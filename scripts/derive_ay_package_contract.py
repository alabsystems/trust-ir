#!/usr/bin/env python3
"""Derive exact AY package versions from authenticated immutable manifests.

Cargo metadata supplies package identities and repository-relative locators;
it does not supply authority for the expected versions. No checkout bytes are
read. Python 3.9 bootstrap uses the pinned upstream Tomli backport when the
standard-library TOML parser is unavailable. This operational
dependency contract grants no mathematical proof or codegen license.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import posixpath
import re
import sys

try:
    import tomllib
except ModuleNotFoundError:
    from _vendor import tomli as tomllib

from dependency_authority import ManifestAuthority, exact_revision, require
from pin_rewrite import AY_REMOTE, SEMVER_RE

MAX_PACKAGES = 256


def repository_path(manifest: str, revision: str, cargo_home: Path) -> str:
    """Interpret Cargo's checkout locator without reading arbitrary local files.

    An unsupported layout refuses. The only accepted source bytes are then
    fetched from the authenticated AY commit at this relative path.
    """
    require(isinstance(manifest, str) and len(manifest) <= 4096,
            "invalid Cargo manifest locator")
    path = Path(manifest)
    require(path.is_absolute() and str(path) == manifest and ".." not in path.parts,
            "noncanonical Cargo manifest locator")
    try:
        parts = path.relative_to(cargo_home / "git" / "checkouts").parts
    except ValueError as error:
        raise ValueError("AY manifest is outside the selected Cargo Git cache") from error
    require(len(parts) >= 3 and re.fullmatch(r"ay-[0-9a-f]+", parts[0]) is not None,
            "unsupported AY checkout locator")
    require(re.fullmatch(r"[0-9a-f]{7,40}", parts[1]) is not None
            and revision.startswith(parts[1]), "AY checkout revision locator mismatch")
    relative = PurePosixPath(*parts[2:]).as_posix()
    require(relative.endswith("Cargo.toml"), "expected Cargo manifest locator")
    return relative


def document(authority: ManifestAuthority, path: str, optional: bool = False):
    raw = authority.optional(path) if optional else authority.read(path)
    if raw is None:
        return None
    data, oid = raw
    parsed = tomllib.loads(data.decode("utf-8"))
    return parsed, {"path": path, "git_blob": oid,
                    "sha256": hashlib.sha256(data).hexdigest()}


def workspace_source(authority: ManifestAuthority, manifest_path: str, package: dict):
    directory = PurePosixPath(manifest_path).parent
    explicit = package.get("workspace")
    if explicit is not None:
        require(isinstance(explicit, str) and explicit and not explicit.startswith("/")
                and "\\" not in explicit, "invalid package workspace locator")
        resolved = posixpath.normpath(posixpath.join(str(directory), explicit))
        require(resolved != ".." and not resolved.startswith("../"),
                "package workspace escapes immutable repository")
        path = "Cargo.toml" if resolved == "." else resolved + "/Cargo.toml"
        result = document(authority, path)
        require(isinstance(result[0].get("workspace"), dict), "missing explicit workspace")
        return result
    # Cargo finds the closest enclosing workspace. Intermediate Cargo.toml
    # files may be absent; corrupt, duplicate, symlinked or truncated trees
    # must still refuse rather than becoming an absent-workspace fallback.
    for parent in (directory, *directory.parents):
        path = "Cargo.toml" if str(parent) == "." else parent.as_posix() + "/Cargo.toml"
        result = document(authority, path, optional=True)
        if result is not None and isinstance(result[0].get("workspace"), dict):
            return result
    raise ValueError("inherited package version has no immutable workspace")


def declared_workspace_version(document: dict):
    workspace = document.get("workspace")
    require(isinstance(workspace, dict), "missing immutable workspace table")
    package = workspace.get("package")
    require(isinstance(package, dict), "missing immutable workspace package table")
    return package.get("version")


def derive(metadata: dict, revision: str, workspace_version: str,
           cargo_home: Path, authority=None, remote: str = AY_REMOTE) -> dict:
    """The contract for AY at `revision` of `remote`: the development remote by
    default; publication's T6 names the public one with an authority over that
    public commit."""
    exact_revision(revision)
    require(SEMVER_RE.fullmatch(workspace_version) is not None,
            "expected exact AY workspace version")
    require(isinstance(metadata, dict) and isinstance(metadata.get("packages"), list),
            "missing resolved Cargo package inventory")
    selector = f"git+{remote}?rev={revision}#{revision}"
    candidates = [p for p in metadata["packages"]
                  if isinstance(p, dict) and isinstance(p.get("source"), str)
                  and remote in p["source"]]
    require(0 < len(candidates) <= MAX_PACKAGES, "empty or excessive AY package inventory")
    require(all(p["source"] == selector for p in candidates), "split AY source authority")
    source = authority if authority is not None else ManifestAuthority("ay", revision)
    root, root_identity = document(source, "Cargo.toml")
    require(declared_workspace_version(root) == workspace_version,
            "immutable AY workspace version disagrees with reviewed version")
    packages = []
    names = set()
    for item in candidates:
        name, version = item.get("name"), item.get("version")
        require(isinstance(name, str) and re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_-]*", name)
                and name not in names, "invalid or duplicate resolved AY package identity")
        names.add(name)
        require(isinstance(version, str) and SEMVER_RE.fullmatch(version) is not None,
                "invalid resolved AY package version")
        path = repository_path(item.get("manifest_path"), revision, cargo_home)
        manifest, identity = document(source, path)
        package = manifest.get("package")
        require(isinstance(package, dict) and package.get("name") == name,
                "immutable package name disagrees with resolved identity: " + name)
        declared = package.get("version")
        version_identity = identity
        if isinstance(declared, dict) and set(declared) == {"workspace"} and declared["workspace"] is True:
            owner, version_identity = workspace_source(source, path, package)
            declared = declared_workspace_version(owner)
        require(isinstance(declared, str) and declared == version,
                "resolved version disagrees with immutable package manifest: " + name)
        packages.append({"name": name, "version": version, "manifest": identity,
                         "version_source": version_identity})
    return {"schema": 1, "repository": remote, "revision": revision,
            "workspace_version": workspace_version, "workspace_manifest": root_identity,
            "packages": sorted(packages, key=lambda p: p["name"])}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--metadata", type=Path, required=True)
    parser.add_argument("--revision", required=True)
    parser.add_argument("--workspace-version", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    home = Path(os.environ.get("CARGO_HOME", str(Path.home() / ".cargo"))).absolute()
    result = derive(json.loads(args.metadata.read_text()), args.revision,
                    args.workspace_version, home)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True, ensure_ascii=False) + "\n")
    print(f"AY_PACKAGE_CONTRACT=derived {len(result['packages'])} exact immutable packages")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError) as error:
        print(f"AY package authority refused: {error}", file=sys.stderr)
        sys.exit(1)
