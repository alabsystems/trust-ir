// Keep the constellation-coordinated Clean pin atomic across the independently
// publishable crates and the standalone rustc frontend lock. "Frozen" below
// always means "frozen relative to the constants in THIS file" — the pin itself
// moves often and is meant to; see the `clean-kernel` note in
// crates/trust-ir/Cargo.toml for why the old "deliberately frozen baseline"
// wording was retired.
//
// Until 2026-08-19 this test was the ONLY mechanical enforcement of the Clean
// pin in the whole repository, because the root `[patch]` rewrote clean.git to
// `../clean` PATH deps, path deps emit no `source =` row, and a Clean move
// therefore produced a byte-identical root Cargo.lock that `--locked` could
// never fail on. That patch is gone (see the note in the workspace root
// Cargo.toml), so the root lock now records the revision and `--locked` is a
// second, independent check. This test remains the enforcement for the legs no
// lockfile covers: the two manifests and the `exclude`d frontend workspace.
// For that workspace it also asks Cargo whether the whole lock still RESOLVES
// (`frontend_lock_resolves_under_locked`), because a non-pin manifest
// change stales it too and nothing else here would notice.
//
// The patch's removal is itself an invariant now — `clean_pin_is_not_path_patched`
// below. Re-introducing it would restore the pin cycle it was deleted to cut:
// a path patch makes ambient working-tree bytes authoritative while Clean pins
// trust-ir back through the non-optional clean-reflect edge. The Clean commit
// every repo pins would then have to name the trust-ir commit that names it.
//
// Every assertion below appends PIN_MOVE_PROTOCOL, because whoever trips one
// has almost certainly just hand-edited a subset of the legs.
//
// The machine-readable leg table lives in `scripts/pin_rewrite.py`; the two
// must be updated together whenever a declaration is added or reshaped.

/// Appended to every assertion in this file. A partial pin move has shipped
/// three times; the recovery procedure has to be in the failure output, not in
/// a document the bumper was never going to open.
const PIN_MOVE_PROTOCOL: &str = r#"

================ DEPENDENCY PIN INCOHERENCE ================
A Clean/AY pin move is ATOMIC. Moving fewer than all of its legs
leaves main RED. Do not hand-edit — run the one correct action:

    scripts/bump-dep-pin.sh clean <40-hex-sha> [--clean-version X.Y.Z]
    scripts/bump-dep-pin.sh ay    <40-hex-sha> [--ay-version X.Y.Z]

When target Clean changes either package version, use the coordinated form:
    scripts/bump-dep-pin.sh clean-ay <clean-sha> <ay-sha> \
        --clean-version X.Y.Z --ay-version X.Y.Z

CLEAN legs:
  1. crates/trust-ir/Cargo.toml               clean-kernel            (1 rev)
  2. crates/trust-ir-build/Cargo.toml         kernel/mathverse/olean/verify (6 declarations;
                                              olean twice: optional and dev)
  3. crates/trust-ir/tests/dependency_pin_coherence.rs  CLEAN_REVISION
  4. frontend/Cargo.lock  <-- SEPARATE WORKSPACE. frontend/ is `exclude`d
     from the root workspace, so it is INVISIBLE to --workspace. This is
     the leg that has been missed three times. Refresh:
       targo update --manifest-path frontend/Cargo.toml -p clean-kernel
  5. Cargo.lock (root) — since the root [patch] was deleted (2026-08-19)
     this DOES record the rev on every clean.git package, so `--locked`
     now fails on a partial move too.
     Refresh: targo metadata --format-version 1 --all-features >/dev/null
  6. (RETIRED) There is no ../clean working-tree leg any more. The root
     [patch] is gone, so cargo compiles clean.git AT THE PINNED REV and
     never the sibling's working tree. Do NOT "align" ../clean by
     checking it out at the pin, and do NOT chase ../clean's HEAD with a
     new pin: Clean pins trust-ir back (clean-reflect), so following its
     HEAD reopens the pin cycle this deletion cut. Cross-repo publication
     instead uses the ratified predecessor-epoch cut: backedges may retain
     immutable predecessor identities while successor repositories advance.
     The final epoch receipt, not raw five-workspace SHA equality, attests
     the exact cohort.

AY legs:
  1. crates/trust-ir-ay/Cargo.toml            ay + ay-proof          (2 revs)
  2. crates/trust-ir-ay/src/vc.rs             pub const AY_REV        (1 rev)
  3. crates/trust-ir-ay/src/bvblast.rs        BVBLAST_PROVER          (1 rev)
  4. crates/trust-ir/tests/dependency_pin_coherence.rs  AY_REVISION
  5. Cargo.lock (root) — 37 ay packages; refresh with the metadata line
  6. The selected Clean COMMIT's Cargo.toml pins ay too (7 declarations).
     The bumper reads that immutable commit before writing anything. If it
     disagrees, Cargo.lock carries two ay graphs and this guard fails.

VERIFY: scripts/run-targo.sh test -p trust-ir --test dependency_pin_coherence
        (standing gate 7 in scripts/ci_gates.sh; its exact toolchain-free
         mirror is scripts/pin_rewrite.py static-guard)
The compiled test is independent parity for the mandatory static mirror;
`check --workspace` alone still executes neither one.
============================================================
"#;

const CLEAN_REPOSITORY: &str = "https://github.com/alabsystems/clean.git";
// Leg 3. This constant had been left at 71449eaa across two Clean moves, so
// the clean half of this gate had been red (and therefore uninformative) the
// whole time. It is now the revision legs 1, 2, 4 and 5 actually carry, which
// is TrustIR's exact local Clean authority. The cross-repository graph is an
// SCC: predecessor backedges intentionally need not resolve this same commit.
// The final epoch receipt attests those predecessor/successor identities.
const CLEAN_REVISION: &str = "e86b4b61e665f73b4737dd360773677561462f7e";
const CLEAN_VERSION: &str = "0.9.4";
const AY_REPOSITORY: &str = "https://github.com/alabsystems/ay.git";
const AY_REVISION: &str = "12d411d420e27eea05099f8cd277eb288e8622c9";
const AY_VERSION: &str = "0.28.4";
/// The AY workspace version whose lock carries `trust-exec-policy` 0.13.0 as
/// its one independently versioned package. The rules below accept that owner
/// only at this version, so moving the AY pin re-reviews it. Publication
/// transform T6 moves it with the public AY pin, after the public AY's own
/// manifests show the same owner.
const AY_POLICY_OWNER_VERSION: &str = "0.28.4";

const TRUST_IR_MANIFEST: &str = include_str!("../Cargo.toml");
const TRUST_IR_AY_MANIFEST: &str = include_str!("../../trust-ir-ay/Cargo.toml");
const TRUST_IR_AY_VC: &str = include_str!("../../trust-ir-ay/src/vc.rs");
const TRUST_IR_AY_BVBLAST: &str = include_str!("../../trust-ir-ay/src/bvblast.rs");
const TRUST_IR_BUILD_MANIFEST: &str = include_str!("../../trust-ir-build/Cargo.toml");
const ROOT_MANIFEST: &str = include_str!("../../../Cargo.toml");
const ROOT_LOCK: &str = include_str!("../../../Cargo.lock");
const FRONTEND_LOCK: &str = include_str!("../../../frontend/Cargo.lock");
const AY_PACKAGE_CONTRACT: &str = include_str!("../../../data/ay_package_versions.json");

fn contract_string<'a>(value: &'a serde_json::Value, key: &str) -> &'a str {
    value[key].as_str().unwrap_or_else(|| {
        panic!("AY package contract needs string {key}; run scripts/bump-dep-pin.sh")
    })
}

fn contract_hex(value: &str, length: usize) -> bool {
    value.len() == length
        && value
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

fn contract_version(value: &str) -> bool {
    let identifiers = |s: &str| {
        s.split('.').all(|part| {
            !part.is_empty() && part.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-')
        })
    };
    let (before_build, build_ok) = value
        .split_once('+')
        .map_or((value, true), |(core, build)| (core, identifiers(build)));
    let (core, pre_ok) = before_build
        .split_once('-')
        .map_or((before_build, true), |(core, pre)| (core, identifiers(pre)));
    let numbers: Vec<_> = core.split('.').collect();
    build_ok
        && pre_ok
        && numbers.len() == 3
        && numbers.iter().all(|number| {
            !number.is_empty()
                && (number.len() == 1 || !number.starts_with('0'))
                && number.bytes().all(|b| b.is_ascii_digit())
        })
}

fn contract_manifest_identity(value: &serde_json::Value, root: &serde_json::Value) {
    assert_eq!(
        value.as_object().expect("manifest object").len(),
        3,
        "AY manifest object shape{PIN_MOVE_PROTOCOL}"
    );
    let path = contract_string(value, "path");
    let parts: Vec<_> = path.split('/').collect();
    assert!(
        path.len() <= 4096
            && (1..=32).contains(&parts.len())
            && parts.last() == Some(&"Cargo.toml")
            && parts.iter().all(|part| {
                !part.is_empty()
                    && *part != "."
                    && *part != ".."
                    && !part.contains('\\')
                    && !part.bytes().any(|b| b.is_ascii_control())
            }),
        "AY package contract manifest path{PIN_MOVE_PROTOCOL}"
    );
    assert!(
        contract_hex(contract_string(value, "git_blob"), 40),
        "AY manifest Git identity{PIN_MOVE_PROTOCOL}"
    );
    assert!(
        contract_hex(contract_string(value, "sha256"), 64),
        "AY manifest digest{PIN_MOVE_PROTOCOL}"
    );
    if path == "Cargo.toml" {
        assert_eq!(value, root, "AY root manifest identity{PIN_MOVE_PROTOCOL}");
    }
}

fn exact_ay_package_versions() -> std::collections::BTreeMap<String, String> {
    let data: serde_json::Value =
        serde_json::from_str(AY_PACKAGE_CONTRACT).expect("AY package contract JSON");
    // The owner's canonical representation also refuses duplicate JSON keys;
    // deserializing and silently keeping their last value is insufficient.
    assert_eq!(
        AY_PACKAGE_CONTRACT,
        format!(
            "{}\n",
            serde_json::to_string_pretty(&data).expect("canonical JSON")
        ),
        "AY package contract must use the owner's canonical JSON{PIN_MOVE_PROTOCOL}"
    );
    assert_eq!(
        data.as_object().expect("contract object").len(),
        6,
        "AY contract shape{PIN_MOVE_PROTOCOL}"
    );
    assert_eq!(
        data["schema"].as_u64(),
        Some(1),
        "AY contract schema{PIN_MOVE_PROTOCOL}"
    );
    assert_eq!(
        contract_string(&data, "repository"),
        AY_REPOSITORY,
        "AY contract repository{PIN_MOVE_PROTOCOL}"
    );
    assert_eq!(
        contract_string(&data, "revision"),
        AY_REVISION,
        "AY contract revision{PIN_MOVE_PROTOCOL}"
    );
    assert_eq!(
        contract_string(&data, "workspace_version"),
        AY_VERSION,
        "AY contract workspace version{PIN_MOVE_PROTOCOL}"
    );
    let root = &data["workspace_manifest"];
    contract_manifest_identity(root, root);
    assert_eq!(
        contract_string(root, "path"),
        "Cargo.toml",
        "AY contract workspace path{PIN_MOVE_PROTOCOL}"
    );
    let packages = data["packages"].as_array().expect("package inventory");
    assert!(
        (1..=256).contains(&packages.len()),
        "AY package inventory bounds{PIN_MOVE_PROTOCOL}"
    );
    let mut versions = std::collections::BTreeMap::new();
    let mut previous = "";
    for package in packages {
        assert_eq!(
            package.as_object().expect("package object").len(),
            4,
            "AY package shape{PIN_MOVE_PROTOCOL}"
        );
        let name = contract_string(package, "name");
        let version = contract_string(package, "version");
        assert!(
            name > previous
                && name
                    .bytes()
                    .next()
                    .is_some_and(|b| b.is_ascii_alphanumeric())
                && name
                    .bytes()
                    .all(|b| b.is_ascii_alphanumeric() || b == b'_' || b == b'-'),
            "AY package identity/order{PIN_MOVE_PROTOCOL}"
        );
        assert!(
            contract_version(version),
            "AY exact package version{PIN_MOVE_PROTOCOL}"
        );
        contract_manifest_identity(&package["manifest"], root);
        contract_manifest_identity(&package["version_source"], root);
        assert!(
            versions
                .insert(name.to_owned(), version.to_owned())
                .is_none(),
            "AY package duplicate identity{PIN_MOVE_PROTOCOL}"
        );
        previous = name;
    }
    versions
}

#[derive(Debug)]
struct LockedPackage<'a> {
    fields: std::collections::BTreeMap<&'a str, &'a str>,
    dependencies: Option<Vec<&'a str>>,
}

fn canonical_lock_quoted(value: &str) -> Option<&str> {
    value
        .strip_prefix('"')
        .and_then(|v| v.strip_suffix('"'))
        .filter(|v| !v.contains(['"', '\\']))
}

fn canonical_lock_packages(lock: &str) -> Result<Vec<LockedPackage<'_>>, String> {
    let mut packages = Vec::new();
    for block in lock.split("[[package]]").skip(1) {
        let mut package = LockedPackage {
            fields: Default::default(),
            dependencies: None,
        };
        let mut dependencies = None::<Vec<&str>>;
        for line in block
            .lines()
            .map(str::trim)
            .filter(|line| !line.is_empty() && !line.starts_with('#'))
        {
            if let Some(values) = dependencies.as_mut() {
                if line == "]" {
                    package.dependencies = dependencies.take();
                } else {
                    let value = line
                        .strip_suffix(',')
                        .and_then(canonical_lock_quoted)
                        .ok_or("unsupported canonical dependency line")?;
                    values.push(value);
                }
                continue;
            }
            if line == "dependencies = [" {
                if package.dependencies.is_some() {
                    return Err("duplicate dependency array".into());
                }
                dependencies = Some(Vec::new());
                continue;
            }
            let (key, value) = line
                .split_once(" = ")
                .ok_or("unsupported canonical lock field")?;
            if !key.starts_with(|c: char| c.is_ascii_lowercase())
                || !key
                    .chars()
                    .all(|c| c.is_ascii_lowercase() || c == '_' || c == '-')
            {
                return Err("unsupported canonical field name".into());
            }
            let value = canonical_lock_quoted(value).ok_or("unsupported canonical quoted field")?;
            if package.fields.insert(key, value).is_some() {
                return Err("duplicate lock field".into());
            }
        }
        if dependencies.is_some()
            || !package.fields.contains_key("name")
            || !package.fields.contains_key("version")
        {
            return Err("incomplete canonical package".into());
        }
        packages.push(package);
    }
    Ok(packages)
}

fn lock_edge_index(raw: &str, packages: &[LockedPackage<'_>]) -> Result<usize, String> {
    let fields: Vec<_> = raw.split_whitespace().collect();
    if fields.is_empty() || fields.len() > 3 {
        return Err("malformed dependency identity".into());
    }
    let source = if fields.len() == 3 {
        Some(
            fields[2]
                .strip_prefix('(')
                .and_then(|v| v.strip_suffix(')'))
                .ok_or("malformed dependency source")?,
        )
    } else {
        None
    };
    let matching: Vec<_> = packages
        .iter()
        .enumerate()
        .filter(|(_, package)| {
            package.fields.get("name").copied() == Some(fields[0])
                && (fields.len() < 2 || package.fields.get("version").copied() == Some(fields[1]))
                && source.is_none_or(|wanted| {
                    package.fields.get("source").is_some_and(|actual| {
                        *actual == wanted
                            || (wanted.starts_with("git+")
                                && !wanted.contains('#')
                                && actual.rsplit_once('#').is_some_and(|(base, precise)| {
                                    base == wanted
                                        && precise.len() == 40
                                        && precise.bytes().all(|c| {
                                            c.is_ascii_digit() || (b'a'..=b'f').contains(&c)
                                        })
                                }))
                    })
                })
        })
        .map(|(index, _)| index)
        .collect();
    if matching.len() == 1 {
        Ok(matching[0])
    } else {
        Err("ambiguous or missing dependency".into())
    }
}

fn validate_ay_lock_source_owner(lock: &str, revision: &str, version: &str) -> Result<(), String> {
    const POLICY: &str = "trust-exec-policy";
    const REGISTRY: &str = "registry+https://github.com/rust-lang/crates.io-index";
    let packages = canonical_lock_packages(lock)?;
    let source = format!("git+{AY_REPOSITORY}?rev={revision}#{revision}");
    let prefix = format!("git+{AY_REPOSITORY}");
    let selected: Vec<_> = packages
        .iter()
        .enumerate()
        .filter(|(_, p)| {
            p.fields
                .get("source")
                .is_some_and(|s| s.starts_with(&prefix))
        })
        .map(|(index, _)| index)
        .collect();
    if selected.is_empty() {
        return Err("missing selected AY source".into());
    }
    let mut vendors = Vec::new();
    let mut systems = Vec::new();
    for &index in &selected {
        let row = &packages[index];
        if row.fields.get("source").copied() != Some(source.as_str()) {
            return Err("stale AY source".into());
        }
        let name = row.fields["name"];
        if name == "ay-sys" {
            systems.push(index);
        }
        if name == "ay" || name.starts_with("ay-") {
            if row.fields["version"] != version {
                return Err("wrong AY package version".into());
            }
        } else if name == POLICY
            && row.fields["version"] == "0.13.0"
            && version == AY_POLICY_OWNER_VERSION
        {
            vendors.push(index);
        } else {
            return Err("foreign AY-source package".into());
        }
    }
    if vendors.is_empty() {
        return if version == AY_POLICY_OWNER_VERSION && !systems.is_empty() {
            Err("missing actual required system policy owner".into())
        } else {
            Ok(())
        };
    }
    if vendors.len() != 1 || systems.len() != 1 {
        return Err("duplicate/missing independent owner".into());
    }
    let (vendor, system) = (vendors[0], systems[0]);
    let mut incoming = Vec::new();
    for (index, row) in packages.iter().enumerate() {
        for edge in row.dependencies.iter().flatten() {
            if edge.split_whitespace().next() == Some(POLICY) {
                let target = lock_edge_index(edge, &packages)?;
                if target == vendor {
                    incoming.push((index, target));
                }
            }
        }
    }
    let policy = &packages[vendor];
    if incoming != [(system, vendor)] || policy.fields.len() != 3 {
        return Err("requires exactly the actual ay-sys incoming edge and policy metadata".into());
    }
    let edges = policy
        .dependencies
        .as_ref()
        .ok_or("missing policy libc edge")?;
    if edges.len() != 1 {
        return Err("requires the sole policy libc edge".into());
    }
    let libc = &packages[lock_edge_index(edges[0], &packages)?];
    let patch = libc.fields["version"]
        .strip_prefix("0.2.")
        .ok_or("unsupported libc version")?;
    if libc.fields["name"] != "libc"
        || libc.fields.get("source").copied() != Some(REGISTRY)
        || patch.is_empty()
        || !patch.bytes().all(|c| c.is_ascii_digit())
        || (patch.len() > 1 && patch.starts_with('0'))
    {
        return Err("requires canonical registry libc0.2".into());
    }
    Ok(())
}

#[test]
fn ay_independent_policy_source_owner_controls() {
    let revision = "1111111111111111111111111111111111111111";
    let source = format!("git+{AY_REPOSITORY}?rev={revision}#{revision}");
    let system = format!(
        "[[package]]\nname = \"ay-sys\"\nversion = \"{AY_POLICY_OWNER_VERSION}\"\nsource = \"{source}\"\ndependencies = [\n \"trust-exec-policy\",\n]\n"
    );
    let policy = format!(
        "[[package]]\nname = \"trust-exec-policy\"\nversion = \"0.13.0\"\nsource = \"{source}\"\ndependencies = [\n \"libc\",\n]\n"
    );
    let libc = format!(
        "[[package]]\nname = \"libc\"\nversion = \"0.2.177\"\nsource = \"registry+https://github.com/rust-lang/crates.io-index\"\nchecksum = \"{}\"\n",
        "a".repeat(64)
    );
    let fixture = format!("{system}{policy}{libc}");
    assert!(
        validate_ay_lock_source_owner(&fixture, revision, AY_POLICY_OWNER_VERSION).is_ok(),
        "supported independent source owner refused{PIN_MOVE_PROTOCOL}"
    );
    let legacy = system
        .replace(
            &format!("version = \"{AY_POLICY_OWNER_VERSION}\""),
            "version = \"0.27.0\"",
        )
        .replace("dependencies = [\n \"trust-exec-policy\",\n]\n", "")
        + &libc;
    assert!(
        validate_ay_lock_source_owner(&legacy, revision, "0.27.0").is_ok(),
        "legacy independent source owner refused{PIN_MOVE_PROTOCOL}"
    );
    let candidates = [
        fixture.replace(
            "version = \"0.13.0\"",
            &format!("version = \"{AY_POLICY_OWNER_VERSION}\""),
        ),
        fixture.replace("version = \"0.2.177\"", "version = \"0.3.0\""),
        fixture.replace(" \"trust-exec-policy\",\n", ""),
        format!("{fixture}{policy}"),
        fixture.clone() + &system.replace("name = \"ay-sys\"", "name = \"other\""),
        fixture.clone()
            + &policy
                .replace("name = \"trust-exec-policy\"", "name = \"foreign\"")
                .replace(
                    "version = \"0.13.0\"",
                    &format!("version = \"{AY_POLICY_OWNER_VERSION}\""),
                ),
        format!("{system}{libc}"),
        fixture.replace("name = \"ay-sys\"", "name = \"ay-other\""),
        system
            + &policy.replace(
                "version = \"0.13.0\"",
                "checksum = \"a\"\nversion = \"0.13.0\"",
            )
            + &libc,
    ];
    for (index, candidate) in candidates.iter().enumerate() {
        assert!(
            validate_ay_lock_source_owner(candidate, revision, AY_POLICY_OWNER_VERSION).is_err(),
            "hostile independent source-owner fixture {index} accepted{PIN_MOVE_PROTOCOL}"
        );
    }
}

fn clean_dependency_lines(manifest: &str) -> Vec<&str> {
    manifest
        .lines()
        .map(str::trim)
        .filter(|line| {
            !line.starts_with('#') && line.starts_with("clean-") && line.contains(" = {")
        })
        .collect()
}

fn assert_exact_manifest_pins(manifest_name: &str, manifest: &str, expected_count: usize) {
    let lines = clean_dependency_lines(manifest);
    assert_eq!(
        lines.len(),
        expected_count,
        "{manifest_name} Clean dependency inventory changed; update this guard and every pin atomically: {lines:?}{PIN_MOVE_PROTOCOL}"
    );

    let exact_git = format!("git = \"{CLEAN_REPOSITORY}\"");
    let exact_rev = format!("rev = \"{CLEAN_REVISION}\"");
    let exact_version = format!("version = \"{CLEAN_VERSION}\"");
    for line in lines {
        assert!(
            line.contains(&exact_version),
            "{manifest_name} has a Clean dependency outside the frozen package version: {line}{PIN_MOVE_PROTOCOL}"
        );
        assert!(
            line.contains(&exact_git),
            "{manifest_name} has a Clean dependency outside the canonical repository: {line}{PIN_MOVE_PROTOCOL}"
        );
        assert!(
            line.contains(&exact_rev),
            "{manifest_name} has a Clean dependency outside the frozen revision: {line}{PIN_MOVE_PROTOCOL}"
        );
        assert!(
            !line.contains("branch =") && !line.contains("tag ="),
            "{manifest_name} must not add floating Clean selectors: {line}{PIN_MOVE_PROTOCOL}"
        );
    }
}

#[test]
fn clean_consumability_baseline_is_exact_and_atomic() {
    assert_exact_manifest_pins("crates/trust-ir/Cargo.toml", TRUST_IR_MANIFEST, 1);
    assert_exact_manifest_pins(
        "crates/trust-ir-build/Cargo.toml",
        TRUST_IR_BUILD_MANIFEST,
        6,
    );

    let clean_packages: Vec<&str> = FRONTEND_LOCK
        .split("[[package]]")
        .filter(|package| {
            package.lines().any(|line| {
                line.trim()
                    .strip_prefix("name = \"")
                    .is_some_and(|name| name.starts_with("clean-"))
            })
        })
        .collect();
    assert_eq!(
        clean_packages.len(),
        1,
        "frontend/Cargo.lock Clean package inventory changed; update this guard and every pin atomically{PIN_MOVE_PROTOCOL}"
    );
    let exact_version = format!("version = \"{CLEAN_VERSION}\"");
    assert!(
        clean_packages[0]
            .lines()
            .any(|line| line.trim() == exact_version),
        "frontend/Cargo.lock does not resolve Clean to the frozen package version{PIN_MOVE_PROTOCOL}"
    );

    let exact_source =
        format!("source = \"git+{CLEAN_REPOSITORY}?rev={CLEAN_REVISION}#{CLEAN_REVISION}\"");
    assert!(
        clean_packages[0]
            .lines()
            .any(|line| line.trim() == exact_source),
        "frontend/Cargo.lock does not resolve its Clean package to the exact frozen revision{PIN_MOVE_PROTOCOL}"
    );

    let clean_git_source = format!("git+{CLEAN_REPOSITORY}");
    let clean_source_rows: Vec<&str> = FRONTEND_LOCK
        .lines()
        .map(str::trim)
        .filter(|line| line.contains(&clean_git_source))
        .collect();
    assert_eq!(
        clean_source_rows,
        vec![exact_source.as_str()],
        "frontend/Cargo.lock contains a floating or split Clean source{PIN_MOVE_PROTOCOL}"
    );
}

/// The workspace root must NOT redirect clean.git onto the `../clean` sibling.
///
/// A `[patch]` there is invisible to every consumer of trust-ir (Cargo only
/// honours `[patch]` in the workspace root it is building), so it bought
/// nothing but local convenience — while costing two things that matter:
/// the root Cargo.lock stopped recording the Clean revision at all, and
/// `ty-mcc-drift-guard` had to prove the patched declaration by requiring
/// `HEAD(../clean) == the declared rev`. Because Clean pins trust-ir back
/// through the non-optional clean-reflect edge, that requirement made the
/// five-repo pin set unsatisfiable: the Clean commit every repo names would
/// have had to name the trust-ir commit that names it. Keeping the patch out
/// is what keeps that set solvable.
///
/// Develop against a live sibling with an UNCOMMITTED override instead — a
/// gitignored `.cargo/config.toml` `[patch]`, or `paths = ["../clean"]`.
#[test]
fn clean_pin_is_not_path_patched() {
    let offending: Vec<&str> = ROOT_MANIFEST
        .lines()
        .map(str::trim)
        .filter(|line| !line.starts_with('#'))
        .filter(|line| line.starts_with("[patch") && line.contains("clean.git"))
        .collect();
    assert!(
        offending.is_empty(),
        "the workspace root re-introduced a Clean path patch: {offending:?}\n\
         It cannot help any consumer (Cargo ignores [patch] outside the root being \
         built) and it reopens the trust-ir <-> clean pin cycle.{PIN_MOVE_PROTOCOL}"
    );

    // Leg 5, newly enforceable now that the patch is gone: every clean.git row
    // in the root lock must be the frozen revision, and there must be at least
    // one — a lock with no clean.git row means the patch is back.
    let exact_source =
        format!("source = \"git+{CLEAN_REPOSITORY}?rev={CLEAN_REVISION}#{CLEAN_REVISION}\"");
    let clean_git_source = format!("git+{CLEAN_REPOSITORY}");
    let clean_source_rows: Vec<&str> = ROOT_LOCK
        .lines()
        .map(str::trim)
        .filter(|line| line.contains(&clean_git_source))
        .collect();
    assert!(
        !clean_source_rows.is_empty(),
        "root Cargo.lock records no clean.git source; the Clean dependency was \
         path-patched or dropped{PIN_MOVE_PROTOCOL}"
    );
    assert!(
        clean_source_rows
            .iter()
            .all(|line| *line == exact_source.as_str()),
        "root Cargo.lock contains a stale or split Clean source: {clean_source_rows:?}{PIN_MOVE_PROTOCOL}"
    );
}

/// Appended to the frontend-lock resolution assertion below, beside
/// [`PIN_MOVE_PROTOCOL`]: that assertion also fires on a lock made stale by a
/// change that is NOT a pin move, and then this is the fix.
const FRONTEND_LOCK_REFRESH: &str = r#"

================ frontend/Cargo.lock DOES NOT RESOLVE ================
frontend/ is a SEPARATE workspace (`exclude`d from the root), so no
--workspace command ever resolves its lock. Any manifest change on its
path-dependency graph (crates/trust-ir, crates/trust-ir-build and their
own path dependencies) can make it stale, pin move or not.

If the lock is STALE ("cannot update the lock file ... --locked"),
refresh it (non-compiling; no verification claim) and commit the result:

    cd frontend && targo metadata --offline --format-version 1 >/dev/null

The diff should add or drop exactly the packages your manifest change
added or dropped. If it also moves unrelated versions, the offline cache
could not supply the locked ones: discard it and run the same command
without --offline.

If it failed for another reason, read Cargo's error above. The offline
query needs every package the lock names in the local cache; when it
cannot decide offline the test asks again WITH the network, so a
network error here means the cache is cold AND the registry or the
Clean git remote is unreachable. Warm the cache and re-run:

    targo fetch --locked --manifest-path frontend/Cargo.toml
=======================================================================
"#;

/// `frontend/Cargo.lock` must RESOLVE under `--locked`, not merely carry the
/// right Clean row.
///
/// `frontend/` is workspace-`exclude`d, so no `--workspace` command reads its
/// lock, and [`clean_consumability_baseline_is_exact_and_atomic`] reads only
/// its Clean rows. On 2026-09-25 a NON-pin change (`trust-ir-build` gained the
/// path dependency `trust-ir-laws`) left this lock stale, every `--locked`
/// frontend command failed, and no gate noticed until review. This asks Cargo
/// itself, through the non-compiling query `metadata --locked`, which fails
/// exactly when the lock would have to change to describe the current
/// manifests, whichever leg moved.
///
/// It runs the Cargo that is running this test (`CARGO`, which Cargo sets for
/// every test process). Under gate 7 that is `targo` itself (measured: a
/// `targo --unverified test` process sees `CARGO=<store>/bin/targo`, and targo
/// warns that a recursive `$CARGO` must select its own lane), so this runs
/// `targo metadata`: it compiles nothing, needs no lane, and establishes no
/// verification.
///
/// Network: the query runs `--offline` first. `metadata` needs every package
/// the lock names, for every platform, in the local cache, and building or
/// testing the root workspace does not put them there (the frontend lock pins
/// crates.io versions the root lock does not use). So when the offline query
/// cannot DECIDE (its error names `--offline` and is not the stale-lock error),
/// the same query runs once more with the network allowed, and that answer is
/// the verdict. Measured 2026-09-27 on a fresh `CARGO_HOME`: offline answers
/// "no matching package named `serde`"; the networked query downloads the
/// frontend's packages and passes; on a warm cache the networked query makes
/// no request (it passes behind an unreachable proxy). A stale lock fails
/// either way ("cannot update the lock file ... --locked"). Without a cache
/// and without the network this test FAILS (fail closed: the lock is then not
/// shown to resolve), and the message names the fetch that warms the cache.
#[test]
fn frontend_lock_resolves_under_locked() {
    let root = concat!(env!("CARGO_MANIFEST_DIR"), "/../..");
    let manifest = format!("{root}/frontend/Cargo.toml");
    // Runtime, not `env!`: the Cargo running the test is the authority, and a
    // test binary run outside Cargo refuses rather than guessing one.
    let cargo = std::env::var_os("CARGO");
    let resolve = |offline: bool| -> (bool, String) {
        let Some(cargo) = cargo.as_ref() else {
            return (
                false,
                "CARGO is unset: run this through `scripts/run-targo.sh test -p trust-ir \
                 --test dependency_pin_coherence`, so the toolchain running the gate \
                 resolves the lock"
                    .to_owned(),
            );
        };
        let mut command = std::process::Command::new(cargo);
        command.args(["metadata", "--locked", "--format-version", "1"]);
        if offline {
            command.arg("--offline");
        }
        match command
            .arg("--manifest-path")
            .arg(&manifest)
            .current_dir(root)
            .stdout(std::process::Stdio::null())
            .output()
        {
            Ok(output) => (
                output.status.success(),
                String::from_utf8_lossy(&output.stderr).into_owned(),
            ),
            Err(error) => (false, format!("could not run CARGO: {error}")),
        }
    };
    let (offline_ok, offline_stderr) = resolve(true);
    if offline_ok {
        return;
    }
    // The stale-lock error's own help text names `--offline` too, so the
    // undecided case is "names --offline" MINUS "the lock would change".
    let stale = offline_stderr.contains("cannot update the lock file");
    let undecided_offline = !stale && offline_stderr.contains("--offline");
    let (success, stderr) = if undecided_offline {
        let (online_ok, online_stderr) = resolve(false);
        (
            online_ok,
            format!(
                "offline, Cargo could not decide:\n{offline_stderr}\n\
                 with the network allowed:\n{online_stderr}"
            ),
        )
    } else {
        (false, offline_stderr)
    };
    assert!(
        success,
        "`$CARGO metadata --locked [--offline] --format-version 1 --manifest-path \
         {manifest}` failed:\n{stderr}{FRONTEND_LOCK_REFRESH}{PIN_MOVE_PROTOCOL}"
    );
}

#[test]
fn ay_manifest_and_root_lock_are_exact_and_atomic() {
    // BOTH AY legs of the manifest. `ay` is the solver facade; `ay-proof` is the
    // bit-blast proof exporter, a DIRECT dependency because the facade does not
    // re-export `BvExpr` / `export_bv_blast_proof_expr`. They must move
    // together: a split rev puts two ay graphs in the lock, and the bv-blast
    // authority capability re-runs ay's blaster to bind a stored refutation to
    // a re-derived goal — so a rev drift between the two legs would compare a
    // proof produced by one blaster against a CNF derived by another.
    let ay_dependency_lines: Vec<&str> = TRUST_IR_AY_MANIFEST
        .lines()
        .map(str::trim)
        .filter(|line| {
            !line.starts_with('#')
                && (line.starts_with("ay = {") || line.starts_with("ay-proof = {"))
        })
        .collect();
    assert_eq!(
        ay_dependency_lines.len(),
        2,
        "trust-ir-ay AY dependency inventory changed; update this guard and every pin atomically{PIN_MOVE_PROTOCOL}"
    );
    let manifest_git = format!("git = \"{AY_REPOSITORY}\"");
    let manifest_rev = format!("rev = \"{AY_REVISION}\"");
    let manifest_version = format!("version = \"{AY_VERSION}\"");
    for line in &ay_dependency_lines {
        assert!(
            line.contains(&manifest_git)
                && line.contains(&manifest_rev)
                && line.contains(&manifest_version)
                && !line.contains("branch =")
                && !line.contains("tag ="),
            "trust-ir-ay must use the exact canonical AY authority: {line}{PIN_MOVE_PROTOCOL}"
        );
    }

    // One provenance leg no lockfile can catch: `AY_REV` is stamped
    // into every emitted verification bundle as solver provenance. A stale
    // value compiles, links, and silently misreports which solver replayed a
    // proof — there is no resolution step that could disagree with it.
    let exact_ay_rev = format!("pub const AY_REV: &str = \"{AY_REVISION}\";");
    assert!(
        TRUST_IR_AY_VC
            .lines()
            .any(|line| line.trim() == exact_ay_rev),
        "crates/trust-ir-ay/src/vc.rs AY_REV disagrees with the frozen AY revision; it stamps evidence provenance into every emitted bundle and a stale value silently misreports which solver replayed a proof{PIN_MOVE_PROTOCOL}"
    );
    let exact_bvblast_prover =
        format!("pub const BVBLAST_PROVER: &str = \"trust-ir-ay/bvblast@{AY_REVISION}\";");
    assert!(
        TRUST_IR_AY_BVBLAST
            .lines()
            .any(|line| line.trim() == exact_bvblast_prover),
        "crates/trust-ir-ay/src/bvblast.rs BVBLAST_PROVER disagrees with the frozen AY revision; it is the authority identity stamped into every stored bit-blast certificate{PIN_MOVE_PROTOCOL}"
    );

    let selector = format!("git+{AY_REPOSITORY}?rev={AY_REVISION}");
    let ay_git_source = format!("git+{AY_REPOSITORY}?rev=");
    let ay_selector_rows: Vec<&str> = ROOT_LOCK
        .lines()
        .map(str::trim)
        .filter(|line| line.contains(&ay_git_source))
        .collect();
    assert!(
        !ay_selector_rows.is_empty(),
        "root Cargo.lock must resolve the AY graph pulled through trust-ir-ay and Clean{PIN_MOVE_PROTOCOL}"
    );
    assert!(
        ay_selector_rows.iter().all(|line| line.contains(&selector)),
        "root Cargo.lock contains a stale or split AY selector: {ay_selector_rows:?}{PIN_MOVE_PROTOCOL}"
    );

    let exact_source = format!("source = \"{selector}#{AY_REVISION}\"");
    let ay_source_rows: Vec<&str> = ay_selector_rows
        .iter()
        .copied()
        .filter(|line| line.starts_with("source = "))
        .collect();
    assert!(
        !ay_source_rows.is_empty()
            && ay_source_rows
                .iter()
                .all(|line| *line == exact_source.as_str()),
        "root Cargo.lock does not resolve every AY package to the exact AY authority: {ay_source_rows:?}{PIN_MOVE_PROTOCOL}"
    );

    let ay_packages: Vec<&str> = ROOT_LOCK
        .split("[[package]]")
        .filter(|package| package.lines().any(|line| line.trim() == exact_source))
        .collect();
    assert_eq!(
        ay_packages.len(),
        ay_source_rows.len(),
        "root Cargo.lock AY package inventory disagrees with its exact source rows{PIN_MOVE_PROTOCOL}"
    );
    assert!(
        ay_packages
            .iter()
            .all(|package| ay_lock_package_version_allowed(package, AY_REVISION, AY_VERSION)),
        "root Cargo.lock resolves an AY package outside the frozen package version{PIN_MOVE_PROTOCOL}"
    );
    let expected_versions = exact_ay_package_versions();
    let mut observed_versions = std::collections::BTreeMap::new();
    for package in ay_packages {
        let field = |key: &str| {
            let prefix = format!("{key} = \"");
            let values: Vec<_> = package
                .lines()
                .map(str::trim)
                .filter_map(|line| line.strip_prefix(&prefix)?.strip_suffix('"'))
                .collect();
            assert_eq!(
                values.len(),
                1,
                "AY package field cardinality{PIN_MOVE_PROTOCOL}"
            );
            values[0].to_owned()
        };
        let name = field("name");
        let version = field("version");
        assert_eq!(
            expected_versions.get(&name),
            Some(&version),
            "root Cargo.lock resolves an AY package outside its exact immutable version: {name}{PIN_MOVE_PROTOCOL}"
        );
        assert!(
            observed_versions.insert(name, version).is_none(),
            "duplicate AY lock package identity{PIN_MOVE_PROTOCOL}"
        );
    }
    assert_eq!(
        observed_versions, expected_versions,
        "root Cargo.lock AY inventory differs from immutable manifest contract{PIN_MOVE_PROTOCOL}"
    );
    assert!(
        validate_ay_lock_source_owner(ROOT_LOCK, AY_REVISION, AY_VERSION).is_ok(),
        "root Cargo.lock AY policy dependency ownership mismatch{PIN_MOVE_PROTOCOL}"
    );
}

fn ay_lock_package_version_allowed(package: &str, revision: &str, version: &str) -> bool {
    fn field<'a>(package: &'a str, key: &str) -> Option<&'a str> {
        let prefix = format!("{key} = \"");
        let mut values = package
            .lines()
            .map(str::trim)
            .filter_map(|line| line.strip_prefix(prefix.as_str())?.strip_suffix('"'));
        let value = values.next()?;
        if values.next().is_some() || value.contains(['"', '\\']) {
            return None;
        }
        Some(value)
    }
    let source = format!("git+{AY_REPOSITORY}?rev={revision}#{revision}");
    if field(package, "source") != Some(source.as_str()) {
        return false;
    }
    match field(package, "name") {
        Some("trust-exec-policy") => {
            version == AY_POLICY_OWNER_VERSION && field(package, "version") == Some("0.13.0")
        }
        Some(_) => field(package, "version") == Some(version),
        None => false,
    }
}

#[test]
fn independent_ay_package_version_owner_is_exact() {
    let revision = "1111111111111111111111111111111111111111";
    let source = format!("git+{AY_REPOSITORY}?rev={revision}#{revision}");
    let row = |name: &str, version: &str, origin: &str| {
        format!("name = \"{name}\"\nversion = \"{version}\"\nsource = \"{origin}\"\n")
    };
    assert!(
        ay_lock_package_version_allowed(
            &row("trust-exec-policy", "0.13.0", &source),
            revision,
            AY_POLICY_OWNER_VERSION
        ),
        "{PIN_MOVE_PROTOCOL}"
    );
    assert!(
        ay_lock_package_version_allowed(
            &row("ay-core", AY_POLICY_OWNER_VERSION, &source),
            revision,
            AY_POLICY_OWNER_VERSION
        ),
        "{PIN_MOVE_PROTOCOL}"
    );
    for (name, version, origin) in [
        ("another-policy", "0.13.0", source.clone()),
        ("ay-core", "0.13.0", source.clone()),
        ("trust-exec-policy", AY_POLICY_OWNER_VERSION, source.clone()),
        ("trust-exec-policy", "0.13.1", source.clone()),
        (
            "trust-exec-policy",
            "0.13.0",
            source.replace("alabsystems/ay", "foreign/ay"),
        ),
        ("trust-exec-policy", "0.13.0", format!("{source}bad")),
        (
            "trust-exec-policy",
            "0.13.0",
            "registry+https://github.com/rust-lang/crates.io-index".into(),
        ),
    ] {
        assert!(
            !ay_lock_package_version_allowed(
                &row(name, version, &origin),
                revision,
                AY_POLICY_OWNER_VERSION
            ),
            "{PIN_MOVE_PROTOCOL}"
        );
    }
    assert!(
        !ay_lock_package_version_allowed(
            &row("trust-exec-policy", "0.13.0", &source),
            revision,
            "0.27.0"
        ),
        "{PIN_MOVE_PROTOCOL}"
    );
}

/// The x86-64 vector-compare certificate ground names the AY that produced
/// every certificate (`trust_ir::CHC_X86_ICMP_CERTIFICATE_RULE`), and trust-cg's
/// certificate gate requires its own AY pin to equal it, while trust-cg's pin
/// transaction requires trust-ir to co-own trust-cg's AY. So an AY move here
/// that does not carry the rule would turn trust-cg's gate red at trust-cg's
/// next pin move, a red nothing runs per landing. This makes the move fail
/// HERE instead: re-certify the certificate cells under the new AY with
/// trust-cg's gate, then move the rule's `ay.rev`, `ay.version` and
/// `certifying_sha256` in the same commit as this pin
/// (`scripts/bump-dep-pin.sh` cannot move them: they are evidence, not a pin
/// leg). The revision AND the version are held, as `publish/transforms.sh` T1
/// holds them, because the rule's version is the one the rebuilt binary's
/// banner must report. What this cannot see is the re-certification itself:
/// the digests are evidence, not identity. Mirrored without a compiler by
/// `scripts/pin_rewrite.py static-guard` (its `GUARD_TEST_MIRRORS` row).
#[test]
fn x86_icmp_certificate_rule_names_the_pinned_ay() {
    let rule = trust_ir::CHC_X86_ICMP_CERTIFICATE_RULE.ay;
    assert_eq!(
        (rule.rev, rule.version),
        (AY_REVISION, AY_VERSION),
        "CHC_X86_ICMP_CERTIFICATE_RULE.ay (rev, version) differs from the AY pin: re-certify \
         the x86-64 vector-compare certificate cells under the new AY (trust-cg \
         scripts/check_x86_icmp_certificates.py) and move the rule with the pin{PIN_MOVE_PROTOCOL}"
    );
}
