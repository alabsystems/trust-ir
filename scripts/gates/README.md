# Gate test registries

`scripts/ci_gates.sh` reads the test targets of its registry-backed gates from these files, one
file per (gate, crate): `<gate-name>.<crate>.tests`. Each non-blank line is one cargo test target
(`--test <name>`); `#` starts a comment. The gate runs ONE `test --locked --workspace --test …` over
the targets of all of its files (the workspace selection keeps one feature resolution for every
gate; a test target name two crates share runs in both).

Add a test to a gate by adding ONE line to the right file, never by editing `ci_gates.sh`.
`.gitattributes` marks `*.tests` `merge=union`, so two branches that each add a line merge without
a conflict (the lists are sets; order is irrelevant). Put the reason on the line itself as a
trailing comment (`struct_repr_and_target  # WS2.3: declared layout coherence`).

A new gate that runs a list of test targets should get its own registry the same way.

A workspace-EXCLUDED package (the root manifest's `exclude`, today `frontend/`) gets a registry
named by its directory, `<gate-name>.<package-dir>.tests`, run by `run_excluded_registry <gate>
<package-dir>` as ONE `test --locked --manifest-path <package-dir>/Cargo.toml` over its targets
(its own lock and feature resolution). A listed target must pass whole: a test that must be gated
lives in a target that passes. `scripts/check_enforcement_links.py` counts the tests of such a
target as `(test)` witnesses only while a wired registry lists it.
