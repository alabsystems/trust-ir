# Third-party notes

TrustIr is licensed under Apache-2.0. This file records notable project
influences and cross-repository provenance; it is not a complete generated
software bill of materials. Cargo dependencies retain their own copyright and
license terms.

## Aeneas

The experimental give-back representation is conceptually influenced by the
[Aeneas](https://github.com/AeneasVerif/aeneas) approach to functional
translations of Rust borrowing. TrustIr's implementation is maintained in this
repository; this note does not imply source vendoring or compatibility with the
complete Aeneas model.

## Rust compiler interfaces

The workspace-excluded `frontend/` driver uses Rust compiler-internal THIR and
MIR interfaces. Those interfaces and the Rust compiler are separate upstream
works under their own terms. No Rust compiler source tree is vendored here.

## ALab Systems sibling projects

The frontend lowering structure draws on the separately maintained TrustCg
lowering path. Clean and AY are consumed as exact Git dependencies for kernel
re-checking and the non-default solver adapter. These sibling repositories are
not vendored into TrustIr; public snapshots resolve only revisions attested by
the publication mapping ledger.

## Dependency inventory

`Cargo.lock` and `frontend/Cargo.lock` record the exact Rust dependency graphs
for the workspace and excluded frontend. Before redistribution, review those
graphs with an appropriate license-audit or SBOM tool for the intended build
and feature set.

## MiniRust and the SemR operator slice

`lean/semr/MiniRust.lean` contains a generated translation of the selected
MiniRust specification at revision `e8666821f7ee06282199e126a623679f8df85a36`,
preceded by Trust's hand-authored Specr-compatible primitive prelude. The
translation's upstream revision marker and existing byte identity are retained.

The exact upstream [Apache license text](LICENSES/MiniRust-APACHE.txt) and
[MIT license text](LICENSES/MiniRust-MIT.txt) accompany the translated material.
[Provenance and byte hashes](LICENSES/MiniRust.json) bind them to the
[pinned upstream source](https://github.com/minirust/minirust/tree/e8666821f7ee06282199e126a623679f8df85a36).
TrustIr-authored sources remain under the repository's Apache-2.0 terms.
