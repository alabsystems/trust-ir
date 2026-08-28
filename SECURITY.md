# Security policy

## Coverage

Security maintenance is best-effort for the latest public TrustIr source
snapshot and the newest active 0.x release.
Historical snapshots, private combined-workspace layouts, internal reports,
and third-party forks are not maintained release artifacts.

Because TrustIr carries proof claims, a soundness or authority defect can be a
security issue even when it does not involve memory corruption.

## Reporting

Please do not open a public issue for a suspected vulnerability or a defect
that could silently overstate proof authority. Email
`andrewyates.name@gmail.com` and include as much of the following as possible:

- what the problem is and why it matters;
- the exact commit or release identifier, Rust version, platform, and selected
  Cargo features;
- the command, API, artifact format, and proof gate involved;
- a minimal reproducer or malformed module/lineage artifact;
- whether public discussion would make exploitation or proof laundering
  easier.

If plain email is not suitable for the report, say so in the first message so
another confidential channel can be arranged.

There is no response-time SLA. Reports are reviewed when maintainer capacity
allows; credible issues are investigated privately, and a fix may land before
technical details are published.

## Examples in scope

- forged, replayed, stale, or misbound evidence accepted as `Certified`;
- a false lineage-closure, module-identity, or checker-authority result;
- unsafe handling of untrusted module, certificate, request-bundle, or lineage
  input, including serious resource-exhaustion flaws;
- unintended file access, command execution, or trust-boundary escape in
  shipped tooling;
- publication or packaging flaws that expose credentials or substitute an
  unattested dependency revision.

Ordinary unsupported input, documented `unknown` or fail-closed results,
benchmark regressions without a security consequence, and behavior confined to
private scratch material can use the normal support channels.
