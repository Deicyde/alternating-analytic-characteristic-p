# Verification evidence

`publication-verification.json`, `publication-build.log` and `publication-axioms.log` record the current complete build and exhaustive audit. They cover every proof-library and comparator-solution declaration, including private and generated helpers, with only the standard axioms `propext`, `Classical.choice` and `Quot.sound` permitted.

`challenge.lean` imports only Mathlib. Its two theorems assume universal analytic smoothness of alternating precomposition and conclude `False`: the first is the general statement used in the characteristic-two challenge; the second fixes an arbitrary prescribed positive-characteristic field and a degree at least its characteristic and quantifies over Banach source and target spaces. These are direct corollaries of the full construction. They do not restate every constructive conclusion or the factorial classification, which remain proved and audited in the unchanged library.

The challenge contains two deliberate theorem placeholders. It is never imported into `solution.lean` or the axiom audit, and those placeholders are excluded from proof-development counts. The source manifest authenticates the challenge, solution, comparator configuration, metadata and CI configuration. The verifier requires its probe to cover the entire library and solution and rejects unlisted proof modules. The negative-control receipts document these checks.

`comparator-local.json` and `comparator-local.log` identify the exact theorem names, file hashes and outcome of the official comparator run. It compares statement dependencies, checks permitted axioms and replays the solution in Lean's default kernel. Local macOS runs use upstream's development launcher without the Linux sandbox. The separate GitHub Actions job uses a fresh checkout, real Landrun and the documented AF_UNIX restriction; consult Actions for remote status.

`metadata-validation.json` records validation against the official formalization.yaml v0.4 schema. `comparator-semantic-audit.json` records the statement review, including correspondence with the characteristic-two challenge and the precise scope of the prescribed-field corollary.

Earlier full-owned-declarations, standalone and component records preserve the original 89-module, 2,021-declaration library checks before comparator integration. The original library source files are unchanged. Component checks enumerated non-internal roots; final exhaustive audits also cover private and generated roots. Dependency sources are pinned, existing Mathlib caches were reused locally, and caches are excluded from the repository.

The paper-coverage audit distinguishes proved results from external classifications, announcements, open problems and an unnecessary planning abstraction. Source provenance and editorial changes are preserved. Jury timeouts remain abstentions and are separate from kernel verification; no globally clean model-jury result is claimed.
