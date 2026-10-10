# Alternating bundles and analytic descent

[![Comparator](https://github.com/Deicyde/alternating-analytic-characteristic-p/actions/workflows/comparator.yml/badge.svg)](https://github.com/Deicyde/alternating-analytic-characteristic-p/actions/workflows/comparator.yml)

This repository holds the paper [*Alternating bundles and analytic descent*](paper/charp.pdf) (Jack McCarthy, October 2026) and a Lean 4 / Mathlib formalization of its numbered results.

The paper asks when the construction E, F ↦ Alt^k(E; F) of bounded alternating maps is analytic: as a functor on normed spaces over a nontrivially normed field K, and on analytic vector bundles. In short:

- The functor is always C^∞. It is analytic on all hom spaces exactly when k! ≠ 0 in K (Corollary 6.2).
- Over a base with finite coordinates, it takes analytic bundles to analytic bundles in every characteristic (Corollary 4.6).
- In characteristic p with k ≥ p it can fail: there are Banach counterexamples over every such field (Theorem 6.1), and, over complete fields, for scalar targets exactly when K is not spherically complete (Theorem 6.3).

## Status

Every theorem, proposition, lemma and corollary of the paper except Proposition 6.6 has a Lean proof of a corresponding statement, as do three remarks and two unnumbered statements: 76 ledger rows in all (Theorems 4.5 and 6.1 have two rows each). [challenge.md](challenge.md) lists them, one row per claim, with links to the Lean statement and its proof, and notes where the Lean statement differs from the paper. Proposition 6.6 has a written proof only.

CI runs the comparator on the original six-statement challenge. The 76 ledger checks are run locally with `scripts/check_claim.py`; [challenge.md](challenge.md) records the last run. The paper cites the commit of this repository that holds the Lean code and the ledger; `main` is that commit plus the final copy of the paper.

## Layout

| Path | Contents |
|---|---|
| [paper/](paper/) | The manuscript, PDF and LaTeX, and `Section8.lean`, the definition displayed in Section 8 of the paper. |
| [challenge.md](challenge.md) | The claim ledger. |
| [Challenges/](Challenges/) | Each claim stated in Lean with `sorry`, plus a comparator config `<ID>.json`. |
| [Solutions/](Solutions/) | The same statements, proved from the library. |
| [AlternatingAnalytic/](AlternatingAnalytic/) | The library (see below). |
| [challenge.lean](challenge.lean), [solution.lean](solution.lean), [comparator.json](comparator.json) | The original six-statement comparator challenge. |
| [scripts/](scripts/) | `check_claim.py` checks one claim end to end; `run_lean.py` limits how many Lean processes run at once, to keep memory use down. |
| [sources/](sources/) | The manuscript as it stood when formalization started (2026-09-23). |

Roughly where the library proves each part of the paper:

| Paper | Directory |
|---|---|
| Sections 2–3: bundles, descent through closed subspaces | `Bundle/`, `Descent/` |
| Section 4: positive results, the bundle theorem | `Analysis/` (factorial, spherical, finite-coordinate, c₀ and ℓ¹ files), `Geometry/` |
| Section 5: exterior powers, dual tests | `Exterior/` |
| Section 6 and Appendix F: obstructions, scalar counterexample | `Main.lean`, `MainTheorem.lean`, `Scalar/`, `Analysis/` (`AlternatingAction*`, `Factorial*`, `Shear*`), `Geometry/ShearBundleGeneral.lean` |
| Section 7: analytic differential forms | `Forms/` |
| Appendix A: preliminaries | Mathlib, `Analysis/PositiveCharacteristic.lean` |
| Appendix B: the finite-field multiplier theorem | `Algebra/` |
| Appendices C–E: Laurent construction, base change | `Analysis/` (`Laurent*`, `BaseChange*`), `Laurent/` |
| Appendix G: universal analytic reflection | `Analysis/` (tensor files), `Tensor/` |
| Appendix H: no largest analytic domain | `Category/`, `Analysis/` (`Determinant*`, `Padded*`) |
| Appendix I: coordinate methods | `Coordinates/` |

The ledger names the exact declarations for each claim.

## Building and checking

The project uses Lean v4.34.0-rc2 and Mathlib from the fork `Deicyde/mathlib4` at `2b73d98` (tag `alternating-analytic-characteristic-p` on the fork). That is upstream Mathlib `0383a80e64` plus one commit, [mathlib4#43548](https://github.com/leanprover-community/mathlib4/pull/43548), which shows that smoothness reflects along linear isometries with closed range. Because of that commit, `lake exe cache get` leaves about a thousand Mathlib files to build locally.

Install Lean with [elan](https://lean-lang.org/install/); `lake` then fetches the toolchain. The scripts need macOS or Linux.

```sh
lake exe cache get
lake build
python3 scripts/check_claim.py ThmF_1
```

A full build runs several Lean processes at once, and each one that imports the library needs about 2.4 GB. With less than about 32 GB of memory, build one target at a time, for example `python3 scripts/run_lean.py --build Solutions.ThmF_1`, instead of a bare `lake build`. `lake build` also compiles `challenge.lean` and `Challenges/`, which are statements only, so the warnings `declaration uses 'sorry'` from those files are expected. `lake env lean paper/Section8.lean` checks the definition displayed in Section 8 of the paper.

`check_claim.py` needs the git history and the tag `ledger-base`, so use an ordinary clone, not a ZIP download or a shallow clone. It confirms that the challenge's code is unchanged since the ledger was created, builds the challenge and solution, checks that the proof uses only `propext`, `Classical.choice` and `Quot.sound`, and checks that both files state the same theorem. The [comparator](https://github.com/leanprover/comparator) (revision `19e111e`) needs Linux, `landrun` and `lean4export`; [.github/workflows/comparator.yml](.github/workflows/comparator.yml) is a working recipe and runs it on `comparator.json`, the original challenge, on every push. Each claim also has a config `Challenges/<ID>.json`; these have not yet been run through the comparator.

## How this was made

The paper was developed with Anthropic's Claude and OpenAI's Codex. The original library was formalized with Codex and Autoform between 2026-09-23 and 2026-10-01. The per-claim challenges and the 31 claims the original library did not cover were formalized with Claude Code on 2026-10-08. [formalization.yaml](formalization.yaml) records the details.

The proof of `cpolynomialAt_nsmul_compContinuousLinearMapCLM` in `AlternatingAnalytic/Analysis/FactorialInvertible.lean` is adapted from Sébastien Gouëzel's Mathlib pull request [#43338](https://github.com/leanprover-community/mathlib4/pull/43338), which is released under the Apache 2.0 license.

## License

This repository, including the paper, is released under the Apache License 2.0. See [LICENSE](LICENSE).
