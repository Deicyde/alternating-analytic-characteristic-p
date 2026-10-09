# Alternating bundles and analytic descent

This repository holds the paper *Alternating bundles and analytic descent* (Jack McCarthy, October 2026) and a Lean 4 / Mathlib formalization of all its numbered results.

The paper asks when the construction E, F ↦ Alt^k(E; F) of bounded alternating maps is analytic: as a functor on normed spaces over a nontrivially normed field K, and on analytic vector bundles. In short:

- The functor is always C^∞. It is analytic on all hom spaces exactly when k! ≠ 0 in K (Corollary 6.2).
- Over a base with finite coordinates, it takes analytic bundles to analytic bundles in every characteristic (Corollary 4.6).
- In characteristic p with k ≥ p it can fail: there are Banach counterexamples over every such field (Theorem 6.1), and, over complete fields, for scalar targets exactly when K is not spherically complete (Theorem 6.3).

## Status

All 76 numbered claims of the paper are proved in Lean. [challenge.md](challenge.md) lists them, one row per claim, with links to the Lean statement and its proof, and notes where the Lean statement differs from the paper.

No human expert has reviewed the paper or the Lean statements yet.

## Layout

| Path | Contents |
|---|---|
| [paper/](paper/) | The manuscript, PDF and LaTeX. |
| [challenge.md](challenge.md) | The claim ledger. |
| [Challenges/](Challenges/) | Each claim stated in Lean with `sorry`, plus a comparator config `<ID>.json`. |
| [Solutions/](Solutions/) | The same statements, proved from the library. |
| [AlternatingAnalytic/](AlternatingAnalytic/) | The library (see below). |
| [challenge.lean](challenge.lean), [solution.lean](solution.lean), [comparator.json](comparator.json) | The original six-statement comparator challenge. |
| [scripts/](scripts/) | `check_claim.py` checks one claim end to end; `run_lean.py` runs Lean with a memory limit. |
| [sources/](sources/) | The manuscript as it stood when formalization started (2026-09-23). |

Where the library proves each part of the paper:

| Paper | Directory |
|---|---|
| Sections 2–3: bundles, descent through closed subspaces | `Bundle/`, `Descent/` |
| Section 4: positive results, the bundle theorem | `Analysis/` (factorial, spherical, finite-coordinate, c₀ and ℓ¹ files), `Geometry/` |
| Section 5: exterior powers, dual tests | `Exterior/` |
| Section 6 and Appendix F: obstructions, scalar counterexample | `MainTheorem.lean`, `Scalar/` |
| Section 7: analytic differential forms | `Forms/` |
| Appendix B: the finite-field multiplier theorem | `Algebra/` |
| Appendices C–E: Laurent construction, base change | `Analysis/` (`Laurent*`, `BaseChange*`), `Laurent/` |
| Appendix G: universal analytic reflection | `Analysis/` (tensor files), `Tensor/` |
| Appendix H: no largest analytic domain | `Category/`, `Analysis/` (`Determinant*`, `Padded*`) |
| Appendix I: coordinate methods | `Coordinates/` |

The ledger names the exact declarations for each claim.

## Building and checking

The project uses Lean v4.34.0-rc2 and Mathlib from the fork `Deicyde/mathlib4` at `2b73d98`. That is upstream Mathlib `0383a80e64` plus one commit, [mathlib4#43548](https://github.com/leanprover-community/mathlib4/pull/43548), which shows that smoothness reflects along linear isometries with closed range. Because of that commit, `lake exe cache get` leaves about a thousand Mathlib files to build locally.

```sh
lake exe cache get
lake build
python3 scripts/check_claim.py ThmF_1
```

`check_claim.py` confirms that the challenge's code is unchanged since the ledger was created, builds the challenge and solution, checks that the proof uses only `propext`, `Classical.choice` and `Quot.sound`, and checks that both files state the same theorem. To run the [comparator](https://github.com/leanprover/comparator) (revision `19e111e`) on a claim, run `lake env <comparator> Challenges/<ID>.json`. Use `comparator.json` for the original challenge.

## How this was made

The paper was developed with Anthropic's Claude and OpenAI's Codex. The original library was formalized with Codex and Autoform in September 2026. The per-claim challenges and the 31 claims the original library did not cover were formalized with Claude Code on 2026-10-08. [formalization.yaml](formalization.yaml) records the details.

## License

No license has been chosen yet.
