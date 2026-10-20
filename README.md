# The Nash–Williams triangle-decomposition theorem in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

This repository is the Palomar submission of the Lean formalization accompanying *Triangle
decompositions I: Formalizing the Nash–Williams theorem in Lean* (preprint 1.0, 2026). All
statements are in the namespace `NashWilliamsTheorem`:

1. `nash_williams`, **the Nash–Williams theorem for large graphs (Delcourt–Postle, Theorem 1.8).**
   There is `N` such that every finite simple graph on `n ≥ N` vertices that is
   triangle-divisible (`3 ∣ e(G)` and every degree even, `NashWilliams.IsTriangleDivisible`) and
   satisfies `3n ≤ 4δ(G)` has a triangle decomposition (`NashWilliams.HasTriangleDecomposition`):
   a family of triangles of `G` such that every edge of `G` lies in exactly one of them.
2. `fractional_nash_williams`, **the fractional threshold (Delcourt–Postle, Theorem 1.4).** Every
   finite simple graph with `3n ≤ 4δ(G)` has a fractional triangle decomposition; neither
   divisibility nor large order is assumed.
3. `fractional_stability`, **fractional stability (Delcourt–Postle, Theorem 1.6), with an order
   threshold.** There is `σ₀ > 0` such that for every `0 < σ ≤ σ₀` there are `ε > 0` and `n₀` such
   that every graph on `n ≥ n₀` vertices with `δ(G) ≥ (3/4 − ε)n` has a fractional triangle
   decomposition or is `σ`-extremal (`NashWilliams18.IsExtremal`). The original statement has no
   order threshold.

The theorems are due to Delcourt and Postle. Their decomposition step applies their Theorem 13.16,
whose proof they assign to a separate manuscript (reference 17 of their paper); no public version
of it was located. The proof formalized here follows their division into extremal and
non-extremal cases and does **not** assume Theorem 13.16: the extremal residuals are decomposed
with typed absorption results (Paper II of the series, developed under
`PartitionedTriangleAbsorption/`), and the non-extremal case with a protected covering-round
argument proved in the development.

The definitions used by the statements are reproduced in `Challenge.lean` verbatim, with the
same names as in the library (`RequestProject/NashWilliamsBasic.lean` and
`RequestProject/NW18/Defs.lean`). `comparator.json` selects only the three theorems; the
definitions are not selected separately and enter the check only as part of the theorem
statements that use them.

## Files

- [`Challenge.lean`](Challenge.lean): the definitions and the audited statements. It imports only
  Mathlib.
- [`Solution.lean`](Solution.lean): the three theorems, each obtained from the library:
  `NashWilliams18.PaperI.nash_williams_via_paperII` (`RequestProject/NW18/PaperIIAssembly.lean`),
  `NashWilliams.Frac.exists_fractional_weights` (`RequestProject/Fractional/Final.lean`) and
  `NashWilliams.Frac.theorem_1_6_proof` (`RequestProject/FracStab/Main.lean`).
- [`RequestProject/`](RequestProject) and [`PartitionedTriangleAbsorption/`](PartitionedTriangleAbsorption):
  the 1,070 Lean modules of the proof (the import closure of the final assembly), byte-identical to
  the source freeze `PAPER_I_LEAN_20261020_ALIGNED_v3`.
- [`comparator.json`](comparator.json): the theorems that are compared.
- [`MATHLIB_DEFINITIONS.md`](MATHLIB_DEFINITIONS.md): verbatim copies of the Mathlib definitions
  used.
- [`formalization.yaml`](formalization.yaml): provenance, sources and process.

## How the proof goes

* **Fractional inputs.** The fractional threshold (Theorem 1.4) is proved by Delcourt–Postle's
  dual discharging argument and Farkas' lemma; fractional stability (Theorem 1.6) and its
  regular form (Theorem 2.6) by the stability analysis of the dual.
* **Case division.** As in Delcourt–Postle, a graph is either close to one of the extremal
  configurations or not. In the extremal cases a preliminary triangle packing covers the
  exceptional vertices and leaves a partitioned residual whose remaining triangles must have
  prescribed types.
* **Replacement branches.** The residuals are decomposed with the typed results of Paper II: a
  semidense theorem (`theorem146_F0`), a nearly complete typed theorem (`idealized_F12`, used
  through `theorem147_F1` and `theorem147_F2`) and a four-colour bridge
  (`margin_four_colour_decomposition`). The non-extremal case uses a protected covering round
  (`roundUnivSpec124_holds`) followed by a terminal absorption construction. The matching input
  is the Ehard–Glock–Joos theorem (`Pseudorandom.theorem_1_2`).
* **Audit.** `RequestProject/NW18/AuditPaperIIAssembly.lean` walks the proof-dependency closure
  of the main theorem, requires the replacement inputs, forbids the earlier final theorem and the
  hypothesis `Theorem1316Statement`, and checks that only `propext`, `Classical.choice` and
  `Quot.sound` are used.

## Build evidence

A recorded clean build of the 1,070 modules (Lean `v4.35.0-rc3`, Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`) passed the audit above, with only the three standard
axioms in the six final axiom queries and no `sorry` warning. The sources here are those of the
freeze after an author-header correction that changes only the initial header comment of each
file; the header-corrected sources were not rebuilt locally before this submission.

## Sources

* M. Delcourt, L. Postle, *A Proof of Nash-Williams' Conjecture*, arXiv:2606.11178 (2026),
  doi:10.48550/arXiv.2606.11178.
* C. St. J. A. Nash-Williams, *An unsolved problem concerning decomposition of graphs into
  triangles*, in: Combinatorial Theory and its Applications III, North-Holland (1970), 1179–1183.
* S. Ehard, S. Glock, F. Joos, *Pseudorandom hypergraph matchings*; formalized separately by the
  author as Palomar entry
  [PALOMAR-2026-10-17-000004](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-17-000004&version=1).
* J. P. Traverso Gianini, *Triangle decompositions I: Formalizing the Nash–Williams theorem in
  Lean*, and *Triangle decompositions II: Robust absorption for typed triangles*, preprints 1.0
  (2026).

## Authorship and use of AI

The author directed the work and is responsible for the arguments and the code. Aristotle, by
Harmonic, contributed to exploring approaches, developing proofs and formalizing and reviewing
them in Lean; Claude, by Anthropic, and ChatGPT/Codex, by OpenAI, were used to explore and check
arguments and to prepare the documents and this package. Lean checks everything mechanically. See
`formalization.yaml`.

## Building

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```bash
lake exe cache get
lake build
```

The full build compiles 1,070 project modules and takes many CPU hours.
