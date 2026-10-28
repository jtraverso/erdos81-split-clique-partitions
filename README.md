# Linear-error clique partitions of split graphs (Erdős #81, Paper III) in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

A Lean 4 / Mathlib formalization of the main results of the preprint *Linear-Error Clique
Partitions of Split Graphs via Structured Triangle Packing* (Erdős #81 series, Paper III,
v1.6, [doi:10.5281/zenodo.23478825](https://doi.org/10.5281/zenodo.23478825); series repository
[jtraverso/erdos-81-chordal-clique-partitions](https://github.com/jtraverso/erdos-81-chordal-clique-partitions)).

For a finite simple graph `G` on `n` vertices let `ν₃(G)` be the largest number of pairwise
edge-disjoint triangles of `G`, and `cp(G)` the least number of cliques of `G` covering every edge
exactly once (a clique partition). A graph is *split* if its vertices can be partitioned into a
clique and an independent set.

| Lean (namespace `ErdosPaperIII`) | Statement |
|---|---|
| `theorem_1_1` | There is `C` such that every split graph satisfies `|E(G)| − 2ν₃(G) ≤ n²/6 + C·n`. |
| `corollary_1_2` | There is `C` such that every split graph has a clique partition with at most `n²/6 + C·n` cliques. |

The coefficient `1/6` is sharp for split graphs; `C` is existential.

## Files

- [`ErdosPaperIIIChallenge.lean`](ErdosPaperIIIChallenge.lean): the definitions (`SplitPartition`,
  `IsSplit`, `IsTrianglePacking`, `nu3`, `cp`) and the two statements; it imports only Mathlib.
  `SplitPartition` and `IsSplit` are copied verbatim from
  [PALOMAR-2026-10-18-000006](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-18-000006&version=1),
  `IsTrianglePacking` from
  [PALOMAR-2026-10-15-000011](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-15-000011&version=1).
- [`ErdosPaperIIISolution.lean`](ErdosPaperIIISolution.lean) and [`PaperIII/`](PaperIII): the proofs.
- [`comparator.json`](comparator.json), [`MATHLIB_DEFINITIONS.md`](MATHLIB_DEFINITIONS.md),
  [`formalization.yaml`](formalization.yaml).

## How the proof is organized

The library works with split graphs given by a profile (`PaperIII.SplitGraph`: clique size `p`,
independent set of size `q`, neighbourhoods `N i`). `PaperIII/Main.lean` proves the bound
`Φ(G) = |E| − 2ν₃ ≤ n²/6 + C·n` from two inputs, stated as hypotheses `AX1Assumption` and
`AX2Assumption` (`PaperIII/AXDefs.lean`), by the article's corridor analysis: explicit triangle
packings from edge colourings and factorizations (E-3 to E-8), the double-factor inequality and
dispersion bounds (Proposition 10.1), and an induction erasing independent vertices.

The two inputs are discharged in `PaperIII/ReuseFinal.lean` from registered formalizations:

- **AX1**, the fractional–integral triangle-packing gap `τ₃*(G) − ν₃(G) ≤ εn²` for all large `n`, is
  `LeanPool.AsymptoticTrianglePacking.triangleCoverPackingGap` of
  [jtraverso/asymptotic-triangle-packing](https://github.com/jtraverso/asymptotic-triangle-packing)
  (PALOMAR-2026-10-15-000011), with the identification of the two `ν₃` in
  `PaperIII/YusterBridgeReuse.lean`;
- **AX2**, exact triangle decompositions of large triangle-divisible graphs with minimum degree at
  least `(0.9 + ε)n`, follows from the Nash–Williams theorem with minimum degree `3n/4`
  (`NashWilliams18.PaperI.nash_williams_via_paperII` of
  [jtraverso/nash-williams-lean](https://github.com/jtraverso/nash-williams-lean),
  PALOMAR-2026-10-21-000009).

Both are pinned dependencies in `lakefile.toml`. The Solution transports the result to an
arbitrary split `SimpleGraph` through the profile presentation `PaperIII.SplitGraph.ofPartition`
and its graph isomorphism.

## Provenance

The proofs come from the author's Lean freeze `lean_v1.4_freeze` of the article (Lean 4.28),
whose proofs were produced with Harmonic's Aristotle under the author's direction. For this
package, Claude (Claude Code) ported the 29-module core to Lean `v4.35.0-rc3` and the module system,
rewrote the proofs broken by the Mathlib update, replaced the vendored developments of the freeze
(about 360 modules) by the two registered formalizations above, and wrote the Challenge/Solution
pair. The freeze itself is unchanged in the series repository.

## Checks

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`. `lake build` of the whole
dependency chain; no `sorry`; `#print axioms` gives only `propext`, `Classical.choice`,
`Quot.sound` for both theorems; the elaborated statements and definitions of the Challenge and the
Solution are identical (`pp.all`).

```
lake build
```

The first build compiles the two pinned dependencies (about 1,150 modules in all).
