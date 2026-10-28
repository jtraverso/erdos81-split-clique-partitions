/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Paper III — Linear-error clique partitions of split graphs

J. P. Traverso Gianini, *Integral split partitions* (Paper III of the Erdős #81 series, preprint
v1.6). For a split graph `G` on `n` vertices let `ν₃(G)` be the maximum number of pairwise
edge-disjoint triangles and `cp(G)` the clique-partition number. Statements in the namespace
`ErdosPaperIII`:

* `theorem_1_1`: there is a constant `C` such that `|E(G)| − 2ν₃(G) ≤ n²/6 + C·n` for every split
  graph `G` (Theorem 1.1);
* `corollary_1_2`: there is a constant `C` such that `cp(G) ≤ n²/6 + C·n` for every split graph
  (Corollary 1.2).

Split graphs and triangle packings use the same definitions as the author's registered Palomar
entries `jtraverso/chordal-split-threshold-graphs` (`SplitPartition`, `IsSplit`) and
`jtraverso/asymptotic-triangle-packing` (`IsTrianglePacking`). The definitions below are part of
the audited statements; the Mathlib definitions used are reproduced in `MATHLIB_DEFINITIONS.md`.
-/

@[expose] public section

namespace ErdosPaperIII

open Finset

/-- A partition of the vertices into a clique and an independent set. -/
structure SplitPartition {V : Type*} (G : SimpleGraph V) where
  /-- The clique part. -/
  clique : Set V
  /-- The independent part. -/
  independent : Set V
  /-- The clique part induces a complete graph. -/
  isClique : G.IsClique clique
  /-- The independent part contains no edges. -/
  isIndepSet : G.IsIndepSet independent
  /-- No vertex belongs to both parts. -/
  disjoint : Disjoint clique independent
  /-- Every vertex belongs to one of the parts. -/
  cover : clique ∪ independent = Set.univ

/-- A graph is split if it admits a split partition. -/
def IsSplit {V : Type*} (G : SimpleGraph V) : Prop := Nonempty (SplitPartition G)

/-- An (integral) triangle packing of `G`: a family of triangles of `G`, any two of which share
at most one vertex, i.e. no edge. -/
def IsTrianglePacking {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (P : Finset (Finset V)) : Prop :=
  P ⊆ G.cliqueFinset 3 ∧ ∀ s ∈ P, ∀ t ∈ P, s ≠ t → #(s ∩ t) ≤ 1

/-- `ν₃(G)`: the maximum number of pairwise edge-disjoint triangles of `G`. -/
noncomputable def nu3 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℕ :=
  sSup {k | ∃ P : Finset (Finset V), IsTrianglePacking G P ∧ P.card = k}

/-- The clique-partition number `cp(G)`: the least number of cliques of `G` whose vertex sets
cover each edge of `G` exactly once. -/
noncomputable def cp {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℕ :=
  sInf {k | ∃ P : Finset (Finset V),
    (∀ c ∈ P, G.IsClique (c : Set V)) ∧
    P.card = k ∧
    ∀ e ∈ G.edgeFinset, ∃! c, c ∈ P ∧ ∀ v ∈ e, v ∈ c}

/-- **Paper III, Theorem 1.1.** There is a constant `C` such that every split graph `G` on `n`
vertices satisfies `|E(G)| − 2ν₃(G) ≤ n²/6 + C·n`. -/
theorem theorem_1_1 :
    ∃ C : ℝ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      IsSplit G →
        (G.edgeFinset.card : ℝ) - 2 * (nu3 G : ℝ) ≤
          (Fintype.card V : ℝ) ^ 2 / 6 + C * (Fintype.card V : ℝ) := by
  sorry

/-- **Paper III, Corollary 1.2.** There is a constant `C` such that every split graph `G` on `n`
vertices has a clique partition with at most `n²/6 + C·n` cliques. -/
theorem corollary_1_2 :
    ∃ C : ℝ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      IsSplit G → (cp G : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 / 6 + C * (Fintype.card V : ℝ) := by
  sorry

end ErdosPaperIII
