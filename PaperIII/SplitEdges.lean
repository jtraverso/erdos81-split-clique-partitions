/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PaperIII.Defs

/-!
# Paper III — Edge decomposition of the split graph

`E(G) = (clique edges) ⊔ (cross edges)`, the resulting sum decomposition for any edge
weighting, and the edge count `|E(G)| = C(p,2) + Σᵢ dᵢ` (used by E-3.1's uniform cover
and by the `T(G)` identity).  Also the triangle classification: every triangle of a
split graph is `KKK` or `KKI`.
-/

@[expose] public section

namespace PaperIII

namespace SplitGraph

variable (G : SplitGraph)

/-- The clique edges of the split graph (both endpoints in `K`). -/
def cliqueEdges : Finset (Sym2 G.V) :=
  (⊤ : SimpleGraph (Fin G.p)).edgeFinset.image (Sym2.map Sum.inl)

/-- The cross edges `{inl a, inr i}` with `a ∈ N i`. -/
def crossEdges : Finset (Sym2 G.V) :=
  (Finset.univ.sigma fun i => G.N i).image fun x => s(Sum.inl x.2, Sum.inr x.1)

theorem edgeFinset_eq : G.graph.edgeFinset = G.cliqueEdges ∪ G.crossEdges := by
  ext e
  constructor
  · intro he
    rw [Finset.mem_union]
    revert he
    refine Sym2.ind (fun x y => ?_) e
    intro he
    have h : G.graph.Adj x y := by
      simpa [SimpleGraph.mem_edgeFinset] using he
    rcases x with a | i <;> rcases y with b | j
    · refine Or.inl (Finset.mem_image.mpr ⟨s(a, b), ?_, rfl⟩)
      simpa [SimpleGraph.mem_edgeFinset, graph, Adj] using h
    · exact Or.inr (Finset.mem_image.mpr ⟨⟨j, a⟩, Finset.mem_sigma.mpr
        ⟨Finset.mem_univ _, by simpa [graph, Adj] using h⟩, rfl⟩)
    · refine Or.inr (Finset.mem_image.mpr ⟨⟨i, b⟩, Finset.mem_sigma.mpr
        ⟨Finset.mem_univ _, by simpa [graph, Adj] using h⟩, ?_⟩)
      exact Sym2.eq_swap
    · exact absurd h (by simp [graph, Adj])
  · intro he
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
      revert he'
      refine Sym2.ind (fun a b => ?_) e'
      intro he'
      have hab : a ≠ b := by simpa [SimpleGraph.mem_edgeFinset] using he'
      exact SimpleGraph.mem_edgeFinset.mpr (by simpa [graph, Adj] using hab)
    · obtain ⟨⟨i, a⟩, hia, rfl⟩ := Finset.mem_image.mp he
      have ha : a ∈ G.N i := (Finset.mem_sigma.mp hia).2
      exact SimpleGraph.mem_edgeFinset.mpr (by simpa [graph, Adj] using ha)

theorem disjoint_cliqueEdges_crossEdges : Disjoint G.cliqueEdges G.crossEdges := by
  rw [Finset.disjoint_left]
  intro e he he'
  obtain ⟨e', _, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨⟨i, a⟩, _, heq⟩ := Finset.mem_image.mp he'
  revert heq
  refine Sym2.ind (fun x y => ?_) e'
  intro heq
  rw [Sym2.map_mk, Sym2.eq_iff] at heq
  rcases heq with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> exact absurd h₂ (by simp)

/-- Sum decomposition over the edges of a split graph. -/
theorem sum_edgeFinset {β : Type*} [AddCommMonoid β] (f : Sym2 G.V → β) :
    ∑ e ∈ G.graph.edgeFinset, f e =
      (∑ e ∈ (⊤ : SimpleGraph (Fin G.p)).edgeFinset, f (e.map Sum.inl)) +
      ∑ i, ∑ a ∈ G.N i, f s(Sum.inl a, Sum.inr i) := by
  rw [edgeFinset_eq, Finset.sum_union (G.disjoint_cliqueEdges_crossEdges)]
  congr 1
  · rw [cliqueEdges, Finset.sum_image]
    intro e₁ _ e₂ _ h
    exact Sym2.map.injective Sum.inl_injective h
  · rw [crossEdges, Finset.sum_image, Finset.sum_sigma]
    intro x hx y hy h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Sigma.ext (by simpa using h₂) (by simpa using heq_of_eq h₁)
    · exact absurd h₁ (by simp)

/-- `|E(G)| = C(p,2) + Σᵢ dᵢ` (LEDGER §0 / the `T(G)` identity input). -/
theorem edgeCount_eq : G.edgeCount = G.p.choose 2 + ∑ i, G.d i := by
  have h := G.sum_edgeFinset (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
  have htop := SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin G.p)
  rw [Fintype.card_fin] at htop
  rw [edgeCount, h, htop]
  simp [d]

/-- **Triangle classification**: every triangle of a split graph is `KKK` (three clique
vertices) or `KKI` (two adjacent clique vertices in the common neighborhood of one
independent vertex). -/
theorem triangle_cases {t : Finset G.V} (ht : t ∈ G.graph.cliqueFinset 3) :
    (∃ a b c : Fin G.p, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      t = {Sum.inl a, Sum.inl b, Sum.inl c}) ∨
    (∃ (a b : Fin G.p) (i : Fin G.q), a ≠ b ∧ a ∈ G.N i ∧ b ∈ G.N i ∧
      t = {Sum.inl a, Sum.inl b, Sum.inr i}) := by
  rw [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff] at ht
  obtain ⟨hclique, hcard⟩ := ht
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hcard
  have hx : x ∈ ({x, y, z} : Finset G.V) := by simp
  have hy : y ∈ ({x, y, z} : Finset G.V) := by simp
  have hz : z ∈ ({x, y, z} : Finset G.V) := by simp
  have adjxy : G.graph.Adj x y := hclique hx hy hxy
  have adjxz : G.graph.Adj x z := hclique hx hz hxz
  have adjyz : G.graph.Adj y z := hclique hy hz hyz
  rcases x with a | i <;> rcases y with b | j <;> rcases z with c | k
  · exact Or.inl ⟨a, b, c, by simpa using hxy, by simpa using hxz, by simpa using hyz,
      rfl⟩
  · exact Or.inr ⟨a, b, k, by simpa using hxy, (adjxz : a ∈ G.N k),
      (adjyz : b ∈ G.N k), rfl⟩
  · refine Or.inr ⟨a, c, j, by simpa using hxz, (adjxy : a ∈ G.N j),
      ((adjyz.symm : G.graph.Adj (Sum.inl c) (Sum.inr j)) : c ∈ G.N j), ?_⟩
    ext v; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  · exact absurd adjyz (by simp [graph, Adj])
  · refine Or.inr ⟨b, c, i, by simpa using hyz, (adjxy.symm : b ∈ G.N i),
      (adjxz.symm : c ∈ G.N i), ?_⟩
    ext v; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  · exact absurd adjxz (by simp [graph, Adj])
  · exact absurd adjxy (by simp [graph, Adj])
  · exact absurd adjxy (by simp [graph, Adj])

end SplitGraph

end PaperIII
