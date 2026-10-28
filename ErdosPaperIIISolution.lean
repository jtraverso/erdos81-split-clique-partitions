/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import PaperIII.ReuseFinal
public import PaperIII.OfPartition

/-!
# Proofs of the statements in `Challenge.lean`

The definitions are copied verbatim from `ErdosPaperIIIChallenge.lean`. The theorems are proved from the
Paper III library (namespace `PaperIII`): `PaperIII.Theorem_1_1` and `PaperIII.Corollary_1_2`
(`PaperIII/ReuseFinal.lean`, where AX1 and AX2 are discharged from the registered
formalizations of the asymptotic triangle-packing gap and of the Nash–Williams theorem),
transported to an arbitrary split graph through `PaperIII.SplitGraph.ofPartition`.
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

/-! ### Bridges to the Paper III library -/

section Bridges

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem isTrianglePacking_iff (P : Finset (Finset V)) :
    IsTrianglePacking G P ↔ PaperIII.IsTrianglePacking G P := by
  unfold IsTrianglePacking PaperIII.IsTrianglePacking
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun t ht => SimpleGraph.mem_cliqueFinset_iff.1 (h1 ht),
      fun s hs t ht hst => h2 s hs t ht hst⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun t ht => SimpleGraph.mem_cliqueFinset_iff.2 (h1 t ht),
      fun s hs t ht hst => h2 hs ht hst⟩

theorem nu3_eq_paperIII : nu3 G = PaperIII.nu3 G := by
  unfold nu3 PaperIII.nu3
  simp only [isTrianglePacking_iff]

/-- The clique partitions of `H`, by size. -/
def cpSet {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj] :
    Set ℕ :=
  {k | ∃ P : Finset (Finset W),
    (∀ c ∈ P, H.IsClique (c : Set W)) ∧
    P.card = k ∧
    ∀ e ∈ H.edgeFinset, ∃! c, c ∈ P ∧ ∀ v ∈ e, v ∈ c}

/-- The edges, as two-element cliques, form a clique partition. -/
theorem cpSet_nonempty {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] : (cpSet H).Nonempty := by
  refine ⟨_, H.edgeFinset.image Sym2.toFinset, ?_, rfl, ?_⟩
  · intro c hc
    obtain ⟨f, hf, rfl⟩ := mem_image.1 hc
    induction f using Sym2.ind with
    | _ x y =>
      have hxy : H.Adj x y := by simpa using hf
      rw [Sym2.toFinset_mk_eq, coe_insert, coe_singleton]
      exact SimpleGraph.isClique_pair.2 fun _ => hxy
  · intro f hf
    induction f using Sym2.ind with
    | _ x y =>
      have hxy : x ≠ y := H.ne_of_adj (by simpa using hf)
      refine ⟨s(x, y).toFinset, ⟨mem_image_of_mem _ hf, fun v hv => ?_⟩, ?_⟩
      · rw [Sym2.toFinset_mk_eq]
        rcases Sym2.mem_iff.1 hv with rfl | rfl <;> simp
      · rintro c ⟨hc, hcov⟩
        obtain ⟨g, -, rfl⟩ := mem_image.1 hc
        induction g using Sym2.ind with
        | _ a b =>
          have hx := hcov x (Sym2.mem_mk_left _ _)
          have hy := hcov y (Sym2.mem_mk_right _ _)
          rw [Sym2.toFinset_mk_eq] at hx hy ⊢
          rw [Sym2.toFinset_mk_eq]
          simp only [mem_insert, mem_singleton] at hx hy
          rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
          · exact absurd rfl hxy
          · rfl
          · exact Finset.pair_comm _ _
          · exact absurd rfl hxy

/-- Clique partitions transport along graph isomorphisms. -/
theorem cpSet_subset_of_iso {W₁ W₂ : Type} [Fintype W₁] [DecidableEq W₁] [Fintype W₂]
    [DecidableEq W₂] {H₁ : SimpleGraph W₁} [DecidableRel H₁.Adj] {H₂ : SimpleGraph W₂}
    [DecidableRel H₂.Adj] (e : H₁ ≃g H₂) : cpSet H₁ ⊆ cpSet H₂ := by
  rintro k ⟨P, hcl, hcard, hcov⟩
  refine ⟨P.image (fun c => c.map e.toEquiv.toEmbedding), ?_, ?_, ?_⟩
  · intro c' hc'
    obtain ⟨c, hc, rfl⟩ := mem_image.1 hc'
    intro x hx y hy hxy
    simp only [coe_map, Set.mem_image, mem_coe, Equiv.coe_toEmbedding] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    have hab : a ≠ b := fun h => hxy (by rw [h])
    exact e.map_adj_iff.2 (hcl c hc ha hb hab)
  · rw [card_image_of_injective _ (fun c d h => Finset.map_injective _ h)]
    exact hcard
  · intro f hf
    induction f using Sym2.ind with
    | _ x y =>
      have hxy : H₂.Adj x y := by simpa using hf
      have hxy' : H₁.Adj (e.symm x) (e.symm y) := e.symm.map_adj_iff.2 (by simpa using hxy)
      obtain ⟨c, ⟨hcP, hcov'⟩, huniq⟩ := hcov s(e.symm x, e.symm y) (by simpa using hxy')
      have hmem : ∀ v ∈ s(x, y), e.symm v ∈ c := by
        intro v hv
        rcases Sym2.mem_iff.1 hv with rfl | rfl
        · exact hcov' _ (Sym2.mem_mk_left _ _)
        · exact hcov' _ (Sym2.mem_mk_right _ _)
      refine ⟨c.map e.toEquiv.toEmbedding, ⟨mem_image_of_mem _ hcP, fun v hv => ?_⟩, ?_⟩
      · exact mem_map.2 ⟨e.symm v, hmem v hv, by simp⟩
      · rintro c'' ⟨hc'', hcov''⟩
        obtain ⟨c₀, hc₀, rfl⟩ := mem_image.1 hc''
        have hpull : ∀ v ∈ s(x, y), e.symm v ∈ c₀ := by
          intro v hv
          obtain ⟨a, ha, hav⟩ := mem_map.1 (hcov'' v hv)
          have : e.symm v = a := by
            rw [← hav]
            simp
          rw [this]
          exact ha
        have h0 : c₀ = c := huniq c₀ ⟨hc₀, fun w hw => by
          rcases Sym2.mem_iff.1 hw with rfl | rfl
          · exact hpull x (Sym2.mem_mk_left _ _)
          · exact hpull y (Sym2.mem_mk_right _ _)⟩
        rw [h0]

/-- A split partition gives the finsets required by the Paper III library. -/
theorem exists_finset_partition (S : SplitPartition G) :
    ∃ K I : Finset V, K ∪ I = Finset.univ ∧ Disjoint K I ∧ G.IsClique (K : Set V) ∧
      G.IsIndepSet (I : Set V) := by
  classical
  refine ⟨Finset.univ.filter (· ∈ S.clique), Finset.univ.filter (· ∈ S.independent), ?_, ?_, ?_, ?_⟩
  · ext v
    have := Set.ext_iff.1 S.cover v
    simp only [Set.mem_union, Set.mem_univ, iff_true] at this
    simpa using this
  · exact Finset.disjoint_filter.2 fun v _ h1 h2 => Set.disjoint_left.1 S.disjoint h1 h2
  · have : ((Finset.univ.filter (· ∈ S.clique) : Finset V) : Set V) = S.clique := by
      ext v
      simp
    rw [this]
    exact S.isClique
  · have : ((Finset.univ.filter (· ∈ S.independent) : Finset V) : Set V) = S.independent := by
      ext v
      simp
    rw [this]
    exact S.isIndepSet

end Bridges

/-- **Paper III, Theorem 1.1.** There is a constant `C` such that every split graph `G` on `n`
vertices satisfies `|E(G)| − 2ν₃(G) ≤ n²/6 + C·n`. -/
theorem theorem_1_1 :
    ∃ C : ℝ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      IsSplit G →
        (G.edgeFinset.card : ℝ) - 2 * (nu3 G : ℝ) ≤
          (Fintype.card V : ℝ) ^ 2 / 6 + C * (Fintype.card V : ℝ) := by
  obtain ⟨C, hC⟩ := PaperIII.Theorem_1_1_of_splitPartition PaperIII.Theorem_1_1
  refine ⟨C, fun {V} _ _ G _ hG => ?_⟩
  obtain ⟨S⟩ := hG
  obtain ⟨K, I, hcover, hdisj, hclique, hindep⟩ := exists_finset_partition G S
  have h := hC G K I hcover hdisj hclique hindep
  rw [nu3_eq_paperIII]
  push_cast at h
  exact h

/-- **Paper III, Corollary 1.2.** There is a constant `C` such that every split graph `G` on `n`
vertices has a clique partition with at most `n²/6 + C·n` cliques. -/
theorem corollary_1_2 :
    ∃ C : ℝ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      IsSplit G → (cp G : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 / 6 + C * (Fintype.card V : ℝ) := by
  obtain ⟨C, hC⟩ := PaperIII.Corollary_1_2
  refine ⟨C, fun {V} _ _ G _ hG => ?_⟩
  obtain ⟨S⟩ := hG
  obtain ⟨K, I, hcover, hdisj, hclique, hindep⟩ := exists_finset_partition G S
  set Gs := PaperIII.SplitGraph.ofPartition G K I hcover hdisj hclique hindep with hGs
  have h := hC Gs
  rw [PaperIII.SplitGraph.ofPartition_n] at h
  have hcp : cp G ≤ Gs.cp := by
    have hmem : Gs.cp ∈ cpSet Gs.graph := Nat.sInf_mem (cpSet_nonempty Gs.graph)
    exact Nat.sInf_le
      (cpSet_subset_of_iso (PaperIII.SplitGraph.ofPartitionIso G K I hcover hdisj hclique hindep) hmem)
  calc (cp G : ℝ) ≤ (Gs.cp : ℝ) := by exact_mod_cast hcp
    _ ≤ _ := h

end ErdosPaperIII
