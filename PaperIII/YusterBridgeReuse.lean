/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.YusterEdge

/-!
# Nibble — ③ definitional bridge: PaperIII-style triangle packing ↦ ν₃

Standalone, Mathlib-only. Connects the PaperIII packing predicate `IsTrianglePacking` (triangles pairwise
sharing ≤ 1 vertex = edge-disjoint) to `Nibble.nu3` (max matching of the edge-based triangle hypergraph).
This is the architecture-independent half of the cross-project bridge `Nibble.nu3 ↔ PaperIII.nu3` needed to
wire the Yuster/nibble bound into `PaperIII/AX.lean`.

* `IsTrianglePacking` — the PaperIII predicate, replicated verbatim.
* `trianglePacking_card_le_nu3` — any such packing `T` has `T.card ≤ ν₃ G` (map `t ↦ t.powersetCard 2`
  gives a hypergraph matching of equal cardinality; injective + pairwise-disjoint edge-sets).

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

@[expose] public section

open Finset SimpleGraph Hypergraph

namespace Nibble.YusterE

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- PaperIII-style triangle packing: triangles pairwise sharing at most one vertex (edge-disjoint). -/
def IsTrianglePacking (T : Finset (Finset V)) : Prop :=
  (∀ t ∈ T, G.IsNClique 3 t) ∧
    (T : Set (Finset V)).Pairwise fun t₁ t₂ => (t₁ ∩ t₂).card ≤ 1

/-- The edge-set map `t ↦ t.powersetCard 2` is injective on triangles. -/
private theorem powersetCard2_injOn :
    Set.InjOn (fun t => t.powersetCard 2) (G.cliqueFinset 3 : Set (Finset V)) := by
  intro t ht t' ht' heq
  rw [Finset.mem_coe, SimpleGraph.mem_cliqueFinset_iff] at ht ht'
  have key : ∀ {a b : Finset V}, G.IsNClique 3 a → G.IsNClique 3 b →
      a.powersetCard 2 = b.powersetCard 2 → a ⊆ b := by
    intro a b ha hb hab x hx
    obtain ⟨y, hy, hyx⟩ : ∃ y ∈ a, y ≠ x := by
      have hne : (a.erase x).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hx, ha.card_eq]; omega
      obtain ⟨y, hy⟩ := hne
      exact ⟨y, Finset.mem_of_mem_erase hy, Finset.ne_of_mem_erase hy⟩
    have hxy : ({x, y} : Finset V) ∈ a.powersetCard 2 := by
      rw [Finset.mem_powersetCard]
      refine ⟨?_, Finset.card_pair (fun h => hyx h.symm)⟩
      intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl; exact hx; exact hy
    rw [hab, Finset.mem_powersetCard] at hxy
    exact hxy.1 (by simp)
  exact Finset.Subset.antisymm (key ht ht' heq) (key ht' ht heq.symm)

/-- **③ bridge direction.** Any PaperIII-style triangle packing `T` gives a matching of the edge-based
triangle hypergraph of the same cardinality, so `T.card ≤ ν₃ G`. -/
theorem trianglePacking_card_le_nu3 {T : Finset (Finset V)} (hT : IsTrianglePacking G T) :
    T.card ≤ nu3 G := by
  set M := T.image (fun t => t.powersetCard 2) with hM
  have hcard : M.card = T.card :=
    Finset.card_image_of_injOn ((powersetCard2_injOn G).mono (by
      intro t ht
      exact Finset.mem_coe.mpr (SimpleGraph.mem_cliqueFinset_iff.mpr (hT.1 t (Finset.mem_coe.mp ht)))))
  have hmatch : IsMatching (triangleHypergraphE G) M := by
    constructor
    · intro E hE
      rw [hM, Finset.mem_image] at hE
      obtain ⟨t, htT, rfl⟩ := hE
      rw [triangleHypergraphE, Finset.mem_image]
      exact ⟨t, SimpleGraph.mem_cliqueFinset_iff.mpr (hT.1 t htT), rfl⟩
    · intro E hE F hF hEF
      rw [hM, Finset.mem_image] at hE hF
      obtain ⟨t₁, ht₁, rfl⟩ := hE
      obtain ⟨t₂, ht₂, rfl⟩ := hF
      have htne : t₁ ≠ t₂ := fun h => hEF (by rw [h])
      -- disjoint edge-sets: a common edge would force |t₁ ∩ t₂| ≥ 2
      rw [Finset.disjoint_left]
      intro e he₁ he₂
      rw [Finset.mem_powersetCard] at he₁ he₂
      have hesub : e ⊆ t₁ ∩ t₂ := Finset.subset_inter he₁.1 he₂.1
      have : 2 ≤ (t₁ ∩ t₂).card := he₁.2 ▸ Finset.card_le_card hesub
      have hle := hT.2 (Finset.mem_coe.mpr ht₁) (Finset.mem_coe.mpr ht₂) htne
      omega
  rw [← hcard]
  exact nu3_ge G hmatch

omit [Fintype V] [DecidableRel G.Adj] in
/-- The union of all `2`-subsets of a triangle is the triangle. -/
private theorem powersetCard2_sup {t : Finset V} (ht : G.IsNClique 3 t) :
    (t.powersetCard 2).sup id = t := by
  apply Finset.Subset.antisymm
  · intro x hx
    rw [Finset.mem_sup] at hx
    obtain ⟨e, he, hxe⟩ := hx
    rw [Finset.mem_powersetCard] at he
    exact he.1 hxe
  · intro a ha
    obtain ⟨b, hb, hab⟩ : ∃ b ∈ t, b ≠ a := by
      have hne : (t.erase a).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem ha, ht.card_eq]; omega
      obtain ⟨b, hbm⟩ := hne
      exact ⟨b, Finset.mem_of_mem_erase hbm, Finset.ne_of_mem_erase hbm⟩
    have hmem : ({a, b} : Finset V) ∈ t.powersetCard 2 := by
      rw [Finset.mem_powersetCard]
      refine ⟨?_, Finset.card_pair (fun h => hab h.symm)⟩
      intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl; exact ha; exact hb
    exact Finset.le_sup (f := id) hmem (by simp)

/-- **③ bridge, reverse direction.** Any matching of the edge-based triangle hypergraph yields a
PaperIII-style triangle packing of the same cardinality. Together with `trianglePacking_card_le_nu3`
this identifies `ν₃` with the PaperIII edge-disjoint triangle packing number. -/
theorem matching_gives_trianglePacking {M : Finset (Finset (Finset V))}
    (hM : IsMatching (triangleHypergraphE G) M) :
    ∃ T : Finset (Finset V), IsTrianglePacking G T ∧ T.card = M.card := by
  have htri : ∀ E ∈ M, ∃ t, G.IsNClique 3 t ∧ E = t.powersetCard 2 ∧ E.sup id = t := by
    intro E hE
    have := hM.subset hE
    rw [triangleHypergraphE, Finset.mem_image] at this
    obtain ⟨t, ht, rfl⟩ := this
    exact ⟨t, SimpleGraph.mem_cliqueFinset_iff.mp ht, rfl,
      powersetCard2_sup G (SimpleGraph.mem_cliqueFinset_iff.mp ht)⟩
  refine ⟨M.image (fun E => E.sup id), ⟨?_, ?_⟩, ?_⟩
  · intro t ht
    rw [Finset.mem_image] at ht
    obtain ⟨E, hE, rfl⟩ := ht
    obtain ⟨s, hs, _, hsup⟩ := htri E hE
    rw [hsup]; exact hs
  · intro t₁ ht₁ t₂ ht₂ hne
    rw [Finset.mem_coe, Finset.mem_image] at ht₁ ht₂
    obtain ⟨E₁, hE₁, rfl⟩ := ht₁
    obtain ⟨E₂, hE₂, rfl⟩ := ht₂
    obtain ⟨s₁, hs₁, hE₁eq, hsup₁⟩ := htri E₁ hE₁
    obtain ⟨s₂, hs₂, hE₂eq, hsup₂⟩ := htri E₂ hE₂
    by_contra hcon
    push_neg at hcon
    obtain ⟨e, hesub, he2⟩ : ∃ e : Finset V, e ⊆ E₁.sup id ∩ E₂.sup id ∧ e.card = 2 := by
      obtain ⟨e, he⟩ := Finset.exists_subset_card_eq (by omega : 2 ≤ (E₁.sup id ∩ E₂.sup id).card)
      exact ⟨e, he.1, he.2⟩
    have hEne : E₁ ≠ E₂ := fun h => hne (by rw [h])
    have hd := hM.disjoint E₁ hE₁ E₂ hE₂ hEne
    rw [Finset.disjoint_left] at hd
    apply hd (a := e)
    · rw [hE₁eq, Finset.mem_powersetCard]
      exact ⟨(Finset.subset_inter_iff.mp hesub).1.trans (by rw [hsup₁]), he2⟩
    · rw [hE₂eq, Finset.mem_powersetCard]
      exact ⟨(Finset.subset_inter_iff.mp hesub).2.trans (by rw [hsup₂]), he2⟩
  · apply Finset.card_image_of_injOn
    intro E₁ hE₁ E₂ hE₂ heq
    obtain ⟨s₁, _, hE₁eq, hsup₁⟩ := htri E₁ hE₁
    obtain ⟨s₂, _, hE₂eq, hsup₂⟩ := htri E₂ hE₂
    have hs : s₁ = s₂ := by rw [← hsup₁, ← hsup₂]; exact heq
    rw [hE₁eq, hE₂eq, hs]

/-- **③ bridge, full identification.** `ν₃ G` equals the PaperIII edge-disjoint triangle packing number
`sSup {k | ∃ T, IsTrianglePacking G T ∧ T.card = k}` — verbatim the `sSup` form of `PaperIII.nu3`, so the
cross-project identification is definitional once the (replicated) `IsTrianglePacking` predicates align. -/
theorem nu3_eq_trianglePacking_sSup :
    (nu3 G : ℕ) = sSup {k | ∃ T : Finset (Finset V), IsTrianglePacking G T ∧ T.card = k} := by
  classical
  set S := {k | ∃ T : Finset (Finset V), IsTrianglePacking G T ∧ T.card = k} with hS
  have hSne : S.Nonempty := ⟨0, ∅, ⟨by simp, by simp⟩, by simp⟩
  have hSbdd : BddAbove S := by
    refine ⟨nu3 G, ?_⟩
    rintro k ⟨T, hT, rfl⟩
    exact trianglePacking_card_le_nu3 G hT
  apply le_antisymm
  · have hne : ((triangleHypergraphE G).powerset.filter
        (fun M => IsMatching (triangleHypergraphE G) M)).Nonempty :=
      ⟨∅, by rw [Finset.mem_filter, Finset.mem_powerset]; exact ⟨by simp, by constructor <;> simp⟩⟩
    obtain ⟨M₀, hM₀mem, hM₀eq⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
    rw [Finset.mem_filter, Finset.mem_powerset] at hM₀mem
    obtain ⟨T, hT, hTcard⟩ := matching_gives_trianglePacking G hM₀mem.2
    have hnu : (nu3 G : ℕ) = T.card := by rw [nu3, hM₀eq, hTcard]
    rw [hnu]
    exact le_csSup hSbdd ⟨T, hT, rfl⟩
  · apply csSup_le hSne
    rintro k ⟨T, hT, rfl⟩
    exact trianglePacking_card_le_nu3 G hT

end Nibble.YusterE
