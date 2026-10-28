/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import PaperIII.Defs

/-!
# Paper III — public API item A: `SplitGraph.ofPartition` and `Theorem_1_1_of_splitPartition`

This file provides the bridge between the *profile* presentation of a split graph
(`PaperIII.SplitGraph`, see `Defs.lean`) and an arbitrary finite simple graph `H` on a
vertex type `V` that comes equipped with a split partition `V = K ⊎ I` (`K` a clique,
`I` an independent set):

* `SplitGraph.ofPartition` builds the profile presentation out of `(H, K, I)`;
* `SplitGraph.ofPartitionIso` is the graph isomorphism `(ofPartition …).graph ≃g H`;
* `nu3_congr_of_iso` and `edgeCount_congr_of_iso` are the (general) isomorphism-invariance
  lemmas for the triangle-packing number and the edge count;
* `ofPartition_n`, `ofPartition_edgeCount`, `ofPartition_nu3`, `ofPartition_Phi` transport the
  profile invariants, and `Theorem_1_1_of_splitPartition` states the headline bound for
  arbitrary split graphs, taking the `SplitGraph`-level bound as a hypothesis `hmain`
  (so that this file only depends on `Defs.lean` and Mathlib).
-/

@[expose] public section

namespace PaperIII

/-! ## A3. Isomorphism invariance of the edge count and of `ν₃` -/

section Invariance

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
  {H₁ : SimpleGraph V} [DecidableRel H₁.Adj] {H₂ : SimpleGraph W} [DecidableRel H₂.Adj]

omit [DecidableEq V] [DecidableEq W] in
/-- An isomorphism of finite simple graphs preserves the number of edges. -/
theorem edgeCount_congr_of_iso (e : H₁ ≃g H₂) : H₁.edgeFinset.card = H₂.edgeFinset.card :=
  e.card_edgeFinset_eq

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableRel H₁.Adj] [DecidableRel H₂.Adj] in
/-- An isomorphism maps `3`-cliques to `3`-cliques. -/
theorem isNClique_image_of_iso (e : H₁ ≃g H₂) {t : Finset V} (ht : H₁.IsNClique 3 t) :
    H₂.IsNClique 3 (t.image e) := by
  have hinjV : Function.Injective (e : V → W) := e.toEquiv.injective
  constructor
  · rintro x hx y hy hxy
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    have hab : a ≠ b := fun h => hxy (by rw [h])
    exact (e.map_adj_iff).2 (ht.1 ha hb hab)
  · rw [Finset.card_image_of_injective _ hinjV]
    exact ht.2

omit [Fintype V] [Fintype W] [DecidableRel H₁.Adj] [DecidableRel H₂.Adj] in
/-- Transport of a triangle packing along an isomorphism. -/
theorem isTrianglePacking_image_of_iso (e : H₁ ≃g H₂) {T : Finset (Finset V)}
    (hT : IsTrianglePacking H₁ T) :
    IsTrianglePacking H₂ (T.image (fun t => t.image e)) := by
  have hinjV : Function.Injective (e : V → W) := e.toEquiv.injective
  constructor
  · intro t ht
    simp only [Finset.mem_image] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    exact isNClique_image_of_iso e (hT.1 s hs)
  · intro t₁ h₁ t₂ h₂ hne
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at h₁ h₂
    obtain ⟨s₁, hs₁, rfl⟩ := h₁
    obtain ⟨s₂, hs₂, rfl⟩ := h₂
    have hs : s₁ ≠ s₂ := fun h => hne (by rw [h])
    have hcap : s₁.image (e : V → W) ∩ s₂.image (e : V → W) = (s₁ ∩ s₂).image (e : V → W) := by
      rw [Finset.image_inter _ _ hinjV]
    rw [hcap, Finset.card_image_of_injective _ hinjV]
    exact hT.2 hs₁ hs₂ hs

omit [Fintype V] [Fintype W] [DecidableRel H₁.Adj] [DecidableRel H₂.Adj] in
/-- The set of achievable triangle-packing sizes is preserved by isomorphisms. -/
theorem exists_packing_card_of_iso (e : H₁ ≃g H₂) {k : ℕ}
    (h : ∃ T : Finset (Finset V), IsTrianglePacking H₁ T ∧ T.card = k) :
    ∃ T : Finset (Finset W), IsTrianglePacking H₂ T ∧ T.card = k := by
  obtain ⟨T, hT, hcard⟩ := h
  have hinjV : Function.Injective (e : V → W) := e.toEquiv.injective
  have hinj : Function.Injective (fun t : Finset V => t.image (e : V → W)) :=
    fun s t hst => Finset.image_injective hinjV hst
  refine ⟨T.image (fun t => t.image e), isTrianglePacking_image_of_iso e hT, ?_⟩
  rw [Finset.card_image_of_injective _ hinj, hcard]

omit [Fintype V] [Fintype W] [DecidableRel H₁.Adj] [DecidableRel H₂.Adj] in
/-- `ν₃` is an isomorphism invariant. -/
theorem nu3_congr_of_iso (e : H₁ ≃g H₂) : nu3 H₁ = nu3 H₂ := by
  unfold nu3
  congr 1
  ext k
  exact ⟨fun h => exists_packing_card_of_iso e h, fun h => exists_packing_card_of_iso e.symm h⟩

end Invariance

/-- The composite `Fin s.card → s → α` is injective. -/
theorem equivFin_symm_coe_injective {α : Type*} {s : Finset α} {a b : Fin s.card}
    (h : (s.equivFin.symm a : α) = (s.equivFin.symm b : α)) : a = b := by
  have : s.equivFin.symm a = s.equivFin.symm b := Subtype.ext h
  simpa using congrArg s.equivFin this

namespace SplitGraph

/-! ## A1. The generic constructor -/

section OfPartition

variable {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
  (K I : Finset V)

/-- The profile presentation of a graph `H` equipped with a split partition
`V = K ⊎ I` (`K` a clique, `I` an independent set): the clique has `K.card` vertices,
the independent set has `I.card` vertices, and the `i`-th independent vertex is joined to
exactly those clique vertices adjacent to it in `H`. -/
noncomputable def ofPartition
    (_hcover : K ∪ I = Finset.univ) (_hdisj : Disjoint K I)
    (_hclique : H.IsClique (K : Set V)) (_hindep : H.IsIndepSet (I : Set V)) : SplitGraph where
  p := K.card
  q := I.card
  N i := Finset.univ.filter
    fun a : Fin K.card => H.Adj ((I.equivFin.symm i : V)) ((K.equivFin.symm a : V))

variable (hcover : K ∪ I = Finset.univ) (hdisj : Disjoint K I)
  (hclique : H.IsClique (K : Set V)) (hindep : H.IsIndepSet (I : Set V))

@[simp] theorem ofPartition_p : (ofPartition H K I hcover hdisj hclique hindep).p = K.card := rfl

@[simp] theorem ofPartition_q : (ofPartition H K I hcover hdisj hclique hindep).q = I.card := rfl

/-- The underlying vertex bijection of `ofPartitionIso`. -/
noncomputable def ofPartitionEquiv : (Fin K.card ⊕ Fin I.card) ≃ V :=
  Equiv.ofBijective
    (Sum.elim (fun a => (K.equivFin.symm a : V)) (fun i => (I.equivFin.symm i : V)))
    (by
      constructor
      · rintro (a | i) (b | j) h <;>
          simp only [Sum.elim_inl, Sum.elim_inr] at h
        · have hab : a = b := by
            have : K.equivFin.symm a = K.equivFin.symm b := Subtype.ext h
            simpa using congrArg K.equivFin this
          rw [hab]
        · have hK : (K.equivFin.symm a : V) ∈ K := (K.equivFin.symm a).2
          have hI : (I.equivFin.symm j : V) ∈ I := (I.equivFin.symm j).2
          rw [h] at hK
          exact absurd hI (Finset.disjoint_left.1 hdisj hK)
        · have hI : (I.equivFin.symm i : V) ∈ I := (I.equivFin.symm i).2
          have hK : (K.equivFin.symm b : V) ∈ K := (K.equivFin.symm b).2
          rw [h] at hI
          exact absurd hI (Finset.disjoint_left.1 hdisj hK)
        · have hij : i = j := by
            have : I.equivFin.symm i = I.equivFin.symm j := Subtype.ext h
            simpa using congrArg I.equivFin this
          rw [hij]
      · intro v
        have hv : v ∈ K ∪ I := by rw [hcover]; exact Finset.mem_univ v
        rcases Finset.mem_union.1 hv with hK | hI
        · exact ⟨Sum.inl (K.equivFin ⟨v, hK⟩), by simp⟩
        · exact ⟨Sum.inr (I.equivFin ⟨v, hI⟩), by simp⟩)

@[simp] theorem ofPartitionEquiv_inl (a : Fin K.card) :
    ofPartitionEquiv K I hcover hdisj (Sum.inl a) = (K.equivFin.symm a : V) := rfl

@[simp] theorem ofPartitionEquiv_inr (i : Fin I.card) :
    ofPartitionEquiv K I hcover hdisj (Sum.inr i) = (I.equivFin.symm i : V) := rfl

/-- Membership in the clique-neighborhood of the `i`-th independent vertex. -/
theorem mem_ofPartition_N (i : Fin I.card) (a : Fin K.card) :
    a ∈ (ofPartition H K I hcover hdisj hclique hindep).N i ↔
      H.Adj ((I.equivFin.symm i : V)) ((K.equivFin.symm a : V)) := by
  show a ∈ Finset.univ.filter
      (fun x : Fin K.card => H.Adj ((I.equivFin.symm i : V)) ((K.equivFin.symm x : V))) ↔ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-! ## A2. The graph isomorphism -/

/-- The graph built from a split partition of `H` is isomorphic to `H`. -/
noncomputable def ofPartitionIso :
    (ofPartition H K I hcover hdisj hclique hindep).graph ≃g H where
  toEquiv := ofPartitionEquiv K I hcover hdisj
  map_rel_iff' := by
    rintro (a | i) (b | j)
    · constructor
      · intro h
        show a ≠ b
        intro hc
        exact h.ne (by rw [hc])
      · intro h
        have hab : a ≠ b := h
        exact hclique (K.equivFin.symm a).2 (K.equivFin.symm b).2
          fun hc => hab (equivFin_symm_coe_injective hc)
    · constructor
      · intro h
        exact (mem_ofPartition_N H K I hcover hdisj hclique hindep j a).2 h.symm
      · intro h
        exact ((mem_ofPartition_N H K I hcover hdisj hclique hindep j a).1 h).symm
    · constructor
      · intro h
        exact (mem_ofPartition_N H K I hcover hdisj hclique hindep i b).2 h
      · intro h
        exact (mem_ofPartition_N H K I hcover hdisj hclique hindep i b).1 h
    · constructor
      · intro h
        rcases eq_or_ne i j with rfl | hij
        · exact absurd h H.irrefl
        · exact absurd h (hindep (I.equivFin.symm i).2 (I.equivFin.symm j).2 h.ne)
      · intro h
        exact (h : False).elim

/-! ## A4. The transported invariants -/

theorem ofPartition_n : (ofPartition H K I hcover hdisj hclique hindep).n = Fintype.card V := by
  show K.card + I.card = Fintype.card V
  rw [← Finset.card_union_of_disjoint hdisj, hcover, Finset.card_univ]

theorem ofPartition_edgeCount :
    (ofPartition H K I hcover hdisj hclique hindep).edgeCount = H.edgeFinset.card :=
  edgeCount_congr_of_iso (ofPartitionIso H K I hcover hdisj hclique hindep)

theorem ofPartition_nu3 : (ofPartition H K I hcover hdisj hclique hindep).nu3' = nu3 H :=
  nu3_congr_of_iso (ofPartitionIso H K I hcover hdisj hclique hindep)

theorem ofPartition_Phi : (ofPartition H K I hcover hdisj hclique hindep).Phi
    = (H.edgeFinset.card : ℤ) - 2 * (nu3 H : ℤ) := by
  unfold Phi
  rw [ofPartition_edgeCount, ofPartition_nu3]

end OfPartition

end SplitGraph

/-! ## The headline corollary, parametrized by the main bound -/

/-- The `Φ ≤ n²/6 + C·n` bound for arbitrary split graphs presented by a clique/independent-set
partition, deduced from the corresponding bound `hmain` for `SplitGraph`s. -/
theorem Theorem_1_1_of_splitPartition
    (hmain : ∃ C : ℝ, ∀ G : SplitGraph, ((G.Phi : ℤ) : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ)) :
    ∃ C : ℝ, ∀ {V : Type} [Fintype V] [DecidableEq V]
      (H : SimpleGraph V) [DecidableRel H.Adj] (K I : Finset V),
      K ∪ I = Finset.univ → Disjoint K I → H.IsClique (K : Set V) → H.IsIndepSet (I : Set V) →
      (((H.edgeFinset.card : ℤ) - 2 * (nu3 H : ℤ) : ℤ) : ℝ)
        ≤ (Fintype.card V : ℝ) ^ 2 / 6 + C * (Fintype.card V : ℝ) := by
  obtain ⟨C, hC⟩ := hmain
  refine ⟨C, ?_⟩
  intro V _ _ H _ K I hcover hdisj hclique hindep
  have h := hC (SplitGraph.ofPartition H K I hcover hdisj hclique hindep)
  rwa [SplitGraph.ofPartition_Phi, SplitGraph.ofPartition_n] at h

end PaperIII
