/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import PaperIII.E_B
public import PaperIII.DiracHamilton

/-!
# Paper III — E-8 divisibility correction (helper file)

Self-contained combinatorial helpers for `clique_divisible_correction`.

Given a dense graph `H` on `Fin p` (here `H = Kₚ − D` with `δ(H) ≥ 0.9 p`), we delete a
further bounded set `C` of edges so that `H − C` is *triangle-divisible*:

* all degrees become even (parity correction, `exists_parity_edges`, via the already-proved
  `pathCorrection_odd_iff` applied along a Hamiltonian ordering of `H`);
* the number of edges becomes `≡ 0 (mod 3)` (`exists_parity_cycle`, deleting a single short
  even cycle of length `0`, `4`, or `5`);

while keeping every vertex-degree loss `≤ 6`, hence min-degree `≥ 0.9 p − 6`.

The main export is `exists_divisible_correction_edges`.
-/

@[expose] public section

namespace PaperIII

open Finset SimpleGraph

variable {p : ℕ}

/-- Incidence degree of a vertex `v` in an edge set `S`: the number of edges of `S`
containing `v`. -/
def incDeg {V : Type*} [DecidableEq V] (S : Finset (Sym2 V)) (v : V) : ℕ :=
  (S.filter (fun e => v ∈ e)).card

/-- Incidence degree is additive over a disjoint union of edge sets. -/
lemma incDeg_union_of_disjoint {V : Type*} [DecidableEq V] {A B : Finset (Sym2 V)}
    (h : Disjoint A B) (v : V) :
    incDeg (A ∪ B) v = incDeg A v + incDeg B v := by
  unfold incDeg
  rw [Finset.filter_union, Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter_filter h

/-- Monotonicity of incidence degree. -/
lemma incDeg_mono {V : Type*} [DecidableEq V] {A B : Finset (Sym2 V)} (h : A ⊆ B) (v : V) :
    incDeg A v ≤ incDeg B v := by
  unfold incDeg
  exact Finset.card_le_card (Finset.filter_subset_filter _ h)

/-- Incidence degree of `v` over *all* edges of `H` equals the graph degree of `v`. -/
lemma incDeg_edgeFinset_eq_degree {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (v : V) :
    incDeg H.edgeFinset v = H.degree v := by
  have hinc : H.incidenceFinset v = H.edgeFinset.filter (fun e => v ∈ e) := by
    ext e
    rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.incidenceFinset,
      Set.mem_toFinset]
    exact Iff.rfl
  unfold incDeg
  rw [← hinc, H.card_incidenceFinset_eq_degree]

/-- Handshake lower bound: `|V| · k ≤ 2·|E(H)|` when every degree is at least `k`. -/
lemma twice_card_edgeFinset_ge {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (k : ℕ) (hd : ∀ v, k ≤ H.degree v) :
    Fintype.card V * k ≤ 2 * H.edgeFinset.card := by
  have h := H.sum_degrees_eq_twice_card_edges
  calc Fintype.card V * k = ∑ _v : V, k := by rw [Finset.sum_const, Finset.card_univ]; ring
    _ ≤ ∑ v : V, H.degree v := Finset.sum_le_sum (fun v _ => hd v)
    _ = 2 * H.edgeFinset.card := h

/-- Degree in `H − C` is `deg_H(v) − incDeg C v`, for `C` a set of edges of `H`. -/
lemma degree_deleteEdges_of_subset {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (C : Finset (Sym2 V))
    (hC : (C : Set (Sym2 V)) ⊆ H.edgeSet) (v : V) :
    (H.deleteEdges (C : Set (Sym2 V))).degree v = H.degree v - incDeg C v := by
  classical
  have hCf : C ⊆ H.edgeFinset := by
    intro e he; rw [SimpleGraph.mem_edgeFinset]; exact hC he
  rw [← incDeg_edgeFinset_eq_degree, ← incDeg_edgeFinset_eq_degree H v,
    SimpleGraph.edgeFinset_deleteEdges]
  unfold incDeg
  have key : (H.edgeFinset \ C).filter (fun e => v ∈ e)
      = H.edgeFinset.filter (fun e => v ∈ e) \ C.filter (fun e => v ∈ e) := by
    ext e; simp only [mem_filter, mem_sdiff]; tauto
  have hsub : C.filter (fun e => v ∈ e) ⊆ H.edgeFinset.filter (fun e => v ∈ e) :=
    Finset.filter_subset_filter _ hCf
  rw [key]
  have := Finset.card_sdiff_add_card_eq_card hsub
  omega

/-- Edge count of `H − C` is `|E(H)| − |C|`, for `C` a set of edges of `H`. -/
lemma edgeFinset_card_deleteEdges_of_subset {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (C : Finset (Sym2 V))
    (hC : C ⊆ H.edgeFinset) :
    (H.deleteEdges (C : Set (Sym2 V))).edgeFinset.card = H.edgeFinset.card - C.card := by
  rw [SimpleGraph.edgeFinset_deleteEdges]
  have := Finset.card_sdiff_add_card_eq_card hC
  omega

/-- **Hamiltonian ordering** of a graph with min degree `≥ p/2` (Dirac, path version):
there is a bijection `f : Fin p → Fin p` listing the vertices so that consecutive vertices
are adjacent in `H`. -/
lemma exists_hamiltonian_ordering (H : SimpleGraph (Fin p)) [DecidableRel H.Adj]
    (hp : 3 ≤ p) (hδ : ∀ v, p ≤ 2 * H.degree v) :
    ∃ f : Fin p → Fin p, Function.Bijective f ∧
      ∀ (i : ℕ) (h : i + 1 < p), H.Adj (f ⟨i, by omega⟩) (f ⟨i + 1, h⟩) :=
  hamiltonian_ordering_of_minDegree H hp hδ

/-- Every vertex meets the path-correction edge set at most twice. -/
lemma pathDegree_le_two (P : ℕ) (J : Finset (Fin (P - 1))) (w : Fin P) :
    pathDegree P J w ≤ 2 := by
  unfold pathDegree
  have hsub : (J.filter (fun j : Fin (P-1) => (w:ℕ) = (j:ℕ) ∨ (w:ℕ) = (j:ℕ)+1)) ⊆
      J.filter (fun j : Fin (P-1) => (j:ℕ) = (w:ℕ) ∨ (j:ℕ) = (w:ℕ) - 1) := by
    intro j hj; simp only [Finset.mem_filter] at hj ⊢; exact ⟨hj.1, by omega⟩
  refine le_trans (Finset.card_le_card hsub) ?_
  have h2 : (J.filter (fun j : Fin (P-1) => (j:ℕ)=(w:ℕ) ∨ (j:ℕ)=(w:ℕ)-1)).card ≤
      ({(w:ℕ), (w:ℕ)-1} : Finset ℕ).card := by
    apply Finset.card_le_card_of_injOn (f := fun j : Fin (P-1) => (j : ℕ))
    · intro j hj
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hj ⊢
      exact hj.2
    · intro j1 _ j2 _ h; exact Fin.ext h
  refine le_trans h2 (le_trans (Finset.card_insert_le _ _) ?_)
  simp

/-- **Parity correction, core.** Given a Hamiltonian ordering `f` of `H`, the image under
`f` of the path-correction edge set toggles exactly the odd-degree vertices, using `≤ p`
edges with incidence degree `≤ 2`. -/
lemma parity_core (H : SimpleGraph (Fin p)) [DecidableRel H.Adj] (hp : 3 ≤ p)
    (f : Fin p → Fin p) (hf : Function.Bijective f)
    (hadj : ∀ (i : ℕ) (h : i + 1 < p), H.Adj (f ⟨i, by omega⟩) (f ⟨i + 1, h⟩)) :
    ∃ F : Finset (Sym2 (Fin p)),
      (F : Set (Sym2 (Fin p))) ⊆ H.edgeSet ∧ F.card ≤ p ∧
      (∀ v, incDeg F v ≤ 2) ∧ (∀ v, Odd (incDeg F v) ↔ Odd (H.degree v)) := by
  classical
  let eqv : Fin p ≃ Fin p := Equiv.ofBijective f hf
  set OddSet : Finset (Fin p) := Finset.univ.filter (fun v => Odd (H.degree v)) with hOdd
  have hOEven : Even OddSet.card := by
    have := H.even_card_odd_degree_vertices; rw [hOdd]; convert this using 2
  set O : Finset (Fin p) := OddSet.image eqv.symm with hO
  have hOcardEven : Even O.card := by
    rw [hO, Finset.card_image_of_injective _ eqv.symm.injective]; exact hOEven
  set e : Fin (p-1) → Sym2 (Fin p) := fun j => s(f ⟨j.1, by omega⟩, f ⟨j.1+1, by omega⟩) with he_def
  have he_inj : Function.Injective e := by
    intro j1 j2 h
    simp only [he_def, Sym2.eq_iff] at h
    apply Fin.ext
    rcases h with ⟨h1, _⟩ | ⟨h1, h2⟩
    · have := Fin.ext_iff.mp (hf.1 h1); simpa using this
    · exfalso
      have ha := Fin.ext_iff.mp (hf.1 h1)
      have hb := Fin.ext_iff.mp (hf.1 h2)
      simp only at ha hb; omega
  have hval : ∀ (v : Fin p) (k : ℕ) (hk : k < p),
      (v = f ⟨k, hk⟩) ↔ (eqv.symm v : Fin p).val = k := by
    intro v k hk
    constructor
    · intro h; subst h
      have h2 : eqv.symm (f ⟨k, hk⟩) = ⟨k, hk⟩ := by
        show eqv.symm (eqv ⟨k, hk⟩) = ⟨k, hk⟩
        rw [Equiv.symm_apply_apply]
      rw [h2]
    · intro h
      have h2 : eqv.symm v = ⟨k, hk⟩ := Fin.ext h
      have h3 := congrArg eqv h2
      rw [Equiv.apply_symm_apply] at h3
      exact h3
  have hkey : ∀ v : Fin p,
      incDeg ((pathCorrection p O).image e) v = pathDegree p (pathCorrection p O) (eqv.symm v) := by
    intro v
    unfold incDeg pathDegree
    rw [Finset.filter_image, Finset.card_image_of_injective _ he_inj]
    congr 1
    apply Finset.filter_congr
    intro j hj
    simp only [he_def, Sym2.mem_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl ((hval v j.1 (by omega)).mp h)
      · exact Or.inr ((hval v (j.1+1) (by omega)).mp h)
    · rintro (h | h)
      · exact Or.inl ((hval v j.1 (by omega)).mpr h)
      · exact Or.inr ((hval v (j.1+1) (by omega)).mpr h)
  refine ⟨(pathCorrection p O).image e, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    rw [SimpleGraph.mem_edgeSet]
    exact hadj j.1 (by omega)
  · refine le_trans (Finset.card_image_le) ?_
    refine le_trans (Finset.card_filter_le _ _) ?_
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  · intro v; rw [hkey v]; exact pathDegree_le_two p _ _
  · intro v
    rw [hkey v, pathCorrection_odd_iff p O hOcardEven (eqv.symm v), hO]
    constructor
    · intro hmem
      rw [Finset.mem_image] at hmem
      obtain ⟨a, ha, hae⟩ := hmem
      rw [eqv.symm.injective hae] at ha
      rw [hOdd, Finset.mem_filter] at ha
      exact ha.2
    · intro hodd
      rw [Finset.mem_image]
      exact ⟨v, by rw [hOdd, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hodd⟩, rfl⟩

/-- **Parity correction.** In a graph `H` on `Fin p` with min degree `≥ p/2`, there is an
edge set `F ⊆ E(H)` with `|F| ≤ p`, incidence degree `≤ 2` at every vertex, whose incidence
degrees have exactly the odd-degree vertices of `H` as their odd set. Deleting `F` makes all
degrees even. -/
lemma exists_parity_edges (H : SimpleGraph (Fin p)) [DecidableRel H.Adj]
    (hp : 3 ≤ p) (hδ : ∀ v, p ≤ 2 * H.degree v) :
    ∃ F : Finset (Sym2 (Fin p)),
      (F : Set (Sym2 (Fin p))) ⊆ H.edgeSet ∧
      F.card ≤ p ∧
      (∀ v, incDeg F v ≤ 2) ∧
      (∀ v, Odd (incDeg F v) ↔ Odd (H.degree v)) := by
  obtain ⟨f, hf, hadj⟩ := exists_hamiltonian_ordering H hp hδ
  exact parity_core H hp f hf hadj

/-- The number of neighbours `w` of `u` with `s(u,w) ∈ F` is at most `incDeg F u`. -/
lemma card_nbr_in_edgeset (H : SimpleGraph (Fin p)) [DecidableRel H.Adj]
    (F : Finset (Sym2 (Fin p))) (u : Fin p) :
    ((H.neighborFinset u).filter (fun w => s(u, w) ∈ F)).card ≤ incDeg F u := by
  unfold incDeg
  apply Finset.card_le_card_of_injOn (fun w => s(u, w))
  · intro w hw
    simp only [Finset.mem_coe, Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hw ⊢
    exact ⟨hw.2, Sym2.mem_iff.mpr (Or.inl rfl)⟩
  · intro w1 hw1 w2 hw2 h
    simp only [Finset.mem_coe, Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hw1 hw2
    rw [Sym2.eq_iff] at h
    rcases h with ⟨_, h⟩ | ⟨h1, _⟩
    · exact h
    · exact absurd h1 (H.ne_of_adj hw2.1)

/-- Lower bound on the number of "good" neighbours of `u` (adjacent, edge not in `F`). -/
lemma card_good_ge (H : SimpleGraph (Fin p)) [DecidableRel H.Adj]
    (F : Finset (Sym2 (Fin p))) (hF : ∀ v, incDeg F v ≤ 2) (u : Fin p) :
    H.degree u - 2 ≤ ((H.neighborFinset u).filter (fun w => s(u, w) ∉ F)).card := by
  have hcard := Finset.card_filter_add_card_filter_not
    (s := H.neighborFinset u) (fun w => s(u, w) ∉ F)
  rw [card_neighborFinset_eq_degree] at hcard
  have heq : (H.neighborFinset u).filter (fun w => ¬ s(u, w) ∉ F)
      = (H.neighborFinset u).filter (fun w => s(u, w) ∈ F) := by
    apply Finset.filter_congr; intro w _; simp
  rw [heq] at hcard
  have h3 := card_nbr_in_edgeset H F u
  have h4 := hF u
  omega

/-- **Good neighbour.** If `u` has enough degree, it has a neighbour `w` outside `X` with
`s(u,w) ∉ F`. -/
lemma exists_good_neighbor (H : SimpleGraph (Fin p)) [DecidableRel H.Adj]
    (F : Finset (Sym2 (Fin p))) (hF : ∀ v, incDeg F v ≤ 2) (u : Fin p)
    (X : Finset (Fin p)) (hX : X.card + 3 ≤ H.degree u) :
    ∃ w, H.Adj u w ∧ s(u, w) ∉ F ∧ w ∉ X := by
  classical
  by_contra hcon
  push_neg at hcon
  have hsub : H.neighborFinset u ⊆
      (H.neighborFinset u).filter (fun w => s(u, w) ∈ F) ∪ X := by
    intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    simp only [Finset.mem_union, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    by_cases hf : s(u, w) ∈ F
    · exact Or.inl ⟨hw, hf⟩
    · exact Or.inr (hcon w hw hf)
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le ((H.neighborFinset u).filter (fun w => s(u, w) ∈ F)) X
  have h3 := card_nbr_in_edgeset H F u
  have h4 := hF u
  rw [card_neighborFinset_eq_degree] at h1
  omega

/-- **Good common neighbour.** If `u, u'` have enough degree, they have a common neighbour
`w` outside `X` with `s(u,w), s(u',w) ∉ F`. -/
lemma exists_good_common_neighbor (H : SimpleGraph (Fin p)) [DecidableRel H.Adj]
    (F : Finset (Sym2 (Fin p))) (hF : ∀ v, incDeg F v ≤ 2) (u u' : Fin p)
    (X : Finset (Fin p)) (hX : X.card + p + 5 ≤ H.degree u + H.degree u') :
    ∃ w, H.Adj u w ∧ H.Adj u' w ∧ s(u, w) ∉ F ∧ s(u', w) ∉ F ∧ w ∉ X := by
  classical
  have hGuc := card_good_ge H F hF u
  have hGuc' := card_good_ge H F hF u'
  have hun := Finset.card_union_add_card_inter
    ((H.neighborFinset u).filter (fun w => s(u, w) ∉ F))
    ((H.neighborFinset u').filter (fun w => s(u', w) ∉ F))
  have hle : (((H.neighborFinset u).filter (fun w => s(u, w) ∉ F)) ∪
      ((H.neighborFinset u').filter (fun w => s(u', w) ∉ F))).card ≤ p := by
    have := Finset.card_le_univ (((H.neighborFinset u).filter (fun w => s(u, w) ∉ F)) ∪
      ((H.neighborFinset u').filter (fun w => s(u', w) ∉ F)))
    rwa [Fintype.card_fin] at this
  have hinter : X.card < (((H.neighborFinset u).filter (fun w => s(u, w) ∉ F)) ∩
      ((H.neighborFinset u').filter (fun w => s(u', w) ∉ F))).card := by
    omega
  obtain ⟨w, hw⟩ : ((((H.neighborFinset u).filter (fun w => s(u, w) ∉ F)) ∩
      ((H.neighborFinset u').filter (fun w => s(u', w) ∉ F))) \ X).Nonempty := by
    rw [← Finset.card_pos]
    have := Finset.le_card_sdiff X (((H.neighborFinset u).filter (fun w => s(u, w) ∉ F)) ∩
      ((H.neighborFinset u').filter (fun w => s(u', w) ∉ F)))
    omega
  simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_filter,
    SimpleGraph.mem_neighborFinset] at hw
  exact ⟨w, hw.1.1.1, hw.1.2.1, hw.1.1.2, hw.1.2.2, hw.2⟩

/-- Cardinality of the edge set of a `4`-cycle on distinct vertices. -/
lemma fourcycle_card (a b c d : Fin p)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ({s(a,b), s(b,c), s(c,d), s(a,d)} : Finset (Sym2 (Fin p))).card = 4 := by
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton] <;>
    simp [Sym2.eq_iff] <;> tauto

/-- Incidence degrees of a `4`-cycle are `≤ 2` and even. -/
lemma fourcycle_inc (a b c d : Fin p)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (v : Fin p) :
    incDeg ({s(a,b), s(b,c), s(c,d), s(a,d)} : Finset (Sym2 (Fin p))) v ≤ 2 ∧
    Even (incDeg ({s(a,b), s(b,c), s(c,d), s(a,d)} : Finset (Sym2 (Fin p))) v) := by
  rw [incDeg, Finset.card_filter,
      Finset.sum_insert (by simp [Sym2.eq_iff]; tauto),
      Finset.sum_insert (by simp [Sym2.eq_iff]; tauto),
      Finset.sum_insert (by simp [Sym2.eq_iff]; tauto),
      Finset.sum_singleton]
  simp only [Sym2.mem_iff]
  by_cases hva : v = a <;> by_cases hvb : v = b <;> by_cases hvc : v = c <;> by_cases hvd : v = d <;>
    simp_all

/-- Cardinality of the edge set of a `5`-cycle on distinct vertices. -/
lemma fivecycle_card (a b c d e : Fin p)
    (hab : a≠b)(hac:a≠c)(had:a≠d)(hae:a≠e)(hbc:b≠c)(hbd:b≠d)(hbe:b≠e)(hcd:c≠d)(hce:c≠e)(hde:d≠e) :
    ({s(a,b), s(b,c), s(c,d), s(d,e), s(a,e)} : Finset (Sym2 (Fin p))).card = 5 := by
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton] <;>
    simp [Sym2.eq_iff] <;> tauto

/-- Incidence degrees of a `5`-cycle are `≤ 2` and even. -/
lemma fivecycle_inc (a b c d e : Fin p)
    (hab : a≠b)(hac:a≠c)(had:a≠d)(hae:a≠e)(hbc:b≠c)(hbd:b≠d)(hbe:b≠e)(hcd:c≠d)(hce:c≠e)(hde:d≠e)
    (v : Fin p) :
    incDeg ({s(a,b), s(b,c), s(c,d), s(d,e), s(a,e)} : Finset (Sym2 (Fin p))) v ≤ 2 ∧
    Even (incDeg ({s(a,b), s(b,c), s(c,d), s(d,e), s(a,e)} : Finset (Sym2 (Fin p))) v) := by
  rw [incDeg, Finset.card_filter,
      Finset.sum_insert (by simp [Sym2.eq_iff]; tauto),
      Finset.sum_insert (by simp [Sym2.eq_iff]; tauto),
      Finset.sum_insert (by simp [Sym2.eq_iff]; tauto),
      Finset.sum_insert (by simp [Sym2.eq_iff]; tauto),
      Finset.sum_singleton]
  simp only [Sym2.mem_iff]
  by_cases hva : v = a <;> by_cases hvb : v = b <;> by_cases hvc : v = c <;> by_cases hvd : v = d <;>
    by_cases hve : v = e <;> simp_all

/-- **Short even cycle for the mod-3 correction.** In a dense graph `H`, avoiding a bounded
edge set `F`, one can find an edge set `G` that is either empty or a single `4`- or `5`-cycle,
so that `|G| % 3 = m` for a prescribed `m ≤ 2`, every vertex loses an even degree `≤ 2`, and
`G` is disjoint from `F`. -/
lemma exists_parity_cycle (H : SimpleGraph (Fin p)) [DecidableRel H.Adj]
    (hp : 20 ≤ p) (hδ : ∀ v, 9 * p ≤ 10 * H.degree v)
    (F : Finset (Sym2 (Fin p))) (hF : ∀ v, incDeg F v ≤ 2)
    (m : ℕ) (hm : m ≤ 2) :
    ∃ G : Finset (Sym2 (Fin p)),
      (G : Set (Sym2 (Fin p))) ⊆ H.edgeSet ∧
      Disjoint G F ∧
      (∀ v, incDeg G v ≤ 2) ∧
      (∀ v, Even (incDeg G v)) ∧
      G.card ≤ 5 ∧
      G.card % 3 = m := by
  classical
  have h0 : 0 < p := by omega
  interval_cases m
  · -- m = 0: delete nothing
    refine ⟨∅, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [incDeg]
  · -- m = 1: delete a 4-cycle
    set a : Fin p := ⟨0, h0⟩ with ha
    obtain ⟨b, hAab, hFab, hbX⟩ := exists_good_neighbor H F hF a {a}
      (by have := hδ a; simp only [Finset.card_singleton]; omega)
    obtain ⟨c, hAbc, hFbc, hcX⟩ := exists_good_neighbor H F hF b {a, b}
      (by have := hδ b
          have e1 := Finset.card_insert_le a ({b} : Finset (Fin p))
          simp only [Finset.card_singleton] at e1
          omega)
    obtain ⟨d, hAcd, hAad, hFcd, hFad, hdX⟩ := exists_good_common_neighbor H F hF c a {a, b, c}
      (by have h1 := hδ c; have h2 := hδ a
          have e1 := Finset.card_insert_le a ({b, c} : Finset (Fin p))
          have e2 := Finset.card_insert_le b ({c} : Finset (Fin p))
          simp only [Finset.card_singleton] at e2
          omega)
    have hba : b ≠ a := Finset.notMem_singleton.mp hbX
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcX hdX
    obtain ⟨hca, hcb⟩ := hcX
    obtain ⟨hda, hdb, hdc⟩ := hdX
    have hab : a ≠ b := hba.symm
    have hac : a ≠ c := Ne.symm hca
    have had : a ≠ d := Ne.symm hda
    have hbc : b ≠ c := Ne.symm hcb
    have hbd : b ≠ d := Ne.symm hdb
    have hcd : c ≠ d := Ne.symm hdc
    refine ⟨{s(a,b), s(b,c), s(c,d), s(a,d)}, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
        Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> rw [SimpleGraph.mem_edgeSet]
      exacts [hAab, hAbc, hAcd, hAad]
    · rw [Finset.disjoint_left]
      intro x hx hfx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      exacts [hFab hfx, hFbc hfx, hFcd hfx, hFad hfx]
    · exact fun v => (fourcycle_inc a b c d hab hac had hbc hbd hcd v).1
    · exact fun v => (fourcycle_inc a b c d hab hac had hbc hbd hcd v).2
    · have := fourcycle_card a b c d hab hac had hbc hbd hcd
      omega
    · have := fourcycle_card a b c d hab hac had hbc hbd hcd
      omega
  · -- m = 2: delete a 5-cycle
    set a : Fin p := ⟨0, h0⟩ with ha
    obtain ⟨b, hAab, hFab, hbX⟩ := exists_good_neighbor H F hF a {a}
      (by have := hδ a; simp only [Finset.card_singleton]; omega)
    obtain ⟨c, hAbc, hFbc, hcX⟩ := exists_good_neighbor H F hF b {a, b}
      (by have := hδ b
          have e1 := Finset.card_insert_le a ({b} : Finset (Fin p))
          simp only [Finset.card_singleton] at e1
          omega)
    obtain ⟨d, hAcd, hFcd, hdX⟩ := exists_good_neighbor H F hF c {a, b, c}
      (by have := hδ c
          have e1 := Finset.card_insert_le a ({b, c} : Finset (Fin p))
          have e2 := Finset.card_insert_le b ({c} : Finset (Fin p))
          simp only [Finset.card_singleton] at e2
          omega)
    obtain ⟨e, hAde, hAae, hFde, hFae, heX⟩ := exists_good_common_neighbor H F hF d a {a, b, c, d}
      (by have h1 := hδ d; have h2 := hδ a
          have e1 := Finset.card_insert_le a ({b, c, d} : Finset (Fin p))
          have e2 := Finset.card_insert_le b ({c, d} : Finset (Fin p))
          have e3 := Finset.card_insert_le c ({d} : Finset (Fin p))
          simp only [Finset.card_singleton] at e3
          omega)
    have hba : b ≠ a := Finset.notMem_singleton.mp hbX
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcX hdX heX
    obtain ⟨hca, hcb⟩ := hcX
    obtain ⟨hda, hdb, hdc⟩ := hdX
    obtain ⟨hea, heb, hec, hed⟩ := heX
    have hab : a ≠ b := hba.symm
    have hac : a ≠ c := Ne.symm hca
    have had : a ≠ d := Ne.symm hda
    have hae : a ≠ e := Ne.symm hea
    have hbc : b ≠ c := Ne.symm hcb
    have hbd : b ≠ d := Ne.symm hdb
    have hbe : b ≠ e := Ne.symm heb
    have hcd : c ≠ d := Ne.symm hdc
    have hce : c ≠ e := Ne.symm hec
    have hde : d ≠ e := Ne.symm hed
    refine ⟨{s(a,b), s(b,c), s(c,d), s(d,e), s(a,e)}, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
        Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> rw [SimpleGraph.mem_edgeSet]
      exacts [hAab, hAbc, hAcd, hAde, hAae]
    · rw [Finset.disjoint_left]
      intro x hx hfx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      exacts [hFab hfx, hFbc hfx, hFcd hfx, hFde hfx, hFae hfx]
    · exact fun v => (fivecycle_inc a b c d e hab hac had hae hbc hbd hbe hcd hce hde v).1
    · exact fun v => (fivecycle_inc a b c d e hab hac had hae hbc hbd hbe hcd hce hde v).2
    · have := fivecycle_card a b c d e hab hac had hae hbc hbd hbe hcd hce hde
      omega
    · have := fivecycle_card a b c d e hab hac had hae hbc hbd hbe hcd hce hde
      omega

/-- **Divisibility correction of a dense graph.** For `H` on `Fin p` (`p ≥ 2000`) with min
degree `≥ 0.9 p`, there is an edge set `C ⊆ E(H)` with `|C| ≤ p + 8`, incidence degree `≤ 6`
at every vertex, such that in `H − C` all degrees are even and the number of edges is
`≡ 0 (mod 3)`. -/
lemma exists_divisible_correction_edges (H : SimpleGraph (Fin p)) [DecidableRel H.Adj]
    (hp : 2000 ≤ p) (hδ : ∀ v, 9 * p ≤ 10 * H.degree v) :
    ∃ C : Finset (Sym2 (Fin p)),
      (C : Set (Sym2 (Fin p))) ⊆ H.edgeSet ∧
      C.card ≤ p + 8 ∧
      (∀ v, incDeg C v ≤ 6) ∧
      (∀ v, Even (H.degree v - incDeg C v)) ∧
      (H.edgeFinset.card - C.card) % 3 = 0 := by
  classical
  have hδ2 : ∀ v, p ≤ 2 * H.degree v := by
    intro v; have := hδ v; omega
  -- parity correction F
  obtain ⟨F, hFsub, hFcard, hFinc, hFparity⟩ :=
    exists_parity_edges H (by omega) hδ2
  -- incidence bound of F by degree
  have hFdeg : ∀ v, incDeg F v ≤ H.degree v := by
    intro v
    have h1 : incDeg F v ≤ incDeg H.edgeFinset v := by
      apply incDeg_mono
      intro e he
      rw [SimpleGraph.mem_edgeFinset]
      exact hFsub he
    rw [incDeg_edgeFinset_eq_degree] at h1
    exact h1
  -- choose residue m to make the final count divisible by 3
  set m := (H.edgeFinset.card - F.card) % 3 with hm
  have hmle : m ≤ 2 := by rw [hm]; omega
  obtain ⟨G, hGsub, hGF, hGinc, hGeven, hGcard, hGmod⟩ :=
    exists_parity_cycle H (by omega) hδ (F := F) hFinc m hmle
  have hdisj : Disjoint F G := hGF.symm
  have hcard : (F ∪ G).card = F.card + G.card := Finset.card_union_of_disjoint hdisj
  refine ⟨F ∪ G, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    rw [Finset.coe_union, Set.mem_union] at he
    rcases he with h | h
    · exact hFsub h
    · exact hGsub h
  · omega
  · intro v
    rw [incDeg_union_of_disjoint hdisj]
    have h1 := hFinc v
    have h2 := hGinc v
    omega
  · intro v
    rw [incDeg_union_of_disjoint hdisj]
    -- deg - (incF + incG), with incF parity = deg parity, incG even
    have hpar := hFparity v
    have hgev := hGeven v
    have hfd := hFdeg v
    -- Nat parity reasoning
    rcases Nat.even_or_odd (H.degree v) with hev | hodd
    · have : ¬ Odd (incDeg F v) := by
        intro h; exact (Nat.not_even_iff_odd.mpr (hpar.mp h)) hev
      have hFev : Even (incDeg F v) := Nat.not_odd_iff_even.mp this
      obtain ⟨a, ha⟩ := hev
      obtain ⟨b, hb⟩ := hFev
      obtain ⟨c, hc⟩ := hgev
      refine ⟨a - (b + c), ?_⟩
      omega
    · have hFodd : Odd (incDeg F v) := hpar.mpr hodd
      obtain ⟨a, ha⟩ := hodd
      obtain ⟨b, hb⟩ := hFodd
      obtain ⟨c, hc⟩ := hgev
      refine ⟨a - (b + c), ?_⟩
      omega
  · rw [hcard]
    -- (|E| - |F|) - |G| ≡ 0 mod 3, using |G| % 3 = (|E| - |F|) % 3 and |G| ≤ |E| - |F|
    have hd4 : ∀ v, 4 ≤ H.degree v := by intro v; have := hδ v; omega
    have htwice := twice_card_edgeFinset_ge H 4 hd4
    rw [Fintype.card_fin] at htwice
    have hbig : F.card + G.card ≤ H.edgeFinset.card := by omega
    omega

end PaperIII
