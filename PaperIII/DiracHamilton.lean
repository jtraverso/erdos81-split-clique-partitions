/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Paper III — Dirac-type Hamiltonian path (helper file)

A graph on `Fin p` with minimum degree `≥ p/2` has a Hamiltonian path, presented as a
bijective vertex ordering `f : Fin p → Fin p` with consecutive vertices adjacent.

The proof is the classical maximal-path / rotation–extension argument, organised as:

* `hamiltonian_path_extend` — a non-spanning path (as a `Nodup`/`IsChain` list) can be
  lengthened by one vertex (the analytic core);
* `exists_spanning_isChain` — iterating the extension (`Nat.findGreatest`) yields a spanning
  path of length `p`;
* `ordering_of_spanning_isChain` — a spanning `Nodup`/`IsChain` list gives the ordering.

The main export is `hamiltonian_ordering_of_minDegree`.
-/

@[expose] public section

namespace PaperIII

open Finset SimpleGraph

variable {p : ℕ}

/-- A spanning (`length = p`), duplicate-free chain gives a bijective ordering of the
vertices with consecutive vertices adjacent. -/
lemma ordering_of_spanning_isChain (H : SimpleGraph (Fin p)) [DecidableRel H.Adj]
    (L : List (Fin p)) (hchain : L.IsChain H.Adj) (hnodup : L.Nodup) (hlen : L.length = p) :
    ∃ f : Fin p → Fin p, Function.Bijective f ∧
      ∀ (i : ℕ) (h : i + 1 < p), H.Adj (f ⟨i, by omega⟩) (f ⟨i + 1, h⟩) := by
  refine ⟨fun i => L[(i : ℕ)]'(by rw [hlen]; exact i.2), ?_, ?_⟩
  · have hinj : Function.Injective (fun i : Fin p => L[(i : ℕ)]'(by rw [hlen]; exact i.2)) := by
      intro i j h
      simp only at h
      exact Fin.ext ((List.Nodup.getElem_inj_iff hnodup).mp h)
    exact (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, rfl⟩
  · intro i h
    rw [List.isChain_iff_getElem] at hchain
    exact hchain i (by rw [hlen]; omega)

/-- `getLast?` of a `take (t+1)` prefix is the element at index `t`. -/
lemma getLast?_take_succ {α : Type*} (C : List α) (t : ℕ) (ht : t < C.length) :
    (C.take (t + 1)).getLast? = some (C[t]'ht) := by
  have hlen : (C.take (t + 1)).length = t + 1 := by rw [List.length_take]; omega
  rw [List.getLast?_eq_getElem?, hlen]
  simp only [Nat.add_sub_cancel]
  rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem ht]

/-- **Re-rooting a cycle.** A chain that closes up (`getLast → head` is an edge) can be
rotated to end at any of its positions, remaining a chain covering the same vertices. -/
lemma cycle_reroot {α : Type*} (R : α → α → Prop) (C : List α) (hC : C.IsChain R)
    (hclose : ∀ x ∈ C.getLast?, ∀ y ∈ C.head?, R x y)
    (t : ℕ) (ht : t < C.length) :
    ∃ Q : List α, Q.IsChain R ∧ List.Perm Q C ∧ Q.getLast? = some (C[t]'ht) ∧
      Q.length = C.length := by
  classical
  have hsplit := List.take_append_drop (t + 1) C
  rw [← hsplit] at hC
  rw [List.isChain_append] at hC
  obtain ⟨hct, hcd, _hj⟩ := hC
  refine ⟨C.drop (t + 1) ++ C.take (t + 1), ?_, ?_, ?_, ?_⟩
  · rw [List.isChain_append]
    refine ⟨hcd, hct, ?_⟩
    intro x hx y hy
    rw [List.getLast?_drop] at hx
    rw [List.head?_take] at hy
    have ht1 : t + 1 ≠ 0 := by omega
    simp only [ht1, if_false] at hy
    by_cases hcase : C.length ≤ t + 1
    · simp [hcase] at hx
    · simp only [hcase, if_false] at hx
      exact hclose x hx y hy
  · have hperm : List.Perm (C.drop (t + 1) ++ C.take (t + 1))
        (C.take (t + 1) ++ C.drop (t + 1)) := List.perm_append_comm
    rwa [hsplit] at hperm
  · rw [List.getLast?_append, getLast?_take_succ C t ht]; rfl
  · rw [List.length_append, List.length_take, List.length_drop]; omega

/-- **Rotation index (pigeonhole).** For a duplicate-free chain both of whose endpoints have
all neighbours inside the chain, there is an index `j` with `head ~ L[j+1]` and `L[j] ~ last`.
(Uses `deg(head) + deg(last) ≥ p > length − 1`.) -/
lemma rotationIndex_exists (H : SimpleGraph (Fin p)) [DecidableRel H.Adj]
    (hδ : ∀ v, p ≤ 2 * H.degree v)
    (L : List (Fin p)) (hnodup : L.Nodup) (hne : L ≠ [])
    (ha : ∀ w, H.Adj (L.head hne) w → w ∈ L)
    (hb : ∀ w, H.Adj (L.getLast hne) w → w ∈ L)
    (hlen2 : 2 ≤ L.length) (hlt : L.length < p) :
    ∃ j : Fin (L.length - 1),
      H.Adj (L.head hne) (L.get ⟨j + 1, by omega⟩) ∧ H.Adj (L.get ⟨j, by omega⟩) (L.getLast hne) := by
  classical
  set n := L.length with hn
  set a := L.head hne with hadef
  set b := L.getLast hne with hbdef
  have haget : a = L.get ⟨0, by omega⟩ := by rw [hadef, List.head_eq_getElem]; rfl
  have hbget : b = L.get ⟨n - 1, by omega⟩ := by rw [hbdef, List.getLast_eq_getElem]; rfl
  set φ : Fin (n - 1) → Fin p := fun j => L.get ⟨j + 1, by omega⟩ with hφ
  set ψ : Fin (n - 1) → Fin p := fun j => L.get ⟨j, by omega⟩ with hψ
  have hφinj : Function.Injective φ := by
    intro j1 j2 h; simp only [hφ] at h
    have := (List.nodup_iff_injective_get.mp hnodup) h
    simp only [Fin.mk.injEq] at this; exact Fin.ext (by omega)
  have hψinj : Function.Injective ψ := by
    intro j1 j2 h; simp only [hψ] at h
    have := (List.nodup_iff_injective_get.mp hnodup) h
    simp only [Fin.mk.injEq] at this; exact Fin.ext (by omega)
  set SA : Finset (Fin (n - 1)) := univ.filter (fun j => H.Adj a (φ j)) with hSA
  set SB : Finset (Fin (n - 1)) := univ.filter (fun j => H.Adj (ψ j) b) with hSB
  have hcardSA : SA.card = H.degree a := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hSA,
        ← Finset.card_image_of_injOn hφinj.injOn]
    congr 1; ext v
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact hj
    · intro hv
      obtain ⟨m, hm⟩ := List.mem_iff_get.mp (ha v hv)
      have hmlt : (m : ℕ) < n := by rw [hn]; exact m.isLt
      have hm0 : (m : ℕ) ≠ 0 := by
        intro h0
        have hva : v = a := by rw [← hm, haget]; congr 1; exact Fin.ext (by omega)
        exact H.ne_of_adj hv hva.symm
      have hφv : φ ⟨(m : ℕ) - 1, by omega⟩ = v := by
        simp only [hφ]; rw [← hm]; congr 1
        exact Fin.ext (show (m : ℕ) - 1 + 1 = (m : ℕ) by omega)
      exact ⟨⟨(m : ℕ) - 1, by omega⟩, by rw [hφv]; exact hv, hφv⟩
  have hcardSB : SB.card = H.degree b := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hSB,
        ← Finset.card_image_of_injOn hψinj.injOn]
    congr 1; ext v
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact H.adj_symm hj
    · intro hv
      obtain ⟨m, hm⟩ := List.mem_iff_get.mp (hb v hv)
      have hmlt : (m : ℕ) < n := by rw [hn]; exact m.isLt
      have hmn : (m : ℕ) ≠ n - 1 := by
        intro h0
        have hvb : v = b := by rw [← hm, hbget]; congr 1; exact Fin.ext (by omega)
        exact H.ne_of_adj hv hvb.symm
      have hψv : ψ ⟨(m : ℕ), by omega⟩ = v := by simp only [hψ]; rw [← hm]
      exact ⟨⟨(m : ℕ), by omega⟩, by rw [hψv]; exact H.adj_symm hv, hψv⟩
  have hdeg : H.degree a + H.degree b ≥ p := by have := hδ a; have := hδ b; omega
  have hInter : (SA ∩ SB).Nonempty := by
    rw [← Finset.card_pos]
    have hun := Finset.card_union_add_card_inter SA SB
    have hle : (SA ∪ SB).card ≤ n - 1 := le_trans (Finset.card_le_univ _) (by simp)
    omega
  obtain ⟨j, hj⟩ := hInter
  rw [Finset.mem_inter, hSA, hSB, Finset.mem_filter, Finset.mem_filter] at hj
  exact ⟨j, hj.1.2, hj.2.2⟩

/-- **External edge.** A non-spanning duplicate-free chain whose head has all neighbours
inside it must nonetheless have an edge from some chain vertex to a vertex outside it. -/
lemma exists_external_edge (H : SimpleGraph (Fin p)) [DecidableRel H.Adj]
    (hδ : ∀ v, p ≤ 2 * H.degree v)
    (L : List (Fin p)) (hnodup : L.Nodup) (hne : L ≠ [])
    (ha : ∀ w, H.Adj (L.head hne) w → w ∈ L)
    (hlt : L.length < p) :
    ∃ w, w ∉ L ∧ ∃ x, x ∈ L ∧ H.Adj x w := by
  classical
  set a := L.head hne with hadef
  have hcardL : L.toFinset.card = L.length := List.toFinset_card_of_nodup hnodup
  have hexists : ∃ w, w ∉ L.toFinset := by
    by_contra hcon
    push_neg at hcon
    have : L.toFinset = univ := Finset.eq_univ_iff_forall.mpr hcon
    rw [this, Finset.card_univ, Fintype.card_fin] at hcardL
    omega
  obtain ⟨w, hw⟩ := hexists
  rw [List.mem_toFinset] at hw
  have haL : L.head hne ∈ L := List.head_mem hne
  have hanotin : a ∉ H.neighborFinset a := by
    rw [SimpleGraph.mem_neighborFinset]; exact H.irrefl
  have hdega : H.degree a + 1 ≤ L.length := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← hcardL]
    have hins : insert a (H.neighborFinset a) ⊆ L.toFinset := by
      apply Finset.insert_subset (by rw [List.mem_toFinset]; exact haL)
      intro x hx
      rw [SimpleGraph.mem_neighborFinset] at hx
      rw [List.mem_toFinset]; exact ha x hx
    have := Finset.card_le_card hins
    rw [Finset.card_insert_of_notMem hanotin] at this
    omega
  refine ⟨w, hw, ?_⟩
  by_contra hcon
  push_neg at hcon
  have hsub : H.neighborFinset w ⊆ univ \ insert w L.toFinset := by
    intro x hx
    rw [SimpleGraph.mem_neighborFinset] at hx
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      List.mem_toFinset, not_or]
    refine ⟨?_, ?_⟩
    · intro hxw; rw [hxw] at hx; exact H.irrefl hx
    · intro hxL; exact hcon x hxL (H.adj_symm hx)
  have hdegw : H.degree w ≤ p - L.length - 1 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have hcard := Finset.card_le_card hsub
    have heq := Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ (insert w L.toFinset))
    rw [Finset.card_univ, Fintype.card_fin,
        Finset.card_insert_of_notMem (by rw [List.mem_toFinset]; exact hw), hcardL] at heq
    omega
  have h1 := hδ w; have h2 := hδ a
  omega

/-- **Rotation–extension core (Dirac).** In a graph with minimum degree `≥ p/2`, any
duplicate-free chain that is not yet spanning can be extended by one vertex. -/
lemma hamiltonian_path_extend (H : SimpleGraph (Fin p)) [DecidableRel H.Adj]
    (hδ : ∀ v, p ≤ 2 * H.degree v)
    (L : List (Fin p)) (hchain : L.IsChain H.Adj) (hnodup : L.Nodup) (hlt : L.length < p) :
    ∃ L' : List (Fin p), L'.IsChain H.Adj ∧ L'.Nodup ∧ L'.length = L.length + 1 := by
  classical
  rcases eq_or_ne L [] with rfl | hne
  · haveI : Nonempty (Fin p) := ⟨⟨0, by omega⟩⟩
    exact ⟨[⟨0, by omega⟩], by simp, by simp, by simp⟩
  set a := L.head hne with hadef
  set b := L.getLast hne with hbdef
  by_cases hApp : ∃ w, H.Adj b w ∧ w ∉ L
  · obtain ⟨w, hbw, hwL⟩ := hApp
    refine ⟨L ++ [w], ?_, ?_, by simp⟩
    · rw [List.isChain_append]
      refine ⟨hchain, by simp, ?_⟩
      intro y hy z hz
      rw [List.getLast?_eq_some_getLast hne] at hy
      simp only [List.head?_cons, Option.mem_some_iff] at hy hz
      subst hy; subst hz; exact hbw
    · rw [List.nodup_append]
      refine ⟨hnodup, by simp, ?_⟩
      intro y hy z hz; simp only [List.mem_singleton] at hz
      subst hz; intro heq; exact hwL (heq ▸ hy)
  by_cases hPre : ∃ w, H.Adj a w ∧ w ∉ L
  · obtain ⟨w, haw, hwL⟩ := hPre
    refine ⟨w :: L, ?_, ?_, by simp⟩
    · rw [List.isChain_cons]
      refine ⟨?_, hchain⟩
      intro y hy
      rw [List.head?_eq_some_head hne] at hy
      simp only [Option.mem_some_iff] at hy
      subst hy; exact H.adj_symm haw
    · rw [List.nodup_cons]; exact ⟨hwL, hnodup⟩
  · push_neg at hApp hPre
    obtain ⟨w, hwL, x, hxL, hxw⟩ := exists_external_edge H hδ L hnodup hne hPre hlt
    have hn2 : 2 ≤ L.length := by
      by_contra hlt2
      have hn1 : L.length = 1 := by have := List.length_pos_of_ne_nil hne; omega
      have hd0 : H.degree a = 0 := by
        by_contra hd
        have hpos : 0 < H.degree a := Nat.pos_of_ne_zero hd
        rw [← SimpleGraph.card_neighborFinset_eq_degree] at hpos
        obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos
        rw [SimpleGraph.mem_neighborFinset] at hy
        have hyL := hPre y hy
        have hLeq : L = [a] := by
          rcases L with _ | ⟨c, tl⟩
          · simp at hn1
          · simp only [List.length_cons] at hn1
            have htl : tl = [] := List.length_eq_zero_iff.mp (by omega)
            subst htl; simp [hadef]
        rw [hLeq] at hyL; simp only [List.mem_singleton] at hyL
        subst hyL; exact H.irrefl hy
      have := hδ a; omega
    obtain ⟨j, hja, hjb⟩ := rotationIndex_exists H hδ L hnodup hne hPre hApp hn2 hlt
    set jv := (j : ℕ) with hjv
    have hjlt : jv + 1 < L.length := by have := j.isLt; omega
    set Cyc := L.take (jv + 1) ++ (L.drop (jv + 1)).reverse with hCyc
    have hLsplit := List.take_append_drop (jv + 1) L
    have hchain2 := hchain
    rw [← hLsplit, List.isChain_append] at hchain2
    obtain ⟨hct, hcd, _hjunc⟩ := hchain2
    have hflip : (fun x y : Fin p => H.Adj y x) = H.Adj := by
      ext x y; exact H.adj_comm y x
    have hchain_rev : (L.drop (jv + 1)).reverse.IsChain H.Adj := by
      rw [List.isChain_reverse, hflip]; exact hcd
    have hCyc_chain : Cyc.IsChain H.Adj := by
      rw [hCyc, List.isChain_append]
      refine ⟨hct, hchain_rev, ?_⟩
      intro y hy z hz
      rw [getLast?_take_succ L jv (by omega)] at hy
      rw [List.head?_reverse, List.getLast?_drop] at hz
      simp only [Option.mem_some_iff] at hy
      have hnotle : ¬ L.length ≤ jv + 1 := by omega
      rw [if_neg hnotle, List.getLast?_eq_some_getLast hne] at hz
      simp only [Option.mem_some_iff] at hz
      subst hy; subst hz
      have hgg : L.get ⟨jv, by omega⟩ = L[jv] := rfl
      rw [← hgg]; exact hjb
    have hCyc_perm : List.Perm Cyc L := by
      rw [hCyc]
      have h2 := List.Perm.append_left (L.take (jv + 1)) (List.reverse_perm (L.drop (jv + 1)))
      rwa [hLsplit] at h2
    have hCyc_nodup : Cyc.Nodup := hCyc_perm.nodup_iff.mpr hnodup
    have hCyc_len : Cyc.length = L.length := hCyc_perm.length_eq
    have hclose : ∀ y ∈ Cyc.getLast?, ∀ z ∈ Cyc.head?, H.Adj y z := by
      intro y hy z hz
      rw [hCyc, List.getLast?_append, List.getLast?_reverse, List.head?_drop,
          List.getElem?_eq_getElem hjlt] at hy
      simp only [Option.some_or, Option.mem_some_iff] at hy
      rw [hCyc, List.head?_append, List.head?_take] at hz
      have hne1 : jv + 1 ≠ 0 := by omega
      rw [if_neg hne1, List.head?_eq_some_head hne] at hz
      simp only [Option.some_or, Option.mem_some_iff] at hz
      subst hy; subst hz
      have hgg : L.get ⟨jv + 1, by omega⟩ = L[jv + 1] := rfl
      rw [← hgg]; exact H.adj_symm hja
    have hxCyc : x ∈ Cyc := hCyc_perm.mem_iff.mpr hxL
    obtain ⟨t, ht, hCt⟩ := List.mem_iff_getElem.mp hxCyc
    obtain ⟨Q, hQchain, hQperm, hQlast, hQlen⟩ := cycle_reroot H.Adj Cyc hCyc_chain hclose t ht
    have hwQ : w ∉ Q := fun hwQ => hwL (hCyc_perm.mem_iff.mp (hQperm.mem_iff.mp hwQ))
    refine ⟨Q ++ [w], ?_, ?_, ?_⟩
    · rw [List.isChain_append]
      refine ⟨hQchain, by simp, ?_⟩
      intro y hy z hz
      rw [hQlast] at hy
      simp only [List.head?_cons, Option.mem_some_iff] at hy hz
      subst hy; subst hz
      rw [hCt]; exact hxw
    · rw [List.nodup_append]
      refine ⟨hQperm.nodup_iff.mpr hCyc_nodup, by simp, ?_⟩
      intro y hy z hz; simp only [List.mem_singleton] at hz
      subst hz; intro heq; exact hwQ (heq ▸ hy)
    · rw [List.length_append, hQlen, hCyc_len]; simp

/-- Iterating `hamiltonian_path_extend` yields a spanning chain of length `p`. -/
lemma exists_spanning_isChain (H : SimpleGraph (Fin p)) [DecidableRel H.Adj]
    (hδ : ∀ v, p ≤ 2 * H.degree v) :
    ∃ L : List (Fin p), L.IsChain H.Adj ∧ L.Nodup ∧ L.length = p := by
  classical
  set Pr : ℕ → Prop := fun n => ∃ L : List (Fin p), L.IsChain H.Adj ∧ L.Nodup ∧ L.length = n
    with hPr
  have hPr0 : Pr 0 := ⟨[], by simp, by simp, rfl⟩
  have hNle : Nat.findGreatest Pr p ≤ p := Nat.findGreatest_le p
  have hPrN : Pr (Nat.findGreatest Pr p) := Nat.findGreatest_spec (Nat.zero_le p) hPr0
  have hNp : Nat.findGreatest Pr p = p := by
    by_contra hne
    have hlt : Nat.findGreatest Pr p < p := lt_of_le_of_ne hNle hne
    obtain ⟨L, hc, hn, hl⟩ := hPrN
    obtain ⟨L', hc', hn', hl'⟩ := hamiltonian_path_extend H hδ L hc hn (by rw [hl]; exact hlt)
    have hPrN1 : Pr (Nat.findGreatest Pr p + 1) := ⟨L', hc', hn', by rw [hl', hl]⟩
    have := Nat.le_findGreatest (by omega : Nat.findGreatest Pr p + 1 ≤ p) hPrN1
    omega
  obtain ⟨L, a, b, c⟩ := hPrN
  exact ⟨L, a, b, c.trans hNp⟩

/-- **Dirac (path form).** A graph on `Fin p` with minimum degree `≥ p/2` admits a bijective
vertex ordering along which consecutive vertices are adjacent (a Hamiltonian path). -/
theorem hamiltonian_ordering_of_minDegree (H : SimpleGraph (Fin p)) [DecidableRel H.Adj]
    (hp : 3 ≤ p) (hδ : ∀ v, p ≤ 2 * H.degree v) :
    ∃ f : Fin p → Fin p, Function.Bijective f ∧
      ∀ (i : ℕ) (h : i + 1 < p), H.Adj (f ⟨i, by omega⟩) (f ⟨i + 1, h⟩) := by
  obtain ⟨L, hc, hn, hl⟩ := exists_spanning_isChain H hδ
  exact ordering_of_spanning_isChain H L hc hn hl

end PaperIII
