/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PaperIII.E_B
public import PaperIII.E_8_Divisible
public import PaperIII.AXDefs
public import PaperIII.SplitEdges
public import PaperIII.DiracMatching
public import PaperIII.Duality
public import PaperIII.Counting

/-!
# Paper III — §8 core construction (E-8), combinatorial building blocks

This file isolates the two combinatorial building blocks of the very-sparse packing
estimate `E_8_packing_exists`, together with the structural glue needed to combine them:

* `clique_remainder_mindegree` — deleting a bounded edge set from `Kₚ` keeps min degree
  `≥ p − 1 − q`.
* `trianglePacking_union` — the union of two edge-disjoint triangle packings is a packing.
* `E_8_cross_packing` (**KKI**) — a family of `KKI` cross triangles covering all but `≤ q`
  of the cross edges, using a set `D` of clique edges with per-vertex incidence `≤ q`.
* `E_8_clique_packing` (**AX2**) — for the clique remainder `Kₚ − D` (`δ ≥ p − 1 − q`),
  a family of clique triangles (all of whose edges avoid `D`) covering all but `≤ 2p`
  clique edges of the remainder.

The final assembly (counting) lives in `E_8.lean`.
-/

@[expose] public section

namespace PaperIII

open SplitGraph

open SimpleGraph in
/-- **Clique-remainder minimum degree.** Removing an edge set `D` from the complete
graph `K_p` that touches each vertex at most `q` times leaves minimum degree at least
`p - 1 - q`.  Every vertex of `K_p` has degree `p - 1`; deleting `D` removes from a
vertex `v` only the (at most `q`) edges of `D` incident to `v`, so the surviving degree
is at least `(p - 1) - q`.

The hypothesis `hD` (that `D` contains no diagonal edges) is not needed for the proof;
it is kept only to match the requested interface. -/
lemma clique_remainder_mindegree {p q : ℕ}
    (D : Finset (Sym2 (Fin p)))
    (hD : ∀ e ∈ D, ¬ e.IsDiag)
    (hinc : ∀ v : Fin p, (D.filter (fun e => v ∈ e)).card ≤ q) :
    (p - 1 - q : ℕ) ≤ ((⊤ : SimpleGraph (Fin p)).deleteEdges (D : Set (Sym2 (Fin p)))).minDegree := by
  classical
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp; simp
  · haveI : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
    apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro v
    set G' := (⊤ : SimpleGraph (Fin p)).deleteEdges (D : Set (Sym2 (Fin p))) with hG'
    have hsub : G'.neighborFinset v ⊆ (⊤ : SimpleGraph (Fin p)).neighborFinset v := by
      intro w hw
      rw [mem_neighborFinset] at hw ⊢
      exact (deleteEdges_adj.mp hw).1
    have hAcard : ((⊤ : SimpleGraph (Fin p)).neighborFinset v).card = p - 1 := by
      rw [card_neighborFinset_eq_degree]
      have h := SimpleGraph.IsRegularOfDegree.top (V := Fin p) v
      simp only [Fintype.card_fin] at h
      exact h
    have hsdiff_bound :
        ((⊤ : SimpleGraph (Fin p)).neighborFinset v \ G'.neighborFinset v).card ≤ q := by
      have hmap :
          ((⊤ : SimpleGraph (Fin p)).neighborFinset v \ G'.neighborFinset v).card
            ≤ (D.filter (fun e => v ∈ e)).card := by
        apply Finset.card_le_card_of_injOn (fun w => s(v, w))
        · intro w hw
          simp only [Finset.mem_coe, Finset.mem_sdiff, mem_neighborFinset] at hw
          obtain ⟨hadj, hnadj⟩ := hw
          simp only [Finset.mem_coe, Finset.mem_filter]
          refine ⟨?_, Sym2.mem_iff.mpr (Or.inl rfl)⟩
          by_contra hnotin
          apply hnadj
          rw [hG', deleteEdges_adj]
          exact ⟨hadj, by simpa using hnotin⟩
        · intro w1 hw1 w2 hw2 heq
          simp only [Finset.mem_coe, Finset.mem_sdiff, mem_neighborFinset, top_adj] at hw1 hw2
          rw [Sym2.eq_iff] at heq
          rcases heq with ⟨_, h⟩ | ⟨_, h2⟩
          · exact h
          · exact absurd h2.symm hw1.1
      exact le_trans hmap (hinc v)
    have hcard_sdiff := Finset.card_sdiff_add_card_eq_card hsub
    have hdeg : G'.degree v = (G'.neighborFinset v).card :=
      (card_neighborFinset_eq_degree _ _).symm
    rw [hdeg]
    omega

/-- The union of two edge-disjoint triangle packings (`t₁ ∈ T₁`, `t₂ ∈ T₂` always share
at most one vertex) is again a triangle packing. -/
lemma trianglePacking_union {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] {T₁ T₂ : Finset (Finset W)}
    (h₁ : IsTrianglePacking H T₁) (h₂ : IsTrianglePacking H T₂)
    (hcross : ∀ t₁ ∈ T₁, ∀ t₂ ∈ T₂, (t₁ ∩ t₂).card ≤ 1) :
    IsTrianglePacking H (T₁ ∪ T₂) := by
  classical
  refine ⟨?_, ?_⟩
  · intro t ht
    rcases Finset.mem_union.mp ht with ht | ht
    · exact h₁.1 t ht
    · exact h₂.1 t ht
  · intro t₁ ht₁ t₂ ht₂ hne
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at ht₁ ht₂
    rcases ht₁ with ht₁ | ht₁ <;> rcases ht₂ with ht₂ | ht₂
    · exact h₁.2 ht₁ ht₂ hne
    · exact hcross t₁ ht₁ t₂ ht₂
    · rw [Finset.inter_comm]; exact hcross t₂ ht₂ t₁ ht₁
    · exact h₂.2 ht₁ ht₂ hne

open SimpleGraph in
/-- **KKI single-vertex matching step.**  In the complete graph on a set `N ⊆ Fin p`, after
removing a forbidden edge set `U` in which each vertex is incident to at most `b` edges, if
`|N| ≥ 2b + 1` then there is a matching `M` (pairwise-disjoint non-diagonal pairs inside `N`,
all avoiding `U`) covering all but at most one vertex of `N`.

Proof: form the graph on the subtype `{a // a ∈ N}` with `a ~ b ↔ a ≠ b ∧ s(a,b) ∉ U`.  Its
minimum degree is `≥ |N| − 1 − b ≥ (|N| − 1)/2`, so `|N| ≤ 2δ + 1` and
`exists_near_perfect_matching` yields a matching covering all but one vertex; transport it
back to `Finset (Sym2 (Fin p))`. -/
lemma cross_matching_step {p : ℕ} (N : Finset (Fin p)) (U : Finset (Sym2 (Fin p))) (b : ℕ)
    (hUinc : ∀ a : Fin p, (U.filter (fun e => a ∈ e)).card ≤ b)
    (hbN : 2 * b + 1 ≤ N.card) :
    ∃ M : Finset (Sym2 (Fin p)),
      (∀ e ∈ M, ¬ e.IsDiag) ∧
      (∀ e ∈ M, ∀ v ∈ e, v ∈ N) ∧
      (∀ e ∈ M, e ∉ U) ∧
      (∀ a : Fin p, (M.filter (fun e => a ∈ e)).card ≤ 1) ∧
      N.card ≤ 2 * M.card + 1 := by
  classical
  set W := {a : Fin p // a ∈ N} with hWdef
  set Gsub : SimpleGraph W :=
    (⊤ : SimpleGraph W).deleteEdges {e | Sym2.map (Subtype.val) e ∈ U} with hGsub
  haveI : DecidableRel Gsub.Adj := Classical.decRel _
  have hcardW : Fintype.card W = N.card := by simp [hWdef, Fintype.card_coe]
  haveI : Nonempty W := by
    have hpos : 0 < N.card := by omega
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
    exact ⟨⟨a, ha⟩⟩
  have hval : Function.Injective (Subtype.val : W → Fin p) := Subtype.val_injective
  have hadj : ∀ x y : W, Gsub.Adj x y ↔ (x ≠ y ∧ s(x.val, y.val) ∉ U) := by
    intro x y
    rw [hGsub, SimpleGraph.deleteEdges_adj]
    constructor
    · rintro ⟨htop, hnotin⟩
      exact ⟨fun h => by rw [h] at htop; exact (SimpleGraph.irrefl _ htop),
        fun hmem => hnotin (by simpa using hmem)⟩
    · rintro ⟨hne, hnotin⟩
      exact ⟨by simpa using hne, fun hmem => hnotin (by simpa using hmem)⟩
  have hmindeg : ∀ x : W, N.card - 1 - b ≤ Gsub.degree x := by
    intro x
    rw [← card_neighborFinset_eq_degree]
    have hxmem : x ∈ Finset.univ \ Gsub.neighborFinset x := by
      simp [mem_neighborFinset, SimpleGraph.irrefl]
    have hmap : ((Finset.univ \ Gsub.neighborFinset x).erase x).card
        ≤ (U.filter (fun e => x.val ∈ e)).card := by
      apply Finset.card_le_card_of_injOn (fun y => s(x.val, y.val))
      · intro y hy
        rw [Finset.mem_coe, Finset.mem_erase, Finset.mem_sdiff, mem_neighborFinset] at hy
        obtain ⟨hyx, _, hnadj⟩ := hy
        rw [hadj] at hnadj; push_neg at hnadj
        have hxy : x ≠ y := fun h => hyx h.symm
        exact Finset.mem_filter.mpr ⟨hnadj hxy, by simp [Sym2.mem_iff]⟩
      · intro y1 hy1 y2 hy2 heq
        rw [Finset.mem_coe, Finset.mem_erase] at hy1 hy2
        rw [Sym2.eq_iff] at heq
        rcases heq with ⟨_, h⟩ | ⟨h1, _⟩
        · exact hval h
        · exact absurd (hval h1) (fun hc => hy2.1 hc.symm)
    have hcard_erase : (Finset.univ \ Gsub.neighborFinset x).card
        = ((Finset.univ \ Gsub.neighborFinset x).erase x).card + 1 := by
      rw [Finset.card_erase_of_mem hxmem]
      have : 1 ≤ (Finset.univ \ Gsub.neighborFinset x).card := Finset.card_pos.mpr ⟨x, hxmem⟩
      omega
    have hUb := hUinc x.val
    have hnb : Fintype.card W - (b + 1) ≤ (Gsub.neighborFinset x).card := by
      have hh := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (Gsub.neighborFinset x))
      rw [Finset.card_univ] at hh
      omega
    rw [hcardW] at hnb
    omega
  have hcard_le : Fintype.card W ≤ 2 * Gsub.minDegree + 1 := by
    have hmin : N.card - 1 - b ≤ Gsub.minDegree :=
      SimpleGraph.le_minDegree_of_forall_le_degree _ _ hmindeg
    rw [hcardW]; omega
  obtain ⟨Mm, hMatch, hcov⟩ := PaperIII.exists_near_perfect_matching Gsub hcard_le
  set EF : Finset (Sym2 W) := Finset.univ.filter (fun e => e ∈ Mm.edgeSet) with hEF
  set MFin : Finset (Sym2 (Fin p)) := EF.image (Sym2.map Subtype.val) with hMFin
  have hmemMFin : ∀ e ∈ MFin, ∃ x y : W, Gsub.Adj x y ∧ e = s(x.val, y.val) := by
    intro e he
    rw [hMFin, Finset.mem_image] at he
    obtain ⟨e0, he0, rfl⟩ := he
    rw [hEF, Finset.mem_filter] at he0
    induction e0 using Sym2.ind with
    | _ x y =>
      rw [SimpleGraph.Subgraph.mem_edgeSet] at he0
      exact ⟨x, y, Mm.adj_sub he0.2, by simp⟩
  have hincW : ∀ x : W, (EF.filter (fun e => x ∈ e)).card ≤ 1 := by
    intro x
    rw [Finset.card_le_one]
    intro e1 h1 e2 h2
    rw [hEF] at h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    obtain ⟨he1, hxe1⟩ := h1
    obtain ⟨he2, hxe2⟩ := h2
    induction e1 using Sym2.ind with
    | _ a b =>
      induction e2 using Sym2.ind with
      | _ c d =>
        rw [SimpleGraph.Subgraph.mem_edgeSet] at he1 he2
        rw [Sym2.mem_iff] at hxe1 hxe2
        have hxv : x ∈ Mm.verts := by
          rcases hxe1 with rfl | rfl
          · exact Mm.edge_vert he1
          · exact Mm.edge_vert (Mm.adj_symm he1)
        obtain ⟨w, hw, huniq⟩ := hMatch hxv
        have hforce : ∀ {u v : W}, Mm.Adj u v → x = u ∨ x = v → s(u, v) = s(x, w) := by
          intro u v huv hx
          rcases hx with rfl | rfl
          · rw [huniq v huv]
          · rw [huniq u (Mm.adj_symm huv), Sym2.eq_swap]
        rw [hforce he1 hxe1, hforce he2 hxe2]
  refine ⟨MFin, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨x, y, hxy, rfl⟩ := hmemMFin e he
    rw [hadj] at hxy
    simp only [Sym2.mk_isDiag_iff]
    exact fun h => hxy.1 (hval h)
  · intro e he v hv
    obtain ⟨x, y, hxy, rfl⟩ := hmemMFin e he
    rw [Sym2.mem_iff] at hv
    rcases hv with rfl | rfl
    · exact x.2
    · exact y.2
  · intro e he
    obtain ⟨x, y, hxy, rfl⟩ := hmemMFin e he
    rw [hadj] at hxy; exact hxy.2
  · intro a
    by_cases ha : a ∈ N
    · have hsubimg : MFin.filter (fun e => a ∈ e)
          ⊆ (EF.filter (fun e0 => (⟨a, ha⟩ : W) ∈ e0)).image (Sym2.map Subtype.val) := by
        intro e he
        rw [Finset.mem_filter, hMFin, Finset.mem_image] at he
        obtain ⟨⟨e0, he0, rfl⟩, hae⟩ := he
        rw [Finset.mem_image]
        refine ⟨e0, ?_, rfl⟩
        rw [Finset.mem_filter]
        refine ⟨he0, ?_⟩
        induction e0 using Sym2.ind with
        | _ x y =>
          rw [Sym2.mem_iff]
          simp only [Sym2.map_mk, Sym2.mem_iff] at hae
          rcases hae with h | h
          · left; exact Subtype.ext h
          · right; exact Subtype.ext h
      calc (MFin.filter (fun e => a ∈ e)).card
          ≤ ((EF.filter (fun e0 => (⟨a, ha⟩ : W) ∈ e0)).image (Sym2.map Subtype.val)).card :=
            Finset.card_le_card hsubimg
        _ ≤ (EF.filter (fun e0 => (⟨a, ha⟩ : W) ∈ e0)).card := Finset.card_image_le
        _ ≤ 1 := hincW _
    · have hempty : MFin.filter (fun e => a ∈ e) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro e he hae
        obtain ⟨x, y, hxy, rfl⟩ := hmemMFin e he
        rw [Sym2.mem_iff] at hae
        rcases hae with rfl | rfl
        · exact ha x.2
        · exact ha y.2
      rw [hempty]; simp
  · have hverts : Mm.verts.toFinset.card ≤ 2 * EF.card := by
      have hsub : Mm.verts.toFinset ⊆ EF.biUnion (fun e0 => e0.toFinset) := by
        intro v hv
        rw [Set.mem_toFinset] at hv
        obtain ⟨w, hw, _⟩ := hMatch hv
        rw [Finset.mem_biUnion]
        refine ⟨s(v, w), ?_, ?_⟩
        · rw [hEF, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, by rw [SimpleGraph.Subgraph.mem_edgeSet]; exact hw⟩
        · simp
      calc Mm.verts.toFinset.card ≤ (EF.biUnion (fun e0 => e0.toFinset)).card :=
            Finset.card_le_card hsub
        _ ≤ ∑ e0 ∈ EF, e0.toFinset.card := Finset.card_biUnion_le
        _ = ∑ e0 ∈ EF, 2 := by
            apply Finset.sum_congr rfl
            intro e0 he0
            rw [hEF, Finset.mem_filter] at he0
            induction e0 using Sym2.ind with
            | _ a b =>
              rw [SimpleGraph.Subgraph.mem_edgeSet] at he0
              have hab : a ≠ b := (Mm.adj_sub he0.2).ne
              have hset : (s(a,b) : Sym2 W).toFinset = {a, b} := by
                ext z; simp [Sym2.mem_toFinset, Sym2.mem_iff]
              rw [hset, Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton]
        _ = 2 * EF.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have hMFcard : MFin.card = EF.card :=
      Finset.card_image_of_injective _ (Sym2.map.injective hval)
    rw [← hcardW, hMFcard]
    omega

/-- **KKI cross packing, processing the first `m` independent vertices.**  The inductive
core of `E_8_cross_packing`: process independent vertices `i` with `(i : ℕ) < m` one at a
time, each contributing (via `cross_matching_step`) a matching of its clique neighbourhood
that avoids the clique edges `D` already used.  Maintains: `Tc` is a packing of `KKI` cross
triangles whose apexes have index `< m`; the used clique edges `D` have per-vertex incidence
`≤ m`; `|D| ≤ |Tc|`; and the processed cross edges are covered up to `≤ m` leftover. -/
lemma cross_packing_upto (G : SplitGraph)
    (hd : ∀ i : Fin G.q, 2 * G.q + 1 ≤ G.d i) (m : ℕ) (hm : m ≤ G.q) :
    ∃ (Tc : Finset (Finset G.V)) (D : Finset (Sym2 (Fin G.p))),
      IsTrianglePacking G.graph Tc ∧
      (∀ e ∈ D, ¬ e.IsDiag) ∧
      (∀ v : Fin G.p, (D.filter (fun e => v ∈ e)).card ≤ m) ∧
      D.card ≤ Tc.card ∧
      (∀ t ∈ Tc, ∃ (a b : Fin G.p) (i : Fin G.q),
          a ≠ b ∧ s(a, b) ∈ D ∧ (i : ℕ) < m ∧ t = {Sum.inl a, Sum.inl b, Sum.inr i}) ∧
      (∑ i ∈ Finset.univ.filter (fun i : Fin G.q => (i : ℕ) < m), G.d i)
        ≤ 2 * Tc.card + m := by
  classical
  revert hm
  induction m with
  | zero =>
    intro _
    refine ⟨∅, ∅, ⟨by simp, by simp [Set.Pairwise]⟩, by simp, by simp, by simp, by simp, by simp⟩
  | succ m ih =>
    intro hm
    obtain ⟨Tc, D, hpack, hdiag, hinc, hDcard, hform, hcov⟩ := ih (by omega)
    have hmlt : m < G.q := by omega
    set j : Fin G.q := ⟨m, hmlt⟩ with hj
    have hjm : (j : ℕ) = m := rfl
    have hdj : 2 * m + 1 ≤ (G.N j).card := by
      have h := hd j; unfold SplitGraph.d at h; omega
    obtain ⟨M, hMdiag, hMwithin, hMavoid, hMmatch, hMcov⟩ :=
      cross_matching_step (G.N j) D m hinc hdj
    set mkTri : Sym2 (Fin G.p) → Finset G.V :=
      fun e => insert (Sum.inr j) (e.toFinset.image (Sum.inl : Fin G.p → G.V)) with hmk
    have hSym2inj : ∀ e f : Sym2 (Fin G.p), e.toFinset = f.toFinset → e = f := by
      intro e f h
      induction e using Sym2.ind with
      | _ a b =>
        induction f using Sym2.ind with
        | _ c d =>
          have ha : a ∈ ({c, d} : Finset (Fin G.p)) := by
            have : a ∈ (s(a,b)).toFinset := by simp
            rw [h] at this; simpa using this
          have hb : b ∈ ({c, d} : Finset (Fin G.p)) := by
            have : b ∈ (s(a,b)).toFinset := by simp
            rw [h] at this; simpa using this
          have hc : c ∈ ({a, b} : Finset (Fin G.p)) := by
            have : c ∈ (s(c,d)).toFinset := by simp
            rw [← h] at this; simpa using this
          have hd2 : d ∈ ({a, b} : Finset (Fin G.p)) := by
            have : d ∈ (s(c,d)).toFinset := by simp
            rw [← h] at this; simpa using this
          simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc hd2
          rw [Sym2.eq_iff]; tauto
    have hmkinj : Function.Injective mkTri := by
      intro e f hef
      simp only [hmk] at hef
      have h1 : (insert (Sum.inr j) (e.toFinset.image (Sum.inl : Fin G.p → G.V))).erase (Sum.inr j)
          = e.toFinset.image (Sum.inl) := by rw [Finset.erase_insert]; simp
      have h2 : (insert (Sum.inr j) (f.toFinset.image (Sum.inl : Fin G.p → G.V))).erase (Sum.inr j)
          = f.toFinset.image (Sum.inl) := by rw [Finset.erase_insert]; simp
      have key : e.toFinset.image (Sum.inl : Fin G.p → G.V)
          = f.toFinset.image (Sum.inl : Fin G.p → G.V) := by rw [← h1, ← h2, hef]
      exact hSym2inj e f (Finset.image_injective Sum.inl_injective key)
    have hclique : ∀ e ∈ M, G.graph.IsNClique 3 (mkTri e) := by
      intro e he
      induction e using Sym2.ind with
      | _ a b =>
        have hab : a ≠ b := by
          have := hMdiag _ he; simpa [Sym2.mk_isDiag_iff] using this
        have haN : a ∈ G.N j := hMwithin _ he a (by simp)
        have hbN : b ∈ G.N j := hMwithin _ he b (by simp)
        have hset : mkTri s(a, b) = {Sum.inl a, Sum.inl b, Sum.inr j} := by
          rw [hmk]; ext v; simp [Sym2.mem_toFinset]; tauto
        rw [hset, SimpleGraph.isNClique_iff]
        refine ⟨?_, ?_⟩
        · intro x hx y hy hxy
          simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
            Set.mem_singleton_iff] at hx hy
          rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
            first
              | (exact absurd rfl hxy)
              | (simp [SplitGraph.graph, SplitGraph.Adj, hab, haN, hbN, Ne.symm hab])
        · rw [Finset.card_insert_of_notMem (by simp [hab]),
            Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
    set newT : Finset (Finset G.V) := M.image mkTri with hnewT
    have hnewTpack : IsTrianglePacking G.graph newT := by
      refine ⟨?_, ?_⟩
      · intro t ht
        simp only [hnewT, Finset.mem_image] at ht
        obtain ⟨e, he, rfl⟩ := ht
        exact hclique e he
      · intro t1 ht1 t2 ht2 hne12
        simp only [hnewT, Finset.coe_image, Set.mem_image, Finset.mem_coe] at ht1 ht2
        obtain ⟨e, he, rfl⟩ := ht1
        obtain ⟨e', he', rfl⟩ := ht2
        have hee' : e ≠ e' := fun h => hne12 (by rw [h])
        have hdisj : ∀ a : Fin G.p, ¬ (a ∈ e ∧ a ∈ e') := by
          rintro a ⟨hae, hae'⟩
          have h2 : 1 < (M.filter (fun x => a ∈ x)).card :=
            Finset.one_lt_card.mpr ⟨e, by simp [he, hae], e', by simp [he', hae'], hee'⟩
          exact absurd (hMmatch a) (by omega)
        have hsub : mkTri e ∩ mkTri e' ⊆ {Sum.inr j} := by
          intro w hw
          rw [Finset.mem_inter, hmk] at hw
          simp only [Finset.mem_insert, Finset.mem_image, Sym2.mem_toFinset] at hw
          obtain ⟨hwe, hwe'⟩ := hw
          simp only [Finset.mem_singleton]
          rcases hwe with rfl | ⟨a, hae, rfl⟩
          · rfl
          · exfalso
            rcases hwe' with h | ⟨a', hae', h⟩
            · exact absurd h (by simp)
            · rw [Sum.inl.injEq] at h; exact hdisj a ⟨hae, h ▸ hae'⟩
        calc (mkTri e ∩ mkTri e').card ≤ ({Sum.inr j} : Finset G.V).card := Finset.card_le_card hsub
          _ = 1 := Finset.card_singleton _
    have hcross : ∀ t₁ ∈ Tc, ∀ t₂ ∈ newT, (t₁ ∩ t₂).card ≤ 1 := by
      intro t₁ ht₁ t₂ ht₂
      obtain ⟨a, b, i, hab, hDab, him, rfl⟩ := hform t₁ ht₁
      simp only [hnewT, Finset.mem_image] at ht₂
      obtain ⟨e', he', rfl⟩ := ht₂
      have hidiff : (Sum.inr i : G.V) ≠ Sum.inr j := by
        simp only [ne_eq, Sum.inr.injEq]; intro h; rw [h] at him; omega
      have hsub : ({Sum.inl a, Sum.inl b, Sum.inr i} : Finset G.V) ∩ mkTri e'
          ⊆ {Sum.inl a, Sum.inl b} := by
        intro w hw
        rw [Finset.mem_inter, hmk] at hw
        obtain ⟨hw1, hw2⟩ := hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw1 ⊢
        simp only [Finset.mem_insert, Finset.mem_image, Sym2.mem_toFinset] at hw2
        rcases hw1 with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exfalso
          rcases hw2 with h | ⟨c, hc, h⟩
          · exact hidiff h
          · exact absurd h (by simp)
      by_contra hcon
      rw [not_le] at hcon
      have hcard2 : ({Sum.inl a, Sum.inl b} : Finset G.V).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton]
      have heq : ({Sum.inl a, Sum.inl b, Sum.inr i} : Finset G.V) ∩ mkTri e' = {Sum.inl a, Sum.inl b} :=
        Finset.eq_of_subset_of_card_le hsub (by rw [hcard2]; omega)
      have hain : (Sum.inl a : G.V) ∈ mkTri e' := by
        have : (Sum.inl a : G.V) ∈ ({Sum.inl a, Sum.inl b, Sum.inr i} : Finset G.V) ∩ mkTri e' := by
          rw [heq]; simp
        exact (Finset.mem_inter.mp this).2
      have hbin : (Sum.inl b : G.V) ∈ mkTri e' := by
        have : (Sum.inl b : G.V) ∈ ({Sum.inl a, Sum.inl b, Sum.inr i} : Finset G.V) ∩ mkTri e' := by
          rw [heq]; simp
        exact (Finset.mem_inter.mp this).2
      rw [hmk] at hain hbin
      simp only [Finset.mem_insert, Finset.mem_image, Sym2.mem_toFinset] at hain hbin
      have hae' : a ∈ e' := by
        rcases hain with h | ⟨c, hc, h⟩
        · exact absurd h (by simp)
        · rw [Sum.inl.injEq] at h; exact h ▸ hc
      have hbe' : b ∈ e' := by
        rcases hbin with h | ⟨c, hc, h⟩
        · exact absurd h (by simp)
        · rw [Sum.inl.injEq] at h; exact h ▸ hc
      have he'eq : e' = s(a, b) := by
        induction e' using Sym2.ind with
        | _ c d =>
          have hcd : c ≠ d := by have := hMdiag _ he'; simpa [Sym2.mk_isDiag_iff] using this
          simp only [Sym2.mem_iff] at hae' hbe'
          rw [Sym2.eq_iff]
          rcases hae' with rfl | rfl <;> rcases hbe' with rfl | rfl <;> tauto
      rw [he'eq] at he'
      exact hMavoid _ he' hDab
    have hdisjTcnew : Disjoint Tc newT := by
      rw [Finset.disjoint_left]
      intro t htc htnew
      simp only [hnewT, Finset.mem_image] at htnew
      obtain ⟨e, he, rfl⟩ := htnew
      obtain ⟨a, b, i, hab, hDab, him, hteq⟩ := hform (mkTri e) htc
      have hjin : (Sum.inr j : G.V) ∈ mkTri e := by rw [hmk]; simp
      rw [hteq] at hjin
      simp only [Finset.mem_insert, Finset.mem_singleton] at hjin
      rcases hjin with h | h | h
      · exact absurd h (by simp)
      · exact absurd h (by simp)
      · rw [Sum.inr.injEq] at h
        have : (i : ℕ) = m := by rw [← h, hjm]
        omega
    have hnewTcard : newT.card = M.card := Finset.card_image_of_injective _ hmkinj
    refine ⟨Tc ∪ newT, D ∪ M, trianglePacking_union G.graph hpack hnewTpack hcross, ?_, ?_, ?_, ?_, ?_⟩
    · intro e he
      rw [Finset.mem_union] at he
      rcases he with h | h
      · exact hdiag e h
      · exact hMdiag e h
    · intro v
      rw [Finset.filter_union]
      exact le_trans (Finset.card_union_le _ _) (by have := hinc v; have := hMmatch v; omega)
    · rw [Finset.card_union_of_disjoint hdisjTcnew, hnewTcard]
      exact le_trans (Finset.card_union_le _ _) (by omega)
    · intro t ht
      rw [Finset.mem_union] at ht
      rcases ht with ht | ht
      · obtain ⟨a, b, i, hab, hDab, him, hteq⟩ := hform t ht
        exact ⟨a, b, i, hab, Finset.mem_union_left _ hDab, by omega, hteq⟩
      · simp only [hnewT, Finset.mem_image] at ht
        obtain ⟨e, he, rfl⟩ := ht
        induction e using Sym2.ind with
        | _ a b =>
          have hab : a ≠ b := by have := hMdiag _ he; simpa [Sym2.mk_isDiag_iff] using this
          have hset : mkTri s(a, b) = {Sum.inl a, Sum.inl b, Sum.inr j} := by
            rw [hmk]; ext v; simp [Sym2.mem_toFinset]; tauto
          exact ⟨a, b, j, hab, Finset.mem_union_right _ he, by omega, hset⟩
    · have hsplit : (Finset.univ.filter (fun i : Fin G.q => (i : ℕ) < m + 1))
          = insert j (Finset.univ.filter (fun i : Fin G.q => (i : ℕ) < m)) := by
        ext i
        simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hi
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
          · exact Or.inr h
          · exact Or.inl (Fin.ext (by rw [hjm]; exact h))
        · rintro (rfl | h)
          · rw [hjm]; omega
          · omega
      have hjnotin : j ∉ Finset.univ.filter (fun i : Fin G.q => (i : ℕ) < m) := by
        simp [hjm]
      rw [hsplit, Finset.sum_insert hjnotin,
        Finset.card_union_of_disjoint hdisjTcnew, hnewTcard]
      have hdj' : G.d j = (G.N j).card := rfl
      have hdjle : G.d j ≤ 2 * M.card + 1 := by rw [hdj']; exact hMcov
      omega

/-- **KKI cross packing (E-8).**  With `d i ≥ 2q + 1` for every independent vertex, there
is an edge-disjoint family `Tc` of `KKI` cross triangles `{inl a, inl b, inr i}` covering
all but at most `q` of the cross edges.  The clique edges used form a set `D` (no diagonal,
each clique vertex incident to at most `q` of them, `|D| ≤ |Tc|`), which is exactly what
the clique-remainder packing needs. -/
lemma E_8_cross_packing (G : SplitGraph)
    (hd : ∀ i : Fin G.q, 2 * G.q + 1 ≤ G.d i) :
    ∃ (Tc : Finset (Finset G.V)) (D : Finset (Sym2 (Fin G.p))),
      IsTrianglePacking G.graph Tc ∧
      (∀ e ∈ D, ¬ e.IsDiag) ∧
      (∀ v : Fin G.p, (D.filter (fun e => v ∈ e)).card ≤ G.q) ∧
      D.card ≤ Tc.card ∧
      (∀ t ∈ Tc, ∃ (a b : Fin G.p) (i : Fin G.q),
          a ≠ b ∧ s(a, b) ∈ D ∧ t = {Sum.inl a, Sum.inl b, Sum.inr i}) ∧
      ∑ i, G.d i ≤ 2 * Tc.card + G.q := by
  obtain ⟨Tc, D, hpack, hdiag, hinc, hDcard, hform, hcov⟩ :=
    cross_packing_upto G hd G.q le_rfl
  refine ⟨Tc, D, hpack, hdiag, hinc, hDcard, ?_, ?_⟩
  · intro t ht
    obtain ⟨a, b, i, hab, hDab, _, hteq⟩ := hform t ht
    exact ⟨a, b, i, hab, hDab, hteq⟩
  · have hfull : (Finset.univ.filter (fun i : Fin G.q => (i : ℕ) < G.q)) = Finset.univ := by
      ext i; simp
    rw [hfull] at hcov
    exact hcov

/-- An exact triangle decomposition has exactly `|E|/3` triangles. -/
lemma triangleDecomposition_card_edges
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (T : Finset (Finset V))
    (htri : ∀ t ∈ T, H.IsNClique 3 t)
    (hpart : ∀ e ∈ H.edgeFinset, ∃! t, t ∈ T ∧ ∀ v ∈ e, v ∈ t) :
    3 * T.card = H.edgeFinset.card := by
  have hdis : ∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ →
      Disjoint (edgesIn H t₁) (edgesIn H t₂) := by
    intro t₁ ht₁ t₂ ht₂ hne
    rw [Finset.disjoint_left]
    intro e he₁ he₂
    have he₁' := he₁
    have he₂' := he₂
    simp only [edgesIn, Finset.mem_filter] at he₁' he₂'
    apply hne
    apply (hpart e he₁'.1).unique
    · exact ⟨ht₁, he₁'.2⟩
    · exact ⟨ht₂, he₂'.2⟩
  have hunion : T.biUnion (edgesIn H) = H.edgeFinset := by
    ext e
    constructor
    · simp only [Finset.mem_biUnion]
      rintro ⟨t, _ht, he⟩
      simp only [edgesIn, Finset.mem_filter] at he
      exact he.1
    · intro he
      obtain ⟨t, ht, hcover⟩ := (hpart e he).exists
      simp only [Finset.mem_biUnion]
      exact ⟨t, ht, by
        simp only [edgesIn, Finset.mem_filter]
        exact ⟨he, hcover⟩⟩
  rw [← hunion, Finset.card_biUnion hdis]
  calc
    3 * T.card = ∑ _t ∈ T, 3 := by simp [mul_comm]
    _ = ∑ t ∈ T, (edgesIn H t).card := by
      apply Finset.sum_congr rfl
      intro t ht
      symm
      apply card_edgesIn_triangle
      simpa using htri t ht

/-- `|E(Kₚ − D')| = C(p,2) − |D'|` when `D'` consists of edges of `Kₚ`. -/
lemma edgeFinset_deleteEdges_card {p : ℕ} (D' : Finset (Sym2 (Fin p)))
    (hsub : D' ⊆ (⊤ : SimpleGraph (Fin p)).edgeFinset) :
    ((⊤ : SimpleGraph (Fin p)).deleteEdges (D' : Set (Sym2 (Fin p)))).edgeFinset.card
      = p.choose 2 - D'.card := by
  rw [SimpleGraph.edgeFinset_deleteEdges]
  have h := Finset.card_sdiff_add_card_eq_card hsub
  have ht : (⊤ : SimpleGraph (Fin p)).edgeFinset.card = p.choose 2 := by
    rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
  omega

/-- An exact triangle decomposition is in particular an (edge-disjoint) triangle packing. -/
lemma decomposition_isPacking {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (T : Finset (Finset V))
    (htri : ∀ t ∈ T, H.IsNClique 3 t)
    (hpart : ∀ e ∈ H.edgeFinset, ∃! t, t ∈ T ∧ ∀ v ∈ e, v ∈ t) :
    IsTrianglePacking H T := by
  refine ⟨htri, ?_⟩
  intro t₁ ht₁ t₂ ht₂ hne
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hcon
  rw [Finset.mem_inter] at hu hv
  have hadj : H.Adj u v := (htri t₁ ht₁).1 hu.1 hv.1 huv
  have hmem : s(u, v) ∈ H.edgeFinset := by rw [SimpleGraph.mem_edgeFinset]; exact hadj
  have hc1 : t₁ ∈ T ∧ ∀ w ∈ s(u, v), w ∈ t₁ :=
    ⟨ht₁, by intro w hw; rw [Sym2.mem_iff] at hw; rcases hw with rfl | rfl; exacts [hu.1, hv.1]⟩
  have hc2 : t₂ ∈ T ∧ ∀ w ∈ s(u, v), w ∈ t₂ :=
    ⟨ht₂, by intro w hw; rw [Sym2.mem_iff] at hw; rcases hw with rfl | rfl; exacts [hu.2, hv.2]⟩
  exact hne ((hpart s(u, v) hmem).unique hc1 hc2)

/-- Pushing a triangle packing along an injective graph homomorphism yields a triangle
packing of the image. -/
lemma trianglePacking_image {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (H : SimpleGraph V) (H' : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel H'.Adj]
    (f : V → W) (hf : Function.Injective f)
    (hhom : ∀ a b, H.Adj a b → H'.Adj (f a) (f b))
    {T : Finset (Finset V)} (hT : IsTrianglePacking H T) :
    IsTrianglePacking H' (T.image (fun t => t.image f)) := by
  classical
  refine ⟨?_, ?_⟩
  · intro s hs
    simp only [Finset.mem_image] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    have hclq := hT.1 t ht
    refine ⟨?_, ?_⟩
    · intro a ha b hb hab
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at ha hb
      obtain ⟨a', ha', rfl⟩ := ha
      obtain ⟨b', hb', rfl⟩ := hb
      exact hhom a' b' (hclq.1 ha' hb' (fun h => hab (by rw [h])))
    · rw [Finset.card_image_of_injective _ hf, hclq.2]
  · intro s₁ hs₁ s₂ hs₂ hne
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hs₁ hs₂
    obtain ⟨t₁, ht₁, rfl⟩ := hs₁
    obtain ⟨t₂, ht₂, rfl⟩ := hs₂
    have hne' : t₁ ≠ t₂ := fun h => hne (by rw [h])
    have hkey := hT.2 ht₁ ht₂ hne'
    rw [← Finset.image_inter _ _ hf, Finset.card_image_of_injective _ hf]
    exact hkey

/-- **Triangle-divisibility correction of the clique remainder** (E-B; residual analytic
step).  Given a set `D` of clique edges (edges of `Kₚ`, each vertex incident to at most `q`)
with `12q < p` and `p` large, one can delete a further set of at most `2p` clique edges so
that the resulting graph `R' = Kₚ − D'` is triangle-divisible (`|E| ≡ 0 mod 3`, all degrees
even) and still has minimum degree `≥ (0.9 + 1/100)·p`.

The parity part is `pathCorrection_odd_iff`; the `mod 3` part deletes a bounded `C₄`/`C₅`.
This is the sole residual analytic estimate of the §8 reduction. -/
lemma clique_divisible_correction :
    ∃ n₀ : ℕ, ∀ (p q : ℕ) (D : Finset (Sym2 (Fin p))),
      n₀ ≤ p → 12 * q < p →
      D ⊆ (⊤ : SimpleGraph (Fin p)).edgeFinset →
      (∀ v : Fin p, (D.filter (fun e => v ∈ e)).card ≤ q) →
      ∃ D' : Finset (Sym2 (Fin p)),
        D ⊆ D' ∧
        D' ⊆ (⊤ : SimpleGraph (Fin p)).edgeFinset ∧
        D'.card ≤ D.card + 2 * p ∧
        ((⊤ : SimpleGraph (Fin p)).deleteEdges (D' : Set (Sym2 (Fin p)))).edgeFinset.card % 3 = 0 ∧
        (∀ v : Fin p,
          Even (((⊤ : SimpleGraph (Fin p)).deleteEdges (D' : Set (Sym2 (Fin p)))).degree v)) ∧
        ((0.9 + 1 / 100) * (p : ℝ) ≤
          (((⊤ : SimpleGraph (Fin p)).deleteEdges (D' : Set (Sym2 (Fin p)))).minDegree : ℝ)) := by
  classical
  refine ⟨2000, fun p q D hp hq hDsub hinc => ?_⟩
  haveI : Nonempty (Fin p) := ⟨⟨0, by omega⟩⟩
  have edge_iff : ∀ e : Sym2 (Fin p),
      e ∈ (⊤ : SimpleGraph (Fin p)).edgeFinset ↔ ¬ e.IsDiag := by
    intro e; induction e using Sym2.ind with
    | _ a b => simp [Sym2.mk_isDiag_iff]
  have hD : ∀ e ∈ D, ¬ e.IsDiag := fun e he => (edge_iff e).mp (hDsub he)
  set H := (⊤ : SimpleGraph (Fin p)).deleteEdges (↑D) with hHdef
  have hmin : (p - 1 - q : ℕ) ≤ H.minDegree := clique_remainder_mindegree D hD hinc
  have hHdeg : ∀ v, p - 1 - q ≤ H.degree v := fun v =>
    le_trans hmin (SimpleGraph.minDegree_le_degree H v)
  have hδ : ∀ v, 9 * p ≤ 10 * H.degree v := by
    intro v; have := hHdeg v; omega
  obtain ⟨C, hCsub, hCcard, hCinc, hCeven, hCmod⟩ :=
    PaperIII.exists_divisible_correction_edges H (by omega) hδ
  -- `C` is disjoint from `D` and consists of edges of `Kₚ`
  have hCtop : C ⊆ (⊤ : SimpleGraph (Fin p)).edgeFinset := by
    intro e he
    have hmem : e ∈ H.edgeSet := hCsub he
    rw [SimpleGraph.mem_edgeFinset]
    revert hmem
    refine Sym2.ind (fun a b h => ?_) e
    rw [hHdef, SimpleGraph.mem_edgeSet, SimpleGraph.deleteEdges_adj] at h
    rw [SimpleGraph.mem_edgeSet]
    exact h.1
  have hChe : C ⊆ H.edgeFinset := by
    intro e he; rw [SimpleGraph.mem_edgeFinset]; exact hCsub he
  have hCD : Disjoint C D := by
    rw [Finset.disjoint_left]
    intro e heC heD
    have hmem : e ∈ H.edgeSet := hCsub heC
    revert hmem heD
    refine Sym2.ind (fun a b h1 h2 => ?_) e
    rw [hHdef, SimpleGraph.mem_edgeSet, SimpleGraph.deleteEdges_adj] at h2
    exact h2.2 (Finset.mem_coe.mpr h1)
  -- degree/edge-count of the corrected graph, computed with `⊤` as the base graph
  have hsubDC : ((D ∪ C : Finset (Sym2 (Fin p))) : Set (Sym2 (Fin p)))
      ⊆ (⊤ : SimpleGraph (Fin p)).edgeSet := by
    intro e he
    rw [Finset.mem_coe] at he
    have : e ∈ (⊤ : SimpleGraph (Fin p)).edgeFinset :=
      Finset.union_subset hDsub hCtop he
    rwa [SimpleGraph.mem_edgeFinset] at this
  have hsubD : ((D : Finset (Sym2 (Fin p))) : Set (Sym2 (Fin p)))
      ⊆ (⊤ : SimpleGraph (Fin p)).edgeSet := by
    intro e he
    rw [Finset.mem_coe] at he
    have : e ∈ (⊤ : SimpleGraph (Fin p)).edgeFinset := hDsub he
    rwa [SimpleGraph.mem_edgeFinset] at this
  have htopdeg : ∀ v : Fin p, (⊤ : SimpleGraph (Fin p)).degree v = p - 1 := by
    intro v; simpa using SimpleGraph.IsRegularOfDegree.top (V := Fin p) v
  have hHdegv : ∀ v, H.degree v = (p - 1) - incDeg D v := by
    intro v
    have h := PaperIII.degree_deleteEdges_of_subset (⊤ : SimpleGraph (Fin p)) D hsubD v
    rw [htopdeg] at h
    exact h
  have hincDC : ∀ v, incDeg (D ∪ C) v = incDeg D v + incDeg C v := by
    intro v; exact PaperIII.incDeg_union_of_disjoint hCD.symm v
  have hdegDC : ∀ v, ((⊤ : SimpleGraph (Fin p)).deleteEdges
      ((D ∪ C : Finset (Sym2 (Fin p))) : Set (Sym2 (Fin p)))).degree v
      = H.degree v - incDeg C v := by
    intro v
    rw [PaperIII.degree_deleteEdges_of_subset (⊤ : SimpleGraph (Fin p)) (D ∪ C) hsubDC v,
      htopdeg v, hincDC v, hHdegv v]
    omega
  have hcardDC : ((⊤ : SimpleGraph (Fin p)).deleteEdges
      ((D ∪ C : Finset (Sym2 (Fin p))) : Set (Sym2 (Fin p)))).edgeFinset.card
      = H.edgeFinset.card - C.card := by
    have h1 := edgeFinset_deleteEdges_card (D ∪ C) (Finset.union_subset hDsub hCtop)
    have h2 : H.edgeFinset.card = p.choose 2 - D.card :=
      edgeFinset_deleteEdges_card D hDsub
    have h3 : (D ∪ C).card = D.card + C.card := Finset.card_union_of_disjoint hCD.symm
    rw [h1, h2, h3]; omega
  refine ⟨D ∪ C, Finset.subset_union_left, Finset.union_subset hDsub hCtop, ?_, ?_, ?_, ?_⟩
  · -- cardinality
    have := Finset.card_union_le D C
    omega
  · -- edge count ≡ 0 (mod 3)
    rw [hcardDC]; exact hCmod
  · -- all degrees even
    intro v
    rw [hdegDC v]; exact hCeven v
  · -- minimum degree ≥ 0.91 p
    have hqle : q + 7 ≤ p := by omega
    have hmd : p - 1 - q - 6 ≤ ((⊤ : SimpleGraph (Fin p)).deleteEdges
        ((D ∪ C : Finset (Sym2 (Fin p))) : Set (Sym2 (Fin p)))).minDegree := by
      apply SimpleGraph.le_minDegree_of_forall_le_degree
      intro v
      rw [hdegDC v]
      have h1 := hHdeg v
      have h2 := hCinc v
      omega
    have hcast : ((p - 1 - q - 6 : ℕ) : ℝ) ≤
        (((⊤ : SimpleGraph (Fin p)).deleteEdges
          ((D ∪ C : Finset (Sym2 (Fin p))) : Set (Sym2 (Fin p)))).minDegree : ℝ) := by
      exact_mod_cast hmd
    have hp_real : (2000 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have hq_real : (12 : ℝ) * (q : ℝ) < (p : ℝ) := by exact_mod_cast hq
    have heq : ((p - 1 - q - 6 : ℕ) : ℝ) = (p : ℝ) - (q : ℝ) - 7 := by
      have hrw : p - 1 - q - 6 = p - (q + 7) := by omega
      rw [hrw, Nat.cast_sub hqle]
      push_cast
      ring
    rw [heq] at hcast
    have hlin : (0.9 + 1 / 100) * (p : ℝ) ≤ (p : ℝ) - (q : ℝ) - 7 := by
      nlinarith [hp_real, hq_real]
    linarith [hcast, hlin]

/-- **Clique-remainder packing via AX2 (E-8).**  For a set `D` of clique edges with each
vertex incident to at most `q` of them and `12q < p`, the remainder `R = Kₚ − D` has
`δ(R) ≥ p − 1 − q ≥ (0.9 + 1/100)·p`.  Correcting `R` to a triangle-divisible graph `R'`
(`clique_divisible_correction`) loses at most `2p` edges, and `AX2 (1/100)` decomposes `R'`
into clique triangles.  Mapping those triangles through `Sum.inl` yields a packing `Tk` of
`G.graph`, all of whose triangle edges avoid `D` (hence edge-disjoint from the KKI family),
covering all but at most `2p` clique edges of the remainder. -/
lemma E_8_clique_packing_of_AX2
    (hAX2 : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
        (H : SimpleGraph V) (_ : DecidableRel H.Adj),
        H.edgeFinset.card % 3 = 0 →
        (∀ v : V, Even (H.degree v)) →
        n₀ ≤ Fintype.card V →
        ((0.9 + ε) * (Fintype.card V : ℝ) ≤ (H.minDegree : ℝ)) →
        HasTriangleDecomposition H) :
    ∃ n₀ : ℕ, ∀ (G : SplitGraph) (D : Finset (Sym2 (Fin G.p))),
      n₀ ≤ G.p → 12 * G.q < G.p →
      (∀ e ∈ D, ¬ e.IsDiag) →
      (∀ v : Fin G.p, (D.filter (fun e => v ∈ e)).card ≤ G.q) →
      ∃ Tk : Finset (Finset G.V),
        IsTrianglePacking G.graph Tk ∧
        (∀ t ∈ Tk, ∃ (x y z : Fin G.p),
            x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
            t = {Sum.inl x, Sum.inl y, Sum.inl z} ∧
            s(x, y) ∉ D ∧ s(x, z) ∉ D ∧ s(y, z) ∉ D) ∧
        G.p.choose 2 ≤ 3 * Tk.card + D.card + 2 * G.p := by
  classical
  obtain ⟨nc, hcorr⟩ := clique_divisible_correction
  obtain ⟨na, hAX⟩ := hAX2 (1 / 100) (by norm_num)
  refine ⟨max nc na, fun G D hp hq hdiag hinc => ?_⟩
  have hnc : nc ≤ G.p := le_trans (le_max_left _ _) hp
  have hna : na ≤ G.p := le_trans (le_max_right _ _) hp
  have edge_iff : ∀ e : Sym2 (Fin G.p),
      e ∈ (⊤ : SimpleGraph (Fin G.p)).edgeFinset ↔ ¬ e.IsDiag := by
    intro e; induction e using Sym2.ind with
    | _ a b => simp [Sym2.mk_isDiag_iff]
  have hDsub : D ⊆ (⊤ : SimpleGraph (Fin G.p)).edgeFinset :=
    fun e he => (edge_iff e).mpr (hdiag e he)
  obtain ⟨D', hDD', hD'sub, hD'card, hmod3, heven, hmindeg⟩ :=
    hcorr G.p G.q D hnc hq hDsub hinc
  set R' := (⊤ : SimpleGraph (Fin G.p)).deleteEdges (D' : Set (Sym2 (Fin G.p))) with hR'def
  have hcardV : na ≤ Fintype.card (Fin G.p) := by rw [Fintype.card_fin]; exact hna
  have hmindeg' : (0.9 + 1 / 100) * (Fintype.card (Fin G.p) : ℝ) ≤ (R'.minDegree : ℝ) := by
    rw [Fintype.card_fin]; exact hmindeg
  obtain ⟨T', hT'tri, hT'part⟩ :=
    hAX (Fin G.p) inferInstance inferInstance R' inferInstance hmod3 heven hcardV hmindeg'
  have hcount : 3 * T'.card = R'.edgeFinset.card :=
    triangleDecomposition_card_edges R' T' hT'tri hT'part
  have hER' : R'.edgeFinset.card = G.p.choose 2 - D'.card :=
    edgeFinset_deleteEdges_card D' hD'sub
  have hD'le : D'.card ≤ G.p.choose 2 := by
    have hle := Finset.card_le_card hD'sub
    rwa [SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin] at hle
  refine ⟨T'.image (fun t => t.image (Sum.inl : Fin G.p → G.V)), ?_, ?_, ?_⟩
  · apply trianglePacking_image R' G.graph (Sum.inl : Fin G.p → G.V) Sum.inl_injective ?_
      (decomposition_isPacking R' T' hT'tri hT'part)
    intro a b hab
    rw [hR'def, SimpleGraph.deleteEdges_adj] at hab
    rcases hab with ⟨htop, _⟩
    exact (show a ≠ b by simpa using htop)
  · intro t ht
    simp only [Finset.mem_image] at ht
    obtain ⟨t', ht', rfl⟩ := ht
    have hclq := hT'tri t' ht'
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hclq.2
    have hne_of_D : ∀ {a b : Fin G.p}, R'.Adj a b → s(a, b) ∉ D := by
      intro a b hadj hmem
      rw [hR'def, SimpleGraph.deleteEdges_adj] at hadj
      exact hadj.2 (Finset.mem_coe.mpr (hDD' hmem))
    have hxin : x ∈ ({x, y, z} : Finset (Fin G.p)) := by simp
    have hyin : y ∈ ({x, y, z} : Finset (Fin G.p)) := by simp
    have hzin : z ∈ ({x, y, z} : Finset (Fin G.p)) := by simp
    refine ⟨x, y, z, hxy, hxz, hyz, ?_, ?_, ?_, ?_⟩
    · simp [Finset.image_insert, Finset.image_singleton]
    · exact hne_of_D (hclq.1 hxin hyin hxy)
    · exact hne_of_D (hclq.1 hxin hzin hxz)
    · exact hne_of_D (hclq.1 hyin hzin hyz)
  · have hTkcard :
        (T'.image (fun t => t.image (Sum.inl : Fin G.p → G.V))).card = T'.card :=
      Finset.card_image_of_injective _ (Finset.image_injective Sum.inl_injective)
    rw [hTkcard]
    omega

end PaperIII
