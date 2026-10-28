/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PaperIII.Defs

/-!
# Paper III — Fractional packing/cover weak duality

The one LP-duality layer everything in E-3.x/E-4.x rests on (agent instructions §2):
fractional triangle covers, weak duality `Σw ≤ Σy`, and the resulting API for `ν₃*`:
`le_nu3Star_of_packing` (primal lower bounds) and `nu3Star_le_of_cover` (dual upper
bounds).
-/

@[expose] public section

namespace PaperIII

variable {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]

/-- The edges of `H` contained in the vertex set `t`. -/
def edgesIn (t : Finset W) : Finset (Sym2 W) :=
  H.edgeFinset.filter fun e => ∀ v ∈ e, v ∈ t

/-- A fractional triangle cover: nonnegative edge weights with total weight at least 1
inside each triangle. -/
def IsFracCover (y : Sym2 W → ℝ) : Prop :=
  (∀ e, 0 ≤ y e) ∧ ∀ t ∈ H.cliqueFinset 3, 1 ≤ ∑ e ∈ edgesIn H t, y e

/-- **Weak LP duality**: any fractional packing value is at most any fractional cover
value. -/
theorem weak_duality {w : Finset W → ℝ} {y : Sym2 W → ℝ}
    (hw : IsFracPacking H w) (hy : IsFracCover H y) :
    ∑ t ∈ H.cliqueFinset 3, w t ≤ ∑ e ∈ H.edgeFinset, y e := by
  obtain ⟨hw0, -, hwe⟩ := hw
  obtain ⟨hy0, hyt⟩ := hy
  calc ∑ t ∈ H.cliqueFinset 3, w t
      ≤ ∑ t ∈ H.cliqueFinset 3, w t * ∑ e ∈ edgesIn H t, y e := by
        refine Finset.sum_le_sum fun t ht => ?_
        conv_lhs => rw [← mul_one (w t)]
        exact mul_le_mul_of_nonneg_left (hyt t ht) (hw0 t)
    _ = ∑ t ∈ H.cliqueFinset 3, ∑ e ∈ H.edgeFinset,
          if ∀ v ∈ e, v ∈ t then w t * y e else 0 := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.mul_sum, edgesIn, Finset.sum_filter]
    _ = ∑ e ∈ H.edgeFinset, ∑ t ∈ H.cliqueFinset 3,
          if ∀ v ∈ e, v ∈ t then w t * y e else 0 := Finset.sum_comm
    _ = ∑ e ∈ H.edgeFinset,
          (∑ t ∈ (H.cliqueFinset 3).filter (fun t => ∀ v ∈ e, v ∈ t), w t) * y e := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.sum_mul, Finset.sum_filter]
    _ ≤ ∑ e ∈ H.edgeFinset, 1 * y e := by
        refine Finset.sum_le_sum fun e he => ?_
        exact mul_le_mul_of_nonneg_right (hwe e he) (hy0 e)
    _ = ∑ e ∈ H.edgeFinset, y e := by simp

/-- The zero weighting is a fractional packing. -/
theorem zero_isFracPacking : IsFracPacking H (fun _ => 0) :=
  ⟨fun _ => le_refl 0, fun _ h => absurd rfl h, fun _ _ => by simp⟩

/-- Every triangle contains at least one edge. -/
theorem edgesIn_nonempty {t : Finset W} (ht : t ∈ H.cliqueFinset 3) :
    (edgesIn H t).Nonempty := by
  rw [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff] at ht
  obtain ⟨hclique, hcard⟩ := ht
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (by omega : 1 < t.card)
  refine ⟨s(u, v), ?_⟩
  rw [edgesIn, Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  refine ⟨hclique hu hv huv, fun x hx => ?_⟩
  rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption

/-- The all-ones edge weighting is a fractional cover. -/
theorem allOnes_isFracCover : IsFracCover H (fun _ => 1) := by
  refine ⟨fun _ => zero_le_one, fun t ht => ?_⟩
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (Finset.card_ne_zero.mpr (edgesIn_nonempty H ht))

/-- The set of fractional packing values is bounded above. -/
theorem bddAbove_packingValues :
    BddAbove {x | ∃ w : Finset W → ℝ, IsFracPacking H w ∧
      x = ∑ t ∈ H.cliqueFinset 3, w t} := by
  refine ⟨∑ e ∈ H.edgeFinset, (1 : ℝ), ?_⟩
  rintro x ⟨w, hw, rfl⟩
  exact weak_duality H hw (allOnes_isFracCover H)

/-- The set of fractional packing values is nonempty (the zero packing). -/
theorem packingValues_nonempty :
    {x | ∃ w : Finset W → ℝ, IsFracPacking H w ∧
      x = ∑ t ∈ H.cliqueFinset 3, w t}.Nonempty :=
  ⟨0, fun _ => 0, zero_isFracPacking H, by simp⟩

/-- Primal bound: any fractional packing value is at most `ν₃*`. -/
theorem le_nu3Star_of_packing {w : Finset W → ℝ} (hw : IsFracPacking H w) :
    ∑ t ∈ H.cliqueFinset 3, w t ≤ nu3Star H :=
  le_csSup (bddAbove_packingValues H) ⟨w, hw, rfl⟩

/-- Dual bound: `ν₃*` is at most any fractional cover value. -/
theorem nu3Star_le_of_cover {y : Sym2 W → ℝ} (hy : IsFracCover H y) :
    nu3Star H ≤ ∑ e ∈ H.edgeFinset, y e := by
  refine csSup_le (packingValues_nonempty H) ?_
  rintro x ⟨w, hw, rfl⟩
  exact weak_duality H hw hy

/-- `ν₃* ≥ 0`. -/
theorem nu3Star_nonneg : 0 ≤ nu3Star H := by
  have := le_nu3Star_of_packing H (zero_isFracPacking H)
  simpa using this

/-! ## The fractional cover optimum `τ₃*`

By classical finite LP duality `ν₃* = τ₃*`; mathlib has no strong-duality package, and
the paper's §3/§4 arguments are cover-side, so the ledger's "fractional optimum" is
formalized as `τ₃*` where the proof is cover-side.  Weak duality (`nu3Star_le_tau3Star`)
keeps the two connected. -/

/-- `τ₃* H` = the fractional triangle-cover optimum (LP value), as a real `csInf`. -/
noncomputable def tau3Star : ℝ :=
  sInf {x | ∃ y : Sym2 W → ℝ, IsFracCover H y ∧ x = ∑ e ∈ H.edgeFinset, y e}

/-- The set of fractional cover values is nonempty (the all-ones cover). -/
theorem coverValues_nonempty :
    {x | ∃ y : Sym2 W → ℝ, IsFracCover H y ∧
      x = ∑ e ∈ H.edgeFinset, y e}.Nonempty :=
  ⟨∑ e ∈ H.edgeFinset, (1 : ℝ), fun _ => 1, allOnes_isFracCover H, rfl⟩

/-- The set of fractional cover values is bounded below (by `0`). -/
theorem bddBelow_coverValues :
    BddBelow {x | ∃ y : Sym2 W → ℝ, IsFracCover H y ∧
      x = ∑ e ∈ H.edgeFinset, y e} := by
  refine ⟨0, ?_⟩
  rintro x ⟨y, hy, rfl⟩
  exact Finset.sum_nonneg fun e _ => hy.1 e

/-- Dual bound: `τ₃*` is at most any fractional cover value. -/
theorem tau3Star_le_of_cover {y : Sym2 W → ℝ} (hy : IsFracCover H y) :
    tau3Star H ≤ ∑ e ∈ H.edgeFinset, y e :=
  csInf_le (bddBelow_coverValues H) ⟨y, hy, rfl⟩

/-- Lower bound on `τ₃*` from a lower bound on every fractional cover value. -/
theorem le_tau3Star (c : ℝ)
    (h : ∀ y : Sym2 W → ℝ, IsFracCover H y → c ≤ ∑ e ∈ H.edgeFinset, y e) :
    c ≤ tau3Star H := by
  refine le_csInf (coverValues_nonempty H) ?_
  rintro x ⟨y, hy, rfl⟩
  exact h y hy

/-- Weak duality between the two LP optima: `ν₃* ≤ τ₃*`. -/
theorem nu3Star_le_tau3Star : nu3Star H ≤ tau3Star H := by
  refine le_tau3Star H _ fun y hy => ?_
  exact nu3Star_le_of_cover H hy

/-! ## Integral packing API for `ν₃` -/

/-- Any triangle packing bounds `ν₃` from below. -/
theorem le_nu3_of_packing {T : Finset (Finset W)} (hT : IsTrianglePacking H T) :
    T.card ≤ nu3 H := by
  have hbdd : BddAbove {k | ∃ T : Finset (Finset W),
      IsTrianglePacking H T ∧ T.card = k} := by
    refine ⟨(Finset.univ : Finset (Finset W)).card, ?_⟩
    rintro k ⟨T', _, rfl⟩
    exact Finset.card_le_card (Finset.subset_univ T')
  exact le_csSup hbdd ⟨T, hT, rfl⟩

end PaperIII
