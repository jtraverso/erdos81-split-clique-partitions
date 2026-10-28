/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PaperIII.E_5
public import PaperIII.E_6
public import PaperIII.E_7
public import PaperIII.Identities

/-!
# Paper III — Proposition 10.1 (effective corridor, Layer E, NO axioms)

For `p ≥ 36`, `0 ≤ s ≤ 6√p` (i.e. `s² ≤ 36p`): `Φ ≤ n²/6 + 2n`.
For `p ≥ 2304`, `6√p ≤ s ≤ p/8` and `d(v) > (2n−1)/6 + 1` ∀v: `Φ ≤ n²/6`.
The machine-verifiable-unconditionally sub-result: only E-5, E-6, E-7 + algebra.
`#print axioms Prop_10_1` must show NO axioms (LEDGER Prop-10.1).
-/

@[expose] public section

namespace PaperIII

open SplitGraph

/-- `rp t ≤ t` for all `t`. -/
theorem rp_le (t : ℕ) : rp t ≤ t := by
  rw [rp]; split
  · omega
  · split <;> omega

/-- **L1 (handoff P1).** From `s² ≤ 36p` and `p ≥ 37`, an integer `s` satisfies `s ≤ p − 1`.
This is the integer step that lets the short corridor keep its `−s/2` term. -/
lemma s_le_p_sub_one {p s : ℕ} (hp : 37 ≤ p) (hs : s ^ 2 ≤ 36 * p) : s ≤ p - 1 := by
  have hpR : (37 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hsR : (s : ℝ) ^ 2 ≤ 36 * (p : ℝ) := by exact_mod_cast hs
  have hsltp : (s : ℝ) < (p : ℝ) := by nlinarith [hsR, hpR, Nat.cast_nonneg (α := ℝ) s]
  have hsltp' : s < p := by exact_mod_cast hsltp
  omega

/-- **L2 (handoff P1).** The sharpened short-corridor inequality with `C_corr = 3/2`:
`p/2 + (s²−6s+3)/12 ≤ (3/2)(3p−s)` for `p ≥ 37` and `s² ≤ 36p`. -/
lemma short_corridor_sharp {p s : ℕ} (hp : 37 ≤ p) (hs : s ^ 2 ≤ 36 * p) :
    (p : ℝ) / 2 + ((s : ℝ) ^ 2 - 6 * (s : ℝ) + 3) / 12
      ≤ (3 / 2) * (3 * (p : ℝ) - (s : ℝ)) := by
  have h1 : s + 1 ≤ p := by have := s_le_p_sub_one hp hs; omega
  have hsr : (s : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast h1
  have hsR : (s : ℝ) ^ 2 ≤ 36 * (p : ℝ) := by exact_mod_cast hs
  nlinarith [hsr, hsR]

/-- **Prop-10.1, low-corridor part**: for `p ≥ 37` and `0 ≤ s`, `s² ≤ 36p`,
`Φ(G) ≤ n²/6 + (3/2)n` (LEDGER Prop-10.1; from Corollary 5.3 and `short_corridor_sharp`, no
axioms). Sharpened constant `C_corr = 3/2` (handoff P1). -/
theorem Prop_10_1_low (G : SplitGraph) (hp : 37 ≤ G.p)
    (hs0 : 0 ≤ G.s) (hs : (G.s : ℝ) ^ 2 ≤ 36 * (G.p : ℝ)) :
    ((G.Phi : ℤ) : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + (3 / 2) * (G.n : ℝ) := by
  have hn : (G.n : ℝ) = (G.p : ℝ) + (G.q : ℝ) := by rw [SplitGraph.n]; push_cast; ring
  have hsr : (G.s : ℝ) = 2 * (G.p : ℝ) - (G.q : ℝ) := by rw [SplitGraph.s]; push_cast; ring
  -- integer value of s (nonnegative in the corridor) to feed the arithmetic lemmas
  set sN : ℕ := G.s.toNat with hsNdef
  have hsNz : (sN : ℤ) = G.s := by rw [hsNdef]; exact Int.toNat_of_nonneg hs0
  have hsNcast : (sN : ℝ) = (G.s : ℝ) := by exact_mod_cast hsNz
  have hsNsq : sN ^ 2 ≤ 36 * G.p := by
    have h : (sN : ℝ) ^ 2 ≤ 36 * (G.p : ℝ) := by rw [hsNcast]; exact hs
    exact_mod_cast h
  -- s ≤ p ⇒ q = 2p − s ≥ p ≥ r_p, q ≥ 1
  have hsp : (G.s : ℝ) ≤ (G.p : ℝ) := by
    have h2 : sN ≤ G.p := by have := s_le_p_sub_one hp hsNsq; omega
    have h2' : (sN : ℝ) ≤ (G.p : ℝ) := by exact_mod_cast h2
    rw [hsNcast] at h2'; exact h2'
  have hqp : G.p ≤ G.q := by
    have : (G.p : ℝ) ≤ (G.q : ℝ) := by rw [hsr] at hsp; linarith
    exact_mod_cast this
  have hrp : rp G.p ≤ G.q := le_trans (rp_le G.p) hqp
  have hq1 : 1 ≤ G.q := le_trans (by omega) hqp
  have h53 := cor_5_3 G hrp hq1
  -- sharpened corridor bound via the named lemma L2
  have hsharp := short_corridor_sharp hp hsNsq
  rw [hsNcast] at hsharp
  have hns : (3 : ℝ) * (G.p : ℝ) - (G.s : ℝ) = (G.n : ℝ) := by rw [hn, hsr]; ring
  rw [hns] at hsharp
  linarith [h53, hsharp]

private lemma sum_symmDiff_eq_two_dispersionD (G : SplitGraph) :
    ∑ i, ∑ j, (symmDiff (G.S i) (G.S j)).card = 2 * G.dispersionD := by
  unfold dispersionD; simp +decide [ symmDiff ] ; ring;
  -- By definition of $missCount$, we can rewrite the right-hand side of the equation.
  have h_missCount : ∀ x : Fin G.q, ∀ y : Fin G.q, (G.S x \ G.S y ∪ G.S y \ G.S x).card = ∑ z : Fin G.p, (if z ∈ G.S x then (if z ∈ G.S y then 0 else 1) else if z ∈ G.S y then 1 else 0) := by
    intro x y; rw [ Finset.card_eq_sum_ones ] ; rw [ ← Finset.sum_subset ( Finset.subset_univ _ ) ] ; simp +decide [ Finset.sum_ite ] ;
    any_goals exact Finset.univ;
    · rw [ ← Finset.card_union_of_disjoint ] ; congr ; ext ; aesop;
      · grind;
      · exact Finset.disjoint_left.mpr ( by aesop );
    · grind +splitIndPred;
  simp +decide only [h_missCount, Finset.sum_mul _ _ _];
  rw [ Finset.sum_comm ] ; rw [ Finset.sum_congr rfl fun i hi => Finset.sum_comm ] ; simp +decide [ Finset.sum_ite, Finset.filter_not, Finset.card_sdiff ] ; ring;
  rw [ Finset.sum_comm ] ; rw [ Finset.sum_congr rfl fun i hi => Finset.sum_add_distrib ] ; simp +decide [ Finset.sum_ite, Finset.filter_not, Finset.card_sdiff ] ; ring;
  exact Finset.sum_congr rfl fun _ _ => by rw [ SplitGraph.missCount ] ; ring;

private lemma center_deviation_eq (G : SplitGraph) (j : Fin G.q) :
    ShiftedCenter.AR G (G.S j) + ShiftedCenter.BR G (G.S j) =
      ∑ i, (symmDiff (G.S i) (G.S j)).card := by
  rw [ ShiftedCenter.AR, ShiftedCenter.BR, ← Finset.sum_add_distrib ];
  refine' Finset.sum_congr rfl fun i _ => _;
  unfold ShiftedCenter.tt ShiftedCenter.gg;
  rw [ ← Finset.card_union_of_disjoint ];
  · rfl;
  · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by aesop;

private lemma mid_corridor_profile_bounds (G : SplitGraph) (hp : 2304 ≤ G.p)
    (hs8 : 8 * (G.s : ℝ) ≤ (G.p : ℝ))
    (hdeg : ∀ i : Fin G.q, (2 * (G.n : ℝ) - 1) / 6 + 1 < (G.d i : ℝ)) :
    2 ≤ G.q ∧ (0 : ℝ) < (G.s : ℝ) ∧
      ∀ i : Fin G.q, 3 * G.m i ≤ G.s - 3 := by
  refine' ⟨ _, _, _ ⟩;
  · rcases G with ⟨ p, q, N ⟩ ; rcases q with ( _ | _ | q ) <;> norm_num at *;
    · norm_num [ SplitGraph.s ] at hs8 ; linarith [ ( by norm_cast : ( 2304 : ℝ ) ≤ p ) ];
    · simp_all +decide [ SplitGraph.d, SplitGraph.s, SplitGraph.n ];
      linarith [ show ( p : ℝ ) ≥ 2304 by norm_cast ];
  · contrapose! hdeg;
    norm_num [ SplitGraph.s, SplitGraph.n ] at *;
    obtain ⟨i, hi⟩ : ∃ i : Fin G.q, True := by
      exact ⟨ ⟨ 0, by norm_cast at *; linarith ⟩, trivial ⟩;
    exact ⟨ i, by linarith [ show ( G.d i : ℝ ) ≤ G.p by exact_mod_cast le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ] ⟩;
  · intro i
    have h_deg : (G.d i : ℚ) > (2 * (G.p + G.q) - 1) / 6 + 1 := by
      exact_mod_cast hdeg i;
    have h_m : (G.m i : ℚ) = G.p - G.d i := by
      simp +decide [ SplitGraph.m, SplitGraph.d, SplitGraph.S ];
      simp +decide [ Finset.card_compl ];
      rw [ Nat.cast_sub ( le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ) ];
    rw [ show ( G.s : ℤ ) = 2 * G.p - G.q from rfl ];
    exact Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℚ ] ; push_cast; linarith )

private lemma mid_profile_term_bound (G : SplitGraph) (hq : 2 ≤ G.q)
    (hm : ∀ i : Fin G.q, 3 * G.m i ≤ G.s - 3) :
    (((G.s : ℝ) - 1) * (G.M : ℝ) - (G.S₂ : ℝ)) / (G.q : ℝ)
      ≤ 2 * (G.s : ℝ) ^ 2 / 9 - 2 * (G.s : ℝ) / 3 := by
  -- Apply the pointwise inequality to each term in the sum.
  have h_pointwise : ∀ i : Fin G.q, ((G.s : ℝ) - 1) * (G.m i : ℝ) - (G.m i : ℝ) ^ 2 ≤ (2 * (G.s : ℝ) ^ 2 - 6 * (G.s : ℝ)) / 9 := by
    intro i
    have h_pointwise : (G.m i : ℝ) ≥ 0 ∧ 3 * (G.m i : ℝ) ≤ G.s - 3 := by
      exact ⟨ Nat.cast_nonneg _, mod_cast hm i ⟩;
    nlinarith [ sq_nonneg ( ( G.m i : ℝ ) - ( G.s - 3 ) / 3 ) ];
  rw [ div_le_iff₀ ];
  · convert Finset.sum_le_sum fun i ( hi : i ∈ Finset.univ ) => h_pointwise i using 1 ; norm_num [ SplitGraph.M, SplitGraph.S₂ ] ; ring;
    · rw [ Finset.mul_sum _ _ _, Finset.sum_sub_distrib ];
    · norm_num ; ring;
  · positivity

private lemma doubledFactors_ratio_bound (G : SplitGraph) (hp : 2304 ≤ G.p)
    (hs8 : 8 * (G.s : ℝ) ≤ (G.p : ℝ)) :
    (7 : ℝ) / 8 ≤ (G.doubledFactors : ℝ) / (rp G.p : ℝ) := by
  rw [ div_le_div_iff₀ ] <;> norm_cast;
  · unfold SplitGraph.doubledFactors SplitGraph.rp;
    unfold SplitGraph.s at hs8 ; norm_num at hs8 ; split_ifs <;> norm_num at *;
    · norm_cast at hs8;
      rw [ Int.subNatNat_eq_coe ] at hs8 ; omega;
    · norm_cast at hs8;
      rw [ Int.subNatNat_eq_coe ] at hs8 ; omega;
  · unfold rp; split_ifs <;> omega;

private lemma high_dispersionV_bound (G : SplitGraph) (hp : 2304 ≤ G.p)
    (hs8 : 8 * (G.s : ℝ) ≤ (G.p : ℝ))
    (hdeg : ∀ i : Fin G.q, (2 * (G.n : ℝ) - 1) / 6 + 1 < (G.d i : ℝ))
    (hD : (G.q : ℝ) * (G.s : ℝ) ^ 2 / 12 ≤ (G.dispersionD : ℝ)) :
    (G.q : ℝ) * ((G.q : ℝ) + 2) * (G.s : ℝ) ^ 2 / 24
      ≤ (G.dispersionV : ℝ) := by
  -- Let $m := \max_i m_i$, attained at index $j$ (Finite search often uses `Finset.max'`).
  obtain ⟨j, hj⟩ : ∃ j : Fin G.q, ∀ i : Fin G.q, G.m i ≤ G.m j := by
    simpa using Finset.exists_max_image Finset.univ ( fun i => G.m i ) ⟨ ⟨ 0, by
      rcases G with ⟨ _ | _ | Gq, _ | _ | Gp, hN ⟩ <;> norm_num at *;
      norm_num [ SplitGraph.s ] at hs8 ; linarith ⟩, Finset.mem_univ _ ⟩;
  -- From mid corridor profile bounds, have 3 * G.m j ≤ G.s - 3.
  have h_bound : 3 * (G.m j : ℝ) ≤ G.s - 3 := by
    have := mid_corridor_profile_bounds G hp hs8 hdeg;
    exact_mod_cast this.2.2 j;
  -- By E-6.1 (with m := G.m j), have V ≥ ((2p - 3m - 1)/4) * Σ |Sᵢ △ Sⱼ|.
  have h_e61 : ((2 * (G.p : ℝ) - 3 * (G.m j : ℝ) - 1) / 4) * (∑ i, ∑ j, ((symmDiff (G.S i) (G.S j)).card : ℝ)) ≤ (G.dispersionV : ℝ) := by
    convert E_6_1 G ( G.m j ) hj _ using 1;
    exact_mod_cast ( by linarith : ( 3 : ℝ ) * G.m j < 2 * G.p );
  -- By sum_symmDiff_eq_two_dispersionD, Σ |Sᵢ △ Sⱼ| = 2D.
  have h_sum_symmDiff : (∑ i, ∑ j, ((symmDiff (G.S i) (G.S j)).card : ℝ)) = 2 * (G.dispersionD : ℝ) := by
    exact_mod_cast sum_symmDiff_eq_two_dispersionD G;
  -- By mid corridor profile bounds, have 2p - 3m - 1 ≥ q + 2.
  have h_coeff : (2 * (G.p : ℝ) - 3 * (G.m j : ℝ) - 1) / 4 ≥ (G.q + 2 : ℝ) / 4 := by
    unfold SplitGraph.s at *; norm_num at *; linarith;
  nlinarith [ show ( G.q : ℝ ) ≥ 0 by positivity ]

private lemma Prop_10_1_mid_high (G : SplitGraph) (hp : 2304 ≤ G.p)
    (hs : 36 * (G.p : ℝ) ≤ (G.s : ℝ) ^ 2) (hs8 : 8 * (G.s : ℝ) ≤ (G.p : ℝ))
    (hdeg : ∀ i : Fin G.q, (2 * (G.n : ℝ) - 1) / 6 + 1 < (G.d i : ℝ))
    (hD : (G.q : ℝ) * (G.s : ℝ) ^ 2 / 12 ≤ (G.dispersionD : ℝ)) :
    ((G.Phi : ℤ) : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 := by
  have hmid := mid_corridor_profile_bounds G hp hs8 hdeg;
  have hterm := mid_profile_term_bound G hmid.1 hmid.2.2;
  have hdelta := doubledFactors_ratio_bound G hp hs8;
  have hV := high_dispersionV_bound G hp hs8 hdeg hD;
  have h_neg_term : -2 * ((G.doubledFactors : ℝ) / (rp G.p : ℝ)) * (G.dispersionV : ℝ) / ((G.q : ℝ) * ((G.q : ℝ) - 1)) ≤ -7 * (G.s : ℝ) ^ 2 / 96 := by
    rw [ div_le_iff₀ ] <;> nlinarith [ show ( G.q : ℝ ) ≥ 2 by norm_cast; linarith, show ( G.q : ℝ ) ^ 2 ≥ 4 by norm_cast; nlinarith ];
  have := E_5_2 G (by
  contrapose! hdelta; norm_num [ SplitGraph.doubledFactors ] at *;
  norm_num [ Nat.sub_eq_zero_of_le hdelta.le ] at *) (by
  linarith);
  have key : -2 * ((G.doubledFactors : ℝ) / (rp G.p : ℝ)) * (G.dispersionV : ℝ) /
      ((G.q : ℝ) * ((G.q : ℝ) - 1)) = -(2 * ((G.doubledFactors : ℝ) / (rp G.p : ℝ)) *
      (G.dispersionV : ℝ) / ((G.q : ℝ) * ((G.q : ℝ) - 1))) := by ring
  linarith [key, hmid.2.1]

private lemma exists_low_center (G : SplitGraph)
    (hD : (G.dispersionD : ℝ) < (G.q : ℝ) * (G.s : ℝ) ^ 2 / 12) :
    ∃ j : Fin G.q,
      (ShiftedCenter.AR G (G.S j) + ShiftedCenter.BR G (G.S j) : ℝ)
        < (G.s : ℝ) ^ 2 / 6 := by
  contrapose! hD;
  have h_sum : ∑ j : Fin G.q, (ShiftedCenter.AR G (G.S j) + ShiftedCenter.BR G (G.S j) : ℝ) ≥ G.q * (G.s : ℝ) ^ 2 / 6 := by
    exact le_trans ( by norm_num; linarith ) ( Finset.sum_le_sum fun _ _ => hD _ );
  have h_sum_eq1 : ∑ j : Fin G.q, (ShiftedCenter.AR G (G.S j) + ShiftedCenter.BR G (G.S j) : ℝ) = ∑ i : Fin G.q, ∑ j : Fin G.q, (symmDiff (G.S i) (G.S j)).card := by
    have h_sum_eq : ∀ j : Fin G.q, (ShiftedCenter.AR G (G.S j) + ShiftedCenter.BR G (G.S j) : ℝ) = ∑ i : Fin G.q, (symmDiff (G.S i) (G.S j)).card := by
      exact fun j => mod_cast center_deviation_eq G j;
    simp +decide only [h_sum_eq, Nat.cast_sum];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [ symmDiff_comm ] );
  have h_sum_eq2 : ∑ i : Fin G.q, ∑ j : Fin G.q, (symmDiff (G.S i) (G.S j)).card = 2 * G.dispersionD := by
    convert sum_symmDiff_eq_two_dispersionD G using 1;
  have h2 : ((∑ i : Fin G.q, ∑ j : Fin G.q, (symmDiff (G.S i) (G.S j)).card : ℕ) : ℝ) =
      2 * (G.dispersionD : ℝ) := by exact_mod_cast h_sum_eq2
  rw [h_sum_eq1] at h_sum
  push_cast at h_sum h2
  linarith

private lemma low_center_E7_hypotheses (G : SplitGraph) (hp : 2304 ≤ G.p)
    (hs8 : 8 * (G.s : ℝ) ≤ (G.p : ℝ))
    (hdeg : ∀ i : Fin G.q, (2 * (G.n : ℝ) - 1) / 6 + 1 < (G.d i : ℝ))
    (j : Fin G.q) :
    2 ≤ G.p - (G.S j).card ∧
    rp (G.p - (G.S j).card) ≤ G.q ∧
    rp (G.S j).card ≤ G.p - (G.S j).card ∧
    (∀ i, max (G.S j).card (G.q - rp (G.p - (G.S j).card)) ≤
      (G.p - (G.S j).card) - ShiftedCenter.tt G (G.S j) i) := by
  refine' ⟨ _, _, _, _ ⟩;
  · refine' le_tsub_of_add_le_left _;
    have h_m_le : 3 * (G.S j).card ≤ G.s - 3 := by
      convert mid_corridor_profile_bounds G hp hs8 hdeg |>.2.2 j using 1 <;> rfl;
    norm_num [ SplitGraph.s ] at * ; linarith;
  · refine' le_trans ( rp_le _ ) _;
    -- Since $G.s = 2 * G.p - G.q$, we have $G.p - G.s = G.q$.
    norm_cast at *;
    rw [ SplitGraph.n, SplitGraph.s ] at * ; omega;
  · have := mid_corridor_profile_bounds G hp hs8 hdeg;
    refine' le_trans _ ( show G.p - ( G.S j |> Finset.card ) ≥ 3 * ( G.S j |> Finset.card ) from _ );
    · exact le_trans ( rp_le _ ) ( by linarith );
    · norm_cast at *;
      exact le_tsub_of_add_le_left ( by push_cast [ Int.subNatNat_eq_coe ] at *; linarith! [ this.2.2 j, show G.m j = ( G.S j |> Finset.card ) from rfl ] );
  · intro i
    have h_card_S : (G.S j).card = G.m j := by
      rfl
    have h_card_S_i : ShiftedCenter.tt G (G.S j) i = (G.S i \ G.S j).card := by
      rfl
    simp [h_card_S, h_card_S_i] at *;
    have h_card_S_i : 3 * G.m j ≤ G.s - 3 ∧ 3 * (G.S i \ G.S j).card ≤ G.s - 3 := by
      have h_card_S_i : ∀ i : Fin G.q, 3 * G.m i ≤ G.s - 3 := by
        convert mid_corridor_profile_bounds G hp hs8 hdeg |>.2.2 using 1
      have h_card_S_i_j : 3 * (G.S i \ G.S j).card ≤ G.s - 3 := by
        exact le_trans ( mul_le_mul_of_nonneg_left ( Nat.cast_le.mpr ( Finset.card_le_card ( Finset.sdiff_subset ) ) ) zero_le_three ) ( h_card_S_i i )
      exact ⟨h_card_S_i j, h_card_S_i_j⟩;
    constructor <;> norm_cast at *;
    · lia;
    · unfold rp; split_ifs <;> norm_num at *;
      · grind +locals;
      · unfold SplitGraph.s at * ; omega;
      · unfold SplitGraph.s at * ; omega

private lemma low_center_A_coefficient (G : SplitGraph) (hp : 2304 ≤ G.p)
    (hs8 : 8 * (G.s : ℝ) ≤ (G.p : ℝ))
    (hdeg : ∀ i : Fin G.q, (2 * (G.n : ℝ) - 1) / 6 + 1 < (G.d i : ℝ))
    (j : Fin G.q) :
    ((G.s : ℝ) - 2 * ((G.S j).card : ℝ) - 1) / (G.q : ℝ)
      ≤ 5 * (G.s : ℝ) / (4 * (G.p : ℝ)) := by
  rw [ div_le_div_iff₀ ];
  · -- By mid_corridor_profile_bounds, we have $3 * G.m j ≤ G.s - 3$.
    have h_mj : 3 * G.m j ≤ G.s - 3 := by
      convert mid_corridor_profile_bounds G hp hs8 hdeg |>.2.2 j using 1 <;> rfl;
    -- By mid_corridor_profile_bounds, we have $G.s = 2 * G.p - G.q$.
    have h_s : (G.s : ℚ) = 2 * (G.p : ℚ) - (G.q : ℚ) := by
      unfold SplitGraph.s; norm_num;
    norm_cast at *;
    norm_num [ Int.subNatNat_eq_coe ] at * ; nlinarith;
  · exact Nat.cast_pos.mpr ( Fin.pos j );
  · positivity

private lemma low_center_B_algebra (P S R : ℝ) (hP : 0 < P) (hS : 0 < S)
    (h8 : 8 * S ≤ P) (hR : 0 ≤ R) (hR3 : 3 * R ≤ S - 3) :
    1 - 2 * ((P - 2 * R) / (P - R)) * ((P - S + R) / (2 * P - S))
      ≤ 5 * S / (4 * P) := by
  rw [ mul_div, sub_div', div_le_div_iff₀ ] <;> try nlinarith;
  field_simp;
  rw [ sub_div', mul_div_assoc', div_mul_eq_mul_div, mul_comm ];
  · rw [ div_le_iff₀ ] <;> nlinarith [ mul_le_mul_of_nonneg_left h8 hP.le, mul_le_mul_of_nonneg_left hR3 hP.le, mul_le_mul_of_nonneg_left h8 hS.le, mul_le_mul_of_nonneg_left hR3 hS.le ];
  · linarith

private lemma low_center_theta_factor (G : SplitGraph) (hp : 2304 ≤ G.p)
    (hs8 : 8 * (G.s : ℝ) ≤ (G.p : ℝ))
    (hdeg : ∀ i : Fin G.q, (2 * (G.n : ℝ) - 1) / 6 + 1 < (G.d i : ℝ))
    (j : Fin G.q) :
    (G.p : ℝ) - 2 * ((G.S j).card : ℝ) ≥ 0 ∧
    ((G.p : ℝ) - 2 * ((G.S j).card : ℝ)) /
        ((G.p : ℝ) - ((G.S j).card : ℝ))
      ≤ 1 - (max ((G.S j).card - 1) 0 : ℕ) /
        ((G.p - (G.S j).card : ℕ) : ℝ) := by
  constructor;
  · have h_rho : 3 * (G.S j).card ≤ G.s - 3 := by
      convert mid_corridor_profile_bounds G hp hs8 hdeg |>.2.2 j using 1 <;> rfl;
    norm_cast at *;
    rw [ Int.subNatNat_eq_coe ] at * ; omega;
  · rw [ Nat.cast_sub ];
    · rw [ one_sub_div ];
      · cases h : ( G.S j |> Finset.card ) <;> simp_all +decide;
        exact div_le_div_of_nonneg_right ( by linarith ) ( sub_nonneg_of_le <| by norm_cast; linarith [ show ( G.S j |> Finset.card ) ≤ G.p from le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ] );
      · have h_rho_le_s : 3 * (G.S j).card ≤ G.s - 3 := by
          convert mid_corridor_profile_bounds G hp hs8 hdeg |>.2.2 j using 1 <;> rfl;
        norm_cast at *;
        grind;
    · exact le_trans ( Finset.card_le_univ _ ) ( by norm_num )

private lemma low_center_u_factor (G : SplitGraph) (hp : 2304 ≤ G.p)
    (hs8 : 8 * (G.s : ℝ) ≤ (G.p : ℝ))
    (hdeg : ∀ i : Fin G.q, (2 * (G.n : ℝ) - 1) / 6 + 1 < (G.d i : ℝ))
    (j : Fin G.q) :
    ((G.p : ℝ) - (G.s : ℝ) + ((G.S j).card : ℝ)) /
        (2 * (G.p : ℝ) - (G.s : ℝ))
      ≤ ((G.q - rp (G.p - (G.S j).card) : ℕ) : ℝ) / (G.q : ℝ) := by
  rw [ Nat.cast_sub ];
  · rw [ show ( G.q : ℝ ) = 2 * G.p - G.s by
          unfold SplitGraph.s; norm_num; ];
    gcongr;
    · linarith;
    · unfold rp;
      split_ifs <;> norm_num at *;
      · linarith [ show ( G.S j |> Finset.card : ℝ ) ≤ G.p by exact_mod_cast le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ];
      · rw [ Nat.sub_sub, Nat.cast_sub ] <;> push_cast <;> linarith;
      · rw [ Nat.cast_sub ] <;> linarith;
  · convert low_center_E7_hypotheses G hp hs8 hdeg j |>.2.1 using 1

private lemma low_center_B_coefficient (G : SplitGraph) (hp : 2304 ≤ G.p)
    (hs8 : 8 * (G.s : ℝ) ≤ (G.p : ℝ))
    (hdeg : ∀ i : Fin G.q, (2 * (G.n : ℝ) - 1) / 6 + 1 < (G.d i : ℝ))
    (j : Fin G.q) :
    1 - 2 * (1 - (max ((G.S j).card - 1) 0 : ℕ) /
          ((G.p - (G.S j).card : ℕ) : ℝ))
          * ((G.q - rp (G.p - (G.S j).card) : ℕ) : ℝ) / (G.q : ℝ)
      ≤ 5 * (G.s : ℝ) / (4 * (G.p : ℝ)) := by
  have hmc := mid_corridor_profile_bounds G hp hs8 hdeg
  have hS0 : (0 : ℝ) < G.s := by exact_mod_cast hmc.2.1
  have hR3 : 3 * ((G.S j).card : ℝ) ≤ (G.s : ℝ) - 3 := by
    have h' : 3 * ((G.S j).card : ℤ) ≤ G.s - 3 := hmc.2.2 j
    exact_mod_cast h'
  have hq : (0 : ℝ) < G.q := by
    have : 2 ≤ G.q := hmc.1
    exact_mod_cast (by omega : 0 < G.q)
  have hP : (0 : ℝ) < G.p := by exact_mod_cast (by omega : 0 < G.p)
  have hRnn : (0 : ℝ) ≤ (G.S j).card := Nat.cast_nonneg _
  have hAlg := low_center_B_algebra G.p G.s (G.S j).card hP hS0 hs8 hRnn hR3
  obtain ⟨hθ0, hθ⟩ := low_center_theta_factor G hp hs8 hdeg j
  have hu := low_center_u_factor G hp hs8 hdeg j
  set T := (1 - (max ((G.S j).card - 1) 0 : ℕ) / ((G.p - (G.S j).card : ℕ) : ℝ)) with hT
  set B := ((G.q - rp (G.p - (G.S j).card) : ℕ) : ℝ) with hB
  set θ0 := ((G.p : ℝ) - 2 * ((G.S j).card : ℝ)) / ((G.p : ℝ) - ((G.S j).card : ℝ)) with hθ0def
  set u0 := ((G.p : ℝ) - (G.s : ℝ) + ((G.S j).card : ℝ)) / (2 * (G.p : ℝ) - (G.s : ℝ))
    with hu0def
  have hθ0nn : 0 ≤ θ0 := div_nonneg hθ0 (by linarith)
  have hu0nn : 0 ≤ u0 := div_nonneg (by linarith) (by linarith)
  have hkey : θ0 * u0 ≤ T * (B / G.q) := mul_le_mul hθ hu hu0nn (hθ0nn.trans hθ)
  calc 1 - 2 * T * B / (G.q : ℝ) = 1 - 2 * (T * (B / G.q)) := by ring
    _ ≤ 1 - 2 * (θ0 * u0) := by linarith
    _ = 1 - 2 * θ0 * u0 := by ring
    _ ≤ 5 * (G.s : ℝ) / (4 * (G.p : ℝ)) := hAlg

private lemma low_center_deviation_bound (G : SplitGraph) (hp : 2304 ≤ G.p)
    (hs8 : 8 * (G.s : ℝ) ≤ (G.p : ℝ))
    (hdeg : ∀ i : Fin G.q, (2 * (G.n : ℝ) - 1) / 6 + 1 < (G.d i : ℝ))
    (j : Fin G.q) :
    (1 - 2 * (1 - (max ((G.S j).card - 1) 0 : ℕ) /
          ((G.p - (G.S j).card : ℕ) : ℝ))
          * ((G.q - rp (G.p - (G.S j).card) : ℕ) : ℝ) / (G.q : ℝ))
          * (ShiftedCenter.BR G (G.S j) : ℝ)
      + (((G.s : ℝ) - 2 * ((G.S j).card : ℝ) - 1) *
          (ShiftedCenter.AR G (G.S j) : ℝ) -
          (ShiftedCenter.A2R G (G.S j) : ℝ)) / (G.q : ℝ)
    ≤ (5 * (G.s : ℝ) / (4 * (G.p : ℝ))) *
      ((ShiftedCenter.AR G (G.S j) + ShiftedCenter.BR G (G.S j) : ℕ) : ℝ) := by
  have := low_center_A_coefficient G hp hs8 hdeg j;
  have := low_center_B_coefficient G hp hs8 hdeg j;
  refine' le_trans ( add_le_add ( mul_le_mul_of_nonneg_right this _ ) _ ) _;
  exact ( 5 * G.s / ( 4 * G.p ) ) * ShiftedCenter.AR G ( G.S j );
  · exact Nat.cast_nonneg _;
  · convert le_trans _ ( mul_le_mul_of_nonneg_right ‹ ( G.s - 2 * ( G.S j |> Finset.card ) - 1 : ℝ ) / G.q ≤ 5 * G.s / ( 4 * G.p ) › ( Nat.cast_nonneg _ ) ) using 1 ; ring;
    linarith [ show ( 0 : ℝ ) ≤ ShiftedCenter.A2R G ( G.S j ) * ( G.q : ℝ ) ⁻¹ by exact mul_nonneg ( Nat.cast_nonneg _ ) ( inv_nonneg.mpr ( Nat.cast_nonneg _ ) ) ];
  · norm_num [ mul_add, add_comm ]

private lemma low_center_E7_bound (G : SplitGraph) (hp : 2304 ≤ G.p)
    (hs8 : 8 * (G.s : ℝ) ≤ (G.p : ℝ))
    (hdeg : ∀ i : Fin G.q, (2 * (G.n : ℝ) - 1) / 6 + 1 < (G.d i : ℝ))
    (j : Fin G.q)
    (hcenter : (ShiftedCenter.AR G (G.S j) + ShiftedCenter.BR G (G.S j) : ℝ)
      < (G.s : ℝ) ^ 2 / 6) :
    ((G.Phi : ℤ) : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + (G.p : ℝ) / 2 - (G.s : ℝ) ^ 2 / 64 := by
  contrapose! hcenter;
  contrapose! hcenter; have := low_center_E7_hypotheses G hp hs8 hdeg j; simp_all +decide ; (
  refine le_trans ( E_7_1 G ( G.S j ) ?_ ?_ ?_ ?_ ) ?_ <;> try linarith!;
  · grind;
  · have := low_center_deviation_bound G hp hs8 hdeg j; simp_all +decide ; (
    have h_baseline : - (G.s : ℝ) ^ 2 / 6 + (G.s : ℝ) * (G.S j).card - 2 * (G.S j).card ^ 2 ≤ - (G.s : ℝ) ^ 2 / 24 := by
      nlinarith only [ sq_nonneg ( ( G.s : ℝ ) - 4 * ( G.S j |> Finset.card ) ) ];
    have h_deviation : (5 * (G.s : ℝ) / (4 * (G.p : ℝ))) * ((ShiftedCenter.AR G (G.S j) + ShiftedCenter.BR G (G.S j) : ℕ) : ℝ) ≤ 5 * (G.s : ℝ) ^ 2 / 192 := by
      rw [ div_mul_eq_mul_div, div_le_iff₀ ] <;> try positivity;
      rw [ lt_div_iff₀ ] at hcenter <;> norm_num at * ; nlinarith [ ( by norm_cast : ( 2304 : ℝ ) ≤ G.p ) ] ;
    grind +splitIndPred))

private lemma Prop_10_1_mid_low (G : SplitGraph) (hp : 2304 ≤ G.p)
    (hs : 36 * (G.p : ℝ) ≤ (G.s : ℝ) ^ 2) (hs8 : 8 * (G.s : ℝ) ≤ (G.p : ℝ))
    (hdeg : ∀ i : Fin G.q, (2 * (G.n : ℝ) - 1) / 6 + 1 < (G.d i : ℝ))
    (hD : (G.dispersionD : ℝ) < (G.q : ℝ) * (G.s : ℝ) ^ 2 / 12) :
    ((G.Phi : ℤ) : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 := by
  obtain ⟨j, hcenter⟩ : ∃ j : Fin G.q, (ShiftedCenter.AR G (G.S j) + ShiftedCenter.BR G (G.S j) : ℝ) < (G.s : ℝ) ^ 2 / 6 := by
    apply exists_low_center
    convert hD using 1;
  convert low_center_E7_bound G hp hs8 hdeg j hcenter |> le_trans <| ?_ using 1;
  grind +splitIndPred

/-- **Prop-10.1, mid-corridor part**: for `p ≥ 2304`, `36p ≤ s²`, `8s ≤ p`, and the
degree bound `d(v) > (2n−1)/6 + 1` ∀v, `Φ(G) ≤ n²/6` (LEDGER Prop-10.1; from the
dispersion dichotomy E-5.2/E-6.1 vs E-7.1, no axioms). -/
theorem Prop_10_1_mid (G : SplitGraph) (hp : 2304 ≤ G.p)
    (hs : 36 * (G.p : ℝ) ≤ (G.s : ℝ) ^ 2) (hs8 : 8 * (G.s : ℝ) ≤ (G.p : ℝ))
    (hdeg : ∀ i : Fin G.q, (2 * (G.n : ℝ) - 1) / 6 + 1 < (G.d i : ℝ)) :
    ((G.Phi : ℤ) : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 := by
  by_cases hD : (G.q : ℝ) * (G.s : ℝ) ^ 2 / 12 ≤ (G.dispersionD : ℝ)
  · exact Prop_10_1_mid_high G hp hs hs8 hdeg hD
  · exact Prop_10_1_mid_low G hp hs hs8 hdeg (lt_of_not_ge hD)

end PaperIII