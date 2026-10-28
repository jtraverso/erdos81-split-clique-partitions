/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Paper III — E-3.1, the reduced 4-variable LP bound (dual side, by hand)

The heart of the lower bound `τ₃*(H(p,q,d)) ≥ F(p,q,d)`: any nonnegative
`(A,B,C,E)` satisfying the five aggregated triangle-constraint sums is at least the
three-branch minimum.  Here `A,B,C,E` are the total cover weights on the edge classes
`E(N), E(N,I), E(N,R), E(R)`, and the constraints (guarded by nonemptiness of the
corresponding triangle family) are the sums of the per-triangle constraints over the
families `NNI, NNN, NNR, NRR, RRR`.  In averaged variables `a = A/C(d,2)`,
`b = B/(qd)`, `c = C/(dr)`, `e = E/C(r,2)` these are exactly (3.1)–(3.2), and the goal
is the LP optimum (3.5).
-/

@[expose] public section

namespace PaperIII

set_option maxHeartbeats 800000 in
section

private lemma lp_AB_low (d q : ℝ) (A B : ℝ)
    (hd : 3 ≤ d) (hq : 1 ≤ q) (hqd : q ≤ d - 1) (hB : 0 ≤ B)
    (c1 : q * A + (d - 1) * B ≥ (d * (d - 1) / 2) * q)
    (c2 : (d - 2) * A ≥ d * (d - 1) * (d - 2) / 6) :
    A + B ≥ (d * (d - 1) / 2 + q * d) / 3 := by
  nlinarith [ mul_le_mul_of_nonneg_left hqd ( sub_nonneg.mpr hq ), mul_le_mul_of_nonneg_left hqd ( sub_nonneg.mpr hd ), mul_le_mul_of_nonneg_left hq ( sub_nonneg.mpr hqd ), mul_le_mul_of_nonneg_left hq ( sub_nonneg.mpr hd ), mul_le_mul_of_nonneg_left hd ( sub_nonneg.mpr hqd ), mul_le_mul_of_nonneg_left hd ( sub_nonneg.mpr hq ) ]

private lemma lp_AB_high (d q : ℝ) (A B : ℝ)
    (hd : 2 ≤ d) (hqd : d - 1 ≤ q) (hB : 0 ≤ B)
    (c1 : q * A + (d - 1) * B ≥ (d * (d - 1) / 2) * q) :
    A + B ≥ d * (d - 1) / 2 := by
  nlinarith

private lemma lp_CE_low (d r : ℝ) (C E : ℝ)
    (hd : 1 ≤ d) (hr : 3 ≤ r) (hdr : d ≤ r - 1)
    (c4 : (r - 1) * C + d * E ≥ d * (r * (r - 1) / 2))
    (c5 : (r - 2) * E ≥ r * (r - 1) * (r - 2) / 6) :
    C + E ≥ (d * r + r * (r - 1) / 2) / 3 := by
  nlinarith [ sq_nonneg ( r - 2 ) ]

private lemma lp_CE_high (d r : ℝ) (C E : ℝ)
    (hr : 3 ≤ r) (hrd : r - 1 ≤ d) (hC : 0 ≤ C)
    (c4 : (r - 1) * C + d * E ≥ d * (r * (r - 1) / 2)) :
    C + E ≥ r * (r - 1) / 2 := by
  nlinarith [ mul_le_mul_of_nonneg_left hrd hC ]

private lemma lp_cross_gap (d r q : ℝ) (A B C E : ℝ)
    (hd : 3 ≤ d) (hr : 3 ≤ r) (hq : 1 ≤ q)
    (hqd : q ≤ d - 1) (hrd : r ≤ d - 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (c1 : q * A + (d - 1) * B ≥ (d * (d - 1) / 2) * q)
    (c2 : (d - 2) * A ≥ d * (d - 1) * (d - 2) / 6)
    (c3 : r * A + (d - 1) * C ≥ (d * (d - 1) / 2) * r)
    (c4 : (r - 1) * C + d * E ≥ d * (r * (r - 1) / 2))
    (c5 : (r - 2) * E ≥ r * (r - 1) * (r - 2) / 6) :
    A + B + C + E ≥
      min (((d + r) * (d + r - 1) / 2 + q * d) / 3)
        (min (d * (d - 1) / 2 + r * (r - 1) / 2)
          (d * (d - 1) / 2 + (d * r + r * (r - 1) / 2) / 3)) := by
  -- Start by showing that $A+B \geq \min\left(\frac{d(d-1)}{2}, \frac{d(d-1)/2+qd}{3}\right)$.
  by_cases hAB : q + r ≤ d - 1;
  · rw [ min_def, min_def ] ; split_ifs ;
    · by_contra h_contra;
      have hE' : E ≥ r * (r - 1) / 6 := by
        nlinarith only [ hr, hE, c5 ];
      nlinarith only [ hd, hr, hq, hAB, h_contra, hE', c1, c2, c3, c4, c5, ‹ ( ( d + r ) * ( d + r - 1 ) / 2 + q * d ) / 3 ≤ d * ( d - 1 ) / 2 + r * ( r - 1 ) / 2 ›, sq_nonneg ( d - 2 ), sq_nonneg ( r - 2 ), sq_nonneg ( q - 1 ) ];
    · nlinarith [ sq_nonneg ( d - 3 ), sq_nonneg ( r - 3 ) ];
    · nlinarith [ sq_nonneg ( d - 3 ), sq_nonneg ( r - 3 ), mul_le_mul_of_nonneg_left hr ( sub_nonneg.mpr hrd ), mul_le_mul_of_nonneg_left hr ( sub_nonneg.mpr hqd ) ];
    · nlinarith [ sq_nonneg ( d - 3 ), sq_nonneg ( r - 3 ) ];
  · rw [ min_def, min_def ] ; split_ifs ;
    · by_contra h_contra;
      have hA_ge : A ≥ d * (d - 1) / 6 := by
        nlinarith only [ hd, hr, hq, hqd, hrd, c2, h_contra ];
      have hE_ge : E ≥ r * (r - 1) / 6 := by
        nlinarith only [ hr, hE, c5, sq_nonneg ( r - 2 ) ];
      have hC_ge : C ≥ (d * (d - 1) / 2 * r - r * A) / (d - 1) := by
        rw [ ge_iff_le, div_le_iff₀ ] <;> linarith;
      nlinarith only [ hd, hr, hq, hqd, hrd, hAB, h_contra, hA_ge, hE_ge, hC_ge, c1, c2, c3, c4, c5, ‹ ( ( d + r ) * ( d + r - 1 ) / 2 + q * d ) / 3 ≤ d * ( d - 1 ) / 2 + r * ( r - 1 ) / 2 ›, sq_nonneg ( d - r ), sq_nonneg ( d - 3 ), sq_nonneg ( r - 3 ) ];
    · by_contra h_contra;
      -- From the assumption $A + B + C + E < d * (d - 1) / 2 + r * (r - 1) / 2$, we can derive that $A < d * (d - 1) / 2$.
      have hA_lt : A < d * (d - 1) / 2 := by
        nlinarith [ sq_nonneg ( d - 3 ), sq_nonneg ( r - 3 ) ];
      by_cases hE_lt : E < r * (r - 1) / 6;
      · nlinarith only [ hd, hr, hq, hqd, hrd, hA, hB, hC, hE, c1, c2, c3, c4, c5, hAB, h_contra, hA_lt, hE_lt, ‹¬ ( ( d + r ) * ( d + r - 1 ) / 2 + q * d ) / 3 ≤ d * ( d - 1 ) / 2 + r * ( r - 1 ) / 2›, sq_nonneg ( r - 2 ) ];
      · nlinarith only [ hd, hr, hq, hqd, hrd, hA, hB, hC, hE, c1, c2, c3, c4, c5, hAB, h_contra, hA_lt, hE_lt, ‹¬ ( ( d + r ) * ( d + r - 1 ) / 2 + q * d ) / 3 ≤ d * ( d - 1 ) / 2 + r * ( r - 1 ) / 2› ];
    · nlinarith [ sq_nonneg ( d - r ), sq_nonneg ( d + r - 1 ) ];
    · nlinarith [ sq_nonneg ( d - 3 ), sq_nonneg ( r - 3 ) ]

private lemma lp_cross_case (d r q : ℝ) (A B C E : ℝ)
    (hd : 3 ≤ d) (hr : 3 ≤ r) (hq : 1 ≤ q)
    (hqd : q ≤ d - 1) (hrd : r - 1 ≤ d)
    (hdisc : r ≤ d - 1 ∨ r = d ∨ d = r - 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (c1 : q * A + (d - 1) * B ≥ (d * (d - 1) / 2) * q)
    (c2 : (d - 2) * A ≥ d * (d - 1) * (d - 2) / 6)
    (c3 : r * A + (d - 1) * C ≥ (d * (d - 1) / 2) * r)
    (c4 : (r - 1) * C + d * E ≥ d * (r * (r - 1) / 2))
    (c5 : (r - 2) * E ≥ r * (r - 1) * (r - 2) / 6) :
    A + B + C + E ≥
      min (((d + r) * (d + r - 1) / 2 + q * d) / 3)
        (min (d * (d - 1) / 2 + r * (r - 1) / 2)
          (d * (d - 1) / 2 + (d * r + r * (r - 1) / 2) / 3)) := by
  obtain h | h | h := hdisc <;> simp_all +decide [ min_def, sub_le_iff_le_add ];
  · convert lp_cross_gap d r q A B C E hd hr hq hqd h using 1;
    grind;
  · split_ifs <;> ring_nf at *;
    · by_contra h_contra;
      have h_div : (d - 2) ^ 2 * (d - 3) > 0 := by
        exact mul_pos ( sq_pos_of_pos ( by linarith ) ) ( by nlinarith );
      nlinarith only [ h, h_contra, h_div, c5, c4, c3, c2, c1, hq, hA, hB, hC, hE, hqd, ‹d * ( -1 / 3 ) + d * q * ( 1 / 3 ) + d ^ 2 * ( 2 / 3 ) ≤ -d + d ^ 2› ];
    · nlinarith [ sq_nonneg ( d - 3 ) ];
    · grind;
    · grind +qlia;
  · split_ifs <;> try nlinarith;
    by_contra h_contra;
    -- Substitute $r = d + 1$ into the inequalities.
    by_cases hr_eq : r = 3;
    · grind;
    · by_cases hr_gt : r > 3;
      · nlinarith only [ hr_gt, hq, hqd, c1, c2, c3, c4, c5, h_contra, ‹r * ( r - 1 ) / 2 ≤ ( ( r - 1 ) * r + r * ( r - 1 ) / 2 ) / 3›, ‹ ( ( r - 1 + r ) * ( r - 1 + r - 1 ) / 2 + q * ( r - 1 ) ) / 3 ≤ ( r - 1 ) * ( r - 1 - 1 ) / 2 + r * ( r - 1 ) / 2 ›, pow_pos ( sub_pos.mpr hr_gt ) 2, pow_pos ( sub_pos.mpr hr_gt ) 3 ];
      · exact hr_eq ( by linarith )

private lemma lp_dual_bound_generic (d r q : ℕ) (A B C E : ℝ)
    (hq : 1 ≤ q) (hd : 3 ≤ d) (hr : 3 ≤ r)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (c1 : (q : ℝ) * A + ((d : ℝ) - 1) * B ≥
      ((d : ℝ) * ((d : ℝ) - 1) / 2) * q)
    (c2 : ((d : ℝ) - 2) * A ≥
      (d : ℝ) * ((d : ℝ) - 1) * ((d : ℝ) - 2) / 6)
    (c3 : (r : ℝ) * A + ((d : ℝ) - 1) * C ≥
      ((d : ℝ) * ((d : ℝ) - 1) / 2) * r)
    (c4 : ((r : ℝ) - 1) * C + (d : ℝ) * E ≥
      (d : ℝ) * ((r : ℝ) * ((r : ℝ) - 1) / 2))
    (c5 : ((r : ℝ) - 2) * E ≥
      (r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) / 6) :
    A + B + C + E ≥
      min ((((d : ℝ) + r) * (((d : ℝ) + r) - 1) / 2 + (q : ℝ) * d) / 3)
        (min ((d : ℝ) * ((d : ℝ) - 1) / 2 + (r : ℝ) * ((r : ℝ) - 1) / 2)
          ((d : ℝ) * ((d : ℝ) - 1) / 2
            + ((d : ℝ) * r + (r : ℝ) * ((r : ℝ) - 1) / 2) / 3)) := by
  by_cases hq_le_d_minus_1 : q ≤ d - 1;
  · by_cases hrd : r - 1 ≤ d;
    · apply_rules [ lp_cross_case ];
      all_goals norm_cast;
      · grind;
      · rw [ Int.subNatNat_eq_coe ] ; omega;
      · grind;
    · have h_combined : A + B ≥ (d * (d - 1) / 2 + q * d) / 3 ∧ C + E ≥ (d * r + r * (r - 1) / 2) / 3 := by
        apply And.intro;
        · apply lp_AB_low;
          all_goals norm_cast;
          · rw [ Int.subNatNat_of_le ] <;> norm_cast ; linarith;
          · simpa [ Rat.divInt_eq_div ] using c1;
          · simpa [ Rat.divInt_eq_div ] using c2;
        · apply lp_CE_low;
          · norm_cast ; linarith;
          · norm_cast;
          · exact le_tsub_of_add_le_right ( by norm_cast; omega );
          · linarith;
          · convert c5 using 1;
      grind;
  · by_cases hrd_le_d : r - 1 ≤ d;
    · refine' le_trans ( min_le_right _ _ ) _;
      refine' le_trans ( min_le_left _ _ ) _;
      have := lp_AB_high d q A B ( by norm_cast; linarith ) ( by linarith [ show ( q : ℝ ) ≥ d by exact_mod_cast Nat.le_of_not_lt fun h => hq_le_d_minus_1 <| Nat.le_sub_one_of_lt h ] ) hB c1;
      nlinarith [ show ( r : ℝ ) ≥ 3 by norm_cast, show ( d : ℝ ) ≥ r - 1 by exact le_trans ( by cases r <;> norm_num at * ) ( Nat.cast_le.mpr hrd_le_d ) ];
    · refine' le_trans ( min_le_right _ _ ) _;
      rw [ min_le_iff ];
      refine' Or.inr _;
      -- Apply the lp_AB_high lemma to get $A + B \geq d * (d - 1) / 2$.
      have h_AB : A + B ≥ d * (d - 1) / 2 := by
        nlinarith [ show ( q : ℝ ) ≥ d by norm_cast; omega, show ( d : ℝ ) ≥ 3 by norm_cast ];
      have := lp_CE_low ( d := d ) ( r := r ) ( C := C ) ( E := E ) ( by linarith [ ( by norm_cast : ( 3 : ℝ ) ≤ d ), ( by norm_cast : ( 3 : ℝ ) ≤ r ) ] ) ( by linarith [ ( by norm_cast : ( 3 : ℝ ) ≤ d ), ( by norm_cast : ( 3 : ℝ ) ≤ r ) ] ) ( by linarith [ ( by norm_cast : ( 3 : ℝ ) ≤ d ), ( by norm_cast : ( 3 : ℝ ) ≤ r ), show ( r : ℝ ) ≥ d + 2 by norm_cast; omega ] ) c4 c5; linarith;

end

set_option maxHeartbeats 800000 in
private lemma lp_dual_bound_small (d r q : ℕ) (A B C E : ℝ)
    (hq : 1 ≤ q) (hp : 3 ≤ d + r) (hsmall : d < 3 ∨ r < 3)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (c1 : 2 ≤ d → (q : ℝ) * A + ((d : ℝ) - 1) * B ≥
      ((d : ℝ) * ((d : ℝ) - 1) / 2) * q)
    (c2 : 3 ≤ d → ((d : ℝ) - 2) * A ≥
      (d : ℝ) * ((d : ℝ) - 1) * ((d : ℝ) - 2) / 6)
    (c3 : 2 ≤ d → 1 ≤ r → (r : ℝ) * A + ((d : ℝ) - 1) * C ≥
      ((d : ℝ) * ((d : ℝ) - 1) / 2) * r)
    (c4 : 1 ≤ d → 2 ≤ r → ((r : ℝ) - 1) * C + (d : ℝ) * E ≥
      (d : ℝ) * ((r : ℝ) * ((r : ℝ) - 1) / 2))
    (c5 : 3 ≤ r → ((r : ℝ) - 2) * E ≥
      (r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) / 6) :
    A + B + C + E ≥
      min ((((d : ℝ) + r) * (((d : ℝ) + r) - 1) / 2 + (q : ℝ) * d) / 3)
        (min ((d : ℝ) * ((d : ℝ) - 1) / 2 + (r : ℝ) * ((r : ℝ) - 1) / 2)
          ((d : ℝ) * ((d : ℝ) - 1) / 2
            + ((d : ℝ) * r + (r : ℝ) * ((r : ℝ) - 1) / 2) / 3)) := by
  by_cases hd : 3 ≤ d
  · have hr : r < 3 := hsmall.resolve_left (by omega)
    interval_cases r
    · by_cases hqd : (q : ℝ) ≤ d - 1
      · refine le_trans (min_le_left _ _) ?_
        have hab := lp_AB_low (d : ℝ) (q : ℝ) A B (by norm_cast) (by norm_cast)
          hqd hB (c1 (by omega)) (c2 hd)
        nlinarith
      · refine le_trans (le_trans (min_le_right _ _) (min_le_left _ _)) ?_
        have hab := lp_AB_high (d : ℝ) (q : ℝ) A B (by norm_cast; omega)
          (by linarith) hB (c1 (by omega))
        nlinarith
    ·
      rcases d with ( _ | _ | _ | d ) <;> norm_num at *;
      contrapose! c1;
      ring_nf at *;
      by_cases hq_ge_d : q ≥ d + 2;
      · nlinarith only [ hA, hB, hC, hE, c1, c2, c3, show ( q : ℝ ) ≥ d + 2 by norm_cast ];
      · nlinarith only [ c1, c2, c3, show ( q : ℝ ) ≤ d + 1 by norm_cast; linarith, hq_ge_d, hA, hB, hC, hE ]
    · by_cases hqd : (q : ℝ) ≤ d - 1
      · have hab := lp_AB_low (d : ℝ) (q : ℝ) A B (by norm_cast) (by norm_cast)
          hqd hB (c1 (by omega)) (c2 hd)
        have hc2 := c2 hd
        have hc3 := c3 (by omega) (by omega)
        have hc4 := c4 (by omega) (by omega)
        rcases d with ( _ | _ | _ | d ) <;> norm_num at *;
        by_cases hq_cases : q ≤ d + 1;
        · by_cases hq_cases : q ≤ d;
          · contrapose! hq_cases;
            exact_mod_cast ( by nlinarith [ sq ( d : ℝ ) ] : ( d : ℝ ) < q );
          · norm_num [ show q = d + 1 by linarith ] at *;
            exact Classical.or_iff_not_imp_left.2 fun h => Classical.or_iff_not_imp_left.2 fun h' => by nlinarith;
        · norm_num [ show q = d + 2 by exact le_antisymm ( by exact_mod_cast hqd ) ( by linarith ) ] at *;
          exact Or.inr <| Or.inl <| by nlinarith only [ hab, hc3, hc4, hA, hB, hC, hE ] ;
      · have hab := lp_AB_high (d : ℝ) (q : ℝ) A B (by norm_cast; omega)
          (by linarith) hB (c1 (by omega))
        have hc4 := c4 (by omega) (by omega)
        have hdreal : (3 : ℝ) ≤ d := by norm_cast
        have hce : 1 ≤ C + E := by nlinarith [mul_nonneg (sub_nonneg.mpr (show (1 : ℝ) ≤ d by linarith)) hC]
        refine le_trans (le_trans (min_le_right _ _) (min_le_left _ _)) ?_
        norm_num at *
        nlinarith
  · have hdlt : d < 3 := by omega
    interval_cases d
    · have hr : 3 ≤ r := by omega
      have hc5 := c5 hr
      refine le_trans (min_le_left _ _) ?_
      have hrr : (3 : ℝ) ≤ r := by norm_cast
      nlinarith [sq_nonneg ((r : ℝ) - 2)]
    ·
      rcases r with ( _ | _ | _ | r ) <;> norm_num at *;
      · exact Or.inr ( by linarith );
      · exact Or.inr <| Or.inr <| by nlinarith [ sq_nonneg ( r : ℝ ) ] ;
    ·
      rcases r with ( _ | _ | _ | r ) <;> norm_num at *;
      · exact Or.inr ( by linarith );
      · exact Or.inr ( by linarith [ show ( q : ℝ ) ≥ 1 by norm_cast ] );
      · by_cases h_case : E ≥ (r + 3) * (r + 2) / 6;
        · contrapose! h_case;
          rcases q with ( _ | _ | q ) <;> norm_num at *;
          · nlinarith only [ c1, c3, c4, h_case ];
          · nlinarith [ mul_nonneg ( Nat.cast_nonneg q : ( 0 : ℝ ) ≤ q ) ( Nat.cast_nonneg r : ( 0 : ℝ ) ≤ r ) ];
        · nlinarith [ sq ( r : ℝ ) ]

/-- **Reduced LP lower bound** (dual certificate of E-3.1).  Variables are cast from
`ℕ` so the nonemptiness guards behave; `p = d + r ≥ 3`, `q ≥ 1`. -/
theorem lp_dual_bound_real (d r q : ℕ) (A B C E : ℝ)
    (hq : 1 ≤ q) (hp : 3 ≤ d + r)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (c1 : 2 ≤ d → (q : ℝ) * A + ((d : ℝ) - 1) * B ≥ ((d : ℝ) * ((d : ℝ) - 1) / 2) * q)
    (c2 : 3 ≤ d → ((d : ℝ) - 2) * A ≥ (d : ℝ) * ((d : ℝ) - 1) * ((d : ℝ) - 2) / 6)
    (c3 : 2 ≤ d → 1 ≤ r →
      (r : ℝ) * A + ((d : ℝ) - 1) * C ≥ ((d : ℝ) * ((d : ℝ) - 1) / 2) * r)
    (c4 : 1 ≤ d → 2 ≤ r →
      ((r : ℝ) - 1) * C + (d : ℝ) * E ≥ (d : ℝ) * ((r : ℝ) * ((r : ℝ) - 1) / 2))
    (c5 : 3 ≤ r → ((r : ℝ) - 2) * E ≥ (r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) / 6) :
    A + B + C + E ≥
      min ((((d : ℝ) + r) * (((d : ℝ) + r) - 1) / 2 + (q : ℝ) * d) / 3)
        (min ((d : ℝ) * ((d : ℝ) - 1) / 2 + (r : ℝ) * ((r : ℝ) - 1) / 2)
          ((d : ℝ) * ((d : ℝ) - 1) / 2
            + ((d : ℝ) * r + (r : ℝ) * ((r : ℝ) - 1) / 2) / 3)) := by
  by_cases hd : 3 ≤ d
  · by_cases hr : 3 ≤ r
    · exact lp_dual_bound_generic d r q A B C E hq hd hr hA hB hC hE
        (c1 (by omega)) (c2 hd) (c3 (by omega) (by omega))
        (c4 (by omega) (by omega)) (c5 hr)
    · exact lp_dual_bound_small d r q A B C E hq hp (Or.inr (by omega))
        hA hB hC hE c1 c2 c3 c4 c5
  · exact lp_dual_bound_small d r q A B C E hq hp (Or.inl (by omega))
      hA hB hC hE c1 c2 c3 c4 c5

end PaperIII