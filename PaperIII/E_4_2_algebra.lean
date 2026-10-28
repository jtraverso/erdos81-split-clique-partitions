/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PaperIII.Identities

/-!
# Paper III — E-4.2, the per-branch algebra (the 45,904-case audit, as general proofs)

The completion-of-squares inequality (4.5): each branch of `F(p,q,d)` is at least
`qd/2 + (C_α + μ(α))p² − p/2` for `0 < q ≤ 2p`, `0 ≤ d ≤ p`, `α = q/p`.  Pure `ℚ`
algebra; the third branch is dominated per Appendix A (the residual
`α(8−5α)/48` / `(2−α)²/12` is never below `μ(α)`).
-/

@[expose] public section

namespace PaperIII

open SplitGraph

variable {P Q D : ℚ}

/-- `α ≤ 2/3 ↔ 3q ≤ 2p` (for `p > 0`). -/
theorem alpha_le_iff (hP : 0 < P) : Q / P ≤ 2 / 3 ↔ 3 * Q ≤ 2 * P := by
  rw [div_le_div_iff₀ hP (by norm_num : (0:ℚ) < 3)]
  constructor <;> intro h <;> linarith

/-- `μ(Q/P)·P² = Q²/12` on the low branch `3Q ≤ 2P`. -/
theorem mu_mul_sq_low (hP : 0 < P) (h : 3 * Q ≤ 2 * P) :
    mu (Q / P) * P ^ 2 = Q ^ 2 / 12 := by
  rw [mu, if_pos ((alpha_le_iff hP).mpr h)]
  field_simp

/-- `μ(Q/P)·P² = (2P−Q)²/48` on the high branch `2P ≤ 3Q`. -/
theorem mu_mul_sq_high (hP : 0 < P) (h : 2 * P ≤ 3 * Q) :
    mu (Q / P) * P ^ 2 = (2 * P - Q) ^ 2 / 48 := by
  rw [mu]
  by_cases hc : Q / P ≤ 2 / 3
  · have h3 : 3 * Q ≤ 2 * P := (alpha_le_iff hP).mp hc
    have h0 : 2 * P - 3 * Q = 0 := by linarith
    rw [if_pos hc]
    have hL : (Q / P) ^ 2 / 12 * P ^ 2 = Q ^ 2 / 12 := by field_simp
    rw [hL]
    linear_combination (-(2 * P + Q) / 48) * h0
  · rw [if_neg hc]
    have hL : (2 - Q / P) ^ 2 / 48 * P ^ 2 = (2 * P - Q) ^ 2 / 48 := by
      have : (2 - Q / P) * P = 2 * P - Q := by field_simp
      calc (2 - Q / P) ^ 2 / 48 * P ^ 2 = ((2 - Q / P) * P) ^ 2 / 48 := by ring
        _ = (2 * P - Q) ^ 2 / 48 := by rw [this]
    exact hL

/-- `C_α(Q/P)·P² = (2P² − 2QP − Q²)/12`. -/
theorem Ca_mul_sq (hP : 0 < P) :
    Cα (Q / P) * P ^ 2 = (2 * P ^ 2 - 2 * Q * P - Q ^ 2) / 12 := by
  rw [Cα]
  have h1 : (Q / P) * P = Q := by field_simp
  have h2 : (Q / P) ^ 2 * P ^ 2 = Q ^ 2 := by
    calc (Q / P) ^ 2 * P ^ 2 = ((Q / P) * P) ^ 2 := by ring
      _ = Q ^ 2 := by rw [h1]
  calc (2 - 2 * (Q / P) - (Q / P) ^ 2) / 12 * P ^ 2
      = (2 * P ^ 2 - 2 * ((Q / P) * P) * P - (Q / P) ^ 2 * P ^ 2) / 12 := by ring
    _ = (2 * P ^ 2 - 2 * Q * P - Q ^ 2) / 12 := by rw [h1, h2]

/-- **(4.5), branch 1** (uniform): `(C2(p)+qd)/3 ≥ qd/2 + (C_α+μ)p² − p/2`. -/
theorem branch1_bound (hP : 0 < P) (hQ : 0 < Q) (hQ2 : Q ≤ 2 * P)
    (hD0 : 0 ≤ D) (hDP : D ≤ P) :
    Q * D / 2 + (Cα (Q / P) + mu (Q / P)) * P ^ 2 - P / 2
      ≤ (C2 P + Q * D) / 3 := by
  rw [add_mul, Ca_mul_sq hP, C2]
  rcases le_total (3 * Q) (2 * P) with h | h
  · rw [mu_mul_sq_low hP h]
    nlinarith [mul_nonneg hQ.le (sub_nonneg.mpr hDP)]
  · rw [mu_mul_sq_high hP h]
    nlinarith [mul_nonneg hQ.le (sub_nonneg.mpr hDP),
      mul_nonneg (by linarith : (0:ℚ) ≤ 3 * Q - 2 * P) (by linarith : (0:ℚ) ≤ Q + 2 * P)]

/-- **(4.5), branch 2** (separated): `C2(d)+C2(p−d) ≥ qd/2 + (C_α+μ)p² − p/2`. -/
theorem branch2_bound (hP : 0 < P) (hQ : 0 < Q) (hQ2 : Q ≤ 2 * P)
    (hD0 : 0 ≤ D) (hDP : D ≤ P) :
    Q * D / 2 + (Cα (Q / P) + mu (Q / P)) * P ^ 2 - P / 2
      ≤ C2 D + C2 (P - D) := by
  rw [add_mul, Ca_mul_sq hP, C2, C2]
  rcases le_total (3 * Q) (2 * P) with h | h
  · rw [mu_mul_sq_low hP h]
    nlinarith [sq_nonneg (4 * D - 2 * P - Q),
      mul_nonneg (by linarith : (0:ℚ) ≤ 2 * P - 3 * Q) (by linarith : (0:ℚ) ≤ 2 * P + Q)]
  · rw [mu_mul_sq_high hP h]
    nlinarith [sq_nonneg (4 * D - 2 * P - Q)]

/-- **(4.5), branch 3** (hot-neighborhood): dominated residual, Appendix A. -/
theorem branch3_bound (hP : 0 < P) (hQ : 0 < Q) (hQ2 : Q ≤ 2 * P)
    (hD0 : 0 ≤ D) (hDP : D ≤ P) :
    Q * D / 2 + (Cα (Q / P) + mu (Q / P)) * P ^ 2 - P / 2
      ≤ C2 D + (D * (P - D) + C2 (P - D)) / 3 := by
  rw [add_mul, Ca_mul_sq hP, C2, C2]
  rcases le_total (3 * Q) (2 * P) with h | h
  · -- α ≤ 2/3: residual `α(8−5α)/48 ≥ α²/12 ⟺ α ≤ 8/9`, holds with room
    rw [mu_mul_sq_low hP h]
    nlinarith [sq_nonneg (4 * D - 3 * Q), sub_nonneg.mpr hDP,
      mul_nonneg (by linarith : (0:ℚ) ≤ 2 * P - 3 * Q) hQ.le]
  · rw [mu_mul_sq_high hP h]
    rcases le_total (3 * Q) (4 * P) with h4 | h4
    · -- 2/3 ≤ α ≤ 4/3: residual `α(8−5α)/48 ≥ (2−α)²/48`
      nlinarith [sq_nonneg (4 * D - 3 * Q), sub_nonneg.mpr hDP,
        mul_nonneg (by linarith : (0:ℚ) ≤ 3 * Q - 2 * P)
          (by linarith : (0:ℚ) ≤ 4 * P - 3 * Q)]
    · -- α ≥ 4/3: vertex at `d = p`, residual `(2−α)²/12 ≥ (2−α)²/48`
      nlinarith [sq_nonneg (2 * P - Q), sub_nonneg.mpr hDP,
        mul_nonneg (sub_nonneg.mpr hDP) (by linarith : (0:ℚ) ≤ 3 * Q - 4 * P),
        sq_nonneg (P - D)]

/-- **(4.5)**: `F(p,q,d) ≥ qd/2 + (C_α + μ(α))p² − p/2` (as rationals, `F` in its
three-branch form). -/
theorem F_branch_bound (hP : 0 < P) (hQ : 0 < Q) (hQ2 : Q ≤ 2 * P)
    (hD0 : 0 ≤ D) (hDP : D ≤ P) :
    Q * D / 2 + (Cα (Q / P) + mu (Q / P)) * P ^ 2 - P / 2
      ≤ min ((C2 P + Q * D) / 3)
          (min (C2 D + C2 (P - D)) (C2 D + (D * (P - D) + C2 (P - D)) / 3)) :=
  le_min (branch1_bound hP hQ hQ2 hD0 hDP)
    (le_min (branch2_bound hP hQ hQ2 hD0 hDP) (branch3_bound hP hQ hQ2 hD0 hDP))

end PaperIII
