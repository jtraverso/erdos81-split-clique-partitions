/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PaperIII.Defs

/-!
# Paper III — Audited algebraic identities (LEDGER "Audit status" + M1)

The symbolic checks of `verify_ledger_algebra.py`, as Lean lemmas over `ℚ`:
* the `T(G)` key identity of E-4.2 (`T = ½Σd + C_α p² − p/4`);
* the (9.12) `s²` coefficient `−1/6 + 2/9 − 7/96 = −5/288`;
* the completed square (9.19) and its lower bound `s²/24`;
* the (9.20) coefficient `−1/24 + 5/192 = −1/64`;
* `δ ≥ 7/8` at `s ≤ p/8` in both parities of `p` (9.10);
* the corridor threshold `6√p = p/8 ⟺ p = 2304` (in squared form `36p = p²/64`);
* well-definedness of `μ` at the breakpoint `α = 2/3`.
-/

@[expose] public section

namespace PaperIII

open SplitGraph

/-- **Key identity of E-4.2** (audited `= 0`): with `E = C(p,2) + Σdᵢ` and `α = q/p`,
`T = (E − (p+q)²/6)/2 = ½ Σdᵢ + C_α p² − p/4`.  Stated as pure `ℚ` algebra. -/
theorem T_key_identity (P Q Sd : ℚ) (hP : P ≠ 0) :
    (C2 P + Sd - (P + Q) ^ 2 / 6) / 2 = Sd / 2 + Cα (Q / P) * P ^ 2 - P / 4 := by
  unfold C2 Cα
  field_simp
  ring

/-- **(9.12) `s²` coefficient** (audited): `−1/6 + 2/9 − 7/96 = −5/288`. -/
theorem coeff_9_12 : (-1 : ℚ) / 6 + 2 / 9 - 7 / 96 = -5 / 288 := by norm_num

/-- **(9.19)** (audited `= 0`): `s²/6 − sρ + 2ρ² = 2(ρ − s/4)² + s²/24`. -/
theorem identity_9_19 (S R : ℚ) :
    S ^ 2 / 6 - S * R + 2 * R ^ 2 = 2 * (R - S / 4) ^ 2 + S ^ 2 / 24 := by ring

/-- **(9.19), inequality form**: `s²/6 − sρ + 2ρ² ≥ s²/24`. -/
theorem ineq_9_19 (S R : ℚ) : S ^ 2 / 6 - S * R + 2 * R ^ 2 ≥ S ^ 2 / 24 := by
  rw [identity_9_19]; nlinarith [sq_nonneg (R - S / 4)]

/-- **(9.20) coefficient** (audited `= s²/64` loss): `−1/24 + 5/192 = −1/64`. -/
theorem coeff_9_20 : (-1 : ℚ) / 24 + 5 / 192 = -1 / 64 := by norm_num

/-- **(9.10), `p` odd** (audited): if `0 < p` and `s ≤ p/8` then `δ = (p−s)/p ≥ 7/8`. -/
theorem delta_ge_odd (P S : ℚ) (hP : 0 < P) (hS : S ≤ P / 8) :
    (P - S) / P ≥ 7 / 8 := by
  rw [ge_iff_le, div_le_div_iff₀ (by norm_num) hP]
  linarith

/-- **(9.10), `p` even** (audited): if `2 ≤ p` and `s ≤ p/8` then
`δ = (p+1−s)/(p−1) ≥ 7/8`. -/
theorem delta_ge_even (P S : ℚ) (hP : 2 ≤ P) (hS : S ≤ P / 8) :
    (P + 1 - S) / (P - 1) ≥ 7 / 8 := by
  rw [ge_iff_le, div_le_div_iff₀ (by norm_num) (by linarith)]
  linarith

/-- **Corridor threshold** (audited): for `p > 0`, `36p = p²/64 ⟺ p = 2304`
(the squared form of `6√p = p/8`). -/
theorem corridor_threshold (P : ℚ) (hP : 0 < P) :
    36 * P = P ^ 2 / 64 ↔ P = 2304 := by
  constructor
  · intro h
    have h64 : P ^ 2 = 2304 * P := by linarith
    have := mul_right_cancel₀ (ne_of_gt hP) (by nlinarith : P * P = 2304 * P)
    linarith
  · rintro rfl; norm_num

/-- `μ` is well defined at the breakpoint: `(2/3)²/12 = (2 − 2/3)²/48`. -/
theorem mu_breakpoint : ((2 : ℚ) / 3) ^ 2 / 12 = (2 - 2 / 3) ^ 2 / 48 := by norm_num

/-- `μ(α) ≥ 0` for all `α`. -/
theorem mu_nonneg (a : ℚ) : 0 ≤ SplitGraph.mu a := by
  unfold SplitGraph.mu
  split <;> positivity

end PaperIII
