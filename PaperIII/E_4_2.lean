/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PaperIII.E_4_agg
public import PaperIII.E_4_2_algebra

/-!
# Paper III — E-4.2 (Unified fractional margin)

`ν₃*(G) ≥ T(G) + μ(α)p² − p/4` for `p ≥ 3`, `0 < q ≤ 2p` (`ν₃*` read as the LP cover
optimum `τ₃*`).  Assembly: E-4.1 (replication) + the per-branch completion of squares
(4.5) (`F_branch_bound`) + the key `T(G)` identity.
-/

@[expose] public section

namespace PaperIII

open SplitGraph Finset

/-- The `T(G)` identity in graph form (LEDGER E-4.2 "key identity"):
`T(G) = ½ Σᵢ dᵢ + C_α p² − p/4`. -/
theorem T_eq (G : SplitGraph) (hp : 1 ≤ G.p) :
    G.T = (∑ i, (G.d i : ℚ)) / 2 + Cα G.α * (G.p : ℚ) ^ 2 - (G.p : ℚ) / 4 := by
  have hP : (G.p : ℚ) ≠ 0 := by positivity
  have hE : (G.edgeCount : ℚ) = C2 (G.p : ℚ) + ∑ i, (G.d i : ℚ) := by
    rw [G.edgeCount_eq, C2]
    push_cast [Nat.cast_choose_two]
    ring
  have := T_key_identity (G.p : ℚ) (G.q : ℚ) (∑ i, (G.d i : ℚ)) hP
  rw [SplitGraph.T, hE, SplitGraph.α]
  linarith [this]

/-- **E-4.2 (Unified fractional margin)**: for `p ≥ 3` and `0 < q ≤ 2p`,
`ν₃*(G) ≥ T(G) + μ(α)·p² − p/4` (LEDGER E-4.2; `ν₃*` read as `τ₃*`). -/
theorem E_4_2 (G : SplitGraph) (hp : 3 ≤ G.p) (hq1 : 1 ≤ G.q) (hq2 : G.q ≤ 2 * G.p) :
    ((G.T + SplitGraph.mu G.α * (G.p : ℚ) ^ 2 - (G.p : ℚ) / 4 : ℚ) : ℝ)
      ≤ tau3Star G.graph := by
  have hP : (0 : ℚ) < (G.p : ℚ) := by exact_mod_cast (by omega : 0 < G.p)
  have hQ : (0 : ℚ) < (G.q : ℚ) := by exact_mod_cast hq1
  have hQ2 : (G.q : ℚ) ≤ 2 * (G.p : ℚ) := by exact_mod_cast hq2
  -- per-vertex branch bound, in ℚ
  have branch : ∀ i : Fin G.q,
      (G.q : ℚ) * (G.d i : ℚ) / 2
        + (Cα G.α + SplitGraph.mu G.α) * (G.p : ℚ) ^ 2 - (G.p : ℚ) / 2
      ≤ F G.p G.q (G.d i) := by
    intro i
    have hD0 : (0 : ℚ) ≤ (G.d i : ℚ) := by positivity
    have hDP : (G.d i : ℚ) ≤ (G.p : ℚ) := by
      exact_mod_cast Agg.d_le_p G i
    have h := F_branch_bound hP hQ hQ2 hD0 hDP
    have hF : F G.p G.q (G.d i)
        = min ((C2 G.p + G.q * G.d i) / 3)
            (min (C2 (G.d i) + C2 ((G.p : ℚ) - G.d i))
              (C2 (G.d i) + ((G.d i : ℚ) * ((G.p : ℚ) - G.d i)
                + C2 ((G.p : ℚ) - G.d i)) / 3)) := rfl
    rw [hF, SplitGraph.α]
    exact h
  -- sum the branch bound and rewrite via the T identity
  have hsum : G.T + SplitGraph.mu G.α * (G.p : ℚ) ^ 2 - (G.p : ℚ) / 4
      ≤ (1 / (G.q : ℚ)) * ∑ i, F G.p G.q (G.d i) := by
    have hs : ∑ i, ((G.q : ℚ) * (G.d i : ℚ) / 2
          + (Cα G.α + SplitGraph.mu G.α) * (G.p : ℚ) ^ 2 - (G.p : ℚ) / 2)
        ≤ ∑ i, F G.p G.q (G.d i) := Finset.sum_le_sum fun i _ => branch i
    have hexp : ∑ i, ((G.q : ℚ) * (G.d i : ℚ) / 2
          + (Cα G.α + SplitGraph.mu G.α) * (G.p : ℚ) ^ 2 - (G.p : ℚ) / 2)
        = (G.q : ℚ) * ((∑ i, (G.d i : ℚ)) / 2
          + (Cα G.α + SplitGraph.mu G.α) * (G.p : ℚ) ^ 2 - (G.p : ℚ) / 2) := by
      calc ∑ i, ((G.q : ℚ) * (G.d i : ℚ) / 2
            + (Cα G.α + SplitGraph.mu G.α) * (G.p : ℚ) ^ 2 - (G.p : ℚ) / 2)
          = ∑ i, ((G.q : ℚ) / 2 * (G.d i : ℚ)
            + ((Cα G.α + SplitGraph.mu G.α) * (G.p : ℚ) ^ 2 - (G.p : ℚ) / 2)) :=
            Finset.sum_congr rfl fun i _ => by ring
        _ = (G.q : ℚ) / 2 * (∑ i, (G.d i : ℚ))
            + (G.q : ℚ) * ((Cα G.α + SplitGraph.mu G.α) * (G.p : ℚ) ^ 2
              - (G.p : ℚ) / 2) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
              Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ = (G.q : ℚ) * ((∑ i, (G.d i : ℚ)) / 2
            + (Cα G.α + SplitGraph.mu G.α) * (G.p : ℚ) ^ 2 - (G.p : ℚ) / 2) := by
            ring
    rw [T_eq G (by omega), one_div, le_inv_mul_iff₀ hQ]
    have hswap : (G.q : ℚ) * ((∑ i, (G.d i : ℚ)) / 2 + Cα G.α * (G.p : ℚ) ^ 2
          - (G.p : ℚ) / 4 + SplitGraph.mu G.α * (G.p : ℚ) ^ 2 - (G.p : ℚ) / 4)
        = ∑ i, ((G.q : ℚ) * (G.d i : ℚ) / 2
          + (Cα G.α + SplitGraph.mu G.α) * (G.p : ℚ) ^ 2 - (G.p : ℚ) / 2) := by
      rw [hexp]
      ring
    rw [hswap]
    exact hs
  calc ((G.T + SplitGraph.mu G.α * (G.p : ℚ) ^ 2 - (G.p : ℚ) / 4 : ℚ) : ℝ)
      ≤ (((1 / (G.q : ℚ)) * ∑ i, F G.p G.q (G.d i) : ℚ) : ℝ) := by
        exact_mod_cast hsum
    _ = (1 / (G.q : ℝ)) * ∑ i, ((F G.p G.q (G.d i) : ℚ) : ℝ) := by
        push_cast
        ring
    _ ≤ tau3Star G.graph := E_4_1 G hp hq1

end PaperIII
