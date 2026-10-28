/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PaperIII.E_4_2
public import PaperIII.AXDefs

/-!
# Paper III — E-4.3 (Bulk consequence)

If `ε ≤ α ≤ 2 − ε` then `μ(α) ≥ ε²/48 > 0`; with **AX1**, `ν₃(G) ≥ T(G)` for `n`
large, i.e. `Φ(G) ≤ n²/6` (LEDGER E-4.3).  Uses AX1 only.
-/

@[expose] public section

namespace PaperIII

open SplitGraph

/-- `μ(α) ≥ ε²/48` on the bulk `ε ≤ α ≤ 2 − ε`. -/
theorem mu_ge_bulk {ε a : ℚ} (hε : 0 < ε) (h1 : ε ≤ a) (h2 : a ≤ 2 - ε) :
    ε ^ 2 / 48 ≤ SplitGraph.mu a := by
  rw [SplitGraph.mu]
  split
  · nlinarith
  · nlinarith

/-- `|V(G)| = n`. -/
theorem card_V (G : SplitGraph) : Fintype.card G.V = G.n := by
  simp [SplitGraph.n]

/-- **E-4.3 (Bulk consequence), parametrized by AX1**: for every `ε > 0` there is `n₀` such that every
split graph with `n ≥ n₀` and `ε ≤ α ≤ 2 − ε` satisfies `Φ(G) ≤ n²/6`
(LEDGER E-4.3; uses AX1). -/
theorem E_4_3_of_AX1
    (hAX1 : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
        (G : SimpleGraph V) (_ : DecidableRel G.Adj),
        n₀ ≤ Fintype.card V →
        tau3Star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2)
    (ε : ℚ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ G : SplitGraph, n₀ ≤ G.n →
      ε ≤ G.α → G.α ≤ 2 - ε → ((G.Phi : ℤ) : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 := by
  classical
  -- the margin constant and the AX1 threshold
  set c : ℝ := ((ε ^ 2 / 48 : ℚ) : ℝ) with hc
  have hc0 : 0 < c := by
    rw [hc]; exact_mod_cast by positivity
  obtain ⟨n₁, hn₁⟩ := hAX1 (c / 18) (by positivity)
  refine ⟨max n₁ (max 9 (Nat.ceil ((9 : ℝ) / (2 * c)))), fun G hn hα1 hα2 => ?_⟩
  have hn1 : n₁ ≤ G.n := le_trans (le_max_left _ _) hn
  have hn9 : 9 ≤ G.n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnc : (9 : ℝ) / (2 * c) ≤ (G.n : ℝ) := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast this)
  -- basic regime facts
  have hq1 : 1 ≤ G.q := by
    by_contra h
    have hq0 : G.q = 0 := by omega
    have : G.α = 0 := by simp [SplitGraph.α, hq0]
    rw [this] at hα1; linarith
  have hp1 : 1 ≤ G.p := by
    by_contra h
    have hp0 : G.p = 0 := by omega
    have : G.α = 0 := by simp [SplitGraph.α, hp0]
    rw [this] at hα1; linarith
  have hP : (0 : ℚ) < (G.p : ℚ) := by exact_mod_cast hp1
  have hq2 : G.q ≤ 2 * G.p := by
    have h2 : G.α ≤ 2 := by linarith
    rw [SplitGraph.α, div_le_iff₀ hP] at h2
    exact_mod_cast by exact_mod_cast h2
  have hp3n : G.n ≤ 3 * G.p := by
    rw [SplitGraph.n]; omega
  have hp3 : 3 ≤ G.p := by omega
  -- AX1 at G
  have hAX := hn₁ G.V inferInstance inferInstance G.graph inferInstance
    (by rw [card_V]; exact hn1)
  rw [card_V] at hAX
  -- E-4.2
  have hE42 := E_4_2 G hp3 hq1 hq2
  -- the margin: μ(α) ≥ c
  have hμ : c ≤ ((SplitGraph.mu G.α : ℚ) : ℝ) := by
    rw [hc]; exact_mod_cast mu_ge_bulk hε hα1 hα2
  -- 2T = |E| − n²/6
  have hT : ((G.T : ℚ) : ℝ) * 2
      = (G.edgeCount : ℝ) - ((G.n : ℝ)) ^ 2 / 6 := by
    have : (G.T : ℚ) * 2 = (G.edgeCount : ℚ) - ((G.p : ℚ) + (G.q : ℚ)) ^ 2 / 6 := by
      rw [SplitGraph.T]; ring
    have hn' : ((G.n : ℝ)) = (G.p : ℝ) + (G.q : ℝ) := by
      rw [SplitGraph.n]; push_cast; ring
    rw [hn']
    have h2 := congrArg (Rat.cast (K := ℝ)) this
    push_cast at h2
    push_cast
    linarith [h2]
  -- p ≥ n/3 in ℝ
  have hpn : (G.n : ℝ) / 3 ≤ (G.p : ℝ) := by
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 3)]
    have : (G.n : ℝ) ≤ 3 * (G.p : ℝ) := by exact_mod_cast hp3n
    linarith
  -- assemble
  have hnu : ((nu3 G.graph : ℕ) : ℝ)
      ≥ ((G.T : ℚ) : ℝ) + ((SplitGraph.mu G.α : ℚ) : ℝ) * (G.p : ℝ) ^ 2
        - (G.p : ℝ) / 4 - (c / 18) * (G.n : ℝ) ^ 2 := by
    have h1 : ((G.T + SplitGraph.mu G.α * (G.p : ℚ) ^ 2 - (G.p : ℚ) / 4 : ℚ) : ℝ)
        = ((G.T : ℚ) : ℝ) + ((SplitGraph.mu G.α : ℚ) : ℝ) * (G.p : ℝ) ^ 2
          - (G.p : ℝ) / 4 := by push_cast; ring
    have h2 := le_trans (le_of_eq h1.symm) hE42
    linarith [hAX, h2]
  have hPhi : ((G.Phi : ℤ) : ℝ) = (G.edgeCount : ℝ) - 2 * ((nu3 G.graph : ℕ) : ℝ) := by
    rw [SplitGraph.Phi]
    push_cast
    rfl
  have hn0 : (0 : ℝ) < (G.n : ℝ) := by exact_mod_cast by omega
  have hnn : (G.n : ℝ) ≤ (G.p : ℝ) + (G.q : ℝ) := by
    rw [SplitGraph.n]; push_cast; linarith
  -- final arithmetic: Φ ≤ n²/6 − 2μp² + p/2 + (c/9)n² ≤ n²/6
  rw [hPhi]
  have hkey : 2 * c * ((G.n : ℝ) / 3) ^ 2 ≥ (c / 9) * (G.n : ℝ) ^ 2 := by
    ring_nf; nlinarith [sq_nonneg (G.n : ℝ)]
  have hμp : ((SplitGraph.mu G.α : ℚ) : ℝ) * (G.p : ℝ) ^ 2 ≥ c * ((G.n : ℝ) / 3) ^ 2 := by
    have hp0 : (0 : ℝ) ≤ (G.n : ℝ) / 3 := by positivity
    have hμ0 : (0 : ℝ) ≤ ((SplitGraph.mu G.α : ℚ) : ℝ) := le_trans hc0.le hμ
    have := mul_le_mul hμ (mul_self_le_mul_self hp0 hpn) (by positivity) hμ0
    calc c * ((G.n : ℝ) / 3) ^ 2 = c * (((G.n : ℝ) / 3) * ((G.n : ℝ) / 3)) := by ring
      _ ≤ ((SplitGraph.mu G.α : ℚ) : ℝ) * ((G.p : ℝ) * (G.p : ℝ)) := this
      _ = ((SplitGraph.mu G.α : ℚ) : ℝ) * (G.p : ℝ) ^ 2 := by ring
  have hpn2 : (G.p : ℝ) ≤ (G.n : ℝ) := by
    rw [SplitGraph.n]; push_cast; linarith [ (by exact_mod_cast hq1 : (1:ℝ) ≤ (G.q:ℝ)) ]
  have htail : (G.p : ℝ) / 2 ≤ (c / 9) * (G.n : ℝ) ^ 2 := by
    have h9 : 9 / (2 * c) * (2 * c) ≤ (G.n : ℝ) * (2 * c) :=
      mul_le_mul_of_nonneg_right hnc (by positivity)
    rw [div_mul_cancel₀ _ (by positivity : (2 : ℝ) * c ≠ 0)] at h9
    nlinarith [hn0, hpn2]
  linarith [hnu, hT, hμp, hkey, htail]

end PaperIII
