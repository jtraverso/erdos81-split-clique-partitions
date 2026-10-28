/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PaperIII.Main
public import PaperIII.YusterBridgeReuse
public import LeanPool.AsymptoticTrianglePacking.Main
public import RequestProject.NW18.PaperIIAssembly

/-!
# Paper III — unconditional assembly from registered formalizations

`Theorem_1_1` / `Corollary_1_2` for split graphs, `Φ(G) ≤ n²/6 + C·n`, with the two interfaces
`AX1Assumption` and `AX2Assumption` discharged from two registered Palomar entries:

* **AX1** (fractional–integral triangle-packing gap `τ₃* − ν₃ ≤ ε n²`) from
  `LeanPool.AsymptoticTrianglePacking.triangleCoverPackingGap`
  (jtraverso/asymptotic-triangle-packing, PALOMAR-2026-10-15-000011), through the bridge
  `Nibble.YusterE.nu3_eq_trianglePacking_sSup`;
* **AX2** (exact triangle decompositions of dense triangle-divisible graphs) from the
  Nash–Williams theorem with minimum degree `3n/4`,
  `NashWilliams18.PaperI.nash_williams_via_paperII`
  (jtraverso/nash-williams-lean, PALOMAR-2026-10-21-000009); AX2 only asks for `(0.9 + ε) n`.
-/

@[expose] public section

namespace PaperIII

open SimpleGraph

/-- **AX1, unconditionally**, from the registered asymptotic triangle-packing gap. -/
theorem AX1_holds : AX1Assumption := by
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := LeanPool.AsymptoticTrianglePacking.triangleCoverPackingGap ε hε
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hV
  have h := hn₀ V G hV
  have hnu : Nibble.YusterE.nu3 G = nu3 G := by
    rw [nu3]
    exact Nibble.YusterE.nu3_eq_trianglePacking_sSup G
  have htau : Nibble.AX1.tau3Star G = tau3Star G := rfl
  rw [hnu, htau] at h
  linarith

/-- **AX2, unconditionally**, from the registered Nash–Williams theorem (`3 n ≤ 4 δ(G)`). -/
theorem AX2_holds : AX2Assumption := by
  intro ε hε
  obtain ⟨N, hN⟩ := NashWilliams18.PaperI.nash_williams_via_paperII
  refine ⟨N, ?_⟩
  intro V _ _ H _ hcard hdeg hn hδ
  have hdiv : NashWilliams.IsTriangleDivisible H := ⟨Nat.dvd_of_mod_eq_zero hcard, hdeg⟩
  have h34 : 3 * Fintype.card V ≤ 4 * H.minDegree := by
    have hV0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
    have : (3 : ℝ) * Fintype.card V ≤ 4 * H.minDegree := by nlinarith
    exact_mod_cast this
  obtain ⟨D, hDtri, hDuniq⟩ := hN V H hn hdiv h34
  refine ⟨D, hDtri, ?_⟩
  intro e he
  induction e using Sym2.ind with
  | _ a b =>
    have hab : H.Adj a b := by simpa using he
    obtain ⟨t, ⟨htD, hat, hbt⟩, huniq⟩ := hDuniq a b hab
    refine ⟨t, ⟨htD, ?_⟩, ?_⟩
    · intro v hv
      rcases Sym2.mem_iff.1 hv with rfl | rfl
      · exact hat
      · exact hbt
    · rintro t' ⟨ht'D, ht'⟩
      exact huniq t' ⟨ht'D, ht' a (Sym2.mem_mk_left _ _), ht' b (Sym2.mem_mk_right _ _)⟩

/-- **Theorem 1.1 (Paper III), unconditional.** There is an absolute constant `C` with
`Φ(G) ≤ n²/6 + C·n` for every split graph `G`. -/
theorem Theorem_1_1 :
    ∃ C : ℝ, ∀ G : SplitGraph, ((G.Phi : ℤ) : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) :=
  Theorem_1_1_of_AX1_AX2 AX1_holds AX2_holds

/-- **Corollary 1.2 (Paper III), unconditional.** The same bound for the clique-partition number,
`cp(G) ≤ n²/6 + C·n`. -/
theorem Corollary_1_2 :
    ∃ C : ℝ, ∀ G : SplitGraph, (G.cp : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) :=
  Corollary_1_2_of_AX1_AX2 AX1_holds AX2_holds

end PaperIII
