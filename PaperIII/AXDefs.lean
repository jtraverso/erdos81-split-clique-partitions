/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PaperIII.Duality

/-!
# Paper III — AX-shaped interfaces without axioms

This module contains only the statement shapes used by the clean assembly. The legacy
Layer-X axioms live in `PaperIII.AX`; the root `PaperIII` target should import this file
instead when it only needs explicit assumptions.
-/

@[expose] public section

namespace PaperIII

/-- A triangle decomposition: a family of triangles whose edge sets partition `E(H)`. -/
def HasTriangleDecomposition {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] : Prop :=
  ∃ T : Finset (Finset V), (∀ t ∈ T, H.IsNClique 3 t) ∧
    ∀ e ∈ H.edgeFinset, ∃! t, t ∈ T ∧ ∀ v ∈ e, v ∈ t

/-- Paper III's AX1 statement shape, used as an explicit assumption in the clean assembly. -/
abbrev AX1Assumption : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
    ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (H : SimpleGraph V) (_ : DecidableRel H.Adj),
      n₀ ≤ Fintype.card V →
      tau3Star H - (nu3 H : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2

/-- Paper III's AX2 statement shape, used as an explicit assumption in the clean assembly. -/
abbrev AX2Assumption : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
    ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (H : SimpleGraph V) (_ : DecidableRel H.Adj),
      H.edgeFinset.card % 3 = 0 →
      (∀ v : V, Even (H.degree v)) →
      n₀ ≤ Fintype.card V →
      ((0.9 + ε) * (Fintype.card V : ℝ) ≤ (H.minDegree : ℝ)) →
      HasTriangleDecomposition H

end PaperIII
