/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Paper III — Core definitions (LEDGER.md §0 "Notation")

A split graph with a distinguished partition is exactly the data of the clique size `p`,
the independent-set size `q`, and for each independent vertex its clique-neighborhood
`N i ⊆ K`.  All profile quantities (`d i`, `S i`, `m i`, `M`, `S₂`, `s`, `α`) derive from
this.  `ν₃` is the maximum size of an edge-disjoint triangle family, `ν₃*` the fractional
LP optimum (a `csSup` over feasible fractional packings, valued in `ℝ`),
`Φ G = |E G| − 2 ν₃ G`, and `T G = (|E G| − (p+q)²/6)/2`.

`F p q d` is the explicit three-term minimum of E-3.1; `μ` the unified fractional margin
of E-4.2; `rp t = χ'(K_t)` the complete-graph edge-chromatic number as a formula.
-/

@[expose] public section

namespace PaperIII

/-- A split graph presented by its profile (LEDGER §0): clique `K` of size `p`,
independent set `I` of size `q`, and the clique-neighborhood `N i ⊆ K` of each
independent vertex. -/
structure SplitGraph where
  p : ℕ
  q : ℕ
  N : Fin q → Finset (Fin p)

namespace SplitGraph

variable (G : SplitGraph)

/-- Vertex type: clique vertices on the left, independent vertices on the right. -/
abbrev V : Type := Fin G.p ⊕ Fin G.q

/-- Adjacency: `K` is a clique, `I` is independent, and `inl a ~ inr i ↔ a ∈ N i`. -/
def Adj : G.V → G.V → Prop
  | .inl a, .inl b => a ≠ b
  | .inl a, .inr i => a ∈ G.N i
  | .inr i, .inl a => a ∈ G.N i
  | .inr _, .inr _ => False

instance : DecidableRel G.Adj := fun x y =>
  match x, y with
  | .inl a, .inl b => inferInstanceAs (Decidable (a ≠ b))
  | .inl a, .inr i => inferInstanceAs (Decidable (a ∈ G.N i))
  | .inr i, .inl a => inferInstanceAs (Decidable (a ∈ G.N i))
  | .inr _, .inr _ => inferInstanceAs (Decidable False)

/-- The underlying simple graph of the split graph. -/
def graph : SimpleGraph G.V where
  Adj := G.Adj
  symm := ⟨by rintro (a | i) (b | j) h <;> simp only [Adj] at h ⊢ <;>
    first | exact h.symm | exact h⟩
  loopless := by
    refine ⟨?_⟩
    rintro (a | i) h
    · exact h rfl
    · exact h

instance : DecidableRel G.graph.Adj := fun x y => inferInstanceAs (Decidable (G.Adj x y))

/-! ## Profile quantities (LEDGER §0) -/

/-- `n = p + q`, the number of vertices. -/
def n : ℕ := G.p + G.q

/-- `d i = |N i|`, the clique-degree of independent vertex `i`. -/
def d (i : Fin G.q) : ℕ := (G.N i).card

/-- `S i = K ∖ N i`, the missing set of independent vertex `i`. -/
def S (i : Fin G.q) : Finset (Fin G.p) := (G.N i)ᶜ

/-- `m i = |S i| = p − d i`. -/
def m (i : Fin G.q) : ℕ := (G.S i).card

/-- `M = Σᵢ m i`. -/
def M : ℕ := ∑ i, G.m i

/-- `S₂ = Σᵢ (m i)²`. -/
def S₂ : ℕ := ∑ i, (G.m i) ^ 2

/-- Near `q = 2p`: `s = 2p − q` (an integer; the corridor regime has `s ≥ 0`). -/
def s : ℤ := 2 * (G.p : ℤ) - (G.q : ℤ)

/-- `α = q/p`. -/
def α : ℚ := (G.q : ℚ) / (G.p : ℚ)

/-- Number of edges of the split graph. -/
def edgeCount : ℕ := G.graph.edgeFinset.card

end SplitGraph

/-! ## Triangle packings: `ν₃` and `ν₃*` (generic, for any finite simple graph) -/

section Packing

variable {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]

/-- A triangle packing: a family of triangles of `H`, pairwise edge-disjoint.
For 3-cliques, edge-disjointness is equivalent to sharing at most one vertex. -/
def IsTrianglePacking (T : Finset (Finset W)) : Prop :=
  (∀ t ∈ T, H.IsNClique 3 t) ∧
    (T : Set (Finset W)).Pairwise fun t₁ t₂ => (t₁ ∩ t₂).card ≤ 1

/-- `ν₃ H` = maximum number of pairwise edge-disjoint triangles in `H`. -/
noncomputable def nu3 : ℕ :=
  sSup {k | ∃ T : Finset (Finset W), IsTrianglePacking H T ∧ T.card = k}

/-- A fractional triangle packing: nonnegative weights supported on triangles with total
weight at most 1 across each edge. -/
def IsFracPacking (w : Finset W → ℝ) : Prop :=
  (∀ t, 0 ≤ w t) ∧ (∀ t, w t ≠ 0 → H.IsNClique 3 t) ∧
    ∀ e ∈ H.edgeFinset,
      (∑ t ∈ (H.cliqueFinset 3).filter (fun t => ∀ v ∈ e, v ∈ t), w t) ≤ 1

/-- `ν₃* H` = the fractional triangle-packing optimum (LP value), as a real `csSup`. -/
noncomputable def nu3Star : ℝ :=
  sSup {x | ∃ w : Finset W → ℝ, IsFracPacking H w ∧ x = ∑ t ∈ H.cliqueFinset 3, w t}

end Packing

namespace SplitGraph

variable (G : SplitGraph)

/-- `ν₃ G` for a split graph. -/
noncomputable def nu3' : ℕ := nu3 G.graph

/-- `ν₃* G` for a split graph. -/
noncomputable def nu3Star' : ℝ := nu3Star G.graph

/-- `Φ(G) = |E(G)| − 2 ν₃(G)` (an integer; nonnegative since `2ν₃ ≤ (2/3)|E|`). -/
noncomputable def Phi : ℤ := (G.edgeCount : ℤ) - 2 * (G.nu3' : ℤ)

/-- `T(G) = ½ (|E(G)| − (p+q)²/6)`. -/
def T : ℚ := ((G.edgeCount : ℚ) - ((G.p : ℚ) + (G.q : ℚ)) ^ 2 / 6) / 2

/-! ## The explicit functions of the ledger -/

/-- `C2 x = x(x−1)/2`, the rational "choose 2" (agrees with `Nat.choose x 2` on casts). -/
def C2 (x : ℚ) : ℚ := x * (x - 1) / 2

/-- `F p q d` (E-3.1): the common-profile fractional optimum, with `r = p − d`:
`min{ (C(p,2)+q·d)/3 , C(d,2)+C(r,2) , C(d,2)+(d·r+C(r,2))/3 }`. -/
def F (p q d : ℕ) : ℚ :=
  let P : ℚ := p; let Q : ℚ := q; let D : ℚ := d; let R : ℚ := P - D
  min ((C2 P + Q * D) / 3) (min (C2 D + C2 R) (C2 D + (D * R + C2 R) / 3))

/-- `μ(α)` (E-4.2): the unified fractional margin,
`α²/12` on `[0, 2/3]` and `(2−α)²/48` on `[2/3, 2]` (they agree at `α = 2/3`). -/
def mu (a : ℚ) : ℚ := if a ≤ 2 / 3 then a ^ 2 / 12 else (2 - a) ^ 2 / 48

/-- `r_p = χ'(K_p)`: `p−1` for `p` even, `p` for `p` odd, and `0` for `p ≤ 1`. -/
def rp (t : ℕ) : ℕ := if t ≤ 1 then 0 else if Even t then t - 1 else t

/-- `C_α = (2 − 2α − α²)/12`, the constant of the key identity of E-4.2. -/
def Cα (a : ℚ) : ℚ := (2 - 2 * a - a ^ 2) / 12

end SplitGraph

end PaperIII
