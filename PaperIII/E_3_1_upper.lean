/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PaperIII.Counting
public import PaperIII.SplitEdges

/-!
# Paper III — E-3.1, upper bound (`τ₃* ≤ F`)

The three explicit covers of §3.3 (uniform, separated, hot-neighborhood), each verified
against every triangle via the KKK/KKI classification, give
`τ₃*(H(p,q,d)) ≤ F(p,q,d)`.
-/

@[expose] public section

namespace PaperIII

open SplitGraph Finset

/-- The common-profile split graph `H(p,q,d)` (§3): every independent vertex has the
same neighborhood, the first `d` clique vertices. -/
abbrev commonProfile (p q d : ℕ) : SplitGraph :=
  ⟨p, q, fun _ => Finset.univ.filter fun a => (a : ℕ) < d⟩

namespace CommonProfile

variable {p q d : ℕ}

theorem mem_N_iff {i : Fin q} {a : Fin p} :
    a ∈ (commonProfile p q d).N i ↔ (a : ℕ) < d := by
  show a ∈ Finset.univ.filter (fun a : Fin p => (a : ℕ) < d) ↔ _
  rw [Finset.mem_filter]
  simp

/-- `|N| = d` when `d ≤ p`. -/
theorem card_N (hd : d ≤ p) (i : Fin q) : (commonProfile p q d).d i = d := by
  show ((commonProfile p q d).N i).card = d
  have himg : (commonProfile p q d).N i
      = (Finset.univ : Finset (Fin d)).image (Fin.castLE hd) := by
    ext a
    simp only [mem_N_iff, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro h; exact ⟨⟨(a : ℕ), (Finset.mem_filter.1 h).2⟩, by ext; simp [Fin.castLE]⟩
    · rintro ⟨b, rfl⟩; simpa [Fin.castLE] using b.isLt
  rw [himg, Finset.card_image_of_injective _ (Fin.castLE_injective hd)]
  simp

/-- The `N`-membership indicator on the vertices of `H(p,q,d)`. -/
def isN (d : ℕ) : (commonProfile p q d).V → Bool
  | .inl a => decide ((a : ℕ) < d)
  | .inr _ => false

/-- The clique-membership indicator. -/
def isK : (commonProfile p q d).V → Bool
  | .inl _ => true
  | .inr _ => false

/-! ### The three covers -/

/-- Uniform cover: weight `1/3` everywhere. -/
noncomputable def yUnif : Sym2 (commonProfile p q d).V → ℝ := fun _ => 1 / 3

/-- Separated cover: weight `1` on edges inside `N` and inside `R`, else `0`. -/
noncomputable def ySep (d : ℕ) : Sym2 (commonProfile p q d).V → ℝ := fun e =>
  if (∀ v ∈ e, isN d v = true) ∨ (∀ v ∈ e, isK v = true ∧ isN d v = false)
    then 1 else 0

/-- Hot-neighborhood cover: weight `1` inside `N`, `1/3` on the remaining clique
edges, `0` on cross edges. -/
noncomputable def yHot (d : ℕ) : Sym2 (commonProfile p q d).V → ℝ := fun e =>
  if ∀ v ∈ e, isN d v = true then 1
  else if ∀ v ∈ e, isK v = true then 1 / 3 else 0

/-! ### Cover constraint checks -/

theorem yUnif_isFracCover :
    IsFracCover (commonProfile p q d).graph (yUnif (p := p) (q := q) (d := d)) := by
  refine ⟨fun _ => by norm_num [yUnif], fun t ht => ?_⟩
  simp only [yUnif]
  rw [Finset.sum_const, card_edgesIn_triangle _ ht]
  norm_num

/-- An edge between two vertices of a triangle set belongs to `edgesIn` of it. -/
theorem edge_mem_edgesIn {t : Finset (commonProfile p q d).V}
    {x y : (commonProfile p q d).V} (hadj : (commonProfile p q d).graph.Adj x y)
    (hx : x ∈ t) (hy : y ∈ t) :
    s(x, y) ∈ edgesIn (commonProfile p q d).graph t := by
  rw [edgesIn, Finset.mem_filter, SimpleGraph.mem_edgeFinset,
    SimpleGraph.mem_edgeSet]
  refine ⟨hadj, fun v hv => ?_⟩
  rcases Sym2.mem_iff.mp hv with rfl | rfl <;> assumption

theorem ySep_isFracCover :
    IsFracCover (commonProfile p q d).graph (ySep (p := p) (q := q) d) := by
  constructor
  · intro e; simp only [ySep]; split <;> norm_num
  · intro t ht
    have hnn : ∀ e ∈ edgesIn (commonProfile p q d).graph t, 0 ≤ ySep d e := by
      intro e _; simp only [ySep]; split <;> norm_num
    rcases triangle_cases _ ht with ⟨a, b, c, hab, hac, hbc, rfl⟩ |
      ⟨a, b, i, hab, haN, hbN, rfl⟩
    · -- KKK: two of a,b,c lie on the same side of the threshold d
      have main : ∀ x y : Fin p, x ≠ y →
          Sum.inl x ∈ ({Sum.inl a, Sum.inl b, Sum.inl c} :
            Finset (commonProfile p q d).V) →
          Sum.inl y ∈ ({Sum.inl a, Sum.inl b, Sum.inl c} :
            Finset (commonProfile p q d).V) →
          (((x : ℕ) < d ∧ (y : ℕ) < d) ∨ (¬ (x : ℕ) < d ∧ ¬ (y : ℕ) < d)) →
          (1 : ℝ) ≤ ∑ e ∈ edgesIn (commonProfile p q d).graph
            {Sum.inl a, Sum.inl b, Sum.inl c}, ySep d e := by
        intro x y hxy hxmem hymem hside
        have hedge := edge_mem_edgesIn
          (show (commonProfile p q d).graph.Adj (Sum.inl x) (Sum.inl y) from hxy) hxmem hymem
        have hval : ySep (p := p) (q := q) d s(Sum.inl x, Sum.inl y) = 1 := by
          simp only [ySep]
          rw [if_pos]
          rcases hside with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
          · left
            intro v hv
            rcases Sym2.mem_iff.mp hv with rfl | rfl <;> simp [isN, *]
          · right
            intro v hv
            rcases Sym2.mem_iff.mp hv with rfl | rfl <;> simp [isN, isK, *]
        calc (1 : ℝ) = ySep (p := p) (q := q) d s(Sum.inl x, Sum.inl y) := hval.symm
          _ ≤ _ := Finset.single_le_sum hnn hedge
      by_cases ha : (a : ℕ) < d <;> by_cases hb : (b : ℕ) < d <;>
        by_cases hc : (c : ℕ) < d
      · exact main a b hab (by first | exact Finset.mem_insert_self _ _ | exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _) | exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
          (by first | exact Finset.mem_insert_self _ _ | exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _) | exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))) (Or.inl ⟨ha, hb⟩)
      · exact main a b hab (by first | exact Finset.mem_insert_self _ _ | exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _) | exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
          (by first | exact Finset.mem_insert_self _ _ | exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _) | exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))) (Or.inl ⟨ha, hb⟩)
      · exact main a c hac (by first | exact Finset.mem_insert_self _ _ | exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _) | exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
          (by first | exact Finset.mem_insert_self _ _ | exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _) | exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))) (Or.inl ⟨ha, hc⟩)
      · exact main b c hbc (by first | exact Finset.mem_insert_self _ _ | exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _) | exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
          (by first | exact Finset.mem_insert_self _ _ | exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _) | exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))) (Or.inr ⟨hb, hc⟩)
      · exact main b c hbc (by first | exact Finset.mem_insert_self _ _ | exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _) | exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
          (by first | exact Finset.mem_insert_self _ _ | exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _) | exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))) (Or.inl ⟨hb, hc⟩)
      · exact main a c hac (by first | exact Finset.mem_insert_self _ _ | exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _) | exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
          (by first | exact Finset.mem_insert_self _ _ | exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _) | exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))) (Or.inr ⟨ha, hc⟩)
      · exact main a b hab (by first | exact Finset.mem_insert_self _ _ | exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _) | exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
          (by first | exact Finset.mem_insert_self _ _ | exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _) | exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))) (Or.inr ⟨ha, hb⟩)
      · exact main a b hab (by first | exact Finset.mem_insert_self _ _ | exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _) | exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
          (by first | exact Finset.mem_insert_self _ _ | exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _) | exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))) (Or.inr ⟨ha, hb⟩)
    · -- KKI: the edge {a,b} lies inside N
      rw [mem_N_iff] at haN hbN
      have hedge := edge_mem_edgesIn
        (show (commonProfile p q d).graph.Adj (Sum.inl a) (Sum.inl b) from hab)
        (show (Sum.inl a : (commonProfile p q d).V) ∈
          ({Sum.inl a, Sum.inl b, Sum.inr i} :
            Finset (commonProfile p q d).V) by simp)
        (show (Sum.inl b : (commonProfile p q d).V) ∈
          ({Sum.inl a, Sum.inl b, Sum.inr i} :
            Finset (commonProfile p q d).V) by simp)
      have hval : ySep (p := p) (q := q) d s(Sum.inl a, Sum.inl b) = 1 := by
        simp only [ySep]
        rw [if_pos]
        left
        intro v hv
        rcases Sym2.mem_iff.mp hv with rfl | rfl <;> simp [isN, *]
      calc (1 : ℝ) = ySep (p := p) (q := q) d s(Sum.inl a, Sum.inl b) := hval.symm
        _ ≤ _ := Finset.single_le_sum hnn hedge

theorem yHot_isFracCover :
    IsFracCover (commonProfile p q d).graph (yHot (p := p) (q := q) d) := by
  constructor
  · intro e; simp only [yHot]; split
    · norm_num
    · split <;> norm_num
  · intro t ht
    have hnn : ∀ e ∈ edgesIn (commonProfile p q d).graph t, 0 ≤ yHot d e := by
      intro e _; simp only [yHot]; split
      · norm_num
      · split <;> norm_num
    rcases triangle_cases _ ht with ⟨a, b, c, hab, hac, hbc, rfl⟩ |
      ⟨a, b, i, hab, haN, hbN, rfl⟩
    · -- KKK: all edges are clique edges of weight ≥ 1/3, and there are exactly 3
      have hcard := card_edgesIn_triangle _ ht
      have hbound : ∀ e ∈ edgesIn (commonProfile p q d).graph
          {Sum.inl a, Sum.inl b, Sum.inl c}, (1 : ℝ) / 3 ≤ yHot d e := by
        intro e he
        rw [edgesIn, Finset.mem_filter] at he
        have hK : ∀ v ∈ e, isK (p := p) (q := q) (d := d) v = true := by
          intro v hv
          have hvt := he.2 v hv
          simp only [Finset.mem_insert, Finset.mem_singleton] at hvt
          rcases hvt with rfl | rfl | rfl <;> simp [isK]
        simp only [yHot]
        by_cases h1 : ∀ v ∈ e, isN (p := p) (q := q) d v = true
        · rw [if_pos h1]; norm_num
        · rw [if_neg h1, if_pos hK]
      have hsum := Finset.card_nsmul_le_sum
        (edgesIn (commonProfile p q d).graph {Sum.inl a, Sum.inl b, Sum.inl c})
        (yHot d) ((1 : ℝ) / 3) hbound
      rw [hcard] at hsum
      calc (1 : ℝ) = (3 : ℕ) • ((1 : ℝ) / 3) := by norm_num
        _ ≤ _ := hsum
    · -- KKI: the edge {a,b} lies inside N and has weight 1
      rw [mem_N_iff] at haN hbN
      have hedge := edge_mem_edgesIn
        (show (commonProfile p q d).graph.Adj (Sum.inl a) (Sum.inl b) from hab)
        (show (Sum.inl a : (commonProfile p q d).V) ∈
          ({Sum.inl a, Sum.inl b, Sum.inr i} :
            Finset (commonProfile p q d).V) by simp)
        (show (Sum.inl b : (commonProfile p q d).V) ∈
          ({Sum.inl a, Sum.inl b, Sum.inr i} :
            Finset (commonProfile p q d).V) by simp)
      have hval : yHot (p := p) (q := q) d s(Sum.inl a, Sum.inl b) = 1 := by
        simp only [yHot]
        rw [if_pos]
        intro v hv
        rcases Sym2.mem_iff.mp hv with rfl | rfl <;> simp [isN, *]
      calc (1 : ℝ) = yHot (p := p) (q := q) d s(Sum.inl a, Sum.inl b) := hval.symm
        _ ≤ _ := Finset.single_le_sum hnn hedge

end CommonProfile

end PaperIII
