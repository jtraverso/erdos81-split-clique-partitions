/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PaperIII.E_3_1_upper

/-!
# Paper III — E-3.1, cover values and the upper bound `τ₃* ≤ F`

Values of the three covers of `E_3_1_upper`:
uniform `(C(p,2)+qd)/3`, separated `C(d,2)+C(r,2)`, hot `C(d,2)+(C(p,2)−C(d,2))/3`;
assembled into `τ₃*(H(p,q,d)) ≤ F(p,q,d)`.
-/

@[expose] public section

namespace PaperIII

open SplitGraph Finset

namespace CommonProfile

variable {p q d : ℕ}

/-- A `Sym2` forall over an explicit pair. -/
theorem forall_mem_pair {α : Type*} {P : α → Prop} {x y : α} :
    (∀ v ∈ s(x, y), P v) ↔ P x ∧ P y := by
  constructor
  · intro h
    exact ⟨h x (Sym2.mem_mk_left x y), h y (Sym2.mem_mk_right x y)⟩
  · rintro ⟨hx, hy⟩ v hv
    rcases Sym2.mem_iff.mp hv with rfl | rfl <;> assumption

/-- `|{a : Fin p | a < d}| = d` when `d ≤ p`. -/
theorem card_filter_lt (hd : d ≤ p) :
    ((Finset.univ : Finset (Fin p)).filter fun a : Fin p => (a : ℕ) < d).card = d :=
  card_N (q := 1) hd 0

/-- `|E(H(p,q,d))| = C(p,2) + q·d`. -/
theorem edgeCount_commonProfile (hd : d ≤ p) :
    (commonProfile p q d).edgeCount = p.choose 2 + q * d := by
  rw [edgeCount_eq]
  congr 1
  calc ∑ i, (commonProfile p q d).d i = ∑ _i : Fin q, d := by
        exact Finset.sum_congr rfl fun i _ => card_N hd i
    _ = q * d := by
        rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin]

/-- Value of the uniform cover. -/
theorem sum_yUnif (hd : d ≤ p) :
    ∑ e ∈ (commonProfile p q d).graph.edgeFinset,
      yUnif (p := p) (q := q) (d := d) e
    = ((p.choose 2 : ℝ) + q * d) / 3 := by
  simp only [yUnif]
  rw [Finset.sum_const, nsmul_eq_mul]
  have h : (commonProfile p q d).graph.edgeFinset.card
      = (commonProfile p q d).edgeCount := rfl
  rw [h, edgeCount_commonProfile hd]
  push_cast
  ring

/-- Value of the separated cover: `C(d,2) + C(p−d,2)`. -/
theorem sum_ySep (hd : d ≤ p) :
    ∑ e ∈ (commonProfile p q d).graph.edgeFinset, ySep (p := p) (q := q) d e
    = (d.choose 2 : ℝ) + ((p - d).choose 2 : ℝ) := by
  rw [ SplitGraph.sum_edgeFinset ];
  unfold ySep;
  convert congr_arg₂ ( · + · ) ( card_top_edges_within ( Finset.filter ( fun a : Fin p => ( a : ℕ ) < d ) Finset.univ ) ) ( card_top_edges_within ( Finset.filter ( fun a : Fin p => ( a : ℕ ) ≥ d ) Finset.univ ) ) using 1;
  norm_num [ isN, isK ];
  rw [ ← Finset.card_union_of_disjoint ];
  · rw [ show ( Finset.filter ( fun a : Fin p => ( a : ℕ ) < d ) Finset.univ ).card = d from ?_, show ( Finset.filter ( fun a : Fin p => d ≤ ( a : ℕ ) ) Finset.univ ).card = p - d from ?_ ];
    · rw [ ← Finset.filter_or ] ; norm_cast;
    · rw [ Finset.card_eq_of_bijective ];
      use fun i hi => ⟨ i + d, by linarith [ Nat.sub_add_cancel hd ] ⟩;
      · exact fun a ha => ⟨ a - d, by rw [ tsub_lt_tsub_iff_right ( by aesop ) ] ; exact a.2, by erw [ Fin.ext_iff ] ; simp +decide [ Nat.sub_add_cancel ( show d ≤ a from by aesop ) ] ⟩;
      · grind;
      · aesop;
    · convert card_filter_lt hd using 1;
  · simp +contextual [ Finset.disjoint_left ];
    exact fun a ha₁ ha₂ => by rcases a with ⟨ x, y ⟩ ; aesop;

/-- Value of the hot-neighborhood cover: `C(d,2) + (C(p,2) − C(d,2))/3`. -/
theorem sum_yHot (hd : d ≤ p) :
    ∑ e ∈ (commonProfile p q d).graph.edgeFinset, yHot (p := p) (q := q) d e
    = (d.choose 2 : ℝ) + ((p.choose 2 : ℝ) - (d.choose 2 : ℝ)) / 3 := by
  rw [ SplitGraph.sum_edgeFinset ];
  unfold yHot;
  simp +decide [ isN, isK, Finset.sum_ite ];
  congr 2;
  · convert card_top_edges_within ( Finset.univ.filter fun a : Fin p => ( a : ℕ ) < d ) using 1;
    · aesop;
    · convert rfl;
      convert card_filter_lt hd using 1;
  · -- The cardinality of the set of pairs in the complete graph on p vertices that are not in the diagonal is equal to the number of ways to choose 2 elements from p, which is p choose 2.
    have h_card : Finset.card (Finset.filter (fun x : Sym2 (Fin p) => ¬x.IsDiag) (Finset.univ : Finset (Sym2 (Fin p)))) = p.choose 2 := by
      convert card_top_edges_within ( Finset.univ : Finset ( Fin p ) ) using 1;
      · refine' Finset.card_bij ( fun x hx => x ) _ _ _ <;> simp +decide;
      · norm_num;
    have h_card_filter : Finset.card (Finset.filter (fun x : Sym2 (Fin p) => ¬x.IsDiag ∧ ∀ a ∈ x, (a : ℕ) < d) (Finset.univ : Finset (Sym2 (Fin p)))) = d.choose 2 := by
      convert card_top_edges_within ( Finset.univ.filter fun a : Fin p => ( a : ℕ ) < d ) using 1;
      · refine' Finset.card_bij ( fun x hx => x.map ( fun a => a ) ) _ _ _ <;> simp +decide [ Finset.mem_filter, Finset.mem_univ ];
      · convert rfl;
        convert card_filter_lt hd;
    rw [ ← h_card, ← h_card_filter, eq_sub_iff_add_eq ];
    rw_mod_cast [ ← Finset.card_union_of_disjoint ];
    · congr with x ; by_cases hx : ∃ a ∈ x, d ≤ ( a : ℕ ) <;> aesop;
    · simp +contextual [ Finset.disjoint_left ];
      all_goals exact fun x hx y hy hy' => ⟨ y, hy, hy' ⟩

/-! ### Assembly: `τ₃*(H(p,q,d)) ≤ F(p,q,d)` -/

/-- **E-3.1, upper bound.** -/
theorem tau3Star_le_F (hd : d ≤ p) :
    tau3Star (commonProfile p q d).graph ≤ ((F p q d : ℚ) : ℝ) := by
  have h1 : tau3Star (commonProfile p q d).graph
      ≤ ((p.choose 2 : ℝ) + q * d) / 3 := by
    rw [← sum_yUnif (q := q) hd]
    exact tau3Star_le_of_cover _ yUnif_isFracCover
  have h2 : tau3Star (commonProfile p q d).graph
      ≤ (d.choose 2 : ℝ) + ((p - d).choose 2 : ℝ) := by
    rw [← sum_ySep (q := q) hd]
    exact tau3Star_le_of_cover _ ySep_isFracCover
  have h3 : tau3Star (commonProfile p q d).graph
      ≤ (d.choose 2 : ℝ) + ((p.choose 2 : ℝ) - (d.choose 2 : ℝ)) / 3 := by
    rw [← sum_yHot (q := q) hd]
    exact tau3Star_le_of_cover _ yHot_isFracCover
  -- identify the three cover values with the three branches of `F`
  have c1 : (((C2 p + q * d) / 3 : ℚ) : ℝ) = ((p.choose 2 : ℝ) + q * d) / 3 := by
    rw [C2]
    push_cast [Nat.cast_choose_two]
    ring
  have c2 : ((C2 d + C2 ((p : ℚ) - d) : ℚ) : ℝ)
      = (d.choose 2 : ℝ) + ((p - d).choose 2 : ℝ) := by
    rw [C2, C2]
    push_cast [Nat.cast_choose_two, Nat.cast_sub hd]
    ring
  have c3 : ((C2 d + ((d : ℚ) * ((p : ℚ) - d) + C2 ((p : ℚ) - d)) / 3 : ℚ) : ℝ)
      = (d.choose 2 : ℝ) + ((p.choose 2 : ℝ) - (d.choose 2 : ℝ)) / 3 := by
    rw [C2, C2]
    push_cast [Nat.cast_choose_two, Nat.cast_sub hd]
    ring
  have hF : F p q d
      = min ((C2 p + q * d) / 3)
          (min (C2 d + C2 ((p : ℚ) - d))
            (C2 d + ((d : ℚ) * ((p : ℚ) - d) + C2 ((p : ℚ) - d)) / 3)) := rfl
  rw [hF, Rat.cast_min, Rat.cast_min, c1, c2, c3]
  exact le_min h1 (le_min h2 h3)

end CommonProfile

end PaperIII