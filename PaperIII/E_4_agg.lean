/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PaperIII.Counting
public import PaperIII.SplitEdges
public import PaperIII.E_3_1_LP
public import PaperIII.E_3_1_values

/-!
# Paper III — Aggregated cover constraints (E-4.1 replication + E-3.1 lower bound)

For a fractional cover `y` of a split graph `G` and an independent vertex `i`, the four
class sums `A_i, B_i, C_i, E_i` (weights inside `N_i`, on the `v_i`-incidences, crossing
`N_i`/`R_i`, inside `R_i`) satisfy the five aggregated triangle constraints; feeding them
to `lp_dual_bound` yields the per-vertex bound
`A_i + q·B_i + C_i + E_i ≥ F(p,q,d_i)`.  Summed over `i` this is E-4.1
(`τ₃*(G) ≥ (1/q) Σᵢ F(p,q,dᵢ)`); applied to the common profile it is E-3.1's lower
bound.  This replaces the paper's cloning construction with an equivalent in-graph
aggregation (the relabelled triangles are the same `G`-triangles).
-/

@[expose] public section

namespace PaperIII

open SplitGraph Finset

namespace Agg

variable (G : SplitGraph) (y : Sym2 G.V → ℝ) (i : Fin G.q)

/-- `A_i`: total cover weight on clique edges inside `N_i`. -/
noncomputable def wA : ℝ :=
  ∑ e ∈ (⊤ : SimpleGraph (Fin G.p)).edgeFinset.filter
    (fun e => ∀ v ∈ e, v ∈ G.N i), y (e.map Sum.inl)

/-- `B_i`: total cover weight on the incidences of `v_i`. -/
noncomputable def wB : ℝ := ∑ a ∈ G.N i, y s(Sum.inl a, Sum.inr i)

/-- `C_i`: total cover weight on clique edges crossing `N_i`/`R_i`. -/
noncomputable def wC : ℝ :=
  ∑ e ∈ (⊤ : SimpleGraph (Fin G.p)).edgeFinset.filter
    (fun e => ¬(∀ v ∈ e, v ∈ G.N i) ∧ ¬(∀ v ∈ e, v ∉ G.N i)), y (e.map Sum.inl)

/-- `E_i`: total cover weight on clique edges inside `R_i = K ∖ N_i`. -/
noncomputable def wE : ℝ :=
  ∑ e ∈ (⊤ : SimpleGraph (Fin G.p)).edgeFinset.filter
    (fun e => ∀ v ∈ e, v ∉ G.N i), y (e.map Sum.inl)

/-- The three clique-edge classes partition the clique total. -/
theorem class_partition :
    wA G y i + wC G y i + wE G y i
      = ∑ e ∈ (⊤ : SimpleGraph (Fin G.p)).edgeFinset, y (e.map Sum.inl) := by
  classical
  rw [wA, wC, wE]
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e
  refine Sym2.ind (fun a b => ?_) e
  intro hab
  simp_all [SimpleGraph.mem_edgeFinset, Sym2.forall]
  aesop

/-
**Aggregated NNI constraint**: `A_i + (d_i − 1)·B_i ≥ C(d_i, 2)`
(sum of the cover constraint over the `G`-triangles `{a, b, v_i}`, `{a,b} ⊆ N_i`).
-/
theorem agg_NNI (hy : IsFracCover G.graph y) (hd : 2 ≤ G.d i) :
    wA G y i + ((G.d i : ℝ) - 1) * wB G y i ≥ (G.d i : ℝ) * ((G.d i : ℝ) - 1) / 2 := by
  have hNNI : ∀ e ∈ (⊤ : SimpleGraph (Fin G.p)).edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ G.N i), y (e.map Sum.inl) + ∑ a ∈ e.toFinset, y s(Sum.inl a, Sum.inr i) ≥ 1 := by
    intro e he;
    rcases e with ⟨ a, b ⟩ ; simp_all +decide [ IsFracCover ] ;
    convert hy.2 { Sum.inl a, Sum.inl b, Sum.inr i } _ using 1;
    · rw [ edgesIn_triangle ];
      · have hab : a ≠ b := he.1
        have hT : Sym2.toFinset (Quot.mk (Sym2.Rel (Fin G.p)) (a, b)) = {a, b} :=
          Sym2.toFinset_mk_eq
        rw [hT, Finset.sum_pair hab, Finset.sum_insert (by simp [Sym2.eq_iff]),
          Finset.sum_pair (by simp [Sym2.eq_iff, hab])]
      · exact he.1;
      · exact he.2.1;
      · exact he.2.2;
    · simp +decide [ *, SimpleGraph.isNClique_iff ];
      exact ⟨ by exact he.2.2, by exact he.1, by exact he.2.1 ⟩;
  have hNNI_sum : ∑ e ∈ (⊤ : SimpleGraph (Fin G.p)).edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ G.N i), (y (e.map Sum.inl) + ∑ a ∈ e.toFinset, y s(Sum.inl a, Sum.inr i)) = wA G y i + (G.d i - 1) * wB G y i := by
    have hNNI_sum : ∑ e ∈ (⊤ : SimpleGraph (Fin G.p)).edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ G.N i), ∑ a ∈ e.toFinset, y s(Sum.inl a, Sum.inr i) = (G.d i - 1) * ∑ a ∈ G.N i, y s(Sum.inl a, Sum.inr i) := by
      have hNNI_sum : ∀ a ∈ G.N i, ∑ e ∈ (⊤ : SimpleGraph (Fin G.p)).edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ G.N i), (if a ∈ e.toFinset then 1 else 0) = (G.d i - 1) := by
        intro a ha
        have hNNI_sum : Finset.filter (fun e => a ∈ e.toFinset) ((⊤ : SimpleGraph (Fin G.p)).edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ G.N i)) = Finset.image (fun b => s(a, b)) (G.N i \ {a}) := by
          ext e; simp [Finset.mem_image];
          rcases e with ⟨ ⟨ x, y ⟩ ⟩ ; simp_all +decide [ Sym2.eq_swap ];
          grind;
        simp_all +decide [ Finset.sum_ite ];
        rw [ Finset.card_image_of_injOn, Finset.card_sdiff ] ; aesop;
        intro x hx y hy; aesop;
      have hNNI_sum : ∑ e ∈ (⊤ : SimpleGraph (Fin G.p)).edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ G.N i), ∑ a ∈ e.toFinset, y s(Sum.inl a, Sum.inr i) = ∑ a ∈ G.N i, ∑ e ∈ (⊤ : SimpleGraph (Fin G.p)).edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ G.N i), (if a ∈ e.toFinset then y s(Sum.inl a, Sum.inr i) else 0) := by
        rw [ Finset.sum_comm, Finset.sum_congr rfl ];
        simp +contextual [ Finset.sum_ite ];
        intro e he h; congr; ext; aesop;
      simp_all +decide [ Finset.sum_ite ];
      rw [ ← Finset.mul_sum _ _ _, Nat.cast_pred ( by linarith ) ];
    rw [ Finset.sum_add_distrib, hNNI_sum ] ; rfl;
  have hNNI_card : (Finset.filter (fun e => ∀ v ∈ e, v ∈ G.N i) (⊤ : SimpleGraph (Fin G.p)).edgeFinset).card = (G.d i).choose 2 := by
    show _ = ((G.N i).card).choose 2
    rw [← card_top_edges_within (G.N i)]
    congr 1
    ext e
    simp
  have hNNI_card : (Finset.filter (fun e => ∀ v ∈ e, v ∈ G.N i) (⊤ : SimpleGraph (Fin G.p)).edgeFinset).card = (G.d i : ℝ) * (G.d i - 1) / 2 := by
    rw [ hNNI_card, Nat.choose_two_right ];
    cases G.d i <;> norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.mod_two_of_bodd ];
  exact hNNI_card ▸ hNNI_sum ▸ le_trans ( by norm_num ) ( Finset.sum_le_sum hNNI )

/-
**Aggregated NNN constraint**: `(d_i − 2)·A_i ≥ C(d_i, 3)`.
-/
set_option maxHeartbeats 1000000 in
theorem agg_NNN (hy : IsFracCover G.graph y) (hd : 3 ≤ G.d i) :
    ((G.d i : ℝ) - 2) * wA G y i
      ≥ (G.d i : ℝ) * ((G.d i : ℝ) - 1) * ((G.d i : ℝ) - 2) / 6 := by
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ S ∈ Finset.powersetCard 3 (G.N i), ∑ e ∈ (⊤ : SimpleGraph (Fin G.p)).edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ S), y (e.map Sum.inl) = ∑ e ∈ (⊤ : SimpleGraph (Fin G.p)).edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ G.N i), (G.d i - 2) * y (e.map Sum.inl) := by
    have h_fubini : ∀ e ∈ (⊤ : SimpleGraph (Fin G.p)).edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ G.N i), ∑ S ∈ Finset.powersetCard 3 (G.N i), (if ∀ v ∈ e, v ∈ S then 1 else 0) = (G.d i - 2) := by
      intro e he
      have h_fubini : Finset.card (Finset.filter (fun S => ∀ v ∈ e, v ∈ S) (Finset.powersetCard 3 (G.N i))) = G.d i - 2 := by
        obtain ⟨a, b, hab⟩ : ∃ a b : Fin G.p, a ≠ b ∧ e = s(a, b) ∧ a ∈ G.N i ∧ b ∈ G.N i := by
          rcases e with ⟨ a, b ⟩ ; aesop;
        have h_count : Finset.card (Finset.filter (fun S => a ∈ S ∧ b ∈ S) ((G.N i).powersetCard 3)) = Finset.card (Finset.powersetCard 1 (G.N i \ {a, b})) := by
          refine' Finset.card_bij ( fun S hS => S \ { a, b } ) _ _ _ <;> simp_all +decide [ Finset.subset_iff ];
          · intro S hS₁ hS₂ hS₃ hS₄; rw [ Finset.card_sdiff ] ; simp_all +decide [ Finset.subset_iff ] ;
          · intro a₁ ha₁ ha₂ ha₃ ha₄ a₂ ha₅ ha₆ ha₇ ha₈ h; ext x; by_cases hx : x = a <;> by_cases hx' : x = b <;> simp_all +decide [ Finset.ext_iff ] ;
          · intro S hS hS'; obtain ⟨ x, hx ⟩ := Finset.card_eq_one.mp hS'; use { x, a, b } ; aesop;
        simp_all +decide [ Finset.card_sdiff, Finset.subset_iff ];
        rfl;
      aesop;
    have h_fubini : ∑ S ∈ Finset.powersetCard 3 (G.N i), ∑ e ∈ (⊤ : SimpleGraph (Fin G.p)).edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ S), y (e.map Sum.inl) = ∑ e ∈ (⊤ : SimpleGraph (Fin G.p)).edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ G.N i), ∑ S ∈ Finset.powersetCard 3 (G.N i), (if ∀ v ∈ e, v ∈ S then y (e.map Sum.inl) else 0) := by
      rw [ Finset.sum_comm, Finset.sum_congr rfl ];
      simp +contextual [ Finset.sum_ite ];
      intro S hS hS'; refine' Finset.sum_subset _ _ <;> simp_all +decide [ Finset.subset_iff ] ;
    simp_all +decide [ Finset.sum_ite ];
    refine' Finset.sum_congr rfl fun x hx => _;
    simp +zetaDelta at *;
    exact Or.inl ( by rw [ ‹∀ e : Sym2 ( Fin G.p ), ¬e.IsDiag → ( ∀ v ∈ e, v ∈ G.N i ) → # ( { x ∈ powersetCard 3 ( G.N i ) | ∀ v ∈ e, v ∈ x } ) = G.d i - 2› x hx.1 hx.2 ] ; rw [ Nat.cast_sub ] <;> norm_num ; linarith );
  -- By Fubini's theorem, we can interchange the order of summation in the aggregated NNN constraint.
  have h_fubini : ∑ S ∈ Finset.powersetCard 3 (G.N i), ∑ e ∈ (⊤ : SimpleGraph (Fin G.p)).edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ S), y (e.map Sum.inl) ≥ ∑ S ∈ Finset.powersetCard 3 (G.N i), 1 := by
    gcongr;
    convert hy.2 _ _;
    rotate_left;
    exact Finset.image ( fun x : Fin G.p => Sum.inl x ) ‹Finset ( Fin G.p ) ›;
    · simp_all +decide [ SimpleGraph.isNClique_iff, Finset.card_image_of_injective, Function.Injective ];
      refine ⟨?_, ?_⟩
      · rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩ hab
        exact fun h => hab (congrArg _ h)
      · rw [Finset.card_image_of_injective _ Sum.inl_injective]
        simp_all
    · refine' Finset.sum_bij ( fun e he => e.map Sum.inl ) _ _ _ _ <;> simp +decide [ edgesIn ];
      · intro a ha h; induction a using Sym2.inductionOn; aesop;
      · intro a₁ ha₁ ha₂ a₂ ha₃ ha₄ h; induction a₁ using Sym2.inductionOn ; induction a₂ using Sym2.inductionOn ; aesop;
      · rintro ⟨ a, b ⟩ hab h₁ h₂; rcases a with ( a | a ) <;> rcases b with ( b | b ) <;> simp_all +decide ;
        · exact ⟨ s(a, b), ⟨ by aesop_cat, by aesop_cat ⟩, rfl ⟩;
        · exact absurd ( h₂ a ) ( by simp +decide );
  simp_all +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, wA ];
  convert h_fubini using 1;
  rw [ Nat.cast_choose ];
  · rw [ div_eq_div_iff ] <;> norm_num [ Nat.factorial ];
    · rw [ show ( Finset.card ( G.N i ) : ℕ ) = G.d i from rfl ] ; rcases n : G.d i with ( _ | _ | _ | k ) <;> simp_all +decide [ Nat.factorial ] ; ring;
    · positivity;
  · exact hd

/-
**Aggregated NNR constraint**: `r_i·A_i + (d_i − 1)·C_i ≥ C(d_i,2)·r_i`.
-/
set_option maxHeartbeats 1000000 in
theorem agg_NNR (hy : IsFracCover G.graph y) (hd : 2 ≤ G.d i)
    (hr : 1 ≤ G.p - G.d i) :
    ((G.p - G.d i : ℕ) : ℝ) * wA G y i + ((G.d i : ℝ) - 1) * wC G y i
      ≥ ((G.d i : ℝ) * ((G.d i : ℝ) - 1) / 2) * ((G.p - G.d i : ℕ) : ℝ) := by
  obtain ⟨N, hN⟩ : ∃ N : Finset (Fin G.p), N = G.N i ∧ N.card = G.d i ∧ N ⊆ Finset.univ := by
    aesop;
  have h_sum : ∑ a ∈ N, ∑ b ∈ N, ∑ u ∈ Nᶜ, (if a ≠ b then (y (s(Sum.inl a, Sum.inl b)) + y (s(Sum.inl a, Sum.inl u)) + y (s(Sum.inl b, Sum.inl u))) else 0) ≥ ∑ a ∈ N, ∑ b ∈ N, ∑ u ∈ Nᶜ, (if a ≠ b then 1 else 0) := by
    refine Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb =>
      Finset.sum_le_sum fun c hc => ?_
    have := hy.2 { Sum.inl a, Sum.inl b, Sum.inl c } ; simp_all +decide [ SimpleGraph.isNClique_iff ];
    by_cases hab : a = b <;> by_cases hac : a = c <;> by_cases hbc : b = c <;> simp_all +decide [ edgesIn_triangle ];
    simp_all +decide [ add_assoc, SplitGraph.Adj ];
    exact this ( by tauto ) ( by tauto ) ( by tauto );
  have h_sum : ∑ a ∈ N, ∑ b ∈ N, ∑ u ∈ Nᶜ, (if a ≠ b then (y (s(Sum.inl a, Sum.inl b)) + y (s(Sum.inl a, Sum.inl u)) + y (s(Sum.inl b, Sum.inl u))) else 0) = 2 * (Nᶜ.card : ℝ) * wA G y i + 2 * (N.card - 1) * wC G y i := by
    have h_sum : ∑ a ∈ N, ∑ b ∈ N, ∑ u ∈ Nᶜ, (if a ≠ b then y (s(Sum.inl a, Sum.inl b)) else 0) = 2 * (Nᶜ.card : ℝ) * wA G y i := by
      have h_sum : ∑ a ∈ N, ∑ b ∈ N, (if a ≠ b then y (s(Sum.inl a, Sum.inl b)) else 0) = 2 * wA G y i := by
        have h_sum : ∑ a ∈ N, ∑ b ∈ N, (if a ≠ b then y (s(Sum.inl a, Sum.inl b)) else 0) = ∑ e ∈ (⊤ : SimpleGraph (Fin G.p)).edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ N), y (e.map Sum.inl) * 2 := by
          have h_sum : ∑ a ∈ N, ∑ b ∈ N, (if a ≠ b then y (s(Sum.inl a, Sum.inl b)) else 0) = ∑ e ∈ (⊤ : SimpleGraph (Fin G.p)).edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ N), ∑ a ∈ N, ∑ b ∈ N, (if e = s(a, b) then y (e.map Sum.inl) else 0) := by
            rw [ Finset.sum_comm, Finset.sum_congr rfl ];
            rw [ Finset.sum_comm ];
            intro a ha; rw [ Finset.sum_comm ] ; simp +decide [ Finset.sum_ite, Finset.filter_ne', Finset.filter_eq', Sym2.eq_swap ] ;
            congr 1 with x ; aesop;
          rw [h_sum];
          refine' Finset.sum_congr rfl fun e he => _;
          rcases e with ⟨ a, b ⟩ ; simp +decide [ Finset.sum_ite ] at he ⊢;
          rw [ Finset.sum_eq_add ( a ) ( b ) ] <;> simp +decide [ he ];
          · rw [ show ( Finset.filter ( fun x => b = x ∨ a = x ∧ b = a ) N ) = { b } from ?_, show ( Finset.filter ( fun x => a = x ) N ) = { a } from ?_ ] <;> norm_num [ he ] ; ring; all_goals grind;
          · grind;
        rw [ h_sum, ← Finset.sum_mul _ _ _ ] ; ring!;
        unfold wA; aesop;
      simp_all +decide [ Finset.sum_ite ];
      simp_all +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ] ; ring;
    have h_sum : ∑ a ∈ N, ∑ b ∈ N, ∑ u ∈ Nᶜ, (if a ≠ b then y (s(Sum.inl a, Sum.inl u)) else 0) = (N.card - 1) * wC G y i := by
      have h_sum : ∑ a ∈ N, ∑ u ∈ Nᶜ, y (s(Sum.inl a, Sum.inl u)) = wC G y i := by
        rw [ ← Finset.sum_product' ];
        refine' Finset.sum_bij ( fun x hx => s(x.1, x.2) ) _ _ _ _ <;> simp +decide [ * ];
        · grind +qlia;
        · grind;
        · rintro ⟨ a, b ⟩ hab x hx₁ hx₂ y hy₁ hy₂; use y, x; aesop;
      simp +decide [ ← h_sum, Finset.sum_ite, Finset.filter_ne ];
      rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_congr rfl fun x hx => by rw [ Finset.card_erase_of_mem hx ] ; rw [ Nat.cast_sub ( by linarith ) ] ; ring;
    have h_sum : ∑ a ∈ N, ∑ b ∈ N, ∑ u ∈ Nᶜ, (if a ≠ b then y (s(Sum.inl b, Sum.inl u)) else 0) = (N.card - 1) * wC G y i := by
      rw [ ← h_sum, Finset.sum_comm ];
      simp +decide only [ne_comm];
    convert congr_arg₂ ( · + · ) ( congr_arg₂ ( · + · ) ‹ ( ∑ a ∈ N, ∑ b ∈ N, ∑ u ∈ Nᶜ, if a ≠ b then y s(Sum.inl a, Sum.inl b) else 0 ) = 2 * ↑ ( #Nᶜ ) * wA G y i › ‹ ( ∑ a ∈ N, ∑ b ∈ N, ∑ u ∈ Nᶜ, if a ≠ b then y s(Sum.inl a, Sum.inl u) else 0 ) = ( ↑ ( #N ) - 1 ) * wC G y i › ) ‹ ( ∑ a ∈ N, ∑ b ∈ N, ∑ u ∈ Nᶜ, if a ≠ b then y s(Sum.inl b, Sum.inl u) else 0 ) = ( ↑ ( #N ) - 1 ) * wC G y i › using 1 ; ring;
    · simp +decide only [← sum_add_distrib] ; congr ; ext ; congr ; ext ; congr ; ext ; split_ifs <;> ring;
    · ring;
  have h_sum : ∑ a ∈ N, ∑ b ∈ N, ∑ u ∈ Nᶜ, (if a ≠ b then 1 else 0) = (N.card * (N.card - 1)) * Nᶜ.card := by
    simp +decide [ Finset.sum_ite, Finset.filter_ne ];
    rw [ Finset.sum_congr rfl fun x hx => by rw [ Finset.card_erase_of_mem hx ] ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.sum_mul _ _ _ ];
  simp_all +decide [ Finset.card_compl ];
  simp_all +decide [ Finset.sum_ite, Finset.filter_ne ];
  simp_all +decide [ ← hN.1 ];
  rw [ Nat.cast_sub ] at * <;> try linarith;
  · rw [ Nat.cast_sub ] at *;
    · norm_num at * ; linarith;
    · exact le_of_lt ( Nat.lt_of_sub_pos hr );
  · exact le_of_lt ( Nat.lt_of_sub_pos hr );
  · exact le_of_lt ( Nat.lt_of_sub_pos hr )

/-
**Aggregated NRR constraint**: `(r_i − 1)·C_i + d_i·E_i ≥ d_i·C(r_i,2)`.
-/
set_option maxHeartbeats 2000000 in
theorem agg_NRR (hy : IsFracCover G.graph y) (hd : 1 ≤ G.d i)
    (hr : 2 ≤ G.p - G.d i) :
    (((G.p - G.d i : ℕ) : ℝ) - 1) * wC G y i + (G.d i : ℝ) * wE G y i
      ≥ (G.d i : ℝ) * (((G.p - G.d i : ℕ) : ℝ) * (((G.p - G.d i : ℕ) : ℝ) - 1) / 2) := by
  have hAggNNR : ∀ a ∈ G.N i, ∀ u ∈ (G.N i)ᶜ, ∀ v ∈ (G.N i)ᶜ, u ≠ v →
    (y s(Sum.inl u, Sum.inl v) + y s(Sum.inl a, Sum.inl u) + y s(Sum.inl a, Sum.inl v)) ≥ 1 := by
      intros a ha u hu v hv huv
      have h_triangle : G.graph.IsNClique 3 {Sum.inl a, Sum.inl u, Sum.inl v} := by
        simp_all +decide [ SimpleGraph.isNClique_iff ];
        exact ⟨ ⟨ by tauto, by tauto, by tauto ⟩, by rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton ] <;> aesop ⟩;
      have := hy.2 { Sum.inl a, Sum.inl u, Sum.inl v } ?_ <;> simp_all +decide [ Finset.sum_filter ];
      rw [ edgesIn_triangle ] at this;
      · grind;
      · exact h_triangle.1 ( by aesop ) ( by aesop ) ( by aesop );
      · exact h_triangle.1 ( by aesop ) ( by aesop ) ( by aesop );
      · exact h_triangle.1 |> fun h => by aesop;
  have h_sumNNR : ∑ a ∈ G.N i, ∑ u ∈ (G.N i)ᶜ, ∑ v ∈ (G.N i)ᶜ, (if u ≠ v then (y s(Sum.inl u, Sum.inl v) + y s(Sum.inl a, Sum.inl u) + y s(Sum.inl a, Sum.inl v)) else 0) ≥ (G.d i : ℝ) * ((G.p - G.d i : ℕ) : ℝ) * ((G.p - G.d i : ℕ) - 1) := by
    refine' le_trans _ ( Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun u hu => Finset.sum_le_sum fun v hv => show ( if u ≠ v then y s(Sum.inl u, Sum.inl v) + y s(Sum.inl a, Sum.inl u) + y s(Sum.inl a, Sum.inl v) else 0 ) ≥ if u ≠ v then 1 else 0 from _ );
    · simp +decide [ Finset.sum_ite, Finset.filter_ne ];
      rw [ Finset.sum_congr rfl fun x hx => by rw [ Finset.card_erase_of_mem hx ] ] ; norm_num [ Finset.card_compl ] ; ring_nf ; norm_num;
      norm_num [ SplitGraph.d ] at *;
      rw [ Nat.cast_sub ( by omega ) ] ; ring_nf;
      rw [ Nat.sub_sub, Nat.cast_sub ] <;> push_cast <;> nlinarith [ Nat.sub_add_cancel ( show # ( G.N i ) ≤ G.p from le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ) ];
    · aesop;
  have h_sumNNR_simplified : ∑ a ∈ G.N i, ∑ u ∈ (G.N i)ᶜ, ∑ v ∈ (G.N i)ᶜ, (if u ≠ v then y s(Sum.inl u, Sum.inl v) else 0) = 2 * (G.d i : ℝ) * wE G y i := by
    have h_sumNNR : ∑ u ∈ (G.N i)ᶜ, ∑ v ∈ (G.N i)ᶜ, (if u ≠ v then y s(Sum.inl u, Sum.inl v) else 0) = 2 * wE G y i := by
      have h_sumNNR : ∑ u ∈ (G.N i)ᶜ, ∑ v ∈ (G.N i)ᶜ, (if u ≠ v then y s(Sum.inl u, Sum.inl v) else 0) = ∑ e ∈ (⊤ : SimpleGraph (Fin G.p)).edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ (G.N i)ᶜ), y (e.map Sum.inl) * 2 := by
        have h_sumNNR : ∀ u ∈ (G.N i)ᶜ, ∑ v ∈ (G.N i)ᶜ, (if u ≠ v then y s(Sum.inl u, Sum.inl v) else 0) = ∑ e ∈ (⊤ : SimpleGraph (Fin G.p)).edgeFinset.filter (fun e => u ∈ e ∧ ∀ v ∈ e, v ∈ (G.N i)ᶜ), y (e.map Sum.inl) := by
          intros u hu
          have h_sumNNR : Finset.filter (fun e => u ∈ e ∧ ∀ v ∈ e, v ∈ (G.N i)ᶜ) (⊤ : SimpleGraph (Fin G.p)).edgeFinset = Finset.image (fun v => s(u, v)) (Finset.filter (fun v => u ≠ v) (G.N i)ᶜ) := by
            ext e; simp [Finset.mem_image];
            constructor;
            · rcases e with ⟨ a, b ⟩ ; simp +decide [ Sym2.eq_swap ] ;
              grind;
            · rintro ⟨ v, hv, rfl ⟩ ; simp_all +decide [ Sym2.IsDiag ];
          simp_all +decide [ Finset.sum_ite ];
        rw [ Finset.sum_congr rfl h_sumNNR, Finset.sum_sigma' ];
        rw [ show ( Finset.sigma ( G.N i ) ᶜ fun x => Finset.filter ( fun e => x ∈ e ∧ ∀ v ∈ e, v ∈ ( G.N i ) ᶜ ) ( ⊤ : SimpleGraph ( Fin G.p ) ).edgeFinset ) = Finset.biUnion ( Finset.filter ( fun e => ∀ v ∈ e, v ∈ ( G.N i ) ᶜ ) ( ⊤ : SimpleGraph ( Fin G.p ) ).edgeFinset ) ( fun e => Finset.image ( fun x => ⟨ x, e ⟩ ) ( Finset.filter ( fun x => x ∈ e ) ( G.N i ) ᶜ ) ) from ?_, Finset.sum_biUnion ];
        · refine' Finset.sum_congr rfl fun e he => _;
          rcases e with ⟨ u, v ⟩ ; simp +decide [ Finset.filter_insert, Finset.filter_singleton ] at he ⊢;
          rw [ show ( Finset.filter ( fun x => x = u ∨ x = v ) ( G.N i ) ᶜ ) = { u, v } by ext x; aesop ] ; simp +decide [ he ] ; ring;
        · intros e he f hf hne; simp_all +decide [ Finset.disjoint_left ] ;
          grind;
        · ext ⟨x, e⟩; simp [Finset.mem_sigma, Finset.mem_biUnion];
          tauto;
      rw [ h_sumNNR, ← Finset.sum_mul _ _ _ ] ; ring!;
      congr! 1;
      refine' Finset.sum_bij ( fun e he => e ) _ _ _ _ <;> simp +decide [ Sym2.map ];
    simp_all +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
    exact Or.inl rfl;
  have h_sumNNR_simplified : ∑ a ∈ G.N i, ∑ u ∈ (G.N i)ᶜ, ∑ v ∈ (G.N i)ᶜ, (if u ≠ v then y s(Sum.inl a, Sum.inl u) else 0) = ((G.p - G.d i : ℕ) - 1) * wC G y i := by
    have h_sumNNR_simplified : ∀ a ∈ G.N i, ∑ u ∈ (G.N i)ᶜ, ∑ v ∈ (G.N i)ᶜ, (if u ≠ v then y s(Sum.inl a, Sum.inl u) else 0) = ((G.p - G.d i : ℕ) - 1) * ∑ u ∈ (G.N i)ᶜ, y s(Sum.inl a, Sum.inl u) := by
      intros a ha
      have h_sumNNR_simplified : ∑ u ∈ (G.N i)ᶜ, ∑ v ∈ (G.N i)ᶜ, (if u ≠ v then y s(Sum.inl a, Sum.inl u) else 0) = ∑ u ∈ (G.N i)ᶜ, (Finset.card (G.N i)ᶜ - 1) * y s(Sum.inl a, Sum.inl u) := by
        simp +decide [ Finset.sum_ite, Finset.filter_ne ];
        exact Finset.sum_congr rfl fun x hx => by rw [ Finset.card_erase_of_mem hx ] ; simp +decide [ Nat.cast_sub ( show 1 ≤ Finset.card ( G.N i ) ᶜ from Finset.card_pos.mpr ⟨ x, hx ⟩ ) ] ;
      simp_all +decide [ Finset.card_compl ];
      rw [ Finset.mul_sum _ _ _ ];
      rfl;
    rw [ Finset.sum_congr rfl h_sumNNR_simplified, ← Finset.mul_sum _ _ _, wC ];
    rw [ Finset.sum_sigma' ];
    refine' congrArg _ ( Finset.sum_bij ( fun x hx => s(x.1, x.2) ) _ _ _ _ ) <;> simp +decide;
    · grind;
    · grind +revert;
    · rintro ⟨ a, b ⟩ hab x hx₁ hx₂ y hy₁ hy₂; use y, x; aesop;
  have h_sumNNR_simplified : ∑ a ∈ G.N i, ∑ u ∈ (G.N i)ᶜ, ∑ v ∈ (G.N i)ᶜ, (if u ≠ v then y s(Sum.inl a, Sum.inl v) else 0) = ((G.p - G.d i : ℕ) - 1) * wC G y i := by
    convert h_sumNNR_simplified using 1;
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by aesop );
  simp_all +decide [ Finset.sum_ite, Finset.filter_ne ];
  simp_all +decide [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _ ];
  linarith

/-
**Aggregated RRR constraint**: `(r_i − 2)·E_i ≥ C(r_i,3)`.
-/
set_option maxHeartbeats 1500000 in
theorem agg_RRR (hy : IsFracCover G.graph y) (hr : 3 ≤ G.p - G.d i) :
    (((G.p - G.d i : ℕ) : ℝ) - 2) * wE G y i
      ≥ ((G.p - G.d i : ℕ) : ℝ) * (((G.p - G.d i : ℕ) : ℝ) - 1)
        * (((G.p - G.d i : ℕ) : ℝ) - 2) / 6 := by
  have h_agg_NNN : ∀ t ∈ Finset.powersetCard 3 ((G.N i)ᶜ : Finset (Fin G.p)), 1 ≤ ∑ e ∈ (⊤ : SimpleGraph (Fin G.p)).edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ t), y (e.map Sum.inl) := by
    intro t ht; have := hy.2; simp_all +decide [ Finset.subset_iff ] ;
    convert this ( t.image Sum.inl ) _ using 1;
    · refine' Finset.sum_bij ( fun e he => e.map Sum.inl ) _ _ _ _ <;> simp +decide [ edgesIn ];
      · intro a ha ht; induction a using Sym2.inductionOn; aesop;
      · intro a₁ ha₁ ha₂ a₂ ha₃ ha₄ h; induction a₁ using Sym2.inductionOn ; induction a₂ using Sym2.inductionOn ; aesop;
      · rintro ⟨ a, b ⟩ hab h₁ h₂; rcases a with ( _ | a ) <;> rcases b with ( _ | b ) <;> simp_all +decide [ SplitGraph.graph ] ;
        · exact ⟨ s(_, _), ⟨ by aesop, by aesop ⟩, rfl ⟩;
        · exact absurd ( h₂ a ) ( by simp +decide );
    · simp_all +decide [ SimpleGraph.isNClique_iff, Finset.card_image_of_injective, Function.Injective ];
      refine ⟨?_, ?_⟩
      · rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩ hab
        exact fun h => hab (congrArg _ h)
      · rw [Finset.card_image_of_injective _ Sum.inl_injective]
        simp_all
  have h_double_count : ∑ t ∈ Finset.powersetCard 3 ((G.N i)ᶜ : Finset (Fin G.p)), (∑ e ∈ (⊤ : SimpleGraph (Fin G.p)).edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ t), y (e.map Sum.inl)) = ∑ e ∈ (⊤ : SimpleGraph (Fin G.p)).edgeFinset.filter (fun e => ∀ v ∈ e, v ∉ G.N i), (G.p - G.d i - 2) * y (e.map Sum.inl) := by
    have h_double_count : ∀ e ∈ (⊤ : SimpleGraph (Fin G.p)).edgeFinset.filter (fun e => ∀ v ∈ e, v ∉ G.N i), ∑ t ∈ Finset.powersetCard 3 ((G.N i)ᶜ : Finset (Fin G.p)), (if ∀ v ∈ e, v ∈ t then 1 else 0) = (G.p - G.d i - 2 : ℕ) := by
      intros e he
      have h_card : ∀ a b : Fin G.p, a ≠ b → a ∉ G.N i → b ∉ G.N i → ∑ t ∈ Finset.powersetCard 3 ((G.N i)ᶜ : Finset (Fin G.p)), (if a ∈ t ∧ b ∈ t then 1 else 0) = (G.p - G.d i - 2) := by
        intros a b hab ha hb
        have h_card : Finset.card (Finset.filter (fun t => a ∈ t ∧ b ∈ t) (Finset.powersetCard 3 ((G.N i)ᶜ : Finset (Fin G.p)))) = Finset.card (Finset.powersetCard 1 ((G.N i)ᶜ \ {a, b})) := by
          refine' Finset.card_bij ( fun t ht => t \ { a, b } ) _ _ _;
          · grind;
          · simp +contextual [ Finset.ext_iff ];
            grind;
          · simp +decide [ Finset.mem_powersetCard, Finset.subset_iff ];
            intro t ht ht'; obtain ⟨ x, hx ⟩ := Finset.card_eq_one.mp ht'; use { x, a, b } ; aesop;
        simp_all +decide [ Finset.card_sdiff, Finset.card_singleton, Finset.card_insert_of_notMem, Finset.card_compl ];
        rfl;
      rcases e with ⟨ a, b ⟩ ; simp_all +decide [ Finset.sum_ite ] ;
    have h_double_count : ∑ t ∈ Finset.powersetCard 3 ((G.N i)ᶜ : Finset (Fin G.p)), (∑ e ∈ (⊤ : SimpleGraph (Fin G.p)).edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ t), y (e.map Sum.inl)) = ∑ e ∈ (⊤ : SimpleGraph (Fin G.p)).edgeFinset.filter (fun e => ∀ v ∈ e, v ∉ G.N i), (∑ t ∈ Finset.powersetCard 3 ((G.N i)ᶜ : Finset (Fin G.p)), (if ∀ v ∈ e, v ∈ t then y (e.map Sum.inl) else 0)) := by
      rw [ Finset.sum_comm, Finset.sum_congr rfl ];
      simp +contextual [ Finset.sum_ite ];
      intro t ht ht'; refine' Finset.sum_subset _ _ <;> simp +contextual [ Finset.subset_iff ] ;
      exact fun e he he' v hv => fun hv' => Finset.mem_compl.mp ( ht ( he' v hv ) ) hv';
    convert h_double_count using 2;
    simp_all +decide [ Finset.sum_ite ];
    exact Or.inl ( by rw [ Nat.cast_sub <| by omega, Nat.cast_sub <| by omega ] ; push_cast ; ring );
  have := Finset.sum_le_sum h_agg_NNN; simp_all +decide [ Finset.sum_add_distrib, Finset.mul_sum _ _ _ ] ;
  convert this using 1;
  · rw [ Nat.cast_choose ] <;> norm_num [ Finset.card_compl ];
    · rw [ div_eq_div_iff ] <;> norm_num [ Nat.factorial_ne_zero ];
      rw [ show G.p - # ( G.N i ) = ( G.p - G.d i ) by rfl ] ; rcases n : G.p - G.d i with ( _ | _ | _ | n ) <;> simp_all +decide [ Nat.factorial ] ; ring;
    · exact hr;
  · simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, wE ];
    exact Or.inl <| Nat.cast_sub <| le_of_lt <| Nat.lt_of_sub_pos <| pos_of_gt hr

/-- Class sums are nonnegative. -/
theorem wA_nonneg (hy : IsFracCover G.graph y) : 0 ≤ wA G y i :=
  Finset.sum_nonneg fun e _ => hy.1 _

theorem wB_nonneg (hy : IsFracCover G.graph y) : 0 ≤ wB G y i :=
  Finset.sum_nonneg fun a _ => hy.1 _

theorem wC_nonneg (hy : IsFracCover G.graph y) : 0 ≤ wC G y i :=
  Finset.sum_nonneg fun e _ => hy.1 _

theorem wE_nonneg (hy : IsFracCover G.graph y) : 0 ≤ wE G y i :=
  Finset.sum_nonneg fun e _ => hy.1 _

/-- `d_i ≤ p`. -/
theorem d_le_p : G.d i ≤ G.p := by
  have := Finset.card_le_univ (G.N i)
  simpa [SplitGraph.d] using this

/-- **Per-vertex class bound** (E-4.1's inner inequality, via `lp_dual_bound_real`):
`A_i + q·B_i + C_i + E_i ≥ F(p, q, d_i)`. -/
theorem class_bound (hy : IsFracCover G.graph y) (hp : 3 ≤ G.p) (hq : 1 ≤ G.q) :
    ((F G.p G.q (G.d i) : ℚ) : ℝ)
      ≤ wA G y i + (G.q : ℝ) * wB G y i + wC G y i + wE G y i := by
  have hdp : G.d i ≤ G.p := d_le_p G i
  have hdr : G.d i + (G.p - G.d i) = G.p := Nat.add_sub_cancel' hdp
  have hq0 : (0 : ℝ) ≤ (G.q : ℝ) := by positivity
  have key := lp_dual_bound_real (G.d i) (G.p - G.d i) G.q
    (wA G y i) ((G.q : ℝ) * wB G y i) (wC G y i) (wE G y i)
    hq (by omega)
    (wA_nonneg G y i hy) (mul_nonneg hq0 (wB_nonneg G y i hy))
    (wC_nonneg G y i hy) (wE_nonneg G y i hy)
    (fun hd => by
      have h1 := agg_NNI G y i hy hd
      have h2 := mul_le_mul_of_nonneg_left h1 hq0
      calc ((G.d i : ℝ) * ((G.d i : ℝ) - 1) / 2) * (G.q : ℝ)
          = (G.q : ℝ) * ((G.d i : ℝ) * ((G.d i : ℝ) - 1) / 2) := by ring
        _ ≤ (G.q : ℝ) * (wA G y i + ((G.d i : ℝ) - 1) * wB G y i) := h2
        _ = (G.q : ℝ) * wA G y i + ((G.d i : ℝ) - 1) * ((G.q : ℝ) * wB G y i) := by
            ring)
    (fun hd => agg_NNN G y i hy hd)
    (fun hd hr => agg_NNR G y i hy hd hr)
    (fun hd hr => agg_NRR G y i hy hd hr)
    (fun hr => agg_RRR G y i hy hr)
  refine le_trans (le_of_eq ?_) key
  -- identify `↑F` with the LP minimum, using `↑(p − d) = ↑p − ↑d`
  have hcast : ((G.p - G.d i : ℕ) : ℝ) = (G.p : ℝ) - (G.d i : ℝ) :=
    Nat.cast_sub hdp
  have hF : F G.p G.q (G.d i)
      = min ((C2 G.p + G.q * G.d i) / 3)
          (min (C2 (G.d i) + C2 ((G.p : ℚ) - G.d i))
            (C2 (G.d i) + ((G.d i : ℚ) * ((G.p : ℚ) - G.d i)
              + C2 ((G.p : ℚ) - G.d i)) / 3)) := rfl
  rw [hF, Rat.cast_min, Rat.cast_min]
  have e1 : (((C2 G.p + G.q * G.d i) / 3 : ℚ) : ℝ)
      = ((((G.d i : ℝ) + ((G.p - G.d i : ℕ) : ℝ))
          * (((G.d i : ℝ) + ((G.p - G.d i : ℕ) : ℝ)) - 1) / 2
          + (G.q : ℝ) * (G.d i : ℝ)) / 3) := by
    rw [hcast, C2]
    push_cast
    ring
  have e2 : ((C2 (G.d i) + C2 ((G.p : ℚ) - G.d i) : ℚ) : ℝ)
      = ((G.d i : ℝ) * ((G.d i : ℝ) - 1) / 2
          + ((G.p - G.d i : ℕ) : ℝ) * (((G.p - G.d i : ℕ) : ℝ) - 1) / 2) := by
    rw [hcast, C2, C2]
    push_cast
    ring
  have e3 : ((C2 (G.d i) + ((G.d i : ℚ) * ((G.p : ℚ) - G.d i)
        + C2 ((G.p : ℚ) - G.d i)) / 3 : ℚ) : ℝ)
      = ((G.d i : ℝ) * ((G.d i : ℝ) - 1) / 2
          + ((G.d i : ℝ) * ((G.p - G.d i : ℕ) : ℝ)
            + ((G.p - G.d i : ℕ) : ℝ) * (((G.p - G.d i : ℕ) : ℝ) - 1) / 2) / 3) := by
    rw [hcast, C2, C2]
    push_cast
    ring
  rw [e1, e2, e3]

end Agg

open Agg in
/-- **E-4.1 (Replication)**: `ν₃*(G) ≥ (1/q) Σᵢ F(p, q, dᵢ)` for `q ≥ 1`
(`ν₃*` read as the LP cover optimum `τ₃*`; LEDGER E-4.1). -/
theorem E_4_1 (G : SplitGraph) (hp : 3 ≤ G.p) (hq : 1 ≤ G.q) :
    (1 / (G.q : ℝ)) * ∑ i, ((F G.p G.q (G.d i) : ℚ) : ℝ) ≤ tau3Star G.graph := by
  have hq0 : (0 : ℝ) < (G.q : ℝ) := by exact_mod_cast hq
  refine le_tau3Star _ _ fun y hy => ?_
  rw [one_div, inv_mul_le_iff₀ hq0]
  calc ∑ i, ((F G.p G.q (G.d i) : ℚ) : ℝ)
      ≤ ∑ i, (wA G y i + (G.q : ℝ) * wB G y i + wC G y i + wE G y i) :=
        Finset.sum_le_sum fun i _ => class_bound G y i hy hp hq
    _ = ∑ i, (wA G y i + wC G y i + wE G y i) + (G.q : ℝ) * ∑ i, wB G y i := by
        rw [Finset.mul_sum]
        simp only [Finset.sum_add_distrib]
        ring
    _ = (G.q : ℝ) * ∑ e ∈ G.graph.edgeFinset, y e := by
        rw [G.sum_edgeFinset y]
        have hpart : ∀ i : Fin G.q, wA G y i + wC G y i + wE G y i
            = ∑ e ∈ (⊤ : SimpleGraph (Fin G.p)).edgeFinset, y (e.map Sum.inl) :=
          fun i => class_partition G y i
        rw [Finset.sum_congr rfl fun i _ => hpart i, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hB : ∀ i : Fin G.q, wB G y i = ∑ a ∈ G.N i, y s(Sum.inl a, Sum.inr i) :=
          fun i => rfl
        rw [Finset.sum_congr rfl fun i _ => hB i]
        ring

open Agg CommonProfile in
/-- **E-3.1 (Common-profile formula)**: `ν₃*(H(p,q,d)) = F(p,q,d)` for `p ≥ 3`,
`q ≥ 1`, `d ≤ p` (`ν₃*` read as the LP cover optimum `τ₃*`; LEDGER E-3.1). -/
theorem E_3_1 (p q d : ℕ) (hp : 3 ≤ p) (hq : 1 ≤ q) (hd : d ≤ p) :
    tau3Star (commonProfile p q d).graph = ((F p q d : ℚ) : ℝ) := by
  refine le_antisymm (tau3Star_le_F hd) ?_
  have h := E_4_1 (commonProfile p q d) hp hq
  simp only [show (commonProfile p q d).p = p from rfl,
    show (commonProfile p q d).q = q from rfl] at h
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hsum : ∑ i : Fin (commonProfile p q d).q,
        ((F p q ((commonProfile p q d).d i) : ℚ) : ℝ)
      = (q : ℝ) * ((F p q d : ℚ) : ℝ) := by
    rw [Finset.sum_congr rfl fun i _ => by rw [card_N (q := q) hd i]]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    all_goals rfl
  rw [hsum, one_div, inv_mul_cancel_left₀ (ne_of_gt hq0)] at h
  exact h

end PaperIII