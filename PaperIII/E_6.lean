/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PaperIII.CorridorDefs

/-!
# Paper III — §6 Quantitative polarization (E-6.1)

`V = Σ_{i,j} |Bᵢ ∖ Bⱼ|` with `Bᵢ = {e ∈ E(K) : e ∩ Sᵢ ≠ ∅}`; and if `2p − 3m − 1 ≥ 0`
then `V ≥ ((2p−3m−1)/4)·Σ_{i,j}|Sᵢ △ Sⱼ|` (LEDGER E-6.1).
-/

@[expose] public section

namespace PaperIII

open SplitGraph Finset

/-- `Bᵢ = {clique edges meeting Sᵢ}`. -/
def SplitGraph.badEdges (G : SplitGraph) (i : Fin G.q) : Finset (Sym2 (Fin G.p)) :=
  (⊤ : SimpleGraph (Fin G.p)).edgeFinset.filter fun e => ∃ v ∈ e, v ∈ G.S i

/-- **(6.1)**: `V = Σ_{i,j} |Bᵢ ∖ Bⱼ|`. -/
theorem dispersionV_eq (G : SplitGraph) :
    G.dispersionV = ∑ i, ∑ j, ((G.badEdges i) \ (G.badEdges j)).card := by
  have h1 : ∀ e ∈ (⊤ : SimpleGraph (Fin G.p)).edgeFinset, G.badCount e * (G.q - G.badCount e) = ∑ i : Fin G.q, ∑ j : Fin G.q, (if e ∈ G.badEdges i \ G.badEdges j then 1 else 0) := by
    intro e he
    have h_filter : G.badCount e = (Finset.univ.filter fun i : Fin G.q => e ∈ G.badEdges i).card := by
      simp +decide [ SplitGraph.badCount, SplitGraph.badEdges ];
      congr with i ; simp +decide [ SplitGraph.S ];
      cases e ; aesop;
    simp_all +decide;
    rw [ Finset.sum_congr rfl fun i hi => show Finset.card ( Finset.filter ( fun j => e ∈ G.badEdges i ∧ e ∉ G.badEdges j ) Finset.univ ) = if e ∈ G.badEdges i then Finset.card ( Finset.univ \ Finset.filter ( fun j => e ∈ G.badEdges j ) Finset.univ ) else 0 from ?_ ];
    · simp +decide [ Finset.sum_ite, Finset.card_sdiff ];
    · split_ifs <;> simp_all +decide [ Finset.filter_not ];
  rw [ SplitGraph.dispersionV, Finset.sum_congr rfl h1 ];
  rw [ Finset.sum_comm, Finset.sum_congr rfl ];
  intro i hi; rw [ Finset.sum_comm ] ; simp +decide;
  congr! 2;
  ext; simp [SplitGraph.badEdges];
  tauto

set_option maxHeartbeats 1000000 in
/-- **E-6.1 (Polarization inequality)**: if `2p − 3m − 1 ≥ 0` then
`V ≥ ((2p−3m−1)/4)·Σ_{i,j}|Sᵢ △ Sⱼ|` (LEDGER E-6.1). -/
theorem E_6_1 (G : SplitGraph) (m : ℕ) (hm : ∀ i, G.m i ≤ m)
    (hpos : 2 * G.p ≥ 3 * m + 1) :
    ((2 * (G.p : ℝ) - 3 * (m : ℝ) - 1) / 4)
        * ∑ i, ∑ j, ((symmDiff (G.S i) (G.S j)).card : ℝ)
      ≤ (G.dispersionV : ℝ) := by
  have h_abs_diff : ∀ i j : Fin G.q, (G.badEdges i \ G.badEdges j).card ≥ ((2 * G.p - 3 * m - 1) / 2 : ℝ) * (G.S i \ G.S j).card := by
    intro i j
    have h_card : (G.badEdges i \ G.badEdges j).card = (G.p - G.m j).choose 2 - (G.p - G.m j - (G.S i \ G.S j).card).choose 2 := by
      have h_card : (G.badEdges i \ G.badEdges j).card = ((⊤ : SimpleGraph (Fin G.p)).edgeFinset.filter fun e => ∀ v ∈ e, v ∈ (G.S j)ᶜ ∧ ∃ v ∈ e, v ∈ G.S i \ G.S j).card := by
        refine' congr_arg Finset.card ( Finset.ext fun e => _ );
        simp [SplitGraph.badEdges];
        constructor <;> intro h <;> simp_all +decide;
        · grind +qlia;
        · exact h.2 _ ( Classical.choose_spec ( show ∃ v, v ∈ e from by rcases e with ⟨ a, b ⟩ ; exact ⟨ a, by simp +decide ⟩ ) ) |>.2.imp fun x hx => ⟨ hx.1, hx.2.1 ⟩;
      have h_card : ((⊤ : SimpleGraph (Fin G.p)).edgeFinset.filter fun e => ∀ v ∈ e, v ∈ (G.S j)ᶜ ∧ ∃ v ∈ e, v ∈ G.S i \ G.S j).card = ((⊤ : SimpleGraph (Fin G.p)).edgeFinset.filter fun e => ∀ v ∈ e, v ∈ (G.S j)ᶜ).card - ((⊤ : SimpleGraph (Fin G.p)).edgeFinset.filter fun e => ∀ v ∈ e, v ∈ (G.S j)ᶜ ∧ ∀ v ∈ e, v ∉ G.S i \ G.S j).card := by
        rw [ tsub_eq_of_eq_add ];
        rw [ ← Finset.card_union_of_disjoint ];
        · congr with e ; by_cases he : ∃ v ∈ e, v ∈ G.S i \ G.S j <;> aesop;
        · simp +contextual [ Finset.disjoint_left ];
          exact fun e he₁ he₂ => by obtain ⟨ x, hx ⟩ := e; exact ⟨ ⟨ x, by aesop ⟩, by obtain ⟨ y, hy ⟩ := he₂ x ( by aesop ) |>.2; exact ⟨ y, by aesop ⟩ ⟩ ;
      have h_card : ∀ (A : Finset (Fin G.p)), ((⊤ : SimpleGraph (Fin G.p)).edgeFinset.filter fun e => ∀ v ∈ e, v ∈ A).card = Nat.choose A.card 2 := by
        intros A
        have h_card : ((⊤ : SimpleGraph (Fin G.p)).edgeFinset.filter fun e => ∀ v ∈ e, v ∈ A).card = Finset.card (Finset.powersetCard 2 A) := by
          refine' Finset.card_bij ( fun e he => Finset.univ.filter fun v => v ∈ e ) _ _ _ <;> simp +decide [ Finset.subset_iff ];
          · intro a ha hA; rcases a with ⟨ x, y ⟩ ; simp_all +decide [ Sym2.IsDiag ] ;
            rw [ show ( Finset.filter ( fun v => v = x ∨ v = y ) Finset.univ : Finset ( Fin G.p ) ) = { x, y } by ext; aesop ] ; aesop;
          · simp +contextual [ Finset.ext_iff, Sym2.ext_iff ];
          · intro b hb hb'; obtain ⟨ x, y, hxy ⟩ := Finset.card_eq_two.mp hb'; use s( x, y ) ; aesop;
        rw [ h_card, Finset.card_powersetCard ];
      simp_all +decide [ Finset.card_sdiff ];
      congr 1;
      · convert h_card ( G.S j ) ᶜ using 1;
        · simp +decide [ Finset.mem_compl ];
        · simp +decide [ Finset.card_compl, SplitGraph.m ];
      · convert h_card ( ( G.S j ) ᶜ \ ( G.S i \ G.S j ) ) using 1;
        · congr! 2;
          simp +decide [ Finset.mem_sdiff, Finset.mem_compl ] ;
          grind;
        · simp +decide [ Finset.card_sdiff ];
          rw [ show G.S i \ G.S j ∩ ( G.S j ) ᶜ = G.S i \ G.S j from ?_, Finset.card_sdiff ];
          · simp +decide [ Finset.card_compl, SplitGraph.m ];
          · exact Finset.inter_eq_left.mpr fun x hx => by aesop;
    have h_card_simplified : (G.p - G.m j).choose 2 - (G.p - G.m j - (G.S i \ G.S j).card).choose 2 ≥ ((2 * G.p - 3 * m - 1) / 2 : ℝ) * (G.S i \ G.S j).card := by
      have h_card_simplified : ∀ a b : ℕ, a ≥ b → (a.choose 2 - (a - b).choose 2 : ℝ) = b * (2 * a - b - 1) / 2 := by
        intros a b hab
        have h_card_simplified : (a.choose 2 : ℝ) = a * (a - 1) / 2 ∧ ((a - b).choose 2 : ℝ) = (a - b) * (a - b - 1) / 2 := by
          have h_card_simplified : ∀ n : ℕ, (n.choose 2 : ℝ) = n * (n - 1) / 2 := by
            exact fun n => by induction n <;> simp +decide [ Nat.choose, * ] ; ring;
          exact ⟨ h_card_simplified a, by rw [ h_card_simplified, Nat.cast_sub hab ] ⟩;
        rw [ h_card_simplified.1, h_card_simplified.2 ] ; ring;
      rw [ h_card_simplified ];
      · rw [ Nat.cast_sub ];
        · have h_card_simplified : (G.S i \ G.S j).card ≤ G.m i := by
            exact Finset.card_le_card fun x hx => by aesop;
          nlinarith only [ show ( G.m i : ℝ ) ≤ m by exact_mod_cast hm i, show ( G.m j : ℝ ) ≤ m by exact_mod_cast hm j, show ( #(G.S i \ G.S j) : ℝ ) ≤ G.m i by exact_mod_cast h_card_simplified, show ( 2 * G.p : ℝ ) ≥ 3 * m + 1 by exact_mod_cast hpos ];
        · exact le_trans ( hm j ) ( by linarith );
      · exact le_trans ( Finset.card_le_card fun x hx => by aesop ) ( show Finset.card ( G.S j )ᶜ ≤ G.p - G.m j from by simp +decide [ Finset.card_compl, SplitGraph.m ] );
    rw [ h_card, Nat.cast_sub ];
    · convert h_card_simplified using 1;
    · exact Nat.choose_le_choose _ ( Nat.sub_le _ _ );
  have h_sum_abs_diff : (G.dispersionV : ℝ) ≥ ((2 * G.p - 3 * m - 1) / 2 : ℝ) * (∑ i, ∑ j, (G.S i \ G.S j).card) := by
    simp_all +decide [ Finset.mul_sum _ _ _ ];
    exact le_trans ( Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h_abs_diff i j ) ( mod_cast by rw [ ← dispersionV_eq ] );
  have h_sum_symm_diff : (∑ i, ∑ j, (symmDiff (G.S i) (G.S j)).card : ℝ) = 2 * (∑ i, ∑ j, (G.S i \ G.S j).card) := by
    have h_sum_symm_diff : ∀ i j : Fin G.q, (symmDiff (G.S i) (G.S j)).card = (G.S i \ G.S j).card + (G.S j \ G.S i).card := by
      exact fun i j => by rw [ ← Finset.card_union_of_disjoint ( Finset.disjoint_right.mpr fun x => by aesop ) ] ; rfl;
    simp +decide [ h_sum_symm_diff, Finset.sum_add_distrib, two_mul ];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
  nlinarith [ show ( 2 * G.p : ℝ ) ≥ 3 * m + 1 by norm_cast ]

end PaperIII