/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PaperIII.Defs

/-!
# Paper III — 1-factorization of the complete graph (input to E-5.1/E-5.2/E-7.1)

`χ'(K_p) ≤ r_p` by the explicit round-robin coloring: for `p` odd, color
`{a,b} ↦ (a+b) mod p`; for `p` even, color `{a,b} ↦ (a+b) mod (p−1)` for `a,b < p−1`
and `{a, p−1} ↦ (2a) mod (p−1)`.  Also the averaging tool: an injection achieving at
least the mean (used by E-5.1's factor assignment).
-/

@[expose] public section

namespace PaperIII

open SplitGraph Finset

private lemma edge_coloring_of_vertex_formula {p r : ℕ} (g : Fin p → Fin p → ℕ)
    (hsym : ∀ a b, g a b = g b a)
    (hbound : ∀ a b, a ≠ b → g a b < r)
    (hproper : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → g a b ≠ g a c) :
    ∃ φ : Sym2 (Fin p) → ℕ,
      (∀ e ∈ (⊤ : SimpleGraph (Fin p)).edgeFinset, φ e < r) ∧
      ∀ e ∈ (⊤ : SimpleGraph (Fin p)).edgeFinset,
        ∀ f ∈ (⊤ : SimpleGraph (Fin p)).edgeFinset,
          e ≠ f → (∃ v, v ∈ e ∧ v ∈ f) → φ e ≠ φ f := by
  refine' ⟨ _, _, _ ⟩;
  exact fun e => Sym2.lift ⟨ fun a b => g a b, fun a b => by simp +decide [ hsym ] ⟩ e;
  · rintro ⟨ a, b ⟩ ; aesop;
  · intro e he f hf hne h; rcases e with ⟨ a, b ⟩ ; rcases f with ⟨ c, d ⟩ ; simp_all +decide ;
    grind

set_option maxHeartbeats 800000 in
/-- **Round-robin edge coloring of `K_p`** with `r_p = χ'(K_p)` colors: a proper edge
coloring `φ : Sym2 (Fin p) → ℕ` with all colors `< rp p`. -/
theorem complete_graph_edge_coloring (p : ℕ) :
    ∃ φ : Sym2 (Fin p) → ℕ,
      (∀ e ∈ (⊤ : SimpleGraph (Fin p)).edgeFinset, φ e < rp p) ∧
      ∀ e ∈ (⊤ : SimpleGraph (Fin p)).edgeFinset,
        ∀ f ∈ (⊤ : SimpleGraph (Fin p)).edgeFinset,
          e ≠ f → (∃ v, v ∈ e ∧ v ∈ f) → φ e ≠ φ f := by
  by_cases hp : p ≤ 1;
  · interval_cases p <;> simp_all +decide [ rp ];
  · by_cases hp_even : Even p;
    · convert edge_coloring_of_vertex_formula ( fun a b => if a = b then 0 else if a.val = p - 1 then ( 2 * b.val ) % ( p - 1 ) else if b.val = p - 1 then ( 2 * a.val ) % ( p - 1 ) else ( a.val + b.val ) % ( p - 1 ) ) _ _ _ using 1;
      · grind;
      · unfold rp; rcases p with ( _ | _ | p ) <;> simp_all +decide ;
        exact fun a b hab => by split_ifs <;> exact Nat.le_of_lt_succ ( Nat.mod_lt _ ( Nat.succ_pos _ ) ) ;
      · intro a b c hab hbc hca; simp +decide [ hab, hbc ] ;
        split_ifs <;> simp_all +decide [ Fin.ext_iff ];
        · intro h; have := Nat.modEq_iff_dvd.mp h.symm; simp_all +decide ;
          -- Since $p$ is even, $p - 1$ is odd, and thus $2$ is invertible modulo $p - 1$.
          have h_inv : ∃ x : ℤ, 2 * x ≡ 1 [ZMOD (p - 1)] := by
            exact ⟨ ( p / 2 ), Int.modEq_iff_dvd.mpr ⟨ -1, by linarith [ Nat.div_add_mod p 2, Nat.even_iff.mp hp_even ] ⟩ ⟩;
          obtain ⟨ x, hx ⟩ := h_inv;
          -- Multiply both sides of the congruence $2 * b ≡ 2 * c [ZMOD (p - 1)]$ by $x$.
          have h_mul : (2 * x) * b ≡ (2 * x) * c [ZMOD (p - 1)] := by
            rw [ Int.modEq_iff_dvd ] at *;
            convert this.mul_left ( -x ) using 1 ; ring;
            · grind +splitImp;
            · ring;
          simp_all +decide [ Int.ModEq, Int.mul_emod ];
          simp_all +decide [ ← Int.mul_emod ];
          rw [ Int.emod_eq_of_lt, Int.emod_eq_of_lt ] at h_mul <;> omega;
        · intro h; have := Nat.modEq_iff_dvd.mp h.symm; simp_all +decide ;
          -- Since $p - 1$ divides $a - c$, we have $a \equiv c \pmod{p - 1}$.
          have h_mod : (a : ℤ) ≡ (c : ℤ) [ZMOD (p - 1)] := by
            exact Int.ModEq.symm ( Int.modEq_of_dvd <| by convert this using 1; rw [ Nat.cast_pred hp.le ] ; ring );
          rw [ Int.ModEq ] at h_mod;
          rw [ Int.emod_eq_of_lt, Int.emod_eq_of_lt ] at h_mod <;> omega;
        · intro h; have := Nat.modEq_iff_dvd.mp h.symm; simp_all +decide ;
          obtain ⟨ k, hk ⟩ := this; rcases p with ( _ | _ | p ) <;> simp_all +decide ;
          exact hab ( by nlinarith [ show k = 0 by nlinarith [ Fin.is_lt a, Fin.is_lt b, Nat.lt_of_le_of_ne ( Nat.le_of_lt_succ ( Fin.is_lt a ) ) ‹_›, Nat.lt_of_le_of_ne ( Nat.le_of_lt_succ ( Fin.is_lt b ) ) ‹_› ] ] );
        · intro h; have := Nat.modEq_iff_dvd.mp h.symm; simp_all +decide ;
          obtain ⟨ k, hk ⟩ := this; rw [ Nat.cast_sub hp.le ] at hk; simp_all +decide [ sub_eq_iff_eq_add ] ;
          rcases p with ( _ | _ | p ) <;> simp_all +decide;
          exact hca ( by nlinarith [ show k = 0 by nlinarith [ Fin.is_lt b, Fin.is_lt c, Nat.lt_of_le_of_ne ( Nat.le_of_lt_succ ( Fin.is_lt b ) ) ‹¬ ( b : ℕ ) = p + 1›, Nat.lt_of_le_of_ne ( Nat.le_of_lt_succ ( Fin.is_lt c ) ) ‹¬ ( c : ℕ ) = p + 1› ] ] );
    · convert edge_coloring_of_vertex_formula ( fun a b => ( a.val + b.val ) % p ) _ _ _ using 1 <;> norm_num [ Nat.ModEq, Nat.add_mod, Nat.mod_eq_of_lt ];
      · exact fun a b => by rw [ add_comm ] ;
      · unfold rp; simp +decide [ Nat.mod_eq_of_lt ] ;
        exact fun a b hab => by rw [ if_neg hp, if_neg hp_even ] ; exact Nat.mod_lt _ ( by linarith ) ;
      · intro a b c hab hbc hca; contrapose! hca; simp_all +decide [ Fin.ext_iff, Nat.mod_eq_of_lt ] ;
        exact Nat.mod_eq_of_lt b.2 ▸ Nat.mod_eq_of_lt c.2 ▸ by simpa [ ← ZMod.natCast_eq_natCast_iff' ] using hca;

/-- **Injection above the mean**: if `|A| ≤ |B|`, any weight `f : A → B → ℝ` admits an
injection `σ : A ↪ B` with `Σ_a f a (σ a) ≥ (1/|B|) Σ_a Σ_b f a b`. -/
theorem exists_injection_ge_mean {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (f : A → B → ℝ)
    (hAB : Fintype.card A ≤ Fintype.card B) (hB : 0 < Fintype.card B) :
    ∃ σ : A ↪ B, (1 / (Fintype.card B : ℝ)) * ∑ a, ∑ b, f a b
      ≤ ∑ a, f a (σ a) := by
  revert hAB hB;
  intro hAB hB_pos
  by_contra h_contra
  push_neg at h_contra
  have h_avg : ∑ σ : Function.Embedding A B, ∑ a : A, f a (σ a) = (Fintype.card (Function.Embedding A B) : ℝ) * (1 / Fintype.card B : ℝ) * ∑ a : A, ∑ b : B, f a b := by
    have h_avg : ∀ a : A, ∑ σ : Function.Embedding A B, f a (σ a) = (Fintype.card (Function.Embedding A B) : ℝ) * (1 / Fintype.card B : ℝ) * ∑ b : B, f a b := by
      intro a
      have h_sum_embedding : ∀ b : B, ∑ σ : Function.Embedding A B, (if σ a = b then 1 else 0 : ℝ) = (Fintype.card (Function.Embedding A B) : ℝ) / Fintype.card B := by
        intro b
        have h_sum_embedding : ∀ b₁ b₂ : B, ∑ σ : Function.Embedding A B, (if σ a = b₁ then 1 else 0 : ℝ) = ∑ σ : Function.Embedding A B, (if σ a = b₂ then 1 else 0 : ℝ) := by
          intro b₁ b₂
          have h_sum_embedding : ∑ σ : Function.Embedding A B, (if σ a = b₁ then 1 else 0 : ℝ) = ∑ σ : Function.Embedding A B, (if σ a = b₂ then 1 else 0 : ℝ) := by
            have h_bij : ∃ g : B ≃ B, g b₁ = b₂ := by
              exact ⟨ Equiv.swap b₁ b₂, by simp +decide ⟩
            obtain ⟨ g, hg ⟩ := h_bij
            generalize_proofs at *; (
            apply Finset.sum_bij (fun σ _ => Function.Embedding.mk (fun x => g (σ x)) (by
            exact g.injective.comp σ.injective))
            all_goals generalize_proofs at *;
            · exact fun _ _ => Finset.mem_univ _;
            · simp +decide [ Function.Embedding.ext_iff ];
            · exact fun σ _ => ⟨ Function.Embedding.mk ( fun x => g.symm ( σ x ) ) ( by
                exact fun x y hxy => σ.injective <| by simpa using hxy; ), Finset.mem_univ _, by ext x; exact g.apply_symm_apply (σ x) ⟩;
            · simp +decide [ ← hg ])
          generalize_proofs at *; (
          convert h_sum_embedding using 1)
        generalize_proofs at *; (
        have h_sum_embedding : ∑ b : B, ∑ σ : Function.Embedding A B, (if σ a = b then 1 else 0 : ℝ) = (Fintype.card (Function.Embedding A B) : ℝ) := by
          rw [ Finset.sum_comm ] ; aesop;
        generalize_proofs at *; (
        rw [ ← h_sum_embedding, Finset.sum_congr rfl fun x _ => ‹∀ b₁ b₂ : B, ( ∑ σ : Function.Embedding A B, if σ a = b₁ then 1 else 0 : ℝ ) = ∑ σ : Function.Embedding A B, if σ a = b₂ then 1 else 0› x b, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_cancel_left₀ _ ( by positivity ) ]))
      generalize_proofs at *; (
      have h_sum_embedding : ∑ σ : Function.Embedding A B, f a (σ a) = ∑ b : B, f a b * ∑ σ : Function.Embedding A B, (if σ a = b then 1 else 0 : ℝ) := by
        simp +decide only [Finset.mul_sum _ _ _];
        rw [ Finset.sum_comm ] ; simp +decide ;
      generalize_proofs at *; (
      simp_all +decide [ div_eq_mul_inv, mul_comm, Finset.mul_sum _ _ _ ];
      rw [ Finset.sum_mul _ _ _ ]))
    generalize_proofs at *; (
    rw [ Finset.sum_comm, Finset.mul_sum _ _ _, Finset.sum_congr rfl fun a ha => h_avg a ])
  generalize_proofs at *; (
  have h_card : Fintype.card (Function.Embedding A B) > 0 := by
    simp +zetaDelta at *;
    exact hAB
  generalize_proofs at *; (
  exact absurd ( Finset.sum_lt_sum_of_nonempty ( Finset.univ_nonempty_iff.mpr ⟨ Classical.choice ( Fintype.card_pos_iff.mp h_card ) ⟩ ) fun σ _ => h_contra σ ) ( by simp +decide [ h_avg, mul_assoc ] )));

end PaperIII
