/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PaperIII.Factorization
public import PaperIII.CorridorDefs

/-!
# Paper III — §5 Factorization rounding (E-5.1, E-5.2)

`E-5.1` (one-factor averaging): if `q ≥ r_p` then `ν₃(G) ≥ (1/q) Σᵢ C(dᵢ,2)`, via a
`1`-factorization of `K_p` assigned to `I` (Factorization.complete_graph_edge_coloring
+ exists_injection_ge_mean).  Corollary `5.3`: `Φ(G) ≤ n²/6 + p/2 + (s²−6s+3)/12`.
`E-5.2` (double-factor): `Φ(G) ≤ n²/6 + p/2 − s²/6 + ((s−1)M − S₂)/q − 2δV/(q(q−1))`.
-/

@[expose] public section

namespace PaperIII

open SplitGraph Finset

set_option maxHeartbeats 800000

private def factorEdges (G : SplitGraph) (φ : Sym2 (Fin G.p) → ℕ)
    (c : Fin (rp G.p)) (i : Fin G.q) : Finset (Sym2 (Fin G.p)) :=
  (⊤ : SimpleGraph (Fin G.p)).edgeFinset.filter
    fun e => φ e = c.1 ∧ ∀ v ∈ e, v ∈ G.N i

private def kkiTriangle (G : SplitGraph) (i : Fin G.q)
    (e : Sym2 (Fin G.p)) : Finset G.V :=
  insert (Sum.inr i) (e.toFinset.image Sum.inl)

private def assignedTriangles (G : SplitGraph) (φ : Sym2 (Fin G.p) → ℕ)
    (σ : Fin (rp G.p) ↪ Fin G.q) : Finset (Finset G.V) :=
  Finset.univ.biUnion fun c => (factorEdges G φ c (σ c)).image (kkiTriangle G (σ c))

private lemma assignedTriangles_isPacking (G : SplitGraph)
    (φ : Sym2 (Fin G.p) → ℕ)
    (hproper : ∀ e ∈ (⊤ : SimpleGraph (Fin G.p)).edgeFinset,
      ∀ f ∈ (⊤ : SimpleGraph (Fin G.p)).edgeFinset,
        e ≠ f → (∃ v, v ∈ e ∧ v ∈ f) → φ e ≠ φ f)
    (σ : Fin (rp G.p) ↪ Fin G.q) :
    IsTrianglePacking G.graph (assignedTriangles G φ σ) := by
  constructor;
  · unfold assignedTriangles; simp +decide [ *, SimpleGraph.isNClique_iff ] ;
    rintro t c e he rfl; unfold factorEdges kkiTriangle at *; simp_all +decide [ SimpleGraph.isClique_iff, Finset.card_image_of_injective, Function.Injective ] ;
    rcases e with ⟨ a, b ⟩ ; simp_all +decide [ SimpleGraph.adj_comm ] ;
    simp_all +decide [ Sym2.toFinset, Set.Pairwise ];
    simp_all +decide [ SplitGraph.graph, SplitGraph.Adj ];
    simp +decide [ Sym2.toMultiset, he.1 ];
  · intro t₁ ht₁ t₂ ht₂ hne;
    -- By definition of `assignedTriangles`, there exist colors `c₁` and `c₂` and edges `e₁` and `e₂` such that `t₁ = kkiTriangle G (σ c₁) e₁` and `t₂ = kkiTriangle G (σ c₂) e₂`.
    obtain ⟨c₁, e₁, hc₁, he₁⟩ : ∃ c₁ : Fin (rp G.p), ∃ e₁ : Sym2 (Fin G.p), t₁ = kkiTriangle G (σ c₁) e₁ ∧ e₁ ∈ factorEdges G φ c₁ (σ c₁) := by
      unfold assignedTriangles at ht₁; aesop;
    obtain ⟨c₂, e₂, hc₂, he₂⟩ : ∃ c₂ : Fin (rp G.p), ∃ e₂ : Sym2 (Fin G.p), t₂ = kkiTriangle G (σ c₂) e₂ ∧ e₂ ∈ factorEdges G φ c₂ (σ c₂) := by
      unfold assignedTriangles at ht₂; aesop;
    by_cases h : c₁ = c₂ <;> simp_all +decide [ factorEdges ];
    · -- Since $e₁$ and $e₂$ are distinct edges in the same color class, they cannot share any vertices.
      have h_no_common_vertices : ∀ v : Fin G.p, v ∈ e₁ → v ∈ e₂ → False := by
        grind;
      unfold kkiTriangle; simp +decide [ Finset.ext_iff ] ;
      exact fun v hv w hw h => h_no_common_vertices v hv ( h ▸ hw );
    · by_cases h' : e₁ = e₂ <;> simp_all +decide [ kkiTriangle ];
      · exact False.elim <| h <| Fin.ext he₁.1.symm;
      · contrapose! hproper;
        obtain ⟨ x, hx ⟩ := Finset.one_lt_card.mp hproper;
        cases e₁ ; cases e₂ ; aesop

private lemma card_assignedTriangles (G : SplitGraph)
    (φ : Sym2 (Fin G.p) → ℕ)
    (σ : Fin (rp G.p) ↪ Fin G.q) :
    (assignedTriangles G φ σ).card =
      ∑ c : Fin (rp G.p), (factorEdges G φ c (σ c)).card := by
  unfold assignedTriangles
  rw [Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [ Finset.card_image_of_injOn ];
    intro e₁ he₁ e₂ he₂ h_eq;
    unfold kkiTriangle at h_eq;
    simp_all +decide [ Finset.ext_iff, Sym2.ext_iff ];
  · intro c hc d hd hcd; simp_all +decide [ Finset.disjoint_left, kkiTriangle ] ;
    intro a ha x hx; intro H; replace H := Finset.ext_iff.mp H ( Sum.inr ( σ d ) ) ; simp_all +decide ;

private lemma sum_factorEdges_card (G : SplitGraph)
    (φ : Sym2 (Fin G.p) → ℕ)
    (hbound : ∀ e ∈ (⊤ : SimpleGraph (Fin G.p)).edgeFinset, φ e < rp G.p)
    (i : Fin G.q) :
    ∑ c : Fin (rp G.p), (factorEdges G φ c i).card = (G.d i).choose 2 := by
  show _ = ((G.N i).card).choose 2
  rw [ ← Finset.card_biUnion ];
  · convert Finset.card_powersetCard 2 ( G.N i ) using 1;
    refine' Finset.card_bij ( fun e he => e.toFinset ) _ _ _ <;> simp +decide [ factorEdges ];
    · intro a ha x hx hx'; rcases a with ⟨ a, b ⟩ ; simp_all +decide [ Finset.subset_iff ] ;
      simp +decide [ Sym2.toFinset, ha ];
      simp +decide [ Sym2.toMultiset, ha ];
    · intro a₁ ha₁ x hx₁ hx₂ a₂ ha₂ y hy₁ hy₂ h; rw [ Finset.ext_iff ] at h; simp_all +decide [ Sym2.ext_iff ] ;
    · intro b hb hb'; obtain ⟨ x, y, hxy ⟩ := Finset.card_eq_two.mp hb'; use s(x, y) ; simp_all +decide [ Finset.subset_iff ] ;
      exact ⟨ ⟨ ⟨ φ s(x, y), hbound _ ( by aesop ) ⟩, rfl ⟩, by aesop ⟩;
  · intros c hc d hd hcd; simp_all +decide [ Finset.disjoint_left, factorEdges ] ;
    exact fun e he₁ he₂ he₃ => by simpa [ Fin.ext_iff ] using hcd;

/-
**E-5.1 (One-factor averaging)**: if `q ≥ r_p` then
`ν₃(G) ≥ (1/q) Σᵢ C(dᵢ,2)` (LEDGER E-5.1).
-/
theorem E_5_1 (G : SplitGraph) (hrp : rp G.p ≤ G.q) (hq : 1 ≤ G.q) :
    (1 / (G.q : ℝ)) * ∑ i, ((G.d i).choose 2 : ℝ) ≤ (G.nu3' : ℝ) := by
  -- Welaminate edges E problem各项.
  set weight_f := fun c i => (factorEdges G (Classical.choose (complete_graph_edge_coloring G.p)) c i).card;
  -- By the existence of a uniform packing, there exists an injection $\sigma$ such that the sum of weights is at least the average.
  obtain ⟨σ, hσ⟩ : ∃ σ : Fin (rp G.p) ↪ Fin G.q, (∑ i, (∑ c, (weight_f c i))) ≤ (G.q : ℝ) * (∑ c, (weight_f c (σ c))) := by
    obtain ⟨σ, hσ⟩ := exists_injection_ge_mean
      (fun c i => (weight_f c i : ℝ) : Fin (rp G.p) → Fin G.q → ℝ)
      (by simpa using hrp) (by simp only [Fintype.card_fin]; omega)
    refine ⟨σ, ?_⟩
    have hq0 : (0 : ℝ) < G.q := by exact_mod_cast hq
    simp only [Fintype.card_fin] at hσ
    rw [one_div, inv_mul_le_iff₀ hq0] at hσ
    push_cast
    rw [Finset.sum_comm]
    exact hσ
  -- By the definition of `nu3'`, we know that
  have h_nu3'_def : (G.nu3' : ℝ) ≥ (∑ c, (weight_f c (σ c))) := by
    have h_nu3'_def : (G.nu3' : ℝ) ≥ (assignedTriangles G (Classical.choose (complete_graph_edge_coloring G.p)) σ).card := by
      refine' mod_cast le_csSup _ _;
      · exact ⟨ _, fun k hk => hk.choose_spec.2 ▸ Finset.card_le_univ _ ⟩;
      · exact ⟨ _, assignedTriangles_isPacking G _ ( Classical.choose_spec ( complete_graph_edge_coloring G.p ) |>.2 ) σ, rfl ⟩;
    convert h_nu3'_def using 1;
    rw [ card_assignedTriangles ];
  -- By the definition of `weight_f`, we know that
  have h_weight_f_sum : ∑ i, (∑ c, (weight_f c i)) = ∑ i, (G.d i).choose 2 := by
    refine' Finset.sum_congr rfl fun i hi => _;
    convert sum_factorEdges_card G ( Classical.choose ( complete_graph_edge_coloring G.p ) ) ( Classical.choose_spec ( complete_graph_edge_coloring G.p ) |>.1 ) i using 1;
  rw [ div_mul_eq_mul_div, div_le_iff₀ ] <;> norm_cast at * ; nlinarith

/-
**Corollary 5.3** (`q = 2p − s`): `Φ(G) ≤ n²/6 + p/2 + (s²−6s+3)/12`
(closes `s = O(√p)`; LEDGER E-5.1 corollary).
-/
theorem cor_5_3 (G : SplitGraph) (hrp : rp G.p ≤ G.q) (hq : 1 ≤ G.q) :
    ((G.Phi : ℤ) : ℝ)
      ≤ (G.n : ℝ) ^ 2 / 6 + (G.p : ℝ) / 2
        + ((G.s : ℝ) ^ 2 - 6 * (G.s : ℝ) + 3) / 12 := by
  -- From edgeCount_eq and Phi get Φ ≤ edgeCount - (2/q)Σchoose.
  have h_bound : (G.Phi : ℝ) ≤ (G.edgeCount : ℝ) - (2 / (G.q : ℝ)) * ∑ i, ((G.d i).choose 2 : ℝ) := by
    have := E_5_1 G hrp hq;
    unfold SplitGraph.Phi SplitGraph.nu3' at * ; norm_num at * ; ring_nf at * ; linarith!;
  -- Algebra gives intermediate Φ ≤ n²/6+p/2-s²/6+((s-1)M-S₂)/q.
  have h_intermediate : (G.Phi : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + (G.p : ℝ) / 2 - (G.s : ℝ) ^ 2 / 6 + ((G.s - 1) * (G.M : ℝ) - (G.S₂ : ℝ)) / (G.q : ℝ) := by
    -- From edgeCount_eq and Phi get Φ ≤ edgeCount - (2/q)Σchoose. Use this to derive the intermediate inequality.
    have h_intermediate : (G.Phi : ℝ) ≤ (G.p * (G.p - 1) / 2 + ∑ i, (G.d i : ℝ)) - (2 / (G.q : ℝ)) * (∑ i, ((G.d i).choose 2 : ℝ)) := by
      convert h_bound using 2;
      rw [ SplitGraph.edgeCount_eq ];
      norm_num [ Nat.choose_two_right ];
      cases G.p <;> norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.mod_two_of_bodd ];
    -- Use the identities $\sum d_i = qp - M$ and $\sum d_i^2 = qp^2 - 2pM + S_2$.
    have h_identities : (∑ i, (G.d i : ℝ)) = (G.p : ℝ) * (G.q : ℝ) - (G.M : ℝ) ∧ (∑ i, ((G.d i).choose 2 : ℝ)) = ((G.p : ℝ) * (G.q : ℝ) * (G.p - 1) - (G.M : ℝ) * (2 * (G.p : ℝ) - 1) + (G.S₂ : ℝ)) / 2 := by
      have h_identities : (∑ i, (G.d i : ℝ)) = (G.p : ℝ) * (G.q : ℝ) - (G.M : ℝ) ∧ (∑ i, ((G.d i) ^ 2 : ℝ)) = (G.p : ℝ) ^ 2 * (G.q : ℝ) - 2 * (G.p : ℝ) * (G.M : ℝ) + (G.S₂ : ℝ) := by
        have h_identities : ∀ i, (G.d i : ℝ) = (G.p : ℝ) - (G.m i : ℝ) := by
          intro i; rw [ eq_sub_iff_add_eq ] ; norm_cast; simp +decide [ SplitGraph.d, SplitGraph.m, SplitGraph.S ] ;
        simp_all +decide [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, sub_sq ];
        simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, mul_comm, SplitGraph.M, SplitGraph.S₂ ];
      have h_choose : ∀ i, ((G.d i).choose 2 : ℝ) = ((G.d i : ℝ) * ((G.d i : ℝ) - 1)) / 2 := by
        intro i; rw [ Nat.choose_two_right ] ; induction' G.d i with d hd <;> norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mod_two_of_bodd ] ;
      simp_all +decide [ Finset.sum_div _ _ _, mul_sub ];
      simp_all +decide [ ← sq, ← Finset.sum_div _ _ _ ] ; ring;
    convert h_intermediate using 1 ; push_cast [ h_identities ] ; ring;
    unfold SplitGraph.n SplitGraph.s; norm_num [ show G.q ≠ 0 by linarith ] ; ring;
    norm_num [ mul_comm, ne_of_gt ( zero_lt_one.trans_le hq ) ];
  -- For Cauchy, specialize Finset.sum_mul_sq_le_sq_mul_sq univ (fun _ => 1) (fun i => (m i:ℝ)), simplify to M²≤q*S₂.
  have h_cauchy : (G.M : ℝ) ^ 2 ≤ (G.q : ℝ) * (G.S₂ : ℝ) := by
    have := Finset.sum_mul_sq_le_sq_mul_sq ( Finset.univ : Finset ( Fin G.q ) ) ( fun _ => 1 ) ( fun i => ( G.m i : ℝ ) );
    convert this using 1 <;> norm_num [ SplitGraph.M, SplitGraph.S₂ ];
  -- Since $q>0$, combine with sq_nonneg (2*M-q*(s-1)) to show ((s-1)M-S₂)/q ≤ (s-1)^2/4.
  have h_final : ((G.s - 1) * (G.M : ℝ) - (G.S₂ : ℝ)) / (G.q : ℝ) ≤ ((G.s - 1) ^ 2 : ℝ) / 4 := by
    rw [ div_le_iff₀ ] <;> nlinarith [ sq_nonneg ( 2 * ( G.M : ℝ ) - ( G.q : ℝ ) * ( G.s - 1 ) ), show ( G.q : ℝ ) ≥ 1 by norm_cast ];
  grind +locals

private lemma sum_embedding_one_point
    {A : Type*} [Fintype A] [DecidableEq A] (q : ℕ)
    (hq : Fintype.card A ≤ q) (x : A) (g : Fin q → ℝ) :
    ∑ σ : A ↪ Fin q, g (σ x) =
      (Fintype.card (A ↪ Fin q) : ℝ) / q * ∑ i, g i := by
  have h_fiber_pigeonhole : ∀ i : Fin q, ∑ σ : A ↪ Fin q, (if σ x = i then 1 else 0 : ℝ) = (Fintype.card (A ↪ Fin q) : ℝ) / q := by
    intro i
    have h_sum_const : ∀ i j : Fin q, ∑ σ : A ↪ Fin q, (if σ x = i then 1 else 0 : ℝ) = ∑ σ : A ↪ Fin q, (if σ x = j then 1 else 0 : ℝ) := by
      intro i j
      have h_bij : Finset.card (Finset.filter (fun σ : A ↪ Fin q => σ x = i) Finset.univ) = Finset.card (Finset.filter (fun σ : A ↪ Fin q => σ x = j) Finset.univ) := by
        refine' Finset.card_bij ( fun σ _ => ⟨ fun y => if σ y = i then j else if σ y = j then i else σ y, _ ⟩ ) _ _ _ <;> simp +decide [ Function.Injective ];
        grind +splitImp;
        · tauto;
        · intro a₁ ha₁ a₂ ha₂ h; ext y; replace h := congr_fun h y; aesop;
        · intro b hb; use ⟨ fun y => if b y = i then j else if b y = j then i else b y, by
            intro y z h; have := b.injective; aesop; ⟩ ; aesop;
      simp_all +decide [ Finset.sum_ite ];
    have h_sum_const : ∑ i : Fin q, ∑ σ : A ↪ Fin q, (if σ x = i then 1 else 0 : ℝ) = (Fintype.card (A ↪ Fin q) : ℝ) := by
      rw [ Finset.sum_comm ] ; aesop;
    rw [ ← h_sum_const, Finset.sum_congr rfl fun j _ => ‹∀ i j : Fin q, ( ∑ σ : A ↪ Fin q, if σ x = i then 1 else 0 : ℝ ) = ∑ σ : A ↪ Fin q, if σ x = j then 1 else 0› j i ] ; norm_num [ mul_div_cancel₀, show q ≠ 0 by linarith [ Fin.is_lt i ] ];
  convert Finset.sum_congr rfl fun i _ => congr_arg ( fun x : ℝ => x * g i ) ( h_fiber_pigeonhole i ) using 1;
  any_goals exact Finset.univ;
  · simp +decide only [Finset.sum_mul _ _ _];
    rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop;
  · rw [ Finset.mul_sum _ _ _ ]

private lemma sum_embedding_two_point
    {A : Type*} [Fintype A] [DecidableEq A] (q : ℕ)
    (hq2 : 2 ≤ q) (hq : Fintype.card A ≤ q) {x y : A} (hxy : x ≠ y)
    (g : Fin q → Fin q → ℝ) :
    ∑ σ : A ↪ Fin q, g (σ x) (σ y) =
      (Fintype.card (A ↪ Fin q) : ℝ) / ((q : ℝ) * (q - 1)) *
        ∑ i, ∑ j, if i = j then 0 else g i j := by
  revert x y hxy;
  intro x y hxy
  have h_fibers : ∀ (i j : Fin q), i ≠ j → ∑ σ : A ↪ Fin q, (if σ x = i ∧ σ y = j then 1 else 0) = (Fintype.card (A ↪ Fin q) : ℝ) / (q * (q - 1)) := by
    intro i j hij
    have h_fibers : ∀ (i j : Fin q), i ≠ j → Finset.card (Finset.filter (fun σ : A ↪ Fin q => σ x = i ∧ σ y = j) Finset.univ) = Finset.card (Finset.filter (fun σ : A ↪ Fin q => σ x = ⟨0, by linarith⟩ ∧ σ y = ⟨1, by linarith⟩) Finset.univ) := by
      intro i j hij
      obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin q), σ i = ⟨0, by linarith⟩ ∧ σ j = ⟨1, by linarith⟩ := by
        -- Since $i \neq j$, we can construct a permutation $\sigma$ that swaps $i$ and $0$, and $j$ and $1$.
        obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin q), σ i = ⟨0, by linarith⟩ := by
          exact ⟨ Equiv.swap i ⟨ 0, by linarith ⟩, by simp +decide ⟩;
        use σ * Equiv.swap j (σ⁻¹ ⟨1, by linarith⟩);
        simp +decide [ *, Equiv.swap_apply_def ];
        split_ifs <;> simp_all +decide [ Equiv.symm_apply_eq ];
      have hσ1 : σ.symm ⟨0, by linarith⟩ = i := (Equiv.symm_apply_eq σ).2 hσ.1.symm
      have hσ2 : σ.symm ⟨1, by linarith⟩ = j := (Equiv.symm_apply_eq σ).2 hσ.2.symm
      refine Finset.card_bij' (fun τ _ => τ.trans σ.toEmbedding)
        (fun τ _ => τ.trans σ.symm.toEmbedding) ?_ ?_ ?_ ?_
      · intro τ hτ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
        simp [hτ.1, hτ.2, hσ.1, hσ.2]
      · intro τ hτ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
        simp [hτ.1, hτ.2, hσ1, hσ2]
      · intro τ _
        ext a
        simp
      · intro τ _
        ext a
        simp
    have h_fibers_sum : ∑ i : Fin q, ∑ j : Fin q, (if i ≠ j then Finset.card (Finset.filter (fun σ : A ↪ Fin q => σ x = i ∧ σ y = j) Finset.univ) else 0) = Fintype.card (A ↪ Fin q) := by
      rw [ ← Finset.sum_product' ];
      rw [ ← Finset.sum_filter ];
      rw [ ← Finset.card_biUnion ];
      · convert Finset.card_univ using 2;
        ext σ; simp [Finset.mem_biUnion];
        exact hxy;
      · exact fun a ha b hb hab => Finset.disjoint_left.mpr fun σ hσ₁ hσ₂ => hab <| by aesop;
    simp_all +decide [ Finset.sum_ite ];
    rw [ ← h_fibers_sum, eq_div_iff ] <;> norm_cast;
    · simp +decide [ Finset.filter_ne, Finset.filter_and, Finset.card_sdiff, Finset.card_singleton, Finset.card_univ, Int.subNatNat_eq_coe ];
      rw [ Nat.cast_pred ] <;> linarith;
    · rw [ Int.subNatNat_eq_coe ] ; push_cast ; nlinarith;
  have h_sum_fibers : ∑ σ : A ↪ Fin q, g (σ x) (σ y) = ∑ i : Fin q, ∑ j : Fin q, (∑ σ : A ↪ Fin q, (if σ x = i ∧ σ y = j then 1 else 0)) * g i j := by
    have h_sum_fibers : ∑ σ : A ↪ Fin q, g (σ x) (σ y) = ∑ σ : A ↪ Fin q, ∑ i : Fin q, ∑ j : Fin q, (if σ x = i ∧ σ y = j then g i j else 0) := by
      refine' Finset.sum_congr rfl fun σ _ => _;
      rw [ Finset.sum_eq_single ( σ x ) ] <;> simp +contextual [ Finset.sum_ite ];
      exact fun i hi => Finset.sum_eq_zero fun j hj => False.elim <| hi <| by aesop;
    rw [ h_sum_fibers, Finset.sum_comm ];
    simp +decide only [Finset.sum_mul _ _ _];
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by split_ifs <;> ring );
  rw [ h_sum_fibers, Finset.mul_sum _ _ _ ];
  refine' Finset.sum_congr rfl fun i hi => _;
  rw [ Finset.mul_sum _ _ _, Finset.sum_congr rfl ];
  intro j hj; by_cases hij : i = j <;> simp +decide [ hij, h_fibers ] ;
  exact Or.inl fun σ hσ₁ hσ₂ => hxy <| σ.injective <| hσ₁.trans hσ₂.symm

private lemma exists_rescue_assignment
    (r q h : ℕ) (f : Fin r → Fin q → ℝ)
    (hf : ∀ c i, f c i = 0 ∨ f c i = 1)
    (hh : h ≤ r) (hrq : r + h ≤ q) (hq2 : 2 ≤ q) :
    ∃ τ : Fin h ↪ Fin r, ∃ σ : (Fin r ⊕ Fin h) ↪ Fin q,
      (1 / (q : ℝ)) * ∑ c, ∑ i, f c i
        + (h : ℝ) / (r : ℝ) / ((q : ℝ) * ((q : ℝ) - 1)) *
          ∑ c, (∑ i, (1 - f c i)) * (∑ i, f c i)
      ≤ ∑ c, f c (σ (Sum.inl c))
          + ∑ k, (1 - f (τ k) (σ (Sum.inl (τ k)))) *
              f (τ k) (σ (Sum.inr k)) := by
  by_contra! h_contra;
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ τ : Fin h ↪ Fin r, ∑ σ : (Fin r ⊕ Fin h) ↪ Fin q, (∑ c, f c (σ (Sum.inl c)) + ∑ k, (1 - f (τ k) (σ (Sum.inl (τ k)))) * f (τ k) (σ (Sum.inr k))) = (Nat.card (Fin h ↪ Fin r) * Nat.card ((Fin r ⊕ Fin h) ↪ Fin q) : ℝ) * ((1 / q : ℝ) * ∑ c, ∑ i, f c i + h / r / (q * (q - 1)) * ∑ c, (∑ i, (1 - f c i)) * ∑ i, f c i) := by
    have h_fubini : ∑ τ : Fin h ↪ Fin r, ∑ σ : (Fin r ⊕ Fin h) ↪ Fin q, (∑ c, f c (σ (Sum.inl c))) = (Nat.card (Fin h ↪ Fin r) * Nat.card ((Fin r ⊕ Fin h) ↪ Fin q) : ℝ) * ((1 / q : ℝ) * ∑ c, ∑ i, f c i) := by
      have h_fubini : ∀ c : Fin r, ∑ τ : Fin h ↪ Fin r, ∑ σ : (Fin r ⊕ Fin h) ↪ Fin q, f c (σ (Sum.inl c)) = (Nat.card (Fin h ↪ Fin r) * Nat.card ((Fin r ⊕ Fin h) ↪ Fin q) : ℝ) * ((1 / q : ℝ) * ∑ i, f c i) := by
        intro c
        have h_fubini_step : ∑ σ : (Fin r ⊕ Fin h) ↪ Fin q, f c (σ (Sum.inl c)) = (Nat.card ((Fin r ⊕ Fin h) ↪ Fin q) : ℝ) * ((1 / q : ℝ) * ∑ i, f c i) := by
          convert sum_embedding_one_point q _ ( Sum.inl c ) ( fun i => f c i ) using 1;
          · rw [ Nat.card_eq_fintype_card ] ; ring;
          · infer_instance;
          · simp +arith +decide [ hrq ];
        simp_all +decide [ mul_assoc ];
      convert Finset.sum_congr rfl fun c _ => h_fubini c using 1;
      any_goals exact Finset.univ;
      · exact Eq.symm ( by rw [ Finset.sum_comm ] ; exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm );
      · rw [ ← Finset.mul_sum _ _ _, ← Finset.mul_sum _ _ _ ];
    have h_fubini_rescue : ∀ k : Fin h, ∑ τ : Fin h ↪ Fin r, ∑ σ : (Fin r ⊕ Fin h) ↪ Fin q, (1 - f (τ k) (σ (Sum.inl (τ k)))) * f (τ k) (σ (Sum.inr k)) = (Nat.card (Fin h ↪ Fin r) * Nat.card ((Fin r ⊕ Fin h) ↪ Fin q) : ℝ) * ((1 / r : ℝ) * (1 / (q * (q - 1) : ℝ)) * ∑ c, (∑ i, (1 - f c i)) * ∑ i, f c i) := by
      intro k
      have h_fubini_rescue_step : ∀ τ : Fin h ↪ Fin r, ∑ σ : (Fin r ⊕ Fin h) ↪ Fin q, (1 - f (τ k) (σ (Sum.inl (τ k)))) * f (τ k) (σ (Sum.inr k)) = (Nat.card ((Fin r ⊕ Fin h) ↪ Fin q) : ℝ) * ((1 / (q * (q - 1) : ℝ)) * (∑ i, (1 - f (τ k) i)) * (∑ i, f (τ k) i)) := by
        intro τ
        have h_fubini_rescue_step : ∑ σ : (Fin r ⊕ Fin h) ↪ Fin q, (1 - f (τ k) (σ (Sum.inl (τ k)))) * f (τ k) (σ (Sum.inr k)) = (Nat.card ((Fin r ⊕ Fin h) ↪ Fin q) : ℝ) * ((1 / (q * (q - 1) : ℝ)) * (∑ i, (1 - f (τ k) i)) * (∑ i, f (τ k) i)) := by
          have := sum_embedding_two_point q hq2 (by
          simp +arith +decide [ * ] : Fintype.card (Fin r ⊕ Fin h) ≤ q) (by
          grind : (Sum.inl (τ k) : Fin r ⊕ Fin h) ≠ Sum.inr k) (fun i j => (1 - f (τ k) i) * f (τ k) j)
          convert this using 1;
          simp +decide [ Finset.sum_ite, Finset.filter_ne ];
          simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, sub_mul, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Nat.descFactorial_eq_factorial_mul_choose ] ; ring;
          rw [ show ( ∑ x : Fin q, f ( τ k ) x ^ 2 ) = ∑ x : Fin q, f ( τ k ) x from Finset.sum_congr rfl fun _ _ => by cases hf ( τ k ) ‹_› <;> simp +decide [ * ] ] ; ring;
          grind;
        convert h_fubini_rescue_step using 1;
      simp +decide only [h_fubini_rescue_step];
      have h_fubini_rescue_step : ∑ τ : Fin h ↪ Fin r, (∑ i, (1 - f (τ k) i)) * (∑ i, f (τ k) i) = (Nat.card (Fin h ↪ Fin r) : ℝ) * ((1 / r : ℝ) * ∑ c, (∑ i, (1 - f c i)) * ∑ i, f c i) := by
        convert sum_embedding_one_point r ( by simpa using hh ) k ( fun c => ( ∑ i, ( 1 - f c i ) ) * ∑ i, f c i ) using 1;
        rw [ Nat.card_eq_fintype_card ] ; ring;
      convert congr_arg ( fun x : ℝ => ( Nat.card ( Fin r ⊕ Fin h ↪ Fin q ) : ℝ ) * ( 1 / ( q * ( q - 1 ) : ℝ ) ) * x ) h_fubini_rescue_step using 1 <;> ring;
      simp +decide only [sum_mul, Finset.mul_sum _ _ _];
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring;
    convert congr_arg₂ ( · + · ) h_fubini ( Finset.sum_congr rfl fun k ( hk : k ∈ Finset.univ ) => h_fubini_rescue k ) using 1;
    · simp +decide only [sum_add_distrib, sum_sigma'];
      refine' congr rfl ( Finset.sum_bij ( fun x _ => ⟨ x.snd.snd, x.fst, x.snd.fst ⟩ ) _ _ _ _ ) <;> simp +decide;
      bound;
    · norm_num [ div_eq_mul_inv, mul_add, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
  contrapose! h_fubini;
  refine' ne_of_lt ( lt_of_lt_of_le ( Finset.sum_lt_sum_of_nonempty _ fun τ _ => Finset.sum_lt_sum_of_nonempty _ fun σ _ => h_contra τ σ ) _ );
  · rcases r with ( _ | r ) <;> rcases h with ( _ | h ) <;> norm_num at *;
    refine' ⟨ ⟨ fun i => ⟨ i, by linarith [ Fin.is_lt i ] ⟩, fun i j hij => _ ⟩, Finset.mem_univ _ ⟩ ; aesop;
  · refine' ⟨ _, Finset.mem_univ _ ⟩;
    refine' ⟨ fun x => x.elim ( fun x => ⟨ x.val, by linarith [ Fin.is_lt x ] ⟩ ) fun x => ⟨ r + x.val, by linarith [ Fin.is_lt x ] ⟩, fun x y hxy => _ ⟩;
    rcases x with ( x | x ) <;> rcases y with ( y | y ) <;> norm_num at hxy ⊢ <;> omega;
  · norm_num [ Nat.card_eq_fintype_card ];
    linarith

private lemma exists_rescue_assignment_edgewise
    {E : Type*} [Fintype E] [DecidableEq E]
    (r q h : ℕ) (f : Fin r → E → Fin q → ℝ)
    (hf : ∀ c e i, f c e i = 0 ∨ f c e i = 1)
    (hh : h ≤ r) (hrq : r + h ≤ q) (hq2 : 2 ≤ q) :
    ∃ τ : Fin h ↪ Fin r, ∃ σ : (Fin r ⊕ Fin h) ↪ Fin q,
      (1 / (q : ℝ)) * ∑ c, ∑ e, ∑ i, f c e i
        + (h : ℝ) / (r : ℝ) / ((q : ℝ) * ((q : ℝ) - 1)) *
          ∑ c, ∑ e, (∑ i, (1 - f c e i)) * (∑ i, f c e i)
      ≤ ∑ c, ∑ e, f c e (σ (Sum.inl c))
          + ∑ k, ∑ e, (1 - f (τ k) e (σ (Sum.inl (τ k)))) *
              f (τ k) e (σ (Sum.inr k)) := by
  by_contra! h_contra;
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∀ (τ : Fin h ↪ Fin r) (σ : (Fin r ⊕ Fin h) ↪ Fin q), (∑ c, (∑ e, f c e (σ (Sum.inl c)))
    + ∑ k, (∑ e, (1 - f (τ k) e (σ (Sum.inl (τ k)))) * f (τ k) e (σ (Sum.inr k))))
    = (∑ e, (∑ c, f c e (σ (Sum.inl c))
    + ∑ k, (1 - f (τ k) e (σ (Sum.inl (τ k)))) * f (τ k) e (σ (Sum.inr k)))) := by
      simp +decide only [sum_add_distrib];
      exact fun τ σ => congr_arg₂ ( · + · ) ( Finset.sum_comm ) ( Finset.sum_comm );
  have h_fubini_sum : ∀ (τ : Fin h ↪ Fin r), ∑ σ : (Fin r ⊕ Fin h) ↪ Fin q, (∑ e, (∑ c, f c e (σ (Sum.inl c))
    + ∑ k, (1 - f (τ k) e (σ (Sum.inl (τ k)))) * f (τ k) e (σ (Sum.inr k))))
    = ∑ e, (Fintype.card (Fin r ⊕ Fin h ↪ Fin q) : ℝ) / q * (∑ c, ∑ i, f c e i)
    + ∑ e, ∑ k, (Fintype.card (Fin r ⊕ Fin h ↪ Fin q) : ℝ) / ((q : ℝ) * (q - 1)) * (∑ i, (1 - f (τ k) e i)) * (∑ i, f (τ k) e i) := by
      intro τ
      have h_sum_embedding : ∀ (e : E), ∑ σ : (Fin r ⊕ Fin h) ↪ Fin q, (∑ c, f c e (σ (Sum.inl c))
        + ∑ k, (1 - f (τ k) e (σ (Sum.inl (τ k)))) * f (τ k) e (σ (Sum.inr k)))
        = (Fintype.card (Fin r ⊕ Fin h ↪ Fin q) : ℝ) / q * (∑ c, ∑ i, f c e i)
        + ∑ k, (Fintype.card (Fin r ⊕ Fin h ↪ Fin q) : ℝ) / ((q : ℝ) * (q - 1)) * (∑ i, (1 - f (τ k) e i)) * (∑ i, f (τ k) e i) := by
          intro e
          have h_sum_embedding : ∑ σ : (Fin r ⊕ Fin h) ↪ Fin q, (∑ c, f c e (σ (Sum.inl c))) = (Fintype.card (Fin r ⊕ Fin h ↪ Fin q) : ℝ) / q * (∑ c, ∑ i, f c e i) := by
            have h_sum_embedding : ∀ (c : Fin r), ∑ σ : (Fin r ⊕ Fin h) ↪ Fin q, f c e (σ (Sum.inl c)) = (Fintype.card (Fin r ⊕ Fin h ↪ Fin q) : ℝ) / q * (∑ i, f c e i) := by
              intro c;
              convert sum_embedding_one_point q _ _ _ using 1;
              · infer_instance;
              · simp +decide [ Fintype.card_sum ] ; linarith;
            rw [ Finset.sum_comm, Finset.mul_sum _ _ _, Finset.sum_congr rfl fun _ _ => h_sum_embedding _ ];
          have h_sum_embedding_rescue : ∀ k : Fin h, ∑ σ : (Fin r ⊕ Fin h) ↪ Fin q, (1 - f (τ k) e (σ (Sum.inl (τ k)))) * f (τ k) e (σ (Sum.inr k)) = (Fintype.card (Fin r ⊕ Fin h ↪ Fin q) : ℝ) / ((q : ℝ) * (q - 1)) * (∑ i, (1 - f (τ k) e i)) * (∑ i, f (τ k) e i) := by
            intro k;
            have := sum_embedding_two_point q hq2 ( show Fintype.card ( Fin r ⊕ Fin h ) ≤ q from by simpa using by linarith ) ( show Sum.inl ( τ k ) ≠ Sum.inr k from by simp +decide ) ( fun i j => ( 1 - f ( τ k ) e i ) * f ( τ k ) e j );
            convert this using 1;
            simp +decide [ Finset.sum_ite, Finset.filter_ne, Finset.mul_sum _ _ _, Finset.sum_mul ];
            simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, sub_mul, mul_sub ];
            rw [ show ∑ x : Fin q, f ( τ k ) e x * f ( τ k ) e x = ∑ x : Fin q, f ( τ k ) e x from Finset.sum_congr rfl fun _ _ => by cases hf ( τ k ) e ‹_› <;> simp +decide [ * ] ] ; ring;
          simp +decide only [sum_add_distrib, ← h_sum_embedding, ← h_sum_embedding_rescue];
          exact congrArg₂ ( · + · ) rfl ( Finset.sum_comm );
      rw [ Finset.sum_comm, Finset.sum_congr rfl fun e _ => h_sum_embedding e, Finset.sum_add_distrib ];
  obtain ⟨τ, hτ⟩ : ∃ τ : Fin h ↪ Fin r, ∑ k, ∑ e, (∑ i, (1 - f (τ k) e i)) * (∑ i, f (τ k) e i) ≥ (h : ℝ) / r * ∑ c, ∑ e, (∑ i, (1 - f c e i)) * (∑ i, f c e i) := by
    have h_fubini_sum : ∑ τ : Fin h ↪ Fin r, ∑ k, ∑ e, (∑ i, (1 - f (τ k) e i)) * (∑ i, f (τ k) e i) = (Fintype.card (Fin h ↪ Fin r) : ℝ) * (h : ℝ) / r * ∑ c, ∑ e, (∑ i, (1 - f c e i)) * (∑ i, f c e i) := by
      have h_fubini_sum : ∀ (e : E), ∑ τ : Fin h ↪ Fin r, ∑ k, (∑ i, (1 - f (τ k) e i)) * (∑ i, f (τ k) e i) = (Fintype.card (Fin h ↪ Fin r) : ℝ) * (h : ℝ) / r * ∑ c, (∑ i, (1 - f c e i)) * (∑ i, f c e i) := by
        intro e
        have h_fubini_sum : ∀ (k : Fin h), ∑ τ : Fin h ↪ Fin r, (∑ i, (1 - f (τ k) e i)) * (∑ i, f (τ k) e i) = (Fintype.card (Fin h ↪ Fin r) : ℝ) / r * ∑ c, (∑ i, (1 - f c e i)) * (∑ i, f c e i) := by
          intro k;
          have := @sum_embedding_one_point ( Fin h );
          convert this r ( by simpa using hh ) k ( fun c => ( ∑ i, ( 1 - f c e i ) ) * ∑ i, f c e i ) using 1;
        rw [ Finset.sum_comm, Finset.sum_congr rfl fun _ _ => h_fubini_sum _ ] ; simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
      convert Finset.sum_congr rfl fun e _ => h_fubini_sum e using 1;
      any_goals exact Finset.univ;
      · rw [ Finset.sum_comm, Finset.sum_congr rfl fun _ _ => Finset.sum_comm ];
        exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm );
      · rw [ ← Finset.mul_sum _ _ _, Finset.sum_comm ];
    contrapose! h_fubini_sum;
    refine' ne_of_lt ( lt_of_lt_of_le ( Finset.sum_lt_sum_of_nonempty _ fun τ _ => h_fubini_sum τ ) _ );
    · exact ⟨ ⟨ fun i => ⟨ i, by linarith [ Fin.is_lt i ] ⟩, fun i j hij => by simpa [ Fin.ext_iff ] using hij ⟩, Finset.mem_univ _ ⟩;
    · simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
  have h_fubini_sum : ∑ σ : (Fin r ⊕ Fin h) ↪ Fin q, (∑ e, (∑ c, f c e (σ (Sum.inl c))
      + ∑ k, (1 - f (τ k) e (σ (Sum.inl (τ k)))) * f (τ k) e (σ (Sum.inr k)))) ≥
      (Fintype.card (Fin r ⊕ Fin h ↪ Fin q) : ℝ) * ((1 / q : ℝ) * ∑ c, ∑ e, ∑ i, f c e i
      + (h : ℝ) / r / ((q : ℝ) * (q - 1)) * ∑ c, ∑ e, (∑ i, (1 - f c e i)) * (∑ i, f c e i)) := by
        rw [ h_fubini_sum τ ];
        simp +decide only [mul_add];
        refine' add_le_add _ _;
        · simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ];
          exact Finset.sum_comm.le;
        · convert mul_le_mul_of_nonneg_left hτ ( show ( 0 : ℝ ) ≤ ( Fintype.card ( Fin r ⊕ Fin h ↪ Fin q ) : ℝ ) / ( q * ( q - 1 ) ) by exact div_nonneg ( Nat.cast_nonneg _ ) ( mul_nonneg ( Nat.cast_nonneg _ ) ( sub_nonneg.mpr ( Nat.one_le_cast.mpr ( by linarith ) ) ) ) ) using 1;
          · ring;
          · simp +decide only [Finset.mul_sum _ _ _];
            simp +decide only [sum_mul, Finset.mul_sum _ _ _];
            exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
  contrapose! h_fubini_sum;
  convert Finset.sum_lt_sum_of_nonempty _ fun σ _ => h_contra τ σ using 1;
  any_goals exact Finset.univ;
  · exact Finset.sum_congr rfl fun _ _ => h_fubini τ _ ▸ rfl;
  · simp +decide [ mul_add, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_add_distrib ];
  · refine' ⟨ _, Finset.mem_univ _ ⟩;
    refine' ⟨ fun x => x.elim ( fun x => ⟨ x.val, by linarith [ Fin.is_lt x ] ⟩ ) fun x => ⟨ r + x.val, by linarith [ Fin.is_lt x ] ⟩, fun x y hxy => _ ⟩;
    rcases x with ( x | x ) <;> rcases y with ( y | y ) <;> norm_num at hxy ⊢ <;> omega

private def rescueTriangles (G : SplitGraph) (φ : Sym2 (Fin G.p) → ℕ)
    (τ : Fin G.doubledFactors ↪ Fin (rp G.p))
    (σ : (Fin (rp G.p) ⊕ Fin G.doubledFactors) ↪ Fin G.q) :
    Finset (Finset G.V) :=
  (Finset.univ.biUnion fun c : Fin (rp G.p) =>
    (factorEdges G φ c (σ (Sum.inl c))).image
      (kkiTriangle G (σ (Sum.inl c)))) ∪
  (Finset.univ.biUnion fun k : Fin G.doubledFactors =>
    ((factorEdges G φ (τ k) (σ (Sum.inr k))).filter fun e =>
      ¬ ∀ v ∈ e, v ∈ G.N (σ (Sum.inl (τ k)))).image
      (kkiTriangle G (σ (Sum.inr k))))

private lemma rescueTriangles_isPacking (G : SplitGraph)
    (φ : Sym2 (Fin G.p) → ℕ)
    (hproper : ∀ e ∈ (⊤ : SimpleGraph (Fin G.p)).edgeFinset,
      ∀ f ∈ (⊤ : SimpleGraph (Fin G.p)).edgeFinset,
        e ≠ f → (∃ v, v ∈ e ∧ v ∈ f) → φ e ≠ φ f)
    (τ : Fin G.doubledFactors ↪ Fin (rp G.p))
    (σ : (Fin (rp G.p) ⊕ Fin G.doubledFactors) ↪ Fin G.q) :
    IsTrianglePacking G.graph (rescueTriangles G φ τ σ) := by
  constructor;
  · unfold rescueTriangles; simp +decide [ IsTrianglePacking ] ;
    rintro t ( ⟨ a, b, hb, rfl ⟩ | ⟨ a, b, ⟨ hb, x, hx, hx' ⟩, rfl ⟩ ) <;> simp_all +decide [ kkiTriangle, factorEdges ];
    · constructor;
      · intro x hx y hy; simp_all +decide [ SplitGraph.graph ] ;
        rcases hx with ( rfl | ⟨ x, hx, rfl ⟩ ) <;> rcases hy with ( rfl | ⟨ y, hy, rfl ⟩ ) <;> simp_all +decide [ SplitGraph.Adj ];
      · rw [ Finset.card_insert_of_notMem ] <;> simp +decide [ hb ];
        rw [ Finset.card_image_of_injective _ Sum.inl_injective, Sym2.card_toFinset ] ; aesop;
    · rcases b with ⟨ a, b ⟩ ; simp_all +decide [ SimpleGraph.isNClique_iff ];
      simp_all +decide [ SimpleGraph.IsClique, Finset.card_image_of_injective, Function.Injective, SplitGraph.graph ];
      simp_all +decide [ Set.Pairwise, SplitGraph.Adj ];
      simp_all +decide [ Sym2.toFinset ];
      simp_all +decide [ Sym2.toMultiset ];
      grind;
  · intro t₁ ht₁ t₂ ht₂ hne; simp_all +decide [ Finset.subset_iff ] ;
    unfold rescueTriangles at ht₁ ht₂; simp_all +decide [ Finset.mem_biUnion ] ;
    rcases ht₁ with ( ⟨ a, b, hb, rfl ⟩ | ⟨ a, b, ⟨ hb, x, hx, hx' ⟩, rfl ⟩ ) <;> rcases ht₂ with ( ⟨ c, d, hd, rfl ⟩ | ⟨ c, d, ⟨ hd, y, hy, hy' ⟩, rfl ⟩ ) <;> simp_all +decide [ kkiTriangle ];
    · by_cases hac : a = c <;> simp_all +decide [ Finset.ext_iff ];
      · unfold factorEdges at hb hd; simp_all +decide [ Finset.mem_filter ] ;
        grind;
      · by_cases h : b = d <;> simp_all +decide [ Finset.ext_iff, Sym2.forall ];
        · unfold factorEdges at hb hd; simp_all +decide [ Finset.mem_filter ] ;
          exact False.elim <| hac <| Fin.ext hd.1;
        · rcases b with ⟨ x, y ⟩ ; rcases d with ⟨ u, v ⟩ ; simp_all +decide [ Finset.card_le_one ];
          grind;
    · by_cases h : b = d <;> simp_all +decide [ Finset.ext_iff, Sym2.forall ];
      · grind +locals;
      · rcases b with ⟨ x, y ⟩ ; rcases d with ⟨ u, v ⟩ ; simp_all +decide [ Finset.card_le_one ];
        grind;
    · by_cases h : b = d <;> simp_all +decide [ Finset.ext_iff, Sym2.forall ];
      · unfold factorEdges at hb hd; simp_all +decide [ Finset.mem_filter ] ;
        grind;
      · rcases b with ⟨ ⟨ a, b ⟩ ⟩ ; rcases d with ⟨ ⟨ c, d ⟩ ⟩ ; simp_all +decide [ Finset.card_le_one ] ;
        grind;
    · by_cases hac : a = c <;> simp_all +decide [ Finset.ext_iff ];
      · unfold factorEdges at hb hd; simp_all +decide [ Finset.mem_filter ] ;
        grind;
      · have h_inter : b ≠ d := by
          contrapose! hac; simp_all +decide [ factorEdges ] ;
          exact τ.injective ( Fin.ext hd.1 );
        rcases b with ⟨ a, b ⟩ ; rcases d with ⟨ c, d ⟩ ; simp_all +decide [ Sym2.eq_swap ] ;
        simp +decide [ Sym2.toFinset, Finset.card_le_one ];
        grind

private lemma card_rescueTriangles (G : SplitGraph)
    (φ : Sym2 (Fin G.p) → ℕ)
    (τ : Fin G.doubledFactors ↪ Fin (rp G.p))
    (σ : (Fin (rp G.p) ⊕ Fin G.doubledFactors) ↪ Fin G.q) :
    (rescueTriangles G φ τ σ).card =
      ∑ c, (factorEdges G φ c (σ (Sum.inl c))).card +
      ∑ k, ((factorEdges G φ (τ k) (σ (Sum.inr k))).filter fun e =>
        ¬ ∀ v ∈ e, v ∈ G.N (σ (Sum.inl (τ k)))).card := by
  rw [ rescueTriangles, Finset.card_union_of_disjoint ];
  · rw [ Finset.card_biUnion, Finset.card_biUnion ];
    · congr! 2;
      · rw [ Finset.card_image_of_injOn ];
        intro e he f hf; simp_all +decide [ kkiTriangle ] ;
        simp_all +decide [ Finset.ext_iff, Set.ext_iff ];
        exact fun h => by ext a; specialize h a; aesop;
      · rw [ Finset.card_image_of_injOn ];
        intro e he f hf; simp_all +decide [ kkiTriangle ] ;
        intro h; replace h := Finset.ext_iff.mp h; have := h ( Sum.inr ( σ ( Sum.inr ‹_› ) ) ) ; simp_all +decide ;
        ext a; specialize h a; aesop;
    · intros k hk l hl hkl;
      simp +decide [ Finset.disjoint_left, kkiTriangle ];
      rintro a x hx y hy hy' rfl z hz w hw hw';
      intro H; replace H := Finset.ext_iff.mp H ( Sum.inr ( σ ( Sum.inr l ) ) ) ; simp_all +decide ;
    · intro c hc d hd hcd; simp_all +decide [ Finset.disjoint_left, kkiTriangle ] ;
      intro a ha x hx; intro H; replace H := Finset.ext_iff.mp H ( Sum.inr ( σ ( Sum.inl d ) ) ) ; simp_all +decide ;
  · simp +decide [ Finset.disjoint_left ];
    rintro _ c e he rfl k f hf g hg hg';
    unfold kkiTriangle; simp +decide [ Finset.ext_iff ] ;

private lemma diagSet_toFinset_compl {α : Type*} [Fintype α] [DecidableEq α]
    [Fintype ↑(Sym2.diagSet (α := α))] :
    (Sym2.diagSet (α := α)).toFinsetᶜ = Finset.univ.filter (fun z : Sym2 α => ¬ z.IsDiag) := by
  ext z
  simp [Set.mem_toFinset]

private lemma exists_double_factor_packing (G : SplitGraph)
    (hrp : rp G.p ≤ G.q) (hq2 : 2 ≤ G.q) :
    ∃ T : Finset (Finset G.V), IsTrianglePacking G.graph T ∧
      (1 / (G.q : ℝ)) * ∑ i, ((G.d i).choose 2 : ℝ)
        + ((G.doubledFactors : ℝ) / (rp G.p : ℝ)) * (G.dispersionV : ℝ)
          / ((G.q : ℝ) * ((G.q : ℝ) - 1)) ≤ (T.card : ℝ) := by
  obtain ⟨ φ, hbound, hproper ⟩ := complete_graph_edge_coloring G.p;
  obtain ⟨ τ, σ, h ⟩ := exists_rescue_assignment_edgewise ( rp G.p ) G.q G.doubledFactors ( fun c e i => if e ∈ ( ⊤ : SimpleGraph ( Fin G.p ) ).edgeFinset ∧ φ e = c ∧ ∀ v ∈ e, v ∈ G.N i then 1 else 0 ) ( by
    lia ) ( by
    exact min_le_left _ _ ) ( by
    unfold SplitGraph.doubledFactors; omega; ) ( by
    linarith );
  refine' ⟨ rescueTriangles G φ τ σ, rescueTriangles_isPacking G φ hproper τ σ, _ ⟩;
  convert h using 1;
  · congr! 1;
    · rw [ Finset.sum_comm ];
      congr! 2;
      convert Finset.sum_congr rfl fun i hi => sum_factorEdges_card G φ hbound i using 1;
      norm_cast;
      rw [ eq_comm ];
      rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; rw [ Finset.sum_comm ] ;
      intro c hc; rw [ Finset.sum_comm ] ; congr; ext e; simp +decide [ factorEdges ] ;
      congr! 1;
      ext; simp [Set.mem_toFinset, Sym2.mem_diagSet];
    · rw [ Finset.sum_comm ];
      rw [ Finset.sum_congr rfl fun e he => ?_ ];
      rotate_left;
      use fun e => if e ∈ ( ⊤ : SimpleGraph ( Fin G.p ) ).edgeFinset then ( G.q - G.badCount e ) * G.badCount e else 0;
      · by_cases he' : e ∈ ( ⊤ : SimpleGraph ( Fin G.p ) ).edgeFinset <;> simp +decide [ he' ];
        · rw [ Finset.sum_eq_single ⟨ φ e, hbound e he' ⟩ ] <;> simp +contextual [ Fin.ext_iff ];
          · simp +decide [ SplitGraph.badCount ];
            split_ifs <;> simp +decide [ *, Finset.filter_not, Finset.card_sdiff ];
            rw [ show ( Finset.univ.filter fun i => ∀ v ∈ e, v ∈ G.N i ) = Finset.univ \ ( Finset.univ.filter fun i => ∃ x ∈ e, x ∉ G.N i ) by ext; simp +contextual [ Finset.mem_sdiff, Finset.mem_filter ] ] ; simp +decide [ Finset.card_sdiff ] ;
            rw [ Nat.cast_sub ( show _ ≤ _ from le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ) ] ; ring;
          · grind;
        · cases e ; simp +decide [ SimpleGraph.edgeFinset ] at he' ⊢;
          simp +decide [ he' ];
      · rw [ Finset.sum_ite ] ; norm_num;
        rw [ show G.dispersionV = ∑ e ∈ ( ⊤ : SimpleGraph ( Fin G.p ) ).edgeFinset, G.badCount e * ( G.q - G.badCount e ) from rfl ] ; norm_num [ Finset.sum_mul _ _ _ ] ; ring;
        rw [ Finset.sum_congr rfl fun x hx => by rw [ Nat.cast_sub ( show G.badCount x ≤ G.q from le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ) ] ] ; ring;
        simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
        simp +decide [ diagSet_toFinset_compl ];
  · rw [ card_rescueTriangles ];
    simp +decide [ factorEdges ];
    congr! 2;
    · congr! 2;
      ext; simp [Set.mem_toFinset, Sym2.mem_diagSet];
    · simp +decide [ Finset.sum_ite ];
      rw [ eq_sub_iff_add_eq ];
      rw_mod_cast [ ← Finset.card_union_of_disjoint ];
      · congr with x ; by_cases hx : x.IsDiag <;> simp +decide [ hx ];
        grind;
      · simp +contextual [ Finset.disjoint_left ]

lemma double_factor_nu_bound (G : SplitGraph)
    (hrp : rp G.p ≤ G.q) (hq2 : 2 ≤ G.q) :
    (1 / (G.q : ℝ)) * ∑ i, ((G.d i).choose 2 : ℝ)
      + ((G.doubledFactors : ℝ) / (rp G.p : ℝ)) * (G.dispersionV : ℝ)
        / ((G.q : ℝ) * ((G.q : ℝ) - 1)) ≤ (G.nu3' : ℝ) := by
  obtain ⟨T, hT₁, hT₂⟩ := exists_double_factor_packing G hrp hq2
  have hbdd : BddAbove {k : ℕ | ∃ T : Finset (Finset G.V), IsTrianglePacking G.graph T ∧ T.card = k} :=
    ⟨_, fun k hk => by obtain ⟨T, -, rfl⟩ := hk; exact Finset.card_le_univ _⟩
  exact hT₂.trans (Nat.cast_le.mpr (le_csSup hbdd ⟨T, hT₁, rfl⟩))

/-
**E-5.2 (Double-factor inequality)**: if `q ≥ r_p` then, with `δ = h/r_p`,
`Φ(G) ≤ n²/6 + p/2 − s²/6 + ((s−1)M − S₂)/q − 2δV/(q(q−1))` (LEDGER E-5.2).
-/
theorem E_5_2 (G : SplitGraph) (hrp : rp G.p ≤ G.q) (hq2 : 2 ≤ G.q) :
    ((G.Phi : ℤ) : ℝ)
      ≤ (G.n : ℝ) ^ 2 / 6 + (G.p : ℝ) / 2 - (G.s : ℝ) ^ 2 / 6
        + (((G.s : ℝ) - 1) * (G.M : ℝ) - (G.S₂ : ℝ)) / (G.q : ℝ)
        - 2 * ((G.doubledFactors : ℝ) / (rp G.p : ℝ)) * (G.dispersionV : ℝ)
          / ((G.q : ℝ) * ((G.q : ℝ) - 1)) := by
  have := double_factor_nu_bound G hrp hq2;
  unfold PaperIII.SplitGraph.Phi;
  -- By definition of $edgeCount$, we know that
  have h_edgeCount : (G.edgeCount : ℝ) = (G.p : ℝ) * (G.p - 1) / 2 + ∑ i, (G.d i : ℝ) := by
    convert congr_arg ( ( ↑ ) : ℕ → ℝ ) ( edgeCount_eq G ) using 1;
    rw [ Nat.choose_two_right ];
    cases G.p <;> norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.mod_two_of_bodd ];
  -- By definition of $M$ and $S₂$, we know that
  have h_M_S2 : (G.M : ℝ) = G.p * G.q - ∑ i, (G.d i : ℝ) ∧ (G.S₂ : ℝ) = G.p ^ 2 * G.q - 2 * G.p * ∑ i, (G.d i : ℝ) + ∑ i, (G.d i : ℝ) ^ 2 := by
    have h_M_S2 : ∀ i, (G.m i : ℝ) = G.p - (G.d i : ℝ) ∧ (G.m i : ℝ) ^ 2 = G.p ^ 2 - 2 * G.p * (G.d i : ℝ) + (G.d i : ℝ) ^ 2 := by
      intro i
      simp [SplitGraph.m, SplitGraph.d];
      rw [ show G.S i = Finset.univ \ G.N i from rfl, Finset.card_sdiff ] ; norm_num;
      rw [ Nat.cast_sub ( show _ ≤ _ from le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ) ] ; ring ; norm_num;
    simp_all +decide [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, SplitGraph.M, SplitGraph.S₂ ];
    simp +decide [ sub_sq, Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, mul_assoc, mul_comm, mul_left_comm ];
  -- By definition of $choose 2$, we know that
  have h_choose2 : ∑ i, (Nat.choose (G.d i) 2 : ℝ) = (∑ i, (G.d i : ℝ) ^ 2 - ∑ i, (G.d i : ℝ)) / 2 := by
    rw [ ← Finset.sum_sub_distrib, Finset.sum_div ] ; congr ; ext i ; induction G.d i <;> simp +decide [ Nat.choose, * ] ; ring;
  simp_all +decide [ SplitGraph.n, SplitGraph.s ];
  field_simp at *;
  grind

end PaperIII