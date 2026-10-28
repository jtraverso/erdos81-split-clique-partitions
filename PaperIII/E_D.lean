/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Paper III — Appendix D: self-contained list edge coloring (E-D.1, E-D.2, E-D.3)

Encoding: a simple bipartite graph is a `Finset (U × R)` of edges.  Preferences are
injective rank functions (as produced by a proper coloring in Galvin's argument).

* `kernel_coloring` (E-D.1): kernel-perfect digraph, lists of size `d⁺+1` ⟹ proper
  list coloring of the underlying graph.
* `gale_shapley` (E-D.2): stable matchings exist.
* `konig_edge_coloring` (Step 1 of E-D.3): bipartite `Δ`-edge-coloring, proved by
  alternating-path recoloring.
* `galvin_max_degree` (E-D.3): bipartite, `|L(e)| ≥ Δ` ⟹ proper list edge coloring.
-/

@[expose] public section

namespace PaperIII

namespace AppendixD

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `K` is a kernel of the sub-digraph induced by `S`: independent, and every vertex
of `S ∖ K` has an out-neighbour in `K`. -/
def IsKernelOn (A : V → V → Prop) (S K : Finset V) : Prop :=
  K ⊆ S ∧ (∀ x ∈ K, ∀ y ∈ K, ¬ A x y) ∧ ∀ x ∈ S, x ∉ K → ∃ y ∈ K, A x y

/-
**E-D.1 (Kernel coloring lemma).**  If every induced subdigraph of `A` has a
kernel and `|L(v)| ≥ d⁺(v) + 1`, the underlying graph is `L`-colorable.
-/
set_option maxHeartbeats 800000 in
theorem kernel_coloring (A : V → V → Prop) [DecidableRel A]
    (hirr : ∀ v, ¬ A v v)
    (hker : ∀ S : Finset V, ∃ K, IsKernelOn A S K)
    (L : V → Finset ℕ)
    (hL : ∀ v, (Finset.univ.filter fun u => A v u).card + 1 ≤ (L v).card) :
    ∃ φ : V → ℕ, (∀ v, φ v ∈ L v) ∧ ∀ u v, A u v → φ u ≠ φ v := by
  by_contra! h_contra;
  -- By induction on the size of $S$, we can construct a coloring $\phi$ for any subset $S \subseteq V$.
  have h_ind : ∀ (S : Finset V), ∀ (L : V → Finset ℕ), (∀ v ∈ S, (Finset.card (Finset.filter (fun u => A v u) S) + 1 ≤ Finset.card (L v))) → ∃ (φ : V → ℕ), (∀ v ∈ S, φ v ∈ L v) ∧ (∀ u v, u ∈ S → v ∈ S → A u v → φ u ≠ φ v) := by
    intro S L hL; induction' S using Finset.strongInduction with S ih generalizing L; rcases S.eq_empty_or_nonempty with ( rfl | hS ) <;> simp_all +decide ;
    -- Let $v_0 \in S$ be a vertex and $c \in L(v_0)$.
    obtain ⟨v₀, hv₀⟩ : ∃ v₀ ∈ S, True := by
      exact ⟨ hS.choose, hS.choose_spec, trivial ⟩
    obtain ⟨c, hc⟩ : ∃ c ∈ L v₀, True := by
      exact Exists.elim ( Finset.card_pos.mp ( pos_of_gt ( hL v₀ hv₀.1 ) ) ) fun x hx => ⟨ x, hx, trivial ⟩;
    -- Let $S_c = \{v \in S \mid c \in L(v)\}$.
    set Sc := Finset.filter (fun v => c ∈ L v) S with hSc_def
    obtain ⟨K, hK⟩ : ∃ K : Finset V, IsKernelOn A Sc K := by
      exact hker Sc
    have hK_nonempty : K.Nonempty := by
      have := hK.2.2 v₀; simp_all +decide [ IsKernelOn ] ;
      exact not_not.mp fun h => by obtain ⟨ y, hy, hy' ⟩ := hK.2.2 v₀ hv₀ hc ( by aesop ) ; aesop;
    have hK_subset : K ⊆ Sc := by
      exact hK.1
    have hK_ind : ∀ v ∈ Sc \ K, ∃ u ∈ K, A v u := by
      exact fun v hv => hK.2.2 v ( Finset.mem_sdiff.mp hv |>.1 ) ( Finset.mem_sdiff.mp hv |>.2 ) |> fun ⟨ u, hu₁, hu₂ ⟩ => ⟨ u, hu₁, hu₂ ⟩ ;
    have hK_card : ∀ v ∈ Sc \ K, (Finset.card (Finset.filter (fun u => A v u) (S \ K)) + 1 ≤ Finset.card (L v \ {c})) := by
      intro v hv; specialize hL v; simp_all +decide [ Finset.filter_not, Finset.card_sdiff ] ;
      refine' lt_of_lt_of_le ( Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr ⟨ _, _ ⟩ ) ) ( Nat.le_sub_one_of_lt hL );
      · simp +contextual [ Finset.subset_iff ];
      · simp_all +decide [ Finset.ext_iff ];
        exact Exists.elim ( hK_ind v hv.1.1 hv.1.2 hv.2 ) fun u hu => ⟨ u, hu.2, Finset.mem_filter.mp ( hK_subset hu.1 ) |>.1, hu.1 ⟩
    obtain ⟨φ', hφ'⟩ : ∃ φ' : V → ℕ, (∀ v ∈ S \ K, φ' v ∈ L v \ {c}) ∧ (∀ u v, u ∈ S \ K → v ∈ S \ K → A u v → φ' u ≠ φ' v) := by
      apply ih (S \ K) (by
      grind) (fun v => L v \ {c}) (by
      intro v hv; specialize hL v; by_cases hv' : c ∈ L v <;> simp_all +decide [ Finset.sdiff_singleton_eq_erase ] ;
      exact lt_of_le_of_lt ( Finset.card_mono fun x hx => by aesop ) hL)
    use fun v => if v ∈ K then c else φ' v
    simp_all +decide [ Finset.subset_iff ];
    grind +locals;
  obtain ⟨ φ, hφ₁, hφ₂ ⟩ := h_ind Finset.univ L ( fun v _ => by simpa using hL v ) ; obtain ⟨ u, v, huv, h ⟩ := h_contra φ ( fun v => hφ₁ v ( Finset.mem_univ v ) ) ; exact hφ₂ u v ( Finset.mem_univ u ) ( Finset.mem_univ v ) huv h;

variable {U R : Type*} [Fintype U] [Fintype R] [DecidableEq U] [DecidableEq R]

/-- A stable matching of the bipartite graph `B` under rank preferences `pu` (each
`u` prefers larger `pu u ·`) and `pr` (each `r` prefers larger `pr r ·`):
a submatching such that every non-matching edge is dominated at one endpoint. -/
def IsStableMatching (B : Finset (U × R)) (pu : U → R → ℕ) (pr : R → U → ℕ)
    (M : Finset (U × R)) : Prop :=
  M ⊆ B ∧ (∀ e ∈ M, ∀ f ∈ M, e ≠ f → e.1 ≠ f.1 ∧ e.2 ≠ f.2) ∧
    ∀ e ∈ B, e ∉ M →
      (∃ f ∈ M, f.1 = e.1 ∧ pu e.1 e.2 < pu e.1 f.2) ∨
      (∃ f ∈ M, f.2 = e.2 ∧ pr e.2 e.1 < pr e.2 f.1)

/-- Proposals currently retained by each receiver (the receiver keeps a maximum-rank proposal). -/
private def DAAccepted (P : Finset (U × R)) (pr : R → U → ℕ) : Finset (U × R) :=
  P.filter fun e => ∀ f ∈ P, f.2 = e.2 → pr e.2 f.1 ≤ pr e.2 e.1

/-- Proposal sets produced by deferred acceptance are upper-closed in proposer preference,
and their currently accepted proposals use each proposer at most once. -/
private def DAGood (B P : Finset (U × R)) (pu : U → R → ℕ) (pr : R → U → ℕ) : Prop :=
  P ⊆ B ∧
  (∀ e ∈ P, ∀ f ∈ B, f.1 = e.1 → pu e.1 e.2 < pu e.1 f.2 → f ∈ P) ∧
  (∀ e ∈ DAAccepted P pr, ∀ f ∈ DAAccepted P pr, e ≠ f → e.1 ≠ f.1)

private lemma da_accepted_is_matching
    (B P : Finset (U × R)) (pu : U → R → ℕ) (pr : R → U → ℕ)
    (hr : ∀ r u u', (u, r) ∈ B → (u', r) ∈ B → pr r u = pr r u' → u = u')
    (hP : DAGood B P pu pr) :
    DAAccepted P pr ⊆ B ∧
      ∀ e ∈ DAAccepted P pr, ∀ f ∈ DAAccepted P pr, e ≠ f →
        e.1 ≠ f.1 ∧ e.2 ≠ f.2 := by
  grind +locals

private lemma da_rejected_dominated
    (B P : Finset (U × R)) (pr : R → U → ℕ)
    (hr : ∀ r u u', (u, r) ∈ B → (u', r) ∈ B → pr r u = pr r u' → u = u')
    (hPB : P ⊆ B) {e : U × R} (heP : e ∈ P) (heA : e ∉ DAAccepted P pr) :
    ∃ f ∈ DAAccepted P pr, f.2 = e.2 ∧ pr e.2 e.1 < pr e.2 f.1 := by
  simp +zetaDelta at *;
  obtain ⟨f, hfP, hfA⟩ : ∃ f ∈ P, f.2 = e.2 ∧ pr e.2 e.1 < pr e.2 f.1 := by
    contrapose! heA; unfold DAAccepted; aesop;
  obtain ⟨g, hgP, hgA⟩ : ∃ g ∈ P, g.2 = e.2 ∧ ∀ h ∈ P, h.2 = e.2 → pr e.2 h.1 ≤ pr e.2 g.1 := by
    have := Finset.exists_max_image ( P.filter fun x => x.2 = e.2 ) ( fun x => pr e.2 x.1 ) ⟨ f, by aesop ⟩ ; aesop;
  simp +decide [ DAAccepted, hgA ];
  grind

set_option maxHeartbeats 1000000 in
private lemma da_maximal_terminal
    (B P : Finset (U × R)) (pu : U → R → ℕ) (pr : R → U → ℕ)
    (hu : ∀ u r r', (u, r) ∈ B → (u, r') ∈ B → pu u r = pu u r' → r = r')
    (hr : ∀ r u u', (u, r) ∈ B → (u', r) ∈ B → pr r u = pr r u' → u = u')
    (hgood : DAGood B P pu pr)
    (hmax : ∀ Q, DAGood B Q pu pr → Q.card ≤ P.card) :
    ∀ e ∈ B, e ∉ P →
      ∃ f ∈ DAAccepted P pr, f.1 = e.1 ∧ pu e.1 e.2 < pu e.1 f.2 := by
  intro e heB heP;
  by_contra h_contra;
  -- Choose q among unproposed B-edges at e.1 of maximum pu rank.
  obtain ⟨q, hqB, hqP, hqmax⟩ : ∃ q ∈ Finset.filter (fun f => f.1 = e.1) B, q ∉ P ∧ ∀ f ∈ Finset.filter (fun f => f.1 = e.1) B, f ∉ P → pu e.1 f.2 ≤ pu e.1 q.2 := by
    obtain ⟨q, hq⟩ : ∃ q ∈ Finset.filter (fun f => f.1 = e.1) B \ P, ∀ f ∈ Finset.filter (fun f => f.1 = e.1) B \ P, pu e.1 f.2 ≤ pu e.1 q.2 := by
      exact Finset.exists_max_image _ _ ⟨ e, by aesop ⟩;
    exact ⟨ q, by aesop ⟩;
  -- Show Q=insert q P is DAGood.
  have hQgood : DAGood B (insert q P) pu pr := by
    refine' ⟨ _, _, _ ⟩;
    · exact Finset.insert_subset_iff.mpr ⟨ Finset.mem_filter.mp hqB |>.1, hgood.1 ⟩;
    · simp +zetaDelta at *;
      constructor;
      · grind;
      · intro a b hab a' b' hab' ha' h;
        have := hgood.2.1 ( a, b ) hab ( a', b' ) hab' ; simp_all +decide ;
    · intro e he f hf hne;
      by_cases heq : e.2 = q.2 <;> by_cases hfq : f.2 = q.2 <;> simp +decide [ heq, hfq, DAAccepted ] at he hf ⊢;
      · grind +revert;
      · grind +locals;
      · grind +locals;
      · have := hgood.2.2 e; have := hgood.2.2 f; simp +decide [ heq, hfq ] at *;
        grind +locals;
  grind

/-
A finite deferred-acceptance lemma in the edge-set/rank formulation.
-/
private lemma finite_deferred_acceptance
    (B : Finset (U × R)) (pu : U → R → ℕ) (pr : R → U → ℕ)
    (hu : ∀ u r r', (u, r) ∈ B → (u, r') ∈ B → pu u r = pu u r' → r = r')
    (hr : ∀ r u u', (u, r) ∈ B → (u', r) ∈ B → pr r u = pr r u' → u = u') :
    ∃ M, IsStableMatching B pu pr M := by
  -- Choose a maximum-cardinality DAGood proposal set P.
  obtain ⟨P, hP⟩ : ∃ P : Finset (U × R), DAGood B P pu pr ∧ ∀ Q : Finset (U × R), DAGood B Q pu pr → Q.card ≤ P.card := by
    apply_rules [ Set.exists_max_image ];
    · exact Set.toFinite _;
    · refine' ⟨ ∅, _, _, _ ⟩ <;> simp +decide [ DAAccepted ];
  refine' ⟨ DAAccepted P pr, _, _, _ ⟩;
  · exact fun x hx => hP.1.1 ( Finset.mem_filter.mp hx |>.1 );
  · exact da_accepted_is_matching B P pu pr hr hP.1 |>.2;
  · intro e he hne;
    by_cases heP : e ∈ P;
    · exact Or.inr ( da_rejected_dominated B P pr hr hP.1.1 heP hne );
    · exact Or.inl ( da_maximal_terminal B P pu pr hu hr hP.1 hP.2 e he heP )

/-- **E-D.2 (Gale–Shapley).**  For injective rank preferences a stable matching
exists. -/
theorem gale_shapley (B : Finset (U × R)) (pu : U → R → ℕ) (pr : R → U → ℕ)
    (hu : ∀ u r r', (u, r) ∈ B → (u, r') ∈ B → pu u r = pu u r' → r = r')
    (hr : ∀ r u u', (u, r) ∈ B → (u', r) ∈ B → pr r u = pr r u' → u = u') :
    ∃ M, IsStableMatching B pu pr M := by
  exact finite_deferred_acceptance B pu pr hu hr

private lemma matching_saturates_max_left (B : Finset (U × R)) (Δ : ℕ) (hΔ : 0 < Δ)
    (hdegU : ∀ u, (B.filter fun e => e.1 = u).card ≤ Δ)
    (hdegR : ∀ r, (B.filter fun e => e.2 = r).card ≤ Δ) :
    ∃ M : Finset (U × R), M ⊆ B ∧
      (∀ e ∈ M, ∀ f ∈ M, e ≠ f → e.1 ≠ f.1 ∧ e.2 ≠ f.2) ∧
      (∀ u, (B.filter fun e => e.1 = u).card = Δ → ∃ e ∈ M, e.1 = u) := by
  -- Let's define the set of left vertices with degree exactly Δ.
  set S := Finset.filter (fun u => (Finset.card (Finset.filter (fun e => e.1 = u) B)) = Δ) (Finset.univ : Finset U) with hS_def;
  -- By Hall's theorem, there exists a matching in $B$ that covers $S$.
  have h_hall : ∀ T ⊆ S, T.card ≤ (Finset.biUnion T (fun u => Finset.image Prod.snd (Finset.filter (fun e => e.1 = u) B))).card := by
    intro T hT
    have h_card_edges : (Finset.card (Finset.biUnion T (fun u => Finset.filter (fun e => e.1 = u) B))) = Δ * T.card := by
      rw [ Finset.card_biUnion ];
      · rw [ Finset.sum_congr rfl fun u hu => Finset.mem_filter.mp ( hT hu ) |>.2, Finset.sum_const, smul_eq_mul, mul_comm ];
      · exact fun u hu v hv huv => Finset.disjoint_left.mpr fun e heu hev => huv <| by aesop;
    have h_card_edges : (Finset.card (Finset.biUnion (Finset.biUnion T (fun u => Finset.filter (fun e => e.1 = u) B)) (fun e => Finset.filter (fun f => f.2 = e.2) B))) ≤ Δ * (Finset.card (Finset.biUnion T (fun u => Finset.image Prod.snd (Finset.filter (fun e => e.1 = u) B)))) := by
      have h_card_edges : (Finset.card (Finset.biUnion (Finset.biUnion T (fun u => Finset.filter (fun e => e.1 = u) B)) (fun e => Finset.filter (fun f => f.2 = e.2) B))) ≤ Finset.sum (Finset.biUnion T (fun u => Finset.image Prod.snd (Finset.filter (fun e => e.1 = u) B))) (fun r => Finset.card (Finset.filter (fun f => f.2 = r) B)) := by
        refine' le_trans ( Finset.card_le_card _ ) ( Finset.card_biUnion_le );
        simp +decide [ Finset.subset_iff ];
      exact h_card_edges.trans ( by rw [ mul_comm ] ; exact le_trans ( Finset.sum_le_sum fun _ _ => hdegR _ ) ( by simp +decide [ mul_comm ] ) );
    have h_card_edges : (Finset.biUnion (Finset.biUnion T (fun u => Finset.filter (fun e => e.1 = u) B)) (fun e => Finset.filter (fun f => f.2 = e.2) B)) ⊇ Finset.biUnion T (fun u => Finset.filter (fun e => e.1 = u) B) := by
      grind;
    nlinarith [ Finset.card_le_card h_card_edges ];
  -- By Hall's theorem, there exists an injective function $f : S \to R$ such that $(u, f u) \in B$ for all $u \in S$.
  obtain ⟨f, hf_inj, hf⟩ : ∃ f : S → R, Function.Injective f ∧ ∀ u : S, (u.val, f u) ∈ B := by
    have := Finset.all_card_le_biUnion_card_iff_exists_injective ( fun u : S => Finset.image Prod.snd ( Finset.filter ( fun e => e.1 = u.val ) B ) );
    obtain ⟨ f, hf₁, hf₂ ⟩ := this.mp ( fun s => by
      convert h_hall ( Finset.image Subtype.val s ) _;
      · rw [ Finset.card_image_of_injective _ Subtype.coe_injective ];
      · ext; simp [Finset.mem_biUnion, Finset.mem_image];
      · exact Finset.image_subset_iff.mpr fun x hx => x.2 );
    grind +splitImp;
  refine' ⟨ Finset.image ( fun u : S => ( u.val, f u ) ) Finset.univ, _, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ]; all_goals grind

private lemma matching_saturates_max_right (B : Finset (U × R)) (Δ : ℕ) (hΔ : 0 < Δ)
    (hdegU : ∀ u, (B.filter fun e => e.1 = u).card ≤ Δ)
    (hdegR : ∀ r, (B.filter fun e => e.2 = r).card ≤ Δ) :
    ∃ M : Finset (U × R), M ⊆ B ∧
      (∀ e ∈ M, ∀ f ∈ M, e ≠ f → e.1 ≠ f.1 ∧ e.2 ≠ f.2) ∧
      (∀ r, (B.filter fun e => e.2 = r).card = Δ → ∃ e ∈ M, e.2 = r) := by
  obtain ⟨ M, hM₁, hM₂, hM₃ ⟩ := matching_saturates_max_left ( Finset.image Prod.swap B ) Δ hΔ ( by
    intro r; specialize hdegR r; simp_all +decide [ Finset.filter_image ] ;
    rwa [ Finset.card_image_of_injective _ Prod.swap_injective ] ) ( by
    intro u; specialize hdegU u; rw [ Finset.card_filter ] at *; simp_all +decide [ Finset.sum_image ] ;
    rw [ Finset.card_filter ] at *;
    rw [ Finset.sum_image ] <;> aesop );
  refine' ⟨ M.image Prod.swap, _, _, _ ⟩;
  · grind +extAll;
  · grind +splitImp;
  · intro r hr; specialize hM₃ r; simp_all +decide [ Finset.filter_image ] ;
    exact hM₃ ( by rw [ Finset.card_image_of_injective _ Prod.swap_injective ] ; exact hr )

private lemma merge_matchings_preserving_sides
    (B ML MR : Finset (U × R))
    (hMLB : ML ⊆ B) (hMRB : MR ⊆ B)
    (hML : ∀ e ∈ ML, ∀ f ∈ ML, e ≠ f → e.1 ≠ f.1 ∧ e.2 ≠ f.2)
    (hMR : ∀ e ∈ MR, ∀ f ∈ MR, e ≠ f → e.1 ≠ f.1 ∧ e.2 ≠ f.2) :
    ∃ M : Finset (U × R), M ⊆ B ∧
      (∀ e ∈ M, ∀ f ∈ M, e ≠ f → e.1 ≠ f.1 ∧ e.2 ≠ f.2) ∧
      (∀ u, (∃ e ∈ ML, e.1 = u) → ∃ e ∈ M, e.1 = u) ∧
      (∀ r, (∃ e ∈ MR, e.2 = r) → ∃ e ∈ M, e.2 = r) := by
  by_contra h;
  obtain ⟨M, hMB, hM⟩ : ∃ M : Finset (U × R), M ⊆ ML ∪ MR ∧ (∀ e ∈ M, ∀ f ∈ M, e ≠ f → e.1 ≠ f.1 ∧ e.2 ≠ f.2) ∧ (∀ u, (∃ e ∈ ML, e.1 = u) → ∃ e ∈ M, e.1 = u) ∧ (∀ r, (∃ e ∈ MR, e.2 = r) → ∃ e ∈ M, e.2 = r) := by
    obtain ⟨M, hMB, hM⟩ : ∃ M : Finset (U × R), M ⊆ ML ∪ MR ∧ (∀ e ∈ M, ∀ f ∈ M, e ≠ f → e.1 ≠ f.1 ∧ e.2 ≠ f.2) ∧ (∀ e ∈ ML ∪ MR, e ∉ M → (∃ f ∈ M, f.1 = e.1 ∧ (if e ∈ ML then 0 else 1) < (if f ∈ ML then 0 else 1)) ∨ (∃ f ∈ M, f.2 = e.2 ∧ (if e ∈ MR then 0 else 1) < (if f ∈ MR then 0 else 1))) := by
      have := @gale_shapley;
      convert this ( ML ∪ MR ) ( fun u r => if ( u, r ) ∈ ML then 0 else 1 ) ( fun r u => if ( u, r ) ∈ MR then 0 else 1 ) _ _ using 1;
      · ext M; simp [IsStableMatching];
      · grind;
      · grind +splitImp;
    refine' ⟨ M, hMB, hM.1, _, _ ⟩;
    · rintro u ⟨ e, he, rfl ⟩;
      grind;
    · rintro r ⟨ e, he, rfl ⟩;
      grind;
  exact h ⟨ M, Finset.Subset.trans hMB ( Finset.union_subset hMLB hMRB ), hM ⟩

/-- A matching meeting every vertex whose degree attains the common upper bound. -/
private lemma saturated_vertex_matching (B : Finset (U × R)) (Δ : ℕ) (hΔ : 0 < Δ)
    (hdegU : ∀ u, (B.filter fun e => e.1 = u).card ≤ Δ)
    (hdegR : ∀ r, (B.filter fun e => e.2 = r).card ≤ Δ) :
    ∃ M : Finset (U × R), M ⊆ B ∧
      (∀ e ∈ M, ∀ f ∈ M, e ≠ f → e.1 ≠ f.1 ∧ e.2 ≠ f.2) ∧
      (∀ u, (B.filter fun e => e.1 = u).card = Δ → ∃ e ∈ M, e.1 = u) ∧
      (∀ r, (B.filter fun e => e.2 = r).card = Δ → ∃ e ∈ M, e.2 = r) := by
  obtain ⟨ML, hML⟩ := matching_saturates_max_left B Δ hΔ hdegU hdegR
  obtain ⟨MR, hMR⟩ := matching_saturates_max_right B Δ hΔ hdegU hdegR;
  exact merge_matchings_preserving_sides B ML MR hML.1 hMR.1 hML.2.1 hMR.2.1 |> fun ⟨ M, hM ⟩ => ⟨ M, hM.1, hM.2.1, fun u hu => hM.2.2.1 u ( hML.2.2 u hu ), fun r hr => hM.2.2.2 r ( hMR.2.2 r hr ) ⟩

/-
A finite bipartite edge-coloring helper in the pair/Finset encoding.
-/
set_option maxHeartbeats 1000000 in
private lemma finite_bipartite_edge_coloring (B : Finset (U × R)) (Δ : ℕ)
    (hdegU : ∀ u, (B.filter fun e => e.1 = u).card ≤ Δ)
    (hdegR : ∀ r, (B.filter fun e => e.2 = r).card ≤ Δ) :
    ∃ φ : U × R → ℕ, (∀ e ∈ B, φ e < Δ) ∧
      ∀ e ∈ B, ∀ f ∈ B, e ≠ f → (e.1 = f.1 ∨ e.2 = f.2) → φ e ≠ φ f := by
  induction' Δ with Δ ih generalizing B;
  · simp_all +decide [ Finset.ext_iff ];
    exact ⟨ fun a b hab => hdegU a a b hab rfl, 0, fun a b hab c d hcd hne h => False.elim <| hdegU a a b hab rfl ⟩;
  · obtain ⟨ M, hM ⟩ := saturated_vertex_matching B ( Δ + 1 ) ( Nat.succ_pos _ ) hdegU hdegR;
    -- Let $B' = B \setminus M$. Show that each $B'$ degree ≤ Δ.
    set B' := B \ M with hB'
    have hdegU' : ∀ u, (B'.filter fun e => e.1 = u).card ≤ Δ := by
      intro u
      by_cases hu : (B.filter fun e => e.1 = u).card = Δ + 1;
      · obtain ⟨ e, heM, heu ⟩ := hM.2.2.1 u hu;
        have h_card_B' : (B'.filter fun e => e.1 = u).card ≤ (B.filter fun e => e.1 = u).card - 1 := by
          refine' Nat.le_sub_one_of_lt ( Finset.card_lt_card _ );
          simp +decide [ Finset.ssubset_def, Finset.subset_iff ];
          grind +qlia;
        exact h_card_B'.trans ( by simp +decide [ hu ] );
      · exact Nat.le_of_lt_succ ( lt_of_le_of_ne ( hdegU u ) hu ) |> le_trans ( Finset.card_mono <| fun x hx => by aesop )
    have hdegR' : ∀ r, (B'.filter fun e => e.2 = r).card ≤ Δ := by
      intro r
      by_cases hr : (B.filter fun e => e.2 = r).card = Δ + 1;
      · obtain ⟨ e, heM, her ⟩ := hM.2.2.2 r hr;
        have h_card_B'_r : (B'.filter fun e => e.2 = r).card ≤ (B.filter fun e => e.2 = r).card - 1 := by
          refine' Nat.le_sub_one_of_lt ( Finset.card_lt_card _ );
          simp_all +decide [ Finset.ssubset_def, Finset.subset_iff ];
          grind;
        exact h_card_B'_r.trans ( by simp +decide [ hr ] );
      · exact le_trans ( Finset.card_mono <| fun x hx => by aesop ) ( Nat.le_of_lt_succ <| lt_of_le_of_ne ( hdegR r ) hr );
    obtain ⟨φ', hφ'⟩ := ih B' hdegU' hdegR';
    use fun e => if e ∈ M then Δ else φ' e;
    grind

/-- **König's edge coloring** (Step 1 of E-D.3, by alternating-path recoloring):
a bipartite graph with degrees at most `Δ` has a proper `Δ`-edge-coloring. -/
theorem konig_edge_coloring (B : Finset (U × R)) (Δ : ℕ)
    (hdegU : ∀ u, (B.filter fun e => e.1 = u).card ≤ Δ)
    (hdegR : ∀ r, (B.filter fun e => e.2 = r).card ≤ Δ) :
    ∃ φ : U × R → ℕ, (∀ e ∈ B, φ e < Δ) ∧
      ∀ e ∈ B, ∀ f ∈ B, e ≠ f → (e.1 = f.1 ∨ e.2 = f.2) → φ e ≠ φ f := by
  exact finite_bipartite_edge_coloring B Δ hdegU hdegR

/-
**E-D.3 (Galvin, maximum-degree case).**  A simple bipartite graph with all
degrees at most `Δ` and all lists of size at least `Δ` has a proper list edge
coloring.
-/
set_option maxHeartbeats 1200000 in
theorem galvin_max_degree (B : Finset (U × R)) (Δ : ℕ)
    (hdegU : ∀ u, (B.filter fun e => e.1 = u).card ≤ Δ)
    (hdegR : ∀ r, (B.filter fun e => e.2 = r).card ≤ Δ)
    (L : U × R → Finset ℕ) (hL : ∀ e ∈ B, Δ ≤ (L e).card) :
    ∃ φ : U × R → ℕ, (∀ e ∈ B, φ e ∈ L e) ∧
      ∀ e ∈ B, ∀ f ∈ B, e ≠ f → (e.1 = f.1 ∨ e.2 = f.2) → φ e ≠ φ f := by
  by_contra h;
  revert hL h;
  intro hL h_contra
  obtain ⟨φ0, hφ0⟩ : ∃ φ0 : U × R → ℕ, (∀ e ∈ B, φ0 e < Δ) ∧ ∀ e ∈ B, ∀ f ∈ B, e ≠ f → (e.1 = f.1 ∨ e.2 = f.2) → φ0 e ≠ φ0 f := by
    apply konig_edge_coloring B Δ hdegU hdegR;
  -- Define A e f iff e, f∈B and ((same left endpoint and φ0 e < φ0 f) or (same right endpoint and φ0 f < φ0 e)).
  set A : (U × R) → (U × R) → Prop := fun e f => e ∈ B ∧ f ∈ B ∧ ((e.1 = f.1 ∧ φ0 e < φ0 f) ∨ (e.2 = f.2 ∧ φ0 f < φ0 e));
  -- Extend input lists outside B to a singleton, retaining L on B.
  set L' : U × R → Finset ℕ := fun e => if e ∈ B then L e else {0};
  -- Prove A irreflexive.
  have hA_irrefl : ∀ e, ¬ A e e := by
    grind;
  -- Bound outdegree by (Δ-1-c)+c via injectivity of proper colors at each endpoint; use Finset cardinal/image/filter bounds.
  have hA_outdeg : ∀ e, (Finset.univ.filter (fun f => A e f)).card ≤ Δ - 1 := by
    intro e
    by_cases he : e ∈ B;
    · -- Let $c = \phi_0(e)$.
      set c := φ0 e;
      -- The number of edges $f$ with $e.1 = f.1$ and $\phi_0(e) < \phi_0(f)$ is at most $\Delta - 1 - c$.
      have h_card_left : (Finset.filter (fun f => f ∈ B ∧ e.1 = f.1 ∧ c < φ0 f) Finset.univ).card ≤ Δ - 1 - c := by
        have h_card_left : (Finset.image (fun f => φ0 f) (Finset.filter (fun f => f ∈ B ∧ e.1 = f.1 ∧ c < φ0 f) Finset.univ)).card ≤ Δ - 1 - c := by
          have h_card_left : Finset.image (fun f => φ0 f) (Finset.filter (fun f => f ∈ B ∧ e.1 = f.1 ∧ c < φ0 f) Finset.univ) ⊆ Finset.Icc (c + 1) (Δ - 1) := by
            exact Finset.image_subset_iff.mpr fun f hf => Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_filter.mp hf ], Nat.le_sub_one_of_lt ( hφ0.1 f ( Finset.mem_filter.mp hf |>.2.1 ) ) ⟩;
          exact le_trans ( Finset.card_le_card h_card_left ) ( by simp +decide [ Nat.sub_sub ] );
        rwa [ Finset.card_image_of_injOn ] at h_card_left;
        exact fun x hx y hy hxy => Classical.not_not.1 fun h => hφ0.2 x ( Finset.mem_filter.mp hx |>.2.1 ) y ( Finset.mem_filter.mp hy |>.2.1 ) h ( by aesop ) hxy;
      -- The number of edges $f$ with $e.2 = f.2$ and $\phi_0(f) < \phi_0(e)$ is at most $c$.
      have h_card_right : (Finset.filter (fun f => f ∈ B ∧ e.2 = f.2 ∧ φ0 f < c) Finset.univ).card ≤ c := by
        have h_card_right : (Finset.image φ0 (Finset.filter (fun f => f ∈ B ∧ e.2 = f.2 ∧ φ0 f < c) Finset.univ)).card ≤ c := by
          exact le_trans ( Finset.card_le_card ( Finset.image_subset_iff.mpr fun f hf => Finset.mem_range.mpr <| Finset.mem_filter.mp hf |>.2.2.2 ) ) ( by simpa );
        rwa [ Finset.card_image_of_injOn ] at h_card_right;
        simp +zetaDelta at *;
        exact fun x hx y hy hxy => Classical.not_not.1 fun h => hφ0.2 _ _ hx.1 _ _ hy.1 ( by aesop ) ( by aesop ) hxy;
      convert le_trans ( Finset.card_union_le _ _ ) ( add_le_add h_card_left h_card_right ) using 1;
      · congr with f ; simp +decide [ A ] ; tauto;
      · rw [ Nat.sub_add_cancel ( Nat.le_sub_one_of_lt ( hφ0.1 e he ) ) ];
    · simp [A, he];
  -- For every S, apply gale_shapley to S with pu u r=φ0(u,r) and pr r u=Δ-1-φ0(u,r) (or Nat subtraction); properness gives injectivity.
  have h_gale_shapley : ∀ S : Finset (U × R), ∃ K : Finset (U × R), K ⊆ S ∧ (∀ e ∈ K, ∀ f ∈ K, ¬ A e f) ∧ (∀ e ∈ S, e ∉ K → ∃ f ∈ K, A e f) := by
    intro S;
    -- Let $S' = S \cap B$.
    set S' : Finset (U × R) := S.filter (fun e => e ∈ B);
    -- Apply gale_shapley to S' with pu u r=φ0(u,r) and pr r u=Δ-1-φ0(u,r).
    obtain ⟨M, hM⟩ : ∃ M : Finset (U × R), M ⊆ S' ∧ (∀ e ∈ M, ∀ f ∈ M, e ≠ f → e.1 ≠ f.1 ∧ e.2 ≠ f.2) ∧ (∀ e ∈ S', e ∉ M → (∃ f ∈ M, f.1 = e.1 ∧ φ0 e < φ0 f) ∨ (∃ f ∈ M, f.2 = e.2 ∧ Δ - 1 - φ0 e < Δ - 1 - φ0 f)) := by
      convert gale_shapley ( S' ) ( fun u r => φ0 ( u, r ) ) ( fun r u => Δ - 1 - φ0 ( u, r ) ) _ _ using 1;
      · ext; simp [IsStableMatching];
      · grind +splitImp;
      · simp +zetaDelta at *;
        grind;
    refine' ⟨ M ∪ ( S \ S' ), _, _, _ ⟩;
    · exact Finset.union_subset ( Finset.Subset.trans hM.1 ( Finset.filter_subset _ _ ) ) ( Finset.sdiff_subset );
    · grind;
    · grind;
  -- Then kernel_coloring gives a coloring of all U×R from extended lists; restrict conclusion to B.
  obtain ⟨φ, hφ⟩ : ∃ φ : U × R → ℕ, (∀ e, φ e ∈ L' e) ∧ ∀ e f, A e f → φ e ≠ φ f := by
    have h_kernel_coloring : ∀ e, (Finset.univ.filter (fun f => A e f)).card + 1 ≤ (L' e).card := by
      intro e; specialize hA_outdeg e; by_cases he : e ∈ B <;> simp +decide [ he ] at hA_outdeg ⊢;
      · grind +extAll;
      · simp +zetaDelta at *;
        simp +decide [ he ];
    convert kernel_coloring A hA_irrefl _ L' h_kernel_coloring;
    exact fun S => by obtain ⟨ K, hK₁, hK₂, hK₃ ⟩ := h_gale_shapley S; exact ⟨ K, hK₁, hK₂, hK₃ ⟩ ;
  refine' h_contra ⟨ φ, _, _ ⟩; all_goals grind

end AppendixD

end PaperIII