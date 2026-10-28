/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PaperIII.E_4_3
public import PaperIII.E_5
public import PaperIII.E_8
public import PaperIII.Prop_10_1
public import PaperIII.CliquePartition
public import PaperIII.AXDefs

/-!
# Paper III — §9 assembly: Theorem 1.1 and Corollary 1.2

`Theorem_1_1`: `∃ C, ∀` split `G`: `Φ(G) ≤ n²/6 + C·n`.
`Corollary_1_2`: `cp(G) ≤ n²/6 + C·n`, from `cp(G) ≤ Φ(G)`.

The §9 contradiction combines: E-5.1 (`q ≥ 2p−1`), E-4.3 (+AX1, bulk),
E-8 (+AX2, sparse), Corollary 5.3 (`s = O(√p)`), and the dispersion dichotomy
E-5.2/E-6.1/E-7.1 (`√p ≪ s = o(p)`).
-/

@[expose] public section

namespace PaperIII

open SplitGraph

/-- Removing one independent vertex loses at most its incident edges from `Φ`.
This is the monotonicity input for the minimal-counterexample argument. -/
lemma Phi_le_erase_independent (G : SplitGraph) (i : Fin G.q) :
    ∃ H : SplitGraph, H.p = G.p ∧ H.n + 1 = G.n ∧
      ((G.Phi : ℤ) : ℝ) ≤ ((H.Phi : ℤ) : ℝ) + (G.d i : ℝ) := by
  have hq : 0 < G.q := Fin.pos i
  -- Create equivalence from Fin (G.q - 1) to (Fin G.q) \ {i}
  let s : Finset (Fin G.q) := Finset.univ.erase i
  have hcard : Finset.card s = G.q - 1 := by rw [Finset.card_erase_of_mem (Finset.mem_univ i)]; simp
  have hcard' : Fintype.card (Fin (G.q - 1)) = Fintype.card (↥s) := by simp [hcard]
  let m : Fin (G.q - 1) ≃ s := Fintype.equivOfCardEq hcard'
  -- Define H by erasing vertex i
  let H : SplitGraph := ⟨G.p, G.q - 1, fun j => G.N (m j : Fin G.q)⟩
  have Hp : H.p = G.p := rfl
  have Hq : H.q = G.q - 1 := rfl
  refine ⟨H, Hp, ?_, ?_⟩
  · -- H.n + 1 = G.n
    simp [SplitGraph.n, Hp, Hq]
    omega
  · -- G.Phi ≤ H.Phi + G.d i
    simp [SplitGraph.Phi]
    -- Need: edgeCount G - 2 * nu3' G ≤ edgeCount H - 2 * nu3' H + d i
    -- Equivalently: (edgeCount G - edgeCount H) + 2*(nu3' H - nu3' G) ≤ d i
    -- We have edgeCount G - edgeCount H = d i and nu3' H ≤ nu3' G
    have h_edge : (G.edgeCount : ℝ) = (H.edgeCount : ℝ) + (G.d i : ℝ) := by
      rw [G.edgeCount_eq, H.edgeCount_eq, Hp]
      simp only [SplitGraph.d]
      -- H.N j = G.N (m j)
      have hHN : ∀ j, (H.N j).card = (G.N (m j)).card := fun _ => rfl
      simp_rw [hHN]
      -- Need: ∑ x, (G.N x).card = ∑ j, (G.N (m j)).card + (G.N i).card
      -- m is a bijection from Fin (G.q - 1) to s = univ.erase i
      have hsumm : ∑ j, (G.N (m j)).card = ∑ x ∈ s, (G.N x).card := by
        calc ∑ j, (G.N (m j)).card = ∑ x : ↥s, (G.N x).card := Equiv.sum_comp m fun x => (G.N x).card
          _ = ∑ x ∈ s.attach, (G.N x).card := rfl
          _ = ∑ x ∈ s, (G.N x).card := Finset.sum_attach s fun x => (G.N x).card
      rw [hsumm]
      -- And ∑ x : Fin G.q, (G.N x).card = ∑ x ∈ s, (G.N x).card + (G.N i).card
      have huniv : (Finset.univ : Finset (Fin G.q)) = s ∪ {i} := by simp [s]
      rw [huniv, Finset.sum_union (by simp [s]), Finset.sum_singleton]
      simp [add_assoc]
    have h_tri : (H.nu3' : ℝ) ≤ (G.nu3' : ℝ) := by
      -- H is an induced subgraph of G, so any triangle packing in H lifts to G
      -- Define embedding from H.V to G.V
      let embed : H.V → G.V := fun v =>
        match v with
        | Sum.inl a => Sum.inl a
        | Sum.inr j => Sum.inr (m j).val
      -- Embedding is injective
      have embed_inj : Function.Injective embed := by
        intro v v' huv
        simp only [embed] at huv
        cases v <;> cases v' <;> simp_all [Sum.inl.injEq, Sum.inr.injEq]
      -- Embedding preserves adjacency
      have embed_adj : ∀ v v', H.graph.Adj v v' → G.graph.Adj (embed v) (embed v') := by
        intro v v' hadj
        simp only [SplitGraph.graph, SplitGraph.Adj] at hadj ⊢
        cases v <;> cases v' <;> simp_all [embed]
        all_goals simp_all [H]
      -- For any triangle T in H, embed(T) is a triangle in G
      have embed_triangle : ∀ t : Finset H.V, t.card = 3 → H.graph.IsNClique 3 t → G.graph.IsNClique 3 (t.image embed) := by
        intro t ht hclique
        simp only [SimpleGraph.isNClique_iff] at hclique ⊢
        refine ⟨?adj, ?card⟩
        · intro a ha b hb hab
          simp only [Finset.mem_coe] at ha hb
          rw [Finset.mem_image] at ha hb
          obtain ⟨a', ha', rfl⟩ := ha
          obtain ⟨b', hb', rfl⟩ := hb
          have hab' : a' ≠ b' := fun heq => hab (heq ▸ rfl)
          exact embed_adj a' b' (hclique.1 ha' hb' hab')
        · rw [Finset.card_image_of_injective _ embed_inj, ht]
      -- Mapping a packing through embedding
      have embed_packing : ∀ T : Finset (Finset H.V),
          IsTrianglePacking H.graph T → IsTrianglePacking G.graph (T.biUnion fun t => {t.image embed}) := by
        intro T ⟨h_tri, h_disj⟩
        constructor
        · intro t' ht'
          simp only [Finset.mem_biUnion, Finset.mem_singleton] at ht'
          obtain ⟨t, htT, rfl⟩ := ht'
          exact embed_triangle t (h_tri t htT).card_eq (h_tri t htT)
        · intro t₁' ht' t₂' ht'' heq
          rcases Finset.mem_biUnion.mp ht' with ⟨t₁, ht₁T, ht₁'mem⟩
          rcases Finset.mem_biUnion.mp ht'' with ⟨t₂, ht₂T, ht₂'mem⟩
          simp only [Finset.mem_singleton] at ht₁'mem ht₂'mem
          rw [ht₁'mem, ht₂'mem]
          by_cases heqT : t₁ = t₂
          · simp_all
          · have heq' : (t₁.image embed ∩ t₂.image embed) = (t₁ ∩ t₂).image embed := by
              apply Finset.ext
              intro x
              simp only [Finset.mem_inter, Finset.mem_image]
              constructor
              · rintro ⟨⟨a, ha₁, rfl⟩, ⟨b, hb₂, hbq⟩⟩
                have heq' : a = b := embed_inj hbq.symm
                exact ⟨a, ⟨ha₁, heq'.symm ▸ hb₂⟩, rfl⟩
              · rintro ⟨a, ⟨ha₁, ha₂⟩, rfl⟩
                exact ⟨⟨a, ha₁, rfl⟩, ⟨a, ha₂, rfl⟩⟩
            rw [heq']
            rw [Finset.card_image_of_injective _ embed_inj]
            exact h_disj ht₁T ht₂T heqT
      have hsub : {k | ∃ T : Finset (Finset H.V), IsTrianglePacking H.graph T ∧ T.card = k} ⊆
                   {k | ∃ T : Finset (Finset G.V), IsTrianglePacking G.graph T ∧ T.card = k} := by
        intro k ⟨T, hT_pack, hk⟩
        refine ⟨T.biUnion fun t => {t.image embed}, embed_packing T hT_pack, ?_⟩
        rw [Finset.card_biUnion]
        · simp_all
        · intro t₁ ht₁ t₂ ht₂ hne
          simp
          intro heq
          exact hne (Finset.image_injective embed_inj heq)
      simp only [SplitGraph.nu3', nu3]
      have hne : Set.Nonempty {k | ∃ T : Finset (Finset H.V), IsTrianglePacking H.graph T ∧ T.card = k} := by
        use 0
        use ∅
        simp [IsTrianglePacking]
      exact Nat.cast_le.mpr (csSup_le_csSup (by
        use G.n ^ 3
        intro k ⟨T, hT, hk⟩
        simp
        have : T.card ≤ Nat.choose G.n 3 := by
          have hsubT : T ⊆ Finset.powersetCard 3 Finset.univ := by
            intro t ht
            rw [Finset.mem_powersetCard]
            exact ⟨Finset.subset_univ t, (hT.1 t ht).card_eq⟩
          calc T.card ≤ (Finset.powersetCard 3 Finset.univ).card := Finset.card_le_card hsubT
            _ = (Finset.card (Finset.univ : Finset G.V)).choose 3 := Finset.card_powersetCard 3 _
            _ = G.n.choose 3 := by simp [SplitGraph.n]
        calc k = T.card := hk.symm
          _ ≤ Nat.choose G.n 3 := this
          _ ≤ G.n ^ 3 := by
            have : Nat.choose G.n 3 ≤ G.n ^ 3 := Nat.choose_le_pow _ _
            exact this) hne hsub)
    calc (G.edgeCount : ℝ) = (H.edgeCount : ℝ) + (G.d i : ℝ) := h_edge
      _ ≤ (H.edgeCount : ℝ) - 2 * (H.nu3' : ℝ) + (G.d i : ℝ) + 2 * (G.nu3' : ℝ) := by linarith

/-- The factorization estimate controls the entire range at and above `q = 2p - 1`. -/
lemma Phi_le_high_ratio (G : SplitGraph) (hq : 2 * G.p ≤ G.q + 1) :
    ((G.Phi : ℤ) : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + (G.n : ℝ) / 2 := by
  by_cases hp : G.p = 0
  · -- When p = 0, Phi = 0 and n²/6 + n/2 ≥ 0
    have hn_zero : G.n = G.q := by simp [SplitGraph.n, hp]
    have hPhi : G.Phi = 0 := by
      have hgraph : G.graph = ⊥ := by
        show (SplitGraph.graph G) = ⊥
        ext u v
        simp only [SplitGraph.graph, SplitGraph.Adj, SimpleGraph.bot_adj]
        rcases u with a | i <;> rcases v with b | j <;> first
          | exact Fin.elim0 a
          | exact Fin.elim0 b
          | rw [hp] at a; exact Fin.elim0 a
          | rw [hp] at b; exact Fin.elim0 b
          | simp_all
      have hedges : G.graph.edgeFinset = ∅ := by simp [hgraph]
      simp [SplitGraph.Phi, SplitGraph.nu3', SplitGraph.edgeCount, hedges, hgraph]
      simp [nu3, IsTrianglePacking]
      have : {k : ℕ | ∃ T : Finset (Finset G.V), (((∀ t : Finset G.V, t ∉ T) ∧ (T : Set (Finset G.V)).Pairwise (fun t₁ t₂ => (t₁ ∩ t₂).card ≤ 1)) ∧ T.card = k)} = {0} := by
        ext k
        simp only [Set.mem_singleton_iff]
        constructor
        · rintro ⟨T, ⟨hT1, _⟩, rfl⟩
          have hT2 : T = ∅ := by
            ext t
            simp [hT1 t]
          simp [hT2]
        · intro hk
          rw [hk]
          refine ⟨∅, ⟨by simp, by simp⟩, rfl⟩
      rw [this]
      simp
    rw [hPhi]
    push_cast [hn_zero]
    have : (0 : ℝ) ≤ (G.q : ℝ) ^ 2 / 6 + (G.q : ℝ) / 2 := by positivity
    linarith
  · -- When p ≥ 1
    have hp1 : 1 ≤ G.p := Nat.pos_of_ne_zero hp
    -- Need to show rp G.p ≤ G.q
    have hqp : G.p ≤ G.q := by omega
    have hrp : rp G.p ≤ G.q := le_trans (rp_le G.p) hqp
    -- Basic facts
    have hn : (G.n : ℝ) = (G.p : ℝ) + (G.q : ℝ) := by rw [SplitGraph.n]; push_cast; ring
    have hs : (G.s : ℝ) = 2 * (G.p : ℝ) - (G.q : ℝ) := by rw [SplitGraph.s]; push_cast; ring
    have hs_le : (G.s : ℝ) ≤ 1 := by
      have hq' : (2 : ℝ) * G.p ≤ G.q + 1 := by exact_mod_cast hq
      rw [hs]; linarith
    -- Case split on q
    by_cases hq2 : 2 ≤ G.q
    · -- Use E-5.2
      have hE52 := E_5_2 G hrp hq2
      -- When 2p ≤ q + 1, we have s ≤ 1
      have hs_le1 : (G.s : ℝ) ≤ 1 := hs_le
      have hs_sub1_neg : (G.s : ℝ) - 1 ≤ 0 := by linarith
      -- s²/6 ≥ 0
      have hs2_nonneg : (G.s : ℝ) ^ 2 / 6 ≥ 0 := by positivity
      -- The terms ((s-1)*M - S₂)/q and -2*(doubledFactors/rp)*V/(q*(q-1)) are non-positive
      have hM_neg : (((G.s : ℝ) - 1) * (G.M : ℝ) - (G.S₂ : ℝ)) / (G.q : ℝ) ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg
        · nlinarith [sq_nonneg (G.s : ℝ), show (0 : ℝ) ≤ G.M by positivity,
                     show (0 : ℝ) ≤ G.S₂ by positivity]
        · positivity
      -- The last term is non-negative, so -term ≤ 0
      have hq_sub1_pos : (G.q : ℝ) - 1 > 0 := by
        have : (2 : ℝ) ≤ G.q := by exact_mod_cast hq2
        linarith
      have hlast_nonneg : 2 * ((G.doubledFactors : ℝ) / (rp G.p : ℝ)) * (G.dispersionV : ℝ)
                         / ((G.q : ℝ) * ((G.q : ℝ) - 1)) ≥ 0 := by positivity
      -- p ≤ n
      have hp_le_n : (G.p : ℝ) ≤ G.n := by exact_mod_cast Nat.le_add_right G.p G.q
      linarith
    · -- q = 1, so p = 1 (from 2p ≤ q + 1 = 2)
      have hq1 : G.q = 1 := by omega
      have hp_eq_1 : G.p = 1 := by omega
      -- For p = 1, q = 1: n = 2, s = 1
      -- Phi = edgeCount - 2*nu3' ≤ edgeCount ≤ 1 (at most one edge)
      -- Bound: n²/6 + n/2 = 4/6 + 1 = 5/3 > 1
      have hphi_bound : (G.Phi : ℤ) ≤ 1 := by
        have hedge : G.edgeCount ≤ 1 := by
          unfold SplitGraph.edgeCount
          have h := G.graph.card_edgeFinset_le_card_choose_two
          have hV : Fintype.card G.V = 2 := by simp [SplitGraph.V, hp_eq_1, hq1]
          rw [hV] at h
          simpa using h
        have hnu3 : G.nu3' = 0 := by
          unfold SplitGraph.nu3'
          rw [nu3]
          have hvp2 : Fintype.card G.V ≤ 2 := by simp [SplitGraph.V, hp_eq_1, hq1]
          have hno_triangle : ∀ t : Finset G.V, ¬G.graph.IsNClique 3 t := by
            intro t ht3
            have hcard3 : t.card = 3 := ht3.2
            have : t.card ≤ Fintype.card G.V := Finset.card_le_univ t
            linarith
          have hset_eq : {k | ∃ T : Finset (Finset G.V), IsTrianglePacking G.graph T ∧ T.card = k} = {0} := by
            ext k
            simp [IsTrianglePacking]
            constructor
            · rintro ⟨T, ⟨hTtri, _⟩, rfl⟩
              by_cases hTempty : T = ∅
              · simp [hTempty]
              · obtain ⟨t, ht⟩ := Finset.nonempty_of_ne_empty hTempty
                exact False.elim (hno_triangle t (hTtri t ht))
            · intro hk
              rw [hk]
              exact ⟨∅, ⟨fun t ht => False.elim (Finset.notMem_empty t ht), by simp⟩, rfl⟩
          rw [hset_eq]
          simp
        simp [SplitGraph.Phi, hnu3]
        linarith
      have hn_val : (G.n : ℝ) = 2 := by rw [SplitGraph.n, hp_eq_1, hq1]; norm_num
      have hgoal : (G.n : ℝ) ^ 2 / 6 + (G.n : ℝ) / 2 = 5 / 3 := by rw [hn_val]; norm_num
      have : (G.Phi : ℝ) ≤ (1 : ℝ) := by exact_mod_cast hphi_bound
      linarith

/-- Assembly of the large-order, minimum-degree case from the bulk, sparse, and
corridor estimates. -/
lemma eventual_bound_of_high_degree_of_AX1_AX2
    (hAX1 : AX1Assumption) (hAX2 : AX2Assumption) :
    ∃ N : ℕ, ∀ G : SplitGraph, N ≤ G.n →
      (∀ i : Fin G.q, (2 * (G.n : ℝ) - 1) / 6 + 1 < (G.d i : ℝ)) →
      ((G.Phi : ℤ) : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + 2 * (G.n : ℝ) := by
  obtain ⟨nBulk, hBulk⟩ := E_4_3_of_AX1 hAX1 (1 / 10) (by norm_num)
  obtain ⟨nSparse, hSparse⟩ := E_8_of_AX1_AX2 hAX1 hAX2 1
  refine ⟨max nBulk (max nSparse 7000), fun G hn hdeg => ?_⟩
  have hnBulk : nBulk ≤ G.n := le_trans (le_max_left _ _) hn
  have hnSparse : nSparse ≤ G.n :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn7000 : 7000 ≤ G.n :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hn0 : (0 : ℝ) ≤ (G.n : ℝ) := by positivity
  by_cases hhigh : 2 * G.p ≤ G.q + 1
  · have h := Phi_le_high_ratio G hhigh
    linarith
  by_cases hsparse : 2 * G.q ≤ G.p
  · have hdeg' : ∀ i : Fin G.q,
        (2 * (G.n : ℝ) - 1) / 6 + (1 : ℕ) < (G.d i : ℝ) := by simpa using hdeg
    have h := hSparse G hnSparse hsparse hdeg'
    linarith
  have hp0 : 0 < G.p := by
    rw [SplitGraph.n] at hn7000
    omega
  have hpQ : (0 : ℚ) < (G.p : ℚ) := by exact_mod_cast hp0
  have haLower : (1 / 10 : ℚ) ≤ G.α := by
    rw [SplitGraph.α, le_div_iff₀ hpQ]
    have hnat : G.p < 2 * G.q := Nat.lt_of_not_ge hsparse
    have hcast : (G.p : ℚ) ≤ 10 * (G.q : ℚ) := by exact_mod_cast (by omega : G.p ≤ 10 * G.q)
    linarith
  by_cases haUpper : G.α ≤ (19 / 10 : ℚ)
  · have h := hBulk G hnBulk haLower (by norm_num at haUpper ⊢; exact haUpper)
    linarith
  have haHigh : (19 / 10 : ℚ) < G.α := lt_of_not_ge haUpper
  have hqHigh : 19 * G.p < 10 * G.q := by
    rw [SplitGraph.α, lt_div_iff₀ hpQ] at haHigh
    exact_mod_cast (by linarith : (19 : ℚ) * G.p < 10 * G.q)
  have hqBelow : G.q + 1 < 2 * G.p := Nat.lt_of_not_ge hhigh
  have hp2304 : 2304 ≤ G.p := by
    rw [SplitGraph.n] at hn7000
    omega
  have hs0 : 0 ≤ G.s := by
    rw [SplitGraph.s]
    omega
  have hs8 : 8 * (G.s : ℝ) ≤ (G.p : ℝ) := by
    rw [SplitGraph.s]
    push_cast
    exact_mod_cast (by omega : 8 * (2 * G.p - G.q : ℤ) ≤ G.p)
  by_cases hsLow : (G.s : ℝ) ^ 2 ≤ 36 * (G.p : ℝ)
  · -- Prop_10_1_low now gives the sharper Φ ≤ n²/6 + (3/2)n; relax to the +2n target.
    have h := Prop_10_1_low G (le_trans (by norm_num) hp2304) hs0 hsLow
    have hn0 : (0 : ℝ) ≤ (G.n : ℝ) := by positivity
    linarith
  · have h := Prop_10_1_mid G hp2304 (le_of_not_ge hsLow) hs8 hdeg
    linarith

/-- The minimal-counterexample induction: an eventual estimate under the degree
condition gives one absolute linear-error estimate for all split graphs. -/
lemma global_bound_from_eventual_high_degree
    (N : ℕ)
    (heventual : ∀ G : SplitGraph, N ≤ G.n →
      (∀ i : Fin G.q, (2 * (G.n : ℝ) - 1) / 6 + 1 < (G.d i : ℝ)) →
      ((G.Phi : ℤ) : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + 2 * (G.n : ℝ)) :
    ∀ G : SplitGraph, ((G.Phi : ℤ) : ℝ) ≤
      (G.n : ℝ) ^ 2 / 6 + (max 2 (N : ℝ)) * (G.n : ℝ) := by
  -- We'll prove by strong induction on n
  have hind : ∀ m : ℕ, ∀ G : SplitGraph, G.n = m →
      ((G.Phi : ℤ) : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + (max 2 (N : ℝ)) * (G.n : ℝ) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro G hG
    rw [hG]
    -- Case 1: m = 0 means empty graph
    by_cases hm0 : m = 0
    · -- When m = 0, Φ(G) = 0 and RHS = 0
      subst hm0
      have hn0 : G.n = 0 := hG
      have hp0 : G.p = 0 := by simp [SplitGraph.n] at hn0; omega
      have hq0 : G.q = 0 := by simp [SplitGraph.n] at hn0; omega
      have hG0 : (Fintype.card G.V) = 0 := by rw [card_V, hn0]
      have hEC : G.edgeCount = 0 := by
        unfold edgeCount
        apply Finset.card_eq_zero.mpr
        ext e
        simp
        have hV : IsEmpty G.V := Fintype.card_eq_zero_iff.mp hG0
        induction e using Quot.ind with
        | _ s => exact False.elim (IsEmpty.elim hV s.1)
      have hnu : G.nu3' = 0 := by
        simp [SplitGraph.nu3', nu3]
        refine le_antisymm ?_ (Nat.zero_le _)
        apply csSup_le
        · exact ⟨0, ∅, by simp [IsTrianglePacking], rfl⟩
        · intro k hk
          simp only [Set.mem_setOf_eq] at hk
          obtain ⟨T, hT, rfl⟩ := hk
          refine Nat.le_zero.mpr ?_
          apply Finset.card_eq_zero.mpr
          ext t
          simp
          intro ht
          have h1 := hT.1 t ht
          have hc := h1.card_eq
          have hV : IsEmpty G.V := Fintype.card_eq_zero_iff.mp hG0
          have ht_empty : t = ∅ := by
            ext x
            simp
            exact IsEmpty.elim hV x
          rw [ht_empty, Finset.card_empty] at hc
          norm_num at hc
      simp [SplitGraph.Phi, hEC, hnu]
    -- Case 2: m > 0
    · -- Check if G satisfies the degree condition
      by_cases hdeg : ∀ i : Fin G.q, (2 * (m : ℝ) - 1) / 6 + 1 < (G.d i : ℝ)
      · -- Case: all degrees are high
        -- If m ≥ N, apply heventual
        by_cases hmN : N ≤ m
        · have h := heventual G (by rw [hG]; exact hmN) (by simpa only [hG] using hdeg)
          simp only [hG] at h
          calc (G.Phi : ℝ) ≤ (m : ℝ) ^ 2 / 6 + 2 * (m : ℝ) := h
            _ ≤ (m : ℝ) ^ 2 / 6 + max 2 (N : ℝ) * (m : ℝ) := by
              apply add_le_add_right
              apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
              exact le_max_left _ _
        · -- If m < N, we use a trivial bound
          -- Phi ≤ edgeCount ≤ m²/2 and max 2 N * m > m² when m < N
          have hm_lt_N : m < N := Nat.lt_of_not_le hmN
          have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
          -- Phi ≤ edgeCount
          have hPhi_le_edgeCount : ((G.Phi : ℤ) : ℝ) ≤ (G.edgeCount : ℝ) := by
            simp [SplitGraph.Phi]
          -- edgeCount ≤ n choose 2 ≤ n²/2
          -- Use a crude bound: edgeCount ≤ n²
          have h_ed : (G.edgeCount : ℝ) ≤ (m : ℝ) ^ 2 := by
            have hn : G.n = m := hG
            have h1 : G.edgeCount ≤ G.n ^ 2 := by
              -- Use that edgeFinset ⊆ Sym2.univ, and |Sym2 V| ≤ |V|²
              have hsym2_bound : Fintype.card (Sym2 G.V) ≤ Fintype.card G.V ^ 2 := by
                have hsurj : Function.Surjective (Function.uncurry (Sym2.mk : G.V → G.V → Sym2 G.V)) := Sym2.mk_surjective
                calc Fintype.card (Sym2 G.V) ≤ Fintype.card (G.V × G.V) := Fintype.card_le_of_surjective _ hsurj
                  _ = Fintype.card G.V ^ 2 := by simp [Fintype.card_prod]; ring
              calc G.edgeCount = G.graph.edgeFinset.card := rfl
                _ ≤ (Finset.univ : Finset (Sym2 G.V)).card := Finset.card_le_card (Finset.subset_univ _)
                _ = Fintype.card (Sym2 G.V) := Finset.card_univ
                _ ≤ Fintype.card G.V ^ 2 := hsym2_bound
                _ = G.n ^ 2 := by rw [card_V]
            have h2 : (G.edgeCount : ℝ) ≤ (G.n ^ 2 : ℝ) := by exact_mod_cast h1
            rw [hn] at h2
            exact h2
          -- Now conclude: Phi ≤ m² ≤ m²/6 + max 2 N * m
          calc ((G.Phi : ℤ) : ℝ) ≤ (G.edgeCount : ℝ) := hPhi_le_edgeCount
            _ ≤ (m : ℝ) ^ 2 := h_ed
            _ ≤ (m : ℝ) ^ 2 / 6 + max 2 (N : ℝ) * (m : ℝ) := by
                have h2 : (m : ℝ) < N := by exact_mod_cast hm_lt_N
                have h3 : max (2 : ℝ) (N : ℝ) ≥ m := le_of_lt (lt_max_of_lt_right h2)
                have hm_pos_real : (0 : ℝ) < m := Nat.cast_pos.mpr hm_pos
                nlinarith [hm_pos_real]
      · -- Case: some degree is low
        -- There exists a vertex with low degree
        push_neg at hdeg
        obtain ⟨i, hi⟩ := hdeg
        -- Use Phi_le_erase_independent to get a graph H with H.n + 1 = G.n
        obtain ⟨H, _, hHn, hPhi_bound⟩ := Phi_le_erase_independent G i
        -- m > 0 from hm0
        have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
        -- H.n = m - 1 since H.n + 1 = G.n = m and m > 0
        have hHn_eq : H.n = m - 1 := by omega
        -- H.n < m for the induction hypothesis
        have hHn_lt : H.n < m := by omega
        -- Apply induction hypothesis to H
        have hH_bound := ih (m - 1) (by omega) H hHn_eq
        -- (m - 1 : ℕ) cast to ℝ = (m : ℝ) - 1 since m > 0
        have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
        rw [hHn_eq, hcast] at hH_bound
        -- Combine: Phi(G) ≤ Phi(H) + d(i) ≤ IH_bound + d(i)
        -- Since d(i) ≤ (2m - 1)/6 + 1, we get the result
        -- max(2, N) ≥ 2 ≥ 1
        have hmax : (max 2 (N : ℝ)) ≥ 2 := le_max_left _ _
        linarith
  exact fun G => hind G.n G rfl

/-- **Theorem 1.1** (LEDGER E-9): there is an absolute constant `C` with
`Φ(G) ≤ n²/6 + C·n` for every split graph `G`.  Uses AX1, AX2. -/
theorem Theorem_1_1_of_AX1_AX2
    (hAX1 : AX1Assumption) (hAX2 : AX2Assumption) :
    ∃ C : ℝ, ∀ G : SplitGraph, ((G.Phi : ℤ) : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) := by
  obtain ⟨N, hN⟩ := eventual_bound_of_high_degree_of_AX1_AX2 hAX1 hAX2
  exact ⟨max 2 (N : ℝ), global_bound_from_eventual_high_degree N hN⟩

/-- **Corollary 1.2** (LEDGER): the same bound for the clique-partition number,
`cp(G) ≤ n²/6 + C·n`. -/
theorem Corollary_1_2_of_AX1_AX2
    (hAX1 : AX1Assumption) (hAX2 : AX2Assumption) :
    ∃ C : ℝ, ∀ G : SplitGraph, (G.cp : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) := by
  obtain ⟨C, hC⟩ := Theorem_1_1_of_AX1_AX2 hAX1 hAX2
  refine ⟨C, fun G => ?_⟩
  have h1 : (G.cp : ℝ) ≤ ((G.Phi : ℤ) : ℝ) := by exact_mod_cast cp_le_Phi G
  exact le_trans h1 (hC G)

end PaperIII
