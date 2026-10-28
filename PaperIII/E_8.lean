/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PaperIII.E_B
public import PaperIII.AXDefs
public import PaperIII.E_4_3
public import PaperIII.CorridorDefs
public import PaperIII.DiracMatching
public import PaperIII.E_8_Core

/-!
# Paper III — §8 Sparse-independent regime (E-8)

If `q = o(p)` and every `v ∈ I` has `d(v) > (2n−1)/6 + k`, then `Φ(G) ≤ n²/6 + O(n)`.
Uses Dirac (Hamilton path at high min-degree), Turán (`K₅`), **AX2**, and the
divisibility correction **E-B** (`pathCorrection_odd_iff`).

**Statement note (2026-07-23).** The three §8 lemmas carry the ledger's additive `O(n)`
slack (here `+2·n` in `Φ`-form, equivalently `−n` in packing-form).  The earlier strict
form `Φ ≤ n²/6` was FALSE: on the degenerate `q = 0` clique `K_p` (admissible since
`10·0 < p` and the degree hypothesis is vacuous) one has `Φ(K_p) = n²/6 + p/6 > n²/6`
(machine-checked in `diagnostics/E_8_Disproof.lean`).  Restoring the `O(n)` slack matches
`LEDGER.md` line 146 and is absorbed by `Theorem_1_1`'s `+C·n`.
-/

@[expose] public section

namespace PaperIII

open SplitGraph

/-- The number of edges of a split graph is at most `C(n,2)` (it is a simple graph on
`n = p+q` vertices). -/
private lemma edgeCount_le_choose (G : SplitGraph) : G.edgeCount ≤ G.n.choose 2 := by
  have h := SimpleGraph.card_edgeFinset_le_card_choose_two (G := G.graph)
  rw [card_V] at h
  exact h

/-- **KKI + clique-remainder packing (combinatorial core of E-8).**  In the very sparse
regime `10q < p` with the E-8 degree lower bound, the split graph has an edge-disjoint
triangle family covering all but at most `3n` edges.  Concretely:

* For each independent vertex `i` choose a matching `Mᵢ` inside its clique neighbourhood
  `Nᵢ`, kept edge-disjoint across `i`; each matched clique edge `{u,v} ⊆ Nᵢ` gives the
  triangle `{inl u, inl v, inr i}`.  Because `dᵢ > (2n−1)/6 + k ≥ 2q`, the available
  sub-neighbourhood always has minimum degree `≥ dᵢ/2`, so (Dirac) admits a near-perfect
  matching; at most one cross edge per `i` (so `≤ q` total) is left uncovered.
* The clique remainder `R = K_p − ⋃ Mᵢ` has `δ(R) ≥ p−1−q ≥ 0.9p`
  (`clique_remainder_mindegree`); correct it to a triangle-divisible `R'` (even degrees via
  `pathCorrection_odd_iff`, `|E| ≡ 0 mod 3` by deleting a bounded `C₄`/`C₅`), losing
  `O(n)+O(1)` edges, then apply `AX2` to obtain `|E(R')|/3` clique triangles.

The two families are edge-disjoint and cover all but `≤ q + p + O(1) ≤ 3n` edges, hence
`edgeCount ≤ 3·|F| + 3n`. -/
private lemma E_8_packing_exists_of_AX2
    (hAX2 : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
        (H : SimpleGraph V) (_ : DecidableRel H.Adj),
        H.edgeFinset.card % 3 = 0 →
        (∀ v : V, Even (H.degree v)) →
        n₀ ≤ Fintype.card V →
        ((0.9 + ε) * (Fintype.card V : ℝ) ≤ (H.minDegree : ℝ)) →
        HasTriangleDecomposition H)
    (k : ℕ) :
    ∃ n₀ : ℕ, ∀ G : SplitGraph, n₀ ≤ G.n → 12 * G.q < G.p →
      (∀ i : Fin G.q, (2 * (G.n : ℝ) - 1) / 6 + k < (G.d i : ℝ)) →
      ∃ T : Finset (Finset G.V), IsTrianglePacking G.graph T ∧
        G.edgeCount ≤ 3 * T.card + 3 * G.n := by
  classical
  obtain ⟨n₂, hclique⟩ := E_8_clique_packing_of_AX2 hAX2
  refine ⟨2 * n₂ + 1, fun G hn hq hd => ?_⟩
  have hn_def : G.n = G.p + G.q := rfl
  -- `p` is large: `12q < p` and `n = p + q` force `p ≥ n₂`.
  have hpn2 : n₂ ≤ G.p := by omega
  -- Convert the real degree lower bound into `d i ≥ 2q + 1` for each independent vertex.
  have hd_nat : ∀ i : Fin G.q, 2 * G.q + 1 ≤ G.d i := by
    intro i
    have hq1 : 1 ≤ G.q := i.pos
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
    have hreal : (2 * (G.n : ℝ) - 1) < 6 * (G.d i : ℝ) := by
      have := hd i; nlinarith [this, hk0]
    have hnatlt : 2 * G.n < 6 * G.d i + 1 := by
      have h1 : ((2 * G.n : ℕ) : ℝ) < ((6 * G.d i + 1 : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast h1
    omega
  obtain ⟨Tc, D, hTc_pack, hD_diag, hD_inc, hD_card, hTc_form, hcross_cover⟩ :=
    E_8_cross_packing G hd_nat
  obtain ⟨Tk, hTk_pack, hTk_form, hclique_cover⟩ :=
    hclique G D hpn2 hq hD_diag hD_inc
  -- KKI triangles and clique triangles are edge-disjoint: a shared clique edge would lie
  -- in `D` (from the KKI side) yet avoid `D` (from the clique side).
  have hcross_disj : ∀ t₁ ∈ Tc, ∀ t₂ ∈ Tk, (t₁ ∩ t₂).card ≤ 1 := by
    intro t₁ ht₁ t₂ ht₂
    obtain ⟨a, b, i, hab, hDab, rfl⟩ := hTc_form t₁ ht₁
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl, hnxy, hnxz, hnyz⟩ := hTk_form t₂ ht₂
    by_contra hcon
    push_neg at hcon
    have hsub : ({Sum.inl a, Sum.inl b, Sum.inr i} : Finset G.V) ∩
        {Sum.inl x, Sum.inl y, Sum.inl z} ⊆ {Sum.inl a, Sum.inl b} := by
      intro w hw
      rw [Finset.mem_inter] at hw
      have hw1 := hw.1
      have hw2 := hw.2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw1 hw2 ⊢
      rcases hw1 with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · rcases hw2 with h | h | h <;> exact absurd h (by simp)
    have hcard2 : ({Sum.inl a, Sum.inl b} : Finset G.V).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton]
    have heq : ({Sum.inl a, Sum.inl b, Sum.inr i} : Finset G.V) ∩
        {Sum.inl x, Sum.inl y, Sum.inl z} = {Sum.inl a, Sum.inl b} :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcard2]; exact hcon)
    have hain : (Sum.inl a : G.V) ∈ ({Sum.inl x, Sum.inl y, Sum.inl z} : Finset G.V) := by
      have : (Sum.inl a : G.V) ∈ ({Sum.inl a, Sum.inl b, Sum.inr i} : Finset G.V) ∩
          {Sum.inl x, Sum.inl y, Sum.inl z} := by rw [heq]; simp
      exact (Finset.mem_inter.mp this).2
    have hbin : (Sum.inl b : G.V) ∈ ({Sum.inl x, Sum.inl y, Sum.inl z} : Finset G.V) := by
      have : (Sum.inl b : G.V) ∈ ({Sum.inl a, Sum.inl b, Sum.inr i} : Finset G.V) ∩
          {Sum.inl x, Sum.inl y, Sum.inl z} := by rw [heq]; simp
      exact (Finset.mem_inter.mp this).2
    simp only [Finset.mem_insert, Finset.mem_singleton, Sum.inl.injEq] at hain hbin
    -- both `a` and `b` are among `x, y, z`, hence `s(a,b)` is an edge of `t₂` — contradiction.
    rcases hain with rfl | rfl | rfl <;> rcases hbin with rfl | rfl | rfl <;>
      first
        | exact hab rfl
        | (exact hnxy hDab) | (exact hnxz hDab) | (exact hnyz hDab)
        | (rw [Sym2.eq_swap] at hDab; first | exact hnxy hDab | exact hnxz hDab | exact hnyz hDab)
  have hT_pack : IsTrianglePacking G.graph (Tc ∪ Tk) :=
    trianglePacking_union G.graph hTc_pack hTk_pack hcross_disj
  refine ⟨Tc ∪ Tk, hT_pack, ?_⟩
  -- The two families are disjoint as finsets (KKI triangles contain an `inr` vertex).
  have hdisj_fin : Disjoint Tc Tk := by
    rw [Finset.disjoint_left]
    intro t htc htk
    obtain ⟨a, b, i, _, _, htc_eq⟩ := hTc_form t htc
    obtain ⟨x, y, z, _, _, _, htk_eq, _, _, _⟩ := hTk_form t htk
    have hmem : (Sum.inr i : G.V) ∈ ({Sum.inl x, Sum.inl y, Sum.inl z} : Finset G.V) := by
      rw [← htk_eq, htc_eq]; simp
    simp at hmem
  have hcard : (Tc ∪ Tk).card = Tc.card + Tk.card :=
    Finset.card_union_of_disjoint hdisj_fin
  rw [hcard, edgeCount_eq]
  omega

/-- The genuinely sparse part of the packing estimate, WITH the ledger's `O(n)` slack
(packing-form: `−n` on the left, i.e. `Φ ≤ n²/6 + 2n`).  The stronger numerical
assumption isolates the range in which the corrected clique remainder is dense enough
for `AX2`; the complementary range is supplied by `E_4_3`. -/
private theorem E_8_very_sparse_packing_estimate_of_AX2
    (hAX2 : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
        (H : SimpleGraph V) (_ : DecidableRel H.Adj),
        H.edgeFinset.card % 3 = 0 →
        (∀ v : V, Even (H.degree v)) →
        n₀ ≤ Fintype.card V →
        ((0.9 + ε) * (Fintype.card V : ℝ) ≤ (H.minDegree : ℝ)) →
        HasTriangleDecomposition H)
    (k : ℕ) :
    ∃ n₀ : ℕ, ∀ G : SplitGraph, n₀ ≤ G.n → 12 * G.q < G.p →
      (∀ i : Fin G.q, (2 * (G.n : ℝ) - 1) / 6 + k < (G.d i : ℝ)) →
      ((G.edgeCount : ℝ) - (G.n : ℝ) ^ 2 / 6) / 2 - (G.n : ℝ) ≤ (G.nu3' : ℝ) := by
  obtain ⟨n₀, hpack⟩ := E_8_packing_exists_of_AX2 hAX2 k
  refine ⟨n₀, fun G hn hq hd => ?_⟩
  obtain ⟨T, hT, hcard⟩ := hpack G hn hq hd
  -- ν₃ dominates any packing size.
  have h1 : (T.card : ℝ) ≤ (G.nu3' : ℝ) := by
    have hle := le_nu3_of_packing G.graph hT
    have : (T.card : ℝ) ≤ (nu3 G.graph : ℝ) := by exact_mod_cast hle
    simpa [SplitGraph.nu3'] using this
  -- packing covers all but ≤ 3n edges.
  have h2 : (G.edgeCount : ℝ) ≤ 3 * (T.card : ℝ) + 3 * (G.n : ℝ) := by exact_mod_cast hcard
  -- edgeCount ≤ C(n,2) = (n² − n)/2.
  have h3 : (G.edgeCount : ℝ) ≤ ((G.n : ℝ) ^ 2 - (G.n : ℝ)) / 2 := by
    have hc := edgeCount_le_choose G
    have hcR : (G.edgeCount : ℝ) ≤ (G.n.choose 2 : ℝ) := by exact_mod_cast hc
    rw [Nat.cast_choose_two ℝ] at hcR
    have : (G.n : ℝ) * ((G.n : ℝ) - 1) / 2 = ((G.n : ℝ) ^ 2 - (G.n : ℝ)) / 2 := by ring
    rwa [this] at hcR
  have hn0 : (0 : ℝ) ≤ (G.n : ℝ) := by positivity
  nlinarith [h1, h2, h3, hn0]

/-- The packing estimate at the heart of E-8, WITH the ledger's `O(n)` slack.  In the paper
this is obtained by correcting the clique remainder to a triangle-divisible graph (the parity
part is `pathCorrection_odd_iff`), finding the bounded `C₄`/`C₅` correction inside a Turán
`K₅`, and applying `AX2`.  This is the only residual analytic estimate in the formal
reduction. -/
private theorem E_8_sparse_packing_estimate_of_AX1_AX2
    (hAX1 : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
        (G : SimpleGraph V) (_ : DecidableRel G.Adj),
        n₀ ≤ Fintype.card V →
        tau3Star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2)
    (hAX2 : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
        (H : SimpleGraph V) (_ : DecidableRel H.Adj),
        H.edgeFinset.card % 3 = 0 →
        (∀ v : V, Even (H.degree v)) →
        n₀ ≤ Fintype.card V →
        ((0.9 + ε) * (Fintype.card V : ℝ) ≤ (H.minDegree : ℝ)) →
        HasTriangleDecomposition H)
    (k : ℕ) :
    ∃ n₀ : ℕ, ∀ G : SplitGraph, n₀ ≤ G.n → 2 * G.q ≤ G.p →
      (∀ i : Fin G.q, (2 * (G.n : ℝ) - 1) / 6 + k < (G.d i : ℝ)) →
      ((G.edgeCount : ℝ) - (G.n : ℝ) ^ 2 / 6) / 2 - (G.n : ℝ) ≤ (G.nu3' : ℝ) := by
  -- Residual §8 estimate: construct the corrected dense remainder and invoke AX2.
  obtain ⟨n₁, hn₁⟩ := E_8_very_sparse_packing_estimate_of_AX2 hAX2 k
  obtain ⟨n₁', hn₁'⟩ := E_4_3_of_AX1 hAX1 (1/12) (by norm_num : 0 < (1:ℚ)/12)
  use max n₁ n₁'
  intro G hn hqp hd
  have hn0R : (0 : ℝ) ≤ (G.n : ℝ) := by positivity
  by_cases h : 12 * G.q < G.p
  · exact hn₁ G (le_trans (le_max_left _ _) hn) h hd
  · -- Case: G.p ≤ 10 * G.q, so α = q/p ∈ [1/10, 1/2] (if q > 0)
    -- Use E_4_3 with ε = 1/10
    by_cases hq0 : G.q = 0
    · -- q = 0: From hqp and hq0, G.p = 0. Empty graph, trivial.
      have hp0 : G.p = 0 := by simp [hq0] at hqp; linarith
      have hn0 : G.n = 0 := by simp [SplitGraph.n, hp0, hq0]
      have hgraph : G.graph = ⊥ := by
        apply SimpleGraph.ext
        funext u v
        simp_all [SplitGraph.graph, SplitGraph.Adj]
        rcases u with ⟨a⟩ | ⟨i⟩
        · exact absurd a.isLt (by simp [hp0])
        · exact absurd i.isLt (by simp [hq0])
      have hedge0 : G.edgeCount = 0 := by simp [SplitGraph.edgeCount, hgraph]
      have hnu3_0 : G.nu3' = 0 := by
        simp only [SplitGraph.nu3']
        rw [hgraph]
        apply le_antisymm
        · apply csSup_le
          · use 0
            use ∅
            simp [IsTrianglePacking]
          · rintro x ⟨T, hT, rfl⟩
            simp [IsTrianglePacking] at hT
            rw [Finset.card_eq_zero.mpr (by ext t; simp [hT.1])]
        · exact Nat.zero_le _
      simp [hedge0, hn0, hnu3_0]
    · -- q > 0: Use E_4_3
      -- We have q > 0 and p ≤ 10*q, so α = q/p ∈ [1/10, 1/2]
      -- Prove α ∈ [1/10, 1/2]
      have hq1 : 1 ≤ G.q := Nat.pos_of_ne_zero hq0
      have hα_lo : (1:ℚ)/12 ≤ G.α := by
        rw [SplitGraph.α]
        have hp_pos : 0 < G.p := by omega
        rw [div_le_div_iff₀ (by norm_num : (0:ℚ) < 12) (by exact_mod_cast hp_pos)]
        norm_cast
        omega
      have hα_hi : G.α ≤ 2 - (1:ℚ)/12 := by
        rw [SplitGraph.α]
        have hp_pos : 0 < G.p := by omega
        rw [div_le_iff₀ (by exact_mod_cast hp_pos)]
        have h2 : (G.q : ℚ) ≤ G.p / 2 := by
          have : 2 * (G.q : ℚ) ≤ G.p := by exact_mod_cast hqp
          linarith [show (G.p : ℚ) = G.p from rfl]
        linarith
      specialize hn₁' G (le_trans (le_max_right _ _) hn) hα_lo hα_hi
      -- hn₁' : Φ(G) ≤ n²/6 (strict, stronger than the slack goal), need slack form
      simp [SplitGraph.Phi] at hn₁'
      linarith

/-- **E-8 (Sparse bound), parametrized by AX1** (LEDGER E-8, line 146; uses AX2).  Stated in the form consumed by
the E-9 assembly with the ledger's additive `O(n)` slack: for every `k` there is `n₀` such
that any split graph in the sparse regime `2q ≤ p`, with the minimal-counterexample degree
bound and `n ≥ n₀`, satisfies `Φ(G) ≤ n²/6 + 2·n`. -/
theorem E_8_of_AX1_AX2
    (hAX1 : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
        (G : SimpleGraph V) (_ : DecidableRel G.Adj),
        n₀ ≤ Fintype.card V →
        tau3Star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2)
    (hAX2 : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
        (H : SimpleGraph V) (_ : DecidableRel H.Adj),
        H.edgeFinset.card % 3 = 0 →
        (∀ v : V, Even (H.degree v)) →
        n₀ ≤ Fintype.card V →
        ((0.9 + ε) * (Fintype.card V : ℝ) ≤ (H.minDegree : ℝ)) →
        HasTriangleDecomposition H)
    (k : ℕ) :
    ∃ n₀ : ℕ, ∀ G : SplitGraph, n₀ ≤ G.n → 2 * G.q ≤ G.p →
      (∀ i : Fin G.q, (2 * (G.n : ℝ) - 1) / 6 + k < (G.d i : ℝ)) →
      ((G.Phi : ℤ) : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + 2 * (G.n : ℝ) := by
  obtain ⟨n₀, hpack⟩ := E_8_sparse_packing_estimate_of_AX1_AX2 hAX1 hAX2 k
  refine ⟨n₀, fun G hn hqp hd => ?_⟩
  have h := hpack G hn hqp hd
  rw [SplitGraph.Phi]
  push_cast
  linarith

end PaperIII
