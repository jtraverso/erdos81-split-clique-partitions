/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PaperIII.Counting

/-!
# Paper III — Clique partitions and `cp(G) ≤ Φ(G)` (Corollary 1.2 input)

`cp(G)` = least number of cliques whose vertex sets cover each edge exactly once.
`cp(G) ≤ Φ(G) = |E| − 2ν₃`: a maximum edge-disjoint triangle packing (`ν₃` triangles)
together with the `|E| − 3ν₃` remaining edges as 2-vertex cliques is a clique partition
of size `ν₃ + (|E| − 3ν₃) = |E| − 2ν₃`.
-/

@[expose] public section

namespace PaperIII

open SplitGraph Finset

/-- Clique-partition number: the least number of cliques whose vertex sets cover each
edge of `G` exactly once. -/
noncomputable def SplitGraph.cp (G : SplitGraph) : ℕ :=
  sInf {k | ∃ P : Finset (Finset G.V),
    (∀ c ∈ P, G.graph.IsClique (c : Set G.V)) ∧
    P.card = k ∧
    ∀ e ∈ G.graph.edgeFinset, ∃! c, c ∈ P ∧ ∀ v ∈ e, v ∈ c}

private def coveredEdges {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (T : Finset (Finset W)) : Finset (Sym2 W) :=
  H.edgeFinset.filter fun e => ∃ t ∈ T, ∀ v ∈ e, v ∈ t

private lemma packing_edgesIn_disjoint {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] {T : Finset (Finset W)}
    (hT : IsTrianglePacking H T) {t₁ t₂ : Finset W}
    (ht₁ : t₁ ∈ T) (ht₂ : t₂ ∈ T) (hne : t₁ ≠ t₂) :
    Disjoint (edgesIn H t₁) (edgesIn H t₂) := by
  have h_card : (t₁ ∩ t₂).card ≤ 1 := by
    exact hT.2 ht₁ ht₂ hne;
  rw [ Finset.disjoint_left ];
  intro e he₁ he₂; contrapose! h_card; simp_all +decide [ edgesIn ] ;
  rcases e with ⟨ v, w ⟩ ; simp_all +decide [ Finset.card_le_one ] ;
  exact Finset.one_lt_card.2 ⟨ v, by aesop, w, by aesop ⟩

private lemma card_coveredEdges {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] {T : Finset (Finset W)}
    (hT : IsTrianglePacking H T) :
    (coveredEdges H T).card = 3 * T.card := by
  rw [ show coveredEdges H T = Finset.biUnion T ( fun t => edgesIn H t ) from ?_, Finset.card_biUnion ];
  · rw [ Finset.sum_const_nat ];
    rw [ mul_comm ];
    exact fun t ht => card_edgesIn_triangle H ( hT.1 t ht |> fun h => by simpa using h );
  · exact fun x hx y hy hxy => packing_edgesIn_disjoint H hT hx hy hxy;
  · ext e; simp [coveredEdges, edgesIn];
    grind

private lemma maximum_triangle_packing (G : SplitGraph) :
    ∃ T : Finset (Finset G.V), IsTrianglePacking G.graph T ∧ T.card = G.nu3' := by
  have hne : {k | ∃ T : Finset (Finset G.V), IsTrianglePacking G.graph T ∧ T.card = k}.Nonempty :=
    ⟨0, ∅, by simp [IsTrianglePacking], rfl⟩
  have hbdd : BddAbove {k | ∃ T : Finset (Finset G.V), IsTrianglePacking G.graph T ∧ T.card = k} :=
    ⟨_, fun k hk => by obtain ⟨T, -, rfl⟩ := hk; exact Finset.card_le_univ _⟩
  exact Nat.sSup_mem hne hbdd

set_option maxHeartbeats 800000 in
private lemma packing_gives_clique_partition (G : SplitGraph)
    {T : Finset (Finset G.V)} (hT : IsTrianglePacking G.graph T) :
    ∃ P : Finset (Finset G.V),
      (∀ c ∈ P, G.graph.IsClique (c : Set G.V)) ∧
      P.card = G.edgeCount - 2 * T.card ∧
      ∀ e ∈ G.graph.edgeFinset, ∃! c, c ∈ P ∧ ∀ v ∈ e, v ∈ c := by
  refine' ⟨ T ∪ Finset.image ( fun e => e.toFinset ) ( G.graph.edgeFinset \ Finset.biUnion T ( fun t => edgesIn G.graph t ) ), _, _, _ ⟩;
  · simp_all +decide [ IsTrianglePacking, SimpleGraph.isClique_iff ];
    rintro c ( hc | ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ) <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
    rcases a with ⟨ x, y ⟩ ; simp_all +decide [ SimpleGraph.adj_comm, Set.Pairwise ];
  · rw [ Finset.card_union_of_disjoint, Finset.card_image_of_injOn ];
    · rw [ Finset.card_sdiff ];
      rw [ show ( T.biUnion fun t => edgesIn G.graph t ) ∩ G.graph.edgeFinset = Finset.biUnion T ( fun t => edgesIn G.graph t ) from ?_, Finset.card_biUnion ];
      · rw [ show ∑ u ∈ T, # ( edgesIn G.graph u ) = 3 * T.card from ?_ ];
        · rw [ show G.edgeCount = G.graph.edgeFinset.card from rfl ];
          rw [ ← Nat.add_sub_assoc ];
          · omega;
          · have := card_coveredEdges G.graph hT;
            exact this ▸ Finset.card_le_card ( Finset.filter_subset _ _ );
        · rw [ Finset.sum_congr rfl fun x hx => card_edgesIn_triangle _ <| by have := hT.1 x hx; aesop ] ; simp +decide [ mul_comm ];
      · exact fun x hx y hy hxy => packing_edgesIn_disjoint _ hT hx hy hxy;
      · ext; simp [edgesIn];
        tauto;
    · intro e he e' he' h; simp_all +decide [ Sym2.ext_iff ] ;
      simp_all +decide [ Finset.ext_iff ];
    · simp +decide [ Finset.disjoint_left ];
      intro t ht x hx hx'; contrapose! hx'; simp_all +decide [ edgesIn ] ;
      use t; aesop;
  · intro e he
    by_cases h_covered : e ∈ Finset.biUnion T (fun t => edgesIn G.graph t);
    · obtain ⟨t, ht⟩ : ∃ t ∈ T, e ∈ edgesIn G.graph t := by
        aesop;
      refine' ⟨ t, _, _ ⟩ <;> simp_all +decide;
      · unfold edgesIn at ht; aesop;
      · rintro y ( hy | ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ) hy₁ hy₂ <;> simp_all +decide [ edgesIn ];
        · have := packing_edgesIn_disjoint G.graph hT hy ht.1; simp_all +decide [ Finset.disjoint_left ] ;
          contrapose! this; simp_all +decide [ edgesIn ] ;
          exact ⟨ e, ⟨ he, hy₁, hy₂ ⟩, he, ht.2.1, ht.2.2 ⟩;
        · rcases e with ⟨ x, y ⟩ ; rcases a with ⟨ u, v ⟩ ; simp_all +decide;
          contrapose! ha₂;
          use t;
          cases x <;> cases y <;> aesop;
    · use e.toFinset;
      constructor;
      · cases e ; aesop;
      · intro y hy
        obtain ⟨hyT, hye⟩ := hy
        by_cases hyT' : y ∈ T;
        · exact False.elim <| h_covered <| Finset.mem_biUnion.mpr ⟨ y, hyT', Finset.mem_filter.mpr ⟨ he, hye ⟩ ⟩;
        · obtain ⟨ e', he', rfl ⟩ := Finset.mem_image.mp ( Finset.mem_union.mp hyT |> Or.resolve_left <| by aesop );
          cases e ; cases e' ; simp_all +decide [ Sym2.eq_swap ];
          cases hye.1 <;> cases hye.2 <;> simp_all +decide [ Sym2.eq_swap ]

/-- **`cp(G) ≤ Φ(G)`** (LEDGER Corollary 1.2 input). -/
theorem cp_le_Phi (G : SplitGraph) : (G.cp : ℤ) ≤ G.Phi := by
  obtain ⟨T, hT⟩ := maximum_triangle_packing G;
  obtain ⟨P, hP⟩ := packing_gives_clique_partition G hT.left;
  refine' le_trans ( Nat.cast_le.mpr <| Nat.sInf_le ⟨ P, hP.1, _, hP.2.2 ⟩ ) _;
  exact G.edgeCount - 2 * G.nu3';
  · rw [ hP.2.1, hT.2 ];
  · rw [ Nat.cast_sub ] <;> norm_num [ hT.2, hP.2.1 ];
    · unfold SplitGraph.Phi; norm_num;
    · have h_card_coveredEdges : (coveredEdges G.graph T).card ≤ G.edgeCount := by
        exact Finset.card_le_card ( Finset.filter_subset _ _ );
      linarith [ card_coveredEdges G.graph hT.1 ]

end PaperIII
