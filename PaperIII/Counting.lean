/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PaperIII.Duality

/-!
# Paper III — Counting lemmas for E-3.1

Edge counts inside vertex subsets of the complete graph, and the three edges of a
triangle.  Pure finite combinatorics supporting the cover-value computations of E-3.1.
-/

@[expose] public section

namespace PaperIII

open Finset

variable {W : Type*} [Fintype W] [DecidableEq W]

/-
The number of edges of the complete graph inside a vertex subset `A` is `C(|A|,2)`.
-/
theorem card_top_edges_within (A : Finset W) :
    (((⊤ : SimpleGraph W).edgeFinset.filter fun e => ∀ v ∈ e, v ∈ A).card)
      = A.card.choose 2 := by
  convert Finset.card_powersetCard 2 A using 1;
  refine' Finset.card_bij ( fun e he => e.toFinset ) _ _ _;
  · simp +contextual [ Sym2.forall, Finset.mem_powersetCard ];
    simp +contextual [ Finset.subset_iff, Sym2.toFinset ];
    simp +contextual [ Sym2.toMultiset, Finset.card_eq_two ];
  · simp +contextual [ Finset.ext_iff, Sym2.ext_iff ];
  · simp +decide [ Finset.mem_powersetCard ];
    intro b hb hb'; obtain ⟨ x, y, hxy ⟩ := Finset.card_eq_two.mp hb'; use s( x, y ) ; aesop;

variable (H : SimpleGraph W) [DecidableRel H.Adj]

/-
The edges of `H` inside a triangle `{x,y,z}` are exactly the three pairs.
-/
theorem edgesIn_triangle {x y z : W} (hxy : H.Adj x y) (hxz : H.Adj x z)
    (hyz : H.Adj y z) :
    edgesIn H {x, y, z} = {s(x, y), s(x, z), s(y, z)} := by
  ext e;
  constructor <;> intro h <;> simp_all +decide [ edgesIn ];
  · rcases e with ⟨ a, b ⟩ ; rcases h.2 a ( by simp +decide ) with ha | ha | ha <;> rcases h.2 b ( by simp +decide ) with hb | hb | hb <;> simp_all +decide [ SimpleGraph.adj_comm ] ;
  · rcases h with ( rfl | rfl | rfl ) <;> simp_all +decide [ SimpleGraph.adj_comm ]

/-
A triangle of `H` contains exactly three edges.
-/
theorem card_edgesIn_triangle {t : Finset W} (ht : t ∈ H.cliqueFinset 3) :
    (edgesIn H t).card = 3 := by
  obtain ⟨x, y, z, hxyz⟩ : ∃ x y z : W, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ t = {x, y, z} := by
    simp_all +decide [ SimpleGraph.mem_cliqueFinset_iff ];
    rcases Finset.card_eq_three.mp ht.2 with ⟨ x, y, z, hxyz ⟩ ; use x, y, by aesop, z ; aesop;
  have h_edges : edgesIn H {x, y, z} = {s(x, y), s(x, z), s(y, z)} := by
    apply edgesIn_triangle; all_goals simp_all +decide [ SimpleGraph.isNClique_iff ];
  simp_all +decide [ Sym2.eq_iff ]

end PaperIII