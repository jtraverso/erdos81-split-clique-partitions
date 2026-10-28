/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Paper III — E-B (Divisibility correction, Appendix B), path-parity part

For the path `x₀ … x_{p−1}` (edges `j — j+1` indexed by `j : Fin (p−1)`) and a set `O`
of even cardinality, the edge set `J = {j : |O ∩ {x₀..x_j}| odd}` has odd-degree
vertex set exactly `O`.  (`|E(J)| ≤ p−1` and `Δ(J) ≤ 2` are immediate from the
encoding: `J` is a set of path-edge indices and each vertex meets at most two.)
-/

@[expose] public section

namespace PaperIII

open Finset

/-- The correcting edge set `J ⊆ {0, …, p−2}`: edge `j` (joining `j` and `j+1`) is
selected iff the prefix `{0..j}` meets `O` an odd number of times. -/
def pathCorrection (p : ℕ) (O : Finset (Fin p)) : Finset (Fin (p - 1)) :=
  Finset.univ.filter fun j => Odd ((O.filter fun x : Fin p => (x : ℕ) ≤ (j : ℕ)).card)

/-- Degree of vertex `v` in the edge set `J` (as path-edge indices). -/
def pathDegree (p : ℕ) (J : Finset (Fin (p - 1))) (v : Fin p) : ℕ :=
  (J.filter fun j : Fin (p - 1) => (v : ℕ) = (j : ℕ) ∨ (v : ℕ) = (j : ℕ) + 1).card

set_option maxHeartbeats 800000 in
/-- **E-B, parity part**: `Odd(J) = O` — a vertex has odd degree in the correcting
edge set iff it lies in `O` (for `|O|` even). -/
theorem pathCorrection_odd_iff (p : ℕ) (O : Finset (Fin p)) (hO : Even O.card)
    (v : Fin p) :
    Odd (pathDegree p (pathCorrection p O) v) ↔ v ∈ O := by
  rcases p with ( _ | _ | p ) <;> simp_all +decide [ pathDegree ];
  · fin_cases v;
  · fin_cases O <;> fin_cases v <;> trivial;
  · by_cases hv : v.val = 0 <;> by_cases hv' : v.val = p + 1 <;> simp_all +decide [ Finset.filter_or ];
    · -- The set of edges incident to vertex 0 is exactly the set of edges where the first vertex is 0.
      have h_incident_0 : Finset.filter (fun j : Fin (p + 1) => (0 : ℕ) = (j : ℕ)) (pathCorrection (p + 2) O) = if 0 ∈ O then {⟨0, by linarith⟩} else ∅ := by
        ext ⟨ j, hj ⟩ ; simp +decide [ pathCorrection ] ;
        split_ifs <;> simp_all +decide;
        · rcases j with ( _ | j ) <;> simp_all +decide [ Finset.filter_eq' ];
        · rintro h rfl; simp_all +decide [ Finset.filter_eq' ] ;
      grind +revert;
    · rw [ Finset.filter_eq_empty_iff.mpr ] <;> simp_all +decide [ pathCorrection ];
      · -- Since $v = p + 1$, we need to show that the number of elements in $O$ that are less than or equal to $p$ is odd if and only if $v \in O$.
        have h_card : Finset.card (Finset.filter (fun x : Fin (p + 2) => x.val ≤ p) O) = Finset.card O - (if v ∈ O then 1 else 0) := by
          rw [ show ( Finset.filter ( fun x : Fin ( p + 2 ) => ( x : ℕ ) ≤ p ) O ) = O \ { v } from ?_, Finset.card_sdiff ] ; aesop;
          grind;
        split_ifs at h_card <;> simp_all +decide;
        · refine' Finset.card_eq_one.mpr _ |> fun h => h.symm ▸ by simp +decide [ parity_simps ] ;
          use ⟨ p, by linarith ⟩ ; ext; simp +decide [ Fin.ext_iff ] ;
          rename_i k; constructor <;> intro hk <;> simp_all +decide ;
          grind +splitIndPred;
        · rw [ Finset.filter_eq_empty_iff.mpr ] <;> norm_num;
          intro x hx; contrapose! hx; simp_all +decide [ Nat.even_iff ] ;
      · grind;
    · -- Let's simplify the expression for the degree of `v` in the edge set `J`.
      have h_deg : ((pathCorrection (p + 2) O).filter (fun j => v.val = j.val ∨ v.val = j.val + 1)).card = ((O.filter (fun x => x.val ≤ v.val)).card % 2) + ((O.filter (fun x => x.val ≤ v.val - 1)).card % 2) := by
        have h_deg : ((pathCorrection (p + 2) O).filter (fun j => v.val = j.val ∨ v.val = j.val + 1)) = {⟨v.val - 1, by
          omega⟩, ⟨v.val, by
          exact lt_of_le_of_ne ( Nat.le_of_lt_succ v.2 ) hv'⟩} ∩ (pathCorrection (p + 2) O) := by
          grind
        generalize_proofs at *;
        grind +locals;
      -- Let's simplify the expression for the cardinality of the set of elements in `O` that are less than or equal to `v`.
      have h_card : ((O.filter (fun x => x.val ≤ v.val)).card) = ((O.filter (fun x => x.val ≤ v.val - 1)).card) + (if v ∈ O then 1 else 0) := by
        rw [ show ( Finset.filter ( fun x : Fin ( p + 2 ) => ( x : ℕ ) ≤ v ) O ) = Finset.filter ( fun x : Fin ( p + 2 ) => ( x : ℕ ) ≤ v - 1 ) O ∪ ( if v ∈ O then { v } else ∅ ) from ?_, Finset.card_union ];
        · split_ifs <;> simp_all +decide;
          grind;
        · grind;
      simp_all +decide [ Finset.filter_or, parity_simps ];
      grind

end PaperIII
