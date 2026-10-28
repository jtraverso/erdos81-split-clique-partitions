/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PaperIII.SplitEdges

/-!
# Paper III — Corridor quantities (inputs to E-5.2 / E-6.1 / E-9)

`bₑ = |{i : e ⊄ Nᵢ}|` (bad count of a clique pair), `V = Σ_{e ∈ E(K)} bₑ(q−bₑ)`
(the dispersion functional of E-5.2), `δ = h/r_p` with `h = min{r_p, q−r_p}`, and
`D = Σ_x a_x(q−a_x)` with `a_x = |{i : x ∈ Sᵢ}|` (the vertex dispersion of §9).
-/

@[expose] public section

namespace PaperIII

namespace SplitGraph

variable (G : SplitGraph)

/-- `bₑ`: the number of independent vertices whose neighborhood misses the clique
pair `e` (defined on `Sym2 (Fin p)`). -/
def badCount (e : Sym2 (Fin G.p)) : ℕ :=
  (Finset.univ.filter fun i : Fin G.q => ¬ ∀ v ∈ e, v ∈ G.N i).card

/-- `V = Σ_{e ∈ E(K)} bₑ (q − bₑ)`, the double-factor dispersion (E-5.2). -/
def dispersionV : ℕ :=
  ∑ e ∈ (⊤ : SimpleGraph (Fin G.p)).edgeFinset, G.badCount e * (G.q - G.badCount e)

/-- `h = min{r_p, q − r_p}`, the number of doubled factors. -/
def doubledFactors : ℕ := min (rp G.p) (G.q - rp G.p)

/-- `a_x = |{i : x ∈ Sᵢ}|`, the miss count of a clique vertex. -/
def missCount (x : Fin G.p) : ℕ :=
  (Finset.univ.filter fun i : Fin G.q => x ∈ G.S i).card

/-- `D = Σ_x a_x (q − a_x)`, the vertex dispersion of the §9 dichotomy. -/
def dispersionD : ℕ := ∑ x, G.missCount x * (G.q - G.missCount x)

end SplitGraph

end PaperIII
