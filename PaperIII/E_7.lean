/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PaperIII.CorridorDefs
public import PaperIII.Factorization
public import PaperIII.E_D
public import PaperIII.Duality

/-!
# Paper III — §7 Shifted-center gain completion (E-7.1)

Fix `R ⊆ K`, `ρ=|R|`, `b=|K∖R|`; `Tᵢ=Sᵢ∖R`, `Gᵢ=R∖Sᵢ`; `A_R=Σtᵢ`, `A₂=Σtᵢ²`,
`B_R=Σgᵢ`; `r_b=χ'(K_b)`, `u=q−r_b`; `θ=max{ρ−1,0}/b`; `κ=1−2(1−θ)u/q`.  Under (7.1)
(`b≥2`, `q≥r_b`, `b≥χ'(K_ρ)`) and (7.2) (`b−tᵢ ≥ max{ρ,u}`):
`Φ(G) ≤ n²/6 + p/2 − s²/6 + s·ρ − 2ρ² + κ·B_R + ((s−2ρ−1)A_R − A₂)/q`.

Uses the three edge-disjoint triangle families QQI/IRQ/RRQ; IRQ needs Galvin (E-D.3).
-/

@[expose] public section

namespace PaperIII

set_option maxHeartbeats 800000

open SplitGraph Finset

namespace ShiftedCenter

variable (G : SplitGraph) (R : Finset (Fin G.p))

/-- `tᵢ = |Sᵢ ∖ R|`. -/
def tt (i : Fin G.q) : ℕ := ((G.S i) \ R).card
/-- `gᵢ = |R ∖ Sᵢ|`. -/
def gg (i : Fin G.q) : ℕ := (R \ (G.S i)).card
/-- `A_R = Σ tᵢ`. -/
def AR : ℕ := ∑ i, tt G R i
/-- `A₂ = Σ tᵢ²`. -/
def A2R : ℕ := ∑ i, (tt G R i) ^ 2
/-- `B_R = Σ gᵢ`. -/
def BR : ℕ := ∑ i, gg G R i

end ShiftedCenter

open ShiftedCenter in
/-- Splitting the clique into `R` and its complement gives the basic shifted profile
identity `dᵢ+tᵢ=b+gᵢ`. -/
theorem degree_add_tt_eq (G : SplitGraph) (R : Finset (Fin G.p)) (i : Fin G.q) :
    G.d i + tt G R i = (G.p - R.card) + gg G R i := by
  have h_card_S : G.p = G.d i + (G.S i).card := by
    unfold SplitGraph.d SplitGraph.S; simp +decide;
  have h_card_R : R.card = (R \ G.S i).card + (R ∩ G.S i).card := by
    rw [ Finset.card_sdiff_add_card_inter ];
  have h_card_S_R : (G.S i).card = ((G.S i) \ R).card + (R ∩ G.S i).card := by
    grind;
  unfold tt gg;
  linarith [ Nat.sub_add_cancel ( show #R ≤ G.p from le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ) ]

open ShiftedCenter in
/-- The corresponding identity for the total number of edges. -/
theorem edgeCount_shifted (G : SplitGraph) (R : Finset (Fin G.p)) :
    G.edgeCount + AR G R = G.p.choose 2 + G.q * (G.p - R.card) + BR G R := by
  rw [ edgeCount_eq, ShiftedCenter.AR, ShiftedCenter.BR ];
  have := fun i => degree_add_tt_eq G R i;
  simp +arith +decide [ ← Finset.sum_add_distrib, this ];
  simp +arith +decide [ Finset.sum_add_distrib ]

open ShiftedCenter in
private lemma card_clique_complement (G : SplitGraph) (R : Finset (Fin G.p)) :
    Fintype.card {x : Fin G.p // x ∉ R} = G.p - R.card := by
  rw [ Fintype.card_subtype ];
  rw [ Finset.filter_not, Finset.card_sdiff ] ; norm_num

open ShiftedCenter in
private lemma card_available_Q (G : SplitGraph) (R : Finset (Fin G.p)) (i : Fin G.q) :
    Fintype.card {x : Fin G.p // x ∉ R ∧ x ∈ G.N i} =
      G.p - R.card - tt G R i := by
  rw [ Fintype.card_subtype ];
  rw [ show ( Finset.filter ( fun x => x ∉ R ∧ x ∈ G.N i ) Finset.univ : Finset ( Fin G.p ) ) = ( Finset.univ \ R ) \ ( G.S i \ R ) from ?_, Finset.card_sdiff ];
  · simp +decide [ Finset.card_sdiff, Finset.subset_iff ];
    congr 2 ; ext ; aesop;
  · ext x; simp [SplitGraph.S];
    grind

open ShiftedCenter in
private lemma card_reserved_gain (G : SplitGraph) (R : Finset (Fin G.p)) (i : Fin G.q) :
    Fintype.card {x : Fin G.p // x ∈ R ∧ x ∈ G.N i} = gg G R i := by
  rw [ Fintype.card_subtype ] ; congr ; ext ; simp +decide [ SplitGraph.S ] ;

private lemma qqi_isTriangle (G : SplitGraph) {a b : Fin G.p} {i : Fin G.q}
    (hab : a ≠ b) (ha : a ∈ G.N i) (hb : b ∈ G.N i) :
    G.graph.IsNClique 3 {Sum.inl a, Sum.inl b, Sum.inr i} := by
  rw [ SimpleGraph.isNClique_iff ];
  simp +decide [ *, SimpleGraph.isClique_iff, Set.Pairwise ];
  exact ⟨ ⟨ by tauto, by tauto ⟩, ⟨ fun _ => by tauto, by tauto ⟩, by tauto, by tauto ⟩

private lemma rrq_isTriangle (G : SplitGraph) {a b c : Fin G.p}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    G.graph.IsNClique 3 {Sum.inl a, Sum.inl b, Sum.inl c} := by
  constructor;
  · unfold SplitGraph.graph; aesop;
  · grind

private lemma irq_isTriangle (G : SplitGraph) {x y : Fin G.p} {i : Fin G.q}
    (hxy : x ≠ y) (hx : x ∈ G.N i) (hy : y ∈ G.N i) :
    G.graph.IsNClique 3 {Sum.inl x, Sum.inl y, Sum.inr i} := by
  exact qqi_isTriangle G hxy hx hy

private lemma IsTrianglePacking.union_of_cross
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    {T₁ T₂ : Finset (Finset W)}
    (h₁ : IsTrianglePacking H T₁) (h₂ : IsTrianglePacking H T₂)
    (hcross : ∀ t₁ ∈ T₁, ∀ t₂ ∈ T₂, (t₁ ∩ t₂).card ≤ 1) :
    IsTrianglePacking H (T₁ ∪ T₂) := by
  constructor;
  · exact fun t ht => by cases Finset.mem_union.mp ht <;> [ exact h₁.1 t ‹_›; exact h₂.1 t ‹_› ] ;
  · intro t₁ ht₁ t₂ ht₂ hne; cases' Finset.mem_union.mp ht₁ with ht₁ ht₁ <;> cases' Finset.mem_union.mp ht₂ with ht₂ ht₂ <;> simp_all +decide [ IsTrianglePacking ] ;
    · exact h₁.2 ht₁ ht₂ hne;
    · simpa only [ Finset.inter_comm ] using hcross _ ht₂ _ ht₁;
    · exact h₂.2 ht₁ ht₂ hne

private lemma card_union_of_disjoint
    {α : Type*} [DecidableEq α] {A B : Finset α} (h : Disjoint A B) :
    (A ∪ B).card = A.card + B.card := by
  exact Finset.card_union_of_disjoint h

private lemma complete_graph_edge_coloring_fintype
    (A : Type*) [Fintype A] [DecidableEq A] :
    ∃ phi : Sym2 A → ℕ,
      (∀ e ∈ (⊤ : SimpleGraph A).edgeFinset, phi e < rp (Fintype.card A)) ∧
      ∀ e ∈ (⊤ : SimpleGraph A).edgeFinset,
        ∀ f ∈ (⊤ : SimpleGraph A).edgeFinset,
          e ≠ f → (∃ v, v ∈ e ∧ v ∈ f) → phi e ≠ phi f := by
  obtain ⟨phi, hphi⟩ : ∃ phi : Sym2 (Fin (Fintype.card A)) → ℕ,
      (∀ e ∈ (⊤ : SimpleGraph (Fin (Fintype.card A))).edgeFinset, phi e < rp (Fintype.card A)) ∧
      ∀ e ∈ (⊤ : SimpleGraph (Fin (Fintype.card A))).edgeFinset,
        ∀ f ∈ (⊤ : SimpleGraph (Fin (Fintype.card A))).edgeFinset,
          e ≠ f → (∃ v, v ∈ e ∧ v ∈ f) → phi e ≠ phi f := by
    exact complete_graph_edge_coloring (Fintype.card A)
  refine' ⟨ fun e => phi ( Sym2.map ( Fintype.equivFin A ) e ), _, _ ⟩;
  · intro e he; specialize hphi; have := hphi.1 ( Sym2.map ( Fintype.equivFin A ) e ) ; simp_all +decide [ SimpleGraph.edgeFinset ] ;
    cases e ; aesop;
  · intro e he f hf hne h;
    convert hphi.2 _ _ _ _ _ _ using 1;
    · cases e ; cases f ; aesop;
    · cases f ; aesop;
    · exact fun h' => hne <| Sym2.map.injective ( Fintype.equivFin A ).injective h';
    · rcases h with ⟨ v, hv₁, hv₂ ⟩ ; use Fintype.equivFin A v; aesop;

private lemma rp_pos_of_two_le {b : ℕ} (hb : 2 ≤ b) : 0 < rp b := by
  unfold rp;
  grind

private lemma pred_le_of_rp_le {rho b : ℕ} (h : rp rho ≤ b) : rho - 1 ≤ b := by
  unfold rp at h; rcases rho with ( _ | _ | rho ) <;> simp_all +arith +decide;
  grind

private lemma q_pos_of_rp_le {b q : ℕ} (hb : 2 ≤ b) (h : rp b ≤ q) : 0 < q := by
  exact lt_of_lt_of_le (rp_pos_of_two_le hb) h

/-- Factor edges of the `R`-complement clique that are available to `i` (both endpoints
in `N i`), of colour `c`. -/
private def qFactorEdges (G : SplitGraph) (R : Finset (Fin G.p))
    (φ : Sym2 {x : Fin G.p // x ∉ R} → ℕ)
    (c : Fin (rp (Fintype.card {x : Fin G.p // x ∉ R}))) (i : Fin G.q) :
    Finset (Sym2 {x : Fin G.p // x ∉ R}) :=
  (⊤ : SimpleGraph {x : Fin G.p // x ∉ R}).edgeFinset.filter
    fun e => φ e = c.1 ∧ ∀ v ∈ e, v.val ∈ G.N i

/-- The QQI triangle from a factor edge `{u,v}` of the `R`-complement clique together
with the independent vertex `i`. -/
private def qTriangle (G : SplitGraph) (R : Finset (Fin G.p)) (i : Fin G.q)
    (e : Sym2 {x : Fin G.p // x ∉ R}) : Finset G.V :=
  insert (Sum.inr i) (e.toFinset.image (fun v => Sum.inl v.val))

/-- The full QQI family assigned by a colouring `φ` and an injection `σ` of colours into
independent vertices. -/
private def qAssignedTriangles (G : SplitGraph) (R : Finset (Fin G.p))
    (φ : Sym2 {x : Fin G.p // x ∉ R} → ℕ)
    (σ : Fin (rp (Fintype.card {x : Fin G.p // x ∉ R})) ↪ Fin G.q) :
    Finset (Finset G.V) :=
  Finset.univ.biUnion fun c =>
    (qFactorEdges G R φ c (σ c)).image (qTriangle G R (σ c))

private lemma qAssignedTriangles_isPacking (G : SplitGraph) (R : Finset (Fin G.p))
    (φ : Sym2 {x : Fin G.p // x ∉ R} → ℕ)
    (hproper : ∀ e ∈ (⊤ : SimpleGraph {x : Fin G.p // x ∉ R}).edgeFinset,
      ∀ f ∈ (⊤ : SimpleGraph {x : Fin G.p // x ∉ R}).edgeFinset,
        e ≠ f → (∃ v, v ∈ e ∧ v ∈ f) → φ e ≠ φ f)
    (σ : Fin (rp (Fintype.card {x : Fin G.p // x ∉ R})) ↪ Fin G.q) :
    IsTrianglePacking G.graph (qAssignedTriangles G R φ σ) := by
  have hmemT : ∀ (c : Fin (rp (Fintype.card {x : Fin G.p // x ∉ R})))
      (e : Sym2 {x : Fin G.p // x ∉ R}) (z : G.V),
      z ∈ qTriangle G R (σ c) e ↔ z = Sum.inr (σ c) ∨ ∃ w ∈ e, z = Sum.inl w.val := by
    intro c e z
    simp only [qTriangle, Finset.mem_insert, Finset.mem_image, Sym2.mem_toFinset]
    constructor
    · rintro (rfl | ⟨w, hw, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨w, hw, rfl⟩
    · rintro (rfl | ⟨w, hw, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨w, hw, rfl⟩
  refine ⟨?_, ?_⟩
  · intro t ht
    simp only [qAssignedTriangles, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ,
      true_and] at ht
    obtain ⟨c, e, he, rfl⟩ := ht
    rcases e with ⟨a, b⟩
    unfold qFactorEdges at he
    rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
      SimpleGraph.top_adj] at he
    have hab : a ≠ b := he.1
    have ha : a.val ∈ G.N (σ c) := he.2.2 a (by simp [Sym2.mem_iff])
    have hb : b.val ∈ G.N (σ c) := he.2.2 b (by simp [Sym2.mem_iff])
    have hval : a.val ≠ b.val := fun hh => hab (Subtype.ext hh)
    have htri := qqi_isTriangle G hval ha hb
    have hset : qTriangle G R (σ c) (s(a, b))
        = ({Sum.inl a.val, Sum.inl b.val, Sum.inr (σ c)} : Finset G.V) := by
      ext z
      rw [hmemT]
      simp only [Sym2.mem_iff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (rfl | ⟨w, (rfl | rfl), rfl⟩) <;> tauto
      · rintro (rfl | rfl | rfl)
        · exact Or.inr ⟨a, Or.inl rfl, rfl⟩
        · exact Or.inr ⟨b, Or.inr rfl, rfl⟩
        · exact Or.inl rfl
    rw [hset]; exact htri
  · intro t₁ ht₁ t₂ ht₂ hne
    obtain ⟨c₁, e₁, rfl, he₁⟩ : ∃ c₁ e₁, t₁ = qTriangle G R (σ c₁) e₁ ∧
        e₁ ∈ qFactorEdges G R φ c₁ (σ c₁) := by
      unfold qAssignedTriangles at ht₁; aesop
    obtain ⟨c₂, e₂, rfl, he₂⟩ : ∃ c₂ e₂, t₂ = qTriangle G R (σ c₂) e₂ ∧
        e₂ ∈ qFactorEdges G R φ c₂ (σ c₂) := by
      unfold qAssignedTriangles at ht₂; aesop
    have hc₁ : φ e₁ = c₁.1 ∧ e₁ ∈ (⊤ : SimpleGraph {x : Fin G.p // x ∉ R}).edgeFinset := by
      unfold qFactorEdges at he₁; rw [Finset.mem_filter] at he₁; exact ⟨he₁.2.1, he₁.1⟩
    have hc₂ : φ e₂ = c₂.1 ∧ e₂ ∈ (⊤ : SimpleGraph {x : Fin G.p // x ∉ R}).edgeFinset := by
      unfold qFactorEdges at he₂; rw [Finset.mem_filter] at he₂; exact ⟨he₂.2.1, he₂.1⟩
    have hedgene : e₁ ≠ e₂ := by
      rintro rfl
      have : c₁ = c₂ := Fin.ext (hc₁.1 ▸ hc₂.1)
      subst this; exact hne rfl
    have hsamecol_disj : c₁ = c₂ → ∀ w : {x : Fin G.p // x ∉ R}, w ∈ e₁ → w ∈ e₂ → False := by
      intro hcc w hw1 hw2
      exact absurd (hc₁.1.trans (hcc ▸ hc₂.1).symm)
        (hproper e₁ hc₁.2 e₂ hc₂.2 hedgene ⟨w, hw1, hw2⟩)
    have hedge_eq : ∀ (e : Sym2 {x : Fin G.p // x ∉ R}) (u v : {x : Fin G.p // x ∉ R}),
        u ≠ v → u ∈ e → v ∈ e → e = s(u, v) := by
      intro e u v huv hu hv
      rcases e with ⟨a, b⟩
      simp only [Sym2.mem_iff] at hu hv
      rw [Sym2.eq_iff]
      rcases hu with hu | hu <;> rcases hv with hv | hv
      · exact absurd (hu.trans hv.symm) huv
      · exact Or.inl ⟨hu.symm, hv.symm⟩
      · exact Or.inr ⟨hv.symm, hu.symm⟩
      · exact absurd (hu.trans hv.symm) huv
    have hshare : ∀ u v : {x : Fin G.p // x ∉ R}, u ∈ e₁ → u ∈ e₂ → v ∈ e₁ → v ∈ e₂ → u = v := by
      intro u v hu1 hu2 hv1 hv2
      by_contra huv
      exact hedgene ((hedge_eq e₁ u v huv hu1 hv1).trans (hedge_eq e₂ u v huv hu2 hv2).symm)
    have hclass : ∀ z : G.V, (z = Sum.inr (σ c₁) ∨ ∃ w ∈ e₁, z = Sum.inl w.val) →
        (z = Sum.inr (σ c₂) ∨ ∃ w ∈ e₂, z = Sum.inl w.val) →
        (z = Sum.inr (σ c₁) ∧ σ c₁ = σ c₂) ∨
          (∃ w, w ∈ e₁ ∧ w ∈ e₂ ∧ z = Sum.inl w.val) := by
      intro z h1 h2
      rcases h1 with rfl | ⟨w, hw1, rfl⟩
      · rcases h2 with h2 | ⟨w, hw2, h2⟩
        · exact Or.inl ⟨rfl, Sum.inr_injective h2⟩
        · exact absurd h2.symm (by simp)
      · rcases h2 with h2 | ⟨w', hw2, h2⟩
        · exact absurd h2 (by simp)
        · have hww : w = w' := Subtype.ext (by simpa using h2)
          exact Or.inr ⟨w, hw1, hww ▸ hw2, rfl⟩
    rw [Finset.card_le_one]
    intro z hz z' hz'
    simp only [Finset.mem_inter, hmemT] at hz hz'
    obtain ⟨Hz1, Hz2⟩ := hz
    obtain ⟨Hz1', Hz2'⟩ := hz'
    have Hz := hclass z Hz1 Hz2
    have Hz' := hclass z' Hz1' Hz2'
    rcases Hz with ⟨rfl, hσ⟩ | ⟨w, hw1, hw2, rfl⟩
    · rcases Hz' with ⟨rfl, _⟩ | ⟨w', hw1', hw2', rfl⟩
      · rfl
      · exact (hsamecol_disj (σ.injective hσ) w' hw1' hw2').elim
    · rcases Hz' with ⟨rfl, hσ⟩ | ⟨w', hw1', hw2', rfl⟩
      · exact (hsamecol_disj (σ.injective hσ) w hw1 hw2).elim
      · rw [hshare w w' hw1 hw2 hw1' hw2']

private lemma card_qAssignedTriangles (G : SplitGraph) (R : Finset (Fin G.p))
    (φ : Sym2 {x : Fin G.p // x ∉ R} → ℕ)
    (σ : Fin (rp (Fintype.card {x : Fin G.p // x ∉ R})) ↪ Fin G.q) :
    (qAssignedTriangles G R φ σ).card =
      ∑ c, (qFactorEdges G R φ c (σ c)).card := by
  unfold qAssignedTriangles
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro c _
    rw [Finset.card_image_of_injOn]
    intro e₁ he₁ e₂ he₂ h_eq
    unfold qTriangle at h_eq
    have h1 : (Sum.inr (σ c) : G.V) ∉ e₁.toFinset.image (fun v : {x : Fin G.p // x ∉ R} => (Sum.inl v.val : G.V)) := by
      simp
    have h2 : (Sum.inr (σ c) : G.V) ∉ e₂.toFinset.image (fun v : {x : Fin G.p // x ∉ R} => (Sum.inl v.val : G.V)) := by
      simp
    have himg : e₁.toFinset.image (fun v : {x : Fin G.p // x ∉ R} => (Sum.inl v.val : G.V))
        = e₂.toFinset.image (fun v : {x : Fin G.p // x ∉ R} => (Sum.inl v.val : G.V)) := by
      rw [← Finset.erase_insert h1, ← Finset.erase_insert h2, h_eq]
    have hinj : Function.Injective (fun v : {x : Fin G.p // x ∉ R} => (Sum.inl v.val : G.V)) := by
      intro u v huv; exact Subtype.ext (by simpa using huv)
    have htf : e₁.toFinset = e₂.toFinset :=
      Finset.image_injective hinj himg
    have hmem : ∀ v, v ∈ e₁ ↔ v ∈ e₂ := by
      intro v; simpa [Sym2.mem_toFinset] using Finset.ext_iff.mp htf v
    rcases e₁ with ⟨a, b⟩; rcases e₂ with ⟨x, y⟩
    have hab : a ≠ b := by
      rintro rfl
      simp [qFactorEdges] at he₁
    simp only [Sym2.mem_iff] at hmem
    rw [Sym2.eq_iff]
    have ha := (hmem a).mp (Or.inl rfl)
    have hb := (hmem b).mp (Or.inr rfl)
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp_all
  · intro c hc d hd hcd; simp_all +decide [ Finset.disjoint_left, qTriangle ]
    intro a ha x hx; intro H; replace H := Finset.ext_iff.mp H (Sum.inr (σ d)); simp_all +decide

open ShiftedCenter in
private lemma sum_qFactorEdges_card (G : SplitGraph) (R : Finset (Fin G.p))
    (φ : Sym2 {x : Fin G.p // x ∉ R} → ℕ)
    (hbound : ∀ e ∈ (⊤ : SimpleGraph {x : Fin G.p // x ∉ R}).edgeFinset,
      φ e < rp (Fintype.card {x : Fin G.p // x ∉ R}))
    (i : Fin G.q) :
    ∑ c, (qFactorEdges G R φ c i).card =
      (G.p - R.card - tt G R i).choose 2 := by
  have havail : (Finset.univ.filter (fun v : {x : Fin G.p // x ∉ R} => v.val ∈ G.N i)).card
      = G.p - R.card - tt G R i := by
    rw [← card_available_Q G R i, Fintype.card_subtype]
    apply Finset.card_bij (fun (v : {x : Fin G.p // x ∉ R}) _ => v.val)
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      exact ⟨v.property, hv⟩
    · intro v _ w _ h; exact Subtype.ext h
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      exact ⟨⟨b, hb.1⟩, by simp [Finset.mem_filter, hb.2], rfl⟩
  rw [← havail, ← Finset.card_biUnion]
  · rw [← Finset.card_powersetCard 2
      (Finset.univ.filter (fun v : {x : Fin G.p // x ∉ R} => v.val ∈ G.N i))]
    apply Finset.card_bij (fun e _ => e.toFinset)
    · intro a ha
      rcases a with ⟨p, q⟩
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at ha
      obtain ⟨c, hc⟩ := ha
      unfold qFactorEdges at hc
      rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        SimpleGraph.top_adj] at hc
      rw [Finset.mem_powersetCard]
      refine ⟨?_, ?_⟩
      · intro v hv
        simp only [Sym2.mem_toFinset] at hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hc.2.2 v hv
      · have htf : (s(p, q)).toFinset = {p, q} := by
          ext z; simp [Sym2.mem_toFinset, Sym2.mem_iff]
        simp only [htf]
        exact Finset.card_pair hc.1
    · intro a₁ ha₁ a₂ ha₂ h
      rcases a₁ with ⟨p, q⟩; rcases a₂ with ⟨r, s⟩
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at ha₁
      obtain ⟨c, hc⟩ := ha₁
      unfold qFactorEdges at hc
      rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        SimpleGraph.top_adj] at hc
      have hpq : p ≠ q := hc.1
      have hmem : ∀ z, z ∈ (s(p, q)) ↔ z ∈ (s(r, s)) := by
        intro z; simpa [Sym2.mem_toFinset] using Finset.ext_iff.mp h z
      simp only [Sym2.mem_iff] at hmem
      rw [Sym2.eq_iff]
      have hp := (hmem p).mp (Or.inl rfl)
      have hq := (hmem q).mp (Or.inr rfl)
      rcases hp with hp | hp <;> rcases hq with hq | hq <;> simp_all
    · intro b hb
      rw [Finset.mem_powersetCard] at hb
      obtain ⟨hsub, hcard⟩ := hb
      obtain ⟨x, y, hne, rfl⟩ := Finset.card_eq_two.mp hcard
      have hxi : x.val ∈ G.N i := by
        have := hsub (Finset.mem_insert_self x {y})
        simpa [Finset.mem_filter] using this
      have hyi : y.val ∈ G.N i := by
        have := hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
        simpa [Finset.mem_filter] using this
      have hmem : s(x, y) ∈ (⊤ : SimpleGraph {x : Fin G.p // x ∉ R}).edgeFinset := by
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.top_adj]; exact hne
      refine ⟨s(x, y), ?_, ?_⟩
      · rw [Finset.mem_biUnion]
        refine ⟨⟨φ (s(x, y)), hbound _ hmem⟩, Finset.mem_univ _, ?_⟩
        unfold qFactorEdges
        rw [Finset.mem_filter]
        exact ⟨hmem, rfl, fun v hv => by
          rw [Sym2.mem_iff] at hv; rcases hv with rfl | rfl <;> assumption⟩
      · show (s(x, y)).toFinset = {x, y}
        ext z; simp [Sym2.mem_toFinset, Sym2.mem_iff, Finset.mem_insert, Finset.mem_singleton]
  · intros c hc d hd hcd; simp_all +decide [ Finset.disjoint_left, qFactorEdges ]
    exact fun e he₁ he₂ he₃ => by simpa [ Fin.ext_iff ] using hcd

open ShiftedCenter in
/-- **QQI averaged family**: there is a triangle packing of `G.graph` whose size is at
least the averaged QQI count `(1/q) Σᵢ C(b - tᵢ, 2)`. -/
private lemma qqi_family (G : SplitGraph) (R : Finset (Fin G.p))
    (hb2 : 2 ≤ G.p - R.card)
    (hqrb : rp (G.p - R.card) ≤ G.q)
    (h72 : ∀ i, max R.card (G.q - rp (G.p - R.card)) ≤ (G.p - R.card) - tt G R i) :
    ∃ T : Finset (Finset G.V), IsTrianglePacking G.graph T ∧
      (1 / (G.q : ℝ)) * ∑ i, (((G.p - R.card - tt G R i).choose 2 : ℕ) : ℝ) ≤ (T.card : ℝ) := by
  classical
  obtain ⟨φ, hbound, hproper⟩ := complete_graph_edge_coloring_fintype {x : Fin G.p // x ∉ R}
  have hcardA : Fintype.card {x : Fin G.p // x ∉ R} = G.p - R.card := card_clique_complement G R
  have hq : 0 < G.q := q_pos_of_rp_le hb2 hqrb
  set f : Fin (rp (Fintype.card {x : Fin G.p // x ∉ R})) → Fin G.q → ℝ :=
    fun c i => ((qFactorEdges G R φ c i).card : ℝ) with hf
  obtain ⟨σ, hσ⟩ := exists_injection_ge_mean f
    (by simp only [Fintype.card_fin, hcardA]; exact hqrb)
    (by simp only [Fintype.card_fin]; exact hq)
  refine ⟨qAssignedTriangles G R φ σ, qAssignedTriangles_isPacking G R φ hproper σ, ?_⟩
  have hTcard : ((qAssignedTriangles G R φ σ).card : ℝ) = ∑ c, f c (σ c) := by
    rw [card_qAssignedTriangles, Nat.cast_sum]
  have hsum : ∑ c, ∑ i, f c i = ∑ i, (((G.p - R.card - tt G R i).choose 2 : ℕ) : ℝ) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have h := sum_qFactorEdges_card G R φ hbound i
    simp only [hf]
    rw [← Nat.cast_sum, h]
  rw [hTcard]
  calc (1 / (G.q : ℝ)) * ∑ i, (((G.p - R.card - tt G R i).choose 2 : ℕ) : ℝ)
      = (1 / (G.q : ℝ)) * ∑ c, ∑ i, f c i := by rw [hsum]
    _ ≤ ∑ c, f c (σ c) := by rw [Fintype.card_fin] at hσ; exact hσ

/-- Edges of the reserved clique `K[R]` (on the subtype `{x // x ∈ R}`) of colour `c`. -/
private def rrqFactorEdges (G : SplitGraph) (R : Finset (Fin G.p))
    (φ : Sym2 {x : Fin G.p // x ∈ R} → ℕ)
    (c : Fin (rp (Fintype.card {x : Fin G.p // x ∈ R}))) :
    Finset (Sym2 {x : Fin G.p // x ∈ R}) :=
  (⊤ : SimpleGraph {x : Fin G.p // x ∈ R}).edgeFinset.filter fun e => φ e = c.1

/-- The RRQ triangle from a reserved edge `{a,b} ⊆ R` together with a complement
vertex `v ∉ R` used as the third clique vertex. -/
private def rrqTriangle (G : SplitGraph) (R : Finset (Fin G.p)) (v : Fin G.p)
    (e : Sym2 {x : Fin G.p // x ∈ R}) : Finset G.V :=
  insert (Sum.inl v) (e.toFinset.image (fun w => Sum.inl w.val))

/-- The full RRQ family assigned by a colouring `φ` of the reserved clique and an
injection `σ` of colours into complement vertices. -/
private def rrqAssignedTriangles (G : SplitGraph) (R : Finset (Fin G.p))
    (φ : Sym2 {x : Fin G.p // x ∈ R} → ℕ)
    (σ : Fin (rp (Fintype.card {x : Fin G.p // x ∈ R})) ↪ {x : Fin G.p // x ∉ R}) :
    Finset (Finset G.V) :=
  Finset.univ.biUnion fun c =>
    (rrqFactorEdges G R φ c).image (rrqTriangle G R (σ c).val)

private lemma card_reserved_subtype (G : SplitGraph) (R : Finset (Fin G.p)) :
    Fintype.card {x : Fin G.p // x ∈ R} = R.card := by
  simp [Fintype.card_subtype]

private lemma rrqAssignedTriangles_isPacking (G : SplitGraph) (R : Finset (Fin G.p))
    (φ : Sym2 {x : Fin G.p // x ∈ R} → ℕ)
    (hproper : ∀ e ∈ (⊤ : SimpleGraph {x : Fin G.p // x ∈ R}).edgeFinset,
      ∀ f ∈ (⊤ : SimpleGraph {x : Fin G.p // x ∈ R}).edgeFinset,
        e ≠ f → (∃ v, v ∈ e ∧ v ∈ f) → φ e ≠ φ f)
    (σ : Fin (rp (Fintype.card {x : Fin G.p // x ∈ R})) ↪ {x : Fin G.p // x ∉ R}) :
    IsTrianglePacking G.graph (rrqAssignedTriangles G R φ σ) := by
  classical
  have hmemT : ∀ (c : Fin (rp (Fintype.card {x : Fin G.p // x ∈ R})))
      (e : Sym2 {x : Fin G.p // x ∈ R}) (z : G.V),
      z ∈ rrqTriangle G R (σ c).val e ↔
        z = Sum.inl (σ c).val ∨ ∃ w ∈ e, z = Sum.inl w.val := by
    intro c e z
    simp only [rrqTriangle, Finset.mem_insert, Finset.mem_image, Sym2.mem_toFinset]
    constructor
    · rintro (rfl | ⟨w, hw, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨w, hw, rfl⟩
    · rintro (rfl | ⟨w, hw, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨w, hw, rfl⟩
  refine ⟨?_, ?_⟩
  · intro t ht
    simp only [rrqAssignedTriangles, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ,
      true_and] at ht
    obtain ⟨c, e, he, rfl⟩ := ht
    rcases e with ⟨a, b⟩
    unfold rrqFactorEdges at he
    rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
      SimpleGraph.top_adj] at he
    have hab : a ≠ b := he.1
    have hval : a.val ≠ b.val := fun hh => hab (Subtype.ext hh)
    have hane : a.val ≠ (σ c).val := fun hh => (σ c).property (hh ▸ a.property)
    have hbne : b.val ≠ (σ c).val := fun hh => (σ c).property (hh ▸ b.property)
    have htri := rrq_isTriangle G hval hane hbne
    have hset : rrqTriangle G R (σ c).val (s(a, b))
        = ({Sum.inl a.val, Sum.inl b.val, Sum.inl (σ c).val} : Finset G.V) := by
      ext z
      rw [hmemT]
      simp only [Sym2.mem_iff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (rfl | ⟨w, (rfl | rfl), rfl⟩) <;> tauto
      · rintro (rfl | rfl | rfl)
        · exact Or.inr ⟨a, Or.inl rfl, rfl⟩
        · exact Or.inr ⟨b, Or.inr rfl, rfl⟩
        · exact Or.inl rfl
    rw [hset]; exact htri
  · intro t₁ ht₁ t₂ ht₂ hne
    obtain ⟨c₁, e₁, rfl, he₁⟩ : ∃ c₁ e₁, t₁ = rrqTriangle G R (σ c₁).val e₁ ∧
        e₁ ∈ rrqFactorEdges G R φ c₁ := by
      unfold rrqAssignedTriangles at ht₁; aesop
    obtain ⟨c₂, e₂, rfl, he₂⟩ : ∃ c₂ e₂, t₂ = rrqTriangle G R (σ c₂).val e₂ ∧
        e₂ ∈ rrqFactorEdges G R φ c₂ := by
      unfold rrqAssignedTriangles at ht₂; aesop
    have hc₁ : φ e₁ = c₁.1 ∧ e₁ ∈ (⊤ : SimpleGraph {x : Fin G.p // x ∈ R}).edgeFinset := by
      unfold rrqFactorEdges at he₁; rw [Finset.mem_filter] at he₁; exact ⟨he₁.2, he₁.1⟩
    have hc₂ : φ e₂ = c₂.1 ∧ e₂ ∈ (⊤ : SimpleGraph {x : Fin G.p // x ∈ R}).edgeFinset := by
      unfold rrqFactorEdges at he₂; rw [Finset.mem_filter] at he₂; exact ⟨he₂.2, he₂.1⟩
    have hedgene : e₁ ≠ e₂ := by
      rintro rfl
      have : c₁ = c₂ := Fin.ext (hc₁.1 ▸ hc₂.1)
      subst this; exact hne rfl
    have hsamecol_disj : c₁ = c₂ → ∀ w : {x : Fin G.p // x ∈ R}, w ∈ e₁ → w ∈ e₂ → False := by
      intro hcc w hw1 hw2
      exact absurd (hc₁.1.trans (hcc ▸ hc₂.1).symm)
        (hproper e₁ hc₁.2 e₂ hc₂.2 hedgene ⟨w, hw1, hw2⟩)
    have hedge_eq : ∀ (e : Sym2 {x : Fin G.p // x ∈ R}) (u v : {x : Fin G.p // x ∈ R}),
        u ≠ v → u ∈ e → v ∈ e → e = s(u, v) := by
      intro e u v huv hu hv
      rcases e with ⟨a, b⟩
      simp only [Sym2.mem_iff] at hu hv
      rw [Sym2.eq_iff]
      rcases hu with hu | hu <;> rcases hv with hv | hv
      · exact absurd (hu.trans hv.symm) huv
      · exact Or.inl ⟨hu.symm, hv.symm⟩
      · exact Or.inr ⟨hv.symm, hu.symm⟩
      · exact absurd (hu.trans hv.symm) huv
    have hshare : ∀ u v : {x : Fin G.p // x ∈ R}, u ∈ e₁ → u ∈ e₂ → v ∈ e₁ → v ∈ e₂ → u = v := by
      intro u v hu1 hu2 hv1 hv2
      by_contra huv
      exact hedgene ((hedge_eq e₁ u v huv hu1 hv1).trans (hedge_eq e₂ u v huv hu2 hv2).symm)
    have hclass : ∀ z : G.V, (z = Sum.inl (σ c₁).val ∨ ∃ w ∈ e₁, z = Sum.inl w.val) →
        (z = Sum.inl (σ c₂).val ∨ ∃ w ∈ e₂, z = Sum.inl w.val) →
        (z = Sum.inl (σ c₁).val ∧ (σ c₁).val = (σ c₂).val) ∨
          (∃ w, w ∈ e₁ ∧ w ∈ e₂ ∧ z = Sum.inl w.val) := by
      intro z h1 h2
      rcases h1 with rfl | ⟨w, hw1, rfl⟩
      · rcases h2 with h2 | ⟨w, hw2, h2⟩
        · exact Or.inl ⟨rfl, Sum.inl_injective h2⟩
        · exact absurd (Sum.inl_injective h2.symm)
            (fun hh => (σ c₁).property (by rw [← hh]; exact w.property))
      · rcases h2 with h2 | ⟨w', hw2, h2⟩
        · exact absurd (Sum.inl_injective h2)
            (fun hh => (σ c₂).property (by rw [← hh]; exact w.property))
        · have hww : w = w' := Subtype.ext (by simpa using Sum.inl_injective h2)
          exact Or.inr ⟨w, hw1, hww ▸ hw2, rfl⟩
    rw [Finset.card_le_one]
    intro z hz z' hz'
    simp only [Finset.mem_inter, hmemT] at hz hz'
    obtain ⟨Hz1, Hz2⟩ := hz
    obtain ⟨Hz1', Hz2'⟩ := hz'
    have Hz := hclass z Hz1 Hz2
    have Hz' := hclass z' Hz1' Hz2'
    rcases Hz with ⟨rfl, hσ⟩ | ⟨w, hw1, hw2, rfl⟩
    · rcases Hz' with ⟨rfl, _⟩ | ⟨w', hw1', hw2', rfl⟩
      · rfl
      · exact (hsamecol_disj (σ.injective (Subtype.ext hσ)) w' hw1' hw2').elim
    · rcases Hz' with ⟨rfl, hσ⟩ | ⟨w', hw1', hw2', rfl⟩
      · exact (hsamecol_disj (σ.injective (Subtype.ext hσ)) w hw1 hw2).elim
      · rw [hshare w w' hw1 hw2 hw1' hw2']

private lemma card_rrqAssignedTriangles (G : SplitGraph) (R : Finset (Fin G.p))
    (φ : Sym2 {x : Fin G.p // x ∈ R} → ℕ)
    (σ : Fin (rp (Fintype.card {x : Fin G.p // x ∈ R})) ↪ {x : Fin G.p // x ∉ R}) :
    (rrqAssignedTriangles G R φ σ).card =
      ∑ c, (rrqFactorEdges G R φ c).card := by
  have hsub : ∀ c, rrqFactorEdges G R φ c ⊆
      (⊤ : SimpleGraph {x : Fin G.p // x ∈ R}).edgeFinset :=
    fun c => by unfold rrqFactorEdges; exact Finset.filter_subset _ _
  unfold rrqAssignedTriangles rrqTriangle
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro c _
    rw [Finset.card_image_of_injOn]
    intro e₁ he₁ e₂ he₂ h_eq
    dsimp only at h_eq
    have hnotmem : ∀ (e : Sym2 {x : Fin G.p // x ∈ R}),
        (Sum.inl (σ c).val : G.V) ∉
          e.toFinset.image (fun w : {x // x ∈ R} => (Sum.inl w.val : G.V)) := by
      intro e; simp only [Finset.mem_image, Sym2.mem_toFinset, not_exists]
      rintro w ⟨hw, heq⟩
      have hval : w.val = (σ c).val := by simpa using heq
      exact (σ c).property (hval ▸ w.property)
    have himg : e₁.toFinset.image (fun w : {x // x ∈ R} => (Sum.inl w.val : G.V))
        = e₂.toFinset.image (fun w : {x // x ∈ R} => (Sum.inl w.val : G.V)) := by
      rw [← Finset.erase_insert (hnotmem e₁), ← Finset.erase_insert (hnotmem e₂), h_eq]
    have hinj : Function.Injective (fun w : {x : Fin G.p // x ∈ R} => (Sum.inl w.val : G.V)) := by
      intro u v huv; exact Subtype.ext (by simpa using huv)
    have htf : e₁.toFinset = e₂.toFinset := Finset.image_injective hinj himg
    have hmem : ∀ v, v ∈ e₁ ↔ v ∈ e₂ := by
      intro v; simpa [Sym2.mem_toFinset] using Finset.ext_iff.mp htf v
    rcases e₁ with ⟨a, b⟩; rcases e₂ with ⟨x, y⟩
    have hab : a ≠ b := by
      have := hsub c he₁
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.top_adj] at this
      exact this
    simp only [Sym2.mem_iff] at hmem
    rw [Sym2.eq_iff]
    have ha := (hmem a).mp (Or.inl rfl)
    have hb := (hmem b).mp (Or.inr rfl)
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp_all
  · intro c hc d hd hcd
    simp only [Finset.disjoint_left, Finset.mem_image]
    rintro t ⟨e, he, rfl⟩ ⟨e', he', hteq⟩
    have hcin : (Sum.inl (σ c).val : G.V) ∈
        insert (Sum.inl (σ c).val : G.V)
          (e.toFinset.image (fun w : {x // x ∈ R} => (Sum.inl w.val : G.V))) :=
      Finset.mem_insert_self _ _
    rw [← hteq] at hcin
    simp only [Finset.mem_insert, Finset.mem_image, Sym2.mem_toFinset] at hcin
    rcases hcin with h | ⟨w, hw, hweq⟩
    · exact hcd (σ.injective (Subtype.ext (by simpa using h)))
    · have hval : w.val = (σ c).val := by simpa using hweq
      exact absurd (hval ▸ w.property) (σ c).property

private lemma sum_rrqFactorEdges_card (G : SplitGraph) (R : Finset (Fin G.p))
    (φ : Sym2 {x : Fin G.p // x ∈ R} → ℕ)
    (hbound : ∀ e ∈ (⊤ : SimpleGraph {x : Fin G.p // x ∈ R}).edgeFinset,
      φ e < rp (Fintype.card {x : Fin G.p // x ∈ R})) :
    ∑ c, (rrqFactorEdges G R φ c).card = R.card.choose 2 := by
  unfold rrqFactorEdges
  rw [← card_reserved_subtype G R,
      ← SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := {x : Fin G.p // x ∈ R})]
  rw [Finset.card_eq_sum_card_fiberwise
      (f := fun e => φ e) (t := Finset.range (rp (Fintype.card {x : Fin G.p // x ∈ R})))
      (fun e he => Finset.mem_range.mpr (hbound e he))]
  rw [Fin.sum_univ_eq_sum_range
      (fun k => ((⊤ : SimpleGraph {x : Fin G.p // x ∈ R}).edgeFinset.filter fun e => φ e = k).card)
      (rp (Fintype.card {x : Fin G.p // x ∈ R}))]

/-- **RRQ family**: factorising the reserved clique `K[R]` gives a triangle packing of
`G.graph` of size at least `C(ρ, 2)` where `ρ = |R|`. -/
private lemma rrq_family (G : SplitGraph) (R : Finset (Fin G.p))
    (hbrho : rp R.card ≤ G.p - R.card) :
    ∃ T : Finset (Finset G.V), IsTrianglePacking G.graph T ∧
      ((R.card.choose 2 : ℕ) : ℝ) ≤ (T.card : ℝ) := by
  classical
  obtain ⟨φ, hbound, hproper⟩ := complete_graph_edge_coloring_fintype {x : Fin G.p // x ∈ R}
  have hcardR : Fintype.card {x : Fin G.p // x ∈ R} = R.card := card_reserved_subtype G R
  have hcompl : Fintype.card {x : Fin G.p // x ∉ R} = G.p - R.card :=
    card_clique_complement G R
  have hne : Nonempty (Fin (rp (Fintype.card {x : Fin G.p // x ∈ R})) ↪
      {x : Fin G.p // x ∉ R}) := by
    apply Function.Embedding.nonempty_of_card_le
    rw [Fintype.card_fin, hcompl, hcardR]; exact hbrho
  obtain ⟨σ⟩ := hne
  refine ⟨rrqAssignedTriangles G R φ σ, rrqAssignedTriangles_isPacking G R φ hproper σ, ?_⟩
  rw [card_rrqAssignedTriangles G R φ σ, sum_rrqFactorEdges_card G R φ hbound]

/-! ### IRQ reserved-gain family (third §7.2 summand, via Galvin list edge colouring) -/

open ShiftedCenter in
/-- `gᵢ = |R ∖ Sᵢ| = |R ∩ Nᵢ|`. -/
private lemma gg_eq_inter_card (G : SplitGraph) (R : Finset (Fin G.p)) (i : Fin G.q) :
    gg G R i = (R ∩ G.N i).card := by
  unfold gg SplitGraph.S; rw [sdiff_eq, compl_compl]; rfl

open ShiftedCenter in
/-- The admissible-colour list size `|Nᵢ ∖ R| = b − tᵢ` (available `Q`-vertices). -/
private lemma card_N_sdiff_R (G : SplitGraph) (R : Finset (Fin G.p)) (i : Fin G.q) :
    (G.N i \ R).card = G.p - R.card - tt G R i := by
  have hpart : (G.N i \ R).card + ((G.S i) \ R).card = (Finset.univ \ R).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      unfold SplitGraph.S
      ext x
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_compl, Finset.mem_univ, true_and]
      tauto
    · rw [Finset.disjoint_left]
      intro x hx hx2
      simp only [Finset.mem_sdiff, SplitGraph.S, Finset.mem_compl] at hx hx2
      exact hx2.1 hx.1
  have hcompl : (Finset.univ \ R : Finset (Fin G.p)).card = G.p - R.card := by
    rw [Finset.card_sdiff]; simp
  unfold tt
  omega

/-- The IRQ **gain graph**: bipartite edges `(x, a)` between reserved vertices `x ∈ R`
and the `u` selected independent slots `a : Fin u` (via `σ`), present when `x ∈ N (σ a)`. -/
private def irqGain (G : SplitGraph) (R : Finset (Fin G.p)) (u : ℕ) (σ : Fin u → Fin G.q) :
    Finset (Fin G.p × Fin u) :=
  Finset.univ.filter (fun e => e.1 ∈ R ∧ e.1 ∈ G.N (σ e.2))

/-- The IRQ triangle attached to a gain edge `e = (x, a)` with colour vertex `ψ e`. -/
private def irqTri (G : SplitGraph) (u : ℕ) (σ : Fin u → Fin G.q)
    (ψ : Fin G.p × Fin u → Fin G.p) (e : Fin G.p × Fin u) : Finset G.V :=
  {Sum.inl e.1, Sum.inl (ψ e), Sum.inr (σ e.2)}

/-- The IRQ triangle family produced from a proper vertex-colouring `ψ` of the gain graph. -/
private def irqTriangles (G : SplitGraph) (R : Finset (Fin G.p)) (u : ℕ)
    (σ : Fin u → Fin G.q) (ψ : Fin G.p × Fin u → Fin G.p) : Finset (Finset G.V) :=
  (irqGain G R u σ).image (irqTri G u σ ψ)

open ShiftedCenter in
/-- **Galvin list edge colouring of the IRQ gain graph.**  Every edge `(x, a)` with
`x ∈ R ∩ N (σ a)` gets a colour vertex `ψ (x,a) ∈ N (σ a) ∖ R`, with adjacent edges
(sharing the reserved endpoint `x` or the independent endpoint `a`) receiving distinct
colour vertices.  The lists `L (x,a) = N (σ a) ∖ R` have size `≥ max R.card u`, the two
maximum degrees, so Galvin's theorem (`galvin_max_degree`) applies. -/
private lemma irq_list_coloring (G : SplitGraph) (R : Finset (Fin G.p))
    (u : ℕ) (σ : Fin u → Fin G.q)
    (hlist : ∀ a : Fin u, max R.card u ≤ (G.N (σ a) \ R).card) :
    ∃ ψ : Fin G.p × Fin u → Fin G.p,
      (∀ e : Fin G.p × Fin u, e.1 ∈ R → e.1 ∈ G.N (σ e.2) →
        ψ e ∈ G.N (σ e.2) ∧ ψ e ∉ R) ∧
      (∀ e ∈ irqGain G R u σ, ∀ f ∈ irqGain G R u σ, e ≠ f →
        (e.1 = f.1 ∨ e.2 = f.2) → ψ e ≠ ψ f) := by
  classical
  set B := irqGain G R u σ with hB
  set Δ := max R.card u with hΔ
  set L : Fin G.p × Fin u → Finset ℕ := fun e => (G.N (σ e.2) \ R).image (Fin.val) with hL
  have hdegU : ∀ x : Fin G.p, (B.filter (fun e => e.1 = x)).card ≤ Δ := by
    intro x
    have hsub : B.filter (fun e => e.1 = x) ⊆ ({x} ×ˢ (Finset.univ : Finset (Fin u))) := by
      intro e he
      simp only [Finset.mem_filter] at he
      simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_univ, and_true]
      exact he.2
    have hle := Finset.card_le_card hsub
    simp only [Finset.card_product, Finset.card_singleton, Finset.card_univ, Fintype.card_fin,
      one_mul] at hle
    exact le_trans hle (le_max_right _ _)
  have hdegR : ∀ a : Fin u, (B.filter (fun e => e.2 = a)).card ≤ Δ := by
    intro a
    have hsub : B.filter (fun e => e.2 = a) ⊆ (R ×ˢ ({a} : Finset (Fin u))) := by
      intro e he
      simp only [Finset.mem_filter, hB, irqGain, Finset.mem_univ, true_and] at he
      simp only [Finset.mem_product, Finset.mem_singleton]
      exact ⟨he.1.1, he.2⟩
    have hle := Finset.card_le_card hsub
    simp only [Finset.card_product, Finset.card_singleton, mul_one] at hle
    exact le_trans hle (le_max_left _ _)
  have hLcard : ∀ e ∈ B, Δ ≤ (L e).card := by
    intro e _
    have hcard : (L e).card = (G.N (σ e.2) \ R).card := by
      rw [hL]; apply Finset.card_image_of_injOn
      intro a _ b _ hab; exact Fin.val_injective hab
    rw [hcard]; exact hlist e.2
  obtain ⟨φ, hφmem, hφproper⟩ := AppendixD.galvin_max_degree B Δ hdegU hdegR L hLcard
  have hmemB : ∀ e : Fin G.p × Fin u, e.1 ∈ R → e.1 ∈ G.N (σ e.2) → e ∈ B := by
    intro e he1 he2
    simp only [hB, irqGain, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨he1, he2⟩
  have hex : ∀ e ∈ B, ∃ y : Fin G.p, y ∈ G.N (σ e.2) ∧ y ∉ R ∧ (y : ℕ) = φ e := by
    intro e he
    have hm := hφmem e he
    rw [hL] at hm
    simp only [Finset.mem_image, Finset.mem_sdiff] at hm
    obtain ⟨y, ⟨hy1, hy2⟩, hy3⟩ := hm
    exact ⟨y, hy1, hy2, hy3⟩
  refine ⟨fun e => if h : ∃ y : Fin G.p, y ∈ G.N (σ e.2) ∧ y ∉ R ∧ (y : ℕ) = φ e
      then h.choose else e.1, ?_, ?_⟩
  · intro e he1 he2
    have hexe := hex e (hmemB e he1 he2)
    simp only [dif_pos hexe]
    obtain ⟨hz1, hz2, _⟩ := hexe.choose_spec
    exact ⟨hz1, hz2⟩
  · intro e heB f hfB hef hadj
    have hexe := hex e heB
    have hexf := hex f hfB
    simp only [dif_pos hexe, dif_pos hexf]
    have hne : φ e ≠ φ f := hφproper e heB f hfB hef hadj
    intro hcontra
    apply hne
    have h1 := hexe.choose_spec.2.2
    have h2 := hexf.choose_spec.2.2
    rw [← h1, ← h2, hcontra]

open ShiftedCenter in
/-- The IRQ triangle family is an (edge-disjoint) triangle packing. -/
private lemma irqTriangles_isPacking (G : SplitGraph) (R : Finset (Fin G.p))
    (u : ℕ) (σ : Fin u → Fin G.q) (hσ : Function.Injective σ)
    (ψ : Fin G.p × Fin u → Fin G.p)
    (hψ1 : ∀ e : Fin G.p × Fin u, e.1 ∈ R → e.1 ∈ G.N (σ e.2) →
      ψ e ∈ G.N (σ e.2) ∧ ψ e ∉ R)
    (hψ2 : ∀ e ∈ irqGain G R u σ, ∀ f ∈ irqGain G R u σ, e ≠ f →
      (e.1 = f.1 ∨ e.2 = f.2) → ψ e ≠ ψ f) :
    IsTrianglePacking G.graph (irqTriangles G R u σ ψ) := by
  classical
  refine ⟨?_, ?_⟩
  · intro t ht
    simp only [irqTriangles, Finset.mem_image] at ht
    obtain ⟨e, he, rfl⟩ := ht
    have heR : e.1 ∈ R ∧ e.1 ∈ G.N (σ e.2) := by
      simpa only [irqGain, Finset.mem_filter, Finset.mem_univ, true_and] using he
    have hy := hψ1 e heR.1 heR.2
    have hxy : e.1 ≠ ψ e := fun h => hy.2 (h ▸ heR.1)
    show G.graph.IsNClique 3 ({Sum.inl e.1, Sum.inl (ψ e), Sum.inr (σ e.2)} : Finset G.V)
    exact irq_isTriangle G hxy heR.2 hy.1
  · intro t1 ht1 t2 ht2 hne
    simp only [Finset.mem_coe, irqTriangles, Finset.mem_image] at ht1 ht2
    obtain ⟨e, he, rfl⟩ := ht1
    obtain ⟨f, hf, rfl⟩ := ht2
    have heR : e.1 ∈ R ∧ e.1 ∈ G.N (σ e.2) := by
      simpa only [irqGain, Finset.mem_filter, Finset.mem_univ, true_and] using he
    have hfR : f.1 ∈ R ∧ f.1 ∈ G.N (σ f.2) := by
      simpa only [irqGain, Finset.mem_filter, Finset.mem_univ, true_and] using hf
    have hyeR : ψ e ∉ R := (hψ1 e heR.1 heR.2).2
    have hyfR : ψ f ∉ R := (hψ1 f hfR.1 hfR.2).2
    have hef : e ≠ f := fun h => hne (by rw [h])
    have hne3 : ¬(e.1 = f.1 ∧ e.2 = f.2) := fun ⟨ha, hb⟩ => hef (Prod.ext ha hb)
    have hne1 : ¬(e.1 = f.1 ∧ ψ e = ψ f) := fun ⟨ha, hb⟩ => hψ2 e he f hf hef (Or.inl ha) hb
    have hne2 : ¬(e.2 = f.2 ∧ ψ e = ψ f) := fun ⟨ha, hb⟩ => hψ2 e he f hf hef (Or.inr ha) hb
    have hcl : ∀ w : G.V,
        (w = Sum.inl e.1 ∨ w = Sum.inl (ψ e) ∨ w = Sum.inr (σ e.2)) →
        (w = Sum.inl f.1 ∨ w = Sum.inl (ψ f) ∨ w = Sum.inr (σ f.2)) →
        (w = Sum.inr (σ e.2) ∧ e.2 = f.2) ∨ (w = Sum.inl e.1 ∧ e.1 = f.1) ∨
          (w = Sum.inl (ψ e) ∧ ψ e = ψ f) := by
      intro w hw1 hw2
      rcases hw1 with h1 | h1 | h1 <;> rcases hw2 with h2 | h2 | h2
      · exact Or.inr (Or.inl ⟨h1, Sum.inl_injective (h1.symm.trans h2)⟩)
      · exact absurd (Sum.inl_injective (h1.symm.trans h2)) (fun h => hyfR (h ▸ heR.1))
      · exact absurd (h1.symm.trans h2) (by simp)
      · exact absurd (Sum.inl_injective (h1.symm.trans h2)) (fun h => hyeR (h.symm ▸ hfR.1))
      · exact Or.inr (Or.inr ⟨h1, Sum.inl_injective (h1.symm.trans h2)⟩)
      · exact absurd (h1.symm.trans h2) (by simp)
      · exact absurd (h1.symm.trans h2) (by simp)
      · exact absurd (h1.symm.trans h2) (by simp)
      · exact Or.inl ⟨h1, hσ (Sum.inr_injective (h1.symm.trans h2))⟩
    rw [Finset.card_le_one]
    intro z hz z' hz'
    simp only [irqTri, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hz hz'
    have Hz := hcl z hz.1 hz.2
    have Hz' := hcl z' hz'.1 hz'.2
    rcases Hz with ⟨hzv, hzc⟩ | ⟨hzv, hzc⟩ | ⟨hzv, hzc⟩ <;>
      rcases Hz' with ⟨hz'v, hz'c⟩ | ⟨hz'v, hz'c⟩ | ⟨hz'v, hz'c⟩
    · rw [hzv, hz'v]
    · exact absurd ⟨hz'c, hzc⟩ hne3
    · exact absurd ⟨hzc, hz'c⟩ hne2
    · exact absurd ⟨hzc, hz'c⟩ hne3
    · rw [hzv, hz'v]
    · exact absurd ⟨hzc, hz'c⟩ hne1
    · exact absurd ⟨hz'c, hzc⟩ hne2
    · exact absurd ⟨hz'c, hzc⟩ hne1
    · rw [hzv, hz'v]

open ShiftedCenter in
/-- The IRQ family has exactly `∑ₐ |R ∩ N (σ a)|` triangles, one per gain edge. -/
private lemma card_irqTriangles (G : SplitGraph) (R : Finset (Fin G.p))
    (u : ℕ) (σ : Fin u → Fin G.q) (hσ : Function.Injective σ)
    (ψ : Fin G.p × Fin u → Fin G.p)
    (hψ1 : ∀ e : Fin G.p × Fin u, e.1 ∈ R → e.1 ∈ G.N (σ e.2) →
      ψ e ∈ G.N (σ e.2) ∧ ψ e ∉ R) :
    (irqTriangles G R u σ ψ).card = ∑ a : Fin u, (R ∩ G.N (σ a)).card := by
  rw [irqTriangles]
  rw [Finset.card_image_of_injOn]
  · -- Compute cardinality of irqGain
    -- irqGain = {(x, a) | x ∈ R ∧ x ∈ G.N (σ a)}
    -- Rewrite as biUnion over a
    have h_eq : irqGain G R u σ = (Finset.univ : Finset (Fin u)).biUnion 
      (fun j => (R ∩ G.N (σ j)).image (fun x => (x, j))) := by
      ext ⟨x, j⟩
      simp [irqGain, Finset.mem_biUnion, Finset.mem_image]
    rw [h_eq]
    rw [Finset.card_biUnion]
    · congr 1 with j
      exact Finset.card_image_of_injective _ (fun x y h => by simpa using h)
    · intro a _ b _ hab
      apply Finset.disjoint_left.mpr
      intro x hx₁ hx₂
      simp only [Finset.mem_image] at hx₁ hx₂
      obtain ⟨y₁, hy₁, rfl⟩ := hx₁
      obtain ⟨y₂, hy₂, hxy⟩ := hx₂
      simp at hxy
      exact hab hxy.2.symm
  · intro e₁ he₁ e₂ he₂ htri
    simp only [irqTri] at htri
    -- From set equality, σ e₁.2 = σ e₂.2 (via Sum.inr element)
    have hσ_eq : σ e₁.2 = σ e₂.2 := by
      have : Sum.inr (σ e₁.2) ∈ ({Sum.inl e₂.1, Sum.inl (ψ e₂), Sum.inr (σ e₂.2)} : Finset G.V) := by
        rw [← htri]; simp
      simp at this
      exact this
    have h2_eq : e₁.2 = e₂.2 := hσ hσ_eq
    -- e₁.1 must equal e₂.1
    have he₁_mem : e₁.1 ∈ R ∧ e₁.1 ∈ G.N (σ e₁.2) := by
      rw [irqGain] at he₁; simp at he₁; exact he₁
    have he₂_mem : e₂.1 ∈ R ∧ e₂.1 ∈ G.N (σ e₂.2) := by
      rw [irqGain] at he₂; simp at he₂; exact he₂
    -- From set equality, e₁.1 is in the second set
    have he₁1_in_s2 : Sum.inl e₁.1 ∈ ({Sum.inl e₂.1, Sum.inl (ψ e₂), Sum.inr (σ e₂.2)} : Finset G.V) := by
      rw [← htri]; simp
    simp at he₁1_in_s2
    -- Rule out e₁.1 = ψ e₂ (since ψ e₂ ∉ R but e₁.1 ∈ R)
    have hpsi_notin_R : ψ e₂ ∉ R := (hψ1 e₂ (he₂_mem.1) (he₂_mem.2)).2
    cases he₁1_in_s2 with
    | inl h => exact Prod.ext h h2_eq
    | inr h => exact absurd (h ▸ he₁_mem.1) hpsi_notin_R

open ShiftedCenter in
/-- **IRQ reserved-gain family** (third §7.2 summand).  There is a triangle packing of
`G.graph` realising the reserved-gain bound `(1 − (ρ−1)/b)·(u/q)·B_R`. -/
private lemma irq_family (G : SplitGraph) (R : Finset (Fin G.p))
    (hb2 : 2 ≤ G.p - R.card)
    (hqrb : rp (G.p - R.card) ≤ G.q)
    (hbrho : rp R.card ≤ G.p - R.card)
    (h72 : ∀ i, max R.card (G.q - rp (G.p - R.card)) ≤ (G.p - R.card) - tt G R i) :
    ∃ T : Finset (Finset G.V), IsTrianglePacking G.graph T ∧
      (1 - ((R.card - 1 : ℕ) : ℝ) / (G.p - R.card : ℝ))
          * ((G.q - rp (G.p - R.card) : ℕ) : ℝ) / (G.q : ℝ) * (BR G R : ℝ) ≤ (T.card : ℝ) := by
  classical
  set u := G.q - rp (G.p - R.card) with hu
  have hq : 0 < G.q := q_pos_of_rp_le hb2 hqrb
  have hRp : R.card ≤ G.p := le_trans (Finset.card_le_univ _) (by norm_num)
  -- averaging: pick `u` independent slots whose reserved-gain sum is at least the mean
  obtain ⟨σ, hσmean⟩ := exists_injection_ge_mean
    (fun (_ : Fin u) (i : Fin G.q) => (gg G R i : ℝ))
    (by simp only [Fintype.card_fin]; omega)
    (by simp only [Fintype.card_fin]; exact hq)
  simp only [Fintype.card_fin] at hσmean
  -- list-size condition from (7.2)
  have hlist : ∀ a : Fin u, max R.card u ≤ (G.N (σ a) \ R).card := by
    intro a; rw [card_N_sdiff_R]; exact h72 (σ a)
  obtain ⟨ψ, hψ1, hψ2⟩ := irq_list_coloring G R u σ hlist
  refine ⟨irqTriangles G R u σ ψ,
    irqTriangles_isPacking G R u σ σ.injective ψ hψ1 hψ2, ?_⟩
  -- card of the family
  have hcard : ((irqTriangles G R u σ ψ).card : ℝ) = ∑ a : Fin u, (gg G R (σ a) : ℝ) := by
    rw [card_irqTriangles G R u σ σ.injective ψ hψ1]
    push_cast
    exact Finset.sum_congr rfl (fun a _ => by rw [gg_eq_inter_card])
  -- mean bound, simplified
  have hmean : (1 / (G.q : ℝ)) * ((u : ℝ) * (BR G R : ℝ)) ≤ ∑ a : Fin u, (gg G R (σ a) : ℝ) := by
    have hsum : ∑ (_ : Fin u), ∑ i, (gg G R i : ℝ) = (u : ℝ) * (BR G R : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      congr 1
      rw [BR]; push_cast; rfl
    calc (1 / (G.q : ℝ)) * ((u : ℝ) * (BR G R : ℝ))
        = (1 / (G.q : ℝ)) * ∑ (_ : Fin u), ∑ i, (gg G R i : ℝ) := by rw [hsum]
      _ ≤ ∑ a : Fin u, (gg G R (σ a) : ℝ) := hσmean
  -- slack factor `(1 - (ρ-1)/b) ≤ 1`
  have hbpos : (0 : ℝ) < (G.p - R.card : ℝ) := by
    have heq : (G.p - R.card : ℝ) = ((G.p - R.card : ℕ) : ℝ) := by rw [Nat.cast_sub hRp]
    rw [heq]
    have : (2 : ℝ) ≤ ((G.p - R.card : ℕ) : ℝ) := by exact_mod_cast hb2
    linarith
  have hfac : (1 - ((R.card - 1 : ℕ) : ℝ) / (G.p - R.card : ℝ)) ≤ 1 := by
    have h0 : (0 : ℝ) ≤ ((R.card - 1 : ℕ) : ℝ) / (G.p - R.card : ℝ) := by positivity
    linarith
  have hnonneg : (0 : ℝ) ≤ (1 / (G.q : ℝ)) * ((u : ℝ) * (BR G R : ℝ)) := by positivity
  rw [hcard]
  have hstep : (1 - ((R.card - 1 : ℕ) : ℝ) / (G.p - R.card : ℝ))
      * ((u : ℝ)) / (G.q : ℝ) * (BR G R : ℝ)
      ≤ (1 / (G.q : ℝ)) * ((u : ℝ) * (BR G R : ℝ)) := by
    have hX : (0 : ℝ) ≤ (u : ℝ) * (BR G R : ℝ) / (G.q : ℝ) := by positivity
    have hL : (1 - ((R.card - 1 : ℕ) : ℝ) / (G.p - R.card : ℝ))
        * ((u : ℝ)) / (G.q : ℝ) * (BR G R : ℝ)
        = (1 - ((R.card - 1 : ℕ) : ℝ) / (G.p - R.card : ℝ))
            * ((u : ℝ) * (BR G R : ℝ) / (G.q : ℝ)) := by ring
    have hR : (1 / (G.q : ℝ)) * ((u : ℝ) * (BR G R : ℝ))
        = 1 * ((u : ℝ) * (BR G R : ℝ) / (G.q : ℝ)) := by ring
    rw [hL, hR]
    exact mul_le_mul_of_nonneg_right hfac hX
  calc (1 - ((R.card - 1 : ℕ) : ℝ) / (G.p - R.card : ℝ))
          * ((G.q - rp (G.p - R.card) : ℕ) : ℝ) / (G.q : ℝ) * (BR G R : ℝ)
      = (1 - ((R.card - 1 : ℕ) : ℝ) / (G.p - R.card : ℝ))
          * ((u : ℝ)) / (G.q : ℝ) * (BR G R : ℝ) := by rw [hu]
    _ ≤ (1 / (G.q : ℝ)) * ((u : ℝ) * (BR G R : ℝ)) := hstep
    _ ≤ ∑ a : Fin u, (gg G R (σ a) : ℝ) := hmean

/-! ### Coordinated assembly of the three §7.2 families -/

open ShiftedCenter in
/-- **Cross-disjointness RRQ vs QQI.**  An RRQ triangle (three `Sum.inl` clique vertices,
using an `R`–`R` factor edge and one complement vertex) and a QQI triangle (two complement
`Sum.inl` vertices and the independent `Sum.inr` vertex) share at most one vertex: the only
possible common vertex is the single complement (`∉ R`) `Sum.inl` vertex of the RRQ triangle. -/
private lemma rrq_qqi_cross (G : SplitGraph) (R : Finset (Fin G.p))
    (φR : Sym2 {x : Fin G.p // x ∈ R} → ℕ)
    (σR : Fin (rp (Fintype.card {x : Fin G.p // x ∈ R})) ↪ {x : Fin G.p // x ∉ R})
    (φQ : Sym2 {x : Fin G.p // x ∉ R} → ℕ)
    (σQ : Fin (rp (Fintype.card {x : Fin G.p // x ∉ R})) ↪ Fin G.q)
    (t₁ : Finset G.V) (h₁ : t₁ ∈ rrqAssignedTriangles G R φR σR)
    (t₂ : Finset G.V) (h₂ : t₂ ∈ qAssignedTriangles G R φQ σQ) :
    (t₁ ∩ t₂).card ≤ 1 := by
  obtain ⟨c₁, e₁, he₁, rfl⟩ : ∃ c₁ e₁, e₁ ∈ rrqFactorEdges G R φR c₁ ∧
      t₁ = rrqTriangle G R (σR c₁).val e₁ := by
    simp only [rrqAssignedTriangles, Finset.mem_biUnion, Finset.mem_image] at h₁
    obtain ⟨c₁, -, e₁, he₁, heq⟩ := h₁
    exact ⟨c₁, e₁, he₁, heq.symm⟩
  obtain ⟨c₂, e₂, he₂, rfl⟩ : ∃ c₂ e₂, e₂ ∈ qFactorEdges G R φQ c₂ (σQ c₂) ∧
      t₂ = qTriangle G R (σQ c₂) e₂ := by
    simp only [qAssignedTriangles, Finset.mem_biUnion, Finset.mem_image] at h₂
    obtain ⟨c₂, -, e₂, he₂, heq⟩ := h₂
    exact ⟨c₂, e₂, he₂, heq.symm⟩
  have hsub : rrqTriangle G R (σR c₁).val e₁ ∩ qTriangle G R (σQ c₂) e₂ ⊆
      {Sum.inl (σR c₁).val} := by
    intro z hz
    simp only [Finset.mem_inter, rrqTriangle, qTriangle, Finset.mem_insert, Finset.mem_image,
      Sym2.mem_toFinset] at hz
    rcases hz with ⟨hz₁, hz₂⟩
    rcases hz₁ with hz₁ | ⟨w₁, hw₁, hzw₁⟩
    · exact Finset.mem_singleton.mpr hz₁
    · rcases hz₂ with hz₂' | ⟨w₂, hw₂, hzw₂⟩
      · have : Sum.inl (w₁ : Fin G.p) = Sum.inr (σQ c₂) := hzw₁.trans hz₂'
        cases this
      · have heq : Sum.inl (w₁ : Fin G.p) = Sum.inl (w₂ : Fin G.p) := hzw₁.trans hzw₂.symm
        have : (w₁ : Fin G.p) = (w₂ : Fin G.p) := by injection heq
        exact absurd (this ▸ w₁.property) w₂.property
  exact Finset.card_le_one.mpr (fun x hx y hy => by
    have hx' := hsub hx
    have hy' := hsub hy
    simp_all [Finset.mem_singleton])

open ShiftedCenter in
/-- **Cross-disjointness QQI vs IRQ.**  When the QQI independent slots (`σQ`) are disjoint
from the IRQ independent slots (`σI`), a QQI triangle and an IRQ triangle share at most one
vertex: they use distinct `Sum.inr` vertices, so any common vertex is a complement `Sum.inl`
vertex. -/
private lemma qqi_irq_cross (G : SplitGraph) (R : Finset (Fin G.p)) (u : ℕ)
    (φQ : Sym2 {x : Fin G.p // x ∉ R} → ℕ)
    (σQ : Fin (rp (Fintype.card {x : Fin G.p // x ∉ R})) ↪ Fin G.q)
    (σI : Fin u → Fin G.q) (ψ : Fin G.p × Fin u → Fin G.p)
    (hdisj : ∀ (c : Fin (rp (Fintype.card {x : Fin G.p // x ∉ R}))) (a : Fin u),
      σQ c ≠ σI a)
    (t₁ : Finset G.V) (h₁ : t₁ ∈ qAssignedTriangles G R φQ σQ)
    (t₂ : Finset G.V) (h₂ : t₂ ∈ irqTriangles G R u σI ψ) :
    (t₁ ∩ t₂).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro z hz z' hz'
  simp only [qAssignedTriangles, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ,
    true_and] at h₁
  obtain ⟨c, e, he, rfl⟩ := h₁
  simp only [irqTriangles, Finset.mem_image] at h₂
  obtain ⟨ed, heder, rfl⟩ := h₂
  simp only [irqGain, Finset.mem_filter, Finset.mem_univ, true_and] at heder
  have hedR : ed.1 ∈ R := heder.1
  have qqi_mem : ∀ w : G.V, w ∈ qTriangle G R (σQ c) e ↔
      w = Sum.inr (σQ c) ∨ ∃ (v : {x : Fin G.p // x ∉ R}), v ∈ e ∧ w = Sum.inl v.val := by
    intro w
    simp only [qTriangle, Finset.mem_insert, Finset.mem_image]
    simp only [Sym2.mem_toFinset]
    tauto
  have irq_mem : ∀ w : G.V, w ∈ irqTri G u σI ψ ed ↔
      w = Sum.inl ed.1 ∨ w = Sum.inl (ψ ed) ∨ w = Sum.inr (σI ed.2) := by
    intro w
    simp only [irqTri, Finset.mem_insert, Finset.mem_singleton]
  have hz_qqi := (qqi_mem z).mp (Finset.mem_of_mem_inter_left hz)
  have hz_irq := (irq_mem z).mp (Finset.mem_of_mem_inter_right hz)
  have hz'_qqi := (qqi_mem z').mp (Finset.mem_of_mem_inter_left hz')
  have hz'_irq := (irq_mem z').mp (Finset.mem_of_mem_inter_right hz')
  have hne_inr : σQ c ≠ σI ed.2 := hdisj c ed.2
  have hz_eq : z = Sum.inl (ψ ed) := by
    rcases hz_qqi with hz_r | ⟨v, hv, hz_l⟩
    · rcases hz_irq with h | h | h
      · exact absurd (hz_r.symm.trans h).symm Sum.inl_ne_inr
      · exact absurd (hz_r.symm.trans h).symm Sum.inl_ne_inr
      · rw [hz_r] at h; exact False.elim (hne_inr (Sum.inr.inj h))
    · have hv_prop : v.val ∉ R := v.property
      rcases hz_irq with h | h | h
      · rw [hz_l] at h; simp at h; exact absurd hedR (h ▸ hv_prop)
      · exact h
      · exact absurd (hz_l.symm.trans h) Sum.inl_ne_inr
  have hz'_eq : z' = Sum.inl (ψ ed) := by
    rcases hz'_qqi with hz'_r | ⟨v, hv, hz'_l⟩
    · rcases hz'_irq with h | h | h
      · exact absurd (hz'_r.symm.trans h).symm Sum.inl_ne_inr
      · exact absurd (hz'_r.symm.trans h).symm Sum.inl_ne_inr
      · rw [hz'_r] at h; exact False.elim (hne_inr (Sum.inr.inj h))
    · have hv_prop : v.val ∉ R := v.property
      rcases hz'_irq with h | h | h
      · rw [hz'_l] at h; simp at h; exact absurd hedR (h ▸ hv_prop)
      · exact h
      · exact absurd (hz'_l.symm.trans h) Sum.inl_ne_inr
  rw [hz_eq, hz'_eq]

open ShiftedCenter in
/-- The IRQ triangles pruned of those that share an edge with the RRQ family. -/
private def prunedIrqTriangles (G : SplitGraph) (R : Finset (Fin G.p)) (u : ℕ)
    (σI : Fin u → Fin G.q) (ψ : Fin G.p × Fin u → Fin G.p)
    (φR : Sym2 {x : Fin G.p // x ∈ R} → ℕ)
    (σR : Fin (rp (Fintype.card {x : Fin G.p // x ∈ R})) ↪ {x : Fin G.p // x ∉ R}) :
    Finset (Finset G.V) :=
  (irqTriangles G R u σI ψ).filter
    (fun t => ∀ t' ∈ rrqAssignedTriangles G R φR σR, (t ∩ t').card ≤ 1)

/-- The reserved (`∈ R`) vertices incident to a colour-`c` reserved edge. -/
private def rrqColVerts (G : SplitGraph) (R : Finset (Fin G.p))
    (φR : Sym2 {x : Fin G.p // x ∈ R} → ℕ)
    (c : Fin (rp (Fintype.card {x : Fin G.p // x ∈ R}))) : Finset (Fin G.p) :=
  (rrqFactorEdges G R φR c).biUnion (fun e => e.toFinset.image (fun w => w.val))

open ShiftedCenter in
/-- `|IRQ| = |gain graph|`: the IRQ triangle map is injective on gain edges. -/
private lemma irqTriangles_card_eq_gain (G : SplitGraph) (R : Finset (Fin G.p)) (u : ℕ)
    (σI : Fin u → Fin G.q) (hσI : Function.Injective σI)
    (ψ : Fin G.p × Fin u → Fin G.p)
    (hψ1 : ∀ e : Fin G.p × Fin u, e.1 ∈ R → e.1 ∈ G.N (σI e.2) →
      ψ e ∈ G.N (σI e.2) ∧ ψ e ∉ R) :
    (irqTriangles G R u σI ψ).card = (irqGain G R u σI).card := by
  rw [irqTriangles, Finset.card_image_of_injOn]
  intro e₁ he₁ e₂ he₂ htri
  simp only [irqTri] at htri
  have hσ_eq : σI e₁.2 = σI e₂.2 := by
    have hin : Sum.inr (σI e₁.2) ∈
        ({Sum.inl e₂.1, Sum.inl (ψ e₂), Sum.inr (σI e₂.2)} : Finset G.V) := by
      rw [← htri]; simp
    simp at hin; exact hin
  have h2_eq : e₁.2 = e₂.2 := hσI hσ_eq
  have he₂_mem : e₂.1 ∈ R ∧ e₂.1 ∈ G.N (σI e₂.2) := by
    rw [irqGain] at he₂; simp at he₂; exact he₂
  have he₁_mem : e₁.1 ∈ R ∧ e₁.1 ∈ G.N (σI e₁.2) := by
    rw [irqGain] at he₁; simp at he₁; exact he₁
  have he₁_in : Sum.inl e₁.1 ∈
      ({Sum.inl e₂.1, Sum.inl (ψ e₂), Sum.inr (σI e₂.2)} : Finset G.V) := by
    rw [← htri]; simp
  simp at he₁_in
  have hpsi : ψ e₂ ∉ R := (hψ1 e₂ he₂_mem.1 he₂_mem.2).2
  rcases he₁_in with h | h
  · exact Prod.ext h h2_eq
  · exact absurd (h ▸ he₁_mem.1) hpsi

open ShiftedCenter in
/-- Pruning splits the gain graph: the pruned triangles plus the IRQ triangles that share an
edge (≥ 2 vertices) with an RRQ triangle account for the whole gain graph. -/
private lemma prunedIrqTriangles_add_bad (G : SplitGraph) (R : Finset (Fin G.p)) (u : ℕ)
    (σI : Fin u → Fin G.q) (hσI : Function.Injective σI)
    (ψ : Fin G.p × Fin u → Fin G.p)
    (hψ1 : ∀ e : Fin G.p × Fin u, e.1 ∈ R → e.1 ∈ G.N (σI e.2) →
      ψ e ∈ G.N (σI e.2) ∧ ψ e ∉ R)
    (φR : Sym2 {x : Fin G.p // x ∈ R} → ℕ)
    (σR : Fin (rp (Fintype.card {x : Fin G.p // x ∈ R})) ↪ {x : Fin G.p // x ∉ R}) :
    (prunedIrqTriangles G R u σI ψ φR σR).card
      + ((irqGain G R u σI).filter
          (fun e => ∃ t' ∈ rrqAssignedTriangles G R φR σR,
              2 ≤ (irqTri G u σI ψ e ∩ t').card)).card
      = (irqGain G R u σI).card := by
  classical
  have hinj : Set.InjOn (irqTri G u σI ψ) (irqGain G R u σI) := by
    intro e₁ he₁ e₂ he₂ htri
    simp only [irqTri] at htri
    have hσ_eq : σI e₁.2 = σI e₂.2 := by
      have hin : Sum.inr (σI e₁.2) ∈
          ({Sum.inl e₂.1, Sum.inl (ψ e₂), Sum.inr (σI e₂.2)} : Finset G.V) := by
        rw [← htri]; simp
      simp at hin; exact hin
    have h2_eq : e₁.2 = e₂.2 := hσI hσ_eq
    have he₂_mem : e₂.1 ∈ R ∧ e₂.1 ∈ G.N (σI e₂.2) := by
      rw [irqGain] at he₂; simp at he₂; exact he₂
    have he₁_mem : e₁.1 ∈ R ∧ e₁.1 ∈ G.N (σI e₁.2) := by
      rw [irqGain] at he₁; simp at he₁; exact he₁
    have he₁_in : Sum.inl e₁.1 ∈
        ({Sum.inl e₂.1, Sum.inl (ψ e₂), Sum.inr (σI e₂.2)} : Finset G.V) := by
      rw [← htri]; simp
    simp at he₁_in
    have hpsi : ψ e₂ ∉ R := (hψ1 e₂ he₂_mem.1 he₂_mem.2).2
    rcases he₁_in with h | h
    · exact Prod.ext h h2_eq
    · exact absurd (h ▸ he₁_mem.1) hpsi
  have hbadeq : (irqGain G R u σI).filter
        (fun e => ∃ t' ∈ rrqAssignedTriangles G R φR σR, 2 ≤ (irqTri G u σI ψ e ∩ t').card)
      = (irqGain G R u σI).filter
        (fun e => ¬ ∀ t' ∈ rrqAssignedTriangles G R φR σR, (irqTri G u σI ψ e ∩ t').card ≤ 1) := by
    apply Finset.filter_congr
    intro e _
    constructor
    · rintro ⟨t', ht', hc⟩ hall
      exact absurd (hall t' ht') (by omega)
    · intro hnot
      push_neg at hnot
      obtain ⟨t', ht', hc⟩ := hnot
      exact ⟨t', ht', by omega⟩
  have hpruned : (prunedIrqTriangles G R u σI ψ φR σR).card
      = ((irqGain G R u σI).filter
          (fun e => ∀ t' ∈ rrqAssignedTriangles G R φR σR,
            (irqTri G u σI ψ e ∩ t').card ≤ 1)).card := by
    rw [prunedIrqTriangles, irqTriangles, Finset.filter_image,
      Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _))]
  rw [hpruned, hbadeq]
  exact Finset.card_filter_add_card_filter_not _

open ShiftedCenter in
/-- Geometric core: an IRQ triangle sharing an edge with some RRQ triangle must reuse an
RRQ complement vertex (`σR c = ψ e`) at a reserved endpoint covered by colour `c`. -/
private lemma badTri_subset_alg (G : SplitGraph) (R : Finset (Fin G.p)) (u : ℕ)
    (σI : Fin u → Fin G.q) (ψ : Fin G.p × Fin u → Fin G.p)
    (hψ1 : ∀ e : Fin G.p × Fin u, e.1 ∈ R → e.1 ∈ G.N (σI e.2) →
      ψ e ∈ G.N (σI e.2) ∧ ψ e ∉ R)
    (φR : Sym2 {x : Fin G.p // x ∈ R} → ℕ)
    (σR : Fin (rp (Fintype.card {x : Fin G.p // x ∈ R})) ↪ {x : Fin G.p // x ∉ R}) :
    (irqGain G R u σI).filter
        (fun e => ∃ t' ∈ rrqAssignedTriangles G R φR σR, 2 ≤ (irqTri G u σI ψ e ∩ t').card)
      ⊆ (irqGain G R u σI).filter
        (fun e => ∃ c, ((σR c : {x : Fin G.p // x ∉ R}) : Fin G.p) = ψ e
            ∧ e.1 ∈ rrqColVerts G R φR c) := by
  classical
  intro e he
  simp only [Finset.mem_filter] at he ⊢
  obtain ⟨hgain, t', ht', hcard⟩ := he
  refine ⟨hgain, ?_⟩
  have hg : e.1 ∈ R ∧ e.1 ∈ G.N (σI e.2) := by
    simpa only [irqGain, Finset.mem_filter, Finset.mem_univ, true_and] using hgain
  have hψR : ψ e ∉ R := (hψ1 e hg.1 hg.2).2
  simp only [rrqAssignedTriangles, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ,
    true_and] at ht'
  obtain ⟨c', f', hf', rfl⟩ := ht'
  have hsub : irqTri G u σI ψ e ∩ rrqTriangle G R (σR c').val f' ⊆
      {Sum.inl e.1, Sum.inl (ψ e)} := by
    intro z hz
    rw [Finset.mem_inter] at hz
    have hz1 := hz.1
    simp only [irqTri, Finset.mem_insert, Finset.mem_singleton] at hz1
    rcases hz1 with h | h | h
    · simp [h]
    · simp [h]
    · exfalso
      rw [h] at hz
      have h2 := hz.2
      simp only [rrqTriangle, Finset.mem_insert, Finset.mem_image, Sym2.mem_toFinset] at h2
      rcases h2 with h' | ⟨w, _, h'⟩ <;> exact absurd h' (by simp)
  have hne : (Sum.inl e.1 : G.V) ≠ Sum.inl (ψ e) := by
    intro h; injection h with h; exact hψR (h ▸ hg.1)
  have hpair : ({Sum.inl e.1, Sum.inl (ψ e)} : Finset G.V).card = 2 :=
    Finset.card_pair hne
  have heq : irqTri G u σI ψ e ∩ rrqTriangle G R (σR c').val f'
      = {Sum.inl e.1, Sum.inl (ψ e)} :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hpair]; exact hcard)
  have h1 : (Sum.inl e.1 : G.V) ∈ rrqTriangle G R (σR c').val f' := by
    have hm : (Sum.inl e.1 : G.V) ∈ irqTri G u σI ψ e ∩ rrqTriangle G R (σR c').val f' := by
      rw [heq]; simp
    exact (Finset.mem_inter.mp hm).2
  have h2 : (Sum.inl (ψ e) : G.V) ∈ rrqTriangle G R (σR c').val f' := by
    have hm : (Sum.inl (ψ e) : G.V) ∈ irqTri G u σI ψ e ∩ rrqTriangle G R (σR c').val f' := by
      rw [heq]; simp
    exact (Finset.mem_inter.mp hm).2
  refine ⟨c', ?_, ?_⟩
  · simp only [rrqTriangle, Finset.mem_insert, Finset.mem_image, Sym2.mem_toFinset] at h2
    rcases h2 with h | ⟨w, hw, h⟩
    · injection h with h; exact h.symm
    · exfalso; injection h with h; exact absurd (h ▸ w.property) hψR
  · simp only [rrqTriangle, Finset.mem_insert, Finset.mem_image, Sym2.mem_toFinset] at h1
    rcases h1 with h | ⟨w, hw, h⟩
    · exfalso; injection h with h; exact (σR c').property (h ▸ hg.1)
    · simp only [rrqColVerts, Finset.mem_biUnion, Finset.mem_image, Sym2.mem_toFinset]
      refine ⟨f', hf', w, hw, ?_⟩
      injection h with h

open ShiftedCenter in
/-- Union bound over colours for the (algebraic) collision set. -/
private lemma alg_bad_card_le_sum (G : SplitGraph) (R : Finset (Fin G.p)) (u : ℕ)
    (σI : Fin u → Fin G.q) (ψ : Fin G.p × Fin u → Fin G.p)
    (φR : Sym2 {x : Fin G.p // x ∈ R} → ℕ)
    (σR : Fin (rp (Fintype.card {x : Fin G.p // x ∈ R})) ↪ {x : Fin G.p // x ∉ R}) :
    ((irqGain G R u σI).filter
        (fun e => ∃ c, ((σR c : {x : Fin G.p // x ∉ R}) : Fin G.p) = ψ e
            ∧ e.1 ∈ rrqColVerts G R φR c)).card
      ≤ ∑ c, ((irqGain G R u σI).filter
          (fun e => ((σR c : {x : Fin G.p // x ∉ R}) : Fin G.p) = ψ e
              ∧ e.1 ∈ rrqColVerts G R φR c)).card := by
  classical
  have hbi : (irqGain G R u σI).filter
      (fun e => ∃ c, ((σR c : {x : Fin G.p // x ∉ R}) : Fin G.p) = ψ e
          ∧ e.1 ∈ rrqColVerts G R φR c)
      = Finset.univ.biUnion (fun c => (irqGain G R u σI).filter
          (fun e => ((σR c : {x : Fin G.p // x ∉ R}) : Fin G.p) = ψ e
              ∧ e.1 ∈ rrqColVerts G R φR c)) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
    tauto
  rw [hbi]
  exact Finset.card_biUnion_le

open ShiftedCenter in
/-- Summing the per-vertex collision weight over complement vertices recovers the number of
gain edges whose reserved endpoint is covered by colour `c`. -/
private lemma sum_over_compl_weight (G : SplitGraph) (R : Finset (Fin G.p)) (u : ℕ)
    (σI : Fin u → Fin G.q) (ψ : Fin G.p × Fin u → Fin G.p)
    (hψ1 : ∀ e : Fin G.p × Fin u, e.1 ∈ R → e.1 ∈ G.N (σI e.2) →
      ψ e ∈ G.N (σI e.2) ∧ ψ e ∉ R)
    (φR : Sym2 {x : Fin G.p // x ∈ R} → ℕ)
    (c : Fin (rp (Fintype.card {x : Fin G.p // x ∈ R}))) :
    ∑ y : {x : Fin G.p // x ∉ R},
        ((irqGain G R u σI).filter
          (fun e => (y : Fin G.p) = ψ e ∧ e.1 ∈ rrqColVerts G R φR c)).card
      = ((irqGain G R u σI).filter (fun e => e.1 ∈ rrqColVerts G R φR c)).card := by
  classical
  have hdisj : ((Finset.univ : Finset {x : Fin G.p // x ∉ R}) :
        Set {x : Fin G.p // x ∉ R}).PairwiseDisjoint
      (fun y : {x : Fin G.p // x ∉ R} =>
        (irqGain G R u σI).filter (fun e => (y : Fin G.p) = ψ e ∧ e.1 ∈ rrqColVerts G R φR c)) := by
    intro y _ y' _ hyy
    refine Finset.disjoint_left.mpr (fun e he he' => ?_)
    simp only [Finset.mem_filter] at he he'
    exact hyy (Subtype.ext (he.2.1.trans he'.2.1.symm))
  have hcov : (irqGain G R u σI).filter (fun e => e.1 ∈ rrqColVerts G R φR c)
      = Finset.univ.biUnion (fun y : {x : Fin G.p // x ∉ R} =>
          (irqGain G R u σI).filter (fun e => (y : Fin G.p) = ψ e ∧ e.1 ∈ rrqColVerts G R φR c)) := by
    ext e
    constructor
    · intro he
      rw [Finset.mem_filter] at he
      have hg : e.1 ∈ R ∧ e.1 ∈ G.N (σI e.2) := by
        simpa only [irqGain, Finset.mem_filter, Finset.mem_univ, true_and] using he.1
      have hψR : ψ e ∉ R := (hψ1 e hg.1 hg.2).2
      rw [Finset.mem_biUnion]
      exact ⟨⟨ψ e, hψR⟩, Finset.mem_univ _, Finset.mem_filter.mpr ⟨he.1, rfl, he.2⟩⟩
    · intro he
      rw [Finset.mem_biUnion] at he
      obtain ⟨y, -, hy⟩ := he
      rw [Finset.mem_filter] at hy ⊢
      exact ⟨hy.1, hy.2.2⟩
  rw [hcov, Finset.card_biUnion hdisj]

open ShiftedCenter in
/-- Each reserved vertex lies on at most `ρ−1` reserved edges, hence in at most `ρ−1` colour
classes; double counting bounds the total colour-incidence of the gain graph. -/
private lemma sum_colVerts_le (G : SplitGraph) (R : Finset (Fin G.p)) (u : ℕ)
    (σI : Fin u → Fin G.q)
    (φR : Sym2 {x : Fin G.p // x ∈ R} → ℕ) :
    ∑ c, ((irqGain G R u σI).filter (fun e => e.1 ∈ rrqColVerts G R φR c)).card
      ≤ (R.card - 1) * (irqGain G R u σI).card := by
  classical
  have key : ∀ v : Fin G.p, v ∈ R →
      (Finset.univ.filter (fun c => v ∈ rrqColVerts G R φR c)).card ≤ R.card - 1 := by
    intro v hv
    set w : {x : Fin G.p // x ∈ R} := ⟨v, hv⟩ with hw
    have hsub : (Finset.univ.filter (fun c => v ∈ rrqColVerts G R φR c)).image (Fin.val)
        ⊆ ((⊤ : SimpleGraph {x : Fin G.p // x ∈ R}).incidenceFinset w).image φR := by
      intro n hn
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hn
      obtain ⟨c, hc, rfl⟩ := hn
      simp only [rrqColVerts, rrqFactorEdges, Finset.mem_biUnion, Finset.mem_filter,
        Finset.mem_image, Sym2.mem_toFinset, SimpleGraph.mem_edgeFinset] at hc
      obtain ⟨f, ⟨hf_edge, hf_col⟩, z, hz_mem, hz_eq⟩ := hc
      have hzw : z = w := Subtype.ext (by rw [hw]; exact hz_eq)
      refine Finset.mem_image.mpr ⟨f, ?_, hf_col⟩
      rw [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet]
      exact ⟨hf_edge, by rw [← hzw]; exact hz_mem⟩
    calc (Finset.univ.filter (fun c => v ∈ rrqColVerts G R φR c)).card
        = ((Finset.univ.filter (fun c => v ∈ rrqColVerts G R φR c)).image Fin.val).card := by
          rw [Finset.card_image_of_injective _ Fin.val_injective]
      _ ≤ (((⊤ : SimpleGraph {x : Fin G.p // x ∈ R}).incidenceFinset w).image φR).card :=
          Finset.card_le_card hsub
      _ ≤ ((⊤ : SimpleGraph {x : Fin G.p // x ∈ R}).incidenceFinset w).card := Finset.card_image_le
      _ = (⊤ : SimpleGraph {x : Fin G.p // x ∈ R}).degree w :=
          SimpleGraph.card_incidenceFinset_eq_degree _ _
      _ = Fintype.card {x : Fin G.p // x ∈ R} - 1 := SimpleGraph.complete_graph_degree w
      _ = R.card - 1 := by rw [card_reserved_subtype G R]
  calc ∑ c, ((irqGain G R u σI).filter (fun e => e.1 ∈ rrqColVerts G R φR c)).card
      = ∑ e ∈ irqGain G R u σI, (Finset.univ.filter (fun c => e.1 ∈ rrqColVerts G R φR c)).card := by
        simp_rw [Finset.card_filter]
        rw [Finset.sum_comm]
    _ ≤ ∑ _e ∈ irqGain G R u σI, (R.card - 1) := by
        apply Finset.sum_le_sum
        intro e he
        have heR : e.1 ∈ R := by
          have h' := he
          simp only [irqGain, Finset.mem_filter, Finset.mem_univ, true_and] at h'
          exact h'.1
        exact key e.1 heR
    _ = (R.card - 1) * (irqGain G R u σI).card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]

open ShiftedCenter in
/-- **RRQ-collision pruning bound.**  For a fixed IRQ family there is a choice of complement
vertices `σR` (and a proper bounded colouring `φR` of the reserved clique) such that pruning
the IRQ triangles colliding with the resulting RRQ family deletes at most a `(ρ−1)/b` fraction:
the pruned family still has at least `(1 − (ρ−1)/b)·|IRQ|` triangles.  Proved by averaging the
complement-vertex assignment `σR` over injections, using that each reserved vertex lies on only
`ρ−1` reserved edges. -/
private lemma prune_card_bound (G : SplitGraph) (R : Finset (Fin G.p)) (u : ℕ)
    (σI : Fin u → Fin G.q) (hσI : Function.Injective σI)
    (ψ : Fin G.p × Fin u → Fin G.p)
    (hψ1 : ∀ e : Fin G.p × Fin u, e.1 ∈ R → e.1 ∈ G.N (σI e.2) →
      ψ e ∈ G.N (σI e.2) ∧ ψ e ∉ R)
    (hb2 : 2 ≤ G.p - R.card)
    (hbrho : rp R.card ≤ G.p - R.card) :
    ∃ (φR : Sym2 {x : Fin G.p // x ∈ R} → ℕ)
      (σR : Fin (rp (Fintype.card {x : Fin G.p // x ∈ R})) ↪ {x : Fin G.p // x ∉ R}),
      (∀ e ∈ (⊤ : SimpleGraph {x : Fin G.p // x ∈ R}).edgeFinset,
        φR e < rp (Fintype.card {x : Fin G.p // x ∈ R})) ∧
      (∀ e ∈ (⊤ : SimpleGraph {x : Fin G.p // x ∈ R}).edgeFinset,
        ∀ f ∈ (⊤ : SimpleGraph {x : Fin G.p // x ∈ R}).edgeFinset,
          e ≠ f → (∃ v, v ∈ e ∧ v ∈ f) → φR e ≠ φR f) ∧
      (1 - ((R.card - 1 : ℕ) : ℝ) / ((G.p - R.card : ℕ) : ℝ))
            * ((irqTriangles G R u σI ψ).card : ℝ)
        ≤ ((prunedIrqTriangles G R u σI ψ φR σR).card : ℝ) := by
  classical
  obtain ⟨φR, hRbound, hRproper⟩ :=
    complete_graph_edge_coloring_fintype {x : Fin G.p // x ∈ R}
  have hcardR : Fintype.card {x : Fin G.p // x ∈ R} = R.card := card_reserved_subtype G R
  have hcompl : Fintype.card {x : Fin G.p // x ∉ R} = G.p - R.card := card_clique_complement G R
  set W : Fin (rp (Fintype.card {x : Fin G.p // x ∈ R})) → {x : Fin G.p // x ∉ R} → ℝ :=
    fun c y => (((irqGain G R u σI).filter
      (fun e => (y : Fin G.p) = ψ e ∧ e.1 ∈ rrqColVerts G R φR c)).card : ℝ) with hW
  have hcardAB : Fintype.card (Fin (rp (Fintype.card {x : Fin G.p // x ∈ R})))
      ≤ Fintype.card {x : Fin G.p // x ∉ R} := by
    rw [Fintype.card_fin, hcompl, hcardR]; exact hbrho
  have hposB : 0 < Fintype.card {x : Fin G.p // x ∉ R} := by rw [hcompl]; omega
  obtain ⟨σR, hσRmean⟩ := exists_injection_ge_mean (fun c y => - W c y) hcardAB hposB
  refine ⟨φR, σR, hRbound, hRproper, ?_⟩
  have hbpos : (0 : ℝ) < ((G.p - R.card : ℕ) : ℝ) := by
    have : 0 < G.p - R.card := by omega
    exact_mod_cast this
  -- mean inequality (after negation): ∑_c W c (σR c) ≤ (1/b) ∑_c ∑_y W c y
  have hmean : (∑ c, W c (σR c))
      ≤ (1 / (Fintype.card {x : Fin G.p // x ∉ R} : ℝ)) * ∑ c, ∑ y, W c y := by
    have h := hσRmean
    have e1 : (∑ c, ∑ y, (fun c y => - W c y) c y) = - ∑ c, ∑ y, W c y := by
      simp only [Finset.sum_neg_distrib]
    have e2 : (∑ c, (fun c y => - W c y) c (σR c)) = - ∑ c, W c (σR c) := by
      simp only [Finset.sum_neg_distrib]
    rw [e1, e2, mul_neg] at h
    linarith
  rw [hcompl] at hmean
  -- ∑_c ∑_y W = ∑_c |gain edges covered by colour c|
  have hDsum : (∑ c, ∑ y, W c y)
      = ∑ c, (((irqGain G R u σI).filter (fun e => e.1 ∈ rrqColVerts G R φR c)).card : ℝ) := by
    refine Finset.sum_congr rfl (fun c _ => ?_)
    simp only [hW]
    rw [← Nat.cast_sum, sum_over_compl_weight G R u σI ψ hψ1 φR c]
  have hsumsum : (∑ c, ∑ y, W c y)
      ≤ ((R.card - 1 : ℕ) : ℝ) * ((irqGain G R u σI).card : ℝ) := by
    rw [hDsum]
    have hnat := sum_colVerts_le G R u σI φR
    calc (∑ c, (((irqGain G R u σI).filter (fun e => e.1 ∈ rrqColVerts G R φR c)).card : ℝ))
        = ((∑ c, ((irqGain G R u σI).filter (fun e => e.1 ∈ rrqColVerts G R φR c)).card : ℕ) : ℝ) := by
          rw [Nat.cast_sum]
      _ ≤ (((R.card - 1) * (irqGain G R u σI).card : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = ((R.card - 1 : ℕ) : ℝ) * ((irqGain G R u σI).card : ℝ) := by push_cast; ring
  -- bad gain edges
  have hAeq := prunedIrqTriangles_add_bad G R u σI hσI ψ hψ1 φR σR
  set badG : ℕ := ((irqGain G R u σI).filter
      (fun e => ∃ t' ∈ rrqAssignedTriangles G R φR σR,
          2 ≤ (irqTri G u σI ψ e ∩ t').card)).card with hbadG
  have hbad_le : (badG : ℝ) ≤ ∑ c, W c (σR c) := by
    have h1 := badTri_subset_alg G R u σI ψ hψ1 φR σR
    have h2 : badG ≤ ((irqGain G R u σI).filter
        (fun e => ∃ c, ((σR c : {x : Fin G.p // x ∉ R}) : Fin G.p) = ψ e
            ∧ e.1 ∈ rrqColVerts G R φR c)).card := Finset.card_le_card h1
    have h3 := alg_bad_card_le_sum G R u σI ψ φR σR
    have h4 : badG ≤ ∑ c, ((irqGain G R u σI).filter
        (fun e => ((σR c : {x : Fin G.p // x ∉ R}) : Fin G.p) = ψ e
            ∧ e.1 ∈ rrqColVerts G R φR c)).card := le_trans h2 h3
    have h5 : (∑ c, W c (σR c))
        = ((∑ c, ((irqGain G R u σI).filter
            (fun e => ((σR c : {x : Fin G.p // x ∉ R}) : Fin G.p) = ψ e
                ∧ e.1 ∈ rrqColVerts G R φR c)).card : ℕ) : ℝ) := by
      rw [Nat.cast_sum]
    rw [h5]; exact_mod_cast h4
  -- combine
  have hgc := irqTriangles_card_eq_gain G R u σI hσI ψ hψ1
  have hpr : ((prunedIrqTriangles G R u σI ψ φR σR).card : ℝ)
      = ((irqGain G R u σI).card : ℝ) - (badG : ℝ) := by
    have hsum : (prunedIrqTriangles G R u σI ψ φR σR).card + badG = (irqGain G R u σI).card := by
      rw [hbadG]; exact hAeq
    have : ((prunedIrqTriangles G R u σI ψ φR σR).card : ℝ) + (badG : ℝ)
        = ((irqGain G R u σI).card : ℝ) := by exact_mod_cast hsum
    linarith
  rw [hgc, hpr]
  have hchain : (1 / ((G.p - R.card : ℕ) : ℝ)) * (∑ c, ∑ y, W c y)
      ≤ (1 / ((G.p - R.card : ℕ) : ℝ)) * (((R.card - 1 : ℕ) : ℝ) * ((irqGain G R u σI).card : ℝ)) :=
    mul_le_mul_of_nonneg_left hsumsum (by positivity)
  have hid : (1 - ((R.card - 1 : ℕ) : ℝ) / ((G.p - R.card : ℕ) : ℝ)) * ((irqGain G R u σI).card : ℝ)
      = ((irqGain G R u σI).card : ℝ)
        - (1 / ((G.p - R.card : ℕ) : ℝ)) * (((R.card - 1 : ℕ) : ℝ) * ((irqGain G R u σI).card : ℝ)) := by
    field_simp
  rw [hid]
  linarith [hbad_le, hmean, hchain]

open ShiftedCenter in
/-- Set-level disjointness of the RRQ and QQI triangle families (RRQ triangles have no
`Sum.inr` vertex, QQI triangles have one). -/
private lemma rrq_qqi_setDisjoint (G : SplitGraph) (R : Finset (Fin G.p))
    (φR : Sym2 {x : Fin G.p // x ∈ R} → ℕ)
    (σR : Fin (rp (Fintype.card {x : Fin G.p // x ∈ R})) ↪ {x : Fin G.p // x ∉ R})
    (φQ : Sym2 {x : Fin G.p // x ∉ R} → ℕ)
    (σQ : Fin (rp (Fintype.card {x : Fin G.p // x ∉ R})) ↪ Fin G.q) :
    Disjoint (rrqAssignedTriangles G R φR σR) (qAssignedTriangles G R φQ σQ) := by
  rw [Finset.disjoint_left]
  intro t ht
  simp only [rrqAssignedTriangles, Finset.mem_biUnion, Finset.mem_image] at ht
  obtain ⟨c, _, a, ha, rfl⟩ := ht
  simp only [qAssignedTriangles, Finset.mem_biUnion, Finset.mem_image]
  rintro ⟨c2, _, e2, he2, htri⟩
  have hmem : (Sum.inr (σQ c2) : G.V) ∈ qTriangle G R (σQ c2) e2 := by simp [qTriangle]
  rw [htri] at hmem
  simp only [rrqTriangle, Finset.mem_insert, Finset.mem_image] at hmem
  rcases hmem with hmem | ⟨w, _, hmem⟩
  · nomatch hmem
  · nomatch hmem

open ShiftedCenter in
/-- Set-level disjointness of the RRQ and IRQ triangle families (RRQ triangles have no
`Sum.inr` vertex, IRQ triangles have one). -/
private lemma rrq_irq_setDisjoint (G : SplitGraph) (R : Finset (Fin G.p)) (u : ℕ)
    (φR : Sym2 {x : Fin G.p // x ∈ R} → ℕ)
    (σR : Fin (rp (Fintype.card {x : Fin G.p // x ∈ R})) ↪ {x : Fin G.p // x ∉ R})
    (σI : Fin u → Fin G.q) (ψ : Fin G.p × Fin u → Fin G.p) :
    Disjoint (rrqAssignedTriangles G R φR σR) (irqTriangles G R u σI ψ) := by
  rw [Finset.disjoint_left]
  intro t ht
  simp only [rrqAssignedTriangles, Finset.mem_biUnion, Finset.mem_image] at ht
  obtain ⟨c, _, a, ha, rfl⟩ := ht
  simp only [irqTriangles, Finset.mem_image]
  intro ⟨e', he', htri⟩
  have hIRQ : Sum.inr (σI e'.2) ∈ irqTri G u σI ψ e' := by
    simp [irqTri]
  rw [htri] at hIRQ
  simp only [rrqTriangle, Finset.mem_insert, Finset.mem_image] at hIRQ
  rcases hIRQ with hIRQ | ⟨w, _, hIRQ⟩
  · nomatch hIRQ
  · nomatch hIRQ

open ShiftedCenter in
/-- Set-level disjointness of the QQI and IRQ triangle families when their independent
slots are disjoint (a QQI triangle's `Sum.inl` vertices are all `∉ R`, an IRQ triangle has
one `∈ R`). -/
private lemma qqi_irq_setDisjoint (G : SplitGraph) (R : Finset (Fin G.p)) (u : ℕ)
    (φQ : Sym2 {x : Fin G.p // x ∉ R} → ℕ)
    (σQ : Fin (rp (Fintype.card {x : Fin G.p // x ∉ R})) ↪ Fin G.q)
    (σI : Fin u → Fin G.q) (ψ : Fin G.p × Fin u → Fin G.p) :
    Disjoint (qAssignedTriangles G R φQ σQ) (irqTriangles G R u σI ψ) := by
  rw [Finset.disjoint_left]
  intro t ht
  simp only [qAssignedTriangles, Finset.mem_biUnion, Finset.mem_image] at ht
  obtain ⟨c, _, a, ha, rfl⟩ := ht
  simp only [irqTriangles, Finset.mem_image]
  rintro ⟨e', he', htri⟩
  have heR : e'.1 ∈ R := by
    simp only [irqGain, Finset.mem_filter, Finset.mem_univ, true_and] at he'; exact he'.1
  have hmem : (Sum.inl e'.1 : G.V) ∈ irqTri G u σI ψ e' := by simp [irqTri]
  rw [htri] at hmem
  simp only [qTriangle, Finset.mem_insert, Finset.mem_image, Sym2.mem_toFinset] at hmem
  rcases hmem with hmem | ⟨w, _, hmem⟩
  · nomatch hmem
  · have hval : (w : Fin G.p) = e'.1 := by simpa using hmem
    rw [← hval] at heR
    exact absurd heR w.property

open ShiftedCenter in
private lemma exists_reserved_gain_packing (G : SplitGraph) (R : Finset (Fin G.p))
    (hb2 : 2 ≤ G.p - R.card)
    (hqrb : rp (G.p - R.card) ≤ G.q)
    (hbrho : rp R.card ≤ G.p - R.card)
    (h72 : ∀ i, max R.card (G.q - rp (G.p - R.card)) ≤
      (G.p - R.card) - tt G R i) :
    ∃ T : Finset (Finset G.V), IsTrianglePacking G.graph T ∧
      ((R.card.choose 2 : ℕ) : ℝ)
          + (1 / (G.q : ℝ)) * ∑ i,
              (((G.p - R.card - tt G R i).choose 2 : ℕ) : ℝ)
          + (1 - ((R.card - 1 : ℕ) : ℝ) / (G.p - R.card : ℝ))
              * ((G.q - rp (G.p - R.card) : ℕ) : ℝ) / (G.q : ℝ)
              * (BR G R : ℝ)
        ≤ (T.card : ℝ) := by
  classical
  have hq : 0 < G.q := q_pos_of_rp_le hb2 hqrb
  have hRp : R.card ≤ G.p := le_trans (Finset.card_le_univ _) (by norm_num)
  set u := G.q - rp (G.p - R.card) with hu
  -- QQI edge-colouring of the `R`-complement clique
  obtain ⟨φQ, hQbound, hQproper⟩ :=
    complete_graph_edge_coloring_fintype {x : Fin G.p // x ∉ R}
  have hcardComp : Fintype.card {x : Fin G.p // x ∉ R} = G.p - R.card :=
    card_clique_complement G R
  -- slack factor `λ = 1 - (ρ-1)/b`
  set lam : ℝ := 1 - ((R.card - 1 : ℕ) : ℝ) / ((G.p - R.card : ℕ) : ℝ) with hlam
  -- joint weight over (QQI colours) ⊕ (IRQ slots)
  set f : (Fin (rp (Fintype.card {x : Fin G.p // x ∉ R})) ⊕ Fin u) → Fin G.q → ℝ :=
    fun x i => Sum.elim (fun c => ((qFactorEdges G R φQ c i).card : ℝ))
                        (fun _ => lam * (gg G R i : ℝ)) x with hf
  have hcardA :
      Fintype.card (Fin (rp (Fintype.card {x : Fin G.p // x ∉ R})) ⊕ Fin u)
        ≤ Fintype.card (Fin G.q) := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin, hcardComp, hu]
    omega
  have hposB : 0 < Fintype.card (Fin G.q) := by rw [Fintype.card_fin]; exact hq
  obtain ⟨σj, hσj⟩ := exists_injection_ge_mean f hcardA hposB
  -- QQI and IRQ independent-slot assignments, with disjoint images
  set σQ : Fin (rp (Fintype.card {x : Fin G.p // x ∉ R})) ↪ Fin G.q :=
    (Function.Embedding.inl).trans σj with hσQ
  have hσQc : ∀ c, σQ c = σj (Sum.inl c) := fun c => rfl
  set σI : Fin u → Fin G.q := fun a => σj (Sum.inr a) with hσIdef
  have hσIinj : Function.Injective σI := by
    intro a b hab; exact Sum.inr_injective (σj.injective hab)
  have hdisj : ∀ (c : Fin (rp (Fintype.card {x : Fin G.p // x ∉ R}))) (a : Fin u),
      σQ c ≠ σI a := by
    intro c a h
    rw [hσQc] at h
    have h2 : σj (Sum.inl c) = σj (Sum.inr a) := h
    exact absurd (σj.injective h2) (by simp)
  -- IRQ Galvin colouring on the `u` chosen slots
  have hlist : ∀ a : Fin u, max R.card u ≤ (G.N (σI a) \ R).card := by
    intro a; rw [card_N_sdiff_R]; exact h72 (σI a)
  obtain ⟨ψ, hψ1, hψ2⟩ := irq_list_coloring G R u σI hlist
  -- the three families
  set QQI := qAssignedTriangles G R φQ σQ with hQQI
  set IRQ := irqTriangles G R u σI ψ with hIRQ
  have hQQIpack : IsTrianglePacking G.graph QQI :=
    qAssignedTriangles_isPacking G R φQ hQproper σQ
  have hIRQpack : IsTrianglePacking G.graph IRQ :=
    irqTriangles_isPacking G R u σI hσIinj ψ hψ1 hψ2
  -- pruning against the RRQ family
  obtain ⟨φR, σR, hRbound, hRproper, hprune⟩ :=
    prune_card_bound G R u σI hσIinj ψ hψ1 hb2 hbrho
  rw [← hIRQ, ← hlam] at hprune
  set RRQ := rrqAssignedTriangles G R φR σR with hRRQ
  set PIRQ := prunedIrqTriangles G R u σI ψ φR σR with hPIRQ
  have hRRQpack : IsTrianglePacking G.graph RRQ :=
    rrqAssignedTriangles_isPacking G R φR hRproper σR
  have hPIRQsub : PIRQ ⊆ IRQ := by rw [hPIRQ, hIRQ]; exact Finset.filter_subset _ _
  have hPIRQpack : IsTrianglePacking G.graph PIRQ := by
    refine ⟨fun t ht => hIRQpack.1 t (hPIRQsub ht), ?_⟩
    intro t1 h1 t2 h2 hne
    exact hIRQpack.2 (hPIRQsub h1) (hPIRQsub h2) hne
  -- cross-disjointness between the families
  have cross_RQ : ∀ t₁ ∈ RRQ, ∀ t₂ ∈ QQI, (t₁ ∩ t₂).card ≤ 1 :=
    fun t₁ h₁ t₂ h₂ => rrq_qqi_cross G R φR σR φQ σQ t₁ h₁ t₂ h₂
  have cross_QP : ∀ t₁ ∈ QQI, ∀ t₂ ∈ PIRQ, (t₁ ∩ t₂).card ≤ 1 :=
    fun t₁ h₁ t₂ h₂ => qqi_irq_cross G R u φQ σQ σI ψ hdisj t₁ h₁ t₂ (hPIRQsub h₂)
  have cross_RP : ∀ t₁ ∈ RRQ, ∀ t₂ ∈ PIRQ, (t₁ ∩ t₂).card ≤ 1 := by
    intro t₁ h₁ t₂ h₂
    simp only [hPIRQ, prunedIrqTriangles, Finset.mem_filter] at h₂
    have hcond := h₂.2 t₁ h₁
    rwa [Finset.inter_comm] at hcond
  -- packing of the union
  have hP1pack : IsTrianglePacking G.graph (RRQ ∪ QQI) :=
    IsTrianglePacking.union_of_cross G.graph hRRQpack hQQIpack cross_RQ
  have crossP1 : ∀ t₁ ∈ RRQ ∪ QQI, ∀ t₂ ∈ PIRQ, (t₁ ∩ t₂).card ≤ 1 := by
    intro t₁ h₁ t₂ h₂
    rcases Finset.mem_union.mp h₁ with h | h
    · exact cross_RP t₁ h t₂ h₂
    · exact cross_QP t₁ h t₂ h₂
  have hTpack : IsTrianglePacking G.graph ((RRQ ∪ QQI) ∪ PIRQ) :=
    IsTrianglePacking.union_of_cross G.graph hP1pack hPIRQpack crossP1
  -- set-level disjointness for the cardinality count
  have hdRQ : Disjoint RRQ QQI := rrq_qqi_setDisjoint G R φR σR φQ σQ
  have hdRI : Disjoint RRQ IRQ := rrq_irq_setDisjoint G R u φR σR σI ψ
  have hdQI : Disjoint QQI IRQ := qqi_irq_setDisjoint G R u φQ σQ σI ψ
  have hdP1 : Disjoint (RRQ ∪ QQI) PIRQ := by
    rw [Finset.disjoint_union_left]
    exact ⟨hdRI.mono_right hPIRQsub, hdQI.mono_right hPIRQsub⟩
  have hcardT : ((RRQ ∪ QQI) ∪ PIRQ).card = RRQ.card + QQI.card + PIRQ.card := by
    rw [card_union_of_disjoint hdP1, card_union_of_disjoint hdRQ]
  -- cardinalities of the three families
  have hRRQcard : (RRQ.card : ℝ) = ((R.card.choose 2 : ℕ) : ℝ) := by
    rw [hRRQ, card_rrqAssignedTriangles G R φR σR, sum_rrqFactorEdges_card G R φR hRbound]
  have hQQIcard : (QQI.card : ℝ)
      = ∑ c, ((qFactorEdges G R φQ c (σQ c)).card : ℝ) := by
    rw [hQQI, card_qAssignedTriangles, Nat.cast_sum]
  have hIRQcard : (IRQ.card : ℝ) = ∑ a : Fin u, (gg G R (σI a) : ℝ) := by
    rw [hIRQ, card_irqTriangles G R u σI hσIinj ψ hψ1, Nat.cast_sum]
    exact Finset.sum_congr rfl (fun a _ => by rw [gg_eq_inter_card])
  -- value of the averaged assignment
  have hjoint_val : (∑ x, f x (σj x))
      = (∑ c, ((qFactorEdges G R φQ c (σQ c)).card : ℝ)) + lam * (IRQ.card : ℝ) := by
    rw [Fintype.sum_sum_type]
    have h1 : (∑ a, f (Sum.inl a) (σj (Sum.inl a)))
        = ∑ c, ((qFactorEdges G R φQ c (σQ c)).card : ℝ) := by
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [hσQc]; simp only [hf, Sum.elim_inl]
    have h2 : (∑ b, f (Sum.inr b) (σj (Sum.inr b))) = lam * (IRQ.card : ℝ) := by
      rw [hIRQcard, Finset.mul_sum _ _ _]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      simp only [hf, Sum.elim_inr, hσIdef]
    rw [h1, h2]
  -- value of the mean
  have hBRcast : (∑ i, (gg G R i : ℝ)) = (BR G R : ℝ) := by
    rw [BR]; push_cast; rfl
  have hmean_val : (1 / (Fintype.card (Fin G.q) : ℝ)) * ∑ x, ∑ i, f x i
      = (1 / (G.q : ℝ)) * (∑ i, (((G.p - R.card - tt G R i).choose 2 : ℕ) : ℝ))
          + lam * (u : ℝ) / (G.q : ℝ) * (BR G R : ℝ) := by
    rw [Fintype.card_fin]
    have h1 : (∑ a, ∑ i, f (Sum.inl a) i)
        = ∑ i, (((G.p - R.card - tt G R i).choose 2 : ℕ) : ℝ) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← sum_qFactorEdges_card G R φQ hQbound i, Nat.cast_sum]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      simp only [hf, Sum.elim_inl]
    have hconst : ∀ b : Fin u, (∑ i, f (Sum.inr b) i) = lam * (BR G R : ℝ) := by
      intro b
      rw [← hBRcast, Finset.mul_sum _ _ _]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [hf, Sum.elim_inr]
    have h2 : (∑ b, ∑ i, f (Sum.inr b) i) = (u : ℝ) * (lam * (BR G R : ℝ)) := by
      rw [Finset.sum_congr rfl (fun b _ => hconst b), Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hsplit : (∑ x, ∑ i, f x i)
        = (∑ i, (((G.p - R.card - tt G R i).choose 2 : ℕ) : ℝ))
            + (u : ℝ) * (lam * (BR G R : ℝ)) := by
      rw [Fintype.sum_sum_type, h1, h2]
    rw [hsplit]; ring
  -- combine
  refine ⟨(RRQ ∪ QQI) ∪ PIRQ, hTpack, ?_⟩
  have hlam_bridge :
      (1 - ((R.card - 1 : ℕ) : ℝ) / (G.p - R.card : ℝ)) = lam := by
    rw [hlam, Nat.cast_sub hRp]
  rw [hlam_bridge]
  have hmean_le :
      (1 / (G.q : ℝ)) * (∑ i, (((G.p - R.card - tt G R i).choose 2 : ℕ) : ℝ))
          + lam * (u : ℝ) / (G.q : ℝ) * (BR G R : ℝ)
        ≤ (∑ c, ((qFactorEdges G R φQ c (σQ c)).card : ℝ)) + lam * (IRQ.card : ℝ) := by
    have h := hσj
    rw [hjoint_val, hmean_val] at h
    exact h
  have hgoalsum : ((R.card.choose 2 : ℕ) : ℝ)
        + ((1 / (G.q : ℝ)) * (∑ i, (((G.p - R.card - tt G R i).choose 2 : ℕ) : ℝ)))
        + lam * (u : ℝ) / (G.q : ℝ) * (BR G R : ℝ)
      ≤ (RRQ.card : ℝ) + (QQI.card : ℝ) + (PIRQ.card : ℝ) := by
    rw [hRRQcard, hQQIcard]
    linarith [hmean_le, hprune]
  rw [hcardT]
  push_cast
  linarith [hgoalsum]

open ShiftedCenter in
/-- The packing estimate supplied by the three §7.2 families.  The three summands are,
respectively, RRQ, the averaged QQI family, and the reserved IRQ gain. -/
theorem reserved_gain_packing_bound (G : SplitGraph) (R : Finset (Fin G.p))
    (hb2 : 2 ≤ G.p - R.card)
    (hqrb : rp (G.p - R.card) ≤ G.q)
    (hbrho : rp R.card ≤ G.p - R.card)
    (h72 : ∀ i, max R.card (G.q - rp (G.p - R.card)) ≤
      (G.p - R.card) - tt G R i) :
    ((R.card.choose 2 : ℕ) : ℝ)
        + (1 / (G.q : ℝ)) * ∑ i,
            (((G.p - R.card - tt G R i).choose 2 : ℕ) : ℝ)
        + (1 - ((R.card - 1 : ℕ) : ℝ) / (G.p - R.card : ℝ))
            * ((G.q - rp (G.p - R.card) : ℕ) : ℝ) / (G.q : ℝ)
            * (BR G R : ℝ)
      ≤ (G.nu3' : ℝ) := by
  obtain ⟨T, hT, hcount⟩ := exists_reserved_gain_packing G R hb2 hqrb hbrho h72
  exact hcount.trans (by exact_mod_cast le_nu3_of_packing G.graph hT)

open ShiftedCenter in
/-- **E-7.1 (Reserved-gain shifted-center inequality)** (LEDGER E-7.1).  With
`ρ=|R|`, `b=p−ρ`, `r_b=χ'(K_b)`, `u=q−r_b`, `θ=max(ρ−1,0)/b`, `κ=1−2(1−θ)u/q`,
under (7.1)–(7.2). -/
theorem E_7_1 (G : SplitGraph) (R : Finset (Fin G.p))
    (hb2 : 2 ≤ G.p - R.card)
    (hqrb : rp (G.p - R.card) ≤ G.q)
    (hbrho : rp R.card ≤ G.p - R.card)
    (h72 : ∀ i, max R.card (G.q - rp (G.p - R.card)) ≤ (G.p - R.card) - tt G R i) :
    ((G.Phi : ℤ) : ℝ)
      ≤ (G.n : ℝ) ^ 2 / 6 + (G.p : ℝ) / 2 - (G.s : ℝ) ^ 2 / 6
        + (G.s : ℝ) * (R.card : ℝ) - 2 * (R.card : ℝ) ^ 2
        + (1 - 2 * (1 - (max (R.card - 1) 0 : ℕ) / ((G.p - R.card : ℕ) : ℝ))
              * ((G.q - rp (G.p - R.card) : ℕ) : ℝ) / (G.q : ℝ)) * (BR G R : ℝ)
        + (((G.s : ℝ) - 2 * (R.card : ℝ) - 1) * (AR G R : ℝ) - (A2R G R : ℝ))
            / (G.q : ℝ) := by
  by_cases hq : G.q = 0 <;> simp_all +decide [ -Nat.cast_sub, Nat.cast_sub ( show R.card ≤ G.p from le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ) ] ; ring_nf at *;
  · unfold rp at hqrb; rcases k : G.p - Finset.card R with ( _ | _ | k ) <;> simp_all +arith +decide;
    grind +revert;
  · have h_packing_bound : (G.nu3' : ℝ) ≥ ((R.card.choose 2 : ℕ) : ℝ) + (1 / (G.q : ℝ)) * ∑ i, (((G.p - R.card - tt G R i).choose 2 : ℕ) : ℝ) + (1 - ((R.card - 1 : ℕ) : ℝ) / (G.p - R.card : ℝ)) * ((G.q - rp (G.p - R.card) : ℕ) : ℝ) / (G.q : ℝ) * (BR G R : ℝ) := by
      convert reserved_gain_packing_bound G R hb2 hqrb hbrho _ using 1;
      grind;
    have h_edge_count : (G.edgeCount : ℝ) = (G.p.choose 2 : ℕ) + G.q * (G.p - R.card) + BR G R - AR G R := by
      have h_edge_count : (G.edgeCount : ℝ) + (AR G R : ℝ) = (G.p.choose 2 : ℕ) + G.q * (G.p - R.card) + (BR G R : ℝ) := by
        convert congr_arg ( ( ↑ ) : ℕ → ℝ ) ( edgeCount_shifted G R ) using 1 ; norm_num [ AR, BR ] ; ring;
        norm_num [ Nat.cast_sub ( show #R ≤ G.p from le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ) ] ; ring;
      linarith;
    have h_choose_identity : ∀ i, (((G.p - R.card - tt G R i).choose 2 : ℕ) : ℝ) = ((G.p - R.card : ℝ) ^ 2 - (G.p - R.card : ℝ) - 2 * (G.p - R.card : ℝ) * (tt G R i : ℝ) + (tt G R i : ℝ) ^ 2 + (tt G R i : ℝ)) / 2 := by
      intro i
      have h_choose_identity : ∀ n : ℕ, (n.choose 2 : ℝ) = (n * (n - 1)) / 2 := by
        exact fun n => by induction n <;> norm_num [ Nat.choose ] at * ; linarith;
      convert h_choose_identity ( G.p - R.card - tt G R i ) using 1 ; ring;
      rw [ Nat.cast_sub, Nat.cast_sub ] <;> repeat linarith [ h72 i ] ;
      · exact le_trans ( Finset.card_le_univ _ ) ( by norm_num );
      · exact le_trans ( Finset.card_le_card ( show ( G.S i \ R ) ⊆ Finset.univ \ R from Finset.sdiff_subset_sdiff ( Finset.subset_univ _ ) ( Finset.Subset.refl _ ) ) ) ( by simp +decide [ Finset.card_sdiff, * ] );
    have h_sum_choose_identity : ∑ i, (((G.p - R.card - tt G R i).choose 2 : ℕ) : ℝ) = ((G.p - R.card : ℝ) ^ 2 - (G.p - R.card : ℝ)) * G.q / 2 - (G.p - R.card : ℝ) * AR G R + A2R G R / 2 + AR G R / 2 := by
      simp +decide [ h_choose_identity, Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_div, AR, A2R ] ; ring;
      norm_num [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul ] ; ring;
    have h_choose_identity : (G.p.choose 2 : ℕ) = (G.p * (G.p - 1) : ℝ) / 2 ∧ (R.card.choose 2 : ℕ) = (R.card * (R.card - 1) : ℝ) / 2 := by
      exact ⟨ by rw [ Nat.choose_two_right ] ; induction G.p <;> norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mod_two_of_bodd ] at *, by rw [ Nat.choose_two_right ] ; induction #R <;> norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mod_two_of_bodd ] at * ⟩;
    simp_all +decide [ SplitGraph.Phi, SplitGraph.n, SplitGraph.s ];
    field_simp at *;
    grind

end PaperIII