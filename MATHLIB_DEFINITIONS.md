# Mathlib definitions used in the statements

The statements in [`ErdosPaperIIIChallenge.lean`](ErdosPaperIIIChallenge.lean) use the following
Mathlib definitions. They are reproduced verbatim from Mathlib at the pinned revision
`c55e6e786f49471c72fbddbec5415808896aec1e` (Lean `v4.35.0-rc3`).

## `SimpleGraph` — `Mathlib/Combinatorics/SimpleGraph/Basic.lean:95`

```lean
structure SimpleGraph (V : Type u) where
  /-- The adjacency relation of a simple graph. -/
  Adj : V → V → Prop
  symm : Std.Symm Adj := by aesop_graph
  loopless : Std.Irrefl Adj := by aesop_graph
```

## `SimpleGraph.IsClique` — `Mathlib/Combinatorics/SimpleGraph/Clique.lean:48`

```lean
abbrev IsClique (s : Set α) : Prop :=
  s.Pairwise G.Adj
```

## `SimpleGraph.IsIndepSet` — `Mathlib/Combinatorics/SimpleGraph/Clique.lean:907`

```lean
abbrev IsIndepSet (s : Set α) : Prop :=
  s.Pairwise (fun v w ↦ ¬G.Adj v w)
```

## `SimpleGraph.IsNClique` — `Mathlib/Combinatorics/SimpleGraph/Clique.lean:246`

```lean
structure IsNClique (n : ℕ) (s : Finset α) : Prop where
  isClique : G.IsClique s
  card_eq : #s = n
```

## `SimpleGraph.cliqueFinset` — `Mathlib/Combinatorics/SimpleGraph/Clique.lean:854`

```lean
def cliqueFinset (n : ℕ) : Finset (Finset α) := {s | G.IsNClique n s}
```

## `SimpleGraph.edgeFinset` — `Mathlib/Combinatorics/SimpleGraph/Finite.lean:59`

```lean
def edgeFinset : Finset (Sym2 V) :=
  Set.toFinset G.edgeSet
```

## `sInf` and `sSup` on `ℕ` — `Mathlib/Order/Lattice/Nat.lean:29`, `:33`

```lean
noncomputable instance : InfSet ℕ :=
  ⟨fun s ↦ if h : ∃ n, n ∈ s then @Nat.find (fun n ↦ n ∈ s) _ h else 0⟩

noncomputable instance : SupSet ℕ :=
  ⟨fun s ↦ if h : ∃ n, ∀ a ∈ s, a ≤ n then @Nat.find (fun n ↦ ∀ a ∈ s, a ≤ n) _ h else 0⟩
```

So `nu3 G` (a supremum of a bounded set of natural numbers) is the maximum size of a triangle
packing, and `cp G` (an infimum of a nonempty set) is the minimum size of a clique partition.

The remaining notions (`Finset.card`, `Fintype.card`, `Set`, `Disjoint`, `Nonempty`, the real
numbers and their order) are the standard ones of Lean core and Mathlib.
