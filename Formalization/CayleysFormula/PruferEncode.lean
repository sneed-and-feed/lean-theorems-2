import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort

open Classical

/-!
# Prüfer Encoding for Labeled Trees

This module formalizes the encoding direction of Heinz Prüfer's (1918) bijective
correspondence between labeled trees on $n$ vertices and sequences of length $n - 2$.

## Mathematical Details

Given a labeled tree $T$ on vertex set $\{1, \dots, n\}$ ($n \ge 2$):
1. Find the leaf (vertex of degree 1 in the remaining vertex set) with the smallest label.
2. Record its unique neighbor in the sequence.
3. Remove that leaf and its incident edge from $T$.
4. Repeat $n - 2$ times to produce the Prüfer sequence of length $n - 2$.

## Computational Transparency

The encoding constructions (`smallestLeaf`, `minNeighbor`, `pruferPeelStep`, `pruferPeelIter`, `pruferCode`)
are mathematically constructive using classical finite-set choice (`noncomputable`), operating on
`Finset.min'` and classical decidability of adjacency, rather than executable/computable in Lean's runtime sense.

## Main Definitions & Theorems
- `LabeledTree`: Structure representing a labeled tree on `Fin n`.
- `LabeledTree.ext`: Extensionality for labeled trees.
- `LabeledTree.ext_edgeFinset`: Extensionality for labeled trees via edge finsets.
- `LabeledTree.isTree`: Proof that a `LabeledTree` satisfies `SimpleGraph.IsTree`.
- `LabeledTree.edge_card`: Number of edges in any labeled tree on $n$ vertices is $n - 1$.
- `PruferSequence`: Type alias `Fin (n - 2) → Fin n`.
- `PruferSequence.prufer_sequence_card`: Cardinality $|PruferSequence(n)| = n^{n - 2}$.
- `vertNeighbors`: Neighbors of a vertex among remaining vertices `S`.
- `pruferLeaves`: Candidate leaves not in the remaining sequence list.
- `pruferLeaves_nonempty`: Nonemptiness lemma for candidate leaves.
- `smallestLeaf`: Leaf (degree 1 in `S`) with smallest label.
- `minNeighbor`: Minimum neighbor of a vertex among remaining vertices `S`.
- `unique_neighbor_of_leaf`: Dedicated lemma establishing that `minNeighbor` is the unique neighbor when degree in `S` is 1.
- `pruferPeelStep`: Single leaf-peeling step.
- `pruferPeelIter`: Iterative leaf-peeling.
- `pruferCode`: Constructive Prüfer encoding function.
-/

variable {n : ℕ}

/-- A labeled tree on vertex set `Fin n` is a simple graph that is both connected and acyclic. -/
structure LabeledTree (n : ℕ) where
  /-- The underlying simple graph on `Fin n` -/
  graph : SimpleGraph (Fin n)
  /-- The graph is connected -/
  connected : graph.Connected
  /-- The graph has no cycles -/
  is_acyclic : graph.IsAcyclic

namespace LabeledTree

@[ext]
theorem ext {n : ℕ} (T1 T2 : LabeledTree n) (h : T1.graph = T2.graph) : T1 = T2 := by
  cases T1; cases T2; cases h; rfl

/-- Two labeled trees with the same edge finsets are equal. -/
theorem ext_edgeFinset {n : ℕ} (T1 T2 : LabeledTree n)
    (h : T1.graph.edgeFinset = T2.graph.edgeFinset) : T1 = T2 := by
  apply LabeledTree.ext
  rw [← SimpleGraph.edgeSet_inj, ← SimpleGraph.coe_edgeFinset T1.graph, ← SimpleGraph.coe_edgeFinset T2.graph, h]

variable (T : LabeledTree n)

/-- A labeled tree satisfies `SimpleGraph.IsTree`. -/
theorem isTree : T.graph.IsTree :=
  ⟨T.connected, T.is_acyclic⟩

/-- Any tree on $n$ vertices has exactly $n - 1$ edges. -/
theorem edge_card (_hn : 0 < n) [Fintype T.graph.edgeSet] :
    Fintype.card T.graph.edgeSet = n - 1 := by
  have h := T.isTree.card_edgeFinset
  have _hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  have _hedge : T.graph.edgeFinset.card = Fintype.card T.graph.edgeSet := by
    rw [SimpleGraph.edgeFinset, Set.toFinset_card]
  omega

end LabeledTree

/-- A Prüfer sequence of order $n$ is a sequence of $n - 2$ elements from `Fin n`. -/
abbrev PruferSequence (n : ℕ) := Fin (n - 2) → Fin n

namespace PruferSequence

/-- The number of Prüfer sequences of length $n - 2$ with symbols in `Fin n` is $n^{n - 2}$. -/
theorem prufer_sequence_card (n : ℕ) :
    Fintype.card (PruferSequence n) = n ^ (n - 2) := by
  simp only [Fintype.card_fun, Fintype.card_fin]

end PruferSequence

/-- The set of candidate leaves from `S` not appearing in the remainder list `L`. -/
def pruferLeaves (n : ℕ) (S : Finset (Fin n)) (L : List (Fin n)) : Finset (Fin n) :=
  S.filter (fun x => x ∉ L)

/-- Candidate leaves set is always nonempty when $|L| + 2 \le |S|$. -/
theorem pruferLeaves_nonempty {n : ℕ} {S : Finset (Fin n)} {L : List (Fin n)}
    (hS : L.length + 2 ≤ S.card) :
    (pruferLeaves n S L).Nonempty := by
  rw [pruferLeaves]
  have h_sub : (S.filter (fun x => x ∈ L)).card ≤ L.length := by
    have : (S.filter (fun x => x ∈ L)) ⊆ L.toFinset := by
      intro x hx
      simp only [Finset.mem_filter, List.mem_toFinset] at hx ⊢
      exact hx.2
    exact le_trans (Finset.card_le_card this) L.toFinset_card_le
  have h_sum : (S.filter (fun x => x ∈ L)).card + (S.filter (fun x => x ∉ L)).card = S.card :=
    S.card_filter_add_card_filter_not (fun x => x ∈ L)
  have h_pos : 0 < (S.filter (fun x => x ∉ L)).card := by omega
  exact Finset.card_pos.mp h_pos

/-- The neighbors of vertex `v` among remaining vertices `S`. -/
noncomputable def vertNeighbors (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v : Fin n) : Finset (Fin n) :=
  S.filter (fun u => G.Adj v u)

@[simp] lemma mem_vertNeighbors (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v u : Fin n) :
    u ∈ vertNeighbors G S v ↔ u ∈ S ∧ G.Adj v u :=
  Finset.mem_filter

/-- Selects the vertex with the smallest label among all vertices in `S` that have degree 1 in
the induced subgraph on `S` (i.e., exactly one neighbor in `S`), or `none` if no such degree-1 vertex exists. -/
noncomputable def smallestLeaf (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Option (Fin n) :=
  let leaves := S.filter (fun v => (vertNeighbors G S v).card = 1)
  if h : leaves.Nonempty then
    some (leaves.min' h)
  else
    none

/-- Selects the minimum neighbor of vertex `v` among vertices in `S` with respect to the standard
ordering on `Fin n`, or `none` if `v` has no neighbors in `S`. Note that this definition simply takes
the minimum available neighbor and does not require or assume uniqueness at the definition level. -/
noncomputable def minNeighbor (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v : Fin n) : Option (Fin n) :=
  let neighbors := vertNeighbors G S v
  if h : neighbors.Nonempty then
    some (neighbors.min' h)
  else
    none

/-- When a vertex `v` has exactly one neighbor in `S` (i.e. degree 1 in the induced subgraph on `S`),
`minNeighbor G S v` returns that unique neighbor `a ∈ S`, satisfying `vertNeighbors G S v = {a}`
and `∀ u ∈ S, G.Adj v u ↔ u = a`. -/
theorem unique_neighbor_of_leaf (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v : Fin n)
    (h_card : (vertNeighbors G S v).card = 1) :
    ∃ a ∈ S, minNeighbor G S v = some a ∧ vertNeighbors G S v = {a} ∧
      ∀ u ∈ S, G.Adj v u ↔ u = a := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h_card
  have ha_mem : a ∈ vertNeighbors G S v := by rw [ha]; exact Finset.mem_singleton_self a
  rw [mem_vertNeighbors] at ha_mem
  have h_min : minNeighbor G S v = some a := by
    dsimp [minNeighbor]
    have h_ne : (vertNeighbors G S v).Nonempty := by rw [ha]; exact Finset.singleton_nonempty a
    split_ifs
    · congr 1
      have ha_in : a ∈ vertNeighbors G S v := by rw [ha]; exact Finset.mem_singleton_self a
      refine le_antisymm (Finset.min'_le _ a ha_in) ?_
      refine Finset.le_min' _ h_ne a (fun u hu => ?_)
      rw [ha, Finset.mem_singleton] at hu
      subst hu
      rfl
  refine ⟨a, ha_mem.1, h_min, ha, fun u hu => ?_⟩
  constructor
  · intro hadj
    have : u ∈ vertNeighbors G S v := by rw [mem_vertNeighbors]; exact ⟨hu, hadj⟩
    rw [ha, Finset.mem_singleton] at this
    exact this
  · rintro rfl
    exact ha_mem.2

/-- Alias for `minNeighbor` preserved for backwards compatibility. -/
noncomputable abbrev leafNeighbor (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v : Fin n) : Option (Fin n) :=
  minNeighbor G S v

/-- One leaf-peeling step: finds the smallest leaf in `S`, records its neighbor, and removes the leaf. -/
noncomputable def pruferPeelStep (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Option (Fin n) × Finset (Fin n) :=
  match smallestLeaf G S with
  | some v => (minNeighbor G S v, S.erase v)
  | none => (none, S)

/-- Peel `k` leaves iteratively from the vertex set `S`. -/
noncomputable def pruferPeelIter : ℕ → SimpleGraph (Fin n) → Finset (Fin n) → List (Fin n)
  | 0, _, _ => []
  | k + 1, G, S =>
    let (u_opt, S') := pruferPeelStep G S
    match u_opt with
    | some u => u :: pruferPeelIter k G S'
    | none => pruferPeelIter k G S'

/-- Prüfer encoding algorithm: converts a labeled tree into a Prüfer sequence of length $n - 2$. -/
noncomputable def pruferCode (T : LabeledTree n) : PruferSequence n :=
  let l := pruferPeelIter (n - 2) T.graph Finset.univ
  fun (i : Fin (n - 2)) =>
    if h : (i : ℕ) < l.length then
      l.get ⟨i.val, h⟩
    else
      i.castLT (by omega)
