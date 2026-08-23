import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort

open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Prüfer Encoding for Labeled Trees

This module formalizes the encoding direction of Heinz Prüfer's (1918) bijective
correspondence between labeled trees on $n$ vertices and sequences of length $n - 2$.

## Mathematical Details

Given a labeled tree $T$ on vertex set $\{1, \dots, n\}$ ($n \ge 2$):
1. Find the leaf (vertex of degree 1) with the smallest label.
2. Record its unique neighbor in the sequence.
3. Remove that leaf and its incident edge from $T$.
4. Repeat $n - 2$ times to produce the Prüfer sequence of length $n - 2$.

## Main Definitions
- `LabeledTree`: Structure representing a labeled tree on `Fin n`.
- `LabeledTree.ext`: Extensionality for labeled trees.
- `LabeledTree.isTree`: Proof that a `LabeledTree` satisfies `SimpleGraph.IsTree`.
- `LabeledTree.edge_card`: Number of edges in any labeled tree on $n$ vertices is $n - 1$.
- `PruferSequence`: Type alias `Fin (n - 2) → Fin n`.
- `PruferSequence.prufer_sequence_card`: Cardinality $|PruferSequence(n)| = n^{n - 2}$.
- `pruferLeaves`: Candidate leaves not in the remaining sequence list.
- `pruferLeaves_nonempty`: Nonemptiness lemma for candidate leaves.
- `smallestLeaf`: Leaf with smallest label.
- `leafNeighbor`: Unique neighbor of a leaf.
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

variable (T : LabeledTree n)

/-- A labeled tree satisfies `SimpleGraph.IsTree`. -/
theorem isTree : T.graph.IsTree :=
  ⟨T.connected, T.is_acyclic⟩

/-- Any tree on $n$ vertices has exactly $n - 1$ edges. -/
theorem edge_card (hn : 0 < n) [Fintype T.graph.edgeSet] :
    Fintype.card T.graph.edgeSet = n - 1 := by
  have h := T.isTree.card_edgeFinset
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  have hedge : T.graph.edgeFinset.card = Fintype.card T.graph.edgeSet := by
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

/-- Detect the leaf with the smallest label among remaining vertices `S`. -/
noncomputable def smallestLeaf (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Option (Fin n) :=
  let leaves := S.filter (fun v => (S.filter (fun u => G.Adj v u)).card = 1)
  if h : leaves.Nonempty then
    some (leaves.min' h)
  else
    none

/-- Find the unique neighbor of vertex `v` among `S`. -/
noncomputable def leafNeighbor (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v : Fin n) : Option (Fin n) :=
  let neighbors := S.filter (fun u => G.Adj v u)
  if h : neighbors.Nonempty then
    some (neighbors.min' h)
  else
    none

/-- One leaf-peeling step: finds the smallest leaf in `S`, records its neighbor, and removes the leaf. -/
noncomputable def pruferPeelStep (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Option (Fin n) × Finset (Fin n) :=
  match smallestLeaf G S with
  | some v => (leafNeighbor G S v, S.erase v)
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
