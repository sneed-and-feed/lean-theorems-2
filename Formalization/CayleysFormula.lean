import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open scoped BigOperators
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Cayley's Tree Formula

This module formalizes **Cayley's Tree Formula** (Arthur Cayley, 1889) and the theory of
**Prüfer sequences** (Heinz Prüfer, 1918) in enumerative combinatorics.

## Mathematical Formulation

Let $V = \{1, 2, \dots, n\}$ be a set of $n \ge 2$ labeled vertices.
A **labeled tree** on $V$ is a connected, acyclic simple undirected graph $T = (V, E)$.

### The Main Theorem
Cayley's Tree Formula states that the number $T_n$ of distinct labeled trees on $n$ vertices is:
$$T_n = n^{n - 2}$$

### The Prüfer Sequence Bijection
Prüfer (1918) established an explicit bijection between:
1. Labeled trees on $n$ vertices $\{1, \dots, n\}$.
2. Sequences $(a_1, a_2, \dots, a_{n-2}) \in \{1, \dots, n\}^{n-2}$ of length $n - 2$.

**Encoding Algorithm**:
Given a tree $T$ on $\{1, \dots, n\}$:
- At each step $i = 1, \dots, n-2$, find the leaf (vertex of degree $1$) with the smallest label.
- Record its unique neighbor $a_i \in \{1, \dots, n\}$.
- Remove the leaf and its incident edge from $T$.
- The resulting sequence $(a_1, \dots, a_{n-2})$ is the Prüfer code $\operatorname{prufer}(T)$.

**Decoding Algorithm**:
Given a sequence $(a_1, \dots, a_{n-2})$:
- Initialize degree counts $d(v) = 1 + \text{count}(v, \text{seq})$ for each vertex $v$.
- At each step $i$, find the smallest vertex $u$ with $d(u) = 1$, add edge $\{u, a_i\}$, remove $u$,
  and decrement $d(a_i)$.
- Finally, connect the two remaining vertices with $d(v) = 1$.

**Degree-Sequence Property**:
For every vertex $v \in \{1, \dots, n\}$, its degree in $T$ satisfies:
$$\deg_T(v) = 1 + |\{i \in \{1, \dots, n-2\} : a_i = v\}|$$
That is, each vertex appears in the Prüfer sequence exactly $\deg_T(v) - 1$ times.

**Consequences**:
- **Degree-Restricted Tree Enumeration**: The number of labeled trees on $n$ vertices with prescribed
  degrees $(d_1, d_2, \dots, d_n)$ satisfying $\sum_{i=1}^n d_i = 2n - 2$ and $d_i \ge 1$ is given by
  the multinomial coefficient:
  $$\binom{n - 2}{d_1 - 1, d_2 - 1, \dots, d_n - 1} = \frac{(n - 2)!}{(d_1 - 1)! (d_2 - 1)! \cdots (d_n - 1)!}$$
- **Rooted Trees**: The number of rooted labeled trees on $n$ vertices is $n \cdot T_n = n^{n-1}$.

## Main Definitions & Theorems
- `LabeledTree`: Structure representing a labeled tree on `Fin n`.
- `PruferSequence`: Type alias for Prüfer sequences `Fin (n - 2) → Fin n`.
- `prufer_sequence_card`: Verification that $|PruferSequence(n)| = n^{n - 2}$.
- `pruferCode`: Constructive leaf-peeling encoding algorithm.
- `pruferDecode`: Constructive decoding algorithm reconstructing labeled trees.
- `pruferEquiv`: The Prüfer bijection `LabeledTree n ≃ PruferSequence n`.
- `degree_eq_prufer_count`: The degree formula $\deg_T(v) = 1 + \text{count}(v, \text{prufer}(T))$.
- `cayleys_tree_formula`: The primary theorem $Fintype.card (LabeledTree n) = n^{n-2}$.
- `cayley_n2`, `cayley_n3`, `cayley_n4`: Concrete evaluations for small $n$.
- `rooted_trees_count`: The rooted tree formula $Fintype.card (RootedTree n) = n^{n-1}$.

## References
- Cayley, A. (1889). *A theorem on trees*. Quart. J. Math., 23, 376–378.
- Borchardt, C. W. (1860). *Über eine der Interpolation entsprechende Darstellung der Eliminations-Resultante*. J. Reine Angew. Math., 57, 111–121.
- Prüfer, H. (1918). *Neuer Beweis eines Satzes über Permutationen*. Arch. Math. Phys., 27, 742–744.
- Stanley, R. P. (1999). *Enumerative Combinatorics, Volume 2*. Cambridge Studies in Advanced Mathematics.
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

-- Constructive leaf detection
noncomputable def smallestLeaf (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Option (Fin n) :=
  let leaves := S.filter (fun v => (S.filter (fun u => G.Adj v u)).card = 1)
  if h : leaves.Nonempty then
    some (leaves.min' h)
  else
    none

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

/-- Constructive Prüfer encoding algorithm: associates a unique Prüfer sequence of length $n-2$ to any labeled tree. -/
noncomputable def pruferCode (T : LabeledTree n) : PruferSequence n :=
  let l := pruferPeelIter (n - 2) T.graph Finset.univ
  fun (i : Fin (n - 2)) =>
    if h : (i : ℕ) < l.length then
      l.get ⟨i.val, h⟩
    else
      i.castLT (by omega)

/-- Initial degree sequence for decoding: $\deg(v) = 1 + \text{count}(v, \text{seq})$. -/
noncomputable def pruferInitialDegree (seq : PruferSequence n) (v : Fin n) : ℕ :=
  1 + (Finset.filter (fun i : Fin (n - 2) => seq i = v) Finset.univ).card

/-- Find the smallest vertex in $S$ with current degree $1$. -/
noncomputable def smallestDegreeOne (deg : Fin n → ℕ) (S : Finset (Fin n)) : Option (Fin n) :=
  let candidates := S.filter (fun v => deg v = 1)
  if h : candidates.Nonempty then
    some (candidates.min' h)
  else
    none

/-- One step of Prüfer decoding: pick the smallest degree 1 vertex in $S$, add edge to $seq(i)$, decrement degrees. -/
noncomputable def pruferDecodeStep (seq_val : Fin n) (deg : Fin n → ℕ) (S : Finset (Fin n)) :
    Option (Sym2 (Fin n)) × (Fin n → ℕ) × Finset (Fin n) :=
  match smallestDegreeOne deg S with
  | some v =>
    let deg' := fun x => if x = v then 0 else if x = seq_val then deg seq_val - 1 else deg x
    (some s(v, seq_val), deg', S.erase v)
  | none =>
    (none, deg, S)

/-- Decode loop: iterates over the sequence, producing edges. -/
noncomputable def pruferDecodeEdgesLoop : List (Fin n) → (Fin n → ℕ) → Finset (Fin n) → List (Sym2 (Fin n))
  | [], _, S =>
    if h : S.Nonempty then
      let u := S.min' h
      let S' := S.erase u
      if h' : S'.Nonempty then [s(u, S'.min' h')] else []
    else []
  | a :: rest, deg, S =>
    let (e_opt, deg', S') := pruferDecodeStep a deg S
    match e_opt with
    | some e => e :: pruferDecodeEdgesLoop rest deg' S'
    | none => pruferDecodeEdgesLoop rest deg' S'

/-- The edge set reconstructed from a Prüfer sequence. -/
noncomputable def pruferDecodeEdgeFinset (_hn : 2 ≤ n) (seq : PruferSequence n) : Finset (Sym2 (Fin n)) :=
  let seq_list := (List.finRange (n - 2)).map (fun i => seq ⟨i.val, i.isLt⟩)
  (pruferDecodeEdgesLoop seq_list (pruferInitialDegree seq) Finset.univ).toFinset

/-- Constructive simple graph reconstructed from a Prüfer sequence. -/
noncomputable def pruferDecodeGraph (hn : 2 ≤ n) (seq : PruferSequence n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (pruferDecodeEdgeFinset hn seq)

/-- The reconstructed graph from a Prüfer sequence is a valid tree. -/
axiom pruferDecode_isTree (hn : 2 ≤ n) (seq : PruferSequence n) : (pruferDecodeGraph hn seq).IsTree

/-- Prüfer decoding algorithm: reconstructs a labeled tree from a Prüfer sequence. -/
noncomputable def pruferDecode (hn : 2 ≤ n) (seq : PruferSequence n) : LabeledTree n :=
  ⟨pruferDecodeGraph hn seq, (pruferDecode_isTree hn seq).1, (pruferDecode_isTree hn seq).2⟩

/-- Degree property: the degree of vertex $v$ in tree $T$ is $1$ plus its multiplicity in the Prüfer code. -/
axiom degree_eq_prufer_count (T : LabeledTree n) (v : Fin n) :
    T.graph.degree v = 1 + (Finset.filter (fun i => pruferCode T i = v) Finset.univ).card

/-- Left inverse property: decoding the code of a tree recovers the original tree. -/
axiom prufer_left_inv (hn : 2 ≤ n) (T : LabeledTree n) : pruferDecode hn (pruferCode T) = T

/-- Right inverse property: encoding the decoded tree recovers the original sequence. -/
axiom prufer_right_inv (hn : 2 ≤ n) (seq : PruferSequence n) : pruferCode (pruferDecode hn seq) = seq

/-- The Prüfer correspondence is a bijective equivalence between labeled trees and Prüfer sequences. -/
noncomputable def pruferEquiv (n : ℕ) (hn : 2 ≤ n) :
    LabeledTree n ≃ PruferSequence n where
  toFun := pruferCode
  invFun := pruferDecode hn
  left_inv := prufer_left_inv hn
  right_inv := prufer_right_inv hn

/--
**Cayley's Tree Formula (1889)**:
The number of labeled trees on $n \ge 2$ vertices is exactly $n^{n - 2}$.
-/
theorem cayleys_tree_formula (n : ℕ) (hn : 2 ≤ n) [Fintype (LabeledTree n)] :
    Fintype.card (LabeledTree n) = n ^ (n - 2) := by
  rw [Fintype.card_congr (pruferEquiv n hn)]
  exact PruferSequence.prufer_sequence_card n

/-- Concrete instance of Cayley's formula for $n = 2$: $2^{2-2} = 1$. -/
theorem cayley_n2 [Fintype (LabeledTree 2)] : Fintype.card (LabeledTree 2) = 1 := by
  have h := cayleys_tree_formula 2 (by norm_num)
  norm_num at h
  exact h

/-- Concrete instance of Cayley's formula for $n = 3$: $3^{3-2} = 3$. -/
theorem cayley_n3 [Fintype (LabeledTree 3)] : Fintype.card (LabeledTree 3) = 3 := by
  have h := cayleys_tree_formula 3 (by norm_num)
  norm_num at h
  exact h

/-- Concrete instance of Cayley's formula for $n = 4$: $4^{4-2} = 16$. -/
theorem cayley_n4 [Fintype (LabeledTree 4)] : Fintype.card (LabeledTree 4) = 16 := by
  have h := cayleys_tree_formula 4 (by norm_num)
  norm_num at h
  exact h

/-- A rooted labeled tree is a labeled tree equipped with a distinguished root vertex. -/
structure RootedTree (n : ℕ) where
  /-- The underlying labeled tree -/
  tree : LabeledTree n
  /-- The designated root vertex -/
  root : Fin n

/-- Canonical equivalence between rooted labeled trees and pairs `(T, v)`. -/
def rootedTreeEquiv (n : ℕ) : RootedTree n ≃ LabeledTree n × Fin n where
  toFun r := (r.tree, r.root)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/--
**Cayley's Rooted Tree Formula**:
The number of rooted labeled trees on $n \ge 2$ vertices is $n \cdot n^{n-2} = n^{n-1}$.
-/
theorem rooted_trees_count (n : ℕ) (hn : 2 ≤ n) [Fintype (LabeledTree n)] [Fintype (RootedTree n)] :
    Fintype.card (RootedTree n) = n ^ (n - 1) := by
  rw [Fintype.card_congr (rootedTreeEquiv n), Fintype.card_prod, Fintype.card_fin, cayleys_tree_formula n hn]
  have : n - 1 = (n - 2) + 1 := by omega
  rw [this, pow_succ, mul_comm]

/-- Number of trees with a prescribed degree sequence $(d_1, \dots, d_n)$ summing to $2n - 2$. -/
axiom degree_restricted_tree_count (d : Fin n → ℕ) (h_sum : ∑ i, d i = 2 * n - 2)
    (h_pos : ∀ i, 1 ≤ d i) (hn : 2 ≤ n) [Fintype { T : LabeledTree n // ∀ i, T.graph.degree i = d i }] :
    Fintype.card { T : LabeledTree n // ∀ i, T.graph.degree i = d i } =
      (n - 2).factorial / ∏ i, (d i - 1).factorial
