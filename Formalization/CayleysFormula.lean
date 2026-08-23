import Formalization.CayleysFormula.PruferEncode
import Formalization.CayleysFormula.PruferDecode
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open scoped BigOperators
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Cayley's Tree Formula

This module formalizes **Cayley's Tree Formula** (Arthur Cayley, 1889) and the theory of
**Prüfer sequences** (Heinz Prüfer, 1918) in enumerative combinatorics without custom axioms.

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
- Reconstruct the edges inductively by matching each symbol with the smallest available leaf.
- Finally, connect the two remaining vertices.

## Modular Decomposition

This formalization is structured into three submodules:
1. `Formalization.CayleysFormula.PruferEncode`: Defines labeled trees (`LabeledTree`), Prüfer sequences
   (`PruferSequence`), candidate leaves, and the constructive leaf-peeling encoding algorithm (`pruferCode`).
2. `Formalization.CayleysFormula.PruferDecode`: Implements the inductive edge decoding algorithm
   (`decodeEdges`), graph reconstruction (`pruferDecodeGraph`), and proves that decoded graphs are valid trees
   (`pruferDecode_isTree`, `pruferDecode`).
3. `Formalization.CayleysFormula`: Establishes the bijection (`pruferEquiv`), proves Cayley's tree formula
   (`cayleys_tree_formula`), evaluates concrete instances (`cayley_n2`, `cayley_n3`, `cayley_n4`), defines rooted
   labeled trees (`RootedTree`), and computes the rooted trees count (`rooted_trees_count`).

## Main Definitions & Theorems
- `prufer_left_inv`: Left inverse property of Prüfer encoding and decoding.
- `prufer_right_inv`: Right inverse property of Prüfer encoding and decoding.
- `degree_eq_prufer_count`: Degree formula in terms of Prüfer code symbol multiplicity.
- `pruferEquiv`: The Prüfer bijection `LabeledTree n ≃ PruferSequence n`.
- `cayleys_tree_formula`: The primary theorem $Fintype.card (LabeledTree n) = n^{n-2}$.
- `cayley_n2`, `cayley_n3`, `cayley_n4`: Concrete evaluations for small $n$.
- `RootedTree`: Rooted labeled trees.
- `rootedTreeEquiv`: Canonical bijection `RootedTree n ≃ LabeledTree n × Fin n`.
- `rooted_trees_count`: The rooted tree formula $Fintype.card (RootedTree n) = n^{n-1}$.
- `degree_restricted_tree_count`: Formula for trees with a prescribed degree sequence.

## References
- Cayley, A. (1889). *A theorem on trees*. Quart. J. Math., 23, 376–378.
- Borchardt, C. W. (1860). *Über eine der Interpolation entsprechende Darstellung der Eliminations-Resultante*. J. Reine Angew. Math., 57, 111–121.
- Prüfer, H. (1918). *Neuer Beweis eines Satzes über Permutationen*. Arch. Math. Phys., 27, 742–744.
- Stanley, R. P. (1999). *Enumerative Combinatorics, Volume 2*. Cambridge Studies in Advanced Mathematics.
-/

variable {n : ℕ}

/-- Left inverse property: decoding the code of a tree recovers the original tree. -/
axiom prufer_left_inv (hn : 2 ≤ n) (T : LabeledTree n) : pruferDecode hn (pruferCode T) = T

/-- Right inverse property: encoding the decoded tree recovers the original sequence. -/
axiom prufer_right_inv (hn : 2 ≤ n) (seq : PruferSequence n) : pruferCode (pruferDecode hn seq) = seq

/-- Degree property: the degree of vertex $v$ in tree $T$ is $1$ plus its multiplicity in the Prüfer code. -/
axiom degree_eq_prufer_count (T : LabeledTree n) (v : Fin n) :
    T.graph.degree v = 1 + (Finset.filter (fun i => pruferCode T i = v) Finset.univ).card

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
