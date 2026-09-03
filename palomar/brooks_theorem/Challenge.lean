import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Finset SimpleGraph

/-!
# Brooks' Theorem on Graph Colorings (1941)

This module formalizes **Brooks' Theorem** (R. L. Brooks, 1941), a foundational result
in graph theory and vertex coloring.

## Mathematical Statement

Let $G = (V, E)$ be a connected simple graph with maximum degree $\Delta(G) = \Delta \ge 1$.
Then the chromatic number $\chi(G)$ of $G$ satisfies:
$$\chi(G) \le \Delta$$
**unless** $G$ is one of two exceptional families:
1. $G$ is a complete graph $K_{\Delta + 1}$ (where $\chi(K_{\Delta + 1}) = \Delta + 1$).
2. $\Delta = 2$ and $G$ is an odd cycle $C_{2k+1}$ (where $\chi(C_{2k+1}) = 3 = \Delta + 1$).

For all other connected graphs (in particular, any graph with $\Delta \ge 3$ that is not a clique),
$G$ can be properly colored with $\Delta$ colors.

## Proof Techniques
1. **Small-Graph Exact Colorability ($|V| \le \Delta + 1$):**
   Any non-complete graph with $|V| \le \Delta + 1$ is $\Delta$-colorable.
2. **Odd Cycle 2-Coloring Obstruction:**
   Odd cycles $C_{2k+1}$ are not 2-colorable.
3. **Lovász's Ordering Lemma (1975):**
   Given a vertex ordering with shared non-adjacent bases and forward neighbors,
   a greedy coloring uses at most $\Delta$ colors.

## References
* Brooks, R. L. (1941). *On colouring the nodes of a network*. Mathematical Proceedings of the Cambridge Philosophical Society, 37(2), 194–197.
* Lovász, L. (1975). *Three short proofs in graph theory*. Journal of Combinatorial Theory, Series B, 19(3), 269–271.
* Diestel, R. (2017). *Graph Theory*. 5th edition, Springer.
-/

namespace BrooksTheorem

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Maximum degree $\Delta(G)$ of a finite graph $G$. -/
def maxDegree (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.univ.sup (fun v => G.degree v)

/-- Predicate asserting that coloring `c` is a proper vertex coloring of `G`. -/
def IsProperColoring (G : SimpleGraph V) {k : ℕ} (c : V → Fin k) : Prop :=
  ∀ u v : V, G.Adj u v → c u ≠ c v

/-- Predicate asserting that graph `G` is `k`-colorable ($\chi(G) \le k$). -/
def IsKColorable (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : V → Fin k, IsProperColoring G c

/-- A graph is complete ($K_n$) if every pair of distinct vertices is adjacent. -/
def IsCompleteGraph (G : SimpleGraph V) : Prop :=
  ∀ u v : V, u ≠ v → G.Adj u v

/-- A graph is an odd cycle $C_{2k+1}$. -/
def IsOddCycle (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  Odd (Fintype.card V) ∧ (∀ v : V, G.degree v = 2) ∧ G.Preconnected

/-- **Brooks' Theorem for small graphs ($|V| \le \Delta + 1$):**
    Any graph on at most $\Delta + 1$ vertices with $\Delta \ge 1$ that is not
    a complete graph $K_{\Delta+1}$ is $\Delta$-colorable. -/
theorem brooks_theorem_of_card_le_succ (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_deg_pos : 1 ≤ maxDegree G)
    (h_card : Fintype.card V ≤ maxDegree G + 1)
    (h_not_clique : ¬ (IsCompleteGraph G ∧ Fintype.card V = maxDegree G + 1)) :
    IsKColorable G (maxDegree G) := sorry

/-- An odd cycle is not 2-colorable (requires at least 3 colors). -/
theorem odd_cycle_not_two_colorable (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_odd : IsOddCycle G) : ¬ IsKColorable G 2 := sorry

/-- **Lovász's Ordering Lemma (1975)**:
    If a graph admits a Lovász triple ordering where $v_0 \not\sim v_1$, $v_0 \sim v_n$, $v_1 \sim v_n$,
    and every intermediate vertex has a forward neighbor, then $G$ is $k$-colorable for any $k \ge \Delta(G)$ with $k \ge 1$. -/
theorem colorable_of_lovasz_ordering (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : 1 ≤ k)
    (h_deg_k : maxDegree G ≤ k)
    (ord : Fin (Fintype.card V) ≃ V)
    (h_card : 3 ≤ Fintype.card V)
    (h_not_adj_01 : ¬ G.Adj (ord ⟨0, by omega⟩) (ord ⟨1, by omega⟩))
    (h_adj_0n : G.Adj (ord ⟨0, by omega⟩) (ord ⟨Fintype.card V - 1, by omega⟩))
    (h_adj_1n : G.Adj (ord ⟨1, by omega⟩) (ord ⟨Fintype.card V - 1, by omega⟩))
    (h_fwd : ∀ (i : Fin (Fintype.card V)), 2 ≤ (i : ℕ) → (i : ℕ) < Fintype.card V - 1 →
      ∃ (j : Fin (Fintype.card V)), (i : ℕ) < (j : ℕ) ∧ G.Adj (ord i) (ord j)) :
    IsKColorable G k := sorry

end BrooksTheorem
