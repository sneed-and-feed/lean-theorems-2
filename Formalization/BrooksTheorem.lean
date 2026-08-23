import Formalization.BrooksTheorem.Basic
import Formalization.BrooksTheorem.OddCycles
import Formalization.BrooksTheorem.Greedy
import Formalization.BrooksTheorem.LovaszOrdering

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

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

## Modular Decomposition
- `Formalization.BrooksTheorem.Basic`: Maximum degree and basic vertex coloring predicates.
- `Formalization.BrooksTheorem.OddCycles`: Complete graph characterizations, small graph coloring lemmas, and odd cycle obstructions.
- `Formalization.BrooksTheorem.Greedy`: Greedy coloring bounds, ordered colorability, and Lovász's ordering lemma.
- `Formalization.BrooksTheorem.LovaszOrdering`: BFS spanning tree constructions, distance lemmas, Lovász triple orderings.

## Proof Techniques
1. **Greedy Coloring ($\chi(G) \le \Delta + 1$):**
   Ordering the vertices $v_1, \dots, v_n$ allows a greedy coloring where each vertex has at most $\Delta$
   previously colored neighbors, never exhausting $\Delta + 1$ available colors.
2. **2-Connected Reduction & Spanning DFS/BFS Trees:**
   When $G$ is 2-connected and not regular, one can find a vertex of degree $< \Delta$ and order the vertices
   towards it. When $G$ is $\Delta$-regular and 3-connected, one can find a pair of non-adjacent vertices
   $v_1, v_2$ with a common neighbor $v_n$ such that $G \setminus \{v_1, v_2\}$ is connected,
   giving $v_1$ and $v_2$ the same color and greedily coloring the rest.

## References
* Brooks, R. L. (1941). *On colouring the nodes of a network*. Mathematical Proceedings of the Cambridge Philosophical Society, 37(2), 194–197.
* Lovász, L. (1975). *Three short proofs in graph theory*. Journal of Combinatorial Theory, Series B, 19(3), 269–271.
* Diestel, R. (2017). *Graph Theory*. 5th edition, Springer.
* Freek Wiedijk. *Formalizing 100 Theorems*.
-/

namespace BrooksTheorem

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Brooks' Theorem for small graphs ($|V| \le \Delta + 1$):**
    Any graph on at most $\Delta + 1$ vertices with $\Delta \ge 1$ that is not
    a complete graph $K_{\Delta+1}$ is $\Delta$-colorable. -/
theorem brooks_theorem_of_card_le_succ (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_deg_pos : 1 ≤ maxDegree G)
    (h_card : Fintype.card V ≤ maxDegree G + 1)
    (h_not_clique : ¬ (IsCompleteGraph G ∧ Fintype.card V = maxDegree G + 1)) :
    IsKColorable G (maxDegree G) := by
  rcases lt_or_eq_of_le h_card with h_lt | h_eq
  · have : Fintype.card V ≤ maxDegree G := by omega
    exact isKColorable_of_card_le G (maxDegree G) this
  · have h_not_comp : ¬ IsCompleteGraph G := by
      intro h_comp
      exact h_not_clique ⟨h_comp, h_eq⟩
    exact isKColorable_of_card_eq_succ_not_complete G h_deg_pos h_eq h_not_comp

/-- **Brooks' Theorem (1941):**
    If $G$ is a connected simple graph with maximum degree $\Delta \ge 1$,
    and $G$ is neither a complete graph $K_{\Delta+1}$ nor an odd cycle,
    then $G$ is $\Delta$-colorable ($\chi(G) \le \Delta$). -/
theorem brooks_theorem (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_conn : G.Preconnected)
    (h_deg_pos : 1 ≤ maxDegree G)
    (h_not_clique : ¬ (IsCompleteGraph G ∧ Fintype.card V = maxDegree G + 1))
    (h_not_odd_cycle : ¬ (maxDegree G = 2 ∧ IsOddCycle G)) :
    IsKColorable G (maxDegree G) := by
  rcases le_or_gt (Fintype.card V) (maxDegree G + 1) with h_le | h_gt
  · exact brooks_theorem_of_card_le_succ G h_deg_pos h_le h_not_clique
  · have h_not_comp : ¬ IsCompleteGraph G := by
      intro h_comp
      have h_nonempty : Nonempty V := by
        have : 0 < Fintype.card V := by omega
        exact Fintype.card_pos_iff.mp this
      obtain ⟨v0⟩ := h_nonempty
      have h_adj : G.neighborFinset v0 = (Finset.univ.erase v0) := by
        ext w
        simp only [G.mem_neighborFinset, Finset.mem_erase, Finset.mem_univ, and_true]
        exact ⟨fun h => (G.ne_of_adj h).symm, fun h => h_comp v0 w h.symm⟩
      have h_deg_v0 : G.degree v0 ≤ maxDegree G := degree_le_maxDegree G v0
      have h1 : G.degree v0 = Fintype.card V - 1 := by
        have hd : G.degree v0 = (G.neighborFinset v0).card := (G.card_neighborFinset_eq_degree v0).symm
        rw [hd, h_adj, Finset.card_erase_of_mem (Finset.mem_univ v0), Finset.card_univ]
      omega
    have h_card3 : 3 ≤ Fintype.card V := by omega
    obtain ⟨ord, h01, h0n, h1n, hfwd⟩ :=
      exists_lovasz_ordering G h_conn h_deg_pos h_not_comp h_not_odd_cycle h_gt
    exact colorable_of_lovasz_ordering G h_deg_pos (le_refl _) ord h_card3 h01 h0n h1n hfwd

end BrooksTheorem
