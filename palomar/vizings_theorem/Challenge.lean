import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic

open scoped BigOperators
open Classical

/-!
# Vizing's Theorem on Edge Colorings & König's Line Coloring Theorem

This module formalizes the theory of proper edge colorings, the chromatic index $\chi'(G)$,
König's Line Coloring Theorem for bipartite graphs, and the statement of Vizing's Theorem
for finite simple graphs.

## References
- Vizing, V. G. (1964). *On an estimate of the chromatic class of a p-graph*. Diskret. Analiz., 3, 25–30.
- König, D. (1916). *Über Graphen und ihre Anwendung auf Determinantentheorie und Mengenlehre*. Mathematische Annalen, 77(4), 453–465.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

namespace SimpleGraph

/-- Two undirected edges in $G$ share a common endpoint vertex. -/
def ShareVertex (e₁ e₂ : G.edgeSet) : Prop :=
  ∃ v : V, v ∈ (e₁ : Sym2 V) ∧ v ∈ (e₂ : Sym2 V)

/-- A proper edge coloring of $G$ with color set $\alpha$ assigns colors to edges
such that any two distinct incident edges receive different colors. -/
def IsProperEdgeColoring {α : Type*} (c : G.edgeSet → α) : Prop :=
  ∀ ⦃e₁ e₂ : G.edgeSet⦄, e₁ ≠ e₂ → ShareVertex G e₁ e₂ → c e₁ ≠ c e₂

/-- The type of proper edge colorings of $G$ using $k$ colors. -/
structure EdgeColoring (k : ℕ) where
  color : G.edgeSet → Fin k
  proper : IsProperEdgeColoring G color

/-- A graph is $k$-edge-colorable if it admits a proper $k$-edge-coloring. -/
def IsEdgeColorable (k : ℕ) : Prop := Nonempty (EdgeColoring G k)

/-- The chromatic index (edge chromatic number) $\chi'(G)$ is the minimum number of colors
needed to properly color the edges of $G$. -/
noncomputable def chromaticIndex : ℕ := sInf {k : ℕ | IsEdgeColorable G k}

/-- Every bipartite graph $G$ admits a proper edge coloring with $\Delta(G)$ colors. -/
theorem edgeColorable_of_bipartite (h_bip : G.Colorable 2) :
    IsEdgeColorable G G.maxDegree := sorry

/-- Every graph $G$ admits a proper edge coloring with $\Delta(G) + 1$ colors. -/
theorem edgeColorable_of_maxDegree_succ :
    IsEdgeColorable G (G.maxDegree + 1) := sorry

/--
Vizing's Theorem (1964):
For any finite simple graph $G$ with maximum degree $\Delta(G)$, the edge chromatic number
(chromatic index) $\chi'(G)$ satisfies:
$$\Delta(G) \le \chi'(G) \le \Delta(G) + 1$$
-/
theorem vizings_theorem [Fintype G.edgeSet] :
    G.maxDegree ≤ chromaticIndex G ∧ chromaticIndex G ≤ G.maxDegree + 1 := sorry

/-- A graph is Class 1 if its edge chromatic number achieves the maximum degree $\Delta(G)$. -/
def IsClassOne [Fintype G.edgeSet] : Prop := chromaticIndex G = G.maxDegree

/-- A graph is Class 2 if its edge chromatic number is $\Delta(G) + 1$. -/
def IsClassTwo [Fintype G.edgeSet] : Prop := chromaticIndex G = G.maxDegree + 1

/-- Vizing's Classification: Every finite simple graph is either Class 1 or Class 2. -/
theorem vizing_classification [Fintype G.edgeSet] : IsClassOne G ∨ IsClassTwo G := sorry

/--
König's Line Coloring Theorem (1916):
Every bipartite graph is Class 1, i.e., $\chi'(G) = \Delta(G)$.
-/
theorem konig_edge_coloring [Fintype G.edgeSet] (h_bip : G.Colorable 2) : IsClassOne G := sorry

end SimpleGraph
