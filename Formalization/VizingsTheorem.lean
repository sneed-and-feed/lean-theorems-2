import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-!
# Vizing's Theorem on Edge Colorings

This file formalizes the theory of proper edge colorings, the chromatic index $\chi'(G)$,
and the statement of Vizing's Theorem for finite simple graphs.

## Main Definitions
- `ShareVertex`: The relation that two undirected edges share a common endpoint.
- `IsProperEdgeColoring`: Predicate asserting that adjacent edges receive distinct colors.
- `EdgeColoring`: Structure of a proper $k$-edge-coloring of $G$.
- `ChromaticIndex`: The minimum number of colors needed to properly color the edges of $G$.
- `IsClassOne`: Predicate for Class 1 graphs ($\chi'(G) = \Delta(G)$).
- `IsClassTwo`: Predicate for Class 2 graphs ($\chi'(G) = \Delta(G) + 1$).

## Main Results
- `chromatic_index_ge_maxDegree`: The trivial lower bound $\chi'(G) \ge \Delta(G)$.
- `vizings_theorem`: Vizing's Theorem $\Delta(G) \le \chi'(G) \le \Delta(G) + 1$.
- `vizing_classification`: Classification into Class 1 or Class 2.
- `konig_edge_coloring`: König's line coloring theorem (bipartite graphs are Class 1).

## References
- Vizing, V. G. (1964). *On an estimate of the chromatic class of a p-graph*. Diskret. Analiz., 3, 25–30.
- König, D. (1916). *Über Graphen und ihre Anwendung auf Determinantentheorie und Mengenlehre*. Mathematische Annalen, 77(4), 453–465.
- Diestel, R. (2017). *Graph Theory*. Graduate Texts in Mathematics, 173.
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
def IsEdgeColorable (k : ℕ) : Prop :=
  Nonempty (EdgeColoring G k)

/-- The chromatic index (edge chromatic number) $\chi'(G)$ is the minimum number of colors
needed to properly color the edges of $G$. -/
noncomputable def chromaticIndex : ℕ :=
  sInf {k : ℕ | IsEdgeColorable G k}

theorem edgeColorable_card_edgeSet [Fintype G.edgeSet] :
    IsEdgeColorable G (Fintype.card G.edgeSet) := by
  refine ⟨⟨Fintype.equivFin G.edgeSet, ?_⟩⟩
  intro e1 e2 hne _ heq
  exact hne ((Fintype.equivFin G.edgeSet).injective heq)

theorem degree_le_of_edgeColoring {k : ℕ} (c : EdgeColoring G k) (v : V) :
    G.degree v ≤ k := by
  let f : (G.incidenceSet v) → G.edgeSet := fun e => ⟨e.val, e.property.1⟩
  have hf_inj : Function.Injective f := by
    intro e1 e2 h
    have : (f e1).val = (f e2).val := congr_arg Subtype.val h
    exact Subtype.ext this
  let g : (G.incidenceSet v) → Fin k := c.color ∘ f
  have hg_inj : Function.Injective g := by
    intro e1 e2 hg
    dsimp [g] at hg
    by_contra hne
    have hf_ne : f e1 ≠ f e2 := fun h => hne (hf_inj h)
    have hshare : ShareVertex G (f e1) (f e2) := by
      refine ⟨v, e1.property.2, e2.property.2⟩
    exact c.proper hf_ne hshare hg
  have h_card : Fintype.card (G.incidenceSet v) ≤ Fintype.card (Fin k) :=
    Fintype.card_le_of_injective g hg_inj
  rw [SimpleGraph.card_incidenceSet_eq_degree, Fintype.card_fin] at h_card
  exact h_card

theorem maxDegree_le_of_edgeColorable {k : ℕ} (h : IsEdgeColorable G k) :
    G.maxDegree ≤ k := by
  obtain ⟨c⟩ := h
  dsimp [SimpleGraph.maxDegree]
  rw [WithBot.unbotD_le_iff (fun _ => Nat.zero_le k)]
  rw [Finset.max_le_iff]
  intro a ha
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp ha
  exact WithBot.coe_le_coe.mpr (degree_le_of_edgeColoring G c v)

/-- Every vertex of degree $d$ has $d$ incident edges that pairwise share a vertex,
providing the trivial lower bound $\chi'(G) \ge \Delta(G)$. -/
theorem chromatic_index_ge_maxDegree [Fintype G.edgeSet] :
    G.maxDegree ≤ chromaticIndex G := by
  dsimp [chromaticIndex]
  have h_ne : {k : ℕ | IsEdgeColorable G k}.Nonempty := ⟨Fintype.card G.edgeSet, edgeColorable_card_edgeSet G⟩
  apply le_csInf h_ne
  intro k hk
  exact maxDegree_le_of_edgeColorable G hk

/--
Vizing's Theorem (1964):
For any finite simple graph $G$ with maximum degree $\Delta(G)$, the edge chromatic number
(chromatic index) $\chi'(G)$ satisfies:
$$\Delta(G) \le \chi'(G) \le \Delta(G) + 1$$
-/
axiom vizings_theorem [Fintype G.edgeSet] :
    G.maxDegree ≤ chromaticIndex G ∧ chromaticIndex G ≤ G.maxDegree + 1

/-- A graph is Class 1 if its edge chromatic number achieves the maximum degree $\Delta(G)$. -/
def IsClassOne [Fintype G.edgeSet] : Prop :=
  chromaticIndex G = G.maxDegree

/-- A graph is Class 2 if its edge chromatic number is $\Delta(G) + 1$. -/
def IsClassTwo [Fintype G.edgeSet] : Prop :=
  chromaticIndex G = G.maxDegree + 1

/-- Vizing's Classification: Every finite simple graph is either Class 1 or Class 2. -/
theorem vizing_classification [Fintype G.edgeSet] :
    IsClassOne G ∨ IsClassTwo G := by
  have ⟨hle, hub⟩ := vizings_theorem G
  dsimp [IsClassOne, IsClassTwo]
  omega

/--
König's Line Coloring Theorem (1916):
Every bipartite graph is Class 1, i.e., $\chi'(G) = \Delta(G)$.
-/
axiom konig_edge_coloring [Fintype G.edgeSet] (h_bip : G.Colorable 2) :
    IsClassOne G

end SimpleGraph

