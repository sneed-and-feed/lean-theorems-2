import Formalization.VizingsTheorem.Basic
import Formalization.VizingsTheorem.Kempe
import Formalization.VizingsTheorem.Bipartite
import Formalization.VizingsTheorem.Fan

open scoped BigOperators
open Classical

/-!
# Vizing's Theorem on Edge Colorings & König's Line Coloring Theorem

This file formalizes the theory of proper edge colorings, the chromatic index $\chi'(G)$,
König's Line Coloring Theorem for bipartite graphs, and the statement of Vizing's Theorem
for finite simple graphs.

## Modular Decomposition
- `Formalization.VizingsTheorem.Basic`: Edge colorings, partial colorings, missing colors, degrees.
- `Formalization.VizingsTheorem.Kempe`: Kempe chains, Kempe subgraphs, and alternating walks.
- `Formalization.VizingsTheorem.Bipartite`: Shift steps and König's edge coloring theorem.
- `Formalization.VizingsTheorem.Fan`: Vizing fan extensions and inductive coloring step.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

namespace SimpleGraph

namespace PartialEdgeColoring

variable {G} {k : ℕ} (c : PartialEdgeColoring G k)

omit [DecidableEq V] in
lemma color_isSome (h : c.uncoloredEdges = ∅) (e : G.edgeSet) : ∃ col, c.color e = some col := by
  cases hc : c.color e with
  | none => exact False.elim (Finset.notMem_empty e (h ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ e, hc⟩))
  | some col => exact ⟨col, rfl⟩

/-- Convert a fully defined `PartialEdgeColoring` (no uncolored edges) into a total `EdgeColoring`. -/
noncomputable def toEdgeColoring (h : c.uncoloredEdges = ∅) : EdgeColoring G k where
  color e := (c.color_isSome h e).choose
  proper e₁ e₂ hne hshare heq := by
    have h1 := (c.color_isSome h e₁).choose_spec
    have h2 := (c.color_isSome h e₂).choose_spec
    dsimp at heq
    exact c.proper hne hshare (heq ▸ h1) h2

end PartialEdgeColoring

/-- Every bipartite graph $G$ admits a proper edge coloring with $\Delta(G)$ colors. -/
theorem edgeColorable_of_bipartite (h_bip : G.Colorable 2) :
    IsEdgeColorable G G.maxDegree := by
  obtain ⟨c, hc⟩ := PartialEdgeColoring.exists_full_coloring (le_refl G.maxDegree) h_bip .empty
  exact ⟨c.toEdgeColoring hc⟩

/-- Every graph $G$ admits a proper edge coloring with $\Delta(G) + 1$ colors. -/
theorem edgeColorable_of_maxDegree_succ :
    IsEdgeColorable G (G.maxDegree + 1) := by
  obtain ⟨c, hc⟩ := PartialEdgeColoring.exists_full_coloring_vizing (Nat.lt_succ_self G.maxDegree) .empty
  exact ⟨c.toEdgeColoring hc⟩

/--
Vizing's Theorem (1964):
For any finite simple graph $G$ with maximum degree $\Delta(G)$, the edge chromatic number
(chromatic index) $\chi'(G)$ satisfies:
$$\Delta(G) \le \chi'(G) \le \Delta(G) + 1$$
-/
theorem vizings_theorem [Fintype G.edgeSet] :
    G.maxDegree ≤ chromaticIndex G ∧ chromaticIndex G ≤ G.maxDegree + 1 :=
  ⟨chromatic_index_ge_maxDegree G, csInf_le ⟨0, fun _ _ => Nat.zero_le _⟩ (edgeColorable_of_maxDegree_succ G)⟩

/-- A graph is Class 1 if its edge chromatic number achieves the maximum degree $\Delta(G)$. -/
def IsClassOne [Fintype G.edgeSet] : Prop := chromaticIndex G = G.maxDegree

/-- A graph is Class 2 if its edge chromatic number is $\Delta(G) + 1$. -/
def IsClassTwo [Fintype G.edgeSet] : Prop := chromaticIndex G = G.maxDegree + 1

/-- Vizing's Classification: Every finite simple graph is either Class 1 or Class 2. -/
theorem vizing_classification [Fintype G.edgeSet] : IsClassOne G ∨ IsClassTwo G := by
  have ⟨hle, hub⟩ := vizings_theorem G; dsimp [IsClassOne, IsClassTwo]; omega

/--
König's Line Coloring Theorem (1916):
Every bipartite graph is Class 1, i.e., $\chi'(G) = \Delta(G)$.
-/
theorem konig_edge_coloring [Fintype G.edgeSet] (h_bip : G.Colorable 2) : IsClassOne G := by
  have h_ge := chromatic_index_ge_maxDegree G
  have h_le : chromaticIndex G ≤ G.maxDegree := csInf_le ⟨0, fun _ _ => Nat.zero_le _⟩ (edgeColorable_of_bipartite G h_bip)
  dsimp [IsClassOne]; omega

end SimpleGraph
