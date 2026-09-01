import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Order.Lattice.Nat
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Tactic.IntervalCases

open scoped Finset
open Classical

set_option linter.unusedSectionVars false

/-!
# Menger's Theorem on Disjoint Paths and Vertex Separators

This module formalizes **Menger's Theorem** (Karl Menger, 1927), a foundational result
in graph theory establishing min-max duality between disjoint paths and separators.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace MengersTheorem

/-- An $s\text{-}t$ simple path in a graph $G$, specified by its vertex list. -/
structure STPath (G : SimpleGraph V) (s t : V) where
  /-- The ordered sequence of vertices along the path -/
  verts : List V
  /-- Path starts at $s$ -/
  head_eq : verts.head? = some s
  /-- Path ends at $t$ -/
  getLast_eq : verts.getLast? = some t
  /-- Vertices along the path are distinct -/
  nodup : verts.Nodup
  /-- Consecutive vertices are adjacent in $G$ -/
  adj_consec : ∀ i (h : i + 1 < verts.length),
    G.Adj (verts.get ⟨i, by omega⟩) (verts.get ⟨i + 1, h⟩)

/-- The interior (internal) vertices of an $s\text{-}t$ path: all vertices excluding $s$ and $t$. -/
def innerVertices {G : SimpleGraph V} {s t : V} (p : STPath G s t) : Finset V :=
  p.verts.toFinset \ {s, t}

/-- Two $s\text{-}t$ paths are internally vertex-disjoint if their interior vertices are disjoint. -/
def AreInternallyDisjoint {G : SimpleGraph V} {s t : V} (p1 p2 : STPath G s t) : Prop :=
  Disjoint (innerVertices p1) (innerVertices p2)

/-- A family $\mathcal{P}$ of $s\text{-}t$ paths is pairwise internally disjoint. -/
def IsDisjointPathSystem {G : SimpleGraph V} {s t : V} (P : Finset (STPath G s t)) : Prop :=
  ∀ p1 ∈ P, ∀ p2 ∈ P, p1 ≠ p2 → AreInternallyDisjoint p1 p2

/-- An $s\text{-}t$ vertex separator: a set $S \subseteq V \setminus \{s, t\}$ intersecting\nevery $s\text{-}t$ path. -/
def IsVertexSeparator (G : SimpleGraph V) (s t : V) (S : Finset V) : Prop :=
  s ∉ S ∧ t ∉ S ∧ ∀ p : STPath G s t, ∃ v ∈ S, v ∈ innerVertices p

/--
**Weak Duality for Vertex Separators and Disjoint Paths**:
For any family $\mathcal{P}$ of pairwise internally vertex-disjoint $s\text{-}t$ paths
and any $s\text{-}t$ vertex separator $S$, the number of paths is at most the separator size:
$$|\mathcal{P}| \le |S|$$
-/
theorem weak_duality (G : SimpleGraph V) {s t : V} (P : Finset (STPath G s t)) (S : Finset V)
    (hP : IsDisjointPathSystem P) (hS : IsVertexSeparator G s t S) :
    P.card ≤ S.card := sorry

/-- The maximum number of pairwise internally vertex-disjoint $s\text{-}t$ paths. -/
noncomputable def maxDisjointPaths (G : SimpleGraph V) (s t : V) : ℕ :=
  sSup { n : ℕ | ∃ P : Finset (STPath G s t), IsDisjointPathSystem P ∧ P.card = n }

/-- The minimum size of an $s\text{-}t$ vertex separator. -/
noncomputable def minVertexSeparator (G : SimpleGraph V) (s t : V) : ℕ :=
  sInf { n : ℕ | ∃ S : Finset V, IsVertexSeparator G s t S ∧ S.card = n }

/-- Two $s\text{-}t$ paths are edge-disjoint if they share no edges in $G$. -/
def AreEdgeDisjoint {G : SimpleGraph V} {s t : V} (p1 p2 : STPath G s t) : Prop :=
  ∀ i (hi : i + 1 < p1.verts.length) j (hj : j + 1 < p2.verts.length),
    Sym2.mk (p1.verts.get ⟨i, by omega⟩) (p1.verts.get ⟨i + 1, hi⟩) ≠
    Sym2.mk (p2.verts.get ⟨j, by omega⟩) (p2.verts.get ⟨j + 1, hj⟩)

/-- A family of $s\text{-}t$ paths is pairwise edge-disjoint. -/
def IsEdgeDisjointPathSystem {G : SimpleGraph V} {s t : V} (P : Finset (STPath G s t)) : Prop :=
  ∀ p1 ∈ P, ∀ p2 ∈ P, p1 ≠ p2 → AreEdgeDisjoint p1 p2

/-- An edge cut separating $s$ and $t$ is a set of edges $F \subseteq E(G)$ such that\nevery $s\text{-}t$ path in $G$ uses at least one edge in $F$. -/
def IsEdgeSeparator (G : SimpleGraph V) (s t : V) (F : Finset (Sym2 V)) : Prop :=
  ∀ p : STPath G s t, ∃ i, ∃ hi : i + 1 < p.verts.length,
    Sym2.mk (p.verts.get ⟨i, by omega⟩) (p.verts.get ⟨i + 1, hi⟩) ∈ F

/-- The maximum number of pairwise edge-disjoint $s\text{-}t$ paths in $G$. -/
noncomputable def maxEdgeDisjointPaths (G : SimpleGraph V) (s t : V) : ℕ :=
  sSup { n : ℕ | ∃ P : Finset (STPath G s t), IsEdgeDisjointPathSystem P ∧ P.card = n }

/-- The minimum size of an $s\text{-}t$ edge separator in $G$. -/
noncomputable def minEdgeSeparator (G : SimpleGraph V) (s t : V) : ℕ :=
  sInf { n : ℕ | ∃ F : Finset (Sym2 V), IsEdgeSeparator G s t F ∧ F.card = n }

/--
Weak duality for edge-disjoint paths and edge cuts:
For any edge-disjoint path system $\mathcal{P}$ and any edge cut $F$, $|\mathcal{P}| \le |F|$.
-/
theorem weak_duality_edge (G : SimpleGraph V) {s t : V}
    (P : Finset (STPath G s t)) (F : Finset (Sym2 V))
    (hP : IsEdgeDisjointPathSystem P) (hF : IsEdgeSeparator G s t F) :
    P.card ≤ F.card := sorry

/-- A graph is $k$-connected if $|V| > k$ and removing fewer than $k$ vertices leaves $G$ connected. -/
def IsKConnected (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧
  ∀ S : Finset V, S.card < k →
    ∀ u v : V, u ∉ S → v ∉ S → u ≠ v →
      ∃ p : STPath G u v, Disjoint p.verts.toFinset S

/-- **Menger's Theorem (Vertex Version, 1927)**:
For any finite simple graph $G$ and distinct non-adjacent vertices $s, t \in V$,
the maximum number of pairwise internally vertex-disjoint $s\text{-}t$ paths equals
the minimum size of an $s\text{-}t$ vertex separator:
$$\max |\mathcal{P}| = \min |S|$$ -/
theorem menger_vertex (G : SimpleGraph V) (s t : V)
    (hne : s ≠ t) (h_not_adj : ¬ G.Adj s t) :
    maxDisjointPaths G s t = minVertexSeparator G s t := sorry

/-- **Menger's Theorem (Edge Version)**:
For any finite simple graph $G$ and distinct vertices $s \ne t$, the maximum number of
pairwise edge-disjoint $s\text{-}t$ paths equals the minimum size of an $s\text{-}t$ edge cut:
$$\max_{\text{edge-disjoint}} |\mathcal{P}| = \min_{\text{edge cut}} |F|$$ -/
theorem menger_edge (G : SimpleGraph V) (s t : V) (hne : s ≠ t) :
    maxEdgeDisjointPaths G s t = minEdgeSeparator G s t := sorry

/-- **Whitney's Connectivity Theorem (1932)**:
A graph $G$ on at least $k+1$ vertices is $k$-connected if and only if every pair
of distinct non-adjacent vertices has at least $k$ pairwise internally vertex-disjoint paths. -/
theorem menger_whitney (G : SimpleGraph V) (k : ℕ) (hk : 1 ≤ k) :
    IsKConnected G k ↔
      (k < Fintype.card V ∧
       ∀ u v : V, u ≠ v → ¬ G.Adj u v → k ≤ maxDisjointPaths G u v) := sorry
end MengersTheorem
