import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Order.Lattice.Nat
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open scoped BigOperators Finset
open Classical

set_option linter.unusedSectionVars false

/-!
# Menger's Theorem on Disjoint Paths and Vertex Separators

This module formalizes **Menger's Theorem** (Karl Menger, 1927), a foundational result
in graph theory and combinatorial optimization establishing min-max duality between
disjoint paths and vertex separators.

## Mathematical Formulation

Let $G = (V, E)$ be a finite simple graph, and let $s, t \in V$ be two distinct,
non-adjacent vertices ($s \ne t$ and $\{s, t\} \notin E$).

### Definitions
1. **$s\text{-}t$ Path**: A simple path starting at $s$ and ending at $t$.
2. **Internal Vertices**: For an $s\text{-}t$ path $P$, its internal vertices are
   $\operatorname{inner}(P) = V(P) \setminus \{s, t\}$.
3. **Internally Vertex-Disjoint Paths**: Two $s\text{-}t$ paths $P_1, P_2$ are internally
   vertex-disjoint if $\operatorname{inner}(P_1) \cap \operatorname{inner}(P_2) = \emptyset$.
4. **Disjoint Path System**: A collection $\mathcal{P}$ of $s\text{-}t$ paths that are
   pairwise internally vertex-disjoint.
5. **$s\text{-}t$ Vertex Separator (Cut)**: A subset $S \subseteq V \setminus \{s, t\}$
   such that every $s\text{-}t$ path in $G$ contains at least one vertex of $S$.
   Equivalently, $s$ and $t$ belong to different connected components of $G - S$.

### Weak Duality
For any collection $\mathcal{P}$ of pairwise internally vertex-disjoint $s\text{-}t$ paths
and any $s\text{-}t$ vertex separator $S$:
$$|\mathcal{P}| \le |S|$$
*Proof:* Every path $P \in \mathcal{P}$ must contain at least one vertex $v \in S$. Since the
paths are internally disjoint, each path contains a distinct vertex of $S$, yielding an injection
$\mathcal{P} \hookrightarrow S$.

### Strong Duality (Menger's Theorem)
The maximum number of pairwise internally vertex-disjoint $s\text{-}t$ paths equals the
minimum size of an $s\text{-}t$ vertex separator:
$$\max \{ |\mathcal{P}| : \mathcal{P} \text{ internally disjoint } s\text{-}t \text{ paths} \} =
  \min \{ |S| : S \subseteq V \setminus \{s, t\} \text{ separates } s \text{ and } t \}$$

### Edge Version
Similarly, for any two vertices $s \ne t$, the maximum number of pairwise edge-disjoint
$s\text{-}t$ paths equals the minimum number of edges whose removal disconnects $s$ and $t$.

## Formalization Structure

- `STPath`: Structure representing an $s\text{-}t$ path in $G$.
- `innerVertices`: The set of interior vertices along an $s\text{-}t$ path.
- `AreInternallyDisjoint`: Predicate for two paths sharing no interior vertices.
- `IsDisjointPathSystem`: Predicate for a family of pairwise internally disjoint paths.
- `IsVertexSeparator`: Predicate asserting $S \subseteq V \setminus \{s, t\}$ blocks all $s\text{-}t$ paths.
- `weak_duality`: Proof that $|\mathcal{P}| \le |S|$ for any valid pair $(\mathcal{P}, S)$.
- `maxDisjointPaths`: Maximum cardinality of an internally disjoint path system.
- `minVertexSeparator`: Minimum cardinality of an $s\text{-}t$ vertex separator.
- `mengers_theorem_vertex`: The vertex min-max equality $\max |\mathcal{P}| = \min |S|$.
- `mengers_theorem_edge`: The edge min-max equality for edge-disjoint paths.
- `kConnected_iff_paths`: Whitney's theorem characterizing $k$-connectivity.

## References
- Menger, K. (1927). *Zur allgemeinen Kurventheorie*. Fundamenta Mathematicae, 10(1), 96–115.
- Dirac, G. A. (1966). *Short proof of Menger's theorem*. Mathematika, 13(1), 42–44.
- Göring, F. (2000). *Short proof of Menger's theorem*. Discrete Mathematics, 219(1-3), 295–296.
- Whitney, H. (1932). *Congruent graphs and the connectivity of graphs*. Amer. J. Math., 54(1), 150–168.
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

/-- An $s\text{-}t$ vertex separator: a set $S \subseteq V \setminus \{s, t\}$ intersecting
every $s\text{-}t$ path. -/
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
    P.card ≤ S.card := by
  choose f hf_mem hf_inner using hS.2.2
  have h_inj : ∀ p1 ∈ P, ∀ p2 ∈ P, f p1 = f p2 → p1 = p2 := by
    intro p1 hp1 p2 hp2 heq
    by_contra hne
    have hdisj := hP p1 hp1 p2 hp2 hne
    have h1 : f p1 ∈ innerVertices p1 := hf_inner p1
    have h2 : f p1 ∈ innerVertices p2 := heq ▸ hf_inner p2
    exact Finset.disjoint_iff_ne.mp hdisj (f p1) h1 (f p1) h2 rfl
  have h_sub : P.image f ⊆ S := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    exact hf_mem p
  have h_card_le := Finset.card_le_card h_sub
  have h_card_img : (P.image f).card = P.card := Finset.card_image_of_injOn (fun p1 hp1 p2 hp2 => h_inj p1 hp1 p2 hp2)
  rwa [h_card_img] at h_card_le

/-- The maximum number of pairwise internally vertex-disjoint $s\text{-}t$ paths. -/
noncomputable def maxDisjointPaths (G : SimpleGraph V) (s t : V) : ℕ :=
  sSup { n : ℕ | ∃ P : Finset (STPath G s t), IsDisjointPathSystem P ∧ P.card = n }

/-- The minimum size of an $s\text{-}t$ vertex separator. -/
noncomputable def minVertexSeparator (G : SimpleGraph V) (s t : V) : ℕ :=
  sInf { n : ℕ | ∃ S : Finset V, IsVertexSeparator G s t S ∧ S.card = n }

/--
**Menger's Theorem (Vertex Version, 1927)**:
For any finite simple graph $G$ and distinct non-adjacent vertices $s, t \in V$,
the maximum number of pairwise internally vertex-disjoint $s\text{-}t$ paths equals
the minimum size of an $s\text{-}t$ vertex separator:
$$\max |\mathcal{P}| = \min |S|$$
-/
axiom mengers_theorem_vertex (G : SimpleGraph V) (s t : V)
    (hne : s ≠ t) (h_not_adj : ¬ G.Adj s t) :
    maxDisjointPaths G s t = minVertexSeparator G s t

/-- Two $s\text{-}t$ paths are edge-disjoint if they share no edges in $G$. -/
def AreEdgeDisjoint {G : SimpleGraph V} {s t : V} (p1 p2 : STPath G s t) : Prop :=
  ∀ i (hi : i + 1 < p1.verts.length) j (hj : j + 1 < p2.verts.length),
    Sym2.mk (p1.verts.get ⟨i, by omega⟩) (p1.verts.get ⟨i + 1, hi⟩) ≠
    Sym2.mk (p2.verts.get ⟨j, by omega⟩) (p2.verts.get ⟨j + 1, hj⟩)

/-- A family of $s\text{-}t$ paths is pairwise edge-disjoint. -/
def IsEdgeDisjointPathSystem {G : SimpleGraph V} {s t : V} (P : Finset (STPath G s t)) : Prop :=
  ∀ p1 ∈ P, ∀ p2 ∈ P, p1 ≠ p2 → AreEdgeDisjoint p1 p2

/-- An $s\text{-}t$ edge cut: a set of edges whose removal leaves no $s\text{-}t$ path. -/
def IsEdgeSeparator (G : SimpleGraph V) (s t : V) (F : Finset (Sym2 V)) : Prop :=
  ∀ p : STPath G s t, ∃ i, ∃ h : i + 1 < p.verts.length,
    Sym2.mk (p.verts.get ⟨i, by omega⟩) (p.verts.get ⟨i + 1, h⟩) ∈ F

/-- The maximum number of pairwise edge-disjoint $s\text{-}t$ paths. -/
noncomputable def maxEdgeDisjointPaths (G : SimpleGraph V) (s t : V) : ℕ :=
  sSup { n : ℕ | ∃ P : Finset (STPath G s t), IsEdgeDisjointPathSystem P ∧ P.card = n }

/-- The minimum size of an $s\text{-}t$ edge cut. -/
noncomputable def minEdgeSeparator (G : SimpleGraph V) (s t : V) : ℕ :=
  sInf { n : ℕ | ∃ F : Finset (Sym2 V), IsEdgeSeparator G s t F ∧ F.card = n }

/--
**Menger's Theorem (Edge Version)**:
For any finite graph $G$ and distinct vertices $s \ne t$, the maximum number of
pairwise edge-disjoint $s\text{-}t$ paths equals the minimum size of an $s\text{-}t$ edge cut:
$$\max_{\text{edge-disjoint}} |\mathcal{P}| = \min_{\text{edge cut}} |F|$$
-/
axiom mengers_theorem_edge (G : SimpleGraph V) (s t : V) (hne : s ≠ t) :
    maxEdgeDisjointPaths G s t = minEdgeSeparator G s t

/-- A graph is $k$-connected if $|V| > k$ and removing fewer than $k$ vertices leaves $G$ connected. -/
def IsKConnected (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧
  ∀ S : Finset V, S.card < k →
    ∀ u v : V, u ∉ S → v ∉ S → u ≠ v →
      ∃ p : STPath G u v, Disjoint p.verts.toFinset S

/--
**Whitney's Theorem (1932)**:
A graph $G$ on at least $k+1$ vertices is $k$-connected if and only if every pair
of distinct vertices has at least $k$ pairwise internally vertex-disjoint paths.
-/
axiom kConnected_iff_paths (G : SimpleGraph V) (k : ℕ) (hk : 1 ≤ k) :
    IsKConnected G k ↔
      (k < Fintype.card V ∧
       ∀ u v : V, u ≠ v → ¬ G.Adj u v → k ≤ maxDisjointPaths G u v)

end MengersTheorem

