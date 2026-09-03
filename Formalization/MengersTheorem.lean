import Formalization.MengersTheorem.Basic
import Formalization.MengersTheorem.VertexMenger
import Formalization.MengersTheorem.EdgeMenger
import Formalization.MengersTheorem.Whitney

open scoped Finset
open Classical

/-!
# Menger's Theorem on Disjoint Paths and Vertex Separators

This module formalizes **Menger's Theorem** (Karl Menger, 1927), a foundational result
in graph theory establishing min-max duality between disjoint paths and separators.

## Mathematical Overview

Let $G = (V, E)$ be a finite simple graph, and let $s, t \in V$ be two distinct vertices.

### 1. Vertex Version (Karl Menger, 1927)
For non-adjacent vertices $s \ne t$, the maximum number of pairwise internally
vertex-disjoint $s\text{-}t$ paths equals the minimum size of an $s\text{-}t$ vertex separator:
$$\max \{ |\mathcal{P}| : \mathcal{P} \text{ internally disjoint } s\text{-}t \text{ paths} \} =
  \min \{ |S| : S \subseteq V \setminus \{s, t\} \text{ separates } s \text{ and } t \}$$

### 2. Edge Version
For any distinct vertices $s \ne t$, the maximum number of pairwise edge-disjoint
$s\text{-}t$ paths equals the minimum size of an $s\text{-}t$ edge cut:
$$\max \{ |\mathcal{P}| : \mathcal{P} \text{ edge-disjoint } s\text{-}t \text{ paths} \} =
  \min \{ |F| : F \subseteq E(G) \text{ separates } s \text{ and } t \}$$

### 3. Whitney's Connectivity Theorem (Hassler Whitney, 1932)
A graph $G$ on at least $k+1$ vertices is $k$-connected if and only if every pair
of distinct non-adjacent vertices has at least $k$ pairwise internally vertex-disjoint paths.

## Modular Decomposition
- `Formalization.MengersTheorem.Basic`: Foundational structures (`STPath`, `innerVertices`),
  disjoint path systems, vertex separators, and weak duality ($|\mathcal{P}| \le |S|$).
- `Formalization.MengersTheorem.VertexMenger`: Reductions under edge deletions and Dirac's
  induction yielding `mengers_theorem_vertex`.
- `Formalization.MengersTheorem.EdgeMenger`: Edge-disjoint path systems, edge cuts,
  weak duality for edges, and `mengers_theorem_edge`.
- `Formalization.MengersTheorem.Whitney`: Characterization of $k$-vertex-connected graphs
  via Menger's duality (`kConnected_iff_paths`).

## References
- Menger, K. (1927). *Zur allgemeinen Kurventheorie*. Fundamenta Mathematicae, 10(1), 96–115.
- Dirac, G. A. (1966). *Short proof of Menger's theorem*. Mathematika, 13(1), 42–44.
- Göring, F. (2000). *Short proof of Menger's theorem*. Discrete Mathematics, 219(1-3), 295–296.
- Whitney, H. (1932). *Congruent graphs and the connectivity of graphs*. Amer. J. Math., 54(1), 150–168.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace MengersTheorem

/-!
### Master Theorem Entrypoints
The theorems below provide the primary public interface for Menger's duality and its corollaries.
-/

/-- **Menger's Theorem (Vertex Version, 1927)**:
For any finite simple graph $G$ and distinct non-adjacent vertices $s, t \in V$,
the maximum number of pairwise internally vertex-disjoint $s\text{-}t$ paths equals
the minimum size of an $s\text{-}t$ vertex separator:
$$\max |\mathcal{P}| = \min |S|$$ -/
theorem menger_vertex (G : SimpleGraph V) (s t : V)
    (hne : s ≠ t) (h_not_adj : ¬ G.Adj s t) :
    maxDisjointPaths G s t = minVertexSeparator G s t :=
  mengers_theorem_vertex G s t hne h_not_adj

/-- **Menger's Theorem (Edge Version)**:
For any finite simple graph $G$ and distinct vertices $s \ne t$, the maximum number of
pairwise edge-disjoint $s\text{-}t$ paths equals the minimum size of an $s\text{-}t$ edge cut:
$$\max_{\text{edge-disjoint}} |\mathcal{P}| = \min_{\text{edge cut}} |F|$$ -/
theorem menger_edge (G : SimpleGraph V) (s t : V) (hne : s ≠ t) :
    maxEdgeDisjointPaths G s t = minEdgeSeparator G s t :=
  mengers_theorem_edge G s t hne

/-- **Whitney's Connectivity Theorem (1932)**:
A graph $G$ on at least $k+1$ vertices is $k$-connected if and only if every pair
of distinct non-adjacent vertices has at least $k$ pairwise internally vertex-disjoint paths. -/
theorem menger_whitney (G : SimpleGraph V) (k : ℕ) (hk : 1 ≤ k) :
    IsKConnected G k ↔
      (k < Fintype.card V ∧
       ∀ u v : V, u ≠ v → ¬ G.Adj u v → k ≤ maxDisjointPaths G u v) :=
  kConnected_iff_paths G k hk

end MengersTheorem
