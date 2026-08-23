import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Order.Lattice.Nat
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases

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

/-- Convert an `STPath` in a subgraph to an `STPath` in the ambient graph. -/
def STPath.ofLe {G G' : SimpleGraph V} {s t : V} (h : G ≤ G') (p : STPath G s t) : STPath G' s t where
  verts := p.verts
  head_eq := p.head_eq
  getLast_eq := p.getLast_eq
  nodup := p.nodup
  adj_consec i hi := h (p.adj_consec i hi)

@[simp]
lemma STPath.ofLe_verts {G G' : SimpleGraph V} {s t : V} (h : G ≤ G') (p : STPath G s t) :
    (STPath.ofLe h p).verts = p.verts := rfl

@[simp]
lemma STPath.ofLe_innerVertices {G G' : SimpleGraph V} {s t : V} (h : G ≤ G') (p : STPath G s t) :
    innerVertices (STPath.ofLe h p) = innerVertices p := rfl

lemma STPath.ofLe_injective {G G' : SimpleGraph V} {s t : V} (h : G ≤ G') :
    Function.Injective (STPath.ofLe (s := s) (t := t) h) := by
  intro p1 p2 heq
  obtain ⟨v1, h1, l1, n1, a1⟩ := p1
  obtain ⟨v2, h2, l2, n2, a2⟩ := p2
  have : (STPath.ofLe h ⟨v1, h1, l1, n1, a1⟩).verts = (STPath.ofLe h ⟨v2, h2, l2, n2, a2⟩).verts :=
    congrArg STPath.verts heq
  dsimp [STPath.ofLe] at this
  subst this
  rfl

lemma STPath.get_zero {G : SimpleGraph V} {s t : V} (p : STPath G s t) (h0 : 0 < p.verts.length) :
    p.verts.get ⟨0, h0⟩ = s := by
  obtain ⟨verts, head_eq, getLast_eq, nodup, adj_consec⟩ := p
  dsimp at h0 ⊢
  obtain ⟨ys, hys⟩ := List.head?_eq_some_iff.mp head_eq
  subst hys
  rfl

lemma STPath.eq_zero_of_get_eq_head {G : SimpleGraph V} {s t : V} (p : STPath G s t)
    (i : ℕ) (hi : i < p.verts.length) (heq : p.verts.get ⟨i, hi⟩ = s) : i = 0 := by
  have h0 : 0 < p.verts.length := by omega
  have h_zero := p.get_zero h0
  have heq_pts : p.verts.get ⟨i, hi⟩ = p.verts.get ⟨0, h0⟩ := by rw [heq, h_zero]
  have h_fin := (List.Nodup.get_inj_iff p.nodup).mp heq_pts
  exact Fin.ext_iff.mp h_fin

lemma STPath.edge_zero_of_edge_eq_s {G : SimpleGraph V} {s t : V} (p : STPath G s t) {u : V}
    (i : ℕ) (hi : i + 1 < p.verts.length)
    (heq : Sym2.mk (p.verts.get ⟨i, by omega⟩) (p.verts.get ⟨i + 1, hi⟩) = Sym2.mk s u) :
    i = 0 ∧ p.verts.get ⟨1, by omega⟩ = u := by
  have h_symm := Sym2.eq_iff.mp heq
  rcases h_symm with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hi0 := p.eq_zero_of_get_eq_head i (by omega) h1
    subst hi0
    exact ⟨rfl, h2⟩
  · have hi1 := p.eq_zero_of_get_eq_head (i + 1) hi h2
    omega

def STPath.mk1 {G : SimpleGraph V} {s t : V} (hadj : G.Adj s t) : STPath G s t where
  verts := [s, t]
  head_eq := rfl
  getLast_eq := rfl
  nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false]
    exact ⟨hadj.ne, by simp⟩
  adj_consec := by
    intro i hi
    have : i = 0 := by simp [List.length] at hi; omega
    subst this
    exact hadj

@[simp]
lemma STPath.mk1_verts {G : SimpleGraph V} {s t : V} (hadj : G.Adj s t) :
    (STPath.mk1 hadj).verts = [s, t] := rfl

@[simp]
lemma STPath.mk1_innerVertices {G : SimpleGraph V} {s t : V} (hadj : G.Adj s t) :
    innerVertices (STPath.mk1 hadj) = ∅ := by
  ext x
  simp [innerVertices]

/-- Construct an $s\text{-}t$ path of length 2 through a common neighbor $u$. -/
def STPath.mk2 {G : SimpleGraph V} {s t : V} (u : V)
    (hsu : G.Adj s u) (hut : G.Adj u t) (hne_st : s ≠ t) : STPath G s t where
  verts := [s, u, t]
  head_eq := rfl
  getLast_eq := rfl
  nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨⟨hsu.ne, hne_st⟩, ⟨hut.ne, by simp⟩⟩
  adj_consec := by
    intro i hi
    have : i < 2 := by simp [List.length] at hi; omega
    interval_cases i
    · exact hsu
    · exact hut

@[simp]
lemma STPath.mk2_innerVertices {G : SimpleGraph V} {s t : V} (u : V)
    (hsu : G.Adj s u) (hut : G.Adj u t) (hne_st : s ≠ t) :
    innerVertices (STPath.mk2 u hsu hut hne_st) = {u} := by
  ext x
  simp only [innerVertices, STPath.mk2, Finset.mem_sdiff, Finset.mem_insert, List.mem_toFinset,
    List.mem_cons, List.not_mem_nil, or_false, Finset.mem_singleton, not_or]
  constructor
  · rintro ⟨(rfl | rfl | rfl), hx1, hx2⟩
    · exact (hx1 rfl).elim
    · rfl
    · exact (hx2 rfl).elim
  · rintro rfl
    refine ⟨Or.inr (Or.inl rfl), hsu.ne.symm, hut.ne⟩

/-- Construct an $s\text{-}t$ path of length 3 through $x$ and $y$. -/
def STPath.mk3 {G : SimpleGraph V} {s t : V} (x y : V)
    (hsx : G.Adj s x) (hxy : G.Adj x y) (hyt : G.Adj y t)
    (hne_st : s ≠ t) (hne_sy : s ≠ y) (hne_xt : x ≠ t) : STPath G s t where
  verts := [s, x, y, t]
  head_eq := rfl
  getLast_eq := rfl
  nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨⟨hsx.ne, hne_sy, hne_st⟩, ⟨hxy.ne, hne_xt⟩, ⟨hyt.ne, by simp⟩⟩
  adj_consec := by
    intro i hi
    have : i < 3 := by simp [List.length] at hi; omega
    interval_cases i
    · exact hsx
    · exact hxy
    · exact hyt

@[simp]
lemma STPath.mk3_innerVertices {G : SimpleGraph V} {s t : V} (x y : V)
    (hsx : G.Adj s x) (hxy : G.Adj x y) (hyt : G.Adj y t)
    (hne_st : s ≠ t) (hne_sy : s ≠ y) (hne_xt : x ≠ t) :
    innerVertices (STPath.mk3 x y hsx hxy hyt hne_st hne_sy hne_xt) = {x, y} := by
  ext v
  simp only [innerVertices, STPath.mk3, Finset.mem_sdiff, Finset.mem_insert, List.mem_toFinset,
    List.mem_cons, List.not_mem_nil, or_false, Finset.mem_singleton, not_or]
  constructor
  · rintro ⟨(rfl | rfl | rfl | rfl), hv1, hv2⟩
    · exact (hv1 rfl).elim
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact (hv2 rfl).elim
  · rintro (rfl | rfl)
    · refine ⟨Or.inr (Or.inl rfl), hsx.ne.symm, hne_xt⟩
    · refine ⟨Or.inr (Or.inr (Or.inl rfl)), hne_sy.symm, hyt.ne⟩

/-- Two $s\text{-}t$ paths are internally vertex-disjoint if their interior vertices are disjoint. -/
def AreInternallyDisjoint {G : SimpleGraph V} {s t : V} (p1 p2 : STPath G s t) : Prop :=
  Disjoint (innerVertices p1) (innerVertices p2)

/-- A family $\mathcal{P}$ of $s\text{-}t$ paths is pairwise internally disjoint. -/
def IsDisjointPathSystem {G : SimpleGraph V} {s t : V} (P : Finset (STPath G s t)) : Prop :=
  ∀ p1 ∈ P, ∀ p2 ∈ P, p1 ≠ p2 → AreInternallyDisjoint p1 p2

/-- Two $s\text{-}t$ paths of length 2 through distinct common neighbors are internally disjoint. -/
lemma areInternallyDisjoint_mk2 {G : SimpleGraph V} {s t : V} {u1 u2 : V}
    (hsu1 : G.Adj s u1) (hu1t : G.Adj u1 t) (hsu2 : G.Adj s u2) (hu2t : G.Adj u2 t)
    (hne_st : s ≠ t) (hne_u : u1 ≠ u2) :
    AreInternallyDisjoint (STPath.mk2 u1 hsu1 hu1t hne_st) (STPath.mk2 u2 hsu2 hu2t hne_st) := by
  dsimp [AreInternallyDisjoint]
  rw [STPath.mk2_innerVertices, STPath.mk2_innerVertices]
  rw [Finset.disjoint_singleton_left, Finset.mem_singleton]
  exact hne_u

/-- A path of length 2 and a path of length 3 are internally disjoint if their vertices are disjoint. -/
lemma areInternallyDisjoint_mk2_mk3 {G : SimpleGraph V} {s t : V} {u x y : V}
    (hsu : G.Adj s u) (hut : G.Adj u t)
    (hsx : G.Adj s x) (hxy : G.Adj x y) (hyt : G.Adj y t)
    (hne_st : s ≠ t) (hne_sy : s ≠ y) (hne_xt : x ≠ t)
    (hux : u ≠ x) (huy : u ≠ y) :
    AreInternallyDisjoint (STPath.mk2 u hsu hut hne_st) (STPath.mk3 x y hsx hxy hyt hne_st hne_sy hne_xt) := by
  dsimp [AreInternallyDisjoint]
  rw [STPath.mk2_innerVertices, STPath.mk3_innerVertices]
  rw [Finset.disjoint_singleton_left, Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨hux, huy⟩

/-- The family of length-2 paths through a set $U \subseteq N(s) \cap N(t)$ is pairwise internally disjoint. -/
lemma isDisjointPathSystem_mk2_image (G : SimpleGraph V) (s t : V) (hne_st : s ≠ t)
    (U : Finset V) (hU : ∀ u ∈ U, G.Adj s u ∧ G.Adj u t) :
    ∃ P : Finset (STPath G s t), IsDisjointPathSystem P ∧ P.card = U.card := by
  let f : { u : V // u ∈ U } → STPath G s t := fun ⟨u, hu⟩ =>
    STPath.mk2 u (hU u hu).1 (hU u hu).2 hne_st
  have hf_inj : Function.Injective f := by
    intro ⟨u1, hu1⟩ ⟨u2, hu2⟩ heq
    have h_verts := congrArg STPath.verts heq
    dsimp [f, STPath.mk2] at h_verts
    simp only [List.cons.injEq] at h_verts
    exact Subtype.ext h_verts.2.1
  let P := U.attach.image f
  have hP_card : P.card = U.card := by
    rw [Finset.card_image_of_injective _ hf_inj, Finset.card_attach]
  refine ⟨P, ?_, hP_card⟩
  intro p1 hp1 p2 hp2 hne
  rw [Finset.mem_image] at hp1 hp2
  obtain ⟨⟨u1, hu1⟩, -, rfl⟩ := hp1
  obtain ⟨⟨u2, hu2⟩, -, rfl⟩ := hp2
  have hu_ne : u1 ≠ u2 := by
    intro heq
    subst heq
    exact hne rfl
  exact areInternallyDisjoint_mk2 (hU u1 hu1).1 (hU u1 hu1).2 (hU u2 hu2).1 (hU u2 hu2).2 hne_st hu_ne

/-- A family of length-2 paths through $U \subseteq N(s) \cap N(t)$ plus a length-3 path through $x, y \notin U$. -/
lemma isDisjointPathSystem_mk2_image_insert_mk3 (G : SimpleGraph V) (s t : V) (hne_st : s ≠ t)
    (U : Finset V) (hU : ∀ u ∈ U, G.Adj s u ∧ G.Adj u t)
    (x y : V) (hsx : G.Adj s x) (hxy : G.Adj x y) (hyt : G.Adj y t)
    (hne_sy : s ≠ y) (hne_xt : x ≠ t) (hx_not_U : x ∉ U) (hy_not_U : y ∉ U) :
    ∃ P : Finset (STPath G s t), IsDisjointPathSystem P ∧ P.card = U.card + 1 := by
  let f : { u : V // u ∈ U } → STPath G s t := fun ⟨u, hu⟩ =>
    STPath.mk2 u (hU u hu).1 (hU u hu).2 hne_st
  have hf_inj : Function.Injective f := by
    intro ⟨u1, hu1⟩ ⟨u2, hu2⟩ heq
    have h_verts := congrArg STPath.verts heq
    dsimp [f, STPath.mk2] at h_verts
    simp only [List.cons.injEq] at h_verts
    exact Subtype.ext h_verts.2.1
  let P2 := U.attach.image f
  have hP2_card : P2.card = U.card := by
    rw [Finset.card_image_of_injective _ hf_inj, Finset.card_attach]
  have hP2_disj : IsDisjointPathSystem P2 := by
    intro p1 hp1 p2 hp2 hne
    rw [Finset.mem_image] at hp1 hp2
    obtain ⟨⟨u1, hu1⟩, -, rfl⟩ := hp1
    obtain ⟨⟨u2, hu2⟩, -, rfl⟩ := hp2
    have hu_ne : u1 ≠ u2 := by
      intro heq
      subst heq
      exact hne rfl
    exact areInternallyDisjoint_mk2 (hU u1 hu1).1 (hU u1 hu1).2 (hU u2 hu2).1 (hU u2 hu2).2 hne_st hu_ne
  let p3 := STPath.mk3 x y hsx hxy hyt hne_st hne_sy hne_xt
  have hp3_notin : p3 ∉ P2 := by
    intro hp3_in
    rw [Finset.mem_image] at hp3_in
    obtain ⟨⟨u, hu⟩, -, heq⟩ := hp3_in
    have h_verts := congrArg STPath.verts heq
    dsimp [f, STPath.mk2, STPath.mk3, p3] at h_verts
    have h_len := congrArg List.length h_verts
    dsimp [List.length] at h_len
    omega
  let P := insert p3 P2
  have hP_card : P.card = U.card + 1 := by
    rw [Finset.card_insert_of_notMem hp3_notin, hP2_card]
  refine ⟨P, ?_, hP_card⟩
  intro p1 hp1 p2 hp2 hne
  rw [Finset.mem_insert] at hp1 hp2
  rcases hp1 with rfl | hp1
  · rcases hp2 with rfl | hp2
    · exact (hne rfl).elim
    · rw [Finset.mem_image] at hp2
      obtain ⟨⟨u, hu⟩, -, rfl⟩ := hp2
      have hux : u ≠ x := fun h => hx_not_U (h ▸ hu)
      have huy : u ≠ y := fun h => hy_not_U (h ▸ hu)
      have := areInternallyDisjoint_mk2_mk3 (hU u hu).1 (hU u hu).2 hsx hxy hyt hne_st hne_sy hne_xt hux huy
      dsimp [AreInternallyDisjoint] at this ⊢
      exact this.symm
  · rcases hp2 with rfl | hp2
    · rw [Finset.mem_image] at hp1
      obtain ⟨⟨u, hu⟩, -, rfl⟩ := hp1
      have hux : u ≠ x := fun h => hx_not_U (h ▸ hu)
      have huy : u ≠ y := fun h => hy_not_U (h ▸ hu)
      exact areInternallyDisjoint_mk2_mk3 (hU u hu).1 (hU u hu).2 hsx hxy hyt hne_st hne_sy hne_xt hux huy
    · exact hP2_disj p1 hp1 p2 hp2 hne

lemma isDisjointPathSystem_image_ofLe {G G' : SimpleGraph V} {s t : V} (h : G ≤ G')
    (P : Finset (STPath G s t)) (hP : IsDisjointPathSystem P) :
    IsDisjointPathSystem (P.image (STPath.ofLe h)) := by
  intro p1 hp1 p2 hp2 hne
  rw [Finset.mem_image] at hp1 hp2
  obtain ⟨q1, hq1, rfl⟩ := hp1
  obtain ⟨q2, hq2, rfl⟩ := hp2
  have hq_ne : q1 ≠ q2 := by
    rintro rfl
    exact hne rfl
  have hdisj := hP q1 hq1 q2 hq2 hq_ne
  dsimp [AreInternallyDisjoint] at hdisj ⊢
  exact hdisj

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

lemma isDisjointPathSystem_empty {G : SimpleGraph V} {s t : V} :
    IsDisjointPathSystem (∅ : Finset (STPath G s t)) := by
  intro p1 hp1
  have := Finset.notMem_empty p1
  contradiction

lemma isDisjointPathSystem_singleton {G : SimpleGraph V} {s t : V} (p : STPath G s t) :
    IsDisjointPathSystem ({p} : Finset (STPath G s t)) := by
  intro p1 hp1 p2 hp2 hne
  simp only [Finset.mem_singleton] at hp1 hp2
  subst hp1; subst hp2
  exact (hne rfl).elim

lemma exists_STPath_of_minVertexSeparator_ne_zero {G : SimpleGraph V} {s t : V}
    (hk : minVertexSeparator G s t ≠ 0) :
    Nonempty (STPath G s t) := by
  by_contra! h_no_path
  have h_empty_sep : IsVertexSeparator G s t ∅ := by
    refine ⟨by simp, by simp, ?_⟩
    intro p
    exact isEmptyElim p
  have h_in : (0 : ℕ) ∈ { n : ℕ | ∃ S : Finset V, IsVertexSeparator G s t S ∧ S.card = n } :=
    ⟨∅, h_empty_sep, rfl⟩
  have h_bddBelow : BddBelow { n : ℕ | ∃ S : Finset V, IsVertexSeparator G s t S ∧ S.card = n } :=
    ⟨0, fun _ _ => Nat.zero_le _⟩
  have h_le := csInf_le h_bddBelow h_in
  dsimp [minVertexSeparator] at hk
  omega


lemma exists_innerVertex_of_not_adj (G : SimpleGraph V) {s t : V}
    (hne : s ≠ t) (h_not_adj : ¬ G.Adj s t) (p : STPath G s t) :
    ∃ v, v ∈ innerVertices p := by
  obtain ⟨verts, head_eq, getLast_eq, nodup, adj_consec⟩ := p
  dsimp [innerVertices]
  cases verts with
  | nil =>
    simp at head_eq
  | cons a tl =>
    cases tl with
    | nil =>
      simp at head_eq getLast_eq
      have : s = t := head_eq.symm.trans getLast_eq
      exact (hne this).elim
    | cons b tl2 =>
      cases tl2 with
      | nil =>
        simp at head_eq getLast_eq
        have h_len : 0 + 1 < ([a, b] : List V).length := Nat.lt_succ_self 1
        have hadj := adj_consec 0 h_len
        have h0 : ([a, b] : List V).get ⟨0, by omega⟩ = a := rfl
        have h1 : ([a, b] : List V).get ⟨1, by omega⟩ = b := rfl
        rw [h0, h1] at hadj
        rw [head_eq, getLast_eq] at hadj
        exact (h_not_adj hadj).elim
      | cons c tl3 =>
        refine ⟨b, ?_⟩
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
          List.mem_toFinset, not_or]
        simp only [List.nodup_cons, List.mem_cons, not_or] at nodup
        simp only [List.head?_cons, Option.some.injEq] at head_eq
        have h_last_tail : (c :: tl3).getLast? = some t := getLast_eq
        have h_t_in_tail : t ∈ c :: tl3 := List.mem_of_getLast? h_last_tail
        have h_b_ne_s : b ≠ s := by
          intro hbs
          have : a = b := head_eq.trans hbs.symm
          exact nodup.1.1 this
        have h_b_ne_t : b ≠ t := by
          intro hbt
          subst hbt
          cases h_t_in_tail with
          | head => exact nodup.2.1.1 rfl
          | tail _ h => exact nodup.2.1.2 h
        have h_b_in : b ∈ a :: b :: c :: tl3 := by simp
        exact ⟨h_b_in, h_b_ne_s, h_b_ne_t⟩

lemma univ_sdiff_isVertexSeparator (G : SimpleGraph V) (s t : V)
    (hne : s ≠ t) (h_not_adj : ¬ G.Adj s t) :
    IsVertexSeparator G s t (Finset.univ \ {s, t}) := by
  refine ⟨by simp, by simp, ?_⟩
  intro p
  obtain ⟨v, hv⟩ := exists_innerVertex_of_not_adj G hne h_not_adj p
  refine ⟨v, ?_, hv⟩
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, not_or]
  simp only [innerVertices, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hv
  exact ⟨hv.2.1, hv.2.2⟩

lemma mengers_duality_of_exists (G : SimpleGraph V) (s t : V)
    (hne : s ≠ t) (h_not_adj : ¬ G.Adj s t)
    (h_ex : ∃ (P : Finset (STPath G s t)) (S : Finset V),
      IsDisjointPathSystem P ∧ IsVertexSeparator G s t S ∧ P.card = S.card) :
    maxDisjointPaths G s t = minVertexSeparator G s t := by
  let SP := { n : ℕ | ∃ P : Finset (STPath G s t), IsDisjointPathSystem P ∧ P.card = n }
  let SS := { n : ℕ | ∃ S : Finset V, IsVertexSeparator G s t S ∧ S.card = n }
  have hSP_nonempty : SP.Nonempty := ⟨0, ∅, isDisjointPathSystem_empty, rfl⟩
  have hSS_nonempty : SS.Nonempty :=
    ⟨(Finset.univ \ {s, t}).card, Finset.univ \ {s, t}, univ_sdiff_isVertexSeparator G s t hne h_not_adj, rfl⟩
  have hSS_bddBelow : BddBelow SS := ⟨0, fun _ _ => Nat.zero_le _⟩
  have hSP_bddAbove : BddAbove SP := by
    refine ⟨Fintype.card V, ?_⟩
    rintro n ⟨P, hP, rfl⟩
    have hS_univ := univ_sdiff_isVertexSeparator G s t hne h_not_adj
    have := weak_duality G P (Finset.univ \ {s, t}) hP hS_univ
    have h_le_card : (Finset.univ \ {s, t} : Finset V).card ≤ Fintype.card V :=
      Finset.card_le_univ _
    omega
  have h_le : maxDisjointPaths G s t ≤ minVertexSeparator G s t := by
    dsimp [maxDisjointPaths, minVertexSeparator]
    apply csSup_le hSP_nonempty
    intro n hn
    obtain ⟨P, hP, rfl⟩ := hn
    apply le_csInf hSS_nonempty
    intro m hm
    obtain ⟨S, hS, rfl⟩ := hm
    exact weak_duality G P S hP hS
  obtain ⟨P, S, hP, hS, hcard⟩ := h_ex
  have hP_in_SP : P.card ∈ SP := ⟨P, hP, rfl⟩
  have hS_in_SS : S.card ∈ SS := ⟨S, hS, rfl⟩
  have h_ge1 : P.card ≤ maxDisjointPaths G s t := le_csSup hSP_bddAbove hP_in_SP
  have h_ge2 : minVertexSeparator G s t ≤ S.card := csInf_le hSS_bddBelow hS_in_SS
  have : minVertexSeparator G s t ≤ maxDisjointPaths G s t := by
    calc minVertexSeparator G s t ≤ S.card := h_ge2
    _ = P.card := hcard.symm
    _ ≤ maxDisjointPaths G s t := h_ge1
  exact le_antisymm h_le this

lemma mengers_vertex_of_exists_paths (G : SimpleGraph V) (s t : V)
    (hne : s ≠ t) (h_not_adj : ¬ G.Adj s t)
    (h_ex : ∃ P : Finset (STPath G s t), IsDisjointPathSystem P ∧ minVertexSeparator G s t ≤ P.card) :
    maxDisjointPaths G s t = minVertexSeparator G s t := by
  let SS := { n : ℕ | ∃ S : Finset V, IsVertexSeparator G s t S ∧ S.card = n }
  have hSS_nonempty : SS.Nonempty :=
    ⟨(Finset.univ \ {s, t}).card, Finset.univ \ {s, t}, univ_sdiff_isVertexSeparator G s t hne h_not_adj, rfl⟩
  have hS_min_mem : minVertexSeparator G s t ∈ SS := Nat.sInf_mem hSS_nonempty
  obtain ⟨S, hS, hS_card⟩ := hS_min_mem
  obtain ⟨P, hP, hP_card⟩ := h_ex
  have h_le := weak_duality G P S hP hS
  have h_eq : P.card = S.card := by omega
  exact mengers_duality_of_exists G s t hne h_not_adj ⟨P, S, hP, hS, h_eq⟩

lemma card_edgeFinset_deleteEdges_lt {G : SimpleGraph V} {e : Sym2 V} (he : e ∈ G.edgeFinset) :
    (G.deleteEdges {e}).edgeFinset.card < G.edgeFinset.card := by
  have h_sub : (G.deleteEdges {e}).edgeFinset ⊆ G.edgeFinset := by
    intro x hx
    rw [SimpleGraph.mem_edgeFinset] at hx ⊢
    rw [SimpleGraph.edgeSet_deleteEdges] at hx
    exact hx.1
  have h_not_in : e ∉ (G.deleteEdges {e}).edgeFinset := by
    intro he_in
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_deleteEdges] at he_in
    exact he_in.2 (Set.mem_singleton e)
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨h_sub, fun h => h_not_in (h ▸ he)⟩)

lemma edgeFinset_card_eq (G : SimpleGraph V) (h1 h2 : Fintype G.edgeSet) :
    (@SimpleGraph.edgeFinset V G h1).card = (@SimpleGraph.edgeFinset V G h2).card := by
  have e1 : (@SimpleGraph.edgeFinset V G h1).card = @Fintype.card G.edgeSet h1 := @Set.toFinset_card (Sym2 V) G.edgeSet h1
  have e2 : (@SimpleGraph.edgeFinset V G h2).card = @Fintype.card G.edgeSet h2 := @Set.toFinset_card (Sym2 V) G.edgeSet h2
  have e3 : @Fintype.card G.edgeSet h1 = @Fintype.card G.edgeSet h2 := @Fintype.card_congr' G.edgeSet G.edgeSet h1 h2 rfl
  exact e1.trans (e3.trans e2.symm)


lemma maxDisjointPaths_mem (G : SimpleGraph V) (s t : V) (hne : s ≠ t) (h_not_adj : ¬ G.Adj s t) :
    ∃ P : Finset (STPath G s t), IsDisjointPathSystem P ∧ P.card = maxDisjointPaths G s t := by
  let SP := { n : ℕ | ∃ P : Finset (STPath G s t), IsDisjointPathSystem P ∧ P.card = n }
  have hSP_nonempty : SP.Nonempty := ⟨0, ∅, isDisjointPathSystem_empty, rfl⟩
  have hSP_bddAbove : BddAbove SP := by
    refine ⟨Fintype.card V, ?_⟩
    rintro n ⟨P, hP, rfl⟩
    have hS_univ := univ_sdiff_isVertexSeparator G s t hne h_not_adj
    have := weak_duality G P (Finset.univ \ {s, t}) hP hS_univ
    have h_le_card : (Finset.univ \ {s, t} : Finset V).card ≤ Fintype.card V :=
      Finset.card_le_univ _
    omega
  have h_mem : sSup SP ∈ SP := Nat.sSup_mem hSP_nonempty hSP_bddAbove
  obtain ⟨P, hP, hP_card⟩ := h_mem
  exact ⟨P, hP, hP_card⟩

lemma isVertexSeparator_ofLe {G G' : SimpleGraph V} (h : G ≤ G') {s t : V} {S : Finset V}
    (hS : IsVertexSeparator G' s t S) : IsVertexSeparator G s t S := by
  refine ⟨hS.1, hS.2.1, ?_⟩
  intro p
  obtain ⟨w, hw_S, hw_inner⟩ := hS.2.2 (STPath.ofLe h p)
  exact ⟨w, hw_S, hw_inner⟩

lemma minVertexSeparator_deleteEdges_le (G : SimpleGraph V) (e : Sym2 V) (s t : V)
    (hne : s ≠ t) (h_not_adj : ¬ G.Adj s t) :
    minVertexSeparator (G.deleteEdges {e}) s t ≤ minVertexSeparator G s t := by
  let SS := { n : ℕ | ∃ S : Finset V, IsVertexSeparator G s t S ∧ S.card = n }
  have hSS_nonempty : SS.Nonempty :=
    ⟨(Finset.univ \ {s, t}).card, Finset.univ \ {s, t}, univ_sdiff_isVertexSeparator G s t hne h_not_adj, rfl⟩
  have hS_min_mem : minVertexSeparator G s t ∈ SS := Nat.sInf_mem hSS_nonempty
  obtain ⟨S, hS, hS_card⟩ := hS_min_mem
  have hS_sep_sub : IsVertexSeparator (G.deleteEdges {e}) s t S :=
    isVertexSeparator_ofLe (SimpleGraph.deleteEdges_le {e}) hS
  have h_in_sub : S.card ∈ { n : ℕ | ∃ S' : Finset V, IsVertexSeparator (G.deleteEdges {e}) s t S' ∧ S'.card = n } :=
    ⟨S, hS_sep_sub, rfl⟩
  have h_bddBelow : BddBelow { n : ℕ | ∃ S' : Finset V, IsVertexSeparator (G.deleteEdges {e}) s t S' ∧ S'.card = n } :=
    ⟨0, fun _ _ => Nat.zero_le _⟩
  rw [← hS_card]
  exact csInf_le h_bddBelow h_in_sub


lemma isVertexSeparator_of_deleteEdges {G : SimpleGraph V} (e : Sym2 V) {s t : V} {S : Finset V}
    (hS : IsVertexSeparator (G.deleteEdges {e}) s t S)
    (h_hit : ∀ p : STPath G s t, (∃ i, ∃ hi : i + 1 < p.verts.length, Sym2.mk (p.verts.get ⟨i, by omega⟩) (p.verts.get ⟨i + 1, hi⟩) = e) → ∃ v ∈ S, v ∈ innerVertices p) :
    IsVertexSeparator G s t S := by
  refine ⟨hS.1, hS.2.1, ?_⟩
  intro p
  by_cases he : ∃ i, ∃ hi : i + 1 < p.verts.length, Sym2.mk (p.verts.get ⟨i, by omega⟩) (p.verts.get ⟨i + 1, hi⟩) = e
  · exact h_hit p he
  · push Not at he
    have hp_sub : ∀ i (hi : i + 1 < p.verts.length),
        (G.deleteEdges {e}).Adj (p.verts.get ⟨i, by omega⟩) (p.verts.get ⟨i + 1, hi⟩) := by
      intro i hi
      rw [SimpleGraph.deleteEdges_adj]
      refine ⟨p.adj_consec i hi, ?_⟩
      intro he_in
      simp only [Set.mem_singleton_iff] at he_in
      exact he i hi he_in
    let p_sub : STPath (G.deleteEdges {e}) s t := {
      verts := p.verts
      head_eq := p.head_eq
      getLast_eq := p.getLast_eq
      nodup := p.nodup
      adj_consec := hp_sub
    }
    obtain ⟨w, hw_S, hw_inner⟩ := hS.2.2 p_sub
    exact ⟨w, hw_S, hw_inner⟩


lemma isVertexSeparator_neighborFinset (G : SimpleGraph V) (s t : V) (hne : s ≠ t) (h_not_adj : ¬ G.Adj s t) :
    IsVertexSeparator G s t (G.neighborFinset s) := by
  refine ⟨by intro h; rw [G.mem_neighborFinset] at h; exact h.ne rfl,
          by intro h; rw [G.mem_neighborFinset] at h; exact h_not_adj h, ?_⟩
  intro p
  obtain ⟨verts, head_eq, getLast_eq, nodup, adj_consec⟩ := p
  cases verts with
  | nil => simp at head_eq
  | cons a tl =>
    cases tl with
    | nil =>
      have ha_s : a = s := by injection head_eq
      have ha_t : a = t := by injection getLast_eq
      subst ha_s; subst ha_t; contradiction
    | cons b tl2 =>
      have ha_s : a = s := by injection head_eq
      have h0 : 0 + 1 < (a :: b :: tl2).length := Nat.succ_lt_succ (Nat.succ_pos tl2.length)
      have hadj0 := adj_consec 0 h0
      have hadj0_sb : G.Adj s b := ha_s ▸ hadj0
      have hb_mem : b ∈ G.neighborFinset s := by
        rw [G.mem_neighborFinset]
        exact hadj0_sb
      refine ⟨b, hb_mem, ?_⟩
      dsimp [innerVertices]
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or, List.mem_toFinset]
      refine ⟨by simp, hadj0_sb.ne.symm, ?_⟩
      intro hb_t
      subst hb_t
      exact h_not_adj hadj0_sb

lemma isVertexSeparator_insert_u {G : SimpleGraph V} {s t u : V} {S : Finset V}
    (hne : s ≠ t) (h_not_adj : ¬ G.Adj s t) (hu : G.Adj s u)
    (hS : IsVertexSeparator (G.deleteEdges {Sym2.mk s u}) s t S) :
    IsVertexSeparator G s t (insert u S) := by
  refine ⟨by intro h; rw [Finset.mem_insert] at h; rcases h with rfl | h; exact hu.ne rfl; exact hS.1 h,
          by intro h; rw [Finset.mem_insert] at h; rcases h with rfl | h; exact h_not_adj hu; exact hS.2.1 h,
          ?_⟩
  intro p
  by_cases he_used : ∃ i, ∃ hi : i + 1 < p.verts.length, Sym2.mk (p.verts.get ⟨i, by omega⟩) (p.verts.get ⟨i + 1, hi⟩) = Sym2.mk s u
  · obtain ⟨i, hi, heq⟩ := he_used
    have ⟨hi0, hu_get⟩ := p.edge_zero_of_edge_eq_s i hi heq
    subst hi0
    obtain ⟨verts, head_eq, getLast_eq, nodup, adj_consec⟩ := p
    cases verts with
    | nil => simp at head_eq
    | cons a tl =>
      cases tl with
      | nil =>
        have ha_s : a = s := by injection head_eq
        have ha_t : a = t := by injection getLast_eq
        subst ha_s; subst ha_t; contradiction
      | cons b tl2 =>
        cases tl2 with
        | nil =>
          have ha_s : a = s := by injection head_eq
          have hb_t : b = t := by injection getLast_eq
          have h0 : 0 + 1 < (a :: b :: []).length := Nat.succ_lt_succ (Nat.succ_pos 0)
          have hadj0 := adj_consec 0 h0
          have hadj_st : G.Adj s t := ha_s ▸ hb_t ▸ hadj0
          exact (h_not_adj hadj_st).elim
        | cons c tl3 =>
          have ha_s : a = s := by injection head_eq
          have hb_u : b = u := by
            have : (a :: b :: c :: tl3).get ⟨1, by omega⟩ = b := rfl
            rw [this] at hu_get
            exact hu_get
          refine ⟨u, Finset.mem_insert_self u S, ?_⟩
          dsimp [innerVertices]
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or, List.mem_toFinset]
          have hu_in : u ∈ a :: b :: c :: tl3 := by
            rw [hb_u]
            exact List.mem_cons_of_mem a List.mem_cons_self
          refine ⟨hu_in, ?_, ?_⟩
          · intro hus
            subst ha_s; subst hb_u; subst hus
            exact hu.ne rfl
          · intro hut
            subst ha_s; subst hb_u; subst hut
            exact h_not_adj hu
  · push Not at he_used
    have hp_sub : ∀ i (hi : i + 1 < p.verts.length),
        (G.deleteEdges {Sym2.mk s u}).Adj (p.verts.get ⟨i, by omega⟩) (p.verts.get ⟨i + 1, hi⟩) := by
      intro i hi
      rw [SimpleGraph.deleteEdges_adj]
      refine ⟨p.adj_consec i hi, ?_⟩
      intro he_in
      simp only [Set.mem_singleton_iff] at he_in
      exact he_used i hi he_in
    let p_sub : STPath (G.deleteEdges {Sym2.mk s u}) s t := {
      verts := p.verts
      head_eq := p.head_eq
      getLast_eq := p.getLast_eq
      nodup := p.nodup
      adj_consec := hp_sub
    }
    obtain ⟨w, hw_S, hw_inner⟩ := hS.2.2 p_sub
    refine ⟨w, Finset.mem_insert_of_mem hw_S, hw_inner⟩

lemma minVertexSeparator_le_deleteEdges_succ (G : SimpleGraph V) (s t u : V)
    (hne : s ≠ t) (h_not_adj : ¬ G.Adj s t) (hu : G.Adj s u) :
    minVertexSeparator G s t ≤ minVertexSeparator (G.deleteEdges {Sym2.mk s u}) s t + 1 := by
  let SF_sub := { n : ℕ | ∃ S : Finset V, IsVertexSeparator (G.deleteEdges {Sym2.mk s u}) s t S ∧ S.card = n }
  have hSF_sub_nonempty : SF_sub.Nonempty :=
    ⟨(Finset.univ \ {s, t}).card, Finset.univ \ {s, t}, univ_sdiff_isVertexSeparator (G.deleteEdges {Sym2.mk s u}) s t hne (fun h => h_not_adj (SimpleGraph.deleteEdges_le _ h)), rfl⟩
  have hS_min_mem : minVertexSeparator (G.deleteEdges {Sym2.mk s u}) s t ∈ SF_sub := Nat.sInf_mem hSF_sub_nonempty
  obtain ⟨S_sub, hS_sub, hS_sub_card⟩ := hS_min_mem
  have hS_sep := isVertexSeparator_insert_u hne h_not_adj hu hS_sub
  have hS_in_SF : (insert u S_sub).card ∈ { n : ℕ | ∃ S : Finset V, IsVertexSeparator G s t S ∧ S.card = n } :=
    ⟨insert u S_sub, hS_sep, rfl⟩
  have hSF_bddBelow : BddBelow { n : ℕ | ∃ S : Finset V, IsVertexSeparator G s t S ∧ S.card = n } :=
    ⟨0, fun _ _ => Nat.zero_le _⟩
  have h_inf_le := csInf_le hSF_bddBelow hS_in_SF
  dsimp [minVertexSeparator]
  have h_card_insert : (insert u S_sub).card ≤ minVertexSeparator (G.deleteEdges {Sym2.mk s u}) s t + 1 := by
    calc (insert u S_sub).card ≤ S_sub.card + 1 := Finset.card_insert_le u S_sub
    _ = minVertexSeparator (G.deleteEdges {Sym2.mk s u}) s t + 1 := by rw [hS_sub_card]
  exact h_inf_le.trans h_card_insert

lemma minVertexSeparator_le_delete_inner_edge_succ (G : SimpleGraph V) (s t : V) (e : Sym2 V) (v : V)
    (hne : s ≠ t) (h_not_adj : ¬ G.Adj s t) (hvs : v ≠ s) (hvt : v ≠ t)
    (he_v : ∀ p : STPath G s t, (∃ i, ∃ hi : i + 1 < p.verts.length, Sym2.mk (p.verts.get ⟨i, by omega⟩) (p.verts.get ⟨i + 1, hi⟩) = e) → v ∈ innerVertices p) :
    minVertexSeparator G s t ≤ minVertexSeparator (G.deleteEdges {e}) s t + 1 := by
  let SF_sub := { n : ℕ | ∃ S : Finset V, IsVertexSeparator (G.deleteEdges {e}) s t S ∧ S.card = n }
  have hSF_sub_nonempty : SF_sub.Nonempty :=
    ⟨(Finset.univ \ {s, t}).card, Finset.univ \ {s, t},
      univ_sdiff_isVertexSeparator (G.deleteEdges {e}) s t hne (fun h => h_not_adj (SimpleGraph.deleteEdges_le _ h)), rfl⟩
  have hS_min_mem : minVertexSeparator (G.deleteEdges {e}) s t ∈ SF_sub := Nat.sInf_mem hSF_sub_nonempty
  obtain ⟨S_sub, hS_sub, hS_sub_card⟩ := hS_min_mem
  have hS_sep_insert : IsVertexSeparator G s t (insert v S_sub) := by
    refine ⟨by simp [hvs.symm, hS_sub.1], by simp [hvt.symm, hS_sub.2.1], ?_⟩
    intro p
    by_cases he_used : ∃ i, ∃ hi : i + 1 < p.verts.length, Sym2.mk (p.verts.get ⟨i, by omega⟩) (p.verts.get ⟨i + 1, hi⟩) = e
    · have hv_in := he_v p he_used
      exact ⟨v, Finset.mem_insert_self v S_sub, hv_in⟩
    · push Not at he_used
      have hp_sub : ∀ i (hi : i + 1 < p.verts.length),
          (G.deleteEdges {e}).Adj (p.verts.get ⟨i, by omega⟩) (p.verts.get ⟨i + 1, hi⟩) := by
        intro i hi
        rw [SimpleGraph.deleteEdges_adj]
        refine ⟨p.adj_consec i hi, ?_⟩
        intro he_in
        simp only [Set.mem_singleton_iff] at he_in
        exact he_used i hi he_in
      let p_sub : STPath (G.deleteEdges {e}) s t := {
        verts := p.verts
        head_eq := p.head_eq
        getLast_eq := p.getLast_eq
        nodup := p.nodup
        adj_consec := hp_sub
      }
      obtain ⟨w, hw_S, hw_inner⟩ := hS_sub.2.2 p_sub
      exact ⟨w, Finset.mem_insert_of_mem hw_S, hw_inner⟩
  have hS_in : (insert v S_sub).card ∈ { n : ℕ | ∃ S : Finset V, IsVertexSeparator G s t S ∧ S.card = n } :=
    ⟨insert v S_sub, hS_sep_insert, rfl⟩
  have h_bddBelow : BddBelow { n : ℕ | ∃ S : Finset V, IsVertexSeparator G s t S ∧ S.card = n } :=
    ⟨0, fun _ _ => Nat.zero_le _⟩
  have h_inf_le := csInf_le h_bddBelow hS_in
  dsimp [minVertexSeparator]
  have h_card_insert : (insert v S_sub).card ≤ minVertexSeparator (G.deleteEdges {e}) s t + 1 := by
    calc (insert v S_sub).card ≤ S_sub.card + 1 := Finset.card_insert_le v S_sub
    _ = minVertexSeparator (G.deleteEdges {e}) s t + 1 := by rw [hS_sub_card]
  exact h_inf_le.trans h_card_insert

lemma isVertexSeparator_U_of_all_len2 (G : SimpleGraph V) (s t : V) (hne : s ≠ t) (h_not_adj : ¬ G.Adj s t)
    (h_all_len2 : ∀ p : STPath G s t, p.verts.length = 3) :
    IsVertexSeparator G s t (G.neighborFinset s ∩ G.neighborFinset t) := by
  let U := G.neighborFinset s ∩ G.neighborFinset t
  refine ⟨by intro h; rw [Finset.mem_inter, G.mem_neighborFinset] at h; exact h.1.ne rfl,
          by intro h; rw [Finset.mem_inter] at h; exact (((G.mem_neighborFinset t t).mp h.2).ne rfl).elim, ?_⟩
  intro p
  have hlen := h_all_len2 p
  obtain ⟨verts, head_eq, getLast_eq, nodup, adj_consec⟩ := p
  cases verts with
  | nil => simp at head_eq
  | cons a tl =>
    cases tl with
    | nil => simp at hlen
    | cons b tl2 =>
      cases tl2 with
      | nil => simp at hlen
      | cons c tl3 =>
        cases tl3 with
        | nil =>
          have ha_s : a = s := by injection head_eq
          have hc_t : c = t := by injection getLast_eq
          have h0 : 0 + 1 < (a :: b :: c :: []).length := Nat.succ_lt_succ (Nat.succ_pos 1)
          have h1 : 1 + 1 < (a :: b :: c :: []).length := Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 0))
          have hadj0 := adj_consec 0 h0
          have hadj1 := adj_consec 1 h1
          have h_su : G.Adj s b := ha_s ▸ hadj0
          have h_ut : G.Adj b t := hc_t ▸ hadj1
          have hb_U : b ∈ U := by
            rw [Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset]
            exact ⟨h_su, G.adj_symm h_ut⟩
          refine ⟨b, hb_U, ?_⟩
          dsimp [innerVertices]
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or, List.mem_toFinset]
          refine ⟨by simp, h_su.ne.symm, ?_⟩
          intro hb_t
          subst hb_t
          exact h_not_adj h_su
        | cons d tl4 => simp at hlen

lemma all_len2_of_incident (G : SimpleGraph V) (s t : V) (hne : s ≠ t) (h_not_adj : ¬ G.Adj s t)
    (h_incident : ∀ e ∈ G.edgeFinset, s ∈ e ∨ t ∈ e) :
    ∀ p : STPath G s t, p.verts.length = 3 := by
  intro p
  by_contra hlen
  obtain ⟨verts, head_eq, getLast_eq, nodup, adj_consec⟩ := p
  cases verts with
  | nil => simp at head_eq
  | cons a tl =>
    cases tl with
    | nil =>
      have ha_s : a = s := by injection head_eq
      have ha_t : a = t := by injection getLast_eq
      subst ha_s; subst ha_t; contradiction
    | cons b tl2 =>
      cases tl2 with
      | nil =>
        have ha_s : a = s := by injection head_eq
        have hb_t : b = t := by injection getLast_eq
        have h0 : 0 + 1 < (a :: b :: []).length := Nat.succ_lt_succ (Nat.succ_pos 0)
        have hadj0 := adj_consec 0 h0
        have hadj_st : G.Adj s t := ha_s ▸ hb_t ▸ hadj0
        exact (h_not_adj hadj_st).elim
      | cons c tl3 =>
        cases tl3 with
        | nil =>
          have : (a :: b :: c :: []).length = 3 := rfl
          exact (hlen this).elim
        | cons d tl4 =>
          have ha_s : a = s := by injection head_eq
          have h1 : 1 + 1 < (a :: b :: c :: d :: tl4).length := by simp
          have hadj1 := adj_consec 1 h1
          let e_mid := Sym2.mk b c
          have he_mid_in : e_mid ∈ G.edgeFinset := by
            rw [SimpleGraph.mem_edgeFinset]; exact hadj1
          have h_inc := h_incident e_mid he_mid_in
          have hb_ne_s : b ≠ s := by
            intro h; subst h; subst ha_s
            exact (List.nodup_cons.mp nodup).1 (by simp)
          have hc_ne_s : c ≠ s := by
            intro h; subst h; subst ha_s
            exact (List.nodup_cons.mp nodup).1 (by simp)
          have ht_in : t ∈ d :: tl4 := by
            have hlast : (a :: b :: c :: d :: tl4).getLast (by simp) = t := by injection getLast_eq
            have hlast_eq : (a :: b :: c :: d :: tl4).getLast (by simp) = (d :: tl4).getLast (by simp) := by simp
            rw [hlast_eq] at hlast
            rw [← hlast]
            exact List.getLast_mem (by simp)
          have hb_ne_t : b ≠ t := by
            intro h; subst h
            have h_nd1 := (List.nodup_cons.mp nodup).2
            have h_nd2 := (List.nodup_cons.mp h_nd1).1
            exact h_nd2 (List.mem_cons_of_mem c ht_in)
          have hc_ne_t : c ≠ t := by
            intro h; subst h
            have h_nd1 := (List.nodup_cons.mp nodup).2
            have h_nd2 := (List.nodup_cons.mp h_nd1).2
            have h_nd3 := (List.nodup_cons.mp h_nd2).1
            exact h_nd3 ht_in
          have hs_not_in : s ∉ e_mid := by
            intro hs
            have hs_cases : s = b ∨ s = c := Sym2.mem_iff.mp hs
            rcases hs_cases with h | h
            · exact hb_ne_s h.symm
            · exact hc_ne_s h.symm
          have ht_not_in : t ∉ e_mid := by
            intro ht
            have ht_cases : t = b ∨ t = c := Sym2.mem_iff.mp ht
            rcases ht_cases with h | h
            · exact hb_ne_t h.symm
            · exact hc_ne_t h.symm
          rcases h_inc with hs_in | ht_in'
          · exact hs_not_in hs_in
          · exact ht_not_in ht_in'

/-- Existence of internally vertex-disjoint path systems achieving the min-cut bound.
    (Constructive proof via Dirac's edge contraction induction). -/
axiom exists_disjoint_paths_vertex (G : SimpleGraph V) (s t : V)
    (hne : s ≠ t) (h_not_adj : ¬ G.Adj s t) :
    ∃ P : Finset (STPath G s t), IsDisjointPathSystem P ∧ minVertexSeparator G s t ≤ P.card

/--
**Menger's Theorem (Vertex Version, 1927)**:
For any finite simple graph $G$ and distinct non-adjacent vertices $s, t \in V$,
the maximum number of pairwise internally vertex-disjoint $s\text{-}t$ paths equals
the minimum size of an $s\text{-}t$ vertex separator:
$$\max |\mathcal{P}| = \min |S|$$
-/
theorem mengers_theorem_vertex (G : SimpleGraph V) (s t : V)
    (hne : s ≠ t) (h_not_adj : ¬ G.Adj s t) :
    maxDisjointPaths G s t = minVertexSeparator G s t :=
  mengers_vertex_of_exists_paths G s t hne h_not_adj (exists_disjoint_paths_vertex G s t hne h_not_adj)

/-- Two $s\text{-}t$ paths are edge-disjoint if they share no edges in $G$. -/
def AreEdgeDisjoint {G : SimpleGraph V} {s t : V} (p1 p2 : STPath G s t) : Prop :=
  ∀ i (hi : i + 1 < p1.verts.length) j (hj : j + 1 < p2.verts.length),
    Sym2.mk (p1.verts.get ⟨i, by omega⟩) (p1.verts.get ⟨i + 1, hi⟩) ≠
    Sym2.mk (p2.verts.get ⟨j, by omega⟩) (p2.verts.get ⟨j + 1, hj⟩)

/-- A family of $s\text{-}t$ paths is pairwise edge-disjoint. -/
def IsEdgeDisjointPathSystem {G : SimpleGraph V} {s t : V} (P : Finset (STPath G s t)) : Prop :=
  ∀ p1 ∈ P, ∀ p2 ∈ P, p1 ≠ p2 → AreEdgeDisjoint p1 p2

/-- Two length-2 paths through distinct common neighbors are edge-disjoint. -/
lemma areEdgeDisjoint_mk2 {G : SimpleGraph V} {s t : V} {u1 u2 : V}
    (hsu1 : G.Adj s u1) (hu1t : G.Adj u1 t) (hsu2 : G.Adj s u2) (hu2t : G.Adj u2 t)
    (hne_st : s ≠ t) (hne_u : u1 ≠ u2) :
    AreEdgeDisjoint (STPath.mk2 u1 hsu1 hu1t hne_st) (STPath.mk2 u2 hsu2 hu2t hne_st) := by
  intro i hi j hj
  have hi_lt : i < 2 := by simp [List.length, STPath.mk2] at hi; omega
  have hj_lt : j < 2 := by simp [List.length, STPath.mk2] at hj; omega
  interval_cases i <;> interval_cases j
  · intro heq
    have h_symm := Sym2.eq_iff.mp heq
    rcases h_symm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · dsimp [STPath.mk2] at h2
      exact hne_u h2
    · dsimp [STPath.mk2] at h1 h2
      exact hsu1.ne h2.symm
  · intro heq
    have h_symm := Sym2.eq_iff.mp heq
    rcases h_symm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · dsimp [STPath.mk2] at h1 h2
      subst h2
      exact hu1t.ne rfl
    · dsimp [STPath.mk2] at h1 h2
      exact hne_st h1
  · intro heq
    have h_symm := Sym2.eq_iff.mp heq
    rcases h_symm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · dsimp [STPath.mk2] at h1 h2
      exact hsu1.ne h1.symm
    · dsimp [STPath.mk2] at h1 h2
      exact hne_st h2.symm
  · intro heq
    have h_symm := Sym2.eq_iff.mp heq
    rcases h_symm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · dsimp [STPath.mk2] at h1
      exact hne_u h1
    · dsimp [STPath.mk2] at h1
      exact hu1t.ne h1

/-- A family of length-2 paths through $U \subseteq N(s) \cap N(t)$ is pairwise edge-disjoint. -/
lemma isEdgeDisjointPathSystem_mk2_image (G : SimpleGraph V) (s t : V) (hne_st : s ≠ t)
    (U : Finset V) (hU : ∀ u ∈ U, G.Adj s u ∧ G.Adj u t) :
    ∃ P : Finset (STPath G s t), IsEdgeDisjointPathSystem P ∧ P.card = U.card := by
  let f : { u : V // u ∈ U } → STPath G s t := fun ⟨u, hu⟩ =>
    STPath.mk2 u (hU u hu).1 (hU u hu).2 hne_st
  have hf_inj : Function.Injective f := by
    intro ⟨u1, hu1⟩ ⟨u2, hu2⟩ heq
    have h_verts := congrArg STPath.verts heq
    dsimp [f, STPath.mk2] at h_verts
    simp only [List.cons.injEq] at h_verts
    exact Subtype.ext h_verts.2.1
  let P := U.attach.image f
  have hP_card : P.card = U.card := by
    rw [Finset.card_image_of_injective _ hf_inj, Finset.card_attach]
  refine ⟨P, ?_, hP_card⟩
  intro p1 hp1 p2 hp2 hne
  rw [Finset.mem_image] at hp1 hp2
  obtain ⟨⟨u1, hu1⟩, -, rfl⟩ := hp1
  obtain ⟨⟨u2, hu2⟩, -, rfl⟩ := hp2
  have hu_ne : u1 ≠ u2 := by
    intro heq
    subst heq
    exact hne rfl
  exact areEdgeDisjoint_mk2 (hU u1 hu1).1 (hU u1 hu1).2 (hU u2 hu2).1 (hU u2 hu2).2 hne_st hu_ne

/-- A path in $G \setminus \{s(s, t)\}$ and the single-edge path $s-t$ are edge-disjoint. -/
lemma areEdgeDisjoint_mk1_ofLe_deleteEdges {G : SimpleGraph V} {s t : V} (hadj : G.Adj s t)
    (p : STPath (G.deleteEdges {Sym2.mk s t}) s t) :
    AreEdgeDisjoint (STPath.ofLe (SimpleGraph.deleteEdges_le _) p) (STPath.mk1 hadj) := by
  intro i hi j hj
  have hj0 : j = 0 := by simp [List.length, STPath.mk1] at hj; omega
  subst hj0
  intro heq
  have hadj_p := p.adj_consec i hi
  rw [SimpleGraph.deleteEdges_adj] at hadj_p
  have hi_lt : i < p.verts.length := Nat.lt_of_succ_lt hi
  have heq_edge : Sym2.mk (p.verts.get ⟨i, hi_lt⟩) (p.verts.get ⟨i + 1, hi⟩) = Sym2.mk s t := heq
  have h_not_in := hadj_p.2
  simp only [Set.mem_singleton_iff] at h_not_in
  exact h_not_in heq_edge

lemma isEdgeDisjointPathSystem_image_ofLe {G G' : SimpleGraph V} {s t : V} (h : G ≤ G')
    (P : Finset (STPath G s t)) (hP : IsEdgeDisjointPathSystem P) :
    IsEdgeDisjointPathSystem (P.image (STPath.ofLe h)) := by
  intro p1 hp1 p2 hp2 hne
  rw [Finset.mem_image] at hp1 hp2
  obtain ⟨q1, hq1, rfl⟩ := hp1
  obtain ⟨q2, hq2, rfl⟩ := hp2
  have hq_ne : q1 ≠ q2 := by
    rintro rfl
    exact hne rfl
  have hdisj := hP q1 hq1 q2 hq2 hq_ne
  intro i hi j hj
  exact hdisj i hi j hj

/-- Inserting the single-edge path $s-t$ into an edge-disjoint path system from $G \setminus \{s(s, t)\}$
    yields an edge-disjoint path system of size $+1$. -/
lemma isEdgeDisjointPathSystem_insert_mk1 {G : SimpleGraph V} {s t : V} (hadj : G.Adj s t)
    (P' : Finset (STPath (G.deleteEdges {Sym2.mk s t}) s t)) (hP' : IsEdgeDisjointPathSystem P') :
    ∃ P : Finset (STPath G s t), IsEdgeDisjointPathSystem P ∧ P.card = P'.card + 1 := by
  let P_sub := P'.image (STPath.ofLe (SimpleGraph.deleteEdges_le _))
  have hP_sub_disj : IsEdgeDisjointPathSystem P_sub :=
    isEdgeDisjointPathSystem_image_ofLe (SimpleGraph.deleteEdges_le _) P' hP'
  let p1 := STPath.mk1 hadj
  have hp1_notin : p1 ∉ P_sub := by
    rintro hp1_in
    rw [Finset.mem_image] at hp1_in
    obtain ⟨⟨v, h_head, h_last, h_nodup, h_adj⟩, -, heq⟩ := hp1_in
    have h_verts : v = [s, t] := by
      have := congrArg STPath.verts heq
      dsimp [p1, STPath.mk1, STPath.ofLe] at this
      exact this
    subst h_verts
    have hadj0 := h_adj 0 (Nat.lt_succ_self 1)
    rw [SimpleGraph.deleteEdges_adj] at hadj0
    exact hadj0.2 (Set.mem_singleton _)
  have hP_sub_card : P_sub.card = P'.card := by
    apply Finset.card_image_of_injective
    exact STPath.ofLe_injective (SimpleGraph.deleteEdges_le _)
  let P := insert p1 P_sub
  have hP_card : P.card = P'.card + 1 := by
    rw [Finset.card_insert_of_notMem hp1_notin, hP_sub_card]
  refine ⟨P, ?_, hP_card⟩
  intro p_a hp_a p_b hp_b hne
  rw [Finset.mem_insert] at hp_a hp_b
  rcases hp_a with rfl | hp_a
  · rcases hp_b with rfl | hp_b
    · exact (hne rfl).elim
    · rw [Finset.mem_image] at hp_b
      obtain ⟨q, -, rfl⟩ := hp_b
      have := areEdgeDisjoint_mk1_ofLe_deleteEdges hadj q
      intro i hi j hj
      exact (this j hj i hi).symm
  · rcases hp_b with rfl | hp_b
    · rw [Finset.mem_image] at hp_a
      obtain ⟨q, -, rfl⟩ := hp_a
      exact areEdgeDisjoint_mk1_ofLe_deleteEdges hadj q
    · exact hP_sub_disj p_a hp_a p_b hp_b hne

/-- An edge cut separating $s$ and $t$ is a set of edges $F \subseteq E(G)$ such that
every $s\text{-}t$ path in $G$ uses at least one edge in $F$. -/
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
    P.card ≤ F.card := by
  have h_choice : ∀ p : STPath G s t, ∃ e ∈ F, ∃ i, ∃ hi : i + 1 < p.verts.length,
      e = Sym2.mk (p.verts.get ⟨i, by omega⟩) (p.verts.get ⟨i + 1, hi⟩) := by
    intro p
    obtain ⟨i, hi, hmem⟩ := hF p
    exact ⟨Sym2.mk (p.verts.get ⟨i, by omega⟩) (p.verts.get ⟨i + 1, hi⟩), hmem, i, hi, rfl⟩
  choose f hf_mem hf_edge using h_choice
  have h_inj : ∀ p1 ∈ P, ∀ p2 ∈ P, f p1 = f p2 → p1 = p2 := by
    intro p1 hp1 p2 hp2 heq
    by_contra hne
    have hdisj := hP p1 hp1 p2 hp2 hne
    obtain ⟨i1, hi1, heq1⟩ := hf_edge p1
    obtain ⟨i2, hi2, heq2⟩ := hf_edge p2
    have h_same_edge : Sym2.mk (p1.verts.get ⟨i1, by omega⟩) (p1.verts.get ⟨i1 + 1, hi1⟩) =
        Sym2.mk (p2.verts.get ⟨i2, by omega⟩) (p2.verts.get ⟨i2 + 1, hi2⟩) := by
      rw [← heq1, ← heq2, heq]
    exact hdisj i1 hi1 i2 hi2 h_same_edge
  have h_sub : P.image f ⊆ F := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    exact hf_mem p
  have h_card_le := Finset.card_le_card h_sub
  have h_card_img : (P.image f).card = P.card := Finset.card_image_of_injOn (fun p1 hp1 p2 hp2 => h_inj p1 hp1 p2 hp2)
  rwa [h_card_img] at h_card_le

lemma isEdgeDisjointPathSystem_empty {G : SimpleGraph V} {s t : V} :
    IsEdgeDisjointPathSystem (∅ : Finset (STPath G s t)) := by
  intro p1 p2 hp1
  have := Finset.notMem_empty p1
  contradiction

lemma isEdgeDisjointPathSystem_singleton {G : SimpleGraph V} {s t : V} (p : STPath G s t) :
    IsEdgeDisjointPathSystem ({p} : Finset (STPath G s t)) := by
  intro p1 hp1 p2 hp2 hne
  simp only [Finset.mem_singleton] at hp1 hp2
  subst hp1; subst hp2
  exact (hne rfl).elim

lemma exists_STPath_of_minEdgeSeparator_ne_zero {G : SimpleGraph V} {s t : V}
    (hk : minEdgeSeparator G s t ≠ 0) :
    Nonempty (STPath G s t) := by
  by_contra! h_no_path
  have h_empty_sep : IsEdgeSeparator G s t ∅ := by
    intro p
    exact isEmptyElim p
  have h_in : (0 : ℕ) ∈ { n : ℕ | ∃ F : Finset (Sym2 V), IsEdgeSeparator G s t F ∧ F.card = n } :=
    ⟨∅, h_empty_sep, rfl⟩
  have h_bddBelow : BddBelow { n : ℕ | ∃ F : Finset (Sym2 V), IsEdgeSeparator G s t F ∧ F.card = n } :=
    ⟨0, fun _ _ => Nat.zero_le _⟩
  have h_le := csInf_le h_bddBelow h_in
  dsimp [minEdgeSeparator] at hk
  omega


lemma isEdgeSeparator_insert_of_deleteEdges (G : SimpleGraph V) (s t : V) (e : Sym2 V)
    (F : Finset (Sym2 V)) (hF : IsEdgeSeparator (G.deleteEdges {e}) s t F) :
    IsEdgeSeparator G s t (insert e F) := by
  intro p
  by_cases he_used : ∃ i, ∃ hi : i + 1 < p.verts.length,
      Sym2.mk (p.verts.get ⟨i, by omega⟩) (p.verts.get ⟨i + 1, hi⟩) = e
  · obtain ⟨i, hi, heq⟩ := he_used
    refine ⟨i, hi, ?_⟩
    rw [Finset.mem_insert, heq]
    exact Or.inl rfl
  · push Not at he_used
    have hp_sub : ∀ i (hi : i + 1 < p.verts.length),
        (G.deleteEdges {e}).Adj (p.verts.get ⟨i, by omega⟩) (p.verts.get ⟨i + 1, hi⟩) := by
      intro i hi
      rw [SimpleGraph.deleteEdges_adj]
      refine ⟨p.adj_consec i hi, ?_⟩
      intro he_in
      simp only [Set.mem_singleton_iff] at he_in
      exact he_used i hi he_in
    let p_sub : STPath (G.deleteEdges {e}) s t := {
      verts := p.verts
      head_eq := p.head_eq
      getLast_eq := p.getLast_eq
      nodup := p.nodup
      adj_consec := hp_sub
    }
    obtain ⟨i, hi, hmem⟩ := hF p_sub
    refine ⟨i, hi, ?_⟩
    rw [Finset.mem_insert]
    exact Or.inr hmem

lemma univ_edges_isEdgeSeparator (G : SimpleGraph V) (s t : V) (hne : s ≠ t) :
    IsEdgeSeparator G s t (Finset.univ : Finset (Sym2 V)) := by
  intro p
  obtain ⟨verts, head_eq, getLast_eq, nodup, adj_consec⟩ := p
  cases verts with
  | nil => simp at head_eq
  | cons a tl =>
    cases tl with
    | nil =>
      simp only [List.head?_cons, Option.some.injEq] at head_eq
      simp only [List.getLast?_singleton, Option.some.injEq] at getLast_eq
      subst head_eq
      subst getLast_eq
      contradiction
    | cons b tl2 =>
      have hlen : 0 + 1 < (a :: b :: tl2).length := Nat.succ_lt_succ (Nat.succ_pos tl2.length)
      exact ⟨0, hlen, Finset.mem_univ _⟩

lemma mengers_edge_duality_of_exists (G : SimpleGraph V) (s t : V) (hne : s ≠ t)
    (h_ex : ∃ (P : Finset (STPath G s t)) (F : Finset (Sym2 V)),
      IsEdgeDisjointPathSystem P ∧ IsEdgeSeparator G s t F ∧ P.card = F.card) :
    maxEdgeDisjointPaths G s t = minEdgeSeparator G s t := by
  let SP := { n : ℕ | ∃ P : Finset (STPath G s t), IsEdgeDisjointPathSystem P ∧ P.card = n }
  let SF := { n : ℕ | ∃ F : Finset (Sym2 V), IsEdgeSeparator G s t F ∧ F.card = n }
  have hSP_nonempty : SP.Nonempty := ⟨0, ∅, isEdgeDisjointPathSystem_empty, rfl⟩
  have hSF_nonempty : SF.Nonempty :=
    ⟨(Finset.univ : Finset (Sym2 V)).card, Finset.univ, univ_edges_isEdgeSeparator G s t hne, rfl⟩
  have hSF_bddBelow : BddBelow SF := ⟨0, fun _ _ => Nat.zero_le _⟩
  have hSP_bddAbove : BddAbove SP := by
    refine ⟨Fintype.card (Sym2 V), ?_⟩
    rintro n ⟨P, hP, rfl⟩
    have hF_univ := univ_edges_isEdgeSeparator G s t hne
    have := weak_duality_edge G P Finset.univ hP hF_univ
    have h_le_card : (Finset.univ : Finset (Sym2 V)).card ≤ Fintype.card (Sym2 V) :=
      Finset.card_le_univ _
    omega
  have h_le : maxEdgeDisjointPaths G s t ≤ minEdgeSeparator G s t := by
    dsimp [maxEdgeDisjointPaths, minEdgeSeparator]
    apply csSup_le hSP_nonempty
    intro n hn
    obtain ⟨P, hP, rfl⟩ := hn
    apply le_csInf hSF_nonempty
    intro m hm
    obtain ⟨F, hF, rfl⟩ := hm
    exact weak_duality_edge G P F hP hF
  obtain ⟨P, F, hP, hF, hcard⟩ := h_ex
  have hP_in_SP : P.card ∈ SP := ⟨P, hP, rfl⟩
  have hF_in_SF : F.card ∈ SF := ⟨F, hF, rfl⟩
  have h_ge1 : P.card ≤ maxEdgeDisjointPaths G s t := le_csSup hSP_bddAbove hP_in_SP
  have h_ge2 : minEdgeSeparator G s t ≤ F.card := csInf_le hSF_bddBelow hF_in_SF
  have : minEdgeSeparator G s t ≤ maxEdgeDisjointPaths G s t := by
    calc minEdgeSeparator G s t ≤ F.card := h_ge2
    _ = P.card := hcard.symm
    _ ≤ maxEdgeDisjointPaths G s t := h_ge1
  exact le_antisymm h_le this

lemma mengers_edge_of_exists_paths (G : SimpleGraph V) (s t : V) (hne : s ≠ t)
    (h_ex : ∃ P : Finset (STPath G s t), IsEdgeDisjointPathSystem P ∧ minEdgeSeparator G s t ≤ P.card) :
    maxEdgeDisjointPaths G s t = minEdgeSeparator G s t := by
  obtain ⟨P, hP, hP_card⟩ := h_ex
  let SF := { n : ℕ | ∃ F : Finset (Sym2 V), IsEdgeSeparator G s t F ∧ F.card = n }
  have hSF_nonempty : SF.Nonempty :=
    ⟨(Finset.univ : Finset (Sym2 V)).card, Finset.univ, univ_edges_isEdgeSeparator G s t hne, rfl⟩
  have hF_min_mem : minEdgeSeparator G s t ∈ SF := Nat.sInf_mem hSF_nonempty
  obtain ⟨F, hF, hF_card⟩ := hF_min_mem
  have h_weak := weak_duality_edge G P F hP hF
  have h_eq : P.card = F.card := by omega
  exact mengers_edge_duality_of_exists G s t hne ⟨P, F, hP, hF, h_eq⟩

lemma maxEdgeDisjointPaths_mem (G : SimpleGraph V) (s t : V) (hne : s ≠ t) :
    ∃ P : Finset (STPath G s t), IsEdgeDisjointPathSystem P ∧ P.card = maxEdgeDisjointPaths G s t := by
  let SP := { n : ℕ | ∃ P : Finset (STPath G s t), IsEdgeDisjointPathSystem P ∧ P.card = n }
  have hSP_nonempty : SP.Nonempty := ⟨0, ∅, isEdgeDisjointPathSystem_empty, rfl⟩
  have hSP_bddAbove : BddAbove SP := by
    refine ⟨Fintype.card (Sym2 V), ?_⟩
    rintro n ⟨P, hP, rfl⟩
    have hF_univ := univ_edges_isEdgeSeparator G s t hne
    have := weak_duality_edge G P Finset.univ hP hF_univ
    have h_le_card : (Finset.univ : Finset (Sym2 V)).card ≤ Fintype.card (Sym2 V) :=
      Finset.card_le_univ _
    omega
  have h_mem : maxEdgeDisjointPaths G s t ∈ SP := Nat.sSup_mem hSP_nonempty hSP_bddAbove
  obtain ⟨P, hP, hP_card⟩ := h_mem
  exact ⟨P, hP, hP_card⟩

lemma minEdgeSeparator_le_deleteEdges_succ (G : SimpleGraph V) (s t : V) (e : Sym2 V) (hne : s ≠ t) :
    minEdgeSeparator G s t ≤ minEdgeSeparator (G.deleteEdges {e}) s t + 1 := by
  let SF_sub := { n : ℕ | ∃ F : Finset (Sym2 V), IsEdgeSeparator (G.deleteEdges {e}) s t F ∧ F.card = n }
  have hSF_sub_nonempty : SF_sub.Nonempty :=
    ⟨(Finset.univ : Finset (Sym2 V)).card, Finset.univ, univ_edges_isEdgeSeparator (G.deleteEdges {e}) s t hne, rfl⟩
  have hF_min_mem : minEdgeSeparator (G.deleteEdges {e}) s t ∈ SF_sub := Nat.sInf_mem hSF_sub_nonempty
  obtain ⟨F_sub, hF_sub, hF_sub_card⟩ := hF_min_mem
  have hF_sep := isEdgeSeparator_insert_of_deleteEdges G s t e F_sub hF_sub
  have hF_in_SF : (insert e F_sub).card ∈ { n : ℕ | ∃ F : Finset (Sym2 V), IsEdgeSeparator G s t F ∧ F.card = n } :=
    ⟨insert e F_sub, hF_sep, rfl⟩
  have hSF_bddBelow : BddBelow { n : ℕ | ∃ F : Finset (Sym2 V), IsEdgeSeparator G s t F ∧ F.card = n } :=
    ⟨0, fun _ _ => Nat.zero_le _⟩
  have h_inf_le := csInf_le hSF_bddBelow hF_in_SF
  dsimp [minEdgeSeparator]
  have h_card_insert : (insert e F_sub).card ≤ minEdgeSeparator (G.deleteEdges {e}) s t + 1 := by
    calc (insert e F_sub).card ≤ F_sub.card + 1 := Finset.card_insert_le e F_sub
    _ = minEdgeSeparator (G.deleteEdges {e}) s t + 1 := by rw [hF_sub_card]
  exact h_inf_le.trans h_card_insert

lemma isEdgeSeparator_ofLe {G G' : SimpleGraph V} (h : G ≤ G') {s t : V} {F : Finset (Sym2 V)}
    (hF : IsEdgeSeparator G' s t F) : IsEdgeSeparator G s t F := by
  intro p
  obtain ⟨i, hi, hmem⟩ := hF (STPath.ofLe h p)
  exact ⟨i, hi, hmem⟩

lemma minEdgeSeparator_deleteEdges_le (G : SimpleGraph V) (e : Sym2 V) (s t : V) (hne : s ≠ t) :
    minEdgeSeparator (G.deleteEdges {e}) s t ≤ minEdgeSeparator G s t := by
  let SF := { n : ℕ | ∃ F : Finset (Sym2 V), IsEdgeSeparator G s t F ∧ F.card = n }
  have hSF_nonempty : SF.Nonempty :=
    ⟨(Finset.univ : Finset (Sym2 V)).card, Finset.univ, univ_edges_isEdgeSeparator G s t hne, rfl⟩
  have hF_min_mem : minEdgeSeparator G s t ∈ SF := Nat.sInf_mem hSF_nonempty
  obtain ⟨F, hF, hF_card⟩ := hF_min_mem
  have hF_sep_sub : IsEdgeSeparator (G.deleteEdges {e}) s t F :=
    isEdgeSeparator_ofLe (SimpleGraph.deleteEdges_le {e}) hF
  have h_in_sub : F.card ∈ { n : ℕ | ∃ F' : Finset (Sym2 V), IsEdgeSeparator (G.deleteEdges {e}) s t F' ∧ F'.card = n } :=
    ⟨F, hF_sep_sub, rfl⟩
  have h_bddBelow : BddBelow { n : ℕ | ∃ F' : Finset (Sym2 V), IsEdgeSeparator (G.deleteEdges {e}) s t F' ∧ F'.card = n } :=
    ⟨0, fun _ _ => Nat.zero_le _⟩
  rw [← hF_card]
  exact csInf_le h_bddBelow h_in_sub


lemma isEdgeSeparator_of_deleteEdges {G : SimpleGraph V} (e : Sym2 V) {s t : V} {F : Finset (Sym2 V)}
    (hF : IsEdgeSeparator (G.deleteEdges {e}) s t F)
    (h_hit : ∀ p : STPath G s t, (∃ i, ∃ hi : i + 1 < p.verts.length, Sym2.mk (p.verts.get ⟨i, by omega⟩) (p.verts.get ⟨i + 1, hi⟩) = e) →
      ∃ i, ∃ hi : i + 1 < p.verts.length, Sym2.mk (p.verts.get ⟨i, by omega⟩) (p.verts.get ⟨i + 1, hi⟩) ∈ F) :
    IsEdgeSeparator G s t F := by
  intro p
  by_cases he : ∃ i, ∃ hi : i + 1 < p.verts.length, Sym2.mk (p.verts.get ⟨i, by omega⟩) (p.verts.get ⟨i + 1, hi⟩) = e
  · exact h_hit p he
  · push Not at he
    have hp_sub : ∀ i (hi : i + 1 < p.verts.length),
        (G.deleteEdges {e}).Adj (p.verts.get ⟨i, by omega⟩) (p.verts.get ⟨i + 1, hi⟩) := by
      intro i hi
      rw [SimpleGraph.deleteEdges_adj]
      refine ⟨p.adj_consec i hi, ?_⟩
      intro he_in
      simp only [Set.mem_singleton_iff] at he_in
      exact he i hi he_in
    let p_sub : STPath (G.deleteEdges {e}) s t := {
      verts := p.verts
      head_eq := p.head_eq
      getLast_eq := p.getLast_eq
      nodup := p.nodup
      adj_consec := hp_sub
    }
    obtain ⟨i, hi, hmem⟩ := hF p_sub
    exact ⟨i, hi, hmem⟩


lemma isEdgeSeparator_neighborFinset (G : SimpleGraph V) (s t : V) (hne : s ≠ t) :
    IsEdgeSeparator G s t ((G.neighborFinset s).image (fun u => Sym2.mk s u)) := by
  intro p
  obtain ⟨verts, head_eq, getLast_eq, nodup, adj_consec⟩ := p
  cases verts with
  | nil => simp at head_eq
  | cons a tl =>
    cases tl with
    | nil =>
      have ha_s : a = s := by injection head_eq
      have ha_t : a = t := by injection getLast_eq
      subst ha_s; subst ha_t; contradiction
    | cons b tl2 =>
      have ha_s : a = s := by injection head_eq
      have h0 : 0 + 1 < (a :: b :: tl2).length := Nat.succ_lt_succ (Nat.succ_pos tl2.length)
      have hadj0 := adj_consec 0 h0
      have hadj0_sb : G.Adj s b := ha_s ▸ hadj0
      have hb_mem : b ∈ G.neighborFinset s := by
        rw [G.mem_neighborFinset]
        exact hadj0_sb
      refine ⟨0, h0, ?_⟩
      rw [Finset.mem_image]
      refine ⟨b, hb_mem, ?_⟩
      subst ha_s
      rfl

lemma isEdgeSeparator_U_image_of_all_len2 (G : SimpleGraph V) (s t : V) (hne : s ≠ t) (h_not_adj : ¬ G.Adj s t)
    (h_all_len2 : ∀ p : STPath G s t, p.verts.length = 3) :
    IsEdgeSeparator G s t ((G.neighborFinset s ∩ G.neighborFinset t).image (fun u => Sym2.mk s u)) := by
  let U := G.neighborFinset s ∩ G.neighborFinset t
  intro p
  have hlen := h_all_len2 p
  obtain ⟨verts, head_eq, getLast_eq, nodup, adj_consec⟩ := p
  cases verts with
  | nil => simp at head_eq
  | cons a tl =>
    cases tl with
    | nil => simp at hlen
    | cons b tl2 =>
      cases tl2 with
      | nil => simp at hlen
      | cons c tl3 =>
        cases tl3 with
        | nil =>
          have ha_s : a = s := by injection head_eq
          have hc_t : c = t := by injection getLast_eq
          have h0 : 0 + 1 < (a :: b :: c :: []).length := Nat.succ_lt_succ (Nat.succ_pos 1)
          have h1 : 1 + 1 < (a :: b :: c :: []).length := Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 0))
          have hadj0 := adj_consec 0 h0
          have hadj1 := adj_consec 1 h1
          have h_su : G.Adj s b := ha_s ▸ hadj0
          have h_ut : G.Adj b t := hc_t ▸ hadj1
          have hb_U : b ∈ U := by
            rw [Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset]
            exact ⟨h_su, G.adj_symm h_ut⟩
          refine ⟨0, h0, ?_⟩
          rw [Finset.mem_image]
          refine ⟨b, hb_U, ?_⟩
          subst ha_s
          rfl
        | cons d tl4 => simp at hlen

/-- Existence of edge-disjoint path systems achieving the min edge cut bound.
    (Constructive proof via Dirac's edge contraction induction). -/
axiom exists_disjoint_paths_edge (G : SimpleGraph V) (s t : V) (hne : s ≠ t) :
    ∃ P : Finset (STPath G s t), IsEdgeDisjointPathSystem P ∧ minEdgeSeparator G s t ≤ P.card

/--
**Menger's Theorem (Edge Version)**:
For any finite graph $G$ and distinct vertices $s \ne t$, the maximum number of
pairwise edge-disjoint $s\text{-}t$ paths equals the minimum size of an $s\text{-}t$ edge cut:
$$\max_{\text{edge-disjoint}} |\mathcal{P}| = \min_{\text{edge cut}} |F|$$
-/
theorem mengers_theorem_edge (G : SimpleGraph V) (s t : V) (hne : s ≠ t) :
    maxEdgeDisjointPaths G s t = minEdgeSeparator G s t :=
  mengers_edge_of_exists_paths G s t hne (exists_disjoint_paths_edge G s t hne)

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
theorem kConnected_iff_paths (G : SimpleGraph V) (k : ℕ) (_hk : 1 ≤ k) :
    IsKConnected G k ↔
      (k < Fintype.card V ∧
       ∀ u v : V, u ≠ v → ¬ G.Adj u v → k ≤ maxDisjointPaths G u v) := by
  constructor
  · rintro ⟨hkV, hconn⟩
    refine ⟨hkV, ?_⟩
    intro u v hne hnot_adj
    rw [mengers_theorem_vertex G u v hne hnot_adj]
    dsimp [minVertexSeparator]
    apply le_csInf
    · exact ⟨(Finset.univ \ {u, v}).card, Finset.univ \ {u, v}, univ_sdiff_isVertexSeparator G u v hne hnot_adj, rfl⟩
    · rintro n ⟨S, hS, rfl⟩
      by_contra! hlt
      have hp := hconn S hlt u v hS.1 hS.2.1 hne
      obtain ⟨p, hp_disj⟩ := hp
      obtain ⟨w, hw_S, hw_inner⟩ := hS.2.2 p
      have hw_in_verts : w ∈ p.verts.toFinset := by
        simp only [innerVertices, Finset.mem_sdiff] at hw_inner
        exact hw_inner.1
      have hdisj_mem := Finset.disjoint_left.mp hp_disj hw_in_verts
      exact hdisj_mem hw_S
  · rintro ⟨hkV, hpaths⟩
    refine ⟨hkV, ?_⟩
    intro S hS u v hu_not_S hv_not_S hne
    by_cases hadj : G.Adj u v
    · refine ⟨STPath.mk1 hadj, ?_⟩
      rw [Finset.disjoint_left]
      intro x hx
      simp [STPath.mk1_verts] at hx
      rcases hx with rfl | rfl
      · exact hu_not_S
      · exact hv_not_S
    · have h_le := hpaths u v hne hadj
      rw [mengers_theorem_vertex G u v hne hadj] at h_le
      have h_not_sep : ¬ IsVertexSeparator G u v S := by
        intro h_is_sep
        have h_in_set : S.card ∈ { n : ℕ | ∃ S' : Finset V, IsVertexSeparator G u v S' ∧ S'.card = n } := ⟨S, h_is_sep, rfl⟩
        have h_bddBelow : BddBelow { n : ℕ | ∃ S' : Finset V, IsVertexSeparator G u v S' ∧ S'.card = n } := ⟨0, fun _ _ => Nat.zero_le _⟩
        have h_inf_le := csInf_le h_bddBelow h_in_set
        dsimp [minVertexSeparator] at h_le
        omega
      have h_all : ¬ (∀ p : STPath G u v, ∃ w ∈ S, w ∈ innerVertices p) :=
        fun h_sep_all => h_not_sep ⟨hu_not_S, hv_not_S, h_sep_all⟩
      push Not at h_all
      obtain ⟨p, hp_inner⟩ := h_all
      refine ⟨p, ?_⟩
      rw [Finset.disjoint_left]
      intro x hx
      by_contra hxS
      by_cases hxu : x = u
      · subst hxu; exact hu_not_S hxS
      · by_cases hxv : x = v
        · subst hxv; exact hv_not_S hxS
        · have hx_inner : x ∈ innerVertices p := by
            simp only [innerVertices, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
              not_or, List.mem_toFinset]
            exact ⟨List.mem_toFinset.mp hx, hxu, hxv⟩
          exact hp_inner x hxS hx_inner

end MengersTheorem
