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

/-!
# Menger's Theorem — Basic Definitions and Path Systems

This module establishes foundational definitions and lemmas for Menger's Theorem:
- `STPath`: Representation of $s\text{-}t$ simple paths.
- `innerVertices`: Interior vertices of an $s\text{-}t$ path ($V(P) \setminus \{s, t\}$).
- Path constructors: `STPath.mk1`, `STPath.mk2`, `STPath.mk3`, and `STPath.ofLe`.
- `AreInternallyDisjoint` and `IsDisjointPathSystem`: Internally vertex-disjoint paths.
- `IsVertexSeparator`: Vertex separator blocking all $s\text{-}t$ paths.
- `weak_duality`: Weak duality bound $|\mathcal{P}| \le |S|$.
- `maxDisjointPaths` and `minVertexSeparator`: Extremal quantities.
- Foundational existence and separator lemmas (`exists_innerVertex_of_not_adj`, `univ_sdiff_isVertexSeparator`, etc.).
-/

variable {V : Type*}

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

section DecEq

variable [DecidableEq V]

/-- The interior (internal) vertices of an $s\text{-}t$ path: all vertices excluding $s$ and $t$. -/
def innerVertices {G : SimpleGraph V} {s t : V} (p : STPath G s t) : Finset V :=
  p.verts.toFinset \ {s, t}

@[simp]
lemma STPath.ofLe_innerVertices {G G' : SimpleGraph V} {s t : V} (h : G ≤ G') (p : STPath G s t) :
    innerVertices (STPath.ofLe h p) = innerVertices p := rfl

@[simp]
lemma STPath.mk1_innerVertices {G : SimpleGraph V} {s t : V} (hadj : G.Adj s t) :
    innerVertices (STPath.mk1 hadj) = ∅ := by
  ext x
  simp [innerVertices]

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

lemma univ_sdiff_isVertexSeparator [Fintype V] (G : SimpleGraph V) (s t : V)
    (hne : s ≠ t) (h_not_adj : ¬ G.Adj s t) :
    IsVertexSeparator G s t (Finset.univ \ {s, t}) := by
  refine ⟨by simp, by simp, ?_⟩
  intro p
  obtain ⟨v, hv⟩ := exists_innerVertex_of_not_adj G hne h_not_adj p
  refine ⟨v, ?_, hv⟩
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, not_or]
  simp only [innerVertices, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hv
  exact ⟨hv.2.1, hv.2.2⟩

end DecEq

lemma edgeFinset_card_eq (G : SimpleGraph V) (h1 h2 : Fintype G.edgeSet) :
    (@SimpleGraph.edgeFinset V G h1).card = (@SimpleGraph.edgeFinset V G h2).card := by
  have e1 : (@SimpleGraph.edgeFinset V G h1).card = @Fintype.card G.edgeSet h1 := @Set.toFinset_card (Sym2 V) G.edgeSet h1
  have e2 : (@SimpleGraph.edgeFinset V G h2).card = @Fintype.card G.edgeSet h2 := @Set.toFinset_card (Sym2 V) G.edgeSet h2
  have e3 : @Fintype.card G.edgeSet h1 = @Fintype.card G.edgeSet h2 := @Fintype.card_congr' G.edgeSet G.edgeSet h1 h2 rfl
  exact e1.trans (e3.trans e2.symm)

end MengersTheorem
