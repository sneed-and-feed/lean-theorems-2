import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators
open Classical

set_option linter.unusedSectionVars false

/-!
# Kőnig–Egerváry Duality Theorem

This module formalizes the **Kőnig–Egerváry Theorem** (Dénes Kőnig, 1931; Jenő Egerváry, 1931),
a cornerstone of combinatorial optimization and structural graph theory establishing strong
min-max duality between matchings and vertex covers in bipartite graphs.

## Mathematical Framework

Let $G = (V, E)$ be a finite simple undirected graph.

### Matchings and Vertex Covers
- A **matching** $M \subseteq E$ is a set of pairwise vertex-disjoint edges:
  $$\forall e_1, e_2 \in M, e_1 \ne e_2 \implies e_1 \cap e_2 = \emptyset$$
- A **vertex cover** $C \subseteq V$ is a set of vertices hitting every edge:
  $$\forall \{u, v\} \in E, u \in C \lor v \in C$$

### Invariants
- The **matching number** $\nu(G)$ is the maximum cardinality of a matching:
  $$\nu(G) = \max \{ |M| : M \subseteq E \text{ is a matching} \}$$
- The **vertex cover number** $\tau(G)$ is the minimum cardinality of a vertex cover:
  $$\tau(G) = \min \{ |C| : C \subseteq V \text{ is a vertex cover} \}$$

### Weak Duality
For *any* graph $G$, every matching $M$ and every vertex cover $C$ satisfy $|M| \le |C|$.
Indeed, each vertex in $C$ can cover at most one edge from the vertex-disjoint family $M$.
Consequently:
$$\nu(G) \le \tau(G)$$

### Strong Duality (Kőnig–Egerváry Theorem)
When $G$ is **bipartite** ($2$-colorable), weak duality becomes an exact equality:
$$\nu(G) = \tau(G)$$

### Connections to Linear Programming & Gallai Identities
- **Total Unimodularity**: The vertex-edge incidence matrix of any bipartite graph is totally unimodular,
  so the LP relaxation of matching/vertex cover has integral extreme points.
- **Gallai's Identities (1959)**:
  - $\alpha(G) + \tau(G) = |V|$ (Independence number + Vertex cover number)
  - $\nu(G) + \rho(G) = |V|$ (Matching number + Edge cover number, for graphs without isolated vertices)

## Main Definitions & Theorems
- `EdgesShareEndpoint`: Relation that two edges share an endpoint.
- `IsMatching`: Predicate for an edge set forming a valid matching.
- `IsVertexCover`: Predicate for a vertex set covering all edges.
- `matchingNumber`: Maximum cardinality $\nu(G)$ of a matching in $G$.
- `vertexCoverNumber`: Minimum cardinality $\tau(G)$ of a vertex cover in $G$.
- `matching_card_le_vertexCover_card`: Elementary bound $|M| \le |C|$ for any matching $M$ and cover $C$.
- `weak_duality`: The general inequality $\nu(G) \le \tau(G)$.
- `konig_duality`: The Kőnig–Egerváry theorem $\nu(G) = \tau(G)$ for $2$-colorable graphs.
- `gallai_independence_vertex_cover`: Gallai's identity $\alpha(G) + \tau(G) = |V|$.

## References
- Kőnig, D. (1931). *Gráfok és mátrixok*. Matematikai és Fizikai Lapok, 38, 116–119.
- Egerváry, J. (1931). *Matrixok kombinatorius tulajdonságairól*. Matematikai és Fizikai Lapok, 38, 16–28.
- Gallai, T. (1959). *Über extreme Punkt- und Kantenmengen*. Ann. Univ. Sci. Budapest, Eötvös Sect. Math., 2, 133–138.
- Schrijver, A. (2003). *Combinatorial Optimization: Polyhedra and Efficiency*. Springer.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace SimpleGraph

/-- Two edges in $G$ share a common endpoint vertex. -/
def EdgesShareEndpoint (e₁ e₂ : Sym2 V) : Prop :=
  ∃ v : V, v ∈ e₁ ∧ v ∈ e₂

/-- A set of edges $M \subseteq \operatorname{Sym2}(V)$ is a matching in $G$ if all edges belong to $G$
and no two distinct edges share a vertex. -/
def IsMatching (G : SimpleGraph V) (M : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧
  (∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → ¬ EdgesShareEndpoint e₁ e₂)

/-- A set of vertices $C \subseteq V$ is a vertex cover of $G$ if every edge has at least
one endpoint in $C$. -/
def IsVertexCover (G : SimpleGraph V) (C : Finset V) : Prop :=
  ∀ u v : V, G.Adj u v → u ∈ C ∨ v ∈ C

/-- The empty edge set is always a valid matching. -/
theorem isMatching_empty (G : SimpleGraph V) : IsMatching G ∅ := by
  constructor
  · intro e he
    simp at he
  · intro e₁ he₁
    simp at he₁

/-- The full vertex set is always a valid vertex cover. -/
theorem isVertexCover_univ (G : SimpleGraph V) : IsVertexCover G Finset.univ := by
  intro u v _
  left
  exact Finset.mem_univ u

/-- The matching number $\nu(G)$: maximum size of a matching in $G$. -/
noncomputable def matchingNumber (G : SimpleGraph V) : ℕ :=
  sSup { k : ℕ | ∃ M : Finset (Sym2 V), IsMatching G M ∧ M.card = k }

/-- The vertex cover number $\tau(G)$: minimum size of a vertex cover in $G$. -/
noncomputable def vertexCoverNumber (G : SimpleGraph V) : ℕ :=
  sInf { k : ℕ | ∃ C : Finset V, IsVertexCover G C ∧ C.card = k }

/-- An independent set in $G$ is a set of pairwise non-adjacent vertices. -/
def IsIndependentSet (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v

/-- The empty vertex set is always an independent set. -/
theorem isIndependentSet_empty (G : SimpleGraph V) : IsIndependentSet G ∅ := by
  intro u hu
  simp at hu

/-- The independence number $\alpha(G)$: maximum size of an independent set in $G$. -/
noncomputable def independenceNumber (G : SimpleGraph V) : ℕ :=
  sSup { k : ℕ | ∃ S : Finset V, IsIndependentSet G S ∧ S.card = k }

/-- An independent set corresponds bijectively to the complement of a vertex cover. -/
theorem isIndependentSet_iff_isVertexCover_compl (G : SimpleGraph V) (S : Finset V) :
    IsIndependentSet G S ↔ IsVertexCover G (Finset.univ \ S) := by
  constructor
  · intro hS u v hadj
    by_contra h
    have h1 : ¬ (u ∈ Finset.univ \ S) := fun hu => h (Or.inl hu)
    have h2 : ¬ (v ∈ Finset.univ \ S) := fun hv => h (Or.inr hv)
    have hu : u ∈ S := by
      by_contra hu'
      have : u ∈ Finset.univ \ S := by simp [hu']
      exact h1 this
    have hv : v ∈ S := by
      by_contra hv'
      have : v ∈ Finset.univ \ S := by simp [hv']
      exact h2 this
    exact hS u hu v hv hadj
  · intro hC u hu v hv hadj
    have h := hC u v hadj
    cases h with
    | inl hu_cov => simp [hu] at hu_cov
    | inr hv_cov => simp [hv] at hv_cov

/--
**Weak Duality for Matchings and Vertex Covers**:
Any matching $M$ and any vertex cover $C$ satisfy $|M| \le |C|$, since each vertex in $C$
can cover at most one edge of the vertex-disjoint family $M$.
-/
theorem matching_card_le_vertexCover_card (G : SimpleGraph V) {M : Finset (Sym2 V)} {C : Finset V}
    (hM : IsMatching G M) (hC : IsVertexCover G C) :
    M.card ≤ C.card := by
  have h_choice : ∀ e ∈ M, ∃ v ∈ C, v ∈ e := by
    intro e he
    have he_edge := hM.1 e he
    induction e using Sym2.inductionOn with
    | hf u v =>
      have hadj : G.Adj u v := he_edge
      cases hC u v hadj with
      | inl hu => exact ⟨u, hu, Sym2.mem_mk_left u v⟩
      | inr hv => exact ⟨v, hv, Sym2.mem_mk_right u v⟩
  choose f hfC hfe using h_choice
  have h_inj : ∀ (e₁ : Sym2 V) (he₁ : e₁ ∈ M) (e₂ : Sym2 V) (he₂ : e₂ ∈ M), f e₁ he₁ = f e₂ he₂ → e₁ = e₂ := by
    intro e₁ he₁ e₂ he₂ heq
    by_contra hne
    have hshare : EdgesShareEndpoint e₁ e₂ := ⟨f e₁ he₁, hfe e₁ he₁, heq ▸ hfe e₂ he₂⟩
    exact hM.2 e₁ he₁ e₂ he₂ hne hshare
  have h_sub : (M.attach.image (fun ⟨e, he⟩ => f e he)) ⊆ C := by
    intro v hv
    simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hv
    obtain ⟨e, he, rfl⟩ := hv
    exact hfC e he
  have h_card_eq : (M.attach.image (fun ⟨e, he⟩ => f e he)).card = M.card := by
    rw [Finset.card_image_of_injective]
    · simp
    · intro ⟨e₁, he₁⟩ ⟨e₂, he₂⟩ heq
      simp only [Subtype.mk.injEq]
      exact h_inj e₁ he₁ e₂ he₂ heq
  rw [← h_card_eq]
  exact Finset.card_le_card h_sub

/--
**Weak Duality Theorem**:
For any finite simple graph $G$, the matching number is bounded by the vertex cover number:
$$\nu(G) \le \tau(G)$$
-/
theorem weak_duality (G : SimpleGraph V) :
    matchingNumber G ≤ vertexCoverNumber G := by
  let SM := { k : ℕ | ∃ M : Finset (Sym2 V), IsMatching G M ∧ M.card = k }
  let SC := { k : ℕ | ∃ C : Finset V, IsVertexCover G C ∧ C.card = k }
  have hSM_nonempty : SM.Nonempty := ⟨0, ∅, isMatching_empty G, rfl⟩
  have hSC_nonempty : SC.Nonempty := ⟨Fintype.card V, Finset.univ, isVertexCover_univ G, Finset.card_univ⟩
  have h_le : ∀ k ∈ SM, ∀ l ∈ SC, k ≤ l := by
    rintro k ⟨M, hM, rfl⟩ l ⟨C, hC, rfl⟩
    exact matching_card_le_vertexCover_card G hM hC
  have h_sup_le : ∀ l ∈ SC, sSup SM ≤ l := by
    intro l hl
    exact csSup_le hSM_nonempty (fun k hk => h_le k hk l hl)
  exact le_csInf hSC_nonempty h_sup_le

/--
**Kőnig–Egerváry Theorem (1931)**:
In any bipartite ($2$-colorable) graph $G$, the maximum size of a matching equals the minimum
size of a vertex cover (strong min-max duality):
$$\nu(G) = \tau(G)$$
-/
axiom konig_duality (G : SimpleGraph V) (h_bip : G.Colorable 2) :
    matchingNumber G = vertexCoverNumber G

/--
**Gallai's Identity for Vertex Covers and Independent Sets (1959)**:
For any finite graph $G$, the independence number and vertex cover number sum to $|V|$:
$$\alpha(G) + \tau(G) = |V|$$
-/
theorem gallai_independence_vertex_cover (G : SimpleGraph V) :
    independenceNumber G + vertexCoverNumber G = Fintype.card V := by
  let SI := { k : ℕ | ∃ S : Finset V, IsIndependentSet G S ∧ S.card = k }
  let SC := { k : ℕ | ∃ C : Finset V, IsVertexCover G C ∧ C.card = k }
  have hSI_nonempty : SI.Nonempty := ⟨0, ∅, isIndependentSet_empty G, rfl⟩
  have hSC_nonempty : SC.Nonempty := ⟨Fintype.card V, Finset.univ, isVertexCover_univ G, Finset.card_univ⟩
  have hSI_bdd : BddAbove SI := by
    refine ⟨Fintype.card V, ?_⟩
    rintro a ⟨S, _, rfl⟩
    exact Finset.card_le_univ S
  have hSC_bddBelow : BddBelow SC := ⟨0, fun _ _ => Nat.zero_le _⟩
  have hC_mem : vertexCoverNumber G ∈ SC := Nat.sInf_mem hSC_nonempty
  obtain ⟨C_opt, hC_opt_cov, hC_opt_card⟩ := hC_mem
  have hS_opt_ind : IsIndependentSet G (Finset.univ \ C_opt) := by
    rw [isIndependentSet_iff_isVertexCover_compl]
    have : Finset.univ \ (Finset.univ \ C_opt) = C_opt := by ext x; simp
    rw [this]
    exact hC_opt_cov
  have hS_opt_card : (Finset.univ \ C_opt).card = Fintype.card V - vertexCoverNumber G := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hC_opt_card]
  have h_compl_in_SI : (Fintype.card V - vertexCoverNumber G) ∈ SI := by
    refine ⟨Finset.univ \ C_opt, hS_opt_ind, hS_opt_card⟩
  have h_le1 : Fintype.card V - vertexCoverNumber G ≤ independenceNumber G :=
    le_csSup hSI_bdd h_compl_in_SI
  have h_le2 : ∀ k ∈ SI, k ≤ Fintype.card V - vertexCoverNumber G := by
    rintro k ⟨S, hS_ind, rfl⟩
    have hC_cov : IsVertexCover G (Finset.univ \ S) := (isIndependentSet_iff_isVertexCover_compl G S).mp hS_ind
    have hC_card : (Finset.univ \ S).card = Fintype.card V - S.card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
    have h_in_SC : (Fintype.card V - S.card) ∈ SC := ⟨Finset.univ \ S, hC_cov, hC_card⟩
    have h_tau_le : vertexCoverNumber G ≤ Fintype.card V - S.card :=
      csInf_le hSC_bddBelow h_in_SC
    have hS_le_V : S.card ≤ Fintype.card V := Finset.card_le_univ S
    omega
  have h_indep_le : independenceNumber G ≤ Fintype.card V - vertexCoverNumber G :=
    csSup_le hSI_nonempty h_le2
  have h_eq : independenceNumber G = Fintype.card V - vertexCoverNumber G :=
    le_antisymm h_indep_le h_le1
  have h_tau_le_V : vertexCoverNumber G ≤ Fintype.card V := by
    have h_univ_in_SC : Fintype.card V ∈ SC := ⟨Finset.univ, isVertexCover_univ G, Finset.card_univ⟩
    exact csInf_le hSC_bddBelow h_univ_in_SC
  omega

/--
**Kőnig's Min-Max Formula for Independent Sets in Bipartite Graphs**:
In a bipartite graph, the independence number satisfies $\alpha(G) = |V| - \nu(G)$.
-/
theorem konig_independence_matching (G : SimpleGraph V) (h_bip : G.Colorable 2) :
    independenceNumber G + matchingNumber G = Fintype.card V := by
  rw [konig_duality G h_bip]
  exact gallai_independence_vertex_cover G

end SimpleGraph

