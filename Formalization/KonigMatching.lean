import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
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
- `exists_max_defect`: Existence of a maximum deficiency subset for Hall's defect theorem.
- `konig_duality_le`: Reverse inequality $\tau(G) \le \nu(G)$ in bipartite graphs.
- `konig_duality`: The Kőnig–Egerváry theorem $\nu(G) = \tau(G)$ for $2$-colorable graphs.
- `gallai_independence_vertex_cover`: Gallai's identity $\alpha(G) + \tau(G) = |V|$.
- `konig_independence_matching`: Kőnig's formula $\alpha(G) + \nu(G) = |V|$.

## References
- Kőnig, D. (1931). *Gráfok és mátrixok*. Matematikai és Fizikai Lapok, 38, 116–119.
- Egerváry, J. (1931). *Matrixok kombinatorius tulajdonságairól*. Matematikai és Fizikai Lapok, 38, 16–28.
- Gallai, T. (1959). *Über extreme Punkt- und Kantenmengen*. Ann. Univ. Sci. Budapest, Eötvös Sect. Math., 2, 133–138.
- Schrijver, A. (2003). *Combinatorial Optimization: Polyhedra and Efficiency*. Springer.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace SimpleGraph

lemma fin2_cases (y : Fin 2) : y = 0 ∨ y = 1 := by
  revert y; decide

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
  · intro e he; simp at he
  · intro e₁ he₁; simp at he₁

/-- The full vertex set is always a valid vertex cover. -/
theorem isVertexCover_univ (G : SimpleGraph V) : IsVertexCover G Finset.univ := by
  intro u v _; left; exact Finset.mem_univ u

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
  intro u hu; simp at hu

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
Existence of a maximal deficiency subset $S_0 \subseteq A$ for the defect form of Hall's condition.
-/
theorem exists_max_defect (G : SimpleGraph V) (A : Finset V) :
    ∃ (S₀ : Finset V) (d : ℕ), S₀ ⊆ A ∧
      (S₀.biUnion (fun a => G.neighborFinset a)).card ≤ S₀.card ∧
      d = S₀.card - (S₀.biUnion (fun a => G.neighborFinset a)).card ∧
      ∀ S ⊆ A, S.card ≤ (S.biUnion (fun a => G.neighborFinset a)).card + d := by
  let f (S : Finset V) : ℕ := S.card - (S.biUnion (fun a => G.neighborFinset a)).card
  have h_nonempty : A.powerset.Nonempty := ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset A)⟩
  obtain ⟨S₁, hS₁_mem, hS₁_max⟩ := Finset.exists_max_image A.powerset f h_nonempty
  have hS₁_sub : S₁ ⊆ A := Finset.mem_powerset.mp hS₁_mem
  by_cases hd : f S₁ = 0
  · refine ⟨∅, 0, Finset.empty_subset A, by simp, by simp, ?_⟩
    intro S hS
    have hS_pow : S ∈ A.powerset := Finset.mem_powerset.mpr hS
    have hle := hS₁_max S hS_pow
    have : f S ≤ 0 := by omega
    have : S.card ≤ (S.biUnion (fun a => G.neighborFinset a)).card := by
      dsimp [f] at this; omega
    omega
  · have h_pos : 0 < f S₁ := by omega
    have h_le_card : (S₁.biUnion (fun a => G.neighborFinset a)).card ≤ S₁.card := by
      dsimp [f] at h_pos; omega
    refine ⟨S₁, f S₁, hS₁_sub, h_le_card, rfl, ?_⟩
    intro S hS
    have hS_pow : S ∈ A.powerset := Finset.mem_powerset.mpr hS
    have hle := hS₁_max S hS_pow
    have : S.card ≤ (S.biUnion (fun a => G.neighborFinset a)).card + f S := by
      dsimp [f]; omega
    omega

/--
**Strong Duality Inequality in Bipartite Graphs**:
For any $2$-colorable graph $G$, the vertex cover number is bounded by the matching number:
$$\tau(G) \le \nu(G)$$
-/
theorem konig_duality_le (G : SimpleGraph V) (h_bip : G.Colorable 2) :
    vertexCoverNumber G ≤ matchingNumber G := by
  obtain ⟨c⟩ := h_bip
  let A : Finset V := Finset.filter (fun v => c v = 0) Finset.univ
  let B : Finset V := Finset.filter (fun v => c v = 1) Finset.univ
  obtain ⟨S₀, d, hS₀_sub, hS₀_card_le, hd_eq, hd_max⟩ := exists_max_defect G A
  let N (S : Finset V) : Finset V := S.biUnion (fun a => G.neighborFinset a)
  let C : Finset V := (A \ S₀) ∪ N S₀
  have hcu : ∀ v, c v = 0 ∨ c v = 1 := fun v => fin2_cases (c v)
  have hC_cov : IsVertexCover G C := by
    intro u v hadj
    have hcuv := c.valid hadj
    cases hcu u with
    | inl hu0 =>
      have huA : u ∈ A := by simp [A, hu0]
      by_cases huS : u ∈ S₀
      · right
        have hv_in : v ∈ G.neighborFinset u := (G.mem_neighborFinset u v).mpr hadj
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨u, huS, hv_in⟩)
      · left
        exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨huA, huS⟩)
    | inr hu1 =>
      cases hcu v with
      | inl hv0 =>
        have hvA : v ∈ A := by simp [A, hv0]
        by_cases hvS : v ∈ S₀
        · left
          have hu_in : u ∈ G.neighborFinset v := (G.mem_neighborFinset v u).mpr hadj.symm
          exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨v, hvS, hu_in⟩)
        · right
          exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hvA, hvS⟩)
      | inr hv1 =>
        exfalso
        apply hcuv
        rw [hu1, hv1]
  have hN_sub_B : ∀ S ⊆ A, N S ⊆ B := by
    intro S hS b hb
    simp only [N, Finset.mem_biUnion] at hb
    obtain ⟨a, haS, hab⟩ := hb
    have haA : a ∈ A := hS haS
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at haA
    rw [G.mem_neighborFinset] at hab
    have h_adj := c.valid hab
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
    cases hcu b with
    | inl h0 => exfalso; apply h_adj; rw [haA, h0]
    | inr h1 => exact h1
  have hA_disj_B : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    simp only [A, Finset.mem_filter] at hxA
    simp only [B, Finset.mem_filter] at hxB
    have : (0 : Fin 2) = 1 := hxA.2.symm.trans hxB.2
    revert this; decide
  have h_disj_C : Disjoint (A \ S₀) (N S₀) := by
    apply Disjoint.mono_left (Finset.sdiff_subset)
    apply Disjoint.mono_right (hN_sub_B S₀ hS₀_sub)
    exact hA_disj_B
  have hC_card : C.card = A.card - d := by
    rw [Finset.card_union_of_disjoint h_disj_C, Finset.card_sdiff, Finset.inter_eq_left.mpr hS₀_sub, hd_eq]
    have hS₀_le_A : S₀.card ≤ A.card := Finset.card_le_card hS₀_sub
    have hN_eq : (N S₀).card = (S₀.biUnion (fun a => G.neighborFinset a)).card := rfl
    omega
  -- Hall construction
  let t (a : V) : Finset (V ⊕ Fin d) :=
    ((G.neighborFinset a).image Sum.inl) ∪ ((Finset.univ : Finset (Fin d)).image Sum.inr)
  have h_hall : ∀ (S : Finset V), S ⊆ A → S.card ≤ (S.biUnion t).card := by
    intro S hS
    by_cases hS_emp : S = ∅
    · rw [hS_emp]; simp
    · have h_biUnion_eq : S.biUnion t = (N S).image Sum.inl ∪ (Finset.univ : Finset (Fin d)).image Sum.inr := by
        ext x
        simp only [Finset.mem_biUnion, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, N, t]
        constructor
        · rintro ⟨a, haS, hx⟩
          cases hx with
          | inl hx =>
            obtain ⟨v, hv, rfl⟩ := hx
            left; exact ⟨v, ⟨a, haS, hv⟩, rfl⟩
          | inr hx =>
            obtain ⟨i, rfl⟩ := hx
            right; exact ⟨i, rfl⟩
        · rintro (⟨v, ⟨a, haS, hv⟩, rfl⟩ | ⟨i, rfl⟩)
          · exact ⟨a, haS, Or.inl ⟨v, hv, rfl⟩⟩
          · obtain ⟨a, haS⟩ := Finset.nonempty_iff_ne_empty.mpr hS_emp
            exact ⟨a, haS, Or.inr ⟨i, rfl⟩⟩
      have h_disj : Disjoint ((N S).image Sum.inl) ((Finset.univ : Finset (Fin d)).image Sum.inr) := by
        rw [Finset.disjoint_iff_ne]
        rintro _ h1 _ h2 rfl
        obtain ⟨x, -, hx⟩ := Finset.mem_image.mp h1
        obtain ⟨y, -, hy⟩ := Finset.mem_image.mp h2
        rw [← hx] at hy
        cases hy
      rw [h_biUnion_eq, Finset.card_union_of_disjoint h_disj]
      rw [Finset.card_image_of_injective _ (fun _ _ => Sum.inl.inj), Finset.card_image_of_injective _ (fun _ _ => Sum.inr.inj)]
      rw [Finset.card_fin]
      exact hd_max S hS
  -- Apply Hall's theorem to the subtype A
  let t' (a : A) : Finset (V ⊕ Fin d) := t a.val
  have h_hall' : ∀ (S' : Finset A), S'.card ≤ (S'.biUnion t').card := by
    intro S'
    have h_sub : S'.image Subtype.val ⊆ A := by
      intro x hx
      obtain ⟨⟨y, hyA⟩, _, rfl⟩ := Finset.mem_image.mp hx
      exact hyA
    have h_card_eq : (S'.image Subtype.val).card = S'.card :=
      Finset.card_image_of_injective S' Subtype.val_injective
    have h_biUnion_eq : (S'.image Subtype.val).biUnion t = S'.biUnion t' := by
      ext x
      simp [t', t]
    have := h_hall (S'.image Subtype.val) h_sub
    rwa [h_card_eq, h_biUnion_eq] at this
  obtain ⟨f, hf_inj, hf_mem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t').mp h_hall'
  -- Filter matching edges
  let A_matched : Finset A := Finset.filter (fun a => ∃ v : V, f a = Sum.inl v) Finset.univ
  have hA_matched_card : A.card - d ≤ A_matched.card := by
    have h_univ_card : (Finset.univ : Finset A).card = A.card := by
      rw [Finset.card_univ, Fintype.card_coe]
    have h_not_matched : (Finset.univ \ A_matched).card ≤ d := by
      have h_all_inr : ∀ a ∈ (Finset.univ \ A_matched : Finset A), ∃ i : Fin d, f a = Sum.inr i := by
        intro a ha
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_filter, not_exists, A_matched] at ha
        cases hfa : f a with
        | inl v => exact (ha v hfa).elim
        | inr i => exact ⟨i, rfl⟩
      choose f_inr hf_inr using h_all_inr
      have h_inj_on : ∀ a₁ (h₁ : a₁ ∈ Finset.univ \ A_matched) a₂ (h₂ : a₂ ∈ Finset.univ \ A_matched),
          f_inr a₁ h₁ = f_inr a₂ h₂ → a₁ = a₂ := by
        intro a₁ h₁ a₂ h₂ heq
        have h1 := hf_inr a₁ h₁
        have h2 := hf_inr a₂ h₂
        have : f a₁ = f a₂ := by rw [h1, h2, heq]
        exact hf_inj this
      have h_img_card : ((Finset.univ \ A_matched).attach.image (fun ⟨a, ha⟩ => f_inr a ha)).card = (Finset.univ \ A_matched).card := by
        rw [Finset.card_image_of_injective]
        · simp
        · intro ⟨a₁, h₁⟩ ⟨a₂, h₂⟩ heq
          simp only [Subtype.mk.injEq]
          exact h_inj_on a₁ h₁ a₂ h₂ heq
      have h_le : ((Finset.univ \ A_matched).attach.image (fun ⟨a, ha⟩ => f_inr a ha)).card ≤ (Finset.univ : Finset (Fin d)).card :=
        Finset.card_le_univ _
      rw [Finset.card_fin] at h_le
      rwa [h_img_card] at h_le
    have h_split : (Finset.univ : Finset A).card = A_matched.card + (Finset.univ \ A_matched).card := by
      have h_sub : A_matched ⊆ Finset.univ := Finset.subset_univ _
      have hsdiff := Finset.card_sdiff (s := A_matched) (t := Finset.univ)
      rw [Finset.inter_eq_left.mpr h_sub] at hsdiff
      have h_le : A_matched.card ≤ (Finset.univ : Finset A).card := Finset.card_le_univ A_matched
      omega
    rw [h_univ_card] at h_split
    omega
  -- Extract matching function g : A_matched → V
  have hg_choice : ∀ a ∈ A_matched, ∃ v : V, f a = Sum.inl v ∧ G.Adj a.val v := by
    intro a ha
    simp only [A_matched, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    obtain ⟨v, hv⟩ := ha
    have hfa := hf_mem a
    simp only [t', t, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hfa
    cases hfa with
    | inl h_adj =>
      obtain ⟨v', hv', heq⟩ := h_adj
      have heq' : Sum.inl v = Sum.inl v' := hv.symm.trans heq.symm
      have : v = v' := Sum.inl.inj heq'
      subst this
      exact ⟨v, hv, (G.mem_neighborFinset a.val v).mp hv'⟩
    | inr h_inr =>
      obtain ⟨i, heq⟩ := h_inr
      have heq' : Sum.inl v = Sum.inr i := hv.symm.trans heq.symm
      cases heq'
  choose g hg_f hg_adj using hg_choice
  let M : Finset (Sym2 V) := A_matched.attach.image (fun ⟨a, ha⟩ => s(a.val, g a ha))
  have hM_card : M.card = A_matched.card := by
    rw [Finset.card_image_of_injective]
    · simp
    · intro ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩ heq
      simp only [Subtype.mk.injEq]
      have h_a1_A : a₁.val ∈ A := a₁.property
      have h_a2_A : a₂.val ∈ A := a₂.property
      have h_ga1_B : g a₁ ha₁ ∈ B := by
        have := hg_adj a₁ ha₁
        have h_adj := c.valid this
        simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at h_a1_A
        simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
        cases hcu (g a₁ ha₁) with
        | inl h0 => exfalso; apply h_adj; rw [h_a1_A, h0]
        | inr h1 => exact h1
      have h_ga2_B : g a₂ ha₂ ∈ B := by
        have := hg_adj a₂ ha₂
        have h_adj := c.valid this
        simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at h_a2_A
        simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
        cases hcu (g a₂ ha₂) with
        | inl h0 => exfalso; apply h_adj; rw [h_a2_A, h0]
        | inr h1 => exact h1
      have h_symm := Sym2.eq_iff.mp heq
      cases h_symm with
      | inl h_eq_pair =>
        exact Subtype.ext h_eq_pair.1
      | inr h_cross =>
        have ha1_in_B : a₁.val ∈ B := by rw [h_cross.1]; exact h_ga2_B
        have : a₁.val ∈ A ∩ B := Finset.mem_inter.mpr ⟨h_a1_A, ha1_in_B⟩
        rw [Finset.disjoint_iff_inter_eq_empty.mp hA_disj_B] at this
        simp at this
  have hM_matching : IsMatching G M := by
    constructor
    · intro e he
      obtain ⟨⟨a, ha⟩, -, rfl⟩ := Finset.mem_image.mp he
      simp only [SimpleGraph.mem_edgeSet]
      exact hg_adj a ha
    · intro e₁ he₁ e₂ he₂ hne
      obtain ⟨⟨a₁, ha₁⟩, -, rfl⟩ := Finset.mem_image.mp he₁
      obtain ⟨⟨a₂, ha₂⟩, -, rfl⟩ := Finset.mem_image.mp he₂
      intro ⟨v, hv₁, hv₂⟩
      have h_a1_A : a₁.val ∈ A := a₁.property
      have h_a2_A : a₂.val ∈ A := a₂.property
      have h_ga1_B : g a₁ ha₁ ∈ B := by
        have := hg_adj a₁ ha₁
        have h_adj := c.valid this
        simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at h_a1_A
        simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
        cases hcu (g a₁ ha₁) with
        | inl h0 => exfalso; apply h_adj; rw [h_a1_A, h0]
        | inr h1 => exact h1
      have h_ga2_B : g a₂ ha₂ ∈ B := by
        have := hg_adj a₂ ha₂
        have h_adj := c.valid this
        simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at h_a2_A
        simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
        cases hcu (g a₂ ha₂) with
        | inl h0 => exfalso; apply h_adj; rw [h_a2_A, h0]
        | inr h1 => exact h1
      have hv1_cases : v = a₁.val ∨ v = g a₁ ha₁ := Sym2.mem_iff.mp hv₁
      have hv2_cases : v = a₂.val ∨ v = g a₂ ha₂ := Sym2.mem_iff.mp hv₂
      cases hv1_cases with
      | inl hv_a1 =>
        cases hv2_cases with
        | inl hv_a2 =>
          have : a₁.val = a₂.val := hv_a1.symm.trans hv_a2
          have : a₁ = a₂ := Subtype.ext this
          subst this
          exact hne rfl
        | inr hv_ga2 =>
          have : a₁.val = g a₂ ha₂ := hv_a1.symm.trans hv_ga2
          have : a₁.val ∈ B := this ▸ h_ga2_B
          have : a₁.val ∈ A ∩ B := Finset.mem_inter.mpr ⟨h_a1_A, this⟩
          rw [Finset.disjoint_iff_inter_eq_empty.mp hA_disj_B] at this
          simp at this
      | inr hv_ga1 =>
        cases hv2_cases with
        | inl hv_a2 =>
          have : g a₁ ha₁ = a₂.val := hv_ga1.symm.trans hv_a2
          have : a₂.val ∈ B := this ▸ h_ga1_B
          have : a₂.val ∈ A ∩ B := Finset.mem_inter.mpr ⟨h_a2_A, this⟩
          rw [Finset.disjoint_iff_inter_eq_empty.mp hA_disj_B] at this
          simp at this
        | inr hv_ga2 =>
          have hg_eq : g a₁ ha₁ = g a₂ ha₂ := hv_ga1.symm.trans hv_ga2
          have hf_eq : f a₁ = f a₂ := by
            rw [hg_f a₁ ha₁, hg_f a₂ ha₂, hg_eq]
          have : a₁ = a₂ := hf_inj hf_eq
          subst this
          exact hne rfl
  -- Now connect vertex cover and matching numbers
  let SC := { k : ℕ | ∃ C : Finset V, IsVertexCover G C ∧ C.card = k }
  let SM := { k : ℕ | ∃ M : Finset (Sym2 V), IsMatching G M ∧ M.card = k }
  have hC_in_SC : C.card ∈ SC := ⟨C, hC_cov, rfl⟩
  have hM_in_SM : M.card ∈ SM := ⟨M, hM_matching, rfl⟩
  have hSC_bddBelow : BddBelow SC := ⟨0, fun _ _ => Nat.zero_le _⟩
  have hSM_bddAbove : BddAbove SM := ⟨Fintype.card (Sym2 V), by
    rintro k ⟨M', _, rfl⟩
    exact Finset.card_le_univ M'⟩
  have h_tau_le : vertexCoverNumber G ≤ C.card := csInf_le hSC_bddBelow hC_in_SC
  have h_le_nu : M.card ≤ matchingNumber G := le_csSup hSM_bddAbove hM_in_SM
  rw [hC_card] at h_tau_le
  rw [hM_card] at h_le_nu
  omega

/--
**Kőnig–Egerváry Theorem (1931)**:
In any bipartite ($2$-colorable) graph $G$, the maximum size of a matching equals the minimum
size of a vertex cover (strong min-max duality):
$$\nu(G) = \tau(G)$$
-/
theorem konig_duality (G : SimpleGraph V) (h_bip : G.Colorable 2) :
    matchingNumber G = vertexCoverNumber G :=
  le_antisymm (weak_duality G) (konig_duality_le G h_bip)

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
