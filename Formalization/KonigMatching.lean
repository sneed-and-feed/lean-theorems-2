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
- `isVertexCover_bipartite_defect`: Vertex cover construction from maximal defect set.
- `bipartite_defect_cover_card`: Cardinality $|C| = |A| - d$ for defect cover.
- `augmentedNeighbors`: Augmented neighborhood family $t(a) = N(a) \oplus \text{Fin } d$.
- `hall_condition_augmented`: Hall condition satisfaction for augmented neighborhoods.
- `exists_matching_from_hall_inj`: Extraction and validity of matching from Hall injection.
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

omit [Fintype V] [DecidableEq V] in
/-- The empty edge set is always a valid matching. -/
theorem isMatching_empty (G : SimpleGraph V) : IsMatching G ∅ :=
  ⟨by simp, by simp⟩

omit [DecidableEq V] in
/-- The full vertex set is always a valid vertex cover. -/
theorem isVertexCover_univ (G : SimpleGraph V) : IsVertexCover G Finset.univ :=
  fun _ _ _ => Or.inl (Finset.mem_univ _)

/-- The matching number $\nu(G)$: maximum size of a matching in $G$. -/
noncomputable def matchingNumber (G : SimpleGraph V) : ℕ :=
  sSup { k : ℕ | ∃ M : Finset (Sym2 V), IsMatching G M ∧ M.card = k }

/-- The vertex cover number $\tau(G)$: minimum size of a vertex cover in $G$. -/
noncomputable def vertexCoverNumber (G : SimpleGraph V) : ℕ :=
  sInf { k : ℕ | ∃ C : Finset V, IsVertexCover G C ∧ C.card = k }

/-- An independent set in $G$ is a set of pairwise non-adjacent vertices. -/
def IsIndependentSet (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v

omit [Fintype V] [DecidableEq V] in
/-- The empty vertex set is always an independent set. -/
theorem isIndependentSet_empty (G : SimpleGraph V) : IsIndependentSet G ∅ := by
  simp [IsIndependentSet]

/-- The independence number $\alpha(G)$: maximum size of an independent set in $G$. -/
noncomputable def independenceNumber (G : SimpleGraph V) : ℕ :=
  sSup { k : ℕ | ∃ S : Finset V, IsIndependentSet G S ∧ S.card = k }

/-- An independent set corresponds bijectively to the complement of a vertex cover. -/
theorem isIndependentSet_iff_isVertexCover_compl (G : SimpleGraph V) (S : Finset V) :
    IsIndependentSet G S ↔ IsVertexCover G (Finset.univ \ S) := by
  simp only [IsIndependentSet, IsVertexCover, Finset.mem_sdiff, Finset.mem_univ, true_and]
  constructor
  · intro h u v hadj
    by_contra! h'
    exact h u h'.1 v h'.2 hadj
  · intro h u hu v hv hadj
    rcases h u v hadj with hu' | hv' <;> contradiction

omit [Fintype V] in
/--
**Weak Duality for Matchings and Vertex Covers**:
Any matching $M$ and any vertex cover $C$ satisfy $|M| \le |C|$, since each vertex in $C$
can cover at most one edge of the vertex-disjoint family $M$.
-/
theorem matching_card_le_vertexCover_card (G : SimpleGraph V) {M : Finset (Sym2 V)} {C : Finset V}
    (hM : IsMatching G M) (hC : IsVertexCover G C) :
    M.card ≤ C.card := by
  have : ∀ e ∈ M, ∃ v ∈ C, v ∈ e := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf u v =>
      rcases hC u v (hM.1 _ he) with hu | hv
      · exact ⟨u, hu, Sym2.mem_mk_left u v⟩
      · exact ⟨v, hv, Sym2.mem_mk_right u v⟩
  choose f hfC hfe using this
  have h_inj : ∀ (e₁ : Sym2 V) (he₁ : e₁ ∈ M) (e₂ : Sym2 V) (he₂ : e₂ ∈ M), f e₁ he₁ = f e₂ he₂ → e₁ = e₂ := by
    intro e₁ he₁ e₂ he₂ heq
    by_contra hne
    exact hM.2 e₁ he₁ e₂ he₂ hne ⟨f e₁ he₁, hfe e₁ he₁, heq ▸ hfe e₂ he₂⟩
  have h_sub : M.attach.image (fun ⟨e, he⟩ => f e he) ⊆ C := by
    rintro v hv
    obtain ⟨⟨e, he⟩, -, rfl⟩ := Finset.mem_image.mp hv
    exact hfC e he
  have h_card_eq : (M.attach.image (fun ⟨e, he⟩ => f e he)).card = M.card := by
    rw [Finset.card_image_of_injective]
    · exact Finset.card_attach
    · intro ⟨e₁, he₁⟩ ⟨e₂, he₂⟩ heq
      exact Subtype.ext (h_inj e₁ he₁ e₂ he₂ heq)
  rw [← h_card_eq]
  exact Finset.card_le_card h_sub

/--
**Weak Duality Theorem**:
For any finite simple graph $G$, the matching number is bounded by the vertex cover number:
$$\nu(G) \le \tau(G)$$
-/
theorem weak_duality (G : SimpleGraph V) :
    matchingNumber G ≤ vertexCoverNumber G := by
  refine le_csInf ⟨Fintype.card V, Finset.univ, isVertexCover_univ G, Finset.card_univ⟩ ?_
  rintro l ⟨C, hC, rfl⟩
  refine csSup_le ⟨0, ∅, isMatching_empty G, rfl⟩ ?_
  rintro k ⟨M, hM, rfl⟩
  exact matching_card_le_vertexCover_card G hM hC

/--
Existence of a maximal deficiency subset $S_0 \subseteq A$ for the defect form of Hall's condition.
-/
theorem exists_max_defect (G : SimpleGraph V) (A : Finset V) :
    ∃ (S₀ : Finset V) (d : ℕ), S₀ ⊆ A ∧
      (S₀.biUnion (fun a => G.neighborFinset a)).card ≤ S₀.card ∧
      d = S₀.card - (S₀.biUnion (fun a => G.neighborFinset a)).card ∧
      ∀ S ⊆ A, S.card ≤ (S.biUnion (fun a => G.neighborFinset a)).card + d := by
  let f (S : Finset V) : ℕ := S.card - (S.biUnion (fun a => G.neighborFinset a)).card
  obtain ⟨S₁, hS₁_mem, hS₁_max⟩ := Finset.exists_max_image A.powerset f
    ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset A)⟩
  have hS₁_sub : S₁ ⊆ A := Finset.mem_powerset.mp hS₁_mem
  by_cases hd : f S₁ = 0
  · refine ⟨∅, 0, Finset.empty_subset A, by simp, by simp, fun S hS => ?_⟩
    have := hS₁_max S (Finset.mem_powerset.mpr hS)
    dsimp [f] at hd this; omega
  · refine ⟨S₁, f S₁, hS₁_sub, by dsimp [f] at *; omega, rfl, fun S hS => ?_⟩
    have := hS₁_max S (Finset.mem_powerset.mpr hS)
    dsimp [f] at *; omega

/-! ### Modular Helpers for Kőnig's Duality Theorem -/

/-- In a 2-colored graph, neighbors of vertices colored 0 all have color 1. -/
lemma bipartite_neighborFinset_subset (G : SimpleGraph V) (c : G.Coloring (Fin 2)) (S : Finset V)
    (hS : ∀ x ∈ S, c x = 0) :
    S.biUnion (fun a => G.neighborFinset a) ⊆ Finset.filter (fun v => c v = 1) Finset.univ := by
  intro b hb
  simp only [Finset.mem_biUnion, G.mem_neighborFinset] at hb
  obtain ⟨a, ha, hadj⟩ := hb
  have hc := c.valid hadj
  have ha0 : c a = 0 := hS a ha
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  cases fin2_cases (c b) with
  | inl h0 => exfalso; apply hc; rw [ha0, h0]
  | inr h1 => exact h1

/-- Construction of a vertex cover $(A \setminus S_0) \cup N(S_0)$ from a defect set $S_0 \subseteq A$. -/
lemma isVertexCover_bipartite_defect (G : SimpleGraph V) (c : G.Coloring (Fin 2))
    (A S₀ : Finset V) (hA : A = Finset.filter (fun v => c v = 0) Finset.univ) (_hS₀ : S₀ ⊆ A) :
    IsVertexCover G ((A \ S₀) ∪ S₀.biUnion (fun a => G.neighborFinset a)) := by
  have h_cov (x y : V) (hxy : G.Adj x y) (hx0 : c x = 0) :
      (x ∈ (A \ S₀) ∪ S₀.biUnion (fun a => G.neighborFinset a)) ∨ (y ∈ (A \ S₀) ∪ S₀.biUnion (fun a => G.neighborFinset a)) := by
    by_cases hxS : x ∈ S₀
    · exact Or.inr (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨x, hxS, (G.mem_neighborFinset x y).mpr hxy⟩))
    · exact Or.inl (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨by simp [hA, hx0], hxS⟩))
  intro u v hadj
  have hc := c.valid hadj
  rcases fin2_cases (c u) with hu0 | hu1
  · exact h_cov u v hadj hu0
  · rcases fin2_cases (c v) with hv0 | hv1
    · exact (h_cov v u hadj.symm hv0).symm
    · exact False.elim (hc (by rw [hu1, hv1]))

/-- Cardinality of the vertex cover $(A \setminus S_0) \cup N(S_0)$ is exactly $|A| - d$. -/
lemma bipartite_defect_cover_card (G : SimpleGraph V) (c : G.Coloring (Fin 2))
    (A S₀ : Finset V) (d : ℕ)
    (hA : A = Finset.filter (fun v => c v = 0) Finset.univ)
    (hS₀ : S₀ ⊆ A)
    (hd_eq : d = S₀.card - (S₀.biUnion (fun a => G.neighborFinset a)).card)
    (hS₀_le : (S₀.biUnion (fun a => G.neighborFinset a)).card ≤ S₀.card) :
    ((A \ S₀) ∪ S₀.biUnion (fun a => G.neighborFinset a)).card = A.card - d := by
  have h_disj : Disjoint (A \ S₀) (S₀.biUnion (fun a => G.neighborFinset a)) := by
    refine Disjoint.mono Finset.sdiff_subset (bipartite_neighborFinset_subset G c S₀ ?_) ?_
    · intro x hx
      have := hS₀ hx
      rw [hA, Finset.mem_filter] at this
      exact this.2
    · rw [hA, Finset.disjoint_left]
      intro x hxA hxB
      have := (Finset.mem_filter.mp hxA).2.symm.trans (Finset.mem_filter.mp hxB).2
      revert this; decide
  rw [Finset.card_union_of_disjoint h_disj, Finset.card_sdiff, Finset.inter_eq_left.mpr hS₀, hd_eq]
  have := Finset.card_le_card hS₀
  omega

/-- Augmented neighborhood family for Hall's condition with defect $d$. -/
noncomputable def augmentedNeighbors (G : SimpleGraph V) (d : ℕ) (a : V) : Finset (V ⊕ Fin d) :=
  (G.neighborFinset a).image Sum.inl ∪ (Finset.univ : Finset (Fin d)).image Sum.inr

lemma augmentedNeighbors_biUnion (G : SimpleGraph V) (d : ℕ) {S : Finset V} (hS : S.Nonempty) :
    S.biUnion (augmentedNeighbors G d) =
      (S.biUnion (fun a => G.neighborFinset a)).image Sum.inl ∪ (Finset.univ : Finset (Fin d)).image Sum.inr := by
  ext (v | i) <;> simp [augmentedNeighbors, hS.exists_mem]

lemma card_augmentedNeighbors_biUnion (G : SimpleGraph V) (d : ℕ) {S : Finset V} (hS : S.Nonempty) :
    (S.biUnion (augmentedNeighbors G d)).card = (S.biUnion (fun a => G.neighborFinset a)).card + d := by
  have h_disj : Disjoint ((S.biUnion (fun a => G.neighborFinset a)).image Sum.inl)
      ((Finset.univ : Finset (Fin d)).image Sum.inr) := by simp [Finset.disjoint_left]
  rw [augmentedNeighbors_biUnion G d hS, Finset.card_union_of_disjoint h_disj,
      Finset.card_image_of_injective _ (fun _ _ => Sum.inl.inj),
      Finset.card_image_of_injective _ (fun _ _ => Sum.inr.inj),
      Finset.card_fin]

/-- Hall's condition holds for the augmented neighborhood family on the subtype $A$. -/
lemma hall_condition_augmented (G : SimpleGraph V) (A : Finset V) (d : ℕ)
    (hd_max : ∀ S ⊆ A, S.card ≤ (S.biUnion (fun a => G.neighborFinset a)).card + d)
    (S' : Finset A) :
    S'.card ≤ (S'.biUnion (fun a => augmentedNeighbors G d a.val)).card := by
  by_cases hS' : S'.Nonempty
  · have h_sub : S'.image Subtype.val ⊆ A := fun x hx => by
      obtain ⟨⟨y, hyA⟩, -, rfl⟩ := Finset.mem_image.mp hx; exact hyA
    have h_nonemp : (S'.image Subtype.val).Nonempty := hS'.image Subtype.val
    have h_biUnion : (S'.image Subtype.val).biUnion (augmentedNeighbors G d) =
        S'.biUnion (fun a => augmentedNeighbors G d a.val) := by
      ext x; simp [augmentedNeighbors]
    rw [← Finset.card_image_of_injective S' Subtype.val_injective, ← h_biUnion,
        card_augmentedNeighbors_biUnion G d h_nonemp]
    exact hd_max (S'.image Subtype.val) h_sub
  · rw [Finset.nonempty_iff_ne_empty, not_not] at hS'
    simp [hS']

/-- Extraction of a valid matching $M$ of cardinality at least $|A| - d$ from Hall's injection. -/
lemma exists_matching_from_hall_inj (G : SimpleGraph V) (c : G.Coloring (Fin 2))
    (A : Finset V) (d : ℕ)
    (hA : A = Finset.filter (fun v => c v = 0) Finset.univ)
    (f : A → V ⊕ Fin d) (hf_inj : Function.Injective f)
    (hf_mem : ∀ a : A, f a ∈ augmentedNeighbors G d a.val) :
    ∃ M : Finset (Sym2 V), IsMatching G M ∧ A.card - d ≤ M.card := by
  let A_mat : Finset A := Finset.filter (fun a => ∃ v : V, f a = Sum.inl v) Finset.univ
  have h_compl_card : (Finset.univ \ A_mat : Finset A).card ≤ d := by
    have h_inr : ∀ a ∈ (Finset.univ \ A_mat : Finset A), ∃ i : Fin d, f a = Sum.inr i := by
      intro a ha
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_filter, not_exists, A_mat] at ha
      cases hfa : f a with
      | inl v => exact (ha v hfa).elim
      | inr i => exact ⟨i, rfl⟩
    choose finr hfinr using h_inr
    have h_sub : (Finset.univ \ A_mat).attach.image (fun ⟨a, ha⟩ => finr a ha) ⊆ Finset.univ :=
      Finset.subset_univ _
    have h_inj' : ∀ (x y : { a : A // a ∈ Finset.univ \ A_mat }), finr x.1 x.2 = finr y.1 y.2 → x = y := by
      rintro ⟨a₁, h₁⟩ ⟨a₂, h₂⟩ heq
      have : f a₁ = f a₂ := by rw [hfinr a₁ h₁, hfinr a₂ h₂, heq]
      exact Subtype.ext (hf_inj this)
    have := Finset.card_le_card h_sub
    rw [Finset.card_image_of_injective _ (fun _ _ => h_inj' _ _), Finset.card_attach, Finset.card_fin] at this
    exact this
  have hA_mat_card : A.card - d ≤ A_mat.card := by
    have h_split := Finset.card_sdiff (s := A_mat) (t := Finset.univ)
    rw [Finset.inter_eq_left.mpr (Finset.subset_univ _), Finset.card_univ, Fintype.card_coe] at h_split
    omega
  have hg_choice : ∀ a ∈ A_mat, ∃ v : V, f a = Sum.inl v ∧ G.Adj a.val v := by
    intro a ha
    simp only [A_mat, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    obtain ⟨v, hv⟩ := ha
    have hfa := hf_mem a
    simp only [augmentedNeighbors, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hfa
    rcases hfa with (⟨v', hv', heq⟩ | ⟨i, heq⟩)
    · have : v = v' := Sum.inl.inj (hv.symm.trans heq.symm)
      subst this
      exact ⟨v, hv, (G.mem_neighborFinset a.val v).mp hv'⟩
    · cases hv.symm.trans heq.symm
  choose g hg_f hg_adj using hg_choice
  let M : Finset (Sym2 V) := A_mat.attach.image (fun ⟨a, ha⟩ => s(a.val, g a ha))
  have ha_c : ∀ a : A, c a.val = 0 := fun a => by
    have ha := a.property
    have : a.val ∈ Finset.filter (fun v => c v = 0) Finset.univ := hA ▸ ha
    exact (Finset.mem_filter.mp this).2
  have hg_c : ∀ (a : A) (ha : a ∈ A_mat), c (g a ha) = 1 := by
    intro a ha
    have hc := c.valid (hg_adj a ha)
    cases fin2_cases (c (g a ha)) with
    | inl h0 => exfalso; apply hc; rw [ha_c a, h0]
    | inr h1 => exact h1
  have hM_card : M.card = A_mat.card := by
    rw [Finset.card_image_of_injective]
    · exact Finset.card_attach
    · rintro ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩ heq
      simp only [Subtype.mk.injEq]
      rcases Sym2.eq_iff.mp heq with (⟨h1, -⟩ | ⟨h1, -⟩)
      · exact Subtype.ext h1
      · exfalso
        have : c a₁.val = c (g a₂ ha₂) := congrArg c h1
        rw [ha_c a₁, hg_c a₂ ha₂] at this
        revert this; decide
  refine ⟨M, ⟨?_, ?_⟩, by omega⟩
  · rintro e he
    obtain ⟨⟨a, ha⟩, -, rfl⟩ := Finset.mem_image.mp he
    exact hg_adj a ha
  · rintro e₁ he₁ e₂ he₂ hne ⟨w, hw₁, hw₂⟩
    obtain ⟨⟨a₁, ha₁⟩, -, rfl⟩ := Finset.mem_image.mp he₁
    obtain ⟨⟨a₂, ha₂⟩, -, rfl⟩ := Finset.mem_image.mp he₂
    rcases Sym2.mem_iff.mp hw₁ with (hw1 | hw1) <;> rcases Sym2.mem_iff.mp hw₂ with (hw2 | hw2)
    · have h_eq : a₁.val = a₂.val := hw1.symm.trans hw2
      have : a₁ = a₂ := Subtype.ext h_eq
      subst this; exact hne rfl
    · exfalso
      have : c a₁.val = c (g a₂ ha₂) := by rw [← hw1, hw2]
      rw [ha_c a₁, hg_c a₂ ha₂] at this
      revert this; decide
    · exfalso
      have : c (g a₁ ha₁) = c a₂.val := by rw [← hw1, hw2]
      rw [hg_c a₁ ha₁, ha_c a₂] at this
      revert this; decide
    · have hg_eq : g a₁ ha₁ = g a₂ ha₂ := hw1.symm.trans hw2
      have hf_eq : f a₁ = f a₂ := by rw [hg_f a₁ ha₁, hg_f a₂ ha₂, hg_eq]
      have : a₁ = a₂ := hf_inj hf_eq
      subst this; exact hne rfl

/--
**Strong Duality Inequality in Bipartite Graphs**:
For any $2$-colorable graph $G$, the vertex cover number is bounded by the matching number:
$$\tau(G) \le \nu(G)$$
-/
theorem konig_duality_le (G : SimpleGraph V) (h_bip : G.Colorable 2) :
    vertexCoverNumber G ≤ matchingNumber G := by
  obtain ⟨c⟩ := h_bip
  let A := Finset.filter (fun v => c v = 0) Finset.univ
  obtain ⟨S₀, d, hS₀_sub, hS₀_card_le, hd_eq, hd_max⟩ := exists_max_defect G A
  let C := (A \ S₀) ∪ S₀.biUnion (fun a => G.neighborFinset a)
  have hC_cov : IsVertexCover G C := isVertexCover_bipartite_defect G c A S₀ rfl hS₀_sub
  have hC_card : C.card = A.card - d :=
    bipartite_defect_cover_card G c A S₀ d rfl hS₀_sub hd_eq hS₀_card_le
  have h_hall' : ∀ S' : Finset A, S'.card ≤ (S'.biUnion (fun a => augmentedNeighbors G d a.val)).card :=
    hall_condition_augmented G A d hd_max
  obtain ⟨f, hf_inj, hf_mem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective (fun (a : A) => augmentedNeighbors G d a.val)).mp h_hall'
  obtain ⟨M, hM_match, hM_card⟩ := exists_matching_from_hall_inj G c A d rfl f hf_inj hf_mem
  have h_tau_le : vertexCoverNumber G ≤ C.card :=
    csInf_le ⟨0, fun _ _ => Nat.zero_le _⟩ ⟨C, hC_cov, rfl⟩
  have h_le_nu : M.card ≤ matchingNumber G :=
    le_csSup ⟨Fintype.card (Sym2 V), by rintro _ ⟨M', -, rfl⟩; exact Finset.card_le_univ M'⟩ ⟨M, hM_match, rfl⟩
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
  have hSC_nonempty : { k : ℕ | ∃ C : Finset V, IsVertexCover G C ∧ C.card = k }.Nonempty :=
    ⟨Fintype.card V, Finset.univ, isVertexCover_univ G, Finset.card_univ⟩
  obtain ⟨C, hC_cov, hC_card⟩ := Nat.sInf_mem hSC_nonempty
  have hS_ind : IsIndependentSet G (Finset.univ \ C) := by
    rw [isIndependentSet_iff_isVertexCover_compl]
    have : Finset.univ \ (Finset.univ \ C) = C := by ext x; simp
    rw [this]
    exact hC_cov
  have hS_card : (Finset.univ \ C).card = Fintype.card V - vertexCoverNumber G := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hC_card]
    rfl
  have h_le1 : Fintype.card V - vertexCoverNumber G ≤ independenceNumber G :=
    le_csSup ⟨Fintype.card V, by rintro _ ⟨S, -, rfl⟩; exact Finset.card_le_univ S⟩ ⟨_, hS_ind, hS_card⟩
  have h_le2 : ∀ k ∈ { k : ℕ | ∃ S : Finset V, IsIndependentSet G S ∧ S.card = k },
      k ≤ Fintype.card V - vertexCoverNumber G := by
    rintro k ⟨S, hS, rfl⟩
    have hC' : IsVertexCover G (Finset.univ \ S) := (isIndependentSet_iff_isVertexCover_compl G S).mp hS
    have h_tau : vertexCoverNumber G ≤ (Finset.univ \ S).card :=
      csInf_le ⟨0, fun _ _ => Nat.zero_le _⟩ ⟨_, hC', rfl⟩
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ] at h_tau
    have : S.card ≤ Fintype.card V := Finset.card_le_univ S
    omega
  have h_ind_le : independenceNumber G ≤ Fintype.card V - vertexCoverNumber G :=
    csSup_le ⟨0, ∅, isIndependentSet_empty G, rfl⟩ h_le2
  have h_tau_le : vertexCoverNumber G ≤ Fintype.card V :=
    csInf_le ⟨0, fun _ _ => Nat.zero_le _⟩ ⟨Finset.univ, isVertexCover_univ G, Finset.card_univ⟩
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
