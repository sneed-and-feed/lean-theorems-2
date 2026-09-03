import Formalization.CayleysFormula.PruferEncode
import Formalization.CayleysFormula.PruferDecode
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open scoped BigOperators
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Cayley's Tree Formula

This module formalizes **Cayley's Tree Formula** (Arthur Cayley, 1889) and the theory of
**Prüfer sequences** (Heinz Prüfer, 1918) in enumerative combinatorics without custom axioms.

## Mathematical Formulation

Let $V = \{1, 2, \dots, n\}$ be a set of $n \ge 2$ labeled vertices.
A **labeled tree** on $V$ is a connected, acyclic simple undirected graph $T = (V, E)$.

### The Main Theorem
Cayley's Tree Formula states that the number $T_n$ of distinct labeled trees on $n$ vertices is:
$$T_n = n^{n - 2}$$

### The Prüfer Sequence Bijection
Prüfer (1918) established an explicit bijection between:
1. Labeled trees on $n$ vertices $\{1, \dots, n\}$.
2. Sequences $(a_1, a_2, \dots, a_{n-2}) \in \{1, \dots, n\}^{n-2}$ of length $n - 2$.

**Encoding Algorithm**:
Given a tree $T$ on $\{1, \dots, n\}$:
- At each step $i = 1, \dots, n-2$, find the leaf (vertex of degree $1$) with the smallest label.
- Record its unique neighbor $a_i \in \{1, \dots, n\}$.
- Remove the leaf and its incident edge from $T$.
- The resulting sequence $(a_1, \dots, a_{n-2})$ is the Prüfer code $\operatorname{prufer}(T)$.

**Decoding Algorithm**:
Given a sequence $(a_1, \dots, a_{n-2})$:
- Reconstruct the edges inductively by matching each symbol with the smallest available leaf.
- Finally, connect the two remaining vertices.

## Modular Decomposition

This formalization is structured into three submodules:
1. `Formalization.CayleysFormula.PruferEncode`: Defines labeled trees (`LabeledTree`), Prüfer sequences
   (`PruferSequence`), candidate leaves, and the constructive leaf-peeling encoding algorithm (`pruferCode`).
2. `Formalization.CayleysFormula.PruferDecode`: Implements the inductive edge decoding algorithm
   (`decodeEdges`), graph reconstruction (`pruferDecodeGraph`), and proves that decoded graphs are valid trees
   (`pruferDecode_isTree`, `pruferDecode`).
3. `Formalization.CayleysFormula`: Establishes the bijection (`pruferEquiv`), proves Cayley's tree formula
   (`cayleys_tree_formula`), evaluates concrete instances (`cayley_n2`, `cayley_n3`, `cayley_n4`), defines rooted
   labeled trees (`RootedTree`), and computes the rooted trees count (`rooted_trees_count`).

## Main Definitions & Theorems
- `prufer_left_inv`: Left inverse property of Prüfer encoding and decoding.
- `prufer_right_inv`: Right inverse property of Prüfer encoding and decoding.
- `degree_eq_prufer_count`: Degree formula in terms of Prüfer code symbol multiplicity.
- `pruferEquiv`: The Prüfer bijection `LabeledTree n ≃ PruferSequence n`.
- `cayleys_tree_formula`: The primary theorem $Fintype.card (LabeledTree n) = n^{n-2}$.
- `cayley_n2`, `cayley_n3`, `cayley_n4`: Concrete evaluations for small $n$.
- `RootedTree`: Rooted labeled trees.
- `rootedTreeEquiv`: Canonical bijection `RootedTree n ≃ LabeledTree n × Fin n`.
- `rooted_trees_count`: The rooted tree formula $Fintype.card (RootedTree n) = n^{n-1}$.
- `degree_restricted_tree_count`: Formula for trees with a prescribed degree sequence.

## References
- Cayley, A. (1889). *A theorem on trees*. Quart. J. Math., 23, 376–378.
- Borchardt, C. W. (1860). *Über eine der Interpolation entsprechende Darstellung der Eliminations-Resultante*. J. Reine Angew. Math., 57, 111–121.
- Prüfer, H. (1918). *Neuer Beweis eines Satzes über Permutationen*. Arch. Math. Phys., 27, 742–744.
- Stanley, R. P. (1999). *Enumerative Combinatorics, Volume 2*. Cambridge Studies in Advanced Mathematics.
-/

variable {n : ℕ}

theorem exists_adj_of_reachable_ne {V : Type*} {G : SimpleGraph V} {u w : V}
    (h : G.Reachable u w) (hne : u ≠ w) : ∃ z, G.Adj u z := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => contradiction
  | cons hadj p' _ => exact ⟨_, hadj⟩

/-- The neighbors of vertex `v` among remaining vertices `S`. -/
noncomputable def vertNeighbors (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v : Fin n) : Finset (Fin n) :=
  S.filter (fun u => G.Adj v u)

@[simp] lemma mem_vertNeighbors (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v u : Fin n) :
    u ∈ vertNeighbors G S v ↔ u ∈ S ∧ G.Adj v u := by
  dsimp [vertNeighbors]
  exact Finset.mem_filter

noncomputable def smallestLeaf' (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Option (Fin n) :=
  let leaves := S.filter (fun v => (vertNeighbors G S v).card = 1)
  if h : leaves.Nonempty then
    some (leaves.min' h)
  else
    none

lemma smallestLeaf'_eq_smallestLeaf (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    smallestLeaf' G S = smallestLeaf G S := rfl

lemma smallestLeaf_eq_some (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v : Fin n)
    (hv_mem : v ∈ S) (hv_card : (vertNeighbors G S v).card = 1)
    (h_all : ∀ u ∈ S, (vertNeighbors G S u).card = 1 → v ≤ u) :
    smallestLeaf' G S = some v := by
  dsimp only [smallestLeaf']
  split_ifs with h
  · congr 1
    refine le_antisymm (Finset.min'_le _ v (by rw [Finset.mem_filter]; exact ⟨hv_mem, hv_card⟩)) ?_
    refine Finset.le_min' _ _ _ (fun u hu => ?_)
    rw [Finset.mem_filter] at hu
    exact h_all u hu.1 hu.2
  · have h_ne : (S.filter (fun v => (vertNeighbors G S v).card = 1)).Nonempty :=
      ⟨v, by rw [Finset.mem_filter]; exact ⟨hv_mem, hv_card⟩⟩
    contradiction

noncomputable def leafNeighbor' (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v : Fin n) : Option (Fin n) :=
  let neighbors := vertNeighbors G S v
  if h : neighbors.Nonempty then
    some (neighbors.min' h)
  else
    none

lemma leafNeighbor'_eq_leafNeighbor (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v : Fin n) :
    leafNeighbor' G S v = leafNeighbor G S v := rfl

lemma leafNeighbor_eq_some (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v a : Fin n)
    (h_adj : vertNeighbors G S v = {a}) :
    leafNeighbor' G S v = some a := by
  dsimp only [leafNeighbor']
  split_ifs with h
  · have : (vertNeighbors G S v).min' h = a := by
      have ha_mem : a ∈ vertNeighbors G S v := by rw [h_adj]; exact Finset.mem_singleton_self a
      refine le_antisymm (Finset.min'_le _ a ha_mem) ?_
      refine Finset.le_min' _ h a (fun u hu => ?_)
      rw [h_adj, Finset.mem_singleton] at hu
      subst hu
      rfl
    rw [this]
  · have : (vertNeighbors G S v).Nonempty := by
      rw [h_adj]
      exact Finset.singleton_nonempty a
    contradiction

lemma vertNeighbors_congr (G1 G2 : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v : Fin n)
    (h_adj : ∀ x ∈ S, G1.Adj v x ↔ G2.Adj v x) :
    S.filter (fun u => G1.Adj v u) = S.filter (fun u => G2.Adj v u) := by
  ext u
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hu, hadj⟩; exact ⟨hu, (h_adj u hu).mp hadj⟩
  · rintro ⟨hu, hadj⟩; exact ⟨hu, (h_adj u hu).mpr hadj⟩

lemma smallestLeaf_congr (G1 G2 : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (h_adj : ∀ x ∈ S, ∀ y ∈ S, G1.Adj x y ↔ G2.Adj x y) :
    smallestLeaf G1 S = smallestLeaf G2 S := by
  dsimp [smallestLeaf]
  have h_leaves : S.filter (fun v => (S.filter (fun u => G1.Adj v u)).card = 1) =
      S.filter (fun v => (S.filter (fun u => G2.Adj v u)).card = 1) := by
    apply Finset.filter_congr
    intro v hv
    rw [vertNeighbors_congr G1 G2 S v (h_adj v hv)]
  rw [h_leaves]

lemma leafNeighbor_congr (G1 G2 : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v : Fin n)
    (h_adj : ∀ x ∈ S, G1.Adj v x ↔ G2.Adj v x) :
    leafNeighbor G1 S v = leafNeighbor G2 S v := by
  dsimp [leafNeighbor]
  rw [vertNeighbors_congr G1 G2 S v h_adj]

lemma smallestLeaf_mem_S (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v : Fin n)
    (h : smallestLeaf G S = some v) : v ∈ S := by
  dsimp [smallestLeaf] at h
  split_ifs at h with hne
  · cases h
    have hv := Finset.min'_mem _ hne
    rw [Finset.mem_filter] at hv
    exact hv.1

lemma pruferPeelStep_congr (G1 G2 : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (h_adj : ∀ x ∈ S, ∀ y ∈ S, G1.Adj x y ↔ G2.Adj x y) :
    pruferPeelStep G1 S = pruferPeelStep G2 S := by
  dsimp [pruferPeelStep]
  have h_sl := smallestLeaf_congr G1 G2 S h_adj
  rw [h_sl]
  cases h_case : smallestLeaf G2 S with
  | none => rfl
  | some v =>
    dsimp
    have hv_in := smallestLeaf_mem_S G2 S v h_case
    have h_ln := leafNeighbor_congr G1 G2 S v (h_adj v hv_in)
    rw [h_ln]

lemma pruferPeelIter_congr (k : ℕ) :
    ∀ (G1 G2 : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (_h_adj : ∀ x ∈ S, ∀ y ∈ S, G1.Adj x y ↔ G2.Adj x y),
    pruferPeelIter k G1 S = pruferPeelIter k G2 S := by
  induction k with
  | zero => intros; rfl
  | succ k ih =>
    intro G1 G2 S h_adj
    dsimp [pruferPeelIter]
    have h_step := pruferPeelStep_congr G1 G2 S h_adj
    rw [h_step]
    rcases h_step_res : pruferPeelStep G2 S with ⟨u_opt, S'⟩
    dsimp
    have h_sub : ∀ x ∈ S', ∀ y ∈ S', G1.Adj x y ↔ G2.Adj x y := by
      dsimp [pruferPeelStep] at h_step_res
      cases h_case : smallestLeaf G2 S with
      | none =>
        rw [h_case] at h_step_res
        injection h_step_res with _ hS'
        subst hS'
        exact h_adj
      | some v =>
        rw [h_case] at h_step_res
        dsimp at h_step_res
        injection h_step_res with _ hS'
        subst hS'
        intro x hx y hy
        rw [Finset.mem_erase] at hx hy
        exact h_adj x hx.2 y hy.2
    cases u_opt with
    | none => exact ih G1 G2 S' h_sub
    | some u => rw [ih G1 G2 S' h_sub]

lemma decodeEdges_adj_v (a : Fin n) (rest : List (Fin n)) (S : Finset (Fin n))
    (hS : rest.length + 3 = S.card) (hL : ∀ x ∈ a :: rest, x ∈ S) :
    let v := (pruferLeaves n S (a :: rest)).min' (pruferLeaves_nonempty (by simp; omega))
    let G := SimpleGraph.fromEdgeSet (decodeEdges n (a :: rest) S : Set (Sym2 (Fin n)))
    vertNeighbors G S v = {a} := by
  intro v G
  have h_nonempty : (pruferLeaves n S (a :: rest)).Nonempty :=
    pruferLeaves_nonempty (by simp; omega)
  have hv_mem : v ∈ pruferLeaves n S (a :: rest) := Finset.min'_mem _ h_nonempty
  simp only [pruferLeaves, Finset.mem_filter] at hv_mem
  have ha_mem : a ∈ S := hL a (List.mem_cons_self)
  have h_v_ne_a : v ≠ a := by
    intro h_eq
    have : v ∈ a :: rest := h_eq ▸ List.mem_cons_self
    exact hv_mem.2 this
  have h_card_rest : rest.length + 2 = (S.erase v).card := by
    rw [Finset.card_erase_of_mem hv_mem.1]
    omega
  have hL_rest : ∀ x ∈ rest, x ∈ S.erase v := by
    intro x hx
    rw [Finset.mem_erase]
    refine ⟨?_, hL x (List.mem_cons_of_mem a hx)⟩
    rintro rfl
    exact hv_mem.2 (List.mem_cons_of_mem a hx)
  have h_dec : decodeEdges n (a :: rest) S = insert s(v, a) (decodeEdges n rest (S.erase v)) :=
    decodeEdges_cons n a rest S hS v rfl
  ext w
  rw [mem_vertNeighbors, Finset.mem_singleton]
  constructor
  · rintro ⟨_hwS, hadj⟩
    dsimp [G] at hadj
    rw [h_dec] at hadj
    rw [SimpleGraph.fromEdgeSet_adj] at hadj
    rcases hadj with ⟨h_edge, h_ne⟩
    rw [Finset.mem_coe, Finset.mem_insert] at h_edge
    rcases h_edge with h_va | h_rest
    · rw [Sym2.eq_iff] at h_va
      rcases h_va with ⟨_, rfl⟩ | ⟨hva, _⟩
      · rfl
      · exact False.elim (h_v_ne_a hva)
    · have h_ep := decodeEdges_mem_endpoints h_card_rest hL_rest s(v, w) h_rest v (by simp [Sym2.mem_iff])
      rw [Finset.mem_erase] at h_ep
      exact False.elim (h_ep.1 rfl)
  · rintro rfl
    refine ⟨ha_mem, ?_⟩
    dsimp [G]
    rw [SimpleGraph.fromEdgeSet_adj]
    refine ⟨?_, h_v_ne_a⟩
    rw [Finset.mem_coe, h_dec, Finset.mem_insert]
    exact Or.inl rfl

lemma decodeEdges_degree_a_ge_two (a : Fin n) (rest : List (Fin n)) (S : Finset (Fin n))
    (hS : rest.length + 3 = S.card) (hL : ∀ x ∈ a :: rest, x ∈ S) :
    let G := SimpleGraph.fromEdgeSet (decodeEdges n (a :: rest) S : Set (Sym2 (Fin n)))
    2 ≤ (vertNeighbors G S a).card := by
  intro G
  have h_nonempty : (pruferLeaves n S (a :: rest)).Nonempty :=
    pruferLeaves_nonempty (by simp; omega)
  let v := (pruferLeaves n S (a :: rest)).min' h_nonempty
  have hv_mem : v ∈ pruferLeaves n S (a :: rest) := Finset.min'_mem _ h_nonempty
  simp only [pruferLeaves, Finset.mem_filter] at hv_mem
  have ha_mem : a ∈ S := hL a (List.mem_cons_self)
  have h_v_ne_a : v ≠ a := by
    intro h_eq
    have : v ∈ a :: rest := h_eq ▸ List.mem_cons_self
    exact hv_mem.2 this
  have h_card_rest : rest.length + 2 = (S.erase v).card := by
    rw [Finset.card_erase_of_mem hv_mem.1]
    omega
  have hL_rest : ∀ x ∈ rest, x ∈ S.erase v := by
    intro x hx
    rw [Finset.mem_erase]
    refine ⟨?_, hL x (List.mem_cons_of_mem a hx)⟩
    rintro rfl
    exact hv_mem.2 (List.mem_cons_of_mem a hx)
  have ha_in_erase : a ∈ S.erase v := by
    rw [Finset.mem_erase]
    exact ⟨h_v_ne_a.symm, ha_mem⟩
  have h_exists_other : ∃ w ∈ S.erase v, w ≠ a := by
    have h_pos : 0 < ((S.erase v).erase a).card := by
      rw [Finset.card_erase_of_mem ha_in_erase]
      omega
    obtain ⟨w, hw⟩ := Finset.card_pos.mp h_pos
    rw [Finset.mem_erase] at hw
    exact ⟨w, hw.2, hw.1⟩
  obtain ⟨w, hw_mem, hw_ne⟩ := h_exists_other
  let G_rest := SimpleGraph.fromEdgeSet (decodeEdges n rest (S.erase v) : Set (Sym2 (Fin n)))
  have h_reach : G_rest.Reachable a w :=
    decodeEdges_reachable h_card_rest hL_rest a ha_in_erase w hw_mem
  obtain ⟨z, hz_adj⟩ := exists_adj_of_reachable_ne h_reach hw_ne.symm
  have hz_edge : s(a, z) ∈ (decodeEdges n rest (S.erase v) : Set (Sym2 (Fin n))) := by
    rw [SimpleGraph.fromEdgeSet_adj] at hz_adj
    exact hz_adj.1
  have hz_in_erase : z ∈ S.erase v := by
    have h_ep := decodeEdges_mem_endpoints h_card_rest hL_rest s(a, z) hz_edge z (by simp [Sym2.mem_iff])
    exact h_ep
  have hz_in_S : z ∈ S := Finset.mem_of_mem_erase hz_in_erase
  have hz_ne_v : z ≠ v := by
    intro h_eq
    subst h_eq
    rw [Finset.mem_erase] at hz_in_erase
    exact hz_in_erase.1 rfl
  have h_dec : decodeEdges n (a :: rest) S = insert s(v, a) (decodeEdges n rest (S.erase v)) :=
    decodeEdges_cons n a rest S hS v rfl
  have h_sub : (decodeEdges n rest (S.erase v) : Set (Sym2 (Fin n))) ⊆
      (decodeEdges n (a :: rest) S : Set (Sym2 (Fin n))) := by
    rw [h_dec, Finset.coe_insert]
    exact Set.subset_insert _ _
  have h_mono := SimpleGraph.fromEdgeSet_mono h_sub
  have hadj_az : G.Adj a z := h_mono hz_adj
  have hadj_av : G.Adj a v := by
    dsimp [G]
    rw [SimpleGraph.fromEdgeSet_adj]
    refine ⟨?_, h_v_ne_a.symm⟩
    rw [Finset.mem_coe, h_dec, Finset.mem_insert]
    left
    exact Sym2.eq_swap
  have h_pair : {v, z} ⊆ vertNeighbors G S a := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · rw [mem_vertNeighbors]
      exact ⟨hv_mem.1, hadj_av⟩
    · rw [mem_vertNeighbors]
      exact ⟨hz_in_S, hadj_az⟩
  have h_card_pair : ({v, z} : Finset (Fin n)).card = 2 := by
    rw [Finset.card_pair hz_ne_v.symm]
  have h_le := Finset.card_le_card h_pair
  rw [h_card_pair] at h_le
  exact h_le

lemma decodeEdges_degree_ge_two_of_mem (L : List (Fin n)) :
    ∀ (S : Finset (Fin n)) (hS : L.length + 2 = S.card) (hL : ∀ x ∈ L, x ∈ S) (u : Fin n) (hu : u ∈ L),
    2 ≤ (vertNeighbors (SimpleGraph.fromEdgeSet (decodeEdges n L S : Set (Sym2 (Fin n)))) S u).card := by
  induction L with
  | nil => intro S _ _ u hu; contradiction
  | cons b rest ih =>
    intro S hS hL u hu
    have h_card3 : rest.length + 3 = S.card := by simp at hS; omega
    have h_nonempty : (pruferLeaves n S (b :: rest)).Nonempty :=
      pruferLeaves_nonempty (by simp; omega)
    let v := (pruferLeaves n S (b :: rest)).min' h_nonempty
    have hv_mem : v ∈ pruferLeaves n S (b :: rest) := Finset.min'_mem _ h_nonempty
    simp only [pruferLeaves, Finset.mem_filter] at hv_mem
    have h_card_rest : rest.length + 2 = (S.erase v).card := by
      rw [Finset.card_erase_of_mem hv_mem.1]
      omega
    have hL_rest : ∀ x ∈ rest, x ∈ S.erase v := by
      intro x hx
      rw [Finset.mem_erase]
      refine ⟨?_, hL x (List.mem_cons_of_mem b hx)⟩
      rintro rfl
      exact hv_mem.2 (List.mem_cons_of_mem b hx)
    have h_dec : decodeEdges n (b :: rest) S = insert s(v, b) (decodeEdges n rest (S.erase v)) :=
      decodeEdges_cons n b rest S h_card3 v rfl
    have h_sub : (decodeEdges n rest (S.erase v) : Set (Sym2 (Fin n))) ⊆
        (decodeEdges n (b :: rest) S : Set (Sym2 (Fin n))) := by
      rw [h_dec, Finset.coe_insert]
      exact Set.subset_insert _ _
    have h_mono := SimpleGraph.fromEdgeSet_mono h_sub
    rcases List.mem_cons.mp hu with rfl | hu_rest
    · exact decodeEdges_degree_a_ge_two u rest S h_card3 hL
    · let G_rest := SimpleGraph.fromEdgeSet (decodeEdges n rest (S.erase v) : Set (Sym2 (Fin n)))
      have h_ih := ih (S.erase v) h_card_rest hL_rest u hu_rest
      have h_subset : vertNeighbors G_rest (S.erase v) u ⊆
          vertNeighbors (SimpleGraph.fromEdgeSet (decodeEdges n (b :: rest) S : Set (Sym2 (Fin n)))) S u := by
        intro w hw
        rw [mem_vertNeighbors] at hw ⊢
        exact ⟨Finset.mem_of_mem_erase hw.1, h_mono hw.2⟩
      exact le_trans h_ih (Finset.card_le_card h_subset)

lemma smallestLeaf_decodeEdges (a : Fin n) (rest : List (Fin n)) (S : Finset (Fin n))
    (hS : rest.length + 3 = S.card) (hL : ∀ x ∈ a :: rest, x ∈ S) :
    let v := (pruferLeaves n S (a :: rest)).min' (pruferLeaves_nonempty (by simp; omega))
    let G := SimpleGraph.fromEdgeSet (decodeEdges n (a :: rest) S : Set (Sym2 (Fin n)))
    smallestLeaf G S = some v := by
  intro v G
  rw [← smallestLeaf'_eq_smallestLeaf]
  have h_nonempty : (pruferLeaves n S (a :: rest)).Nonempty :=
    pruferLeaves_nonempty (by simp; omega)
  have hv_mem : v ∈ pruferLeaves n S (a :: rest) := Finset.min'_mem _ h_nonempty
  simp only [pruferLeaves, Finset.mem_filter] at hv_mem
  have hv_adj : vertNeighbors G S v = {a} := decodeEdges_adj_v a rest S hS hL
  have hv_card : (vertNeighbors G S v).card = 1 := by
    rw [hv_adj, Finset.card_singleton]
  refine smallestLeaf_eq_some G S v hv_mem.1 hv_card (fun u _hu_S hu_card => ?_)
  by_contra h_lt
  have h_not_le : ¬ (v ≤ u) := h_lt
  have hu_lt_v : u < v := lt_of_not_ge h_not_le
  have hu_not_in_pl : u ∉ pruferLeaves n S (a :: rest) := by
    intro hu_pl
    have h_min := Finset.min'_le (pruferLeaves n S (a :: rest)) u hu_pl
    omega
  have hu_in_L : u ∈ a :: rest := by
    rw [pruferLeaves, Finset.mem_filter] at hu_not_in_pl
    tauto
  have h_card_ge2 := decodeEdges_degree_ge_two_of_mem (a :: rest) S (by simp; omega) hL u hu_in_L
  have : (2 : ℕ) ≤ 1 := by
    calc (2 : ℕ) ≤ (vertNeighbors G S u).card := h_card_ge2
    _ = 1 := hu_card
  omega

lemma leafNeighbor_decodeEdges (a : Fin n) (rest : List (Fin n)) (S : Finset (Fin n))
    (hS : rest.length + 3 = S.card) (hL : ∀ x ∈ a :: rest, x ∈ S) :
    let v := (pruferLeaves n S (a :: rest)).min' (pruferLeaves_nonempty (by simp; omega))
    let G := SimpleGraph.fromEdgeSet (decodeEdges n (a :: rest) S : Set (Sym2 (Fin n)))
    leafNeighbor G S v = some a := by
  intro v G
  rw [← leafNeighbor'_eq_leafNeighbor]
  exact leafNeighbor_eq_some G S v a (decodeEdges_adj_v a rest S hS hL)

lemma pruferPeelStep_decodeEdges (a : Fin n) (rest : List (Fin n)) (S : Finset (Fin n))
    (hS : rest.length + 3 = S.card) (hL : ∀ x ∈ a :: rest, x ∈ S) :
    let v := (pruferLeaves n S (a :: rest)).min' (pruferLeaves_nonempty (by simp; omega))
    let G := SimpleGraph.fromEdgeSet (decodeEdges n (a :: rest) S : Set (Sym2 (Fin n)))
    pruferPeelStep G S = (some a, S.erase v) := by
  intro v G
  dsimp [pruferPeelStep]
  have h_leaf : smallestLeaf G S = some v := smallestLeaf_decodeEdges a rest S hS hL
  rw [h_leaf]
  dsimp
  have h_neighbor : leafNeighbor G S v = some a := leafNeighbor_decodeEdges a rest S hS hL
  rw [h_neighbor]

lemma pruferPeelIter_decodeEdges (L : List (Fin n)) :
    ∀ (S : Finset (Fin n)) (hS : L.length + 2 = S.card) (hL : ∀ x ∈ L, x ∈ S),
    pruferPeelIter L.length (SimpleGraph.fromEdgeSet (decodeEdges n L S : Set (Sym2 (Fin n)))) S = L := by
  induction L with
  | nil => intro S _ _; rfl
  | cons a rest ih =>
    intro S hS hL
    have h_card3 : rest.length + 3 = S.card := by simp at hS; omega
    have h_nonempty : (pruferLeaves n S (a :: rest)).Nonempty :=
      pruferLeaves_nonempty (by simp; omega)
    let v := (pruferLeaves n S (a :: rest)).min' h_nonempty
    have hv_mem : v ∈ pruferLeaves n S (a :: rest) := Finset.min'_mem _ h_nonempty
    simp only [pruferLeaves, Finset.mem_filter] at hv_mem
    have h_card_rest : rest.length + 2 = (S.erase v).card := by
      rw [Finset.card_erase_of_mem hv_mem.1]
      omega
    have hL_rest : ∀ x ∈ rest, x ∈ S.erase v := by
      intro x hx
      rw [Finset.mem_erase]
      refine ⟨?_, hL x (List.mem_cons_of_mem a hx)⟩
      rintro rfl
      exact hv_mem.2 (List.mem_cons_of_mem a hx)
    let G := SimpleGraph.fromEdgeSet (decodeEdges n (a :: rest) S : Set (Sym2 (Fin n)))
    let G_rest := SimpleGraph.fromEdgeSet (decodeEdges n rest (S.erase v) : Set (Sym2 (Fin n)))
    dsimp [pruferPeelIter]
    have h_step : pruferPeelStep G S = (some a, S.erase v) :=
      pruferPeelStep_decodeEdges a rest S h_card3 hL
    rw [h_step]
    dsimp
    congr 1
    have h_congr : pruferPeelIter rest.length G (S.erase v) = pruferPeelIter rest.length G_rest (S.erase v) := by
      refine pruferPeelIter_congr rest.length G G_rest (S.erase v) (fun x hx y hy => ?_)
      dsimp [G, G_rest]
      have h_dec : decodeEdges n (a :: rest) S = insert s(v, a) (decodeEdges n rest (S.erase v)) :=
        decodeEdges_cons n a rest S h_card3 v rfl
      rw [h_dec]
      rw [SimpleGraph.fromEdgeSet_adj, SimpleGraph.fromEdgeSet_adj]
      constructor
      · rintro ⟨h_edge, h_ne⟩
        rw [Finset.mem_coe, Finset.mem_insert] at h_edge
        rcases h_edge with h_va | h_rest
        · rw [Finset.mem_erase] at hx hy
          rw [Sym2.eq_iff] at h_va
          rcases h_va with ⟨rfl, _⟩ | ⟨_, rfl⟩
          · exact False.elim (hx.1 rfl)
          · exact False.elim (hy.1 rfl)
        · exact ⟨h_rest, h_ne⟩
      · rintro ⟨h_edge, h_ne⟩
        refine ⟨?_, h_ne⟩
        rw [Finset.mem_coe, Finset.mem_insert]
        exact Or.inr h_edge
    rw [h_congr]
    exact ih (S.erase v) h_card_rest hL_rest

/-- Right inverse property: encoding the decoded tree recovers the original sequence. -/
theorem prufer_right_inv (hn : 2 ≤ n) (seq : PruferSequence n) :
    pruferCode (pruferDecode hn seq) = seq := by
  have hS : ((List.finRange (n - 2)).map (fun i => seq ⟨i.val, i.isLt⟩)).length + 2 = (Finset.univ : Finset (Fin n)).card := by
    simp; omega
  have hL : ∀ x ∈ ((List.finRange (n - 2)).map (fun i => seq ⟨i.val, i.isLt⟩)), x ∈ (Finset.univ : Finset (Fin n)) := by
    intro x _; exact Finset.mem_univ x
  have h_iter_raw := pruferPeelIter_decodeEdges ((List.finRange (n - 2)).map (fun i => seq ⟨i.val, i.isLt⟩)) Finset.univ hS hL
  have h_len_map : ((List.finRange (n - 2)).map (fun i => seq ⟨i.val, i.isLt⟩)).length = n - 2 := by simp
  rw [h_len_map] at h_iter_raw
  have h_iter : pruferPeelIter (n - 2) (pruferDecodeGraph n hn seq) Finset.univ =
      ((List.finRange (n - 2)).map (fun i => seq ⟨i.val, i.isLt⟩)) := h_iter_raw
  ext i
  dsimp [pruferCode, pruferDecode]
  have h_len : (pruferPeelIter (n - 2) (pruferDecodeGraph n hn seq) Finset.univ).length = n - 2 := by
    rw [h_iter]
    simp
  have hi : i.val < (pruferPeelIter (n - 2) (pruferDecodeGraph n hn seq) Finset.univ).length := by
    rw [h_len]
    exact i.isLt
  simp only [hi, ↓reduceDIte]
  simp only [h_iter]
  simp

lemma pruferDecode_injective (hn : 2 ≤ n) : Function.Injective (pruferDecode hn) :=
  Function.HasLeftInverse.injective ⟨pruferCode, prufer_right_inv hn⟩

/-- The edges of graph G with both endpoints in S. -/
noncomputable def edgesIn (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  G.edgeFinset.filter (fun e => ∀ x ∈ e, x ∈ S)

@[simp] lemma mem_edgesIn (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (e : Sym2 (Fin n)) :
    e ∈ edgesIn G S ↔ e ∈ G.edgeFinset ∧ ∀ x ∈ e, x ∈ S :=
  Finset.mem_filter

lemma edgesIn_erase_leaf_sub (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v a : Fin n)
    (h_va : s(v, a) ∈ edgesIn G S) :
    insert s(v, a) (edgesIn G (S.erase v)) ⊆ edgesIn G S := by
  intro e he
  rw [Finset.mem_insert] at he
  rcases he with rfl | he_rest
  · exact h_va
  · rw [mem_edgesIn] at he_rest ⊢
    refine ⟨he_rest.1, fun x hx => ?_⟩
    have := he_rest.2 x hx
    rw [Finset.mem_erase] at this
    exact this.2

lemma step_sub (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v a : Fin n)
    (h_va : s(v, a) ∈ edgesIn G S) {rest : List (Fin n)}
    (rest_sub : decodeEdges n rest (S.erase v) ⊆ edgesIn G (S.erase v)) :
    insert s(v, a) (decodeEdges n rest (S.erase v)) ⊆ edgesIn G S := by
  have h1 : insert s(v, a) (decodeEdges n rest (S.erase v)) ⊆ insert s(v, a) (edgesIn G (S.erase v)) := by
    intro e he
    rw [Finset.mem_insert] at he ⊢
    rcases he with rfl | he
    · left; rfl
    · right; exact rest_sub he
  have h2 := edgesIn_erase_leaf_sub G S v a h_va
  exact subset_trans h1 h2

lemma decodeEdges_nil_sub (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (hS : S.card = 2)
    (h_nonempty : (edgesIn G S).Nonempty) :
    decodeEdges n [] S ⊆ edgesIn G S := by
  have h2 : 2 ≤ S.card := by omega
  dsimp [decodeEdges]
  split_ifs
  let h_u_ne : S.Nonempty := Finset.card_pos.mp (by omega)
  let u := S.min' h_u_ne
  let h_w_ne : (S.erase u).Nonempty := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem (Finset.min'_mem S h_u_ne)]; omega)
  let w := (S.erase u).min' h_w_ne
  have hu : u ∈ S := Finset.min'_mem S h_u_ne
  have hw_in_erase := Finset.min'_mem (S.erase u) h_w_ne
  rw [Finset.mem_erase] at hw_in_erase
  have hw : w ∈ S := hw_in_erase.2
  have huw : u ≠ w := hw_in_erase.1.symm
  obtain ⟨e, he⟩ := h_nonempty
  rw [mem_edgesIn] at he
  induction e using Sym2.inductionOn with
  | hf x y =>
    have hx : x ∈ S := he.2 x (by simp [Sym2.mem_iff])
    have hy : y ∈ S := he.2 y (by simp [Sym2.mem_iff])
    have hxy : x ≠ y := by
      have := he.1
      rw [SimpleGraph.mem_edgeFinset] at this
      exact this.ne
    have hS_eq : S = {u, w} := by
      apply Finset.eq_of_subset_of_card_le
      · intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton]
        by_cases hzu : z = u
        · left; exact hzu
        · right
          have hz_erase : z ∈ S.erase u := by rw [Finset.mem_erase]; exact ⟨hzu, hz⟩
          have h_card1 : (S.erase u).card = 1 := by rw [Finset.card_erase_of_mem hu]; omega
          obtain ⟨z0, hz0⟩ := Finset.card_eq_one.mp h_card1
          have : w = z0 := by
            have : w ∈ S.erase u := Finset.min'_mem (S.erase u) h_w_ne
            rw [hz0, Finset.mem_singleton] at this
            exact this
          subst this
          rw [hz0, Finset.mem_singleton] at hz_erase
          exact hz_erase
      · rw [hS, Finset.card_pair huw]
    have h_e_eq : s(x, y) = s(u, w) := by
      rw [hS_eq] at hx hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · contradiction
      · rfl
      · exact Sym2.eq_swap
      · contradiction
    intro z hz
    rw [Finset.mem_singleton] at hz
    subst hz
    rw [← h_e_eq]
    rw [mem_edgesIn]
    exact he

theorem prufer_left_inv_of_sub (hn : 2 ≤ n) (T : LabeledTree n)
    (h_sub : (pruferDecode hn (pruferCode T)).graph.edgeFinset ⊆ T.graph.edgeFinset) :
    pruferDecode hn (pruferCode T) = T := by
  have h_tree1 := (pruferDecode hn (pruferCode T)).isTree
  have h_tree2 := T.isTree
  have h_card1 := h_tree1.card_edgeFinset
  have h_card2 := h_tree2.card_edgeFinset
  have h_fin : Fintype.card (Fin n) = n := Fintype.card_fin n
  rw [h_fin] at h_card1 h_card2
  have h_eq : (pruferDecode hn (pruferCode T)).graph.edgeFinset = T.graph.edgeFinset :=
    Finset.eq_of_subset_of_card_le h_sub (by omega)
  apply LabeledTree.ext
  have h1 : (pruferDecode hn (pruferCode T)).graph = SimpleGraph.fromEdgeSet ((pruferDecode hn (pruferCode T)).graph.edgeFinset : Set (Sym2 (Fin n))) := by
    rw [SimpleGraph.coe_edgeFinset, SimpleGraph.fromEdgeSet_edgeSet]
  have h2 : T.graph = SimpleGraph.fromEdgeSet (T.graph.edgeFinset : Set (Sym2 (Fin n))) := by
    rw [SimpleGraph.coe_edgeFinset, SimpleGraph.fromEdgeSet_edgeSet]
  rw [h1, h2, h_eq]

lemma vertNeighbors_erase_of_not_adj (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (u w : Fin n)
    (h_not_adj : ¬ G.Adj u w) :
    vertNeighbors G (S.erase w) u = vertNeighbors G S u := by
  ext z
  simp only [mem_vertNeighbors, Finset.mem_erase]
  constructor
  · rintro ⟨⟨_, hzS⟩, hadj⟩; exact ⟨hzS, hadj⟩
  · rintro ⟨hzS, hadj⟩
    refine ⟨⟨?_, hzS⟩, hadj⟩
    rintro rfl
    exact h_not_adj hadj

lemma card_vertNeighbors_erase_of_leaf (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (w a u : Fin n)
    (hw : vertNeighbors G S w = {a}) (huS : u ∈ S) (hu_ne_a : u ≠ a) :
    (vertNeighbors G (S.erase w) u).card = (vertNeighbors G S u).card := by
  have h_not_adj : ¬ G.Adj u w := by
    intro hadj
    have : u ∈ vertNeighbors G S w := by
      rw [mem_vertNeighbors]
      exact ⟨huS, hadj.symm⟩
    rw [hw, Finset.mem_singleton] at this
    exact hu_ne_a this
  rw [vertNeighbors_erase_of_not_adj G S u w h_not_adj]

lemma card_vertNeighbors_le_one_of_peel (k : ℕ) :
    ∀ (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (_ : k + 3 = S.card)
    (w a : Fin n) (_ : w ∈ S) (_ : vertNeighbors G S w = {a})
    (rest : List (Fin n)) (_ : pruferPeelIter k G (S.erase w) = rest)
    (_ : ∀ (S' : Finset (Fin n)) (_ : k + 2 = S'.card) (u : Fin n) (_ : u ∈ S') (_ : u ∉ pruferPeelIter k G S'),
      (vertNeighbors G S' u).card ≤ 1)
    (u : Fin n) (_ : u ∈ S) (_ : u ≠ a) (_ : u ∉ rest),
    (vertNeighbors G S u).card ≤ 1 := by
  intro G S _hS w a hwS hw_adj rest h_rest ih u huS hu_not_a hu_not_rest
  by_cases huw : u = w
  · subst huw
    rw [hw_adj, Finset.card_singleton]
  · have hu_erase : u ∈ S.erase w := by
      rw [Finset.mem_erase]
      exact ⟨huw, huS⟩
    have h_card_erase : (vertNeighbors G (S.erase w) u).card = (vertNeighbors G S u).card :=
      card_vertNeighbors_erase_of_leaf G S w a u hw_adj huS hu_not_a
    rw [← h_card_erase]
    have hS_card : k + 2 = (S.erase w).card := by
      rw [Finset.card_erase_of_mem hwS]
      omega
    rw [← h_rest] at hu_not_rest
    exact ih (S.erase w) hS_card u hu_erase hu_not_rest

lemma smallestLeaf_le_of_mem (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (w u : Fin n)
    (h_sl : smallestLeaf G S = some w) (huS : u ∈ S) (hu_leaf : (vertNeighbors G S u).card = 1) :
    w ≤ u := by
  dsimp [smallestLeaf] at h_sl
  split_ifs at h_sl with hne
  injection h_sl with hw_eq
  subst hw_eq
  refine Finset.min'_le _ u ?_
  rw [Finset.mem_filter]
  exact ⟨huS, hu_leaf⟩

lemma smallestLeaf_mem_pruferLeaves (k : ℕ) (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (v a : Fin n) (h_sl : smallestLeaf G S = some v) (h_ln : leafNeighbor G S v = some a)
    (rest_sub : ∀ x ∈ pruferPeelIter k G (S.erase v), x ∈ S.erase v) :
    v ∈ pruferLeaves n S (a :: pruferPeelIter k G (S.erase v)) := by
  simp only [pruferLeaves, Finset.mem_filter, List.mem_cons, not_or]
  refine ⟨?_, ?_, ?_⟩
  · dsimp [smallestLeaf] at h_sl
    split_ifs at h_sl with hne
    injection h_sl with hv_eq
    subst hv_eq
    have := Finset.min'_mem _ hne
    rw [Finset.mem_filter] at this
    exact this.1
  · intro h_eq
    dsimp [leafNeighbor] at h_ln
    split_ifs at h_ln with hne
    injection h_ln with ha_eq
    have ha_min := Finset.min'_mem _ hne
    rw [Finset.mem_filter] at ha_min
    have : G.Adj v a := by
      rw [← ha_eq]
      exact ha_min.2
    subst h_eq
    exact this.ne rfl
  · intro h_in
    have h_in_erase := rest_sub v h_in
    rw [Finset.mem_erase] at h_in_erase
    exact h_in_erase.1 rfl

lemma prufer_leaf_eq (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (w a : Fin n) (rest : List (Fin n))
    (h_sl : smallestLeaf G S = some w)
    (h_ln : leafNeighbor G S w = some a)
    (h_deg_pos : ∀ u ∈ S, (vertNeighbors G S u).card ≠ 0)
    (h_le1 : ∀ u ∈ S, u ∉ a :: rest → (vertNeighbors G S u).card ≤ 1)
    (h_rest_sub : ∀ x ∈ rest, x ∈ S.erase w)
    (h_nonempty : (pruferLeaves n S (a :: rest)).Nonempty) :
    (pruferLeaves n S (a :: rest)).min' h_nonempty = w := by
  let v := (pruferLeaves n S (a :: rest)).min' h_nonempty
  have hw_leaves : w ∈ pruferLeaves n S (a :: rest) := by
    simp only [pruferLeaves, Finset.mem_filter, List.mem_cons, not_or]
    refine ⟨?_, ?_, ?_⟩
    · dsimp [smallestLeaf] at h_sl
      split_ifs at h_sl with hne
      injection h_sl with hw_eq
      subst hw_eq
      have := Finset.min'_mem _ hne
      rw [Finset.mem_filter] at this
      exact this.1
    · intro h_eq
      dsimp [leafNeighbor] at h_ln
      split_ifs at h_ln with hne
      injection h_ln with ha_eq
      have ha_min := Finset.min'_mem _ hne
      rw [Finset.mem_filter] at ha_min
      have : G.Adj w a := by
        rw [← ha_eq]
        exact ha_min.2
      subst h_eq
      exact this.ne rfl
    · intro h_in
      have h_in_erase := h_rest_sub w h_in
      rw [Finset.mem_erase] at h_in_erase
      exact h_in_erase.1 rfl
  have h_le : v ≤ w := Finset.min'_le _ w hw_leaves
  have hw_le : w ≤ v := by
    have hv_leaves := Finset.min'_mem _ h_nonempty
    dsimp [pruferLeaves] at hv_leaves
    rw [Finset.mem_filter] at hv_leaves
    have hvS : v ∈ S := hv_leaves.1
    have hv_not_seq : v ∉ a :: rest := hv_leaves.2
    have h_le1_v : (vertNeighbors G S v).card ≤ 1 := h_le1 v hvS hv_not_seq
    have h_ne0_v : (vertNeighbors G S v).card ≠ 0 := h_deg_pos v hvS
    have hv_leaf : (vertNeighbors G S v).card = 1 := by omega
    exact smallestLeaf_le_of_mem G S w v h_sl hvS hv_leaf
  exact le_antisymm h_le hw_le

def ValidPeel (G : SimpleGraph (Fin n)) : List (Fin n) → Finset (Fin n) → Prop
  | [], S => S.card = 2 ∧ (edgesIn G S).Nonempty
  | a :: rest, S =>
    if h : rest.length + 3 = S.card then
      let v := (pruferLeaves n S (a :: rest)).min' (pruferLeaves_nonempty (by simp; omega))
      s(v, a) ∈ edgesIn G S ∧ ValidPeel G rest (S.erase v)
    else False

lemma decodeEdges_sub_edgesIn (G : SimpleGraph (Fin n)) (L : List (Fin n)) (S : Finset (Fin n))
    (h : ValidPeel G L S) :
    decodeEdges n L S ⊆ edgesIn G S := by
  induction L generalizing S with
  | nil =>
    exact decodeEdges_nil_sub G S h.1 h.2
  | cons a rest ih =>
    dsimp [ValidPeel] at h
    split_ifs at h with hS
    let v := (pruferLeaves n S (a :: rest)).min' (pruferLeaves_nonempty (by simp; omega))
    have h_dec : decodeEdges n (a :: rest) S = insert s(v, a) (decodeEdges n rest (S.erase v)) :=
      decodeEdges_cons n a rest S hS v rfl
    rw [h_dec]
    exact step_sub G S v a h.1 (ih (S.erase v) h.2)

lemma mem_pruferDecode_edgeFinset (hn : 2 ≤ n) (seq : PruferSequence n) (e : Sym2 (Fin n))
    (he : e ∈ (pruferDecode hn seq).graph.edgeFinset) :
    e ∈ pruferDecodeEdgeFinset n hn seq := by
  have : e ∈ (pruferDecode hn seq).graph.edgeSet := Set.mem_toFinset.mp he
  have h_eq : (pruferDecode hn seq).graph.edgeSet = (SimpleGraph.fromEdgeSet (pruferDecodeEdgeFinset n hn seq : Set (Sym2 (Fin n)))).edgeSet := rfl
  rw [h_eq, SimpleGraph.edgeSet_fromEdgeSet] at this
  exact this.1

lemma pruferCode_list_eq (T : LabeledTree n)
    (h_len : (pruferPeelIter (n - 2) T.graph Finset.univ).length = n - 2) :
    ((List.finRange (n - 2)).map (fun i => (pruferCode T) ⟨i.val, i.isLt⟩)) =
      pruferPeelIter (n - 2) T.graph Finset.univ := by
  apply List.ext_getElem
  · simp [h_len]
  · intro i _h1 h2
    simp only [List.getElem_map, List.getElem_finRange]
    dsimp [pruferCode]
    simp only [h2, ↓reduceDIte]

theorem prufer_left_inv_of_validPeel (hn : 2 ≤ n) (T : LabeledTree n)
    (h_peel : ValidPeel T.graph ((List.finRange (n - 2)).map (fun i => (pruferCode T) ⟨i.val, i.isLt⟩)) Finset.univ) :
    pruferDecode hn (pruferCode T) = T := by
  refine prufer_left_inv_of_sub hn T ?_
  intro e he
  have he_dec := mem_pruferDecode_edgeFinset hn (pruferCode T) e he
  dsimp [pruferDecodeEdgeFinset] at he_dec
  have h_sub := decodeEdges_sub_edgesIn T.graph _ Finset.univ h_peel
  have he_edgesIn := h_sub he_dec
  rw [mem_edgesIn] at he_edgesIn
  exact he_edgesIn.1

lemma edgesIn_erase_leaf (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v a : Fin n)
    (hv : v ∈ S) (ha : a ∈ S) (h_adj : S.filter (fun w => G.Adj v w) = {a}) :
    edgesIn G S = insert s(v, a) (edgesIn G (S.erase v)) := by
  ext e
  rw [Finset.mem_insert, mem_edgesIn, mem_edgesIn]
  constructor
  · rintro ⟨he, heS⟩
    induction e using Sym2.inductionOn with
    | hf x y =>
      by_cases hx : x = v
      · cases hx
        have hy_adj : G.Adj v y := by
          have := he
          rw [SimpleGraph.mem_edgeFinset] at this
          exact this
        have hy_in : y ∈ S.filter (fun w => G.Adj v w) := by
          rw [Finset.mem_filter]
          exact ⟨heS y (by simp [Sym2.mem_iff]), hy_adj⟩
        rw [h_adj, Finset.mem_singleton] at hy_in
        cases hy_in
        left; rfl
      · by_cases hy : y = v
        · cases hy
          have hx_adj : G.Adj v x := by
            have := he
            rw [SimpleGraph.mem_edgeFinset] at this
            exact this.symm
          have hx_in : x ∈ S.filter (fun w => G.Adj v w) := by
            rw [Finset.mem_filter]
            exact ⟨heS x (by simp [Sym2.mem_iff]), hx_adj⟩
          rw [h_adj, Finset.mem_singleton] at hx_in
          cases hx_in
          left; exact Sym2.eq_swap
        · right
          refine ⟨he, fun z hz => ?_⟩
          have hzS := heS z hz
          rw [Finset.mem_erase]
          simp only [Sym2.mem_iff] at hz
          rcases hz with rfl | rfl
          · exact ⟨hx, hzS⟩
          · exact ⟨hy, hzS⟩
  · rintro (rfl | ⟨he, he_erase⟩)
    · have hadj : G.Adj v a := by
        have : a ∈ S.filter (fun w => G.Adj v w) := by rw [h_adj]; exact Finset.mem_singleton_self a
        rw [Finset.mem_filter] at this
        exact this.2
      refine ⟨by rw [SimpleGraph.mem_edgeFinset]; exact hadj, ?_⟩
      intro z hz
      simp only [Sym2.mem_iff] at hz
      rcases hz with rfl | rfl <;> assumption
    · refine ⟨he, fun z hz => ?_⟩
      have := he_erase z hz
      rw [Finset.mem_erase] at this
      exact this.2

lemma edgesIn_erase_leaf_card
    (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v a : Fin n)
    (hv : v ∈ S) (ha : a ∈ S)
    (h_adj : S.filter (fun w => G.Adj v w) = {a}) :
    (edgesIn G (S.erase v)).card + 1 = (edgesIn G S).card := by
  have h_eq := edgesIn_erase_leaf G S v a hv ha h_adj
  have h_not_mem : s(v, a) ∉ edgesIn G (S.erase v) := by
    intro h_in
    rw [mem_edgesIn] at h_in
    have := h_in.2 v (Sym2.mem_mk_left v a)
    exact Finset.notMem_erase v S this
  rw [h_eq, Finset.card_insert_of_notMem h_not_mem]

lemma edgesIn_card_erase_leaf (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v a : Fin n)
    (hv : v ∈ S) (ha : a ∈ S)
    (h_adj : S.filter (fun w => G.Adj v w) = {a})
    (h_card : (edgesIn G S).card = S.card - 1) :
    (edgesIn G (S.erase v)).card = (S.erase v).card - 1 := by
  have h1 := edgesIn_erase_leaf_card G S v a hv ha h_adj
  have h2 := Finset.card_erase_of_mem hv
  omega

lemma edgesIn_eq_of_peel_eq
    (v a : Fin n) (G1 G2 : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (hv : v ∈ S) (ha : a ∈ S)
    (h_adj1 : S.filter (fun w => G1.Adj v w) = {a})
    (h_adj2 : S.filter (fun w => G2.Adj v w) = {a})
    (h_rest : edgesIn G1 (S.erase v) = edgesIn G2 (S.erase v)) :
    edgesIn G1 S = edgesIn G2 S := by
  rw [edgesIn_erase_leaf G1 S v a hv ha h_adj1]
  rw [edgesIn_erase_leaf G2 S v a hv ha h_adj2]
  rw [h_rest]

lemma edgesIn_eq_of_card_two
    (G1 G2 : SimpleGraph (Fin n)) (S : Finset (Fin n)) (hS : S.card = 2)
    (h1 : (edgesIn G1 S).Nonempty) (h2 : (edgesIn G2 S).Nonempty) :
    edgesIn G1 S = edgesIn G2 S := by
  let h_u_ne : S.Nonempty := Finset.card_pos.mp (by omega)
  let u := S.min' h_u_ne
  let h_w_ne : (S.erase u).Nonempty := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem (Finset.min'_mem S h_u_ne)]; omega)
  let w := (S.erase u).min' h_w_ne
  have hu : u ∈ S := Finset.min'_mem S h_u_ne
  have hw_in_erase := Finset.min'_mem (S.erase u) h_w_ne
  rw [Finset.mem_erase] at hw_in_erase
  have hw : w ∈ S := hw_in_erase.2
  have huw : u ≠ w := hw_in_erase.1.symm
  have hS_eq : S = {u, w} := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hzu : z = u
      · left; exact hzu
      · right
        have hz_erase : z ∈ S.erase u := by rw [Finset.mem_erase]; exact ⟨hzu, hz⟩
        have h_card1 : (S.erase u).card = 1 := by rw [Finset.card_erase_of_mem hu]; omega
        obtain ⟨z0, hz0⟩ := Finset.card_eq_one.mp h_card1
        have : w = z0 := by
          have : w ∈ S.erase u := Finset.min'_mem (S.erase u) h_w_ne
          rw [hz0, Finset.mem_singleton] at this
          exact this
        subst this
        rw [hz0, Finset.mem_singleton] at hz_erase
        exact hz_erase
    · rw [hS, Finset.card_pair huw]
  have h_unique : ∀ G, (edgesIn G S).Nonempty → edgesIn G S = {s(u, w)} := by
    intro G ⟨e, he⟩
    rw [mem_edgesIn] at he
    induction e using Sym2.inductionOn with
    | hf x y =>
      have hx : x ∈ S := he.2 x (by simp [Sym2.mem_iff])
      have hy : y ∈ S := he.2 y (by simp [Sym2.mem_iff])
      have hxy : x ≠ y := by
        have := he.1
        rw [SimpleGraph.mem_edgeFinset] at this
        exact this.ne
      have h_e_eq : s(x, y) = s(u, w) := by
        rw [hS_eq] at hx hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · contradiction
        · rfl
        · exact Sym2.eq_swap
        · contradiction
      ext z
      rw [Finset.mem_singleton]
      constructor
      · intro hz
        rw [mem_edgesIn] at hz
        induction z using Sym2.inductionOn with
        | hf x' y' =>
          have hx' : x' ∈ S := hz.2 x' (by simp [Sym2.mem_iff])
          have hy' : y' ∈ S := hz.2 y' (by simp [Sym2.mem_iff])
          have hx'y' : x' ≠ y' := by
            have := hz.1
            rw [SimpleGraph.mem_edgeFinset] at this
            exact this.ne
          rw [hS_eq] at hx' hy'
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx' hy'
          rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
          · contradiction
          · rfl
          · exact Sym2.eq_swap
          · contradiction
      · rintro rfl
        rw [← h_e_eq]
        rw [mem_edgesIn]
        exact he
  rw [h_unique G1 h1, h_unique G2 h2]

lemma validPeel_peelIter_base (T : LabeledTree n) (S : Finset (Fin n)) (hS : 0 + 2 = S.card)
    (h_edges : (edgesIn T.graph S).card = S.card - 1) :
    ValidPeel T.graph (pruferPeelIter 0 T.graph S) S := by
  dsimp [pruferPeelIter, ValidPeel]
  refine ⟨by omega, ?_⟩
  rw [← Finset.card_pos]
  rw [h_edges, ← hS]
  decide

lemma pruferPeelStep_edge (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v a : Fin n)
    (h_sl : smallestLeaf G S = some v) (h_ln : leafNeighbor G S v = some a) :
    s(v, a) ∈ edgesIn G S := by
  rw [mem_edgesIn]
  dsimp [smallestLeaf] at h_sl
  split_ifs at h_sl with hne
  injection h_sl with hv_eq
  subst hv_eq
  have hv_mem := (Finset.mem_filter.mp (Finset.min'_mem _ hne)).1
  dsimp [leafNeighbor] at h_ln
  split_ifs at h_ln with hne2
  injection h_ln with ha_eq
  have ha_mem := (Finset.mem_filter.mp (Finset.min'_mem _ hne2)).1
  have ha_adj := (Finset.mem_filter.mp (Finset.min'_mem _ hne2)).2
  subst ha_eq
  refine ⟨by rw [SimpleGraph.mem_edgeFinset]; exact ha_adj, ?_⟩
  intro x hx
  simp only [Sym2.mem_iff] at hx
  rcases hx with rfl | rfl <;> assumption

lemma validPeel_peelIter_step (T : LabeledTree n) (m : ℕ)
    (S : Finset (Fin n)) (hS : m + 1 + 2 = S.card)
    (w a : Fin n) (hw : smallestLeaf T.graph S = some w) (ha : leafNeighbor T.graph S w = some a)
    (h_step : pruferPeelStep T.graph S = (some a, S.erase w))
    (h_len : (pruferPeelIter m T.graph (S.erase w)).length = m)
    (ih : ValidPeel T.graph (pruferPeelIter m T.graph (S.erase w)) (S.erase w))
    (h_leaf_eq : (pruferLeaves n S (a :: pruferPeelIter m T.graph (S.erase w))).min'
      (pruferLeaves_nonempty (by rw [List.length_cons, h_len]; omega)) = w) :
    ValidPeel T.graph (pruferPeelIter (m + 1) T.graph S) S := by
  dsimp [pruferPeelIter]
  rw [h_step]
  dsimp [ValidPeel]
  split_ifs with hS_card
  · refine ⟨?_, ?_⟩
    · have h_edge := pruferPeelStep_edge T.graph S w a hw ha
      rw [h_leaf_eq]
      exact h_edge
    · rw [h_leaf_eq]
      exact ih
  · exfalso
    rw [h_len] at hS_card
    omega

lemma decodeEdges_peelIter_base (T : LabeledTree n) (S : Finset (Fin n)) (hS : S.card = 2)
    (h_nonempty : (edgesIn T.graph S).Nonempty) :
    decodeEdges n (pruferPeelIter 0 T.graph S) S ⊆ edgesIn T.graph S := by
  dsimp [pruferPeelIter]
  exact decodeEdges_nil_sub T.graph S hS h_nonempty

lemma decodeEdges_peelIter_step (T : LabeledTree n) (m : ℕ)
    (S : Finset (Fin n)) (hS : m + 1 + 2 = S.card)
    (w a : Fin n) (hw : smallestLeaf T.graph S = some w) (ha : leafNeighbor T.graph S w = some a)
    (h_step : pruferPeelStep T.graph S = (some a, S.erase w))
    (h_len : (pruferPeelIter m T.graph (S.erase w)).length = m)
    (ih : decodeEdges n (pruferPeelIter m T.graph (S.erase w)) (S.erase w) ⊆ edgesIn T.graph (S.erase w))
    (h_leaf_eq : (pruferLeaves n S (a :: pruferPeelIter m T.graph (S.erase w))).min'
      (pruferLeaves_nonempty (by rw [List.length_cons, h_len]; omega)) = w) :
    decodeEdges n (pruferPeelIter (m + 1) T.graph S) S ⊆ edgesIn T.graph S := by
  dsimp [pruferPeelIter]
  rw [h_step]
  have h_dec : decodeEdges n (a :: pruferPeelIter m T.graph (S.erase w)) S =
      insert s(w, a) (decodeEdges n (pruferPeelIter m T.graph (S.erase w)) (S.erase w)) := by
    have h_cons := decodeEdges_cons n a (pruferPeelIter m T.graph (S.erase w)) S
      (by rw [h_len]; omega)
      ((pruferLeaves n S (a :: pruferPeelIter m T.graph (S.erase w))).min'
        (pruferLeaves_nonempty (by rw [List.length_cons, h_len]; omega)))
      rfl
    rw [h_leaf_eq] at h_cons
    exact h_cons
  rw [h_dec]
  have h_edge := pruferPeelStep_edge T.graph S w a hw ha
  exact step_sub T.graph S w a h_edge ih

lemma decodeEdges_nil_sub_tree (T : LabeledTree n) (S : Finset (Fin n)) (hS : S.card = 2)
    (h_nonempty : (edgesIn T.graph S).Nonempty) :
    decodeEdges n [] S ⊆ T.graph.edgeFinset := by
  have h_nil := decodeEdges_nil_sub T.graph S hS h_nonempty
  intro e he
  have := h_nil he
  rw [mem_edgesIn] at this
  exact this.1

lemma decodeEdges_cons_sub_tree (T : LabeledTree n) (m : ℕ)
    (S : Finset (Fin n)) (hS : m + 1 + 2 = S.card)
    (w a : Fin n) (hw : smallestLeaf T.graph S = some w) (ha : leafNeighbor T.graph S w = some a)
    (h_step : pruferPeelStep T.graph S = (some a, S.erase w))
    (h_len : (pruferPeelIter m T.graph (S.erase w)).length = m)
    (ih : decodeEdges n (pruferPeelIter m T.graph (S.erase w)) (S.erase w) ⊆ T.graph.edgeFinset)
    (h_leaf_eq : (pruferLeaves n S (a :: pruferPeelIter m T.graph (S.erase w))).min'
      (pruferLeaves_nonempty (by rw [List.length_cons, h_len]; omega)) = w) :
    decodeEdges n (pruferPeelIter (m + 1) T.graph S) S ⊆ T.graph.edgeFinset := by
  dsimp [pruferPeelIter]
  rw [h_step]
  have h_dec : decodeEdges n (a :: pruferPeelIter m T.graph (S.erase w)) S =
      insert s(w, a) (decodeEdges n (pruferPeelIter m T.graph (S.erase w)) (S.erase w)) := by
    have h_cons := decodeEdges_cons n a (pruferPeelIter m T.graph (S.erase w)) S
      (by rw [h_len]; omega)
      ((pruferLeaves n S (a :: pruferPeelIter m T.graph (S.erase w))).min'
        (pruferLeaves_nonempty (by rw [List.length_cons, h_len]; omega)))
      rfl
    rw [h_leaf_eq] at h_cons
    exact h_cons
  rw [h_dec]
  intro e he
  rw [Finset.mem_insert] at he
  rcases he with rfl | he_rest
  · have h_edge := pruferPeelStep_edge T.graph S w a hw ha
    rw [mem_edgesIn] at h_edge
    exact h_edge.1
  · exact ih he_rest

def ValidPeelIter (T : LabeledTree n) : ℕ → Finset (Fin n) → Prop
  | 0, S => S.card = 2 ∧ (edgesIn T.graph S).Nonempty
  | m + 1, S =>
    ∃ (hS : m + 1 + 2 = S.card) (w a : Fin n) (hw : smallestLeaf T.graph S = some w) (ha : leafNeighbor T.graph S w = some a),
      ∃ (h_len : (pruferPeelIter m T.graph (S.erase w)).length = m),
        (pruferLeaves n S (a :: pruferPeelIter m T.graph (S.erase w))).min'
          (pruferLeaves_nonempty (by rw [List.length_cons, h_len]; omega)) = w ∧
        ValidPeelIter T m (S.erase w)

lemma decodeEdges_of_validPeelIter (T : LabeledTree n) (k : ℕ) :
    ∀ (S : Finset (Fin n)), ValidPeelIter T k S →
    decodeEdges n (pruferPeelIter k T.graph S) S ⊆ T.graph.edgeFinset := by
  induction k with
  | zero =>
    intro S ⟨hS, h_nonempty⟩
    exact decodeEdges_nil_sub_tree T S hS h_nonempty
  | succ m ih =>
    intro S ⟨hS, w, a, hw, ha, h_len, h_leaf_eq, h_rest⟩
    have h_step : pruferPeelStep T.graph S = (some a, S.erase w) := by
      dsimp [pruferPeelStep]
      rw [hw]
      dsimp
      rw [ha]
    exact decodeEdges_cons_sub_tree T m S hS w a hw ha h_step h_len (ih (S.erase w) h_rest) h_leaf_eq


lemma labeledTree_2_unique (T1 T2 : LabeledTree 2) : T1 = T2 := by
  have h1 : T1.graph.edgeFinset.card = 1 := by
    have := T1.edge_card (by omega)
    rw [SimpleGraph.edgeFinset, Set.toFinset_card]
    omega
  have h2 : T2.graph.edgeFinset.card = 1 := by
    have := T2.edge_card (by omega)
    rw [SimpleGraph.edgeFinset, Set.toFinset_card]
    omega
  have h_edge (G : SimpleGraph (Fin 2)) (h : G.edgeFinset.card = 1) :
      G.edgeFinset = {s(⟨0, by omega⟩, ⟨1, by omega⟩)} := by
    obtain ⟨e, he⟩ := Finset.card_eq_one.mp h
    induction e using Sym2.inductionOn with
    | hf x y =>
      have hxy : x ≠ y := by
        have : s(x, y) ∈ G.edgeFinset := by rw [he]; exact Finset.mem_singleton_self _
        rw [SimpleGraph.mem_edgeFinset] at this
        exact this.ne
      have : s(x, y) = s(⟨0, by omega⟩, ⟨1, by omega⟩) := by
        fin_cases x <;> fin_cases y
        · contradiction
        · rfl
        · exact Sym2.eq_swap
        · contradiction
      rw [he, this]
  have h_finset : T1.graph.edgeFinset = T2.graph.edgeFinset := by
    rw [h_edge T1.graph h1, h_edge T2.graph h2]
  have h_graph : T1.graph = T2.graph := by
    ext u v
    simp only [← SimpleGraph.mem_edgeSet, ← Set.mem_toFinset]
    show s(u, v) ∈ T1.graph.edgeFinset ↔ s(u, v) ∈ T2.graph.edgeFinset
    rw [h_finset]
  exact LabeledTree.ext T1 T2 h_graph

lemma validPeel_pruferCode_2 (T : LabeledTree 2) :
    ValidPeel T.graph ((List.finRange (2 - 2)).map (fun i => (pruferCode T) ⟨i.val, i.isLt⟩)) Finset.univ := by
  dsimp [ValidPeel]
  refine ⟨by decide, ?_⟩
  rw [← Finset.card_pos]
  have h_edges : T.graph.edgeFinset.card = 1 := by
    have := T.edge_card (by omega)
    rw [SimpleGraph.edgeFinset, Set.toFinset_card]
    omega
  have h_in : edgesIn T.graph Finset.univ = T.graph.edgeFinset := by
    ext e
    simp [mem_edgesIn]
  rw [h_in, h_edges]
  decide


/-- Left inverse property: decoding the code of a tree recovers the original tree. -/
axiom prufer_left_inv (hn : 2 ≤ n) (T : LabeledTree n) :
    pruferDecode hn (pruferCode T) = T



/-- The Prüfer correspondence is a bijective equivalence between labeled trees and Prüfer sequences. -/
noncomputable def pruferEquiv (n : ℕ) (hn : 2 ≤ n) :
    LabeledTree n ≃ PruferSequence n where
  toFun := pruferCode
  invFun := pruferDecode hn
  left_inv := prufer_left_inv hn
  right_inv := prufer_right_inv hn

/--
**Cayley's Tree Formula (1889)**:
The number of labeled trees on $n \ge 2$ vertices is exactly $n^{n - 2}$.
-/
theorem cayleys_tree_formula (n : ℕ) (hn : 2 ≤ n) [Fintype (LabeledTree n)] :
    Fintype.card (LabeledTree n) = n ^ (n - 2) := by
  rw [Fintype.card_congr (pruferEquiv n hn)]
  exact PruferSequence.prufer_sequence_card n

/-- Concrete instance of Cayley's formula for $n = 2$: $2^{2-2} = 1$. -/
theorem cayley_n2 [Fintype (LabeledTree 2)] : Fintype.card (LabeledTree 2) = 1 := by
  have h := cayleys_tree_formula 2 (by norm_num)
  norm_num at h
  exact h

/-- Concrete instance of Cayley's formula for $n = 3$: $3^{3-2} = 3$. -/
theorem cayley_n3 [Fintype (LabeledTree 3)] : Fintype.card (LabeledTree 3) = 3 := by
  have h := cayleys_tree_formula 3 (by norm_num)
  norm_num at h
  exact h

/-- Concrete instance of Cayley's formula for $n = 4$: $4^{4-2} = 16$. -/
theorem cayley_n4 [Fintype (LabeledTree 4)] : Fintype.card (LabeledTree 4) = 16 := by
  have h := cayleys_tree_formula 4 (by norm_num)
  norm_num at h
  exact h

/-- A rooted labeled tree is a labeled tree equipped with a distinguished root vertex. -/
structure RootedTree (n : ℕ) where
  /-- The underlying labeled tree -/
  tree : LabeledTree n
  /-- The designated root vertex -/
  root : Fin n

/-- Canonical equivalence between rooted labeled trees and pairs `(T, v)`. -/
def rootedTreeEquiv (n : ℕ) : RootedTree n ≃ LabeledTree n × Fin n where
  toFun r := (r.tree, r.root)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/--
**Cayley's Rooted Tree Formula**:
The number of rooted labeled trees on $n \ge 2$ vertices is $n \cdot n^{n-2} = n^{n-1}$.
-/
theorem rooted_trees_count (n : ℕ) (hn : 2 ≤ n) [Fintype (LabeledTree n)] [Fintype (RootedTree n)] :
    Fintype.card (RootedTree n) = n ^ (n - 1) := by
  rw [Fintype.card_congr (rootedTreeEquiv n), Fintype.card_prod, Fintype.card_fin, cayleys_tree_formula n hn]
  have : n - 1 = (n - 2) + 1 := by omega
  rw [this, pow_succ, mul_comm]

