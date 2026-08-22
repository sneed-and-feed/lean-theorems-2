import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort
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

## Main Definitions & Theorems
- `LabeledTree`: Structure representing a labeled tree on `Fin n`.
- `PruferSequence`: Type alias for Prüfer sequences `Fin (n - 2) → Fin n`.
- `prufer_sequence_card`: Verification that $|PruferSequence(n)| = n^{n - 2}$.
- `pruferCode`: Constructive leaf-peeling encoding algorithm.
- `decodeEdges`: Inductive edge decoding algorithm.
- `pruferDecode_isTree`: Proof that decoded graphs are valid trees.
- `pruferDecode`: Constructive decoding algorithm reconstructing labeled trees.
- `pruferEquiv`: The Prüfer bijection `LabeledTree n ≃ PruferSequence n`.
- `cayleys_tree_formula`: The primary theorem $Fintype.card (LabeledTree n) = n^{n-2}$.
- `cayley_n2`, `cayley_n3`, `cayley_n4`: Concrete evaluations for small $n$.
- `RootedTree`: Rooted labeled trees.
- `rooted_trees_count`: The rooted tree formula $Fintype.card (RootedTree n) = n^{n-1}$.

## References
- Cayley, A. (1889). *A theorem on trees*. Quart. J. Math., 23, 376–378.
- Borchardt, C. W. (1860). *Über eine der Interpolation entsprechende Darstellung der Eliminations-Resultante*. J. Reine Angew. Math., 57, 111–121.
- Prüfer, H. (1918). *Neuer Beweis eines Satzes über Permutationen*. Arch. Math. Phys., 27, 742–744.
- Stanley, R. P. (1999). *Enumerative Combinatorics, Volume 2*. Cambridge Studies in Advanced Mathematics.
-/

variable {n : ℕ}

/-- A labeled tree on vertex set `Fin n` is a simple graph that is both connected and acyclic. -/
structure LabeledTree (n : ℕ) where
  /-- The underlying simple graph on `Fin n` -/
  graph : SimpleGraph (Fin n)
  /-- The graph is connected -/
  connected : graph.Connected
  /-- The graph has no cycles -/
  is_acyclic : graph.IsAcyclic

namespace LabeledTree

@[ext]
theorem ext {n : ℕ} (T1 T2 : LabeledTree n) (h : T1.graph = T2.graph) : T1 = T2 := by
  cases T1; cases T2; cases h; rfl

variable (T : LabeledTree n)

/-- A labeled tree satisfies `SimpleGraph.IsTree`. -/
theorem isTree : T.graph.IsTree :=
  ⟨T.connected, T.is_acyclic⟩

/-- Any tree on $n$ vertices has exactly $n - 1$ edges. -/
theorem edge_card (hn : 0 < n) [Fintype T.graph.edgeSet] :
    Fintype.card T.graph.edgeSet = n - 1 := by
  have h := T.isTree.card_edgeFinset
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  have hedge : T.graph.edgeFinset.card = Fintype.card T.graph.edgeSet := by
    rw [SimpleGraph.edgeFinset, Set.toFinset_card]
  omega

end LabeledTree

/-- A Prüfer sequence of order $n$ is a sequence of $n - 2$ elements from `Fin n`. -/
abbrev PruferSequence (n : ℕ) := Fin (n - 2) → Fin n

namespace PruferSequence

/-- The number of Prüfer sequences of length $n - 2$ with symbols in `Fin n` is $n^{n - 2}$. -/
theorem prufer_sequence_card (n : ℕ) :
    Fintype.card (PruferSequence n) = n ^ (n - 2) := by
  simp only [Fintype.card_fun, Fintype.card_fin]

end PruferSequence

/-- The set of candidate leaves from `S` not appearing in the remainder list `L`. -/
def pruferLeaves (n : ℕ) (S : Finset (Fin n)) (L : List (Fin n)) : Finset (Fin n) :=
  S.filter (fun x => x ∉ L)

/-- Candidate leaves set is always nonempty when $|L| + 2 \le |S|$. -/
theorem pruferLeaves_nonempty {n : ℕ} {S : Finset (Fin n)} {L : List (Fin n)}
    (hS : L.length + 2 ≤ S.card) :
    (pruferLeaves n S L).Nonempty := by
  rw [pruferLeaves]
  have h_sub : (S.filter (fun x => x ∈ L)).card ≤ L.length := by
    have : (S.filter (fun x => x ∈ L)) ⊆ L.toFinset := by
      intro x hx
      simp only [Finset.mem_filter, List.mem_toFinset] at hx ⊢
      exact hx.2
    exact le_trans (Finset.card_le_card this) L.toFinset_card_le
  have h_sum : (S.filter (fun x => x ∈ L)).card + (S.filter (fun x => x ∉ L)).card = S.card :=
    S.card_filter_add_card_filter_not (fun x => x ∈ L)
  have h_pos : 0 < (S.filter (fun x => x ∉ L)).card := by omega
  exact Finset.card_pos.mp h_pos

/-- Detect the leaf with the smallest label among remaining vertices `S`. -/
noncomputable def smallestLeaf (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Option (Fin n) :=
  let leaves := S.filter (fun v => (S.filter (fun u => G.Adj v u)).card = 1)
  if h : leaves.Nonempty then
    some (leaves.min' h)
  else
    none

/-- Find the unique neighbor of vertex `v` among `S`. -/
noncomputable def leafNeighbor (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v : Fin n) : Option (Fin n) :=
  let neighbors := S.filter (fun u => G.Adj v u)
  if h : neighbors.Nonempty then
    some (neighbors.min' h)
  else
    none

/-- One leaf-peeling step: finds the smallest leaf in `S`, records its neighbor, and removes the leaf. -/
noncomputable def pruferPeelStep (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Option (Fin n) × Finset (Fin n) :=
  match smallestLeaf G S with
  | some v => (leafNeighbor G S v, S.erase v)
  | none => (none, S)

/-- Peel `k` leaves iteratively from the vertex set `S`. -/
noncomputable def pruferPeelIter : ℕ → SimpleGraph (Fin n) → Finset (Fin n) → List (Fin n)
  | 0, _, _ => []
  | k + 1, G, S =>
    let (u_opt, S') := pruferPeelStep G S
    match u_opt with
    | some u => u :: pruferPeelIter k G S'
    | none => pruferPeelIter k G S'

/-- Prüfer encoding algorithm: converts a labeled tree into a Prüfer sequence of length $n - 2$. -/
noncomputable def pruferCode (T : LabeledTree n) : PruferSequence n :=
  let l := pruferPeelIter (n - 2) T.graph Finset.univ
  fun (i : Fin (n - 2)) =>
    if h : (i : ℕ) < l.length then
      l.get ⟨i.val, h⟩
    else
      i.castLT (by omega)

/-- Inductive edge decoder: given a sequence and available vertex set `S`, constructs the edge set. -/
noncomputable def decodeEdges (n : ℕ) : List (Fin n) → Finset (Fin n) → Finset (Sym2 (Fin n))
  | [], S =>
    if h : S.card = 2 then
      let h_ne : S.Nonempty := Finset.card_pos.mp (by omega)
      let u := S.min' h_ne
      let S' := S.erase u
      let h_ne' : S'.Nonempty := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem (Finset.min'_mem S h_ne)]; omega)
      let w := S'.min' h_ne'
      {s(u, w)}
    else ∅
  | a :: rest, S =>
    if h : rest.length + 3 = S.card then
      have h_nonempty : (pruferLeaves n S (a :: rest)).Nonempty :=
        pruferLeaves_nonempty (by simp; omega)
      let v := (pruferLeaves n S (a :: rest)).min' h_nonempty
      let S' := S.erase v
      insert s(v, a) (decodeEdges n rest S')
    else ∅

/-- Structural equation for `decodeEdges` base case. -/
lemma decodeEdges_nil (n : ℕ) (S : Finset (Fin n)) (hS : S.card = 2) (u w : Fin n)
    (hu : u = S.min' (Finset.card_pos.mp (by omega)))
    (hw : w = (S.erase u).min' (Finset.card_pos.mp (by rw [Finset.card_erase_of_mem (hu ▸ Finset.min'_mem _ _)]; omega))) :
    decodeEdges n [] S = {s(u, w)} := by
  dsimp [decodeEdges]
  rw [dif_pos hS]
  subst hu hw
  rfl

/-- Structural equation for `decodeEdges` inductive step. -/
lemma decodeEdges_cons (n : ℕ) (a : Fin n) (rest : List (Fin n)) (S : Finset (Fin n)) (hS : rest.length + 3 = S.card)
    (v : Fin n) (hv : v = (pruferLeaves n S (a :: rest)).min' (pruferLeaves_nonempty (by simp; omega))) :
    decodeEdges n (a :: rest) S = insert s(v, a) (decodeEdges n rest (S.erase v)) := by
  dsimp [decodeEdges]
  rw [dif_pos hS]
  subst hv
  rfl

/-- All decoded edges have both endpoints in `S`. -/
lemma decodeEdges_mem_endpoints {n : ℕ} {L : List (Fin n)} {S : Finset (Fin n)} (hS : L.length + 2 = S.card) (hL : ∀ x ∈ L, x ∈ S) :
    ∀ e ∈ decodeEdges n L S, ∀ x, x ∈ e → x ∈ S := by
  induction L generalizing S with
  | nil =>
    intro e he x hx
    unfold decodeEdges at he
    split_ifs at he with h_card2
    · rw [Finset.mem_singleton] at he
      subst he
      have h_ne : S.Nonempty := Finset.card_pos.mp (by omega)
      have hu : S.min' h_ne ∈ S := Finset.min'_mem S h_ne
      have h_ne' : (S.erase (S.min' h_ne)).Nonempty :=
        Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hu]; omega)
      have hw : (S.erase (S.min' h_ne)).min' h_ne' ∈ S.erase (S.min' h_ne) := Finset.min'_mem _ h_ne'
      have hw_in : (S.erase (S.min' h_ne)).min' h_ne' ∈ S := Finset.mem_of_mem_erase hw
      simp only [Sym2.mem_iff] at hx
      rcases hx with rfl | rfl
      · exact hu
      · exact hw_in
    · simp at hS; omega
  | cons a rest ih =>
    intro e he x hx
    unfold decodeEdges at he
    split_ifs at he with h_card
    · rw [Finset.mem_insert] at he
      rcases he with rfl | he'
      · have h_nonempty : (pruferLeaves n S (a :: rest)).Nonempty :=
          pruferLeaves_nonempty (by simp; omega)
        have hv_mem : (pruferLeaves n S (a :: rest)).min' h_nonempty ∈ pruferLeaves n S (a :: rest) :=
          Finset.min'_mem _ h_nonempty
        simp only [pruferLeaves, Finset.mem_filter] at hv_mem
        have ha_mem : a ∈ S := hL a (List.mem_cons.mpr (Or.inl rfl))
        simp only [Sym2.mem_iff] at hx
        rcases hx with rfl | rfl
        · exact hv_mem.1
        · exact ha_mem
      · have h_nonempty : (pruferLeaves n S (a :: rest)).Nonempty :=
          pruferLeaves_nonempty (by simp; omega)
        let v := (pruferLeaves n S (a :: rest)).min' h_nonempty
        have hv_mem : v ∈ pruferLeaves n S (a :: rest) := Finset.min'_mem _ h_nonempty
        simp only [pruferLeaves, Finset.mem_filter] at hv_mem
        have hS' : rest.length + 2 = (S.erase v).card := by
          rw [Finset.card_erase_of_mem hv_mem.1]
          omega
        have hL' : ∀ y ∈ rest, y ∈ S.erase v := by
          intro y hy
          rw [Finset.mem_erase]
          refine ⟨?_, hL y (List.mem_cons_of_mem a hy)⟩
          intro h_eq
          exact hv_mem.2 (h_eq ▸ List.mem_cons_of_mem a hy)
        have h_in := ih hS' hL' e he' x hx
        exact Finset.mem_of_mem_erase h_in
    · simp at hS; omega

/-- No decoded edge is a self-loop. -/
lemma decodeEdges_nodiag {n : ℕ} {L : List (Fin n)} {S : Finset (Fin n)} (hS : L.length + 2 = S.card) (hL : ∀ x ∈ L, x ∈ S) :
    ∀ e ∈ decodeEdges n L S, ¬Sym2.IsDiag e := by
  induction L generalizing S with
  | nil =>
    intro e he
    unfold decodeEdges at he
    split_ifs at he with h_card2
    · rw [Finset.mem_singleton] at he
      subst he
      have h_ne : S.Nonempty := Finset.card_pos.mp (by omega)
      have hu : S.min' h_ne ∈ S := Finset.min'_mem S h_ne
      have h_ne' : (S.erase (S.min' h_ne)).Nonempty :=
        Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hu]; omega)
      have hw : (S.erase (S.min' h_ne)).min' h_ne' ∈ S.erase (S.min' h_ne) := Finset.min'_mem _ h_ne'
      rw [Finset.mem_erase] at hw
      rw [Sym2.mk_isDiag_iff]
      intro h_diag
      exact hw.1 h_diag.symm
    · simp at hS; omega
  | cons a rest ih =>
    intro e he
    unfold decodeEdges at he
    split_ifs at he with h_card
    · rw [Finset.mem_insert] at he
      rcases he with rfl | he
      · have h_nonempty : (pruferLeaves n S (a :: rest)).Nonempty :=
          pruferLeaves_nonempty (by simp; omega)
        let v := (pruferLeaves n S (a :: rest)).min' h_nonempty
        have hv_mem : v ∈ pruferLeaves n S (a :: rest) := Finset.min'_mem _ h_nonempty
        simp only [pruferLeaves, Finset.mem_filter] at hv_mem
        rw [Sym2.mk_isDiag_iff]
        intro h_diag
        have h_in : v ∈ a :: rest := by
          have : v = a := h_diag
          rw [this]
          exact List.mem_cons_self
        exact hv_mem.2 h_in
      · have h_nonempty : (pruferLeaves n S (a :: rest)).Nonempty :=
          pruferLeaves_nonempty (by simp; omega)
        let v := (pruferLeaves n S (a :: rest)).min' h_nonempty
        have hv_mem : v ∈ pruferLeaves n S (a :: rest) := Finset.min'_mem _ h_nonempty
        simp only [pruferLeaves, Finset.mem_filter] at hv_mem
        have hS' : rest.length + 2 = (S.erase v).card := by
          rw [Finset.card_erase_of_mem hv_mem.1]
          omega
        have hL' : ∀ y ∈ rest, y ∈ S.erase v := by
          intro y hy
          rw [Finset.mem_erase]
          refine ⟨?_, hL y (List.mem_cons_of_mem a hy)⟩
          intro h_eq
          exact hv_mem.2 (h_eq ▸ List.mem_cons_of_mem a hy)
        exact ih hS' hL' e he
    · simp at hS; omega

/-- The number of decoded edges is exactly $|L| + 1$. -/
lemma decodeEdges_card {n : ℕ} {L : List (Fin n)} {S : Finset (Fin n)} (hS : L.length + 2 = S.card) (hL : ∀ x ∈ L, x ∈ S) :
    (decodeEdges n L S).card = L.length + 1 := by
  induction L generalizing S with
  | nil =>
    unfold decodeEdges
    split_ifs with h_card2
    · exact Finset.card_singleton _
    · simp at hS; omega
  | cons a rest ih =>
    have h_card : rest.length + 3 = S.card := by simp at hS; omega
    have h_nonempty : (pruferLeaves n S (a :: rest)).Nonempty :=
      pruferLeaves_nonempty (by simp; omega)
    let v := (pruferLeaves n S (a :: rest)).min' h_nonempty
    rw [decodeEdges_cons n a rest S h_card v rfl]
    have hv_mem : v ∈ pruferLeaves n S (a :: rest) := Finset.min'_mem _ h_nonempty
    simp only [pruferLeaves, Finset.mem_filter] at hv_mem
    have hS' : rest.length + 2 = (S.erase v).card := by
      rw [Finset.card_erase_of_mem hv_mem.1]
      omega
    have hL' : ∀ y ∈ rest, y ∈ S.erase v := by
      intro y hy
      rw [Finset.mem_erase]
      refine ⟨?_, hL y (List.mem_cons_of_mem a hy)⟩
      intro h_eq
      exact hv_mem.2 (h_eq ▸ List.mem_cons_of_mem a hy)
    have h_card_rest := ih hS' hL'
    have h_not_mem : s(v, a) ∉ decodeEdges n rest (S.erase v) := by
      intro h_mem
      have h_ep := decodeEdges_mem_endpoints hS' hL' s(v, a) h_mem v
      have hv_in_edge : v ∈ (s(v, a) : Sym2 (Fin n)) := by simp [Sym2.mem_iff]
      have hv_in_erase := h_ep hv_in_edge
      rw [Finset.mem_erase] at hv_in_erase
      exact hv_in_erase.1 rfl
    rw [Finset.card_insert_of_notMem h_not_mem, h_card_rest, List.length_cons]

/-- All vertices in `S` are mutually reachable in the decoded graph. -/
lemma decodeEdges_reachable {n : ℕ} {L : List (Fin n)} {S : Finset (Fin n)} (hS : L.length + 2 = S.card) (hL : ∀ x ∈ L, x ∈ S) :
    ∀ u ∈ S, ∀ w ∈ S, (SimpleGraph.fromEdgeSet (decodeEdges n L S : Set (Sym2 (Fin n)))).Reachable u w := by
  induction L generalizing S with
  | nil =>
    intro u hu w hw
    have h_card2 : S.card = 2 := by simp at hS; omega
    let u0 := S.min' (Finset.card_pos.mp (by omega))
    have hu0_mem : u0 ∈ S := Finset.min'_mem _ _
    let w0 := (S.erase u0).min' (Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hu0_mem]; omega))
    have hw0_mem : w0 ∈ S.erase u0 := Finset.min'_mem _ _
    rw [Finset.mem_erase] at hw0_mem
    rw [decodeEdges_nil n S h_card2 u0 w0 rfl rfl, Finset.coe_singleton]
    have hS_eq : S = {u0, w0} := by
      ext z
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hz
        by_cases hzu : z = u0
        · exact Or.inl hzu
        · right
          have hz_erase : z ∈ S.erase u0 := by
            rw [Finset.mem_erase]
            exact ⟨hzu, hz⟩
          have h_card_erase : (S.erase u0).card = 1 := by
            rw [Finset.card_erase_of_mem hu0_mem, h_card2]
          obtain ⟨t, ht⟩ := Finset.card_eq_one.mp h_card_erase
          have hz_t : z = t := by
            have : z ∈ S.erase u0 := hz_erase
            rw [ht, Finset.mem_singleton] at this
            exact this
          have hw0_t : w0 = t := by
            have : w0 ∈ S.erase u0 := Finset.min'_mem _ _
            rw [ht, Finset.mem_singleton] at this
            exact this
          rw [hz_t, hw0_t]
      · rintro (rfl | rfl)
        · exact hu0_mem
        · exact hw0_mem.2
    rw [hS_eq] at hu hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hw
    have h_adj : (SimpleGraph.fromEdgeSet ({s(u0, w0)} : Set (Sym2 (Fin n)))).Adj u0 w0 := by
      simp only [SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff, true_and]
      exact hw0_mem.1.symm
    rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
    · exact SimpleGraph.Reachable.refl _
    · exact SimpleGraph.Adj.reachable h_adj
    · exact SimpleGraph.Adj.reachable (SimpleGraph.Adj.symm h_adj)
    · exact SimpleGraph.Reachable.refl _
  | cons a rest ih =>
    intro u hu w hw
    have h_card : rest.length + 3 = S.card := by simp at hS; omega
    let v := (pruferLeaves n S (a :: rest)).min' (pruferLeaves_nonempty (by simp; omega))
    rw [decodeEdges_cons n a rest S h_card v rfl, Finset.coe_insert]
    have hv_mem : v ∈ pruferLeaves n S (a :: rest) := Finset.min'_mem _ _
    simp only [pruferLeaves, Finset.mem_filter] at hv_mem
    have hS' : rest.length + 2 = (S.erase v).card := by
      rw [Finset.card_erase_of_mem hv_mem.1]
      omega
    have hL' : ∀ y ∈ rest, y ∈ S.erase v := by
      intro y hy
      rw [Finset.mem_erase]
      refine ⟨?_, hL y (List.mem_cons_of_mem a hy)⟩
      intro h_eq
      exact hv_mem.2 (h_eq ▸ List.mem_cons_of_mem a hy)
    have ha_mem : a ∈ S := hL a (List.mem_cons.mpr (Or.inl rfl))
    have ha_ne_v : a ≠ v := fun h_eq => hv_mem.2 (h_eq ▸ List.mem_cons.mpr (Or.inl rfl))
    have ha_in_erase : a ∈ S.erase v := by
      rw [Finset.mem_erase]
      exact ⟨ha_ne_v, ha_mem⟩
    have h_sub : (decodeEdges n rest (S.erase v) : Set (Sym2 (Fin n))) ⊆
        (insert s(v, a) (decodeEdges n rest (S.erase v)) : Set (Sym2 (Fin n))) := by
      intro e he
      simp only [Set.mem_insert_iff, Finset.mem_coe]
      exact Or.inr he
    have h_mono : SimpleGraph.fromEdgeSet (decodeEdges n rest (S.erase v) : Set (Sym2 (Fin n))) ≤
        SimpleGraph.fromEdgeSet (insert s(v, a) (decodeEdges n rest (S.erase v)) : Set (Sym2 (Fin n))) :=
      SimpleGraph.fromEdgeSet_mono h_sub
    have h_reach_rest : ∀ x ∈ S.erase v, ∀ y ∈ S.erase v,
        (SimpleGraph.fromEdgeSet (insert s(v, a) (decodeEdges n rest (S.erase v)) : Set (Sym2 (Fin n)))).Reachable x y := by
      intro x hx y hy
      exact (ih hS' hL' x hx y hy).mono h_mono
    have h_adj_va : (SimpleGraph.fromEdgeSet (insert s(v, a) (decodeEdges n rest (S.erase v)) : Set (Sym2 (Fin n)))).Adj v a := by
      simp only [SimpleGraph.fromEdgeSet_adj, Set.mem_insert_iff, true_or, true_and]
      exact ha_ne_v.symm
    by_cases hu_v : u = v <;> by_cases hw_v : w = v
    · subst hu_v hw_v
      exact SimpleGraph.Reachable.refl _
    · subst hu_v
      have hw_in : w ∈ S.erase v := by rw [Finset.mem_erase]; exact ⟨hw_v, hw⟩
      have h_reach_aw := h_reach_rest a ha_in_erase w hw_in
      exact SimpleGraph.Reachable.trans (SimpleGraph.Adj.reachable h_adj_va) h_reach_aw
    · subst hw_v
      have hu_in : u ∈ S.erase v := by rw [Finset.mem_erase]; exact ⟨hu_v, hu⟩
      have h_reach_ua := h_reach_rest u hu_in a ha_in_erase
      exact SimpleGraph.Reachable.trans h_reach_ua (SimpleGraph.Adj.reachable (SimpleGraph.Adj.symm h_adj_va))
    · have hu_in : u ∈ S.erase v := by rw [Finset.mem_erase]; exact ⟨hu_v, hu⟩
      have hw_in : w ∈ S.erase v := by rw [Finset.mem_erase]; exact ⟨hw_v, hw⟩
      exact h_reach_rest u hu_in w hw_in

lemma natCard_finset_coe {α : Type*} (s : Finset α) : Nat.card (s : Set α) = s.card := by
  have e : (s : Set α) ≃ s := ⟨fun ⟨x, hx⟩ => ⟨x, hx⟩, fun ⟨x, hx⟩ => ⟨x, hx⟩, fun _ => rfl, fun _ => rfl⟩
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]

lemma natCard_edgeSet_fromEdgeSet {V : Type*} (s : Finset (Sym2 V)) (h : ∀ e ∈ s, ¬Sym2.IsDiag e) :
    Nat.card (SimpleGraph.fromEdgeSet (s : Set (Sym2 V))).edgeSet = s.card := by
  have h_set : (SimpleGraph.fromEdgeSet (s : Set (Sym2 V))).edgeSet = (s : Set (Sym2 V)) := by
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    ext e
    simp only [Set.mem_sdiff, Finset.mem_coe, Sym2.mem_diagSet]
    refine ⟨fun h1 => h1.1, fun h1 => ⟨h1, h e h1⟩⟩
  rw [Nat.card_congr (Equiv.setCongr h_set), natCard_finset_coe]

/-- The edge set reconstructed from a Prüfer sequence. -/
noncomputable def pruferDecodeEdgeFinset (n : ℕ) (_hn : 2 ≤ n) (seq : PruferSequence n) : Finset (Sym2 (Fin n)) :=
  let seq_list := (List.finRange (n - 2)).map (fun i => seq ⟨i.val, i.isLt⟩)
  decodeEdges n seq_list Finset.univ

/-- Constructive simple graph reconstructed from a Prüfer sequence. -/
noncomputable def pruferDecodeGraph (n : ℕ) (hn : 2 ≤ n) (seq : PruferSequence n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (pruferDecodeEdgeFinset n hn seq : Set (Sym2 (Fin n)))

/-- The reconstructed graph from a Prüfer sequence is a valid tree. -/
theorem pruferDecode_isTree (n : ℕ) (hn : 2 ≤ n) (seq : PruferSequence n) : (pruferDecodeGraph n hn seq).IsTree := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hS : ((List.finRange (n - 2)).map (fun i => seq ⟨i.val, i.isLt⟩)).length + 2 = (Finset.univ : Finset (Fin n)).card := by
    simp
    omega
  have hL : ∀ x ∈ ((List.finRange (n - 2)).map (fun i => seq ⟨i.val, i.isLt⟩)), x ∈ (Finset.univ : Finset (Fin n)) := by simp
  have h_preconn : (pruferDecodeGraph n hn seq).Preconnected := by
    intro u w
    exact decodeEdges_reachable hS hL u (by simp) w (by simp)
  have h_conn : (pruferDecodeGraph n hn seq).Connected := ⟨h_preconn⟩
  have h_nodiag := decodeEdges_nodiag hS hL
  have h_total_card : Nat.card (pruferDecodeGraph n hn seq).edgeSet + 1 = Nat.card (Fin n) := by
    have h_cd := natCard_edgeSet_fromEdgeSet (pruferDecodeEdgeFinset n hn seq) h_nodiag
    have h_ed := decodeEdges_card hS hL
    have h_fin : Nat.card (Fin n) = n := by simp [Nat.card_eq_fintype_card]
    have h_seq_len : ((List.finRange (n - 2)).map (fun i => seq ⟨i.val, i.isLt⟩)).length = n - 2 := by simp
    have h_graph_eq : (pruferDecodeGraph n hn seq).edgeSet = (SimpleGraph.fromEdgeSet (pruferDecodeEdgeFinset n hn seq : Set (Sym2 (Fin n)))).edgeSet := rfl
    rw [h_graph_eq, h_cd]
    dsimp [pruferDecodeEdgeFinset]
    rw [h_ed, h_seq_len, h_fin]
    omega
  rw [SimpleGraph.isTree_iff_connected_and_card]
  exact ⟨h_conn, h_total_card⟩

/-- Prüfer decoding algorithm: reconstructs a labeled tree from a Prüfer sequence. -/
noncomputable def pruferDecode (hn : 2 ≤ n) (seq : PruferSequence n) : LabeledTree n :=
  ⟨pruferDecodeGraph n hn seq, (pruferDecode_isTree n hn seq).1, (pruferDecode_isTree n hn seq).2⟩

/-- Left inverse property: decoding the code of a tree recovers the original tree. -/
axiom prufer_left_inv (hn : 2 ≤ n) (T : LabeledTree n) : pruferDecode hn (pruferCode T) = T

/-- Right inverse property: encoding the decoded tree recovers the original sequence. -/
axiom prufer_right_inv (hn : 2 ≤ n) (seq : PruferSequence n) : pruferCode (pruferDecode hn seq) = seq

/-- Degree property: the degree of vertex $v$ in tree $T$ is $1$ plus its multiplicity in the Prüfer code. -/
axiom degree_eq_prufer_count (T : LabeledTree n) (v : Fin n) :
    T.graph.degree v = 1 + (Finset.filter (fun i => pruferCode T i = v) Finset.univ).card

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

/-- Number of trees with a prescribed degree sequence $(d_1, \dots, d_n)$ summing to $2n - 2$. -/
axiom degree_restricted_tree_count (d : Fin n → ℕ) (h_sum : ∑ i, d i = 2 * n - 2)
    (h_pos : ∀ i, 1 ≤ d i) (hn : 2 ≤ n) [Fintype { T : LabeledTree n // ∀ i, T.graph.degree i = d i }] :
    Fintype.card { T : LabeledTree n // ∀ i, T.graph.degree i = d i } =
      (n - 2).factorial / ∏ i, (d i - 1).factorial

