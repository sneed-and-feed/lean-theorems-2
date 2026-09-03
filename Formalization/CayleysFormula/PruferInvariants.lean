import Formalization.CayleysFormula.PruferEncode
import Formalization.CayleysFormula.PruferDecode
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

open Classical

/-!
# Prüfer Invariants: Vertex Degrees, Neighborhoods, and Leaf Sets

This module formalizes structural graph invariants connecting Prüfer sequence counts
with vertex degrees in labeled trees and simple graphs.
-/

variable {n : ℕ}

theorem exists_adj_of_reachable_ne {V : Type*} {G : SimpleGraph V} {u w : V}
    (h : G.Reachable u w) (hne : u ≠ w) : ∃ z, G.Adj u z := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => contradiction
  | cons hadj p' _ => exact ⟨_, hadj⟩

/-- The edges of graph G with both endpoints in S. -/
noncomputable def edgesIn (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  G.edgeFinset.filter (fun e => ∀ x ∈ e, x ∈ S)

@[simp] lemma mem_edgesIn (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (e : Sym2 (Fin n)) :
    e ∈ edgesIn G S ↔ e ∈ G.edgeFinset ∧ ∀ x ∈ e, x ∈ S :=
  Finset.mem_filter

lemma smallestLeaf_eq_some (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v : Fin n)
    (hv_mem : v ∈ S) (hv_card : (vertNeighbors G S v).card = 1)
    (h_all : ∀ u ∈ S, (vertNeighbors G S u).card = 1 → v ≤ u) :
    smallestLeaf G S = some v := by
  dsimp only [smallestLeaf]
  split_ifs with h
  · congr 1
    refine le_antisymm (Finset.min'_le _ v (by rw [Finset.mem_filter]; exact ⟨hv_mem, hv_card⟩)) ?_
    refine Finset.le_min' _ _ _ (fun u hu => ?_)
    rw [Finset.mem_filter] at hu
    exact h_all u hu.1 hu.2
  · have h_ne : (S.filter (fun v => (vertNeighbors G S v).card = 1)).Nonempty :=
      ⟨v, by rw [Finset.mem_filter]; exact ⟨hv_mem, hv_card⟩⟩
    contradiction

lemma minNeighbor_eq_some (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v a : Fin n)
    (h_adj : vertNeighbors G S v = {a}) :
    minNeighbor G S v = some a := by
  dsimp only [minNeighbor]
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

lemma leafNeighbor_eq_some (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v a : Fin n)
    (h_adj : vertNeighbors G S v = {a}) :
    leafNeighbor G S v = some a :=
  minNeighbor_eq_some G S v a h_adj

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

lemma edgesIn_erase_leaf_card (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v a : Fin n)
    (hv : v ∈ S) (ha : a ∈ S) (h_adj : S.filter (fun w => G.Adj v w) = {a}) :
    (edgesIn G (S.erase v)).card + 1 = (edgesIn G S).card := by
  have h_eq := edgesIn_erase_leaf G S v a hv ha h_adj
  have h_not_mem : s(v, a) ∉ edgesIn G (S.erase v) := by
    intro h_in
    rw [mem_edgesIn] at h_in
    have := h_in.2 v (Sym2.mem_mk_left v a)
    exact Finset.notMem_erase v S this
  rw [h_eq, Finset.card_insert_of_notMem h_not_mem]

lemma edgesIn_card_erase_leaf (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v a : Fin n)
    (hv : v ∈ S) (ha : a ∈ S) (h_adj : S.filter (fun w => G.Adj v w) = {a})
    (h_card : (edgesIn G S).card = S.card - 1) :
    (edgesIn G (S.erase v)).card = (S.erase v).card - 1 := by
  have h1 := edgesIn_erase_leaf_card G S v a hv ha h_adj
  rw [Finset.card_erase_of_mem hv]
  omega

def induceEraseIso (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (w : Fin n) (hwS : w ∈ S) :
    (G.induce (S : Set (Fin n))).induce {⟨w, hwS⟩}ᶜ ≃g G.induce ((S.erase w : Set (Fin n))) where
  toFun := fun ⟨⟨x, hxS⟩, hne⟩ => ⟨x, Finset.mem_erase.mpr ⟨fun h => hne (Subtype.ext h), hxS⟩⟩
  invFun := fun ⟨y, hy⟩ => ⟨⟨y, (Finset.mem_erase.mp hy).2⟩, fun h => (Finset.mem_erase.mp hy).1 (Subtype.ext_iff.mp h)⟩
  left_inv := by intro ⟨⟨x, hxS⟩, hne⟩; rfl
  right_inv := by intro ⟨y, hy⟩; rfl
  map_rel_iff' := by intro ⟨⟨x1, hx1⟩, hne1⟩ ⟨⟨x2, hx2⟩, hne2⟩; rfl

lemma degree_induce_eq_card_vertNeighbors (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (w : Fin n) (hw : w ∈ S) :
    (G.induce (S : Set (Fin n))).degree ⟨w, hw⟩ = (vertNeighbors G S w).card := by
  have h1 : (G.induce (S : Set (Fin n))).degree ⟨w, hw⟩ = ((G.induce (S : Set (Fin n))).neighborFinset ⟨w, hw⟩).card :=
    (SimpleGraph.card_neighborFinset_eq_degree (G.induce (S : Set (Fin n))) ⟨w, hw⟩).symm
  rw [h1]
  dsimp [vertNeighbors]
  apply Finset.card_bij (fun ⟨u, _⟩ _ => u)
  · intro ⟨u, huS⟩ hu_adj
    rw [Finset.mem_filter]
    rw [SimpleGraph.mem_neighborFinset, SimpleGraph.induce_adj] at hu_adj
    exact ⟨huS, hu_adj⟩
  · intro ⟨u1, hu1⟩ _ ⟨u2, hu2⟩ _ heq
    exact Subtype.ext heq
  · intro u hu
    rw [Finset.mem_filter] at hu
    refine ⟨⟨u, hu.1⟩, ?_, rfl⟩
    rw [SimpleGraph.mem_neighborFinset, SimpleGraph.induce_adj]
    exact hu.2

lemma isTree_has_leaf (T : LabeledTree n) (S : Finset (Fin n)) (hS : 2 ≤ S.card)
    (h_tree : (T.graph.induce (S : Set (Fin n))).IsTree) :
    ∃ w ∈ S, (vertNeighbors T.graph S w).card = 1 := by
  have h_nontriv : Nontrivial (S : Set (Fin n)) := by
    rw [← Fintype.one_lt_card_iff_nontrivial]
    have : Fintype.card (S : Set (Fin n)) = S.card := Fintype.card_coe S
    omega
  obtain ⟨⟨w, hw⟩, hdeg⟩ := @SimpleGraph.IsTree.exists_vert_degree_one_of_nontrivial _ _ _ h_nontriv _ h_tree
  refine ⟨w, hw, ?_⟩
  rw [← degree_induce_eq_card_vertNeighbors T.graph S w hw]
  exact hdeg

lemma isTree_erase_leaf (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (w : Fin n) (hwS : w ∈ S)
    (h_tree : (G.induce (S : Set (Fin n))).IsTree)
    (hw_deg : (vertNeighbors G S w).card = 1) :
    (G.induce ((S.erase w) : Set (Fin n))).IsTree := by
  have h_iso := induceEraseIso G S w hwS
  rw [← SimpleGraph.Iso.isTree_iff h_iso]
  refine ⟨?_, h_tree.isAcyclic.induce _⟩
  have hdeg : (G.induce (S : Set (Fin n))).degree ⟨w, hwS⟩ = 1 := by
    rw [degree_induce_eq_card_vertNeighbors G S w hwS, hw_deg]
  exact SimpleGraph.Connected.induce_compl_singleton_of_degree_eq_one h_tree.connected hdeg

lemma smallestLeaf_minNeighbor_of_isTree (T : LabeledTree n) (S : Finset (Fin n)) (hS : 2 ≤ S.card)
    (h_tree : (T.graph.induce (S : Set (Fin n))).IsTree) :
    ∃ (w a : Fin n), w ∈ S ∧ vertNeighbors T.graph S w = {a} ∧
      smallestLeaf T.graph S = some w ∧ minNeighbor T.graph S w = some a := by
  have ⟨w0, hw0S, hw0_deg⟩ := isTree_has_leaf T S hS h_tree
  have h_leaves_ne : (S.filter (fun v => (vertNeighbors T.graph S v).card = 1)).Nonempty := by
    refine ⟨w0, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨hw0S, hw0_deg⟩
  let w := (S.filter (fun v => (vertNeighbors T.graph S v).card = 1)).min' h_leaves_ne
  have hw_mem : w ∈ S.filter (fun v => (vertNeighbors T.graph S v).card = 1) :=
    Finset.min'_mem _ h_leaves_ne
  rw [Finset.mem_filter] at hw_mem
  have hwS : w ∈ S := hw_mem.1
  have hw_card : (vertNeighbors T.graph S w).card = 1 := hw_mem.2
  have h_sl : smallestLeaf T.graph S = some w := by
    dsimp [smallestLeaf]
    split_ifs
    · rfl
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hw_card
  have h_ln : minNeighbor T.graph S w = some a := by
    exact minNeighbor_eq_some T.graph S w a ha
  exact ⟨w, a, hwS, ha, h_sl, h_ln⟩

lemma smallestLeaf_leafNeighbor_of_isTree (T : LabeledTree n) (S : Finset (Fin n)) (hS : 2 ≤ S.card)
    (h_tree : (T.graph.induce (S : Set (Fin n))).IsTree) :
    ∃ (w a : Fin n), w ∈ S ∧ vertNeighbors T.graph S w = {a} ∧
      smallestLeaf T.graph S = some w ∧ leafNeighbor T.graph S w = some a :=
  smallestLeaf_minNeighbor_of_isTree T S hS h_tree

lemma vertNeighbors_erase (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (w a : Fin n) :
    vertNeighbors G (S.erase w) a = (vertNeighbors G S a).erase w := by
  ext z; simp only [mem_vertNeighbors, Finset.mem_erase]; tauto

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
  have h_eq : vertNeighbors G (S.erase w) u = vertNeighbors G S u := by
    ext z
    simp only [mem_vertNeighbors, Finset.mem_erase]
    constructor
    · rintro ⟨⟨_, hzS⟩, hadj⟩; exact ⟨hzS, hadj⟩
    · rintro ⟨hzS, hadj⟩
      refine ⟨⟨?_, hzS⟩, hadj⟩
      rintro rfl
      exact h_not_adj hadj
  rw [h_eq]

lemma card_vertNeighbors_step (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (w a : Fin n) (hwS : w ∈ S) (hw_adj : vertNeighbors G S w = {a})
    (L' : List (Fin n)) (h_rest_sub : ∀ x ∈ L', x ∈ S.erase w)
    (ih : ∀ u ∈ S.erase w, (vertNeighbors G (S.erase w) u).card = 1 + L'.count u) :
    ∀ u ∈ S, (vertNeighbors G S u).card = 1 + (a :: L').count u := by
  intro u huS
  have haS : a ∈ S := by
    have : a ∈ vertNeighbors G S w := by rw [hw_adj]; exact Finset.mem_singleton_self a
    rw [mem_vertNeighbors] at this
    exact this.1
  have hwa : w ≠ a := by
    intro h
    have : a ∈ vertNeighbors G S w := by rw [hw_adj]; exact Finset.mem_singleton_self a
    rw [h] at this
    rw [mem_vertNeighbors] at this
    exact this.2.ne rfl
  by_cases huw : u = w
  · rw [huw, hw_adj, Finset.card_singleton]
    have hw_not_in : w ∉ a :: L' := by
      intro h_in
      cases List.mem_cons.mp h_in with
      | inl heq => exact hwa heq
      | inr hmem =>
        have := h_rest_sub w hmem
        rw [Finset.mem_erase] at this
        exact this.1 rfl
    rw [List.count_eq_zero.mpr hw_not_in, add_zero]
  · have hu_erase : u ∈ S.erase w := Finset.mem_erase.mpr ⟨huw, huS⟩
    by_cases hua : u = a
    · rw [hua]
      have hw_in_a : w ∈ vertNeighbors G S a := by
        rw [mem_vertNeighbors]
        have : a ∈ vertNeighbors G S w := by rw [hw_adj]; exact Finset.mem_singleton_self a
        rw [mem_vertNeighbors] at this
        exact ⟨hwS, this.2.symm⟩
      have h_erase_a : vertNeighbors G (S.erase w) a = (vertNeighbors G S a).erase w :=
        vertNeighbors_erase G S w a
      have h_card_a : (vertNeighbors G (S.erase w) a).card + 1 = (vertNeighbors G S a).card := by
        rw [h_erase_a]
        exact Finset.card_erase_add_one hw_in_a
      have h_ih_a := ih a (Finset.mem_erase.mpr ⟨Ne.symm hwa, haS⟩)
      rw [List.count_cons_self]
      omega
    · have h_card_u := card_vertNeighbors_erase_of_leaf G S w a u hw_adj huS hua
      have h_ih_u := ih u hu_erase
      rw [List.count_cons_of_ne (Ne.symm hua)]
      omega

lemma min'_congr {α : Type*} [LinearOrder α] {A B : Finset α} (h : A = B) (hA : A.Nonempty) (hB : B.Nonempty) :
    A.min' hA = B.min' hB := by
  subst h; rfl

lemma leaves_eq_pruferLeaves (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (L : List (Fin n))
    (h_deg : ∀ u ∈ S, (vertNeighbors G S u).card = 1 + L.count u) :
    S.filter (fun v => (vertNeighbors G S v).card = 1) = pruferLeaves n S L := by
  dsimp [pruferLeaves]
  ext v
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hvS, hcard⟩
    refine ⟨hvS, ?_⟩
    have h_eq := h_deg v hvS
    rw [hcard] at h_eq
    intro h_in
    have : 1 ≤ L.count v := List.count_pos_iff.mpr h_in
    omega
  · rintro ⟨hvS, h_not_in⟩
    have h_cnt : L.count v = 0 := List.count_eq_zero.mpr h_not_in
    have h_eq := h_deg v hvS
    rw [h_cnt, add_zero] at h_eq
    exact ⟨hvS, h_eq⟩

lemma smallestLeaf_eq_pruferLeaves_min (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (L : List (Fin n))
    (h_deg : ∀ u ∈ S, (vertNeighbors G S u).card = 1 + L.count u)
    (hS : L.length + 2 ≤ S.card) :
    let h_ne : (pruferLeaves n S L).Nonempty := pruferLeaves_nonempty hS
    smallestLeaf G S = some ((pruferLeaves n S L).min' h_ne) := by
  intro h_ne
  dsimp [smallestLeaf]
  have h_leaves : S.filter (fun v => (vertNeighbors G S v).card = 1) = pruferLeaves n S L :=
    leaves_eq_pruferLeaves G S L h_deg
  split_ifs with h_nonempty
  · congr 1
    exact min'_congr h_leaves h_nonempty h_ne
  · rw [h_leaves] at h_nonempty
    contradiction

lemma card_vertNeighbors_base (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (hS : S.card = 2) (h_edges : (edgesIn G S).card = 1) :
    ∀ u ∈ S, (vertNeighbors G S u).card = 1 := by
  intro u huS
  have h_sub : vertNeighbors G S u ⊆ S.erase u := by
    intro z hz
    rw [mem_vertNeighbors] at hz
    rw [Finset.mem_erase]
    exact ⟨hz.2.ne.symm, hz.1⟩
  have h_le : (vertNeighbors G S u).card ≤ 1 := by
    have := Finset.card_le_card h_sub
    rw [Finset.card_erase_of_mem huS, hS] at this
    omega
  obtain ⟨e, he⟩ := Finset.card_pos.mp (by omega : 0 < (edgesIn G S).card)
  rw [mem_edgesIn] at he
  induction e using Sym2.inductionOn with
  | hf x y =>
    have hadj : G.Adj x y := by simpa using he.1
    have hxS := he.2 x (by simp)
    have hyS := he.2 y (by simp)
    have h_ne : x ≠ y := hadj.ne
    have h_pair_sub : ({x, y} : Finset (Fin n)) ⊆ S := by
      intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz; rcases hz with rfl | rfl <;> assumption
    have h_pair_card : ({x, y} : Finset (Fin n)).card = 2 := Finset.card_pair h_ne
    have hS_eq : ({x, y} : Finset (Fin n)) = S := Finset.eq_of_subset_of_card_le h_pair_sub (by rw [h_pair_card, hS])
    have hu_mem : u ∈ ({x, y} : Finset (Fin n)) := by rw [hS_eq]; exact huS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu_mem
    have : (vertNeighbors G S u).Nonempty := by
      rcases hu_mem with rfl | rfl
      · exact ⟨y, by rw [mem_vertNeighbors]; exact ⟨hyS, hadj⟩⟩
      · exact ⟨x, by rw [mem_vertNeighbors]; exact ⟨hxS, hadj.symm⟩⟩
    have := Finset.card_pos.mpr this
    omega

lemma edgesIn_erase_leaf_sub (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v a : Fin n)
    (h_va : s(v, a) ∈ edgesIn G S) :
    insert s(v, a) (edgesIn G (S.erase v)) ⊆ edgesIn G S := by
  intro e he
  rw [Finset.mem_insert] at he
  rcases he with rfl | he_rest
  · exact h_va
  · rw [mem_edgesIn] at he_rest ⊢
    refine ⟨he_rest.1, fun x hx => ?_⟩
    exact Finset.mem_of_mem_erase (he_rest.2 x hx)

lemma decodeEdges_nil_sub (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (hS : S.card = 2)
    (h_nonempty : (edgesIn G S).Nonempty) :
    decodeEdges n [] S ⊆ edgesIn G S := by
  dsimp [decodeEdges]
  split_ifs
  let u := S.min' (Finset.card_pos.mp (by omega))
  let w := (S.erase u).min' (Finset.card_pos.mp (by rw [Finset.card_erase_of_mem (Finset.min'_mem _ _)]; omega))
  have hu : u ∈ S := Finset.min'_mem _ _
  have hw_erase : w ∈ S.erase u := Finset.min'_mem _ _
  rw [Finset.mem_erase] at hw_erase
  have hw : w ∈ S := hw_erase.2
  have huw : u ≠ w := hw_erase.1.symm
  have h_pair_card : ({u, w} : Finset (Fin n)).card = 2 := Finset.card_pair huw
  have h_pair_sub : ({u, w} : Finset (Fin n)) ⊆ S := by
    intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz; rcases hz with rfl | rfl <;> assumption
  have hS_eq : ({u, w} : Finset (Fin n)) = S := Finset.eq_of_subset_of_card_le h_pair_sub (by rw [h_pair_card, hS])
  obtain ⟨e, he⟩ := h_nonempty
  rw [mem_edgesIn] at he
  induction e using Sym2.inductionOn with
  | hf x y =>
    have hadj : G.Adj x y := by simpa using he.1
    have hxS := he.2 x (by simp)
    have hyS := he.2 y (by simp)
    have hxy : x ≠ y := hadj.ne
    have hx_pair : x ∈ ({u, w} : Finset (Fin n)) := by rw [hS_eq]; exact hxS
    have hy_pair : y ∈ ({u, w} : Finset (Fin n)) := by rw [hS_eq]; exact hyS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx_pair hy_pair
    have h_eq : s(u, w) = s(x, y) := by
      rcases hx_pair with rfl | rfl <;> rcases hy_pair with rfl | rfl
      · exact False.elim (hxy rfl)
      · rfl
      · exact Sym2.eq_swap
      · exact False.elim (hxy rfl)
    intro z hz
    rw [Finset.mem_singleton] at hz
    subst hz
    rw [h_eq, mem_edgesIn]
    exact he
