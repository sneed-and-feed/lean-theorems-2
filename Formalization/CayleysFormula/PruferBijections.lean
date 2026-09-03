import Formalization.CayleysFormula.PruferEncode
import Formalization.CayleysFormula.PruferDecode
import Formalization.CayleysFormula.PruferInvariants
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Prüfer Bijections: Encoding and Decoding Inverses

This module formalizes both directions of the Prüfer correspondence:
1. `prufer_right_inv`: Encoding the decoded tree recovers the original Prüfer sequence.
2. `prufer_left_inv`: Decoding the encoded tree recovers the original labeled tree.
-/

variable {n : ℕ}

/-! ## Part 1: Right Inverse and Decoded Tree Peeling -/

lemma vertNeighbors_congr (G1 G2 : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v : Fin n)
    (h_adj : ∀ x ∈ S, G1.Adj v x ↔ G2.Adj v x) :
    S.filter (fun u => G1.Adj v u) = S.filter (fun u => G2.Adj v u) := by
  ext u; simp only [Finset.mem_filter]
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
    rcases List.mem_cons.mp hu with rfl | hu_rest
    · exact decodeEdges_degree_a_ge_two u rest S h_card3 hL
    · have h_ih := ih (S.erase v) h_card_rest hL_rest u hu_rest
      have h_sub : (decodeEdges n rest (S.erase v) : Set (Sym2 (Fin n))) ⊆
          (decodeEdges n (b :: rest) S : Set (Sym2 (Fin n))) := by
        have h_dec : decodeEdges n (b :: rest) S = insert s(v, b) (decodeEdges n rest (S.erase v)) :=
          decodeEdges_cons n b rest S h_card3 v rfl
        rw [h_dec, Finset.coe_insert]
        exact Set.subset_insert _ _
      have h_mono := SimpleGraph.fromEdgeSet_mono h_sub
      have h_subset : vertNeighbors (SimpleGraph.fromEdgeSet (decodeEdges n rest (S.erase v) : Set (Sym2 (Fin n)))) (S.erase v) u ⊆
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

/-! ## Part 2: Left Inverse and Decoded Tree Reconstruction -/

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

lemma validPeelIter_all (T : LabeledTree n) (k : ℕ) :
    ∀ (S : Finset (Fin n)), k + 2 = S.card →
      (T.graph.induce (S : Set (Fin n))).IsTree →
      (edgesIn T.graph S).card = S.card - 1 →
      ValidPeelIter T k S ∧
      (pruferPeelIter k T.graph S).length = k ∧
      (∀ x ∈ pruferPeelIter k T.graph S, x ∈ S) ∧
      (∀ u ∈ S, (vertNeighbors T.graph S u).card = 1 + (pruferPeelIter k T.graph S).count u) := by
  induction k with
  | zero =>
    intro S hS _ h_edges
    have hS2 : S.card = 2 := by omega
    have h_edges1 : (edgesIn T.graph S).card = 1 := by omega
    have h_nonempty : (edgesIn T.graph S).Nonempty := Finset.card_pos.mp (by omega)
    refine ⟨⟨hS2, h_nonempty⟩, rfl, ?_, ?_⟩
    · intro x hx
      dsimp [pruferPeelIter] at hx
      cases hx
    · intro u huS
      rw [pruferPeelIter, List.count_nil, add_zero]
      exact card_vertNeighbors_base T.graph S hS2 h_edges1 u huS
  | succ m ih =>
    intro S hS h_tree h_edges
    have hS_ge2 : 2 ≤ S.card := by omega
    obtain ⟨w, a, hwS, hw_adj, hw, ha⟩ := smallestLeaf_leafNeighbor_of_isTree T S hS_ge2 h_tree
    have h_step : pruferPeelStep T.graph S = (some a, S.erase w) := by
      dsimp [pruferPeelStep]
      rw [hw]
      dsimp
      rw [ha]
    have h_iter : pruferPeelIter (m + 1) T.graph S = a :: pruferPeelIter m T.graph (S.erase w) := by
      dsimp [pruferPeelIter]
      rw [h_step]
    have hS' : m + 2 = (S.erase w).card := by
      rw [Finset.card_erase_of_mem hwS]
      omega
    have h_tree' : (T.graph.induce ((S.erase w) : Set (Fin n))).IsTree :=
      isTree_erase_leaf T.graph S w hwS h_tree (by rw [hw_adj, Finset.card_singleton])
    have haS : a ∈ S := by
      have : a ∈ vertNeighbors T.graph S w := by rw [hw_adj]; exact Finset.mem_singleton_self a
      rw [mem_vertNeighbors] at this
      exact this.1
    have h_edges' : (edgesIn T.graph (S.erase w)).card = (S.erase w).card - 1 :=
      edgesIn_card_erase_leaf T.graph S w a hwS haS hw_adj h_edges
    obtain ⟨ih_valid, ih_len, ih_sub, ih_deg⟩ := ih (S.erase w) hS' h_tree' h_edges'
    have h_deg_all : ∀ u ∈ S, (vertNeighbors T.graph S u).card = 1 + (a :: pruferPeelIter m T.graph (S.erase w)).count u :=
      card_vertNeighbors_step T.graph S w a hwS hw_adj (pruferPeelIter m T.graph (S.erase w)) ih_sub ih_deg
    have h_leaf_eq : (pruferLeaves n S (a :: pruferPeelIter m T.graph (S.erase w))).min'
        (pruferLeaves_nonempty (by rw [List.length_cons, ih_len]; omega)) = w := by
      have h_min := smallestLeaf_eq_pruferLeaves_min T.graph S (a :: pruferPeelIter m T.graph (S.erase w))
        h_deg_all (by rw [List.length_cons, ih_len]; omega)
      rw [hw] at h_min
      injection h_min with h_eq
      exact h_eq.symm
    have h_valid : ValidPeelIter T (m + 1) S := by
      dsimp [ValidPeelIter]
      refine ⟨hS, w, a, hw, ha, ih_len, h_leaf_eq, ih_valid⟩
    have h_len : (pruferPeelIter (m + 1) T.graph S).length = m + 1 := by
      rw [h_iter, List.length_cons, ih_len]
    have h_sub : ∀ x ∈ pruferPeelIter (m + 1) T.graph S, x ∈ S := by
      rw [h_iter]
      intro x hx
      cases List.mem_cons.mp hx with
      | inl heq => subst heq; exact haS
      | inr hmem => exact Finset.mem_of_mem_erase (ih_sub x hmem)
    have h_deg : ∀ u ∈ S, (vertNeighbors T.graph S u).card = 1 + (pruferPeelIter (m + 1) T.graph S).count u := by
      rw [h_iter]
      exact h_deg_all
    exact ⟨h_valid, h_len, h_sub, h_deg⟩

lemma isTree_univ (T : LabeledTree n) :
    (T.graph.induce ((Finset.univ : Finset (Fin n)) : Set (Fin n))).IsTree := by
  have h_eq : (((Finset.univ : Finset (Fin n)) : Set (Fin n))) = Set.univ := Finset.coe_univ
  rw [h_eq]
  exact (SimpleGraph.Iso.isTree_iff (SimpleGraph.induceUnivIso T.graph)).mpr T.isTree

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

/-- Left inverse property: decoding the code of a tree recovers the original tree. -/
theorem prufer_left_inv (hn : 2 ≤ n) (T : LabeledTree n) :
    pruferDecode hn (pruferCode T) = T := by
  have hS : (n - 2) + 2 = (Finset.univ : Finset (Fin n)).card := by
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  have h_tree : (T.graph.induce ((Finset.univ : Finset (Fin n)) : Set (Fin n))).IsTree := isTree_univ T
  have h_edges : (edgesIn T.graph Finset.univ).card = (Finset.univ : Finset (Fin n)).card - 1 := by
    have h_in : edgesIn T.graph Finset.univ = T.graph.edgeFinset := by
      ext e
      simp [mem_edgesIn]
    have h_card := T.isTree.card_edgeFinset
    have h_fin : Fintype.card (Fin n) = n := Fintype.card_fin n
    rw [h_fin] at h_card
    simp only [Finset.card_univ, Fintype.card_fin]
    rw [h_in]
    omega
  obtain ⟨h_valid, h_len, _, _⟩ := validPeelIter_all T (n - 2) Finset.univ hS h_tree h_edges
  have h_dec_sub := decodeEdges_of_validPeelIter T (n - 2) Finset.univ h_valid
  have h_list_eq := pruferCode_list_eq T h_len
  have h_sub : (pruferDecode hn (pruferCode T)).graph.edgeFinset ⊆ T.graph.edgeFinset := by
    intro e he
    have he_dec := mem_pruferDecode_edgeFinset hn (pruferCode T) e he
    dsimp [pruferDecodeEdgeFinset] at he_dec
    rw [h_list_eq] at he_dec
    exact h_dec_sub he_dec
  exact prufer_left_inv_of_sub hn T h_sub
