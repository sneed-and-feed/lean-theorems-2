import Formalization.CayleysFormula.PruferEncode

open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Prüfer Decoding for Labeled Trees

This module formalizes the decoding direction of Heinz Prüfer's (1918) bijective
correspondence: reconstructing a labeled tree on $n$ vertices from a sequence of length $n - 2$.

## Mathematical Details

Given a sequence $(a_1, \dots, a_{n-2}) \in \{1, \dots, n\}^{n-2}$:
1. Reconstruct edges iteratively: at step $i$, find the smallest available vertex not appearing
   in the remaining sequence, connect it to $a_i$, and remove it from the available set.
2. At the final step, connect the two remaining vertices.
3. The resulting graph is shown to be connected and acyclic (a valid labeled tree).

## Main Definitions & Theorems
- `decodeEdges`: Inductive edge reconstruction algorithm.
- `decodeEdges_nil`: Structural equation for base case (2 vertices remaining).
- `decodeEdges_cons`: Structural equation for inductive step.
- `decodeEdges_mem_endpoints`: All decoded edges have endpoints in the available vertex set.
- `decodeEdges_nodiag`: No decoded edge is a self-loop.
- `decodeEdges_card`: The decoded edge set has cardinality $|L| + 1$.
- `decodeEdges_reachable`: All vertices in the available set are mutually reachable.
- `natCard_finset_coe`: Natural cardinality of a finset coercion.
- `natCard_edgeSet_fromEdgeSet`: Edge set cardinality of a graph constructed from edges.
- `pruferDecodeEdgeFinset`: Finset of edges decoded from a Prüfer sequence.
- `pruferDecodeGraph`: Simple graph decoded from a Prüfer sequence.
- `pruferDecode_isTree`: Proof that `pruferDecodeGraph` is a valid tree.
- `pruferDecode`: Function returning the decoded `LabeledTree`.
-/

variable {n : ℕ}

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
  split_ifs
  subst hu hw
  rfl

/-- Structural equation for `decodeEdges` inductive step. -/
lemma decodeEdges_cons (n : ℕ) (a : Fin n) (rest : List (Fin n)) (S : Finset (Fin n)) (hS : rest.length + 3 = S.card)
    (v : Fin n) (hv : v = (pruferLeaves n S (a :: rest)).min' (pruferLeaves_nonempty (by simp; omega))) :
    decodeEdges n (a :: rest) S = insert s(v, a) (decodeEdges n rest (S.erase v)) := by
  dsimp [decodeEdges]
  split_ifs
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
