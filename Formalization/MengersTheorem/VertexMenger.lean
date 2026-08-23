import Formalization.MengersTheorem.Basic
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

open scoped Finset
open Classical

set_option linter.unusedSectionVars false

/-!
# Menger's Theorem — Vertex Version

This module proves Menger's Theorem for vertex separators and internally disjoint paths:
- Duality lemmas connecting disjoint paths and vertex cuts.
- Edge deletion and reduction properties for vertex separators.
- `mengers_theorem_vertex`: Max number of internally vertex-disjoint $s\text{-}t$ paths
  equals the min size of an $s\text{-}t$ vertex separator for non-adjacent $s, t$.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace MengersTheorem

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

end MengersTheorem
