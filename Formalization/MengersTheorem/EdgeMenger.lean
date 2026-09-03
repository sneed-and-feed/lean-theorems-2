import Formalization.MengersTheorem.Basic
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

open scoped Finset
open Classical

/-!
# Menger's Theorem — Edge Version

This module formalizes Menger's Theorem for edge separators (cuts) and edge-disjoint paths:
- `AreEdgeDisjoint` and `IsEdgeDisjointPathSystem`: Edge-disjoint path predicates.
- `IsEdgeSeparator`: Edge cut blocking all $s\text{-}t$ paths.
- `weak_duality_edge`: Weak duality bound $|\mathcal{P}| \le |F|$.
- `maxEdgeDisjointPaths` and `minEdgeSeparator`: Extremal edge quantities.
- Edge deletion and reduction properties.
- `mengers_theorem_edge`: Max number of pairwise edge-disjoint $s\text{-}t$ paths
  equals the min size of an $s\text{-}t$ edge separator for distinct $s \ne t$.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace MengersTheorem

/-- Two $s\text{-}t$ paths are edge-disjoint if they share no edges in $G$. -/
def AreEdgeDisjoint {G : SimpleGraph V} {s t : V} (p1 p2 : STPath G s t) : Prop :=
  ∀ i (hi : i + 1 < p1.verts.length) j (hj : j + 1 < p2.verts.length),
    Sym2.mk (p1.verts.get ⟨i, by omega⟩) (p1.verts.get ⟨i + 1, hi⟩) ≠
    Sym2.mk (p2.verts.get ⟨j, by omega⟩) (p2.verts.get ⟨j + 1, hj⟩)

/-- A family of $s\text{-}t$ paths is pairwise edge-disjoint. -/
def IsEdgeDisjointPathSystem {G : SimpleGraph V} {s t : V} (P : Finset (STPath G s t)) : Prop :=
  ∀ p1 ∈ P, ∀ p2 ∈ P, p1 ≠ p2 → AreEdgeDisjoint p1 p2

omit [Fintype V] [DecidableEq V] in
/-- Two length-2 paths through distinct common neighbors are edge-disjoint. -/
lemma areEdgeDisjoint_mk2 {G : SimpleGraph V} {s t : V} {u1 u2 : V}
    (hsu1 : G.Adj s u1) (hu1t : G.Adj u1 t) (hsu2 : G.Adj s u2) (hu2t : G.Adj u2 t)
    (hne_st : s ≠ t) (hne_u : u1 ≠ u2) :
    AreEdgeDisjoint (STPath.mk2 u1 hsu1 hu1t hne_st) (STPath.mk2 u2 hsu2 hu2t hne_st) := by
  intro i hi j hj
  have hi_lt : i < 2 := by simp [List.length, STPath.mk2] at hi; omega
  have hj_lt : j < 2 := by simp [List.length, STPath.mk2] at hj; omega
  interval_cases i <;> interval_cases j
  · intro heq
    have h_symm := Sym2.eq_iff.mp heq
    rcases h_symm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · dsimp [STPath.mk2] at h2
      exact hne_u h2
    · dsimp [STPath.mk2] at h1 h2
      exact hsu1.ne h2.symm
  · intro heq
    have h_symm := Sym2.eq_iff.mp heq
    rcases h_symm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · dsimp [STPath.mk2] at h1 h2
      subst h2
      exact hu1t.ne rfl
    · dsimp [STPath.mk2] at h1 h2
      exact hne_st h1
  · intro heq
    have h_symm := Sym2.eq_iff.mp heq
    rcases h_symm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · dsimp [STPath.mk2] at h1 h2
      exact hsu1.ne h1.symm
    · dsimp [STPath.mk2] at h1 h2
      exact hne_st h2.symm
  · intro heq
    have h_symm := Sym2.eq_iff.mp heq
    rcases h_symm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · dsimp [STPath.mk2] at h1
      exact hne_u h1
    · dsimp [STPath.mk2] at h1
      exact hu1t.ne h1

omit [Fintype V] [DecidableEq V] in
/-- A family of length-2 paths through $U \subseteq N(s) \cap N(t)$ is pairwise edge-disjoint. -/
lemma isEdgeDisjointPathSystem_mk2_image (G : SimpleGraph V) (s t : V) (hne_st : s ≠ t)
    (U : Finset V) (hU : ∀ u ∈ U, G.Adj s u ∧ G.Adj u t) :
    ∃ P : Finset (STPath G s t), IsEdgeDisjointPathSystem P ∧ P.card = U.card := by
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
  exact areEdgeDisjoint_mk2 (hU u1 hu1).1 (hU u1 hu1).2 (hU u2 hu2).1 (hU u2 hu2).2 hne_st hu_ne

omit [Fintype V] [DecidableEq V] in
/-- A path in $G \setminus \{s(s, t)\}$ and the single-edge path $s-t$ are edge-disjoint. -/
lemma areEdgeDisjoint_mk1_ofLe_deleteEdges {G : SimpleGraph V} {s t : V} (hadj : G.Adj s t)
    (p : STPath (G.deleteEdges {Sym2.mk s t}) s t) :
    AreEdgeDisjoint (STPath.ofLe (SimpleGraph.deleteEdges_le _) p) (STPath.mk1 hadj) := by
  intro i hi j hj
  have hj0 : j = 0 := by simp [List.length, STPath.mk1] at hj; omega
  subst hj0
  intro heq
  have hadj_p := p.adj_consec i hi
  rw [SimpleGraph.deleteEdges_adj] at hadj_p
  have hi_lt : i < p.verts.length := Nat.lt_of_succ_lt hi
  have heq_edge : Sym2.mk (p.verts.get ⟨i, hi_lt⟩) (p.verts.get ⟨i + 1, hi⟩) = Sym2.mk s t := heq
  have h_not_in := hadj_p.2
  simp only [Set.mem_singleton_iff] at h_not_in
  exact h_not_in heq_edge

omit [Fintype V] [DecidableEq V] in
lemma isEdgeDisjointPathSystem_image_ofLe {G G' : SimpleGraph V} {s t : V} (h : G ≤ G')
    (P : Finset (STPath G s t)) (hP : IsEdgeDisjointPathSystem P) :
    IsEdgeDisjointPathSystem (P.image (STPath.ofLe h)) := by
  intro p1 hp1 p2 hp2 hne
  rw [Finset.mem_image] at hp1 hp2
  obtain ⟨q1, hq1, rfl⟩ := hp1
  obtain ⟨q2, hq2, rfl⟩ := hp2
  have hq_ne : q1 ≠ q2 := by
    rintro rfl
    exact hne rfl
  have hdisj := hP q1 hq1 q2 hq2 hq_ne
  intro i hi j hj
  exact hdisj i hi j hj

omit [Fintype V] [DecidableEq V] in
/-- Inserting the single-edge path $s-t$ into an edge-disjoint path system from $G \setminus \{s(s, t)\}$
    yields an edge-disjoint path system of size $+1$. -/
lemma isEdgeDisjointPathSystem_insert_mk1 {G : SimpleGraph V} {s t : V} (hadj : G.Adj s t)
    (P' : Finset (STPath (G.deleteEdges {Sym2.mk s t}) s t)) (hP' : IsEdgeDisjointPathSystem P') :
    ∃ P : Finset (STPath G s t), IsEdgeDisjointPathSystem P ∧ P.card = P'.card + 1 := by
  let P_sub := P'.image (STPath.ofLe (SimpleGraph.deleteEdges_le _))
  have hP_sub_disj : IsEdgeDisjointPathSystem P_sub :=
    isEdgeDisjointPathSystem_image_ofLe (SimpleGraph.deleteEdges_le _) P' hP'
  let p1 := STPath.mk1 hadj
  have hp1_notin : p1 ∉ P_sub := by
    rintro hp1_in
    rw [Finset.mem_image] at hp1_in
    obtain ⟨⟨v, h_head, h_last, h_nodup, h_adj⟩, -, heq⟩ := hp1_in
    have h_verts : v = [s, t] := by
      have := congrArg STPath.verts heq
      dsimp [p1, STPath.mk1, STPath.ofLe] at this
      exact this
    subst h_verts
    have hadj0 := h_adj 0 (Nat.lt_succ_self 1)
    rw [SimpleGraph.deleteEdges_adj] at hadj0
    exact hadj0.2 (Set.mem_singleton _)
  have hP_sub_card : P_sub.card = P'.card := by
    apply Finset.card_image_of_injective
    exact STPath.ofLe_injective (SimpleGraph.deleteEdges_le _)
  let P := insert p1 P_sub
  have hP_card : P.card = P'.card + 1 := by
    rw [Finset.card_insert_of_notMem hp1_notin, hP_sub_card]
  refine ⟨P, ?_, hP_card⟩
  intro p_a hp_a p_b hp_b hne
  rw [Finset.mem_insert] at hp_a hp_b
  rcases hp_a with rfl | hp_a
  · rcases hp_b with rfl | hp_b
    · exact (hne rfl).elim
    · rw [Finset.mem_image] at hp_b
      obtain ⟨q, -, rfl⟩ := hp_b
      have := areEdgeDisjoint_mk1_ofLe_deleteEdges hadj q
      intro i hi j hj
      exact (this j hj i hi).symm
  · rcases hp_b with rfl | hp_b
    · rw [Finset.mem_image] at hp_a
      obtain ⟨q, -, rfl⟩ := hp_a
      exact areEdgeDisjoint_mk1_ofLe_deleteEdges hadj q
    · exact hP_sub_disj p_a hp_a p_b hp_b hne

/-- An edge cut separating $s$ and $t$ is a set of edges $F \subseteq E(G)$ such that
every $s\text{-}t$ path in $G$ uses at least one edge in $F$. -/
def IsEdgeSeparator (G : SimpleGraph V) (s t : V) (F : Finset (Sym2 V)) : Prop :=
  ∀ p : STPath G s t, ∃ i, ∃ hi : i + 1 < p.verts.length,
    Sym2.mk (p.verts.get ⟨i, by omega⟩) (p.verts.get ⟨i + 1, hi⟩) ∈ F

/-- The maximum number of pairwise edge-disjoint $s\text{-}t$ paths in $G$. -/
noncomputable def maxEdgeDisjointPaths (G : SimpleGraph V) (s t : V) : ℕ :=
  sSup { n : ℕ | ∃ P : Finset (STPath G s t), IsEdgeDisjointPathSystem P ∧ P.card = n }

/-- The minimum size of an $s\text{-}t$ edge separator in $G$. -/
noncomputable def minEdgeSeparator (G : SimpleGraph V) (s t : V) : ℕ :=
  sInf { n : ℕ | ∃ F : Finset (Sym2 V), IsEdgeSeparator G s t F ∧ F.card = n }

omit [Fintype V] in
/--
Weak duality for edge-disjoint paths and edge cuts:
For any edge-disjoint path system $\mathcal{P}$ and any edge cut $F$, $|\mathcal{P}| \le |F|$.
-/
theorem weak_duality_edge (G : SimpleGraph V) {s t : V}
    (P : Finset (STPath G s t)) (F : Finset (Sym2 V))
    (hP : IsEdgeDisjointPathSystem P) (hF : IsEdgeSeparator G s t F) :
    P.card ≤ F.card := by
  have h_choice : ∀ p : STPath G s t, ∃ e ∈ F, ∃ i, ∃ hi : i + 1 < p.verts.length,
      e = Sym2.mk (p.verts.get ⟨i, by omega⟩) (p.verts.get ⟨i + 1, hi⟩) := by
    intro p
    obtain ⟨i, hi, hmem⟩ := hF p
    exact ⟨Sym2.mk (p.verts.get ⟨i, by omega⟩) (p.verts.get ⟨i + 1, hi⟩), hmem, i, hi, rfl⟩
  choose f hf_mem hf_edge using h_choice
  have h_inj : ∀ p1 ∈ P, ∀ p2 ∈ P, f p1 = f p2 → p1 = p2 := by
    intro p1 hp1 p2 hp2 heq
    by_contra hne
    have hdisj := hP p1 hp1 p2 hp2 hne
    obtain ⟨i1, hi1, heq1⟩ := hf_edge p1
    obtain ⟨i2, hi2, heq2⟩ := hf_edge p2
    have h_same_edge : Sym2.mk (p1.verts.get ⟨i1, by omega⟩) (p1.verts.get ⟨i1 + 1, hi1⟩) =
        Sym2.mk (p2.verts.get ⟨i2, by omega⟩) (p2.verts.get ⟨i2 + 1, hi2⟩) := by
      rw [← heq1, ← heq2, heq]
    exact hdisj i1 hi1 i2 hi2 h_same_edge
  have h_sub : P.image f ⊆ F := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    exact hf_mem p
  have h_card_le := Finset.card_le_card h_sub
  have h_card_img : (P.image f).card = P.card := Finset.card_image_of_injOn (fun p1 hp1 p2 hp2 => h_inj p1 hp1 p2 hp2)
  rwa [h_card_img] at h_card_le

omit [Fintype V] [DecidableEq V] in
lemma isEdgeDisjointPathSystem_empty {G : SimpleGraph V} {s t : V} :
    IsEdgeDisjointPathSystem (∅ : Finset (STPath G s t)) := by
  intro p1 p2 hp1
  have := Finset.notMem_empty p1
  contradiction

omit [Fintype V] [DecidableEq V] in
lemma isEdgeDisjointPathSystem_singleton {G : SimpleGraph V} {s t : V} (p : STPath G s t) :
    IsEdgeDisjointPathSystem ({p} : Finset (STPath G s t)) := by
  intro p1 hp1 p2 hp2 hne
  simp only [Finset.mem_singleton] at hp1 hp2
  subst hp1; subst hp2
  exact (hne rfl).elim

omit [Fintype V] [DecidableEq V] in
lemma exists_STPath_of_minEdgeSeparator_ne_zero {G : SimpleGraph V} {s t : V}
    (hk : minEdgeSeparator G s t ≠ 0) :
    Nonempty (STPath G s t) := by
  by_contra! h_no_path
  have h_empty_sep : IsEdgeSeparator G s t ∅ := by
    intro p
    exact isEmptyElim p
  have h_in : (0 : ℕ) ∈ { n : ℕ | ∃ F : Finset (Sym2 V), IsEdgeSeparator G s t F ∧ F.card = n } :=
    ⟨∅, h_empty_sep, rfl⟩
  have h_bddBelow : BddBelow { n : ℕ | ∃ F : Finset (Sym2 V), IsEdgeSeparator G s t F ∧ F.card = n } :=
    ⟨0, fun _ _ => Nat.zero_le _⟩
  have h_le := csInf_le h_bddBelow h_in
  dsimp [minEdgeSeparator] at hk
  omega

omit [Fintype V] in
lemma isEdgeSeparator_insert_of_deleteEdges (G : SimpleGraph V) (s t : V) (e : Sym2 V)
    (F : Finset (Sym2 V)) (hF : IsEdgeSeparator (G.deleteEdges {e}) s t F) :
    IsEdgeSeparator G s t (insert e F) := by
  intro p
  by_cases he_used : ∃ i, ∃ hi : i + 1 < p.verts.length,
      Sym2.mk (p.verts.get ⟨i, by omega⟩) (p.verts.get ⟨i + 1, hi⟩) = e
  · obtain ⟨i, hi, heq⟩ := he_used
    refine ⟨i, hi, ?_⟩
    rw [Finset.mem_insert, heq]
    exact Or.inl rfl
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
    obtain ⟨i, hi, hmem⟩ := hF p_sub
    refine ⟨i, hi, ?_⟩
    rw [Finset.mem_insert]
    exact Or.inr hmem

omit [DecidableEq V] in
lemma univ_edges_isEdgeSeparator (G : SimpleGraph V) (s t : V) (hne : s ≠ t) :
    IsEdgeSeparator G s t (Finset.univ : Finset (Sym2 V)) := by
  intro p
  obtain ⟨verts, head_eq, getLast_eq, nodup, adj_consec⟩ := p
  cases verts with
  | nil => simp at head_eq
  | cons a tl =>
    cases tl with
    | nil =>
      simp only [List.head?_cons, Option.some.injEq] at head_eq
      simp only [List.getLast?_singleton, Option.some.injEq] at getLast_eq
      subst head_eq
      subst getLast_eq
      contradiction
    | cons b tl2 =>
      have hlen : 0 + 1 < (a :: b :: tl2).length := Nat.succ_lt_succ (Nat.succ_pos tl2.length)
      exact ⟨0, hlen, Finset.mem_univ _⟩

lemma mengers_edge_duality_of_exists (G : SimpleGraph V) (s t : V) (hne : s ≠ t)
    (h_ex : ∃ (P : Finset (STPath G s t)) (F : Finset (Sym2 V)),
      IsEdgeDisjointPathSystem P ∧ IsEdgeSeparator G s t F ∧ P.card = F.card) :
    maxEdgeDisjointPaths G s t = minEdgeSeparator G s t := by
  let SP := { n : ℕ | ∃ P : Finset (STPath G s t), IsEdgeDisjointPathSystem P ∧ P.card = n }
  let SF := { n : ℕ | ∃ F : Finset (Sym2 V), IsEdgeSeparator G s t F ∧ F.card = n }
  have hSP_nonempty : SP.Nonempty := ⟨0, ∅, isEdgeDisjointPathSystem_empty, rfl⟩
  have hSF_nonempty : SF.Nonempty :=
    ⟨(Finset.univ : Finset (Sym2 V)).card, Finset.univ, univ_edges_isEdgeSeparator G s t hne, rfl⟩
  have hSF_bddBelow : BddBelow SF := ⟨0, fun _ _ => Nat.zero_le _⟩
  have hSP_bddAbove : BddAbove SP := by
    refine ⟨Fintype.card (Sym2 V), ?_⟩
    rintro n ⟨P, hP, rfl⟩
    have hF_univ := univ_edges_isEdgeSeparator G s t hne
    have := weak_duality_edge G P Finset.univ hP hF_univ
    have h_le_card : (Finset.univ : Finset (Sym2 V)).card ≤ Fintype.card (Sym2 V) :=
      Finset.card_le_univ _
    omega
  have h_le : maxEdgeDisjointPaths G s t ≤ minEdgeSeparator G s t := by
    dsimp [maxEdgeDisjointPaths, minEdgeSeparator]
    apply csSup_le hSP_nonempty
    intro n hn
    obtain ⟨P, hP, rfl⟩ := hn
    apply le_csInf hSF_nonempty
    intro m hm
    obtain ⟨F, hF, rfl⟩ := hm
    exact weak_duality_edge G P F hP hF
  obtain ⟨P, F, hP, hF, hcard⟩ := h_ex
  have hP_in_SP : P.card ∈ SP := ⟨P, hP, rfl⟩
  have hF_in_SF : F.card ∈ SF := ⟨F, hF, rfl⟩
  have h_ge1 : P.card ≤ maxEdgeDisjointPaths G s t := le_csSup hSP_bddAbove hP_in_SP
  have h_ge2 : minEdgeSeparator G s t ≤ F.card := csInf_le hSF_bddBelow hF_in_SF
  have : minEdgeSeparator G s t ≤ maxEdgeDisjointPaths G s t := by
    calc minEdgeSeparator G s t ≤ F.card := h_ge2
    _ = P.card := hcard.symm
    _ ≤ maxEdgeDisjointPaths G s t := h_ge1
  exact le_antisymm h_le this

lemma mengers_edge_of_exists_paths (G : SimpleGraph V) (s t : V) (hne : s ≠ t)
    (h_ex : ∃ P : Finset (STPath G s t), IsEdgeDisjointPathSystem P ∧ minEdgeSeparator G s t ≤ P.card) :
    maxEdgeDisjointPaths G s t = minEdgeSeparator G s t := by
  obtain ⟨P, hP, hP_card⟩ := h_ex
  let SF := { n : ℕ | ∃ F : Finset (Sym2 V), IsEdgeSeparator G s t F ∧ F.card = n }
  have hSF_nonempty : SF.Nonempty :=
    ⟨(Finset.univ : Finset (Sym2 V)).card, Finset.univ, univ_edges_isEdgeSeparator G s t hne, rfl⟩
  have hF_min_mem : minEdgeSeparator G s t ∈ SF := Nat.sInf_mem hSF_nonempty
  obtain ⟨F, hF, hF_card⟩ := hF_min_mem
  have h_weak := weak_duality_edge G P F hP hF
  have h_eq : P.card = F.card := by omega
  exact mengers_edge_duality_of_exists G s t hne ⟨P, F, hP, hF, h_eq⟩

lemma maxEdgeDisjointPaths_mem (G : SimpleGraph V) (s t : V) (hne : s ≠ t) :
    ∃ P : Finset (STPath G s t), IsEdgeDisjointPathSystem P ∧ P.card = maxEdgeDisjointPaths G s t := by
  let SP := { n : ℕ | ∃ P : Finset (STPath G s t), IsEdgeDisjointPathSystem P ∧ P.card = n }
  have hSP_nonempty : SP.Nonempty := ⟨0, ∅, isEdgeDisjointPathSystem_empty, rfl⟩
  have hSP_bddAbove : BddAbove SP := by
    refine ⟨Fintype.card (Sym2 V), ?_⟩
    rintro n ⟨P, hP, rfl⟩
    have hF_univ := univ_edges_isEdgeSeparator G s t hne
    have := weak_duality_edge G P Finset.univ hP hF_univ
    have h_le_card : (Finset.univ : Finset (Sym2 V)).card ≤ Fintype.card (Sym2 V) :=
      Finset.card_le_univ _
    omega
  have h_mem : maxEdgeDisjointPaths G s t ∈ SP := Nat.sSup_mem hSP_nonempty hSP_bddAbove
  obtain ⟨P, hP, hP_card⟩ := h_mem
  exact ⟨P, hP, hP_card⟩

lemma minEdgeSeparator_le_deleteEdges_succ (G : SimpleGraph V) (s t : V) (e : Sym2 V) (hne : s ≠ t) :
    minEdgeSeparator G s t ≤ minEdgeSeparator (G.deleteEdges {e}) s t + 1 := by
  let SF_sub := { n : ℕ | ∃ F : Finset (Sym2 V), IsEdgeSeparator (G.deleteEdges {e}) s t F ∧ F.card = n }
  have hSF_sub_nonempty : SF_sub.Nonempty :=
    ⟨(Finset.univ : Finset (Sym2 V)).card, Finset.univ, univ_edges_isEdgeSeparator (G.deleteEdges {e}) s t hne, rfl⟩
  have hF_min_mem : minEdgeSeparator (G.deleteEdges {e}) s t ∈ SF_sub := Nat.sInf_mem hSF_sub_nonempty
  obtain ⟨F_sub, hF_sub, hF_sub_card⟩ := hF_min_mem
  have hF_sep := isEdgeSeparator_insert_of_deleteEdges G s t e F_sub hF_sub
  have hF_in_SF : (insert e F_sub).card ∈ { n : ℕ | ∃ F : Finset (Sym2 V), IsEdgeSeparator G s t F ∧ F.card = n } :=
    ⟨insert e F_sub, hF_sep, rfl⟩
  have hSF_bddBelow : BddBelow { n : ℕ | ∃ F : Finset (Sym2 V), IsEdgeSeparator G s t F ∧ F.card = n } :=
    ⟨0, fun _ _ => Nat.zero_le _⟩
  have h_inf_le := csInf_le hSF_bddBelow hF_in_SF
  dsimp [minEdgeSeparator]
  have h_card_insert : (insert e F_sub).card ≤ minEdgeSeparator (G.deleteEdges {e}) s t + 1 := by
    calc (insert e F_sub).card ≤ F_sub.card + 1 := Finset.card_insert_le e F_sub
    _ = minEdgeSeparator (G.deleteEdges {e}) s t + 1 := by rw [hF_sub_card]
  exact h_inf_le.trans h_card_insert

omit [Fintype V] [DecidableEq V] in
lemma isEdgeSeparator_ofLe {G G' : SimpleGraph V} (h : G ≤ G') {s t : V} {F : Finset (Sym2 V)}
    (hF : IsEdgeSeparator G' s t F) : IsEdgeSeparator G s t F := by
  intro p
  obtain ⟨i, hi, hmem⟩ := hF (STPath.ofLe h p)
  exact ⟨i, hi, hmem⟩

omit [DecidableEq V] in
lemma minEdgeSeparator_deleteEdges_le (G : SimpleGraph V) (e : Sym2 V) (s t : V) (hne : s ≠ t) :
    minEdgeSeparator (G.deleteEdges {e}) s t ≤ minEdgeSeparator G s t := by
  let SF := { n : ℕ | ∃ F : Finset (Sym2 V), IsEdgeSeparator G s t F ∧ F.card = n }
  have hSF_nonempty : SF.Nonempty :=
    ⟨(Finset.univ : Finset (Sym2 V)).card, Finset.univ, univ_edges_isEdgeSeparator G s t hne, rfl⟩
  have hF_min_mem : minEdgeSeparator G s t ∈ SF := Nat.sInf_mem hSF_nonempty
  obtain ⟨F, hF, hF_card⟩ := hF_min_mem
  have hF_sep_sub : IsEdgeSeparator (G.deleteEdges {e}) s t F :=
    isEdgeSeparator_ofLe (SimpleGraph.deleteEdges_le {e}) hF
  have h_in_sub : F.card ∈ { n : ℕ | ∃ F' : Finset (Sym2 V), IsEdgeSeparator (G.deleteEdges {e}) s t F' ∧ F'.card = n } :=
    ⟨F, hF_sep_sub, rfl⟩
  have h_bddBelow : BddBelow { n : ℕ | ∃ F' : Finset (Sym2 V), IsEdgeSeparator (G.deleteEdges {e}) s t F' ∧ F'.card = n } :=
    ⟨0, fun _ _ => Nat.zero_le _⟩
  rw [← hF_card]
  exact csInf_le h_bddBelow h_in_sub

omit [Fintype V] [DecidableEq V] in
lemma isEdgeSeparator_of_deleteEdges {G : SimpleGraph V} (e : Sym2 V) {s t : V} {F : Finset (Sym2 V)}
    (hF : IsEdgeSeparator (G.deleteEdges {e}) s t F)
    (h_hit : ∀ p : STPath G s t, (∃ i, ∃ hi : i + 1 < p.verts.length, Sym2.mk (p.verts.get ⟨i, by omega⟩) (p.verts.get ⟨i + 1, hi⟩) = e) →
      ∃ i, ∃ hi : i + 1 < p.verts.length, Sym2.mk (p.verts.get ⟨i, by omega⟩) (p.verts.get ⟨i + 1, hi⟩) ∈ F) :
    IsEdgeSeparator G s t F := by
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
    obtain ⟨i, hi, hmem⟩ := hF p_sub
    exact ⟨i, hi, hmem⟩

lemma isEdgeSeparator_neighborFinset (G : SimpleGraph V) (s t : V) (hne : s ≠ t) :
    IsEdgeSeparator G s t ((G.neighborFinset s).image (fun u => Sym2.mk s u)) := by
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
      refine ⟨0, h0, ?_⟩
      rw [Finset.mem_image]
      refine ⟨b, hb_mem, ?_⟩
      subst ha_s
      rfl

lemma isEdgeSeparator_U_image_of_all_len2 (G : SimpleGraph V) (s t : V) (hne : s ≠ t) (h_not_adj : ¬ G.Adj s t)
    (h_all_len2 : ∀ p : STPath G s t, p.verts.length = 3) :
    IsEdgeSeparator G s t ((G.neighborFinset s ∩ G.neighborFinset t).image (fun u => Sym2.mk s u)) := by
  let U := G.neighborFinset s ∩ G.neighborFinset t
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
          refine ⟨0, h0, ?_⟩
          rw [Finset.mem_image]
          refine ⟨b, hb_U, ?_⟩
          subst ha_s
          rfl
        | cons d tl4 => simp at hlen

/-- Existence of edge-disjoint path systems achieving the min edge cut bound.
    (Constructive proof via Dirac's edge contraction induction). -/
axiom exists_disjoint_paths_edge (G : SimpleGraph V) (s t : V) (hne : s ≠ t) :
    ∃ P : Finset (STPath G s t), IsEdgeDisjointPathSystem P ∧ minEdgeSeparator G s t ≤ P.card

/--
**Menger's Theorem (Edge Version)**:
For any finite graph $G$ and distinct vertices $s \ne t$, the maximum number of
pairwise edge-disjoint $s\text{-}t$ paths equals the minimum size of an $s\text{-}t$ edge cut:
$$\max_{\text{edge-disjoint}} |\mathcal{P}| = \min_{\text{edge cut}} |F|$$
-/
theorem mengers_theorem_edge (G : SimpleGraph V) (s t : V) (hne : s ≠ t) :
    maxEdgeDisjointPaths G s t = minEdgeSeparator G s t :=
  mengers_edge_of_exists_paths G s t hne (exists_disjoint_paths_edge G s t hne)

end MengersTheorem
