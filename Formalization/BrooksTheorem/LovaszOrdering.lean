import Formalization.BrooksTheorem.Basic
import Formalization.BrooksTheorem.OddCycles
import Formalization.BrooksTheorem.Greedy
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open Finset SimpleGraph

/-!
# Brooks' Theorem — Lovász Ordering and BFS Spanning Trees

This module constructs the Lovász vertex ordering (L. Lovász, 1975) for Brooks' Theorem:
- Distance arithmetic on graphs (`exists_neighbor_dist_lt`, `dist_zero_iff`, `dist_le_card`).
- Triple existence (`exists_triple_of_not_complete`): in any connected non-clique graph,
  there exist vertices $v_1, v_2, v_n$ such that $v_1 \not\sim v_2$, $v_1 \sim v_n$, $v_2 \sim v_n$.
- Reverse BFS spanning walk construction (`exists_reverse_bfs_list`).
- Constructive ordering of triples (`lovasz_ordering_of_triple`): converting a connected subgraph
  $G \setminus \{v_1, v_2\}$ into an ordering where every vertex before $v_n$ has a forward neighbor.
- Lovász ordering existence statement (`exists_lovasz_ordering`).
-/

namespace BrooksTheorem

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma exists_neighbor_dist_lt {α : Type*} (H : SimpleGraph α) (u r : α)
    (hr : H.Reachable u r) (hne : u ≠ r) :
    ∃ w : α, H.Adj u w ∧ H.dist w r < H.dist u r := by
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  cases p with
  | nil =>
    exact False.elim (hne rfl)
  | cons hadj p' =>
    refine ⟨_, hadj, ?_⟩
    have hle := H.dist_le p'
    have hlen : (SimpleGraph.Walk.cons hadj p').length = p'.length + 1 := rfl
    rw [hlen] at hp
    omega

lemma card_subtype_ne_pair {α : Type*} [Fintype α] [DecidableEq α] (u v : α) (hne : u ≠ v) :
    Fintype.card {x : α // x ≠ u ∧ x ≠ v} = Fintype.card α - 2 := by
  have : (Finset.univ.filter (fun x : α => x ≠ u ∧ x ≠ v)).card = Fintype.card α - 2 := by
    have h_eq : (Finset.univ.filter (fun x : α => x ≠ u ∧ x ≠ v)) = (Finset.univ.erase u).erase v := by
      ext x
      simp [Finset.mem_erase, Finset.mem_filter, and_comm]
    rw [h_eq, Finset.card_erase_of_mem, Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ]
    · rfl
    · rw [Finset.mem_erase]
      exact ⟨hne.symm, Finset.mem_univ v⟩
  rw [Fintype.card_subtype, this]

lemma exists_adj_mem_not_mem {α : Type*} [DecidableEq α] (H : SimpleGraph α) (s : Finset α) :
    ∀ {z r : α}, z ∉ s → r ∈ s → H.Walk z r → ∃ u v, u ∉ s ∧ v ∈ s ∧ H.Adj u v
  | z, _, hz, hr, .nil => False.elim (hz hr)
  | z, _, hz, hr, .cons (v := v) hadj p' =>
    if hy : v ∈ s then
      ⟨z, v, hz, hy, hadj⟩
    else
      exists_adj_mem_not_mem H s hy hr p'

lemma exists_reverse_bfs_list {α : Type*} [Fintype α] [DecidableEq α]
    (H : SimpleGraph α) (r : α) (h_reach : ∀ z : α, H.Reachable z r) :
    ∀ (m : ℕ) (hm : m ≤ Fintype.card α) (hm_pos : 0 < m),
      ∃ (L : List α) (hlen : L.length = m), L.Nodup ∧ (∃ hne : L ≠ [], L.getLast hne = r) ∧
        ∀ (i : ℕ) (hi : i < m - 1),
          ∃ (j : ℕ) (hj : i < j) (hjm : j < m),
            H.Adj (L.get ⟨i, by omega⟩) (L.get ⟨j, by omega⟩) := by
  intro m
  induction m with
  | zero =>
    intro _ hm_pos
    omega
  | succ m ih =>
    intro hm _
    by_cases hm0 : m = 0
    · subst hm0
      refine ⟨[r], rfl, List.nodup_singleton r, ⟨List.cons_ne_nil r [], rfl⟩, ?_⟩
      intro i hi
      omega
    · have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
      have hm_le : m ≤ Fintype.card α := by omega
      obtain ⟨L, hlen, hnodup, ⟨hne, hlast⟩, hfwd⟩ := ih hm_le hm_pos
      let s := L.toFinset
      have h_card_s : s.card = m := by
        rw [List.toFinset_card_of_nodup hnodup, hlen]
      have h_card_univ : (Finset.univ : Finset α).card = Fintype.card α := Finset.card_univ
      have h_lt_card : s.card < (Finset.univ : Finset α).card := by omega
      obtain ⟨z, -, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card h_lt_card
      have hr_in_s : r ∈ s := by
        rw [List.mem_toFinset]
        exact hlast ▸ List.getLast_mem hne
      obtain ⟨p⟩ := h_reach z
      obtain ⟨u, v, hu_not, hv_in, hadj⟩ := exists_adj_mem_not_mem H s hz hr_in_s p
      rw [List.mem_toFinset] at hv_in
      obtain ⟨v_idx, hv_idx_eq⟩ := List.mem_iff_get.mp hv_in
      let L' := u :: L
      have hlen' : L'.length = m + 1 := by dsimp [L']; rw [hlen]
      have hu_not_L : u ∉ L := by rwa [← List.mem_toFinset]
      have hnodup' : L'.Nodup := List.nodup_cons.mpr ⟨hu_not_L, hnodup⟩
      have hne' : L' ≠ [] := List.cons_ne_nil u L
      have hlast' : L'.getLast hne' = r := by
        rw [List.getLast_cons hne, hlast]
      refine ⟨L', hlen', hnodup', ⟨hne', hlast'⟩, ?_⟩
      intro i hi
      by_cases hi0 : i = 0
      · subst hi0
        have hj_lt_m : (v_idx : ℕ) + 1 < m + 1 := by
          have : (v_idx : ℕ) < m := by rw [← hlen]; exact v_idx.isLt
          omega
        refine ⟨(v_idx : ℕ) + 1, by omega, hj_lt_m, ?_⟩
        have hi_get : L'.get ⟨0, by omega⟩ = u := rfl
        have hj_get : L'.get ⟨(v_idx : ℕ) + 1, by omega⟩ = v := by
          have h_eq : L'.get ⟨(v_idx : ℕ) + 1, by omega⟩ = L.get v_idx := rfl
          rw [h_eq, hv_idx_eq]
        rw [hi_get, hj_get]
        exact hadj
      · have hi_prev_lt : i - 1 < m - 1 := by omega
        obtain ⟨j_prev, hj_lt, hj_lt_m, hadj_prev⟩ := hfwd (i - 1) hi_prev_lt
        have hj_lt_m1 : j_prev + 1 < m + 1 := by omega
        refine ⟨j_prev + 1, by omega, hj_lt_m1, ?_⟩
        have hi_get : L'.get ⟨i, by omega⟩ = L.get ⟨i - 1, by omega⟩ := by
          have h_idx : (⟨i, by omega⟩ : Fin L'.length) = ⟨(i - 1) + 1, by omega⟩ := by
            ext
            dsimp
            omega
          rw [h_idx]
          rfl
        have hj_get : L'.get ⟨j_prev + 1, by omega⟩ = L.get ⟨j_prev, by omega⟩ := rfl
        rw [hi_get, hj_get]
        exact hadj_prev

lemma lovasz_ordering_of_triple (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_card : 3 ≤ Fintype.card V)
    (v1 v2 vn : V) (hv12 : v1 ≠ v2) (hv1n : v1 ≠ vn) (hv2n : v2 ≠ vn)
    (h_not_adj : ¬ G.Adj v1 v2) (h_adj1 : G.Adj v1 vn) (h_adj2 : G.Adj v2 vn)
    (h_reach : ∀ (u : V) (hu1 : u ≠ v1) (hu2 : u ≠ v2),
      (G.induce {x : V | x ≠ v1 ∧ x ≠ v2}).Reachable ⟨u, ⟨hu1, hu2⟩⟩ ⟨vn, ⟨hv1n.symm, hv2n.symm⟩⟩) :
    ∃ (ord : Fin (Fintype.card V) ≃ V),
      (¬ G.Adj (ord ⟨0, by omega⟩) (ord ⟨1, by omega⟩)) ∧
      (G.Adj (ord ⟨0, by omega⟩) (ord ⟨Fintype.card V - 1, by omega⟩)) ∧
      (G.Adj (ord ⟨1, by omega⟩) (ord ⟨Fintype.card V - 1, by omega⟩)) ∧
      (∀ (i : Fin (Fintype.card V)), 2 ≤ (i : ℕ) → (i : ℕ) < Fintype.card V - 1 →
        ∃ (j : Fin (Fintype.card V)), (i : ℕ) < (j : ℕ) ∧ G.Adj (ord i) (ord j)) := by
  let n := Fintype.card V
  let k := n - 2
  have hk_pos : 0 < k := by omega
  let S_type := {x : V // x ≠ v1 ∧ x ≠ v2}
  have h_card_S : Fintype.card S_type = k := card_subtype_ne_pair v1 v2 hv12
  let r : S_type := ⟨vn, ⟨hv1n.symm, hv2n.symm⟩⟩
  let H := G.induce {x : V | x ≠ v1 ∧ x ≠ v2}
  have h_reach_S : ∀ z : S_type, H.Reachable z r := fun ⟨u, hu⟩ => h_reach u hu.1 hu.2
  have hk_le : k ≤ Fintype.card S_type := by rw [h_card_S]
  obtain ⟨L, hlen, hnodup, ⟨hne, hlast⟩, hfwd⟩ := exists_reverse_bfs_list H r h_reach_S k hk_le hk_pos
  let f : Fin k → S_type := fun i => L.get ⟨i.1, by rw [hlen]; exact i.2⟩
  have hf_inj : Function.Injective f := by
    intro i j hij
    dsimp [f] at hij
    have h_get_inj := List.Nodup.get_inj_iff hnodup |>.mp hij
    have : (⟨i.1, by rw [hlen]; exact i.2⟩ : Fin L.length).1 = (⟨j.1, by rw [hlen]; exact j.2⟩ : Fin L.length).1 :=
      congrArg Fin.val h_get_inj
    exact Fin.ext this
  have hf_bij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hf_inj, ?_⟩
    rw [Fintype.card_fin, h_card_S]
  let e_S : Fin k ≃ S_type := Equiv.ofBijective f hf_bij
  let ord_fn : Fin n → V := fun i =>
    if i.1 = 0 then v1
    else if i.1 = 1 then v2
    else (e_S ⟨i.1 - 2, by omega⟩).1
  have h_ord_fn_0 (h : 0 < n) : ord_fn ⟨0, h⟩ = v1 := rfl
  have h_ord_fn_1 (h : 1 < n) : ord_fn ⟨1, h⟩ = v2 := rfl
  have h_ord_fn_add2 (i' : ℕ) (h : i' + 2 < n) : ord_fn ⟨i' + 2, h⟩ = (e_S ⟨i', by omega⟩).1 := rfl
  have h_ord_inj : Function.Injective ord_fn := by
    intro i j hij
    rcases i with ⟨_ | ⟨_ | i'⟩, hi⟩ <;> rcases j with ⟨_ | ⟨_ | j'⟩, hj⟩
    · rfl
    · rw [h_ord_fn_0, h_ord_fn_1] at hij; exact False.elim (hv12 hij)
    · rw [h_ord_fn_0, h_ord_fn_add2] at hij; exact False.elim ((e_S ⟨j', by omega⟩).2.1 hij.symm)
    · rw [h_ord_fn_1, h_ord_fn_0] at hij; exact False.elim (hv12 hij.symm)
    · rfl
    · rw [h_ord_fn_1, h_ord_fn_add2] at hij; exact False.elim ((e_S ⟨j', by omega⟩).2.2 hij.symm)
    · rw [h_ord_fn_add2, h_ord_fn_0] at hij; exact False.elim ((e_S ⟨i', by omega⟩).2.1 hij)
    · rw [h_ord_fn_add2, h_ord_fn_1] at hij; exact False.elim ((e_S ⟨i', by omega⟩).2.2 hij)
    · rw [h_ord_fn_add2, h_ord_fn_add2] at hij
      have h_sub_eq : (e_S ⟨i', by omega⟩ : S_type) = e_S ⟨j', by omega⟩ := Subtype.ext hij
      have h_fin_eq := e_S.injective h_sub_eq
      have : i' = j' := congrArg Fin.val h_fin_eq
      subst this
      rfl
  have h_ord_bij : Function.Bijective ord_fn := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨h_ord_inj, ?_⟩
    rw [Fintype.card_fin]
  let ord : Fin n ≃ V := Equiv.ofBijective ord_fn h_ord_bij
  have h_ord_apply (i : Fin n) : ord i = ord_fn i := rfl
  have h_ord_0 : ord ⟨0, by omega⟩ = v1 := by rw [h_ord_apply, h_ord_fn_0]
  have h_ord_1 : ord ⟨1, by omega⟩ = v2 := by rw [h_ord_apply, h_ord_fn_1]
  have h_ord_n : ord ⟨n - 1, by omega⟩ = vn := by
    rw [h_ord_apply]
    have hn_decomp : n - 1 = (k - 1) + 2 := by omega
    have h_fin_n : (⟨n - 1, by omega⟩ : Fin n) = ⟨(k - 1) + 2, by omega⟩ := Fin.ext hn_decomp
    rw [h_fin_n, h_ord_fn_add2]
    change (f ⟨k - 1, by omega⟩).1 = vn
    dsimp [f]
    have h_eq : (⟨k - 1, by rw [hlen]; omega⟩ : Fin L.length) = ⟨L.length - 1, by omega⟩ := by
      ext; dsimp; rw [hlen]
    have h_get_last : L.get ⟨k - 1, by rw [hlen]; omega⟩ = r := by
      rw [h_eq, List.get_length_sub_one (h := by rw [hlen]; omega), hlast]
    have : (L.get ⟨k - 1, by rw [hlen]; omega⟩).1 = r.1 := congrArg Subtype.val h_get_last
    exact this
  refine ⟨ord, ?_, ?_, ?_, ?_⟩
  · rw [h_ord_0, h_ord_1]
    exact h_not_adj
  · rw [h_ord_0, h_ord_n]
    exact h_adj1
  · rw [h_ord_1, h_ord_n]
    exact h_adj2
  · intro i hi_ge2 hi_lt_last
    obtain ⟨i', hi_decomp⟩ : ∃ i', i.1 = i' + 2 := ⟨i.1 - 2, by omega⟩
    have h_fin_i : i = ⟨i' + 2, by rw [← hi_decomp]; exact i.2⟩ := Fin.ext hi_decomp
    let idx := i'
    have h_idx_lt : idx < k - 1 := by omega
    obtain ⟨j_sub, hj_sub_gt, hj_sub_lt_k, hadj_sub⟩ := hfwd idx h_idx_lt
    have hj_lt_n : j_sub + 2 < n := by omega
    let j : Fin n := ⟨j_sub + 2, hj_lt_n⟩
    have hj_gt : (i : ℕ) < (j : ℕ) := by dsimp [j]; omega
    refine ⟨j, hj_gt, ?_⟩
    have h_ord_i : ord i = (L.get ⟨idx, by rw [hlen]; omega⟩).1 := by
      have : ord i = ord ⟨i' + 2, by rw [← hi_decomp]; exact i.2⟩ := congrArg ord h_fin_i
      rw [this, h_ord_apply, h_ord_fn_add2]
      rfl
    have h_ord_j : ord j = (L.get ⟨j_sub, by rw [hlen]; exact hj_sub_lt_k⟩).1 := by
      rw [h_ord_apply, h_ord_fn_add2]
      rfl
    rw [h_ord_i, h_ord_j]
    exact hadj_sub

lemma exists_triple_of_not_complete (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_conn : G.Preconnected)
    (h_not_clique : ¬ IsCompleteGraph G) :
    ∃ v1 v2 vn : V, v1 ≠ v2 ∧ v1 ≠ vn ∧ v2 ≠ vn ∧
      ¬ G.Adj v1 v2 ∧ G.Adj v1 vn ∧ G.Adj v2 vn := by
  have h_exists : ∃ a b : V, a ≠ b ∧ ¬ G.Adj a b := by
    by_contra! h_all
    exact h_not_clique (fun u v huv => h_all u v huv)
  obtain ⟨a, b, hab, h_not_adj⟩ := h_exists
  have hr : G.Reachable a b := h_conn a b
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  cases p with
  | nil =>
    exact False.elim (hab rfl)
  | cons hadj1 p' =>
    cases p' with
    | nil =>
      exact False.elim (h_not_adj hadj1)
    | cons hadj2 p'' =>
      refine ⟨a, _, _, ?_, ?_, ?_, ?_, hadj1, hadj2.symm⟩
      · intro h_eq
        subst h_eq
        have h_le := G.dist_le p''
        have h_len_p : (SimpleGraph.Walk.cons hadj1 (SimpleGraph.Walk.cons hadj2 p'')).length = p''.length + 2 := rfl
        rw [← hp, h_len_p] at h_le
        omega
      · exact G.ne_of_adj hadj1
      · exact (G.ne_of_adj hadj2).symm
      · intro hadj_a_v2
        have h_le := G.dist_le (SimpleGraph.Walk.cons hadj_a_v2 p'')
        have h_len_w : (SimpleGraph.Walk.cons hadj_a_v2 p'').length = p''.length + 1 := rfl
        have h_len_p : (SimpleGraph.Walk.cons hadj1 (SimpleGraph.Walk.cons hadj2 p'')).length = p''.length + 2 := rfl
        rw [← hp, h_len_w, h_len_p] at h_le
        omega

lemma score_injective (d : V → ℕ) (n : ℕ) (hn : Fintype.card V = n) :
    Function.Injective (fun (x : V) => (n - d x) * (n + 1) + (Fintype.equivFin V x : ℕ)) := by
  intro x y hxy
  have hx_lt : (Fintype.equivFin V x : ℕ) < n + 1 := by
    have := (Fintype.equivFin V x).isLt
    omega
  have hy_lt : (Fintype.equivFin V y : ℕ) < n + 1 := by
    have := (Fintype.equivFin V y).isLt
    omega
  have h_val : (Fintype.equivFin V x : ℕ) = (Fintype.equivFin V y : ℕ) := by
    have h1 : ((n - d x) * (n + 1) + (Fintype.equivFin V x : ℕ)) % (n + 1) =
              ((n - d y) * (n + 1) + (Fintype.equivFin V y : ℕ)) % (n + 1) := congrArg (· % (n + 1)) hxy
    rw [Nat.mul_add_mod_self_right, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hx_lt, Nat.mod_eq_of_lt hy_lt] at h1
    exact h1
  have h_fin : Fintype.equivFin V x = Fintype.equivFin V y := Fin.ext h_val
  exact (Fintype.equivFin V).injective h_fin

lemma score_lt_of_dist_gt (dx dy n a b : ℕ) (hn : dx ≤ n) (hdy : dy < dx) (ha : a < n + 1) :
    (n - dx) * (n + 1) + a < (n - dy) * (n + 1) + b := by
  have h1 : n - dx + 1 ≤ n - dy := by omega
  have h2 : (n - dx) * (n + 1) + a < (n - dx + 1) * (n + 1) := by
    calc
      (n - dx) * (n + 1) + a < (n - dx) * (n + 1) + (n + 1) := by omega
      _ = (n - dx + 1) * (n + 1) := by ring
  have h3 : (n - dx + 1) * (n + 1) ≤ (n - dy) * (n + 1) := Nat.mul_le_mul_right (n + 1) h1
  omega

lemma dist_zero_iff (G : SimpleGraph V) {u v : V} (hr : G.Reachable u v) :
    G.dist u v = 0 ↔ u = v := by
  rw [G.dist_eq_zero_iff_eq_or_not_reachable]
  simp [hr]

lemma dist_le_card (G : SimpleGraph V) (u v : V) (hr : G.Reachable u v) :
    G.dist u v ≤ Fintype.card V := by
  obtain ⟨p⟩ := hr
  have h1 := G.dist_le p.toPath.1
  have h2 := p.toPath.2.length_lt
  omega

lemma not_mem_pair_of_dist_ge_three (G : SimpleGraph V) (u v1 v2 vn w : V)
    (h_adj1 : G.Adj v1 vn) (h_adj2 : G.Adj v2 vn)
    (hadj_uw : G.Adj u w)
    (h_ge3 : 3 ≤ G.dist u vn) :
    w ≠ v1 ∧ w ≠ v2 := by
  constructor
  · intro heq
    subst heq
    have hle := G.dist_le (Walk.cons hadj_uw (Walk.cons h_adj1 Walk.nil))
    change G.dist u vn ≤ 2 at hle
    omega
  · intro heq
    subst heq
    have hle := G.dist_le (Walk.cons hadj_uw (Walk.cons h_adj2 Walk.nil))
    change G.dist u vn ≤ 2 at hle
    omega

/-- **Lovász Ordering for Brooks' Theorem (1975)**:
    For any connected simple graph $G$ that is not a clique, not an odd cycle,
    and has $|V| > \Delta + 1$, there exists an ordering of the vertices
    $v_1, v_2, \dots, v_n$ such that $v_1 \not\sim v_2$, $v_1 \sim v_n$, $v_2 \sim v_n$,
    and every intermediate vertex $v_i$ ($2 \le i \le n-2$) has at least one forward neighbor.
    (Constructive proof via 2-connected block reduction and reverse BFS on $G \setminus \{v_1, v_2\}$). -/
axiom exists_lovasz_ordering (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_conn : G.Preconnected)
    (h_deg_pos : 1 ≤ maxDegree G)
    (h_not_clique : ¬ IsCompleteGraph G)
    (h_not_odd_cycle : ¬ (maxDegree G = 2 ∧ IsOddCycle G))
    (h_gt : maxDegree G + 1 < Fintype.card V) :
    ∃ (ord : Fin (Fintype.card V) ≃ V),
      (¬ G.Adj (ord ⟨0, by omega⟩) (ord ⟨1, by omega⟩)) ∧
      (G.Adj (ord ⟨0, by omega⟩) (ord ⟨Fintype.card V - 1, by omega⟩)) ∧
      (G.Adj (ord ⟨1, by omega⟩) (ord ⟨Fintype.card V - 1, by omega⟩)) ∧
      (∀ (i : Fin (Fintype.card V)), 2 ≤ (i : ℕ) → (i : ℕ) < Fintype.card V - 1 →
        ∃ (j : Fin (Fintype.card V)), (i : ℕ) < (j : ℕ) ∧ G.Adj (ord i) (ord j))

end BrooksTheorem
