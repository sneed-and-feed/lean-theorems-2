import Formalization.BrooksTheorem.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Finset SimpleGraph

/-!
# Brooks' Theorem — Greedy and Ordered Graph Colorings

This module formalizes greedy vertex coloring theorems and ordering lemmas:
- `card_image_erase_le`: Set-theoretic inequality for color collision.
- `colorable_of_ordered_degree_lt`: Greedy coloring when vertices have $< k$ predecessors.
- `colorable_of_lovasz_ordering`: Lovász's ordering coloring lemma (1975) giving a $k$-coloring
  for $k \ge \Delta(G)$ given a Lovász triple ordering.
- `exists_partial_coloring` and `greedy_coloring_bound`: Classical $\Delta + 1$ greedy coloring bound.
- `chromaticNumber_le_maxDegree_succ`: Bound $\chi(G) \le \Delta(G) + 1$ on the chromatic number.
-/

namespace BrooksTheorem

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma card_image_erase_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → β) (u v : α) (hu : u ∈ s) (hv : v ∈ s) (hne : u ≠ v) (heq : f u = f v) :
    (s.image f).card ≤ s.card - 1 := by
  have h_eq : s.image f = (s.erase v).image f := by
    ext b
    simp only [Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨x, hx, rfl⟩
      by_cases hxv : x = v
      · subst hxv
        refine ⟨u, ⟨hne, hu⟩, heq⟩
      · refine ⟨x, ⟨hxv, hx⟩, rfl⟩
    · rintro ⟨x, ⟨-, hx⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
  rw [h_eq]
  have h1 : ((s.erase v).image f).card ≤ (s.erase v).card := Finset.card_image_le
  have h2 : (s.erase v).card = s.card - 1 := Finset.card_erase_of_mem hv
  omega

/-- If vertices can be ordered such that every vertex has fewer than `k` previously
    colored neighbors in the ordering, then the graph is `k`-colorable. -/
lemma colorable_of_ordered_degree_lt (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : 0 < k)
    (ord : Fin (Fintype.card V) ≃ V)
    (h_deg : ∀ i : Fin (Fintype.card V),
      ((Finset.univ.filter (fun j : Fin (Fintype.card V) => (j : ℕ) < (i : ℕ) ∧ G.Adj (ord i) (ord j))).card < k)) :
    IsKColorable G k := by
  have h_ind : ∀ m ≤ Fintype.card V,
      ∃ c : V → Fin k, ∀ (i j : Fin (Fintype.card V)),
        (i : ℕ) < m → (j : ℕ) < m → G.Adj (ord i) (ord j) → c (ord i) ≠ c (ord j) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨fun _ => ⟨0, hk⟩, ?_⟩
      intro i j hi
      omega
    | succ m ih =>
      intro hm
      have hm_le : m ≤ Fintype.card V := by omega
      obtain ⟨c, hc⟩ := ih hm_le
      let idx : Fin (Fintype.card V) := ⟨m, by omega⟩
      let x := ord idx
      let prev_neighbors := Finset.univ.filter (fun j : Fin (Fintype.card V) => (j : ℕ) < m ∧ G.Adj x (ord j))
      let used_colors := prev_neighbors.image (fun j => c (ord j))
      have h_card_prev : prev_neighbors.card < k := by
        have := h_deg idx
        exact this
      have h_card_used : used_colors.card < (Finset.univ : Finset (Fin k)).card := by
        have h1 : used_colors.card ≤ prev_neighbors.card := Finset.card_image_le
        rw [Finset.card_univ, Fintype.card_fin]
        omega
      obtain ⟨col, -, h_not_used⟩ := Finset.exists_mem_notMem_of_card_lt_card h_card_used
      let c' : V → Fin k := Function.update c x col
      refine ⟨c', ?_⟩
      intro i j hi hj hadj
      have hi_cases : (i : ℕ) < m ∨ (i : ℕ) = m := by omega
      have hj_cases : (j : ℕ) < m ∨ (j : ℕ) = m := by omega
      rcases hi_cases with hi_lt | hi_eq
      · rcases hj_cases with hj_lt | hj_eq
        · have hi_ne : ord i ≠ x := by
            intro heq
            have := ord.injective heq
            have : (i : ℕ) = m := by simpa [idx] using congrArg Fin.val this
            omega
          have hj_ne : ord j ≠ x := by
            intro heq
            have := ord.injective heq
            have : (j : ℕ) = m := by simpa [idx] using congrArg Fin.val this
            omega
          have hc'i : c' (ord i) = c (ord i) := Function.update_of_ne hi_ne col c
          have hc'j : c' (ord j) = c (ord j) := Function.update_of_ne hj_ne col c
          rw [hc'i, hc'j]
          exact hc i j hi_lt hj_lt hadj
        · have hi_ne : ord i ≠ x := by
            intro heq
            have := ord.injective heq
            have : (i : ℕ) = m := by simpa [idx] using congrArg Fin.val this
            omega
          have hj_x : ord j = x := by
            have : j = idx := Fin.ext hj_eq
            rw [this]
          have hc'i : c' (ord i) = c (ord i) := Function.update_of_ne hi_ne col c
          have hc'j : c' (ord j) = col := by rw [hj_x]; exact Function.update_self x col c
          rw [hc'i, hc'j]
          intro heq
          apply h_not_used
          rw [Finset.mem_image]
          refine ⟨i, ?_, heq⟩
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ i, ⟨hi_lt, ?_⟩⟩
          rw [← hj_x]
          exact G.adj_symm hadj
      · rcases hj_cases with hj_lt | hj_eq
        · have hj_ne : ord j ≠ x := by
            intro heq
            have := ord.injective heq
            have : (j : ℕ) = m := by simpa [idx] using congrArg Fin.val this
            omega
          have hi_x : ord i = x := by
            have : i = idx := Fin.ext hi_eq
            rw [this]
          have hc'j : c' (ord j) = c (ord j) := Function.update_of_ne hj_ne col c
          have hc'i : c' (ord i) = col := by rw [hi_x]; exact Function.update_self x col c
          rw [hc'i, hc'j]
          intro heq
          apply h_not_used
          rw [Finset.mem_image]
          refine ⟨j, ?_, heq.symm⟩
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ j, ⟨hj_lt, ?_⟩⟩
          rw [← hi_x]
          exact hadj
        · have hi_eq_j : i = j := Fin.ext (by omega)
          subst hi_eq_j
          exact False.elim (G.irrefl hadj)
  obtain ⟨c, hc⟩ := h_ind (Fintype.card V) (le_refl _)
  refine ⟨c, ?_⟩
  intro u v hadj
  have hu_eq : u = ord (ord.symm u) := (ord.apply_symm_apply u).symm
  have hv_eq : v = ord (ord.symm v) := (ord.apply_symm_apply v).symm
  rw [hu_eq, hv_eq] at hadj ⊢
  exact hc (ord.symm u) (ord.symm v) (ord.symm u).isLt (ord.symm v).isLt hadj

/-- **Lovász's Ordering Lemma (1975):**
    If vertices are ordered such that the first two vertices $v_1, v_2$ are non-adjacent
    and share a common neighbor $v_n$ (the last vertex), and every intermediate vertex $v_i$
    ($2 \le i \le n-2$) has at least one forward neighbor ($j > i$),
    then $G$ is $k$-colorable for any $k \ge \Delta(G)$ with $k \ge 1$. -/
lemma colorable_of_lovasz_ordering (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : 1 ≤ k)
    (h_deg_k : maxDegree G ≤ k)
    (ord : Fin (Fintype.card V) ≃ V)
    (h_card : 3 ≤ Fintype.card V)
    (h_not_adj_01 : ¬ G.Adj (ord ⟨0, by omega⟩) (ord ⟨1, by omega⟩))
    (h_adj_0n : G.Adj (ord ⟨0, by omega⟩) (ord ⟨Fintype.card V - 1, by omega⟩))
    (h_adj_1n : G.Adj (ord ⟨1, by omega⟩) (ord ⟨Fintype.card V - 1, by omega⟩))
    (h_fwd : ∀ (i : Fin (Fintype.card V)), 2 ≤ (i : ℕ) → (i : ℕ) < Fintype.card V - 1 →
      ∃ (j : Fin (Fintype.card V)), (i : ℕ) < (j : ℕ) ∧ G.Adj (ord i) (ord j)) :
    IsKColorable G k := by
  have h_pos : 0 < Fintype.card V := by omega
  let zero_idx : Fin (Fintype.card V) := ⟨0, h_pos⟩
  let one_idx : Fin (Fintype.card V) := ⟨1, by omega⟩
  let last_idx : Fin (Fintype.card V) := ⟨Fintype.card V - 1, by omega⟩
  let v1 := ord zero_idx
  let v2 := ord one_idx
  let vn := ord last_idx
  have h_ind : ∀ m ≤ Fintype.card V,
      ∃ c : V → Fin k, (c v1 = ⟨0, hk⟩) ∧ (c v2 = ⟨0, hk⟩) ∧
        ∀ (i j : Fin (Fintype.card V)), (i : ℕ) < m → (j : ℕ) < m → G.Adj (ord i) (ord j) → c (ord i) ≠ c (ord j) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨fun _ => ⟨0, hk⟩, rfl, rfl, ?_⟩
      intro i j hi
      omega
    | succ m ih =>
      intro hm
      have hm_le : m ≤ Fintype.card V := by omega
      obtain ⟨c, hc_v1, hc_v2, hc⟩ := ih hm_le
      by_cases hm_lt2 : m < 2
      · refine ⟨c, hc_v1, hc_v2, ?_⟩
        intro i j hi hj hadj
        have hi_le : (i : ℕ) ≤ 1 := by omega
        have hj_le : (j : ℕ) ≤ 1 := by omega
        have hi_cases : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by omega
        have hj_cases : (j : ℕ) = 0 ∨ (j : ℕ) = 1 := by omega
        rcases hi_cases with hi0 | hi1 <;> rcases hj_cases with hj0 | hj1
        · have : i = j := Fin.ext (by omega)
          subst this
          exact False.elim (G.irrefl hadj)
        · have hi_eq : i = zero_idx := Fin.ext hi0
          have hj_eq : j = one_idx := Fin.ext hj1
          rw [hi_eq, hj_eq] at hadj
          exact False.elim (h_not_adj_01 hadj)
        · have hi_eq : i = one_idx := Fin.ext hi1
          have hj_eq : j = zero_idx := Fin.ext hj0
          rw [hi_eq, hj_eq] at hadj
          exact False.elim (h_not_adj_01 (G.adj_symm hadj))
        · have : i = j := Fin.ext (by omega)
          subst this
          exact False.elim (G.irrefl hadj)
      · by_cases hm_last : m = Fintype.card V - 1
        · let idx_n : Fin (Fintype.card V) := ⟨m, by omega⟩
          let x := ord idx_n
          have h_idx_eq : idx_n = last_idx := Fin.ext hm_last
          have hx_vn : x = vn := by dsimp [x, vn]; rw [h_idx_eq]
          let neighbor_colors := (G.neighborFinset x).image c
          have hv1_mem : v1 ∈ G.neighborFinset x := by
            rw [hx_vn]
            exact (G.mem_neighborFinset vn v1).mpr (G.adj_symm h_adj_0n)
          have hv2_mem : v2 ∈ G.neighborFinset x := by
            rw [hx_vn]
            exact (G.mem_neighborFinset vn v2).mpr (G.adj_symm h_adj_1n)
          have hv1_ne_v2 : v1 ≠ v2 := by
            intro heq
            have : zero_idx = one_idx := ord.injective heq
            have : (zero_idx : ℕ) = (one_idx : ℕ) := congrArg Fin.val this
            change 0 = 1 at this
            omega
          have hc_eq : c v1 = c v2 := by rw [hc_v1, hc_v2]
          have h_card_nc : neighbor_colors.card ≤ (G.neighborFinset x).card - 1 :=
            card_image_erase_le (G.neighborFinset x) c v1 v2 hv1_mem hv2_mem hv1_ne_v2 hc_eq
          have h_card_used : neighbor_colors.card < (Finset.univ : Finset (Fin k)).card := by
            rw [G.card_neighborFinset_eq_degree] at h_card_nc
            have h_deg_le := (degree_le_maxDegree G x).trans h_deg_k
            rw [Finset.card_univ, Fintype.card_fin]
            omega
          obtain ⟨col, -, h_not_used⟩ := Finset.exists_mem_notMem_of_card_lt_card h_card_used
          let c_final : V → Fin k := Function.update c x col
          have h_ne_v1 : v1 ≠ x := by
            intro heq
            have : zero_idx = idx_n := ord.injective heq
            have : (zero_idx : ℕ) = (idx_n : ℕ) := congrArg Fin.val this
            change 0 = m at this
            omega
          have h_ne_v2 : v2 ≠ x := by
            intro heq
            have : one_idx = idx_n := ord.injective heq
            have : (one_idx : ℕ) = (idx_n : ℕ) := congrArg Fin.val this
            change 1 = m at this
            omega
          have hc'_v1 : c_final v1 = ⟨0, hk⟩ := by
            dsimp [c_final]
            rw [Function.update_of_ne h_ne_v1 col c, hc_v1]
          have hc'_v2 : c_final v2 = ⟨0, hk⟩ := by
            dsimp [c_final]
            rw [Function.update_of_ne h_ne_v2 col c, hc_v2]
          refine ⟨c_final, hc'_v1, hc'_v2, ?_⟩
          intro i j hi hj hadj
          have hi_cases : (i : ℕ) < m ∨ (i : ℕ) = m := by omega
          have hj_cases : (j : ℕ) < m ∨ (j : ℕ) = m := by omega
          rcases hi_cases with hi_lt | hi_eq
          · rcases hj_cases with hj_lt | hj_eq
            · have hi_ne : ord i ≠ x := by
                intro heq
                have : i = idx_n := ord.injective heq
                have : (i : ℕ) = m := by simpa [idx_n] using congrArg Fin.val this
                omega
              have hj_ne : ord j ≠ x := by
                intro heq
                have : j = idx_n := ord.injective heq
                have : (j : ℕ) = m := by simpa [idx_n] using congrArg Fin.val this
                omega
              dsimp [c_final]
              rw [Function.update_of_ne hi_ne col c, Function.update_of_ne hj_ne col c]
              exact hc i j hi_lt hj_lt hadj
            · have hi_ne : ord i ≠ x := by
                intro heq
                have : i = idx_n := ord.injective heq
                have : (i : ℕ) = m := by simpa [idx_n] using congrArg Fin.val this
                omega
              have hj_x : ord j = x := by
                have : j = idx_n := Fin.ext hj_eq
                rw [this]
              dsimp [c_final]
              rw [Function.update_of_ne hi_ne col c, hj_x, Function.update_self x col c]
              intro heq
              apply h_not_used
              rw [Finset.mem_image]
              refine ⟨ord i, ?_, heq⟩
              rw [G.mem_neighborFinset]
              rw [hj_x] at hadj
              exact G.adj_symm hadj
          · rcases hj_cases with hj_lt | hj_eq
            · have hj_ne : ord j ≠ x := by
                intro heq
                have : j = idx_n := ord.injective heq
                have : (j : ℕ) = m := by simpa [idx_n] using congrArg Fin.val this
                omega
              have hi_x : ord i = x := by
                have : i = idx_n := Fin.ext hi_eq
                rw [this]
              dsimp [c_final]
              rw [Function.update_of_ne hj_ne col c, hi_x, Function.update_self x col c]
              intro heq
              apply h_not_used
              rw [Finset.mem_image]
              refine ⟨ord j, ?_, heq.symm⟩
              rw [G.mem_neighborFinset]
              rw [hi_x] at hadj
              exact hadj
            · have : i = j := Fin.ext (by omega)
              subst this
              exact False.elim (G.irrefl hadj)
        · let idx : Fin (Fintype.card V) := ⟨m, by omega⟩
          let x := ord idx
          have h_m_ge2 : 2 ≤ (idx : ℕ) := by dsimp [idx]; omega
          have h_m_lt_last : (idx : ℕ) < Fintype.card V - 1 := by dsimp [idx]; omega
          obtain ⟨j_fwd, hj_lt, hadj_fwd⟩ := h_fwd idx h_m_ge2 h_m_lt_last
          let prev_neighbors := Finset.univ.filter (fun p : Fin (Fintype.card V) => (p : ℕ) < m ∧ G.Adj x (ord p))
          let used_colors := prev_neighbors.image (fun p => c (ord p))
          have h_sub_erase : prev_neighbors.image ord ⊆ (G.neighborFinset x).erase (ord j_fwd) := by
            intro y hy
            rw [Finset.mem_image] at hy
            obtain ⟨p, hp, rfl⟩ := hy
            rw [Finset.mem_filter] at hp
            rw [Finset.mem_erase, G.mem_neighborFinset]
            refine ⟨?_, hp.2.2⟩
            intro heq
            have hp_lt : (p : ℕ) < m := hp.2.1
            have : p = j_fwd := ord.injective heq
            have : (p : ℕ) = (j_fwd : ℕ) := congrArg Fin.val this
            have h_idx_m : (idx : ℕ) = m := rfl
            omega
          have h_fwd_mem : ord j_fwd ∈ G.neighborFinset x :=
            (G.mem_neighborFinset x (ord j_fwd)).mpr hadj_fwd
          have h_card_prev : prev_neighbors.card ≤ k - 1 := by
            have h_img_card : (prev_neighbors.image ord).card = prev_neighbors.card :=
              Finset.card_image_of_injective prev_neighbors ord.injective
            have h_sub_card := Finset.card_le_card h_sub_erase
            rw [Finset.card_erase_of_mem h_fwd_mem, G.card_neighborFinset_eq_degree] at h_sub_card
            have h_deg_le := (degree_le_maxDegree G x).trans h_deg_k
            omega
          have h_card_used : used_colors.card < (Finset.univ : Finset (Fin k)).card := by
            have h1 : used_colors.card ≤ prev_neighbors.card := Finset.card_image_le
            rw [Finset.card_univ, Fintype.card_fin]
            omega
          obtain ⟨col, -, h_not_used⟩ := Finset.exists_mem_notMem_of_card_lt_card h_card_used
          let c' : V → Fin k := Function.update c x col
          have h_ne_v1 : v1 ≠ x := by
            intro heq
            have : zero_idx = idx := ord.injective heq
            have : (zero_idx : ℕ) = (idx : ℕ) := congrArg Fin.val this
            change 0 = m at this
            omega
          have h_ne_v2 : v2 ≠ x := by
            intro heq
            have : one_idx = idx := ord.injective heq
            have : (one_idx : ℕ) = (idx : ℕ) := congrArg Fin.val this
            change 1 = m at this
            omega
          have hc'_v1 : c' v1 = ⟨0, hk⟩ := by
            dsimp [c']
            rw [Function.update_of_ne h_ne_v1 col c, hc_v1]
          have hc'_v2 : c' v2 = ⟨0, hk⟩ := by
            dsimp [c']
            rw [Function.update_of_ne h_ne_v2 col c, hc_v2]
          refine ⟨c', hc'_v1, hc'_v2, ?_⟩
          intro i j hi hj hadj
          have hi_cases : (i : ℕ) < m ∨ (i : ℕ) = m := by omega
          have hj_cases : (j : ℕ) < m ∨ (j : ℕ) = m := by omega
          rcases hi_cases with hi_lt | hi_eq
          · rcases hj_cases with hj_lt | hj_eq
            · have hi_ne : ord i ≠ x := by
                intro heq
                have : i = idx := ord.injective heq
                have : (i : ℕ) = m := by simpa [idx] using congrArg Fin.val this
                omega
              have hj_ne : ord j ≠ x := by
                intro heq
                have : j = idx := ord.injective heq
                have : (j : ℕ) = m := by simpa [idx] using congrArg Fin.val this
                omega
              dsimp [c']
              rw [Function.update_of_ne hi_ne col c, Function.update_of_ne hj_ne col c]
              exact hc i j hi_lt hj_lt hadj
            · have hi_ne : ord i ≠ x := by
                intro heq
                have : i = idx := ord.injective heq
                have : (i : ℕ) = m := by simpa [idx] using congrArg Fin.val this
                omega
              have hj_x : ord j = x := by
                have : j = idx := Fin.ext hj_eq
                rw [this]
              dsimp [c']
              rw [Function.update_of_ne hi_ne col c, hj_x, Function.update_self x col c]
              intro heq
              apply h_not_used
              rw [Finset.mem_image]
              refine ⟨i, ?_, heq⟩
              rw [Finset.mem_filter]
              refine ⟨Finset.mem_univ i, ⟨hi_lt, ?_⟩⟩
              rw [← hj_x]
              exact G.adj_symm hadj
          · rcases hj_cases with hj_lt | hj_eq
            · have hj_ne : ord j ≠ x := by
                intro heq
                have : j = idx := ord.injective heq
                have : (j : ℕ) = m := by simpa [idx] using congrArg Fin.val this
                omega
              have hi_x : ord i = x := by
                have : i = idx := Fin.ext hi_eq
                rw [this]
              dsimp [c']
              rw [Function.update_of_ne hj_ne col c, hi_x, Function.update_self x col c]
              intro heq
              apply h_not_used
              rw [Finset.mem_image]
              refine ⟨j, ?_, heq.symm⟩
              rw [Finset.mem_filter]
              refine ⟨Finset.mem_univ j, ⟨hj_lt, ?_⟩⟩
              rw [← hi_x]
              exact hadj
            · have : i = j := Fin.ext (by omega)
              subst this
              exact False.elim (G.irrefl hadj)
  obtain ⟨c, -, -, hc⟩ := h_ind (Fintype.card V) (le_refl _)
  refine ⟨c, ?_⟩
  intro u v hadj
  have hu_eq : u = ord (ord.symm u) := (ord.apply_symm_apply u).symm
  have hv_eq : v = ord (ord.symm v) := (ord.apply_symm_apply v).symm
  rw [hu_eq, hv_eq] at hadj ⊢
  exact hc (ord.symm u) (ord.symm v) (ord.symm u).isLt (ord.symm v).isLt hadj

lemma exists_partial_coloring (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) :
    ∃ c : V → Fin (maxDegree G + 1), ∀ u ∈ s, ∀ v ∈ s, G.Adj u v → c u ≠ c v := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => ⟨0, Nat.succ_pos _⟩, ?_⟩
    intro u hu
    simp at hu
  | insert x s hx ih =>
    obtain ⟨c, hc⟩ := ih
    let neighbors_in_s := s.filter (fun y => G.Adj x y)
    let used_colors := neighbors_in_s.image c
    have h_sub : neighbors_in_s ⊆ G.neighborFinset x := by
      intro y hy
      rw [Finset.mem_filter] at hy
      exact (G.mem_neighborFinset x y).mpr hy.2
    have h_card_neighbors : neighbors_in_s.card ≤ G.degree x := by
      have h1 := Finset.card_le_card h_sub
      rwa [G.card_neighborFinset_eq_degree x] at h1
    have h_card_used : used_colors.card ≤ maxDegree G := by
      have h1 : used_colors.card ≤ neighbors_in_s.card := Finset.card_image_le
      have h2 := degree_le_maxDegree G x
      omega
    have h_univ_card : (Finset.univ : Finset (Fin (maxDegree G + 1))).card = maxDegree G + 1 := by
      exact Fintype.card_fin (maxDegree G + 1)
    have h_lt : used_colors.card < (Finset.univ : Finset (Fin (maxDegree G + 1))).card := by
      omega
    obtain ⟨col, -, h_not_used⟩ := Finset.exists_mem_notMem_of_card_lt_card h_lt
    let c' : V → Fin (maxDegree G + 1) := Function.update c x col
    refine ⟨c', ?_⟩
    intro u hu v hv hadj
    by_cases hu_x : u = x
    · have hc'u : c' u = col := by rw [hu_x]; exact Function.update_self x col c
      by_cases hv_x : v = x
      · have h_uv : u = v := hu_x.trans hv_x.symm
        subst h_uv
        exact False.elim (G.irrefl hadj)
      · have hv_s : v ∈ s := (Finset.mem_insert.mp hv).resolve_left hv_x
        have hc'v : c' v = c v := Function.update_of_ne hv_x col c
        rw [hc'u, hc'v]
        intro heq
        apply h_not_used
        rw [Finset.mem_image]
        refine ⟨v, ?_, heq.symm⟩
        rw [Finset.mem_filter]
        exact ⟨hv_s, hu_x ▸ hadj⟩
    · have hu_s : u ∈ s := (Finset.mem_insert.mp hu).resolve_left hu_x
      by_cases hv_x : v = x
      · have hc'v : c' v = col := by rw [hv_x]; exact Function.update_self x col c
        have hc'u : c' u = c u := Function.update_of_ne hu_x col c
        rw [hc'u, hc'v]
        intro heq
        apply h_not_used
        rw [Finset.mem_image]
        refine ⟨u, ?_, heq⟩
        rw [Finset.mem_filter]
        exact ⟨hu_s, hv_x ▸ G.adj_symm hadj⟩
      · have hv_s : v ∈ s := (Finset.mem_insert.mp hv).resolve_left hv_x
        have hc'u : c' u = c u := Function.update_of_ne hu_x col c
        have hc'v : c' v = c v := Function.update_of_ne hv_x col c
        rw [hc'u, hc'v]
        exact hc u hu_s v hv_s hadj

/-- The classical greedy coloring theorem: any graph with maximum degree $\Delta$
    can be properly colored with $\Delta + 1$ colors. -/
theorem greedy_coloring_bound (G : SimpleGraph V) [DecidableRel G.Adj] :
    IsKColorable G (maxDegree G + 1) := by
  obtain ⟨c, hc⟩ := exists_partial_coloring G Finset.univ
  exact ⟨c, fun u v hadj => hc u (Finset.mem_univ u) v (Finset.mem_univ v) hadj⟩

/-- The chromatic number of any finite graph is bounded by its maximum degree plus one:
    $\chi(G) \le \Delta(G) + 1$. -/
lemma chromaticNumber_le_maxDegree_succ (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.chromaticNumber ≤ (maxDegree G + 1 : ℕ∞) := by
  have hcol : G.Colorable (maxDegree G + 1) :=
    (isKColorable_iff_colorable G (maxDegree G + 1)).mp (greedy_coloring_bound G)
  exact iInf₂_le (maxDegree G + 1) hcol

end BrooksTheorem
