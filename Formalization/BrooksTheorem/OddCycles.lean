import Formalization.BrooksTheorem.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open Finset SimpleGraph

/-!
# Brooks' Theorem — Exceptional Graphs (Cliques and Odd Cycles)

This module characterizes the two extremal graph families in Brooks' Theorem:
1. Complete graphs $K_n$: definition (`IsCompleteGraph`), non-colorability with $< |V|$ colors
   (`not_colorable_completeGraph`), and small graph colorability lemmas (`isKColorable_of_card_le`,
   `isKColorable_of_card_eq_succ_not_complete`).
2. Odd cycles $C_{2k+1}$: definition (`IsOddCycle`), parity/bipartite obstruction, and proof that
   odd cycles are not 2-colorable (`odd_cycle_not_two_colorable`).
-/

namespace BrooksTheorem

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A graph is complete ($K_n$) if every pair of distinct vertices is adjacent. -/
def IsCompleteGraph (G : SimpleGraph V) : Prop :=
  ∀ u v : V, u ≠ v → G.Adj u v

lemma exists_not_adj_of_not_complete (G : SimpleGraph V) (h : ¬ IsCompleteGraph G) :
    ∃ u v : V, u ≠ v ∧ ¬ G.Adj u v := by
  dsimp [IsCompleteGraph] at h
  push Not at h
  exact h

/-- Any graph on at most `k` vertices is `k`-colorable. -/
lemma isKColorable_of_card_le (G : SimpleGraph V) (k : ℕ) (h : Fintype.card V ≤ k) :
    IsKColorable G k := by
  let f : V → Fin k := fun v => (Fintype.equivFin V v).castLE h
  refine ⟨f, ?_⟩
  intro u v hadj heq
  have hne : u ≠ v := G.ne_of_adj hadj
  dsimp [f] at heq
  have hval : ((Fintype.equivFin V u).castLE h : ℕ) = ((Fintype.equivFin V v).castLE h : ℕ) :=
    congrArg Fin.val heq
  dsimp at hval
  have hequiv : Fintype.equivFin V u = Fintype.equivFin V v := Fin.ext hval
  have : u = v := (Fintype.equivFin V).injective hequiv
  exact hne this

/-- Any graph on `k + 1` vertices that is not complete is `k`-colorable (`k ≥ 1`). -/
lemma isKColorable_of_card_eq_succ_not_complete (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (hk : 1 ≤ k) (h_card : Fintype.card V = k + 1) (h_not_comp : ¬ IsCompleteGraph G) :
    IsKColorable G k := by
  obtain ⟨u, v, h_ne, h_not_adj⟩ := exists_not_adj_of_not_complete G h_not_comp
  let S : Finset V := (Finset.univ.erase u).erase v
  have hu_notin_S : u ∉ S := by
    intro h
    rw [Finset.mem_erase, Finset.mem_erase] at h
    exact h.2.1 rfl
  have hv_notin_S : v ∉ S := by
    intro h
    rw [Finset.mem_erase] at h
    exact h.1 rfl
  have h_card_S : S.card = k - 1 := by
    have hu_mem : u ∈ (Finset.univ : Finset V) := Finset.mem_univ u
    have hv_mem : v ∈ (Finset.univ : Finset V).erase u := by
      rw [Finset.mem_erase]
      exact ⟨h_ne.symm, Finset.mem_univ v⟩
    have h1 : ((Finset.univ : Finset V).erase u).card = Fintype.card V - 1 :=
      Finset.card_erase_of_mem hu_mem
    have h2 : S.card = ((Finset.univ : Finset V).erase u).card - 1 :=
      Finset.card_erase_of_mem hv_mem
    omega
  let S_type := { x : V // x ∈ S }
  haveI : Fintype S_type := Subtype.fintype (fun x => x ∈ S)
  have h_card_Stype : Fintype.card S_type = k - 1 := by
    rw [Fintype.card_coe, h_card_S]
  let e : S_type ≃ Fin (k - 1) := Fintype.equivFin S_type |>.trans (Fin.castOrderIso h_card_Stype).toEquiv
  let c : V → Fin k := fun x =>
    if hx : x = u ∨ x = v then
      ⟨0, hk⟩
    else
      have hxS : x ∈ S := by
        push Not at hx
        rw [Finset.mem_erase, Finset.mem_erase]
        exact ⟨hx.2, ⟨hx.1, Finset.mem_univ x⟩⟩
      let sx : S_type := ⟨x, hxS⟩
      ⟨(e sx : ℕ) + 1, by
        have : (e sx : ℕ) < k - 1 := (e sx).isLt
        omega⟩
  refine ⟨c, ?_⟩
  intro x y hadj
  have hxy_ne : x ≠ y := G.ne_of_adj hadj
  dsimp [c]
  split_ifs with hx hy hy
  · rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact False.elim (G.irrefl hadj)
    · exact False.elim (h_not_adj hadj)
    · exact False.elim (h_not_adj (G.adj_symm hadj))
    · exact False.elim (G.irrefl hadj)
  · intro heq
    have h_val : 0 = (e ⟨y, _⟩ : ℕ) + 1 := congrArg Fin.val heq
    omega
  · intro heq
    have h_val : (e ⟨x, _⟩ : ℕ) + 1 = 0 := congrArg Fin.val heq
    omega
  · intro heq
    injection heq with h_inj
    have hxS : x ∈ S := by
      push Not at hx
      rw [Finset.mem_erase, Finset.mem_erase]
      exact ⟨hx.2, ⟨hx.1, Finset.mem_univ x⟩⟩
    have hyS : y ∈ S := by
      push Not at hy
      rw [Finset.mem_erase, Finset.mem_erase]
      exact ⟨hy.2, ⟨hy.1, Finset.mem_univ y⟩⟩
    have hx_eq : (⟨x, _⟩ : S_type) = ⟨x, hxS⟩ := Subtype.ext rfl
    have hy_eq : (⟨y, _⟩ : S_type) = ⟨y, hyS⟩ := Subtype.ext rfl
    rw [hx_eq, hy_eq] at h_inj
    have h_eval : (e ⟨x, hxS⟩ : ℕ) = (e ⟨y, hyS⟩ : ℕ) := by omega
    have he_eq : e ⟨x, hxS⟩ = e ⟨y, hyS⟩ := Fin.ext h_eval
    have h_sub_eq : (⟨x, hxS⟩ : S_type) = ⟨y, hyS⟩ := e.injective he_eq
    have : x = y := Subtype.ext_iff.mp h_sub_eq
    exact hxy_ne this

/-- If two non-adjacent vertices $u, v$ are identified via the quotient map
    $\pi(x) = \text{if } x = v \text{ then } u \text{ else } x$, any proper coloring
    of the merged graph pulls back to a proper coloring of the original graph $G$. -/
lemma properColoring_of_pullback (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (u v : V) (h_ne : u ≠ v) (h_not_adj : ¬ G.Adj u v)
    (c : V → Fin k)
    (hc : ∀ x y : V, x ≠ y →
      (∃ a b, (if a = v then u else a) = x ∧ (if b = v then u else b) = y ∧ G.Adj a b) → c x ≠ c y) :
    IsProperColoring G (fun x => c (if x = v then u else x)) := by
  intro a b hadj
  let pi := fun x : V => if x = v then u else x
  have h_pi_ne : pi a ≠ pi b := by
    intro h_eq
    have h_pia : pi a = if a = v then u else a := rfl
    have h_pib : pi b = if b = v then u else b := rfl
    rw [h_pia, h_pib] at h_eq
    by_cases ha : a = v <;> by_cases hb : b = v
    · subst ha; subst hb; exact False.elim (G.irrefl hadj)
    · simp only [ha, hb, ↓reduceIte] at h_eq
      have h_vb : G.Adj v b := ha ▸ hadj
      have h_vu : G.Adj v u := h_eq ▸ h_vb
      exact False.elim (h_not_adj (G.adj_symm h_vu))
    · simp only [ha, hb, ↓reduceIte] at h_eq
      have h_av : G.Adj a v := hb ▸ hadj
      have h_uv : G.Adj u v := h_eq ▸ h_av
      exact False.elim (h_not_adj h_uv)
    · simp only [ha, hb, ↓reduceIte] at h_eq
      exact False.elim (hadj.ne h_eq)
  exact hc (pi a) (pi b) h_pi_ne ⟨a, b, rfl, rfl, hadj⟩

/-- A proper coloring of a complete graph must assign distinct colors to every vertex. -/
lemma completeGraph_coloring_injective (G : SimpleGraph V) {k : ℕ} (h_comp : IsCompleteGraph G)
    (c : V → Fin k) (hc : IsProperColoring G c) : Function.Injective c := by
  intro u v heq
  by_contra hne
  have hadj := h_comp u v hne
  exact hc u v hadj heq

/-- Complete graph on $n$ vertices requires at least $n$ colors. -/
lemma completeGraph_card_le_of_properColoring (G : SimpleGraph V) {k : ℕ} (h_comp : IsCompleteGraph G)
    (c : V → Fin k) (hc : IsProperColoring G c) : Fintype.card V ≤ k := by
  have hinj := completeGraph_coloring_injective G h_comp c hc
  have hle := Fintype.card_le_of_injective c hinj
  rwa [Fintype.card_fin] at hle

/-- A complete graph cannot be colored with fewer than $|V|$ colors. -/
lemma not_colorable_completeGraph (G : SimpleGraph V) {k : ℕ} (h_comp : IsCompleteGraph G)
    (hk : k < Fintype.card V) : ¬ IsKColorable G k := by
  rintro ⟨c, hc⟩
  have := completeGraph_card_le_of_properColoring G h_comp c hc
  omega

/-- A graph is an odd cycle $C_{2k+1}$. -/
def IsOddCycle (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  Odd (Fintype.card V) ∧ (∀ v : V, G.degree v = 2) ∧ G.Preconnected

lemma fin2_cases (y : Fin 2) : y = 0 ∨ y = 1 := by
  revert y
  decide

/-- An odd cycle is not 2-colorable (requires at least 3 colors). -/
lemma odd_cycle_not_two_colorable (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_odd : IsOddCycle G) : ¬ IsKColorable G 2 := by
  rintro ⟨c, hc⟩
  let V0 := Finset.univ.filter (fun v => c v = 0)
  let V1 := Finset.univ.filter (fun v => c v = 1)
  have h_disj : Disjoint V0 V1 := by
    rw [Finset.disjoint_filter]
    intro x _ h0 h1
    have h_ne : (0 : Fin 2) ≠ 1 := by decide
    exact h_ne (h0.symm.trans h1)
  have h_union : V0 ∪ V1 = Finset.univ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, V0, V1]
    exact iff_true_intro (fin2_cases (c x))
  have h_card_sum : V0.card + V1.card = Fintype.card V := by
    rw [← Finset.card_union_of_disjoint h_disj, h_union, Finset.card_univ]
  have h_neighbors_0 : ∀ u ∈ V0, ∀ w ∈ G.neighborFinset u, w ∈ V1 := by
    intro u hu w hw
    rw [Finset.mem_filter] at hu
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ w, ?_⟩
    have hadj := (G.mem_neighborFinset u w).mp hw
    have hc_ne := hc u w hadj
    have hc_u : c u = 0 := hu.2
    rcases fin2_cases (c w) with h0 | h1
    · rw [hc_u, h0] at hc_ne
      exact False.elim (hc_ne rfl)
    · exact h1
  have h_neighbors_1 : ∀ w ∈ V1, ∀ u ∈ G.neighborFinset w, u ∈ V0 := by
    intro w hw u hu
    rw [Finset.mem_filter] at hw
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ u, ?_⟩
    have hadj := (G.mem_neighborFinset w u).mp hu
    have hc_ne := hc w u hadj
    have hc_w : c w = 1 := hw.2
    rcases fin2_cases (c u) with h0 | h1
    · exact h0
    · rw [hc_w, h1] at hc_ne
      exact False.elim (hc_ne rfl)
  have h_sum0 : ∑ u ∈ V0, (G.neighborFinset u).card = 2 * V0.card := by
    have : (∑ u ∈ V0, (G.neighborFinset u).card) = ∑ u ∈ V0, 2 := by
      apply Finset.sum_congr rfl
      intro u _
      rw [G.card_neighborFinset_eq_degree]
      exact h_odd.2.1 u
    rw [this, Finset.sum_const, smul_eq_mul, mul_comm]
  have h_sum1 : ∑ w ∈ V1, (G.neighborFinset w).card = 2 * V1.card := by
    have : (∑ w ∈ V1, (G.neighborFinset w).card) = ∑ w ∈ V1, 2 := by
      apply Finset.sum_congr rfl
      intro w _
      rw [G.card_neighborFinset_eq_degree]
      exact h_odd.2.1 w
    rw [this, Finset.sum_const, smul_eq_mul, mul_comm]
  have h_double_sum : (∑ u ∈ V0, (G.neighborFinset u).card) = (∑ w ∈ V1, (G.neighborFinset w).card) := by
    have h_lhs : (∑ u ∈ V0, (G.neighborFinset u).card) =
        ∑ u ∈ V0, ∑ w ∈ V1, (if G.Adj u w then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro u hu
      have h_sub : G.neighborFinset u ⊆ V1 := h_neighbors_0 u hu
      have h_filter : (G.neighborFinset u) = V1.filter (fun w => G.Adj u w) := by
        ext w
        simp only [Finset.mem_filter, G.mem_neighborFinset]
        constructor
        · intro hw
          exact ⟨h_sub ((G.mem_neighborFinset u w).mpr hw), hw⟩
        · intro ⟨_, hw⟩
          exact hw
      rw [h_filter, Finset.card_eq_sum_ones, Finset.sum_filter]
    have h_rhs : (∑ w ∈ V1, (G.neighborFinset w).card) =
        ∑ w ∈ V1, ∑ u ∈ V0, (if G.Adj w u then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro w hw
      have h_sub : G.neighborFinset w ⊆ V0 := h_neighbors_1 w hw
      have h_filter : (G.neighborFinset w) = V0.filter (fun u => G.Adj w u) := by
        ext u
        simp only [Finset.mem_filter, G.mem_neighborFinset]
        constructor
        · intro hu
          exact ⟨h_sub ((G.mem_neighborFinset w u).mpr hu), hu⟩
        · intro ⟨_, hu⟩
          exact hu
      rw [h_filter, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [h_lhs, h_rhs, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro w _
    by_cases hadj : G.Adj u w
    · have hadj_symm : G.Adj w u := G.adj_symm hadj
      simp [hadj, hadj_symm]
    · have hadj_symm : ¬ G.Adj w u := fun h => hadj (G.adj_symm h)
      simp [hadj, hadj_symm]
  rw [h_sum0, h_sum1] at h_double_sum
  have h_eq_card : V0.card = V1.card := by omega
  have h_even : Even (Fintype.card V) := by
    use V0.card
    omega
  have h_not_even := Nat.not_even_iff_odd.mpr h_odd.1
  exact h_not_even h_even

end BrooksTheorem
