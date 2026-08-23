import Formalization.VizingsTheorem.Bipartite

open scoped BigOperators
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Vizing's Fan Lemma and Coloring Extensions

This module formalizes Vizing fans, the fan recoloring step, fan cycles with Kempe chains,
and proves that every graph admits a proper edge coloring using $\Delta(G) + 1$ colors.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

namespace SimpleGraph

namespace PartialEdgeColoring

variable {G} {k : ℕ} (c : PartialEdgeColoring G k)

lemma exists_extended_of_fan (u : V) :
    ∀ (n : ℕ) (vs : List V) (cols : List (Fin k)) (c : PartialEdgeColoring G k)
      (hlen_vs : vs.length = n + 1)
      (hlen : cols.length = vs.length)
      (hnodup : vs.Nodup)
      (hadj : ∀ v ∈ vs, G.Adj u v)
      (hnone : ∀ (hne : vs ≠ []), c.colorOf u (vs.head hne) (hadj _ (List.head_mem hne)) = none)
      (hstep : ∀ (i : ℕ) (hi : i + 1 < vs.length),
        c.colorOf u vs[i + 1] (hadj _ (List.getElem_mem _)) = some cols[i])
      (hmiss : ∀ (i : ℕ) (hi : i < vs.length),
        cols[i] ∈ c.missingColors vs[i])
      (hend : ∀ (hne : cols ≠ []), cols.getLast hne ∈ c.missingColors u),
      ∃ c' : PartialEdgeColoring G k, c'.uncoloredEdges.card < c.uncoloredEdges.card := by
  intro n
  induction n with
  | zero =>
    intro vs cols c hlen_vs hlen _ hadj hnone _ hmiss hend
    rcases vs with _ | ⟨v₀, _ | ⟨v₁, vs'⟩⟩ <;> try cases hlen_vs
    rcases cols with _ | ⟨β₀, _ | ⟨β₁, cols'⟩⟩ <;> try cases hlen
    have hadj0 : G.Adj u v₀ := hadj v₀ (by simp)
    have hnone0 : c.colorOf u v₀ hadj0 = none := hnone (by simp)
    have hmiss0 : β₀ ∈ c.missingColors v₀ := hmiss 0 (by simp)
    have hend0 : β₀ ∈ c.missingColors u := hend (by simp)
    exact ⟨c.extendColor u v₀ hadj0 β₀ hend0 hmiss0,
      c.card_uncoloredEdges_extendColor_lt u v₀ hadj0 β₀ hend0 hmiss0 hnone0⟩
  | succ m ih =>
    intro vs cols c hlen_vs hlen hnodup hadj hnone hstep hmiss hend
    rcases vs with _ | ⟨v₀, _ | ⟨v₁, vs'⟩⟩
    · contradiction
    · simp only [List.length_cons, List.length_nil] at hlen_vs; omega
    rcases cols with _ | ⟨β₀, _ | ⟨β₁, cols'⟩⟩
    · simp only [List.length_cons, List.length_nil] at hlen; omega
    · simp only [List.length_cons, List.length_nil] at hlen; omega
    have hlen_tail : (β₁ :: cols').length = (v₁ :: vs').length := by
      simp only [List.length_cons] at hlen ⊢; omega
    have hlen_vs_tail : (v₁ :: vs').length = m + 1 := by
      simp only [List.length_cons] at hlen_vs ⊢; omega
    have hadj0 : G.Adj u v₀ := hadj v₀ (by simp)
    have hadj1 : G.Adj u v₁ := hadj v₁ (by simp)
    have hnone0 : c.colorOf u v₀ hadj0 = none := hnone (by simp)
    have hcol0 : c.colorOf u v₁ hadj1 = some β₀ := hstep 0 (by simp [hlen_vs])
    have hmiss0 : β₀ ∈ c.missingColors v₀ := hmiss 0 (by simp [hlen_vs])
    let c₁ := c.shiftStep u v₀ v₁ hadj0 hadj1 β₀ hcol0 hmiss0
    have hcard_c1 : c₁.uncoloredEdges.card = c.uncoloredEdges.card :=
      card_uncoloredEdges_shiftStep c u v₀ v₁ hadj0 hadj1 β₀ hcol0 hmiss0 hnone0
    have hnodup_cons := (List.nodup_cons.mp hnodup).2
    have h_v0_not_in : v₀ ∉ v₁ :: vs' := (List.nodup_cons.mp hnodup).1
    have hadj_tail : ∀ v ∈ v₁ :: vs', G.Adj u v := fun v hv => hadj v (List.mem_cons_of_mem _ hv)
    have hnone_tail : ∀ (hne : v₁ :: vs' ≠ []), c₁.colorOf u ((v₁ :: vs').head hne) (hadj_tail _ (List.head_mem hne)) = none := by
      intro _
      exact shiftStep_colorOf_none c u v₀ v₁ hadj0 hadj1 β₀ hcol0 hmiss0
    have hstep_tail : ∀ (i : ℕ) (hi : i + 1 < (v₁ :: vs').length),
        c₁.colorOf u (v₁ :: vs')[i + 1] (hadj_tail _ (List.getElem_mem _)) = some (β₁ :: cols')[i] := by
      intro i hi
      have hi_vs' : i < vs'.length := by simp only [List.length_cons] at hi; omega
      have h_ne1 : (⟨s(u, (v₁ :: vs')[i + 1]), hadj_tail _ (List.getElem_mem _)⟩ : G.edgeSet) ≠ ⟨s(u, v₀), hadj0⟩ :=
        mk_edge_ne_neighbor G _ hadj0 (fun heq => h_v0_not_in (heq ▸ List.mem_cons_of_mem _ (List.getElem_mem hi_vs')))
      have h_ne2 : (⟨s(u, (v₁ :: vs')[i + 1]), hadj_tail _ (List.getElem_mem _)⟩ : G.edgeSet) ≠ ⟨s(u, v₁), hadj1⟩ :=
        mk_edge_ne_neighbor G _ hadj1 (fun heq => (List.nodup_cons.mp hnodup_cons).1 (heq ▸ List.getElem_mem hi_vs'))
      rw [shiftStep_colorOf_of_ne c u v₀ v₁ _ _ hadj0 hadj1 β₀ hcol0 hmiss0 _ h_ne1 h_ne2]
      exact hstep (i + 1) (by simp only [List.length_cons] at hi ⊢; omega)
    have hmiss_tail : ∀ (i : ℕ) (hi : i < (v₁ :: vs').length),
        (β₁ :: cols')[i] ∈ c₁.missingColors (v₁ :: vs')[i] := by
      intro i hi
      have h_ne_v0 : (v₁ :: vs')[i] ≠ v₀ := fun heq => h_v0_not_in (heq ▸ List.getElem_mem (by omega))
      exact shiftStep_missing_of_ne_v c u v₀ v₁ _ hadj0 hadj1 β₀ hcol0 hmiss0 h_ne_v0 _
        (hmiss (i + 1) (by simp only [List.length_cons] at hi ⊢; omega))
    have hend_tail : ∀ (hne : β₁ :: cols' ≠ []), (β₁ :: cols').getLast hne ∈ c₁.missingColors u := by
      intro hne'
      have h_last_eq : (β₁ :: cols').getLast hne' = (β₀ :: β₁ :: cols').getLast (by simp) := rfl
      rw [h_last_eq]
      exact shiftStep_missing_u c u v₀ v₁ hadj0 hadj1 β₀ hcol0 hmiss0 _ (hend (by simp))
    obtain ⟨c', hlt⟩ := ih (v₁ :: vs') (β₁ :: cols') c₁ hlen_vs_tail hlen_tail hnodup_cons hadj_tail hnone_tail hstep_tail hmiss_tail hend_tail
    refine ⟨c', ?_⟩
    rwa [hcard_c1] at hlt

lemma exists_extended_of_fan_cycle (u : V) (n : ℕ) (vs : List V) (cols : List (Fin k))
    (c : PartialEdgeColoring G k) (α : Fin k) (j : ℕ)
    (hlen_vs : vs.length = n + 1)
    (hlen : cols.length = vs.length)
    (hnodup : vs.Nodup)
    (hadj : ∀ v ∈ vs, G.Adj u v)
    (hnone : ∀ (hne : vs ≠ []), c.colorOf u (vs.head hne) (hadj _ (List.head_mem hne)) = none)
    (hstep : ∀ (i : ℕ) (hi : i + 1 < vs.length),
      c.colorOf u vs[i + 1] (hadj _ (List.getElem_mem _)) = some cols[i])
    (hmiss : ∀ (i : ℕ) (hi : i < vs.length),
      cols[i] ∈ c.missingColors vs[i])
    (hα : α ∈ c.missingColors u)
    (hj : j < n)
    (h_cycle : cols[n]'(by rw [hlen, hlen_vs]; omega) = cols[j]'(by rw [hlen, hlen_vs]; omega))
    (h_diff : ∀ (i : ℕ) (hi : i < n), i ≠ j → cols[i]'(by rw [hlen, hlen_vs]; omega) ≠ cols[j]'(by rw [hlen, hlen_vs]; omega)) :
    ∃ c' : PartialEdgeColoring G k, c'.uncoloredEdges.card < c.uncoloredEdges.card := by
  have hj_lt_cols : j < cols.length := by rw [hlen, hlen_vs]; omega
  have hn_lt_cols : n < cols.length := by rw [hlen, hlen_vs]; omega
  have hj_lt_vs : j < vs.length := by rw [hlen_vs]; omega
  have hn_lt_vs : n < vs.length := by rw [hlen_vs]; omega
  let β : Fin k := cols[j]
  have hβ_eq : cols[n] = β := h_cycle
  have h_col_ne_α : ∀ (i : ℕ) (hi : i < n), cols[i]'(by rw [hlen, hlen_vs]; omega) ≠ α := by
    intro i hi heq
    have h_edge := hstep i (by rw [hlen_vs]; omega)
    rw [mem_missingColors_iff] at hα
    have h_ne := hα vs[i + 1] (hadj _ (List.getElem_mem (by rw [hlen_vs]; omega)))
    rw [heq] at h_edge
    exact h_ne h_edge
  have h_ne_α_β : α ≠ β := by
    have := h_col_ne_α j hj
    intro heq; exact this heq.symm
  have hmiss_j : β ∈ c.missingColors vs[j] := hmiss j hj_lt_vs
  have hmiss_n : β ∈ c.missingColors vs[n] := by
    have := hmiss n hn_lt_vs; rw [hβ_eq] at this; exact this
  have h_vs_ne : vs[j] ≠ vs[n] := by
    intro heq
    have heq_idx : (⟨j, hj_lt_vs⟩ : Fin vs.length) = ⟨n, hn_lt_vs⟩ :=
      (List.nodup_iff_injective_getElem.mp hnodup) heq
    have : j = n := Fin.ext_iff.mp heq_idx
    omega
  have h_not_reach_both := kempe_not_reachable_both c h_ne_α_β hα hmiss_j hmiss_n h_vs_ne
  let c_swap := c.kempeSwap α β u
  have h_card_swap : c_swap.uncoloredEdges.card = c.uncoloredEdges.card := by
    rw [uncoloredEdges_kempeSwap]
  have h_miss_u_swap : β ∈ c_swap.missingColors u := kempeSwap_missing_u c α β u hα
  have hnone_swap : ∀ (hne : vs ≠ []), c_swap.colorOf u (vs.head hne) (hadj _ (List.head_mem hne)) = none := by
    intro hne; exact kempeSwap_color_none c α β u _ (hnone hne)
  by_cases h_reach_j : (c.kempeGraph α β).Reachable u vs[j]
  · have hnreach_n : ¬ (c.kempeGraph α β).Reachable u vs[n] := fun h => h_not_reach_both ⟨h_reach_j, h⟩
    have hmiss_n_swap : β ∈ c_swap.missingColors vs[n] := kempeSwap_missing_v c α β u vs[n] hnreach_n hmiss_n
    have hmiss_j_swap : α ∈ c_swap.missingColors vs[j] := kempeSwap_missing_of_reachable c α β u vs[j] h_reach_j hmiss_j
    let cols' := cols.set j α
    have hlen_cols' : cols'.length = vs.length := by rw [List.length_set, hlen]
    have hstep_swap : ∀ (i : ℕ) (hi : i + 1 < vs.length),
        c_swap.colorOf u vs[i + 1] (hadj _ (List.getElem_mem _)) = some cols'[i] := by
      intro i hi
      have hi_lt_n : i < n := by rw [hlen_vs] at hi; omega
      have h_col_orig := hstep i hi
      by_cases heq_ij : i = j
      · subst heq_ij
        have : cols'[i] = α := by simp [cols', List.getElem_set]
        rw [this]
        exact kempeSwap_colorOf_alpha c α β u vs[i + 1] (hadj _ (List.getElem_mem _)) h_col_orig
      · have : cols'[i] = cols[i] := by
          have : j ≠ i := fun h => heq_ij h.symm
          simp [cols', List.getElem_set, this]
        rw [this]
        exact kempeSwap_colorOf_of_ne c α β (cols[i]) u u vs[i + 1] (hadj _ (List.getElem_mem _))
          (h_col_ne_α i hi_lt_n) (h_diff i hi_lt_n heq_ij) h_col_orig
    have hmiss_swap : ∀ (i : ℕ) (hi : i < vs.length), cols'[i] ∈ c_swap.missingColors vs[i] := by
      intro i hi
      by_cases heq_ij : i = j
      · subst heq_ij
        have : cols'[i] = α := by simp [cols', List.getElem_set]
        rw [this]; exact hmiss_j_swap
      · by_cases heq_in : i = n
        · have : cols'[i] = β := by
            have : cols'[i] = cols'[n] := by congr 1
            rw [this, List.getElem_set]
            have : j ≠ n := ne_of_lt hj
            simp [this, hβ_eq]
          rw [this]
          have : vs[i] = vs[n] := by congr 1
          rw [this]; exact hmiss_n_swap
        · have hi_lt_n : i < n := by rw [hlen_vs] at hi; omega
          have : cols'[i] = cols[i] := by
            have : j ≠ i := fun h => heq_ij h.symm
            simp [cols', List.getElem_set, this]
          rw [this]
          exact kempeSwap_missing_of_ne c α β (cols[i]) u vs[i] (h_col_ne_α i hi_lt_n) (h_diff i hi_lt_n heq_ij) (hmiss i (by rw [hlen_vs]; omega))
    have hend_swap : ∀ (hne : cols' ≠ []), cols'.getLast hne ∈ c_swap.missingColors u := by
      intro hne
      have : cols'.getLast hne = β := by
        rw [List.getLast_eq_getElem, show cols'[cols'.length - 1] = cols'[n] by congr 1; rw [hlen_cols', hlen_vs]; omega, List.getElem_set]
        have : j ≠ n := ne_of_lt hj
        simp [this, hβ_eq]
      rw [this]; exact h_miss_u_swap
    obtain ⟨c', hlt⟩ := exists_extended_of_fan u n vs cols' c_swap hlen_vs hlen_cols' hnodup hadj hnone_swap hstep_swap hmiss_swap hend_swap
    refine ⟨c', ?_⟩
    rwa [h_card_swap] at hlt
  · have hnreach_j : ¬ (c.kempeGraph α β).Reachable u vs[j] := h_reach_j
    have hmiss_j_swap : β ∈ c_swap.missingColors vs[j] := kempeSwap_missing_v c α β u vs[j] hnreach_j hmiss_j
    let vs_sub := vs.take (j + 1)
    let cols_sub := cols.take (j + 1)
    have hlen_vs_sub : vs_sub.length = j + 1 := by dsimp [vs_sub]; rw [List.length_take]; omega
    have hlen_cols_sub : cols_sub.length = vs_sub.length := by dsimp [cols_sub, vs_sub]; rw [List.length_take, List.length_take, hlen]
    have hnodup_sub : vs_sub.Nodup := List.Nodup.sublist (List.take_sublist (j + 1) vs) hnodup
    have hadj_sub : ∀ v ∈ vs_sub, G.Adj u v := fun v hv => hadj v (List.mem_of_mem_take hv)
    have hnone_swap_sub : ∀ (hne : vs_sub ≠ []), c_swap.colorOf u (vs_sub.head hne) (hadj_sub _ (List.head_mem hne)) = none := by
      intro hne
      have hne_vs : vs ≠ [] := List.ne_nil_of_length_pos (by rw [hlen_vs]; omega)
      rcases vs with _ | ⟨v₀, vs_tl⟩
      · contradiction
      · exact hnone_swap (by simp)
    have hstep_swap_sub : ∀ (i : ℕ) (hi : i + 1 < vs_sub.length),
        c_swap.colorOf u vs_sub[i + 1] (hadj_sub _ (List.getElem_mem _)) = some cols_sub[i] := by
      intro i hi
      have hi_lt_j : i < j := by rw [hlen_vs_sub] at hi; omega
      have hi_lt_n : i < n := by omega
      have h_get_vs : vs_sub[i + 1] = vs[i + 1] := List.getElem_take
      have h_get_cols : cols_sub[i] = cols[i] := List.getElem_take
      have heq_edge : (⟨s(u, vs_sub[i + 1]), hadj_sub _ (List.getElem_mem _)⟩ : G.edgeSet) = ⟨s(u, vs[i + 1]), hadj _ (List.getElem_mem (by rw [hlen_vs]; omega))⟩ := by
        ext; simp [h_get_vs]
      dsimp [colorOf] at ⊢
      rw [heq_edge, h_get_cols]
      exact kempeSwap_colorOf_of_ne c α β (cols[i]) u u vs[i + 1] (hadj _ (List.getElem_mem _))
        (h_col_ne_α i hi_lt_n) (h_diff i hi_lt_n (ne_of_lt hi_lt_j)) (hstep i (by rw [hlen_vs]; omega))
    have hmiss_swap_sub : ∀ (i : ℕ) (hi : i < vs_sub.length), cols_sub[i] ∈ c_swap.missingColors vs_sub[i] := by
      intro i hi
      have hi_le_j : i ≤ j := by rw [hlen_vs_sub] at hi; omega
      have h_get_vs : vs_sub[i] = vs[i] := List.getElem_take
      have h_get_cols : cols_sub[i] = cols[i] := List.getElem_take
      rw [h_get_vs, h_get_cols]
      by_cases heq_ij : i = j
      · subst heq_ij; exact hmiss_j_swap
      · have hi_lt_j : i < j := Nat.lt_of_le_of_ne hi_le_j heq_ij
        have hi_lt_n : i < n := by omega
        exact kempeSwap_missing_of_ne c α β (cols[i]) u vs[i] (h_col_ne_α i hi_lt_n) (h_diff i hi_lt_n heq_ij) (hmiss i (by rw [hlen_vs]; omega))
    have hend_swap_sub : ∀ (hne : cols_sub ≠ []), cols_sub.getLast hne ∈ c_swap.missingColors u := by
      intro hne
      have : cols_sub.getLast hne = β := by
        have : cols_sub.length - 1 = j := by dsimp [cols_sub]; rw [List.length_take]; omega
        rw [List.getLast_eq_getElem, show cols_sub[cols_sub.length - 1] = cols_sub[j] by congr 1, List.getElem_take]
      rw [this]; exact h_miss_u_swap
    obtain ⟨c', hlt⟩ := exists_extended_of_fan u j vs_sub cols_sub c_swap hlen_vs_sub hlen_cols_sub hnodup_sub hadj_sub hnone_swap_sub hstep_swap_sub hmiss_swap_sub hend_swap_sub
    refine ⟨c', ?_⟩
    rwa [h_card_swap] at hlt

lemma exists_extended_coloring_of_fan (u : V) (α : Fin k) (hα : α ∈ c.missingColors u) (h_max : G.maxDegree < k) :
    ∀ (N : ℕ) (n : ℕ) (vs : List V) (cols : List (Fin k))
      (_hN : Fintype.card V - vs.length = N)
      (hlen_vs : vs.length = n + 1)
      (hlen : cols.length = vs.length)
      (_hnodup : vs.Nodup)
      (hadj : ∀ v ∈ vs, G.Adj u v)
      (_hnone : ∀ (hne : vs ≠ []), c.colorOf u (vs.head hne) (hadj _ (List.head_mem hne)) = none)
      (_hstep : ∀ (i : ℕ) (hi : i + 1 < vs.length),
        c.colorOf u vs[i + 1] (hadj _ (List.getElem_mem _)) = some cols[i])
      (_hmiss : ∀ (i : ℕ) (hi : i < vs.length),
        cols[i] ∈ c.missingColors vs[i])
      (_h_diff : ∀ (i : ℕ) (hi : i < n) (j : ℕ) (hj : j < i),
        cols[i]'(by rw [hlen, hlen_vs]; omega) ≠ cols[j]'(by rw [hlen, hlen_vs]; omega)),
      ∃ c' : PartialEdgeColoring G k, c'.uncoloredEdges.card < c.uncoloredEdges.card := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro n vs cols hN hlen_vs hlen hnodup hadj hnone hstep hmiss h_diff
    have hn_lt_cols : n < cols.length := by rw [hlen, hlen_vs]; omega
    have hn_lt_vs : n < vs.length := by rw [hlen_vs]; omega
    by_cases h_miss_u : cols[n] ∈ c.missingColors u
    · have hend : ∀ (hne : cols ≠ []), cols.getLast hne ∈ c.missingColors u := by
        intro hne
        rw [List.getLast_eq_getElem]
        have : cols.length - 1 = n := by rw [hlen, hlen_vs]; omega
        have h_get : cols[cols.length - 1] = cols[n] := by congr 1
        rw [h_get]
        exact h_miss_u
      exact exists_extended_of_fan u n vs cols c hlen_vs hlen hnodup hadj hnone hstep hmiss hend
    · have hw_used : cols[n] ∈ c.usedColors u := by
        have : cols[n] ∈ (Finset.univ : Finset (Fin k)) := Finset.mem_univ _
        simpa [missingColors, Finset.mem_sdiff, this] using h_miss_u
      rw [mem_usedColors_iff] at hw_used
      obtain ⟨w, hw_adj, hw_col⟩ := hw_used
      by_cases hw_in : w ∈ vs
      · obtain ⟨m, hm_lt, hm_eq⟩ := List.getElem_of_mem hw_in
        have hm_pos : 0 < m := by
          by_contra hm0; have hm_zero : m = 0 := by omega
          have hne_vs : vs ≠ [] := List.ne_nil_of_length_pos (by rw [hlen_vs]; omega)
          have h0 := hnone hne_vs; dsimp [colorOf] at h0 hw_col
          have : (⟨s(u, vs.head hne_vs), hadj _ (List.head_mem hne_vs)⟩ : G.edgeSet) = ⟨s(u, w), hw_adj⟩ := by
            ext; simp [List.head_eq_getElem hne_vs, ← show vs[m] = vs[0] by congr 1, hm_eq]
          rw [this, hw_col] at h0; cases h0
        let j := m - 1
        have hj : j < n := by rw [hlen_vs] at hm_lt; omega
        have h_cycle : cols[n]'(by rw [hlen, hlen_vs]; omega) = cols[j]'(by rw [hlen, hlen_vs]; omega) := by
          have h_step_j := hstep j (by rw [hlen_vs]; omega)
          have h_vs_j1 : vs[j + 1] = w := by rw [show vs[j + 1] = vs[m] by congr 1; omega, hm_eq]
          dsimp [colorOf] at h_step_j hw_col
          have : (⟨s(u, vs[j + 1]), hadj _ (List.getElem_mem (by rw [hlen_vs]; omega))⟩ : G.edgeSet) = ⟨s(u, w), hw_adj⟩ := by
            ext; simp [h_vs_j1]
          rw [this, hw_col] at h_step_j; exact Option.some.inj h_step_j
        have h_diff_cycle : ∀ (i : ℕ) (hi : i < n), i ≠ j → cols[i]'(by rw [hlen, hlen_vs]; omega) ≠ cols[j]'(by rw [hlen, hlen_vs]; omega) := by
          intro i hi hne_ij
          rcases lt_or_gt_of_ne hne_ij with hlt | hgt
          · exact (h_diff j hj i hlt).symm
          · exact h_diff i hi j hgt
        exact exists_extended_of_fan_cycle u n vs cols c α j hlen_vs hlen hnodup hadj hnone hstep hmiss hα hj h_cycle h_diff_cycle
      · obtain ⟨β_next, hβ_next⟩ := exists_missingColor_of_maxDegree_lt c h_max (u := w)
        have hlen_vs' : (vs ++ [w]).length = (n + 1) + 1 := by simp [hlen_vs]
        have hlen_cols' : (cols ++ [β_next]).length = (vs ++ [w]).length := by simp [hlen, hlen_vs]
        have hnodup' : (vs ++ [w]).Nodup := by
          rw [List.nodup_append]; exact ⟨hnodup, by simp, fun a ha b hb => by simp only [List.mem_singleton] at hb; subst hb; rintro rfl; exact hw_in ha⟩
        have hadj' : ∀ v ∈ vs ++ [w], G.Adj u v := by
          intro v hv; simp only [List.mem_append, List.mem_singleton] at hv
          rcases hv with hv | rfl; exacts [hadj v hv, hw_adj]
        have hnone' : ∀ (hne : vs ++ [w] ≠ []), c.colorOf u ((vs ++ [w]).head hne) (hadj' _ (List.head_mem hne)) = none := by
          intro hne
          rcases vs with _ | ⟨v0, vs_tl⟩
          · contradiction
          · exact hnone (by simp)
        have hstep' : ∀ (i : ℕ) (hi : i + 1 < (vs ++ [w]).length),
            c.colorOf u (vs ++ [w])[i + 1] (hadj' _ (List.getElem_mem _)) = some (cols ++ [β_next])[i] := by
          intro i hi
          by_cases heq_in : i = n
          · have h_get_vs : (vs ++ [w])[i + 1] = w := by simp [heq_in, hlen_vs]
            have h_get_cols : (cols ++ [β_next])[i] = cols[n] := by simp [heq_in, List.getElem_append_left hn_lt_cols]
            dsimp [colorOf] at hw_col ⊢
            have heq_edge : (⟨s(u, (vs ++ [w])[i + 1]), hadj' _ (List.getElem_mem _)⟩ : G.edgeSet) = ⟨s(u, w), hw_adj⟩ := by ext; simp [h_get_vs]
            rw [heq_edge, h_get_cols, hw_col]
          · have hi_lt_n : i < n := by omega
            have h_get_vs : (vs ++ [w])[i + 1] = vs[i + 1] := List.getElem_append_left (by omega)
            have h_get_cols : (cols ++ [β_next])[i] = cols[i] := List.getElem_append_left (by omega)
            have h_step_orig := hstep i (by omega)
            dsimp [colorOf] at h_step_orig ⊢
            have heq_edge : (⟨s(u, (vs ++ [w])[i + 1]), hadj' _ (List.getElem_mem _)⟩ : G.edgeSet) = ⟨s(u, vs[i + 1]), hadj _ (List.getElem_mem (by omega))⟩ := by
              ext; simp [h_get_vs]
            rw [heq_edge, h_get_cols, h_step_orig]
        have hmiss' : ∀ (i : ℕ) (hi : i < (vs ++ [w]).length), (cols ++ [β_next])[i] ∈ c.missingColors (vs ++ [w])[i] := by
          intro i hi
          by_cases heq_in : i = vs.length
          · have h_get_vs : (vs ++ [w])[i] = w := by simp [heq_in]
            have h_get_cols : (cols ++ [β_next])[i] = β_next := by
              have : i = cols.length := by rw [heq_in, hlen]
              simp [this]
            rw [h_get_vs, h_get_cols]; exact hβ_next
          · have hi_lt : i < vs.length := by omega
            rw [List.getElem_append_left hi_lt, List.getElem_append_left (by rw [hlen]; exact hi_lt)]
            exact hmiss i hi_lt
        have h_diff' : ∀ (i : ℕ) (hi : i < n + 1) (j : ℕ) (hj : j < i),
            (cols ++ [β_next])[i]'(by omega) ≠ (cols ++ [β_next])[j]'(by omega) := by
          intro i hi j hj
          by_cases heq_in : i = n
          · have h_get_i : (cols ++ [β_next])[i] = cols[n] := by
              have : (cols ++ [β_next])[n] = cols[n] := List.getElem_append_left hn_lt_cols
              rw [show (cols ++ [β_next])[i] = (cols ++ [β_next])[n] by congr 1, this]
            have h_get_j : (cols ++ [β_next])[j] = cols[j] := List.getElem_append_left (by omega)
            rw [h_get_i, h_get_j]
            intro heq_cols
            have h_step_j := hstep j (by omega)
            have h_step_j' : c.colorOf u vs[j + 1] (hadj _ (List.getElem_mem (by omega))) = some (cols[n]) := by rw [h_step_j, heq_cols]
            have heq_w := colorOf_inj_neighbor c u vs[j + 1] w (hadj _ (List.getElem_mem (by omega))) hw_adj (cols[n]) h_step_j' hw_col
            exact hw_in (heq_w ▸ List.getElem_mem (by omega))
          · have hi_lt_n : i < n := by omega
            rw [List.getElem_append_left (show i < cols.length by omega),
                List.getElem_append_left (show j < cols.length by omega)]
            exact h_diff i hi_lt_n j hj
        have hN' : Fintype.card V - (vs ++ [w]).length < N := by
          rw [← hN, List.length_append, List.length_singleton]
          have : (vs ++ [w]).length ≤ Fintype.card V := by rw [← List.toFinset_card_of_nodup hnodup']; exact Finset.card_le_univ _
          omega
        exact ih _ hN' (n + 1) (vs ++ [w]) (cols ++ [β_next]) rfl hlen_vs' hlen_cols' hnodup' hadj' hnone' hstep' hmiss' h_diff'

/-- Any non-empty partial edge coloring with $k > \Delta(G)$ can be extended to strictly fewer uncolored edges. -/
theorem exists_extended_coloring_vizing (h_max : G.maxDegree < k)
    (hne : c.uncoloredEdges.Nonempty) :
    ∃ c' : PartialEdgeColoring G k, c'.uncoloredEdges.card < c.uncoloredEdges.card := by
  obtain ⟨⟨e_val, he_prop⟩, he⟩ := hne
  induction e_val using Sym2.inductionOn with
  | hf u v =>
    have hadj : G.Adj u v := he_prop
    have he_none : c.colorOf u v hadj = none := by
      simp only [uncoloredEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he; exact he
    obtain ⟨α, hα⟩ := exists_missingColor_of_maxDegree_lt c h_max (u := u)
    obtain ⟨β₀, hβ₀⟩ := exists_missingColor_of_maxDegree_lt c h_max (u := v)
    have hadj_single : ∀ w ∈ [v], G.Adj u w := fun _ hw => by simp only [List.mem_singleton] at hw; subst hw; exact hadj
    have hnone_single : ∀ (hne' : [v] ≠ []), c.colorOf u ([v].head hne') (hadj_single _ (List.head_mem hne')) = none := fun _ => he_none
    have hstep_single : ∀ (i : ℕ) (hi : i + 1 < [v].length),
        c.colorOf u [v][i + 1] (hadj_single _ (List.getElem_mem _)) = some [β₀][i] := by
      intro i hi; simp only [List.length_singleton] at hi; omega
    have hmiss_single : ∀ (i : ℕ) (hi : i < [v].length),
        [β₀][i] ∈ c.missingColors [v][i] := by
      intro i hi; have : i = 0 := by simp only [List.length_singleton] at hi; omega
      subst this; exact hβ₀
    have h_diff_single : ∀ (i : ℕ) (hi : i < 0) (j : ℕ) (hj : j < i),
        [β₀][i]'(by omega) ≠ [β₀][j]'(by omega) := by intro i hi; omega
    exact c.exists_extended_coloring_of_fan u α hα h_max (Fintype.card V - 1) 0 [v] [β₀] rfl rfl rfl (List.nodup_singleton v) hadj_single hnone_single hstep_single hmiss_single h_diff_single

/-- By well-founded induction on uncolored edges, any graph admits a complete proper edge coloring with $k > \Delta(G)$ colors. -/
theorem exists_full_coloring_vizing (h_max : G.maxDegree < k)
    (c : PartialEdgeColoring G k) :
    ∃ c' : PartialEdgeColoring G k, c'.uncoloredEdges = ∅ := by
  by_cases h : c.uncoloredEdges = ∅
  · exact ⟨c, h⟩
  · obtain ⟨c', hlt⟩ := c.exists_extended_coloring_vizing h_max (Finset.nonempty_iff_ne_empty.mpr h)
    obtain ⟨c'', h''⟩ := exists_full_coloring_vizing h_max c'
    exact ⟨c'', h''⟩
termination_by c.uncoloredEdges.card

end PartialEdgeColoring

end SimpleGraph
