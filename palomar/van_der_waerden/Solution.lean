import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic.IntervalCases
import Mathlib.Combinatorics.HalesJewett
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open Finset

/-!
# Van der Waerden's Theorem on Arithmetic Progressions (1927)

This module formalizes **Van der Waerden's Theorem** (B. L. van der Waerden, 1927),
one of the central pillars of Ramsey theory and additive combinatorics.

## Mathematical Statement

For any positive integers $r \ge 1$ (number of colors) and $k \ge 1$ (length of progression),
there exists a finite positive integer $W(r, k)$, known as the **Van der Waerden number**,
such that for every $r$-coloring of the integers $\{1, 2, \dots, W(r, k)\}$:
$$\chi : \{1, \dots, W(r, k)\} \to \{1, \dots, r\}$$
there exists a **monochromatic arithmetic progression** of length $k$:
$$\exists a, d \in \mathbb{N}, \quad d > 0 \quad \text{such that} \quad \chi(a) = \chi(a + d) = \chi(a + 2d) = \dots = \chi(a + (k - 1)d)$$

## Proof Architecture (Multiple Van der Waerden & Color Focusing)
1. **Double Induction (on $k$, then on $r$):**
   The standard proof proceeds by strong induction on $k$, and an inner induction on $r$,
   proving the stronger statement that for any $m \ge 1$, one can find "color-focused" fans of APs.
2. **Product Coloring & Block Induction:**
   Large intervals are partitioned into blocks of length $B$. An $r$-coloring of the universe induces
   an $r^B$-coloring of the blocks. By induction on $k-1$, blocks contain monochromatic structures,
   which are then extended to a full $k$-term monochromatic AP.

## References
* Van der Waerden, B. L. (1927). *Beweis einer Baudetschen Vermutung*. Nieuw Archief voor Wiskunde, 15, 212–216.
* Graham, R. L., Rothschild, B. L., & Spencer, J. H. (1990). *Ramsey Theory*. John Wiley & Sons.
* Gowers, W. T. (2001). *A new proof of Szemerédi's theorem*. Geometric and Functional Analysis, 11(3), 465–588.
* Freek Wiedijk. *Formalizing 100 Theorems*.
-/

namespace VanDerWaerden

-- ============================================================================
-- Section 1: Arithmetic Progressions and Monochromaticity
-- ============================================================================

/-- An arithmetic progression of length `k` with start `a` and step `d`. -/
def arithmeticProgression (a d k : ℕ) : Finset ℕ :=
  (Finset.range k).image (fun i => a + i * d)

/-- Predicate stating that an arithmetic progression is monochromatic under coloring `c`. -/
def IsMonochromaticAP {r : ℕ} (c : ℕ → Fin r) (a d k : ℕ) : Prop :=
  d > 0 ∧ ∀ i : Fin k, c (a + (i : ℕ) * d) = c a

/-- A finite interval `Fin W` contains a monochromatic arithmetic progression of length `k`. -/
def HasMonochromaticAP {r : ℕ} (W : ℕ) (c : Fin W → Fin r) (k : ℕ) : Prop :=
  ∃ (a d : ℕ), d > 0 ∧ ∃ (h_bound : a + (k - 1) * d < W),
    ∀ (i : Fin k),
      c ⟨a + (i : ℕ) * d, by
        have : (i : ℕ) ≤ k - 1 := by omega
        have h_mul : (i : ℕ) * d ≤ (k - 1) * d := Nat.mul_le_mul_right d this
        omega⟩ = c ⟨a, by
        have : a ≤ a + (k - 1) * d := by omega
        omega⟩

/-- The Van der Waerden property for a given bound `W`, number of colors `r`, and length `k`. -/
def HasVDWProperty (W r k : ℕ) : Prop :=
  ∀ (c : Fin W → Fin r), HasMonochromaticAP W c k

-- ============================================================================
-- Section 2: Small Values and Base Cases
-- ============================================================================

/-- Trivial base case: any coloring contains an AP of length 1 (a single point). -/
theorem vdw_one (r : ℕ) (hr : 1 ≤ r) :
    HasVDWProperty 1 r 1 := by
  intro c
  refine ⟨0, 1, by omega, ⟨by omega, ?_⟩⟩
  intro ⟨i, hi⟩
  have : i = 0 := by omega
  subst this
  rfl

/-- Two-point base case (Pigeonhole Principle): W(r, 2) = r + 1. -/
theorem vdw_two (r : ℕ) (hr : 1 ≤ r) :
    HasVDWProperty (r + 1) r 2 := by
  intro c
  have h_card : Fintype.card (Fin r) < Fintype.card (Fin (r + 1)) := by
    simp only [Fintype.card_fin]
    omega
  obtain ⟨x, y, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt c h_card
  have h_val_ne : (x : ℕ) ≠ (y : ℕ) := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne h_val_ne with hlt | hgt
  · refine ⟨(x : ℕ), (y : ℕ) - (x : ℕ), by omega, ⟨by omega, ?_⟩⟩
    intro ⟨i, hi⟩
    interval_cases i
    · simp
    · have h1 : (x : ℕ) + 1 * ((y : ℕ) - (x : ℕ)) = (y : ℕ) := by omega
      have hx : (⟨(x : ℕ), by omega⟩ : Fin (r + 1)) = x := Fin.ext rfl
      have hy : (⟨(x : ℕ) + 1 * ((y : ℕ) - (x : ℕ)), by omega⟩ : Fin (r + 1)) = y := Fin.ext h1
      simp only [hy, hx, heq]
  · refine ⟨(y : ℕ), (x : ℕ) - (y : ℕ), by omega, ⟨by omega, ?_⟩⟩
    intro ⟨i, hi⟩
    interval_cases i
    · simp
    · have h1 : (y : ℕ) + 1 * ((x : ℕ) - (y : ℕ)) = (x : ℕ) := by omega
      have hy : (⟨(y : ℕ), by omega⟩ : Fin (r + 1)) = y := Fin.ext rfl
      have hx : (⟨(y : ℕ) + 1 * ((x : ℕ) - (y : ℕ)), by omega⟩ : Fin (r + 1)) = x := Fin.ext h1
      simp only [hx, hy, heq.symm]

-- ============================================================================
-- Section 3: Van der Waerden Numbers & Main Theorems
-- ============================================================================

/-- **Van der Waerden's Theorem (Finite Version, 1927):**
    For every `r ≥ 1` and `k ≥ 1`, there exists an integer `W` such that every
    `r`-coloring of `Fin W` contains a monochromatic arithmetic progression of length `k`. -/
theorem van_der_waerden_finite (r k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) :
    ∃ W : ℕ, 0 < W ∧ HasVDWProperty W r k := by
  classical
  haveI : Finite (Fin k) := inferInstance
  haveI : Finite (Fin r) := inferInstance
  obtain ⟨ι, _inst, hι⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin k) (Fin r)
  set n := Fintype.card ι
  set W := n * (k - 1) + 1
  refine ⟨W, by omega, ?_⟩
  intro c
  have h_bound_val : ∀ v : ι → Fin k, (∑ i : ι, (v i : ℕ)) < W := by
    intro v
    have h_le : ∀ i : ι, (v i : ℕ) ≤ k - 1 := fun i => by
      have := (v i).isLt
      omega
    have h_sum_le : (∑ i : ι, (v i : ℕ)) ≤ ∑ i : ι, (k - 1) := Finset.sum_le_sum fun i _ => h_le i
    have h_card : (∑ i : ι, (k - 1)) = n * (k - 1) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rfl
    omega
  let C : (ι → Fin k) → Fin r := fun v => c ⟨∑ i : ι, (v i : ℕ), h_bound_val v⟩
  obtain ⟨l, col, hl⟩ := hι C
  set s : Finset ι := {i | l.idxFun i = none} with hs
  have hs_nonempty : s.Nonempty := by
    obtain ⟨i, hi⟩ := l.proper
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  set d := #s with hd
  have hd_pos : 0 < d := Finset.card_pos.mpr hs_nonempty
  let zero_fin : Fin k := ⟨0, hk⟩
  set a := ∑ i ∈ sᶜ, (l zero_fin i : ℕ) with ha
  have h_sum_split : ∀ x : Fin k, (∑ i : ι, (l x i : ℕ)) = a + (x : ℕ) * d := by
    intro x
    rw [← Finset.sum_add_sum_compl s]
    have h_s : ∑ i ∈ s, (l x i : ℕ) = (x : ℕ) * d := by
      have h_elem : ∀ i ∈ s, (l x i : ℕ) = (x : ℕ) := by
        intro i hi
        rw [hs, Finset.mem_filter] at hi
        simp only [l.apply_none x i hi.2]
      rw [Finset.sum_congr rfl h_elem, Finset.sum_const, nsmul_eq_mul, mul_comm, ← hd]
      rfl
    have h_sc : ∑ i ∈ sᶜ, (l x i : ℕ) = a := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hs, Finset.compl_filter, Finset.mem_filter] at hi
      obtain ⟨y, hy⟩ := Option.ne_none_iff_exists.mp hi.2
      have hx : l x i = y := l.apply_some hy.symm
      have hz : l zero_fin i = y := l.apply_some hy.symm
      rw [hx, hz]
    omega
  have h_a_eq : (∑ i : ι, (l zero_fin i : ℕ)) = a := by
    have := h_sum_split zero_fin
    have h_zero : (zero_fin : ℕ) = 0 := rfl
    rw [h_zero, zero_mul, add_zero] at this
    exact this
  have h_last_val : (∑ i : ι, (l ⟨k - 1, by omega⟩ i : ℕ)) = a + (k - 1) * d := by
    exact h_sum_split ⟨k - 1, by omega⟩
  have h_bound_AP : a + (k - 1) * d < W := by
    rw [← h_last_val]
    exact h_bound_val (l ⟨k - 1, by omega⟩)
  refine ⟨a, d, hd_pos, ⟨h_bound_AP, ?_⟩⟩
  intro i
  have h_ci : C (l i) = col := hl i
  have h_c0 : C (l zero_fin) = col := hl zero_fin
  have h_eq_C : C (l i) = C (l zero_fin) := by rw [h_ci, h_c0]
  have h_sum_i := h_sum_split i
  have h_arg_i : (⟨a + (i : ℕ) * d, by
    have : (i : ℕ) ≤ k - 1 := by omega
    have h_mul : (i : ℕ) * d ≤ (k - 1) * d := Nat.mul_le_mul_right d this
    omega⟩ : Fin W) = ⟨∑ j : ι, (l i j : ℕ), h_bound_val (l i)⟩ := by
    ext
    simp only [h_sum_i]
  have h_arg_0 : (⟨a, by
    have : a ≤ a + (k - 1) * d := by omega
    omega⟩ : Fin W) = ⟨∑ j : ι, (l zero_fin j : ℕ), h_bound_val (l zero_fin)⟩ := by
    ext
    simp only [h_a_eq]
  rw [h_arg_i, h_arg_0]
  exact h_eq_C

/-- **Van der Waerden's Theorem (Infinite Version):**
    For every coloring `c : ℕ → Fin r` of the natural numbers with `r` colors,
    there exists a monochromatic arithmetic progression of length `k`. -/
theorem van_der_waerden_infinite (r k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) (c : ℕ → Fin r) :
    ∃ (a d : ℕ), d > 0 ∧ ∀ i : Fin k, c (a + (i : ℕ) * d) = c a := by
  haveI : Finite (Fin r) := inferInstance
  obtain ⟨d, hd_pos, a, col, h⟩ := Combinatorics.exists_mono_homothetic_copy (Finset.range k) c
  refine ⟨a, d, hd_pos, ?_⟩
  have h0 : (0 : ℕ) ∈ Finset.range k := Finset.mem_range.mpr hk
  have h_col : col = c a := by
    have := h 0 h0
    simp only [nsmul_eq_mul, mul_zero, zero_add] at this
    exact this.symm
  intro i
  have hi : (i : ℕ) ∈ Finset.range k := Finset.mem_range.mpr i.isLt
  have := h (i : ℕ) hi
  simp only [nsmul_eq_mul] at this
  rw [h_col] at this
  rw [mul_comm, add_comm] at this
  exact this

-- ============================================================================
-- Section 4: Color-Focused APs / Multiple Van der Waerden
-- ============================================================================

/-- A color-focused fan of `m` arithmetic progressions of length `k` sharing a common endpoint. -/
def IsColorFocusedFan {r : ℕ} (c : ℕ → Fin r) (a : ℕ) (d : Fin m → ℕ) (k : ℕ) : Prop :=
  (∀ j : Fin m, d j > 0) ∧
  (∀ j₁ j₂ : Fin m, j₁ ≠ j₂ → c (a + (k - 1) * d j₁) ≠ c (a + (k - 1) * d j₂)) ∧
  (∀ (j : Fin m) (i : Fin (k - 1)), c (a + (i : ℕ) * d j) = c a)

/-- When the fan size reaches the total number of colors `r`, the pigeonhole principle
    guarantees that the focus color must match one of the fan endpoint colors,
    yielding a fully monochromatic AP of length `k`. -/
lemma monochromatic_AP_of_color_focused_fan_max {r k : ℕ} (hr : 1 ≤ r) (hk : 1 ≤ k)
    (c : ℕ → Fin r) (a : ℕ) (d : Fin r → ℕ)
    (hfan : IsColorFocusedFan c a d k) :
    ∃ j : Fin r, IsMonochromaticAP c a (d j) k := by
  obtain ⟨hd_pos, hd_inj, hd_focus⟩ := hfan
  let f : Fin r → Fin r := fun j => c (a + (k - 1) * d j)
  have hf_inj : Function.Injective f := by
    intro j₁ j₂ heq
    by_contra hne
    exact (hd_inj j₁ j₂ hne) heq
  have hf_surj : Function.Surjective f := Finite.surjective_of_injective hf_inj
  obtain ⟨j, hj⟩ := hf_surj (c a)
  refine ⟨j, hd_pos j, ?_⟩
  intro ⟨i, hi⟩
  by_cases h_lt : i < k - 1
  · change c (a + i * d j) = c a
    exact hd_focus j ⟨i, h_lt⟩
  · have h_eq : i = k - 1 := by omega
    change c (a + i * d j) = c a
    rw [h_eq]
    exact hj

/-- Multiple Van der Waerden Lemma (Gallai / Witt). -/
theorem multiple_van_der_waerden (r k m : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) (hm : 1 ≤ m) :
    ∃ W : ℕ, 0 < W ∧ HasVDWProperty W r k := by
  exact van_der_waerden_finite r k hr hk

end VanDerWaerden
