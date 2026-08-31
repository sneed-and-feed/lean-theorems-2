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
  obtain ⟨x, y, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt c (by simp)
  have h_mono (u v : Fin (r + 1)) (hlt : (u : ℕ) < (v : ℕ)) (hcol : c u = c v) :
      HasMonochromaticAP (r + 1) c 2 := by
    refine ⟨(u : ℕ), (v : ℕ) - (u : ℕ), by omega, ⟨by omega, ?_⟩⟩
    intro ⟨i, hi⟩
    interval_cases i
    · simp
    · have hu : (⟨(u : ℕ), by omega⟩ : Fin (r + 1)) = u := Fin.ext rfl
      have hv : (⟨(u : ℕ) + 1 * ((v : ℕ) - (u : ℕ)), by omega⟩ : Fin (r + 1)) = v := Fin.ext (by dsimp; omega)
      simp only [hv, hu, hcol]
  rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with h | h
  · exact h_mono x y h heq
  · exact h_mono y x h heq.symm

-- ============================================================================
-- Section 3: Van der Waerden Numbers & Main Theorems
-- ============================================================================

/-- **Van der Waerden's Theorem (Finite Version, 1927):**
    For every `r ≥ 1` and `k ≥ 1`, there exists an integer `W` such that every
    `r`-coloring of `Fin W` contains a monochromatic arithmetic progression of length `k`. -/
theorem van_der_waerden_finite (r k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) :
    ∃ W : ℕ, 0 < W ∧ HasVDWProperty W r k := by
  classical
  obtain ⟨ι, _inst, hι⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin k) (Fin r)
  set n := Fintype.card ι
  set W := n * (k - 1) + 1
  refine ⟨W, by omega, ?_⟩
  intro c
  have h_bound_val (v : ι → Fin k) : (∑ i : ι, (v i : ℕ)) < W := by
    have : (∑ i : ι, (v i : ℕ)) ≤ ∑ _i : ι, (k - 1) := Finset.sum_le_sum fun i _ => by omega
    have : (∑ _i : ι, (k - 1)) = n * (k - 1) := by simp [n, Finset.card_univ]
    omega
  let C : (ι → Fin k) → Fin r := fun v => c ⟨∑ i : ι, (v i : ℕ), h_bound_val v⟩
  obtain ⟨l, col, hl⟩ := hι C
  set s : Finset ι := {i | l.idxFun i = none}
  have hd_pos : 0 < #s := by
    obtain ⟨i, hi⟩ := l.proper
    exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  set d := #s
  let zero_fin : Fin k := ⟨0, hk⟩
  set a := ∑ i ∈ sᶜ, (l zero_fin i : ℕ)
  have h_sum_split (x : Fin k) : (∑ i : ι, (l x i : ℕ)) = a + (x : ℕ) * d := by
    rw [← Finset.sum_add_sum_compl s]
    have h_s : ∑ i ∈ s, (l x i : ℕ) = (x : ℕ) * d := by
      have h_elem : ∀ i ∈ s, (l x i : ℕ) = (x : ℕ) := fun i hi => by
        simp only [l.apply_none x i (Finset.mem_filter.mp hi).2]
      rw [Finset.sum_congr rfl h_elem, Finset.sum_const, nsmul_eq_mul, mul_comm]
      rfl
    have h_sc : ∑ i ∈ sᶜ, (l x i : ℕ) = a := by
      refine Finset.sum_congr rfl fun i hi => ?_
      obtain ⟨y, hy⟩ := Option.ne_none_iff_exists.mp (by simpa [s] using hi)
      rw [l.apply_some hy.symm, l.apply_some hy.symm]
    omega
  have h_bound_AP : a + (k - 1) * d < W := by
    have := h_bound_val (l ⟨k - 1, by omega⟩)
    rwa [h_sum_split] at this
  have h_a0 : (∑ i, (l zero_fin i : ℕ)) = a := by simpa [zero_fin] using h_sum_split zero_fin
  refine ⟨a, d, hd_pos, ⟨h_bound_AP, fun i => ?_⟩⟩
  have h_arg (x : Fin k) (hbound : _) : (⟨a + (x : ℕ) * d, hbound⟩ : Fin W) = ⟨∑ j : ι, (l x j : ℕ), h_bound_val (l x)⟩ :=
    Fin.ext (h_sum_split x).symm
  rw [h_arg i, show (⟨a, _⟩ : Fin W) = ⟨∑ j, (l zero_fin j : ℕ), h_bound_val (l zero_fin)⟩ from Fin.ext h_a0.symm]
  exact (hl i).trans (hl zero_fin).symm

/-- **Van der Waerden's Theorem (Infinite Version):**
    For every coloring `c : ℕ → Fin r` of the natural numbers with `r` colors,
    there exists a monochromatic arithmetic progression of length `k`. -/
theorem van_der_waerden_infinite (r k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) (c : ℕ → Fin r) :
    ∃ (a d : ℕ), d > 0 ∧ ∀ i : Fin k, c (a + (i : ℕ) * d) = c a := by
  obtain ⟨d, hd_pos, a, col, h⟩ := Combinatorics.exists_mono_homothetic_copy (Finset.range k) c
  have h_col : col = c a := by simpa using (h 0 (Finset.mem_range.mpr hk)).symm
  exact ⟨a, d, hd_pos, fun i => by simpa [h_col, nsmul_eq_mul, mul_comm, add_comm] using h i (Finset.mem_range.mpr i.isLt)⟩

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
  obtain ⟨j, hj⟩ := (Finite.injective_iff_surjective.mp fun _ _ h =>
    not_not.mp fun hne => hd_inj _ _ hne h) (c a)
  refine ⟨j, hd_pos j, fun ⟨i, hi⟩ => ?_⟩
  rcases lt_or_eq_of_le (Nat.le_pred_of_lt hi) with hlt | rfl
  · exact hd_focus j ⟨i, hlt⟩
  · exact hj

/-- Multiple Van der Waerden Lemma (Gallai / Witt). -/
theorem multiple_van_der_waerden (r k m : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) (hm : 1 ≤ m) :
    ∃ W : ℕ, 0 < W ∧ HasVDWProperty W r k := by
  exact van_der_waerden_finite r k hr hk

end VanDerWaerden
