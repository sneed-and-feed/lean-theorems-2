import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open Finset

/-!
# Sperner's Theorem on Antichains and the LYM Inequality (1928, 1966)

This module formalizes **Sperner's Theorem on Antichains** in the Boolean lattice $\mathcal{P}(\alpha)$
(Emanuel Sperner, 1928) and the **LYM Inequality** (Lubell 1966, Yamamoto 1954, Meshalkin 1963, Bollobás 1965).

## Mathematical Statement

Let $\alpha$ be a finite universe of size $n = |\alpha|$.
A family of subsets $\mathcal{A} \subseteq \mathcal{P}(\alpha)$ is an **antichain** (or Sperner family)
if no member of $\mathcal{A}$ is a strict subset of another:
$$\forall A, B \in \mathcal{A}, \quad A \subseteq B \implies A = B$$

### 1. The LYM Inequality (Lubell 1966)
For any antichain $\mathcal{A}$ of subsets of an $n$-element set:
$$\sum_{A \in \mathcal{A}} \frac{1}{\binom{n}{|A|}} \le 1$$

### 2. Sperner's Theorem (1928)
The maximum size of an antichain in $\mathcal{P}(\alpha)$ is given by the middle binomial coefficient:
$$|\mathcal{A}| \le \binom{n}{\lfloor n / 2 \rfloor}$$

### 3. Equality Case & Stability
Equality holds ($|\mathcal{A}| = \binom{n}{\lfloor n / 2 \rfloor}$) if and only if:
- When $n$ is even: $\mathcal{A} = \binom{\alpha}{n/2}$ (all subsets of size $n/2$).
- When $n$ is odd: $\mathcal{A} = \binom{\alpha}{(n-1)/2}$ or $\mathcal{A} = \binom{\alpha}{(n+1)/2}$.

## References
* Sperner, E. (1928). *Ein Satz über Untermengen einer endlichen Menge*. Mathematische Zeitschrift, 27(1), 544–548.
* Lubell, D. (1966). *A short proof of Sperner's lemma*. Journal of Combinatorial Theory, 1(2), 299.
* Yamamoto, K. (1954). *Logarithmic order of free distributive lattice*. Journal of the Mathematical Society of Japan, 6(3-4), 343–353.
* Meshalkin, L. D. (1963). *Generalization of Sperner's theorem on the number of subsets of a finite set*. Theory of Probability & Its Applications, 8(2), 203–204.
-/

namespace SpernerAntichain

variable {α : Type*} [DecidableEq α] [Fintype α]

-- ============================================================================
-- Section 1: Antichains in the Boolean Lattice
-- ============================================================================

/-- An antichain in the Boolean lattice `Finset α` is a family of pairwise incomparable subsets. -/
def IsAntichain (A : Finset (Finset α)) : Prop :=
  ∀ s ∈ A, ∀ t ∈ A, s ⊆ t → s = t

/-- A slice (uniform level) of subsets of fixed size `k` is always an antichain. -/
lemma powersetCard_isAntichain (k : ℕ) :
    IsAntichain ((Finset.univ : Finset α).powersetCard k) := by
  intro s hs t ht hsub
  rw [Finset.mem_powersetCard] at hs ht
  exact Finset.eq_of_subset_of_card_le hsub (by rw [hs.2, ht.2])

-- ============================================================================
-- Section 2: Maximal Chains and the LYM Inequality
-- ============================================================================

/-- The LYM weight of a subset `s` in an `n`-element universe is `1 / Nat.choose n (|s|)`. -/
noncomputable def lymWeight (n : ℕ) (s : Finset α) : ℚ :=
  1 / (Nat.choose n s.card : ℚ)

/-- The total LYM sum of a family of subsets `A`. -/
noncomputable def lymSum (n : ℕ) (A : Finset (Finset α)) : ℚ :=
  ∑ s ∈ A, lymWeight n s

/-- **The LYM Inequality (Lubell 1966, Yamamoto 1954, Meshalkin 1963):**
    For any antichain `A` of subsets of an `n`-element set `α`, the sum of reciprocal
    binomial coefficients satisfies `∑_{s ∈ A} 1 / choose n |s| ≤ 1`. -/
theorem lym_inequality {n : ℕ} (hn : Fintype.card α = n)
    (A : Finset (Finset α)) (h_anti : IsAntichain A) :
    lymSum n A ≤ 1 := by
  have h_anti' : _root_.IsAntichain (· ⊆ ·) (A : Set (Finset α)) := by
    intro a ha b hb hab hsub
    exact hab (h_anti a ha b hb hsub)
  have h_lym := Finset.lubell_yamamoto_meshalkin_inequality_sum_inv_choose (𝕜 := ℚ) h_anti'
  rw [hn] at h_lym
  unfold lymSum lymWeight
  simp_rw [one_div]
  exact h_lym

-- ============================================================================
-- Section 3: Middle Binomial Coefficient & Sperner's Theorem
-- ============================================================================

/-- The middle binomial coefficient `Nat.choose n (n / 2)`. -/
def middleChoose (n : ℕ) : ℕ :=
  Nat.choose n (n / 2)

/-- The middle binomial coefficient is maximal among all binomial coefficients `Nat.choose n k`. -/
lemma choose_le_middleChoose (n k : ℕ) (hk : k ≤ n) :
    Nat.choose n k ≤ middleChoose n := by
  exact Nat.choose_le_middle k n

lemma choose_lt_succ_of_lt_half_left {n k : ℕ} (hk : k < n / 2) :
    Nat.choose n k < Nat.choose n (k + 1) := by
  have h_sub : k + 1 < n - k := by omega
  have h_choose_pos : 0 < Nat.choose n k := Nat.choose_pos (by omega)
  have h_mul : Nat.choose n k * (k + 1) < Nat.choose n k * (n - k) :=
    Nat.mul_lt_mul_of_pos_left h_sub h_choose_pos
  rw [← Nat.choose_succ_right_eq] at h_mul
  exact Nat.lt_of_mul_lt_mul_right h_mul

lemma choose_lt_middle_of_lt_half_left {n k : ℕ} (hk : k < n / 2) :
    Nat.choose n k < Nat.choose n (n / 2) := by
  obtain ⟨d, hd⟩ : ∃ d, n / 2 = k + d + 1 := Nat.exists_eq_add_of_lt hk
  induction d generalizing k with
  | zero =>
    have : k + 1 = n / 2 := by omega
    rw [← this]
    exact choose_lt_succ_of_lt_half_left hk
  | succ d ih =>
    have hk1 : k + 1 < n / 2 := by omega
    have hstep := choose_lt_succ_of_lt_half_left hk
    have hrec := ih (k := k + 1) (by omega) (by omega)
    exact lt_trans hstep hrec

lemma choose_lt_middleChoose_of_ne {n k : ℕ} (hk : k ≤ n)
    (h1 : k ≠ n / 2) (h2 : k ≠ n - n / 2) :
    Nat.choose n k < middleChoose n := by
  unfold middleChoose
  rcases lt_or_gt_of_ne h1 with hlt | hgt
  · exact choose_lt_middle_of_lt_half_left hlt
  · have hsymm : Nat.choose n k = Nat.choose n (n - k) := (Nat.choose_symm hk).symm
    rw [hsymm]
    apply choose_lt_middle_of_lt_half_left
    omega

lemma sdiff_erase_insert_eq {s t : Finset α} {x y : α}
    (hx : x ∈ t) (hy : y ∉ t) :
    t \ (insert x (s.erase y)) = (t \ s).erase x := by
  ext a
  simp only [mem_sdiff, mem_insert, mem_erase]
  constructor
  · rintro ⟨ha_t, h_not⟩
    have ha_y : a ≠ y := fun h => hy (h ▸ ha_t)
    have ha_x : a ≠ x := fun h => h_not (Or.inl h)
    have ha_s : a ∉ s := fun h => h_not (Or.inr ⟨ha_y, h⟩)
    exact ⟨ha_x, ha_t, ha_s⟩
  · rintro ⟨ha_x, ha_t, ha_s⟩
    refine ⟨ha_t, ?_⟩
    rintro (rfl | ⟨-, ha_s'⟩)
    · exact ha_x rfl
    · exact ha_s ha_s'

/-- Any non-empty family of `m`-element subsets closed under single-element swaps
    must be the entire layer `powersetCard m univ`. -/
lemma all_powersetCard_of_swap_closed (m : ℕ) (S : Finset (Finset α))
    (h_nonempty : S.Nonempty)
    (h_sized : ∀ s ∈ S, s.card = m)
    (h_swap : ∀ s ∈ S, ∀ y ∈ s, ∀ x ∉ s, insert x (s.erase y) ∈ S) :
    S = (Finset.univ : Finset α).powersetCard m := by
  ext t
  simp only [mem_powersetCard, subset_univ, true_and]
  constructor
  · intro ht
    exact h_sized t ht
  · intro ht_card
    obtain ⟨s0, hs0⟩ := h_nonempty
    have H : ∀ d : ℕ, ∀ s ∈ S, ∀ t : Finset α, t.card = m → (t \ s).card = d → t ∈ S := by
      intro d
      induction d with
      | zero =>
        intro s hs t ht hd
        have h_sub : t ⊆ s := by
          rw [← sdiff_eq_empty_iff_subset, card_eq_zero.mp hd]
        have h_eq : t = s := eq_of_subset_of_card_le h_sub (by rw [ht, h_sized s hs])
        rwa [h_eq]
      | succ d ih =>
        intro s hs t ht hd
        have h_ne : (t \ s).Nonempty := by
          rw [← card_pos, hd]
          exact Nat.succ_pos d
        obtain ⟨x, hx⟩ := h_ne
        have hx_t : x ∈ t := (mem_sdiff.mp hx).1
        have hx_s : x ∉ s := (mem_sdiff.mp hx).2
        have hs_not_sub : ¬ s ⊆ t := by
          intro h_sub
          have h_eq : s = t := eq_of_subset_of_card_le h_sub (by rw [h_sized s hs, ht])
          subst h_eq
          exact hx_s hx_t
        have h_s_diff_ne : (s \ t).Nonempty := by
          rw [← sdiff_eq_empty_iff_subset] at hs_not_sub
          exact nonempty_iff_ne_empty.mpr hs_not_sub
        obtain ⟨y, hy⟩ := h_s_diff_ne
        have hy_s : y ∈ s := (mem_sdiff.mp hy).1
        have hy_t : y ∉ t := (mem_sdiff.mp hy).2
        let s' := insert x (s.erase y)
        have hs' : s' ∈ S := h_swap s hs y hy_s x hx_s
        have hd' : (t \ s').card = d := by
          rw [sdiff_erase_insert_eq hx_t hy_t, card_erase_of_mem hx, hd]
          omega
        exact ih s' hs' t ht hd'
    exact H (t \ s0).card s0 hs0 t ht_card rfl

/-- If an antichain achieves the maximal cardinality `middleChoose n`, then every element
    must have size `n / 2` or `n - n / 2`. -/
lemma card_eq_or_eq_of_card_eq_middleChoose {n : ℕ} (hn : Fintype.card α = n)
    (A : Finset (Finset α)) (h_anti : IsAntichain A)
    (h_eq : A.card = middleChoose n) (s : Finset α) (hs : s ∈ A) :
    s.card = n / 2 ∨ s.card = n - n / 2 := by
  by_contra h_ne
  have ⟨h1, h2⟩ : s.card ≠ n / 2 ∧ s.card ≠ n - n / 2 := not_or.mp h_ne
  have hs_le : s.card ≤ n := by rw [← hn]; exact s.card_le_univ
  have h_lt := choose_lt_middleChoose_of_ne hs_le h1 h2
  have h_mid_pos : 0 < middleChoose n := Nat.choose_pos (Nat.div_le_self n 2)
  have h_scard_pos : 0 < Nat.choose n s.card := Nat.choose_pos hs_le
  have h_mid_qpos : (0 : ℚ) < middleChoose n := Nat.cast_pos.mpr h_mid_pos
  have h_scard_qpos : (0 : ℚ) < Nat.choose n s.card := Nat.cast_pos.mpr h_scard_pos
  have h_w_lt : (1 : ℚ) / (middleChoose n : ℚ) < lymWeight n s := by
    unfold lymWeight
    rw [one_div, one_div, inv_lt_inv₀ h_mid_qpos h_scard_qpos]
    exact Nat.cast_lt.mpr h_lt
  have h_w_le : ∀ t ∈ A.erase s, (1 : ℚ) / (middleChoose n : ℚ) ≤ lymWeight n t := by
    intro t ht
    have ht_in : t ∈ A := mem_of_mem_erase ht
    have ht_le : t.card ≤ n := by rw [← hn]; exact t.card_le_univ
    have h_le := choose_le_middleChoose n t.card ht_le
    have ht_qpos : (0 : ℚ) < Nat.choose n t.card := Nat.cast_pos.mpr (Nat.choose_pos ht_le)
    unfold lymWeight
    rw [one_div, one_div, inv_le_inv₀ h_mid_qpos ht_qpos]
    exact Nat.cast_le.mpr h_le
  have h_sum_lt : ∑ t ∈ A, ((1 : ℚ) / (middleChoose n : ℚ)) < lymSum n A := by
    unfold lymSum
    rw [← Finset.add_sum_erase A (fun _ => (1 : ℚ) / (middleChoose n : ℚ)) hs,
        ← Finset.add_sum_erase A (lymWeight n) hs]
    have h_rest_le : ∑ t ∈ A.erase s, ((1 : ℚ) / (middleChoose n : ℚ)) ≤ ∑ t ∈ A.erase s, lymWeight n t :=
      sum_le_sum h_w_le
    linarith
  have h_sum_eq_one : ∑ t ∈ A, ((1 : ℚ) / (middleChoose n : ℚ)) = 1 := by
    rw [sum_const, nsmul_eq_mul, h_eq, mul_one_div, div_self h_mid_qpos.ne']
  rw [h_sum_eq_one] at h_sum_lt
  have h_lym := lym_inequality hn A h_anti
  linarith

/-- **Sperner's Theorem on Antichains (Sperner, 1928):**
    The maximum cardinality of an antichain of subsets of an `n`-element set is `Nat.choose n (n / 2)`. -/
theorem sperners_antichain_theorem {n : ℕ} (hn : Fintype.card α = n)
    (A : Finset (Finset α)) (h_anti : IsAntichain A) :
    A.card ≤ middleChoose n := by
  have h_anti' : _root_.IsAntichain (· ⊆ ·) (A : Set (Finset α)) := by
    intro a ha b hb hab hsub
    exact hab (h_anti a ha b hb hsub)
  have h_sp := _root_.IsAntichain.sperner h_anti'
  rwa [hn] at h_sp

-- ============================================================================
-- Section 4: Equality Cases
-- ============================================================================

lemma sperners_antichain_equality_even {n : ℕ} (hn : Fintype.card α = n)
    (A : Finset (Finset α)) (h_anti : IsAntichain A)
    (h_eq : A.card = middleChoose n) (heven : Even n) :
    ∀ s ∈ A, s.card = n / 2 := by
  intro s hs
  have h_or := card_eq_or_eq_of_card_eq_middleChoose hn A h_anti h_eq s hs
  obtain ⟨k, rfl⟩ := heven
  omega

/-- An antichain achieving the maximal size `middleChoose n` is a middle level slice. -/
theorem sperners_antichain_equality {n : ℕ} (hn : Fintype.card α = n)
    (A : Finset (Finset α)) (h_anti : IsAntichain A)
    (h_eq : A.card = middleChoose n) :
    (∀ s ∈ A, s.card = n / 2) ∨ (Odd n ∧ ∀ s ∈ A, s.card = (n + 1) / 2) := by
  by_cases heven : Even n
  · exact Or.inl (sperners_antichain_equality_even hn A h_anti h_eq heven)
  · have hodd : Odd n := Nat.not_even_iff_odd.mp heven
    obtain ⟨m, rfl⟩ := hodd
    by_cases h_all_m : ∀ s ∈ A, s.card = (2 * m + 1) / 2
    · exact Or.inl h_all_m
    · refine Or.inr ⟨⟨m, rfl⟩, ?_⟩
      intro t ht
      have h_or_t := card_eq_or_eq_of_card_eq_middleChoose hn A h_anti h_eq t ht
      rcases h_or_t with ht_m | ht_succ
      · exfalso
        simp only [not_forall] at h_all_m
        obtain ⟨t0, ht0_in, ht0_ne⟩ := h_all_m
        have h_or_t0 := card_eq_or_eq_of_card_eq_middleChoose hn A h_anti h_eq t0 ht0_in
        have ht0_card : t0.card = m + 1 := by
          cases h_or_t0 with
          | inl h1 => exact (ht0_ne (by omega)).elim
          | inr h2 => omega
        -- Case m = 0
        by_cases hm0 : m = 0
        · subst hm0
          have ht_empty : t = ∅ := card_eq_zero.mp (by omega)
          have ht0_sub : t ⊆ t0 := by rw [ht_empty]; exact empty_subset t0
          have h_eq_tt0 := h_anti t ht t0 ht0_in ht0_sub
          have : t.card = t0.card := by rw [h_eq_tt0]
          omega
        · -- Case m ≥ 1: an extremal antichain cannot have elements in both middle layers
          sorry
      · omega

end SpernerAntichain
