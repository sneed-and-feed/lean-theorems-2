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

/-- An antichain achieving the maximal size `middleChoose n` is a middle level slice. -/
theorem sperners_antichain_equality {n : ℕ} (hn : Fintype.card α = n)
    (A : Finset (Finset α)) (h_anti : IsAntichain A)
    (h_eq : A.card = middleChoose n) :
    (∀ s ∈ A, s.card = n / 2) ∨ (Odd n ∧ ∀ s ∈ A, s.card = (n + 1) / 2) := by
  sorry

end SpernerAntichain
