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
open scoped FinsetFamily

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

lemma sum_eq_of_forall_le_and_sum_eq {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ) (c : ℕ)
    (hle : ∀ i ∈ s, f i ≤ c) (hsum : ∑ i ∈ s, f i = s.card * c) (i : ι) (hi : i ∈ s) :
    f i = c := by
  by_contra hne
  have hlt : f i < c := lt_of_le_of_ne (hle i hi) hne
  have h_sum_lt : ∑ j ∈ s, f j < s.card * c := by
    rw [← Finset.add_sum_erase s f hi]
    have h_rest_le : ∑ j ∈ s.erase i, f j ≤ (s.card - 1) * c := by
      have : ∑ j ∈ s.erase i, f j ≤ ∑ j ∈ s.erase i, c :=
        sum_le_sum (fun j hj => hle j (mem_of_mem_erase hj))
      rw [sum_const, card_erase_of_mem hi, nsmul_eq_mul] at this
      exact this
    have h_pos : 0 < s.card := card_pos.mpr ⟨i, hi⟩
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h_pos.ne'
    have h_split : s.card * c = (s.card - 1) * c + c := by
      rw [hk, Nat.succ_sub_one, Nat.succ_mul, add_comm]
    rw [h_split]
    omega
  omega

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
          let B : Finset (Finset α) := A.filter (fun s => s.card = m + 1)
          let Am : Finset (Finset α) := A.filter (fun s => s.card = m)
          have ht0_B : t0 ∈ B := mem_filter.mpr ⟨ht0_in, ht0_card⟩
          have hB_nonempty : B.Nonempty := ⟨t0, ht0_B⟩
          have ht_Am : t ∈ Am := mem_filter.mpr ⟨ht, by omega⟩
          have hAm_nonempty : Am.Nonempty := ⟨t, ht_Am⟩
          have hB_sized : (B : Set (Finset α)).Sized (m + 1) := fun s hs => (mem_filter.mp hs).2
          have hAm_sized : (Am : Set (Finset α)).Sized m := fun s hs => (mem_filter.mp hs).2
          have h_mem_or : ∀ s ∈ A, s ∈ Am ∨ s ∈ B := by
            intro s hs
            have h_or := card_eq_or_eq_of_card_eq_middleChoose hn A h_anti h_eq s hs
            rcases h_or with h1 | h2
            · left; exact mem_filter.mpr ⟨hs, by omega⟩
            · right; exact mem_filter.mpr ⟨hs, by omega⟩
          have h_disj_Am_B : Disjoint Am B := by
            rw [disjoint_filter]
            intro s _ h1 h2
            omega
          have h_card_A : A.card = Am.card + B.card := by
            have h_eq_union : A = Am ∪ B := by
              ext s
              simp only [mem_union]
              constructor
              · intro hs
                exact h_mem_or s hs
              · rintro (hs | hs)
                · exact (mem_filter.mp hs).1
                · exact (mem_filter.mp hs).1
            rw [h_eq_union, card_union_of_disjoint h_disj_Am_B]
          have h_sum_cards : Am.card + B.card = middleChoose (2 * m + 1) := by
            rw [← h_card_A, h_eq]
          have h_shB_sized : (∂ B : Set (Finset α)).Sized m := by
            have := Set.Sized.shadow hB_sized
            rwa [add_tsub_cancel_right] at this
          have h_disj_Am_shB : Disjoint Am (∂ B) := by
            rw [disjoint_iff_ne]
            intro u hu v hv heq
            subst heq
            rw [mem_filter] at hu
            rw [mem_shadow_iff] at hv
            obtain ⟨s, hs_B, a, ha_s, rfl⟩ := hv
            have hs_A : s ∈ A := (mem_filter.mp hs_B).1
            have hu_sub_s : erase s a ⊆ s := erase_subset a s
            have hu_eq_s : erase s a = s := h_anti (erase s a) hu.1 s hs_A hu_sub_s
            have h_card_eq : (erase s a).card = s.card := by rw [hu_eq_s]
            rw [hu.2, (mem_filter.mp hs_B).2] at h_card_eq
            omega
          have h_sub_pow : Am ∪ (∂ B) ⊆ (Finset.univ : Finset α).powersetCard m := by
            intro u hu
            rw [mem_union] at hu
            simp only [mem_powersetCard, subset_univ, true_and]
            rcases hu with hu | hu
            · exact hAm_sized hu
            · exact h_shB_sized hu
          have h_card_union_le : (Am ∪ (∂ B)).card ≤ middleChoose (2 * m + 1) := by
            have h1 := card_le_card h_sub_pow
            rw [card_powersetCard, card_univ, hn] at h1
            unfold middleChoose
            have : (2 * m + 1) / 2 = m := by omega
            rwa [this]
          have h_card_union_eq : (Am ∪ (∂ B)).card = Am.card + (∂ B).card :=
            card_union_of_disjoint h_disj_Am_shB
          have h_Am_shB_le : Am.card + (∂ B).card ≤ middleChoose (2 * m + 1) := by
            linarith
          have h_lym_B := local_lubell_yamamoto_meshalkin_inequality_mul hB_sized
          have h_B_le_shB : B.card ≤ (∂ B).card := by
            rw [hn] at h_lym_B
            have : 2 * m + 1 - (m + 1) + 1 = m + 1 := by omega
            rw [this] at h_lym_B
            exact Nat.le_of_mul_le_mul_right h_lym_B (by omega)
          have h_B_eq_shB : B.card = (∂ B).card := by omega
          have hb_below : ∀ b ∈ B, m + 1 ≤ #((∂ B).bipartiteBelow (· ⊆ ·) b) := by
            intro b hb
            have hb_card : b.card = m + 1 := (mem_filter.mp hb).2
            have h_sub : b.image (fun a => b.erase a) ⊆ (∂ B).bipartiteBelow (· ⊆ ·) b := by
              intro u hu
              simp only [mem_image] at hu
              obtain ⟨a, ha_b, rfl⟩ := hu
              simp only [mem_bipartiteBelow]
              refine ⟨?_, erase_subset a b⟩
              rw [mem_shadow_iff]
              exact ⟨b, hb, a, ha_b, rfl⟩
            have h_inj : (b : Set α).InjOn (fun a => b.erase a) := by
              intro a1 ha1 a2 ha2 heq
              dsimp at heq
              by_contra hne
              have : a2 ∈ b.erase a1 := mem_erase.mpr ⟨Ne.symm hne, ha2⟩
              rw [heq, mem_erase] at this
              exact this.1 rfl
            have h_card_im : (b.image (fun a => b.erase a)).card = m + 1 := by
              rw [card_image_of_injOn h_inj, hb_card]
            rw [← h_card_im]
            exact card_le_card h_sub
          have hu_above : ∀ u ∈ ∂ B, #(B.bipartiteAbove (· ⊆ ·) u) ≤ m + 1 := by
            intro u hu
            have hu_card : u.card = m := h_shB_sized hu
            have h_sub : B.bipartiteAbove (· ⊆ ·) u ⊆ (Finset.univ \ u).image (fun a => insert a u) := by
              intro s hs
              simp only [mem_bipartiteAbove] at hs
              obtain ⟨hs_B, hu_sub_s⟩ := hs
              have hs_card : s.card = m + 1 := (mem_filter.mp hs_B).2
              have h_ins : ∃ a ∉ u, insert a u = s := by
                apply exists_eq_insert_iff.mpr
                exact ⟨hu_sub_s, by omega⟩
              obtain ⟨a, ha_not, rfl⟩ := h_ins
              simp only [mem_image, mem_sdiff, mem_univ, true_and]
              exact ⟨a, ha_not, rfl⟩
            have h_card_im : ((Finset.univ \ u).image (fun a => insert a u)).card ≤ m + 1 := by
              refine le_trans card_image_le ?_
              rw [card_sdiff_of_subset (subset_univ u), card_univ, hn, hu_card]
              omega
            exact le_trans (card_le_card h_sub) h_card_im
          have h_sum_eq : (∑ u ∈ ∂ B, #(B.bipartiteAbove (· ⊆ ·) u)) = ∑ b ∈ B, #((∂ B).bipartiteBelow (· ⊆ ·) b) :=
            sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (r := ((· ⊆ ·) : Finset α → Finset α → Prop))
          have h_sum_below : B.card * (m + 1) ≤ ∑ b ∈ B, #((∂ B).bipartiteBelow (· ⊆ ·) b) := by
            have := sum_le_sum (fun b (hb : b ∈ B) => hb_below b hb)
            rw [sum_const, nsmul_eq_mul] at this
            exact this
          have h_sum_above : ∑ u ∈ ∂ B, #(B.bipartiteAbove (· ⊆ ·) u) ≤ (∂ B).card * (m + 1) := by
            have := sum_le_sum (fun u (hu : u ∈ ∂ B) => hu_above u hu)
            rw [sum_const, nsmul_eq_mul] at this
            exact this
          have h_all_sum_eq : ∑ u ∈ ∂ B, #(B.bipartiteAbove (· ⊆ ·) u) = (∂ B).card * (m + 1) := by
            have h1 : ∑ u ∈ ∂ B, #(B.bipartiteAbove (· ⊆ ·) u) = ∑ b ∈ B, #((∂ B).bipartiteBelow (· ⊆ ·) b) := h_sum_eq
            have h2 : (∂ B).card * (m + 1) ≤ ∑ b ∈ B, #((∂ B).bipartiteBelow (· ⊆ ·) b) := by
              rwa [← h_B_eq_shB]
            omega
          have hu_above_eq : ∀ u ∈ ∂ B, #(B.bipartiteAbove (· ⊆ ·) u) = m + 1 :=
            fun u hu => sum_eq_of_forall_le_and_sum_eq (∂ B) (fun v => #(B.bipartiteAbove (· ⊆ ·) v)) (m + 1)
              hu_above h_all_sum_eq u hu
          have h_ins_in_B : ∀ u ∈ ∂ B, ∀ x ∉ u, insert x u ∈ B := by
            intro u hu x hx
            have hu_card : u.card = m := h_shB_sized hu
            have h_sub : B.bipartiteAbove (· ⊆ ·) u ⊆ (Finset.univ \ u).image (fun a => insert a u) := by
              intro s hs
              simp only [mem_bipartiteAbove] at hs
              obtain ⟨hs_B, hu_sub_s⟩ := hs
              have hs_card : s.card = m + 1 := (mem_filter.mp hs_B).2
              have h_ins : ∃ a ∉ u, insert a u = s := by
                apply exists_eq_insert_iff.mpr
                exact ⟨hu_sub_s, by omega⟩
              obtain ⟨a, ha_not, rfl⟩ := h_ins
              simp only [mem_image, mem_sdiff, mem_univ, true_and]
              exact ⟨a, ha_not, rfl⟩
            have h_inj : ((Finset.univ \ u : Finset α) : Set α).InjOn (fun a => insert a u) := by
              intro a1 ha1 a2 ha2 heq
              dsimp at heq
              rw [coe_sdiff, coe_univ, Set.mem_sdiff] at ha1 ha2
              have ha1_not : a1 ∉ u := ha1.2
              have : a1 ∈ insert a2 u := by rw [← heq]; exact mem_insert_self a1 u
              simp only [mem_insert] at this
              cases this with
              | inl h => exact h
              | inr h => exact (ha1_not h).elim
            have h_card_im : ((Finset.univ \ u).image (fun a => insert a u)).card = m + 1 := by
              rw [card_image_of_injOn h_inj]
              rw [card_sdiff_of_subset (subset_univ u), card_univ, hn, hu_card]
              omega
            have h_above_eq_im : B.bipartiteAbove (· ⊆ ·) u = (Finset.univ \ u).image (fun a => insert a u) :=
              eq_of_subset_of_card_le h_sub (by rw [hu_above_eq u hu, h_card_im])
            have hx_im : insert x u ∈ (Finset.univ \ u).image (fun a => insert a u) := by
              simp only [mem_image, mem_sdiff, mem_univ, true_and]
              exact ⟨x, hx, rfl⟩
            rw [← h_above_eq_im] at hx_im
            simp only [mem_bipartiteAbove] at hx_im
            exact hx_im.1
          have h_swap : ∀ s ∈ B, ∀ y ∈ s, ∀ x ∉ s, insert x (s.erase y) ∈ B := by
            intro s hs y hy x hx
            have hu : s.erase y ∈ ∂ B := erase_mem_shadow hs hy
            have hx_not : x ∉ s.erase y := fun h => hx (mem_of_mem_erase h)
            exact h_ins_in_B (s.erase y) hu x hx_not
          have h_B_all := all_powersetCard_of_swap_closed (m + 1) B hB_nonempty hB_sized h_swap
          have h_B_card_all : B.card = middleChoose (2 * m + 1) := by
            rw [h_B_all, card_powersetCard, card_univ, hn]
            unfold middleChoose
            have : (2 * m + 1) / 2 = m := by omega
            rw [this]
            have h_symm : (2 * m + 1).choose (m + 1) = (2 * m + 1).choose (2 * m + 1 - (m + 1)) :=
              (Nat.choose_symm (show m + 1 ≤ 2 * m + 1 by omega)).symm
            have h_sub_eq : 2 * m + 1 - (m + 1) = m := by omega
            rwa [h_sub_eq] at h_symm
          have h_Am_zero : Am.card = 0 := by omega
          have h_Am_pos : 0 < Am.card := card_pos.mpr hAm_nonempty
          omega
      · omega

end SpernerAntichain
