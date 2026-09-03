import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring


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

omit [DecidableEq α] in
/-- A slice (uniform level) of subsets of fixed size `k` is always an antichain. -/
lemma powersetCard_isAntichain (k : ℕ) :
    IsAntichain ((Finset.univ : Finset α).powersetCard k) :=
  fun s hs t ht hsub => eq_of_subset_of_card_le hsub
    (by rw [(mem_powersetCard.mp hs).2, (mem_powersetCard.mp ht).2])

-- ============================================================================
-- Section 2: Maximal Chains and the LYM Inequality
-- ============================================================================

/-- The LYM weight of a subset `s` in an `n`-element universe is `1 / Nat.choose n (|s|)`. -/
noncomputable def lymWeight (n : ℕ) (s : Finset α) : ℚ :=
  1 / (Nat.choose n s.card : ℚ)

/-- The total LYM sum of a family of subsets `A`. -/
noncomputable def lymSum (n : ℕ) (A : Finset (Finset α)) : ℚ :=
  ∑ s ∈ A, lymWeight n s

omit [DecidableEq α] in
/-- **The LYM Inequality (Lubell 1966, Yamamoto 1954, Meshalkin 1963):**
    For any antichain `A` of subsets of an `n`-element set `α`, the sum of reciprocal
    binomial coefficients satisfies `∑_{s ∈ A} 1 / choose n |s| ≤ 1`. -/
theorem lym_inequality {n : ℕ} (hn : Fintype.card α = n)
    (A : Finset (Finset α)) (h_anti : IsAntichain A) :
    lymSum n A ≤ 1 := by
  have h_anti' : _root_.IsAntichain (· ⊆ ·) (A : Set (Finset α)) :=
    fun a ha b hb hab => hab ∘ h_anti a ha b hb
  simpa [lymSum, lymWeight, hn] using
    lubell_yamamoto_meshalkin_inequality_sum_inv_choose (𝕜 := ℚ) h_anti'

-- ============================================================================
-- Section 3: Middle Binomial Coefficient & Sperner's Theorem
-- ============================================================================

/-- The middle binomial coefficient `Nat.choose n (n / 2)`. -/
def middleChoose (n : ℕ) : ℕ :=
  Nat.choose n (n / 2)

/-- The middle binomial coefficient is maximal among all binomial coefficients `Nat.choose n k`. -/
lemma choose_le_middleChoose (n k : ℕ) (_hk : k ≤ n) :
    Nat.choose n k ≤ middleChoose n :=
  Nat.choose_le_middle k n

lemma choose_lt_succ_of_lt_half_left {n k : ℕ} (hk : k < n / 2) :
    Nat.choose n k < Nat.choose n (k + 1) := by
  have h_mul : Nat.choose n k * (k + 1) < Nat.choose n k * (n - k) :=
    Nat.mul_lt_mul_of_pos_left (by omega) (Nat.choose_pos (by omega))
  rw [← Nat.choose_succ_right_eq] at h_mul
  exact Nat.lt_of_mul_lt_mul_right h_mul

lemma choose_lt_middle_of_lt_half_left {n k : ℕ} (hk : k < n / 2) :
    Nat.choose n k < Nat.choose n (n / 2) := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hk
  induction d generalizing k with
  | zero =>
    have : k + 1 = n / 2 := by omega
    rw [← this]
    exact choose_lt_succ_of_lt_half_left hk
  | succ d ih =>
    exact (choose_lt_succ_of_lt_half_left hk).trans (ih (by omega) (by omega))

lemma choose_lt_middleChoose_of_ne {n k : ℕ} (hk : k ≤ n)
    (h1 : k ≠ n / 2) (h2 : k ≠ n - n / 2) :
    Nat.choose n k < middleChoose n := by
  unfold middleChoose
  rcases lt_or_gt_of_ne h1 with hlt | hgt
  · exact choose_lt_middle_of_lt_half_left hlt
  · rw [← Nat.choose_symm hk]
    exact choose_lt_middle_of_lt_half_left (by omega)

omit [Fintype α] in
lemma sdiff_erase_insert_eq {s t : Finset α} {x y : α}
    (_hx : x ∈ t) (hy : y ∉ t) :
    t \ (insert x (s.erase y)) = (t \ s).erase x := by
  ext a
  simp only [mem_sdiff, mem_insert, mem_erase]
  aesop

/-- Any non-empty family of `m`-element subsets closed under single-element swaps
    must be the entire layer `powersetCard m univ`. -/
lemma all_powersetCard_of_swap_closed (m : ℕ) (S : Finset (Finset α))
    (h_nonempty : S.Nonempty)
    (h_sized : ∀ s ∈ S, s.card = m)
    (h_swap : ∀ s ∈ S, ∀ y ∈ s, ∀ x ∉ s, insert x (s.erase y) ∈ S) :
    S = (Finset.univ : Finset α).powersetCard m := by
  ext t
  simp only [mem_powersetCard, subset_univ, true_and]
  refine ⟨fun ht => h_sized t ht, fun ht_card => ?_⟩
  obtain ⟨s0, hs0⟩ := h_nonempty
  have H : ∀ d : ℕ, ∀ s ∈ S, ∀ t : Finset α, t.card = m → (t \ s).card = d → t ∈ S := by
    intro d
    induction d with
    | zero =>
      intro s hs t ht hd
      have h_sub : t ⊆ s := by rw [← sdiff_eq_empty_iff_subset, card_eq_zero.mp hd]
      rwa [eq_of_subset_of_card_le h_sub (by rw [ht, h_sized s hs])]
    | succ d ih =>
      intro s hs t ht hd
      have h_ne : (t \ s).Nonempty := by rw [← card_pos, hd]; exact Nat.succ_pos d
      obtain ⟨x, hx⟩ := h_ne
      have hx_t : x ∈ t := (mem_sdiff.mp hx).1
      have hx_s : x ∉ s := (mem_sdiff.mp hx).2
      have hs_not_sub : ¬ s ⊆ t := fun h => hx_s (eq_of_subset_of_card_le h (by rw [h_sized s hs, ht]) ▸ hx_t)
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
  by_contra! h_ne
  have hs_le : s.card ≤ n := by rw [← hn]; exact s.card_le_univ
  have h_mid_pos : (0 : ℚ) < middleChoose n := Nat.cast_pos.mpr (Nat.choose_pos (Nat.div_le_self n 2))
  have h_w_lt : (1 : ℚ) / (middleChoose n : ℚ) < lymWeight n s := by
    unfold lymWeight
    rw [one_div, one_div, inv_lt_inv₀ h_mid_pos (Nat.cast_pos.mpr (Nat.choose_pos hs_le))]
    exact Nat.cast_lt.mpr (choose_lt_middleChoose_of_ne hs_le h_ne.1 h_ne.2)
  have h_w_le : ∀ t ∈ A.erase s, (1 : ℚ) / (middleChoose n : ℚ) ≤ lymWeight n t := by
    intro t ht
    have ht_le : t.card ≤ n := by rw [← hn]; exact t.card_le_univ
    have ht_qpos : (0 : ℚ) < Nat.choose n t.card := Nat.cast_pos.mpr (Nat.choose_pos ht_le)
    unfold lymWeight
    rw [one_div, one_div, inv_le_inv₀ h_mid_pos ht_qpos]
    exact Nat.cast_le.mpr (choose_le_middleChoose n t.card ht_le)
  have h_sum_lt : ∑ t ∈ A, ((1 : ℚ) / (middleChoose n : ℚ)) < lymSum n A := by
    unfold lymSum
    rw [← Finset.add_sum_erase A (fun _ => (1 : ℚ) / (middleChoose n : ℚ)) hs,
        ← Finset.add_sum_erase A (lymWeight n) hs]
    have := sum_le_sum h_w_le
    linarith
  have h_sum_eq_one : ∑ t ∈ A, ((1 : ℚ) / (middleChoose n : ℚ)) = 1 := by
    rw [sum_const, nsmul_eq_mul, h_eq, mul_one_div, div_self h_mid_pos.ne']
  have h_lym := lym_inequality hn A h_anti
  linarith

omit [DecidableEq α] in
/-- **Sperner's Theorem on Antichains (Sperner, 1928):**
    The maximum cardinality of an antichain of subsets of an `n`-element set is `Nat.choose n (n / 2)`. -/
theorem sperners_antichain_theorem {n : ℕ} (hn : Fintype.card α = n)
    (A : Finset (Finset α)) (h_anti : IsAntichain A) :
    A.card ≤ middleChoose n := by
  have h_anti' : _root_.IsAntichain (· ⊆ ·) (A : Set (Finset α)) :=
    fun a ha b hb hab => hab ∘ h_anti a ha b hb
  simpa [middleChoose, hn] using _root_.IsAntichain.sperner h_anti'

-- ============================================================================
-- Section 4: Equality Cases & Modularized Decompositions
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
  obtain ⟨k, rfl⟩ := heven
  have h_or := card_eq_or_eq_of_card_eq_middleChoose hn A h_anti h_eq s hs
  omega

omit [Fintype α] in
/-- For an antichain `A`, the `m`-sized layer `Am` and the shadow `∂ B` of any `(m+1)`-sized
subfamily `B ⊆ A` are disjoint. -/
lemma shadow_disjoint_of_antichain (A : Finset (Finset α)) (h_anti : IsAntichain A)
    {m : ℕ} {B Am : Finset (Finset α)}
    (hB_sub : B ⊆ A) (hB_sized : ∀ s ∈ B, s.card = m + 1)
    (hAm_sub : Am ⊆ A) (hAm_sized : ∀ s ∈ Am, s.card = m) :
    Disjoint Am (∂ B) := by
  rw [disjoint_iff_ne]
  rintro u hu _ hv rfl
  rw [mem_shadow_iff] at hv
  obtain ⟨s, hs_B, a, ha_s, rfl⟩ := hv
  have hu_eq_s := h_anti (s.erase a) (hAm_sub hu) s (hB_sub hs_B) (erase_subset a s)
  have := congr_arg Finset.card hu_eq_s
  rw [hAm_sized (s.erase a) hu, hB_sized s hs_B] at this
  omega

/-- When an antichain's middle layers achieve the capacity `middleChoose (2 * m + 1)`,
the shadow `∂ B` has the exact same cardinality as `B`. -/
lemma shadow_card_eq_of_extremal {m : ℕ} (hn : Fintype.card α = 2 * m + 1)
    {B Am : Finset (Finset α)}
    (hB_sized : (B : Set (Finset α)).Sized (m + 1))
    (hAm_sized : (Am : Set (Finset α)).Sized m)
    (h_disj : Disjoint Am (∂ B))
    (h_sum : Am.card + B.card = middleChoose (2 * m + 1)) :
    B.card = (∂ B).card := by
  have h_shB_sized : (∂ B : Set (Finset α)).Sized m := by
    have := Set.Sized.shadow hB_sized
    rwa [add_tsub_cancel_right] at this
  have h_sub_pow : Am ∪ ∂ B ⊆ (Finset.univ : Finset α).powersetCard m := by
    intro u hu
    simp only [mem_powersetCard, subset_univ, true_and]
    rcases mem_union.mp hu with hu | hu
    · exact hAm_sized hu
    · exact h_shB_sized hu
  have h_lym_B := local_lubell_yamamoto_meshalkin_inequality_mul hB_sized
  rw [hn] at h_lym_B
  have h_le_mid : (Am ∪ ∂ B).card ≤ middleChoose (2 * m + 1) := by
    have h1 := card_le_card h_sub_pow
    rw [card_powersetCard, card_univ, hn] at h1
    unfold middleChoose
    have : (2 * m + 1) / 2 = m := by omega
    rwa [this]
  rw [card_union_of_disjoint h_disj] at h_le_mid
  have h_B_le : B.card ≤ (∂ B).card := by
    have : 2 * m + 1 - (m + 1) + 1 = m + 1 := by omega
    rw [this] at h_lym_B
    exact Nat.le_of_mul_le_mul_right h_lym_B (by omega)
  omega

/-- Double counting degrees between `B` and `∂ B` forces maximal degree `m + 1` in the incidence graph. -/
lemma bipartite_incidence_eq {m : ℕ} (hn : Fintype.card α = 2 * m + 1)
    {B : Finset (Finset α)} (hB_sized : (B : Set (Finset α)).Sized (m + 1))
    (h_eq_card : B.card = (∂ B).card) (u : Finset α) (hu : u ∈ ∂ B) :
    #(B.bipartiteAbove (· ⊆ ·) u) = m + 1 := by
  have h_shB_sized : (∂ B : Set (Finset α)).Sized m := by
    have := Set.Sized.shadow hB_sized
    rwa [add_tsub_cancel_right] at this
  have hb_below : ∀ b ∈ B, m + 1 ≤ #((∂ B).bipartiteBelow (· ⊆ ·) b) := by
    intro b hb
    have hb_card : b.card = m + 1 := hB_sized hb
    have h_sub : b.image (fun a => b.erase a) ⊆ (∂ B).bipartiteBelow (· ⊆ ·) b := by
      intro v hv
      simp only [mem_image] at hv
      obtain ⟨a, ha_b, rfl⟩ := hv
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
  have hu_above : ∀ v ∈ ∂ B, #(B.bipartiteAbove (· ⊆ ·) v) ≤ m + 1 := by
    intro v hv
    have hv_card : v.card = m := h_shB_sized hv
    have h_sub : B.bipartiteAbove (· ⊆ ·) v ⊆ (Finset.univ \ v).image (fun a => insert a v) := by
      intro s hs
      simp only [mem_bipartiteAbove] at hs
      obtain ⟨hs_B, hv_sub_s⟩ := hs
      have hs_card : s.card = m + 1 := hB_sized hs_B
      have h_ins : ∃ a ∉ v, insert a v = s := by
        apply exists_eq_insert_iff.mpr
        exact ⟨hv_sub_s, by omega⟩
      obtain ⟨a, ha_not, rfl⟩ := h_ins
      simp only [mem_image, mem_sdiff, mem_univ, true_and]
      exact ⟨a, ha_not, rfl⟩
    have h_card_im : ((Finset.univ \ v).image (fun a => insert a v)).card ≤ m + 1 := by
      refine le_trans card_image_le ?_
      rw [card_sdiff_of_subset (subset_univ v), card_univ, hn, hv_card]
      omega
    exact le_trans (card_le_card h_sub) h_card_im
  have h_sum_below : B.card * (m + 1) ≤ ∑ b ∈ B, #((∂ B).bipartiteBelow (· ⊆ ·) b) := by
    have := sum_le_sum (fun b hb => hb_below b hb)
    rwa [sum_const, nsmul_eq_mul] at this
  have h_sum_above : ∑ v ∈ ∂ B, #(B.bipartiteAbove (· ⊆ ·) v) ≤ (∂ B).card * (m + 1) := by
    have := sum_le_sum (fun v hv => hu_above v hv)
    rwa [sum_const, nsmul_eq_mul] at this
  have h_sum_eq : (∑ v ∈ ∂ B, #(B.bipartiteAbove (· ⊆ ·) v)) = ∑ b ∈ B, #((∂ B).bipartiteBelow (· ⊆ ·) b) :=
    sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (r := ((· ⊆ ·) : Finset α → Finset α → Prop))
  have h_all_sum_eq : ∑ v ∈ ∂ B, #(B.bipartiteAbove (· ⊆ ·) v) = (∂ B).card * (m + 1) := by
    have h2 : (∂ B).card * (m + 1) ≤ ∑ b ∈ B, #((∂ B).bipartiteBelow (· ⊆ ·) b) := by
      rwa [← h_eq_card]
    omega
  exact sum_eq_of_forall_le_and_sum_eq (∂ B) (fun v => #(B.bipartiteAbove (· ⊆ ·) v)) (m + 1)
    hu_above h_all_sum_eq u hu

lemma insert_mem_of_degree_eq {m : ℕ} (hn : Fintype.card α = 2 * m + 1)
    {B : Finset (Finset α)} (hB_sized : (B : Set (Finset α)).Sized (m + 1))
    (u : Finset α) (hu_card : u.card = m)
    (h_deg : #(B.bipartiteAbove (· ⊆ ·) u) = m + 1) (x : α) (hx : x ∉ u) :
    insert x u ∈ B := by
  have h_sub : B.bipartiteAbove (· ⊆ ·) u ⊆ (Finset.univ \ u).image (fun a => insert a u) := by
    intro t ht
    simp only [mem_bipartiteAbove] at ht
    obtain ⟨ht_B, hu_sub_t⟩ := ht
    have ht_card : t.card = m + 1 := hB_sized ht_B
    obtain ⟨a, ha_not, rfl⟩ := exists_eq_insert_iff.mpr ⟨hu_sub_t, by omega⟩
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
    rw [card_image_of_injOn h_inj, card_sdiff_of_subset (subset_univ u), card_univ, hn, hu_card]
    omega
  have h_above_eq : B.bipartiteAbove (· ⊆ ·) u = (Finset.univ \ u).image (fun a => insert a u) :=
    eq_of_subset_of_card_le h_sub (by rw [h_deg, h_card_im])
  have hx_im : insert x u ∈ (Finset.univ \ u).image (fun a => insert a u) := by
    simp only [mem_image, mem_sdiff, mem_univ, true_and]
    exact ⟨x, hx, rfl⟩
  rw [← h_above_eq] at hx_im
  simp only [mem_bipartiteAbove] at hx_im
  exact hx_im.1

/-- Deduce that `B` is closed under single-element swaps `insert x (s.erase y) ∈ B`. -/
lemma swap_closed_of_extremal_shadow {m : ℕ} (hn : Fintype.card α = 2 * m + 1)
    {B : Finset (Finset α)} (hB_sized : (B : Set (Finset α)).Sized (m + 1))
    (h_eq_card : B.card = (∂ B).card) :
    ∀ s ∈ B, ∀ y ∈ s, ∀ x ∉ s, insert x (s.erase y) ∈ B := by
  have h_shB_sized : (∂ B : Set (Finset α)).Sized m := by
    have := Set.Sized.shadow hB_sized
    rwa [add_tsub_cancel_right] at this
  intro s hs y hy x hx
  have hu : s.erase y ∈ ∂ B := erase_mem_shadow hs hy
  have hu_card : (s.erase y).card = m := h_shB_sized hu
  have h_deg := bipartite_incidence_eq hn hB_sized h_eq_card (s.erase y) hu
  exact insert_mem_of_degree_eq hn hB_sized (s.erase y) hu_card h_deg x (fun h => hx (mem_of_mem_erase h))

/-- An extremal antichain cannot simultaneously contain elements of size `m` and size `m + 1`. -/
lemma no_mixed_middle_layers {m : ℕ} (hn : Fintype.card α = 2 * m + 1) (_hm : m ≠ 0)
    (A : Finset (Finset α)) (h_anti : IsAntichain A)
    (h_eq : A.card = middleChoose (2 * m + 1))
    {s t : Finset α} (hs : s ∈ A) (hs_card : s.card = m)
    (ht : t ∈ A) (ht_card : t.card = m + 1) : False := by
  let B : Finset (Finset α) := A.filter (fun u => u.card = m + 1)
  let Am : Finset (Finset α) := A.filter (fun u => u.card = m)
  have hB_nonempty : B.Nonempty := ⟨t, mem_filter.mpr ⟨ht, ht_card⟩⟩
  have hAm_nonempty : Am.Nonempty := ⟨s, mem_filter.mpr ⟨hs, hs_card⟩⟩
  have hB_sized : (B : Set (Finset α)).Sized (m + 1) := fun u hu => (mem_filter.mp hu).2
  have hAm_sized : (Am : Set (Finset α)).Sized m := fun u hu => (mem_filter.mp hu).2
  have h_disj_Am_B : Disjoint Am B := by
    rw [disjoint_filter]
    intro _ _ h1 h2
    omega
  have h_card_A : A.card = Am.card + B.card := by
    have h_eq_union : A = Am ∪ B := by
      ext u
      simp only [mem_union]
      constructor
      · intro hu
        rcases card_eq_or_eq_of_card_eq_middleChoose hn A h_anti h_eq u hu with h | h
        · exact Or.inl (mem_filter.mpr ⟨hu, by omega⟩)
        · exact Or.inr (mem_filter.mpr ⟨hu, by omega⟩)
      · rintro (hu | hu)
        · exact (mem_filter.mp hu).1
        · exact (mem_filter.mp hu).1
    rw [h_eq_union, card_union_of_disjoint h_disj_Am_B]
  have h_sum_cards : Am.card + B.card = middleChoose (2 * m + 1) := by
    rw [← h_card_A, h_eq]
  have h_disj_Am_shB : Disjoint Am (∂ B) :=
    shadow_disjoint_of_antichain A h_anti (fun _ hu => (mem_filter.mp hu).1) hB_sized
      (fun _ hu => (mem_filter.mp hu).1) hAm_sized
  have h_B_eq_shB : B.card = (∂ B).card :=
    shadow_card_eq_of_extremal hn hB_sized hAm_sized h_disj_Am_shB h_sum_cards
  have h_swap : ∀ u ∈ B, ∀ y ∈ u, ∀ x ∉ u, insert x (u.erase y) ∈ B :=
    swap_closed_of_extremal_shadow hn hB_sized h_B_eq_shB
  have h_B_all := all_powersetCard_of_swap_closed (m + 1) B hB_nonempty hB_sized h_swap
  have h_B_card_all : B.card = middleChoose (2 * m + 1) := by
    rw [h_B_all, card_powersetCard, card_univ, hn]
    unfold middleChoose
    have : (2 * m + 1) / 2 = m := by omega
    rw [this]
    have h_symm : (2 * m + 1).choose (m + 1) = (2 * m + 1).choose (2 * m + 1 - (m + 1)) :=
      (Nat.choose_symm (by omega)).symm
    rwa [show 2 * m + 1 - (m + 1) = m by omega] at h_symm
  have h_Am_zero : Am.card = 0 := by omega
  have h_Am_pos : 0 < Am.card := card_pos.mpr hAm_nonempty
  omega

/-- An antichain achieving the maximal size `middleChoose n` is a middle level slice. -/
theorem sperners_antichain_equality {n : ℕ} (hn : Fintype.card α = n)
    (A : Finset (Finset α)) (h_anti : IsAntichain A)
    (h_eq : A.card = middleChoose n) :
    (∀ s ∈ A, s.card = n / 2) ∨ (Odd n ∧ ∀ s ∈ A, s.card = (n + 1) / 2) := by
  by_cases heven : Even n
  · exact Or.inl (sperners_antichain_equality_even hn A h_anti h_eq heven)
  · obtain ⟨m, rfl⟩ := Nat.not_even_iff_odd.mp heven
    by_cases h_all_m : ∀ s ∈ A, s.card = (2 * m + 1) / 2
    · exact Or.inl h_all_m
    · refine Or.inr ⟨⟨m, rfl⟩, fun t ht => ?_⟩
      simp only [not_forall] at h_all_m
      obtain ⟨t0, ht0_in, ht0_ne⟩ := h_all_m
      have ht0_card : t0.card = m + 1 := by
        rcases card_eq_or_eq_of_card_eq_middleChoose hn A h_anti h_eq t0 ht0_in with h | h
        · exact (ht0_ne (by omega)).elim
        · omega
      rcases card_eq_or_eq_of_card_eq_middleChoose hn A h_anti h_eq t ht with ht_m | ht_succ
      · by_cases hm0 : m = 0
        · subst hm0
          have ht_empty : t = ∅ := card_eq_zero.mp (by omega)
          have : t.card = t0.card := congr_arg Finset.card
            (h_anti t ht t0 ht0_in (by rw [ht_empty]; exact empty_subset t0))
          omega
        · exact (no_mixed_middle_layers hn hm0 A h_anti h_eq ht (by omega) ht0_in ht0_card).elim
      · omega

end SpernerAntichain
