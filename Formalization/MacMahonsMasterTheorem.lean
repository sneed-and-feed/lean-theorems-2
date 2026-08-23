import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators Matrix
open Classical

set_option linter.unusedSectionVars false

/-!
# MacMahon's Master Theorem

This module formalizes **MacMahon's Master Theorem** (Major Percy Alexander MacMahon, 1915),
relating the coefficients of products of linear forms to the reciprocal determinant of a matrix:
$$[X^s] \prod_{i=1}^n \left(\sum_{j=1}^n A_{ij} X_j\right)^{s_i} = [X^s] \frac{1}{\det(I_n - X A)}$$
-/

variable {R : Type*} [CommRing R] {n : ℕ}

namespace MacMahon

/-- Convert a function $s : \text{Fin } n \to \mathbb{N}$ to a finitely supported multi-index. -/
noncomputable def toFinsupp (s : Fin n → ℕ) : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm s

/-- The $i$-th linear form $Y_i = \sum_{j=1}^n A_{ij} X_j$ in $R[X_1, \dots, X_n]$. -/
noncomputable def linearForm (A : Matrix (Fin n) (Fin n) R) (i : Fin n) : MvPolynomial (Fin n) R :=
  ∑ j : Fin n, MvPolynomial.C (A i j) * MvPolynomial.X j

/-- The product of powers of linear forms $\prod_{i=1}^n Y_i^{s_i}$. -/
noncomputable def prodLinearForms (A : Matrix (Fin n) (Fin n) R) (s : Fin n → ℕ) : MvPolynomial (Fin n) R :=
  ∏ i : Fin n, (linearForm A i) ^ (s i)

/-- The matrix $I_n - X A$ whose $(i, j)$ entry is $\delta_{ij} - X_i A_{ij}$. -/
noncomputable def macmahonMatrix (A : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) R) :=
  Matrix.of (fun i j => (if i = j then (1 : MvPolynomial (Fin n) R) else 0) -
    MvPolynomial.X i * MvPolynomial.C (A i j))

/-- The polynomial determinant $\det(I_n - X A)$. -/
noncomputable def detMacMahon (A : Matrix (Fin n) (Fin n) R) : MvPolynomial (Fin n) R :=
  Matrix.det (macmahonMatrix A)

/-- The reciprocal determinant $\det(I_n - X A)^{-1}$ as a formal power series. -/
noncomputable def invDetMacMahon (A : Matrix (Fin n) (Fin n) R) : MvPowerSeries (Fin n) R :=
  MvPowerSeries.invOfUnit (MvPolynomial.toMvPowerSeries (detMacMahon A)) 1

theorem macmahon_zero_exponent (A : Matrix (Fin n) (Fin n) R) :
    MvPolynomial.coeff (toFinsupp (fun _ => 0)) (prodLinearForms A (fun _ => 0)) = 1 := by
  have h_prod : prodLinearForms A (fun _ => 0) = 1 := by dsimp [prodLinearForms]; simp
  have h_finsupp : toFinsupp (fun _ : Fin n => 0) = 0 := by ext i; simp [toFinsupp]
  rw [h_prod, h_finsupp, ← MvPolynomial.C_1, MvPolynomial.coeff_zero_C]

theorem coeff_zero_detMacMahon (A : Matrix (Fin n) (Fin n) R) :
    MvPolynomial.coeff 0 (detMacMahon A) = 1 := by
  rw [← MvPolynomial.constantCoeff_eq, detMacMahon, RingHom.map_det]
  have : (MvPolynomial.constantCoeff.mapMatrix (macmahonMatrix A)) = 1 := by
    ext i j; simp [macmahonMatrix, Matrix.one_apply]
  rw [this, Matrix.det_one]

theorem invOfUnit_one_eq_of_antidiagonal_eq_zero {σ : Type*} [DecidableEq σ]
    (φ : MvPowerSeries σ R) (g : (σ →₀ ℕ) → R)
    (hφ0 : MvPowerSeries.coeff 0 φ = 1) (hg0 : g 0 = 1)
    (hrec : ∀ m : σ →₀ ℕ, m ≠ 0 → ∑ x ∈ Finset.antidiagonal m, MvPowerSeries.coeff x.1 φ * g x.2 = 0) :
    ∀ m : σ →₀ ℕ, g m = MvPowerSeries.coeff m (MvPowerSeries.invOfUnit φ 1) := by
  intro m
  induction m using WellFoundedLT.induction with
  | ind m ih =>
    by_cases hm : m = 0
    · subst hm; rw [hg0, MvPowerSeries.coeff_invOfUnit]; simp
    · rw [MvPowerSeries.coeff_invOfUnit]
      simp only [hm, ite_false, Units.val_one, inv_one, one_mul, neg_mul]
      have h0m : ((0 : σ →₀ ℕ), m) ∈ Finset.antidiagonal m := by rw [Finset.mem_antidiagonal, zero_add]
      have h_sum : ∑ x ∈ Finset.antidiagonal m, MvPowerSeries.coeff x.1 φ * g x.2 =
          g m + ∑ x ∈ Finset.antidiagonal m, if x.2 < m then MvPowerSeries.coeff x.1 φ * g x.2 else 0 := by
        rw [← Finset.insert_erase h0m, Finset.sum_insert (Finset.notMem_erase _ _)]
        simp only [hφ0, one_mul]
        congr 1
        rw [← Finset.insert_erase h0m, Finset.sum_insert (Finset.notMem_erase _ _)]
        simp only [not_lt_of_ge le_rfl, ite_false, zero_add, Finset.erase_insert (Finset.notMem_erase _ _)]
        refine Finset.sum_congr rfl (fun ⟨i, j⟩ hij => ?_)
        rw [Finset.mem_erase, Finset.mem_antidiagonal] at hij
        obtain ⟨hne, hij_in⟩ := hij
        have hjlt : j < m := by
          refine lt_of_le_of_ne ?_ ?_
          · rw [← hij_in]; exact le_add_self
          · rintro rfl
            apply hne
            have hi : i = 0 := by
              have : i + j = 0 + j := by rw [hij_in, zero_add]
              exact add_right_cancel this
            rw [hi]
        simp only [hjlt, ite_true]
      have hrec_m := hrec m hm
      rw [h_sum] at hrec_m
      have hgm : g m = - ∑ x ∈ Finset.antidiagonal m, if x.2 < m then MvPowerSeries.coeff x.1 φ * g x.2 else 0 :=
        eq_neg_of_add_eq_zero_left hrec_m
      rw [hgm, neg_inj]
      refine Finset.sum_congr rfl (fun ⟨i, j⟩ _ => ?_)
      split_ifs with hj
      · rw [ih j hj]
      · rfl

noncomputable def G (A : Matrix (Fin n) (Fin n) R) (m : Fin n →₀ ℕ) : R :=
  MvPolynomial.coeff m (prodLinearForms A (Finsupp.equivFunOnFinite m))

theorem G_zero (A : Matrix (Fin n) (Fin n) R) : G A 0 = 1 := by
  dsimp [G]
  have : Finsupp.equivFunOnFinite (0 : Fin n →₀ ℕ) = (fun _ => 0) := by ext; rfl
  rw [this]
  have := macmahon_zero_exponent A
  have h_finsupp : toFinsupp (fun _ : Fin n => 0) = 0 := by ext; simp [toFinsupp]
  rwa [h_finsupp] at this

theorem toMvPowerSeries_coeff_eq_coeff (P : MvPolynomial (Fin n) R) (d : Fin n →₀ ℕ) :
    MvPowerSeries.coeff d (MvPolynomial.toMvPowerSeries P) = MvPolynomial.coeff d P := rfl

noncomputable def subdetCoeff (A : Matrix (Fin n) (Fin n) R) (K : Finset (Fin n)) : MvPolynomial (Fin n) R :=
  ∑ σ : Equiv.Perm (Fin n), (if ∀ i ∉ K, σ i = i then 1 else 0) *
    (Equiv.Perm.sign σ • ((-1 : MvPolynomial (Fin n) R) ^ K.card * MvPolynomial.C (∏ i ∈ K, A i (σ i))))

noncomputable def subdetCoeffScalar (A : Matrix (Fin n) (Fin n) R) (K : Finset (Fin n)) : R :=
  ∑ σ : Equiv.Perm (Fin n), (if ∀ i ∉ K, σ i = i then 1 else 0) *
    (Equiv.Perm.sign σ • ((-1 : R) ^ K.card * (∏ i ∈ K, A i (σ i))))

theorem subdetCoeff_eq_C (A : Matrix (Fin n) (Fin n) R) (K : Finset (Fin n)) :
    subdetCoeff A K = MvPolynomial.C (subdetCoeffScalar A K) := by
  dsimp [subdetCoeff, subdetCoeffScalar]
  simp only [map_sum, map_mul, Units.smul_def]
  refine Finset.sum_congr rfl (fun σ _ => by split_ifs <;> simp)

noncomputable def indicatorFinsupp (K : Finset (Fin n)) : Fin n →₀ ℕ :=
  ∑ i ∈ K, Finsupp.single i 1

theorem indicatorFinsupp_apply (K : Finset (Fin n)) (i : Fin n) :
    indicatorFinsupp K i = if i ∈ K then 1 else 0 := by
  dsimp [indicatorFinsupp]
  rw [Finsupp.finsetSum_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (fun h' => (h' h).elim)]; simp
  · exact Finset.sum_eq_zero (fun j hj => by simp [show j ≠ i by rintro rfl; exact h hj])

theorem prod_X_eq_monomial (K : Finset (Fin n)) :
    (∏ i ∈ K, (MvPolynomial.X i : MvPolynomial (Fin n) R)) = MvPolynomial.monomial (indicatorFinsupp K) 1 := by
  induction K using Finset.induction_on with
  | empty => simp [indicatorFinsupp]
  | @insert i s hi ih =>
    dsimp [indicatorFinsupp] at ih ⊢
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul]

theorem subdetCoeff_mul_prod_X (A : Matrix (Fin n) (Fin n) R) (K : Finset (Fin n)) :
    subdetCoeff A K * ∏ i ∈ K, (MvPolynomial.X i : MvPolynomial (Fin n) R) =
    MvPolynomial.monomial (indicatorFinsupp K) (subdetCoeffScalar A K) := by
  rw [subdetCoeff_eq_C, prod_X_eq_monomial, MvPolynomial.C_mul_monomial, mul_one]

theorem prod_ite_eq_self (t : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) (f : Fin n → MvPolynomial (Fin n) R) :
    (∏ i ∈ t, (if i = σ i then f i else 0)) = if ∀ i ∈ t, σ i = i then ∏ i ∈ t, f i else 0 := by
  split_ifs with h
  · refine Finset.prod_congr rfl (fun i hi => by simp [h i hi])
  · push Not at h
    obtain ⟨i, hi, hne⟩ := h
    exact Finset.prod_eq_zero hi (by split_ifs with h' <;> [exact (hne h'.symm).elim; rfl])

theorem prod_neg_if_X_mul_C (K : Finset (Fin n)) (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) (A : Matrix (Fin n) (Fin n) R) :
    (∏ i ∈ K, (- (if i ∈ S then MvPolynomial.X i * MvPolynomial.C (A i (σ i)) else 0))) =
    if K ⊆ S then (-1 : MvPolynomial (Fin n) R) ^ K.card * (∏ i ∈ K, MvPolynomial.X i) * MvPolynomial.C (∏ i ∈ K, A i (σ i)) else 0 := by
  split_ifs with hK
  · have : (∏ i ∈ K, (- (if i ∈ S then MvPolynomial.X i * MvPolynomial.C (A i (σ i)) else 0))) =
        ∏ i ∈ K, ((-1 : MvPolynomial (Fin n) R) * MvPolynomial.X i * MvPolynomial.C (A i (σ i))) :=
      Finset.prod_congr rfl (fun i hi => by simp [hK hi])
    rw [this, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, map_prod]
  · obtain ⟨i, hiK, hiS⟩ := Finset.not_subset.mp hK
    exact Finset.prod_eq_zero hiK (by simp [hiS])

def complEquiv : Finset (Fin n) ≃ Finset (Fin n) where
  toFun := compl
  invFun := compl
  left_inv := compl_compl
  right_inv := compl_compl

noncomputable def genMatrix (D : Fin n → MvPolynomial (Fin n) R) (S : Finset (Fin n))
    (A : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) R) :=
  Matrix.of (fun i j => (if i = j then D i else 0) - (if i ∈ S then MvPolynomial.X i * MvPolynomial.C (A i j) else 0))

theorem det_genMatrix (D : Fin n → MvPolynomial (Fin n) R) (S : Finset (Fin n)) (A : Matrix (Fin n) (Fin n) R) :
    Matrix.det (genMatrix D S A) = ∑ K ∈ (Finset.univ : Finset (Fin n)).powerset,
      if K ⊆ S then (∏ i ∈ Finset.univ \ K, D i) * MvPolynomial.monomial (indicatorFinsupp K) (subdetCoeffScalar A K) else 0 := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  have h_prod (σ : Equiv.Perm (Fin n)) : (∏ i : Fin n, (genMatrix D S A)ᵀ (σ i) i) =
      ∑ t ∈ (Finset.univ : Finset (Fin n)).powerset, (if ∀ i ∈ t, σ i = i then ∏ i ∈ t, D i else 0) *
        if Finset.univ \ t ⊆ S then ((-1 : MvPolynomial (Fin n) R) ^ (Finset.univ \ t).card *
          (∏ i ∈ Finset.univ \ t, MvPolynomial.X i) * MvPolynomial.C (∏ i ∈ Finset.univ \ t, A i (σ i))) else 0 := by
    have h_entry : (fun i => (genMatrix D S A)ᵀ (σ i) i) =
        fun i => (if i = σ i then D i else 0) + (- if i ∈ S then MvPolynomial.X i * MvPolynomial.C (A i (σ i)) else 0) := by
      ext i; simp [genMatrix, Matrix.transpose_apply, sub_eq_add_neg]
    rw [h_entry, Finset.prod_add]
    exact Finset.sum_congr rfl (fun t _ => by rw [prod_ite_eq_self t σ D, prod_neg_if_X_mul_C (Finset.univ \ t) S σ A])
  simp_rw [h_prod, Finset.smul_sum]
  have h_comp (σ : Equiv.Perm (Fin n)) :
      (∑ t ∈ (Finset.univ : Finset (Fin n)).powerset, Equiv.Perm.sign σ •
        ((if ∀ i ∈ t, σ i = i then ∏ i ∈ t, D i else 0) *
          if Finset.univ \ t ⊆ S then ((-1 : MvPolynomial (Fin n) R) ^ (Finset.univ \ t).card *
            (∏ i ∈ Finset.univ \ t, MvPolynomial.X i) * MvPolynomial.C (∏ i ∈ Finset.univ \ t, A i (σ i))) else 0)) =
      ∑ K ∈ (Finset.univ : Finset (Fin n)).powerset, Equiv.Perm.sign σ •
        ((if ∀ i ∉ K, σ i = i then ∏ i ∈ Finset.univ \ K, D i else 0) *
          if K ⊆ S then ((-1 : MvPolynomial (Fin n) R) ^ K.card * (∏ i ∈ K, MvPolynomial.X i) *
            MvPolynomial.C (∏ i ∈ K, A i (σ i))) else 0) := by
    have h_rw : (∑ t ∈ (Finset.univ : Finset (Fin n)).powerset, Equiv.Perm.sign σ •
        ((if ∀ i ∈ t, σ i = i then ∏ i ∈ t, D i else 0) *
          if Finset.univ \ t ⊆ S then ((-1 : MvPolynomial (Fin n) R) ^ (Finset.univ \ t).card *
            (∏ i ∈ Finset.univ \ t, MvPolynomial.X i) * MvPolynomial.C (∏ i ∈ Finset.univ \ t, A i (σ i))) else 0)) =
        ∑ t ∈ (Finset.univ : Finset (Fin n)).powerset, Equiv.Perm.sign σ •
          ((if ∀ i ∉ Finset.univ \ t, σ i = i then ∏ i ∈ Finset.univ \ (Finset.univ \ t), D i else 0) *
            if Finset.univ \ t ⊆ S then ((-1 : MvPolynomial (Fin n) R) ^ (Finset.univ \ t).card *
              (∏ i ∈ Finset.univ \ t, MvPolynomial.X i) * MvPolynomial.C (∏ i ∈ Finset.univ \ t, A i (σ i))) else 0) :=
      Finset.sum_congr rfl (fun t _ => by simp [Finset.mem_sdiff])
    rw [h_rw, Finset.powerset_univ]; exact Fintype.sum_equiv (complEquiv (n := n)) _ _ (fun _ => rfl)
  simp_rw [h_comp, Finset.sum_comm (s := Finset.univ)]
  refine Finset.sum_congr rfl (fun K _ => ?_)
  split_ifs with hKS
  · rw [← subdetCoeff_mul_prod_X, ← mul_assoc, mul_comm (∏ i ∈ Finset.univ \ K, D i), mul_assoc]
    dsimp [subdetCoeff]
    simp only [Finset.sum_mul, Units.smul_def]
    exact Finset.sum_congr rfl (fun σ _ => by split_ifs <;> ring)
  · simp

theorem detMacMahon_eq_sum_monomial (A : Matrix (Fin n) (Fin n) R) :
    detMacMahon A = ∑ K ∈ (Finset.univ : Finset (Fin n)).powerset,
      MvPolynomial.monomial (indicatorFinsupp K) (subdetCoeffScalar A K) := by
  have h : macmahonMatrix A = genMatrix (fun _ => 1) Finset.univ A := by ext i j; simp [macmahonMatrix, genMatrix]
  rw [detMacMahon, h, det_genMatrix]; simp

theorem sum_antidiagonal_ite_eq_indicator (m : Fin n →₀ ℕ) (K : Finset (Fin n)) (c : R) (g : (Fin n →₀ ℕ) → R) :
    (∑ x ∈ Finset.antidiagonal m, (if x.1 = indicatorFinsupp K then c * g x.2 else 0)) =
    if indicatorFinsupp K ≤ m then c * g (m - indicatorFinsupp K) else 0 := by
  split_ifs with hle
  · have h_mem : (indicatorFinsupp K, m - indicatorFinsupp K) ∈ Finset.antidiagonal m := by
      rw [Finset.mem_antidiagonal, add_tsub_cancel_of_le hle]
    rw [Finset.sum_eq_single (indicatorFinsupp K, m - indicatorFinsupp K)]
    · simp
    · rintro ⟨x1, x2⟩ hx hne
      rw [Finset.mem_antidiagonal] at hx
      split_ifs with hx1
      · subst hx1
        have : x2 = m - indicatorFinsupp K := by
          have : indicatorFinsupp K + x2 = indicatorFinsupp K + (m - indicatorFinsupp K) := by
            rw [hx, add_tsub_cancel_of_le hle]
          exact add_left_cancel this
        subst this; contradiction
      · rfl
    · intro hnot; exact False.elim (hnot h_mem)
  · apply Finset.sum_eq_zero
    rintro ⟨x1, x2⟩ hx
    rw [Finset.mem_antidiagonal] at hx
    split_ifs with hx1
    · subst hx1
      have : indicatorFinsupp K ≤ m := fun i => by rw [← hx, Finsupp.add_apply]; exact Nat.le_add_right _ _
      exact False.elim (hle this)
    · rfl

theorem sum_antidiagonal_detMacMahon_mul_G (A : Matrix (Fin n) (Fin n) R) (m : Fin n →₀ ℕ) :
    (∑ x ∈ Finset.antidiagonal m, MvPolynomial.coeff x.1 (detMacMahon A) * G A x.2) =
    ∑ K ∈ (Finset.univ : Finset (Fin n)).powerset,
      if indicatorFinsupp K ≤ m then subdetCoeffScalar A K * G A (m - indicatorFinsupp K) else 0 := by
  simp_rw [detMacMahon_eq_sum_monomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_mul]
  simp_rw [eq_comm (a := indicatorFinsupp _), ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun K _ => sum_antidiagonal_ite_eq_indicator m K _ _)

noncomputable def macmahonRelMatrix' (A : Matrix (Fin n) (Fin n) R) (S : Finset (Fin n)) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) R) :=
  Matrix.of (fun i j => (if i = j then (if i ∈ S then linearForm A i else 1) else 0) -
    (if i ∈ S then MvPolynomial.X i * MvPolynomial.C (A i j) else 0))

theorem macmahonRelMatrix'_mulVec_X (A : Matrix (Fin n) (Fin n) R) (S : Finset (Fin n)) :
    macmahonRelMatrix' A S *ᵥ (fun j => MvPolynomial.X j) = fun i => if i ∈ S then 0 else MvPolynomial.X i := by
  apply funext
  intro i
  simp only [Matrix.mulVec_apply_eq_sum, macmahonRelMatrix', Matrix.of_apply, sub_mul]
  rw [Finset.sum_sub_distrib]
  by_cases hi : i ∈ S
  · simp only [hi, ite_true]
    have h1 : (∑ j : Fin n, (if i = j then linearForm A i else 0) * MvPolynomial.X j) = linearForm A i * MvPolynomial.X i := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        split_ifs with hij
        · subst hij; contradiction
        · simp
      · intro hnot; exact (hnot (Finset.mem_univ i)).elim
    have h2 : (∑ j : Fin n, MvPolynomial.X i * MvPolynomial.C (A i j) * MvPolynomial.X j) = linearForm A i * MvPolynomial.X i := by
      dsimp [linearForm]; rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [h1, h2, sub_self]
  · simp only [hi, ite_false]
    have h1 : (∑ j : Fin n, (if i = j then (1 : MvPolynomial (Fin n) R) else 0) * MvPolynomial.X j) = MvPolynomial.X i := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        split_ifs with hij
        · subst hij; contradiction
        · simp
      · intro hnot; exact (hnot (Finset.mem_univ i)).elim
    have h2 : (∑ j : Fin n, (0 : MvPolynomial (Fin n) R) * MvPolynomial.X j) = 0 := by simp
    rw [h1, h2, sub_zero]

theorem macmahonRelMatrix'_adjugate_mulVec (A : Matrix (Fin n) (Fin n) R) (S : Finset (Fin n)) (k : Fin n) :
    Matrix.det (macmahonRelMatrix' A S) * MvPolynomial.X k =
    ∑ i ∈ Finset.univ \ S, (Matrix.adjugate (macmahonRelMatrix' A S)) k i * MvPolynomial.X i := by
  have h : (Matrix.adjugate (macmahonRelMatrix' A S) * macmahonRelMatrix' A S) *ᵥ (fun j => MvPolynomial.X j) =
      Matrix.adjugate (macmahonRelMatrix' A S) *ᵥ (macmahonRelMatrix' A S *ᵥ (fun j => MvPolynomial.X j)) := by
    rw [Matrix.mulVec_mulVec]
  rw [Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec] at h
  have hk := congr_fun h k
  simp only [macmahonRelMatrix'_mulVec_X, Matrix.mulVec_apply_eq_sum, Pi.smul_apply, smul_eq_mul] at hk
  have h_sum : (∑ i : Fin n, (Matrix.adjugate (macmahonRelMatrix' A S)) k i * (if i ∈ S then 0 else MvPolynomial.X i)) =
      ∑ i ∈ Finset.univ \ S, (Matrix.adjugate (macmahonRelMatrix' A S)) k i * MvPolynomial.X i := by
    rw [← Finset.sum_sdiff (Finset.subset_univ S)]
    have hS_zero : (∑ i ∈ S, (Matrix.adjugate (macmahonRelMatrix' A S)) k i * (if i ∈ S then 0 else MvPolynomial.X i)) = 0 :=
      Finset.sum_eq_zero (fun x hx => by simp [hx])
    rw [hS_zero, add_zero]
    exact Finset.sum_congr rfl (fun x hx => by simp [(Finset.mem_sdiff.mp hx).2])
  rw [h_sum] at hk
  exact hk

theorem coeff_det_macmahonRelMatrix'_mul_eq_zero (A : Matrix (Fin n) (Fin n) R)
    (m : Fin n →₀ ℕ) (k : Fin n) (hk : k ∈ m.support) (P : MvPolynomial (Fin n) R) :
    MvPolynomial.coeff m (Matrix.det (macmahonRelMatrix' A m.support) * P) = 0 := by
  have h_adj := macmahonRelMatrix'_adjugate_mulVec A m.support k
  have h_mul : Matrix.det (macmahonRelMatrix' A m.support) * P * MvPolynomial.X k =
      ∑ i ∈ Finset.univ \ m.support, (Matrix.adjugate (macmahonRelMatrix' A m.support)) k i * P * MvPolynomial.X i := by
    calc Matrix.det (macmahonRelMatrix' A m.support) * P * MvPolynomial.X k
      _ = (Matrix.det (macmahonRelMatrix' A m.support) * MvPolynomial.X k) * P := by ring
      _ = (∑ i ∈ Finset.univ \ m.support, (Matrix.adjugate (macmahonRelMatrix' A m.support)) k i * MvPolynomial.X i) * P := by rw [h_adj]
      _ = ∑ i ∈ Finset.univ \ m.support, (Matrix.adjugate (macmahonRelMatrix' A m.support)) k i * P * MvPolynomial.X i := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun i _ => by ring)
  have h_coeff := congr_arg (MvPolynomial.coeff (m + Finsupp.single k 1)) h_mul
  rw [MvPolynomial.coeff_mul_X, MvPolynomial.coeff_sum] at h_coeff
  have h_zero : (∑ i ∈ Finset.univ \ m.support,
      MvPolynomial.coeff (m + Finsupp.single k 1)
        ((Matrix.adjugate (macmahonRelMatrix' A m.support)) k i * P * MvPolynomial.X i)) = 0 := by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    rw [Finset.mem_sdiff, Finsupp.mem_support_iff, not_not] at hi
    have h_not_supp : i ∉ (m + Finsupp.single k 1).support := by
      rw [Finsupp.mem_support_iff, not_not, Finsupp.add_apply]
      have hne : k ≠ i := fun h => (Finsupp.mem_support_iff.mp hk) (h ▸ hi.2)
      simp [hi.2, hne.symm]
    rw [MvPolynomial.coeff_mul_X']
    simp only [h_not_supp, ite_false]
  rw [h_zero] at h_coeff
  exact h_coeff

theorem prod_ite_linearForm_or_one (t : Finset (Fin n)) (S : Finset (Fin n)) (K : Finset (Fin n))
    (ht : t = Finset.univ \ K) (_hKS : K ⊆ S) :
    (∏ i ∈ t, (if i ∈ S then linearForm A i else (1 : MvPolynomial (Fin n) R))) =
    ∏ i ∈ S \ K, linearForm A i := by
  subst ht
  have h_sub : S \ K ⊆ Finset.univ \ K := fun x hx => by
    rw [Finset.mem_sdiff] at hx ⊢; simp [hx.2]
  rw [← Finset.prod_sdiff h_sub]
  have h1 : (∏ i ∈ (Finset.univ \ K) \ (S \ K), (if i ∈ S then linearForm A i else (1 : MvPolynomial (Fin n) R))) = 1 := by
    refine Finset.prod_eq_one (fun i hi => ?_)
    rw [Finset.mem_sdiff, Finset.mem_sdiff] at hi
    have : i ∉ S := fun hiS => hi.2 (Finset.mem_sdiff.mpr ⟨hiS, hi.1.2⟩)
    simp [this]
  have h3 : (∏ i ∈ S \ K, (if i ∈ S then linearForm A i else (1 : MvPolynomial (Fin n) R))) =
      ∏ i ∈ S \ K, linearForm A i :=
    Finset.prod_congr rfl (fun i hi => by simp [(Finset.mem_sdiff.mp hi).1])
  rw [h1, h3, one_mul]

theorem det_macmahonRelMatrix'_eq_sum_subdetCoeff (A : Matrix (Fin n) (Fin n) R) (S : Finset (Fin n)) :
    Matrix.det (macmahonRelMatrix' A S) = ∑ K ∈ (Finset.univ : Finset (Fin n)).powerset,
      if K ⊆ S then subdetCoeff A K * (∏ i ∈ K, MvPolynomial.X i) * (∏ i ∈ S \ K, linearForm A i) else 0 := by
  have h : macmahonRelMatrix' A S = genMatrix (fun i => if i ∈ S then linearForm A i else 1) S A := rfl
  rw [h, det_genMatrix]
  refine Finset.sum_congr rfl (fun K _ => ?_)
  split_ifs with hKS <;> [rw [prod_ite_linearForm_or_one _ _ _ rfl hKS, subdetCoeff_mul_prod_X, mul_comm (∏ i ∈ S \ K, _)]; rfl]

theorem prod_linearForms_eq_of_le' (A : Matrix (Fin n) (Fin n) R) (m : Fin n →₀ ℕ) (K : Finset (Fin n)) (hKS : K ⊆ m.support) :
    (∏ i ∈ m.support \ K, linearForm A i) * (∏ i : Fin n, (linearForm A i) ^ (m i - 1)) =
    prodLinearForms A (Finsupp.equivFunOnFinite (m - indicatorFinsupp K)) := by
  dsimp [prodLinearForms]
  have h_prod1 : (∏ i ∈ m.support \ K, linearForm A i) =
      ∏ i : Fin n, (linearForm A i) ^ (if i ∈ m.support \ K then 1 else 0) := by
    rw [← Finset.prod_subset (Finset.subset_univ (m.support \ K))]
    · refine Finset.prod_congr rfl (fun i hi => by simp [hi])
    · intro i _ hi; simp [hi]
  rw [h_prod1, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [← pow_add]
  congr 1
  dsimp [Finsupp.equivFunOnFinite]
  rw [indicatorFinsupp_apply]
  by_cases hiK : i ∈ K
  · have hiS := hKS hiK
    rw [Finsupp.mem_support_iff] at hiS
    have : i ∉ m.support \ K := fun h => (Finset.mem_sdiff.mp h).2 hiK
    simp [this, hiK]
  · by_cases hiS : i ∈ m.support
    · have : i ∈ m.support \ K := Finset.mem_sdiff.mpr ⟨hiS, hiK⟩
      rw [Finsupp.mem_support_iff] at hiS
      simp [this, hiK, Nat.add_sub_of_le (Nat.one_le_iff_ne_zero.mpr hiS)]
    · rw [Finsupp.mem_support_iff, not_not] at hiS
      have : i ∉ m.support \ K := fun h => Finsupp.mem_support_iff.mp (Finset.mem_sdiff.mp h).1 hiS
      simp [this, hiK, hiS]

theorem subset_support_of_indicator_le {K : Finset (Fin n)} {m : Fin n →₀ ℕ}
    (hle : indicatorFinsupp K ≤ m) : K ⊆ m.support := by
  intro i hi
  rw [Finsupp.mem_support_iff]
  intro h0
  have h_le := hle i
  rw [indicatorFinsupp_apply] at h_le
  simp only [hi, ite_true, h0] at h_le
  cases h_le

/--
**MacMahon's Master Theorem (1915)**:
For any $n \times n$ matrix $A \in M_{n \times n}(R)$ and any multi-index $s \in \mathbb{N}^n$,
the coefficient of $X^s = X_1^{s_1} \cdots X_n^{s_n}$ in the product of linear forms
$\prod_{i=1}^n (\sum_{j=1}^n A_{ij} X_j)^{s_i}$ equals the coefficient of $X^s$ in the
formal power series expansion of $\det(I_n - X A)^{-1}$:
$$[X^s] \prod_{i=1}^n \left(\sum_{j=1}^n A_{ij} X_j\right)^{s_i} = [X^s] \frac{1}{\det(I_n - X A)}$$
-/
theorem macmahon_master_theorem (A : Matrix (Fin n) (Fin n) R) (s : Fin n → ℕ) :
    MvPolynomial.coeff (toFinsupp s) (prodLinearForms A s) =
    MvPowerSeries.coeff (toFinsupp s) (invDetMacMahon A) := by
  have h_unique := invOfUnit_one_eq_of_antidiagonal_eq_zero
    (φ := MvPolynomial.toMvPowerSeries (detMacMahon A)) (g := G A)
    (hφ0 := by rw [toMvPowerSeries_coeff_eq_coeff, coeff_zero_detMacMahon]) (hg0 := G_zero A)
  by_cases hs : toFinsupp s = 0
  · have hs_zero : s = (fun _ => 0) := by
      have : Finsupp.equivFunOnFinite (toFinsupp s) = Finsupp.equivFunOnFinite 0 := by rw [hs]
      exact this
    subst hs_zero
    rw [macmahon_zero_exponent]
    have h_finsupp : toFinsupp (fun _ : Fin n => 0) = 0 := by ext i; simp [toFinsupp]
    rw [h_finsupp]
    dsimp [invDetMacMahon]
    rw [MvPowerSeries.constantCoeff_invOfUnit]; simp
  · have hrec : ∀ m : Fin n →₀ ℕ, m ≠ 0 → ∑ x ∈ Finset.antidiagonal m, MvPowerSeries.coeff x.1 (MvPolynomial.toMvPowerSeries (detMacMahon A)) * G A x.2 = 0 := by
      intro m hm
      simp_rw [toMvPowerSeries_coeff_eq_coeff]
      obtain ⟨k, hk⟩ := Finsupp.support_nonempty_iff.mpr hm
      have h_mul_zero := coeff_det_macmahonRelMatrix'_mul_eq_zero A m k hk (∏ i : Fin n, (linearForm A i) ^ (m i - 1))
      rw [det_macmahonRelMatrix'_eq_sum_subdetCoeff, Finset.sum_mul, MvPolynomial.coeff_sum] at h_mul_zero
      have h_sum_eq : ∑ K ∈ (Finset.univ : Finset (Fin n)).powerset,
          MvPolynomial.coeff m
            ((if K ⊆ m.support then subdetCoeff A K * (∏ i ∈ K, MvPolynomial.X i) * (∏ i ∈ m.support \ K, linearForm A i) else 0) *
              ∏ i : Fin n, (linearForm A i) ^ (m i - 1)) =
          ∑ x ∈ Finset.antidiagonal m, MvPolynomial.coeff x.1 (detMacMahon A) * G A x.2 := by
        rw [sum_antidiagonal_detMacMahon_mul_G A m]
        refine Finset.sum_congr rfl (fun K _ => ?_)
        by_cases hKS : K ⊆ m.support
        · simp only [hKS, ite_true]
          have h_rw : subdetCoeff A K * (∏ i ∈ K, MvPolynomial.X i) * (∏ i ∈ m.support \ K, linearForm A i) * ∏ i : Fin n, (linearForm A i) ^ (m i - 1) =
              (MvPolynomial.monomial (indicatorFinsupp K) (subdetCoeffScalar A K)) *
              ((∏ i ∈ m.support \ K, linearForm A i) * ∏ i : Fin n, (linearForm A i) ^ (m i - 1)) := by
            rw [mul_assoc (subdetCoeff A K * ∏ i ∈ K, MvPolynomial.X i), subdetCoeff_mul_prod_X]
          rw [h_rw, MvPolynomial.coeff_monomial_mul']
          split_ifs with hle <;> [congr 1; rfl]
          dsimp [G]; rw [prod_linearForms_eq_of_le' A m K hKS]
        · simp only [hKS, ite_false, zero_mul, MvPolynomial.coeff_zero]
          have hle : ¬ indicatorFinsupp K ≤ m := fun h => hKS (subset_support_of_indicator_le h)
          simp only [hle, ite_false]
      rw [h_sum_eq] at h_mul_zero
      exact h_mul_zero
    have hs_res := h_unique hrec (toFinsupp s)
    have hG : G A (toFinsupp s) = MvPolynomial.coeff (toFinsupp s) (prodLinearForms A s) := by
      dsimp [G, toFinsupp]; simp
    rwa [← hG]

/-- Specialization to $n = 1$: The 1D Master Theorem is the geometric series expansion. -/
theorem macmahon_dim1 (A : Matrix (Fin 1) (Fin 1) R) (s : Fin 1 → ℕ) :
    MvPolynomial.coeff (toFinsupp s) (prodLinearForms A s) =
    MvPowerSeries.coeff (toFinsupp s) (invDetMacMahon A) :=
  macmahon_master_theorem A s

end MacMahon
