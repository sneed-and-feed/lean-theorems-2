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
a profound identity in enumerative combinatorics relating the coefficients of products
of linear forms to the reciprocal determinant of a matrix.

## Mathematical Formulation

Let $R$ be a commutative ring, and let $A \in M_{n \times n}(R)$ be an $n \times n$ matrix
with entries $(a_{ij})_{i, j = 1}^n$.

Consider $n$ formal indeterminates $x = (x_1, \dots, x_n)$ and the $n$ associated linear forms:
$$Y_i = \sum_{j=1}^n a_{ij} x_j \quad (i = 1, \dots, n)$$

For any tuple of non-negative integers (multi-index) $s = (s_1, \dots, s_n) \in \mathbb{N}^n$,
we define the product of powers:
$$G(x) = \prod_{i=1}^n Y_i^{s_i} = \prod_{i=1}^n \left( \sum_{j=1}^n a_{ij} x_j \right)^{s_i}$$

Let $X = \operatorname{diag}(x_1, \dots, x_n)$ be the diagonal matrix of indeterminates.
The **reciprocal determinant** is:
$$F(x) = \frac{1}{\det(I_n - X A)} = \det(I_n - X A)^{-1}$$
where $(X A)_{ij} = x_i a_{ij}$.

### The Master Theorem
MacMahon's Master Theorem states that for every multi-index $s = (s_1, \dots, s_n) \in \mathbb{N}^n$,
the coefficient of the monomial $x^s = x_1^{s_1} \cdots x_n^{s_n}$ in $G(x)$ equals the
coefficient of $x^s$ in the formal power series expansion of $F(x)$:
$$[x_1^{s_1} \cdots x_n^{s_n}] \prod_{i=1}^n \left( \sum_{j=1}^n a_{ij} x_j \right)^{s_i} =
  [x_1^{s_1} \cdots x_n^{s_n}] \frac{1}{\det(I_n - X A)}$$

## Applications & Classical Corollaries
1. **Multinomial & Binomial Theorems ($n = 1$)**: Reduces directly to the geometric series
   $(1 - a x)^{-1} = \sum_{k \ge 0} a^k x^k$.
2. **Dixon's Identity**: Summation identities for products of three binomial coefficients.
3. **Derangements**: Enumeration of permutations with no fixed points ($A = J - I$).
4. **Good's Extension**: Multivariable Lagrange inversion and Laurent series generalizations.

## Formalization Structure

- `MultiIndex`: Representation of tuples $s \in \mathbb{N}^n$ via `Fin n → ℕ` and `Fin n →₀ ℕ`.
- `linearForm`: The polynomial $Y_i = \sum_j A_{ij} X_j \in R[X_1, \dots, X_n]$.
- `prodLinearForms`: The polynomial product $\prod_{i} Y_i^{s_i}$.
- `macmahonMatrix`: The matrix $I_n - X A$ over the polynomial ring $R[X_1, \dots, X_n]$.
- `detMacMahon`: The polynomial determinant $\det(I_n - X A)$.
- `invDetMacMahon`: The formal power series expansion $\det(I_n - X A)^{-1}$.
- `macmahon_master_theorem`: The main equality of coefficients $[X^s] \prod Y_i^{s_i} = [X^s] \det(I - X A)^{-1}$.
- `macmahon_dim1`: Specialization to dimension $n = 1$.

## References
- MacMahon, P. A. (1915). *Combinatory Analysis* (Vol. 1 & 2). Cambridge University Press.
- Cartier, P. (1972). *On the Cartier–Foata proof of MacMahon's Master Theorem*.
- Foata, D. (1965). *Étude algébrique de certains problèmes d'analyse combinatoire et du calcul des probabilités*. Publ. Inst. Statist. Univ. Paris.
- Stanley, R. P. (2012). *Enumerative Combinatorics*, Vol. 1, Section 4.7.
-/

variable {R : Type*} [CommRing R]
variable {n : ℕ}

namespace MacMahon

/-- Convert a function $s : \text{Fin } n \to \mathbb{N}$ to a finitely supported multi-index. -/
noncomputable def toFinsupp (s : Fin n → ℕ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm s

/-- The $i$-th linear form $Y_i = \sum_{j=1}^n A_{ij} X_j$ in $R[X_1, \dots, X_n]$. -/
noncomputable def linearForm (A : Matrix (Fin n) (Fin n) R) (i : Fin n) :
    MvPolynomial (Fin n) R :=
  ∑ j : Fin n, MvPolynomial.C (A i j) * MvPolynomial.X j

/-- The product of powers of linear forms $\prod_{i=1}^n Y_i^{s_i}$. -/
noncomputable def prodLinearForms (A : Matrix (Fin n) (Fin n) R) (s : Fin n → ℕ) :
    MvPolynomial (Fin n) R :=
  ∏ i : Fin n, (linearForm A i) ^ (s i)

/-- The matrix $I_n - X A$ whose $(i, j)$ entry is $\delta_{ij} - X_i A_{ij}$. -/
noncomputable def macmahonMatrix (A : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) R) :=
  Matrix.of (fun i j => (if i = j then (1 : MvPolynomial (Fin n) R) else 0) -
    MvPolynomial.X i * MvPolynomial.C (A i j))

/-- The polynomial determinant $\det(I_n - X A)$. -/
noncomputable def detMacMahon (A : Matrix (Fin n) (Fin n) R) :
    MvPolynomial (Fin n) R :=
  Matrix.det (macmahonMatrix A)

/-- The reciprocal determinant $\det(I_n - X A)^{-1}$ as a formal power series. -/
noncomputable def invDetMacMahon (A : Matrix (Fin n) (Fin n) R) :
    MvPowerSeries (Fin n) R :=
  MvPowerSeries.invOfUnit (MvPolynomial.toMvPowerSeries (detMacMahon A)) 1

/-- Zero exponent identity: For $s = (0, \dots, 0)$, both sides equal $1$. -/
theorem macmahon_zero_exponent (A : Matrix (Fin n) (Fin n) R) :
    MvPolynomial.coeff (toFinsupp (fun _ => 0)) (prodLinearForms A (fun _ => 0)) = 1 := by
  have h_prod : prodLinearForms A (fun _ => 0) = 1 := by
    dsimp [prodLinearForms]
    simp
  have h_finsupp : toFinsupp (fun _ : Fin n => 0) = 0 := by
    ext i
    simp [toFinsupp]
  rw [h_prod, h_finsupp, ← MvPolynomial.C_1, MvPolynomial.coeff_zero_C]

theorem coeff_zero_detMacMahon (A : Matrix (Fin n) (Fin n) R) :
    MvPolynomial.coeff 0 (detMacMahon A) = 1 := by
  rw [← MvPolynomial.constantCoeff_eq]
  rw [detMacMahon, RingHom.map_det]
  have h_mat : (MvPolynomial.constantCoeff.mapMatrix (macmahonMatrix A)) = 1 := by
    ext i j
    simp only [RingHom.mapMatrix_apply, macmahonMatrix, Matrix.map_apply, Matrix.of_apply, map_sub, map_mul,
      MvPolynomial.constantCoeff_X, zero_mul, sub_zero, Matrix.one_apply]
    split_ifs <;> simp
  rw [h_mat, Matrix.det_one]

theorem invOfUnit_one_eq_of_antidiagonal_eq_zero {σ : Type*} [DecidableEq σ]
    (φ : MvPowerSeries σ R) (g : (σ →₀ ℕ) → R)
    (hφ0 : MvPowerSeries.coeff 0 φ = 1)
    (hg0 : g 0 = 1)
    (hrec : ∀ m : σ →₀ ℕ, m ≠ 0 → ∑ x ∈ Finset.antidiagonal m, MvPowerSeries.coeff x.1 φ * g x.2 = 0) :
    ∀ m : σ →₀ ℕ, g m = MvPowerSeries.coeff m (MvPowerSeries.invOfUnit φ 1) := by
  intro m
  induction m using WellFoundedLT.induction with
  | ind m ih =>
    by_cases hm : m = 0
    · subst hm
      rw [hg0, MvPowerSeries.coeff_invOfUnit]
      simp
    · rw [MvPowerSeries.coeff_invOfUnit]
      simp only [Units.val_one, inv_one, one_mul, neg_mul]
      rw [if_neg hm]
      have h0m : ((0 : σ →₀ ℕ), m) ∈ Finset.antidiagonal m := by rw [Finset.mem_antidiagonal, zero_add]
      have h_sum : ∑ x ∈ Finset.antidiagonal m, MvPowerSeries.coeff x.1 φ * g x.2 =
          g m + ∑ x ∈ Finset.antidiagonal m, if x.2 < m then MvPowerSeries.coeff x.1 φ * g x.2 else 0 := by
        rw [← Finset.insert_erase h0m, Finset.sum_insert (Finset.notMem_erase _ _)]
        simp only [hφ0, one_mul]
        congr 1
        rw [← Finset.insert_erase h0m, Finset.sum_insert (Finset.notMem_erase _ _)]
        rw [if_neg (not_lt_of_ge le_rfl), zero_add]
        rw [Finset.erase_insert (Finset.notMem_erase _ _)]
        apply Finset.sum_congr rfl
        rintro ⟨i, j⟩ hij
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
        rw [if_pos hjlt]
      have hrec_m := hrec m hm
      rw [h_sum] at hrec_m
      have hgm : g m = - ∑ x ∈ Finset.antidiagonal m, if x.2 < m then MvPowerSeries.coeff x.1 φ * g x.2 else 0 :=
        eq_neg_of_add_eq_zero_left hrec_m
      rw [hgm]
      simp only [neg_inj]
      apply Finset.sum_congr rfl
      rintro ⟨i, j⟩ _
      split_ifs with hj
      · rw [ih j hj]
      · rfl

noncomputable def macmahonRelMatrix (A : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) R) :=
  Matrix.of (fun i j => (if i = j then linearForm A i else 0) -
    MvPolynomial.X i * MvPolynomial.C (A i j))

theorem det_mul_eq_zero_of_mulVec_eq_zero
    (M : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) R)) (v : Fin n → MvPolynomial (Fin n) R)
    (hMv : M *ᵥ v = 0) (j : Fin n) :
    Matrix.det M * v j = 0 := by
  have h : (Matrix.adjugate M * M) *ᵥ v = 0 := by
    rw [← Matrix.mulVec_mulVec, hMv, Matrix.mulVec_zero]
  rw [Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec] at h
  exact congr_fun h j

theorem eq_zero_of_mul_X_eq_zero (P : MvPolynomial (Fin n) R) (j : Fin n) (h : P * MvPolynomial.X j = 0) :
    P = 0 := by
  ext d
  have h_coeff := congr_arg (MvPolynomial.coeff (d + Finsupp.single j 1)) h
  rw [MvPolynomial.coeff_mul_X, MvPolynomial.coeff_zero] at h_coeff
  exact h_coeff

theorem macmahonRelMatrix_mulVec_X (A : Matrix (Fin n) (Fin n) R) :
    macmahonRelMatrix A *ᵥ (fun j => MvPolynomial.X j) = 0 := by
  ext i
  simp only [Matrix.mulVec_apply_eq_sum, macmahonRelMatrix, Matrix.of_apply, Pi.zero_apply, sub_mul]
  rw [Finset.sum_sub_distrib]
  have h1 : (∑ j : Fin n, (if i = j then linearForm A i else 0) * MvPolynomial.X j) =
      linearForm A i * MvPolynomial.X i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      split_ifs with hij
      · subst hij; contradiction
      · simp
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  have h2 : (∑ j : Fin n, MvPolynomial.X i * MvPolynomial.C (A i j) * MvPolynomial.X j) =
      linearForm A i * MvPolynomial.X i := by
    dsimp [linearForm]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h1, h2, sub_self]

theorem det_macmahonRelMatrix_eq_zero [NeZero n] (A : Matrix (Fin n) (Fin n) R) :
    Matrix.det (macmahonRelMatrix A) = 0 := by
  have h := det_mul_eq_zero_of_mulVec_eq_zero (macmahonRelMatrix A) (fun j => MvPolynomial.X j)
    (macmahonRelMatrix_mulVec_X A) 0
  exact eq_zero_of_mul_X_eq_zero (Matrix.det (macmahonRelMatrix A)) 0 h

noncomputable def subdetCoeff (A : Matrix (Fin n) (Fin n) R) (K : Finset (Fin n)) :
    MvPolynomial (Fin n) R :=
  ∑ σ : Equiv.Perm (Fin n),
    (if ∀ i ∉ K, σ i = i then 1 else 0) *
    (Equiv.Perm.sign σ • ((-1 : MvPolynomial (Fin n) R) ^ K.card * MvPolynomial.C (∏ i ∈ K, A i (σ i))))

theorem prod_ite_eq_self (t : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) (f : Fin n → MvPolynomial (Fin n) R) :
    (∏ i ∈ t, (if i = σ i then f i else 0)) =
    if ∀ i ∈ t, σ i = i then ∏ i ∈ t, f i else 0 := by
  split_ifs with h
  · apply Finset.prod_congr rfl
    intro i hi
    simp [h i hi]
  · push Not at h
    obtain ⟨i, hi, hne⟩ := h
    have : (if i = σ i then f i else (0 : MvPolynomial (Fin n) R)) = 0 := by
      split_ifs with h'
      · exact False.elim (hne h'.symm)
      · rfl
    exact Finset.prod_eq_zero hi this

theorem prod_neg_X_mul_C (K : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) (A : Matrix (Fin n) (Fin n) R) :
    (∏ i ∈ K, (- (MvPolynomial.X i * MvPolynomial.C (A i (σ i))))) =
    (-1 : MvPolynomial (Fin n) R) ^ K.card * (∏ i ∈ K, MvPolynomial.X i) * MvPolynomial.C (∏ i ∈ K, A i (σ i)) := by
  have : (∏ i ∈ K, (- (MvPolynomial.X i * MvPolynomial.C (A i (σ i))))) =
      ∏ i ∈ K, ((-1 : MvPolynomial (Fin n) R) * MvPolynomial.X i * MvPolynomial.C (A i (σ i))) := by
    apply Finset.prod_congr rfl
    intro i _
    ring
  rw [this]
  simp_rw [Finset.prod_mul_distrib]
  rw [Finset.prod_const]
  simp only [map_prod]

def complEquiv : Finset (Fin n) ≃ Finset (Fin n) where
  toFun := compl
  invFun := compl
  left_inv := compl_compl
  right_inv := compl_compl

theorem sum_powerset_compl (f : Finset (Fin n) → MvPolynomial (Fin n) R) :
    (∑ t ∈ (Finset.univ : Finset (Fin n)).powerset, f (Finset.univ \ t)) =
    ∑ K ∈ (Finset.univ : Finset (Fin n)).powerset, f K := by
  rw [Finset.powerset_univ]
  exact Fintype.sum_equiv (complEquiv (n := n)) (fun t => f (Finset.univ \ t)) f (fun t => rfl)

theorem forall_not_mem_compl_iff (t : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) :
    (∀ i ∉ Finset.univ \ t, σ i = i) ↔ (∀ i ∈ t, σ i = i) := by
  simp [Finset.mem_sdiff]

theorem compl_compl_eq (t : Finset (Fin n)) : Finset.univ \ (Finset.univ \ t) = t := by
  ext x
  simp

theorem detMacMahon_eq_sum_subdetCoeff (A : Matrix (Fin n) (Fin n) R) :
    detMacMahon A = ∑ K ∈ (Finset.univ : Finset (Fin n)).powerset,
      subdetCoeff A K * ∏ i ∈ K, MvPolynomial.X i := by
  rw [detMacMahon, ← Matrix.det_transpose, Matrix.det_apply]
  have h_prod (σ : Equiv.Perm (Fin n)) :
      (∏ i : Fin n, (macmahonMatrix A)ᵀ (σ i) i) =
      ∑ t ∈ (Finset.univ : Finset (Fin n)).powerset,
        (if ∀ i ∈ t, σ i = i then (1 : MvPolynomial (Fin n) R) else 0) *
        ((-1 : MvPolynomial (Fin n) R) ^ (Finset.univ \ t).card * (∏ i ∈ Finset.univ \ t, MvPolynomial.X i) *
          MvPolynomial.C (∏ i ∈ Finset.univ \ t, A i (σ i))) := by
    have h_entry : (fun i => (macmahonMatrix A)ᵀ (σ i) i) =
        (fun i => (if i = σ i then (1 : MvPolynomial (Fin n) R) else 0) + (- (MvPolynomial.X i * MvPolynomial.C (A i (σ i))))) := by
      ext i
      simp only [macmahonMatrix, Matrix.transpose_apply, Matrix.of_apply, sub_eq_add_neg]
    rw [h_entry, Finset.prod_add]
    apply Finset.sum_congr rfl
    intro t _
    rw [prod_ite_eq_self t σ (fun _ => 1), prod_neg_X_mul_C (Finset.univ \ t) σ A]
    simp only [Finset.prod_const_one]
  simp_rw [h_prod, Finset.smul_sum]
  have h_comp (σ : Equiv.Perm (Fin n)) :
      (∑ t ∈ (Finset.univ : Finset (Fin n)).powerset,
        Equiv.Perm.sign σ •
          ((if ∀ i ∈ t, σ i = i then 1 else 0) *
            ((-1 : MvPolynomial (Fin n) R) ^ (Finset.univ \ t).card * (∏ i ∈ Finset.univ \ t, MvPolynomial.X i) *
              MvPolynomial.C (∏ i ∈ Finset.univ \ t, A i (σ i))))) =
      ∑ K ∈ (Finset.univ : Finset (Fin n)).powerset,
        Equiv.Perm.sign σ •
          ((if ∀ i ∉ K, σ i = i then 1 else 0) *
            ((-1 : MvPolynomial (Fin n) R) ^ K.card * (∏ i ∈ K, MvPolynomial.X i) *
              MvPolynomial.C (∏ i ∈ K, A i (σ i)))) := by
    have h_rw : (∑ t ∈ (Finset.univ : Finset (Fin n)).powerset,
        Equiv.Perm.sign σ •
          ((if ∀ i ∈ t, σ i = i then 1 else 0) *
            ((-1 : MvPolynomial (Fin n) R) ^ (Finset.univ \ t).card * (∏ i ∈ Finset.univ \ t, MvPolynomial.X i) *
              MvPolynomial.C (∏ i ∈ Finset.univ \ t, A i (σ i))))) =
        ∑ t ∈ (Finset.univ : Finset (Fin n)).powerset,
        Equiv.Perm.sign σ •
          ((if ∀ i ∉ Finset.univ \ t, σ i = i then 1 else 0) *
            ((-1 : MvPolynomial (Fin n) R) ^ (Finset.univ \ t).card * (∏ i ∈ Finset.univ \ t, MvPolynomial.X i) *
              MvPolynomial.C (∏ i ∈ Finset.univ \ t, A i (σ i)))) := by
      apply Finset.sum_congr rfl
      intro t _
      simp_rw [forall_not_mem_compl_iff]
    rw [h_rw]
    apply sum_powerset_compl (fun K =>
      Equiv.Perm.sign σ •
        ((if ∀ i ∉ K, σ i = i then (1 : MvPolynomial (Fin n) R) else 0) *
          ((-1 : MvPolynomial (Fin n) R) ^ K.card * (∏ i ∈ K, MvPolynomial.X i) *
            MvPolynomial.C (∏ i ∈ K, A i (σ i)))))
  simp_rw [h_comp]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro K _
  dsimp [subdetCoeff]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Units.smul_def]
  ring

theorem det_macmahonRelMatrix_eq_sum_subdetCoeff (A : Matrix (Fin n) (Fin n) R) :
    Matrix.det (macmahonRelMatrix A) = ∑ K ∈ (Finset.univ : Finset (Fin n)).powerset,
      subdetCoeff A K * (∏ i ∈ K, MvPolynomial.X i) * (∏ i ∈ Finset.univ \ K, linearForm A i) := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  have h_prod (σ : Equiv.Perm (Fin n)) :
      (∏ i : Fin n, (macmahonRelMatrix A)ᵀ (σ i) i) =
      ∑ t ∈ (Finset.univ : Finset (Fin n)).powerset,
        (if ∀ i ∈ t, σ i = i then ∏ i ∈ t, linearForm A i else 0) *
        ((-1 : MvPolynomial (Fin n) R) ^ (Finset.univ \ t).card * (∏ i ∈ Finset.univ \ t, MvPolynomial.X i) *
          MvPolynomial.C (∏ i ∈ Finset.univ \ t, A i (σ i))) := by
    have h_entry : (fun i => (macmahonRelMatrix A)ᵀ (σ i) i) =
        (fun i => (if i = σ i then linearForm A i else 0) + (- (MvPolynomial.X i * MvPolynomial.C (A i (σ i))))) := by
      ext i
      simp only [macmahonRelMatrix, Matrix.transpose_apply, Matrix.of_apply, sub_eq_add_neg]
    rw [h_entry, Finset.prod_add]
    apply Finset.sum_congr rfl
    intro t _
    rw [prod_ite_eq_self t σ (linearForm A), prod_neg_X_mul_C (Finset.univ \ t) σ A]
  simp_rw [h_prod, Finset.smul_sum]
  have h_comp (σ : Equiv.Perm (Fin n)) :
      (∑ t ∈ (Finset.univ : Finset (Fin n)).powerset,
        Equiv.Perm.sign σ •
          ((if ∀ i ∈ t, σ i = i then ∏ i ∈ t, linearForm A i else 0) *
            ((-1 : MvPolynomial (Fin n) R) ^ (Finset.univ \ t).card * (∏ i ∈ Finset.univ \ t, MvPolynomial.X i) *
              MvPolynomial.C (∏ i ∈ Finset.univ \ t, A i (σ i))))) =
      ∑ K ∈ (Finset.univ : Finset (Fin n)).powerset,
        Equiv.Perm.sign σ •
          ((if ∀ i ∉ K, σ i = i then ∏ i ∈ Finset.univ \ K, linearForm A i else 0) *
            ((-1 : MvPolynomial (Fin n) R) ^ K.card * (∏ i ∈ K, MvPolynomial.X i) *
              MvPolynomial.C (∏ i ∈ K, A i (σ i)))) := by
    have h_rw : (∑ t ∈ (Finset.univ : Finset (Fin n)).powerset,
        Equiv.Perm.sign σ •
          ((if ∀ i ∈ t, σ i = i then ∏ i ∈ t, linearForm A i else 0) *
            ((-1 : MvPolynomial (Fin n) R) ^ (Finset.univ \ t).card * (∏ i ∈ Finset.univ \ t, MvPolynomial.X i) *
              MvPolynomial.C (∏ i ∈ Finset.univ \ t, A i (σ i))))) =
        ∑ t ∈ (Finset.univ : Finset (Fin n)).powerset,
        Equiv.Perm.sign σ •
          ((if ∀ i ∉ Finset.univ \ t, σ i = i then ∏ i ∈ Finset.univ \ (Finset.univ \ t), linearForm A i else 0) *
            ((-1 : MvPolynomial (Fin n) R) ^ (Finset.univ \ t).card * (∏ i ∈ Finset.univ \ t, MvPolynomial.X i) *
              MvPolynomial.C (∏ i ∈ Finset.univ \ t, A i (σ i)))) := by
      apply Finset.sum_congr rfl
      intro t _
      simp_rw [forall_not_mem_compl_iff, compl_compl_eq]
    rw [h_rw]
    apply sum_powerset_compl (fun K =>
      Equiv.Perm.sign σ •
        ((if ∀ i ∉ K, σ i = i then ∏ i ∈ Finset.univ \ K, linearForm A i else 0) *
          ((-1 : MvPolynomial (Fin n) R) ^ K.card * (∏ i ∈ K, MvPolynomial.X i) *
            MvPolynomial.C (∏ i ∈ K, A i (σ i)))))
  simp_rw [h_comp]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro K _
  dsimp [subdetCoeff]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Units.smul_def]
  split_ifs <;> ring

noncomputable def G (A : Matrix (Fin n) (Fin n) R) (m : Fin n →₀ ℕ) : R :=
  MvPolynomial.coeff m (prodLinearForms A (Finsupp.equivFunOnFinite m))

theorem G_zero (A : Matrix (Fin n) (Fin n) R) : G A 0 = 1 := by
  dsimp [G]
  have h0 : Finsupp.equivFunOnFinite (0 : Fin n →₀ ℕ) = (fun _ => 0) := by
    ext i
    rfl
  rw [h0]
  have h_exp := macmahon_zero_exponent A
  have h_finsupp : toFinsupp (fun _ : Fin n => 0) = 0 := by
    ext i
    simp [toFinsupp]
  rwa [h_finsupp] at h_exp

theorem toMvPowerSeries_coeff_eq_coeff (P : MvPolynomial (Fin n) R) (d : Fin n →₀ ℕ) :
    MvPowerSeries.coeff d (MvPolynomial.toMvPowerSeries P) = MvPolynomial.coeff d P := rfl

theorem neZero_of_finsupp_ne_zero (m : Fin n →₀ ℕ) (hm : m ≠ 0) : NeZero n := by
  by_cases hn : n = 0
  · subst hn
    have : m = 0 := Subsingleton.elim m 0
    exact False.elim (hm this)
  · exact ⟨hn⟩

noncomputable def subdetCoeffScalar (A : Matrix (Fin n) (Fin n) R) (K : Finset (Fin n)) : R :=
  ∑ σ : Equiv.Perm (Fin n),
    (if ∀ i ∉ K, σ i = i then 1 else 0) *
    (Equiv.Perm.sign σ • ((-1 : R) ^ K.card * (∏ i ∈ K, A i (σ i))))

noncomputable def indicatorFinsupp (K : Finset (Fin n)) : Fin n →₀ ℕ :=
  ∑ i ∈ K, Finsupp.single i 1

theorem indicatorFinsupp_apply_mem {K : Finset (Fin n)} {i : Fin n} (hi : i ∈ K) :
    indicatorFinsupp K i = 1 := by
  dsimp [indicatorFinsupp]
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single i]
  · simp
  · intro j hj hne; simp [hne.symm]
  · intro hi'; exact False.elim (hi' hi)

theorem indicatorFinsupp_apply_not_mem {K : Finset (Fin n)} {i : Fin n} (hi : i ∉ K) :
    indicatorFinsupp K i = 0 := by
  dsimp [indicatorFinsupp]
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  have : j ≠ i := by rintro rfl; exact hi hj
  simp [this]

theorem subdetCoeff_eq_C (A : Matrix (Fin n) (Fin n) R) (K : Finset (Fin n)) :
    subdetCoeff A K = MvPolynomial.C (subdetCoeffScalar A K) := by
  dsimp [subdetCoeff, subdetCoeffScalar]
  simp only [map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Units.smul_def]
  split_ifs <;> simp

theorem prod_X_eq_monomial (K : Finset (Fin n)) :
    (∏ i ∈ K, (MvPolynomial.X i : MvPolynomial (Fin n) R)) = MvPolynomial.monomial (indicatorFinsupp K) 1 := by
  induction K using Finset.induction_on with
  | empty => simp [indicatorFinsupp]
  | @insert i s hi ih =>
    dsimp [indicatorFinsupp] at ih ⊢
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, MvPolynomial.X, MvPolynomial.monomial_mul_monomial]
    simp

theorem subdetCoeff_mul_prod_X (A : Matrix (Fin n) (Fin n) R) (K : Finset (Fin n)) :
    subdetCoeff A K * ∏ i ∈ K, (MvPolynomial.X i : MvPolynomial (Fin n) R) =
    MvPolynomial.monomial (indicatorFinsupp K) (subdetCoeffScalar A K) := by
  rw [subdetCoeff_eq_C, prod_X_eq_monomial, MvPolynomial.C_mul_monomial, mul_one]

theorem detMacMahon_eq_sum_monomial (A : Matrix (Fin n) (Fin n) R) :
    detMacMahon A = ∑ K ∈ (Finset.univ : Finset (Fin n)).powerset, MvPolynomial.monomial (indicatorFinsupp K) (subdetCoeffScalar A K) := by
  rw [detMacMahon_eq_sum_subdetCoeff]
  apply Finset.sum_congr rfl
  intro K _
  exact subdetCoeff_mul_prod_X A K

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
        have hx2 : x2 = m - indicatorFinsupp K := by
          have : indicatorFinsupp K + x2 = indicatorFinsupp K + (m - indicatorFinsupp K) := by
            rw [hx, add_tsub_cancel_of_le hle]
          exact add_left_cancel this
        subst hx2
        contradiction
      · rfl
    · intro hnot
      exact False.elim (hnot h_mem)
  · apply Finset.sum_eq_zero
    rintro ⟨x1, x2⟩ hx
    rw [Finset.mem_antidiagonal] at hx
    split_ifs with hx1
    · subst hx1
      have : indicatorFinsupp K ≤ m := by
        intro i
        rw [← hx, Finsupp.add_apply]
        exact Nat.le_add_right _ _
      exact False.elim (hle this)
    · rfl

theorem sum_antidiagonal_detMacMahon_mul_G (A : Matrix (Fin n) (Fin n) R) (m : Fin n →₀ ℕ) :
    (∑ x ∈ Finset.antidiagonal m, MvPolynomial.coeff x.1 (detMacMahon A) * G A x.2) =
    ∑ K ∈ (Finset.univ : Finset (Fin n)).powerset,
      if indicatorFinsupp K ≤ m then subdetCoeffScalar A K * G A (m - indicatorFinsupp K) else 0 := by
  have h_det := detMacMahon_eq_sum_monomial A
  simp_rw [h_det, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_mul]
  simp_rw [eq_comm (a := indicatorFinsupp _), ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro K _
  exact sum_antidiagonal_ite_eq_indicator m K (subdetCoeffScalar A K) (G A)

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
    have h1 : (∑ j : Fin n, (if i = j then linearForm A i else 0) * MvPolynomial.X j) =
        linearForm A i * MvPolynomial.X i := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        split_ifs with hij
        · subst hij; contradiction
        · simp
      · intro hi'
        exact False.elim (hi' (Finset.mem_univ i))
    have h2 : (∑ j : Fin n, MvPolynomial.X i * MvPolynomial.C (A i j) * MvPolynomial.X j) =
        linearForm A i * MvPolynomial.X i := by
      dsimp [linearForm]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [h1, h2, sub_self]
  · simp only [hi, ite_false]
    have h1 : (∑ j : Fin n, (if i = j then (1 : MvPolynomial (Fin n) R) else 0) * MvPolynomial.X j) =
        MvPolynomial.X i := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        split_ifs with hij
        · subst hij; contradiction
        · simp
      · intro hi'
        exact False.elim (hi' (Finset.mem_univ i))
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
    have hS_zero : (∑ i ∈ S, (Matrix.adjugate (macmahonRelMatrix' A S)) k i * (if i ∈ S then 0 else MvPolynomial.X i)) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      simp [hx]
    rw [hS_zero, add_zero]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_sdiff] at hx
    simp [hx.2]
  rw [h_sum] at hk
  exact hk

theorem coeff_det_macmahonRelMatrix'_mul_eq_zero (A : Matrix (Fin n) (Fin n) R)
    (m : Fin n →₀ ℕ) (k : Fin n) (hk : k ∈ m.support)
    (P : MvPolynomial (Fin n) R) :
    MvPolynomial.coeff m (Matrix.det (macmahonRelMatrix' A m.support) * P) = 0 := by
  have h_adj := macmahonRelMatrix'_adjugate_mulVec A m.support k
  have h_mul : Matrix.det (macmahonRelMatrix' A m.support) * P * MvPolynomial.X k =
      ∑ i ∈ Finset.univ \ m.support, (Matrix.adjugate (macmahonRelMatrix' A m.support)) k i * P * MvPolynomial.X i := by
    calc Matrix.det (macmahonRelMatrix' A m.support) * P * MvPolynomial.X k
      _ = (Matrix.det (macmahonRelMatrix' A m.support) * MvPolynomial.X k) * P := by ring
      _ = (∑ i ∈ Finset.univ \ m.support, (Matrix.adjugate (macmahonRelMatrix' A m.support)) k i * MvPolynomial.X i) * P := by rw [h_adj]
      _ = ∑ i ∈ Finset.univ \ m.support, (Matrix.adjugate (macmahonRelMatrix' A m.support)) k i * P * MvPolynomial.X i := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have h_coeff := congr_arg (MvPolynomial.coeff (m + Finsupp.single k 1)) h_mul
  rw [MvPolynomial.coeff_mul_X, MvPolynomial.coeff_sum] at h_coeff
  have h_zero : (∑ i ∈ Finset.univ \ m.support,
      MvPolynomial.coeff (m + Finsupp.single k 1)
        ((Matrix.adjugate (macmahonRelMatrix' A m.support)) k i * P * MvPolynomial.X i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_sdiff, Finsupp.mem_support_iff, not_not] at hi
    have h_not_supp : i ∉ (m + Finsupp.single k 1).support := by
      rw [Finsupp.mem_support_iff, not_not, Finsupp.add_apply]
      have hne : k ≠ i := by
        rintro rfl
        exact (Finsupp.mem_support_iff.mp hk) hi.2
      simp [hi.2, hne.symm]
    rw [MvPolynomial.coeff_mul_X']
    rw [if_neg h_not_supp]
  rw [h_zero] at h_coeff
  exact h_coeff

theorem prod_neg_if_X_mul_C (K : Finset (Fin n)) (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) (A : Matrix (Fin n) (Fin n) R) :
    (∏ i ∈ K, (- (if i ∈ S then MvPolynomial.X i * MvPolynomial.C (A i (σ i)) else 0))) =
    if K ⊆ S then (-1 : MvPolynomial (Fin n) R) ^ K.card * (∏ i ∈ K, MvPolynomial.X i) * MvPolynomial.C (∏ i ∈ K, A i (σ i)) else 0 := by
  split_ifs with hK
  · have : (∏ i ∈ K, (- (if i ∈ S then MvPolynomial.X i * MvPolynomial.C (A i (σ i)) else 0))) =
        ∏ i ∈ K, (- (MvPolynomial.X i * MvPolynomial.C (A i (σ i)))) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [if_pos (hK hi)]
    rw [this, prod_neg_X_mul_C]
  · rw [Finset.subset_iff] at hK
    push Not at hK
    obtain ⟨i, hiK, hiS⟩ := hK
    have : (- (if i ∈ S then MvPolynomial.X i * MvPolynomial.C (A i (σ i)) else (0 : MvPolynomial (Fin n) R))) = 0 := by
      rw [if_neg hiS, neg_zero]
    exact Finset.prod_eq_zero hiK this

theorem prod_ite_linearForm_or_one (t : Finset (Fin n)) (S : Finset (Fin n)) (K : Finset (Fin n))
    (ht : t = Finset.univ \ K) (_hKS : K ⊆ S) :
    (∏ i ∈ t, (if i ∈ S then linearForm A i else (1 : MvPolynomial (Fin n) R))) =
    ∏ i ∈ S \ K, linearForm A i := by
  subst ht
  have h_sub : S \ K ⊆ Finset.univ \ K := by
    intro x hx
    rw [Finset.mem_sdiff] at hx ⊢
    simp [hx.2]
  rw [← Finset.prod_sdiff h_sub]
  have h1 : (∏ i ∈ (Finset.univ \ K) \ (S \ K), (if i ∈ S then linearForm A i else (1 : MvPolynomial (Fin n) R))) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    rw [Finset.mem_sdiff, Finset.mem_sdiff] at hi
    have : i ∉ S := by
      intro hiS
      apply hi.2
      rw [Finset.mem_sdiff]
      exact ⟨hiS, hi.1.2⟩
    simp [this]
  have h3 : (∏ i ∈ S \ K, (if i ∈ S then linearForm A i else (1 : MvPolynomial (Fin n) R))) =
      ∏ i ∈ S \ K, linearForm A i := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.mem_sdiff] at hi
    simp [hi.1]
  rw [h1, h3, one_mul]

theorem det_macmahonRelMatrix'_eq_sum_subdetCoeff (A : Matrix (Fin n) (Fin n) R) (S : Finset (Fin n)) :
    Matrix.det (macmahonRelMatrix' A S) = ∑ K ∈ (Finset.univ : Finset (Fin n)).powerset,
      if K ⊆ S then subdetCoeff A K * (∏ i ∈ K, MvPolynomial.X i) * (∏ i ∈ S \ K, linearForm A i) else 0 := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  have h_prod (σ : Equiv.Perm (Fin n)) :
      (∏ i : Fin n, (macmahonRelMatrix' A S)ᵀ (σ i) i) =
      ∑ t ∈ (Finset.univ : Finset (Fin n)).powerset,
        (if ∀ i ∈ t, σ i = i then ∏ i ∈ t, (if i ∈ S then linearForm A i else 1) else 0) *
        (if Finset.univ \ t ⊆ S then
          ((-1 : MvPolynomial (Fin n) R) ^ (Finset.univ \ t).card * (∏ i ∈ Finset.univ \ t, MvPolynomial.X i) *
            MvPolynomial.C (∏ i ∈ Finset.univ \ t, A i (σ i))) else 0) := by
    have h_entry : (fun i => (macmahonRelMatrix' A S)ᵀ (σ i) i) =
        (fun i => (if i = σ i then (if i ∈ S then linearForm A i else 1) else 0) +
          (- (if i ∈ S then MvPolynomial.X i * MvPolynomial.C (A i (σ i)) else 0))) := by
      ext i
      simp only [macmahonRelMatrix', Matrix.transpose_apply, Matrix.of_apply, sub_eq_add_neg]
    rw [h_entry, Finset.prod_add]
    apply Finset.sum_congr rfl
    intro t _
    rw [prod_ite_eq_self t σ (fun i => if i ∈ S then linearForm A i else 1), prod_neg_if_X_mul_C (Finset.univ \ t) S σ A]
  simp_rw [h_prod, Finset.smul_sum]
  have h_comp (σ : Equiv.Perm (Fin n)) :
      (∑ t ∈ (Finset.univ : Finset (Fin n)).powerset,
        Equiv.Perm.sign σ •
          ((if ∀ i ∈ t, σ i = i then ∏ i ∈ t, (if i ∈ S then linearForm A i else 1) else 0) *
            (if Finset.univ \ t ⊆ S then
              ((-1 : MvPolynomial (Fin n) R) ^ (Finset.univ \ t).card * (∏ i ∈ Finset.univ \ t, MvPolynomial.X i) *
                MvPolynomial.C (∏ i ∈ Finset.univ \ t, A i (σ i))) else 0))) =
      ∑ K ∈ (Finset.univ : Finset (Fin n)).powerset,
        Equiv.Perm.sign σ •
          ((if ∀ i ∉ K, σ i = i then ∏ i ∈ Finset.univ \ K, (if i ∈ S then linearForm A i else 1) else 0) *
            (if K ⊆ S then
              ((-1 : MvPolynomial (Fin n) R) ^ K.card * (∏ i ∈ K, MvPolynomial.X i) *
                MvPolynomial.C (∏ i ∈ K, A i (σ i))) else 0)) := by
    have h_rw : (∑ t ∈ (Finset.univ : Finset (Fin n)).powerset,
        Equiv.Perm.sign σ •
          ((if ∀ i ∈ t, σ i = i then ∏ i ∈ t, (if i ∈ S then linearForm A i else 1) else 0) *
            (if Finset.univ \ t ⊆ S then
              ((-1 : MvPolynomial (Fin n) R) ^ (Finset.univ \ t).card * (∏ i ∈ Finset.univ \ t, MvPolynomial.X i) *
                MvPolynomial.C (∏ i ∈ Finset.univ \ t, A i (σ i))) else 0))) =
        ∑ t ∈ (Finset.univ : Finset (Fin n)).powerset,
        Equiv.Perm.sign σ •
          ((if ∀ i ∉ Finset.univ \ t, σ i = i then ∏ i ∈ Finset.univ \ (Finset.univ \ t), (if i ∈ S then linearForm A i else 1) else 0) *
            (if Finset.univ \ t ⊆ S then
              ((-1 : MvPolynomial (Fin n) R) ^ (Finset.univ \ t).card * (∏ i ∈ Finset.univ \ t, MvPolynomial.X i) *
                MvPolynomial.C (∏ i ∈ Finset.univ \ t, A i (σ i))) else 0)) := by
      apply Finset.sum_congr rfl
      intro t _
      simp_rw [forall_not_mem_compl_iff, compl_compl_eq]
    rw [h_rw]
    apply sum_powerset_compl (fun K =>
      Equiv.Perm.sign σ •
        ((if ∀ i ∉ K, σ i = i then ∏ i ∈ Finset.univ \ K, (if i ∈ S then linearForm A i else 1) else 0) *
          (if K ⊆ S then
            ((-1 : MvPolynomial (Fin n) R) ^ K.card * (∏ i ∈ K, MvPolynomial.X i) *
              MvPolynomial.C (∏ i ∈ K, A i (σ i))) else 0)))
  simp_rw [h_comp]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro K _
  split_ifs with hKS
  · rw [prod_ite_linearForm_or_one (Finset.univ \ K) S K rfl hKS]
    dsimp [subdetCoeff]
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro σ _
    simp only [Units.smul_def]
    split_ifs <;> ring
  · simp only [mul_zero, smul_zero, Finset.sum_const_zero]

theorem prod_linearForms_eq_of_le' (A : Matrix (Fin n) (Fin n) R) (m : Fin n →₀ ℕ) (K : Finset (Fin n)) (hKS : K ⊆ m.support) :
    (∏ i ∈ m.support \ K, linearForm A i) * (∏ i : Fin n, (linearForm A i) ^ (m i - 1)) =
    prodLinearForms A (Finsupp.equivFunOnFinite (m - indicatorFinsupp K)) := by
  have h_univ : (Finset.univ : Finset (Fin n)) = (m.support \ K) ∪ (K ∪ (Finset.univ \ m.support)) := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_sdiff, Finsupp.mem_support_iff, true_iff]
    by_cases hxK : x ∈ K
    · right; left; exact hxK
    · by_cases hxS : m x ≠ 0
      · left; exact ⟨hxS, hxK⟩
      · right; right; exact ⟨trivial, hxS⟩
  have h_disj1 : Disjoint (m.support \ K) (K ∪ (Finset.univ \ m.support)) := by
    rw [Finset.disjoint_union_right]
    refine ⟨?_, ?_⟩
    · rw [Finset.disjoint_iff_inter_eq_empty]
      ext x
      simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.notMem_empty, iff_false, not_and]
      intro ⟨_, hxK⟩ hxK'
      exact hxK hxK'
    · rw [Finset.disjoint_iff_inter_eq_empty]
      ext x
      simp only [Finset.mem_inter, Finset.mem_sdiff, Finsupp.mem_support_iff,
        Finset.notMem_empty, iff_false, not_and]
      intro ⟨hxS, _⟩ _
      exact not_not.mpr hxS
  have h_split : (∏ i : Fin n, (linearForm A i) ^ (m i - 1)) =
      (∏ i ∈ m.support \ K, (linearForm A i) ^ (m i - 1)) *
      (∏ i ∈ K ∪ (Finset.univ \ m.support), (linearForm A i) ^ (m i - 1)) := by
    conv_lhs => rw [h_univ, Finset.prod_union h_disj1]
  rw [h_split, ← mul_assoc]
  have h_comb : (∏ i ∈ m.support \ K, linearForm A i) * ∏ i ∈ m.support \ K, (linearForm A i) ^ (m i - 1) =
      ∏ i ∈ m.support \ K, (linearForm A i) ^ (m i) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.mem_sdiff, Finsupp.mem_support_iff] at hi
    have h1 : 1 ≤ m i := Nat.one_le_iff_ne_zero.mpr hi.1
    have : linearForm A i * linearForm A i ^ (m i - 1) = linearForm A i ^ (1 + (m i - 1)) := by
      rw [pow_add, pow_one]
    rw [this, Nat.add_sub_of_le h1]
  rw [h_comb]
  dsimp [prodLinearForms]
  conv_rhs => rw [h_univ, Finset.prod_union h_disj1]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.mem_sdiff] at hi
    have hK := indicatorFinsupp_apply_not_mem hi.2
    have : (Finsupp.equivFunOnFinite (m - indicatorFinsupp K)) i = m i := by
      dsimp [Finsupp.equivFunOnFinite]
      rw [hK, tsub_zero]
    rw [this]
  · have h_disj2 : Disjoint K (Finset.univ \ m.support) := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      ext x
      simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ, true_and,
        Finsupp.mem_support_iff, Finset.notMem_empty, iff_false, not_and]
      intro hxK hxS
      exact hxS (Finsupp.mem_support_iff.mp (hKS hxK))
    rw [Finset.prod_union h_disj2, Finset.prod_union h_disj2]
    congr 1
    · apply Finset.prod_congr rfl
      intro i hi
      have hK := indicatorFinsupp_apply_mem hi
      have : (Finsupp.equivFunOnFinite (m - indicatorFinsupp K)) i = m i - 1 := by
        dsimp [Finsupp.equivFunOnFinite]
        rw [hK]
      rw [this]
    · apply Finset.prod_congr rfl
      intro i hi
      rw [Finset.mem_sdiff, Finsupp.mem_support_iff, not_not] at hi
      have hi_not_K : i ∉ K := by
        intro hxK
        exact (Finsupp.mem_support_iff.mp (hKS hxK)) hi.2
      have hK := indicatorFinsupp_apply_not_mem hi_not_K
      have : (Finsupp.equivFunOnFinite (m - indicatorFinsupp K)) i = 0 := by
        dsimp [Finsupp.equivFunOnFinite]
        rw [hK, hi.2, tsub_zero]
      have hm_zero : m i - 1 = 0 := by
        rw [hi.2]
        rfl
      rw [this, hm_zero]

theorem subset_support_of_indicator_le {K : Finset (Fin n)} {m : Fin n →₀ ℕ}
    (hle : indicatorFinsupp K ≤ m) : K ⊆ m.support := by
  intro i hi
  rw [Finsupp.mem_support_iff]
  intro h0
  have h_le := hle i
  rw [indicatorFinsupp_apply_mem hi, h0] at h_le
  contradiction

theorem h_sum_eq_term' (A : Matrix (Fin n) (Fin n) R) (m : Fin n →₀ ℕ) (K : Finset (Fin n)) (hKS : K ⊆ m.support) :
    MvPolynomial.coeff (m - indicatorFinsupp K) ((∏ i ∈ m.support \ K, linearForm A i) * ∏ i : Fin n, (linearForm A i) ^ (m i - 1)) =
    G A (m - indicatorFinsupp K) := by
  dsimp [G]
  rw [prod_linearForms_eq_of_le' A m K hKS]

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
    (φ := MvPolynomial.toMvPowerSeries (detMacMahon A))
    (g := G A)
    (hφ0 := by rw [toMvPowerSeries_coeff_eq_coeff, coeff_zero_detMacMahon])
    (hg0 := G_zero A)
  by_cases hs : toFinsupp s = 0
  · have hs_zero : s = (fun _ => 0) := by
      have : Finsupp.equivFunOnFinite (toFinsupp s) = Finsupp.equivFunOnFinite 0 := by rw [hs]
      dsimp [toFinsupp] at this
      simp at this
      exact this
    subst hs_zero
    rw [macmahon_zero_exponent]
    have h_finsupp : toFinsupp (fun _ : Fin n => 0) = 0 := by
      ext i
      simp [toFinsupp]
    rw [h_finsupp]
    dsimp [invDetMacMahon]
    rw [MvPowerSeries.constantCoeff_invOfUnit]
    simp
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
        apply Finset.sum_congr rfl
        intro K _
        by_cases hKS : K ⊆ m.support
        · rw [if_pos hKS]
          have h_prod_X := subdetCoeff_mul_prod_X A K
          have h_mon := MvPolynomial.coeff_monomial_mul' m (indicatorFinsupp K) (subdetCoeffScalar A K)
            ((∏ i ∈ m.support \ K, linearForm A i) * ∏ i : Fin n, (linearForm A i) ^ (m i - 1))
          have h_rw : subdetCoeff A K * (∏ i ∈ K, MvPolynomial.X i) * (∏ i ∈ m.support \ K, linearForm A i) * ∏ i : Fin n, (linearForm A i) ^ (m i - 1) =
              (MvPolynomial.monomial (indicatorFinsupp K) (subdetCoeffScalar A K)) *
              ((∏ i ∈ m.support \ K, linearForm A i) * ∏ i : Fin n, (linearForm A i) ^ (m i - 1)) := by
            rw [mul_assoc (subdetCoeff A K * ∏ i ∈ K, MvPolynomial.X i), h_prod_X]
          rw [h_rw, h_mon]
          split_ifs with hle
          · congr 1
            exact h_sum_eq_term' A m K hKS
          · rfl
        · rw [if_neg hKS, zero_mul, MvPolynomial.coeff_zero]
          have hle : ¬ indicatorFinsupp K ≤ m := by
            intro h
            exact hKS (subset_support_of_indicator_le h)
          rw [if_neg hle]
      rw [h_sum_eq] at h_mul_zero
      exact h_mul_zero
    have hs_res := h_unique hrec (toFinsupp s)
    have hG : G A (toFinsupp s) = MvPolynomial.coeff (toFinsupp s) (prodLinearForms A s) := by
      dsimp [G, toFinsupp]
      simp
    rwa [← hG]

/-- Specialization to $n = 1$: The 1D Master Theorem is the geometric series expansion. -/
theorem macmahon_dim1 (A : Matrix (Fin 1) (Fin 1) R) (s : Fin 1 → ℕ) :
    MvPolynomial.coeff (toFinsupp s) (prodLinearForms A s) =
    MvPowerSeries.coeff (toFinsupp s) (invDetMacMahon A) :=
  macmahon_master_theorem A s

end MacMahon
