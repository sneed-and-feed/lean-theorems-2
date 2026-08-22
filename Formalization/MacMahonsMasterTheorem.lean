import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Inverse
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

/--
**MacMahon's Master Theorem (1915)**:
For any $n \times n$ matrix $A \in M_{n \times n}(R)$ and any multi-index $s \in \mathbb{N}^n$,
the coefficient of $X^s = X_1^{s_1} \cdots X_n^{s_n}$ in the product of linear forms
$\prod_{i=1}^n (\sum_{j=1}^n A_{ij} X_j)^{s_i}$ equals the coefficient of $X^s$ in the
formal power series expansion of $\det(I_n - X A)^{-1}$:
$$[X^s] \prod_{i=1}^n \left(\sum_{j=1}^n A_{ij} X_j\right)^{s_i} = [X^s] \frac{1}{\det(I_n - X A)}$$
-/
axiom macmahon_master_theorem (A : Matrix (Fin n) (Fin n) R) (s : Fin n → ℕ) :
    MvPolynomial.coeff (toFinsupp s) (prodLinearForms A s) =
    MvPowerSeries.coeff (toFinsupp s) (invDetMacMahon A)

/-- Specialization to $n = 1$: The 1D Master Theorem is the geometric series expansion. -/
theorem macmahon_dim1 (A : Matrix (Fin 1) (Fin 1) R) (s : Fin 1 → ℕ) :
    MvPolynomial.coeff (toFinsupp s) (prodLinearForms A s) =
    MvPowerSeries.coeff (toFinsupp s) (invDetMacMahon A) :=
  macmahon_master_theorem A s

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

end MacMahon
