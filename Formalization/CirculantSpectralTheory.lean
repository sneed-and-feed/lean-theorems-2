import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Diagonal

/-!
# Spectral Theory of Circulant Matrices and the Discrete Fourier Transform

This file formalizes the spectral theory of circulant matrices over `ℂ`, establishing
the connection between `Matrix.Circulant` and `ZMod.dft`:
1. Simultaneous Character Eigenvectors: The characters `χ_k` are simultaneous eigenvectors
   of any circulant matrix `Matrix.circulant c`, with eigenvalue `ZMod.dft c k`.
2. Fourier Matrix Diagonalization: The unnormalized Fourier matrix `F` diagonalizes
   every circulant matrix.
3. Circulant Determinant Formula: `det (Matrix.circulant c) = ∏ k, ZMod.dft c k`.
4. Circulant Characteristic Polynomial: `charpoly (Matrix.circulant c) = ∏ k, (X - C (ZMod.dft c k))`.
-/

open Matrix Polynomial Finset
open scoped BigOperators Matrix ComplexConjugate

variable {n : ℕ} [NeZero n]

/-- The discrete Fourier transform matrix (unnormalized) on `ZMod n`. -/
noncomputable def fourierMatrix (n : ℕ) [NeZero n] : Matrix (ZMod n) (ZMod n) ℂ :=
  fun j k => ZMod.stdAddChar (j * k)

/-- Complex conjugate of the standard additive character evaluated on `ZMod n`. -/
lemma star_stdAddChar (a : ZMod n) : star (ZMod.stdAddChar a) = ZMod.stdAddChar (-a) := by
  rw [← starRingEnd_apply, ZMod.stdAddChar_apply, ← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv, ZMod.stdAddChar_apply]

/-- Character orthogonality on `ZMod n`: the sum of characters is `n` if trivial and `0` otherwise. -/
lemma sum_stdAddChar (t : ZMod n) :
    ∑ i : ZMod n, ZMod.stdAddChar (t * i) = if t = 0 then (n : ℂ) else 0 := by
  split_ifs with h
  · simp [h, ZMod.card]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar n h)

/-- 1. Simultaneous character eigenvectors: `χ_k` is an eigenvector of `Matrix.circulant c`
with eigenvalue `ZMod.dft c k`. -/
theorem circulant_mulVec_character (c : ZMod n → ℂ) (k : ZMod n) :
    Matrix.mulVec (Matrix.circulant c) (fun j => ZMod.stdAddChar (j * k)) =
      ZMod.dft c k • (fun j => ZMod.stdAddChar (j * k)) := by
  ext i
  simp only [mulVec, dotProduct, circulant_apply, Pi.smul_apply, smul_eq_mul]
  have h_reindex : (∑ j, c (i - j) * ZMod.stdAddChar (j * k)) =
      ∑ l, c l * ZMod.stdAddChar ((i - l) * k) :=
    Fintype.sum_equiv (Equiv.subLeft i) _ _ fun _ => by simp [sub_sub_cancel]
  have h_split (l : ZMod n) :
      c l * ZMod.stdAddChar ((i - l) * k) =
        (ZMod.stdAddChar (-(l * k)) * c l) * ZMod.stdAddChar (i * k) := by
    rw [show (i - l) * k = -(l * k) + i * k by ring, AddChar.map_add_eq_mul]
    ring
  rw [h_reindex]
  simp_rw [h_split, ← sum_mul]
  rfl

/-- 2. Character orthogonality implies `Fᴴ * F = n • 1`. -/
theorem fourierMatrix_conjTranspose_mul (n : ℕ) [NeZero n] :
    (fourierMatrix n).conjTranspose * fourierMatrix n = (n : ℂ) • 1 := by
  ext i k
  simp only [mul_apply, conjTranspose_apply, fourierMatrix, Matrix.smul_apply, Matrix.one_apply]
  have h_term (j : ZMod n) :
      star (ZMod.stdAddChar (j * i)) * ZMod.stdAddChar (j * k) =
        ZMod.stdAddChar ((k - i) * j) := by
    rw [mul_comm j i, star_stdAddChar, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [h_term, sum_stdAddChar, sub_eq_zero, eq_comm]
  split_ifs <;> simp

/-- The unnormalized Fourier matrix has non-zero determinant. -/
lemma fourierMatrix_det_ne_zero (n : ℕ) [NeZero n] :
    (fourierMatrix n).det ≠ 0 := by
  intro h_zero
  have h_prod := fourierMatrix_conjTranspose_mul n
  apply_fun Matrix.det at h_prod
  rw [det_mul, h_zero, mul_zero, det_smul] at h_prod
  simp only [det_one, mul_one, ZMod.card n] at h_prod
  exact pow_ne_zero n (Nat.cast_ne_zero.mpr (NeZero.ne n)) h_prod.symm

/-- Circulant matrix diagonalization by the Fourier matrix. -/
lemma circulant_mul_fourierMatrix (c : ZMod n → ℂ) :
    Matrix.circulant c * fourierMatrix n =
      fourierMatrix n * Matrix.diagonal (ZMod.dft c) := by
  ext i k
  simp only [mul_apply, fourierMatrix, diagonal_apply, mul_ite, mul_zero]
  change (Matrix.mulVec (Matrix.circulant c) (fun j => ZMod.stdAddChar (j * k))) i = _
  rw [circulant_mulVec_character c k]
  simp [sum_ite_eq', mul_comm]

/-- 3. The determinant of a circulant matrix is the product of its DFT eigenvalues. -/
theorem det_circulant (c : ZMod n → ℂ) :
    (Matrix.circulant c).det = ∏ k : ZMod n, ZMod.dft c k := by
  have h := congr_arg Matrix.det (circulant_mul_fourierMatrix c)
  rw [det_mul, det_mul, det_diagonal, mul_comm (fourierMatrix n).det] at h
  exact mul_right_cancel₀ (fourierMatrix_det_ne_zero n) h

/-- 4. The characteristic polynomial of a circulant matrix is the product of linear factors
`X - C (ZMod.dft c k)`. -/
theorem charpoly_circulant (c : ZMod n → ℂ) :
    (Matrix.circulant c).charpoly =
      ∏ k : ZMod n, (Polynomial.X - Polynomial.C (ZMod.dft c k)) := by
  have h_diag := circulant_mul_fourierMatrix c
  let A := Matrix.circulant c
  let D := Matrix.diagonal (ZMod.dft c)
  let F := fourierMatrix n
  let FP : Matrix (ZMod n) (ZMod n) ℂ[X] := F.map Polynomial.C
  have h_charmatrix_mul : charmatrix A * FP = FP * charmatrix D := by
    dsimp only [FP, charmatrix]
    change _ * (C : ℂ →+* ℂ[X]).mapMatrix F = (C : ℂ →+* ℂ[X]).mapMatrix F * _
    rw [sub_mul, mul_sub, scalar_apply, ← smul_eq_diagonal_mul, ← smul_eq_mul_diagonal,
      ← map_mul, ← map_mul, h_diag]
  have h_det_eq := congr_arg Matrix.det h_charmatrix_mul
  rw [det_mul, det_mul, mul_comm FP.det] at h_det_eq
  have h_det_ne : FP.det ≠ 0 := by
    rw [show FP = (C : ℂ →+* ℂ[X]).mapMatrix F from rfl, ← RingHom.map_det, ne_eq, C_eq_zero]
    exact fourierMatrix_det_ne_zero n
  have h_char_eq := mul_right_cancel₀ h_det_ne h_det_eq
  change A.charpoly = D.charpoly at h_char_eq
  rw [h_char_eq]
  exact charpoly_diagonal (ZMod.dft c)
