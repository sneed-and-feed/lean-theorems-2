import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Diagonal

/-!
# Spectral Theory of Circulant Matrices and the Discrete Fourier Transform

This module formalizes the spectral theory of circulant matrices over `ℂ`, establishing
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

/-- 1. Simultaneous character eigenvectors: `χ_k` is an eigenvector of `Matrix.circulant c`
with eigenvalue `ZMod.dft c k`. -/
theorem circulant_mulVec_character (c : ZMod n → ℂ) (k : ZMod n) :
    Matrix.mulVec (Matrix.circulant c) (fun j => ZMod.stdAddChar (j * k)) =
      ZMod.dft c k • (fun j => ZMod.stdAddChar (j * k)) := sorry

/-- 2. Character orthogonality implies `Fᴴ * F = n • 1`. -/
theorem fourierMatrix_conjTranspose_mul (n : ℕ) [NeZero n] :
    (fourierMatrix n).conjTranspose * fourierMatrix n = (n : ℂ) • 1 := sorry

/-- 3. The determinant of a circulant matrix is the product of its DFT eigenvalues. -/
theorem det_circulant (c : ZMod n → ℂ) :
    (Matrix.circulant c).det = ∏ k : ZMod n, ZMod.dft c k := sorry

/-- 4. The characteristic polynomial of a circulant matrix is the product of linear factors
`X - C (ZMod.dft c k)`. -/
theorem charpoly_circulant (c : ZMod n → ℂ) :
    (Matrix.circulant c).charpoly =
      ∏ k : ZMod n, (Polynomial.X - Polynomial.C (ZMod.dft c k)) := sorry
