import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Basic

open Matrix Polynomial Finset
open scoped Polynomial


/-!
# Characteristic Polynomial of Cyclic Shift and Weighted Cyclic Matrices

This file proves the characteristic polynomial of a general weighted cyclic shift matrix
over an arbitrary commutative ring `R`.

## Main Definitions
- `shiftMatrix n W`: The `n × n` subdiagonal shift matrix with weights `W : Fin n → R`.
- `upperBidiagonal n W`: An auxiliary upper-bidiagonal polynomial matrix whose determinant
  computes the off-diagonal minor in the cofactor expansion.
- `cyclicWeightMatrix W`: The `L × L` cyclic matrix indexed by `ZMod L` where entry `(i, j)`
  is `W j` if `i = j + 1` and `0` otherwise.

## Main Results
- `charpoly_shiftMatrix`: The characteristic polynomial of `shiftMatrix n W` is `X ^ n`.
- `det_upperBidiagonal`: The determinant of `upperBidiagonal n W` is `∏ i, - C (W i)`.
- `charpoly_cyclicWeightMatrix`: For any `L : ℕ` with `[NeZero L]` and any `W : ZMod L → R`,
  the characteristic polynomial of `cyclicWeightMatrix W` is `X ^ L - C (∏ k, W k)`.
-/

variable {R : Type*} [CommRing R]

/-- The `n × n` subdiagonal shift matrix with weights `W`. -/
def shiftMatrix (n : ℕ) (W : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  fun i j => if (i : ℕ) = (j : ℕ) + 1 then W j else 0

/-- Upper-bidiagonal auxiliary matrix for cofactor expansion of cyclic matrices. -/
noncomputable def upperBidiagonal (n : ℕ) (W : Fin n → R) : Matrix (Fin n) (Fin n) (Polynomial R) :=
  fun i j => if (i : ℕ) = (j : ℕ) then - C (W j) else if (i : ℕ) + 1 = (j : ℕ) then X else 0

/-- The `L × L` cyclic matrix with weights `W : ZMod L → R`. -/
def cyclicWeightMatrix {L : ℕ} (W : ZMod L → R) : Matrix (ZMod L) (ZMod L) R :=
  Matrix.of fun i j => if i = j + 1 then W j else 0

/-- The characteristic polynomial of a nilpotent shift matrix is `X ^ n`. -/
lemma charpoly_shiftMatrix (n : ℕ) (W : Fin n → R) :
    (shiftMatrix n W).charpoly = X ^ n := sorry

/-- The determinant of an upper-bidiagonal polynomial matrix. -/
lemma det_upperBidiagonal (n : ℕ) (W : Fin n → R) :
    (upperBidiagonal n W).det = ∏ i : Fin n, - C (W i) := sorry

/-- The characteristic polynomial of an `L × L` cyclic weight matrix is `X ^ L - ∏ W`. -/
theorem charpoly_cyclicWeightMatrix {L : ℕ} [NeZero L] (W : ZMod L → R) :
    (cyclicWeightMatrix W).charpoly = X ^ L - C (∏ k : ZMod L, W k) := sorry
