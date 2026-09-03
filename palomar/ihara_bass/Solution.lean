import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Formalization.IharaZeta
import Formalization.IharaBass

open Matrix
open scoped Matrix


variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (R : Type*) [CommRing R]
variable (u : R)
