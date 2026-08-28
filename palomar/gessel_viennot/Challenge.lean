import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Equiv Equiv.Perm Matrix BigOperators Classical

set_option linter.unusedSectionVars false

/-!
# Lindström–Gessel–Viennot Lemma (LGV Lemma)

This module formalizes the **Lindström–Gessel–Viennot Lemma** (Lindström 1973, Gessel & Viennot 1985),
a fundamental bridge between algebraic determinants and enumerative combinatorics.

## References
- Lindström, B. (1973). *On the vector representations of induced matroids*. Bulletin of the London Mathematical Society, 5(1), 85–90.
- Gessel, I., & Viennot, G. (1985). *Binomial determinants, paths, and hook length formulae*. Advances in Mathematics, 58(3), 300–321.
- Stanley, R. P. (1999). *Enumerative Combinatorics, Volume 2*. Cambridge Studies in Advanced Mathematics.
-/

/-- A directed path in a graph on vertex set $V$. -/
structure DirectedPath (V : Type*) where
  verts : List V
  nonempty : verts ≠ []

variable {n : ℕ} {R : Type*} [CommRing R] {V : Type*} [DecidableEq V] [Fintype (DirectedPath V)]

namespace DirectedPath

def start (P : DirectedPath V) : V := P.verts.head P.nonempty

def target (P : DirectedPath V) : V := P.verts.getLast P.nonempty

def Intersects (P Q : DirectedPath V) : Prop :=
  ∃ v : V, v ∈ P.verts ∧ v ∈ Q.verts

def Disjoint (P Q : DirectedPath V) : Prop :=
  ¬ Intersects P Q

lemma disjoint_comm (P Q : DirectedPath V) : Disjoint P Q ↔ Disjoint Q P := by
  simp only [Disjoint, Intersects, and_comm]

end DirectedPath

abbrev PathSystem (A B : Fin n → V) (σ : Perm (Fin n)) :=
  ∀ i : Fin n, { P : DirectedPath V // P.start = A i ∧ P.target = B (σ i) }

def IsNonIntersecting {A B : Fin n → V} {σ : Perm (Fin n)} (paths : PathSystem A B σ) : Prop :=
  ∀ i j : Fin n, i ≠ j → DirectedPath.Disjoint (paths i).val (paths j).val

def IsIntersecting {A B : Fin n → V} {σ : Perm (Fin n)} (paths : PathSystem A B σ) : Prop :=
  ¬ IsNonIntersecting paths

def PathMatrix (e : V → V → R) (A B : Fin n → V) : Matrix (Fin n) (Fin n) R :=
  fun i j => e (A i) (B j)

theorem det_pathMatrix_eq_permutation_sum (e : V → V → R) (A B : Fin n → V) :
    Matrix.det (PathMatrix e A B) =
      ∑ σ : Perm (Fin n), (Equiv.Perm.sign σ : R) * ∏ i : Fin n, e (A i) (B (σ i)) := sorry

def lgv_sign_reversing_involution_prop
    (A B : Fin n → V)
    (w : DirectedPath V → R) : Prop :=
  ∃ (Φ : (Σ σ : Perm (Fin n), { paths : PathSystem A B σ // IsIntersecting paths }) →
         (Σ σ : Perm (Fin n), { paths : PathSystem A B σ // IsIntersecting paths })),
    Function.Involutive Φ ∧
    (∀ x, Φ x ≠ x) ∧
    (∀ x, (Equiv.Perm.sign (Φ x).1 : R) * (∏ i, w ((Φ x).2.val i).val) =
          - ((Equiv.Perm.sign x.1 : R) * (∏ i, w (x.2.val i).val)))

theorem intersecting_path_systems_sum_zero
    (A B : Fin n → V)
    (w : DirectedPath V → R)
    (h_inv : lgv_sign_reversing_involution_prop A B w) :
    (∑ σ : Perm (Fin n), (Equiv.Perm.sign σ : R) *
      (∑ paths : { p : PathSystem A B σ // IsIntersecting p }, ∏ i, w (paths.val i).val)) = 0 := sorry

theorem lindstrom_gessel_viennot
    (e : V → V → R) (A B : Fin n → V)
    (w : DirectedPath V → R)
    (h_inv : lgv_sign_reversing_involution_prop A B w)
    (h_weight_sum : ∀ i j, e (A i) (B j) = ∑ P : { P : DirectedPath V // P.start = A i ∧ P.target = B j }, w P.val) :
    Matrix.det (PathMatrix e A B) =
      ∑ σ : Perm (Fin n), (Equiv.Perm.sign σ : R) *
        (∑ paths : { p : PathSystem A B σ // IsNonIntersecting p }, ∏ i, w (paths.val i).val) := sorry

theorem gessel_viennot_planar_dag
    (e : V → V → R) (A B : Fin n → V)
    (w : DirectedPath V → R)
    (h_inv : lgv_sign_reversing_involution_prop A B w)
    (h_weight_sum : ∀ i j, e (A i) (B j) = ∑ P : { P : DirectedPath V // P.start = A i ∧ P.target = B j }, w P.val)
    (h_only_id : ∀ σ : Perm (Fin n), (∃ paths : PathSystem A B σ, IsNonIntersecting paths) → σ = 1) :
    Matrix.det (PathMatrix e A B) =
      ∑ paths : { p : PathSystem A B 1 // IsNonIntersecting p }, ∏ i, w (paths.val i).val := sorry
