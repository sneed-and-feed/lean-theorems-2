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


/-!
# Lindström–Gessel–Viennot Lemma (LGV Lemma)
-/

/-- A directed path in a graph on vertex set $V$. -/
structure DirectedPath (V : Type*) where
  verts : List V
  nonempty : verts ≠ []

variable {V : Type*}

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

variable {n : ℕ} {R : Type*} [CommRing R]

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
      ∑ σ : Perm (Fin n), (Equiv.Perm.sign σ : R) * ∏ i : Fin n, e (A i) (B (σ i)) := by
  rw [← Matrix.det_transpose (PathMatrix e A B)]
  rw [Matrix.det_apply]
  simp only [PathMatrix, Matrix.transpose_apply]
  congr 1
  ext σ
  simp [zsmul_eq_mul, Units.smul_def]

def lgv_sign_reversing_involution_prop
    (A B : Fin n → V)
    (w : DirectedPath V → R) : Prop :=
  ∃ (Φ : (Σ σ : Perm (Fin n), { paths : PathSystem A B σ // IsIntersecting paths }) →
         (Σ σ : Perm (Fin n), { paths : PathSystem A B σ // IsIntersecting paths })),
    Function.Involutive Φ ∧
    (∀ x, Φ x ≠ x) ∧
    (∀ x, (Equiv.Perm.sign (Φ x).1 : R) * (∏ i, w ((Φ x).2.val i).val) =
          - ((Equiv.Perm.sign x.1 : R) * (∏ i, w (x.2.val i).val)))

variable [DecidableEq V] [Fintype (DirectedPath V)]

theorem intersecting_path_systems_sum_zero
    (A B : Fin n → V)
    (w : DirectedPath V → R)
    (h_inv : lgv_sign_reversing_involution_prop A B w) :
    (∑ σ : Perm (Fin n), (Equiv.Perm.sign σ : R) *
      (∑ paths : { p : PathSystem A B σ // IsIntersecting p }, ∏ i, w (paths.val i).val)) = 0 := by
  obtain ⟨Φ, h_invol, h_ne, h_anti⟩ := h_inv
  let X := Σ σ : Perm (Fin n), { paths : PathSystem A B σ // IsIntersecting paths }
  let f : X → R := fun x => (Equiv.Perm.sign x.1 : R) * (∏ i, w (x.2.val i).val)
  have h_sum : ∑ x : X, f x =
      (∑ σ : Perm (Fin n), (Equiv.Perm.sign σ : R) *
        (∑ paths : { p : PathSystem A B σ // IsIntersecting p }, ∏ i, w (paths.val i).val)) := by
    dsimp [f]
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro σ _
    rw [Finset.mul_sum]
  rw [← h_sum]
  have h_pair : ∀ x : X, f x + f (Φ x) = 0 := by
    intro x
    have : f (Φ x) = - f x := h_anti x
    rw [this, add_neg_cancel]
  have h_fixed : ∀ x : X, f x ≠ 0 → Φ x ≠ x := fun x _ => h_ne x
  have h_mem : ∀ x : X, Φ x ∈ (Finset.univ : Finset X) := fun x => Finset.mem_univ (Φ x)
  exact Finset.sum_ninvolution (fun x => Φ x) (fun a => h_pair a) (fun a ha => h_fixed a ha)
    h_mem (fun a => h_invol a)

lemma prod_weight_sum_eq (A B : Fin n → V) (σ : Perm (Fin n)) (w : DirectedPath V → R)
    (e : V → V → R)
    (h_weight_sum : ∀ i j, e (A i) (B j) = ∑ P : { P : DirectedPath V // P.start = A i ∧ P.target = B j }, w P.val) :
    ∏ i : Fin n, e (A i) (B (σ i)) = ∑ paths : PathSystem A B σ, ∏ i, w (paths i).val := by
  have : (∏ i : Fin n, e (A i) (B (σ i))) =
      ∏ i : Fin n, ∑ P : { P : DirectedPath V // P.start = A i ∧ P.target = B (σ i) }, w P.val := by
    apply Finset.prod_congr rfl
    intro i _
    exact h_weight_sum i (σ i)
  rw [this]
  exact Fintype.prod_sum (fun (i : Fin n) (P : { P : DirectedPath V // P.start = A i ∧ P.target = B (σ i) }) => w P.val)

lemma sum_pathSystem_eq_nonint_add_int (A B : Fin n → V) (σ : Perm (Fin n)) (w : DirectedPath V → R) :
    (∑ paths : PathSystem A B σ, ∏ i, w (paths i).val) =
      (∑ paths : { p : PathSystem A B σ // IsNonIntersecting p }, ∏ i, w (paths.val i).val) +
      (∑ paths : { p : PathSystem A B σ // IsIntersecting p }, ∏ i, w (paths.val i).val) := by
  have h1 : (∑ paths : { p : PathSystem A B σ // IsNonIntersecting p }, ∏ i, w (paths.val i).val) =
      ∑ paths ∈ Finset.univ.filter (fun p : PathSystem A B σ => IsNonIntersecting p), ∏ i, w (paths i).val :=
    (Finset.sum_subtype (Finset.univ.filter (fun p : PathSystem A B σ => IsNonIntersecting p)) (fun x => by simp) (fun p => ∏ i, w (p i).val)).symm
  have h2 : (∑ paths : { p : PathSystem A B σ // IsIntersecting p }, ∏ i, w (paths.val i).val) =
      ∑ paths ∈ Finset.univ.filter (fun p : PathSystem A B σ => ¬ IsNonIntersecting p), ∏ i, w (paths i).val :=
    (Finset.sum_subtype (Finset.univ.filter (fun p : PathSystem A B σ => ¬ IsNonIntersecting p)) (fun (x : PathSystem A B σ) => by simp [IsIntersecting]) (fun p => ∏ i, w (p i).val)).symm
  rw [h1, h2, Finset.sum_filter_add_sum_filter_not]

/-- **Lindström–Gessel–Viennot (LGV) Lemma**:
The determinant of the path matrix $M$ equals the signed sum over all **non-intersecting** path systems:
$$\det(M) = \sum_{\sigma \in S_n} \operatorname{sgn}(\sigma) \sum_{\mathcal{P} : A \to B_\sigma \text{ non-intersecting}} w(\mathcal{P})$$ -/
theorem lindstrom_gessel_viennot
    (e : V → V → R) (A B : Fin n → V)
    (w : DirectedPath V → R)
    (h_inv : lgv_sign_reversing_involution_prop A B w)
    (h_weight_sum : ∀ i j, e (A i) (B j) = ∑ P : { P : DirectedPath V // P.start = A i ∧ P.target = B j }, w P.val) :
    Matrix.det (PathMatrix e A B) =
      ∑ σ : Perm (Fin n), (Equiv.Perm.sign σ : R) *
        (∑ paths : { p : PathSystem A B σ // IsNonIntersecting p }, ∏ i, w (paths.val i).val) := by
  rw [det_pathMatrix_eq_permutation_sum]
  have h_prod : ∀ σ : Perm (Fin n), ∏ i : Fin n, e (A i) (B (σ i)) =
      (∑ paths : { p : PathSystem A B σ // IsNonIntersecting p }, ∏ i, w (paths.val i).val) +
      (∑ paths : { p : PathSystem A B σ // IsIntersecting p }, ∏ i, w (paths.val i).val) := by
    intro σ
    rw [prod_weight_sum_eq A B σ w e h_weight_sum]
    exact sum_pathSystem_eq_nonint_add_int A B σ w
  simp_rw [h_prod, mul_add, Finset.sum_add_distrib]
  rw [intersecting_path_systems_sum_zero A B w h_inv, add_zero]

/-- **LGV Lemma for Planar Directed Acyclic Graphs**:
When non-intersecting paths only exist for the identity permutation $\sigma = \mathrm{id}$
(e.g., standard planar grid DAGs with boundary-ordered sources and sinks),
$\det(M)$ directly counts the total weight of non-intersecting path systems:
$$\det(M) = \sum_{\mathcal{P} : A \to B \text{ non-intersecting}} w(\mathcal{P})$$ -/
theorem gessel_viennot_planar_dag
    (e : V → V → R) (A B : Fin n → V)
    (w : DirectedPath V → R)
    (h_inv : lgv_sign_reversing_involution_prop A B w)
    (h_weight_sum : ∀ i j, e (A i) (B j) = ∑ P : { P : DirectedPath V // P.start = A i ∧ P.target = B j }, w P.val)
    (h_only_id : ∀ σ : Perm (Fin n), (∃ paths : PathSystem A B σ, IsNonIntersecting paths) → σ = 1) :
    Matrix.det (PathMatrix e A B) =
      ∑ paths : { p : PathSystem A B 1 // IsNonIntersecting p }, ∏ i, w (paths.val i).val := by
  rw [lindstrom_gessel_viennot e A B w h_inv h_weight_sum]
  rw [Fintype.sum_eq_single (1 : Perm (Fin n))]
  · simp
  · intro σ hσ
    have h_empty : IsEmpty { p : PathSystem A B σ // IsNonIntersecting p } := by
      refine ⟨fun ⟨paths, hp⟩ => hσ (h_only_id σ ⟨paths, hp⟩)⟩
    simp
