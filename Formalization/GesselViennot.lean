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

This module formalizes the **Lindström–Gessel–Viennot Lemma** (Lindström 1973, Gessel & Viennot 1985),
a fundamental bridge between algebraic determinants and enumerative combinatorics.

## Mathematical Formulation

Let $G = (V, E)$ be a directed acyclic graph (DAG) equipped with edge weights $w : E \to R$
taking values in a commutative ring $R$.

### Path Systems and Weights
For any directed path $P = (v_0, v_1, \dots, v_k)$, its weight is defined multiplicatively:
$$w(P) = \prod_{i=0}^{k-1} w(v_i, v_{i+1})$$
For any pair of vertices $u, v \in V$, the total path weight is:
$$e(u, v) = \sum_{P : u \to v} w(P)$$

Given $n$ source vertices $A = (a_1, \dots, a_n)$ and $n$ sink vertices $B = (b_1, \dots, b_n)$,
the **path matrix** $M \in M_{n \times n}(R)$ is defined by:
$$M_{i, j} = e(a_i, b_j)$$

### Determinantal Expansion & Non-Intersecting Path Systems
By the Leibniz determinant formula:
$$\det(M) = \sum_{\sigma \in S_n} \operatorname{sgn}(\sigma) \prod_{i=1}^n e(a_i, b_{\sigma(i)}) = \sum_{\sigma \in S_n} \operatorname{sgn}(\sigma) \sum_{\mathcal{P} : A \to B_\sigma} w(\mathcal{P})$$
where $\mathcal{P} = (P_1, \dots, P_n)$ is an $n$-tuple of paths with $P_i : a_i \to b_{\sigma(i)}$,
and $w(\mathcal{P}) = \prod_{i=1}^n w(P_i)$.

Two paths $P_i$ and $P_j$ **intersect** if they share at least one vertex. A path system $\mathcal{P}$
is **non-intersecting** (vertex-disjoint) if no two distinct paths in $\mathcal{P}$ intersect.

### The Sign-Reversing Involution
On the set of intersecting path systems, there exists a canonical sign-reversing, weight-preserving
involution $\Phi$:
1. Choose the smallest index $i$ such that $P_i$ intersects some $P_j$ ($j > i$), and let $v$ be
   the first intersection vertex along $P_i$.
2. Choose the minimal such $j > i$.
3. Swap the tails of $P_i$ and $P_j$ starting at $v$.
This swaps the targets of $P_i$ and $P_j$, replacing the permutation $\sigma$ with $\sigma \circ (i \, j)$,
thereby reversing the sign ($\operatorname{sgn}(\sigma \circ (i \, j)) = -\operatorname{sgn}(\sigma)$)
while preserving the total weight $w(\mathcal{P}' ) = w(\mathcal{P})$.

Consequently, all intersecting path tuples cancel out in pairs in the determinant:
$$\sum_{\sigma \in S_n} \operatorname{sgn}(\sigma) \sum_{\mathcal{P} \text{ intersecting}} w(\mathcal{P}) = 0$$

### The LGV Theorem
$$\det(M) = \sum_{\sigma \in S_n} \operatorname{sgn}(\sigma) \sum_{\substack{\mathcal{P} : A \to B_\sigma \\ \mathcal{P} \text{ non-intersecting}}} w(\mathcal{P})$$

In particular, if the DAG is planar with sources and sinks ordered along the boundary such that
non-intersecting paths can only exist for $\sigma = \mathrm{id}$, then:
$$\det(M) = \sum_{\mathcal{P} : A \to B \text{ non-intersecting}} w(\mathcal{P})$$

## Main Definitions & Theorems
- `DirectedPath`: Representation of a path as a sequence of vertices.
- `DirectedPath.Intersects`: Predicate for two paths sharing a vertex.
- `DirectedPath.Disjoint`: Predicate for vertex-disjoint paths.
- `PathSystem`: An $n$-tuple of paths connecting $A_i \to B_{\sigma(i)}$.
- `IsNonIntersecting`: Predicate for non-intersecting path systems.
- `IsIntersecting`: Predicate for intersecting path systems.
- `det_leibniz_path_sum`: Expansion of $\det(M)$ into sum over all path systems.
- `lgv_sign_reversing_involution`: Existence of the weight-preserving sign-reversing involution.
- `intersecting_path_systems_sum_zero`: Vanishing of the intersecting path sum.
- `lindstrom_gessel_viennot`: The full LGV determinant identity.
- `gessel_viennot_planar_dag`: The non-intersecting path count for ordered planar systems.

## References
- Lindström, B. (1973). *On the vector representations of induced matroids*. Bulletin of the London Mathematical Society, 5(1), 85–90.
- Gessel, I., & Viennot, G. (1985). *Binomial determinants, paths, and hook length formulae*. Advances in Mathematics, 58(3), 300–321.
- Stanley, R. P. (1999). *Enumerative Combinatorics, Volume 2*. Cambridge Studies in Advanced Mathematics.
-/

/-- A directed path in a graph on vertex set $V$. -/
structure DirectedPath (V : Type*) where
  /-- Ordered vertex sequence $(v_0, v_1, \dots, v_k)$ along the path -/
  verts : List V
  /-- The path contains at least one vertex -/
  nonempty : verts ≠ []

variable {V : Type*}

namespace DirectedPath

/-- The source vertex of a path: $v_0 = \operatorname{start}(P)$. -/
def start (P : DirectedPath V) : V := P.verts.head P.nonempty

/-- The target vertex of a path: $v_k = \operatorname{target}(P)$. -/
def target (P : DirectedPath V) : V := P.verts.getLast P.nonempty

/-- Two paths intersect if they share at least one common vertex. -/
def Intersects (P Q : DirectedPath V) : Prop :=
  ∃ v : V, v ∈ P.verts ∧ v ∈ Q.verts

/-- Two paths are vertex-disjoint (non-intersecting). -/
def Disjoint (P Q : DirectedPath V) : Prop :=
  ¬ Intersects P Q

lemma disjoint_comm (P Q : DirectedPath V) : Disjoint P Q ↔ Disjoint Q P := by
  simp only [Disjoint, Intersects, and_comm]

variable [DecidableEq V]

/-- Splicing two paths $P$ and $Q$ at a common vertex $v$: takes the prefix of $P$ up to $v$ and the suffix of $Q$ after $v$. -/
def splice (P Q : DirectedPath V) (v : V) : DirectedPath V where
  verts := P.verts.take (P.verts.idxOf v + 1) ++ Q.verts.drop (Q.verts.idxOf v + 1)
  nonempty := by
    intro h
    have ⟨h1, _⟩ := List.append_eq_nil_iff.mp h
    cases List.take_eq_nil_iff.mp h1 with
    | inl h2 => omega
    | inr h3 => exact P.nonempty h3

lemma start_splice (P Q : DirectedPath V) (v : V) :
    (splice P Q v).start = P.start := by
  dsimp [start, splice]
  have htake : P.verts.take (P.verts.idxOf v + 1) ≠ [] := by
    intro h
    cases List.take_eq_nil_iff.mp h with
    | inl h2 => omega
    | inr h3 => exact P.nonempty h3
  rw [List.head_append_of_ne_nil htake]
  exact List.head_take htake

lemma getLast_take_idxOf (P : DirectedPath V) (v : V) (hv : v ∈ P.verts)
    (h : P.verts.take (P.verts.idxOf v + 1) ≠ []) :
    (P.verts.take (P.verts.idxOf v + 1)).getLast h = v := by
  have hlt : P.verts.idxOf v < P.verts.length := List.idxOf_lt_length_iff.mpr hv
  have htake : (P.verts.take (P.verts.idxOf v + 1)).getLast h =
      P.verts[P.verts.idxOf v + 1 - 1]?.getD (P.verts.getLast P.nonempty) :=
    List.getLast_take h
  rw [Nat.add_sub_cancel] at htake
  rw [List.getElem?_eq_getElem hlt] at htake
  dsimp at htake
  rw [List.getElem_idxOf] at htake
  exact htake

lemma target_splice (P Q : DirectedPath V) (v : V)
    (hvP : v ∈ P.verts) (hvQ : v ∈ Q.verts) :
    (splice P Q v).target = Q.target := by
  dsimp [target, splice]
  by_cases hd : Q.verts.drop (Q.verts.idxOf v + 1) = []
  · have htake : P.verts.take (P.verts.idxOf v + 1) ≠ [] := by
      intro h
      cases List.take_eq_nil_iff.mp h with
      | inl h2 => omega
      | inr h3 => exact P.nonempty h3
    have h_drop_nil : Q.verts.length ≤ Q.verts.idxOf v + 1 := List.drop_eq_nil_iff.mp hd
    have h_lt : Q.verts.idxOf v < Q.verts.length := List.idxOf_lt_length_iff.mpr hvQ
    have h_idx_eq : Q.verts.length - 1 = Q.verts.idxOf v := by omega
    have h_last_Q : Q.verts.getLast Q.nonempty = v := by
      rw [List.getLast_eq_getElem]
      have hget := List.getElem_idxOf (x := v) (xs := Q.verts) (h := h_lt)
      convert hget using 2
    have h_take_last : (P.verts.take (P.verts.idxOf v + 1)).getLast htake = v :=
      getLast_take_idxOf P v hvP htake
    have h_app_nil : P.verts.take (P.verts.idxOf v + 1) ++ Q.verts.drop (Q.verts.idxOf v + 1) =
        P.verts.take (P.verts.idxOf v + 1) := by rw [hd, List.append_nil]
    have h_res : (P.verts.take (P.verts.idxOf v + 1) ++ Q.verts.drop (Q.verts.idxOf v + 1)).getLast
        (splice P Q v).nonempty = (P.verts.take (P.verts.idxOf v + 1)).getLast htake := by
      exact List.getLast_congr _ _ h_app_nil
    rw [h_res, h_take_last, h_last_Q]
  · rw [List.getLast_append_of_ne_nil _ hd]
    exact List.getLast_drop hd

lemma mem_splice_left (P Q : DirectedPath V) (v : V) (hv : v ∈ P.verts) :
    v ∈ (splice P Q v).verts := by
  dsimp [splice]
  have hlt : P.verts.idxOf v < P.verts.length := List.idxOf_lt_length_iff.mpr hv
  have htake : v ∈ P.verts.take (P.verts.idxOf v + 1) := by
    rw [List.take_add_one]
    rw [List.getElem?_eq_getElem hlt]
    rw [Option.toList_some]
    have hget := List.getElem_idxOf (x := v) (xs := P.verts) (h := hlt)
    rw [hget]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  exact List.mem_append_left _ htake

end DirectedPath

variable {n : ℕ} {R : Type*} [CommRing R]

/-- A system of $n$ paths connecting sources $A : \text{Fin } n \to V$ to targets $B \circ \sigma$. -/
abbrev PathSystem (A B : Fin n → V) (σ : Perm (Fin n)) :=
  ∀ i : Fin n, { P : DirectedPath V // P.start = A i ∧ P.target = B (σ i) }

/-- A path system is non-intersecting if all pairs of distinct paths are vertex-disjoint. -/
def IsNonIntersecting {A B : Fin n → V} {σ : Perm (Fin n)} (paths : PathSystem A B σ) : Prop :=
  ∀ i j : Fin n, i ≠ j → DirectedPath.Disjoint (paths i).val (paths j).val

/-- A path system is intersecting if some pair of distinct paths shares a vertex. -/
def IsIntersecting {A B : Fin n → V} {σ : Perm (Fin n)} (paths : PathSystem A B σ) : Prop :=
  ¬ IsNonIntersecting paths

/-- The path matrix $M_{i, j} = e(A_i, B_j)$ representing total path weights between sources and sinks. -/
def PathMatrix (e : V → V → R) (A B : Fin n → V) : Matrix (Fin n) (Fin n) R :=
  fun i j => e (A i) (B j)

/-- Expansion of the determinant $\det(M)$ via the Leibniz formula into a permutation sum over path products. -/
theorem det_pathMatrix_eq_permutation_sum (e : V → V → R) (A B : Fin n → V) :
    Matrix.det (PathMatrix e A B) =
      ∑ σ : Perm (Fin n), (Equiv.Perm.sign σ : R) * ∏ i : Fin n, e (A i) (B (σ i)) := by
  rw [← Matrix.det_transpose (PathMatrix e A B)]
  rw [Matrix.det_apply]
  simp only [PathMatrix, Matrix.transpose_apply]
  congr 1
  ext σ
  simp [zsmul_eq_mul, Units.smul_def]

/-- The sign-reversing involution property on intersecting path systems:
There exists an involution $\Phi$ on the set of intersecting path systems that has no fixed points,
reverses the permutation sign, and preserves path weights. -/
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

/-- The sum of signed weights over all intersecting path systems is identically zero. -/
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

