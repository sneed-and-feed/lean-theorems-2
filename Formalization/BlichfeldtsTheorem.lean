import Mathlib.Data.Real.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

open scoped BigOperators ENNReal Pointwise
open Classical
open MeasureTheory


/-!
# Blichfeldt's Theorem in the Geometry of Numbers

This module formalizes **Blichfeldt's Theorem** (Hans Frederick Blichfeldt, 1914),
a fundamental principle in the geometry of numbers that generalizes Minkowski's Convex Body Theorem
to arbitrary measurable sets and higher multiplicities.

## Mathematical Formulation

Let $E = \mathbb{R}^d = \text{EuclideanSpace } \mathbb{R} (\text{Fin } d)$ be the $d$-dimensional
Euclidean space equipped with the standard Lebesgue measure $\operatorname{vol} = \mu_{\text{Lebesgue}}$.

### Integer Lattice & Fundamental Domain
- The **integer lattice** $\mathbb{Z}^d \subset \mathbb{R}^d$ consists of points whose coordinates are integers.
- The standard **fundamental domain** (unit cube) is:
  $$\mathcal{F} = [0, 1)^d = \{x \in \mathbb{R}^d : \forall i, 0 \le x_i < 1\}$$
  with volume $\operatorname{vol}(\mathcal{F}) = 1$.
- The family of lattice translates $\{z + \mathcal{F}\}_{z \in \mathbb{Z}^d}$ forms a partition of $\mathbb{R}^d$:
  $$\mathbb{R}^d = \bigsqcup_{z \in \mathbb{Z}^d} (z + \mathcal{F})$$

### Blichfeldt's Theorem
Let $S \subset \mathbb{R}^d$ be any Lebesgue measurable set, and let $k \ge 1$ be an integer.
If the volume of $S$ exceeds $k$:
$$\operatorname{vol}(S) > k$$
then there exist $k + 1$ distinct points $x_0, x_1, \dots, x_k \in S$ such that all pairwise
differences belong to the integer lattice $\mathbb{Z}^d$:
$$x_i - x_j \in \mathbb{Z}^d \quad \text{for all } 0 \le i, j \le k$$

### Minkowski's Convex Body Theorem as a Corollary
If $K \subset \mathbb{R}^d$ is convex, centrally symmetric ($K = -K$), and $\operatorname{vol}(K) > 2^d$,
then the scaled set $\frac{1}{2} K = \{ \frac{1}{2} x : x \in K \}$ has volume
$\operatorname{vol}(\frac{1}{2} K) = 2^{-d} \operatorname{vol}(K) > 1$.
Applying Blichfeldt with $k = 1$ gives distinct $u, v \in \frac{1}{2} K$ with $u - v \in \mathbb{Z}^d$.
By symmetry and convexity:
$$u - v = \frac{1}{2}(2u) + \frac{1}{2}(-2v) \in K$$
so $u - v$ is a non-zero lattice point in $K \cap (\mathbb{Z}^d \setminus \{0\})$.

## Formalization Structure

- `Space`: The Euclidean space $\mathbb{R}^d = \text{EuclideanSpace } \mathbb{R} (\text{Fin } d)$.
- `IsIntegerVector`: Predicate asserting all coordinates are integers.
- `unitCube`: The fundamental domain $[0, 1)^d$.
- `latticeShift`: The shifted set $S + z$.
- `IsCentrallySymmetric`: Predicate $S = -S$.
- `blichfeldts_theorem`: The main theorem on $k+1$ points with lattice differences.
- `minkowski_convex_body_theorem`: Deduction of Minkowski's First Theorem.
- `blichfeldt_dim1`: Specialization to $d = 1$.

## References
- Blichfeldt, H. F. (1914). *A new principle in the geometry of numbers, with some applications*. Trans. Amer. Math. Soc., 15(3), 227–235.
- Minkowski, H. (1896). *Geometrie der Zahlen*. Teubner, Leipzig.
- Cassels, J. W. S. (1971). *An Introduction to the Geometry of Numbers*. Springer-Verlag. Chapter III.
- Siegel, C. L. (1989). *Lectures on the Geometry of Numbers*. Springer-Verlag.
-/

variable {d : ℕ}

namespace Blichfeldt

/-- The $d$-dimensional Euclidean space $\mathbb{R}^d$. -/
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Predicate asserting that a vector in $\mathbb{R}^d$ has integer coordinates. -/
def IsIntegerVector (v : Space d) : Prop :=
  ∀ i : Fin d, ∃ z : ℤ, v i = (z : ℝ)

/-- The standard fundamental domain (unit half-open cube) $[0, 1)^d \subset \mathbb{R}^d$. -/
def unitCube (d : ℕ) : Set (Space d) :=
  { x : Space d | ∀ i : Fin d, 0 ≤ x i ∧ x i < 1 }

/-- Lattice translate of a set by an integer vector $z$. -/
def latticeShift (S : Set (Space d)) (z : Fin d → ℤ) : Set (Space d) :=
  { x : Space d | ∃ s ∈ S, ∀ i : Fin d, x i = s i + (z i : ℝ) }

/-- Centrally symmetric set: $S = -S$. -/
def IsCentrallySymmetric (S : Set (Space d)) : Prop :=
  ∀ x ∈ S, -x ∈ S

theorem mem_span_basisFun_iff (v : Space d) :
    v ∈ Submodule.span ℤ (Set.range ⇑(EuclideanSpace.basisFun (Fin d) ℝ).toBasis) ↔ IsIntegerVector v := by
  let b := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
  rw [b.mem_span_iff_repr_mem ℤ]
  constructor
  · intro h i
    obtain ⟨z, hz⟩ := h i
    use z
    simp [b] at hz
    exact hz.symm
  · intro h i
    obtain ⟨z, hz⟩ := h i
    use z
    simp [b]
    exact hz.symm

theorem sum_indicator_eq_card {α ι : Type*} (U : Finset ι) (A : ι → Set α) (x : α)
    [DecidablePred (fun g => x ∈ A g)] :
    (∑ g ∈ U, (A g).indicator (1 : α → ℝ≥0∞) x) = ((U.filter (fun g => x ∈ A g)).card : ℝ≥0∞) := by
  classical
  rw [← Finset.sum_filter_ne_zero]
  have h_filt : (U.filter fun g => (A g).indicator (1 : α → ℝ≥0∞) x ≠ 0) = U.filter (fun g => x ∈ A g) := by
    ext g
    simp only [Finset.mem_filter, Set.indicator_apply, Pi.one_apply]
    split_ifs with h <;> simp [h]
  rw [h_filt]
  simp only [Set.indicator_apply, Pi.one_apply]
  have : ∀ g ∈ U.filter (fun g => x ∈ A g), (if x ∈ A g then (1 : ℝ≥0∞) else 0) = 1 := by
    intro g hg
    simp only [Finset.mem_filter] at hg
    simp [hg.2]
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_one]

/--
**Blichfeldt's Theorem (1914)**:
Let $S \subset \mathbb{R}^d$ be a Lebesgue measurable set with volume strictly greater
than an integer $k \ge 1$:
$$\operatorname{vol}(S) > k$$
Then there exist $k + 1$ distinct points $x_0, x_1, \dots, x_k \in S$ such that
every pairwise difference $x_i - x_j$ is an integer lattice vector in $\mathbb{Z}^d$:
$$x_i - x_j \in \mathbb{Z}^d \quad (\forall i, j)$$
-/
theorem blichfeldts_theorem (d : ℕ) (k : ℕ) (hk : 1 ≤ k) (S : Set (Space d))
    (hS_meas : MeasurableSet S)
    (hS_vol : (k : ℝ≥0∞) < MeasureTheory.volume S) :
    ∃ (pts : Fin (k + 1) → Space d),
      Function.Injective pts ∧
      (∀ i : Fin (k + 1), pts i ∈ S) ∧
      (∀ i j : Fin (k + 1), IsIntegerVector (pts i - pts j)) := by
  have _ := hk
  let ob := EuclideanSpace.basisFun (Fin d) ℝ
  let b := ob.toBasis
  let L := (Submodule.span ℤ (Set.range ⇑b)).toAddSubgroup
  have : Countable L :=
    Countable.of_equiv (Fin d → ℤ) (b.restrictScalars ℤ).equivFun.toEquiv.symm
  let F := ZSpan.fundamentalDomain b
  have hF_meas : MeasurableSet F := ZSpan.fundamentalDomain_measurableSet b
  have fund : IsAddFundamentalDomain L F volume :=
    ZSpan.isAddFundamentalDomain' b volume
  have hF_vol : volume F = 1 := by
    have h1 : F =ᵐ[volume] parallelepiped b :=
      ZSpan.fundamentalDomain_ae_parallelepiped b volume
    rw [measure_congr h1]
    exact ob.volume_parallelepiped
  have h_tsum : volume S = ∑' (g : L), volume ((g +ᵥ S) ∩ F) :=
    fund.measure_eq_tsum S
  have h_k_lt : (k : ℝ≥0∞) < ∑' (g : L), volume ((g +ᵥ S) ∩ F) := by
    rwa [← h_tsum]
  rw [ENNReal.tsum_eq_iSup_sum] at h_k_lt
  obtain ⟨U, hU⟩ := lt_iSup_iff.mp h_k_lt
  let A (g : L) : Set (Space d) := (g +ᵥ S) ∩ F
  have hA_meas (g : L) : MeasurableSet (A g) := by
    apply MeasurableSet.inter _ hF_meas
    exact MeasurableSet.const_vadd hS_meas (g : Space d)
  have h_sum_eq : (∑ g ∈ U, volume (A g)) = ∫⁻ x, ∑ g ∈ U, (A g).indicator (1 : Space d → ℝ≥0∞) x ∂volume := by
    have h_int : (∑ g ∈ U, ∫⁻ x, (A g).indicator (1 : Space d → ℝ≥0∞) x ∂volume) =
        ∫⁻ x, ∑ g ∈ U, (A g).indicator (1 : Space d → ℝ≥0∞) x ∂volume :=
      (lintegral_finsetSum U fun g _ => Measurable.indicator (measurable_const (a := (1 : ℝ≥0∞))) (hA_meas g)).symm
    have h_eq : (∑ g ∈ U, volume (A g)) = ∑ g ∈ U, ∫⁻ x, (A g).indicator (1 : Space d → ℝ≥0∞) x ∂volume := by
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [lintegral_indicator_one (hA_meas g)]
    rw [h_eq, h_int]
  let f (x : Space d) : ℝ≥0∞ := ∑ g ∈ U, (A g).indicator (1 : Space d → ℝ≥0∞) x
  have h_int_gt : (k : ℝ≥0∞) < ∫⁻ x, f x ∂volume := by
    rw [← h_sum_eq]
    exact hU
  have h_not_le : ¬ (∀ x, f x ≤ (k : ℝ≥0∞) * F.indicator 1 x) := by
    intro h_all
    have h_le : ∫⁻ x, f x ∂volume ≤ (k : ℝ≥0∞) := by
      calc
        ∫⁻ x, f x ∂volume ≤ ∫⁻ x, (k : ℝ≥0∞) * F.indicator 1 x ∂volume := lintegral_mono h_all
        _ = (k : ℝ≥0∞) * ∫⁻ x, F.indicator 1 x ∂volume := lintegral_const_mul _ (Measurable.indicator measurable_const hF_meas)
        _ = (k : ℝ≥0∞) * volume F := by rw [lintegral_indicator_one hF_meas]
        _ = (k : ℝ≥0∞) := by rw [hF_vol, mul_one]
    exact lt_irrefl _ (h_le.trans_lt h_int_gt)
  have h_ex : ∃ x, ¬ (f x ≤ (k : ℝ≥0∞) * F.indicator 1 x) := by
    by_contra h_all
    apply h_not_le
    push Not at h_all
    exact h_all
  obtain ⟨x0, hx0_not⟩ := h_ex
  have hx0 : (k : ℝ≥0∞) * F.indicator 1 x0 < f x0 := lt_of_not_ge hx0_not
  have hx0_F : x0 ∈ F := by
    by_contra h_not
    have h_f0 : f x0 = 0 := by
      dsimp [f]
      have : ∀ g ∈ U, (A g).indicator (1 : Space d → ℝ≥0∞) x0 = 0 := by
        intro g _
        apply Set.indicator_of_notMem
        intro h_in
        exact h_not h_in.2
      rw [Finset.sum_congr rfl this, Finset.sum_const_zero]
    rw [h_f0] at hx0
    exact not_lt_zero hx0
  rw [Set.indicator_of_mem hx0_F, Pi.one_apply, mul_one] at hx0
  dsimp [f] at hx0
  rw [sum_indicator_eq_card U A x0] at hx0
  rw [Nat.cast_lt] at hx0
  have h_card_le : k + 1 ≤ (U.filter (fun g => x0 ∈ A g)).card := Nat.succ_le_of_lt hx0
  let S_filt := U.filter (fun g => x0 ∈ A g)
  let emb := Fin.castLE h_card_le
  let g_seq : Fin (k + 1) → L := fun i => (S_filt.equivFin.symm (emb i) : L)
  have h_g_inj : Function.Injective g_seq := by
    intro i j h
    have h1 : S_filt.equivFin.symm (emb i) = S_filt.equivFin.symm (emb j) := Subtype.ext h
    have h2 : emb i = emb j := S_filt.equivFin.symm.injective h1
    exact Fin.castLE_injective h_card_le h2
  have h_g_mem (i : Fin (k + 1)) : x0 ∈ A (g_seq i) := by
    have h_sub := (S_filt.equivFin.symm (emb i)).prop
    rw [Finset.mem_filter] at h_sub
    exact h_sub.2
  let pts : Fin (k + 1) → Space d := fun i => -((g_seq i : L) : Space d) + x0
  refine ⟨pts, ?_, ?_, ?_⟩
  · intro i j h
    dsimp [pts] at h
    have h_add : -((g_seq i : L) : Space d) = -((g_seq j : L) : Space d) := by
      exact add_right_cancel h
    have h_eq : ((g_seq i : L) : Space d) = ((g_seq j : L) : Space d) := by
      exact neg_inj.mp h_add
    have h_g_eq : g_seq i = g_seq j := Subtype.ext h_eq
    exact h_g_inj h_g_eq
  · intro i
    have h_in := (h_g_mem i).1
    rwa [Set.mem_vadd_set_iff_neg_vadd_mem] at h_in
  · intro i j
    dsimp [pts]
    have h_diff : (-((g_seq i : L) : Space d) + x0) - (-((g_seq j : L) : Space d) + x0) =
        ((g_seq j : L) : Space d) - ((g_seq i : L) : Space d) := by
      abel
    rw [h_diff]
    have h_sub_mem : ((g_seq j : L) : Space d) - ((g_seq i : L) : Space d) =
        (((g_seq j - g_seq i : L) : L) : Space d) := rfl
    rw [h_sub_mem]
    exact (mem_span_basisFun_iff _).mp (g_seq j - g_seq i).prop

/--
**Minkowski's First Convex Body Theorem (as a Corollary to Blichfeldt)**:
Let $K \subset \mathbb{R}^d$ be a convex, centrally symmetric, measurable set with
volume $\operatorname{vol}(K) > 2^d$. Then $K$ contains at least one non-zero
integer lattice point $z \in \mathbb{Z}^d \setminus \{0\}$:
$$K \cap (\mathbb{Z}^d \setminus \{0\}) \ne \emptyset$$
-/
theorem minkowski_convex_body_theorem (d : ℕ) (K : Set (Space d))
    (hK_conv : Convex ℝ K)
    (hK_symm : IsCentrallySymmetric K)
    (hK_meas : MeasurableSet K)
    (hK_vol : (2 : ℝ≥0∞) ^ d < MeasureTheory.volume K) :
    ∃ z : Space d, z ∈ K ∧ z ≠ 0 ∧ IsIntegerVector z := by
  have _ := hK_meas
  let ob := EuclideanSpace.basisFun (Fin d) ℝ
  let b := ob.toBasis
  let L := (Submodule.span ℤ (Set.range ⇑b)).toAddSubgroup
  have : Countable L :=
    Countable.of_equiv (Fin d → ℤ) (b.restrictScalars ℤ).equivFun.toEquiv.symm
  have fund : IsAddFundamentalDomain L (ZSpan.fundamentalDomain b) volume :=
    ZSpan.isAddFundamentalDomain' b volume
  have h_vol_fd : volume (ZSpan.fundamentalDomain b) = 1 := by
    have h1 : ZSpan.fundamentalDomain b =ᵐ[volume] parallelepiped b :=
      ZSpan.fundamentalDomain_ae_parallelepiped b volume
    rw [measure_congr h1]
    exact ob.volume_parallelepiped
  have h_dim : Module.finrank ℝ (Space d) = d := by simp
  have h_ineq : volume (ZSpan.fundamentalDomain b) * 2 ^ (Module.finrank ℝ (Space d)) < volume K := by
    rw [h_vol_fd, one_mul, h_dim]
    exact hK_vol
  obtain ⟨x, hx_ne, hx_mem⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure fund hK_symm hK_conv h_ineq
  refine ⟨(x : Space d), hx_mem, ?_, ?_⟩
  · intro h0
    apply hx_ne
    exact Subtype.ext h0
  · exact (mem_span_basisFun_iff (x : Space d)).mp x.prop

/-- Specialization to dimension $d = 1$: Any measurable set of length $> 1$ on $\mathbb{R}$
contains two points with integer distance. -/
theorem blichfeldt_dim1 (S : Set (Space 1)) (hS_meas : MeasurableSet S)
    (hS_vol : (1 : ℝ≥0∞) < MeasureTheory.volume S) :
    ∃ x y : Space 1, x ∈ S ∧ y ∈ S ∧ x ≠ y ∧ IsIntegerVector (x - y) := by
  have h_vol : ((1 : ℕ) : ℝ≥0∞) < MeasureTheory.volume S := by
    simp only [Nat.cast_one]
    exact hS_vol
  obtain ⟨pts, h_inj, h_mem, h_diff⟩ := blichfeldts_theorem 1 1 (by norm_num) S hS_meas h_vol
  have h01 : (0 : Fin 2) ≠ (1 : Fin 2) := by decide
  refine ⟨pts 0, pts 1, h_mem 0, h_mem 1, fun h => h01 (h_inj h), h_diff 0 1⟩

end Blichfeldt


