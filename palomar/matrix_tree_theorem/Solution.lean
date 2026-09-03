import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Matrix Classical
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (R : Type*) [CommRing R]

namespace SimpleGraph

/-- The combinatorial Laplacian matrix $L(G) = D(G) - A(G)$ over a commutative ring $R$. -/
noncomputable def laplacianMatrix : Matrix V V R :=
  Matrix.diagonal (fun v => (G.degree v : R)) - G.adjMatrix R

@[simp]
lemma laplacian_apply_diag (v : V) :
    (laplacianMatrix G R) v v = (G.degree v : R) := by
  simp [laplacianMatrix]

lemma laplacian_apply_offdiag {u v : V} (h : u ≠ v) :
    (laplacianMatrix G R) u v = if G.Adj u v then -1 else 0 := by
  have h_diag : (u = v) ↔ False := by simp [h]
  simp [laplacianMatrix, h_diag, SimpleGraph.adjMatrix_apply]
  split_ifs <;> simp

lemma laplacian_apply_adj {u v : V} (h : G.Adj u v) :
    (laplacianMatrix G R) u v = -1 := by
  have h_ne : u ≠ v := h.ne
  rw [laplacian_apply_offdiag G R h_ne]
  simp [h]

lemma laplacian_apply_not_adj {u v : V} (h_ne : u ≠ v) (h_not_adj : ¬ G.Adj u v) :
    (laplacianMatrix G R) u v = 0 := by
  rw [laplacian_apply_offdiag G R h_ne]
  simp [h_not_adj]

/-- The Laplacian matrix is symmetric. -/
theorem laplacian_transpose_eq :
    (laplacianMatrix G R)ᵀ = laplacianMatrix G R := by
  ext u v
  simp only [laplacianMatrix, Matrix.transpose_apply, Matrix.sub_apply, Matrix.diagonal_apply, SimpleGraph.adjMatrix_apply]
  by_cases h : u = v
  · subst h; simp
  · have h_symm : (v = u) ↔ False := by simp [Ne.symm h]
    have h_u : (u = v) ↔ False := by simp [h]
    simp only [h_symm, h_u, ite_false, zero_sub, neg_inj]
    by_cases h_adj : G.Adj u v
    · simp [h_adj, G.adj_symm h_adj]
    · have h_not_symm : ¬ G.Adj v u := fun h' => h_adj (G.adj_symm h')
      simp [h_adj, h_not_symm]

/-- The row sums of the Laplacian matrix are all zero: $L \mathbf{1} = \mathbf{0}$. -/
theorem laplacian_row_sum_zero (u : V) :
    ∑ v : V, (laplacianMatrix G R) u v = 0 := by
  have h_split : ∑ v : V, (laplacianMatrix G R) u v =
      (laplacianMatrix G R) u u + ∑ v ∈ Finset.univ.erase u, (laplacianMatrix G R) u v := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ u)]
  rw [h_split, laplacian_apply_diag]
  have h_rest : ∑ v ∈ Finset.univ.erase u, (laplacianMatrix G R) u v =
      ∑ v ∈ Finset.univ.erase u, (if G.Adj u v then (-1 : R) else 0) := by
    apply Finset.sum_congr rfl
    intro v hv
    have h_ne : u ≠ v := (Finset.ne_of_mem_erase hv).symm
    exact laplacian_apply_offdiag G R h_ne
  rw [h_rest]
  have h_filter : ∑ v ∈ Finset.univ.erase u, (if G.Adj u v then (-1 : R) else 0) =
      ∑ _v ∈ (Finset.univ.erase u).filter (fun v => G.Adj u v), (-1 : R) := by
    rw [Finset.sum_filter]
  rw [h_filter]
  have h_set_eq : (Finset.univ.erase u).filter (fun v => G.Adj u v) = G.neighborFinset u := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨_, hadj⟩; exact hadj
    · intro hadj
      have hne : x ≠ u := fun heq => by subst heq; exact (fun h => (SimpleGraph.ne_of_adj G h) rfl) hadj
      exact ⟨hne, hadj⟩
  rw [h_set_eq, Finset.sum_const, nsmul_eq_mul]
  have h_card : (G.neighborFinset u).card = G.degree u := SimpleGraph.card_neighborFinset_eq_degree G u
  rw [h_card]
  ring

/-- An orientation of the edge set of $G$ choosing a source and target vertex for each undirected edge. -/
structure EdgeOrientation (G : SimpleGraph V) where
  source : G.edgeSet → V
  target : G.edgeSet → V
  src_mem : ∀ e : G.edgeSet, source e ∈ (e.val : Set V)
  tgt_mem : ∀ e : G.edgeSet, target e ∈ (e.val : Set V)
  src_ne_tgt : ∀ e : G.edgeSet, source e ≠ target e

variable [Fintype G.edgeSet]

/-- The signed vertex-edge incidence matrix $B \in M_{V \times E}(R)$ associated with an orientation. -/
noncomputable def incidenceMatrix (ori : EdgeOrientation G) : Matrix V G.edgeSet R :=
  fun v e => if v = ori.source e then 1 else if v = ori.target e then -1 else 0

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Fintype G.edgeSet] in
lemma edge_eq_sym2 (ori : EdgeOrientation G) (e : G.edgeSet) :
    e.val = s(ori.source e, ori.target e) := by
  have h_src : ori.source e ∈ (e.val : Set V) := ori.src_mem e
  have h_tgt : ori.target e ∈ (e.val : Set V) := ori.tgt_mem e
  have h_ne := ori.src_ne_tgt e
  rcases e with ⟨s, hs⟩
  induction s using Sym2.inductionOn with
  | hf x y =>
    have h_src' : ori.source ⟨s(x, y), hs⟩ ∈ s(x, y) := h_src
    have h_tgt' : ori.target ⟨s(x, y), hs⟩ ∈ s(x, y) := h_tgt
    rw [Sym2.mem_iff] at h_src' h_tgt'
    rcases h_src' with (h1 | h1) <;> rcases h_tgt' with (h2 | h2)
    · have : ori.source ⟨s(x, y), hs⟩ = ori.target ⟨s(x, y), hs⟩ := h1.trans h2.symm
      contradiction
    · exact congr_arg₂ (fun a b => s(a, b)) h1.symm h2.symm
    · exact (Sym2.eq_swap (a := x) (b := y)).trans (congr_arg₂ (fun a b => s(a, b)) h1.symm h2.symm)
    · have : ori.source ⟨s(x, y), hs⟩ = ori.target ⟨s(x, y), hs⟩ := h1.trans h2.symm
      contradiction

omit [Fintype V] [DecidableRel G.Adj] [Fintype G.edgeSet] in
lemma incidenceMatrix_sq_apply (ori : EdgeOrientation G) (u : V) (e : G.edgeSet) :
    (incidenceMatrix G R ori u e) * (incidenceMatrix G R ori u e) =
      if u ∈ (e.val : Set V) then 1 else 0 := by
  dsimp [incidenceMatrix]
  have h_ne := ori.src_ne_tgt e
  have h_eq := edge_eq_sym2 G ori e
  by_cases h_src : u = ori.source e
  · subst h_src
    have h_mem : ori.source e ∈ (e.val : Set V) := ori.src_mem e
    simp [h_mem]
  · by_cases h_tgt : u = ori.target e
    · subst h_tgt
      have h_mem : ori.target e ∈ (e.val : Set V) := ori.tgt_mem e
      have : ori.target e ≠ ori.source e := h_ne.symm
      simp [h_mem, this]
    · have h_not_mem : ¬ (u ∈ (e.val : Set V)) := by
        intro hu
        have hu' : u ∈ s(ori.source e, ori.target e) := by
          have : (e.val : Set V) = (s(ori.source e, ori.target e) : Set V) := by rw [h_eq]
          rwa [this] at hu
        rw [Sym2.mem_iff] at hu'
        rcases hu' with (rfl | rfl)
        · exact h_src rfl
        · exact h_tgt rfl
      simp [h_src, h_tgt, h_not_mem]

omit [Fintype V] [DecidableRel G.Adj] [Fintype G.edgeSet] in
lemma incidenceMatrix_mul_apply_offdiag (ori : EdgeOrientation G) {u v : V} (hne : u ≠ v) (e : G.edgeSet) :
    (incidenceMatrix G R ori u e) * (incidenceMatrix G R ori v e) =
      if e.val = s(u, v) then -1 else 0 := by
  dsimp [incidenceMatrix]
  have h_eq := edge_eq_sym2 G ori e
  have h_ne := ori.src_ne_tgt e
  by_cases h1 : u = ori.source e ∧ v = ori.target e
  · obtain ⟨rfl, rfl⟩ := h1
    have he_val : e.val = s(ori.source e, ori.target e) := h_eq
    have : ori.target e ≠ ori.source e := h_ne.symm
    simp [he_val, this]
  · by_cases h2 : u = ori.target e ∧ v = ori.source e
    · obtain ⟨rfl, rfl⟩ := h2
      have he_val : e.val = s(ori.target e, ori.source e) := by rw [h_eq, Sym2.eq_swap]
      have : ori.target e ≠ ori.source e := h_ne.symm
      simp [he_val, this]
    · have h_not_e : e.val ≠ s(u, v) := by
        intro he_eq
        have h_sym2 : s(ori.source e, ori.target e) = s(u, v) := by rwa [← h_eq]
        rw [Sym2.eq_iff] at h_sym2
        rcases h_sym2 with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact h1 ⟨rfl, rfl⟩
        · exact h2 ⟨rfl, rfl⟩
      have : (if e.val = s(u, v) then (-1 : R) else 0) = 0 := by simp [h_not_e]
      rw [this]
      by_cases hu_s : u = ori.source e
      · subst hu_s
        have hv_t : v ≠ ori.target e := fun h => h1 ⟨rfl, h⟩
        have hv_s : v ≠ ori.source e := hne.symm
        simp [hv_t, hv_s]
      · by_cases hu_t : u = ori.target e
        · subst hu_t
          have hv_s : v ≠ ori.source e := fun h => h2 ⟨rfl, h⟩
          have hv_t : v ≠ ori.target e := hne.symm
          simp [hv_s, hv_t]
        · simp [hu_s, hu_t]

lemma card_filter_mem_edgeSet_eq_degree (u : V) :
    (Finset.filter (fun (e : G.edgeSet) => u ∈ (e.val : Set V)) Finset.univ).card = G.degree u := by
  have h_equiv : (Finset.filter (fun (e : G.edgeSet) => u ∈ (e.val : Set V)) Finset.univ) ≃
      (G.incidenceSet u) := by
    refine {
      toFun := fun ⟨e, he⟩ => ⟨e.val, ?_⟩
      invFun := fun ⟨s, hs⟩ => ⟨⟨s, hs.1⟩, ?_⟩
      left_inv := fun ⟨e, he⟩ => rfl
      right_inv := fun ⟨s, hs⟩ => rfl
    }
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
      exact ⟨e.property, he⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hs.2
  have h_card := Fintype.card_congr h_equiv
  rw [Fintype.card_coe, SimpleGraph.card_incidenceSet_eq_degree] at h_card
  exact h_card

/-- The fundamental factorization of the graph Laplacian: $L = B B^T$. -/
theorem incidence_mul_transpose (ori : EdgeOrientation G)
    (_h_edge_cover : ∀ u v, G.Adj u v → ∃! e : G.edgeSet,
      (ori.source e = u ∧ ori.target e = v) ∨ (ori.source e = v ∧ ori.target e = u)) :
    incidenceMatrix G R ori * (incidenceMatrix G R ori)ᵀ = laplacianMatrix G R := by
  ext u v
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  by_cases heq : u = v
  · subst heq
    rw [laplacian_apply_diag]
    have h_terms : ∀ e : G.edgeSet, (incidenceMatrix G R ori u e) * (incidenceMatrix G R ori u e) =
        if u ∈ (e.val : Set V) then 1 else 0 := incidenceMatrix_sq_apply G R ori u
    simp_rw [h_terms]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [card_filter_mem_edgeSet_eq_degree]
  · rw [laplacian_apply_offdiag G R heq]
    have h_terms : ∀ e : G.edgeSet, (incidenceMatrix G R ori u e) * (incidenceMatrix G R ori v e) =
        if e.val = s(u, v) then -1 else 0 := incidenceMatrix_mul_apply_offdiag G R ori heq
    simp_rw [h_terms]
    by_cases hadj : G.Adj u v
    · simp only [hadj, ↓reduceIte]
      have h_exists : ∃! e : G.edgeSet, e.val = s(u, v) := by
        refine ⟨⟨s(u, v), hadj⟩, rfl, ?_⟩
        intro ⟨s', hs'⟩ he'
        exact Subtype.ext he'
      obtain ⟨e0, he0, huniq⟩ := h_exists
      rw [Fintype.sum_eq_single e0]
      · simp [he0]
      · intro e he
        have : e.val ≠ s(u, v) := fun h => he (huniq e h)
        simp [this]
    · simp only [hadj, ↓reduceIte]
      have h_empty : ∀ e : G.edgeSet, e.val ≠ s(u, v) := by
        intro e he_val
        have : s(u, v) ∈ G.edgeSet := by rw [← he_val]; exact e.property
        exact hadj this
      have : ∀ e : G.edgeSet, (if e.val = s(u, v) then (-1 : R) else 0) = 0 := by
        intro e
        simp [h_empty e]
      simp [this]

end SimpleGraph
