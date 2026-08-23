import Formalization.MengersTheorem.Basic
import Formalization.MengersTheorem.VertexMenger

open scoped Finset
open Classical

set_option linter.unusedSectionVars false

/-!
# Whitney's Connectivity Theorem

This module formalizes Whitney's Theorem (Hassler Whitney, 1932) on graph connectivity:
- `IsKConnected`: Definition of $k$-vertex-connected graphs.
- `kConnected_iff_paths`: Equivalence between $k$-connectivity and having $\ge k$
  internally vertex-disjoint paths between every non-adjacent pair of vertices.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace MengersTheorem

/-- A graph is $k$-connected if $|V| > k$ and removing fewer than $k$ vertices leaves $G$ connected. -/
def IsKConnected (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧
  ∀ S : Finset V, S.card < k →
    ∀ u v : V, u ∉ S → v ∉ S → u ≠ v →
      ∃ p : STPath G u v, Disjoint p.verts.toFinset S

/--
**Whitney's Theorem (1932)**:
A graph $G$ on at least $k+1$ vertices is $k$-connected if and only if every pair
of distinct vertices has at least $k$ pairwise internally vertex-disjoint paths.
-/
theorem kConnected_iff_paths (G : SimpleGraph V) (k : ℕ) (_hk : 1 ≤ k) :
    IsKConnected G k ↔
      (k < Fintype.card V ∧
       ∀ u v : V, u ≠ v → ¬ G.Adj u v → k ≤ maxDisjointPaths G u v) := by
  constructor
  · rintro ⟨hkV, hconn⟩
    refine ⟨hkV, ?_⟩
    intro u v hne hnot_adj
    rw [mengers_theorem_vertex G u v hne hnot_adj]
    dsimp [minVertexSeparator]
    apply le_csInf
    · exact ⟨(Finset.univ \ {u, v}).card, Finset.univ \ {u, v}, univ_sdiff_isVertexSeparator G u v hne hnot_adj, rfl⟩
    · rintro n ⟨S, hS, rfl⟩
      by_contra! hlt
      have hp := hconn S hlt u v hS.1 hS.2.1 hne
      obtain ⟨p, hp_disj⟩ := hp
      obtain ⟨w, hw_S, hw_inner⟩ := hS.2.2 p
      have hw_in_verts : w ∈ p.verts.toFinset := by
        simp only [innerVertices, Finset.mem_sdiff] at hw_inner
        exact hw_inner.1
      have hdisj_mem := Finset.disjoint_left.mp hp_disj hw_in_verts
      exact hdisj_mem hw_S
  · rintro ⟨hkV, hpaths⟩
    refine ⟨hkV, ?_⟩
    intro S hS u v hu_not_S hv_not_S hne
    by_cases hadj : G.Adj u v
    · refine ⟨STPath.mk1 hadj, ?_⟩
      rw [Finset.disjoint_left]
      intro x hx
      simp [STPath.mk1_verts] at hx
      rcases hx with rfl | rfl
      · exact hu_not_S
      · exact hv_not_S
    · have h_le := hpaths u v hne hadj
      rw [mengers_theorem_vertex G u v hne hadj] at h_le
      have h_not_sep : ¬ IsVertexSeparator G u v S := by
        intro h_is_sep
        have h_in_set : S.card ∈ { n : ℕ | ∃ S' : Finset V, IsVertexSeparator G u v S' ∧ S'.card = n } := ⟨S, h_is_sep, rfl⟩
        have h_bddBelow : BddBelow { n : ℕ | ∃ S' : Finset V, IsVertexSeparator G u v S' ∧ S'.card = n } := ⟨0, fun _ _ => Nat.zero_le _⟩
        have h_inf_le := csInf_le h_bddBelow h_in_set
        dsimp [minVertexSeparator] at h_le
        omega
      have h_all : ¬ (∀ p : STPath G u v, ∃ w ∈ S, w ∈ innerVertices p) :=
        fun h_sep_all => h_not_sep ⟨hu_not_S, hv_not_S, h_sep_all⟩
      push Not at h_all
      obtain ⟨p, hp_inner⟩ := h_all
      refine ⟨p, ?_⟩
      rw [Finset.disjoint_left]
      intro x hx
      by_contra hxS
      by_cases hxu : x = u
      · subst hxu; exact hu_not_S hxS
      · by_cases hxv : x = v
        · subst hxv; exact hv_not_S hxS
        · have hx_inner : x ∈ innerVertices p := by
            simp only [innerVertices, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
              not_or, List.mem_toFinset]
            exact ⟨List.mem_toFinset.mp hx, hxu, hxv⟩
          exact hp_inner x hxS hx_inner

end MengersTheorem
