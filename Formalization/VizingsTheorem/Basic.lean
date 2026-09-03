import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic

open scoped BigOperators
open Classical

/-!
# Vizing's Theorem — Basic Definitions and Setup

This module defines edge colorings, the chromatic index $\chi'(G)$,
partial edge colorings, used/missing colors at vertices, and foundational lemmas.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

namespace SimpleGraph

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma mk_edge_symm {u v : V} (h : G.Adj v u) :
    (⟨s(v, u), h⟩ : G.edgeSet) = ⟨s(u, v), h.symm⟩ := Subtype.ext Sym2.eq_swap

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma mk_edge_inj_neighbor {u v w : V} (hv : G.Adj u v) (hw : G.Adj u w) :
    (⟨s(u, v), hv⟩ : G.edgeSet) = ⟨s(u, w), hw⟩ ↔ v = w := by
  constructor
  · intro heq
    have : s(u, v) = s(u, w) := Subtype.ext_iff.mp heq
    rw [Sym2.eq_iff] at this
    rcases this with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · rfl
    · exact (hv.ne rfl).elim
  · rintro rfl; rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma mk_edge_ne_neighbor {u v w : V} (hv : G.Adj u v) (hw : G.Adj u w) (h : v ≠ w) :
    (⟨s(u, v), hv⟩ : G.edgeSet) ≠ ⟨s(u, w), hw⟩ := fun heq =>
  h ((mk_edge_inj_neighbor G hv hw).mp heq)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma edge_eq_of_mem (e : G.edgeSet) (v : V) (hv : v ∈ (e : Sym2 V)) :
    ∃ (w : V) (h : G.Adj v w), e = ⟨s(v, w), h⟩ := by
  rcases e with ⟨e_val, he_prop⟩
  induction e_val using Sym2.inductionOn with
  | hf x y =>
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact ⟨y, he_prop, rfl⟩
    · exact ⟨x, he_prop.symm, mk_edge_symm G he_prop⟩

/-- Two undirected edges in $G$ share a common endpoint vertex. -/
def ShareVertex (e₁ e₂ : G.edgeSet) : Prop :=
  ∃ v : V, v ∈ (e₁ : Sym2 V) ∧ v ∈ (e₂ : Sym2 V)

/-- A proper edge coloring of $G$ with color set $\alpha$ assigns colors to edges
such that any two distinct incident edges receive different colors. -/
def IsProperEdgeColoring {α : Type*} (c : G.edgeSet → α) : Prop :=
  ∀ ⦃e₁ e₂ : G.edgeSet⦄, e₁ ≠ e₂ → ShareVertex G e₁ e₂ → c e₁ ≠ c e₂

/-- The type of proper edge colorings of $G$ using $k$ colors. -/
structure EdgeColoring (k : ℕ) where
  color : G.edgeSet → Fin k
  proper : IsProperEdgeColoring G color

/-- A graph is $k$-edge-colorable if it admits a proper $k$-edge-coloring. -/
def IsEdgeColorable (k : ℕ) : Prop := Nonempty (EdgeColoring G k)

/-- The chromatic index (edge chromatic number) $\chi'(G)$ is the minimum number of colors
needed to properly color the edges of $G$. -/
noncomputable def chromaticIndex : ℕ := sInf {k : ℕ | IsEdgeColorable G k}

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem edgeColorable_card_edgeSet [Fintype G.edgeSet] :
    IsEdgeColorable G (Fintype.card G.edgeSet) :=
  ⟨⟨Fintype.equivFin G.edgeSet, fun _ _ hne _ heq => hne ((Fintype.equivFin G.edgeSet).injective heq)⟩⟩

theorem degree_le_of_edgeColoring {k : ℕ} (c : EdgeColoring G k) (v : V) : G.degree v ≤ k := by
  have h_inj : Function.Injective (fun e : G.incidenceSet v => c.color ⟨e.val, e.prop.1⟩) := by
    intro e₁ e₂ heq
    by_contra hne
    have he_ne : (⟨e₁.val, e₁.prop.1⟩ : G.edgeSet) ≠ ⟨e₂.val, e₂.prop.1⟩ := by
      intro h_eq
      have h_val : e₁.val = e₂.val := by injection h_eq
      exact hne (Subtype.ext h_val)
    exact c.proper he_ne ⟨v, e₁.prop.2, e₂.prop.2⟩ heq
  have h_le := Fintype.card_le_of_injective _ h_inj
  rwa [SimpleGraph.card_incidenceSet_eq_degree, Fintype.card_fin] at h_le

theorem maxDegree_le_of_edgeColorable {k : ℕ} (h : IsEdgeColorable G k) : G.maxDegree ≤ k := by
  obtain ⟨c⟩ := h
  rw [SimpleGraph.maxDegree, WithBot.unbotD_le_iff (fun _ => Nat.zero_le k), Finset.max_le_iff]
  intro a ha; obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp ha
  exact WithBot.coe_le_coe.mpr (degree_le_of_edgeColoring G c v)

/-- Every vertex of degree $d$ has $d$ incident edges that pairwise share a vertex,
providing the trivial lower bound $\chi'(G) \ge \Delta(G)$. -/
theorem chromatic_index_ge_maxDegree [Fintype G.edgeSet] : G.maxDegree ≤ chromaticIndex G :=
  le_csInf ⟨_, edgeColorable_card_edgeSet G⟩ fun _ hk => maxDegree_le_of_edgeColorable G hk

/-! ### Partial Edge Colorings and Kempe Chains -/

/-- A partial proper edge coloring of $G$ using $k$ colors. -/
structure PartialEdgeColoring (k : ℕ) where
  color : G.edgeSet → Option (Fin k)
  proper : ∀ ⦃e₁ e₂ : G.edgeSet⦄, e₁ ≠ e₂ → ShareVertex G e₁ e₂ →
    ∀ ⦃col : Fin k⦄, color e₁ = some col → color e₂ = some col → False

namespace PartialEdgeColoring

variable {G} {k : ℕ} (c : PartialEdgeColoring G k)

/-- The set of uncolored edges under partial coloring `c`. -/
def uncoloredEdges : Finset G.edgeSet := Finset.univ.filter (fun e => c.color e = none)

/-- The empty partial edge coloring (no edges colored). -/
def empty : PartialEdgeColoring G k where
  color _ := none
  proper _ _ _ _ _ h := by cases h

/-- The color assigned to adjacent vertices $u$ and $v$ (if colored). -/
def colorOf (u v : V) (h : G.Adj u v) : Option (Fin k) := c.color ⟨s(u, v), h⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma colorOf_symm (u v : V) (h : G.Adj u v) : c.colorOf v u h.symm = c.colorOf u v h := by
  dsimp [colorOf]; rw [mk_edge_symm G h]

/-- The set of colors present on edges incident to $v$. -/
def usedColors (v : V) : Finset (Fin k) :=
  Finset.univ.filter (fun col => ∃ (w : V) (h : G.Adj v w), c.colorOf v w h = some col)

/-- The set of colors missing at vertex $v$. -/
def missingColors (v : V) : Finset (Fin k) := Finset.univ \ c.usedColors v

omit [DecidableEq V] in
@[simp] theorem mem_usedColors_iff (v : V) (col : Fin k) :
    col ∈ c.usedColors v ↔ ∃ (w : V) (h : G.Adj v w), c.colorOf v w h = some col := by simp [usedColors]

omit [DecidableEq V] in
@[simp] theorem mem_missingColors_iff (v : V) (col : Fin k) :
    col ∈ c.missingColors v ↔ ∀ (w : V) (h : G.Adj v w), c.colorOf v w h ≠ some col := by simp [missingColors]

omit [Fintype V] [DecidableRel G.Adj] in
lemma colorOf_inj_neighbor (u v w : V) (hv : G.Adj u v) (hw : G.Adj u w) (col : Fin k)
    (h1 : c.colorOf u v hv = some col) (h2 : c.colorOf u w hw = some col) : v = w := by
  by_contra hne
  have he_ne : (⟨s(u, v), hv⟩ : G.edgeSet) ≠ ⟨s(u, w), hw⟩ := by
    intro heq
    rcases Sym2.eq_iff.mp (Subtype.ext_iff.mp heq) with ⟨-, rfl⟩ | ⟨rfl, rfl⟩
    · exact hne rfl
    · exact hv.ne rfl
  exact c.proper he_ne ⟨u, Sym2.mem_mk_left u v, Sym2.mem_mk_left u w⟩ h1 h2

noncomputable def neighborOfColor (u : V) (col : Fin k) : V :=
  if h : col ∈ c.usedColors u then Classical.choose (c.mem_usedColors_iff u col |>.mp h) else u

omit [DecidableEq V] in
lemma neighborOfColor_spec (u : V) {col : Fin k} (h : col ∈ c.usedColors u) :
    ∃ h' : G.Adj u (c.neighborOfColor u col), c.colorOf u (c.neighborOfColor u col) h' = some col := by
  dsimp [neighborOfColor]; split_ifs; exact Classical.choose_spec (c.mem_usedColors_iff u col |>.mp h)

omit [DecidableEq V] in
lemma neighborOfColor_inj (u : V) : Set.InjOn (c.neighborOfColor u) (c.usedColors u : Set (Fin k)) := by
  intro c1 hc1 c2 hc2 heq
  obtain ⟨h1, hc1'⟩ := c.neighborOfColor_spec u (Finset.mem_coe.mp hc1)
  obtain ⟨h2, hc2'⟩ := c.neighborOfColor_spec u (Finset.mem_coe.mp hc2)
  dsimp [colorOf] at hc1' hc2'
  have he : (⟨s(u, c.neighborOfColor u c1), h1⟩ : G.edgeSet) = ⟨s(u, c.neighborOfColor u c2), h2⟩ := by ext; simp [heq]
  exact Option.some.inj (hc1'.symm.trans (he ▸ hc2'))

omit [DecidableEq V] in
theorem card_usedColors_le_degree (u : V) : (c.usedColors u).card ≤ G.degree u := by
  have h_maps : Set.MapsTo (c.neighborOfColor u) (c.usedColors u : Set (Fin k)) (G.neighborFinset u : Set V) := by
    intro col hcol; obtain ⟨h', -⟩ := c.neighborOfColor_spec u (Finset.mem_coe.mp hcol)
    exact Finset.mem_coe.mpr ((G.mem_neighborFinset u _).mpr h')
  have h_le := Finset.card_le_card_of_injOn (c.neighborOfColor u) h_maps (c.neighborOfColor_inj u)
  rwa [G.card_neighborFinset_eq_degree u] at h_le

theorem card_usedColors_le_of_uncolored {u v : V} (h : G.Adj u v) (h_none : c.colorOf u v h = none) :
    (c.usedColors u).card ≤ G.maxDegree - 1 := by
  have h_maps : Set.MapsTo (c.neighborOfColor u) (c.usedColors u : Set (Fin k)) ((G.neighborFinset u).erase v : Set V) := by
    intro col hcol
    obtain ⟨h', hc'⟩ := c.neighborOfColor_spec u (Finset.mem_coe.mp hcol)
    have hne : c.neighborOfColor u col ≠ v := by
      intro heq
      have : c.colorOf u v (heq ▸ h') = some col := heq ▸ hc'
      rw [show c.colorOf u v (heq ▸ h') = c.colorOf u v h from rfl, h_none] at this
      cases this
    exact Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hne, (G.mem_neighborFinset u _).mpr h'⟩)
  have h_le := Finset.card_le_card_of_injOn (c.neighborOfColor u) h_maps (c.neighborOfColor_inj u)
  have hv_mem : v ∈ G.neighborFinset u := (G.mem_neighborFinset u _).mpr h
  rw [Finset.card_erase_of_mem hv_mem, G.card_neighborFinset_eq_degree u] at h_le
  exact h_le.trans (Nat.sub_le_sub_right (G.degree_le_maxDegree u) 1)

theorem card_usedColors_lt_of_uncolored {u v : V} (h : G.Adj u v) (h_none : c.colorOf u v h = none)
    (h_max : G.maxDegree ≤ k) : (c.usedColors u).card < k := by
  have h1 := c.card_usedColors_le_of_uncolored h h_none
  have h2 : 1 ≤ G.degree u := Finset.card_pos.mpr ⟨v, (G.mem_neighborFinset u v).mpr h⟩
  have h3 := G.degree_le_maxDegree u
  omega

omit [DecidableEq V] in
lemma missingColors_nonempty_of_card_lt {u : V} (hlt : (c.usedColors u).card < k) :
    (c.missingColors u).Nonempty := by
  rw [missingColors, Finset.nonempty_iff_ne_empty, ne_eq, Finset.sdiff_eq_empty_iff_subset]
  intro hsub
  have := Finset.card_le_card hsub
  rw [Finset.card_fin] at this
  omega

theorem exists_missingColor_of_uncolored {u v : V} (h : G.Adj u v) (h_none : c.colorOf u v h = none)
    (h_max : G.maxDegree ≤ k) : (c.missingColors u).Nonempty :=
  c.missingColors_nonempty_of_card_lt (c.card_usedColors_lt_of_uncolored h h_none h_max)

omit [DecidableEq V] in
theorem exists_missingColor_of_maxDegree_lt {u : V} (h_max : G.maxDegree < k) :
    (c.missingColors u).Nonempty := by
  have hdeg := c.card_usedColors_le_degree u
  have hmax := G.degree_le_maxDegree u
  exact c.missingColors_nonempty_of_card_lt (by omega)

end PartialEdgeColoring

end SimpleGraph
