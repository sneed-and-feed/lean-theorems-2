import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

open Finset SimpleGraph

/-!
# Brooks' Theorem — Basic Definitions & Colorability Predicates

This module provides foundational definitions for the formalization of Brooks' Theorem (1941):
- Maximum degree $\Delta(G)$ (`maxDegree`) and its bound on vertex degrees (`degree_le_maxDegree`).
- Proper vertex colorings (`IsProperColoring`) and $k$-colorability (`IsKColorable`).
- Bridge to Mathlib's native `SimpleGraph.Colorable` (`isKColorable_iff_colorable`).
- Monotonicity of $k$-colorability (`isKColorable_mono`).
-/

namespace BrooksTheorem

variable {V : Type*}

section MaxDeg
variable [Fintype V]

/-- Maximum degree $\Delta(G)$ of a finite graph $G$. -/
def maxDegree (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.univ.sup (fun v => G.degree v)

lemma degree_le_maxDegree (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    G.degree v ≤ maxDegree G :=
  Finset.le_sup (f := fun u => G.degree u) (Finset.mem_univ v)

end MaxDeg

/-- Predicate asserting that coloring `c` is a proper vertex coloring of `G`. -/
def IsProperColoring (G : SimpleGraph V) {k : ℕ} (c : V → Fin k) : Prop :=
  ∀ u v : V, G.Adj u v → c u ≠ c v

/-- Predicate asserting that graph `G` is `k`-colorable ($\chi(G) \le k$). -/
def IsKColorable (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : V → Fin k, IsProperColoring G c

/-- Bridge between `IsKColorable G k` and Mathlib's native `G.Colorable k`. -/
lemma isKColorable_iff_colorable (G : SimpleGraph V) (k : ℕ) :
    IsKColorable G k ↔ G.Colorable k := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨SimpleGraph.Coloring.mk c (fun hadj => hc _ _ hadj)⟩
  · rintro ⟨C⟩
    exact ⟨C.toFun, fun u v hadj => C.valid hadj⟩

/-- Monotonicity of colorability: if $G$ is $k$-colorable, it is also $m$-colorable for any $m \ge k$. -/
lemma isKColorable_mono (G : SimpleGraph V) {k m : ℕ} (hkm : k ≤ m) (h : IsKColorable G k) :
    IsKColorable G m := by
  obtain ⟨c, hc⟩ := h
  refine ⟨fun v => (c v).castLE hkm, ?_⟩
  intro u v hadj heq
  have hc_ne := hc u v hadj
  dsimp at heq
  have h_val : ((c u).castLE hkm : ℕ) = ((c v).castLE hkm : ℕ) := congrArg Fin.val heq
  have : c u = c v := Fin.ext h_val
  exact hc_ne this

end BrooksTheorem
