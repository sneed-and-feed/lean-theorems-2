import Formalization.BrooksTheorem.Basic
import Formalization.BrooksTheorem.OddCycles
import Formalization.BrooksTheorem.Greedy

namespace BrooksTheorem

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Brooks' Theorem for small graphs ($|V| \le \Delta + 1$):**
    Any graph on at most $\Delta + 1$ vertices with $\Delta \ge 1$ that is not
    a complete graph $K_{\Delta+1}$ is $\Delta$-colorable. -/
theorem brooks_theorem_of_card_le_succ (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_deg_pos : 1 ≤ maxDegree G)
    (h_card : Fintype.card V ≤ maxDegree G + 1)
    (h_not_clique : ¬ (IsCompleteGraph G ∧ Fintype.card V = maxDegree G + 1)) :
    IsKColorable G (maxDegree G) := by
  rcases lt_or_eq_of_le h_card with h_lt | h_eq
  · have : Fintype.card V ≤ maxDegree G := by omega
    exact isKColorable_of_card_le G (maxDegree G) this
  · have h_not_comp : ¬ IsCompleteGraph G := by
      intro h_comp
      exact h_not_clique ⟨h_comp, h_eq⟩
    exact isKColorable_of_card_eq_succ_not_complete G h_deg_pos h_eq h_not_comp

end BrooksTheorem
