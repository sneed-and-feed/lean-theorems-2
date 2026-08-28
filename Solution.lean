import Formalization.VizingsTheorem.Basic
import Formalization.VizingsTheorem.Kempe
import Formalization.VizingsTheorem.Bipartite
import Formalization.VizingsTheorem.Fan
import Formalization.VizingsTheorem

open scoped BigOperators
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
