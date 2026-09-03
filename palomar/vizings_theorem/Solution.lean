import Formalization.VizingsTheorem.Basic
import Formalization.VizingsTheorem.Kempe
import Formalization.VizingsTheorem.Bipartite
import Formalization.VizingsTheorem.Fan
import Formalization.VizingsTheorem

open scoped BigOperators
open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
