import Formalization.StanleySL2
import Formalization.VizingsTheorem
import Formalization.BirkhoffVonNeumann
import Formalization.IharaBass
import Formalization.IharaZeta
import Formalization.MacMahonsMasterTheorem
import Formalization.FishersInequality
import Formalization.KonigMatching
import Formalization.SpernerAntichain
import Formalization.TuransTheorem
import Formalization.VanDerWaerden
import Formalization.BlichfeldtsTheorem
import Formalization.JungsTheorem
import Formalization.GesselViennot
import Formalization.CayleysFormula
import Formalization.CirculantSpectralTheory
import Formalization.HoffmanSingleton
import Formalization.BrooksTheorem
import Formalization.MatrixTreeTheorem
import Formalization.MengersTheorem
import Formalization.RamanujanTau

/-!
# Root Formalization Library: Repo 2
Imports all verified Tier-1 Palomar submission packages and active research scaffolds.
Retired and superseded theories are decoupled below to ensure minimal compilation overhead,
shield against upstream Mathlib drift, and preserve complete audit integrity.
-/

-- ==============================================================================
-- 🛑 Decoupled Retired & Superseded Theories (Archived in Place for Audit Integrity)
-- ==============================================================================
-- import Formalization.PrefixSparsity    -- Retired: AP-18, AP-26 (Trivial finite function arithmetic)
-- import Formalization.CyclicShift       -- Superseded: Class A package replaced by CirculantSpectralTheory
-- import Formalization.RSKBijection      -- Retired: AP-01 (Tautological hypothesis projection)
