import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open PowerSeries

/-!
# Ramanujan Tau Function and Congruence Modulo 691
-/

noncomputable def X_series : PowerSeries ℤ := X

noncomputable def ramanujan_trunc (N : ℕ) : PowerSeries ℤ :=
  (Finset.range N).prod (fun n => (1 - (X_series ^ (n + 1))) ^ 24)

noncomputable def ramanujanTau (n : ℕ) : ℤ :=
  coeff n (X_series * ramanujan_trunc n)

def divisor_sum_11 (n : ℕ) : ℤ :=
  (Finset.filter (fun d => n % d = 0) (Finset.Icc 1 n)).sum (fun d => (d : ℤ) ^ 11)

def ramanujan_congruence_691 (n : ℕ) : Prop :=
  (ramanujanTau n - divisor_sum_11 n) % 691 = 0

def q_add (p q : ℤ × ℕ) : ℤ × ℕ := (p.1 * (q.2 : ℤ) + q.1 * (p.2 : ℤ), p.2 * q.2)
def q_sub (p q : ℤ × ℕ) : ℤ × ℕ := (p.1 * (q.2 : ℤ) - q.1 * (p.2 : ℤ), p.2 * q.2)
def q_mul (p q : ℤ × ℕ) : ℤ × ℕ := (p.1 * q.1, p.2 * q.2)

def q_bernoulli_seq : ℕ → List (ℤ × ℕ)
  | 0 => [(1, 1)]
  | n + 1 =>
    let prev := q_bernoulli_seq n
    let sum_term := (List.range (n + 1)).foldl (fun (acc : ℤ × ℕ) (k : ℕ) =>
      let b_k := prev.getD k (0, 1)
      let coeff := ((Nat.choose (n + 1) k : ℤ), n + 1 - k + 1)
      q_add acc (q_mul coeff b_k)) (0, 1)
    let next_b := q_sub (1, 1) sum_term
    prev ++ [next_b]

def q_bernoulli (n : ℕ) : ℤ × ℕ :=
  (q_bernoulli_seq n).getD n (0, 1)

def q_eq (p q : ℤ × ℕ) : Bool :=
  p.1 * (q.2 : ℤ) == q.1 * (p.2 : ℤ)

theorem bernoulli_12_exact : q_eq (q_bernoulli 12) (-691, 2730) = true := by
  decide

noncomputable def E_12 : PowerSeries ℚ :=
  PowerSeries.mk fun n => if n = 0 then 1 else (65520 / 691) * (divisor_sum_11 n : ℚ)

noncomputable def Delta_Q : PowerSeries ℚ :=
  PowerSeries.mk fun n => (ramanujanTau n : ℚ)

section ModForms

variable (M_12 : Set (PowerSeries ℚ))

theorem ramanujan_tau_congruence
    (F_exists : ∃ (F_int : PowerSeries ℤ),
      (PowerSeries.map (algebraMap ℤ ℚ) F_int) ∈ M_12 ∧
      coeff 0 F_int = 1 ∧
      coeff 1 F_int = 720)
    (M_12_is_span : ∀ (f : PowerSeries ℚ), f ∈ M_12 → ∃ a b : ℚ, f = a • E_12 + b • Delta_Q)
    (tau_zero : ramanujanTau 0 = 0)
    (tau_one : ramanujanTau 1 = 1)
    (divisor_sum_11_one : divisor_sum_11 1 = 1)
    (n : ℕ) (hn : n > 0) : ramanujan_congruence_691 n := by
  rcases F_exists with ⟨F_int, hF_M12, hF_0, hF_1⟩
  rcases M_12_is_span _ hF_M12 with ⟨a, b, h_span⟩
  
  have ha : a = 1 := by
    have h := congr_arg (coeff 0) h_span
    simp [E_12, Delta_Q, tau_zero, hF_0, coeff_map] at h
    exact h.symm

  have hb : b = 432000 / 691 := by
    have h := congr_arg (coeff 1) h_span
    simp [E_12, Delta_Q, tau_one, divisor_sum_11_one, hF_1, ha, coeff_map] at h
    linarith

  have hn_eq := congr_arg (coeff n) h_span
  simp [E_12, Delta_Q, ne_of_gt hn, ha, hb, coeff_map] at hn_eq
  
  have h_clear : (691 : ℚ) * ((coeff n F_int : ℤ) : ℚ) = 65520 * (divisor_sum_11 n : ℚ) + 432000 * (ramanujanTau n : ℚ) := by
    calc (691 : ℚ) * ((coeff n F_int : ℤ) : ℚ) = 691 * ((65520 / 691) * (divisor_sum_11 n : ℚ) + (432000 / 691) * (ramanujanTau n : ℚ)) := by rw [hn_eq]
         _ = 65520 * (divisor_sum_11 n : ℚ) + 432000 * (ramanujanTau n : ℚ) := by ring
         
  have h_int : (691 * coeff n F_int : ℤ) = 65520 * divisor_sum_11 n + 432000 * ramanujanTau n := by
    exact_mod_cast h_clear

  dsimp [ramanujan_congruence_691]
  omega

end ModForms
