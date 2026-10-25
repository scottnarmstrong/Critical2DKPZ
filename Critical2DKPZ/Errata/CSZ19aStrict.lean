/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Lattice.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.NumberTheory.Harmonic.GammaDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-! # Dickman density and renewal parameter identities -/

public section

open MeasureTheory

namespace Critical2DKPZ.Errata.CSZ19a

open Critical2DKPZ

/-- The real logarithmic derivative of Gamma, used in CSZ19a's optimizer
equation `(log Γ)'(c s̄) = log t + (A/c) θ - γ`. -/
noncomputable def logGammaDeriv (x : ℝ) : ℝ :=
  deriv (fun y : ℝ => Real.log (Real.Gamma y)) x

private theorem logGammaDeriv_one :
    logGammaDeriv 1 = -Real.eulerMascheroniConstant := by
  have hΓ : Real.Gamma 1 ≠ 0 := by rw [Real.Gamma_one]; norm_num
  have h := Real.hasDerivAt_Gamma_one.log hΓ
  have h' : HasDerivAt (fun y : ℝ => Real.log (Real.Gamma y))
      (-Real.eulerMascheroniConstant) 1 := by
    simpa [Real.Gamma_one] using h
  simpa [logGammaDeriv] using h'.deriv

/-- The renewal path has its defining time-zero value. -/
def clockTrajectory (k : ℕ) (_ : Unit) : ℕ := k

/-- A time-zero probability-one event violates the proposed bound at `N = 1` and `t = exp(-2/c)` for every positive `c`. -/
theorem csz19a_04_all_N_tail_bound_false (c : ℝ) (hc : 0 < c) :
    ∃ t : ℝ, 0 < t ∧
      MeasureTheory.Measure.dirac ()
        {ω : Unit | ((clockTrajectory (Nat.floor (1 * Real.log 1)) ω : ℕ) : ℝ) ≤ t * 1} = 1 ∧
      Real.exp (1 - c * 1 * Real.log (1 / t)) < 1 := by
  let t : ℝ := Real.exp (-2 / c)
  have ht : 0 < t := Real.exp_pos _
  have hclock : Nat.floor (1 * Real.log 1) = 0 := by simp
  have hlog : Real.log (1 / t) = 2 / c := by
    dsimp [t]
    rw [one_div, Real.log_inv, Real.log_exp]
    ring
  have hexp : Real.exp (1 - c * 1 * Real.log (1 / t)) = Real.exp (-1) := by
    rw [hlog]
    congr 1
    field_simp [ne_of_gt hc]
    ring
  refine ⟨t, ht, ?_, ?_⟩
  · have hset :
        {ω : Unit | ((clockTrajectory (Nat.floor (1 * Real.log 1)) ω : ℕ) : ℝ) ≤ t * 1} =
          Set.univ := by
      ext ω
      rw [hclock]
      simp [clockTrajectory, ht.le]
    rw [hset]
    simp
  · rw [hexp]
    exact Real.exp_lt_one_iff.mpr (by norm_num)

/-- For simple-random-walk renewal weights at `r = 1` and `N = 2`, a positive probability exceeds the zero logarithmic bound. -/
theorem csz19a_07_log_r_bound_false :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ r N : ℕ, 1 ≤ N → 1 ≤ r → r ≤ N →
      replicaOverlap r / replicaOverlap N ≤ C * Real.log r / Real.log N := by
  rintro ⟨C, hC, hbound⟩
  have hratio := hbound 1 2 (by norm_num) (by norm_num) (by norm_num)
  have hleft : 0 < replicaOverlap 1 / replicaOverlap 2 :=
    div_pos (replicaOverlap_pos (by norm_num)) (replicaOverlap_pos (by norm_num))
  simp only [Nat.cast_one, Real.log_one, mul_zero, zero_div] at hratio
  linarith

/-- At `n = N = 1`, the admissible optimizer equation has a solution exceeding the proposed linear upper bound. -/
theorem csz19a_11_printed_inverse_digamma_bound_false :
    ∃ A c θ sbar : ℝ, ∃ n N : ℕ,
      0 < A ∧ 0 < c ∧ 1 ≤ n ∧ n ≤ N ∧ 1 ≤ N ∧
      logGammaDeriv (c * sbar) =
        Real.log ((n : ℝ) / N) + A / c * θ - Real.eulerMascheroniConstant ∧
      ¬ sbar ≤ A * θ / c - Real.eulerMascheroniConstant := by
  refine ⟨1, 1, 0, 1, 1, 1, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, ?_, ?_⟩
  · rw [one_mul, logGammaDeriv_one]
    norm_num
  · intro hbound
    have hγ := Real.one_half_lt_eulerMascheroniConstant
    norm_num at hbound
    linarith

/-- At `s = 1` and `t = 3/2`, integration of the Dickman density derivative gives a negative contribution from its explicit first branch. -/
theorem csz19a_19_printed_positive_integral_sign_false
    (f : ℝ → ℝ)
    (hbase : ∀ x : ℝ, 0 < x → x ≤ 1 →
      f x = Real.exp (-Real.eulerMascheroniConstant))
    (hzero : ∀ x : ℝ, x < 0 → f x = 0)
    (hderiv : ∀ x ∈ Set.Ioo (1 : ℝ) (3 / 2),
      deriv f x = -f (x - 1) / x)
    (hcont : ContinuousOn f (Set.uIcc (1 : ℝ) (3 / 2)))
    (hdiff : ∀ x ∈ Set.Ioo (1 : ℝ) (3 / 2), DifferentiableAt ℝ f x)
    (hderivInt : IntervalIntegrable (deriv f) volume 1 (3 / 2))
    (hphi01 : IntervalIntegrable (fun u : ℝ => f (u - 1) / u) volume 0 1)
    (hphi1t : IntervalIntegrable (fun u : ℝ => f (u - 1) / u) volume 1 (3 / 2))
    (hprinted : f (3 / 2) - Real.exp (-Real.eulerMascheroniConstant) =
      ∫ u in (0 : ℝ)..(3 / 2), f (u - 1) / u) : False := by
  let K : ℝ := Real.exp (-Real.eulerMascheroniConstant)
  let φ : ℝ → ℝ := fun u => f (u - 1) / u
  have hK : 0 < K := Real.exp_pos _
  have hKf : f 1 = K := by
    dsimp [K]
    exact hbase 1 (by norm_num) (by norm_num)
  have hzero01 : Set.EqOn φ (fun _ => 0) (Set.Ioo (0 : ℝ) 1) := by
    intro u hu
    have hu' := hu
    simp only [Set.mem_Ioo] at hu'
    have hfu : f (u - 1) = 0 := hzero (u - 1) (by linarith)
    simp [φ, hfu]
  have hzeroInt : ∫ u in (0 : ℝ)..1, φ u = 0 := by
    rw [intervalIntegral.integral_congr_Ioo_of_le (by norm_num) hzero01]
    simp
  have hadd := intervalIntegral.integral_add_adjacent_intervals hphi01 hphi1t
  have hprinted' : f (3 / 2) - K = ∫ u in (1 : ℝ)..(3 / 2), φ u := by
    dsimp [φ, K] at hprinted ⊢
    rw [← hadd, hzeroInt] at hprinted
    linarith
  have hderivEq : Set.EqOn (deriv f) (fun u => -φ u)
      (Set.Ioo (1 : ℝ) (3 / 2)) := by
    intro u hu
    rw [hderiv u hu]
    dsimp [φ]
    ring
  have hftc := intervalIntegral.integral_deriv_eq_sub_uIoo
    (f := f) hcont (fun x hx => hdiff x (by
      simpa [Set.uIoo_of_le (by norm_num : (1 : ℝ) ≤ 3 / 2)] using hx)) hderivInt
  rw [intervalIntegral.integral_congr_Ioo_of_le (by norm_num) hderivEq,
    intervalIntegral.integral_neg, hKf] at hftc
  have hφpos : ∀ u : ℝ, u ∈ Set.Ioo (1 : ℝ) (3 / 2) → 0 < φ u := by
    intro u hu
    have hfu : f (u - 1) = K := by
      dsimp [K]
      exact hbase (u - 1) (by linarith [hu.1]) (by linarith [hu.2])
    change 0 < f (u - 1) / u
    rw [hfu]
    exact div_pos hK (by linarith [hu.1])
  have hφintpos := intervalIntegral.intervalIntegral_pos_of_pos_on hphi1t hφpos
    (by norm_num : (1 : ℝ) < 3 / 2)
  linarith

end Critical2DKPZ.Errata.CSZ19a

