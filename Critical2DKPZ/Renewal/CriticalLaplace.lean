/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Renewal.LaplaceNormalization
public import Critical2DKPZ.Renewal.GeneratingFunction

/-! # Laplace convergence of the critical renewal measure

The discrete geometric resolvent and the summable local central limit error yield the
Laplace limit `1 / (log a + γ - ϑ)` for the period-two return weights. -/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace Critical2DKPZ.Renewal

/-- The generating variable at the macroscopic lattice scale. -/
def dampingBase (a : ℝ) (N : ℕ) : ℝ := Real.exp (-a / (N + 1))

/-- Powers of the damping base equal the corresponding exponential damping factor. -/
theorem dampingBase_pow (a : ℝ) (N n : ℕ) :
    dampingBase a N ^ n = Real.exp (-a * n / (N + 1)) := by
  rw [dampingBase, ← Real.exp_nat_mul]
  congr 1
  ring

/-- The positive-step generating function is precisely the damped collision return sum. -/
theorem hasSum_weightedStep_critical (ϑ : ℝ) (a : {a : ℝ // 0 < a}) (N : ℕ) :
    HasSum (weightedStep (fun r => criticalSigmaSq ϑ N * returnWeight r) (dampingBase a N))
      (criticalSigmaSq ϑ N * dampedReturnSum a N) := by
  have h := ((hasSum_damped_return a N).mul_left (criticalSigmaSq ϑ N))
  rw [← dampedReturnSum_eq] at h
  have htail : HasSum (fun n => weightedStep
      (fun r => criticalSigmaSq ϑ N * returnWeight r) (dampingBase a N) (n + 1))
      (criticalSigmaSq ϑ N * dampedReturnSum a N) := by
    apply h.congr_fun
    intro n
    simp only [weightedStep, Nat.add_one_ne_zero, ↓reduceIte, dampingBase_pow,
      dampingFactor, Nat.cast_add, Nat.cast_one]
    ring
  rw [← hasSum_nat_add_iff' 1]
  simpa only [Finset.sum_range_one, weightedStep, ↓reduceIte, sub_zero] using htail

/-- The logarithmic critical gap has the Euler-shifted continuum normalization. -/
theorem tendsto_log_mul_critical_gap (ϑ : ℝ) (a : {a : ℝ // 0 < a}) :
    Tendsto (fun N : ℕ => Real.log N *
      (1 - criticalSigmaSq ϑ N * dampedReturnSum a N)) atTop
      (nhds (Real.log a + Real.eulerMascheroniConstant - ϑ)) := by
  have h := (tendsto_sigma_mul_log ϑ).mul (tendsto_dampedReturnSum_sub_overlap a)
  have h' := (tendsto_const_nhds (x := -ϑ)).sub h
  have hlimit : -ϑ - Real.pi *
      (-(Real.log a + Real.eulerMascheroniConstant) / Real.pi) =
      Real.log a + Real.eulerMascheroniConstant - ϑ := by
    field_simp
    ring
  rw [hlimit] at h'
  apply h'.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  have heq := criticalSigmaSq_mul_overlap ϑ (N := N) (by omega)
  have hcancel : Real.log N * (criticalSigmaSq ϑ N * replicaOverlap N - 1) = ϑ := by
    rw [heq]
    field_simp
    ring
  nlinarith only [hcancel]

/-- The damped critical renewal kernel is eventually subcritical. -/
theorem eventually_critical_damped_subcritical (ϑ : ℝ) (a : {a : ℝ // 0 < a})
    (ha : ϑ < Real.log a + Real.eulerMascheroniConstant) :
    ∀ᶠ N : ℕ in atTop, criticalSigmaSq ϑ N * dampedReturnSum a N < 1 := by
  filter_upwards [(tendsto_log_mul_critical_gap ϑ a).eventually
    (eventually_gt_nhds (sub_pos.mpr ha)),
    eventually_ge_atTop 2] with N h hN
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  exact sub_pos.mp ((mul_pos_iff_of_pos_left hlog).mp h)

/-- The whole critical renewal mass has a finite Laplace transform above its critical abscissa. -/
theorem eventually_hasSum_damped_criticalRenewalMass (ϑ : ℝ) (a : {a : ℝ // 0 < a})
    (ha : ϑ < Real.log a + Real.eulerMascheroniConstant) :
    ∀ᶠ N : ℕ in atTop, HasSum
      (fun n => criticalRenewalMass ϑ N n * Real.exp (-a * n / (N + 1)))
      (1 / (1 - criticalSigmaSq ϑ N * dampedReturnSum a N)) := by
  filter_upwards [criticalSigmaSq_eventually_pos ϑ,
    eventually_critical_damped_subcritical ϑ a ha] with N hσ hsub
  have hs := hasSum_weightedStep_critical ϑ a N
  have hw : ∀ r, 0 ≤ criticalSigmaSq ϑ N * returnWeight r :=
    fun r => mul_nonneg hσ.le (srwKernel_nonneg _ _)
  have h := hasSum_weighted_renewalMass (w := fun r => criticalSigmaSq ϑ N * returnWeight r)
    (ρ := dampingBase a N) hw (Real.exp_pos _).le hs.summable (by rwa [hs.tsum_eq])
  simpa only [criticalRenewalMass, dampingBase_pow, hs.tsum_eq] using h

/-- Laplace convergence with the normalization fixed by the critical variance. -/
theorem tendsto_damped_criticalRenewalMass (ϑ : ℝ) (a : {a : ℝ // 0 < a})
    (ha : ϑ < Real.log a + Real.eulerMascheroniConstant) :
    Tendsto (fun N : ℕ => (∑' n, criticalRenewalMass ϑ N n *
      Real.exp (-a * n / (N + 1))) / Real.log N) atTop
      (nhds (1 / (Real.log a + Real.eulerMascheroniConstant - ϑ))) := by
  have h := (tendsto_log_mul_critical_gap ϑ a).inv₀ (sub_pos.mpr ha).ne'
  rw [one_div]
  apply h.congr'
  filter_upwards [eventually_hasSum_damped_criticalRenewalMass ϑ a ha] with N hN
  rw [hN.tsum_eq]
  simp only [mul_inv_rev, div_eq_mul_inv, one_mul]

end Critical2DKPZ.Renewal

end
