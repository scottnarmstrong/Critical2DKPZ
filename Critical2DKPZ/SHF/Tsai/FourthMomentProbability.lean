/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConvergenceApproximation

/-! # Vanishing fourth moments imply convergence in probability

Markov's inequality applies directly to the integrable nonnegative fourth
powers. No extra measurability hypothesis is imposed on the signed errors.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Tsai

/-- Integrable fourth-power errors with vanishing expectations give convergence in measure. -/
theorem tendstoInMeasure_of_integrable_fourth_moments {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hI : ∀ n, Integrable (fun ω => (f n ω - g ω) ^ 4) P)
    (hlim : Tendsto (fun n => ∫ ω, (f n ω - g ω) ^ 4 ∂P) atTop (𝓝 0)) :
    TendstoInMeasure P f atTop g := by
  rw [tendstoInMeasure_iff_measureReal_dist]
  intro ε hε
  have hbound (n) : P.real {ω | ε ≤ dist (f n ω) (g ω)} ≤
      (∫ ω, (f n ω - g ω) ^ 4 ∂P) / ε ^ 4 := by
    have hMarkov := mul_meas_ge_le_integral_of_nonneg
      (Eventually.of_forall (fun ω => (show Even 4 from ⟨2, rfl⟩).pow_nonneg (f n ω - g ω)))
      (hI n) (ε ^ 4)
    have hset : {ω | ε ≤ dist (f n ω) (g ω)} ⊆ {ω | ε ^ 4 ≤ (f n ω - g ω) ^ 4} := by
      intro ω hω
      change ε ≤ dist (f n ω) (g ω) at hω
      rw [Real.dist_eq] at hω
      change ε ^ 4 ≤ (f n ω - g ω) ^ 4
      simpa only [Even.pow_abs (show Even 4 from ⟨2, rfl⟩)] using
        pow_le_pow_left₀ hε.le hω 4
    apply (le_div_iff₀ (pow_pos hε 4)).2
    calc
      _ ≤ ε ^ 4 * P.real {ω | ε ^ 4 ≤ (f n ω - g ω) ^ 4} := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (measureReal_mono hset) (pow_nonneg hε.le _)
      _ ≤ _ := hMarkov
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [zero_div] using hlim.div_const (ε ^ 4)) (fun _ => measureReal_nonneg) hbound

end Critical2DKPZ.SHF.Tsai

end
