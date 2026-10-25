/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonScalarLatticeClt
public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonParameters
public import Critical2DKPZ.Extensions.GffTangent.FlowMartingale
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! # The scalar lattice CLT in the defining SHF normalization -/

@[expose] public noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators NNReal

namespace Critical2DKPZ.Extensions.GffTangent

/-- A flat rescaled pairing is exactly its finite cell sum. -/
theorem integral_rescaledP2Plane_eq_cell_sum (ϑ : ℝ) (N : ℕ) (T : ℝ)
    (f : TestFn) (ω : Disorder) :
    (∫ x, f x * rescaledP2Plane ϑ N 0 T x ω) =
      ∑ w ∈ fixedHorizonCellSites N f, signedCellProfile N f w *
        pointToPlane (criticalBeta ϑ N) 0 (evenCeil ((N : ℝ) * T)) w ω := by
  simp only [rescaledP2Plane, mul_zero, evenCeil_zero, Nat.sub_zero]
  rw [integral_latticeStep_mul_eq_tsum_cell N f f.continuous f.hasCompactSupport
    (fun w => pointToPlane (criticalBeta ϑ N) 0 (evenCeil ((N : ℝ) * T)) w ω)]
  apply tsum_eq_sum
  intro w hw
  have hz : signedCellProfile N f w = 0 := by
    apply abs_eq_zero.mp
    apply le_antisymm _ (abs_nonneg _)
    simpa only [signedCellProfile, absoluteCellProfile_zero_of_not_mem N f hw] using
      abs_integral_cell_le_absoluteCellProfile N f w
  rw [show (∫ x in cell N w, f x) = 0 from hz, zero_mul]

/-- Mean-zero tests identify the centered finite entrance variable with the
unmodified flat-terminal pairing in the definition of the SHF limit. -/
theorem finiteEntranceFluctuation_eq_sqrt_rescaled (l : ℝ) (N : ℕ) (T : ℝ)
    (f : TestFn) (hf : (∫ x : Plane, f x) = 0) (ω : Disorder) :
    finiteEntranceFluctuation (criticalBeta (-l) N) (Real.sqrt l) 0
      (evenCeil ((N : ℝ) * T)) (fixedHorizonCellSites N f) (signedCellProfile N f) ω =
      Real.sqrt l * ∫ x, f x * rescaledP2Plane (-l) N 0 T x ω := by
  rw [integral_rescaledP2Plane_eq_cell_sum]
  unfold finiteEntranceFluctuation
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, sum_signedCellProfile, hf, sub_zero]

/-- The moving critical beta is eventually positive in the actual
quasi-critical regime. -/
theorem eventually_quasiCritical_criticalBeta_pos (l : ℕ → ℝ)
    (hl : Tendsto l atTop atTop)
    (hratio : Tendsto (fun N => l N / Real.log (N : ℝ)) atTop (𝓝 0)) :
    ∀ᶠ N : ℕ in atTop, 0 < criticalBeta (-l N) N := by
  have hσ : ∀ᶠ N : ℕ in atTop,
      Polymer.sigmaSq (criticalBeta (-l N) N) = criticalSigmaSq (-l N) N := by
    simpa only [Polymer.sigmaSq] using eventually_criticalBeta_spec_neg_moving l hl hratio
  filter_upwards [hσ, eventually_ge_atTop 2,
    hratio.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with N hσN hN hsmall
  have hnum : 0 < 1 + -l N / Real.log (N : ℝ) := by
    simpa only [neg_div, sub_eq_add_neg] using sub_pos.mpr hsmall
  have hspos : 0 < criticalSigmaSq (-l N) N :=
    div_pos hnum (replicaOverlap_pos (by omega))
  have hb0 : 0 ≤ criticalBeta (-l N) N := Real.sqrt_nonneg _
  have hbne : criticalBeta (-l N) N ≠ 0 := by
    intro he
    rw [he, Polymer.sigmaSq] at hσN
    norm_num only [zero_pow (by decide : 2 ≠ 0), Real.exp_zero, sub_self] at hσN
    exact hspos.ne' hσN.symm
  exact lt_of_le_of_ne hb0 (Ne.symm hbne)

/-- The scalar CCR limit for the exact rescaled flat-terminal pairing used
by `IsCriticalSHF`, at every positive fixed horizon. -/
theorem tendstoInDistribution_sqrt_rescaledP2Plane
    (l : ℕ → ℝ) (hl : Tendsto l atTop atTop)
    (hratio : Tendsto (fun N => l N / Real.log (N : ℝ)) atTop (𝓝 0))
    {T : ℝ} (hT : 0 < T) (f : TestFn) (hf : (∫ x : Plane, f x) = 0) :
    TendstoInDistribution (fun N ω => Real.sqrt (l N) *
      ∫ x, f x * rescaledP2Plane (-l N) N 0 T x ω) atTop id
      (fun _ => disorderLaw) (gaussianReal 0 (Real.toNNReal
        (4 * Real.pi * ∫ t in Ioo 0 T, ∫ p : Plane × Plane,
          f p.1 * f p.2 * heatKernel (2 * t) (p.2 - p.1) ∂(volume.prod volume)))) := by
  have hσ : ∀ᶠ N : ℕ in atTop,
      Polymer.sigmaSq (criticalBeta (-l N) N) = criticalSigmaSq (-l N) N := by
    simpa only [Polymer.sigmaSq] using eventually_criticalBeta_spec_neg_moving l hl hratio
  have hn := SHF.Moments.tendsto_evenCeil_div T hT.le
  have hclt := tendstoInDistribution_sqrt_finiteEntranceFluctuation l
    (fun N => criticalBeta (-l N) N) hl hratio (eventually_quasiCritical_criticalBeta_pos l hl hratio)
    hσ (fun N => evenCeil ((N : ℝ) * T)) hT hn f
  exact hclt.congr (fun N => Eventually.of_forall (fun ω =>
    finiteEntranceFluctuation_eq_sqrt_rescaled (l N) N T f hf ω)) (Eventually.of_forall (fun _ => rfl))

end Critical2DKPZ.Extensions.GffTangent
