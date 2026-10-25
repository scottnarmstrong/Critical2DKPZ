/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonFiniteArrayClt
public import Critical2DKPZ.Extensions.ScaleLimit.ArrayMoments
import Mathlib.Tactic

/-! # Finite-row fourth-moment CLT including the degenerate Gaussian -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators NNReal

namespace Critical2DKPZ.Extensions.GffTangent

/-- The fourth-moment criterion for finite independent rows, including a
possibly zero limiting variance. -/
theorem tendstoInDistribution_fin_sum_of_variance_fourth
    {κ Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filter κ) [F.IsCountablyGenerated] (n : κ → ℕ)
    (Y : (k : κ) → Fin (n k) → Ω → ℝ) (v : ℝ≥0)
    (hind : ∀ k, iIndepFun (Y k) P)
    (hm : ∀ k i, AEMeasurable (Y k i) P)
    (hmem : ∀ k i, MemLp (Y k i) 4 P)
    (hmean : ∀ k i, (∫ ω, Y k i ω ∂P) = 0)
    (hvar : Tendsto (fun k => ∑ i, ∫ ω, Y k i ω ^ 2 ∂P) F (𝓝 (v : ℝ)))
    (hfourth : Tendsto (fun k => ∑ i, ∫ ω, Y k i ω ^ 4 ∂P) F (𝓝 0)) :
    TendstoInDistribution (fun k ω => ∑ i, Y k i ω)
      F id (fun _ => P) (gaussianReal 0 v) := by
  by_cases hv : v = 0
  · subst v
    have hsum (k : κ) : MemLp (fun ω => ∑ i, Y k i ω) 2 P :=
      memLp_finsetSum _ (fun i _ => (hmem k i).mono_exponent (by norm_num))
    have hzero := ScaleLimit.tendstoInMeasure_zero_of_integral_sq P F
      (fun k ω => ∑ i, Y k i ω) hsum (by
        simpa only [ScaleLimit.integral_sq_sum_indep_centered P _ _ (hind _)
          (fun i _ => (hmem _ i).mono_exponent (by norm_num))
          (fun i _ => hmean _ i), NNReal.coe_zero] using hvar)
    have hzlaw := hzero.tendstoInDistribution_of_aemeasurable
      (fun k => (hsum k).aemeasurable) measurable_const.aemeasurable
    have hmap : P.map (fun _ : Ω => (0 : ℝ)) = (gaussianReal 0 0).map id := by
      simp only [gaussianReal_zero_var, Measure.map_id, Measure.map_const, measure_univ, one_smul]
    refine ⟨fun k => (hsum k).aemeasurable, measurable_id.aemeasurable, ?_⟩
    simpa only [hmap] using hzlaw.tendsto
  · have hvpos : 0 < (v : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
    have hs := Real.sqrt_pos.mpr hvpos
    have hs2 : Real.sqrt (v : ℝ) ^ 2 = (v : ℝ) := Real.sq_sqrt v.coe_nonneg
    exact tendstoInDistribution_fin_sum_of_fourth_moments P F n Y v (Real.sqrt v)
      hs hs2 hind hm hmem hmean (by simpa only [hs2] using hvar) hfourth

end Critical2DKPZ.Extensions.GffTangent
