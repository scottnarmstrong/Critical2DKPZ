/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.SlabProductsCore
import Mathlib.MeasureTheory.Function.L2Space

/-! # Orthogonal projection with a measurable comparison -/

@[expose] public section

open MeasureTheory

noncomputable section

namespace Critical2DKPZ.SHF.TimeContinuity

/-- If `C` is the conditional expectation of `Y` and `B` is measurable with respect to the same
sigma algebra, then the squared distance from `Y` to `B` splits into the projection loss and the
distance from `C` to `B`. -/
theorem integral_sq_sub_condExp_add_measurable
    {m : MeasurableSpace Disorder} (hm : m ≤ MeasurableSpace.pi)
    {Y C B : Disorder → ℝ}
    (hY : MemLp Y 2 disorderLaw) (hC : MemLp C 2 disorderLaw)
    (hB : MemLp B 2 disorderLaw)
    (hCm : AEStronglyMeasurable[m] C disorderLaw)
    (hBm : AEStronglyMeasurable[m] B disorderLaw)
    (hCce : C =ᵐ[disorderLaw] disorderLaw[Y | m]) :
    Integrable (fun ω => Y ω ^ 2) disorderLaw ∧
    Integrable (fun ω => C ω ^ 2) disorderLaw ∧
    Integrable (fun ω => (C ω - B ω) ^ 2) disorderLaw ∧
    Integrable (fun ω => (Y ω - B ω) ^ 2) disorderLaw ∧
    ∫ ω, (Y ω - B ω) ^ 2 ∂disorderLaw =
      (∫ ω, Y ω ^ 2 ∂disorderLaw - ∫ ω, C ω ^ 2 ∂disorderLaw) +
        ∫ ω, (C ω - B ω) ^ 2 ∂disorderLaw := by
  let H : Disorder → ℝ := fun ω => C ω - B ω
  have hHm : AEStronglyMeasurable[m] H disorderLaw := by
    dsimp [H]
    exact hCm.sub hBm
  have hHLp : MemLp H 2 disorderLaw := by
    dsimp [H]
    exact hC.sub hB
  have hYsq : Integrable (fun ω => Y ω ^ 2) disorderLaw := by
    have h := hY.integrable_norm_pow'
    apply h.congr
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, sq_abs]
  have hCsq : Integrable (fun ω => C ω ^ 2) disorderLaw := by
    have h := hC.integrable_norm_pow'
    apply h.congr
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, sq_abs]
  have hHsq : Integrable (fun ω => H ω ^ 2) disorderLaw := by
    have h := hHLp.integrable_norm_pow'
    apply h.congr
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, sq_abs]
  have hdiffLp : MemLp (fun ω => Y ω - B ω) 2 disorderLaw := hY.sub hB
  have hdiffsq : Integrable (fun ω => (Y ω - B ω) ^ 2) disorderLaw := by
    have h := hdiffLp.integrable_norm_pow'
    apply h.congr
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, sq_abs]
  have hYH : Integrable (fun ω => Y ω * H ω) disorderLaw := hY.integrable_mul hHLp
  have hCH : Integrable (fun ω => C ω * H ω) disorderLaw := hC.integrable_mul hHLp
  let fY : Lp ℝ 2 disorderLaw := hY.toLp Y
  let fH : Lp ℝ 2 disorderLaw := hHLp.toLp H
  have hHmeasLp : AEStronglyMeasurable[m] (fH : Disorder → ℝ) disorderLaw := by
    exact hHm.congr hHLp.coeFn_toLp.symm
  let fC : Lp ℝ 2 disorderLaw := hC.toLp C
  have hCmeasLp : AEStronglyMeasurable[m] (fC : Disorder → ℝ) disorderLaw := by
    exact hCm.congr hC.coeFn_toLp.symm
  have hinner := inner_condExpL2_eq_inner_fun (E := ℝ) (𝕜 := ℝ)
    (m0 := MeasurableSpace.pi) hm fY fH hHmeasLp
  rw [L2.inner_def, L2.inner_def] at hinner
  simp only [Real.inner_apply] at hinner
  have hCE2 := hY.condExpL2_ae_eq_condExp (E := ℝ) (𝕜 := ℝ)
    (m₀ := MeasurableSpace.pi) hm
  have hinnerInt :
      ∫ ω, (condExpL2 ℝ ℝ hm (hY.toLp Y) : Disorder → ℝ) ω * H ω ∂disorderLaw =
        ∫ ω, Y ω * H ω ∂disorderLaw := by
    calc
      _ = ∫ ω, (condExpL2 ℝ ℝ hm (hY.toLp Y) : Disorder → ℝ) ω *
            (hHLp.toLp H) ω ∂disorderLaw := by
          apply integral_congr_ae
          filter_upwards [hHLp.coeFn_toLp] with ω hHω
          rw [hHω]
      _ = ∫ ω, (hY.toLp Y) ω * (hHLp.toLp H) ω ∂disorderLaw := hinner
      _ = ∫ ω, Y ω * H ω ∂disorderLaw := by
          apply integral_congr_ae
          filter_upwards [hY.coeFn_toLp, hHLp.coeFn_toLp] with ω hYω hHω
          rw [hYω, hHω]
  have hinnerC := inner_condExpL2_eq_inner_fun (E := ℝ) (𝕜 := ℝ)
    (m0 := MeasurableSpace.pi) hm fY fC hCmeasLp
  rw [L2.inner_def, L2.inner_def] at hinnerC
  simp only [Real.inner_apply] at hinnerC
  have hinnerCInt :
      ∫ ω, (condExpL2 ℝ ℝ hm (hY.toLp Y) : Disorder → ℝ) ω * C ω ∂disorderLaw =
        ∫ ω, Y ω * C ω ∂disorderLaw := by
    calc
      _ = ∫ ω, (condExpL2 ℝ ℝ hm (hY.toLp Y) : Disorder → ℝ) ω *
            (hC.toLp C) ω ∂disorderLaw := by
          apply integral_congr_ae
          filter_upwards [hC.coeFn_toLp] with ω hCω
          rw [hCω]
      _ = ∫ ω, (hY.toLp Y) ω * (hC.toLp C) ω ∂disorderLaw := hinnerC
      _ = ∫ ω, Y ω * C ω ∂disorderLaw := by
          apply integral_congr_ae
          filter_upwards [hY.coeFn_toLp, hC.coeFn_toLp] with ω hYω hCω
          rw [hYω, hCω]
  have hcrossC : ∫ ω, C ω * C ω ∂disorderLaw =
      ∫ ω, Y ω * C ω ∂disorderLaw := by
    calc
      ∫ ω, C ω * C ω ∂disorderLaw =
          ∫ ω, (disorderLaw[Y | m] : Disorder → ℝ) ω * C ω ∂disorderLaw := by
            apply integral_congr_ae
            filter_upwards [hCce] with ω hω
            rw [hω]
      _ = ∫ ω, (condExpL2 ℝ ℝ hm (hY.toLp Y) : Disorder → ℝ) ω *
            C ω ∂disorderLaw := by
              apply integral_congr_ae
              filter_upwards [hCE2] with ω hω
              rw [hω]
      _ = ∫ ω, Y ω * C ω ∂disorderLaw := hinnerCInt
  have hcrossCZero : ∫ ω, (Y ω - C ω) * C ω ∂disorderLaw = 0 := by
    calc
      ∫ ω, (Y ω - C ω) * C ω ∂disorderLaw =
          ∫ ω, (Y ω * C ω - C ω * C ω) ∂disorderLaw := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun ω => by ring
      _ = ∫ ω, Y ω * C ω ∂disorderLaw -
            ∫ ω, C ω * C ω ∂disorderLaw :=
              integral_sub (hY.integrable_mul hC) (hC.integrable_mul hC)
      _ = 0 := by rw [hcrossC]; ring
  have hcross : ∫ ω, C ω * H ω ∂disorderLaw =
      ∫ ω, Y ω * H ω ∂disorderLaw := by
    calc
      ∫ ω, C ω * H ω ∂disorderLaw =
          ∫ ω, (disorderLaw[Y | m] : Disorder → ℝ) ω * H ω ∂disorderLaw := by
            apply integral_congr_ae
            filter_upwards [hCce] with ω hω
            rw [hω]
      _ = ∫ ω, (condExpL2 ℝ ℝ hm (hY.toLp Y) : Disorder → ℝ) ω *
            H ω ∂disorderLaw := by
              apply integral_congr_ae
              filter_upwards [hCE2] with ω hω
              rw [hω]
      _ = ∫ ω, Y ω * H ω ∂disorderLaw := hinnerInt
  have hcrossZero : ∫ ω, (Y ω - C ω) * H ω ∂disorderLaw = 0 := by
    have hsub := integral_sub hYH hCH
    rw [hcross] at hsub
    calc
      ∫ ω, (Y ω - C ω) * H ω ∂disorderLaw =
          ∫ ω, (Y ω * H ω - C ω * H ω) ∂disorderLaw := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun ω => by ring
      _ = _ := by rw [hsub]; ring
  refine ⟨hYsq, hCsq, ?_, hdiffsq, ?_⟩
  · simpa only [H] using hHsq
  · have hpoint (ω : Disorder) :
        (Y ω - B ω) ^ 2 = (Y ω - C ω) ^ 2 + H ω ^ 2 +
          2 * ((Y ω - C ω) * H ω) := by
          dsimp [H]
          ring
    have hYC : Integrable (fun ω => (Y ω - C ω) ^ 2) disorderLaw := by
      have h := hY.sub hC
      have hpow := h.integrable_norm_pow'
      convert hpow using 1
      funext ω
      rw [Real.norm_eq_abs, sq_abs]
      rfl
    have hcrossInt : Integrable (fun ω => (Y ω - C ω) * H ω) disorderLaw :=
      (hY.sub hC).integrable_mul hHLp
    have hEq :
        ∫ ω, (Y ω - B ω) ^ 2 ∂disorderLaw =
          ∫ ω, ((Y ω - C ω) ^ 2 + H ω ^ 2 +
            2 * ((Y ω - C ω) * H ω)) ∂disorderLaw :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)
    have hsplit :
        (∫ ω, ((Y ω - C ω) ^ 2 + H ω ^ 2 +
          2 * ((Y ω - C ω) * H ω)) ∂disorderLaw) =
          (∫ ω, (Y ω - C ω) ^ 2 ∂disorderLaw +
            ∫ ω, H ω ^ 2 ∂disorderLaw) +
            2 * ∫ ω, (Y ω - C ω) * H ω ∂disorderLaw := by
      calc
        _ = (∫ ω, ((Y ω - C ω) ^ 2 + H ω ^ 2) ∂disorderLaw) +
              ∫ ω, 2 * ((Y ω - C ω) * H ω) ∂disorderLaw :=
                integral_add (hYC.add hHsq) (hcrossInt.const_mul 2)
        _ = _ := by rw [integral_add hYC hHsq, integral_const_mul]
    rw [hsplit] at hEq
    have hDsqEq : ∫ ω, (Y ω - C ω) ^ 2 ∂disorderLaw =
        ∫ ω, Y ω ^ 2 ∂disorderLaw - ∫ ω, C ω ^ 2 ∂disorderLaw := by
      have hpointD (ω : Disorder) :
          Y ω ^ 2 = (Y ω - C ω) ^ 2 + C ω ^ 2 +
            2 * ((Y ω - C ω) * C ω) := by ring
      have hDcrossInt : Integrable (fun ω => (Y ω - C ω) * C ω) disorderLaw :=
        (hY.sub hC).integrable_mul hC
      have hDadd :
          ∫ ω, ((Y ω - C ω) ^ 2 + C ω ^ 2) ∂disorderLaw =
            ∫ ω, (Y ω - C ω) ^ 2 ∂disorderLaw +
              ∫ ω, C ω ^ 2 ∂disorderLaw := integral_add hYC hCsq
      have hDscale :
          ∫ ω, 2 * ((Y ω - C ω) * C ω) ∂disorderLaw =
            2 * ∫ ω, (Y ω - C ω) * C ω ∂disorderLaw := integral_const_mul _ _
      have hDecomp :
          ∫ ω, Y ω ^ 2 ∂disorderLaw =
            (∫ ω, (Y ω - C ω) ^ 2 ∂disorderLaw +
              ∫ ω, C ω ^ 2 ∂disorderLaw) +
              2 * ∫ ω, (Y ω - C ω) * C ω ∂disorderLaw := by
        calc
          _ = ∫ ω, ((Y ω - C ω) ^ 2 + C ω ^ 2 +
                2 * ((Y ω - C ω) * C ω)) ∂disorderLaw := by
                  apply integral_congr_ae
                  exact Filter.Eventually.of_forall hpointD
          _ = (∫ ω, ((Y ω - C ω) ^ 2 + C ω ^ 2) ∂disorderLaw) +
                ∫ ω, 2 * ((Y ω - C ω) * C ω) ∂disorderLaw :=
                  integral_add (hYC.add hCsq) (hDcrossInt.const_mul 2)
          _ = _ := by rw [hDadd, hDscale]
      rw [hcrossCZero] at hDecomp
      linarith only [hDecomp]
    rw [hDsqEq, hcrossZero] at hEq
    simpa only [H, add_zero, mul_zero] using hEq

end Critical2DKPZ.SHF.TimeContinuity

end
