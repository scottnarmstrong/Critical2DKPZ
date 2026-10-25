/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.CompactTensorTests
public import Critical2DKPZ.SHF.Tsai.TensorMoments
public import Critical2DKPZ.SHF.Tsai.MomentOperatorWeights

/-! # Moment operators applied to compact configuration tensors

Applying a moment operator to a compact configuration tensor gives an `L²` function
represented almost everywhere by its kernel integral, with the same weighted seminorms.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal CompactlySupported
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- The actual function represented by the moment operator applied to a compact endpoint tensor. -/
def momentTensorTest {n : ℕ} (hn : n ≤ 4) (θ : ℝ) {t : ℝ} (ht : 0 < t)
    (g : Fin n → C_c(Plane, ℝ)) : Configuration n → ℝ :=
  momentOperator hn θ ht (tensorLp (fun i => g i)
    (fun i => (g i).continuous.memLp_of_hasCompactSupport (g i).hasCompactSupport))


/-- The compact-tensor moment-operator test equals its kernel integral almost everywhere; row integrability follows from `ae_integrable_configurationKernelAction`. -/
theorem momentTensorTest_ae_eq_integral {n : ℕ} (hn : n ≤ 4) (θ : ℝ) {t : ℝ} (ht : 0 < t)
    (g : Fin n → C_c(Plane, ℝ)) :
    momentTensorTest hn θ ht g =ᵐ[volume]
      fun x => ∫ y, (momentKernel n θ t x y).toReal * ∏ i, g i (y i) :=
  coe_momentOperator_toLp_eq_kernelAction hn θ ht
    (memLp_configuration_tensor (fun i => g i)
      (fun i => (g i).continuous.memLp_of_hasCompactSupport (g i).hasCompactSupport))

/-- The weighted seminorm of a compact-tensor semigroup test equals the weighted literal kernel-action seminorm. -/
theorem eLpNorm_momentTensorTest_mul_exp {n : ℕ} (hn : n ≤ 4) (θ a : ℝ)
    {t : ℝ} (ht : 0 < t) (g : Fin n → C_c(Plane, ℝ)) (p : ℝ≥0∞) :
    eLpNorm (fun x => momentTensorTest hn θ ht g x * Real.exp (a * configL1Norm x)) p =
      eLpNorm (fun x => Real.exp (a * configL1Norm x) *
        ∫ y, (momentKernel n θ t x y).toReal * ∏ i, g i (y i)) p := by
  apply eLpNorm_congr_ae
  filter_upwards [momentTensorTest_ae_eq_integral hn θ ht g] with x hx
  rw [hx, mul_comm]

end Critical2DKPZ.SHF.Tsai

end
