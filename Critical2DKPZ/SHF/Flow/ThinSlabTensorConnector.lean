/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.MollifiedHeatConnectorConvergence
public import Critical2DKPZ.SHF.Flow.ThinSlabMollifierBounds
public import Critical2DKPZ.SHF.Tsai.ChainFormBounds
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-! # Tensorization of the mollified heat connector -/

@[expose] public noncomputable section
open MeasureTheory Critical2DKPZ.DeltaBose Critical2DKPZ.SHF.Tsai
open scoped ENNReal
namespace Critical2DKPZ.SHF.Flow

/-- Two independent scalar heat convolutions are precisely the composition
of the tensor connector with the free two-particle heat kernel. -/
theorem lintegral_connectorKernel_freeKernel_two (k : Plane → ℝ)
    (hk : Continuous k) (hkc : HasCompactSupport k) (hk0 : ∀ x, 0 ≤ k x)
    {v : ℝ} (hv : 0 < v) (x z : Configuration 2) :
    (∫⁻ y : Configuration 2, connectorKernel (fun _ : Fin 2 => k) x y *
      ENNReal.ofReal (freeKernel 2 v y z)) =
      ∏ i : Fin 2, ENNReal.ofReal (∫ y : Plane, k (x i - y) * heatKernel v (z i - y)) := by
  let f : Fin 2 → Plane → ℝ := fun i y => k (x i - y) * heatKernel v (z i - y)
  have hf (i : Fin 2) : Integrable (f i) := by
    apply Continuous.integrable_of_hasCompactSupport
      ((hk.comp (continuous_const.sub continuous_id)).mul
        ((Critical2DKPZ.continuous_heatKernel v).comp (continuous_const.sub continuous_id)))
    exact (hkc.comp_homeomorph (Homeomorph.subLeft (x i))).mul_right
  have hf0 (i : Fin 2) (y : Plane) : 0 ≤ f i y :=
    mul_nonneg (hk0 _) (heatKernel_nonneg hv.le _)
  have hProd : Integrable (fun y : Configuration 2 => ∏ i, f i (y i)) :=
    Integrable.fintype_prod hf
  have hProd0 (y : Configuration 2) : 0 ≤ ∏ i, f i (y i) :=
    Finset.prod_nonneg fun i _ => hf0 i (y i)
  have hEq (y : Configuration 2) : connectorKernel (fun _ : Fin 2 => k) x y *
      ENNReal.ofReal (freeKernel 2 v y z) = ENNReal.ofReal (∏ i, f i (y i)) := by
    simp only [connectorKernel, freeKernel, Fin.prod_univ_two, f]
    rw [← ENNReal.ofReal_mul (hk0 _), ← ENNReal.ofReal_mul (mul_nonneg (hk0 _) (hk0 _))]
    congr 1
    ring
  simp_rw [hEq]
  rw [← ofReal_integral_eq_lintegral_ofReal hProd (Filter.Eventually.of_forall hProd0),
    integral_fintype_prod_volume_eq_prod f]
  simp only [Fin.prod_univ_two]
  rw [ENNReal.ofReal_mul (integral_nonneg (hf0 0))]

/-- The tensor of smoothed heat connectors is `W_e` composed with the free
 two-particle kernel, with the canonical mollifier tensor normalization. -/
theorem slabSmoothedHeatTensor_eq_spatialKernelComp {v e : ℝ}
    (hv : 0 < v) (he : 0 < e) (w : Plane → ℝ) (hw : Continuous w)
    (hwc : HasCompactSupport w) (hw0 : ∀ x, 0 ≤ w x) (x z : Configuration 2) :
    (∏ i : Fin 2, ENNReal.ofReal (slabSmoothedHeatConnector v e w (x i, z i))) =
      spatialKernelComp volume (slabMollifierTensorKernel 2 e w)
        (fun y z => ENNReal.ofReal (freeKernel 2 v y z)) x z := by
  let we : Plane → ℝ := fun y => e⁻¹ ^ 2 * w (e⁻¹ • y)
  have hwe : Continuous we := continuous_const.mul
    (hw.comp ((continuous_const : Continuous fun _ : Plane => e⁻¹).smul continuous_id))
  have hwec : HasCompactSupport we := by
    have hcomp : HasCompactSupport (fun y : Plane => w (e⁻¹ • y)) :=
      hwc.comp_smul (inv_ne_zero he.ne')
    exact HasCompactSupport.smul_left (f := fun _ : Plane => (e⁻¹ ^ 2 : ℝ)) hcomp
  have hwe0 (y : Plane) : 0 ≤ we y := mul_nonneg (sq_nonneg _) (hw0 _)
  have h := lintegral_connectorKernel_freeKernel_two we hwe hwec hwe0 hv x z
  simpa only [slabSmoothedHeatConnector_eq_integral, spatialKernelComp,
    slabMollifierTensorKernel] using h.symm

end Critical2DKPZ.SHF.Flow
end
