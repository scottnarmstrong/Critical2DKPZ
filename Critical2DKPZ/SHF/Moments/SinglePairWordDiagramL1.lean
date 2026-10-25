/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.DiagramKernelBounds
public import Critical2DKPZ.SHF.DeltaBose.Measurability
public import Critical2DKPZ.SHF.Tsai.ConfigurationKernelForms
public import Critical2DKPZ.SHF.Tsai.CompactTensorMajorants
public import Critical2DKPZ.SHF.Tsai.TensorMoments
import Mathlib.Tactic

/-! # Absolute integrability of the tested two-particle diagram -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory
open scoped CompactlySupported ENNReal
open DeltaBose

private theorem pairTwo_diagram_formBound (θ : ℝ) {T : ℝ} (hT : 0 < T) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ FormBound volume volume (diagramKernel θ [pairTwo] T) c := by
  obtain ⟨C, c, rate, _hC, _hc, _hrate, hb⟩ := exists_formBound_diagramKernel 2 θ
  refine ⟨ENNReal.ofReal (C * Real.exp (rate * T) * min T 1 ^ (-(2 : ℝ))),
    ENNReal.ofReal_ne_top, ?_⟩
  have h := hb θ le_rfl rate le_rfl 0 (pairEquivWordOne 2 pairTwo) T hT
  change FormBound volume volume
    (diagramKernel θ (List.ofFn (fun _ : Fin 1 => pairTwo)) T) _ at h
  simpa only [List.ofFn_const, List.replicate_succ,
    List.replicate_zero, pow_zero, mul_one, Nat.cast_ofNat] using h

/-- Every compact endpoint-pair test gives an absolutely integrable single pair-block diagram. -/
theorem integrable_tested_pairTwo_diagram
    (θ : ℝ) {T : ℝ} (hT : 0 < T) (φ : Fin 2 → C_c(Plane × Plane, ℝ)) :
    Integrable (fun p : Configuration 2 × Configuration 2 =>
      (∏ i, φ i (p.1 i, p.2 i)) * (diagramKernel θ [pairTwo] T p.1 p.2).toReal)
      (volume.prod volume) := by
  classical
  choose g g' hg hg' hone using fun i : Fin 2 =>
    Tsai.exists_compactTensor_majorant (tsupport (φ i)) (φ i).hasCompactSupport.isCompact
  have hb (i : Fin 2) (x y : Plane) :
      |φ i (x, y)| ≤ ‖(φ i).toBoundedContinuousFunction‖ * (g i x * g' i y) := by
    by_cases hp : (x, y) ∈ tsupport (φ i)
    · rw [hone i (x, y) hp, mul_one]
      exact (φ i).toBoundedContinuousFunction.norm_coe_le_norm (x, y)
    · rw [image_eq_zero_of_notMem_tsupport hp, abs_zero]
      exact mul_nonneg (norm_nonneg _) (mul_nonneg (hg i x) (hg' i y))
  let F : Configuration 2 → ℝ := fun x => ∏ i, g i (x i)
  let G : Configuration 2 → ℝ := fun y => ∏ i, g' i (y i)
  have hF : MemLp F 2 := Tsai.memLp_configuration_tensor (fun i => g i)
    (fun i => (g i).continuous.memLp_of_hasCompactSupport (g i).hasCompactSupport)
  have hG : MemLp G 2 := Tsai.memLp_configuration_tensor (fun i => g' i)
    (fun i => (g' i).continuous.memLp_of_hasCompactSupport (g' i).hasCompactSupport)
  have hm : Measurable (Function.uncurry (diagramKernel θ [pairTwo] T)) := by
    have hmap : Measurable (fun p : Configuration 2 × Configuration 2 => ((θ, T), p)) :=
      measurable_const.prodMk measurable_id
    exact (measurable_diagramKernel [pairTwo]).comp hmap
  obtain ⟨c, hc, hform⟩ := pairTwo_diagram_formBound θ hT
  have hi := (Tsai.configurationKernel_real_form_bound hm hc hform F G hF hG).1
  let M : ℝ := ‖(φ 0).toBoundedContinuousFunction‖ * ‖(φ 1).toBoundedContinuousFunction‖
  apply (hi.const_mul M).mono'
  · exact ((Finset.measurable_prod Finset.univ (fun i _ =>
      (φ i).measurable.comp (((measurable_pi_apply i).comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp measurable_snd)))).mul
        hm.ennreal_toReal).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro p
    have hk : 0 ≤ (diagramKernel θ [pairTwo] T p.1 p.2).toReal := ENNReal.toReal_nonneg
    have hprod : |∏ i, φ i (p.1 i, p.2 i)| ≤ M * (F p.1 * G p.2) := by
      simp only [Fin.prod_univ_two, abs_mul]
      calc
        _ ≤ (‖(φ 0).toBoundedContinuousFunction‖ * (g 0 (p.1 0) * g' 0 (p.2 0))) *
            (‖(φ 1).toBoundedContinuousFunction‖ * (g 1 (p.1 1) * g' 1 (p.2 1))) :=
          mul_le_mul (hb 0 _ _) (hb 1 _ _) (abs_nonneg _)
            (mul_nonneg (norm_nonneg _) (mul_nonneg (hg _ _) (hg' _ _)))
        _ = _ := by dsimp [M, F, G]; simp only [Fin.prod_univ_two]; ring
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk]
    calc
      _ ≤ M * (F p.1 * G p.2) * (diagramKernel θ [pairTwo] T p.1 p.2).toReal :=
        mul_le_mul_of_nonneg_right hprod hk
      _ = _ := by ring

end Critical2DKPZ.SHF.Moments
