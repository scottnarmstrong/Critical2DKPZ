/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.ThreeBlockHeatBound
public import Critical2DKPZ.SHF.Tsai.PositiveChainBlockTests
import Mathlib.Tactic

/-! # Middle slices of Gaussian-smoothed three-block chains -/

@[expose] public noncomputable section

open MeasureTheory
open Critical2DKPZ.SHF.Tsai
open scoped ENNReal

namespace Critical2DKPZ.NonGaussian

/-- The middle-block slice of a Gaussian-smoothed chain is the integral over its two outer endpoint pairs. -/
theorem positiveChainBlockTest_three_heat_eq
    (μ : ℕ → Measure (Plane × Plane)) [∀ k, SigmaFinite (μ k)]
    (f g : Plane → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (ε : ℝ) (q : Plane × Plane) :
    positiveChainBlockTest 2 1 μ (fun _ => heatKernel ε)
      (fun p => f p.1 * g p.2) q =
      ∫⁻ o : (Plane × Plane) × (Plane × Plane),
        (f o.1.1 * g o.2.2) *
          (ENNReal.ofReal (heatKernel ε (q.1 - o.1.2)) *
            ENNReal.ofReal (heatKernel ε (o.2.1 - q.2))) ∂(μ 0).prod (μ 2) := by
  let j : Fin 3 := 1
  let e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => Plane × Plane)
  let e₃ := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => Plane × Plane) j
  let J (p : Fin 2 → Plane × Plane) := chainPathTest 2 (fun _ => heatKernel ε)
    (fun p => f p.1 * g p.2) (e₃.symm (q, p))
  have hJ : Measurable J :=
    (measurable_chainPathTest 2 (fun _ => measurable_heatKernel ε)
      ((hf.comp measurable_fst).mul (hg.comp measurable_snd))).comp
        (e₃.symm.measurable.comp (measurable_const.prodMk measurable_id))
  have he := measurePreserving_piFinTwo (fun i : Fin 2 => μ (j.succAbove i))
  have hcomp := (he.symm e).lintegral_comp hJ
  change (∫⁻ p, J p ∂Measure.pi (fun i : Fin 2 => μ (j.succAbove i))) = _
  rw [← hcomp]
  apply lintegral_congr
  intro o
  dsimp [J, e₃, e, j, chainPathTest]
  simp [Fin.prod_univ_two]
  have h0 : Fin.insertNth (α := fun _ : Fin 3 => Plane × Plane) 1 q ![o.1, o.2] 0 = o.1 := by
    rw [show (0 : Fin 3) = (1 : Fin 3).succAbove 0 by rfl, Fin.insertNth_apply_succAbove]
    rfl
  have h2 : Fin.insertNth (α := fun _ : Fin 3 => Plane × Plane) 1 q ![o.1, o.2] 2 = o.2 := by
    rw [show (2 : Fin 3) = (1 : Fin 3).succAbove 1 by rfl, Fin.insertNth_apply_succAbove]
    rfl
  simp only [h0, h2]
  rw [show o.1.2 - q.1 = -(q.1 - o.1.2) by abel,
    show q.2 - o.2.1 = -(o.2.1 - q.2) by abel, heatKernel_neg, heatKernel_neg]
  ac_rfl

/-- Averaging the middle slice against the heat block of duration `τ` bounds it
by `(2πτ)⁻¹` times the product of the two outer masses. -/
theorem lintegral_positiveChainBlockTest_three_heat_le
    (μ : ℕ → Measure (Plane × Plane)) [∀ k, SigmaFinite (μ k)]
    (f g : Plane → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε) :
    (∫⁻ q, positiveChainBlockTest 2 1 μ (fun _ => heatKernel ε)
      (fun p => f p.1 * g p.2) q ∂heatBlock τ) ≤
      ENNReal.ofReal ((2 * Real.pi * τ)⁻¹) *
        (∫⁻ p, f p.1 ∂μ 0) * (∫⁻ p, g p.2 ∂μ 2) := by
  simp_rw [positiveChainBlockTest_three_heat_eq μ f g hf hg ε]
  exact lintegral_threeBlock_heat_le (μ 0) (μ 2) f g hf hg hτ hε

end Critical2DKPZ.NonGaussian

end
