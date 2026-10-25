/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.Dictionary
public import Critical2DKPZ.SHF.DeltaBose.DiagramSeries
public import Critical2DKPZ.SHF.DeltaBose.TwoParticle
public import Critical2DKPZ.SHF.DeltaBose.KernelCompositionL2
import Critical2DKPZ.SHF.DeltaBose.MomentKernelTwoL2
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic

/-! # Continuous diagram coefficients and delta-Bose kernels

A coefficient with `k` pair blocks sums over collision words of length `k` in
the positive diagram series. The empty word gives the free kernel. Every
nonempty word uses the collision block with scalar parameter `ϑ - γ` and
coefficient `4π`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ.SHF.Moments

private instance instUniqueCollisionWordZero (n : ℕ) :
    Unique (DeltaBose.CollisionWord n 0) where
  default := ⟨Fin.elim0, by intro i; exact Fin.elim0 i⟩
  uniq w := by
    apply Subtype.ext
    funext i
    exact Fin.elim0 i

/-- The continuum diagram coefficient with exactly `k` collision blocks is the sum over consecutive-distinct collision words of length `k`. The zero-block term is the free heat kernel. -/
noncomputable def continuousMomentDiagramCoefficient
    (n k : ℕ) (ϑ h : ℝ) (x y : DeltaBose.Configuration n) : ℝ≥0∞ :=
  ∑ w : DeltaBose.CollisionWord n k,
    DeltaBose.diagramKernel (ϑ - Real.eulerMascheroniConstant)
      (List.ofFn w.1) h x y

/-- The zero-collision diagram coefficient is exactly the free kernel. -/
theorem continuousMomentDiagramCoefficient_zero
    (n : ℕ) (ϑ h : ℝ) (x y : DeltaBose.Configuration n) :
    continuousMomentDiagramCoefficient n 0 ϑ h x y =
      ENNReal.ofReal (DeltaBose.freeKernel n h x y) := by
  classical
  simp [continuousMomentDiagramCoefficient, DeltaBose.diagramKernel]

/-- Summing the continuum diagram coefficients over all word lengths gives the moment kernel at parameter `θ = ϑ - γ`. -/
theorem momentKernel_eq_tsum_continuousMomentDiagramCoefficient
    (n : ℕ) (ϑ h : ℝ) (x y : DeltaBose.Configuration n) :
    DeltaBose.momentKernel n (ϑ - Real.eulerMascheroniConstant) h x y =
      ∑' k : ℕ, continuousMomentDiagramCoefficient n k ϑ h x y := by
  classical
  rw [tsum_eq_zero_add' ENNReal.summable]
  rw [continuousMomentDiagramCoefficient_zero]
  rw [DeltaBose.momentKernel]
  congr 1


/-- The critical scalar density satisfies the horizon rescaling identity with Euler-shifted parameter. -/
theorem scalarDensity_horizon_rescale_critical
    (ϑ B t : ℝ) (hB : 0 < B) (ht : 0 < t) :
    B⁻¹ * DeltaBose.scalarDensity
        (ϑ + Real.log B - Real.eulerMascheroniConstant) (t / B) =
      DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) t := by
  rw [show ϑ + Real.log B - Real.eulerMascheroniConstant =
      (ϑ - Real.eulerMascheroniConstant) + Real.log B by ring]
  exact scalarDensity_horizon_rescale
    (ϑ - Real.eulerMascheroniConstant) B t hB ht

/-- At parameter `ϑ - γ`, the scalar collision density is the Gamma integral with weight `exp (ϑu) * exp (-γu)`. -/
theorem scalarDensity_eulerWeightedGammaIntegral (ϑ t : ℝ) :
    DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) t =
      ∫ u in Ioi 0,
        t ^ (u - 1) * Real.exp (ϑ * u) *
          Real.exp (-Real.eulerMascheroniConstant * u) / Real.Gamma u := by
  rw [DeltaBose.scalarDensity_eq_integral]
  apply integral_congr_ae
  filter_upwards with u
  have hexp :
      Real.exp ((ϑ - Real.eulerMascheroniConstant) * u) =
        Real.exp (ϑ * u) * Real.exp (-Real.eulerMascheroniConstant * u) := by
    rw [show (ϑ - Real.eulerMascheroniConstant) * u =
      ϑ * u + -Real.eulerMascheroniConstant * u by ring, Real.exp_add]
  rw [hexp]
  ring




















end Critical2DKPZ.SHF.Moments

end
