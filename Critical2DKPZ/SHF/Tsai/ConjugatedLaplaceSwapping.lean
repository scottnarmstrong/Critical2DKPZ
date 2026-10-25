/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConjugatedIntegratedLp
public import Critical2DKPZ.SHF.Tsai.ConjugatedLaplaceDomination
public import Critical2DKPZ.SHF.Tsai.ConjugatedFormTransport
import Critical2DKPZ.SHF.Tsai.ConjugatedLpForm
import Mathlib.Tactic

/-! # The conjugated `Lᵖ` swapping resolvent bound -/

@[expose] public noncomputable section

open MeasureTheory Critical2DKPZ.DeltaBose Critical2DKPZ.SHF.Flow
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- Exponential damping gives a conjugated swapping-resolvent form bound for every finite `p > 1`, a damped counterpart of Tsai (2024), equation (2.9c). -/
theorem weightedFormBound_laplace_swapping_conj {n : ℕ} (α β : CollisionPair n) (hαβ : α ≠ β) {p a : ℝ}
    (hp : 1 < p) (ha : 0 ≤ a) :
    ∃ c rate₀ : ℝ, 0 < c ∧ ∀ rate : ℝ, rate₀ ≤ rate →
      WeightedFormBound volume volume (fun y => -(a * fusedOneNorm α y)) (fun z => a * fusedOneNorm β z)
        p (p / (p - 1)) (laplaceTimeKernel rate (fun q : ℝ × FusedConfiguration α × FusedConfiguration β =>
          ENNReal.ofReal (swappingKernel α β q.1 q.2.1 q.2.2))) (ENNReal.ofReal c) := by
  obtain ⟨C, hCt, hbound⟩ := exists_integratedSwappingKernel_lp_bound α β hαβ hp
  let D : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ n) * ENNReal.ofReal (1 / 2 : ℝ)
  have hDt : D ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hDCt : D * C ≠ ⊤ := ENNReal.mul_ne_top hDt hCt
  let c : ℝ := (D * C).toReal + 1
  have hc : 0 < c := by dsimp [c]; positivity
  have hcoef : D * C ≤ ENNReal.ofReal c := by
    calc
      D * C = ENNReal.ofReal (D * C).toReal := (ENNReal.ofReal_toReal hDCt).symm
      _ ≤ ENNReal.ofReal c := ENNReal.ofReal_le_ofReal (by dsimp [c]; linarith)
  refine ⟨c, 2 * n * a ^ 2, hc, ?_⟩
  intro rate hrate
  let K : FusedConfiguration α → FusedConfiguration β → ℝ≥0∞ :=
    laplaceTimeKernel rate (fun q : ℝ × FusedConfiguration α × FusedConfiguration β =>
      ENNReal.ofReal (swappingKernel α β q.1 q.2.1 q.2.2))
  have hK : Measurable (Function.uncurry K) :=
    measurable_laplaceTimeKernel rate (measurable_swappingKernel α β).ennreal_ofReal
  have hbase : WeightedFormBound volume volume (fun _ : FusedConfiguration α => 0)
      (fun _ : FusedConfiguration β => 0) p (p / (p - 1)) (integratedSwappingKernel α β) C :=
    WeightedFormBound.of_rpow_action_bound hp (measurable_integratedSwappingKernel α β) hbound
  have hscaled := weightedFormBound_const_mul hDt hbase
  have hx : Measurable (fun z : FusedConfiguration α => a * fusedOneNorm α z) :=
    measurable_const.mul (measurable_fusedOneNorm α)
  have hy : Measurable (fun w : FusedConfiguration β => a * fusedOneNorm β w) :=
    measurable_const.mul (measurable_fusedOneNorm β)
  have hbar : WeightedFormBound volume volume (fun _ : FusedConfiguration α => 0)
      (fun _ : FusedConfiguration β => 0) p (p / (p - 1))
      (expConjugate (fun z => a * fusedOneNorm α z) (fun w => a * fusedOneNorm β w) K) (D * C) :=
    hscaled.mono (fun z w => expConjugate_laplace_swapping_le α β ha hrate z w) le_rfl
  exact (WeightedFormBound.of_expConjugate hx hy hK hbar).mono (fun _ _ => le_rfl) hcoef

end Critical2DKPZ.SHF.Tsai

end
