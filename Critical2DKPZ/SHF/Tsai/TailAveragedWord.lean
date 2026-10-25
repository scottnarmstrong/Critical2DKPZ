/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.TailTimeComparison
public import Critical2DKPZ.SHF.Tsai.TailLaplaceWord
import Critical2DKPZ.SHF.Tsai.ConjugatedLaplaceAverage
import Critical2DKPZ.SHF.Tsai.ConjugatedCollisionLp
import Mathlib.Tactic

/-! # Fixed-time tail words from their Laplace averages -/

@[expose] public section

open MeasureTheory Set Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- A short forward time average transfers the scaled Laplace bound to the
literal tail word. The inverse window length and endpoint power are kept
explicit for the uniform scalar estimate. -/
theorem weightedFormBound_averaged_tailWord {p a θ lam t : ℝ}
    (hp : 2 < p) (ha : 0 < a) (hlam : 0 < lam) (hθ : θ < Real.log lam)
    (ht : 0 < t) (hWindow : 1 / lam ≤ t)
    (β : CollisionPair 4) (w : List (CollisionPair 4))
    (hword : collisionListNoAdjacentRepeat (β :: w)) :
    WeightedFormBound volume volume (fun _ : FusedConfiguration β => 0)
      (fun y : Configuration 4 => a * configurationOneNorm y) p 2
      (tailWordKernel θ β w t)
      ((ENNReal.ofReal lam * ENNReal.ofReal (Real.exp (lam * (t + 1 / lam))) *
          ENNReal.ofReal ((2 : ℝ) ^ (4 * (2 * w.length + 2)))) *
        (laplaceCollisionResolventConstant θ lam *
          (integratedPotentialRowConstant ^ w.length *
            (laplaceCollisionResolventConstant θ lam ^ w.length *
              ENNReal.ofReal (laplaceIncomingScaledUniformConstant hp ha *
                (1 / lam) ^ (1 - 1 / p)))))) := by
  let F : ℝ≥0∞ := ENNReal.ofReal lam *
    ENNReal.ofReal (Real.exp (lam * (t + 1 / lam))) *
      ENNReal.ofReal ((2 : ℝ) ^ (4 * (2 * w.length + 2)))
  have hFt : F ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    ENNReal.ofReal_ne_top
  have hpoint (z : FusedConfiguration β) (y : Configuration 4) :
      tailWordKernel θ β w t z y ≤
        F * laplaceTimeKernel lam (tailWordTimeKernel θ β w) z y := by
    rw [tailWordKernel_eq_tailWordTimeKernel]
    have h := le_laplaceTimeKernel_of_local_comparison
      (tailWordTimeKernel θ β w) hlam.le ht (one_div_pos.mpr hlam)
      (C := ENNReal.ofReal ((2 : ℝ) ^ (4 * (2 * w.length + 2))))
      ENNReal.ofReal_ne_top z y (by
        intro s hts hst
        have hs : s ≤ 2 * t := by linarith only [hst, hWindow]
        rw [← tailWordKernel_eq_tailWordTimeKernel,
          ← tailWordKernel_eq_tailWordTimeKernel]
        exact tailWordKernel_le_on_double_time_interval θ β w ht hts hs z y)
    simpa only [F, one_div, inv_inv] using h
  have hLap := weightedFormBound_laplace_tailWord_scaled hp ha hlam hθ β w hword
  exact (weightedFormBound_const_mul hFt hLap).mono hpoint le_rfl

end Critical2DKPZ.SHF.Tsai

end
