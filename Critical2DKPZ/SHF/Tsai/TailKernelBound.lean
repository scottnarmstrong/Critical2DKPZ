/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.TailWordBound
public import Critical2DKPZ.SHF.Tsai.TailKernelResummation

/-! # The complete four-particle tail-kernel bound -/

@[expose] public section

open MeasureTheory Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- The four-particle tail kernel has a weighted `Lᵖ → L²` form bound of order `t^{-1/p}` on each bounded positive-time interval. -/
theorem weightedFormBound_tailKernel (θ T : ℝ) {p a : ℝ} (hp : 2 < p) (ha : 0 < a) (β : CollisionPair 4) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 < t → t ≤ T →
      WeightedFormBound volume volume (fun _ => 0) (fun y => a * configurationOneNorm y) p 2
        (tailKernel θ β t) (ENNReal.ofReal (c * t ^ (-1 / p))) := by
  obtain ⟨c, hc, hword⟩ := weightedFormBound_tailWord_le θ T hp ha
  exact weightedFormBound_tailKernel_of_tailWord_bound θ T β hc
    (fun rate hrate m w hfirst t ht htT => hword rate hrate β m w hfirst t ht htT)

end Critical2DKPZ.SHF.Tsai

end
