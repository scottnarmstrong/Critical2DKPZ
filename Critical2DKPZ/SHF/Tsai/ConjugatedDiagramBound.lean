/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConjugatedAveragedDiagram
public import Critical2DKPZ.SHF.Tsai.ConjugatedDiagramScalarUniform
import Mathlib.Tactic

/-! # Uniform near-zero conjugated bounds for individual collision diagrams -/

@[expose] public noncomputable section

open MeasureTheory Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- Every conjugated diagram word satisfies a weighted bilinear bound with an explicit cubic word-length factor and logarithmic damping gain. -/
theorem weightedFormBound_diagramKernel_conj_le (n : ℕ) (θ T : ℝ) {p a : ℝ} (hp : 1 < p) (ha : 0 ≤ a) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ rate : ℝ, c + 3 ≤ rate → ∀ (m : ℕ) (w : CollisionWord n (m + 1)),
      ∀ t : ℝ, 0 < t → t ≤ T →
      WeightedFormBound volume volume (fun x => -(a * configurationOneNorm x)) (fun y => a * configurationOneNorm y)
        p (p / (p - 1)) (diagramKernel θ (List.ofFn w.1) t)
        (ENNReal.ofReal (c ^ (m + 1) * ((m : ℝ) + 1) ^ 3 * (c / Real.log (rate - c - 1)) ^ m *
          Real.exp (rate * t))) := by
  let g : ℝ := 2 * n * a ^ 2
  let c₀ : ℝ := conjugatedEndpointShift n hp ha
  let R : ℝ := conjugatedSwappingThreshold n hp ha
  let P : ℝ := conjugatedEndpointProductConstant n hp ha
  let S : ℝ := conjugatedSwappingConstant n hp ha
  let J : ℝ := (2 : ℝ) ^ n * (4 * Real.pi)
  have hg : 0 ≤ g := by dsimp [g]; positivity
  have hc₀ : 0 ≤ c₀ := zero_le_one.trans (conjugatedEndpointShift_ge_one n hp ha)
  have hR : 0 ≤ R := zero_le_one.trans (conjugatedSwappingConstants_ge_one n hp ha).2
  have hP : 0 ≤ P := (conjugatedEndpointProductConstant_pos n hp ha).le
  have hS : 0 ≤ S := zero_le_one.trans (conjugatedSwappingConstants_ge_one n hp ha).1
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  obtain ⟨c, hc, h2c, hRc, hgc, hbound⟩ :=
    exists_scalar_conjugated_diagram_bound n θ g c₀ R P S J hg hc₀ hR hP hS hJ
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  refine ⟨c, hc, ?_⟩
  intro rate hrate m w t ht _htT
  let lam : ℝ := rate + 1 / t
  have hcr : c ≤ rate := by linarith only [hrate]
  have hlam : rate ≤ lam := le_add_of_nonneg_right (one_div_pos.mpr ht).le
  have hwindow := conjugated_averaging_window_bounds hc₀ (h2c.trans hcr) ht
  have hlog := conjugated_collision_log_rate_bounds hgc hrate hlam
  have hL : 0 < Real.log (rate - c - 1) := hlog.1
  have hEndpoint : c₀ < lam := sub_pos.mp hwindow.1
  have hSwap : R ≤ lam := hRc.trans (hcr.trans hlam)
  have hE : 0 < Real.exp (2 * max θ 0 + 1) := Real.exp_pos _
  have hGrowth : g < lam := by linarith only [hgc, hrate, hlam, hE]
  have hTheta : θ < Real.log (lam - g) := by linarith only [hlog.2.1]
  let l : List (CollisionPair n) := List.ofFn w.1
  have hlen : l.length = m + 1 := List.length_ofFn
  have hlChain : collisionListNoAdjacentRepeat l := collisionListNoAdjacentRepeat_of_collisionWord w
  change WeightedFormBound volume volume (fun x : Configuration n => -(a * configurationOneNorm x))
    (fun y : Configuration n => a * configurationOneNorm y) p (p / (p - 1)) (diagramKernel θ l t) _
  cases hList : l with
  | nil =>
    have hzero : l.length = 0 := congrArg List.length hList
    omega
  | cons α v =>
    have hvlen : v.length = m := by
      have h : v.length + 1 = m + 1 := (congrArg List.length hList).symm.trans hlen
      omega
    have hchain : collisionListNoAdjacentRepeat (α :: v) := hList ▸ hlChain
    have hAt := weightedFormBound_averaged_diagram_conj θ hp ha ht hEndpoint hSwap hGrowth hTheta
      hwindow.2.2.1 α v hchain
    rw [hvlen] at hAt
    have hBasic := hAt.mono (fun _ _ => le_rfl)
      (ENNReal.ofReal_le_ofReal (hbound m rate t hrate ht))
    have hpoly : 1 ≤ ((m : ℝ) + 1) ^ 3 := one_le_pow₀ (le_add_of_nonneg_left (Nat.cast_nonneg m))
    have hterm : 0 ≤ c ^ (m + 1) * (c / Real.log (rate - c - 1)) ^ m * Real.exp (rate * t) := by
      positivity
    have hCubic : c ^ (m + 1) * (c / Real.log (rate - c - 1)) ^ m * Real.exp (rate * t) ≤
        c ^ (m + 1) * ((m : ℝ) + 1) ^ 3 * (c / Real.log (rate - c - 1)) ^ m * Real.exp (rate * t) := by
      calc
        _ ≤ (c ^ (m + 1) * (c / Real.log (rate - c - 1)) ^ m * Real.exp (rate * t)) *
            ((m : ℝ) + 1) ^ 3 := le_mul_of_one_le_right hterm hpoly
        _ = _ := by ac_rfl
    exact hBasic.mono (fun _ _ => le_rfl) (ENNReal.ofReal_le_ofReal hCubic)

end Critical2DKPZ.SHF.Tsai

end
