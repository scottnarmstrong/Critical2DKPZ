/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.TailAveragedWord
public import Critical2DKPZ.SHF.Tsai.TailAverageScalar
import Mathlib.Tactic

/-! # Uniform fixed-time bounds for all four-particle tail words -/

@[expose] public section

open MeasureTheory Set Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- A four-particle tail word has a weighted `Lᵖ → L²` form bound uniform in its length and collision labels, with a logarithmic gain for each continuation. -/
theorem weightedFormBound_tailWord_le (θ T : ℝ) {p a : ℝ} (hp : 2 < p) (ha : 0 < a) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ rate : ℝ, c + 3 ≤ rate → ∀ (β : CollisionPair 4) (m : ℕ) (w : CollisionWord 4 m),
      (∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β) → ∀ t : ℝ, 0 < t → t ≤ T →
      WeightedFormBound volume volume (fun _ => 0) (fun y => a * configurationOneNorm y) p 2
        (fun (z : FusedConfiguration β) (y : Configuration 4) => ∫⁻ u in Set.Ioo 0 t,
          ∫⁻ z' : FusedConfiguration β, ENNReal.ofReal (collisionKernel β θ u z z') *
            diagramKernel θ (List.ofFn w.1) (t - u) (collisionEmbedding β z') y)
        (ENNReal.ofReal (c ^ (m + 1) * ((m : ℝ) + 1) ^ 3 * (c / Real.log (rate - c - 1)) ^ m *
          Real.exp (rate * t) * t ^ (-1 / p))) := by
  let P : ℝ := laplaceIncomingScaledUniformConstant hp ha
  let S : ℝ := integratedPotentialRowConstant.toReal
  let J : ℝ := 4 * Real.pi
  have hP : 0 ≤ P := by dsimp [P, laplaceIncomingScaledUniformConstant]; positivity
  have hS : 0 ≤ S := ENNReal.toReal_nonneg
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hq : 1 / p ≤ 1 := by
    exact (one_div_le_one_div_of_le zero_lt_one (by linarith only [hp])).trans_eq (by norm_num)
  obtain ⟨c, hc, hcE, hScalar⟩ := exists_scalar_averaged_tail_bound θ P S J (1 / p) hP hS hJ hq
  refine ⟨c, hc, ?_⟩
  intro rate hrate β m w hfirst t ht _htT
  let lam : ℝ := rate / 2 + 1 / t
  have hrate0 : 0 ≤ rate := by linarith only [hrate, hc]
  have hlamLower : rate / 2 ≤ lam := le_add_of_nonneg_right (one_div_pos.mpr ht).le
  have hlog := tail_collision_log_rate_bounds hcE hrate hlamLower
  have hlam : 0 < lam := hlog.1
  have hθ : θ < Real.log lam := by linarith only [hlog.2.2.1]
  have hWindow : 1 / lam ≤ t := by
    apply (div_le_iff₀ hlam).mpr
    have heq : t * lam = t * rate / 2 + 1 := by dsimp [lam]; field_simp
    rw [heq]
    linarith only [mul_nonneg ht.le hrate0]
  have hchain : collisionListNoAdjacentRepeat (β :: List.ofFn w.1) := by
    have hw := collisionListNoAdjacentRepeat_of_collisionWord w
    cases m with
    | zero => simp only [List.ofFn_zero, collisionListNoAdjacentRepeat]
    | succ k =>
      rw [List.ofFn_succ]
      exact ⟨(hfirst (by omega)).symm, by simpa only [List.ofFn_succ] using hw⟩
  have hAvg := weightedFormBound_averaged_tailWord hp ha hlam hθ ht hWindow β (List.ofFn w.1) hchain
  rw [List.length_ofFn] at hAvg
  let D : ℝ := Real.log lam - θ
  let R : ℝ := J / D
  let E : ℝ := Real.exp (lam * (t + 1 / lam))
  let K : ℝ := (2 : ℝ) ^ (4 * (2 * m + 2))
  let I : ℝ := (1 / lam) ^ (1 - 1 / p)
  have hD : 0 < D := sub_pos.mpr hθ
  have hR : 0 ≤ R := div_nonneg hJ hD.le
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hRow : integratedPotentialRowConstant = ENNReal.ofReal S :=
    (ENNReal.ofReal_toReal integratedPotentialRowConstant_ne_top).symm
  have hCollision : laplaceCollisionResolventConstant θ lam = ENNReal.ofReal R := by
    rfl
  have hCoeff :
      (ENNReal.ofReal lam * ENNReal.ofReal E * ENNReal.ofReal K) *
        (laplaceCollisionResolventConstant θ lam *
          (integratedPotentialRowConstant ^ m *
            (laplaceCollisionResolventConstant θ lam ^ m * ENNReal.ofReal (P * I)))) =
      ENNReal.ofReal (E * (lam * I) * K * P * R * (S * R) ^ m) := by
    rw [hRow, hCollision, ← ENNReal.ofReal_pow hS, ← ENNReal.ofReal_pow hR]
    rw [← ENNReal.ofReal_mul (pow_nonneg hR m),
      ← ENNReal.ofReal_mul (pow_nonneg hS m), ← ENNReal.ofReal_mul hR,
      ← ENNReal.ofReal_mul hlam.le,
      ← ENNReal.ofReal_mul (mul_nonneg hlam.le hE),
      ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hlam.le hE) hK)]
    congr 1
    rw [mul_pow]
    ring
  change WeightedFormBound volume volume (fun _ : FusedConfiguration β => 0)
    (fun y : Configuration 4 => a * configurationOneNorm y) p 2
    (tailWordKernel θ β (List.ofFn w.1) t) _
  change WeightedFormBound volume volume (fun _ : FusedConfiguration β => 0)
    (fun y : Configuration 4 => a * configurationOneNorm y) p 2
    (tailWordKernel θ β (List.ofFn w.1) t)
    ((ENNReal.ofReal lam * ENNReal.ofReal E * ENNReal.ofReal K) *
      (laplaceCollisionResolventConstant θ lam *
        (integratedPotentialRowConstant ^ m *
          (laplaceCollisionResolventConstant θ lam ^ m * ENNReal.ofReal (P * I))))) at hAvg
  rw [hCoeff] at hAvg
  have hScalar' := hScalar m rate t hrate ht
  have hScalar'' : E * (lam * I) * K * P * R * (S * R) ^ m ≤
      c ^ (m + 1) * (c / Real.log (rate - c - 1)) ^ m * Real.exp (rate * t) * t ^ (-1 / p) := by
    have hRatio : S * R = S * J / D := by dsimp [R]; ring
    rw [hRatio]
    simpa only [E, I, K, R, D, lam, show -(1 / p) = -1 / p by ring] using hScalar'
  have hpoly : 1 ≤ ((m : ℝ) + 1) ^ 3 := one_le_pow₀ (le_add_of_nonneg_left (Nat.cast_nonneg m))
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  have hL : 0 < Real.log (rate - c - 1) := hlog.2.1
  have hTargetNonneg : 0 ≤ c ^ (m + 1) * (c / Real.log (rate - c - 1)) ^ m *
      Real.exp (rate * t) * t ^ (-1 / p) := by positivity
  apply hAvg.mono (fun _ _ => le_rfl)
  apply ENNReal.ofReal_le_ofReal
  refine hScalar''.trans ?_
  calc
    _ ≤ (c ^ (m + 1) * (c / Real.log (rate - c - 1)) ^ m * Real.exp (rate * t) * t ^ (-1 / p)) *
        ((m : ℝ) + 1) ^ 3 := le_mul_of_one_le_right hTargetNonneg hpoly
    _ = _ := by ring

end Critical2DKPZ.SHF.Tsai

end
