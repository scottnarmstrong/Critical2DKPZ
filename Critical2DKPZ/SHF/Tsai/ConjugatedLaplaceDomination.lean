/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConjugatedCollisionLp
public import Critical2DKPZ.SHF.DeltaBose.WeightedBlockL2
public import Critical2DKPZ.SHF.DeltaBose.IncomingMass
public import Critical2DKPZ.SHF.Flow.WeightMeasurability
public import Mathlib.Tactic
public import Critical2DKPZ.SHF.DeltaBose.LaplaceComposition
public import Critical2DKPZ.SHF.DeltaBose.PotentialIntegratedSchur
public import Critical2DKPZ.SHF.Flow.KernelConjugation
import Mathlib.Tactic

/-! # Damping the exponential weights in a swapping resolvent -/

@[expose] public section

open MeasureTheory Set Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- Sufficient Laplace damping absorbs the quadratic exponential weight
growth uniformly over all positive times. -/
theorem laplaceTimeWeight_mul_weightGrowth_le (n : ℕ) (a : ℝ) {rate t : ℝ}
    (hrate : 2 * n * a ^ 2 ≤ rate) (ht : 0 ≤ t) :
    laplaceTimeWeight rate t * ENNReal.ofReal (weightGrowth n a t) ≤
      ENNReal.ofReal ((2 : ℝ) ^ n) := by
  unfold laplaceTimeWeight
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  have he : Real.exp (-(rate * t)) * weightGrowth n a t =
      (2 : ℝ) ^ n * Real.exp ((2 * n * a ^ 2 - rate) * t) := by
    unfold weightGrowth
    rw [mul_left_comm, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [he]
  apply mul_le_of_le_one_right (by positivity)
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hrate) ht)

/-- The damped conjugated swapping resolvent is pointwise dominated by a
finite multiple of the unweighted, time-integrated swapping kernel. -/
theorem expConjugate_laplace_swapping_le {n : ℕ} (α β : CollisionPair n)
    {a rate : ℝ} (ha : 0 ≤ a) (hrate : 2 * n * a ^ 2 ≤ rate)
    (z : FusedConfiguration α) (w : FusedConfiguration β) :
    Critical2DKPZ.SHF.Flow.expConjugate (fun z => a * fusedOneNorm α z)
      (fun w => a * fusedOneNorm β w)
      (laplaceTimeKernel rate (fun q : ℝ × FusedConfiguration α × FusedConfiguration β =>
        ENNReal.ofReal (swappingKernel α β q.1 q.2.1 q.2.2))) z w ≤
      (ENNReal.ofReal ((2 : ℝ) ^ n) * ENNReal.ofReal (1 / 2 : ℝ)) *
        integratedSwappingKernel α β z w := by
  let E : ℝ≥0∞ := ENNReal.ofReal (Real.exp (a * fusedOneNorm α z - a * fusedOneNorm β w))
  have hpoint {t : ℝ} (ht : 0 < t) :
      (laplaceTimeWeight rate t * ENNReal.ofReal (swappingKernel α β t z w)) * E ≤
        ENNReal.ofReal ((2 : ℝ) ^ n) * ENNReal.ofReal (swappingKernel α β (2 * t) z w) := by
    have hswap : ENNReal.ofReal (swappingKernel α β t z w) * E ≤
        ENNReal.ofReal (weightGrowth n a t) * ENNReal.ofReal (swappingKernel α β (2 * t) z w) := by
      dsimp [E]
      rw [mul_comm (ENNReal.ofReal (swappingKernel α β t z w)),
        ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← ENNReal.ofReal_mul (weightGrowth_pos n a t).le]
      apply ENNReal.ofReal_le_ofReal
      have he : a * fusedOneNorm α z - a * fusedOneNorm β w =
          a * (fusedOneNorm α z - fusedOneNorm β w) := by ring
      rw [he, mul_comm (Real.exp _) (swappingKernel α β t z w)]
      exact swappingKernel_mul_exp_weight_le α β ha ht z w
    calc
      _ = laplaceTimeWeight rate t * (ENNReal.ofReal (swappingKernel α β t z w) * E) :=
        mul_assoc _ _ _
      _ ≤ laplaceTimeWeight rate t * (ENNReal.ofReal (weightGrowth n a t) *
          ENNReal.ofReal (swappingKernel α β (2 * t) z w)) := mul_le_mul' le_rfl hswap
      _ = (laplaceTimeWeight rate t * ENNReal.ofReal (weightGrowth n a t)) *
          ENNReal.ofReal (swappingKernel α β (2 * t) z w) := (mul_assoc _ _ _).symm
      _ ≤ _ := mul_le_mul' (laplaceTimeWeight_mul_weightGrowth_le n a hrate ht.le) le_rfl
  have hsub : integratedSwappingKernel α β z w = ENNReal.ofReal (2 : ℝ) *
      ∫⁻ t in Ioi 0, ENNReal.ofReal (swappingKernel α β (2 * t) z w) :=
    lintegral_Ioi_mul (show (0 : ℝ) < 2 by norm_num) _
  have hhalf : (∫⁻ t in Ioi 0, ENNReal.ofReal (swappingKernel α β (2 * t) z w)) =
      ENNReal.ofReal (1 / 2 : ℝ) * integratedSwappingKernel α β z w := by
    rw [hsub, ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num
  change (∫⁻ t in Ioi 0, laplaceTimeWeight rate t *
    ENNReal.ofReal (swappingKernel α β t z w)) * E ≤ _
  rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  calc
    _ ≤ ∫⁻ t in Ioi 0, ENNReal.ofReal ((2 : ℝ) ^ n) *
        ENNReal.ofReal (swappingKernel α β (2 * t) z w) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hpoint ht
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hhalf, mul_assoc]

end Critical2DKPZ.SHF.Tsai

end
