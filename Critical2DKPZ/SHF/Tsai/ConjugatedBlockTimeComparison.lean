/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConjugatedTimeComparison
import Mathlib.Tactic

/-! # Time-dilation comparison of the concrete delta-Bose blocks -/

@[expose] public section

open MeasureTheory Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- A free configuration kernel loses at most one normalization factor
per particle when its elapsed time is increased. -/
theorem freeKernel_le_time_dilate (n : ℕ) {a t : ℝ} (ha : 1 ≤ a) (ht : 0 < t)
    (x y : Configuration n) : freeKernel n t x y ≤ a ^ n * freeKernel n (a * t) x y := by
  unfold freeKernel
  calc
    _ ≤ ∏ i : Fin n, a * heatKernel (a * t) (y i - x i) :=
      Finset.prod_le_prod₀ (fun _ _ => (heatKernel_pos ht _).le)
        (fun _ _ => heatKernel_le_time_dilate ha ht _)
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The collision block obeys the same normalization comparison as the
free `n`-particle kernel: its density supplies the missing heat factor. -/
theorem collisionKernel_le_time_dilate {n : ℕ} (α : CollisionPair n) (θ : ℝ)
    {a t : ℝ} (ha : 1 ≤ a) (ht : 0 < t) (y z : FusedConfiguration α) :
    collisionKernel α θ t y z ≤ a ^ n * collisionKernel α θ (a * t) y z := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hat : 0 < a * t := mul_pos ha0 ht
  have ht2 : 0 < t / 2 := by positivity
  have hat2 : 0 < a * t / 2 := by positivity
  have hcenter : heatKernel (t / 2) (z.1 - y.1) ≤ a * heatKernel (a * t / 2) (z.1 - y.1) := by
    simpa only [show a * (t / 2) = a * t / 2 by ring] using
      heatKernel_le_time_dilate ha ht2 (z.1 - y.1)
  have hprod : (∏ i : Spectator α, heatKernel t (z.2 i - y.2 i)) ≤
      ∏ i : Spectator α, a * heatKernel (a * t) (z.2 i - y.2 i) :=
    Finset.prod_le_prod₀ (fun _ _ => (heatKernel_pos ht _).le)
      (fun _ _ => heatKernel_le_time_dilate ha ht _)
  have hscalar : 4 * Real.pi * scalarDensity θ t ≤
      4 * Real.pi * (a * scalarDensity θ (a * t)) :=
    mul_le_mul_of_nonneg_left (scalarDensity_le_time_dilate θ ha ht) (by positivity)
  have htwo : (4 * Real.pi * scalarDensity θ t) * heatKernel (t / 2) (z.1 - y.1) ≤
      (4 * Real.pi * (a * scalarDensity θ (a * t))) *
        (a * heatKernel (a * t / 2) (z.1 - y.1)) :=
    mul_le_mul hscalar hcenter (heatKernel_pos ht2 _).le
      (mul_nonneg (by positivity) (mul_nonneg ha0.le (scalarDensity_pos θ hat).le))
  have hn : n = Fintype.card (Spectator α) + 2 := by
    rw [card_spectator]
    have h := α.2
    have h' := α.1.2.isLt
    omega
  have hapow : a ^ n = a ^ Fintype.card (Spectator α) * a ^ 2 := by
    calc
      a ^ n = a ^ (Fintype.card (Spectator α) + 2) := congrArg (fun k : ℕ => a ^ k) hn
      _ = _ := pow_add _ _ _
  unfold collisionKernel
  calc
    _ ≤ ((4 * Real.pi * (a * scalarDensity θ (a * t))) *
        (a * heatKernel (a * t / 2) (z.1 - y.1))) *
          ∏ i : Spectator α, a * heatKernel (a * t) (z.2 i - y.2 i) :=
      mul_le_mul htwo hprod (Finset.prod_nonneg fun _ _ => (heatKernel_pos ht _).le)
        (mul_nonneg (mul_nonneg (by positivity) (mul_nonneg ha0.le (scalarDensity_pos θ hat).le))
          (mul_nonneg ha0.le (heatKernel_pos hat2 _).le))
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hapow, pow_two]
      ring

end Critical2DKPZ.SHF.Tsai

end
