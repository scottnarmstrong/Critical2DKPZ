/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonBlocks
public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonParity
import Critical2DKPZ.MomentBounds.AiiKSmoothedShift
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic

/-! # Free entrance smoothing does not increase fourth moments -/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped BigOperators ENNReal

namespace Critical2DKPZ.Extensions.GffTangent

/-- Finite centered entrance pairings have every finite disorder moment. -/
theorem memLp_finiteEntranceFluctuation (β c : ℝ) (a n : ℕ)
    (S : Finset Site) (ν : Site → ℝ) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (finiteEntranceFluctuation β c a n S ν) p disorderLaw := by
  unfold finiteEntranceFluctuation
  apply MemLp.const_mul
  exact memLp_finsetSum S fun w _ =>
    ((Polymer.memLp_pointToPlane β a n w p hp).sub (memLp_const 1)).const_mul _

/-- A common shift of all starts preserves every polynomial moment of the
finite centered pairing, with its signed weights unchanged. -/
theorem integral_pow_finiteEntranceFluctuation_translate (β c : ℝ) (a n : ℕ)
    (S : Finset Site) (ν : Site → ℝ) (v : Site) (k : ℕ) :
    (∫ ω, (c * ∑ w ∈ S, ν w * (pointToPlane β a n (w + v) ω - 1)) ^ k ∂disorderLaw) =
      ∫ ω, finiteEntranceFluctuation β c a n S ν ω ^ k ∂disorderLaw := by
  have hm : Measurable (fun ω => c * ∑ w ∈ S, ν w * (pointToPlane β a n (w + v) ω - 1)) :=
    measurable_const.mul (Finset.measurable_sum _ fun w _ =>
      measurable_const.mul ((Polymer.measurable_pointToPlane β a n (w + v)).sub measurable_const))
  rw [← integral_map hm.aemeasurable (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x ^ k)
    (disorderLaw.map (fun ω => c * ∑ w ∈ S, ν w * (pointToPlane β a n (w + v) ω - 1)))),
    law_finiteEntranceFluctuation_translate]
  exact integral_map (measurable_finiteEntranceFluctuation β c a n S ν).aemeasurable
    (by fun_prop)

/-- A common shift of the disorder time origin preserves the centered pairing's
polynomial moments. -/
theorem integral_pow_finiteEntranceFluctuation_timeShift (β c : ℝ) (a n : ℕ)
    (S : Finset Site) (ν : Site → ℝ) (k : ℕ) :
    (∫ ω, finiteEntranceFluctuation β c a n S ν ω ^ k ∂disorderLaw) =
      ∫ ω, finiteEntranceFluctuation β c 0 n S ν ω ^ k ∂disorderLaw := by
  have he (ω : Disorder) : finiteEntranceFluctuation β c a n S ν ω =
      finiteEntranceFluctuation β c 0 n S ν (Smoothing.shiftEnvironment a ω) := by
    unfold finiteEntranceFluctuation
    congr 1
    apply Finset.sum_congr rfl
    intro w _
    rw [MomentBounds.pointToPlane_timeShift β a n w ω]
  simp_rw [he]
  exact Smoothing.integral_shiftEnvironment a
    ((measurable_finiteEntranceFluctuation β c 0 n S ν).pow_const k)

/-- The free-entrance window is an average of common spatial translations of
an unsmoothed finite pairing. The same displacement is used at every start. -/
theorem latticeWindowFluctuation_eq_walk_average (β c : ℝ) (a b : ℕ)
    (S : Finset Site) (ν : Site → ℝ) (ω : Disorder) :
    latticeWindowFluctuation β c a b S ν ω =
      ∑ s : Fin a → Fin 4, (4 : ℝ)⁻¹ ^ a *
        (c * ∑ w ∈ S, ν w *
          (pointToPlane β a (b - a) (w + walkPosition 0 s a) ω - 1)) := by
  have hmass := Polymer.sum_walkProbability a
  have hfree (w : Site) : freeEntranceWindowMass β a b w ω =
      ∑ s : Fin a → Fin 4, (4 : ℝ)⁻¹ ^ a *
        pointToPlane β a (b - a) (w + walkPosition 0 s a) ω := by
    unfold freeEntranceWindowMass
    apply Finset.sum_congr rfl
    intro s _
    rw [Polymer.walkPosition_eq_start_add w s a]
  unfold latticeWindowFluctuation
  simp_rw [hfree]
  calc
    _ = c * ∑ w ∈ S, ν w *
        (∑ s : Fin a → Fin 4, (4 : ℝ)⁻¹ ^ a *
          (pointToPlane β a (b - a) (w + walkPosition 0 s a) ω - 1)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro w _
      simp_rw [mul_sub, mul_one]
      rw [Finset.sum_sub_distrib, hmass]
      ring
    _ = _ := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro w _
      ring

/-- Jensen and disorder stationarity remove the free entrance from a fourth
moment upper bound. No sign restriction on the entrance coefficients is needed. -/
theorem integral_fourth_latticeWindowFluctuation_le (β c : ℝ) (a b : ℕ)
    (S : Finset Site) (ν : Site → ℝ) :
    (∫ ω, latticeWindowFluctuation β c a b S ν ω ^ 4 ∂disorderLaw) ≤
      ∫ ω, finiteEntranceFluctuation β c 0 (b - a) S ν ω ^ 4 ∂disorderLaw := by
  let Y : (Fin a → Fin 4) → Disorder → ℝ := fun s ω =>
    c * ∑ w ∈ S, ν w * (pointToPlane β a (b - a) (w + walkPosition 0 s a) ω - 1)
  have hY (s : Fin a → Fin 4) : Integrable (fun ω => Y s ω ^ 4) disorderLaw := by
    have hmem : MemLp (Y s) 4 disorderLaw := by
      apply MemLp.const_mul
      exact memLp_finsetSum S fun w _ =>
        ((Polymer.memLp_pointToPlane β a (b - a) (w + walkPosition 0 s a) 4 (by norm_num)).sub
          (memLp_const 1)).const_mul _
    have h := hmem.integrable_norm_pow'
    simpa only [Real.norm_eq_abs, Even.pow_abs (by decide : Even 4)] using h
  have hpoint (ω : Disorder) : latticeWindowFluctuation β c a b S ν ω ^ 4 ≤
      ∑ s : Fin a → Fin 4, (4 : ℝ)⁻¹ ^ a * Y s ω ^ 4 := by
    rw [latticeWindowFluctuation_eq_walk_average]
    exact Real.pow_arith_mean_le_arith_mean_pow_of_even Finset.univ
      (fun _ => (4 : ℝ)⁻¹ ^ a) (fun s => Y s ω) (fun _ _ => by positivity)
      (Polymer.sum_walkProbability a) (by decide : Even 4)
  have hleft : Integrable (fun ω => latticeWindowFluctuation β c a b S ν ω ^ 4) disorderLaw := by
    have h := (memLp_latticeWindowFluctuation β c a b S ν 4 (by norm_num)).integrable_norm_pow'
    simpa only [Real.norm_eq_abs, Even.pow_abs (by decide : Even 4)] using h
  calc
    _ ≤ ∫ ω, ∑ s : Fin a → Fin 4, (4 : ℝ)⁻¹ ^ a * Y s ω ^ 4 ∂disorderLaw :=
      integral_mono hleft (integrable_finsetSum _ (fun s _ => (hY s).const_mul _)) hpoint
    _ = ∑ s : Fin a → Fin 4, (4 : ℝ)⁻¹ ^ a *
        (∫ ω, finiteEntranceFluctuation β c a (b - a) S ν ω ^ 4 ∂disorderLaw) := by
      rw [integral_finsetSum _ (fun s _ => (hY s).const_mul _)]
      apply Finset.sum_congr rfl
      intro s _
      rw [integral_const_mul]
      exact congrArg ((4 : ℝ)⁻¹ ^ a * ·)
        (integral_pow_finiteEntranceFluctuation_translate β c a (b - a) S ν (walkPosition 0 s a) 4)
    _ = _ := by
      rw [← Finset.sum_mul, Polymer.sum_walkProbability, one_mul,
        integral_pow_finiteEntranceFluctuation_timeShift]

end Critical2DKPZ.Extensions.GffTangent
