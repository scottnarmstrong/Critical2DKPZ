/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConjugatedDiagramBound
public import Critical2DKPZ.SHF.Tsai.ConjugatedFreeBounds
public import Critical2DKPZ.SHF.Tsai.ConjugatedSeriesMajorant
import Mathlib.Tactic

/-! # The conjugated moment semigroup bound, uniform near time zero -/

@[expose] public noncomputable section

open MeasureTheory Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- On each bounded positive-time interval, the moment kernel has a uniform conjugated weighted `Lᵖ` form bound for every finite `p > 1`, as in Tsai (2024), equation (2.16). -/
theorem weightedFormBound_momentKernel_conj (n : ℕ) (θ T : ℝ) {p a : ℝ} (hp : 1 < p) (ha : 0 ≤ a) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 < t → t ≤ T →
      WeightedFormBound volume volume (fun x => -(a * configurationOneNorm x)) (fun y => a * configurationOneNorm y)
        p (p / (p - 1)) (momentKernel n θ t) (ENNReal.ofReal c) := by
  classical
  obtain ⟨c, hc, hDiagram⟩ := weightedFormBound_diagramKernel_conj_le n θ T hp ha
  obtain ⟨rate, B, hrate, hRate0, hB, hSummable, hCount⟩ :=
    exists_summable_conjugated_diagram_majorant n c T hc
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  have hL : 0 < Real.log (rate - c - 1) := Real.log_pos (by linarith only [hrate])
  let b : ℕ → ℝ := fun m => B * ((m : ℝ) + 1) ^ 3 * (1 / 2 : ℝ) ^ m
  let d : ℕ → ℝ := fun m => c ^ (m + 1) * ((m : ℝ) + 1) ^ 3 *
    (c / Real.log (rate - c - 1)) ^ m * Real.exp (rate * max T 1)
  let D : ℝ≥0∞ := ∑' m : ℕ, ENNReal.ofReal (b m)
  have hb (m : ℕ) : 0 ≤ b m := by dsimp [b]; positivity
  have hDt : D ≠ ⊤ := by
    change (∑' m : ℕ, ENNReal.ofReal (b m)) ≠ ⊤
    rw [← ENNReal.ofReal_tsum_of_nonneg hb hSummable]
    exact ENNReal.ofReal_ne_top
  have hCountCoeff (m : ℕ) :
      (∑' w : CollisionWord n (m + 1), ENNReal.ofReal (d m)) ≤ ENNReal.ofReal (b m) := by
    have hSum : (∑' w : CollisionWord n (m + 1), ENNReal.ofReal (d m)) =
        ENNReal.ofReal ((Fintype.card (CollisionWord n (m + 1)) : ℝ) * d m) := by
      simp only [tsum_fintype, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    rw [hSum]
    exact ENNReal.ofReal_le_ofReal (hCount m)
  let W : ℝ := weightGrowth n a (max T 1)
  let M : ℝ≥0∞ := ENNReal.ofReal W + D
  have hMt : M ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, hDt⟩
  let C : ℝ := M.toReal + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hCoeff : M ≤ ENNReal.ofReal C := by
    calc
      M = ENNReal.ofReal M.toReal := (ENNReal.ofReal_toReal hMt).symm
      _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal (by dsimp [C]; linarith)
  refine ⟨C, hC, ?_⟩
  intro t ht htT
  have htMax : t ≤ max T 1 := htT.trans (le_max_left _ _)
  let K : ℕ → Configuration n → Configuration n → ℝ≥0∞ := fun m x y =>
    ∑ w : CollisionWord n (m + 1), diagramKernel θ (List.ofFn w.1) t x y
  have hWordMeas (m : ℕ) (w : CollisionWord n (m + 1)) :
      Measurable (Function.uncurry (fun x y : Configuration n => diagramKernel θ (List.ofFn w.1) t x y)) :=
    measurable_diagramKernel_comp (List.ofFn w.1) measurable_const measurable_const measurable_fst measurable_snd
  have hKMeas (m : ℕ) : Measurable (Function.uncurry (K m)) := by
    dsimp [K]
    apply Finset.measurable_sum
    intro w _
    exact hWordMeas m w
  have hWordBound (m : ℕ) (w : CollisionWord n (m + 1)) :
      WeightedFormBound volume volume (fun x => -(a * configurationOneNorm x))
        (fun y => a * configurationOneNorm y) p (p / (p - 1))
        (fun x y : Configuration n => diagramKernel θ (List.ofFn w.1) t x y) (ENNReal.ofReal (d m)) := by
    have hExp : Real.exp (rate * t) ≤ Real.exp (rate * max T 1) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htMax hRate0)
    apply (hDiagram rate hrate m w t ht htT).mono (fun _ _ => le_rfl)
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left hExp (by positivity)
  have hKBound (m : ℕ) :
      WeightedFormBound volume volume (fun x => -(a * configurationOneNorm x))
        (fun y => a * configurationOneNorm y) p (p / (p - 1)) (K m) (ENNReal.ofReal (b m)) := by
    have h := WeightedFormBound.tsum (fun w : CollisionWord n (m + 1) => hWordMeas m w)
      (fun w : CollisionWord n (m + 1) => hWordBound m w)
    have h' := h.mono (fun _ _ => le_rfl) (hCountCoeff m)
    simpa only [K, tsum_fintype] using h'
  have hSeriesMeas : Measurable (Function.uncurry (fun x y : Configuration n => ∑' m : ℕ, K m x y)) := by
    apply Measurable.tsum
    intro m
    exact hKMeas m
  have hSeries := WeightedFormBound.tsum hKMeas hKBound
  have hGrowth : weightGrowth n a t ≤ W := by
    unfold weightGrowth W
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htMax (by positivity))) (by positivity)
  have hFree := (weightedFormBound_freeKernel_conj n hp ha ht).mono (fun _ _ => le_rfl)
    (ENNReal.ofReal_le_ofReal hGrowth)
  have hFreeMeas : Measurable (Function.uncurry
      (fun x y : Configuration n => ENNReal.ofReal (freeKernel n t x y))) :=
    (Measurable.comp
      (g := fun q : ℝ × Configuration n × Configuration n => freeKernel n q.1 q.2.1 q.2.2)
      (f := fun q : Configuration n × Configuration n => (t, q))
      (measurable_freeKernel n) (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hAll := WeightedFormBound.add hFreeMeas hSeriesMeas hFree hSeries
  change WeightedFormBound volume volume (fun x => -(a * configurationOneNorm x))
    (fun y => a * configurationOneNorm y) p (p / (p - 1)) (momentKernel n θ t) M at hAll
  exact hAll.mono (fun _ _ => le_rfl) hCoeff

end Critical2DKPZ.SHF.Tsai

end
