/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.LaplaceComposition
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas

/-! # Supremum kernels over a positive-time tail -/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- The pointwise supremum over times `τ ≥ τ₀` of the damped kernel. -/
noncomputable def supTimeKernel {X Y : Type*} (rate τ₀ : ℝ) (K : TimeKernel X Y)
    (x : X) (y : Y) : ℝ≥0∞ :=
  ⨆ τ : {t : ℝ // τ₀ ≤ t}, laplaceTimeWeight rate τ.1 * K (τ.1, x, y)

/-- Every time in the tail is bounded by its supremum kernel. -/
theorem le_supTimeKernel {X Y : Type*} (rate : ℝ) (K : TimeKernel X Y)
    {τ₀ τ : ℝ} (h : τ₀ ≤ τ) (x : X) (y : Y) :
    laplaceTimeWeight rate τ * K (τ, x, y) ≤ supTimeKernel rate τ₀ K x y := by
  exact le_iSup_of_le ⟨τ, h⟩ le_rfl


/-- Joint measurability of the tail supremum when the kernel is continuous in
positive time. The real supremum equals the countable supremum over rational
times in the same tail. -/
theorem measurable_supTimeKernel {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    {K : TimeKernel X Y} (hK : Measurable K)
    (hc : ∀ x y, ContinuousOn (fun τ => K (τ, x, y)) (Ioi 0))
    (rate : ℝ) {τ₀ : ℝ} (hτ₀ : 0 < τ₀) :
    Measurable (Function.uncurry (supTimeKernel rate τ₀ K)) := by
  classical
  let R := {q : ℚ // τ₀ ≤ (q : ℝ)}
  have hWeight : Continuous (fun t : ℝ => laplaceTimeWeight rate t) := by
    unfold laplaceTimeWeight
    exact ENNReal.continuous_ofReal.comp
      (Real.continuous_exp.comp (by fun_prop))
  have hWeightPos (t : ℝ) : 0 < laplaceTimeWeight rate t := by
    unfold laplaceTimeWeight
    positivity
  have hWeightTop (t : ℝ) : laplaceTimeWeight rate t ≠ ⊤ := by
    simp [laplaceTimeWeight]
  have hTimeCont (x : X) (y : Y) :
      ContinuousOn (fun t : ℝ => laplaceTimeWeight rate t * K (t, x, y)) (Ioi 0) := by
    apply hWeight.continuousOn.ennreal_mul (hc x y)
    · intro t ht
      exact Or.inl (ne_of_gt (hWeightPos t))
    · intro t ht
      exact Or.inr (hWeightTop t)
  have hRMeas (q : R) : Measurable (fun p : X × Y =>
      laplaceTimeWeight rate (q.1 : ℝ) * K (q.1, p.1, p.2)) := by
    exact measurable_const.mul (hK.comp (by fun_prop))
  have hRatSup : Measurable (fun p : X × Y =>
      ⨆ q : R, laplaceTimeWeight rate (q.1 : ℝ) * K (q.1, p.1, p.2)) :=
    Measurable.iSup hRMeas
  have hSupEq (x : X) (y : Y) :
      supTimeKernel rate τ₀ K x y =
        ⨆ q : R, laplaceTimeWeight rate (q.1 : ℝ) * K (q.1, x, y) := by
    apply le_antisymm
    · let H : ℝ → ℝ≥0∞ := fun t => laplaceTimeWeight rate t * K (t, x, y)
      change (⨆ t : {t : ℝ // τ₀ ≤ t}, H t.1) ≤
        ⨆ q : R, laplaceTimeWeight rate (q.1 : ℝ) * K (q.1, x, y)
      apply iSup_le
      intro t
      have hAt : 0 < t.1 := lt_of_lt_of_le hτ₀ t.2
      obtain ⟨u, huAnti, hAbove, hu⟩ :=
        Real.exists_seq_rat_strictAnti_tendsto t.1
      have hContAt : ContinuousAt H t.1 :=
        (hTimeCont x y).continuousAt (isOpen_Ioi.mem_nhds hAt)
      have hLimit : Tendsto (fun n => H (u n : ℝ)) atTop (nhds (H t.1)) :=
        hContAt.tendsto.comp hu
      have hBound (n : ℕ) : H (u n : ℝ) ≤
          ⨆ r : R, laplaceTimeWeight rate (r.1 : ℝ) * K (r.1, x, y) := by
        have hTail : τ₀ ≤ (u n : ℝ) := le_trans t.2 (le_of_lt (hAbove n))
        exact le_iSup_of_le ⟨u n, hTail⟩ le_rfl
      exact le_of_tendsto hLimit (Filter.Eventually.of_forall hBound)
    · change (⨆ q : R, laplaceTimeWeight rate (q.1 : ℝ) * K (q.1, x, y)) ≤
        ⨆ t : {t : ℝ // τ₀ ≤ t}, laplaceTimeWeight rate t.1 * K (t.1, x, y)
      apply iSup_le
      intro q
      exact le_iSup_of_le ⟨(q.1 : ℝ), q.2⟩ le_rfl
  have hEq : supTimeKernel rate τ₀ K = fun x y =>
      ⨆ q : R, laplaceTimeWeight rate (q.1 : ℝ) * K (q.1, x, y) := by
    funext x y
    exact hSupEq x y
  rw [hEq]
  exact hRatSup


end Critical2DKPZ.DeltaBose
