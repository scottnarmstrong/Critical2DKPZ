/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.CovarianceKernel.WeakLpCompactness

/-! # Order properties of weak limits in real `L²` -/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace Critical2DKPZ.CovarianceKernel

/-- Weak limits in real `L²` preserve almost-everywhere nonnegativity. -/
theorem ae_nonneg_of_weak_L2_inner_tendsto
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (u : ℕ → Lp ℝ 2 μ) (v : Lp ℝ 2 μ)
    (hweak : ∀ g : Lp ℝ 2 μ,
      Tendsto (fun n => inner ℝ (u n) g) atTop (𝓝 (inner ℝ v g)))
    (hu : ∀ n, ∀ᵐ x ∂μ, 0 ≤ u n x) :
    ∀ᵐ x ∂μ, 0 ≤ v x := by
  let g : α → ℝ := fun x => max (-v x) 0
  have hv : MemLp (fun x => v x) 2 μ := Lp.memLp v
  have hgstrong : AEStronglyMeasurable g μ := by
    have hcont : Continuous (fun x : ℝ => max (-x) 0) :=
      continuous_id.neg.max continuous_const
    simpa [g] using hcont.comp_aestronglyMeasurable hv.aestronglyMeasurable
  have hgbound : ∀ᵐ x ∂μ, ‖g x‖ ≤ 1 * ‖v x‖ := by
    filter_upwards [] with x
    by_cases hx : v x ≤ 0
    · have hneg : 0 ≤ -v x := neg_nonneg.mpr hx
      simp [g, max_eq_left hneg, Real.norm_eq_abs]
    · have hpos : 0 < v x := lt_of_not_ge hx
      have hneg : -v x ≤ 0 := le_of_lt (neg_neg_of_pos hpos)
      simp [g, max_eq_right hneg, Real.norm_eq_abs]
  have hgmem : MemLp g 2 μ := hv.of_le_mul hgstrong hgbound
  let G : Lp ℝ 2 μ := hgmem.toLp g
  have hGnonneg (x : α) : 0 ≤ g x := le_max_right _ _
  have hseq : ∀ n, 0 ≤ inner ℝ (u n) G := by
    intro n
    rw [L2.inner_def]
    simp only [Real.inner_apply]
    apply integral_nonneg_of_ae
    filter_upwards [hu n, hgmem.coeFn_toLp] with x hux hGx
    rw [hGx]
    exact mul_nonneg hux (hGnonneg x)
  have hlim : 0 ≤ inner ℝ v G :=
    ge_of_tendsto (hweak G) (Filter.Eventually.of_forall hseq)
  have hEq : (fun x => v x * G x) =ᵐ[μ] fun x => -(g x ^ 2) := by
    filter_upwards [hgmem.coeFn_toLp] with x hGx
    rw [hGx]
    by_cases hx : v x ≤ 0
    · have hneg : 0 ≤ -v x := neg_nonneg.mpr hx
      simp [g, max_eq_left hneg]
      ring
    · have hpos : 0 < v x := lt_of_not_ge hx
      have hneg : -v x ≤ 0 := le_of_lt (neg_neg_of_pos hpos)
      simp [g, max_eq_right hneg]
  have hGsq : (fun x => g x ^ 2) =ᵐ[μ] fun x => G x * G x := by
    filter_upwards [hgmem.coeFn_toLp] with x hGx
    rw [hGx]
    ring
  have hinner : inner ℝ v G = -‖G‖ ^ 2 := by
    calc
      inner ℝ v G = ∫ x, v x * G x ∂μ := by
        rw [L2.inner_def]
        simp only [Real.inner_apply]
      _ = - ∫ x, g x ^ 2 ∂μ := by
        rw [integral_congr_ae hEq, integral_neg]
      _ = - ∫ x, G x * G x ∂μ := by
        congr 1
        exact integral_congr_ae hGsq
      _ = -‖G‖ ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, L2.inner_def]
        simp only [Real.inner_apply]
  have hGzero : ‖G‖ = 0 := by nlinarith [norm_nonneg G]
  have hG0 : G = 0 := norm_eq_zero.mp hGzero
  have hgzero : g =ᵐ[μ] 0 := by
    filter_upwards [hgmem.coeFn_toLp, Lp.coeFn_zero ℝ 2 μ] with x hGx hzero
    have hGx0 : G x = 0 := by rw [hG0]; exact hzero
    rw [← hGx, hGx0]
    rfl
  filter_upwards [hgzero] with x hx
  change g x = 0 at hx
  by_contra hnot
  have hpos : 0 < -v x := by linarith
  have : g x = -v x := max_eq_left hpos.le
  rw [this] at hx
  linarith

end Critical2DKPZ.CovarianceKernel

end
