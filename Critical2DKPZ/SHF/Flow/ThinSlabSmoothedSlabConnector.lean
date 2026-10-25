/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.SlabMeanKernelLimit
public import Critical2DKPZ.SHF.Flow.SlabMeanKernelGaussianBound
public import Critical2DKPZ.SHF.Flow.SlabSmoothedBridge
import Mathlib.Tactic

/-! # Compact convergence of the annealed smoothed slab connector -/

@[expose] public noncomputable section

open MeasureTheory Filter Set Critical2DKPZ.SHF.Limit

namespace Critical2DKPZ.SHF.Flow

/-- The slab mean is jointly measurable in its two spatial endpoints. -/
theorem measurable_slabMeanKernel (ϑ : ℝ) (N : ℕ) (t t' : ℝ) :
    Measurable (fun p : Plane × Plane => slabMeanKernel ϑ N t t' p.1 p.2) := by
  simp_rw [slabMeanKernel_eq_srwKernel]
  apply measurable_const.mul
  have hwalk : Measurable (fun z : Site =>
      srwKernel (evenCeil ((N : ℝ) * t') - evenCeil ((N : ℝ) * t)) z) :=
    measurable_of_countable _
  exact hwalk.comp
    (((measurable_latticePoint N).comp measurable_snd).sub
      ((measurable_latticePoint N).comp measurable_fst))

/-- The fixed positive slab connector has one finite bound, uniform in scale
and spatial endpoints. -/
theorem exists_slabMeanKernel_bound (ϑ : ℝ) {t v : ℝ} (ht : 0 ≤ t) (hv : 0 < v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N x y, |slabMeanKernel ϑ N t (t + v) x y| ≤ C := by
  obtain ⟨C, c, hc, hbound⟩ := exists_slabMeanKernel_gaussianBound ϑ ht hv
  refine ⟨|C|, abs_nonneg C, ?_⟩
  intro N x y
  have hexp : Real.exp (-c * ‖y - x‖ ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (sq_nonneg _))
  exact (hbound N x y).trans
    ((mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp (abs_nonneg C)))

/-- A compact continuous convolution profile preserves uniform convergence
of the slab mean on compact endpoint sets. The profile need not be normalized. -/
theorem tendsto_slabSmoothedConnector_uniformOn_compact (ϑ : ℝ)
    {t v : ℝ} (ht : 0 ≤ t) (hv : 0 < v) (k : Plane → ℝ)
    (hk : Continuous k) (hkc : HasCompactSupport k)
    (K : Set (Plane × Plane)) (hK : IsCompact K) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ a b, (a, b) ∈ K →
      |slabSmoothedConnector ϑ N t (t + v) k a b -
        ∫ y, k (a - y) * heatKernel v (b - y)| < ε := by
  intro ε hε
  let M : ℝ := ∫ z, |k z|
  have hM : 0 ≤ M := integral_nonneg fun z => abs_nonneg (k z)
  let δ : ℝ := ε / (M + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδM : δ * M < ε := by
    have heq : δ * (M + 1) = ε := by dsimp [δ]; field_simp
    nlinarith only [hδ, heq]
  let K' : Set (Plane × Plane) :=
    (fun q : (Plane × Plane) × Plane => (q.1.1 - q.2, q.1.2)) '' (K ×ˢ tsupport k)
  have hK' : IsCompact K' := (hK.prod hkc).image (by fun_prop)
  have hlocal := tendsto_slabMeanKernel_uniformOn_compact ϑ ht hv K' hK' δ hδ
  obtain ⟨C, _hC, hbound⟩ := exists_slabMeanKernel_bound ϑ ht hv
  filter_upwards [hlocal] with N hN a b hab
  have hweight : Integrable (fun y : Plane => k (a - y)) :=
    (hk.comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport
      (hkc.comp_homeomorph (Homeomorph.subLeft a))
  have hSlabMeas : AEStronglyMeasurable (fun y : Plane => slabMeanKernel ϑ N t (t + v) y b) volume :=
    ((measurable_slabMeanKernel ϑ N t (t + v)).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have hSlab : Integrable (fun y : Plane => k (a - y) * slabMeanKernel ϑ N t (t + v) y b) :=
    hweight.mul_bdd hSlabMeas (Eventually.of_forall fun y => by
      simpa only [Real.norm_eq_abs] using hbound N y b)
  have hHeatMeas : AEStronglyMeasurable (fun y : Plane => heatKernel v (b - y)) volume :=
    ((Critical2DKPZ.continuous_heatKernel v).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hHeat : Integrable (fun y : Plane => k (a - y) * heatKernel v (b - y)) :=
    hweight.mul_bdd hHeatMeas (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (heatKernel_pos hv _).le]
      exact heatKernel_le_at_zero hv.le _)
  have hDifference :
      slabSmoothedConnector ϑ N t (t + v) k a b - (∫ y, k (a - y) * heatKernel v (b - y)) =
        ∫ y, k (a - y) * (slabMeanKernel ϑ N t (t + v) y b - heatKernel v (b - y)) := by
    rw [slabSmoothedConnector, ← integral_sub hSlab hHeat]
    apply integral_congr_ae
    filter_upwards [] with y
    ring
  have hpoint (y : Plane) :
      ‖k (a - y) * (slabMeanKernel ϑ N t (t + v) y b - heatKernel v (b - y))‖ ≤ δ * |k (a - y)| := by
    rw [Real.norm_eq_abs, abs_mul]
    by_cases hzero : k (a - y) = 0
    · simp only [hzero, abs_zero, zero_mul, mul_zero, le_refl]
    · have hmem : (y, b) ∈ K' := by
        refine ⟨((a, b), a - y), ⟨hab, subset_tsupport k hzero⟩, ?_⟩
        ext <;> dsimp
        abel
      have hsmall := (hN y b hmem).le
      simpa only [mul_comm δ] using mul_le_mul_of_nonneg_left hsmall (abs_nonneg (k (a - y)))
  have hIntegral :
      |∫ y, k (a - y) * (slabMeanKernel ϑ N t (t + v) y b - heatKernel v (b - y))| ≤ δ * M := by
    have h := norm_integral_le_of_norm_le (hweight.abs.const_mul δ) (Eventually.of_forall hpoint)
    rw [Real.norm_eq_abs, integral_const_mul,
      integral_sub_left_eq_self (fun z : Plane => |k z|) volume a] at h
    exact h
  rw [hDifference]
  exact hIntegral.trans_lt hδM

end Critical2DKPZ.SHF.Flow

end
