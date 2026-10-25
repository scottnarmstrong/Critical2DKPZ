/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.Definitions.ScaledPairing
public import Critical2DKPZ.Extensions.Definitions.IsWienerLaw
import Critical2DKPZ.Analysis.Sobolev.TestFunctionFamily

/-!
# The scale clock and continuity of the tested distribution

The scale widths and tested pairings are given by their defining formulas.
Compact support is uniform over widths in `(0,1]`, allowing continuity in the
LF test-function topology.
-/

@[expose] public section

noncomputable section

open TopologicalSpace
open scoped Topology NNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The scale width is strictly positive. -/
theorem scaleRadius_pos (L s : ℝ) : 0 < scaleRadius L s :=
  Real.exp_pos _

/-- The scale width is always below one, including at scale time zero. -/
theorem scaleRadius_lt_one (L s : ℝ) : scaleRadius L s < 1 :=
  Real.exp_lt_one_iff.mpr (neg_neg_of_pos (Real.exp_pos _))


/-- The doubly logarithmic clock is exact, with no asymptotic error. -/
theorem log_log_inv_scaleRadius (L s : ℝ) :
    Real.log (Real.log (scaleRadius L s)⁻¹) = L * s := by
  rw [scaleRadius, Real.log_inv, Real.log_exp, neg_neg, Real.log_exp]

/-- All widths in `(0,1]` share a common compact support after dilation. -/
theorem exists_compact_dilate_support (φ : TestFn) (x : Plane) :
    ∃ K : Compacts Plane, ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
      tsupport (φ.dilate ε x) ⊆ K := by
  let K : Set Plane := (fun p : ℝ × Plane => x + p.1 • p.2) ''
    (Set.Icc (0 : ℝ) 1 ×ˢ tsupport φ)
  have hK : IsCompact K :=
    (isCompact_Icc.prod φ.hasCompactSupport.isCompact).image (by fun_prop)
  refine ⟨⟨K, hK⟩, ?_⟩
  intro ε hε
  apply closure_minimal ?_ hK.isClosed
  intro y hy
  have hφ : φ (ε⁻¹ • (y - x)) ≠ 0 := by
    intro hz
    apply hy
    change ε⁻¹ ^ 2 * φ (ε⁻¹ • (y - x)) = 0
    rw [hz, mul_zero]
  refine ⟨(ε, ε⁻¹ • (y - x)), ⟨⟨hε.1.le, hε.2⟩, subset_tsupport φ hφ⟩, ?_⟩
  dsimp
  rw [smul_smul, mul_inv_cancel₀ hε.1.ne', one_smul, add_sub_cancel]

/-- The scale radius is a smooth function of the scale time. -/
theorem contDiff_scaleRadius (L : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => scaleRadius L s) := by
  unfold scaleRadius
  exact (Real.contDiff_exp.comp ((Real.contDiff_exp.comp
    (contDiff_const.mul contDiff_id)).neg))

/-- Scale dilation depends continuously on the scale time in the test topology. -/
theorem continuous_scaleRadius_dilate (φ : TestFn) (x : Plane) (L : ℝ) :
    Continuous (fun s : ℝ => φ.dilate (scaleRadius L s) x) := by
  obtain ⟨K, hK⟩ := exists_compact_dilate_support φ x
  apply continuous_testFn_family K
  · intro s
    exact hK _ ⟨scaleRadius_pos L s, (scaleRadius_lt_one L s).le⟩
  · have hr : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : ℝ × Plane => (scaleRadius L p.1)⁻¹) :=
      ((contDiff_scaleRadius L).comp contDiff_fst).inv
        (fun p => (scaleRadius_pos L p.1).ne')
    change ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Plane =>
      (scaleRadius L p.1)⁻¹ ^ 2 * φ ((scaleRadius L p.1)⁻¹ • (p.2 - x)))
    exact (hr.pow 2).mul (φ.contDiff.comp (hr.smul (contDiff_snd.sub contDiff_const)))

/-- A distribution tested at the shrinking scale is a continuous real path. -/
theorem continuous_scaledPairing (T : Distr) (φ : TestFn) (x : Plane)
    (L : Set.Ioi (0 : ℝ)) :
    Continuous (fun s : ℝ => scaledPairing T φ x L s) :=
  (T.continuous.comp (continuous_scaleRadius_dilate φ x L)).div_const _

/-- The literal continuous path specified by the scale pairing. -/
def scalePath (S : ℝ≥0) (T : Distr) (φ : TestFn) (x : Plane)
    (L : Set.Ioi (0 : ℝ)) : ScalePath S :=
  ⟨fun s => scaledPairing T φ x L s,
    (continuous_scaledPairing T φ x L).comp continuous_subtype_val⟩



end Critical2DKPZ.Extensions.ScaleLimit
