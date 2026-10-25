/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.KernelProductL2
import Critical2DKPZ.Polymer.SummableCovariance
import Mathlib.Tactic

/-! # Square integrability of separated polymer slab products -/

@[expose] public noncomputable section

open MeasureTheory
open Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Tsai
open scoped CompactlySupported ENNReal

namespace Critical2DKPZ.SHF.Flow

/-- The separated polymer slab product belongs to `L²` at every finite scale. -/
theorem memLp_slabProduct_two (ϑ : ℝ) (N : ℕ) {s t t' u : ℝ}
    (_hs : 0 ≤ s) (_hst : s < t) (_htt' : t < t') (_ht'u : t' < u)
    (Φ : C_c(Plane × Plane, ℝ)) :
    MemLp (fun ω => kernelProductPairing (polymerMeasure ϑ N s t ω)
      (slabMeanKernel ϑ N t t') (polymerMeasure ϑ N t' u ω) Φ) 2 disorderLaw := by
  have hm : Measurable (fun p : Plane × Plane => slabMeanKernel ϑ N t t' p.1 p.2) := by
    rw [show (fun p : Plane × Plane => slabMeanKernel ϑ N t t' p.1 p.2) =
      (fun z : Site => (N : ℝ) / 4 *
        srwKernel (evenCeil ((N : ℝ) * t') - evenCeil ((N : ℝ) * t)) z) ∘
        (fun p : Plane × Plane => latticePoint N p.2 - latticePoint N p.1) from by
          funext p
          rw [slabMeanKernel_eq_srwKernel]
          rfl]
    apply (measurable_of_countable _).comp
    exact (measurable_of_countable fun z : Site × Site => z.1 - z.2).comp
      (((measurable_latticePoint N).comp measurable_snd).prodMk
        ((measurable_latticePoint N).comp measurable_fst))
  have hb (p : Plane × Plane) : ‖slabMeanKernel ϑ N t t' p.1 p.2‖ ≤ (N : ℝ) / 4 := by
    rw [slabMeanKernel_eq_srwKernel, norm_mul,
      Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (N : ℝ) / 4),
      Real.norm_eq_abs, abs_of_nonneg (srwKernel_nonneg _ _)]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (Polymer.srwKernel_le_one _ _)
        (by positivity : 0 ≤ (N : ℝ) / 4)
  exact memLp_kernelProductPairing_two ϑ N s t t' u Φ
    (fun p => slabMeanKernel ϑ N t t' p.1 p.2) hm ((N : ℝ) / 4) hb

/-- The separated smoothed slab product belongs to `L²` at every finite scale. -/
theorem memLp_slabSmoothedProduct_two (ϑ : ℝ) (N : ℕ) {s t t' u : ℝ}
    (_hs : 0 ≤ s) (_hst : s < t) (_htt' : t < t') (_ht'u : t' < u)
    (Φ : C_c(Plane × Plane, ℝ)) (w : Plane → ℝ) (hw : Continuous w)
    (hwc : HasCompactSupport w) :
    MemLp (fun ω => kernelProductPairing (polymerMeasure ϑ N s t ω)
      (fun a b => ∫ y, w (a - y) * slabMeanKernel ϑ N t t' y b)
      (polymerMeasure ϑ N t' u ω) Φ) 2 disorderLaw := by
  classical
  by_cases hN : N = 0
  · subst N
    simp [polymerMeasure_zero_at_zero, kernelProductPairing]
  obtain ⟨C, hC⟩ := exists_slabSmoothedConnector_bound ϑ N (Nat.pos_of_ne_zero hN)
    t t' w hw hwc
  exact memLp_kernelProductPairing_two ϑ N s t t' u Φ
    (fun p => slabSmoothedConnector ϑ N t t' w p.1 p.2)
    (measurable_slabSmoothedConnector ϑ N t t' w hw hwc) C (fun p => hC p.1 p.2)

end Critical2DKPZ.SHF.Flow
