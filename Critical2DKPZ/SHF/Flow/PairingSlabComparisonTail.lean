/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.PairingSlabComparisonPairingMoment
public import Critical2DKPZ.SHF.Flow.KernelProductCutoffUniform
public import Critical2DKPZ.SHF.Flow.SlabMeanKernelGaussianBound

/-! # Gaussian cutoff tails for annealed slab pairings -/

@[expose] public section

open MeasureTheory Filter
open Critical2DKPZ.SHF.Limit
open Critical2DKPZ.SHF.Tsai
open scoped CompactlySupported

namespace Critical2DKPZ.SHF.Flow

/-- The Gaussian cutoff-tail bound applies to a polymer product connected by an annealed slab kernel. -/
theorem slabPairing_cutoff_tail (ϑ : ℝ) {s t u : ℝ} (hs : 0 ≤ s)
    (hst : s < t) (_htu : t < u) (Φ : C_c(Plane × Plane, ℝ)) {v : ℝ}
    (hv : 0 < v) (hvu : t + v < u) :
    ∀ ε > 0, ∃ R₀ : ℝ, ∀ R ≥ R₀, ∀ᶠ N : ℕ in atTop,
      ∫ ω,
        (kernelProductPairing (polymerMeasure ϑ N s t ω)
            (slabMeanKernel ϑ N t (t + v))
            (polymerMeasure ϑ N (t + v) u ω) Φ -
          ∫ q, Φ (q.1.1, q.2.2) * slabMeanKernel ϑ N t (t + v) q.1.2 q.2.1 *
            ballCutoff R q.1.2 * ballCutoff R q.2.1
            ∂((polymerMeasure ϑ N s t ω).prod
              (polymerMeasure ϑ N (t + v) u ω))) ^ 2 ∂disorderLaw ≤ ε := by
  let κ : ℕ → Plane → Plane → ℝ := fun N => slabMeanKernel ϑ N t (t + v)
  have hκm (N : ℕ) : Measurable fun q : Plane × Plane => κ N q.1 q.2 := by
    simpa only [κ] using measurable_slabMeanKernel ϑ N t (t + v)
  obtain ⟨C, c, hc, hκ⟩ :=
    exists_slabMeanKernel_gaussianBound ϑ (le_trans hs hst.le) hv
  exact kernelProduct_cutoff_tail ϑ hs hst
    (le_of_lt (lt_add_of_pos_right t hv)) hvu Φ κ hκm
    ⟨C, c, hc, by
      intro N x y
      simpa only [κ, norm_sub_rev] using hκ N x y⟩

end Critical2DKPZ.SHF.Flow

end
