/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.ThinSlabVaryingCutoffConnector
public import Critical2DKPZ.SHF.Flow.KernelProductL2
public import Critical2DKPZ.SHF.Flow.KernelProductCutoffUniform
public import Mathlib.Tactic
public import Critical2DKPZ.SHF.Flow.ThinSlabSecondMomentApproximation
import Mathlib.Tactic

/-! # Existence of uncut second-moment limits for smooth connectors -/

@[expose] public noncomputable section
open MeasureTheory Filter Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Tsai
open scoped CompactlySupported Topology
namespace Critical2DKPZ.SHF.Flow

/-- For locally uniformly convergent connectors with a common Gaussian bound, the uncut pairing has a second-moment limit, including on touching polymer intervals. Square integrability is supplied by `memLp_kernelProductPairing_two` and `memLp_kernelProductCutoffPairing_two`. -/
theorem exists_slabConnector_secondMoment_limit_with_cutoffs (ϑ : ℝ)
    (hPolymerMomentInput : PolymerMomentLimit ϑ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
    {s t r u : ℝ} (hs : 0 ≤ s) (hst : s < t) (htr : t ≤ r) (hru : r < u)
    (Φ : C_c(Plane × Plane, ℝ)) (κ : ℕ → Plane × Plane → ℝ)
    (hκm : ∀ N, Measurable (κ N)) (κlim : C(Plane × Plane, ℝ))
    (hUniform : ∀ K : Set (Plane × Plane), IsCompact K → ∀ δ > 0,
      ∀ᶠ N : ℕ in atTop, ∀ p ∈ K, |κ N p - κlim p| ≤ δ)
    (hκ : ∃ C c : ℝ, 0 < c ∧ ∀ N a b,
      |κ N (a, b)| ≤ C * Real.exp (-c * ‖a - b‖ ^ 2)) :
    ∃ L : ℝ, Tendsto (fun N => ∫ ω,
      kernelProductPairing (polymerMeasure ϑ N s t ω) (fun a b => κ N (a, b))
        (polymerMeasure ϑ N r u ω) Φ ^ 2 ∂disorderLaw) atTop (𝓝 L) ∧
      Tendsto (fun R => slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant)
        (t - s) (u - r) (slabReplicaSourceTest (slabCutoffConnectorTest Φ κlim R)))
        atTop (𝓝 L) := by
  obtain ⟨C, c, hc, hEnvelope⟩ := hκ
  have hC : 0 ≤ C := by
    have h := hEnvelope 0 0 0
    simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero, Real.exp_zero, mul_one] at h
    exact (abs_nonneg _).trans h
  have hBound (N : ℕ) (p : Plane × Plane) : ‖κ N p‖ ≤ C := by
    rw [Real.norm_eq_abs]
    calc
      _ ≤ C * Real.exp (-c * ‖p.1 - p.2‖ ^ 2) := hEnvelope N p.1 p.2
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left
        (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith only [hc])
          (sq_nonneg _))) hC
      _ = C := mul_one C
  let f : ℕ → Disorder → ℝ := fun N ω =>
    kernelProductPairing (polymerMeasure ϑ N s t ω) (fun a b => κ N (a, b))
      (polymerMeasure ϑ N r u ω) Φ
  let g : ℝ → ℕ → Disorder → ℝ := fun R N ω =>
    ∫ q, Φ (q.1.1, q.2.2) * κ N (q.1.2, q.2.1) *
      ballCutoff R q.1.2 * ballCutoff R q.2.1 ∂
        ((polymerMeasure ϑ N s t ω).prod (polymerMeasure ϑ N r u ω))
  have hfull (N : ℕ) : MemLp (f N) 2 disorderLaw :=
    memLp_kernelProductPairing_two ϑ N s t r u Φ (κ N) (hκm N) C (hBound N)
  have hcut (R : ℝ) (N : ℕ) : MemLp (g R N) 2 disorderLaw :=
    memLp_kernelProductCutoffPairing_two ϑ N s t r u Φ (κ N) (hκm N) C R (hBound N)
  apply exists_secondMoment_limit_with_cutoffs disorderLaw f g
    (fun R => slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r)
      (slabReplicaSourceTest (slabCutoffConnectorTest Φ κlim R)))
  · exact Eventually.of_forall fun N => (hfull N).integrable_sq
  · exact fun R => Eventually.of_forall fun N => (hcut R N).integrable_sq
  · exact fun R => Eventually.of_forall fun N => ((hfull N).sub (hcut R N)).integrable_sq
  · exact kernelProduct_cutoff_tail ϑ hs hst htr hru Φ (fun N a b => κ N (a, b)) hκm
      ⟨C, c, hc, hEnvelope⟩
  · exact fun R => tendsto_slabVaryingCutoffConnector_sq ϑ hPolymerMomentInput hFlatSixthMomentInput hs hst htr hru
      Φ κ hκm κlim hUniform R


end Critical2DKPZ.SHF.Flow
end
