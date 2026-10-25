/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ChainCauchyFour
public import Critical2DKPZ.SHF.Tsai.LpLimitIdentification

/-! # Identification of the fourth-moment chain limit

For independent moment blocks the actual chain pairings are Cauchy in `L⁴`.
Any identification of their limit in probability consequently identifies
their fourth-moment limit as well, with integrability of every error.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace Critical2DKPZ.SHF.Tsai

local instance instFactOneLeFourENNRealIdentification : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- Identification in measure of an independent chain upgrades to fourth-moment convergence. -/
theorem tendsto_integral_chainPairing_sub_pow_four_of_tendstoInMeasure
    {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (K : ℕ) (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k)
    (B : ℕ → Ω → Measure (Plane × Plane)) (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hind : iIndepFun (fun k : Fin (K + 1) => B k) P)
    (w : ℕ → ℕ → Plane → ℝ) (hw : ∀ k, IsL2ApplicableMollifier (w k))
    (g g' : Plane → ℝ) (hg : MemLp g 2) (hg' : MemLp g' 2) (F : Ω → ℝ)
    (hconv : TendstoInMeasure P (fun ℓ ω => ∫ p, g p.1 * g' p.2
      ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K) atTop F) :
    MemLp F 4 P ∧
    (∀ ℓ, Integrable (fun ω => ((∫ p, g p.1 * g' p.2
      ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K) - F ω) ^ 4) P) ∧
    Tendsto (fun ℓ => ∫ ω, ((∫ p, g p.1 * g' p.2
      ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K) - F ω) ^ 4 ∂P) atTop (𝓝 0) := by
  let φ (ℓ : ℕ) (ω : Ω) := ∫ p, g p.1 * g' p.2
    ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K
  have hφ (ℓ) : MemLp (φ ℓ) 4 P := memLp_chainPairing_four K τ hτ B hB hind w hw ℓ g g' hg hg'
  obtain ⟨hF, hlim⟩ := tendsto_eLpNorm_sub_of_cauchySeq_of_tendstoInMeasure P φ hφ F
    (cauchySeq_chainPairing_toLp_four K τ hτ B hB hind w hw g g' hg hg') hconv
  have hδ (ℓ) : MemLp (φ ℓ - F) 4 P := (hφ ℓ).sub hF
  have hI (ℓ) : Integrable (fun ω => (φ ℓ ω - F ω) ^ 4) P := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs, Even.pow_abs (show Even 4 from ⟨2, rfl⟩)] using
      (hδ ℓ).integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
  exact ⟨hF, hI, tendsto_integral_pow_four_of_eLpNorm P (fun ℓ ω => φ ℓ ω - F ω)
    (fun ℓ => (hδ ℓ).aestronglyMeasurable) hI hlim⟩

end Critical2DKPZ.SHF.Tsai

end
