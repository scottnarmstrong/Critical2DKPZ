/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ChainCauchyFour
public import Critical2DKPZ.SHF.Tsai.FourthMomentTransitivity

/-! # Common fourth-moment limits of mollified chains

Independent blocks with delta-Bose moments have a common measurable `L⁴` pairing limit
for every applicable mollifier family.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace Critical2DKPZ.SHF.Tsai

local instance instFactOneLeFourENNRealUniversal : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- Independent moment blocks have a common `L⁴` pairing limit for every applicable mollifier family. -/
theorem exists_chainPairing_four_limit_universal {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (K : ℕ) (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k)
    (B : ℕ → Ω → Measure (Plane × Plane)) (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hind : iIndepFun (fun k : Fin (K + 1) => B k) P)
    (u : ℕ → ℕ → Plane → ℝ) (hu : ∀ k, IsL2ApplicableMollifier (u k))
    (g g' : Plane → ℝ) (hg : MemLp g 2) (hg' : MemLp g' 2) :
    ∃ F : Ω → ℝ, MemLp F 4 P ∧ ∀ v : ℕ → ℕ → Plane → ℝ,
      (∀ k, IsL2ApplicableMollifier (v k)) →
      (∀ ℓ, Integrable (fun ω => ((∫ p, g p.1 * g' p.2
        ∂chainProduct (fun k => B k ω) (fun k => v k ℓ) K) - F ω) ^ 4) P) ∧
      Tendsto (fun ℓ => ∫ ω, ((∫ p, g p.1 * g' p.2
        ∂chainProduct (fun k => B k ω) (fun k => v k ℓ) K) - F ω) ^ 4 ∂P) atTop (𝓝 0) := by
  let X (v : ℕ → ℕ → Plane → ℝ) (ℓ : ℕ) (ω : Ω) := ∫ p, g p.1 * g' p.2
    ∂chainProduct (fun k => B k ω) (fun k => v k ℓ) K
  have hmem (v) (hv : ∀ k, IsL2ApplicableMollifier (v k)) (ℓ) : MemLp (X v ℓ) 4 P :=
    memLp_chainPairing_four K τ hτ B hB hind v hv ℓ g g' hg hg'
  obtain ⟨F, hF⟩ := exists_chainPairing_toLp_four_limit K τ hτ B hB hind u hu g g' hg hg'
  have hnorm0 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ F).1 hF
  have hnorm : Tendsto (fun ℓ => eLpNorm (fun ω => X u ℓ ω - F ω) 4 P) atTop (𝓝 0) := by
    apply hnorm0.congr
    intro ℓ
    exact eLpNorm_congr_ae ((hmem u hu ℓ).coeFn_toLp.sub EventuallyEq.rfl)
  have hI (ℓ) : Integrable (fun ω => (X u ℓ ω - F ω) ^ 4) P := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs, Even.pow_abs (show Even 4 from ⟨2, rfl⟩)] using
      ((hmem u hu ℓ).sub (Lp.memLp F)).integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
  have hlim := tendsto_integral_pow_four_of_eLpNorm P (fun ℓ ω => X u ℓ ω - F ω)
    (fun ℓ => ((hmem u hu ℓ).sub (Lp.memLp F)).aestronglyMeasurable) hI hnorm
  refine ⟨F, Lp.memLp F, fun v hv => ?_⟩
  have hcompare := tendsto_integral_chainProduct_sub_pow_four K τ hτ B hB hind v u hv hu g g' hg hg'
  exact tendsto_integral_sub_pow_four_trans P (X v) (X u) F (hmem v hv) (hmem u hu)
    (Lp.memLp F) hcompare.2 hlim

end Critical2DKPZ.SHF.Tsai

end
