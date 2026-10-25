/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.RatioVector
import Critical2DKPZ.Extensions.ScaleLimit.LatticeProfileBounds
import Critical2DKPZ.Extensions.ScaleLimit.DistributionBounds
import Mathlib.Tactic

/-! # The uniform geometric flow block-ratio tail -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- A single large-enough geometric ratio admits a uniform flow ratio tail.
Constants are chosen before either endpoint. -/
theorem blockR_prob_bound (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z) :
    ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ → ∃ (C : ℝ) (ℓ₀ : ℕ),
      ∀ n ℓ : ℕ, ℓ₀ ≤ ℓ → ℓ < n →
        P {ω | 1 / 2 < |blockR Z ρ n ℓ ω - 1|} ≤ ENNReal.ofReal (C / ℓ) := by
  obtain ⟨ρ₀, hρ₀, hPE⟩ := lattice_profile_estimates |ϑ|
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro ρ hρ
  have hρ1 : 1 < ρ := hρ₀.trans_le hρ
  obtain ⟨C, ℓPE, hC⟩ := hPE ρ
  refine ⟨C, max ℓPE 1, ?_⟩
  intro n ℓ hℓ hℓn
  have hℓPE : ℓPE ≤ ℓ := (le_max_left _ _).trans hℓ
  have h2 : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    tendsto_atTop_mono (f := fun N : ℕ => N) (fun N => by omega) tendsto_id
  have hbound := h2.eventually (hC ρ ⟨hρ, le_rfl⟩)
  have hK := ((Blocks.blockCount_tendsto_atTop hρ1).comp h2).eventually_ge_atTop n
  have hlattice : ∀ᶠ N : ℕ in atTop,
      disorderLaw (latticeBlockVector ϑ ρ n ℓ N ⁻¹' ratioBadEvent (n - ℓ)) ≤
        ENNReal.ofReal (C / ℓ) := by
    filter_upwards [hbound, hK] with N hN hnK
    change n ≤ blockCount (2 * N) ρ at hnK
    let K := blockCount (2 * N) ρ
    let r := K - n + 1
    let s := K - ℓ
    have hr : 1 ≤ r := by dsimp [r]; omega
    have hrs : r ≤ s := by dsimp [r, s, K]; omega
    have hs : s + ℓPE ≤ K := by dsimp [s, K]; omega
    have hp := (hN ϑ ⟨neg_abs_le ϑ, le_abs_self ϑ⟩ r s hr hrs hs).1
    have hgap : (K : ℝ) - (s : ℝ) = (ℓ : ℝ) := by
      dsimp [s]
      rw [Nat.cast_sub (by dsimp [K]; omega)]
      ring
    change (disorderLaw (FutureProfiles.profileGoodSet (criticalBeta ϑ (2 * N))
      (blockTime (2 * N) ρ) r s)ᶜ).toReal ≤ C / ((K : ℝ) - (s : ℝ)) at hp
    rw [hgap] at hp
    have hsubset : latticeBlockVector ϑ ρ n ℓ N ⁻¹' ratioBadEvent (n - ℓ) ⊆
        (FutureProfiles.profileGoodSet (criticalBeta ϑ (2 * N)) (blockTime (2 * N) ρ) r s)ᶜ := by
      intro ω hω hgood
      have ht := (mem_ratioBadEvent_iff _ (latticeBlockVector_product_pos ϑ ρ N n ℓ ω)).mp hω
      rw [latticeBlockVector_ratio_eq ϑ ρ N n ℓ hℓn hnK ω] at ht
      exact (not_le_of_gt ht) hgood.2
    apply (measure_mono hsubset).trans
    rw [← ENNReal.ofReal_toReal (measure_ne_top disorderLaw _)]
    exact ENNReal.ofReal_le_ofReal hp
  have hlimit := measure_open_le_of_tendstoInDistribution
    (blockVector_tendsto ϑ P Z hZ hρ1 n ℓ hℓn)
    (ratioBadEvent (n - ℓ)) (isOpen_ratioBadEvent _) (ENNReal.ofReal (C / ℓ)) hlattice
  have heq : (flowBlockVector Z ρ n ℓ ⁻¹' ratioBadEvent (n - ℓ)) =ᵐ[P]
      {ω | 1 / 2 < |blockR Z ρ n ℓ ω - 1|} := by
    filter_upwards [flowBlockVector_product_pos_ae ϑ P Z hZ hρ1 n ℓ] with ω hω
    simp only [Set.mem_preimage, mem_ratioBadEvent_iff _ hω,
      flowBlockVector_ratio_eq]
  rw [measure_congr heq] at hlimit
  exact hlimit

end Critical2DKPZ.Extensions.ScaleLimit
