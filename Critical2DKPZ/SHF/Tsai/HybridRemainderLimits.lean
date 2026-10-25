/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.HybridSwapComparison
public import Critical2DKPZ.SHF.Tsai.CenteredFourthLimits
public import Critical2DKPZ.SHF.Tsai.HybridAdjacentLimits
import Critical2DKPZ.SHF.Tsai.BlockMomentTransport
import Critical2DKPZ.SHF.Tsai.HeatMollifier

/-! # Fourth-moment control of interior hybrid differences

The centered fourth remainder has a common finite nonnegative limit that controls the
difference between the two interior hybrid expectation limits.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology CompactlySupported

namespace Critical2DKPZ.SHF.Tsai

/-- The literal centered fourth remainder for an interior three-block hybrid replacement. -/
def hybridCenteredFourth {Ω Ω' : Type*}
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane))
    (s a b t : ℝ) (u : ℕ → Plane → ℝ) {m r : ℕ}
    (g g' : Fin m → Fin r → C_c(Plane, ℝ)) (ℓ ℓ' : ℕ) (ω : Ω' × Ω) : ℝ :=
  ∑ i, (threeBlockPairing ![fun ω : Ω' × Ω => Z' s a ω.1,
      fun ω => Z a b ω.2, fun ω => Z b t ω.2] u g g' ℓ ℓ' ω i -
    threeBlockPairing ![fun ω : Ω' × Ω => Z' s a ω.1,
      fun _ => heatBlock (b - a), fun ω => Z b t ω.2] u g g' ℓ ℓ' ω i) ^ 4

/-- The interior centered remainder has one finite nonnegative limit for every applicable connector family. -/
theorem exists_hybridCenteredFourth_limit {θ : ℝ} {D : Set ℝ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane))
    (hZ : IsDenseSHF θ D P Z) (hZ' : IsDenseSHF θ D P' Z')
    {s a b t : ℝ} (hs : s ∈ D) (ha : a ∈ D) (hb : b ∈ D) (ht : t ∈ D)
    (hsa : s < a) (hab : a < b) (hbt : b < t) {m r : ℕ}
    (g g' : Fin m → Fin r → C_c(Plane, ℝ)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u : ℕ → Plane → ℝ, IsL2ApplicableMollifier u →
      (∀ ℓ, Integrable (hybridCenteredFourth Z Z' s a b t u g g' ℓ ℓ) (P'.prod P)) ∧
      Tendsto (fun ℓ => ∫ ω, hybridCenteredFourth Z Z' s a b t u g g' ℓ ℓ ω ∂P'.prod P)
        atTop (𝓝 M) := by
  classical
  let B (k : ℕ) (ω : Ω' × Ω) := if k = 0 then Z' s a ω.1 else
    if k = 1 then Z a b ω.2 else Z b t ω.2
  let τ (k : ℕ) := if k = 0 then a - s else if k = 1 then b - a else t - b
  have hτ (k : ℕ) (hk : k ≤ 2) : 0 < τ k := by
    interval_cases k
    · exact sub_pos.2 hsa
    · exact sub_pos.2 hab
    · exact sub_pos.2 hbt
  have hB (k : ℕ) (hk : k ≤ 2) : HasDeltaBoseMoments θ (τ k) (P'.prod P) (B k) := by
    interval_cases k
    · exact (hZ'.hasDeltaBoseMoments hs ha hsa).comp_measurePreserving measurePreserving_fst
    · exact (hZ.hasDeltaBoseMoments ha hb hab).comp_measurePreserving measurePreserving_snd
    · exact (hZ.hasDeltaBoseMoments hb ht hbt).comp_measurePreserving measurePreserving_snd
  have hind : iIndepFun (fun k : Fin 3 => B k) (P'.prod P) := by
    have h := (hZ.iIndepFun_hybridSwap P P' Z Z' hZ' hs ha hb ht hsa hab hbt).precomp
      (Fin.castSucc_injective 3)
    have heq : (fun k : Fin 3 =>
        (![fun ω : Ω' × Ω => Z' s a ω.1, fun ω => Z a b ω.2,
          fun ω => Z b t ω.2, fun ω => Z' a b ω.1] : Fin 4 → Ω' × Ω → Measure (Plane × Plane)) k.castSucc) =
        fun k : Fin 3 => B k := by
      funext k ω
      fin_cases k <;> rfl
    rwa [heq] at h
  obtain ⟨M, hM, hLimit⟩ := exists_integral_sum_centeredChainPairings_four_limit 2 1 (by norm_num)
    τ hτ B hB hind (fun i j => g i j) (fun i j => g' i j)
    (fun i j => (g i j).continuous.memLp_of_hasCompactSupport (g i j).hasCompactSupport)
    (fun i j => (g' i j).continuous.memLp_of_hasCompactSupport (g' i j).hasCompactSupport)
  refine ⟨M, hM, fun u hu => ?_⟩
  exact hLimit (fun _ => u) (fun _ => hu)

/-- The difference of the two interior hybrid limits is bounded by the actual centered fourth-moment limit. -/
theorem exists_hybrid_adjacent_limit_comparison {θ : ℝ} (D : Set ℝ) {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane))
    (hZ : IsDenseSHF θ D P Z) (hZ' : IsDenseSHF θ D P' Z')
    {s a b t : ℝ} (hs : s ∈ D) (ha : a ∈ D) (hb : b ∈ D) (ht : t ∈ D)
    (hsa : s < a) (hab : a < b) (hbt : b < t) {m r : ℕ}
    (g g' : Fin m → Fin r → C_c(Plane, ℝ))
    (H : (Fin m → ℝ) → ℝ) (hH : ContDiff ℝ 4 H) (CH : ℝ)
    (hCH : ∀ k ≤ 4, ∀ x, ‖iteratedFDeriv ℝ k H x‖ ≤ CH) :
    ∃ La Lb M : ℝ, 0 ≤ M ∧
      Tendsto (fun ℓ => hybridValue P P' Z Z' s t g g' H a ℓ) atTop (𝓝 La) ∧
      Tendsto (fun ℓ => hybridValue P P' Z Z' s t g g' H b ℓ) atTop (𝓝 Lb) ∧
      (∀ ℓ, Integrable (hybridCenteredFourth Z Z' s a b t heatMollifier g g' ℓ ℓ) (P'.prod P)) ∧
      Tendsto (fun ℓ => ∫ ω, hybridCenteredFourth Z Z' s a b t heatMollifier g g' ℓ ℓ ω ∂P'.prod P)
        atTop (𝓝 M) ∧ |La - Lb| ≤ CH / 12 * M := by
  obtain ⟨La, Lb, hLa, hLb, hA, hB⟩ := exists_hybrid_adjacent_joint_limits D P P' Z Z' hZ hZ'
    hs ha hb ht hsa hab hbt g g' H hH CH hCH
  obtain ⟨M, hM, hLimit⟩ := exists_hybridCenteredFourth_limit P P' Z Z' hZ hZ'
    hs ha hb ht hsa hab hbt g g'
  have hL := hLimit heatMollifier isL2ApplicableMollifier_heatMollifier
  refine ⟨La, Lb, M, hM, hLa, hLb, hL.1, hL.2, ?_⟩
  have hLeft := ((hA.comp tendsto_atTop_diagonal).sub (hB.comp tendsto_atTop_diagonal)).abs
  have hRight := hL.2.const_mul (CH / 12)
  apply le_of_tendsto_of_tendsto hLeft hRight
  apply Eventually.of_forall
  intro ℓ
  exact (integrable_and_abs_integral_hybridSwap_le P P' Z Z' hZ hZ' hs ha hb ht hsa hab hbt
    heatMollifier isL2ApplicableMollifier_heatMollifier ℓ ℓ g g' H hH CH hCH).2.2.2

end Critical2DKPZ.SHF.Tsai

end
