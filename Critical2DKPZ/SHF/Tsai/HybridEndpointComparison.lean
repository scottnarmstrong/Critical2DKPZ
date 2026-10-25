/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.HybridEndpointLimits
public import Critical2DKPZ.SHF.Tsai.ChainSwapLimits
public import Critical2DKPZ.SHF.Tsai.HybridSwapIndependence
import Critical2DKPZ.SHF.Tsai.BlockMomentTransport

/-! # Initial-endpoint hybrid comparison at the centered remainder limit

The two-block replacement estimate has exactly the initial hybrid expectation
and the next interior hybrid value as its two limits. Its nonnegative centered
fourth-moment limit controls their difference before the quantitative kernel
estimate is applied.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology CompactlySupported

namespace Critical2DKPZ.SHF.Tsai

/-- The initial endpoint and the next interior hybrid limit obey the actual centered fourth-moment bound. -/
theorem exists_hybrid_leftEndpoint_limit_comparison {θ : ℝ} (D : Set ℝ) {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane))
    (hZ : IsDenseSHF θ D P Z) (hZ' : IsDenseSHF θ D P' Z')
    {s b t : ℝ} (hs : s ∈ D) (hb : b ∈ D) (ht : t ∈ D) (hsb : s < b) (hbt : b < t)
    {m r : ℕ} (g g' : Fin m → Fin r → C_c(Plane, ℝ))
    (H : (Fin m → ℝ) → ℝ) (hH : ContDiff ℝ 4 H) (CH : ℝ)
    (hCH : ∀ k ≤ 4, ∀ x, ‖iteratedFDeriv ℝ k H x‖ ≤ CH) :
    let A (ℓ : ℕ) (ω : Ω' × Ω) (i : Fin m) := ∑ k, ∫ p, g i k p.1 * g' i k p.2
      ∂smoothedProductMeasure (Z s b ω.2) (heatMollifier ℓ) (Z b t ω.2)
    let E (ℓ : ℕ) (ω : Ω' × Ω) (i : Fin m) := ∑ k, ∫ p, g i k p.1 * g' i k p.2
      ∂smoothedProductMeasure (heatBlock (b - s)) (heatMollifier ℓ) (Z b t ω.2)
    ∃ Lb M : ℝ, 0 ≤ M ∧
      Tendsto (fun ℓ => hybridValue P P' Z Z' s t g g' H b ℓ) atTop (𝓝 Lb) ∧
      (∀ ℓ, Integrable (fun ω => ∑ i, (A ℓ ω i - E ℓ ω i) ^ 4) (P'.prod P)) ∧
      Tendsto (fun ℓ => ∫ ω, ∑ i, (A ℓ ω i - E ℓ ω i) ^ 4 ∂P'.prod P) atTop (𝓝 M) ∧
      |hybridValue P P' Z Z' s t g g' H s 0 - Lb| ≤ CH / 12 * M := by
  classical
  dsimp only
  let B (k : ℕ) (ω : Ω' × Ω) := if k = 0 then Z s b ω.2 else Z b t ω.2
  let R (ω : Ω' × Ω) := Z' s b ω.1
  let τ (k : ℕ) := if k = 0 then b - s else t - b
  have hτ (k : ℕ) (hk : k ≤ 1) : 0 < τ k := by
    interval_cases k
    · exact sub_pos.2 hsb
    · exact sub_pos.2 hbt
  have hB (k : ℕ) (hk : k ≤ 1) : HasDeltaBoseMoments θ (τ k) (P'.prod P) (B k) := by
    interval_cases k
    · exact (hZ.hasDeltaBoseMoments hs hb hsb).comp_measurePreserving measurePreserving_snd
    · exact (hZ.hasDeltaBoseMoments hb ht hbt).comp_measurePreserving measurePreserving_snd
  have hR : HasDeltaBoseMoments θ (τ 0) (P'.prod P) R :=
    (hZ'.hasDeltaBoseMoments hs hb hsb).comp_measurePreserving measurePreserving_fst
  have hind : iIndepFun (fun k : Fin 3 => if (k : ℕ) ≤ 1 then B k else R) (P'.prod P) := by
    have heq : (fun k : Fin 3 => if (k : ℕ) ≤ 1 then B k else R) =
        (![fun ω : Ω' × Ω => Z s b ω.2, fun ω => Z b t ω.2,
          fun ω => Z' s b ω.1] : Fin 3 → Ω' × Ω → Measure (Plane × Plane)) := by
      funext k ω
      fin_cases k <;> rfl
    rw [heq]
    exact hZ.iIndepFun_hybridSwap_leftEndpoint P P' Z Z' hZ' hs hb ht hsb hbt
  have hg (i k) : MemLp (g i k) 2 := (g i k).continuous.memLp_of_hasCompactSupport (g i k).hasCompactSupport
  have hg' (i k) : MemLp (g' i k) 2 := (g' i k).continuous.memLp_of_hasCompactSupport (g' i k).hasCompactSupport
  obtain ⟨La, Lb, M, hM, _hIA, _hIB, hI, hLa, hLb, hMoment, hbound⟩ :=
    exists_chain_swap_limit_comparison (P'.prod P) 1 0 (by norm_num) τ hτ B R hB hR hind
      (fun _ => heatMollifier) (fun _ => isL2ApplicableMollifier_heatMollifier)
      (fun i k => g i k) (fun i k => g' i k) hg hg' H hH CH hCH
  have hH0 (z) : ‖H z‖ ≤ CH := by
    simpa only [norm_iteratedFDeriv_zero] using hCH 0 (by omega) z
  obtain ⟨L, hHybrid, hOrig, hRep, _hOrigI, _hRepI⟩ := exists_hybrid_leftEndpoint_limits D P P' Z Z' hZ hZ'
    hs hb ht hsb hbt g g' H hH.continuous CH hH0
  have hLaEq : La = hybridValue P P' Z Z' s t g g' H s 0 := tendsto_nhds_unique hLa hOrig
  have hLbEq : Lb = L := tendsto_nhds_unique hLb hRep
  subst La
  subst Lb
  exact ⟨L, M, hM, hHybrid, hI, hMoment, hbound⟩

/-- The last interior hybrid limit and terminal endpoint obey the actual centered fourth-moment bound. -/
theorem exists_hybrid_rightEndpoint_limit_comparison {θ : ℝ} (D : Set ℝ) {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane))
    (hZ : IsDenseSHF θ D P Z) (hZ' : IsDenseSHF θ D P' Z')
    {s a t : ℝ} (hs : s ∈ D) (ha : a ∈ D) (ht : t ∈ D) (hsa : s < a) (hat : a < t)
    {m r : ℕ} (g g' : Fin m → Fin r → C_c(Plane, ℝ))
    (H : (Fin m → ℝ) → ℝ) (hH : ContDiff ℝ 4 H) (CH : ℝ)
    (hCH : ∀ k ≤ 4, ∀ x, ‖iteratedFDeriv ℝ k H x‖ ≤ CH) :
    let A (ℓ : ℕ) (ω : Ω' × Ω) (i : Fin m) := ∑ k, ∫ p, g i k p.1 * g' i k p.2
      ∂smoothedProductMeasure (Z' s a ω.1) (heatMollifier ℓ) (Z a t ω.2)
    let E (ℓ : ℕ) (ω : Ω' × Ω) (i : Fin m) := ∑ k, ∫ p, g i k p.1 * g' i k p.2
      ∂smoothedProductMeasure (Z' s a ω.1) (heatMollifier ℓ) (heatBlock (t - a))
    ∃ La M : ℝ, 0 ≤ M ∧
      Tendsto (fun ℓ => hybridValue P P' Z Z' s t g g' H a ℓ) atTop (𝓝 La) ∧
      (∀ ℓ, Integrable (fun ω => ∑ i, (A ℓ ω i - E ℓ ω i) ^ 4) (P'.prod P)) ∧
      Tendsto (fun ℓ => ∫ ω, ∑ i, (A ℓ ω i - E ℓ ω i) ^ 4 ∂P'.prod P) atTop (𝓝 M) ∧
      |La - hybridValue P P' Z Z' s t g g' H t 0| ≤ CH / 12 * M := by
  classical
  dsimp only
  let B (k : ℕ) (ω : Ω' × Ω) := if k = 0 then Z' s a ω.1 else Z a t ω.2
  let R (ω : Ω' × Ω) := Z' a t ω.1
  let τ (k : ℕ) := if k = 0 then a - s else t - a
  have hτ (k : ℕ) (hk : k ≤ 1) : 0 < τ k := by
    interval_cases k
    · exact sub_pos.2 hsa
    · exact sub_pos.2 hat
  have hB (k : ℕ) (hk : k ≤ 1) : HasDeltaBoseMoments θ (τ k) (P'.prod P) (B k) := by
    interval_cases k
    · exact (hZ'.hasDeltaBoseMoments hs ha hsa).comp_measurePreserving measurePreserving_fst
    · exact (hZ.hasDeltaBoseMoments ha ht hat).comp_measurePreserving measurePreserving_snd
  have hR : HasDeltaBoseMoments θ (τ 1) (P'.prod P) R :=
    (hZ'.hasDeltaBoseMoments ha ht hat).comp_measurePreserving measurePreserving_fst
  have hind : iIndepFun (fun k : Fin 3 => if (k : ℕ) ≤ 1 then B k else R) (P'.prod P) := by
    have heq : (fun k : Fin 3 => if (k : ℕ) ≤ 1 then B k else R) =
        (![fun ω : Ω' × Ω => Z' s a ω.1, fun ω => Z a t ω.2,
          fun ω => Z' a t ω.1] : Fin 3 → Ω' × Ω → Measure (Plane × Plane)) := by
      funext k ω
      fin_cases k <;> rfl
    rw [heq]
    exact hZ.iIndepFun_hybridSwap_rightEndpoint P P' Z Z' hZ' hs ha ht hsa hat
  have hg (i k) : MemLp (g i k) 2 := (g i k).continuous.memLp_of_hasCompactSupport (g i k).hasCompactSupport
  have hg' (i k) : MemLp (g' i k) 2 := (g' i k).continuous.memLp_of_hasCompactSupport (g' i k).hasCompactSupport
  obtain ⟨La, Lb, M, hM, _hIA, _hIB, hI, hLa, hLb, hMoment, hbound⟩ :=
    exists_chain_swap_limit_comparison (P'.prod P) 1 1 (by norm_num) τ hτ B R hB hR hind
      (fun _ => heatMollifier) (fun _ => isL2ApplicableMollifier_heatMollifier)
      (fun i k => g i k) (fun i k => g' i k) hg hg' H hH CH hCH
  have hH0 (z) : ‖H z‖ ≤ CH := by
    simpa only [norm_iteratedFDeriv_zero] using hCH 0 (by omega) z
  obtain ⟨L, hHybrid, hOrig, hRep, _hOrigI, _hRepI⟩ := exists_hybrid_rightEndpoint_limits D P P' Z Z' hZ hZ'
    hs ha ht hsa hat g g' H hH.continuous CH hH0
  have hLaEq : La = L := tendsto_nhds_unique hLa hOrig
  have hLbEq : Lb = hybridValue P P' Z Z' s t g g' H t 0 := tendsto_nhds_unique hLb hRep
  subst La
  subst Lb
  exact ⟨L, M, hM, hHybrid, hI, hMoment, hbound⟩

end Critical2DKPZ.SHF.Tsai

end
