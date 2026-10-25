/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.HybridSwapIndependence
public import Critical2DKPZ.SHF.Tsai.ThreeBlockLimits
import Critical2DKPZ.SHF.Tsai.ChainSwap
import Critical2DKPZ.SHF.Tsai.BlockMomentTransport

/-! # Three-block hybrid replacement bounds

Replacing the middle hybrid increment gives a nonlinear expectation bound controlled by
the centered fourth moment of the original block about its heat replacement, with
integrability of all observables.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped CompactlySupported

namespace Critical2DKPZ.SHF.Tsai

/-- Replacing the interior hybrid increment obeys the Taylor bound, with all three integrability assertions. -/
theorem integrable_and_abs_integral_hybridSwap_le {θ : ℝ} {D : Set ℝ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane))
    (hZ : IsDenseSHF θ D P Z) (hZ' : IsDenseSHF θ D P' Z')
    {s a b t : ℝ} (hs : s ∈ D) (ha : a ∈ D) (hb : b ∈ D) (ht : t ∈ D)
    (hsa : s < a) (hab : a < b) (hbt : b < t)
    (u : ℕ → Plane → ℝ) (hu : IsL2ApplicableMollifier u) (ℓ ℓ' : ℕ)
    {m r : ℕ} (g g' : Fin m → Fin r → C_c(Plane, ℝ))
    (H : (Fin m → ℝ) → ℝ) (hH : ContDiff ℝ 4 H) (CH : ℝ)
    (hCH : ∀ k ≤ 4, ∀ x, ‖iteratedFDeriv ℝ k H x‖ ≤ CH) :
    let B : Fin 3 → Ω' × Ω → Measure (Plane × Plane) :=
      ![fun ω => Z' s a ω.1, fun ω => Z a b ω.2, fun ω => Z b t ω.2]
    let R : Fin 3 → Ω' × Ω → Measure (Plane × Plane) :=
      ![fun ω => Z' s a ω.1, fun ω => Z' a b ω.1, fun ω => Z b t ω.2]
    let E : Fin 3 → Ω' × Ω → Measure (Plane × Plane) :=
      ![fun ω => Z' s a ω.1, fun _ => heatBlock (b - a), fun ω => Z b t ω.2]
    Integrable (fun ω => H (threeBlockPairing B u g g' ℓ ℓ' ω)) (P'.prod P) ∧
    Integrable (fun ω => H (threeBlockPairing R u g g' ℓ ℓ' ω)) (P'.prod P) ∧
    Integrable (fun ω => ∑ i, (threeBlockPairing B u g g' ℓ ℓ' ω i -
      threeBlockPairing E u g g' ℓ ℓ' ω i) ^ 4) (P'.prod P) ∧
    |(∫ ω, H (threeBlockPairing B u g g' ℓ ℓ' ω) ∂P'.prod P) -
      ∫ ω, H (threeBlockPairing R u g g' ℓ ℓ' ω) ∂P'.prod P| ≤
      CH / 12 * ∫ ω, ∑ i, (threeBlockPairing B u g g' ℓ ℓ' ω i -
        threeBlockPairing E u g g' ℓ ℓ' ω i) ^ 4 ∂P'.prod P := by
  classical
  dsimp only
  let B (k : ℕ) (ω : Ω' × Ω) := if k = 0 then Z' s a ω.1 else
    if k = 1 then Z a b ω.2 else Z b t ω.2
  let R (ω : Ω' × Ω) := Z' a b ω.1
  let τ (k : ℕ) := if k = 0 then a - s else if k = 1 then b - a else t - b
  let v (k : ℕ) := u (if k = 0 then ℓ else ℓ')
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
  have hR : HasDeltaBoseMoments θ (τ 1) (P'.prod P) R :=
    (hZ'.hasDeltaBoseMoments ha hb hab).comp_measurePreserving measurePreserving_fst
  have hind : iIndepFun (fun k : Fin 4 => if (k : ℕ) ≤ 2 then B k else R) (P'.prod P) := by
    have heq : (fun k : Fin 4 => if (k : ℕ) ≤ 2 then B k else R) =
        (![fun ω : Ω' × Ω => Z' s a ω.1, fun ω => Z a b ω.2,
          fun ω => Z b t ω.2, fun ω => Z' a b ω.1] : Fin 4 → Ω' × Ω → Measure (Plane × Plane)) := by
      funext k ω
      fin_cases k <;> rfl
    rw [heq]
    exact hZ.iIndepFun_hybridSwap P P' Z Z' hZ' hs ha hb ht hsa hab hbt
  have hv (k : ℕ) : ∃ w : ℕ → Plane → ℝ, IsL2ApplicableMollifier w ∧ ∃ j, v k = w j :=
    ⟨u, hu, if k = 0 then ℓ else ℓ', rfl⟩
  have hg (i j) : MemLp (g i j) 2 := (g i j).continuous.memLp_of_hasCompactSupport (g i j).hasCompactSupport
  have hg' (i j) : MemLp (g' i j) 2 := (g' i j).continuous.memLp_of_hasCompactSupport (g' i j).hasCompactSupport
  have hI := integrable_comp_chain_swap 2 1 (by norm_num) τ hτ B R hB hR hind v hv
    (fun i j => g i j) (fun i j => g' i j) hg hg' H hH CH hCH
  have hbound := (abs_integral_comp_chain_swap_le 2 1 (by norm_num) τ hτ B R hB hR hind v hv
    (fun i j => g i j) (fun i j => g' i j) hg hg' H hH CH hCH).2
  exact ⟨hI.1, hI.2.1, hI.2.2, hbound⟩

end Critical2DKPZ.SHF.Tsai

end
