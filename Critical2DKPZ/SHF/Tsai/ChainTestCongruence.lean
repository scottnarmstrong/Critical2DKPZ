/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.EndpointTestCongruence
public import Critical2DKPZ.SHF.Tsai.MixedChainEndpointMoments

/-! # Chain pairings of volume-equivalent endpoint tests

Absolute continuity of the first endpoint moment measure gives almost-sure equality of
chain pairings for volume-equivalent tests, both before and after a heat replacement.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- Volume-equivalent endpoint tests give equal chain pairings almost surely. -/
theorem ae_integral_chainProduct_congr {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (K : ℕ) (τ : ℕ → ℝ)
    (hτ : ∀ k ≤ K, 0 < τ k) (B : ℕ → Ω → Measure (Plane × Plane))
    (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hind : iIndepFun (fun k : Fin (K + 1) => B k) P)
    (w : ℕ → ℕ → Plane → ℝ) (hw : ∀ k, IsL2ApplicableMollifier (w k)) (ℓ : ℕ)
    (F G : Plane × Plane → ℝ) (hFG : F =ᵐ[volume] G) :
    (fun ω => ∫ p, F p ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K) =ᵐ[P]
      fun ω => ∫ p, G p ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K := by
  obtain ⟨C, hCm, hClf, hCeq, hmean⟩ := exists_chain_endpointTuple_moment_measure K τ hτ B hB hind
    (n := 1) (by norm_num) (by norm_num) (fun _ => w) (fun _ => hw) ℓ
  have hCi (i : Fin 1) : C i = C 0 := congrArg C (Subsingleton.elim i 0)
  simp_rw [hCi] at hmean
  have hread := ae_integral_congr_of_endpointTuple_mean P (C 0) (hCm 0) (hClf 0)
    _ hmean (withDensity_absolutelyContinuous _ _) F G hFG
  filter_upwards [hCeq 0, hread] with ω hω hEq
  rw [hω] at hEq
  exact hEq

/-- Volume-equivalent endpoint tests give equal heat-replaced chain pairings almost surely. -/
theorem ae_integral_chainProduct_update_heat_congr {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (K j : ℕ) (hj : j ≤ K) (τ : ℕ → ℝ)
    (hτ : ∀ k ≤ K, 0 < τ k) (B : ℕ → Ω → Measure (Plane × Plane))
    (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hind : iIndepFun (fun k : Fin (K + 1) => B k) P)
    (w : ℕ → ℕ → Plane → ℝ) (hw : ∀ k, IsL2ApplicableMollifier (w k)) (ℓ : ℕ)
    (F G : Plane × Plane → ℝ) (hFG : F =ᵐ[volume] G) :
    (fun ω => ∫ p, F p ∂chainProduct
      (Function.update (fun k => B k ω) j (heatBlock (τ j))) (fun k => w k ℓ) K) =ᵐ[P]
      fun ω => ∫ p, G p ∂chainProduct
        (Function.update (fun k => B k ω) j (heatBlock (τ j))) (fun k => w k ℓ) K := by
  obtain ⟨C, hCm, hClf, hCeq, hmean⟩ := exists_mixedChain_endpointTuple_moment_measure K j hj τ hτ B hB hind
    (n := 1) (by norm_num) (by norm_num) ∅ (fun _ => w) (fun _ => hw) ℓ
  have hCi (i : Fin 1) : C i = C 0 := congrArg C (Subsingleton.elim i 0)
  simp_rw [hCi] at hmean
  have hread := ae_integral_congr_of_endpointTuple_mean P (C 0) (hCm 0) (hClf 0)
    _ hmean (withDensity_absolutelyContinuous _ _) F G hFG
  have hEq := hCeq 0
  simp only [Finset.notMem_empty, ite_false] at hEq
  filter_upwards [hEq, hread] with ω hω hRead
  rw [hω] at hRead
  exact hRead

end Critical2DKPZ.SHF.Tsai

end
