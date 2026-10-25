/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.SignedChainMoments

/-! # Almost-sure linearity of actual chain tensor pairings

The signed moment identity supplies integrability of arbitrary `L²` endpoint
representatives inside the random measure. Bochner linearity therefore holds
almost surely without imposing extra measurability on those representatives.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

variable {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] (K : ℕ) (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k)
  (B : ℕ → Ω → Measure (Plane × Plane)) (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
  (hind : iIndepFun (fun k : Fin (K + 1) => B k) P)
  (w : ℕ → ℕ → Plane → ℝ) (hw : ∀ k, IsL2ApplicableMollifier (w k)) (ℓ : ℕ)

include hτ hB hind hw

/-- An arbitrary `L²` endpoint tensor is integrable in the actual chain almost surely. -/
theorem ae_integrable_chainPairing (g g' : Plane → ℝ) (hg : MemLp g 2) (hg' : MemLp g' 2) :
    ∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane => g p.1 * g' p.2)
      (chainProduct (fun k => B k ω) (fun k => w k ℓ) K) := by
  have h := (integral_prod_chainProduct_eq K τ hτ B hB hind (n := 1)
    (by norm_num) (by norm_num) (fun _ => w) (fun _ => hw) ℓ
    (fun _ => g) (fun _ => g') (fun _ => hg) (fun _ => hg')).1
  exact h.mono (fun _ hω => hω 0)

/-- Subtracting the first endpoint test subtracts its actual chain pairing almost surely. -/
theorem ae_chainPairing_sub_left (g h g' : Plane → ℝ)
    (hg : MemLp g 2) (hh : MemLp h 2) (hg' : MemLp g' 2) :
    ∀ᵐ ω ∂P, (∫ p, (g p.1 - h p.1) * g' p.2
      ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K) =
      (∫ p, g p.1 * g' p.2 ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K) -
        ∫ p, h p.1 * g' p.2 ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K := by
  filter_upwards [ae_integrable_chainPairing K τ hτ B hB hind w hw ℓ g g' hg hg',
    ae_integrable_chainPairing K τ hτ B hB hind w hw ℓ h g' hh hg'] with ω hIg hIh
  simp_rw [sub_mul]
  exact integral_sub hIg hIh

/-- Subtracting the second endpoint test subtracts its actual chain pairing almost surely. -/
theorem ae_chainPairing_sub_right (g g' h' : Plane → ℝ)
    (hg : MemLp g 2) (hg' : MemLp g' 2) (hh' : MemLp h' 2) :
    ∀ᵐ ω ∂P, (∫ p, g p.1 * (g' p.2 - h' p.2)
      ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K) =
      (∫ p, g p.1 * g' p.2 ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K) -
        ∫ p, g p.1 * h' p.2 ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K := by
  filter_upwards [ae_integrable_chainPairing K τ hτ B hB hind w hw ℓ g g' hg hg',
    ae_integrable_chainPairing K τ hτ B hB hind w hw ℓ g h' hg hh'] with ω hIg hIh
  simp_rw [mul_sub]
  exact integral_sub hIg hIh

end Critical2DKPZ.SHF.Tsai

end
