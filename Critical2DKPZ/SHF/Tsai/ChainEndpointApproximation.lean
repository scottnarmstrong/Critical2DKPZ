/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ChainMomentBounds
public import Critical2DKPZ.SHF.Tsai.ChainPairingLinearity

/-! # Uniform second-moment control of endpoint approximation errors

Almost-sure linearity turns the error of actual pairings into the pairing
with the endpoint difference. The second-moment bound then controls that
error by the spatial `L²` distance, uniformly in the mollifier index.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

variable {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] (K : ℕ) (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k)
  (B : ℕ → Ω → Measure (Plane × Plane)) (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
  (hind : iIndepFun (fun k : Fin (K + 1) => B k) P)
  (w : ℕ → ℕ → Plane → ℝ) (hw : ∀ k, IsL2ApplicableMollifier (w k))

include hτ hB hind hw

/-- One constant controls all first-endpoint pairing errors, with integrability. -/
theorem exists_chainPairing_sub_left_sq_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ℓ : ℕ) (g h g' : Plane → ℝ),
      MemLp g 2 → MemLp h 2 → MemLp g' 2 →
      Integrable (fun ω => ((∫ p, g p.1 * g' p.2
        ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K) -
          ∫ p, h p.1 * g' p.2 ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K) ^ 2) P ∧
      (∫ ω, ((∫ p, g p.1 * g' p.2 ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K) -
        ∫ p, h p.1 * g' p.2 ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K) ^ 2 ∂P) ≤
        C * (eLpNorm (g - h) 2).toReal ^ 2 * (eLpNorm g' 2).toReal ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_chainPairing_sq_bound K τ hτ B hB hind w hw
  refine ⟨C, hC, fun ℓ g h g' hg hh hg' => ?_⟩
  have hb := hbound ℓ (g - h) g' (hg.sub hh) hg'
  have heq := (ae_chainPairing_sub_left K τ hτ B hB hind w hw ℓ g h g' hg hh hg').mono
    (fun _ hω => congrArg (fun x : ℝ => x ^ 2) hω)
  exact ⟨hb.1.congr heq, (integral_congr_ae heq).symm.trans_le hb.2⟩

/-- One constant controls all second-endpoint pairing errors, with integrability. -/
theorem exists_chainPairing_sub_right_sq_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ℓ : ℕ) (g g' h' : Plane → ℝ),
      MemLp g 2 → MemLp g' 2 → MemLp h' 2 →
      Integrable (fun ω => ((∫ p, g p.1 * g' p.2
        ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K) -
          ∫ p, g p.1 * h' p.2 ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K) ^ 2) P ∧
      (∫ ω, ((∫ p, g p.1 * g' p.2 ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K) -
        ∫ p, g p.1 * h' p.2 ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K) ^ 2 ∂P) ≤
        C * (eLpNorm g 2).toReal ^ 2 * (eLpNorm (g' - h') 2).toReal ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_chainPairing_sq_bound K τ hτ B hB hind w hw
  refine ⟨C, hC, fun ℓ g g' h' hg hg' hh' => ?_⟩
  have hb := hbound ℓ g (g' - h') hg (hg'.sub hh')
  have heq := (ae_chainPairing_sub_right K τ hτ B hB hind w hw ℓ g g' h' hg hg' hh').mono
    (fun _ hω => congrArg (fun x : ℝ => x ^ 2) hω)
  exact ⟨hb.1.congr heq, (integral_congr_ae heq).symm.trans_le hb.2⟩

end Critical2DKPZ.SHF.Tsai

end
