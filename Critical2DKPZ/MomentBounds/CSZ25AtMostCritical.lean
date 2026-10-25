/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CSZ25UniformGreen
public import Critical2DKPZ.MomentBounds.CSZ25Variance
import Critical2DKPZ.MomentBounds.CSZ25ReturnWeights
import Critical2DKPZ.MomentBounds.BoundedScaledRenewal
import Critical2DKPZ.Lattice.Basic

/-! # The reciprocal-free at-most-critical bound in CSZ25 Lemma 5.4 -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace Critical2DKPZ.MomentBounds

/-- A uniform shift bounds the disorder variance times the replica overlap, as in CSZ25 Lemma 5.4. -/
theorem sigmaSq_mul_replicaOverlap_sub_le_one (t c₁ c₃ : ℝ) (ht : 0 < t) (hc₁ : 0 < c₁)
    (hc₃ : 0 < c₃) :
    ∃ θ : ℝ, 0 ≤ θ ∧ ∀ β : ℝ, ∀ L : ℕ, ∀ φ : Site → ℝ, (∀ z, 0 ≤ φ z) → HasSum φ 1 →
      ExpLocalized t c₁ L φ →
      Var[fun ω => profileP2Fun β 0 L φ (fun _ => 1) ω; disorderLaw] ≤ c₃ →
      Polymer.sigmaSq β * (replicaOverlap L - θ) ≤ 1 := by
  obtain ⟨aLo, aHi, haLo, haLH, hreturn⟩ := srwKernel_two_mul_zero_bounds
  have haHi : 0 < aHi := haLo.trans_le haLH
  have hu : ∀ r : ℕ, 1 ≤ r → (r : ℝ) * Renewal.returnWeight r ≤ aHi := by
    intro r hr
    have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    exact (mul_comm _ _).trans_le ((le_div_iff₀ hr0).1 (hreturn r hr).2)
  obtain ⟨η, hη, hGreen⟩ := greenEnergy_half_ge t c₁ ht hc₁
  obtain ⟨θ₀, hθ₀, hshift⟩ := exists_shift_of_bounded_scaled_renewal Renewal.returnWeight
    (B := c₃ / η) (fun r => srwKernel_nonneg _ _) haHi (div_nonneg hc₃.le hη.le) hu
  refine ⟨max θ₀ (replicaOverlap 1), hθ₀.trans (le_max_left _ _), fun β L φ hφ hmass hlocal hvar => ?_⟩
  have hσ : 0 ≤ Polymer.sigmaSq β := sub_nonneg.2 (Real.one_le_exp_iff.2 (sq_nonneg β))
  by_cases hL : 2 ≤ L
  · have hG := hGreen L hL φ hφ hmass hlocal
    have hV := (variance_profileP2Fun_bounds β L φ hφ hmass.summable).1
    have hF : 0 ≤ Renewal.freeSecondMoment β (L / 2) := integral_nonneg (fun _ => sq_nonneg _)
    have hscaled : Polymer.sigmaSq β * Renewal.freeSecondMoment β (L / 2) ≤ c₃ / η := by
      apply (le_div_iff₀ hη).2
      have hprod := mul_le_mul_of_nonneg_right hG (mul_nonneg hσ hF)
      nlinarith only [hprod, hV, hvar]
    rw [Renewal.freeSecondMoment_eq_renewalFunction] at hscaled
    have h := hshift (Polymer.sigmaSq β) hσ L hscaled
    change Polymer.sigmaSq β * (replicaOverlap L - θ₀) ≤ 1 at h
    exact (mul_le_mul_of_nonneg_left (sub_le_sub_left (le_max_left θ₀ (replicaOverlap 1)) _) hσ).trans h
  · have hsmall : replicaOverlap L ≤ replicaOverlap 1 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right (show L ≤ 1 by omega))
      intro n _ _
      exact srwKernel_nonneg _ _
    have hnonpos : replicaOverlap L - max θ₀ (replicaOverlap 1) ≤ 0 :=
      sub_nonpos.2 (hsmall.trans (le_max_right _ _))
    exact (mul_nonpos_of_nonneg_of_nonpos hσ hnonpos).trans zero_le_one

end Critical2DKPZ.MomentBounds
