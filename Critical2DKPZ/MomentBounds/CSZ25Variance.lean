/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CSZ25GreenCalculus
public import Critical2DKPZ.Polymer.ProbabilityProfiles
public import Critical2DKPZ.Renewal.PolymerBridge

/-! # CSZ25 variance identities for the directed polymer -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace Critical2DKPZ.MomentBounds

/-- The profile partition-function variance is the sum of collision weights times free second moments. -/
theorem variance_profileP2Fun_eq_sum (β : ℝ) (L : ℕ) (φ : Site → ℝ) (hφ : ∀ z, 0 ≤ φ z)
    (hsum : Summable φ) :
    Var[fun ω => profileP2Fun β 0 L φ (fun _ => 1) ω; disorderLaw] =
      ∑ m ∈ Finset.Icc 1 L, (∑' z, ∑' w, φ z * srwKernel (2 * m) (z - w) * φ w) *
        Polymer.sigmaSq β * Renewal.freeSecondMoment β (L - m) := by
  have habs : Summable (fun z => |φ z|) := by simpa only [abs_of_nonneg (hφ _)] using hsum
  have hmem := Polymer.memLp_profileP2Fun_summable β 0 L φ (fun _ => 1)
    habs 1 zero_le_one (fun _ => by norm_num) 2 (by norm_num)
  have hmean : (∫ ω, profileP2Fun β 0 L φ (fun _ => 1) ω ∂disorderLaw) = ∑' z, φ z := by
    rw [Polymer.integral_profileP2Fun_summable β 0 L φ (fun _ => 1)
      habs 1 zero_le_one (fun _ => by norm_num)]
    simp only [mul_one, Polymer.tsum_srwKernel]
  have hfc := Polymer.profile_firstCollision_summable β 0 L φ φ habs habs
  simp only [Nat.zero_add] at hfc
  rw [variance_eq_sub hmem, hmean]
  simp only [Pi.pow_apply]
  simp only [← pow_two] at hfc
  rw [hfc]
  apply Finset.sum_congr rfl
  intro m _
  have hs := summable_evenTimeEnergy_terms m φ hφ hsum
  calc
    _ = ∑' p : Site × Site,
        (φ p.1 * srwKernel (2 * m) (p.1 - p.2) * φ p.2) *
          (Polymer.sigmaSq β * Renewal.freeSecondMoment β (L - m)) := by
      apply tsum_congr
      intro p
      rw [Polymer.srwKernel_sub_swap, Polymer.pairMoment_eq_secondMoment]
      change φ p.1 * φ p.2 * srwKernel (2 * m) (p.1 - p.2) * Polymer.sigmaSq β *
        Renewal.freeSecondMoment β (L - m) = _
      ring
    _ = _ := by rw [tsum_mul_right, hs.tsum_prod]; ring

/-- The free second moment bounds the finite profile variance from both sides, with square integrability supplied by `Polymer.memLp_profileP2Fun_summable`. -/
theorem variance_profileP2Fun_bounds (β : ℝ) (L : ℕ) (φ : Site → ℝ) (hφ : ∀ z, 0 ≤ φ z)
    (hsum : Summable φ) :
    greenEnergy (L / 2) φ * Polymer.sigmaSq β * Renewal.freeSecondMoment β (L / 2) ≤
        Var[fun ω => profileP2Fun β 0 L φ (fun _ => 1) ω; disorderLaw] ∧
      Var[fun ω => profileP2Fun β 0 L φ (fun _ => 1) ω; disorderLaw] ≤
        greenEnergy L φ * Polymer.sigmaSq β * Renewal.freeSecondMoment β L := by
  let E : ℕ → ℝ := fun m => ∑' z, ∑' w, φ z * srwKernel (2 * m) (z - w) * φ w
  have hE : ∀ m, 0 ≤ E m := fun m => tsum_nonneg fun z => tsum_nonneg fun w =>
    mul_nonneg (mul_nonneg (hφ z) (srwKernel_nonneg _ _)) (hφ w)
  have hσ : 0 ≤ Polymer.sigmaSq β := sub_nonneg.2 (Real.one_le_exp_iff.2 (sq_nonneg β))
  have hF : Monotone (Renewal.freeSecondMoment β) := by
    rw [Renewal.freeSecondMoment_eq_renewalFunction]
    exact Renewal.renewalFunction_mono_time (fun r => mul_nonneg hσ (srwKernel_nonneg _ _))
  have hF0 : ∀ n, 0 ≤ Renewal.freeSecondMoment β n :=
    fun n => integral_nonneg (fun _ => sq_nonneg _)
  rw [variance_profileP2Fun_eq_sum β L φ hφ hsum,
    greenEnergy_eq_sum (L / 2) φ hφ hsum, greenEnergy_eq_sum L φ hφ hsum]
  change (∑ m ∈ Finset.Icc 1 (L / 2), E m) * Polymer.sigmaSq β *
      Renewal.freeSecondMoment β (L / 2) ≤
      ∑ m ∈ Finset.Icc 1 L, E m * Polymer.sigmaSq β * Renewal.freeSecondMoment β (L - m) ∧
    (∑ m ∈ Finset.Icc 1 L, E m * Polymer.sigmaSq β * Renewal.freeSecondMoment β (L - m)) ≤
      (∑ m ∈ Finset.Icc 1 L, E m) * Polymer.sigmaSq β * Renewal.freeSecondMoment β L
  simp only [Finset.sum_mul]
  constructor
  · calc
      _ ≤ ∑ m ∈ Finset.Icc 1 (L / 2), E m * Polymer.sigmaSq β *
          Renewal.freeSecondMoment β (L - m) := by
        apply Finset.sum_le_sum
        intro m hm
        exact mul_le_mul_of_nonneg_left (hF (by have := (Finset.mem_Icc.1 hm).2; omega))
          (mul_nonneg (hE m) hσ)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Icc_subset_Icc_right (Nat.div_le_self L 2))
        (fun m _ _ => mul_nonneg (mul_nonneg (hE m) hσ) (hF0 _))
  · exact Finset.sum_le_sum (fun m _ => mul_le_mul_of_nonneg_left
      (hF (Nat.sub_le L m)) (mul_nonneg (hE m) hσ))

end Critical2DKPZ.MomentBounds
