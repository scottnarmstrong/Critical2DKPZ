/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CSZ25Green
public import Critical2DKPZ.Renewal.PolymerBridge
public import Critical2DKPZ.Polymer.Chaos
import Critical2DKPZ.MomentBounds.DampedRenewalLower

/-! # CSZ25 Lemma 5.5 for the directed polymer -/

@[expose] public noncomputable section

namespace Critical2DKPZ.MomentBounds

/-- A damped geometric sum bounds the free second moment from below, as in CSZ25 Lemma 5.5. -/
theorem inv_two_mul_le_freeSecondMoment_half {aHi : ℝ}
    (ha : ∀ n : ℕ, 1 ≤ n → srwKernel (2 * n) 0 ≤ aHi / n) (β : ℝ) (L : ℕ)
    {lam : ℝ} (hlam : 0 ≤ lam)
    (hσ : Polymer.sigmaSq β * (dampedOverlap (lam / L) L + 4 * aHi) ≤ 1) :
    1 / (2 * (1 - Polymer.sigmaSq β * dampedOverlap (lam / L) L)) ≤
      Renewal.freeSecondMoment β (L / 2) := by
  have hA : 0 < aHi := srwKernel_two_zero_pos.trans_le (by simpa using ha 1 le_rfl)
  have hsig : 0 ≤ Polymer.sigmaSq β := by
    exact sub_nonneg.2 (Real.one_le_exp_iff.2 (sq_nonneg β))
  have hupper : ∀ r : ℕ, 1 ≤ r → (r : ℝ) * Renewal.returnWeight r ≤ aHi := by
    intro r hr
    have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    exact (mul_comm _ _).trans_le ((le_div_iff₀ hr0).1 (ha r hr))
  have hD : (∑ r ∈ Finset.Icc 1 L, Real.exp (-lam * r / L) * Renewal.returnWeight r) =
      dampedOverlap (lam / L) L := by
    apply Finset.sum_congr rfl
    intro r _
    dsimp [Renewal.returnWeight]
    congr 2
    ring
  have h := half_geometric_le_damped_renewal Renewal.returnWeight
    (fun r => srwKernel_nonneg _ _) hA hsig hlam hupper L
  dsimp only at h
  rw [hD] at h
  rw [Renewal.freeSecondMoment_eq_renewalFunction]
  exact h hσ

end Critical2DKPZ.MomentBounds
