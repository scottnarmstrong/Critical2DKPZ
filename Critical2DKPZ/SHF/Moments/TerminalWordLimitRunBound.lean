/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitLocalBounds
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitRun
import Mathlib.Tactic

/-! # Uniform normalized collision-run bounds on interior slabs -/

@[expose] public noncomputable section

open Filter
open scoped BigOperators Topology
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- The exact run normalization factors into its critical scalar coefficient,
normalized spatial renewal, and one normalized free kernel per spectator. -/
theorem scaled_collisionWordUndampedPairRunFactor_eq (ϑ : ℝ) {h N : ℕ}
    (α : CollisionPair h) (r : ℕ) (u v : LatticeConfiguration h)
    (hσ : sigmaSq (criticalBeta ϑ N) = criticalSigmaSq ϑ N)
    (hlog : Real.log (N : ℝ) ≠ 0)
    (hu : u α.1.1 = u α.1.2) (hv : v α.1.1 = v α.1.2) :
    4 * (N : ℝ) * ((N : ℝ) / 4) ^ (h - 1) *
        collisionWordUndampedPairRunFactor (criticalBeta ϑ N) α r u v =
      4 * (criticalSigmaSq ϑ N * Real.log N) *
        (((N : ℝ) / 4) * (N / Real.log N) *
          Collision.spatialRenewal (criticalSigmaSq ϑ N) r (v α.1.1 - u α.1.1)) *
        ∏ i : Spectator α, ((N : ℝ) / 4) * srwKernel r (v i.1 - u i.1) := by
  classical
  have hh : 2 ≤ h := by have ha := α.2; omega
  have hfactor : collisionWordUndampedPairRunFactor (criticalBeta ϑ N) α r u v =
      criticalSigmaSq ϑ N * Collision.spatialRenewal (criticalSigmaSq ϑ N) r
        (v α.1.1 - u α.1.1) * ∏ i : Spectator α, srwKernel r (v i.1 - u i.1) := by
    rw [pairRunFactor_eq_pairTwo_mul_spectators]
    simp [collisionWordUndampedPairRunFactor, pairTwo, pairRestrict, hu, hv, hσ]
  rw [hfactor, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, card_spectator]
  have hexp : h - 1 = (h - 2) + 1 := by omega
  rw [hexp, pow_succ]
  field_simp [hlog]

/-- On a compact positive run-time slab and a diffusive center-displacement
window, the fully normalized collision run is uniformly bounded. -/
theorem eventually_scaled_pairRun_interior_bound (ϑ a T R : ℝ)
    (ha : 0 < a) (haT : a ≤ T) {h : ℕ} (α : CollisionPair h) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ r : ℕ,
      a * N ≤ (r : ℝ) → (r : ℝ) ≤ T * N → ∀ u v : LatticeConfiguration h,
      u α.1.1 = u α.1.2 → v α.1.1 = v α.1.2 →
      Even ((r : ℤ) + (v α.1.1 - u α.1.1) 0 + (v α.1.1 - u α.1.1) 1) →
      ‖siteToPlane (v α.1.1 - u α.1.1)‖ ≤ R * Real.sqrt (N : ℝ) →
      |4 * (N : ℝ) * ((N : ℝ) / 4) ^ (h - 1) *
        collisionWordUndampedPairRunFactor (criticalBeta ϑ N) α r u v| ≤ C := by
  obtain ⟨B, hB, hrenewal⟩ := eventually_scaled_spatialRenewal_interior_bound ϑ a T R ha haT
  obtain ⟨Q, hQ, hwalk⟩ := exists_scaled_srwKernel_interior_bound ha
  have hcrit : ∀ᶠ N : ℕ in atTop, |criticalSigmaSq ϑ N * Real.log N| ≤ Real.pi + 1 := by
    have hb := (Renewal.tendsto_sigma_mul_log ϑ).abs.eventually
      (Iio_mem_nhds (show |Real.pi| < Real.pi + 1 by rw [abs_of_pos Real.pi_pos]; linarith))
    exact hb.mono fun N hN => hN.le
  refine ⟨4 * (Real.pi + 1) * B * Q ^ (h - 2), by positivity, ?_⟩
  filter_upwards [hrenewal, hcrit, criticalBeta_spec ϑ, eventually_gt_atTop 1]
      with N hb hcritN hσ hN
  intro r hrlo hrhi u v hu hv hphase hspace
  rw [scaled_collisionWordUndampedPairRunFactor_eq ϑ α r u v hσ
    (Real.log_pos (by exact_mod_cast hN)).ne' hu hv]
  have hprod : |∏ i : Spectator α, ((N : ℝ) / 4) * srwKernel r (v i.1 - u i.1)| ≤ Q ^ (h - 2) := by
    rw [Finset.abs_prod]
    calc
      (∏ i : Spectator α, |((N : ℝ) / 4) * srwKernel r (v i.1 - u i.1)|) ≤
          ∏ _i : Spectator α, Q := by
        apply Finset.prod_le_prod₀
        · intro i hi; exact abs_nonneg _
        · intro i hi
          rw [abs_of_nonneg (mul_nonneg (by positivity) (srwKernel_nonneg _ _))]
          exact hwalk N r hrlo _
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, card_spectator]
  rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  exact mul_le_mul
    (mul_le_mul (mul_le_mul_of_nonneg_left hcritN (by norm_num))
      (hb r hrlo hrhi _ hphase hspace) (abs_nonneg _) (by positivity))
    hprod (abs_nonneg _) (by positivity)

end Critical2DKPZ.SHF.Moments
