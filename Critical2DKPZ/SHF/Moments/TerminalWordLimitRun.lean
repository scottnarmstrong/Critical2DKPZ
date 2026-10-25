/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.PairBlockSpatialRenewalHorizon
public import Critical2DKPZ.SHF.Moments.KernelLimit
public import Critical2DKPZ.SHF.Moments.WordLimitRunMass
public import Critical2DKPZ.SHF.DeltaBose.CollisionScaling
import Mathlib.Tactic

/-! # Moving local limit of one collision run with free spectators -/

@[expose] public noncomputable section

open Filter
open scoped BigOperators Topology
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- The normalized run factor has the collision-kernel local limit at every
positive time. The factor four accounts for the preceding collision entrance. -/
theorem tendsto_scaled_wordPairRun_moving (ϑ : ℝ) {h : ℕ} (α : CollisionPair h)
    {t : ℝ} (ht : 0 < t) (rN : ℕ → ℕ)
    (hr : Tendsto (fun N : ℕ => (rN N : ℝ) / N) atTop (𝓝 t))
    (uN vN : ℕ → Fin h → Site) (u v : Configuration h)
    (hu : ∀ i, Tendsto (fun N => latticeRepresentative N (uN N i)) atTop (𝓝 (u i)))
    (hv : ∀ i, Tendsto (fun N => latticeRepresentative N (vN N i)) atTop (𝓝 (v i)))
    (huPair : ∀ᶠ N : ℕ in atTop, uN N α.1.1 = uN N α.1.2)
    (hvPair : ∀ᶠ N : ℕ in atTop, vN N α.1.1 = vN N α.1.2)
    (hphase : ∀ i, ∀ᶠ N : ℕ in atTop,
      Even ((vN N i - uN N i) 0 + (vN N i - uN N i) 1 + (rN N : ℤ))) :
    Tendsto (fun N : ℕ => 4 * (N : ℝ) * ((N : ℝ) / 4) ^ (h - 1) *
      collisionWordUndampedPairRunFactor (criticalBeta ϑ N) α (rN N) (uN N) (vN N)) atTop
      (𝓝 (collisionKernel α (ϑ - Real.eulerMascheroniConstant) t
        (u α.1.1, fun i : Spectator α => u i.1)
        (v α.1.1, fun i : Spectator α => v i.1))) := by
  classical
  have hh : 2 ≤ h := by have ha := α.2; omega
  have hgap (i : Fin h) : Tendsto
      (fun N => latticeRepresentative N (vN N i - uN N i)) atTop (𝓝 (v i - u i)) := by
    simpa only [latticeRepresentative_sub] using (hv i).sub (hu i)
  have hR := tendsto_scaled_spatialRenewal_moving_horizon ϑ t ht rN hr
    (fun N => vN N α.1.1 - uN N α.1.1) (v α.1.1 - u α.1.1) (hgap α.1.1)
    (by simpa only [add_comm, add_left_comm, add_assoc] using hphase α.1.1)
  have hQ (i : Spectator α) := tendsto_scaled_srwKernel ht hr (hgap i.1) (hphase i.1)
  have hprod := tendsto_finsetProd Finset.univ (fun i hi => hQ i)
  have hlim := (((Renewal.tendsto_sigma_mul_log ϑ).const_mul 4).mul hR).mul hprod
  have hlim' : Tendsto (fun N : ℕ =>
      4 * (criticalSigmaSq ϑ N * Real.log N) *
        (((N : ℝ) / 4) * (N / Real.log N) *
          Collision.spatialRenewal (criticalSigmaSq ϑ N) (rN N)
            (vN N α.1.1 - uN N α.1.1)) *
        ∏ i : Spectator α, ((N : ℝ) / 4) * srwKernel (rN N) (vN N i.1 - uN N i.1)) atTop
      (𝓝 (collisionKernel α (ϑ - Real.eulerMascheroniConstant) t
        (u α.1.1, fun i : Spectator α => u i.1)
        (v α.1.1, fun i : Spectator α => v i.1))) := by
    convert hlim using 1
    congr 1
    dsimp [collisionKernel]
    ring
  apply hlim'.congr'
  filter_upwards [criticalBeta_spec ϑ, huPair, hvPair, eventually_gt_atTop 1]
    with N hβ huN hvN hN
  have hσ : sigmaSq (criticalBeta ϑ N) = criticalSigmaSq ϑ N := hβ
  have hlog : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  have hfactor : collisionWordUndampedPairRunFactor (criticalBeta ϑ N) α (rN N) (uN N) (vN N) =
      criticalSigmaSq ϑ N * Collision.spatialRenewal (criticalSigmaSq ϑ N) (rN N)
        (vN N α.1.1 - uN N α.1.1) *
        ∏ i : Spectator α, srwKernel (rN N) (vN N i.1 - uN N i.1) := by
    rw [pairRunFactor_eq_pairTwo_mul_spectators]
    simp [collisionWordUndampedPairRunFactor, pairTwo, pairRestrict, huN, hvN, hσ]
  rw [hfactor, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, card_spectator]
  have hexp : h - 1 = (h - 2) + 1 := by omega
  rw [hexp, pow_succ]
  field_simp [hlog]

end Critical2DKPZ.SHF.Moments
