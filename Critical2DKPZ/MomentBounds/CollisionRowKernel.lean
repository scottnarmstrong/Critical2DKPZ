/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.SpectatorPeeling
public import Critical2DKPZ.MomentBounds.TwoCoordinateSum
import Mathlib.Tactic

/-! # Collision-row bound after spectator peeling -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

noncomputable section

/-- The weighted kernel on a pair of free coordinates and finitely many spectators. -/
def collisionProfileKernel (L r a p : ℝ) {m : ℕ} (anchor : Fin m → Site)
    (u : Site) (z : Fin m → Site) (v : Site × Site) : ℝ :=
  (L + replicaEnergy anchor z + ‖siteToPlane (v.1 - u)‖ ^ 2 +
      ‖siteToPlane (v.2 - u)‖ ^ 2) ^ (-r) *
    (1 + ‖siteToPlane (v.1 - v.2)‖ ^ (2 * a)) ^ (-p)

/-- A finite collision row is bounded uniformly in the spectator cutoff and reference site. -/
theorem sum_collisionProfileKernel_le {L a p : ℝ} {m : ℕ} (hL : 1 ≤ L)
    (ha : 0 < a) (hp : 0 < p) (hap : a * p < 1)
    (anchor : Fin m → Site) (u : Site) (pairs : Finset (Site × Site)) (k : ℕ) :
    (∑ v ∈ pairs, ∑ z ∈ finPiBox m k, collisionProfileKernel L ((m : ℝ) + 2) a p
        anchor u z v) ≤
      (9 : ℝ) ^ m * 1188 * L ^ (-(a * p)) / (a * p * (1 - a * p)) := by
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hrow (v : Site × Site) :
      (∑ z ∈ finPiBox m k, collisionProfileKernel L ((m : ℝ) + 2) a p
          anchor u z v) ≤
        (9 : ℝ) ^ m * twoCoordinateKernel L a p u v := by
    let M := L + ‖siteToPlane (v.1 - u)‖ ^ 2 + ‖siteToPlane (v.2 - u)‖ ^ 2
    have hM : 1 ≤ M := by
      dsimp [M]
      have h1 := sq_nonneg (‖siteToPlane (v.1 - u)‖)
      have h2 := sq_nonneg (‖siteToPlane (v.2 - u)‖)
      linarith
    have hspectator := sum_replicaPowerKernel_finPiBox_le m hM
      (by simp : (m : ℝ) + 2 ≤ (m : ℝ) + 2) anchor k
    have hexp : (m : ℝ) - ((m : ℝ) + 2) = -2 := by ring
    have hspectator' :
        (∑ z ∈ finPiBox m k, (M + replicaEnergy anchor z) ^ (-((m : ℝ) + 2))) ≤
          (9 : ℝ) ^ m * M ^ (-2 : ℝ) := by
      simpa [replicaPowerKernel, hexp] using hspectator
    have hweight : 0 ≤ (1 + ‖siteToPlane (v.1 - v.2)‖ ^ (2 * a)) ^ (-p) :=
      Real.rpow_nonneg (by positivity) _
    have hfactor :
        (∑ z ∈ finPiBox m k, collisionProfileKernel L ((m : ℝ) + 2) a p
            anchor u z v) =
          (1 + ‖siteToPlane (v.1 - v.2)‖ ^ (2 * a)) ^ (-p) *
            ∑ z ∈ finPiBox m k, (M + replicaEnergy anchor z) ^ (-((m : ℝ) + 2)) := by
      calc
        _ = ∑ z ∈ finPiBox m k,
              (1 + ‖siteToPlane (v.1 - v.2)‖ ^ (2 * a)) ^ (-p) *
                (M + replicaEnergy anchor z) ^ (-((m : ℝ) + 2)) := by
                  apply Finset.sum_congr rfl
                  intro z hz
                  unfold collisionProfileKernel
                  simp only [M]
                  rw [show L + replicaEnergy anchor z + ‖siteToPlane (v.1 - u)‖ ^ 2 +
                    ‖siteToPlane (v.2 - u)‖ ^ 2 =
                      L + ‖siteToPlane (v.1 - u)‖ ^ 2 +
                        ‖siteToPlane (v.2 - u)‖ ^ 2 + replicaEnergy anchor z by ring]
                  ring
        _ = _ := by rw [← Finset.mul_sum]
    rw [hfactor]
    calc
      (1 + ‖siteToPlane (v.1 - v.2)‖ ^ (2 * a)) ^ (-p) *
          ∑ z ∈ finPiBox m k, (M + replicaEnergy anchor z) ^ (-((m : ℝ) + 2)) ≤
        (1 + ‖siteToPlane (v.1 - v.2)‖ ^ (2 * a)) ^ (-p) *
          ((9 : ℝ) ^ m * M ^ (-2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hspectator' hweight
      _ = (9 : ℝ) ^ m * twoCoordinateKernel L a p u v := by
        simp [twoCoordinateKernel, M]
        ring
  calc
    (∑ v ∈ pairs, ∑ z ∈ finPiBox m k, collisionProfileKernel L ((m : ℝ) + 2) a p
        anchor u z v) ≤ ∑ v ∈ pairs, (9 : ℝ) ^ m * twoCoordinateKernel L a p u v :=
      Finset.sum_le_sum fun v _ => hrow v
    _ = (9 : ℝ) ^ m * ∑ v ∈ pairs, twoCoordinateKernel L a p u v := by
      rw [← Finset.mul_sum]
    _ ≤ (9 : ℝ) ^ m *
        (1188 * L ^ (-(a * p)) / (a * p * (1 - a * p))) :=
      mul_le_mul_of_nonneg_left (sum_twoCoordinateKernel_le hL ha hp hap u pairs)
        (by positivity)
    _ = _ := by ring

end

end Critical2DKPZ.MomentBounds
