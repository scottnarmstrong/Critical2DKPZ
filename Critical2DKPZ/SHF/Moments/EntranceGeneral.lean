/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.EntranceDiagonalAssembly
import Mathlib.Tactic

/-! # Collision entrance limits -/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Moments


/-- Lattice representatives preserve addition of microscopic sites. -/
theorem latticeRepresentative_add (N : ℕ) (x y : Site) :
    latticeRepresentative N (x + y) =
      latticeRepresentative N x + latticeRepresentative N y := by
  ext i
  have hsite : siteToPlane (x + y) = siteToPlane x + siteToPlane y := by
    ext j
    simp [siteToPlane]
  rw [latticeRepresentative, latticeRepresentative, latticeRepresentative, hsite, smul_add]

/-- Collision entrances converge in three regimes: positive entrance time, separated centers at time zero, and coalescing centers with a linearly vanishing test and the stated centering rate. -/
theorem tendsto_collisionEntrance_spatial_test_local_limit
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t)
    (aSite bSite : ℕ → Site)
    (haSite : ∀ N, aSite N ∈ evenLattice)
    (hbSite : ∀ N, bSite N ∈ evenLattice)
    (a b : Plane)
    (ha : Tendsto (fun N => latticeRepresentative N (aSite N)) atTop (𝓝 a))
    (hb : Tendsto (fun N => latticeRepresentative N (bSite N)) atTop (𝓝 b))
    (F : ℝ × Plane → ℝ) (R M : ℝ) (hM : 0 ≤ M)
    (hFcont : Continuous F)
    (hFbound : ∀ u x, |F (u, x)| ≤ M)
    (hFsupport : ∀ u x, F (u, x) ≠ 0 → ‖x‖ ≤ R)
    (hregime : 0 < s ∨ (s = 0 ∧ a ≠ b) ∨
      (s = 0 ∧ a = b ∧ ∃ L : ℝ, 0 ≤ L ∧
        Tendsto (fun N : ℕ => ‖latticeRepresentative N (aSite N) - a‖ *
          Real.log ((N : ℝ) + 2)) atTop (𝓝 0) ∧
        Tendsto (fun N : ℕ => ‖latticeRepresentative N (bSite N) - a‖ *
          Real.log ((N : ℝ) + 2)) atTop (𝓝 0) ∧
        ∀ u x, 0 ≤ u → |F (u, x)| ≤ L * (u + ‖x - a‖))) :
    Tendsto (fun N : ℕ => collisionEntrance N
      (if 0 < s then evenCeil ((N : ℝ) * s) + 1 else 0)
      (evenCeil ((N : ℝ) * t)) (aSite N) (bSite N) F) atTop
      (𝓝 (4 * (∫ u in s..t, heatKernelPairProfileIntegral u a b F))) := by
  rcases hregime with hspos | ⟨hs0, hab⟩ | ⟨hs0, hab, L, hL, hcenterA, hcenterB, hFvanish⟩
  · have h := tendsto_collisionEntrance_spatial_test_away_zero
      hspos hst aSite bSite haSite hbSite a b ha hb F R M hM hFcont hFbound hFsupport
    simpa [hspos] using h
  · subst s
    have h := tendsto_collisionEntrance_spatial_test_offDiagonal_zero
      hab (sub_pos.mpr hst) aSite bSite haSite hbSite ha hb F R M hM hFcont
      hFbound hFsupport
    simpa using h
  · subst s
    subst b
    have h := tendsto_collisionEntrance_spatial_test_coalescing_center_zero
      (sub_pos.mpr hst) aSite bSite a haSite hbSite hcenterA hcenterB F R M L
      hM hL hFcont hFbound hFsupport hFvanish
    simpa using h


end Critical2DKPZ.SHF.Moments

end
