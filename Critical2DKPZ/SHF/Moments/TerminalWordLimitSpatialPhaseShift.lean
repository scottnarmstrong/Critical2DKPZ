/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitFusedSample
public import Critical2DKPZ.SHF.Moments.WordLimitTerminalGeneral
public import Critical2DKPZ.RandomWalk.GaussianBridge
import Mathlib.Tactic

/-! # Bounded coordinate phase shifts for arbitrary starting parities -/

@[expose] public noncomputable section
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds
namespace Critical2DKPZ.SHF.Moments

/-- Correct one starting coordinate's terminal parity by a zero or unit shift. -/
def wordCoordinateParityShift (n : ℕ) (x : Site) : Site :=
  if Even (x 0 + x 1 + (n : ℤ)) then 0 else ![1, 0]

/-- The parity correction is bounded by one lattice unit. -/
theorem norm_siteToPlane_wordCoordinateParityShift_le (n : ℕ) (x : Site) :
    ‖siteToPlane (wordCoordinateParityShift n x)‖ ≤ 1 := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
  rw [norm_siteToPlane_sq]
  unfold wordCoordinateParityShift
  split_ifs <;> norm_num

/-- The shifted starting site has the even terminal phase. -/
theorem even_wordCoordinateParityShift_sub (n : ℕ) (x : Site) :
    Even ((x - wordCoordinateParityShift n x) 0 +
      (x - wordCoordinateParityShift n x) 1 + (n : ℤ)) := by
  unfold wordCoordinateParityShift
  split_ifs with hp
  · simpa only [Pi.sub_apply, Pi.zero_apply, sub_zero] using hp
  · rw [Int.even_iff] at hp ⊢
    simp only [Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    omega

/-- Each reachable coordinate has the common phase after its own fixed
starting-parity correction. No parity assumption on the initial state is used. -/
theorem word_shifted_recursion_phases {h : ℕ} (n s r : ℕ) (hfit : s + r ≤ n)
    (x u v : LatticeConfiguration h)
    (hu : u ∈ collisionWordConfigurationEndpointSet s x)
    (hv : v ∈ collisionWordConfigurationEndpointSet r u) :
    ∀ i, Even ((u i - wordCoordinateParityShift n (x i)) 0 +
      (u i - wordCoordinateParityShift n (x i)) 1 + ((n - s : ℕ) : ℤ)) ∧
      Even ((v i - wordCoordinateParityShift n (x i)) 0 +
        (v i - wordCoordinateParityShift n (x i)) 1 + ((n - s - r : ℕ) : ℤ)) := by
  intro i
  have hp := even_wordCoordinateParityShift_sub n (x i)
  have hs := endpoints_accessible_phase s (x i) (u i) (Fintype.mem_piFinset.mp hu i)
  have hr := endpoints_accessible_phase r (u i) (v i) (Fintype.mem_piFinset.mp hv i)
  rw [Int.even_iff] at hp hs hr
  simp only [Pi.sub_apply] at hp hs hr
  constructor
  · rw [Int.even_iff]
    simp only [Pi.sub_apply]
    omega
  · rw [Int.even_iff]
    simp only [Pi.sub_apply]
    omega

end Critical2DKPZ.SHF.Moments
