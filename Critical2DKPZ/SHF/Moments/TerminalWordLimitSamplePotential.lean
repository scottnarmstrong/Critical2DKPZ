/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitPotentialGreen
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitSampling
public import Critical2DKPZ.SHF.Moments.EntranceGeneral
import Critical2DKPZ.Analysis.Lattice.Basic
import Mathlib.Tactic

/-! # Integrable inverse-distance majorants for phase-correct samples -/

@[expose] public noncomputable section

open Critical2DKPZ.Polymer

namespace Critical2DKPZ.SHF.Moments

/-- The phase shift does not enlarge the nearest-grid sampling error. -/
theorem norm_sub_pairTwoFutureSampleSite_le {N : ℕ} (hN : 0 < N)
    (k : ℕ) (y : Plane) :
    ‖y - latticeRepresentative N (pairTwoFutureSampleSite N k y)‖ ≤
      (Real.sqrt ((N : ℝ) / 2))⁻¹ := by
  have heq : y - latticeRepresentative N (pairTwoFutureSampleSite N k y) =
      (y - latticeRepresentative N (entranceParityShift k)) -
        latticeRepresentative N (latticePoint N (y - latticeRepresentative N (entranceParityShift k))) := by
    rw [pairTwoFutureSampleSite, latticeRepresentative_add]
    abel
  rw [heq]
  exact norm_sub_latticePoint_le hN _

private theorem sqrt_mul_latticeMesh_le_two {N : ℕ} (hN : 0 < N) :
    Real.sqrt (N : ℝ) * (Real.sqrt ((N : ℝ) / 2))⁻¹ ≤ 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt ((N : ℝ) / 2) := by positivity
  rw [← div_eq_mul_inv, div_le_iff₀ hs]
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt hNr.le, Real.sq_sqrt (by positivity)]
  linarith only [hNr]

/-- A sampled gap can vanish, but its continuum separation is bounded by the
regularized discrete gap times the mesh. This handles the diagonal cells. -/
theorem scaled_norm_sub_le_sampleGap {N : ℕ} (hN : 0 < N)
    (k : ℕ) (a b : Plane) :
    Real.sqrt (N : ℝ) * ‖b - a‖ ≤
      4 * (1 + ‖siteToPlane (pairTwoFutureSampleSite N k b - pairTwoFutureSampleSite N k a)‖) := by
  let a' := latticeRepresentative N (pairTwoFutureSampleSite N k a)
  let b' := latticeRepresentative N (pairTwoFutureSampleSite N k b)
  let r := ‖siteToPlane (pairTwoFutureSampleSite N k b - pairTwoFutureSampleSite N k a)‖
  let mesh := (Real.sqrt ((N : ℝ) / 2))⁻¹
  have hmesh := sqrt_mul_latticeMesh_le_two hN
  have hgap : ‖b' - a'‖ = mesh * r := by
    rw [← latticeRepresentative_sub]
    simp only [latticeRepresentative, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    rfl
  have herr : ‖b - a‖ ≤ mesh + mesh * r + mesh := by
    calc
      _ = ‖(b - b') + (b' - a') + (a' - a)‖ := by congr 1; abel
      _ ≤ ‖b - b'‖ + ‖b' - a'‖ + ‖a' - a‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ _ := add_le_add (add_le_add (norm_sub_pairTwoFutureSampleSite_le hN k b) hgap.le)
        (by simpa only [norm_sub_rev] using norm_sub_pairTwoFutureSampleSite_le hN k a)
  calc
    _ ≤ Real.sqrt (N : ℝ) * (mesh + mesh * r + mesh) :=
      mul_le_mul_of_nonneg_left herr (Real.sqrt_nonneg _)
    _ = (Real.sqrt (N : ℝ) * mesh) * (2 + r) := by ring
    _ ≤ 2 * (2 + r) := mul_le_mul_of_nonneg_right hmesh (by dsimp [r]; positivity)
    _ ≤ _ := by dsimp [r]; nlinarith only [norm_nonneg (siteToPlane
      (pairTwoFutureSampleSite N k b - pairTwoFutureSampleSite N k a))]


end Critical2DKPZ.SHF.Moments
