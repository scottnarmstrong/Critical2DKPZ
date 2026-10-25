/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Lattice.Basic
public import Critical2DKPZ.Analysis.Lattice.Volume
public import Critical2DKPZ.SHF.Moments.WordDominationTestDomination
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! # Compact test support at lattice-cell endpoints -/

@[expose] public section

open MeasureTheory
open scoped BigOperators CompactlySupported

namespace Critical2DKPZ.SHF.Moments

/-- If a compact test is supported in a radius-`R` ball in both coordinates,
then a nonzero cell average can only use sites in the radius-`R + 2` scaled
ball. The slack `2` covers the nearest-even mesh at every positive integer
scale. -/
theorem cellTestWeight_ne_zero_imp_scaled_sites_bounded {N : ℕ} (hN : 0 < N)
    (φ : C_c(Plane × Plane, ℝ)) {R : ℝ}
    (hR : ∀ p, φ p ≠ 0 → ‖p.1‖ ≤ R ∧ ‖p.2‖ ≤ R)
    (w z : Site) (hwz : cellTestWeight N φ w z ≠ 0) :
    ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane w‖ ≤ R + 2 ∧
      ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane z‖ ≤ R + 2 := by
  let S : Set (Plane × Plane) := cell N w ×ˢ cell N z
  have hS : MeasurableSet S := (measurableSet_cell N w).prod (measurableSet_cell N z)
  have hscale : (N / 4 : ℝ) ≠ 0 := by
    apply ne_of_gt
    positivity
  have hint : (∫ p in S, φ p) ≠ 0 := by
    intro hzero
    apply hwz
    simp [cellTestWeight, S, hzero]
  have hexists : ∃ p ∈ S, φ p ≠ 0 := by
    by_contra h
    have hzero : (fun p : Plane × Plane => φ p) =ᵐ[volume.restrict S]
        fun _ => (0 : ℝ) := by
      filter_upwards [ae_restrict_mem hS] with p hp
      by_contra hφ
      exact h ⟨p, hp, hφ⟩
    have := integral_eq_zero_of_ae hzero
    exact hint (by simpa [S] using this)
  obtain ⟨p, hpS, hpφ⟩ := hexists
  have hpS' : p.1 ∈ cell N w ∧ p.2 ∈ cell N z := Set.mem_prod.mp hpS
  have hpw : latticePoint N p.1 = w := by simpa using hpS'.1
  have hpz : latticePoint N p.2 = z := by simpa using hpS'.2
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.succ_le_of_lt hN)
  have hmeshPos : 0 < Real.sqrt ((N : ℝ) / 2) := Real.sqrt_pos.mpr (by positivity)
  have hmeshSqr : (1 / 2 : ℝ) ^ 2 ≤ (Real.sqrt ((N : ℝ) / 2)) ^ 2 := by
    rw [Real.sq_sqrt (by positivity : 0 ≤ (N : ℝ) / 2)]
    nlinarith
  have hmesh : (1 / 2 : ℝ) ≤ Real.sqrt ((N : ℝ) / 2) :=
    (sq_le_sq₀ (by norm_num) hmeshPos.le).mp hmeshSqr
  have hinvmesh : (Real.sqrt ((N : ℝ) / 2))⁻¹ ≤ 2 := by
    have hhalf : 0 < (1 / 2 : ℝ) := by norm_num
    have h := (one_div_le_one_div hmeshPos hhalf).2 hmesh
    simpa using h
  have hcoordinate (q : Plane) (v : Site) (hq : latticePoint N q = v)
      (hqnorm : ‖q‖ ≤ R) :
      ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane v‖ ≤ R + 2 := by
    have hmeshErr := norm_sub_latticePoint_le hN q
    rw [hq] at hmeshErr
    have htri :
        ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane v‖ ≤
          ‖q‖ + ‖q - (Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane v‖ := by
      have heq : (Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane v =
          q - (q - (Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane v) := by abel
      calc
        ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane v‖ =
            ‖q - (q - (Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane v)‖ :=
              congrArg norm heq
        _ ≤ ‖q‖ + ‖q - (Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane v‖ := norm_sub_le _ _
    exact htri.trans (by nlinarith [hqnorm, hmeshErr, hinvmesh])
  exact ⟨hcoordinate p.1 w hpw (hR p hpφ).1,
    hcoordinate p.2 z hpz (hR p hpφ).2⟩

/-- A uniformly bounded test has cell weight at most `4 M / N` in absolute
value. This is the cell-volume normalization used to turn compact pair tests
into finite start profiles for the CCR operator estimate. -/
theorem abs_cellTestWeight_le_four_mul_bound_div {N : ℕ} (hN : 0 < N)
    (φ : C_c(Plane × Plane, ℝ)) (M : ℝ) (hM : 0 ≤ M)
    (hφ : ∀ p, |φ p| ≤ M) (w z : Site) :
    |cellTestWeight N φ w z| ≤ 4 * M / N := by
  let S : Set (Plane × Plane) := cell N w ×ˢ cell N z
  have hS : MeasurableSet S := (measurableSet_cell N w).prod (measurableSet_cell N z)
  have hscale : 0 ≤ (N / 4 : ℝ) := by positivity
  by_cases hw : w ∈ evenLattice
  · by_cases hz : z ∈ evenLattice
    · have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
      have hfinite : volume S < ⊤ := by
        rw [Measure.volume_eq_prod, Measure.prod_prod]
        exact ENNReal.mul_lt_top (volume_cell_lt_top hN hw)
          (volume_cell_lt_top hN hz)
      have hvolume : (volume S).toReal = (16 : ℝ) / (N : ℝ) ^ 2 := by
        rw [Measure.volume_eq_prod, Measure.prod_prod]
        rw [ENNReal.toReal_mul]
        rw [volume_cell_toReal hN hw, volume_cell_toReal hN hz]
        field_simp [ne_of_gt hNreal]
        ring
      have hφint : IntegrableOn (fun p : Plane × Plane => φ p) S volume := by
        apply IntegrableOn.of_bound hfinite φ.continuous.measurable.aestronglyMeasurable M
        filter_upwards [] with p
        rw [Real.norm_eq_abs]
        exact hφ p
      have hconst : IntegrableOn (fun _ : Plane × Plane => M) S volume :=
        integrableOn_const hfinite.ne
      have hpoint : ∀ p ∈ S, |φ p| ≤ M := fun p _ => hφ p
      have hint : |∫ p in S, φ p| ≤ ∫ p in S, |φ p| :=
        abs_integral_le_integral_abs
      have hbound : ∫ p in S, |φ p| ≤ M * (volume S).toReal := by
        calc
          ∫ p in S, |φ p| ≤ ∫ p in S, (fun _ : Plane × Plane => M) p :=
            setIntegral_mono_on (hφint.norm) hconst hS hpoint
          _ = M * (volume S).toReal := by
            rw [setIntegral_const, measureReal_def, smul_eq_mul]
            ring
      have hscaled := mul_le_mul_of_nonneg_left
        (hint.trans hbound) hscale
      rw [cellTestWeight, abs_mul, abs_of_nonneg hscale]
      calc
        (N / 4 : ℝ) * |∫ p in S, φ p| ≤ (N / 4 : ℝ) *
            (M * (volume S).toReal) := hscaled
        _ = 4 * M / N := by rw [hvolume]; field_simp; ring
    · have hEmpty : cell N z = ∅ := cell_eq_empty_of_not_even hz
      simp [cellTestWeight, hEmpty]
      positivity
  · have hEmpty : cell N w = ∅ := cell_eq_empty_of_not_even hw
    simp [cellTestWeight, hEmpty]
    positivity

end Critical2DKPZ.SHF.Moments

end
