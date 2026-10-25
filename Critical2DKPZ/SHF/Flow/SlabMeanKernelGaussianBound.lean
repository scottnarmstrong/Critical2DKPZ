/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Limit.SlabMean
public import Critical2DKPZ.SHF.Moments.WalkBounds
public import Critical2DKPZ.Analysis.Lattice.Sampling
public import Critical2DKPZ.PolymerCalculus.Clocks
import Mathlib.Tactic

/-! # Uniform Gaussian envelope for a mean slab kernel -/

@[expose] public section

open Critical2DKPZ.SHF.Limit
open Critical2DKPZ.SHF.Moments

namespace Critical2DKPZ.SHF.Flow

/-- A positive macroscopic slab has a Gaussian bound uniform over every lattice scale. -/
theorem exists_slabMeanKernel_gaussianBound (ϑ : ℝ) {t : ℝ} (ht : 0 ≤ t)
    {v : ℝ} (hv : 0 < v) :
    ∃ C c : ℝ, 0 < c ∧ ∀ N : ℕ, ∀ x y : Plane,
      |slabMeanKernel ϑ N t (t + v) x y| ≤ C * Real.exp (-c * ‖y - x‖ ^ 2) := by
  obtain ⟨Cw, cw, hCw, hcw, hwalk⟩ := srwKernel_gaussianBound_all_times
  let c := cw / (4 * (v + 3))
  refine ⟨Cw / v * Real.exp (4 * cw), c, ?_, ?_⟩
  · dsimp [c]
    positivity
  · intro N x y
    by_cases hN : N = 0
    · subst N
      rw [slabMeanKernel_eq_srwKernel]
      simp
      exact le_of_lt (mul_pos (mul_pos (div_pos hCw hv) (Real.exp_pos _))
        (Real.exp_pos _))
    · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
      let m := evenCeil ((N : ℝ) * (t + v)) - evenCeil ((N : ℝ) * t)
      let z := latticePoint N y - latticePoint N x
      let r := latticeRepresentative N z
      have hmono : evenCeil ((N : ℝ) * t) ≤ evenCeil ((N : ℝ) * (t + v)) :=
        evenCeil_mono (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
      have hmcast : (m : ℝ) =
          (evenCeil ((N : ℝ) * (t + v)) : ℝ) - evenCeil ((N : ℝ) * t) := by
        simp only [m, Nat.cast_sub hmono]
      have hround := evenCeil_duration_error
        (s := (N : ℝ) * t) (t := (N : ℝ) * (t + v)) (by positivity) (by positivity)
      have hclock : |(m : ℝ) - (N : ℝ) * v| < 2 := by
        rw [hmcast]
        convert hround using 1
        ring_nf
      have hmupper : (m : ℝ) + 1 ≤ (N : ℝ) * v + 3 := by
        have h := (abs_lt.mp hclock).2
        linarith
      have hNcast : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
      have hcoeff : (N : ℝ) / (4 * ((m : ℝ) + 1)) ≤ 1 / v := by
        by_cases hlarge : 4 ≤ (N : ℝ) * v
        · have hmlower : (N : ℝ) * v / 2 ≤ (m : ℝ) + 1 := by
            have h := (abs_lt.mp hclock).1
            linarith
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith only [hmlower]
        · have hNvsmall : (N : ℝ) * v < 4 := lt_of_not_ge hlarge
          have hone : 1 ≤ (m : ℝ) + 1 := by
            have hmnonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
            linarith
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith only [hNvsmall, hone]
      have hrrep : latticeRepresentative N z = cellSample N y - cellSample N x := by
        simp only [z, latticeRepresentative, cellSample]
        rw [← smul_sub]
        congr 1
        ext i
        simp [siteToPlane]
      have hdist : ‖(y - x) - r‖ ≤ 2 * (Real.sqrt ((N : ℝ) / 2))⁻¹ := by
        change ‖(y - x) - latticeRepresentative N z‖ ≤ _
        rw [hrrep]
        have hrewrite : (y - x) - (cellSample N y - cellSample N x) =
            (y - cellSample N y) - (x - cellSample N x) := by abel
        rw [hrewrite]
        calc
          ‖(y - cellSample N y) - (x - cellSample N x)‖ ≤
              ‖y - cellSample N y‖ + ‖x - cellSample N x‖ := norm_sub_le _ _
          _ ≤ (Real.sqrt ((N : ℝ) / 2))⁻¹ +
              (Real.sqrt ((N : ℝ) / 2))⁻¹ := by
            have hy := dist_cellSample_le hNpos y
            have hx := dist_cellSample_le hNpos x
            rw [dist_comm, dist_eq_norm] at hy hx
            exact add_le_add hy hx
          _ = _ := by ring
      have hmeshSq : (Real.sqrt ((N : ℝ) / 2))⁻¹ ^ 2 = 2 / (N : ℝ) := by
        rw [inv_pow, Real.sq_sqrt (by positivity)]
        field_simp
      have hrepSq : ‖r‖ ^ 2 ≥ ‖y - x‖ ^ 2 / 2 - 8 / (N : ℝ) := by
        have htri : ‖y - x‖ ≤ ‖r‖ + 2 * (Real.sqrt ((N : ℝ) / 2))⁻¹ := by
          calc
            ‖y - x‖ = ‖((y - x) - r) + r‖ := by congr 1; abel
            _ ≤ ‖(y - x) - r‖ + ‖r‖ := norm_add_le _ _
            _ ≤ 2 * (Real.sqrt ((N : ℝ) / 2))⁻¹ + ‖r‖ := add_le_add hdist le_rfl
            _ = _ := by ring
        have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr htri
        have hyoung : (‖r‖ + 2 * (Real.sqrt ((N : ℝ) / 2))⁻¹) ^ 2 ≤
            2 * ‖r‖ ^ 2 + 8 * (Real.sqrt ((N : ℝ) / 2))⁻¹ ^ 2 := by
          nlinarith only [sq_nonneg (‖r‖ -
            2 * (Real.sqrt ((N : ℝ) / 2))⁻¹)]
        have hcombined : ‖y - x‖ ^ 2 ≤
            2 * ‖r‖ ^ 2 + 8 * (Real.sqrt ((N : ℝ) / 2))⁻¹ ^ 2 := le_trans hsq hyoung
        rw [hmeshSq] at hcombined
        rw [show 8 * (2 / (N : ℝ)) = 16 / (N : ℝ) by ring] at hcombined
        have hhalf : ‖y - x‖ ^ 2 / 2 ≤ ‖r‖ ^ 2 + 8 / (N : ℝ) := by
          calc
            ‖y - x‖ ^ 2 / 2 ≤ (2 * ‖r‖ ^ 2 + 16 / (N : ℝ)) / 2 :=
              div_le_div_of_nonneg_right hcombined (by norm_num)
            _ = ‖r‖ ^ 2 + 8 / (N : ℝ) := by ring
        linarith
      have hroot : 0 < Real.sqrt ((N : ℝ) / 2) := Real.sqrt_pos.mpr (by positivity)
      have hsite : siteToPlane z = Real.sqrt ((N : ℝ) / 2) • r := by
        dsimp [r, latticeRepresentative]
        rw [smul_smul, mul_inv_cancel₀ hroot.ne', one_smul]
      have hsiteSq : ‖siteToPlane z‖ ^ 2 = ((N : ℝ) / 2) * ‖r‖ ^ 2 := by
        rw [hsite, norm_smul, Real.norm_eq_abs, abs_of_pos hroot, mul_pow,
          Real.sq_sqrt (by positivity : 0 ≤ (N : ℝ) / 2)]
      let α := cw * (N : ℝ) / (2 * ((m : ℝ) + 1))
      have hαnonneg : 0 ≤ α := by dsimp [α]; positivity
      have hαlower : cw / (2 * (v + 3)) ≤ α := by
        dsimp [α]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith only [hmupper, hNcast, hcw.le, hv.le]
      have hαmesh : α * (8 / (N : ℝ)) ≤ 4 * cw := by
        have hone : 1 ≤ (m : ℝ) + 1 := by
          have hmnonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
          linarith
        have heq : α * (8 / (N : ℝ)) = 4 * cw / ((m : ℝ) + 1) := by
          dsimp [α]
          field_simp
          ring
        rw [heq, div_le_iff₀ (by positivity)]
        nlinarith only [hone, hcw.le]
      have hαhalf : c ≤ α / 2 := by
        calc
          cw / (4 * (v + 3)) = (cw / (2 * (v + 3))) * (1 / 2) := by field_simp; ring
          _ ≤ α * (1 / 2) := mul_le_mul_of_nonneg_right hαlower (by norm_num)
          _ = α / 2 := by ring
      have hαd : c * ‖y - x‖ ^ 2 ≤ α * ‖y - x‖ ^ 2 / 2 := by
        have h := mul_le_mul_of_nonneg_right hαhalf (sq_nonneg ‖y - x‖)
        nlinarith only [h]
      have hexpArg : -(cw * ‖siteToPlane z‖ ^ 2 / ((m : ℝ) + 1)) ≤
          4 * cw - c * ‖y - x‖ ^ 2 := by
        have harg : cw * ‖siteToPlane z‖ ^ 2 / ((m : ℝ) + 1) = α * ‖r‖ ^ 2 := by
          rw [hsiteSq]
          dsimp [α]
          field_simp
        have hmain := mul_le_mul_of_nonneg_left hrepSq hαnonneg
        rw [harg]
        rw [mul_sub] at hmain
        nlinarith only [hmain, hαmesh, hαd]
      have hexp : Real.exp (-cw * ‖siteToPlane z‖ ^ 2 / ((m : ℝ) + 1)) ≤
          Real.exp (4 * cw) * Real.exp (-c * ‖y - x‖ ^ 2) := by
        have hargForm : -cw * ‖siteToPlane z‖ ^ 2 / ((m : ℝ) + 1) =
            -(cw * ‖siteToPlane z‖ ^ 2 / ((m : ℝ) + 1)) := by ring
        rw [hargForm]
        calc
          Real.exp (-(cw * ‖siteToPlane z‖ ^ 2 / ((m : ℝ) + 1))) ≤
              Real.exp (4 * cw - c * ‖y - x‖ ^ 2) := Real.exp_le_exp.mpr hexpArg
          _ = Real.exp (4 * cw) * Real.exp (-c * ‖y - x‖ ^ 2) := by
            rw [← Real.exp_add]
            congr 1
            ring
      have hformula : slabMeanKernel ϑ N t (t + v) x y =
          ((N : ℝ) / 4) * srwKernel m z := by
        rw [slabMeanKernel_eq_srwKernel]
      rw [hformula, abs_of_nonneg (mul_nonneg (by positivity) (srwKernel_nonneg _ _))]
      calc
        ((N : ℝ) / 4) * srwKernel m z ≤
          ((N : ℝ) / 4) * (Cw / ((m : ℝ) + 1) *
            Real.exp (-cw * ‖siteToPlane z‖ ^ 2 / ((m : ℝ) + 1)) : ℝ) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact hwalk m z
        _ ≤ (Cw / v) * (Real.exp (4 * cw) * Real.exp (-c * ‖y - x‖ ^ 2)) := by
          have hcoef' : (N : ℝ) / 4 * (Cw / ((m : ℝ) + 1)) ≤ Cw / v := by
            rw [show (N : ℝ) / 4 * (Cw / ((m : ℝ) + 1)) =
              Cw * ((N : ℝ) / (4 * ((m : ℝ) + 1))) by field_simp]
            calc
              Cw * ((N : ℝ) / (4 * ((m : ℝ) + 1))) ≤ Cw * (1 / v) :=
                mul_le_mul_of_nonneg_left hcoeff hCw.le
              _ = Cw / v := by ring
          calc
            ((N : ℝ) / 4) * (Cw / ((m : ℝ) + 1) *
                Real.exp (-cw * ‖siteToPlane z‖ ^ 2 / ((m : ℝ) + 1))) ≤
                ((N : ℝ) / 4 * (Cw / ((m : ℝ) + 1))) *
                  (Real.exp (4 * cw) * Real.exp (-c * ‖y - x‖ ^ 2)) := by
              calc
                _ = ((N : ℝ) / 4 * (Cw / ((m : ℝ) + 1))) *
                    Real.exp (-cw * ‖siteToPlane z‖ ^ 2 / ((m : ℝ) + 1)) := by ring
                _ ≤ ((N : ℝ) / 4 * (Cw / ((m : ℝ) + 1))) *
                    (Real.exp (4 * cw) * Real.exp (-c * ‖y - x‖ ^ 2)) :=
                  mul_le_mul_of_nonneg_left hexp (by positivity)
            _ ≤ (Cw / v) * (Real.exp (4 * cw) * Real.exp (-c * ‖y - x‖ ^ 2)) :=
              mul_le_mul_of_nonneg_right hcoef' (by positivity)
        _ = (Cw / v * Real.exp (4 * cw)) * Real.exp (-c * ‖y - x‖ ^ 2) := by ring

end Critical2DKPZ.SHF.Flow

end
