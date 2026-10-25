/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Heat.Moments
public import Critical2DKPZ.SHF.Moments.Dictionary
public import Critical2DKPZ.SHF.Moments.EntranceRiemann
import Mathlib.Tactic

/-! # Diagonal short-time collision-profile bounds -/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Critical2DKPZ.SHF.Moments

private theorem integral_norm_mul_heatKernel_le_sqrt {u : ℝ} (hu : 0 < u) :
    ∫ x : Plane, ‖x‖ * heatKernel u x ≤ (9 / 2) * Real.sqrt u := by
  have hsqrt : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
  have hsq : Real.sqrt u * Real.sqrt u = u := by
    nlinarith [Real.sq_sqrt hu.le]
  have hsecond : Integrable (fun x : Plane => ‖x‖ ^ 2 * heatKernel u x) := by
    simpa using Critical2DKPZ.integrable_norm_pow_mul_heatKernel_even hu 1
  have hEq : (fun x : Plane => (1 + ‖x‖ ^ 2 / u) * heatKernel u x) =
      (fun x => heatKernel u x) + (fun x => u⁻¹ * (‖x‖ ^ 2 * heatKernel u x)) := by
    funext x
    change (1 + ‖x‖ ^ 2 * u⁻¹) * heatKernel u x =
      heatKernel u x + u⁻¹ * (‖x‖ ^ 2 * heatKernel u x)
    ring
  have hbase : Integrable (fun x : Plane =>
      (1 + ‖x‖ ^ 2 / u) * heatKernel u x) := by
    have hkernel := Critical2DKPZ.integrable_heatKernel hu
    rw [hEq]
    exact hkernel.add (by simpa [mul_comm, mul_left_comm, mul_assoc] using hsecond.const_mul u⁻¹)
  have hmajorant : Integrable (fun x : Plane =>
      (Real.sqrt u / 2) * ((1 + ‖x‖ ^ 2 / u) * heatKernel u x)) :=
    hbase.const_mul (Real.sqrt u / 2)
  have hleft : Integrable (fun x : Plane => ‖x‖ * heatKernel u x) := by
    simpa using Critical2DKPZ.integrable_norm_pow_mul_heatKernel hu 1
  have hpoint (x : Plane) : ‖x‖ * heatKernel u x ≤
      (Real.sqrt u / 2) * ((1 + ‖x‖ ^ 2 / u) * heatKernel u x) := by
    have hdiff : Real.sqrt u / 2 * (1 + ‖x‖ ^ 2 / u) - ‖x‖ =
        (‖x‖ - Real.sqrt u) ^ 2 / (2 * Real.sqrt u) := by
      field_simp [hu.ne', hsqrt.ne']
      nlinarith [hsq]
    have hscalar : ‖x‖ ≤ Real.sqrt u / 2 * (1 + ‖x‖ ^ 2 / u) := by
      rw [← sub_nonneg, hdiff]
      positivity
    calc
      ‖x‖ * heatKernel u x ≤
          (Real.sqrt u / 2 * (1 + ‖x‖ ^ 2 / u)) * heatKernel u x :=
        mul_le_mul_of_nonneg_right hscalar (Critical2DKPZ.heatKernel_nonneg hu.le x)
      _ = (Real.sqrt u / 2) * ((1 + ‖x‖ ^ 2 / u) * heatKernel u x) := by ring
  have hmoment := Critical2DKPZ.integral_norm_pow_mul_heatKernel_even_le hu 1
  have hmoment' : (∫ x : Plane, ‖x‖ ^ 2 * heatKernel u x) ≤ 8 * u := by
    have h := hmoment
    norm_num [Nat.factorial] at h
    nlinarith [h]
  have hineq := integral_mono hleft hmajorant hpoint
  calc
    _ ≤ (Real.sqrt u / 2) * (1 + u⁻¹ *
        ∫ x : Plane, ‖x‖ ^ 2 * heatKernel u x) := by
      calc
        _ ≤ ∫ x : Plane,
            (Real.sqrt u / 2) * ((1 + ‖x‖ ^ 2 / u) * heatKernel u x) := hineq
        _ = _ := by
          have hbaseIntegral :
              ∫ x : Plane, (1 + ‖x‖ ^ 2 / u) * heatKernel u x =
                1 + u⁻¹ * ∫ x : Plane, ‖x‖ ^ 2 * heatKernel u x := by
            calc
              _ = ∫ x : Plane, heatKernel u x +
                  u⁻¹ * (‖x‖ ^ 2 * heatKernel u x) := by
                    rw [hEq]
                    rfl
              _ = _ := by
                rw [integral_add (Critical2DKPZ.integrable_heatKernel hu)
                    (by simpa [mul_comm, mul_left_comm, mul_assoc] using hsecond.const_mul u⁻¹),
                  Critical2DKPZ.integral_heatKernel hu, integral_const_mul]
          rw [integral_const_mul, hbaseIntegral]
    _ ≤ (Real.sqrt u / 2) * 9 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have huinv : 0 ≤ u⁻¹ := inv_nonneg.mpr hu.le
      have hmul := mul_le_mul_of_nonneg_left hmoment' huinv
      have huunit : u⁻¹ * (8 * u) = 8 := by field_simp [hu.ne']
      rw [huunit] at hmul
      nlinarith
    _ = (9 / 2) * Real.sqrt u := by ring

/-- Linear vanishing of the test controls the diagonal heat-pair profile by an
integrable `u^{-1/2}` singularity. -/
theorem heatKernelPairProfileIntegral_diagonal_bound
    {a : Plane} (F : ℝ × Plane → ℝ) (L : ℝ)
    (hL : 0 ≤ L) (hFcont : Continuous F)
    (hFvanish : ∀ u x, 0 < u → |F (u, x)| ≤ L * (u + ‖x - a‖))
    {u : ℝ} (hu : 0 < u) :
    |heatKernelPairProfileIntegral u a a F| ≤
      L * heatKernel (2 * u) 0 * (u + (9 / 2) * Real.sqrt (u / 2)) := by
  let v : ℝ := u / 2
  let c : ℝ := heatKernel (2 * u) 0
  let pair : Plane → ℝ := fun x => heatKernel u (x - a) * heatKernel u (x - a)
  let majorant : Plane → ℝ := fun x => L * c *
    (u * heatKernel v (x - a) + ‖x - a‖ * heatKernel v (x - a))
  have hv : 0 < v := by dsimp [v]; linarith
  have hc : 0 ≤ c := Critical2DKPZ.heatKernel_nonneg (by positivity) 0
  have hcenter : (1 / 2 : ℝ) • (a + a) = a := by module
  have hpair (x : Plane) : pair x = c * heatKernel v (x - a) := by
    dsimp [pair, c, v]
    rw [heatKernel_product_center_factorization hu a a x]
    rw [hcenter]
    simp
  have hkernelInt : Integrable (fun x : Plane => heatKernel v (x - a)) :=
    (Critical2DKPZ.integrable_heatKernel hv).comp_sub_right a
  have hmomentInt : Integrable (fun x : Plane =>
      ‖x - a‖ * heatKernel v (x - a)) := by
    have h := Critical2DKPZ.integrable_norm_pow_mul_heatKernel hv 1
    have h' := h.comp_sub_right a
    simpa only [pow_one] using h'
  have htimeInt : Integrable (fun x : Plane => u * heatKernel v (x - a)) := by
    simpa [mul_comm] using hkernelInt.const_mul u
  have hmajorantInt : Integrable majorant := by
    have hsum : Integrable (fun x : Plane =>
        u * heatKernel v (x - a) + ‖x - a‖ * heatKernel v (x - a)) :=
      htimeInt.add hmomentInt
    simpa only [majorant] using hsum.const_mul (L * c)
  have hFslice : Continuous (fun x : Plane => F (u, x)) :=
    hFcont.comp (continuous_const.prodMk continuous_id)
  have hpairCont : Continuous pair := by
    dsimp [pair]
    exact (Critical2DKPZ.continuous_heatKernel u).comp
        (continuous_id.sub continuous_const) |>.mul
      ((Critical2DKPZ.continuous_heatKernel u).comp
        (continuous_id.sub continuous_const))
  have hpairMeas : AEStronglyMeasurable pair := by
    exact hpairCont.aestronglyMeasurable
  have hprodInt : Integrable (fun x : Plane => F (u, x) * pair x) := by
    apply hmajorantInt.mono' (hFslice.aestronglyMeasurable.mul hpairMeas)
    filter_upwards [] with x
    change |F (u, x) * pair x| ≤ majorant x
    rw [abs_mul, hpair x, abs_mul, abs_of_nonneg hc,
      abs_of_nonneg (Critical2DKPZ.heatKernel_nonneg hv.le (x - a))]
    calc
      |F (u, x)| * (c * heatKernel v (x - a)) ≤
          (L * (u + ‖x - a‖)) * (c * heatKernel v (x - a)) :=
        mul_le_mul_of_nonneg_right (hFvanish u x hu)
          (mul_nonneg hc (Critical2DKPZ.heatKernel_nonneg hv.le _))
      _ = majorant x := by dsimp [majorant]; ring
  have hpairNonneg (x : Plane) : 0 ≤ pair x :=
    mul_nonneg (Critical2DKPZ.heatKernel_nonneg hu.le _) (Critical2DKPZ.heatKernel_nonneg hu.le _)
  have hintegralBound :
      |∫ x : Plane, F (u, x) * pair x| ≤
        L * c * (u + (9 / 2) * Real.sqrt v) := by
    have hmomentShift :
        ∫ x : Plane, ‖x - a‖ * heatKernel v (x - a) ≤ (9 / 2) * Real.sqrt v := by
      rw [integral_sub_right_eq_self (fun x : Plane => ‖x‖ * heatKernel v x) a]
      exact integral_norm_mul_heatKernel_le_sqrt hv
    have hpairMajorantIntegral :
        ∫ x : Plane, majorant x =
          L * c * (u + ∫ x : Plane, ‖x - a‖ * heatKernel v (x - a)) := by
      change ∫ x : Plane, (L * c) *
          (u * heatKernel v (x - a) + ‖x - a‖ * heatKernel v (x - a)) = _
      rw [integral_const_mul, integral_add htimeInt hmomentInt, integral_const_mul,
        Critical2DKPZ.integral_heatKernel_sub hv a]
      ring
    calc
      _ = ‖∫ x : Plane, F (u, x) * pair x‖ := by rw [Real.norm_eq_abs]
      _ ≤ ∫ x : Plane, ‖F (u, x) * pair x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x : Plane, majorant x := by
        apply integral_mono hprodInt.norm hmajorantInt
        intro x
        change ‖F (u, x) * pair x‖ ≤ majorant x
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hpairNonneg x)]
        calc
          |F (u, x)| * pair x ≤ L * (u + ‖x - a‖) * pair x :=
            mul_le_mul_of_nonneg_right (hFvanish u x hu) (hpairNonneg x)
          _ = majorant x := by rw [hpair x]; dsimp [majorant, c, v]; ring
      _ ≤ L * c * (u + (9 / 2) * Real.sqrt v) := by
        rw [hpairMajorantIntegral]
        have hsum : u + ∫ x : Plane, ‖x - a‖ * heatKernel v (x - a) ≤
            u + (9 / 2) * Real.sqrt v := by linarith [hmomentShift]
        exact mul_le_mul_of_nonneg_left hsum (mul_nonneg hL hc)
  simpa only [heatKernelPairProfileIntegral, pair, c, v] using hintegralBound

end Critical2DKPZ.SHF.Moments

end
