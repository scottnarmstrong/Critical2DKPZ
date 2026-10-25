/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.SmoothedCovariance
import Mathlib.Tactic

/-! # Short-clock moments of a diffuse initial profile -/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.Smoothing

/-- The first-collision identity for a diffuse walk-kernel profile over a short clock. The
collision kernel retains the initial smoothing width, which is useful when the clock changes by
only finitely many steps. -/
theorem integrable_walkKernel_shortProfile_sq_eq_firstCollision (β : ℝ)
    (d s : ℕ) (x : Site) :
    (∀ r ∈ Finset.Icc 1 s,
      Integrable (fun ω => pointToPlane β 0 (s - r) 0 ω ^ 2) disorderLaw) ∧
    Integrable (fun ω =>
      profileP2Fun β 0 s (fun y => srwKernel d (y - x)) (fun _ => 1) ω ^ 2)
      disorderLaw ∧
    (∫ ω, profileP2Fun β 0 s (fun y => srwKernel d (y - x)) (fun _ => 1) ω ^ 2
      ∂disorderLaw) - 1 =
      ∑ r ∈ Finset.Icc 1 s,
        srwKernel (2 * (d + r)) 0 * Polymer.sigmaSq β *
          (∫ ω, pointToPlane β 0 (s - r) 0 ω ^ 2 ∂disorderLaw) := by
  classical
  let A := Polymer.endpoints x d
  let ν : Site → ℝ := fun y => srwKernel d (y - x)
  have hνA : ∀ y ∉ A, ν y = 0 := by
    intro y hy
    exact Polymer.srwKernel_eq_zero_of_not_mem d x y (by simpa [A] using hy)
  have hν0 : ∀ y, 0 ≤ ν y := fun y => Polymer.kernel_nonneg d (y - x)
  have hν1 : ∑ y ∈ A, ν y = 1 := by
    exact Polymer.sum_srwKernel_endpoints d x
  have hprofileMem : MemLp
      (profileP2Fun β 0 s ν (fun _ => 1)) 2 disorderLaw := by
    exact Polymer.memLp_profileP2Fun_finset β 0 s ν (fun _ => 1) A hνA 2 (by norm_num)
  have hprofileInt : Integrable
      (fun ω => profileP2Fun β 0 s ν (fun _ => 1) ω ^ 2) disorderLaw := by
    have h := hprofileMem.integrable_norm_pow'
    simpa only [Real.norm_eq_abs, sq_abs] using h
  have hcollisionInt : ∀ r ∈ Finset.Icc 1 s,
      Integrable (fun ω => pointToPlane β 0 (s - r) 0 ω ^ 2) disorderLaw := by
    intro r hr
    exact Polymer.integrable_pow_pointToPlane β 0 (s - r) 0 2
  have hfc := Polymer.probability_profile_firstCollision_finset β 0 s ν ν A A
    hνA hνA hν1 hν1
  have hkernel (r : ℕ) :
      (∑ y ∈ A, ∑ z ∈ A,
        ν y * ν z * srwKernel (2 * r) (z - y)) =
        srwKernel (2 * (d + r)) 0 := by
    have h := Polymer.kernel_sandwich d (2 * r) x x
    simpa [A, ν, two_mul, Nat.mul_add, add_comm, add_left_comm, add_assoc,
      sub_self] using h
  have hcollect :
      (∑ r ∈ Finset.Icc 1 s, ∑ y ∈ A, ∑ z ∈ A,
        ν y * ν z * srwKernel (2 * r) (z - y) * Polymer.sigmaSq β *
          (∫ ω, pointToPlane β 0 (s - r) 0 ω ^ 2 ∂disorderLaw)) =
      ∑ r ∈ Finset.Icc 1 s,
        srwKernel (2 * (d + r)) 0 * Polymer.sigmaSq β *
          (∫ ω, pointToPlane β 0 (s - r) 0 ω ^ 2 ∂disorderLaw) := by
    apply Finset.sum_congr rfl
    intro r hr
    let c := Polymer.sigmaSq β *
      (∫ ω, pointToPlane β 0 (s - r) 0 ω ^ 2 ∂disorderLaw)
    calc
      (∑ y ∈ A, ∑ z ∈ A,
          ν y * ν z * srwKernel (2 * r) (z - y) * Polymer.sigmaSq β *
            (∫ ω, pointToPlane β 0 (s - r) 0 ω ^ 2 ∂disorderLaw))
          = ∑ y ∈ A, (∑ z ∈ A,
              ν y * ν z * srwKernel (2 * r) (z - y)) * c := by
                apply Finset.sum_congr rfl
                intro y hy
                calc
                  (∑ z ∈ A,
                      ν y * ν z * srwKernel (2 * r) (z - y) * Polymer.sigmaSq β *
                        (∫ ω, pointToPlane β 0 (s - r) 0 ω ^ 2 ∂disorderLaw))
                      = ∑ z ∈ A,
                          ν y * ν z * srwKernel (2 * r) (z - y) * c := by
                            apply Finset.sum_congr rfl
                            intro z hz
                            dsimp [c]
                            ring
                  _ = (∑ z ∈ A,
                        ν y * ν z * srwKernel (2 * r) (z - y)) * c := by
                          rw [Finset.sum_mul]
      _ = (∑ y ∈ A, ∑ z ∈ A,
              ν y * ν z * srwKernel (2 * r) (z - y)) * c := by
                rw [← Finset.sum_mul]
      _ = srwKernel (2 * (d + r)) 0 * Polymer.sigmaSq β *
            (∫ ω, pointToPlane β 0 (s - r) 0 ω ^ 2 ∂disorderLaw) := by
              rw [hkernel]
              dsimp [c]
              ring
  refine ⟨hcollisionInt, hprofileInt, ?_⟩
  have hformula :
      (∫ ω, profileP2Fun β 0 s ν (fun _ => 1) ω *
        profileP2Fun β 0 s ν (fun _ => 1) ω ∂disorderLaw) - 1 =
      ∑ r ∈ Finset.Icc 1 s, ∑ y ∈ A, ∑ z ∈ A,
        ν y * ν z * srwKernel (2 * r) (z - y) * Polymer.sigmaSq β *
          (∫ ω, pointToPlane β 0 (s - r) 0 ω ^ 2 ∂disorderLaw) := by
    simpa only [Nat.zero_add] using hfc
  calc
    (∫ ω, profileP2Fun β 0 s ν (fun _ => 1) ω ^ 2 ∂disorderLaw) - 1
        = ∑ r ∈ Finset.Icc 1 s, ∑ y ∈ A, ∑ z ∈ A,
            ν y * ν z * srwKernel (2 * r) (z - y) * Polymer.sigmaSq β *
              (∫ ω, pointToPlane β 0 (s - r) 0 ω ^ 2 ∂disorderLaw) := by
                simpa only [pow_two] using hformula
    _ = ∑ r ∈ Finset.Icc 1 s,
          srwKernel (2 * (d + r)) 0 * Polymer.sigmaSq β *
            (∫ ω, pointToPlane β 0 (s - r) 0 ω ^ 2 ∂disorderLaw) := hcollect

/-- The same collision identity after centering the diffuse short-clock mass at its mean one.
The displayed integrability conjunct makes this a genuine variance formula. -/
theorem integrable_walkKernel_shortProfile_centered_sq_eq_firstCollision (β : ℝ)
    (d s : ℕ) (x : Site) :
    Integrable (fun ω =>
      (profileP2Fun β 0 s (fun y => srwKernel d (y - x)) (fun _ => 1) ω - 1) ^ 2)
      disorderLaw ∧
    (∫ ω,
      (profileP2Fun β 0 s (fun y => srwKernel d (y - x)) (fun _ => 1) ω - 1) ^ 2
        ∂disorderLaw) =
      ∑ r ∈ Finset.Icc 1 s,
        srwKernel (2 * (d + r)) 0 * Polymer.sigmaSq β *
          (∫ ω, pointToPlane β 0 (s - r) 0 ω ^ 2 ∂disorderLaw) := by
  classical
  let A := Polymer.endpoints x d
  let ν : Site → ℝ := fun y => srwKernel d (y - x)
  have hνA : ∀ y ∉ A, ν y = 0 := by
    intro y hy
    exact Polymer.srwKernel_eq_zero_of_not_mem d x y (by simpa [A] using hy)
  have hZmem : MemLp (fun ω => profileP2Fun β 0 s ν (fun _ => 1) ω)
      2 disorderLaw :=
    Polymer.memLp_profileP2Fun_finset β 0 s ν (fun _ => 1) A hνA 2 (by norm_num)
  let Z : Disorder → ℝ := fun ω => profileP2Fun β 0 s ν (fun _ => 1) ω
  have hZint : Integrable Z disorderLaw := by
    exact hZmem.integrable (by norm_num)
  have hZsq : Integrable (fun ω => Z ω ^ 2) disorderLaw := by
    have h := hZmem.integrable_norm_pow'
    simpa only [Real.norm_eq_abs, sq_abs] using h
  have hνsum : ∑ y ∈ A, ν y = 1 := by
    exact Polymer.sum_srwKernel_endpoints d x
  have hZmean : (∫ ω, Z ω ∂disorderLaw) = 1 := by
    calc
      _ = ∑ y ∈ A, ν y * (∑' z, srwKernel s (z - y)) := by
        change (∫ ω, profileP2Fun β 0 s ν (fun _ => 1) ω ∂disorderLaw) = _
        rw [Polymer.integral_profileP2Fun_finset β 0 s ν (fun _ => 1) A hνA]
        simp only [mul_one, Nat.sub_zero]
      _ = ∑ y ∈ A, ν y := by simp [Polymer.tsum_srwKernel]
      _ = 1 := hνsum
  have hpolyInt : Integrable (fun ω => Z ω ^ 2 - 2 * Z ω + 1) disorderLaw := by
    exact (hZsq.sub (hZint.const_mul 2)).add (integrable_const (1 : ℝ))
  have hcenterInt : Integrable (fun ω => (Z ω - 1) ^ 2) disorderLaw := by
    apply hpolyInt.congr
    filter_upwards [] with ω
    ring
  have hpolyMean :
      (∫ ω, Z ω ^ 2 - 2 * Z ω + 1 ∂disorderLaw) =
        (∫ ω, Z ω ^ 2 ∂disorderLaw) - 1 := by
    calc
      _ = (∫ ω, Z ω ^ 2 - 2 * Z ω ∂disorderLaw) +
            ∫ ω, (1 : ℝ) ∂disorderLaw :=
          integral_add (hZsq.sub (hZint.const_mul 2)) (integrable_const (1 : ℝ))
      _ = ((∫ ω, Z ω ^ 2 ∂disorderLaw) -
            ∫ ω, 2 * Z ω ∂disorderLaw) + 1 := by
          rw [integral_sub hZsq (hZint.const_mul 2)]
          simp [MeasureTheory.integral_const]
      _ = _ := by rw [integral_const_mul, hZmean]; ring
  have hcenterMoment :
      (∫ ω, (Z ω - 1) ^ 2 ∂disorderLaw) =
        (∫ ω, Z ω ^ 2 ∂disorderLaw) - 1 := by
    calc
      _ = ∫ ω, Z ω ^ 2 - 2 * Z ω + 1 ∂disorderLaw := by
        apply integral_congr_ae
        filter_upwards [] with ω
        ring
      _ = _ := hpolyMean
  have hraw := integrable_walkKernel_shortProfile_sq_eq_firstCollision β d s x
  refine ⟨?_, ?_⟩
  · have hfun : (fun ω =>
        (profileP2Fun β 0 s ν (fun _ => 1) ω - 1) ^ 2) =
        fun ω => (Z ω - 1) ^ 2 := by funext ω; rfl
    rw [hfun]
    exact hcenterInt
  · rw [show (fun ω =>
        (profileP2Fun β 0 s ν (fun _ => 1) ω - 1) ^ 2) =
        fun ω => (Z ω - 1) ^ 2 by funext ω; rfl, hcenterMoment]
    have hprofileFormula := hraw.2.2
    have hZformula :
        (∫ ω, Z ω ^ 2 ∂disorderLaw) - 1 =
          ∑ r ∈ Finset.Icc 1 s,
            srwKernel (2 * (d + r)) 0 * Polymer.sigmaSq β *
              (∫ ω, pointToPlane β 0 (s - r) 0 ω ^ 2 ∂disorderLaw) := by
      simpa [Z, ν] using hprofileFormula
    exact hZformula

end Critical2DKPZ.Smoothing

end
