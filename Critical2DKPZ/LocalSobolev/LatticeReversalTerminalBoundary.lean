/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.WalkKernel
public import Critical2DKPZ.Polymer.ChapmanKolmogorov
public import Critical2DKPZ.Smoothing.EndpointDistribution
public import Critical2DKPZ.LocalSobolev.RandomBoundaryTerminalStep
import Mathlib.Tactic

/-! # Weighted masses after removing the terminal Gaussian slice -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.LocalSobolev

/-- Factoring a point-started profile at its penultimate time expresses the zero-noise terminal
step using the normalized endpoint law of the preceding polymer. -/
theorem pointToPlane_mul_zeroLastProfile (β : ℝ) (n : ℕ) (x : Site)
    (f : Site → ℝ) (ω : Disorder) :
    pointToPlane β 0 n x ω *
        profileP2Fun 0 n (n + 1) (endpointDist β n x ω) f ω =
      ∑' y : Site, pointToPoint β 0 n x y ω *
        (∑' z : Site, pointToPoint 0 n 1 y z ω * f z) := by
  classical
  let A := Polymer.endpoints x n
  let η : Site → ℝ := endpointDist β n x ω
  let M : ℝ := pointToPlane β 0 n x ω
  have hM : 0 < M := Polymer.pointToPlane_pos β 0 n x ω
  have hηA : ∀ y ∉ A, η y = 0 := by
    intro y hy
    exact Polymer.endpointDist_eq_zero_of_not_mem β n x y ω (by simpa [A] using hy)
  have hprofile := Polymer.profileP2Fun_eq_sum 0 n (n + 1) η f A hηA ω
  calc
    _ = M * ∑ y ∈ A, η y * (∑' z : Site,
          pointToPoint 0 n 1 y z ω * f z) := by
            simpa only [M, η, Nat.add_sub_cancel_left] using congrArg (fun q : ℝ => M * q) hprofile
    _ = ∑ y ∈ A, (M * η y) * (∑' z : Site,
          pointToPoint 0 n 1 y z ω * f z) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro y hy
            ring
    _ = ∑ y ∈ A, pointToPoint β 0 n x y ω * (∑' z : Site,
          pointToPoint 0 n 1 y z ω * f z) := by
            apply Finset.sum_congr rfl
            intro y hy
            dsimp [M, η, endpointDist]
            rw [div_eq_mul_inv]
            calc
              _ = (pointToPlane β 0 n x ω *
                    (pointToPlane β 0 n x ω)⁻¹) *
                    (pointToPoint β 0 n x y ω *
                      (∑' z : Site, pointToPoint 0 n 1 y z ω * f z)) := by ring
              _ = _ := by
                rw [mul_inv_cancel₀ (Polymer.pointToPlane_pos β 0 n x ω).ne']
                rw [one_mul]
    _ = _ := by
          symm
          apply tsum_eq_sum
          intro y hy
          have hy' : y ∉ Polymer.endpoints x n := by simpa [A] using hy
          rw [Polymer.pointToPoint_eq_zero_of_not_mem β 0 n x y ω hy', zero_mul]

/-- The random endpoint law of a point-started polymer satisfies the one-slice terminal estimate
for every positive deterministic terminal profile. -/
theorem integral_sq_log_endpointDist_terminal_ratio_le (β : ℝ) (n : ℕ)
    (x : Site) (f : Site → ℝ) (hf : ∀ z, 0 < f z) :
    Integrable (fun ω =>
      (Real.log (profileP2Fun β n (n + 1) (endpointDist β n x ω) f ω) -
        Real.log (profileP2Fun 0 n (n + 1) (endpointDist β n x ω) f ω)) ^ 2)
        disorderLaw ∧
    (∫ ω,
      (Real.log (profileP2Fun β n (n + 1) (endpointDist β n x ω) f ω) -
        Real.log (profileP2Fun 0 n (n + 1) (endpointDist β n x ω) f ω)) ^ 2
        ∂disorderLaw) ≤ β ^ 2 + β ^ 4 / 4 := by
  let A := Polymer.endpoints x n
  let η : Disorder → Site → ℝ := endpointDist β n x
  have hsupp : ∀ ω z, z ∉ A → η ω z = 0 := by
    intro ω z hz
    exact Polymer.endpointDist_eq_zero_of_not_mem β n x z ω (by simpa [A] using hz)
  have hη0 : ∀ ω z, 0 ≤ η ω z := by
    intro ω z
    exact Polymer.endpointDist_nonneg β n x z ω
  have hη1 : ∀ ω, ∑ z ∈ A, η ω z = 1 := by
    intro ω
    exact (Smoothing.endpointDist_probability β n x ω).2.2
  have hηmeas : ∀ z, Measurable[disorderPast n] (η · z) := by
    intro z
    exact Polymer.measurable_endpointDist_past β n x z
  exact integral_sq_log_profileP2Fun_random_past_terminal_ratio_le β n A η f
    hsupp hη0 hη1 hηmeas hf

/-- Multiplying the final endpoint by its inverse Gaussian weight removes that slice's random
factor and leaves its deterministic simple-walk transition and Gaussian normalization. -/
theorem oneStepPointToPoint_remove_terminalSlice (β : ℝ) (n : ℕ) (x : Site)
    (f : Site → ℝ) (ω : Disorder) :
    (∑' z : Site, pointToPoint β n 1 x z ω *
      (f z * Real.exp (-β * ω (n + 1, z)))) =
      Real.exp (-(β ^ 2) / 2) *
        ∑' z : Site, pointToPoint 0 n 1 x z ω * f z := by
  have hβ := Polymer.terminalProfile_succ β n 0 x
    (fun z => f z * Real.exp (-β * ω (n + 1, z))) ω
  have hβ' :
      (∑' z : Site, pointToPoint β n 1 x z ω *
        (f z * Real.exp (-β * ω (n + 1, z)))) =
        ∑ i : Fin 4, (4 : ℝ)⁻¹ *
          (Real.exp (β * ω (n + 1, x + srwStep i) - β ^ 2 / 2) *
            (f (x + srwStep i) *
              Real.exp (-β * ω (n + 1, x + srwStep i)))) := by
    simpa only [Nat.zero_add, Polymer.pointToPoint_zero, ite_mul, one_mul, zero_mul,
      tsum_ite_eq, tsum_ite_eq', mul_assoc] using hβ
  have h0 := Polymer.terminalProfile_succ 0 n 0 x f ω
  have h0' :
      (∑' z : Site, pointToPoint 0 n 1 x z ω * f z) =
        ∑ i : Fin 4, (4 : ℝ)⁻¹ * f (x + srwStep i) := by
    simpa [Nat.zero_add, Polymer.pointToPoint_zero, ite_mul, one_mul, zero_mul,
      tsum_ite_eq, tsum_ite_eq', mul_assoc] using h0
  rw [hβ', h0']
  calc
    _ = ∑ i : Fin 4, (4 : ℝ)⁻¹ *
        (Real.exp (-(β ^ 2) / 2) * f (x + srwStep i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          have he : Real.exp (β * ω (n + 1, x + srwStep i) - β ^ 2 / 2) *
              Real.exp (-β * ω (n + 1, x + srwStep i)) =
                Real.exp (-(β ^ 2) / 2) := by
            rw [← Real.exp_add]
            congr 1
            ring
          congr 1
          calc
            _ = (Real.exp (β * ω (n + 1, x + srwStep i) - β ^ 2 / 2) *
                Real.exp (-β * ω (n + 1, x + srwStep i))) *
                f (x + srwStep i) := by ring
            _ = _ := by rw [he]
    _ = Real.exp (-(β ^ 2) / 2) *
        ∑ i : Fin 4, (4 : ℝ)⁻¹ * f (x + srwStep i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring

/-- The same terminal-slice cancellation after any finite first portion of a polymer. -/
theorem tsum_weightedPointToPoint_remove_terminalSlice (β : ℝ) (n : ℕ) (x : Site)
    (f : Site → ℝ) (ω : Disorder) :
    (∑' z : Site, pointToPoint β 0 (n + 1) x z ω *
      (f z * Real.exp (-β * ω (n + 1, z)))) =
      Real.exp (-(β ^ 2) / 2) *
        ∑' y : Site, pointToPoint β 0 n x y ω *
          (∑' z : Site, pointToPoint 0 n 1 y z ω * f z) := by
  have hck := Polymer.terminalProfile_chapmanKolmogorov β 0 n 1 x
    (fun z => f z * Real.exp (-β * ω (n + 1, z))) ω
  rw [show 0 + n = n by omega] at hck
  rw [hck]
  calc
    _ = ∑' y : Site, Real.exp (-(β ^ 2) / 2) *
        (pointToPoint β 0 n x y ω *
          (∑' z : Site, pointToPoint 0 n 1 y z ω * f z)) := by
            apply tsum_congr
            intro y
            conv_lhs =>
              rw [oneStepPointToPoint_remove_terminalSlice β n y f ω]
            ring
    _ = _ := by rw [← tsum_mul_left]

/-- The terminal-slice-cancelled point-started mass equals the endpoint-profile with that final
Gaussian coefficient set to zero, times the preceding point-to-plane mass. -/
theorem tsum_weightedPointToPoint_remove_terminalSlice_eq_profile (β : ℝ) (n : ℕ)
    (x : Site) (f : Site → ℝ) (ω : Disorder) :
    (∑' z : Site, pointToPoint β 0 (n + 1) x z ω *
      (f z * Real.exp (-β * ω (n + 1, z)))) =
      Real.exp (-(β ^ 2) / 2) *
        (pointToPlane β 0 n x ω *
          profileP2Fun 0 n (n + 1) (endpointDist β n x ω) f ω) := by
  rw [tsum_weightedPointToPoint_remove_terminalSlice β n x f ω,
    ← pointToPlane_mul_zeroLastProfile β n x f ω]

end Critical2DKPZ.LocalSobolev

end
