/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordContinuity
import Mathlib.Tactic

/-! # Uniform interior renewal-time profiles for the two-particle word -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.SHF.Moments

open MeasureTheory Filter Polymer
open scoped CompactlySupported Topology Uniformity

/-- The tested spatial renewal slice with its time-Riemann normalization. -/
def pairTwoTestedSpatialSlice (ϑ : ℝ) (N r k : ℕ)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (x : Fin 2 → Site) (z : Site) : ℝ :=
  (N : ℝ) ^ 3 * criticalSigmaSq ϑ N *
    ∑ d ∈ endpoints 0 r, Collision.spatialRenewal (criticalSigmaSq ϑ N) r d *
      pairTwoFutureTerminalCellFactor N k φ x (z + d) 0 *
      pairTwoFutureTerminalCellFactor N k φ x (z + d) 1

/-- Sample the renewal duration at a macroscopic time, leaving the rest of the
future horizon for the two terminal walks. -/
def pairTwoTestedSpatialSliceProfile (ϑ : ℝ) (N L : ℕ)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (x : Fin 2 → Site) (z : Site) (u : ℝ) : ℝ :=
  pairTwoTestedSpatialSlice ϑ N (Nat.floor ((N : ℝ) * u))
    (L - Nat.floor ((N : ℝ) * u)) φ x z

/-- Moving positive macroscopic times are preserved by the microscopic floor. -/
theorem tendsto_floor_scaled_moving
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop) (uN : ℕ → ℝ) {u : ℝ}
    (huN : Tendsto uN atTop (𝓝 u)) (hu : 0 < u) :
    Tendsto (fun N : ℕ => (Nat.floor ((M N : ℝ) * uN N) : ℝ) / M N)
      atTop (𝓝 u) := by
  have hfloor := Renewal.tendsto_floor_div_succ hM huN hu
  have hfactor : Tendsto (fun N : ℕ => ((M N + 1 : ℕ) : ℝ) / M N) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).add ((tendsto_const_div_nat 1).comp hM)
    have h' : Tendsto (fun N : ℕ => 1 + 1 / (M N : ℝ)) atTop (𝓝 1) := by
      simpa only [add_zero, Function.comp_apply] using h
    apply h'.congr'
    filter_upwards [hM.eventually (eventually_gt_atTop 0)] with N hN
    have hNr : (M N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    push_cast
    field_simp
  have h := hfloor.mul hfactor
  apply (show Tendsto (fun N : ℕ =>
      ((Nat.floor ((M N : ℝ) * uN N) : ℝ) / ((M N + 1 : ℕ) : ℝ)) *
        (((M N + 1 : ℕ) : ℝ) / M N)) atTop (𝓝 u) by simpa only [mul_one] using h).congr'
  filter_upwards [hM.eventually (eventually_gt_atTop 0)] with N hN
  have hNr : (M N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hsucc : ((M N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp





end Critical2DKPZ.SHF.Moments

end
