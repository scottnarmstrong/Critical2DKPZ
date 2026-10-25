/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.BlockIndependence
import Critical2DKPZ.SHF.Positivity.HeatPairingEhrhard
import Mathlib.Tactic

/-! # Positivity and logarithmic factorization of geometric flow blocks -/

@[expose] public noncomputable section

open MeasureTheory Filter

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- A strictly ordered multi-block mass is almost surely positive. -/
theorem blockA_pos_ae (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {ρ : ℝ} (hρ : 1 < ρ) {n ℓ : ℕ} (hℓn : ℓ < n) :
    ∀ᵐ ω ∂P, 0 < blockA Z ρ n ℓ ω := by
  have h := (SHF.Positivity.isCriticalSHF_heat_pairing_pos_isEhrhardType ϑ P Z hZ
    (tau ρ n) (tau ρ ℓ) (tau ρ n) 0 0 (tau_pos hρ n).le
    (strictAnti_tau hρ hℓn) (tau_pos hρ n)).1
  simpa only [blockA, sub_zero, BoundedContinuousFunction.coe_zero, Pi.zero_apply,
    Real.exp_zero] using h

/-- The terminal heat-start mass is almost surely positive at every positive index. -/
theorem geometric_fullMass_pos_ae (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {ρ : ℝ} (hρ : 1 < ρ) {n : ℕ} (hn : 0 < n) :
    ∀ᵐ ω ∂P, 0 < shfPairing Z (tau ρ n) 1 (fun y => heatKernel (tau ρ n) y) (fun _ => 1) ω := by
  have h := (SHF.Positivity.isCriticalSHF_heat_pairing_pos_isEhrhardType ϑ P Z hZ
    (tau ρ n) 1 (tau ρ n) 0 0 (tau_pos hρ n).le (tau_lt_one hρ hn) (tau_pos hρ n)).1
  simpa only [sub_zero, BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero] using h

/-- All positive-index individual masses are simultaneously positive. -/
theorem all_blockMass_pos_ae (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {ρ : ℝ} (hρ : 1 < ρ) : ∀ᵐ ω ∂P, ∀ j : ℕ, 0 < j → 0 < blockMass Z ρ j ω := by
  filter_upwards [ae_all_iff.mpr (blockMass_pos_ae ϑ P Z hZ hρ)] with ω hω
  intro j hj
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
  exact hω k


/-- The logarithmic block decomposition holds on the original flow probability space. -/
theorem block_log_decomposition (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {ρ : ℝ} (hρ : 1 < ρ) {n ℓ : ℕ} (hℓn : ℓ < n) :
    ∀ᵐ ω ∂P, Fheat Z (tau ρ n) 0 ω = Real.log (blockQ Z ρ n ℓ ω) +
      Real.log (blockR Z ρ n ℓ ω) + ∑ j ∈ Finset.Ioc ℓ n, Real.log (blockMass Z ρ j ω) := by
  filter_upwards [blockA_pos_ae ϑ P Z hZ hρ hℓn,
    geometric_fullMass_pos_ae ϑ P Z hZ hρ (by omega : 0 < n),
    all_blockMass_pos_ae ϑ P Z hZ hρ] with ω hA hM hZp
  have hp (j : ℕ) (hj : j ∈ Finset.Ioc ℓ n) : 0 < blockMass Z ρ j ω :=
    hZp j (by have := (Finset.mem_Ioc.mp hj).1; omega)
  have hD := Finset.prod_pos hp
  simp only [Fheat, sub_zero, blockQ, blockR]
  rw [Real.log_div hM.ne' hA.ne', Real.log_div hA.ne' hD.ne',
    Real.log_prod (fun j hj => (hp j hj).ne')]
  ring

end Critical2DKPZ.Extensions.ScaleLimit
