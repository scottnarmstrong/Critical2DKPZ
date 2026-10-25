/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.L2Perturbation
import Mathlib.Tactic

/-! # Elementary L2 error combinations at positive real scales -/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The difference of two vanishing L2 errors is a vanishing L2 error. -/
theorem integral_sq_sub_tendsto_zero {ι Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {l : Filter ι} {E F : ι → Ω → ℝ}
    (hE : ∀ i, MemLp (E i) 2 P) (hF : ∀ i, MemLp (F i) 2 P)
    (hE2 : Tendsto (fun i => ∫ ω, E i ω ^ 2 ∂P) l (𝓝 0))
    (hF2 : Tendsto (fun i => ∫ ω, F i ω ^ 2 ∂P) l (𝓝 0)) :
    Tendsto (fun i => ∫ ω, (E i ω - F i ω) ^ 2 ∂P) l (𝓝 0) := by
  apply squeeze_zero (fun i => integral_nonneg fun _ => sq_nonneg _)
    (fun i => ?_) (by simpa only [mul_zero, add_zero] using (hE2.const_mul 2).add (hF2.const_mul 2))
  calc
    _ ≤ ∫ ω, 2 * E i ω ^ 2 + 2 * F i ω ^ 2 ∂P := by
      apply integral_mono_ae ((hE i).sub (hF i)).integrable_sq
        (((hE i).integrable_sq.const_mul 2).add ((hF i).integrable_sq.const_mul 2))
      exact Eventually.of_forall fun ω => by
        change (E i ω - F i ω) ^ 2 ≤ 2 * E i ω ^ 2 + 2 * F i ω ^ 2
        nlinarith only [sq_nonneg (E i ω + F i ω)]
    _ = _ := by rw [integral_add ((hE i).integrable_sq.const_mul 2) ((hF i).integrable_sq.const_mul 2),
      integral_const_mul, integral_const_mul]

/-- A fixed square-integrable variable is negligible after division by sqrt L.
The integrability assertion is included, even though the scalar limit alone
would also hold for totalized integrals. -/
theorem normalized_fixed_L2_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Ω → ℝ) (hF : MemLp F 2 P) :
    (∀ L : Set.Ioi (0 : ℝ), MemLp (fun ω => (Real.sqrt (L : ℝ))⁻¹ * F ω) 2 P) ∧
    Tendsto (fun L : Set.Ioi (0 : ℝ) => ∫ ω, ((Real.sqrt (L : ℝ))⁻¹ * F ω) ^ 2 ∂P) atTop (𝓝 0) := by
  refine ⟨fun L => hF.const_mul _, ?_⟩
  have hL : Tendsto (fun L : Set.Ioi (0 : ℝ) => (L : ℝ)) atTop atTop :=
    tendsto_Ioi_atTop.mp tendsto_id
  have hh := (tendsto_inv_atTop_zero.comp hL).mul_const (∫ ω, F ω ^ 2 ∂P)
  have hh' : Tendsto (fun L : Set.Ioi (0 : ℝ) => (L : ℝ)⁻¹ * (∫ ω, F ω ^ 2 ∂P)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, zero_mul] using hh
  apply hh'.congr
  intro L
  simp_rw [mul_pow]
  rw [integral_const_mul, inv_pow, Real.sq_sqrt L.property.le]

end Critical2DKPZ.Extensions.ScaleLimit
