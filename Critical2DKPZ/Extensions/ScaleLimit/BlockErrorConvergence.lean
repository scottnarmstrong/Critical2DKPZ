/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.BlockApproximation
public import Critical2DKPZ.Extensions.ScaleLimit.Grid
import Critical2DKPZ.Extensions.ScaleLimit.UniformTailConvergence
import Mathlib.Tactic

/-! # Negligibility of the normalized block error

The argument works for every diverging index and normalization. In particular
it gives the geometric real-scale approximation and a strictly positive
normalization at all natural indices for the centring lemma.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The normalized block error vanishes along any diverging block index and
any diverging deterministic normalization. -/
theorem block_error_div_tendstoInMeasure {κ : Type*} (l : Filter κ)
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z) :
    ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ → ∀ (n : κ → ℕ) (a : κ → ℝ),
      Tendsto n l atTop → Tendsto a l atTop →
      TendstoInMeasure P (fun i ω =>
        (Fheat Z (tau ρ (n i)) 0 ω - partialSum Z ρ (n i) ω) / a i) l (fun _ => 0) := by
  obtain ⟨ρ₀, hρ₀, hB⟩ := block_approximation ϑ P Z hZ
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro ρ hρ n a hn ha
  obtain ⟨C, ℓ₀, hC, _hℓ₀, htail⟩ := hB ρ hρ
  exact tendstoInMeasure_div_of_uniform_tail P
    (fun n ω => Fheat Z (tau ρ n) 0 ω - partialSum Z ρ n ω)
    hC ℓ₀ htail l n a hn ha


/-- A positive normalization at every natural index, for the centring lemma. -/
theorem block_oP_log (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z) :
    ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ →
      TendstoInMeasure P (fun n ω =>
        (Fheat Z (tau ρ n) 0 ω - partialSum Z ρ n ω) / Real.sqrt (1 + Real.log n))
        atTop (fun _ => 0) := by
  obtain ⟨ρ₀, hρ₀, hE⟩ := block_error_div_tendstoInMeasure (κ := ℕ) atTop ϑ P Z hZ
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro ρ hρ
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hclock : Tendsto (fun n : ℕ => 1 + Real.log n) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith) hlog
  exact hE ρ hρ id (fun n => Real.sqrt (1 + Real.log n)) tendsto_id
    (Real.tendsto_sqrt_atTop.comp hclock)

end Critical2DKPZ.Extensions.ScaleLimit
