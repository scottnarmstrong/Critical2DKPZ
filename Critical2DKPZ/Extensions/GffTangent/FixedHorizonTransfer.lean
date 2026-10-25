/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.ConvergenceTools
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Critical2DKPZ.Extensions.GffTangent.LinearCovariance

/-! # Fixed-parameter lattice-to-flow test convergence -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology CompactlySupported BoundedContinuousFunction

namespace Critical2DKPZ.Extensions.GffTangent

/-- The defining SHF convergence includes the actual flat-terminal vector,
with any fixed deterministic normalization. -/
theorem flat_pairing_vector_lattice_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ϑ : ℝ) (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {T : ℝ} (hT : 0 < T) {k : ℕ} (f : Fin k → TestFn) (c : ℝ) :
    TendstoInDistribution
      (fun (N : ℕ) (ω : Disorder) => WithLp.toLp 2
        (fun i => c * ∫ x, f i x * rescaledP2Plane ϑ N 0 T x ω)) atTop
      (fun ω => WithLp.toLp 2 (fun i => c * shfPairing Z 0 T (f i) (fun _ => 1) ω))
      (fun _ => disorderLaw) P := by
  let ψ : Fin k → C_c(Plane, ℝ) := fun i => ⟨⟨f i, (f i).continuous⟩, (f i).hasCompactSupport⟩
  have hψ (i : Fin k) : ((ψ i) : Plane → ℝ) = (f i : Plane → ℝ) := by
    simp only [ψ, CompactlySupportedContinuousMap.coe_mk, ContinuousMap.coe_mk]
  have hj := hZ.2.2 k (fun _ => 0) (fun _ => T) (fun _ => ⟨le_refl 0, hT⟩)
    (fun _ => 0) ψ
  have hv := hj.continuous_comp
    (g := fun v : Fin k → ℝ × ℝ => WithLp.toLp 2 (fun i => c * (v i).2)) (by fun_prop)
  have he (ω : Ω) (i : Fin k) :
      (∫ x, f i x ∂((Z 0 T ω).map Prod.fst)) = shfPairing Z 0 T (f i) (fun _ => 1) ω := by
    have hm : Measurable (fun x : Plane => f i x) := (f i).continuous.measurable
    rw [integral_map measurable_fst.aemeasurable hm.aestronglyMeasurable]
    simp only [shfPairing, mul_one]
  simpa only [Function.comp_def, hψ, he] using hv


end Critical2DKPZ.Extensions.GffTangent
