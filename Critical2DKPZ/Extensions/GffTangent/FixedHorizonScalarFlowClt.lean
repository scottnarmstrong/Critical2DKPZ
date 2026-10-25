/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonRescaledClt
public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonSlowTransfer
public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonTransfer
import Mathlib.Tactic

/-! # Transfer of the scalar CCR limit to every critical SHF -/

@[expose] public noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators NNReal BoundedContinuousFunction

namespace Critical2DKPZ.Extensions.GffTangent

/-- The scalar flat-terminal lattice pairing converges to its flow pairing
at each fixed parameter, with any fixed scalar normalization. -/
theorem flat_pairing_scalar_lattice_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ϑ : ℝ) (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {T : ℝ} (hT : 0 < T) (f : TestFn) (c : ℝ) :
    TendstoInDistribution (fun N ω => c * ∫ x, f x * rescaledP2Plane ϑ N 0 T x ω) atTop
      (fun ω => c * shfPairing Z 0 T f (fun _ => 1) ω) (fun _ => disorderLaw) P := by
  have h := (flat_pairing_vector_lattice_tendsto P ϑ Z hZ hT (fun _ : Fin 1 => f) c).continuous_comp
    (g := fun v : EuclideanSpace ℝ (Fin 1) => v 0) (by fun_prop)
  simpa only [Function.comp_def, PiLp.toLp_apply] using h

/-- The fixed-horizon scalar Gaussian limit for the critical SHF. The
lattice-to-flow transfer uses the defining fixed-parameter convergence and
slow full-scale quasi-critical limits, with no uniform-in-parameter assumption. -/
theorem tendstoInDistribution_sqrt_shfPairing_scalar_fixedHorizon
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : ∀ l, IsCriticalSHF (-l) P (Z l))
    {T : ℝ} (hT : 0 < T) (f : TestFn) (hf : (∫ x : Plane, f x) = 0) :
    TendstoInDistribution (fun l ω => Real.sqrt l * shfPairing (Z l) 0 T f (fun _ => 1) ω)
      atTop id (fun _ => P) (gaussianReal 0 (Real.toNNReal
        (4 * Real.pi * ∫ t in Ioo 0 T, ∫ p : Plane × Plane,
          f p.1 * f p.2 * heatKernel (2 * t) (p.2 - p.1) ∂(volume.prod volume)))) := by
  let X : ℝ → Ω → ℝ := fun l ω => Real.sqrt l * shfPairing (Z l) 0 T f (fun _ => 1) ω
  let ν := gaussianReal 0 (Real.toNNReal
    (4 * Real.pi * ∫ t in Ioo 0 T, ∫ p : Plane × Plane,
      f p.1 * f p.2 * heatKernel (2 * t) (p.2 - p.1) ∂(volume.prod volume)))
  have hfixed (l : ℝ) := flat_pairing_scalar_lattice_tendsto P (-l) (Z l) (hZ l) hT f (Real.sqrt l)
  have hX (l : ℝ) : AEMeasurable (X l) P := (hfixed l).aemeasurable_limit
  apply (tendstoInDistribution_iff_forall_seq hX
    (measurable_id.aemeasurable : AEMeasurable id ν)).mpr
  intro l hl
  apply (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    (fun k => hX (l k)) (measurable_id.aemeasurable : AEMeasurable id ν)).mpr
  intro h
  let A : ℕ → ℕ → ℝ := fun k N => ∫ ω, h (Real.sqrt (l k) *
    ∫ x, f x * rescaledP2Plane (-l k) N 0 T x ω) ∂disorderLaw
  let B : ℕ → ℝ := fun k => ∫ ω, h (X (l k) ω) ∂P
  have hA (k : ℕ) : Tendsto (A k) atTop (𝓝 (B k)) :=
    (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
      (hfixed (l k)).forall_aemeasurable (hfixed (l k)).aemeasurable_limit).mp (hfixed (l k)) h
  apply tendsto_of_slow_quasiCritical_limits l B A hA (∫ y, h y ∂ν)
  intro q hq hratio
  have hc := tendstoInDistribution_sqrt_rescaledP2Plane (fun N => l (q N))
    (hl.comp hq) hratio hT f hf
  exact (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    hc.forall_aemeasurable hc.aemeasurable_limit).mp hc h

end Critical2DKPZ.Extensions.GffTangent
