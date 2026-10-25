/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonParameters
public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonProjections

/-! # Fixed-horizon quasi-critical central limit theorem

The moving-parameter and scalar renewal facts are provided by a separate
leaf module so that the moment estimates and final assembly have acyclic imports.
-/

@[expose] public noncomputable section


open Filter MeasureTheory ProbabilityTheory Set Matrix
open scoped Topology BigOperators NNReal

namespace Critical2DKPZ.Extensions.GffTangent

/-- CCR25's fixed-horizon Gaussian limit for a finite family of flat-terminal
critical SHF pairings, in the note's 4*pi covariance normalization. -/
theorem tendstoInDistribution_sqrt_shfPairing_fixedHorizon
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : ∀ l, IsCriticalSHF (-l) P (Z l))
    {n : ℕ} (f : Fin n → TestFn) (hfzero : ∀ i, (∫ x : Plane, f i x) = 0)
    {T : ℝ} (hT : 0 < T) :
    TendstoInDistribution
      (fun l ω => WithLp.toLp 2 (fun i : Fin n => Real.sqrt l *
        shfPairing (Z l) 0 T (f i) (fun _ => 1) ω)) atTop id (fun _ => P)
      (multivariateGaussian 0 (Matrix.of fun i j => 4 * Real.pi *
        ∫ s in Ioc (0 : ℝ) T, ∫ x : Plane, f i x * heatSmooth (2 * s) (f j) x)) := by
  classical
  let S : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => 4 * Real.pi *
    ∫ s in Ioc (0 : ℝ) T, ∫ x : Plane, f i x * heatSmooth (2 * s) (f j) x
  have hS : S.PosSemidef := posSemidef_truncatedHeatCovariance f hfzero hT
  let X : ℝ → Ω → EuclideanSpace ℝ (Fin n) := fun l ω =>
    WithLp.toLp 2 (fun i => Real.sqrt l * shfPairing (Z l) 0 T (f i) (fun _ => 1) ω)
  have hX (l : ℝ) : AEMeasurable (X l) P :=
    (flat_pairing_vector_lattice_tendsto P (-l) (Z l) (hZ l) hT f (Real.sqrt l)).aemeasurable_limit
  apply (tendstoInDistribution_iff_inner hX
    (measurable_id.aemeasurable : AEMeasurable id (multivariateGaussian 0 S))).mpr
  intro t
  let g : TestFn := ∑ i, t i • f i
  have hg : (∫ x : Plane, g x) = 0 := integral_testFn_linearCombination_eq_zero f hfzero t
  have hc := tendstoInDistribution_sqrt_shfPairing_scalar_fixedHorizon P Z hZ hT g hg
  have hcov :
      (4 * Real.pi * ∫ s in Ioo (0 : ℝ) T, ∫ p : Plane × Plane,
        g p.1 * g p.2 * heatKernel (2 * s) (p.2 - p.1) ∂(volume.prod volume)) = t ⬝ᵥ S *ᵥ t := by
    rw [integral_fixedHorizon_product_heat_eq g g hT]
    exact (fixedHorizon_covariance_quadratic f hfzero T t).symm
  rw [hcov] at hc
  have hproj (l : ℝ) :
      (fun ω => Real.sqrt l * shfPairing (Z l) 0 T g (fun _ => 1) ω) =ᵐ[P]
        (fun ω => inner ℝ (X l ω) t) := by
    filter_upwards [shfPairing_linearCombination_ae P (-l) (Z l) (hZ l) hT f t] with ω hω
    change Real.sqrt l * shfPairing (Z l) 0 T g (fun _ => 1) ω = _
    rw [hω, Finset.mul_sum]
    simp only [X, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hp := hc.congr hproj (Eventually.of_forall (fun _ => rfl))
  refine ⟨hp.forall_aemeasurable, (by fun_prop), ?_⟩
  simpa only [id_eq, Measure.map_id, map_inner_multivariateGaussian S hS t] using hp.tendsto

end Critical2DKPZ.Extensions.GffTangent
