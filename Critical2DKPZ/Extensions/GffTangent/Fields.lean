/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Provider.ThmToyJoint
import Critical2DKPZ.Extensions.Common.Moments
import Critical2DKPZ.CovarianceKernel.PointwiseMoments
import Critical2DKPZ.Provider.ShfSymmetries
import Mathlib.MeasureTheory.Integral.Prod

/-! # Forward heat-started logarithmic averages and their fixed-horizon limits -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal BoundedContinuousFunction

namespace Critical2DKPZ.Extensions.GffTangent

/-- The logarithmic average of a flow started at the temporal entrance `a`. -/
def lField {Ω : Type*} (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (a T : ℝ) (f : TestFn) (ω : Ω) : ℝ :=
  ∫ x, f x * Real.log
    (shfPairing Z a T (fun y => heatKernel a (y - x)) (fun _ => 1) ω)

variable (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P]
  (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
  (T : ℝ) (hT : 0 < T)

/-- The flat reversed-field limit, chosen simultaneously for all tests at a
positive horizon. The horizon positivity is part of the definition's domain. -/
def kField (f : TestFn) : Ω → ℝ :=
  (Classical.choose (Critical2DKPZ.Provider.thm_toy_joint ϑ P Z hZ T hT)) 0 0 f

/-- Each chosen limit is measurable in the sigma algebra of the same flow. -/
theorem kField_measurable (f : TestFn) :
    Measurable[shfSigma Z] (kField ϑ P Z hZ T hT f) :=
  (Classical.choose_spec (Critical2DKPZ.Provider.thm_toy_joint ϑ P Z hZ T hT)).1
    0 0 f le_rfl hT

/-- Ambient measurability follows from measurability of the flow coordinates. -/
theorem kField_aemeasurable (f : TestFn) :
    AEMeasurable (kField ϑ P Z hZ T hT f) P :=
  ((kField_measurable ϑ P Z hZ T hT f).mono
    (Common.shfSigma_le ϑ P Z hZ) le_rfl).aemeasurable

/-- The chosen limits have the fixed-time joint law of every associated KPZ field. -/
theorem kField_law_eq (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr)
    (hH : IsCriticalKPZ P Z H) (n : ℕ) (f : Fin n → TestFn) :
    P.map (fun ω i => kField ϑ P Z hZ T hT (f i) ω) =
      P.map (fun ω i => H T 0 ω (f i)) := by
  simpa only [kField, sub_zero] using
    (Classical.choose_spec (Critical2DKPZ.Provider.thm_toy_joint ϑ P Z hZ T hT)).2.2.2.2
      H hH n (fun _ => 0) (fun _ => 0) f (fun _ => ⟨le_rfl, hT⟩)

/-- All finite moments of the fixed-horizon limit follow from its KPZ law. -/
theorem kField_memLp (f : TestFn) (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ⊤) :
    MemLp (kField ϑ P Z hZ T hT f) p P := by
  obtain ⟨H, hH, _⟩ := Common.exists_canonical_criticalKPZ ϑ P Z hZ
  have hHmeas : AEMeasurable (fun ω (_ : Fin 1) => H T 0 ω f) P :=
    aemeasurable_pi_iff.mpr fun _ =>
      Common.aemeasurable_pairing_of_isCriticalKPZ ϑ P Z hZ H hH T hT 0 f
  have hKmeas : AEMeasurable (fun ω (_ : Fin 1) => kField ϑ P Z hZ T hT f ω) P :=
    aemeasurable_pi_iff.mpr fun _ => kField_aemeasurable ϑ P Z hZ T hT f
  have hm := Common.memLp_criticalKPZ_pairing ϑ P Z hZ H hH T hT 0 f p hp hp_top
  have hpush : MemLp (fun v : Fin 1 → ℝ => v 0) p
      (P.map (fun ω (_ : Fin 1) => H T 0 ω f)) :=
    (memLp_map_measure_iff (measurable_pi_apply 0).aestronglyMeasurable hHmeas).mpr hm
  rw [← kField_law_eq ϑ P Z hZ T hT H hH 1 (fun _ => f)] at hpush
  exact hpush.comp_of_map hKmeas

/-- The reversed regularizations converge to the chosen limit in every finite Lp. -/
theorem kField_regularized_limit (f : TestFn) (p : ℝ≥0∞)
    (hp : 1 ≤ p) (hp_top : p ≠ ⊤) :
    Tendsto (fun a : ℝ => eLpNorm (fun ω =>
      (∫ x, f x * kpzRegularizedReversed P Z 0 T a 0 x ω) -
        kField ϑ P Z hZ T hT f ω) p P) (𝓝[>] 0) (𝓝 0) :=
  (Classical.choose_spec (Critical2DKPZ.Provider.thm_toy_joint ϑ P Z hZ T hT)).2.2.1
    0 0 f p le_rfl hT hp hp_top

include hZ

/-- Uniform spatial square moments for logarithms at a positive entrance. -/
theorem entrance_log_uniform_square {a : ℝ} (ha : 0 < a) (haT : a < T) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : Plane,
      Integrable (fun ω => |Real.log (shfPairing Z a T
        (fun y => heatKernel a (y - x)) (fun _ => 1) ω)| ^ 2) P ∧
      (∫ ω, |Real.log (shfPairing Z a T
        (fun y => heatKernel a (y - x)) (fun _ => 1) ω)| ^ 2 ∂P) ≤ M := by
  have hh := JointConvergence.shf_heatStartLogField_square_bound ϑ P Z hZ
    (fun hs hst hδ x g => SHF.Positivity.isCriticalSHF_heat_bounded_pairing
      ϑ P Z hZ hs hst hδ x g)
    (fun k s t δ x g h => SHF.Positivity.isCriticalSHF_heat_bounded_pairing_joint
      ϑ P Z hZ k s t δ x g h)
    (fun s t δ x h₀ hs hst hδ =>
      let h := SHF.Positivity.isCriticalSHF_heat_pairing_pos_isEhrhardType
        ϑ P Z hZ s t δ x h₀ hs hst hδ
      ⟨h.1, h.2.1⟩) T 0 ha.le haT ha
  simpa only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero] using hh

/-- The integrand defining the entrance average is integrable jointly in space and randomness. -/
theorem lField_integrable_joint {a : ℝ} (ha : 0 < a) (haT : a < T) (f : TestFn) :
    Integrable (fun q : Plane × Ω => f q.1 * Real.log
      (shfPairing Z a T (fun y => heatKernel a (y - q.1)) (fun _ => 1) q.2))
      (volume.prod P) := by
  have hj := JointConvergence.aemeasurable_shfLogField_joint
    ϑ P Z hZ a T a ha.le haT ha 0
  have hj' : AEMeasurable (fun q : Plane × Ω => Real.log
      (shfPairing Z a T (fun y => heatKernel a (y - q.1)) (fun _ => 1) q.2))
      (volume.prod P) := by
    simpa only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero] using hj
  obtain ⟨M, hM, hSq⟩ := entrance_log_uniform_square ϑ P Z hZ T ha haT
  apply JointConvergence.integrable_test_mul_joint P hj' ?_ hM hSq f
  intro x
  exact (CovarianceKernel.log_heatStartPairing_memLp_two_of ϑ P Z hZ
    (Critical2DKPZ.Provider.shf_symmetries ϑ P Z hZ) ha.le haT ha x).aestronglyMeasurable

/-- The logarithmic entrance average is integrable. -/
theorem lField_integrable {a : ℝ} (ha : 0 < a) (haT : a < T) (f : TestFn) :
    Integrable (lField Z a T f) P :=
  (lField_integrable_joint ϑ P Z hZ T ha haT f).integral_prod_right

/-- For a zero-mass test, the deterministic centring in the regularization cancels. -/
theorem lField_eq_regularized_ae {a : ℝ} (ha : 0 < a) (haT : a < T)
    (f : TestFn) (hf : (∫ x, f x) = 0) :
    lField Z a T f =ᵐ[P] fun ω => ∫ x, f x * kpzRegularizedReversed P Z 0 T a 0 x ω := by
  filter_upwards [(lField_integrable_joint ϑ P Z hZ T ha haT f).prod_left_ae]
    with ω hω
  simp only [kpzRegularizedReversed, zero_add, BoundedContinuousFunction.coe_zero,
    Pi.zero_apply, Real.exp_zero, mul_sub]
  have hfi : Integrable (fun x : Plane => f x) volume :=
    f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  rw [integral_sub hω (hfi.mul_const _), integral_mul_const, hf, zero_mul, sub_zero]
  rfl

/-- The uncentred entrance average converges in L2 for every zero-mass test. -/
theorem kField_l2_limit (f : TestFn) (hf : (∫ x, f x) = 0) :
    Tendsto (fun a : ℝ => eLpNorm (fun ω => lField Z a T f ω -
      kField ϑ P Z hZ T hT f ω) 2 P) (𝓝[>] 0) (𝓝 0) := by
  apply (kField_regularized_limit ϑ P Z hZ T hT f 2 (by norm_num) (by norm_num)).congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds] with a ha haT
  apply eLpNorm_congr_ae
  filter_upwards [lField_eq_regularized_ae ϑ P Z hZ T ha haT f hf] with ω hω
  rw [hω]

/-- Spatial translation preserves the one-point law of an entrance logarithm. -/
theorem entrance_log_identDistrib {a : ℝ} (ha : 0 < a) (haT : a < T) (x : Plane) :
    IdentDistrib (fun ω => Real.log (shfPairing Z a T
      (fun y => heatKernel a (y - x)) (fun _ => 1) ω))
      (fun ω => Real.log (shfPairing Z a T
        (fun y => heatKernel a y) (fun _ => 1) ω)) P P := by
  let τ : Plane × Plane → Plane × Plane := fun p => (p.1 + x, p.2 + x)
  let Zx : ℝ → ℝ → Ω → Measure (Plane × Plane) := fun s t ω => (Z s t ω).map τ
  have hτ : Measurable τ := by dsimp [τ]; fun_prop
  have hZx : IsCriticalSHF ϑ P Zx :=
    (Critical2DKPZ.Provider.shf_symmetries ϑ P Z hZ).1 x
  have hm : Measurable (Z a T) := hZ.1 a T ha.le haT
  have hmx : Measurable (Zx a T) := (Measure.measurable_map τ hτ).comp hm
  have hlaw : P.map (Z a T) = P.map (Zx a T) := by
    apply CovarianceKernel.map_singleton_eq_of_map_pi_eq P _ _ hm hmx
    exact SHF.Symmetries.isCriticalSHF_fdd_eq ϑ P P Z Zx hZ hZx 1
      (fun _ => a) (fun _ => T) (fun _ => ⟨ha.le, haT⟩)
  have hid : IdentDistrib (Z a T) (Zx a T) P P :=
    ⟨hm.aemeasurable, hmx.aemeasurable, hlaw⟩
  let Q : Measure (Plane × Plane) → ℝ :=
    fun μ => Real.log (∫ p, heatKernel a (p.1 - x) ∂μ)
  have hQ : Measurable Q := CovarianceKernel.measurable_log_heatPairingMeasure a ha x
  have hcomp := hid.comp hQ
  have heq (ω : Ω) : Q (Zx a T ω) =
      Real.log (shfPairing Z a T (fun y => heatKernel a y) (fun _ => 1) ω) := by
    dsimp [Q, Zx]
    have hfunc : Measurable (fun p : Plane × Plane => heatKernel a (p.1 - x)) :=
      (measurable_heatKernel a).comp (measurable_fst.sub_const x)
    rw [integral_map (μ := Z a T ω) hτ.aemeasurable hfunc.aestronglyMeasurable]
    simp only [τ, add_sub_cancel_right, shfPairing, mul_one]
  simpa only [Function.comp_def, Q, heq, shfPairing, mul_one] using hcomp

/-- A zero-mass test makes the integrable logarithmic entrance average centred. -/
theorem lField_centred {a : ℝ} (ha : 0 < a) (haT : a < T)
    (f : TestFn) (hf : (∫ x, f x) = 0) :
    (∫ ω, lField Z a T f ω ∂P) = 0 := by
  change (∫ ω, (∫ x, f x * Real.log
    (shfPairing Z a T (fun y => heatKernel a (y - x)) (fun _ => 1) ω)) ∂P) = 0
  rw [← integral_integral_swap (lField_integrable_joint ϑ P Z hZ T ha haT f)]
  simp_rw [integral_const_mul, (entrance_log_identDistrib ϑ P Z hZ T ha haT _).integral_eq]
  rw [integral_mul_const, hf, zero_mul]

end Critical2DKPZ.Extensions.GffTangent
