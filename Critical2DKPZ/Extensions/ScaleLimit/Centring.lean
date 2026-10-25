/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.Common.Moments
import Critical2DKPZ.CovarianceKernel.RegularizedSpecification
import Critical2DKPZ.Assembly.Final
import Critical2DKPZ.Assembly.RootInputs
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Centring of the flat critical KPZ field

Translation invariance gives mean zero at each regularized point. Fubini gives
mean zero for the tested regularizations, and their L¹ convergence gives mean
zero for every associated critical KPZ field.
-/

public section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal Topology BoundedContinuousFunction

namespace Critical2DKPZ.Extensions.ScaleLimit

variable (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P]
  (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)

include hZ

/-- The pointwise flat regularized field is centred at every spatial point. -/
theorem integral_kpzRegularized_eq_zero {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t)
    (x : Plane) : (∫ ω, kpzRegularized P Z t δ 0 x ω ∂P) = 0 := by
  have hsym := Assembly.shfSymmetriesAt ϑ P Z hZ
  have hrev := Assembly.shfReversalLawAt_of_isCriticalSHF ϑ P Z hZ
  have hlog := CovarianceKernel.swappedHeatStartLog_memLp_two_of
    ϑ P Z hZ hsym hrev hδ hδt 0
  have hzero : (∫ ω, kpzRegularized P Z t δ 0 0 ω ∂P) = 0 := by
    rw [CovarianceKernel.kpzRegularized_eq_swappedHeatStartLog_sub_mean P Z 0]
    rw [integral_sub (hlog.integrable (by norm_num)) (integrable_const _)]
    simp only [integral_const, probReal_univ, one_smul, sub_self]
  have hid := CovarianceKernel.kpzRegularized_identDistrib_translate_of
    ϑ P Z hZ hsym hδ hδt x x
  have hid0 : IdentDistrib (kpzRegularized P Z t δ 0 x)
      (kpzRegularized P Z t δ 0 0) P P := by
    simpa only [sub_self] using hid
  exact hid0.integral_eq.trans hzero

/-- The flat regularized field tested against a compact smooth function is centred. -/
theorem integral_test_kpzRegularized_eq_zero {t δ : ℝ}
    (hδ : 0 < δ) (hδt : δ < t) (f : TestFn) :
    (∫ ω, (∫ x, f x * kpzRegularized P Z t δ 0 x ω) ∂P) = 0 := by
  have hsym := Assembly.shfSymmetriesAt ϑ P Z hZ
  have hrev := Assembly.shfReversalLawAt_of_isCriticalSHF ϑ P Z hZ
  obtain ⟨B, hB, hm⟩ := CovarianceKernel.kpzRegularized_uniform_second_moment_of
    ϑ P Z hZ hsym hrev hδ hδt
  have hj := CovarianceKernel.kpzRegularized_joint_aestronglyMeasurable_of
    ϑ P Z hZ hδ hδt
  have hswap := hj.comp_measurePreserving (Measure.measurePreserving_swap (μ := (volume : Measure Plane)) (ν := P))
  have hj' : AEStronglyMeasurable
      (fun p : Plane × Ω => kpzRegularized P Z t δ 0 p.1 p.2) (volume.prod P) :=
    by simpa only [Function.comp_def, Prod.swap] using hswap
  have hint : Integrable (fun q : Plane × Ω =>
      f q.1 * kpzRegularized P Z t δ 0 q.1 q.2) (volume.prod P) :=
    JointConvergence.integrable_test_mul_joint P
    (F := fun q : Plane × Ω => kpzRegularized P Z t δ 0 q.1 q.2) hj'.aemeasurable
    (fun x => (hm x).1.aestronglyMeasurable) hB
    (fun x => by simpa only [sq_abs] using ⟨(hm x).2.1, (hm x).2.2.le⟩) f
  rw [← integral_integral_swap hint]
  simp_rw [integral_const_mul, integral_kpzRegularized_eq_zero ϑ P Z hZ hδ hδt,
    mul_zero]
  exact integral_zero _ _

variable (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
  (t : ℝ) (ht : 0 < t)

include hH ht

/-- Every flat tested KPZ field is square-integrable, including arbitrary versions. -/
theorem memLp_kpz_two (f : TestFn) : MemLp (fun ω => H t 0 ω f) 2 P :=
  Common.memLp_criticalKPZ_pairing ϑ P Z hZ H hH t ht 0 f 2
    (by norm_num) (by norm_num)

/-- All flat tested KPZ fields have expectation zero. -/
theorem integral_kpz_eq_zero (f : TestFn) : (∫ ω, H t 0 ω f ∂P) = 0 := by
  have hconv := Common.tendsto_eLpNorm_kpzRegularized_isCriticalKPZ
    ϑ P Z hZ H hH t ht 0 f 1 le_rfl (by simp)
  have hsmall : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), δ < t :=
    (eventually_lt_nhds ht).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < δ := self_mem_nhdsWithin
  have hint : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0),
      Integrable (fun ω => ∫ x, f x * kpzRegularized P Z t δ 0 x ω) P := by
    filter_upwards [hpos, hsmall] with δ hδ hδt
    exact (Common.memLp_kpzRegularized_pairing ϑ P Z hZ t δ ht hδ hδt
      0 f 1 le_rfl (by simp)).integrable le_rfl
  have hi := tendsto_integral_of_L1' (fun ω => H t 0 ω f) hint hconv
  have hz : (fun δ => ∫ ω, (∫ x, f x * kpzRegularized P Z t δ 0 x ω) ∂P)
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)] fun _ => 0 := by
    filter_upwards [hpos, hsmall] with δ hδ hδt
    exact integral_test_kpzRegularized_eq_zero ϑ P Z hZ hδ hδt f
  exact tendsto_nhds_unique (hi.congr' hz) tendsto_const_nhds

/-- Centred second moments agree with covariances. -/
theorem integral_mul_kpz_eq_covariance (f g : TestFn) :
    (∫ ω, H t 0 ω f * H t 0 ω g ∂P) =
      cov[fun ω => H t 0 ω f, fun ω => H t 0 ω g; P] := by
  rw [covariance_eq_sub (memLp_kpz_two ϑ P Z hZ H hH t ht f)
    (memLp_kpz_two ϑ P Z hZ H hH t ht g),
    integral_kpz_eq_zero ϑ P Z hZ H hH t ht f, zero_mul, sub_zero]
  rfl

end Critical2DKPZ.Extensions.ScaleLimit
