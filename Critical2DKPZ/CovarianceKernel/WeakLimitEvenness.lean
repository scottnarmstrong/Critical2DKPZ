/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.CovarianceKernel.RegularizedSpecification
public import Critical2DKPZ.CovarianceKernel.WeakCovarianceLimit

/-! # Evenness of covariance-kernel weak limits -/

@[expose] public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction Topology

namespace Critical2DKPZ.CovarianceKernel

private noncomputable def reflectL2 (f : Lp ℝ 2 (volume : Measure Plane)) :
    Lp ℝ 2 (volume : Measure Plane) :=
  Lp.compMeasurePreserving (fun z : Plane => -z)
    (Measure.measurePreserving_neg (volume : Measure Plane)) f

private theorem inner_reflectL2 (f g : Lp ℝ 2 (volume : Measure Plane)) :
    inner ℝ (reflectL2 f) g = inner ℝ f (reflectL2 g) := by
  let hneg := Measure.measurePreserving_neg (volume : Measure Plane)
  have hleft : inner ℝ (reflectL2 f) g = ∫ z : Plane, f (-z) * g z := by
    change inner ℝ (Lp.compMeasurePreserving (fun z : Plane => -z)
      (Measure.measurePreserving_neg (volume : Measure Plane)) f) g = _
    rw [L2.inner_def]
    simp only [Real.inner_apply]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_compMeasurePreserving f
      (Measure.measurePreserving_neg (volume : Measure Plane))] with z hz
    rw [hz]
    simp only [Function.comp_apply]
  have hright : inner ℝ f (reflectL2 g) = ∫ z : Plane, f z * g (-z) := by
    change inner ℝ f (Lp.compMeasurePreserving (fun z : Plane => -z)
      (Measure.measurePreserving_neg (volume : Measure Plane)) g) = _
    rw [L2.inner_def]
    simp only [Real.inner_apply]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_compMeasurePreserving g
      (Measure.measurePreserving_neg (volume : Measure Plane))] with z hz
    rw [hz]
    simp only [Function.comp_apply]
  have hchange : (∫ z : Plane, f (-z) * g z) = ∫ z : Plane, f z * g (-z) := by
    simpa only [neg_neg] using hneg.integral_comp
      (Homeomorph.neg Plane).measurableEmbedding (fun z : Plane => f z * g (-z))
  exact hleft.trans (hchange.trans hright.symm)

/-- Weak limits preserve evenness when the approximating `L²` functions are even. -/
theorem weakLimitL2_even_of_even_seq
    (s : ℕ → ℕ) (v : Lp ℝ 2 (volume : Measure Plane))
    (F : ℕ → Plane → ℝ)
    (hmem : ∀ n, MemLp (F n) 2 volume)
    (hweak : ∀ g : Lp ℝ 2 (volume : Measure Plane),
      Tendsto (fun n => inner ℝ ((hmem (s n)).toLp (F (s n))) g)
        atTop (𝓝 (inner ℝ v g)))
    (heven : ∀ n z, F n (-z) = F n z) :
    (fun z : Plane => v (-z)) =ᵐ[volume] v := by
  let U : ℕ → Lp ℝ 2 (volume : Measure Plane) := fun n => (hmem (s n)).toLp (F (s n))
  have hUAE (n : ℕ) : ∀ᵐ z : Plane ∂volume, U n z = F (s n) z := by
    dsimp [U]
    exact (hmem (s n)).coeFn_toLp
  have hUeven (n : ℕ) : reflectL2 (U n) = U n := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving (U n)
        (Measure.measurePreserving_neg (volume : Measure Plane)), hUAE n,
      (Measure.measurePreserving_neg (volume : Measure Plane)).quasiMeasurePreserving.ae (hUAE n)]
        with z hcomp hU hUneg
    calc
      reflectL2 (U n) z = U n (-z) := by simpa [reflectL2] using hcomp
      _ = F (s n) (-z) := hUneg
      _ = F (s n) z := heven (s n) z
      _ = U n z := hU.symm
  have hinnerInvariant (g : Lp ℝ 2 (volume : Measure Plane)) :
      inner ℝ v g = inner ℝ v (reflectL2 g) := by
    have hlim₁ := hweak g
    have hlim₂ := hweak (reflectL2 g)
    have hlim₁' : Tendsto (fun n => inner ℝ (U n) (reflectL2 g)) atTop
        (𝓝 (inner ℝ v g)) := by
      apply hlim₁.congr'
      filter_upwards [] with n
      calc
        inner ℝ (U n) g = inner ℝ (reflectL2 (U n)) g := by rw [hUeven n]
        _ = inner ℝ (U n) (reflectL2 g) := inner_reflectL2 (U n) g
    exact tendsto_nhds_unique hlim₁' hlim₂
  have hinnerEq (g : Lp ℝ 2 (volume : Measure Plane)) :
      inner ℝ (reflectL2 v) g = inner ℝ v g := by
    calc
      inner ℝ (reflectL2 v) g = inner ℝ v (reflectL2 g) := inner_reflectL2 v g
      _ = inner ℝ v g := (hinnerInvariant g).symm
  let d : Lp ℝ 2 (volume : Measure Plane) := reflectL2 v - v
  have hself : inner ℝ d d = 0 := by
    have hEq := hinnerEq d
    calc
      inner ℝ d d = inner ℝ (reflectL2 v - v) d := by rfl
      _ = inner ℝ (reflectL2 v) d - inner ℝ v d := by rw [inner_sub_left]
      _ = 0 := by rw [hEq]; ring
  have hnormsq : ‖d‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq]
    exact hself
  have hd0 : d = 0 := by
    apply norm_eq_zero.mp
    nlinarith [sq_nonneg ‖d‖]
  have hreflectEq : reflectL2 v = v := by
    have h := congrArg (fun x : Lp ℝ 2 (volume : Measure Plane) => x + v) hd0
    simpa [d] using h
  filter_upwards [Lp.coeFn_compMeasurePreserving v
      (Measure.measurePreserving_neg (volume : Measure Plane)), Lp.ext_iff.mp hreflectEq]
      with z hz heq
  exact hz.symm.trans heq

/-- The regularized covariance is exactly even by stationarity and the definition of covariance. -/
theorem regCovKernel_even_of_shfSymmetries
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : LocalSobolev.ShfSymmetriesAt ϑ P Z)
    (hrevL : SmallScales.ShfReversalLawAt P Z)
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) (z : Plane) :
    regCovKernel P Z t δ z = regCovKernel P Z t δ (-z) := by
  have hspec := (regCovKernel_spec_of ϑ P Z hZ hsym hrevL hδ hδt).1 0 z
  have hspec' : cov[kpzRegularized P Z t δ 0 0, kpzRegularized P Z t δ 0 z; P] =
      regCovKernel P Z t δ (-z) := by simpa only [zero_sub] using hspec
  change cov[kpzRegularized P Z t δ 0 0, kpzRegularized P Z t δ 0 z; P] = _ at hspec
  change regCovKernel P Z t δ z = _
  calc
    regCovKernel P Z t δ z =
        cov[kpzRegularized P Z t δ 0 0, kpzRegularized P Z t δ 0 z; P] := rfl
    _ = regCovKernel P Z t δ (-z) := hspec'

/-- Every weighted weak covariance limit is even almost everywhere. -/
theorem weightedWeakCovarianceLimit_even_of_shfSymmetries
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : LocalSobolev.ShfSymmetriesAt ϑ P Z)
    (hrevL : SmallScales.ShfReversalLawAt P Z)
    {t : ℝ} (ht : 0 < t) (s : ℕ → ℕ) (v : Lp ℝ 2 (volume : Measure Plane))
    (hmem : ∀ n : ℕ, MemLp (fun z : Plane => covarianceDecayWeight z *
      regCovKernel P Z t (t / ((n : ℝ) + 3)) z) 2 volume)
    (hweak : ∀ g : Lp ℝ 2 (volume : Measure Plane),
      Tendsto (fun n => inner ℝ ((hmem (s n)).toLp (fun z : Plane => covarianceDecayWeight z *
        regCovKernel P Z t (t / ((s n : ℝ) + 3)) z)) g)
        atTop (𝓝 (inner ℝ v g))) :
    (fun z : Plane => v (-z)) =ᵐ[volume] v := by
  apply weakLimitL2_even_of_even_seq s v
    (fun n z => covarianceDecayWeight z * regCovKernel P Z t (t / ((n : ℝ) + 3)) z)
    hmem (by simpa using hweak) ?_
  intro n z
  have hδ : 0 < t / ((n : ℝ) + 3) := by positivity
  have hδt : t / ((n : ℝ) + 3) < t := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hd : 1 < (n : ℝ) + 3 := by linarith
    exact div_lt_self ht hd
  have hEq := regCovKernel_even_of_shfSymmetries ϑ P Z hZ hsym hrevL hδ hδt z
  simp [covarianceDecayWeight, norm_neg, hEq]

end Critical2DKPZ.CovarianceKernel

end
