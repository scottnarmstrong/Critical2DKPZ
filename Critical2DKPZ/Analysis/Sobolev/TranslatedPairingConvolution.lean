/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.Localization
public import Critical2DKPZ.Analysis.Sobolev.Rellich.RellichConvolutionJets
public import Critical2DKPZ.Analysis.Sobolev.TranslatedKernelDerivative
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Convolution against a translated distribution pairing

Integrating a translated pairing against a compact smooth weight moves the weight and kernel into
one convolution test function before applying the distribution.
-/

@[expose] public section

noncomputable section

open MeasureTheory TopologicalSpace
open scoped Convolution Distributions Pointwise

namespace Critical2DKPZ.Analysis.Sobolev

/-- Reflection of a compact smooth test function. -/
def reflectedTestFn (ρ : TestFn) : TestFn := {
  toFun := fun x => ρ (-x)
  contDiff' := ρ.contDiff.comp contDiff_neg
  hasCompactSupport' := ρ.hasCompactSupport.comp_homeomorph (Homeomorph.neg Plane)
  tsupport_subset' := fun _ _ => trivial }

/-- Reflection of a test function evaluates it at the opposite point. -/
@[simp] theorem reflectedTestFn_apply (ρ : TestFn) (x : Plane) :
    reflectedTestFn ρ x = ρ (-x) := rfl

/-- The convolution of a weight with the reflected kernel, bundled as a test function. -/
def testFnConvolution (ψ ρ : TestFn) : TestFn := {
  toFun := MeasureTheory.convolution ψ (reflectedTestFn ρ)
    (ContinuousLinearMap.mul ℝ ℝ) volume
  contDiff' := by
    exact (reflectedTestFn ρ).hasCompactSupport.contDiff_convolution_right
      (ContinuousLinearMap.mul ℝ ℝ) ψ.continuous.locallyIntegrable
      (reflectedTestFn ρ).contDiff
  hasCompactSupport' := HasCompactSupport.convolution
    (L := ContinuousLinearMap.mul ℝ ℝ) (μ := volume) ψ.hasCompactSupport
      (reflectedTestFn ρ).hasCompactSupport
  tsupport_subset' := fun _ _ => trivial }

/-- Test-function convolution evaluates to its defining translated-product integral. -/
@[simp] theorem testFnConvolution_apply (ψ ρ : TestFn) (x : Plane) :
    testFnConvolution ψ ρ x = ∫ y, ψ y * ρ (y - x) := by
  change MeasureTheory.convolution ψ (reflectedTestFn ρ)
    (ContinuousLinearMap.mul ℝ ℝ) volume x = _
  rw [MeasureTheory.convolution_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [reflectedTestFn_apply]
  congr 1
  abel_nf

/-- Convolution preserves the product of the total masses of its two test functions. -/
theorem integral_testFnConvolution (ψ ρ : TestFn) :
    ∫ x, testFnConvolution ψ ρ x = (∫ y, ψ y) * (∫ y, ρ y) := by
  have hreflect : ∫ x, reflectedTestFn ρ x = ∫ x, ρ x := by
    change ∫ x, ρ (-x) = ∫ x, ρ x
    rw [integral_neg_eq_self]
  have hψ : Integrable ψ volume :=
    ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
  have hρ : Integrable (reflectedTestFn ρ) volume :=
    (reflectedTestFn ρ).continuous.integrable_of_hasCompactSupport
      (reflectedTestFn ρ).hasCompactSupport
  calc
    ∫ x, testFnConvolution ψ ρ x =
        ∫ x, (ψ ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] reflectedTestFn ρ) x := rfl
    _ = (∫ y, ψ y) * (∫ x, reflectedTestFn ρ x) := by
      have hconv := MeasureTheory.integral_convolution
        (ContinuousLinearMap.mul ℝ ℝ) hψ hρ
      change (∫ x, (ψ ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] reflectedTestFn ρ) x) =
        (∫ y, ψ y) * (∫ x, reflectedTestFn ρ x) at hconv
      exact hconv
    _ = (∫ y, ψ y) * (∫ y, ρ y) := by rw [hreflect]

/-- The topological support of the convolution lies in the sum of the supports, by the canonical
Rellich convolution support theorem. -/
theorem tsupport_testFnConvolution_subset_sum (ψ ρ : TestFn) :
    tsupport (testFnConvolution ψ ρ) ⊆
      tsupport ψ + tsupport (reflectedTestFn ρ) := by
  have hψ : Critical2DKPZ.Analysis.Sobolev.Rellich.IsTestFn (tsupport ψ) ψ :=
    ⟨ψ.contDiff, ψ.hasCompactSupport, subset_rfl⟩
  have hbounded : Bornology.IsBounded (tsupport ψ) :=
    ψ.hasCompactSupport.isCompact.isBounded
  have hconv := Critical2DKPZ.Analysis.Sobolev.Rellich.tsupport_convReal_subset_sum
    (d := 2) hbounded hψ (reflectedTestFn ρ).hasCompactSupport
  have hclosed : IsClosed (tsupport ψ) := isClosed_tsupport _
  have hcl : closure (tsupport ψ) = tsupport ψ := hclosed.closure_eq
  change tsupport (Critical2DKPZ.Analysis.Sobolev.Rellich.convReal ψ (reflectedTestFn ρ)) ⊆
    tsupport ψ + tsupport (reflectedTestFn ρ)
  rw [hcl] at hconv
  calc
    tsupport (Critical2DKPZ.Analysis.Sobolev.Rellich.convReal ψ (reflectedTestFn ρ)) ⊆
        tsupport (reflectedTestFn ρ) + tsupport ψ := hconv
    _ = tsupport ψ + tsupport (reflectedTestFn ρ) := add_comm _ _

/-- The convolution test function has the derivative supplied by differentiation of its compact
kernel. -/
theorem hasFDerivAt_testFnConvolution (ψ ρ : TestFn) (x : Plane) :
    HasFDerivAt (testFnConvolution ψ ρ)
      ((ψ ⋆[(ContinuousLinearMap.mul ℝ ℝ).precompR Plane, volume]
        fderiv ℝ (reflectedTestFn ρ)) x) x := by
  change HasFDerivAt
    (ψ ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] reflectedTestFn ρ)
    ((ψ ⋆[(ContinuousLinearMap.mul ℝ ℝ).precompR Plane, volume]
      fderiv ℝ (reflectedTestFn ρ)) x) x
  exact (reflectedTestFn ρ).hasCompactSupport.hasFDerivAt_convolution_right
    (ContinuousLinearMap.mul ℝ ℝ) ψ.continuous.locallyIntegrable
    ((reflectedTestFn ρ).contDiff.of_le (by simp)) x

/-- Iterated directional differentiation of a compact smooth kernel gives another compact smooth test function. -/
def iteratedDirectionalTestKernel (ρ : TestFn) : (k : ℕ) → (Fin k → Plane) → TestFn
  | 0, _ => ρ
  | k + 1, v =>
      directionalDerivativeKernel (iteratedDirectionalTestKernel ρ k (Fin.tail v)) (v 0)

/-- The test-kernel recursion agrees pointwise with directional differentiation on the Euclidean plane. -/
theorem iteratedDirectionalTestKernel_eq_rellich (ρ : TestFn) :
    ∀ (k : ℕ) (v : Fin k → Plane) (x : Plane),
      iteratedDirectionalTestKernel ρ k v x =
        Critical2DKPZ.Analysis.Sobolev.Rellich.rellichDirectionalKernel ρ k v x := by
  intro k
  induction k with
  | zero =>
      intro v x
      rfl
  | succ k ih =>
      intro v x
      change fderiv ℝ (iteratedDirectionalTestKernel ρ k (Fin.tail v)) x (v 0) =
        fderiv ℝ (Critical2DKPZ.Analysis.Sobolev.Rellich.rellichDirectionalKernel ρ k (Fin.tail v)) x (v 0)
      have hfun : iteratedDirectionalTestKernel ρ k (Fin.tail v) =
          Critical2DKPZ.Analysis.Sobolev.Rellich.rellichDirectionalKernel ρ k (Fin.tail v) := by
        funext z
        exact ih (Fin.tail v) z
      rw [hfun]

/-- The actual iterated directional derivative of a translated pairing, with directions ordered
from the outer derivative to the inner derivative. -/
noncomputable def iteratedTranslatedPairingDerivative (T : Distr) (φ ρ : TestFn) :
    (k : ℕ) → (Fin k → Plane) → Plane → ℝ
  | 0, _ => translatedDistributionPairing T φ ρ
  | k + 1, v => fun y =>
      fderiv ℝ (iteratedTranslatedPairingDerivative T φ ρ k (Fin.tail v)) y (v 0)

/-- Every iterated translation derivative is the translated pairing against the corresponding
iterated directional derivative of the kernel. -/
theorem iteratedTranslatedPairingDerivative_eq_kernel (T : Distr) (φ ρ : TestFn) :
    ∀ (k : ℕ) (v : Fin k → Plane),
      (fun y => iteratedTranslatedPairingDerivative T φ ρ k v y) =
        translatedDistributionPairing T φ (iteratedDirectionalTestKernel ρ k v) := by
  intro k
  induction k with
  | zero =>
      intro v
      rfl
  | succ k ih =>
      intro v
      change (fun y => fderiv ℝ
          (iteratedTranslatedPairingDerivative T φ ρ k (Fin.tail v)) y (v 0)) =
        translatedDistributionPairing T φ
          (directionalDerivativeKernel (iteratedDirectionalTestKernel ρ k (Fin.tail v)) (v 0))
      have hfun := ih (Fin.tail v)
      funext y
      have hfun' := congrArg (fun g : Plane → ℝ => fderiv ℝ g y (v 0)) hfun
      calc
        fderiv ℝ (iteratedTranslatedPairingDerivative T φ ρ k (Fin.tail v)) y (v 0) =
            fderiv ℝ (translatedDistributionPairing T φ
              (iteratedDirectionalTestKernel ρ k (Fin.tail v))) y (v 0) := hfun'
        _ = translatedDistributionPairing T φ
              (directionalDerivativeKernel (iteratedDirectionalTestKernel ρ k (Fin.tail v))
                (v 0)) y := by
                rw [(hasFDerivAt_translatedDistributionPairing T φ
                  (iteratedDirectionalTestKernel ρ k (Fin.tail v)) y).fderiv,
                  translatedDistributionPairingFDeriv_apply,
                  translatedDistributionPairingDirectionalDerivative_eq_kernel]

/-- A weighted integral of translated distribution pairings is the distribution applied to the
product of the original test function and the weight-kernel convolution. -/
theorem integral_mul_translatedDistributionPairing_eq_testFnConvolution
    (T : Distr) (φ ρ ψ : TestFn) :
    ∫ y, ψ y * translatedDistributionPairing T φ ρ y =
      T (testFnMul φ (testFnConvolution ψ ρ)) := by
  let K : Compacts Plane := ⟨tsupport φ, φ.hasCompactSupport.isCompact⟩
  let S : Compacts Plane := ⟨tsupport ψ, ψ.hasCompactSupport.isCompact⟩
  let F (y : Plane) : ContDiffMapSupportedIn Plane ℝ ⊤ K := {
    toFun := fun x => ψ y * φ x * ρ (y - x)
    contDiff' := by
      have hsub : ContDiff ℝ (⊤ : ℕ∞) (fun x : Plane => y - x) := by
        simpa only [id_eq] using (contDiff_const.sub contDiff_id)
      exact ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Plane => ψ y)).mul
        φ.contDiff).mul (ρ.contDiff.comp hsub)
    zero_on_compl' := by
      intro x hx
      have hφ : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hφ] }
  have Ktop : (K : Set Plane) ⊆ (⊤ : Opens Plane) := fun _ _ => trivial
  have K0top : (compactTestSupport φ : Set Plane) ⊆ (⊤ : Opens Plane) :=
    fun _ _ => trivial
  have hF : ContDiff ℝ (⊤ : ℕ∞) (fun p : Plane × Plane => F p.1 p.2) := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Plane × Plane => ψ p.1 * φ p.2 * ρ (p.1 - p.2))
    exact ((ψ.contDiff.comp contDiff_fst).mul (φ.contDiff.comp contDiff_snd)).mul
      (ρ.contDiff.comp (contDiff_fst.sub contDiff_snd))
  have hS : ∀ y, y ∉ S → F y = 0 := by
    intro y hy
    change y ∉ tsupport ψ at hy
    have hψ : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy
    apply ContDiffMapSupportedIn.ext
    intro x
    change ψ y * φ x * ρ (y - x) = 0
    simp [hψ]
  let η := testFnConvolution ψ ρ
  let output : ContDiffMapSupportedIn Plane ℝ ⊤ K := {
    toFun := testFnMul φ η
    contDiff' := (testFnMul φ η).contDiff
    zero_on_compl' := by
      intro x hx
      change x ∉ tsupport φ at hx
      have hφ : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [testFnMul_apply, hφ]
      simp }
  have hout : TestFunction.ofSupportedIn Ktop output = testFnMul φ η := by
    ext x
    rfl
  have hφ : ∀ x, testFnMul φ η x = ∫ y, F y x := by
    intro x
    rw [testFnMul_apply, testFnConvolution_apply]
    calc
      φ x * (∫ y, ψ y * ρ (y - x)) =
          ∫ y, φ x * (ψ y * ρ (y - x)) := by rw [integral_const_mul]
      _ = ∫ y, ψ y * φ x * ρ (y - x) := by
        apply integral_congr_ae
        filter_upwards [] with y
        ring
  have hcomm := distribution_integral_compact_smooth_test_family volume T S K F hF hS
    output hφ
  have hpair (y : Plane) :
      T (TestFunction.ofSupportedIn Ktop (F y)) =
        ψ y * translatedDistributionPairing T φ ρ y := by
    have heq : TestFunction.ofSupportedIn Ktop (F y) =
        ψ y • TestFunction.ofSupportedIn K0top
          (translatedTestFamily φ ρ y) := by
      ext x
      change ψ y * φ x * ρ (y - x) = ψ y * (φ x * ρ (y - x))
      ring
    calc
      T (TestFunction.ofSupportedIn Ktop (F y)) =
          T (ψ y • TestFunction.ofSupportedIn K0top
            (translatedTestFamily φ ρ y)) := by rw [heq]
      _ = ψ y • T (TestFunction.ofSupportedIn K0top
            (translatedTestFamily φ ρ y)) := by rw [map_smul]
      _ = ψ y * translatedDistributionPairing T φ ρ y := by
        rw [smul_eq_mul, translatedDistributionPairing_apply]
  calc
    ∫ y, ψ y * translatedDistributionPairing T φ ρ y =
        ∫ y, T (TestFunction.ofSupportedIn Ktop (F y)) := by
          apply integral_congr_ae
          filter_upwards [] with y
          exact (hpair y).symm
    _ = T (TestFunction.ofSupportedIn Ktop output) := hcomm.symm
    _ = T (testFnMul φ η) := by rw [hout]

/-- Every finite translation jet can be integrated against a compact test weight by applying the
distribution to the convolution with the corresponding differentiated kernel. -/
theorem integral_mul_iteratedTranslatedPairingDerivative_eq_testFnConvolution
    (T : Distr) (φ ρ ψ : TestFn) (k : ℕ) (v : Fin k → Plane) :
    ∫ y, ψ y * iteratedTranslatedPairingDerivative T φ ρ k v y =
      T (testFnMul φ (testFnConvolution ψ (iteratedDirectionalTestKernel ρ k v))) := by
  calc
    ∫ y, ψ y * iteratedTranslatedPairingDerivative T φ ρ k v y =
        ∫ y, ψ y * translatedDistributionPairing T φ
          (iteratedDirectionalTestKernel ρ k v) y := by
            apply integral_congr_ae
            filter_upwards [] with y
            have hjet := congrFun
              (iteratedTranslatedPairingDerivative_eq_kernel T φ ρ k v) y
            rw [hjet]
    _ = T (testFnMul φ (testFnConvolution ψ (iteratedDirectionalTestKernel ρ k v))) :=
      integral_mul_translatedDistributionPairing_eq_testFnConvolution
        T φ (iteratedDirectionalTestKernel ρ k v) ψ

/-- The same distributional convolution identity applies to the first translation jet, by using
the differentiated kernel as the compact convolution kernel. -/
theorem integral_mul_translatedDistributionPairingDirectionalDerivative_eq_testFnConvolution
    (T : Distr) (φ ρ ψ : TestFn) (v : Plane) :
    ∫ y, ψ y * translatedDistributionPairingDirectionalDerivative T φ ρ (y, v) =
      T (testFnMul φ (testFnConvolution ψ (directionalDerivativeKernel ρ v))) := by
  calc
    ∫ y, ψ y * translatedDistributionPairingDirectionalDerivative T φ ρ (y, v) =
        ∫ y, ψ y * translatedDistributionPairing T φ (directionalDerivativeKernel ρ v) y := by
          apply integral_congr_ae
          filter_upwards [] with y
          rw [translatedDistributionPairingDirectionalDerivative_eq_kernel]
    _ = T (testFnMul φ (testFnConvolution ψ (directionalDerivativeKernel ρ v))) :=
      integral_mul_translatedDistributionPairing_eq_testFnConvolution
        T φ (directionalDerivativeKernel ρ v) ψ

/-- The integral of the mixed second translation derivative is the distribution applied to the
convolution against the twice differentiated kernel. -/
theorem integral_mul_translatedDistributionPairingSecondDerivative_eq_testFnConvolution
    (T : Distr) (φ ρ ψ : TestFn) (v w : Plane) :
    ∫ y, ψ y * fderiv ℝ
      (fun z => translatedDistributionPairingDirectionalDerivative T φ ρ (z, v)) y w =
        T (testFnMul φ (testFnConvolution ψ
          (directionalDerivativeKernel (directionalDerivativeKernel ρ v) w))) := by
  have hderiv (y : Plane) :
      fderiv ℝ
        (fun z => translatedDistributionPairingDirectionalDerivative T φ ρ (z, v)) y w =
          translatedDistributionPairingDirectionalDerivative T φ
            (directionalDerivativeKernel ρ v) (y, w) := by
    have h :=
      (hasFDerivAt_translatedDistributionPairingDirectionalDerivative T φ ρ y v).fderiv
    have hw := congrArg (fun L : Plane →L[ℝ] ℝ => L w) h
    simpa only [translatedDistributionPairingFDeriv_apply] using hw
  calc
    ∫ y, ψ y * fderiv ℝ
        (fun z => translatedDistributionPairingDirectionalDerivative T φ ρ (z, v)) y w =
        ∫ y, ψ y * translatedDistributionPairingDirectionalDerivative T φ
          (directionalDerivativeKernel ρ v) (y, w) := by
            apply integral_congr_ae
            filter_upwards [] with y
            rw [hderiv]
    _ = T (testFnMul φ (testFnConvolution ψ
          (directionalDerivativeKernel (directionalDerivativeKernel ρ v) w))) :=
      integral_mul_translatedDistributionPairingDirectionalDerivative_eq_testFnConvolution
        T φ (directionalDerivativeKernel ρ v) ψ w

end Critical2DKPZ.Analysis.Sobolev

end
