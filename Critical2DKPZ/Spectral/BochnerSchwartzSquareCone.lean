/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Spectral.SchwartzKernelIntegrability
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # The Fourier transform of a positive-type kernel on Schwartz squares -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate Convolution FourierTransform

namespace Critical2DKPZ.Spectral

/-- Complex conjugation on Schwartz functions. -/
noncomputable def conjugateSchwartz (f : SchwartzMap Plane ℂ) : SchwartzMap Plane ℂ :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.conjCLE f

/-- Reflection of a Schwartz function through the origin. -/
noncomputable def reflectedSchwartz (f : SchwartzMap Plane ℂ) : SchwartzMap Plane ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((LinearIsometryEquiv.neg ℝ (E := Plane)).toContinuousLinearEquiv) f

/-- The autocorrelation Schwartz function associated with a complex Schwartz function. -/
noncomputable def schwartzAutocorrelation (f : SchwartzMap Plane ℂ) : SchwartzMap Plane ℂ :=
  SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
    (conjugateSchwartz f) (reflectedSchwartz f)

/-- Conjugating a Schwartz function conjugates each of its values. -/
@[simp] theorem conjugateSchwartz_apply (f : SchwartzMap Plane ℂ) (x : Plane) :
    conjugateSchwartz f x = conj (f x) := rfl


/-- Pointwise, the Schwartz autocorrelation is the expected translated quadratic integral. -/
theorem schwartzAutocorrelation_apply (f : SchwartzMap Plane ℂ) (z : Plane) :
    schwartzAutocorrelation f z = ∫ y : Plane, conj (f (z + y)) * f y := by
  rw [schwartzAutocorrelation, SchwartzMap.convolution_apply]
  rw [convolution_eq_swap]
  change (∫ y : Plane, conj (f (z - y)) * f (-y)) = _
  rw [← integral_neg_eq_self]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [neg_neg, sub_neg_eq_add]

/-- Fourier transform conjugation reflects frequency. -/
theorem fourier_conjugateSchwartz_apply (f : SchwartzMap Plane ℂ) (ξ : Plane) :
    𝓕 (conjugateSchwartz f) ξ = conj (𝓕 f (-ξ)) := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, Real.fourier_eq, Real.fourier_eq]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [Circle.smul_def, inner_neg_right]

/-- Fourier transform reflection reflects frequency. -/
theorem fourier_reflectedSchwartz_apply (f : SchwartzMap Plane ℂ) (ξ : Plane) :
    𝓕 (reflectedSchwartz f) ξ = 𝓕 f (-ξ) := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
  change 𝓕 (f ∘ LinearIsometryEquiv.neg ℝ) ξ = _
  rw [Real.fourier_comp_linearIsometry]
  rfl

/-- The Fourier transform of a Schwartz autocorrelation is a pointwise square. -/
theorem fourier_schwartzAutocorrelation_apply (f : SchwartzMap Plane ℂ) (ξ : Plane) :
    𝓕 (schwartzAutocorrelation f) ξ =
      Complex.ofReal (‖𝓕 f (-ξ)‖ ^ 2) := by
  rw [schwartzAutocorrelation, SchwartzMap.fourier_convolution]
  rw [SchwartzMap.pairing_apply_apply, fourier_conjugateSchwartz_apply,
    fourier_reflectedSchwartz_apply]
  change conj (𝓕 f (-ξ)) * 𝓕 f (-ξ) = _
  rw [Complex.conj_mul', ← Complex.ofReal_pow]

/-- Regard a real Schwartz function as a complex Schwartz function. -/
noncomputable def realSchwartzToComplex (r : SchwartzMap Plane ℝ) : SchwartzMap Plane ℂ :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM r

/-- Complexification of a real Schwartz function preserves its values. -/
@[simp] theorem realSchwartzToComplex_apply (r : SchwartzMap Plane ℝ) (x : Plane) :
    realSchwartzToComplex r x = (r x : ℂ) := rfl

/-- The complex Schwartz function given by the pointwise square of a real Schwartz function. -/
noncomputable def realSchwartzSquare (r : SchwartzMap Plane ℝ) : SchwartzMap Plane ℂ :=
  SchwartzMap.pairing (𝕜 := ℂ) (ContinuousLinearMap.mul ℂ ℂ)
    (realSchwartzToComplex r) (realSchwartzToComplex r)

/-- The complex Schwartz square evaluates to the square of the real function. -/
@[simp] theorem realSchwartzSquare_apply (r : SchwartzMap Plane ℝ) (x : Plane) :
    realSchwartzSquare r x = (r x ^ 2 : ℂ) := by
  simp [realSchwartzSquare, pow_two, ← Complex.ofReal_mul]

/-- The autocorrelation of the inverse Fourier transform of a real Schwartz function is the
Fourier transform of its pointwise square. -/
theorem schwartzAutocorrelation_fourierInv_real (r : SchwartzMap Plane ℝ) :
    schwartzAutocorrelation (𝓕⁻ (realSchwartzToComplex r)) =
      𝓕 (realSchwartzSquare r) := by
  have hFourier :
      𝓕 (schwartzAutocorrelation (𝓕⁻ (realSchwartzToComplex r))) =
        𝓕 (𝓕 (realSchwartzSquare r)) := by
    ext ξ
    rw [fourier_schwartzAutocorrelation_apply]
    have hInv : 𝓕 (𝓕⁻ (realSchwartzToComplex r)) = realSchwartzToComplex r := by
      simp
    rw [hInv]
    have hFourierSquare : 𝓕 (𝓕 (realSchwartzSquare r)) ξ =
        realSchwartzSquare r (-ξ) := by
      calc
        𝓕 (𝓕 (realSchwartzSquare r)) ξ =
            𝓕⁻ (𝓕 (realSchwartzSquare r)) (-ξ) := by
          simpa only [SchwartzMap.fourier_coe, SchwartzMap.fourierInv_coe, neg_neg] using
            (Real.fourierInv_eq_fourier_neg
              (fun x : Plane => 𝓕 (realSchwartzSquare r) x) (-ξ)).symm
        _ = realSchwartzSquare r (-ξ) := by
          exact congrArg (fun q : SchwartzMap Plane ℂ => q (-ξ))
            (show 𝓕⁻ (𝓕 (realSchwartzSquare r)) = realSchwartzSquare r by simp)
    rw [hFourierSquare, realSchwartzSquare_apply]
    simp [realSchwartzToComplex, Complex.norm_real, sq_abs]
  have h := congrArg (fun q : SchwartzMap Plane ℂ => 𝓕⁻ q) hFourier
  simpa using h

/-- The complex Schwartz quadratic form is the kernel integral against its autocorrelation. -/
theorem integral_complex_schwartz_kernelPair_eq_autocorrelation (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (∫ z in Metric.closedBall 0 R, |C z|) ≤ A * R ^ k)
    (heven : (fun z : Plane => C (-z)) =ᵐ[volume] C)
    (hpos : ∀ φ : TestFn, 0 ≤ ∫ p : Plane × Plane,
      φ p.1 * φ p.2 * C (p.1 - p.2)) (f : SchwartzMap Plane ℂ) :
    (∫ p : Plane × Plane,
      conj (f p.1) * f p.2 * (C (p.1 - p.2) : ℂ) ∂(volume.prod volume)) =
      ∫ z : Plane, schwartzAutocorrelation f z * (C z : ℂ) := by
  let F : Plane × Plane → ℂ := fun p =>
    conj (f (p.1 + p.2)) * f p.2 * (C p.1 : ℂ)
  let e : Plane × Plane ≃ᵐ Plane × Plane := {
    toEquiv := {
      toFun := fun p => (p.1 - p.2, p.2)
      invFun := fun p => (p.1 + p.2, p.2)
      left_inv := by intro p; ext <;> simp
      right_inv := by intro p; ext <;> simp }
    measurable_toFun := (continuous_fst.sub continuous_snd).measurable.prodMk
      measurable_snd
    measurable_invFun := (continuous_fst.add continuous_snd).measurable.prodMk
      measurable_snd }
  have hpair := (complex_schwartz_kernel_quadratic_nonneg C hC hgrowth
    heven hpos f).1
  have hcomp : Integrable (F ∘ e) (volume.prod volume) := by
    apply hpair.congr
    filter_upwards [] with p
    rcases p with ⟨x, y⟩
    dsimp [F, e]
    rw [sub_add_cancel]
  have hmp : MeasurePreserving (fun p : Plane × Plane => (p.1 - p.2, p.2))
      (volume.prod volume) (volume.prod volume) := by
    exact measurePreserving_sub_prod volume volume
  have hF : Integrable F (volume.prod volume) :=
    (hmp.integrable_comp_emb e.measurableEmbedding).mp hcomp
  have hshift (z : Plane) :
      (∫ y : Plane, conj (f (z + y)) * f y) = schwartzAutocorrelation f z :=
    (schwartzAutocorrelation_apply f z).symm
  calc
    (∫ p : Plane × Plane,
      conj (f p.1) * f p.2 * (C (p.1 - p.2) : ℂ) ∂(volume.prod volume)) =
        ∫ p : Plane × Plane, F (e p) := by
          apply integral_congr_ae
          filter_upwards [] with p
          rcases p with ⟨x, y⟩
          dsimp [F, e]
          rw [sub_add_cancel]
    _ = ∫ p : Plane × Plane, F p := hmp.integral_comp' F
    _ = ∫ z : Plane, ∫ y : Plane, F (z, y) := integral_prod F hF
    _ = ∫ z : Plane, schwartzAutocorrelation f z * (C z : ℂ) := by
          apply integral_congr_ae
          filter_upwards [] with z
          dsimp [F]
          calc
            (∫ y : Plane, conj (f (z + y)) * f y * (C z : ℂ)) =
                (C z : ℂ) * ∫ y : Plane, conj (f (z + y)) * f y := by
                  rw [show (fun y : Plane => conj (f (z + y)) * f y * (C z : ℂ)) =
                    (fun y => (C z : ℂ) * (conj (f (z + y)) * f y)) by
                      funext y
                      ring,
                    integral_const_mul]
            _ = schwartzAutocorrelation f z * (C z : ℂ) := by
                  rw [hshift z]
                  ring

/-- The Fourier transform of the kernel distribution is nonnegative on squares of real Schwartz
functions. -/
theorem fourier_kernelTemperedDistribution_re_nonneg_realSchwartzSquare (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (∫ z in Metric.closedBall 0 R, |C z|) ≤ A * R ^ k)
    (heven : (fun z : Plane => C (-z)) =ᵐ[volume] C)
    (hpos : ∀ φ : TestFn, 0 ≤ ∫ p : Plane × Plane,
      φ p.1 * φ p.2 * C (p.1 - p.2)) (r : SchwartzMap Plane ℝ) :
    0 ≤ ((𝓕 (kernelTemperedDistribution C hC hgrowth))
      (realSchwartzSquare r)).re := by
  let f := 𝓕⁻ (realSchwartzToComplex r)
  have hquadratic := complex_schwartz_kernel_quadratic_nonneg
    C hC hgrowth heven hpos f
  have hpair := integral_complex_schwartz_kernelPair_eq_autocorrelation
    C hC hgrowth heven hpos f
  have hauto := schwartzAutocorrelation_fourierInv_real r
  have hEq :
      (∫ x : Plane, (C x : ℂ) * (𝓕 (realSchwartzSquare r)) x) =
        ∫ p : Plane × Plane,
          conj (f p.1) * f p.2 * (C (p.1 - p.2) : ℂ) ∂(volume.prod volume) := by
    calc
      (∫ x : Plane, (C x : ℂ) * (𝓕 (realSchwartzSquare r)) x) =
          ∫ x : Plane, schwartzAutocorrelation f x * (C x : ℂ) := by
            rw [← hauto]
            apply integral_congr_ae
            filter_upwards [] with x
            ring
      _ = ∫ p : Plane × Plane,
          conj (f p.1) * f p.2 * (C (p.1 - p.2) : ℂ) ∂(volume.prod volume) := hpair.symm
  rw [TemperedDistribution.fourier_apply,
    kernelTemperedDistribution_apply_schwartz C hC hgrowth, hEq]
  exact hquadratic.2.1

/-- Embed a real compactly supported smooth test function into real Schwartz space. -/
noncomputable def testFnToRealSchwartz (f : TestFn) : SchwartzMap Plane ℝ :=
  f.hasCompactSupport.toSchwartzMap f.contDiff

/-- Viewing a test function as a real Schwartz function preserves its values. -/
@[simp] theorem testFnToRealSchwartz_apply (f : TestFn) (x : Plane) :
    testFnToRealSchwartz f x = f x := rfl

/-- A compactly supported smooth square root of `f + ε`, cut off by the canonical localizer. -/
noncomputable def positiveTestSquareRoot (f : TestFn) (ε : ℝ) (hε : 0 < ε)
    (hf : ∀ x : Plane, 0 ≤ f x) (n : ℕ) : TestFn where
  toFun x := Critical2DKPZ.localizer n x * Real.sqrt (f x + ε)
  contDiff' := by
    apply (Critical2DKPZ.localizer n).contDiff.mul
    apply ContDiff.sqrt
    · exact f.contDiff.add contDiff_const
    · intro x
      exact (add_pos_of_nonneg_of_pos (hf x) hε).ne'
  hasCompactSupport' := (Critical2DKPZ.localizer n).hasCompactSupport.mul_right
  tsupport_subset' := fun _ _ => trivial


/-- A positive-type kernel's Fourier distribution is nonnegative on every nonnegative compact
test. -/
theorem fourier_kernelTemperedDistribution_re_nonneg_testFn (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (∫ z in Metric.closedBall 0 R, |C z|) ≤ A * R ^ k)
    (heven : (fun z : Plane => C (-z)) =ᵐ[volume] C)
    (hpos : ∀ φ : TestFn, 0 ≤ ∫ p : Plane × Plane,
      φ p.1 * φ p.2 * C (p.1 - p.2))
    (f : TestFn) (hf : ∀ x : Plane, 0 ≤ f x) :
    0 ≤ ((𝓕 (kernelTemperedDistribution C hC hgrowth))
      (testFnToSchwartzMap f)).re := by
  obtain ⟨n, hn⟩ := Critical2DKPZ.exists_localizer_mul_testFn_eq f
  let χ : TestFn := Critical2DKPZ.localizer n
  let χsq : TestFn := Critical2DKPZ.testFnMul χ χ
  have hcut (x : Plane) : χ x * f x = f x := by
    change Critical2DKPZ.localizer n x * f x = f x
    exact hn n le_rfl x
  let T := 𝓕 (kernelTemperedDistribution C hC hgrowth)
  let a : ℝ := (T (testFnToSchwartzMap f)).re
  let b : ℝ := (T (testFnToSchwartzMap χsq)).re
  have hperturb (ε : ℝ) (hε : 0 < ε) : 0 ≤ a + ε * b := by
    let r : TestFn := positiveTestSquareRoot f ε hε hf n
    let rs : SchwartzMap Plane ℝ := testFnToRealSchwartz r
    have hχsqf (x : Plane) : χ x ^ 2 * f x = f x := by
      calc
        χ x ^ 2 * f x = χ x * (χ x * f x) := by ring
        _ = χ x * f x := congrArg (fun y : ℝ => χ x * y) (hcut x)
        _ = f x := hcut x
    have hrSquare (x : Plane) : r x ^ 2 = f x + ε * χ x ^ 2 := by
      change (χ x * Real.sqrt (f x + ε)) ^ 2 = _
      rw [mul_pow, Real.sq_sqrt (add_nonneg (hf x) hε.le)]
      calc
        χ x ^ 2 * (f x + ε) = χ x ^ 2 * f x + ε * χ x ^ 2 := by ring
        _ = f x + ε * χ x ^ 2 := by rw [hχsqf]
    have hSchwartzEq : realSchwartzSquare rs =
        testFnToSchwartzMap f + (ε : ℂ) • testFnToSchwartzMap χsq := by
      ext x
      simp only [realSchwartzSquare_apply, rs, testFnToRealSchwartz_apply,
        add_apply, smul_apply, smul_eq_mul, testFnToSchwartzMap_apply,
        χsq, Critical2DKPZ.testFnMul_apply]
      have hreal : r x ^ 2 = f x + ε * (χ x * χ x) := by
        rw [hrSquare x]
        ring
      calc
        Complex.ofReal (r x) ^ 2 = Complex.ofReal (r x ^ 2) := by
          rw [Complex.ofReal_pow]
        _ = Complex.ofReal (f x + ε * (χ x * χ x)) := congrArg Complex.ofReal hreal
        _ = Complex.ofReal (f x) + Complex.ofReal ε * Complex.ofReal (χ x * χ x) := by
          rw [Complex.ofReal_add, Complex.ofReal_mul]
    have hEval : T (realSchwartzSquare rs) =
        T (testFnToSchwartzMap f) + (ε : ℂ) * T (testFnToSchwartzMap χsq) := by
      rw [hSchwartzEq]
      simp only [map_add, map_smul, smul_eq_mul]
    have hRealEval : (T (realSchwartzSquare rs)).re = a + ε * b := by
      rw [hEval]
      simp [a, b, Complex.mul_re]
    have hSquare := fourier_kernelTemperedDistribution_re_nonneg_realSchwartzSquare
      C hC hgrowth heven hpos rs
    rw [hRealEval] at hSquare
    exact hSquare
  by_contra hnot
  have ha : a < 0 := lt_of_not_ge hnot
  obtain ⟨ε, hε, hsmall⟩ := exists_pos_mul_lt (neg_pos.mpr ha) |b|
  have hbound : ε * b ≤ |b| * ε := by
    calc
      ε * b ≤ ε * |b| := mul_le_mul_of_nonneg_left (le_abs_self b) hε.le
      _ = |b| * ε := by ring
  have hcontr := hperturb ε hε
  linarith

end Critical2DKPZ.Spectral

end
