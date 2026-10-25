/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.Rellich.NegativeNormCompactness
public import Critical2DKPZ.Analysis.Sobolev.Rellich.FrozenNorm
public import Critical2DKPZ.Analysis.Sobolev.FourierProduct
public import Critical2DKPZ.Analysis.Sobolev.LocalizedEnergy
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic.Positivity

/-! The Fourier product identity and weighted Cauchy–Schwarz inequality bound distribution pairings by local negative Sobolev energy. -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap

namespace Critical2DKPZ.Analysis.Sobolev.Rellich

/-- Distribution pairings are controlled by the positive Sobolev norm of the test and the local negative Sobolev energy at a cutoff equal to one on its support. -/
theorem distribution_pairing_le_localNegSobolev_product (a : ℝ) (T : Distr)
    (χ φ : TestFn) (hχ : ∀ x ∈ tsupport φ, χ x = 1) :
    ENNReal.ofReal |T φ| ≤
      (sobolevNormSq 2 a (fun x => (φ x : ℝ))) ^ ((1 : ℝ) / 2) *
        (localNegSobolevSq a T χ) ^ ((1 : ℝ) / 2) := by
  let w : Plane → ℝ := fun η => sobolevWeight (d := 2) a η
  let A : Plane → ℝ≥0∞ := fun η => ENNReal.ofReal
    (Real.sqrt (w η) * ‖(𝓕 (testFnSchwartz φ)) η‖)
  let B : Plane → ℝ≥0∞ := fun η => ENNReal.ofReal
    (Real.sqrt (sobolevWeight (-a) η) *
      ‖localizedFourier T χ (-((2 * Real.pi) • η))‖)
  have hFourier (η : Plane) :
      (𝓕 (testFnSchwartz φ)) η = 𝓕 (fun x : Plane => (φ x : ℂ)) η := by
    rw [SchwartzMap.fourier_coe]
    rfl
  have hw : Continuous w := by
    dsimp [w]
    exact continuous_sobolevWeight (d := 2) a
  have hwn : Continuous (sobolevWeight (d := 2) (-a)) :=
    continuous_sobolevWeight (d := 2) (-a)
  have hAmeas : AEMeasurable A volume := by
    have hsqrt : Continuous (fun η : Plane => Real.sqrt (w η)) :=
      Real.continuous_sqrt.comp hw
    have hcont : Continuous (fun η : Plane =>
        Real.sqrt (w η) * ‖(𝓕 (testFnSchwartz φ)) η‖) :=
      hsqrt.mul (𝓕 (testFnSchwartz φ)).continuous.norm
    dsimp [A]
    exact hcont.measurable.ennreal_ofReal.aemeasurable
  have hBmeas : AEMeasurable B volume := by
    have hsqrt : Continuous (fun η : Plane => Real.sqrt (sobolevWeight (-a) η)) :=
      Real.continuous_sqrt.comp hwn
    have hneg : Continuous (fun η : Plane => -((2 * Real.pi) • η)) := by fun_prop
    have hcont : Continuous (fun η : Plane =>
        Real.sqrt (sobolevWeight (-a) η) *
          ‖localizedFourier T χ (-((2 * Real.pi) • η))‖) :=
      hsqrt.mul ((continuous_localizedFourier T χ).comp hneg).norm
    dsimp [B]
    exact hcont.measurable.ennreal_ofReal.aemeasurable
  have hAsq : ∫⁻ η : Plane, A η ^ (2 : ℝ) =
      sobolevNormSq 2 a (fun x => (φ x : ℝ)) := by
    rw [sobolevNormSq_eq_lintegral_weight]
    apply lintegral_congr
    intro η
    dsimp [A, w]
    rw [hFourier, ENNReal.ofReal_rpow_of_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) (by norm_num),
      Real.rpow_two, mul_pow, Real.sq_sqrt (sobolevWeight_nonneg a η)]
  have hBsq : ∫⁻ η : Plane, B η ^ (2 : ℝ) = localNegSobolevSq a T χ := by
    rw [localNegSobolevSq_eq_scaled_localizedFourier_neg]
    apply lintegral_congr
    intro η
    dsimp [B, w]
    rw [ENNReal.ofReal_rpow_of_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) (by norm_num),
      Real.rpow_two, mul_pow,
      Real.sq_sqrt (sobolevWeight_nonneg (-a) η)]
    simp only [sobolevWeight]
  have hsqrtWeight (η : Plane) :
      Real.sqrt (sobolevWeight a η) * Real.sqrt (sobolevWeight (-a) η) = 1 := by
    have hweight : sobolevWeight a η * sobolevWeight (-a) η = 1 := by
      dsimp [sobolevWeight]
      rw [← Real.rpow_add (by positivity : 0 < 1 + (2 * Real.pi * ‖η‖) ^ 2)]
      simp
    rw [← Real.sqrt_mul (sobolevWeight_nonneg a η), hweight]
    norm_num
  let g : Plane → ℂ := fun η =>
    (𝓕 (testFnSchwartz φ)) η * localizedFourier T χ (-((2 * Real.pi) • η))
  have hProduct := localizedFourier_testFnMul_eq_scaled_frequency_integral T φ χ 0
  have hProductTest : testFnMul φ χ = φ := by
    calc
      testFnMul φ χ = testFnMul χ φ := testFnMul_comm φ χ
      _ = φ := testFnMul_eq_self_of_eq_one_on_tsupport φ χ hχ
  have hAtZero : localizedFourier T φ 0 = (T φ : ℂ) := by
    have hcos : φ.mulCos 0 = φ := by
      ext x
      simp [TestFn.mulCos]
    have hsin : φ.mulSin 0 = 0 := by
      ext x
      simp [TestFn.mulSin]
    rw [localizedFourier, hcos, hsin]
    simp
  have hPair : (T φ : ℂ) = ∫ η : Plane, g η := by
    calc
      (T φ : ℂ) = localizedFourier T φ 0 := hAtZero.symm
      _ = localizedFourier T (testFnMul φ χ) 0 := by rw [hProductTest]
      _ = ∫ η : Plane, g η := by simpa [g, sub_zero] using hProduct.2
  have hInt : Integrable g := by
    simpa [g, sub_zero] using hProduct.1
  have hpoint (η : Plane) : ENNReal.ofReal ‖g η‖ = A η * B η := by
    have hnorm : ‖g η‖ =
        ‖(𝓕 (testFnSchwartz φ)) η‖ *
          ‖localizedFourier T χ (-((2 * Real.pi) • η))‖ := by
      dsimp [g]
      rw [norm_mul]
    rw [hnorm]
    dsimp [A, B]
    rw [← ENNReal.ofReal_mul
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))]
    congr 1
    calc
      ‖(𝓕 (testFnSchwartz φ)) η‖ *
          ‖localizedFourier T χ (-((2 * Real.pi) • η))‖ =
        1 * (‖(𝓕 (testFnSchwartz φ)) η‖ *
          ‖localizedFourier T χ (-((2 * Real.pi) • η))‖) := by simp
      _ = (Real.sqrt (w η) * Real.sqrt (sobolevWeight (-a) η)) *
          (‖(𝓕 (testFnSchwartz φ)) η‖ *
            ‖localizedFourier T χ (-((2 * Real.pi) • η))‖) := by
          rw [show w η = sobolevWeight a η by rfl, hsqrtWeight]
      _ = (Real.sqrt (w η) * ‖(𝓕 (testFnSchwartz φ)) η‖) *
          (Real.sqrt (sobolevWeight (-a) η) *
            ‖localizedFourier T χ (-((2 * Real.pi) • η))‖) := by ring
  have hlin : (∫⁻ η : Plane, A η * B η) =
      ENNReal.ofReal (∫ η : Plane, ‖g η‖) := by
    calc
      (∫⁻ η : Plane, A η * B η) =
          ∫⁻ η : Plane, ENNReal.ofReal ‖g η‖ := by
            apply lintegral_congr
            intro η
            exact (hpoint η).symm
      _ = ENNReal.ofReal (∫ η : Plane, ‖g η‖) :=
        (ofReal_integral_eq_lintegral_ofReal hInt.norm
          (Filter.Eventually.of_forall fun η => norm_nonneg (g η))).symm
  have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq volume
    Real.HolderConjugate.two_two hAmeas hBmeas
  calc
    ENNReal.ofReal |T φ| = ENNReal.ofReal ‖(T φ : ℂ)‖ := by simp
    _ ≤ ENNReal.ofReal (∫ η : Plane, ‖g η‖) := by
      apply ENNReal.ofReal_le_ofReal
      rw [hPair]
      exact norm_integral_le_integral_norm g
    _ = ∫⁻ η : Plane, A η * B η := hlin.symm
    _ ≤ (∫⁻ η : Plane, A η ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) *
        (∫⁻ η : Plane, B η ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := hCS
    _ = (sobolevNormSq 2 a (fun x => (φ x : ℝ))) ^ ((1 : ℝ) / 2) *
        (localNegSobolevSq a T χ) ^ ((1 : ℝ) / 2) := by rw [hAsq, hBsq]

/-- A cutoff equal to one on a bounded domain converts finite local energy into a negative Sobolev dual bound on that domain. -/
theorem distributionFunctional_negSobolevNorm_le_localEnergy
    {D : Set (Space 2)} (T : Distr) (χ : TestFn) (a : ℝ)
    (hχ : ∀ x ∈ D, χ x = 1) :
    negSobolevNorm 2 a D (distributionFunctional T) ≤
    (localNegSobolevSq a T χ) ^ ((1 : ℝ) / 2) := by
  unfold negSobolevNorm
  apply sSup_le
  rintro v ⟨φ, hφ, hnorm, rfl⟩
  have hpair := distributionFunctional_apply T hφ
  have hsupport : ∀ x ∈ tsupport (testFnOfRellich hφ.1 hφ.2.1), χ x = 1 := by
    intro x hx
    exact hχ x (hφ.2.2 hx)
  have hpoint := distribution_pairing_le_localNegSobolev_product a T χ
    (testFnOfRellich hφ.1 hφ.2.1) hsupport
  have hroot :
      (sobolevNormSq 2 a φ) ^ ((1 : ℝ) / 2) ≤ 1 := by
    calc
      (sobolevNormSq 2 a φ) ^ ((1 : ℝ) / 2) ≤
          (1 : ℝ≥0∞) ^ ((1 : ℝ) / 2) :=
        ENNReal.rpow_le_rpow hnorm (by norm_num)
      _ = 1 := by simp
  calc
    ENNReal.ofReal |distributionFunctional T φ| = ENNReal.ofReal
        |T (testFnOfRellich hφ.1 hφ.2.1)| := by rw [hpair]
    _ ≤ (sobolevNormSq 2 a φ) ^ ((1 : ℝ) / 2) *
        (localNegSobolevSq a T χ) ^ ((1 : ℝ) / 2) := by
      simpa [sobolevNormSq, testFnOfRellich] using hpoint
    _ ≤ (localNegSobolevSq a T χ) ^ ((1 : ℝ) / 2) := by
      calc
        _ ≤ 1 * (localNegSobolevSq a T χ) ^ ((1 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right hroot (by positivity)
        _ = _ := by simp

/-- A uniform local-energy bound and pointwise Cauchy pairings yield a limiting functional in every strictly weaker negative Sobolev norm. -/
theorem exists_limit_distributionPairingFunctional_of_localEnergy
    {D : Set (Space 2)} (hD : IsDomain D) (χ : TestFn)
    (hχ : ∀ x ∈ D, χ x = 1) {s₀ s M : ℝ} (hM : 0 ≤ M) (h : s₀ < s)
    (T : ℕ → Distr)
    (henergy : ∀ n, localNegSobolevSq s₀ (T n) χ ≤ ENNReal.ofReal (M ^ 2))
    (hpair : ∀ φ (hφ : IsTestFn D φ), ∀ δ : ℝ, 0 < δ →
      ∃ K, ∀ n m, K ≤ n → K ≤ m →
        |T n (testFnOfRellich hφ.1 hφ.2.1) -
          T m (testFnOfRellich hφ.1 hφ.2.1)| ≤ δ) :
    ∃ G : (Space 2 → ℝ) → ℝ,
      (∀ φ ψ, IsTestFn D φ → IsTestFn D ψ → G (φ + ψ) = G φ + G ψ) ∧
      (∀ (c : ℝ) φ, IsTestFn D φ → G (fun x => c * φ x) = c * G φ) ∧
      negSobolevNorm 2 s₀ D G ≤ ENNReal.ofReal M ∧
      ∀ ε : ℝ, 0 < ε → ∃ K, ∀ n, K ≤ n →
        negSobolevNorm 2 s D (fun φ => distributionFunctional (T n) φ - G φ)
          ≤ ENNReal.ofReal ε := by
  have hbound : ∀ n,
      negSobolevNorm 2 s₀ D (distributionFunctional (T n)) ≤ ENNReal.ofReal M := by
    intro n
    calc
      negSobolevNorm 2 s₀ D (distributionFunctional (T n)) ≤
          (localNegSobolevSq s₀ (T n) χ) ^ ((1 : ℝ) / 2) :=
        distributionFunctional_negSobolevNorm_le_localEnergy (T n) χ s₀ hχ
      _ ≤ (ENNReal.ofReal (M ^ 2)) ^ ((1 : ℝ) / 2) :=
        ENNReal.rpow_le_rpow (henergy n) (by norm_num)
      _ = ENNReal.ofReal M := by
        rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg M) (by norm_num)]
        congr 1
        rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_of_nonneg hM]
  exact exists_limit_distribution_pairingFunctional_of_pointwise_cauchy
    hD h hM T hbound hpair

end Critical2DKPZ.Analysis.Sobolev.Rellich

end
