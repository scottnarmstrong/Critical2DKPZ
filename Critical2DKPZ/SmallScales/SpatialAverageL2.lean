/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Gaussian.Poincare
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Critical2DKPZ.JointConvergence.HeatStartLogFieldConvergence
public import Critical2DKPZ.Definitions.TestFn

/-! # Second moments of normalized spatial averages -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped CompactlySupported Distributions

namespace Critical2DKPZ.SmallScales

/-- A nonnegative unit-mass test average preserves a uniform pointwise second-moment bound. -/
theorem integral_test_second_moment_le_of_uniform_square
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {F : Plane × Ω → ℝ} (hF : AEMeasurable F (volume.prod P))
    (hFsec : ∀ x, AEStronglyMeasurable (fun ω => F (x, ω)) P)
    {M : ℝ} (hM : 0 ≤ M)
    (hSq : ∀ x, Integrable (fun ω => |F (x, ω)| ^ 2) P ∧
      ∫ ω, |F (x, ω)| ^ 2 ∂P ≤ M)
    (φ : TestFn) (hφ : ∀ x, 0 ≤ φ x) (hφ₁ : ∫ x, φ x = 1) :
    MemLp (fun ω => ∫ x, φ x * F (x, ω)) 2 P ∧
      ∫ ω, |∫ x, φ x * F (x, ω)| ^ 2 ∂P ≤ M := by
  classical
  let K : Set Plane := tsupport (φ : Plane → ℝ)
  have hKcompact : IsCompact K := φ.hasCompactSupport
  have hKmeas : MeasurableSet K := hKcompact.isClosed.measurableSet
  have hφzero (x : Plane) (hx : x ∉ K) : φ x = 0 := by
    by_contra hne
    have hxSupp : x ∈ Function.support (φ : Plane → ℝ) := by
      simpa [Function.mem_support] using hne
    exact hx (by simpa [K] using subset_tsupport (φ : Plane → ℝ) hxSupp)
  have hφint : Integrable (fun x : Plane => φ x) :=
    φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  let K2 : Set (Plane × Ω) := K ×ˢ Set.univ
  have hK2 : MeasurableSet K2 := hKmeas.prod MeasurableSet.univ
  let G : Plane × Ω → ℝ := K2.indicator (fun q => φ q.1 * |F q| ^ 2)
  have hFsq : AEMeasurable (fun q : Plane × Ω => |F q| ^ 2) (volume.prod P) :=
    ((continuous_abs.pow 2).measurable.comp_aemeasurable hF)
  have hGsm : AEStronglyMeasurable G (volume.prod P) := by
    dsimp [G]
    exact ((φ.continuous.measurable.comp measurable_fst).aestronglyMeasurable.mul
      hFsq.aestronglyMeasurable).indicator hK2
  have hGsec (x : Plane) : Integrable (fun ω => G (x, ω)) P := by
    by_cases hx : x ∈ K
    · simpa [G, K2, hx] using ((hSq x).1.const_mul (φ x))
    · simp [G, K2, hx]
  let H : Plane → ℝ := fun x => ∫ ω, ‖G (x, ω)‖ ∂P
  have hHmeas : AEMeasurable H volume := hGsm.norm.integral_prod_right'.aemeasurable
  have hHbound (x : Plane) : H x ≤ M * φ x := by
    by_cases hx : x ∈ K
    · have hEq : H x = φ x * ∫ ω, |F (x, ω)| ^ 2 ∂P := by
        simp [H, G, K2, hx, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (hφ x) (sq_nonneg _)), integral_const_mul]
      rw [hEq]
      calc
        φ x * ∫ ω, |F (x, ω)| ^ 2 ∂P ≤ φ x * M :=
          mul_le_mul_of_nonneg_left (hSq x).2 (hφ x)
        _ = M * φ x := by ring
    · have hzero : H x = 0 := by
        apply le_antisymm
        · simp [H, G, K2, hx]
        · exact integral_nonneg_of_ae
            (Filter.Eventually.of_forall fun ω => norm_nonneg (G (x, ω)))
      rw [hzero, hφzero x hx]
      simp
  have hMajor : Integrable (fun x : Plane => M * φ x) := hφint.const_mul M
  have hHint : Integrable H volume := by
    apply hMajor.mono' hHmeas.aestronglyMeasurable
    filter_upwards [] with x
    have hHnonneg : 0 ≤ H x := integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun ω => norm_nonneg (G (x, ω)))
    have hMφ : 0 ≤ M * φ x := mul_nonneg hM (hφ x)
    simpa [Real.norm_of_nonneg hHnonneg, Real.norm_of_nonneg hMφ] using hHbound x
  have hGint : Integrable G (volume.prod P) :=
    (integrable_prod_iff hGsm).2 ⟨Filter.Eventually.of_forall hGsec, hHint⟩
  have hGsecAE : ∀ᵐ ω ∂P, Integrable (fun x => G (x, ω)) volume :=
    hGint.prod_left_ae
  have hFsecAE : ∀ᵐ ω ∂P, AEStronglyMeasurable (fun x => F (x, ω)) volume :=
    hF.aestronglyMeasurable.prod_swap.prodMk_left
  have hProd : Integrable (fun q : Plane × Ω => φ q.1 * F q) (volume.prod P) :=
    Critical2DKPZ.JointConvergence.integrable_test_mul_joint P hF hFsec hM hSq φ
  have hProdSecAE : ∀ᵐ ω ∂P, Integrable (fun x => φ x * F (x, ω)) volume :=
    hProd.prod_left_ae
  let μK : Measure Plane := volume.restrict K
  let sqrtφ : Plane → ℝ := fun x => Real.sqrt (φ x)
  have hsqrtφCont : Continuous sqrtφ := Real.continuous_sqrt.comp φ.continuous
  have hsqrtφSqInt : Integrable (fun x : Plane => |sqrtφ x| ^ 2) μK := by
    have hφK : Integrable (fun x : Plane => φ x) μK := hφint.mono_measure Measure.restrict_le_self
    have heq : (fun x : Plane => |sqrtφ x| ^ 2) = fun x => φ x := by
      funext x
      simp [sqrtφ, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hφ x)]
    rw [heq]
    exact hφK
  have hsqrtφMemK : MemLp sqrtφ 2 μK := by
    apply (memLp_two_iff_integrable_sq hsqrtφCont.aestronglyMeasurable).2
    simpa [sq_abs] using hsqrtφSqInt
  have hYsqAE : ∀ᵐ ω ∂P,
      |∫ x, φ x * F (x, ω)| ^ 2 ≤ ∫ x, φ x * |F (x, ω)| ^ 2 ∂μK := by
    filter_upwards [hGsecAE, hFsecAE, hProdSecAE] with ω hGω hFω hProdω
    have hGω' : Integrable (K.indicator (fun x => φ x * |F (x, ω)| ^ 2)) volume := by
      convert hGω using 1
      ext x
      by_cases hx : x ∈ K <;> simp [G, K2, hx]
    have hFsqK : Integrable (fun x => φ x * |F (x, ω)| ^ 2) μK := by
      simpa only [μK, IntegrableOn] using (integrable_indicator_iff hKmeas).mp hGω'
    have hsqrtφmemK' : MemLp sqrtφ (ENNReal.ofReal (2 : ℝ)) μK := by
      simpa using hsqrtφMemK
    have hFmemK : MemLp (fun x : Plane => Real.sqrt (φ x) * F (x, ω)) 2 μK := by
      have hprodMeas : AEStronglyMeasurable
          (fun x : Plane => Real.sqrt (φ x) * F (x, ω)) μK :=
        hsqrtφCont.aestronglyMeasurable.mul
          (hFω.mono_measure Measure.restrict_le_self)
      have hprodSqAbs : Integrable
          (fun x : Plane => |Real.sqrt (φ x) * F (x, ω)| ^ 2) μK := by
        have hEq : (fun x : Plane => |Real.sqrt (φ x) * F (x, ω)| ^ 2) =
            fun x => φ x * |F (x, ω)| ^ 2 := by
          funext x
          calc
            |Real.sqrt (φ x) * F (x, ω)| ^ 2 =
                (Real.sqrt (φ x) * |F (x, ω)|) ^ 2 := by
                  simp [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
            _ = φ x * |F (x, ω)| ^ 2 := by
              rw [mul_pow, Real.sq_sqrt (hφ x)]
        rw [hEq]
        exact hFsqK
      apply (memLp_two_iff_integrable_sq hprodMeas).2
      have hprodSq : Integrable (fun x => (Real.sqrt (φ x) * F (x, ω)) ^ 2) μK := by
        simpa only [sq_abs] using hprodSqAbs
      exact hprodSq
    have hHolder : (2 : ℝ).HolderConjugate 2 := by
      rw [Real.holderConjugate_iff]
      norm_num
    have hCS := integral_mul_norm_le_Lp_mul_Lq (p := 2) (q := 2)
      hHolder hsqrtφmemK' (by simpa using hFmemK)
    have hset : (∫ x in K, φ x * F (x, ω) ∂volume) =
        ∫ x, φ x * F (x, ω) ∂volume :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        rw [hφzero x hx]
        simp
    have hCS' : |∫ x, φ x * F (x, ω) ∂volume| ≤
        (∫ x, |sqrtφ x| ^ 2 ∂μK) ^ (1 / 2 : ℝ) *
          (∫ x, |Real.sqrt (φ x) * F (x, ω)| ^ 2 ∂μK) ^ (1 / 2 : ℝ) := by
      rw [← hset]
      calc
        |∫ x in K, φ x * F (x, ω) ∂volume| ≤
            ∫ x in K, ‖φ x * F (x, ω)‖ ∂volume := abs_integral_le_integral_abs
        _ = ∫ x, ‖sqrtφ x‖ * ‖Real.sqrt (φ x) * F (x, ω)‖ ∂μK := by
          apply integral_congr_ae
          filter_upwards [] with x
          have hroot : Real.sqrt (φ x) * Real.sqrt (φ x) = φ x := by
            rw [← pow_two, Real.sq_sqrt (hφ x)]
          have hnormsqrt : ‖sqrtφ x‖ = Real.sqrt (φ x) := by
            simp [sqrtφ, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
          calc
            ‖φ x * F (x, ω)‖ = φ x * |F (x, ω)| := by
              simp [Real.norm_eq_abs, abs_of_nonneg (hφ x)]
            _ = Real.sqrt (φ x) * (Real.sqrt (φ x) * |F (x, ω)|) := by
              calc
                φ x * |F (x, ω)| =
                    (Real.sqrt (φ x) * Real.sqrt (φ x)) * |F (x, ω)| := by rw [hroot]
                _ = Real.sqrt (φ x) * (Real.sqrt (φ x) * |F (x, ω)|) := by ring
            _ = Real.sqrt (φ x) * |Real.sqrt (φ x) * F (x, ω)| := by
              rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
            _ = ‖sqrtφ x‖ * ‖Real.sqrt (φ x) * F (x, ω)‖ := by
              rw [hnormsqrt, Real.norm_eq_abs]
        _ ≤ _ := by
          simpa [Real.norm_eq_abs, Real.rpow_natCast] using hCS
    have hmass : ∫ x, |sqrtφ x| ^ 2 ∂μK = 1 := by
      calc
        ∫ x, |sqrtφ x| ^ 2 ∂μK = ∫ x, φ x ∂volume := by
          simp only [μK, ← integral_indicator hKmeas]
          apply integral_congr_ae
          filter_upwards [] with x
          by_cases hx : x ∈ K
          · simp [sqrtφ, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hφ x), hx]
          · simp [sqrtφ, hφzero x hx]
        _ = 1 := hφ₁
    have hrootmass : (∫ x, |sqrtφ x| ^ 2 ∂μK) ^ (1 / 2 : ℝ) = 1 := by
      rw [hmass]
      norm_num
    have hFsqmass : ∫ x, |Real.sqrt (φ x) * F (x, ω)| ^ 2 ∂μK =
        ∫ x, φ x * |F (x, ω)| ^ 2 ∂μK := by
      apply integral_congr_ae
      filter_upwards [] with x
      calc
        |Real.sqrt (φ x) * F (x, ω)| ^ 2 =
            (Real.sqrt (φ x) * |F (x, ω)|) ^ 2 := by
              simp [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        _ = φ x * |F (x, ω)| ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (hφ x)]
    have hbound : |∫ x, φ x * F (x, ω) ∂volume| ≤
        (∫ x, φ x * |F (x, ω)| ^ 2 ∂μK) ^ (1 / 2 : ℝ) := by
      rw [hrootmass, hFsqmass] at hCS'
      simpa using hCS'
    have hBnonneg : 0 ≤ ∫ x, φ x * |F (x, ω)| ^ 2 ∂μK :=
      integral_nonneg_of_ae (Filter.Eventually.of_forall fun x =>
        mul_nonneg (hφ x) (sq_nonneg _))
    have hnonneg : 0 ≤ (∫ x, φ x * |F (x, ω)| ^ 2 ∂μK) ^ (1 / 2 : ℝ) :=
      Real.rpow_nonneg hBnonneg _
    calc
      |∫ x, φ x * F (x, ω) ∂volume| ^ 2 ≤
          ((∫ x, φ x * |F (x, ω)| ^ 2 ∂μK) ^ (1 / 2 : ℝ)) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) hnonneg).2 hbound
      _ = ∫ x, φ x * |F (x, ω)| ^ 2 ∂μK := by
        rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hBnonneg]
  have hHomega : Integrable (fun ω => ∫ x, ‖G (x, ω)‖ ∂volume) P :=
    hGint.integral_norm_prod_right
  have hGintEq (ω : Ω) : (∫ x, ‖G (x, ω)‖ ∂volume) =
      ∫ x, φ x * |F (x, ω)| ^ 2 ∂μK := by
    have hpoint : (fun x : Plane => ‖G (x, ω)‖) =
        K.indicator (fun x => φ x * |F (x, ω)| ^ 2) := by
      funext x
      by_cases hx : x ∈ K
      · have hGval : G (x, ω) = φ x * |F (x, ω)| ^ 2 := by simp [G, K2, hx]
        calc
          ‖G (x, ω)‖ = ‖φ x * |F (x, ω)| ^ 2‖ := by rw [hGval]
          _ = φ x * |F (x, ω)| ^ 2 := by
            rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hφ x) (sq_nonneg _))]
          _ = K.indicator (fun x => φ x * |F (x, ω)| ^ 2) x := by simp [hx]
      · simp [G, K2, hx]
    rw [hpoint]
    simp only [μK]
    rw [← integral_indicator hKmeas]
  have hYsm : AEStronglyMeasurable (fun ω => ∫ x, φ x * F (x, ω)) P :=
    hProd.aestronglyMeasurable.prod_swap.integral_prod_right'
  have hYle : ∀ᵐ ω ∂P,
      |∫ x, φ x * F (x, ω)| ^ 2 ≤ ∫ x, ‖G (x, ω)‖ ∂volume := by
    filter_upwards [hYsqAE] with ω hω
    exact hω.trans_eq (hGintEq ω).symm
  have hYsqInt : Integrable (fun ω => |∫ x, φ x * F (x, ω)| ^ 2) P := by
    have hYmajor : Integrable (fun ω => ∫ x, ‖G (x, ω)‖ ∂volume) P := hHomega
    have hYsqMeas : AEStronglyMeasurable
        (fun ω => |∫ x, φ x * F (x, ω)| ^ 2) P :=
      ((continuous_abs.pow 2).measurable.comp_aemeasurable hYsm.aemeasurable).aestronglyMeasurable
    apply hYmajor.mono' hYsqMeas
    filter_upwards [hYle] with ω hω
    calc
      ‖|∫ x, φ x * F (x, ω)| ^ 2‖ = |∫ x, φ x * F (x, ω)| ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      _ ≤ ∫ x, ‖G (x, ω)‖ ∂volume := hω
  have hYmem : MemLp (fun ω => ∫ x, φ x * F (x, ω)) 2 P := by
    apply (memLp_two_iff_integrable_sq hYsm).2
    simpa [sq_abs] using hYsqInt
  have hFinal : ∫ ω, |∫ x, φ x * F (x, ω)| ^ 2 ∂P ≤ M := by
    calc
      ∫ ω, |∫ x, φ x * F (x, ω)| ^ 2 ∂P ≤
          ∫ ω, (∫ x, ‖G (x, ω)‖ ∂volume) ∂P :=
        integral_mono_ae hYsqInt hHomega hYle
      _ = ∫ x, H x ∂volume := by
        calc
          (∫ ω, ∫ x, ‖G (x, ω)‖ ∂volume ∂P) =
              ∫ q, ‖G q‖ ∂(volume.prod P) :=
            (integral_prod_symm (fun q => ‖G q‖) hGint.norm).symm
          _ = ∫ x, H x ∂volume := by
            rw [integral_prod (fun q => ‖G q‖) hGint.norm]
      _ ≤ ∫ x, M * φ x ∂volume := integral_mono hHint hMajor hHbound
      _ = M := by rw [integral_const_mul, hφ₁, mul_one]
  exact ⟨hYmem, hFinal⟩

end Critical2DKPZ.SmallScales

end
