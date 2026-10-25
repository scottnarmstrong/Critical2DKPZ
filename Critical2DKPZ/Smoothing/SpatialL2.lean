/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Smoothing.LocalErrorBounds
public import Critical2DKPZ.Smoothing.ProfileL2Perturbation
import Mathlib.Tactic

/-! # Spatial integration of uniformly square-integrable fields -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.Smoothing

/-- An `L²` seminorm bound implies an integrable square and the corresponding second-moment
integral bound. -/
theorem integral_sq_le_of_eLpNorm_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {F : Ω → ℝ} (hF : MemLp F 2 μ)
    (R : ℝ) (hR : 0 ≤ R)
    (hbound : eLpNorm F 2 μ ≤ ENNReal.ofReal R) :
    Integrable (fun ω => F ω ^ 2) μ ∧ (∫ ω, F ω ^ 2 ∂μ) ≤ R ^ 2 := by
  have hsqInt : Integrable (fun ω => F ω ^ 2) μ := by
    have h := hF.integrable_norm_pow'
    simpa only [Real.norm_eq_abs, sq_abs] using h
  have hnormPow :
      (∫ ω, ‖F ω‖ ^ ENNReal.toReal (2 : ℝ≥0∞) ∂μ) ^
          (ENNReal.toReal (2 : ℝ≥0∞))⁻¹ = (eLpNorm F 2 μ).toReal := by
    rw [hF.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    have hnonneg : 0 ≤
        (∫ ω, ‖F ω‖ ^ ENNReal.toReal (2 : ℝ≥0∞) ∂μ) ^
          (ENNReal.toReal (2 : ℝ≥0∞))⁻¹ := by positivity
    exact (ENNReal.toReal_ofReal hnonneg).symm
  have hsq :
      ∫ ω, ‖F ω‖ ^ ENNReal.toReal (2 : ℝ≥0∞) ∂μ = ∫ ω, F ω ^ 2 ∂μ := by
    simp [ENNReal.toReal_ofNat, Real.norm_eq_abs, sq_abs]
  have htoReal : (eLpNorm F 2 μ).toReal = Real.sqrt (∫ ω, F ω ^ 2 ∂μ) := by
    calc
      _ = (∫ ω, ‖F ω‖ ^ ENNReal.toReal (2 : ℝ≥0∞) ∂μ) ^
            (ENNReal.toReal (2 : ℝ≥0∞))⁻¹ := hnormPow.symm
      _ = Real.sqrt (∫ ω, F ω ^ 2 ∂μ) := by
        rw [hsq, Real.sqrt_eq_rpow]
        congr 1
        norm_num [ENNReal.toReal_ofNat]
  have hreal : (eLpNorm F 2 μ).toReal ≤ R := by
    calc
      _ ≤ (ENNReal.ofReal R).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
      _ = R := ENNReal.toReal_ofReal hR
  refine ⟨hsqInt, ?_⟩
  rw [htoReal] at hreal
  have hnonneg : 0 ≤ ∫ ω, F ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg (F ω)
  have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _) hR).2 hreal
  rw [Real.sq_sqrt hnonneg] at hsq
  exact hsq

/-- A spatial integral against an `L¹` weight is in `L²` when the field has a uniform second
moment. The product-field integrability needed for the second-moment calculation is included in
the hypotheses. -/
theorem eLpNorm_integral_mul_le_of_uniform_secondMoment
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    [IsProbabilityMeasure μ] {Z : Ω → Plane → ℝ} (φ : Plane → ℝ)
    (hφ : Measurable φ) (hφint : Integrable φ)
    (hZ : Measurable (fun p : Ω × Plane => Z p.1 p.2))
    (hZmem : ∀ x, MemLp (fun ω => Z ω x) 2 μ) (B : ℝ) (hB : 0 ≤ B)
    (hZsq : ∀ x, Integrable (fun ω => Z ω x ^ 2) μ ∧
      (∫ ω, Z ω x ^ 2 ∂μ) ≤ B) :
    Integrable (fun ω => ∫ x, φ x * Z ω x) μ ∧
    eLpNorm (fun ω => ∫ x, φ x * Z ω x) 2 μ ≤
      ENNReal.ofReal (Real.sqrt B * ∫ x, |φ x|) := by
  have hfield := weighted_field_integrability μ φ hφ hφint hZ hZmem B hB hZsq
  let F : Ω → Plane → ℝ := fun ω x => φ x * Z ω x
  have hFmeas : Measurable (fun p : Ω × Plane => F p.1 p.2) := by
    dsimp [F]
    exact (hφ.comp measurable_snd).mul hZ
  have hFstrong : StronglyMeasurable (fun p : Plane × Ω => F p.2 p.1) := by
    exact hFmeas.stronglyMeasurable.comp_measurable
      (show Measurable (fun p : Plane × Ω => (p.2, p.1)) by fun_prop)
  have hIntF : ∀ᵐ ω ∂μ, Integrable (F ω) volume := hfield.1
  have hProdF : Integrable (fun p : Ω × (Plane × Plane) =>
      F p.1 p.2.1 * F p.1 p.2.2) (μ.prod (volume.prod volume)) := by
    simpa [F] using hfield.2.1
  have hSqInt : Integrable (fun ω => (∫ x, F ω x) ^ 2) μ := hfield.2.2
  have hFmeas' : StronglyMeasurable (fun ω => ∫ x, F ω x ∂volume) :=
    hFstrong.integral_prod_left'
  have hFmem : MemLp (fun ω => ∫ x, F ω x ∂volume) 2 μ :=
    (memLp_two_iff_integrable_sq hFmeas'.aestronglyMeasurable).2 hSqInt
  have hFmoment : (∫ ω, (∫ x, F ω x ∂volume) ^ 2 ∂μ) ≤
      B * (∫ x, |φ x| ∂volume) ^ 2 := by
    have hswap := integral_integral_swap
      (f := fun (ω : Ω) (p : Plane × Plane) => F ω p.1 * F ω p.2) hProdF
    have hpoint : ∀ᵐ ω ∂μ,
        (∫ x, F ω x ∂volume) ^ 2 =
          ∫ p : Plane × Plane, F ω p.1 * F ω p.2 ∂(volume.prod volume) := by
      filter_upwards [hIntF] with ω hω
      rw [pow_two]
      exact (integral_prod_mul (μ := volume) (ν := volume) (F ω) (F ω)).symm
    have hfirst : (∫ ω, (∫ x, F ω x ∂volume) ^ 2 ∂μ) =
        ∫ ω, ∫ p : Plane × Plane, F ω p.1 * F ω p.2
          ∂(volume.prod volume) ∂μ := integral_congr_ae hpoint
    have hsecond : (∫ ω, ∫ p : Plane × Plane, F ω p.1 * F ω p.2
        ∂(volume.prod volume) ∂μ) =
        ∫ p : Plane × Plane, ∫ ω, F ω p.1 * F ω p.2 ∂μ
          ∂(volume.prod volume) := by
      simpa only [Pi.mul_apply] using hswap
    have hZprodInt (x y : Plane) :
        Integrable (fun ω => Z ω x * Z ω y) μ := by
      have hx := hZmem x
      have hy := hZmem y
      have hmul : MemLp (fun ω => Z ω x * Z ω y) 1 μ := hx.mul hy
      exact hmul.integrable (by norm_num)
    have hpointBound (p : Plane × Plane) :
        |∫ ω, F ω p.1 * F ω p.2 ∂μ| ≤
          |φ p.1| * |φ p.2| * B := by
      have hprodInt : Integrable (fun ω => F ω p.1 * F ω p.2) μ := by
        have h := (hZprodInt p.1 p.2).const_mul (φ p.1 * φ p.2)
        refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
        dsimp [F]
        ring
      have hhc : (2 : ℝ).HolderConjugate 2 := by
        rw [Real.holderConjugate_iff]
        norm_num
      have hmemx : MemLp (fun ω => Z ω p.1) (ENNReal.ofReal (2 : ℝ)) μ := by
        simpa using hZmem p.1
      have hmemy : MemLp (fun ω => Z ω p.2) (ENNReal.ofReal (2 : ℝ)) μ := by
        simpa using hZmem p.2
      have hholder := integral_mul_norm_le_Lp_mul_Lq
        hhc hmemx hmemy
      have hsqx : (∫ ω, ‖Z ω p.1‖ ^ (2 : ℝ) ∂μ) =
          ∫ ω, Z ω p.1 ^ 2 ∂μ := by
        simp [Real.norm_eq_abs, sq_abs]
      have hsqy : (∫ ω, ‖Z ω p.2‖ ^ (2 : ℝ) ∂μ) =
          ∫ ω, Z ω p.2 ^ 2 ∂μ := by
        simp [Real.norm_eq_abs, sq_abs]
      have hrootx :
          (∫ ω, ‖Z ω p.1‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) ≤ Real.sqrt B := by
        rw [hsqx, Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow (integral_nonneg fun ω => sq_nonneg (Z ω p.1))
          (hZsq p.1).2 (by norm_num)
      have hrooty :
          (∫ ω, ‖Z ω p.2‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) ≤ Real.sqrt B := by
        rw [hsqy, Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow (integral_nonneg fun ω => sq_nonneg (Z ω p.2))
          (hZsq p.2).2 (by norm_num)
      have hmulBound :
          ∫ ω, ‖Z ω p.1‖ * ‖Z ω p.2‖ ∂μ ≤ B := by
        calc
          _ ≤ (∫ ω, ‖Z ω p.1‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
              (∫ ω, ‖Z ω p.2‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := hholder
          _ ≤ Real.sqrt B * Real.sqrt B := mul_le_mul hrootx hrooty
              (by positivity) (Real.sqrt_nonneg _)
          _ = B := by rw [← pow_two, Real.sq_sqrt hB]
      calc
        _ = |∫ ω, φ p.1 * φ p.2 * (Z ω p.1 * Z ω p.2) ∂μ| := by
          congr 1
          apply integral_congr_ae
          filter_upwards [] with ω
          simp [F]
          ring
        _ ≤ ∫ ω, |φ p.1 * φ p.2 * (Z ω p.1 * Z ω p.2)| ∂μ :=
          abs_integral_le_integral_abs
        _ = |φ p.1| * |φ p.2| *
            (∫ ω, ‖Z ω p.1‖ * ‖Z ω p.2‖ ∂μ) := by
          calc
            _ = ∫ ω, (|φ p.1| * |φ p.2|) *
                (‖Z ω p.1‖ * ‖Z ω p.2‖) ∂μ := by
                  apply integral_congr_ae
                  exact Filter.Eventually.of_forall fun ω => by
                    simp only [abs_mul, Real.norm_eq_abs]
            _ = |φ p.1| * |φ p.2| *
                (∫ ω, ‖Z ω p.1‖ * ‖Z ω p.2‖ ∂μ) := by
                  rw [integral_const_mul]
        _ ≤ |φ p.1| * |φ p.2| * B := by
          exact mul_le_mul_of_nonneg_left hmulBound
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    let K : Plane × Plane → ℝ := fun p => |φ p.1| * |φ p.2| * B
    have hKint : Integrable K (volume.prod volume) := by
      have habs : Integrable (fun x : Plane => |φ x|) volume := by
        simpa only [Real.norm_eq_abs] using hφint.norm
      simpa [K, mul_assoc] using (habs.mul_prod habs).mul_const B
    have hcovInt : Integrable (fun p : Plane × Plane =>
        ∫ ω, F ω p.1 * F ω p.2 ∂μ) (volume.prod volume) := hProdF.integral_prod_right
    have hmain : (∫ ω, (∫ x, F ω x ∂volume) ^ 2 ∂μ) =
        ∫ p : Plane × Plane, ∫ ω, F ω p.1 * F ω p.2 ∂μ
          ∂(volume.prod volume) := by rw [hfirst, hsecond]
    calc
      _ = ∫ p : Plane × Plane, ∫ ω, F ω p.1 * F ω p.2 ∂μ
            ∂(volume.prod volume) := hmain
      _ ≤ ∫ p : Plane × Plane, K p ∂(volume.prod volume) :=
        integral_mono hcovInt hKint (fun p => by
          calc
            ∫ ω, F ω p.1 * F ω p.2 ∂μ ≤
                |∫ ω, F ω p.1 * F ω p.2 ∂μ| := le_abs_self _
            _ ≤ K p := by simpa [K] using hpointBound p)
      _ = B * (∫ x, |φ x| ∂volume) ^ 2 := by
        have habs : Integrable (fun x : Plane => |φ x|) volume := by
          simpa only [Real.norm_eq_abs] using hφint.norm
        calc
          _ = B * ∫ p : Plane × Plane, |φ p.1| * |φ p.2|
                ∂(volume.prod volume) := by
              calc
                _ = (∫ p : Plane × Plane, |φ p.1| * |φ p.2|
                      ∂(volume.prod volume)) * B := by
                    change (∫ p : Plane × Plane,
                      (|φ p.1| * |φ p.2|) * B ∂(volume.prod volume)) = _
                    rw [integral_mul_const]
                _ = _ := by ring
          _ = B * ((∫ x, |φ x| ∂volume) * ∫ x, |φ x| ∂volume) := by
              have hprodabs :
                  (∫ p : Plane × Plane, |φ p.1| * |φ p.2|
                    ∂(volume.prod volume)) =
                    (∫ x : Plane, |φ x| ∂volume) * ∫ x : Plane, |φ x| ∂volume := by
                exact integral_prod_mul (μ := volume) (ν := volume)
                  (fun x : Plane => |φ x|) (fun y : Plane => |φ y|)
              rw [hprodabs]
          _ = _ := by ring
  have hnonneg : 0 ≤ ∫ x, |φ x| ∂volume := integral_nonneg fun x => abs_nonneg _
  refine ⟨hFmem.integrable (by norm_num), ?_⟩
  have hnorm := eLpNorm_le_of_integral_sq_le μ hFmem hFmoment
  simpa [F, Real.sqrt_mul hB, Real.sqrt_sq_eq_abs, abs_of_nonneg hnonneg] using hnorm

end Critical2DKPZ.Smoothing

end
