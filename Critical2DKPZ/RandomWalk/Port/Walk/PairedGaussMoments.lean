/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
module

public import Mathlib
public import Critical2DKPZ.RandomWalk.Port.Walk.PairedFourier

/-!
# Gaussian integrals on `ℝ^d` for the local limit theorem

The Gaussian integral `∫_{ℝ^d} e^{-b|θ|²} = (π/b)^{d/2}` as a product of one-dimensional
ones, the second and fourth moments `∫ |θ|^{2m} e^{-a|θ|²} ≤ K a^{-(d+2m)/2}` by domination
with a Gaussian of half the rate, and the tail
`∫_{θ ∉ G} e^{-n|θ|²/(2d)} = O(n^{-(d+2)/2})` off the Gaussian region
`G = {θ : |θᵢ| ≤ π/2}`, where `|θ|² ≥ π²/4`.
-/

@[expose] public section

open MeasureTheory Filter Topology

noncomputable section

namespace LatticeProb.LocalCLT

open ContinuousTime

variable {d : ℕ}

/-- The sum in the Gaussian exponent is rewritten as a product of coordinate exponentials. -/
private lemma exp_neg_mul_sum_sq_eq_prod {b : ℝ} (θ : Fin d → ℝ) :
    Real.exp (-b * ∑ i, θ i ^ 2) = ∏ i, Real.exp (-b * θ i ^ 2) := by
  rw [Finset.mul_sum, Real.exp_sum]

/-- The Gaussian `e^{-b|θ|²}` is integrable on `ℝ^d` for `b > 0`. -/
theorem integrable_exp_neg_mul_sum_sq {b : ℝ} (hb : 0 < b) :
    Integrable fun θ : Fin d → ℝ => Real.exp (-b * ∑ i, θ i ^ 2) := by
  have hprod : Integrable (fun θ : Fin d → ℝ => ∏ i, Real.exp (-b * θ i ^ 2)) := by
    rw [MeasureTheory.volume_pi]
    exact Integrable.fintype_prod (fun i => integrable_exp_neg_mul_sq hb)
  exact hprod.congr (Filter.Eventually.of_forall fun θ => (exp_neg_mul_sum_sq_eq_prod θ).symm)

/-- For positive `b`, the Gaussian integral on `ℝ^d` equals `(π/b)^{d/2}`. -/
theorem integral_exp_neg_mul_sum_sq (b : ℝ) :
    ∫ θ : Fin d → ℝ, Real.exp (-b * ∑ i, θ i ^ 2) = Real.sqrt (Real.pi / b) ^ d := by
  calc ∫ θ : Fin d → ℝ, Real.exp (-b * ∑ i, θ i ^ 2)
      = ∫ θ : Fin d → ℝ, ∏ i, Real.exp (-b * θ i ^ 2) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
        exact exp_neg_mul_sum_sq_eq_prod θ
    _ = (∫ x : ℝ, Real.exp (-b * x ^ 2)) ^ d := by
        rw [MeasureTheory.integral_fintype_prod_volume_eq_pow
          (f := fun x : ℝ => Real.exp (-b * x ^ 2)), Fintype.card_fin]
    _ = Real.sqrt (Real.pi / b) ^ d := by rw [integral_gaussian]

/-- Pointwise bound `S e^{-aS} ≤ 2 a⁻¹ e^{-(a/2)S}`. -/
private lemma mul_exp_neg_le (a S : ℝ) (ha : 0 < a) :
    S * Real.exp (-a * S) ≤ (2 * a⁻¹) * Real.exp (-(a / 2) * S) := by
  have h1 : a * S ≤ 2 * Real.exp ((a * S) / 2) := by
    have h := Real.add_one_le_exp ((a * S) / 2)
    nlinarith [h]
  have h2 : (a * S) * Real.exp (-(a * S) / 2) ≤ 2 := by
    calc
      (a * S) * Real.exp (-(a * S) / 2)
          ≤ (2 * Real.exp ((a * S) / 2)) * Real.exp (-(a * S) / 2) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
      _ = 2 * (Real.exp ((a * S) / 2) * Real.exp (-(a * S) / 2)) := by ring
      _ = 2 * Real.exp ((a * S) / 2 + -(a * S) / 2) := by rw [← Real.exp_add]
      _ = 2 := by
            rw [show (a * S) / 2 + -(a * S) / 2 = 0 by ring, Real.exp_zero, mul_one]
  have h3 : S * Real.exp (-(a * S) / 2) ≤ 2 * a⁻¹ := by
    calc
      S * Real.exp (-(a * S) / 2) = a⁻¹ * ((a * S) * Real.exp (-(a * S) / 2)) := by
            field_simp
      _ ≤ a⁻¹ * 2 := mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr ha.le)
      _ = 2 * a⁻¹ := by ring
  calc
    S * Real.exp (-a * S) = (S * Real.exp (-(a * S) / 2)) * Real.exp (-(a / 2) * S) := by
          rw [mul_assoc, ← Real.exp_add, show -(a * S) / 2 + -(a / 2) * S = -a * S by ring]
    _ ≤ (2 * a⁻¹) * Real.exp (-(a / 2) * S) :=
          mul_le_mul_of_nonneg_right h3 (Real.exp_nonneg _)

/-- Pointwise bound `S² e^{-aS} ≤ 8 a⁻² e^{-(a/2)S}` for `S ≥ 0`. -/
private lemma sq_sq_exp_neg_le (a S : ℝ) (ha : 0 < a) (hS : 0 ≤ S) :
    S ^ 2 * Real.exp (-a * S) ≤ (8 * a⁻¹ ^ 2) * Real.exp (-(a / 2) * S) := by
  have h1 : (a * S) ^ 2 ≤ 8 * Real.exp ((a * S) / 2) := by
    have h := Real.quadratic_le_exp_of_nonneg (show 0 ≤ (a * S) / 2 by positivity)
    nlinarith [h]
  have h2 : (a * S) ^ 2 * Real.exp (-(a * S) / 2) ≤ 8 := by
    calc
      (a * S) ^ 2 * Real.exp (-(a * S) / 2)
          ≤ (8 * Real.exp ((a * S) / 2)) * Real.exp (-(a * S) / 2) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
      _ = 8 * (Real.exp ((a * S) / 2) * Real.exp (-(a * S) / 2)) := by ring
      _ = 8 * Real.exp ((a * S) / 2 + -(a * S) / 2) := by rw [← Real.exp_add]
      _ = 8 := by
            rw [show (a * S) / 2 + -(a * S) / 2 = 0 by ring, Real.exp_zero, mul_one]
  have h3 : S ^ 2 * Real.exp (-(a * S) / 2) ≤ 8 * a⁻¹ ^ 2 := by
    calc
      S ^ 2 * Real.exp (-(a * S) / 2)
          = a⁻¹ ^ 2 * ((a * S) ^ 2 * Real.exp (-(a * S) / 2)) := by
            field_simp
      _ ≤ a⁻¹ ^ 2 * 8 := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = 8 * a⁻¹ ^ 2 := by ring
  calc
    S ^ 2 * Real.exp (-a * S)
        = (S ^ 2 * Real.exp (-(a * S) / 2)) * Real.exp (-(a / 2) * S) := by
          rw [mul_assoc, ← Real.exp_add, show -(a * S) / 2 + -(a / 2) * S = -a * S by ring]
    _ ≤ (8 * a⁻¹ ^ 2) * Real.exp (-(a / 2) * S) :=
          mul_le_mul_of_nonneg_right h3 (Real.exp_nonneg _)

/-- Rewrites `√(π/(a/2))^d` as `(2π)^{d/2} a^{-d/2}`. -/
private lemma sqrt_pi_div_half_pow (a : ℝ) (ha : 0 < a) (d : ℕ) :
    Real.sqrt (Real.pi / (a / 2)) ^ d
      = (2 * Real.pi) ^ ((d : ℝ) / 2) * a ^ (-(d : ℝ) / 2) := by
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hbase : (0 : ℝ) ≤ 2 * Real.pi / a := div_nonneg h2pi.le ha.le
  rw [show Real.pi / (a / 2) = 2 * Real.pi / a by field_simp]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((2 * Real.pi / a) ^ (1 / 2 : ℝ)) d,
    ← Real.rpow_mul hbase (1 / 2 : ℝ) (d : ℝ)]
  rw [show (1 / 2 : ℝ) * (d : ℝ) = (d : ℝ) / 2 by ring]
  rw [Real.div_rpow h2pi.le ha.le, div_eq_mul_inv, ← Real.rpow_neg ha.le]
  rw [show -((d : ℝ) / 2) = -(d : ℝ) / 2 by ring]

/-- Combines the prefactor with the Gaussian integral value for the first moment. -/
private lemma gauss_first_bound (a : ℝ) (ha : 0 < a) (d : ℕ) :
    (2 * a⁻¹) * Real.sqrt (Real.pi / (a / 2)) ^ d
      = (2 * (2 * Real.pi) ^ ((d : ℝ) / 2)) * a ^ (-((d : ℝ) + 2) / 2) := by
  rw [sqrt_pi_div_half_pow a ha d, ← Real.rpow_neg_one a]
  rw [show (2 * a ^ (-1 : ℝ)) * ((2 * Real.pi) ^ ((d : ℝ) / 2) * a ^ (-(d : ℝ) / 2))
      = 2 * (2 * Real.pi) ^ ((d : ℝ) / 2) * (a ^ (-1 : ℝ) * a ^ (-(d : ℝ) / 2)) by ring]
  rw [← Real.rpow_add ha]
  rw [show -1 + -(d : ℝ) / 2 = -((d : ℝ) + 2) / 2 by ring]

/-- Combines the prefactor with the Gaussian integral value for the second moment. -/
private lemma gauss_second_bound (a : ℝ) (ha : 0 < a) (d : ℕ) :
    (8 * a⁻¹ ^ 2) * Real.sqrt (Real.pi / (a / 2)) ^ d
      = (8 * (2 * Real.pi) ^ ((d : ℝ) / 2)) * a ^ (-((d : ℝ) + 4) / 2) := by
  rw [sqrt_pi_div_half_pow a ha d]
  rw [show (8 * a⁻¹ ^ 2) * ((2 * Real.pi) ^ ((d : ℝ) / 2) * a ^ (-(d : ℝ) / 2))
      = 8 * (2 * Real.pi) ^ ((d : ℝ) / 2) * ((a⁻¹) ^ 2 * a ^ (-(d : ℝ) / 2)) by ring]
  rw [show (a⁻¹ : ℝ) ^ 2 = a ^ (-2 : ℝ) by
        rw [inv_pow, ← Real.rpow_natCast a 2, ← Real.rpow_neg ha.le]
        norm_num]
  rw [← Real.rpow_add ha]
  rw [show -2 + -(d : ℝ) / 2 = -((d : ℝ) + 4) / 2 by ring]

/-- The second moment of the Gaussian: `∫ |θ|² e^{-a|θ|²} ≤ K a^{-(d+2)/2}`. -/
theorem exists_integral_sq_mul_gauss_le (d : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ a : ℝ, 0 < a →
      Integrable (fun θ : Fin d → ℝ => (∑ i, θ i ^ 2) * Real.exp (-a * ∑ i, θ i ^ 2)) ∧
      ∫ θ : Fin d → ℝ, (∑ i, θ i ^ 2) * Real.exp (-a * ∑ i, θ i ^ 2)
        ≤ K * a ^ (-((d : ℝ) + 2) / 2) := by
  refine ⟨2 * (2 * Real.pi) ^ ((d : ℝ) / 2), by positivity, ?_⟩
  intro a ha
  have ha2 : 0 < a / 2 := by positivity
  have hInt_g : Integrable fun θ : Fin d → ℝ => Real.exp (-(a / 2) * ∑ i, θ i ^ 2) :=
    integrable_exp_neg_mul_sum_sq ha2
  have hbound : Integrable fun θ : Fin d → ℝ =>
      (2 * a⁻¹) * Real.exp (-(a / 2) * ∑ i, θ i ^ 2) := hInt_g.const_mul (2 * a⁻¹)
  have hf_meas : AEStronglyMeasurable
      (fun θ : Fin d → ℝ => (∑ i, θ i ^ 2) * Real.exp (-a * ∑ i, θ i ^ 2)) volume :=
    (by fun_prop : Continuous (fun θ : Fin d → ℝ =>
      (∑ i, θ i ^ 2) * Real.exp (-a * ∑ i, θ i ^ 2))).aestronglyMeasurable
  have hpt : ∀ θ : Fin d → ℝ,
      ‖(∑ i, θ i ^ 2) * Real.exp (-a * ∑ i, θ i ^ 2)‖
        ≤ (2 * a⁻¹) * Real.exp (-(a / 2) * ∑ i, θ i ^ 2) := by
    intro θ
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _))
        (Real.exp_nonneg _))]
    exact mul_exp_neg_le a (∑ i, θ i ^ 2) ha
  have hf : Integrable (fun θ : Fin d → ℝ =>
      (∑ i, θ i ^ 2) * Real.exp (-a * ∑ i, θ i ^ 2)) :=
    Integrable.mono' hbound hf_meas (Filter.Eventually.of_forall hpt)
  refine ⟨hf, ?_⟩
  have hle : ∫ θ : Fin d → ℝ, (∑ i, θ i ^ 2) * Real.exp (-a * ∑ i, θ i ^ 2)
      ≤ ∫ θ : Fin d → ℝ, (2 * a⁻¹) * Real.exp (-(a / 2) * ∑ i, θ i ^ 2) :=
    integral_mono hf hbound (fun θ => mul_exp_neg_le a (∑ i, θ i ^ 2) ha)
  rw [integral_const_mul, integral_exp_neg_mul_sum_sq] at hle
  calc
    ∫ θ : Fin d → ℝ, (∑ i, θ i ^ 2) * Real.exp (-a * ∑ i, θ i ^ 2)
        ≤ (2 * a⁻¹) * Real.sqrt (Real.pi / (a / 2)) ^ d := hle
    _ = (2 * (2 * Real.pi) ^ ((d : ℝ) / 2)) * a ^ (-((d : ℝ) + 2) / 2) :=
          gauss_first_bound a ha d

/-- The fourth moment of the Gaussian: `∫ |θ|⁴ e^{-a|θ|²} ≤ K a^{-(d+4)/2}`. -/
theorem exists_integral_sq_sq_mul_gauss_le (d : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ a : ℝ, 0 < a →
      Integrable (fun θ : Fin d → ℝ =>
        (∑ i, θ i ^ 2) ^ 2 * Real.exp (-a * ∑ i, θ i ^ 2)) ∧
      ∫ θ : Fin d → ℝ, (∑ i, θ i ^ 2) ^ 2 * Real.exp (-a * ∑ i, θ i ^ 2)
        ≤ K * a ^ (-((d : ℝ) + 4) / 2) := by
  refine ⟨8 * (2 * Real.pi) ^ ((d : ℝ) / 2), by positivity, ?_⟩
  intro a ha
  have ha2 : 0 < a / 2 := by positivity
  have hInt_g : Integrable fun θ : Fin d → ℝ => Real.exp (-(a / 2) * ∑ i, θ i ^ 2) :=
    integrable_exp_neg_mul_sum_sq ha2
  have hbound : Integrable fun θ : Fin d → ℝ =>
      (8 * a⁻¹ ^ 2) * Real.exp (-(a / 2) * ∑ i, θ i ^ 2) := hInt_g.const_mul (8 * a⁻¹ ^ 2)
  have hf_meas : AEStronglyMeasurable
      (fun θ : Fin d → ℝ => (∑ i, θ i ^ 2) ^ 2 * Real.exp (-a * ∑ i, θ i ^ 2)) volume :=
    (by fun_prop : Continuous (fun θ : Fin d → ℝ =>
      (∑ i, θ i ^ 2) ^ 2 * Real.exp (-a * ∑ i, θ i ^ 2))).aestronglyMeasurable
  have hpt : ∀ θ : Fin d → ℝ,
      ‖(∑ i, θ i ^ 2) ^ 2 * Real.exp (-a * ∑ i, θ i ^ 2)‖
        ≤ (8 * a⁻¹ ^ 2) * Real.exp (-(a / 2) * ∑ i, θ i ^ 2) := by
    intro θ
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_nonneg _))]
    exact sq_sq_exp_neg_le a (∑ i, θ i ^ 2) ha
      (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  have hf : Integrable (fun θ : Fin d → ℝ =>
      (∑ i, θ i ^ 2) ^ 2 * Real.exp (-a * ∑ i, θ i ^ 2)) :=
    Integrable.mono' hbound hf_meas (Filter.Eventually.of_forall hpt)
  refine ⟨hf, ?_⟩
  have hle : ∫ θ : Fin d → ℝ, (∑ i, θ i ^ 2) ^ 2 * Real.exp (-a * ∑ i, θ i ^ 2)
      ≤ ∫ θ : Fin d → ℝ, (8 * a⁻¹ ^ 2) * Real.exp (-(a / 2) * ∑ i, θ i ^ 2) :=
    integral_mono hf hbound (fun θ => sq_sq_exp_neg_le a (∑ i, θ i ^ 2) ha
      (Finset.sum_nonneg (fun i _ => sq_nonneg _)))
  rw [integral_const_mul, integral_exp_neg_mul_sum_sq] at hle
  calc
    ∫ θ : Fin d → ℝ, (∑ i, θ i ^ 2) ^ 2 * Real.exp (-a * ∑ i, θ i ^ 2)
        ≤ (8 * a⁻¹ ^ 2) * Real.sqrt (Real.pi / (a / 2)) ^ d := hle
    _ = (8 * (2 * Real.pi) ^ ((d : ℝ) / 2)) * a ^ (-((d : ℝ) + 4) / 2) :=
          gauss_second_bound a ha d

/-- Off the Gaussian region the Gaussian weight is bounded by an exponentially small
constant times a Gaussian. -/
private lemma exp_le_exp_compl_gaussRegion {d : ℕ} {n : ℕ} {θ : Fin d → ℝ}
    (hθ : θ ∈ (gaussRegion d)ᶜ) :
    Real.exp (-(n : ℝ) * (∑ i, θ i ^ 2) / (2 * d))
      ≤ Real.exp (-(n : ℝ) * Real.pi ^ 2 / (16 * d))
        * Real.exp (-((n : ℝ) / (4 * d)) * ∑ i, θ i ^ 2) := by
  rw [Set.mem_compl_iff, gaussRegion, Set.mem_ofPred_eq, Classical.not_forall] at hθ
  obtain ⟨i, hi⟩ := hθ
  have hpi : Real.pi / 2 < |θ i| := lt_of_not_ge hi
  have hsq : Real.pi ^ 2 / 4 ≤ θ i ^ 2 := by
    rw [← sq_abs (θ i)]
    nlinarith [hpi, Real.pi_pos]
  have hS : Real.pi ^ 2 / 4 ≤ ∑ j, θ j ^ 2 :=
    hsq.trans (Finset.single_le_sum (fun j _ => sq_nonneg (θ j)) (Finset.mem_univ i))
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hfac : 0 ≤ (n : ℝ) / (4 * d) * (∑ j, θ j ^ 2 - Real.pi ^ 2 / 4) :=
    mul_nonneg (div_nonneg (Nat.cast_nonneg n) (by positivity)) (by linarith)
  have hkey : -↑n * Real.pi ^ 2 / (16 * ↑d) + -(↑n / (4 * ↑d)) * (∑ j, θ j ^ 2)
      = (-↑n * (∑ j, θ j ^ 2)) / (2 * ↑d)
        + (↑n / (4 * ↑d)) * ((∑ j, θ j ^ 2) - Real.pi ^ 2 / 4) := by ring
  linarith [hfac, hkey]


/-- The Gaussian off the Gaussian region integrates to `O(n^{-(d+2)/2})`. -/
theorem exists_integral_compl_gaussRegion_le (hd : 1 ≤ d) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n →
      ∫ θ in (gaussRegion d)ᶜ, Real.exp (-(n : ℝ) * (∑ i, θ i ^ 2) / (2 * d))
        ≤ K * (n : ℝ) ^ (-((d : ℝ) + 2) / 2) := by
  have hdpos_nat : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hdpos_nat
  have hGmeas : MeasurableSet (gaussRegion d) := by
    have hset : gaussRegion d = ⋂ i : Fin d, {θ : Fin d → ℝ | |θ i| ≤ Real.pi / 2} := by
      ext θ
      simp [gaussRegion]
    rw [hset]
    exact (isClosed_iInter fun i =>
      isClosed_le (continuous_apply i |>.abs) continuous_const).measurableSet
  refine ⟨(16 * (d : ℝ) / Real.pi ^ 2) * (4 * Real.pi * (d : ℝ)) ^ ((d : ℝ) / 2),
    ?_, ?_⟩
  · have hc : 0 < 4 * Real.pi * (d : ℝ) :=
      mul_pos (mul_pos (by norm_num) Real.pi_pos) hdpos
    positivity
  · intro n hn
    have hnpos : (0 : ℝ) < n := by
      have : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
      exact_mod_cast this
    have hb : 0 < (n : ℝ) / (4 * (d : ℝ)) := div_pos hnpos (mul_pos (by norm_num) hdpos)
    have hb2 : 0 < (n : ℝ) / (2 * (d : ℝ)) := div_pos hnpos (mul_pos (by norm_num) hdpos)
    have hf_int : IntegrableOn
        (fun θ : Fin d → ℝ => Real.exp (-(n : ℝ) * (∑ i, θ i ^ 2) / (2 * (d : ℝ))))
        ((gaussRegion d)ᶜ) := by
      refine ((integrable_exp_neg_mul_sum_sq (d := d)
        (b := (n : ℝ) / (2 * (d : ℝ))) hb2).congr ?_).integrableOn
      filter_upwards with θ
      congr 1
      ring
    have hg_int : IntegrableOn
        (fun θ : Fin d → ℝ => Real.exp (-(n : ℝ) * Real.pi ^ 2 / (16 * (d : ℝ)))
          * Real.exp (-((n : ℝ) / (4 * (d : ℝ))) * (∑ i, θ i ^ 2)))
        ((gaussRegion d)ᶜ) :=
      ((integrable_exp_neg_mul_sum_sq (d := d)
        (b := (n : ℝ) / (4 * (d : ℝ))) hb).const_mul _).integrableOn
    have hmono : (∫ θ in (gaussRegion d)ᶜ,
          Real.exp (-(n : ℝ) * (∑ i, θ i ^ 2) / (2 * (d : ℝ))))
        ≤ ∫ θ in (gaussRegion d)ᶜ, Real.exp (-(n : ℝ) * Real.pi ^ 2 / (16 * (d : ℝ)))
            * Real.exp (-((n : ℝ) / (4 * (d : ℝ))) * (∑ i, θ i ^ 2)) :=
      setIntegral_mono_on hf_int hg_int hGmeas.compl
        (fun θ hθ => exp_le_exp_compl_gaussRegion hθ)
    have hexp : Real.exp (-(n : ℝ) * Real.pi ^ 2 / (16 * (d : ℝ)))
        ≤ 16 * (d : ℝ) / (Real.pi ^ 2 * n) := by
      have hx : 0 < (n : ℝ) * Real.pi ^ 2 / (16 * (d : ℝ)) := by
        apply div_pos
        · exact mul_pos hnpos (pow_pos Real.pi_pos 2)
        · exact mul_pos (by norm_num) hdpos
      have hx' : -(n : ℝ) * Real.pi ^ 2 / (16 * (d : ℝ))
          = -((n : ℝ) * Real.pi ^ 2 / (16 * (d : ℝ))) := by ring
      rw [hx', Real.exp_neg]
      calc (Real.exp ((n : ℝ) * Real.pi ^ 2 / (16 * (d : ℝ))))⁻¹
          ≤ ((n : ℝ) * Real.pi ^ 2 / (16 * (d : ℝ)))⁻¹ :=
            (inv_le_inv₀ (Real.exp_pos _) hx).mpr
              (by linarith [Real.add_one_le_exp ((n : ℝ) * Real.pi ^ 2 / (16 * (d : ℝ)))])
        _ = 16 * (d : ℝ) / (Real.pi ^ 2 * n) := by field_simp
    have halgebra : (16 * (d : ℝ) / (Real.pi ^ 2 * n))
          * (Real.sqrt (4 * Real.pi * (d : ℝ) / n)) ^ d
        = ((16 * (d : ℝ) / Real.pi ^ 2) * (4 * Real.pi * (d : ℝ)) ^ ((d : ℝ) / 2))
          * n ^ (-((d : ℝ) + 2) / 2) := by
      have hc : 0 < 4 * Real.pi * (d : ℝ) :=
        mul_pos (mul_pos (by norm_num) Real.pi_pos) hdpos
      have hsqrt : (Real.sqrt (4 * Real.pi * (d : ℝ) / n)) ^ d
          = (4 * Real.pi * (d : ℝ)) ^ ((d : ℝ) / 2) * n ^ (-((d : ℝ) / 2)) := by
        rw [Real.sqrt_eq_rpow]
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul (by positivity : 0 ≤ 4 * Real.pi * (d : ℝ) / n)]
        rw [show (1 / 2 : ℝ) * (d : ℝ) = (d : ℝ) / 2 by ring]
        rw [Real.div_rpow hc.le hnpos.le]
        rw [div_eq_mul_inv, ← Real.rpow_neg hnpos.le]
      have h_one : 16 * (d : ℝ) / (Real.pi ^ 2 * n)
          = (16 * (d : ℝ) / Real.pi ^ 2) * n ^ (-1 : ℝ) := by
        rw [Real.rpow_neg_one]
        field_simp
      rw [h_one, hsqrt]
      rw [show (16 * (d : ℝ) / Real.pi ^ 2) * n ^ (-1 : ℝ)
            * ((4 * Real.pi * (d : ℝ)) ^ ((d : ℝ) / 2) * n ^ (-((d : ℝ) / 2)))
          = (16 * (d : ℝ) / Real.pi ^ 2) * (4 * Real.pi * (d : ℝ)) ^ ((d : ℝ) / 2)
            * (n ^ (-1 : ℝ) * n ^ (-((d : ℝ) / 2))) by ring]
      rw [← Real.rpow_add hnpos (-1) (-((d : ℝ) / 2))]
      rw [show (-1 : ℝ) + -((d : ℝ) / 2) = -((d : ℝ) + 2) / 2 by ring]
    calc (∫ θ in (gaussRegion d)ᶜ,
            Real.exp (-(n : ℝ) * (∑ i, θ i ^ 2) / (2 * (d : ℝ))))
        ≤ ∫ θ in (gaussRegion d)ᶜ, Real.exp (-(n : ℝ) * Real.pi ^ 2 / (16 * (d : ℝ)))
            * Real.exp (-((n : ℝ) / (4 * (d : ℝ))) * (∑ i, θ i ^ 2)) := hmono
      _ = Real.exp (-(n : ℝ) * Real.pi ^ 2 / (16 * (d : ℝ)))
            * ∫ θ in (gaussRegion d)ᶜ,
                Real.exp (-((n : ℝ) / (4 * (d : ℝ))) * (∑ i, θ i ^ 2)) := by
            rw [integral_const_mul]
      _ ≤ Real.exp (-(n : ℝ) * Real.pi ^ 2 / (16 * (d : ℝ)))
            * ∫ θ : Fin d → ℝ,
                Real.exp (-((n : ℝ) / (4 * (d : ℝ))) * (∑ i, θ i ^ 2)) := by
            exact mul_le_mul_of_nonneg_left
              (setIntegral_le_integral
                (integrable_exp_neg_mul_sum_sq (d := d)
                  (b := (n : ℝ) / (4 * (d : ℝ))) hb)
                (Filter.Eventually.of_forall fun θ => Real.exp_nonneg _))
              (Real.exp_nonneg _)
      _ = Real.exp (-(n : ℝ) * Real.pi ^ 2 / (16 * (d : ℝ)))
            * (Real.sqrt (Real.pi / ((n : ℝ) / (4 * (d : ℝ))))) ^ d := by
            rw [integral_exp_neg_mul_sum_sq]
      _ = Real.exp (-(n : ℝ) * Real.pi ^ 2 / (16 * (d : ℝ)))
            * (Real.sqrt (4 * Real.pi * (d : ℝ) / n)) ^ d := by
            rw [show Real.pi / ((n : ℝ) / (4 * (d : ℝ))) = 4 * Real.pi * (d : ℝ) / n by
              field_simp]
      _ ≤ (16 * (d : ℝ) / (Real.pi ^ 2 * n))
            * (Real.sqrt (4 * Real.pi * (d : ℝ) / n)) ^ d := by
            exact mul_le_mul_of_nonneg_right hexp (by positivity)
      _ = ((16 * (d : ℝ) / Real.pi ^ 2) * (4 * Real.pi * (d : ℝ)) ^ ((d : ℝ) / 2))
            * n ^ (-((d : ℝ) + 2) / 2) := halgebra

end LatticeProb.LocalCLT

end
