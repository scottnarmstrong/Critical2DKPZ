/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.SupTimeKernel
public import Critical2DKPZ.SHF.DeltaBose.ConfigurationWeight
public import Critical2DKPZ.SHF.DeltaBose.FormBounds
public import Critical2DKPZ.SHF.DeltaBose.SchurTest
public import Critical2DKPZ.SHF.DeltaBose.ScalarEnvelope
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Tactic

/-! # Uniform form bounds for pointwise block suprema -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- The one-dimensional exponential tail has finite mass. -/
theorem integrable_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ => Real.exp (-a * |x|)) := by
  have hpos : IntegrableOn (fun x : ℝ => Real.exp (-a * x)) (Set.Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hneg : IntegrableOn (fun x : ℝ => Real.exp (a * x)) (Set.Iic 0) :=
    integrableOn_exp_mul_Iic ha 0
  have hpos' : IntegrableOn (fun x : ℝ => Real.exp (-a * |x|)) (Set.Ioi 0) := by
    apply hpos.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [abs_of_nonneg (le_of_lt hx)]
  have hneg' : IntegrableOn (fun x : ℝ => Real.exp (-a * |x|)) (Set.Iic 0) := by
    apply hneg.congr
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
    rw [abs_of_nonpos hx]
    congr 1
    ring
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi]
  exact integrableOn_union.mpr ⟨hneg', hpos'⟩

/-- The integral of the one-dimensional exponential tail. -/
theorem integral_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ, Real.exp (-a * |x|)) = 2 / a := by
  calc (∫ x : ℝ, Real.exp (-a * |x|))
      = 2 * ∫ x : ℝ in Set.Ioi 0, Real.exp (-a * x) := by
          simpa only [Function.comp_apply] using
            (integral_comp_abs (f := fun x : ℝ => Real.exp (-a * x)))
    _ = 2 / a := by
          rw [_root_.integral_exp_mul_Ioi (a := -a) (by linarith) 0]
          simp [div_eq_mul_inv]

/-- Integrability of the planar exponential tail in the coordinate one-norm. -/
theorem integrable_exp_neg_planeOneNorm {a : ℝ} (ha : 0 < a) :
    Integrable (fun z : Plane => Real.exp (-a * planeOneNorm z)) := by
  let f : (Fin 2 → ℝ) → ℝ := fun z => ∏ i, Real.exp (-a * |z i|)
  have hf : Integrable f := by
    dsimp [f]
    exact Integrable.fintype_prod fun _ => integrable_exp_neg_mul_abs ha
  have hcomp : (fun z : Plane => Real.exp (-a * planeOneNorm z)) =
      f ∘ (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm := by
    funext z
    have hz : (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm z = fun i => z i := by
      funext i
      rfl
    change Real.exp (-a * planeOneNorm z) =
      f ((MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm z)
    rw [hz]
    dsimp only [f, planeOneNorm]
    rw [Fin.prod_univ_two, ← Real.exp_add]
    congr 1
    ring
  rw [hcomp]
  exact (PiLp.volume_preserving_ofLp (Fin 2)).integrable_comp_of_integrable hf

/-- The exact mass of the planar exponential tail in the coordinate one-norm. -/
theorem integral_exp_neg_planeOneNorm {a : ℝ} (ha : 0 < a) :
    (∫ z : Plane, Real.exp (-a * planeOneNorm z)) = (2 / a) ^ 2 := by
  let f : (Fin 2 → ℝ) → ℝ := fun z => ∏ i, Real.exp (-a * |z i|)
  have hcomp : (fun z : Plane => Real.exp (-a * planeOneNorm z)) =
      f ∘ (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm := by
    funext z
    have hz : (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm z = fun i => z i := by
      funext i
      rfl
    change Real.exp (-a * planeOneNorm z) =
      f ((MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm z)
    rw [hz]
    dsimp only [f, planeOneNorm]
    rw [Fin.prod_univ_two, ← Real.exp_add]
    congr 1
    ring
  rw [hcomp]
  change (∫ z : Plane, f ((MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm z)) = _
  rw [(PiLp.volume_preserving_ofLp (Fin 2)).integral_comp' f]
  rw [integral_fintype_prod_volume_eq_prod (fun i x => Real.exp (-a * |x|))]
  rw [integral_exp_neg_mul_abs ha]
  rw [Fin.prod_univ_two]
  field_simp [ne_of_gt ha]

/-- A product exponential kernel on full configurations. -/
@[irreducible] noncomputable def configurationExpDecayKernel {n : ℕ} (a : ℝ)
    (x y : Configuration n) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-a * configurationOneNorm (fun i => y i - x i)))

/-- The full-configuration exponential kernel's pointwise formula. -/
theorem configurationExpDecayKernel_apply {n : ℕ} (a : ℝ)
    (x y : Configuration n) :
    configurationExpDecayKernel a x y =
      ENNReal.ofReal (Real.exp (-a * configurationOneNorm (fun i => y i - x i))) := by
  unfold configurationExpDecayKernel
  rfl

/-- Integrability of the translated planar exponential tail. -/
theorem integrable_exp_neg_planeOneNorm_sub {a : ℝ} (ha : 0 < a) (c : Plane) :
    Integrable (fun z : Plane => Real.exp (-a * planeOneNorm (z - c))) := by
  exact (integrable_exp_neg_planeOneNorm ha).comp_sub_right c

/-- The translated planar exponential tail has the same exact mass. -/
theorem integral_exp_neg_planeOneNorm_sub {a : ℝ} (ha : 0 < a) (c : Plane) :
    (∫ z : Plane, Real.exp (-a * planeOneNorm (z - c))) = (2 / a) ^ 2 := by
  calc (∫ z : Plane, Real.exp (-a * planeOneNorm (z - c)))
      = ∫ z : Plane, Real.exp (-a * planeOneNorm z) :=
          (integral_sub_right_eq_self (fun z : Plane =>
            Real.exp (-a * planeOneNorm z)) c)
    _ = (2 / a) ^ 2 := integral_exp_neg_planeOneNorm ha

/-- Damping one heat strand yields a uniform exponential spatial tail. -/
theorem heatKernel_damped_exp_le {a q τ₀ τ : ℝ}
    (hdecay : 0 ≤ q - 2 * a ^ 2) (hτ₀ : 0 < τ₀) (hτ : τ₀ ≤ τ) (z : Plane) :
    Real.exp (-q * τ) * heatKernel τ z ≤
      (2 * Real.pi * τ₀)⁻¹ * Real.exp (-a * planeOneNorm z) := by
  have htime : 0 < τ := lt_of_lt_of_le hτ₀ hτ
  have hweight := heatKernel_mul_exp_oneNorm_le a htime z
  have hcancel : heatKernel τ z ≤
      2 * Real.exp (2 * a ^ 2 * τ) * heatKernel (2 * τ) z *
        Real.exp (-a * planeOneNorm z) := by
    calc heatKernel τ z =
          (heatKernel τ z * Real.exp (a * planeOneNorm z)) *
            Real.exp (-a * planeOneNorm z) := by
          rw [mul_assoc, ← Real.exp_add]
          simp
      _ ≤ (2 * Real.exp (2 * a ^ 2 * τ) * heatKernel (2 * τ) z) *
            Real.exp (-a * planeOneNorm z) :=
          mul_le_mul_of_nonneg_right hweight (Real.exp_nonneg _)
      _ = _ := by ring
  have hdecayExp : Real.exp (-((q - 2 * a ^ 2) * τ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hdecay htime.le))
  have hheat : heatKernel (2 * τ) z ≤ (4 * Real.pi * τ₀)⁻¹ := by
    calc heatKernel (2 * τ) z ≤ (2 * Real.pi * (2 * τ))⁻¹ :=
          heatKernel_le_at_zero (by positivity) z
      _ ≤ (4 * Real.pi * τ₀)⁻¹ := by
          apply inv_anti₀
          · positivity
          · nlinarith [Real.pi_pos]
  calc Real.exp (-q * τ) * heatKernel τ z
      ≤ Real.exp (-q * τ) *
          (2 * Real.exp (2 * a ^ 2 * τ) * heatKernel (2 * τ) z *
            Real.exp (-a * planeOneNorm z)) :=
          mul_le_mul_of_nonneg_left hcancel (Real.exp_nonneg _)
    _ = 2 * Real.exp (-((q - 2 * a ^ 2) * τ)) *
          heatKernel (2 * τ) z * Real.exp (-a * planeOneNorm z) := by
          have hexp : Real.exp (-q * τ) * Real.exp (2 * a ^ 2 * τ) =
              Real.exp (-((q - 2 * a ^ 2) * τ)) := by
            rw [← Real.exp_add]
            congr 1
            ring
          calc _ = 2 * (Real.exp (-q * τ) * Real.exp (2 * a ^ 2 * τ)) *
                heatKernel (2 * τ) z * Real.exp (-a * planeOneNorm z) := by ring
            _ = _ := by rw [hexp]
    _ ≤ 2 * 1 * (4 * Real.pi * τ₀)⁻¹ * Real.exp (-a * planeOneNorm z) := by
          have hhk : 0 ≤ heatKernel (2 * τ) z :=
            (Critical2DKPZ.heatKernel_pos (by positivity) z).le
          gcongr
    _ = (2 * Real.pi * τ₀)⁻¹ * Real.exp (-a * planeOneNorm z) := by ring

/-- The collision envelope is bounded by a fixed multiple of `exp(t) / t`. -/
noncomputable def collisionEnvelopeTailConstant : ℝ :=
  2 / (Real.log (1 / 2 : ℝ)) ^ 2

/-- At positive times, the collision-time envelope is bounded by a constant times `exp t / t`. -/
theorem collisionTimeEnvelope_le_exp_div {t : ℝ} (ht : 0 < t) :
    collisionTimeEnvelope t ≤ collisionEnvelopeTailConstant * Real.exp t / t := by
  let L := Real.log (1 / 2 : ℝ)
  let D := collisionEnvelopeTailConstant
  have hLneg : Real.log (1 / 2 : ℝ) < 0 := Real.log_neg (by norm_num) (by norm_num)
  have hLsq : 0 < L ^ 2 := sq_pos_of_ne_zero hLneg.ne
  have hDpos : 0 < D := by dsimp [D, collisionEnvelopeTailConstant]; positivity
  have hDrepr : D = 2 / L ^ 2 := by rfl
  by_cases hsmall : t ≤ 1 / 2
  · have hlogtneg : Real.log t < 0 := Real.log_neg ht (by linarith)
    have hlogmono : Real.log t ≤ L := Real.log_le_log ht hsmall
    have habs : |L| ≤ |Real.log t| := by
      rw [abs_of_neg hLneg, abs_of_neg hlogtneg]
      linarith
    have hsq : L ^ 2 ≤ (Real.log t) ^ 2 := by
      nlinarith [sq_nonneg (|Real.log t| - |L|)]
    have hdenA : 0 < t * (Real.log t) ^ 2 :=
      mul_pos ht (sq_pos_of_ne_zero hlogtneg.ne)
    have hdenB : 0 < L ^ 2 * t / 2 := by positivity
    have hdenle : L ^ 2 * t / 2 ≤ t * (Real.log t) ^ 2 := by
      nlinarith [hsq, ht]
    have hDover : D / t = (L ^ 2 * t / 2)⁻¹ := by
      rw [hDrepr]
      field_simp [ne_of_gt hLsq, ne_of_gt ht]
    have hsmallBound : collisionTimeEnvelope t ≤ D / t := by
      rw [collisionTimeEnvelope, min_eq_left hsmall]
      rw [hDover]
      exact (inv_le_inv₀ hdenA hdenB).2 hdenle
    calc collisionTimeEnvelope t ≤ D / t := hsmallBound
      _ ≤ D / t * Real.exp t := by
        exact le_mul_of_one_le_right (by positivity) (Real.one_le_exp ht.le)
      _ = D * Real.exp t / t := by ring
  · have hbig : 1 / 2 ≤ t := le_of_not_ge hsmall
    have hte : t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
    have hDover : 0 ≤ D / t := by positivity
    calc collisionTimeEnvelope t = D := by
          rw [collisionTimeEnvelope, min_eq_right hbig]
          dsimp [D, collisionEnvelopeTailConstant]
          field_simp [ne_of_gt hLsq]
      _ = (D / t) * t := by field_simp [ne_of_gt ht]
      _ ≤ (D / t) * Real.exp t := mul_le_mul_of_nonneg_left hte hDover
      _ = D * Real.exp t / t := by ring

/-- A half-time center heat strand has twice the exponential decay rate. -/
theorem heatKernel_half_damped_exp_le {a q τ₀ τ : ℝ}
    (hdecay : 0 ≤ q - 4 * a ^ 2) (hτ₀ : 0 < τ₀) (hτ : τ₀ ≤ τ) (z : Plane) :
    Real.exp (-q * τ) * heatKernel (τ / 2) z ≤
      (Real.pi * τ₀)⁻¹ * Real.exp (-2 * a * planeOneNorm z) := by
  have htime : 0 < τ := lt_of_lt_of_le hτ₀ hτ
  have hweight := heatKernel_mul_exp_oneNorm_le (2 * a) (by positivity : 0 < τ / 2) z
  rw [show 2 * (τ / 2) = τ by ring] at hweight
  have hcancel : heatKernel (τ / 2) z ≤
      2 * Real.exp (4 * a ^ 2 * τ) * heatKernel τ z *
        Real.exp (-2 * a * planeOneNorm z) := by
    calc heatKernel (τ / 2) z =
          (heatKernel (τ / 2) z * Real.exp (2 * a * planeOneNorm z)) *
            Real.exp (-2 * a * planeOneNorm z) := by
          rw [mul_assoc, ← Real.exp_add]
          simp
      _ ≤ (2 * Real.exp (2 * (2 * a) ^ 2 * (τ / 2)) * heatKernel τ z) *
            Real.exp (-2 * a * planeOneNorm z) :=
          mul_le_mul_of_nonneg_right hweight (Real.exp_nonneg _)
      _ = _ := by congr 1; ring_nf
  have hdecayExp : Real.exp (-((q - 4 * a ^ 2) * τ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hdecay htime.le))
  have hheat : heatKernel τ z ≤ (2 * Real.pi * τ₀)⁻¹ := by
    calc heatKernel τ z ≤ (2 * Real.pi * τ)⁻¹ := heatKernel_le_at_zero htime.le z
      _ ≤ (2 * Real.pi * τ₀)⁻¹ := by
        apply inv_anti₀
        · positivity
        · nlinarith [Real.pi_pos]
  calc Real.exp (-q * τ) * heatKernel (τ / 2) z
      ≤ Real.exp (-q * τ) *
          (2 * Real.exp (4 * a ^ 2 * τ) * heatKernel τ z *
            Real.exp (-2 * a * planeOneNorm z)) :=
          mul_le_mul_of_nonneg_left hcancel (Real.exp_nonneg _)
    _ = 2 * Real.exp (-((q - 4 * a ^ 2) * τ)) *
          heatKernel τ z * Real.exp (-2 * a * planeOneNorm z) := by
          have hexp : Real.exp (-q * τ) * Real.exp (4 * a ^ 2 * τ) =
              Real.exp (-((q - 4 * a ^ 2) * τ)) := by
            rw [← Real.exp_add]
            congr 1
            ring
          calc _ = 2 * (Real.exp (-q * τ) * Real.exp (4 * a ^ 2 * τ)) *
                heatKernel τ z * Real.exp (-2 * a * planeOneNorm z) := by ring
            _ = _ := by rw [hexp]
    _ ≤ 2 * 1 * (2 * Real.pi * τ₀)⁻¹ * Real.exp (-2 * a * planeOneNorm z) := by
          have hhk : 0 ≤ heatKernel τ z :=
            (Critical2DKPZ.heatKernel_pos htime z).le
          gcongr
    _ = (Real.pi * τ₀)⁻¹ * Real.exp (-2 * a * planeOneNorm z) := by ring

/-- A damped product heat kernel has an exponential tail in every particle
displacement. -/
theorem freeKernel_damped_exp_le {n : ℕ} (hn : 0 < n) {rate τ₀ τ a : ℝ}
    (hτ₀ : 0 < τ₀) (hτ : τ₀ ≤ τ)
    (hdecay : 2 * a ^ 2 ≤ rate / n) (x y : Configuration n) :
    Real.exp (-rate * τ) * freeKernel n τ x y ≤
      ((2 * Real.pi * τ₀)⁻¹) ^ n *
        Real.exp (-a * configurationOneNorm (fun i => y i - x i)) := by
  have hq : 0 ≤ rate / (n : ℝ) - 2 * a ^ 2 := by
    exact sub_nonneg.mpr hdecay
  have hsplit : Real.exp (-rate * τ) =
      ∏ i : Fin n, Real.exp (-(rate / (n : ℝ)) * τ) := by
    rw [← Real.exp_sum]
    congr 1
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [ne_of_gt (Nat.cast_pos.mpr hn)]
  rw [hsplit, freeKernel, ← Finset.prod_mul_distrib]
  calc (∏ i : Fin n,
        Real.exp (-(rate / (n : ℝ)) * τ) * heatKernel τ (y i - x i))
      ≤ ∏ i : Fin n,
          ((2 * Real.pi * τ₀)⁻¹ *
            Real.exp (-a * planeOneNorm (y i - x i))) := by
          apply Finset.prod_le_prod₀
          · intro i hi
            exact mul_nonneg (Real.exp_nonneg _)
              (Critical2DKPZ.heatKernel_nonneg (le_of_lt (lt_of_lt_of_le hτ₀ hτ)) _)
          · intro i hi
            exact heatKernel_damped_exp_le hq hτ₀ hτ (y i - x i)
    _ = ((2 * Real.pi * τ₀)⁻¹) ^ n *
          Real.exp (-a * configurationOneNorm (fun i => y i - x i)) := by
          calc _ = (∏ _i : Fin n, (2 * Real.pi * τ₀)⁻¹) *
                ∏ i : Fin n, Real.exp (-a * planeOneNorm (y i - x i)) :=
                  Finset.prod_mul_distrib
            _ = ((2 * Real.pi * τ₀)⁻¹) ^ n *
                Real.exp (∑ i : Fin n, -a * planeOneNorm (y i - x i)) := by
                  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
                    ← Real.exp_sum]
            _ = _ := by
                  rw [configurationOneNorm, ← Finset.mul_sum]

/-- One damped free time-kernel value is bounded by the scaled exponential
kernel. -/
theorem laplace_freeTimeKernel_le_exp {n : ℕ} {X Y : Type}
    {eX : X → Configuration n} {eY : Y → Configuration n}
    {rate τ₀ τ a : ℝ} (hn : 0 < n)
    (hτ₀ : 0 < τ₀) (hτ : τ₀ ≤ τ)
    (hdecay : 2 * a ^ 2 ≤ rate / n) (x : X) (y : Y) :
    laplaceTimeWeight rate τ *
        freeTimeKernel (n := n) (X := X) (Y := Y) eX eY (τ, x, y) ≤
      ENNReal.ofReal (((2 * Real.pi * τ₀)⁻¹) ^ n) *
        configurationExpDecayKernel a (eX x) (eY y) := by
  simp only [laplaceTimeWeight, freeTimeKernel]
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), configurationExpDecayKernel_apply]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ ((2 * Real.pi * τ₀)⁻¹) ^ n)]
  simpa only [neg_mul] using ENNReal.ofReal_le_ofReal
    (freeKernel_damped_exp_le hn hτ₀ hτ hdecay (eX x) (eY y))

/-- The supremum of damped free kernels is bounded by a scaled exponential
kernel. -/
theorem supTimeKernel_freeTimeKernel_le_exp {n : ℕ} {X Y : Type}
    {eX : X → Configuration n} {eY : Y → Configuration n}
    (rate τ₀ a : ℝ) (hn : 0 < n)
    (hτ₀ : 0 < τ₀) (hdecay : 2 * a ^ 2 ≤ rate / n)
    (x : X) (y : Y) :
    supTimeKernel rate τ₀ (freeTimeKernel (n := n) (X := X) (Y := Y) eX eY) x y ≤
      ENNReal.ofReal (((2 * Real.pi * τ₀)⁻¹) ^ n) *
        configurationExpDecayKernel a (eX x) (eY y) := by
  unfold supTimeKernel
  apply iSup_le
  intro t
  exact laplace_freeTimeKernel_le_exp hn hτ₀ t.2 hdecay x y

/-- The full-configuration exponential tail is integrable in either endpoint. -/
theorem integrable_configurationExpDecayKernel_right {n : ℕ} {a : ℝ} (ha : 0 < a)
    (x : Configuration n) :
    Integrable (fun y : Configuration n =>
      Real.exp (-a * configurationOneNorm (fun i => y i - x i))) := by
  have hEq (y : Configuration n) :
      Real.exp (-a * configurationOneNorm (fun i => y i - x i)) =
        ∏ i, Real.exp (-a * planeOneNorm (y i - x i)) := by
    rw [configurationOneNorm, Finset.mul_sum, Real.exp_sum]
  rw [show (fun y : Configuration n =>
      Real.exp (-a * configurationOneNorm (fun i => y i - x i))) =
        fun y => ∏ i, Real.exp (-a * planeOneNorm (y i - x i)) by
          funext y
          exact hEq y]
  exact Integrable.fintype_prod fun i => integrable_exp_neg_planeOneNorm_sub ha (x i)

/-- The full-configuration exponential tail has exact mass `((2/a)^2)^n`. -/
theorem integral_configurationExpDecayKernel_right {n : ℕ} {a : ℝ} (ha : 0 < a)
    (x : Configuration n) :
    (∫ y : Configuration n,
      Real.exp (-a * configurationOneNorm (fun i => y i - x i))) = ((2 / a) ^ 2) ^ n := by
  have hEq (y : Configuration n) :
      Real.exp (-a * configurationOneNorm (fun i => y i - x i)) =
        ∏ i, Real.exp (-a * planeOneNorm (y i - x i)) := by
    rw [configurationOneNorm, Finset.mul_sum, Real.exp_sum]
  rw [show (fun y : Configuration n =>
      Real.exp (-a * configurationOneNorm (fun i => y i - x i))) =
        fun y => ∏ i, Real.exp (-a * planeOneNorm (y i - x i)) by
          funext y
          exact hEq y]
  have hm (i : Fin n) :
      (∫ z : Plane, Real.exp (-a * planeOneNorm (z - x i))) = (2 / a) ^ 2 := by
    exact integral_exp_neg_planeOneNorm_sub ha (x i)
  rw [integral_fintype_prod_volume_eq_prod
    (fun i (z : Plane) => Real.exp (-a * planeOneNorm (z - x i)))]
  simp_rw [hm]
  simp [Finset.prod_const, Fintype.card_fin]

/-- The full-configuration exponential kernel has exact row mass. -/
theorem lintegral_configurationExpDecayKernel_right {n : ℕ} {a : ℝ} (ha : 0 < a)
    (x : Configuration n) :
    (∫⁻ y : Configuration n, configurationExpDecayKernel a x y) =
      ENNReal.ofReal (((2 / a) ^ 2) ^ n) := by
  have hrewrite :
      (∫⁻ y : Configuration n, configurationExpDecayKernel a x y) =
        ∫⁻ y : Configuration n,
          ENNReal.ofReal (Real.exp (-a * configurationOneNorm (fun i => y i - x i))) := by
    apply lintegral_congr
    intro y
    exact configurationExpDecayKernel_apply a x y
  rw [hrewrite]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_configurationExpDecayKernel_right ha x)
    (Filter.Eventually.of_forall fun _ => (Real.exp_nonneg _))]
  exact congrArg ENNReal.ofReal (integral_configurationExpDecayKernel_right ha x)

/-- Reversing endpoints leaves the full-configuration exponential kernel unchanged. -/
theorem configurationExpDecayKernel_symm {n : ℕ} (a : ℝ)
    (x y : Configuration n) :
    configurationExpDecayKernel a x y = configurationExpDecayKernel a y x := by
  unfold configurationExpDecayKernel
  congr 1
  unfold configurationOneNorm
  apply congrArg (fun r : ℝ => Real.exp (-a * r))
  apply Finset.sum_congr rfl
  intro i hi
  simp [planeOneNorm, abs_sub_comm]


/-- A fused-coordinate exponential kernel with one full endpoint. -/
@[irreducible] noncomputable def fusedConfigurationExpDecayKernel {n : ℕ}
    (α : CollisionPair n) (a : ℝ)
    (x : Configuration n) (z : FusedConfiguration α) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp
    (-a * configurationOneNorm (fun i => collisionEmbedding α z i - x i)))

/-- A fused endpoint is represented by its collision embedding in the full kernel. -/
theorem fusedConfigurationExpDecayKernel_eq {n : ℕ} (α : CollisionPair n) (a : ℝ)
    (x : Configuration n) (z : FusedConfiguration α) :
    fusedConfigurationExpDecayKernel α a x z =
      configurationExpDecayKernel a x (collisionEmbedding α z) := by
  unfold fusedConfigurationExpDecayKernel configurationExpDecayKernel
  rfl

/-- An exponential tail between two fused collision spaces. -/
@[irreducible] noncomputable def fusedFusedExpDecayKernel {n : ℕ}
    (α β : CollisionPair n) (a : ℝ)
    (x : FusedConfiguration α) (y : FusedConfiguration β) : ℝ≥0∞ :=
  configurationExpDecayKernel a (collisionEmbedding α x) (collisionEmbedding β y)

/-- The two-fused-endpoint kernel is the full kernel on the embedded endpoints. -/
theorem fusedFusedExpDecayKernel_eq {n : ℕ} (α β : CollisionPair n) (a : ℝ)
    (x : FusedConfiguration α) (y : FusedConfiguration β) :
    fusedFusedExpDecayKernel α β a x y =
      configurationExpDecayKernel a (collisionEmbedding α x) (collisionEmbedding β y) := by
  unfold fusedFusedExpDecayKernel
  rfl

/-- A product majorant for the exponential tail on fused coordinates. -/
noncomputable def fusedConfigurationExpDecayMajorant {n : ℕ} (α : CollisionPair n) (a : ℝ)
    (x : Configuration n) (z : FusedConfiguration α) : ℝ :=
  Real.exp (-a * planeOneNorm (z.1 - x α.1.1)) *
    ∏ i : Spectator α, Real.exp (-a * planeOneNorm (z.2 i - x i.1))

/-- The fused displacement norm splits into its two center strands and spectators. -/
theorem configurationOneNorm_collisionEmbedding_sub {n : ℕ} (α : CollisionPair n)
    (x : Configuration n) (z : FusedConfiguration α) :
    configurationOneNorm (fun i => collisionEmbedding α z i - x i) =
      planeOneNorm (z.1 - x α.1.1) + planeOneNorm (z.1 - x α.1.2) +
        ∑ i : Spectator α, planeOneNorm (z.2 i - x i.1) := by
  have hsum := sum_collision_labels α
    (fun i => planeOneNorm (collisionEmbedding α z i - x i))
  rw [configurationOneNorm]
  rw [hsum]
  simp only [collisionEmbedding, true_or, dite_true, or_true]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [i.2.1, i.2.2, or_self, dite_false]

/-- Damping the center and spectator heat strands gives the full embedded
configuration exponential tail. -/
theorem collisionHeatProduct_damped_exp_le {n : ℕ} (α : CollisionPair n)
    {a q τ₀ τ : ℝ} (hqCenter : 0 ≤ q - 4 * a ^ 2)
    (hqSpectator : 0 ≤ q - 2 * a ^ 2) (hτ₀ : 0 < τ₀) (hτ : τ₀ ≤ τ)
    (y z : FusedConfiguration α) :
    (Real.exp (-q * τ) * heatKernel (τ / 2) (z.1 - y.1)) *
      ∏ i : Spectator α,
        (Real.exp (-q * τ) * heatKernel τ (z.2 i - y.2 i)) ≤
      2 * ((2 * Real.pi * τ₀)⁻¹) ^ (Fintype.card (Spectator α) + 1) *
        Real.exp (-a * configurationOneNorm
          (fun i => collisionEmbedding α z i - collisionEmbedding α y i)) := by
  have hcenter := heatKernel_half_damped_exp_le
    (a := a) (q := q) hqCenter hτ₀ hτ (z.1 - y.1)
  have hspec (i : Spectator α) :=
    heatKernel_damped_exp_le (a := a) (q := q) hqSpectator hτ₀ hτ
      (z.2 i - y.2 i)
  have hspecProd :
      (∏ i : Spectator α,
        (2 * Real.pi * τ₀)⁻¹ * Real.exp (-a * planeOneNorm (z.2 i - y.2 i))) =
        ((2 * Real.pi * τ₀)⁻¹) ^ Fintype.card (Spectator α) *
          Real.exp (-a * ∑ i : Spectator α, planeOneNorm (z.2 i - y.2 i)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum]
    have hsum : (∑ i : Spectator α, -a * planeOneNorm (z.2 i - y.2 i)) =
        -a * ∑ i : Spectator α, planeOneNorm (z.2 i - y.2 i) := by
      rw [← Finset.mul_sum]
    rw [hsum]
  have hcoeff : (Real.pi * τ₀)⁻¹ * ((2 * Real.pi * τ₀)⁻¹) ^
        Fintype.card (Spectator α) =
      2 * ((2 * Real.pi * τ₀)⁻¹) ^ (Fintype.card (Spectator α) + 1) := by
    rw [show (Real.pi * τ₀)⁻¹ = 2 * (2 * Real.pi * τ₀)⁻¹ by field_simp,
      pow_succ]
    ring
  have hnorm : configurationOneNorm
      (fun i => collisionEmbedding α z i - collisionEmbedding α y i) =
      2 * planeOneNorm (z.1 - y.1) +
        ∑ i : Spectator α, planeOneNorm (z.2 i - y.2 i) := by
    have hsum := sum_collision_labels α
      (fun i => planeOneNorm (collisionEmbedding α z i - collisionEmbedding α y i))
    rw [configurationOneNorm, hsum]
    simp only [collisionEmbedding, true_or, dite_true, or_true]
    rw [two_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    simp only [i.2.1, i.2.2, or_self, dite_false]
  have hExp : Real.exp (-2 * a * planeOneNorm (z.1 - y.1)) *
      Real.exp (-a * ∑ i : Spectator α, planeOneNorm (z.2 i - y.2 i)) =
        Real.exp (-a * configurationOneNorm
          (fun i => collisionEmbedding α z i - collisionEmbedding α y i)) := by
    rw [← Real.exp_add, hnorm]
    congr 1
    ring
  have hprodBound :
      (∏ i : Spectator α,
        (Real.exp (-q * τ) * heatKernel τ (z.2 i - y.2 i))) ≤
        ∏ i : Spectator α,
          ((2 * Real.pi * τ₀)⁻¹ *
            Real.exp (-a * planeOneNorm (z.2 i - y.2 i))) := by
    apply Finset.prod_le_prod₀
    · intro i hi
      exact mul_nonneg (Real.exp_nonneg _)
        (Critical2DKPZ.heatKernel_nonneg (le_of_lt (lt_of_lt_of_le hτ₀ hτ)) _)
    · intro i hi
      exact hspec i
  calc (Real.exp (-q * τ) * heatKernel (τ / 2) (z.1 - y.1)) *
        ∏ i : Spectator α,
          (Real.exp (-q * τ) * heatKernel τ (z.2 i - y.2 i))
      ≤ ((Real.pi * τ₀)⁻¹ * Real.exp (-2 * a * planeOneNorm (z.1 - y.1))) *
          ∏ i : Spectator α,
            ((2 * Real.pi * τ₀)⁻¹ *
              Real.exp (-a * planeOneNorm (z.2 i - y.2 i))) := by
          have hleftprod : 0 ≤ ∏ i : Spectator α,
              (Real.exp (-q * τ) * heatKernel τ (z.2 i - y.2 i)) :=
            Finset.prod_nonneg fun i hi => mul_nonneg (Real.exp_nonneg _)
              (Critical2DKPZ.heatKernel_nonneg
                (le_of_lt (lt_of_lt_of_le hτ₀ hτ)) _)
          have hcenterRhs : 0 ≤ (Real.pi * τ₀)⁻¹ *
              Real.exp (-2 * a * planeOneNorm (z.1 - y.1)) := by positivity
          exact mul_le_mul hcenter hprodBound hleftprod hcenterRhs
    _ = 2 * ((2 * Real.pi * τ₀)⁻¹) ^ (Fintype.card (Spectator α) + 1) *
          Real.exp (-a * configurationOneNorm
            (fun i => collisionEmbedding α z i - collisionEmbedding α y i)) := by
          rw [hspecProd]
          calc (Real.pi * τ₀)⁻¹ * Real.exp (-2 * a * planeOneNorm (z.1 - y.1)) *
                (((2 * Real.pi * τ₀)⁻¹) ^ Fintype.card (Spectator α) *
                  Real.exp (-a * ∑ i : Spectator α,
                    planeOneNorm (z.2 i - y.2 i)))
              = ((Real.pi * τ₀)⁻¹ * ((2 * Real.pi * τ₀)⁻¹) ^
                    Fintype.card (Spectator α)) *
                  (Real.exp (-2 * a * planeOneNorm (z.1 - y.1)) *
                    Real.exp (-a * ∑ i : Spectator α,
                      planeOneNorm (z.2 i - y.2 i))) := by ring
            _ = _ := by rw [hcoeff, hExp]

/-- Split a scalar exponential damping over one center and all spectator
strands. -/
theorem exp_damping_split_fused {n : ℕ} (α : CollisionPair n) {b q t : ℝ}
    (hq : q * ((Fintype.card (Spectator α) + 1 : ℕ) : ℝ) = b) :
    Real.exp (-b * t) = Real.exp (-q * t) *
      ∏ _i : Spectator α, Real.exp (-q * t) := by
  have hprod (v : ℝ) :
      (∏ i : Spectator α, Real.exp v) =
        Real.exp (v * (Fintype.card (Spectator α) : ℝ)) := by
    rw [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
    congr 1
    ring
  rw [hprod, ← Real.exp_add]
  congr 1
  calc -b * t = -(q * ((Fintype.card (Spectator α) + 1 : ℕ) : ℝ)) * t := by rw [hq]
    _ = -q * t + (-q * t) * (Fintype.card (Spectator α) : ℝ) := by push_cast; ring

/-- Damped scalar collision density after absorbing the envelope's exponential
growth and its `1/t` singularity. -/
theorem scalarDensity_damped_envelope_le {θ rate t C c : ℝ}
    (hC : 0 ≤ C) (ht : 0 < t)
    (hscalar : scalarDensity θ t ≤ C * collisionTimeEnvelope t * Real.exp (c * t)) :
    Real.exp (-rate * t) * scalarDensity θ t ≤
      C * collisionEnvelopeTailConstant / t * Real.exp (-(rate - (c + 1)) * t) := by
  have henv := collisionTimeEnvelope_le_exp_div ht
  have hscalar' : scalarDensity θ t ≤
      C * (collisionEnvelopeTailConstant * Real.exp t / t) * Real.exp (c * t) :=
    le_trans hscalar (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left henv hC) (Real.exp_nonneg _))
  have hexp : Real.exp (-rate * t) * Real.exp t * Real.exp (c * t) =
      Real.exp (-(rate - (c + 1)) * t) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc Real.exp (-rate * t) * scalarDensity θ t
      ≤ Real.exp (-rate * t) *
          (C * (collisionEnvelopeTailConstant * Real.exp t / t) * Real.exp (c * t)) :=
            mul_le_mul_of_nonneg_left hscalar' (Real.exp_nonneg _)
    _ = (C * collisionEnvelopeTailConstant / t) *
          (Real.exp (-rate * t) * Real.exp t * Real.exp (c * t)) := by ring
    _ = _ := by rw [hexp]

/-- Converting an integer reciprocal power to a negative real power. -/
theorem inv_pow_eq_rpow_neg {n : ℕ} {t : ℝ} (ht : 0 < t) :
    (t⁻¹) ^ n = t ^ (-(n : ℝ)) := by
  calc (t⁻¹) ^ n = (t⁻¹) ^ (n : ℝ) := (Real.rpow_natCast _ _).symm
    _ = (t ^ (-1 : ℝ)) ^ (n : ℝ) := by rw [← Real.rpow_neg_one t]
    _ = t ^ ((-1 : ℝ) * (n : ℝ)) := by rw [Real.rpow_mul ht.le]
    _ = t ^ (-(n : ℝ)) := by congr 1; ring

/-- The heat and scalar singularity prefactors scale as `τ₀⁻ⁿ`. -/
theorem collisionSup_scale_eq {m n : ℕ} (hm : m + 1 = n) {τ₀ : ℝ}
    (hτ₀ : 0 < τ₀) :
    ((2 * Real.pi * τ₀)⁻¹) ^ m * τ₀⁻¹ =
      ((2 * Real.pi)⁻¹) ^ m * τ₀ ^ (-(n : ℝ)) := by
  calc ((2 * Real.pi * τ₀)⁻¹) ^ m * τ₀⁻¹
      = ((2 * Real.pi)⁻¹) ^ m * (τ₀⁻¹) ^ m * τ₀⁻¹ := by
          rw [mul_inv_rev, mul_pow]
          ring
    _ = ((2 * Real.pi)⁻¹) ^ m * (τ₀⁻¹) ^ (m + 1) := by
          rw [pow_succ]
          ring
    _ = ((2 * Real.pi)⁻¹) ^ m * τ₀ ^ (-(n : ℝ)) := by
          rw [hm, inv_pow_eq_rpow_neg hτ₀]


/-- The fused exponential tail is pointwise bounded by the product majorant. -/
theorem fusedConfigurationExpDecayKernel_le_majorant {n : ℕ} (α : CollisionPair n)
    {a : ℝ} (ha : 0 < a) (x : Configuration n) (z : FusedConfiguration α) :
    Real.exp (-a * configurationOneNorm (fun i => collisionEmbedding α z i - x i)) ≤
      fusedConfigurationExpDecayMajorant α a x z := by
  rw [configurationOneNorm_collisionEmbedding_sub]
  have h₂ : 0 ≤ planeOneNorm (z.1 - x α.1.2) := planeOneNorm_nonneg _
  have hprod : fusedConfigurationExpDecayMajorant α a x z =
      Real.exp (-a * (planeOneNorm (z.1 - x α.1.1) +
        ∑ i : Spectator α, planeOneNorm (z.2 i - x i.1))) := by
    unfold fusedConfigurationExpDecayMajorant
    have hs : (∏ i : Spectator α, Real.exp (-a * planeOneNorm (z.2 i - x i.1))) =
        Real.exp (-a * ∑ i : Spectator α, planeOneNorm (z.2 i - x i.1)) := by
      rw [← Real.exp_sum]
      congr 1
      rw [← Finset.mul_sum]
    rw [hs, ← Real.exp_add]
    congr 1
    ring
  rw [hprod]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg ha.le h₂]

/-- The fused-coordinate exponential majorant is integrable. -/
theorem integrable_fusedConfigurationExpDecayMajorant {n : ℕ}
    (α : CollisionPair n) {a : ℝ} (ha : 0 < a) (x : Configuration n) :
    Integrable (fun z : FusedConfiguration α => fusedConfigurationExpDecayMajorant α a x z) := by
  unfold fusedConfigurationExpDecayMajorant
  have hs : Integrable (fun z : Spectator α → Plane =>
      ∏ i : Spectator α, Real.exp (-a * planeOneNorm (z i - x i.1))) :=
    Integrable.fintype_prod
      (μ := fun _ : Spectator α => (volume : Measure Plane))
      (fun i : Spectator α => integrable_exp_neg_planeOneNorm_sub ha (x i.1))
  exact (integrable_exp_neg_planeOneNorm_sub ha (x α.1.1)).mul_prod
    hs

/-- The fused-coordinate exponential majorant has exact mass. -/
theorem integral_fusedConfigurationExpDecayMajorant {n : ℕ}
    (α : CollisionPair n) {a : ℝ} (ha : 0 < a) (x : Configuration n) :
    (∫ z : FusedConfiguration α, fusedConfigurationExpDecayMajorant α a x z) =
      ((2 / a) ^ 2) ^ (Fintype.card (Spectator α) + 1) := by
  unfold fusedConfigurationExpDecayMajorant
  rw [Measure.volume_eq_prod]
  rw [integral_prod_mul (μ := (volume : Measure Plane))
    (ν := (volume : Measure (Spectator α → Plane)))
    (fun z : Plane => Real.exp (-a * planeOneNorm (z - x α.1.1)))
    (fun z : Spectator α → Plane =>
      ∏ i : Spectator α, Real.exp (-a * planeOneNorm (z i - x i.1)))]
  rw [integral_exp_neg_planeOneNorm_sub ha]
  rw [integral_fintype_prod_volume_eq_prod
    (fun (i : Spectator α) (z : Plane) => Real.exp (-a * planeOneNorm (z - x i.1)))]
  have hm (i : Spectator α) :
      (∫ z : Plane, Real.exp (-a * planeOneNorm (z - x i.1))) = (2 / a) ^ 2 :=
    integral_exp_neg_planeOneNorm_sub ha (x i.1)
  simp_rw [hm]
  rw [Finset.prod_const]
  simp only [Finset.card_univ]
  rw [pow_succ]
  ring

/-- Integral bound for the fused-coordinate exponential tail; the majorant is integrable. -/
theorem lintegral_fusedConfigurationExpDecayKernel_right {n : ℕ}
    (α : CollisionPair n) {a : ℝ} (ha : 0 < a) (x : Configuration n) :
    (∫⁻ z : FusedConfiguration α, fusedConfigurationExpDecayKernel α a x z) ≤
      ENNReal.ofReal (((2 / a) ^ 2) ^ (Fintype.card (Spectator α) + 1)) := by
  have hrewrite :
      (∫⁻ z : FusedConfiguration α, fusedConfigurationExpDecayKernel α a x z) =
        ∫⁻ z : FusedConfiguration α,
          ENNReal.ofReal (Real.exp
            (-a * configurationOneNorm (fun i => collisionEmbedding α z i - x i))) := by
    apply lintegral_congr
    intro z
    unfold fusedConfigurationExpDecayKernel
    rfl
  rw [hrewrite]
  calc (∫⁻ z : FusedConfiguration α, ENNReal.ofReal (Real.exp
        (-a * configurationOneNorm (fun i => collisionEmbedding α z i - x i))))
      ≤ ∫⁻ z : FusedConfiguration α,
          ENNReal.ofReal (fusedConfigurationExpDecayMajorant α a x z) := by
            apply lintegral_mono
            intro z
            exact ENNReal.ofReal_le_ofReal
              (fusedConfigurationExpDecayKernel_le_majorant α ha x z)
    _ = ENNReal.ofReal (∫ z : FusedConfiguration α,
          fusedConfigurationExpDecayMajorant α a x z) := by
            have hnonneg (z : FusedConfiguration α) :
                0 ≤ fusedConfigurationExpDecayMajorant α a x z := by
              unfold fusedConfigurationExpDecayMajorant
              exact mul_nonneg (Real.exp_nonneg _)
                (Finset.prod_nonneg fun _ _ => Real.exp_nonneg _)
            rw [← ofReal_integral_eq_lintegral_ofReal
              (integrable_fusedConfigurationExpDecayMajorant α ha x)
              (Filter.Eventually.of_forall hnonneg)]
    _ = ENNReal.ofReal (((2 / a) ^ 2) ^ (Fintype.card (Spectator α) + 1)) := by
            rw [integral_fusedConfigurationExpDecayMajorant α ha x]

/-- Joint measurability of the planar one-norm. -/
theorem measurable_planeOneNorm : Measurable (planeOneNorm : Plane → ℝ) := by
  unfold planeOneNorm
  fun_prop

/-- The sum of the coordinate one-norms is measurable on configuration space. -/
theorem measurable_configurationOneNorm {n : ℕ} :
    Measurable (configurationOneNorm : Configuration n → ℝ) := by
  unfold configurationOneNorm
  exact Finset.univ.measurable_fun_sum fun i hi =>
    measurable_planeOneNorm.comp (measurable_pi_apply i)

/-- Joint measurability of the full-configuration exponential kernel. -/
theorem measurable_configurationExpDecayKernel {n : ℕ} (a : ℝ) :
    Measurable (Function.uncurry (configurationExpDecayKernel (n := n) a)) := by
  have hdiff : Measurable (fun p : Configuration n × Configuration n =>
      fun i => p.2 i - p.1 i) := by
    apply Measurable.of_eval
    intro i
    fun_prop
  have hnorm : Measurable (fun p : Configuration n × Configuration n =>
      configurationOneNorm (fun i => p.2 i - p.1 i)) :=
    measurable_configurationOneNorm.comp hdiff
  unfold configurationExpDecayKernel
  exact (Real.continuous_exp.measurable.comp (measurable_const.mul hnorm)).ennreal_ofReal

/-- Joint measurability of an exponential kernel with one fused endpoint. -/
theorem measurable_fusedConfigurationExpDecayKernel {n : ℕ} (α : CollisionPair n) (a : ℝ) :
    Measurable (fun p : Configuration n × FusedConfiguration α =>
      fusedConfigurationExpDecayKernel α a p.1 p.2) := by
  have harg : Measurable (fun p : Configuration n × FusedConfiguration α =>
      (p.1, collisionEmbedding α p.2)) :=
    measurable_fst.prodMk ((measurable_collisionEmbedding α).comp measurable_snd)
  have heq : (fun p : Configuration n × FusedConfiguration α =>
      fusedConfigurationExpDecayKernel α a p.1 p.2) =
      (fun p => configurationExpDecayKernel a p.1 (collisionEmbedding α p.2)) := by
    funext p
    exact fusedConfigurationExpDecayKernel_eq α a p.1 p.2
  rw [heq]
  exact (measurable_configurationExpDecayKernel a).comp harg

/-- Joint measurability of an exponential kernel between fused endpoints. -/
theorem measurable_fusedFusedExpDecayKernel {n : ℕ} (α β : CollisionPair n) (a : ℝ) :
    Measurable (fun p : FusedConfiguration α × FusedConfiguration β =>
      fusedFusedExpDecayKernel α β a p.1 p.2) := by
  have harg : Measurable (fun p : FusedConfiguration α × FusedConfiguration β =>
      (collisionEmbedding α p.1, collisionEmbedding β p.2)) :=
    ((measurable_collisionEmbedding α).comp measurable_fst).prodMk
      ((measurable_collisionEmbedding β).comp measurable_snd)
  have heq : (fun p : FusedConfiguration α × FusedConfiguration β =>
      fusedFusedExpDecayKernel α β a p.1 p.2) =
      (fun p => configurationExpDecayKernel a (collisionEmbedding α p.1)
        (collisionEmbedding β p.2)) := by
    funext p
    exact fusedFusedExpDecayKernel_eq α β a p.1 p.2
  rw [heq]
  exact (measurable_configurationExpDecayKernel a).comp harg

/-- Schur bounds convert to a positive bilinear form bound. -/
theorem formBound_of_schur {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] [SigmaFinite μ] [SigmaFinite ν]
    {K : X → Y → ℝ≥0∞} {A B c : ℝ≥0∞}
    (hK : Measurable (Function.uncurry K))
    (hrow : ∀ x, ∫⁻ y, K x y ∂ν ≤ A) (hcol : ∀ y, ∫⁻ x, K x y ∂μ ≤ B)
    (hc : A * B ≤ c ^ 2) : FormBound μ ν K c := by
  apply (formBound_iff_l2_sq_le μ ν hK c).2
  intro f hf
  calc (∫⁻ x, (∫⁻ y, K x y * f y ∂ν) ^ (2 : ℝ) ∂μ)
      ≤ A * B * ∫⁻ y, f y ^ (2 : ℝ) ∂ν := by
          simpa only [ENNReal.rpow_two] using lintegral_kernel_sq_le μ ν hK hrow hcol hf
    _ ≤ c ^ 2 * ∫⁻ y, f y ^ (2 : ℝ) ∂ν := mul_le_mul' hc le_rfl

/-- Multiplying a positive kernel by a finite scalar multiplies its form bound
by the same scalar. -/
theorem FormBound.const_mul_left {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    {K : X → Y → ℝ≥0∞} {c d : ℝ≥0∞} (hd : d ≠ ⊤)
    (h : FormBound μ ν K c) :
    FormBound μ ν (fun x y => d * K x y) (d * c) := by
  intro f g hf hg
  have hinner (x : X) :
      (∫⁻ y, (d * K x y) * f y ∂ν) = d * ∫⁻ y, K x y * f y ∂ν := by
    rw [show (fun y => (d * K x y) * f y) = fun y => d * (K x y * f y) by
      funext y
      ring, lintegral_const_mul' d _ hd]
  calc (∫⁻ x, g x * (∫⁻ y, (d * K x y) * f y ∂ν) ∂μ)
      = d * ∫⁻ x, g x * (∫⁻ y, K x y * f y ∂ν) ∂μ := by
          simp_rw [hinner]
          rw [show (fun x => g x * (d * ∫⁻ y, K x y * f y ∂ν)) =
            fun x => d * (g x * ∫⁻ y, K x y * f y ∂ν) by
              funext x
              ring, lintegral_const_mul' d _ hd]
    _ ≤ d * (c * (∫⁻ y, f y ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) *
          (∫⁻ x, g x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)) :=
            mul_le_mul' le_rfl (h f g hf hg)
    _ = d * c * (∫⁻ y, f y ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) *
          (∫⁻ x, g x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by ring


/-- The fused exponential row mass is bounded by `M^n` when `M` dominates
the one-coordinate tail mass. -/
theorem lintegral_fusedConfigurationExpDecayKernel_le_pow {n : ℕ} (α : CollisionPair n)
    {a M : ℝ} (ha : 0 < a) (hM : 1 ≤ M) (hscale : (2 / a) ^ 2 ≤ M)
    (x : Configuration n) :
    (∫⁻ z : FusedConfiguration α, fusedConfigurationExpDecayKernel α a x z) ≤
      ENNReal.ofReal (M ^ n) := by
  have hn : 2 ≤ n := by
    have hlt := α.2
    have hi := α.1.1.isLt
    have hj := α.1.2.isLt
    omega
  have hcard : Fintype.card (Spectator α) + 1 ≤ n := by
    rw [card_spectator]
    omega
  have hmass : ((2 / a) ^ 2) ^ (Fintype.card (Spectator α) + 1) ≤ M ^ n := by
    exact (pow_le_pow_left₀ (sq_nonneg (2 / a)) hscale _).trans
      (pow_le_pow_right₀ hM hcard)
  calc (∫⁻ z : FusedConfiguration α, fusedConfigurationExpDecayKernel α a x z)
      ≤ ENNReal.ofReal (((2 / a) ^ 2) ^ (Fintype.card (Spectator α) + 1)) :=
          lintegral_fusedConfigurationExpDecayKernel_right α ha x
    _ ≤ ENNReal.ofReal (M ^ n) := ENNReal.ofReal_le_ofReal hmass

/-- A fused endpoint costs at most one exponential-tail mass per independent coordinate. -/
theorem formBound_fusedConfigurationExpDecayKernel {n : ℕ} (α : CollisionPair n)
    {a : ℝ} (ha : 0 < a) {M : ℝ} (hM : 1 ≤ M)
    (hscale : (2 / a) ^ 2 ≤ M) :
    FormBound volume volume (fusedConfigurationExpDecayKernel α a)
      (ENNReal.ofReal (M ^ n)) := by
  let c : ℝ≥0∞ := ENNReal.ofReal (M ^ n)
  have hrow (x : Configuration n) :
      (∫⁻ z : FusedConfiguration α, fusedConfigurationExpDecayKernel α a x z) ≤ c := by
    exact lintegral_fusedConfigurationExpDecayKernel_le_pow α ha hM hscale x
  have hcol (z : FusedConfiguration α) :
      (∫⁻ x : Configuration n, fusedConfigurationExpDecayKernel α a x z) ≤ c := by
    have hrewrite :
        (∫⁻ x : Configuration n, fusedConfigurationExpDecayKernel α a x z) =
          ∫⁻ x : Configuration n,
            configurationExpDecayKernel a x (collisionEmbedding α z) := by
      apply lintegral_congr
      intro x
      exact fusedConfigurationExpDecayKernel_eq α a x z
    rw [hrewrite]
    calc (∫⁻ x : Configuration n, configurationExpDecayKernel a x (collisionEmbedding α z))
        = ∫⁻ x : Configuration n, configurationExpDecayKernel a (collisionEmbedding α z) x := by
            apply lintegral_congr
            intro x
            exact configurationExpDecayKernel_symm a x (collisionEmbedding α z)
      _ = ENNReal.ofReal (((2 / a) ^ 2) ^ n) :=
            lintegral_configurationExpDecayKernel_right ha (collisionEmbedding α z)
      _ ≤ c := ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (sq_nonneg (2 / a)) hscale n |>.trans
            (pow_le_pow_right₀ hM le_rfl))
  have hc : c * c ≤ c ^ 2 := by rw [pow_two]
  exact formBound_of_schur volume volume (measurable_fusedConfigurationExpDecayKernel α a)
    hrow hcol hc

/-- The column mass of a fused-endpoint exponential tail has the same bound
as its row mass. -/
theorem lintegral_fusedConfigurationExpDecayKernel_left_le_pow {n : ℕ}
    (α : CollisionPair n) {a M : ℝ} (ha : 0 < a) (hM : 1 ≤ M)
    (hscale : (2 / a) ^ 2 ≤ M) (z : FusedConfiguration α) :
    (∫⁻ x : Configuration n, fusedConfigurationExpDecayKernel α a x z) ≤
      ENNReal.ofReal (M ^ n) := by
  have hrow : (∫⁻ x : Configuration n,
      fusedConfigurationExpDecayKernel α a x z) =
      ∫⁻ x : Configuration n, configurationExpDecayKernel a
        (collisionEmbedding α z) x := by
    apply lintegral_congr
    intro x
    rw [fusedConfigurationExpDecayKernel_eq]
    exact configurationExpDecayKernel_symm a x (collisionEmbedding α z)
  rw [hrow]
  calc (∫⁻ x : Configuration n,
        configurationExpDecayKernel a (collisionEmbedding α z) x)
      = ENNReal.ofReal (((2 / a) ^ 2) ^ n) :=
          lintegral_configurationExpDecayKernel_right ha (collisionEmbedding α z)
    _ ≤ ENNReal.ofReal (M ^ n) := ENNReal.ofReal_le_ofReal
      (pow_le_pow_left₀ (sq_nonneg (2 / a)) hscale n |>.trans
        (pow_le_pow_right₀ hM le_rfl))

/-- The time-independent real constant in the free supremum estimate. -/
noncomputable def freeSupFormConstant (n : ℕ) : ℝ :=
  (8 * (n : ℝ)) ^ n * (2 * Real.pi)⁻¹ ^ n

/-- The product of the heat prefactor and exponential-tail mass has the
required `τ₀⁻ⁿ` scaling. -/
theorem freeSup_scale_eq {n : ℕ} {τ₀ : ℝ} (hτ₀ : 0 < τ₀) :
    ((2 * Real.pi * τ₀)⁻¹) ^ n * (8 * (n : ℝ)) ^ n =
      freeSupFormConstant n * τ₀ ^ (-(n : ℝ)) := by
  have hτpow : (τ₀⁻¹) ^ n = τ₀ ^ (-(n : ℝ)) := by
    calc (τ₀⁻¹) ^ n = (τ₀⁻¹) ^ (n : ℝ) := (Real.rpow_natCast _ _).symm
      _ = (τ₀ ^ (-1 : ℝ)) ^ (n : ℝ) := by rw [← Real.rpow_neg_one τ₀]
      _ = τ₀ ^ ((-1 : ℝ) * (n : ℝ)) := by rw [Real.rpow_mul hτ₀.le]
      _ = τ₀ ^ (-(n : ℝ)) := by congr 1; ring
  have hsplit : (2 * Real.pi * τ₀)⁻¹ = (2 * Real.pi)⁻¹ * τ₀⁻¹ := by
    rw [mul_inv_rev]
    ring
  dsimp [freeSupFormConstant]
  calc ((2 * Real.pi * τ₀)⁻¹) ^ n * (8 * (n : ℝ)) ^ n
      = ((2 * Real.pi)⁻¹ * τ₀⁻¹) ^ n * (8 * (n : ℝ)) ^ n := by rw [hsplit]
    _ = (2 * Real.pi)⁻¹ ^ n * (τ₀⁻¹) ^ n * (8 * (n : ℝ)) ^ n := by rw [mul_pow]
    _ = (8 * (n : ℝ)) ^ n * (2 * Real.pi)⁻¹ ^ n * τ₀ ^ (-(n : ℝ)) := by
      rw [hτpow]
      ring

/-- The free-supremum scale constant is positive. -/
theorem freeSupFormConstant_pos (n : ℕ) :
    0 < freeSupFormConstant n := by
  by_cases hn : n = 0
  · simp [freeSupFormConstant, hn]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hnpos
    unfold freeSupFormConstant
    positivity

/-- The scaled exponential tail with transposed endpoints has the same
bilinear form bound. -/
theorem formBound_transposed_fusedConfigurationExpDecayKernel {n : ℕ}
    (α : CollisionPair n) {a M : ℝ} (ha : 0 < a) (hM : 1 ≤ M)
    (hscale : (2 / a) ^ 2 ≤ M) {d : ℝ≥0∞} (hd : d ≠ ⊤) :
    FormBound volume volume
      (fun z x => d * fusedConfigurationExpDecayKernel α a x z)
      (d * ENNReal.ofReal (M ^ n)) := by
  have hK : Measurable (Function.uncurry
      (fun z : FusedConfiguration α => fun x : Configuration n =>
        d * fusedConfigurationExpDecayKernel α a x z)) := by
    exact measurable_const.mul
      ((measurable_fusedConfigurationExpDecayKernel α a).comp measurable_swap)
  let c : ℝ≥0∞ := d * ENNReal.ofReal (M ^ n)
  have hrow (z : FusedConfiguration α) :
      (∫⁻ x : Configuration n,
        d * fusedConfigurationExpDecayKernel α a x z) ≤ c := by
    rw [lintegral_const_mul' d _ hd]
    exact mul_le_mul' le_rfl
      (lintegral_fusedConfigurationExpDecayKernel_left_le_pow α ha hM hscale z)
  have hcol (x : Configuration n) :
      (∫⁻ z : FusedConfiguration α,
        d * fusedConfigurationExpDecayKernel α a x z) ≤ c := by
    rw [lintegral_const_mul' d _ hd]
    exact mul_le_mul' le_rfl
      (lintegral_fusedConfigurationExpDecayKernel_le_pow α ha hM hscale x)
  have hc : c * c ≤ c ^ 2 := by rw [pow_two]
  exact formBound_of_schur volume volume hK hrow hcol hc


/-- Schur bound for the exponential kernel between fused collision spaces. -/
theorem formBound_fusedFusedExpDecayKernel {n : ℕ} (α β : CollisionPair n)
    {a : ℝ} (ha : 0 < a) {M : ℝ} (hM : 1 ≤ M)
    (hscale : (2 / a) ^ 2 ≤ M) :
    FormBound volume volume (fusedFusedExpDecayKernel α β a)
      (ENNReal.ofReal (M ^ n)) := by
  let c : ℝ≥0∞ := ENNReal.ofReal (M ^ n)
  have hrow (x : FusedConfiguration α) :
      (∫⁻ y : FusedConfiguration β, fusedFusedExpDecayKernel α β a x y) ≤ c := by
    have hrewrite :
        (∫⁻ y : FusedConfiguration β, fusedFusedExpDecayKernel α β a x y) =
          ∫⁻ y : FusedConfiguration β,
            fusedConfigurationExpDecayKernel β a (collisionEmbedding α x) y := by
      apply lintegral_congr
      intro y
      rw [fusedFusedExpDecayKernel_eq, fusedConfigurationExpDecayKernel_eq]
    rw [hrewrite]
    exact lintegral_fusedConfigurationExpDecayKernel_le_pow β ha hM hscale
      (collisionEmbedding α x)
  have hcol (y : FusedConfiguration β) :
      (∫⁻ x : FusedConfiguration α, fusedFusedExpDecayKernel α β a x y) ≤ c := by
    have hrewrite :
        (∫⁻ x : FusedConfiguration α, fusedFusedExpDecayKernel α β a x y) =
          ∫⁻ x : FusedConfiguration α,
            fusedConfigurationExpDecayKernel α a (collisionEmbedding β y) x := by
      apply lintegral_congr
      intro x
      calc fusedFusedExpDecayKernel α β a x y
          = configurationExpDecayKernel a (collisionEmbedding α x)
              (collisionEmbedding β y) := fusedFusedExpDecayKernel_eq α β a x y
        _ = configurationExpDecayKernel a (collisionEmbedding β y)
              (collisionEmbedding α x) :=
                configurationExpDecayKernel_symm a _ _
        _ = fusedConfigurationExpDecayKernel α a (collisionEmbedding β y) x :=
              (fusedConfigurationExpDecayKernel_eq α a _ _).symm
    rw [hrewrite]
    exact lintegral_fusedConfigurationExpDecayKernel_le_pow α ha hM hscale
      (collisionEmbedding β y)
  have hc : c * c ≤ c ^ 2 := by rw [pow_two]
  exact formBound_of_schur volume volume (measurable_fusedFusedExpDecayKernel α β a)
    hrow hcol hc

/-- The three free pointwise-supremum blocks have a uniform `L²` form bound. -/
theorem exists_formBound_sup_free (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ rate : ℝ, 1 ≤ rate → ∀ τ₀ : ℝ, 0 < τ₀ → τ₀ ≤ 1 →
      (∀ α : CollisionPair n, FormBound volume volume
        (supTimeKernel rate τ₀ (freeTimeKernel id (collisionEmbedding α)))
        (ENNReal.ofReal (C * τ₀ ^ (-(n : ℝ))))) ∧
      (∀ α : CollisionPair n, FormBound volume volume
        (supTimeKernel rate τ₀ (freeTimeKernel (collisionEmbedding α) id))
        (ENNReal.ofReal (C * τ₀ ^ (-(n : ℝ))))) ∧
      (∀ α β : CollisionPair n, FormBound volume volume
        (supTimeKernel rate τ₀ (freeTimeKernel (collisionEmbedding α) (collisionEmbedding β)))
        (ENNReal.ofReal (C * τ₀ ^ (-(n : ℝ))))) := by
  refine ⟨freeSupFormConstant n, freeSupFormConstant_pos n, ?_⟩
  by_cases hnSmall : n ≤ 1
  · intro rate hrate τ₀ hτ₀ _hτ₀le
    refine ⟨?_, ?_, ?_⟩
    · intro α
      exact False.elim (collisionPair_impossible hnSmall α)
    · intro α
      exact False.elim (collisionPair_impossible hnSmall α)
    · intro α β
      exact False.elim (collisionPair_impossible hnSmall α)
  · have hn : 2 ≤ n := by omega
    have hnpos : 0 < n := by omega
    intro rate hrate τ₀ hτ₀ _hτ₀le
    have hnR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    let a : ℝ := (Real.sqrt (2 * (n : ℝ)))⁻¹
    let M : ℝ := 8 * (n : ℝ)
    have ha : 0 < a := by
      dsimp [a]
      positivity
    have haSq : a ^ 2 = (2 * (n : ℝ))⁻¹ := by
      dsimp [a]
      rw [inv_pow, Real.sq_sqrt (by positivity)]
    have hdecay : 2 * a ^ 2 ≤ rate / (n : ℝ) := by
      calc 2 * a ^ 2 = 1 / (n : ℝ) := by rw [haSq]; field_simp
        _ ≤ rate / (n : ℝ) := div_le_div_of_nonneg_right hrate hnR.le
    have hM : 1 ≤ M := by
      dsimp [M]
      have hnR2 : 2 ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith
    have hscale : (2 / a) ^ 2 ≤ M := by
      calc (2 / a) ^ 2 = 4 / a ^ 2 := by field_simp [ne_of_gt ha]; norm_num
        _ = 8 * (n : ℝ) := by rw [haSq]; field_simp; ring
        _ = M := rfl
        _ ≤ M := le_rfl
    let d : ℝ≥0∞ := ENNReal.ofReal (((2 * Real.pi * τ₀)⁻¹) ^ n)
    have hd : d ≠ ⊤ := by simp [d]
    have hmass : d * ENNReal.ofReal (M ^ n) =
        ENNReal.ofReal (freeSupFormConstant n * τ₀ ^ (-(n : ℝ))) := by
      dsimp [d, M]
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ ((2 * Real.pi * τ₀)⁻¹) ^ n)]
      rw [freeSup_scale_eq hτ₀]
    refine ⟨?_, ?_, ?_⟩
    · intro α
      have hbase := formBound_fusedConfigurationExpDecayKernel α ha hM hscale
      have hscaled := FormBound.const_mul_left hd hbase
      apply hscaled.mono
      · intro x z
        calc supTimeKernel rate τ₀ (freeTimeKernel id (collisionEmbedding α)) x z
            ≤ ENNReal.ofReal (((2 * Real.pi * τ₀)⁻¹) ^ n) *
                configurationExpDecayKernel a x (collisionEmbedding α z) :=
                  supTimeKernel_freeTimeKernel_le_exp (n := n)
                    (X := Configuration n) (Y := FusedConfiguration α)
                    (eX := id) (eY := collisionEmbedding α) rate τ₀ a hnpos hτ₀ hdecay x z
          _ = d * fusedConfigurationExpDecayKernel α a x z := by
                dsimp [d]
                rw [fusedConfigurationExpDecayKernel_eq]
      · rw [hmass]

    · intro α
      have hbase := formBound_transposed_fusedConfigurationExpDecayKernel α ha hM hscale hd
      apply hbase.mono
      · intro z x
        calc supTimeKernel rate τ₀ (freeTimeKernel (collisionEmbedding α) id) z x
            ≤ ENNReal.ofReal (((2 * Real.pi * τ₀)⁻¹) ^ n) *
                configurationExpDecayKernel a (collisionEmbedding α z) x :=
                  supTimeKernel_freeTimeKernel_le_exp (n := n)
                    (X := FusedConfiguration α) (Y := Configuration n)
                    (eX := collisionEmbedding α) (eY := id) rate τ₀ a hnpos hτ₀ hdecay z x
          _ = d * fusedConfigurationExpDecayKernel α a x z := by
                dsimp [d]
                rw [fusedConfigurationExpDecayKernel_eq]
                congr 1
                exact (configurationExpDecayKernel_symm a x (collisionEmbedding α z)).symm
      · rw [hmass]
    · intro α β
      have hbase := formBound_fusedFusedExpDecayKernel α β ha hM hscale
      have hscaled := FormBound.const_mul_left hd hbase
      apply hscaled.mono
      · intro x y
        calc supTimeKernel rate τ₀
              (freeTimeKernel (collisionEmbedding α) (collisionEmbedding β)) x y
            ≤ ENNReal.ofReal (((2 * Real.pi * τ₀)⁻¹) ^ n) *
                configurationExpDecayKernel a (collisionEmbedding α x)
                  (collisionEmbedding β y) :=
                  supTimeKernel_freeTimeKernel_le_exp (n := n)
                    (X := FusedConfiguration α) (Y := FusedConfiguration β)
                    (eX := collisionEmbedding α) (eY := collisionEmbedding β)
                    rate τ₀ a hnpos hτ₀ hdecay x y
          _ = d * fusedFusedExpDecayKernel α β a x y := by
                dsimp [d]
                rw [fusedFusedExpDecayKernel_eq]
      · rw [hmass]

/-- The collision pointwise-supremum kernel has a uniform `L²` form bound
when the Laplace rate dominates the scalar envelope growth. -/
theorem exists_formBound_sup_collision (n : ℕ) (A : ℝ) :
    ∃ C rate₀ : ℝ, 0 < C ∧ ∀ θ : ℝ, θ ≤ A → ∀ rate : ℝ, rate₀ ≤ rate →
      ∀ τ₀ : ℝ, 0 < τ₀ → τ₀ ≤ 1 → ∀ α : CollisionPair n,
        FormBound volume volume
          (supTimeKernel rate τ₀ (collisionTimeKernel α θ))
          (ENNReal.ofReal (C * τ₀ ^ (-(n : ℝ)))) := by
  obtain ⟨Cscalar, cscalar, hCscalar, hcscalar, hscalar⟩ :=
    exists_scalarDensity_le_envelope A
  by_cases hnSmall : n ≤ 1
  · refine ⟨1, 1, by norm_num, ?_⟩
    intro θ hθ rate hrate τ₀ hτ₀ _hτ₀le α
    exact False.elim (collisionPair_impossible hnSmall α)
  · have hn : 2 ≤ n := by omega
    let m : ℕ := n - 1
    let rate₀ : ℝ := 2 * cscalar + 2
    let a : ℝ := (Real.sqrt (4 * (m : ℝ)))⁻¹
    let M : ℝ := 16 * (m : ℝ)
    let K₀ : ℝ := (8 * Real.pi * Cscalar * collisionEnvelopeTailConstant) *
      ((2 * Real.pi)⁻¹) ^ m
    let C : ℝ := K₀ * M ^ n
    have hm : 0 < m := by dsimp [m]; omega
    have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
    have ha : 0 < a := by dsimp [a]; positivity
    have haSq : a ^ 2 = (4 * (m : ℝ))⁻¹ := by
      dsimp [a]
      rw [inv_pow, Real.sq_sqrt (by positivity)]
    have h4a : 4 * a ^ 2 = 1 / (m : ℝ) := by rw [haSq]; field_simp
    have h2a : 2 * a ^ 2 = 1 / (2 * (m : ℝ)) := by
      rw [haSq]
      field_simp
      norm_num
    have hM : 1 ≤ M := by
      dsimp [M]
      have hmNat : 1 ≤ m := Nat.succ_le_of_lt hm
      have hmRone : 1 ≤ (m : ℝ) := by exact_mod_cast hmNat
      nlinarith
    have hscale : (2 / a) ^ 2 ≤ M := by
      calc (2 / a) ^ 2 = 4 / a ^ 2 := by field_simp [ne_of_gt ha]; norm_num
        _ = 16 * (m : ℝ) := by rw [haSq]; field_simp; ring
        _ = M := rfl
        _ ≤ M := le_rfl
    have htail : 0 < collisionEnvelopeTailConstant := by
      unfold collisionEnvelopeTailConstant
      positivity
    have hK₀pos : 0 < K₀ := by
      dsimp [K₀]
      positivity
    have hCpos : 0 < C := by
      dsimp [C]
      positivity
    have hcard (α : CollisionPair n) : Fintype.card (Spectator α) + 1 = m := by
      dsimp [m]
      rw [card_spectator]
      omega
    have hm_succ : m + 1 = n := by dsimp [m]; omega
    refine ⟨C, rate₀, hCpos, ?_⟩
    intro θ hθ rate hrate τ₀ hτ₀ _hτ₀le α
    have htmin (t : {t : ℝ // τ₀ ≤ t}) : 0 < t.1 := lt_of_lt_of_le hτ₀ t.2
    have hb : 1 ≤ rate - (cscalar + 1) := by
      dsimp [rate₀] at hrate
      nlinarith [hcscalar]
    let b : ℝ := rate - (cscalar + 1)
    let q : ℝ := b / (m : ℝ)
    have hqLower : 1 / (m : ℝ) ≤ q := by
      dsimp [q, b]
      exact div_le_div_of_nonneg_right hb hmR.le
    have hhalf : 1 / (2 * (m : ℝ)) ≤ 1 / (m : ℝ) := by
      field_simp [ne_of_gt hmR]
      norm_num
    have hqCenter : 0 ≤ q - 4 * a ^ 2 := by rw [h4a]; linarith
    have hqSpectator : 0 ≤ q - 2 * a ^ 2 := by rw [h2a]; linarith
    have hqsplit : q * ((Fintype.card (Spectator α) + 1 : ℕ) : ℝ) = b := by
      have hcardR : ((Fintype.card (Spectator α) + 1 : ℕ) : ℝ) = (m : ℝ) := by
        exact_mod_cast hcard α
      rw [hcardR]
      dsimp [q]
      field_simp [ne_of_gt hmR]
    let d : ℝ≥0∞ := ENNReal.ofReal (K₀ * τ₀ ^ (-(n : ℝ)))
    have hd : d ≠ ⊤ := by simp [d]
    have hcollision {t : ℝ} (ht : 0 < t) (hτ₀t : τ₀ ≤ t)
        (y z : FusedConfiguration α) :
        Real.exp (-rate * t) * collisionKernel α θ t y z ≤
          K₀ * τ₀ ^ (-(n : ℝ)) * Real.exp
            (-a * configurationOneNorm
              (fun i => collisionEmbedding α z i - collisionEmbedding α y i)) := by
      have hscalarAt := hscalar θ t hθ ht
      have hscalarDamped := scalarDensity_damped_envelope_le
        (rate := rate) (t := t) (C := Cscalar) (c := cscalar)
        hCscalar.le ht hscalarAt
      have hsplit := exp_damping_split_fused α (t := t) hqsplit
      have hheat := collisionHeatProduct_damped_exp_le α hqCenter hqSpectator
        hτ₀ hτ₀t y z
      have hheatNonneg : 0 ≤ heatKernel (t / 2) (z.1 - y.1) *
          ∏ i : Spectator α, heatKernel t (z.2 i - y.2 i) := by
        apply mul_nonneg
        · exact Critical2DKPZ.heatKernel_nonneg (by positivity) _
        · exact Finset.prod_nonneg fun i hi =>
            Critical2DKPZ.heatKernel_nonneg (by positivity) _
      have hbasePref :
          (4 * Real.pi * Cscalar * collisionEnvelopeTailConstant / t) *
            (2 * ((2 * Real.pi * τ₀)⁻¹) ^ m) *
              Real.exp (-a * configurationOneNorm
                (fun i => collisionEmbedding α z i - collisionEmbedding α y i)) ≤
          (8 * Real.pi * Cscalar * collisionEnvelopeTailConstant *
            ((2 * Real.pi * τ₀)⁻¹) ^ m * τ₀⁻¹) *
              Real.exp (-a * configurationOneNorm
                (fun i => collisionEmbedding α z i - collisionEmbedding α y i)) := by
        have hdiv :
            (8 * Real.pi * Cscalar * collisionEnvelopeTailConstant *
                ((2 * Real.pi * τ₀)⁻¹) ^ m) / t ≤
              (8 * Real.pi * Cscalar * collisionEnvelopeTailConstant *
                ((2 * Real.pi * τ₀)⁻¹) ^ m) / τ₀ :=
          div_le_div_of_nonneg_left (by positivity) hτ₀ hτ₀t
        calc _ = ((8 * Real.pi * Cscalar * collisionEnvelopeTailConstant *
                ((2 * Real.pi * τ₀)⁻¹) ^ m) / t) *
              Real.exp (-a * configurationOneNorm
                (fun i => collisionEmbedding α z i - collisionEmbedding α y i)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hdiv (Real.exp_nonneg _)
          _ = _ := by rw [div_eq_mul_inv]
      calc Real.exp (-rate * t) * collisionKernel α θ t y z
          = (4 * Real.pi) * (Real.exp (-rate * t) * scalarDensity θ t) *
              (heatKernel (t / 2) (z.1 - y.1) *
                ∏ i : Spectator α, heatKernel t (z.2 i - y.2 i)) := by
                rw [collisionKernel]
                ring
        _ ≤ (4 * Real.pi) *
              (Cscalar * collisionEnvelopeTailConstant / t * Real.exp (-b * t)) *
                (heatKernel (t / 2) (z.1 - y.1) *
                  ∏ i : Spectator α, heatKernel t (z.2 i - y.2 i)) := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hscalarDamped (by positivity)) hheatNonneg
        _ = (4 * Real.pi * Cscalar * collisionEnvelopeTailConstant / t) *
              (Real.exp (-b * t) *
                (heatKernel (t / 2) (z.1 - y.1) *
                  ∏ i : Spectator α, heatKernel t (z.2 i - y.2 i))) := by ring
        _ = (4 * Real.pi * Cscalar * collisionEnvelopeTailConstant / t) *
              ((Real.exp (-q * t) * heatKernel (t / 2) (z.1 - y.1)) *
                ∏ i : Spectator α,
                  (Real.exp (-q * t) * heatKernel t (z.2 i - y.2 i))) := by
                rw [hsplit]
                congr 1
                calc
                  (Real.exp (-q * t) * ∏ i : Spectator α, Real.exp (-q * t)) *
                      (heatKernel (t / 2) (z.1 - y.1) *
                        ∏ i : Spectator α, heatKernel t (z.2 i - y.2 i))
                    = (Real.exp (-q * t) * heatKernel (t / 2) (z.1 - y.1)) *
                        ((∏ i : Spectator α, Real.exp (-q * t)) *
                          ∏ i : Spectator α, heatKernel t (z.2 i - y.2 i)) := by ring
                  _ = (Real.exp (-q * t) * heatKernel (t / 2) (z.1 - y.1)) *
                        ∏ i : Spectator α,
                          (Real.exp (-q * t) * heatKernel t (z.2 i - y.2 i)) := by
                        rw [← Finset.prod_mul_distrib]
        _ ≤ (4 * Real.pi * Cscalar * collisionEnvelopeTailConstant / t) *
              (2 * ((2 * Real.pi * τ₀)⁻¹) ^ m) *
                Real.exp (-a * configurationOneNorm
                  (fun i => collisionEmbedding α z i - collisionEmbedding α y i)) := by
                rw [hcard α] at hheat
                simpa only [mul_assoc] using
                  (mul_le_mul_of_nonneg_left hheat
                    (show 0 ≤ 4 * Real.pi * Cscalar *
                      collisionEnvelopeTailConstant / t by positivity))
        _ ≤ (8 * Real.pi * Cscalar * collisionEnvelopeTailConstant *
              ((2 * Real.pi * τ₀)⁻¹) ^ m * τ₀⁻¹) *
                Real.exp (-a * configurationOneNorm
                  (fun i => collisionEmbedding α z i - collisionEmbedding α y i)) := hbasePref
        _ = K₀ * τ₀ ^ (-(n : ℝ)) *
              Real.exp (-a * configurationOneNorm
                (fun i => collisionEmbedding α z i - collisionEmbedding α y i)) := by
                dsimp [K₀]
                calc
                  _ = (8 * Real.pi * Cscalar * collisionEnvelopeTailConstant) *
                      (((2 * Real.pi * τ₀)⁻¹) ^ m * τ₀⁻¹) *
                        Real.exp (-a * configurationOneNorm
                          (fun i => collisionEmbedding α z i - collisionEmbedding α y i)) := by ring
                  _ = (8 * Real.pi * Cscalar * collisionEnvelopeTailConstant) *
                      (((2 * Real.pi)⁻¹) ^ m * τ₀ ^ (-(n : ℝ))) *
                        Real.exp (-a * configurationOneNorm
                          (fun i => collisionEmbedding α z i - collisionEmbedding α y i)) := by
                        rw [collisionSup_scale_eq hm_succ hτ₀]
                  _ = _ := by ring
    have hbase := formBound_fusedFusedExpDecayKernel α α ha hM hscale
    have hscaled := FormBound.const_mul_left hd hbase
    have hsup (y z : FusedConfiguration α) :
        supTimeKernel rate τ₀ (collisionTimeKernel α θ) y z ≤
          d * fusedFusedExpDecayKernel α α a y z := by
      unfold supTimeKernel
      apply iSup_le
      intro t
      have hpoint := hcollision (lt_of_lt_of_le hτ₀ t.2) t.2 y z
      simp only [laplaceTimeWeight, collisionTimeKernel]
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), fusedFusedExpDecayKernel_eq,
        configurationExpDecayKernel_apply]
      rw [← ENNReal.ofReal_mul
        (by positivity : 0 ≤ K₀ * τ₀ ^ (-(n : ℝ)))]
      simpa only [neg_mul] using ENNReal.ofReal_le_ofReal hpoint
    have hconst : d * ENNReal.ofReal (M ^ n) ≤
        ENNReal.ofReal (C * τ₀ ^ (-(n : ℝ))) := by
      dsimp [d, C]
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ K₀ * τ₀ ^ (-(n : ℝ)))]
      apply ENNReal.ofReal_le_ofReal
      apply le_of_eq
      ring
    apply hscaled.mono hsup hconst

end Critical2DKPZ.DeltaBose
