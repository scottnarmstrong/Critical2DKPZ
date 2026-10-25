/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Smoothing.ProfileL2Perturbation
public import Critical2DKPZ.Smoothing.KernelVariation
import Mathlib.Tactic

/-! # First-collision bounds for changing a finite initial profile -/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.Smoothing

/-- The squared difference of two flat profiles is integrable for finite initial supports. -/
theorem integrable_probability_profile_difference_sq (β : ℝ) (a n : ℕ)
    (ν ν' : Site → ℝ) (A : Finset Site)
    (hν : ∀ w ∉ A, ν w = 0) (hν' : ∀ w ∉ A, ν' w = 0) :
    Integrable (fun ω => (profileP2Fun β a (a + n) ν (fun _ => 1) ω -
      profileP2Fun β a (a + n) ν' (fun _ => 1) ω) ^ 2) disorderLaw := by
  have hνmem := Polymer.memLp_profileP2Fun_finset β a (a + n) ν (fun _ => 1)
    A hν 2 (by norm_num)
  have hν'mem := Polymer.memLp_profileP2Fun_finset β a (a + n) ν' (fun _ => 1)
    A hν' 2 (by norm_num)
  have hdiff := (hνmem.sub hν'mem).integrable_norm_pow'
  change Integrable (fun ω =>
    ((profileP2Fun β a (a + n) ν (fun _ => 1) -
      profileP2Fun β a (a + n) ν' (fun _ => 1)) ω) ^ 2) disorderLaw
  simpa only [Real.norm_eq_abs, sq_abs, Pi.sub_apply] using hdiff


/-- A nonnegative finite initial profile has an integrable flat-profile square, bounded by its
mass squared times the first-collision sum with the even-time kernel cap. -/
theorem integral_nonnegative_profile_sq_le (β : ℝ) (a T : ℕ)
    (μ : Site → ℝ) (A : Finset Site)
    (hμ : ∀ w ∉ A, μ w = 0) (hμ0 : ∀ w, 0 ≤ μ w) :
    Integrable (fun ω => profileP2Fun β a (a + T) μ (fun _ => 1) ω ^ 2) disorderLaw ∧
      (∫ ω, profileP2Fun β a (a + T) μ (fun _ => 1) ω ^ 2 ∂disorderLaw) ≤
        (∑ w ∈ A, μ w) ^ 2 *
          (1 + ∑ r ∈ Finset.Icc 1 T,
            Polymer.sigmaSq β *
              (∫ ω, pointToPlane β 0 (T - r) 0 ω ^ 2 ∂disorderLaw) /
                ((r : ℝ) + 1)) := by
  classical
  let Z : Disorder → ℝ := profileP2Fun β a (a + T) μ (fun _ => 1)
  let τ : ℝ := ∑ w ∈ A, μ w
  have hZint : Integrable (fun ω => Z ω ^ 2) disorderLaw := by
    have h := integrable_probability_profile_difference_sq β a T μ (fun _ => 0) A hμ
      (by intro w hw; rfl)
    have hzero (ω : Disorder) :
        profileP2Fun β a (a + T) (fun _ => 0) (fun _ => 1) ω = 0 := by
      simp [profileP2Fun]
    simpa [Z, hzero] using h
  have hfc := Polymer.profile_firstCollision_finset β a T μ μ A A hμ hμ
  have hformula :
      (∫ ω, Z ω ^ 2 ∂disorderLaw) - τ ^ 2 =
        ∑ r ∈ Finset.Icc 1 T, ∑ w ∈ A, ∑ v ∈ A,
          μ w * μ v * srwKernel (2 * r) (v - w) * Polymer.sigmaSq β *
            (∫ ω, pointToPlane β 0 (T - r) 0 ω ^ 2 ∂disorderLaw) := by
    dsimp [Z, τ]
    simpa only [pow_two] using hfc
  have hσ : 0 ≤ Polymer.sigmaSq β := by
    unfold Polymer.sigmaSq
    exact sub_nonneg.mpr (Real.one_le_exp (sq_nonneg β))
  have hmoment (r : ℕ) :
      0 ≤ ∫ ω, pointToPlane β 0 (T - r) 0 ω ^ 2 ∂disorderLaw :=
    integral_nonneg fun ω => sq_nonneg _
  have hcollision (r : ℕ) :
      (∑ w ∈ A, ∑ v ∈ A,
        μ w * μ v * srwKernel (2 * r) (v - w) * Polymer.sigmaSq β *
          (∫ ω, pointToPlane β 0 (T - r) 0 ω ^ 2 ∂disorderLaw)) ≤
        τ ^ 2 * (Polymer.sigmaSq β *
          (∫ ω, pointToPlane β 0 (T - r) 0 ω ^ 2 ∂disorderLaw) /
            ((r : ℝ) + 1)) := by
    have hcoeff : 0 ≤ Polymer.sigmaSq β *
        (∫ ω, pointToPlane β 0 (T - r) 0 ω ^ 2 ∂disorderLaw) :=
      mul_nonneg hσ (hmoment r)
    have hterm (w v : Site) :
        μ w * μ v * srwKernel (2 * r) (v - w) * Polymer.sigmaSq β *
          (∫ ω, pointToPlane β 0 (T - r) 0 ω ^ 2 ∂disorderLaw) ≤
        μ w * μ v * (Polymer.sigmaSq β *
          (∫ ω, pointToPlane β 0 (T - r) 0 ω ^ 2 ∂disorderLaw) /
            ((r : ℝ) + 1)) := by
      calc
        _ = μ w * μ v * (srwKernel (2 * r) (v - w) *
            (Polymer.sigmaSq β *
              (∫ ω, pointToPlane β 0 (T - r) 0 ω ^ 2 ∂disorderLaw))) := by ring
        _ ≤ μ w * μ v * ((1 / ((r : ℝ) + 1)) *
            (Polymer.sigmaSq β *
              (∫ ω, pointToPlane β 0 (T - r) 0 ω ^ 2 ∂disorderLaw))) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hμ0 w) (hμ0 v))
          exact mul_le_mul_of_nonneg_right
            (srwKernel_even_le_inv_succ r (v - w)) hcoeff
        _ = _ := by ring
    calc
      _ ≤ ∑ w ∈ A, ∑ v ∈ A,
          μ w * μ v * (Polymer.sigmaSq β *
            (∫ ω, pointToPlane β 0 (T - r) 0 ω ^ 2 ∂disorderLaw) /
              ((r : ℝ) + 1)) := by
          apply Finset.sum_le_sum
          intro w hw
          apply Finset.sum_le_sum
          intro v hv
          exact hterm w v
      _ = τ ^ 2 * (Polymer.sigmaSq β *
          (∫ ω, pointToPlane β 0 (T - r) 0 ω ^ 2 ∂disorderLaw) /
            ((r : ℝ) + 1)) := by
          let C : ℝ := Polymer.sigmaSq β *
            (∫ ω, pointToPlane β 0 (T - r) 0 ω ^ 2 ∂disorderLaw) /
              ((r : ℝ) + 1)
          calc
            _ = (∑ w ∈ A, μ w) * (∑ v ∈ A, μ v) * C := by
              calc
                _ = ∑ w ∈ A, ((μ w * (∑ v ∈ A, μ v)) * C) := by
                  apply Finset.sum_congr rfl
                  intro w hw
                  calc
                    ∑ v ∈ A, μ w * μ v * C =
                        (∑ v ∈ A, μ w * μ v) * C := by rw [Finset.sum_mul]
                    _ = (μ w * (∑ v ∈ A, μ v)) * C := by rw [← Finset.mul_sum]
                _ = _ := by rw [Finset.sum_mul, Finset.sum_mul]
            _ = _ := by dsimp [τ, C]; ring
  have hCnonneg : 0 ≤ ∑ r ∈ Finset.Icc 1 T,
      Polymer.sigmaSq β *
        (∫ ω, pointToPlane β 0 (T - r) 0 ω ^ 2 ∂disorderLaw) / ((r : ℝ) + 1) := by
    apply Finset.sum_nonneg
    intro r hr
    exact div_nonneg (mul_nonneg hσ (hmoment r)) (by positivity)
  have htotal :
      ∑ r ∈ Finset.Icc 1 T, ∑ w ∈ A, ∑ v ∈ A,
        μ w * μ v * srwKernel (2 * r) (v - w) * Polymer.sigmaSq β *
          (∫ ω, pointToPlane β 0 (T - r) 0 ω ^ 2 ∂disorderLaw) ≤
        τ ^ 2 * ∑ r ∈ Finset.Icc 1 T,
          Polymer.sigmaSq β *
            (∫ ω, pointToPlane β 0 (T - r) 0 ω ^ 2 ∂disorderLaw) / ((r : ℝ) + 1) := by
    calc
      _ ≤ ∑ r ∈ Finset.Icc 1 T, τ ^ 2 *
          (Polymer.sigmaSq β *
            (∫ ω, pointToPlane β 0 (T - r) 0 ω ^ 2 ∂disorderLaw) /
              ((r : ℝ) + 1)) := by
          apply Finset.sum_le_sum
          intro r hr
          exact hcollision r
      _ = _ := by rw [← Finset.mul_sum]
  refine ⟨hZint, ?_⟩
  have hmomentEq :
      (∫ ω, Z ω ^ 2 ∂disorderLaw) = τ ^ 2 +
        ∑ r ∈ Finset.Icc 1 T, ∑ w ∈ A, ∑ v ∈ A,
          μ w * μ v * srwKernel (2 * r) (v - w) * Polymer.sigmaSq β *
            (∫ ω, pointToPlane β 0 (T - r) 0 ω ^ 2 ∂disorderLaw) := by
    linarith [hformula]
  rw [hmomentEq]
  calc
    _ ≤ τ ^ 2 + τ ^ 2 * ∑ r ∈ Finset.Icc 1 T,
        Polymer.sigmaSq β *
          (∫ ω, pointToPlane β 0 (T - r) 0 ω ^ 2 ∂disorderLaw) / ((r : ℝ) + 1) :=
      add_le_add (le_refl (τ ^ 2)) htotal
    _ = _ := by ring

/-- A bounded terminal observable inherits the same first-collision control when its finite initial
profile is changed. The bound uses the total variation of the signed profile difference. -/
theorem integral_profileP2Fun_initial_difference_sq_le (β : ℝ) (a T : ℕ)
    (ν ν' : Site → ℝ) (A : Finset Site)
    (hν : ∀ w ∉ A, ν w = 0) (hν' : ∀ w ∉ A, ν' w = 0)
    (f : Site → ℝ) (F : ℝ) (hF : 0 ≤ F) (hf : ∀ z, |f z| ≤ F) :
    Integrable (fun ω =>
      (profileP2Fun β a (a + T) ν f ω - profileP2Fun β a (a + T) ν' f ω) ^ 2)
        disorderLaw ∧
    (∫ ω,
      (profileP2Fun β a (a + T) ν f ω - profileP2Fun β a (a + T) ν' f ω) ^ 2
        ∂disorderLaw) ≤
      F ^ 2 * (∑ w ∈ A, |ν w - ν' w|) ^ 2 *
        (1 + ∑ r ∈ Finset.Icc 1 T,
          Polymer.sigmaSq β *
            (∫ ω, pointToPlane β 0 (T - r) 0 ω ^ 2 ∂disorderLaw) /
              ((r : ℝ) + 1)) := by
  classical
  let μ : Site → ℝ := fun w => |ν w - ν' w|
  let τ : ℝ := ∑ w ∈ A, μ w
  have hμ (w : Site) (hw : w ∉ A) : μ w = 0 := by
    simp [μ, hν w hw, hν' w hw]
  have hμ0 (w : Site) : 0 ≤ μ w := by simp [μ]
  have hmass := integral_nonnegative_profile_sq_le β a T μ A hμ hμ0
  have hνmem := Polymer.memLp_profileP2Fun_finset β a (a + T) ν f A hν 2 (by norm_num)
  have hν'mem := Polymer.memLp_profileP2Fun_finset β a (a + T) ν' f A hν' 2
    (by norm_num)
  have hdiffInt : Integrable (fun ω =>
      (profileP2Fun β a (a + T) ν f ω - profileP2Fun β a (a + T) ν' f ω) ^ 2)
      disorderLaw := by
    have h := (hνmem.sub hν'mem).integrable_norm_pow'
    change Integrable (fun ω =>
      ((profileP2Fun β a (a + T) ν f - profileP2Fun β a (a + T) ν' f) ω) ^ 2)
      disorderLaw
    simpa only [Real.norm_eq_abs, sq_abs, Pi.sub_apply] using h
  have hZnonneg (ω : Disorder) :
      0 ≤ profileP2Fun β a (a + T) μ (fun _ => 1) ω := by
    rw [Polymer.profileP2Fun_flat_eq_sum β a T μ A hμ ω]
    apply Finset.sum_nonneg
    intro w hw
    exact mul_nonneg (hμ0 w) (Polymer.pointToPlane_pos β a T w ω).le
  have hrepr (ω : Disorder) :
      profileP2Fun β a (a + T) ν f ω - profileP2Fun β a (a + T) ν' f ω =
        ∑ w ∈ A, (ν w - ν' w) *
          (∑' z, pointToPoint β a T w z ω * f z) := by
    rw [Polymer.profileP2Fun_eq_sum β a (a + T) ν f A hν ω,
      Polymer.profileP2Fun_eq_sum β a (a + T) ν' f A hν' ω]
    simp only [Nat.add_sub_cancel_left]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro w hw
    ring
  have hmajor (ω : Disorder) :
      |profileP2Fun β a (a + T) ν f ω - profileP2Fun β a (a + T) ν' f ω| ≤
        F * profileP2Fun β a (a + T) μ (fun _ => 1) ω := by
    rw [hrepr]
    calc
      _ ≤ ∑ w ∈ A,
          |(ν w - ν' w) * (∑' z, pointToPoint β a T w z ω * f z)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ w ∈ A, μ w * (F * pointToPlane β a T w ω) := by
          apply Finset.sum_le_sum
          intro w hw
          rw [abs_mul]
          calc
            _ ≤ μ w * |∑' z, pointToPoint β a T w z ω * f z| := by rfl
            _ ≤ μ w * (F * pointToPlane β a T w ω) :=
              mul_le_mul_of_nonneg_left
                (Polymer.terminalProfile_abs_le β a T w f F hf ω) (hμ0 w)
      _ = F * ∑ w ∈ A, μ w * pointToPlane β a T w ω := by
          calc
            _ = ∑ w ∈ A, F * (μ w * pointToPlane β a T w ω) := by
              apply Finset.sum_congr rfl
              intro w hw
              ring
            _ = _ := by rw [← Finset.mul_sum]
      _ = F * profileP2Fun β a (a + T) μ (fun _ => 1) ω := by
          rw [Polymer.profileP2Fun_flat_eq_sum β a T μ A hμ ω]
  have hpointSq (ω : Disorder) :
      (profileP2Fun β a (a + T) ν f ω - profileP2Fun β a (a + T) ν' f ω) ^ 2 ≤
        F ^ 2 * profileP2Fun β a (a + T) μ (fun _ => 1) ω ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hF (hZnonneg ω))).2 (hmajor ω)
    simpa only [sq_abs, mul_pow] using h
  have hmajorInt : Integrable (fun ω =>
      F ^ 2 * profileP2Fun β a (a + T) μ (fun _ => 1) ω ^ 2) disorderLaw := by
    simpa [mul_comm] using hmass.1.const_mul (F ^ 2)
  have hI := integral_mono hdiffInt hmajorInt hpointSq
  refine ⟨hdiffInt, ?_⟩
  calc
    _ ≤ F ^ 2 *
        (∫ ω, profileP2Fun β a (a + T) μ (fun _ => 1) ω ^ 2 ∂disorderLaw) := by
          simpa only [integral_const_mul] using hI
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left hmass.2
      exact sq_nonneg F
    _ = _ := by
      dsimp [τ, μ]
      ring

/-- A finite support realization of the total variation between two translated, even-time walk
kernels. Its bound is the multistep kernel variation estimate. -/
theorem walkKernel_initialVariation_le {p q : ℕ} (hpq : p ≤ q) (x : Site) :
    (∑ w ∈ (Polymer.endpoints x (2 * p) ∪ Polymer.endpoints x (2 * q)),
      |srwKernel (2 * q) (w - x) - srwKernel (2 * p) (w - x)|) ≤
        2 * ((q - p : ℕ) : ℝ) / Real.sqrt ((p : ℝ) + 1) := by
  classical
  let A := Polymer.endpoints x (2 * p) ∪ Polymer.endpoints x (2 * q)
  have hzero (w : Site) (hw : w ∉ A) :
      |srwKernel (2 * q) (w - x) - srwKernel (2 * p) (w - x)| = 0 := by
    have hq : w ∉ Polymer.endpoints x (2 * q) := by
      intro h
      exact hw (Finset.mem_union.mpr (Or.inr h))
    have hp : w ∉ Polymer.endpoints x (2 * p) := by
      intro h
      exact hw (Finset.mem_union.mpr (Or.inl h))
    rw [Polymer.srwKernel_eq_zero_of_not_mem (2 * q) x w hq,
      Polymer.srwKernel_eq_zero_of_not_mem (2 * p) x w hp]
    simp
  have hsum :
      (∑ w ∈ A, |srwKernel (2 * q) (w - x) - srwKernel (2 * p) (w - x)|) =
        ∑' w : Site, |srwKernel (2 * q) (w - x) - srwKernel (2 * p) (w - x)| := by
    symm
    exact tsum_eq_sum hzero
  calc
    _ = ∑' w : Site,
        |srwKernel (2 * q) (w - x) - srwKernel (2 * p) (w - x)| := by
          simpa only [A] using hsum
    _ = ∑' z : Site, |srwKernel (2 * q) z - srwKernel (2 * p) z| := by
          exact Equiv.tsum_eq (Equiv.subRight x)
            (fun z : Site => |srwKernel (2 * q) z - srwKernel (2 * p) z|)
    _ ≤ 2 * ((q - p : ℕ) : ℝ) / Real.sqrt ((p : ℝ) + 1) :=
          srwKernel_even_timeVariation_le_of_le hpq



end Critical2DKPZ.Smoothing

end
