/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Smoothing.WidthLogL2
public import Critical2DKPZ.Smoothing.CenteredWidthLogL2
public import Critical2DKPZ.Smoothing.ProfileInverseL1
public import Critical2DKPZ.Smoothing.ProfileKernelPerturbation
public import Critical2DKPZ.Smoothing.WidthCollisionControl
import Mathlib.Tactic

/-! # Width stability with explicit inverse-moment bounds -/

@[expose] public section

open MeasureTheory Filter
open scoped BigOperators ENNReal

namespace Critical2DKPZ.Smoothing

/-- A bounded positive terminal weight preserves the explicit collision estimate for a change of
walk-kernel width, once the flat-profile second moments are bounded. -/
theorem eLpNorm_log_walkKernel_profile_difference_le_of_inverseMoment
    (β : ℝ) (hβ : 0 ≤ β) (a T p q : ℕ) (x : Site) (f : Site → ℝ)
    (H F Q : ℝ) (_hH : 0 ≤ H) (hF : 0 ≤ F)
    (hfb : ∀ z, |f z| ≤ F)
    (hf : ∀ z, 0 < f z ∧ |Real.log (f z)| ≤ H)
    (hflatq : Integrable (fun ω => profileP2Fun β a (a + T)
        (fun w => srwKernel (2 * q) (w - x)) (fun _ => 1) ω ^ 2) disorderLaw ∧
      (∫ ω, profileP2Fun β a (a + T)
        (fun w => srwKernel (2 * q) (w - x)) (fun _ => 1) ω ^ 2 ∂disorderLaw) ≤ Q)
    (hflatp : Integrable (fun ω => profileP2Fun β a (a + T)
        (fun w => srwKernel (2 * p) (w - x)) (fun _ => 1) ω ^ 2) disorderLaw ∧
      (∫ ω, profileP2Fun β a (a + T)
        (fun w => srwKernel (2 * p) (w - x)) (fun _ => 1) ω ^ 2 ∂disorderLaw) ≤ Q) :
    eLpNorm (fun ω =>
      Real.log (profileP2Fun β a (a + T)
        (fun w => srwKernel (2 * q) (w - x)) f ω) -
      Real.log (profileP2Fun β a (a + T)
        (fun w => srwKernel (2 * p) (w - x)) f ω)) 2 disorderLaw ≤
      ENNReal.ofReal logHolderConstant *
        ENNReal.ofReal (Real.sqrt (F ^ 2 *
          (∑ w ∈ (Polymer.endpoints x (2 * p) ∪ Polymer.endpoints x (2 * q)),
            |srwKernel (2 * q) (w - x) - srwKernel (2 * p) (w - x)|) ^ 2 *
          (1 + ∑ r ∈ Finset.Icc 1 T,
            Polymer.sigmaSq β *
              (∫ ω, pointToPlane β 0 (T - r) 0 ω ^ 2 ∂disorderLaw) /
                ((r : ℝ) + 1)))) ^ ((1 : ℝ) / 3) *
        (2 * (ENNReal.ofReal (Real.exp H * Q)) ^ ((1 : ℝ) / 3)) := by
  classical
  let νq : Site → ℝ := fun w => srwKernel (2 * q) (w - x)
  let νp : Site → ℝ := fun w => srwKernel (2 * p) (w - x)
  let A : Finset Site := Polymer.endpoints x (2 * p) ∪ Polymer.endpoints x (2 * q)
  have hνqA : ∀ w ∉ A, νq w = 0 := by
    intro w hw
    exact Polymer.srwKernel_eq_zero_of_not_mem (2 * q) x w (by
      intro hwq
      exact hw (Finset.mem_union_right _ hwq))
  have hνpA : ∀ w ∉ A, νp w = 0 := by
    intro w hw
    exact Polymer.srwKernel_eq_zero_of_not_mem (2 * p) x w (by
      intro hwp
      exact hw (Finset.mem_union_left _ hwp))
  have hνq0 : ∀ w, 0 ≤ νq w := fun w => Polymer.kernel_nonneg (2 * q) (w - x)
  have hνp0 : ∀ w, 0 ≤ νp w := fun w => Polymer.kernel_nonneg (2 * p) (w - x)
  have hνq1 : ∑ w ∈ A, νq w = 1 := by
    dsimp [νq, A]
    calc
      _ = ∑ w ∈ Polymer.endpoints x (2 * q), srwKernel (2 * q) (w - x) := by
        symm
        apply Finset.sum_subset Finset.subset_union_right
        intro w hw hnot
        exact Polymer.srwKernel_eq_zero_of_not_mem (2 * q) x w hnot
      _ = 1 := Polymer.sum_srwKernel_endpoints (2 * q) x
  have hνp1 : ∑ w ∈ A, νp w = 1 := by
    dsimp [νp, A]
    calc
      _ = ∑ w ∈ Polymer.endpoints x (2 * p), srwKernel (2 * p) (w - x) := by
        symm
        apply Finset.sum_subset Finset.subset_union_left
        intro w hw hnot
        exact Polymer.srwKernel_eq_zero_of_not_mem (2 * p) x w hnot
      _ = 1 := Polymer.sum_srwKernel_endpoints (2 * p) x
  have hνqpos : ∃ w ∈ A, 0 < νq w := by
    have hsum : 0 < ∑ w ∈ A, νq w := by rw [hνq1]; norm_num
    exact (Finset.sum_pos_iff_of_nonneg (fun w hw => hνq0 w)).mp hsum
  have hνppos : ∃ w ∈ A, 0 < νp w := by
    have hsum : 0 < ∑ w ∈ A, νp w := by rw [hνp1]; norm_num
    exact (Finset.sum_pos_iff_of_nonneg (fun w hw => hνp0 w)).mp hsum
  have hQ : 0 ≤ Q := le_trans (integral_nonneg fun ω => sq_nonneg
    (profileP2Fun β a (a + T) νq (fun _ => 1) ω)) hflatq.2
  have hqInv := eLpNorm_inv_profile_terminal_le_of_secondMoment β hβ a (a + T)
    νq A hνqA hνq0 hνq1 f H hf Q (by simpa [νq] using hflatq)
  have hpInv := eLpNorm_inv_profile_terminal_le_of_secondMoment β hβ a (a + T)
    νp A hνpA hνp0 hνp1 f H hf Q (by simpa [νp] using hflatp)
  have hraw := eLpNorm_log_walkKernel_profile_difference_le_collision β a T p q x f F H
    hF hfb hf
  calc
    _ ≤ ENNReal.ofReal logHolderConstant *
          ENNReal.ofReal (Real.sqrt (F ^ 2 *
            (∑ w ∈ (Polymer.endpoints x (2 * p) ∪ Polymer.endpoints x (2 * q)),
              |srwKernel (2 * q) (w - x) - srwKernel (2 * p) (w - x)|) ^ 2 *
            (1 + ∑ r ∈ Finset.Icc 1 T,
              Polymer.sigmaSq β *
                (∫ ω, pointToPlane β 0 (T - r) 0 ω ^ 2 ∂disorderLaw) /
                  ((r : ℝ) + 1)))) ^ ((1 : ℝ) / 3) *
          (eLpNorm (fun ω => (profileP2Fun β a (a + T)
              (fun w => srwKernel (2 * q) (w - x)) f ω)⁻¹) 1 disorderLaw ^
                ((1 : ℝ) / 3) +
            eLpNorm (fun ω => (profileP2Fun β a (a + T)
              (fun w => srwKernel (2 * p) (w - x)) f ω)⁻¹) 1 disorderLaw ^
                ((1 : ℝ) / 3)) := hraw
    _ ≤ ENNReal.ofReal logHolderConstant *
          ENNReal.ofReal (Real.sqrt (F ^ 2 *
            (∑ w ∈ (Polymer.endpoints x (2 * p) ∪ Polymer.endpoints x (2 * q)),
              |srwKernel (2 * q) (w - x) - srwKernel (2 * p) (w - x)|) ^ 2 *
            (1 + ∑ r ∈ Finset.Icc 1 T,
              Polymer.sigmaSq β *
                (∫ ω, pointToPlane β 0 (T - r) 0 ω ^ 2 ∂disorderLaw) /
                  ((r : ℝ) + 1)))) ^ ((1 : ℝ) / 3) *
          (2 * (ENNReal.ofReal (Real.exp H * Q)) ^ ((1 : ℝ) / 3)) := by
      have hqpow := ENNReal.rpow_le_rpow hqInv (by norm_num : 0 ≤ (1 : ℝ) / 3)
      have hppow := ENNReal.rpow_le_rpow hpInv (by norm_num : 0 ≤ (1 : ℝ) / 3)
      have hsum :
          eLpNorm (fun ω => (profileP2Fun β a (a + T)
              (fun w => srwKernel (2 * q) (w - x)) f ω)⁻¹) 1 disorderLaw ^
                ((1 : ℝ) / 3) +
            eLpNorm (fun ω => (profileP2Fun β a (a + T)
              (fun w => srwKernel (2 * p) (w - x)) f ω)⁻¹) 1 disorderLaw ^
                ((1 : ℝ) / 3) ≤
          2 * (ENNReal.ofReal (Real.exp H * Q)) ^ ((1 : ℝ) / 3) := by
        calc
          _ ≤ (ENNReal.ofReal (Real.exp H * Q)) ^ ((1 : ℝ) / 3) +
              (ENNReal.ofReal (Real.exp H * Q)) ^ ((1 : ℝ) / 3) := by
                exact add_le_add (by simpa only [νq] using hqpow)
                  (by simpa only [νp] using hppow)
          _ = _ := by rw [← two_mul]
      exact mul_le_mul_of_nonneg_left hsum (by positivity)

/-- Centering the two terminal profiles preserves the explicit width bound, with one contribution
from the weighted profiles and one from the flat profiles. -/
theorem eLpNorm_centered_log_walkKernel_profile_difference_le_of_inverseMoment
    (β : ℝ) (hβ : 0 ≤ β) (a T p q : ℕ) (x : Site) (f : Site → ℝ)
    (H F Q : ℝ) (hH : 0 ≤ H) (hF : 0 ≤ F)
    (hfb : ∀ z, |f z| ≤ F)
    (hf : ∀ z, 0 < f z ∧ |Real.log (f z)| ≤ H)
    (hflatq : Integrable (fun ω => profileP2Fun β a (a + T)
        (fun w => srwKernel (2 * q) (w - x)) (fun _ => 1) ω ^ 2) disorderLaw ∧
      (∫ ω, profileP2Fun β a (a + T)
        (fun w => srwKernel (2 * q) (w - x)) (fun _ => 1) ω ^ 2 ∂disorderLaw) ≤ Q)
    (hflatp : Integrable (fun ω => profileP2Fun β a (a + T)
        (fun w => srwKernel (2 * p) (w - x)) (fun _ => 1) ω ^ 2) disorderLaw ∧
      (∫ ω, profileP2Fun β a (a + T)
        (fun w => srwKernel (2 * p) (w - x)) (fun _ => 1) ω ^ 2 ∂disorderLaw) ≤ Q) :
    eLpNorm (fun ω =>
      (Real.log (profileP2Fun β a (a + T)
          (fun w => srwKernel (2 * q) (w - x)) f ω) -
        Real.log (profileP2Fun β a (a + T)
          (fun w => srwKernel (2 * p) (w - x)) f ω) -
        (∫ ω', Real.log (profileP2Fun β a (a + T)
            (fun w => srwKernel (2 * q) (w - x)) (fun _ => 1) ω') -
          Real.log (profileP2Fun β a (a + T)
            (fun w => srwKernel (2 * p) (w - x)) (fun _ => 1) ω')
            ∂disorderLaw))) 2 disorderLaw ≤
      (ENNReal.ofReal logHolderConstant *
        ENNReal.ofReal (Real.sqrt (F ^ 2 *
          (∑ w ∈ (Polymer.endpoints x (2 * p) ∪ Polymer.endpoints x (2 * q)),
            |srwKernel (2 * q) (w - x) - srwKernel (2 * p) (w - x)|) ^ 2 *
          (1 + ∑ r ∈ Finset.Icc 1 T,
            Polymer.sigmaSq β *
              (∫ ω, pointToPlane β 0 (T - r) 0 ω ^ 2 ∂disorderLaw) /
                ((r : ℝ) + 1)))) ^ ((1 : ℝ) / 3) *
        (2 * (ENNReal.ofReal (Real.exp H * Q)) ^ ((1 : ℝ) / 3))) +
      (ENNReal.ofReal logHolderConstant *
        ENNReal.ofReal (Real.sqrt (
          (∑ w ∈ (Polymer.endpoints x (2 * p) ∪ Polymer.endpoints x (2 * q)),
            |srwKernel (2 * q) (w - x) - srwKernel (2 * p) (w - x)|) ^ 2 *
          (1 + ∑ r ∈ Finset.Icc 1 T,
            Polymer.sigmaSq β *
              (∫ ω, pointToPlane β 0 (T - r) 0 ω ^ 2 ∂disorderLaw) /
                ((r : ℝ) + 1)))) ^ ((1 : ℝ) / 3) *
        (2 * (ENNReal.ofReal Q) ^ ((1 : ℝ) / 3))) := by
  have hcenter := eLpNorm_centered_log_walkKernel_profile_difference_le β a T p q x f H hH hf
  have hweighted := eLpNorm_log_walkKernel_profile_difference_le_of_inverseMoment
    β hβ a T p q x f H F Q hH hF hfb hf hflatq hflatp
  have hflatBound := eLpNorm_log_walkKernel_profile_difference_le_of_inverseMoment
    β hβ a T p q x (fun _ => 1) 0 1 Q (by norm_num) (by norm_num)
    (by intro z; norm_num) (by intro z; constructor <;> norm_num)
    hflatq hflatp
  apply hcenter.trans
  exact add_le_add hweighted (by
    simpa only [one_pow, one_mul, Real.exp_zero] using hflatBound)

/-- A uniform collision bound gives a centered logarithmic width estimate for bounded positive
terminal weights. The flat-profile second moments in the argument carry their integrability
companions. -/
theorem eLpNorm_centered_log_walkKernel_profile_difference_le_collision_uniform
    (A H F : ℝ) (hH : 0 ≤ H) (hF : 0 ≤ F)
    :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ M : ℕ in atTop,
      ∀ ϑ ∈ Set.Icc (-A) A, ∀ f : Site → ℝ,
        (∀ z, |f z| ≤ F) → (∀ z, 0 < f z ∧ |Real.log (f z)| ≤ H) →
        ∀ a T p q : ℕ, a + T ≤ M → ∀ x : Site,
        eLpNorm (fun ω =>
          (Real.log (profileP2Fun (criticalBeta ϑ M) a (a + T)
              (fun w => srwKernel (2 * q) (w - x)) f ω) -
            Real.log (profileP2Fun (criticalBeta ϑ M) a (a + T)
              (fun w => srwKernel (2 * p) (w - x)) f ω)) -
            (∫ ω', (Real.log (profileP2Fun (criticalBeta ϑ M) a (a + T)
                (fun w => srwKernel (2 * q) (w - x)) (fun _ => 1) ω') -
              Real.log (profileP2Fun (criticalBeta ϑ M) a (a + T)
                (fun w => srwKernel (2 * p) (w - x)) (fun _ => 1) ω'))
              ∂disorderLaw)) 2 disorderLaw ≤
          (ENNReal.ofReal logHolderConstant *
            ENNReal.ofReal (Real.sqrt (F ^ 2 *
              (∑ w ∈ (Polymer.endpoints x (2 * p) ∪ Polymer.endpoints x (2 * q)),
                |srwKernel (2 * q) (w - x) - srwKernel (2 * p) (w - x)|) ^ 2 *
              ((C + 1) * (1 + Real.log ((M : ℝ) + 1))))) ^ ((1 : ℝ) / 3) *
            (2 * (ENNReal.ofReal (Real.exp H * C * (1 + Real.log ((M : ℝ) + 1))) ^
              ((1 : ℝ) / 3))) +
          ENNReal.ofReal logHolderConstant *
            ENNReal.ofReal (Real.sqrt (
              (∑ w ∈ (Polymer.endpoints x (2 * p) ∪ Polymer.endpoints x (2 * q)),
                |srwKernel (2 * q) (w - x) - srwKernel (2 * p) (w - x)|) ^ 2 *
              ((C + 1) * (1 + Real.log ((M : ℝ) + 1))))) ^ ((1 : ℝ) / 3) *
            (2 * (ENNReal.ofReal (C * (1 + Real.log ((M : ℝ) + 1))) ^
              ((1 : ℝ) / 3)))) := by
  obtain ⟨Cflat, hCflat, hflat⟩ :=
    integral_walkKernel_flat_profile_sq_le_log_uniform A
  obtain ⟨Ccoll, hCcoll, hcollision⟩ :=
    critical_walkKernel_collision_sum_le_log_uniform A
  let C : ℝ := max Cflat Ccoll
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [hflat, hcollision] with M hflatM hcollisionM
  intro ϑ hϑ f hfb hf a T p q haTM x
  have hTM : T ≤ M := by omega
  have hlog : 0 ≤ Real.log ((M : ℝ) + 1) :=
    Real.log_nonneg (by have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg _; linarith)
  have hQ : Cflat * (1 + Real.log ((M : ℝ) + 1)) ≤
      C * (1 + Real.log ((M : ℝ) + 1)) := by
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
  have hflatq : Integrable (fun ω => profileP2Fun (criticalBeta ϑ M) a (a + T)
      (fun w => srwKernel (2 * q) (w - x)) (fun _ => 1) ω ^ 2) disorderLaw ∧
      (∫ ω, profileP2Fun (criticalBeta ϑ M) a (a + T)
        (fun w => srwKernel (2 * q) (w - x)) (fun _ => 1) ω ^ 2 ∂disorderLaw) ≤
        C * (1 + Real.log ((M : ℝ) + 1)) := by
    have h := hflatM ϑ hϑ a T q hTM x
    exact ⟨h.1, h.2.trans hQ⟩
  have hflatp : Integrable (fun ω => profileP2Fun (criticalBeta ϑ M) a (a + T)
      (fun w => srwKernel (2 * p) (w - x)) (fun _ => 1) ω ^ 2) disorderLaw ∧
      (∫ ω, profileP2Fun (criticalBeta ϑ M) a (a + T)
        (fun w => srwKernel (2 * p) (w - x)) (fun _ => 1) ω ^ 2 ∂disorderLaw) ≤
        C * (1 + Real.log ((M : ℝ) + 1)) := by
    have h := hflatM ϑ hϑ a T p hTM x
    exact ⟨h.1, h.2.trans hQ⟩
  have hcollision := hcollisionM ϑ hϑ T hTM
  have hcollisionBound :
      1 + ∑ r ∈ Finset.Icc 1 T,
        Polymer.sigmaSq (criticalBeta ϑ M) *
          (∫ ω, pointToPlane (criticalBeta ϑ M) 0 (T - r) 0 ω ^ 2 ∂disorderLaw) /
            ((r : ℝ) + 1) ≤ (C + 1) * (1 + Real.log ((M : ℝ) + 1)) := by
    have hCcmp : Ccoll ≤ C := le_max_right _ _
    have hmain :
        ∑ r ∈ Finset.Icc 1 T,
          Polymer.sigmaSq (criticalBeta ϑ M) *
            (∫ ω, pointToPlane (criticalBeta ϑ M) 0 (T - r) 0 ω ^ 2 ∂disorderLaw) /
              ((r : ℝ) + 1) ≤ C * (1 + Real.log ((M : ℝ) + 1)) :=
      (hcollisionM ϑ hϑ T hTM).trans
        (mul_le_mul_of_nonneg_right hCcmp (by linarith))
    nlinarith [hmain]
  have hβ : 0 ≤ criticalBeta ϑ M := Real.sqrt_nonneg _
  have hraw := eLpNorm_centered_log_walkKernel_profile_difference_le_of_inverseMoment
    (criticalBeta ϑ M) hβ a T p q x f H F
    (C * (1 + Real.log ((M : ℝ) + 1))) hH hF hfb hf hflatq hflatp
  have hExpArg : Real.exp H *
      (C * (1 + Real.log ((M : ℝ) + 1))) =
      Real.exp H * C * (1 + Real.log ((M : ℝ) + 1)) := by ring
  rw [hExpArg] at hraw
  have hraw' :
      eLpNorm (fun ω =>
        Real.log (profileP2Fun (criticalBeta ϑ M) a (a + T)
            (fun w => srwKernel (2 * q) (w - x)) f ω) -
          Real.log (profileP2Fun (criticalBeta ϑ M) a (a + T)
            (fun w => srwKernel (2 * p) (w - x)) f ω) -
          (∫ ω', Real.log (profileP2Fun (criticalBeta ϑ M) a (a + T)
              (fun w => srwKernel (2 * q) (w - x)) (fun _ => 1) ω') -
            Real.log (profileP2Fun (criticalBeta ϑ M) a (a + T)
              (fun w => srwKernel (2 * p) (w - x)) (fun _ => 1) ω')
              ∂disorderLaw)) 2 disorderLaw ≤
      (ENNReal.ofReal logHolderConstant *
        ENNReal.ofReal (Real.sqrt (F ^ 2 *
          (∑ w ∈ (Polymer.endpoints x (2 * p) ∪ Polymer.endpoints x (2 * q)),
            |srwKernel (2 * q) (w - x) - srwKernel (2 * p) (w - x)|) ^ 2 *
          ((C + 1) * (1 + Real.log ((M : ℝ) + 1))))) ^ ((1 : ℝ) / 3) *
        (2 * (ENNReal.ofReal (Real.exp H * C * (1 + Real.log ((M : ℝ) + 1))) ^
          ((1 : ℝ) / 3))) +
      ENNReal.ofReal logHolderConstant *
        ENNReal.ofReal (Real.sqrt (
          (∑ w ∈ (Polymer.endpoints x (2 * p) ∪ Polymer.endpoints x (2 * q)),
            |srwKernel (2 * q) (w - x) - srwKernel (2 * p) (w - x)|) ^ 2 *
          ((C + 1) * (1 + Real.log ((M : ℝ) + 1))))) ^ ((1 : ℝ) / 3) *
        (2 * (ENNReal.ofReal (C * (1 + Real.log ((M : ℝ) + 1))) ^
          ((1 : ℝ) / 3)))) := by
    apply hraw.trans
    apply add_le_add
    · gcongr
    · gcongr
  exact hraw'

end Critical2DKPZ.Smoothing

end
