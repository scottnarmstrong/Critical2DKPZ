/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.Series
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.Tactic

/-! # First-moment control for summable start profiles -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.JointConvergence

/-- A bounded nonnegative terminal profile turns the `ℓ¹` norm of a summable start profile into
an `L¹` bound for the polymer profile. The accompanying `MemLp` conclusion records
integrability, so the integral bound is meaningful. -/
theorem memLp_one_profileP2Fun_le_of_summable (β : ℝ) (a b : ℕ) (ν f : Site → ℝ)
    (hν : Summable (fun w => |ν w|)) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ z, 0 ≤ f z ∧ f z ≤ M) :
    MemLp (profileP2Fun β a b ν f) 1 disorderLaw ∧
      eLpNorm (profileP2Fun β a b ν f) 1 disorderLaw ≤
        ENNReal.ofReal M * ∑' w, ENNReal.ofReal |ν w| := by
  classical
  let term : Site → Disorder → ℝ := fun w ω =>
    ν w * ∑' z, pointToPoint β a (b - a) w z ω * f z
  let F (w : Site) : Lp ℝ 1 disorderLaw :=
    ((Polymer.memLp_terminalProfile β a (b - a) w f 1 (by simp)).const_mul (ν w)).toLp
      (term w)
  have htermAE (w : Site) : (F w : Disorder → ℝ) =ᵐ[disorderLaw] term w := by
    exact ((Polymer.memLp_terminalProfile β a (b - a) w f 1 (by simp)).const_mul
      (ν w)).coeFn_toLp
  have hpointBound (w : Site) :
      eLpNorm (term w) 1 disorderLaw ≤ ENNReal.ofReal (M * |ν w|) := by
    have hmem := Polymer.memLp_terminalProfile β a (b - a) w f 1 (by simp)
    have htermMem : MemLp (term w) 1 disorderLaw := by
      simpa [term, mul_comm] using hmem.const_mul (ν w)
    have hmajor (ω : Disorder) :
        ‖term w ω‖ ≤ |ν w| * M * pointToPlane β a (b - a) w ω := by
      change |ν w * ∑' z, pointToPoint β a (b - a) w z ω * f z| ≤ _
      rw [abs_mul]
      have htail := Polymer.terminalProfile_abs_le β a (b - a) w f M
        (fun z => by rw [abs_of_nonneg (hf z).1]; exact (hf z).2) ω
      calc
        |ν w| * |∑' z, pointToPoint β a (b - a) w z ω * f z| ≤
            |ν w| * (M * pointToPlane β a (b - a) w ω) :=
              mul_le_mul_of_nonneg_left htail (abs_nonneg _)
        _ = |ν w| * M * pointToPlane β a (b - a) w ω := by ring
    have hmajorNorm (ω : Disorder) :
        ‖(|ν w| * M) * pointToPlane β a (b - a) w ω‖ =
          |ν w| * M * pointToPlane β a (b - a) w ω := by
      calc
        ‖(|ν w| * M) * pointToPlane β a (b - a) w ω‖ =
            |(|ν w| * M) * pointToPlane β a (b - a) w ω| := Real.norm_eq_abs _
        _ = |ν w| * M * pointToPlane β a (b - a) w ω := by
          rw [abs_of_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) hM)
            (Polymer.pointToPlane_pos β a (b - a) w ω).le)]
    have hmono : eLpNorm (term w) 1 disorderLaw ≤
        eLpNorm (fun ω => (|ν w| * M) * pointToPlane β a (b - a) w ω) 1 disorderLaw := by
      apply eLpNorm_mono_ae htermMem.aestronglyMeasurable
      exact Filter.Eventually.of_forall fun ω => by
        calc
          ‖term w ω‖ ≤ |ν w| * M * pointToPlane β a (b - a) w ω := hmajor ω
          _ = ‖(|ν w| * M) * pointToPlane β a (b - a) w ω‖ := (hmajorNorm ω).symm
    have hptMem : MemLp (pointToPlane β a (b - a) w) 1 disorderLaw :=
      Polymer.memLp_pointToPlane β a (b - a) w 1 (by simp)
    have hptNorm : eLpNorm (pointToPlane β a (b - a) w) 1 disorderLaw = 1 := by
      rw [eLpNorm_one_eq_lintegral_enorm hptMem.aestronglyMeasurable]
      have hnonneg : 0 ≤ᵐ[disorderLaw] pointToPlane β a (b - a) w :=
        Filter.Eventually.of_forall fun ω => (Polymer.pointToPlane_pos β a (b - a) w ω).le
      have hlin : (∫⁻ ω, ‖pointToPlane β a (b - a) w ω‖ₑ ∂disorderLaw) =
          ∫⁻ ω, ENNReal.ofReal (pointToPlane β a (b - a) w ω) ∂disorderLaw := by
        apply lintegral_congr_ae
        filter_upwards [hnonneg] with ω hω
        rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hω]
      rw [hlin, ← ofReal_integral_eq_lintegral_ofReal
          (hptMem.integrable (by norm_num)) hnonneg, Polymer.integral_pointToPlane]
      simp
    have heqsmul : (fun ω => (|ν w| * M) * pointToPlane β a (b - a) w ω) =
        (|ν w| * M) • pointToPlane β a (b - a) w := by
      funext ω
      simp [smul_eq_mul]
    rw [heqsmul, eLpNorm_const_smul, hptNorm] at hmono
    have hνnonneg : 0 ≤ |ν w| := abs_nonneg _
    have hcoef : ‖|ν w| * M‖ₑ = ENNReal.ofReal (M * |ν w|) := by
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (mul_nonneg hνnonneg hM)]
      congr 1; ring
    simpa only [hcoef, ENNReal.one_rpow, mul_one] using hmono
  have hnormBound (w : Site) : ‖F w‖ₑ ≤ ENNReal.ofReal M * ENNReal.ofReal |ν w| := by
    have h := hpointBound w
    have heq : ENNReal.ofReal (M * |ν w|) = ENNReal.ofReal M * ENNReal.ofReal |ν w| := by
      rw [ENNReal.ofReal_mul hM]
    simpa only [F, Lp.enorm_toLp, heq] using h
  have hsumNorm : ∑' w, ‖F w‖ₑ ≤ ENNReal.ofReal M * ∑' w, ENNReal.ofReal |ν w| := by
    calc
      ∑' w, ‖F w‖ₑ ≤ ∑' w, ENNReal.ofReal M * ENNReal.ofReal |ν w| :=
        ENNReal.tsum_le_tsum hnormBound
      _ = ENNReal.ofReal M * ∑' w, ENNReal.ofReal |ν w| := ENNReal.tsum_mul_left
  have hsumFinite : ∑' w, ‖F w‖ₑ ≠ ∞ := by
    have hνtop : ∑' w, ENNReal.ofReal |ν w| < ∞ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun w => abs_nonneg _) hν]
      exact ENNReal.ofReal_lt_top
    apply (lt_of_le_of_lt hsumNorm (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hνtop)).ne
  have hFsum : Summable F := Summable.of_enorm hsumFinite
  have hcoe := Lp.coeFn_tsum (f := F) hsumFinite
  have htermAll : ∀ᵐ ω ∂disorderLaw, ∀ w, (F w : Disorder → ℝ) ω = term w ω :=
    ae_all_iff.2 htermAE
  have hseries : (fun ω => (∑' w, F w) ω) =ᵐ[disorderLaw]
      fun ω => profileP2Fun β a b ν f ω := by
    filter_upwards [hcoe, htermAll] with ω hω hall
    rw [hω]
    calc
      ∑' w, (F w : Disorder → ℝ) ω = ∑' w, term w ω := tsum_congr (hall)
      _ = profileP2Fun β a b ν f ω := by
        simp only [term, profileP2Fun]
  have hprofile : MemLp (profileP2Fun β a b ν f) 1 disorderLaw :=
    Polymer.memLp_profileP2Fun_summable β a b ν f hν M hM
      (fun z => by rw [abs_le]; constructor <;> linarith [hf z]) 1 (by simp)
  let G : Lp ℝ 1 disorderLaw := hprofile.toLp (profileP2Fun β a b ν f)
  have hGae : (G : Disorder → ℝ) =ᵐ[disorderLaw] profileP2Fun β a b ν f :=
    MemLp.coeFn_toLp hprofile
  have hG : G = ∑' w, F w := by
    apply Lp.ext
    exact hGae.trans hseries.symm
  refine ⟨hprofile, ?_⟩
  rw [← Lp.enorm_toLp hprofile]
  change ‖G‖ₑ ≤ _
  rw [hG]
  exact enorm_tsum_le_tsum_enorm.trans hsumNorm

end Critical2DKPZ.JointConvergence

end
