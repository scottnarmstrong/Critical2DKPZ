/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.LocalSobolev.RandomBoundaryTerminal
public import Critical2DKPZ.Gaussian.TimeBlocks
public import Critical2DKPZ.FutureProfiles.FreezingPast
import Mathlib.Tactic

/-! # One-step boundary estimate with a random past profile and terminal data -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Critical2DKPZ.LocalSobolev

/-- The one-slice log ratio has a uniform second-moment bound for a normalized finite profile
measurable with respect to the past, with any positive deterministic terminal weight. -/
theorem integral_sq_log_profileP2Fun_random_past_terminal_ratio_le (β : ℝ) (n : ℕ)
    (A : Finset Site) (η : Disorder → Site → ℝ) (f : Site → ℝ)
    (hsupp : ∀ ω z, z ∉ A → η ω z = 0)
    (hη0 : ∀ ω z, 0 ≤ η ω z)
    (hη1 : ∀ ω, ∑ z ∈ A, η ω z = 1)
    (hηmeas : ∀ z, Measurable[disorderPast n] (η · z))
    (hf : ∀ z, 0 < f z) :
    Integrable (fun ω =>
      (Real.log (profileP2Fun β n (n + 1) (η ω) f ω) -
        Real.log (profileP2Fun 0 n (n + 1) (η ω) f ω)) ^ 2) disorderLaw ∧
    (∫ ω,
      (Real.log (profileP2Fun β n (n + 1) (η ω) f ω) -
        Real.log (profileP2Fun 0 n (n + 1) (η ω) f ω)) ^ 2 ∂disorderLaw) ≤
      β ^ 2 + β ^ 4 / 4 := by
  classical
  let F : Disorder → ℝ := fun ω =>
    Real.log (profileP2Fun β n (n + 1) (η ω) f ω) -
      Real.log (profileP2Fun 0 n (n + 1) (η ω) f ω)
  have hprofileMeas (γ : ℝ) :
      Measurable (fun ω => profileP2Fun γ n (n + 1) (η ω) f ω) :=
    FutureProfiles.measurable_randomTerminalProfilePolymer γ n (n + 1) A η f
      hsupp hηmeas
  have hFmeas : Measurable F := by
    dsimp [F]
    exact (Real.measurable_log.comp (hprofileMeas β)).sub
      (Real.measurable_log.comp (hprofileMeas 0))
  let B : ℝ := β ^ 2 + β ^ 4 / 4
  let Fsq (ω : Disorder) : ℝ := F ω ^ 2
  have htruncMeas (m : ℕ) : Measurable (fun ω => min (Fsq ω) (m : ℝ)) :=
    (hFmeas.pow_const 2).min measurable_const
  have htruncInt (m : ℕ) : Integrable (fun ω => min (Fsq ω) (m : ℝ)) disorderLaw := by
    apply (integrable_const (m : ℝ)).mono' (htruncMeas m).aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact min_le_right _ _
  have htruncBound (m : ℕ) :
      (∫ ω, min (Fsq ω) (m : ℝ) ∂disorderLaw) ≤ B := by
    let X : Disorder → ℝ := fun ω => min (Fsq ω) (m : ℝ)
    have hce := Gaussian.condExp_disorderBlock_ae_eq 0 n (htruncMeas m) (htruncInt m)
    rw [Gaussian.disorderBlock_zero] at hce
    have hcond : disorderLaw[X | disorderPast n] ≤ᵐ[disorderLaw] fun _ => B := by
      filter_upwards [hce] with ω hω
      rw [hω]
      have hresample (ξ : Disorder) :
          F (Gaussian.resample (Gaussian.timeBlock 0 n) ω ξ) =
            Real.log (profileP2Fun β n (n + 1) (η ω) f ξ) -
              Real.log (profileP2Fun 0 n (n + 1) (η ω) f ξ) := by
        dsimp [F]
        have hprofileResample (γ : ℝ) :
            profileP2Fun γ n (n + 1)
                (η (Gaussian.resample (Gaussian.timeBlock 0 n) ω ξ)) f
                (Gaussian.resample (Gaussian.timeBlock 0 n) ω ξ) =
              profileP2Fun γ n (n + 1) (η ω) f ξ := by
          rw [Polymer.profileP2Fun_eq_sum γ n (n + 1)
            (η (Gaussian.resample (Gaussian.timeBlock 0 n) ω ξ)) f A (hsupp _)]
          rw [Polymer.profileP2Fun_eq_sum γ n (n + 1) (η ω) f A (hsupp ω)]
          apply Finset.sum_congr rfl
          intro z hz
          rw [Critical2DKPZ.Collision.pastMeasurable_resample_eq
            (hηmeas z) ω ξ, Critical2DKPZ.Collision.terminalProfile_resamplePast]
        rw [hprofileResample β, hprofileResample 0]
      have hbound := integral_sq_log_profileP2Fun_oneStep_terminal_ratio_le
        β n A (η ω) f (hsupp ω) (hη0 ω) (hη1 ω) hf
      have hfiberMeas (γ : ℝ) :
          Measurable (fun ξ => profileP2Fun γ n (n + 1) (η ω) f ξ) :=
        Polymer.measurable_profileP2Fun γ n (n + 1) (η ω) f
      have hsmallInt : Integrable
          (fun ξ => min ((Real.log (profileP2Fun β n (n + 1) (η ω) f ξ) -
            Real.log (profileP2Fun 0 n (n + 1) (η ω) f ξ)) ^ 2) (m : ℝ)) disorderLaw := by
        apply (integrable_const (m : ℝ)).mono'
          ((((Real.measurable_log.comp (hfiberMeas β)).sub
            (Real.measurable_log.comp (hfiberMeas 0))).pow_const 2).min
            measurable_const).aestronglyMeasurable
        filter_upwards [] with ξ
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact min_le_right _ _
      have hsmall_le :
          (∫ ξ, min ((Real.log (profileP2Fun β n (n + 1) (η ω) f ξ) -
            Real.log (profileP2Fun 0 n (n + 1) (η ω) f ξ)) ^ 2) (m : ℝ)
              ∂disorderLaw) ≤ B := by
        exact (integral_mono hsmallInt hbound.1 (fun ξ => min_le_left _ _)).trans hbound.2
      simp only [Fsq]
      calc
        _ = ∫ ξ, min ((Real.log (profileP2Fun β n (n + 1) (η ω) f ξ) -
              Real.log (profileP2Fun 0 n (n + 1) (η ω) f ξ)) ^ 2) (m : ℝ)
                ∂disorderLaw := by
            apply integral_congr_ae
            filter_upwards [] with ξ
            rw [← hresample ξ]
        _ ≤ B := hsmall_le
    have hpastle : disorderPast n ≤ (inferInstance : MeasurableSpace Disorder) :=
      Gaussian.disorderBlock_le 0 n
    calc
      (∫ ω, X ω ∂disorderLaw) =
          ∫ ω, disorderLaw[X | disorderPast n] ω ∂disorderLaw := by
            symm
            exact integral_condExp hpastle
      _ ≤ ∫ _ω, B ∂disorderLaw := integral_mono_ae integrable_condExp
          (integrable_const _) hcond
      _ = B := by simp [B]
  have hlinTrunc (m : ℕ) :
      (∫⁻ ω, ENNReal.ofReal (min (Fsq ω) (m : ℝ)) ∂disorderLaw) ≤ ENNReal.ofReal B := by
    rw [← ofReal_integral_eq_lintegral_ofReal (htruncInt m)
      (Filter.Eventually.of_forall fun ω => by positivity)]
    exact ENNReal.ofReal_le_ofReal (htruncBound m)
  have hmono : Monotone (fun m : ℕ => fun ω =>
      ENNReal.ofReal (min (Fsq ω) (m : ℝ))) := by
    intro m l hml ω
    exact ENNReal.ofReal_le_ofReal (min_le_min_left _ (Nat.cast_le.mpr hml))
  have hlin : (∫⁻ ω, ENNReal.ofReal (Fsq ω) ∂disorderLaw) ≤ ENNReal.ofReal B := by
    have hsup : (fun ω => ENNReal.ofReal (Fsq ω)) =
        ⨆ m : ℕ, fun ω => ENNReal.ofReal (min (Fsq ω) (m : ℝ)) := by
      funext ω
      simp only [iSup_apply]
      apply le_antisymm
      · obtain ⟨m, hm⟩ := exists_nat_gt (Fsq ω)
        calc
          ENNReal.ofReal (Fsq ω) = ENNReal.ofReal (min (Fsq ω) (m : ℝ)) := by
            rw [min_eq_left hm.le]
          _ ≤ ⨆ j : ℕ, ENNReal.ofReal (min (Fsq ω) (j : ℝ)) := le_iSup_of_le m le_rfl
      · apply iSup_le
        intro m
        change ENNReal.ofReal (min (Fsq ω) (m : ℝ)) ≤ ENNReal.ofReal (Fsq ω)
        exact ENNReal.ofReal_le_ofReal (min_le_left _ _)
    calc
      _ = ∫⁻ ω, ⨆ m : ℕ, ENNReal.ofReal (min (Fsq ω) (m : ℝ)) ∂disorderLaw := by
        apply lintegral_congr
        intro ω
        simpa only [iSup_apply] using congrFun hsup ω
      _ = ⨆ m : ℕ, ∫⁻ ω, ENNReal.ofReal (min (Fsq ω) (m : ℝ)) ∂disorderLaw := by
        simpa only [Function.comp_apply] using lintegral_iSup
          (fun m => ENNReal.measurable_ofReal.comp
            ((hFmeas.pow_const 2).min measurable_const)) hmono
      _ ≤ ENNReal.ofReal B := iSup_le fun m => hlinTrunc m
  have hreal :
      (∫ ω, Fsq ω ∂disorderLaw) =
        (∫⁻ ω, ENNReal.ofReal (Fsq ω) ∂disorderLaw).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun ω => sq_nonneg (F ω))
      ((hFmeas.pow_const 2).aestronglyMeasurable)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨?_, ?_⟩
  · refine ⟨(hFmeas.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun ω => sq_nonneg (F ω))]
    exact lt_of_le_of_lt hlin ENNReal.ofReal_lt_top
  · rw [hreal]
    exact ENNReal.toReal_le_of_le_ofReal hB hlin

end Critical2DKPZ.LocalSobolev

end
