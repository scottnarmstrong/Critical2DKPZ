/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordContinuumBound
public import Critical2DKPZ.Analysis.Heat.Semigroup
public import Critical2DKPZ.SHF.Moments.SinglePairWordFutureJoint
import Mathlib.Tactic

/-! # Integrable incoming heat majorants for two-particle entrances -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory Filter
open scoped CompactlySupported

private theorem incoming_heat_pair_integrable {u : ℝ} (hu : 0 < u) (a : Plane) :
    Integrable (fun p : Plane × Plane => heatKernel u (p.1 - a) * heatKernel u (p.2 - p.1))
      ((volume : Measure Plane).prod volume) := by
  have hm : AEStronglyMeasurable
      (fun p : Plane × Plane => heatKernel u (p.1 - a) * heatKernel u (p.2 - p.1))
      ((volume : Measure Plane).prod volume) := by
    exact (((continuous_heatKernel u).comp (continuous_fst.sub continuous_const)).mul
      ((continuous_heatKernel u).comp (continuous_snd.sub continuous_fst))).aestronglyMeasurable
  apply (integrable_prod_iff hm).mpr
  constructor
  · apply Eventually.of_forall
    intro z
    have hz : Integrable (fun b : Plane => heatKernel u (b - z)) (volume : Measure Plane) :=
      (integrable_heatKernel hu).comp_sub_right z
    exact hz.const_mul (heatKernel u (z - a))
  · have he (z : Plane) : (∫ b : Plane, ‖heatKernel u (z - a) * heatKernel u (b - z)‖) =
        heatKernel u (z - a) := by
      simp only [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (heatKernel_nonneg hu.le _)]
      rw [integral_const_mul, integral_heatKernel_sub hu, mul_one]
    simpa only [he] using (integrable_heatKernel hu).comp_sub_right a

private theorem incoming_heat_pair_integral {u : ℝ} (hu : 0 < u) (a : Plane) :
    (∫ p : Plane × Plane, heatKernel u (p.1 - a) * heatKernel u (p.2 - p.1)
      ∂(volume : Measure Plane).prod volume) = 1 := by
  rw [integral_prod _ (incoming_heat_pair_integrable hu a)]
  simp only [integral_const_mul, integral_heatKernel_sub hu, mul_one]

/-- Integrating the incoming heat factors leaves the finite volume of one incoming cutoff, giving a majorant integrable down to entrance time zero. -/
theorem integrable_pairTwo_incoming_heat_majorant
    (T : ℝ) (K : Set Plane) (hK : volume K ≠ ⊤) :
    Integrable (fun p : ℝ × (Plane × (Plane × Plane)) =>
      heatKernel p.1 (p.2.2.1 - p.2.1) * heatKernel p.1 (p.2.2.2 - p.2.2.1))
      ((volume.restrict (Set.Ioo 0 T)).prod
        ((volume.restrict K).prod ((volume : Measure Plane).prod volume))) := by
  let ν : Measure (Plane × Plane) := (volume : Measure Plane).prod volume
  let F := fun p : ℝ × (Plane × (Plane × Plane)) =>
    heatKernel p.1 (p.2.2.1 - p.2.1) * heatKernel p.1 (p.2.2.2 - p.2.2.1)
  have hm : Measurable F := by
    dsimp [F]
    unfold heatKernel
    fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    have hrow : Integrable (fun p : Plane × (Plane × Plane) => F (u, p))
        ((volume.restrict K).prod ν) := by
      apply (integrable_prod_iff ((hm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)).mpr
      constructor
      · exact Eventually.of_forall fun a => incoming_heat_pair_integrable hu.1 a
      · have he (a : Plane) : (∫ p : Plane × Plane, ‖F (u, a, p)‖ ∂ν) = 1 := by
          have hn (p : Plane × Plane) : 0 ≤ F (u, a, p) :=
            mul_nonneg (heatKernel_nonneg hu.1.le _) (heatKernel_nonneg hu.1.le _)
          simp only [Real.norm_eq_abs, abs_of_nonneg (hn _)]
          exact incoming_heat_pair_integral hu.1 a
        simpa only [Function.comp_apply, id_eq, he, IntegrableOn] using (integrableOn_const (C := (1 : ℝ)) hK)
    exact hrow
  · have he : (fun u => ∫ p : Plane × (Plane × Plane), ‖F (u, p)‖
        ∂(volume.restrict K).prod ν) =ᵐ[volume.restrict (Set.Ioo 0 T)]
        fun _ => (volume K).toReal := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      have hn (p : Plane × (Plane × Plane)) : 0 ≤ F (u, p) :=
        mul_nonneg (heatKernel_nonneg hu.1.le _) (heatKernel_nonneg hu.1.le _)
      simp only [Real.norm_eq_abs, abs_of_nonneg (hn _)]
      rw [integral_prod]
      · change (∫ a in K, ∫ p : Plane × Plane,
          heatKernel u (p.1 - a) * heatKernel u (p.2 - p.1) ∂ν) = _
        have he (a : Plane) : (∫ p : Plane × Plane,
            heatKernel u (p.1 - a) * heatKernel u (p.2 - p.1) ∂ν) = 1 :=
          incoming_heat_pair_integral hu.1 a
        simp only [he, setIntegral_const, Measure.real, smul_eq_mul, mul_one]
      · apply (integrable_prod_iff
          ((hm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)).mpr
        constructor
        · exact Eventually.of_forall fun a => incoming_heat_pair_integrable hu.1 a
        · have heNorm (a : Plane) : (∫ p : Plane × Plane, ‖F (u, a, p)‖ ∂ν) = 1 := by
            have hn' (p : Plane × Plane) : 0 ≤ F (u, a, p) :=
              mul_nonneg (heatKernel_nonneg hu.1.le _) (heatKernel_nonneg hu.1.le _)
            simp only [Real.norm_eq_abs, abs_of_nonneg (hn' _)]
            exact incoming_heat_pair_integral hu.1 a
          simpa only [Function.comp_apply, id_eq, heNorm, IntegrableOn] using
            (integrableOn_const (C := (1 : ℝ)) hK)
    exact (integrableOn_const (C := (volume K).toReal) (by simp)).congr he.symm

/-- The full continuum entrance integrand is absolutely integrable on the
complete open time slab, with only a finite-volume cutoff in the first
incoming location. No separation of the incoming points is assumed. -/
theorem integrable_pairTwo_continuum_entrance_on_initial_window
    (θ T : ℝ) (hT : 0 < T) (φ : Fin 2 → C_c(Plane × Plane, ℝ))
    (K : Set Plane) (hK : volume K ≠ ⊤) :
    Integrable (fun p : ℝ × (Plane × (Plane × Plane)) =>
      (heatKernel p.1 (p.2.2.1 - p.2.1) * heatKernel p.1 (p.2.2.2 - p.2.2.1)) *
        pairTwoContinuumFuture θ (T - p.1) φ ![p.2.1, p.2.2.2] p.2.2.1)
      ((volume.restrict (Set.Ioo 0 T)).prod
        ((volume.restrict K).prod ((volume : Measure Plane).prod volume))) := by
  let X := Plane × (Plane × Plane)
  let ν : Measure X := (volume.restrict K).prod ((volume : Measure Plane).prod volume)
  let G := fun p : ℝ × X =>
    pairTwoContinuumFuture θ (T - p.1) φ ![p.2.1, p.2.2.2] p.2.2.1
  have hG : ContinuousOn G (Set.Ioo 0 T ×ˢ Set.univ) := by
    intro p hp
    have harg : ContinuousAt (fun p : ℝ × X =>
        (T - p.1, (![p.2.1, p.2.2.2] : Fin 2 → Plane), p.2.2.1)) p := by
      dsimp only [X]
      fun_prop
    have hcont := continuousAt_pairTwoContinuumFuture θ φ
      (T - p.1, (![p.2.1, p.2.2.2] : Fin 2 → Plane), p.2.2.1)
      (sub_pos.mpr hp.1.2)
    exact (ContinuousAt.comp'
      (f := fun p : ℝ × X => (T - p.1, (![p.2.1, p.2.2.2] : Fin 2 → Plane), p.2.2.1))
      (g := fun p : ℝ × (Fin 2 → Plane) × Plane =>
        pairTwoContinuumFuture θ p.1 φ p.2.1 p.2.2) hcont harg).continuousWithinAt
  have hmG : AEStronglyMeasurable G ((volume.restrict (Set.Ioo 0 T)).prod ν) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    exact hG.aestronglyMeasurable (measurableSet_Ioo.prod MeasurableSet.univ)
  let H := fun p : ℝ × X =>
    heatKernel p.1 (p.2.2.1 - p.2.1) * heatKernel p.1 (p.2.2.2 - p.2.2.1)
  have hmH : Measurable H := by
    dsimp [H, X]
    unfold heatKernel
    fun_prop
  obtain ⟨C, hC, hb⟩ := exists_pairTwoContinuumFuture_bound θ T hT φ
  have hi := (integrable_pairTwo_incoming_heat_majorant T K hK).mul_const C
  apply hi.mono' (hmH.aestronglyMeasurable.mul hmG)
  have ht : ∀ᵐ p : ℝ × X ∂(volume.restrict (Set.Ioo 0 T)).prod ν,
      p.1 ∈ Set.Ioo 0 T := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioo.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact Eventually.of_forall fun _ => hu
  filter_upwards [ht] with p hp
  have hn : 0 ≤ H p :=
    mul_nonneg (heatKernel_nonneg hp.1.le _) (heatKernel_nonneg hp.1.le _)
  change ‖H p * G p‖ ≤ H p * C
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hn]
  exact mul_le_mul_of_nonneg_left (hb (T - p.1) (sub_pos.mpr hp.2).le
    (sub_le_self T hp.1.le) _ _) hn

end Critical2DKPZ.SHF.Moments
