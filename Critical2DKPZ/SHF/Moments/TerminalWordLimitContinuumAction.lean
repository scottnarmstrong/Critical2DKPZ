/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordLimitTimeAction
import Critical2DKPZ.SHF.Moments.TerminalWordLimitContinuumMass
public import Critical2DKPZ.SHF.DeltaBose.PathKernel
public import Critical2DKPZ.SHF.DeltaBose.PathDominating
public import Critical2DKPZ.SHF.DeltaBose.PotentialFusedRows
public import Critical2DKPZ.SHF.DeltaBose.PotentialIntegratedSchur
public import Critical2DKPZ.SHF.DeltaBose.ScalarEnvelope
public import Critical2DKPZ.SHF.DeltaBose.IncomingMass
public import Critical2DKPZ.SHF.DeltaBose.KernelBlocks
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-! # Signed first-letter action for continuum collision diagrams -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators CompactlySupported Topology ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Moments

private theorem heatPotential_ne_top_of_ne_zero {z : Plane} (hz : z ≠ 0) :
    heatPotential z ≠ ⊤ := by
  let f : ℝ → ℝ := fun t => t ^ (-(1 / 2 : ℝ)) * heatKernel t z
  have hf : Measurable f := by
    dsimp [f]
    unfold heatKernel
    fun_prop
  have hr : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
  have hsmall : IntegrableOn f (Ioc (0 : ℝ) 1) := by
    have hp : IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) (Ioc 0 1) :=
      (intervalIntegral.intervalIntegrable_rpow' (r := -(1 / 2 : ℝ))
        (by norm_num) (a := 0) (b := 1)).1
    apply (hp.const_mul (Real.pi * ‖z‖ ^ 2)⁻¹).mono' hf.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 < t := ht.1
    have hu : 0 < ‖z‖ ^ 2 / (2 * t) := div_pos hr (by positivity)
    have hexp0 := (Real.mul_exp_neg_le_exp_neg_one (‖z‖ ^ 2 / (2 * t))).trans
      (Real.exp_le_one_iff.mpr (by norm_num : -(1 : ℝ) ≤ 0))
    have hexp : Real.exp (-(‖z‖ ^ 2 / (2 * t))) ≤ 2 * t / ‖z‖ ^ 2 := by
      calc
        Real.exp (-(‖z‖ ^ 2 / (2 * t))) ≤ (‖z‖ ^ 2 / (2 * t))⁻¹ := by
          calc
            _ = (‖z‖ ^ 2 / (2 * t))⁻¹ *
                ((‖z‖ ^ 2 / (2 * t)) * Real.exp (-(‖z‖ ^ 2 / (2 * t)))) := by
                  field_simp [ne_of_gt hu]
            _ ≤ (‖z‖ ^ 2 / (2 * t))⁻¹ * 1 :=
                  mul_le_mul_of_nonneg_left hexp0 (inv_nonneg.mpr hu.le)
            _ = _ := by ring
        _ = 2 * t / ‖z‖ ^ 2 := by field_simp [ne_of_gt hu, ne_of_gt hr]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.1.le _)
      (Critical2DKPZ.heatKernel_pos ht0 z).le)]
    calc
      f t = t ^ (-(1 / 2 : ℝ)) *
          ((2 * Real.pi * t)⁻¹ * Real.exp (-(‖z‖ ^ 2 / (2 * t)))) := by
            change t ^ (-(1 / 2 : ℝ)) * heatKernel t z = _
            rw [Critical2DKPZ.heatKernel]
            congr 1
            ring_nf
      _ ≤ t ^ (-(1 / 2 : ℝ)) * ((2 * Real.pi * t)⁻¹ * (2 * t / ‖z‖ ^ 2)) := by
            apply mul_le_mul_of_nonneg_left
            · exact mul_le_mul_of_nonneg_left hexp (by positivity)
            · exact Real.rpow_nonneg ht0.le _
      _ = (Real.pi * ‖z‖ ^ 2)⁻¹ * t ^ (-(1 / 2 : ℝ)) := by
            field_simp [ne_of_gt ht0, ne_of_gt hr]
  have hlarge : IntegrableOn f (Ioi (1 : ℝ)) := by
    have hp : IntegrableOn (fun t : ℝ => t ^ (-(3 / 2 : ℝ))) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num : -(3 / 2 : ℝ) < -1) (by norm_num)
    apply (hp.const_mul (2 * Real.pi)⁻¹).mono' hf.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    have hexp : Real.exp (-(‖z‖ ^ 2 / (2 * t))) ≤ 1 :=
      Real.exp_le_one_iff.mpr
        (neg_nonpos.mpr (div_nonneg hr.le (by positivity)))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht0.le _)
      (Critical2DKPZ.heatKernel_pos ht0 z).le)]
    calc
      f t = t ^ (-(1 / 2 : ℝ)) *
          ((2 * Real.pi * t)⁻¹ * Real.exp (-(‖z‖ ^ 2 / (2 * t)))) := by
            change t ^ (-(1 / 2 : ℝ)) * heatKernel t z = _
            rw [Critical2DKPZ.heatKernel]
            congr 1
            ring_nf
      _ ≤ t ^ (-(1 / 2 : ℝ)) * (2 * Real.pi * t)⁻¹ :=
            mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (by positivity) hexp)
              (Real.rpow_nonneg ht0.le _)
      _ = (2 * Real.pi)⁻¹ * (t ^ (-(1 / 2 : ℝ)) * t⁻¹) := by
            field_simp [ne_of_gt ht0]
      _ = (2 * Real.pi)⁻¹ * t ^ (-(3 / 2 : ℝ)) := by
            have hinv : t⁻¹ = t ^ (-1 : ℝ) := by
              rw [Real.rpow_neg ht0.le, Real.rpow_one]
            rw [hinv, ← Real.rpow_add ht0]
            congr 2
            ring
  have hint : IntegrableOn f (Ioi (0 : ℝ)) := by
    rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
    exact hsmall.union hlarge
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.rpow_nonneg ht.le _) (Critical2DKPZ.heatKernel_pos ht z).le
  have hrepr : heatPotential z = ENNReal.ofReal (∫ t in Ioi (0 : ℝ), f t) := by
    rw [heatPotential]
    calc
      _ = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (f t) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        change ENNReal.ofReal (t ^ (-(1 / 2 : ℝ))) *
          ENNReal.ofReal (heatKernel t z) =
          ENNReal.ofReal (t ^ (-(1 / 2 : ℝ)) * heatKernel t z)
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
      _ = ENNReal.ofReal (∫ t in Ioi (0 : ℝ), f t) :=
        (ofReal_integral_eq_lintegral_ofReal hint hnonneg).symm
  rw [hrepr]
  exact ENNReal.ofReal_ne_top

private theorem integrable_mul_toReal_of_lintegral_lt_top
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (K : X → ℝ≥0∞)
    (hK : AEStronglyMeasurable K μ)
    (hKfin : (∫⁻ x, K x ∂μ) < ⊤)
    (g : X → ℝ) (hg : AEStronglyMeasurable g μ) (B : ℝ)
    (hgB : ∀ᵐ x ∂μ, ‖g x‖ ≤ B) :
    Integrable (fun x => g x * (K x).toReal) μ := by
  have hKtoReal : Integrable (fun x => (K x).toReal) μ :=
    integrable_toReal_of_lintegral_ne_top hK.aemeasurable hKfin.ne
  have hmul := hKtoReal.mul_bdd hg (c := B) hgB
  simpa only [mul_comm] using hmul

private theorem signed_action_of_lintegral_action
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (K₀ : Y → ℝ≥0∞) (K : X × Y → ℝ≥0∞)
    (hK₀ : Measurable K₀) (hK : Measurable K)
    (hfinite : (∫⁻ y, K₀ y ∂ν) < ⊤)
    (haction : ∀ f : Y → ℝ≥0∞, Measurable f →
      (∫⁻ y, K₀ y * f y ∂ν) = ∫⁻ x, ∫⁻ y, K (x, y) * f y ∂ν ∂μ)
    (g : Y → ℝ) (hg : Measurable g) (B : ℝ) (hB : ∀ y, ‖g y‖ ≤ B) :
    Integrable (fun y => g y * (K₀ y).toReal) ν ∧
    Integrable (fun p => g p.2 * (K p).toReal) (μ.prod ν) ∧
    (∫ y, g y * (K₀ y).toReal ∂ν) =
      ∫ p, g p.2 * (K p).toReal ∂μ.prod ν := by
  have hmass : (∫⁻ p, K p ∂μ.prod ν) = ∫⁻ y, K₀ y ∂ν := by
    rw [lintegral_prod _ hK.aemeasurable]
    simpa only [mul_one] using (haction (fun _ => 1) measurable_const).symm
  have hfiniteK : (∫⁻ p, K p ∂μ.prod ν) < ⊤ := by rw [hmass]; exact hfinite
  have hi₀ := integrable_mul_toReal_of_lintegral_lt_top ν K₀
    hK₀.aestronglyMeasurable hfinite g hg.aestronglyMeasurable B
    (Eventually.of_forall hB)
  have hi := integrable_mul_toReal_of_lintegral_lt_top (μ.prod ν) K
    hK.aestronglyMeasurable hfiniteK (fun p => g p.2)
    (hg.comp measurable_snd).aestronglyMeasurable B
    (Eventually.of_forall fun p => hB p.2)
  have hpart (a : Y → ℝ) (ha : Measurable a) :
      (∫⁻ y, ENNReal.ofReal (a y * (K₀ y).toReal) ∂ν) =
        ∫⁻ p, ENNReal.ofReal (a p.2 * (K p).toReal) ∂μ.prod ν := by
    calc
      _ = ∫⁻ y, K₀ y * ENNReal.ofReal (a y) ∂ν := by
        apply lintegral_congr_ae
        filter_upwards [ae_lt_top' hK₀.aemeasurable hfinite.ne] with y hy
        rw [mul_comm (a y), ENNReal.ofReal_mul ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal hy.ne]
      _ = ∫⁻ x, ∫⁻ y, K (x, y) * ENNReal.ofReal (a y) ∂ν ∂μ :=
        haction _ ha.ennreal_ofReal
      _ = ∫⁻ p, K p * ENNReal.ofReal (a p.2) ∂μ.prod ν :=
        (lintegral_prod _ (hK.mul (ha.comp measurable_snd).ennreal_ofReal).aemeasurable).symm
      _ = _ := by
        apply lintegral_congr_ae
        filter_upwards [ae_lt_top' hK.aemeasurable hfiniteK.ne] with p hp
        rw [mul_comm (a p.2), ENNReal.ofReal_mul ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal hp.ne]
  refine ⟨hi₀, hi, ?_⟩
  have hpos := hpart g hg
  have hneg := hpart (fun y => -g y) hg.neg
  simp only [neg_mul] at hneg
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi₀,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi, hpos, hneg]

private theorem measurable_tensorTest {h : ℕ} (ψ : Fin h → C_c(Plane, ℝ)) :
    Measurable (fun y : Configuration h => ∏ i, ψ i (y i)) := by
  apply Finset.measurable_fun_prod
  intro i hi
  exact (ψ i).continuous.measurable.comp (measurable_pi_apply i)

private theorem exists_tensorTest_bound {h : ℕ} (ψ : Fin h → C_c(Plane, ℝ)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : Configuration h, |∏ i, ψ i (y i)| ≤ B := by
  let B : ℝ := ∏ i, ‖(ψ i).toBoundedContinuousFunction‖
  refine ⟨B, Finset.prod_nonneg fun i hi => norm_nonneg _, fun y => ?_⟩
  rw [Finset.abs_prod]
  dsimp [B]
  apply Finset.prod_le_prod₀
  · intro i hi
    exact abs_nonneg _
  · intro i hi
    have hψ := (ψ i).toBoundedContinuousFunction.norm_coe_le_norm (y i)
    simpa using hψ

private theorem lintegral_fusedTensor_weight_le {n : ℕ} (α : CollisionPair n)
    {a b : ℝ} (ha : 0 < a) (c₀ : Plane) (x : Spectator α → Plane)
    (W : Plane → (Spectator α → Plane) → ℝ≥0∞)
    (hW : Measurable (Function.uncurry W)) (R : ℝ≥0∞)
    (hrow : ∀ c : Plane, (∫⁻ v : Spectator α → Plane,
      (∏ i : Spectator α, ENNReal.ofReal (heatKernel b (v i - x i))) * W c v) ≤ R) :
    (∫⁻ z : FusedConfiguration α,
      (ENNReal.ofReal (heatKernel a (z.1 - c₀)) *
        ∏ i : Spectator α, ENNReal.ofReal (heatKernel b (z.2 i - x i))) * W z.1 z.2) ≤ R := by
  classical
  let C : Plane → ℝ≥0∞ := fun c => ENNReal.ofReal (heatKernel a (c - c₀))
  let S : (Spectator α → Plane) → ℝ≥0∞ := fun v =>
    ∏ i : Spectator α, ENNReal.ofReal (heatKernel b (v i - x i))
  have hC : Measurable C := by
    dsimp [C]
    unfold heatKernel
    fun_prop
  have hS : Measurable S := by
    dsimp [S]
    apply Finset.measurable_fun_prod
    intro i hi
    unfold heatKernel
    fun_prop
  have hF : Measurable (fun z : FusedConfiguration α =>
      (C z.1 * S z.2) * W z.1 z.2) :=
    ((hC.comp measurable_fst).mul (hS.comp measurable_snd)).mul
      (hW.comp measurable_id)
  calc
    _ = ∫⁻ c : Plane, ∫⁻ v : Spectator α → Plane,
          (C c * S v) * W c v := by
            rw [Measure.volume_eq_prod, lintegral_prod _ hF.aemeasurable]
    _ ≤ ∫⁻ c : Plane, C c * R := by
          apply lintegral_mono
          intro c
          have hSv : Measurable (fun v : Spectator α → Plane => S v * W c v) :=
            hS.mul (hW.comp (measurable_const.prodMk measurable_id))
          calc (∫⁻ v : Spectator α → Plane, (C c * S v) * W c v)
              = C c * (∫⁻ v : Spectator α → Plane, S v * W c v) := by
                  calc
                    _ = ∫⁻ v : Spectator α → Plane, C c * (S v * W c v) := by
                          apply lintegral_congr
                          intro v
                          ac_rfl
                    _ = _ := lintegral_const_mul (C c) hSv
            _ ≤ C c * R := mul_le_mul_right (hrow c) (C c)
    _ = R := by
          rw [lintegral_mul_const _ hC, lintegral_heatKernel_sub ha c₀, one_mul]

private theorem pair_eq_of_endpoint_mem {n : ℕ} {α β : CollisionPair n}
    (h₁ : β.1.1 = α.1.1 ∨ β.1.1 = α.1.2)
    (h₂ : β.1.2 = α.1.1 ∨ β.1.2 = α.1.2) : β = α := by
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · have hβ := β.2
    have hα := α.2
    exfalso
    omega
  · apply Subtype.ext
    exact Prod.ext h₁ h₂
  · have hβ := β.2
    have hα := α.2
    exfalso
    omega
  · have hβ := β.2
    have hα := α.2
    exfalso
    omega

private theorem lintegral_fusedPairPotential_separated_le {n : ℕ}
    (α β : CollisionPair n) (hne : α ≠ β) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (c₀ : Plane) (x : Spectator α → Plane) :
    (∫⁻ z : FusedConfiguration α,
      (ENNReal.ofReal (heatKernel a (z.1 - c₀)) *
        ∏ i : Spectator α, ENNReal.ofReal (heatKernel b (z.2 i - x i))) *
        heatPotential ((collisionEmbedding α z) β.1.1 -
          (collisionEmbedding α z) β.1.2)) ≤ heatPotentialRowBound b := by
  classical
  by_cases h₁ : β.1.1 = α.1.1 ∨ β.1.1 = α.1.2
  · by_cases h₂ : β.1.2 = α.1.1 ∨ β.1.2 = α.1.2
    · exact False.elim (hne.symm (pair_eq_of_endpoint_mem h₁ h₂))
    · have hout : β.1.2 ≠ α.1.1 ∧ β.1.2 ≠ α.1.2 := by
        simpa only [not_or] using h₂
      let j : Spectator α := ⟨β.1.2, hout⟩
      let W : Plane → (Spectator α → Plane) → ℝ≥0∞ := fun c v =>
        heatPotential (c - v j)
      have hW : Measurable (Function.uncurry W) := by
        dsimp [W]
        exact measurable_heatPotential.comp
          (measurable_fst.sub ((measurable_pi_apply j).comp measurable_snd))
      have hweight : ∀ c : Plane, ∀ v : Spectator α → Plane,
          heatPotential ((collisionEmbedding α (c, v)) β.1.1 -
            (collisionEmbedding α (c, v)) β.1.2) = W c v := by
        intro c v
        rcases h₁ with hleft | hright
        · simp [W, collisionEmbedding, hleft, hout, j]
        · simp [W, collisionEmbedding, hright, hout, j]
      calc
        _ = ∫⁻ z : FusedConfiguration α,
            (ENNReal.ofReal (heatKernel a (z.1 - c₀)) *
              ∏ i : Spectator α, ENNReal.ofReal (heatKernel b (z.2 i - x i))) *
              W z.1 z.2 := by
                apply lintegral_congr
                intro z
                rw [hweight z.1 z.2]
        _ ≤ heatPotentialRowBound b := by
              apply lintegral_fusedTensor_weight_le α ha c₀ x W hW
              intro c
              simpa [W, heatPotential_sub_swap] using
                (lintegral_tensorHeatKernel_mul_shiftedPotential_le hb j x c)
  · by_cases h₂ : β.1.2 = α.1.1 ∨ β.1.2 = α.1.2
    · have hout : β.1.1 ≠ α.1.1 ∧ β.1.1 ≠ α.1.2 := by
        simpa only [not_or] using h₁
      let i : Spectator α := ⟨β.1.1, hout⟩
      let W : Plane → (Spectator α → Plane) → ℝ≥0∞ := fun c v =>
        heatPotential (v i - c)
      have hW : Measurable (Function.uncurry W) := by
        dsimp [W]
        exact measurable_heatPotential.comp
          (((measurable_pi_apply i).comp measurable_snd).sub measurable_fst)
      have hweight : ∀ c : Plane, ∀ v : Spectator α → Plane,
          heatPotential ((collisionEmbedding α (c, v)) β.1.1 -
            (collisionEmbedding α (c, v)) β.1.2) = W c v := by
        intro c v
        rcases h₂ with hleft | hright
        · simp [W, collisionEmbedding, hleft, hout, i]
        · simp [W, collisionEmbedding, hright, hout, i]
      calc
        _ = ∫⁻ z : FusedConfiguration α,
            (ENNReal.ofReal (heatKernel a (z.1 - c₀)) *
              ∏ i' : Spectator α, ENNReal.ofReal (heatKernel b (z.2 i' - x i'))) *
              W z.1 z.2 := by
                apply lintegral_congr
                intro z
                rw [hweight z.1 z.2]
        _ ≤ heatPotentialRowBound b := by
              apply lintegral_fusedTensor_weight_le α ha c₀ x W hW
              intro c
              exact lintegral_tensorHeatKernel_mul_shiftedPotential_le hb i x c
    · have hout₁ : β.1.1 ≠ α.1.1 ∧ β.1.1 ≠ α.1.2 := by
        simpa only [not_or] using h₁
      have hout₂ : β.1.2 ≠ α.1.1 ∧ β.1.2 ≠ α.1.2 := by
        simpa only [not_or] using h₂
      let i : Spectator α := ⟨β.1.1, hout₁⟩
      let j : Spectator α := ⟨β.1.2, hout₂⟩
      have hij : i ≠ j := by
        intro he
        have hv := congrArg Subtype.val he
        exact (ne_of_lt β.2) hv
      let W : Plane → (Spectator α → Plane) → ℝ≥0∞ := fun _ v =>
        heatPotential (v i - v j)
      have hW : Measurable (Function.uncurry W) := by
        dsimp [W]
        exact measurable_heatPotential.comp
          (((measurable_pi_apply i).comp measurable_snd).sub
            ((measurable_pi_apply j).comp measurable_snd))
      have hweight : ∀ c : Plane, ∀ v : Spectator α → Plane,
          heatPotential ((collisionEmbedding α (c, v)) β.1.1 -
            (collisionEmbedding α (c, v)) β.1.2) = W c v := by
        intro c v
        simp [W, collisionEmbedding, hout₁, hout₂, i, j]
      calc
        _ = ∫⁻ z : FusedConfiguration α,
            (ENNReal.ofReal (heatKernel a (z.1 - c₀)) *
              ∏ i' : Spectator α, ENNReal.ofReal (heatKernel b (z.2 i' - x i'))) *
              W z.1 z.2 := by
                apply lintegral_congr
                intro z
                rw [hweight z.1 z.2]
        _ ≤ heatPotentialRowBound b := by
              apply lintegral_fusedTensor_weight_le α ha c₀ x W hW
              intro c
              exact lintegral_tensorHeatKernel_mul_pairPotential_le hb i j hij x

private theorem lintegral_collisionKernel_nextPotential_le {n : ℕ}
    (α β : CollisionPair n) (hne : α ≠ β) (θ : ℝ) {t : ℝ} (ht : 0 < t)
    (z₀ : FusedConfiguration α) :
    (∫⁻ z : FusedConfiguration α,
      ENNReal.ofReal (collisionKernel α θ t z₀ z) *
        heatPotential ((collisionEmbedding α z) β.1.1 -
          (collisionEmbedding α z) β.1.2)) ≤
      ENNReal.ofReal (4 * Real.pi * scalarDensity θ t) * heatPotentialRowBound t := by
  let κ : ℝ := 4 * Real.pi * scalarDensity θ t
  let H : FusedConfiguration α → ℝ≥0∞ := fun z =>
    (ENNReal.ofReal (heatKernel (t / 2) (z.1 - z₀.1)) *
      ∏ i : Spectator α, ENNReal.ofReal (heatKernel t (z.2 i - z₀.2 i))) *
      heatPotential ((collisionEmbedding α z) β.1.1 -
        (collisionEmbedding α z) β.1.2)
  have hκ : 0 ≤ κ := by
    dsimp [κ]
    exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
      (scalarDensity_pos θ ht).le
  have hH : Measurable H := by
    dsimp [H]
    have hc : Measurable (fun z : FusedConfiguration α =>
        heatKernel (t / 2) (z.1 - z₀.1)) := by
      unfold heatKernel
      fun_prop
    have hs : Measurable (fun z : FusedConfiguration α =>
        ∏ i : Spectator α, ENNReal.ofReal (heatKernel t (z.2 i - z₀.2 i))) := by
      apply Finset.measurable_fun_prod
      intro i hi
      have hm : Measurable (fun z : FusedConfiguration α =>
          heatKernel t (z.2 i - z₀.2 i)) := by
        unfold heatKernel
        fun_prop
      exact hm.ennreal_ofReal
    have hp : Measurable (fun z : FusedConfiguration α =>
        heatPotential ((collisionEmbedding α z) β.1.1 -
          (collisionEmbedding α z) β.1.2)) := by
      exact measurable_heatPotential.comp
        (((measurable_pi_apply β.1.1).comp (measurable_collisionEmbedding α)).sub
          ((measurable_pi_apply β.1.2).comp (measurable_collisionEmbedding α)))
    exact ((hc.ennreal_ofReal).mul hs).mul hp
  have hpoint (z : FusedConfiguration α) :
      ENNReal.ofReal (collisionKernel α θ t z₀ z) *
        heatPotential ((collisionEmbedding α z) β.1.1 -
          (collisionEmbedding α z) β.1.2) = ENNReal.ofReal κ * H z := by
    have hkernel : collisionKernel α θ t z₀ z =
        κ * (heatKernel (t / 2) (z.1 - z₀.1) *
          ∏ i : Spectator α, heatKernel t (z.2 i - z₀.2 i)) := by
      simp [collisionKernel, κ]
      ac_rfl
    rw [hkernel, ENNReal.ofReal_mul hκ,
      ENNReal.ofReal_mul (Critical2DKPZ.heatKernel_pos (by positivity : 0 < t / 2) _).le,
      ENNReal.ofReal_prod_of_nonneg (fun i hi =>
        (Critical2DKPZ.heatKernel_pos ht _).le)]
    dsimp [H]
    ac_rfl
  have hrow := lintegral_fusedPairPotential_separated_le α β hne
    (by positivity : 0 < t / 2) ht z₀.1 z₀.2
  calc
    _ = ∫⁻ z : FusedConfiguration α, ENNReal.ofReal κ * H z := by
          apply lintegral_congr
          exact hpoint
    _ = ENNReal.ofReal κ * ∫⁻ z : FusedConfiguration α, H z :=
          lintegral_const_mul (ENNReal.ofReal κ) hH
    _ ≤ ENNReal.ofReal κ * heatPotentialRowBound t :=
          mul_le_mul_right hrow (ENNReal.ofReal κ)

private theorem lintegral_incoming_collision_nextPotential_le {n : ℕ}
    (α β : CollisionPair n) (hne : α ≠ β) (θ : ℝ)
    {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (x : Configuration n) :
    (∫⁻ z : FusedConfiguration α, ∫⁻ z' : FusedConfiguration α,
      (ENNReal.ofReal (incomingKernel α r z x) *
        ENNReal.ofReal (collisionKernel α θ t z z')) *
        heatPotential ((collisionEmbedding α z') β.1.1 -
          (collisionEmbedding α z') β.1.2)) ≤
      ENNReal.ofReal (heatKernel (2 * r) (x α.1.2 - x α.1.1)) *
        (ENNReal.ofReal (4 * Real.pi * scalarDensity θ t) * heatPotentialRowBound t) := by
  have hW (z : FusedConfiguration α) : Measurable (fun z' : FusedConfiguration α =>
      ENNReal.ofReal (collisionKernel α θ t z z') *
        heatPotential ((collisionEmbedding α z') β.1.1 -
          (collisionEmbedding α z') β.1.2)) := by
    have hc : Measurable (fun z' : FusedConfiguration α =>
        collisionKernel α θ t z z') := by
      unfold collisionKernel heatKernel
      fun_prop
    have hp : Measurable (fun z' : FusedConfiguration α =>
        heatPotential ((collisionEmbedding α z') β.1.1 -
          (collisionEmbedding α z') β.1.2)) := by
      exact measurable_heatPotential.comp
        (((measurable_pi_apply β.1.1).comp (measurable_collisionEmbedding α)).sub
          ((measurable_pi_apply β.1.2).comp (measurable_collisionEmbedding α)))
    exact hc.ennreal_ofReal.mul hp
  have hI : Measurable (fun z : FusedConfiguration α =>
      ENNReal.ofReal (incomingKernel α r z x)) := by
    exact ((measurable_incomingKernel α).comp
      (measurable_const.prodMk (measurable_id.prodMk measurable_const))).ennreal_ofReal
  calc
    _ = ∫⁻ z : FusedConfiguration α,
        ENNReal.ofReal (incomingKernel α r z x) *
          (∫⁻ z' : FusedConfiguration α,
            ENNReal.ofReal (collisionKernel α θ t z z') *
              heatPotential ((collisionEmbedding α z') β.1.1 -
                (collisionEmbedding α z') β.1.2)) := by
          apply lintegral_congr
          intro z
          calc
            _ = ∫⁻ z' : FusedConfiguration α,
                  ENNReal.ofReal (incomingKernel α r z x) *
                    (ENNReal.ofReal (collisionKernel α θ t z z') *
                      heatPotential ((collisionEmbedding α z') β.1.1 -
                        (collisionEmbedding α z') β.1.2)) := by
                    apply lintegral_congr
                    intro z'
                    ac_rfl
            _ = _ := lintegral_const_mul _ (hW z)
    _ ≤ ∫⁻ z : FusedConfiguration α,
        ENNReal.ofReal (incomingKernel α r z x) *
          (ENNReal.ofReal (4 * Real.pi * scalarDensity θ t) * heatPotentialRowBound t) := by
          apply lintegral_mono
          intro z
          exact mul_le_mul_right
            (lintegral_collisionKernel_nextPotential_le α β hne θ ht z)
            (ENNReal.ofReal (incomingKernel α r z x))
    _ = (ENNReal.ofReal (4 * Real.pi * scalarDensity θ t) * heatPotentialRowBound t) *
          ∫⁻ z : FusedConfiguration α, ENNReal.ofReal (incomingKernel α r z x) := by
          rw [lintegral_mul_const _ hI]
          ac_rfl
    _ = _ := by rw [lintegral_incomingKernel_fused α hr x]; ac_rfl

private theorem measurable_firstLetterActionKernel
    (θ τ : ℝ) {h : ℕ} (α : CollisionPair h) (w : List (CollisionPair h))
    (x : Configuration h) :
    Measurable (fun z : ((ℝ × ℝ) ×
        (FusedConfiguration α × FusedConfiguration α)) × Configuration h =>
      (ENNReal.ofReal (incomingKernel α z.1.1.1 z.1.2.1 x) *
        ENNReal.ofReal (collisionKernel α θ z.1.1.2 z.1.2.1 z.1.2.2)) *
        diagramKernel θ w (τ - z.1.1.1 - z.1.1.2)
          (collisionEmbedding α z.1.2.2) z.2) := by
  have hr : Measurable (fun z : ((ℝ × ℝ) ×
      (FusedConfiguration α × FusedConfiguration α)) × Configuration h => z.1.1.1) := by fun_prop
  have hs : Measurable (fun z : ((ℝ × ℝ) ×
      (FusedConfiguration α × FusedConfiguration α)) × Configuration h => z.1.1.2) := by fun_prop
  have hz : Measurable (fun z : ((ℝ × ℝ) ×
      (FusedConfiguration α × FusedConfiguration α)) × Configuration h => z.1.2.1) := by fun_prop
  have hz' : Measurable (fun z : ((ℝ × ℝ) ×
      (FusedConfiguration α × FusedConfiguration α)) × Configuration h => z.1.2.2) := by fun_prop
  have hi := ((measurable_incomingKernel α).comp
    (hr.prodMk (hz.prodMk (measurable_const (a := x))))).ennreal_ofReal
  have hc := ((measurable_collisionKernel α).comp
    (((measurable_const (a := θ)).prodMk hs).prodMk (hz.prodMk hz'))).ennreal_ofReal
  have ht := measurable_diagramKernel_comp w (measurable_const (a := θ))
    (((measurable_const (a := τ)).sub hr).sub hs)
    ((measurable_collisionEmbedding α).comp hz') measurable_snd
  exact (hi.mul hc).mul ht

private theorem lintegral_durationTriangle (τ : ℝ) {F : ℝ × ℝ → ℝ≥0∞}
    (hF : Measurable F) :
    (∫⁻ q in {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < τ}, F q) =
      ∫⁻ r in Ioo 0 τ, ∫⁻ s in Ioo 0 (τ - r), F (r, s) := by
  let D : Set (ℝ × ℝ) := {q | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < τ}
  have hD : MeasurableSet D := by dsimp [D]; measurability
  rw [← lintegral_indicator hD, Measure.volume_eq_prod,
    lintegral_prod _ (hF.indicator hD).aemeasurable,
    ← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro r
  by_cases hr : r ∈ Ioo 0 τ
  · rw [indicator_of_mem hr, ← lintegral_indicator measurableSet_Ioo]
    apply lintegral_congr
    intro s
    have he : (r, s) ∈ D ↔ s ∈ Ioo 0 (τ - r) := by
      simp only [D, mem_ofPred_eq, mem_Ioo]
      constructor
      · rintro ⟨_, hs, ht⟩
        exact ⟨hs, by linarith only [ht]⟩
      · rintro ⟨hs, ht⟩
        exact ⟨hr.1, hs, by linarith only [ht]⟩
    simp only [indicator, he]
  · rw [indicator_of_notMem hr]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [] with s
    have hn : (r, s) ∉ D := by
      rintro ⟨hr0, hs, ht⟩
      exact hr ⟨hr0, by linarith only [hs, ht]⟩
    exact indicator_of_notMem hn F

private theorem diagramKernel_cons_duration_action
    (θ τ : ℝ) {h : ℕ} (α : CollisionPair h) (w : List (CollisionPair h))
    (x y : Configuration h) :
    diagramKernel θ (α :: w) τ x y =
      ∫⁻ q in {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < τ},
        ∫⁻ p : FusedConfiguration α × FusedConfiguration α,
          (ENNReal.ofReal (incomingKernel α q.1 p.1 x) *
            ENNReal.ofReal (collisionKernel α θ q.2 p.1 p.2)) *
            diagramKernel θ w (τ - q.1 - q.2) (collisionEmbedding α p.2) y := by
  have : SigmaFinite (volume : Measure (Spectator α → Plane)) := by infer_instance
  have : SigmaFinite (volume : Measure (FusedConfiguration α)) := by infer_instance
  have : SFinite (volume : Measure (FusedConfiguration α × FusedConfiguration α)) := by infer_instance
  have hJ : Measurable (fun z : (ℝ × ℝ) ×
      (FusedConfiguration α × FusedConfiguration α) =>
      (ENNReal.ofReal (incomingKernel α z.1.1 z.2.1 x) *
        ENNReal.ofReal (collisionKernel α θ z.1.2 z.2.1 z.2.2)) *
        diagramKernel θ w (τ - z.1.1 - z.1.2) (collisionEmbedding α z.2.2) y) :=
    by
      have hmap : Measurable (fun z : (ℝ × ℝ) ×
          (FusedConfiguration α × FusedConfiguration α) => (z, y)) :=
        measurable_id.prodMk measurable_const
      have hm := (measurable_firstLetterActionKernel θ τ α w x).comp hmap
      dsimp only [Function.comp_def] at hm
      exact hm
  rw [lintegral_durationTriangle τ (hJ.lintegral_prod_right'
    (ν := (volume : Measure (FusedConfiguration α × FusedConfiguration α))))]
  rw [diagramKernel]
  apply lintegral_congr
  intro r
  have hspace (s : ℝ) :
      (∫⁻ p : FusedConfiguration α × FusedConfiguration α,
        (ENNReal.ofReal (incomingKernel α r p.1 x) *
          ENNReal.ofReal (collisionKernel α θ s p.1 p.2)) *
          diagramKernel θ w (τ - r - s) (collisionEmbedding α p.2) y) =
      ∫⁻ z : FusedConfiguration α, ∫⁻ z' : FusedConfiguration α,
        (ENNReal.ofReal (incomingKernel α r z x) *
          ENNReal.ofReal (collisionKernel α θ s z z')) *
          diagramKernel θ w (τ - r - s) (collisionEmbedding α z') y := by
    have hmap : Measurable (fun p : FusedConfiguration α × FusedConfiguration α =>
        ((r, s), p)) := measurable_const.prodMk measurable_id
    have hm := hJ.comp hmap
    dsimp only [Function.comp_def] at hm
    rw [Measure.volume_eq_prod, lintegral_prod _ hm.aemeasurable]
  simp_rw [hspace]
  have he := lintegral_Ioo_sub_right r τ (fun s =>
    ∫⁻ z : FusedConfiguration α, ∫⁻ z' : FusedConfiguration α,
      (ENNReal.ofReal (incomingKernel α r z x) *
        ENNReal.ofReal (collisionKernel α θ s z z')) *
        diagramKernel θ w (τ - r - s) (collisionEmbedding α z') y)
  simpa only [sub_sub_sub_cancel_right] using he.symm

private theorem lintegral_diagramKernel_lt_top_of_separated
    (θ : ℝ) {h : ℕ} (α : CollisionPair h) (w : List (CollisionPair h))
    (hw : (α :: w).IsChain (· ≠ ·)) {τ : ℝ} (hτ : 0 < τ)
    (x : Configuration h) (hsep : x α.1.1 ≠ x α.1.2) :
    (∫⁻ y : Configuration h, diagramKernel θ (α :: w) τ x y) < ⊤ := by
  obtain ⟨C, _hC, hbound⟩ :=
    exists_lintegral_diagramKernel_row_le_heatPotential θ α w hw hτ
  have hpotential : heatPotential (x α.1.2 - x α.1.1) ≠ ⊤ :=
    heatPotential_ne_top_of_ne_zero (sub_ne_zero.mpr hsep.symm)
  exact lt_of_le_of_lt (hbound x) (ENNReal.mul_lt_top
    (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top) (lt_top_iff_ne_top.mpr hpotential))

private theorem lintegral_firstLetterActionKernel_lt_top
    (θ : ℝ) {h : ℕ} (α : CollisionPair h) (w : List (CollisionPair h))
    (hw : (α :: w).IsChain (· ≠ ·)) {r t s : ℝ}
    (hr : 0 < r) (ht : 0 < t) (hs : 0 < s) (x : Configuration h) :
    (∫⁻ p : FusedConfiguration α × FusedConfiguration α, ∫⁻ y : Configuration h,
      (ENNReal.ofReal (incomingKernel α r p.1 x) *
        ENNReal.ofReal (collisionKernel α θ t p.1 p.2)) *
        diagramKernel θ w s (collisionEmbedding α p.2) y) < ⊤ := by
  have hI : Measurable (fun z : FusedConfiguration α =>
      ENNReal.ofReal (incomingKernel α r z x)) := by
    have hmap : Measurable (fun z : FusedConfiguration α => (r, z, x)) :=
      measurable_const.prodMk (measurable_id.prodMk measurable_const)
    have hm := (measurable_incomingKernel α).comp hmap
    dsimp only [Function.comp_def] at hm
    exact hm.ennreal_ofReal
  have hC : Measurable (fun p : FusedConfiguration α × FusedConfiguration α =>
      ENNReal.ofReal (collisionKernel α θ t p.1 p.2)) := by
    have hmap : Measurable (fun p : FusedConfiguration α × FusedConfiguration α =>
        ((θ, t), p)) := measurable_const.prodMk measurable_id
    have hm := (measurable_collisionKernel α).comp hmap
    dsimp only [Function.comp_def] at hm
    exact hm.ennreal_ofReal
  have hweight : Measurable (fun p : FusedConfiguration α × FusedConfiguration α =>
      ENNReal.ofReal (incomingKernel α r p.1 x) *
        ENNReal.ofReal (collisionKernel α θ t p.1 p.2)) := by
    simpa only [Function.comp_def, Pi.mul_def] using (hI.comp measurable_fst).mul hC
  have hfactor :
      (∫⁻ p : FusedConfiguration α × FusedConfiguration α, ∫⁻ y : Configuration h,
        (ENNReal.ofReal (incomingKernel α r p.1 x) *
          ENNReal.ofReal (collisionKernel α θ t p.1 p.2)) *
          diagramKernel θ w s (collisionEmbedding α p.2) y) =
      ∫⁻ p : FusedConfiguration α × FusedConfiguration α,
        (ENNReal.ofReal (incomingKernel α r p.1 x) *
          ENNReal.ofReal (collisionKernel α θ t p.1 p.2)) *
          (∫⁻ y : Configuration h, diagramKernel θ w s (collisionEmbedding α p.2) y) := by
    apply lintegral_congr
    intro p
    exact lintegral_const_mul' _ _ (by finiteness)
  rw [hfactor]
  cases w with
  | nil =>
    have hmass (z : FusedConfiguration α) :
        (∫⁻ y : Configuration h, diagramKernel θ [] s (collisionEmbedding α z) y) = 1 := by
      change (∫⁻ y : Configuration h, ENNReal.ofReal (freeKernel h s (collisionEmbedding α z) y)) = 1
      rw [← ofReal_integral_eq_lintegral_ofReal
        (integrable_freeKernel_right h hs (collisionEmbedding α z))
        (Eventually.of_forall fun y => (freeKernel_pos h hs _ y).le),
        integral_freeKernel_right h hs, ENNReal.ofReal_one]
    simp_rw [hmass, mul_one]
    rw [Measure.volume_eq_prod, lintegral_prod _ hweight.aemeasurable]
    have hinner (z : FusedConfiguration α) :
        (∫⁻ z' : FusedConfiguration α,
          ENNReal.ofReal (incomingKernel α r z x) *
            ENNReal.ofReal (collisionKernel α θ t z z')) =
          ENNReal.ofReal (incomingKernel α r z x) *
            ENNReal.ofReal (4 * Real.pi * scalarDensity θ t) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_collisionKernel_right α θ ht]
    simp_rw [hinner]
    rw [lintegral_mul_const _ hI, lintegral_incomingKernel_fused α hr x]
    finiteness
  | cons β v =>
    have hne : α ≠ β := (List.isChain_cons_cons.mp hw).1
    obtain ⟨C, _hC, hbound⟩ :=
      exists_lintegral_diagramKernel_row_le_heatPotential θ β v hw.tail hs
    have hrow (z : FusedConfiguration α) :
        (∫⁻ y : Configuration h, diagramKernel θ (β :: v) s (collisionEmbedding α z) y) ≤
          ENNReal.ofReal C * heatPotential ((collisionEmbedding α z) β.1.1 -
            (collisionEmbedding α z) β.1.2) := by
      rw [heatPotential_sub_swap]
      exact hbound (collisionEmbedding α z)
    have hP : Measurable (fun p : FusedConfiguration α × FusedConfiguration α =>
        heatPotential ((collisionEmbedding α p.2) β.1.1 -
          (collisionEmbedding α p.2) β.1.2)) := by
      exact measurable_heatPotential.comp
        ((((measurable_pi_apply β.1.1).comp (measurable_collisionEmbedding α)).comp
          measurable_snd).sub
          (((measurable_pi_apply β.1.2).comp (measurable_collisionEmbedding α)).comp
            measurable_snd))
    have hspatial :
        (∫⁻ p : FusedConfiguration α × FusedConfiguration α,
          (ENNReal.ofReal (incomingKernel α r p.1 x) *
            ENNReal.ofReal (collisionKernel α θ t p.1 p.2)) *
            heatPotential ((collisionEmbedding α p.2) β.1.1 -
              (collisionEmbedding α p.2) β.1.2)) ≤
          ENNReal.ofReal (heatKernel (2 * r) (x α.1.2 - x α.1.1)) *
            (ENNReal.ofReal (4 * Real.pi * scalarDensity θ t) * heatPotentialRowBound t) := by
      have hm : Measurable (fun p : FusedConfiguration α × FusedConfiguration α =>
          (ENNReal.ofReal (incomingKernel α r p.1 x) *
            ENNReal.ofReal (collisionKernel α θ t p.1 p.2)) *
            heatPotential ((collisionEmbedding α p.2) β.1.1 -
              (collisionEmbedding α p.2) β.1.2)) := hweight.mul hP
      rw [Measure.volume_eq_prod, lintegral_prod _ hm.aemeasurable]
      exact lintegral_incoming_collision_nextPotential_le α β hne θ hr ht x
    have hle :
        (∫⁻ p : FusedConfiguration α × FusedConfiguration α,
          (ENNReal.ofReal (incomingKernel α r p.1 x) *
            ENNReal.ofReal (collisionKernel α θ t p.1 p.2)) *
            (∫⁻ y : Configuration h,
              diagramKernel θ (β :: v) s (collisionEmbedding α p.2) y)) ≤
          ENNReal.ofReal C *
            (ENNReal.ofReal (heatKernel (2 * r) (x α.1.2 - x α.1.1)) *
              (ENNReal.ofReal (4 * Real.pi * scalarDensity θ t) * heatPotentialRowBound t)) := by
      calc
        _ ≤ ∫⁻ p : FusedConfiguration α × FusedConfiguration α,
            (ENNReal.ofReal (incomingKernel α r p.1 x) *
              ENNReal.ofReal (collisionKernel α θ t p.1 p.2)) *
              (ENNReal.ofReal C * heatPotential ((collisionEmbedding α p.2) β.1.1 -
                (collisionEmbedding α p.2) β.1.2)) := by
            apply lintegral_mono
            intro p
            exact mul_le_mul_right (hrow p.2) _
        _ = ENNReal.ofReal C *
            (∫⁻ p : FusedConfiguration α × FusedConfiguration α,
              (ENNReal.ofReal (incomingKernel α r p.1 x) *
                ENNReal.ofReal (collisionKernel α θ t p.1 p.2)) *
                heatPotential ((collisionEmbedding α p.2) β.1.1 -
                  (collisionEmbedding α p.2) β.1.2)) := by
            rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            apply lintegral_congr
            intro p
            ac_rfl
        _ ≤ _ := mul_le_mul_right hspatial (ENNReal.ofReal C)
    apply lt_of_le_of_lt hle
    have hPfinite := heatPotentialRowBound_ne_top t
    finiteness

/-- The signed tensor action of the first collision letter, with absolute
integrability both on every interior time slice and over the full time domain. -/
theorem integrable_integral_diagramKernel_cons_tensor_action
    (θ : ℝ) {h : ℕ} (α : CollisionPair h) (w : List (CollisionPair h))
    (hw : (α :: w).IsChain (· ≠ ·)) {τ : ℝ} (hτ : 0 < τ)
    (x : Configuration h) (hsep : x α.1.1 ≠ x α.1.2)
    (ψ : Fin h → C_c(Plane, ℝ)) :
    let D : Set (ℝ × ℝ) := {q | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < τ}
    let A : (ℝ × ℝ) → (FusedConfiguration α × FusedConfiguration α) → ℝ :=
      fun q p => incomingKernel α q.1 p.1 x * collisionKernel α θ q.2 p.1 p.2 *
        (∫ y : Configuration h, (∏ i, ψ i (y i)) *
          (diagramKernel θ w (τ - q.1 - q.2) (collisionEmbedding α p.2) y).toReal)
    Integrable (fun y : Configuration h =>
      (∏ i, ψ i (y i)) * (diagramKernel θ (α :: w) τ x y).toReal) ∧
    (∀ q ∈ D, Integrable (A q)) ∧
    IntegrableOn (fun q => ∫ p, A q p) D ∧
    (∫ y : Configuration h, (∏ i, ψ i (y i)) *
      (diagramKernel θ (α :: w) τ x y).toReal) = ∫ q in D, ∫ p, A q p := by
  have : SigmaFinite (volume : Measure (Spectator α → Plane)) := by infer_instance
  have : SigmaFinite (volume : Measure (FusedConfiguration α)) := by infer_instance
  have : SigmaFinite (volume : Measure (FusedConfiguration α × FusedConfiguration α)) := by
    infer_instance
  let P := FusedConfiguration α × FusedConfiguration α
  let X := (ℝ × ℝ) × P
  let D : Set (ℝ × ℝ) := {q | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < τ}
  let g : Configuration h → ℝ := fun y => ∏ i, ψ i (y i)
  let A : (ℝ × ℝ) → P → ℝ := fun q p =>
    incomingKernel α q.1 p.1 x * collisionKernel α θ q.2 p.1 p.2 *
      (∫ y : Configuration h, g y *
        (diagramKernel θ w (τ - q.1 - q.2) (collisionEmbedding α p.2) y).toReal)
  let μ : Measure (ℝ × ℝ) := volume.restrict D
  let ξ : Measure X := μ.prod volume
  let K₀ : Configuration h → ℝ≥0∞ := diagramKernel θ (α :: w) τ x
  let K : X × Configuration h → ℝ≥0∞ := fun z =>
    (ENNReal.ofReal (incomingKernel α z.1.1.1 z.1.2.1 x) *
      ENNReal.ofReal (collisionKernel α θ z.1.1.2 z.1.2.1 z.1.2.2)) *
      diagramKernel θ w (τ - z.1.1.1 - z.1.1.2)
        (collisionEmbedding α z.1.2.2) z.2
  change Integrable (fun y => g y * (K₀ y).toReal) ∧
    (∀ q ∈ D, Integrable (A q)) ∧
    IntegrableOn (fun q => ∫ p, A q p) D ∧
    (∫ y, g y * (K₀ y).toReal) = ∫ q in D, ∫ p, A q p
  have hD : MeasurableSet D := by dsimp [D]; measurability
  have hK : Measurable K := measurable_firstLetterActionKernel θ τ α w x
  have hK₀ : Measurable K₀ :=
    measurable_diagramKernel_comp (α :: w) measurable_const measurable_const
      measurable_const measurable_id
  have hpartial (y : Configuration h) : Measurable (fun v : X => K (v, y)) := by
    have hmap : Measurable (fun v : X => (v, y)) := measurable_id.prodMk measurable_const
    have hm := hK.comp hmap
    simpa only [Function.comp_def] using hm
  have hrepr (y : Configuration h) : K₀ y = ∫⁻ v, K (v, y) ∂ξ := by
    rw [lintegral_prod _ (hpartial y).aemeasurable]
    exact diagramKernel_cons_duration_action θ τ α w x y
  have haction (f : Configuration h → ℝ≥0∞) (hf : Measurable f) :
      (∫⁻ y, K₀ y * f y) = ∫⁻ v, ∫⁻ y, K (v, y) * f y ∂volume ∂ξ := by
    calc
      _ = ∫⁻ y, (∫⁻ v, K (v, y) ∂ξ) * f y := by
        apply lintegral_congr
        intro y
        rw [hrepr]
      _ = ∫⁻ y, ∫⁻ v, K (v, y) * f y ∂ξ := by
        apply lintegral_congr
        intro y
        exact (lintegral_mul_const (f y) (hpartial y)).symm
      _ = _ := lintegral_lintegral_swap
        ((hK.comp measurable_swap).mul (hf.comp measurable_fst)).aemeasurable
  have hfinite : (∫⁻ y, K₀ y) < ⊤ :=
    lintegral_diagramKernel_lt_top_of_separated θ α w hw hτ x hsep
  have hg : Measurable g := measurable_tensorTest ψ
  obtain ⟨B, _hB, hB⟩ := exists_tensorTest_bound ψ
  have hBg (y : Configuration h) : ‖g y‖ ≤ B := by
    rw [Real.norm_eq_abs]
    exact hB y
  obtain ⟨hi₀, hi, heq⟩ := signed_action_of_lintegral_action ξ volume
    K₀ K hK₀ hK hfinite haction g hg B hBg
  have hTeq (q : ℝ × ℝ) (hq : q ∈ D) (p : P) :
      (∫ y : Configuration h, g y * (K ((q, p), y)).toReal) = A q p := by
    have hIpos := (incomingKernel_pos α hq.1 p.1 x).le
    have hCpos := (collisionKernel_pos α θ hq.2.1 p.1 p.2).le
    dsimp only [A]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    dsimp only [K]
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hIpos, ENNReal.toReal_ofReal hCpos]
    ring
  have hqAE : ∀ᵐ v : X ∂ξ, v.1 ∈ D := by
    apply (Measure.ae_prod_iff_ae_ae (hD.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem hD] with q hq
    exact Eventually.of_forall fun _ => hq
  have hAE : (fun v : X => ∫ y : Configuration h, g y * (K (v, y)).toReal) =ᵐ[ξ]
      (fun v : X => A v.1 v.2) := by
    filter_upwards [hqAE] with v hv
    exact hTeq v.1 hv v.2
  have hiA : Integrable (fun v : X => A v.1 v.2) ξ := hi.integral_prod_left.congr hAE
  have hslices (q : ℝ × ℝ) (hq : q ∈ D) : Integrable (A q) := by
    let Kq : P × Configuration h → ℝ≥0∞ := fun z => K ((q, z.1), z.2)
    have hKq : Measurable Kq := by
      have hmap : Measurable (fun z : P × Configuration h => ((q, z.1), z.2)) :=
        (measurable_const.prodMk measurable_fst).prodMk measurable_snd
      have hm := hK.comp hmap
      simpa only [Kq, Function.comp_def] using hm
    have hfiniteq : (∫⁻ z, Kq z ∂(volume : Measure P).prod volume) < ⊤ := by
      rw [lintegral_prod _ hKq.aemeasurable]
      exact lintegral_firstLetterActionKernel_lt_top θ α w hw
        (r := q.1) (t := q.2) (s := τ - q.1 - q.2) hq.1 hq.2.1
        (by dsimp [D] at hq; linarith only [hq.2.2]) x
    have hiq := integrable_mul_toReal_of_lintegral_lt_top
      ((volume : Measure P).prod volume) Kq hKq.aestronglyMeasurable hfiniteq
      (fun z => g z.2) (hg.comp measurable_snd).aestronglyMeasurable B
      (Eventually.of_forall fun z => hBg z.2)
    apply hiq.integral_prod_left.congr
    exact Eventually.of_forall fun p => hTeq q hq p
  refine ⟨hi₀, hslices, hiA.integral_prod_left, ?_⟩
  calc
    _ = ∫ z, g z.2 * (K z).toReal ∂ξ.prod volume := heq
    _ = ∫ v, ∫ y : Configuration h, g y * (K (v, y)).toReal ∂volume ∂ξ :=
      integral_prod _ hi
    _ = ∫ v : X, A v.1 v.2 ∂ξ := integral_congr_ae hAE
    _ = ∫ q in D, ∫ p : P, A q p := integral_prod _ hiA

end Critical2DKPZ.SHF.Moments

end
