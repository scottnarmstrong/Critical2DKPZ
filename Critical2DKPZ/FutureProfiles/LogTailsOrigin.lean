/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.FutureProfiles.SplitBoundInputs
public import Critical2DKPZ.FutureProfiles.SplitInputs
import Critical2DKPZ.Smoothing.Measurability
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! # Logarithmic tail bounds at the origin -/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal
open Critical2DKPZ.Polymer Critical2DKPZ.Smoothing

namespace Critical2DKPZ.FutureProfiles

private theorem eLpNorm_le_of_exp_tail {μ : Measure Disorder} [IsProbabilityMeasure μ]
    {f : Disorder → ℝ} (hf : AEStronglyMeasurable f μ) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp_top : p ≠ ∞) {B : ℝ} (hB : 1 ≤ B)
    (hTail : ∀ u : ℝ, 0 ≤ u → (μ {ω | u < |f ω|}).toReal ≤ B * Real.exp (-u / 3)) :
    eLpNorm f p μ ≤ ENNReal.ofReal
      (3 * Real.log B + (p.toReal * 3 ^ p.toReal * Real.Gamma p.toReal) ^ (1 / p.toReal)) := by
  let q : ℝ := p.toReal
  have hqpos : 0 < q := by
    dsimp [q]
    exact ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)) hp_top
  have hqge : 1 ≤ q := by
    dsimp [q]
    exact (ENNReal.toReal_le_toReal ENNReal.one_ne_top hp_top).2 hp
  have hBpos : 0 < B := by linarith
  let a : ℝ := 3 * Real.log B
  have ha : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (by norm_num) (Real.log_nonneg hB)
  have hshift : ∀ u : ℝ, 0 ≤ u → (μ {ω | u < max (|f ω| - a) 0}).toReal ≤ Real.exp (-u / 3) := by
    intro u hu
    have hsub : {ω | u < max (|f ω| - a) 0} ⊆ {ω | a + u < |f ω|} := by
      intro ω hω
      change u < max (|f ω| - a) 0 at hω
      change a + u < |f ω|
      by_cases hnonneg : 0 ≤ |f ω| - a
      · rw [max_eq_left hnonneg] at hω
        linarith
      · rw [max_eq_right (le_of_not_ge hnonneg)] at hω
        exact (not_lt_of_ge hu hω).elim
    have htail := hTail (a + u) (by linarith)
    have hfactor : B * Real.exp (-(a + u) / 3) = Real.exp (-u / 3) := by
      calc
        B * Real.exp (-(a + u) / 3) = Real.exp (Real.log B) * Real.exp (-(a + u) / 3) := by
          rw [Real.exp_log hBpos]
        _ = Real.exp (Real.log B + (-(a + u) / 3)) := (Real.exp_add _ _).symm
        _ = Real.exp (-u / 3) := by congr 1; dsimp [a]; ring
    calc
      (μ {ω | u < max (|f ω| - a) 0}).toReal ≤
          (μ {ω | a + u < |f ω|}).toReal := by
            exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsub)
      _ ≤ B * Real.exp (-(a + u) / 3) := htail
      _ = Real.exp (-u / 3) := hfactor
  let Y : Disorder → ℝ := fun ω => max (|f ω| - a) 0
  have hYmeas : AEStronglyMeasurable Y μ := by
    have hfabs : AEStronglyMeasurable (fun ω => |f ω|) μ := by
      simpa only [Real.norm_eq_abs] using hf.norm
    have hsub : AEStronglyMeasurable (fun ω => |f ω| + -a) μ :=
      hfabs.add aestronglyMeasurable_const
    exact continuous_max.comp_aestronglyMeasurable
      (hsub.prodMk aestronglyMeasurable_const)
  have hYnn : ∀ ω, 0 ≤ Y ω := fun ω => le_max_right _ _
  have hYmoment : ∫⁻ ω, ENNReal.ofReal (Y ω ^ q) ∂μ ≤
      ENNReal.ofReal (q * 3 ^ q * Real.Gamma q) := by
    rw [MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul (μ := μ)
      (Filter.Eventually.of_forall hYnn) hYmeas.aemeasurable hqpos]
    have hkernel : IntegrableOn (fun t : ℝ => t ^ (q - 1) * Real.exp (-(t / 3))) (Ioi 0) := by
      have h := integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := q - 1) (p := 1) (b := 1 / 3) (by linarith) one_pos (by norm_num)
      simpa [Real.rpow_one, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
    have hkernel_nonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
        (fun t : ℝ => t ^ (q - 1) * Real.exp (-(t / 3))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_nonneg _)
    have hkernel_int := ofReal_integral_eq_lintegral_ofReal hkernel hkernel_nonneg
    have hkernelval : ∫ t : ℝ in Ioi 0, t ^ (q - 1) * Real.exp (-(t / 3)) =
        3 ^ q * Real.Gamma q := by
      have hval := Real.integral_rpow_mul_exp_neg_mul_Ioi hqpos (by norm_num : (0 : ℝ) < 1 / 3)
      calc
        ∫ t : ℝ in Ioi 0, t ^ (q - 1) * Real.exp (-(t / 3)) =
            ∫ t : ℝ in Ioi 0, t ^ (q - 1) * Real.exp (-((1 / 3 : ℝ) * t)) := by
              apply setIntegral_congr_fun measurableSet_Ioi
              intro t ht
              ring_nf
        _ = (1 / (1 / 3 : ℝ)) ^ q * Real.Gamma q := hval
        _ = 3 ^ q * Real.Gamma q := by norm_num
    have htailEnn : ∀ t : ℝ, 0 < t → μ {ω | t < Y ω} ≤ ENNReal.ofReal (Real.exp (-t / 3)) := by
      intro t ht
      have h := hshift t ht.le
      have hne : μ {ω | t < Y ω} ≠ ∞ := measure_ne_top μ _
      calc
        μ {ω | t < Y ω} = ENNReal.ofReal (μ {ω | t < Y ω}).toReal :=
          (ENNReal.ofReal_toReal hne).symm
        _ ≤ ENNReal.ofReal (Real.exp (-t / 3)) := ENNReal.ofReal_le_ofReal h
    have hlin : ∫⁻ t in Ioi (0 : ℝ), μ {ω | t < Y ω} * ENNReal.ofReal (t ^ (q - 1)) ≤
        ENNReal.ofReal (∫ t : ℝ in Ioi 0, t ^ (q - 1) * Real.exp (-(t / 3))) := by
      calc
        ∫⁻ t in Ioi (0 : ℝ), μ {ω | t < Y ω} * ENNReal.ofReal (t ^ (q - 1)) ≤
            ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (q - 1) * Real.exp (-(t / 3))) := by
              apply lintegral_mono_ae
              filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
              have htail := htailEnn t ht
              calc
                μ {ω | t < Y ω} * ENNReal.ofReal (t ^ (q - 1)) ≤
                    ENNReal.ofReal (Real.exp (-t / 3)) * ENNReal.ofReal (t ^ (q - 1)) :=
                      by gcongr
                _ = ENNReal.ofReal (t ^ (q - 1) * Real.exp (-(t / 3))) := by
                  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
                  have hexp : Real.exp (-t / 3) = Real.exp (-(t / 3)) := by
                    congr 1
                    ring_nf
                  rw [hexp, mul_comm]
        _ = ENNReal.ofReal (∫ t : ℝ in Ioi 0, t ^ (q - 1) * Real.exp (-(t / 3))) := by
              rw [← hkernel_int]
    calc
      ENNReal.ofReal q * ∫⁻ t in Ioi (0 : ℝ), μ {ω | t < Y ω} * ENNReal.ofReal (t ^ (q - 1)) ≤
          ENNReal.ofReal q * ENNReal.ofReal (∫ t : ℝ in Ioi 0,
            t ^ (q - 1) * Real.exp (-(t / 3))) := by
              gcongr
      _ = ENNReal.ofReal (q * 3 ^ q * Real.Gamma q) := by
        rw [← ENNReal.ofReal_mul (by linarith), hkernelval]
        ring_nf
  have hYlp : eLpNorm Y p μ ≤ ENNReal.ofReal ((q * 3 ^ q * Real.Gamma q) ^ (1 / q)) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)) hp_top hYmeas]
    have hintegrand : (fun ω => ‖Y ω‖ₑ ^ p.toReal) =
        (fun ω => ENNReal.ofReal (Y ω ^ q)) := by
      funext ω
      simp [q, Real.enorm_eq_ofReal (hYnn ω),
        ENNReal.ofReal_rpow_of_nonneg (hYnn ω) hqpos.le]
    have hqdef : q = p.toReal := rfl
    have hroot := ENNReal.rpow_le_rpow hYmoment (by positivity : 0 ≤ 1 / q)
    calc
      (∫⁻ ω, ‖Y ω‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) =
          (∫⁻ ω, ENNReal.ofReal (Y ω ^ q) ∂μ) ^ (1 / q) := by
            rw [hintegrand, hqdef]
      _ ≤
          ENNReal.ofReal (q * 3 ^ q * Real.Gamma q) ^ (1 / q) := by
            simpa [q] using hroot
      _ = ENNReal.ofReal ((q * 3 ^ q * Real.Gamma q) ^ (1 / q)) := by
            rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
  have hpoint : ∀ ω, |f ω| ≤ a + Y ω := by
    intro ω
    dsimp [Y]
    calc
      |f ω| = a + (|f ω| - a) := by ring
      _ ≤ a + max (|f ω| - a) 0 := by gcongr; exact le_max_left _ _
  have hmajor : eLpNorm f p μ ≤ eLpNorm (fun ω => a + Y ω) p μ :=
    eLpNorm_mono_real hf hpoint
  have hsum : eLpNorm (fun ω => a + Y ω) p μ ≤
      ENNReal.ofReal a + ENNReal.ofReal ((q * 3 ^ q * Real.Gamma q) ^ (1 / q)) := by
    calc
      eLpNorm (fun ω => a + Y ω) p μ ≤ eLpNorm (fun _ : Disorder => a) p μ + eLpNorm Y p μ := by
        change eLpNorm ((fun _ : Disorder => a) + Y) p μ ≤ _
        exact eLpNorm_add_le hp
      _ ≤ ENNReal.ofReal a + ENNReal.ofReal ((q * 3 ^ q * Real.Gamma q) ^ (1 / q)) := by
        apply add_le_add
        · rw [eLpNorm_const' a (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)) hp_top]
          simp [Real.enorm_eq_ofReal ha]
        · exact hYlp
  calc
    eLpNorm f p μ ≤ eLpNorm (fun ω => a + Y ω) p μ := hmajor
    _ ≤ ENNReal.ofReal a + ENNReal.ofReal ((q * 3 ^ q * Real.Gamma q) ^ (1 / q)) := hsum
    _ = ENNReal.ofReal (3 * Real.log B + (q * 3 ^ q * Real.Gamma q) ^ (1 / q)) := by
      rw [← ENNReal.ofReal_add ha (by positivity)]

/-- The endpoint and smoothed-endpoint log partition functions have finite positive moments bounded by a power of the double logarithm of the smoothing scale. -/
theorem logTails_origin_of (hT : LogProfileTailBound) (A : ℝ) :
    ∀ p : ENNReal, 1 ≤ p → p ≠ ⊤ → ∃ C δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₁ →
      ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A,
        eLpNorm (fun ω => Real.log (profileP2Fun (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) N
            (endpointDist (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) 0 ω) (fun _ => 1) ω)) p
            disorderLaw ≤ ENNReal.ofReal (C * Real.log |Real.log δ|) ∧
        eLpNorm (fun ω => Real.log (profileP2Fun (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) N
            (smoothedEndpointDist (criticalBeta ϑ N) (evenCeil (δ * N)) (evenCeil (Real.sqrt δ * N)) 0 ω)
            (fun _ => 1) ω)) p disorderLaw ≤ ENNReal.ofReal (C * Real.log |Real.log δ|) := by
  intro p hp hp_top
  obtain ⟨δT, Ctail, hδTpos, hTails⟩ := hT A
  let D : ℝ := max Ctail 1
  have hD : 1 ≤ D := le_max_right _ _
  have hDpos : 0 < D := by linarith
  let Kp : ℝ := (p.toReal * 3 ^ p.toReal * Real.Gamma p.toReal) ^ (1 / p.toReal)
  let C : ℝ := 3 * Real.log D + Kp + 4
  let δ₁ : ℝ := min δT (Real.exp (-Real.exp 2))
  refine ⟨C, δ₁, lt_min hδTpos (Real.exp_pos _), ?_⟩
  intro δ hδ hδsmall
  have hδT : δ < δT := lt_of_lt_of_le hδsmall (min_le_left _ _)
  have hδexp : δ < Real.exp (-Real.exp 2) := lt_of_lt_of_le hδsmall (min_le_right _ _)
  have hlogδ : Real.log δ < -Real.exp 2 := (Real.log_lt_iff_lt_exp hδ).2 hδexp
  let L : ℝ := |Real.log δ|
  have hL : Real.exp 2 < L := by
    dsimp [L]
    have hExp2pos : 0 < Real.exp 2 := Real.exp_pos _
    have hlogδneg : Real.log δ < 0 := lt_of_lt_of_le hlogδ (by linarith)
    rw [abs_of_neg hlogδneg]
    linarith
  have hexp2 : 1 < Real.exp 2 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 2)
  have hLge : 1 ≤ L := (hexp2.trans hL).le
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hLge
  have hlogL : 1 ≤ Real.log L := by
    have hExp1 : Real.exp 1 < L := by
      exact (Real.exp_lt_exp.mpr (by norm_num : (1 : ℝ) < 2)).trans hL
    have hlog : 1 < Real.log L := (Real.lt_log_iff_exp_lt hLpos).2 hExp1
    exact hlog.le
  have hsqrtL : Real.sqrt L ≤ L := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
    have hsqrtsq : (Real.sqrt L) ^ 2 = L := Real.sq_sqrt hLpos.le
    nlinarith [sq_nonneg (Real.sqrt L - 1)]
  have hCtail : Ctail ≤ D := le_max_left _ _
  have hB : 1 ≤ D * L := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hD) (sub_nonneg.mpr hLge)]
  have htailN := hTails δ hδ hδT
  filter_upwards [htailN] with N hN
  intro ϑ hϑ
  have htails := hN ϑ hϑ
  let β := criticalBeta ϑ N
  let m := evenCeil (Real.sqrt δ * N)
  let m₀ := evenCeil (δ * N)
  let f₁ : Disorder → ℝ := fun ω => Real.log
    (profileP2Fun β m N (endpointDist β m 0 ω) (fun _ => 1) ω)
  let f₂ : Disorder → ℝ := fun ω => Real.log
    (profileP2Fun β m N (smoothedEndpointDist β m₀ m 0 ω) (fun _ => 1) ω)
  have hf₁ : AEStronglyMeasurable f₁ disorderLaw := by
    have hν : ∀ z : Site, Measurable (fun ω : Disorder => endpointDist β m 0 ω z) := by
      intro z
      exact measurable_endpointDist β m 0 z
    have hm : Measurable f₁ := by
      dsimp [f₁]
      exact (measurable_profileP2Fun_param β m N (fun _ => 1) hν measurable_id).log
    exact hm.aestronglyMeasurable
  have hf₂ : AEStronglyMeasurable f₂ disorderLaw := by
    have hν : ∀ z : Site, Measurable (fun ω : Disorder => smoothedEndpointDist β m₀ m 0 ω z) := by
      intro z
      exact measurable_smoothedEndpointDist β m₀ m 0 z
    have hm : Measurable f₂ := by
      dsimp [f₂]
      exact (measurable_profileP2Fun_param β m N (fun _ => 1) hν measurable_id).log
    exact hm.aestronglyMeasurable
  have htail₁ : ∀ u : ℝ, 0 ≤ u →
      (disorderLaw {ω | u < |f₁ ω|}).toReal ≤ (D * L) * Real.exp (-u / 3) := by
    intro u hu
    have htail := (htails u hu).1
    calc
      (disorderLaw {ω | u < |f₁ ω|}).toReal ≤
          Ctail * Real.sqrt L * Real.exp (-u / 3) := by
            simpa [f₁, L, β, m] using htail
      _ ≤ (D * L) * Real.exp (-u / 3) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
            calc
              Ctail * Real.sqrt L ≤ D * Real.sqrt L :=
                mul_le_mul_of_nonneg_right hCtail (Real.sqrt_nonneg _)
              _ ≤ D * L := mul_le_mul_of_nonneg_left hsqrtL hDpos.le
  have htail₂ : ∀ u : ℝ, 0 ≤ u →
      (disorderLaw {ω | u < |f₂ ω|}).toReal ≤ (D * L) * Real.exp (-u / 3) := by
    intro u hu
    have htail := (htails u hu).2
    calc
      (disorderLaw {ω | u < |f₂ ω|}).toReal ≤
          Ctail * Real.sqrt L * Real.exp (-u / 3) := by
            simpa [f₂, L, β, m, m₀] using htail
      _ ≤ (D * L) * Real.exp (-u / 3) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
            calc
              Ctail * Real.sqrt L ≤ D * Real.sqrt L :=
                mul_le_mul_of_nonneg_right hCtail (Real.sqrt_nonneg _)
              _ ≤ D * L := mul_le_mul_of_nonneg_left hsqrtL hDpos.le
  have hLp₁ : eLpNorm f₁ p disorderLaw ≤
      ENNReal.ofReal (3 * Real.log (D * L) + Kp) := by
    simpa [Kp] using eLpNorm_le_of_exp_tail hf₁ hp hp_top hB htail₁
  have hLp₂ : eLpNorm f₂ p disorderLaw ≤
      ENNReal.ofReal (3 * Real.log (D * L) + Kp) := by
    simpa [Kp] using eLpNorm_le_of_exp_tail hf₂ hp hp_top hB htail₂
  have hlogmul : Real.log (D * L) = Real.log D + Real.log L :=
    Real.log_mul (ne_of_gt hDpos) (ne_of_gt hLpos)
  have hcoef : 0 ≤ 3 * Real.log D + Kp := by
    have hGamma : 0 < Real.Gamma p.toReal :=
      Real.Gamma_pos_of_pos (ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)) hp_top)
    have hpPos : 0 < p.toReal :=
      ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)) hp_top
    have hpow : 0 < (3 : ℝ) ^ p.toReal := Real.rpow_pos_of_pos (by norm_num) _
    have hbase : 0 < p.toReal * 3 ^ p.toReal * Real.Gamma p.toReal :=
      mul_pos (mul_pos hpPos hpow) hGamma
    have hKp : 0 ≤ Kp := by
      dsimp [Kp]
      exact Real.rpow_nonneg hbase.le _
    exact add_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg hD)) hKp
  have hrealbound : 3 * Real.log (D * L) + Kp ≤ C * Real.log L := by
    rw [hlogmul]
    dsimp [C]
    nlinarith [mul_nonneg hcoef (sub_nonneg.mpr hlogL)]
  have hbound₁ : eLpNorm f₁ p disorderLaw ≤ ENNReal.ofReal (C * Real.log L) :=
    hLp₁.trans (ENNReal.ofReal_le_ofReal hrealbound)
  have hbound₂ : eLpNorm f₂ p disorderLaw ≤ ENNReal.ofReal (C * Real.log L) :=
    hLp₂.trans (ENNReal.ofReal_le_ofReal hrealbound)
  exact ⟨by simpa [f₁, β, m, L] using hbound₁, by simpa [f₂, β, m, m₀, L] using hbound₂⟩

end Critical2DKPZ.FutureProfiles

end
