/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! # Interpolation from a small second moment -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal
open scoped Topology

namespace Critical2DKPZ.JointConvergence

private theorem tendsto_rpow_log_product {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    Tendsto (fun x : ℝ => x ^ (-(α / 40)) * (1 + Real.log (1 + x)) ^ β)
      atTop (𝓝 0) := by
  let s : ℝ := α / 80
  have hs : 0 < s := by dsimp [s]; positivity
  have hshift : Tendsto (fun x : ℝ => 1 + x) atTop atTop := by
    apply tendsto_atTop_mono (f := fun x : ℝ => x) (g := fun x => 1 + x)
    · intro x
      linarith
    · exact tendsto_id
  have hsmall : (fun x : ℝ => Real.log (1 + x) ^ β) =o[atTop]
      fun x => (1 + x) ^ s := by
    simpa [Function.comp_def] using
      (isLittleO_log_rpow_rpow_atTop β hs).comp_tendsto hshift
  have hlog : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log (1 + x) := by
    exact (Real.tendsto_log_atTop.comp hshift).eventually_ge_atTop 1
  have hx : ∀ᶠ x : ℝ in atTop, 1 ≤ x := eventually_ge_atTop 1
  have hbound : ∀ᶠ x : ℝ in atTop,
      x ^ (-(α / 40)) * (1 + Real.log (1 + x)) ^ β ≤
        (2 ^ β * 2 ^ s) * x ^ (-(α / 80)) := by
    filter_upwards [hsmall.eventuallyLE, hlog, hx] with x hsmallx hlogx hxx
    have hlognonneg : 0 ≤ Real.log (1 + x) := by linarith
    have hxarg : 0 ≤ 1 + x := by linarith
    have hsmallpow : Real.log (1 + x) ^ β ≤ (1 + x) ^ s := by
      simpa only [Real.norm_of_nonneg (Real.rpow_nonneg hlognonneg β),
        Real.norm_of_nonneg (Real.rpow_nonneg hxarg s)] using hsmallx
    have hlogfactor : (1 + Real.log (1 + x)) ^ β ≤ 2 ^ β * (1 + x) ^ s := by
      calc
        _ ≤ (2 * Real.log (1 + x)) ^ β := by
          apply Real.rpow_le_rpow (by positivity) _ hβ.le
          nlinarith
        _ = 2 ^ β * Real.log (1 + x) ^ β := by
          rw [Real.mul_rpow (by norm_num) hlognonneg]
        _ ≤ 2 ^ β * (1 + x) ^ s :=
          mul_le_mul_of_nonneg_left hsmallpow (Real.rpow_nonneg (by norm_num) β)
    have harg : (1 + x) ^ s ≤ (2 * x) ^ s := by
      apply Real.rpow_le_rpow (by linarith) _ hs.le
      nlinarith
    have harg' : (2 * x) ^ s = 2 ^ s * x ^ s := by
      rw [Real.mul_rpow (by norm_num) (by linarith)]
    have hnonneg : 0 ≤ x ^ (-(α / 40)) := Real.rpow_nonneg (by linarith) _
    calc
      _ ≤ x ^ (-(α / 40)) * (2 ^ β * (2 ^ s * x ^ s)) :=
        mul_le_mul_of_nonneg_left
          (hlogfactor.trans (by
            calc
              2 ^ β * (1 + x) ^ s ≤ 2 ^ β * (2 * x) ^ s :=
                mul_le_mul_of_nonneg_left harg (by positivity)
              _ = 2 ^ β * (2 ^ s * x ^ s) := by rw [harg'])) hnonneg
      _ = (2 ^ β * 2 ^ s) * (x ^ (-(α / 40)) * x ^ s) := by ring
      _ = (2 ^ β * 2 ^ s) * x ^ (-(α / 80)) := by
        rw [← Real.rpow_add (by linarith : 0 < x)]
        congr 1
        dsimp [s]
        ring_nf
  have hupper : Tendsto (fun x : ℝ => (2 ^ β * 2 ^ s) * x ^ (-(α / 80)))
      atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (y := α / 80) (by positivity)).const_mul
      (2 ^ β * 2 ^ s)
  have hlower : ∀ᶠ x : ℝ in atTop,
      0 ≤ x ^ (-(α / 40)) * (1 + Real.log (1 + x)) ^ β := by
    filter_upwards [hlog, hx] with x hlogx hxx
    exact mul_nonneg (Real.rpow_nonneg (by linarith) _)
      (Real.rpow_nonneg (by linarith) _)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper hlower hbound

private theorem eLpNorm_interpolate_two_to_two_mul_measurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {p : ℝ} (hp : 2 < p) (f : Ω → ℝ)
    (hf : AEStronglyMeasurable f P) :
    eLpNorm f (ENNReal.ofReal p) P ≤
      eLpNorm f 2 P ^ (1 / (p - 1)) *
        eLpNorm f (ENNReal.ofReal (2 * p)) P ^ ((p - 2) / (p - 1)) := by
  let a : ℝ := p / (p - 1)
  let b : ℝ := p * (p - 2) / (p - 1)
  let q : ℝ := 2 / a
  let r : ℝ := 2 * p / b
  have hp1 : 1 < p := by linarith
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hq : 1 < q := by
    dsimp [q, a]
    rw [lt_div_iff₀ (by positivity : 0 < p / (p - 1))]
    norm_num
    change p / (p - 1) < 2
    rw [div_lt_iff₀ (by linarith : 0 < p - 1)]
    linarith
  have hr : 0 < r := by dsimp [r]; positivity
  have hq' : q = 2 * (p - 1) / p := by
    dsimp [q, a]
    field_simp [ne_of_gt (by linarith : 0 < p - 1), ne_of_gt (by linarith : 0 < p)]
  have hr' : r = 2 * (p - 1) / (p - 2) := by
    dsimp [r, b]
    field_simp [ne_of_gt (by linarith : 0 < p - 1), ne_of_gt (by linarith : 0 < p - 2)]
  have hpqr : 1 = 1 / q + 1 / r := by
    rw [hq', hr']
    field_simp [ne_of_gt (by linarith : 0 < p - 1), ne_of_gt (by linarith : 0 < p),
      ne_of_gt (by linarith : 0 < p - 2)]
    ring
  have hqa : a * q = 2 := by
    rw [hq']
    dsimp [a]
    field_simp [ne_of_gt (by linarith : 0 < p - 1), ne_of_gt (by linarith : 0 < p)]
  have hrb : b * r = 2 * p := by
    rw [hr']
    dsimp [b]
    field_simp [ne_of_gt (by linarith : 0 < p - 1), ne_of_gt (by linarith : 0 < p - 2)]
  have hab : a + b = p := by
    dsimp [a, b]
    field_simp [ne_of_gt (by linarith : 0 < p - 1)]
    ring
  let F : Ω → ℝ≥0∞ := fun ω => ‖f ω‖ₑ ^ a
  let G : Ω → ℝ≥0∞ := fun ω => ‖f ω‖ₑ ^ b
  have hF : AEMeasurable F P := by
    dsimp [F]
    exact ((ENNReal.continuous_rpow_const (y := a)).comp_aestronglyMeasurable
      hf.enorm.aestronglyMeasurable).aemeasurable
  have hG : AEMeasurable G P := by
    dsimp [G]
    exact ((ENNReal.continuous_rpow_const (y := b)).comp_aestronglyMeasurable
      hf.enorm.aestronglyMeasurable).aemeasurable
  have hpqr' : 1 / (1 : ℝ) = 1 / q + 1 / r := by simpa using hpqr
  have hHolder := ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr
    (p := 1) (q := q) (r := r) (by norm_num) hq hpqr' P hF hG
  have hHolder₀ : ∫⁻ ω, F ω * G ω ∂P ≤
      (∫⁻ ω, F ω ^ q ∂P) ^ (1 / q) * (∫⁻ ω, G ω ^ r ∂P) ^ (1 / r) := by
    simpa using hHolder
  have hFG (ω : Ω) : (F ω * G ω) ^ (1 : ℝ) = ‖f ω‖ₑ ^ p := by
    rw [ENNReal.rpow_one]
    change (‖f ω‖ₑ ^ a) * (‖f ω‖ₑ ^ b) = ‖f ω‖ₑ ^ p
    rw [← ENNReal.rpow_add_of_nonneg _ _ ha.le hb.le]
    rw [hab]
  have hFq (ω : Ω) : F ω ^ q = ‖f ω‖ₑ ^ (2 : ℝ) := by
    dsimp [F]
    rw [← ENNReal.rpow_mul]
    rw [hqa]
  have hGr (ω : Ω) : G ω ^ r = ‖f ω‖ₑ ^ (2 * p) := by
    dsimp [G]
    rw [← ENNReal.rpow_mul]
    rw [hrb]
  have hHolder' :
      ∫⁻ ω, ‖f ω‖ₑ ^ p ∂P ≤
        (∫⁻ ω, ‖f ω‖ₑ ^ (2 : ℝ) ∂P) ^ (1 / q) *
          (∫⁻ ω, ‖f ω‖ₑ ^ (2 * p) ∂P) ^ (1 / r) := by
    calc
      _ = ∫⁻ ω, (F ω * G ω) ^ (1 : ℝ) ∂P := by
        apply lintegral_congr
        intro ω
        exact (hFG ω).symm
      _ ≤ (∫⁻ ω, F ω ^ q ∂P) ^ (1 / q) *
          (∫⁻ ω, G ω ^ r ∂P) ^ (1 / r) := by
            simpa only [ENNReal.rpow_one] using hHolder₀
      _ = _ := by
        rw [lintegral_congr hFq, lintegral_congr hGr]
  have hpENN : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr (by linarith : 0 < p)).ne'
  have htopENN : ENNReal.ofReal p ≠ ⊤ := by simp
  have h2formula : eLpNorm f 2 P =
      (∫⁻ ω, ‖f ω‖ₑ ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) := by
    exact eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2 : ℝ≥0∞))
      (f := f) (μ := P) (by norm_num) (by norm_num) hf
  have hp0 : 0 < p := by linarith
  have hpformula : eLpNorm f (ENNReal.ofReal p) P =
      (∫⁻ ω, ‖f ω‖ₑ ^ p ∂P) ^ (1 / p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpENN htopENN hf]
    simp only [ENNReal.toReal_ofReal hp0.le]
  have h2pENN : ENNReal.ofReal (2 * p) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have h2pTop : ENNReal.ofReal (2 * p) ≠ ⊤ := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact ENNReal.mul_ne_top (by simp) (by simp)
  have h2pformula : eLpNorm f (ENNReal.ofReal (2 * p)) P =
      (∫⁻ ω, ‖f ω‖ₑ ^ (2 * p) ∂P) ^ (1 / (2 * p)) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := ENNReal.ofReal (2 * p))
      h2pENN h2pTop hf]
    simp only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * p)]
  have hroot := ENNReal.rpow_le_rpow hHolder' (by positivity : 0 ≤ 1 / p)
  calc
    eLpNorm f (ENNReal.ofReal p) P =
        (∫⁻ ω, ‖f ω‖ₑ ^ p ∂P) ^ (1 / p) := hpformula
    _ ≤ ((∫⁻ ω, ‖f ω‖ₑ ^ (2 : ℝ) ∂P) ^ (1 / q) *
        (∫⁻ ω, ‖f ω‖ₑ ^ (2 * p) ∂P) ^ (1 / r)) ^ (1 / p) := hroot
    _ = (∫⁻ ω, ‖f ω‖ₑ ^ (2 : ℝ) ∂P) ^ (1 / (q * p)) *
        (∫⁻ ω, ‖f ω‖ₑ ^ (2 * p) ∂P) ^ (1 / (r * p)) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ 1 / p)]
          rw [← ENNReal.rpow_mul]
          rw [← ENNReal.rpow_mul]
          rw [show (1 / q) * (1 / p) = 1 / (q * p) by field_simp,
            show (1 / r) * (1 / p) = 1 / (r * p) by field_simp]
    _ = eLpNorm f 2 P ^ (1 / (p - 1)) *
        eLpNorm f (ENNReal.ofReal (2 * p)) P ^ ((p - 2) / (p - 1)) := by
          rw [h2formula, h2pformula]
          rw [← ENNReal.rpow_mul]
          rw [← ENNReal.rpow_mul]
          rw [show 1 / (q * p) = (1 / 2) * (1 / (p - 1) : ℝ) by
                rw [hq']
                field_simp [ne_of_gt (by linarith : 0 < p - 1), ne_of_gt (by linarith : 0 < p)],
            show 1 / (r * p) = (1 / (2 * p)) * ((p - 2) / (p - 1)) by
                rw [hr']
                field_simp [ne_of_gt (by linarith : 0 < p - 1), ne_of_gt (by linarith : 0 < p - 2),
                  ne_of_gt (by linarith : 0 < p)]]

/-- For `p > 2`, `‖f‖_p ≤ ‖f‖₂^(1/(p-1)) * ‖f‖_{2p}^((p-2)/(p-1))`. -/
theorem eLpNorm_interpolate_two_to_two_mul {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {p : ℝ} (hp : 2 < p) (f : Ω → ℝ) :
    eLpNorm f (ENNReal.ofReal p) P ≤
      eLpNorm f 2 P ^ (1 / (p - 1)) *
        eLpNorm f (ENNReal.ofReal (2 * p)) P ^ ((p - 2) / (p - 1)) := by
  let α : ℝ := 1 / (p - 1)
  let β : ℝ := (p - 2) / (p - 1)
  by_cases hf : AEStronglyMeasurable f P
  · exact eLpNorm_interpolate_two_to_two_mul_measurable P hp f hf
  · rw [eLpNorm_of_not_aestronglyMeasurable hf,
      eLpNorm_of_not_aestronglyMeasurable hf,
      eLpNorm_of_not_aestronglyMeasurable hf]
    have hden : 0 < p - 1 := by linarith
    have hnum : 0 < p - 2 := by linarith
    have hα : 0 < 1 / (p - 1) := div_pos zero_lt_one hden
    have hβ : 0 < (p - 2) / (p - 1) := div_pos hnum hden
    rw [ENNReal.top_rpow_of_pos hα, ENNReal.top_rpow_of_pos hβ]
    simp

/-- An `L²` rate dominates the logarithmic higher-moment growth under interpolation. -/
theorem tendsto_eLpNorm_of_rate_of_log_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℝ → Ω → ℝ) (X : Ω → ℝ)
    {c C : ℝ} (hc : 0 < c)
    (hrate : ∀ δ ∈ Set.Ioo 0 c,
      eLpNorm (fun ω => Y δ ω - X ω) 2 P ≤
        ENNReal.ofReal (C * |Real.log (δ / c)| ^ (-(1 : ℝ) / 40)))
    (hlog : ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ → ∃ Cp : ℝ, ∀ δ ∈ Set.Ioo 0 c,
      eLpNorm (fun ω => Y δ ω - X ω) (2 * p) P ≤
        ENNReal.ofReal (Cp * (1 + Real.log (1 + |Real.log (δ / c)|)))) :
    ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ →
      Tendsto (fun δ => eLpNorm (fun ω => Y δ ω - X ω) p P) (𝓝[>] 0) (𝓝 0) := by
  have hdiv0 : Tendsto (fun δ : ℝ => δ / c) (𝓝[>] 0) (𝓝 0) := by
    have hdivAll : Tendsto (fun δ : ℝ => δ / c) (𝓝 0) (𝓝 0) := by
      have hcont : Continuous fun δ : ℝ => δ / c := by fun_prop
      simpa using (hcont.continuousAt (x := (0 : ℝ))).tendsto
    exact hdivAll.mono_left nhdsWithin_le_nhds
  have hdivPos : Tendsto (fun δ : ℝ => δ / c) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hdiv0, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact div_pos hδ hc
  have hlogAtBot : Tendsto (fun δ : ℝ => Real.log (δ / c)) (𝓝[>] 0) atBot :=
    Real.tendsto_log_nhdsGT_zero.comp hdivPos
  have hlogAbs : Tendsto (fun δ : ℝ => |Real.log (δ / c)|) (𝓝[>] 0) atTop :=
    tendsto_abs_atBot_atTop.comp hlogAtBot
  have hrateReal : Tendsto (fun δ : ℝ => C * |Real.log (δ / c)| ^ (-(1 : ℝ) / 40))
      (𝓝[>] 0) (𝓝 0) := by
    have hpow₀ := (tendsto_rpow_neg_atTop (y := (1 : ℝ) / 40) (by norm_num)).comp hlogAbs
    have hpow : Tendsto (fun δ : ℝ => |Real.log (δ / c)| ^ (-(1 / 40 : ℝ)))
        (𝓝[>] 0) (𝓝 0) := by
      simpa [Function.comp_def] using hpow₀
    simpa [neg_div, mul_zero] using hpow.const_mul C
  have hrateENN : Tendsto
      (fun δ : ℝ => ENNReal.ofReal (C * |Real.log (δ / c)| ^ (-(1 : ℝ) / 40)))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hrateReal
  intro p hp hptop
  by_cases hp2 : p ≤ 2
  · have hbound : ∀ᶠ δ : ℝ in 𝓝[>] 0,
        eLpNorm (fun ω => Y δ ω - X ω) p P ≤
          ENNReal.ofReal (C * |Real.log (δ / c)| ^ (-(1 : ℝ) / 40)) := by
      filter_upwards [Ioo_mem_nhdsGT hc] with δ hδ
      exact (eLpNorm_le_eLpNorm_of_exponent_le hp2).trans (hrate δ hδ)
    apply ENNReal.tendsto_nhds_zero.mpr
    intro ε hε
    filter_upwards [hbound, hrateENN.eventually (Iic_mem_nhds hε)] with δ hδ hε'
    exact hδ.trans hε'
  · have hp2' : 2 < p := lt_of_not_ge hp2
    have hpReal : 2 < p.toReal :=
      (ENNReal.toReal_lt_toReal (by simp) hptop).2 hp2'
    have hOfp : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal hptop
    have hOf2p : ENNReal.ofReal (2 * p.toReal) = 2 * p := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      simp [hOfp]
    obtain ⟨Cp, hCp⟩ := hlog p hp hptop
    let C₀ : ℝ := max C 0
    let Cp₀ : ℝ := max Cp 0
    have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
    have hCp₀ : 0 ≤ Cp₀ := by dsimp [Cp₀]; positivity
    let α : ℝ := 1 / (p.toReal - 1)
    let β : ℝ := (p.toReal - 2) / (p.toReal - 1)
    have hα : 0 < α := by
      dsimp [α]
      exact div_pos zero_lt_one (by linarith)
    have hβ : 0 < β := by
      dsimp [β]
      exact div_pos (by linarith) (by linarith)
    have hRateReal : Tendsto
        (fun δ : ℝ =>
          (C₀ * |Real.log (δ / c)| ^ (-(1 : ℝ) / 40)) ^ α *
            (Cp₀ * (1 + Real.log (1 + |Real.log (δ / c)|))) ^ β)
        (𝓝[>] 0) (𝓝 0) := by
      have hRateX := tendsto_rpow_log_product hα hβ
      have hRateX' := hRateX.const_mul (C₀ ^ α * Cp₀ ^ β)
      have hAeq (x : ℝ) (hx : 1 ≤ x) :
          (C₀ * x ^ (-(1 : ℝ) / 40)) ^ α = C₀ ^ α * x ^ (-(α / 40)) := by
        rw [Real.mul_rpow hC₀ (Real.rpow_nonneg (by linarith) _)]
        rw [← Real.rpow_mul (by linarith : 0 ≤ x)]
        congr 1
        ring_nf
      have hBeq (x : ℝ) (hx : 1 ≤ x) :
          (Cp₀ * (1 + Real.log (1 + x))) ^ β =
            Cp₀ ^ β * (1 + Real.log (1 + x)) ^ β := by
        have hD : 0 ≤ 1 + Real.log (1 + x) := by
          have : 1 ≤ 1 + x := by linarith
          exact add_nonneg (by norm_num) (Real.log_nonneg this)
        exact Real.mul_rpow hCp₀ hD
      have heq : (fun x : ℝ =>
          (C₀ * x ^ (-(1 : ℝ) / 40)) ^ α * (Cp₀ * (1 + Real.log (1 + x))) ^ β) =ᶠ[atTop]
          fun x => (C₀ ^ α * Cp₀ ^ β) *
            (x ^ (-(α / 40)) * (1 + Real.log (1 + x)) ^ β) := by
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
        rw [hAeq x hx, hBeq x hx]
        ring
      have hRateXlog := hRateX'.comp hlogAbs
      simpa [Function.comp_def, mul_zero] using
        Tendsto.congr' (heq.comp_tendsto hlogAbs).symm hRateXlog
    have hRateENN : Tendsto
        (fun δ : ℝ => ENNReal.ofReal
          ((C₀ * |Real.log (δ / c)| ^ (-(1 : ℝ) / 40)) ^ α *
            (Cp₀ * (1 + Real.log (1 + |Real.log (δ / c)|))) ^ β))
        (𝓝[>] 0) (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal hRateReal
    have hbound : ∀ᶠ δ : ℝ in 𝓝[>] 0,
        eLpNorm (fun ω => Y δ ω - X ω) p P ≤ ENNReal.ofReal
          ((C₀ * |Real.log (δ / c)| ^ (-(1 : ℝ) / 40)) ^ α *
            (Cp₀ * (1 + Real.log (1 + |Real.log (δ / c)|))) ^ β) := by
      filter_upwards [Ioo_mem_nhdsGT hc,
        hlogAbs.eventually (eventually_ge_atTop (1 : ℝ))] with δ hδ hL
      let L : ℝ := |Real.log (δ / c)|
      have hLnonneg : 0 ≤ L := abs_nonneg _
      have hLpow : 0 ≤ L ^ (-(1 : ℝ) / 40) := Real.rpow_nonneg hLnonneg _
      have hDnonneg : 0 ≤ 1 + Real.log (1 + L) := by
        have : 1 ≤ 1 + L := by dsimp [L]; linarith
        have hlogD : 0 ≤ Real.log (1 + L) := Real.log_nonneg this
        linarith
      have h2 : eLpNorm (fun ω => Y δ ω - X ω) 2 P ≤
          ENNReal.ofReal (C₀ * L ^ (-(1 : ℝ) / 40)) := by
        refine (hrate δ hδ).trans ?_
        exact ENNReal.ofReal_le_ofReal <| mul_le_mul_of_nonneg_right
          (le_max_left C 0) hLpow
      have hhigh : eLpNorm (fun ω => Y δ ω - X ω) (2 * p) P ≤
          ENNReal.ofReal (Cp₀ * (1 + Real.log (1 + L))) := by
        refine (hCp δ hδ).trans ?_
        exact ENNReal.ofReal_le_ofReal <| mul_le_mul_of_nonneg_right
          (le_max_left Cp 0) hDnonneg
      have hinterp := eLpNorm_interpolate_two_to_two_mul P hpReal
        (fun ω => Y δ ω - X ω)
      rw [hOfp, hOf2p] at hinterp
      have h2pow := ENNReal.rpow_le_rpow h2 hα.le
      have hhighpow := ENNReal.rpow_le_rpow hhigh hβ.le
      have hA : 0 ≤ C₀ * L ^ (-(1 : ℝ) / 40) := mul_nonneg hC₀ hLpow
      have hB : 0 ≤ Cp₀ * (1 + Real.log (1 + L)) := mul_nonneg hCp₀ hDnonneg
      have hpoint : eLpNorm (fun ω => Y δ ω - X ω) p P ≤ ENNReal.ofReal
          ((C₀ * L ^ (-(1 : ℝ) / 40)) ^ α *
            (Cp₀ * (1 + Real.log (1 + L))) ^ β) := by
       calc
        eLpNorm (fun ω => Y δ ω - X ω) p P ≤
            eLpNorm (fun ω => Y δ ω - X ω) 2 P ^ α *
              eLpNorm (fun ω => Y δ ω - X ω) (2 * p) P ^ β := hinterp
        _ ≤ ENNReal.ofReal (C₀ * L ^ (-(1 : ℝ) / 40)) ^ α *
              ENNReal.ofReal (Cp₀ * (1 + Real.log (1 + L))) ^ β :=
            mul_le_mul h2pow hhighpow (by positivity) (by positivity)
        _ = ENNReal.ofReal
              ((C₀ * L ^ (-(1 : ℝ) / 40)) ^ α *
                (Cp₀ * (1 + Real.log (1 + L))) ^ β) := by
            rw [ENNReal.ofReal_rpow_of_nonneg hA hα.le,
              ENNReal.ofReal_rpow_of_nonneg hB hβ.le]
            rw [← ENNReal.ofReal_mul (by positivity)]
      simpa [L, α, β] using hpoint
    apply ENNReal.tendsto_nhds_zero.mpr
    intro ε hε
    filter_upwards [hbound, hRateENN.eventually (Iic_mem_nhds hε)] with δ hδ hε'
    exact hδ.trans hε'

end Critical2DKPZ.JointConvergence

end
