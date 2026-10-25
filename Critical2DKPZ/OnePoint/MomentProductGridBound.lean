/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.OnePoint.MomentProductSecondMomentProduct
public import Critical2DKPZ.OnePoint.BlockMomentAndTiltedRatioBounds
public import Critical2DKPZ.OnePoint.BlockRatioIntegralExpansion
public import Critical2DKPZ.Blocks.GridAlignment
import Critical2DKPZ.OnePoint.MomentProductTiltedIdentity
import Critical2DKPZ.OnePoint.MomentProductIntegralBounds
import Critical2DKPZ.OnePoint.MomentProductInverseProduct
import Critical2DKPZ.OnePoint.FiniteProfileGaussian
import Critical2DKPZ.MomentBounds.BlockClockBounds
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic

/-! # Grid comparison for the long second and inverse moments -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace Critical2DKPZ.OnePoint

open Critical2DKPZ.Blocks

private noncomputable def normalizedBlockTilt (W : Disorder → ℝ) (Z : ℝ) : Measure Disorder :=
  disorderLaw.withDensity (fun ω => ENNReal.ofReal (W ω / Z))

private theorem isProbabilityMeasure_normalizedBlockTilt (W : Disorder → ℝ) (Z : ℝ)
    (hW : Integrable W disorderLaw) (hWnonneg : ∀ ω, 0 ≤ W ω)
    (hZ : Z = ∫ ω, W ω ∂disorderLaw) (hZpos : 0 < Z) :
    IsProbabilityMeasure (normalizedBlockTilt W Z) := by
  constructor
  have hdiv : Integrable (fun ω => W ω / Z) disorderLaw := hW.div_const Z
  have hdivnonneg : ∀ ω, 0 ≤ W ω / Z := fun ω => div_nonneg (hWnonneg ω) hZpos.le
  rw [normalizedBlockTilt, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hdiv (Filter.Eventually.of_forall hdivnonneg)]
  have hint : (∫ ω, W ω / Z ∂disorderLaw) = 1 := by
    rw [integral_div]
    calc
      (∫ ω, W ω ∂disorderLaw) / Z = Z / Z := by rw [hZ]
      _ = 1 := div_self hZpos.ne'
  rw [hint]
  norm_num

private theorem integral_normalizedBlockTilt (W : Disorder → ℝ) (Z : ℝ)
    (hWmeas : Measurable W) (hWnonneg : ∀ ω, 0 ≤ W ω) (hZpos : 0 < Z)
    (f : Disorder → ℝ) :
    ∫ ω, f ω ∂normalizedBlockTilt W Z =
      (∫ ω, W ω * f ω ∂disorderLaw) / Z := by
  have hDensity : Measurable (fun ω => ENNReal.ofReal (W ω / Z)) :=
    (hWmeas.div_const Z).ennreal_ofReal
  rw [normalizedBlockTilt,
    integral_withDensity_eq_integral_toReal_smul hDensity
      (Filter.Eventually.of_forall fun ω => ENNReal.ofReal_lt_top) f]
  simp_rw [ENNReal.toReal_ofReal (div_nonneg (hWnonneg _) hZpos.le), smul_eq_mul]
  have hfun : (fun ω => W ω / Z * f ω) = fun ω => (W ω * f ω) / Z := by
    funext ω
    ring
  rw [hfun, integral_div]

private theorem setIntegral_normalizedBlockTilt (W : Disorder → ℝ) (Z : ℝ)
    (hWmeas : Measurable W) (hWnonneg : ∀ ω, 0 ≤ W ω) (hZpos : 0 < Z)
    {G : Set Disorder} (hG : MeasurableSet G) (f : Disorder → ℝ) :
    ∫ ω in G, f ω ∂normalizedBlockTilt W Z =
      (∫ ω in G, W ω * f ω ∂disorderLaw) / Z := by
  rw [← integral_indicator hG]
  rw [integral_normalizedBlockTilt W Z hWmeas hWnonneg hZpos]
  have hfun : (fun ω => W ω * G.indicator f ω) = G.indicator (fun ω => W ω * f ω) := by
    funext ω
    by_cases hω : ω ∈ G <;> simp [hω]
  rw [hfun, integral_indicator hG]

private theorem normalizedBlockTilt_compl_real (W : Disorder → ℝ) (Z : ℝ)
    (hWmeas : Measurable W) (hWnonneg : ∀ ω, 0 ≤ W ω) (hZpos : 0 < Z)
    {G : Set Disorder} (hG : MeasurableSet G) :
    (normalizedBlockTilt W Z Gᶜ).toReal =
      (∫ ω in Gᶜ, W ω ∂disorderLaw) / Z := by
  let Q := normalizedBlockTilt W Z
  have hcomp : MeasurableSet Gᶜ := hG.compl
  have hmeasure : (Q Gᶜ).toReal = ∫ ω in Gᶜ, (1 : ℝ) ∂Q := by
    calc
      (Q Gᶜ).toReal = Q.real Gᶜ := rfl
      _ = ∫ ω in Gᶜ, (1 : ℝ) ∂Q := by simp
  calc
    (normalizedBlockTilt W Z Gᶜ).toReal = ∫ ω in Gᶜ, (1 : ℝ) ∂Q := by
      simpa [Q] using hmeasure
    _ = (∫ ω in Gᶜ, W ω * 1 ∂disorderLaw) / Z :=
      setIntegral_normalizedBlockTilt W Z hWmeas hWnonneg hZpos hcomp _
    _ = (∫ ω in Gᶜ, W ω ∂disorderLaw) / Z := by simp

private theorem blockMass_secondMoment_ge_one (β : ℝ) (t : ℕ → ℕ) (i : ℕ) :
    1 ≤ ∫ ω, blockMass β t i ω ^ 2 ∂disorderLaw := by
  have hmem : MemLp (blockMass β t i) 2 disorderLaw := by
    change MemLp (smoothedP2Plane β (t (i - 1)) (t i) 0) 2 disorderLaw
    exact
      Polymer.memLp_smoothedP2Plane β (t (i - 1)) (t i) 0 2 (by norm_num)
  have hv := ProbabilityTheory.variance_nonneg (blockMass β t i) disorderLaw
  rw [ProbabilityTheory.variance_eq_sub hmem] at hv
  have hmean : ∫ ω, blockMass β t i ω ∂disorderLaw = 1 := by
    dsimp [blockMass]
    exact Polymer.integral_smoothedP2Plane β (t (i - 1)) (t i) 0
  rw [hmean] at hv
  norm_num at hv
  linarith

private theorem blockMass_inv_prod_integral_pos (β : ℝ) (t : ℕ → ℕ)
    (ht : Monotone t) {r s : ℕ} (hr : 1 ≤ r) :
    0 < ∫ ω, ∏ i ∈ Finset.Icc r s, (blockMass β t i ω)⁻¹ ∂disorderLaw := by
  rw [integral_prod_inv_blockMass β t ht hr (s := s)]
  have hprod : 1 ≤ ∏ i ∈ Finset.Icc r s,
      ∫ ω, (blockMass β t i ω)⁻¹ ∂disorderLaw := by
    rw [← Finset.prod_const_one]
    apply Finset.prod_le_prod₀
    · intro i hi
      positivity
    · intro i hi
      exact one_le_integral_inv_blockMass β t i
  linarith

private theorem blockInverseProduct_le_on_goodSet (β : ℝ) (t : ℕ → ℕ)
    {r s : ℕ} {ω : Disorder}
    (hω : ω ∈ blockGoodSet β t r s) :
    (∏ i ∈ Finset.Icc r s, (blockMass β t i ω)⁻¹) ≤ 2 ^ (s + 1) := by
  classical
  let S := Finset.Icc r s
  change ∀ i ∈ S, |blockMass β t i ω - 1| ≤ 1 / 2 at hω
  have hcard : S.card ≤ s + 1 := by
    have hsub : S ⊆ Finset.Icc 0 s := by
      intro i hi
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, (Finset.mem_Icc.mp hi).2⟩
    calc
      S.card ≤ (Finset.Icc 0 s).card := Finset.card_le_card hsub
      _ = s + 1 := by simp [Nat.card_Icc]
  have hinv (i : ℕ) (hi : i ∈ S) : (blockMass β t i ω)⁻¹ ≤ 2 := by
    have hgood := hω i hi
    have hpos := blockMass_pos β t i ω
    have hlow : 1 / 2 ≤ blockMass β t i ω := by
      rw [abs_le] at hgood
      linarith
    exact (inv_le_iff_one_le_mul₀' hpos).2 (by nlinarith)
  have hprod : (∏ i ∈ S, (blockMass β t i ω)⁻¹) ≤ ∏ _i ∈ S, (2 : ℝ) := by
    apply Finset.prod_le_prod₀
    · intro i hi
      exact inv_nonneg.mpr (blockMass_pos β t i ω).le
    · intro i hi
      exact hinv i hi
  calc
    (∏ i ∈ Finset.Icc r s, (blockMass β t i ω)⁻¹) ≤ ∏ _i ∈ S, (2 : ℝ) := hprod
    _ = 2 ^ S.card := by simp
    _ ≤ 2 ^ (s + 1) := pow_le_pow_right₀ (by norm_num) hcard

private theorem sqrt_sqrt_eq_rpow_quarter (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (Real.sqrt x) = x ^ ((1 : ℝ) / 4) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  have hpow := Real.rpow_mul hx ((1 : ℝ) / 2) ((1 : ℝ) / 2)
  convert hpow.symm using 1
  norm_num

/-- On the geometric grid, the logarithm of the second-to-reciprocal moment ratio has an inverse fourth-root endpoint-distance bound, assuming the block-moment and tilted-ratio bounds. -/
theorem log_secondMoment_div_inv_moment_grid_le_of (hC6 : BlockMomentsBound)
    (hQ : TiltedRatioBound) (A : ℝ) :
    ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ∀ ρ₁ : ℝ, ∃ C : ℝ, ∃ J₀ : ℕ,
      ∀ ρ ∈ Set.Icc ρ₀ ρ₁, ∀ᶠ N : ℕ in atTop,
        ∀ ϑ ∈ Set.Icc (-A) A, ∀ u b : ℕ, u ≤ b → b + J₀ ≤ blockCount N ρ →
          Real.log ((∫ ω, smoothedP2Plane (criticalBeta ϑ N) (blockTime N ρ u)
              (blockTime N ρ b) 0 ω ^ 2 ∂disorderLaw) /
            ∫ ω, (smoothedP2Plane (criticalBeta ϑ N) (blockTime N ρ u)
              (blockTime N ρ b) 0 ω)⁻¹ ∂disorderLaw) ≤
            C / ((blockCount N ρ : ℝ) - b) ^ ((1 : ℝ) / 4) := by
  obtain ⟨ρ₀, hρ₀, hQρ⟩ := hQ A
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro ρ₁
  obtain ⟨Cq, hq⟩ := hQρ ρ₁
  obtain ⟨C₂, J₂, hJ₂, hsecond⟩ :=
    secondMoment_le_prod_blockSecondMoment A ρ₀ ρ₁ hρ₀
  obtain ⟨Ci, hinverseProduct⟩ := prod_integral_inv_blockMass_ge_of hC6 A ρ₀ ρ₁ hρ₀
  let cq := |Cq|
  let c₂ := |C₂|
  let ci := |Ci|
  let Sq := cq + Real.sqrt cq
  let S := Sq + ci
  let B := 2 * S + 1
  let J₀ : ℕ := max J₂ ⌈B ^ (4 : ℝ)⌉₊
  let C := 2 * (c₂ + S)
  have hcq : 0 ≤ cq := abs_nonneg Cq
  have hc₂ : 0 ≤ c₂ := abs_nonneg C₂
  have hci : 0 ≤ ci := abs_nonneg Ci
  have hSq : 0 ≤ Sq := by dsimp [Sq]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hB : 1 ≤ B := by
    dsimp [B, S, Sq]
    linarith [hcq, hci, Real.sqrt_nonneg cq]
  have hC : 0 ≤ C := by dsimp [C, c₂, S, Sq]; positivity
  have hJ₀ : 1 ≤ J₀ := by
    exact le_trans hJ₂ (Nat.le_max_left _ _)
  have hJpower : (B ^ 4 : ℝ) ≤ (J₀ : ℝ) := by
    have hceilNat : ⌈B ^ (4 : ℝ)⌉₊ ≤ J₀ := by
      dsimp [J₀]
      exact Nat.le_max_right _ _
    have hceil : B ^ (4 : ℝ) ≤ (⌈B ^ (4 : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
    have hcast : (⌈B ^ (4 : ℝ)⌉₊ : ℝ) ≤ (J₀ : ℝ) := by exact_mod_cast hceilNat
    have hpow : B ^ 4 = B ^ (4 : ℝ) := (Real.rpow_natCast B 4).symm
    exact hpow ▸ hceil.trans hcast
  refine ⟨C, J₀, ?_⟩
  intro ρ hρρ
  have hρ : 1 < ρ := lt_of_lt_of_le hρ₀ hρρ.1
  filter_upwards [hsecond ρ hρρ, hinverseProduct ρ hρρ, hq ρ hρρ,
    Critical2DKPZ.Blocks.blockTime_monotone hρ] with N hsecondN hinverseN hqN hclock
  intro ϑ hϑ u b hub hKb
  let K := blockCount N ρ
  let D := (K : ℝ) - b
  have hJnat : J₀ ≤ K - b := by dsimp [K]; omega
  have hJreal : (J₀ : ℝ) ≤ D := by
    dsimp [D]
    have hcast : (J₀ : ℝ) ≤ ((K - b : ℕ) : ℝ) := by exact_mod_cast hJnat
    rw [Nat.cast_sub (by dsimp [K]; omega)] at hcast
    exact hcast
  have hD1 : 1 ≤ D := le_trans (by exact_mod_cast hJ₀) hJreal
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD1
  have hDnn : 0 ≤ D := hDpos.le
  let q := Real.sqrt (Real.sqrt D)
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hqSq : q ^ 2 = Real.sqrt D := by
    dsimp [q]
    exact Real.sq_sqrt (Real.sqrt_nonneg D)
  have hqgeone : 1 ≤ q := by
    have hsqrtD : 1 ≤ Real.sqrt D := Real.one_le_sqrt.mpr hD1
    nlinarith [Real.sqrt_nonneg (Real.sqrt D)]
  have hqleSqrtD : q ≤ Real.sqrt D := by nlinarith [hqSq]
  have hqleone : q ≤ D := by
    have hsqrtDle : Real.sqrt D ≤ D := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨hDnn, ?_⟩
      nlinarith [sq_nonneg (D - 1)]
    exact hqleSqrtD.trans hsqrtDle
  have hBfourth : B ^ 4 ≤ D := by
    calc
      B ^ 4 ≤ (J₀ : ℝ) := hJpower
      _ ≤ D := hJreal
  have hqgeB : B ≤ q := by
    have hrootB : Real.sqrt (Real.sqrt (B ^ 4)) = B := by
      rw [show B ^ 4 = (B ^ 2) ^ 2 by ring, Real.sqrt_sq_eq_abs,
        abs_of_nonneg (sq_nonneg B), Real.sqrt_sq_eq_abs, abs_of_nonneg (by linarith : 0 ≤ B)]
    calc
      B = Real.sqrt (Real.sqrt (B ^ 4)) := hrootB.symm
    _ ≤ Real.sqrt (Real.sqrt D) :=
        Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hBfourth)
  have hqgeS : 2 * S ≤ q := by
    dsimp [B] at hqgeB
    linarith
  have hquarter : q = D ^ ((1 : ℝ) / 4) := by
    simpa [q] using sqrt_sqrt_eq_rpow_quarter D hDnn
  have hqSqFactor : q ^ 2 = Real.sqrt D := hqSq
  have hsqrtDpos : 0 < Real.sqrt D := Real.sqrt_pos.2 hDpos
  by_cases hubEq : u = b
  · subst b
    have hpoint (ω : Disorder) :
        smoothedP2Plane (criticalBeta ϑ N) (blockTime N ρ u) (blockTime N ρ u) 0 ω = 1 :=
      Critical2DKPZ.Blocks.smoothedP2Plane_eq_one_of_eq
        (criticalBeta ϑ N) (blockTime N ρ u) ω
    have hratio :
        (∫ ω, smoothedP2Plane (criticalBeta ϑ N) (blockTime N ρ u)
          (blockTime N ρ u) 0 ω ^ 2 ∂disorderLaw) /
        ∫ ω, (smoothedP2Plane (criticalBeta ϑ N) (blockTime N ρ u)
          (blockTime N ρ u) 0 ω)⁻¹ ∂disorderLaw = 1 := by
      simp [hpoint]
    rw [hratio, Real.log_one]
    exact div_nonneg hC (Real.rpow_nonneg hDnn _)
  · have hublt : u < b := by omega
    let r := u + 1
    let β := criticalBeta ϑ N
    let t := blockTime N ρ
    let R : Disorder → ℝ := blockRatio β t r b
    let W : Disorder → ℝ := fun ω =>
      ∏ i ∈ Finset.Icc r b, (blockMass β t i ω)⁻¹
    let Z := ∫ ω, W ω ∂disorderLaw
    let G := blockGoodSet β t r b
    let density : Disorder → ENNReal := fun ω => ENNReal.ofReal (W ω / Z)
    let Q := normalizedBlockTilt W Z
    have hr : 1 ≤ r := by dsimp [r]; omega
    have hrs : r ≤ b := by dsimp [r]; omega
    have hbplus : b + 1 ≤ K := by dsimp [K]; omega
    have hG : MeasurableSet G := by
      exact measurableSet_blockGoodSet β t r b
    have hWmeas : Measurable W := by
      dsimp [W]
      apply Finset.measurable_prod
      intro i hi
      have hmass : Measurable (blockMass β t i) := by
        change Measurable (smoothedP2Plane β (t (i - 1)) (t i) 0)
        exact Polymer.measurable_smoothedP2Plane β (t (i - 1)) (t i) 0
      exact hmass.inv
    have hWnonneg (ω : Disorder) : 0 ≤ W ω := by
      dsimp [W]
      apply Finset.prod_nonneg
      intro i hi
      exact inv_nonneg.mpr (blockMass_pos β t i ω).le
    have hZpos : 0 < Z := by
      dsimp [Z, W]
      exact blockMass_inv_prod_integral_pos β t hclock hr (s := b)
    have hWint : Integrable W disorderLaw := by
      apply Integrable.of_integral_ne_zero
      simpa [Z] using (ne_of_gt hZpos)
    have hQprob := isProbabilityMeasure_normalizedBlockTilt W Z hWint hWnonneg rfl hZpos
    have hDensity : Measurable density := by
      dsimp [density]
      exact (hWmeas.div_const Z).ennreal_ofReal
    have hDensityFinite : ∀ᵐ ω ∂disorderLaw, density ω < ⊤ := by
      filter_upwards with ω
      exact ENNReal.ofReal_lt_top
    have hRpos (ω : Disorder) : 0 < R ω := by
      dsimp [R, blockRatio]
      exact div_pos (Polymer.smoothedP2Plane_pos β (t (r - 1)) (t b) 0 ω)
        (Finset.prod_pos fun i hi => blockMass_pos β t i ω)
    have hWbound : ∀ᵐ ω ∂disorderLaw.restrict G, ‖W ω‖ ≤ 2 ^ (b + 1) := by
      filter_upwards [ae_restrict_mem hG] with ω hω
      have hbound := blockInverseProduct_le_on_goodSet β t hω
      rw [Real.norm_eq_abs, abs_of_nonneg (hWnonneg ω)]
      exact hbound
    have hWstrong : AEStronglyMeasurable W (disorderLaw.restrict G) :=
      hWmeas.aestronglyMeasurable.restrict
    have hRatioSqInt : Integrable (fun ω => (R ω - 1) ^ 2)
        (disorderLaw.restrict G) := by
      change IntegrableOn (fun ω => (blockRatio β t r b ω - 1) ^ 2) G disorderLaw
      exact integrableOn_blockRatio_sub_one_sq β hclock hr hrs
    have hWeightedSq : Integrable (fun ω => W ω * (R ω - 1) ^ 2)
        (disorderLaw.restrict G) := hRatioSqInt.bdd_mul hWstrong hWbound
    have hInvLong : Integrable (fun ω =>
        (smoothedP2Plane β (t (r - 1)) (t b) 0 ω)⁻¹) disorderLaw := by
      simpa only [Real.rpow_neg_one] using
        integrable_rpow_smoothedP2Plane β (t (r - 1)) (t b) 0 (-1)
    have hpoint (ω : Disorder) :
        (smoothedP2Plane β (t (r - 1)) (t b) 0 ω)⁻¹ = (R ω)⁻¹ * W ω := by
      have hdecomp := smoothedP2Plane_eq_prod_blockMass_mul_blockRatio β t r b ω
      dsimp [R, W]
      rw [hdecomp, mul_inv, Finset.prod_inv_distrib]
      ring
    have hInvQ : Integrable (fun ω => (R ω)⁻¹) Q := by
      change Integrable (fun ω => (R ω)⁻¹) (disorderLaw.withDensity density)
      rw [integrable_withDensity_iff_integrable_smul' hDensity hDensityFinite]
      change Integrable (fun ω => (density ω).toReal * (R ω)⁻¹) disorderLaw
      have heq : (fun ω => (density ω).toReal * (R ω)⁻¹) = fun ω =>
          ((smoothedP2Plane β (t (r - 1)) (t b) 0 ω)⁻¹) / Z := by
        funext ω
        rw [show (density ω).toReal = W ω / Z by
          dsimp [density]
          rw [ENNReal.toReal_ofReal (div_nonneg (hWnonneg ω) hZpos.le)]]
        rw [hpoint]
        ring
      rw [heq]
      exact hInvLong.div_const Z
    have hSqQ : IntegrableOn (fun ω => (R ω - 1) ^ 2) G Q := by
      change Integrable (fun ω => (R ω - 1) ^ 2) (Q.restrict G)
      change Integrable (fun ω => (R ω - 1) ^ 2)
        ((disorderLaw.withDensity density).restrict G)
      rw [restrict_withDensity hG]
      rw [integrable_withDensity_iff_integrable_smul' hDensity
        (Filter.Eventually.of_forall fun ω => ENNReal.ofReal_lt_top)]
      change Integrable (fun ω => (density ω).toReal * (R ω - 1) ^ 2)
        (disorderLaw.restrict G)
      have heq : (fun ω => (density ω).toReal * (R ω - 1) ^ 2) = fun ω =>
          (W ω * (R ω - 1) ^ 2) / Z := by
        funext ω
        rw [show (density ω).toReal = W ω / Z by
          dsimp [density]
          rw [ENNReal.toReal_ofReal (div_nonneg (hWnonneg ω) hZpos.le)]]
        ring
      rw [heq]
      exact hWeightedSq.div_const Z
    have htilt := @one_sub_le_integral_inv Disorder inferInstance Q hQprob
      (R := R) hRpos (G := G) hG hInvQ hSqQ
    have hbad := normalizedBlockTilt_compl_real W Z hWmeas hWnonneg hZpos hG
    have hgood := setIntegral_normalizedBlockTilt W Z hWmeas hWnonneg hZpos hG
      (fun ω => (R ω - 1) ^ 2)
    have hqData := hqN ϑ hϑ r b hr hrs hbplus
    rcases hqData with ⟨hbadQ, hgoodQ⟩
    have hDreal : (blockCount N ρ : ℝ) - b = D := by rfl
    have hCqbound : Cq ≤ cq := le_abs_self Cq
    have hbadle : (Q Gᶜ).toReal ≤ cq / Real.sqrt D := by
      rw [show Q = normalizedBlockTilt W Z by rfl, hbad]
      rw [hDreal] at hbadQ
      calc
        (∫ ω in Gᶜ, W ω ∂disorderLaw) / Z ≤ Cq / Real.sqrt D := hbadQ
        _ ≤ cq / Real.sqrt D := div_le_div_of_nonneg_right hCqbound hsqrtDpos.le
    have hgoodIntQ : 0 ≤ ∫ ω in G, (R ω - 1) ^ 2 ∂Q :=
      integral_nonneg fun ω => sq_nonneg (R ω - 1)
    have hgoodle : (∫ ω in G, (R ω - 1) ^ 2 ∂Q) ≤ cq / Real.sqrt D := by
      rw [hgood]
      have hcomm : (fun ω => W ω * (R ω - 1) ^ 2) =
          fun ω => (R ω - 1) ^ 2 * W ω := by
        funext ω
        ring
      rw [hcomm]
      rw [hDreal] at hgoodQ
      calc
        (∫ ω in G, (R ω - 1) ^ 2 * W ω ∂disorderLaw) / Z ≤ Cq / Real.sqrt D := hgoodQ
        _ ≤ cq / Real.sqrt D := div_le_div_of_nonneg_right hCqbound hsqrtDpos.le
    have hCqOverSqrt : cq / Real.sqrt D ≤ cq / q := by
      apply (div_le_div_iff₀ hsqrtDpos hqpos).2
      exact mul_le_mul_of_nonneg_left hqleSqrtD hcq
    have hbadle' : (Q Gᶜ).toReal ≤ cq / q := hbadle.trans hCqOverSqrt
    have hrootle : Real.sqrt (∫ ω in G, (R ω - 1) ^ 2 ∂Q) ≤ Real.sqrt cq / q := by
      calc
        Real.sqrt (∫ ω in G, (R ω - 1) ^ 2 ∂Q) ≤ Real.sqrt (cq / Real.sqrt D) :=
          Real.sqrt_le_sqrt hgoodle
        _ = Real.sqrt cq / q := by
          rw [Real.sqrt_div hcq]
    have htilt' : 1 - Sq / q ≤ ∫ ω, (R ω)⁻¹ ∂Q := by
      have hrootRewrite :
          (∫ ω in G, (R ω - 1) ^ 2 ∂Q) ^ ((1 : ℝ) / 2) =
            Real.sqrt (∫ ω in G, (R ω - 1) ^ 2 ∂Q) := by
        rw [← Real.sqrt_eq_rpow]
      rw [hrootRewrite] at htilt
      have hsum : (Q Gᶜ).toReal +
          Real.sqrt (∫ ω in G, (R ω - 1) ^ 2 ∂Q) ≤ Sq / q := by
        dsimp [Sq]
        calc
          (Q Gᶜ).toReal +
              Real.sqrt (∫ ω in G, (R ω - 1) ^ 2 ∂Q) ≤ cq / q + Real.sqrt cq / q :=
            add_le_add hbadle' hrootle
          _ = (cq + Real.sqrt cq) / q := by ring
      calc
        1 - Sq / q ≤ 1 - ((Q Gᶜ).toReal +
            Real.sqrt (∫ ω in G, (R ω - 1) ^ 2 ∂Q)) := by linarith
        _ = 1 - (Q Gᶜ).toReal -
            Real.sqrt (∫ ω in G, (R ω - 1) ^ 2 ∂Q) := by ring
        _ ≤ ∫ ω, (R ω)⁻¹ ∂Q := htilt
    have hSqSmall : Sq / q ≤ 1 / 2 := by
      apply (div_le_iff₀ hqpos).2
      dsimp [S] at hqgeS
      dsimp [Sq] at hqgeS ⊢
      linarith
    have hInvQpos : 0 < ∫ ω, (R ω)⁻¹ ∂Q := by
      have hhalf : (1 / 2 : ℝ) ≤ ∫ ω, (R ω)⁻¹ ∂Q := by
        have := htilt'
        linarith
      linarith
    let P := ∏ i ∈ Finset.Icc r b,
      ∫ ω, blockMass β t i ω ^ 2 ∂disorderLaw
    have hPge : 1 ≤ P := by
      dsimp [P]
      rw [← Finset.prod_const_one]
      apply Finset.prod_le_prod₀
      · intro i hi
        exact zero_le_one
      · intro i hi
        exact blockMass_secondMoment_ge_one β t i
    have hPnonneg : 0 ≤ P := le_trans (by norm_num) hPge
    have hinverseN' := hinverseN ϑ hϑ r b hr hrs hbplus
    rw [hDreal] at hinverseN'
    have hciOverSqrt : Ci / Real.sqrt D ≤ ci / q := by
      calc
        Ci / Real.sqrt D ≤ ci / Real.sqrt D :=
          div_le_div_of_nonneg_right (le_abs_self Ci) hsqrtDpos.le
        _ ≤ ci / q := by
          apply (div_le_div_iff₀ hsqrtDpos hqpos).2
          exact mul_le_mul_of_nonneg_left hqleSqrtD hci
    have hprodLower : (1 - ci / q) * P ≤
        ∏ i ∈ Finset.Icc r b,
          ∫ ω, (blockMass β t i ω)⁻¹ ∂disorderLaw := by
      have hfactor : 1 - ci / q ≤ 1 - Ci / Real.sqrt D := by linarith
      have hmul := mul_le_mul_of_nonneg_right hfactor hPnonneg
      exact hmul.trans hinverseN'
    have hCiSmall : ci / q ≤ 1 / 2 := by
      apply (div_le_iff₀ hqpos).2
      dsimp [S] at hqgeS
      dsimp [Sq] at hqgeS
      dsimp [ci] at hqgeS ⊢
      have hroot : 0 ≤ Real.sqrt cq := Real.sqrt_nonneg cq
      linarith
    have hJ₂le : J₂ ≤ J₀ := Nat.le_trans (Nat.le_max_left _ _) le_rfl
    have hKb₂ : b + J₂ ≤ blockCount N ρ := by omega
    have hsecondN' := hsecondN ϑ hϑ u b hub hKb₂
    rw [hDreal] at hsecondN'
    have hc₂OverD : C₂ / D ≤ c₂ / q := by
      calc
        C₂ / D ≤ c₂ / D := div_le_div_of_nonneg_right (le_abs_self C₂) hDpos.le
        _ ≤ c₂ / q := by
          apply (div_le_div_iff₀ hDpos hqpos).2
          exact mul_le_mul_of_nonneg_left hqleone hc₂
    have hnumUpper :
        ∫ ω, smoothedP2Plane β (t u) (t b) 0 ω ^ 2 ∂disorderLaw ≤
          (1 + c₂ / q) * P := by
      calc
        _ ≤ (1 + C₂ / D) * P := hsecondN'
        _ ≤ (1 + c₂ / q) * P := by
          apply mul_le_mul_of_nonneg_right _ hPnonneg
          linarith
    have hfactor : 1 - S / q ≤ (1 - Sq / q) * (1 - ci / q) := by
      dsimp [S]
      rw [add_div]
      have hmul : 0 ≤ (Sq / q) * (ci / q) := by positivity
      calc
        1 - (Sq / q + ci / q) = 1 - Sq / q - ci / q := by ring
        _ ≤ 1 - Sq / q - ci / q + (Sq / q) * (ci / q) :=
          le_add_of_nonneg_right hmul
        _ = (1 - Sq / q) * (1 - ci / q) := by ring
    have hprodLowerNonneg : 0 ≤ (1 - ci / q) * P :=
      mul_nonneg (by linarith [hCiSmall]) hPnonneg
    have hleftmul :
        (1 - Sq / q) * ((1 - ci / q) * P) ≤
          (∫ ω, (R ω)⁻¹ ∂Q) *
            ∏ i ∈ Finset.Icc r b,
              ∫ ω, (blockMass β t i ω)⁻¹ ∂disorderLaw :=
      mul_le_mul htilt' hprodLower hprodLowerNonneg
        (integral_nonneg fun ω => inv_nonneg.mpr (hRpos ω).le)
    have hmulLower : (1 - S / q) * P ≤
        (∫ ω, (R ω)⁻¹ ∂Q) *
          ∏ i ∈ Finset.Icc r b,
            ∫ ω, (blockMass β t i ω)⁻¹ ∂disorderLaw := by
      calc
        (1 - S / q) * P ≤ ((1 - Sq / q) * (1 - ci / q)) * P :=
          mul_le_mul_of_nonneg_right hfactor hPnonneg
        _ = (1 - Sq / q) * ((1 - ci / q) * P) := by ring
        _ ≤ _ := hleftmul
    have hdenomIdentity :
        ∫ ω, (smoothedP2Plane β (t u) (t b) 0 ω)⁻¹ ∂disorderLaw =
          (∫ ω, (R ω)⁻¹ ∂Q) *
            ∏ i ∈ Finset.Icc r b,
              ∫ ω, (blockMass β t i ω)⁻¹ ∂disorderLaw := by
      have htilted := integral_inv_smoothedP2Plane_eq_tilted β hclock hr (s := b)
      have hnorm : (∫ ω, (R ω)⁻¹ * W ω ∂disorderLaw) / Z =
          ∫ ω, (R ω)⁻¹ ∂Q := by
        rw [show Q = normalizedBlockTilt W Z by rfl]
        rw [integral_normalizedBlockTilt W Z hWmeas hWnonneg hZpos]
        congr 1
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω => by ring
      have hnum :
          ∫ ω, (blockRatio β t r b ω)⁻¹ *
              ∏ i ∈ Finset.Icc r b, (blockMass β t i ω)⁻¹ ∂disorderLaw =
            ∫ ω, (R ω)⁻¹ * W ω ∂disorderLaw := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω => by
          simp [R, W]
      rw [show r - 1 = u by omega] at htilted
      rw [hnum, show (∫ ω, W ω ∂disorderLaw) = Z by rfl, hnorm] at htilted
      simpa [R, W] using htilted
    have hdenomLower :
        (1 - S / q) * P ≤
          ∫ ω, (smoothedP2Plane β (t u) (t b) 0 ω)⁻¹ ∂disorderLaw := by
      rw [hdenomIdentity]
      exact hmulLower
    have hSsmall : S / q ≤ 1 / 2 := by
      apply (div_le_iff₀ hqpos).2
      linarith only [hqgeS]
    have hdenomPos : 0 <
        ∫ ω, (smoothedP2Plane β (t u) (t b) 0 ω)⁻¹ ∂disorderLaw := by
      have hfactor : 0 < 1 - S / q := by linarith
      have hPpos : 0 < P := lt_of_lt_of_le zero_lt_one hPge
      have hpositive := mul_pos hfactor hPpos
      exact lt_of_lt_of_le hpositive hdenomLower
    have hnumPos : 0 <
        ∫ ω, smoothedP2Plane β (t u) (t b) 0 ω ^ 2 ∂disorderLaw := by
      have hmem : MemLp (smoothedP2Plane β (t u) (t b) 0) 2 disorderLaw :=
        Polymer.memLp_smoothedP2Plane β (t u) (t b) 0 2 (by norm_num)
      have hv := ProbabilityTheory.variance_nonneg
        (smoothedP2Plane β (t u) (t b) 0) disorderLaw
      rw [ProbabilityTheory.variance_eq_sub hmem,
        Polymer.integral_smoothedP2Plane] at hv
      norm_num at hv
      linarith
    have hratioPos : 0 <
        (∫ ω, smoothedP2Plane β (t u) (t b) 0 ω ^ 2 ∂disorderLaw) /
          ∫ ω, (smoothedP2Plane β (t u) (t b) 0 ω)⁻¹ ∂disorderLaw :=
      div_pos hnumPos hdenomPos
    have hRatioUpper :
        (∫ ω, smoothedP2Plane β (t u) (t b) 0 ω ^ 2 ∂disorderLaw) /
          ∫ ω, (smoothedP2Plane β (t u) (t b) 0 ω)⁻¹ ∂disorderLaw ≤
          1 + C / q := by
      rw [hdenomIdentity]
      have hdenomProductPos : 0 < (∫ ω, (R ω)⁻¹ ∂Q) *
          ∏ i ∈ Finset.Icc r b,
            ∫ ω, (blockMass β t i ω)⁻¹ ∂disorderLaw := by
        rw [← hdenomIdentity]
        exact hdenomPos
      apply (div_le_iff₀ hdenomProductPos).2
      have hratioNum : 1 + c₂ / q ≤ (1 + C / q) * (1 - S / q) := by
        have hCdef : C = 2 * (c₂ + S) := by rfl
        rw [hCdef]
        have hidentity :
            (1 + 2 * (c₂ + S) / q) * (1 - S / q) - (1 + c₂ / q) =
              ((c₂ + S) * (q - 2 * S)) / q ^ 2 := by
          field_simp [ne_of_gt hqpos]
          ring
        rw [← sub_nonneg, hidentity]
        apply div_nonneg
        · exact mul_nonneg (by positivity) (by linarith [hqgeS])
        · positivity
      calc
        _ ≤ (1 + c₂ / q) * P := hnumUpper
        _ ≤ (1 + C / q) * ((1 - S / q) * P) := by
          have hmul := mul_le_mul_of_nonneg_right hratioNum hPnonneg
          simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
        _ ≤ (1 + C / q) *
            ((∫ ω, (R ω)⁻¹ ∂Q) *
              ∏ i ∈ Finset.Icc r b,
                ∫ ω, (blockMass β t i ω)⁻¹ ∂disorderLaw) := by
          have hdenomLower' := hdenomLower
          rw [hdenomIdentity] at hdenomLower'
          exact mul_le_mul_of_nonneg_left hdenomLower' (by positivity)
    have hlog := Real.log_le_sub_one_of_pos hratioPos
    have hstep : Real.log ((∫ ω, smoothedP2Plane β (t u) (t b) 0 ω ^ 2 ∂disorderLaw) /
        ∫ ω, (smoothedP2Plane β (t u) (t b) 0 ω)⁻¹ ∂disorderLaw) ≤ C / q := by
      linarith [hlog, hRatioUpper]
    have hfinalEq : C / q =
        C / ((blockCount N ρ : ℝ) - b) ^ ((1 : ℝ) / 4) := by
      rw [hquarter, ← hDreal]
    rw [← hfinalEq]
    exact hstep

end Critical2DKPZ.OnePoint

end
