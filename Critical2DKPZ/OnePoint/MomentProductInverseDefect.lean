/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.OnePoint.MomentProductInverseFourthMoment
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic

/-! # Reciprocal block-mass comparison -/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory

namespace Critical2DKPZ.OnePoint

open Critical2DKPZ.Blocks

/-- The inverse first moment differs from the second moment by the block fourth-moment scale.
Integrability of both displayed integrands is supplied by
`integrable_blockMass_inv_and_sq`. -/
theorem blockMass_inv_moment_sub_sq_moment_of (hC6 : BlockMomentsBound)
    (A ρ₀ ρ₁ : ℝ) (hρ : 1 < ρ₀) :
    ∃ C : ℝ, ∀ ρ ∈ Set.Icc ρ₀ ρ₁, ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A,
      ∀ i : ℕ, 1 ≤ i → i + 1 ≤ blockCount N ρ →
        |∫ ω, (blockMass (criticalBeta ϑ N) (blockTime N ρ) i ω)⁻¹ ∂disorderLaw -
            ∫ ω, blockMass (criticalBeta ϑ N) (blockTime N ρ) i ω ^ 2 ∂disorderLaw| ≤
          C / ((blockCount N ρ : ℝ) - i) ^ ((3 : ℝ) / 2) := by
  obtain ⟨C₆, hC₆bound⟩ := hC6 A ρ₀ ρ₁ hρ
  obtain ⟨Cinv, hCinv⟩ := integral_inv_blockMass_pow_four_le_of hC6 A ρ₀ ρ₁ hρ
  let D := max (max C₆ Cinv) 1
  have hDnonneg : 0 ≤ D := by dsimp [D]; positivity
  have hC₆le : C₆ ≤ D := by dsimp [D]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hCinvle : Cinv ≤ D := by dsimp [D]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  refine ⟨D, ?_⟩
  intro ρ hρρ
  filter_upwards [hC₆bound ρ hρρ, hCinv ρ hρρ] with N hC₆at hCinvat
  intro ϑ hϑ i hi hiK
  have hiK' : i ≤ blockCount N ρ := by omega
  have hgapNat : 1 ≤ blockCount N ρ - i := by omega
  let d : ℝ := (blockCount N ρ : ℝ) - i
  have hdpos : 0 < d := by
    dsimp [d]
    have hdNat : 0 < blockCount N ρ - i := by omega
    exact_mod_cast hdNat
  have hdle : d ≤ d + 1 := by linarith
  let β := criticalBeta ϑ N
  let t := blockTime N ρ
  let Z : Disorder → ℝ := blockMass β t i
  let X : Disorder → ℝ := fun ω => Z ω - 1
  let G : Disorder → ℝ := fun ω => |X ω| ^ 3
  let H : Disorder → ℝ := fun ω => (Z ω)⁻¹
  let F : Disorder → ℝ := fun ω => -((X ω) ^ 3 / Z ω)
  have hZpos (ω : Disorder) : 0 < Z ω := by
    exact blockMass_pos β t i ω
  have hmeanZ : ∫ ω, Z ω ∂disorderLaw = 1 := by
    dsimp [Z, blockMass, β, t]
    exact Polymer.integral_smoothedP2Plane _ _ _ _
  have hZint : Integrable Z disorderLaw := integrable_of_integral_eq_one hmeanZ
  have hmeanX : ∫ ω, X ω ∂disorderLaw = 0 := by
    rw [integral_sub hZint (integrable_const (1 : ℝ)), hmeanZ]
    simp
  have hZmem4 : MemLp Z 4 disorderLaw := by
    dsimp [Z, blockMass, β, t]
    exact Polymer.memLp_smoothedP2Plane _ _ _ _ 4 (by norm_num)
  have hXmem4 : MemLp X 4 disorderLaw := by
    exact hZmem4.sub (memLp_const (1 : ℝ))
  have hXmem4' : MemLp X (ENNReal.ofReal (4 : ℝ)) disorderLaw := by
    simpa using hXmem4
  have hGmem : MemLp G (ENNReal.ofReal ((4 : ℝ) / 3)) disorderLaw := by
    have h := hXmem4'.norm_rpow_div (3 : ENNReal)
    convert h using 1
    · funext ω
      simp [G, X, Real.norm_eq_abs]
    · rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]
      norm_num
  have hInvSqInt := integrable_blockMass_inv_and_sq β t i
  have hHInt : Integrable H disorderLaw := by
    simpa [H, Z, β, t] using hInvSqInt.1
  have hInvfour : Integrable (fun ω => H ω ^ 4) disorderLaw := by
    simpa [H, Z, β, t] using
      (integrable_blockMass_inv_pow_four β t i)
  have hHnonneg (ω : Disorder) : 0 ≤ H ω := inv_nonneg.mpr (le_of_lt (hZpos ω))
  have hHmem : MemLp H (ENNReal.ofReal (4 : ℝ)) disorderLaw := by
    apply (integrable_norm_rpow_iff hHInt.aestronglyMeasurable
      (by norm_num) (by simp)).mp
    have hpoint (ω : Disorder) : ‖H ω‖ ^ (4 : ℝ) = H ω ^ 4 := by
      calc
        ‖H ω‖ ^ (4 : ℝ) = ‖H ω‖ ^ 4 := Real.rpow_natCast _ _
        _ = H ω ^ 4 := by rw [Real.norm_eq_abs, abs_of_nonneg (hHnonneg ω)]
    rw [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (4 : ℝ))]
    have heq : (fun ω => ‖H ω‖ ^ (4 : ℝ)) = fun ω => H ω ^ 4 := funext hpoint
    convert hInvfour using 1
  have hGnonneg (ω : Disorder) : 0 ≤ G ω := by positivity
  have hGfourth : Integrable (fun ω => |X ω| ^ 4) disorderLaw := by
    have h := hXmem4.integrable_norm_pow'
    simpa only [Real.norm_eq_abs] using h
  have hGpow (ω : Disorder) : G ω ^ ((4 : ℝ) / 3) = |X ω| ^ 4 := by
    dsimp [G]
    rw [← Real.rpow_natCast (abs (X ω)) 3,
      ← Real.rpow_mul (abs_nonneg (X ω))]
    norm_num
  have hMoment4 := hC₆at ϑ hϑ i hi hiK'
  have hdenC6 : (blockCount N ρ : ℝ) + 1 - i = d + 1 := by
    dsimp [d]
    ring
  have hfourthD : ∫ ω, |X ω| ^ 4 ∂disorderLaw ≤ D / d ^ 2 := by
    have hdenpos : 0 < d + 1 := by linarith
    have hdenSq : 0 < (d + 1) ^ 2 := by positivity
    have hdsq : d ^ 2 ≤ (d + 1) ^ 2 := by nlinarith
    have hdSqPos : 0 < d ^ 2 := by positivity
    rw [hdenC6] at hMoment4
    calc
      ∫ ω, |X ω| ^ 4 ∂disorderLaw ≤ C₆ / (d + 1) ^ 2 := hMoment4.2
      _ ≤ D / (d + 1) ^ 2 := div_le_div_of_nonneg_right hC₆le (sq_nonneg _)
      _ ≤ D / d ^ 2 := div_le_div_of_nonneg_left hDnonneg hdSqPos hdsq
  have hGmoment : ∫ ω, G ω ^ ((4 : ℝ) / 3) ∂disorderLaw =
      ∫ ω, |X ω| ^ 4 ∂disorderLaw := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hGpow
  have hHmoment : ∫ ω, H ω ^ 4 ∂disorderLaw ≤ D := by
    have h := hCinvat ϑ hϑ i hi hiK'
    simpa [H, Z, β, t] using h.trans hCinvle
  have hpq : ((4 : ℝ) / 3).HolderConjugate 4 := by
    apply Real.holderConjugate_iff.mpr
    constructor <;> norm_num
  have hpqENN : ENNReal.HolderTriple (ENNReal.ofReal ((4 : ℝ) / 3))
      (ENNReal.ofReal 4) 1 := hpq.ennrealOfReal
  have hGHmem : MemLp (fun ω => G ω * H ω) 1 disorderLaw := by
    exact @MemLp.mul Disorder inferInstance ℝ inferInstance disorderLaw
      (ENNReal.ofReal ((4 : ℝ) / 3)) (ENNReal.ofReal 4) 1 H G hGmem hHmem hpqENN
  have hGHint : Integrable (fun ω => G ω * H ω) disorderLaw :=
    hGHmem.integrable (by norm_num)
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall hGnonneg) (Filter.Eventually.of_forall hHnonneg)
    hGmem hHmem
  have hHolder' : ∫ ω, G ω * H ω ∂disorderLaw ≤
      (∫ ω, G ω ^ ((4 : ℝ) / 3) ∂disorderLaw) ^ ((3 : ℝ) / 4) *
        (∫ ω, H ω ^ 4 ∂disorderLaw) ^ ((1 : ℝ) / 4) := by
    convert hHolder using 1; norm_num
  have hGmomentNonneg : 0 ≤ ∫ ω, G ω ^ ((4 : ℝ) / 3) ∂disorderLaw := by
    apply integral_nonneg
    intro ω
    exact Real.rpow_nonneg (hGnonneg ω) _
  have hHmomentNonneg : 0 ≤ ∫ ω, H ω ^ 4 ∂disorderLaw := by
    apply integral_nonneg
    intro ω
    positivity
  have hrootG : (∫ ω, G ω ^ ((4 : ℝ) / 3) ∂disorderLaw) ^ ((3 : ℝ) / 4) ≤
      (D / d ^ 2) ^ ((3 : ℝ) / 4) := by
    rw [hGmoment]
    exact Real.rpow_le_rpow (integral_nonneg (fun ω => pow_nonneg (abs_nonneg (X ω)) 4))
      hfourthD (by norm_num)
  have hrootH : (∫ ω, H ω ^ 4 ∂disorderLaw) ^ ((1 : ℝ) / 4) ≤
      D ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow hHmomentNonneg hHmoment (by norm_num)
  have hHolderBound : ∫ ω, G ω * H ω ∂disorderLaw ≤ D / d ^ ((3 : ℝ) / 2) := by
    have hscale : (D / d ^ 2) ^ ((3 : ℝ) / 4) * D ^ ((1 : ℝ) / 4) =
        D / d ^ ((3 : ℝ) / 2) := by
      have hDpos : 0 < D := by dsimp [D]; positivity
      have hdeq : (d ^ 2) ^ ((3 : ℝ) / 4) = d ^ ((3 : ℝ) / 2) := by
        rw [← Real.rpow_natCast d 2, ← Real.rpow_mul hdpos.le]
        norm_num
      rw [Real.div_rpow hDpos.le (sq_nonneg d), hdeq]
      calc
        D ^ ((3 : ℝ) / 4) / d ^ ((3 : ℝ) / 2) * D ^ ((1 : ℝ) / 4) =
            (D ^ ((3 : ℝ) / 4) * D ^ ((1 : ℝ) / 4)) / d ^ ((3 : ℝ) / 2) := by ring
        _ = D ^ (((3 : ℝ) / 4) + (1 : ℝ) / 4) / d ^ ((3 : ℝ) / 2) := by
          rw [← Real.rpow_add hDpos]
        _ = D / d ^ ((3 : ℝ) / 2) := by
          rw [show (3 : ℝ) / 4 + 1 / 4 = 1 by norm_num, Real.rpow_one]
    calc
      ∫ ω, G ω * H ω ∂disorderLaw ≤
          (∫ ω, G ω ^ ((4 : ℝ) / 3) ∂disorderLaw) ^ ((3 : ℝ) / 4) *
            (∫ ω, H ω ^ 4 ∂disorderLaw) ^ ((1 : ℝ) / 4) := hHolder'
      _ ≤ (D / d ^ 2) ^ ((3 : ℝ) / 4) * D ^ ((1 : ℝ) / 4) := by
        exact mul_le_mul hrootG hrootH (by positivity) (by positivity)
      _ = D / d ^ ((3 : ℝ) / 2) := hscale
  have hFint : Integrable F disorderLaw := by
    have hmeasZ : Measurable Z := by
      dsimp [Z]
      exact (measurable_blockMass β t i).mono (Gaussian.disorderBlock_le _ _) le_rfl
    have hmeasX : Measurable X := by
      dsimp [X]
      exact hmeasZ.sub measurable_const
    have hmeasF : Measurable F := by
      dsimp [F]
      exact ((hmeasX.pow_const 3).div hmeasZ).neg
    apply hGHint.mono' hmeasF.aestronglyMeasurable
    filter_upwards [] with ω
    have habs : |F ω| = G ω * H ω := by
      dsimp [F, G, H, X]
      rw [abs_neg, abs_div, abs_pow, abs_of_pos (hZpos ω)]
      rw [div_eq_mul_inv]
    rw [Real.norm_eq_abs, habs]
  have hInvInt : Integrable (fun ω => H ω) disorderLaw := hHInt
  have hSqInt : Integrable (fun ω => Z ω ^ 2) disorderLaw := by
    simpa [Z, β, t] using hInvSqInt.2
  have hpoint (ω : Disorder) : H ω - Z ω ^ 2 = F ω - 3 * X ω := by
    have h := hZpos ω
    have halg : H ω - Z ω ^ 2 + 3 * X ω = F ω := by
      dsimp [H, F, X]
      field_simp [ne_of_gt h]
      ring
    linarith
  have hdelta : (∫ ω, H ω ∂disorderLaw) - ∫ ω, Z ω ^ 2 ∂disorderLaw =
      ∫ ω, F ω ∂disorderLaw := by
    have hfun : (fun ω => H ω - Z ω ^ 2) = fun ω => F ω - 3 * X ω :=
      funext hpoint
    have hXintegrable : Integrable X disorderLaw := hXmem4.integrable (by norm_num)
    have h3Xintegrable : Integrable (fun ω => (3 : ℝ) * X ω) disorderLaw := by
      simpa only [smul_eq_mul] using hXintegrable.const_mul 3
    calc
      _ = ∫ ω, (H ω - Z ω ^ 2) ∂disorderLaw := by
        rw [integral_sub hInvInt hSqInt]
      _ = ∫ ω, (F ω - 3 * X ω) ∂disorderLaw := by
        rw [hfun]
      _ = (∫ ω, F ω ∂disorderLaw) - 3 * ∫ ω, X ω ∂disorderLaw := by
        rw [integral_sub hFint h3Xintegrable]
        rw [integral_const_mul]
      _ = ∫ ω, F ω ∂disorderLaw := by rw [hmeanX]; ring
  have habsF : Integrable (fun ω => |F ω|) disorderLaw := hFint.abs
  have hpointAbs (ω : Disorder) : |F ω| = G ω * H ω := by
    dsimp [F, G, H, X]
    rw [abs_neg, abs_div, abs_pow, abs_of_pos (hZpos ω), div_eq_mul_inv]
  have habsBound : |∫ ω, F ω ∂disorderLaw| ≤ D / d ^ ((3 : ℝ) / 2) := by
    calc
      |∫ ω, F ω ∂disorderLaw| ≤ ∫ ω, |F ω| ∂disorderLaw := abs_integral_le_integral_abs
      _ = ∫ ω, G ω * H ω ∂disorderLaw := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hpointAbs
      _ ≤ D / d ^ ((3 : ℝ) / 2) := hHolderBound
  rw [← hdelta] at habsBound
  simpa [d, H, Z, β, t] using habsBound

end Critical2DKPZ.OnePoint

end
