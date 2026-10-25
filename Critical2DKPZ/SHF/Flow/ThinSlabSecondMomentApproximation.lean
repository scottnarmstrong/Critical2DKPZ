/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic

/-! # Second-moment comparison under a square-integrable cutoff error -/

@[expose] public section
open MeasureTheory Filter
open scoped Topology
namespace Critical2DKPZ.SHF.Flow

private theorem slab_abs_sq_sub_sq_le (x y η : ℝ) (hη : 0 < η) :
    |x ^ 2 - y ^ 2| ≤ η * x ^ 2 + (1 + η⁻¹) * (x - y) ^ 2 := by
  have heq : η * (η * x ^ 2 + (1 + η⁻¹) * (x - y) ^ 2) =
      (η * x) ^ 2 + (η + 1) * (x - y) ^ 2 := by
    field_simp
  apply abs_le.mpr
  constructor
  · apply (mul_le_mul_iff_right₀ hη).mp
    rw [mul_neg, heq]
    nlinarith only [sq_nonneg (η * x + (x - y))]
  · apply (mul_le_mul_iff_right₀ hη).mp
    rw [heq]
    nlinarith only [sq_nonneg (η * x - (x - y)),
      mul_nonneg hη.le (sq_nonneg (x - y))]

/-- The second moments of two square-integrable functions differ by a small
multiple of the first second moment and a controlled square-error term. -/
theorem integral_sq_sub_integral_sq_abs_le {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f g : X → ℝ}
    (hf : Integrable (fun x => f x ^ 2) μ) (hg : Integrable (fun x => g x ^ 2) μ)
    (hd : Integrable (fun x => (f x - g x) ^ 2) μ)
    {η : ℝ} (hη : 0 < η) :
    |(∫ x, f x ^ 2 ∂μ) - ∫ x, g x ^ 2 ∂μ| ≤
      η * (∫ x, f x ^ 2 ∂μ) + (1 + η⁻¹) * ∫ x, (f x - g x) ^ 2 ∂μ := by
  rw [← integral_sub hf hg]
  have hmajorant := (hf.const_mul η).add (hd.const_mul (1 + η⁻¹))
  calc
    _ ≤ ∫ x, η * f x ^ 2 + (1 + η⁻¹) * (f x - g x) ^ 2 ∂μ := by
      rw [← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le hmajorant
      filter_upwards [] with x
      simpa only [Real.norm_eq_abs, Pi.add_apply] using slab_abs_sq_sub_sq_le (f x) (g x) η hη
    _ = _ := by rw [integral_add (hf.const_mul η) (hd.const_mul (1 + η⁻¹)),
      integral_const_mul, integral_const_mul]

/-- A bounded second moment and a sufficiently small square error control
second moments uniformly over the underlying functions and measure. -/
theorem exists_sq_error_threshold {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ δ > 0, ∀ {X : Type*} [MeasurableSpace X] (μ : Measure X) (f g : X → ℝ),
      Integrable (fun x => f x ^ 2) μ → Integrable (fun x => g x ^ 2) μ →
      Integrable (fun x => (f x - g x) ^ 2) μ →
      (∫ x, f x ^ 2 ∂μ) ≤ C → (∫ x, (f x - g x) ^ 2 ∂μ) ≤ δ →
      |(∫ x, f x ^ 2 ∂μ) - ∫ x, g x ^ 2 ∂μ| < ε := by
  let η : ℝ := ε / (4 * (C + 1))
  have hη : 0 < η := div_pos hε (by positivity)
  have hηC : η * C ≤ ε / 4 := by
    have heq : η * (C + 1) = ε / 4 := by dsimp [η]; field_simp
    nlinarith only [hη.le, heq]
  let δ : ℝ := ε / (4 * (1 + η⁻¹))
  have hfactor : 0 < 1 + η⁻¹ := by positivity
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδeq : (1 + η⁻¹) * δ = ε / 4 := by dsimp [δ]; field_simp
  refine ⟨δ, hδ, ?_⟩
  intro X _ μ f g hf hg hd hbound herror
  have h := integral_sq_sub_integral_sq_abs_le hf hg hd hη
  have hfirst := mul_le_mul_of_nonneg_left hbound hη.le
  have hsecond := mul_le_mul_of_nonneg_left herror hfactor.le
  linarith only [h, hfirst, hsecond, hηC, hδeq, hε]

/-- Compact second-moment limits extend to an uncut limit when the square
cutoff error vanishes uniformly eventually and the uncut second moments are bounded. -/
theorem tendsto_secondMoment_of_cutoffs {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : ℕ → X → ℝ) (g : ℝ → ℕ → X → ℝ)
    (A : ℝ → ℝ) (L : ℝ)
    (hbound : ∃ C ≥ 0, ∀ᶠ N : ℕ in atTop,
      Integrable (fun x => f N x ^ 2) μ ∧ (∫ x, f N x ^ 2 ∂μ) ≤ C)
    (hInt : ∀ R, ∀ᶠ N : ℕ in atTop,
      Integrable (fun x => g R N x ^ 2) μ ∧
      Integrable (fun x => (f N x - g R N x) ^ 2) μ)
    (hTail : ∀ δ > 0, ∃ R₀ : ℝ, ∀ R ≥ R₀, ∀ᶠ N : ℕ in atTop,
      (∫ x, (f N x - g R N x) ^ 2 ∂μ) ≤ δ)
    (hCompact : ∀ R, Tendsto (fun N => ∫ x, g R N x ^ 2 ∂μ) atTop (𝓝 (A R)))
    (hContinuum : Tendsto A atTop (𝓝 L)) :
    Tendsto (fun N => ∫ x, f N x ^ 2 ∂μ) atTop (𝓝 L) := by
  obtain ⟨C, hC, hbound⟩ := hbound
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hthird : 0 < ε / 3 := div_pos hε (by norm_num)
  obtain ⟨δ, hδ, hCompare⟩ := exists_sq_error_threshold hC hthird
  obtain ⟨R₀, hR₀⟩ := hTail δ hδ
  have hNear := (Metric.tendsto_nhds.mp hContinuum) (ε / 3) hthird
  obtain ⟨R₁, hR₁⟩ := eventually_atTop.mp hNear
  let R := max R₀ R₁
  have hA : |A R - L| < ε / 3 := by
    simpa only [Real.dist_eq] using hR₁ R (le_max_right _ _)
  have hLimit := (Metric.tendsto_nhds.mp (hCompact R)) (ε / 3) hthird
  filter_upwards [hbound, hInt R, hR₀ R (le_max_left _ _), hLimit] with N hN hI hE hL
  have hfirst := hCompare μ (f N) (g R N) hN.1 hI.1 hI.2 hN.2 hE
  have hsecond : |(∫ x, g R N x ^ 2 ∂μ) - A R| < ε / 3 := by
    simpa only [Real.dist_eq] using hL
  rw [Real.dist_eq]
  have hTriangle :
      |(∫ x, f N x ^ 2 ∂μ) - L| ≤
        |(∫ x, f N x ^ 2 ∂μ) - ∫ x, g R N x ^ 2 ∂μ| +
        |(∫ x, g R N x ^ 2 ∂μ) - A R| + |A R - L| := by
    calc
      _ = |((∫ x, f N x ^ 2 ∂μ) - ∫ x, g R N x ^ 2 ∂μ) +
          ((∫ x, g R N x ^ 2 ∂μ) - A R) + (A R - L)| := by congr 1; ring
      _ ≤ _ := (abs_add_le
        (((∫ x, f N x ^ 2 ∂μ) - ∫ x, g R N x ^ 2 ∂μ) +
          ((∫ x, g R N x ^ 2 ∂μ) - A R)) (A R - L)).trans
        (add_le_add (abs_add_le _ _) (le_refl |A R - L|))
  linarith only [hTriangle, hfirst, hsecond, hA]

/-- Convergent compact second moments and uniformly vanishing square cutoff
errors already imply existence of an uncut second-moment limit. -/
theorem exists_secondMoment_limit_of_cutoffs {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : ℕ → X → ℝ) (g : ℝ → ℕ → X → ℝ) (A : ℝ → ℝ)
    (hf : ∀ᶠ N : ℕ in atTop, Integrable (fun x => f N x ^ 2) μ)
    (hg : ∀ R, ∀ᶠ N : ℕ in atTop, Integrable (fun x => g R N x ^ 2) μ)
    (hd : ∀ R, ∀ᶠ N : ℕ in atTop, Integrable (fun x => (f N x - g R N x) ^ 2) μ)
    (hTail : ∀ δ > 0, ∃ R₀ : ℝ, ∀ R ≥ R₀, ∀ᶠ N : ℕ in atTop,
      (∫ x, (f N x - g R N x) ^ 2 ∂μ) ≤ δ)
    (hCompact : ∀ R, Tendsto (fun N => ∫ x, g R N x ^ 2 ∂μ) atTop (𝓝 (A R))) :
    ∃ L : ℝ, Tendsto (fun N => ∫ x, f N x ^ 2 ∂μ) atTop (𝓝 L) := by
  obtain ⟨R₀, hR₀⟩ := hTail 1 one_pos
  have hCompactBound : ∀ᶠ N : ℕ in atTop,
      (∫ x, g R₀ N x ^ 2 ∂μ) ≤ |A R₀| + 1 := by
    filter_upwards [(Metric.tendsto_nhds.mp (hCompact R₀)) 1 one_pos] with N hN
    rw [Real.dist_eq] at hN
    have hupper := (abs_lt.mp hN).2
    linarith only [hupper, le_abs_self (A R₀)]
  let C : ℝ := 2 + 2 * (|A R₀| + 1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hBound : ∀ᶠ N : ℕ in atTop,
      Integrable (fun x => f N x ^ 2) μ ∧ (∫ x, f N x ^ 2 ∂μ) ≤ C := by
    filter_upwards [hf, hg R₀, hd R₀, hR₀ R₀ le_rfl, hCompactBound] with N hF hG hD hE hB
    refine ⟨hF, ?_⟩
    have hMajor : (∫ x, f N x ^ 2 ∂μ) ≤
        ∫ x, 2 * (f N x - g R₀ N x) ^ 2 + 2 * g R₀ N x ^ 2 ∂μ := by
      apply integral_mono hF ((hD.const_mul 2).add (hG.const_mul 2))
      intro x
      change f N x ^ 2 ≤ 2 * (f N x - g R₀ N x) ^ 2 + 2 * g R₀ N x ^ 2
      nlinarith only [sq_nonneg (f N x - 2 * g R₀ N x)]
    rw [integral_add (hD.const_mul 2) (hG.const_mul 2), integral_const_mul,
      integral_const_mul] at hMajor
    dsimp [C]
    linarith only [hMajor, hE, hB]
  have hApprox : ∀ ε > 0, ∃ a : ℝ, ∀ᶠ N : ℕ in atTop,
      |(∫ x, f N x ^ 2 ∂μ) - a| < ε := by
    intro ε hε
    obtain ⟨δ, hδ, hCompare⟩ := exists_sq_error_threshold hC (half_pos hε)
    obtain ⟨R, hR⟩ := hTail δ hδ
    refine ⟨A R, ?_⟩
    filter_upwards [hBound, hg R, hd R, hR R le_rfl,
      (Metric.tendsto_nhds.mp (hCompact R)) (ε / 2) (half_pos hε)] with N hF hG hD hE hL
    have hfirst := hCompare μ (f N) (g R N) hF.1 hG hD hF.2 hE
    rw [Real.dist_eq] at hL
    exact (abs_sub_le _ _ _).trans_lt (by linarith only [hfirst, hL])
  apply cauchySeq_tendsto_of_complete
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨a, ha⟩ := hApprox (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp ha
  refine ⟨N, ?_⟩
  intro m hm n hn
  rw [Real.dist_eq]
  have htri := abs_sub_le (∫ x, f m x ^ 2 ∂μ) a (∫ x, f n x ^ 2 ∂μ)
  have hrev : |a - ∫ x, f n x ^ 2 ∂μ| < ε / 2 := by
    rw [abs_sub_comm]
    exact hN n hn
  linarith only [htri, hN m hm, hrev]

/-- The limits of compact second moments approach the uncut second-moment
limit whenever the square cutoff errors vanish uniformly eventually. -/
theorem tendsto_cutoff_secondMoment_limits {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : ℕ → X → ℝ) (g : ℝ → ℕ → X → ℝ) (A : ℝ → ℝ) (L : ℝ)
    (hf : ∀ᶠ N : ℕ in atTop, Integrable (fun x => f N x ^ 2) μ)
    (hInt : ∀ R, ∀ᶠ N : ℕ in atTop,
      Integrable (fun x => g R N x ^ 2) μ ∧
      Integrable (fun x => (f N x - g R N x) ^ 2) μ)
    (hTail : ∀ δ > 0, ∃ R₀ : ℝ, ∀ R ≥ R₀, ∀ᶠ N : ℕ in atTop,
      (∫ x, (f N x - g R N x) ^ 2 ∂μ) ≤ δ)
    (hCompact : ∀ R, Tendsto (fun N => ∫ x, g R N x ^ 2 ∂μ) atTop (𝓝 (A R)))
    (hFull : Tendsto (fun N => ∫ x, f N x ^ 2 ∂μ) atTop (𝓝 L)) :
    Tendsto A atTop (𝓝 L) := by
  let C : ℝ := |L| + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hBound : ∀ᶠ N : ℕ in atTop, (∫ x, f N x ^ 2 ∂μ) ≤ C := by
    filter_upwards [(Metric.tendsto_nhds.mp hFull) 1 one_pos] with N hN
    rw [Real.dist_eq] at hN
    have hu := (abs_lt.mp hN).2
    dsimp [C]
    linarith only [hu, le_abs_self L]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hCompare⟩ := exists_sq_error_threshold hC (half_pos hε)
  obtain ⟨R₀, hR₀⟩ := hTail δ hδ
  filter_upwards [eventually_ge_atTop R₀] with R hR
  have hApprox : ∀ᶠ N : ℕ in atTop,
      |(∫ x, f N x ^ 2 ∂μ) - ∫ x, g R N x ^ 2 ∂μ| ≤ ε / 2 := by
    filter_upwards [hf, hInt R, hBound, hR₀ R hR] with N hF hI hB hE
    exact (hCompare μ (f N) (g R N) hF hI.1 hI.2 hB hE).le
  have hlim := (hFull.sub (hCompact R)).abs
  have hle : |L - A R| ≤ ε / 2 := le_of_tendsto hlim hApprox
  rw [Real.dist_eq, abs_sub_comm]
  exact hle.trans_lt (half_lt_self hε)

/-- The compact and uncut second moments converge to the same limit. -/
theorem exists_secondMoment_limit_with_cutoffs {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : ℕ → X → ℝ) (g : ℝ → ℕ → X → ℝ) (A : ℝ → ℝ)
    (hf : ∀ᶠ N : ℕ in atTop, Integrable (fun x => f N x ^ 2) μ)
    (hg : ∀ R, ∀ᶠ N : ℕ in atTop, Integrable (fun x => g R N x ^ 2) μ)
    (hd : ∀ R, ∀ᶠ N : ℕ in atTop, Integrable (fun x => (f N x - g R N x) ^ 2) μ)
    (hTail : ∀ δ > 0, ∃ R₀ : ℝ, ∀ R ≥ R₀, ∀ᶠ N : ℕ in atTop,
      (∫ x, (f N x - g R N x) ^ 2 ∂μ) ≤ δ)
    (hCompact : ∀ R, Tendsto (fun N => ∫ x, g R N x ^ 2 ∂μ) atTop (𝓝 (A R))) :
    ∃ L : ℝ, Tendsto (fun N => ∫ x, f N x ^ 2 ∂μ) atTop (𝓝 L) ∧
      Tendsto A atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := exists_secondMoment_limit_of_cutoffs μ f g A hf hg hd hTail hCompact
  exact ⟨L, hL, tendsto_cutoff_secondMoment_limits μ f g A L hf
    (fun R => (hg R).and (hd R)) hTail hCompact hL⟩

end Critical2DKPZ.SHF.Flow
end
