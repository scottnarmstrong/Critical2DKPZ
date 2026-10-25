/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
module

public import Mathlib
public import Critical2DKPZ.RandomWalk.Port.Walk.PairedFourier
import Critical2DKPZ.RandomWalk.Port.Walk.PairedMultiplier
import Critical2DKPZ.RandomWalk.Port.Walk.PairedOffIntegral
import Critical2DKPZ.RandomWalk.Port.Walk.PairedGaussMoments

/-!
# The local central limit theorem on `ℤ^d`

**The paired local limit theorem** `|p_n(x) + p_{n+1}(x) - 2 ctGauss d n x| ≤ C n^{-(d+2)/2}`
for `n ≥ 1`, uniformly in `x` (`exists_abs_srwHeat_add_succ_sub_le`), where
`ctGauss d n x = (d/(2πn))^{d/2} e^{-d|x|²/(2n)}`, and its parity form
`|p_n(x) - 2 ctGauss d n x| ≤ C n^{-(d+2)/2}` at the sites of the parity of `n`
(`exists_abs_srwHeat_sub_le`), Lawler–Limic, *Random Walk: A Modern Introduction*, Theorem
2.1.3. The proof writes `(2π)^d(p_n + p_{n+1} - 2 ctGauss)` as the integral over the Gaussian
region of the difference of the paired multiplier and twice the Gaussian, plus the torus integral
off the Gaussian region, minus the Gaussian off it, and bounds the three.
-/

@[expose] public section

open MeasureTheory Filter Topology

noncomputable section

namespace LatticeProb.LocalCLT

open ContinuousTime

variable {d : ℕ}

/-- The paired kernel minus twice the Gaussian, times `(2π)^d`, split over the Gaussian region,
the rest of the torus, and the complement of the Gaussian region. -/
theorem srwHeat_add_succ_sub_mul_eq (hd : 1 ≤ d) {n : ℕ} (hn : 0 < n) (x : Site d) :
    (((srwHeat d n x + srwHeat d (n + 1) x - 2 * ctGauss d n x : ℝ)) : ℂ) * (2 * Real.pi) ^ d
      = (∫ θ in gaussRegion d, (pairedIntegrand x n θ - 2 * gaussCharacter x n θ))
        + (∫ θ in torusBox d \ gaussRegion d, pairedIntegrand x n θ)
        - 2 * ∫ θ in (gaussRegion d)ᶜ, gaussCharacter x n θ := by
  have hFint := integrableOn_pairedIntegrand x n
  have hHint : Integrable (gaussCharacter x n) := integrable_character_mul_gauss hd hn x
  have hsplitT := integral_inter_add_sdiff (measurableSet_gaussRegion d) hFint
  rw [Set.inter_eq_right.mpr (gaussRegion_subset_torusBox d)] at hsplitT
  have hsplitR := integral_add_compl (measurableSet_gaussRegion d) hHint
  have hsub : (((srwHeat d n x + srwHeat d (n + 1) x - 2 * ctGauss d n x : ℝ)) : ℂ)
      * (2 * Real.pi) ^ d
      = ((srwHeat d n x + srwHeat d (n + 1) x : ℝ) : ℂ) * (2 * Real.pi) ^ d
        - 2 * ((2 * Real.pi) ^ d * (ctGauss d n x : ℂ)) := by
    push_cast; ring
  have hL0 : ((srwHeat d n x + srwHeat d (n + 1) x : ℝ) : ℂ) * (2 * Real.pi) ^ d
      = ∫ θ in torusBox d, pairedIntegrand x n θ := srwHeat_add_succ_eq_integral hd n x
  have hL1 : ∫ θ, gaussCharacter x n θ = (2 * Real.pi) ^ d * ctGauss d n x :=
    integral_character_mul_gauss hd hn x
  rw [hsub, hL0, ← hL1, integral_sub (hFint.mono_set (gaussRegion_subset_torusBox d))
    (hHint.integrableOn.const_mul 2), integral_const_mul, ← hsplitT, ← hsplitR]
  ring

/-- The Gaussian-region part of the error is `O(n^{-(d+2)/2})`. -/
theorem exists_norm_integral_gaussRegion_sub_le (hd : 1 ≤ d) :
    ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, 1 ≤ n → ∀ x : Site d,
      ‖∫ θ in gaussRegion d, (pairedIntegrand x n θ - 2 * gaussCharacter x n θ)‖
        ≤ A * (n : ℝ) ^ (-((d : ℝ) + 2) / 2) := by
  obtain ⟨K, c, hK, hc, hG⟩ := exists_abs_charFn_pow_mul_sub_le hd
  obtain ⟨K₂, hK₂, h₂⟩ := exists_integral_sq_mul_gauss_le d
  obtain ⟨K₄, hK₄, h₄⟩ := exists_integral_sq_sq_mul_gauss_le d
  refine ⟨K * (K₄ * c ^ (-((d : ℝ) + 4) / 2) + K₂ * c ^ (-((d : ℝ) + 2) / 2)),
      by positivity,
    fun n hn x => ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hcn : 0 < c * n := by positivity
  obtain ⟨hi2, hv2⟩ := h₂ (c * n) hcn
  obtain ⟨hi4, hv4⟩ := h₄ (c * n) hcn
  set B : (Fin d → ℝ) → ℝ := fun θ => K * ((n : ℝ) * ((∑ i, θ i ^ 2) ^ 2
    * Real.exp (-(c * n) * ∑ i, θ i ^ 2)) + (∑ i, θ i ^ 2)
        * Real.exp (-(c * n) * ∑ i, θ i ^ 2))
    with hB
  have hBint : Integrable B := ((hi4.const_mul (n : ℝ)).add hi2).const_mul K
  have hbound : ∀ θ ∈ gaussRegion d, ‖pairedIntegrand x n θ - 2 * gaussCharacter x n θ‖
      ≤ B θ := by
    intro θ hθ
    have hrew : pairedIntegrand x n θ - 2 * gaussCharacter x n θ = character x θ
        * ((charFn d θ ^ n * (1 + charFn d θ)
          - 2 * Real.exp (-(n : ℝ) * (∑ i, θ i ^ 2) / (2 * d)) : ℝ) : ℂ) := by
      unfold pairedIntegrand gaussCharacter; push_cast; ring
    rw [hrew, norm_mul, norm_character, one_mul, Complex.norm_real, Real.norm_eq_abs]
    refine (hG n hn θ hθ).trans (le_of_eq ?_)
    rw [hB]
    simp only
    ring_nf
  calc ‖∫ θ in gaussRegion d, (pairedIntegrand x n θ - 2 * gaussCharacter x n θ)‖
      ≤ ∫ θ in gaussRegion d, B θ :=
        norm_integral_le_of_norm_le hBint.integrableOn
          ((ae_restrict_iff' (measurableSet_gaussRegion d)).mpr
            (Filter.Eventually.of_forall hbound))
    _ ≤ ∫ θ, B θ := setIntegral_le_integral hBint
        (Filter.Eventually.of_forall fun θ => by rw [hB]; positivity)
    _ = K * ((n : ℝ)
        * (∫ θ : Fin d → ℝ, (∑ i, θ i ^ 2) ^ 2 * Real.exp (-(c * n) * ∑ i, θ i ^ 2))
          + ∫ θ : Fin d → ℝ, (∑ i, θ i ^ 2) * Real.exp (-(c * n) * ∑ i, θ i ^ 2)) := by
        rw [hB, integral_const_mul, integral_add (hi4.const_mul _) hi2, integral_const_mul]
    _ ≤ K * ((n : ℝ) * (K₄ * (c * n) ^ (-((d : ℝ) + 4) / 2))
          + K₂ * (c * n) ^ (-((d : ℝ) + 2) / 2)) := by
        gcongr
    _ = K * (K₄ * c ^ (-((d : ℝ) + 4) / 2) + K₂ * c ^ (-((d : ℝ) + 2) / 2))
          * (n : ℝ) ^ (-((d : ℝ) + 2) / 2) := by
        rw [Real.mul_rpow hc.le hnpos.le, Real.mul_rpow hc.le hnpos.le]
        have hshift : (n : ℝ) * (n : ℝ) ^ (-((d : ℝ) + 4) / 2)
            = (n : ℝ) ^ (-((d : ℝ) + 2) / 2) := by
          rw [← Real.rpow_one_add' hnpos.le]
          · congr 1; ring
          · have : (0 : ℝ) ≤ d := by positivity
            intro h; linarith
        calc K * ((n : ℝ)
            * (K₄ * (c ^ (-((d : ℝ) + 4) / 2) * (n : ℝ) ^ (-((d : ℝ) + 4) / 2)))
              + K₂ * (c ^ (-((d : ℝ) + 2) / 2) * (n : ℝ) ^ (-((d : ℝ) + 2) / 2)))
            = K * (K₄ * c ^ (-((d : ℝ) + 4) / 2)
                * ((n : ℝ) * (n : ℝ) ^ (-((d : ℝ) + 4) / 2))
              + K₂ * c ^ (-((d : ℝ) + 2) / 2) * (n : ℝ) ^ (-((d : ℝ) + 2) / 2)) := by ring
          _ = _ := by rw [hshift]; ring

/-- The part of the torus off the Gaussian region contributes `O(n^{-(d+2)/2})`. -/
theorem exists_norm_integral_torusBox_sdiff_le (hd : 1 ≤ d) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ n : ℕ, 1 ≤ n → ∀ x : Site d,
      ‖∫ θ in torusBox d \ gaussRegion d, pairedIntegrand x n θ‖
        ≤ K₀ * (n : ℝ) ^ (-((d : ℝ) + 2) / 2) := by
  obtain ⟨K₀, hK₀, h₀⟩ := exists_integral_offBound_le hd
  refine ⟨K₀, hK₀, fun n hn x => ?_⟩
  obtain ⟨hint0, hval0⟩ := h₀ n hn
  have hbound : ∀ θ ∈ torusBox d \ gaussRegion d, ‖pairedIntegrand x n θ‖
      ≤ offBound d n θ := by
    intro θ hθ
    have hcast : pairedIntegrand x n θ
        = character x θ * ((charFn d θ ^ n * (1 + charFn d θ) : ℝ) : ℂ) := by
      unfold pairedIntegrand; push_cast; ring
    rw [hcast, norm_mul, norm_character, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact abs_charFn_pow_mul_le_offBound hd hθ.1 hθ.2 n
  have hmeasD : MeasurableSet (torusBox d \ gaussRegion d) :=
    (torusBox_measurable d).diff (measurableSet_gaussRegion d)
  calc ‖∫ θ in torusBox d \ gaussRegion d, pairedIntegrand x n θ‖
      ≤ ∫ θ in torusBox d \ gaussRegion d, offBound d n θ :=
        norm_integral_le_of_norm_le (hint0.mono_set Set.sdiff_subset)
          ((ae_restrict_iff' hmeasD).mpr (Filter.Eventually.of_forall hbound))
    _ ≤ ∫ θ in torusBox d, offBound d n θ :=
        setIntegral_mono_set hint0
          (Filter.Eventually.of_forall fun θ => offBound_nonneg hd n θ)
          (Filter.Eventually.of_forall fun θ hθ => hθ.1)
    _ ≤ K₀ * (n : ℝ) ^ (-((d : ℝ) + 2) / 2) := hval0

/-- The Gaussian off the Gaussian region contributes `O(n^{-(d+2)/2})`. -/
theorem exists_norm_integral_compl_gaussCharacter_le (hd : 1 ≤ d) :
    ∃ K₁ : ℝ, 0 < K₁ ∧ ∀ n : ℕ, 1 ≤ n → ∀ x : Site d,
      ‖∫ θ in (gaussRegion d)ᶜ, gaussCharacter x n θ‖
        ≤ K₁ * (n : ℝ) ^ (-((d : ℝ) + 2) / 2) := by
  obtain ⟨K₁, hK₁, h₁⟩ := exists_integral_compl_gaussRegion_le hd
  refine ⟨K₁, hK₁, fun n hn x => ?_⟩
  have hnd : 0 < n := by omega
  have hHint : Integrable (gaussCharacter x n) := integrable_character_mul_gauss hd hnd x
  have hnormeq : ∀ θ, ‖gaussCharacter x n θ‖
      = Real.exp (-(n : ℝ) * (∑ i, θ i ^ 2) / (2 * d)) := by
    intro θ
    unfold gaussCharacter
    rw [norm_mul, norm_character, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  have hEint : Integrable fun θ : Fin d
      → ℝ => Real.exp (-(n : ℝ) * (∑ i, θ i ^ 2) / (2 * d)) :=
    hHint.norm.congr (Filter.Eventually.of_forall hnormeq)
  calc ‖∫ θ in (gaussRegion d)ᶜ, gaussCharacter x n θ‖
      ≤ ∫ θ in (gaussRegion d)ᶜ, Real.exp (-(n : ℝ) * (∑ i, θ i ^ 2) / (2 * d)) :=
        norm_integral_le_of_norm_le hEint.integrableOn
          (Filter.Eventually.of_forall fun θ => le_of_eq (hnormeq θ))
    _ ≤ K₁ * (n : ℝ) ^ (-((d : ℝ) + 2) / 2) := h₁ n hn

/-- **The paired local central limit theorem** on `ℤ^d` (Lawler–Limic, Theorem 2.1.3):
`|p_n(x) + p_{n+1}(x) - 2 ctGauss d n x| ≤ C n^{-(d+2)/2}` for `n ≥ 1`, uniformly in `x`, where
`ctGauss d n x = (d/(2πn))^{d/2} e^{-d|x|²/(2n)}`. -/
theorem exists_abs_srwHeat_add_succ_sub_le (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ x : Site d,
      |srwHeat d n x + srwHeat d (n + 1) x - 2 * ctGauss d n x|
        ≤ C * (n : ℝ) ^ (-((d : ℝ) + 2) / 2) := by
  obtain ⟨A, hA, hAb⟩ := exists_norm_integral_gaussRegion_sub_le hd
  obtain ⟨K₀, hK₀, hK₀b⟩ := exists_norm_integral_torusBox_sdiff_le hd
  obtain ⟨K₁, hK₁, hK₁b⟩ := exists_norm_integral_compl_gaussCharacter_le hd
  have hpi : (0 : ℝ) < (2 * Real.pi) ^ d := by positivity
  refine ⟨(A + K₀ + 2 * K₁) / (2 * Real.pi) ^ d, by positivity, fun n hn x => ?_⟩
  have hnd : 0 < n := by omega
  set r : ℝ := (n : ℝ) ^ (-((d : ℝ) + 2) / 2) with hr
  have h := congrArg (‖·‖) (srwHeat_add_succ_sub_mul_eq hd hnd x)
  have hpinorm : ‖((2 * Real.pi : ℂ)) ^ d‖ = (2 * Real.pi) ^ d := by
    rw [norm_pow, show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, hpinorm] at h
  have hsum : |srwHeat d n x + srwHeat d (n + 1) x - 2 * ctGauss d n x| * (2 * Real.pi) ^ d
      ≤ (A + K₀ + 2 * K₁) * r := by
    rw [h]
    refine (norm_sub_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
    have h3 : ‖2 * ∫ θ in (gaussRegion d)ᶜ, gaussCharacter x n θ‖ ≤ 2 * (K₁ * r) := by
      rw [norm_mul, Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left (hK₁b n hn x) (by norm_num)
    linarith [hAb n hn x, hK₀b n hn x, h3]
  rw [div_mul_eq_mul_div, le_div_iff₀ hpi]
  exact hsum

/-- **The local central limit theorem in parity form**: at the sites of the parity of `n`,
`|p_n(x) - 2 ctGauss d n x| ≤ C n^{-(d+2)/2}`. -/
theorem exists_abs_srwHeat_sub_le (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ x : Site d,
      ((graphNorm x : ℕ) : ZMod 2) = ((n : ℕ) : ZMod 2) →
      |srwHeat d n x - 2 * ctGauss d n x| ≤ C * (n : ℝ) ^ (-((d : ℝ) + 2) / 2) := by
  obtain ⟨C, hC, h⟩ := exists_abs_srwHeat_add_succ_sub_le hd
  refine ⟨C, hC, fun n hn x hpar => ?_⟩
  have hzero : srwHeat d (n + 1) x = 0 := by
    apply srwHeat_eq_zero_of_parity
    rw [hpar]
    push_cast
    intro hc
    have h1 : (1 : ZMod 2) = 0 := by
      linear_combination -hc
    exact absurd h1 (by decide)
  have h' := h n hn x
  rw [hzero, add_zero] at h'
  exact h'

end LatticeProb.LocalCLT

end
