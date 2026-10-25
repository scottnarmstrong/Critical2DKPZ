/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A. Bou-Rabee, Scott Armstrong
Modified for Critical2DKPZ, 2026.
-/
module

public import Critical2DKPZ.Analysis.Sobolev.Rellich.Weight
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Uniform derivative bounds on a common compact support control Sobolev energy.

Adapted from work of A. Bou-Rabee, licensed under Apache 2.0. -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform Topology Filter

namespace Critical2DKPZ.Analysis.Sobolev.Rellich


/-! Polynomial Fourier decay from uniform derivative bounds on a compact support. -/

/-! Integration by parts gives Fourier decay sufficient to integrate the Sobolev weight. -/

private theorem weight_lower (t : ℝ) :
    (1 + t) ^ 2 ≤ 2 * (1 + (2 * Real.pi * t) ^ 2) := by
  have hpi9 : (9 : ℝ) < Real.pi ^ 2 := by
    have h1 : (0 : ℝ) < Real.pi - 3 := by linarith [Real.pi_gt_three]
    have h2 : (0 : ℝ) < Real.pi + 3 := by linarith [Real.pi_gt_three]
    nlinarith [mul_pos h1 h2]
  have hc : (0 : ℝ) ≤ 8 * Real.pi ^ 2 - 2 := by linarith
  nlinarith [sq_nonneg (t - 1), mul_nonneg hc (sq_nonneg t)]

private theorem weight_upper {t : ℝ} (ht : 0 ≤ t) :
    1 + (2 * Real.pi * t) ^ 2 ≤ (2 * Real.pi) ^ 2 * (1 + t) ^ 2 := by
  have hpi9 : (9 : ℝ) < Real.pi ^ 2 := by
    have h1 : (0 : ℝ) < Real.pi - 3 := by linarith [Real.pi_gt_three]
    have h2 : (0 : ℝ) < Real.pi + 3 := by linarith [Real.pi_gt_three]
    nlinarith [mul_pos h1 h2]
  nlinarith [mul_nonneg (sq_nonneg Real.pi) ht, hpi9]

/-- Convert an `rpow` of a squared nonnegative real into an `rpow` with doubled exponent. -/
private theorem sq_rpow {x : ℝ} (hx : 0 ≤ x) (y : ℝ) :
    (x ^ 2 : ℝ) ^ y = x ^ (2 * y) := by
  rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx]
  norm_num

/-- The weight `(1 + (2π‖ξ‖)²)^{s₀}` is controlled, up to an explicit constant depending only on
`s₀`, by `(1 + ‖ξ‖)^{2s₀}`. -/
private theorem weight_rpow_le (s₀ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
      (1 + (2 * Real.pi * t) ^ 2) ^ s₀ ≤ C * (1 + t) ^ (2 * s₀) := by
  rcases le_total 0 s₀ with hs | hs
  · refine ⟨(2 * Real.pi) ^ (2 * s₀), by positivity, fun t ht => ?_⟩
    have hle := weight_upper ht
    calc (1 + (2 * Real.pi * t) ^ 2) ^ s₀
        ≤ ((2 * Real.pi) ^ 2 * (1 + t) ^ 2) ^ s₀ :=
          Real.rpow_le_rpow (by positivity) hle hs
      _ = ((2 * Real.pi) ^ 2) ^ s₀ * ((1 + t) ^ 2) ^ s₀ :=
          Real.mul_rpow (by positivity) (by positivity)
      _ = (2 * Real.pi) ^ (2 * s₀) * (1 + t) ^ (2 * s₀) := by
          rw [sq_rpow (by positivity) s₀, sq_rpow (by positivity) s₀]
  · refine ⟨2 ^ (-s₀), by positivity, fun t ht => ?_⟩
    have hle := weight_lower t
    have hxpos : (0 : ℝ) < (1 + t) ^ 2 / 2 := by positivity
    have h2 : (1 + t) ^ 2 / 2 ≤ 1 + (2 * Real.pi * t) ^ 2 := by linarith
    calc (1 + (2 * Real.pi * t) ^ 2) ^ s₀
        ≤ ((1 + t) ^ 2 / 2) ^ s₀ := Real.rpow_le_rpow_of_nonpos hxpos h2 hs
      _ = ((1 + t) ^ 2) ^ s₀ / (2 : ℝ) ^ s₀ := Real.div_rpow (by positivity) (by norm_num) s₀
      _ = (1 + t) ^ (2 * s₀) / (2 : ℝ) ^ s₀ := by rw [sq_rpow (by positivity) s₀]
      _ = (2 : ℝ) ^ (-s₀) * (1 + t) ^ (2 * s₀) := by
          rw [Real.rpow_neg (by norm_num), div_eq_mul_inv, mul_comm]

/-- Composing a real-valued smooth function with the isometric embedding `ℝ ↪ ℂ` does not change
the norm of any iterated derivative. -/
private theorem iteratedFDeriv_ofReal_norm {d : ℕ} {g : Space d → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (n : ℕ) (x : Space d) :
    ‖iteratedFDeriv ℝ n (fun y => (g y : ℂ)) x‖ = ‖iteratedFDeriv ℝ n g x‖ := by
  have hcomp : (fun y => (g y : ℂ)) = Complex.ofRealLI ∘ g := by
    funext y; simp [Complex.ofRealLI_apply]
  rw [hcomp]
  exact Complex.ofRealLI.norm_iteratedFDeriv_comp_left hg.contDiffAt
    (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))

/-- The `ℂ`-coercion of a smooth real-valued function is smooth. -/
private theorem contDiff_ofReal {d : ℕ} {g : Space d → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) : ContDiff ℝ (⊤ : ℕ∞) (fun y => (g y : ℂ)) := by
  have hcomp : (fun y => (g y : ℂ)) = Complex.ofRealCLM ∘ g := by
    funext y; simp [Complex.ofRealCLM_apply]
  rw [hcomp]
  exact Complex.ofRealCLM.contDiff.comp hg

/-- Every iterated derivative of a smooth function supported in a fixed compact set has
integrable norm. -/
private theorem iteratedFDeriv_integrable {d : ℕ} {K : Set (Space d)} (hK : IsCompact K)
    {g : Space d → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hsupp : tsupport g ⊆ K) (n : ℕ) :
    Integrable (fun v => ‖iteratedFDeriv ℝ n (fun x => (g x : ℂ)) v‖) := by
  have hgc : HasCompactSupport g := IsCompact.of_isClosed_subset hK (isClosed_tsupport g) hsupp
  have hcont : Continuous (iteratedFDeriv ℝ n g) :=
    hg.continuous_iteratedFDeriv (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  have hcs : HasCompactSupport (iteratedFDeriv ℝ n g) := hgc.iteratedFDeriv n
  have hint : Integrable (iteratedFDeriv ℝ n g) := hcont.integrable_of_hasCompactSupport hcs
  have heq : (fun v => ‖iteratedFDeriv ℝ n (fun x => (g x : ℂ)) v‖)
      = (fun v => ‖iteratedFDeriv ℝ n g v‖) := by
    funext v; exact iteratedFDeriv_ofReal_norm hg n v
  rw [heq]
  exact hint.norm

/-- For `g` smooth and supported in the compact `K` with `j`-th derivative bounded by `1`
everywhere, `∫ ‖iteratedFDeriv ℝ j (ℂ-coercion of g)‖ ≤ volume K`. -/
private theorem term_bound {d : ℕ} {K : Set (Space d)} (hK : IsCompact K)
    {g : Space d → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hsupp : tsupport g ⊆ K) {j : ℕ}
    (hbd : ∀ x : Space d, ‖iteratedFDeriv ℝ j g x‖ ≤ 1) :
    ∫ v, ‖iteratedFDeriv ℝ j (fun x => (g x : ℂ)) v‖ ≤ (volume K).toReal := by
  have hzero : ∀ x : Space d, x ∉ K →
      ‖iteratedFDeriv ℝ j (fun y => (g y : ℂ)) x‖ = 0 := by
    intro x hx
    have hx' : x ∉ tsupport g := fun hmem => hx (hsupp hmem)
    have hx'' : x ∉ Function.support (iteratedFDeriv ℝ j g) :=
      fun hmem => hx' (support_iteratedFDeriv_subset j hmem)
    have hz : iteratedFDeriv ℝ j g x = 0 := Function.notMem_support.mp hx''
    rw [iteratedFDeriv_ofReal_norm hg j x, hz, norm_zero]
  have heq : ∫ v, ‖iteratedFDeriv ℝ j (fun x => (g x : ℂ)) v‖
      = ∫ v in K, ‖iteratedFDeriv ℝ j (fun x => (g x : ℂ)) v‖ :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
  rw [heq]
  have hCbound : ∀ x ∈ K, ‖‖iteratedFDeriv ℝ j (fun y => (g y : ℂ)) x‖‖ ≤ (1 : ℝ) := by
    intro x _
    rw [Real.norm_of_nonneg (norm_nonneg _), iteratedFDeriv_ofReal_norm hg j x]
    exact hbd x
  have hnorm_le := norm_setIntegral_le_of_norm_le_const (f := fun v =>
    ‖iteratedFDeriv ℝ j (fun x => (g x : ℂ)) v‖) (μ := volume)
    (hK.measure_lt_top : volume K < ⊤) hCbound
  calc ∫ v in K, ‖iteratedFDeriv ℝ j (fun x => (g x : ℂ)) v‖
      ≤ ‖∫ v in K, ‖iteratedFDeriv ℝ j (fun x => (g x : ℂ)) v‖‖ := by
        rw [Real.norm_eq_abs]; exact le_abs_self _
    _ ≤ 1 * (volume K).toReal := hnorm_le
    _ = (volume K).toReal := one_mul _

/-- The finite sum of `L¹` derivative norms appearing in Mathlib's Fourier-decay bound is
controlled by `(m+1) * volume K`. -/
private theorem sum_bound {d : ℕ} {K : Set (Space d)} (hK : IsCompact K)
    {g : Space d → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hsupp : tsupport g ⊆ K) (m : ℕ)
    (hbd : ∀ k ≤ m, ∀ x : Space d, ‖iteratedFDeriv ℝ k g x‖ ≤ 1) :
    ∑ p ∈ Finset.range 1 ×ˢ Finset.range (m + 1),
        ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 (fun x => (g x : ℂ)) v‖
      ≤ (↑(m + 1) : ℝ) * (volume K).toReal := by
  have hstep : ∑ p ∈ Finset.range 1 ×ˢ Finset.range (m + 1),
      ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 (fun x => (g x : ℂ)) v‖
      = ∑ j ∈ Finset.range (m + 1),
          ∫ v, ‖iteratedFDeriv ℝ j (fun x => (g x : ℂ)) v‖ := by
    rw [Finset.sum_product, Finset.sum_range_one]
    simp only [pow_zero, one_mul]
  rw [hstep]
  calc ∑ j ∈ Finset.range (m + 1), ∫ v, ‖iteratedFDeriv ℝ j (fun x => (g x : ℂ)) v‖
      ≤ ∑ _j ∈ Finset.range (m + 1), (volume K).toReal :=
        Finset.sum_le_sum (fun j hj =>
          term_bound (j := j) hK hg hsupp
            (fun x => hbd j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) x))
    _ = (↑(m + 1) : ℝ) * (volume K).toReal := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Mathlib's Fourier-decay bound, specialised to `k = 0` (no derivative on the Fourier side)
and reduced, via `sum_bound`, to an explicit bound depending only on `m` and `volume K`. -/
private theorem fourier_decay_gen {d : ℕ} {K : Set (Space d)} (hK : IsCompact K)
    {g : Space d → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hsupp : tsupport g ⊆ K)
    (m : ℕ) (hbd : ∀ k ≤ m, ∀ x : Space d, ‖iteratedFDeriv ℝ k g x‖ ≤ 1) (ξ : Space d) :
    ‖ξ‖ ^ m * ‖𝓕 (fun x => (g x : ℂ)) ξ‖ ≤ (2 : ℝ) ^ m * (↑(m + 1) : ℝ) * (volume K).toReal := by
  have hgc : ContDiff ℝ (⊤ : ℕ∞) (fun x => (g x : ℂ)) := contDiff_ofReal hg
  have hint : ∀ (k n : ℕ), k ≤ (0 : ℕ∞) → n ≤ (⊤ : ℕ∞) →
      Integrable (fun v => ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => (g x : ℂ)) v‖) := by
    intro k n hk _
    have hk0 : k = 0 := Nat.le_zero.mp (by exact_mod_cast hk)
    subst hk0
    simpa using iteratedFDeriv_integrable hK hg hsupp n
  have hmain : ‖ξ‖ ^ m * ‖iteratedFDeriv ℝ 0 (𝓕 (fun x => (g x : ℂ))) ξ‖ ≤
      (2 * Real.pi) ^ (0 : ℕ) * (2 * (0 : ℕ) + 2) ^ m *
        ∑ p ∈ Finset.range (0 + 1) ×ˢ Finset.range (m + 1),
          ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 (fun x => (g x : ℂ)) v‖ :=
    Real.pow_mul_norm_iteratedFDeriv_fourier_le (K := (0 : ℕ∞)) (N := (⊤ : ℕ∞)) (k := 0) (n := m)
      hgc hint (le_refl (0 : ℕ∞)) le_top ξ
  rw [norm_iteratedFDeriv_zero] at hmain
  refine hmain.trans ?_
  have hsum := sum_bound hK hg hsupp m hbd
  have hconst : (2 * Real.pi : ℝ) ^ (0 : ℕ) * (2 * (0 : ℕ) + 2) ^ m = (2 : ℝ) ^ m := by norm_num
  rw [hconst]
  calc (2 : ℝ) ^ m * (∑ p ∈ Finset.range (0 + 1) ×ˢ Finset.range (m + 1),
        ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 (fun x => (g x : ℂ)) v‖)
      ≤ (2 : ℝ) ^ m * ((↑(m + 1) : ℝ) * (volume K).toReal) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (2 : ℝ) ^ m * (↑(m + 1) : ℝ) * (volume K).toReal := by ring

/-- Combining the Fourier-decay bound at derivative order `0` and at order `m` gives an explicit
polynomial decay bound `‖𝓕 g ξ‖ ≲ (1 + ‖ξ‖)^{-m}`, uniform over `g`. -/
private theorem fourier_decay {d : ℕ} {K : Set (Space d)} (hK : IsCompact K)
    {g : Space d → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hsupp : tsupport g ⊆ K)
    (m : ℕ) (hbd : ∀ k ≤ m, ∀ x : Space d, ‖iteratedFDeriv ℝ k g x‖ ≤ 1) (ξ : Space d) :
    ‖𝓕 (fun x => (g x : ℂ)) ξ‖ ≤
      ((2 : ℝ) ^ m * (volume K).toReal
        + (2 : ℝ) ^ m * ((2 : ℝ) ^ m * (↑(m + 1) : ℝ) * (volume K).toReal)) / (1 + ‖ξ‖) ^ m := by
  have hbd0 : ∀ k ≤ 0, ∀ x : Space d, ‖iteratedFDeriv ℝ k g x‖ ≤ 1 := fun k hk x => by
    have hk0 : k = 0 := Nat.le_zero.mp hk
    subst hk0; exact hbd 0 (Nat.zero_le m) x
  have hA0 := fourier_decay_gen hK hg hsupp 0 hbd0 ξ
  have hAm := fourier_decay_gen hK hg hsupp m hbd ξ
  simp only [pow_zero, one_mul, Nat.cast_one, zero_add] at hA0
  have hpos : (0 : ℝ) < (1 + ‖ξ‖) ^ m := by positivity
  rw [le_div_iff₀ hpos, mul_comm]
  rcases le_total ‖ξ‖ 1 with hcase | hcase
  · have h1 : (1 + ‖ξ‖) ^ m ≤ (2 : ℝ) ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
    have h4 : (1 + ‖ξ‖) ^ m * ‖𝓕 (fun x => (g x : ℂ)) ξ‖ ≤ (2 : ℝ) ^ m * (volume K).toReal := by
      calc (1 + ‖ξ‖) ^ m * ‖𝓕 (fun x => (g x : ℂ)) ξ‖
          ≤ (2 : ℝ) ^ m * ‖𝓕 (fun x => (g x : ℂ)) ξ‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ ≤ (2 : ℝ) ^ m * (volume K).toReal := mul_le_mul_of_nonneg_left hA0 (by positivity)
    exact h4.trans (le_add_of_nonneg_right (by positivity))
  · have h1 : (1 + ‖ξ‖) ≤ 2 * ‖ξ‖ := by linarith
    have h2 : (1 + ‖ξ‖) ^ m ≤ (2 * ‖ξ‖) ^ m := pow_le_pow_left₀ (by positivity) h1 m
    have h4 : (1 + ‖ξ‖) ^ m * ‖𝓕 (fun x => (g x : ℂ)) ξ‖ ≤
        (2 : ℝ) ^ m * ((2 : ℝ) ^ m * (↑(m + 1) : ℝ) * (volume K).toReal) := by
      calc (1 + ‖ξ‖) ^ m * ‖𝓕 (fun x => (g x : ℂ)) ξ‖
          ≤ (2 * ‖ξ‖) ^ m * ‖𝓕 (fun x => (g x : ℂ)) ξ‖ :=
            mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
        _ = (2 : ℝ) ^ m * (‖ξ‖ ^ m * ‖𝓕 (fun x => (g x : ℂ)) ξ‖) := by rw [mul_pow]; ring
        _ ≤ (2 : ℝ) ^ m * ((2 : ℝ) ^ m * (↑(m + 1) : ℝ) * (volume K).toReal) :=
            mul_le_mul_of_nonneg_left hAm (by positivity)
    exact h4.trans (le_add_of_nonneg_left (by positivity))

/-- The full pointwise bound on the `H^{s₀}` integrand: combining the weight comparison
(`weight_rpow_le`) with the Fourier decay (`fourier_decay`) yields, for any `C` witnessing
the former, an explicit bound of the shape `D * (1+‖ξ‖)^{2s₀-2m}` with `D` depending only on
`C`, `m` and `volume K` (not on `g`). -/
private theorem integrand_bound {d : ℕ} {K : Set (Space d)} (hK : IsCompact K)
    {g : Space d → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hsupp : tsupport g ⊆ K)
    {s₀ : ℝ} (m : ℕ) (hbd : ∀ k ≤ m, ∀ x : Space d, ‖iteratedFDeriv ℝ k g x‖ ≤ 1)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ t : ℝ, 0 ≤ t → (1 + (2 * Real.pi * t) ^ 2) ^ s₀ ≤ C * (1 + t) ^ (2 * s₀))
    (ξ : Space d) :
    (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s₀ * ‖𝓕 (fun x => (g x : ℂ)) ξ‖ ^ 2 ≤
      C * ((2 : ℝ) ^ m * (volume K).toReal
        + (2 : ℝ) ^ m * ((2 : ℝ) ^ m * (↑(m + 1) : ℝ) * (volume K).toReal)) ^ 2
        * (1 + ‖ξ‖) ^ (2 * s₀ - 2 * (m : ℝ)) := by
  set B : ℝ := (2 : ℝ) ^ m * (volume K).toReal
      + (2 : ℝ) ^ m * ((2 : ℝ) ^ m * (↑(m + 1) : ℝ) * (volume K).toReal) with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  set t : ℝ := ‖ξ‖ with ht
  have ht0 : (0 : ℝ) ≤ t := norm_nonneg _
  have hbase : (0 : ℝ) < 1 + t := by positivity
  have hw : (1 + (2 * Real.pi * t) ^ 2) ^ s₀ ≤ C * (1 + t) ^ (2 * s₀) := hC t ht0
  have hd : ‖𝓕 (fun x => (g x : ℂ)) ξ‖ ≤ B / (1 + t) ^ m := fourier_decay hK hg hsupp m hbd ξ
  have hd2 : ‖𝓕 (fun x => (g x : ℂ)) ξ‖ ^ 2 ≤ (B / (1 + t) ^ m) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hd 2
  have hrw : (B / (1 + t) ^ m) ^ 2 = B ^ 2 * (1 + t) ^ (-(2 * (m : ℝ))) := by
    rw [div_pow, div_eq_mul_inv, ← pow_mul]
    congr 1
    rw [← Real.rpow_natCast (1 + t) (m * 2), ← Real.rpow_neg hbase.le]
    congr 1
    push_cast; ring
  rw [hrw] at hd2
  calc (1 + (2 * Real.pi * t) ^ 2) ^ s₀ * ‖𝓕 (fun x => (g x : ℂ)) ξ‖ ^ 2
      ≤ (C * (1 + t) ^ (2 * s₀)) * (B ^ 2 * (1 + t) ^ (-(2 * (m : ℝ)))) :=
        mul_le_mul hw hd2 (sq_nonneg _) (by positivity)
    _ = C * B ^ 2 * ((1 + t) ^ (2 * s₀) * (1 + t) ^ (-(2 * (m : ℝ)))) := by ring
    _ = C * B ^ 2 * (1 + t) ^ (2 * s₀ - 2 * (m : ℝ)) := by
        rw [show (2 * s₀ - 2 * (m : ℝ)) = 2 * s₀ + -(2 * (m : ℝ)) from by ring,
          Real.rpow_add hbase]

/-- Finitely many uniform derivative bounds on a fixed compact support control any prescribed Sobolev energy. -/
theorem rkResidual_holds :
  ∀ (d : ℕ) (K : Set (Space d)), IsCompact K → ∀ s₀ : ℝ,
    ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ g : Space d → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → tsupport g ⊆ K →
        (∀ k ≤ m, ∀ x : Space d, ‖iteratedFDeriv ℝ k g x‖ ≤ 1) →
          sobolevNormSq d s₀ g ≤ ENNReal.ofReal C := by
  intro d K hK s₀
  obtain ⟨C, hC0, hC⟩ := weight_rpow_le s₀
  set m : ℕ := d + ⌈s₀⌉₊ + 1 with hmdef
  refine ⟨m, ?_⟩
  set B : ℝ := (2 : ℝ) ^ m * (volume K).toReal
      + (2 : ℝ) ^ m * ((2 : ℝ) ^ m * (↑(m + 1) : ℝ) * (volume K).toReal) with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  set D : ℝ := C * B ^ 2 with hDdef
  have hD0 : 0 ≤ D := by rw [hDdef]; positivity
  set r : ℝ := 2 * (m : ℝ) - 2 * s₀ with hrdef
  have hdr : (d : ℝ) < r := by
    have hceil : s₀ ≤ (⌈s₀⌉₊ : ℝ) := Nat.le_ceil s₀
    have hmeq : (m : ℝ) = (d : ℝ) + (⌈s₀⌉₊ : ℝ) + 1 := by rw [hmdef]; push_cast; ring
    rw [hrdef, hmeq]; linarith
  have hfr : (Module.finrank ℝ (Space d) : ℝ) = (d : ℝ) := by
    rw [finrank_euclideanSpace_fin]
  have hbase : (∫⁻ ξ : Space d, ENNReal.ofReal ((1 + ‖ξ‖) ^ (-r))) < ⊤ :=
    finite_integral_one_add_norm (E := Space d) (μ := volume) (r := r) (by rw [hfr]; exact hdr)
  have hfin : (∫⁻ ξ : Space d, ENNReal.ofReal (D * (1 + ‖ξ‖) ^ (-r))) < ⊤ := by
    have heq2 : (∫⁻ ξ : Space d, ENNReal.ofReal (D * (1 + ‖ξ‖) ^ (-r)))
        = ENNReal.ofReal D * ∫⁻ ξ : Space d, ENNReal.ofReal ((1 + ‖ξ‖) ^ (-r)) := by
      simp_rw [ENNReal.ofReal_mul hD0]
      exact MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    rw [heq2]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hbase
  refine ⟨(∫⁻ ξ : Space d, ENNReal.ofReal (D * (1 + ‖ξ‖) ^ (-r))).toReal,
    ENNReal.toReal_nonneg, fun g hg hsupp hbd => ?_⟩
  have hgoal : sobolevNormSq d s₀ g ≤ ∫⁻ ξ : Space d, ENNReal.ofReal (D * (1 + ‖ξ‖) ^ (-r)) := by
    unfold sobolevNormSq
    apply MeasureTheory.lintegral_mono
    intro ξ
    apply ENNReal.ofReal_le_ofReal
    have hpt := integrand_bound hK hg hsupp m hbd hC0 hC ξ
    rw [show (2 * s₀ - 2 * (m : ℝ)) = -r from by rw [hrdef]; ring] at hpt
    rw [hDdef]
    exact hpt
  exact hgoal.trans (le_of_eq (ENNReal.ofReal_toReal hfin.ne).symm)

end Critical2DKPZ.Analysis.Sobolev.Rellich

end
