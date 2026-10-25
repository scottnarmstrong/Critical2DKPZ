/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Collision.RenewalStringUniformCell
import Mathlib.Tactic

/-!
# Absolute renewal-string pair-box comparisons

These bounds handle the finitely many scales where the critical coupling may
have either sign.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Critical2DKPZ.Collision

/-- The product of absolute normalized renewal masses is bounded by the product
of their pair-cell density integrals. -/
theorem renewalStringPairBox_absMassProd_le (N m : ℕ)
    (a b : Fin (m + 1) → ℕ) (ϑ c : ℝ) (hN : 0 < N) (hc : 0 < c)
    (hcell : ∀ j : Fin (m + 1),
      ENNReal.ofReal (c / (N : ℝ) *
        |criticalSigmaSq ϑ N * Renewal.criticalRenewalMass ϑ N (b j - a j)|) ≤
        ∫⁻ p in renewalStringPairCell N (a j) (b j),
          ENNReal.ofReal (DeltaBose.scalarDensity
            (ϑ - Real.eulerMascheroniConstant) (p.2 - p.1))) :
    ENNReal.ofReal ((c / (N : ℝ)) ^ (m + 1) *
      ∏ j : Fin (m + 1),
        |criticalSigmaSq ϑ N * Renewal.criticalRenewalMass ϑ N (b j - a j)|) ≤
      ∏ j : Fin (m + 1), ∫⁻ p in renewalStringPairCell N (a j) (b j),
        ENNReal.ofReal (DeltaBose.scalarDensity
          (ϑ - Real.eulerMascheroniConstant) (p.2 - p.1)) := by
  let k : ℝ := c / (N : ℝ)
  let x : Fin (m + 1) → ℝ := fun j =>
    |criticalSigmaSq ϑ N * Renewal.criticalRenewalMass ϑ N (b j - a j)|
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hk : 0 < k := by dsimp [k]; exact div_pos hc hN'
  have hx : ∀ j, 0 ≤ x j := fun j => abs_nonneg _
  have hprodReal : (∏ j : Fin (m + 1), k * x j) =
      k ^ (m + 1) * ∏ j : Fin (m + 1), x j := by
    rw [Finset.prod_mul_distrib, Fin.prod_const]
  have hprodENN : ENNReal.ofReal (k ^ (m + 1) * ∏ j : Fin (m + 1), x j) =
      ∏ j : Fin (m + 1), ENNReal.ofReal (k * x j) := by
    calc
      ENNReal.ofReal (k ^ (m + 1) * ∏ j : Fin (m + 1), x j) =
          ENNReal.ofReal (∏ j : Fin (m + 1), k * x j) := by rw [hprodReal]
      _ = ∏ j : Fin (m + 1), ENNReal.ofReal (k * x j) :=
        ENNReal.ofReal_prod_of_nonneg (fun j hj => mul_nonneg hk.le (hx j))
  calc
    ENNReal.ofReal (k ^ (m + 1) * ∏ j : Fin (m + 1), x j) =
        ∏ j : Fin (m + 1), ENNReal.ofReal (k * x j) := hprodENN
    _ ≤ ∏ j : Fin (m + 1), ∫⁻ p in renewalStringPairCell N (a j) (b j),
        ENNReal.ofReal (DeltaBose.scalarDensity
          (ϑ - Real.eulerMascheroniConstant) (p.2 - p.1)) := by
      apply Finset.prod_le_prod₀
      · intro j hj
        exact zero_le
      · intro j hj
        simpa [k, x] using hcell j

/-- A renewal-string summand, with no sign restriction on the coupling, is
bounded by the continuum integrand over its pair-box. -/
theorem renewalStringPairBox_absTerm_le (N m : ℕ)
    (lo hi a b : Fin (m + 1) → ℕ) (ϑ c : ℝ)
    (hN : 0 < N) (hc : 0 < c)
    (hlo : ∀ j, lo j < a j) (hhi : ∀ j, b j ≤ hi j)
    (hsep : ∀ j : Fin m, hi j.castSucc ≤ lo j.succ)
    (hab : ∀ j, a j ≤ b j) (_hbN : ∀ j, b j ≤ N)
    (hcell : ∀ j : Fin (m + 1),
      ENNReal.ofReal (c / (N : ℝ) *
        |criticalSigmaSq ϑ N * Renewal.criticalRenewalMass ϑ N (b j - a j)|) ≤
        ∫⁻ p in renewalStringPairCell N (a j) (b j),
          ENNReal.ofReal (DeltaBose.scalarDensity
            (ϑ - Real.eulerMascheroniConstant) (p.2 - p.1))) :
    ENNReal.ofReal ((a 0 : ℝ)⁻¹ *
      (∏ j : Fin (m + 1), criticalSigmaSq ϑ N *
        Renewal.criticalRenewalMass ϑ N (b j - a j)) *
      ∏ j : Fin m, (b j.castSucc : ℝ) /
        ((a j.succ : ℝ) * ((a j.succ : ℝ) - b j.castSucc))) ≤
      ENNReal.ofReal ((4 * (1 + c⁻¹)) ^ (m + 1)) *
        ∫⁻ p in renewalStringPairBox N m a b,
          ENNReal.ofReal ((renewalStringPairBoxRational m p) *
            renewalStringPairBoxDensity (ϑ - Real.eulerMascheroniConstant) m p) := by
  let Q : ℝ := (1 / (N : ℝ)) * (4 / (N : ℝ)) ^ m
  let k : ℝ := c / (N : ℝ)
  let C : ℝ := 4 * (1 + c⁻¹)
  let r : ℝ := (a 0 : ℝ)⁻¹ *
      ∏ j : Fin m, (b j.castSucc : ℝ) /
        ((a j.succ : ℝ) * ((a j.succ : ℝ) - b j.castSucc))
  let x : Fin (m + 1) → ℝ := fun j =>
    criticalSigmaSq ϑ N * Renewal.criticalRenewalMass ϑ N (b j - a j)
  let X : ℝ := ∏ j : Fin (m + 1), |x j|
  let R₀ : ℝ := r / Q
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hk : 0 < k := by dsimp [k]; exact div_pos hc hN'
  have hkpow : 0 < k ^ (m + 1) := pow_pos hk _
  have hfirst : 1 ≤ a 0 := by
    exact Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) (hlo 0))
  have hr : 0 ≤ r := by
    dsimp [r]
    have hfirstpos : 0 < (a 0 : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hfirst)
    have hfactor : ∀ j : Fin m, 0 ≤
        (b j.castSucc : ℝ) /
          ((a j.succ : ℝ) * ((a j.succ : ℝ) - b j.castSucc)) := by
      intro j
      have hgap : b j.castSucc < a j.succ := by
        exact lt_of_le_of_lt (hhi j.castSucc) (lt_of_le_of_lt (hsep j) (hlo j.succ))
      have hbpos : 0 ≤ (b j.castSucc : ℝ) := by positivity
      have hapos : 0 < (a j.succ : ℝ) := by
        exact_mod_cast (Nat.zero_lt_of_lt (by omega : 0 < a j.succ))
      have hdiff : 0 < (a j.succ : ℝ) - b j.castSucc := by
        have hcast : (b j.castSucc : ℝ) + 1 ≤ a j.succ := by
          exact_mod_cast (Nat.succ_le_of_lt hgap)
        linarith
      exact div_nonneg hbpos (mul_nonneg hapos.le hdiff.le)
    exact mul_nonneg (inv_nonneg.mpr hfirstpos.le)
      (Finset.prod_nonneg fun j hj => hfactor j)
  have hR₀ : 0 ≤ R₀ := div_nonneg hr hQ.le
  have hR : ∀ p ∈ renewalStringPairBox N m a b,
      R₀ ≤ renewalStringPairBoxRational m p := by
    intro p hp
    have hrat := renewalStringPairBox_rational_le N m lo hi a b hN hlo hhi hsep hab hp
    have hrat' : r ≤ Q * renewalStringPairBoxRational m p := by
      simpa [r, Q, renewalStringPairBoxRational, mul_assoc] using hrat
    exact (div_le_iff₀ hQ).2 (by simpa [R₀, mul_comm] using hrat')
  have hMassProd := renewalStringPairBox_absMassProd_le N m a b ϑ c hN hc hcell
  have hRationalIntegral := lintegral_renewalStringPairBox_rational_density_lower
    N m a b (ϑ - Real.eulerMascheroniConstant) R₀ hN hR₀ hab hR
  have hchain : ENNReal.ofReal R₀ * ENNReal.ofReal (k ^ (m + 1) * X) ≤
      ∫⁻ p in renewalStringPairBox N m a b,
        ENNReal.ofReal (renewalStringPairBoxRational m p *
          renewalStringPairBoxDensity (ϑ - Real.eulerMascheroniConstant) m p) := by
    calc
      _ ≤ ENNReal.ofReal R₀ *
          ∏ j : Fin (m + 1), ∫⁻ q in renewalStringPairCell N (a j) (b j),
            ENNReal.ofReal (DeltaBose.scalarDensity
              (ϑ - Real.eulerMascheroniConstant) (q.2 - q.1)) :=
        mul_le_mul_of_nonneg_left (by simpa [k, x, X] using hMassProd) zero_le
      _ ≤ _ := hRationalIntegral
  have hcoeffDecomp : Q / k ^ (m + 1) = (4 / c) ^ m * (1 / c) := by
    calc
      Q / k ^ (m + 1) = 4 ^ m / c ^ (m + 1) := by
        dsimp [Q, k]
        rw [div_pow, div_pow]
        field_simp [ne_of_gt hN', ne_of_gt hc]
        ring
      _ = (4 / c) ^ m * (1 / c) := by
        rw [div_pow]
        field_simp [ne_of_gt hc]
        ring
  have hC₄ : 4 / c ≤ C := by
    dsimp [C]
    have hinv : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
    rw [div_eq_mul_inv]
    nlinarith
  have hC₁ : 1 / c ≤ C := by
    dsimp [C]
    have hinv : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
    rw [div_eq_mul_inv]
    nlinarith
  have hcoeff : Q / k ^ (m + 1) ≤ C ^ (m + 1) := by
    rw [hcoeffDecomp]
    calc
      (4 / c) ^ m * (1 / c) ≤ C ^ m * C := by
        apply mul_le_mul
        · exact pow_le_pow_left₀ (by positivity) hC₄ _
        · exact hC₁
        · positivity
        · positivity
      _ = C ^ (m + 1) := by rw [pow_succ]
  have hcoeffNonneg : 0 ≤ Q / k ^ (m + 1) := div_nonneg hQ.le hkpow.le
  have hscale : r * X = (Q / k ^ (m + 1)) * (R₀ * (k ^ (m + 1) * X)) := by
    dsimp [R₀]
    field_simp [ne_of_gt hQ, ne_of_gt hkpow]
  have hscaleENN : ENNReal.ofReal (r * X) =
      ENNReal.ofReal (Q / k ^ (m + 1)) *
        (ENNReal.ofReal R₀ * ENNReal.ofReal (k ^ (m + 1) * X)) := by
    calc
      ENNReal.ofReal (r * X) =
          ENNReal.ofReal ((Q / k ^ (m + 1)) *
            (R₀ * (k ^ (m + 1) * X))) := by rw [hscale]
      _ = ENNReal.ofReal (Q / k ^ (m + 1)) *
            ENNReal.ofReal (R₀ * (k ^ (m + 1) * X)) :=
          ENNReal.ofReal_mul hcoeffNonneg
      _ = ENNReal.ofReal (Q / k ^ (m + 1)) *
            (ENNReal.ofReal R₀ * ENNReal.ofReal (k ^ (m + 1) * X)) := by
          rw [ENNReal.ofReal_mul hR₀]
  have hprodAbs : (∏ j : Fin (m + 1), x j) ≤ X := by
    calc
      (∏ j : Fin (m + 1), x j) ≤ |∏ j : Fin (m + 1), x j| := le_abs_self _
      _ = X := by simp [X, Finset.abs_prod]
  have htermReal :
      (a 0 : ℝ)⁻¹ * (∏ j : Fin (m + 1), x j) *
        ∏ j : Fin m, (b j.castSucc : ℝ) /
          ((a j.succ : ℝ) * ((a j.succ : ℝ) - b j.castSucc)) ≤ r * X := by
    calc
      _ = r * (∏ j : Fin (m + 1), x j) := by dsimp [r]; ring
      _ ≤ r * X := mul_le_mul_of_nonneg_left hprodAbs hr
  calc
    _ ≤ ENNReal.ofReal (r * X) := ENNReal.ofReal_le_ofReal htermReal
    _ = ENNReal.ofReal (Q / k ^ (m + 1)) *
          (ENNReal.ofReal R₀ * ENNReal.ofReal (k ^ (m + 1) * X)) := hscaleENN
    _ ≤ ENNReal.ofReal (Q / k ^ (m + 1)) *
          ∫⁻ p in renewalStringPairBox N m a b,
            ENNReal.ofReal (renewalStringPairBoxRational m p *
              renewalStringPairBoxDensity (ϑ - Real.eulerMascheroniConstant) m p) :=
        mul_le_mul_of_nonneg_left hchain zero_le
    _ ≤ ENNReal.ofReal (C ^ (m + 1)) * _ := by
      apply mul_le_mul_of_nonneg_right
      · exact ENNReal.ofReal_le_ofReal hcoeff
      · exact zero_le

end Critical2DKPZ.Collision

end
