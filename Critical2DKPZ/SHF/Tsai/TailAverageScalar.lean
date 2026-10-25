/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Critical2DKPZ.SHF.Tsai.ConjugatedDiagramScalar
import Mathlib.Tactic

/-! # Scalar endpoint estimates for tail-word Laplace averaging -/

@[expose] public section

namespace Critical2DKPZ.SHF.Tsai

/-- The remaining incoming endpoint power is absorbed by half the available
exponential rate, leaving exactly the required negative time power. -/
theorem tail_average_endpoint_le {q rate t : ℝ} (hq : q ≤ 1)
    (hrate : 0 ≤ rate) (ht : 0 < t) :
    let lam := rate / 2 + 1 / t
    Real.exp (lam * (t + 1 / lam)) * (lam * (1 / lam) ^ (1 - q)) ≤
      Real.exp 3 * Real.exp (rate * t) * t ^ (-q) := by
  dsimp only
  let lam := rate / 2 + 1 / t
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have hlt : lam * t = rate * t / 2 + 1 := by
    dsimp [lam]
    field_simp
  have hlt1 : 1 ≤ lam * t := by
    rw [hlt]
    linarith only [mul_nonneg hrate ht.le]
  have hcancel : lam * (1 / lam) ^ (1 - q) = lam ^ q := by
    rw [one_div, ← Real.rpow_neg_eq_inv_rpow]
    calc
      _ = lam ^ (1 : ℝ) * lam ^ (-(1 - q)) := by rw [Real.rpow_one]
      _ = lam ^ ((1 : ℝ) + -(1 - q)) := (Real.rpow_add hlam _ _).symm
      _ = lam ^ q := by congr 1; ring
  have htime : lam ^ q = (lam * t) ^ q * t ^ (-q) := by
    rw [Real.mul_rpow hlam.le ht.le, mul_assoc, ← Real.rpow_add ht]
    simp only [add_neg_cancel, Real.rpow_zero, mul_one]
  have hpow : (lam * t) ^ q ≤ Real.exp (lam * t) := by
    refine (Real.rpow_le_self_of_one_le hlt1 hq).trans ?_
    have h := Real.add_one_le_exp (lam * t)
    linarith only [h]
  have hexponent : lam * (t + 1 / lam) + lam * t = rate * t + 3 := by
    rw [mul_add, mul_one_div_cancel hlam.ne', hlt]
    ring
  change Real.exp (lam * (t + 1 / lam)) * (lam * (1 / lam) ^ (1 - q)) ≤ _
  rw [hcancel, htime]
  calc
    _ ≤ Real.exp (lam * (t + 1 / lam)) * (Real.exp (lam * t) * t ^ (-q)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg ht.le _)) (Real.exp_pos _).le
    _ = Real.exp 3 * Real.exp (rate * t) * t ^ (-q) := by
      rw [← mul_assoc, ← Real.exp_add, hexponent, Real.exp_add]
      ring

/-- Logarithmic collision gains remain uniform when the Laplace damping
uses half the prescribed exponential rate. -/
theorem tail_collision_log_rate_bounds {θ c rate lam : ℝ}
    (hc : 2 * Real.exp (2 * max θ 0 + 2) ≤ c)
    (hrate : c + 3 ≤ rate) (hlam : rate / 2 ≤ lam) :
    0 < lam ∧ 0 < Real.log (rate - c - 1) ∧
      1 ≤ Real.log lam - θ ∧ Real.log (rate - c - 1) / 2 ≤ Real.log lam - θ := by
  have hE : 0 < Real.exp (2 * max θ 0 + 2) := Real.exp_pos _
  have hLower : Real.exp (2 * max θ 0 + 2) ≤ lam := by
    linarith only [hc, hrate, hlam]
  have hlam0 : 0 < lam := hE.trans_le hLower
  have hlog : 2 * max θ 0 + 2 ≤ Real.log lam := by
    simpa only [Real.log_exp] using Real.log_le_log hE hLower
  have hArg : 1 < rate - c - 1 := by linarith only [hrate]
  have hL : 0 < Real.log (rate - c - 1) := Real.log_pos hArg
  have hc0 : 0 ≤ c := by linarith only [hc, hE]
  have hArgLe : rate - c - 1 ≤ 2 * lam := by linarith only [hc0, hlam]
  have hComp : Real.log (rate - c - 1) ≤ 2 + Real.log lam := by
    calc
      _ ≤ Real.log (2 * lam) := Real.log_le_log (by linarith only [hArg]) hArgLe
      _ = Real.log 2 + Real.log lam := Real.log_mul (by norm_num) hlam0.ne'
      _ ≤ 2 + Real.log lam := by
        linarith only [Real.log_le_self (x := (2 : ℝ)) (by norm_num)]
  have hθ : θ ≤ max θ 0 := le_max_left _ _
  have hz : 0 ≤ max θ 0 := le_max_right _ _
  refine ⟨hlam0, hL, ?_, ?_⟩
  · linarith only [hlog, hθ, hz]
  · linarith only [hComp, hlog, hθ]

/-- One scalar constant controls every tail word and damping rate. The
logarithmic gain per continuation and the endpoint time power are uniform. -/
theorem exists_scalar_averaged_tail_bound (θ P S J q : ℝ)
    (hP : 0 ≤ P) (hS : 0 ≤ S) (hJ : 0 ≤ J) (hq : q ≤ 1) :
    ∃ c : ℝ, 1 ≤ c ∧ 2 * Real.exp (2 * max θ 0 + 2) ≤ c ∧
      ∀ (m : ℕ) (rate t : ℝ), c + 3 ≤ rate → 0 < t →
        let lam := rate / 2 + 1 / t
        Real.exp (lam * (t + 1 / lam)) * (lam * (1 / lam) ^ (1 - q)) *
          (2 : ℝ) ^ (4 * (2 * m + 2)) * P *
          (J / (Real.log lam - θ)) * (S * J / (Real.log lam - θ)) ^ m ≤
        c ^ (m + 1) * (c / Real.log (rate - c - 1)) ^ m *
          Real.exp (rate * t) * t ^ (-q) := by
  let A : ℝ := P * Real.exp 3 * (2 : ℝ) ^ (3 * 4) * J
  let B : ℝ := (2 : ℝ) ^ (2 * 4 + 1) * S * J
  let c : ℝ := 2 * Real.exp (2 * max θ 0 + 2) + A + B + 3
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hE : 0 < Real.exp (2 * max θ 0 + 2) := Real.exp_pos _
  have hc : 1 ≤ c := by dsimp [c]; linarith only [hA, hB, hE]
  have hcE : 2 * Real.exp (2 * max θ 0 + 2) ≤ c := by
    dsimp [c]; linarith only [hA, hB]
  have hAc : A ≤ c := by dsimp [c]; linarith only [hB, hE]
  have hBc : B ≤ c := by dsimp [c]; linarith only [hA, hE]
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  refine ⟨c, hc, hcE, ?_⟩
  intro m rate t hrate ht
  let lam : ℝ := rate / 2 + 1 / t
  have hrate0 : 0 ≤ rate := by linarith only [hrate, hc]
  have hlam : rate / 2 ≤ lam := le_add_of_nonneg_right (one_div_pos.mpr ht).le
  have hlog := tail_collision_log_rate_bounds hcE hrate hlam
  let L : ℝ := Real.log (rate - c - 1)
  let D : ℝ := Real.log lam - θ
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hlog.2.2.1
  have hTime := tail_average_endpoint_le hq hrate0 ht
  have hK : (2 : ℝ) ^ (4 * (2 * m + 2)) ≤ (2 : ℝ) ^ (4 * (2 * (m + 1) + 1)) := by
    apply pow_le_pow_right₀ (by norm_num)
    omega
  have hPrefix :
      Real.exp (lam * (t + 1 / lam)) * (lam * (1 / lam) ^ (1 - q)) *
          (2 : ℝ) ^ (4 * (2 * m + 2)) * P * (J / D) * (S * J / D) ^ m ≤
        (Real.exp 3 * Real.exp (rate * t) *
          (2 : ℝ) ^ (4 * (2 * (m + 1) + 1)) * P * (J / D) * (S * J / D) ^ m) * t ^ (-q) := by
    have h1 := mul_le_mul hTime hK (by positivity : 0 ≤ (2 : ℝ) ^ (4 * (2 * m + 2)))
      (by positivity : 0 ≤ Real.exp 3 * Real.exp (rate * t) * t ^ (-q))
    have h2 := mul_le_mul_of_nonneg_right h1 hP
    have h3 := mul_le_mul_of_nonneg_right h2 (div_nonneg hJ hD0.le)
    have h4 := mul_le_mul_of_nonneg_right h3 (pow_nonneg (div_nonneg (mul_nonneg hS hJ) hD0.le) m)
    convert h4 using 1; ring
  have hCore := scalar_averaged_diagram_le (n := 4) (m := m)
    hP hS hJ hlog.2.1 hlog.2.2.1 hlog.2.2.2 (le_refl (Real.exp 3 * Real.exp (rate * t)))
  have hSquare : c ≤ c ^ 2 := by
    simpa only [mul_one, pow_two] using mul_le_mul_of_nonneg_left hc hc0
  have hDiv : B / L ≤ c ^ 2 / L := div_le_div_of_nonneg_right (hBc.trans hSquare) hlog.2.1.le
  have hPow := pow_le_pow_left₀ (div_nonneg hB hlog.2.1.le) hDiv m
  have hCap := mul_le_mul hAc hPow (pow_nonneg (div_nonneg hB hlog.2.1.le) m) hc0
  have hPower : c * (c ^ 2 / L) ^ m = c ^ (m + 1) * (c / L) ^ m := by
    rw [show c ^ 2 / L = c * (c / L) by ring, mul_pow, pow_succ]
    ring
  calc
    _ ≤ _ := hPrefix
    _ ≤ (A * (B / L) ^ m * Real.exp (rate * t)) * t ^ (-q) :=
      mul_le_mul_of_nonneg_right hCore (Real.rpow_nonneg ht.le _)
    _ ≤ (c * (c ^ 2 / L) ^ m * Real.exp (rate * t)) * t ^ (-q) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCap (Real.exp_pos _).le) (Real.rpow_nonneg ht.le _)
    _ = _ := by rw [hPower]

end Critical2DKPZ.SHF.Tsai

end
