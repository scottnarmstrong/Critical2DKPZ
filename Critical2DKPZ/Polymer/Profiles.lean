/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.Endpoints
import Mathlib.Tactic

/-! An arbitrary terminal weight and a finitely supported initial profile define finite sums of polymer path weights. -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Critical2DKPZ.Polymer

/-- The probabilities of all finite walk paths sum to one. -/
theorem sum_walkProbability (n : ℕ) :
    (∑ _s : Fin n → Fin 4, (4 : ℝ)⁻¹ ^ n) = 1 := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [← mul_pow, mul_inv_cancel₀ (by norm_num : (4 : ℝ) ≠ 0), one_pow]

/-- With zero disorder strength, every path weight equals one. -/
@[simp]
theorem pathWeight_zero_beta (a : ℕ) (w : Site) {n : ℕ}
    (s : Fin n → Fin 4) (ω : Disorder) :
    pathWeight 0 a w s ω = 1 := by
  simp only [pathWeight, zero_mul, zero_pow (by decide : 2 ≠ 0),
    zero_div, sub_self, Finset.sum_const_zero, Real.exp_zero]

/-- With zero disorder strength, the point-to-point partition function equals the walk kernel. -/
theorem pointToPoint_zero_beta (a n : ℕ) (w z : Site) (ω : Disorder) :
    pointToPoint 0 a n w z ω = srwKernel n (z - w) := by
  rw [pointToPoint_eq_sum, srwKernel_eq_sum n w z]
  simp only [pathWeight_zero_beta, mul_one]

/-- With zero disorder strength, the point-to-plane partition function equals one. -/
theorem pointToPlane_zero_beta (a n : ℕ) (w : Site) (ω : Disorder) :
    pointToPlane 0 a n w ω = 1 := by
  rw [pointToPlane_eq_sum]
  simp only [pathWeight_zero_beta, mul_one, sum_walkProbability]

/-- The simple-walk transition kernel has total mass one. -/
theorem tsum_srwKernel (n : ℕ) (w : Site) :
    ∑' z, srwKernel n (z - w) = 1 := by
  have h := tsum_pointToPoint 0 0 n w (fun _ => 0)
  simpa only [pointToPoint_zero_beta, pointToPlane_zero_beta] using h

/-- Summing the walk kernel over reachable endpoints gives one. -/
theorem sum_srwKernel_endpoints (n : ℕ) (w : Site) :
    ∑ z ∈ endpoints w n, srwKernel n (z - w) = 1 := by
  rw [← tsum_srwKernel n w]
  symm
  exact tsum_eq_sum fun z hz => srwKernel_eq_zero_of_not_mem n w z hz

/-- The random-walk kernel is nonnegative. -/
theorem kernel_nonneg (n : ℕ) (z : Site) : 0 ≤ srwKernel n z := by
  unfold srwKernel
  exact Finset.sum_nonneg fun _ _ => mul_nonneg (by positivity)
    (by split_ifs <;> positivity)

/-- The smoothed point-to-plane partition function is strictly positive. -/
theorem smoothedP2Plane_pos (β : ℝ) (s n : ℕ) (x : Site) (ω : Disorder) :
    0 < smoothedP2Plane β s n x ω := by
  have hex : ∃ y ∈ endpoints x s, 0 < srwKernel s (y - x) := by
    apply (Finset.sum_pos_iff_of_nonneg (fun y _ => kernel_nonneg s (y - x))).1
    rw [sum_srwKernel_endpoints]
    exact zero_lt_one
  obtain ⟨y, hy, hq⟩ := hex
  rw [smoothedP2Plane_eq_sum]
  exact lt_of_lt_of_le (mul_pos hq (pointToPlane_pos β s (n - s) y ω))
    (Finset.single_le_sum
      (fun z _ => mul_nonneg (kernel_nonneg s (z - x))
        (pointToPlane_pos β s (n - s) z ω).le) hy)

/-- The smoothed point-to-plane partition function has expectation one. -/
theorem integral_smoothedP2Plane (β : ℝ) (s n : ℕ) (x : Site) :
    ∫ ω, smoothedP2Plane β s n x ω ∂disorderLaw = 1 := by
  have heq : smoothedP2Plane β s n x =
      fun ω => ∑ y ∈ endpoints x s, srwKernel s (y - x) *
        pointToPlane β s (n - s) y ω := by
    funext ω
    exact smoothedP2Plane_eq_sum β s n x ω
  rw [heq, integral_finsetSum _ fun y _ =>
    (integrable_pointToPlane β s (n - s) y).const_mul _]
  simp only [integral_const_mul, integral_pointToPlane, mul_one]
  exact sum_srwKernel_endpoints s x

/-- The profile-tested partition function is measurable. -/
theorem measurable_profileP2Fun (β : ℝ) (a b : ℕ) (ν f : Site → ℝ) :
    Measurable (profileP2Fun β a b ν f) := by
  unfold profileP2Fun
  exact Measurable.tsum fun w => measurable_const.mul
    (Measurable.tsum fun z => (measurable_pointToPoint β a (b - a) w z).mul_const _)

/-- A terminal-profile partition function has finite Lᵖ norm. -/
theorem memLp_terminalProfile (β : ℝ) (a n : ℕ) (w : Site) (f : Site → ℝ)
    (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun ω => ∑' z, pointToPoint β a n w z ω * f z) p disorderLaw := by
  simp_rw [tsum_pointToPoint_mul]
  exact memLp_finsetSum _ fun s _ =>
    ((memLp_pathWeight β a w s p hp).const_mul _).mul_const _

/-- The mean terminal-profile partition function is the heat average of its terminal profile. -/
theorem integral_terminalProfile (β : ℝ) (a n : ℕ) (w : Site) (f : Site → ℝ) :
    ∫ ω, (∑' z, pointToPoint β a n w z ω * f z) ∂disorderLaw =
      ∑' z, srwKernel n (z - w) * f z := by
  simp_rw [tsum_pointToPoint_mul]
  rw [integral_finsetSum _ fun s _ =>
    ((integrable_pathWeight β a w s).const_mul _).mul_const _]
  simp only [integral_mul_const, integral_const_mul, integral_pathWeight, mul_one]
  have h := tsum_pointToPoint_mul 0 a n w f (fun _ => 0)
  simpa only [pointToPoint_zero_beta, pathWeight_zero_beta, mul_one] using h.symm

/-- An initial profile with finite support gives a finite weighted sum of terminal-profile partition functions. -/
theorem profileP2Fun_eq_sum (β : ℝ) (a b : ℕ) (ν f : Site → ℝ)
    (t : Finset Site) (hν : ∀ w ∉ t, ν w = 0) (ω : Disorder) :
    profileP2Fun β a b ν f ω =
      ∑ w ∈ t, ν w * ∑' z, pointToPoint β a (b - a) w z ω * f z := by
  unfold profileP2Fun
  exact tsum_eq_sum fun w hw => by rw [hν w hw, zero_mul]

/-- A finitely supported profile pairing has finite Lᵖ norm. -/
theorem memLp_profileP2Fun_finset (β : ℝ) (a b : ℕ) (ν f : Site → ℝ)
    (t : Finset Site) (hν : ∀ w ∉ t, ν w = 0) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (profileP2Fun β a b ν f) p disorderLaw := by
  have heq : profileP2Fun β a b ν f = fun ω =>
      ∑ w ∈ t, ν w * ∑' z, pointToPoint β a (b - a) w z ω * f z := by
    funext ω
    exact profileP2Fun_eq_sum β a b ν f t hν ω
  rw [heq]
  exact memLp_finsetSum _ fun w _ =>
    (memLp_terminalProfile β a (b - a) w f p hp).const_mul _

/-- The mean finite-profile pairing equals the corresponding walk-kernel pairing. -/
theorem integral_profileP2Fun_finset (β : ℝ) (a b : ℕ) (ν f : Site → ℝ)
    (t : Finset Site) (hν : ∀ w ∉ t, ν w = 0) :
    ∫ ω, profileP2Fun β a b ν f ω ∂disorderLaw =
      ∑ w ∈ t, ν w * ∑' z, srwKernel (b - a) (z - w) * f z := by
  have heq : profileP2Fun β a b ν f = fun ω =>
      ∑ w ∈ t, ν w * ∑' z, pointToPoint β a (b - a) w z ω * f z := by
    funext ω
    exact profileP2Fun_eq_sum β a b ν f t hν ω
  rw [heq, integral_finsetSum _ fun w _ =>
    (memLp_one_iff_integrable.mp
      (memLp_terminalProfile β a (b - a) w f 1 (by simp))).const_mul _]
  simp_rw [integral_const_mul, integral_terminalProfile]

end Critical2DKPZ.Polymer
