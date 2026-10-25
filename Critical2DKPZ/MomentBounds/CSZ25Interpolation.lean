/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25FiniteOperators
import Mathlib.Analysis.MeanInequalities

/-! # The weighted finite interpolation bound of CSZ25 Lemma 5.8 -/

@[expose] public noncomputable section

namespace Critical2DKPZ.MomentBounds

/-- Hölder-conjugate exponents with `q > 2` interpolate the weighted finite norm through its quadratic norm. -/
theorem finiteLpNorm_mul_le_interpolation {α : Type*} (s : Finset α) {p q : ℝ}
    (hpq : p.HolderConjugate q) (hq : 2 < q) (f g : α → ℝ) (hg : ∀ x, 0 ≤ g x) :
    finiteLpNorm s p (fun x => f x * g x) ≤
      (∑ x ∈ s, |f x| * g x ^ (q / (q - 2))) ^ (1 - 2 / q) * finiteLpNorm s 2 f ^ (2 / q) := by
  let a := 1 - 2 / q
  let b := 2 / q
  let r := q / (q - 2)
  have hq0 : 0 < q := lt_trans (by norm_num) hq
  have hq2 : 0 < q - 2 := sub_pos.2 hq
  have ha : 0 < a := sub_pos.2 ((div_lt_one hq0).2 hq)
  have hb : 0 < b := div_pos (by norm_num) hq0
  have hr : 0 < r := div_pos hq0 hq2
  have har : a * r = 1 := by dsimp [a, r]; field_simp
  have hbq : b * q = 2 := by dsimp [b]; field_simp
  have hab : a + b = 1 := by dsimp [a, b]; ring
  have htr : r.HolderTriple q p := by
    constructor
    · have h := hpq.inv_add_inv_eq_one
      have he : r⁻¹ + q⁻¹ = 1 - q⁻¹ := by dsimp [r]; field_simp; ring
      linarith only [he, h]
    · exact hr
    · exact hq0
  let F : α → ℝ := fun x => |f x| ^ a * g x
  let G : α → ℝ := fun x => |f x| ^ b
  have hF : ∀ x, 0 ≤ F x := fun x => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (hg x)
  have hG : ∀ x, 0 ≤ G x := fun x => Real.rpow_nonneg (abs_nonneg _) _
  have hFG (x : α) : F x * G x = |f x * g x| := by
    dsimp [F, G]
    rw [abs_mul, abs_of_nonneg (hg x)]
    calc
      _ = (|f x| ^ a * |f x| ^ b) * g x := by ring
      _ = _ := by rw [← Real.rpow_add_of_nonneg (abs_nonneg _) ha.le hb.le, hab, Real.rpow_one]
  have hFr (x : α) : F x ^ r = |f x| * g x ^ r := by
    dsimp [F]
    rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg _) _) (hg x),
      ← Real.rpow_mul (abs_nonneg _), har, Real.rpow_one]
  have hGq (x : α) : G x ^ q = |f x| ^ (2 : ℝ) := by
    dsimp [G]
    rw [← Real.rpow_mul (abs_nonneg _), hbq]
  let U := ∑ x ∈ s, |f x| * g x ^ r
  let V := ∑ x ∈ s, |f x| ^ (2 : ℝ)
  have hU : 0 ≤ U := Finset.sum_nonneg fun x _ => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (hg x) _)
  have hV : 0 ≤ V := Finset.sum_nonneg fun x _ => Real.rpow_nonneg (abs_nonneg _) _
  have h := Real.Lr_rpow_le_Lp_mul_Lq_of_nonneg s htr (fun x _ => hF x) (fun x _ => hG x)
  simp only [hFG, hFr, hGq] at h
  change (∑ x ∈ s, |f x * g x| ^ p) ≤ U ^ (p / r) * V ^ (p / q) at h
  have hroot := Real.rpow_le_rpow (Finset.sum_nonneg (fun x _ => Real.rpow_nonneg (abs_nonneg _) _))
    h (one_div_nonneg.2 hpq.nonneg)
  rw [Real.mul_rpow (Real.rpow_nonneg hU _) (Real.rpow_nonneg hV _),
    ← Real.rpow_mul hU, ← Real.rpow_mul hV] at hroot
  have hpr : p / r * (1 / p) = a := by
    dsimp [r, a]
    field_simp [hpq.ne_zero, hq0.ne', hq2.ne']
  have hpq' : p / q * (1 / p) = 1 / q := by field_simp [hpq.ne_zero]
  rw [hpr, hpq'] at hroot
  change finiteLpNorm s p (fun x => f x * g x) ≤ U ^ a * V ^ (1 / q) at hroot
  have hnorm : finiteLpNorm s 2 f ^ b = V ^ (1 / q) := by
    unfold finiteLpNorm
    rw [← Real.rpow_mul (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (abs_nonneg _) _)]
    have he : (1 / (2 : ℝ)) * b = 1 / q := by dsimp [b]; ring
    rw [he]
  rw [hnorm]
  exact hroot

end Critical2DKPZ.MomentBounds
