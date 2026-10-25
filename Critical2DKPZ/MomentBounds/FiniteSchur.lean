/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

/-! # Finite weighted Schur estimate from row and column bounds -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

noncomputable section

private def schurLeftFactor {X Y : Type*} (K : X → Y → ℝ) (A : X → ℝ) (B : Y → ℝ)
    (f : X → ℝ) (p : ℝ) (x : X) (y : Y) : ℝ :=
  |f x| * ((K x y) ^ (1 / p) * (A x / B y))

private def schurRightFactor {X Y : Type*} (K : X → Y → ℝ) (A : X → ℝ) (B : Y → ℝ)
    (g : Y → ℝ) (q : ℝ) (x : X) (y : Y) : ℝ :=
  |g y| * ((K x y) ^ (1 / q) * (B y / A x))

/-- A finite weighted Schur test. The kernel estimates are explicit hypotheses so this
lemma can be reused for concrete kernels without hiding their analytic work. -/
theorem finite_weighted_schur {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (s : Finset X) (t : Finset Y) (K : X → Y → ℝ) (A : X → ℝ) (B : Y → ℝ)
    (f : X → ℝ) (g : Y → ℝ) {p q C D : ℝ} (hpq : p.HolderConjugate q)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hK : ∀ x y, 0 < K x y) (hA : ∀ x, 0 < A x) (hB : ∀ y, 0 < B y)
    (hrow : ∀ x ∈ s, ∑ y ∈ t, K x y * (A x / B y) ^ p ≤ C)
    (hcol : ∀ y ∈ t, ∑ x ∈ s, K x y * (B y / A x) ^ q ≤ D) :
    (∑ x ∈ s, ∑ y ∈ t, |f x| * K x y * |g y|) ≤
      C ^ (1 / p) * D ^ (1 / q) *
        (∑ x ∈ s, |f x| ^ p) ^ (1 / p) * (∑ y ∈ t, |g y| ^ q) ^ (1 / q) := by
  let F : X × Y → ℝ := fun z => schurLeftFactor K A B f p z.1 z.2
  let G : X × Y → ℝ := fun z => schurRightFactor K A B g q z.1 z.2
  have hFnonneg (x : X) (y : Y) : 0 ≤ F (x, y) := by
    dsimp [F, schurLeftFactor]
    exact mul_nonneg (abs_nonneg _) (mul_nonneg
      (Real.rpow_nonneg (hK x y).le _) (div_nonneg (hA x).le (hB y).le))
  have hGnonneg (x : X) (y : Y) : 0 ≤ G (x, y) := by
    dsimp [G, schurRightFactor]
    exact mul_nonneg (abs_nonneg _) (mul_nonneg
      (Real.rpow_nonneg (hK x y).le _) (div_nonneg (hB y).le (hA x).le))
  have hKpow (x : X) (y : Y) :
      (K x y) ^ (1 / p) * (K x y) ^ (1 / q) = K x y := by
    rw [← Real.rpow_add (hK x y)]
    rw [show 1 / p + 1 / q = 1 by simpa [one_div] using hpq.inv_add_inv_eq_one,
      Real.rpow_one]
  have hratio (x : X) (y : Y) :
      (A x / B y) * (B y / A x) = 1 := by
    field_simp [ne_of_gt (hA x), ne_of_gt (hB y)]
  have hfactor (x : X) (y : Y) :
      F (x, y) * G (x, y) = |f x| * K x y * |g y| := by
    dsimp [F, G, schurLeftFactor, schurRightFactor]
    calc
      |f x| * (K x y ^ (1 / p) * (A x / B y)) *
          (|g y| * (K x y ^ (1 / q) * (B y / A x))) =
          |f x| * |g y| *
            (K x y ^ (1 / p) * K x y ^ (1 / q)) *
            ((A x / B y) * (B y / A x)) := by ring
      _ = |f x| * K x y * |g y| := by rw [hKpow x y, hratio x y]; ring
  have hFpow (x : X) (y : Y) :
      F (x, y) ^ p = |f x| ^ p * K x y * (A x / B y) ^ p := by
    dsimp [F, schurLeftFactor]
    rw [Real.mul_rpow (abs_nonneg (f x)) (mul_nonneg
      (Real.rpow_nonneg (hK x y).le _) (div_pos (hA x) (hB y)).le)]
    rw [Real.mul_rpow (Real.rpow_nonneg (hK x y).le _) (div_pos (hA x) (hB y)).le]
    rw [one_div, Real.rpow_inv_rpow (hK x y).le hpq.ne_zero]
    ring
  have hGpow (x : X) (y : Y) :
      G (x, y) ^ q = |g y| ^ q * K x y * (B y / A x) ^ q := by
    dsimp [G, schurRightFactor]
    rw [Real.mul_rpow (abs_nonneg (g y)) (mul_nonneg
      (Real.rpow_nonneg (hK x y).le _) (div_pos (hB y) (hA x)).le)]
    rw [Real.mul_rpow (Real.rpow_nonneg (hK x y).le _) (div_pos (hB y) (hA x)).le]
    rw [one_div, Real.rpow_inv_rpow (hK x y).le hpq.symm.ne_zero]
    ring
  have hsumF : (∑ z ∈ s ×ˢ t, |F z| ^ p) ≤ C * (∑ x ∈ s, |f x| ^ p) := by
    have heq : (∑ z ∈ s ×ˢ t, |F z| ^ p) =
        ∑ x ∈ s, ∑ y ∈ t, |F (x, y)| ^ p := by
      simpa only [Prod.eta] using
        (Finset.sum_product' s t (fun x y => |F (x, y)| ^ p))
    rw [heq]
    calc
      (∑ x ∈ s, ∑ y ∈ t, |F (x, y)| ^ p) ≤ ∑ x ∈ s, |f x| ^ p * C := by
        apply Finset.sum_le_sum
        intro x hx
        calc
          (∑ y ∈ t, |F (x, y)| ^ p) =
              |f x| ^ p * ∑ y ∈ t, K x y * (A x / B y) ^ p := by
                calc
                  (∑ y ∈ t, |F (x, y)| ^ p) =
                      ∑ y ∈ t, |f x| ^ p * (K x y * (A x / B y) ^ p) := by
                        apply Finset.sum_congr rfl
                        intro y hy
                        rw [abs_of_nonneg (hFnonneg x y), hFpow]
                        ring
                  _ = |f x| ^ p * ∑ y ∈ t, K x y * (A x / B y) ^ p := by
                    rw [← Finset.mul_sum]
          _ ≤ |f x| ^ p * C :=
            mul_le_mul_of_nonneg_left (hrow x hx)
              (Real.rpow_nonneg (abs_nonneg (f x)) _)
      _ = C * (∑ x ∈ s, |f x| ^ p) := by rw [← Finset.sum_mul]; ring
  have hsumG : (∑ z ∈ s ×ˢ t, |G z| ^ q) ≤ D * (∑ y ∈ t, |g y| ^ q) := by
    have heq : (∑ z ∈ s ×ˢ t, |G z| ^ q) =
        ∑ y ∈ t, ∑ x ∈ s, |G (x, y)| ^ q := by
      simpa only [Prod.eta] using
        (Finset.sum_product_right' s t (fun x y => |G (x, y)| ^ q))
    rw [heq]
    calc
      (∑ y ∈ t, ∑ x ∈ s, |G (x, y)| ^ q) ≤ ∑ y ∈ t, |g y| ^ q * D := by
        apply Finset.sum_le_sum
        intro y hy
        calc
          (∑ x ∈ s, |G (x, y)| ^ q) =
              |g y| ^ q * ∑ x ∈ s, K x y * (B y / A x) ^ q := by
                calc
                  (∑ x ∈ s, |G (x, y)| ^ q) =
                      ∑ x ∈ s, |g y| ^ q * (K x y * (B y / A x) ^ q) := by
                        apply Finset.sum_congr rfl
                        intro x hx
                        rw [abs_of_nonneg (hGnonneg x y), hGpow]
                        ring
                  _ = |g y| ^ q * ∑ x ∈ s, K x y * (B y / A x) ^ q := by
                    rw [← Finset.mul_sum]
          _ ≤ |g y| ^ q * D :=
            mul_le_mul_of_nonneg_left (hcol y hy)
              (Real.rpow_nonneg (abs_nonneg (g y)) _)
      _ = D * (∑ y ∈ t, |g y| ^ q) := by rw [← Finset.sum_mul]; ring
  have hHolder := Real.inner_le_Lp_mul_Lq (s ×ˢ t) F G hpq
  have hmain : (∑ x ∈ s, ∑ y ∈ t, |f x| * K x y * |g y|) =
      ∑ z ∈ s ×ˢ t, F z * G z := by
    calc
      (∑ x ∈ s, ∑ y ∈ t, |f x| * K x y * |g y|) =
          ∑ z ∈ s ×ˢ t, |f z.1| * K z.1 z.2 * |g z.2| := by
            symm
            simpa only [Prod.eta] using
              (Finset.sum_product' s t (fun x y => |f x| * K x y * |g y|))
      _ = ∑ z ∈ s ×ˢ t, F z * G z := by
        apply Finset.sum_congr rfl
        intro z hz
        exact (hfactor z.1 z.2).symm
  rw [hmain]
  calc
    _ ≤ (∑ z ∈ s ×ˢ t, |F z| ^ p) ^ (1 / p) *
        (∑ z ∈ s ×ˢ t, |G z| ^ q) ^ (1 / q) := hHolder
    _ ≤ (C * (∑ x ∈ s, |f x| ^ p)) ^ (1 / p) *
        (D * (∑ y ∈ t, |g y| ^ q)) ^ (1 / q) := by
          apply mul_le_mul
          · exact Real.rpow_le_rpow (by positivity) hsumF hpq.one_div_nonneg
          · exact Real.rpow_le_rpow (by positivity) hsumG hpq.symm.one_div_nonneg
          · exact Real.rpow_nonneg (by positivity) _
          · exact Real.rpow_nonneg (by positivity) _
    _ = C ^ (1 / p) * D ^ (1 / q) *
        (∑ x ∈ s, |f x| ^ p) ^ (1 / p) *
        (∑ y ∈ t, |g y| ^ q) ^ (1 / q) := by
          rw [Real.mul_rpow hC (by positivity), Real.mul_rpow hD (by positivity)]
          ring

end

end Critical2DKPZ.MomentBounds
