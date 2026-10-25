/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.WalkTails.Hypergeometric
import Critical2DKPZ.RandomWalk.Port.Walk.SRWOneDim
import Critical2DKPZ.RandomWalk.Port.Walk.S1Gauss
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-! # Sub-Gaussian bounds for squared-binomial walk increments

The squared-binomial law is the one-dimensional collision-increment law
`q_m(x)^2 / q_{2m}(0)`.  Its point masses are bounded by three times those of
the ordinary simple walk.  Symmetry lets this comparison be applied to
`cosh(t x) - 1`, which removes any multiplicative prefactor from the resulting
exponential-moment bound.
-/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.WalkTails

open Finset LatticeProb

/-- Chernoff's one-sided bound for a finite weighted law. -/
theorem finite_exp_upperTail_le {α : Type*} (s : Finset α) (p X : α → ℝ)
    (V r : ℝ) (hV : 0 < V) (hr : 0 ≤ r)
    (hp : ∀ x ∈ s, 0 ≤ p x)
    (hmgf : ∀ t : ℝ,
      (∑ x ∈ s, p x * Real.exp (t * X x)) ≤ Real.exp (V * t ^ 2 / 2)) :
    (∑ x ∈ s.filter (fun x => r ≤ X x), p x) ≤ Real.exp (-r ^ 2 / (2 * V)) := by
  let t : ℝ := r / V
  have ht : 0 ≤ t := div_nonneg hr hV.le
  have hterm : ∀ x ∈ s.filter (fun x => r ≤ X x),
      p x * Real.exp (t * r) ≤ p x * Real.exp (t * X x) := by
    intro x hx
    have hx' : r ≤ X x := (Finset.mem_filter.mp hx).2
    apply mul_le_mul_of_nonneg_left _ (hp x (Finset.mem_filter.mp hx).1)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx' ht)
  have hselected := Finset.sum_le_sum hterm
  have hfactor :
      (∑ x ∈ s.filter (fun x => r ≤ X x), p x * Real.exp (t * r)) =
        Real.exp (t * r) * (∑ x ∈ s.filter (fun x => r ≤ X x), p x) := by
    calc
      _ = (∑ x ∈ s.filter (fun x => r ≤ X x), p x) * Real.exp (t * r) := by
        rw [Finset.sum_mul]
      _ = _ := by ring
  have hsubset :
      (∑ x ∈ s.filter (fun x => r ≤ X x), p x * Real.exp (t * X x)) ≤
        ∑ x ∈ s, p x * Real.exp (t * X x) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ s) (fun x hx _ =>
      mul_nonneg (hp x hx) (Real.exp_nonneg _))
  have hmarkov : Real.exp (t * r) *
      (∑ x ∈ s.filter (fun x => r ≤ X x), p x) ≤ Real.exp (V * t ^ 2 / 2) := by
    calc
      _ = ∑ x ∈ s.filter (fun x => r ≤ X x), p x * Real.exp (t * r) := hfactor.symm
      _ ≤ ∑ x ∈ s.filter (fun x => r ≤ X x), p x * Real.exp (t * X x) := hselected
      _ ≤ ∑ x ∈ s, p x * Real.exp (t * X x) := hsubset
      _ ≤ _ := hmgf t
  have hdiv :
      (∑ x ∈ s.filter (fun x => r ≤ X x), p x) ≤
        Real.exp (V * t ^ 2 / 2) / Real.exp (t * r) :=
    (le_div_iff₀ (Real.exp_pos _)).2 (by simpa [mul_comm] using hmarkov)
  have hexpArg : V * t ^ 2 / 2 - t * r = -r ^ 2 / (2 * V) := by
    dsimp [t]
    field_simp
    ring
  have hexp : Real.exp (V * t ^ 2 / 2) / Real.exp (t * r) =
      Real.exp (-r ^ 2 / (2 * V)) := by
    rw [← Real.exp_sub, hexpArg]
  exact hdiv.trans_eq hexp

/-- A lower bound on the central atom of the lazy one-dimensional walk. -/
private theorem P1_zero_ge_inv_sqrt (m : ℕ) (hm : 1 ≤ m) :
    1 / (2 * Real.sqrt (m : ℝ)) ≤ P1 m 0 := by
  induction m with
  | zero => omega
  | succ m ih =>
      by_cases hm0 : m = 0
      · subst m
        rw [P1_zero_succ]
        norm_num [P1_zero_eq, Nat.centralBinom]
      · have hmpos : 1 ≤ m := by omega
        have hih := ih hmpos
        rw [P1_zero_succ]
        have hmR : (0 : ℝ) < m := by exact_mod_cast (Nat.pos_of_ne_zero hm0)
        let r : ℝ := (2 * (m : ℝ) + 1) / (2 * (m : ℝ) + 2)
        have hrpos : 0 < r := by dsimp [r]; positivity
        have hratioSq : (m : ℝ) / (m + 1) ≤ r ^ 2 := by
          dsimp [r]
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < m + 1)]
          field_simp
          nlinarith
        have hroot : Real.sqrt (m : ℝ) ≤ r * Real.sqrt ((m : ℝ) + 1) := by
          apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hrpos.le (Real.sqrt_nonneg _))).mp
          rw [Real.sq_sqrt (le_of_lt hmR), mul_pow,
            Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1)]
          have hmul := mul_le_mul_of_nonneg_right hratioSq (by positivity : (0 : ℝ) ≤ m + 1)
          have hden : ((m : ℝ) / (m + 1)) * ((m : ℝ) + 1) = m := by
            field_simp
          rw [hden] at hmul
          nlinarith
        have hstep' : 1 / (2 * Real.sqrt ((m : ℝ) + 1)) ≤
            r / (2 * Real.sqrt (m : ℝ)) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        have hstep : 1 / (2 * Real.sqrt ((m : ℝ) + 1)) ≤
            r * (1 / (2 * Real.sqrt (m : ℝ))) := by
          simpa [div_eq_mul_inv] using hstep'
        have hmul := mul_le_mul_of_nonneg_left hih hrpos.le
        calc
          1 / (2 * Real.sqrt ((m + 1 : ℕ) : ℝ))
              = 1 / (2 * Real.sqrt ((m : ℝ) + 1)) := by push_cast; rfl
          _ ≤ r * (1 / (2 * Real.sqrt (m : ℝ))) := hstep
          _ ≤ r * P1 m 0 := hmul

/-- The squared-binomial mass is at most three times the simple-walk mass at the corresponding
increment. -/
private theorem hypergeometricWeight_le_three_srw (m j : ℕ) (hj : j ≤ m) :
    hypergeometricWeight m j ≤ 3 * S1 m ((2 * (j : ℤ)) - m) := by
  by_cases hm : m = 0
  · subst m
    have hj0 : j = 0 := by omega
    subst j
    rw [hypergeometricWeight, S1_zero]
    norm_num [hypergeometricWeight]
  · have hmpos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    have hbin : S1 m ((2 * (j : ℤ)) - m) =
        (Nat.choose m j : ℝ) / 2 ^ m := by
      have h := srwHeat_one_binom m j (m - j) (by omega)
      have hsite : (j : ℤ) - ((m - j : ℕ) : ℤ) = 2 * (j : ℤ) - m := by
        have hjm : j ≤ m := hj
        push_cast [Nat.cast_sub hjm]
        ring
      rw [hsite] at h
      simpa [S1] using h
    have hden : S1 (2 * m) 0 =
        (Nat.choose (2 * m) m : ℝ) / 2 ^ (2 * m) := by
      have h := srwHeat_one_binom (2 * m) m m (by omega)
      have hsite : (m : ℤ) - (m : ℤ) = 0 := by ring
      rw [hsite] at h
      simpa [S1] using h
    have hdenP1 : S1 (2 * m) 0 = P1 m 0 := by
      change srwHeat 1 (2 * m) ![0] = P1 m 0
      exact srwHeat_one_two_mul m 0
    have hlow := P1_zero_ge_inv_sqrt m hmpos
    have hupper : S1 m ((2 * (j : ℤ)) - m) ≤
        Real.sqrt 2 / Real.sqrt ((m : ℝ) + 1) := by
      exact srwHeat_one_le m (2 * (j : ℤ) - m)
    have hratio :
        S1 m ((2 * (j : ℤ)) - m) ≤ 3 * S1 (2 * m) 0 := by
      have hsq' : Real.sqrt 2 ≤ 3 / 2 := by
        have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
        nlinarith
      have hmR : 0 < (m : ℝ) := by exact_mod_cast hmpos
      have hsqrtm : Real.sqrt (m : ℝ) ≤ Real.sqrt ((m : ℝ) + 1) :=
        Real.sqrt_le_sqrt (by linarith)
      rw [hdenP1]
      have hbound : Real.sqrt 2 / Real.sqrt ((m : ℝ) + 1) ≤
          3 * (1 / (2 * Real.sqrt (m : ℝ))) := by
        have hbound' : Real.sqrt 2 / Real.sqrt ((m : ℝ) + 1) ≤
            (3 / 2) / Real.sqrt (m : ℝ) := by
          rw [div_le_div_iff₀ (Real.sqrt_pos.mpr (by positivity))
            (Real.sqrt_pos.mpr (by positivity))]
          calc
            Real.sqrt 2 * Real.sqrt (m : ℝ) ≤
                (3 / 2) * Real.sqrt (m : ℝ) := by gcongr
            _ ≤ (3 / 2) * Real.sqrt ((m : ℝ) + 1) := by gcongr
        calc
          _ ≤ (3 / 2) / Real.sqrt (m : ℝ) := hbound'
          _ = 3 * (1 / (2 * Real.sqrt (m : ℝ))) := by ring
      exact hupper.trans (hbound.trans (by nlinarith [hlow]))
    let q : ℝ := (Nat.choose m j : ℝ) / 2 ^ m
    let d : ℝ := (Nat.choose (2 * m) m : ℝ) / 2 ^ (2 * m)
    have hqnonneg : 0 ≤ q := by dsimp [q]; positivity
    have hdpos : 0 < d := by
      dsimp [d]
      exact div_pos (by exact_mod_cast Nat.choose_pos (by omega)) (by positivity)
    have hqle : q ≤ 3 * d := by
      have hh := hratio
      rw [hbin, hden] at hh
      simpa [q, d] using hh
    have hpow : (2 : ℝ) ^ m * 2 ^ m = 2 ^ (2 * m) := by rw [← pow_add]; congr 1; omega
    have hweight : hypergeometricWeight m j = q ^ 2 / d := by
      unfold hypergeometricWeight
      dsimp [q, d]
      have hdenpos : (Nat.choose (2 * m) m : ℝ) ≠ 0 :=
        (ne_of_gt (hypergeometric_denominator_pos m))
      field_simp [hdenpos]
      rw [pow_two, ← hpow]
      ring
    have hmul := mul_le_mul_of_nonneg_left hqle hqnonneg
    rw [hweight]
    apply (div_le_iff₀ hdpos).2
    nlinarith [hmul]

/-- Exponential moment of one ordinary one-dimensional simple-walk step sum,
written using its binomial distribution. -/
private def simpleWalkExpMoment (m : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1),
    ((Nat.choose m j : ℝ) / 2 ^ m) * Real.exp (t * (2 * (j : ℝ) - m))

private theorem simpleWalkExpMoment_eq_cosh (m : ℕ) (t : ℝ) :
    simpleWalkExpMoment m t = Real.cosh t ^ m := by
  unfold simpleWalkExpMoment
  have hbin : (Real.exp (2 * t) + 1) ^ m =
      ∑ j ∈ Finset.range (m + 1),
        Real.exp (2 * t) ^ j * (Nat.choose m j : ℝ) := by
    simpa only [one_pow, mul_one] using add_pow (Real.exp (2 * t)) (1 : ℝ) m
  have hsum :
      (∑ j ∈ Finset.range (m + 1),
        ((Nat.choose m j : ℝ) / 2 ^ m) * Real.exp (t * (2 * (j : ℝ) - m))) =
       Real.exp (-t * m) * ((Real.exp (2 * t) + 1) ^ m / 2 ^ m) := by
    calc
      _ = ∑ j ∈ Finset.range (m + 1),
          Real.exp (-t * m) *
            (Real.exp (2 * t) ^ j * (Nat.choose m j : ℝ) / 2 ^ m) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hexp : Real.exp (t * (2 * (j : ℝ) - m)) =
              Real.exp (2 * t) ^ j * Real.exp (-t * m) := by
            rw [show t * (2 * (j : ℝ) - m) = (2 * t) * j + (-t * m) by ring,
              Real.exp_add, ← Real.exp_nat_mul]
            ring_nf
          rw [hexp]
          ring
      _ = Real.exp (-t * m) *
          (∑ j ∈ Finset.range (m + 1),
            Real.exp (2 * t) ^ j * (Nat.choose m j : ℝ)) / 2 ^ m := by
          calc
            _ = ∑ j ∈ Finset.range (m + 1),
                (Real.exp (-t * m) *
                  (Real.exp (2 * t) ^ j * (Nat.choose m j : ℝ))) / 2 ^ m := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    ring
            _ = _ := by rw [← Finset.sum_div, ← Finset.mul_sum]
      _ = _ := by rw [hbin]; ring
  rw [hsum]
  have hexp : Real.exp (-t * m) = Real.exp (-t) ^ m := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hprod : Real.exp (-t) * (Real.exp (2 * t) + 1) =
      Real.exp t + Real.exp (-t) := by
    calc
      _ = Real.exp (-t + 2 * t) + Real.exp (-t) := by rw [mul_add, ← Real.exp_add]; ring
      _ = _ := by rw [show -t + 2 * t = t by ring]
  calc
    Real.exp (-t * m) * ((Real.exp (2 * t) + 1) ^ m / 2 ^ m) =
        (Real.exp (-t) * (Real.exp (2 * t) + 1) / 2) ^ m := by
          rw [hexp, ← div_pow, ← mul_pow]
          ring
    _ = Real.cosh t ^ m := by rw [hprod, Real.cosh_eq]

/-- The ordinary simple-walk MGF has the Hoeffding bound with unit prefactor. -/
private theorem simpleWalkExpMoment_le (m : ℕ) (t : ℝ) :
    simpleWalkExpMoment m t ≤ Real.exp ((m : ℝ) * t ^ 2 / 2) := by
  rw [simpleWalkExpMoment_eq_cosh]
  calc
    Real.cosh t ^ m ≤ Real.exp (t ^ 2 / 2) ^ m := by
      gcongr
      exact Real.cosh_le_exp_half_sq t
    _ = Real.exp ((m : ℝ) * t ^ 2 / 2) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- The squared-binomial increment has exponential moment at most `exp (3 m t² / 2)` for every
real `t`. -/
theorem hypergeometricExpMoment_le (m : ℕ) (t : ℝ) :
    (∑ j ∈ Finset.range (m + 1),
      hypergeometricWeight m j *
        Real.exp (t * hypergeometricIncrement m j)) ≤
      Real.exp ((3 * (m : ℝ)) * t ^ 2 / 2) := by
  have hsum : ∑ j ∈ Finset.range (m + 1), hypergeometricWeight m j = 1 :=
    sum_hypergeometricWeight m
  have hcosh :
      (∑ j ∈ Finset.range (m + 1),
        hypergeometricWeight m j * Real.exp (t * hypergeometricIncrement m j)) =
      ∑ j ∈ Finset.range (m + 1),
        hypergeometricWeight m j * Real.cosh (t * hypergeometricIncrement m j) := by
    unfold hypergeometricIncrement
    have hflip : ∑ j ∈ Finset.range (m + 1),
        hypergeometricWeight m j * Real.exp (t * (2 * (j : ℝ) - m)) =
        ∑ j ∈ Finset.range (m + 1),
          hypergeometricWeight m j * Real.exp (-(t * (2 * (j : ℝ) - m))) := by
      rw [← Finset.sum_range_reflect]
      apply Finset.sum_congr rfl
      intro j hj
      have hjm : j ≤ m := by simp only [Finset.mem_range] at hj; omega
      have hidx : m + 1 - 1 - j = m - j := by omega
      rw [hidx, hypergeometricWeight_symm m j hjm]
      congr 2
      push_cast [Nat.cast_sub hjm]
      ring
    calc
      _ = (∑ j ∈ Finset.range (m + 1),
            hypergeometricWeight m j * Real.exp (t * (2 * (j : ℝ) - m)) +
          ∑ j ∈ Finset.range (m + 1),
            hypergeometricWeight m j * Real.exp (-(t * (2 * (j : ℝ) - m)))) / 2 := by
          rw [hflip]
          ring
      _ = (∑ j ∈ Finset.range (m + 1),
            (hypergeometricWeight m j * Real.exp (t * (2 * (j : ℝ) - m)) +
              hypergeometricWeight m j * Real.exp (-(t * (2 * (j : ℝ) - m))))) / 2 := by
          congr 1
          rw [← Finset.sum_add_distrib]
      _ = ∑ j ∈ Finset.range (m + 1),
            (hypergeometricWeight m j * Real.exp (t * (2 * (j : ℝ) - m)) +
              hypergeometricWeight m j * Real.exp (-(t * (2 * (j : ℝ) - m)))) / 2 := by
          rw [Finset.sum_div]
      _ = _ := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Real.cosh_eq]
          ring
  have hcomp : ∀ j ∈ Finset.range (m + 1),
      hypergeometricWeight m j ≤ 3 *
        ((Nat.choose m j : ℝ) / 2 ^ m) := by
    intro j hj
    have hjm : j ≤ m := by simp only [Finset.mem_range] at hj; omega
    have hle := hypergeometricWeight_le_three_srw m j hjm
    have hwalk : S1 m ((2 * (j : ℤ)) - m) =
        (Nat.choose m j : ℝ) / 2 ^ m := by
      have h := srwHeat_one_binom m j (m - j) (by omega)
      have hsite : (j : ℤ) - ((m - j : ℕ) : ℤ) = 2 * (j : ℤ) - m := by
        push_cast [Nat.cast_sub hjm]
        ring
      rw [hsite] at h
      simpa [S1] using h
    rw [hwalk] at hle
    exact hle
  have hnonneg : ∀ j ∈ Finset.range (m + 1),
      0 ≤ Real.cosh (t * hypergeometricIncrement m j) - 1 := by
    intro j hj
    have h := Real.one_le_cosh (t * hypergeometricIncrement m j)
    linarith
  have htail :
      (∑ j ∈ Finset.range (m + 1),
        hypergeometricWeight m j *
          (Real.cosh (t * hypergeometricIncrement m j) - 1)) ≤
      3 * (simpleWalkExpMoment m t - 1) := by
    unfold simpleWalkExpMoment
    have hsumP : ∑ j ∈ Finset.range (m + 1),
        ((Nat.choose m j : ℝ) / 2 ^ m) = 1 := by
      have hchoose : ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) = 2 ^ m := by
        exact_mod_cast Nat.sum_range_choose m
      rw [← Finset.sum_div, hchoose]
      simp
    have hcoshp : simpleWalkExpMoment m t =
        ∑ j ∈ Finset.range (m + 1),
          ((Nat.choose m j : ℝ) / 2 ^ m) *
            Real.cosh (t * (2 * (j : ℝ) - m)) := by
      unfold simpleWalkExpMoment
      have hflip : ∑ j ∈ Finset.range (m + 1),
          ((Nat.choose m j : ℝ) / 2 ^ m) *
              Real.exp (t * (2 * (j : ℝ) - m)) =
          ∑ j ∈ Finset.range (m + 1),
            ((Nat.choose m j : ℝ) / 2 ^ m) *
              Real.exp (-(t * (2 * (j : ℝ) - m))) := by
        rw [← Finset.sum_range_reflect]
        apply Finset.sum_congr rfl
        intro j hj
        have hjm : j ≤ m := by simp only [Finset.mem_range] at hj; omega
        have hidx : m + 1 - 1 - j = m - j := by omega
        rw [hidx]
        have hchooseSymm : (Nat.choose m (m - j) : ℝ) = Nat.choose m j := by
          exact_mod_cast Nat.choose_symm hjm
        rw [hchooseSymm]
        congr 2
        push_cast [Nat.cast_sub hjm]
        ring
      calc
        _ = (∑ j ∈ Finset.range (m + 1),
              ((Nat.choose m j : ℝ) / 2 ^ m) *
                  Real.exp (t * (2 * (j : ℝ) - m)) +
            ∑ j ∈ Finset.range (m + 1),
              ((Nat.choose m j : ℝ) / 2 ^ m) *
                  Real.exp (-(t * (2 * (j : ℝ) - m)))) / 2 := by
            rw [hflip]
            ring
        _ = (∑ j ∈ Finset.range (m + 1),
              (((Nat.choose m j : ℝ) / 2 ^ m) *
                  Real.exp (t * (2 * (j : ℝ) - m)) +
                ((Nat.choose m j : ℝ) / 2 ^ m) *
                  Real.exp (-(t * (2 * (j : ℝ) - m))))) / 2 := by
            congr 1
            rw [← Finset.sum_add_distrib]
        _ = ∑ j ∈ Finset.range (m + 1),
              (((Nat.choose m j : ℝ) / 2 ^ m) *
                  Real.exp (t * (2 * (j : ℝ) - m)) +
                ((Nat.choose m j : ℝ) / 2 ^ m) *
                  Real.exp (-(t * (2 * (j : ℝ) - m)))) / 2 := by
            rw [Finset.sum_div]
        _ = _ := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [Real.cosh_eq]
            ring
    have hterm : ∀ j ∈ Finset.range (m + 1),
        hypergeometricWeight m j *
            (Real.cosh (t * hypergeometricIncrement m j) - 1) ≤
          3 * (((Nat.choose m j : ℝ) / 2 ^ m) *
            (Real.cosh (t * hypergeometricIncrement m j) - 1)) := by
      intro j hj
      calc
        _ ≤ (3 * ((Nat.choose m j : ℝ) / 2 ^ m)) *
              (Real.cosh (t * hypergeometricIncrement m j) - 1) :=
          mul_le_mul_of_nonneg_right (hcomp j hj) (hnonneg j hj)
        _ = _ := by ring
    have hsumTerm := Finset.sum_le_sum hterm
    have hrewrite :
        (∑ j ∈ Finset.range (m + 1),
          ((Nat.choose m j : ℝ) / 2 ^ m) *
              (Real.cosh (t * hypergeometricIncrement m j) - 1)) =
          simpleWalkExpMoment m t - 1 := by
      calc
        _ = ∑ j ∈ Finset.range (m + 1),
              (((Nat.choose m j : ℝ) / 2 ^ m) *
                Real.cosh (t * hypergeometricIncrement m j) -
                ((Nat.choose m j : ℝ) / 2 ^ m)) := by
            apply Finset.sum_congr rfl
            intro j hj
            unfold hypergeometricIncrement
            ring
        _ = (∑ j ∈ Finset.range (m + 1),
              ((Nat.choose m j : ℝ) / 2 ^ m) *
                Real.cosh (t * hypergeometricIncrement m j)) -
              ∑ j ∈ Finset.range (m + 1), ((Nat.choose m j : ℝ) / 2 ^ m) := by
            rw [← Finset.sum_sub_distrib]
        _ = simpleWalkExpMoment m t - 1 := by
            have hcoshp' : simpleWalkExpMoment m t =
                ∑ j ∈ Finset.range (m + 1),
                  ((Nat.choose m j : ℝ) / 2 ^ m) *
                    Real.cosh (t * hypergeometricIncrement m j) := by
              simpa [hypergeometricIncrement] using hcoshp
            rw [hcoshp', hsumP]
    calc
      _ ≤ 3 * (∑ j ∈ Finset.range (m + 1),
          ((Nat.choose m j : ℝ) / 2 ^ m) *
            (Real.cosh (t * hypergeometricIncrement m j) - 1)) := by
          simpa only [Finset.mul_sum] using hsumTerm
      _ = 3 * (simpleWalkExpMoment m t - 1) := by rw [hrewrite]
  have hmgfP := simpleWalkExpMoment_le m t
  have hA : 0 ≤ (m : ℝ) * t ^ 2 / 2 := by positivity
  have hmgf :
      (∑ j ∈ Finset.range (m + 1),
        hypergeometricWeight m j *
          Real.exp (t * hypergeometricIncrement m j)) ≤
        1 + 3 * (Real.exp ((m : ℝ) * t ^ 2 / 2) - 1) := by
    rw [hcosh]
    have hsplit : ∑ j ∈ Finset.range (m + 1),
        hypergeometricWeight m j * Real.cosh (t * hypergeometricIncrement m j) =
        1 + ∑ j ∈ Finset.range (m + 1),
          hypergeometricWeight m j *
            (Real.cosh (t * hypergeometricIncrement m j) - 1) := by
      calc
        _ = ∑ j ∈ Finset.range (m + 1),
              (hypergeometricWeight m j +
                hypergeometricWeight m j *
                  (Real.cosh (t * hypergeometricIncrement m j) - 1)) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
        _ = _ := by rw [Finset.sum_add_distrib, hsum]
    rw [hsplit]
    linarith [htail, hmgfP]
  have hexp : 1 + 3 * (Real.exp ((m : ℝ) * t ^ 2 / 2) - 1) ≤
      Real.exp ((3 * (m : ℝ)) * t ^ 2 / 2) := by
    let x := (m : ℝ) * t ^ 2 / 2
    have hx : 0 ≤ x := by dsimp [x]; positivity
    have hconv : 1 + 3 * (Real.exp x - 1) ≤ Real.exp (3 * x) := by
      have hy : 1 ≤ Real.exp x := Real.one_le_exp_iff.mpr hx
      have hfact : (Real.exp x) ^ 3 - 3 * Real.exp x + 2 =
          (Real.exp x - 1) ^ 2 * (Real.exp x + 2) := by ring
      have hnonneg : 0 ≤ (Real.exp x - 1) ^ 2 * (Real.exp x + 2) :=
        mul_nonneg (sq_nonneg _) (by linarith [Real.exp_pos x])
      have hexp3 : Real.exp (3 * x) = (Real.exp x) ^ 3 := by
        rw [← Real.exp_nat_mul]
        congr 1
      rw [hexp3]
      nlinarith [hfact, hnonneg]
    have hxArg : (3 * (m : ℝ)) * t ^ 2 / 2 = 3 * x := by dsimp [x]; ring
    rw [hxArg]
    exact hconv
  exact hmgf.trans hexp


/-- Products of squared-binomial exponential moments are bounded by `exp (3 t² ∑ mᵢ / 2)`,
uniformly in the number of factors. -/
theorem hypergeometricCompositionExpMoment_le {ι : Type*} (s : Finset ι)
    (m : ι → ℕ) (t : ℝ) :
    (∏ i ∈ s,
      ∑ j ∈ Finset.range (m i + 1),
        hypergeometricWeight (m i) j *
          Real.exp (t * hypergeometricIncrement (m i) j)) ≤
      Real.exp (((3 / 2 : ℝ) * t ^ 2) * ∑ i ∈ s, (m i : ℝ)) := by
  have hprod :
      (∏ i ∈ s,
        ∑ j ∈ Finset.range (m i + 1),
          hypergeometricWeight (m i) j *
            Real.exp (t * hypergeometricIncrement (m i) j)) ≤
      ∏ i ∈ s, Real.exp (((3 / 2 : ℝ) * t ^ 2) * (m i : ℝ)) := by
    apply Finset.prod_le_prod₀
    · intro i hi
      exact Finset.sum_nonneg fun j hj =>
        mul_nonneg (hypergeometricWeight_nonneg (m i) j) (Real.exp_nonneg _)
    · intro i hi
      have hArg : (3 * (m i : ℝ)) * t ^ 2 / 2 =
          ((3 / 2 : ℝ) * t ^ 2) * (m i : ℝ) := by ring
      simpa only [hArg] using hypergeometricExpMoment_le (m i) t
  calc
    _ ≤ ∏ i ∈ s, Real.exp (((3 / 2 : ℝ) * t ^ 2) * (m i : ℝ)) := hprod
    _ = Real.exp (((3 / 2 : ℝ) * t ^ 2) * ∑ i ∈ s, (m i : ℝ)) := by
      rw [← Real.exp_sum]
      congr 1
      rw [← Finset.mul_sum]

/-- The increment of a finite composition of independent squared-binomial
walk increments. -/
def hypergeometricCompositionIncrement {n : ℕ} (m : Fin n → ℕ)
    (j : Fin n → ℕ) : ℝ :=
  ∑ i, hypergeometricIncrement (m i) (j i)

/-- The product mass of one outcome in a finite composition. -/
def hypergeometricCompositionWeight {n : ℕ} (m : Fin n → ℕ)
    (j : Fin n → ℕ) : ℝ :=
  ∏ i, hypergeometricWeight (m i) (j i)

/-- The Cartesian product of the one-increment supports. -/
def hypergeometricCompositionSupport {n : ℕ} (m : Fin n → ℕ) :
    Finset (Fin n → ℕ) :=
  Fintype.piFinset fun i => Finset.range (m i + 1)

/-- The MGF of a finite independent composition factors into the one-increment
MGFs. -/
theorem hypergeometricCompositionExpMoment_eq_prod {n : ℕ}
    (m : Fin n → ℕ) (t : ℝ) :
    (∑ j ∈ hypergeometricCompositionSupport m,
      hypergeometricCompositionWeight m j *
        Real.exp (t * hypergeometricCompositionIncrement m j)) =
      ∏ i, ∑ j ∈ Finset.range (m i + 1),
        hypergeometricWeight (m i) j *
          Real.exp (t * hypergeometricIncrement (m i) j) := by
  classical
  unfold hypergeometricCompositionSupport hypergeometricCompositionWeight
    hypergeometricCompositionIncrement
  calc
    _ = ∑ j ∈ Fintype.piFinset (fun i : Fin n => Finset.range (m i + 1)),
          ∏ i, (hypergeometricWeight (m i) (j i) *
            Real.exp (t * hypergeometricIncrement (m i) (j i))) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mul_sum, Real.exp_sum]
          simp only [Finset.prod_mul_distrib]
    _ = ∏ i, ∑ j ∈ Finset.range (m i + 1),
          hypergeometricWeight (m i) j *
            Real.exp (t * hypergeometricIncrement (m i) j) := by
          symm
          exact Finset.prod_univ_sum
            (fun i : Fin n => Finset.range (m i + 1))
            (fun i j => hypergeometricWeight (m i) j *
              Real.exp (t * hypergeometricIncrement (m i) j))

/-- Finite sums of independent squared-binomial increments have upper tail at most
`exp (-r² / (6 ∑ mᵢ))` for `r ≥ 0` and positive total duration. -/
theorem hypergeometricComposition_upperTail_le {n : ℕ}
    (m : Fin n → ℕ) (hm : 0 < ∑ i, (m i : ℝ)) (r : ℝ) (hr : 0 ≤ r) :
    (∑ j ∈ (hypergeometricCompositionSupport m).filter
      (fun j => r ≤ hypergeometricCompositionIncrement m j),
      hypergeometricCompositionWeight m j) ≤
      Real.exp (-r ^ 2 / (6 * ∑ i, (m i : ℝ))) := by
  let V : ℝ := 3 * ∑ i, (m i : ℝ)
  have hV : 0 < V := by dsimp [V]; positivity
  have hmgf : ∀ t : ℝ,
      (∑ j ∈ hypergeometricCompositionSupport m,
        hypergeometricCompositionWeight m j *
          Real.exp (t * hypergeometricCompositionIncrement m j)) ≤
        Real.exp (V * t ^ 2 / 2) := by
    intro t
    rw [hypergeometricCompositionExpMoment_eq_prod]
    have h := hypergeometricCompositionExpMoment_le Finset.univ m t
    have hArg :
        ((3 / 2 : ℝ) * t ^ 2) * ∑ i, (m i : ℝ) = V * t ^ 2 / 2 := by
      dsimp [V]
      ring
    simpa [hArg] using h
  have h := finite_exp_upperTail_le
    (hypergeometricCompositionSupport m)
    (hypergeometricCompositionWeight m)
    (hypergeometricCompositionIncrement m) V r hV hr
    (by
      intro j hj
      unfold hypergeometricCompositionWeight
      exact Finset.prod_nonneg fun i hi => hypergeometricWeight_nonneg (m i) (j i))
    hmgf
  have hden : 2 * V = 6 * ∑ i, (m i : ℝ) := by dsimp [V]; ring
  simpa only [hden] using h

end Critical2DKPZ.WalkTails

end
