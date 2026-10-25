/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
module

public import Mathlib
public import Critical2DKPZ.RandomWalk.Port.Walk.PairedMultiplierOff

/-!
# The torus integral of the majorant off the Gaussian region

`∫_{[-π,π]^d} offBound d n = O(n^{-(d+2)/2})` (`exists_integral_offBound_le`). The constant
part `2(1 - 1/d)ⁿ` of the majorant decays faster than any power. Its second part is a sum of
products over the coordinates, so its integral is `A B^{d-1}/2` with one-dimensional integrals
`A`, `B` of `1_{|t| > π/2} e^{-b(π - |t|)²}` (weighted by `(π - |t|)²` for `A`),
`b = 2n/(π²d)`; bounding that factor by the two translated Gaussians
`e^{-b(t - π)²} + e^{-b(t + π)²}` gives `A = O(b^{-3/2})` and `B = O(b^{-1/2})`.
-/

@[expose] public section

open MeasureTheory Filter Topology

noncomputable section

namespace LatticeProb.LocalCLT

open ContinuousTime

variable {d : ℕ}

/-- Pointwise bound of the indicator factor by two shifted Gaussians. -/
private lemma offFactor_le_exp_sum (b : ℝ) (t : ℝ) :
    Set.indicator {t : ℝ | Real.pi / 2 < |t|}
        (fun t => Real.exp (-b * (Real.pi - |t|) ^ 2)) t
      ≤ Real.exp (-b * (t - Real.pi) ^ 2) + Real.exp (-b * (t + Real.pi) ^ 2) := by
  by_cases h : Real.pi / 2 < |t|
  · rw [Set.indicator_of_mem (s := {t : ℝ | Real.pi / 2 < |t|}) h]
    rcases le_total 0 t with ht0 | ht0
    · have habs : |t| = t := abs_of_nonneg ht0
      rw [habs]
      have h1 : (Real.pi - t) ^ 2 = (t - Real.pi) ^ 2 := by ring
      rw [h1]
      exact le_add_of_nonneg_right (Real.exp_pos _).le
    · have habs : |t| = -t := abs_of_nonpos ht0
      rw [habs]
      have h1 : Real.pi - -t = t + Real.pi := by ring
      rw [h1]
      exact le_add_of_nonneg_left (Real.exp_pos _).le
  · rw [Set.indicator_of_notMem (s := {t : ℝ | Real.pi / 2 < |t|}) h]
    positivity

/-- Pointwise bound of the squared-distance weighted indicator factor. -/
private lemma sq_mul_offFactor_le (b : ℝ) (t : ℝ) :
    (Real.pi - |t|) ^ 2 * Set.indicator {t : ℝ | Real.pi / 2 < |t|}
        (fun t => Real.exp (-b * (Real.pi - |t|) ^ 2)) t
      ≤ (t - Real.pi) ^ 2 * Real.exp (-b * (t - Real.pi) ^ 2)
        + (t + Real.pi) ^ 2 * Real.exp (-b * (t + Real.pi) ^ 2) := by
  by_cases h : Real.pi / 2 < |t|
  · rw [Set.indicator_of_mem (s := {t : ℝ | Real.pi / 2 < |t|}) h]
    rcases le_total 0 t with ht0 | ht0
    · have habs : |t| = t := abs_of_nonneg ht0
      rw [habs]
      have h1 : (Real.pi - t) ^ 2 = (t - Real.pi) ^ 2 := by ring
      rw [h1]
      exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    · have habs : |t| = -t := abs_of_nonpos ht0
      rw [habs]
      have h1 : Real.pi - -t = t + Real.pi := by ring
      rw [h1]
      exact le_add_of_nonneg_left (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
  · rw [Set.indicator_of_notMem (s := {t : ℝ | Real.pi / 2 < |t|}) h]
    simp only [mul_zero]
    positivity

/-- Pointwise Gaussian-versus-Gaussian bound: `u² e^{-bu²} ≤ (2/b) e^{-(b/2)u²}`. -/
private lemma sq_mul_exp_neg_mul_sq_le (b : ℝ) (hb : 0 < b) (u : ℝ) :
    u ^ 2 * Real.exp (-b * u ^ 2) ≤ 2 / b * Real.exp (-(b / 2) * u ^ 2) := by
  set v := b / 2 * u ^ 2 with hv
  have hexp : v ≤ Real.exp v := by
    have := Real.add_one_le_exp v
    linarith
  have hmain : v * Real.exp (-2 * v) ≤ Real.exp (-v) := by
    calc v * Real.exp (-2 * v) ≤ Real.exp v * Real.exp (-2 * v) :=
          mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
      _ = Real.exp (-v) := by rw [← Real.exp_add]; congr 1; ring_nf
  have hcoef : u ^ 2 = 2 / b * v := by rw [hv]; field_simp [hb.ne']
  have harg : -b * u ^ 2 = -(2 * v) := by rw [hv]; field_simp [hb.ne']
  calc u ^ 2 * Real.exp (-b * u ^ 2)
      = (2 / b * v) * Real.exp (-(2 * v)) := by rw [harg, hcoef]
    _ = 2 / b * (v * Real.exp (-2 * v)) := by ring_nf
    _ ≤ 2 / b * Real.exp (-v) := mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = 2 / b * Real.exp (-(b / 2) * u ^ 2) := by rw [hv]; congr 1; ring_nf

/-- Integrability of `u² e^{-bu²}`. -/
private lemma integrable_sq_mul_exp_neg_mul_sq (b : ℝ) (hb : 0 < b) :
    Integrable (fun u : ℝ => u ^ 2 * Real.exp (-b * u ^ 2)) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq hb (s := (2 : ℝ)) (by norm_num)
  convert h using 1
  ext u
  rw [Real.rpow_two]

/-- The torus-interval integral of the indicator factor is at most `2√(π/b)`. -/
private lemma integral_offFactor_le (b : ℝ) (hb : 0 < b) :
    ∫ t in Set.Icc (-Real.pi) Real.pi,
        Set.indicator {t : ℝ | Real.pi / 2 < |t|}
          (fun t => Real.exp (-b * (Real.pi - |t|) ^ 2)) t
      ≤ 2 * Real.sqrt (Real.pi / b) := by
  have hg : Integrable (fun t : ℝ => Real.exp (-b * (t - Real.pi) ^ 2)
      + Real.exp (-b * (t + Real.pi) ^ 2)) :=
    ((integrable_exp_neg_mul_sq hb).comp_sub_right Real.pi).add
      ((integrable_exp_neg_mul_sq hb).comp_add_right Real.pi)
  calc ∫ t in Set.Icc (-Real.pi) Real.pi,
        Set.indicator {t : ℝ | Real.pi / 2 < |t|}
          (fun t => Real.exp (-b * (Real.pi - |t|) ^ 2)) t
      ≤ ∫ t in Set.Icc (-Real.pi) Real.pi,
          (Real.exp (-b * (t - Real.pi) ^ 2) + Real.exp (-b * (t + Real.pi) ^ 2)) :=
        setIntegral_mono_of_nonneg
          (fun t _ => Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) t)
          (fun t _ => offFactor_le_exp_sum b t)
          hg.integrableOn
    _ ≤ ∫ t : ℝ, (Real.exp (-b * (t - Real.pi) ^ 2) + Real.exp (-b * (t + Real.pi) ^ 2)) :=
        setIntegral_le_integral hg (Eventually.of_forall fun t => by positivity)
    _ = Real.sqrt (Real.pi / b) + Real.sqrt (Real.pi / b) := by
        rw [integral_add ((integrable_exp_neg_mul_sq hb).comp_sub_right Real.pi)
          ((integrable_exp_neg_mul_sq hb).comp_add_right Real.pi)]
        rw [integral_sub_right_eq_self (fun u : ℝ => Real.exp (-b * u ^ 2)) Real.pi,
          integral_add_right_eq_self (fun u : ℝ => Real.exp (-b * u ^ 2)) Real.pi,
          integral_gaussian]
    _ = 2 * Real.sqrt (Real.pi / b) := by ring

/-- The weighted indicator-factor integral is at most `(4/b)√(2π/b)`. -/
private lemma integral_sq_offFactor_le (b : ℝ) (hb : 0 < b) :
    ∫ t in Set.Icc (-Real.pi) Real.pi,
        (Real.pi - |t|) ^ 2 * Set.indicator {t : ℝ | Real.pi / 2 < |t|}
          (fun t => Real.exp (-b * (Real.pi - |t|) ^ 2)) t
      ≤ 4 / b * Real.sqrt (2 * Real.pi / b) := by
  have hg : Integrable (fun t : ℝ => (t - Real.pi) ^ 2 * Real.exp (-b * (t - Real.pi) ^ 2)
      + (t + Real.pi) ^ 2 * Real.exp (-b * (t + Real.pi) ^ 2)) :=
    ((integrable_sq_mul_exp_neg_mul_sq b hb).comp_sub_right Real.pi).add
      ((integrable_sq_mul_exp_neg_mul_sq b hb).comp_add_right Real.pi)
  have h2b : Integrable (fun u : ℝ => (2 / b) * Real.exp (-(b / 2) * u ^ 2)) :=
    (integrable_exp_neg_mul_sq (by positivity : 0 < b / 2)).const_mul (2 / b)
  have hint : ∫ u : ℝ, u ^ 2 * Real.exp (-b * u ^ 2)
      ≤ (2 / b) * Real.sqrt (Real.pi / (b / 2)) := by
    have h1 : ∫ u : ℝ, u ^ 2 * Real.exp (-b * u ^ 2)
        ≤ ∫ u : ℝ, (2 / b) * Real.exp (-(b / 2) * u ^ 2) :=
      integral_mono (integrable_sq_mul_exp_neg_mul_sq b hb) h2b
        (fun u => sq_mul_exp_neg_mul_sq_le b hb u)
    rwa [integral_const_mul, integral_gaussian] at h1
  calc ∫ t in Set.Icc (-Real.pi) Real.pi,
        (Real.pi - |t|) ^ 2 * Set.indicator {t : ℝ | Real.pi / 2 < |t|}
          (fun t => Real.exp (-b * (Real.pi - |t|) ^ 2)) t
      ≤ ∫ t in Set.Icc (-Real.pi) Real.pi,
          ((t - Real.pi) ^ 2 * Real.exp (-b * (t - Real.pi) ^ 2)
            + (t + Real.pi) ^ 2 * Real.exp (-b * (t + Real.pi) ^ 2)) :=
        setIntegral_mono_of_nonneg
          (fun t _ => mul_nonneg (sq_nonneg _)
            (Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) t))
          (fun t _ => sq_mul_offFactor_le b t)
          hg.integrableOn
    _ ≤ ∫ t : ℝ, ((t - Real.pi) ^ 2 * Real.exp (-b * (t - Real.pi) ^ 2)
            + (t + Real.pi) ^ 2 * Real.exp (-b * (t + Real.pi) ^ 2)) :=
        setIntegral_le_integral hg (Eventually.of_forall fun t => by
          have h1 : 0 ≤ (t - Real.pi) ^ 2 * Real.exp (-b * (t - Real.pi) ^ 2) :=
            mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
          have h2 : 0 ≤ (t + Real.pi) ^ 2 * Real.exp (-b * (t + Real.pi) ^ 2) :=
            mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
          exact add_nonneg h1 h2)
    _ = 2 * ∫ u : ℝ, u ^ 2 * Real.exp (-b * u ^ 2) := by
        rw [integral_add ((integrable_sq_mul_exp_neg_mul_sq b hb).comp_sub_right Real.pi)
          ((integrable_sq_mul_exp_neg_mul_sq b hb).comp_add_right Real.pi)]
        rw [integral_sub_right_eq_self (fun u : ℝ => u ^ 2 * Real.exp (-b * u ^ 2)) Real.pi,
          integral_add_right_eq_self (fun u : ℝ => u ^ 2 * Real.exp (-b * u ^ 2)) Real.pi]
        ring
    _ ≤ 2 * ((2 / b) * Real.sqrt (Real.pi / (b / 2))) :=
        mul_le_mul_of_nonneg_left hint (by norm_num)
    _ = 4 / b * Real.sqrt (2 * Real.pi / b) := by
        rw [show Real.pi / (b / 2) = 2 * Real.pi / b by field_simp [hb.ne']]
        ring

/-- The majorant `offBound` is integrable on the torus. -/
theorem integrableOn_offBound (hd : 1 ≤ d) (n : ℕ) :
    IntegrableOn (offBound d n) (torusBox d) := by
  have : IsFiniteMeasure (volume.restrict (torusBox d)) :=
    isFiniteMeasure_restrict.mpr (by rw [volume_torusBox d]; exact ENNReal.ofReal_ne_top)
  have hset : MeasurableSet {t : ℝ | Real.pi / 2 < |t|} := by measurability
  have hmeas : AEStronglyMeasurable (offBound d n) (volume.restrict (torusBox d)) :=
    (by unfold offBound; fun_prop : Measurable (offBound d n)).aestronglyMeasurable
  refine Integrable.of_bound hmeas (2 + Real.pi ^ 2 / 2) ?_
  rw [ae_restrict_iff' (torusBox_measurable d)]
  filter_upwards with θ hθ
  have hmem := Set.mem_Icc.mp hθ
  have hθabs : ∀ i, |θ i| ≤ Real.pi := fun i => by
    rw [abs_le]; exact ⟨by linarith [hmem.1 i], by linarith [hmem.2 i]⟩
  have hgle : ∀ i, Set.indicator {t : ℝ | Real.pi / 2 < |t|}
      (fun t => Real.exp (-(2 / (Real.pi ^ 2 * d)) * n * (Real.pi - |t|) ^ 2)) (θ i) ≤ 1 := by
    intro i
    by_cases hii : Real.pi / 2 < |θ i|
    · rw [Set.indicator_of_mem (s := {t : ℝ | Real.pi / 2 < |t|}) hii, Real.exp_le_one_iff]
      have hc : 0 ≤ (2 / (Real.pi ^ 2 * (d : ℝ))) * (n : ℝ) := by positivity
      nlinarith [sq_nonneg (Real.pi - |θ i|)]
    · rw [Set.indicator_of_notMem (s := {t : ℝ | Real.pi / 2 < |t|}) hii]; norm_num
  have hg1 : ∀ i, 0 ≤ Set.indicator {t : ℝ | Real.pi / 2 < |t|}
      (fun t => Real.exp (-(2 / (Real.pi ^ 2 * d)) * n * (Real.pi - |t|) ^ 2)) (θ i) :=
    fun i => Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) (θ i)
  have hprod : ∏ i, Set.indicator {t : ℝ | Real.pi / 2 < |t|}
      (fun t => Real.exp (-(2 / (Real.pi ^ 2 * d)) * n * (Real.pi - |t|) ^ 2)) (θ i) ≤ 1 :=
    Finset.prod_le_one₀ (fun i _ => hg1 i) (fun i _ => hgle i)
  have hsq : ∀ j, (Real.pi - |θ j|) ^ 2 ≤ Real.pi ^ 2 := by
    intro j
    rw [sq_le_sq, abs_of_nonneg (by linarith [hθabs j]), abs_of_pos Real.pi_pos]
    linarith [hθabs j, abs_nonneg (θ j)]
  have hsum : ∑ j, (Real.pi - |θ j|) ^ 2 / (2 * d)
      * ∏ i, Set.indicator {t : ℝ | Real.pi / 2 < |t|}
        (fun t => Real.exp (-(2 / (Real.pi ^ 2 * d)) * n * (Real.pi - |t|) ^ 2)) (θ i)
      ≤ Real.pi ^ 2 / 2 := by
    calc ∑ j, (Real.pi - |θ j|) ^ 2 / (2 * d)
          * ∏ i, Set.indicator {t : ℝ | Real.pi / 2 < |t|}
            (fun t => Real.exp (-(2 / (Real.pi ^ 2 * d)) * n * (Real.pi - |t|) ^ 2)) (θ i)
        ≤ ∑ _j : Fin d, (Real.pi ^ 2 / (2 * d)) := by
          apply Finset.sum_le_sum; intro j _
          calc (Real.pi - |θ j|) ^ 2 / (2 * d)
                * ∏ i, Set.indicator {t : ℝ | Real.pi / 2 < |t|}
                  (fun t => Real.exp (-(2 / (Real.pi ^ 2 * d)) * n * (Real.pi - |t|) ^ 2)) (θ i)
              ≤ (Real.pi - |θ j|) ^ 2 / (2 * d) * 1 :=
                mul_le_mul_of_nonneg_left hprod (by positivity)
            _ ≤ Real.pi ^ 2 / (2 * d) := by
                rw [mul_one]
                exact div_le_div_of_nonneg_right (hsq j) (by positivity)
      _ = Real.pi ^ 2 / 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp [show (d : ℝ) ≠ 0 by positivity]
  have hsum0 : 0 ≤ ∑ j, (Real.pi - |θ j|) ^ 2 / (2 * d)
      * ∏ i, Set.indicator {t : ℝ | Real.pi / 2 < |t|}
        (fun t => Real.exp (-(2 / (Real.pi ^ 2 * d)) * n * (Real.pi - |t|) ^ 2)) (θ i) :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (by positivity)
      (Finset.prod_nonneg (fun i _ => hg1 i)))
  have h1md0 : 0 ≤ 1 - 1 / (d : ℝ) := by
    rw [sub_nonneg, div_le_one (by positivity)]; exact_mod_cast hd
  have h1md1 : 1 - 1 / (d : ℝ) ≤ 1 := by
    have : 0 ≤ 1 / (d : ℝ) := by positivity
    linarith
  have hconst0 : 0 ≤ 2 * (1 - 1 / (d : ℝ)) ^ n :=
    mul_nonneg (by norm_num) (pow_nonneg h1md0 n)
  have hconst1 : 2 * (1 - 1 / (d : ℝ)) ^ n ≤ 2 := by
    have := pow_le_one₀ h1md0 h1md1 (n := n)
    linarith
  rw [Real.norm_eq_abs, offBound, abs_of_nonneg (add_nonneg hconst0 hsum0)]
  linarith

/-- The constant part of `offBound` integrates to `O(n^{-(d+2)/2})`. -/
private lemma offBound_const_le (hd : 1 ≤ d) (n : ℕ) (hn : 1 ≤ n) :
    2 * (1 - 1 / (d : ℝ)) ^ n * (2 * Real.pi) ^ d
      ≤ (2 * (2 * Real.pi) ^ d * (Nat.factorial (d + 1) : ℝ) * (d : ℝ) ^ (d + 1))
        * (n : ℝ) ^ (-((d : ℝ) + 2) / 2) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1md0 : 0 ≤ 1 - 1 / (d : ℝ) := by
    rw [sub_nonneg, div_le_one (by positivity)]; exact_mod_cast hd
  have hexp1 : (1 - 1 / (d : ℝ)) ^ n ≤ Real.exp (-(n : ℝ) / d) := by
    have hbase : 1 - 1 / (d : ℝ) ≤ Real.exp (-(1 / (d : ℝ))) := by
      have := Real.add_one_le_exp (-(1 / (d : ℝ))); linarith
    calc (1 - 1 / (d : ℝ)) ^ n ≤ (Real.exp (-(1 / (d : ℝ)))) ^ n :=
          pow_le_pow_left₀ h1md0 hbase n
      _ = Real.exp ((n : ℝ) * (-(1 / (d : ℝ)))) := (Real.exp_nat_mul (-(1 / (d : ℝ))) n).symm
      _ = Real.exp (-(n : ℝ) / d) := by congr 1; ring
  have hexp2 : Real.exp (-(n : ℝ) / d)
      ≤ (Nat.factorial (d + 1) : ℝ) * ((d : ℝ) / n) ^ (d + 1) := by
    have hx : 0 ≤ (n : ℝ) / d := by positivity
    have h := Real.pow_div_factorial_le_exp (x := (n : ℝ) / d) hx (d + 1)
    have hmf : (0 : ℝ) < (Nat.factorial (d + 1) : ℝ) := by positivity
    rw [div_le_iff₀ hmf] at h
    rw [neg_div, Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos _)]
    calc (1 : ℝ) = ((n : ℝ) / d) ^ (d + 1) * ((d : ℝ) / n) ^ (d + 1) := by
          rw [← mul_pow]
          have : (n : ℝ) / d * ((d : ℝ) / n) = 1 := by field_simp [hnpos.ne', hdpos.ne']
          rw [this, one_pow]
      _ ≤ (Real.exp ((n : ℝ) / d) * (Nat.factorial (d + 1) : ℝ))
          * ((d : ℝ) / n) ^ (d + 1) :=
          mul_le_mul_of_nonneg_right h (by positivity)
      _ = (Nat.factorial (d + 1) : ℝ) * ((d : ℝ) / n) ^ (d + 1)
            * Real.exp ((n : ℝ) / d) := by ring
  have hdn : ((d : ℝ) / n) ^ (d + 1) = (d : ℝ) ^ (d + 1)
      * (n : ℝ) ^ (-((d + 1 : ℕ) : ℝ)) := by
    rw [div_pow, div_eq_mul_inv, Real.rpow_neg (le_of_lt hnpos), Real.rpow_natCast]
  have hpow : (n : ℝ) ^ (-((d + 1 : ℕ) : ℝ)) ≤ (n : ℝ) ^ (-((d : ℝ) + 2) / 2) := by
    apply Real.rpow_le_rpow_of_exponent_le hn1
    push_cast
    have : (0 : ℝ) ≤ d := by positivity
    linarith
  calc 2 * (1 - 1 / (d : ℝ)) ^ n * (2 * Real.pi) ^ d
      ≤ 2 * Real.exp (-(n : ℝ) / d) * (2 * Real.pi) ^ d := by gcongr
    _ ≤ 2 * ((Nat.factorial (d + 1) : ℝ) * ((d : ℝ) / n) ^ (d + 1)) * (2 * Real.pi) ^ d := by
        gcongr
    _ = 2 * (2 * Real.pi) ^ d * (Nat.factorial (d + 1) : ℝ)
          * ((d : ℝ) ^ (d + 1) * (n : ℝ) ^ (-((d + 1 : ℕ) : ℝ))) := by
        rw [hdn]; ring
    _ ≤ 2 * (2 * Real.pi) ^ d * (Nat.factorial (d + 1) : ℝ)
          * ((d : ℝ) ^ (d + 1) * (n : ℝ) ^ (-((d : ℝ) + 2) / 2)) := by
        gcongr
    _ = (2 * (2 * Real.pi) ^ d * (Nat.factorial (d + 1) : ℝ) * (d : ℝ) ^ (d + 1))
          * (n : ℝ) ^ (-((d : ℝ) + 2) / 2) := by ring

/-- The one-coordinate factor of the majorant off the Gaussian region. -/
private def offFactor (b t : ℝ) : ℝ :=
  Set.indicator {t : ℝ | Real.pi / 2 < |t|} (fun t => Real.exp (-b * (Real.pi - |t|) ^ 2)) t

/-- Each coordinate summand in the second part of `offBound` has torus integral `(2d)⁻¹ A B^{d-1}`, where `A` and `B` are the weighted and unweighted one-dimensional integrals. -/
private lemma integral_offBound_summand_eq (b : ℝ) (j : Fin d) :
    ∫ θ in torusBox d, (Real.pi - |θ j|) ^ 2 / (2 * d) * ∏ i, offFactor b (θ i)
      = (2 * (d : ℝ))⁻¹
          * ((∫ t in Set.Icc (-Real.pi) Real.pi, (Real.pi - |t|) ^ 2 * offFactor b t)
        * (∫ t in Set.Icc (-Real.pi) Real.pi, offFactor b t) ^ (d - 1)) := by
  set F : Fin d → ℝ → ℝ := fun i t =>
    if i = j then (Real.pi - |t|) ^ 2 * offFactor b t else offFactor b t with hF
  have hpt : ∀ θ : Fin d → ℝ, (Real.pi - |θ j|) ^ 2 / (2 * d) * ∏ i, offFactor b (θ i)
      = (2 * (d : ℝ))⁻¹ * ∏ i, F i (θ i) := by
    intro θ
    have h1 : ∏ i, F i (θ i)
        = (∏ i, (if i = j then (Real.pi - |θ i|) ^ 2 else 1)) * ∏ i, offFactor b (θ i) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      by_cases h : i = j <;> simp [hF, h]
    have h2 : ∏ i, (if i = j then (Real.pi - |θ i|) ^ 2 else 1) = (Real.pi - |θ j|) ^ 2 := by
      rw [Finset.prod_ite_eq' Finset.univ j (fun i => (Real.pi - |θ i|) ^ 2)]
      simp
    rw [h1, h2, div_eq_inv_mul]
    ring
  rw [setIntegral_congr_fun (torusBox_measurable d) (fun θ _ => hpt θ), integral_const_mul,
    ← torusMeasure_eq_restrict]
  unfold torusMeasure
  rw [MeasureTheory.integral_fintype_prod_eq_prod (fun i (t : ℝ) => F i t)]
  congr 1
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
  congr 1
  · simp [hF]
  · have hc : ∀ i ∈ Finset.univ.erase j, ∫ t in Set.Icc (-Real.pi) Real.pi, F i t
        = ∫ t in Set.Icc (-Real.pi) Real.pi, offFactor b t := by
      intro i hi
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      simp [hF, hij]
    rw [Finset.prod_congr rfl hc, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ j),
      Finset.card_univ, Fintype.card_fin]

/-- Each summand of the second part of `offBound` is integrable on the torus. -/
private lemma integrableOn_offBound_summand (hd : 1 ≤ d) (b : ℝ) (hb : 0 ≤ b) (j : Fin d) :
    IntegrableOn
        (fun θ : Fin d → ℝ => (Real.pi - |θ j|) ^ 2 / (2 * d) * ∏ i, offFactor b (θ i))
      (torusBox d) := by
  have : IsFiniteMeasure (volume.restrict (torusBox d)) :=
    isFiniteMeasure_restrict.mpr (by rw [volume_torusBox d]; exact ENNReal.ofReal_ne_top)
  have hset : MeasurableSet {t : ℝ | Real.pi / 2 < |t|} := by measurability
  have hmeas : Measurable fun θ : Fin d → ℝ =>
      (Real.pi - |θ j|) ^ 2 / (2 * d) * ∏ i, offFactor b (θ i) := by
    unfold offFactor; fun_prop
  refine Integrable.of_bound hmeas.aestronglyMeasurable (Real.pi ^ 2) ?_
  rw [ae_restrict_iff' (torusBox_measurable d)]
  filter_upwards with θ hθ
  have hmem := Set.mem_Icc.mp hθ
  have hθj : |θ j| ≤ Real.pi := by
    rw [abs_le]; exact ⟨by linarith [hmem.1 j], by linarith [hmem.2 j]⟩
  have hg : ∀ i, 0 ≤ offFactor b (θ i) ∧ offFactor b (θ i) ≤ 1 := by
    intro i
    unfold offFactor
    by_cases h : Real.pi / 2 < |θ i|
    · rw [Set.indicator_of_mem (s := {t : ℝ | Real.pi / 2 < |t|}) h]
      refine ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr ?_⟩
      nlinarith [sq_nonneg (Real.pi - |θ i|)]
    · rw [Set.indicator_of_notMem (s := {t : ℝ | Real.pi / 2 < |t|}) h]; norm_num
  have hprod0 : 0 ≤ ∏ i, offFactor b (θ i) := Finset.prod_nonneg fun i _ => (hg i).1
  have hprod1 : ∏ i, offFactor b (θ i) ≤ 1 := Finset.prod_le_one₀ (fun i _ => (hg i).1)
    (fun i _ => (hg i).2)
  have hsq : (Real.pi - |θ j|) ^ 2 ≤ Real.pi ^ 2 := by
    nlinarith [abs_nonneg (θ j), Real.pi_pos]
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hfrac : (Real.pi - |θ j|) ^ 2 / (2 * d) ≤ Real.pi ^ 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg (Real.pi - |θ j|)]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) hprod0)]
  calc (Real.pi - |θ j|) ^ 2 / (2 * d) * ∏ i, offFactor b (θ i)
      ≤ Real.pi ^ 2 * 1 := mul_le_mul hfrac hprod1 hprod0 (by positivity)
    _ = Real.pi ^ 2 := mul_one _

/-- The product bound `A B^{d-1}/2 ≤ K₂ n^{-(d+2)/2}` of the second part of `offBound`. -/
private lemma half_mul_pow_le (hd : 1 ≤ d) {c : ℝ} (hc : 0 < c) {n : ℕ}
    (hn : 1 ≤ n) {A B : ℝ}
    (hB0 : 0 ≤ B)
    (hA : A ≤ 4 / (c * n) * Real.sqrt (2 * Real.pi / (c * n)))
    (hB : B ≤ 2 * Real.sqrt (Real.pi / (c * n))) :
    A * B ^ (d - 1) / 2 ≤ 2 * Real.sqrt (2 * Real.pi) * (2 * Real.sqrt Real.pi) ^ (d - 1)
      * c ^ (-((d : ℝ) + 2) / 2) * (n : ℝ) ^ (-((d : ℝ) + 2) / 2) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set b : ℝ := c * n with hbdef
  have hb : 0 < b := by positivity
  set q : ℝ := Real.sqrt b with hq
  have hqpos : 0 < q := Real.sqrt_pos.mpr hb
  have hq2 : q ^ 2 = b := Real.sq_sqrt hb.le
  have hs1 : Real.sqrt (2 * Real.pi / b) = Real.sqrt (2 * Real.pi) / q := Real.sqrt_div' _ hb.le
  have hs2 : Real.sqrt (Real.pi / b) = Real.sqrt Real.pi / q := Real.sqrt_div' _ hb.le
  have hstep : A * B ^ (d - 1) / 2
      ≤ 4 / b * (Real.sqrt (2 * Real.pi) / q) * (2 * (Real.sqrt Real.pi / q)) ^ (d - 1) / 2 := by
    rw [← hs1, ← hs2]
    gcongr
  have hpowq : q ^ (d + 2) = b ^ (((d : ℝ) + 2) / 2) := by
    rw [hq, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hb.le]
    congr 1; push_cast; ring
  have halg : 4 / b * (Real.sqrt (2 * Real.pi) / q) * (2 * (Real.sqrt Real.pi / q)) ^ (d - 1) / 2
      = 2 * Real.sqrt (2 * Real.pi) * (2 * Real.sqrt Real.pi) ^ (d - 1) / q ^ (d + 2) := by
    have hd' : d + 2 = (d - 1) + 3 := by omega
    rw [hd', pow_add, ← hq2, mul_pow, div_pow]
    field_simp
    ring
  have hbpow : (q ^ (d + 2))⁻¹ = c ^ (-((d : ℝ) + 2) / 2)
      * (n : ℝ) ^ (-((d : ℝ) + 2) / 2) := by
    rw [hpowq, ← Real.rpow_neg hb.le, hbdef, Real.mul_rpow hc.le hnpos.le]
    congr 2 <;> ring
  calc A * B ^ (d - 1) / 2 ≤ _ := hstep
    _ = 2 * Real.sqrt (2 * Real.pi) * (2 * Real.sqrt Real.pi) ^ (d - 1) / q ^ (d + 2) := halg
    _ = _ := by rw [div_eq_mul_inv, hbpow]; ring

/-- The majorant off the Gaussian region integrates over the torus to `O(n^{-(d+2)/2})`. -/
theorem exists_integral_offBound_le (hd : 1 ≤ d) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n →
      IntegrableOn (offBound d n) (torusBox d) ∧
      ∫ θ in torusBox d, offBound d n θ ≤ K * (n : ℝ) ^ (-((d : ℝ) + 2) / 2) := by
  set c : ℝ := 2 / (Real.pi ^ 2 * d) with hc
  have hcpos : 0 < c := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  set K₁ : ℝ := 2 * (2 * Real.pi) ^ d * (Nat.factorial (d + 1) : ℝ)
      * (d : ℝ) ^ (d + 1) with hK₁
  set K₂ : ℝ := 2 * Real.sqrt (2 * Real.pi) * (2 * Real.sqrt Real.pi) ^ (d - 1)
    * c ^ (-((d : ℝ) + 2) / 2) with hK₂
  have hK₁pos : 0 < K₁ := by positivity
  have hK₂pos : 0 < K₂ := by positivity
  refine ⟨K₁ + K₂, by positivity, fun n hn => ⟨integrableOn_offBound hd n, ?_⟩⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set b : ℝ := c * n with hb
  have hbpos : 0 < b := by positivity
  have hoff : ∀ θ ∈ torusBox d, offBound d n θ = 2 * (1 - 1 / (d : ℝ)) ^ n
      + ∑ j, (Real.pi - |θ j|) ^ 2 / (2 * d) * ∏ i, offFactor b (θ i) := by
    intro θ _
    unfold offBound offFactor
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 1
    funext t
    rw [hb, hc]; ring_nf
  have : IsFiniteMeasure (volume.restrict (torusBox d)) :=
    isFiniteMeasure_restrict.mpr (by rw [volume_torusBox d]; exact ENNReal.ofReal_ne_top)
  have hsum_int : ∀ j ∈ (Finset.univ : Finset (Fin d)), IntegrableOn
      (fun θ : Fin d → ℝ => (Real.pi - |θ j|) ^ 2 / (2 * d) * ∏ i, offFactor b (θ i))
      (torusBox d) := fun j _ => integrableOn_offBound_summand hd b hbpos.le j
  rw [setIntegral_congr_fun (torusBox_measurable d) hoff,
    integral_add (integrable_const _) (integrable_finsetSum _ hsum_int),
    integral_finsetSum _ hsum_int, setIntegral_const]
  simp_rw [integral_offBound_summand_eq]
  set A : ℝ := ∫ t in Set.Icc (-Real.pi) Real.pi, (Real.pi - |t|) ^ 2 * offFactor b t with hA
  set B : ℝ := ∫ t in Set.Icc (-Real.pi) Real.pi, offFactor b t with hB
  have hA0 : 0 ≤ A := setIntegral_nonneg measurableSet_Icc fun t _ => by
    unfold offFactor
    exact mul_nonneg (sq_nonneg _) (Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _)
  have hB0 : 0 ≤ B := setIntegral_nonneg measurableSet_Icc fun t _ => by
    unfold offFactor
    exact Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _
  have hAle : A ≤ 4 / b * Real.sqrt (2 * Real.pi / b) := by
    rw [hA]; unfold offFactor; exact integral_sq_offFactor_le b hbpos
  have hBle : B ≤ 2 * Real.sqrt (Real.pi / b) := by
    rw [hB]; unfold offFactor; exact integral_offFactor_le b hbpos
  have hsecond := half_mul_pow_le (A := A) (B := B) hd hcpos hn hB0 (by rw [← hb]; exact hAle)
    (by rw [← hb]; exact hBle)
  have hfirst := offBound_const_le hd n hn
  have hvol : volume.real (torusBox d) = (2 * Real.pi) ^ d := by
    rw [Measure.real, volume_torusBox d, ENNReal.toReal_ofReal (by positivity)]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsumeq : ∑ _j : Fin d, (2 * (d : ℝ))⁻¹ * (A * B ^ (d - 1)) = A * B ^ (d - 1) / 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [hvol, smul_eq_mul, hsumeq]
  calc (2 * Real.pi) ^ d * (2 * (1 - 1 / (d : ℝ)) ^ n) + A * B ^ (d - 1) / 2
      ≤ K₁ * (n : ℝ) ^ (-((d : ℝ) + 2) / 2) + K₂
          * (n : ℝ) ^ (-((d : ℝ) + 2) / 2) := by
        refine add_le_add ?_ hsecond
        calc (2 * Real.pi) ^ d * (2 * (1 - 1 / (d : ℝ)) ^ n)
            = 2 * (1 - 1 / (d : ℝ)) ^ n * (2 * Real.pi) ^ d := by ring
          _ ≤ _ := hfirst
    _ = (K₁ + K₂) * (n : ℝ) ^ (-((d : ℝ) + 2) / 2) := by ring

/-- `offBound` is nonnegative on the torus. -/
theorem offBound_nonneg (hd : 1 ≤ d) (n : ℕ) (θ : Fin d → ℝ) : 0 ≤ offBound d n θ := by
  unfold offBound
  have h1 : (0 : ℝ) ≤ 1 - 1 / (d : ℝ) := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    rw [sub_nonneg, div_le_one (by linarith)]; exact this
  refine add_nonneg (by positivity) (Finset.sum_nonneg fun j _ => ?_)
  refine mul_nonneg (by positivity) (Finset.prod_nonneg fun i _ => ?_)
  exact Set.indicator_nonneg (fun t _ => (Real.exp_pos _).le) _

end LatticeProb.LocalCLT

end
