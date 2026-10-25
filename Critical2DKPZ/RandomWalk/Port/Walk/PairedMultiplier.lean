/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
module

public import Mathlib
public import Critical2DKPZ.RandomWalk.Port.Walk.PairedFourier

/-!
# The paired Fourier multiplier on the Gaussian region

On the Gaussian region `{θ : |θᵢ| ≤ π/2}` the multiplier `φ(θ) = d⁻¹ ∑ᵢ cos θᵢ`
is nonnegative, below `e^{-2|θ|²/(π²d)}`, and the Gaussian `e^{-|θ|²/(2d)}` up to `|θ|⁴`.
With the elementary bound `|aⁿ - bⁿ| ≤ n|a - b| max(a, b)^{n-1}` this makes the paired
multiplier `φⁿ(1 + φ)` twice the Gaussian `e^{-n|θ|²/(2d)}` up to
`K(n|θ|⁴ + |θ|²)e^{-cn|θ|²}` (`exists_abs_charFn_pow_mul_sub_le`).
-/

@[expose] public section

open MeasureTheory Filter Topology

noncomputable section

namespace LatticeProb.LocalCLT

open ContinuousTime

variable {d : ℕ}

/-- The multiplier is nonnegative on the Gaussian region. -/
theorem charFn_nonneg_of_mem_gaussRegion {θ : Fin d → ℝ} (hθ : θ ∈ gaussRegion d) :
    0 ≤ charFn d θ := by
  have hθ' : ∀ i, |θ i| ≤ Real.pi / 2 := by
    simpa only [gaussRegion, Set.mem_ofPred_eq] using hθ
  rw [charFn]
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro i _
    have h := hθ' i
    rw [abs_le] at h
    exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le h.1 h.2
  · positivity

/-- On the Gaussian region `φ(θ) ≤ exp(-2|θ|²/(π² d))`. -/
theorem charFn_le_exp_of_mem_gaussRegion (hd : 1 ≤ d) {θ : Fin d → ℝ}
    (hθ : θ ∈ gaussRegion d) :
    charFn d θ ≤ Real.exp (-(2 / (Real.pi ^ 2 * d)) * ∑ i, θ i ^ 2) := by
  have hθ' : ∀ i, |θ i| ≤ Real.pi / 2 := by
    simpa only [gaussRegion, Set.mem_ofPred_eq] using hθ
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hcos_le : ∑ i, Real.cos (θ i) ≤ ∑ i, (1 - 2 / Real.pi ^ 2 * θ i ^ 2) := by
    apply Finset.sum_le_sum
    intro i _
    apply Real.cos_le_one_sub_mul_cos_sq
    have hi := hθ' i
    rw [abs_le] at hi ⊢
    constructor <;> linarith [Real.pi_pos, hi.1, hi.2]
  have hcos : ∑ i, Real.cos (θ i) ≤ (d : ℝ) - (2 / Real.pi ^ 2) * ∑ i, θ i ^ 2 := by
    calc
      ∑ i, Real.cos (θ i) ≤ ∑ i, (1 - 2 / Real.pi ^ 2 * θ i ^ 2) := hcos_le
      _ = (d : ℝ) - (2 / Real.pi ^ 2) * ∑ i, θ i ^ 2 := by
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              mul_one]
  have hcalc : charFn d θ ≤ 1 - (2 / (Real.pi ^ 2 * d)) * ∑ i, θ i ^ 2 := by
    rw [charFn]
    calc
      (∑ i, Real.cos (θ i)) / d ≤ ((d : ℝ) - (2 / Real.pi ^ 2) * ∑ i, θ i ^ 2) / d :=
            div_le_div_of_nonneg_right hcos hd0.le
      _ = 1 - (2 / (Real.pi ^ 2 * d)) * ∑ i, θ i ^ 2 := by
            field_simp
  calc
    charFn d θ ≤ 1 - (2 / (Real.pi ^ 2 * d)) * ∑ i, θ i ^ 2 := hcalc
    _ ≤ Real.exp (-(2 / (Real.pi ^ 2 * d)) * ∑ i, θ i ^ 2) := by
          have := Real.add_one_le_exp (-(2 / (Real.pi ^ 2 * d)) * ∑ i, θ i ^ 2)
          linarith

/-- For `u ≥ 0`, `Real.exp (-u) ≤ 1 - u + u²/2`. -/
private lemma exp_neg_sub_one_le_sq (u : ℝ) (hu : 0 ≤ u) :
    Real.exp (-u) ≤ 1 - u + u ^ 2 / 2 := by
  have h1 : 1 + u + u ^ 2 / 2 + u ^ 3 / 6 ≤ Real.exp u := by
    have h := Real.sum_le_exp_of_nonneg hu 4
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hA0 : 0 ≤ 1 - u + u ^ 2 / 2 := by nlinarith [sq_nonneg (u - 1)]
  have hmul : 1 ≤ (1 - u + u ^ 2 / 2) * (1 + u + u ^ 2 / 2 + u ^ 3 / 6) := by
    have hexpand : (1 - u + u ^ 2 / 2) * (1 + u + u ^ 2 / 2 + u ^ 3 / 6)
        = 1 + u ^ 3 / 6 + u ^ 4 / 12 + u ^ 5 / 12 := by ring
    rw [hexpand]
    have h3 : 0 ≤ u ^ 3 := by positivity
    have h4 : 0 ≤ u ^ 4 := by positivity
    have h5 : 0 ≤ u ^ 5 := by positivity
    linarith
  have hAe : 1 ≤ (1 - u + u ^ 2 / 2) * Real.exp u :=
    le_trans hmul (mul_le_mul_of_nonneg_left h1 hA0)
  calc
    Real.exp (-u) = 1 * Real.exp (-u) := (one_mul _).symm
    _ ≤ ((1 - u + u ^ 2 / 2) * Real.exp u) * Real.exp (-u) :=
          mul_le_mul_of_nonneg_right hAe (Real.exp_nonneg _)
    _ = 1 - u + u ^ 2 / 2 := by
          rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

/-- The cosine remainder after subtraction of the quadratic Taylor polynomial is nonnegative when summed over the coordinates. -/
private lemma sum_cos_sub_one_add_nonneg {d : ℕ} {θ : Fin d → ℝ} :
    0 ≤ ∑ i, (Real.cos (θ i) - 1 + θ i ^ 2 / 2) := by
  apply Finset.sum_nonneg
  intro i _
  have h := Real.one_sub_sq_div_two_le_cos (x := θ i)
  linarith

/-- The sum of coordinatewise quadratic cosine remainders equals the cosine sum minus the dimension plus half the sum of squared coordinates. -/
private lemma sum_cos_sub_one_add_eq {d : ℕ} (θ : Fin d → ℝ) :
    (∑ i, (Real.cos (θ i) - 1 + θ i ^ 2 / 2))
      = (∑ i, Real.cos (θ i)) - (d : ℝ) + (∑ i, θ i ^ 2) / 2 := by
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h1 : (∑ i : Fin d, (1 : ℝ)) = (d : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have h2 : (∑ i : Fin d, θ i ^ 2 / 2) = (∑ i, θ i ^ 2) / 2 := by
    rw [Finset.sum_div]
  rw [h1, h2]

/-- The sum of quadratic cosine remainders is bounded by `(∑ θᵢ²)²/24`. -/
private lemma sum_cos_sub_one_add_le {d : ℕ} {θ : Fin d → ℝ}
    (hθ : ∀ i, |θ i| ≤ Real.pi / 2) :
    ∑ i, (Real.cos (θ i) - 1 + θ i ^ 2 / 2) ≤ (∑ i, θ i ^ 2) ^ 2 / 24 := by
  have h1 : ∑ i, (Real.cos (θ i) - 1 + θ i ^ 2 / 2) ≤ ∑ i, θ i ^ 4 / 24 := by
    apply Finset.sum_le_sum
    intro i _
    have hi := hθ i
    rw [abs_le] at hi
    have hq := LocalCLT.cos_le_one_sub_half_sq_add_quartic (θ i) (by
      rw [abs_le]
      exact ⟨by linarith [Real.pi_pos, hi.1], by linarith [Real.pi_pos, hi.2]⟩)
    linarith
  have h2 : ∑ i, θ i ^ 4 / 24 ≤ (∑ i, θ i ^ 2) ^ 2 / 24 := by
    rw [← Finset.sum_div]
    apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 24)
    have hsq : (∑ i, θ i ^ 4) = ∑ i, (θ i ^ 2) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsq]
    exact Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
      (f := fun i : Fin d => θ i ^ 2) (fun i _ => sq_nonneg _)
  linarith

/-- On the Gaussian region the multiplier is the Gaussian up to `|θ|⁴`:
`|φ(θ) - e^{-|θ|²/(2d)}| ≤ |θ|⁴`. -/
theorem abs_charFn_sub_exp_le (hd : 1 ≤ d) {θ : Fin d → ℝ} (hθ : θ ∈ gaussRegion d) :
    |charFn d θ - Real.exp (-(∑ i, θ i ^ 2) / (2 * d))| ≤ (∑ i, θ i ^ 2) ^ 2 := by
  have hθ' : ∀ i, |θ i| ≤ Real.pi / 2 := by
    simpa only [gaussRegion, Set.mem_ofPred_eq] using hθ
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set S : ℝ := ∑ i, θ i ^ 2 with hS
  have hS_nonneg : 0 ≤ S := by rw [hS]; positivity
  set u : ℝ := S / (2 * d) with hu
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hgoal_exp : -(S) / (2 * d) = -u := by rw [hu, neg_div]
  rw [hgoal_exp]
  have hT_nonneg : 0 ≤ ∑ i, (Real.cos (θ i) - 1 + θ i ^ 2 / 2) :=
    sum_cos_sub_one_add_nonneg
  have hT_le : ∑ i, (Real.cos (θ i) - 1 + θ i ^ 2 / 2) ≤ S ^ 2 / 24 := by
    rw [hS]
    exact sum_cos_sub_one_add_le hθ'
  have ha_eq : charFn d θ - (1 - u) = (∑ i, (Real.cos (θ i) - 1 + θ i ^ 2 / 2)) / d := by
    rw [charFn, hu, hS, sum_cos_sub_one_add_eq]
    field_simp
    ring
  have ha_nonneg : 0 ≤ charFn d θ - (1 - u) := by
    rw [ha_eq]
    exact div_nonneg hT_nonneg hd0.le
  have ha_le : charFn d θ - (1 - u) ≤ S ^ 2 / 24 := by
    rw [ha_eq]
    calc
      (∑ i, (Real.cos (θ i) - 1 + θ i ^ 2 / 2)) / d ≤ (S ^ 2 / 24) / d :=
            div_le_div_of_nonneg_right hT_le hd0.le
      _ ≤ S ^ 2 / 24 := by
            rw [div_le_iff₀ hd0]
            have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
            nlinarith [sq_nonneg S, hd1]
  have hb_le : Real.exp (-u) - (1 - u) ≤ S ^ 2 / 8 := by
    have h1 : Real.exp (-u) ≤ 1 - u + u ^ 2 / 2 := exp_neg_sub_one_le_sq u hu0
    have h2 : u ^ 2 / 2 = S ^ 2 / (8 * d ^ 2) := by
      rw [hu]
      field_simp
      ring
    have h3 : S ^ 2 / (8 * d ^ 2) ≤ S ^ 2 / 8 := by
      apply div_le_div_of_nonneg_left (sq_nonneg S) (by norm_num : (0 : ℝ) < 8)
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
      nlinarith [hd1]
    linarith
  have h1 : |charFn d θ - (1 - u)| ≤ S ^ 2 / 24 := by
    rw [abs_of_nonneg ha_nonneg]
    exact ha_le
  have h2 : |(1 - u) - Real.exp (-u)| ≤ S ^ 2 / 8 := by
    have hb_nonneg : 0 ≤ Real.exp (-u) - (1 - u) := by
      have := Real.one_sub_le_exp_neg u
      linarith
    rw [abs_of_nonpos (by linarith : (1 - u) - Real.exp (-u) ≤ 0)]
    linarith
  calc
    |charFn d θ - Real.exp (-u)|
        = |(charFn d θ - (1 - u)) + ((1 - u) - Real.exp (-u))| := by
          congr 1
          ring
    _ ≤ |charFn d θ - (1 - u)| + |(1 - u) - Real.exp (-u)| := abs_add_le _ _
    _ ≤ S ^ 2 / 24 + S ^ 2 / 8 := add_le_add h1 h2
    _ ≤ S ^ 2 := by nlinarith [sq_nonneg S]

/-- `|aⁿ - bⁿ| ≤ n |a - b| max(a, b)^{n-1}` for `a, b ≥ 0`. -/
theorem abs_pow_sub_pow_le_mul_max {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    |a ^ n - b ^ n| ≤ n * |a - b| * max a b ^ (n - 1) := by
  set M := max a b with hM
  have haM : a ≤ M := le_max_left a b
  have hbM : b ≤ M := le_max_right a b
  rw [← geom_sum₂_mul a b n, abs_mul]
  have hsum : ∑ i ∈ Finset.range n, |a ^ i * b ^ (n - 1 - i)| ≤ n * M ^ (n - 1) := by
    calc ∑ i ∈ Finset.range n, |a ^ i * b ^ (n - 1 - i)|
        ≤ ∑ _i ∈ Finset.range n, M ^ (n - 1) := by
          apply Finset.sum_le_sum
          intro i hi
          have hi' : i < n := Finset.mem_range.mp hi
          rw [abs_of_nonneg (mul_nonneg (pow_nonneg ha i) (pow_nonneg hb (n - 1 - i)))]
          calc a ^ i * b ^ (n - 1 - i) ≤ M ^ i * M ^ (n - 1 - i) := by
                gcongr
            _ = M ^ (n - 1) := by
                rw [← pow_add]
                congr 1
                omega
      _ = n * M ^ (n - 1) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have habs : |∑ i ∈ Finset.range n, a ^ i * b ^ (n - 1 - i)| ≤ n * M ^ (n - 1) :=
    le_trans (Finset.abs_sum_le_sum_abs _ _) hsum
  calc |∑ i ∈ Finset.range n, a ^ i * b ^ (n - 1 - i)| * |a - b|
      ≤ (n * M ^ (n - 1)) * |a - b| := mul_le_mul_of_nonneg_right habs (abs_nonneg _)
    _ = n * |a - b| * M ^ (n - 1) := by ring

/-- `|e^{-(n+1)u} - e^{-nu}| ≤ u e^{-nu}` for `u ≥ 0`. -/
theorem abs_exp_succ_sub_exp_le {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    |Real.exp (-((n : ℝ) + 1) * u) - Real.exp (-(n : ℝ) * u)|
      ≤ u * Real.exp (-(n : ℝ) * u) := by
  have harg : -((n : ℝ) + 1) * u = -(n : ℝ) * u + (-u) := by ring
  rw [harg, Real.exp_add]
  have hfac : Real.exp (-(n : ℝ) * u) * Real.exp (-u) - Real.exp (-(n : ℝ) * u)
      = Real.exp (-(n : ℝ) * u) * (Real.exp (-u) - 1) := by ring
  rw [hfac, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hle : Real.exp (-u) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  have habs : |Real.exp (-u) - 1| = 1 - Real.exp (-u) := by
    rw [abs_of_nonpos (by linarith)]; ring
  rw [habs]
  have h1m : 1 - Real.exp (-u) ≤ u := by
    have := Real.add_one_le_exp (-u)
    linarith
  calc Real.exp (-(n : ℝ) * u) * (1 - Real.exp (-u))
      ≤ Real.exp (-(n : ℝ) * u) * u := mul_le_mul_of_nonneg_left h1m (Real.exp_pos _).le
    _ = u * Real.exp (-(n : ℝ) * u) := by ring

/-- On the Gaussian region the paired multiplier is twice the Gaussian up to
`K (n|θ|⁴ + |θ|²) e^{-cn|θ|²}`. -/
theorem exists_abs_charFn_pow_mul_sub_le (hd : 1 ≤ d) :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧ ∀ n : ℕ, 1 ≤ n → ∀ θ ∈ gaussRegion d,
      |charFn d θ ^ n * (1 + charFn d θ)
          - 2 * Real.exp (-(n : ℝ) * (∑ i, θ i ^ 2) / (2 * d))|
        ≤ K * ((n : ℝ) * (∑ i, θ i ^ 2) ^ 2 + ∑ i, θ i ^ 2)
          * Real.exp (-c * n * ∑ i, θ i ^ 2) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  set c : ℝ := 2 / (Real.pi ^ 2 * d) with hc
  have hcpos : 0 < c := by positivity
  refine ⟨3 * Real.exp (1 / 2) + 1, c, by positivity, hcpos, fun n hn θ hθ => ?_⟩
  set S := ∑ i, θ i ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hSle : S ≤ d * (Real.pi / 2) ^ 2 := by
    have h : ∀ i, θ i ^ 2 ≤ (Real.pi / 2) ^ 2 := fun i => by
      have := hθ i
      nlinarith [abs_nonneg (θ i), sq_abs (θ i)]
    calc S ≤ ∑ _i : Fin d, (Real.pi / 2) ^ 2 := Finset.sum_le_sum fun i _ => h i
      _ = d * (Real.pi / 2) ^ 2 := by simp
  have hcS : c * S ≤ 1 / 2 := by
    rw [hc, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  set φ := charFn d θ with hφ
  set M := Real.exp (-c * S) with hM
  set b := Real.exp (-S / (2 * d)) with hb
  have hφ0 : 0 ≤ φ := charFn_nonneg_of_mem_gaussRegion hθ
  have hφM : φ ≤ M := by
    rw [hφ, hM]
    have h := charFn_le_exp_of_mem_gaussRegion hd hθ
    simpa [hc, hS] using h
  have hb0 : 0 ≤ b := (Real.exp_pos _).le
  have hbM : b ≤ M := by
    rw [hb, hM]
    apply Real.exp_le_exp.mpr
    rw [hc, neg_div, neg_mul, neg_le_neg_iff, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity)
      (by positivity)]
    have hpi : (4 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    nlinarith [mul_nonneg (sub_nonneg.mpr hpi) (mul_nonneg hS0 hdpos.le)]
  have hM0 : 0 ≤ M := (Real.exp_pos _).le
  have hM1 : M ≤ 1 := by
    rw [hM, Real.exp_le_one_iff]; nlinarith
  have hmax : max φ b ≤ M := max_le hφM hbM
  have hdiff : |φ - b| ≤ S ^ 2 := by
    have h := abs_charFn_sub_exp_le hd hθ
    simpa [hφ, hb, hS] using h
  -- The error splits into two multiplier-power differences and a consecutive Gaussian-power difference.
  have hbn : ∀ m : ℕ, b ^ m = Real.exp (-(m : ℝ) * S / (2 * d)) := by
    intro m
    rw [hb, ← Real.exp_nat_mul]
    congr 1
    ring
  have hMn : ∀ m : ℕ, M ^ m = Real.exp (-c * m * S) := by
    intro m
    rw [hM, ← Real.exp_nat_mul]
    congr 1
    ring
  have hshift : M ^ (n - 1) ≤ Real.exp (1 / 2) * M ^ n := by
    have hn1 : n = (n - 1) + 1 := by omega
    have hM' : M ^ n = M ^ (n - 1) * M := by rw [← pow_succ, ← hn1]
    rw [hM']
    have hMpos : 0 < M := Real.exp_pos _
    have hinv : 1 ≤ Real.exp (1 / 2) * M := by
      rw [hM, ← Real.exp_add]
      exact Real.one_le_exp (by linarith)
    calc M ^ (n - 1) = M ^ (n - 1) * 1 := (mul_one _).symm
      _ ≤ M ^ (n - 1) * (Real.exp (1 / 2) * M) :=
          mul_le_mul_of_nonneg_left hinv (pow_nonneg hM0 _)
      _ = Real.exp (1 / 2) * (M ^ (n - 1) * M) := by ring
  have h1 : |φ ^ n - b ^ n| ≤ n * S ^ 2 * M ^ (n - 1) := by
    calc |φ ^ n - b ^ n| ≤ n * |φ - b| * max φ b ^ (n - 1) :=
          abs_pow_sub_pow_le_mul_max hφ0 hb0 n
      _ ≤ n * S ^ 2 * M ^ (n - 1) := by
          gcongr
  have h2 : |φ ^ (n + 1) - b ^ (n + 1)| ≤ (n + 1) * S ^ 2 * M ^ (n - 1) := by
    calc |φ ^ (n + 1) - b ^ (n + 1)|
        ≤ ((n + 1 : ℕ) : ℝ) * |φ - b| * max φ b ^ (n + 1 - 1) :=
          abs_pow_sub_pow_le_mul_max hφ0 hb0 (n + 1)
      _ ≤ ((n + 1 : ℕ) : ℝ) * S ^ 2 * M ^ (n - 1) := by
          have hpow : max φ b ^ (n + 1 - 1) ≤ M ^ (n - 1) := by
            rw [Nat.add_sub_cancel]
            calc max φ b ^ n ≤ M ^ n := pow_le_pow_left₀ (le_max_of_le_left hφ0) hmax n
              _ ≤ M ^ (n - 1) := pow_le_pow_of_le_one hM0 hM1 (Nat.sub_le n 1)
          gcongr
      _ = (n + 1) * S ^ 2 * M ^ (n - 1) := by push_cast; ring
  have h3 : |b ^ (n + 1) - b ^ n| ≤ S * M ^ n := by
    rw [hbn, hbn]
    have hu : 0 ≤ S / (2 * d) := by positivity
    have h := abs_exp_succ_sub_exp_le hu n
    have e1 : -(((n + 1 : ℕ) : ℝ)) * S / (2 * d) = -((n : ℝ) + 1) * (S / (2 * d)) := by
      push_cast; ring
    have e2 : -(n : ℝ) * S / (2 * d) = -(n : ℝ) * (S / (2 * d)) := by ring
    rw [e1, e2]
    refine h.trans ?_
    have hexp : Real.exp (-(n : ℝ) * (S / (2 * d))) ≤ M ^ n := by
      have := pow_le_pow_left₀ hb0 hbM n
      rw [hbn n] at this
      calc Real.exp (-(n : ℝ) * (S / (2 * d))) = Real.exp (-(n : ℝ) * S / (2 * d)) := by ring_nf
        _ ≤ M ^ n := this
    have hSd : S / (2 * d) ≤ S := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    exact mul_le_mul hSd hexp (Real.exp_pos _).le hS0
  have hsplit : φ ^ n * (1 + φ) - 2 * Real.exp (-(n : ℝ) * S / (2 * d))
      = (φ ^ n - b ^ n) + (φ ^ (n + 1) - b ^ (n + 1)) + (b ^ (n + 1) - b ^ n) := by
    rw [← hbn n]; ring
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [hsplit, ← hMn n]
  calc |(φ ^ n - b ^ n) + (φ ^ (n + 1) - b ^ (n + 1)) + (b ^ (n + 1) - b ^ n)|
      ≤ |φ ^ n - b ^ n| + |φ ^ (n + 1) - b ^ (n + 1)| + |b ^ (n + 1) - b ^ n| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ n * S ^ 2 * M ^ (n - 1) + (n + 1) * S ^ 2 * M ^ (n - 1) + S * M ^ n := by
        gcongr
    _ ≤ (2 * n + 1) * S ^ 2 * (Real.exp (1 / 2) * M ^ n) + S * M ^ n := by
        have : n * S ^ 2 * M ^ (n - 1) + (n + 1) * S ^ 2 * M ^ (n - 1)
            = (2 * n + 1) * S ^ 2 * M ^ (n - 1) := by ring
        rw [this]
        gcongr
    _ ≤ (3 * Real.exp (1 / 2) + 1) * ((n : ℝ) * S ^ 2 + S) * M ^ n := by
        have hMn0 : 0 ≤ M ^ n := pow_nonneg hM0 n
        have he : 0 ≤ Real.exp (1 / 2) := (Real.exp_pos _).le
        have hA : 0 ≤ ((n : ℝ) - 1) * Real.exp (1 / 2) * S ^ 2 * M ^ n := by
          have : (0 : ℝ) ≤ n - 1 := by linarith
          positivity
        have hB : 0 ≤ Real.exp (1 / 2) * S * M ^ n := by positivity
        have hC : 0 ≤ (n : ℝ) * S ^ 2 * M ^ n := by positivity
        linear_combination hA + 3 * hB + hC

end LatticeProb.LocalCLT

end
