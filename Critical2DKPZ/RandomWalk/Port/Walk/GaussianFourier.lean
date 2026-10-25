/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
module

public import Mathlib
public import Critical2DKPZ.RandomWalk.Port.Site

/-! # Gaussian Fourier integrals

The complex Gaussian integral along any horizontal line equals the Gaussian density
at the integer frequency times `2π`. -/

@[expose] public section

open MeasureTheory

noncomputable section

namespace LatticeProb.ContinuousTime

/-- The Gaussian kernel of variance `s` at an integer, `(2πs)^{-1/2} e^{-k²/(2s)}`. -/
def lineGauss (s : ℝ) (k : ℤ) : ℝ :=
  (Real.sqrt (2 * Real.pi * s))⁻¹ * Real.exp (-(k : ℝ) ^ 2 / (2 * s))

/-- The entire Gaussian integrand `z ↦ e^{-s z²/2 + ikz}`. -/
def gaussIntegrand (s : ℝ) (k : ℤ) (z : ℂ) : ℂ :=
  Complex.exp (-(s : ℂ) / 2 * z ^ 2 + (k : ℂ) * z * Complex.I)

/-- Rewrites `gaussIntegrand s k` at the vertically shifted argument `θ + l I`
as a complex quadratic exponential in `θ` with coefficients `b = -s/2`,
`c = k I - s l I` and `d = s l²/2 - k l`. -/
private lemma gaussIntegrand_shift_expand (s : ℝ) (k : ℤ) (l θ : ℝ) :
    gaussIntegrand s k (θ + l * Complex.I) =
      Complex.exp ((-(s : ℂ) / 2) * θ ^ 2 +
        ((k : ℂ) * Complex.I - (s : ℂ) * (l : ℂ) * Complex.I) * θ +
        ((s : ℂ) * (l : ℂ) ^ 2 / 2 - (k : ℂ) * (l : ℂ))) := by
  simp only [gaussIntegrand]
  congr 1
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The real part `-s/2` of the quadratic coefficient is negative when `s > 0`. -/
private lemma gaussIntegrand_neg_re {s : ℝ} (hs : 0 < s) :
    ((-(s : ℂ) / 2).re < 0) := by
  rw [show (-(s : ℂ) / 2) = (((-(s / 2)) : ℝ) : ℂ) by push_cast; ring]
  simp only [Complex.ofReal_re]
  linarith

/-- The shifted Gaussian exponent `d - c²/(4b)` simplifies to `-k²/(2s)`; the
`l`-terms cancel. -/
private lemma gauss_exponent_eq (s : ℝ) (hs : s ≠ 0) (k : ℤ) (l : ℝ) :
    ((s : ℂ) * (l : ℂ) ^ 2 / 2 - (k : ℂ) * (l : ℂ)) -
      ((k : ℂ) * Complex.I - (s : ℂ) * (l : ℂ) * Complex.I) ^ 2 /
        (4 * (-(s : ℂ) / 2)) = -(k : ℂ) ^ 2 / (2 * (s : ℂ)) := by
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  field_simp [hsC]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The complex Gaussian prefactor `(π / (s/2))^(1/2)` is the complex cast of
`Real.sqrt (2π/s)`. -/
private lemma gauss_coeff_sqrt (s : ℝ) (hs : 0 < s) :
    (Real.pi / (-( -(s : ℂ) / 2))) ^ (1 / 2 : ℂ) =
      ((Real.sqrt (2 * Real.pi / s) : ℝ) : ℂ) := by
  have h1 : (-( -(s : ℂ) / 2)) = ((s / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h1, ← Complex.ofReal_div]
  have h2 : Real.pi / (s / 2) = 2 * Real.pi / s := by
    field_simp
  rw [h2]
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
  rw [← Complex.ofReal_cpow (by positivity : (0:ℝ) ≤ 2 * Real.pi / s) (1/2 : ℝ)]
  rw [Real.sqrt_eq_rpow]

/-- The Gaussian integral value `√(2π/s) e^{-k²/(2s)}` equals `2π * lineGauss s k`. -/
private lemma lineGauss_coeff (s : ℝ) (hs : 0 < s) (k : ℤ) :
    ((Real.sqrt (2 * Real.pi / s) : ℝ) : ℂ) * Complex.exp (-(k : ℂ) ^ 2 / (2 * (s : ℂ))) =
      (2 * Real.pi : ℂ) * lineGauss s k := by
  have hpos1 : 0 ≤ 2 * Real.pi / s := by positivity
  have hpos2 : 0 < 2 * Real.pi * s := by positivity
  have hsq : Real.sqrt (2 * Real.pi / s) * Real.sqrt (2 * Real.pi * s) = 2 * Real.pi := by
    rw [← Real.sqrt_mul hpos1 (2 * Real.pi * s)]
    have hmul : (2 * Real.pi / s) * (2 * Real.pi * s) = (2 * Real.pi) ^ 2 := by
      field_simp
    rw [hmul, Real.sqrt_sq (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
  have hsqrt_ne : Real.sqrt (2 * Real.pi * s) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos2)
  have hreal : Real.sqrt (2 * Real.pi / s) * Real.exp (-(k : ℝ) ^ 2 / (2 * s)) =
      (2 * Real.pi) * lineGauss s k := by
    rw [lineGauss]
    field_simp [Real.exp_ne_zero, hsqrt_ne]
    linarith
  have hexp : -(k : ℂ) ^ 2 / (2 * (s : ℂ)) = (((-(k : ℝ) ^ 2 / (2 * s)) : ℝ) : ℂ) := by
    push_cast
    ring
  have hcexp : Complex.exp (-(k : ℂ) ^ 2 / (2 * (s : ℂ))) =
      ((Real.exp (-(k : ℝ) ^ 2 / (2 * s)) : ℝ) : ℂ) := by
    rw [hexp, ← Complex.ofReal_exp]
  rw [hcexp]
  rw [← Complex.ofReal_mul]
  rw [show (2 * Real.pi : ℂ) * ((lineGauss s k : ℝ) : ℂ) =
      ((2 * Real.pi * lineGauss s k : ℝ) : ℂ) by push_cast; ring]
  exact congrArg (fun x : ℝ => (x : ℂ)) hreal

/-- The Gaussian integrand integrates over every horizontal line `Im z = l` to `2π` times
the Gaussian kernel: the exponent is a complex quadratic in `θ`, and the `l`-terms cancel. -/
theorem integral_gaussIntegrand_shift {s : ℝ} (hs : 0 < s) (k : ℤ) (l : ℝ) :
    ∫ θ : ℝ, gaussIntegrand s k (θ + l * Complex.I)
      = (2 * Real.pi : ℂ) * lineGauss s k := by
  simp_rw [gaussIntegrand_shift_expand s k l]
  rw [integral_cexp_quadratic (gaussIntegrand_neg_re hs)
        ((k : ℂ) * Complex.I - (s : ℂ) * (l : ℂ) * Complex.I)
        ((s : ℂ) * (l : ℂ) ^ 2 / 2 - (k : ℂ) * (l : ℂ))]
  rw [gauss_exponent_eq s (ne_of_gt hs) k l, gauss_coeff_sqrt s hs]
  exact lineGauss_coeff s hs k

/-- The Gaussian integrand is integrable along every horizontal line. -/
theorem integrable_gaussIntegrand_shift {s : ℝ} (hs : 0 < s) (k : ℤ) (l : ℝ) :
    Integrable fun θ : ℝ => gaussIntegrand s k (θ + l * Complex.I) := by
  simp_rw [gaussIntegrand_shift_expand s k l]
  exact integrable_cexp_quadratic' (gaussIntegrand_neg_re hs)
    ((k : ℂ) * Complex.I - (s : ℂ) * (l : ℂ) * Complex.I)
    ((s : ℂ) * (l : ℂ) ^ 2 / 2 - (k : ℂ) * (l : ℂ))


/-- The product Gaussian with covariance `(t / d) I` for positive dimension and time. -/
def ctGauss (d : ℕ) (t : ℝ) (x : Site d) : ℝ := ∏ i, lineGauss (t / d) (x i)

end LatticeProb.ContinuousTime

end
