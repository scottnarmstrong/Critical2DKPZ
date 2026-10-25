/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
module

public import Mathlib
public import Critical2DKPZ.RandomWalk.Port.Walk.LocalCLT
public import Critical2DKPZ.RandomWalk.Port.Walk.GaussianFourier

/-!
# The paired heat kernel of the simple random walk in Fourier form

`p_n(x) + p_{n+1}(x)` is `(2π)^{-d}` times the torus integral of `χ_x φⁿ (1 + φ)`, where
`φ(θ) = d⁻¹ ∑ᵢ cos θᵢ` is the multiplier of one step and
`χ_x(θ) = ∏ₖ e^{iθₖxₖ}`. Pairing two consecutive times puts the factor `1 + φ` in the
integrand, which vanishes at the antipode `θ = (π, …, π)`; this is what lets the local limit
theorem avoid identifying the antipode contribution. The module also computes the Fourier
transform of the Gaussian, `∫_{ℝ^d} χ_x e^{-n|θ|²/(2d)} = (2π)^d ctGauss d n x`, as a
product of one-dimensional Gaussian integrals, and fixes the Gaussian region
`{θ : |θᵢ| ≤ π/2}` of the torus.
-/

@[expose] public section

open MeasureTheory Filter Topology

noncomputable section

namespace LatticeProb.LocalCLT

open ContinuousTime

variable {d : ℕ}

/-- The Gaussian region `{θ : |θᵢ| ≤ π/2 for all i}` of the torus. -/
def gaussRegion (d : ℕ) : Set (Fin d → ℝ) := {θ | ∀ i, |θ i| ≤ Real.pi / 2}

/-- The character `θ ↦ ∏ₖ e^{iθₖxₖ}` of the site `x`. -/
def character (x : Site d) (θ : Fin d → ℝ) : ℂ :=
  ∏ k, Complex.exp (↑(θ k * ↑(x k)) * Complex.I)

/-- The paired Fourier integrand `χ_x φⁿ (1 + φ)`. -/
def pairedIntegrand (x : Site d) (n : ℕ) (θ : Fin d → ℝ) : ℂ :=
  character x θ * ((charFn d θ : ℂ) ^ n * (1 + (charFn d θ : ℂ)))

/-- The Gaussian Fourier integrand `χ_x e^{-n|θ|²/(2d)}`. -/
def gaussCharacter (x : Site d) (n : ℕ) (θ : Fin d → ℝ) : ℂ :=
  character x θ * (Real.exp (-(n : ℝ) * (∑ i, θ i ^ 2) / (2 * d)) : ℂ)

/-- The Fourier representation of the heat kernel with the character and `charFn` written
explicitly. -/
private lemma srwHeat_eq_fourier' {d : ℕ} (hd : 1 ≤ d) (j : ℕ) (x : Site d) :
    (srwHeat d j x : ℂ)
      = (∫ θ in torusBox d, character x θ * (charFn d θ : ℂ) ^ j)
          / (2 * Real.pi) ^ d := by
  rw [srwHeat_eq_fourier hd]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  simp only [character, charFn]
  push_cast
  ring

/-- The paired kernel in Fourier form: `(2π)^d (p_n(x) + p_{n+1}(x))` is the torus integral of
`χ_x φⁿ (1 + φ)`. -/
theorem srwHeat_add_succ_eq_integral (hd : 1 ≤ d) (n : ℕ) (x : Site d) :
    ((srwHeat d n x + srwHeat d (n + 1) x : ℝ) : ℂ) * (2 * Real.pi) ^ d
      = ∫ θ in torusBox d,
          character x θ * ((charFn d θ : ℂ) ^ n * (1 + (charFn d θ : ℂ))) := by
  have hP0 : (2 * Real.pi : ℂ) ^ d ≠ 0 :=
    pow_ne_zero d (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have h1 := srwHeat_eq_fourier' hd n x
  have h2 := srwHeat_eq_fourier' hd (n + 1) x
  have hintn : Integrable (fun θ : Fin d → ℝ => character x θ * (charFn d θ : ℂ) ^ n)
      (volume.restrict (torusBox d)) := by
    refine (fourier_integrand_integrable d n x).congr ?_
    filter_upwards with θ
    simp only [character, charFn]
    push_cast
    ring
  have hintn1 : Integrable
      (fun θ : Fin d → ℝ => character x θ * (charFn d θ : ℂ) ^ (n + 1))
      (volume.restrict (torusBox d)) := by
    refine (fourier_integrand_integrable d (n + 1) x).congr ?_
    filter_upwards with θ
    simp only [character, charFn]
    push_cast
    ring
  have hsum : (∫ θ in torusBox d, character x θ * (charFn d θ : ℂ) ^ n)
      + (∫ θ in torusBox d, character x θ * (charFn d θ : ℂ) ^ (n + 1))
      = ∫ θ in torusBox d,
          character x θ * ((charFn d θ : ℂ) ^ n * (1 + (charFn d θ : ℂ))) := by
    rw [← integral_add hintn hintn1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    simp only []
    rw [pow_succ]
    ring
  rw [Complex.ofReal_add, add_mul, h1, h2, div_mul_cancel₀ _ hP0, div_mul_cancel₀ _ hP0]
  exact hsum

/-- A character has modulus one. -/
theorem norm_character (x : Site d) (θ : Fin d → ℝ) : ‖character x θ‖ = 1 := by
  rw [character, Complex.norm_prod]
  simp only [Complex.norm_exp_ofReal_mul_I, Finset.prod_const_one]

/-- Pointwise rewriting of the paired Gaussian Fourier multiplier as a product of the
one-dimensional Gaussian integrands. -/
private lemma character_mul_gauss_eq_prod (x : Site d) (n : ℕ) (θ : Fin d → ℝ) :
    character x θ * (Real.exp (-(n : ℝ) * (∑ i, θ i ^ 2) / (2 * d)) : ℂ)
      = ∏ k, gaussIntegrand ((n : ℝ) / d) (x k) ((θ k : ℂ) + 0 * Complex.I) := by
  have hB : (↑(-(n : ℝ) * (∑ i, θ i ^ 2) / (2 * d)) : ℂ)
      = -((((n : ℝ) / d : ℝ) : ℂ) / 2) * (∑ k, (θ k : ℂ) ^ 2) := by
    push_cast
    ring
  have hA : (∑ k, (↑(θ k * ↑(x k)) : ℂ) * Complex.I)
      = ∑ k, (x k : ℂ) * (θ k : ℂ) * Complex.I := by
    apply Finset.sum_congr rfl
    intro k _
    push_cast
    ring
  have hRHS : (∏ k, gaussIntegrand ((n : ℝ) / d) (x k) ((θ k : ℂ) + 0 * Complex.I))
      = Complex.exp (∑ k, (-((((n : ℝ) / d : ℝ) : ℂ) / 2) * (θ k : ℂ) ^ 2
          + (x k : ℂ) * (θ k : ℂ) * Complex.I)) := by
    simp only [gaussIntegrand]
    rw [← Complex.exp_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    simp only [zero_mul, add_zero]
    ring
  calc character x θ * (Real.exp (-(n : ℝ) * (∑ i, θ i ^ 2) / (2 * d)) : ℂ)
      = Complex.exp (∑ k, (↑(θ k * ↑(x k)) : ℂ) * Complex.I)
          * Complex.exp (↑(-(n : ℝ) * (∑ i, θ i ^ 2) / (2 * d)) : ℂ) := by
        rw [character, ← Complex.exp_sum, Complex.ofReal_exp]
    _ = Complex.exp ((∑ k, (↑(θ k * ↑(x k)) : ℂ) * Complex.I)
          + ↑(-(n : ℝ) * (∑ i, θ i ^ 2) / (2 * d))) := by
        rw [← Complex.exp_add]
    _ = Complex.exp (∑ k, (-((((n : ℝ) / d : ℝ) : ℂ) / 2) * (θ k : ℂ) ^ 2
          + (x k : ℂ) * (θ k : ℂ) * Complex.I)) := by
        congr 1
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hA, hB]
        abel
    _ = ∏ k, gaussIntegrand ((n : ℝ) / d) (x k) ((θ k : ℂ) + 0 * Complex.I) := hRHS.symm

/-- The Gaussian Fourier integrand `χ_x e^{-n|θ|²/(2d)}` is integrable on `ℝ^d`. -/
theorem integrable_character_mul_gauss (hd : 1 ≤ d) {n : ℕ} (hn : 0 < n) (x : Site d) :
    Integrable fun θ : Fin d → ℝ =>
      character x θ * (Real.exp (-(n : ℝ) * (∑ i, θ i ^ 2) / (2 * d)) : ℂ) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < (n : ℝ) / d := div_pos hn0 hd0
  have hpt := character_mul_gauss_eq_prod (d := d) x n
  rw [show (fun θ : Fin d → ℝ =>
        character x θ * (Real.exp (-(n : ℝ) * (∑ i, θ i ^ 2) / (2 * d)) : ℂ))
      = (fun θ => ∏ k, gaussIntegrand ((n : ℝ) / d) (x k) ((θ k : ℂ) + 0 * Complex.I))
      from funext hpt]
  exact Integrable.fintype_prod (fun k => integrable_gaussIntegrand_shift hs (x k) 0)

/-- The Fourier transform of the Gaussian:
`∫_{ℝ^d} χ_x e^{-n|θ|²/(2d)} = (2π)^d ctGauss d n x`,
a product of one-dimensional Gaussian integrals. -/
theorem integral_character_mul_gauss (hd : 1 ≤ d) {n : ℕ} (hn : 0 < n) (x : Site d) :
    ∫ θ : Fin d → ℝ,
        character x θ * (Real.exp (-(n : ℝ) * (∑ i, θ i ^ 2) / (2 * d)) : ℂ)
      = (2 * Real.pi) ^ d * ctGauss d n x := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < (n : ℝ) / d := div_pos hn0 hd0
  have hpt := character_mul_gauss_eq_prod (d := d) x n
  rw [show (fun θ : Fin d → ℝ =>
        character x θ * (Real.exp (-(n : ℝ) * (∑ i, θ i ^ 2) / (2 * d)) : ℂ))
      = (fun θ => ∏ k, gaussIntegrand ((n : ℝ) / d) (x k) ((θ k : ℂ) + 0 * Complex.I))
      from funext hpt]
  rw [integral_fintype_prod_volume_eq_prod
    (f := fun k (t : ℝ) => gaussIntegrand ((n : ℝ) / d) (x k) ((t : ℂ) + 0 * Complex.I))]
  have hfactor : ∀ k : Fin d,
      (∫ t : ℝ, gaussIntegrand ((n : ℝ) / d) (x k) (t + 0 * Complex.I))
        = (2 * Real.pi : ℂ) * lineGauss ((n : ℝ) / d) (x k) :=
    fun k => integral_gaussIntegrand_shift hs (x k) 0
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ctGauss, Complex.ofReal_prod]

/-- The Gaussian region is measurable. -/
theorem measurableSet_gaussRegion (d : ℕ) : MeasurableSet (gaussRegion d) := by
  unfold gaussRegion; measurability

/-- The Gaussian region lies in the torus box. -/
theorem gaussRegion_subset_torusBox (d : ℕ) : gaussRegion d ⊆ torusBox d := by
  intro θ hθ
  refine ⟨fun i => ?_, fun i => ?_⟩ <;>
    have := hθ i <;> rw [abs_le] at this <;> linarith [Real.pi_pos, this.1, this.2]

/-- The paired Fourier integrand is integrable on the torus. -/
theorem integrableOn_pairedIntegrand (x : Site d) (n : ℕ) :
    IntegrableOn (pairedIntegrand x n) (torusBox d) := by
  have h : Continuous (pairedIntegrand x n) := by
    unfold pairedIntegrand character charFn; fun_prop
  exact h.integrableOn_Icc

end LatticeProb.LocalCLT

end
