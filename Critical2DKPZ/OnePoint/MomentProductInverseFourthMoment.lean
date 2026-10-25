/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.OnePoint.BlockMomentAndTiltedRatioBounds
import Critical2DKPZ.OnePoint.FiniteProfileGaussian
import Mathlib.Tactic

/-! # Fourth inverse moments of block masses -/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory

namespace Critical2DKPZ.OnePoint

open Critical2DKPZ.Blocks

/-- The inverse fourth power of every block mass is integrable. -/
theorem integrable_blockMass_inv_pow_four (β : ℝ) (t : ℕ → ℕ) (i : ℕ) :
    Integrable (fun ω => (blockMass β t i ω)⁻¹ ^ 4) disorderLaw := by
  have hpow := integrable_rpow_smoothedP2Plane β (t (i - 1)) (t i) 0 (-4)
  have heq : (fun ω => (blockMass β t i ω)⁻¹ ^ 4) =
      fun ω => smoothedP2Plane β (t (i - 1)) (t i) 0 ω ^ (-4 : ℝ) := by
    funext ω
    have hpos : 0 < smoothedP2Plane β (t (i - 1)) (t i) 0 ω :=
      Polymer.smoothedP2Plane_pos β (t (i - 1)) (t i) 0 ω
    change (smoothedP2Plane β (t (i - 1)) (t i) 0 ω)⁻¹ ^ 4 = _
    have hpow' : smoothedP2Plane β (t (i - 1)) (t i) 0 ω ^ (-4 : ℝ) =
        (smoothedP2Plane β (t (i - 1)) (t i) 0 ω)⁻¹ ^ 4 := by
      let x := smoothedP2Plane β (t (i - 1)) (t i) 0 ω
      calc
        x ^ (-4 : ℝ) = (x ^ (4 : ℝ))⁻¹ := by
          rw [Real.rpow_neg (le_of_lt hpos)]
        _ = (x ^ 4)⁻¹ := congrArg Inv.inv (Real.rpow_natCast x 4)
        _ = x⁻¹ ^ 4 := (inv_pow x 4).symm
    exact hpow'.symm
  rw [heq]
  exact hpow

/-- The reciprocal and square of every block mass are integrable. -/
theorem integrable_blockMass_inv_and_sq (β : ℝ) (t : ℕ → ℕ) (i : ℕ) :
    Integrable (fun ω => (blockMass β t i ω)⁻¹) disorderLaw ∧
      Integrable (fun ω => blockMass β t i ω ^ 2) disorderLaw := by
  constructor
  · have hpow := integrable_rpow_smoothedP2Plane β (t (i - 1)) (t i) 0 (-1)
    have heq : (fun ω => (blockMass β t i ω)⁻¹) =
        fun ω => smoothedP2Plane β (t (i - 1)) (t i) 0 ω ^ (-1 : ℝ) := by
      funext ω
      rw [blockMass, Real.rpow_neg_one]
    rw [heq]
    exact hpow
  · have hpow := integrable_rpow_smoothedP2Plane β (t (i - 1)) (t i) 0 2
    have heq : (fun ω => blockMass β t i ω ^ 2) =
        fun ω => smoothedP2Plane β (t (i - 1)) (t i) 0 ω ^ (2 : ℝ) := by
      funext ω
      rw [blockMass]
      exact (Real.rpow_natCast _ 2).symm
    rw [heq]
    exact hpow

/-- The block-moment estimate controls the fourth inverse moment of every block, including the terminal block. Its
integrability companion is `integrable_blockMass_inv_pow_four`. -/
theorem integral_inv_blockMass_pow_four_le_of (hC6 : BlockMomentsBound)
    (A ρ₀ ρ₁ : ℝ) (hρ : 1 < ρ₀) :
    ∃ C : ℝ, ∀ ρ ∈ Set.Icc ρ₀ ρ₁, ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A,
      ∀ i : ℕ, 1 ≤ i → i ≤ blockCount N ρ →
        ∫ ω, (blockMass (criticalBeta ϑ N) (blockTime N ρ) i ω)⁻¹ ^ 4 ∂disorderLaw ≤ C := by
  obtain ⟨C₆, hC₆⟩ := hC6 A ρ₀ ρ₁ hρ
  let C := max C₆ 0 + 1
  have hC₆le : C₆ ≤ C := by dsimp [C]; linarith [le_max_left C₆ 0]
  have hCnonneg : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨(1 + C) ^ 10, ?_⟩
  intro ρ hρρ
  filter_upwards [hC₆ ρ hρρ] with N hN
  intro ϑ hϑ i hi hiK
  let β := criticalBeta ϑ N
  let t := blockTime N ρ
  let Z : Disorder → ℝ := blockMass β t i
  let a := t (i - 1)
  let b := t i
  have hmean : ∫ ω, Z ω ∂disorderLaw = 1 := by
    dsimp [Z, blockMass, β, t]
    exact Polymer.integral_smoothedP2Plane _ _ _ _
  have hmem : MemLp Z 2 disorderLaw := by
    dsimp [Z, blockMass, β, t]
    exact Polymer.memLp_smoothedP2Plane _ _ _ _ 2 (by norm_num)
  have hvarEq : Var[Z; disorderLaw] = (∫ ω, Z ω ^ 2 ∂disorderLaw) - 1 := by
    rw [ProbabilityTheory.variance_eq_sub hmem, hmean]
    norm_num
  have hC6at := hN ϑ hϑ i hi hiK
  have hden : 1 ≤ (blockCount N ρ : ℝ) + 1 - i := by
    have hnat : 1 ≤ blockCount N ρ + 1 - i := by omega
    have hcast : ((blockCount N ρ + 1 - i : ℕ) : ℝ) =
        (blockCount N ρ : ℝ) + 1 - i := by
      rw [Nat.cast_sub (by omega : i ≤ blockCount N ρ + 1), Nat.cast_add]
      norm_num
    rw [← hcast]
    exact_mod_cast hnat
  have hvarle : Var[Z; disorderLaw] ≤ C := by
    have hdenpos : 0 < (blockCount N ρ : ℝ) + 1 - i := by linarith
    have hdiv : C₆ / ((blockCount N ρ : ℝ) + 1 - i) ≤ C := by
      rw [div_le_iff₀ hdenpos]
      nlinarith [mul_nonneg hCnonneg (sub_nonneg.mpr hden)]
    exact hC6at.1.trans hdiv
  have hsecondle : ∫ ω, Z ω ^ 2 ∂disorderLaw ≤ 1 + C := by
    have h := hvarle
    rw [hvarEq] at h
    linarith
  let ν : Site → ℝ := fun y => srwKernel a (y - (0 : Site))
  let E : Finset Site := Polymer.endpoints (0 : Site) a
  have hνE : ∀ y ∉ E, ν y = 0 := by
    intro y hy
    exact Polymer.srwKernel_eq_zero_of_not_mem a 0 y (by simpa [E, ν] using hy)
  have hν0 : ∀ y, 0 ≤ ν y := by
    intro y
    exact Polymer.kernel_nonneg a (y - (0 : Site))
  have hν1 : ∑ y ∈ E, ν y = 1 := by
    exact Polymer.sum_srwKernel_endpoints a 0
  have hprofile (ω : Disorder) :
      profileP2Fun β a b ν (fun _ => 1) ω = Z ω := by
    dsimp [Z, a, b, t, β, ν]
    exact Polymer.profileP2Fun_srw_flat _ _ _ _ _
  have hβ : 0 ≤ β := by
    dsimp [β, Critical2DKPZ.criticalBeta]
    exact Real.sqrt_nonneg _
  have hnegative := integral_rpow_neg_profileP2Fun_le hβ a b ν E hνE hν0 hν1
    (p := 4) (by norm_num)
  have hnegative' : ∫ ω, Z ω ^ (-4 : ℝ) ∂disorderLaw ≤
      (∫ ω, Z ω ^ 2 ∂disorderLaw) ^ (10 : ℝ) := by
    have hten : (4 : ℝ) * (4 + 1) / 2 = 10 := by norm_num
    rw [hten] at hnegative
    simpa only [hprofile] using hnegative
  have hpow : ∫ ω, ((Z ω)⁻¹) ^ 4 ∂disorderLaw ≤ (1 + C) ^ 10 := by
    have hpoint (ω : Disorder) : Z ω ^ (-4 : ℝ) = ((Z ω)⁻¹) ^ 4 := by
      dsimp [Z]
      let x := blockMass β t i ω
      calc
        x ^ (-4 : ℝ) = (x ^ (4 : ℝ))⁻¹ := by
          rw [Real.rpow_neg (le_of_lt (blockMass_pos β t i ω))]
        _ = (x ^ 4)⁻¹ := congrArg Inv.inv (Real.rpow_natCast x 4)
        _ = x⁻¹ ^ 4 := (inv_pow x 4).symm
    have hleft : ∫ ω, ((Z ω)⁻¹) ^ 4 ∂disorderLaw =
        ∫ ω, Z ω ^ (-4 : ℝ) ∂disorderLaw := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => (hpoint ω).symm
    calc
      ∫ ω, ((Z ω)⁻¹) ^ 4 ∂disorderLaw = ∫ ω, Z ω ^ (-4 : ℝ) ∂disorderLaw := hleft
      _ ≤ (∫ ω, Z ω ^ 2 ∂disorderLaw) ^ (10 : ℝ) := hnegative'
      _ ≤ (1 + C) ^ 10 := by
        calc
          (∫ ω, Z ω ^ 2 ∂disorderLaw) ^ (10 : ℝ) ≤
              (1 + C) ^ (10 : ℝ) := by
                apply Real.rpow_le_rpow
                · exact integral_nonneg fun ω => sq_nonneg (Z ω)
                · exact hsecondle
                · norm_num
          _ = (1 + C) ^ 10 := Real.rpow_natCast _ 10
  simpa only [Z, β, t] using hpow

end Critical2DKPZ.OnePoint

end
