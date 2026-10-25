/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! # Truncation bounds for cutoff-tail moments -/

@[expose] public section

open MeasureTheory

namespace Critical2DKPZ.SHF.Flow

/-- A small first moment of one tail controls the squared product with another local mass, if
both local masses are dominated by a variable with bounded sixth moment. -/
theorem integral_mul_sq_le_truncation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X T Y : Ω → ℝ) (L : ℝ) (hL : 0 < L)
    (hTm : Measurable T) (hYm : Measurable Y)
    (hX : 0 ≤ᵐ[P] X) (hT : 0 ≤ᵐ[P] T) (hY : 0 ≤ᵐ[P] Y)
    (hTX : T ≤ᵐ[P] X) (hYX : Y ≤ᵐ[P] X)
    (hT_int : Integrable T P) (hX6_int : Integrable (fun ω => X ω ^ 6) P) :
    Integrable (fun ω => (T ω * Y ω) ^ 2) P ∧
      ∫ ω, (T ω * Y ω) ^ 2 ∂P ≤
        L ^ 3 * ∫ ω, T ω ∂P + L⁻¹ ^ 2 * ∫ ω, X ω ^ 6 ∂P := by
  have hpoint : (fun ω => (T ω * Y ω) ^ 2) ≤ᵐ[P] (fun ω =>
      L ^ 3 * T ω + L⁻¹ ^ 2 * X ω ^ 6) := by
    filter_upwards [hX, hT, hY, hTX, hYX] with ω hXω hTω hYω hTXω hYXω
    by_cases hsmall : X ω ≤ L
    · have hTY : T ω * Y ω ^ 2 ≤ X ω ^ 3 := by
        calc
          T ω * Y ω ^ 2 ≤ X ω * Y ω ^ 2 :=
            mul_le_mul_of_nonneg_right hTXω (sq_nonneg (Y ω))
          _ ≤ X ω * X ω ^ 2 := mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hYω hYXω 2) hXω
          _ = X ω ^ 3 := by ring
      have hprod : (T ω * Y ω) ^ 2 ≤ T ω * X ω ^ 3 := by
        calc
          (T ω * Y ω) ^ 2 = T ω * (T ω * Y ω ^ 2) := by ring
          _ ≤ T ω * X ω ^ 3 := mul_le_mul_of_nonneg_left hTY hTω
      have hscale : T ω * X ω ^ 3 ≤ T ω * L ^ 3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hXω hsmall 3) hTω
      calc
        (T ω * Y ω) ^ 2 ≤ T ω * X ω ^ 3 := hprod
        _ ≤ T ω * L ^ 3 := hscale
        _ = L ^ 3 * T ω := by ring
        _ ≤ L ^ 3 * T ω + L⁻¹ ^ 2 * X ω ^ 6 :=
          le_add_of_nonneg_right (mul_nonneg (sq_nonneg (L⁻¹)) (pow_nonneg hXω 6))
    · have hlarge : L ≤ X ω := le_of_not_ge hsmall
      have hT2 : T ω ^ 2 ≤ X ω ^ 2 := pow_le_pow_left₀ hTω hTXω 2
      have hY2 : Y ω ^ 2 ≤ X ω ^ 2 := pow_le_pow_left₀ hYω hYXω 2
      have hprod : (T ω * Y ω) ^ 2 ≤ X ω ^ 4 := by
        calc
          (T ω * Y ω) ^ 2 = T ω ^ 2 * Y ω ^ 2 := by ring
          _ ≤ X ω ^ 2 * Y ω ^ 2 := mul_le_mul_of_nonneg_right hT2 (sq_nonneg (Y ω))
          _ ≤ X ω ^ 2 * X ω ^ 2 := mul_le_mul_of_nonneg_left hY2 (sq_nonneg (X ω))
          _ = X ω ^ 4 := by ring
      have hL2 : L ^ 2 ≤ X ω ^ 2 := pow_le_pow_left₀ (le_of_lt hL) hlarge 2
      have hLmul : L ^ 2 * X ω ^ 4 ≤ X ω ^ 6 := by
        calc
          L ^ 2 * X ω ^ 4 ≤ X ω ^ 2 * X ω ^ 4 :=
            mul_le_mul_of_nonneg_right hL2 (by positivity)
          _ = X ω ^ 6 := by ring
      have hcancel : L⁻¹ ^ 2 * L ^ 2 = 1 := by
        rw [inv_pow]
        field_simp [ne_of_gt hL]
      have hscaled : X ω ^ 4 ≤ L⁻¹ ^ 2 * X ω ^ 6 := by
        calc
          X ω ^ 4 = (L⁻¹ ^ 2 * L ^ 2) * X ω ^ 4 := by rw [hcancel, one_mul]
          _ = L⁻¹ ^ 2 * (L ^ 2 * X ω ^ 4) := by ring
          _ ≤ L⁻¹ ^ 2 * X ω ^ 6 :=
            mul_le_mul_of_nonneg_left hLmul (sq_nonneg (L⁻¹))
      calc
        (T ω * Y ω) ^ 2 ≤ X ω ^ 4 := hprod
        _ ≤ L⁻¹ ^ 2 * X ω ^ 6 := hscaled
        _ ≤ L ^ 3 * T ω + L⁻¹ ^ 2 * X ω ^ 6 :=
          le_add_of_nonneg_left (mul_nonneg (pow_nonneg (le_of_lt hL) 3) hTω)
  have hmajor_int : Integrable (fun ω => L ^ 3 * T ω + L⁻¹ ^ 2 * X ω ^ 6) P :=
    (hT_int.const_mul (L ^ 3)).add (hX6_int.const_mul (L⁻¹ ^ 2))
  have hprod_meas : Measurable (fun ω => (T ω * Y ω) ^ 2) := (hTm.mul hYm).pow_const 2
  have hprod_int : Integrable (fun ω => (T ω * Y ω) ^ 2) P := by
    apply hmajor_int.mono' hprod_meas.aestronglyMeasurable
    filter_upwards [hpoint] with ω hω
    change ‖(T ω * Y ω) ^ 2‖ ≤ L ^ 3 * T ω + L⁻¹ ^ 2 * X ω ^ 6
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (T ω * Y ω))]
    exact hω
  refine ⟨hprod_int, ?_⟩
  calc
    ∫ ω, (T ω * Y ω) ^ 2 ∂P ≤
        ∫ ω, (L ^ 3 * T ω + L⁻¹ ^ 2 * X ω ^ 6) ∂P :=
      integral_mono_ae hprod_int hmajor_int hpoint
    _ = L ^ 3 * ∫ ω, T ω ∂P + L⁻¹ ^ 2 * ∫ ω, X ω ^ 6 ∂P := by
      rw [integral_add (hT_int.const_mul (L ^ 3))
        (hX6_int.const_mul (L⁻¹ ^ 2)), integral_const_mul, integral_const_mul]

/-- A small first moment of a tail controls its squared product with a local mass from another
block. The two local masses need separate sixth-moment bounds. -/
theorem integral_mul_sq_le_two_sixth_truncation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y T V : Ω → ℝ) (L : ℝ) (hL : 0 < L)
    (hXm : Measurable X) (hYm : Measurable Y) (hTm : Measurable T) (hVm : Measurable V)
    (hX : 0 ≤ᵐ[P] X) (hY : 0 ≤ᵐ[P] Y) (hT : 0 ≤ᵐ[P] T) (hV : 0 ≤ᵐ[P] V)
    (hTX : T ≤ᵐ[P] X) (hVY : V ≤ᵐ[P] Y)
    (hT_int : Integrable T P) (hX6_int : Integrable (fun ω => X ω ^ 6) P)
    (hY6_int : Integrable (fun ω => Y ω ^ 6) P) :
    Integrable (fun ω => (T ω * V ω) ^ 2) P ∧
      ∫ ω, (T ω * V ω) ^ 2 ∂P ≤
        L ^ 3 * ∫ ω, T ω ∂P + L⁻¹ ^ 2 *
          (∫ ω, X ω ^ 6 ∂P + ∫ ω, Y ω ^ 6 ∂P) := by
  let Z : Ω → ℝ := fun ω => max (X ω) (Y ω)
  have hZm : Measurable Z := hXm.max hYm
  have hZ : 0 ≤ᵐ[P] Z := hX.mono fun ω hω => le_max_of_le_left hω
  have hTZ : T ≤ᵐ[P] Z := hTX.trans (Filter.Eventually.of_forall fun ω => le_max_left _ _)
  have hVZ : V ≤ᵐ[P] Z := hVY.trans (Filter.Eventually.of_forall fun ω => le_max_right _ _)
  have hsum_int : Integrable (fun ω => X ω ^ 6 + Y ω ^ 6) P := hX6_int.add hY6_int
  have hZsix_le : (fun ω => Z ω ^ 6) ≤ᵐ[P] (fun ω => X ω ^ 6 + Y ω ^ 6) := by
    filter_upwards [hX, hY] with ω hXω hYω
    dsimp [Z]
    by_cases hxy : Y ω ≤ X ω
    · rw [max_eq_left hxy]
      exact le_add_of_nonneg_right (pow_nonneg hYω 6)
    · rw [max_eq_right (le_of_not_ge hxy)]
      exact le_add_of_nonneg_left (pow_nonneg hXω 6)
  have hZsix_int : Integrable (fun ω => Z ω ^ 6) P := by
    apply hsum_int.mono' (hZm.pow_const 6).aestronglyMeasurable
    filter_upwards [hZsix_le, hZ] with ω hω hZω
    change ‖Z ω ^ 6‖ ≤ X ω ^ 6 + Y ω ^ 6
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hZω 6)]
    exact hω
  have hbase := integral_mul_sq_le_truncation P Z T V L hL hTm hVm
    hZ hT hV hTZ hVZ hT_int hZsix_int
  have hZbound : ∫ ω, Z ω ^ 6 ∂P ≤
      ∫ ω, X ω ^ 6 ∂P + ∫ ω, Y ω ^ 6 ∂P := by
    calc
      ∫ ω, Z ω ^ 6 ∂P ≤ ∫ ω, (X ω ^ 6 + Y ω ^ 6) ∂P :=
        integral_mono_ae hZsix_int hsum_int hZsix_le
      _ = _ := integral_add hX6_int hY6_int
  refine ⟨hbase.1, ?_⟩
  calc
    ∫ ω, (T ω * V ω) ^ 2 ∂P ≤
        L ^ 3 * ∫ ω, T ω ∂P + L⁻¹ ^ 2 * ∫ ω, Z ω ^ 6 ∂P := hbase.2
    _ ≤ L ^ 3 * ∫ ω, T ω ∂P + L⁻¹ ^ 2 *
        (∫ ω, X ω ^ 6 ∂P + ∫ ω, Y ω ^ 6 ∂P) := by
          have hsecond := mul_le_mul_of_nonneg_left hZbound (sq_nonneg L⁻¹)
          linarith



end Critical2DKPZ.SHF.Flow

end
