/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.StationaryMaximal
public import Critical2DKPZ.Extensions.ScaleLimit.MaximalMajorant
public import Critical2DKPZ.Extensions.ScaleLimit.LipschitzInMeasure
public import Critical2DKPZ.Extensions.ScaleLimit.SquareTail

/-! # The truncated stationary maximal inequality

Use the Lipschitz tail `max 0 (2|x|-t)` at `t = Λ/(2A)`. This preserves
continuity in probability and gives a square-tail threshold `Λ/(4A)`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The maximal probability of all smooth averages is controlled by a strict
square-tail moment, with positive constants depending only on the test function.
The tail moment is integrable by `integrable_squareTail` and the `L²` premise. -/
theorem truncated_maximal (φ : TestFn) : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (f : Plane → Ω → ℝ), Measurable (Function.uncurry f) →
      (∀ (n : ℕ) (y : Fin n → Plane) (z : Plane),
        IdentDistrib (fun ω i => f (y i + z) ω) (fun ω i => f (y i) ω) P P) →
      (∀ y₀, TendstoInMeasure P f (𝓝 y₀) (f y₀)) → MemLp (f 0) 2 P →
      ∀ Λ > 0,
        P {ω | ENNReal.ofReal Λ < ⨆ r : {r : ℝ // 0 < r},
            ENNReal.ofReal |∫ z, φ z * f ((r : ℝ) • z) ω|} ≤
          ENNReal.ofReal (C / Λ ^ 2 * ∫ ω, (f 0 ω) ^ 2 *
            {x : ℝ | c * Λ < |x|}.indicator 1 (f 0 ω) ∂P) := by
  obtain ⟨A, hA, hdom⟩ := maximal_domination_with_offset φ
  obtain ⟨C, hC⟩ := stationary_maximal (P := P)
  let c : ℝ := 1 / (4 * A)
  let B : ℝ := 16 * A ^ 2 * ((C : ℝ) + 1)
  have hc : 0 < c := by dsimp [c]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B, c, hB, hc, fun f hf hstat hcont hLp Λ hΛ => ?_⟩
  let t : ℝ := Λ / (2 * A)
  have ht : 0 < t := div_pos hΛ (mul_pos (by norm_num) hA)
  have ht₂ : t / 2 = c * Λ := by
    dsimp [t, c]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hAt : A * (t + t) = Λ := by
    dsimp [t]
    field_simp [hA.ne']
    ring
  let g : Plane → Ω → ℝ := fun y ω => softTail t (f y ω)
  have hsoft : Measurable (softTail t) := (softTail_lipschitz t).continuous.measurable
  have hgm : Measurable (Function.uncurry g) := hsoft.comp hf
  have hgs (n : ℕ) (y : Fin n → Plane) (z : Plane) :
      IdentDistrib (fun ω i => g (y i + z) ω) (fun ω i => g (y i) ω) P P :=
    (hstat n y z).comp (Measurable.of_eval fun i => hsoft.comp (measurable_pi_apply i))
  have hgc (y : Plane) : TendstoInMeasure P g (𝓝 y) (g y) :=
    tendstoInMeasure_lipschitz_comp (hcont y) (softTail_lipschitz t) (by norm_num)
  have hf₀ : Measurable (f 0) := hf.of_uncurry_left
  have hfI : Integrable (f 0) P := hLp.integrable (by norm_num)
  have hgI : Integrable (g 0) P := by
    apply (hfI.norm.const_mul 2).mono' (hsoft.comp hf₀).aestronglyMeasurable
    exact Eventually.of_forall fun ω => by
      change ‖softTail t (f 0 ω)‖ ≤ 2 * ‖f 0 ω‖
      rw [Real.norm_of_nonneg (softTail_nonneg t (f 0 ω))]
      exact softTail_le_two_norm ht.le (f 0 ω)
  let I : ℝ := ∫ ω, squareTail (c * Λ) (f 0 ω) ∂P
  have hI : 0 ≤ I := integral_nonneg fun ω => squareTail_nonneg _ _
  have htail : (∫ ω, g 0 ω ∂P) ≤ (4 / t) * I := by
    have hh := integral_softTail_le hf₀ hLp.integrable_sq ht hgI
    rw [ht₂] at hh
    exact hh
  have hnorm : (∫⁻ ω, ‖g 0 ω‖ₑ ∂P) = ENNReal.ofReal (∫ ω, g 0 ω ∂P) := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm hgI]
    apply congrArg ENNReal.ofReal
    apply integral_congr_ae
    exact Eventually.of_forall fun ω => Real.norm_of_nonneg (softTail_nonneg t (f 0 ω))
  have hsub : {ω | ENNReal.ofReal Λ < ⨆ r : {r : ℝ // 0 < r},
        ENNReal.ofReal |∫ z, φ z * f ((r : ℝ) • z) ω|} ⊆
      {ω | ENNReal.ofReal t < maximalFn (fun z => g z ω) 0} := by
    intro ω hω
    change ENNReal.ofReal t < maximalFn (fun z => g z ω) 0
    change ENNReal.ofReal Λ < ⨆ r : {r : ℝ // 0 < r},
      ENNReal.ofReal |∫ z, φ z * f ((r : ℝ) • z) ω| at hω
    apply lt_of_not_ge
    intro hM
    obtain ⟨r, hr⟩ := lt_iSup_iff.mp hω
    have hp (z : Plane) : ‖f z ω‖ ≤ t + ‖g z ω‖ := by
      change ‖f z ω‖ ≤ t + ‖softTail t (f z ω)‖
      rw [Real.norm_of_nonneg (softTail_nonneg t (f z ω))]
      exact norm_le_add_softTail t (f z ω)
    have hh : ENNReal.ofReal |∫ z, φ z * f ((r : ℝ) • z) ω| ≤
        ENNReal.ofReal A * (ENNReal.ofReal t + maximalFn (fun z => g z ω) 0) := by
      simpa only [zero_add] using hdom (fun z => f z ω) (fun z => g z ω) t ht.le hp 0 r r.2
    have hle : ENNReal.ofReal |∫ z, φ z * f ((r : ℝ) • z) ω| ≤ ENNReal.ofReal Λ := by
      calc
        _ ≤ ENNReal.ofReal A * (ENNReal.ofReal t + maximalFn (fun z => g z ω) 0) := hh
        _ ≤ ENNReal.ofReal A * (ENNReal.ofReal t + ENNReal.ofReal t) :=
          mul_le_mul' le_rfl (add_le_add le_rfl hM)
        _ = ENNReal.ofReal Λ := by
          rw [← ENNReal.ofReal_add ht.le ht.le, ← ENNReal.ofReal_mul hA.le, hAt]
    exact (not_lt_of_ge hle hr).elim
  have hcoeff : (1 / t) * (C : ℝ) * (4 / t) ≤ B / Λ ^ 2 := by
    have heq : (1 / t) * (C : ℝ) * (4 / t) = 16 * A ^ 2 * (C : ℝ) / Λ ^ 2 := by
      dsimp [t]
      field_simp [hA.ne', hΛ.ne']
      ring
    rw [heq]
    apply div_le_div_of_nonneg_right _ (sq_nonneg Λ)
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1))
      (by positivity : 0 ≤ 16 * A ^ 2)
  calc
    _ ≤ P {ω | ENNReal.ofReal t < maximalFn (fun z => g z ω) 0} := measure_mono hsub
    _ ≤ ENNReal.ofReal (1 / t) * C * ∫⁻ ω, ‖g 0 ω‖ₑ ∂P := (hC g hgm hgs hgc hgI).2 t ht
    _ ≤ ENNReal.ofReal (1 / t) * C * ENNReal.ofReal ((4 / t) * I) := by
      rw [hnorm]
      exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal htail)
    _ = ENNReal.ofReal (((1 / t) * (C : ℝ) * (4 / t)) * I) := by
      rw [← (ENNReal.ofReal_coe_nnreal : ENNReal.ofReal (C : ℝ) = (C : ℝ≥0∞)),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / t),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ (1 / t) * (C : ℝ))]
      apply congrArg ENNReal.ofReal
      ring
    _ ≤ ENNReal.ofReal (B / Λ ^ 2 * I) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcoeff hI)

end Critical2DKPZ.Extensions.ScaleLimit

end
