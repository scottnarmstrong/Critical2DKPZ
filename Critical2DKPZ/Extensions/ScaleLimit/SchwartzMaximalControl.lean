/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SchwartzRandomPairing
public import Critical2DKPZ.Extensions.ScaleLimit.TruncatedMaximal
public import Critical2DKPZ.Extensions.ScaleLimit.SchwartzField

/-! # Truncated maximal control through the Schwartz-field specification

The representative satisfies the stochastic Schwartz-field specification.
The maximal estimate applies to every Schwartz test, including the difference
of two scaled band kernels.
-/

public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

universe u

/-- Truncated maximal control at every center for any representative satisfying
the stochastic Schwartz-field specification. -/
theorem schwartz_field_truncated_maximal {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {D : Ω → Distr} {ν : Measure Plane}
    (hD : StationarySpectralData P D ν) (φ : TestFn) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (ψ : SchwartzMap Plane ℝ) (F : Plane → Ω → ℝ),
      Measurable (Function.uncurry F) →
      (∀ y, F y =ᵐ[P] fun ω => schwartzExt hD (translateSchwartz y ψ) ω) →
      (∀ (n : ℕ) (y : Fin n → Plane) (z : Plane),
        IdentDistrib (fun ω i => F (y i + z) ω) (fun ω i => F (y i) ω) P P) →
      (∀ y₀, TendstoInMeasure P F (𝓝 y₀) (F y₀)) → ∀ (x : Plane) (Λ : ℝ), 0 < Λ →
      P {ω | ENNReal.ofReal Λ < ⨆ r : {r : ℝ // 0 < r},
        ENNReal.ofReal |∫ z, φ z * F (x + (r : ℝ) • z) ω|} ≤
          ENNReal.ofReal (C / Λ ^ 2 *
            ∫ ω, squareTail (c * Λ) (schwartzExt hD (translateSchwartz x ψ) ω) ∂P) := by
  obtain ⟨C, c, hC, hc, hb⟩ := truncated_maximal (P := P) φ
  refine ⟨C, c, hC, hc, ?_⟩
  intro ψ F hF hrep hstat hcont x Λ hΛ
  let g : Plane → Ω → ℝ := fun y ω => F (y + x) ω
  have hg : Measurable (Function.uncurry g) :=
    hF.comp ((measurable_fst.add_const x).prodMk measurable_snd)
  have hgs (n : ℕ) (y : Fin n → Plane) (z : Plane) :
      IdentDistrib (fun ω i => g (y i + z) ω) (fun ω i => g (y i) ω) P P := by
    simpa only [g, add_assoc, add_comm, add_left_comm] using
      hstat n (fun i => y i + x) z
  have hgc (y : Plane) : TendstoInMeasure P g (𝓝 y) (g y) :=
    (hcont (y + x)).comp (continuous_id.add_const x).continuousAt.tendsto
  have hLp : MemLp (g 0) 2 P := by
    change MemLp (F (0 + x)) 2 P
    rw [zero_add]
    exact (memLp_congr_ae (hrep x)).mpr
      (Lp.memLp (schwartzExt hD (translateSchwartz x ψ)))
  have hh := hb g hg hgs hgc hLp Λ hΛ
  have htail : (∫ ω, squareTail (c * Λ) (g 0 ω) ∂P) =
      ∫ ω, squareTail (c * Λ) (schwartzExt hD (translateSchwartz x ψ) ω) ∂P := by
    apply integral_congr_ae
    filter_upwards [hrep x] with ω hω
    change squareTail (c * Λ) (F (0 + x) ω) = _
    rw [zero_add, hω]
  change P {ω | ENNReal.ofReal Λ < ⨆ r : {r : ℝ // 0 < r},
    ENNReal.ofReal |∫ z, φ z * g ((r : ℝ) • z) ω|} ≤
      ENNReal.ofReal (C / Λ ^ 2 * ∫ ω, squareTail (c * Λ) (g 0 ω) ∂P) at hh
  rw [htail] at hh
  simpa only [g, add_comm] using hh

/-- The maximal estimate specialized to the selected stationary field, including
differences through a single arbitrary Schwartz test. -/
theorem schwartz_truncated_maximal {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {D : Ω → Distr} {ν : Measure Plane}
    (hD : StationarySpectralData P D ν) (φ : TestFn) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (ψ : SchwartzMap Plane ℝ) (x : Plane) (Λ : ℝ), 0 < Λ →
      P {ω | ENNReal.ofReal Λ < ⨆ r : {r : ℝ // 0 < r},
        ENNReal.ofReal |∫ z, φ z * schwartzField hD ψ (x + (r : ℝ) • z) ω|} ≤
          ENNReal.ofReal (C / Λ ^ 2 *
            ∫ ω, squareTail (c * Λ) (schwartzExt hD (translateSchwartz x ψ) ω) ∂P) := by
  obtain ⟨C, c, hC, hc, hb⟩ := schwartz_field_truncated_maximal hD φ
  exact ⟨C, c, hC, hc, fun ψ => hb ψ (schwartzField hD ψ)
    (schwartzField_measurable hD ψ) (schwartzField_ae_eq hD ψ)
    (schwartzField_stationary hD ψ) (schwartzField_tendstoInMeasure hD ψ)⟩

/-- The band-difference estimate uses the jointly stationary difference field,
and its tail moment is the literal difference of the two band variables. -/
theorem band_truncated_maximal {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {D : Ω → Distr} {ν : Measure Plane}
    (hD : StationarySpectralData P D ν) (φ : TestFn) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (a b : ℝ) (x : Plane) (Λ : ℝ), 0 < Λ →
      P {ω | ENNReal.ofReal Λ < ⨆ r : {r : ℝ // 0 < r},
        ENNReal.ofReal |∫ z, φ z * schwartzField hD
          (zetaScaled a 0 - zetaScaled b 0) (x + (r : ℝ) • z) ω|} ≤
          ENNReal.ofReal (C / Λ ^ 2 * ∫ ω,
            squareTail (c * Λ) (bandField hD a x ω - bandField hD b x ω) ∂P) := by
  obtain ⟨C, c, hC, hc, hb⟩ := schwartz_truncated_maximal hD φ
  refine ⟨C, c, hC, hc, ?_⟩
  intro a b x Λ hΛ
  have hh := hb (zetaScaled a 0 - zetaScaled b 0) x Λ hΛ
  have heq : (∫ ω, squareTail (c * Λ) (schwartzExt hD
      (translateSchwartz x (zetaScaled a 0 - zetaScaled b 0)) ω) ∂P) =
      ∫ ω, squareTail (c * Λ) (bandField hD a x ω - bandField hD b x ω) ∂P := by
    apply integral_congr_ae
    filter_upwards [schwartzField_ae_eq hD (zetaScaled a 0 - zetaScaled b 0) x,
      bandField_difference_ae_eq hD a b x] with ω hrep hdiff
    rw [← hrep, hdiff]
  rwa [heq] at hh

end Critical2DKPZ.Extensions.ScaleLimit
