/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.HighRemainderEnvelope
public import Critical2DKPZ.Extensions.ScaleLimit.LowRemainderEnvelope
public import Critical2DKPZ.Extensions.ScaleLimit.SpectralMassClock
import Mathlib.Tactic

/-! # Remainder square envelopes at the scale clock, including time zero -/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Critical2DKPZ.Extensions.ScaleLimit

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {D : Ω → Distr} {ν : Measure Plane}

/-- The two remainder envelopes are `O(R^-2 t L)` on a fixed time window.
The constant precedes the window and `R`; at time zero the coarse-band
spectral mass is fixed and its normalized contribution vanishes. -/
theorem window_remainder_envelopes (hD : StationarySpectralData P D ν)
    (φ : TestFn) (hφ : (∫ z, φ z) = 1) (x : Plane) :
    ∃ C : ℝ, 0 < C ∧ ∀ R s t : ℝ, 0 < R → 0 ≤ s → s < t →
      ∀ᶠ L : Set.Ioi (0 : ℝ) in atTop,
        ∃ u w : ℝ → Ω → ℝ, ∃ ZU ZW : Ω → ℝ,
          (∀ r ∈ Set.Icc (scaleRadius L t) (scaleRadius L s),
            u r =ᵐ[P] (bandLowRemainder hD (R * scaleRadius L s) φ x r : Ω → ℝ) ∧
            w r =ᵐ[P] (bandHighRemainder hD (scaleRadius L t / R) φ x r : Ω → ℝ)) ∧
          Integrable ZU P ∧ Integrable ZW P ∧ (∀ ω, 0 ≤ ZU ω) ∧ (∀ ω, 0 ≤ ZW ω) ∧
          (∀ᵐ ω ∂P, ∀ r ∈ Set.Icc (scaleRadius L t) (scaleRadius L s), u r ω ^ 2 ≤ ZU ω ∧ w r ω ^ 2 ≤ ZW ω) ∧
          (L : ℝ)⁻¹ * (∫ ω, ZU ω ∂P) ≤ C * R⁻¹ ^ 2 * t ∧
          (L : ℝ)⁻¹ * (∫ ω, ZW ω ∂P) ≤ C * R⁻¹ ^ 2 * t := by
  let : IsLocallyFiniteMeasure ν := hD.locFin
  obtain ⟨Ch, hCh, hhigh⟩ := exists_bandHighRemainder_square_envelope hD φ x
  let B := testFirstMoment φ
  let C := 16 * B ^ 2 + 2 * Ch + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hClow : 16 * B ^ 2 ≤ C := by dsimp [C]; linarith only [hCh]
  have hChigh : 2 * Ch ≤ C := by dsimp [C]; nlinarith only [sq_nonneg B]
  refine ⟨C, hC, ?_⟩
  intro R s t hR hs hst
  have ht : 0 < t := hs.trans_lt hst
  have hαL : Tendsto (fun L : Set.Ioi (0 : ℝ) => scaleRadius L t / R) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Eventually.of_forall fun L => div_pos (scaleRadius_pos L t) hR⟩
    simpa only [zero_div] using (scaleRadius_tendsto_zero ht).div_const R
  have hmlow : Tendsto (fun L : Set.Ioi (0 : ℝ) =>
      (L : ℝ)⁻¹ * specMass ν (2 / (R * scaleRadius L s))) atTop (𝓝 s) := by
    have hh := specMass_scaleRadius_tendsto ν hD.ballAsymp (div_pos (by norm_num : (0 : ℝ) < 2) hR) hs
    apply hh.congr
    intro L
    congr 2
    field_simp
  have hmhigh : Tendsto (fun L : Set.Ioi (0 : ℝ) =>
      (L : ℝ)⁻¹ * specMass ν (scaleRadius L t / R)⁻¹) atTop (𝓝 t) := by
    have hh := specMass_scaleRadius_tendsto ν hD.ballAsymp hR ht.le
    apply hh.congr
    intro L
    rw [inv_div]
  filter_upwards [hαL.eventually hhigh,
    hmlow.eventually (Iio_mem_nhds (show s < 2 * t by linarith)),
    hmhigh.eventually (Iio_mem_nhds (show t < 2 * t by linarith))] with L hh hml hmh
  let α := scaleRadius L t
  let β := scaleRadius L s
  have hα : 0 < α := scaleRadius_pos L t
  have hβ : 0 < β := scaleRadius_pos L s
  have hαβ : α < β := scaleRadius_strictAnti L.property hst
  obtain ⟨w, ZW, hw, _, hWi, hW0, hWw, hW⟩ := hh α β hα hαβ
  obtain ⟨u, ZU, hu, _, hUi, hU0, hUu, hU⟩ :=
    exists_bandLowRemainder_square_envelope hD φ hφ x (mul_pos hR hβ) hβ
  have hrlow : β / (R * β) = R⁻¹ := by field_simp
  have hrhigh : (α / R) / α = R⁻¹ := by field_simp
  rw [hrlow] at hU
  rw [hrhigh] at hW
  refine ⟨u, w, ZU, ZW, ?_, hUi, hWi, hU0, hW0, ?_, ?_, ?_⟩
  · intro r hr
    exact ⟨hu r ⟨hα.le.trans hr.1, hr.2⟩, hw r hr⟩
  · filter_upwards [hUu, hWw] with ω hUω hWω r hr
    exact ⟨hUω r ⟨hα.le.trans hr.1, hr.2⟩, hWω r hr⟩
  · calc
      _ ≤ (L : ℝ)⁻¹ * (8 * B ^ 2 * R⁻¹ ^ 2 * specMass ν (2 / (R * β))) :=
        mul_le_mul_of_nonneg_left hU (inv_pos.mpr L.property).le
      _ = (8 * B ^ 2 * R⁻¹ ^ 2) * ((L : ℝ)⁻¹ * specMass ν (2 / (R * β))) := by ring
      _ ≤ (8 * B ^ 2 * R⁻¹ ^ 2) * (2 * t) := mul_le_mul_of_nonneg_left hml.le (by positivity)
      _ = (16 * B ^ 2) * (R⁻¹ ^ 2 * t) := by ring
      _ ≤ C * (R⁻¹ ^ 2 * t) := mul_le_mul_of_nonneg_right hClow (by positivity)
      _ = _ := by ring
  · calc
      _ ≤ (L : ℝ)⁻¹ * (Ch * R⁻¹ ^ 2 * specMass ν (α / R)⁻¹) :=
        mul_le_mul_of_nonneg_left hW (inv_pos.mpr L.property).le
      _ = (Ch * R⁻¹ ^ 2) * ((L : ℝ)⁻¹ * specMass ν (α / R)⁻¹) := by ring
      _ ≤ (Ch * R⁻¹ ^ 2) * (2 * t) := mul_le_mul_of_nonneg_left hmh.le (by positivity)
      _ = (2 * Ch) * (R⁻¹ ^ 2 * t) := by ring
      _ ≤ C * (R⁻¹ ^ 2 * t) := mul_le_mul_of_nonneg_right hChigh (by positivity)
      _ = _ := by ring

end Critical2DKPZ.Extensions.ScaleLimit
