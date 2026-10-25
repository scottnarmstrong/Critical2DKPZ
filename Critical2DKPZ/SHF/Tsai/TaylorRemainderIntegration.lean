/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.TaylorMomentComparison

/-! # Fourth-moment bounds for Taylor expectations

Finite coordinate fourth moments make the cubic Taylor remainder integrable and bound its
expectation. Matching cubic moments then bounds the difference of nonlinear expectations.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace Critical2DKPZ.SHF.Tsai

/-- The actual cubic Taylor remainder is integrable and has the exact fourth-moment expectation bound. -/
theorem integrable_cubicTaylorRemainder_and_abs_integral_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {m : ℕ} (X : Ω → Fin m → ℝ) (hXm : AEStronglyMeasurable X P)
    (hX4 : Integrable (fun ω => ∑ i, X ω i ^ 4) P)
    (H : (Fin m → ℝ) → ℝ) (hH : ContDiff ℝ 4 H) (CH : ℝ)
    (hCH : ∀ z, ‖iteratedFDeriv ℝ 4 H z‖ ≤ CH) (x : Fin m → ℝ)
    (hT : Integrable (fun ω => ∑ k ∈ Finset.range 4,
      (k.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ k H x (fun _ => X ω)) P) :
    Integrable (fun ω => H (x + X ω) - ∑ k ∈ Finset.range 4,
      (k.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ k H x (fun _ => X ω)) P ∧
    |∫ ω, (H (x + X ω) - ∑ k ∈ Finset.range 4,
      (k.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ k H x (fun _ => X ω)) ∂P| ≤
        CH / 24 * ∫ ω, ∑ i, X ω i ^ 4 ∂P := by
  let R (ω : Ω) := H (x + X ω) - ∑ k ∈ Finset.range 4,
    (k.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ k H x (fun _ => X ω)
  have harg : AEStronglyMeasurable (fun ω => x + X ω) P := aestronglyMeasurable_const.add hXm
  have hRm : AEStronglyMeasurable R P :=
    (hH.continuous.comp_aestronglyMeasurable harg).sub hT.aestronglyMeasurable
  have hpoint (ω : Ω) : ‖R ω‖ ≤ CH / 24 * ∑ i, X ω i ^ 4 := by
    simpa only [Real.norm_eq_abs] using abs_sub_cubicTaylor_le_sum_four H hH CH hCH x (X ω)
  have hdom : Integrable (fun ω => CH / 24 * ∑ i, X ω i ^ 4) P := hX4.const_mul _
  have hRI : Integrable R P := hdom.mono' hRm (Filter.Eventually.of_forall hpoint)
  refine ⟨hRI, ?_⟩
  have hbound := integral_mono_ae hRI.norm hdom (Filter.Eventually.of_forall hpoint)
  rw [integral_const_mul] at hbound
  exact (abs_integral_le_integral_abs).trans hbound

/-- Cubic moment matching bounds the difference of nonlinear expectations by both fourth moments. -/
theorem abs_integral_add_sub_le_of_cubic_coordinate_moments {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω') {m : ℕ}
    (X : Ω → Fin m → ℝ) (Y : Ω' → Fin m → ℝ)
    (hXm : AEStronglyMeasurable X P) (hYm : AEStronglyMeasurable Y P')
    (hX4 : Integrable (fun ω => ∑ i, X ω i ^ 4) P)
    (hY4 : Integrable (fun ω => ∑ i, Y ω i ^ 4) P')
    (hX : ∀ k ≤ 3, ∀ q : Fin k → Fin m, Integrable (fun ω => ∏ i, X ω (q i)) P)
    (hY : ∀ k ≤ 3, ∀ q : Fin k → Fin m, Integrable (fun ω => ∏ i, Y ω (q i)) P')
    (hEq : ∀ k ≤ 3, ∀ q : Fin k → Fin m,
      (∫ ω, ∏ i, X ω (q i) ∂P) = ∫ ω, ∏ i, Y ω (q i) ∂P')
    (H : (Fin m → ℝ) → ℝ) (hH : ContDiff ℝ 4 H) (CH : ℝ)
    (hCH : ∀ z, ‖iteratedFDeriv ℝ 4 H z‖ ≤ CH) (x : Fin m → ℝ) :
    Integrable (fun ω => H (x + X ω)) P ∧ Integrable (fun ω => H (x + Y ω)) P' ∧
    |(∫ ω, H (x + X ω) ∂P) - ∫ ω, H (x + Y ω) ∂P'| ≤
      CH / 24 * ((∫ ω, ∑ i, X ω i ^ 4 ∂P) + ∫ ω, ∑ i, Y ω i ^ 4 ∂P') := by
  let T (v : Fin m → ℝ) := ∑ k ∈ Finset.range 4,
    (k.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ k H x (fun _ => v)
  obtain ⟨hTX, hTY, hTEq⟩ := integral_cubicTaylor_eq_of_coordinate_moments P P' X Y hX hY hEq H x
  obtain ⟨hRX, hBX⟩ := integrable_cubicTaylorRemainder_and_abs_integral_le
    P X hXm hX4 H hH CH hCH x hTX
  obtain ⟨hRY, hBY⟩ := integrable_cubicTaylorRemainder_and_abs_integral_le
    P' Y hYm hY4 H hH CH hCH x hTY
  have hHX : Integrable (fun ω => H (x + X ω)) P :=
    (hRX.add hTX).congr (Filter.Eventually.of_forall fun ω => sub_add_cancel _ _)
  have hHY : Integrable (fun ω => H (x + Y ω)) P' :=
    (hRY.add hTY).congr (Filter.Eventually.of_forall fun ω => sub_add_cancel _ _)
  have hIX := integral_sub hHX hTX
  have hIY := integral_sub hHY hTY
  have herror : (∫ ω, H (x + X ω) ∂P) - (∫ ω, H (x + Y ω) ∂P') =
      (∫ ω, (H (x + X ω) - T (X ω)) ∂P) -
        ∫ ω, (H (x + Y ω) - T (Y ω)) ∂P' := by
    rw [hIX, hIY, hTEq]
    ring
  refine ⟨hHX, hHY, ?_⟩
  rw [herror]
  exact (abs_sub _ _).trans ((add_le_add hBX hBY).trans_eq (by ring))

end Critical2DKPZ.SHF.Tsai

end
