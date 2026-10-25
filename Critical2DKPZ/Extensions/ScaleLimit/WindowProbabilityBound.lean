/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.WindowRemainderEnvelopes
public import Critical2DKPZ.Extensions.ScaleLimit.DenseOscillationControl
public import Critical2DKPZ.Extensions.ScaleLimit.SchwartzMaximalControl
public import Critical2DKPZ.Extensions.ScaleLimit.WindowGaussianLimit
public import Critical2DKPZ.Extensions.ScaleLimit.SquareEnvelopeMarkov
public import Critical2DKPZ.Extensions.ScaleLimit.SquareTailScaling
import Mathlib.Tactic

/-! # The one-window probability estimate before taking limits -/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped Topology
namespace Critical2DKPZ.Extensions.ScaleLimit

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {D : Ω → Distr} {ν : Measure Plane}

/-- The oscillation event on a closed real time window. -/
def windowOscillationEvent (X : ℝ → Ω → ℝ) (s t η : ℝ) : Set Ω :=
  {ω | ∃ p q : Set.Icc s t, η < |X p ω - X q ω|}

/-- The exact three-term probability estimate. The constants precede the
window and the auxiliary band separation; the residual terms vanish as
`R` tends to infinity after the scale limit. -/
theorem window_probability_bound (hD : StationarySpectralData P D ν)
    (φ : TestFn) (hφ : (∫ z, φ z) = 1) (x : Plane) :
    ∃ Cm c Cr : ℝ, 0 < Cm ∧ 0 < c ∧ 0 < Cr ∧
      ∀ R s t η : ℝ, 0 < R → 0 ≤ s → s < t → 0 < η →
        ∀ᶠ L : Set.Ioi (0 : ℝ) in atTop,
          P (windowOscillationEvent (fun r ω => scaledPairing (D ω) φ x L r) s t η) ≤
            ENNReal.ofReal ((36 * Cm / η ^ 2) *
              ∫ ω, squareTail (c * η / 6) (bandWindowVariable hD R s t x L ω) ∂P) +
            ENNReal.ofReal (36 * (Cr * R⁻¹ ^ 2 * t) / η ^ 2) +
            ENNReal.ofReal (36 * (Cr * R⁻¹ ^ 2 * t) / η ^ 2) := by
  obtain ⟨Cm, c, hCm, hc, hmax⟩ := band_truncated_maximal hD φ
  obtain ⟨Cr, hCr, hrem⟩ := window_remainder_envelopes hD φ hφ x
  refine ⟨Cm, c, Cr, hCm, hc, hCr, ?_⟩
  intro R s t η hR hs hst hη
  filter_upwards [hrem R s t hR hs hst] with L hLrem
  obtain ⟨u, w, ZU, ZW, hrep, hUi, hWi, hU0, hW0, henv, hUb, hWb⟩ := hLrem
  let α := scaleRadius L t
  let β := scaleRadius L s
  let a := α / R
  let b := R * β
  let Λ := η * Real.sqrt (L : ℝ) / 6
  have hΛ : 0 < Λ := div_pos (mul_pos hη (Real.sqrt_pos.mpr L.property)) (by norm_num)
  let T := Set.Icc s t
  have : Nonempty T := ⟨⟨s, ⟨le_rfl, hst.le⟩⟩⟩
  let X : T → Ω → ℝ := fun q ω => D ω (φ.dilate (scaleRadius L q) x)
  let Y : T → Ω → ℝ := fun q ω => ∫ z, φ z * schwartzField hD
    (zetaScaled a 0 - zetaScaled b 0) (x + scaleRadius L q • z) ω
  let U : T → Ω → ℝ := fun q ω => u (scaleRadius L q) ω
  let W : T → Ω → ℝ := fun q ω => w (scaleRadius L q) ω
  let M : Set Ω := {ω | ENNReal.ofReal Λ < ⨆ r : {r : ℝ // 0 < r}, ENNReal.ofReal
    |∫ z, φ z * schwartzField hD (zetaScaled a 0 - zetaScaled b 0) (x + (r : ℝ) • z) ω|}
  have hr (q : T) : scaleRadius L q ∈ Set.Icc α β :=
    ⟨scaleRadius_antitone L.property.le q.property.2, scaleRadius_antitone L.property.le q.property.1⟩
  have hX (ω : Ω) : Continuous (fun q : T => X q ω) :=
    ((D ω).continuous.comp (continuous_scaleRadius_dilate φ x L)).comp continuous_subtype_val
  have hdec (q : T) : ∀ᵐ ω ∂P, X q ω = Y q ω + bandField hD b x ω + U q ω + W q ω := by
    filter_upwards [band_decomposition hD a b φ x (scaleRadius L q),
      (hrep _ (hr q)).1, (hrep _ (hr q)).2] with ω hd hu hw
    change _ = bandLowRemainder hD b φ x (scaleRadius L q) ω at hu
    change _ = bandHighRemainder hD a φ x (scaleRadius L q) ω at hw
    rw [← hu, ← hw] at hd
    exact hd
  have hU : ∀ᵐ ω ∂P, ∀ q : T, U q ω ^ 2 ≤ ZU ω := henv.mono fun ω h q => (h _ (hr q)).1
  have hW : ∀ᵐ ω ∂P, ∀ q : T, W q ω ^ 2 ≤ ZW ω := henv.mono fun ω h q => (h _ (hr q)).2
  have hY (ω : Ω) (hω : ω ∉ M) (q : T) : |Y q ω| ≤ Λ := by
    have hsup : (⨆ r : {r : ℝ // 0 < r}, ENNReal.ofReal
        |∫ z, φ z * schwartzField hD (zetaScaled a 0 - zetaScaled b 0) (x + (r : ℝ) • z) ω|) ≤
        ENNReal.ofReal Λ := le_of_not_gt hω
    have hh := (le_iSup (fun r : {r : ℝ // 0 < r} => ENNReal.ofReal
      |∫ z, φ z * schwartzField hD (zetaScaled a 0 - zetaScaled b 0) (x + (r : ℝ) • z) ω|)
        ⟨scaleRadius L q, scaleRadius_pos L q⟩).trans hsup
    exact (ENNReal.ofReal_le_ofReal_iff hΛ.le).mp hh
  have hosc := oscillation_measure_le_of_dense_decomposition P X Y U W
    (bandField hD b x) ZU ZW M hΛ.le hX hdec hU hW hY
  have hsub : windowOscillationEvent (fun r ω => scaledPairing (D ω) φ x L r) s t η ⊆
      {ω | ∃ p q : T, 6 * Λ < |X p ω - X q ω|} := by
    rintro ω ⟨p, q, hpq⟩
    refine ⟨p, q, ?_⟩
    change η < |D ω (φ.dilate (scaleRadius L p) x) / Real.sqrt (L : ℝ) -
      D ω (φ.dilate (scaleRadius L q) x) / Real.sqrt (L : ℝ)| at hpq
    rw [← sub_div, abs_div, abs_of_pos (Real.sqrt_pos.mpr L.property)] at hpq
    have hh := (lt_div_iff₀ (Real.sqrt_pos.mpr L.property)).mp hpq
    change 6 * (η * Real.sqrt (L : ℝ) / 6) < _
    convert hh using 1; ring
  have hM := hmax a b x Λ hΛ
  rw [squareTail_window_normalization P (fun ω => bandField hD a x ω - bandField hD b x ω)
    Cm c L.property hη] at hM
  have hfun : (fun ω => (Real.sqrt (L : ℝ))⁻¹ * (bandField hD a x ω - bandField hD b x ω)) =
      bandWindowVariable hD R s t x L := by
    funext ω
    dsimp [bandWindowVariable, a, b, α, β]
    rw [div_eq_mul_inv, mul_comm (scaleRadius L t) R⁻¹]
  have hpoint (ω : Ω) : (Real.sqrt (L : ℝ))⁻¹ * (bandField hD a x ω - bandField hD b x ω) =
      bandWindowVariable hD R s t x L ω := congrFun hfun ω
  simp_rw [hpoint] at hM
  exact (measure_mono hsub).trans (hosc.trans (add_le_add
    (add_le_add hM (measure_window_square_envelope_le P ZU hUi hU0 hη L.property hUb))
    (measure_window_square_envelope_le P ZW hWi hW0 hη L.property hWb)))

end Critical2DKPZ.Extensions.ScaleLimit
