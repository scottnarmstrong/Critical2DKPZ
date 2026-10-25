/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.KpzRegularized
public import Critical2DKPZ.Extensions.Response.TildeH
import Mathlib.Tactic.Linarith

/-! # Spatial shifts and arithmetic of convergence in measure

The pointwise shift rewrites temporal regularization at `t + r` as spatial
smoothing of the flow at `t`. Addition and subtraction preserve convergence
in measure for arbitrary index filters and measures.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

namespace Critical2DKPZ.Extensions.Response

variable {Ω ι : Type*} [MeasurableSpace Ω]

/-- The shifted temporal field uses precisely the time-`t` flow and its centring.
No positivity or size condition on the shift is needed for this identity. -/
theorem kpzRegularized_add_shift (P : Measure Ω)
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (t r : ℝ)
    (h : Plane →ᵇ ℝ) (x : Plane) (ω : Ω) :
    kpzRegularized P Z (t + r) r h x ω =
      Real.log (shfPairing Z 0 t (fun y => Real.exp (h y))
        (fun y => heatKernel r (y - x)) ω) -
      ∫ ω', Real.log (shfPairing Z 0 t (fun _ => 1) (heatKernel r) ω') ∂P := by
  simp only [kpzRegularized, add_sub_cancel_right]

/-- Testing the spatially smoothed field equals testing the temporal field
at the shifted time, with exactly the same centring. -/
theorem spatialCenteredPairing_eq_integral_kpzRegularized (P : Measure Ω)
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (t r : ℝ) (h : Plane →ᵇ ℝ) (ψ : TestFn) (ω : Ω) :
    spatialCenteredPairing P Z t r h ψ ω =
      ∫ x, ψ x * kpzRegularized P Z (t + r) r h x ω := by
  simp only [spatialCenteredPairing, kpzRegularized_add_shift]

/-- Addition preserves convergence in measure, without measurability assumptions. -/
theorem tendstoInMeasure_add (P : Measure Ω) {l : Filter ι}
    {f f' : ι → Ω → ℝ} {g g' : Ω → ℝ}
    (hf : TendstoInMeasure P f l g) (hf' : TendstoInMeasure P f' l g') :
    TendstoInMeasure P (fun i ω => f i ω + f' i ω) l (fun ω => g ω + g' ω) := by
  rw [tendstoInMeasure_iff_dist] at hf hf' ⊢
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have hsum : Tendsto
      (fun i => P {ω | ε / 2 ≤ dist (f i ω) (g ω)} +
        P {ω | ε / 2 ≤ dist (f' i ω) (g' ω)}) l (𝓝 0) := by
    simpa only [add_zero] using (hf (ε / 2) hhalf).add (hf' (ε / 2) hhalf)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) ?_
  intro i
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro ω hω
  by_contra hnot
  have ha : dist (f i ω) (g ω) < ε / 2 :=
    lt_of_not_ge (fun h => hnot (Or.inl h))
  have hb : dist (f' i ω) (g' ω) < ε / 2 :=
    lt_of_not_ge (fun h => hnot (Or.inr h))
  have htriangle := dist_add_add_le (f i ω) (f' i ω) (g ω) (g' ω)
  change ε ≤ dist (f i ω + f' i ω) (g ω + g' ω) at hω
  linarith only [ha, hb, htriangle, hω]

/-- Subtraction preserves convergence in measure for any index filter. -/
theorem tendstoInMeasure_sub (P : Measure Ω) {l : Filter ι}
    {f f' : ι → Ω → ℝ} {g g' : Ω → ℝ}
    (hf : TendstoInMeasure P f l g) (hf' : TendstoInMeasure P f' l g') :
    TendstoInMeasure P (fun i ω => f i ω - f' i ω) l (fun ω => g ω - g' ω) := by
  have hneg : TendstoInMeasure P (fun i ω => -f' i ω) l (fun ω => -g' ω) := by
    rw [tendstoInMeasure_iff_dist] at hf' ⊢
    simpa only [dist_neg_neg] using hf'
  simpa only [sub_eq_add_neg] using tendstoInMeasure_add P hf hneg

end Critical2DKPZ.Extensions.Response
