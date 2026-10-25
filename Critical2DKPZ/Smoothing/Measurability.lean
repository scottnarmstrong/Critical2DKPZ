/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Smoothing.Basic
public import Critical2DKPZ.Polymer.Profiles
public import Critical2DKPZ.Analysis.Lattice.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-! # Measurability of tested smoothing errors -/

@[expose] public noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction

namespace Critical2DKPZ.Smoothing

/-- Measurable initial profiles and environments give a measurable profile pairing. -/
theorem measurable_profileP2Fun_param {E : Type*} [MeasurableSpace E]
    (β : ℝ) (a b : ℕ) (f : Site → ℝ) {ν : E → Site → ℝ} {ξ : E → Disorder}
    (hν : ∀ w, Measurable (fun p => ν p w)) (hξ : Measurable ξ) :
    Measurable (fun p => profileP2Fun β a b (ν p) f (ξ p)) := by
  unfold profileP2Fun
  exact Measurable.tsum fun w => (hν w).mul
    (Measurable.tsum fun z => ((Polymer.measurable_pointToPoint β a (b - a) w z).comp hξ).mul_const (f z))

/-- Centering by the flat terminal pairing preserves joint measurability. -/
theorem measurable_centered_profile_log_param {E : Type*} [MeasurableSpace E]
    (β : ℝ) (a b : ℕ) (f : Site → ℝ) {ν : E → Site → ℝ} {ξ : E → Disorder}
    (hν : ∀ w, Measurable (fun p => ν p w)) (hξ : Measurable ξ) :
    Measurable (fun p => Real.log (profileP2Fun β a b (ν p) f (ξ p)) -
      ∫ ω', Real.log (profileP2Fun β a b (ν p) (fun _ => 1) ω') ∂disorderLaw) := by
  have hm := (measurable_profileP2Fun_param β a b f hν hξ).log
  have hc : Measurable (fun p : E =>
      ∫ ω', Real.log (profileP2Fun β a b (ν p) (fun _ => 1) ω') ∂disorderLaw) := by
    have h := (measurable_profileP2Fun_param β a b (fun _ => 1)
      (fun w => (hν w).comp measurable_fst)
      (show Measurable (fun p : E × Disorder => p.2) from measurable_snd)).log
    exact h.stronglyMeasurable.integral_prod_right'.measurable
  exact hm.sub hc

/-- The tested difference is measurable for every measurable spatial test. -/
theorem measurable_latticeSmoothingError (β : ℝ) (N M k j : ℕ) (h₀ : Plane →ᵇ ℝ)
    {φ : Plane → ℝ} (hφ : Measurable φ) :
    Measurable (latticeSmoothingError β N M k j h₀ φ) := by
  have hν : ∀ w : Site, Measurable (fun p : Disorder × Plane =>
      if w = latticePoint N p.2 then (1 : ℝ) else 0) := by
    intro w
    exact Measurable.ite (measurableSet_eq_fun measurable_const
      ((measurable_latticePoint N).comp measurable_snd)) measurable_const measurable_const
  have hη : ∀ w : Site, Measurable (fun p : Disorder × Plane => srwKernel j (w - latticePoint N p.2)) := by
    intro w
    exact (measurable_of_countable (fun z : Site => srwKernel j (w - z))).comp
      ((measurable_latticePoint N).comp measurable_snd)
  have hp := measurable_centered_profile_log_param β 0 M
    (cellAverage N fun y => Real.exp (h₀ y)) hν
    (show Measurable (fun p : Disorder × Plane => p.1) from measurable_fst)
  have hs := measurable_centered_profile_log_param β k M
    (cellAverage N fun y => Real.exp (h₀ y)) hη
    (show Measurable (fun p : Disorder × Plane => p.1) from measurable_fst)
  exact ((hφ.comp measurable_snd).mul (hp.sub hs)).stronglyMeasurable.integral_prod_right'.measurable

end Critical2DKPZ.Smoothing

end
