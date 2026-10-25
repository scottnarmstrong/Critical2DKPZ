/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.Response.CutoffMeasurable
public import Critical2DKPZ.Extensions.Response.LogMGF
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-! # Starting-point laws for the cutoff response

The terminal heat kernel weights the flow before projection to its first endpoint.
The logarithmic response is the normalized log-MGF of the resulting finite measure.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped BoundedContinuousFunction ENNReal Topology
namespace Critical2DKPZ.Extensions.Response

/-- Unnormalised starting-point measure for a terminally smoothed polymer. -/
def cutoffBase {Ω : Type*} (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (t r : ℝ) (h : Plane →ᵇ ℝ) (x : Plane) (ω : Ω) : Measure Plane :=
  ((Z 0 t ω).withDensity (fun p => ENNReal.ofReal
    (Real.exp (h p.1) * heatKernel r (p.2 - x)))).map Prod.fst

/-- The starting-point probability law on the good event, with exponential tilt. -/
def startingLaw {Ω : Type*} (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (t r : ℝ) (h v : Plane →ᵇ ℝ) (x : Plane) (q : ℝ) (ω : Ω) : Measure Plane :=
  (cutoffBase Z t r h x ω).tilted (fun y => q * v y)

/-- Integration against the base measure unfolds into the original flow pairing. -/
theorem integral_cutoffBase {Ω : Type*} (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (t r : ℝ) (hr : 0 < r) (h v : Plane →ᵇ ℝ) (x : Plane) (ω : Ω) (k : ℕ) (q : ℝ) :
    (∫ y, v y ^ k * Real.exp (q * v y) ∂(cutoffBase Z t r h x ω)) =
      shfPairing Z 0 t (fun y => Real.exp (h y + q * v y) * v y ^ k)
        (fun y => heatKernel r (y - x)) ω := by
  rw [cutoffBase, integral_map measurable_fst.aemeasurable (by fun_prop)]
  rw [integral_withDensity_eq_integral_toReal_smul
    (f := fun p : Plane × Plane => ENNReal.ofReal (Real.exp (h p.1) * heatKernel r (p.2 - x)))
    (g := fun p : Plane × Plane => v p.1 ^ k * Real.exp (q * v p.1))
    (((h.continuous.measurable.comp measurable_fst).exp.mul
      ((measurable_heatKernel r).comp (measurable_snd.sub_const x))).ennreal_ofReal)
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le (heatKernel_nonneg hr.le _)),
    smul_eq_mul, shfPairing, Real.exp_add]
  congr 1
  ext p
  ring

/-- The base starting measure is finite whenever the flat terminal heat kernel is
integrable at the spatial centre. -/
theorem isFiniteMeasure_cutoffBase {Ω : Type*}
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (t r : ℝ) (hr : 0 < r)
    (h : Plane →ᵇ ℝ) (x : Plane) (ω : Ω)
    (hint : Integrable (fun p : Plane × Plane => heatKernel r (p.2 - x)) (Z 0 t ω)) :
    IsFiniteMeasure (cutoffBase Z t r h x ω) := by
  have hi := integrable_weighted_heat hr x hint
    (Real.continuous_exp.comp h.continuous) (exp_profile_bound h)
  have hn : ∀ᵐ p ∂(Z 0 t ω), 0 ≤ Real.exp (h p.1) * heatKernel r (p.2 - x) :=
    Eventually.of_forall (fun p => mul_nonneg (Real.exp_pos _).le (heatKernel_nonneg hr.le _))
  let : IsFiniteMeasure ((Z 0 t ω).withDensity (fun p => ENNReal.ofReal
      (Real.exp (h p.1) * heatKernel r (p.2 - x)))) :=
    isFiniteMeasure_withDensity ((lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable hn).mpr hi)
  exact Measure.isFiniteMeasure_map _ _

/-- The base starting measure has nonzero mass on the deterministic good event. -/
theorem neZero_cutoffBase {Ω : Type*}
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (t r : ℝ) (hr : 0 < r)
    (h : Plane →ᵇ ℝ) (x : Plane) (ω : Ω)
    (hint : ∀ x, Integrable (fun p : Plane × Plane => heatKernel r (p.2 - x)) (Z 0 t ω))
    (hpos : 0 < shfPairing Z 0 t (fun _ => 1) (heatKernel r) ω) :
    NeZero (cutoffBase Z t r h x ω) := by
  have hp : 0 < shfPairing Z 0 t (fun y => Real.exp (h y))
      (fun y => heatKernel r (y - x)) ω := by
    unfold shfPairing
    exact pairing_pos hr hint
      (by simpa only [shfPairing, one_mul] using hpos)
      (Real.continuous_exp.comp h.continuous) (exp_profile_bound h)
      (fun y => Real.exp_pos _) x
  constructor
  intro hz
  have heq := integral_cutoffBase Z t r hr h (0 : Plane →ᵇ ℝ) x ω 0 0
  simp only [hz, integral_zero_measure, pow_zero, zero_mul, Real.exp_zero,
    add_zero, mul_one] at heq
  linarith only [hp, heq]








end Critical2DKPZ.Extensions.Response
