/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.Plane
public import Critical2DKPZ.SHF.DeltaBose.DiagramSeries
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Topology.ContinuousMap.CompactlySupported

/-! # Tsai's dense-time stochastic heat-flow axioms

The flow predicate includes
measurability, almost-sure local finiteness, approximate composition, independent
increments and the first four moment formulas. It makes no path-continuity assumption.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal BigOperators CompactlySupported

namespace Critical2DKPZ.SHF.Tsai

/-- Tsai Definition 1.1: an `L²`-applicable mollifier. -/
def IsL2ApplicableMollifier (w : ℕ → Plane → ℝ) : Prop :=
  (∀ ℓ x, 0 ≤ w ℓ x) ∧ (∀ ℓ, Continuous (w ℓ)) ∧ (∀ ℓ, MemLp (w ℓ) 2) ∧
  (∀ ℓ, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ φ : Plane → ℝ, MemLp φ 2 →
    MemLp (fun x => ∫ y, w ℓ (x - y) * φ y) 2 ∧
      eLpNorm (fun x => ∫ y, w ℓ (x - y) * φ y) 2 ≤ M * eLpNorm φ 2) ∧
  ∀ φ : Plane → ℝ, MemLp φ 2 →
    Tendsto (fun ℓ => eLpNorm (fun x => (∫ y, w ℓ (x - y) * φ y) - φ x) 2) atTop (𝓝 0)

/-- Tsai Definition 1.1: `(μ ⋆_w ν) f = ∫ μ(dx₁ dx₂) w(x₂ − x₃) ν(dx₃ dx₄) f(x₁, x₄)`. -/
def smoothedProductPairing (μ : Measure (Plane × Plane)) (w : Plane → ℝ) (ν : Measure (Plane × Plane))
    (f : Plane × Plane → ℝ) : ℝ :=
  ∫ q, f (q.1.1, q.2.2) * w (q.1.2 - q.2.1) ∂(μ.prod ν)

/-- Tsai Definition 1.1: the product is well-defined (absolute convergence for every compact test). -/
def SmoothedProductWellDefined (μ : Measure (Plane × Plane)) (w : Plane → ℝ)
    (ν : Measure (Plane × Plane)) : Prop :=
  ∀ f : C_c(Plane × Plane, ℝ),
    Integrable (fun q : (Plane × Plane) × (Plane × Plane) => f (q.1.1, q.2.2) * w (q.1.2 - q.2.1))
      (μ.prod ν)

/-- Tsai Definition 1.2 (b)–(d) on the strict pairs of a time set `D` (the hypotheses of Tsai
Theorem 1.9), with the measurability and local finiteness of each `Z s t`. -/
def IsDenseSHF (θ : ℝ) (D : Set ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) : Prop :=
  (∀ s ∈ D, ∀ t ∈ D, s < t → Measurable (Z s t) ∧ ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (Z s t ω)) ∧
  (∀ t₀ ∈ D, ∀ t₁ ∈ D, ∀ t₂ ∈ D, t₀ < t₁ → t₁ < t₂ →
    ∃ w : ℕ → Plane → ℝ, IsL2ApplicableMollifier w ∧
      (∀ ℓ, ∀ᵐ ω ∂P, SmoothedProductWellDefined (Z t₀ t₁ ω) (w ℓ) (Z t₁ t₂ ω)) ∧
      ∀ f : C_c(Plane × Plane, ℝ),
        TendstoInMeasure P (fun ℓ ω => smoothedProductPairing (Z t₀ t₁ ω) (w ℓ) (Z t₁ t₂ ω) f -
          ∫ p, f p ∂(Z t₀ t₂ ω)) atTop (fun _ => 0)) ∧
  (∀ (k : ℕ) (t : Fin (k + 1) → ℝ), StrictMono t → (∀ i, t i ∈ D) →
    iIndepFun (fun i : Fin k => Z (t i.castSucc) (t i.succ)) P) ∧
  ∀ n : ℕ, 1 ≤ n → n ≤ 4 → ∀ s ∈ D, ∀ t ∈ D, s < t →
    ∀ g g' : Fin n → Plane → ℝ, (∀ i, MemLp (g i) 2) → (∀ i, MemLp (g' i) 2) →
      (∀ᵐ ω ∂P, ∀ i, Integrable (fun p : Plane × Plane => g i p.1 * g' i p.2) (Z s t ω)) ∧
      Integrable (fun ω => ∏ i, ∫ p, g i p.1 * g' i p.2 ∂(Z s t ω)) P ∧
      ∫ ω, ∏ i, (∫ p, g i p.1 * g' i p.2 ∂(Z s t ω)) ∂P =
        ∫ x : DeltaBose.Configuration n, ∫ y : DeltaBose.Configuration n,
          (∏ i, g i (x i)) * (DeltaBose.momentKernel n θ (t - s) x y).toReal * ∏ i, g' i (y i)

/-- `χ_R(x) = min 1 (max 0 (R + 1 − |x|))`, the intermediate-variable cutoff of the cutoff-tail estimate. -/
def ballCutoff (R : ℝ) (x : Plane) : ℝ := min 1 (max 0 (R + 1 - ‖x‖))

end Critical2DKPZ.SHF.Tsai

end
