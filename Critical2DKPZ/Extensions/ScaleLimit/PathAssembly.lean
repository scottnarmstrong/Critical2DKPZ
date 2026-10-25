/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.KPZTightness
public import Critical2DKPZ.Extensions.ScaleLimit.PathConvergence

/-! # The path-law assembly from the scale modulus

An asymptotic modulus in probability gives tightness of the literal scale
paths. Their Brownian finite-dimensional limits identify the unique Wiener
law, yielding path convergence in the uniform topology.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology BoundedContinuousFunction
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- A scale modulus gives a unique Wiener law and literal-path convergence.
The modulus premise and the finite-dimensional Brownian limit give tightness
and identify the limiting law. -/
theorem existsUnique_wienerLaw_and_scale_convergence_of_modulus
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (t : ℝ) (ht : 0 < t) (x : Plane) (φ : TestFn)
    (hφ : ∀ y, 0 ≤ φ y) (hφ1 : (∫ y, φ y) = 1) (S : ℝ≥0)
    (hmod : ∀ η : ℝ, 0 < η → ∀ ρ : ℝ, 0 < ρ →
      ∃ δ : ℝ, 0 < δ ∧ ∃ L₀ : ℝ, ∀ L : Set.Ioi (0 : ℝ), L₀ ≤ (L : ℝ) →
        P {ω | ∃ s r : ScaleInterval S, dist (s : ℝ) (r : ℝ) ≤ δ ∧
          η < |scaledPairing (H t 0 ω) φ x L s - scaledPairing (H t 0 ω) φ x L r|}
          ≤ ENNReal.ofReal ρ) :
    ∃! μ : ProbabilityMeasure (ScalePath S),
      IsWienerLaw S μ ∧
      ∃ X : Set.Ioi (0 : ℝ) → Ω → ScalePath S,
        (∀ L ω s, X L ω s = scaledPairing (H t 0 ω) φ x L s) ∧
        TendstoInDistribution X atTop id (fun _ => P) (μ : Measure (ScalePath S)) := by
  have hTight := kpz_isTight_of_modulus ϑ P Z hZ H hH ht x φ S hmod
  let u : ℕ → Set.Ioi (0 : ℝ) := fun n => ⟨(n : ℝ) + 1, by change (0 : ℝ) < (n : ℝ) + 1; positivity⟩
  have hu : Tendsto (fun n => (u n : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  obtain ⟨μ, hμ, _⟩ := existsUnique_wienerLaw_of_tight ϑ P Z hZ H hH ht x φ hφ hφ1 S
    u hu (hTight u hu)
  refine ⟨μ, ⟨hμ, ?_⟩, ?_⟩
  · refine ⟨fun L ω => scalePath S (H t 0 ω) φ x L, fun _ _ _ => rfl, ?_⟩
    exact tendstoInDistribution_scalePath_of_tight ϑ P Z hZ H hH ht x φ hφ hφ1 S hTight hμ
  · intro ν hν
    exact eq_of_isWienerLaw ν μ hν.1 hμ

end Critical2DKPZ.Extensions.ScaleLimit
