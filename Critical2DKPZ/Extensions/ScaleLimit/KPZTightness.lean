/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.InitialTightness
public import Critical2DKPZ.Extensions.ScaleLimit.SequenceTightness

/-! # Applying an asymptotic scale modulus to path laws

An asymptotic modulus in probability gives tightness of the scale-path laws.
The initial-value bound is proved independently, and finite prefixes are
handled by the general sequence tightness criterion.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter TopologicalSpace
open scoped NNReal ENNReal Topology BoundedContinuousFunction
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The event of a large oscillation at some nearby pair of times is open in the
uniform path topology; the pair of times is allowed to range over the whole interval. -/
theorem isOpen_path_modulus_event (S : ℝ≥0) (δ η : ℝ) :
    IsOpen {f : ScalePath S | ∃ s r : ScaleInterval S,
      dist (s : ℝ) (r : ℝ) ≤ δ ∧ η < |f s - f r|} := by
  apply isOpen_iff_mem_nhds.mpr
  rintro f ⟨s, r, hsr, hv⟩
  have hopen : IsOpen {g : ScalePath S | η < |g s - g r|} :=
    isOpen_lt continuous_const (by fun_prop)
  apply mem_of_superset (hopen.mem_nhds hv)
  intro g hg
  exact ⟨s, r, hsr, hg⟩

/-- An asymptotic modulus in probability
gives tightness along each divergent positive-real scale sequence. -/
theorem kpz_isTight_of_modulus
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    {t : ℝ} (ht : 0 < t) (x : Plane) (φ : TestFn) (S : ℝ≥0)
    (hmod : ∀ η : ℝ, 0 < η → ∀ ρ : ℝ, 0 < ρ →
      ∃ δ : ℝ, 0 < δ ∧ ∃ L₀ : ℝ, ∀ L : Set.Ioi (0 : ℝ), L₀ ≤ (L : ℝ) →
        P {ω | ∃ s r : ScaleInterval S, dist (s : ℝ) (r : ℝ) ≤ δ ∧
          η < |scaledPairing (H t 0 ω) φ x L s - scaledPairing (H t 0 ω) φ x L r|}
          ≤ ENNReal.ofReal ρ)
    (u : ℕ → Set.Ioi (0 : ℝ)) (hu : Tendsto (fun n => (u n : ℝ)) atTop atTop) :
    IsTightMeasureSet (Set.range (fun n =>
      P.map (fun ω => scalePath S (H t 0 ω) φ x (u n)))) := by
  let laws : ℕ → ProbabilityMeasure (ScalePath S) := fun n =>
    ⟨P.map (fun ω => scalePath S (H t 0 ω) φ x (u n)), inferInstance⟩
  apply isTightMeasureSet_of_eventual_modulus laws
    (kpz_initial_tail_bound ϑ P Z hZ H hH ht x φ S u hu)
  intro η hη ε hε
  obtain ⟨δ, hδ, L₀, hL⟩ := hmod η hη ε hε
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hu.eventually (eventually_ge_atTop L₀)] with n hn
  change (P.map (fun ω => scalePath S (H t 0 ω) φ x (u n)))
    {f | ∃ s r : ScaleInterval S,
      dist (s : ℝ) (r : ℝ) ≤ δ ∧ η < |f s - f r|} ≤ ENNReal.ofReal ε
  rw [Measure.map_apply_of_aemeasurable
    (aemeasurable_scalePath ϑ P Z hZ H hH ht x φ S (u n))
    (isOpen_path_modulus_event S δ η).measurableSet]
  exact hL (u n) hn

end Critical2DKPZ.Extensions.ScaleLimit
