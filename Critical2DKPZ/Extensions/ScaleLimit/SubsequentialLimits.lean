/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.PathMeasurability
public import Critical2DKPZ.Extensions.ScaleLimit.FiniteDimensional
import Critical2DKPZ.RandomMeasure.GeneralProduct

/-! # Subsequential laws of the scale paths

Tight sequences of literal continuous scale paths have weakly convergent
subsequences. The finite-dimensional limit theorem identifies every such
limit with the Wiener-law predicate.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BoundedContinuousFunction
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Prokhorov extraction for any sequence of measurable continuous scale paths. -/
theorem exists_subseq_limit {S : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ScalePath S)
    (hX : ∀ n, AEMeasurable (X n) P)
    (hTight : IsTightMeasureSet (Set.range (fun n => P.map (X n)))) :
    ∃ (v : ℕ → ℕ) (μ : ProbabilityMeasure (ScalePath S)), StrictMono v ∧
      TendstoInDistribution (fun n => X (v n)) atTop id (fun _ => P)
        (μ : Measure (ScalePath S)) := by
  let laws : ℕ → ProbabilityMeasure (ScalePath S) := fun n => ⟨P.map (X n), inferInstance⟩
  obtain ⟨v, μ, hv, hlim⟩ :=
    Critical2DKPZ.RandomMeasure.exists_subseq_tendsto_of_tight_probability_laws laws hTight
  refine ⟨v, μ, hv, fun n => hX (v n), measurable_id.aemeasurable, ?_⟩
  have hid : (⟨(μ : Measure (ScalePath S)).map id, inferInstance⟩ :
      ProbabilityMeasure (ScalePath S)) = μ := Subtype.ext (Measure.map_id)
  rw [hid]
  exact hlim

/-- Every subsequential path-law limit has all the Brownian finite-dimensional
marginals, including those containing scale time zero. -/
theorem isWienerLaw_of_subseq_limit
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    {t : ℝ} (ht : 0 < t) (x : Plane) (φ : TestFn)
    (hφ : ∀ y, 0 ≤ φ y) (hφ1 : (∫ y, φ y) = 1) (S : ℝ≥0)
    (u : ℕ → Set.Ioi (0 : ℝ)) (hu : Tendsto (fun n => (u n : ℝ)) atTop atTop)
    (μ : ProbabilityMeasure (ScalePath S))
    (hμ : TendstoInDistribution (fun n ω => scalePath S (H t 0 ω) φ x (u n))
      atTop id (fun _ => P) (μ : Measure (ScalePath S))) : IsWienerLaw S μ := by
  intro I hI
  let ev : ScalePath S → I → ℝ := fun f i =>
    f ⟨(i.1 : ℝ), i.1.property, hI i.1 i.2⟩
  have hev : Continuous ev := continuous_pi (fun i => by fun_prop)
  have hpath := hμ.continuous_comp hev
  have hfdd := kpz_scale_finiteDimensional_tendstoInDistribution ϑ P Z hZ H hH ht x φ hφ hφ1 I
  have hseq : TendstoInDistribution
      (fun n ω (i : I) => scaledPairing (H t 0 ω) φ x (u n) (i.val : ℝ))
      atTop id (fun _ => P) (BrownianReal.projectiveFamily I) :=
    ⟨fun n => hfdd.forall_aemeasurable (u n), hfdd.aemeasurable_limit,
      hfdd.tendsto.comp (tendsto_Ioi_atTop.mpr hu)⟩
  have hseq' : TendstoInDistribution
      (fun n => ev ∘ (fun ω => scalePath S (H t 0 ω) φ x (u n)))
      atTop id (fun _ => P) (BrownianReal.projectiveFamily I) := hseq
  refine ⟨hev.measurable.aemeasurable, ?_⟩
  simpa only [Function.comp_id, Measure.map_id] using
    tendstoInDistribution_unique _ hpath hseq'

end Critical2DKPZ.Extensions.ScaleLimit
