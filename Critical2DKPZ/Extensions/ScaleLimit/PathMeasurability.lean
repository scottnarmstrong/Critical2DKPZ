/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.PathApi
public import Critical2DKPZ.Definitions.IsCriticalSHF
public import Critical2DKPZ.Definitions.IsCriticalKPZ
import Critical2DKPZ.SmallScales.PointMatchedComparison
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-! # Measurability of continuous scale paths

Dense evaluations determine the Borel structure on a compact continuous-map space.
The scale path is the literal path at every sample, with no null-set modification.
-/

@[expose] public section
noncomputable section
open MeasureTheory TopologicalSpace
open scoped BoundedContinuousFunction NNReal
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Evaluation on a dense sequence is a measurable embedding of real continuous paths. -/
theorem measurableEmbedding_dense_eval {K : Type*} [MetricSpace K] [CompactSpace K]
    [SecondCountableTopology K] (d : ℕ → K) (hd : DenseRange d) :
    MeasurableEmbedding (fun f : C(K, ℝ) => fun n => f (d n)) := by
  have hm : Measurable (fun f : C(K, ℝ) => fun n => f (d n)) :=
    measurable_pi_iff.mpr (fun n => ContinuousMap.measurable_eval (d n))
  apply hm.measurableEmbedding
  intro f g hfg
  apply ContinuousMap.coe_injective
  exact hd.equalizer f.continuous g.continuous hfg

/-- Coordinatewise almost everywhere measurability suffices for compact continuous paths. -/
theorem aemeasurable_of_continuous_coords {Ω K : Type*} [MeasurableSpace Ω]
    [MetricSpace K] [CompactSpace K] [SecondCountableTopology K] [Nonempty K]
    (P : Measure Ω) (F : Ω → C(K, ℝ))
    (hF : ∀ s, AEMeasurable (fun ω => F ω s) P) : AEMeasurable F P := by
  apply (measurableEmbedding_dense_eval (denseSeq K) (denseRange_denseSeq K)).aemeasurable_comp_iff.mp
  exact aemeasurable_pi_iff.mpr (fun n => hF (denseSeq K n))

/-- The literal scale path of any flat critical KPZ realization is almost everywhere measurable. -/
theorem aemeasurable_scalePath (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    {t : ℝ} (ht : 0 < t) (x : Plane) (φ : TestFn) (S : ℝ≥0)
    (L : Set.Ioi (0 : ℝ)) :
    AEMeasurable (fun ω => scalePath S (H t 0 ω) φ x L) P := by
  let inst : Nonempty (ScaleInterval S) := ⟨⟨0, by simp⟩⟩
  apply aemeasurable_of_continuous_coords
  intro s
  exact (SmallScales.aemeasurable_isCriticalKPZ_of ϑ P Z hZ ht H hH
    (φ.dilate (scaleRadius L s) x)).div_const _

end Critical2DKPZ.Extensions.ScaleLimit
