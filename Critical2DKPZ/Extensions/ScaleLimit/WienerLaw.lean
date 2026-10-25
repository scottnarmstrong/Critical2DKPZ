/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.PathMeasurability
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.Tactic

/-! # Uniqueness of the Wiener law on continuous scale paths

Finite Brownian marginals determine all finite dense-coordinate marginals.
Projective uniqueness and a measurable embedding then determine the path law.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped NNReal
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Two Wiener laws have the same law under every finite list of evaluations,
including lists with repeated times. -/
theorem map_eval_eq_of_isWienerLaw {S : ℝ≥0} (μ ν : ProbabilityMeasure (ScalePath S))
    (hμ : IsWienerLaw S μ) (hν : IsWienerLaw S ν)
    {J : Type*} [Fintype J] (d : J → ScaleInterval S) :
    (μ : Measure (ScalePath S)).map (fun f => fun j => f (d j)) =
      (ν : Measure (ScalePath S)).map (fun f => fun j => f (d j)) := by
  classical
  let τ : J → ℝ≥0 := fun j => ⟨d j, (d j).property.1⟩
  let I : Finset ℝ≥0 := Finset.univ.image τ
  have hI : ∀ s ∈ I, (s : ℝ) ≤ S := by
    intro s hs
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hs
    exact (d j).property.2
  let q : (I → ℝ) → J → ℝ := fun g j => g ⟨τ j, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩
  have hq : Measurable q := measurable_pi_iff.mpr (fun j => measurable_pi_apply _)
  have he : Measurable (fun f : ScalePath S => fun i : I =>
      f ⟨(i.1 : ℝ), i.1.property, hI i.1 i.2⟩) :=
    measurable_pi_iff.mpr (fun i => ContinuousMap.measurable_eval _)
  have hh := congrArg (Measure.map q) ((hμ I hI).map_eq.trans (hν I hI).map_eq.symm)
  have hc : (fun f : ScalePath S => q (fun i : I =>
      f ⟨(i.1 : ℝ), i.1.property, hI i.1 i.2⟩)) =
      (fun f => fun j => f (d j)) := by
    funext f j
    congr 1
  simpa only [Measure.map_map hq he, Function.comp_def, hc] using hh

/-- The finite-dimensional Brownian marginals determine at most one Borel probability
law on continuous paths. No positivity assumption on the horizon is needed. -/
theorem eq_of_isWienerLaw {S : ℝ≥0} (μ ν : ProbabilityMeasure (ScalePath S))
    (hμ : IsWienerLaw S μ) (hν : IsWienerLaw S ν) : μ = ν := by
  let inst : Nonempty (ScaleInterval S) := ⟨⟨0, by simp⟩⟩
  let d := denseSeq (ScaleInterval S)
  let e : ScalePath S → ℕ → ℝ := fun f n => f (d n)
  have he := measurableEmbedding_dense_eval d (denseRange_denseSeq _)
  let p : (J : Finset ℕ) → Measure (J → ℝ) := fun J =>
    ((μ : Measure (ScalePath S)).map e).map J.restrict
  have instFinite : ∀ J, IsFiniteMeasure (p J) := fun J =>
    Measure.isFiniteMeasure_map _ _
  have hm : IsProjectiveLimit ((μ : Measure (ScalePath S)).map e) p := fun _ => rfl
  have hn : IsProjectiveLimit ((ν : Measure (ScalePath S)).map e) p := by
    intro J
    dsimp [p]
    have hr : Measurable (J.restrict : (ℕ → ℝ) → J → ℝ) :=
      measurable_pi_iff.mpr (fun j => measurable_pi_apply _)
    rw [Measure.map_map hr he.measurable, Measure.map_map hr he.measurable]
    exact (map_eval_eq_of_isWienerLaw μ ν hμ hν (fun j : J => d j)).symm
  apply ProbabilityMeasure.toMeasure_injective
  exact he.map_injective (hm.unique hn)

end Critical2DKPZ.Extensions.ScaleLimit
