/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.MixedBlockJointMoments
public import Critical2DKPZ.SHF.Tsai.IndependentBlockTuples

/-! # Independent endpoint tuple means with one partial heat replacement

A blockwise measurable transformation preserves independence. At the selected
time block its endpoint tuple mean is the mixed moment kernel; all other
blocks keep their full moment kernels. Finite form bounds justify the joint
product-measure identity.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- The mixed endpoint tuple map after canonical local-finiteness modification is measurable. -/
theorem measurable_modified_endpointTupleMeasure_ite_heat (n : ℕ) (S : Finset (Fin n))
    (τ : ℝ) (E : CompactExhaustion (Plane × Plane)) :
    Measurable (fun μ : Measure (Plane × Plane) => endpointTupleMeasure
      (fun i => if i ∈ S then RandomMeasure.locallyFiniteMeasureModification E id μ else heatBlock τ)) := by
  classical
  let F := RandomMeasure.locallyFiniteMeasureModification E
    (id : Measure (Plane × Plane) → Measure (Plane × Plane))
  have hF : Measurable F := RandomMeasure.measurable_locallyFiniteMeasureModification E id measurable_id
  apply measurable_endpointTupleMeasure
  · intro i
    by_cases hi : i ∈ S
    · simpa only [ite_eq_left hi] using hF
    · simp only [ite_eq_right hi]
      exact measurable_const
  · intro i μ
    split_ifs
    · exact RandomMeasure.locallyFinite_locallyFiniteMeasureModification E id μ
    · exact locallyFinite_heatBlock τ

/-- Independence factors the full endpoint tuple mean with one selected partial heat replacement. -/
theorem bind_pi_endpointTupleModification_update_heat_eq {θ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (m : ℕ) (j : Fin m)
    {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 4) (S : Finset (Fin n))
    (τ : Fin m → ℝ) (hτ : ∀ k, 0 < τ k)
    (B : Fin m → Ω → Measure (Plane × Plane))
    (hB : ∀ k, HasDeltaBoseMoments θ (τ k) P (B k)) (hind : iIndepFun B P)
    (E : CompactExhaustion (Plane × Plane)) :
    P.bind (fun ω => Measure.pi (fun k : Fin m => endpointTupleMeasure (fun i : Fin n =>
      if k = j then
        (if i ∈ S then RandomMeasure.locallyFiniteMeasureModification E (B k) ω else heatBlock (τ k))
      else RandomMeasure.locallyFiniteMeasureModification E (B k) ω))) =
      Measure.pi (fun k => volume.withDensity (Function.uncurry
        (Function.update (fun k => momentKernel n θ (τ k)) j (mixedBlockKernel n θ (τ j) S) k))) := by
  classical
  let B' k := RandomMeasure.locallyFiniteMeasureModification E (B k)
  have hB' (k) : HasDeltaBoseMoments θ (τ k) P (B' k) :=
    (hB k).locallyFiniteMeasureModification E
  have hlf (k) (ω) : IsLocallyFiniteMeasure (B' k ω) :=
    RandomMeasure.locallyFinite_locallyFiniteMeasureModification E (B k) ω
  let C (k : Fin m) (i : Fin n) (ω : Ω) :=
    if k = j then (if i ∈ S then B' k ω else heatBlock (τ k)) else B' k ω
  have hCm (k i) : Measurable (C k i) := by
    dsimp only [C]
    split_ifs
    · exact (hB' k).1
    · exact measurable_const
    · exact (hB' k).1
  have hClf (k i ω) : IsLocallyFiniteMeasure (C k i ω) := by
    dsimp only [C]
    split_ifs
    · exact hlf k ω
    · exact locallyFinite_heatBlock (τ k)
    · exact hlf k ω
  let κ (k : Fin m) : Kernel Ω (Configuration n × Configuration n) :=
    ⟨fun ω => endpointTupleMeasure (C k · ω), measurable_endpointTupleMeasure (C k) (hCm k) (hClf k)⟩
  have hκ (k) : IsSFiniteKernel (κ k) :=
    isSFiniteKernel_endpointTupleMeasureKernel n (C k) (hCm k) (hClf k)
  have hsf (k ω) : SigmaFinite (κ k ω) := by
    have hCi (i) : SigmaFinite (C k i ω) := by
      let : IsLocallyFiniteMeasure (C k i ω) := hClf k i ω
      infer_instance
    let : ∀ i, SigmaFinite (C k i ω) := hCi
    exact (MeasurableEquiv.arrowProdEquivProdArrow Plane Plane (Fin n)).sigmaFinite_map
  let F (k : Fin m) (μ : Measure (Plane × Plane)) :=
    if k = j then endpointTupleMeasure (fun i : Fin n =>
      if i ∈ S then RandomMeasure.locallyFiniteMeasureModification E id μ else heatBlock (τ k))
    else blockTupleMeasure n (RandomMeasure.locallyFiniteMeasureModification E id μ)
  have hFm (k) : Measurable (F k) := by
    dsimp only [F]
    split_ifs
    · exact measurable_modified_endpointTupleMeasure_ite_heat n S (τ k) E
    · exact measurable_modified_blockTupleMeasure n E
  have hpoint (k : Fin m) (ω : Ω) : F k (B k ω) = κ k ω := by
    have hmod := congrFun (RandomMeasure.locallyFiniteMeasureModification_comp E id (B k)) ω
    dsimp only [Function.comp_def, id_eq] at hmod
    dsimp only [F, κ, C, B']
    split_ifs with hk
    · congr 1
      funext i
      split_ifs
      · exact hmod.symm
      · rfl
    · exact congrArg (blockTupleMeasure n) hmod.symm
  have hind' : iIndepFun (fun k ω => κ k ω) P :=
    (hind.comp F hFm).congr (fun k => Filter.Eventually.of_forall (hpoint k))
  let Lb (k : Fin m) :=
    Function.update (fun k => momentKernel n θ (τ k)) j (mixedBlockKernel n θ (τ j) S) k
  have hLj : Lb j = mixedBlockKernel n θ (τ j) S := Function.update_self _ _ _
  have hmean (k) : P.bind (fun ω => κ k ω) = volume.withDensity (Function.uncurry (Lb k)) := by
    by_cases hk : k = j
    · subst k
      change P.bind (fun ω => endpointTupleMeasure (C j · ω)) = _
      have hC : C j = fun i ω => if i ∈ S then B' j ω else heatBlock (τ j) := by
        funext i ω
        exact ite_eq_left rfl
      rw [hC, hLj]
      exact (hB' j).bind_endpointTupleMeasure_ite_heat_eq_of_locallyFinite (hτ j) (hlf j) hn S
    · have hC : C k = fun _ ω => B' k ω := by
        funext i ω
        exact ite_eq_right hk
      change P.bind (fun ω => endpointTupleMeasure (C k · ω)) = _
      rw [hC]
      have hL : Lb k = momentKernel n θ (τ k) := Function.update_of_ne hk _ _
      rw [hL]
      exact (hB' k).bind_blockTupleMeasure_eq_of_locallyFinite (hτ k) (hlf k) hn1 hn
  have hmeansf (k) : SigmaFinite (P.bind (fun ω => κ k ω)) := by
    rw [hmean k]
    by_cases hk : k = j
    · subst k
      rw [hLj]
      change SigmaFinite (volume.withDensity (Function.uncurry (mixedBlockKernel n θ (τ j) S)))
      obtain ⟨c, hc, hF⟩ := exists_formBound_mixedBlockKernel n S θ (hτ j)
      let : IsLocallyFiniteMeasure
          (volume.withDensity (Function.uncurry (mixedBlockKernel n θ (τ j) S))) :=
        locallyFinite_kernelMeasure (measurable_mixedBlockKernel n θ (τ j) S) hc hF
      infer_instance
    · have hL : Lb k = momentKernel n θ (τ k) := Function.update_of_ne hk _ _
      rw [hL]
      have hm : Measurable (Function.uncurry (momentKernel n θ (τ k))) :=
        Measurable.comp
          (g := fun p : (ℝ × ℝ) × Configuration n × Configuration n =>
            momentKernel n p.1.1 p.1.2 p.2.1 p.2.2)
          (f := fun q : Configuration n × Configuration n => ((θ, τ k), q))
          (measurable_momentKernel n) (measurable_const.prodMk measurable_id)
      obtain ⟨c, rate, _, hF⟩ := exists_formBound_momentKernel n θ
      let : IsLocallyFiniteMeasure (volume.withDensity (Function.uncurry (momentKernel n θ (τ k)))) :=
        locallyFinite_kernelMeasure hm ENNReal.ofReal_ne_top (hF θ le_rfl (τ k) (hτ k))
      infer_instance
  exact (bind_piMeasure_eq_pi_bind_of_iIndepFun P m κ hκ hsf hind' hmeansf).trans
    (congrArg Measure.pi (funext hmean))

end Critical2DKPZ.SHF.Tsai

end
