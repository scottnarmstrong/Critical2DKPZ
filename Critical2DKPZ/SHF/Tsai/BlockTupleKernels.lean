/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.BlockTupleMeasures
public import Critical2DKPZ.SHF.Tsai.BlockModification

/-! # S-finite kernels and independence of modified endpoint tuples

The finite-product kernel construction supplies s-finiteness of actual tuple
measures. Applying the canonical locally finite modification on the measure
carrier gives a globally measurable map, so independence is preserved.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace Critical2DKPZ.SHF.Tsai

/-- Canonical grouping of coordinates preserves sigma-finiteness of a block product. -/
theorem sigmaFinite_blockTupleMeasure (n : ℕ) (μ : Measure (Plane × Plane)) [SigmaFinite μ] :
    SigmaFinite (blockTupleMeasure n μ) :=
  (MeasurableEquiv.arrowProdEquivProdArrow Plane Plane (Fin n)).sigmaFinite_map

/-- Endpoint tuples of an everywhere locally finite family form an s-finite kernel. -/
theorem isSFiniteKernel_endpointTupleMeasureKernel {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : Fin n → Ω → Measure (Plane × Plane)) (hB : ∀ i, Measurable (B i))
    (hlf : ∀ i ω, IsLocallyFiniteMeasure (B i ω)) :
    IsSFiniteKernel (⟨fun ω => endpointTupleMeasure (fun i => B i ω),
      measurable_endpointTupleMeasure B hB hlf⟩ : Kernel Ω (Critical2DKPZ.DeltaBose.Configuration n ×
        Critical2DKPZ.DeltaBose.Configuration n)) := by
  let κ (i : Fin n) : Kernel Ω (Plane × Plane) := ⟨B i, hB i⟩
  have hκ (i) : IsSFiniteKernel (κ i) := isSFiniteKernel_of_locallyFinite (κ i) (hlf i)
  have hsf (i) (ω) : SigmaFinite (κ i ω) := by
    let : IsLocallyFiniteMeasure (B i ω) := hlf i ω
    change SigmaFinite (B i ω)
    infer_instance
  obtain ⟨η, hη, hηeq⟩ := exists_piMeasureKernel n κ hκ hsf
  let : IsSFiniteKernel η := hη
  let e := MeasurableEquiv.arrowProdEquivProdArrow Plane Plane (Fin n)
  have heq : (⟨fun ω => endpointTupleMeasure (fun i => B i ω), measurable_endpointTupleMeasure B hB hlf⟩ :
      Kernel Ω (Critical2DKPZ.DeltaBose.Configuration n × Critical2DKPZ.DeltaBose.Configuration n)) =
      η.map e := by
    ext ω s hs
    rw [Kernel.map_apply η e.measurable, hηeq ω]
    rfl
  rw [heq]
  infer_instance

/-- The measurable actual tuple map of everywhere locally finite blocks is an s-finite kernel. -/
theorem isSFiniteKernel_blockTupleMeasureKernel {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : Ω → Measure (Plane × Plane)) (hB : Measurable B)
    (hlf : ∀ ω, IsLocallyFiniteMeasure (B ω)) :
    IsSFiniteKernel (⟨fun ω => blockTupleMeasure n (B ω),
      measurable_blockTupleMeasure n B hB hlf⟩ : Kernel Ω (Critical2DKPZ.DeltaBose.Configuration n ×
        Critical2DKPZ.DeltaBose.Configuration n)) :=
  isSFiniteKernel_endpointTupleMeasureKernel n (fun _ => B) (fun _ => hB) (fun _ => hlf)

/-- Products of endpoint tuples of locally finite particle-dependent blocks are measurable. -/
theorem measurable_pi_endpointTupleMeasure {Ω : Type*} [MeasurableSpace Ω]
    (m n : ℕ) (B : Fin m → Fin n → Ω → Measure (Plane × Plane))
    (hB : ∀ k i, Measurable (B k i)) (hlf : ∀ k i ω, IsLocallyFiniteMeasure (B k i ω)) :
    Measurable (fun ω => Measure.pi (fun k => endpointTupleMeasure (B k · ω))) := by
  let κ (k : Fin m) : Kernel Ω (Critical2DKPZ.DeltaBose.Configuration n ×
      Critical2DKPZ.DeltaBose.Configuration n) :=
    ⟨fun ω => endpointTupleMeasure (B k · ω), measurable_endpointTupleMeasure (B k) (hB k) (hlf k)⟩
  have hκ (k) : IsSFiniteKernel (κ k) :=
    isSFiniteKernel_endpointTupleMeasureKernel n (B k) (hB k) (hlf k)
  have hsf (k) (ω) : SigmaFinite (κ k ω) := by
    have hsfi (i) : SigmaFinite (B k i ω) := by
      let : IsLocallyFiniteMeasure (B k i ω) := hlf k i ω
      infer_instance
    let : ∀ i, SigmaFinite (B k i ω) := hsfi
    exact (MeasurableEquiv.arrowProdEquivProdArrow Plane Plane (Fin n)).sigmaFinite_map
  exact measurable_piMeasure_of_kernels m κ hκ hsf

/-- Finite products of actual tuple measures of locally finite blocks are measurable. -/
theorem measurable_pi_blockTupleMeasure {Ω : Type*} [MeasurableSpace Ω]
    (m n : ℕ) (B : Fin m → Ω → Measure (Plane × Plane)) (hB : ∀ k, Measurable (B k))
    (hlf : ∀ k ω, IsLocallyFiniteMeasure (B k ω)) :
    Measurable (fun ω => Measure.pi (fun k => blockTupleMeasure n (B k ω))) :=
  measurable_pi_endpointTupleMeasure m n (fun k _ => B k) (fun k _ => hB k) (fun k _ => hlf k)

/-- Modifying a measure on its own carrier, then taking its tuples, is globally measurable. -/
theorem measurable_modified_blockTupleMeasure (n : ℕ) (E : CompactExhaustion (Plane × Plane)) :
    Measurable (fun μ : Measure (Plane × Plane) =>
      blockTupleMeasure n (RandomMeasure.locallyFiniteMeasureModification E id μ)) := by
  have hm : Measurable (RandomMeasure.locallyFiniteMeasureModification E
      (id : Measure (Plane × Plane) → Measure (Plane × Plane))) := by
    classical
    exact Measurable.ite (RandomMeasure.measurableSet_locallyFiniteEvent E id measurable_id)
      measurable_id measurable_const
  exact measurable_blockTupleMeasure n _ hm
    (RandomMeasure.locallyFinite_locallyFiniteMeasureModification E id)

/-- Independent blocks retain independence after the canonical modification and endpoint grouping. -/
theorem iIndepFun_modified_blockTupleMeasure {Ω ι : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (n : ℕ) (E : CompactExhaustion (Plane × Plane))
    {B : ι → Ω → Measure (Plane × Plane)} (hind : iIndepFun B P) :
    iIndepFun (fun i ω => blockTupleMeasure n
      (RandomMeasure.locallyFiniteMeasureModification E (B i) ω)) P := by
  have h := hind.comp
    (fun _ μ => blockTupleMeasure n (RandomMeasure.locallyFiniteMeasureModification E id μ))
    (fun _ => measurable_modified_blockTupleMeasure n E)
  convert h using 1
  funext i ω
  exact congrArg (blockTupleMeasure n)
    (congrFun (RandomMeasure.locallyFiniteMeasureModification_comp E id (B i)) ω)

end Critical2DKPZ.SHF.Tsai

end
