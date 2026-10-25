/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.BlockTupleKernels
public import Critical2DKPZ.SHF.Tsai.BlockJointMoments
public import Critical2DKPZ.SHF.Tsai.KernelMeasureLocalFiniteness
public import Critical2DKPZ.SHF.Tsai.IndependentMeasureProducts

/-! # The joint moment measure of independent blocks

The canonical modifications preserve independence and each block moment law.
Their expected endpoint tuple measures are the locally finite moment-kernel
measures. The finite-product expectation identity thus applies to all joint
path tests at once.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- The joint tuple moment measure of independent modified blocks is the product of moment-kernel measures. -/
theorem bind_pi_blockTupleModification_eq {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (m : ℕ) {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 4)
    (τ : Fin m → ℝ) (hτ : ∀ k, 0 < τ k)
    (B : Fin m → Ω → Measure (Plane × Plane))
    (hB : ∀ k, HasDeltaBoseMoments θ (τ k) P (B k)) (hind : iIndepFun B P)
    (E : CompactExhaustion (Plane × Plane)) :
    P.bind (fun ω => Measure.pi (fun k => blockTupleMeasure n
      (RandomMeasure.locallyFiniteMeasureModification E (B k) ω))) =
      Measure.pi (fun k => volume.withDensity (Function.uncurry (momentKernel n θ (τ k)))) := by
  let B' k := RandomMeasure.locallyFiniteMeasureModification E (B k)
  have hB' (k) : HasDeltaBoseMoments θ (τ k) P (B' k) := (hB k).locallyFiniteMeasureModification E
  have hlf (k) (ω) : IsLocallyFiniteMeasure (B' k ω) :=
    RandomMeasure.locallyFinite_locallyFiniteMeasureModification E (B k) ω
  let κ (k : Fin m) : Kernel Ω (Configuration n × Configuration n) :=
    ⟨fun ω => blockTupleMeasure n (B' k ω), measurable_blockTupleMeasure n (B' k) (hB' k).1 (hlf k)⟩
  have hκ (k) : IsSFiniteKernel (κ k) :=
    isSFiniteKernel_blockTupleMeasureKernel n (B' k) (hB' k).1 (hlf k)
  have hsf (k) (ω) : SigmaFinite (κ k ω) := by
    let : IsLocallyFiniteMeasure (B' k ω) := hlf k ω
    exact sigmaFinite_blockTupleMeasure n (B' k ω)
  have hind' : iIndepFun (fun k ω => κ k ω) P := iIndepFun_modified_blockTupleMeasure n E hind
  have hmean (k) : P.bind (fun ω => κ k ω) =
      volume.withDensity (Function.uncurry (momentKernel n θ (τ k))) :=
    (hB' k).bind_blockTupleMeasure_eq_of_locallyFinite (hτ k) (hlf k) hn1 hn
  have hmeansf (k) : SigmaFinite (P.bind (fun ω => κ k ω)) := by
    rw [hmean k]
    have hKm : Measurable (Function.uncurry (momentKernel n θ (τ k))) :=
      Measurable.comp
        (g := fun p : (ℝ × ℝ) × Configuration n × Configuration n =>
          momentKernel n p.1.1 p.1.2 p.2.1 p.2.2)
        (f := fun q : Configuration n × Configuration n => ((θ, τ k), q))
        (measurable_momentKernel n) (measurable_const.prodMk measurable_id)
    obtain ⟨C, rate, _, hC⟩ := exists_formBound_momentKernel n θ
    let : IsLocallyFiniteMeasure (volume.withDensity (Function.uncurry (momentKernel n θ (τ k)))) :=
      locallyFinite_kernelMeasure hKm ENNReal.ofReal_ne_top (hC θ le_rfl (τ k) (hτ k))
    infer_instance
  calc
    _ = Measure.pi (fun k => P.bind (fun ω => κ k ω)) :=
      bind_piMeasure_eq_pi_bind_of_iIndepFun P m κ hκ hsf hind' hmeansf
    _ = _ := congrArg Measure.pi (funext hmean)

end Critical2DKPZ.SHF.Tsai

end
