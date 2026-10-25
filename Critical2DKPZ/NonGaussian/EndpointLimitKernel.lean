/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.EndpointLimitMeasures
public import Critical2DKPZ.RandomMeasure.GeneralRandom
public import Critical2DKPZ.SHF.Tsai.MeasureKernels
public import Mathlib.Probability.Kernel.WithDensity
public import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Tactic

/-! # Measurable kernels for normalized endpoint measures -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Critical2DKPZ.NonGaussian

/-- The measurable normalized endpoint kernel obtained from a locally finite version
of the random measure. -/
def endpointMeasureKernel {Ω : Type*} [MeasurableSpace Ω]
    (μ : Ω → Measure (Plane × Plane)) (hμ : Measurable μ)
    (r : ℝ) (hr : 0 < r) : Kernel (Plane × Ω) Plane := by
  let E : CompactExhaustion (Plane × Plane) := RandomMeasure.vagueCompactExhaustion _
  let M := RandomMeasure.locallyFiniteMeasureModification E μ
  have hM : Measurable M := RandomMeasure.measurable_locallyFiniteMeasureModification E μ hμ
  let κ : Kernel (Plane × Ω) (Plane × Plane) := ⟨fun q => M q.2, hM.comp measurable_snd⟩
  letI : IsSFiniteKernel κ := SHF.Tsai.isSFiniteKernel_of_locallyFinite κ
    (fun q => RandomMeasure.locallyFinite_locallyFiniteMeasureModification E μ q.2)
  let f : (Plane × Ω) → (Plane × Plane) → ℝ≥0∞ :=
    fun q p => ENNReal.ofReal (heatKernel r (p.1 - q.1))
  have hf : Measurable (Function.uncurry f) :=
    ((measurable_heatKernel r).comp (measurable_snd.fst.sub measurable_fst.fst)).ennreal_ofReal
  let κh := κ.withDensity f
  have hκh (q : Plane × Ω) : κh q =
      (M q.2).withDensity (fun p => ENNReal.ofReal (heatKernel r (p.1 - q.1))) :=
    Kernel.withDensity_apply κ hf q
  let d : Plane × Ω → ℝ := fun q => ∫ p, heatKernel r (p.1 - q.1) ∂M q.2
  have hdEq : d = fun q => (κh q Set.univ).toReal := by
    funext q
    rw [hκh, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
    apply integral_eq_lintegral_of_nonneg_ae
    · exact Filter.Eventually.of_forall fun p => heatKernel_nonneg hr.le _
    · exact ((measurable_heatKernel r).comp
        (measurable_fst.sub_const q.1)).aestronglyMeasurable
  have hd : Measurable d := by
    rw [hdEq]
    exact (κh.measurable_coe MeasurableSet.univ).ennreal_toReal
  refine ⟨fun q => endpointTerminalMeasure (M q.2) r q.1, ?_⟩
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have heq : (fun q : Plane × Ω => endpointTerminalMeasure (M q.2) r q.1 s) =
      fun q => ENNReal.ofReal ((d q)⁻¹) * (κh.map Prod.snd) q s := by
    funext q
    rw [Kernel.map_apply κh measurable_snd q, hκh]
    rfl
  rw [heq]
  exact hd.inv.ennreal_ofReal.mul ((κh.map Prod.snd).measurable_coe hs)

/-- On locally finite samples, the measurable endpoint kernel equals the normalized endpoint measure. -/
theorem endpointMeasureKernel_apply_of_isLocallyFinite {Ω : Type*} [MeasurableSpace Ω]
    (μ : Ω → Measure (Plane × Plane)) (hμ : Measurable μ)
    (r : ℝ) (hr : 0 < r) (x : Plane) (ω : Ω)
    (hω : IsLocallyFiniteMeasure (μ ω)) :
    endpointMeasureKernel μ hμ r hr (x, ω) = endpointTerminalMeasure (μ ω) r x := by
  change endpointTerminalMeasure
    (RandomMeasure.locallyFiniteMeasureModification
      (RandomMeasure.vagueCompactExhaustion (Plane × Plane)) μ ω) r x = _
  rw [RandomMeasure.locallyFiniteMeasureModification_apply_of_isLocallyFinite _ μ ω hω]

/-- Each normalized endpoint kernel has total mass at most one. -/
theorem endpointMeasureKernel_mass_le_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Ω → Measure (Plane × Plane)) (hμ : Measurable μ)
    (r : ℝ) (hr : 0 < r) (q : Plane × Ω) :
    endpointMeasureKernel μ hμ r hr q Set.univ ≤ 1 :=
  endpointTerminalMeasure_mass_le_one _ hr _

instance endpointMeasureKernel_isFiniteKernel {Ω : Type*} [MeasurableSpace Ω]
    (μ : Ω → Measure (Plane × Plane)) (hμ : Measurable μ)
    (r : ℝ) (hr : 0 < r) : IsFiniteKernel (endpointMeasureKernel μ hμ r hr) :=
  ⟨⟨1, ENNReal.one_lt_top, endpointMeasureKernel_mass_le_one μ hμ r hr⟩⟩

end Critical2DKPZ.NonGaussian
