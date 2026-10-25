/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.RandomMeasure.GeneralBorel
public import Mathlib.MeasureTheory.Measure.GiryMonad

/-! On a locally compact second-countable Hausdorff space, a measurable random measure that is locally finite almost surely has a measurable, everywhere locally finite modification with the same almost-sure values. -/

public section

open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal Topology

noncomputable section

set_option linter.style.haveILetI false

namespace Critical2DKPZ.RandomMeasure

/-- Finiteness on a compact exhaustion is equivalent to local finiteness. -/
theorem locallyFinite_iff_finite_compactExhaustion {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (K : CompactExhaustion X) (μ : Measure X) :
    IsLocallyFiniteMeasure μ ↔ ∀ n : ℕ, μ (K n) < ∞ := by
  constructor
  · intro h n
    letI : IsLocallyFiniteMeasure μ := h
    exact (K.isCompact n).measure_lt_top
  · intro h
    refine ⟨fun x => ?_⟩
    obtain ⟨n, hx⟩ := K.exists_mem x
    let U := interior (K (n + 1))
    have hxU : x ∈ U := by
      exact K.subset_interior_succ n hx
    refine ⟨U, isOpen_interior.mem_nhds hxU, ?_⟩
    exact (measure_mono (interior_subset : U ⊆ K (n + 1))).trans_lt (h (n + 1))

/-- The event that a random measure is locally finite. -/
def locallyFiniteEvent {Ω X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (K : CompactExhaustion X) (F : Ω → Measure X) : Set Ω :=
  {ω | ∀ n : ℕ, F ω (K n) < ∞}

/-- The locally-finite event is measurable for an evaluation-measurable random
measure. -/
theorem measurableSet_locallyFiniteEvent {Ω X : Type*}
    [MeasurableSpace Ω] [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (K : CompactExhaustion X) (F : Ω → Measure X)
    (hF : Measurable F) : MeasurableSet (locallyFiniteEvent K F) := by
  rw [locallyFiniteEvent, ofPred_forall]
  apply MeasurableSet.iInter
  intro n
  exact measurableSet_lt
    ((Measure.measurable_coe ((K.isCompact n).isClosed.measurableSet)).comp hF)
    measurable_const

/-- Membership in the compact-exhaustion event is exactly local finiteness of the measure value. -/
theorem mem_locallyFiniteEvent_iff {Ω X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    (K : CompactExhaustion X) (F : Ω → Measure X) (ω : Ω) :
    ω ∈ locallyFiniteEvent K F ↔ IsLocallyFiniteMeasure (F ω) := by
  exact (locallyFinite_iff_finite_compactExhaustion K (F ω)).symm

/-- The local-finiteness predicate of a measurable random measure is a measurable event. -/
theorem measurableSet_isLocallyFiniteMeasure {Ω X : Type*}
    [MeasurableSpace Ω] [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    (K : CompactExhaustion X) (F : Ω → Measure X) (hF : Measurable F) :
    MeasurableSet {ω | IsLocallyFiniteMeasure (F ω)} := by
  have heq : {ω | IsLocallyFiniteMeasure (F ω)} = locallyFiniteEvent K F := by
    ext ω
    exact (mem_locallyFiniteEvent_iff K F ω).symm
  rw [heq]
  exact measurableSet_locallyFiniteEvent K F hF

/-- Replace a measure-valued map by zero wherever its value is not locally finite. -/
@[expose]
noncomputable def locallyFiniteMeasureModification {Ω X : Type*}
    [MeasurableSpace Ω] [TopologicalSpace X] [MeasurableSpace X]
    (K : CompactExhaustion X) (F : Ω → Measure X) : Ω → Measure X := by
  classical
  exact fun ω => if ω ∈ locallyFiniteEvent K F then F ω else 0

/-- The canonical locally finite modification agrees with the input on its locally
finite event and is zero outside that event. -/
@[simp]
theorem locallyFiniteMeasureModification_apply {Ω X : Type*}
    [MeasurableSpace Ω] [TopologicalSpace X] [MeasurableSpace X]
    (K : CompactExhaustion X) (F : Ω → Measure X) (ω : Ω) :
    letI : Decidable (ω ∈ locallyFiniteEvent K F) := Classical.propDecidable _
    locallyFiniteMeasureModification K F ω =
      if ω ∈ locallyFiniteEvent K F then F ω else 0 := rfl

/-- The canonical locally finite modification of a measurable measure map is measurable. -/
theorem measurable_locallyFiniteMeasureModification {Ω X : Type*}
    [MeasurableSpace Ω] [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    (K : CompactExhaustion X) (F : Ω → Measure X) (hF : Measurable F) :
    Measurable (locallyFiniteMeasureModification K F) := by
  classical
  exact Measurable.ite (measurableSet_locallyFiniteEvent K F hF) hF measurable_const

/-- On a locally finite value the canonical modification returns the original measure. -/
theorem locallyFiniteMeasureModification_apply_of_isLocallyFinite {Ω X : Type*}
    [MeasurableSpace Ω] [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    (K : CompactExhaustion X) (F : Ω → Measure X) (ω : Ω)
    (hF : IsLocallyFiniteMeasure (F ω)) :
    locallyFiniteMeasureModification K F ω = F ω := by
  classical
  rw [locallyFiniteMeasureModification_apply,
    ite_eq_left ((mem_locallyFiniteEvent_iff K F ω).2 hF)]

/-- The canonical locally finite modification commutes with precomposition. -/
theorem locallyFiniteMeasureModification_comp {Ω Ω' X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [TopologicalSpace X] [MeasurableSpace X]
    (K : CompactExhaustion X) (F : Ω → Measure X) (g : Ω' → Ω) :
    locallyFiniteMeasureModification K (F ∘ g) = locallyFiniteMeasureModification K F ∘ g := by
  funext ω
  simp only [locallyFiniteMeasureModification, locallyFiniteEvent, Function.comp_apply,
    Set.mem_ofPred_eq]
  rfl

/-- Every value of the modified measure map is locally finite. -/
theorem locallyFinite_locallyFiniteMeasureModification {Ω X : Type*}
    [MeasurableSpace Ω] [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [BorelSpace X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X]
    (K : CompactExhaustion X) (F : Ω → Measure X) (ω : Ω) :
    IsLocallyFiniteMeasure (locallyFiniteMeasureModification K F ω) := by
  classical
  by_cases hω : ω ∈ locallyFiniteEvent K F
  · have hfin : ∀ n : ℕ, F ω (K n) < ∞ := by
      simpa [locallyFiniteEvent] using hω
    have hloc : IsLocallyFiniteMeasure (F ω) :=
      (locallyFinite_iff_finite_compactExhaustion K (F ω)).2 hfin
    simpa [locallyFiniteMeasureModification, hω] using hloc
  · simpa [locallyFiniteMeasureModification, hω] using
      (inferInstance : IsLocallyFiniteMeasure (0 : Measure X))

/-- A measurable random measure induces a measurable map into positive Radon
measures by replacing its non-locally-finite values with zero. -/
@[expose]
noncomputable def radonValuedModification {Ω X : Type*}
    [MeasurableSpace Ω] [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [BorelSpace X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X]
    (K : CompactExhaustion X) (F : Ω → Measure X) (ω : Ω) :
    PositiveRadonMeasure X :=
  ⟨locallyFiniteMeasureModification K F ω,
    locallyFinite_locallyFiniteMeasureModification K F ω⟩

/-- Measurability of the Radon-valued modification in the vague Borel
structure. -/
theorem measurable_radonValuedModification {Ω X : Type*}
    [MeasurableSpace Ω] [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [BorelSpace X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X]
    (K : CompactExhaustion X) (F : Ω → Measure X) (hF : Measurable F) :
    @Measurable Ω (PositiveRadonMeasure X) inferInstance
      (@borel (PositiveRadonMeasure X) (vagueTopology X))
      (radonValuedModification K F) := by
  classical
  have hgood : MeasurableSet (locallyFiniteEvent K F) :=
    measurableSet_locallyFiniteEvent K F hF
  have hraw : Measurable (locallyFiniteMeasureModification K F) := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    have hEq : (fun b => (locallyFiniteMeasureModification K F b) A) =
        fun b => if b ∈ locallyFiniteEvent K F then F b A else 0 := by
      funext b
      by_cases hb : b ∈ locallyFiniteEvent K F <;>
        simp [locallyFiniteMeasureModification, hb]
    rw [hEq]
    exact Measurable.ite hgood ((Measure.measurable_coe hA).comp hF) measurable_const
  have hval : Measurable (radonValuedModification K F) := hraw.subtype_mk
    (h := locallyFinite_locallyFiniteMeasureModification K F)
  rw [← eval_eq_vague_borel]
  exact hval

/-- If the original random measure is locally finite almost surely, the
Radon-valued modification agrees with it almost surely. -/
theorem ae_eq_radonValuedModification {Ω X : Type*}
    [MeasurableSpace Ω] [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [BorelSpace X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X]
    (K : CompactExhaustion X) (P : Measure Ω) (F : Ω → Measure X)
    (hLF : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (F ω)) :
    (fun ω => (radonValuedModification K F ω : Measure X)) =ᵐ[P] F := by
  have hgood : ∀ᵐ ω ∂P, ω ∈ locallyFiniteEvent K F := by
    filter_upwards [hLF] with ω hω
    change ∀ n : ℕ, F ω (K n) < ∞
    exact (locallyFinite_iff_finite_compactExhaustion K (F ω)).mp hω
  filter_upwards [hgood] with ω hω
  change locallyFiniteMeasureModification K F ω = F ω
  simp [locallyFiniteMeasureModification, hω]

/-- An a.e. measurable, a.s. locally finite random measure has a measurable, everywhere locally finite modification. -/
theorem exists_measurable_locallyFinite_modification {Ω X : Type*}
    [MeasurableSpace Ω] [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [BorelSpace X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X]
    (K : CompactExhaustion X) (P : Measure Ω) (F : Ω → Measure X)
    (hF : AEMeasurable F P) (hLF : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (F ω)) :
    ∃ G : Ω → Measure X, Measurable G ∧ (∀ ω, IsLocallyFiniteMeasure (G ω)) ∧ G =ᵐ[P] F := by
  let F₀ := hF.mk F
  have hF₀ : Measurable F₀ := hF.measurable_mk
  have heq : F₀ =ᵐ[P] F := hF.ae_eq_mk.symm
  have hLF₀ : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (F₀ ω) := by
    filter_upwards [hLF, heq] with ω hω hωeq
    rw [hωeq]
    exact hω
  refine ⟨locallyFiniteMeasureModification K F₀, ?_,
    locallyFinite_locallyFiniteMeasureModification K F₀, ?_⟩
  · exact measurable_locallyFiniteMeasureModification K F₀ hF₀
  · exact (ae_eq_radonValuedModification K P F₀ hLF₀).trans heq

end Critical2DKPZ.RandomMeasure

end
