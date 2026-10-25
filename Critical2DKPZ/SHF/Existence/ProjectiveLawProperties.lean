/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Existence.ProjectiveMeasureSupport

/-! # Support properties of finite Radon laws -/

@[expose] public section

set_option linter.style.haveILetI false

open MeasureTheory
open scoped ENNReal
open Critical2DKPZ.SHF.Limit

noncomputable section

namespace Critical2DKPZ.SHF.Existence

private def locallyFiniteFirstMarginalSet {J : Finset SHFTimePair} :
    Set (J → SHFPairRadonMeasure) := {q | ∀ j, IsLocallyFiniteMeasure
      (Measure.map Prod.fst (q j : Measure (Plane × Plane)))}

private theorem measurableSet_locallyFiniteFirstMarginalSet {J : Finset SHFTimePair} :
    MeasurableSet (locallyFiniteFirstMarginalSet (J := J)) := by
  rw [locallyFiniteFirstMarginalSet]
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  have hcoe : Measurable (fun q : J → SHFPairRadonMeasure => (q j : Measure (Plane × Plane))) :=
    measurable_subtype_coe.comp (measurable_pi_apply j)
  have hmap := (Measure.measurable_map Prod.fst measurable_fst).comp hcoe
  exact (Critical2DKPZ.RandomMeasure.measurableSet_isLocallyFiniteMeasure
      (Critical2DKPZ.RandomMeasure.vagueCompactExhaustion Plane)
      (fun μ => μ) measurable_id).preimage hmap

private theorem measurable_finite_limit_radon_vector (ϑ : ℝ) (J : Finset SHFTimePair)
    (d : FiniteSHFSubsequenceLimit ϑ J) :
    @Measurable d.Ω (J → SHFPairRadonMeasure) d.mΩ inferInstance
      (fun (ω : d.Ω) (j : J) =>
        pairMeasureRadonModification (d.Z (projectiveSHFPairStart j) (projectiveSHFPairEnd j) ω)) := by
  letI : MeasurableSpace d.Ω := d.mΩ
  letI : IsProbabilityMeasure d.P := d.hP
  apply measurable_pi_iff.mpr
  intro j
  exact measurable_pairMeasureRadonModification.comp
    ((d.hZ.1 (projectiveSHFPairStart j) (d.htimes j).1
      (projectiveSHFPairEnd j) (d.htimes j).2 ((j : SHFTimePair).property.2)).1)

/-- Radonification leaves a locally finite measure unchanged. -/
theorem pairMeasureRadonModification_eq_of_locallyFinite (μ : Measure (Plane × Plane))
    (hμ : IsLocallyFiniteMeasure μ) :
    (pairMeasureRadonModification μ : Measure (Plane × Plane)) = μ := by
  let K := Critical2DKPZ.RandomMeasure.vagueCompactExhaustion (Plane × Plane)
  change Critical2DKPZ.RandomMeasure.locallyFiniteMeasureModification K id μ = μ
  exact Critical2DKPZ.RandomMeasure.locallyFiniteMeasureModification_apply_of_isLocallyFinite
    K id μ hμ

/-- Every chosen finite Radon law almost surely has locally finite flat
marginals in all its coordinates. -/
theorem finiteSHFRadonLawOfSubsequenceLimit_flatMarginal_ae (ϑ : ℝ) (J : Finset SHFTimePair)
    (d : FiniteSHFSubsequenceLimit ϑ J) :
    ∀ᵐ q ∂(finiteSHFRadonLawOfSubsequenceLimit ϑ J d : Measure (J → SHFPairRadonMeasure)),
      ∀ j, IsLocallyFiniteMeasure
        (Measure.map Prod.fst (q j : Measure (Plane × Plane))) := by
  classical
  letI : MeasurableSpace d.Ω := d.mΩ
  letI : IsProbabilityMeasure d.P := d.hP
  let F : d.Ω → J → SHFPairRadonMeasure := fun ω j =>
    pairMeasureRadonModification (d.Z (projectiveSHFPairStart j) (projectiveSHFPairEnd j) ω)
  have hF : Measurable F := measurable_finite_limit_radon_vector ϑ J d
  have hsourceCoord : ∀ j : J, ∀ᵐ ω ∂d.P,
      IsLocallyFiniteMeasure
        (Measure.map Prod.fst (F ω j : Measure (Plane × Plane))) := by
    intro j
    have hlocal := (d.hZ.1 (projectiveSHFPairStart j) (d.htimes j).1
      (projectiveSHFPairEnd j) (d.htimes j).2 ((j : SHFTimePair).property.2)).2
    filter_upwards [hlocal] with ω hω
    rw [pairMeasureRadonModification_eq_of_locallyFinite _ hω.1]
    exact hω.2
  have hsource : ∀ᵐ ω ∂d.P, F ω ∈ locallyFiniteFirstMarginalSet (J := J) := by
    filter_upwards [ae_all_iff.mpr hsourceCoord] with ω hω
    exact hω
  have hmap := (MeasureTheory.ae_map_iff hF.aemeasurable
      measurableSet_locallyFiniteFirstMarginalSet).2 hsource
  change ∀ᵐ q ∂(d.P.map F), q ∈ locallyFiniteFirstMarginalSet (J := J) at hmap
  have hLaw : (finiteSHFRadonLawOfSubsequenceLimit ϑ J d : Measure (J → SHFPairRadonMeasure)) = d.P.map F := rfl
  rw [hLaw]
  exact hmap


end Critical2DKPZ.SHF.Existence

end
