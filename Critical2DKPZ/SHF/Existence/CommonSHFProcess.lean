/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Existence.ProjectiveMeasureFamily
public import Critical2DKPZ.SHF.Existence.ProjectiveLawProperties

/-! # Common process from the projective family -/

@[expose] public section

set_option linter.style.haveILetI false

open MeasureTheory
open Critical2DKPZ.SHF.Limit

noncomputable section

namespace Critical2DKPZ.SHF.Existence

/-- The finite Radon laws selected for SHF existence. -/
noncomputable def projectiveSHFFamily (ϑ : ℝ) :
    ∀ J : Finset SHFTimePair, Measure (J → SHFPairRadonMeasure) := fun J =>
      (projectiveSHFFiniteRadonLaw ϑ J : Measure (J → SHFPairRadonMeasure))

/-- The measure-valued process encoded by the Kolmogorov coordinates. -/
def projectiveSHFCommonProcess (s t : ℝ) (ω : SHFTimePair → SHFPairRadonMeasure) :
    Measure (Plane × Plane) := by
  classical
  exact if h : 0 ≤ s ∧ s < t then (ω ⟨(s, t), h⟩ : Measure (Plane × Plane)) else 0

/-- A valid process coordinate is measurable. -/
theorem measurable_projectiveSHFCommonProcess (s t : ℝ) (hs : 0 ≤ s) (hst : s < t) :
    Measurable (projectiveSHFCommonProcess s t) := by
  let i : SHFTimePair := ⟨(s, t), hs, hst⟩
  have hcond : 0 ≤ s ∧ s < t := ⟨hs, hst⟩
  change Measurable (fun (ω : SHFTimePair → SHFPairRadonMeasure) => if h : 0 ≤ s ∧ s < t then
    (ω ⟨(s, t), h⟩ : Measure (Plane × Plane)) else 0)
  simp only [dite_eq_left hcond]
  change Measurable (fun (ω : SHFTimePair → SHFPairRadonMeasure) =>
    (ω i : Measure (Plane × Plane)))
  exact measurable_subtype_coe.comp (measurable_pi_apply i)

/-- Every coordinate of the common process is a locally finite measure. -/
theorem projectiveSHFCommonProcess_pair_locallyFinite (s t : ℝ) (hs : 0 ≤ s) (hst : s < t)
    (ω : SHFTimePair → SHFPairRadonMeasure) :
    IsLocallyFiniteMeasure (projectiveSHFCommonProcess s t ω) := by
  let i : SHFTimePair := ⟨(s, t), hs, hst⟩
  have hcond : 0 ≤ s ∧ s < t := ⟨hs, hst⟩
  change IsLocallyFiniteMeasure (if h : 0 ≤ s ∧ s < t then
    (ω ⟨(s, t), h⟩ : Measure (Plane × Plane)) else 0)
  simp only [dite_eq_left hcond]
  change IsLocallyFiniteMeasure (ω i : Measure (Plane × Plane))
  exact (ω i).property


private theorem measurableSet_isLocallyFiniteMeasure_map_fst :
    MeasurableSet {μ : SHFPairRadonMeasure | IsLocallyFiniteMeasure
      (Measure.map Prod.fst (μ : Measure (Plane × Plane)))} := by
  have hcoe : Measurable (fun μ : SHFPairRadonMeasure => (μ : Measure (Plane × Plane))) :=
    measurable_subtype_coe
  have hflat := (Measure.measurable_map Prod.fst measurable_fst).comp hcoe
  exact (Critical2DKPZ.RandomMeasure.measurableSet_isLocallyFiniteMeasure
      (Critical2DKPZ.RandomMeasure.vagueCompactExhaustion Plane)
      (fun μ => μ) measurable_id).preimage hflat

/-- The common process has locally finite flat marginals almost surely. -/
theorem projectiveSHFLimit_flatMarginal_ae (ϑ : ℝ)
    {μ : Measure (SHFTimePair → SHFPairRadonMeasure)}
    (hP : IsProjectiveLimit (α := fun _ : SHFTimePair => SHFPairRadonMeasure) μ
      (projectiveSHFFamily ϑ)) (j : SHFTimePair) :
    ∀ᵐ ω ∂μ, IsLocallyFiniteMeasure
      (Measure.map Prod.fst (ω j : Measure (Plane × Plane))) := by
  classical
  let J : Finset SHFTimePair := {j}
  let i : J := ⟨j, by simp [J]⟩
  let R : (SHFTimePair → SHFPairRadonMeasure) → J → SHFPairRadonMeasure := fun ω k => ω k
  let E : (J → SHFPairRadonMeasure) → SHFPairRadonMeasure := fun q => q i
  have hR : Measurable R := by
    apply measurable_pi_iff.mpr
    intro k
    change Measurable (fun ω : SHFTimePair → SHFPairRadonMeasure => ω (k : SHFTimePair))
    exact measurable_pi_apply (k : SHFTimePair)
  have hE : Measurable E := measurable_pi_apply i
  have hcoord : μ.map (fun ω => ω j) =
      (projectiveSHFFiniteRadonLaw ϑ J : Measure (J → SHFPairRadonMeasure)).map E := by
    calc
      μ.map (fun ω => ω j) = (μ.map R).map E := by
        rw [Measure.map_map hE hR]
        rfl
      _ = (projectiveSHFFiniteRadonLaw ϑ J : Measure (J → SHFPairRadonMeasure)).map E := by
        have hlimJ : μ.map R =
            (projectiveSHFFiniteRadonLaw ϑ J : Measure (J → SHFPairRadonMeasure)) := by
          change μ.map J.restrict = projectiveSHFFiniteRadonLaw ϑ J
          simpa only [projectiveSHFFamily] using hP J
        exact congrArg (fun M : Measure (J → SHFPairRadonMeasure) => M.map E) hlimJ
  have hfinite := finiteSHFRadonLawOfSubsequenceLimit_flatMarginal_ae ϑ J
    (finiteSHFSubsequenceLimit ϑ J)
  have hfiniteCoord : ∀ᵐ q ∂(projectiveSHFFiniteRadonLaw ϑ J : Measure (J → SHFPairRadonMeasure)),
      IsLocallyFiniteMeasure (Measure.map Prod.fst (q i : Measure (Plane × Plane))) := by
    filter_upwards [hfinite] with q hq
    exact hq i
  have hflat := (MeasureTheory.ae_map_iff hE.aemeasurable
      measurableSet_isLocallyFiniteMeasure_map_fst).2 hfiniteCoord
  rw [← hcoord] at hflat
  exact (MeasureTheory.ae_map_iff (measurable_pi_apply j).aemeasurable
    measurableSet_isLocallyFiniteMeasure_map_fst).mp hflat

/-- On a valid time pair, the common process reads the corresponding
Kolmogorov coordinate. -/
theorem projectiveSHFCommonProcess_eq_coordinate (j : SHFTimePair)
    (ω : SHFTimePair → SHFPairRadonMeasure) :
    projectiveSHFCommonProcess (projectiveSHFPairStart j) (projectiveSHFPairEnd j) ω =
      (ω j : Measure (Plane × Plane)) := by
  have hpair := j.property
  have hcond : 0 ≤ projectiveSHFPairStart j ∧ projectiveSHFPairStart j < projectiveSHFPairEnd j := by
    simpa [projectiveSHFPairStart, projectiveSHFPairEnd] using hpair
  change (if h : 0 ≤ projectiveSHFPairStart j ∧ projectiveSHFPairStart j < projectiveSHFPairEnd j then
    (ω ⟨(projectiveSHFPairStart j, projectiveSHFPairEnd j), h⟩ : Measure (Plane × Plane)) else 0) = _
  rw [dite_eq_left hcond]
  congr 1


/-- Kolmogorov's extension of the SHF existence finite-dimensional Radon laws. -/
theorem exists_projectiveSHFLimit (ϑ : ℝ)
    (hDenseSubseqLimitsInput : SubseqLimitsAreDense.{0} ϑ)
    (hT : DenseSHFUnique.{0, 0} (ϑ - Real.eulerMascheroniConstant)) :
    ∃ μ : Measure (SHFTimePair → SHFPairRadonMeasure), IsProbabilityMeasure μ ∧
      IsProjectiveLimit (α := fun _ : SHFTimePair => SHFPairRadonMeasure) μ
        (projectiveSHFFamily ϑ) := by
  classical
  letI : TopologicalSpace SHFPairRadonMeasure :=
    Critical2DKPZ.RandomMeasure.vagueTopology (Plane × Plane)
  letI : PolishSpace SHFPairRadonMeasure :=
    Critical2DKPZ.RandomMeasure.polishSpace_positiveRadonMeasure_planePair
  letI : BorelSpace SHFPairRadonMeasure :=
    ⟨Critical2DKPZ.RandomMeasure.borel_positiveRadonMeasure_eq_comap.symm⟩
  have hprob : ∀ J : Finset SHFTimePair,
      IsProbabilityMeasure (projectiveSHFFamily ϑ J) := by
    intro J
    exact (projectiveSHFFiniteRadonLaw ϑ J).property
  letI : ∀ J : Finset SHFTimePair,
      IsProbabilityMeasure (projectiveSHFFamily ϑ J) := hprob
  have hprojective : IsProjectiveMeasureFamily
      (α := fun _ : SHFTimePair => SHFPairRadonMeasure) (projectiveSHFFamily ϑ) := by
    intro I J hJI
    exact congrArg Subtype.val (projectiveSHFFiniteRadonLaw_projective ϑ hDenseSubseqLimitsInput hT I J hJI)
  exact Critical2DKPZ.RandomMeasure.Kolmogorov.exists_isProjectiveLimit_polish
    (projectiveSHFFamily ϑ) hprojective

end Critical2DKPZ.SHF.Existence

end
