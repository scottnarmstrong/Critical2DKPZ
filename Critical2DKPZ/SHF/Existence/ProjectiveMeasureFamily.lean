/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Existence.ProjectiveMeasureSupport
public import Critical2DKPZ.RandomMeasure.Kolmogorov.Polish

/-! # Projective family of finite polymer laws -/

@[expose] public section

set_option linter.style.haveILetI false

open MeasureTheory
open Critical2DKPZ.SHF.Limit

noncomputable section

namespace Critical2DKPZ.SHF.Existence

/-- Compare a finite law with the same coordinates of a subsequential limit
defined on a larger time set. -/
theorem finiteSHFRadonLawOfSubsequenceLimit_eq_common (ϑ : ℝ)
    (hDenseSubseqLimitsInput : SubseqLimitsAreDense.{0} ϑ)
    (hT : DenseSHFUnique.{0, 0} (ϑ - Real.eulerMascheroniConstant))
    (J : Finset SHFTimePair) (d : FiniteSHFSubsequenceLimit ϑ J)
    {D : Set ℝ} (hDD : d.D ⊆ D) {ψ : ℕ → ℕ} (hψ : StrictMono ψ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsPolymerSubseqLimit ϑ D ψ P Z) :
    finiteSHFRadonLawOfSubsequenceLimit ϑ J d =
      ProbabilityMeasure.map ⟨P, inferInstance⟩
        (fun (ω : Ω) (j : J) => pairMeasureRadonModification
          (Z (projectiveSHFPairStart j) (projectiveSHFPairEnd j) ω)) := by
  exact finiteSHFRadonLawOfSubsequenceLimit_eq_of_fdd_eq ϑ hDenseSubseqLimitsInput hT J d (ψ' := ψ) hψ P Z
    (isPolymerSubseqLimit_mono hDD hZ)

/-- The chosen finite Radon laws are consistent under coordinate restriction. -/
theorem projectiveSHFFiniteRadonLaw_projective (ϑ : ℝ)
    (hDenseSubseqLimitsInput : SubseqLimitsAreDense.{0} ϑ)
    (hT : DenseSHFUnique.{0, 0} (ϑ - Real.eulerMascheroniConstant))
    (I J : Finset SHFTimePair) (hJI : J ⊆ I) :
    projectiveSHFFiniteRadonLaw ϑ J =
      (projectiveSHFFiniteRadonLaw ϑ I).map
        (Finset.restrict₂ (π := fun _ : SHFTimePair => SHFPairRadonMeasure) hJI) := by
  classical
  let dI := finiteSHFSubsequenceLimit ϑ I
  let dJ := finiteSHFSubsequenceLimit ϑ J
  let D := dI.D ∪ dJ.D
  have hD : D.Countable := dI.hD.union dJ.hD
  have hD0 : ∀ r ∈ D, 0 ≤ r := by
    intro r hr
    rcases hr with hr | hr
    · exact (dI.hDB hr).1
    · exact (dJ.hDB hr).1
  obtain ⟨ψ, hψ, Ω, mΩ, P, hP, Z, hZ⟩ :=
    exists_polymerSubseqLimit ϑ D hD hD0 (fun n => n) strictMono_id
  let ψ' := (fun n : ℕ => n) ∘ ψ
  have hψ' : StrictMono ψ' := strictMono_id.comp hψ
  letI : MeasurableSpace Ω := mΩ
  letI : IsProbabilityMeasure P := hP
  have hDI : dI.D ⊆ D := Set.subset_union_left
  have hDJ : dJ.D ⊆ D := Set.subset_union_right
  have hLawI := finiteSHFRadonLawOfSubsequenceLimit_eq_common ϑ hDenseSubseqLimitsInput hT I dI hDI hψ' P Z hZ
  have hLawJ := finiteSHFRadonLawOfSubsequenceLimit_eq_common ϑ hDenseSubseqLimitsInput hT J dJ hDJ hψ' P Z hZ
  have hLawI' : projectiveSHFFiniteRadonLaw ϑ I =
      ProbabilityMeasure.map ⟨P, hP⟩
        (fun (ω : Ω) (i : I) => pairMeasureRadonModification
          (Z (projectiveSHFPairStart i) (projectiveSHFPairEnd i) ω)) := hLawI
  have hLawJ' : projectiveSHFFiniteRadonLaw ϑ J =
      ProbabilityMeasure.map ⟨P, hP⟩
        (fun (ω : Ω) (j : J) => pairMeasureRadonModification
          (Z (projectiveSHFPairStart j) (projectiveSHFPairEnd j) ω)) := hLawJ
  let R : (I → SHFPairRadonMeasure) → J → SHFPairRadonMeasure :=
    Finset.restrict₂ (π := fun _ : SHFTimePair => SHFPairRadonMeasure) hJI
  have hR : Measurable R := by
    apply measurable_pi_iff.mpr
    intro j
    exact measurable_pi_apply (⟨(j : SHFTimePair), hJI j.property⟩ : I)
  have hZI : Measurable (fun (ω : Ω) (i : I) =>
      pairMeasureRadonModification (Z (projectiveSHFPairStart i) (projectiveSHFPairEnd i) ω)) := by
    apply measurable_pi_iff.mpr
    intro i
    have hs : projectiveSHFPairStart i ∈ D := hDI (dI.htimes i).1
    have ht : projectiveSHFPairEnd i ∈ D := hDI (dI.htimes i).2
    have hm := (hZ.1 (projectiveSHFPairStart i) hs
      (projectiveSHFPairEnd i) ht ((i : SHFTimePair).property.2)).1
    exact measurable_pairMeasureRadonModification.comp hm
  have hZJ : Measurable (fun (ω : Ω) (j : J) =>
      pairMeasureRadonModification (Z (projectiveSHFPairStart j) (projectiveSHFPairEnd j) ω)) := by
    apply measurable_pi_iff.mpr
    intro j
    have hs : projectiveSHFPairStart j ∈ D := hDJ (dJ.htimes j).1
    have ht : projectiveSHFPairEnd j ∈ D := hDJ (dJ.htimes j).2
    have hm := (hZ.1 (projectiveSHFPairStart j) hs
      (projectiveSHFPairEnd j) ht ((j : SHFTimePair).property.2)).1
    exact measurable_pairMeasureRadonModification.comp hm
  apply Subtype.ext
  calc
    (projectiveSHFFiniteRadonLaw ϑ J : Measure (J → SHFPairRadonMeasure)) =
        (P.map (fun (ω : Ω) (j : J) =>
          pairMeasureRadonModification (Z (projectiveSHFPairStart j) (projectiveSHFPairEnd j) ω))) := by
            exact congrArg Subtype.val hLawJ'
    _ = (P.map (fun (ω : Ω) (i : I) =>
          pairMeasureRadonModification (Z (projectiveSHFPairStart i) (projectiveSHFPairEnd i) ω))).map R := by
            rw [Measure.map_map hR hZI]
            congr 1
    _ = (projectiveSHFFiniteRadonLaw ϑ I : Measure (I → SHFPairRadonMeasure)).map R := by
            exact congrArg (fun M : Measure (I → SHFPairRadonMeasure) => M.map R)
              (congrArg Subtype.val hLawI').symm

end Critical2DKPZ.SHF.Existence

end
