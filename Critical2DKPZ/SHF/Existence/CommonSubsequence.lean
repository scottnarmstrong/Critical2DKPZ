/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Existence.CommonSHFProcess
public import Critical2DKPZ.SHF.Existence.WindowFiniteDimensionalLaws

/-! # The common process is a subsequential limit on every dense window -/

@[expose] public section

set_option linter.style.haveILetI false

open MeasureTheory
open Critical2DKPZ.SHF.Limit

noncomputable section

namespace Critical2DKPZ.SHF.Existence

/-- The Kolmogorov process and every subsequential polymer limit on a countable dense time window have the same finite-dimensional random-measure laws. -/
theorem projectiveSHFCommonProcess_fdd_eq_of_subseqLimit (ϑ : ℝ)
    (hDenseSubseqLimitsInput : SubseqLimitsAreDense.{0} ϑ)
    (hT : DenseSHFUnique.{0, 0} (ϑ - Real.eulerMascheroniConstant))
    {μ : Measure (SHFTimePair → SHFPairRadonMeasure)} [IsProbabilityMeasure μ]
    (hProjective : IsProjectiveLimit (α := fun _ : SHFTimePair => SHFPairRadonMeasure) μ
      (projectiveSHFFamily ϑ))
    (B : ℝ) (hB : 0 < B) (D : Set ℝ) (hD : D.Countable)
    (hDB : D ⊆ Set.Icc 0 B) (hdense : Set.Icc 0 B ⊆ closure D)
    {ψ : ℕ → ℕ} (hψ : StrictMono ψ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsPolymerSubseqLimit ϑ D ψ P Z)
    (k : ℕ) (s t : Fin k → ℝ)
    (hst : ∀ i, s i ∈ D ∧ t i ∈ D ∧ s i < t i) :
    μ.map (fun ω i => projectiveSHFCommonProcess (s i) (t i) ω) =
      P.map (fun ω i => Z (s i) (t i) ω) := by
  classical
  let idx : Fin k → SHFTimePair := fun i =>
    ⟨(s i, t i), (hDB (hst i).1).1, (hst i).2.2⟩
  let J : Finset SHFTimePair := Finset.univ.image idx
  let intoJ : Fin k → J := fun i =>
    ⟨idx i, Finset.mem_image_of_mem idx (Finset.mem_univ i)⟩
  let A : (J → SHFPairRadonMeasure) → Fin k → Measure (Plane × Plane) := fun q i =>
    (q (intoJ i) : Measure (Plane × Plane))
  let R : (SHFTimePair → SHFPairRadonMeasure) → J → SHFPairRadonMeasure := fun ω j => ω j
  have hR : Measurable R := by
    apply measurable_pi_iff.mpr
    intro j
    exact measurable_pi_apply (j : SHFTimePair)
  have hA : Measurable A := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_subtype_coe.comp (measurable_pi_apply (intoJ i))
  have hstateLaw : μ.map R =
      (projectiveSHFFiniteRadonLaw ϑ J : Measure (J → SHFPairRadonMeasure)) := by
    change μ.map J.restrict = projectiveSHFFiniteRadonLaw ϑ J
    simpa only [projectiveSHFFamily] using hProjective J
  have hprocessFun : (fun ω i => projectiveSHFCommonProcess (s i) (t i) ω) = A ∘ R := by
    funext ω i
    have hi := projectiveSHFCommonProcess_eq_coordinate (idx i) ω
    simpa [idx, A, R, projectiveSHFPairStart, projectiveSHFPairEnd] using hi
  have hprocessLaw : μ.map (fun ω i => projectiveSHFCommonProcess (s i) (t i) ω) =
      (projectiveSHFFiniteRadonLaw ϑ J : Measure (J → SHFPairRadonMeasure)).map A := by
    calc
      μ.map (fun ω i => projectiveSHFCommonProcess (s i) (t i) ω) = μ.map (A ∘ R) := by
        rw [hprocessFun]
      _ = (μ.map R).map A := (Measure.map_map hA hR).symm
      _ = (projectiveSHFFiniteRadonLaw ϑ J : Measure (J → SHFPairRadonMeasure)).map A := by
        rw [hstateLaw]
  have htimesJ : ∀ j : J, projectiveSHFPairStart j ∈ D ∧ projectiveSHFPairEnd j ∈ D := by
    intro j
    rcases Finset.mem_image.mp j.property with ⟨i, -, hij⟩
    have hval : (j : SHFTimePair) = idx i := by simpa using hij.symm
    have hs : projectiveSHFPairStart j = s i := by
      have := congrArg projectiveSHFPairStart hval
      simpa [idx, projectiveSHFPairStart] using this
    have ht : projectiveSHFPairEnd j = t i := by
      have := congrArg projectiveSHFPairEnd hval
      simpa [idx, projectiveSHFPairEnd] using this
    rw [hs, ht]
    exact ⟨(hst i).1, (hst i).2.1⟩
  let d := finiteSHFSubsequenceLimit ϑ J
  have hfiniteRadon := finiteSHFRadonLawOfSubsequenceLimit_eq_of_subseqLimit ϑ hDenseSubseqLimitsInput hT J d
    B hB D hD hDB hdense hψ P Z hZ htimesJ
  have hfiniteMeasure :
      (projectiveSHFFiniteRadonLaw ϑ J : Measure (J → SHFPairRadonMeasure)) =
        P.map (fun ω (j : J) => pairMeasureRadonModification
          (Z (projectiveSHFPairStart j) (projectiveSHFPairEnd j) ω)) := by
    exact congrArg Subtype.val hfiniteRadon
  let radJ : Ω → J → SHFPairRadonMeasure := fun ω j =>
    pairMeasureRadonModification (Z (projectiveSHFPairStart j) (projectiveSHFPairEnd j) ω)
  have hradJ : Measurable radJ := by
    apply measurable_pi_iff.mpr
    intro j
    exact measurable_pairMeasureRadonModification.comp
      ((hZ.1 (projectiveSHFPairStart j) (htimesJ j).1 (projectiveSHFPairEnd j) (htimesJ j).2
        ((j : SHFTimePair).property.2)).1)
  have hmodCoord : ∀ i : Fin k, (fun ω =>
      (pairMeasureRadonModification (Z (s i) (t i) ω) : Measure (Plane × Plane))) =ᵐ[P]
      (fun ω => Z (s i) (t i) ω) := by
    intro i
    have hlocal := (hZ.1 (s i) (hst i).1 (t i) (hst i).2.1
      (hst i).2.2).2
    filter_upwards [hlocal] with ω hω
    exact pairMeasureRadonModification_eq_of_locallyFinite _ hω.1
  have hmod : (fun ω i => Z (s i) (t i) ω) =ᵐ[P] (A ∘ radJ) := by
    filter_upwards [ae_all_iff.mpr hmodCoord] with ω hω
    funext i
    have hi := hω i
    simpa [A, radJ, intoJ, idx, projectiveSHFPairStart, projectiveSHFPairEnd] using hi.symm
  calc
    μ.map (fun ω i => projectiveSHFCommonProcess (s i) (t i) ω) =
        (projectiveSHFFiniteRadonLaw ϑ J : Measure (J → SHFPairRadonMeasure)).map A := hprocessLaw
    _ = (P.map radJ).map A := by rw [hfiniteMeasure]
    _ = P.map (A ∘ radJ) := Measure.map_map hA hradJ
    _ = P.map (fun ω i => Z (s i) (t i) ω) := Measure.map_congr hmod.symm

/-- On every countable dense window, the common process is itself a
subsequential polymer limit. -/
theorem projectiveSHFCommonProcess_isPolymerSubseqLimit (ϑ : ℝ)
    (hDenseSubseqLimitsInput : SubseqLimitsAreDense.{0} ϑ)
    (hT : DenseSHFUnique.{0, 0} (ϑ - Real.eulerMascheroniConstant))
    {μ : Measure (SHFTimePair → SHFPairRadonMeasure)} [IsProbabilityMeasure μ]
    (hProjective : IsProjectiveLimit (α := fun _ : SHFTimePair => SHFPairRadonMeasure) μ
      (projectiveSHFFamily ϑ))
    (B : ℝ) (hB : 0 < B) (D : Set ℝ) (hD : D.Countable)
    (hDB : D ⊆ Set.Icc 0 B) (hdense : Set.Icc 0 B ⊆ closure D)
    {ψ : ℕ → ℕ} (hψ : StrictMono ψ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsPolymerSubseqLimit ϑ D ψ P Z) :
    IsPolymerSubseqLimit ϑ D ψ μ projectiveSHFCommonProcess := by
  apply isPolymerSubseqLimit_of_fdd_eq hZ
  · intro s hs t ht hst
    exact measurable_projectiveSHFCommonProcess s t (hDB hs).1 hst
  · intro k s t htimes
    exact projectiveSHFCommonProcess_fdd_eq_of_subseqLimit ϑ hDenseSubseqLimitsInput hT hProjective B hB D hD
      hDB hdense hψ P Z hZ k s t htimes |>.symm

end Critical2DKPZ.SHF.Existence

end
