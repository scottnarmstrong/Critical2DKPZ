/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Existence.ProjectiveFiniteLaws
public import Critical2DKPZ.SHF.Existence.UniqueFiniteDimensionalLaws
public import Critical2DKPZ.RandomMeasure.Kolmogorov.Polish

/-! # Equality of finite Radon laws -/

@[expose] public section

set_option linter.style.haveILetI false

open MeasureTheory
open Critical2DKPZ.SHF.Limit

noncomputable section

namespace Critical2DKPZ.SHF.Existence

/-- The Radon-valued modification `pairMeasureRadonModification` is measurable. -/
theorem measurable_pairMeasureRadonModification : Measurable pairMeasureRadonModification := by
  have h := Critical2DKPZ.RandomMeasure.measurable_radonValuedModification
    (Critical2DKPZ.RandomMeasure.vagueCompactExhaustion (Plane × Plane)) id measurable_id
  rw [← Critical2DKPZ.RandomMeasure.eval_eq_vague_borel (X := Plane × Plane)] at h
  exact h

private theorem measurable_pairMeasureVectorRadonModification {J : Finset SHFTimePair} :
    Measurable (pairMeasureVectorRadonModification (J := J)) := by
  apply measurable_pi_iff.mpr
  intro j
  exact measurable_pairMeasureRadonModification.comp
    (show Measurable (fun μ : J → Measure (Plane × Plane) => μ j) from
    measurable_pi_apply j)

private theorem measurable_projectiveSHFRawVector (ϑ : ℝ) (J : Finset SHFTimePair)
    (d : FiniteSHFSubsequenceLimit ϑ J) :
    @Measurable d.Ω (J → Measure (Plane × Plane)) d.mΩ inferInstance
      (fun (ω : d.Ω) (j : J) => d.Z (projectiveSHFPairStart j) (projectiveSHFPairEnd j) ω) := by
  letI : MeasurableSpace d.Ω := d.mΩ
  letI : IsProbabilityMeasure d.P := d.hP
  apply measurable_pi_iff.mpr
  intro j
  exact (d.hZ.1 (projectiveSHFPairStart j) (d.htimes j).1
    (projectiveSHFPairEnd j) (d.htimes j).2 ((j : SHFTimePair).property.2)).1

private theorem finiteSHFRadonLawOfSubsequenceLimit_eq_mapped_raw (ϑ : ℝ) (J : Finset SHFTimePair)
    (d : FiniteSHFSubsequenceLimit ϑ J) :
    (finiteSHFRadonLawOfSubsequenceLimit ϑ J d : Measure (J → SHFPairRadonMeasure)) =
      (@Measure.map d.Ω (J → Measure (Plane × Plane)) d.mΩ inferInstance
        (fun (ω : d.Ω) (j : J) => d.Z (projectiveSHFPairStart j) (projectiveSHFPairEnd j) ω) d.P).map
        pairMeasureVectorRadonModification := by
  classical
  letI : MeasurableSpace d.Ω := d.mΩ
  letI : IsProbabilityMeasure d.P := d.hP
  have hraw := measurable_projectiveSHFRawVector ϑ J d
  have hradon := measurable_pairMeasureVectorRadonModification (J := J)
  change d.P.map (fun (ω : d.Ω) (j : J) =>
    pairMeasureRadonModification (d.Z (projectiveSHFPairStart j) (projectiveSHFPairEnd j) ω)) = _
  rw [Measure.map_map hradon hraw]
  rfl

/-- The compact Radon laws from two countable-time subsequential limits agree
whenever their finite-dimensional laws agree. -/
theorem finiteSHFRadonLawOfSubsequenceLimit_eq_of_fdd_eq (ϑ : ℝ) (hDenseSubseqLimitsInput : SubseqLimitsAreDense.{0} ϑ)
    (hT : DenseSHFUnique.{0, 0} (ϑ - Real.eulerMascheroniConstant))
    (J : Finset SHFTimePair) (d : FiniteSHFSubsequenceLimit ϑ J)
    {ψ' : ℕ → ℕ} (hψ' : StrictMono ψ') {Ω' : Type} [MeasurableSpace Ω']
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane))
    (hZ' : IsPolymerSubseqLimit ϑ d.D ψ' P' Z') :
    finiteSHFRadonLawOfSubsequenceLimit ϑ J d =
      MeasureTheory.ProbabilityMeasure.map ⟨P', inferInstance⟩
        (fun (ω : Ω') (j : J) => pairMeasureRadonModification
          (Z' (projectiveSHFPairStart j) (projectiveSHFPairEnd j) ω)) := by
  classical
  letI : MeasurableSpace d.Ω := d.mΩ
  letI : IsProbabilityMeasure d.P := d.hP
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let s : Fin (Fintype.card J) → ℝ := fun i => projectiveSHFPairStart (e.symm i)
  let t : Fin (Fintype.card J) → ℝ := fun i => projectiveSHFPairEnd (e.symm i)
  have hTimes : ∀ i, s i ∈ d.D ∧ t i ∈ d.D ∧ s i < t i := by
    intro i
    have hj := d.htimes (e.symm i)
    exact ⟨hj.1, hj.2, (e.symm i).val.property.2⟩
  have hfin := isPolymerSubseqLimit_fdd_eq_of ϑ hDenseSubseqLimitsInput hDenseSubseqLimitsInput hT d.B d.hB d.D d.hD
    d.hDB d.hdense d.hψ hψ' d.P P' d.Z Z' d.hZ hZ'
    (Fintype.card J) s t hTimes
  let R : (Fin (Fintype.card J) → Measure (Plane × Plane)) →
      (J → Measure (Plane × Plane)) := fun μ j => μ (e j)
  have hR : Measurable R := by
    apply measurable_pi_iff.mpr
    intro j
    exact measurable_pi_apply (e j)
  have hrawD : Measurable (fun (ω : d.Ω) => fun (i : Fin (Fintype.card J)) =>
      d.Z (s i) (t i) ω) := by
    apply measurable_pi_iff.mpr
    intro i
    exact (d.hZ.1 (s i) (hTimes i).1 (t i) (hTimes i).2.1 (hTimes i).2.2).1
  have hraw' : Measurable (fun (ω : Ω') => fun (i : Fin (Fintype.card J)) =>
      Z' (s i) (t i) ω) := by
    apply measurable_pi_iff.mpr
    intro i
    exact (hZ'.1 (s i) (hTimes i).1 (t i) (hTimes i).2.1 (hTimes i).2.2).1
  let Q : (Fin (Fintype.card J) → Measure (Plane × Plane) × Measure Plane) →
      Fin (Fintype.card J) → Measure (Plane × Plane) := fun q i => (q i).1
  have hQ : Measurable Q := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_fst.comp (measurable_pi_apply i)
  let pairD : d.Ω → Fin (Fintype.card J) → Measure (Plane × Plane) × Measure Plane :=
    fun ω i => (d.Z (s i) (t i) ω, Measure.map Prod.fst (d.Z (s i) (t i) ω))
  let pair' : Ω' → Fin (Fintype.card J) → Measure (Plane × Plane) × Measure Plane :=
    fun ω i => (Z' (s i) (t i) ω, Measure.map Prod.fst (Z' (s i) (t i) ω))
  have hpairD : Measurable pairD := by
    apply measurable_pi_iff.mpr
    intro i
    have hi : Measurable (fun ω : d.Ω => d.Z (s i) (t i) ω) :=
      (measurable_pi_apply i).comp hrawD
    exact hi.prodMk ((Measure.measurable_map Prod.fst measurable_fst).comp hi)
  have hpair' : Measurable pair' := by
    apply measurable_pi_iff.mpr
    intro i
    have hi : Measurable (fun ω : Ω' => Z' (s i) (t i) ω) :=
      (measurable_pi_apply i).comp hraw'
    exact hi.prodMk ((Measure.measurable_map Prod.fst measurable_fst).comp hi)
  have hrawJ' : Measurable (fun (ω : Ω') (j : J) =>
      Z' (projectiveSHFPairStart j) (projectiveSHFPairEnd j) ω) := by
    apply measurable_pi_iff.mpr
    intro j
    exact (hZ'.1 (projectiveSHFPairStart j) (d.htimes j).1
      (projectiveSHFPairEnd j) (d.htimes j).2 ((j : SHFTimePair).property.2)).1
  have hfinRaw : d.P.map (fun (ω : d.Ω) (i : Fin (Fintype.card J)) =>
      d.Z (s i) (t i) ω) =
      P'.map (fun (ω : Ω') (i : Fin (Fintype.card J)) => Z' (s i) (t i) ω) := by
    calc
      d.P.map (fun (ω : d.Ω) (i : Fin (Fintype.card J)) => d.Z (s i) (t i) ω) =
          (d.P.map pairD).map Q := by
            rw [Measure.map_map hQ hpairD]
            congr 1
      _ = (P'.map pair').map Q :=
            congrArg (fun M : Measure
                (Fin (Fintype.card J) → Measure (Plane × Plane) × Measure Plane) => M.map Q) hfin
      _ = P'.map (fun (ω : Ω') (i : Fin (Fintype.card J)) => Z' (s i) (t i) ω) := by
            rw [Measure.map_map hQ hpair']
            congr 1
  have hrawLaw : d.P.map (fun (ω : d.Ω) (j : J) =>
      d.Z (projectiveSHFPairStart j) (projectiveSHFPairEnd j) ω) =
      P'.map (fun (ω : Ω') (j : J) => Z' (projectiveSHFPairStart j) (projectiveSHFPairEnd j) ω) := by
    calc
      d.P.map (fun (ω : d.Ω) (j : J) => d.Z (projectiveSHFPairStart j) (projectiveSHFPairEnd j) ω) =
          (d.P.map (fun (ω : d.Ω) (i : Fin (Fintype.card J)) => d.Z (s i) (t i) ω)).map R := by
            rw [Measure.map_map hR hrawD]
            congr 1
            funext ω j
            simp [R, s, t]
      _ = (P'.map (fun (ω : Ω') (i : Fin (Fintype.card J)) => Z' (s i) (t i) ω)).map R := by
            rw [hfinRaw]
      _ = P'.map (fun (ω : Ω') (j : J) => Z' (projectiveSHFPairStart j) (projectiveSHFPairEnd j) ω) := by
            rw [Measure.map_map hR hraw']
            congr 1
            funext ω j
            simp [R, s, t]
  have hradon := measurable_pairMeasureVectorRadonModification (J := J)
  apply Subtype.ext
  calc
    (finiteSHFRadonLawOfSubsequenceLimit ϑ J d : Measure (J → SHFPairRadonMeasure)) =
        (d.P.map (fun (ω : d.Ω) (j : J) => d.Z (projectiveSHFPairStart j) (projectiveSHFPairEnd j) ω)).map
          pairMeasureVectorRadonModification := finiteSHFRadonLawOfSubsequenceLimit_eq_mapped_raw ϑ J d
    _ = (P'.map (fun (ω : Ω') (j : J) => Z' (projectiveSHFPairStart j) (projectiveSHFPairEnd j) ω)).map
          pairMeasureVectorRadonModification := by rw [hrawLaw]
    _ = P'.map (fun (ω : Ω') (j : J) => pairMeasureRadonModification
          (Z' (projectiveSHFPairStart j) (projectiveSHFPairEnd j) ω)) := by
            rw [Measure.map_map hradon hrawJ']
            rfl

end Critical2DKPZ.SHF.Existence

end
