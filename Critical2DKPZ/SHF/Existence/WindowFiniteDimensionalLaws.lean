/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Existence.ProjectiveMeasureFamily

/-! # Comparing limits on different dense windows -/

@[expose] public section

set_option linter.style.haveILetI false

open MeasureTheory
open Critical2DKPZ.SHF.Limit

noncomputable section

namespace Critical2DKPZ.SHF.Existence


/-- Radonifying the first coordinate of the joint compact/flat law preserves
the finite-dimensional equality. -/
theorem projectiveSHFRadonifiedFDD_eq_of_pairFDD_eq {k : ℕ}
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Z : Fin k → Ω → Measure (Plane × Plane))
    (Z' : Fin k → Ω' → Measure (Plane × Plane))
    (hZ : ∀ i, Measurable (Z i)) (hZ' : ∀ i, Measurable (Z' i))
    (hPair : P.map (fun ω i => (Z i ω, (Z i ω).map Prod.fst)) =
      P'.map (fun ω i => (Z' i ω, (Z' i ω).map Prod.fst))) :
    P.map (fun ω i => pairMeasureRadonModification (Z i ω)) =
      P'.map (fun ω i => pairMeasureRadonModification (Z' i ω)) := by
  let G : (Fin k → Measure (Plane × Plane) × Measure Plane) →
      Fin k → SHFPairRadonMeasure := fun q i => pairMeasureRadonModification (q i).1
  have hG : Measurable G := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_pairMeasureRadonModification.comp
      (measurable_fst.comp (measurable_pi_apply i))
  have hPairMap : Measurable (fun ω i => (Z i ω, (Z i ω).map Prod.fst)) := by
    apply measurable_pi_iff.mpr
    intro i
    exact (hZ i).prodMk
      ((Measure.measurable_map Prod.fst measurable_fst).comp (hZ i))
  have hPairMap' : Measurable (fun ω i => (Z' i ω, (Z' i ω).map Prod.fst)) := by
    apply measurable_pi_iff.mpr
    intro i
    exact (hZ' i).prodMk
      ((Measure.measurable_map Prod.fst measurable_fst).comp (hZ' i))
  calc
    P.map (fun ω i => pairMeasureRadonModification (Z i ω)) =
        (P.map (fun ω i => (Z i ω, (Z i ω).map Prod.fst))).map G := by
          rw [Measure.map_map hG hPairMap]
          rfl
    _ = (P'.map (fun ω i => (Z' i ω, (Z' i ω).map Prod.fst))).map G := by
          rw [hPair]
    _ = P'.map (fun ω i => pairMeasureRadonModification (Z' i ω)) := by
          rw [Measure.map_map hG hPairMap']
          rfl

/-- A selected finite Radon law agrees with the Radonified finite-dimensional
law of any subsequential limit on a dense window containing its times. -/
theorem finiteSHFRadonLawOfSubsequenceLimit_eq_of_subseqLimit (ϑ : ℝ)
    (hDenseSubseqLimitsInput : SubseqLimitsAreDense.{0} ϑ)
    (hT : DenseSHFUnique.{0, 0} (ϑ - Real.eulerMascheroniConstant))
    (J : Finset SHFTimePair) (d : FiniteSHFSubsequenceLimit ϑ J)
    (B : ℝ) (hB : 0 < B) (D : Set ℝ) (hD : D.Countable)
    (hDB : D ⊆ Set.Icc 0 B) (hdense : Set.Icc 0 B ⊆ closure D)
    {ψ : ℕ → ℕ} (hψ : StrictMono ψ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsPolymerSubseqLimit ϑ D ψ P Z)
    (htimes : ∀ j : J, projectiveSHFPairStart j ∈ D ∧ projectiveSHFPairEnd j ∈ D) :
    finiteSHFRadonLawOfSubsequenceLimit ϑ J d =
      ProbabilityMeasure.map ⟨P, inferInstance⟩
        (fun (ω : Ω) (j : J) => pairMeasureRadonModification
          (Z (projectiveSHFPairStart j) (projectiveSHFPairEnd j) ω)) := by
  classical
  let U := d.D ∪ D
  have hU : U.Countable := d.hD.union hD
  have hU0 : ∀ r ∈ U, 0 ≤ r := by
    intro r hr
    rcases hr with hr | hr
    · exact (d.hDB hr).1
    · exact (hDB hr).1
  obtain ⟨ψc, hψc, Ωc, mΩc, Pc, hPc, Zc, hZc⟩ :=
    exists_polymerSubseqLimit ϑ U hU hU0 (fun n => n) strictMono_id
  let ψc' := (fun n : ℕ => n) ∘ ψc
  have hψc' : StrictMono ψc' := strictMono_id.comp hψc
  letI : MeasurableSpace Ωc := mΩc
  letI : IsProbabilityMeasure Pc := hPc
  have hDU : d.D ⊆ U := Set.subset_union_left
  have hDoldU : D ⊆ U := Set.subset_union_right
  have hZcOldD : IsPolymerSubseqLimit ϑ D ψc' Pc Zc :=
    isPolymerSubseqLimit_mono hDoldU hZc
  have hdataCommon := finiteSHFRadonLawOfSubsequenceLimit_eq_common ϑ hDenseSubseqLimitsInput hT J d hDU hψc' Pc Zc hZc
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let s : Fin (Fintype.card J) → ℝ := fun i => projectiveSHFPairStart (e.symm i)
  let t : Fin (Fintype.card J) → ℝ := fun i => projectiveSHFPairEnd (e.symm i)
  have htimesFin : ∀ i, s i ∈ D ∧ t i ∈ D ∧ s i < t i := by
    intro i
    have ht := htimes (e.symm i)
    exact ⟨ht.1, ht.2, (e.symm i).val.property.2⟩
  have hpair := isPolymerSubseqLimit_fdd_eq_of ϑ hDenseSubseqLimitsInput hDenseSubseqLimitsInput hT B hB D hD hDB
    hdense hψ hψc' P Pc Z Zc hZ hZcOldD (Fintype.card J) s t htimesFin
  let ZFin : Fin (Fintype.card J) → Ω → Measure (Plane × Plane) :=
    fun i ω => Z (s i) (t i) ω
  let ZcFin : Fin (Fintype.card J) → Ωc → Measure (Plane × Plane) :=
    fun i ω => Zc (s i) (t i) ω
  have hZFin : ∀ i, Measurable (ZFin i) := by
    intro i
    exact (hZ.1 (s i) (htimesFin i).1 (t i) (htimesFin i).2.1
      (htimesFin i).2.2).1
  have hZcFin : ∀ i, Measurable (ZcFin i) := by
    intro i
    have hs : s i ∈ U := Set.mem_union_right d.D (htimesFin i).1
    have ht : t i ∈ U := Set.mem_union_right d.D (htimesFin i).2.1
    exact (hZc.1 (s i) hs (t i) ht (htimesFin i).2.2).1
  have hradFinMeas : Measurable (fun ω i =>
      pairMeasureRadonModification (ZFin i ω)) := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_pairMeasureRadonModification.comp (hZFin i)
  have hradFinMeasC : Measurable (fun ω i =>
      pairMeasureRadonModification (ZcFin i ω)) := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_pairMeasureRadonModification.comp (hZcFin i)
  have hradFin := projectiveSHFRadonifiedFDD_eq_of_pairFDD_eq P Pc ZFin ZcFin
    hZFin hZcFin hpair
  let R : (Fin (Fintype.card J) → SHFPairRadonMeasure) → J → SHFPairRadonMeasure :=
    fun q j => q (e j)
  have hR : Measurable R := by
    apply measurable_pi_iff.mpr
    intro j
    exact measurable_pi_apply (e j)
  let radJ : Ω → J → SHFPairRadonMeasure := fun ω j =>
    pairMeasureRadonModification (Z (projectiveSHFPairStart j) (projectiveSHFPairEnd j) ω)
  let radJc : Ωc → J → SHFPairRadonMeasure := fun ω j =>
    pairMeasureRadonModification (Zc (projectiveSHFPairStart j) (projectiveSHFPairEnd j) ω)
  have hradJ : Measurable radJ := by
    apply measurable_pi_iff.mpr
    intro j
    exact measurable_pairMeasureRadonModification.comp
      ((hZ.1 (projectiveSHFPairStart j) (htimes j).1 (projectiveSHFPairEnd j) (htimes j).2
        ((j : SHFTimePair).property.2)).1)
  have hradJc : Measurable radJc := by
    apply measurable_pi_iff.mpr
    intro j
    have hs : projectiveSHFPairStart j ∈ U := Set.mem_union_right d.D (htimes j).1
    have ht : projectiveSHFPairEnd j ∈ U := Set.mem_union_right d.D (htimes j).2
    exact measurable_pairMeasureRadonModification.comp
      ((hZc.1 (projectiveSHFPairStart j) hs (projectiveSHFPairEnd j) ht
        ((j : SHFTimePair).property.2)).1)
  have hradJlaw : P.map radJ = Pc.map radJc := by
    calc
      P.map radJ = (P.map (fun ω i => pairMeasureRadonModification (ZFin i ω))).map R := by
        rw [Measure.map_map hR hradFinMeas]
        congr 1
        funext ω j
        simp [R, radJ, s, t, ZFin]
      _ = (Pc.map (fun ω i => pairMeasureRadonModification (ZcFin i ω))).map R := by
        rw [hradFin]
      _ = Pc.map radJc := by
        rw [Measure.map_map hR hradFinMeasC]
        congr 1
        funext ω j
        simp [R, radJc, s, t, ZcFin]
  have hradProb :
      ProbabilityMeasure.map ⟨P, inferInstance⟩ radJ =
        ProbabilityMeasure.map ⟨Pc, hPc⟩ radJc := by
    apply Subtype.ext
    exact hradJlaw
  exact hdataCommon.trans hradProb.symm

end Critical2DKPZ.SHF.Existence

end
