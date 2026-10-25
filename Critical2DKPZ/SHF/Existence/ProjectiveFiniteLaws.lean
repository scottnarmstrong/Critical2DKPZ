/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Existence.ProjectiveLawSupport
public import Critical2DKPZ.RandomMeasure.PlanePairInterface

/-! # Finite laws for the Kolmogorov construction -/

@[expose] public section

open MeasureTheory
open Critical2DKPZ.SHF.Limit

noncomputable section

namespace Critical2DKPZ.SHF.Existence

/-- The index of one strict nonnegative time pair. -/
abbrev SHFTimePair := {p : ℝ × ℝ // 0 ≤ p.1 ∧ p.1 < p.2}

/-- The start time of a SHF existence coordinate. -/
def projectiveSHFPairStart (i : SHFTimePair) : ℝ := i.1.1

/-- The end time of a SHF existence coordinate. -/
def projectiveSHFPairEnd (i : SHFTimePair) : ℝ := i.1.2

/-- One countable-time subsequential limit whose time set includes a given
finite family of pair endpoints. -/
structure FiniteSHFSubsequenceLimit (ϑ : ℝ) (J : Finset SHFTimePair) where
  B : ℝ
  hB : 0 < B
  D : Set ℝ
  hD : D.Countable
  hDB : D ⊆ Set.Icc 0 B
  hdense : Set.Icc 0 B ⊆ closure D
  htimes : ∀ j : J, projectiveSHFPairStart j ∈ D ∧ projectiveSHFPairEnd j ∈ D
  ψ : ℕ → ℕ
  hψ : StrictMono ψ
  Ω : Type
  mΩ : MeasurableSpace Ω
  P : Measure Ω
  hP : IsProbabilityMeasure P
  Z : ℝ → ℝ → Ω → Measure (Plane × Plane)
  hZ : @IsPolymerSubseqLimit ϑ D ψ Ω mΩ P hP Z

/-- For each finite collection of time pairs, there is a subsequential polymer limit on a bounded countable dense time window containing their endpoints. -/
theorem exists_finiteSHFSubsequenceLimit (ϑ : ℝ) (J : Finset SHFTimePair) :
    Nonempty (FiniteSHFSubsequenceLimit ϑ J) := by
  classical
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let s : Fin (Fintype.card J) → ℝ := fun i => projectiveSHFPairStart (e.symm i)
  let t : Fin (Fintype.card J) → ℝ := fun i => projectiveSHFPairEnd (e.symm i)
  have hTimes : ∀ i, 0 ≤ s i ∧ s i < t i := by
    intro i
    simpa [s, t, projectiveSHFPairStart, projectiveSHFPairEnd] using (e.symm i).val.property
  obtain ⟨B, hB, D, hD, hDB, hdense, htimesFin⟩ :=
    exists_countable_dense_interval_with_finite_times s t hTimes
  have hD0 : ∀ r ∈ D, 0 ≤ r := fun r hr => (hDB hr).1
  obtain ⟨ψ, hψ, Ω, mΩ, P, hP, Z, hZ⟩ :=
    exists_polymerSubseqLimit ϑ D hD hD0 (fun n => n) strictMono_id
  let ψ' := (fun n : ℕ => n) ∘ ψ
  have hψ' : StrictMono ψ' := strictMono_id.comp hψ
  refine ⟨⟨B, hB, D, hD, hDB, hdense, ?_, ψ', hψ', Ω, mΩ, P, hP, Z, hZ⟩⟩
  intro j
  have h := htimesFin (e j)
  simpa [s, t] using h

/-- A chosen finite-limit datum for `J`, from `exists_finiteSHFSubsequenceLimit`. -/
noncomputable def finiteSHFSubsequenceLimit (ϑ : ℝ) (J : Finset SHFTimePair) :
    FiniteSHFSubsequenceLimit ϑ J :=
  Classical.choice (exists_finiteSHFSubsequenceLimit ϑ J)

/-- The state space of the pair-measure fields: Radon measures on `Plane × Plane`. -/
abbrev SHFPairRadonMeasure := Critical2DKPZ.RandomMeasure.PlanePairRadonMeasure

/-- The canonical Radon-valued modification of a pair measure. -/
noncomputable def pairMeasureRadonModification (μ : Measure (Plane × Plane)) : SHFPairRadonMeasure :=
  Critical2DKPZ.RandomMeasure.radonValuedModification
    (Critical2DKPZ.RandomMeasure.vagueCompactExhaustion (Plane × Plane)) id μ

/-- Coordinatewise Radonification of a finite family of pair measures. -/
def pairMeasureVectorRadonModification {J : Finset SHFTimePair} :
    (J → Measure (Plane × Plane)) → J → SHFPairRadonMeasure := fun μ j =>
      pairMeasureRadonModification (μ j)

/-- The finite law obtained by replacing each locally finite subsequential
limit coordinate by its canonical Radon-valued modification. -/
noncomputable def finiteSHFRadonLawOfSubsequenceLimit (ϑ : ℝ) (J : Finset SHFTimePair)
    (d : FiniteSHFSubsequenceLimit ϑ J) : ProbabilityMeasure (J → SHFPairRadonMeasure) := by
  classical
  letI : MeasurableSpace d.Ω := d.mΩ
  letI : IsProbabilityMeasure d.P := d.hP
  let F : d.Ω → J → SHFPairRadonMeasure := fun ω j =>
    pairMeasureRadonModification (d.Z (projectiveSHFPairStart j) (projectiveSHFPairEnd j) ω)
  exact MeasureTheory.ProbabilityMeasure.map
    (⟨d.P, d.hP⟩ : MeasureTheory.ProbabilityMeasure d.Ω) F

/-- The chosen finite law obtained from the subsequential limit on the
window assigned to `J`. -/
noncomputable def projectiveSHFFiniteRadonLaw (ϑ : ℝ) (J : Finset SHFTimePair) :
    ProbabilityMeasure (J → SHFPairRadonMeasure) := by
  exact finiteSHFRadonLawOfSubsequenceLimit ϑ J (finiteSHFSubsequenceLimit ϑ J)

end Critical2DKPZ.SHF.Existence

end
