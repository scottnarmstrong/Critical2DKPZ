/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Limit.SubseqLimit

/-! # Countable-time subsequential limits of polymer random measures -/

@[expose] public section

open MeasureTheory Filter TopologicalSpace
open scoped CompactlySupported Topology

noncomputable section

set_option linter.style.haveILetI false

namespace Critical2DKPZ.SHF.Limit

private def polymerPairIndexOfProof {D : Set ℝ} {s t : ℝ}
    (h : s ∈ D ∧ t ∈ D ∧ s < t) : PolymerPairIndex D :=
  ⟨(⟨s, h.1⟩, ⟨t, h.2.1⟩), h.2.2⟩

private def polymerSubseqLimitMeasure (D : Set ℝ)
    (m : PolymerPairIndex D →
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure))
    (s t : ℝ) : Measure (Plane × Plane) := by
  classical
  exact if h : s ∈ D ∧ t ∈ D ∧ s < t then
    (m (polymerPairIndexOfProof h)).1.1 else 0

private theorem measurable_polymerSubseqLimitMeasure (D : Set ℝ)
    (s t : ℝ) :
    letI : TopologicalSpace RandomMeasure.PlanePairRadonMeasure :=
      RandomMeasure.vagueTopology (Plane × Plane)
    letI : BorelSpace RandomMeasure.PlanePairRadonMeasure :=
      ⟨RandomMeasure.borel_positiveRadonMeasure_eq_comap.symm⟩
    letI : TopologicalSpace RandomMeasure.PlaneRadonMeasure :=
      RandomMeasure.vagueTopology Plane
    letI : BorelSpace RandomMeasure.PlaneRadonMeasure :=
      ⟨RandomMeasure.eval_eq_vague_borel⟩
    letI : BorelSpace
        (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) := inferInstance
    Measurable (fun m : PolymerPairIndex D →
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) =>
        polymerSubseqLimitMeasure D m s t) := by
  classical
  letI : TopologicalSpace RandomMeasure.PlanePairRadonMeasure :=
    RandomMeasure.vagueTopology (Plane × Plane)
  letI : BorelSpace RandomMeasure.PlanePairRadonMeasure :=
    ⟨RandomMeasure.borel_positiveRadonMeasure_eq_comap.symm⟩
  letI : TopologicalSpace RandomMeasure.PlaneRadonMeasure :=
    RandomMeasure.vagueTopology Plane
  letI : BorelSpace RandomMeasure.PlaneRadonMeasure :=
    ⟨RandomMeasure.eval_eq_vague_borel⟩
  letI : BorelSpace
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) := inferInstance
  by_cases h : s ∈ D ∧ t ∈ D ∧ s < t
  · simp only [polymerSubseqLimitMeasure, dite_eq_left h]
    have hEval : Measurable (fun m : PolymerPairIndex D →
        (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) =>
        m (polymerPairIndexOfProof h)) :=
      measurable_pi_apply (polymerPairIndexOfProof h)
    have hfst : @Measurable
        (PolymerPairIndex D →
          (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure))
        RandomMeasure.PlanePairRadonMeasure inferInstance
        (@borel _ (RandomMeasure.vagueTopology (Plane × Plane)))
        (fun m => (m (polymerPairIndexOfProof h)).1) := by
      rw [RandomMeasure.borel_positiveRadonMeasure_eq_comap]
      rw [measurable_comap_iff]
      exact measurable_subtype_coe.comp (measurable_fst.comp hEval)
    exact RandomMeasure.measurable_coe_positiveRadonMeasure.comp hfst
  · simp only [polymerSubseqLimitMeasure, dite_eq_right h]
    exact measurable_const

private def polymerSubseqIndexOfTimes {D : Set ℝ} {k : ℕ}
    (s t : Fin k → ℝ) (hTimes : ∀ i, s i ∈ D ∧ t i ∈ D ∧ s i < t i)
    (i : Fin k) : PolymerPairIndex D :=
  polymerPairIndexOfProof (hTimes i)

private def polymerPairMarginalCompactFlatReadout {D : Set ℝ} {k : ℕ}
    (s t : Fin k → ℝ) (hTimes : ∀ i, s i ∈ D ∧ t i ∈ D ∧ s i < t i)
    (φ : Fin k → C_c(Plane × Plane, ℝ)) (χ : Fin k → C_c(Plane, ℝ)) :
    (PolymerPairIndex D →
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure)) →
      Fin k → ℝ × ℝ := fun m i =>
        (RandomMeasure.vaguePairing
          (m (polymerSubseqIndexOfTimes s t hTimes i)).1 (φ i),
         RandomMeasure.vaguePairing
          (m (polymerSubseqIndexOfTimes s t hTimes i)).2 (χ i))

private theorem continuous_polymerPairMarginalCompactFlatReadout {D : Set ℝ} {k : ℕ}
    (s t : Fin k → ℝ) (hTimes : ∀ i, s i ∈ D ∧ t i ∈ D ∧ s i < t i)
    (φ : Fin k → C_c(Plane × Plane, ℝ)) (χ : Fin k → C_c(Plane, ℝ)) :
    letI : TopologicalSpace RandomMeasure.PlanePairRadonMeasure :=
      RandomMeasure.vagueTopology (Plane × Plane)
    letI : TopologicalSpace RandomMeasure.PlaneRadonMeasure :=
      RandomMeasure.vagueTopology Plane
    letI : TopologicalSpace
        (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) := inferInstance
    letI : ∀ _i : PolymerPairIndex D, TopologicalSpace
        (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) :=
      fun _ => inferInstance
    letI : TopologicalSpace (PolymerPairIndex D →
        (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure)) :=
      Pi.topologicalSpace
    Continuous (polymerPairMarginalCompactFlatReadout s t hTimes φ χ) := by
  letI : TopologicalSpace RandomMeasure.PlanePairRadonMeasure :=
    RandomMeasure.vagueTopology (Plane × Plane)
  letI : TopologicalSpace RandomMeasure.PlaneRadonMeasure :=
    RandomMeasure.vagueTopology Plane
  letI : TopologicalSpace
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) := inferInstance
  letI : ∀ _i : PolymerPairIndex D, TopologicalSpace
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) :=
    fun _ => inferInstance
  letI : TopologicalSpace (PolymerPairIndex D →
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure)) :=
    Pi.topologicalSpace
  apply continuous_pi
  intro i
  let j := polymerSubseqIndexOfTimes s t hTimes i
  have heval : Continuous (fun m : PolymerPairIndex D →
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) => m j) :=
    continuous_apply j
  exact ((RandomMeasure.continuous_vaguePairing (φ i)).comp
      (continuous_fst.comp heval)).prodMk
    ((RandomMeasure.continuous_vaguePairing (χ i)).comp
      (continuous_snd.comp heval))

/-- On any countable set of nonnegative times, every subsequence of lattice scales has a further subsequence along which compact and flat polymer pairings converge jointly in law. -/
theorem exists_polymerSubseqLimit (ϑ : ℝ) (D : Set ℝ) (hD : D.Countable)
    (hD0 : ∀ s ∈ D, 0 ≤ s) (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (_ : IsProbabilityMeasure P) (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)),
      IsPolymerSubseqLimit ϑ D (φ ∘ ψ) P Z := by
  letI : TopologicalSpace RandomMeasure.PlanePairRadonMeasure :=
    RandomMeasure.vagueTopology (Plane × Plane)
  letI : PolishSpace RandomMeasure.PlanePairRadonMeasure :=
    RandomMeasure.polishSpace_positiveRadonMeasure_planePair
  letI : BorelSpace RandomMeasure.PlanePairRadonMeasure :=
    ⟨RandomMeasure.borel_positiveRadonMeasure_eq_comap.symm⟩
  letI : OpensMeasurableSpace RandomMeasure.PlanePairRadonMeasure :=
    ⟨RandomMeasure.borel_positiveRadonMeasure_eq_comap.le⟩
  letI : TopologicalSpace RandomMeasure.PlaneRadonMeasure :=
    RandomMeasure.vagueTopology Plane
  letI : PolishSpace RandomMeasure.PlaneRadonMeasure := RandomMeasure.vaguePolishSpace
  letI : BorelSpace RandomMeasure.PlaneRadonMeasure :=
    ⟨RandomMeasure.eval_eq_vague_borel⟩
  letI : OpensMeasurableSpace RandomMeasure.PlaneRadonMeasure :=
    ⟨RandomMeasure.eval_eq_vague_borel.symm.le⟩
  letI : PolishSpace
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) := inferInstance
  letI : BorelSpace
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) := inferInstance
  letI : OpensMeasurableSpace
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) := inferInstance
  letI : Countable D := hD.to_subtype
  letI : Countable (D × D) := inferInstance
  letI : Countable (PolymerPairIndex D) := inferInstance
  letI : TopologicalSpace (PolymerPairIndex D →
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure)) :=
    Pi.topologicalSpace
  letI : MeasurableSpace (PolymerPairIndex D →
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure)) := inferInstance
  letI : PolishSpace (PolymerPairIndex D →
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure)) := inferInstance
  letI : BorelSpace (PolymerPairIndex D →
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure)) := inferInstance
  letI : OpensMeasurableSpace (PolymerPairIndex D →
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure)) := inferInstance
  obtain ⟨ψ, hψ, hφψ, Q, hweak⟩ :=
    exists_subseq_tendsto_polymerPairMarginalRadonProcessLaw ϑ D hD φ hφ
  let Ω := PolymerPairIndex D →
    (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure)
  let P : Measure Ω := (Q : Measure Ω)
  let Z : ℝ → ℝ → Ω → Measure (Plane × Plane) := fun s t m =>
    polymerSubseqLimitMeasure D m s t
  refine ⟨ψ, hψ, Ω, inferInstance, P, inferInstance, Z, ?_⟩
  unfold IsPolymerSubseqLimit
  constructor
  · intro s hs t ht hst
    constructor
    · exact measurable_polymerSubseqLimitMeasure D s t
    ·
      let i : PolymerPairIndex D := polymerPairIndexOfProof ⟨hs, ht, hst⟩
      have hcoordWeak : Tendsto
          (fun n => polymerPairMarginalCoordinateLaw ϑ (φ (ψ n)) D i)
          atTop (𝓝 ((Q.map (fun m => m i)))) := by
        have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
          (fun n => polymerPairMarginalRadonProcessLaw ϑ (φ (ψ n)) D)
          Q hweak (continuous_apply i)
        exact Tendsto.congr' (Filter.Eventually.of_forall fun n => rfl) hmap
      have hZ (m : Ω) : Z s t m = ((m i).1.1 : Measure (Plane × Plane)) := by
        simp [Z, polymerSubseqLimitMeasure, i, polymerPairIndexOfProof, hs, ht, hst]
      have hpairLF : ∀ᵐ m ∂P, IsLocallyFiniteMeasure (Z s t m) := by
        filter_upwards [] with m
        rw [hZ m]
        exact (m i).1.2
      have hprojLF : ∀ᵐ m ∂P, IsLocallyFiniteMeasure
          ((Z s t m).map Prod.fst) := by
        have hlocal := ae_polymerPairMarginal_projection_locallyFinite
          ϑ D hD0 i (φ ∘ ψ) hφψ (Q.map fun m => m i) hcoordWeak
        have hpull : ∀ᵐ m ∂P, IsLocallyFiniteMeasure
            (Measure.map Prod.fst (((m i).1.1 : Measure (Plane × Plane)))) :=
          (Measure.tendsto_ae_map (continuous_apply i).aemeasurable).eventually hlocal
        filter_upwards [hpull] with m hm
        rw [hZ m]
        exact hm
      exact hpairLF.and hprojLF
  · intro k s t hTimes φs χs
    let F : Ω → Fin k → ℝ × ℝ :=
      polymerPairMarginalCompactFlatReadout s t hTimes φs χs
    let H : Ω → Fin k → ℝ × ℝ := fun m i =>
      ((∫ p, φs i p ∂Z (s i) (t i) m),
       ∫ x, χs i x ∂((Z (s i) (t i) m).map Prod.fst))
    have hFcont : Continuous F :=
      continuous_polymerPairMarginalCompactFlatReadout s t hTimes φs χs
    have hFmeas : Measurable F := hFcont.measurable
    let N : ℕ → ℕ := fun n => φ (ψ n)
    let sourceReadout : ℕ → Disorder → Fin k → ℝ × ℝ := fun n ω i =>
      ((∫ p, φs i p ∂polymerMeasure ϑ (N n) (s i) (t i) ω),
       ∫ x, χs i x ∂((polymerMeasure ϑ (N n) (s i) (t i) ω).map Prod.fst))
    have hProcessMeas (n : ℕ) : Measurable (polymerPairMarginalRadonProcess
        ϑ (N n) D) := by
      apply measurable_pi_iff.mpr
      intro i
      exact measurable_polymerPairMarginalRadonMeasure ϑ (N n)
        (i.1.1 : ℝ) (i.1.2 : ℝ)
    have hsourceEq (n : ℕ) : sourceReadout n = fun ω =>
        F (polymerPairMarginalRadonProcess ϑ (N n) D ω) := by
      funext ω i
      simp [sourceReadout, F, polymerPairMarginalCompactFlatReadout,
        polymerSubseqIndexOfTimes, polymerPairIndexOfProof,
        polymerPairMarginalRadonProcess, polymerPairMarginalRadonMeasure,
        polymerRadonMeasure, polymerMarginalRadonMeasure,
        RandomMeasure.vaguePairing]
    have hsourceMeas (n : ℕ) : Measurable (sourceReadout n) := by
      rw [hsourceEq n]
      exact hFmeas.comp (hProcessMeas n)
    have hprobEq (n : ℕ) :
        polymerDisorderProbability.map (sourceReadout n) =
          (polymerPairMarginalRadonProcessLaw ϑ (N n) D).map F := by
      apply Subtype.ext
      calc
        Measure.map (sourceReadout n) disorderLaw =
            Measure.map (fun ω => F (polymerPairMarginalRadonProcess ϑ (N n) D ω))
              disorderLaw := by
                apply Measure.map_congr
                exact Filter.Eventually.of_forall fun ω => congrFun (hsourceEq n) ω
        _ = Measure.map F
            (Measure.map (polymerPairMarginalRadonProcess ϑ (N n) D) disorderLaw) :=
              (Measure.map_map hFmeas (hProcessMeas n)).symm
    have hweakMap : Tendsto
        (fun n => (polymerPairMarginalRadonProcessLaw ϑ (N n) D).map F)
        atTop (𝓝 (Q.map F)) :=
      ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
        (fun n => polymerPairMarginalRadonProcessLaw ϑ (N n) D) Q hweak hFcont
    have htargetEqCoord (i : Fin k) : ∀ᵐ m ∂P,
        F m i = H m i := by
      let j := polymerSubseqIndexOfTimes s t hTimes i
      have hcoordWeak : Tendsto
          (fun n => polymerPairMarginalCoordinateLaw ϑ (N n) D j)
          atTop (𝓝 (Q.map fun m => m j)) := by
        have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
          (fun n => polymerPairMarginalRadonProcessLaw ϑ (N n) D)
          Q hweak (continuous_apply j)
        exact Tendsto.congr' (Filter.Eventually.of_forall fun n => rfl) hmap
      have hflat := ae_polymerPairMarginal_pairing_eq_projection
        ϑ D hD0 j (φ ∘ ψ) hφψ (Q.map fun m => m j) (χs i) hcoordWeak
      have hpull : ∀ᵐ m ∂P,
          polymerFlatPairing (χs i) (m j) =
            ∫ x, χs i x ∂Measure.map Prod.fst (((m j).1.1 : Measure (Plane × Plane))) :=
        (Measure.tendsto_ae_map (continuous_apply j).aemeasurable).eventually hflat
      filter_upwards [hpull] with m hm
      change
        (RandomMeasure.vaguePairing (m j).1 (φs i),
          RandomMeasure.vaguePairing (m j).2 (χs i)) =
        ((∫ p, φs i p ∂Z (s i) (t i) m),
          ∫ x, χs i x ∂((Z (s i) (t i) m).map Prod.fst))
      have hZ : Z (s i) (t i) m = ((m j).1.1 : Measure (Plane × Plane)) := by
        simp [Z, polymerSubseqLimitMeasure, j, polymerSubseqIndexOfTimes,
          polymerPairIndexOfProof, hTimes i]
      rw [hZ]
      refine Prod.ext ?_ ?_
      · rfl
      · simpa [polymerFlatPairing] using hm
    have htargetEq : F =ᵐ[P] H := by
      filter_upwards [ae_all_iff.mpr htargetEqCoord] with m hm
      funext i
      exact hm i
    have hHae : AEMeasurable H P := hFmeas.aemeasurable.congr htargetEq
    have hmapEq : Q.map F = Q.map H := by
      apply Subtype.ext
      exact Measure.map_congr htargetEq
    have hweakTarget : Tendsto
        (fun n => (polymerPairMarginalRadonProcessLaw ϑ (N n) D).map F)
        atTop (𝓝 (Q.map H)) := by
      simpa [hmapEq] using hweakMap
    refine {
      forall_aemeasurable := fun n => (hsourceMeas n).aemeasurable
      aemeasurable_limit := hHae
      tendsto := ?_ }
    exact Tendsto.congr' (Filter.Eventually.of_forall fun n => (hprobEq n).symm)
      hweakTarget

end Critical2DKPZ.SHF.Limit

end
