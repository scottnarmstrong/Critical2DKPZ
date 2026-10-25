/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.RandomMeasure.GeneralDetermination
public import Critical2DKPZ.RandomMeasure.GeneralRandom
public import Critical2DKPZ.RandomMeasure.GeneralProduct
public import Mathlib.MeasureTheory.Measure.Regular

/-! Positive locally finite Borel measures on `ℝ² × ℝ²` form a Polish vague space, and joint laws of finite families of such random measures are determined by joint compact-test pairing laws. -/

public section

open MeasureTheory Filter TopologicalSpace
open scoped CompactlySupported Topology

set_option linter.style.haveILetI false

noncomputable section

namespace Critical2DKPZ.RandomMeasure

/-- Positive locally finite Borel measures on `ℝ² × ℝ²` form a Polish space in the vague topology. -/
theorem polishSpace_positiveRadonMeasure_planePair :
    PolishSpace PlanePairRadonMeasure := by
  exact vaguePolishSpace

/-- The vague Borel σ-algebra for measures on `ℝ² × ℝ²` is their measure-evaluation σ-algebra. -/
theorem borel_positiveRadonMeasure_eq_comap :
    @borel PlanePairRadonMeasure inferInstance =
      MeasurableSpace.comap
        (fun μ : PlanePairRadonMeasure => (μ.1 : Measure
          (Critical2DKPZ.Plane × Critical2DKPZ.Plane))) inferInstance := by
  simp only [PlanePairRadonMeasure, eval_eq_vague_borel]

/-- For the vague Borel structure, the map sending a locally finite measure on `ℝ² × ℝ²` to its underlying measure is measurable. -/
theorem measurable_coe_positiveRadonMeasure :
    @Measurable PlanePairRadonMeasure
      (Measure (Critical2DKPZ.Plane × Critical2DKPZ.Plane))
      (@borel _ (vagueTopology
        (Critical2DKPZ.Plane × Critical2DKPZ.Plane))) inferInstance
      (fun μ : PlanePairRadonMeasure =>
      (μ.1 : Measure (Critical2DKPZ.Plane × Critical2DKPZ.Plane))) := by
  rw [← eval_eq_vague_borel
    (X := Critical2DKPZ.Plane × Critical2DKPZ.Plane)]
  exact measurable_subtype_coe




/-- Two finite families of measurable, almost surely locally finite measures on `ℝ² × ℝ²` have the same joint law if all finite joint compact-test pairing laws agree. -/
theorem map_eq_of_pairing_laws {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P'] (k : ℕ)
    (Z : Fin k → Ω → Measure
      (Critical2DKPZ.Plane × Critical2DKPZ.Plane))
    (Z' : Fin k → Ω' → Measure
      (Critical2DKPZ.Plane × Critical2DKPZ.Plane))
    (hZ : ∀ i, Measurable (Z i)) (hZ' : ∀ i, Measurable (Z' i))
    (hlf : ∀ᵐ ω ∂P, ∀ i, IsLocallyFiniteMeasure (Z i ω))
    (hlf' : ∀ᵐ ω ∂P', ∀ i, IsLocallyFiniteMeasure (Z' i ω))
    (h : ∀ (m : ℕ) (f : Fin m → Fin k ×
      C_c(Critical2DKPZ.Plane × Critical2DKPZ.Plane, ℝ)),
      P.map (fun ω j => ∫ p, (f j).2 p ∂(Z (f j).1 ω)) =
        P'.map (fun ω j => ∫ p, (f j).2 p ∂(Z' (f j).1 ω))) :
    P.map (fun ω i => Z i ω) = P'.map (fun ω i => Z' i ω) := by
  let X := Critical2DKPZ.Plane × Critical2DKPZ.Plane
  let K : CompactExhaustion X := vagueCompactExhaustion X
  let F : Ω → Fin k → PositiveRadonMeasure X := fun ω i =>
    radonValuedModification K (Z i) ω
  let F' : Ω' → Fin k → PositiveRadonMeasure X := fun ω i =>
    radonValuedModification K (Z' i) ω
  have hF : Measurable F := by
    apply measurable_pi_iff.mpr
    intro i
    have hi := measurable_radonValuedModification K (Z i) (hZ i)
    rw [← eval_eq_vague_borel (X := X)] at hi
    exact hi
  have hF' : Measurable F' := by
    apply measurable_pi_iff.mpr
    intro i
    have hi := measurable_radonValuedModification K (Z' i) (hZ' i)
    rw [← eval_eq_vague_borel (X := X)] at hi
    exact hi
  have hZvec : Measurable (fun ω i => Z i ω) :=
    measurable_pi_iff.mpr fun i => hZ i
  have hZ'vec : Measurable (fun ω i => Z' i ω) :=
    measurable_pi_iff.mpr fun i => hZ' i
  let PP : ProbabilityMeasure Ω := ⟨P, inferInstance⟩
  let PP' : ProbabilityMeasure Ω' := ⟨P', inferInstance⟩
  let PF : ProbabilityMeasure (Fin k → PositiveRadonMeasure X) := PP.map F
  let PF' : ProbabilityMeasure (Fin k → PositiveRadonMeasure X) := PP'.map F'
  have hfinite : ∀ s : Finset (Fin k × ((ℕ × ℕ) ⊕ ℕ)),
      Measure.map (fun μ : Fin k → PositiveRadonMeasure X =>
        fun p : s => vagueProductReadoutFlat K μ p.1)
          (PF : Measure _) =
        Measure.map (fun μ : Fin k → PositiveRadonMeasure X =>
        fun p : s => vagueProductReadoutFlat K μ p.1)
          (PF' : Measure _) := by
    intro s
    let e : Fin s.card ≃ s := s.equivFin.symm
    let f : Fin s.card → Fin k × C_c(X, ℝ) := fun j =>
      ((e j).1.1, countableVagueTest K (e j).1.2)
    let q : (Fin k → PositiveRadonMeasure X) → Fin s.card → ℝ :=
      fun μ j => vaguePairing (μ (f j).1) (f j).2
    let q' : (Fin k → PositiveRadonMeasure X) → Fin s.card → ℝ :=
      fun μ j => vaguePairing (μ (f j).1) (f j).2
    let T : (Fin k → PositiveRadonMeasure X) → s → ℝ :=
      fun μ p => vagueProductReadoutFlat K μ p.1
    let E : MeasurableEquiv (Fin s.card → ℝ) (s → ℝ) :=
      MeasurableEquiv.piCongrLeft (fun _ : s => ℝ) e
    have hE_apply (x : Fin s.card → ℝ) (p : s) : E x p = x (e.symm p) := by
      change (Equiv.piCongrLeft (fun _ : s => ℝ) e) x p = _
      rw [Equiv.piCongrLeft_apply]
      simp
    have hq : Measurable q := by
      apply measurable_pi_iff.mpr
      intro j
      exact (measurable_vaguePairing_eval (f j).2).comp
        (measurable_pi_apply (f j).1)
    have hq' : Measurable q' := hq
    have hT : Measurable T := by
      apply measurable_pi_iff.mpr
      intro p
      exact (measurable_vaguePairing_eval
        (countableVagueTest K p.1.2)).comp
        (measurable_pi_apply p.1.1)
    have hT' : Measurable T := hT
    have hpairAE_coord (j : Fin s.card) :
        (fun ω => vaguePairing (F ω (f j).1) (f j).2) =ᵐ[P]
          (fun ω => ∫ p, (f j).2 p ∂(Z (f j).1 ω)) := by
      have hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (Z (f j).1 ω) :=
        hlf.mono fun ω hω => hω (f j).1
      have hmod := ae_eq_radonValuedModification K P (Z (f j).1) hloc
      filter_upwards [hmod] with ω hω
      change (F ω (f j).1 : Measure X) = Z (f j).1 ω at hω
      have hp := congrArg (fun μ : Measure X => ∫ p, (f j).2 p ∂μ) hω
      simpa [vaguePairing] using hp
    have hpairAE : (q ∘ F) =ᵐ[P] (fun ω j =>
        ∫ p, (f j).2 p ∂(Z (f j).1 ω)) := by
      filter_upwards [ae_all_iff.mpr hpairAE_coord] with ω hω
      funext j
      exact hω j
    have hpairAE'_coord (j : Fin s.card) :
        (fun ω => vaguePairing (F' ω (f j).1) (f j).2) =ᵐ[P']
          (fun ω => ∫ p, (f j).2 p ∂(Z' (f j).1 ω)) := by
      have hloc : ∀ᵐ ω ∂P', IsLocallyFiniteMeasure (Z' (f j).1 ω) :=
        hlf'.mono fun ω hω => hω (f j).1
      have hmod := ae_eq_radonValuedModification K P' (Z' (f j).1) hloc
      filter_upwards [hmod] with ω hω
      change (F' ω (f j).1 : Measure X) = Z' (f j).1 ω at hω
      have hp := congrArg (fun μ : Measure X => ∫ p, (f j).2 p ∂μ) hω
      simpa [vaguePairing] using hp
    have hpairAE' : (q' ∘ F') =ᵐ[P'] (fun ω j =>
        ∫ p, (f j).2 p ∂(Z' (f j).1 ω)) := by
      filter_upwards [ae_all_iff.mpr hpairAE'_coord] with ω hω
      funext j
      exact hω j
    have hpair : Measure.map (q ∘ F) P = Measure.map (q' ∘ F') P' := by
      calc
        Measure.map (q ∘ F) P =
            Measure.map (fun ω j => ∫ p, (f j).2 p ∂(Z (f j).1 ω)) P :=
          Measure.map_congr hpairAE
        _ = Measure.map (fun ω j => ∫ p, (f j).2 p ∂(Z' (f j).1 ω)) P' := h s.card f
        _ = Measure.map (q' ∘ F') P' := (Measure.map_congr hpairAE').symm
    have hcomp : T ∘ F = E ∘ (q ∘ F) := by
      funext ω p
      change T (F ω) p = E (q (F ω)) p
      rw [hE_apply]
      simp [T, q, f, e, vagueProductReadoutFlat, countableVagueReadout]
    have hcomp' : T ∘ F' = E ∘ (q' ∘ F') := by
      funext ω p
      change T (F' ω) p = E (q' (F' ω)) p
      rw [hE_apply]
      simp [T, q', f, e, vagueProductReadoutFlat, countableVagueReadout]
    have hmapT : Measure.map T (PF : Measure _) =
        Measure.map E (Measure.map (q ∘ F) P) := by
      change Measure.map T ((P : Measure Ω).map F) =
        Measure.map E (Measure.map (q ∘ F) P)
      rw [Measure.map_map hT hF,
        Measure.map_map E.measurable (hq.comp hF)]
      rw [hcomp]
    have hmapT' : Measure.map T (PF' : Measure _) =
        Measure.map E (Measure.map (q' ∘ F') P') := by
      change Measure.map T ((P' : Measure Ω').map F') =
        Measure.map E (Measure.map (q' ∘ F') P')
      rw [Measure.map_map hT' hF',
        Measure.map_map E.measurable (hq'.comp hF')]
      rw [hcomp']
    have hmapE := congrArg (fun m : Measure (Fin s.card → ℝ) =>
      Measure.map E m) hpair
    change Measure.map T (PF : Measure _) =
      Measure.map T (PF' : Measure _) at ⊢
    calc
      Measure.map T (PF : Measure _) =
          Measure.map E (Measure.map (q ∘ F) P) := hmapT
      _ = Measure.map E (Measure.map (q' ∘ F') P') := hmapE
      _ = Measure.map T (PF' : Measure _) := hmapT'.symm
  have hPF : PF = PF' :=
    probabilityMeasure_eq_of_finite_vagueProductReadoutLaws K PF PF' hfinite
  let C : (Fin k → PositiveRadonMeasure X) → (Fin k → Measure X) :=
    fun μ i => μ i
  have hC : Measurable C := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_subtype_coe.comp (measurable_pi_apply i)
  have hmodAE_coord (i : Fin k) :
      (fun ω => Z i ω) =ᵐ[P] (fun ω => (F ω i : Measure X)) := by
    have hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (Z i ω) :=
      hlf.mono fun ω hω => hω i
    exact (ae_eq_radonValuedModification K P (Z i) hloc).symm
  have hmodAE : (fun ω i => Z i ω) =ᵐ[P] (C ∘ F) := by
    filter_upwards [ae_all_iff.mpr hmodAE_coord] with ω hω
    funext i
    exact hω i
  have hmodAE'_coord (i : Fin k) :
      (fun ω => Z' i ω) =ᵐ[P'] (fun ω => (F' ω i : Measure X)) := by
    have hloc : ∀ᵐ ω ∂P', IsLocallyFiniteMeasure (Z' i ω) :=
      hlf'.mono fun ω hω => hω i
    exact (ae_eq_radonValuedModification K P' (Z' i) hloc).symm
  have hmodAE' : (fun ω i => Z' i ω) =ᵐ[P'] (C ∘ F') := by
    filter_upwards [ae_all_iff.mpr hmodAE'_coord] with ω hω
    funext i
    exact hω i
  have hPFmeas : (PF : Measure (Fin k → PositiveRadonMeasure X)) =
      (PF' : Measure (Fin k → PositiveRadonMeasure X)) := congrArg Subtype.val hPF
  calc
    Measure.map (fun ω i => Z i ω) P = Measure.map (C ∘ F) P :=
      Measure.map_congr hmodAE
    _ = (PF : Measure (Fin k → PositiveRadonMeasure X)).map C := by
      change Measure.map (C ∘ F) P =
        ((P : Measure Ω).map F).map C
      exact (Measure.map_map hC hF).symm
    _ = (PF' : Measure (Fin k → PositiveRadonMeasure X)).map C :=
      congrArg (fun m : Measure (Fin k → PositiveRadonMeasure X) => m.map C) hPFmeas
    _ = Measure.map (C ∘ F') P' := by
      change ((P' : Measure Ω').map F').map C = Measure.map (C ∘ F') P'
      exact Measure.map_map hC hF'
    _ = Measure.map (fun ω i => Z' i ω) P' := (Measure.map_congr hmodAE').symm

end Critical2DKPZ.RandomMeasure

end
