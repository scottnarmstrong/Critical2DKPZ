/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Limit.Tightness
public import Critical2DKPZ.RandomMeasure.GeneralTightness
import Mathlib.MeasureTheory.Measure.Tight

/-! # Joint tightness of polymer measures and their first marginals -/

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal CompactlySupported Topology

noncomputable section

set_option linter.style.haveILetI false

namespace Critical2DKPZ.SHF.Limit

/-- The first marginal of a finite-scale polymer measure, as a Radon measure. -/
noncomputable def polymerMarginalRadonMeasure (ϑ : ℝ) (N : ℕ) (s t : ℝ)
    (ω : Disorder) : RandomMeasure.PlaneRadonMeasure :=
  ⟨(polymerMeasure ϑ N s t ω).map Prod.fst,
    isLocallyFiniteMeasure_polymerMarginal ϑ N s t ω⟩

/-- The first-marginal Radon measure is measurable in the disorder. -/
theorem measurable_polymerMarginalRadonMeasure (ϑ : ℝ) (N : ℕ) (s t : ℝ) :
    @Measurable Disorder RandomMeasure.PlaneRadonMeasure inferInstance
      (MeasurableSpace.comap Subtype.val inferInstance)
      (fun ω => polymerMarginalRadonMeasure ϑ N s t ω) := by
  have hmap : Measurable (fun ω : Disorder =>
      (polymerMeasure ϑ N s t ω).map Prod.fst) := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    have hval : Measurable (fun ω : Disorder =>
        polymerMeasure ϑ N s t ω (Prod.fst ⁻¹' A)) :=
      (Measure.measurable_coe (hA.preimage measurable_fst)).comp
        (measurable_polymerMeasure ϑ N s t)
    have hEq : (fun ω : Disorder =>
        ((polymerMeasure ϑ N s t ω).map Prod.fst) A) =
        fun ω => polymerMeasure ϑ N s t ω (Prod.fst ⁻¹' A) := by
      funext ω
      exact Measure.map_apply measurable_fst hA
    rw [hEq]
    exact hval
  exact hmap.subtype_mk
    (h := fun ω => isLocallyFiniteMeasure_polymerMarginal ϑ N s t ω)

/-- The pair and its first marginal, coupled in the same disorder sample. -/
noncomputable def polymerPairMarginalRadonMeasure (ϑ : ℝ) (N : ℕ)
    (s t : ℝ) (ω : Disorder) :
    RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure :=
  (polymerRadonMeasure ϑ N s t ω, polymerMarginalRadonMeasure ϑ N s t ω)

/-- The coupled pair-and-marginal Radon measure is measurable. -/
theorem measurable_polymerPairMarginalRadonMeasure (ϑ : ℝ) (N : ℕ) (s t : ℝ) :
    Measurable (polymerPairMarginalRadonMeasure ϑ N s t) := by
  exact (measurable_polymerRadonMeasure ϑ N s t).prodMk
    (measurable_polymerMarginalRadonMeasure ϑ N s t)

/-- The pair and first-marginal Radon measures indexed by strict time pairs,
coupled in the same disorder sample. -/
noncomputable def polymerPairMarginalRadonProcess (ϑ : ℝ) (N : ℕ) (D : Set ℝ)
    (ω : Disorder) : PolymerPairIndex D →
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) :=
  fun i => polymerPairMarginalRadonMeasure ϑ N
    (i.1.1 : ℝ) (i.1.2 : ℝ) ω

private theorem measurable_polymerPairMarginalRadonProcess
    (ϑ : ℝ) (N : ℕ) (D : Set ℝ) :
    Measurable (polymerPairMarginalRadonProcess ϑ N D) := by
  apply measurable_pi_iff.mpr
  intro i
  exact measurable_polymerPairMarginalRadonMeasure ϑ N
    (i.1.1 : ℝ) (i.1.2 : ℝ)

/-- The one-coordinate first-marginal Radon law in the disorder environment. -/
noncomputable def polymerPlaneRadonCoordinateLaw (ϑ : ℝ) (N : ℕ)
    (D : Set ℝ) (i : PolymerPairIndex D) : ProbabilityMeasure RandomMeasure.PlaneRadonMeasure :=
  polymerDisorderProbability.map (fun ω => polymerMarginalRadonMeasure ϑ N
    (i.1.1 : ℝ) (i.1.2 : ℝ) ω)

/-- The first-marginal coordinate law is its disorder pushforward. -/
theorem polymerPlaneRadonCoordinateLaw_eq_map_disorder (ϑ : ℝ) (N : ℕ)
    (D : Set ℝ) (i : PolymerPairIndex D) :
    (polymerPlaneRadonCoordinateLaw ϑ N D i : Measure _) =
      Measure.map (fun ω => polymerMarginalRadonMeasure ϑ N
        (i.1.1 : ℝ) (i.1.2 : ℝ) ω) disorderLaw := rfl

/-- The pair and first-marginal processes, coupled in the same disorder sample. -/
noncomputable def polymerPairMarginalRadonProcessLaw (ϑ : ℝ) (N : ℕ)
    (D : Set ℝ) : ProbabilityMeasure
      (PolymerPairIndex D →
        (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure)) :=
  polymerDisorderProbability.map (polymerPairMarginalRadonProcess ϑ N D)

/-- The law of one fixed time-pair coordinate of the coupled pair-and-marginal process. -/
noncomputable def polymerPairMarginalCoordinateLaw (ϑ : ℝ) (N : ℕ)
    (D : Set ℝ) (i : PolymerPairIndex D) :
    ProbabilityMeasure
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) :=
  (polymerPairMarginalRadonProcessLaw ϑ N D).map (fun m => m i)

/-- The coupled coordinate law is the disorder law of the fixed-time pair and marginal. -/
theorem polymerPairMarginalCoordinateLaw_eq_map_disorder (ϑ : ℝ) (N : ℕ)
    (D : Set ℝ) (i : PolymerPairIndex D) :
    (polymerPairMarginalCoordinateLaw ϑ N D i : Measure _) =
      Measure.map (fun ω => polymerPairMarginalRadonMeasure ϑ N
        (i.1.1 : ℝ) (i.1.2 : ℝ) ω) disorderLaw := by
  change Measure.map (fun m : PolymerPairIndex D →
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) => m i)
    (Measure.map (polymerPairMarginalRadonProcess ϑ N D) disorderLaw) = _
  rw [Measure.map_map (measurable_pi_apply i)
    (measurable_polymerPairMarginalRadonProcess ϑ N D)]
  rfl

private theorem measurable_polymerRadonProcessForJoint (ϑ : ℝ) (N : ℕ) (D : Set ℝ) :
    Measurable (polymerRadonProcess ϑ N D) := by
  apply measurable_pi_iff.mpr
  intro i
  exact measurable_polymerRadonMeasure ϑ N (i.1.1 : ℝ) (i.1.2 : ℝ)

/-- The pair coordinate law is its disorder pushforward. -/
theorem polymerRadonCoordinateLaw_eq_map_disorder (ϑ : ℝ) (N : ℕ)
    (D : Set ℝ) (i : PolymerPairIndex D) :
    (polymerRadonCoordinateLaw ϑ N D i : Measure _) =
      Measure.map (fun ω => polymerRadonMeasure ϑ N
        (i.1.1 : ℝ) (i.1.2 : ℝ) ω) disorderLaw := by
  change Measure.map (fun m : PolymerPairIndex D → RandomMeasure.PlanePairRadonMeasure => m i)
    (Measure.map (polymerRadonProcess ϑ N D) disorderLaw) = _
  rw [Measure.map_map (measurable_pi_apply i)
    (measurable_polymerRadonProcessForJoint ϑ N D)]
  rfl

private theorem map_fst_polymerPairMarginalCoordinateLaw (ϑ : ℝ) (N : ℕ)
    (D : Set ℝ) (i : PolymerPairIndex D) :
    Measure.map Prod.fst
      (polymerPairMarginalCoordinateLaw ϑ N D i :
        Measure (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure)) =
      ((polymerRadonCoordinateLaw ϑ N D i :
        ProbabilityMeasure RandomMeasure.PlanePairRadonMeasure) :
          Measure RandomMeasure.PlanePairRadonMeasure) := by
  rw [polymerPairMarginalCoordinateLaw_eq_map_disorder,
    polymerRadonCoordinateLaw_eq_map_disorder,
    Measure.map_map measurable_fst
    (measurable_polymerPairMarginalRadonMeasure ϑ N
      (i.1.1 : ℝ) (i.1.2 : ℝ))]
  rfl

private theorem map_snd_polymerPairMarginalCoordinateLaw (ϑ : ℝ) (N : ℕ)
    (D : Set ℝ) (i : PolymerPairIndex D) :
    Measure.map Prod.snd
      (polymerPairMarginalCoordinateLaw ϑ N D i :
        Measure (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure)) =
      ((polymerPlaneRadonCoordinateLaw ϑ N D i :
        ProbabilityMeasure RandomMeasure.PlaneRadonMeasure) :
          Measure RandomMeasure.PlaneRadonMeasure) := by
  rw [polymerPairMarginalCoordinateLaw_eq_map_disorder,
    polymerPlaneRadonCoordinateLaw_eq_map_disorder,
    Measure.map_map measurable_snd
    (measurable_polymerPairMarginalRadonMeasure ϑ N
      (i.1.1 : ℝ) (i.1.2 : ℝ))]
  rfl

private theorem lintegral_polymerPlaneMarginalCoordinateLaw_window (ϑ : ℝ)
    (N : ℕ) (D : Set ℝ) (i : PolymerPairIndex D) (k : ℕ) :
    ∫⁻ μ : RandomMeasure.PlaneRadonMeasure,
        μ.1 (RandomMeasure.vagueCompactExhaustion Plane k)
      ∂(polymerPlaneRadonCoordinateLaw ϑ N D i : Measure _) =
    ∫⁻ ω, ((polymerMeasure ϑ N (i.1.1 : ℝ) (i.1.2 : ℝ) ω).map Prod.fst)
      (RandomMeasure.vagueCompactExhaustion Plane k) ∂disorderLaw := by
  let g : RandomMeasure.PlaneRadonMeasure → ℝ≥0∞ :=
    fun μ => μ.1 (RandomMeasure.vagueCompactExhaustion Plane k)
  have hKmeas : MeasurableSet (RandomMeasure.vagueCompactExhaustion Plane k) :=
    ((RandomMeasure.vagueCompactExhaustion Plane).isCompact k).isClosed.measurableSet
  have hg : Measurable g :=
    (Measure.measurable_coe hKmeas).comp measurable_subtype_coe
  calc
    ∫⁻ μ, g μ ∂(polymerPlaneRadonCoordinateLaw ϑ N D i : Measure _) =
      ∫⁻ ω, g (polymerMarginalRadonMeasure ϑ N
        (i.1.1 : ℝ) (i.1.2 : ℝ) ω) ∂disorderLaw := by
          rw [polymerPlaneRadonCoordinateLaw_eq_map_disorder]
          exact lintegral_map hg
            (measurable_polymerMarginalRadonMeasure ϑ N
              (i.1.1 : ℝ) (i.1.2 : ℝ))
    _ = ∫⁻ ω, ((polymerMeasure ϑ N (i.1.1 : ℝ) (i.1.2 : ℝ) ω).map Prod.fst)
          (RandomMeasure.vagueCompactExhaustion Plane k) ∂disorderLaw := rfl

private theorem isTight_polymerPlaneMarginalCoordinateLaws (ϑ : ℝ) (D : Set ℝ)
    (i : PolymerPairIndex D) :
    IsTightMeasureSet (Set.range fun N : ℕ =>
      (polymerPlaneRadonCoordinateLaw ϑ N D i :
        Measure RandomMeasure.PlaneRadonMeasure)) := by
  classical
  let K : CompactExhaustion Plane :=
    RandomMeasure.vagueCompactExhaustion Plane
  let S : Set (ProbabilityMeasure RandomMeasure.PlaneRadonMeasure) :=
    Set.range fun N : ℕ => polymerPlaneRadonCoordinateLaw ϑ N D i
  have hExp : ∀ k : ℕ, ∃ M : ℝ≥0∞, M < ∞ ∧
      ∀ P ∈ S, ∫⁻ μ : RandomMeasure.PlaneRadonMeasure, μ.1 (K k)
          ∂(P : Measure _) ≤ M := by
    intro k
    refine ⟨volume (K k), (K.isCompact k).measure_lt_top, ?_⟩
    rintro P ⟨N, rfl⟩
    calc
      ∫⁻ μ : RandomMeasure.PlaneRadonMeasure, μ.1 (K k)
          ∂(polymerPlaneRadonCoordinateLaw ϑ N D i : Measure _) =
          ∫⁻ ω, ((polymerMeasure ϑ N (i.1.1 : ℝ) (i.1.2 : ℝ) ω).map Prod.fst)
            (K k) ∂disorderLaw :=
              lintegral_polymerPlaneMarginalCoordinateLaw_window ϑ N D i k
      _ ≤ volume (K k) := by
            by_cases hN0 : N = 0
            · subst N
              have hzero (ω : Disorder) : polymerMeasure ϑ 0
                  (i.1.1 : ℝ) (i.1.2 : ℝ) ω = 0 := by
                rw [polymerMeasure]
                ext A hA
                simp [rescaledP2P]
              simp [hzero]
            · exact le_of_eq (lintegral_polymerMarginal_compact_mass_eq
                ϑ (Nat.one_le_iff_ne_zero.mpr hN0) _ _ (K k) (K.isCompact k))
  letI : TopologicalSpace RandomMeasure.PlaneRadonMeasure :=
    RandomMeasure.vagueTopology Plane
  letI : PolishSpace RandomMeasure.PlaneRadonMeasure := RandomMeasure.vaguePolishSpace
  letI : BorelSpace RandomMeasure.PlaneRadonMeasure :=
    ⟨RandomMeasure.eval_eq_vague_borel⟩
  letI : OpensMeasurableSpace RandomMeasure.PlaneRadonMeasure :=
    ⟨RandomMeasure.eval_eq_vague_borel.symm.le⟩
  have hExp' : ∀ k : ℕ, ∃ M : ℝ≥0∞, M < ∞ ∧
      ∀ P ∈ S, (∫⁻ μ : RandomMeasure.PlaneRadonMeasure,
        Critical2DKPZ.RandomMeasure.vagueCompactWindowMass K k μ
          ∂(P : Measure _)) ≤ M := by
    intro k
    obtain ⟨M, hM, hbound⟩ := hExp k
    refine ⟨M, hM, ?_⟩
    intro P hP
    simpa [Critical2DKPZ.RandomMeasure.vagueCompactWindowMass] using hbound P hP
  have hgeneric :=
    Critical2DKPZ.RandomMeasure.isTightMeasureSet_of_uniform_expected_compact_mass
      K S hExp'
  have hrange :
      {((P : ProbabilityMeasure RandomMeasure.PlaneRadonMeasure) :
        Measure RandomMeasure.PlaneRadonMeasure) | P ∈ S} =
      Set.range fun N : ℕ => (polymerPlaneRadonCoordinateLaw ϑ N D i :
        Measure RandomMeasure.PlaneRadonMeasure) := by
    ext μ
    simp [S]
  rw [← hrange]
  exact hgeneric

/-- A coupled coordinate law is tight when both of its marginal law families
are tight. -/
private theorem isTight_polymerPairMarginalCoordinateLaws (ϑ : ℝ) (D : Set ℝ)
    (i : PolymerPairIndex D) :
    IsTightMeasureSet (Set.range fun N : ℕ =>
      (polymerPairMarginalCoordinateLaw ϑ N D i :
        Measure (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure))) := by
  classical
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
  letI : TopologicalSpace
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) := inferInstance
  letI : BorelSpace
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) := inferInstance
  letI : OpensMeasurableSpace
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) := inferInstance
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  let δ : ℝ≥0∞ := min ε 1
  have hδpos : 0 < δ := lt_min hε zero_lt_one
  have hδtop : δ < ∞ := lt_of_le_of_lt (min_le_right _ _) (by simp)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδtoReal : 0 < δ.toReal := ENNReal.toReal_pos hδpos.ne' hδtop.ne
  let η : ℝ := δ.toReal / 2
  have hηpos : 0 < η := by dsimp [η]; positivity
  have hηnonneg : 0 ≤ η := hηpos.le
  have htight₁ := isTight_polymerRadonCoordinateLaws ϑ D i
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at htight₁
  obtain ⟨K₁, hK₁, htail₁⟩ := htight₁ (ENNReal.ofReal η) (ENNReal.ofReal_pos.mpr hηpos)
  have htight₂ := isTight_polymerPlaneMarginalCoordinateLaws ϑ D i
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at htight₂
  obtain ⟨K₂, hK₂, htail₂⟩ := htight₂ (ENNReal.ofReal η) (ENNReal.ofReal_pos.mpr hηpos)
  let K : Set (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) :=
    K₁ ×ˢ K₂
  have hK : IsCompact K := hK₁.prod hK₂
  have hbad (N : ℕ) :
      (((polymerPairMarginalCoordinateLaw ϑ N D i : ProbabilityMeasure
        (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure)) :
          Measure (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure))
        (Kᶜ)) ≤ δ := by
    have hcover : Kᶜ ⊆
        {z | z.1 ∉ K₁} ∪ {z : RandomMeasure.PlanePairRadonMeasure ×
          RandomMeasure.PlaneRadonMeasure | z.2 ∉ K₂} := by
      intro z hz
      change ¬ (z.1 ∈ K₁ ∧ z.2 ∈ K₂) at hz
      by_cases hfirst : z.1 ∈ K₁
      · exact Or.inr (fun hsecond => hz ⟨hfirst, hsecond⟩)
      · exact Or.inl hfirst
    have htail₁N :
        (polymerRadonCoordinateLaw ϑ N D i : Measure _) (K₁ᶜ) ≤ ENNReal.ofReal η :=
      htail₁ _ ⟨N, rfl⟩
    have htail₂N :
        (polymerPlaneRadonCoordinateLaw ϑ N D i : Measure _) (K₂ᶜ) ≤ ENNReal.ofReal η :=
      htail₂ _ ⟨N, rfl⟩
    have hbad₁ : ((polymerPairMarginalCoordinateLaw ϑ N D i : ProbabilityMeasure
        (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure)) :
          Measure (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure))
        {z : RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure |
          z.1 ∉ K₁} ≤ ENNReal.ofReal η := by
      change ((polymerPairMarginalCoordinateLaw ϑ N D i : ProbabilityMeasure
        (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure)) :
          Measure (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure))
        (Prod.fst ⁻¹' K₁ᶜ) ≤ _
      rw [(Measure.map_apply measurable_fst (hK₁.isClosed.measurableSet.compl)).symm,
        map_fst_polymerPairMarginalCoordinateLaw ϑ N D i]
      exact htail₁N
    have hbad₂ : ((polymerPairMarginalCoordinateLaw ϑ N D i : ProbabilityMeasure
        (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure)) :
          Measure (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure))
        {z : RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure |
          z.2 ∉ K₂} ≤ ENNReal.ofReal η := by
      change ((polymerPairMarginalCoordinateLaw ϑ N D i : ProbabilityMeasure
        (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure)) :
          Measure (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure))
        (Prod.snd ⁻¹' K₂ᶜ) ≤ _
      rw [(Measure.map_apply measurable_snd (hK₂.isClosed.measurableSet.compl)).symm,
        map_snd_polymerPairMarginalCoordinateLaw ϑ N D i]
      exact htail₂N
    calc
      (((polymerPairMarginalCoordinateLaw ϑ N D i : ProbabilityMeasure
        (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure)) :
          Measure (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure))
        (Kᶜ)) ≤
          ((polymerPairMarginalCoordinateLaw ϑ N D i : ProbabilityMeasure
            (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure)) :
              Measure (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure))
            ({z | z.1 ∉ K₁} ∪ {z | z.2 ∉ K₂}) := measure_mono hcover
      _ ≤ ((polymerPairMarginalCoordinateLaw ϑ N D i : ProbabilityMeasure
            (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure)) :
              Measure (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure))
            {z | z.1 ∉ K₁} +
          ((polymerPairMarginalCoordinateLaw ϑ N D i : ProbabilityMeasure
            (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure)) :
              Measure (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure))
            {z | z.2 ∉ K₂} :=
        measure_union_le _ _
      _ ≤ ENNReal.ofReal η + ENNReal.ofReal η := add_le_add hbad₁ hbad₂
      _ = ENNReal.ofReal δ.toReal := by
        rw [← ENNReal.ofReal_add hηnonneg hηnonneg]
        congr 1
        dsimp [η]
        ring
      _ = δ := ENNReal.ofReal_toReal hδtop.ne
  refine ⟨K, hK, ?_⟩
  rintro P ⟨N, rfl⟩
  exact (hbad N).trans hδε

/-- Coupled coordinate tightness makes the countable joint process laws tight. -/
private theorem isTight_polymerPairMarginalRadonProcessLaws (ϑ : ℝ) (D : Set ℝ)
    (hD : D.Countable) :
    letI : TopologicalSpace
        (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) := inferInstance
    letI : MeasurableSpace
        (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure) := inferInstance
    letI : TopologicalSpace (PolymerPairIndex D →
        (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure)) :=
      Pi.topologicalSpace
    IsTightMeasureSet (Set.range fun N : ℕ =>
      (polymerPairMarginalRadonProcessLaw ϑ N D : Measure
        (PolymerPairIndex D →
          (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure)))) := by
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
  letI : TopologicalSpace
      (PolymerPairIndex D →
        (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure)) :=
    Pi.topologicalSpace
  letI : MeasurableSpace
      (PolymerPairIndex D →
        (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure)) := inferInstance
  letI : PolishSpace
      (PolymerPairIndex D →
        (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure)) := inferInstance
  letI : BorelSpace
      (PolymerPairIndex D →
        (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure)) := inferInstance
  letI : OpensMeasurableSpace
      (PolymerPairIndex D →
        (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure)) := inferInstance
  apply Critical2DKPZ.RandomMeasure.isTightMeasureSet_range_of_tight_coordinates
  intro i
  exact isTight_polymerPairMarginalCoordinateLaws ϑ D i

/-- Every reindexing of the coupled pair-and-marginal process laws has a
jointly weakly convergent subsequence. -/
theorem exists_subseq_tendsto_polymerPairMarginalRadonProcessLaw
    (ϑ : ℝ) (D : Set ℝ) (hD : D.Countable) (φ : ℕ → ℕ) (hφ : StrictMono φ) :
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
    letI : Countable D := hD.to_subtype
    letI : Countable (D × D) := inferInstance
    letI : Countable (PolymerPairIndex D) := inferInstance
    letI : PolishSpace (PolymerPairIndex D →
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure)) := inferInstance
    letI : BorelSpace (PolymerPairIndex D →
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure)) := inferInstance
    letI : OpensMeasurableSpace (PolymerPairIndex D →
      (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure)) := inferInstance
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ StrictMono (φ ∘ ψ) ∧
      ∃ Q : ProbabilityMeasure (PolymerPairIndex D →
        (RandomMeasure.PlanePairRadonMeasure × RandomMeasure.PlaneRadonMeasure)),
        Tendsto (fun n => polymerPairMarginalRadonProcessLaw ϑ (φ (ψ n)) D)
          atTop (𝓝 Q) := by
  classical
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
  obtain ⟨ψ, Q, hψ, hlim⟩ :=
    RandomMeasure.exists_subseq_tendsto_of_tight_reindexing_probability_laws
      (fun N => polymerPairMarginalRadonProcessLaw ϑ N D)
      (isTight_polymerPairMarginalRadonProcessLaws ϑ D hD) φ
  exact ⟨ψ, hψ, hφ.comp hψ, Q, hlim⟩

end Critical2DKPZ.SHF.Limit

end
