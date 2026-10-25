/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Limit.Equiv
import Critical2DKPZ.Analysis.Heat.Moments
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Tight

/-! # Compact-mass bounds for polymer measures -/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal CompactlySupported Topology

set_option linter.style.haveILetI false

noncomputable section

namespace Critical2DKPZ.SHF.Limit

private theorem polymerMeasure_zero (ϑ : ℝ) (s t : ℝ) (ω : Disorder) :
    polymerMeasure ϑ 0 s t ω = 0 := by
  rw [polymerMeasure]
  ext A hA
  simp [rescaledP2P]

private theorem lintegral_rescaledP2Plane (ϑ : ℝ) (N : ℕ) (s t : ℝ) (x : Plane) :
    ∫⁻ ω, ENNReal.ofReal (rescaledP2Plane ϑ N s t x ω) ∂disorderLaw = 1 := by
  have hi : Integrable (fun ω => rescaledP2Plane ϑ N s t x ω) disorderLaw := by
    change Integrable (fun ω => pointToPlane (criticalBeta ϑ N)
      (evenCeil ((N : ℝ) * s)) (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s))
      (latticePoint N x) ω) disorderLaw
    exact Polymer.integrable_pointToPlane (criticalBeta ϑ N)
      (evenCeil ((N : ℝ) * s))
      (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) (latticePoint N x)
  have hnonneg : 0 ≤ᵐ[disorderLaw] fun ω => rescaledP2Plane ϑ N s t x ω :=
    Filter.Eventually.of_forall fun ω => (Polymer.pointToPlane_pos ..).le
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnonneg,
    integral_rescaledP2Plane, ENNReal.ofReal_one]

private theorem measurable_rescaledDensity_disorderPlane (ϑ : ℝ) (N : ℕ)
    (s t : ℝ) : Measurable (fun q : Disorder × Plane =>
      ENNReal.ofReal (rescaledP2Plane ϑ N s t q.2 q.1)) := by
  have hbase : Measurable (fun q : Disorder × Plane =>
      rescaledP2Plane ϑ N s t q.2 q.1) := by
    convert (measurable_uncurry_rescaledP2Plane ϑ N s t).comp measurable_swap using 1
    funext q
    rfl
  exact ENNReal.measurable_ofReal.comp hbase

private theorem lintegral_rescaledP2Plane_disorder_compact (ϑ : ℝ) (N : ℕ)
    (s t : ℝ) (A : Set Plane) (hA : IsCompact A) :
    ∫⁻ x in A, ∫⁻ ω, ENNReal.ofReal (rescaledP2Plane ϑ N s t x ω)
      ∂disorderLaw ∂volume = volume A := by
  classical
  have hAmeas : MeasurableSet A := hA.isClosed.measurableSet
  calc
    ∫⁻ x in A, ∫⁻ ω, ENNReal.ofReal (rescaledP2Plane ϑ N s t x ω)
        ∂disorderLaw ∂volume
        = ∫⁻ x in A, 1 ∂volume := by
          apply lintegral_congr_ae
          filter_upwards [] with x
          exact lintegral_rescaledP2Plane ϑ N s t x
    _ = volume A := by
          rw [← lintegral_indicator hAmeas]
          exact lintegral_indicator_one hAmeas

private theorem lintegral_rescaledP2Plane_swap_compact (ϑ : ℝ) (N : ℕ)
    (s t : ℝ) (A : Set Plane) :
    ∫⁻ ω, ∫⁻ x in A, ENNReal.ofReal (rescaledP2Plane ϑ N s t x ω)
      ∂volume ∂disorderLaw =
    ∫⁻ x in A, ∫⁻ ω, ENNReal.ofReal (rescaledP2Plane ϑ N s t x ω)
      ∂disorderLaw ∂volume := by
  classical
  have hbase := measurable_rescaledDensity_disorderPlane ϑ N s t
  change ∫⁻ ω, ∫⁻ x, ENNReal.ofReal (rescaledP2Plane ϑ N s t x ω)
      ∂(volume.restrict A) ∂disorderLaw =
    ∫⁻ x, ∫⁻ ω, ENNReal.ofReal (rescaledP2Plane ϑ N s t x ω)
      ∂disorderLaw ∂(volume.restrict A)
  exact lintegral_lintegral_swap hbase.aemeasurable

private theorem lintegral_rescaledP2Plane_compact (ϑ : ℝ) (N : ℕ)
    (s t : ℝ) (A : Set Plane) (hA : IsCompact A) :
    ∫⁻ ω, ∫⁻ x in A, ENNReal.ofReal (rescaledP2Plane ϑ N s t x ω)
      ∂volume ∂disorderLaw = volume A := by
  rw [lintegral_rescaledP2Plane_swap_compact ϑ N s t A]
  exact lintegral_rescaledP2Plane_disorder_compact ϑ N s t A hA

/-- At positive lattice scale, the expected mass of a compact set under the polymer first marginal equals its Lebesgue volume. -/
theorem lintegral_polymerMarginal_compact_mass_eq (ϑ : ℝ) {N : ℕ}
    (hN : 1 ≤ N) (s t : ℝ) (A : Set Plane) (hA : IsCompact A) :
    ∫⁻ ω, ((polymerMeasure ϑ N s t ω).map Prod.fst) A ∂disorderLaw = volume A := by
  have hAmeas : MeasurableSet A := hA.isClosed.measurableSet
  calc
    ∫⁻ ω, ((polymerMeasure ϑ N s t ω).map Prod.fst) A ∂disorderLaw
        = ∫⁻ ω, ∫⁻ x in A, ENNReal.ofReal (rescaledP2Plane ϑ N s t x ω)
            ∂volume ∂disorderLaw := by
          apply lintegral_congr_ae
          filter_upwards [] with ω
          rw [map_fst_polymerMeasure ϑ hN s t ω,
            withDensity_apply _ hAmeas]
    _ = volume A := lintegral_rescaledP2Plane_compact ϑ N s t A hA

/-- The expected mass of a compact plane-pair set is bounded by the finite Lebesgue volume of its first-coordinate projection. -/
theorem lintegral_polymerMeasure_compact_pair_mass_le (ϑ : ℝ) (N : ℕ) (s t : ℝ)
    (K : Set (Plane × Plane)) (hK : IsCompact K) :
    ∫⁻ ω, polymerMeasure ϑ N s t ω K ∂disorderLaw ≤ volume (Prod.fst '' K) := by
  let A := Prod.fst '' K
  have hA : IsCompact A := hK.image continuous_fst
  have hAmeas : MeasurableSet A := hA.isClosed.measurableSet
  by_cases hN0 : N = 0
  · subst N
    simp_rw [polymerMeasure_zero]
    simp
  · have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
    have hmass_le (ω : Disorder) : polymerMeasure ϑ N s t ω K ≤
        ((polymerMeasure ϑ N s t ω).map Prod.fst) A := by
      calc
        polymerMeasure ϑ N s t ω K ≤
            polymerMeasure ϑ N s t ω (Prod.fst ⁻¹' A) :=
          measure_mono (by
            intro p hp
            exact ⟨p, hp, rfl⟩)
        _ = ((polymerMeasure ϑ N s t ω).map Prod.fst) A := by
          rw [Measure.map_apply measurable_fst hAmeas]
    calc
      ∫⁻ ω, polymerMeasure ϑ N s t ω K ∂disorderLaw ≤
          ∫⁻ ω, ((polymerMeasure ϑ N s t ω).map Prod.fst) A ∂disorderLaw :=
        lintegral_mono hmass_le
      _ = volume A := lintegral_polymerMarginal_compact_mass_eq ϑ hN s t A hA


/-- The countable index of strict ordered pairs from a set of times. -/
abbrev PolymerPairIndex (D : Set ℝ) :=
  {p : D × D // (p.1 : ℝ) < p.2}

/-- A polymer measure at fixed times, viewed as a positive Radon measure. -/
noncomputable def polymerRadonMeasure (ϑ : ℝ) (N : ℕ) (s t : ℝ)
    (ω : Disorder) : RandomMeasure.PlanePairRadonMeasure :=
  ⟨polymerMeasure ϑ N s t ω,
    isLocallyFiniteMeasure_polymerMeasure ϑ N s t ω⟩

/-- The polymer Radon measure is measurable for the evaluation sigma-algebra,
and hence for the equal vague Borel sigma-algebra. -/
theorem measurable_polymerRadonMeasure (ϑ : ℝ) (N : ℕ) (s t : ℝ) :
    @Measurable Disorder RandomMeasure.PlanePairRadonMeasure inferInstance
      (MeasurableSpace.comap Subtype.val inferInstance)
      (fun ω => polymerRadonMeasure ϑ N s t ω) := by
  exact (measurable_polymerMeasure ϑ N s t).subtype_mk
    (h := fun ω => isLocallyFiniteMeasure_polymerMeasure ϑ N s t ω)

/-- The polymer Radon measures indexed by strict time pairs from `D`. -/
noncomputable def polymerRadonProcess (ϑ : ℝ) (N : ℕ) (D : Set ℝ)
    (ω : Disorder) : PolymerPairIndex D → RandomMeasure.PlanePairRadonMeasure :=
  fun i => polymerRadonMeasure ϑ N (i.1.1 : ℝ) (i.1.2 : ℝ) ω

private theorem measurable_polymerRadonProcess (ϑ : ℝ) (N : ℕ) (D : Set ℝ) :
    Measurable (polymerRadonProcess ϑ N D) := by
  apply measurable_pi_iff.mpr
  intro i
  exact measurable_polymerRadonMeasure ϑ N (i.1.1 : ℝ) (i.1.2 : ℝ)

/-- The fixed disorder probability law used for polymer random measures. -/
noncomputable def polymerDisorderProbability : ProbabilityMeasure Disorder :=
  ⟨disorderLaw, inferInstance⟩

/-- The disorder law pushed forward to the countable family of polymer
Radon measures indexed by strict time pairs in `D`. -/
noncomputable def polymerRadonProcessLaw (ϑ : ℝ) (N : ℕ) (D : Set ℝ) :
    ProbabilityMeasure (PolymerPairIndex D → RandomMeasure.PlanePairRadonMeasure) :=
  polymerDisorderProbability.map (polymerRadonProcess ϑ N D)

/-- The law of one strict-time-pair coordinate of the polymer Radon process. -/
noncomputable def polymerRadonCoordinateLaw (ϑ : ℝ) (N : ℕ)
    (D : Set ℝ) (i : PolymerPairIndex D) :
    ProbabilityMeasure RandomMeasure.PlanePairRadonMeasure :=
  (polymerRadonProcessLaw ϑ N D).map (fun m => m i)

/-- Integrating a compact-window coordinate under a polymer product law is
the same as integrating the original polymer mass. -/
private theorem lintegral_polymerRadonProcessLaw_window (ϑ : ℝ) (N : ℕ)
    (D : Set ℝ) (i : PolymerPairIndex D) (k : ℕ) :
    ∫⁻ m : PolymerPairIndex D → RandomMeasure.PlanePairRadonMeasure,
        (m i).1 (RandomMeasure.vagueCompactExhaustion (Plane × Plane) k)
      ∂(polymerRadonProcessLaw ϑ N D : Measure _) =
    ∫⁻ ω, polymerMeasure ϑ N (i.1.1 : ℝ) (i.1.2 : ℝ) ω
      (RandomMeasure.vagueCompactExhaustion (Plane × Plane) k) ∂disorderLaw := by
  let g : (PolymerPairIndex D → RandomMeasure.PlanePairRadonMeasure) → ℝ≥0∞ :=
    fun m => (m i).1 (RandomMeasure.vagueCompactExhaustion (Plane × Plane) k)
  have hKmeas : MeasurableSet
      (RandomMeasure.vagueCompactExhaustion (Plane × Plane) k) :=
    ((RandomMeasure.vagueCompactExhaustion (Plane × Plane)).isCompact k).isClosed.measurableSet
  have hEval : Measurable (fun μ : RandomMeasure.PlanePairRadonMeasure =>
      μ.1 (RandomMeasure.vagueCompactExhaustion (Plane × Plane) k)) :=
    (Measure.measurable_coe hKmeas).comp measurable_subtype_coe
  have hg : Measurable g := hEval.comp (measurable_pi_apply i)
  calc
    ∫⁻ m, g m ∂(polymerRadonProcessLaw ϑ N D : Measure _) =
        ∫⁻ ω, g (polymerRadonProcess ϑ N D ω) ∂disorderLaw := by
          change ∫⁻ m, g m ∂Measure.map
              (polymerRadonProcess ϑ N D) disorderLaw = _
          exact lintegral_map hg (measurable_polymerRadonProcess ϑ N D)
    _ = ∫⁻ ω, polymerMeasure ϑ N (i.1.1 : ℝ) (i.1.2 : ℝ) ω
          (RandomMeasure.vagueCompactExhaustion (Plane × Plane) k) ∂disorderLaw := by
          apply lintegral_congr_ae
          filter_upwards [] with ω
          change (polymerRadonProcess ϑ N D ω i).1
            (RandomMeasure.vagueCompactExhaustion (Plane × Plane) k) = _
          change polymerMeasure ϑ N (i.1.1 : ℝ) (i.1.2 : ℝ) ω
            (RandomMeasure.vagueCompactExhaustion (Plane × Plane) k) = _
          rfl

/-- Expected compact-window mass of one pair coordinate, expressed in the
original disorder environment. -/
theorem lintegral_polymerRadonCoordinateLaw_window (ϑ : ℝ) (N : ℕ)
    (D : Set ℝ) (i : PolymerPairIndex D) (k : ℕ) :
    ∫⁻ μ : RandomMeasure.PlanePairRadonMeasure,
        μ.1 (RandomMeasure.vagueCompactExhaustion (Plane × Plane) k)
      ∂(polymerRadonCoordinateLaw ϑ N D i : Measure _) =
    ∫⁻ ω, polymerMeasure ϑ N (i.1.1 : ℝ) (i.1.2 : ℝ) ω
      (RandomMeasure.vagueCompactExhaustion (Plane × Plane) k) ∂disorderLaw := by
  let g : RandomMeasure.PlanePairRadonMeasure → ℝ≥0∞ :=
    fun μ => μ.1 (RandomMeasure.vagueCompactExhaustion (Plane × Plane) k)
  have hKmeas : MeasurableSet
      (RandomMeasure.vagueCompactExhaustion (Plane × Plane) k) :=
    ((RandomMeasure.vagueCompactExhaustion (Plane × Plane)).isCompact k).isClosed.measurableSet
  have hg : Measurable g :=
    (Measure.measurable_coe hKmeas).comp measurable_subtype_coe
  calc
    ∫⁻ μ, g μ ∂(polymerRadonCoordinateLaw ϑ N D i : Measure _) =
    ∫⁻ m : PolymerPairIndex D → RandomMeasure.PlanePairRadonMeasure,
        g (m i) ∂(polymerRadonProcessLaw ϑ N D : Measure _) := by
          change ∫⁻ μ, g μ ∂Measure.map
              (fun m : PolymerPairIndex D → RandomMeasure.PlanePairRadonMeasure => m i)
              (polymerRadonProcessLaw ϑ N D : Measure _) = _
          exact lintegral_map hg (measurable_pi_apply i)
    _ = ∫⁻ ω, polymerMeasure ϑ N (i.1.1 : ℝ) (i.1.2 : ℝ) ω
          (RandomMeasure.vagueCompactExhaustion (Plane × Plane) k) ∂disorderLaw :=
          lintegral_polymerRadonProcessLaw_window ϑ N D i k

/-- The first-moment compact-window bounds make each coordinate family of
polymer pair laws tight in the vague topology. -/
theorem isTight_polymerRadonCoordinateLaws (ϑ : ℝ) (D : Set ℝ)
    (i : PolymerPairIndex D) :
    IsTightMeasureSet (Set.range fun N : ℕ =>
      (polymerRadonCoordinateLaw ϑ N D i : Measure RandomMeasure.PlanePairRadonMeasure)) := by
  classical
  let K : CompactExhaustion (Plane × Plane) :=
    RandomMeasure.vagueCompactExhaustion (Plane × Plane)
  have hEval (k : ℕ) : Measurable (fun μ : RandomMeasure.PlanePairRadonMeasure =>
      μ.1 (K k)) :=
    (Measure.measurable_coe ((K.isCompact k).isClosed.measurableSet)).comp
      measurable_subtype_coe
  have hExp (k : ℕ) : ∃ M : ℝ≥0∞, M < ∞ ∧
      ∀ N : ℕ,
        (∫⁻ μ : RandomMeasure.PlanePairRadonMeasure, μ.1 (K k)
          ∂(polymerRadonCoordinateLaw ϑ N D i : Measure _)) ≤ M := by
    let A : Set Plane := Prod.fst '' (K k)
    have hA : IsCompact A := (K.isCompact k).image continuous_fst
    refine ⟨volume A, hA.measure_lt_top, ?_⟩
    intro N
    calc
      ∫⁻ μ : RandomMeasure.PlanePairRadonMeasure, μ.1 (K k)
          ∂(polymerRadonCoordinateLaw ϑ N D i : Measure _) =
          ∫⁻ ω, polymerMeasure ϑ N (i.1.1 : ℝ) (i.1.2 : ℝ) ω (K k)
            ∂disorderLaw := lintegral_polymerRadonCoordinateLaw_window ϑ N D i k
      _ ≤ volume A := by
            exact lintegral_polymerMeasure_compact_pair_mass_le
              ϑ N (i.1.1 : ℝ) (i.1.2 : ℝ) (K k) (K.isCompact k)
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  let δ : ℝ≥0∞ := min ε 1
  have hδpos : 0 < δ := lt_min hε zero_lt_one
  have hδtop : δ < ∞ := lt_of_le_of_lt (min_le_right _ _) (by simp)
  have hδε : δ ≤ ε := min_le_left _ _
  choose M hMtop hMbound using hExp
  let w : ℕ → ℝ≥0∞ := fun k => δ * (1 / 2 : ℝ≥0∞) ^ (k + 1)
  have hwpos (k : ℕ) : 0 < w k := by
    dsimp [w]
    exact ENNReal.mul_pos hδpos.ne' (pow_ne_zero _ (by norm_num))
  have hwtop (k : ℕ) : w k < ∞ := by
    dsimp [w]
    apply ENNReal.mul_lt_top hδtop
    finiteness
  let R : ℕ → ℝ≥0∞ := fun k => M k / w k + 1
  have hRpos (k : ℕ) : 0 < R k := by
    dsimp [R]
    exact zero_lt_one.trans_le (le_add_of_nonneg_left (by positivity))
  have hRtop (k : ℕ) : R k < ∞ := by
    dsimp [R]
    rw [ENNReal.add_lt_top]
    exact ⟨ENNReal.div_lt_top (hMtop k).ne (hwpos k).ne', by simp⟩
  have hMtail (k : ℕ) : M k / R k ≤ w k := by
    rw [ENNReal.div_le_iff_le_mul (Or.inl (hRpos k).ne') (Or.inl (hRtop k).ne)]
    dsimp [R]
    have hcancel : M k / w k * w k = M k :=
      ENNReal.div_mul_cancel (hwpos k).ne' (hwtop k).ne
    calc
      M k = M k / w k * w k := hcancel.symm
      _ ≤ (M k / w k + 1) * w k := by
        gcongr
        exact le_add_of_nonneg_right (by norm_num)
      _ = w k * (M k / w k + 1) := mul_comm _ _
  let A : Set RandomMeasure.PlanePairRadonMeasure :=
    {μ | ∀ k, μ.1 (K k) ≤ R k}
  have hcompact : IsCompact (closure A) := by
    rw [RandomMeasure.isCompact_vagueClosure_iff_localMassBound K]
    intro k
    refine ⟨(R k).toReal, fun μ hμ => ?_⟩
    have hle := hμ k
    change μ.measure (K k) ≤ R k at hle
    simpa only [Measure.real_def] using ENNReal.toReal_mono (hRtop k).ne hle
  have hMarkov (P : ProbabilityMeasure RandomMeasure.PlanePairRadonMeasure)
      (k : ℕ) :
      (P : Measure RandomMeasure.PlanePairRadonMeasure)
          {μ : RandomMeasure.PlanePairRadonMeasure | R k ≤ μ.1 (K k)} ≤
        (∫⁻ μ : RandomMeasure.PlanePairRadonMeasure, μ.1 (K k)
          ∂(P : Measure _)) / R k :=
    MeasureTheory.meas_ge_le_lintegral_div
      (μ := (P : Measure RandomMeasure.PlanePairRadonMeasure))
      (f := fun μ : RandomMeasure.PlanePairRadonMeasure => μ.1 (K k))
      (hEval k).aemeasurable (hRpos k).ne' (hRtop k).ne
  have hbad (P : ProbabilityMeasure RandomMeasure.PlanePairRadonMeasure)
      (hP : P ∈ Set.range fun N : ℕ => polymerRadonCoordinateLaw ϑ N D i) :
      (P : Measure RandomMeasure.PlanePairRadonMeasure) (Aᶜ) ≤ δ := by
    obtain ⟨N, rfl⟩ := hP
    have hbadEq : Aᶜ = ⋃ k,
        {μ : RandomMeasure.PlanePairRadonMeasure | R k < μ.1 (K k)} := by
      ext μ
      simp only [A, mem_compl_iff, mem_ofPred_eq, mem_iUnion, not_forall, not_le]
    calc
      (polymerRadonCoordinateLaw ϑ N D i : Measure _) (Aᶜ) =
          (polymerRadonCoordinateLaw ϑ N D i : Measure _)
            (⋃ k, {μ : RandomMeasure.PlanePairRadonMeasure | R k < μ.1 (K k)}) := by
              rw [hbadEq]
      _ ≤ ∑' k, (polymerRadonCoordinateLaw ϑ N D i : Measure _)
          {μ : RandomMeasure.PlanePairRadonMeasure | R k < μ.1 (K k)} :=
            measure_iUnion_le _
      _ ≤ ∑' k, w k := by
        apply ENNReal.tsum_le_tsum
        intro k
        calc
          (polymerRadonCoordinateLaw ϑ N D i : Measure _)
              {μ : RandomMeasure.PlanePairRadonMeasure | R k < μ.1 (K k)} ≤
              (polymerRadonCoordinateLaw ϑ N D i : Measure _)
                {μ : RandomMeasure.PlanePairRadonMeasure | R k ≤ μ.1 (K k)} :=
            measure_mono (by
              intro μ hμ
              change R k < μ.1 (K k) at hμ
              exact hμ.le)
          _ ≤ (∫⁻ μ : RandomMeasure.PlanePairRadonMeasure, μ.1 (K k)
              ∂(polymerRadonCoordinateLaw ϑ N D i : Measure _)) / R k := hMarkov _ k
          _ ≤ M k / R k := ENNReal.div_le_div_right (hMbound k N) _
          _ ≤ w k := hMtail k
      _ = δ := by
        rw [ENNReal.tsum_mul_left]
        have hgeom : (∑' k : ℕ, (1 / 2 : ℝ≥0∞) ^ (k + 1)) = 1 := by
          simp_rw [one_div]
          rw [ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two, inv_inv]
          have htwo0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
          have htwotop : (2 : ℝ≥0∞) ≠ ∞ := by simp
          exact ENNReal.inv_mul_cancel htwo0 htwotop
        rw [hgeom, mul_one]
  refine ⟨closure A, hcompact, ?_⟩
  intro Q hQ
  rcases hQ with ⟨N, hN⟩
  subst Q
  have hsub : (closure A)ᶜ ⊆ Aᶜ := by
    intro μ hμ hA
    exact hμ (subset_closure hA)
  calc
    (polymerRadonCoordinateLaw ϑ N D i : Measure RandomMeasure.PlanePairRadonMeasure)
        ((closure A)ᶜ) ≤
        (polymerRadonCoordinateLaw ϑ N D i : Measure _) (Aᶜ) := measure_mono hsub
    _ ≤ δ := hbad (polymerRadonCoordinateLaw ϑ N D i) ⟨N, rfl⟩
    _ ≤ ε := hδε

/-- Uniform first-moment bounds make the polymer laws tight on the countable
product indexed by strict time pairs. -/
theorem isTight_polymerRadonProcessLaws (ϑ : ℝ) (D : Set ℝ) (hD : D.Countable) :
    IsTightMeasureSet (Set.range fun N : ℕ =>
      (polymerRadonProcessLaw ϑ N D : Measure
        (PolymerPairIndex D → RandomMeasure.PlanePairRadonMeasure))) := by
  letI : PolishSpace RandomMeasure.PlanePairRadonMeasure :=
    RandomMeasure.polishSpace_positiveRadonMeasure_planePair
  letI : BorelSpace RandomMeasure.PlanePairRadonMeasure :=
    ⟨RandomMeasure.borel_positiveRadonMeasure_eq_comap.symm⟩
  letI : OpensMeasurableSpace RandomMeasure.PlanePairRadonMeasure :=
    ⟨RandomMeasure.borel_positiveRadonMeasure_eq_comap.le⟩
  letI : Countable D := hD.to_subtype
  letI : Countable (D × D) := inferInstance
  letI : Countable (PolymerPairIndex D) := inferInstance
  apply RandomMeasure.isTightMeasureSet_range_of_tight_coordinates
  intro i
  exact isTight_polymerRadonCoordinateLaws ϑ D i

/-- Every reindexed sequence of polymer process laws has a weakly convergent subsequence. -/
theorem exists_subseq_tendsto_polymerRadonProcessLaw (ϑ : ℝ) (D : Set ℝ)
    (hD : D.Countable) (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    letI : PolishSpace RandomMeasure.PlanePairRadonMeasure :=
      RandomMeasure.polishSpace_positiveRadonMeasure_planePair
    letI : BorelSpace RandomMeasure.PlanePairRadonMeasure :=
      ⟨RandomMeasure.borel_positiveRadonMeasure_eq_comap.symm⟩
    letI : OpensMeasurableSpace RandomMeasure.PlanePairRadonMeasure :=
      ⟨RandomMeasure.borel_positiveRadonMeasure_eq_comap.le⟩
    letI : Countable D := hD.to_subtype
    letI : Countable (PolymerPairIndex D) := inferInstance
    letI : OpensMeasurableSpace
      (PolymerPairIndex D → RandomMeasure.PlanePairRadonMeasure) := inferInstance
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ StrictMono (φ ∘ ψ) ∧
      ∃ Q : ProbabilityMeasure
        (PolymerPairIndex D → RandomMeasure.PlanePairRadonMeasure),
        Tendsto (fun n => polymerRadonProcessLaw ϑ (φ (ψ n)) D) atTop (𝓝 Q) := by
  classical
  letI : PolishSpace RandomMeasure.PlanePairRadonMeasure :=
    RandomMeasure.polishSpace_positiveRadonMeasure_planePair
  letI : BorelSpace RandomMeasure.PlanePairRadonMeasure :=
    ⟨RandomMeasure.borel_positiveRadonMeasure_eq_comap.symm⟩
  letI : OpensMeasurableSpace RandomMeasure.PlanePairRadonMeasure :=
    ⟨RandomMeasure.borel_positiveRadonMeasure_eq_comap.le⟩
  letI : Countable D := hD.to_subtype
  letI : Countable (PolymerPairIndex D) := inferInstance
  letI : OpensMeasurableSpace
    (PolymerPairIndex D → RandomMeasure.PlanePairRadonMeasure) := inferInstance
  obtain ⟨ψ, Q, hψ, hlim⟩ :=
    RandomMeasure.exists_subseq_tendsto_of_tight_reindexing_probability_laws
      (fun N => polymerRadonProcessLaw ϑ N D)
      (isTight_polymerRadonProcessLaws ϑ D hD) φ
  exact ⟨ψ, hψ, hφ.comp hψ, Q, hlim⟩







/-- The polymer density is integrable in disorder at each fixed pair of continuum endpoints. -/
theorem integrable_rescaledP2P_disorder (ϑ : ℝ) (N : ℕ) (s t : ℝ)
    (p : Plane × Plane) :
    Integrable (fun ω => rescaledP2P ϑ N s t p ω) disorderLaw := by
  change Integrable (fun ω => (N : ℝ) / 4 *
    pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s))
      (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s))
      (latticePoint N p.1) (latticePoint N p.2) ω) disorderLaw
  exact (Polymer.integrable_pointToPoint (criticalBeta ϑ N)
    (evenCeil ((N : ℝ) * s))
    (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s))
    (latticePoint N p.1) (latticePoint N p.2)).const_mul _

/-- A translated Gaussian with positive quadratic decay is Lebesgue-integrable on the plane. -/
private theorem integrable_exp_neg_sq_norm (a : ℝ) (ha : 0 < a) (x : Plane) :
    Integrable (fun y : Plane => Real.exp (-a * ‖y - x‖ ^ 2)) volume := by
  let u := (2 * a)⁻¹
  have hu : 0 < u := by dsimp [u]; positivity
  let F : Plane → ℝ := fun z => Real.exp (-a * ‖z‖ ^ 2)
  have hbase : Integrable F volume := by
    have hheat := (Critical2DKPZ.integrable_heatKernel hu).const_mul (2 * Real.pi * u)
    have heq (z : Plane) : F z = (2 * Real.pi * u) * Critical2DKPZ.heatKernel u z := by
      change Real.exp (-a * ‖z‖ ^ 2) = _
      rw [Critical2DKPZ.heatKernel_eq_exp]
      dsimp [u]
      field_simp
    exact hheat.congr (Filter.Eventually.of_forall fun z => (heq z).symm)
  let e : Plane ≃ᵐ Plane := MeasurableEquiv.subLeft x
  have hcomp : Integrable (fun y : Plane => F (x - y)) volume := by
    change Integrable (F ∘ e) volume
    exact (volume.measurePreserving_sub_left x).integrable_comp_emb
      e.measurableEmbedding |>.mpr hbase
  have hfun : (fun y : Plane => Real.exp (-a * ‖y - x‖ ^ 2)) =
      fun y => F (x - y) := by
    funext y
    simp only [F]
    rw [norm_sub_rev]
  rw [hfun]
  exact hcomp

/-- For centers in a bounded set, the tail integrals of translated Gaussians vanish uniformly as the radius grows; integrability is supplied by `integrable_exp_neg_sq_norm`. -/
private theorem integral_exp_neg_sq_norm_tail_le (a B R : ℝ) (x : Plane)
    (ha : 0 < a) (hx : ‖x‖ ≤ B) (hR : B + 8 ≤ R) :
    ∫ y in {y : Plane | R ≤ ‖y‖}, Real.exp (-a * ‖y - x‖ ^ 2) ≤
      (2 * Real.pi / a) * Real.exp (-a * (R - B) ^ 2 / 2) := by
  let u := (2 * a)⁻¹
  have hu : 0 < u := by dsimp [u]; positivity
  let e : Plane ≃ᵐ Plane := MeasurableEquiv.subLeft x
  let F : Plane → ℝ := fun z => Real.exp (-a * ‖z‖ ^ 2)
  have hbase : Integrable F volume := by
    have hheat := (Critical2DKPZ.integrable_heatKernel hu).const_mul (2 * Real.pi * u)
    have heq (z : Plane) : F z = (2 * Real.pi * u) * Critical2DKPZ.heatKernel u z := by
      change Real.exp (-a * ‖z‖ ^ 2) = _
      rw [Critical2DKPZ.heatKernel_eq_exp]
      dsimp [u]
      field_simp
    exact hheat.congr (Filter.Eventually.of_forall fun z => (heq z).symm)
  have hchange :
      ∫ y in {y : Plane | R ≤ ‖y‖}, F (x - y) =
        ∫ z in e '' {y : Plane | R ≤ ‖y‖}, F z := by
    have hmp := (volume.measurePreserving_sub_left x).restrict_image_emb
      e.measurableEmbedding {y : Plane | R ≤ ‖y‖}
    exact hmp.integral_comp e.measurableEmbedding F
  have hsubset : e '' {y : Plane | R ≤ ‖y‖} ⊆
      {z : Plane | R - B ≤ ‖z‖} := by
    rintro z ⟨y, hy, rfl⟩
    have hnorm : ‖x - y‖ = ‖y - x‖ := norm_sub_rev _ _
    have htriangle : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := norm_le_norm_sub_add _ _
    change R ≤ ‖y‖ at hy
    change R - B ≤ ‖x - y‖
    rw [hnorm]
    linarith [hy, hx, htriangle]
  have hballIntegrable : IntegrableOn F {z : Plane | R - B ≤ ‖z‖} volume :=
    hbase.integrableOn
  have hmono :
      ∫ z in e '' {y : Plane | R ≤ ‖y‖}, F z ≤
        ∫ z in {z : Plane | R - B ≤ ‖z‖}, F z :=
    setIntegral_mono_set hballIntegrable
      (Filter.Eventually.of_forall fun z => (Real.exp_pos _).le)
      (Filter.Eventually.of_forall hsubset)
  have hFheat (z : Plane) : F z = (2 * Real.pi * u) *
      Critical2DKPZ.heatKernel u z := by
    change Real.exp (-a * ‖z‖ ^ 2) = _
    rw [Critical2DKPZ.heatKernel_eq_exp]
    dsimp [u]
    field_simp
  have htail := Critical2DKPZ.integral_heatKernel_tail_le hu (by linarith : 0 ≤ R - B)
  calc
    ∫ y in {y : Plane | R ≤ ‖y‖}, Real.exp (-a * ‖y - x‖ ^ 2) =
        ∫ y in {y : Plane | R ≤ ‖y‖}, F (x - y) := by
          apply integral_congr_ae
          filter_upwards [] with y
          change Real.exp (-a * ‖y - x‖ ^ 2) = Real.exp (-a * ‖x - y‖ ^ 2)
          rw [norm_sub_rev]
    _ = ∫ z in e '' {y : Plane | R ≤ ‖y‖}, F z := hchange
    _ ≤ ∫ z in {z : Plane | R - B ≤ ‖z‖}, F z := hmono
    _ = (2 * Real.pi * u) *
        ∫ z in {z : Plane | R - B ≤ ‖z‖}, Critical2DKPZ.heatKernel u z := by
          calc
            ∫ z in {z : Plane | R - B ≤ ‖z‖}, F z =
                ∫ z in {z : Plane | R - B ≤ ‖z‖},
                  (2 * Real.pi * u) * Critical2DKPZ.heatKernel u z := by
                    apply setIntegral_congr_fun
                      ((isClosed_le continuous_const continuous_norm).measurableSet)
                    intro z hz
                    exact hFheat z
            _ = (2 * Real.pi * u) *
                ∫ z in {z : Plane | R - B ≤ ‖z‖},
                  Critical2DKPZ.heatKernel u z := integral_const_mul _ _
    _ ≤ (2 * Real.pi * u) *
        (2 * Real.exp (-(R - B) ^ 2 / (4 * u))) :=
          mul_le_mul_of_nonneg_left htail (by positivity)
    _ = (2 * Real.pi / a) * Real.exp (-a * (R - B) ^ 2 / 2) := by
          dsimp [u]
          field_simp [ha.ne']
          ; ring_nf

/-- The radial Gaussian tail has the same bound in nonnegative-integral form, with finiteness supplied by `integrable_exp_neg_sq_norm`. -/
private theorem lintegral_exp_neg_sq_norm_tail_le (a R : ℝ) (ha : 0 < a)
    (hR : 8 ≤ R) :
    ∫⁻ y in {y : Plane | R ≤ ‖y‖},
        ENNReal.ofReal (Real.exp (-(a / 2) * ‖y‖ ^ 2)) ≤
      ENNReal.ofReal ((4 * Real.pi / a) * Real.exp (-a * R ^ 2 / 4)) := by
  have hi : Integrable (fun y : Plane => Real.exp (-(a / 2) * ‖y‖ ^ 2)) volume := by
    simpa only [sub_zero] using integrable_exp_neg_sq_norm (a / 2) (by positivity) 0
  have hnonneg : 0 ≤ᵐ[volume.restrict {y : Plane | R ≤ ‖y‖}]
      fun y : Plane => Real.exp (-(a / 2) * ‖y‖ ^ 2) :=
    Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le
  rw [← ofReal_integral_eq_lintegral_ofReal hi.integrableOn hnonneg]
  apply ENNReal.ofReal_le_ofReal
  have hR' : 0 + 8 ≤ R := by simpa using hR
  have hbound := integral_exp_neg_sq_norm_tail_le (a / 2) 0 R 0
    (by positivity) (by norm_num) hR'
  convert hbound using 1
  simp only [sub_zero]
  field_simp [ha.ne']
  ring_nf

/-- The annealed mass in a bounded initial window and outside a growing terminal ball becomes arbitrarily small at sufficiently large lattice scales; pointwise integrability is supplied by `integrable_rescaledP2P_disorder`. -/
private theorem eventually_annealed_rescaledP2P_gaussian_tail_bound
    (ϑ : ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    ∃ C a : ℝ, 0 < C ∧ 0 < a ∧ ∀ᶠ N : ℕ in atTop, ∀ p : Plane × Plane,
      8 ≤ ‖p.2 - p.1‖ →
      ∫ ω, rescaledP2P ϑ N s t p ω ∂disorderLaw ≤
        C * Real.exp (-a * ‖p.2 - p.1‖ ^ 2) := by
  obtain ⟨C₀, c, hC₀, hc, hwalk⟩ :=
    SHF.Moments.srwKernel_gaussianBound_all_times
  let δ := t - s
  let a : ℝ := c / (8 * (δ + 2))
  refine ⟨C₀ / (2 * δ), a, by positivity, by positivity, ?_⟩
  have hratio : Tendsto
      (fun N : ℕ =>
        ((evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s) : ℕ) : ℝ) / N)
      atTop (𝓝 δ) :=
    SHF.Moments.tendsto_evenCeil_gap_div hs hst.le
  filter_upwards [eventually_gt_atTop 0,
    hratio.eventually (Ioo_mem_nhds (a := δ / 2) (b := δ + 1)
      (by dsimp [δ]; linarith) (by dsimp [δ]; linarith))] with N hN hwindow
  intro p hp
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast hN
  let n := evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)
  have hlow : δ / 2 * N < (n : ℝ) := by
    have h := hwindow.1
    dsimp [n] at h ⊢
    rw [lt_div_iff₀ hNr] at h
    nlinarith
  have hupp : (n : ℝ) < (δ + 1) * N := by
    have h := hwindow.2
    dsimp [n] at h ⊢
    rw [div_lt_iff₀ hNr] at h
    nlinarith
  have hnlow : δ / 2 * N ≤ (n : ℝ) + 1 := by linarith
  have hnupp : (n : ℝ) + 1 ≤ (δ + 2) * N := by nlinarith
  have hwalk' := hwalk n (latticePoint N p.2 - latticePoint N p.1)
  have hkernel :
      srwKernel n (latticePoint N p.2 - latticePoint N p.1) ≤
        C₀ / ((n : ℝ) + 1) *
          Real.exp (-c * ‖siteToPlane (latticePoint N p.2 - latticePoint N p.1)‖ ^ 2 /
            ((n : ℝ) + 1)) := hwalk'
  rw [SHF.Moments.integral_rescaledP2P]
  have hsample (x : Plane) :
      dist (Critical2DKPZ.cellSample N x) x ≤ 2 :=
    Critical2DKPZ.dist_cellSample_le_two hN x
  have hdist :
      ‖p.2 - p.1‖ / 2 ≤
        dist (Critical2DKPZ.cellSample N p.2) (Critical2DKPZ.cellSample N p.1) := by
    have htri := dist_triangle4 p.2 (Critical2DKPZ.cellSample N p.2)
      (Critical2DKPZ.cellSample N p.1) p.1
    have hreverse :
        ‖p.2 - p.1‖ = dist p.2 p.1 := by
      simp [dist_eq_norm]
    have hfirst : dist p.2 (Critical2DKPZ.cellSample N p.2) ≤ 2 := by
      simpa only [dist_comm] using hsample p.2
    have hlast : dist (Critical2DKPZ.cellSample N p.1) p.1 ≤ 2 := hsample p.1
    have hbound : ‖p.2 - p.1‖ ≤
        2 + dist (Critical2DKPZ.cellSample N p.2) (Critical2DKPZ.cellSample N p.1) + 2 := by
      calc
        ‖p.2 - p.1‖ = dist p.2 p.1 := hreverse
        _ ≤ dist p.2 (Critical2DKPZ.cellSample N p.2) +
            dist (Critical2DKPZ.cellSample N p.2) (Critical2DKPZ.cellSample N p.1) +
            dist (Critical2DKPZ.cellSample N p.1) p.1 := htri
        _ ≤ _ := by linarith
    calc
      ‖p.2 - p.1‖ / 2 ≤ ‖p.2 - p.1‖ - 4 := by linarith [hp]
      _ ≤ dist (Critical2DKPZ.cellSample N p.2) (Critical2DKPZ.cellSample N p.1) := by
        linarith [hbound]
  have hsqrt : 0 < Real.sqrt (N / 2) := Real.sqrt_pos.mpr (by positivity)
  have hsite :
      siteToPlane (latticePoint N p.2 - latticePoint N p.1) =
        Real.sqrt (N / 2) •
          (Critical2DKPZ.cellSample N p.2 - Critical2DKPZ.cellSample N p.1) := by
    have hrep := SHF.Moments.latticeRepresentative_sub N
      (latticePoint N p.2) (latticePoint N p.1)
    have hscale (z : Site) :
        Real.sqrt (N / 2) • Critical2DKPZ.latticeRepresentative N z =
          siteToPlane z := by
      dsimp [Critical2DKPZ.latticeRepresentative]
      rw [smul_smul, mul_inv_cancel₀ hsqrt.ne', one_smul]
    calc
      siteToPlane (latticePoint N p.2 - latticePoint N p.1) =
          Real.sqrt (N / 2) •
            Critical2DKPZ.latticeRepresentative N
              (latticePoint N p.2 - latticePoint N p.1) :=
        (hscale (latticePoint N p.2 - latticePoint N p.1)).symm
      _ = Real.sqrt (N / 2) •
          (Critical2DKPZ.latticeRepresentative N (latticePoint N p.2) -
            Critical2DKPZ.latticeRepresentative N (latticePoint N p.1)) := by rw [hrep]
      _ = _ := by rfl
  have hsiteNorm :
      ‖siteToPlane (latticePoint N p.2 - latticePoint N p.1)‖ ^ 2 =
        (N : ℝ) / 2 *
          dist (Critical2DKPZ.cellSample N p.2)
            (Critical2DKPZ.cellSample N p.1) ^ 2 := by
    rw [hsite, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hdistNorm :
        ‖Critical2DKPZ.cellSample N p.2 - Critical2DKPZ.cellSample N p.1‖ =
          dist (Critical2DKPZ.cellSample N p.2) (Critical2DKPZ.cellSample N p.1) := by
      rw [dist_eq_norm]
    rw [hdistNorm, mul_pow, Real.sq_sqrt (by positivity)]
  have hexp_arg :
      -c * ‖siteToPlane (latticePoint N p.2 - latticePoint N p.1)‖ ^ 2 /
          ((n : ℝ) + 1) ≤ -a * ‖p.2 - p.1‖ ^ 2 := by
    rw [hsiteNorm]
    let d := dist (Critical2DKPZ.cellSample N p.2) (Critical2DKPZ.cellSample N p.1)
    let r := ‖p.2 - p.1‖
    have hdSq : r ^ 2 / 4 ≤ d ^ 2 := by
      dsimp [d, r]
      nlinarith [sq_nonneg
        (dist (Critical2DKPZ.cellSample N p.2) (Critical2DKPZ.cellSample N p.1) -
          ‖p.2 - p.1‖ / 2)]
    have hratio : 1 / (δ + 2) ≤ (N : ℝ) / ((n : ℝ) + 1) := by
      rw [div_le_div_iff₀ (by positivity : 0 < δ + 2)
        (by positivity : 0 < (n : ℝ) + 1)]
      nlinarith [hnupp]
    have hprod := mul_le_mul hratio hdSq (by positivity) (by positivity)
    have hcore : a * r ^ 2 ≤ c * ((N : ℝ) / 2 * d ^ 2) / ((n : ℝ) + 1) := by
      calc
        a * r ^ 2 = (c / 2) * (1 / (δ + 2) * (r ^ 2 / 4)) := by
          dsimp [a]
          field_simp
          ring
        _ ≤ (c / 2) * ((N : ℝ) / ((n : ℝ) + 1) * d ^ 2) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = c * ((N : ℝ) / 2 * d ^ 2) / ((n : ℝ) + 1) := by
          field_simp
    dsimp [d, r] at hcore ⊢
    calc
      -c * ((N : ℝ) / 2 *
          dist (Critical2DKPZ.cellSample N p.2) (Critical2DKPZ.cellSample N p.1) ^ 2) /
          ((n : ℝ) + 1) =
          -(c * ((N : ℝ) / 2 *
            dist (Critical2DKPZ.cellSample N p.2) (Critical2DKPZ.cellSample N p.1) ^ 2) /
            ((n : ℝ) + 1)) := by ring
      _ ≤ -(a * ‖p.2 - p.1‖ ^ 2) := neg_le_neg hcore
      _ = -a * ‖p.2 - p.1‖ ^ 2 := by ring
  have hcoeff :
      (N : ℝ) / 4 * (C₀ / ((n : ℝ) + 1)) ≤ C₀ / (2 * δ) := by
    have hden : δ * N / 2 ≤ (n : ℝ) + 1 := by
      nlinarith [hnlow]
    have hrecip : C₀ / ((n : ℝ) + 1) ≤ C₀ / (δ * N / 2) := by
      apply (div_le_div_iff₀ (by positivity : 0 < (n : ℝ) + 1)
        (by positivity : 0 < δ * N / 2)).2
      have hmul := mul_le_mul_of_nonneg_left hden hC₀.le
      nlinarith [hmul]
    calc
      (N : ℝ) / 4 * (C₀ / ((n : ℝ) + 1)) ≤
          (N : ℝ) / 4 * (C₀ / (δ * N / 2)) :=
        mul_le_mul_of_nonneg_left hrecip (by positivity)
      _ = C₀ / (2 * δ) := by
        field_simp [hNr.ne', (sub_pos.mpr hst).ne']
        ; ring
  have hExpLe :
      Real.exp (-c * ‖siteToPlane (latticePoint N p.2 - latticePoint N p.1)‖ ^ 2 /
          ((n : ℝ) + 1)) ≤ Real.exp (-a * ‖p.2 - p.1‖ ^ 2) :=
    Real.exp_le_exp.mpr hexp_arg
  calc
    (N : ℝ) / 4 *
        srwKernel n (latticePoint N p.2 - latticePoint N p.1) ≤
        (N : ℝ) / 4 *
          (C₀ / ((n : ℝ) + 1) *
            Real.exp (-c * ‖siteToPlane (latticePoint N p.2 - latticePoint N p.1)‖ ^ 2 /
              ((n : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left hkernel (by positivity)
    _ ≤ C₀ / (2 * δ) * Real.exp (-a * ‖p.2 - p.1‖ ^ 2) := by
      calc
        (N : ℝ) / 4 *
            (C₀ / ((n : ℝ) + 1) *
              Real.exp (-c * ‖siteToPlane (latticePoint N p.2 - latticePoint N p.1)‖ ^ 2 /
                ((n : ℝ) + 1))) =
            ((N : ℝ) / 4 * (C₀ / ((n : ℝ) + 1))) *
              Real.exp (-c * ‖siteToPlane (latticePoint N p.2 - latticePoint N p.1)‖ ^ 2 /
                ((n : ℝ) + 1)) := by ring
        _ ≤ C₀ / (2 * δ) * Real.exp (-a * ‖p.2 - p.1‖ ^ 2) :=
          mul_le_mul hcoeff hExpLe (Real.exp_nonneg _) (by positivity)

/-- For `R ≥ B + 8`, the annealed point-to-point mass from `x ∈ A`, with `‖x‖ ≤ B`, to `‖y‖ ≥ R` is eventually at most `C exp (a B²) · (4π/a) exp (-a R² / 4) · volume A`, with `C` and `a` independent of `R`. -/
private theorem eventually_lintegral_annealed_rescaledP2P_pair_tail_le
    (ϑ : ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (A : Set Plane)
    (B : ℝ) (hB : 0 ≤ B) (hAbox : ∀ x ∈ A, ‖x‖ ≤ B) :
    ∃ C a : ℝ, 0 < C ∧ 0 < a ∧ ∀ R, B + 8 ≤ R → ∀ᶠ N : ℕ in atTop,
      ∫⁻ x in A, ∫⁻ y in {y : Plane | R ≤ ‖y‖},
        ENNReal.ofReal (∫ ω, rescaledP2P ϑ N s t (x, y) ω ∂disorderLaw) ∂volume ∂volume ≤
        ENNReal.ofReal (C * Real.exp (a * B ^ 2)) *
          ENNReal.ofReal ((4 * Real.pi / a) * Real.exp (-a * R ^ 2 / 4)) *
            volume A := by
  obtain ⟨C, a, hC, ha, hpoint⟩ :=
    eventually_annealed_rescaledP2P_gaussian_tail_bound ϑ hs hst
  refine ⟨C, a, hC, ha, ?_⟩
  intro R hR
  have hradial := lintegral_exp_neg_sq_norm_tail_le a R ha
    (by linarith [hR])
  filter_upwards [hpoint] with N hpoint
  let T : Set Plane := {y : Plane | R ≤ ‖y‖}
  let K : ℝ≥0∞ := ENNReal.ofReal (C * Real.exp (a * B ^ 2))
  let g : Plane → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp (-(a / 2) * ‖y‖ ^ 2))
  have hpointwise (x y : Plane) (hx : x ∈ A) (hy : y ∈ T) :
      ENNReal.ofReal (∫ ω, rescaledP2P ϑ N s t (x, y) ω ∂disorderLaw) ≤ K * g y := by
    change R ≤ ‖y‖ at hy
    have hdist : 8 ≤ ‖y - x‖ := by
      have htri : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := norm_le_norm_sub_add y x
      linarith [hAbox x hx, hR]
    have hmean := hpoint (x, y) hdist
    have hquad : ‖y‖ ^ 2 / 2 - ‖x‖ ^ 2 ≤ ‖y - x‖ ^ 2 := by
      have htri : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := norm_le_norm_sub_add y x
      nlinarith [sq_nonneg (‖y - x‖ - ‖x‖)]
    have hxSq : ‖x‖ ^ 2 ≤ B ^ 2 := by
      have hxnonneg := norm_nonneg x
      nlinarith [hAbox x hx]
    have hscaled := mul_le_mul_of_nonneg_left hquad ha.le
    have hxscaled := mul_le_mul_of_nonneg_left hxSq ha.le
    have harg : -a * ‖y - x‖ ^ 2 ≤ a * B ^ 2 - (a / 2) * ‖y‖ ^ 2 := by
      nlinarith [hscaled, hxscaled]
    have hexp : Real.exp (-a * ‖y - x‖ ^ 2) ≤
        Real.exp (a * B ^ 2) * Real.exp (-(a / 2) * ‖y‖ ^ 2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [harg]
    have hmean' : ∫ ω, rescaledP2P ϑ N s t (x, y) ω ∂disorderLaw ≤
        C * (Real.exp (a * B ^ 2) * Real.exp (-(a / 2) * ‖y‖ ^ 2)) := by
      calc
        _ ≤ C * Real.exp (-a * ‖y - x‖ ^ 2) :=
          hmean.trans_eq (by ring)
        _ ≤ _ := mul_le_mul_of_nonneg_left hexp hC.le
    calc
      ENNReal.ofReal (∫ ω, rescaledP2P ϑ N s t (x, y) ω ∂disorderLaw) ≤
          ENNReal.ofReal (C * (Real.exp (a * B ^ 2) *
            Real.exp (-(a / 2) * ‖y‖ ^ 2))) := ENNReal.ofReal_le_ofReal hmean'
      _ = K * g y := by
            dsimp [K, g]
            rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ C * Real.exp (a * B ^ 2))]
            congr 1
            ring
  have htailMeas : Measurable g := by
    dsimp [g]
    exact ENNReal.measurable_ofReal.comp
      ((Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2))).measurable)
  have hinner (x : Plane) :
      ∫⁻ y in T, K * g y ∂volume = K * ∫⁻ y in T, g y ∂volume := by
    rw [lintegral_const_mul'' K htailMeas.aemeasurable]
  have houter (x : Plane) :
      ∫⁻ y in T, g y ∂volume ≤
        ENNReal.ofReal ((4 * Real.pi / a) * Real.exp (-a * R ^ 2 / 4)) := by
    exact hradial
  calc
    ∫⁻ x in A, ∫⁻ y in T,
        ENNReal.ofReal (∫ ω, rescaledP2P ϑ N s t (x, y) ω ∂disorderLaw)
          ∂volume ∂volume ≤
      ∫⁻ x in A, K * ∫⁻ y in T, g y ∂volume ∂volume := by
        apply setLIntegral_mono measurable_const
        intro x hx
        calc
          ∫⁻ y in T,
              ENNReal.ofReal (∫ ω, rescaledP2P ϑ N s t (x, y) ω ∂disorderLaw)
                ∂volume ≤ ∫⁻ y in T, K * g y ∂volume :=
                  setLIntegral_mono' (isClosed_le continuous_const continuous_norm).measurableSet
                    (fun y hy => hpointwise x y hx hy)
          _ = K * ∫⁻ y in T, g y ∂volume := hinner x
    _ ≤ ∫⁻ x in A, K * ENNReal.ofReal
          ((4 * Real.pi / a) * Real.exp (-a * R ^ 2 / 4)) ∂volume := by
          apply setLIntegral_mono measurable_const
          intro x hx
          simpa [mul_comm] using mul_le_mul_left (houter x) K
    _ = ENNReal.ofReal (C * Real.exp (a * B ^ 2)) *
          ENNReal.ofReal ((4 * Real.pi / a) * Real.exp (-a * R ^ 2 / 4)) * volume A := by
          rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]

/-- The expected polymer mass of a bounded initial window and a distant terminal tail obeys the Gaussian tail bound; `integrable_rescaledP2P_disorder` identifies its density expectation with the annealed integral. -/
theorem eventually_expected_polymerMeasure_pair_tail_le
    (ϑ : ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (A : Set Plane)
    (hA : MeasurableSet A) (B : ℝ) (hB : 0 ≤ B)
    (hAbox : ∀ x ∈ A, ‖x‖ ≤ B) :
    ∃ C a : ℝ, 0 < C ∧ 0 < a ∧ ∀ R, B + 8 ≤ R → ∀ᶠ N : ℕ in atTop,
      ∫⁻ ω, polymerMeasure ϑ N s t ω
        (A ×ˢ {y : Plane | R ≤ ‖y‖}) ∂disorderLaw ≤
        ENNReal.ofReal (C * Real.exp (a * B ^ 2)) *
          ENNReal.ofReal ((4 * Real.pi / a) * Real.exp (-a * R ^ 2 / 4)) * volume A := by
  obtain ⟨C, a, hC, ha, hbound⟩ :=
    eventually_lintegral_annealed_rescaledP2P_pair_tail_le
      ϑ hs hst A B hB hAbox
  refine ⟨C, a, hC, ha, ?_⟩
  intro R hR
  let T : Set Plane := {y : Plane | R ≤ ‖y‖}
  let S : Set (Plane × Plane) := A ×ˢ T
  have hT : MeasurableSet T := (isClosed_le continuous_const continuous_norm).measurableSet
  have hS : MeasurableSet S := hA.prod hT
  have hdens (N : ℕ) : Measurable (fun q : Disorder × (Plane × Plane) =>
      ENNReal.ofReal (rescaledP2P ϑ N s t q.2 q.1)) := by
    have hbase : Measurable (fun q : (Plane × Plane) × Disorder =>
        ENNReal.ofReal (rescaledP2P ϑ N s t q.1 q.2)) :=
      ENNReal.measurable_ofReal.comp
        (SHF.Moments.measurable_uncurry_rescaledP2P ϑ N s t)
    convert hbase.comp measurable_swap using 1
    funext q
    rfl
  let F (N : ℕ) : Disorder → Plane × Plane → ℝ≥0∞ := fun ω p =>
    S.indicator (fun p => ENNReal.ofReal (rescaledP2P ϑ N s t p ω)) p
  have hF (N : ℕ) : Measurable (Function.uncurry (F N)) := by
    dsimp [F]
    exact (hdens N).indicator (hS.preimage measurable_snd)
  have hkernel (N : ℕ) (p : Plane × Plane) :
      ∫⁻ ω, ENNReal.ofReal (rescaledP2P ϑ N s t p ω) ∂disorderLaw =
        ENNReal.ofReal (∫ ω, rescaledP2P ϑ N s t p ω ∂disorderLaw) := by
    have hnonneg : 0 ≤ᵐ[disorderLaw] fun ω => rescaledP2P ϑ N s t p ω :=
      Filter.Eventually.of_forall fun ω => (SHF.Moments.rescaledP2P_nonneg ..)
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_rescaledP2P_disorder ϑ N s t p) hnonneg]
  have hmeanMeas (N : ℕ) : Measurable (fun p : Plane × Plane =>
      ENNReal.ofReal (∫ ω, rescaledP2P ϑ N s t p ω ∂disorderLaw)) :=
    ENNReal.measurable_ofReal.comp (SHF.Moments.measurable_integral_rescaledP2P ϑ N s t)
  filter_upwards [hbound R hR] with N hbound
  have hmass : ∫⁻ ω, polymerMeasure ϑ N s t ω S ∂disorderLaw =
      ∫⁻ p in S, ENNReal.ofReal
        (∫ ω, rescaledP2P ϑ N s t p ω ∂disorderLaw) ∂volume := by
    calc
      ∫⁻ ω, polymerMeasure ϑ N s t ω S ∂disorderLaw =
          ∫⁻ ω, ∫⁻ p, F N ω p ∂volume ∂disorderLaw := by
            apply lintegral_congr_ae
            filter_upwards [] with ω
            rw [polymerMeasure, withDensity_apply _ hS, ← lintegral_indicator hS]
      _ = ∫⁻ p, ∫⁻ ω, F N ω p ∂disorderLaw ∂volume :=
            lintegral_lintegral_swap (hF N).aemeasurable
      _ = ∫⁻ p, S.indicator (fun p => ENNReal.ofReal
            (∫ ω, rescaledP2P ϑ N s t p ω ∂disorderLaw)) p ∂volume := by
            apply lintegral_congr_ae
            filter_upwards [] with p
            by_cases hp : p ∈ S
            · simp [F, hp, hkernel N p]
            · simp [F, hp]
      _ = ∫⁻ p in S, ENNReal.ofReal
            (∫ ω, rescaledP2P ϑ N s t p ω ∂disorderLaw) ∂volume := by
            rw [lintegral_indicator hS]
  have hproduct : ∫⁻ p in S, ENNReal.ofReal
        (∫ ω, rescaledP2P ϑ N s t p ω ∂disorderLaw) ∂volume =
      ∫⁻ x in A, ∫⁻ y in T, ENNReal.ofReal
        (∫ ω, rescaledP2P ϑ N s t (x, y) ω ∂disorderLaw) ∂volume ∂volume := by
    calc
      ∫⁻ p in S, ENNReal.ofReal
          (∫ ω, rescaledP2P ϑ N s t p ω ∂disorderLaw) ∂volume =
          ∫⁻ p, S.indicator (fun p => ENNReal.ofReal
            (∫ ω, rescaledP2P ϑ N s t p ω ∂disorderLaw)) p ∂volume := by
              rw [← lintegral_indicator hS]
      _ = ∫⁻ x, ∫⁻ y, S.indicator (fun p => ENNReal.ofReal
            (∫ ω, rescaledP2P ϑ N s t p ω ∂disorderLaw)) (x, y)
            ∂volume ∂volume := by
              rw [Measure.volume_eq_prod, lintegral_prod _
                ((hmeanMeas N).indicator hS).aemeasurable]
      _ = ∫⁻ x in A, ∫⁻ y in T, ENNReal.ofReal
            (∫ ω, rescaledP2P ϑ N s t (x, y) ω ∂disorderLaw) ∂volume ∂volume := by
              rw [← lintegral_indicator hA]
              apply lintegral_congr_ae
              filter_upwards [] with x
              by_cases hx : x ∈ A
              · rw [Set.indicator_of_mem hx, ← lintegral_indicator hT]
                apply lintegral_congr_ae
                filter_upwards [] with y
                by_cases hy : y ∈ T <;> simp [S, Set.indicator, hx, hy]
              · rw [Set.indicator_of_notMem hx]
                simp [S, Set.indicator, hx]
  rw [hmass, hproduct]
  exact hbound


end Critical2DKPZ.SHF.Limit

end
