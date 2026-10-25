/- 
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.PairingSlabComparisonSlabIdentity
public import Critical2DKPZ.SHF.Flow.ThinSlabSeparatedMassBound
public import Critical2DKPZ.SHF.Flow.ThinSlabSmoothedSlabConnector
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Defs
import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

/-! # Convergence of the cut-off slab connector moment -/

@[expose] public noncomputable section

open MeasureTheory Filter
open ProbabilityTheory
open BoundedContinuousFunction
open Critical2DKPZ.SHF.Limit
open Critical2DKPZ.SHF.Tsai
open scoped CompactlySupported Topology BoundedContinuousFunction

namespace Critical2DKPZ.SHF.Flow

private theorem measurable_integral_as_function_of_measure_for_slab_comparison {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] (f : X → ℝ) (hf : StronglyMeasurable f) :
    Measurable (fun μ : Measure X => ∫ x, f x ∂μ) := by
  let κ : Kernel (Measure X) X := ⟨id, measurable_id⟩
  exact (hf.integral_kernel (κ := κ)).measurable

private def pairingCompactTestToBoundedContinuous {X : Type*} [TopologicalSpace X]
    (f : C_c(X, ℝ)) : X →ᵇ ℝ := ofCompactSupport f f.continuous f.hasCompactSupport

/-- At fixed positive slab width and cutoff, the finite replica connector moment converges to the compact heat-connector moment, with eventual integrability supplied by `eventually_slabSeparatedTensorMass_sq_bound`. -/
theorem tendsto_slabCutoffReplicaMoment (ϑ : ℝ)
    (hPolymerMomentInput : PolymerMomentLimit ϑ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
    {s t u : ℝ} (hs : 0 ≤ s) (hst : s < t) (_htu : t < u)
    {v : ℝ} (hv : 0 < v) (hvu : t + v < u)
    (Φ : C_c(Plane × Plane, ℝ)) (R : ℝ) :
    Tendsto
      (fun N => ∫ ω, ∫ q,
        slabCutoffReplicaValue ϑ N t v R Φ q ∂
          slabTwoBlockPiMeasure (polymerMeasure ϑ N s t ω)
            (polymerMeasure ϑ N (t + v) u ω) ∂disorderLaw)
      atTop
      (𝓝 (slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant)
        (t - s) (u - (t + v)) (slabHeatCutoffReplicaTest v R Φ))) := by
  classical
  let χ : C_c(Plane, ℝ) := ⟨⟨ballCutoff R, continuous_ballCutoff R⟩,
    hasCompactSupport_ballCutoff R⟩
  let A : Set Plane := Prod.fst '' tsupport (Φ : (Plane × Plane) → ℝ)
  let B : Set Plane := Prod.snd '' tsupport (Φ : (Plane × Plane) → ℝ)
  let C : Set Plane := tsupport (χ : Plane → ℝ)
  let K : Set (Plane × Plane) := (A ∪ C) ×ˢ (C ∪ B)
  let K4 : Set (Fin 4 → Plane × Plane) := Set.univ.pi fun _ => K
  have hA : IsCompact A := Φ.hasCompactSupport.image continuous_fst
  have hB : IsCompact B := Φ.hasCompactSupport.image continuous_snd
  have hC : IsCompact C := χ.hasCompactSupport
  have hK : IsCompact K := (hA.union hC).prod (hC.union hB)
  have hK4 : IsCompact K4 := isCompact_univ_pi fun _ => hK
  obtain ⟨g, g', hg, hg', hone⟩ := exists_compactTensor_majorant K hK
  let ρ : C_c(Plane × Plane, ℝ) := compactTensorTest g g'
  have hρnonneg (p : Plane × Plane) : 0 ≤ ρ p := by
    simp only [ρ, compactTensorTest_apply]
    exact mul_nonneg (hg _) (hg' _)
  have hρone (p : Plane × Plane) (hp : p ∈ K) : ρ p = 1 := hone p hp
  let T : C_c((Fin 4 → Plane × Plane), ℝ) := slabCompactPiTensorTest (fun _ => ρ)
  have hTnonneg (q : Fin 4 → Plane × Plane) : 0 ≤ T q := by
    simp only [T, slabCompactPiTensorTest_apply]
    exact Finset.prod_nonneg fun i hi => hρnonneg (q i)
  have hTone (q : Fin 4 → Plane × Plane) (hq : q ∈ K4) : T q = 1 := by
    simp only [T, slabCompactPiTensorTest_apply]
    apply Finset.prod_eq_one
    intro i hi
    exact hρone (q i) ((Set.mem_univ_pi.mp hq) i)
  have hslabConnCoords (N : ℕ) (a b : Plane × Plane)
      (hconn : slabCutoffConnectorValue ϑ N t v R Φ a b ≠ 0) :
      a.1 ∈ A ∧ a.2 ∈ C ∧ b.1 ∈ C ∧ b.2 ∈ B := by
    have hΦ : Φ (a.1, b.2) ≠ 0 := by
      intro hzero
      apply hconn
      simp [slabCutoffConnectorValue, hzero]
    have hχ₁ : ballCutoff R a.2 ≠ 0 := by
      intro hzero
      apply hconn
      simp [slabCutoffConnectorValue, hzero]
    have hχ₂ : ballCutoff R b.1 ≠ 0 := by
      intro hzero
      apply hconn
      simp [slabCutoffConnectorValue, hzero]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact ⟨(a.1, b.2), subset_tsupport _ hΦ, rfl⟩
    · apply subset_tsupport χ
      simpa [χ] using hχ₁
    · apply subset_tsupport χ
      simpa [χ] using hχ₂
    · exact ⟨(a.1, b.2), subset_tsupport _ hΦ, rfl⟩
  have hslabZero (N : ℕ) (q : Fin 4 → Plane × Plane) (hq : q ∉ K4) :
      slabCutoffReplicaValue ϑ N t v R Φ q = 0 := by
    by_contra hne
    have h02 : slabCutoffConnectorValue ϑ N t v R Φ (q 0) (q 2) ≠ 0 := by
      intro hz
      apply hne
      simp [slabCutoffReplicaValue, hz]
    have h13 : slabCutoffConnectorValue ϑ N t v R Φ (q 1) (q 3) ≠ 0 := by
      intro hz
      apply hne
      simp [slabCutoffReplicaValue, hz]
    have h02' := hslabConnCoords N (q 0) (q 2) h02
    have h13' := hslabConnCoords N (q 1) (q 3) h13
    have hmem : q ∈ K4 := by
      apply Set.mem_univ_pi.mpr
      intro i
      fin_cases i
      · exact ⟨Set.mem_union_left C h02'.1, Set.mem_union_left B h02'.2.1⟩
      · exact ⟨Set.mem_union_left C h13'.1, Set.mem_union_left B h13'.2.1⟩
      · exact ⟨Set.mem_union_right A h02'.2.2.1, Set.mem_union_right C h02'.2.2.2⟩
      · exact ⟨Set.mem_union_right A h13'.2.2.1, Set.mem_union_right C h13'.2.2.2⟩
    exact hq hmem
  have hheatConnCoords (a b : Plane × Plane)
      (hconn : slabHeatCutoffConnectorValue v R Φ a b ≠ 0) :
      a.1 ∈ A ∧ a.2 ∈ C ∧ b.1 ∈ C ∧ b.2 ∈ B := by
    have hΦ : Φ (a.1, b.2) ≠ 0 := by
      intro hzero
      apply hconn
      simp [slabHeatCutoffConnectorValue, hzero]
    have hχ₁ : ballCutoff R a.2 ≠ 0 := by
      intro hzero
      apply hconn
      simp [slabHeatCutoffConnectorValue, hzero]
    have hχ₂ : ballCutoff R b.1 ≠ 0 := by
      intro hzero
      apply hconn
      simp [slabHeatCutoffConnectorValue, hzero]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact ⟨(a.1, b.2), subset_tsupport _ hΦ, rfl⟩
    · apply subset_tsupport χ
      simpa [χ] using hχ₁
    · apply subset_tsupport χ
      simpa [χ] using hχ₂
    · exact ⟨(a.1, b.2), subset_tsupport _ hΦ, rfl⟩
  have hheatZero (q : Fin 4 → Plane × Plane) (hq : q ∉ K4) :
      slabHeatCutoffReplicaTest v R Φ q = 0 := by
    by_contra hne
    have h02 : slabHeatCutoffConnectorValue v R Φ (q 0) (q 2) ≠ 0 := by
      intro hz
      apply hne
      rw [slabHeatCutoffReplicaTest_apply]
      simp [hz]
    have h13 : slabHeatCutoffConnectorValue v R Φ (q 1) (q 3) ≠ 0 := by
      intro hz
      apply hne
      rw [slabHeatCutoffReplicaTest_apply]
      simp [hz]
    have h02' := hheatConnCoords (q 0) (q 2) h02
    have h13' := hheatConnCoords (q 1) (q 3) h13
    have hmem : q ∈ K4 := by
      apply Set.mem_univ_pi.mpr
      intro i
      fin_cases i
      · exact ⟨Set.mem_union_left C h02'.1, Set.mem_union_left B h02'.2.1⟩
      · exact ⟨Set.mem_union_left C h13'.1, Set.mem_union_left B h13'.2.1⟩
      · exact ⟨Set.mem_union_right A h02'.2.2.1, Set.mem_union_right C h02'.2.2.2⟩
      · exact ⟨Set.mem_union_right A h13'.2.2.1, Set.mem_union_right C h13'.2.2.2⟩
    exact hq hmem
  have hHNmeas (N : ℕ) : Measurable (slabCutoffReplicaValue ϑ N t v R Φ) := by
    have hΦ : Measurable (fun p : (Plane × Plane) × (Plane × Plane) =>
        Φ (p.1.1, p.2.2)) := by fun_prop
    have hκarg : Measurable (fun p : (Plane × Plane) × (Plane × Plane) =>
        (p.1.2, p.2.1)) := by fun_prop
    have hκ := (measurable_slabMeanKernel ϑ N t (t + v)).comp hκarg
    have hcut₁ : Measurable (fun p : (Plane × Plane) × (Plane × Plane) =>
        ballCutoff R p.1.2) := (continuous_ballCutoff R).measurable.comp (by fun_prop)
    have hcut₂ : Measurable (fun p : (Plane × Plane) × (Plane × Plane) =>
        ballCutoff R p.2.1) := (continuous_ballCutoff R).measurable.comp (by fun_prop)
    have hconn : Measurable (fun p : (Plane × Plane) × (Plane × Plane) =>
        slabCutoffConnectorValue ϑ N t v R Φ p.1 p.2) := by
      exact hΦ.mul hκ |>.mul hcut₁ |>.mul hcut₂
    have hpair02 : Measurable (fun q : Fin 4 → Plane × Plane => (q 0, q 2)) := by
      fun_prop
    have hpair13 : Measurable (fun q : Fin 4 → Plane × Plane => (q 1, q 3)) := by
      fun_prop
    exact (hconn.comp hpair02).mul (hconn.comp hpair13)
  have hheatMeas : Measurable (slabHeatCutoffReplicaTest v R Φ) :=
    (slabHeatCutoffReplicaTest v R Φ).continuous.measurable
  let πN : ℕ → Disorder → Measure (Fin 4 → Plane × Plane) := fun N ω =>
    slabTwoBlockPiMeasure (polymerMeasure ϑ N s t ω)
      (polymerMeasure ϑ N (t + v) u ω)
  have hπMeas (N : ℕ) : Measurable (πN N) := by
    rw [show πN N = fun ω => Measure.pi (fun i : Fin 4 =>
      if i.val < 2 then polymerMeasure ϑ N s t ω
      else polymerMeasure ϑ N (t + v) u ω) from rfl]
    exact measurable_piMeasure_of_locallyFinite 4
      (fun i ω => if i.val < 2 then polymerMeasure ϑ N s t ω
        else polymerMeasure ϑ N (t + v) u ω)
      (by intro i; split_ifs <;> exact measurable_polymerMeasure ϑ N _ _)
      (by intro i ω; split_ifs <;> exact isLocallyFiniteMeasure_polymerMeasure ϑ N _ _ ω)
  have hSigma (N : ℕ) (ω : Disorder) :
      SigmaFinite (polymerMeasure ϑ N s t ω) ∧
        SigmaFinite (polymerMeasure ϑ N (t + v) u ω) := by
    exact ⟨@MeasureTheory.sigmaFinite_of_locallyFinite (Plane × Plane) _
      (polymerMeasure ϑ N s t ω) inferInstance inferInstance
      (isLocallyFiniteMeasure_polymerMeasure ϑ N s t ω),
      @MeasureTheory.sigmaFinite_of_locallyFinite (Plane × Plane) _
      (polymerMeasure ϑ N (t + v) u ω) inferInstance inferInstance
      (isLocallyFiniteMeasure_polymerMeasure ϑ N (t + v) u ω)⟩
  have hLFπ (N : ℕ) (ω : Disorder) : IsLocallyFiniteMeasure (πN N ω) := by
    obtain ⟨hσμ, hσν⟩ := hSigma N ω
    change IsLocallyFiniteMeasure (Measure.pi fun i : Fin 4 =>
      if i.val < 2 then polymerMeasure ϑ N s t ω
      else polymerMeasure ϑ N (t + v) u ω)
    exact @MeasureTheory.Measure.pi.isLocallyFiniteMeasure
      (Fin 4) (fun _ => Plane × Plane) inferInstance (fun _ => inferInstance)
      (fun i => if i.val < 2 then polymerMeasure ϑ N s t ω
        else polymerMeasure ϑ N (t + v) u ω)
      (by intro i; split_ifs <;> assumption)
      (fun _ => inferInstance)
      (by intro i; split_ifs <;> exact isLocallyFiniteMeasure_polymerMeasure ϑ N _ _ ω)
  let J₁ : ℕ → Disorder → ℝ := fun N ω =>
    ∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N s t ω
  let J₂ : ℕ → Disorder → ℝ := fun N ω =>
    ∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N (t + v) u ω
  let M : ℕ → Disorder → ℝ := fun N ω => (J₁ N ω) ^ 2 * (J₂ N ω) ^ 2
  obtain ⟨Cmass, hCmass, hMass⟩ := eventually_slabSeparatedTensorMass_sq_bound
    (ϑ := ϑ) hFlatSixthMomentInput (s := s) (t := t) (r := t + v) (u := u)
    hs hst (by linarith [hv]) hvu g g' hg hg'
  have hTint (N : ℕ) (ω : Disorder) : Integrable (fun q => T q) (πN N ω) :=
    integrable_compactTest_of_locallyFinite _ (hLFπ N ω) T
  have hTmass (N : ℕ) (ω : Disorder) : ∫ q, T q ∂πN N ω = M N ω := by
    obtain ⟨hμ, hν⟩ := hSigma N ω
    have h := integral_slabCompactPiTensorTest_twoBlock hμ hν (fun _ => ρ)
    have hρμ : ∫ p, ρ p ∂polymerMeasure ϑ N s t ω = J₁ N ω := by
      simp [ρ, J₁, compactTensorTest_apply]
    have hρν : ∫ p, ρ p ∂polymerMeasure ϑ N (t + v) u ω = J₂ N ω := by
      simp [ρ, J₂, compactTensorTest_apply]
    calc
      _ = (∏ i : Fin 2, ∫ p, ρ p ∂polymerMeasure ϑ N s t ω) *
          ∏ i : Fin 2, ∫ p, ρ p ∂polymerMeasure ϑ N (t + v) u ω := by
        simpa only [T, πN, slabTwoBlockPiMeasure] using h
      _ = M N ω := by simp [M, hρμ, hρν]
  have hHheatBound (q : Fin 4 → Plane × Plane) :
      ‖slabHeatCutoffReplicaTest v R Φ q‖ ≤
        ‖pairingCompactTestToBoundedContinuous (slabHeatCutoffReplicaTest v R Φ)‖ * T q := by
    by_cases hq : q ∈ K4
    · rw [hTone q hq, mul_one]
      exact (pairingCompactTestToBoundedContinuous (slabHeatCutoffReplicaTest v R Φ)).norm_coe_le_norm q
    · have hz := hheatZero q hq
      rw [hz, norm_zero]
      exact mul_nonneg (norm_nonneg _) (hTnonneg q)
  have hDpoint (δ : ℝ) (hδ : 0 < δ) (N : ℕ)
      (hU : ∀ q, |slabCutoffReplicaValue ϑ N t v R Φ q -
        slabHeatCutoffReplicaTest v R Φ q| < δ) (q : Fin 4 → Plane × Plane) :
      ‖slabCutoffReplicaValue ϑ N t v R Φ q -
        slabHeatCutoffReplicaTest v R Φ q‖ ≤ δ * T q := by
    by_cases hq : q ∈ K4
    · rw [hTone q hq, mul_one, Real.norm_eq_abs]
      exact le_of_lt (hU q)
    · have h₁ := hslabZero N q hq
      have h₂ := hheatZero q hq
      rw [h₁, h₂, sub_self, norm_zero]
      exact mul_nonneg hδ.le (hTnonneg q)
  have hheatInt (N : ℕ) (ω : Disorder) :
      Integrable (fun q => slabHeatCutoffReplicaTest v R Φ q) (πN N ω) :=
    integrable_compactTest_of_locallyFinite _ (hLFπ N ω) (slabHeatCutoffReplicaTest v R Φ)
  have hHeatMeas (N : ℕ) :
      Measurable (fun ω => ∫ q, slabHeatCutoffReplicaTest v R Φ q ∂πN N ω) :=
    (measurable_integral_as_function_of_measure_for_slab_comparison _ hheatMeas.stronglyMeasurable).comp (hπMeas N)
  have hSlabMeas (N : ℕ) :
      Measurable (fun ω => ∫ q, slabCutoffReplicaValue ϑ N t v R Φ q ∂πN N ω) :=
    (measurable_integral_as_function_of_measure_for_slab_comparison _ (hHNmeas N).stronglyMeasurable).comp (hπMeas N)
  have hHeatBound (N : ℕ) (ω : Disorder) :
      ‖∫ q, slabHeatCutoffReplicaTest v R Φ q ∂πN N ω‖ ≤
        ‖pairingCompactTestToBoundedContinuous (slabHeatCutoffReplicaTest v R Φ)‖ * M N ω := by
    have hnorm := norm_integral_le_of_norm_le
      ((hTint N ω).const_mul ‖pairingCompactTestToBoundedContinuous (slabHeatCutoffReplicaTest v R Φ)‖)
      (Filter.Eventually.of_forall hHheatBound)
    rw [integral_const_mul, hTmass] at hnorm
    exact hnorm
  have hDint (δ : ℝ) (hδ : 0 < δ) (N : ℕ)
      (hU : ∀ q, |slabCutoffReplicaValue ϑ N t v R Φ q -
        slabHeatCutoffReplicaTest v R Φ q| < δ) (ω : Disorder) :
      Integrable (fun q => slabCutoffReplicaValue ϑ N t v R Φ q -
        slabHeatCutoffReplicaTest v R Φ q) (πN N ω) := by
    apply ((hTint N ω).const_mul δ).mono'
      ((hHNmeas N).sub hheatMeas).aestronglyMeasurable
    exact Filter.Eventually.of_forall (hDpoint δ hδ N hU)
  have hDinnerBound (δ : ℝ) (hδ : 0 < δ) (N : ℕ)
      (hU : ∀ q, |slabCutoffReplicaValue ϑ N t v R Φ q -
        slabHeatCutoffReplicaTest v R Φ q| < δ) (ω : Disorder) :
      ‖∫ q, (slabCutoffReplicaValue ϑ N t v R Φ q -
        slabHeatCutoffReplicaTest v R Φ q) ∂πN N ω‖ ≤ δ * M N ω := by
    have hnorm := norm_integral_le_of_norm_le ((hTint N ω).const_mul δ)
      (Filter.Eventually.of_forall (hDpoint δ hδ N hU))
    rw [integral_const_mul, hTmass] at hnorm
    exact hnorm
  have houterHeat (N : ℕ) (hMN : Integrable (M N) disorderLaw) :
      Integrable (fun ω => ∫ q, slabHeatCutoffReplicaTest v R Φ q ∂πN N ω) disorderLaw := by
    apply (hMN.const_mul ‖pairingCompactTestToBoundedContinuous (slabHeatCutoffReplicaTest v R Φ)‖).mono'
      (hHeatMeas N).aestronglyMeasurable
    filter_upwards [] with ω
    simpa only [Real.norm_eq_abs] using hHeatBound N ω
  have houterD (δ : ℝ) (hδ : 0 < δ) (N : ℕ)
      (hU : ∀ q, |slabCutoffReplicaValue ϑ N t v R Φ q -
        slabHeatCutoffReplicaTest v R Φ q| < δ)
      (hMN : Integrable (M N) disorderLaw) :
      Integrable (fun ω => ∫ q,
        (slabCutoffReplicaValue ϑ N t v R Φ q -
          slabHeatCutoffReplicaTest v R Φ q) ∂πN N ω) disorderLaw := by
    apply (hMN.const_mul δ).mono'
      (((measurable_integral_as_function_of_measure_for_slab_comparison _
        (((hHNmeas N).sub hheatMeas).stronglyMeasurable)).comp
        (hπMeas N)).aestronglyMeasurable)
    filter_upwards [] with ω
    simpa only [Pi.sub_apply, Real.norm_eq_abs, Function.comp_apply] using
      hDinnerBound δ hδ N hU ω
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let δ : ℝ := ε / (2 * (Cmass + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδbound : δ * Cmass < ε / 2 := by
    dsimp [δ]
    have hC : Cmass < Cmass + 1 := by linarith
    have hden : 0 < 2 * (Cmass + 1) := by positivity
    rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith
  have hheat := tendsto_slabHeatCutoffConnectorMoment
    ϑ hPolymerMomentInput hFlatSixthMomentInput hs hst hv hvu Φ R
  have hheatEv := hheat.eventually (Metric.ball_mem_nhds _ (half_pos hε))
  have hEvent : ∀ᶠ N : ℕ in atTop, dist
      (∫ ω, ∫ q, slabCutoffReplicaValue ϑ N t v R Φ q ∂
        slabTwoBlockPiMeasure (polymerMeasure ϑ N s t ω)
          (polymerMeasure ϑ N (t + v) u ω) ∂disorderLaw)
      (slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant)
        (t - s) (u - (t + v)) (slabHeatCutoffReplicaTest v R Φ)) < ε := by
    filter_upwards [hMass, eventually_slabCutoffReplica_uniform ϑ
        (by linarith : 0 ≤ t) hv R Φ δ hδ, hheatEv] with N hMN hU hheatN
    let I : Disorder → ℝ := fun ω =>
      ∫ q, slabCutoffReplicaValue ϑ N t v R Φ q ∂πN N ω
    let H : Disorder → ℝ := fun ω =>
      ∫ q, slabHeatCutoffReplicaTest v R Φ q ∂πN N ω
    let D : Disorder → ℝ := fun ω =>
      ∫ q, (slabCutoffReplicaValue ϑ N t v R Φ q -
        slabHeatCutoffReplicaTest v R Φ q) ∂πN N ω
    have hHI : Integrable H disorderLaw := houterHeat N hMN.1
    have hDI : Integrable D disorderLaw := houterD δ hδ N hU hMN.1
    have hIeq : I = H + D := by
      funext ω
      dsimp [I, H, D]
      have hslabInt : Integrable
          (fun q => slabCutoffReplicaValue ϑ N t v R Φ q) (πN N ω) := by
        have hadd := (hDint δ hδ N hU ω).add (hheatInt N ω)
        apply hadd.congr
        exact Filter.Eventually.of_forall fun q => by
          change (slabCutoffReplicaValue ϑ N t v R Φ q -
            slabHeatCutoffReplicaTest v R Φ q) +
              slabHeatCutoffReplicaTest v R Φ q =
            slabCutoffReplicaValue ϑ N t v R Φ q
          ring
      have hsub := integral_sub hslabInt (hheatInt N ω)
      calc
        ∫ q, slabCutoffReplicaValue ϑ N t v R Φ q ∂πN N ω =
            (∫ q, slabCutoffReplicaValue ϑ N t v R Φ q ∂πN N ω -
              ∫ q, slabHeatCutoffReplicaTest v R Φ q ∂πN N ω) +
              ∫ q, slabHeatCutoffReplicaTest v R Φ q ∂πN N ω := by ring
        _ = (∫ q, (slabCutoffReplicaValue ϑ N t v R Φ q -
              slabHeatCutoffReplicaTest v R Φ q) ∂πN N ω) +
              ∫ q, slabHeatCutoffReplicaTest v R Φ q ∂πN N ω := by rw [hsub]
        _ = _ := by ring
    have hII : Integrable I disorderLaw := by
      rw [hIeq]
      exact hHI.add hDI
    have hOuterDiff : ‖∫ ω, D ω ∂disorderLaw‖ ≤ δ * Cmass := by
      have hnorm := norm_integral_le_of_norm_le (hMN.1.const_mul δ)
        (Filter.Eventually.of_forall fun ω => hDinnerBound δ hδ N hU ω)
      rw [integral_const_mul] at hnorm
      calc
        ‖∫ ω, D ω ∂disorderLaw‖ ≤ δ * ∫ ω, M N ω ∂disorderLaw := by
          simpa [D] using hnorm
        _ ≤ δ * Cmass := mul_le_mul_of_nonneg_left hMN.2 hδ.le
    have hsum : ∫ ω, I ω ∂disorderLaw =
        (∫ ω, H ω ∂disorderLaw) + (∫ ω, D ω ∂disorderLaw) := by
      rw [hIeq]
      exact integral_add hHI hDI
    have hdiff : |(∫ ω, I ω ∂disorderLaw) - ∫ ω, H ω ∂disorderLaw| < ε / 2 := by
      rw [hsum, add_sub_cancel_left]
      rw [← Real.norm_eq_abs]
      exact hOuterDiff.trans_lt hδbound
    have hheatN' : |(∫ ω, H ω ∂disorderLaw) -
        slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant)
          (t - s) (u - (t + v)) (slabHeatCutoffReplicaTest v R Φ)| < ε / 2 := by
      rw [Real.dist_eq] at hheatN
      simpa [H, πN, slabTwoBlockPiMeasure, slabHeatCutoffReplicaTest] using hheatN
    have hdist : dist (∫ ω, I ω ∂disorderLaw)
        (slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant)
          (t - s) (u - (t + v)) (slabHeatCutoffReplicaTest v R Φ)) < ε := by
      rw [Real.dist_eq]
      calc
        |(∫ ω, I ω ∂disorderLaw) -
            slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant)
              (t - s) (u - (t + v)) (slabHeatCutoffReplicaTest v R Φ)| =
          |((∫ ω, I ω ∂disorderLaw) - ∫ ω, H ω ∂disorderLaw) +
            ((∫ ω, H ω ∂disorderLaw) -
              slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant)
                (t - s) (u - (t + v)) (slabHeatCutoffReplicaTest v R Φ))| := by ring_nf
        _ ≤ |(∫ ω, I ω ∂disorderLaw) - ∫ ω, H ω ∂disorderLaw| +
            |(∫ ω, H ω ∂disorderLaw) -
              slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant)
              (t - s) (u - (t + v)) (slabHeatCutoffReplicaTest v R Φ)| := by
          exact abs_add_le _ _
        _ < ε / 2 + ε / 2 := add_lt_add hdiff hheatN'
        _ = ε := by ring
    exact hdist
  rcases Filter.eventually_atTop.mp hEvent with ⟨N, hN⟩
  exact ⟨N, hN⟩

end Critical2DKPZ.SHF.Flow

end
