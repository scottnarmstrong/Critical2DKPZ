/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.ThinSlabContinuumConnectorTest
public import Critical2DKPZ.SHF.Flow.ThinSlabContinuumIntegrability
public import Critical2DKPZ.SHF.Flow.ThinSlabConnectorMomentLimit
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-! # Absolute integrability of uncut continuum connector moments -/

@[expose] public noncomputable section
open MeasureTheory Filter Critical2DKPZ.DeltaBose Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Tsai
open scoped CompactlySupported Topology
namespace Critical2DKPZ.SHF.Flow

/-- Positive-duration two-block moment endpoint laws are locally finite. -/
theorem locallyFinite_slabSeparatedMomentPiMeasure (θ : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IsLocallyFiniteMeasure (slabSeparatedMomentPiMeasure θ a b) := by
  let ν : Fin 2 → Measure (Configuration 2 × Configuration 2) := fun i =>
    if i.val = 0 then slabMomentKernelEndpointMeasure θ a else slabMomentKernelEndpointMeasure θ b
  have hνloc (i : Fin 2) : IsLocallyFiniteMeasure (ν i) := by
    dsimp [ν, slabMomentKernelEndpointMeasure]
    split_ifs <;> apply locallyFinite_momentKernelMeasure <;> assumption
  have hνsigma (i : Fin 2) : SigmaFinite (ν i) :=
    @MeasureTheory.sigmaFinite_of_locallyFinite (Configuration 2 × Configuration 2) _
      (ν i) inferInstance inferInstance (hνloc i)
  exact @MeasureTheory.Measure.pi.isLocallyFiniteMeasure
    (Fin 2) (fun _ => Configuration 2 × Configuration 2) inferInstance (fun _ => inferInstance)
    ν hνsigma (fun _ => inferInstance) hνloc

/-- The explicit continuum connector replica integrand is absolutely integrable.
Absolute-value tests and Fatou transfer the finite uncut second-moment bound
from the discrete approximation. -/
theorem integrable_slabConnectorReplicaValue (ϑ : ℝ)
    (hPolymerMomentInput : PolymerMomentLimit ϑ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
    {s t r u : ℝ} (hs : 0 ≤ s) (hst : s < t) (htr : t ≤ r) (hru : r < u)
    (Φ : C_c(Plane × Plane, ℝ)) (κ : ℕ → Plane × Plane → ℝ)
    (hκm : ∀ N, Measurable (κ N)) (κlim : C(Plane × Plane, ℝ))
    (hUniform : ∀ K : Set (Plane × Plane), IsCompact K → ∀ δ > 0,
      ∀ᶠ N : ℕ in atTop, ∀ p ∈ K, |κ N p - κlim p| ≤ δ)
    (hκ : ∃ C c : ℝ, 0 < c ∧ ∀ N a b,
      |κ N (a, b)| ≤ C * Real.exp (-c * ‖a - b‖ ^ 2)) :
    Integrable (slabConnectorReplicaValue Φ κlim)
      (slabSeparatedMomentPiMeasure (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r)) := by
  let Φabs : C_c(Plane × Plane, ℝ) := ⟨⟨fun p => |Φ p|, Φ.continuous.abs⟩, Φ.hasCompactSupport.abs⟩
  let κabs : C(Plane × Plane, ℝ) := ⟨fun p => |κlim p|, κlim.continuous.abs⟩
  have hU : ∀ K : Set (Plane × Plane), IsCompact K → ∀ δ > 0,
      ∀ᶠ N : ℕ in atTop, ∀ p ∈ K, |(|κ N p|) - κabs p| ≤ δ := by
    intro K hK δ hδ
    filter_upwards [hUniform K hK δ hδ] with N hN p hp
    exact (abs_abs_sub_abs_le _ _).trans (hN p hp)
  have hE : ∃ C c : ℝ, 0 < c ∧ ∀ N a b,
      |(|κ N (a, b)|)| ≤ C * Real.exp (-c * ‖a - b‖ ^ 2) := by
    simpa only [abs_abs] using hκ
  obtain ⟨L, _hFull, hCut⟩ := exists_slabConnector_secondMoment_limit_with_cutoffs ϑ hPolymerMomentInput hFlatSixthMomentInput
    hs hst htr hru Φabs (fun N p => |κ N p|) (fun N => (hκm N).abs) κabs hU hE
  let ν := slabSeparatedMomentPiMeasure (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r)
  let F := slabConnectorReplicaValue Φabs κabs
  let f : ℕ → (Fin 2 → Configuration 2 × Configuration 2) → ℝ := fun n z =>
    slabSeparatedGroupedTest (slabReplicaSourceTest (slabCutoffConnectorTest Φabs κabs (n : ℝ))) z
  have hF : Continuous F := continuous_slabConnectorReplicaValue Φabs.continuous κabs.continuous
  have hF0 (z : Fin 2 → Configuration 2 × Configuration 2) : 0 ≤ F z := by
    exact Finset.prod_nonneg fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hEq (n : ℕ) (z : Fin 2 → Configuration 2 × Configuration 2) :
      f n z = F z * slabConnectorMiddleCutoff n z :=
    slabSeparatedGroupedTest_cutoffConnector Φabs κabs n z
  have hLoc : IsLocallyFiniteMeasure ν :=
    locallyFinite_slabSeparatedMomentPiMeasure _ (sub_pos.mpr hst) (sub_pos.mpr hru)
  let : BorelSpace (Configuration 2) := by infer_instance
  let : BorelSpace (Configuration 2 × Configuration 2) := by infer_instance
  let : BorelSpace (Fin 2 → Configuration 2 × Configuration 2) := by infer_instance
  have hInt : ∀ n, Integrable (f n) ν := fun n =>
    integrable_compactTest_of_locallyFinite ν hLoc
      (slabSeparatedGroupedTest (slabReplicaSourceTest (slabCutoffConnectorTest Φabs κabs n)))
  have hNat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hAbsInt : Integrable F ν := by
    apply integrable_of_nonnegative_cutoff_integral_limit f F L hF.measurable
    · intro n z
      rw [hEq]
      exact mul_nonneg (hF0 z) (slabConnectorMiddleCutoff_mem_Icc n z).1
    · exact hInt
    · intro z
      have hEvent := hNat.eventually (eventually_slabConnectorMiddleCutoff_eq_one z)
      apply (tendsto_congr' (hEvent.mono fun n hn => ?_)).2 tendsto_const_nhds
      rw [hEq, hn, mul_one]
    · exact hCut.comp hNat
  have hPoint (z : Fin 2 → Configuration 2 × Configuration 2) :
      ‖slabConnectorReplicaValue Φ κlim z‖ = F z := by
    simp only [Real.norm_eq_abs, F, slabConnectorReplicaValue, Fin.prod_univ_two, abs_mul]
    rfl
  apply (integrable_norm_iff
    (continuous_slabConnectorReplicaValue Φ.continuous κlim.continuous).aestronglyMeasurable).mp
  exact hAbsInt.congr (Eventually.of_forall fun z => (hPoint z).symm)

/-- Dominated convergence removes the middle cutoffs once absolute
integrability of the explicit continuum connector integrand is known. -/
theorem tendsto_slabContinuumCutoffConnectorMoment (θ a b : ℝ)
    (Φ : C_c(Plane × Plane, ℝ)) (κ : C(Plane × Plane, ℝ))
    (hInt : Integrable (slabConnectorReplicaValue Φ κ) (slabSeparatedMomentPiMeasure θ a b)) :
    Tendsto (fun R => slabSeparatedMomentIntegral θ a b
      (slabReplicaSourceTest (slabCutoffConnectorTest Φ κ R))) atTop
      (𝓝 (∫ z, slabConnectorReplicaValue Φ κ z ∂slabSeparatedMomentPiMeasure θ a b)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun z => ‖slabConnectorReplicaValue Φ κ z‖)
  · exact Eventually.of_forall fun R =>
      (slabSeparatedGroupedTest (slabReplicaSourceTest (slabCutoffConnectorTest Φ κ R))).continuous.aestronglyMeasurable
  · apply Eventually.of_forall
    intro R
    filter_upwards [] with z
    rw [slabSeparatedGroupedTest_cutoffConnector, norm_mul,
      Real.norm_eq_abs (slabConnectorMiddleCutoff R z),
      abs_of_nonneg (slabConnectorMiddleCutoff_mem_Icc R z).1]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (slabConnectorMiddleCutoff_mem_Icc R z).2 (norm_nonneg (slabConnectorReplicaValue Φ κ z))
  · exact hInt.norm
  · filter_upwards [] with z
    apply (tendsto_congr' ((eventually_slabConnectorMiddleCutoff_eq_one z).mono fun R hR => ?_)).2
      tendsto_const_nhds
    rw [slabSeparatedGroupedTest_cutoffConnector, hR, mul_one]

/-- The uncut finite-lattice second moment converges to the continuum two-block replica integral. Absolute integrability follows from `integrable_slabConnectorReplicaValue`, and finite-scale square integrability follows from `memLp_kernelProductPairing_two`. -/
theorem tendsto_slabConnector_secondMoment (ϑ : ℝ)
    (hPolymerMomentInput : PolymerMomentLimit ϑ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
    {s t r u : ℝ} (hs : 0 ≤ s) (hst : s < t) (htr : t ≤ r) (hru : r < u)
    (Φ : C_c(Plane × Plane, ℝ)) (κ : ℕ → Plane × Plane → ℝ)
    (hκm : ∀ N, Measurable (κ N)) (κlim : C(Plane × Plane, ℝ))
    (hUniform : ∀ K : Set (Plane × Plane), IsCompact K → ∀ δ > 0,
      ∀ᶠ N : ℕ in atTop, ∀ p ∈ K, |κ N p - κlim p| ≤ δ)
    (hκ : ∃ C c : ℝ, 0 < c ∧ ∀ N a b,
      |κ N (a, b)| ≤ C * Real.exp (-c * ‖a - b‖ ^ 2)) :
    Tendsto (fun N => ∫ ω,
      kernelProductPairing (polymerMeasure ϑ N s t ω) (fun a b => κ N (a, b))
        (polymerMeasure ϑ N r u ω) Φ ^ 2 ∂disorderLaw) atTop
      (𝓝 (∫ z, slabConnectorReplicaValue Φ κlim z ∂
        slabSeparatedMomentPiMeasure (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r))) := by
  obtain ⟨L, hFull, hCut⟩ := exists_slabConnector_secondMoment_limit_with_cutoffs ϑ hPolymerMomentInput hFlatSixthMomentInput
    hs hst htr hru Φ κ hκm κlim hUniform hκ
  have hInt := integrable_slabConnectorReplicaValue ϑ hPolymerMomentInput hFlatSixthMomentInput hs hst htr hru Φ κ hκm κlim hUniform hκ
  have hDCT := tendsto_slabContinuumCutoffConnectorMoment
    (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r) Φ κlim hInt
  have hEq := tendsto_nhds_unique hCut hDCT
  simpa only [hEq] using hFull

/-- The continuum replica integral is absolutely integrable and is the limit of the uncut finite-lattice second moments; finite-scale square integrability is supplied by `memLp_kernelProductPairing_two`. -/
theorem tendsto_slabConnector_secondMoment_with_integrability (ϑ : ℝ)
    (hPolymerMomentInput : PolymerMomentLimit ϑ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
    {s t r u : ℝ} (hs : 0 ≤ s) (hst : s < t) (htr : t ≤ r) (hru : r < u)
    (Φ : C_c(Plane × Plane, ℝ)) (κ : ℕ → Plane × Plane → ℝ)
    (hκm : ∀ N, Measurable (κ N)) (κlim : C(Plane × Plane, ℝ))
    (hUniform : ∀ K : Set (Plane × Plane), IsCompact K → ∀ δ > 0,
      ∀ᶠ N : ℕ in atTop, ∀ p ∈ K, |κ N p - κlim p| ≤ δ)
    (hκ : ∃ C c : ℝ, 0 < c ∧ ∀ N a b,
      |κ N (a, b)| ≤ C * Real.exp (-c * ‖a - b‖ ^ 2)) :
    Integrable (slabConnectorReplicaValue Φ κlim)
      (slabSeparatedMomentPiMeasure (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r)) ∧
    Tendsto (fun N => ∫ ω,
      kernelProductPairing (polymerMeasure ϑ N s t ω) (fun a b => κ N (a, b))
        (polymerMeasure ϑ N r u ω) Φ ^ 2 ∂disorderLaw) atTop
      (𝓝 (∫ z, slabConnectorReplicaValue Φ κlim z ∂
        slabSeparatedMomentPiMeasure (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r))) :=
  ⟨integrable_slabConnectorReplicaValue ϑ hPolymerMomentInput hFlatSixthMomentInput hs hst htr hru Φ κ hκm κlim hUniform hκ,
    tendsto_slabConnector_secondMoment ϑ hPolymerMomentInput hFlatSixthMomentInput hs hst htr hru Φ κ hκm κlim hUniform hκ⟩

end Critical2DKPZ.SHF.Flow
end
