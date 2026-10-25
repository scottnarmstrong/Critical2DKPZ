/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.ThinSlabSeparatedTensorIntegralLimit
public import Critical2DKPZ.SHF.Flow.ThinSlabSeparatedCompactApproximation
public import Critical2DKPZ.SHF.Flow.ThinSlabSeparatedMassBound
public import Critical2DKPZ.SHF.Tsai.ProductMeasureKernels
import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Probability.Kernel.Composition.Prod

/-! # Compact-test convergence for separated blocks -/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open ProbabilityTheory
open BoundedContinuousFunction
open Critical2DKPZ.SHF.Limit
open Critical2DKPZ.SHF.Tsai
open Critical2DKPZ.DeltaBose
open scoped CompactlySupported Topology BoundedContinuousFunction

namespace Critical2DKPZ.SHF.Flow

private instance instSeparatedBlockConfigurationBorel : BorelSpace (Configuration 2) := by
  infer_instance

private instance instSeparatedBlockConfigurationPairBorel : BorelSpace (Configuration 2 × Configuration 2) := by
  infer_instance

private instance instSeparatedBlockEndpointArrayBorel :
    BorelSpace (Fin 2 → Configuration 2 × Configuration 2) := by
  infer_instance

private def separatedCompactTestToBoundedContinuous {X : Type*} [TopologicalSpace X]
    (f : C_c(X, ℝ)) : X →ᵇ ℝ :=
  ofCompactSupport f f.continuous f.hasCompactSupport

private theorem measurable_integral_compact_test_for_separated_moments {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (f : C_c(X, ℝ)) :
    Measurable (fun μ : Measure X => ∫ x, f x ∂μ) := by
  let κ : Kernel (Measure X) X := ⟨id, measurable_id⟩
  exact (((map_continuous f).measurable).stronglyMeasurable.integral_kernel
    (κ := κ)).measurable

/-- Polymer-moment convergence and sixth-moment bounds extend from separated four-replica tensor tests to every compactly supported
continuous test on the four replica coordinates. The eventual integrable mass majorant is supplied by
`eventually_slabSeparatedTensorMass_sq_bound`. -/
theorem tendsto_slabSeparatedCompactIntegral (ϑ : ℝ)
    (hPolymerMomentInput : PolymerMomentLimit ϑ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
    {s t r u : ℝ} (hs : 0 ≤ s) (hst : s < t) (htr : t < r) (hru : r < u)
    (F : C_c((Fin 4 → Plane × Plane), ℝ)) :
    Tendsto
      (fun N => ∫ ω, ∫ q, F q ∂
        (slabTwoBlockPiMeasure (polymerMeasure ϑ N s t ω)
          (polymerMeasure ϑ N r u ω)) ∂disorderLaw)
      atTop
      (𝓝 (slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r) F)) := by
  classical
  obtain ⟨K₀, hK₀, htensor⟩ := exists_compactTensorProduct_uniform_approx (n := 4) (by norm_num) F
  let Ksrc : Set (Plane × Plane) := ⋃ i : Fin 4,
    (fun q : Fin 4 → Plane × Plane => q i) '' tsupport (F : (Fin 4 → Plane × Plane) → ℝ)
  have hKsrc : IsCompact Ksrc :=
    isCompact_iUnion fun i => F.hasCompactSupport.image (continuous_apply i)
  let K : Set (Plane × Plane) := Ksrc ∪ K₀
  have hK : IsCompact K := hKsrc.union hK₀
  let R : Set (Fin 4 → Plane × Plane) := Set.univ.pi fun _ => K
  have hR : IsCompact R := isCompact_univ_pi fun _ => hK
  have hFsupport : tsupport (F : (Fin 4 → Plane × Plane) → ℝ) ⊆ R := by
    intro q hq
    apply Set.mem_univ_pi.mpr
    intro i
    apply Set.mem_union_left K₀
    exact Set.mem_iUnion.mpr ⟨i, ⟨q, hq, rfl⟩⟩
  obtain ⟨g, g', hg, hg', hone⟩ := exists_compactTensor_majorant K hK
  let ρ : C_c(Plane × Plane, ℝ) := compactTensorTest g g'
  have hρnonneg (p : Plane × Plane) : 0 ≤ ρ p := by
    simp only [ρ, compactTensorTest_apply]
    exact mul_nonneg (hg _) (hg' _)
  have hρone (p : Plane × Plane) (hp : p ∈ K) : ρ p = 1 := hone p hp
  let Tψ : C_c((Fin 4 → Plane × Plane), ℝ) := slabCompactPiTensorTest (fun _ => ρ)
  have hTψnonneg (q : Fin 4 → Plane × Plane) : 0 ≤ Tψ q := by
    simp only [Tψ, slabCompactPiTensorTest_apply]
    exact Finset.prod_nonneg fun i hi => hρnonneg (q i)
  have hTψone (q : Fin 4 → Plane × Plane) (hq : q ∈ R) : Tψ q = 1 := by
    simp only [Tψ, slabCompactPiTensorTest_apply]
    apply Finset.prod_eq_one
    intro i hi
    exact hρone (q i) ((Set.mem_univ_pi.mp hq) i)
  let πN : ℕ → Disorder → Measure (Fin 4 → Plane × Plane) := fun N ω =>
    Measure.pi fun i : Fin 4 =>
      if i.val < 2 then polymerMeasure ϑ N s t ω else polymerMeasure ϑ N r u ω
  have hπMeas (N : ℕ) : Measurable (πN N) := by
    exact measurable_piMeasure_of_locallyFinite 4
      (fun i ω => if i.val < 2 then polymerMeasure ϑ N s t ω else polymerMeasure ϑ N r u ω)
      (by intro i; split_ifs <;> exact measurable_polymerMeasure ϑ N _ _)
      (by intro i ω; split_ifs <;> exact isLocallyFiniteMeasure_polymerMeasure ϑ N _ _ ω)
  have hπSigma (N : ℕ) (ω : Disorder) :
      SigmaFinite (polymerMeasure ϑ N s t ω) ∧ SigmaFinite (polymerMeasure ϑ N r u ω) := by
    exact ⟨@MeasureTheory.sigmaFinite_of_locallyFinite (Plane × Plane) _
      (polymerMeasure ϑ N s t ω) inferInstance inferInstance
      (isLocallyFiniteMeasure_polymerMeasure ϑ N s t ω),
      @MeasureTheory.sigmaFinite_of_locallyFinite (Plane × Plane) _
      (polymerMeasure ϑ N r u ω) inferInstance inferInstance
      (isLocallyFiniteMeasure_polymerMeasure ϑ N r u ω)⟩
  have hLFπ (N : ℕ) (ω : Disorder) : IsLocallyFiniteMeasure (πN N ω) := by
    obtain ⟨hσμ, hσν⟩ := hπSigma N ω
    exact @MeasureTheory.Measure.pi.isLocallyFiniteMeasure
      (Fin 4) (fun _ => Plane × Plane) inferInstance (fun _ => inferInstance)
      (fun i => if i.val < 2 then polymerMeasure ϑ N s t ω else polymerMeasure ϑ N r u ω)
      (by intro i; split_ifs <;> assumption)
      (fun _ => inferInstance)
      (by intro i; split_ifs <;> exact isLocallyFiniteMeasure_polymerMeasure ϑ N _ _ ω)
  have hImeas (H : C_c((Fin 4 → Plane × Plane), ℝ)) (N : ℕ) :
      Measurable (fun ω => ∫ q, H q ∂πN N ω) :=
    (measurable_integral_compact_test_for_separated_moments H).comp (hπMeas N)
  let IF : ℕ → Disorder → ℝ := fun N ω => ∫ q, F q ∂πN N ω
  let J₁ : ℕ → Disorder → ℝ := fun N ω =>
    ∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N s t ω
  let J₂ : ℕ → Disorder → ℝ := fun N ω =>
    ∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N r u ω
  let M : ℕ → Disorder → ℝ := fun N ω => (J₁ N ω) ^ 2 * (J₂ N ω) ^ 2
  have hMbound := eventually_slabSeparatedTensorMass_sq_bound ϑ hFlatSixthMomentInput hs hst htr hru
    g g' hg hg'
  obtain ⟨C, hC, hM⟩ := hMbound
  have hTψint (N : ℕ) (ω : Disorder) : Integrable (fun q => Tψ q) (πN N ω) :=
    integrable_compactTest_of_locallyFinite _ (hLFπ N ω) Tψ
  have hTψmass (N : ℕ) (ω : Disorder) :
      ∫ q, Tψ q ∂πN N ω = M N ω := by
    obtain ⟨hμ, hν⟩ := hπSigma N ω
    have h := integral_slabCompactPiTensorTest_twoBlock hμ hν (fun _ => ρ)
    have hρint₁ : ∫ p, ρ p ∂polymerMeasure ϑ N s t ω = J₁ N ω := by
      simp [ρ, J₁, compactTensorTest_apply]
    have hρint₂ : ∫ p, ρ p ∂polymerMeasure ϑ N r u ω = J₂ N ω := by
      simp [ρ, J₂, compactTensorTest_apply]
    calc
      _ = (∏ i : Fin 2, ∫ p, ρ p ∂polymerMeasure ϑ N s t ω) *
          ∏ i : Fin 2, ∫ p, ρ p ∂polymerMeasure ϑ N r u ω := by
        simpa only [Tψ, πN, slabTwoBlockPiMeasure] using h
      _ = M N ω := by simp [M, hρint₁, hρint₂]
  have hCompactIntegralBound (H : C_c((Fin 4 → Plane × Plane), ℝ))
      (hHs : tsupport (H : (Fin 4 → Plane × Plane) → ℝ) ⊆ R)
      (q : Fin 4 → Plane × Plane) :
      ‖H q‖ ≤ ‖separatedCompactTestToBoundedContinuous H‖ * Tψ q := by
    by_cases hq : q ∈ R
    · rw [hTψone q hq, mul_one]
      exact (separatedCompactTestToBoundedContinuous H).norm_coe_le_norm q
    · have hzero : H q = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        exact fun hsupp => hq (hHs hsupp)
      rw [hzero, norm_zero]
      exact mul_nonneg (norm_nonneg _) (hTψnonneg q)
  have hIntegralBound (H : C_c((Fin 4 → Plane × Plane), ℝ))
      (hHs : tsupport (H : (Fin 4 → Plane × Plane) → ℝ) ⊆ R)
      (N : ℕ) (ω : Disorder) :
      ‖∫ q, H q ∂πN N ω‖ ≤ ‖separatedCompactTestToBoundedContinuous H‖ * M N ω := by
    have hnorm := norm_integral_le_of_norm_le
      ((hTψint N ω).const_mul ‖separatedCompactTestToBoundedContinuous H‖)
      (Filter.Eventually.of_forall (hCompactIntegralBound H hHs))
    rw [integral_const_mul, hTψmass] at hnorm
    exact hnorm
  have hIFint (N : ℕ) (hN : Integrable (M N) disorderLaw) : Integrable (IF N) disorderLaw := by
    have hdom : Integrable (fun ω => ‖separatedCompactTestToBoundedContinuous F‖ * M N ω) disorderLaw :=
      hN.const_mul ‖separatedCompactTestToBoundedContinuous F‖
    exact hdom.mono' ((hImeas F N).aestronglyMeasurable) (Filter.Eventually.of_forall fun ω => by
      simpa only [IF, Real.norm_eq_abs] using hIntegralBound F hFsupport N ω)
  let ν : Fin 2 → Measure (Configuration 2 × Configuration 2) := fun i =>
    if i.val = 0 then slabMomentKernelEndpointMeasure
      (ϑ - Real.eulerMascheroniConstant) (t - s)
    else slabMomentKernelEndpointMeasure (ϑ - Real.eulerMascheroniConstant) (u - r)
  have hνloc (i : Fin 2) : IsLocallyFiniteMeasure (ν i) := by
    dsimp [ν, slabMomentKernelEndpointMeasure]
    split_ifs <;> apply locallyFinite_momentKernelMeasure <;> linarith
  have hνsigma (i : Fin 2) : SigmaFinite (ν i) :=
    @MeasureTheory.sigmaFinite_of_locallyFinite (Configuration 2 × Configuration 2) _
      (ν i) inferInstance inferInstance (hνloc i)
  have htargetLF : IsLocallyFiniteMeasure
      (slabSeparatedMomentPiMeasure (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r)) := by
    dsimp [slabSeparatedMomentPiMeasure]
    change IsLocallyFiniteMeasure (Measure.pi ν)
    exact @MeasureTheory.Measure.pi.isLocallyFiniteMeasure
      (Fin 2) (fun _ => Configuration 2 × Configuration 2) inferInstance (fun _ => inferInstance)
      ν hνsigma (fun _ => inferInstance) hνloc
  have htargetInt (H : C_c((Fin 4 → Plane × Plane), ℝ)) :
      Integrable (slabSeparatedGroupedTest H : (Fin 2 → Configuration 2 × Configuration 2) → ℝ)
        (slabSeparatedMomentPiMeasure (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r)) :=
    integrable_compactTest_of_locallyFinite _ htargetLF (slabSeparatedGroupedTest H)
  have htargetSub (H G : C_c((Fin 4 → Plane × Plane), ℝ)) :
      slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r) (H - G) =
        slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r) H -
          slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r) G := by
    unfold slabSeparatedMomentIntegral
    have hpoint (z : Fin 2 → Configuration 2 × Configuration 2) :
        slabSeparatedGroupedTest (H - G) z =
          slabSeparatedGroupedTest H z - slabSeparatedGroupedTest G z := by
      simp [slabSeparatedGroupedTest_apply]
    calc
      _ = ∫ z, (slabSeparatedGroupedTest H z - slabSeparatedGroupedTest G z)
            ∂slabSeparatedMomentPiMeasure (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hpoint
      _ = _ := integral_sub (htargetInt H) (htargetInt G)
  have htargetMassNonneg :
      0 ≤ slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r) Tψ := by
    apply integral_nonneg
    intro z
    change 0 ≤ Tψ (slabSeparatedArrayHomeomorph z)
    exact hTψnonneg _
  have hTψtargetInt := htargetInt Tψ
  have hTψtarget_nonneg := htargetMassNonneg
  have hδchoice : ∀ δ : ℝ, 0 < δ → ∃ m : ℕ, ∃ φ : Fin m → Fin 4 → C_c(Plane × Plane, ℝ),
      (∀ b i, tsupport (φ b i : Plane × Plane → ℝ) ⊆ K₀) ∧
      ∀ q, |(∑ b, ∏ i, φ b i (q i)) - F q| < δ := by
    intro δ hδ
    exact htensor δ hδ
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let M₁ : ℝ := 1 + slabSeparatedMomentIntegral
    (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r) Tψ
  let δ : ℝ := ε / (3 * (C + M₁))
  have hM₁pos : 0 < M₁ := by dsimp [M₁]; linarith [htargetMassNonneg]
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨m, φ, hφsupport, happrox⟩ := hδchoice δ hδ
  let T : Fin m → C_c((Fin 4 → Plane × Plane), ℝ) := fun b => slabCompactPiTensorTest (φ b)
  let G : C_c((Fin 4 → Plane × Plane), ℝ) := ∑ b, T b
  have hGapply (q : Fin 4 → Plane × Plane) : G q = ∑ b, ∏ i, φ b i (q i) := by
    simp [G, T, slabCompactPiTensorTest_apply]
  have hTsupport (b : Fin m) : tsupport (T b : (Fin 4 → Plane × Plane) → ℝ) ⊆ R := by
    apply closure_minimal
    · intro q hq
      apply Set.mem_univ_pi.mpr
      intro i
      by_contra hi
      have hzero : φ b i (q i) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hsupp => hi (Set.mem_union_right Ksrc
          (hφsupport b i hsupp)))
      change slabCompactPiTensorTest (φ b) q ≠ 0 at hq
      rw [slabCompactPiTensorTest_apply] at hq
      exact hq (Finset.prod_eq_zero (Finset.mem_univ i) hzero)
    · exact hR.isClosed
  have hGsupport : Function.support (G : (Fin 4 → Plane × Plane) → ℝ) ⊆ R := by
    intro q hq
    change G q ≠ 0 at hq
    apply Set.mem_univ_pi.mpr
    intro i
    by_contra hi
    have hφzero (b : Fin m) : φ b i (q i) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hsupp
      exact hi (Set.mem_union_right Ksrc (hφsupport b i hsupp))
    have hGzero : G q = 0 := by
      rw [hGapply]
      apply Finset.sum_eq_zero
      intro b hb
      exact Finset.prod_eq_zero (Finset.mem_univ i) (hφzero b)
    exact hq hGzero
  have hGtsupport : tsupport (G : (Fin 4 → Plane × Plane) → ℝ) ⊆ R :=
    closure_minimal hGsupport hR.isClosed
  have hGapprox (q : Fin 4 → Plane × Plane) : |G q - F q| ≤ δ := by
    rw [hGapply]
    exact (happrox q).le
  have hpointApprox (q : Fin 4 → Plane × Plane) :
      ‖G q - F q‖ ≤ δ * Tψ q := by
    by_cases hq : q ∈ R
    · rw [Real.norm_eq_abs, hTψone q hq, mul_one]
      exact hGapprox q
    · have hFzero : F q = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hsupp
        exact hq (hFsupport hsupp)
      have hGzero : G q = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hsupp
        exact hq (hGtsupport hsupp)
      rw [hFzero, hGzero]
      simp only [sub_self, norm_zero]
      exact mul_nonneg (le_of_lt hδ) (hTψnonneg q)
  have htargetApprox :
      |slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r) F -
        slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r) G| ≤
        δ * slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r) Tψ := by
    have hpoint (z : Fin 2 → Configuration 2 × Configuration 2) :
        ‖slabSeparatedGroupedTest (G - F) z‖ ≤ δ * slabSeparatedGroupedTest Tψ z := by
      let q := slabSeparatedArrayHomeomorph z
      have h := hpointApprox q
      simpa [slabSeparatedGroupedTest_apply, q, slabCompactPiTensorTest_apply] using h
    have hmajor : Integrable (fun z => δ * slabSeparatedGroupedTest Tψ z)
        (slabSeparatedMomentPiMeasure (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r)) :=
      htargetInt Tψ |>.const_mul δ
    have hnorm := norm_integral_le_of_norm_le hmajor
      (Filter.Eventually.of_forall hpoint)
    have hsub := htargetSub G F
    calc
      _ = |slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant)
          (t - s) (u - r) G -
          slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant)
            (t - s) (u - r) F| := abs_sub_comm _ _
      _ = ‖∫ z, slabSeparatedGroupedTest (G - F) z
            ∂slabSeparatedMomentPiMeasure (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r)‖ := by
        rw [Real.norm_eq_abs]
        change |slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant)
            (t - s) (u - r) G -
          slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant)
            (t - s) (u - r) F| =
          |slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant)
            (t - s) (u - r) (G - F)|
        rw [hsub]
      _ ≤ ∫ z, δ * slabSeparatedGroupedTest Tψ z
            ∂slabSeparatedMomentPiMeasure (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r) := hnorm
      _ = δ * slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant)
            (t - s) (u - r) Tψ := by
        change (∫ z, δ * slabSeparatedGroupedTest Tψ z
          ∂slabSeparatedMomentPiMeasure (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r)) =
          δ * (∫ z, slabSeparatedGroupedTest Tψ z
            ∂slabSeparatedMomentPiMeasure (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r))
        rw [integral_const_mul]
  have htargetApprox' :
      |slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r) F -
        slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r) G| ≤
        δ * M₁ := by
    calc
      _ ≤ δ * slabSeparatedMomentIntegral
            (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r) Tψ := htargetApprox
      _ ≤ δ * M₁ := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hδ)
        dsimp [M₁]
        linarith [htargetMassNonneg]
  have htargetSum :
      slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r) G =
        ∑ b : Fin m, slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant)
          (t - s) (u - r) (T b) := by
    unfold slabSeparatedMomentIntegral
    have hpoint (z : Fin 2 → Configuration 2 × Configuration 2) :
        slabSeparatedGroupedTest G z = ∑ b, slabSeparatedGroupedTest (T b) z := by
      simp [G, slabSeparatedGroupedTest_apply, CompactlySupportedContinuousMap.sum_apply]
    calc
      _ = ∫ z, (∑ b, slabSeparatedGroupedTest (T b) z)
            ∂slabSeparatedMomentPiMeasure (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hpoint
      _ = _ := by
        rw [integral_finsetSum]
        intro b hb
        exact htargetInt (T b)
  have hterm (b : Fin m) : Tendsto
      (fun N => ∫ ω, ∫ q, T b q ∂πN N ω ∂disorderLaw) atTop
      (𝓝 (slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r) (T b))) := by
    exact tendsto_slabSeparatedTensorIntegral ϑ hPolymerMomentInput hFlatSixthMomentInput hs hst htr hru (φ b)
  have hsumLimit : Tendsto
      (fun N => ∑ b : Fin m, ∫ ω, ∫ q, T b q ∂πN N ω ∂disorderLaw) atTop
      (𝓝 (∑ b : Fin m, slabSeparatedMomentIntegral
        (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r) (T b))) :=
    tendsto_finsetSum Finset.univ (fun b hb => hterm b)
  have hsumEvent : ∀ᶠ N : ℕ in atTop,
      (∫ ω, ∫ q, G q ∂πN N ω ∂disorderLaw) =
        ∑ b : Fin m, ∫ ω, ∫ q, T b q ∂πN N ω ∂disorderLaw := by
    filter_upwards [hM] with N hMN
    have htermInt (b : Fin m) : Integrable
        (fun ω => ∫ q, T b q ∂πN N ω) disorderLaw := by
      have hdom := hMN.1.const_mul ‖separatedCompactTestToBoundedContinuous (T b)‖
      exact hdom.mono' ((hImeas (T b) N).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun ω => by
          simpa only [Real.norm_eq_abs] using hIntegralBound (T b) (hTsupport b) N ω)
    have hinner (ω : Disorder) :
        (∫ q, G q ∂πN N ω) = ∑ b : Fin m, ∫ q, T b q ∂πN N ω := by
      rw [show (fun q => G q) = fun q => ∑ b : Fin m, T b q from by
        funext q
        simp [G, CompactlySupportedContinuousMap.sum_apply]]
      rw [integral_finsetSum]
      intro b hb
      exact integrable_compactTest_of_locallyFinite _ (hLFπ N ω) (T b)
    calc
      _ = ∫ ω, ∑ b : Fin m, ∫ q, T b q ∂πN N ω ∂disorderLaw := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hinner
      _ = _ := integral_finsetSum _ (fun b hb => htermInt b)
  have hGint (N : ℕ) (hMN : Integrable (M N) disorderLaw) :
      Integrable (fun ω => ∫ q, G q ∂πN N ω) disorderLaw :=
    hMN.const_mul ‖separatedCompactTestToBoundedContinuous G‖ |>.mono' ((hImeas G N).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => by
        simpa only [Real.norm_eq_abs] using hIntegralBound G hGtsupport N ω)
  have hcloseFinite : ∀ᶠ N : ℕ in atTop,
      |(∫ ω, IF N ω ∂disorderLaw) - ∫ ω, ∫ q, G q ∂πN N ω ∂disorderLaw| ≤
        δ * C := by
    filter_upwards [hM] with N hMN
    have hGintN := hGint N hMN.1
    have hpoint (ω : Disorder) : ‖IF N ω - ∫ q, G q ∂πN N ω‖ ≤ δ * M N ω := by
      have hμloc : IsLocallyFiniteMeasure (polymerMeasure ϑ N s t ω) :=
        isLocallyFiniteMeasure_polymerMeasure ϑ N s t ω
      have hνloc : IsLocallyFiniteMeasure (polymerMeasure ϑ N r u ω) :=
        isLocallyFiniteMeasure_polymerMeasure ϑ N r u ω
      have hcompact := @abs_integral_sub_le_slabSeparatedCompactMass
        (polymerMeasure ϑ N s t ω) (polymerMeasure ϑ N r u ω)
        hμloc hνloc K g g' hg hg' hone F G hFsupport hGtsupport δ (le_of_lt hδ)
        (fun q => by simpa only [abs_sub_comm] using hGapprox q)
      simpa [IF, πN, slabTwoBlockPiMeasure, M, J₁, J₂, ρ,
        compactTensorTest_apply, mul_assoc] using hcompact
    have hnorm := norm_integral_le_of_norm_le (hMN.1.const_mul δ)
      (Filter.Eventually.of_forall hpoint)
    have hsub := integral_sub (hIFint N hMN.1) hGintN
    calc
      _ = ‖∫ ω, (IF N ω - ∫ q, G q ∂πN N ω) ∂disorderLaw‖ := by
        rw [hsub, Real.norm_eq_abs]
      _ ≤ ∫ ω, δ * M N ω ∂disorderLaw := hnorm
      _ = δ * ∫ ω, M N ω ∂disorderLaw := integral_const_mul _ _
      _ ≤ δ * C := mul_le_mul_of_nonneg_left hMN.2 (le_of_lt hδ)
  have hmid : Tendsto
      (fun N => ∫ ω, ∫ q, G q ∂πN N ω ∂disorderLaw) atTop
      (𝓝 (slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant)
        (t - s) (u - r) G)) := by
    have hsumEvent' := hsumEvent.mono fun N hN => hN.symm
    have hsum' := hsumLimit.congr' hsumEvent'
    simpa only [htargetSum] using hsum'
  have hcloseMiddle : ∀ᶠ N : ℕ in atTop,
      |(∫ ω, ∫ q, G q ∂πN N ω ∂disorderLaw) -
        slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r) G| < ε / 3 :=
    hmid.eventually (Metric.ball_mem_nhds _ (by positivity))
  have hratioC : C / (C + M₁) ≤ 1 := by
    rw [div_le_iff₀ (by positivity : 0 < C + M₁)]
    simpa only [one_mul] using le_add_of_nonneg_right (le_of_lt hM₁pos)
  have hratioM : M₁ / (C + M₁) ≤ 1 := by
    rw [div_le_iff₀ (by positivity : 0 < C + M₁)]
    simpa only [one_mul] using le_add_of_nonneg_left hC.le
  have hfirst : δ * C ≤ ε / 3 := by
    calc
      δ * C = (ε / 3) * (C / (C + M₁)) := by dsimp [δ]; field_simp
      _ ≤ ε / 3 := by
        have h := mul_le_mul_of_nonneg_left hratioC (by positivity : 0 ≤ ε / 3)
        simpa only [mul_one] using h
  have hlast : δ * M₁ ≤ ε / 3 := by
    calc
      δ * M₁ = (ε / 3) * (M₁ / (C + M₁)) := by dsimp [δ]; field_simp
      _ ≤ ε / 3 := by
        have h := mul_le_mul_of_nonneg_left hratioM (by positivity : 0 ≤ ε / 3)
        simpa only [mul_one] using h
  have hevent : ∀ᶠ N : ℕ in atTop,
      dist (∫ ω, IF N ω ∂disorderLaw)
        (slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r) F) < ε := by
    filter_upwards [hcloseFinite, hcloseMiddle] with N hN₁ hN₂
    rw [Real.dist_eq]
    have htri :
        |(∫ ω, IF N ω ∂disorderLaw) -
          slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r) F| ≤
          |(∫ ω, IF N ω ∂disorderLaw) - ∫ ω, ∫ q, G q ∂πN N ω ∂disorderLaw| +
          |(∫ ω, ∫ q, G q ∂πN N ω ∂disorderLaw) -
            slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r) G| +
          |slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r) G -
            slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r) F| := by
      calc
        _ ≤ |(∫ ω, IF N ω ∂disorderLaw) -
            slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r) G| +
            |slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r) G -
              slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r) F| :=
          abs_sub_le _ _ _
        _ ≤ (|(∫ ω, IF N ω ∂disorderLaw) - ∫ ω, ∫ q, G q ∂πN N ω ∂disorderLaw| +
            |(∫ ω, ∫ q, G q ∂πN N ω ∂disorderLaw) -
              slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r) G|) +
            |slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r) G -
              slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r) F| := by
          exact add_le_add_left (abs_sub_le _ _ _) _
        _ = _ := by ring
    have hfinal :
        |(∫ ω, IF N ω ∂disorderLaw) -
          slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r) F| < ε := by
      have htargetApproxRev :
          |slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r) G -
            slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r) F| ≤ δ * M₁ := by
        simpa only [abs_sub_comm] using htargetApprox'
      apply lt_of_le_of_lt htri
      linarith [hN₁, hN₂, htargetApproxRev, hfirst, hlast]
    exact hfinal
  exact eventually_atTop.mp hevent

end Critical2DKPZ.SHF.Flow

end
