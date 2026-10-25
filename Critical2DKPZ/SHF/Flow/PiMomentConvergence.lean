/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.PiTensorApproximation
public import Critical2DKPZ.SHF.Flow.SubseqDenseMoments
public import Critical2DKPZ.SHF.Limit.LocalFinite
public import Critical2DKPZ.SHF.Tsai.CompactTensorMajorants
public import Critical2DKPZ.SHF.Tsai.MomentKernelMeasureFiniteness
public import Critical2DKPZ.SHF.DeltaBose.MomentKernelFinite
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

/-! Finite products of polymer measures admit compact-test moment limits by tensor approximation and uniform sixth-moment control. -/

@[expose] public noncomputable section

open MeasureTheory Filter
open ProbabilityTheory
open BoundedContinuousFunction
open scoped CompactlySupported Topology ENNReal

namespace Critical2DKPZ.SHF.Flow

open Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Tsai
open Critical2DKPZ.DeltaBose

private def piPairHomeomorph (n : ℕ) :
    (Fin n → Plane × Plane) ≃ₜ (Configuration n × Configuration n) where
  toEquiv := Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Plane) (fun _ => Plane)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem piPairHomeomorph_symm_apply {n : ℕ} (x y : Configuration n) (i : Fin n) :
    (piPairHomeomorph n).symm (x, y) i = (x i, y i) := by
  simp [piPairHomeomorph, Equiv.arrowProdEquivProdArrow]

private theorem piPairHomeomorph_symm_pair {n : ℕ} (x y : Configuration n) :
    (piPairHomeomorph n).symm (x, y) = fun i => (x i, y i) := by
  funext i
  exact piPairHomeomorph_symm_apply x y i

private def piTensorTestCC {n : ℕ} (φ : Fin n → C_c(Plane × Plane, ℝ)) :
    C_c((Fin n → Plane × Plane), ℝ) := by
  let R : Set (Fin n → Plane × Plane) := Set.univ.pi fun i => tsupport (φ i)
  have hR : IsCompact R := isCompact_univ_pi fun i => (φ i).hasCompactSupport
  refine ⟨⟨fun q => ∏ i, φ i (q i), by fun_prop⟩, ?_⟩
  apply HasCompactSupport.of_support_subset_isCompact hR
  intro q hq
  apply Set.mem_univ_pi.mpr
  intro i
  by_contra hi
  have hzero : φ i (q i) = 0 := image_eq_zero_of_notMem_tsupport hi
  apply hq
  simp only [Finset.prod_eq_zero (Finset.mem_univ i), hzero]

private theorem piTensorTestCC_apply {n : ℕ} (φ : Fin n → C_c(Plane × Plane, ℝ))
    (q : Fin n → Plane × Plane) : piTensorTestCC φ q = ∏ i, φ i (q i) := rfl

private def ccBound {X : Type*} [TopologicalSpace X] (f : C_c(X, ℝ)) : X →ᵇ ℝ :=
  ofCompactSupport f f.continuous f.hasCompactSupport

private def piPullTestCC {n : ℕ} (F : C_c((Fin n → Plane × Plane), ℝ)) :
    C_c((Configuration n × Configuration n), ℝ) := by
  let e := piPairHomeomorph n
  refine ⟨⟨fun z => F (e.symm z), F.continuous.comp e.symm.continuous⟩, ?_⟩
  apply HasCompactSupport.of_support_subset_isCompact (F.hasCompactSupport.image e.continuous)
  intro z hz
  refine ⟨e.symm z, subset_tsupport _ hz, ?_⟩
  simp [e]

private theorem piPullTestCC_apply {n : ℕ}
    (F : C_c((Fin n → Plane × Plane), ℝ)) (z : Configuration n × Configuration n) :
    piPullTestCC F z = F ((piPairHomeomorph n).symm z) := rfl

private theorem measurable_integral_measure_cc {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (f : C_c(X, ℝ)) :
    Measurable (fun μ : Measure X => ∫ x, f x ∂μ) := by
  let κ : Kernel (Measure X) X := ⟨id, measurable_id⟩
  exact (((map_continuous f).measurable).stronglyMeasurable.integral_kernel
    (κ := κ)).measurable

private theorem integral_momentKernel_measure_eq_iterated {n : ℕ} (hn : n ≤ 4)
    (θ : ℝ) {τ : ℝ} (hτ : 0 < τ) (F : C_c((Configuration n × Configuration n), ℝ)) :
    (∫ z, F z ∂((volume.prod volume).withDensity
      (Function.uncurry (momentKernel n θ τ)))) =
      ∫ x : Configuration n, ∫ y : Configuration n,
        F (x, y) * (momentKernel n θ τ x y).toReal := by
  let ν : Measure (Configuration n × Configuration n) :=
    (volume.prod volume).withDensity (Function.uncurry (momentKernel n θ τ))
  have hνloc : IsLocallyFiniteMeasure ν :=
    locallyFinite_momentKernelMeasure n θ hτ
  have hν : Integrable (F : Configuration n × Configuration n → ℝ) ν :=
    integrable_compactTest_of_locallyFinite ν hνloc F
  have hK : Measurable (Function.uncurry (momentKernel n θ τ)) := by
    exact Measurable.comp
      (g := fun p : (ℝ × ℝ) × Configuration n × Configuration n =>
        momentKernel n p.1.1 p.1.2 p.2.1 p.2.2)
      (f := fun z : Configuration n × Configuration n => ((θ, τ), z))
      (measurable_momentKernel n) (measurable_const.prodMk measurable_id)
  have hKtop : ∀ᵐ z ∂(volume.prod volume), momentKernel n θ τ z.1 z.2 < ⊤ := by
    filter_upwards [momentKernel_ne_top n hn θ hτ] with z hz
    exact lt_top_iff_ne_top.mpr hz
  have hprod : Integrable (fun z : Configuration n × Configuration n =>
      F z * (momentKernel n θ τ z.1 z.2).toReal) (volume.prod volume) :=
    (integrable_withDensity_iff hK hKtop).mp hν
  calc
    _ = ∫ z, (momentKernel n θ τ z.1 z.2).toReal * F z ∂(volume.prod volume) :=
      integral_withDensity_eq_integral_toReal_smul hK hKtop F
    _ = ∫ z, F z * (momentKernel n θ τ z.1 z.2).toReal ∂(volume.prod volume) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => mul_comm _ _
    _ = ∫ x : Configuration n, ∫ y : Configuration n,
        F (x, y) * (momentKernel n θ τ x y).toReal := integral_prod _ hprod

private theorem piTensor_integral_eq_product {n : ℕ}
    (μ : Measure (Plane × Plane)) (hμ : SigmaFinite μ)
    (φ : Fin n → C_c(Plane × Plane, ℝ)) :
    (∫ q, piTensorTestCC φ q ∂Measure.pi (fun _ : Fin n => μ)) =
      ∏ i, ∫ p, φ i p ∂μ := by
  change (∫ q, ∏ i, φ i (q i) ∂Measure.pi (fun _ : Fin n => μ)) = _
  exact @MeasureTheory.integral_fintype_prod_eq_prod ℝ (Fin n) inferInstance inferInstance
    (fun _ => Plane × Plane) (fun i p => φ i p)
    (mE := fun _ => inferInstance) (μ := fun _ => μ) (fun _ => hμ)

private theorem piTensor_target_eq_sum {n r : ℕ} (hn : n ≤ 4)
    (θ : ℝ) {τ : ℝ} (hτ : 0 < τ) (φ : Fin r → Fin n → C_c(Plane × Plane, ℝ)) :
    (∫ x : Configuration n, ∫ y : Configuration n,
      (∑ b, ∏ i, φ b i (x i, y i)) * (momentKernel n θ τ x y).toReal) =
      ∑ b, ∫ x : Configuration n, ∫ y : Configuration n,
        (∏ i, φ b i (x i, y i)) * (momentKernel n θ τ x y).toReal := by
  let T : Fin r → C_c((Fin n → Plane × Plane), ℝ) := fun b => piTensorTestCC (φ b)
  let A : C_c((Fin n → Plane × Plane), ℝ) := ∑ b, T b
  have hpoint (q : Fin n → Plane × Plane) : A q = ∑ b, ∏ i, φ b i (q i) := by
    simp only [A, T, CompactlySupportedContinuousMap.sum_apply, piTensorTestCC_apply]
  have hpull : piPullTestCC A = ∑ b, piPullTestCC (T b) := by
    ext z
    simp only [piPullTestCC_apply, A, CompactlySupportedContinuousMap.sum_apply]
  have hAvalue (x y : Configuration n) : piPullTestCC A (x, y) =
      ∑ b, ∏ i, φ b i (x i, y i) := by
    rw [piPullTestCC_apply]
    rw [hpoint]
    simp only [piPairHomeomorph_symm_apply]
  calc
    _ = ∫ x : Configuration n, ∫ y : Configuration n,
        piPullTestCC A (x, y) * (momentKernel n θ τ x y).toReal := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        apply integral_congr_ae
        exact Eventually.of_forall fun y => by
          change (∑ b, ∏ i, φ b i (x i, y i)) * _ = _
          rw [← hAvalue]
    _ = ∫ z, piPullTestCC A z ∂((volume.prod volume).withDensity
        (Function.uncurry (momentKernel n θ τ))) :=
      (integral_momentKernel_measure_eq_iterated hn θ hτ (piPullTestCC A)).symm
    _ = ∑ b, ∫ z, piPullTestCC (T b) z ∂((volume.prod volume).withDensity
        (Function.uncurry (momentKernel n θ τ))) := by
      rw [hpull]
      simp only [CompactlySupportedContinuousMap.sum_apply]
      exact integral_finsetSum _ (fun b _ => integrable_compactTest_of_locallyFinite _
        (locallyFinite_momentKernelMeasure n θ hτ) (piPullTestCC (T b)))
    _ = ∑ b, ∫ x : Configuration n, ∫ y : Configuration n,
        (∏ i, φ b i (x i, y i)) * (momentKernel n θ τ x y).toReal := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [integral_momentKernel_measure_eq_iterated hn θ hτ (piPullTestCC (T b))]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        apply integral_congr_ae
        exact Eventually.of_forall fun y => by
          change (piPullTestCC (T b) (x, y)) * _ = _
          rw [piPullTestCC_apply]
          simp only [piPairHomeomorph_symm_apply, T, piTensorTestCC_apply]


/-- Endpoint-tensor moment convergence extends to compactly supported continuous replica tests, with eventual integrability supplied by `eventually_compactTensor_product_rpow_bound`. -/
theorem polymerMeasure_pi_moment_tendsto_of (ϑ : ℝ) (hPolymerMomentInput : PolymerMomentLimit ϑ)
    (hFlatSixthMomentInput : FlatSixthMomentBound ϑ) (n : ℕ) (hn1 : 1 ≤ n) (hn4 : n ≤ 4) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (F : (Fin n → Plane × Plane) → ℝ)
    (hF : Continuous F) (hFc : HasCompactSupport F) :
    Tendsto (fun N => ∫ ω, ∫ q, F q ∂(Measure.pi fun _ : Fin n => polymerMeasure ϑ N s t ω)
        ∂disorderLaw) atTop
      (𝓝 (∫ x : DeltaBose.Configuration n, ∫ y : DeltaBose.Configuration n,
        F (fun i => (x i, y i)) *
          (DeltaBose.momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal)) := by
  classical
  let Fcc : C_c((Fin n → Plane × Plane), ℝ) := ⟨⟨F, hF⟩, hFc⟩
  have hFcc_apply (q : Fin n → Plane × Plane) : Fcc q = F q := rfl
  obtain ⟨K, hK, htensor⟩ := exists_compactTensorProduct_uniform_approx hn1 Fcc
  obtain ⟨g, g', hg, hg', hone⟩ := exists_compactTensor_majorant K hK
  let ψ : C_c(Plane × Plane, ℝ) := compactTensorTest g g'
  have hψnonneg (p : Plane × Plane) : 0 ≤ ψ p := by
    simp only [ψ, compactTensorTest_apply]
    exact mul_nonneg (hg _) (hg' _)
  have hψone (p : Plane × Plane) (hp : p ∈ K) : ψ p = 1 := by
    exact hone p hp
  have hνloc : IsLocallyFiniteMeasure
      ((volume.prod volume).withDensity
        (Function.uncurry (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s)))) :=
    locallyFinite_momentKernelMeasure n _ (by linarith)
  let ν : Measure (Configuration n × Configuration n) :=
    (volume.prod volume).withDensity
      (Function.uncurry (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s)))
  let hψcc : C_c((Fin n → Plane × Plane), ℝ) := piTensorTestCC (fun _ => ψ)
  let Hψ : C_c((Configuration n × Configuration n), ℝ) := piPullTestCC hψcc
  let Lψ : ℝ := ∫ z, Hψ z ∂ν
  have hLψint : Integrable (Hψ : Configuration n × Configuration n → ℝ) ν := by
    exact integrable_compactTest_of_locallyFinite ν hνloc Hψ
  have hHψnonneg (z : Configuration n × Configuration n) : 0 ≤ Hψ z := by
    rw [piPullTestCC_apply]
    simp only [hψcc, piTensorTestCC_apply]
    exact Finset.prod_nonneg fun i hi => hψnonneg (z.1 i, z.2 i)
  have hLψnonneg : 0 ≤ Lψ := integral_nonneg hHψnonneg
  obtain ⟨C₆, hC₆⟩ := eventually_compactTensor_product_rpow_bound ϑ hFlatSixthMomentInput
    1 (by omega) (by omega) hs hst (fun _ : Fin 1 => g) (fun _ => g')
  let J : ℕ → Disorder → ℝ := fun N ω =>
    ∫ p, ψ p ∂polymerMeasure ϑ N s t ω
  have hJmeas (N : ℕ) : Measurable (J N) := by
    exact (measurable_integral_measure_cc ψ).comp (measurable_polymerMeasure ϑ N s t)
  have hJnonneg (N : ℕ) (ω : Disorder) : 0 ≤ J N ω :=
    integral_nonneg fun p => hψnonneg p
  have hJevent : ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω => (J N ω) ^ 6) disorderLaw ∧
        ∫ ω, (J N ω) ^ 6 ∂disorderLaw ≤ C₆ := by
    filter_upwards [hC₆] with N hN
    refine ⟨?_, ?_⟩
    · have heq (ω : Disorder) :
          |∏ i : Fin 1, ∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N s t ω| ^
            ((6 : ℝ) / ((1 : ℕ) : ℝ)) = (J N ω) ^ 6 := by
        have hbase : (∏ i : Fin 1,
            ∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N s t ω) = J N ω := by
          simp [J, ψ, compactTensorTest_apply]
        rw [hbase, abs_of_nonneg (hJnonneg N ω)]
        norm_num [Real.rpow_natCast]
      exact hN.1.congr (Eventually.of_forall fun ω => by
        exact heq ω)
    · have heq (ω : Disorder) :
          |∏ i : Fin 1, ∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N s t ω| ^
            ((6 : ℝ) / ((1 : ℕ) : ℝ)) = (J N ω) ^ 6 := by
        have hbase : (∏ i : Fin 1,
            ∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N s t ω) = J N ω := by
          simp [J, ψ, compactTensorTest_apply]
        rw [hbase, abs_of_nonneg (hJnonneg N ω)]
        norm_num [Real.rpow_natCast]
      have hIntEq : ∫ ω, (J N ω) ^ 6 ∂disorderLaw =
          ∫ ω, |∏ i : Fin 1,
            ∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N s t ω| ^
              ((6 : ℝ) / ((1 : ℕ) : ℝ)) ∂disorderLaw := by
        apply integral_congr_ae
        exact Eventually.of_forall fun ω => by
          exact (heq ω).symm
      rw [hIntEq]
      exact hN.2
  have hJpowerEvent (m : ℕ) (hm : m ≤ 4) : ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω => (J N ω) ^ m) disorderLaw ∧
        ∫ ω, (J N ω) ^ m ∂disorderLaw ≤ 1 + max C₆ 0 := by
    filter_upwards [hJevent] with N hN
    have hmajor : Integrable (fun ω => 1 + (J N ω) ^ 6) disorderLaw :=
      (integrable_const (1 : ℝ)).add hN.1
    have hpowmeas : AEStronglyMeasurable (fun ω => (J N ω) ^ m) disorderLaw :=
      ((continuous_id.pow m).comp_aestronglyMeasurable (hJmeas N).aestronglyMeasurable)
    have hpoint (ω : Disorder) : ‖(J N ω) ^ m‖ ≤ 1 + (J N ω) ^ 6 := by
      rw [Real.norm_of_nonneg (pow_nonneg (hJnonneg N ω) _)]
      have hx := hJnonneg N ω
      by_cases hle : J N ω ≤ 1
      · have hmle : (J N ω) ^ m ≤ 1 := pow_le_one₀ hx hle
        nlinarith [pow_nonneg hx 6]
      · have hge : 1 ≤ J N ω := le_of_not_ge hle
        have hpow : (J N ω) ^ m ≤ (J N ω) ^ 6 :=
          pow_le_pow_right₀ hge (by omega)
        exact hpow.trans (le_add_of_nonneg_left (by positivity))
    have hInt : Integrable (fun ω => (J N ω) ^ m) disorderLaw := hmajor.mono' hpowmeas
      (Eventually.of_forall hpoint)
    have hbound : ∫ ω, (J N ω) ^ m ∂disorderLaw ≤ 1 + max C₆ 0 := by
      calc
        ∫ ω, (J N ω) ^ m ∂disorderLaw ≤ ∫ ω, 1 + (J N ω) ^ 6 ∂disorderLaw :=
          integral_mono hInt hmajor (fun ω => by
            simpa only [Real.norm_of_nonneg (pow_nonneg (hJnonneg N ω) _)] using hpoint ω)
        _ = 1 + ∫ ω, (J N ω) ^ 6 ∂disorderLaw := by
          rw [integral_add (integrable_const _) hN.1, integral_const]
          simp [Measure.real, measure_univ]
        _ ≤ 1 + max C₆ 0 :=
          add_le_add (le_rfl : (1 : ℝ) ≤ 1) (hN.2.trans (le_max_left C₆ 0))
    exact ⟨hInt, hbound⟩
  have hNbound := hJpowerEvent n (by omega)
  let M₀ : ℝ := 1 + max C₆ 0
  let M₁ : ℝ := 1 + max Lψ 0
  have hM₀ : 0 < M₀ := by dsimp [M₀]; positivity
  have hM₁ : 0 < M₁ := by dsimp [M₁]; positivity
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let δ : ℝ := ε / (3 * (M₀ + M₁))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨r, φ, hφsupport, happrox⟩ := htensor δ hδ
  let T : Fin r → C_c((Fin n → Plane × Plane), ℝ) := fun b => piTensorTestCC (φ b)
  let A : C_c((Fin n → Plane × Plane), ℝ) := ∑ b, T b
  have hAapply (q : Fin n → Plane × Plane) : A q = ∑ b, ∏ i, φ b i (q i) := by
    simp only [A, T, CompactlySupportedContinuousMap.sum_apply, piTensorTestCC_apply]
  have hAzero (q : Fin n → Plane × Plane)
      (hq : q ∉ Set.univ.pi fun _ : Fin n => K) : A q = 0 := by
    have hnot : ¬ ∀ i : Fin n, q i ∈ K := by simpa using hq
    push Not at hnot
    obtain ⟨i, hi⟩ := hnot
    rw [hAapply]
    apply Finset.sum_eq_zero
    intro b hb
    have hzero : φ b i (q i) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hx => hi (hφsupport b i hx))
    simp only [Finset.prod_eq_zero (Finset.mem_univ i), hzero]
  have hFzero (q : Fin n → Plane × Plane)
      (hq : q ∉ Set.univ.pi fun _ : Fin n => K) : F q = 0 := by
    by_contra hne
    have habs : 0 < |F q| := abs_pos.mpr hne
    obtain ⟨r', φ', hφsupport', happrox'⟩ := htensor (|F q| / 2) (by positivity)
    have hzero : (∑ b : Fin r', ∏ i, φ' b i (q i)) = 0 := by
      have hnot : ¬ ∀ i : Fin n, q i ∈ K := by simpa using hq
      push Not at hnot
      obtain ⟨i, hi⟩ := hnot
      apply Finset.sum_eq_zero
      intro b hb
      have hφzero : φ' b i (q i) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hx => hi (hφsupport' b i hx))
      simp only [Finset.prod_eq_zero (Finset.mem_univ i), hφzero]
    have := happrox' q
    rw [hzero] at this
    have hsmall : |F q| < |F q| / 2 := by simpa [hzero, Fcc] using this
    nlinarith [abs_nonneg (F q)]
  have hAerr (q : Fin n → Plane × Plane) :
      |A q - F q| ≤ δ * ∏ i, ψ (q i) := by
    by_cases hq : q ∈ Set.univ.pi fun _ : Fin n => K
    · have hprod : ∏ i, ψ (q i) = 1 := by
        apply Finset.prod_eq_one
        intro i hi
        exact hψone (q i) ((Set.mem_univ_pi.mp hq) i)
      rw [hprod, hAapply]
      change |(∑ b, ∏ i, φ b i (q i)) - Fcc q| ≤ δ * 1
      rw [mul_one]
      simpa only [Fcc] using (happrox q).le
    · rw [hAzero q hq, hFzero q hq]
      have hnonneg : 0 ≤ δ * ∏ i, ψ (q i) :=
        mul_nonneg hδ.le (Finset.prod_nonneg fun i hi => hψnonneg (q i))
      simp only [sub_self, abs_zero]
      exact hnonneg
  let piMeasureN : ℕ → Disorder → Measure (Fin n → Plane × Plane) := fun N ω =>
    Measure.pi (fun _ : Fin n => polymerMeasure ϑ N s t ω)
  have hSigma (N : ℕ) (ω : Disorder) :
      SigmaFinite (polymerMeasure ϑ N s t ω) :=
    @MeasureTheory.sigmaFinite_of_locallyFinite (Plane × Plane) _
      (polymerMeasure ϑ N s t ω) inferInstance inferInstance
      (isLocallyFiniteMeasure_polymerMeasure ϑ N s t ω)
  have hLFpi (N : ℕ) (ω : Disorder) : IsLocallyFiniteMeasure (piMeasureN N ω) := by
    exact @MeasureTheory.Measure.pi.isLocallyFiniteMeasure
      (Fin n) (fun _ => Plane × Plane) inferInstance (fun _ => inferInstance)
      (fun _ => polymerMeasure ϑ N s t ω) (fun _ => hSigma N ω)
      (fun _ => inferInstance) (fun _ => isLocallyFiniteMeasure_polymerMeasure ϑ N s t ω)
  have hPiMeasureMeas : ∀ N, Measurable (piMeasureN N) := by
    intro N
    exact measurable_piMeasure_of_locallyFinite n
      (fun _ : Fin n => polymerMeasure ϑ N s t)
      (fun _ => measurable_polymerMeasure ϑ N s t)
      (fun _ ω => isLocallyFiniteMeasure_polymerMeasure ϑ N s t ω)
  have hImeas (G : C_c((Fin n → Plane × Plane), ℝ)) (N : ℕ) :
      Measurable (fun ω => ∫ q, G q ∂piMeasureN N ω) :=
    (measurable_integral_measure_cc G).comp (hPiMeasureMeas N)
  let IF (N : ℕ) (ω : Disorder) : ℝ := ∫ q, Fcc q ∂piMeasureN N ω
  let IA (N : ℕ) (ω : Disorder) : ℝ := ∫ q, A q ∂piMeasureN N ω
  let Iψ (N : ℕ) (ω : Disorder) : ℝ := ∫ q, ∏ i, ψ (q i) ∂piMeasureN N ω
  have hIψ (N : ℕ) (ω : Disorder) : Iψ N ω = (J N ω) ^ n := by
    calc
      Iψ N ω = ∏ i : Fin n, ∫ p, ψ p ∂polymerMeasure ϑ N s t ω := by
        change (∫ q, piTensorTestCC (fun _ : Fin n => ψ) q ∂Measure.pi
          (fun _ : Fin n => polymerMeasure ϑ N s t ω)) = _
        exact piTensor_integral_eq_product (polymerMeasure ϑ N s t ω)
          (hSigma N ω) (fun _ => ψ)
      _ = (J N ω) ^ n := by
        simp only [J, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hIψint (N : ℕ) (ω : Disorder) :
      Integrable (fun q : Fin n → Plane × Plane => ∏ i, ψ (q i)) (piMeasureN N ω) := by
    have hI := integrable_compactTest_of_locallyFinite (piMeasureN N ω) (hLFpi N ω)
      (piTensorTestCC (fun _ : Fin n => ψ))
    exact hI.congr (Filter.Eventually.of_forall fun q => piTensorTestCC_apply _ q)
  have hIψ_eq (N : ℕ) (ω : Disorder) :
      (∫ q : Fin n → Plane × Plane, ∏ i, ψ (q i) ∂piMeasureN N ω) =
        (J N ω) ^ n := hIψ N ω
  have hIAerr (N : ℕ) (ω : Disorder) : |IA N ω - IF N ω| ≤ δ * (J N ω) ^ n := by
    have hmajor : Integrable (fun q : Fin n → Plane × Plane =>
        δ * ∏ i, ψ (q i)) (piMeasureN N ω) := (hIψint N ω).const_mul δ
    have hpoint (q : Fin n → Plane × Plane) :
        ‖A q - Fcc q‖ ≤ δ * ∏ i, ψ (q i) := by
      rw [Real.norm_eq_abs]
      rw [hFcc_apply]
      exact hAerr q
    have hbound := norm_integral_le_of_norm_le (f := fun q => A q - Fcc q) hmajor
      (Eventually.of_forall hpoint)
    have hsub : (∫ q, A q - Fcc q ∂piMeasureN N ω) = IA N ω - IF N ω :=
      integral_sub (integrable_compactTest_of_locallyFinite _
        (hLFpi N ω) A)
        (integrable_compactTest_of_locallyFinite _
          (hLFpi N ω) Fcc)
    rw [hsub] at hbound
    rw [Real.norm_eq_abs, integral_const_mul] at hbound
    rw [hIψ_eq N ω] at hbound
    exact hbound
  have hIAintegrable (N : ℕ) (hN : Integrable (fun ω => (J N ω) ^ n) disorderLaw) :
      Integrable (IA N) disorderLaw := by
    let B_F : ℝ := ‖ccBound Fcc‖
    have hpt (ω : Disorder) : ‖IA N ω‖ ≤ (B_F + δ) * (J N ω) ^ n := by
      have hFbound (q : Fin n → Plane × Plane) : |Fcc q| ≤ B_F * ∏ i, ψ (q i) := by
        by_cases hq : q ∈ Set.univ.pi fun _ : Fin n => K
        · have hp : ∏ i, ψ (q i) = 1 := by
            apply Finset.prod_eq_one
            intro i hi
            exact hψone (q i) ((Set.mem_univ_pi.mp hq) i)
          rw [hp]
          have hn := (ccBound Fcc).norm_coe_le_norm q
          rw [Real.norm_eq_abs] at hn
          change |(ccBound Fcc) q| ≤ ‖ccBound Fcc‖ * 1
          simpa only [mul_one] using hn
        · have hzero : Fcc q = 0 := by rw [hFcc_apply q]; exact hFzero q hq
          simpa only [hzero, abs_zero] using
            (mul_nonneg (norm_nonneg (ccBound Fcc))
              (Finset.prod_nonneg fun i hi => hψnonneg (q i)))
      have hApoint (q : Fin n → Plane × Plane) :
          |A q| ≤ (B_F + δ) * ∏ i, ψ (q i) := by
        calc
          |A q| ≤ |Fcc q| + |A q - Fcc q| := by
            have := abs_add_le (Fcc q) (A q - Fcc q)
            simpa only [add_sub_cancel] using this
          _ ≤ B_F * ∏ i, ψ (q i) + δ * ∏ i, ψ (q i) :=
            add_le_add (hFbound q) (hAerr q)
          _ = _ := by ring
      have hApointNorm (q : Fin n → Plane × Plane) :
          ‖A q‖ ≤ (B_F + δ) * ∏ i, ψ (q i) := by
        rw [Real.norm_eq_abs]
        exact hApoint q
      have hnorm := norm_integral_le_of_norm_le
        (f := fun q => A q) ((hIψint N ω).const_mul (B_F + δ))
        (Eventually.of_forall hApointNorm)
      change ‖IA N ω‖ ≤ ∫ q, (B_F + δ) * ∏ i, ψ (q i) ∂piMeasureN N ω at hnorm
      rw [integral_const_mul] at hnorm
      rw [hIψ_eq N ω] at hnorm
      exact hnorm
    have hdom : Integrable (fun ω => (B_F + δ) * (J N ω) ^ n) disorderLaw :=
      hN.const_mul (B_F + δ)
    exact hdom.mono' ((hImeas A N).aestronglyMeasurable) (Eventually.of_forall hpt)
  have hIFintegrable (N : ℕ) (hN : Integrable (fun ω => (J N ω) ^ n) disorderLaw) :
      Integrable (IF N) disorderLaw := by
    let B_F : ℝ := ‖ccBound Fcc‖
    have hpt (ω : Disorder) : ‖IF N ω‖ ≤ B_F * (J N ω) ^ n := by
      have hFbound (q : Fin n → Plane × Plane) :
          |Fcc q| ≤ B_F * ∏ i, ψ (q i) := by
        by_cases hq : q ∈ Set.univ.pi fun _ : Fin n => K
        · have hp : ∏ i, ψ (q i) = 1 := by
            apply Finset.prod_eq_one
            intro i hi
            exact hψone (q i) ((Set.mem_univ_pi.mp hq) i)
          rw [hp]
          have hn := (ccBound Fcc).norm_coe_le_norm q
          rw [Real.norm_eq_abs] at hn
          change |(ccBound Fcc) q| ≤ ‖ccBound Fcc‖ * 1
          simpa only [mul_one] using hn
        · have hzero : Fcc q = 0 := by rw [hFcc_apply q]; exact hFzero q hq
          simpa only [hzero, abs_zero] using
            (mul_nonneg (norm_nonneg (ccBound Fcc))
              (Finset.prod_nonneg fun i hi => hψnonneg (q i)))
      have hFboundNorm (q : Fin n → Plane × Plane) :
          ‖Fcc q‖ ≤ B_F * ∏ i, ψ (q i) := by
        rw [Real.norm_eq_abs]
        exact hFbound q
      have hnorm := norm_integral_le_of_norm_le (f := fun q => Fcc q)
        ((hIψint N ω).const_mul B_F) (Eventually.of_forall hFboundNorm)
      change ‖IF N ω‖ ≤ ∫ q, B_F * ∏ i, ψ (q i) ∂piMeasureN N ω at hnorm
      rw [integral_const_mul] at hnorm
      rw [hIψ_eq N ω] at hnorm
      exact hnorm
    have hdom : Integrable (fun ω => B_F * (J N ω) ^ n) disorderLaw :=
      hN.const_mul B_F
    exact hdom.mono' ((hImeas Fcc N).aestronglyMeasurable) (Eventually.of_forall hpt)
  have hterm (b : Fin r) : Tendsto
      (fun N => ∫ ω, ∫ q, T b q ∂piMeasureN N ω ∂disorderLaw) atTop
      (𝓝 (∫ x : Configuration n, ∫ y : Configuration n,
        (∏ i, φ b i (x i, y i)) *
          (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal)) := by
    have h := hPolymerMomentInput n hn1 hn4 hs hst (φ b)
    have hseq : (fun N => ∫ ω, ∫ q, T b q ∂piMeasureN N ω ∂disorderLaw) =
        fun N => ∫ ω, ∏ i, ∫ p, φ b i p ∂polymerMeasure ϑ N s t ω ∂disorderLaw := by
      funext N
      apply integral_congr_ae
      exact Eventually.of_forall fun ω => by
        exact piTensor_integral_eq_product (polymerMeasure ϑ N s t ω)
          (hSigma N ω) (φ b)
    rw [hseq]
    exact h
  have hsumSeq : ∀ᶠ N : ℕ in atTop,
      (∫ ω, IA N ω ∂disorderLaw) =
        ∑ b : Fin r, ∫ ω, ∫ q, T b q ∂piMeasureN N ω ∂disorderLaw := by
    filter_upwards [hNbound] with N hN
    have htermBound (b : Fin r) (ω : Disorder) :
        |∫ q, T b q ∂piMeasureN N ω| ≤ ‖ccBound (T b)‖ * (J N ω) ^ n := by
      have hpoint (q : Fin n → Plane × Plane) :
          |T b q| ≤ ‖ccBound (T b)‖ * ∏ i, ψ (q i) := by
        by_cases hq : q ∈ Set.univ.pi fun _ : Fin n => K
        · have hp : ∏ i, ψ (q i) = 1 := by
            apply Finset.prod_eq_one
            intro i hi
            exact hψone (q i) ((Set.mem_univ_pi.mp hq) i)
          rw [hp]
          have hn := (ccBound (T b)).norm_coe_le_norm q
          rw [Real.norm_eq_abs] at hn
          change |(ccBound (T b)) q| ≤ ‖ccBound (T b)‖ * 1
          simpa only [mul_one] using hn
        · have hzero : T b q = 0 := by
            have hnot : ¬ ∀ i : Fin n, q i ∈ K := by simpa using hq
            push Not at hnot
            obtain ⟨i, hi⟩ := hnot
            change (∏ i, φ b i (q i)) = 0
            apply Finset.prod_eq_zero (Finset.mem_univ i)
            exact image_eq_zero_of_notMem_tsupport (fun hx => hi (hφsupport b i hx))
          rw [hzero]
          simpa only [hzero, abs_zero] using
            (mul_nonneg (norm_nonneg (ccBound (T b)))
              (Finset.prod_nonneg fun i hi => hψnonneg (q i)))
      have hpointNorm (q : Fin n → Plane × Plane) :
          ‖T b q‖ ≤ ‖ccBound (T b)‖ * ∏ i, ψ (q i) := by
        rw [Real.norm_eq_abs]
        exact hpoint q
      have hnorm := norm_integral_le_of_norm_le (f := fun q => T b q)
        ((hIψint N ω).const_mul ‖ccBound (T b)‖)
        (Eventually.of_forall hpointNorm)
      change |∫ q, T b q ∂piMeasureN N ω| ≤
        ∫ q, ‖ccBound (T b)‖ * ∏ i, ψ (q i) ∂piMeasureN N ω at hnorm
      rw [integral_const_mul] at hnorm
      rw [hIψ_eq N ω] at hnorm
      exact hnorm
    have htermInt (b : Fin r) :
        Integrable (fun ω => ∫ q, T b q ∂piMeasureN N ω) disorderLaw := by
      have hdom : Integrable (fun ω => ‖ccBound (T b)‖ * (J N ω) ^ n) disorderLaw :=
        hN.1.const_mul ‖ccBound (T b)‖
      exact hdom.mono' ((hImeas (T b) N).aestronglyMeasurable)
        (Eventually.of_forall fun ω => by
          simpa only [Real.norm_eq_abs] using htermBound b ω)
    have hinner (ω : Disorder) : IA N ω =
        ∑ b : Fin r, ∫ q, T b q ∂piMeasureN N ω := by
      calc
        IA N ω = ∫ q, (∑ b : Fin r, T b q) ∂piMeasureN N ω := by
          apply integral_congr_ae
          exact Eventually.of_forall fun q => by
            simp only [A, CompactlySupportedContinuousMap.sum_apply]
        _ = ∑ b, ∫ q, T b q ∂piMeasureN N ω := by
          rw [integral_finsetSum]
          intro b hb
          exact integrable_compactTest_of_locallyFinite _
            (hLFpi N ω) (T b)
    calc
      _ = ∫ ω, ∑ b : Fin r, ∫ q, T b q ∂piMeasureN N ω ∂disorderLaw := by
        apply integral_congr_ae
        exact Eventually.of_forall fun ω => hinner ω
      _ = _ := integral_finsetSum _ (fun b hb => htermInt b)
  have hsum_tendsto : Tendsto (fun N => ∫ ω, IA N ω ∂disorderLaw) atTop
      (𝓝 (∫ x : Configuration n, ∫ y : Configuration n,
        A (fun i => (x i, y i)) *
          (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal)) := by
    have hlim : ∑ b : Fin r, ∫ x : Configuration n, ∫ y : Configuration n,
        (∏ i, φ b i (x i, y i)) *
          (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal =
        ∫ x : Configuration n, ∫ y : Configuration n,
          A (fun i => (x i, y i)) *
            (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal := by
      rw [← piTensor_target_eq_sum hn4 _ (by linarith) φ]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        apply integral_congr_ae
        exact Eventually.of_forall fun y => by
          change (∑ b, ∏ i, φ b i (x i, y i)) *
              (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal =
            A (fun i => (x i, y i)) *
              (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal
          rw [← hAapply (fun i => (x i, y i))]
    have hsum' : Tendsto
        (fun N => ∑ b : Fin r, ∫ ω, ∫ q, T b q ∂piMeasureN N ω ∂disorderLaw)
        atTop (𝓝 (∑ b : Fin r, ∫ x : Configuration n, ∫ y : Configuration n,
          (∏ i, φ b i (x i, y i)) *
            (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal)) := by
      exact tendsto_finsetSum Finset.univ (fun b hb => hterm b)
    have hsumSeq' : ∀ᶠ N : ℕ in atTop,
        (∑ b : Fin r, ∫ ω, ∫ q, T b q ∂piMeasureN N ω ∂disorderLaw) =
          ∫ ω, IA N ω ∂disorderLaw := hsumSeq.mono fun N hN => hN.symm
    have hsum'' := hsum'.congr' hsumSeq'
    simpa only [hlim] using hsum''
  have hcloseN : ∀ᶠ N : ℕ in atTop,
      |(∫ ω, IF N ω ∂disorderLaw) - ∫ ω, IA N ω ∂disorderLaw| ≤ δ * M₀ := by
    filter_upwards [hNbound] with N hN
    have hpoint (ω : Disorder) : ‖IF N ω - IA N ω‖ ≤ δ * (J N ω) ^ n := by
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact hIAerr N ω
    have hbound := norm_integral_le_of_norm_le (f := fun ω => IF N ω - IA N ω)
      (hN.1.const_mul δ)
      (Eventually.of_forall hpoint)
    have heq := integral_sub (hIFintegrable N hN.1) (hIAintegrable N hN.1)
    calc
      |(∫ ω, IF N ω ∂disorderLaw) - ∫ ω, IA N ω ∂disorderLaw| =
          ‖∫ ω, IF N ω - IA N ω ∂disorderLaw‖ := by rw [heq, Real.norm_eq_abs]
      _ ≤ ∫ ω, δ * (J N ω) ^ n ∂disorderLaw := hbound
      _ = δ * ∫ ω, (J N ω) ^ n ∂disorderLaw := integral_const_mul _ _
      _ ≤ δ * M₀ := mul_le_mul_of_nonneg_left hN.2 hδ.le
  have hcloseLimit :
      |(∫ x : Configuration n, ∫ y : Configuration n,
          F (fun i => (x i, y i)) *
            (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal) -
        ∫ x : Configuration n, ∫ y : Configuration n,
          A (fun i => (x i, y i)) *
            (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal| ≤ δ * M₁ := by
    let θ := ϑ - Real.eulerMascheroniConstant
    let τ := t - s
    let Hψ' := piPullTestCC (piTensorTestCC (fun _ : Fin n => ψ))
    let Hdiff : C_c((Configuration n × Configuration n), ℝ) :=
      piPullTestCC (Fcc - A)
    have hmajor : Integrable (fun z : Configuration n × Configuration n =>
        δ * Hψ' z) ν := (hLψint.const_mul δ)
    have hpoint (z : Configuration n × Configuration n) :
        ‖Hdiff z‖ ≤ δ * Hψ' z := by
      let q := (piPairHomeomorph n).symm z
      have h := hAerr q
      change ‖(Fcc - A) q‖ ≤ δ * ∏ i, ψ (q i)
      rw [Real.norm_eq_abs]
      change |Fcc q - A q| ≤ δ * ∏ i, ψ (q i)
      rw [hFcc_apply q, abs_sub_comm]
      exact h
    have hnorm := norm_integral_le_of_norm_le hmajor
      (Eventually.of_forall hpoint)
    have hτpos : 0 < τ := by dsimp [τ]; linarith
    have hFformula :
        (∫ z, piPullTestCC Fcc z ∂ν) =
          ∫ x : Configuration n, ∫ y : Configuration n,
            F (fun i => (x i, y i)) * (momentKernel n θ τ x y).toReal := by
      rw [integral_momentKernel_measure_eq_iterated hn4 θ hτpos (piPullTestCC Fcc)]
      apply integral_congr_ae
      filter_upwards [] with x
      apply integral_congr_ae
      filter_upwards [] with y
      rw [piPullTestCC_apply, piPairHomeomorph_symm_pair, hFcc_apply]
    have hAformula :
        (∫ z, piPullTestCC A z ∂ν) =
          ∫ x : Configuration n, ∫ y : Configuration n,
            A (fun i => (x i, y i)) * (momentKernel n θ τ x y).toReal := by
      rw [integral_momentKernel_measure_eq_iterated hn4 θ hτpos (piPullTestCC A)]
      apply integral_congr_ae
      filter_upwards [] with x
      apply integral_congr_ae
      filter_upwards [] with y
      rw [piPullTestCC_apply, piPairHomeomorph_symm_pair]
    have hdiff_formula :
        (∫ z, Hdiff z ∂ν) =
          (∫ x : Configuration n, ∫ y : Configuration n,
            F (fun i => (x i, y i)) * (momentKernel n θ τ x y).toReal) -
          ∫ x : Configuration n, ∫ y : Configuration n,
            A (fun i => (x i, y i)) * (momentKernel n θ τ x y).toReal := by
      have hpullsub : ∫ z, piPullTestCC (Fcc - A) z ∂ν =
          ∫ z, piPullTestCC Fcc z ∂ν - ∫ z, piPullTestCC A z ∂ν := by
        calc
          ∫ z, piPullTestCC (Fcc - A) z ∂ν =
              ∫ z, (piPullTestCC Fcc z - piPullTestCC A z) ∂ν := by
            apply integral_congr_ae
            filter_upwards [] with z
            simp only [piPullTestCC_apply, CompactlySupportedContinuousMap.sub_apply]
          _ = _ := integral_sub
            (integrable_compactTest_of_locallyFinite ν hνloc (piPullTestCC Fcc))
            (integrable_compactTest_of_locallyFinite ν hνloc (piPullTestCC A))
      change (∫ z, piPullTestCC (Fcc - A) z ∂ν) = _
      rw [hpullsub, hFformula, hAformula]
    rw [hdiff_formula, Real.norm_eq_abs] at hnorm
    have hlim : ∫ z, Hψ' z ∂ν = Lψ := by rfl
    rw [integral_const_mul, hlim] at hnorm
    have hLψbound : Lψ ≤ M₁ := by
      dsimp [M₁]
      exact (le_max_left Lψ 0).trans (le_add_of_nonneg_left (by norm_num))
    exact hnorm.trans (mul_le_mul_of_nonneg_left hLψbound hδ.le)
  have hsum_conv := hsum_tendsto
  have hcloseN' := hcloseN
  have hthird : 0 < ε / 3 := by positivity
  have hsumEventually : ∀ᶠ N : ℕ in atTop,
      dist (∫ ω, IA N ω ∂disorderLaw)
        (∫ x : Configuration n, ∫ y : Configuration n,
          A (fun i => (x i, y i)) *
            (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal) < ε / 3 :=
    (hsum_conv.eventually (Metric.ball_mem_nhds _ hthird))
  have hratio₀ : M₀ / (M₀ + M₁) ≤ 1 := by
    rw [div_le_iff₀ (by positivity : 0 < M₀ + M₁)]
    simpa only [one_mul] using le_add_of_nonneg_right hM₁.le
  have hratio₁ : M₁ / (M₀ + M₁) ≤ 1 := by
    rw [div_le_iff₀ (by positivity : 0 < M₀ + M₁)]
    simpa only [one_mul] using le_add_of_nonneg_left hM₀.le
  have hfirst : δ * M₀ ≤ ε / 3 := by
    calc
      δ * M₀ = (ε / 3) * (M₀ / (M₀ + M₁)) := by
        dsimp [δ]
        field_simp
      _ ≤ ε / 3 := by
        have h := mul_le_mul_of_nonneg_left hratio₀ (by positivity : 0 ≤ ε / 3)
        simpa only [mul_one] using h
  have hlast : δ * M₁ ≤ ε / 3 := by
    calc
      δ * M₁ = (ε / 3) * (M₁ / (M₀ + M₁)) := by
        dsimp [δ]
        field_simp
      _ ≤ ε / 3 := by
        have h := mul_le_mul_of_nonneg_left hratio₁ (by positivity : 0 ≤ ε / 3)
        simpa only [mul_one] using h
  have hevent : ∀ᶠ N : ℕ in atTop, dist
      (∫ ω, IF N ω ∂disorderLaw)
      (∫ x : Configuration n, ∫ y : Configuration n,
        F (fun i => (x i, y i)) *
          (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal) < ε := by
    filter_upwards [hcloseN', hsumEventually] with N hN hA
    rw [Real.dist_eq]
    have hAabs :
        |(∫ ω, IA N ω ∂disorderLaw) -
          ∫ x : Configuration n, ∫ y : Configuration n,
            A (fun i => (x i, y i)) *
              (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal| < ε / 3 := by
      simpa only [Real.dist_eq] using hA
    have hcloseSwap :
        |(∫ x : Configuration n, ∫ y : Configuration n,
            A (fun i => (x i, y i)) *
              (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal) -
          ∫ x : Configuration n, ∫ y : Configuration n,
            F (fun i => (x i, y i)) *
              (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal| ≤ δ * M₁ := by
      rw [abs_sub_comm]
      exact hcloseLimit
    have htriangle :
        |(∫ ω, IF N ω ∂disorderLaw) -
          ∫ x : Configuration n, ∫ y : Configuration n,
            F (fun i => (x i, y i)) *
              (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal| ≤
        |(∫ ω, IF N ω ∂disorderLaw) - ∫ ω, IA N ω ∂disorderLaw| +
          (|(∫ ω, IA N ω ∂disorderLaw) -
              ∫ x : Configuration n, ∫ y : Configuration n,
                A (fun i => (x i, y i)) *
                  (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal| +
            |(∫ x : Configuration n, ∫ y : Configuration n,
                A (fun i => (x i, y i)) *
                  (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal) -
              ∫ x : Configuration n, ∫ y : Configuration n,
                F (fun i => (x i, y i)) *
                  (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal|) := by
      have htri₁ := abs_sub_le
        (∫ ω, IF N ω ∂disorderLaw) (∫ ω, IA N ω ∂disorderLaw)
        (∫ x : Configuration n, ∫ y : Configuration n,
          F (fun i => (x i, y i)) *
            (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal)
      have htri₂ := abs_sub_le
        (∫ ω, IA N ω ∂disorderLaw)
        (∫ x : Configuration n, ∫ y : Configuration n,
          A (fun i => (x i, y i)) *
            (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal)
        (∫ x : Configuration n, ∫ y : Configuration n,
          F (fun i => (x i, y i)) *
            (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal)
      exact htri₁.trans (add_le_add le_rfl htri₂)
    have hmiddle :
        |(∫ ω, IA N ω ∂disorderLaw) -
          ∫ x : Configuration n, ∫ y : Configuration n,
            A (fun i => (x i, y i)) *
              (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal| +
          |(∫ x : Configuration n, ∫ y : Configuration n,
              A (fun i => (x i, y i)) *
                (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal) -
            ∫ x : Configuration n, ∫ y : Configuration n,
              F (fun i => (x i, y i)) *
                (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal| <
          ε / 3 + δ * M₁ :=
      add_lt_add_of_lt_of_le hAabs hcloseSwap
    have hstrict :
        |(∫ ω, IF N ω ∂disorderLaw) -
          ∫ x : Configuration n, ∫ y : Configuration n,
            F (fun i => (x i, y i)) *
              (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal| <
          δ * M₀ + (ε / 3 + δ * M₁) :=
      lt_of_le_of_lt htriangle (add_lt_add_of_le_of_lt hN hmiddle)
    calc
      _ < δ * M₀ + (ε / 3 + δ * M₁) := hstrict
      _ ≤ ε / 3 + (ε / 3 + ε / 3) :=
        add_le_add hfirst (add_le_add le_rfl hlast)
      _ = ε := by ring
  exact eventually_atTop.mp hevent

end Critical2DKPZ.SHF.Flow

end
