/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.SubseqDenseInputs
public import Critical2DKPZ.JointConvergence.MomentConvergence
public import Critical2DKPZ.SHF.Moments.WordDominationFlatProduct
public import Critical2DKPZ.SHF.Tsai.CompactTensorTests
public import Critical2DKPZ.SHF.Tsai.MixedBlockJointMoments
public import Critical2DKPZ.SHF.Tsai.PositiveBlockMoments
public import Critical2DKPZ.SHF.Tsai.EndpointMomentIntegration
public import Critical2DKPZ.RandomMeasure.GeneralTests
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosedProd

/-! # Moment formulas for polymer subsequential limits

The formulas extend from compact tensor tests to arbitrary real square-integrable endpoint tests. -/

@[expose] public section

open MeasureTheory Filter
open scoped BoundedContinuousFunction CompactlySupported Topology ENNReal

namespace Critical2DKPZ.SHF.Flow

open Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Tsai
open Critical2DKPZ.DeltaBose
open Critical2DKPZ.SHF.Moments

/-- A compactly supported continuous real test is integrable against a locally finite measure. -/
theorem integrable_compactTest_of_locallyFinite {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [BorelSpace α] [T2Space α] (μ : Measure α)
    (hμ : IsLocallyFiniteMeasure μ) (f : C_c(α, ℝ)) : Integrable (f : α → ℝ) μ := by
  have hK : IsCompact (tsupport (f : α → ℝ)) := f.hasCompactSupport
  have hfinite : IsFiniteMeasureOnCompacts μ :=
    @isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure α _ _ _ hμ
  have hKfinite : μ (tsupport (f : α → ℝ)) < ∞ := hfinite.lt_top_of_isCompact hK
  have hOn := f.continuous.continuousOn.integrableOn_of_subset_isCompact
    hK hK.measurableSet Set.Subset.rfl hKfinite.ne
  exact (integrableOn_iff_integrable_of_support_subset
    (subset_tsupport (f : α → ℝ))).mp hOn

/-- The finite-scale moment limit for compact tensor endpoint tests, obtained by instantiating
`PolymerMomentLimit` with their compact product. -/
theorem polymerSubseqLimit_compactTensor_moment_tendsto (ϑ : ℝ)
    (hPolymerMomentInput : PolymerMomentLimit ϑ) (n : ℕ) (hn1 : 1 ≤ n) (hn4 : n ≤ 4)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (g g' : Fin n → C_c(Plane, ℝ)) :
    Tendsto
      (fun N => ∫ ω, ∏ i, (∫ p, g i p.1 * g' i p.2
        ∂(polymerMeasure ϑ N s t ω)) ∂disorderLaw)
      atTop
      (𝓝 (∫ x : Configuration n, ∫ y : Configuration n,
        (∏ i, g i (x i)) *
          (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal *
            ∏ i, g' i (y i))) := by
  let φ : Fin n → C_c(Plane × Plane, ℝ) := fun i => compactTensorTest (g i) (g' i)
  have h := hPolymerMomentInput n hn1 hn4 hs hst φ
  have hsource :
      (fun N => ∫ ω, ∏ i, (∫ p, g i p.1 * g' i p.2
        ∂(polymerMeasure ϑ N s t ω)) ∂disorderLaw) =
      (fun N => ∫ ω, ∏ i, (∫ p, φ i p ∂(polymerMeasure ϑ N s t ω)) ∂disorderLaw) := by
    funext N
    apply integral_congr_ae
    filter_upwards [] with ω
    apply Finset.prod_congr rfl
    intro i hi
    simp [φ, compactTensorTest]
  have hprod (x : Configuration n) (y : Configuration n) :
      (∏ i, φ i (x i, y i)) *
          (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal =
        (∏ i, g i (x i)) *
          (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal *
            ∏ i, g' i (y i) := by
    simp only [φ, compactTensorTest_apply]
    rw [Finset.prod_mul_distrib]
    ring
  have hlimit :
      (∫ x : Configuration n, ∫ y : Configuration n,
        (∏ i, φ i (x i, y i)) *
          (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal) =
      ∫ x : Configuration n, ∫ y : Configuration n,
        (∏ i, g i (x i)) *
          (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal *
            ∏ i, g' i (y i) := by
    apply integral_congr_ae
    filter_upwards [] with x
    apply integral_congr_ae
    filter_upwards [] with y
    exact hprod x y
  rw [hsource]
  simpa only [hlimit] using h

/-- Joint convergence in a polymer subsequential limit transfers to products of compact
endpoint tensor pairings. -/
theorem polymerSubseqLimit_compactTensor_product_tendstoInDistribution
    (ϑ : ℝ) (D : Set ℝ) (ψ : ℕ → ℕ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsPolymerSubseqLimit ϑ D ψ P Z)
    (n : ℕ) {s t : ℝ} (hsD : s ∈ D) (htD : t ∈ D) (hst : s < t)
    (g g' : Fin n → C_c(Plane, ℝ)) :
    TendstoInDistribution
      (fun m (ω : Disorder) => ∏ i, ∫ p, g i p.1 * g' i p.2
        ∂polymerMeasure ϑ (ψ m) s t ω)
      atTop
      (fun ω => ∏ i, ∫ p, g i p.1 * g' i p.2 ∂Z s t ω)
      (fun _ => disorderLaw) P := by
  let φ : Fin n → C_c(Plane × Plane, ℝ) := fun i => compactTensorTest (g i) (g' i)
  let H : (Fin n → ℝ × ℝ) → ℝ := fun v => ∏ i, (v i).1
  have hH : Continuous H := by fun_prop
  have hdist := hZ.2 n (fun _ => s) (fun _ => t)
    (fun _ => ⟨hsD, htD, hst⟩) φ (fun _ => 0)
  have hcomp := hdist.continuous_comp hH
  simpa [Function.comp_def, H, φ, compactTensorTest] using hcomp

/-- A uniform sixth-moment bound controls a moment strictly above one for products of up to four compact tensor pairings. -/
theorem eventually_compactTensor_product_rpow_bound (ϑ : ℝ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
    (n : ℕ) (hn1 : 1 ≤ n) (hn4 : n ≤ 4) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t)
    (g g' : Fin n → C_c(Plane, ℝ)) :
    ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω => |∏ i, ∫ p, g i p.1 * g' i p.2
        ∂polymerMeasure ϑ N s t ω| ^ (6 / (n : ℝ))) disorderLaw ∧
      ∫ ω, |∏ i, ∫ p, g i p.1 * g' i p.2
        ∂polymerMeasure ϑ N s t ω| ^ (6 / (n : ℝ)) ∂disorderLaw ≤ C := by
  let φ : Fin n → C_c(Plane × Plane, ℝ) := fun i => compactTensorTest (g i) (g' i)
  let Φ : C_c(Plane × Plane, ℝ) := ∑ i, compactAbs (φ i)
  have hΦnonneg (p : Plane × Plane) : 0 ≤ Φ p := by
    dsimp only [Φ]
    rw [CompactlySupportedContinuousMap.sum_apply]
    exact Finset.sum_nonneg fun i hi => by
      change 0 ≤ |φ i p|
      positivity
  obtain ⟨M, χ, hM, hχ, hmajor⟩ := exists_pairTest_firstCoordinate_majorant Φ
  obtain ⟨C₆, hC₆⟩ := hFlatSixthMomentInput χ (τ := (t - s) / 2) (T := t) (by linarith)
  let q : ℝ := 6 / (n : ℝ)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < n))
  have hq : 1 < q := by
    dsimp [q]
    rw [one_lt_div (by positivity : 0 < (n : ℝ))]
    exact_mod_cast (by omega : n < 6)
  have hnq : (n : ℝ) * q = 6 := by
    dsimp [q]
    field_simp [hn0]
  let Y : ℕ → Disorder → ℝ := fun N ω =>
    ∫ x, χ x ∂((polymerMeasure ϑ N s t ω).map Prod.fst)
  let X : ℕ → Fin n → Disorder → ℝ := fun N i ω =>
    ∫ p, φ i p ∂polymerMeasure ϑ N s t ω
  have hYnonneg (N : ℕ) (ω : Disorder) : 0 ≤ Y N ω :=
    integral_nonneg fun x => hχ x
  have hterm (i : Fin n) (p : Plane × Plane) : |φ i p| ≤ M * χ p.1 := by
    have hle : compactAbs (φ i) p ≤ Φ p := by
      dsimp only [Φ]
      rw [CompactlySupportedContinuousMap.sum_apply]
      exact Finset.single_le_sum
        (fun j hj => show 0 ≤ compactAbs (φ j) p by change 0 ≤ |φ j p|; positivity)
        (Finset.mem_univ i)
    calc
      |φ i p| = compactAbs (φ i) p := rfl
      _ ≤ Φ p := hle
      _ = |Φ p| := (abs_of_nonneg (hΦnonneg p)).symm
      _ ≤ M * χ p.1 := hmajor p
  have hXle (N : ℕ) (i : Fin n) (ω : Disorder) : |X N i ω| ≤ M * Y N ω := by
    have hvol := abs_integral_pairTest_rescaledP2P_le_marginal
      ϑ N s t ω (φ i) χ M (hterm i)
    have hμ : X N i ω =
        ∫ p, φ i p * rescaledP2P ϑ N s t p ω ∂volume := by
      dsimp [X]
      simpa only [φ] using integral_polymerMeasure ϑ N s t ω (φ i)
    rw [hμ]
    simpa only [Y] using hvol
  have hFlatSixthMomentInputEvent : ∀ᶠ N : ℕ in atTop,
      ∀ s' t' : ℝ, 0 ≤ s' → (t - s) / 2 ≤ t' - s' → t' ≤ t →
        Integrable (fun ω => (∫ x, |χ x| ∂((polymerMeasure ϑ N s' t' ω).map Prod.fst)) ^ 6)
          disorderLaw ∧
        ∫ ω, (∫ x, |χ x| ∂((polymerMeasure ϑ N s' t' ω).map Prod.fst)) ^ 6
          ∂disorderLaw ≤ C₆ := hC₆
  have hNspec := hFlatSixthMomentInputEvent.mono fun N hN => hN s t hs (by linarith) le_rfl
  refine ⟨M ^ 6 * max C₆ 0, ?_⟩
  filter_upwards [hNspec] with N hN
  let YN : Disorder → ℝ := Y N
  have hYeq : (fun ω => (∫ x, |χ x| ∂
      ((polymerMeasure ϑ N s t ω).map Prod.fst)) ^ 6) = fun ω => YN ω ^ 6 := by
    funext ω
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => abs_of_nonneg (hχ x)
  have hY6int : Integrable (fun ω => YN ω ^ 6) disorderLaw := by
    rw [← hYeq]
    exact hN.1
  have hY6bound : ∫ ω, YN ω ^ 6 ∂disorderLaw ≤ max C₆ 0 := by
    have hle : ∫ ω, YN ω ^ 6 ∂disorderLaw ≤ C₆ := by
      calc
        ∫ ω, YN ω ^ 6 ∂disorderLaw =
            ∫ ω, (∫ x, |χ x| ∂
              ((polymerMeasure ϑ N s t ω).map Prod.fst)) ^ 6 ∂disorderLaw := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun ω => (congrFun hYeq ω).symm
        _ ≤ C₆ := hN.2
    exact hle.trans (le_max_left _ _)
  let XN : Disorder → ℝ := fun ω => ∏ i, X N i ω
  have hXiInt (i : Fin n) : Integrable (X N i) disorderLaw := by
    let G : (Plane × Plane) × Disorder → ℝ :=
      fun q => φ i q.1 * rescaledP2P ϑ N s t q.1 q.2
    have hG : Integrable G (volume.prod disorderLaw) :=
      integrable_pairing_rescaledP2P ϑ N s t (φ i).continuous_toFun (φ i).hasCompactSupport'
    have hGswap : Integrable (fun q : Disorder × (Plane × Plane) => G (q.2, q.1))
        (disorderLaw.prod volume) := hG.swap
    have htemp : Integrable (fun ω : Disorder =>
        ∫ p, G (p, ω) ∂volume) disorderLaw := by
      simpa only [G, Prod.fst, Prod.snd] using hGswap.integral_prod_left
    apply htemp.congr
    exact Filter.Eventually.of_forall fun ω =>
      by simpa only [G] using (integral_polymerMeasure ϑ N s t ω (φ i)).symm
  have hXNsm : AEStronglyMeasurable XN disorderLaw := by
    have hpair : ∀ i : Fin n, AEStronglyMeasurable (X N i) disorderLaw := by
      intro i
      exact (hXiInt i).aestronglyMeasurable
    simpa only [XN] using Finset.aestronglyMeasurable_fun_prod Finset.univ
      (fun i hi => hpair i)
  have hpoint (ω : Disorder) : |XN ω| ^ q ≤ M ^ 6 * YN ω ^ 6 := by
    have habsprod : |XN ω| = ∏ i, |X N i ω| := by
      dsimp [XN]
      simpa only [Real.norm_eq_abs] using (norm_prod Finset.univ fun i => X N i ω)
    have hprod : |XN ω| ≤ (M * YN ω) ^ n := by
      rw [habsprod]
      calc
        ∏ i, |X N i ω| ≤ ∏ i : Fin n, M * YN ω :=
          Finset.prod_le_prod₀ (fun i hi => abs_nonneg _) (fun i hi => hXle N i ω)
        _ = (M * YN ω) ^ n := by simp
    have hbase : 0 ≤ M * YN ω := mul_nonneg hM (hYnonneg N ω)
    have hqpos : 0 < q := lt_trans zero_lt_one hq
    calc
      |XN ω| ^ q ≤ ((M * YN ω) ^ n) ^ q := Real.rpow_le_rpow (abs_nonneg _) hprod hqpos.le
      _ = (M * YN ω) ^ 6 := by
        calc
          ((M * YN ω) ^ n) ^ q = ((M * YN ω) ^ (n : ℝ)) ^ q := by
            rw [← Real.rpow_natCast]
          _ = (M * YN ω) ^ ((n : ℝ) * q) :=
            (Real.rpow_mul hbase (n : ℝ) q).symm
          _ = (M * YN ω) ^ (6 : ℝ) :=
            congrArg (fun r : ℝ => (M * YN ω) ^ r) hnq
          _ = (M * YN ω) ^ 6 := Real.rpow_natCast _ 6
      _ = M ^ 6 * YN ω ^ 6 := mul_pow M (YN ω) 6
  have hmajorInt : Integrable (fun ω => M ^ 6 * YN ω ^ 6) disorderLaw :=
    hY6int.const_mul (M ^ 6)
  have hXqInt : Integrable (fun ω => |XN ω| ^ q) disorderLaw := by
    have hqcont : Continuous fun z : ℝ => |z| ^ q :=
      (Real.continuous_rpow_const (le_trans zero_le_one hq.le)).comp continuous_abs
    apply hmajorInt.mono' (hqcont.comp_aestronglyMeasurable hXNsm)
    filter_upwards [] with ω
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) q)]
    exact hpoint ω
  have hXqbound : ∫ ω, |XN ω| ^ q ∂disorderLaw ≤ M ^ 6 * max C₆ 0 := by
    calc
      ∫ ω, |XN ω| ^ q ∂disorderLaw ≤ ∫ ω, M ^ 6 * YN ω ^ 6 ∂disorderLaw :=
        integral_mono hXqInt hmajorInt hpoint
      _ = M ^ 6 * ∫ ω, YN ω ^ 6 ∂disorderLaw := by rw [integral_const_mul]
      _ ≤ M ^ 6 * max C₆ 0 := mul_le_mul_of_nonneg_left hY6bound (pow_nonneg hM 6)
  exact ⟨hXqInt, hXqbound⟩

/-- Compact tensor endpoint moments pass to polymer subsequential limits. -/
theorem polymerSubseqLimit_compactTensor_moment_formula_of (ϑ : ℝ)
    (hPolymerMomentInput : PolymerMomentLimit ϑ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
    (D : Set ℝ) (_hD : D.Countable) (hD0 : ∀ s ∈ D, 0 ≤ s) (ψ : ℕ → ℕ)
    (hψ : StrictMono ψ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsPolymerSubseqLimit ϑ D ψ P Z)
    (n : ℕ) (hn1 : 1 ≤ n) (hn4 : n ≤ 4) {s t : ℝ}
    (hsD : s ∈ D) (htD : t ∈ D) (hst : s < t)
    (g g' : Fin n → C_c(Plane, ℝ)) :
    (∀ᵐ ω ∂P, ∀ i, Integrable (fun p : Plane × Plane => g i p.1 * g' i p.2) (Z s t ω)) ∧
    Integrable (fun ω => ∏ i, ∫ p, g i p.1 * g' i p.2 ∂Z s t ω) P ∧
    ∫ ω, ∏ i, (∫ p, g i p.1 * g' i p.2 ∂Z s t ω) ∂P =
      ∫ x : Configuration n, ∫ y : Configuration n,
        (∏ i, g i (x i)) *
          (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal *
            ∏ i, g' i (y i) := by
  let q : ℝ := 6 / (n : ℝ)
  have hq : 1 < q := by
    dsimp [q]
    rw [one_lt_div (by positivity : 0 < (n : ℝ))]
    exact_mod_cast (by omega : n < 6)
  let Y : Ω → ℝ := fun ω =>
    ∏ i, ∫ p, g i p.1 * g' i p.2 ∂Z s t ω
  have hdist := polymerSubseqLimit_compactTensor_product_tendstoInDistribution
    ϑ D ψ P Z hZ n hsD htD hst g g'
  obtain ⟨C, hC⟩ := eventually_compactTensor_product_rpow_bound
    ϑ hFlatSixthMomentInput n hn1 hn4 (s := s) (t := t) (hD0 s hsD) hst g g'
  have hCψ := hψ.tendsto_atTop.eventually hC
  have hYq := JointConvergence.integrable_rpow_limit_of_tendstoInDistribution
    hdist (lt_trans zero_lt_one hq)
    (hCψ.mono fun m hm => hm.1) (hCψ.mono fun m hm => hm.2)
  have hYsm : AEStronglyMeasurable Y P := hdist.aemeasurable_limit.aestronglyMeasurable
  have hYabsInt : Integrable (fun ω => ‖Y ω‖) P := by
    have hYqNorm : Integrable (fun ω => ‖Y ω‖ ^ q) P := by
      simpa only [Real.norm_eq_abs] using hYq.1
    have h := integrable_norm_rpow_of_le hYsm (p := 1) (q := q)
      (by norm_num) (le_of_lt (lt_trans zero_lt_one hq)) hq.le hYqNorm
    simpa only [Real.norm_eq_abs, abs_abs, Real.rpow_one] using h
  have hYint : Integrable Y P := (integrable_norm_iff hYsm).mp hYabsInt
  have hmean := JointConvergence.tendsto_integral_of_tendstoInDistribution
    hdist hq (hCψ.mono fun m hm => hm.2) (hCψ.mono fun m hm => hm.1)
  have hfinite := polymerSubseqLimit_compactTensor_moment_tendsto
    ϑ hPolymerMomentInput n hn1 hn4 (hD0 s hsD) hst g g'
  have hfiniteψ := hfinite.comp hψ.tendsto_atTop
  have hmoment : ∫ ω, Y ω ∂P =
      ∫ x : Configuration n, ∫ y : Configuration n,
        (∏ i, g i (x i)) *
          (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal *
            ∏ i, g' i (y i) := tendsto_nhds_unique hmean hfiniteψ
  have hinner : ∀ᵐ ω ∂P, ∀ i,
      Integrable (fun p : Plane × Plane => g i p.1 * g' i p.2) (Z s t ω) := by
    filter_upwards [(hZ.1 s hsD t htD hst).2] with ω hω
    intro i
    change Integrable (compactTensorTest (g i) (g' i) : Plane × Plane → ℝ) (Z s t ω)
    exact integrable_compactTest_of_locallyFinite (Z s t ω) hω.1
      (compactTensorTest (g i) (g' i))
  exact ⟨hinner, hYint, hmoment⟩




private def configurationCompactExhaustion (n : ℕ)
    (K : CompactExhaustion Plane) : CompactExhaustion (Fin n → Plane) where
  toFun m := Set.univ.pi (fun _ : Fin n => K m)
  isCompact' m := isCompact_univ_pi (fun _ => K.isCompact m)
  subset_interior_succ' m := by
    rw [interior_pi_set Set.finite_univ]
    intro x hx i hi
    exact K.subset_interior_succ m (hx i hi)
  iUnion_eq' := by
    ext x
    constructor
    · intro _
      exact Set.mem_univ x
    · intro _
      have hrange : IsCompact (Set.range x) := (Set.finite_range x).isCompact
      obtain ⟨m, hm⟩ := K.exists_superset_of_isCompact hrange
      refine Set.mem_iUnion.2 ⟨m, ?_⟩
      intro i _
      exact hm ⟨i, rfl⟩

/-- The compact positive tensor cutoffs have finite mass under the expected replica
measure. This gives the local finiteness needed to identify that measure. -/
private theorem polymerSubseqLimit_tupleCutoff_lintegral_lt_top (ϑ : ℝ)
    (hPolymerMomentInput : PolymerMomentLimit ϑ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
    (D : Set ℝ) (hD : D.Countable) (hD0 : ∀ s ∈ D, 0 ≤ s) (ψ : ℕ → ℕ)
    (hψ : StrictMono ψ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsPolymerSubseqLimit ϑ D ψ P Z)
    {s t : ℝ} (hsD : s ∈ D) (htD : t ∈ D) (hst : s < t)
    (n : ℕ) (hn1 : 1 ≤ n) (hn4 : n ≤ 4) (m : ℕ) :
    ∫⁻ q : Configuration n × Configuration n,
      (∏ i, ENNReal.ofReal (RandomMeasure.vagueMassTest
        (RandomMeasure.vagueCompactExhaustion Plane) m (q.1 i))) *
        ∏ i, ENNReal.ofReal (RandomMeasure.vagueMassTest
          (RandomMeasure.vagueCompactExhaustion Plane) m (q.2 i))
      ∂P.bind (fun ω => blockTupleMeasure n
        (RandomMeasure.locallyFiniteMeasureModification
          (RandomMeasure.vagueCompactExhaustion (Plane × Plane)) (Z s t) ω)) < ⊤ := by
  let K := RandomMeasure.vagueCompactExhaustion Plane
  let E := RandomMeasure.vagueCompactExhaustion (Plane × Plane)
  let B : Ω → Measure (Plane × Plane) :=
    RandomMeasure.locallyFiniteMeasureModification E (Z s t)
  let χ : C_c(Plane, ℝ) := RandomMeasure.vagueMassTest K m
  let Y : Ω → ℝ := fun ω =>
    ∏ i : Fin n, ∫ p : Plane × Plane, χ p.1 * χ p.2 ∂B ω
  have hBmeas : Measurable B := by
    exact RandomMeasure.measurable_locallyFiniteMeasureModification E (Z s t)
      ((hZ.1 s hsD t htD hst).1)
  have hBlf (ω : Ω) : IsLocallyFiniteMeasure (B ω) := by
    exact RandomMeasure.locallyFinite_locallyFiniteMeasureModification E (Z s t) ω
  have hBae : B =ᵐ[P] Z s t := by
    filter_upwards [(hZ.1 s hsD t htD hst).2] with ω hω
    change RandomMeasure.locallyFiniteMeasureModification E (Z s t) ω = Z s t ω
    exact RandomMeasure.locallyFiniteMeasureModification_apply_of_isLocallyFinite
      E (Z s t) ω hω.1
  have hcompact := polymerSubseqLimit_compactTensor_moment_formula_of
    ϑ hPolymerMomentInput hFlatSixthMomentInput D hD hD0 ψ hψ P Z hZ n hn1 hn4 hsD htD hst (fun _ => χ) (fun _ => χ)
  have hYeq : (fun ω => ∏ i : Fin n,
      ∫ p : Plane × Plane, χ p.1 * χ p.2 ∂Z s t ω) =ᵐ[P] Y := by
    filter_upwards [hBae] with ω hω
    change (∏ i : Fin n, ∫ p : Plane × Plane,
      χ p.1 * χ p.2 ∂Z s t ω) =
        ∏ i : Fin n, ∫ p : Plane × Plane, χ p.1 * χ p.2 ∂B ω
    apply Finset.prod_congr rfl
    intro i hi
    rw [hω]
  have hYint : Integrable Y P := hcompact.2.1.congr hYeq
  have hYnonneg (ω : Ω) : 0 ≤ Y ω := by
    apply Finset.prod_nonneg
    intro i hi
    apply integral_nonneg
    intro p
    exact mul_nonneg ((RandomMeasure.vagueMassTest_spec K m).1 p.1)
      ((RandomMeasure.vagueMassTest_spec K m).1 p.2)
  have hYof :
      (∫⁻ ω, ENNReal.ofReal (Y ω) ∂P) =
        ENNReal.ofReal (∫ ω, Y ω ∂P) :=
    (ofReal_integral_eq_lintegral_ofReal hYint
      (Filter.Eventually.of_forall hYnonneg)).symm
  have htupleMeas : Measurable (fun ω => blockTupleMeasure n (B ω)) :=
    measurable_blockTupleMeasure n B hBmeas hBlf
  have hHmeas : Measurable (fun q : Configuration n × Configuration n =>
      (∏ i, ENNReal.ofReal (χ (q.1 i))) * ∏ i, ENNReal.ofReal (χ (q.2 i))) := by
    exact (Finset.measurable_prod _ fun i _ =>
      (χ.continuous.measurable.comp
        ((measurable_pi_apply i).comp measurable_fst)).ennreal_ofReal).mul
      (Finset.measurable_prod _ fun i _ =>
        (χ.continuous.measurable.comp
          ((measurable_pi_apply i).comp measurable_snd)).ennreal_ofReal)
  have hbind :
      (∫⁻ q : Configuration n × Configuration n,
        (∏ i, ENNReal.ofReal (χ (q.1 i))) * ∏ i, ENNReal.ofReal (χ (q.2 i))
        ∂P.bind (fun ω => blockTupleMeasure n (B ω))) =
      ∫⁻ ω, ∫⁻ q : Configuration n × Configuration n,
        (∏ i, ENNReal.ofReal (χ (q.1 i))) * ∏ i, ENNReal.ofReal (χ (q.2 i))
          ∂blockTupleMeasure n (B ω) ∂P :=
    Measure.lintegral_bind htupleMeas.aemeasurable hHmeas.aemeasurable
  have hfiber (ω : Ω) :
      (∫⁻ q : Configuration n × Configuration n,
        (∏ i, ENNReal.ofReal (χ (q.1 i))) * ∏ i, ENNReal.ofReal (χ (q.2 i))
        ∂blockTupleMeasure n (B ω)) = ENNReal.ofReal (Y ω) := by
    have hSigma : SigmaFinite (B ω) :=
      @MeasureTheory.sigmaFinite_of_locallyFinite (Plane × Plane) _ (B ω)
        inferInstance inferInstance (hBlf ω)
    have hSigmas : ∀ i : Fin n, SigmaFinite (B ω) := fun _ => hSigma
    have hfactor := @lintegral_endpointTupleMeasure_tensor n (fun _ : Fin n => B ω) hSigmas
      (fun _ x => ENNReal.ofReal (χ x)) (fun _ y => ENNReal.ofReal (χ y))
      (fun _ => χ.continuous.measurable.ennreal_ofReal)
      (fun _ => χ.continuous.measurable.ennreal_ofReal)
    change (∫⁻ q, (∏ i, ENNReal.ofReal (χ (q.1 i))) *
      ∏ i, ENNReal.ofReal (χ (q.2 i)) ∂endpointTupleMeasure (fun _ : Fin n => B ω)) = _
    rw [hfactor]
    have hpair (i : Fin n) :
        (∫⁻ p : Plane × Plane,
          ENNReal.ofReal (χ p.1) * ENNReal.ofReal (χ p.2) ∂B ω) =
          ENNReal.ofReal (∫ p : Plane × Plane, χ p.1 * χ p.2 ∂B ω) := by
      have hI := integrable_compactTest_of_locallyFinite (B ω) (hBlf ω)
        (compactTensorTest χ χ)
      have hnonneg : ∀ p : Plane × Plane, 0 ≤ χ p.1 * χ p.2 :=
        fun p => mul_nonneg ((RandomMeasure.vagueMassTest_spec K m).1 p.1)
          ((RandomMeasure.vagueMassTest_spec K m).1 p.2)
      calc
        _ = ∫⁻ p : Plane × Plane, ENNReal.ofReal (χ p.1 * χ p.2) ∂B ω := by
          apply lintegral_congr_ae
          exact Filter.Eventually.of_forall fun p => by
            exact (ENNReal.ofReal_mul
              ((RandomMeasure.vagueMassTest_spec K m).1 p.1)).symm
        _ = _ := (ofReal_integral_eq_lintegral_ofReal hI
          (Filter.Eventually.of_forall hnonneg)).symm
    calc
      (∏ i : Fin n, ∫⁻ p : Plane × Plane,
        ENNReal.ofReal (χ p.1) * ENNReal.ofReal (χ p.2) ∂B ω) =
          ∏ i : Fin n, ENNReal.ofReal (∫ p : Plane × Plane,
            χ p.1 * χ p.2 ∂B ω) := by
              apply Finset.prod_congr rfl
              intro i hi
              exact hpair i
      _ = ENNReal.ofReal (Y ω) := by
        change (∏ i : Fin n, ENNReal.ofReal
          (∫ p : Plane × Plane, χ p.1 * χ p.2 ∂B ω)) =
            ENNReal.ofReal (∏ i : Fin n, ∫ p : Plane × Plane,
              χ p.1 * χ p.2 ∂B ω)
        exact (ENNReal.ofReal_prod_of_nonneg (s := Finset.univ)
          (f := fun i : Fin n => ∫ p : Plane × Plane, χ p.1 * χ p.2 ∂B ω)
          (by
            intro i hi
            apply integral_nonneg
            intro p
            exact mul_nonneg ((RandomMeasure.vagueMassTest_spec K m).1 p.1)
              ((RandomMeasure.vagueMassTest_spec K m).1 p.2))).symm
  have hlin :
      (∫⁻ q : Configuration n × Configuration n,
        (∏ i, ENNReal.ofReal (χ (q.1 i))) * ∏ i, ENNReal.ofReal (χ (q.2 i))
        ∂P.bind (fun ω => blockTupleMeasure n (B ω))) =
        ENNReal.ofReal (∫ ω, Y ω ∂P) := by
    rw [hbind]
    calc
      (∫⁻ ω, ∫⁻ q : Configuration n × Configuration n,
          (∏ i, ENNReal.ofReal (χ (q.1 i))) * ∏ i, ENNReal.ofReal (χ (q.2 i))
          ∂blockTupleMeasure n (B ω) ∂P) = ∫⁻ ω, ENNReal.ofReal (Y ω) ∂P := by
            apply lintegral_congr_ae
            exact Filter.Eventually.of_forall hfiber
      _ = ENNReal.ofReal (∫ ω, Y ω ∂P) := hYof
  have hlt :
      (∫⁻ q : Configuration n × Configuration n,
        (∏ i, ENNReal.ofReal (χ (q.1 i))) * ∏ i, ENNReal.ofReal (χ (q.2 i))
        ∂P.bind (fun ω => blockTupleMeasure n (B ω))) < ⊤ := by
    rw [hlin]
    exact ENNReal.ofReal_lt_top
  simpa [B, χ, K, E] using hlt

/-- The expected replica tuple measure agrees with the delta-Bose kernel measure.  The
identification is first made after compact cutoffs, where both measures are finite, and then
the cutoffs exhaust the configuration space. -/
private theorem polymerSubseqLimit_expectedTupleMeasure_eq_kernel (ϑ : ℝ)
    (hPolymerMomentInput : PolymerMomentLimit ϑ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
    (D : Set ℝ) (hD : D.Countable) (hD0 : ∀ s ∈ D, 0 ≤ s) (ψ : ℕ → ℕ)
    (hψ : StrictMono ψ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsPolymerSubseqLimit ϑ D ψ P Z)
    {s t : ℝ} (hsD : s ∈ D) (htD : t ∈ D) (hst : s < t)
    (n : ℕ) (hn1 : 1 ≤ n) (hn4 : n ≤ 4) :
    P.bind (fun ω => blockTupleMeasure n
        (RandomMeasure.locallyFiniteMeasureModification
          (RandomMeasure.vagueCompactExhaustion (Plane × Plane)) (Z s t) ω)) =
      volume.withDensity (Function.uncurry
        (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s))) := by
  classical
  let K : CompactExhaustion Plane := RandomMeasure.vagueCompactExhaustion Plane
  let E : CompactExhaustion (Plane × Plane) :=
    RandomMeasure.vagueCompactExhaustion (Plane × Plane)
  let B : Ω → Measure (Plane × Plane) :=
    RandomMeasure.locallyFiniteMeasureModification E (Z s t)
  let ν : Measure (Configuration n × Configuration n) :=
    P.bind (fun ω => blockTupleMeasure n (B ω))
  let κ : Measure (Configuration n × Configuration n) :=
    volume.withDensity (Function.uncurry
      (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s)))
  have hBmeas : Measurable B :=
    RandomMeasure.measurable_locallyFiniteMeasureModification E (Z s t)
      ((hZ.1 s hsD t htD hst).1)
  have hBlf (ω : Ω) : IsLocallyFiniteMeasure (B ω) :=
    RandomMeasure.locallyFinite_locallyFiniteMeasureModification E (Z s t) ω
  have hBae : B =ᵐ[P] Z s t := by
    filter_upwards [(hZ.1 s hsD t htD hst).2] with ω hω
    change RandomMeasure.locallyFiniteMeasureModification E (Z s t) ω = Z s t ω
    exact RandomMeasure.locallyFiniteMeasureModification_apply_of_isLocallyFinite
      E (Z s t) ω hω.1
  have htupleMeas : Measurable (fun ω => blockTupleMeasure n (B ω)) :=
    measurable_blockTupleMeasure n B hBmeas hBlf
  have hkernel : Measurable (Function.uncurry
      (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s))) :=
    Measurable.comp
      (g := fun p : (ℝ × ℝ) × Configuration n × Configuration n =>
        momentKernel n p.1.1 p.1.2 p.2.1 p.2.2)
      (f := fun q : Configuration n × Configuration n =>
        ((ϑ - Real.eulerMascheroniConstant, t - s), q))
      (measurable_momentKernel n) (measurable_const.prodMk measurable_id)
  have hKχ (m : ℕ) :
      ∀ (f g : Fin n → BoundedContinuousFunction Plane NNReal),
        (∫⁻ q, (∏ i, (f i) (q.1 i) : NNReal) * ∏ i, (g i) (q.2 i)
          ∂(ν.withDensity fun q =>
            (∏ i, ENNReal.ofReal (RandomMeasure.vagueMassTest K m (q.1 i))) *
              ∏ i, ENNReal.ofReal (RandomMeasure.vagueMassTest K m (q.2 i)))) =
        (∫⁻ q, (∏ i, (f i) (q.1 i) : NNReal) * ∏ i, (g i) (q.2 i)
          ∂(κ.withDensity fun q =>
            (∏ i, ENNReal.ofReal (RandomMeasure.vagueMassTest K m (q.1 i))) *
              ∏ i, ENNReal.ofReal (RandomMeasure.vagueMassTest K m (q.2 i)))) := by
    intro f g
    let χ : C_c(Plane, ℝ) := RandomMeasure.vagueMassTest K m
    let realNN : C(NNReal, ℝ) := ⟨fun x => (x : ℝ), NNReal.continuous_coe⟩
    let fC : Fin n → C_c(Plane, ℝ) := fun i => realNN.comp (f i).toContinuousMap • χ
    let gC : Fin n → C_c(Plane, ℝ) := fun i => realNN.comp (g i).toContinuousMap • χ
    have hfC (i : Fin n) (x : Plane) : fC i x = (f i x : ℝ) * χ x := rfl
    have hgC (i : Fin n) (x : Plane) : gC i x = (g i x : ℝ) * χ x := rfl
    have hfC0 (i : Fin n) (x : Plane) : 0 ≤ fC i x := by
      rw [hfC]
      exact mul_nonneg (NNReal.coe_nonneg _) ((RandomMeasure.vagueMassTest_spec K m).1 x)
    have hgC0 (i : Fin n) (x : Plane) : 0 ≤ gC i x := by
      rw [hgC]
      exact mul_nonneg (NNReal.coe_nonneg _) ((RandomMeasure.vagueMassTest_spec K m).1 x)
    have hcompact := polymerSubseqLimit_compactTensor_moment_formula_of
      ϑ hPolymerMomentInput hFlatSixthMomentInput D hD hD0 ψ hψ P Z hZ n hn1 hn4 hsD htD hst fC gC
    have hpairEq :
        (fun ω => ∏ i : Fin n, ∫ p : Plane × Plane,
          fC i p.1 * gC i p.2 ∂Z s t ω) =ᵐ[P]
        fun ω => ∏ i : Fin n, ∫ p : Plane × Plane,
          fC i p.1 * gC i p.2 ∂B ω := by
      filter_upwards [hBae] with ω hω
      apply Finset.prod_congr rfl
      intro i hi
      rw [hω]
    have hinnerB : ∀ᵐ ω ∂P, ∀ i : Fin n,
        Integrable (fun p : Plane × Plane => fC i p.1 * gC i p.2) (B ω) := by
      filter_upwards [hcompact.1, hBae] with ω hω hωB
      intro i
      rw [hωB]
      exact hω i
    have houterB : Integrable (fun ω => ∏ i : Fin n,
        ∫ p : Plane × Plane, fC i p.1 * gC i p.2 ∂B ω) P :=
      hcompact.2.1.congr hpairEq
    have hmomentB :
        (∫ ω, ∏ i : Fin n, ∫ p : Plane × Plane,
          fC i p.1 * gC i p.2 ∂B ω ∂P) =
        ∫ x : Configuration n, ∫ y : Configuration n,
          (∏ i, fC i (x i)) *
            (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal *
              ∏ i, gC i (y i) :=
      (integral_congr_ae hpairEq).symm.trans hcompact.2.2
    let W : Configuration n × Configuration n → ℝ≥0∞ := fun q =>
      (∏ i, ENNReal.ofReal (χ (q.1 i))) * ∏ i, ENNReal.ofReal (χ (q.2 i))
    let H : Configuration n × Configuration n → ℝ≥0∞ := fun q =>
      (∏ i, (f i) (q.1 i) : NNReal) * ∏ i, (g i) (q.2 i)
    have hWmeas : Measurable W := by fun_prop
    have hHmeas : Measurable H := by fun_prop
    have hfENN (i : Fin n) (x : Plane) :
        ENNReal.ofReal (fC i x) =
          ENNReal.ofReal (χ x) * (f i x : ℝ≥0∞) := by
      rw [hfC, ENNReal.ofReal_mul (NNReal.coe_nonneg (f i x))]
      simp only [ENNReal.ofReal_coe_nnreal, mul_comm]
    have hgENN (i : Fin n) (x : Plane) :
        ENNReal.ofReal (gC i x) =
          ENNReal.ofReal (χ x) * (g i x : ℝ≥0∞) := by
      rw [hgC, ENNReal.ofReal_mul (NNReal.coe_nonneg (g i x))]
      simp only [ENNReal.ofReal_coe_nnreal, mul_comm]
    have hfprod (x : Configuration n) :
        (∏ i, ENNReal.ofReal (χ (x i))) * ∏ i, (f i) (x i) =
          ∏ i, ENNReal.ofReal (fC i (x i)) := by
      simp only [ENNReal.ofNNReal_finsetProd]
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      exact (hfENN i (x i)).symm
    have hgprod (x : Configuration n) :
        (∏ i, ENNReal.ofReal (χ (x i))) * ∏ i, (g i) (x i) =
          ∏ i, ENNReal.ofReal (gC i (x i)) := by
      simp only [ENNReal.ofNNReal_finsetProd]
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      exact (hgENN i (x i)).symm
    have hWtimesH (q : Configuration n × Configuration n) :
        W q * H q =
          (∏ i, ENNReal.ofReal (fC i (q.1 i))) *
            ∏ i, ENNReal.ofReal (gC i (q.2 i)) := by
      dsimp only [W, H]
      calc
        ((∏ i, ENNReal.ofReal (χ (q.1 i))) *
            ∏ i, ENNReal.ofReal (χ (q.2 i))) *
          (((∏ i, (f i) (q.1 i) : NNReal) : ℝ≥0∞) *
            ((∏ i, (g i) (q.2 i) : NNReal) : ℝ≥0∞)) =
            ((∏ i, ENNReal.ofReal (χ (q.1 i))) * ∏ i, (f i) (q.1 i)) *
              ((∏ i, ENNReal.ofReal (χ (q.2 i))) * ∏ i, (g i) (q.2 i)) := by ac_rfl
        _ = _ := by rw [hfprod, hgprod]
    have htupleTest (ω : Ω) :
        (∫⁻ q : Configuration n × Configuration n, W q * H q
          ∂blockTupleMeasure n (B ω)) =
        ∏ i : Fin n, ∫⁻ p : Plane × Plane,
          ENNReal.ofReal (fC i p.1) * ENNReal.ofReal (gC i p.2) ∂B ω := by
      simp_rw [hWtimesH]
      have hSigma : SigmaFinite (B ω) :=
        @MeasureTheory.sigmaFinite_of_locallyFinite (Plane × Plane) _ (B ω)
          inferInstance inferInstance (hBlf ω)
      have hSigmas : ∀ i : Fin n, SigmaFinite (B ω) := fun _ => hSigma
      have hfactor := @lintegral_endpointTupleMeasure_tensor n (fun _ : Fin n => B ω) hSigmas
        (fun i x => ENNReal.ofReal (fC i x)) (fun i y => ENNReal.ofReal (gC i y))
        (fun i => (fC i).continuous.measurable.ennreal_ofReal)
        (fun i => (gC i).continuous.measurable.ennreal_ofReal)
      simpa only [blockTupleMeasure] using hfactor
    have hfiber : ∀ᵐ ω ∂P,
        (∏ i : Fin n, ∫⁻ p : Plane × Plane,
          ENNReal.ofReal (fC i p.1) * ENNReal.ofReal (gC i p.2) ∂B ω) =
        ENNReal.ofReal (∏ i : Fin n, ∫ p : Plane × Plane,
          fC i p.1 * gC i p.2 ∂B ω) := by
      filter_upwards [hinnerB] with ω hω
      rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg fun p =>
        mul_nonneg (hfC0 i p.1) (hgC0 i p.2))]
      apply Finset.prod_congr rfl
      intro i hi
      calc
        (∫⁻ p : Plane × Plane,
          ENNReal.ofReal (fC i p.1) * ENNReal.ofReal (gC i p.2) ∂B ω) =
          ∫⁻ p : Plane × Plane, ENNReal.ofReal (fC i p.1 * gC i p.2) ∂B ω := by
            apply lintegral_congr
            intro p
            exact (ENNReal.ofReal_mul (hfC0 i p.1)).symm
        _ = ENNReal.ofReal (∫ p : Plane × Plane, fC i p.1 * gC i p.2 ∂B ω) :=
          (ofReal_integral_eq_lintegral_ofReal (hω i)
            (Filter.Eventually.of_forall fun p => mul_nonneg (hfC0 i p.1) (hgC0 i p.2))).symm
    have hleft :
        (∫⁻ q, H q ∂(ν.withDensity W)) =
          ENNReal.ofReal (∫ ω, ∏ i : Fin n,
            ∫ p : Plane × Plane, fC i p.1 * gC i p.2 ∂B ω ∂P) := by
      calc
        (∫⁻ q, H q ∂(ν.withDensity W)) = ∫⁻ q, W q * H q ∂ν :=
          lintegral_withDensity_eq_lintegral_mul ν hWmeas hHmeas
        _ = ∫⁻ ω, ∫⁻ q, W q * H q
              ∂blockTupleMeasure n (B ω) ∂P := by
                exact Measure.lintegral_bind (m := P)
                  (μ := fun ω => blockTupleMeasure n (B ω)) htupleMeas.aemeasurable
                  (hWmeas.mul hHmeas).aemeasurable
        _ = ∫⁻ ω, ∏ i : Fin n, ∫⁻ p : Plane × Plane,
              ENNReal.ofReal (fC i p.1) * ENNReal.ofReal (gC i p.2) ∂B ω ∂P := by
                apply lintegral_congr
                intro ω
                exact htupleTest ω
        _ = ∫⁻ ω, ENNReal.ofReal (∏ i : Fin n,
              ∫ p : Plane × Plane, fC i p.1 * gC i p.2 ∂B ω) ∂P := by
                apply lintegral_congr_ae
                exact hfiber
        _ = ENNReal.ofReal (∫ ω, ∏ i : Fin n,
              ∫ p : Plane × Plane, fC i p.1 * gC i p.2 ∂B ω ∂P) :=
                (ofReal_integral_eq_lintegral_ofReal houterB
                  (Filter.Eventually.of_forall fun ω => Finset.prod_nonneg fun i _ =>
                    integral_nonneg fun p => mul_nonneg (hfC0 i p.1) (hgC0 i p.2))).symm
    have hright :
        (∫⁻ q, H q ∂(κ.withDensity W)) =
          ENNReal.ofReal (∫ x : Configuration n, ∫ y : Configuration n,
            (∏ i, fC i (x i)) *
              (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal *
                ∏ i, gC i (y i)) := by
      calc
        (∫⁻ q, H q ∂(κ.withDensity W)) = ∫⁻ q, W q * H q ∂κ :=
          lintegral_withDensity_eq_lintegral_mul κ hWmeas hHmeas
        _ = ∫⁻ q, (∏ i, ENNReal.ofReal (fC i (q.1 i))) *
              ∏ i, ENNReal.ofReal (gC i (q.2 i)) ∂κ := by
                apply lintegral_congr
                exact hWtimesH
        _ = ∫⁻ x : Configuration n, ∫⁻ y : Configuration n,
              (∏ i, ENNReal.ofReal (fC i (x i))) *
                momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y *
                  ∏ i, ENNReal.ofReal (gC i (y i)) := by
                have hfMeas : Measurable (fun x : Configuration n =>
                    ∏ i, ENNReal.ofReal (fC i (x i))) := by fun_prop
                have hgMeas : Measurable (fun y : Configuration n =>
                    ∏ i, ENNReal.ofReal (gC i (y i))) := by fun_prop
                rw [lintegral_kernelMeasure_mul hkernel hfMeas hgMeas]
        _ = ENNReal.ofReal (∫ x : Configuration n, ∫ y : Configuration n,
              (∏ i, fC i (x i)) *
                (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal *
                  ∏ i, gC i (y i)) :=
                lintegral_momentKernel_tensor_ofReal hn4
                  (ϑ - Real.eulerMascheroniConstant) (by linarith)
                  (fun i x => fC i x) (fun i x => gC i x)
                  (fun i => (fC i).continuous.memLp_of_hasCompactSupport (fC i).hasCompactSupport)
                  (fun i => (gC i).continuous.memLp_of_hasCompactSupport (gC i).hasCompactSupport)
                  hfC0 hgC0
    calc
      _ = ENNReal.ofReal (∫ ω, ∏ i : Fin n,
            ∫ p : Plane × Plane, fC i p.1 * gC i p.2 ∂B ω ∂P) := hleft
      _ = ENNReal.ofReal (∫ x : Configuration n, ∫ y : Configuration n,
            (∏ i, fC i (x i)) *
              (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal *
                ∏ i, gC i (y i)) := congrArg ENNReal.ofReal hmomentB
      _ = _ := hright.symm
  have hcut (m : ℕ) :
      ν.withDensity (fun q =>
        (∏ i, ENNReal.ofReal (RandomMeasure.vagueMassTest K m (q.1 i))) *
          ∏ i, ENNReal.ofReal (RandomMeasure.vagueMassTest K m (q.2 i))) =
      κ.withDensity (fun q =>
        (∏ i, ENNReal.ofReal (RandomMeasure.vagueMassTest K m (q.1 i))) *
          ∏ i, ENNReal.ofReal (RandomMeasure.vagueMassTest K m (q.2 i))) := by
    let χ : C_c(Plane, ℝ) := RandomMeasure.vagueMassTest K m
    let W : Configuration n × Configuration n → ℝ≥0∞ := fun q =>
      (∏ i, ENNReal.ofReal (χ (q.1 i))) * ∏ i, ENNReal.ofReal (χ (q.2 i))
    let νm := ν.withDensity W
    have hfinite : IsFiniteMeasure νm := by
      constructor
      have hlt := polymerSubseqLimit_tupleCutoff_lintegral_lt_top
        ϑ hPolymerMomentInput hFlatSixthMomentInput D hD hD0 ψ hψ P Z hZ hsD htD hst n hn1 hn4 m
      change (ν.withDensity W) Set.univ < ⊤
      rw [withDensity_apply W MeasurableSet.univ]
      simpa only [setLIntegral_univ, ν, B, χ, K, E, W] using hlt
    have htests : ∀ (f g : Fin n → BoundedContinuousFunction Plane NNReal),
        (∫⁻ q, (∏ i, (f i) (q.1 i) : NNReal) * ∏ i, (g i) (q.2 i)
          ∂νm) =
        ∫⁻ q, (∏ i, (f i) (q.1 i) : NNReal) * ∏ i, (g i) (q.2 i)
          ∂(κ.withDensity W) := by
      intro f g
      simpa only [νm, W, χ] using hKχ m f g
    exact @Measure.ext_of_lintegral_prod_mul_prod_boundedContinuousFunction
      (Fin n) (Fin n) (fun _ => Plane) (fun _ => Plane)
      _ inferInstance inferInstance inferInstance _ inferInstance inferInstance inferInstance
      (Fin.fintype n) (Fin.fintype n) νm (κ.withDensity W) hfinite htests
  have hraw : ν = κ := by
    -- The cutoff equalities identify the two measures on an increasing compact exhaustion.
    apply Measure.ext
    intro A hA
    let C := configurationCompactExhaustion n K
    let S (m : ℕ) := A ∩ ((C m) ×ˢ (C m))
    have hSmeas (m : ℕ) : MeasurableSet (S m) := by
      exact hA.inter ((C.isCompact m).isClosed.measurableSet.prod
        (C.isCompact m).isClosed.measurableSet)
    have hSmono : Monotone S := by
      intro m k hmk q hq
      exact ⟨hq.1, ⟨C.subset hmk hq.2.1, C.subset hmk hq.2.2⟩⟩
    have hUnion : (⋃ m, S m) = A := by
      ext q
      constructor
      · intro hq
        rcases Set.mem_iUnion.mp hq with ⟨m, hm⟩
        exact hm.1
      · intro hq
        have hleft : q.1 ∈ ⋃ m, C m := by
          have hcover : (⋃ m, C m) = Set.univ := C.iUnion_eq
          rw [hcover]
          exact Set.mem_univ _
        have hright : q.2 ∈ ⋃ m, C m := by
          have hcover : (⋃ m, C m) = Set.univ := C.iUnion_eq
          rw [hcover]
          exact Set.mem_univ _
        rcases Set.mem_iUnion.mp hleft with ⟨m₁, hm₁⟩
        rcases Set.mem_iUnion.mp hright with ⟨m₂, hm₂⟩
        refine Set.mem_iUnion.mpr ⟨max m₁ m₂, ⟨hq, ?_, ?_⟩⟩
        · exact (C.subset (Nat.le_max_left _ _)) hm₁
        · exact (C.subset (Nat.le_max_right _ _)) hm₂
    have hmass (m : ℕ) : ν (S m) = κ (S m) := by
      let χ : C_c(Plane, ℝ) := RandomMeasure.vagueMassTest K m
      let W : Configuration n × Configuration n → ℝ≥0∞ := fun q =>
        (∏ i, ENNReal.ofReal (χ (q.1 i))) * ∏ i, ENNReal.ofReal (χ (q.2 i))
      have hWone (q : Configuration n × Configuration n) (hq : q ∈ S m) : W q = 1 := by
        have hx (i : Fin n) : q.1 i ∈ K m := by
          have hq1 : q.1 ∈ C m := hq.2.1
          change q.1 ∈ Set.univ.pi (fun _ : Fin n => K m) at hq1
          exact hq1 i (Set.mem_univ i)
        have hy (i : Fin n) : q.2 i ∈ K m := by
          have hq2 : q.2 ∈ C m := hq.2.2
          change q.2 ∈ Set.univ.pi (fun _ : Fin n => K m) at hq2
          exact hq2 i (Set.mem_univ i)
        have hχx (i : Fin n) : χ (q.1 i) = 1 :=
          (RandomMeasure.vagueMassTest_spec K m).2.2.1 _ (hx i)
        have hχy (i : Fin n) : χ (q.2 i) = 1 :=
          (RandomMeasure.vagueMassTest_spec K m).2.2.1 _ (hy i)
        simp [W, hχx, hχy]
      have hcutm := hcut m
      calc
        ν (S m) = (ν.withDensity W) (S m) := by
          calc
            ν (S m) = ∫⁻ q in S m, (1 : ℝ≥0∞) ∂ν := by simp
            _ = ∫⁻ q in S m, W q ∂ν := by
              apply lintegral_congr_ae
              filter_upwards [ae_restrict_mem (hSmeas m)] with q hq
              rw [hWone q hq]
            _ = (ν.withDensity W) (S m) := (withDensity_apply W (hSmeas m)).symm
        _ = (κ.withDensity W) (S m) := congrArg (fun μ : Measure _ => μ (S m)) hcutm
        _ = κ (S m) := by
          calc
            (κ.withDensity W) (S m) = ∫⁻ q in S m, W q ∂κ :=
              withDensity_apply W (hSmeas m)
            _ = ∫⁻ q in S m, (1 : ℝ≥0∞) ∂κ := by
              apply lintegral_congr_ae
              filter_upwards [ae_restrict_mem (hSmeas m)] with q hq
              rw [hWone q hq]
            _ = κ (S m) := by simp
    have hacc : ∀ m, Set.accumulate S m = S m := by
      intro m
      ext q
      constructor
      · intro hq
        rcases Set.mem_accumulate.mp hq with ⟨k, hkm, hq⟩
        exact hSmono hkm hq
      · exact fun hq => Set.mem_accumulate.mpr ⟨m, le_rfl, hq⟩
    calc
      ν A = ⨆ m, ν (Set.accumulate S m) := by
        rw [← hUnion, measure_iUnion_eq_iSup_accumulate]
      _ = ⨆ m, κ (Set.accumulate S m) := iSup_congr fun m => by
        rw [hacc m, hmass m]
      _ = κ A := by
        rw [← hUnion, measure_iUnion_eq_iSup_accumulate]
  simpa only [ν, κ, B, E] using hraw

/-- For one to four replicas, the limiting moment formula holds for arbitrary real square-integrable endpoint tests. -/
theorem polymerSubseqLimit_moment_formula_of (ϑ : ℝ) (hPolymerMomentInput : PolymerMomentLimit ϑ)
    (hFlatSixthMomentInput : FlatSixthMomentBound ϑ) (D : Set ℝ) (hD : D.Countable)
    (hD0 : ∀ s ∈ D, 0 ≤ s) (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsPolymerSubseqLimit ϑ D ψ P Z) :
    ∀ n : ℕ, 1 ≤ n → n ≤ 4 → ∀ s ∈ D, ∀ t ∈ D, s < t →
      ∀ g g' : Fin n → Plane → ℝ, (∀ i, MemLp (g i) 2) → (∀ i, MemLp (g' i) 2) →
        (∀ᵐ ω ∂P, ∀ i, Integrable (fun p : Plane × Plane => g i p.1 * g' i p.2) (Z s t ω)) ∧
        Integrable (fun ω => ∏ i, ∫ p, g i p.1 * g' i p.2 ∂(Z s t ω)) P ∧
        ∫ ω, ∏ i, (∫ p, g i p.1 * g' i p.2 ∂(Z s t ω)) ∂P =
          ∫ x : Configuration n, ∫ y : Configuration n,
            (∏ i, g i (x i)) *
              (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal *
                ∏ i, g' i (y i) := by
  intro n hn1 hn4 s hsD t htD hst g g' hg hg'
  let E : CompactExhaustion (Plane × Plane) :=
    RandomMeasure.vagueCompactExhaustion (Plane × Plane)
  let B : Ω → Measure (Plane × Plane) :=
    RandomMeasure.locallyFiniteMeasureModification E (Z s t)
  have hBmeas : Measurable B :=
    RandomMeasure.measurable_locallyFiniteMeasureModification E (Z s t)
      ((hZ.1 s hsD t htD hst).1)
  have hBlf (ω : Ω) : IsLocallyFiniteMeasure (B ω) :=
    RandomMeasure.locallyFinite_locallyFiniteMeasureModification E (Z s t) ω
  have hBae : B =ᵐ[P] Z s t := by
    filter_upwards [(hZ.1 s hsD t htD hst).2] with ω hω
    change RandomMeasure.locallyFiniteMeasureModification E (Z s t) ω = Z s t ω
    exact RandomMeasure.locallyFiniteMeasureModification_apply_of_isLocallyFinite
      E (Z s t) ω hω.1
  have hmean : P.bind (fun ω => endpointTupleMeasure (fun _ : Fin n => B ω)) =
      volume.withDensity (Function.uncurry
        (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s))) := by
    simpa only [blockTupleMeasure, B, E] using
      polymerSubseqLimit_expectedTupleMeasure_eq_kernel ϑ hPolymerMomentInput hFlatSixthMomentInput D hD hD0 ψ hψ P Z hZ
        hsD htD hst n hn1 hn4
  have hkernel : Measurable (Function.uncurry
      (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s))) :=
    Measurable.comp
      (g := fun p : (ℝ × ℝ) × Configuration n × Configuration n =>
        momentKernel n p.1.1 p.1.2 p.2.1 p.2.2)
      (f := fun q : Configuration n × Configuration n =>
        ((ϑ - Real.eulerMascheroniConstant, t - s), q))
      (measurable_momentKernel n) (measurable_const.prodMk measurable_id)
  obtain ⟨C, rate, _, hbound⟩ :=
    exists_formBound_momentKernel n (ϑ - Real.eulerMascheroniConstant)
  let c : ℝ≥0∞ := ENNReal.ofReal
    (C * Real.exp (rate * (t - s)) * min (t - s) 1 ^ (-(n : ℝ)))
  have hc : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hkernelForm : FormBound volume volume
      (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s)) c := by
    exact hbound (ϑ - Real.eulerMascheroniConstant) le_rfl (t - s) (sub_pos.mpr hst)
  let Cn : Fin n → Ω → Measure (Plane × Plane) := fun _ ω => B ω
  have hCnmeas : ∀ i, Measurable (Cn i) := fun _ => hBmeas
  have hCnlf : ∀ i ω, IsLocallyFiniteMeasure (Cn i ω) := fun _ _ => hBlf _
  have hpair := integral_prod_pairings_of_endpointTuple_mean P Cn hCnmeas hCnlf
    hkernel hc hkernelForm hmean g g' hg hg'
  have hmeanOne : P.bind (fun ω => endpointTupleMeasure (fun _ : Fin 1 => B ω)) =
      volume.withDensity (Function.uncurry
        (momentKernel 1 (ϑ - Real.eulerMascheroniConstant) (t - s))) := by
    simpa only [blockTupleMeasure, B, E] using
      polymerSubseqLimit_expectedTupleMeasure_eq_kernel ϑ hPolymerMomentInput hFlatSixthMomentInput D hD hD0 ψ hψ P Z hZ
        hsD htD hst 1 (by norm_num) (by norm_num)
  have hkernelOne : Measurable (Function.uncurry
      (momentKernel 1 (ϑ - Real.eulerMascheroniConstant) (t - s))) :=
    Measurable.comp
      (g := fun p : (ℝ × ℝ) × Configuration 1 × Configuration 1 =>
        momentKernel 1 p.1.1 p.1.2 p.2.1 p.2.2)
      (f := fun q : Configuration 1 × Configuration 1 =>
        ((ϑ - Real.eulerMascheroniConstant, t - s), q))
      (measurable_momentKernel 1) (measurable_const.prodMk measurable_id)
  obtain ⟨C1, rate1, _, hbound1⟩ :=
    exists_formBound_momentKernel 1 (ϑ - Real.eulerMascheroniConstant)
  let c1 : ℝ≥0∞ := ENNReal.ofReal
    (C1 * Real.exp (rate1 * (t - s)) * min (t - s) 1 ^ (-(1 : ℝ)))
  have hc1 : c1 ≠ ⊤ := ENNReal.ofReal_ne_top
  have hkernelOneForm : FormBound volume volume
      (momentKernel 1 (ϑ - Real.eulerMascheroniConstant) (t - s)) c1 := by
    simpa [c1] using
      hbound1 (ϑ - Real.eulerMascheroniConstant) le_rfl (t - s) (sub_pos.mpr hst)
  have hinnerB : ∀ᵐ ω ∂P, ∀ i : Fin n,
      Integrable (fun p : Plane × Plane => g i p.1 * g' i p.2) (B ω) := by
    apply ae_all_iff.2
    intro i
    exact ae_integrable_pairing_of_endpointTuple_mean P B hBmeas hBlf hkernelOne hc1
      hkernelOneForm hmeanOne (g i) (g' i) (hg i) (hg' i)
  have hinnerZ : ∀ᵐ ω ∂P, ∀ i : Fin n,
      Integrable (fun p : Plane × Plane => g i p.1 * g' i p.2) (Z s t ω) := by
    filter_upwards [hBae, hinnerB] with ω hEq hω
    intro i
    rw [← hEq]
    exact hω i
  have hpairEq : (fun ω => ∏ i : Fin n,
      ∫ p : Plane × Plane, g i p.1 * g' i p.2 ∂B ω) =ᵐ[P]
      fun ω => ∏ i : Fin n,
        ∫ p : Plane × Plane, g i p.1 * g' i p.2 ∂Z s t ω := by
    filter_upwards [hBae, hinnerB, hinnerZ] with ω hEq hωB hωZ
    apply Finset.prod_congr rfl
    intro i hi
    rw [hEq]
  refine ⟨hinnerZ, hpair.1.congr hpairEq, ?_⟩
  calc
    (∫ ω, ∏ i : Fin n, (∫ p : Plane × Plane, g i p.1 * g' i p.2 ∂Z s t ω) ∂P) =
        ∫ ω, ∏ i : Fin n, (∫ p : Plane × Plane, g i p.1 * g' i p.2 ∂B ω) ∂P :=
      integral_congr_ae hpairEq.symm
    _ = ∫ x : Configuration n, ∫ y : Configuration n,
          (∏ i, g i (x i)) *
            (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal *
              ∏ i, g' i (y i) := hpair.2

/-- A uniform flat sixth-moment bound gives finite second moments for compact first-marginal tests of a subsequential limit. -/
theorem polymerSubseqLimit_flatMarginal_secondMoment_of (ϑ : ℝ)
    (hFlatSixthMomentInput : FlatSixthMomentBound ϑ) (D : Set ℝ) (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsPolymerSubseqLimit ϑ D ψ P Z)
    {s t : ℝ} (hsD : s ∈ D) (htD : t ∈ D) (hst : s < t)
    (hs : 0 ≤ s) (χ : C_c(Plane, ℝ)) (hχ : ∀ x, 0 ≤ χ x) :
    ∃ C : ℝ, Integrable (fun ω => (∫ x, χ x ∂((Z s t ω).map Prod.fst)) ^ 2) P ∧
      ∫ ω, (∫ x, χ x ∂((Z s t ω).map Prod.fst)) ^ 2 ∂P ≤ C := by
  let τ : ℝ := (t - s) / 2
  have hτ : 0 < τ := by dsimp [τ]; linarith
  obtain ⟨C, hC⟩ := hFlatSixthMomentInput χ (τ := τ) (T := t) hτ
  have hCevent : ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω => (∫ x, |χ x| ∂
        ((polymerMeasure ϑ N s t ω).map Prod.fst)) ^ 6) disorderLaw ∧
      ∫ ω, (∫ x, |χ x| ∂
        ((polymerMeasure ϑ N s t ω).map Prod.fst)) ^ 6 ∂disorderLaw ≤ C := by
    filter_upwards [hC] with N hN
    exact hN s t hs (by dsimp [τ]; linarith) le_rfl
  let X : ℕ → Disorder → ℝ := fun n ω =>
    ∫ x, χ x ∂((polymerMeasure ϑ (ψ n) s t ω).map Prod.fst)
  let Y : Ω → ℝ := fun ω => ∫ x, χ x ∂((Z s t ω).map Prod.fst)
  let s₁ : Fin 1 → ℝ := fun _ => s
  let t₁ : Fin 1 → ℝ := fun _ => t
  let φ : Fin 1 → C_c(Plane × Plane, ℝ) := fun _ => 0
  let χ₁ : Fin 1 → C_c(Plane, ℝ) := fun _ => χ
  let F : (Fin 1 → ℝ × ℝ) → ℝ := fun v => (v 0).2
  have hF : Continuous F := by fun_prop
  have hdist0 := hZ.2 1 s₁ t₁ (fun _ => ⟨hsD, htD, hst⟩) φ χ₁
  have hdist := hdist0.continuous_comp hF
  have hdist' : TendstoInDistribution X atTop Y (fun _ => disorderLaw) P := by
    simpa [Function.comp_def, X, Y, s₁, t₁, φ, χ₁, F] using hdist
  have hCψ : ∀ᶠ n : ℕ in atTop,
      Integrable (fun ω => |X n ω| ^ (6 : ℝ)) disorderLaw ∧
        ∫ ω, |X n ω| ^ (6 : ℝ) ∂disorderLaw ≤ C := by
    filter_upwards [hψ.tendsto_atTop.eventually hCevent] with n hn
    have hχeq (ω : Disorder) :
        ∫ x, |χ x| ∂((polymerMeasure ϑ (ψ n) s t ω).map Prod.fst) = X n ω := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [abs_of_nonneg (hχ x)]
    have hXnonneg (ω : Disorder) : 0 ≤ X n ω :=
      integral_nonneg (fun x => hχ x)
    have hpoweq : (fun ω => |X n ω| ^ (6 : ℝ)) = fun ω =>
        (∫ x, |χ x| ∂((polymerMeasure ϑ (ψ n) s t ω).map Prod.fst)) ^ (6 : ℕ) := by
      funext ω
      calc
        |X n ω| ^ (6 : ℝ) = |X n ω| ^ (6 : ℕ) := Real.rpow_natCast _ _
        _ = (∫ x, |χ x| ∂((polymerMeasure ϑ (ψ n) s t ω).map Prod.fst)) ^ (6 : ℕ) := by
          rw [abs_of_nonneg (hXnonneg ω), ← hχeq ω]
    refine ⟨hn.1.congr (Filter.Eventually.of_forall fun ω => (congrFun hpoweq ω).symm), ?_⟩
    calc
      ∫ ω, |X n ω| ^ (6 : ℝ) ∂disorderLaw =
          ∫ ω, (∫ x, |χ x| ∂((polymerMeasure ϑ (ψ n) s t ω).map Prod.fst)) ^ (6 : ℕ)
            ∂disorderLaw := integral_congr_ae
              (Filter.Eventually.of_forall fun ω => congrFun hpoweq ω)
      _ ≤ C := hn.2
  have hlim6 := Critical2DKPZ.JointConvergence.integrable_rpow_limit_of_tendstoInDistribution
    hdist' (by norm_num : (0 : ℝ) < 6)
    (hCψ.mono fun n hn => hn.1) (hCψ.mono fun n hn => hn.2)
  have hlim6Nat : Integrable (fun ω => |Y ω| ^ (6 : ℕ)) P ∧
      ∫ ω, |Y ω| ^ (6 : ℕ) ∂P ≤ C := by
    have hpoweq (ω : Ω) : |Y ω| ^ (6 : ℝ) = |Y ω| ^ (6 : ℕ) :=
      Real.rpow_natCast _ _
    refine ⟨hlim6.1.congr (Filter.Eventually.of_forall hpoweq), ?_⟩
    calc
      ∫ ω, |Y ω| ^ (6 : ℕ) ∂P = ∫ ω, |Y ω| ^ (6 : ℝ) ∂P :=
        integral_congr_ae (Filter.Eventually.of_forall fun ω => (hpoweq ω).symm)
      _ ≤ C := hlim6.2
  have hYsm : AEStronglyMeasurable Y P := hdist'.aemeasurable_limit.aestronglyMeasurable
  have hVsm : AEStronglyMeasurable (fun ω => Y ω ^ 2) P :=
    (continuous_id.pow 2).comp_aestronglyMeasurable hYsm
  have hmajorInt : Integrable (fun ω => 1 + |Y ω| ^ 6) P :=
    (integrable_const (1 : ℝ)).add hlim6Nat.1
  have hVInt : Integrable (fun ω => Y ω ^ 2) P := by
    refine hmajorInt.mono' hVsm ?_
    filter_upwards [] with ω
    change ‖Y ω ^ 2‖ ≤ 1 + |Y ω| ^ 6
    rw [Real.norm_of_nonneg (sq_nonneg (Y ω))]
    have hy : 0 ≤ |Y ω| := abs_nonneg _
    by_cases hy1 : |Y ω| ≤ 1
    · have hy2 : |Y ω| ^ 2 ≤ 1 := by
        calc
          |Y ω| ^ 2 ≤ 1 * |Y ω| := by nlinarith [mul_le_mul_of_nonneg_right hy1 hy]
          _ ≤ 1 := by simpa using hy1
      rw [← sq_abs]
      have hpowNonneg : 0 ≤ |Y ω| ^ 6 := pow_nonneg hy 6
      nlinarith
    · have hy1 : 1 ≤ |Y ω| := le_of_not_ge hy1
      have hpow : 1 ≤ |Y ω| ^ 4 := one_le_pow₀ hy1
      have hsq : |Y ω| ^ 2 ≤ |Y ω| ^ 6 := by
        have hmul := mul_nonneg (sq_nonneg (|Y ω|)) (sub_nonneg.mpr hpow)
        nlinarith
      rw [← sq_abs]
      nlinarith
  have hVbound : ∫ ω, Y ω ^ 2 ∂P ≤ 1 + C := by
    calc
      ∫ ω, Y ω ^ 2 ∂P ≤ ∫ ω, (1 + |Y ω| ^ 6) ∂P := by
        apply integral_mono hVInt hmajorInt
        intro ω
        change Y ω ^ 2 ≤ 1 + |Y ω| ^ 6
        have hy : 0 ≤ |Y ω| := abs_nonneg _
        by_cases hy1 : |Y ω| ≤ 1
        · have hy2 : |Y ω| ^ 2 ≤ 1 := by
            calc
              |Y ω| ^ 2 ≤ 1 * |Y ω| := by nlinarith [mul_le_mul_of_nonneg_right hy1 hy]
              _ ≤ 1 := by simpa using hy1
          rw [← sq_abs]
          have hpowNonneg : 0 ≤ |Y ω| ^ 6 := pow_nonneg hy 6
          nlinarith
        · have hy1 : 1 ≤ |Y ω| := le_of_not_ge hy1
          have hpow : 1 ≤ |Y ω| ^ 4 := one_le_pow₀ hy1
          have hsq : |Y ω| ^ 2 ≤ |Y ω| ^ 6 := by
            have hmul := mul_nonneg (sq_nonneg (|Y ω|)) (sub_nonneg.mpr hpow)
            nlinarith
          rw [← sq_abs]
          nlinarith
      _ = 1 + ∫ ω, |Y ω| ^ 6 ∂P := by
        rw [integral_add (integrable_const (1 : ℝ)) hlim6Nat.1, integral_const]
        simp
      _ ≤ 1 + C := by linarith [hlim6Nat.2]
  exact ⟨1 + C, hVInt, hVbound⟩

end Critical2DKPZ.SHF.Flow

end
