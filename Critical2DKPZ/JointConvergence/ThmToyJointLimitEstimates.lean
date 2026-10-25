/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.JointConvergence.ThmToyJointConvergence
public import Critical2DKPZ.JointConvergence.L2ToLp
public import Critical2DKPZ.JointConvergence.LawUniqueness
public import Critical2DKPZ.JointConvergence.Approximation
public import Critical2DKPZ.JointConvergence.KPZRegularizedReverseLaw
public import Critical2DKPZ.Definitions.IsCriticalKPZ
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Tactic

/-! # Moment bounds for tested reversed fields and finite vectors -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open Critical2DKPZ.SHF.Limit
open scoped BoundedContinuousFunction ENNReal Topology

namespace Critical2DKPZ.JointConvergence

private theorem integrable_rpow_sub_const_of_rpow_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {f : Ω → ℝ} {c q B M D : ℝ} (hf : AEStronglyMeasurable f P)
    (hq : 1 ≤ q) (hB : 1 ≤ B) (_hM : 0 ≤ M) (hD : 0 ≤ D)
    (hF : Integrable (fun ω => |f ω| ^ q) P)
    (hFbound : ∫ ω, |f ω| ^ q ∂P ≤ M * B ^ q)
    (hc : |c| ≤ D * B) :
    Integrable (fun ω => |f ω - c| ^ q) P ∧
      ∫ ω, |f ω - c| ^ q ∂P ≤ 2 ^ q * (M + D ^ q) * B ^ q := by
  have hq0 : 0 ≤ q := le_trans zero_le_one hq
  have hpoint (ω : Ω) : |f ω - c| ^ q ≤
      2 ^ q * (|f ω| ^ q + |c| ^ q) := by
    have habs : |f ω - c| ≤ |f ω| + |c| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (f ω) (-c)
    have hmax : |f ω| + |c| ≤ 2 * max |f ω| |c| := by
      nlinarith [le_max_left (|f ω|) |c|, le_max_right (|f ω|) |c|]
    have hpow : (|f ω| + |c|) ^ q ≤
        (2 * max |f ω| |c|) ^ q :=
      Real.rpow_le_rpow (by positivity) hmax hq0
    have hscale : (2 * max |f ω| |c|) ^ q =
        2 ^ q * (max |f ω| |c|) ^ q := by
      rw [Real.mul_rpow (by norm_num) (by positivity)]
    have hmaxpow : (max |f ω| |c|) ^ q ≤ |f ω| ^ q + |c| ^ q := by
      by_cases h : |f ω| ≤ |c|
      · rw [max_eq_right h]
        exact le_add_of_nonneg_left (Real.rpow_nonneg (abs_nonneg _) _)
      · rw [max_eq_left (le_of_not_ge h)]
        exact le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _)
    calc
      |f ω - c| ^ q ≤ (|f ω| + |c|) ^ q :=
        Real.rpow_le_rpow (abs_nonneg _) habs hq0
      _ ≤ (2 * max |f ω| |c|) ^ q := hpow
      _ = 2 ^ q * (max |f ω| |c|) ^ q := hscale
      _ ≤ 2 ^ q * (|f ω| ^ q + |c| ^ q) :=
        mul_le_mul_of_nonneg_left hmaxpow (Real.rpow_nonneg (by norm_num) _)
  have hmajor : Integrable
      (fun ω => 2 ^ q * (|f ω| ^ q + |c| ^ q)) P := by
    exact (hF.add (integrable_const (|c| ^ q))).const_mul (2 ^ q)
  have hmeas : AEStronglyMeasurable (fun ω => |f ω - c| ^ q) P := by
    exact ((Real.continuous_rpow_const hq0).comp continuous_abs).comp_aestronglyMeasurable
      (hf.sub aestronglyMeasurable_const)
  have hInt : Integrable (fun ω => |f ω - c| ^ q) P := by
    apply hmajor.mono' hmeas
    filter_upwards [] with ω
    have hleft : 0 ≤ |f ω - c| ^ q := Real.rpow_nonneg (abs_nonneg _) _
    have hright : 0 ≤ 2 ^ q * (|f ω| ^ q + |c| ^ q) := by positivity
    simpa [Real.norm_eq_abs, abs_of_nonneg hleft, abs_of_nonneg hright] using hpoint ω
  have hcPow : |c| ^ q ≤ D ^ q * B ^ q := by
    calc
      |c| ^ q ≤ (D * B) ^ q := Real.rpow_le_rpow (abs_nonneg _) hc hq0
      _ = D ^ q * B ^ q := by
        rw [Real.mul_rpow hD (le_trans zero_le_one hB)]
  refine ⟨hInt, ?_⟩
  calc
    ∫ ω, |f ω - c| ^ q ∂P ≤
        ∫ ω, 2 ^ q * (|f ω| ^ q + |c| ^ q) ∂P :=
      integral_mono hInt hmajor (fun ω => hpoint ω)
    _ = 2 ^ q * ((∫ ω, |f ω| ^ q ∂P) + |c| ^ q) := by
      rw [integral_const_mul, integral_add hF (integrable_const (|c| ^ q)), integral_const]
      simp
    _ ≤ 2 ^ q * (M * B ^ q + D ^ q * B ^ q) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hFbound hcPow)
        (Real.rpow_nonneg (by norm_num) _)
    _ = 2 ^ q * (M + D ^ q) * B ^ q := by ring

private noncomputable def testIntegralRpowConstant (φ : TestFn) (q : ℝ) : ℝ :=
  let K : Set Plane := tsupport (φ : Plane → ℝ)
  let μK : Measure Plane := volume.restrict K
  let r : ℝ := q / (q - 1)
  ((∫ x, |φ x| ^ r ∂μK) ^ (1 / r : ℝ)) ^ q *
    (∫ x, K.indicator (fun _ => (1 : ℝ)) x ∂volume)

private theorem integral_test_rpow_bound_of_uniform_rpow
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {F : Plane × Ω → ℝ} (hF : AEMeasurable F (volume.prod P))
    (φ : TestFn)
    (hProd : Integrable (fun z : Plane × Ω => (φ : Plane → ℝ) z.1 * F z)
      (volume.prod P))
    {q M : ℝ} (hq : 1 < q) (hM : 0 ≤ M)
    (hMoment : ∀ x, Integrable (fun ω => |F (x, ω)| ^ q) P ∧
      ∫ ω, |F (x, ω)| ^ q ∂P ≤ M) :
    ∃ C : ℝ, C = testIntegralRpowConstant φ q ∧ 0 ≤ C ∧
      Integrable (fun ω => |∫ x, φ x * F (x, ω)| ^ q) P ∧
      ∫ ω, |∫ x, φ x * F (x, ω)| ^ q ∂P ≤ C * M := by
  classical
  let K : Set Plane := tsupport (φ : Plane → ℝ)
  let K2 : Set (Plane × Ω) := K ×ˢ Set.univ
  let μK : Measure Plane := volume.restrict K
  have hKcompact : IsCompact K := φ.hasCompactSupport
  have hKmeas : MeasurableSet K := hKcompact.isClosed.measurableSet
  have hKvol : volume K < ∞ := hKcompact.measure_lt_top
  have hKvolNe : volume K ≠ ∞ := hKvol.ne
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hφzero (x : Plane) (hx : x ∉ K) : φ x = 0 := by
    by_contra hne
    have hxSupp : x ∈ Function.support (φ : Plane → ℝ) := by
      simpa [Function.mem_support] using hne
    exact hx (by simpa [K] using subset_tsupport (φ : Plane → ℝ) hxSupp)
  have hK2 : MeasurableSet K2 := hKmeas.prod MeasurableSet.univ
  let G : Plane × Ω → ℝ := K2.indicator (fun z => |F z| ^ q)
  have hFq : AEMeasurable (fun z : Plane × Ω => |F z| ^ q) (volume.prod P) :=
    ((Real.continuous_rpow_const hqpos.le).comp continuous_abs).measurable.comp_aemeasurable hF
  have hGsm : AEStronglyMeasurable G (volume.prod P) := by
    dsimp [G]
    exact hFq.aestronglyMeasurable.indicator hK2
  have hGsec (x : Plane) : Integrable (fun ω => G (x, ω)) P := by
    by_cases hx : x ∈ K
    · simpa [G, K2, hx] using (hMoment x).1
    · simp [G, K2, hx]
  let H : Plane → ℝ := fun x => ∫ ω, ‖G (x, ω)‖ ∂P
  have hHmeas : AEMeasurable H volume := hGsm.norm.integral_prod_right'.aemeasurable
  have hHbound (x : Plane) : H x ≤ K.indicator (fun _ => M) x := by
    by_cases hx : x ∈ K
    · simpa [H, G, K2, hx, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] using (hMoment x).2
    · simp [H, G, K2, hx]
  have hmajorOn : IntegrableOn (fun _ : Plane => M) K volume :=
    integrableOn_const hKvolNe
  have hmajor : Integrable (K.indicator (fun _ => M)) volume :=
    hmajorOn.integrable_indicator hKmeas
  have hHint : Integrable H volume := by
    apply hmajor.mono' hHmeas.aestronglyMeasurable
    filter_upwards [] with x
    have hHnonneg : 0 ≤ H x := integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun ω => norm_nonneg (G (x, ω)))
    by_cases hx : x ∈ K
    · calc
        ‖H x‖ = H x := Real.norm_of_nonneg hHnonneg
        _ ≤ M := by simpa [hx] using hHbound x
        _ = K.indicator (fun _ => M) x := by simp [hx]
    · have hHzero : H x = 0 := by
        apply le_antisymm
        · simpa [K, hx] using hHbound x
        · exact integral_nonneg_of_ae
            (Filter.Eventually.of_forall fun ω => norm_nonneg (G (x, ω)))
      simp [hx, hHzero]
  have hGint : Integrable G (volume.prod P) :=
    (integrable_prod_iff hGsm).2
      ⟨Filter.Eventually.of_forall hGsec, hHint⟩
  have hGnormInt : Integrable (fun z => ‖G z‖) (volume.prod P) := hGint.norm
  have hGsecAE : ∀ᵐ ω ∂P, Integrable (fun x => G (x, ω)) volume :=
    hGint.prod_left_ae
  have hFsecAE : ∀ᵐ ω ∂P, AEStronglyMeasurable (fun x => F (x, ω)) volume :=
    hF.aestronglyMeasurable.prod_swap.prodMk_left
  have hHomega : Integrable (fun ω => ∫ x, ‖G (x, ω)‖ ∂volume) P :=
    hGnormInt.integral_prod_right
  have hGintEq (ω : Ω) : (∫ x, ‖G (x, ω)‖ ∂volume) =
      ∫ x, |F (x, ω)| ^ q ∂μK := by
    have hpoint : (fun x : Plane => ‖G (x, ω)‖) =
        K.indicator (fun x => |F (x, ω)| ^ q) := by
      funext x
      by_cases hx : x ∈ K
      · simp [G, K2, hx, Real.norm_eq_abs,
          Real.rpow_nonneg (abs_nonneg _) _]
      · simp [G, K2, hx]
    rw [hpoint, ← integral_indicator hKmeas]
  let Mtot : ℝ := ∫ x, K.indicator (fun _ => M) x ∂volume
  let VK : ℝ := ∫ x, K.indicator (fun _ => (1 : ℝ)) x ∂volume
  have hmajor_nonneg (x : Plane) : 0 ≤ K.indicator (fun _ => M) x := by
    by_cases hx : x ∈ K <;> simp [hx, hM]
  have hMtot : 0 ≤ Mtot := by
    dsimp [Mtot]
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall hmajor_nonneg)
  have hMtotEq : Mtot = M * VK := by
    have hpoint : (fun x : Plane => K.indicator (fun _ => M) x) =
        fun x => M * K.indicator (fun _ => (1 : ℝ)) x := by
      funext x
      by_cases hx : x ∈ K <;> simp [hx]
    calc
      Mtot = ∫ x, M * K.indicator (fun _ => (1 : ℝ)) x ∂volume := by
        dsimp [Mtot]
        rw [hpoint]
      _ = M * VK := by simp [VK, integral_const_mul]
  have htotal : ∫ ω, ∫ x, ‖G (x, ω)‖ ∂volume ∂P ≤ Mtot := by
    have hswap : (∫ ω, ∫ x, ‖G (x, ω)‖ ∂volume ∂P) =
        ∫ x, ∫ ω, ‖G (x, ω)‖ ∂P ∂volume := by
      calc
        _ = ∫ z, ‖G z‖ ∂(volume.prod P) :=
          (integral_prod_symm (fun z : Plane × Ω => ‖G z‖) hGnormInt).symm
        _ = _ := integral_prod (fun z : Plane × Ω => ‖G z‖) hGnormInt
    rw [hswap]
    dsimp [Mtot]
    apply integral_mono hHint hmajor
    exact hHbound
  let r : ℝ := q / (q - 1)
  have hqsub : 0 < q - 1 := by linarith
  have hr : 1 < r := by
    dsimp [r]
    rw [one_lt_div hqsub]
    linarith
  have hr0 : 0 ≤ r := by linarith
  have hHolder : r.HolderConjugate q := by
    rw [Real.holderConjugate_iff]
    constructor
    · exact hr
    · dsimp [r]
      field_simp
      ring
  have hφpowSM : AEStronglyMeasurable (fun x : Plane => |φ x| ^ r) volume := by
    exact ((Real.continuous_rpow_const hr0).comp (continuous_abs.comp φ.continuous)).aestronglyMeasurable
  obtain ⟨B₀, hB₀⟩ := hKcompact.exists_bound_of_continuousOn φ.continuous.continuousOn
  let Bφ : ℝ := max B₀ 0
  have hBφ : 0 ≤ Bφ := le_max_right _ _
  have hφbound (x : Plane) (hx : x ∈ K) : |φ x| ≤ Bφ := by
    have h := hB₀ x hx
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  have hφpowInt : IntegrableOn (fun x : Plane => |φ x| ^ r) K volume := by
    apply volume.integrableOn_of_bounded hKvolNe hφpowSM
    filter_upwards [ae_restrict_mem hKmeas] with x hx
    have hbound := Real.rpow_le_rpow (abs_nonneg (φ x)) (hφbound x hx) hr0
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      using hbound
  have hφpowμ : Integrable (fun x : Plane => |φ x| ^ r) μK := by
    simpa only [μK, IntegrableOn] using hφpowInt
  have hrENN : ENNReal.ofReal r ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (lt_trans zero_lt_one hr)).ne'
  have hqENN : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.mpr hqpos).ne'
  have hrTop : ENNReal.ofReal r ≠ ∞ := by simp
  have hqTop : ENNReal.ofReal q ≠ ∞ := by simp
  let μ1 : Measure Plane := μK
  let φfun : Plane → ℝ := fun x => φ x
  have hφmemPow : MemLp (fun x : Plane => ‖φfun x‖ ^ r) 1 μ1 := by
    apply memLp_one_iff_integrable.mpr
    simpa [φfun, Real.norm_eq_abs] using hφpowμ
  have hrDiv : ENNReal.ofReal r / ENNReal.ofReal r = 1 :=
    ENNReal.div_self hrENN (by simp)
  have hφmemPow' : MemLp (fun x : Plane => ‖φfun x‖ ^ ENNReal.toReal (ENNReal.ofReal r))
      (ENNReal.ofReal r / ENNReal.ofReal r) μ1 := by
    simpa [hrDiv, ENNReal.toReal_ofReal hr0, φfun] using hφmemPow
  have hφmem : MemLp φfun (ENNReal.ofReal r) μ1 :=
    (memLp_norm_rpow_iff (f := φfun) (p := ENNReal.ofReal r) (q := ENNReal.ofReal r)
      φ.continuous.aestronglyMeasurable hrENN hrTop).mp hφmemPow'
  have hFmem (ω : Ω) (hωF : AEStronglyMeasurable (fun x : Plane => F (x, ω)) volume)
      (hωG : Integrable (fun x : Plane => G (x, ω)) volume) :
      MemLp (fun x : Plane => F (x, ω)) (ENNReal.ofReal q) μK := by
    have hGω' : Integrable (K.indicator (fun x => |F (x, ω)| ^ q)) volume := by
      convert hωG using 1
      ext x
      by_cases hx : x ∈ K <;> simp [G, K2, hx]
    have hFqμ : Integrable (fun x : Plane => |F (x, ω)| ^ q) μK := by
      simpa only [μK, IntegrableOn] using (integrable_indicator_iff hKmeas).mp hGω'
    have hFmemPow : MemLp (fun x : Plane => ‖F (x, ω)‖ ^ q) 1 μK := by
      apply memLp_one_iff_integrable.mpr
      simpa only [Real.norm_eq_abs] using hFqμ
    have hqDiv : ENNReal.ofReal q / ENNReal.ofReal q = 1 :=
      ENNReal.div_self hqENN (by simp)
    have hFmemPow' : MemLp (fun x : Plane => ‖F (x, ω)‖ ^ ENNReal.toReal (ENNReal.ofReal q))
        (ENNReal.ofReal q / ENNReal.ofReal q) μK := by
      simpa [hqDiv, ENNReal.toReal_ofReal hqpos.le] using hFmemPow
    exact (memLp_norm_rpow_iff (f := fun x : Plane => F (x, ω))
      (p := ENNReal.ofReal q) (q := ENNReal.ofReal q)
      (hωF.mono_measure Measure.restrict_le_self) hqENN hqTop).mp hFmemPow'
  let A : ℝ := (∫ x, ‖φfun x‖ ^ r ∂μK) ^ (1 / r)
  have hAnonneg : 0 ≤ A := by
    dsimp [A]
    apply Real.rpow_nonneg
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun x =>
      Real.rpow_nonneg (norm_nonneg (φfun x)) r)
  have hYstrong : AEStronglyMeasurable (fun ω => ∫ x, φ x * F (x, ω)) P :=
    hProd.aestronglyMeasurable.prod_swap.integral_prod_right'
  have hYqmeas : AEStronglyMeasurable
      (fun ω => |∫ x, φ x * F (x, ω)| ^ q) P :=
    ((Real.continuous_rpow_const hqpos.le).comp continuous_abs).comp_aestronglyMeasurable hYstrong
  let hB : Ω → ℝ := fun ω => ∫ x, |F (x, ω)| ^ q ∂μK
  have hBnonneg (ω : Ω) : 0 ≤ hB ω := by
    apply integral_nonneg_of_ae
    exact Filter.Eventually.of_forall fun x =>
      Real.rpow_nonneg (abs_nonneg (F (x, ω))) q
  have hBint : Integrable hB P := by
    apply hHomega.congr
    filter_upwards [] with ω
    simpa [hB] using hGintEq ω
  have hBbound : ∫ ω, hB ω ∂P ≤ Mtot := by
    calc
      _ = ∫ ω, ∫ x, ‖G (x, ω)‖ ∂volume ∂P := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω => by
          simpa [hB] using (hGintEq ω).symm
      _ ≤ Mtot := htotal
  have hBbound' : ∫ ω, hB ω ∂P ≤ M * VK := by
    rw [← hMtotEq]
    exact hBbound
  have hAqnonneg : 0 ≤ A ^ q := Real.rpow_nonneg hAnonneg _
  have hYqmajor : Integrable (fun ω => A ^ q * hB ω) P := hBint.const_mul (A ^ q)
  have hYqle : ∀ᵐ ω ∂P,
      |∫ x, φ x * F (x, ω)| ^ q ≤ A ^ q * hB ω := by
    filter_upwards [hGsecAE, hFsecAE, hProd.prod_left_ae] with ω hωG hωF hωProd
    let μ1 : Measure Plane := μK
    have hFmemω := hFmem ω hωF hωG
    have hφmemω : MemLp φfun (ENNReal.ofReal r) μ1 := hφmem
    have hHolderω := integral_mul_norm_le_Lp_mul_Lq (p := r) (q := q)
      hHolder hφmemω hFmemω
    have hωProdK : Integrable (fun x => φ x * F (x, ω)) μ1 :=
      hωProd.mono_measure Measure.restrict_le_self
    have hset : (∫ x in K, φ x * F (x, ω) ∂volume) =
        ∫ x, φ x * F (x, ω) ∂volume :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        rw [hφzero x hx]
        simp
    have hYabs : |∫ x, φ x * F (x, ω) ∂volume| ≤
        A * (hB ω) ^ (1 / q) := by
      calc
        |∫ x, φ x * F (x, ω) ∂volume| =
            |∫ x in K, φ x * F (x, ω) ∂volume| := by rw [hset]
        _ ≤ ∫ x in K, ‖φ x * F (x, ω)‖ ∂volume := by
          rw [← Real.norm_eq_abs]
          exact norm_integral_le_integral_norm _
        _ = ∫ x, ‖φfun x‖ * ‖F (x, ω)‖ ∂μ1 := by
          simp only [μ1, μK]
          congr 1
          ext x
          exact norm_mul _ _
        _ ≤ _ := by simpa [A, hB, φfun, μ1, Real.norm_eq_abs] using hHolderω
    have hpower : |∫ x, φ x * F (x, ω) ∂volume| ^ q ≤ A ^ q * hB ω := by
      calc
        _ ≤ (A * (hB ω) ^ (1 / q)) ^ q :=
          Real.rpow_le_rpow (abs_nonneg _) hYabs hqpos.le
        _ = A ^ q * hB ω := by
          rw [Real.mul_rpow hAnonneg (Real.rpow_nonneg (hBnonneg ω) _),
            ← Real.rpow_mul (hBnonneg ω)]
          have hcancel : (1 / q) * q = 1 := by field_simp
          rw [hcancel, Real.rpow_one]
    exact hpower
  have hYqInt : Integrable (fun ω => |∫ x, φ x * F (x, ω)| ^ q) P := by
    apply hYqmajor.mono' hYqmeas
    filter_upwards [hYqle] with ω hω
    have hleft : 0 ≤ |∫ x, φ x * F (x, ω)| ^ q :=
      Real.rpow_nonneg (abs_nonneg _) _
    have hright : 0 ≤ A ^ q * hB ω := mul_nonneg hAqnonneg (hBnonneg ω)
    simpa [Real.norm_eq_abs, abs_of_nonneg hleft, abs_of_nonneg hright] using hω
  have hVKnonneg : 0 ≤ VK := by
    dsimp [VK]
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => by
      by_cases hx : x ∈ K <;> simp [hx])
  refine ⟨A ^ q * VK, ?_, mul_nonneg hAqnonneg hVKnonneg, hYqInt, ?_⟩
  ·
    have hrpow : 1 / (q / (q - 1)) = (q - 1) / q := by
      field_simp
    dsimp [testIntegralRpowConstant, A, VK, φfun, μK, K, r]
  calc
    ∫ ω, |∫ x, φ x * F (x, ω)| ^ q ∂P ≤ ∫ ω, A ^ q * hB ω ∂P := by
      exact integral_mono_ae hYqInt hYqmajor hYqle
    _ = A ^ q * ∫ ω, hB ω ∂P := integral_const_mul _ _
    _ ≤ A ^ q * (M * VK) :=
      mul_le_mul_of_nonneg_left hBbound' hAqnonneg
    _ = (A ^ q * VK) * M := by ring

private theorem shf_heatStartLogField_rpow_log_width_bound
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF ϑ P Z)
    (hpair : ∀ {s t δ : ℝ}, 0 ≤ s → s < t → 0 < δ →
      ∀ (x : Plane) (g : Plane →ᵇ ℝ),
        (∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane =>
          heatKernel δ (p.1 - x) * g p.2) (Z s t ω)) ∧
        Integrable (shfPairing Z s t (fun y => heatKernel δ (y - x)) g) P ∧
        (∫ ω, |shfPairing Z s t (fun y => heatKernel δ (y - x)) g ω| ∂P ≤ ‖g‖) ∧
        TendstoInDistribution
          (fun (N : ℕ) (ω : Disorder) =>
            ∫ p, heatKernel δ (p.1 - x) * g p.2 ∂(polymerMeasure ϑ N s t ω))
          atTop (shfPairing Z s t (fun y => heatKernel δ (y - x)) g)
          (fun _ => disorderLaw) P)
    (hjoint : ∀ (k : ℕ) (s t δ : Fin k → ℝ) (x : Fin k → Plane)
      (g : Fin k → (Plane →ᵇ ℝ)),
      (∀ i, 0 ≤ s i ∧ s i < t i ∧ 0 < δ i) →
      TendstoInDistribution
        (fun (N : ℕ) (ω : Disorder) (i : Fin k) =>
          ∫ p, heatKernel (δ i) (p.1 - x i) * g i p.2
            ∂(polymerMeasure ϑ N (s i) (t i) ω))
        atTop (fun ω i => shfPairing Z (s i) (t i)
          (fun y => heatKernel (δ i) (y - x i)) (g i) ω)
        (fun _ => disorderLaw) P)
    (hpos : ∀ (s t δ : ℝ) (x : Plane) (h₀ : Plane →ᵇ ℝ),
      0 ≤ s → s < t → 0 < δ →
      (∀ᵐ ω ∂P, 0 < shfPairing Z s t
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω) ∧
      AEMeasurable (fun ω => Real.log (shfPairing Z s t
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω)) P)
    (t T δ₁ : ℝ) (ht : 0 ≤ t) (htT : t < T) (hδ₁ : 0 < δ₁)
    (hδ₁T : δ₁ ≤ T - t) (h₀ : Plane →ᵇ ℝ) (H : ℝ)
    (hH : ‖h₀‖ ≤ H) {q : ℝ} (hq : 0 < q) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ δ ∈ Set.Ioo 0 δ₁, ∀ x : Plane,
      Integrable (fun ω => |Real.log (shfPairing Z (t + δ) T
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω)| ^ q) P ∧
      ∫ ω, |Real.log (shfPairing Z (t + δ) T
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω)| ^ q ∂P ≤
        M * (1 + Real.log (1 + |Real.log δ|)) ^ q := by
  obtain ⟨M, hM, hProf⟩ := heatStartLogProfile_rpow_log_width_bound ϑ
    ht htT hδ₁ hδ₁T h₀ H hH hq
  refine ⟨M, hM, ?_⟩
  intro δ hδ x
  have hδpos : 0 < δ := hδ.1
  have hs : 0 ≤ t + δ := by linarith
  have hsT : t + δ < T := by linarith [hδ.2, hδ₁T]
  have hparams : ∀ i : Fin 1,
      0 ≤ (fun _ : Fin 1 => t + δ) i ∧
      (fun _ : Fin 1 => t + δ) i < T ∧
      0 < (fun _ : Fin 1 => δ) i := by
    intro i
    exact ⟨hs, hsT, hδpos⟩
  have hsource := heatStart_log_tendsto_of ϑ P Z hZ hpair hjoint hpos
    T h₀ 1 (fun _ => t + δ) (fun _ => δ) (fun _ => x) hparams
  have hcoord := hsource.2.1.continuous_comp
    (g := fun v : Fin 1 → ℝ => v 0) (continuous_apply 0)
  have hdist : TendstoInDistribution
      (fun N ω => heatStartLogProfile ϑ N (t + δ) T δ x h₀ ω) atTop
      (fun ω => Real.log (shfPairing Z (t + δ) T
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω))
      (fun _ => disorderLaw) P := by
    simpa [heatStartLogProfile, Function.comp_def] using hcoord
  have hN := hProf δ hδ
  have hNint : ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω => |heatStartLogProfile ϑ N (t + δ) T δ x h₀ ω| ^ q)
        disorderLaw := by
    filter_upwards [hN] with N hN
    exact (hN x).1
  have hNbound : ∀ᶠ N : ℕ in atTop,
      ∫ ω, |heatStartLogProfile ϑ N (t + δ) T δ x h₀ ω| ^ q ∂disorderLaw ≤
        M * (1 + Real.log (1 + |Real.log δ|)) ^ q := by
    filter_upwards [hN] with N hN
    exact (hN x).2
  exact integrable_rpow_limit_of_tendstoInDistribution hdist hq hNint hNbound

/-- For `q > 1` there is a constant `C` such that, for every width `δ < δ₁`, the tested reversed
regularized field is a.e. strongly measurable, its `q`-th absolute power is integrable, and its
integral is at most `C (1 + log (1 + |log δ|)) ^ q`. -/
theorem kpzRegularizedReversed_test_rpow_log_width_bound
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF ϑ P Z)
    (hpair : ∀ {s t δ : ℝ}, 0 ≤ s → s < t → 0 < δ →
      ∀ (x : Plane) (g : Plane →ᵇ ℝ),
        (∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane =>
          heatKernel δ (p.1 - x) * g p.2) (Z s t ω)) ∧
        Integrable (shfPairing Z s t (fun y => heatKernel δ (y - x)) g) P ∧
        (∫ ω, |shfPairing Z s t (fun y => heatKernel δ (y - x)) g ω| ∂P ≤ ‖g‖) ∧
        TendstoInDistribution
          (fun (N : ℕ) (ω : Disorder) =>
            ∫ p, heatKernel δ (p.1 - x) * g p.2 ∂(polymerMeasure ϑ N s t ω))
          atTop (shfPairing Z s t (fun y => heatKernel δ (y - x)) g)
          (fun _ => disorderLaw) P)
    (hjoint : ∀ (k : ℕ) (s t δ : Fin k → ℝ) (x : Fin k → Plane)
      (g : Fin k → (Plane →ᵇ ℝ)),
      (∀ i, 0 ≤ s i ∧ s i < t i ∧ 0 < δ i) →
      TendstoInDistribution
        (fun (N : ℕ) (ω : Disorder) (i : Fin k) =>
          ∫ p, heatKernel (δ i) (p.1 - x i) * g i p.2
            ∂(polymerMeasure ϑ N (s i) (t i) ω))
        atTop (fun ω i => shfPairing Z (s i) (t i)
          (fun y => heatKernel (δ i) (y - x i)) (g i) ω)
        (fun _ => disorderLaw) P)
    (hpos : ∀ (s t δ : ℝ) (x : Plane) (h₀ : Plane →ᵇ ℝ),
      0 ≤ s → s < t → 0 < δ →
      (∀ᵐ ω ∂P, 0 < shfPairing Z s t
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω) ∧
      AEMeasurable (fun ω => Real.log (shfPairing Z s t
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω)) P)
    (t T δ₁ : ℝ) (ht : 0 ≤ t) (htT : t < T) (hδ₁ : 0 < δ₁)
    (hδ₁T : δ₁ ≤ T - t) (h₀ : Plane →ᵇ ℝ) (φ : TestFn)
    {q : ℝ} (hq : 1 < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ ∈ Set.Ioo 0 δ₁,
      AEStronglyMeasurable (fun ω => ∫ x, φ x *
        kpzRegularizedReversed P Z t T δ h₀ x ω) P ∧
      Integrable (fun ω => |∫ x, φ x *
        kpzRegularizedReversed P Z t T δ h₀ x ω| ^ q) P ∧
      ∫ ω, |∫ x, φ x * kpzRegularizedReversed P Z t T δ h₀ x ω| ^ q ∂P ≤
        C * (1 + Real.log (1 + |Real.log δ|)) ^ q := by
  classical
  obtain ⟨Mq, hMq, hFieldq⟩ := shf_heatStartLogField_rpow_log_width_bound
    ϑ P Z hZ hpair hjoint hpos t T δ₁ ht htT hδ₁ hδ₁T h₀ ‖h₀‖ le_rfl
    (q := q) (by linarith)
  obtain ⟨M2, hM2, hField2⟩ := shf_heatStartLogField_rpow_log_width_bound
    ϑ P Z hZ hpair hjoint hpos t T δ₁ ht htT hδ₁ hδ₁T h₀ ‖h₀‖ le_rfl
    (q := 2) (by norm_num)
  obtain ⟨M1, hM1, hField1⟩ := shf_heatStartLogField_rpow_log_width_bound
    ϑ P Z hZ hpair hjoint hpos t T δ₁ ht htT hδ₁ hδ₁T (0 : Plane →ᵇ ℝ) 0
    (by simp) (q := 1) (by norm_num)
  let Kφ : ℝ := ∫ x, φ x
  have hKφint : Integrable φ :=
    φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have hBnonneg (δ : ℝ) (hδ : δ ∈ Set.Ioo 0 δ₁) :
      0 ≤ 1 + Real.log (1 + |Real.log δ|) := by
    have harg : 1 ≤ 1 + |Real.log δ| := by linarith [abs_nonneg (Real.log δ)]
    have hlog : 0 ≤ Real.log (1 + |Real.log δ|) := Real.log_nonneg harg
    linarith
  have hBge (δ : ℝ) (hδ : δ ∈ Set.Ioo 0 δ₁) :
      1 ≤ 1 + Real.log (1 + |Real.log δ|) := by
    have harg : 1 ≤ 1 + |Real.log δ| := by linarith [abs_nonneg (Real.log δ)]
    have hlog : 0 ≤ Real.log (1 + |Real.log δ|) := Real.log_nonneg harg
    linarith
  let Ctest₀ : ℝ := max (testIntegralRpowConstant φ q) 0
  let Cq : ℝ := Ctest₀ * Mq
  let D : ℝ := M1 * |Kφ|
  let C : ℝ := 2 ^ q * (Cq + D ^ q)
  have hCq : 0 ≤ Cq := by
    dsimp [Cq, Ctest₀]
    exact mul_nonneg (le_max_right _ _) hMq
  have hD : 0 ≤ D := mul_nonneg hM1 (abs_nonneg _)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro δ hδ
  let B : ℝ := 1 + Real.log (1 + |Real.log δ|)
  let F : Plane × Ω → ℝ := fun z => Real.log
    (shfPairing Z (t + δ) T (fun y => heatKernel δ (y - z.1))
      (fun y => Real.exp (h₀ y)) z.2)
  have hδpos : 0 < δ := hδ.1
  have hs : 0 ≤ t + δ := by linarith [ht]
  have hsT : t + δ < T := by linarith [hδ.2, hδ₁T]
  have hlocal : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (Z (t + δ) T ω) := by
    filter_upwards [hZ.2.1 (t + δ) T hs hsT] with ω hω
    exact hω.1
  have hg : Measurable (fun y : Plane => Real.exp (h₀ y)) :=
    Real.continuous_exp.measurable.comp h₀.continuous.measurable
  have hF : AEMeasurable F (volume.prod P) := by
    exact aemeasurable_log_heatPairing_joint P (Z (t + δ) T)
      (hZ.1 (t + δ) T hs hsT) hlocal δ hδpos
      (fun y => Real.exp (h₀ y)) hg (fun y => (Real.exp_pos (h₀ y)).le)
  have hFsec (x : Plane) : AEStronglyMeasurable (fun ω => F (x, ω)) P := by
    exact (hpos (t + δ) T δ x h₀ hs hsT hδpos).2.aestronglyMeasurable
  have hSq (x : Plane) : Integrable (fun ω => |F (x, ω)| ^ 2) P ∧
      ∫ ω, |F (x, ω)| ^ 2 ∂P ≤ M2 * B ^ 2 := by
    simpa [F, B] using hField2 δ hδ x
  have hM2B : 0 ≤ M2 * B ^ 2 := mul_nonneg hM2 (sq_nonneg B)
  have hSq' (x : Plane) : Integrable (fun ω => |F (x, ω)| ^ 2) P ∧
      ∫ ω, |F (x, ω)| ^ 2 ∂P ≤ M2 * B ^ 2 := hSq x
  have hProd : Integrable (fun z : Plane × Ω => φ z.1 * F z) (volume.prod P) :=
    integrable_test_mul_joint P hF hFsec hM2B hSq' φ
  have hMoment (x : Plane) : Integrable (fun ω => |F (x, ω)| ^ q) P ∧
      ∫ ω, |F (x, ω)| ^ q ∂P ≤ Mq * B ^ q := by
    simpa [F, B] using hFieldq δ hδ x
  obtain ⟨Ctest, hCtestEq, hCtest, hUqInt, hUqBound⟩ :=
    integral_test_rpow_bound_of_uniform_rpow P hF φ hProd hq
      (mul_nonneg hMq (Real.rpow_nonneg (hBnonneg δ hδ) _)) hMoment
  let U : Ω → ℝ := fun ω => ∫ x, φ x * F (x, ω)
  have hCtest₀ : Ctest₀ = Ctest := by
    dsimp [Ctest₀]
    rw [← hCtestEq]
    exact max_eq_left hCtest
  let F₀ : Ω → ℝ := fun ω => Real.log
    (shfPairing Z (t + δ) T (fun y => heatKernel δ y) (fun _ => 1) ω)
  have hF₀sm : AEStronglyMeasurable F₀ P :=
    by simpa [F₀] using (hpos (t + δ) T δ 0 0 hs hsT hδpos).2.aestronglyMeasurable
  have hF₀abs : Integrable (fun ω => |F₀ ω|) P := by
    have h := (hField1 δ hδ 0).1
    simpa [F₀, Real.rpow_one] using h
  have hF₀int : Integrable F₀ P := by
    apply (integrable_norm_iff hF₀sm).mp
    simpa [Real.norm_eq_abs] using hF₀abs
  let c : ℝ := ∫ ω, F₀ ω ∂P
  have hc : |c| ≤ M1 * B := by
    calc
      |c| = ‖∫ ω, F₀ ω ∂P‖ := by simp [c, Real.norm_eq_abs]
      _ ≤ ∫ ω, ‖F₀ ω‖ ∂P := norm_integral_le_integral_norm _
      _ = ∫ ω, |F₀ ω| ∂P := by simp [Real.norm_eq_abs]
      _ ≤ M1 * B := by simpa [F₀, B, Real.rpow_one] using (hField1 δ hδ 0).2
  have hc' : |c * Kφ| ≤ D * B := by
    dsimp [D, Kφ]
    calc
      |c * ∫ x, φ x| = |c| * |∫ x, φ x| := abs_mul _ _
      _ ≤ (M1 * B) * |∫ x, φ x| :=
        mul_le_mul_of_nonneg_right hc (abs_nonneg _)
      _ = (M1 * |∫ x, φ x|) * B := by ring
  have hMcenter : 0 ≤ Cq := hCq
  have hUbound : ∫ ω, |U ω| ^ q ∂P ≤ Cq * B ^ q := by
    have h := hUqBound
    calc
      ∫ ω, |U ω| ^ q ∂P ≤ Ctest * (Mq * B ^ q) := by
        simpa [U] using h
      _ = Cq * B ^ q := by rw [← hCtest₀]; dsimp [Cq]; ring
  have hCentered := integrable_rpow_sub_const_of_rpow_bound
    P (f := U) (c := c * Kφ) (q := q) (B := B) (M := Cq) (D := D)
    hProd.swap.integral_prod_left.aestronglyMeasurable
    (by linarith : 1 ≤ q) (hBge δ hδ) hMcenter hD
    hUqInt hUbound hc'
  have hsection : ∀ᵐ ω ∂P, Integrable (fun x => φ x * F (x, ω)) :=
    hProd.prod_left_ae
  have hYeq : (fun ω => ∫ x, φ x *
      kpzRegularizedReversed P Z t T δ h₀ x ω) =ᵐ[P]
      fun ω => U ω - c * Kφ := by
    filter_upwards [hsection] with ω hω
    let c₀ : ℝ := ∫ ω', Real.log (shfPairing Z (t + δ) T
      (fun y => heatKernel δ y) (fun _ => 1) ω') ∂P
    have hconst : Integrable (fun x : Plane => φ x * c₀) volume := hKφint.mul_const c₀
    change (∫ x, φ x * (Real.log (shfPairing Z (t + δ) T
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω) - c₀)) =
      (∫ x, φ x * Real.log (shfPairing Z (t + δ) T
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω)) - c₀ * (∫ x, φ x)
    calc
      _ = ∫ x, (φ x * Real.log (shfPairing Z (t + δ) T
          (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω) - φ x * c₀) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by ring
      _ = _ := by
        rw [integral_sub hω hconst, integral_mul_const]
        ring
  have hCenteredBound := hCentered.2
  have hInt : Integrable (fun ω => |U ω - c * Kφ| ^ q) P := hCentered.1
  have hBound : ∫ ω, |U ω - c * Kφ| ^ q ∂P ≤ C * B ^ q := by
    calc
      _ ≤ 2 ^ q * (Cq + D ^ q) * B ^ q := hCenteredBound
      _ = C * B ^ q := by dsimp [C]
  constructor
  · exact (hProd.swap.integral_prod_left.aestronglyMeasurable.sub
      aestronglyMeasurable_const).congr hYeq.symm
  · constructor
    · exact hInt.congr (hYeq.symm.mono fun ω hω =>
        congrArg (fun z : ℝ => |z| ^ q) hω)
    ·
      calc
        ∫ ω, |∫ x, φ x * kpzRegularizedReversed P Z t T δ h₀ x ω| ^ q ∂P =
            ∫ ω, |U ω - c * Kφ| ^ q ∂P := by
          apply integral_congr_ae
          filter_upwards [hYeq] with ω hω
          rw [hω]
        _ ≤ C * B ^ q := hBound

/-- If `|f| ^ q` is integrable with integral at most `M * B ^ q`, then
`‖f‖_{L^q} ≤ (M * B ^ q) ^ (1/q)`. -/
theorem eLpNorm_le_of_integral_abs_rpow_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f : Ω → ℝ} {q M B : ℝ}
    (hq : 0 < q) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hf : AEStronglyMeasurable f P)
    (hint : Integrable (fun ω => |f ω| ^ q) P)
    (hbound : ∫ ω, |f ω| ^ q ∂P ≤ M * B ^ q) :
    eLpNorm f (ENNReal.ofReal q) P ≤ ENNReal.ofReal ((M * B ^ q) ^ (1 / q : ℝ)) := by
  have hp0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.mpr hq).ne'
  have hptop : ENNReal.ofReal q ≠ ⊤ := by simp
  have hnonneg (ω : Ω) : 0 ≤ |f ω| ^ q := Real.rpow_nonneg (abs_nonneg _) _
  have hlin : (∫⁻ ω, ENNReal.ofReal (|f ω| ^ q) ∂P) =
      ENNReal.ofReal (∫ ω, |f ω| ^ q ∂P) :=
    (ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun ω => hnonneg ω)).symm
  have hpower (ω : Ω) : ‖f ω‖ₑ ^ q = ENNReal.ofReal (|f ω| ^ q) := by
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hq.le
  have hMB : 0 ≤ M * B ^ q := mul_nonneg hM (Real.rpow_nonneg hB _)
  calc
    eLpNorm f (ENNReal.ofReal q) P =
        (∫⁻ ω, ‖f ω‖ₑ ^ q ∂P) ^ (1 / q : ℝ) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hf]
      simp only [ENNReal.toReal_ofReal hq.le]
    _ = (ENNReal.ofReal (∫ ω, |f ω| ^ q ∂P)) ^ (1 / q : ℝ) := by
      rw [← hlin]
      congr 1
      apply lintegral_congr
      intro ω
      exact hpower ω
    _ ≤ (ENNReal.ofReal (M * B ^ q)) ^ (1 / q : ℝ) := by
      exact ENNReal.rpow_le_rpow
        (ENNReal.ofReal_le_ofReal hbound) (by positivity)
    _ = ENNReal.ofReal ((M * B ^ q) ^ (1 / q : ℝ)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg hMB (by positivity)]

/-- If each coordinate of `X - Y` has `L²` norm at most `ε`, then `∫ ‖X - Y‖ ≤ k * ε`
for `X, Y` valued in `Fin k → ℝ`. -/
theorem lintegral_norm_pi_sub_le_of_uniform_coordinate_eLpNorm
    {Ω : Type*} [MeasurableSpace Ω] (k : ℕ) (P : Measure Ω)
    [IsProbabilityMeasure P] (X Y : Ω → Fin k → ℝ) {ε : ℝ}
    (hcoord : ∀ i, eLpNorm (fun ω => X ω i - Y ω i) 2 P ≤ ENNReal.ofReal ε) :
    ∫⁻ ω, ENNReal.ofReal ‖X ω - Y ω‖ ∂P ≤
      ENNReal.ofReal ((Fintype.card (Fin k) : ℝ) * ε) := by
  classical
  have hcoordSM (i : Fin k) : AEStronglyMeasurable (fun ω => X ω i - Y ω i) P := by
    apply aestronglyMeasurable_of_eLpNorm_ne_top
    exact (hcoord i).trans_lt ENNReal.ofReal_lt_top |>.ne
  have hcoordL1 (i : Fin k) :
      ∫⁻ ω, ENNReal.ofReal |X ω i - Y ω i| ∂P ≤ ENNReal.ofReal ε := by
    have hL1 : eLpNorm (fun ω => X ω i - Y ω i) 1 P ≤
        eLpNorm (fun ω => X ω i - Y ω i) 2 P :=
      eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
    have hEq : eLpNorm (fun ω => X ω i - Y ω i) 1 P =
        ∫⁻ ω, ENNReal.ofReal |X ω i - Y ω i| ∂P := by
      rw [eLpNorm_one_eq_lintegral_enorm (hcoordSM i)]
      congr 1
      funext ω
      rw [Real.enorm_eq_ofReal_abs]
    exact hEq ▸ hL1.trans (hcoord i)
  have hpoint (ω : Ω) : ‖X ω - Y ω‖ ≤ ∑ i, |X ω i - Y ω i| := by
    rw [pi_norm_le_iff_of_nonneg (x := X ω - Y ω)
      (r := ∑ i, |X ω i - Y ω i|) (by positivity)]
    intro i
    calc
      ‖(X ω - Y ω) i‖ = |X ω i - Y ω i| := by
        simp [Real.norm_eq_abs]
      _ ≤ ∑ j, |X ω j - Y ω j| :=
        Finset.single_le_sum (s := Finset.univ)
          (f := fun j : Fin k => |X ω j - Y ω j|)
          (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have hlintegrand (ω : Ω) :
      ENNReal.ofReal ‖X ω - Y ω‖ ≤ ∑ i, ENNReal.ofReal |X ω i - Y ω i| := by
    calc
      ENNReal.ofReal ‖X ω - Y ω‖ ≤ ENNReal.ofReal (∑ i, |X ω i - Y ω i|) :=
        ENNReal.ofReal_le_ofReal (hpoint ω)
      _ = ∑ i, ENNReal.ofReal |X ω i - Y ω i| := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro i hi
        exact abs_nonneg _
  calc
    ∫⁻ ω, ENNReal.ofReal ‖X ω - Y ω‖ ∂P ≤
        ∫⁻ ω, ∑ i, ENNReal.ofReal |X ω i - Y ω i| ∂P :=
      lintegral_mono fun ω => hlintegrand ω
    _ = ∑ i, ∫⁻ ω, ENNReal.ofReal |X ω i - Y ω i| ∂P := by
      exact lintegral_finsetSum' Finset.univ fun i _ =>
        ENNReal.measurable_ofReal.comp_aemeasurable
          (continuous_abs.measurable.comp_aemeasurable (hcoordSM i).aemeasurable)
    _ ≤ ∑ i, ENNReal.ofReal ε := by
      apply Finset.sum_le_sum
      intro i hi
      exact hcoordL1 i
    _ = ENNReal.ofReal ((Fintype.card (Fin k) : ℝ) * ε) := by
      calc
        ∑ i : Fin k, ENNReal.ofReal ε =
            (Fintype.card (Fin k) : ENNReal) * ENNReal.ofReal ε := by simp
        _ = ENNReal.ofReal ((Fintype.card (Fin k) : ℝ) * ε) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]


end Critical2DKPZ.JointConvergence

end
