/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Smoothing.PolymerLogMomentBounds
public import Critical2DKPZ.Smoothing.ChapmanKolmogorov
public import Critical2DKPZ.OnePoint.FiniteProfileGaussian
public import Critical2DKPZ.Polymer.SmoothedCovariance
public import Critical2DKPZ.MomentBounds.CSZ25Green
public import Critical2DKPZ.Smoothing.Measurability
public import Critical2DKPZ.OnePoint.SecondMoment
public import Critical2DKPZ.Smoothing.GreenApproximation
public import Critical2DKPZ.Smoothing.ProfileL2Perturbation
import Critical2DKPZ.Analysis.Sobolev.HeatMoments
import Critical2DKPZ.FutureProfiles.EndpointTranslation
import Mathlib.Tactic

/-! # Local logarithmic error estimates -/

@[expose] public section

open MeasureTheory Filter
open ProbabilityTheory Set
open scoped Topology ENNReal

namespace Critical2DKPZ.Smoothing

private theorem smoothedP2Plane_translate (β : ℝ) (s n : ℕ) (x : Site) (ω : Disorder) :
    smoothedP2Plane β s n x ω = smoothedP2Plane β s n 0
      (fun p => ω (p.1, p.2 + x)) := by
  let ν : Site → ℝ := fun z => srwKernel s z
  calc
    smoothedP2Plane β s n x ω =
        profileP2Fun β s n (fun w => ν (w - x)) (fun _ => 1) ω := by
          symm
          exact Polymer.profileP2Fun_srw_flat β s n x ω
    _ = profileP2Fun β s n ν (fun _ => 1)
          (fun p => ω (p.1, p.2 + x)) := by
          exact FutureProfiles.profileP2Fun_translate β s n x ν (fun _ => 1) ω
    _ = smoothedP2Plane β s n 0 (fun p => ω (p.1, p.2 + x)) := by
          simpa [ν] using Polymer.profileP2Fun_srw_flat β s n 0 _

private theorem memLp_log_smoothedP2Plane_origin (β : ℝ) (s n : ℕ) :
    MemLp (fun ω => Real.log (smoothedP2Plane β s n 0 ω)) 2 disorderLaw := by
  let ν : Site → ℝ := fun z => srwKernel s z
  let A := Polymer.endpoints 0 s
  have hνA : ∀ z ∉ A, ν z = 0 := by
    intro z hz
    simpa [A, ν] using Polymer.srwKernel_eq_zero_of_not_mem s 0 z hz
  have hν0 : ∀ z, 0 ≤ ν z := fun z => Polymer.kernel_nonneg s z
  have hν1 : ∑ z ∈ A, ν z = 1 := by
    simpa [A, ν] using Polymer.sum_srwKernel_endpoints s 0
  have hdom : integrableExpSet
      (fun ω => Real.log (profileP2Fun β s n ν (fun _ => 1) ω)) disorderLaw = univ := by
    simpa only [ν, A] using
      OnePoint.integrableExpSet_log_profileP2Fun_eq_univ β s n ν A hνA hν0 hν1
  have hmem : MemLp
      (fun ω => Real.log (profileP2Fun β s n ν (fun _ => 1) ω)) 2 disorderLaw := by
    have h0 : 0 ∈ interior
        (integrableExpSet
          (fun ω => Real.log (profileP2Fun β s n ν (fun _ => 1) ω)) disorderLaw) := by
      rw [hdom, interior_univ]
      simp
    exact memLp_of_mem_interior_integrableExpSet h0 2
  have hEq : (fun ω => Real.log (profileP2Fun β s n ν (fun _ => 1) ω)) =
      fun ω => Real.log (smoothedP2Plane β s n 0 ω) := by
    funext ω
    simpa [ν] using congrArg Real.log (Polymer.profileP2Fun_srw_flat β s n 0 ω)
  rw [← hEq]
  exact hmem

private theorem abs_le_sq_add_one (x : ℝ) : |x| ≤ x ^ 2 + 1 := by
  rw [abs_le]
  constructor
  · nlinarith [sq_nonneg (x + 1 / 2)]
  · nlinarith [sq_nonneg (x - 1 / 2)]

/-- A uniformly square-integrable measurable field, paired against an integrable spatial weight,
has an integrable product field and an integrable square of its spatial integral. -/
theorem weighted_field_integrability
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ] [IsProbabilityMeasure μ]
    {Z : Ω → Plane → ℝ} (φ : Plane → ℝ) (hφ : Measurable φ)
    (hφint : Integrable φ) (hZ : Measurable (fun p : Ω × Plane => Z p.1 p.2))
    (hZmem : ∀ x, MemLp (fun ω => Z ω x) 2 μ) (B : ℝ) (_hB : 0 ≤ B)
    (hZsq : ∀ x, Integrable (fun ω => Z ω x ^ 2) μ ∧
      (∫ ω, Z ω x ^ 2 ∂μ) ≤ B) :
    (∀ᵐ ω ∂μ, Integrable (fun x => φ x * Z ω x)) ∧
    Integrable (fun p : Ω × (Plane × Plane) =>
      (φ p.2.1 * Z p.1 p.2.1) * (φ p.2.2 * Z p.1 p.2.2))
      (μ.prod (volume.prod volume)) ∧
    Integrable (fun ω => (∫ x, φ x * Z ω x) ^ 2) μ := by
  have habsφ : Integrable (fun x => |φ x|) := by
    simpa only [Real.norm_eq_abs] using hφint.norm
  have hX : Measurable (fun p : Ω × Plane => φ p.2 * Z p.1 p.2) :=
    (hφ.comp measurable_snd).mul hZ
  have hXnorm : Measurable (fun p : Ω × Plane => ‖φ p.2 * Z p.1 p.2‖) := hX.norm
  have hXint : ∀ x, Integrable (fun ω => φ x * Z ω x) μ := by
    intro x
    have hZint : Integrable (fun ω => Z ω x) μ := (hZmem x).integrable (by norm_num)
    simpa [smul_eq_mul, mul_comm] using hZint.const_mul (φ x)
  have hXintnorm (x : Plane) :
      ∫ ω, ‖φ x * Z ω x‖ ∂μ ≤ |φ x| * (B + 1) := by
    have hZx : Measurable (fun ω => Z ω x) :=
      hZ.comp (measurable_id.prodMk measurable_const)
    have hZabs : Integrable (fun ω => |Z ω x|) μ := by
      have hmajor : Integrable (fun ω => Z ω x ^ 2 + 1) μ :=
        (hZsq x).1.add (integrable_const 1)
      have hmeas : AEStronglyMeasurable (fun ω => |Z ω x|) μ := hZx.abs.aestronglyMeasurable
      refine hmajor.mono' hmeas ?_
      filter_upwards [] with ω
      simpa only [Real.norm_eq_abs, abs_abs] using
        abs_le_sq_add_one (Z ω x)
    have hZbound : (∫ ω, |Z ω x| ∂μ) ≤ B + 1 := by
      calc
        _ ≤ ∫ ω, Z ω x ^ 2 + 1 ∂μ := by
          apply integral_mono hZabs ((hZsq x).1.add (integrable_const 1))
          intro ω
          exact abs_le_sq_add_one (Z ω x)
        _ = (∫ ω, Z ω x ^ 2 ∂μ) + 1 := by
          rw [integral_add ((hZsq x).1) (integrable_const 1)]
          simp
        _ ≤ B + 1 := add_le_add (hZsq x).2 le_rfl
    calc
      _ = |φ x| * ∫ ω, |Z ω x| ∂μ := by
        simp_rw [Real.norm_eq_abs, abs_mul]
        rw [integral_const_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hZbound (abs_nonneg _)
  have hXnormStrong : StronglyMeasurable
      (fun p : Ω × Plane => ‖φ p.2 * Z p.1 p.2‖) := hXnorm.stronglyMeasurable
  have hXnormAverageMeas : StronglyMeasurable
      (fun x : Plane => ∫ ω, ‖φ x * Z ω x‖ ∂μ) := by
    simpa only [Function.uncurry_apply_pair] using hXnormStrong.integral_prod_left'
  have hXnormMajor : Integrable (fun x : Plane => |φ x| * (B + 1)) :=
    by simpa [mul_comm] using habsφ.const_mul (B + 1)
  have hXnormAverageInt : Integrable
      (fun x : Plane => ∫ ω, ‖φ x * Z ω x‖ ∂μ) := by
    refine hXnormMajor.mono' hXnormAverageMeas.aestronglyMeasurable ?_
    filter_upwards [] with x
    have hnonneg : 0 ≤ ∫ ω, ‖φ x * Z ω x‖ ∂μ := integral_nonneg fun _ => norm_nonneg _
    rw [Real.norm_of_nonneg hnonneg]
    exact hXintnorm x
  have hXprod1 : Integrable (fun p : Ω × Plane => φ p.2 * Z p.1 p.2)
      (μ.prod volume) := by
    apply (integrable_prod_iff' hX.aestronglyMeasurable).2
    constructor
    · exact Filter.Eventually.of_forall hXint
    · exact hXnormAverageInt
  have hXintAE := hXprod1.prod_right_ae
  have hXpair : Measurable (fun p : Ω × (Plane × Plane) =>
      (φ p.2.1 * Z p.1 p.2.1) * (φ p.2.2 * Z p.1 p.2.2)) := by
    exact (hX.comp (measurable_fst.prodMk measurable_snd.fst)).mul
      (hX.comp (measurable_fst.prodMk measurable_snd.snd))
  have hXpairSection (p : Plane × Plane) :
      Integrable (fun ω => (φ p.1 * Z ω p.1) * (φ p.2 * Z ω p.2)) μ := by
    have hholder : ENNReal.HolderTriple (ENNReal.ofReal (2 : ℝ))
        (ENNReal.ofReal (2 : ℝ)) 1 := Real.HolderConjugate.two_two.ennrealOfReal
    have hleft : MemLp (fun ω => φ p.1 * Z ω p.1) (ENNReal.ofReal (2 : ℝ)) μ := by
      simpa [mul_comm] using (hZmem p.1).const_mul (φ p.1)
    have hright : MemLp (fun ω => φ p.2 * Z ω p.2) (ENNReal.ofReal (2 : ℝ)) μ := by
      simpa [mul_comm] using (hZmem p.2).const_mul (φ p.2)
    have hprod : MemLp
        (fun ω => (φ p.1 * Z ω p.1) * (φ p.2 * Z ω p.2)) 1 μ := by
      simpa only [ENNReal.ofReal_ofNat, mul_comm] using hleft.fun_mul hright
    exact hprod.integrable (by norm_num)
  have hXpairNormMeas : Measurable (fun p : Ω × (Plane × Plane) =>
      ‖(φ p.2.1 * Z p.1 p.2.1) * (φ p.2.2 * Z p.1 p.2.2)‖) := hXpair.norm
  have hXpairMoment (p : Plane × Plane) :
      ∫ ω, ‖(φ p.1 * Z ω p.1) * (φ p.2 * Z ω p.2)‖ ∂μ ≤
        |φ p.1| * |φ p.2| * B := by
    have hleft := (hZsq p.1).1
    have hright := (hZsq p.2).1
    have hmajor : Integrable (fun ω => |φ p.1| * |φ p.2| *
        ((Z ω p.1 ^ 2 + Z ω p.2 ^ 2) / 2)) μ := by
      exact ((hleft.add hright).div_const 2).const_mul
        (|φ p.1| * |φ p.2|)
    have hpt (ω : Ω) :
        ‖(φ p.1 * Z ω p.1) * (φ p.2 * Z ω p.2)‖ ≤
          |φ p.1| * |φ p.2| * ((Z ω p.1 ^ 2 + Z ω p.2 ^ 2) / 2) := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have hzz : |Z ω p.1 * Z ω p.2| ≤
          (Z ω p.1 ^ 2 + Z ω p.2 ^ 2) / 2 := by
        rw [abs_mul]
        nlinarith [sq_nonneg (|Z ω p.1| - |Z ω p.2|),
          sq_abs (Z ω p.1), sq_abs (Z ω p.2)]
      calc
        |φ p.1| * |Z ω p.1| * |φ p.2 * Z ω p.2| =
            |φ p.1| * |φ p.2| * |Z ω p.1 * Z ω p.2| := by
              simp only [abs_mul]
              ring
        _ ≤ |φ p.1| * |φ p.2| * ((Z ω p.1 ^ 2 + Z ω p.2 ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left hzz (by positivity)
    calc
      _ ≤ ∫ ω, |φ p.1| * |φ p.2| *
          ((Z ω p.1 ^ 2 + Z ω p.2 ^ 2) / 2) ∂μ :=
            integral_mono ((hXpairSection p).norm) hmajor hpt
      _ = |φ p.1| * |φ p.2| *
          (((∫ ω, Z ω p.1 ^ 2 ∂μ) + (∫ ω, Z ω p.2 ^ 2 ∂μ)) / 2) := by
            simp_rw [integral_const_mul, integral_div, integral_add hleft hright]
      _ ≤ |φ p.1| * |φ p.2| * ((B + B) / 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply div_le_div_of_nonneg_right
              (add_le_add (hZsq p.1).2 (hZsq p.2).2) (by norm_num)
      _ = |φ p.1| * |φ p.2| * B := by ring
  have hXpairMomentMeas : StronglyMeasurable
      (fun p : Plane × Plane =>
        ∫ ω, ‖(φ p.1 * Z ω p.1) * (φ p.2 * Z ω p.2)‖ ∂μ) := by
    simpa only [Function.uncurry_apply_pair] using hXpairNormMeas.stronglyMeasurable.integral_prod_left'
  have hXpairMajor : Integrable
      (fun p : Plane × Plane => |φ p.1| * |φ p.2| * B) (volume.prod volume) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (habsφ.mul_prod habsφ).const_mul B
  have hXpairNormInt : Integrable
      (fun p : Plane × Plane =>
        ∫ ω, ‖(φ p.1 * Z ω p.1) * (φ p.2 * Z ω p.2)‖ ∂μ) (volume.prod volume) := by
    refine hXpairMajor.mono' hXpairMomentMeas.aestronglyMeasurable ?_
    filter_upwards [] with p
    have hnonneg : 0 ≤ ∫ ω, ‖(φ p.1 * Z ω p.1) * (φ p.2 * Z ω p.2)‖ ∂μ :=
      integral_nonneg fun _ => norm_nonneg _
    rw [Real.norm_of_nonneg hnonneg]
    exact hXpairMoment p
  have hXpairProd : Integrable
      (fun p : Ω × (Plane × Plane) =>
        (φ p.2.1 * Z p.1 p.2.1) * (φ p.2.2 * Z p.1 p.2.2))
      (μ.prod (volume.prod volume)) := by
    apply (integrable_prod_iff' hXpair.aestronglyMeasurable).2
    exact ⟨Filter.Eventually.of_forall hXpairSection, hXpairNormInt⟩
  have hGint : Integrable
      (fun ω => ∫ p : Plane × Plane,
        ‖(φ p.1 * Z ω p.1) * (φ p.2 * Z ω p.2)‖ ∂volume.prod volume) μ :=
    hXpairProd.norm.integral_prod_left
  have hFstrong : StronglyMeasurable (fun ω => ∫ x, φ x * Z ω x) := by
    simpa only [Function.uncurry_apply_pair] using hX.stronglyMeasurable.integral_prod_right'
  have hFsq : Integrable (fun ω => (∫ x, φ x * Z ω x) ^ 2) μ := by
    refine hGint.mono' (hFstrong.pow 2).aestronglyMeasurable ?_
    filter_upwards [hXintAE] with ω hω
    have hprodInt : Integrable
        (fun p : Plane × Plane => (φ p.1 * Z ω p.1) * (φ p.2 * Z ω p.2))
        (volume.prod volume) := hω.mul_prod hω
    have heq : (∫ x, φ x * Z ω x) ^ 2 =
        ∫ p : Plane × Plane, (φ p.1 * Z ω p.1) * (φ p.2 * Z ω p.2)
          ∂volume.prod volume := by
      rw [pow_two]
      exact (integral_prod_mul (μ := (volume : Measure Plane)) (ν := volume)
        (fun x => φ x * Z ω x) (fun x => φ x * Z ω x)).symm
    calc
      ‖(∫ x, φ x * Z ω x) ^ 2‖ =
          ‖∫ p : Plane × Plane,
            (φ p.1 * Z ω p.1) * (φ p.2 * Z ω p.2) ∂volume.prod volume‖ := by
              rw [heq]
      _ ≤ ∫ p : Plane × Plane,
          ‖(φ p.1 * Z ω p.1) * (φ p.2 * Z ω p.2)‖ ∂volume.prod volume :=
            norm_integral_le_integral_norm _
  refine ⟨hXintAE, ?_, hFsq⟩
  exact (integrable_prod_iff' hXpair.aestronglyMeasurable).2
    ⟨Filter.Eventually.of_forall hXpairSection, hXpairNormInt⟩

/-- Logarithms of smoothed partition functions have finite second moments, at every starting site
(the proof reduces to the origin by spatial translation). -/
theorem memLp_log_smoothedP2Plane (β : ℝ) (s n : ℕ) (x : Site) :
    MemLp (fun ω => Real.log (smoothedP2Plane β s n x ω)) 2 disorderLaw := by
  let shift : Disorder → Disorder := fun ω p => ω (p.1, p.2 + x)
  have h0 := memLp_log_smoothedP2Plane_origin β s n
  have hshift := FutureProfiles.measurePreserving_disorderShift x
  have hEq : (fun ω => Real.log (smoothedP2Plane β s n x ω)) =
      fun ω => Real.log (smoothedP2Plane β s n 0 (shift ω)) := by
    funext ω
    exact congrArg Real.log (smoothedP2Plane_translate β s n x ω)
  rw [hEq]
  exact (eLpNorm_comp_measurePreserving h0.aestronglyMeasurable hshift).trans_lt h0

private noncomputable def centeredLogSmoothed (β : ℝ) (s n : ℕ) (x : Site) (ω : Disorder) : ℝ :=
  Real.log (smoothedP2Plane β s n x ω) -
    ∫ ω', Real.log (smoothedP2Plane β s n x ω') ∂disorderLaw

private def disorderShift (x : Site) (ω : Disorder) : Disorder :=
  fun p => ω (p.1, p.2 + x)

private theorem measurableEmbedding_disorderShift (x : Site) :
    MeasurableEmbedding (disorderShift x) := by
  let τeq : Disorder ≃ᵐ Disorder :=
    MeasurableEquiv.piCongrLeft (fun _ : ℕ × Site => ℝ)
      (Gaussian.spatialTranslation x).symm
  have hτeq : disorderShift x = τeq := by
    funext ω p
    simp [disorderShift, τeq, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
      Gaussian.spatialTranslation]
  rw [hτeq]
  exact τeq.measurableEmbedding

private theorem integral_log_smoothedP2Plane_eq_origin (β : ℝ) (s n : ℕ) (x : Site) :
    (∫ ω, Real.log (smoothedP2Plane β s n x ω) ∂disorderLaw) =
      ∫ ω, Real.log (smoothedP2Plane β s n 0 ω) ∂disorderLaw := by
  have hMP := FutureProfiles.measurePreserving_disorderShift x
  calc
    _ = ∫ ω, Real.log (smoothedP2Plane β s n 0 (disorderShift x ω)) ∂disorderLaw := by
      apply integral_congr_ae
      filter_upwards [] with ω
      exact congrArg Real.log (smoothedP2Plane_translate β s n x ω)
    _ = _ := hMP.integral_comp (measurableEmbedding_disorderShift x)
      (fun ω : Disorder => Real.log (smoothedP2Plane β s n 0 ω))

private theorem centeredLogSmoothed_translate (β : ℝ) (s n : ℕ) (x : Site)
    (ω : Disorder) :
    centeredLogSmoothed β s n x ω =
      centeredLogSmoothed β s n 0 (disorderShift x ω) := by
  change (Real.log (smoothedP2Plane β s n x ω) -
      ∫ ω', Real.log (smoothedP2Plane β s n x ω') ∂disorderLaw) =
    (Real.log (smoothedP2Plane β s n 0 (disorderShift x ω)) -
      ∫ ω', Real.log (smoothedP2Plane β s n 0 ω') ∂disorderLaw)
  rw [smoothedP2Plane_translate β s n x ω,
    integral_log_smoothedP2Plane_eq_origin β s n x]
  have hshift : (fun p : ℕ × Site => ω (p.1, p.2 + x)) = disorderShift x ω := rfl
  rw [hshift]

private theorem centered_log_smoothed_field_data (β : ℝ) (s n N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧
      Measurable (fun p : Disorder × Plane =>
        centeredLogSmoothed β s n (latticePoint N p.2) p.1) ∧
      (∀ x : Plane, MemLp
        (fun ω => centeredLogSmoothed β s n (latticePoint N x) ω) 2 disorderLaw) ∧
      (∀ x : Plane,
        Integrable (fun ω => centeredLogSmoothed β s n (latticePoint N x) ω ^ 2) disorderLaw ∧
        (∫ ω, centeredLogSmoothed β s n (latticePoint N x) ω ^ 2 ∂disorderLaw) ≤ B) := by
  let μ₀ := ∫ ω, Real.log (smoothedP2Plane β s n 0 ω) ∂disorderLaw
  let Z₀ : Disorder → ℝ := fun ω => Real.log (smoothedP2Plane β s n 0 ω) - μ₀
  let B := ∫ ω, Z₀ ω ^ 2 ∂disorderLaw
  have hlog0 := memLp_log_smoothedP2Plane β s n 0
  have hZ₀mem : MemLp Z₀ 2 disorderLaw := by
    change MemLp (fun ω => Real.log (smoothedP2Plane β s n 0 ω) - μ₀) 2 disorderLaw
    exact hlog0.sub (memLp_const μ₀)
  have hZ₀sq : Integrable (fun ω => Z₀ ω ^ 2) disorderLaw :=
    (memLp_two_iff_integrable_sq hZ₀mem.aestronglyMeasurable).1 hZ₀mem
  have hB : 0 ≤ B := by
    dsimp [B]
    exact integral_nonneg fun ω => sq_nonneg (Z₀ ω)
  have hlogJoint : Measurable
      (fun p : Disorder × Plane =>
        Real.log (smoothedP2Plane β s n (latticePoint N p.2) p.1)) := by
    have hν (w : Site) : Measurable (fun p : Disorder × Plane =>
        srwKernel s (w - latticePoint N p.2)) := by
      exact (measurable_of_countable fun z : Site => srwKernel s (w - z)).comp
        ((measurable_latticePoint N).comp measurable_snd)
    have hprofile := measurable_profileP2Fun_param β s n (fun _ : Site => 1)
      hν measurable_fst
    have hEq : (fun p : Disorder × Plane =>
        smoothedP2Plane β s n (latticePoint N p.2) p.1) =
        (fun p => profileP2Fun β s n
          (fun w => srwKernel s (w - latticePoint N p.2)) (fun _ => 1) p.1) := by
      funext p
      exact (Polymer.profileP2Fun_srw_flat β s n (latticePoint N p.2) p.1).symm
    have hEqLog : (fun p : Disorder × Plane =>
        Real.log (smoothedP2Plane β s n (latticePoint N p.2) p.1)) =
        fun p => Real.log (profileP2Fun β s n
          (fun w => srwKernel s (w - latticePoint N p.2)) (fun _ => 1) p.1) := by
      funext p
      exact congrArg Real.log (congrFun hEq p)
    exact hEqLog ▸ Real.measurable_log.comp hprofile
  have hjoint : Measurable (fun p : Disorder × Plane =>
      centeredLogSmoothed β s n (latticePoint N p.2) p.1) := by
    have hEq : (fun p : Disorder × Plane =>
        centeredLogSmoothed β s n (latticePoint N p.2) p.1) =
        fun p => Real.log (smoothedP2Plane β s n (latticePoint N p.2) p.1) - μ₀ := by
      funext p
      dsimp [centeredLogSmoothed, μ₀]
      rw [integral_log_smoothedP2Plane_eq_origin]
    rw [hEq]
    exact hlogJoint.sub_const μ₀
  refine ⟨B, hB, hjoint, ?_, ?_⟩
  · intro x
    let z := latticePoint N x
    have hEq : (fun ω => centeredLogSmoothed β s n z ω) = fun ω => Z₀ (disorderShift z ω) := by
      funext ω
      simpa [Z₀, μ₀, centeredLogSmoothed] using centeredLogSmoothed_translate β s n z ω
    rw [hEq]
    exact hZ₀mem.comp_measurePreserving (FutureProfiles.measurePreserving_disorderShift z)
  · intro x
    let z := latticePoint N x
    have hmem := (show MemLp (fun ω => centeredLogSmoothed β s n z ω) 2 disorderLaw from
      by
        have hEq : (fun ω => centeredLogSmoothed β s n z ω) = fun ω => Z₀ (disorderShift z ω) := by
          funext ω
          simpa [Z₀, μ₀, centeredLogSmoothed] using centeredLogSmoothed_translate β s n z ω
        rw [hEq]
        exact hZ₀mem.comp_measurePreserving (FutureProfiles.measurePreserving_disorderShift z))
    have hsqInt : Integrable (fun ω => centeredLogSmoothed β s n z ω ^ 2) disorderLaw :=
      (memLp_two_iff_integrable_sq hmem.aestronglyMeasurable).1 hmem
    have hsqEq : (∫ ω, centeredLogSmoothed β s n z ω ^ 2 ∂disorderLaw) = B := by
      have hEq : (fun ω => centeredLogSmoothed β s n z ω ^ 2) =
          fun ω => Z₀ (disorderShift z ω) ^ 2 := by
        funext ω
        simpa [Z₀, μ₀, centeredLogSmoothed] using
          congrArg (fun u : ℝ => u ^ 2) (centeredLogSmoothed_translate β s n z ω)
      rw [hEq]
      dsimp [B]
      exact (FutureProfiles.measurePreserving_disorderShift z).integral_comp
        (measurableEmbedding_disorderShift z) (fun ω => Z₀ ω ^ 2)
    exact ⟨hsqInt, hsqEq.le⟩

private theorem covariance_log_smoothed_le_truncatedGreen (β : ℝ) (hβ : 0 ≤ β)
    (s n : ℕ) (hsn : s ≤ n) (x y : Site) (C D Dx Dy : ℝ)
    (hC : 0 ≤ C) (hD : 0 < D)
    (hcoeff : ∀ r ∈ Finset.Icc (s + 1) n,
      Polymer.sigmaSq β *
          ∫ ω, pointToPlane β 0 (n - r) 0 ω ^ 2 ∂disorderLaw ≤ C / D)
    (hDx : gaussianityDefect disorderLaw
        (fun ω => Real.log (smoothedP2Plane β s n x ω)) ≤ Dx)
    (hDy : gaussianityDefect disorderLaw
        (fun ω => Real.log (smoothedP2Plane β s n y ω)) ≤ Dy) :
    ProbabilityTheory.covariance
        (fun ω => Real.log (smoothedP2Plane β s n x ω))
        (fun ω => Real.log (smoothedP2Plane β s n y ω)) disorderLaw ≤
      (C / D) * MomentBounds.truncatedGreen n (y - x) + Dx + Dy := by
  have hcov := covariance_log_smoothedP2Plane_le hβ s n x y
  have hXmem := Polymer.memLp_smoothedP2Plane β s n x 2 (by norm_num)
  have hYmem := Polymer.memLp_smoothedP2Plane β s n y 2 (by norm_num)
  have hXmean := Polymer.integral_smoothedP2Plane β s n x
  have hYmean := Polymer.integral_smoothedP2Plane β s n y
  have hcovEq : ProbabilityTheory.covariance
      (fun ω => smoothedP2Plane β s n x ω)
      (fun ω => smoothedP2Plane β s n y ω) disorderLaw =
      (∫ ω, smoothedP2Plane β s n x ω * smoothedP2Plane β s n y ω
        ∂disorderLaw) - 1 := by
    calc
      _ = (∫ ω, smoothedP2Plane β s n x ω * smoothedP2Plane β s n y ω
            ∂disorderLaw) -
          (∫ ω, smoothedP2Plane β s n x ω ∂disorderLaw) *
            (∫ ω, smoothedP2Plane β s n y ω ∂disorderLaw) :=
          ProbabilityTheory.covariance_eq_sub hXmem hYmem
      _ = _ := by rw [hXmean, hYmean]; ring
  have hreplica := Polymer.local_replica_formula β s n hsn x y
  have hσ : 0 ≤ Polymer.sigmaSq β := by
    unfold Polymer.sigmaSq
    exact sub_nonneg.mpr (Real.one_le_exp (sq_nonneg β))
  have hsumNonneg : 0 ≤ ∑ r ∈ Finset.Icc (s + 1) n,
      srwKernel (2 * r) (y - x) * Polymer.sigmaSq β *
        (∫ ω, pointToPlane β 0 (n - r) 0 ω ^ 2 ∂disorderLaw) :=
    Finset.sum_nonneg fun r hr =>
      mul_nonneg (mul_nonneg (Polymer.kernel_nonneg (2 * r) (y - x)) hσ)
        (integral_nonneg fun ω => sq_nonneg _)
  have hprodLower : 1 ≤ ∫ ω, smoothedP2Plane β s n x ω *
      smoothedP2Plane β s n y ω ∂disorderLaw := by
    linarith [hreplica, hsumNonneg]
  have hprodPos : 0 < ∫ ω, smoothedP2Plane β s n x ω *
      smoothedP2Plane β s n y ω ∂disorderLaw := lt_of_lt_of_le zero_lt_one hprodLower
  have hlog : Real.log (∫ ω, smoothedP2Plane β s n x ω *
      smoothedP2Plane β s n y ω ∂disorderLaw) ≤
        (∫ ω, smoothedP2Plane β s n x ω * smoothedP2Plane β s n y ω
          ∂disorderLaw) - 1 :=
    Real.log_le_sub_one_of_pos hprodPos
  have hsum : ∑ r ∈ Finset.Icc (s + 1) n,
      srwKernel (2 * r) (y - x) * Polymer.sigmaSq β *
        (∫ ω, pointToPlane β 0 (n - r) 0 ω ^ 2 ∂disorderLaw) ≤
      (C / D) * MomentBounds.truncatedGreen n (y - x) := by
    have hratio : 0 ≤ C / D := div_nonneg hC hD.le
    calc
      _ ≤ ∑ r ∈ Finset.Icc (s + 1) n,
          srwKernel (2 * r) (y - x) * (C / D) := by
            apply Finset.sum_le_sum
            intro r hr
            have hk := hcoeff r hr
            have hkernel : 0 ≤ srwKernel (2 * r) (y - x) :=
              Polymer.kernel_nonneg (2 * r) (y - x)
            calc
              srwKernel (2 * r) (y - x) * Polymer.sigmaSq β *
                  (∫ ω, pointToPlane β 0 (n - r) 0 ω ^ 2 ∂disorderLaw) =
                srwKernel (2 * r) (y - x) *
                  (Polymer.sigmaSq β *
                    ∫ ω, pointToPlane β 0 (n - r) 0 ω ^ 2 ∂disorderLaw) := by ring
              _ ≤ srwKernel (2 * r) (y - x) * (C / D) :=
                  mul_le_mul_of_nonneg_left hk hkernel
      _ = (C / D) * ∑ r ∈ Finset.Icc (s + 1) n,
          srwKernel (2 * r) (y - x) := by rw [← Finset.sum_mul]; ring
      _ ≤ (C / D) * ∑ r ∈ Finset.Icc 1 n,
          srwKernel (2 * r) (y - x) := by
            apply mul_le_mul_of_nonneg_left _ hratio
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro r hr
              exact Finset.mem_Icc.mpr ⟨by
                have := (Finset.mem_Icc.mp hr).1
                omega, (Finset.mem_Icc.mp hr).2⟩
            · intro r hr _
              exact Polymer.kernel_nonneg (2 * r) (y - x)
      _ = (C / D) * MomentBounds.truncatedGreen n (y - x) := by
            simp [MomentBounds.truncatedGreen]
  calc
    _ ≤ Real.log (∫ ω, smoothedP2Plane β s n x ω *
          smoothedP2Plane β s n y ω ∂disorderLaw) +
          gaussianityDefect disorderLaw
            (fun ω => Real.log (smoothedP2Plane β s n x ω)) +
          gaussianityDefect disorderLaw
            (fun ω => Real.log (smoothedP2Plane β s n y ω)) := hcov.2
    _ ≤ ((∫ ω, smoothedP2Plane β s n x ω * smoothedP2Plane β s n y ω
          ∂disorderLaw) - 1) + Dx + Dy := by
            exact add_le_add (add_le_add hlog hDx) hDy
    _ = (∑ r ∈ Finset.Icc (s + 1) n,
          srwKernel (2 * r) (y - x) * Polymer.sigmaSq β *
            (∫ ω, pointToPlane β 0 (n - r) 0 ω ^ 2 ∂disorderLaw)) + Dx + Dy := by
            rw [← hreplica]
    _ ≤ _ := by
      calc
        _ = (∑ r ∈ Finset.Icc (s + 1) n,
              srwKernel (2 * r) (y - x) * Polymer.sigmaSq β *
                (∫ ω, pointToPlane β 0 (n - r) 0 ω ^ 2 ∂disorderLaw)) + (Dx + Dy) := by ring
        _ ≤ (C / D) * MomentBounds.truncatedGreen n (y - x) + (Dx + Dy) :=
          add_le_add hsum le_rfl
        _ = _ := by ring


private theorem integral_sq_centered_field_eq_covariance
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ] [IsProbabilityMeasure μ]
    {X : Ω → Plane → ℝ}
    (hXint : ∀ᵐ ω ∂μ, Integrable (X ω))
    (hXprod : Integrable (fun p : Ω × (Plane × Plane) =>
      X p.1 p.2.1 * X p.1 p.2.2) (μ.prod (volume.prod volume)))
    (hX2 : ∀ x : Plane, MemLp (fun ω => X ω x) 2 μ)
    (hzero : ∀ x : Plane, ∫ ω, X ω x ∂μ = 0) :
    Integrable (fun p : Plane × Plane =>
      ∫ ω, X ω p.1 * X ω p.2 ∂μ) (volume.prod volume) ∧
    (∫ ω, (∫ x : Plane, X ω x) ^ 2 ∂μ) =
      ∫ p : Plane × Plane, ProbabilityTheory.covariance
        (fun ω => X ω p.1) (fun ω => X ω p.2) μ ∂volume.prod volume := by
  have hswap := integral_integral_swap
    (f := fun (ω : Ω) (p : Plane × Plane) => X ω p.1 * X ω p.2) hXprod
  have hcov (p : Plane × Plane) :
      (∫ ω, X ω p.1 * X ω p.2 ∂μ) =
        ProbabilityTheory.covariance (fun ω => X ω p.1) (fun ω => X ω p.2) μ := by
    rw [ProbabilityTheory.covariance_eq_sub (hX2 p.1) (hX2 p.2), hzero p.1, hzero p.2]
    simp
  have hpoint : ∀ᵐ ω ∂μ,
      (∫ x : Plane, X ω x) ^ 2 =
        ∫ p : Plane × Plane, X ω p.1 * X ω p.2 ∂volume.prod volume := by
    filter_upwards [hXint] with ω hω
    rw [pow_two]
    exact (integral_prod_mul (μ := (volume : Measure Plane)) (ν := volume)
      (X ω) (X ω)).symm
  have hfirst :
      (∫ ω, (∫ x : Plane, X ω x) ^ 2 ∂μ) =
        ∫ ω, ∫ p : Plane × Plane, X ω p.1 * X ω p.2 ∂volume.prod volume ∂μ := by
    exact integral_congr_ae hpoint
  have hsecond :
      (∫ ω, ∫ p : Plane × Plane, X ω p.1 * X ω p.2 ∂volume.prod volume ∂μ) =
        ∫ p : Plane × Plane, ∫ ω, X ω p.1 * X ω p.2 ∂μ ∂volume.prod volume := by
    simpa only [Pi.mul_apply] using hswap
  refine ⟨?_, ?_⟩
  · exact hXprod.integral_prod_right
  · calc
      _ = ∫ ω, ∫ p : Plane × Plane,
            X ω p.1 * X ω p.2 ∂volume.prod volume ∂μ := hfirst
      _ = ∫ p : Plane × Plane, ∫ ω, X ω p.1 * X ω p.2 ∂μ
            ∂volume.prod volume := hsecond
      _ = ∫ p : Plane × Plane,
            ProbabilityTheory.covariance (fun ω => X ω p.1) (fun ω => X ω p.2) μ
            ∂volume.prod volume := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall hcov

/-- The square integral of a centered spatial pairing is bounded by an integrable pointwise
covariance majorant. -/
theorem integral_sq_centered_field_le_of_covariance
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ] [IsProbabilityMeasure μ]
    {X : Ω → Plane → ℝ} (K : Plane × Plane → ℝ)
    (hXint : ∀ᵐ ω ∂μ, Integrable (X ω))
    (hXprod : Integrable (fun p : Ω × (Plane × Plane) =>
      X p.1 p.2.1 * X p.1 p.2.2) (μ.prod (volume.prod volume)))
    (hX2 : ∀ x : Plane, MemLp (fun ω => X ω x) 2 μ)
    (hzero : ∀ x : Plane, ∫ ω, X ω x ∂μ = 0)
    (hcov : ∀ p : Plane × Plane,
      ProbabilityTheory.covariance (fun ω => X ω p.1) (fun ω => X ω p.2) μ ≤ K p)
    (hK : Integrable K (volume.prod volume)) :
    (∫ ω, (∫ x : Plane, X ω x) ^ 2 ∂μ) ≤
      ∫ p : Plane × Plane, K p ∂volume.prod volume := by
  obtain ⟨hcovInt, heq⟩ := integral_sq_centered_field_eq_covariance μ hXint
    hXprod hX2 hzero
  have hcovEq (p : Plane × Plane) :
      (∫ ω, X ω p.1 * X ω p.2 ∂μ) =
        ProbabilityTheory.covariance (fun ω => X ω p.1) (fun ω => X ω p.2) μ := by
    rw [ProbabilityTheory.covariance_eq_sub (hX2 p.1) (hX2 p.2), hzero p.1, hzero p.2]
    simp
  have hcovInt' : Integrable (fun p : Plane × Plane =>
      ProbabilityTheory.covariance (fun ω => X ω p.1) (fun ω => X ω p.2) μ)
      (volume.prod volume) :=
    hcovInt.congr (Filter.Eventually.of_forall fun p => by
      change (∫ ω, X ω p.1 * X ω p.2 ∂μ) =
        ProbabilityTheory.covariance (fun ω => X ω p.1) (fun ω => X ω p.2) μ
      exact hcovEq p)
  rw [heq]
  exact integral_mono hcovInt' hK hcov

private theorem covariance_mul_mul_le_abs_mul_abs_of_nonneg
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X Y : Ω → ℝ) (a b B : ℝ)
    (hcov0 : 0 ≤ ProbabilityTheory.covariance X Y μ)
    (hcovB : ProbabilityTheory.covariance X Y μ ≤ B) :
    ProbabilityTheory.covariance (fun ω => a * X ω) (fun ω => b * Y ω) μ ≤
      |a| * |b| * B := by
  rw [ProbabilityTheory.covariance_const_mul_left,
    ProbabilityTheory.covariance_const_mul_right]
  calc
    a * (b * ProbabilityTheory.covariance X Y μ) =
        (a * b) * ProbabilityTheory.covariance X Y μ := by ring
    _ ≤ (|a| * |b|) * ProbabilityTheory.covariance X Y μ := by
      apply mul_le_mul_of_nonneg_right _ hcov0
      calc
        a * b ≤ |a * b| := le_abs_self _
        _ = |a| * |b| := abs_mul _ _
    _ ≤ (|a| * |b|) * B := by
      exact mul_le_mul_of_nonneg_left hcovB (by positivity)
    _ = |a| * |b| * B := by ring

private theorem covariance_centered_weighted_smoothed_le_truncatedGreen
    (β : ℝ) (hβ : 0 ≤ β) (s n : ℕ) (hsn : s ≤ n) (x y : Site)
    (C D Dx Dy : ℝ) (hC : 0 ≤ C) (hD : 0 < D)
    (hcoeff : ∀ r ∈ Finset.Icc (s + 1) n,
      Polymer.sigmaSq β *
          ∫ ω, pointToPlane β 0 (n - r) 0 ω ^ 2 ∂disorderLaw ≤ C / D)
    (hDx : gaussianityDefect disorderLaw
        (fun ω => Real.log (smoothedP2Plane β s n x ω)) ≤ Dx)
    (hDy : gaussianityDefect disorderLaw
        (fun ω => Real.log (smoothedP2Plane β s n y ω)) ≤ Dy)
    (ha : Integrable (fun ω => Real.log (smoothedP2Plane β s n x ω)) disorderLaw)
    (hb : Integrable (fun ω => Real.log (smoothedP2Plane β s n y ω)) disorderLaw)
    (a b : ℝ) :
    ProbabilityTheory.covariance
        (fun ω => a * (Real.log (smoothedP2Plane β s n x ω) -
          ∫ ω', Real.log (smoothedP2Plane β s n x ω') ∂disorderLaw))
        (fun ω => b * (Real.log (smoothedP2Plane β s n y ω) -
          ∫ ω', Real.log (smoothedP2Plane β s n y ω') ∂disorderLaw)) disorderLaw ≤
      |a| * |b| * ((C / D) * MomentBounds.truncatedGreen n (y - x) + Dx + Dy) := by
  have hcov := covariance_log_smoothed_le_truncatedGreen β hβ s n hsn x y C D Dx Dy hC hD
    hcoeff hDx hDy
  have hcov0 := covariance_log_smoothedP2Plane_le hβ s n x y
  have hcenter :
      ProbabilityTheory.covariance
          (fun ω => a * (Real.log (smoothedP2Plane β s n x ω) -
            ∫ ω', Real.log (smoothedP2Plane β s n x ω') ∂disorderLaw))
          (fun ω => b * (Real.log (smoothedP2Plane β s n y ω) -
            ∫ ω', Real.log (smoothedP2Plane β s n y ω') ∂disorderLaw)) disorderLaw =
        ProbabilityTheory.covariance
          (fun ω => a * Real.log (smoothedP2Plane β s n x ω))
          (fun ω => b * Real.log (smoothedP2Plane β s n y ω)) disorderLaw := by
    calc
      _ = a * (b * ProbabilityTheory.covariance
          (fun ω => Real.log (smoothedP2Plane β s n x ω) -
            ∫ ω', Real.log (smoothedP2Plane β s n x ω') ∂disorderLaw)
          (fun ω => Real.log (smoothedP2Plane β s n y ω) -
            ∫ ω', Real.log (smoothedP2Plane β s n y ω') ∂disorderLaw) disorderLaw) := by
            rw [ProbabilityTheory.covariance_const_mul_left,
              ProbabilityTheory.covariance_const_mul_right]
      _ = a * (b * ProbabilityTheory.covariance
          (fun ω => Real.log (smoothedP2Plane β s n x ω))
          (fun ω => Real.log (smoothedP2Plane β s n y ω)) disorderLaw) := by
            rw [ProbabilityTheory.covariance_sub_const_left ha,
              ProbabilityTheory.covariance_sub_const_right hb]
      _ = _ := by
            rw [ProbabilityTheory.covariance_const_mul_left,
              ProbabilityTheory.covariance_const_mul_right]
  rw [hcenter]
  exact covariance_mul_mul_le_abs_mul_abs_of_nonneg disorderLaw
    (fun ω => Real.log (smoothedP2Plane β s n x ω))
    (fun ω => Real.log (smoothedP2Plane β s n y ω)) a b
    ((C / D) * MomentBounds.truncatedGreen n (y - x) + Dx + Dy)
    hcov0.1 hcov

/-- Under the second-moment bound `C₀ / log (1 + N / k)` and `L / 4 ≤ log (1 + N / k)`, each
collision coefficient `σ² E[Z(0 → n - r)²]`, `1 ≤ r ≤ n`, is at most `4 * C₀ / L`. -/
theorem sigmaSq_collision_secondMoment_le
    (β : ℝ) (N n : ℕ) (L C₀ : ℝ) (hL : 0 < L) (hC₀ : 0 ≤ C₀)
    (hsecond : ∀ k : ℕ, 1 ≤ k → k ≤ n →
      Polymer.sigmaSq β *
        ∫ ω, pointToPlane β 0 k 0 ω ^ 2 ∂disorderLaw ≤
          C₀ / Real.log (1 + (N : ℝ) / k))
    (hlog : ∀ k : ℕ, 1 ≤ k → k ≤ n →
      L / 4 ≤ Real.log (1 + (N : ℝ) / k))
    (hlogN : L / 4 ≤ Real.log (1 + (N : ℝ))) :
    ∀ r ∈ Finset.Icc 1 n,
      Polymer.sigmaSq β *
        ∫ ω, pointToPlane β 0 (n - r) 0 ω ^ 2 ∂disorderLaw ≤ 4 * C₀ / L := by
  intro r hr
  have hr' := Finset.mem_Icc.mp hr
  have hσ : 0 ≤ Polymer.sigmaSq β := by
    unfold Polymer.sigmaSq
    exact sub_nonneg.mpr (Real.one_le_exp (sq_nonneg β))
  by_cases hk : n - r = 0
  · have hmoment : 1 ≤ ∫ ω, pointToPlane β 0 1 0 ω ^ 2 ∂disorderLaw := by
      let F : Disorder → ℝ := fun ω => pointToPlane β 0 1 0 ω
      have hF : Integrable F disorderLaw := Polymer.integrable_pointToPlane β 0 1 0
      have hF2 : Integrable (fun ω => F ω ^ 2) disorderLaw :=
        Polymer.integrable_pow_pointToPlane β 0 1 0 2
      have hdiff : Integrable (fun ω => (F ω - 1) ^ 2) disorderLaw := by
        have hEq : (fun ω => (F ω - 1) ^ 2) =
            fun ω => F ω ^ 2 - 2 * F ω + 1 := by
          funext ω
          ring
        rw [hEq]
        exact (hF2.sub (hF.const_mul 2)).add (integrable_const 1)
      have hmean : (∫ ω, F ω ∂disorderLaw) = 1 := by
        exact Polymer.integral_pointToPlane β 0 1 0
      have hnonneg : 0 ≤ ∫ ω, (F ω - 1) ^ 2 ∂disorderLaw :=
        integral_nonneg fun ω => sq_nonneg (F ω - 1)
      have hEq : (∫ ω, (F ω - 1) ^ 2 ∂disorderLaw) =
          (∫ ω, F ω ^ 2 ∂disorderLaw) - 1 := by
        have hEqfun : (fun ω => (F ω - 1) ^ 2) =
            fun ω => F ω ^ 2 - 2 * F ω + 1 := by
          funext ω
          ring
        have hlinear : (∫ ω, F ω ^ 2 - 2 * F ω ∂disorderLaw) =
            (∫ ω, F ω ^ 2 ∂disorderLaw) - 2 * (∫ ω, F ω ∂disorderLaw) := by
          rw [integral_sub hF2 (hF.const_mul 2), integral_const_mul]
        have hfunInt : (∫ ω, (F ω - 1) ^ 2 ∂disorderLaw) =
            ∫ ω, F ω ^ 2 - 2 * F ω + 1 ∂disorderLaw := by
          apply integral_congr_ae
          filter_upwards [] with ω
          exact congrFun hEqfun ω
        have houter : (∫ ω, F ω ^ 2 - 2 * F ω + 1 ∂disorderLaw) =
            (∫ ω, F ω ^ 2 - 2 * F ω ∂disorderLaw) + 1 := by
          have h := integral_add (hF2.sub (hF.const_mul 2)) (integrable_const 1)
          simpa using h
        calc
          _ = (∫ ω, F ω ^ 2 - 2 * F ω ∂disorderLaw) + 1 := hfunInt.trans houter
          _ = _ := by rw [hlinear, hmean]; ring
      linarith
    have hsecond1 := hsecond 1 (by omega) (by omega)
    have hbound : Polymer.sigmaSq β ≤ C₀ / Real.log (1 + (N : ℝ)) := by
      have hNpos : 0 < N := by
        by_contra hN
        have : N = 0 := by omega
        subst N
        simp at hlogN
        linarith
      have hlogpos : 0 < Real.log (1 + (N : ℝ)) := by
        apply Real.log_pos
        norm_cast
        omega
      have hprod := mul_le_mul_of_nonneg_left hmoment hσ
      calc
        Polymer.sigmaSq β = Polymer.sigmaSq β * 1 := by ring
        _ ≤ Polymer.sigmaSq β *
            ∫ ω, pointToPlane β 0 1 0 ω ^ 2 ∂disorderLaw := hprod
        _ ≤ C₀ / Real.log (1 + (N : ℝ)) := by simpa using hsecond1
    have hden : 0 < L / 4 := by positivity
    have hbound' : C₀ / Real.log (1 + (N : ℝ)) ≤ C₀ / (L / 4) :=
      div_le_div_of_nonneg_left hC₀ hden hlogN
    have hmoment0 : ∫ ω, pointToPlane β 0 (n - r) 0 ω ^ 2 ∂disorderLaw = 1 := by
      simp [hk, pointToPlane]
    rw [hmoment0]
    calc
      Polymer.sigmaSq β * 1 = Polymer.sigmaSq β := by ring
      _ ≤ C₀ / (L / 4) := hbound.trans hbound'
      _ = 4 * C₀ / L := by field_simp
  · have hkpos : 1 ≤ n - r := by omega
    have hkbound : n - r ≤ n := Nat.sub_le _ _
    have hsecond' := hsecond (n - r) hkpos hkbound
    have hden : 0 < L / 4 := by positivity
    have hbound : C₀ / Real.log (1 + (N : ℝ) / (↑(n - r) : ℝ)) ≤ C₀ / (L / 4) :=
      div_le_div_of_nonneg_left hC₀ hden (hlog (n - r) hkpos hkbound)
    calc
      _ ≤ C₀ / Real.log (1 + (N : ℝ) / (↑(n - r) : ℝ)) := hsecond'
      _ ≤ C₀ / (L / 4) := hbound
      _ = 4 * C₀ / L := by field_simp

private theorem centered_log_weighted_field_sq_le (β : ℝ) (hβ : 0 ≤ β)
    (s n N : ℕ) (hsn : s ≤ n) (φ : Plane → ℝ) (hφ : Measurable φ)
    (hφint : Integrable φ) (C D E : ℝ) (hC : 0 ≤ C) (hD : 0 < D)
    (hcoeff : ∀ r ∈ Finset.Icc (s + 1) n,
      Polymer.sigmaSq β *
        ∫ ω, pointToPlane β 0 (n - r) 0 ω ^ 2 ∂disorderLaw ≤ C / D)
    (hDx : ∀ x : Site,
      gaussianityDefect disorderLaw
        (fun ω => Real.log (smoothedP2Plane β s n x ω)) ≤ E)
    (hK : Integrable (fun p : Plane × Plane =>
      |φ p.1| * |φ p.2| *
        ((C / D) * MomentBounds.truncatedGreen n
          (latticePoint N p.2 - latticePoint N p.1) + E + E))
      (volume.prod volume)) :
    (∀ᵐ ω ∂disorderLaw, Integrable (fun x : Plane => φ x *
      centeredLogSmoothed β s n (latticePoint N x) ω)) ∧
    MemLp (fun ω => ∫ x : Plane, φ x *
      centeredLogSmoothed β s n (latticePoint N x) ω) 2 disorderLaw ∧
    Integrable (fun ω => (∫ x : Plane, φ x *
      centeredLogSmoothed β s n (latticePoint N x) ω) ^ 2) disorderLaw ∧
    (∫ ω, (∫ x : Plane, φ x *
      centeredLogSmoothed β s n (latticePoint N x) ω) ^ 2 ∂disorderLaw) ≤
      ∫ p : Plane × Plane, |φ p.1| * |φ p.2| *
        ((C / D) * MomentBounds.truncatedGreen n
          (latticePoint N p.2 - latticePoint N p.1) + E + E)
        ∂volume.prod volume := by
  obtain ⟨B, hB, hZmeas, hZmem, hZsq⟩ := centered_log_smoothed_field_data β s n N
  let Z : Disorder → Plane → ℝ := fun ω x =>
    centeredLogSmoothed β s n (latticePoint N x) ω
  have hZmeas' : Measurable (fun p : Disorder × Plane => Z p.1 p.2) := by
    simpa only [Z] using hZmeas
  have hZmem' : ∀ x, MemLp (fun ω => Z ω x) 2 disorderLaw := by
    simpa only [Z] using hZmem
  have hZsq' : ∀ x, Integrable (fun ω => Z ω x ^ 2) disorderLaw ∧
      (∫ ω, Z ω x ^ 2 ∂disorderLaw) ≤ B := by
    simpa only [Z] using hZsq
  have hfield := weighted_field_integrability disorderLaw φ hφ hφint hZmeas'
    hZmem' B hB hZsq'
  let X : Disorder → Plane → ℝ := fun ω x => φ x * Z ω x
  have hXint : ∀ᵐ ω ∂disorderLaw, Integrable (X ω) := by
    simpa only [X, Z] using hfield.1
  have hXprod : Integrable
      (fun p : Disorder × (Plane × Plane) => X p.1 p.2.1 * X p.1 p.2.2)
      (disorderLaw.prod (volume.prod volume)) := by
    simpa only [X, Z] using hfield.2.1
  have hXsq : Integrable (fun ω => (∫ x : Plane, X ω x) ^ 2) disorderLaw := by
    simpa only [X, Z] using hfield.2.2
  have hXmeas : Measurable (fun p : Disorder × Plane => X p.1 p.2) := by
    exact (hφ.comp measurable_snd).mul hZmeas'
  have hFstrong : StronglyMeasurable (fun ω => ∫ x : Plane, X ω x) := by
    simpa only [Function.uncurry_apply_pair] using
      hXmeas.stronglyMeasurable.integral_prod_right'
  have hFmem : MemLp (fun ω => ∫ x : Plane, X ω x) 2 disorderLaw :=
    (memLp_two_iff_integrable_sq hFstrong.aestronglyMeasurable).2 hXsq
  have hX2 : ∀ x, MemLp (fun ω => X ω x) 2 disorderLaw := by
    intro x
    simpa only [X] using (hZmem' x).const_mul (φ x)
  have hzeroZ (x : Plane) :
      ∫ ω, centeredLogSmoothed β s n (latticePoint N x) ω ∂disorderLaw = 0 := by
    let z := latticePoint N x
    have hlog := memLp_log_smoothedP2Plane β s n z
    have hlogInt : Integrable
        (fun ω => Real.log (smoothedP2Plane β s n z ω)) disorderLaw :=
      hlog.integrable (by norm_num)
    dsimp [centeredLogSmoothed]
    rw [integral_sub hlogInt (integrable_const _)]
    simp [z]
  have hzero : ∀ x, ∫ ω, X ω x ∂disorderLaw = 0 := by
    intro x
    dsimp [X, Z]
    rw [integral_const_mul, hzeroZ]
    simp
  have hcov : ∀ p : Plane × Plane,
      ProbabilityTheory.covariance (fun ω => X ω p.1) (fun ω => X ω p.2)
        disorderLaw ≤
      |φ p.1| * |φ p.2| *
        ((C / D) * MomentBounds.truncatedGreen n
          (latticePoint N p.2 - latticePoint N p.1) + E + E) := by
    intro p
    dsimp [X, Z]
    let x := latticePoint N p.1
    let y := latticePoint N p.2
    have hlogx := (memLp_log_smoothedP2Plane β s n x).integrable (by norm_num)
    have hlogy := (memLp_log_smoothedP2Plane β s n y).integrable (by norm_num)
    simpa [x, y, centeredLogSmoothed] using
      covariance_centered_weighted_smoothed_le_truncatedGreen
      β hβ s n hsn x y C D E E hC hD hcoeff (hDx x) (hDx y) hlogx hlogy
      (φ p.1) (φ p.2)
  refine ⟨?_, ?_, hXsq, ?_⟩
  · simpa only [X, Z] using hXint
  · simpa only [X, Z] using hFmem
  exact integral_sq_centered_field_le_of_covariance disorderLaw
    (fun p : Plane × Plane => |φ p.1| * |φ p.2| *
      ((C / D) * MomentBounds.truncatedGreen n
        (latticePoint N p.2 - latticePoint N p.1) + E + E))
    hXint hXprod hX2 hzero hcov hK

private theorem smoothedP2Plane_zero_eq_pointToPlane (β : ℝ) (n : ℕ)
    (z : Site) (ω : Disorder) :
    smoothedP2Plane β 0 n z ω = pointToPlane β 0 n z ω := by
  unfold smoothedP2Plane
  rw [tsum_eq_single z]
  · simp
  · intro y hy
    have hne : y - z ≠ 0 := by
      intro h
      apply hy
      exact sub_eq_zero.mp h
    simp [hne]

private theorem localLogError_eq_centered_integrals_ae (β : ℝ) (N m n : ℕ)
    (φ : Plane → ℝ) (h0 : ∀ᵐ ω ∂disorderLaw,
      Integrable (fun x : Plane => φ x *
        centeredLogSmoothed β 0 n (latticePoint N x) ω))
    (hm : ∀ᵐ ω ∂disorderLaw,
      Integrable (fun x : Plane => φ x *
        centeredLogSmoothed β m n (latticePoint N x) ω)) :
    ∀ᵐ ω ∂disorderLaw,
      localLogError β N m n φ ω =
        (∫ x : Plane, φ x * centeredLogSmoothed β 0 n (latticePoint N x) ω) -
          ∫ x : Plane, φ x * centeredLogSmoothed β m n (latticePoint N x) ω := by
  filter_upwards [h0, hm] with ω h0ω hmω
  unfold localLogError
  have hpointInt (x : Plane) :
      Integrable (fun ω' => Real.log (pointToPlane β 0 n (latticePoint N x) ω'))
        disorderLaw := by
    let z := latticePoint N x
    have hmem := memLp_log_smoothedP2Plane β 0 n z
    have hEq : (fun ω' => Real.log (pointToPlane β 0 n z ω')) =
        fun ω' => Real.log (smoothedP2Plane β 0 n z ω') := by
      funext ω'
      exact congrArg Real.log (smoothedP2Plane_zero_eq_pointToPlane β n z ω').symm
    rw [hEq]
    exact hmem.integrable (by norm_num)
  have hsmInt (x : Plane) :
      Integrable (fun ω' => Real.log (smoothedP2Plane β m n (latticePoint N x) ω'))
        disorderLaw :=
    (memLp_log_smoothedP2Plane β m n (latticePoint N x)).integrable (by norm_num)
  have hmean0 (x : Plane) :
      (∫ ω', Real.log (smoothedP2Plane β 0 n (latticePoint N x) ω') ∂disorderLaw) =
        ∫ ω', Real.log (pointToPlane β 0 n (latticePoint N x) ω') ∂disorderLaw := by
    apply integral_congr_ae
    filter_upwards [] with ω'
    exact congrArg Real.log (smoothedP2Plane_zero_eq_pointToPlane β n
      (latticePoint N x) ω')
  have hpoint (x : Plane) (ω' : Disorder) :
      Real.log (pointToPlane β 0 n (latticePoint N x) ω') -
        ∫ ω'', Real.log (pointToPlane β 0 n (latticePoint N x) ω'') ∂disorderLaw =
      centeredLogSmoothed β 0 n (latticePoint N x) ω' := by
    dsimp [centeredLogSmoothed]
    rw [← hmean0 x, smoothedP2Plane_zero_eq_pointToPlane]
  have hsm (x : Plane) (ω' : Disorder) :
      Real.log (smoothedP2Plane β m n (latticePoint N x) ω') -
        ∫ ω'', Real.log (smoothedP2Plane β m n (latticePoint N x) ω'') ∂disorderLaw =
      centeredLogSmoothed β m n (latticePoint N x) ω' := by
    rfl
  have hcenterDifference (x : Plane) (ω' : Disorder) :
      (Real.log (pointToPlane β 0 n (latticePoint N x) ω') -
        Real.log (smoothedP2Plane β m n (latticePoint N x) ω')) -
        ∫ ω'', (Real.log (pointToPlane β 0 n (latticePoint N x) ω'') -
          Real.log (smoothedP2Plane β m n (latticePoint N x) ω'')) ∂disorderLaw =
        centeredLogSmoothed β 0 n (latticePoint N x) ω' -
          centeredLogSmoothed β m n (latticePoint N x) ω' := by
    rw [integral_sub (hpointInt x) (hsmInt x)]
    calc
      _ = (Real.log (pointToPlane β 0 n (latticePoint N x) ω') -
          ∫ ω'', Real.log (pointToPlane β 0 n (latticePoint N x) ω'') ∂disorderLaw) -
          (Real.log (smoothedP2Plane β m n (latticePoint N x) ω') -
          ∫ ω'', Real.log (smoothedP2Plane β m n (latticePoint N x) ω'') ∂disorderLaw) := by ring
      _ = _ := by rw [hpoint, hsm]
  calc
    localLogError β N m n φ ω = ∫ x : Plane, φ x *
        (centeredLogSmoothed β 0 n (latticePoint N x) ω -
          centeredLogSmoothed β m n (latticePoint N x) ω) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [hcenterDifference]
    _ = ∫ x : Plane,
        (φ x * centeredLogSmoothed β 0 n (latticePoint N x) ω) -
          (φ x * centeredLogSmoothed β m n (latticePoint N x) ω) := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = (∫ x : Plane, φ x * centeredLogSmoothed β 0 n (latticePoint N x) ω) -
        ∫ x : Plane, φ x * centeredLogSmoothed β m n (latticePoint N x) ω :=
      integral_sub h0ω hmω

/-- The `L²` norm of the local log error is at most twice the square root of the double integral of
`|φ x| |φ y|` against the covariance bound `(C / D) * truncatedGreen + E + E`. -/
theorem localLogError_eLpNorm_le_covariance_integral
    (β : ℝ) (hβ : 0 ≤ β) (N m n : ℕ) (hmn : m ≤ n)
    (φ : Plane → ℝ) (hφ : Measurable φ) (hφint : Integrable φ)
    (C D E : ℝ) (hC : 0 ≤ C) (hD : 0 < D) (hE : 0 ≤ E)
    (hcoeff : ∀ r ∈ Finset.Icc 1 n,
      Polymer.sigmaSq β *
        ∫ ω, pointToPlane β 0 (n - r) 0 ω ^ 2 ∂disorderLaw ≤ C / D)
    (hD0 : ∀ x : Site,
      gaussianityDefect disorderLaw
        (fun ω => Real.log (smoothedP2Plane β 0 n x ω)) ≤ E)
    (hDm : ∀ x : Site,
      gaussianityDefect disorderLaw
        (fun ω => Real.log (smoothedP2Plane β m n x ω)) ≤ E)
    (hK : Integrable (fun p : Plane × Plane =>
      |φ p.1| * |φ p.2| * ((C / D) * MomentBounds.truncatedGreen n
        (latticePoint N p.2 - latticePoint N p.1) + E + E)) (volume.prod volume)) :
    eLpNorm (localLogError β N m n φ) 2 disorderLaw ≤
      2 * ENNReal.ofReal (Real.sqrt
        (∫ p : Plane × Plane, |φ p.1| * |φ p.2| *
          ((C / D) * MomentBounds.truncatedGreen n
            (latticePoint N p.2 - latticePoint N p.1) + E + E)
          ∂volume.prod volume)) := by
  let K : Plane × Plane → ℝ := fun p => |φ p.1| * |φ p.2| *
    ((C / D) * MomentBounds.truncatedGreen n
      (latticePoint N p.2 - latticePoint N p.1) + E + E)
  have hKnonneg : ∀ p, 0 ≤ K p := by
    intro p
    dsimp [K]
    apply mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have hratio : 0 ≤ C / D := div_nonneg hC hD.le
    have hgreen := MomentBounds.truncatedGreen_nonneg n
      (latticePoint N p.2 - latticePoint N p.1)
    positivity
  have hB : 0 ≤ ∫ p : Plane × Plane, K p ∂volume.prod volume :=
    integral_nonneg fun p => hKnonneg p
  have hK' : Integrable K (volume.prod volume) := by simpa only [K] using hK
  have hcoeff0 : ∀ r ∈ Finset.Icc (0 + 1) n,
      Polymer.sigmaSq β *
        ∫ ω, pointToPlane β 0 (n - r) 0 ω ^ 2 ∂disorderLaw ≤ C / D := by
    simpa only [zero_add] using hcoeff
  have hcoeffm : ∀ r ∈ Finset.Icc (m + 1) n,
      Polymer.sigmaSq β *
        ∫ ω, pointToPlane β 0 (n - r) 0 ω ^ 2 ∂disorderLaw ≤ C / D := by
    intro r hr
    rcases Finset.mem_Icc.mp hr with ⟨hrlow, hrhigh⟩
    exact hcoeff r (Finset.mem_Icc.mpr ⟨by omega, hrhigh⟩)
  have hfield0 := centered_log_weighted_field_sq_le β hβ 0 n N (by omega)
    φ hφ hφint C D E hC hD hcoeff0 hD0 hK'
  have hfieldm := centered_log_weighted_field_sq_le β hβ m n N hmn
    φ hφ hφint C D E hC hD hcoeffm hDm hK'
  have hnorm0 := eLpNorm_le_of_integral_sq_le disorderLaw hfield0.2.1 hfield0.2.2.2
  have hnormm := eLpNorm_le_of_integral_sq_le disorderLaw hfieldm.2.1 hfieldm.2.2.2
  have hlocal := localLogError_eq_centered_integrals_ae β N m n φ hfield0.1 hfieldm.1
  rw [eLpNorm_congr_ae hlocal]
  calc
    eLpNorm (fun ω =>
        (∫ x : Plane, φ x * centeredLogSmoothed β 0 n (latticePoint N x) ω) -
          ∫ x : Plane, φ x * centeredLogSmoothed β m n (latticePoint N x) ω)
        2 disorderLaw ≤
      eLpNorm (fun ω => ∫ x : Plane,
        φ x * centeredLogSmoothed β 0 n (latticePoint N x) ω) 2 disorderLaw +
      eLpNorm (fun ω => ∫ x : Plane,
        φ x * centeredLogSmoothed β m n (latticePoint N x) ω) 2 disorderLaw :=
          eLpNorm_sub_le (by norm_num)
    _ ≤ ENNReal.ofReal (Real.sqrt (∫ p, K p ∂volume.prod volume)) +
        ENNReal.ofReal (Real.sqrt (∫ p, K p ∂volume.prod volume)) :=
          add_le_add hnorm0 hnormm
    _ = 2 * ENNReal.ofReal (Real.sqrt (∫ p, K p ∂volume.prod volume)) := by ring
    _ = 2 * ENNReal.ofReal (Real.sqrt
        (∫ p : Plane × Plane, |φ p.1| * |φ p.2| *
          ((C / D) * MomentBounds.truncatedGreen n
            (latticePoint N p.2 - latticePoint N p.1) + E + E)
          ∂volume.prod volume)) := by rfl

/-- From the variance-defect bound, small-time smoothed log partition functions have Gaussianity
defect in `[0, C / |log δ| ^ (1/4) + o N]`, uniformly in `ϑ ∈ [-A, A]`, start site and even `s`. -/
theorem gaussianityDefect_small_time_of (hVD : PropVDBound) (A : ℝ) :
    ∃ δ₀ C : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        ∃ o : ℕ → ℝ, Tendsto o atTop (nhds 0) ∧
          ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A, ∀ (x : Site) (s : ℕ),
            Even s → s ≤ evenCeil (Real.sqrt δ * N) →
              0 ≤ gaussianityDefect disorderLaw
                  (fun ω => Real.log (smoothedP2Plane (criticalBeta ϑ N) s
                    (evenCeil (Real.sqrt δ * N)) x ω)) ∧
                gaussianityDefect disorderLaw
                    (fun ω => Real.log (smoothedP2Plane (criticalBeta ϑ N) s
                      (evenCeil (Real.sqrt δ * N)) x ω)) ≤
                  C / |Real.log δ| ^ ((1 : ℝ) / 4) + o N := by
  rcases hVD A with ⟨_, hsmall⟩
  obtain ⟨δ₀, C, hδ₀pos, hδ₀lt, hsmall⟩ := hsmall
  refine ⟨δ₀, C, hδ₀pos, hδ₀lt, ?_⟩
  intro δ hδ hδle
  obtain ⟨o, ho, hN⟩ := hsmall δ hδ hδle
  refine ⟨o, ho, ?_⟩
  filter_upwards [hN] with N hN
  intro ϑ hϑ x s hs hsn
  have hβ : 0 ≤ criticalBeta ϑ N := by
    dsimp [criticalBeta]
    exact Real.sqrt_nonneg _
  have hdef := OnePoint.gaussianityDefect_log_smoothedP2Plane_bounds hβ s
    (evenCeil (Real.sqrt δ * N)) x
  have hratio := hN ϑ hϑ x s hs hsn
  exact ⟨hdef.1, le_trans hdef.2 hratio⟩

/-- For sufficiently large `N`, the rounded time `√δ N` is at most `N`, and `|log δ| / 4` is a lower bound for `log (1 + N / k)` at positive clocks up to that time and for `log (1 + N)`. -/
theorem eventually_small_time_log_bounds (δ : ℝ) (hδ : 0 < δ)
    (hδ16 : δ ≤ 1 / 16) (hδexp : δ ≤ Real.exp (-8)) :
    ∀ᶠ N : ℕ in atTop,
      (evenCeil (Real.sqrt δ * N) : ℝ) ≤ N ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ evenCeil (Real.sqrt δ * N) →
        |Real.log δ| / 4 ≤ Real.log (1 + (N : ℝ) / k)) ∧
      |Real.log δ| / 4 ≤ Real.log (1 + (N : ℝ)) := by
  have hδlt1 : δ < 1 := by linarith
  have hqpos : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hqle : Real.sqrt δ ≤ 1 / 4 := by
    calc
      Real.sqrt δ ≤ Real.sqrt (1 / 16) := Real.sqrt_le_sqrt hδ16
      _ = 1 / 4 := by norm_num
  have hlogδneg : Real.log δ < 0 := Real.log_neg hδ hδlt1
  have hL : 8 ≤ |Real.log δ| := by
    have hlog := Real.log_le_log hδ hδexp
    rw [Real.log_exp] at hlog
    rw [abs_of_neg hlogδneg]
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hbase : Real.log (1 / (2 * Real.sqrt δ)) =
      |Real.log δ| / 2 - Real.log 2 := by
    rw [one_div, Real.log_inv,
      Real.log_mul (by norm_num) hqpos.ne', Real.log_sqrt hδ.le]
    rw [abs_of_neg hlogδneg]
    ring
  have hNevent : ∀ᶠ N : ℕ in atTop, 2 / Real.sqrt δ ≤ (N : ℝ) := by
    exact (tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [hNevent] with N hN
  have hNpos : 0 < (N : ℝ) := by
    have hbasepos : 0 < 2 / Real.sqrt δ := by positivity
    exact lt_of_lt_of_le hbasepos hN
  let qN : ℝ := Real.sqrt δ * N
  have hqN : 2 ≤ qN := by
    dsimp [qN]
    have hmul := (div_le_iff₀ hqpos).1 hN
    nlinarith
  have hnround := evenCeil_lt_add_two (by positivity : 0 ≤ qN)
  have hnupper : (evenCeil qN : ℝ) ≤ 2 * qN := by
    have hround : (evenCeil qN : ℝ) ≤ qN + 2 := hnround.le
    linarith [hqN]
  have hnle : (evenCeil qN : ℝ) ≤ N := by
    have hqNupper : 2 * qN ≤ (N : ℝ) := by
      dsimp [qN]
      nlinarith [hqle, hNpos]
    exact hnupper.trans hqNupper
  have hnpositive : 0 < (evenCeil qN : ℝ) := by
    have hlower := le_evenCeil qN
    linarith [hqN]
  have hbaseLower : |Real.log δ| / 4 ≤ Real.log (1 + 1 / (2 * Real.sqrt δ)) := by
    calc
      |Real.log δ| / 4 ≤ Real.log (1 / (2 * Real.sqrt δ)) := by
        rw [hbase]
        linarith [hL, hlog2]
      _ ≤ Real.log (1 + 1 / (2 * Real.sqrt δ)) :=
        Real.log_le_log (by positivity) (by linarith)
  have hlogN : |Real.log δ| / 4 ≤ Real.log (1 + (N : ℝ)) := by
    have hsmall : 1 / (2 * Real.sqrt δ) ≤ 2 / Real.sqrt δ := by
      field_simp [ne_of_gt hqpos]
      norm_num
    have hargpos : 0 < 1 + 1 / (2 * Real.sqrt δ) := by positivity
    have hargle : 1 + 1 / (2 * Real.sqrt δ) ≤ 1 + (N : ℝ) := by
      linarith
    have hlogmono := Real.log_le_log hargpos hargle
    exact hbaseLower.trans hlogmono
  refine ⟨hnle, ?_, hlogN⟩
  intro k hkpos hkN
  have hkpos' : 0 < (k : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (by omega))
  have hNdiv : 1 / (2 * Real.sqrt δ) ≤ (N : ℝ) / (evenCeil qN : ℝ) := by
    apply (le_div_iff₀ hnpositive).2
    calc
      (1 / (2 * Real.sqrt δ)) * (evenCeil qN : ℝ) ≤
          (1 / (2 * Real.sqrt δ)) * (2 * qN) :=
        mul_le_mul_of_nonneg_left hnupper (by positivity)
      _ = (N : ℝ) := by dsimp [qN]; field_simp [ne_of_gt hqpos]
  have hkdiv : (N : ℝ) / (evenCeil qN : ℝ) ≤ (N : ℝ) / k :=
    div_le_div_of_nonneg_left (by positivity) hkpos' (by exact_mod_cast hkN)
  have hbaseDiv : 1 / (2 * Real.sqrt δ) ≤ (N : ℝ) / k := by
    have hNdiv' := hNdiv.trans hkdiv
    exact hNdiv'
  have hlogmono := Real.log_le_log (by positivity : 0 < 1 + 1 / (2 * Real.sqrt δ))
    (by linarith : 1 + 1 / (2 * Real.sqrt δ) ≤ 1 + (N : ℝ) / k)
  exact hbaseLower.trans hlogmono

end Critical2DKPZ.Smoothing

end
