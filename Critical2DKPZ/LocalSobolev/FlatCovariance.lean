/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.LocalSobolev.ReversalLaw
public import Critical2DKPZ.LocalSobolev.HeatStartCovariance
public import Critical2DKPZ.CovarianceKernel.CovarianceLimit
public import Critical2DKPZ.JointConvergence.HeatStartLogConvergence
import Critical2DKPZ.JointConvergence.MomentConvergence
import Mathlib.Tactic

/-! # Covariance bounds for flat regularized fields -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.JointConvergence
open scoped BoundedContinuousFunction ENNReal Topology

universe u

namespace Critical2DKPZ.LocalSobolev

private theorem integrable_sq_of_fourth {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : AEMeasurable f μ) (h4 : Integrable (fun ω => |f ω| ^ (4 : ℕ)) μ) :
    Integrable (fun ω => f ω ^ 2) μ := by
  have hmajor : Integrable (fun ω => (1 : ℝ) + |f ω| ^ (4 : ℕ)) μ :=
    (integrable_const 1).add h4
  have hstrong : AEStronglyMeasurable (fun ω => f ω ^ 2) μ :=
    (continuous_id.pow 2).comp_aestronglyMeasurable hf.aestronglyMeasurable
  apply hmajor.mono' hstrong
  filter_upwards [] with ω
  have habs4 : |f ω| ^ (4 : ℕ) = f ω ^ 4 := by
    calc
      |f ω| ^ (4 : ℕ) = |(f ω) ^ 4| := (abs_pow (f ω) 4).symm
      _ = (f ω) ^ 4 := abs_of_nonneg (by positivity)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  rw [habs4]
  nlinarith [sq_nonneg (f ω ^ 2 - 1)]

private theorem memLp_two_of_fourth {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : AEMeasurable f μ) (h4 : Integrable (fun ω => |f ω| ^ (4 : ℕ)) μ) :
    MemLp f 2 μ :=
  (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2
    (integrable_sq_of_fourth hf h4)

private theorem integrable_mul_sq_of_fourth {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f g : Ω → ℝ}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hF : Integrable (fun ω => |f ω| ^ (4 : ℕ)) μ)
    (hG : Integrable (fun ω => |g ω| ^ (4 : ℕ)) μ) :
    Integrable (fun ω => |f ω * g ω| ^ (2 : ℕ)) μ ∧
      ∫ ω, |f ω * g ω| ^ (2 : ℕ) ∂μ ≤
        (∫ ω, |f ω| ^ (4 : ℕ) ∂μ) + ∫ ω, |g ω| ^ (4 : ℕ) ∂μ := by
  have hmajor : Integrable (fun ω => |f ω| ^ (4 : ℕ) + |g ω| ^ (4 : ℕ)) μ :=
    hF.add hG
  have hstrong : AEStronglyMeasurable (fun ω => |f ω * g ω| ^ (2 : ℕ)) μ := by
    exact (continuous_abs.pow 2).comp_aestronglyMeasurable
      (hf.mul hg).aestronglyMeasurable
  have hprod : Integrable (fun ω => |f ω * g ω| ^ (2 : ℕ)) μ := by
    apply hmajor.mono' hstrong
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [abs_mul]
    nlinarith [sq_nonneg (|f ω| ^ 2 - |g ω| ^ 2)]
  refine ⟨hprod, ?_⟩
  calc
    ∫ ω, |f ω * g ω| ^ (2 : ℕ) ∂μ ≤
        ∫ ω, |f ω| ^ (4 : ℕ) + |g ω| ^ (4 : ℕ) ∂μ :=
      integral_mono hprod hmajor (fun ω => by
        rw [abs_mul]
        nlinarith [sq_nonneg (|f ω| ^ 2 - |g ω| ^ 2)])
    _ = (∫ ω, |f ω| ^ (4 : ℕ) ∂μ) + ∫ ω, |g ω| ^ (4 : ℕ) ∂μ :=
      integral_add hF hG

/-- The covariance bound for flat regularized fields, obtained by passing the lattice heat-start covariance bound
through joint convergence and the fourth-moment bounds in fixed-width heat-start convergence. -/
theorem kpzRegularized_flat_covariance_le_of (hVD : Smoothing.PropVDBound) (ϑ : ℝ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hHeatStartLogInput : HeatStartLogAt ϑ P Z) (hsym : ShfSymmetriesAt ϑ P Z)
    {t₀ t₁ : ℝ} (ht₀ : 0 < t₀) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc t₀ t₁, ∀ δ δ' : ℝ,
      0 < δ → δ < t / 2 → 0 < δ' → δ' < t / 2 → ∀ x y : Plane, x ≠ y →
        MemLp (kpzRegularized P Z t δ 0 x) 2 P ∧
        0 ≤ covariance (kpzRegularized P Z t δ 0 x) (kpzRegularized P Z t δ' 0 y) P ∧
        covariance (kpzRegularized P Z t δ 0 x) (kpzRegularized P Z t δ' 0 y) P ≤
          C * (1 + Real.log (1 + max 0 (Real.log ‖x - y‖⁻¹))) := by
  obtain ⟨C, hCovarianceN⟩ := heatStart_lattice_covariance_le_of hVD ϑ (t₁ := t₁) ht₀
  refine ⟨C, ?_⟩
  intro t ht δ δ' hδ hδt hδ' hδ't x y hxy
  have htpos : 0 < t := lt_of_lt_of_le ht₀ ht.1
  let d : Fin 2 → ℝ := fun i => if i = 0 then δ else δ'
  let z : Fin 2 → Plane := fun i => if i = 0 then x else y
  have hdt : ∀ i : Fin 2, 0 < d i ∧ d i < t := by
    intro i
    fin_cases i <;> simp [d] <;> constructor <;> linarith
  let X0 : ℕ → Disorder → ℝ := fun N ω =>
    heatStartLogProfile ϑ N δ t δ x 0 ω
  let X1 : ℕ → Disorder → ℝ := fun N ω =>
    heatStartLogProfile ϑ N δ' t δ' y 0 ω
  let X : ℕ → Disorder → Fin 2 → ℝ := fun N ω i =>
    heatStartLogProfile ϑ N (d i) t (d i) (z i) 0 ω
  let Y0 : Ω → ℝ := fun ω =>
    Real.log (shfPairing Z δ t (fun u => heatKernel δ (u - x)) (fun _ => 1) ω)
  let Y1 : Ω → ℝ := fun ω =>
    Real.log (shfPairing Z δ' t (fun u => heatKernel δ' (u - y)) (fun _ => 1) ω)
  let Y : Ω → Fin 2 → ℝ := fun ω i =>
    Real.log (shfPairing Z (d i) t (fun u => heatKernel (d i) (u - z i))
      (fun _ => 1) ω)
  have hHeatStartLogInputApplied := hHeatStartLogInput t 0 2 d d z (by
    intro i
    have hi := hdt i
    exact ⟨hi.1.le, hi.2, hi.1⟩)
  have hdist : TendstoInDistribution X atTop Y (fun _ => disorderLaw) P := by
    simpa [X, Y, d, z, heatStartLogProfile,
      Real.exp_zero, mul_one] using hHeatStartLogInputApplied.2.1
  have hdist0 : TendstoInDistribution (fun N ω => X N ω 0) atTop Y0
      (fun _ => disorderLaw) P := by
    simpa [Function.comp_def, X, Y, d, z, Y0] using
      hdist.continuous_comp (by fun_prop : Continuous (fun v : Fin 2 → ℝ => v 0))
  have hdist1 : TendstoInDistribution (fun N ω => X N ω 1) atTop Y1
      (fun _ => disorderLaw) P := by
    simpa [Function.comp_def, X, Y, d, z, Y1] using
      hdist.continuous_comp (by fun_prop : Continuous (fun v : Fin 2 → ℝ => v 1))
  let product : (Fin 2 → ℝ) → ℝ := fun v => v 0 * v 1
  have hdistProduct : TendstoInDistribution (fun N ω => X N ω 0 * X N ω 1) atTop
      (fun ω => Y0 ω * Y1 ω) (fun _ => disorderLaw) P := by
    simpa [Function.comp_def, product, X, Y, d, z, Y0, Y1] using
      hdist.continuous_comp (by fun_prop : Continuous product)
  obtain ⟨C0, hC0, hM0⟩ := heatStartLogProfile_rpow_bound ϑ
    (s := δ) (T := t) (δ := δ) hδ.le (by linarith) hδ x 0 (q := 4) (by norm_num)
  obtain ⟨C1, hC1, hM1⟩ := heatStartLogProfile_rpow_bound ϑ
    (s := δ') (T := t) (δ := δ') hδ'.le (by linarith) hδ' y 0 (q := 4) (by norm_num)
  let M0 : ℝ := C0 * 4 * Real.Gamma 4
  let M1 : ℝ := C1 * 4 * Real.Gamma 4
  have hX0int : ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω => |X N ω 0| ^ (4 : ℕ)) disorderLaw := by
    filter_upwards [hM0] with N hN
    simpa [X, X0, d, z, heatStartLogProfile, Real.rpow_natCast] using hN.1
  have hX1int : ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω => |X N ω 1| ^ (4 : ℕ)) disorderLaw := by
    filter_upwards [hM1] with N hN
    simpa [X, X1, d, z, heatStartLogProfile, Real.rpow_natCast] using hN.1
  have hX0bound : ∀ᶠ N : ℕ in atTop,
      ∫ ω, |X N ω 0| ^ (4 : ℕ) ∂disorderLaw ≤ M0 := by
    filter_upwards [hM0] with N hN
    simpa [X, X0, d, z, M0, heatStartLogProfile, Real.rpow_natCast] using hN.2
  have hX1bound : ∀ᶠ N : ℕ in atTop,
      ∫ ω, |X N ω 1| ^ (4 : ℕ) ∂disorderLaw ≤ M1 := by
    filter_upwards [hM1] with N hN
    simpa [X, X1, d, z, M1, heatStartLogProfile, Real.rpow_natCast] using hN.2
  have hX0intR : ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω => |X N ω 0| ^ (4 : ℝ)) disorderLaw := by
    filter_upwards [hX0int] with N hN
    simpa [Real.rpow_natCast] using hN
  have hX1intR : ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω => |X N ω 1| ^ (4 : ℝ)) disorderLaw := by
    filter_upwards [hX1int] with N hN
    simpa [Real.rpow_natCast] using hN
  have hX0boundR : ∀ᶠ N : ℕ in atTop,
      ∫ ω, |X N ω 0| ^ (4 : ℝ) ∂disorderLaw ≤ M0 := by
    filter_upwards [hX0bound] with N hN
    simpa [Real.rpow_natCast] using hN
  have hX1boundR : ∀ᶠ N : ℕ in atTop,
      ∫ ω, |X N ω 1| ^ (4 : ℝ) ∂disorderLaw ≤ M1 := by
    filter_upwards [hX1bound] with N hN
    simpa [Real.rpow_natCast] using hN
  have hmean0 : Tendsto (fun N => ∫ ω, X N ω 0 ∂disorderLaw) atTop
      (𝓝 (∫ ω, Y0 ω ∂P)) :=
    JointConvergence.tendsto_integral_of_tendstoInDistribution hdist0
      (q := 4) (M := M0) (by norm_num) hX0boundR hX0intR
  have hmean1 : Tendsto (fun N => ∫ ω, X N ω 1 ∂disorderLaw) atTop
      (𝓝 (∫ ω, Y1 ω ∂P)) :=
    JointConvergence.tendsto_integral_of_tendstoInDistribution hdist1
      (q := 4) (M := M1) (by norm_num) hX1boundR hX1intR
  have hproductInt : ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω => |X N ω 0 * X N ω 1| ^ (2 : ℕ)) disorderLaw := by
    filter_upwards [hX0int, hX1int] with N hN0 hN1
    simpa [X] using
      (integrable_mul_sq_of_fourth (hdist0.forall_aemeasurable N)
        (hdist1.forall_aemeasurable N) hN0 hN1).1
  have hproductBound : ∀ᶠ N : ℕ in atTop,
      ∫ ω, |X N ω 0 * X N ω 1| ^ (2 : ℕ) ∂disorderLaw ≤ M0 + M1 := by
    filter_upwards [hX0int, hX1int, hX0bound, hX1bound] with N hI0 hI1 hB0 hB1
    have h := integrable_mul_sq_of_fourth (hdist0.forall_aemeasurable N)
      (hdist1.forall_aemeasurable N) hI0 hI1
    simpa [X] using le_trans h.2 (add_le_add hB0 hB1)
  have hproductIntR : ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω => |X N ω 0 * X N ω 1| ^ (2 : ℝ)) disorderLaw := by
    filter_upwards [hproductInt] with N hN
    simpa [Real.rpow_natCast] using hN
  have hproductBoundR : ∀ᶠ N : ℕ in atTop,
      ∫ ω, |X N ω 0 * X N ω 1| ^ (2 : ℝ) ∂disorderLaw ≤ M0 + M1 := by
    filter_upwards [hproductBound] with N hN
    simpa [Real.rpow_natCast] using hN
  have hproductMean : Tendsto
      (fun N => ∫ ω, X N ω 0 * X N ω 1 ∂disorderLaw) atTop
      (𝓝 (∫ ω, Y0 ω * Y1 ω ∂P)) :=
    JointConvergence.tendsto_integral_of_tendstoInDistribution hdistProduct
      (q := 2) (M := M0 + M1) (by norm_num) hproductBoundR hproductIntR
  have hY0four := JointConvergence.integrable_rpow_limit_of_tendstoInDistribution
    hdist0 (q := 4) (M := M0) (by norm_num) hX0intR hX0boundR
  have hY1four := JointConvergence.integrable_rpow_limit_of_tendstoInDistribution
    hdist1 (q := 4) (M := M1) (by norm_num) hX1intR hX1boundR
  have hY0int : Integrable (fun ω => |Y0 ω| ^ (4 : ℕ)) P := by
    simpa [Real.rpow_natCast] using hY0four.1
  have hY1int : Integrable (fun ω => |Y1 ω| ^ (4 : ℕ)) P := by
    simpa [Real.rpow_natCast] using hY1four.1
  have hY0mem : MemLp Y0 2 P :=
    memLp_two_of_fourth hdist0.aemeasurable_limit hY0int
  have hY1mem : MemLp Y1 2 P :=
    memLp_two_of_fourth hdist1.aemeasurable_limit hY1int
  have hcovNFormula : ∀ᶠ N : ℕ in atTop,
      covariance (fun ω => X N ω 0) (fun ω => X N ω 1) disorderLaw =
        (∫ ω, X N ω 0 * X N ω 1 ∂disorderLaw) -
          (∫ ω, X N ω 0 ∂disorderLaw) * ∫ ω, X N ω 1 ∂disorderLaw := by
    filter_upwards [hX0int, hX1int] with N hN0 hN1
    exact covariance_eq_sub
      (memLp_two_of_fourth (hdist0.forall_aemeasurable N) hN0)
      (memLp_two_of_fourth (hdist1.forall_aemeasurable N) hN1)
  have hrawCovTendsto : Tendsto
      (fun N => covariance (fun ω => X N ω 0) (fun ω => X N ω 1) disorderLaw)
      atTop (𝓝 (covariance Y0 Y1 P)) := by
    apply Tendsto.congr' (hcovNFormula.mono fun N hN => hN.symm)
    rw [covariance_eq_sub hY0mem hY1mem]
    exact hproductMean.sub (hmean0.mul hmean1)
  have hcovN : ∀ᶠ N : ℕ in atTop,
      0 ≤ covariance (fun ω => X N ω 0) (fun ω => X N ω 1) disorderLaw ∧
        covariance (fun ω => X N ω 0) (fun ω => X N ω 1) disorderLaw ≤
          C * (1 + Real.log (1 + max 0 (Real.log ‖x - y‖⁻¹))) := by
    filter_upwards [hCovarianceN] with N hN
    simpa [X, X0, X1, d, z, heatStartLogProfile, sub_self, Real.exp_zero] using
      hN t t ht (le_rfl) δ δ' hδ hδt hδ' hδ't x y hxy
  have hrawNonneg : 0 ≤ covariance Y0 Y1 P :=
    isClosed_Ici.mem_of_tendsto hrawCovTendsto
      (hcovN.mono fun N hN => hN.1)
  have hrawUpper : covariance Y0 Y1 P ≤
      C * (1 + Real.log (1 + max 0 (Real.log ‖x - y‖⁻¹))) :=
    isClosed_Iic.mem_of_tendsto hrawCovTendsto
      (hcovN.mono fun N hN => hN.2)
  have hδ_lt : δ < t := by linarith
  have hδ'_lt : δ' < t := by linarith
  obtain ⟨_, _, hMomδ⟩ :=
    Critical2DKPZ.CovarianceKernel.kpzRegularized_uniform_second_moment_of ϑ P Z hZ hsym
    (fun T k s u hst => shfReversal_measureLaw_of ϑ P Z hZ T k s u hst)
    (t := t) (δ := δ)
    hδ hδ_lt
  obtain ⟨_, _, hMomδ'⟩ :=
    Critical2DKPZ.CovarianceKernel.kpzRegularized_uniform_second_moment_of ϑ P Z hZ hsym
    (fun T k s u hst => shfReversal_measureLaw_of ϑ P Z hZ T k s u hst)
    (t := t) (δ := δ')
    hδ' hδ'_lt
  have hFwd0 : MemLp (kpzRegularized P Z t δ 0 x) 2 P := (hMomδ x).1
  have hFwd1 : MemLp (kpzRegularized P Z t δ' 0 y) 2 P := (hMomδ' y).1
  let Fwd : Ω → Fin 2 → ℝ := fun ω i =>
    kpzRegularized P Z t (d i) 0 (z i) ω
  let Rev : Ω → Fin 2 → ℝ := fun ω i =>
    kpzRegularizedReversed P Z 0 t (d i) 0 (z i) ω
  have hpointLaw : P.map Fwd = P.map Rev := by
    simpa [Fwd, Rev] using kpzRegularized_reverse_pointLaw_of ϑ P Z hZ hsym
      t 2 (fun _ => t) d (fun _ => 0) z (by
        intro i
        have hi := hdt i
        exact ⟨hi.1, hi.2, le_rfl⟩)
  have hFwdAE : AEMeasurable Fwd P := by
    apply aemeasurable_pi_iff.mpr
    intro i
    fin_cases i
    · simpa [Fwd, d, z] using hFwd0.aestronglyMeasurable.aemeasurable
    · simpa [Fwd, d, z] using hFwd1.aestronglyMeasurable.aemeasurable
  have hRevField0 : kpzRegularizedReversed P Z 0 t δ 0 x =
      fun ω => Y0 ω -
        ∫ ω', Real.log (shfPairing Z δ t (fun u => heatKernel δ u)
          (fun _ => 1) ω') ∂P := by
    funext ω
    simp [kpzRegularizedReversed, Y0, Real.exp_zero]
  have hRevField1 : kpzRegularizedReversed P Z 0 t δ' 0 y =
      fun ω => Y1 ω -
        ∫ ω', Real.log (shfPairing Z δ' t (fun u => heatKernel δ' u)
          (fun _ => 1) ω') ∂P := by
    funext ω
    simp [kpzRegularizedReversed, Y1, Real.exp_zero]
  have hRevAE : AEMeasurable Rev P := by
    apply aemeasurable_pi_iff.mpr
    intro i
    fin_cases i
    · change AEMeasurable (kpzRegularizedReversed P Z 0 t δ 0 x) P
      rw [hRevField0]
      exact (hY0mem.aestronglyMeasurable.sub aestronglyMeasurable_const).aemeasurable
    · change AEMeasurable (kpzRegularizedReversed P Z 0 t δ' 0 y) P
      rw [hRevField1]
      exact (hY1mem.aestronglyMeasurable.sub aestronglyMeasurable_const).aemeasurable
  have hcovLaw : covariance (kpzRegularized P Z t δ 0 x)
      (kpzRegularized P Z t δ' 0 y) P = covariance
        (kpzRegularizedReversed P Z 0 t δ 0 x)
        (kpzRegularizedReversed P Z 0 t δ' 0 y) P := by
    calc
      covariance (kpzRegularized P Z t δ 0 x)
          (kpzRegularized P Z t δ' 0 y) P =
            covariance (fun v : Fin 2 → ℝ => v 0) (fun v => v 1) (P.map Fwd) := by
              simpa [Fwd, d, z] using (covariance_map_fun
                (μ := P) (Z := Fwd) (measurable_pi_apply 0).aestronglyMeasurable
                (measurable_pi_apply 1).aestronglyMeasurable hFwdAE).symm
      _ = covariance (fun v : Fin 2 → ℝ => v 0) (fun v => v 1) (P.map Rev) := by
            rw [hpointLaw]
      _ = covariance (kpzRegularizedReversed P Z 0 t δ 0 x)
            (kpzRegularizedReversed P Z 0 t δ' 0 y) P := by
              simpa [Rev, d, z] using (covariance_map_fun
                (μ := P) (Z := Rev) (measurable_pi_apply 0).aestronglyMeasurable
                (measurable_pi_apply 1).aestronglyMeasurable hRevAE)
  have hrevCovRaw : covariance
      (kpzRegularizedReversed P Z 0 t δ 0 x)
      (kpzRegularizedReversed P Z 0 t δ' 0 y) P = covariance Y0 Y1 P := by
    rw [hRevField0, hRevField1]
    rw [covariance_sub_const_left (hY0mem.integrable (by norm_num))]
    exact covariance_sub_const_right (hY1mem.integrable (by norm_num)) _
  refine ⟨hFwd0, ?_, ?_⟩
  · rw [hcovLaw, hrevCovRaw]
    exact hrawNonneg
  · rw [hcovLaw, hrevCovRaw]
    exact hrawUpper

end Critical2DKPZ.LocalSobolev

end
