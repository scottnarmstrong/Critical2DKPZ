/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.JointConvergence.ThmToyJointConvergence
public import Critical2DKPZ.Definitions.IsCriticalKPZ
public import Critical2DKPZ.JointConvergence.ThmToyJointLimitEstimates
public import Critical2DKPZ.JointConvergence.ThmToyJointLimitHighLp
public import Critical2DKPZ.JointConvergence.ThmToyJointLimitLattice
import Critical2DKPZ.SHF.Tsai.FiniteVectorConvergence
import Mathlib.Tactic

/-! # Fixed-time limits for the reversed KPZ test fields -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open Critical2DKPZ.SHF.Limit
open scoped BoundedContinuousFunction ENNReal Topology

namespace Critical2DKPZ.JointConvergence

private theorem integral_sq_mean_le_of_uniform_square
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {f : Ω → ℝ} (hf : AEStronglyMeasurable f P)
    (hfsq : Integrable (fun ω => |f ω| ^ 2) P)
    {M : ℝ} (hM : ∫ ω, |f ω| ^ 2 ∂P ≤ M) :
    (∫ ω, f ω ∂P) ^ 2 ≤ M := by
  have hmem : MemLp f 2 P := (memLp_two_iff_integrable_sq hf).2 (by simpa [sq_abs] using hfsq)
  have hHolder : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hmem' : MemLp f (ENNReal.ofReal (2 : ℝ)) P := by simpa using hmem
  have hone : MemLp (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) P := by
    simpa using (memLp_const (1 : ℝ) : MemLp (fun _ : Ω => (1 : ℝ)) 2 P)
  have hCS := integral_mul_norm_le_Lp_mul_Lq hHolder hmem' hone
  have hbound : |∫ ω, f ω ∂P| ≤ (∫ ω, |f ω| ^ 2 ∂P) ^ (1 / 2 : ℝ) := by
    calc
      |∫ ω, f ω ∂P| = ‖∫ ω, f ω ∂P‖ := by rw [Real.norm_eq_abs]
      _ ≤ ∫ ω, ‖f ω‖ ∂P := norm_integral_le_integral_norm _
      _ = ∫ ω, ‖f ω‖ * ‖(1 : ℝ)‖ ∂P := by simp
      _ ≤ (∫ ω, ‖f ω‖ ^ 2 ∂P) ^ (1 / 2 : ℝ) *
          (∫ ω, ‖(1 : ℝ)‖ ^ 2 ∂P) ^ (1 / 2 : ℝ) := hCS
      _ = (∫ ω, |f ω| ^ 2 ∂P) ^ (1 / 2 : ℝ) := by simp [Real.norm_eq_abs]
  have hnonneg : 0 ≤ ∫ ω, |f ω| ^ 2 ∂P :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun ω => sq_nonneg _)
  have hroot : ((∫ ω, |f ω| ^ 2 ∂P) ^ (1 / 2 : ℝ)) ^ 2 =
      ∫ ω, |f ω| ^ 2 ∂P := by
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hnonneg]
  calc
    (∫ ω, f ω ∂P) ^ 2 = |∫ ω, f ω ∂P| ^ 2 := by rw [sq_abs]
    _ ≤ ((∫ ω, |f ω| ^ 2 ∂P) ^ (1 / 2 : ℝ)) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) (Real.rpow_nonneg hnonneg _)).2 hbound
    _ = ∫ ω, |f ω| ^ 2 ∂P := hroot
    _ ≤ M := hM

private theorem ae_eq_of_vanishing_l2_approximations
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℝ → Ω → ℝ) (X X' : Ω → ℝ) (ε ε' : ℝ → ℝ) (δ₁ : ℝ)
    (hδ₁ : 0 < δ₁)
    (hε : Tendsto ε (𝓝[>] 0) (𝓝 0)) (hε' : Tendsto ε' (𝓝[>] 0) (𝓝 0))
    (hε0 : ∀ δ ∈ Set.Ioo 0 δ₁, 0 ≤ ε δ)
    (hε'0 : ∀ δ ∈ Set.Ioo 0 δ₁, 0 ≤ ε' δ)
    (hX : ∀ δ ∈ Set.Ioo 0 δ₁,
      eLpNorm (fun ω => Y δ ω - X ω) 2 P ≤ ENNReal.ofReal (ε δ))
    (hX' : ∀ δ ∈ Set.Ioo 0 δ₁,
      eLpNorm (fun ω => Y δ ω - X' ω) 2 P ≤ ENNReal.ofReal (ε' δ)) :
    X =ᵐ[P] X' := by
  have hbound (δ : ℝ) (hδ : δ ∈ Set.Ioo 0 δ₁) :
      eLpNorm (fun ω => X ω - X' ω) 2 P ≤ ENNReal.ofReal (ε δ + ε' δ) := by
    calc
      eLpNorm (fun ω => X ω - X' ω) 2 P =
          eLpNorm (fun ω => X' ω - X ω) 2 P := eLpNorm_sub_comm X X' 2 P
      _ = eLpNorm (fun ω => (Y δ ω - X ω) - (Y δ ω - X' ω)) 2 P := by
            congr 1
            funext ω
            ring
      _ ≤ eLpNorm (fun ω => Y δ ω - X ω) 2 P +
          eLpNorm (fun ω => Y δ ω - X' ω) 2 P := eLpNorm_sub_le (by norm_num)
      _ ≤ ENNReal.ofReal (ε δ) + ENNReal.ofReal (ε' δ) :=
        add_le_add (hX δ hδ) (hX' δ hδ)
      _ ≤ ENNReal.ofReal (ε δ + ε' δ) := by
        rw [← ENNReal.ofReal_add (hε0 δ hδ) (hε'0 δ hδ)]
  have hsum : Tendsto (fun δ : ℝ => ENNReal.ofReal (ε δ + ε' δ))
      (𝓝[>] 0) (𝓝 0) := by
    simpa [Function.comp_def] using
      (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hε.add hε'))
  have hδ : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ < δ₁ :=
    nhdsWithin_le_nhds (Iio_mem_nhds hδ₁)
  have hconst : Tendsto (fun _ : ℝ => eLpNorm (fun ω => X ω - X' ω) 2 P)
      (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Filter.Eventually.of_forall fun _ => bot_le) ?_
    have hδpos : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
    filter_upwards [hδ, hδpos] with δ hδ hδpos
    exact hbound δ ⟨hδpos, hδ⟩
  have hzero : eLpNorm (fun ω => X ω - X' ω) 2 P = 0 := by
    exact (tendsto_nhds_unique hconst tendsto_const_nhds).symm
  have hzeroAE := (eLpNorm_eq_zero_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0)).mp hzero
  filter_upwards [hzeroAE] with ω hω
  exact sub_eq_zero.mp hω

private theorem tendsto_abs_log_inv40 :
    Tendsto (fun δ : ℝ => |Real.log δ| ^ (-(1 : ℝ) / 40))
      (𝓝[>] 0) (𝓝 0) := by
  have hlog : Tendsto (fun δ : ℝ => |Real.log δ|) (𝓝[>] 0) atTop :=
    tendsto_abs_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hpow := (tendsto_rpow_neg_atTop (y := (1 : ℝ) / 40) (by norm_num)).comp hlog
  have hexp : -(1 : ℝ) / 40 = -(1 / 40 : ℝ) := by ring
  simpa only [Function.comp_def, hexp] using hpow

private theorem log_rpow_scale_bound (a T c δ : ℝ)
    (ha : 0 < a) (hc : a ≤ c) (hcT : c ≤ T)
    (hδ : 0 < δ) (hδa : δ < a / 2)
    (hδexp : δ < Real.exp (-(max |Real.log a| |Real.log T| + 1))) :
    |Real.log δ| ^ (-(1 : ℝ) / 40) ≤
      ((2 : ℝ) ^ (-(1 : ℝ) / 40))⁻¹ * |Real.log (δ / c)| ^ (-(1 : ℝ) / 40) := by
  let K : ℝ := max |Real.log a| |Real.log T|
  let A : ℝ := |Real.log δ|
  let B : ℝ := |Real.log (δ / c)|
  have hlogδ : Real.log δ < -(K + 1) := by
    calc
      Real.log δ < Real.log (Real.exp (-(K + 1))) := Real.log_lt_log hδ hδexp
      _ = -(K + 1) := Real.log_exp _
  have hKnonneg : 0 ≤ K := by dsimp [K]; positivity
  have hlogδneg : Real.log δ < 0 := by linarith [hlogδ, hKnonneg]
  have hA : A = -Real.log δ := by dsimp [A]; exact abs_of_neg hlogδneg
  have hK : |Real.log c| ≤ K := by
    have haAbs : |Real.log a| ≤ K := le_max_left _ _
    have hTAbs : |Real.log T| ≤ K := le_max_right _ _
    have haBounds : -K ≤ Real.log a ∧ Real.log a ≤ K := abs_le.mp haAbs
    have hTBounds : -K ≤ Real.log T ∧ Real.log T ≤ K := abs_le.mp hTAbs
    apply abs_le.mpr
    constructor
    · exact haBounds.1.trans (Real.log_le_log ha hc)
    · exact (Real.log_le_log (lt_of_lt_of_le ha hc) hcT).trans hTBounds.2
  have hAlarge : K ≤ A := by rw [hA]; dsimp [K] at hlogδ; linarith [hlogδ]
  have hratio : 0 < δ / c := div_pos hδ (lt_of_lt_of_le ha hc)
  have hratio1 : δ / c < 1 := (div_lt_one (lt_of_lt_of_le ha hc)).2 (by linarith [hδa, hc])
  have hlogratio : Real.log (δ / c) < 0 := Real.log_neg hratio hratio1
  have hB : B = -Real.log (δ / c) := by dsimp [B]; exact abs_of_neg hlogratio
  have hBbound : B ≤ 2 * A := by
    rw [hB, Real.log_div hδ.ne' (lt_of_lt_of_le ha hc).ne', hA]
    have hlogc_le : Real.log c ≤ K := (abs_le.mp hK).2
    linarith [hAlarge, hlogc_le]
  have hBpos : 0 < B := by rw [hB]; linarith [hlogratio]
  have hBhalf : B / 2 ≤ A := by nlinarith [hBbound]
  have hpow := Real.rpow_le_rpow_of_nonpos (div_pos hBpos (by norm_num)) hBhalf
    (by norm_num : -(1 : ℝ) / 40 ≤ 0)
  calc
    A ^ (-(1 : ℝ) / 40) ≤ (B / 2) ^ (-(1 : ℝ) / 40) := hpow
    _ = B ^ (-(1 : ℝ) / 40) / (2 : ℝ) ^ (-(1 : ℝ) / 40) :=
      Real.div_rpow hBpos.le (by norm_num) _
    _ = ((2 : ℝ) ^ (-(1 : ℝ) / 40))⁻¹ * B ^ (-(1 : ℝ) / 40) := by ring

private theorem logarithmic_width_scale_bound (c δ : ℝ) (hc : 0 < c)
    (hδ : 0 < δ) :
    1 + Real.log (1 + |Real.log δ|) ≤
      (1 + Real.log (1 + |Real.log c|)) *
        (1 + Real.log (1 + |Real.log (δ / c)|)) := by
  let H : ℝ := |Real.log c|
  let L : ℝ := |Real.log (δ / c)|
  let A : ℝ := 1 + Real.log (1 + H)
  let B : ℝ := 1 + Real.log (1 + L)
  have hlogδ : Real.log δ = Real.log (δ / c) + Real.log c := by
    rw [Real.log_div hδ.ne' hc.ne']
    ring
  have hsum : |Real.log δ| ≤ L + H := by
    rw [hlogδ]
    exact abs_add_le _ _
  have hprod : 1 + |Real.log δ| ≤ (1 + L) * (1 + H) := by
    dsimp [L, H]
    nlinarith [hsum, abs_nonneg (Real.log (δ / c)), abs_nonneg (Real.log c)]
  have hlogs : Real.log (1 + |Real.log δ|) ≤
      Real.log (1 + L) + Real.log (1 + H) := by
    calc
      Real.log (1 + |Real.log δ|) ≤ Real.log ((1 + L) * (1 + H)) :=
        Real.log_le_log (by positivity) hprod
      _ = Real.log (1 + L) + Real.log (1 + H) := by
        rw [Real.log_mul (by positivity) (by positivity)]
  have hlogL : 0 ≤ Real.log (1 + L) :=
    Real.log_nonneg (by dsimp [L]; have := abs_nonneg (Real.log (δ / c)); linarith)
  have hlogH : 0 ≤ Real.log (1 + H) :=
    Real.log_nonneg (by dsimp [H]; have := abs_nonneg (Real.log c); linarith)
  have hA : 1 ≤ A := by dsimp [A]; linarith
  have hAB : A + Real.log (1 + L) ≤ A * B := by
    dsimp [A, B]
    nlinarith [mul_nonneg hlogH hlogL]
  calc
    1 + Real.log (1 + |Real.log δ|) ≤
        1 + Real.log (1 + L) + Real.log (1 + H) :=
      calc
        1 + Real.log (1 + |Real.log δ|) =
            Real.log (1 + |Real.log δ|) + 1 := by ring
        _ ≤ (Real.log (1 + L) + Real.log (1 + H)) + 1 :=
          by nlinarith [hlogs]
        _ = 1 + Real.log (1 + L) + Real.log (1 + H) := by ring
    _ = A + Real.log (1 + L) := by dsimp [A]; ring
    _ ≤ A * B := hAB
    _ = (1 + Real.log (1 + |Real.log c|)) *
        (1 + Real.log (1 + |Real.log (δ / c)|)) := by rfl

private theorem exists_kpzRegularizedReversed_test_L2_limit
    (ϑ : ℝ) {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
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
    (T t a : ℝ) (ha : 0 < a)
    (ht : 0 ≤ t) (hta : t ≤ T - a)
    (h₀ : Plane →ᵇ ℝ) (φ : TestFn)
    (C δc : ℝ) (hC : 0 ≤ C)
    (δ₁ : ℝ) (hδ₁ : 0 < δ₁) (hδ₁c : δ₁ ≤ δc)
    (hδ₁a : δ₁ ≤ a / 2)
    (hδ₁exp : δ₁ ≤ Real.exp (-(max |Real.log a| |Real.log T| + 1)))
    (hCauchy : ∀ δ δ' : ℝ, 0 < δ → 0 < δ' → δ < δc → δ' < δc →
      ∀ t : ℝ, 0 ≤ t → t ≤ T - a → t + δ < T → t + δ' < T →
        eLpNorm (fun ω =>
          (∫ x, φ x * kpzRegularizedReversed P Z t T δ h₀ x ω) -
            (∫ x, φ x * kpzRegularizedReversed P Z t T δ' h₀ x ω)) 2 P ≤
          ENNReal.ofReal (C * (|Real.log δ| ^ (-(1 : ℝ) / 40) +
            |Real.log δ'| ^ (-(1 : ℝ) / 40))))
    :
    ∃ X : Ω → ℝ, Measurable[shfSigma Z] X ∧
        (∀ δ ∈ Set.Ioo 0 δ₁,
          eLpNorm (fun ω => (∫ x, φ x * kpzRegularizedReversed P Z t T δ h₀ x ω) -
            X ω) 2 P ≤ ENNReal.ofReal (C * |Real.log δ| ^ (-(1 : ℝ) / 40))) ∧
        (∀ δ ∈ Set.Ioo 0 δ₁,
          eLpNorm (fun ω => (∫ x, φ x * kpzRegularizedReversed P Z t T δ h₀ x ω) -
            X ω) 2 P ≤ ENNReal.ofReal ((C * ((2 : ℝ) ^ (-(1 : ℝ) / 40))⁻¹) *
              |Real.log (δ / (T - t))| ^ (-(1 : ℝ) / 40))) := by
  classical
  let K : ℝ := ((2 : ℝ) ^ (-(1 : ℝ) / 40))⁻¹
  let Y : ℝ → Ω → ℝ := fun δ ω => ∫ x,
    φ x * kpzRegularizedReversed P Z t T δ h₀ x ω
  have hrep : ∀ δ ∈ Set.Ioo 0 δ₁, ∃ f : Ω → ℝ,
      Measurable[shfSigma Z] f ∧ f =ᵐ[P] Y δ := by
    intro δ hδ
    have hsT : t + δ < T := by linarith [hta, hδ.2, hδ₁a]
    obtain ⟨f, hf, hAE⟩ := exists_shfSigma_measurable_kpzRegularizedReversed_integral
      ϑ P Z hZ t T δ ht hδ.1 hsT h₀ φ
    exact ⟨f, hf, hAE⟩
  have hmem : ∀ δ ∈ Set.Ioo 0 δ₁, MemLp (Y δ) 2 P := by
    intro δ hδ
    have hs : 0 ≤ t + δ := by linarith [ht, hδ.1]
    have hsT : t + δ < T := by linarith [hta, hδ.2, hδ₁a]
    let s : ℝ := t + δ
    let G : Plane × Ω → ℝ := fun q => Real.log
      (shfPairing Z s T (fun y => heatKernel δ (y - q.1))
        (fun y => Real.exp (h₀ y)) q.2)
    have hg : Measurable (fun y : Plane => Real.exp (h₀ y)) :=
      Real.continuous_exp.measurable.comp h₀.continuous.measurable
    have hlocal : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (Z s T ω) := by
      filter_upwards [(hZ.2.1 s T hs (by dsimp [s]; exact hsT)).mono
        (fun ω hω => hω.1)] with ω hω
      exact hω
    have hG : AEMeasurable G (volume.prod P) := by
      exact aemeasurable_log_heatPairing_joint P (Z s T)
        (hZ.1 s T hs (by dsimp [s]; exact hsT)) hlocal δ hδ.1
        (fun y => Real.exp (h₀ y)) hg (fun y => (Real.exp_pos _).le)
    have hGsec (x : Plane) : AEStronglyMeasurable (fun ω => G (x, ω)) P := by
      dsimp [G]
      exact (hpos s T δ x h₀ hs (by dsimp [s]; exact hsT) hδ.1).2.aestronglyMeasurable
    obtain ⟨M₁, hM₁, hSq₁⟩ := shf_heatStartLogField_square_bound
      ϑ P Z hZ hpair hjoint hpos T h₀ (s := s) (δ := δ) hs
      (by dsimp [s]; exact hsT) hδ.1
    let G₀ : Plane × Ω → ℝ := fun q => Real.log
      (shfPairing Z s T (fun y => heatKernel δ (y - q.1)) (fun _ => 1) q.2)
    have hG₀ : AEMeasurable G₀ (volume.prod P) := by
      exact aemeasurable_log_heatPairing_joint P (Z s T)
        (hZ.1 s T hs (by dsimp [s]; exact hsT)) hlocal δ hδ.1
        (fun _ => (1 : ℝ)) (by fun_prop) (fun _ => le_of_lt zero_lt_one)
    have hG₀sec (x : Plane) : AEStronglyMeasurable (fun ω => G₀ (x, ω)) P := by
      simpa [G₀] using
        (hpos s T δ x 0 hs (by dsimp [s]; exact hsT) hδ.1).2.aestronglyMeasurable
    obtain ⟨M₀, hM₀, hSq₀⟩ := shf_heatStartLogField_square_bound
      ϑ P Z hZ hpair hjoint hpos T (0 : Plane →ᵇ ℝ) (s := s) (δ := δ) hs
      (by dsimp [s]; exact hsT) hδ.1
    let c : ℝ := ∫ ω, G₀ (0, ω) ∂P
    have hcSq : c ^ 2 ≤ M₀ := by
      have hSqMean := (hSq₀ 0).1
      have hSqBound := (hSq₀ 0).2
      simpa [c, G₀] using
        (integral_sq_mean_le_of_uniform_square P (hG₀sec 0)
          (by simpa [G₀] using hSqMean) (by simpa [G₀] using hSqBound))
    have hM : 0 ≤ M₁ + M₀ := add_nonneg hM₁ hM₀
    have hSq (x : Plane) : Integrable (fun ω => |G (x, ω)| ^ 2) P ∧
        ∫ ω, |G (x, ω)| ^ 2 ∂P ≤ M₁ + M₀ := by
      refine ⟨(hSq₁ x).1, ?_⟩
      exact (hSq₁ x).2.trans (le_add_of_nonneg_right hM₀)
    have hcSq' : c ^ 2 ≤ M₁ + M₀ := by linarith
    have hcentered := memLp_integral_test_sub_const_of_uniform_square
      P hG hGsec hM hSq hcSq' φ
    simpa [Y, s, G, G₀, c, kpzRegularizedReversed, shfPairing] using hcentered
  have hCauchyY : ∀ δ ∈ Set.Ioo 0 δ₁, ∀ δ' ∈ Set.Ioo 0 δ₁,
      eLpNorm (fun ω => Y δ ω - Y δ' ω) 2 P ≤
        ENNReal.ofReal (C * (|Real.log δ| ^ (-(1 : ℝ) / 40) +
          |Real.log δ'| ^ (-(1 : ℝ) / 40))) := by
    intro δ hδ δ' hδ'
    have hδT : t + δ < T := by linarith [hta, hδ.2, hδ₁a]
    have hδ'T : t + δ' < T := by linarith [hta, hδ'.2, hδ₁a]
    simpa [Y] using hCauchy δ δ' hδ.1 hδ'.1
      (lt_of_lt_of_le hδ.2 hδ₁c) (lt_of_lt_of_le hδ'.2 hδ₁c)
      t ht hta hδT hδ'T
  have hm : shfSigma Z ≤ (inferInstance : MeasurableSpace Ω) := by
    dsimp [shfSigma]
    apply iSup_le
    intro s
    apply iSup_le
    intro u
    apply iSup_le
    intro hsu
    exact (hZ.1 s u hsu.1 hsu.2).comap_le
  obtain ⟨X, hXm, hRate⟩ :=
    @exists_L2_limit_of_log_cauchy_ae_representatives Ω mΩ (shfSigma Z) hm P inferInstance
      Y C δ₁ hC hrep hmem hCauchyY
  refine ⟨X, hXm, ?_, ?_⟩
  · intro δ hδ
    simpa [Y] using hRate δ hδ
  · intro δ hδ
    have hδa : δ < a / 2 := lt_of_lt_of_le hδ.2 hδ₁a
    have hδexp : δ < Real.exp (-(max |Real.log a| |Real.log T| + 1)) :=
      lt_of_lt_of_le hδ.2 hδ₁exp
    have hca : a ≤ T - t := by linarith [hta]
    have hct : T - t ≤ T := by linarith [ht]
    have hpow := log_rpow_scale_bound a T (T - t) δ ha hca hct hδ.1 hδa hδexp
    have hreal : C * |Real.log δ| ^ (-(1 : ℝ) / 40) ≤
        (C * K) * |Real.log (δ / (T - t))| ^ (-(1 : ℝ) / 40) := by
      calc
        _ ≤ C * (K * |Real.log (δ / (T - t))| ^ (-(1 : ℝ) / 40)) :=
          mul_le_mul_of_nonneg_left hpow hC
        _ = _ := by dsimp [K]; ring
    calc
      _ ≤ ENNReal.ofReal (C * |Real.log δ| ^ (-(1 : ℝ) / 40)) := hRate δ hδ
      _ ≤ ENNReal.ofReal ((C * K) *
          |Real.log (δ / (T - t))| ^ (-(1 : ℝ) / 40)) := ENNReal.ofReal_le_ofReal hreal

private theorem exists_thm_toy_joint_l2_family
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
    (hC11 : ExtensionApproxBound) (T : ℝ) (hT : 0 < T) :
    ∃ X : ℝ → (Plane →ᵇ ℝ) → TestFn → Ω → ℝ,
      (∀ (t : ℝ) (h₀ : Plane →ᵇ ℝ) (φ : TestFn), 0 ≤ t → t < T →
        Measurable[shfSigma Z] (X t h₀ φ)) ∧
      (∀ (h₀ : Plane →ᵇ ℝ) (φ : TestFn) (a : ℝ), 0 < a → a ≤ T →
        ∃ C δ₁ : ℝ, 0 < δ₁ ∧
          ∀ δ : ℝ, 0 < δ → δ < δ₁ → ∀ t : ℝ, 0 ≤ t → t ≤ T - a →
            eLpNorm (fun ω =>
              (∫ x, φ x * kpzRegularizedReversed P Z t T δ h₀ x ω) - X t h₀ φ ω) 2 P ≤
              ENNReal.ofReal (C * |Real.log (δ / (T - t))| ^ (-(1 : ℝ) / 40))) := by
  classical
  have hLocal (t : ℝ) (h₀ : Plane →ᵇ ℝ) (φ : TestFn)
      (ht : 0 ≤ t) (htT : t < T) :
      ∃ X₀ : Ω → ℝ, Measurable[shfSigma Z] X₀ ∧
        ∃ C₀ δ₀ : ℝ, 0 ≤ C₀ ∧ 0 < δ₀ ∧
          ∀ δ ∈ Set.Ioo 0 δ₀,
            eLpNorm (fun ω =>
              (∫ x, φ x * kpzRegularizedReversed P Z t T δ h₀ x ω) - X₀ ω) 2 P ≤
              ENNReal.ofReal (C₀ * |Real.log δ| ^ (-(1 : ℝ) / 40)) := by
    let a₀ : ℝ := (T - t) / 2
    have ha₀ : 0 < a₀ := by dsimp [a₀]; linarith
    have ha₀T : a₀ ≤ T := by dsimp [a₀]; linarith
    have hta₀ : t ≤ T - a₀ := by dsimp [a₀]; linarith
    obtain ⟨C₀, δc₀, hC₀, hδc₀, hCauchy₀⟩ :=
      kpzRegularizedReversed_eLpNorm_sub_le_of_lattice_smoothing ϑ P Z hZ hpair hjoint hpos hC11
        T a₀ ha₀ ha₀T h₀ φ
    let δ₀ : ℝ := min δc₀
      (min (a₀ / 2) (Real.exp (-(max |Real.log a₀| |Real.log T| + 1))))
    have hδ₀ : 0 < δ₀ := by dsimp [δ₀]; positivity
    have hδ₀c : δ₀ ≤ δc₀ := by dsimp [δ₀]; exact min_le_left _ _
    have hδ₀a : δ₀ ≤ a₀ / 2 := by
      dsimp [δ₀]
      exact (min_le_right _ _).trans (min_le_left _ _)
    have hδ₀exp : δ₀ ≤ Real.exp (-(max |Real.log a₀| |Real.log T| + 1)) := by
      dsimp [δ₀]
      exact (min_le_right _ _).trans (min_le_right _ _)
    obtain ⟨X₀, hX₀, hRate₀, _⟩ := exists_kpzRegularizedReversed_test_L2_limit
      ϑ P Z hZ hpair hjoint hpos T t a₀ ha₀ ht hta₀ h₀ φ C₀ δc₀ hC₀
      δ₀ hδ₀ hδ₀c hδ₀a hδ₀exp hCauchy₀
    exact ⟨X₀, hX₀, C₀, δ₀, hC₀, hδ₀, hRate₀⟩
  let X : ℝ → (Plane →ᵇ ℝ) → TestFn → Ω → ℝ := fun t h₀ φ =>
    if ht : 0 ≤ t ∧ t < T then Classical.choose (hLocal t h₀ φ ht.1 ht.2)
    else fun _ => 0
  refine ⟨X, ?_, ?_⟩
  · intro t h₀ φ ht htT
    have hXeq : X t h₀ φ = Classical.choose (hLocal t h₀ φ ht htT) := by
      simp [X, ht, htT]
    rw [hXeq]
    exact (Classical.choose_spec (hLocal t h₀ φ ht htT)).1
  · intro h₀ φ a ha haT
    obtain ⟨C, δc, hC, hδc, hCauchy⟩ :=
      kpzRegularizedReversed_eLpNorm_sub_le_of_lattice_smoothing ϑ P Z hZ hpair hjoint hpos hC11
        T a ha haT h₀ φ
    let K : ℝ := ((2 : ℝ) ^ (-(1 : ℝ) / 40))⁻¹
    let δlocal : ℝ := min δc (min (a / 2)
      (Real.exp (-(max |Real.log a| |Real.log T| + 1))))
    have hδlocal : 0 < δlocal := by dsimp [δlocal]; positivity
    have hδlocalc : δlocal ≤ δc := by dsimp [δlocal]; exact min_le_left _ _
    have hδlocala : δlocal ≤ a / 2 := by
      dsimp [δlocal]
      exact (min_le_right _ _).trans (min_le_left _ _)
    have hδlocalexp : δlocal ≤ Real.exp (-(max |Real.log a| |Real.log T| + 1)) := by
      dsimp [δlocal]
      exact (min_le_right _ _).trans (min_le_right _ _)
    refine ⟨C * K, δlocal, hδlocal, ?_⟩
    intro δ hδ hδ₁ t ht hta
    have htT : t < T := by linarith [hta, ha]
    have hXeq : X t h₀ φ = Classical.choose (hLocal t h₀ φ ht htT) := by
      simp [X, ht, htT]
    have hchosen := Classical.choose_spec (hLocal t h₀ φ ht htT)
    rcases hchosen with ⟨hXmeas, C₀, δ₀, hC₀, hδ₀, hRate₀⟩
    obtain ⟨X₀, hX₀meas, hRateLocal, hRateLocalScaled⟩ :=
      exists_kpzRegularizedReversed_test_L2_limit ϑ P Z hZ hpair hjoint hpos
        T t a ha ht hta h₀ φ C δc hC δlocal hδlocal hδlocalc hδlocala hδlocalexp hCauchy
    let δcommon : ℝ := min δ₀ δlocal
    have hδcommon : 0 < δcommon := by dsimp [δcommon]; positivity
    let Y : ℝ → Ω → ℝ := fun δ ω =>
      ∫ x, φ x * kpzRegularizedReversed P Z t T δ h₀ x ω
    let ε : ℝ → ℝ := fun δ => C₀ * |Real.log δ| ^ (-(1 : ℝ) / 40)
    let ε' : ℝ → ℝ := fun δ => C * |Real.log δ| ^ (-(1 : ℝ) / 40)
    have hε : Tendsto ε (𝓝[>] 0) (𝓝 0) := by
      simpa [ε, mul_comm] using tendsto_abs_log_inv40.const_mul C₀
    have hε' : Tendsto ε' (𝓝[>] 0) (𝓝 0) := by
      simpa [ε', mul_comm] using tendsto_abs_log_inv40.const_mul C
    have hε0 : ∀ δ ∈ Set.Ioo 0 δcommon, 0 ≤ ε δ := by
      intro δ _
      dsimp [ε]
      exact mul_nonneg hC₀ (Real.rpow_nonneg (abs_nonneg _) _)
    have hε'0 : ∀ δ ∈ Set.Ioo 0 δcommon, 0 ≤ ε' δ := by
      intro δ _
      dsimp [ε']
      exact mul_nonneg hC (Real.rpow_nonneg (abs_nonneg _) _)
    have hEq : Classical.choose (hLocal t h₀ φ ht htT) =ᵐ[P] X₀ :=
      ae_eq_of_vanishing_l2_approximations P Y
        (Classical.choose (hLocal t h₀ φ ht htT)) X₀ ε ε' δcommon hδcommon
        hε hε' hε0 hε'0
        (fun δ hδ => (hRate₀ δ ⟨hδ.1,
          lt_of_lt_of_le hδ.2 (by dsimp [δcommon]; exact min_le_left _ _)⟩))
        (fun δ hδ => hRateLocal δ
          ⟨hδ.1, lt_of_lt_of_le hδ.2 (by dsimp [δcommon]; exact min_le_right _ _)⟩)
    have hnormEq : eLpNorm (fun ω => Y δ ω - Classical.choose (hLocal t h₀ φ ht htT) ω) 2 P =
        eLpNorm (fun ω => Y δ ω - X₀ ω) 2 P := by
      apply eLpNorm_congr_ae
      filter_upwards [hEq] with ω hω
      simp only [hω]
    calc
      eLpNorm (fun ω => Y δ ω - X t h₀ φ ω) 2 P =
          eLpNorm (fun ω => Y δ ω - Classical.choose (hLocal t h₀ φ ht htT) ω) 2 P := by
        rw [hXeq]
      _ = eLpNorm (fun ω => Y δ ω - X₀ ω) 2 P := hnormEq
      _ ≤ ENNReal.ofReal ((C * K) * |Real.log (δ / (T - t))| ^ (-(1 : ℝ) / 40)) :=
        hRateLocalScaled δ ⟨hδ, hδ₁⟩

private theorem tendstoInMeasure_of_logarithmic_L2_rate
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : ℝ → Ω → ℝ) (X : Ω → ℝ)
    {c C δ₁ : ℝ} (hc : 0 < c) (hδ₁ : 0 < δ₁)
    (hrate : ∀ δ : ℝ, 0 < δ → δ < δ₁ →
      eLpNorm (fun ω => Y δ ω - X ω) 2 P ≤
        ENNReal.ofReal (C * |Real.log (δ / c)| ^ (-(1 : ℝ) / 40))) :
    TendstoInMeasure P Y (nhdsWithin 0 (Set.Ioi 0)) X := by
  have hratio0 : Tendsto (fun δ : ℝ => δ / c)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    have hdivAll : Tendsto (fun δ : ℝ => δ / c) (𝓝 0) (𝓝 0) := by
      have hcont : Continuous fun δ : ℝ => δ / c := by fun_prop
      simpa using (hcont.continuousAt (x := (0 : ℝ))).tendsto
    exact hdivAll.mono_left nhdsWithin_le_nhds
  have hratioPos : Tendsto (fun δ : ℝ => δ / c)
      (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hratio0, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact div_pos hδ hc
  have hpow : Tendsto (fun δ : ℝ => |Real.log (δ / c)| ^ (-(1 : ℝ) / 40))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    simpa only [Function.comp_def] using tendsto_abs_log_inv40.comp hratioPos
  have hrateReal : Tendsto (fun δ : ℝ => C *
      |Real.log (δ / c)| ^ (-(1 : ℝ) / 40))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    simpa only [mul_zero] using hpow.const_mul C
  have hrateENN : Tendsto (fun δ : ℝ => ENNReal.ofReal
      (C * |Real.log (δ / c)| ^ (-(1 : ℝ) / 40)))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hrateReal
  have hnorm : Tendsto (fun δ : ℝ => eLpNorm (fun ω => Y δ ω - X ω) 2 P)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hrateENN
      (Filter.Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [Ioo_mem_nhdsGT hδ₁] with δ hδ
    exact hrate δ hδ.1 hδ.2
  exact tendstoInMeasure_of_tendsto_eLpNorm (p := (2 : ℝ≥0∞)) (by norm_num) hnorm

set_option linter.style.haveILetI false in
private theorem isLocallyFinite_of_closedBall_mass (μ : Measure (Plane × Plane))
    (hμ : ∀ n : ℕ, μ (Metric.closedBall (0 : Plane × Plane) (n : ℝ)) < ∞) :
    IsLocallyFiniteMeasure μ := by
  have hfc : IsFiniteMeasureOnCompacts μ := by
    refine ⟨?_⟩
    intro K hK
    obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : Plane × Plane)
    obtain ⟨n, hn⟩ := exists_nat_gt r
    calc
      μ K ≤ μ (Metric.closedBall (0 : Plane × Plane) r) := measure_mono hr
      _ ≤ μ (Metric.closedBall (0 : Plane × Plane) (n : ℝ)) :=
        measure_mono (Metric.closedBall_subset_closedBall (le_of_lt hn))
      _ < ∞ := hμ n
  letI : IsFiniteMeasureOnCompacts μ := hfc
  infer_instance

set_option linter.style.haveILetI false in
private theorem locallyFinite_map_prodSwap {μ : Measure (Plane × Plane)}
    (hμ : IsLocallyFiniteMeasure μ) :
    IsLocallyFiniteMeasure (μ.map Prod.swap) := by
  apply isLocallyFinite_of_closedBall_mass
  intro n
  rw [Measure.map_apply measurable_swap (Metric.isClosed_closedBall.measurableSet)]
  have hpre : Prod.swap ⁻¹' Metric.closedBall (0 : Plane × Plane) (n : ℝ) =
      Metric.closedBall (0 : Plane × Plane) (n : ℝ) := by
    ext p
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm,
      Prod.swap, Prod.norm_def, sub_zero]
    rw [max_comm]
  rw [hpre]
  letI : IsLocallyFiniteMeasure μ := hμ
  exact (isCompact_closedBall (0 : Plane × Plane) (n : ℝ)).measure_lt_top

/-- A test function integral of the regularized KPZ field is almost everywhere measurable at admissible times. -/
theorem aemeasurable_integral_kpzRegularized
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (s δ : ℝ) (hsδ : δ < s) (hδ : 0 < δ) (h₀ : Plane →ᵇ ℝ) (φ : TestFn) :
    AEMeasurable (fun ω => ∫ x, φ x * kpzRegularized P Z s δ h₀ x ω) P := by
  classical
  let Zrev : ℝ → ℝ → Ω → Measure (Plane × Plane) :=
    fun a b ω => (Z (s - b) (s - a) ω).map Prod.swap
  let μ : Ω → Measure (Plane × Plane) := fun ω => (Z 0 (s - δ) ω).map Prod.swap
  have hμ : Measurable μ := by
    exact (Measure.measurable_map Prod.swap measurable_swap).comp
      (hZ.1 0 (s - δ) le_rfl (by linarith))
  have hlocal : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) := by
    filter_upwards [(hZ.2.1 0 (s - δ) le_rfl (by linarith)).mono
      (fun ω hω => hω.1)] with ω hω
    exact locallyFinite_map_prodSwap hω
  let c : ℝ := ∫ ω', Real.log
    (shfPairing Zrev δ s (fun y => heatKernel δ y) (fun _ => 1) ω') ∂P
  let g : Plane → ℝ := fun y => Real.exp (h₀ y)
  have hg : Measurable g := Real.continuous_exp.measurable.comp h₀.continuous.measurable
  have hgn : ∀ y, 0 ≤ g y := fun y => (Real.exp_pos _).le
  have hφ : Measurable (φ : Plane → ℝ) := φ.continuous.measurable
  have hameas := aemeasurable_integral_log_heatPairing P μ hμ hlocal
    δ c hδ g φ hg hgn hφ
  have hpoint (ω : Ω) (x : Plane) :
      kpzRegularized P Z s δ h₀ x ω =
        Real.log (∫ p, heatKernel δ (p.1 - x) * g p.2 ∂μ ω) - c := by
    have hrev := kpzRegularized_eq_kpzRegularizedReversed_of_reverseMeasure
      P Z s s δ h₀ x ω
    rw [hrev]
    simp [kpzRegularizedReversed, Zrev, μ, c, g, shfPairing]
  have hEq : (fun ω => ∫ x, φ x * kpzRegularized P Z s δ h₀ x ω) =
      fun ω => ∫ x, φ x *
        (Real.log (∫ p, heatKernel δ (p.1 - x) * g p.2 ∂μ ω) - c) := by
    funext ω
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change φ x * kpzRegularized P Z s δ h₀ x ω = _
      rw [hpoint ω x]
  rw [hEq]
  exact hameas

/-- Under the pairing-convergence, positivity, time-reversal and lattice-approximation hypotheses, tested reversed regularizations converge in every finite `Lᵖ` space to an SHF-measurable family, with the stated logarithmic `L²` rate.
The reversed lattice fields converge jointly in law to this family, whose finite-dimensional laws agree with those of any critical KPZ solution at reversed times. -/
theorem thm_toy_joint_of (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (T : ℝ) (hT : 0 < T)
    (hpair : ∀ {s t δ : ℝ}, 0 ≤ s → s < t → 0 < δ → ∀ (x : Plane) (g : Plane →ᵇ ℝ),
      (∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane => heatKernel δ (p.1 - x) * g p.2) (Z s t ω)) ∧
      Integrable (shfPairing Z s t (fun y => heatKernel δ (y - x)) g) P ∧
      (∫ ω, |shfPairing Z s t (fun y => heatKernel δ (y - x)) g ω| ∂P ≤ ‖g‖) ∧
      TendstoInDistribution
        (fun (N : ℕ) (ω : Disorder) => ∫ p, heatKernel δ (p.1 - x) * g p.2 ∂(polymerMeasure ϑ N s t ω))
        atTop (shfPairing Z s t (fun y => heatKernel δ (y - x)) g) (fun _ => disorderLaw) P)
    (hjoint : ∀ (k : ℕ) (s t δ : Fin k → ℝ) (x : Fin k → Plane) (g : Fin k → (Plane →ᵇ ℝ)),
      (∀ i, 0 ≤ s i ∧ s i < t i ∧ 0 < δ i) →
      TendstoInDistribution
        (fun (N : ℕ) (ω : Disorder) (i : Fin k) =>
          ∫ p, heatKernel (δ i) (p.1 - x i) * g i p.2 ∂(polymerMeasure ϑ N (s i) (t i) ω))
        atTop (fun ω i => shfPairing Z (s i) (t i) (fun y => heatKernel (δ i) (y - x i)) (g i) ω)
        (fun _ => disorderLaw) P)
    (hpos : ∀ (s t δ : ℝ) (x : Plane) (h₀ : Plane →ᵇ ℝ), 0 ≤ s → s < t → 0 < δ →
      (∀ᵐ ω ∂P, 0 < shfPairing Z s t (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω) ∧
      AEMeasurable (fun ω =>
        Real.log (shfPairing Z s t (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω)) P)
    (hrev : ∀ (k : ℕ) (s t : Fin k → ℝ), (∀ i, 0 ≤ s i ∧ s i < t i ∧ t i ≤ T) →
      P.map (fun ω i => (Z (T - t i) (T - s i) ω).map Prod.swap) = P.map (fun ω i => Z (s i) (t i) ω))
    (hC11 : ExtensionApproxBound) :
    ∃ X : ℝ → (Plane →ᵇ ℝ) → TestFn → Ω → ℝ,
      (∀ (t : ℝ) (h₀ : Plane →ᵇ ℝ) (φ : TestFn), 0 ≤ t → t < T → Measurable[shfSigma Z] (X t h₀ φ)) ∧
      (∀ (h₀ : Plane →ᵇ ℝ) (φ : TestFn) (a : ℝ), 0 < a → a ≤ T → ∃ C δ₁ : ℝ, 0 < δ₁ ∧
        ∀ δ : ℝ, 0 < δ → δ < δ₁ → ∀ t : ℝ, 0 ≤ t → t ≤ T - a →
          eLpNorm (fun ω => (∫ x, φ x * kpzRegularizedReversed P Z t T δ h₀ x ω) - X t h₀ φ ω) 2 P ≤
            ENNReal.ofReal (C * |Real.log (δ / (T - t))| ^ (-(1 : ℝ) / 40))) ∧
      (∀ (t : ℝ) (h₀ : Plane →ᵇ ℝ) (φ : TestFn) (p : ℝ≥0∞), 0 ≤ t → t < T → 1 ≤ p → p ≠ ⊤ →
        Tendsto (fun δ => eLpNorm (fun ω =>
            (∫ x, φ x * kpzRegularizedReversed P Z t T δ h₀ x ω) - X t h₀ φ ω) p P)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) ∧
      (∀ (k : ℕ) (t : Fin k → ℝ) (h₀ : Fin k → (Plane →ᵇ ℝ)) (φ : Fin k → TestFn),
        (∀ i, 0 ≤ t i ∧ t i < T) →
        TendstoInDistribution
          (fun (N : ℕ) (ω : Disorder) (i : Fin k) =>
            ∫ x, φ i x * kpzLatticeReversed ϑ N (t i) T (h₀ i) x ω)
          atTop (fun ω i => X (t i) (h₀ i) (φ i) ω) (fun _ => disorderLaw) P) ∧
      (∀ H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr, IsCriticalKPZ P Z H →
        ∀ (k : ℕ) (t : Fin k → ℝ) (h₀ : Fin k → (Plane →ᵇ ℝ)) (φ : Fin k → TestFn),
          (∀ i, 0 ≤ t i ∧ t i < T) →
          P.map (fun ω i => X (t i) (h₀ i) (φ i) ω) = P.map (fun ω i => H (T - t i) (h₀ i) ω (φ i))) := by
  classical
  obtain ⟨X, hXm, hRate⟩ := exists_thm_toy_joint_l2_family
    ϑ P Z hZ hpair hjoint hpos hC11 T hT
  refine ⟨X, hXm, hRate, ?_, ?_, ?_⟩
  · intro t h₀ φ p ht htT hp hptop
    let a : ℝ := (T - t) / 2
    have ha : 0 < a := by dsimp [a]; linarith
    have haT : a ≤ T := by dsimp [a]; linarith
    obtain ⟨C, δ₁, hδ₁, hbound⟩ := hRate h₀ φ a ha haT
    let C₀ : ℝ := max C 0
    have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; exact le_max_right _ _
    have hCC₀ : C ≤ C₀ := by dsimp [C₀]; exact le_max_left _ _
    have hc0 : 0 < T - t := by linarith
    let c : ℝ := min δ₁ (T - t)
    have hc : 0 < c := by dsimp [c]; positivity
    have hcδ : c ≤ δ₁ := by dsimp [c]; exact min_le_left _ _
    have hcc0 : c ≤ T - t := by dsimp [c]; exact min_le_right _ _
    let Y : ℝ → Ω → ℝ := fun δ ω =>
      ∫ x, φ x * kpzRegularizedReversed P Z t T δ h₀ x ω
    have hrate (δ : ℝ) (hδ : δ ∈ Set.Ioo 0 c) :
        eLpNorm (fun ω => Y δ ω - X t h₀ φ ω) 2 P ≤
          ENNReal.ofReal (C₀ * |Real.log (δ / c)| ^ (-(1 : ℝ) / 40)) := by
      have hδ₁' : δ < δ₁ := lt_of_lt_of_le hδ.2 hcδ
      have hδT : δ < T - t := lt_of_lt_of_le hδ.2 hcc0
      have hsource := hbound δ hδ.1 hδ₁' t ht (by dsimp [a]; linarith)
      have hr₁ : 0 < δ / (T - t) := div_pos hδ.1 hc0
      have hr₂ : 0 < δ / c := div_pos hδ.1 hc
      have hr₁one : δ / (T - t) < 1 := (div_lt_one hc0).2 hδT
      have hr₂one : δ / c < 1 := (div_lt_one hc).2 hδ.2
      have hlog₁ : Real.log (δ / (T - t)) < 0 := Real.log_neg hr₁ hr₁one
      have hlog₂ : Real.log (δ / c) < 0 := Real.log_neg hr₂ hr₂one
      have hratio : δ / (T - t) ≤ δ / c := by
        exact div_le_div_of_nonneg_left hδ.1.le hc hcc0
      have hlogabs : |Real.log (δ / c)| ≤ |Real.log (δ / (T - t))| := by
        rw [abs_of_neg hlog₂, abs_of_neg hlog₁]
        exact neg_le_neg (Real.log_le_log hr₁ hratio)
      have hpow := Real.rpow_le_rpow_of_nonpos
        (abs_pos.mpr (ne_of_lt hlog₂)) hlogabs
        (by norm_num : (-(1 : ℝ) / 40) ≤ 0)
      have hcoeff :
          C * |Real.log (δ / (T - t))| ^ (-(1 : ℝ) / 40) ≤
            C₀ * |Real.log (δ / c)| ^ (-(1 : ℝ) / 40) := by
        calc
          _ ≤ C₀ * |Real.log (δ / (T - t))| ^ (-(1 : ℝ) / 40) :=
            mul_le_mul_of_nonneg_right hCC₀ (Real.rpow_nonneg (abs_nonneg _) _)
          _ ≤ _ := mul_le_mul_of_nonneg_left hpow hC₀
      exact hsource.trans (ENNReal.ofReal_le_ofReal
        hcoeff)
    have hseq0 : Tendsto (fun n : ℕ => c * Real.exp (-Real.exp (n : ℝ)))
        atTop (𝓝 0) := by
      have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
      have hexp := Real.tendsto_exp_atTop.comp hn
      have hsmall := Real.tendsto_exp_neg_atTop_nhds_zero.comp hexp
      simpa using hsmall.const_mul c
    have hseqWithin : Tendsto (fun n : ℕ => c * Real.exp (-Real.exp (n : ℝ)))
        atTop (nhdsWithin 0 (Set.Ioi 0)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨hseq0, ?_⟩
      exact Filter.Eventually.of_forall fun n => mul_pos hc (Real.exp_pos _)
    have hconvSeq : TendstoInMeasure P
        (fun n : ℕ => Y (c * Real.exp (-Real.exp (n : ℝ)))) atTop (X t h₀ φ) := by
      exact (tendstoInMeasure_of_logarithmic_L2_rate P Y (X t h₀ φ)
        hc hc (by
          intro δ hδ hδc
          exact hrate δ ⟨hδ, hδc⟩)).comp hseqWithin
    have hlogBound (p' : ℝ≥0∞) (hp' : 1 ≤ p') (hp'top : p' ≠ ⊤) :
        ∃ Cp : ℝ, ∀ δ ∈ Set.Ioo 0 c,
          eLpNorm (fun ω => Y δ ω - X t h₀ φ ω) (2 * p') P ≤
            ENNReal.ofReal (Cp * (1 + Real.log (1 + |Real.log (δ / c)|))) := by
      have hpReal : 1 ≤ p'.toReal :=
        (ENNReal.toReal_le_toReal (by simp) hp'top).2 hp'
      let q : ℝ := 2 * p'.toReal + 1
      have hq : 2 < q := by dsimp [q]; linarith
      have hOfp : ENNReal.ofReal p'.toReal = p' := ENNReal.ofReal_toReal hp'top
      have hOf2p : ENNReal.ofReal (2 * p'.toReal) = 2 * p' := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        simp [hOfp]
      have hqMoment : 1 < 2 * q := by linarith
      obtain ⟨M, hM, hMomentBound⟩ :=
        kpzRegularizedReversed_test_rpow_log_width_bound
          ϑ P Z hZ hpair hjoint hpos t T c ht htT hc hcc0 h₀ φ
          (q := 2 * q) hqMoment
      have hMoment : ∃ M : ℝ, 0 ≤ M ∧ ∀ δ ∈ Set.Ioo 0 c,
          AEStronglyMeasurable (Y δ) P ∧
          Integrable (fun ω => |Y δ ω| ^ (2 * q)) P ∧
          ∫ ω, |Y δ ω| ^ (2 * q) ∂P ≤
            M * (1 + Real.log (1 + |Real.log δ|)) ^ (2 * q) := by
        refine ⟨M, hM, ?_⟩
        intro δ hδ
        simpa [Y] using hMomentBound δ hδ
      obtain ⟨Cp, hCp, hHigh⟩ := highLp_difference_log_bound
        P Y (X t h₀ φ) c c C₀ q hc hc hq hrate hMoment hconvSeq
      let A : ℝ := 1 + Real.log (1 + |Real.log c|)
      have hA : 1 ≤ A := by
        dsimp [A]
        have hlog : 0 ≤ Real.log (1 + |Real.log c|) :=
          Real.log_nonneg (by have := abs_nonneg (Real.log c); linarith)
        linarith
      refine ⟨Cp * A, ?_⟩
      intro δ hδ
      have hwidth := logarithmic_width_scale_bound c δ hc hδ.1
      have hwidth' :
          Cp * (1 + Real.log (1 + |Real.log δ|)) ≤
            Cp * A * (1 + Real.log (1 + |Real.log (δ / c)|)) := by
        dsimp [A] at hwidth ⊢
        calc
          _ ≤ Cp * ((1 + Real.log (1 + |Real.log c|)) *
              (1 + Real.log (1 + |Real.log (δ / c)|))) :=
            mul_le_mul_of_nonneg_left hwidth hCp
          _ = _ := by ring
      have hqle : 2 * p' ≤ ENNReal.ofReal q := by
        rw [← hOf2p]
        exact ENNReal.ofReal_le_ofReal (by dsimp [q]; linarith)
      exact (eLpNorm_le_eLpNorm_of_exponent_le hqle).trans
        ((hHigh δ hδ).trans (ENNReal.ofReal_le_ofReal hwidth'))
    exact tendsto_eLpNorm_of_rate_of_log_bound P Y (X t h₀ φ)
      hc hrate hlogBound p hp hptop
  · intro k t h₀ φ ht
    exact thm_toy_joint_lattice_limit_of ϑ P Z hZ T hT hpair hjoint hpos hC11 X hXm hRate
      k t h₀ φ ht
  · intro H hH k t h₀ φ ht
    let u : Fin k → ℝ := fun i => T - t i
    have hu_pos (i : Fin k) : 0 < u i := by
      dsimp [u]
      linarith [(ht i).2]
    have hu_le (i : Fin k) : u i ≤ T := by
      dsimp [u]
      linarith [(ht i).1]
    have hsmall : Tendsto (fun n : ℕ => Real.exp (-Real.exp (n : ℝ)))
        atTop (𝓝 0) := by
      have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
      exact Real.tendsto_exp_neg_atTop_nhds_zero.comp (Real.tendsto_exp_atTop.comp hn)
    have hratePack (i : Fin k) :
        ∃ C d : ℝ, 0 < d ∧ ∀ δ ∈ Set.Ioo 0 d,
          eLpNorm (fun ω =>
            (∫ x, φ i x * kpzRegularizedReversed P Z (t i) T δ (h₀ i) x ω) -
              X (t i) (h₀ i) (φ i) ω) 2 P ≤
            ENNReal.ofReal (C * |Real.log (δ / u i)| ^ (-(1 : ℝ) / 40)) := by
      let a : ℝ := u i / 2
      have ha : 0 < a := by
        dsimp [a]
        exact div_pos (hu_pos i) (by norm_num)
      have haT : a ≤ T := by dsimp [a]; linarith [hu_le i]
      obtain ⟨C, d, hd, hb⟩ := hRate (h₀ i) (φ i) a ha haT
      refine ⟨C, d, hd, ?_⟩
      intro δ hδ
      have hta : t i ≤ T - a := by
        dsimp [a, u]
        have htiT : t i ≤ T := le_of_lt (ht i).2
        nlinarith [htiT]
      exact hb δ hδ.1 hδ.2 (t i) (ht i).1 hta
    choose C d hd hbound using hratePack
    let c : Fin k → ℝ := fun i => min (d i) (u i)
    have hc (i : Fin k) : 0 < c i := by
      dsimp [c]
      exact lt_min (hd i) (hu_pos i)
    have hcd (i : Fin k) : c i ≤ d i := by
      dsimp [c]
      exact min_le_left _ _
    have hcu (i : Fin k) : c i ≤ u i := by
      dsimp [c]
      exact min_le_right _ _
    let δseq : ℕ → Fin k → ℝ := fun n i =>
      c i * Real.exp (-Real.exp (n : ℝ))
    let F : ℕ → Ω → Fin k → ℝ := fun n ω i =>
      ∫ x, φ i x * kpzRegularized P Z (u i) (δseq n i) (h₀ i) x ω
    let G : ℕ → Ω → Fin k → ℝ := fun n ω i =>
      ∫ x, φ i x * kpzRegularizedReversed P Z (t i) T (δseq n i) (h₀ i) x ω
    let LF : Ω → Fin k → ℝ := fun ω i => H (u i) (h₀ i) ω (φ i)
    let LG : Ω → Fin k → ℝ := fun ω i => X (t i) (h₀ i) (φ i) ω
    have hδpos (n : ℕ) (i : Fin k) : 0 < δseq n i := by
      dsimp [δseq]
      exact mul_pos (hc i) (Real.exp_pos _)
    have hδltc (n : ℕ) (i : Fin k) : δseq n i < c i := by
      have he : Real.exp (-Real.exp (n : ℝ)) < 1 :=
        Real.exp_lt_one_iff.mpr (neg_neg_of_pos (Real.exp_pos _))
      dsimp [δseq]
      simpa only [mul_one] using mul_lt_mul_of_pos_left he (hc i)
    have hδlt (n : ℕ) (i : Fin k) : δseq n i < u i :=
      lt_of_lt_of_le (hδltc n i) (hcu i)
    have hδtendsto (i : Fin k) :
        Tendsto (fun n : ℕ => δseq n i) atTop (nhdsWithin 0 (Set.Ioi 0)) := by
      have hzero : Tendsto (fun n : ℕ => δseq n i) atTop (𝓝 0) := by
        simpa [δseq] using hsmall.const_mul (c i)
      apply tendsto_nhdsWithin_iff.mpr
      exact ⟨hzero, Filter.Eventually.of_forall fun n => hδpos n i⟩
    have hrate (i : Fin k) (δ : ℝ) (hδ : δ ∈ Set.Ioo 0 (c i)) :
        eLpNorm (fun ω =>
          (∫ x, φ i x * kpzRegularizedReversed P Z (t i) T δ (h₀ i) x ω) -
            X (t i) (h₀ i) (φ i) ω) 2 P ≤
          ENNReal.ofReal (max (C i) 0 *
            |Real.log (δ / c i)| ^ (-(1 : ℝ) / 40)) := by
      have hsrc := hbound i δ ⟨hδ.1, lt_of_lt_of_le hδ.2 (hcd i)⟩
      have hr₁ : 0 < δ / u i := div_pos hδ.1 (hu_pos i)
      have hr₂ : 0 < δ / c i := div_pos hδ.1 (hc i)
      have hr₁one : δ / u i < 1 := (div_lt_one (hu_pos i)).2 (lt_of_lt_of_le hδ.2 (hcu i))
      have hr₂one : δ / c i < 1 := (div_lt_one (hc i)).2 hδ.2
      have hlog₁ : Real.log (δ / u i) < 0 := Real.log_neg hr₁ hr₁one
      have hlog₂ : Real.log (δ / c i) < 0 := Real.log_neg hr₂ hr₂one
      have hratio : δ / u i ≤ δ / c i :=
        div_le_div_of_nonneg_left hδ.1.le (hc i) (hcu i)
      have hlogabs : |Real.log (δ / c i)| ≤ |Real.log (δ / u i)| := by
        rw [abs_of_neg hlog₂, abs_of_neg hlog₁]
        exact neg_le_neg (Real.log_le_log hr₁ hratio)
      have hpow := Real.rpow_le_rpow_of_nonpos
        (abs_pos.mpr (ne_of_lt hlog₂)) hlogabs
        (by norm_num : (-(1 : ℝ) / 40) ≤ 0)
      have hCC₀ : C i ≤ max (C i) 0 := le_max_left _ _
      have hcoeff : C i * |Real.log (δ / u i)| ^ (-(1 : ℝ) / 40) ≤
          max (C i) 0 * |Real.log (δ / c i)| ^ (-(1 : ℝ) / 40) := by
        calc
          _ ≤ max (C i) 0 * |Real.log (δ / u i)| ^ (-(1 : ℝ) / 40) :=
            mul_le_mul_of_nonneg_right hCC₀ (Real.rpow_nonneg (abs_nonneg _) _)
          _ ≤ _ := mul_le_mul_of_nonneg_left hpow (le_max_right _ _)
      exact hsrc.trans (ENNReal.ofReal_le_ofReal hcoeff)
    have hFcoordMeas (n : ℕ) (i : Fin k) :
        AEMeasurable (fun ω => F n ω i) P := by
      apply aemeasurable_integral_kpzRegularized ϑ P Z hZ (u i) (δseq n i)
      · exact hδlt n i
      · exact hδpos n i
    have hGcoordMeas (n : ℕ) (i : Fin k) :
        AEStronglyMeasurable (fun ω => G n ω i) P := by
      obtain ⟨M, hM, hmoment⟩ := kpzRegularizedReversed_test_rpow_log_width_bound
        ϑ P Z hZ hpair hjoint hpos (t i) T (c i) (ht i).1 (ht i).2 (hc i)
        (by simpa [u] using hcu i) (h₀ i) (φ i) (q := 2) (by norm_num)
      have hδmem : δseq n i ∈ Set.Ioo 0 (c i) := by
        exact ⟨hδpos n i, hδltc n i⟩
      simpa [G] using (hmoment (δseq n i) hδmem).1
    have hFm : ∀ n, AEMeasurable (F n) P := by
      intro n
      exact AEMeasurable.of_eval (fun i => hFcoordMeas n i)
    have hGm : ∀ n, AEMeasurable (G n) P := by
      intro n
      exact AEMeasurable.of_eval (fun i => (hGcoordMeas n i).aemeasurable)
    have hFcoord (i : Fin k) :
        TendstoInMeasure P (fun n ω => F n ω i) atTop (fun ω => LF ω i) := by
      have h := hH (u i) (hu_pos i) (h₀ i) (φ i)
      have hs := h.comp (hδtendsto i)
      simpa [F, LF, Function.comp_def] using hs
    have hGcoord (i : Fin k) :
        TendstoInMeasure P (fun n ω => G n ω i) atTop (fun ω => LG ω i) := by
      let Y : ℝ → Ω → ℝ := fun δ ω =>
        ∫ x, φ i x * kpzRegularizedReversed P Z (t i) T δ (h₀ i) x ω
      have hδconv := tendstoInMeasure_of_logarithmic_L2_rate P Y
        (X (t i) (h₀ i) (φ i)) (c := c i) (C := max (C i) 0) (δ₁ := c i)
        (hc i) (hc i)
        (fun δ hδ hδc => hrate i δ ⟨hδ, hδc⟩)
      have hs := hδconv.comp (hδtendsto i)
      simpa [G, LG, Y, Function.comp_def] using hs
    have hFconv : TendstoInMeasure P F atTop LF :=
      Critical2DKPZ.SHF.Tsai.tendstoInMeasure_fintype_pi P F LF hFcoord
    have hGconv : TendstoInMeasure P G atTop LG :=
      Critical2DKPZ.SHF.Tsai.tendstoInMeasure_fintype_pi P G LG hGcoord
    have hLFmeas : AEMeasurable LF P := by
      apply AEMeasurable.of_eval
      intro i
      exact TendstoInMeasure.aemeasurable (fun n => hFcoordMeas n i) (hFcoord i)
    have hSigmaLe : shfSigma Z ≤ (inferInstance : MeasurableSpace Ω) := by
      dsimp [shfSigma]
      apply iSup_le
      intro s
      apply iSup_le
      intro v
      apply iSup_le
      intro hsv
      exact (hZ.1 s v hsv.1 hsv.2).comap_le
    have hLGmeas : AEMeasurable LG P := by
      apply AEMeasurable.of_eval
      intro i
      exact ((hXm (t i) (h₀ i) (φ i) (ht i).1 (ht i).2).mono hSigmaLe le_rfl).aemeasurable
    have hlaw (n : ℕ) : P.map (F n) = P.map (G n) := by
      have hδvalid (i : Fin k) :
          0 < δseq n i ∧ δseq n i < u i ∧ u i ≤ T :=
        ⟨hδpos n i, hδlt n i, hu_le i⟩
      simpa [F, G, u] using
        kpzRegularized_reverse_law_of ϑ P Z hZ T hrev k u (δseq n) h₀ φ hδvalid
    have hmap := map_eq_of_tendstoInMeasure P F G LF LG
      hFconv hGconv hFm hGm hlaw hLFmeas hLGmeas
    exact hmap.symm

end Critical2DKPZ.JointConvergence

end
