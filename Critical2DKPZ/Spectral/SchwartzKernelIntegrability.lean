/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Spectral.BochnerSchwartz
public import Critical2DKPZ.Analysis.Sobolev.Localizers
import Mathlib.Tactic.Positivity

/-! # Schwartz pairings with polynomial-growth kernels -/

@[expose] public section

noncomputable section

open MeasureTheory
open Filter
open TopologicalSpace
open scoped ComplexConjugate

namespace Critical2DKPZ.Spectral

/-- Multiply a real Schwartz function by the canonical compactly supported localizer. -/
def cutoffSchwartzTestFn (n : ℕ) (f : SchwartzMap Plane ℝ) : TestFn where
  toFun x := Critical2DKPZ.localizer n x * f x
  contDiff' := (Critical2DKPZ.localizer n).contDiff.mul (f.smooth ⊤)
  hasCompactSupport' := (Critical2DKPZ.localizer n).hasCompactSupport.mul_right
  tsupport_subset' := fun _ _ => trivial

/-- A localized Schwartz test evaluates to the localizer times the Schwartz function. -/
@[simp] theorem cutoffSchwartzTestFn_apply (n : ℕ) (f : SchwartzMap Plane ℝ)
    (x : Plane) :
    cutoffSchwartzTestFn n f x = Critical2DKPZ.localizer n x * f x := rfl

/-- A locally square-integrable kernel with polynomial integral growth pairs integrably with
Schwartz functions on the two-variable difference kernel. -/
theorem integrable_schwartz_testProduct_kernel (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (∫ z in Metric.closedBall 0 R, |C z|) ≤ A * R ^ k)
    (f g : SchwartzMap Plane ℝ) :
    Integrable (fun p : Plane × Plane => f p.1 * g p.2 * C (p.1 - p.2))
      (volume.prod volume) := by
  obtain ⟨n, hn⟩ :=
    exists_integrable_polynomial_decay_mul_abs_of_ball_growth C hC hgrowth
  let N := n
  let Kf := 2 ^ (N - 1) *
    (SchwartzMap.seminorm ℝ 0 0 f + SchwartzMap.seminorm ℝ N 0 f)
  have hKf : 0 ≤ Kf := by
    dsimp [Kf]
    positivity
  have hf_bound (x : Plane) : (1 + ‖x‖) ^ N * |f x| ≤ Kf := by
    have hsup : |f x| ≤ SchwartzMap.seminorm ℝ 0 0 f := by
      simpa only [Real.norm_eq_abs] using SchwartzMap.norm_le_seminorm ℝ f x
    have hpow : ‖x‖ ^ N * |f x| ≤ SchwartzMap.seminorm ℝ N 0 f := by
      simpa only [Real.norm_eq_abs] using SchwartzMap.norm_pow_mul_le_seminorm ℝ f N x
    have hpoly : (1 + ‖x‖) ^ N ≤ 2 ^ (N - 1) * (1 + ‖x‖ ^ N) := by
      simpa only [one_pow] using
        add_pow_le (a := (1 : ℝ)) (b := ‖x‖) (by norm_num) (norm_nonneg x) N
    calc
      (1 + ‖x‖) ^ N * |f x| ≤
          (2 ^ (N - 1) * (1 + ‖x‖ ^ N)) * |f x| :=
        mul_le_mul_of_nonneg_right hpoly (abs_nonneg _)
      _ = 2 ^ (N - 1) * (|f x| + ‖x‖ ^ N * |f x|) := by ring
      _ ≤ Kf := by
        dsimp [Kf]
        exact mul_le_mul_of_nonneg_left (add_le_add hsup hpow) (by positivity)
  let b : Plane → ℝ := fun y => (1 + ‖y‖) ^ N * |g y|
  have hb : Integrable b volume := by
    have h0 : Integrable (fun y : Plane => |g y|) volume := by
      simpa only [Real.norm_eq_abs] using g.integrable.norm
    have hN : Integrable (fun y : Plane => ‖y‖ ^ N * |g y|) volume := by
      simpa only [Real.norm_eq_abs] using g.integrable_pow_mul volume N
    have hmajor : Integrable
        (fun y : Plane => 2 ^ (N - 1) * (|g y| + ‖y‖ ^ N * |g y|)) volume :=
      (h0.add hN).const_mul (2 ^ (N - 1))
    have hmeas : AEStronglyMeasurable b volume := by
      have hmeas : Measurable b := by
        dsimp [b]
        fun_prop
      exact hmeas.aestronglyMeasurable
    refine hmajor.mono' hmeas ?_
    filter_upwards with y
    have hpoly : (1 + ‖y‖) ^ N ≤ 2 ^ (N - 1) * (1 + ‖y‖ ^ N) := by
      simpa only [one_pow] using
        add_pow_le (a := (1 : ℝ)) (b := ‖y‖) (by norm_num) (norm_nonneg y) N
    have hpoint : b y ≤ 2 ^ (N - 1) * (|g y| + ‖y‖ ^ N * |g y|) := by
      dsimp [b]
      calc
        (1 + ‖y‖) ^ N * |g y| ≤
            (2 ^ (N - 1) * (1 + ‖y‖ ^ N)) * |g y| :=
          mul_le_mul_of_nonneg_right hpoly (abs_nonneg _)
        _ = 2 ^ (N - 1) * (|g y| + ‖y‖ ^ N * |g y|) := by ring
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (abs_nonneg _))]
    exact hpoint
  let a : Plane → ℝ := fun z => (1 + ‖z‖) ^ (-(N : ℝ)) * |C z|
  have ha : Integrable a volume := by
    simpa only [a, N] using hn
  have hab : Integrable (fun p : Plane × Plane => a p.1 * b p.2)
      (volume.prod volume) := ha.mul_prod hb
  let F : Plane × Plane → ℝ := fun p => f (p.1 + p.2) * g p.2 * C p.1
  have hFmeas : AEStronglyMeasurable F (volume.prod volume) := by
    have hloc := locallyIntegrable_of_compactMemLp_two C hC
    have hCmeas : AEStronglyMeasurable (fun p : Plane × Plane => C p.1)
        (volume.prod volume) := hloc.aestronglyMeasurable.comp_fst
    have hfmeas : AEStronglyMeasurable
        (fun p : Plane × Plane => f (p.1 + p.2)) (volume.prod volume) := by
      exact (f.continuous.comp (continuous_fst.add continuous_snd)).measurable.aestronglyMeasurable
    have hgmeas : AEStronglyMeasurable
        (fun p : Plane × Plane => g p.2) (volume.prod volume) := by
      exact (g.continuous.comp continuous_snd).measurable.aestronglyMeasurable
    dsimp [F]
    exact hfmeas.mul hgmeas |>.mul hCmeas
  have hF : Integrable F (volume.prod volume) := by
    refine hab.const_mul Kf |>.mono' hFmeas ?_
    filter_upwards with p
    rcases p with ⟨z, y⟩
    have htriangle : 1 + ‖z‖ ≤ (1 + ‖z + y‖) * (1 + ‖y‖) := by
      have hnorm : ‖z‖ ≤ ‖z + y‖ + ‖y‖ := by
        calc
          ‖z‖ = ‖(z + y) - y‖ := by congr 1; abel
          _ ≤ ‖z + y‖ + ‖y‖ := norm_sub_le _ _
      nlinarith [mul_nonneg (norm_nonneg (z + y)) (norm_nonneg y)]
    have hweight : (1 + ‖z‖) ^ N * |f (z + y)| ≤ Kf * (1 + ‖y‖) ^ N := by
      have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + ‖z‖)
        htriangle N
      calc
        (1 + ‖z‖) ^ N * |f (z + y)| ≤
            ((1 + ‖z + y‖) * (1 + ‖y‖)) ^ N * |f (z + y)| :=
          mul_le_mul_of_nonneg_right hpow (abs_nonneg _)
        _ = (1 + ‖z + y‖) ^ N * |f (z + y)| * (1 + ‖y‖) ^ N := by
          rw [mul_pow]
          ring
        _ ≤ Kf * (1 + ‖y‖) ^ N :=
          mul_le_mul_of_nonneg_right (hf_bound (z + y)) (by positivity)
    have hcancel : (1 + ‖z‖) ^ (-(N : ℝ)) * (1 + ‖z‖) ^ N = 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add (by positivity)]
      simp
    have hpoint :
        |f (z + y) * g y * C z| ≤ Kf * (a z * b y) := by
      rw [abs_mul, abs_mul]
      change |f (z + y)| * |g y| * |C z| ≤
        Kf * ((1 + ‖z‖) ^ (-(N : ℝ)) * |C z| * ((1 + ‖y‖) ^ N * |g y|))
      calc
        |f (z + y)| * |g y| * |C z| =
            ((1 + ‖z‖) ^ (-(N : ℝ)) * (1 + ‖z‖) ^ N) *
              |f (z + y)| * |g y| * |C z| := by
                rw [hcancel]
                ring
        _ = ((1 + ‖z‖) ^ (-(N : ℝ)) * |C z|) *
              ((1 + ‖z‖) ^ N * |f (z + y)|) * |g y| := by ring
        _ ≤ ((1 + ‖z‖) ^ (-(N : ℝ)) * |C z|) *
              (Kf * (1 + ‖y‖) ^ N) * |g y| := by
                gcongr
        _ = Kf *
            ((1 + ‖z‖) ^ (-(N : ℝ)) * |C z| * ((1 + ‖y‖) ^ N * |g y|)) := by
              ring
    rw [Real.norm_eq_abs]
    exact hpoint
  let e : Plane × Plane ≃ᵐ Plane × Plane := {
    toEquiv := {
      toFun := fun p => (p.1 - p.2, p.2)
      invFun := fun p => (p.1 + p.2, p.2)
      left_inv := by intro p; ext <;> simp
      right_inv := by intro p; ext <;> simp }
    measurable_toFun := (continuous_fst.sub continuous_snd).measurable.prodMk
      measurable_snd
    measurable_invFun := (continuous_fst.add continuous_snd).measurable.prodMk
      measurable_snd }
  have hmp : MeasurePreserving (fun p : Plane × Plane => (p.1 - p.2, p.2))
      (volume.prod volume) (volume.prod volume) := by
    exact measurePreserving_sub_prod volume volume
  have hcomp : Integrable (F ∘ e) (volume.prod volume) :=
    (hmp.integrable_comp_emb e.measurableEmbedding).mpr hF
  have hEq : (fun p : Plane × Plane => f p.1 * g p.2 * C (p.1 - p.2)) =ᵐ[
      volume.prod volume] (F ∘ e) := by
    filter_upwards with p
    rcases p with ⟨x, y⟩
    dsimp [F, e]
    rw [sub_add_cancel]
  exact (integrable_congr hEq).2 hcomp

/-- Compact-test positive type extends to real Schwartz functions. -/
theorem real_schwartz_kernel_quadratic_nonneg (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (∫ z in Metric.closedBall 0 R, |C z|) ≤ A * R ^ k)
    (hpos : ∀ φ : TestFn, 0 ≤ ∫ p : Plane × Plane,
      φ p.1 * φ p.2 * C (p.1 - p.2))
    (f : SchwartzMap Plane ℝ) :
    Integrable (fun p : Plane × Plane => f p.1 * f p.2 * C (p.1 - p.2))
        (volume.prod volume) ∧
      0 ≤ ∫ p : Plane × Plane,
        f p.1 * f p.2 * C (p.1 - p.2) ∂(volume.prod volume) := by
  let F : ℕ → Plane × Plane → ℝ := fun n p =>
    cutoffSchwartzTestFn n f p.1 * cutoffSchwartzTestFn n f p.2 * C (p.1 - p.2)
  let bound : Plane × Plane → ℝ := fun p =>
    ‖f p.1 * f p.2 * C (p.1 - p.2)‖
  have hboundInt : Integrable bound (volume.prod volume) := by
    simpa only [bound] using
      (integrable_schwartz_testProduct_kernel C hC hgrowth f f).norm
  have hFInt (n : ℕ) : Integrable (F n) (volume.prod volume) := by
    simpa only [MeasureTheory.Measure.volume_eq_prod, F] using
      integrable_testFnProduct_kernel C hC
        (cutoffSchwartzTestFn n f) (cutoffSchwartzTestFn n f)
  have hFMeas (n : ℕ) : AEStronglyMeasurable (F n) (volume.prod volume) :=
    (hFInt n).aestronglyMeasurable
  have hcutAbs (n : ℕ) (x : Plane) : |Critical2DKPZ.localizer n x| ≤ 1 := by
    rw [abs_of_nonneg (Critical2DKPZ.localizer_nonneg n x)]
    exact Critical2DKPZ.localizer_le_one n x
  have hdom (n : ℕ) : ∀ᵐ p : Plane × Plane ∂(volume.prod volume),
      ‖F n p‖ ≤ bound p := by
    filter_upwards with p
    rcases p with ⟨x, y⟩
    change |Critical2DKPZ.localizer n x * f x *
        (Critical2DKPZ.localizer n y * f y) * C (x - y)| ≤
      ‖f x * f y * C (x - y)‖
    simp only [Real.norm_eq_abs, abs_mul]
    have hxle : |Critical2DKPZ.localizer n x| * |f x| ≤ |f x| := by
      calc
        |Critical2DKPZ.localizer n x| * |f x| ≤ 1 * |f x| :=
          mul_le_mul_of_nonneg_right (hcutAbs n x) (abs_nonneg (f x))
        _ = |f x| := one_mul _
    have hyle : |Critical2DKPZ.localizer n y| * |f y| ≤ |f y| := by
      calc
        |Critical2DKPZ.localizer n y| * |f y| ≤ 1 * |f y| :=
          mul_le_mul_of_nonneg_right (hcutAbs n y) (abs_nonneg (f y))
        _ = |f y| := one_mul _
    calc
      |Critical2DKPZ.localizer n x| * |f x| *
          (|Critical2DKPZ.localizer n y| * |f y|) * |C (x - y)| =
        (|Critical2DKPZ.localizer n x| * |f x|) *
          (|Critical2DKPZ.localizer n y| * |f y|) * |C (x - y)| := by ring
      _ ≤ |f x| * |f y| * |C (x - y)| :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hxle hyle
            (mul_nonneg (abs_nonneg (Critical2DKPZ.localizer n y)) (abs_nonneg (f y)))
            (abs_nonneg (f x)))
          (abs_nonneg (C (x - y)))
  have hcutEq (x : Plane) :
      ∀ᶠ n : ℕ in atTop, Critical2DKPZ.localizer n x = 1 := by
    obtain ⟨N, hN⟩ :=
      Critical2DKPZ.exists_localizer_eq_one_on_compact (isCompact_singleton (x := x))
    filter_upwards [eventually_ge_atTop N] with n hn
    exact hN n hn x (Set.mem_singleton x)
  have hpoint (p : Plane × Plane) :
      Tendsto (fun n => F n p) atTop
        (nhds (f p.1 * f p.2 * C (p.1 - p.2))) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(hcutEq p.1).and (hcutEq p.2)] with n hn
    simp only [F, cutoffSchwartzTestFn_apply, hn.1, hn.2, one_mul]
  have hIntTendsto := tendsto_integral_of_dominated_convergence bound
    hFMeas hboundInt hdom (ae_of_all _ hpoint)
  have hposCut (n : ℕ) : 0 ≤ ∫ p : Plane × Plane, F n p ∂(volume.prod volume) := by
    simpa only [MeasureTheory.Measure.volume_eq_prod, F] using
      hpos (cutoffSchwartzTestFn n f)
  have hposLimit : 0 ≤ ∫ p : Plane × Plane,
      f p.1 * f p.2 * C (p.1 - p.2) ∂(volume.prod volume) :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hIntTendsto
      (Eventually.of_forall hposCut)
  exact ⟨integrable_schwartz_testProduct_kernel C hC hgrowth f f, hposLimit⟩

/-- Evenness makes the real Schwartz difference-kernel pairing symmetric. -/
theorem integral_schwartz_testProduct_kernel_comm (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (∫ z in Metric.closedBall 0 R, |C z|) ≤ A * R ^ k)
    (heven : (fun z : Plane => C (-z)) =ᵐ[volume] C)
    (f g : SchwartzMap Plane ℝ) :
    Integrable (fun p : Plane × Plane => f p.1 * g p.2 * C (p.1 - p.2))
        (volume.prod volume) ∧
      Integrable (fun p : Plane × Plane => g p.1 * f p.2 * C (p.1 - p.2))
        (volume.prod volume) ∧
      (∫ p : Plane × Plane, f p.1 * g p.2 * C (p.1 - p.2)) =
        ∫ p : Plane × Plane, g p.1 * f p.2 * C (p.1 - p.2) := by
  have hEvenProd : ∀ᵐ p : Plane × Plane ∂(volume.prod volume),
      C (p.1 - p.2) = C (p.2 - p.1) := by
    have h := (quasiMeasurePreserving_sub_of_right_invariant volume volume).tendsto_ae heven
    filter_upwards [h] with p hp
    simpa only [neg_sub] using hp.symm
  refine ⟨integrable_schwartz_testProduct_kernel C hC hgrowth f g,
    integrable_schwartz_testProduct_kernel C hC hgrowth g f, ?_⟩
  calc
    (∫ p : Plane × Plane, f p.1 * g p.2 * C (p.1 - p.2)) =
        ∫ p : Plane × Plane, f p.1 * g p.2 * C (p.2 - p.1) := by
      apply integral_congr_ae
      filter_upwards [hEvenProd] with p hp
      rw [hp]
    _ = ∫ p : Plane × Plane, g p.2 * f p.1 * C (p.2 - p.1) := by
      apply integral_congr_ae
      filter_upwards [] with p
      ring
    _ = ∫ p : Plane × Plane, g p.1 * f p.2 * C (p.1 - p.2) := by
      simpa only [Prod.swap, MeasureTheory.Measure.volume_eq_prod] using
        (integral_prod_swap (μ := volume) (ν := volume)
          (fun p : Plane × Plane => g p.1 * f p.2 * C (p.1 - p.2)))

/-- The real part of a complex Schwartz function, as a real Schwartz function. -/
noncomputable def complexSchwartzRealPart (f : SchwartzMap Plane ℂ) : SchwartzMap Plane ℝ :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.reCLM f

/-- The imaginary part of a complex Schwartz function, as a real Schwartz function. -/
noncomputable def complexSchwartzImagPart (f : SchwartzMap Plane ℂ) : SchwartzMap Plane ℝ :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.imCLM f

/-- The real-part Schwartz function evaluates to the real part of the complex value. -/
@[simp] theorem complexSchwartzRealPart_apply (f : SchwartzMap Plane ℂ) (x : Plane) :
    complexSchwartzRealPart f x = (f x).re := rfl

/-- The imaginary-part Schwartz function evaluates to the imaginary part of the complex value. -/
@[simp] theorem complexSchwartzImagPart_apply (f : SchwartzMap Plane ℂ) (x : Plane) :
    complexSchwartzImagPart f x = (f x).im := rfl

/-- Real positive type extends to the Hermitian quadratic pairing of complex Schwartz functions. -/
theorem complex_schwartz_kernel_quadratic_nonneg (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (∫ z in Metric.closedBall 0 R, |C z|) ≤ A * R ^ k)
    (heven : (fun z : Plane => C (-z)) =ᵐ[volume] C)
    (hpos : ∀ φ : TestFn, 0 ≤ ∫ p : Plane × Plane,
      φ p.1 * φ p.2 * C (p.1 - p.2))
    (f : SchwartzMap Plane ℂ) :
    Integrable (fun p : Plane × Plane =>
      conj (f p.1) * f p.2 * (C (p.1 - p.2) : ℂ)) (volume.prod volume) ∧
      0 ≤ (∫ p : Plane × Plane,
        conj (f p.1) * f p.2 * (C (p.1 - p.2) : ℂ)
        ∂(volume.prod volume)).re ∧
      (∫ p : Plane × Plane,
        conj (f p.1) * f p.2 * (C (p.1 - p.2) : ℂ)
        ∂(volume.prod volume)).im = 0 := by
  let fr := complexSchwartzRealPart f
  let fi := complexSchwartzImagPart f
  let a : Plane × Plane → ℝ := fun p =>
    fr p.1 * fr p.2 * C (p.1 - p.2) + fi p.1 * fi p.2 * C (p.1 - p.2)
  let b : Plane × Plane → ℝ := fun p =>
    fr p.1 * fi p.2 * C (p.1 - p.2) - fi p.1 * fr p.2 * C (p.1 - p.2)
  let q : Plane × Plane → ℂ := fun p =>
    conj (f p.1) * f p.2 * (C (p.1 - p.2) : ℂ)
  have hfrfr : Integrable (fun p : Plane × Plane =>
      fr p.1 * fr p.2 * C (p.1 - p.2)) (volume.prod volume) :=
    integrable_schwartz_testProduct_kernel C hC hgrowth fr fr
  have hfifi : Integrable (fun p : Plane × Plane =>
      fi p.1 * fi p.2 * C (p.1 - p.2)) (volume.prod volume) :=
    integrable_schwartz_testProduct_kernel C hC hgrowth fi fi
  have hfrfi : Integrable (fun p : Plane × Plane =>
      fr p.1 * fi p.2 * C (p.1 - p.2)) (volume.prod volume) :=
    integrable_schwartz_testProduct_kernel C hC hgrowth fr fi
  have hfifr : Integrable (fun p : Plane × Plane =>
      fi p.1 * fr p.2 * C (p.1 - p.2)) (volume.prod volume) :=
    integrable_schwartz_testProduct_kernel C hC hgrowth fi fr
  have ha : Integrable a (volume.prod volume) := by
    dsimp [a]
    exact hfrfr.add hfifi
  have hb : Integrable b (volume.prod volume) := by
    dsimp [b]
    exact hfrfi.sub hfifr
  have hdecomp (x : Plane) :
      f x = (fr x : ℂ) + Complex.I * (fi x : ℂ) := by
    apply Complex.ext <;> simp [fr, fi]
  have hpoint (p : Plane × Plane) : q p = (a p : ℂ) + Complex.I * (b p : ℂ) := by
    dsimp [q, a, b]
    rw [hdecomp p.1, hdecomp p.2]
    simp only [map_add, Complex.conj_ofReal, map_mul, Complex.conj_I]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hfun : q = fun p => (a p : ℂ) + Complex.I * (b p : ℂ) := by
    funext p
    exact hpoint p
  have hq : Integrable q (volume.prod volume) := by
    rw [hfun]
    exact ha.ofReal.add (hb.ofReal.const_mul Complex.I)
  have hRePoint : (fun p : Plane × Plane => (q p).re) = a := by
    funext p
    rw [hpoint]
    simp [a]
  have hImPoint : (fun p : Plane × Plane => (q p).im) = b := by
    funext p
    rw [hpoint]
    simp [b]
  have hReInt : (∫ p : Plane × Plane, q p ∂(volume.prod volume)).re =
      ∫ p : Plane × Plane, (q p).re ∂(volume.prod volume) := (integral_re hq).symm
  have hImInt : (∫ p : Plane × Plane, q p ∂(volume.prod volume)).im =
      ∫ p : Plane × Plane, (q p).im ∂(volume.prod volume) := (integral_im hq).symm
  have hposFr : 0 ≤ ∫ p : Plane × Plane,
      fr p.1 * fr p.2 * C (p.1 - p.2) ∂(volume.prod volume) := by
    simpa only [MeasureTheory.Measure.volume_eq_prod] using
      (real_schwartz_kernel_quadratic_nonneg C hC hgrowth hpos fr).2
  have hposFi : 0 ≤ ∫ p : Plane × Plane,
      fi p.1 * fi p.2 * C (p.1 - p.2) ∂(volume.prod volume) := by
    simpa only [MeasureTheory.Measure.volume_eq_prod] using
      (real_schwartz_kernel_quadratic_nonneg C hC hgrowth hpos fi).2
  constructor
  · exact hq
  constructor
  · change 0 ≤ (∫ p : Plane × Plane, q p ∂(volume.prod volume)).re
    rw [hReInt, hRePoint]
    rw [show a = fun p =>
      fr p.1 * fr p.2 * C (p.1 - p.2) + fi p.1 * fi p.2 * C (p.1 - p.2) by rfl,
      integral_add hfrfr hfifi]
    exact add_nonneg hposFr hposFi
  · change (∫ p : Plane × Plane, q p ∂(volume.prod volume)).im = 0
    rw [hImInt, hImPoint]
    rw [show b = fun p =>
      fr p.1 * fi p.2 * C (p.1 - p.2) - fi p.1 * fr p.2 * C (p.1 - p.2) by rfl,
      integral_sub hfrfi hfifr]
    have hcomm := integral_schwartz_testProduct_kernel_comm C hC hgrowth heven fr fi
    simpa only [MeasureTheory.Measure.volume_eq_prod] using sub_eq_zero.mpr hcomm.2.2

end Critical2DKPZ.Spectral

end
