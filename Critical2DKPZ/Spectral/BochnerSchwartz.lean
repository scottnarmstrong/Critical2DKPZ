/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.Distr
public import Critical2DKPZ.Definitions.TestFn
public import Critical2DKPZ.Analysis.Sobolev.TranslatedPairingConvolution
public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Distribution.Distribution
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! Bochner–Schwartz representation for locally square-integrable kernels. -/

@[expose] public section

noncomputable section

open MeasureTheory
open TopologicalSpace
open scoped ComplexConjugate ENNReal SchwartzMap FourierTransform

set_option linter.style.haveILetI false

namespace Critical2DKPZ.Spectral

/-- A function that is square-integrable on every compact set is locally integrable. -/
theorem locallyIntegrable_of_compactMemLp_two (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K)) :
    LocallyIntegrable C volume := by
  intro x
  obtain ⟨K, hK, hxK⟩ := exists_compact_mem_nhds x
  have hKfinite : volume K < ∞ := hK.measure_lt_top
  letI : IsFiniteMeasure (volume.restrict K) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hKfinite⟩
  have hC1 : MemLp C 1 (volume.restrict K) := by
    exact (hC K hK).mono_exponent (by norm_num)
  exact ⟨K, hxK, memLp_one_iff_integrable.mp hC1⟩

/-- The distribution induced by integration against a function on compactly supported tests. -/
noncomputable def kernelDistribution (C : Plane → ℝ) : Distr :=
  Distribution.ofFun (⊤ : Opens Plane) C volume ⊤


private def radialShell (n : ℕ) : Set Plane :=
  {x | (n : ℝ) ≤ ‖x‖ ∧ ‖x‖ < (n : ℝ) + 1}

private theorem measurableSet_radialShell (n : ℕ) : MeasurableSet (radialShell n) := by
  unfold radialShell
  exact (measurableSet_Ici.preimage continuous_norm.measurable).inter
    (measurableSet_Iio.preimage continuous_norm.measurable)

private theorem radialShell_subset_closedBall (n : ℕ) :
    radialShell n ⊆ Metric.closedBall (0 : Plane) ((n : ℝ) + 1) := by
  rintro x ⟨_, hx⟩
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  exact hx.le

private theorem iUnion_radialShell : (⋃ n : ℕ, radialShell n) = Set.univ := by
  ext x
  constructor
  · intro _
    trivial
  · intro _
    let n := ⌊‖x‖⌋₊
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    exact ⟨Nat.floor_le (norm_nonneg x), Nat.lt_floor_add_one _⟩

/-- A locally square-integrable kernel is integrable in absolute value on every closed ball. -/
theorem integrable_abs_kernel_on_closedBall (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (R : ℝ) : IntegrableOn (fun x => |C x|) (Metric.closedBall 0 R) volume := by
  let K := Metric.closedBall (0 : Plane) R
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKfinite : volume K < ∞ := hK.measure_lt_top
  letI : IsFiniteMeasure (volume.restrict K) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hKfinite⟩
  have hC1 : MemLp C 1 (volume.restrict K) := (hC K hK).mono_exponent (by norm_num)
  exact (memLp_one_iff_integrable.mp hC1).abs

/-- A compactly supported real test multiplied by a locally square-integrable kernel is
integrable. -/
theorem integrable_testFn_kernel (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (f : TestFn) : Integrable (fun x : Plane => f x * C x) volume := by
  let K := tsupport f
  have hK : IsCompact K := f.hasCompactSupport.isCompact
  have hKfinite : volume K < ∞ := hK.measure_lt_top
  letI : IsFiniteMeasure (volume.restrict K) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hKfinite⟩
  have hC1 : MemLp C 1 (volume.restrict K) := (hC K hK).mono_exponent (by norm_num)
  have hCint : IntegrableOn C K volume := memLp_one_iff_integrable.mp hC1
  have hCcut : Integrable (K.indicator C) volume := hCint.integrable_indicator hK.measurableSet
  obtain ⟨M, hM⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  let B : ℝ := max M 0
  have hB : 0 ≤ B := le_max_right M 0
  have hfB (x : Plane) : ‖f x‖ ≤ B := (hM x).trans (le_max_left M 0)
  have hmajor : Integrable (fun x : Plane => B * ‖(K.indicator C) x‖) volume :=
    hCcut.norm.const_mul B
  have hmeas : AEStronglyMeasurable (fun x : Plane => f x * (K.indicator C) x) volume :=
    f.continuous.measurable.aestronglyMeasurable.mul hCcut.aestronglyMeasurable
  have hcutProd : Integrable (fun x : Plane => f x * (K.indicator C) x) volume := by
    apply hmajor.mono' hmeas
    filter_upwards [] with x
    change |f x * (K.indicator C) x| ≤ B * ‖(K.indicator C) x‖
    rw [abs_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right
      (by simpa only [Real.norm_eq_abs] using hfB x) (abs_nonneg _)
  have hEq : (fun x : Plane => f x * C x) =ᵐ[volume]
      (fun x => f x * (K.indicator C) x) := by
    filter_upwards [] with x
    by_cases hx : x ∈ K
    · simp [hx]
    · have hfx : f x = 0 := by
        by_contra hfx
        exact hx (subset_tsupport f (Function.mem_support.mpr hfx))
      simp [hx, hfx]
  exact (integrable_congr hEq).2 hcutProd

/-- A compactly supported test-function pairing with a locally square-integrable difference
kernel is integrable. -/
theorem integrable_testFnProduct_kernel (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (f g : TestFn) :
    Integrable (fun p : Plane × Plane => f p.1 * g p.2 * C (p.1 - p.2))
      (volume : Measure (Plane × Plane)) := by
  let K : Set Plane :=
    (fun p : Plane × Plane => p.1 - p.2) '' (tsupport f ×ˢ tsupport g)
  have hsub : Continuous (fun p : Plane × Plane => p.1 - p.2) :=
    continuous_fst.sub continuous_snd
  have hK : IsCompact K := by
    dsimp [K]
    exact (f.hasCompactSupport.isCompact.prod g.hasCompactSupport.isCompact).image hsub
  have hKfinite : volume K < ∞ := hK.measure_lt_top
  letI : IsFiniteMeasure (volume.restrict K) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hKfinite⟩
  have hC1 : MemLp C 1 (volume.restrict K) :=
    (hC K hK).mono_exponent (by norm_num)
  have hCint : IntegrableOn C K volume := memLp_one_iff_integrable.mp hC1
  have hCcut : Integrable (K.indicator C) volume :=
    hCint.integrable_indicator hK.measurableSet
  have hg : Integrable (fun x : Plane => g x) volume := by
    exact g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
  have hkernel : Integrable
      (fun p : Plane × Plane => g p.2 * (K.indicator C) (p.1 - p.2))
      (volume.prod volume) := by
    exact hg.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hCcut
  obtain ⟨M, hM⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  let B : ℝ := max M 0
  have hB : 0 ≤ B := le_max_right M 0
  have hfB (x : Plane) : ‖f x‖ ≤ B := (hM x).trans (le_max_left M 0)
  have hmajor : Integrable
      (fun p : Plane × Plane => B * ‖g p.2 * (K.indicator C) (p.1 - p.2)‖)
      (volume.prod volume) := by
    simpa only [Real.norm_eq_abs] using hkernel.norm.const_mul B
  have hmeasF : AEStronglyMeasurable (fun p : Plane × Plane => f p.1)
      (volume.prod volume) :=
    (f.continuous.measurable.comp measurable_fst).aestronglyMeasurable
  have hmeasKernel : AEStronglyMeasurable
      (fun p : Plane × Plane => g p.2 * (K.indicator C) (p.1 - p.2))
      (volume.prod volume) := hkernel.aestronglyMeasurable
  have hcutPairRight : Integrable
      (fun p : Plane × Plane => f p.1 * (g p.2 * (K.indicator C) (p.1 - p.2)))
      (volume.prod volume) := by
    apply hmajor.mono' (hmeasF.mul hmeasKernel)
    filter_upwards [] with p
    change |f p.1 * (g p.2 * (K.indicator C) (p.1 - p.2))| ≤ _
    rw [abs_mul, Real.norm_eq_abs]
    calc
      |f p.1| * |g p.2 * (K.indicator C) (p.1 - p.2)| ≤
          B * |g p.2 * (K.indicator C) (p.1 - p.2)| :=
        mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hfB p.1)
          (abs_nonneg _)
      _ = B * ‖g p.2 * (K.indicator C) (p.1 - p.2)‖ := by rw [Real.norm_eq_abs]
  have hcutPair : Integrable
      (fun p : Plane × Plane => f p.1 * g p.2 * (K.indicator C) (p.1 - p.2))
      (volume.prod volume) := by
    convert hcutPairRight using 1
    funext p
    ring
  have hEq :
      (fun p : Plane × Plane => f p.1 * g p.2 * C (p.1 - p.2)) =ᵐ[volume.prod volume]
        (fun p => f p.1 * g p.2 * (K.indicator C) (p.1 - p.2)) := by
    filter_upwards [] with p
    rcases p with ⟨x, y⟩
    by_cases hfg : f x * g y = 0
    · simp [hfg]
    · have hfx : f x ≠ 0 := by
        intro h
        apply hfg
        simp [h]
      have hgy : g y ≠ 0 := by
        intro h
        apply hfg
        simp [h]
      have hx : x ∈ tsupport f := subset_tsupport f (Function.mem_support.mpr hfx)
      have hy : y ∈ tsupport g := subset_tsupport g (Function.mem_support.mpr hgy)
      have hxy : x - y ∈ K := ⟨(x, y), ⟨hx, hy⟩, rfl⟩
      simp [hxy]
  simpa only [MeasureTheory.Measure.volume_eq_prod] using (integrable_congr hEq).2 hcutPair

/-- The difference-kernel pairing equals integration of the canonical test convolution against
the kernel. -/
theorem integral_testFnProduct_kernel_eq_integral_testFnConvolution (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (f g : TestFn) :
    ∫ p : Plane × Plane, f p.1 * g p.2 * C (p.1 - p.2) =
      ∫ z : Plane,
        Critical2DKPZ.Analysis.Sobolev.testFnConvolution f g z * C z := by
  let F : Plane × Plane → ℝ := fun p => f (p.1 + p.2) * g p.2 * C p.1
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
  have hpair : Integrable
      (fun p : Plane × Plane => f p.1 * g p.2 * C (p.1 - p.2))
      (volume.prod volume) := by
    simpa only [MeasureTheory.Measure.volume_eq_prod] using
      integrable_testFnProduct_kernel C hC f g
  have hcomp : Integrable (F ∘ e) (volume.prod volume) := by
    apply hpair.congr
    filter_upwards [] with p
    dsimp [F, e]
    rw [sub_add_cancel]
  have hmp : MeasurePreserving (fun p : Plane × Plane => (p.1 - p.2, p.2))
      (volume.prod volume) (volume.prod volume) := by
    exact measurePreserving_sub_prod volume volume
  have hF : Integrable F (volume.prod volume) := by
    exact (hmp.integrable_comp_emb e.measurableEmbedding).mp hcomp
  have hshift (z : Plane) :
      (∫ y : Plane, f (z + y) * g y) =
        Critical2DKPZ.Analysis.Sobolev.testFnConvolution f g z := by
    rw [Critical2DKPZ.Analysis.Sobolev.testFnConvolution_apply]
    calc
      (∫ y : Plane, f (z + y) * g y) =
          ∫ y : Plane, (fun u : Plane => f u * g (u - z)) (y + z) := by
            apply integral_congr_ae
            filter_upwards [] with y
            rw [add_sub_cancel_right]
            rw [add_comm z y]
      _ = ∫ u : Plane, f u * g (u - z) := by
          simpa only [add_comm] using
            (integral_add_left_eq_self z (f := fun u : Plane => f u * g (u - z)))
  calc
    (∫ p : Plane × Plane, f p.1 * g p.2 * C (p.1 - p.2)) =
        ∫ p : Plane × Plane, F (e p) := by
          apply integral_congr_ae
          filter_upwards [] with p
          dsimp [F, e]
          rw [sub_add_cancel]
    _ = ∫ p : Plane × Plane, F p := hmp.integral_comp' F
    _ = ∫ z : Plane, ∫ y : Plane, F (z, y) := integral_prod F hF
    _ = ∫ z : Plane,
        Critical2DKPZ.Analysis.Sobolev.testFnConvolution f g z * C z := by
          apply integral_congr_ae
          filter_upwards [] with z
          dsimp [F]
          calc
            (∫ y : Plane, f (z + y) * g y * C z) =
                C z * ∫ y : Plane, f (z + y) * g y := by
                  rw [show (fun y : Plane => f (z + y) * g y * C z) =
                    (fun y => C z * (f (z + y) * g y)) by
                      funext y
                      ring, integral_const_mul]
            _ = Critical2DKPZ.Analysis.Sobolev.testFnConvolution f g z * C z := by
                  rw [hshift z]
                  ring














/-- A locally finite measure with uniform polynomial growth on centered balls has temperate
growth. -/
theorem measure_hasTemperateGrowth_of_polynomial_ball_growth (μ : Measure Plane)
    [IsLocallyFiniteMeasure μ]
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (μ (Metric.closedBall (0 : Plane) R)).toReal ≤ A * R ^ k) :
    μ.HasTemperateGrowth := by
  obtain ⟨A, k, hA⟩ := hgrowth
  have hmfc : IsFiniteMeasureOnCompacts μ :=
    @isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure Plane _ _ _ ‹IsLocallyFiniteMeasure μ›
  let N := k + 2
  let w : Plane → ℝ := fun x => (1 + ‖x‖) ^ (-(N : ℝ))
  have hwcont : Continuous w := by
    change Continuous (fun x : Plane => (1 + ‖x‖) ^ (-(N : ℝ)))
    apply (continuous_const.add continuous_norm).rpow_const
    intro x
    have hx : (0 : ℝ) < 1 + ‖x‖ := by nlinarith [norm_nonneg x]
    exact Or.inl hx.ne'
  have hwmeas : AEStronglyMeasurable w μ := hwcont.measurable.aestronglyMeasurable
  have hw_nonneg (x : Plane) : 0 ≤ w x := by
    dsimp [w]
    positivity
  have hw_le_one (x : Plane) : w x ≤ 1 := by
    dsimp [w]
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · have : 0 ≤ ‖x‖ := norm_nonneg x
      linarith
    · exact neg_nonpos.mpr (by positivity : (0 : ℝ) ≤ (N : ℝ))
  have hweighted_shell : ∀ n : ℕ,
      IntegrableOn w (radialShell n) μ := by
    intro n
    let R : ℝ := (n : ℝ) + 1
    let K := Metric.closedBall (0 : Plane) R
    have hK : IsCompact K := isCompact_closedBall _ _
    have hKfinite : μ K < ∞ := hmfc.lt_top_of_isCompact hK
    have hball : radialShell n ⊆ K := by
      simpa [R] using radialShell_subset_closedBall n
    have hKintegrable : IntegrableOn w K μ := by
      apply Measure.integrableOn_of_bounded hKfinite.ne hwmeas
      filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_of_nonneg (hw_nonneg x)]
      exact hw_le_one x
    exact hKintegrable.mono_set hball
  have hShellBound : ∀ n : ℕ,
      ∫ x in radialShell n, ‖w x‖ ∂μ ≤ A / ((n : ℝ) + 1) ^ 2 := by
    intro n
    let R : ℝ := (n : ℝ) + 1
    let K := Metric.closedBall (0 : Plane) R
    have hK : IsCompact K := isCompact_closedBall _ _
    have hKfinite : μ K < ∞ := hmfc.lt_top_of_isCompact hK
    have hR : 1 ≤ R := by
      dsimp [R]
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hGrowth := hA R hR
    have hShellSubset : radialShell n ⊆ K := by
      simpa [R] using radialShell_subset_closedBall n
    have hShellFinite : μ (radialShell n) < ∞ :=
      (measure_mono hShellSubset).trans_lt hKfinite
    have hIntShell : IntegrableOn w (radialShell n) μ := hweighted_shell n
    have hweight : ∀ x ∈ radialShell n, w x ≤ R ^ (-(N : ℝ)) := by
      intro x hx
      dsimp [w, R, radialShell] at *
      apply Real.rpow_le_rpow_of_nonpos (by positivity) _
        (neg_nonpos.mpr (by positivity : (0 : ℝ) ≤ (N : ℝ)))
      nlinarith [hx.1]
    have hconstInt : Integrable (fun _ : Plane => R ^ (-(N : ℝ)))
        (μ.restrict (radialShell n)) := by
      letI : IsFiniteMeasure (μ.restrict (radialShell n)) := by
        constructor
        rw [Measure.restrict_apply_univ]
        exact hShellFinite
      exact integrable_const _
    have hShellIne :
        (∫ x in radialShell n, w x ∂μ) ≤
          (∫ x in radialShell n, R ^ (-(N : ℝ)) ∂μ) := by
      apply integral_mono_ae hIntShell hconstInt
      filter_upwards [ae_restrict_mem (measurableSet_radialShell n)] with x hx
      exact hweight x hx
    have hMass : (μ (radialShell n)).toReal ≤ A * R ^ k := by
      calc
        (μ (radialShell n)).toReal ≤ (μ K).toReal :=
          ENNReal.toReal_mono hKfinite.ne (measure_mono hShellSubset)
        _ ≤ A * R ^ k := by simpa [K] using hGrowth
    have hconstEval :
        (∫ x in radialShell n, R ^ (-(N : ℝ)) ∂μ) =
          R ^ (-(N : ℝ)) * (μ (radialShell n)).toReal := by
      rw [integral_const, smul_eq_mul, measureReal_restrict_apply_univ, Measure.real]
      ring
    have hnorm : (fun x : Plane => ‖w x‖) = w := by
      funext x
      rw [Real.norm_eq_abs, abs_of_nonneg (hw_nonneg x)]
    rw [hnorm]
    calc
      ∫ x in radialShell n, w x ∂μ ≤
          R ^ (-(N : ℝ)) * (μ (radialShell n)).toReal := by
        rw [hconstEval] at hShellIne
        exact hShellIne
      _ ≤ R ^ (-(N : ℝ)) * (A * R ^ k) :=
        mul_le_mul_of_nonneg_left hMass (by positivity)
      _ = A / R ^ 2 := by
        rw [Real.rpow_neg (by positivity)]
        simp only [Real.rpow_natCast]
        dsimp [N]
        rw [pow_add]
        field_simp [ne_of_gt (by linarith : 0 < R)]
  have hsumBound : Summable (fun n : ℕ => A / ((n : ℝ) + 1) ^ 2) := by
    have hs := (Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num)
    simpa [div_eq_mul_inv, mul_comm] using hs.mul_left A
  have hsum : Summable (fun n : ℕ => ∫ x in radialShell n, ‖w x‖ ∂μ) := by
    apply hsumBound.of_nonneg_of_le
    · intro n
      exact integral_nonneg fun _ => norm_nonneg _
    · intro n
      exact hShellBound n
  have hInt := integrableOn_iUnion_of_summable_integral_norm
    (f := w) hweighted_shell hsum
  rw [iUnion_radialShell, integrableOn_univ] at hInt
  exact ⟨N, by simpa [w, N] using hInt⟩


/-- The positive measure with density `|C|`. -/
noncomputable def absoluteKernelMeasure (C : Plane → ℝ) : Measure Plane :=
  volume.withDensity (fun x : Plane => ENNReal.ofReal |C x|)

/-- The positive measure with density the positive part of `C`. -/
noncomputable def positivePartKernelMeasure (C : Plane → ℝ) : Measure Plane :=
  volume.withDensity (fun x : Plane => ENNReal.ofReal (max (C x) 0))

/-- The positive measure with density the negative part of `C`. -/
noncomputable def negativePartKernelMeasure (C : Plane → ℝ) : Measure Plane :=
  volume.withDensity (fun x : Plane => ENNReal.ofReal (max (-C x) 0))

/-- Polynomial integral growth on balls makes a locally square-integrable kernel integrable after
multiplication by a sufficiently strong polynomial weight. -/
theorem exists_integrable_polynomial_decay_mul_abs_of_ball_growth (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (∫ z in Metric.closedBall 0 R, |C z|) ≤ A * R ^ k) :
    ∃ n : ℕ, Integrable (fun x : Plane => (1 + ‖x‖) ^ (-(n : ℝ)) * |C x|) := by
  obtain ⟨A, k, hA⟩ := hgrowth
  let N := k + 2
  let w : Plane → ℝ := fun x => (1 + ‖x‖) ^ (-(N : ℝ))
  have hloc := locallyIntegrable_of_compactMemLp_two C hC
  have hweight_meas : Measurable w := by
    change Measurable (fun x : Plane => (1 + ‖x‖) ^ (-(N : ℝ)))
    fun_prop
  have hw_nonneg (x : Plane) : 0 ≤ w x := by
    dsimp [w]
    positivity
  have hw_le_one (x : Plane) : w x ≤ 1 := by
    dsimp [w]
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · have : 0 ≤ ‖x‖ := norm_nonneg x
      linarith
    · exact neg_nonpos.mpr (by positivity : (0 : ℝ) ≤ (N : ℝ))
  have hweighted_shell : ∀ n : ℕ,
      IntegrableOn (fun x : Plane => w x * |C x|) (radialShell n) volume := by
    intro n
    let R : ℝ := (n : ℝ) + 1
    let K := Metric.closedBall (0 : Plane) R
    have hBall : IntegrableOn (fun x : Plane => |C x|) K volume := by
      exact integrable_abs_kernel_on_closedBall C hC R
    have hKint : Integrable (fun x : Plane => |C x|) (volume.restrict K) := hBall
    have hKsm : AEStronglyMeasurable (fun x : Plane => w x * |C x|)
        (volume.restrict K) := by
      exact hweight_meas.aestronglyMeasurable.mul hKint.aestronglyMeasurable
    have hWeightedBall : IntegrableOn (fun x : Plane => w x * |C x|) K volume := by
      apply hKint.mono' hKsm
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw_nonneg x) (abs_nonneg _))]
      calc
        w x * |C x| ≤ 1 * |C x| := mul_le_mul_of_nonneg_right (hw_le_one x) (abs_nonneg _)
        _ = |C x| := one_mul _
    exact hWeightedBall.mono_set (radialShell_subset_closedBall n)
  have hShellBound : ∀ n : ℕ,
      ∫ x in radialShell n, w x * |C x| ∂volume ≤ |A| / ((n : ℝ) + 1) ^ 2 := by
    intro n
    let R : ℝ := (n : ℝ) + 1
    have hR : 1 ≤ R := by
      dsimp [R]
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hIntBall := integrable_abs_kernel_on_closedBall C hC R
    have hGrowth := hA R hR
    have hGrowthAbs : ∫ x in Metric.closedBall 0 R, |C x| ∂volume ≤ |A| * R ^ k :=
      hGrowth.trans (mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity))
    have hweight : ∀ x ∈ radialShell n, w x ≤ R ^ (-(N : ℝ)) := by
      intro x hx
      dsimp [w, R, radialShell] at *
      apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (neg_nonpos.mpr (by positivity : (0 : ℝ) ≤ (N : ℝ)))
      nlinarith [hx.1]
    have hIntShell := hIntBall.mono_set (radialShell_subset_closedBall n)
    have hShellSubset : radialShell n ⊆ Metric.closedBall 0 R := by
      simpa [R] using radialShell_subset_closedBall n
    have hShellAbsLeBall :
        ∫ x in radialShell n, |C x| ∂volume ≤ ∫ x in Metric.closedBall 0 R, |C x| ∂volume :=
      setIntegral_mono_set hIntBall
        (ae_of_all _ fun x => abs_nonneg (C x))
        (ae_of_all _ fun x hx => hShellSubset hx)
    have hShellWeightedLe :
        ∫ x in radialShell n, w x * |C x| ∂volume ≤
          R ^ (-(N : ℝ)) * ∫ x in radialShell n, |C x| ∂volume := by
      calc
        ∫ x, w x * |C x| ∂(volume.restrict (radialShell n)) ≤
            ∫ x, R ^ (-(N : ℝ)) * |C x| ∂(volume.restrict (radialShell n)) := by
          apply integral_mono_ae (hweighted_shell n)
            (hIntShell.const_mul (R ^ (-(N : ℝ))))
          filter_upwards [ae_restrict_mem (measurableSet_radialShell n)] with x hx
          exact mul_le_mul_of_nonneg_right
            (hweight x hx) (abs_nonneg _)
        _ = R ^ (-(N : ℝ)) * ∫ x, |C x| ∂(volume.restrict (radialShell n)) := by
          rw [integral_const_mul]
    calc
      ∫ x in radialShell n, w x * |C x| ∂volume ≤
          R ^ (-(N : ℝ)) * ∫ x in radialShell n, |C x| ∂volume := hShellWeightedLe
      _ ≤ R ^ (-(N : ℝ)) * ∫ x in Metric.closedBall 0 R, |C x| ∂volume :=
        mul_le_mul_of_nonneg_left hShellAbsLeBall (by positivity)
      _ ≤ R ^ (-(N : ℝ)) * (|A| * R ^ k) :=
        mul_le_mul_of_nonneg_left hGrowthAbs (by positivity)
      _ = |A| / R ^ 2 := by
        rw [Real.rpow_neg (by positivity)]
        simp only [Real.rpow_natCast]
        dsimp [N]
        rw [pow_add]
        field_simp [ne_of_gt (by linarith : 0 < R)]
  have hsumBound : Summable (fun n : ℕ => |A| / ((n : ℝ) + 1) ^ 2) := by
    have hs := (Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num)
    simpa [div_eq_mul_inv, mul_comm] using hs.mul_left |A|
  have hnorm : (fun x : Plane => ‖w x * |C x|‖) =
      (fun x => w x * |C x|) := by
    funext x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw_nonneg x) (abs_nonneg _))]
  have hsum : Summable (fun n : ℕ => ∫ x in radialShell n, ‖w x * |C x|‖ ∂volume) := by
    apply hsumBound.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
    intro n
    calc
      ∫ x in radialShell n, ‖w x * |C x|‖ ∂volume =
          ∫ x in radialShell n, w x * |C x| ∂volume :=
        setIntegral_congr_fun (measurableSet_radialShell n) (fun x _ => congrFun hnorm x)
      _ ≤ |A| / ((n : ℝ) + 1) ^ 2 := hShellBound n
  have hInt := integrableOn_iUnion_of_summable_integral_norm
    (f := fun x : Plane => w x * |C x|) hweighted_shell hsum
  rw [iUnion_radialShell, integrableOn_univ] at hInt
  refine ⟨N, ?_⟩
  simpa [w, N] using hInt

/-- The measure with density `|C|` has temperate growth whenever `C` has polynomial integral
growth on balls. -/
theorem absoluteKernelMeasure_hasTemperateGrowth (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (∫ z in Metric.closedBall 0 R, |C z|) ≤ A * R ^ k) :
    (absoluteKernelMeasure C).HasTemperateGrowth := by
  obtain ⟨n, hn⟩ := exists_integrable_polynomial_decay_mul_abs_of_ball_growth C hC hgrowth
  have hloc := locallyIntegrable_of_compactMemLp_two C hC
  have hρ : AEMeasurable (fun x : Plane => ENNReal.ofReal |C x|) volume := by
    have hAbs : AEMeasurable (fun x : Plane => |C x|) volume := by
      simpa only [Real.norm_eq_abs] using hloc.aestronglyMeasurable.norm.aemeasurable
    exact hAbs.ennreal_ofReal
  have hρtop : ∀ᵐ x : Plane ∂volume, ENNReal.ofReal |C x| < ⊤ :=
    Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)
  refine ⟨n, ?_⟩
  rw [absoluteKernelMeasure, integrable_withDensity_iff_integrable_smul₀' hρ hρtop]
  have heq :
      (fun x : Plane => (ENNReal.ofReal |C x|).toReal • (1 + ‖x‖) ^ (-(n : ℝ))) =
        (fun x => (1 + ‖x‖) ^ (-(n : ℝ)) * |C x|) := by
    funext x
    rw [ENNReal.toReal_ofReal (abs_nonneg (C x)), smul_eq_mul]
    ring
  exact hn.congr (Filter.Eventually.of_forall (fun x => (congrFun heq x).symm))

/-- The positive-part measure of a polynomially growing local `L²` kernel has temperate growth. -/
theorem positivePartKernelMeasure_hasTemperateGrowth (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (∫ z in Metric.closedBall 0 R, |C z|) ≤ A * R ^ k) :
    (positivePartKernelMeasure C).HasTemperateGrowth := by
  have hAbs : (absoluteKernelMeasure C).HasTemperateGrowth :=
    absoluteKernelMeasure_hasTemperateGrowth C hC hgrowth
  have hle : positivePartKernelMeasure C ≤ absoluteKernelMeasure C := by
    unfold positivePartKernelMeasure absoluteKernelMeasure
    apply MeasureTheory.withDensity_mono
    filter_upwards [] with x
    apply ENNReal.ofReal_le_ofReal
    exact max_le (le_abs_self (C x)) (abs_nonneg (C x))
  rcases hAbs.exists_integrable with ⟨n, hn⟩
  exact ⟨n, hn.mono_measure hle⟩

/-- The negative-part measure of a polynomially growing local `L²` kernel has temperate growth. -/
theorem negativePartKernelMeasure_hasTemperateGrowth (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (∫ z in Metric.closedBall 0 R, |C z|) ≤ A * R ^ k) :
    (negativePartKernelMeasure C).HasTemperateGrowth := by
  have hAbs : (absoluteKernelMeasure C).HasTemperateGrowth :=
    absoluteKernelMeasure_hasTemperateGrowth C hC hgrowth
  have hle : negativePartKernelMeasure C ≤ absoluteKernelMeasure C := by
    unfold negativePartKernelMeasure absoluteKernelMeasure
    apply MeasureTheory.withDensity_mono
    filter_upwards [] with x
    apply ENNReal.ofReal_le_ofReal
    exact max_le (by simpa only [abs_neg] using le_abs_self (-C x)) (abs_nonneg (C x))
  rcases hAbs.exists_integrable with ⟨n, hn⟩
  exact ⟨n, hn.mono_measure hle⟩

/-- View a real compactly supported test as a complex Schwartz function. -/
noncomputable def testFnToSchwartzMap (f : TestFn) : SchwartzMap Plane ℂ :=
  (f.hasCompactSupport.comp_left rfl).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp f.contDiff)

/-- Viewing a test function as a complex Schwartz function preserves its values. -/
@[simp] theorem testFnToSchwartzMap_apply (f : TestFn) (x : Plane) :
    testFnToSchwartzMap f x = (f x : ℂ) := rfl

/-- The locally square-integrable kernel, integrated against Schwartz functions, defines a
tempered distribution. -/
noncomputable def kernelTemperedDistribution (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (∫ z in Metric.closedBall 0 R, |C z|) ≤ A * R ^ k) :
    TemperedDistribution Plane ℂ := by
  letI : (positivePartKernelMeasure C).HasTemperateGrowth :=
    positivePartKernelMeasure_hasTemperateGrowth C hC hgrowth
  letI : (negativePartKernelMeasure C).HasTemperateGrowth :=
    negativePartKernelMeasure_hasTemperateGrowth C hC hgrowth
  exact (positivePartKernelMeasure C).toTemperedDistribution -
    (negativePartKernelMeasure C).toTemperedDistribution

/-- The tempered extension acts on every Schwartz function by integrating against its kernel. -/
theorem kernelTemperedDistribution_apply_schwartz (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (∫ z in Metric.closedBall 0 R, |C z|) ≤ A * R ^ k) (g : SchwartzMap Plane ℂ) :
    kernelTemperedDistribution C hC hgrowth g =
      ∫ x : Plane, (C x : ℂ) * g x := by
  let μplus := positivePartKernelMeasure C
  let μminus := negativePartKernelMeasure C
  letI : μplus.HasTemperateGrowth := positivePartKernelMeasure_hasTemperateGrowth C hC hgrowth
  letI : μminus.HasTemperateGrowth := negativePartKernelMeasure_hasTemperateGrowth C hC hgrowth
  have hplusInt : Integrable g μplus := g.integrable
  have hminusInt : Integrable g μminus := g.integrable
  have hloc := locallyIntegrable_of_compactMemLp_two C hC
  have hρplus : AEMeasurable (fun x : Plane => ENNReal.ofReal (max (C x) 0)) volume := by
    exact (hloc.aestronglyMeasurable.aemeasurable.max aemeasurable_const).ennreal_ofReal
  have hρminus : AEMeasurable (fun x : Plane => ENNReal.ofReal (max (-C x) 0)) volume := by
    exact (hloc.aestronglyMeasurable.neg.aemeasurable.max aemeasurable_const).ennreal_ofReal
  have hρtop : ∀ᵐ x : Plane ∂volume, ENNReal.ofReal (max (C x) 0) < ⊤ :=
    Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  have hρtop' : ∀ᵐ x : Plane ∂volume, ENNReal.ofReal (max (-C x) 0) < ⊤ :=
    Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  have hplusBase : Integrable
      (fun x : Plane => (ENNReal.ofReal (max (C x) 0)).toReal • g x)
      volume := by
    apply (integrable_withDensity_iff_integrable_smul₀' hρplus hρtop).mp
    simpa [μplus, positivePartKernelMeasure] using hplusInt
  have hminusBase : Integrable
      (fun x : Plane => (ENNReal.ofReal (max (-C x) 0)).toReal • g x)
      volume := by
    apply (integrable_withDensity_iff_integrable_smul₀' hρminus hρtop').mp
    simpa [μminus, negativePartKernelMeasure] using hminusInt
  have hplusFormula :
      ∫ x : Plane, g x ∂μplus =
        ∫ x : Plane, (ENNReal.ofReal (max (C x) 0)).toReal • g x := by
    simpa [μplus, positivePartKernelMeasure] using
      (integral_withDensity_eq_integral_toReal_smul₀ hρplus hρtop g)
  have hminusFormula :
      ∫ x : Plane, g x ∂μminus =
        ∫ x : Plane, (ENNReal.ofReal (max (-C x) 0)).toReal • g x := by
    simpa [μminus, negativePartKernelMeasure] using
      (integral_withDensity_eq_integral_toReal_smul₀ hρminus hρtop' g)
  change (μplus.toTemperedDistribution g - μminus.toTemperedDistribution g) = _
  rw [MeasureTheory.Measure.toTemperedDistribution_apply μplus,
    MeasureTheory.Measure.toTemperedDistribution_apply μminus]
  rw [hplusFormula, hminusFormula, ← integral_sub hplusBase hminusBase]
  apply integral_congr_ae
  filter_upwards [] with x
  have hparts : max (C x) 0 - max (-C x) 0 = C x := by
    by_cases h : 0 ≤ C x
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
      ring
    · have h' : C x < 0 := lt_of_not_ge h
      rw [max_eq_right (le_of_lt h'), max_eq_left (neg_nonneg.mpr (le_of_lt h'))]
      ring
  rw [ENNReal.toReal_ofReal (le_max_right (C x) 0),
    ENNReal.toReal_ofReal (le_max_right (-C x) 0), Complex.real_smul, Complex.real_smul]
  calc
    _ = (Complex.ofReal (max (C x) 0 - max (-C x) 0)) * g x := by
      rw [Complex.ofReal_sub]
      ring
    _ = (C x : ℂ) * g x := by rw [hparts]

/-- The Fourier transform of the tempered kernel distribution acts by integrating `C` against the
Fourier transform of the Schwartz test. -/
theorem fourier_kernelTemperedDistribution_apply_schwartz (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (∫ z in Metric.closedBall 0 R, |C z|) ≤ A * R ^ k)
    (g : SchwartzMap Plane ℂ) :
    (𝓕 (kernelTemperedDistribution C hC hgrowth)) g =
      ∫ x : Plane, (C x : ℂ) * (𝓕 g) x := by
  rw [TemperedDistribution.fourier_apply, kernelTemperedDistribution_apply_schwartz]





end Critical2DKPZ.Spectral

end
