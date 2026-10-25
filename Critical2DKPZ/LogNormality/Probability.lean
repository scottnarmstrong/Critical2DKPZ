/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.LogNormality.Lyapunov
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Tactic

/-! # Probability estimates for lattice log-normality -/

@[expose] public section

namespace Critical2DKPZ.LogNormality

open Filter MeasureTheory ProbabilityTheory
open scoped Topology BoundedContinuousFunction

private noncomputable def inverseQuadraticTest : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => (1 + x ^ 2)⁻¹,
      (by fun_prop : Continuous (fun x : ℝ => 1 + x ^ 2)).inv₀
        (fun x => by positivity)⟩ 1 (by
      intro x y
      change dist ((1 + x ^ 2)⁻¹) ((1 + y ^ 2)⁻¹) ≤ 1
      rw [Real.dist_eq, abs_le]
      have hx : 0 ≤ (1 + x ^ 2)⁻¹ := by positivity
      have hx1 : (1 + x ^ 2)⁻¹ ≤ 1 := by
        rw [inv_le_one₀ (by positivity)]
        nlinarith [sq_nonneg x]
      have hy : 0 ≤ (1 + y ^ 2)⁻¹ := by positivity
      have hy1 : (1 + y ^ 2)⁻¹ ≤ 1 := by
        rw [inv_le_one₀ (by positivity)]
        nlinarith [sq_nonneg y]
      constructor <;> linarith)

private noncomputable def scaledIdentityTest (R : ℝ) (hR : 0 < R) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => R * x / (R + |x|), by
      exact (continuous_const.mul continuous_id).mul
        ((continuous_const.add continuous_abs).inv₀
          (fun x => (add_pos_of_pos_of_nonneg hR (abs_nonneg x)).ne'))⟩
    (2 * R) (by
      intro x y
      change dist (R * x / (R + |x|)) (R * y / (R + |y|)) ≤ 2 * R
      have hxden : 0 < R + |x| := by positivity
      have hyden : 0 < R + |y| := by positivity
      have hxabs : |R * x / (R + |x|)| = R * |x| / (R + |x|) := by
        rw [abs_div, abs_mul, abs_of_pos hR, abs_of_pos hxden]
      have hyabs : |R * y / (R + |y|)| = R * |y| / (R + |y|) := by
        rw [abs_div, abs_mul, abs_of_pos hR, abs_of_pos hyden]
      have hxbound : |R * x / (R + |x|)| ≤ R := by
        rw [hxabs]
        apply (div_le_iff₀ hxden).2
        nlinarith [abs_nonneg x]
      have hybound : |R * y / (R + |y|)| ≤ R := by
        rw [hyabs]
        apply (div_le_iff₀ hyden).2
        nlinarith [abs_nonneg y]
      rw [Real.dist_eq, abs_le]
      have hxlo := (abs_le.mp hxbound).1
      have hxhi := (abs_le.mp hxbound).2
      have hylo := (abs_le.mp hybound).1
      have hyhi := (abs_le.mp hybound).2
      constructor <;> linarith)

private theorem inverseQuadraticTest_nonneg (x : ℝ) : 0 ≤ inverseQuadraticTest x := by
  change 0 ≤ (1 + x ^ 2)⁻¹
  positivity

private theorem inverseQuadraticTest_le_one (x : ℝ) : inverseQuadraticTest x ≤ 1 := by
  change (1 + x ^ 2)⁻¹ ≤ 1
  rw [inv_le_one₀ (by positivity)]
  nlinarith [sq_nonneg x]

private theorem inverseQuadraticTest_pos (x : ℝ) : 0 < inverseQuadraticTest x := by
  change 0 < (1 + x ^ 2)⁻¹
  positivity

private theorem scaledIdentityTest_neg (R : ℝ) (hR : 0 < R) (x : ℝ) :
    scaledIdentityTest R hR (-x) = -scaledIdentityTest R hR x := by
  change R * (-x) / (R + |-x|) = -(R * x / (R + |x|))
  simp [abs_neg, neg_div]

private theorem scaledIdentityTest_sub_bound {R : ℝ} (hR : 0 < R) (x : ℝ) :
    |scaledIdentityTest R hR x - x| ≤ x ^ 2 / R := by
  have hden : 0 < R + |x| := by positivity
  change |R * x / (R + |x|) - x| ≤ x ^ 2 / R
  have hform : R * x / (R + |x|) - x = -(x * |x| / (R + |x|)) := by
    field_simp
    ring
  have hnum : abs (x * abs x) = x ^ 2 := by
    calc
      abs (x * abs x) = abs x * abs (abs x) := abs_mul _ _
      _ = abs x * abs x := by rw [abs_abs]
      _ = x ^ 2 := by ring_nf; rw [sq_abs]
  rw [hform, abs_neg, abs_div, hnum, abs_of_pos hden]
  exact div_le_div_of_nonneg_left (sq_nonneg x) hR
    (by linarith [abs_nonneg x])

private theorem scaledIdentityTest_abs_le {R : ℝ} (hR : 0 < R) (x : ℝ) :
    |scaledIdentityTest R hR x| ≤ R := by
  change |R * x / (R + |x|)| ≤ R
  have hden : 0 < R + |x| := by positivity
  rw [abs_div, abs_mul, abs_of_pos hR, abs_of_pos hden]
  apply (div_le_iff₀ hden).2
  nlinarith [abs_nonneg x]

private theorem integrable_scaledIdentityTest {μ : Measure ℝ} [IsFiniteMeasure μ] {R : ℝ}
    (hR : 0 < R) : Integrable (scaledIdentityTest R hR : ℝ → ℝ) μ := by
  apply Integrable.of_bound (scaledIdentityTest R hR).continuous.aestronglyMeasurable R
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs] using scaledIdentityTest_abs_le hR x

private theorem integral_scaledIdentityTest_gaussian_eq_zero {R : ℝ} (hR : 0 < R) :
    ∫ x, scaledIdentityTest R hR x ∂gaussianReal 0 1 = 0 := by
  let G : Measure ℝ := gaussianReal 0 1
  have hG : G.map (fun x : ℝ => -x) = G := by
    change (gaussianReal 0 1).map (fun x : ℝ => -x) = gaussianReal 0 1
    rw [gaussianReal_map_neg]
    norm_num
  have hInt : Integrable (scaledIdentityTest R hR : ℝ → ℝ) G :=
    integrable_scaledIdentityTest hR
  have hEq : ∫ x, scaledIdentityTest R hR x ∂G =
      ∫ x, scaledIdentityTest R hR (-x) ∂G := by
    have hIntMap : AEStronglyMeasurable (scaledIdentityTest R hR : ℝ → ℝ)
        (G.map (fun x : ℝ => -x)) := by
      rw [hG]
      exact hInt.aestronglyMeasurable
    calc
      _ = ∫ x, scaledIdentityTest R hR x ∂G.map (fun x : ℝ => -x) := by rw [hG]
      _ = _ := by
        rw [integral_map (by fun_prop) hIntMap]
  have hOdd : ∫ x, scaledIdentityTest R hR (-x) ∂G =
      -∫ x, scaledIdentityTest R hR x ∂G := by
    rw [show (fun x : ℝ => scaledIdentityTest R hR (-x)) =
        fun x => -scaledIdentityTest R hR x by
          funext x
          exact scaledIdentityTest_neg R hR x, integral_neg]
  have hzero : ∫ x, scaledIdentityTest R hR x ∂G =
      -∫ x, scaledIdentityTest R hR x ∂G := hEq.trans hOdd
  linarith


/-- The logarithm differs from its tangent at one by at most a quadratic error. -/
theorem abs_log_sub_sub_one_le {z : ℝ} (hz : 0 < z) :
    |Real.log z - (z - 1)| ≤ (z - 1) ^ 2 * (1 + z⁻¹) := by
  have hupper := Real.log_le_sub_one_of_pos hz
  have hlower := Real.one_sub_inv_le_log_of_pos hz
  rw [abs_of_nonpos (sub_nonpos.mpr hupper)]
  calc
    -(Real.log z - (z - 1)) = z - 1 - Real.log z := by ring
    _ ≤ z - 1 - (1 - z⁻¹) := by linarith
    _ = (z - 1) ^ 2 * z⁻¹ := by field_simp [ne_of_gt hz]
    _ ≤ (z - 1) ^ 2 * (1 + z⁻¹) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg (z - 1))
      linarith [inv_pos.mpr hz]

/-- If a law with bounded variance is close to the standard Gaussian under two suitable bounded
continuous tests, its mean is close to zero.
The tests are a bounded odd approximation to the identity and `x ↦ (1 + x²)⁻¹`. -/
theorem exists_testFunctions_abs_integral_le (K : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ (h₁ h₂ : ℝ →ᵇ ℝ) (δ : ℝ), 0 < δ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (U : Ω → ℝ), MemLp U 2 μ → Var[U; μ] ≤ K →
        |(∫ ω, h₁ (U ω) ∂μ) - (∫ y, h₁ y ∂(gaussianReal 0 1))| ≤ δ →
        |(∫ ω, h₂ (U ω) ∂μ) - (∫ y, h₂ y ∂(gaussianReal 0 1))| ≤ δ →
        |∫ ω, U ω ∂μ| ≤ η := by
  let h₂ : ℝ →ᵇ ℝ := inverseQuadraticTest
  have h₂IntG : Integrable (h₂ : ℝ → ℝ) (gaussianReal 0 1) := by
    apply Integrable.of_bound h₂.continuous.aestronglyMeasurable 1
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (inverseQuadraticTest_nonneg x)]
    exact inverseQuadraticTest_le_one x
  let g : ℝ := ∫ y, h₂ y ∂(gaussianReal 0 1)
  have hgpos : 0 < g := by
    dsimp [g]
    apply (integral_pos_iff_support_of_nonneg inverseQuadraticTest_nonneg h₂IntG).2
    have hsupport : Function.support (h₂ : ℝ → ℝ) = Set.univ := by
      ext x
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact (inverseQuadraticTest_pos x).ne'
    rw [hsupport]
    simp
  have hgLE : g ≤ 1 := by
    dsimp [g]
    calc
      _ ≤ ∫ _ : ℝ, (1 : ℝ) ∂(gaussianReal 0 1) :=
        integral_mono h₂IntG (integrable_const (1 : ℝ)) (fun x => inverseQuadraticTest_le_one x)
      _ = 1 := by simp
  let A : ℝ := 2 / g
  have hApos : 0 < A := by dsimp [A]; positivity
  have hAone : 1 ≤ A := by
    dsimp [A]
    rw [one_le_div hgpos]
    linarith
  let K₀ : ℝ := max K 0
  let M : ℝ := A + Real.sqrt (4 * K₀ / g)
  have hK₀ : 0 ≤ K₀ := by dsimp [K₀]; positivity
  have hMpos : 0 < M := by
    dsimp [M]
    positivity
  let R : ℝ := 1 + 2 * (K₀ + M ^ 2) / η
  have hR : 0 < R := by
    dsimp [R]
    positivity
  let h₁ : ℝ →ᵇ ℝ := scaledIdentityTest R hR
  let δ : ℝ := min (g / 4) (η / 2)
  have hδpos : 0 < δ := by
    dsimp [δ]
    positivity
  refine ⟨h₁, h₂, δ, hδpos, ?_⟩
  intro Ω _ μ hμ U hU hVar hclose₁ hclose₂
  let V : Ω → ℝ := hU.aestronglyMeasurable.mk U
  have hVmeas : Measurable V := by
    dsimp [V]
    exact hU.aestronglyMeasurable.measurable_mk
  have hUV : U =ᵐ[μ] V := by
    dsimp [V]
    exact hU.aestronglyMeasurable.ae_eq_mk
  have hVmem : MemLp V 2 μ := MemLp.ae_eq hUV hU
  have hVint : Integrable V μ := hVmem.integrable (by norm_num)
  have hVsqInt : Integrable (fun ω => V ω ^ 2) μ :=
    (memLp_two_iff_integrable_sq hVmem.aestronglyMeasurable).1 hVmem
  let m : ℝ := ∫ ω, V ω ∂μ
  have hmeanEq : ∫ ω, U ω ∂μ = m := by
    dsimp [m]
    exact integral_congr_ae hUV
  have hVarV : Var[V; μ] ≤ K₀ := by
    calc
      Var[V; μ] = Var[U; μ] := variance_congr hUV.symm
      _ ≤ K := hVar
      _ ≤ K₀ := le_max_left _ _
  have h2Vint : Integrable (fun ω => h₂ (V ω)) μ := by
    apply Integrable.of_bound (h₂.continuous.measurable.comp hVmeas).aestronglyMeasurable 1
    filter_upwards [] with ω
    change ‖inverseQuadraticTest (V ω)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (inverseQuadraticTest_nonneg (V ω))]
    exact inverseQuadraticTest_le_one (V ω)
  have h2Vclose : |∫ ω, h₂ (V ω) ∂μ - g| ≤ δ := by
    have hae : (fun ω => h₂ (U ω)) =ᵐ[μ] fun ω => h₂ (V ω) := by
      filter_upwards [hUV] with ω hω
      simp [hω]
    rw [← integral_congr_ae hae]
    simpa [h₂, g] using hclose₂
  let E : Set Ω := {ω | |V ω| ≤ A}
  have hEmeas : MeasurableSet E := by
    dsimp [E]
    apply measurableSet_le
    · exact continuous_abs.measurable.comp hVmeas
    · exact measurable_const
  have hEint : Integrable (E.indicator (1 : Ω → ℝ)) μ := by
    rw [integrable_indicator_iff hEmeas]
    exact integrable_const (1 : ℝ)
  have hEintVal : ∫ ω, E.indicator (1 : Ω → ℝ) ω ∂μ = μ.real E :=
    integral_indicator_one hEmeas
  have hEprob : g / 4 ≤ μ.real E := by
    have htail (x : ℝ) (hx : A < |x|) : inverseQuadraticTest x ≤ g / 2 := by
      change (1 + x ^ 2)⁻¹ ≤ g / 2
      have hxsq : A ^ 2 ≤ x ^ 2 := by
        rw [← sq_abs x]
        exact (sq_le_sq₀ hApos.le (abs_nonneg x)).2 (le_of_lt hx)
      have hbase : 1 ≤ (g / 2) * (1 + A ^ 2) := by
        dsimp [A]
        field_simp [ne_of_gt hgpos]
        nlinarith [hgpos, hgLE]
      rw [← one_div]
      apply (div_le_iff₀ (by positivity : 0 < 1 + x ^ 2)).2
      calc
        1 ≤ (g / 2) * (1 + A ^ 2) := hbase
        _ ≤ (g / 2) * (1 + x ^ 2) := by
          gcongr

    have hpoint (ω : Ω) : h₂ (V ω) ≤ E.indicator (1 : Ω → ℝ) ω + g / 2 := by
      by_cases hω : ω ∈ E
      · simp [E, hω]
        change inverseQuadraticTest (V ω) ≤ 1 + g / 2
        linarith [inverseQuadraticTest_le_one (V ω), hgpos]
      · have hx : A < |V ω| := lt_of_not_ge (by simpa [E] using hω)
        have ht := htail (V ω) hx
        simpa [E, hω] using ht
    have hupper := integral_mono h2Vint (hEint.add (integrable_const (g / 2))) hpoint
    have hupper' : ∫ ω, h₂ (V ω) ∂μ ≤ μ.real E + g / 2 := by
      calc
        _ ≤ ∫ ω, E.indicator (1 : Ω → ℝ) ω + g / 2 ∂μ := hupper
        _ = μ.real E + g / 2 := by
          rw [integral_add hEint (integrable_const _)]
          rw [hEintVal]
          simp [integral_const]
    have hδg : δ ≤ g / 4 := by dsimp [δ]; exact min_le_left _ _
    have hlower : g - δ ≤ ∫ ω, h₂ (V ω) ∂μ := by
      have := (abs_le.mp h2Vclose).1
      linarith
    linarith
  have hmeanBound : |m| ≤ M := by
    let q : ℝ := max (|m| - A) 0
    have hqnonneg : 0 ≤ q := by dsimp [q]; exact le_max_right _ _
    have hdevMem : MemLp (fun ω => V ω - m) 2 μ := hVmem.sub (memLp_const m)
    have hdevInt : Integrable (fun ω => (V ω - m) ^ 2) μ :=
      (memLp_two_iff_integrable_sq hdevMem.aestronglyMeasurable).1 hdevMem
    have hvarIntegral : Var[V; μ] = ∫ ω, (V ω - m) ^ 2 ∂μ := by
      dsimp [m]
      exact variance_eq_integral hVmeas.aemeasurable
    have hpoint (ω : Ω) : q ^ 2 * E.indicator (1 : Ω → ℝ) ω ≤
        (V ω - m) ^ 2 := by
      by_cases hω : ω ∈ E
      · have hVabs : |V ω| ≤ A := by simpa [E] using hω
        have htriangle : |m| ≤ |V ω - m| + A := by
          calc
            |m| = |(m - V ω) + V ω| := by congr 1; ring
            _ ≤ |m - V ω| + |V ω| := abs_add_le _ _
            _ = |V ω - m| + |V ω| := by rw [abs_sub_comm]
            _ ≤ |V ω - m| + A := by linarith [hVabs]
        have hqle : q ≤ |V ω - m| := by
          dsimp [q]
          exact max_le (by linarith) (abs_nonneg _)
        have hsq : q ^ 2 ≤ |V ω - m| ^ 2 := by
          nlinarith [abs_nonneg (V ω - m)]
        simpa [hω, E, sq_abs] using hsq
      · simp [E, hω]
        positivity
    have hleftInt : Integrable
        (fun ω => E.indicator (1 : Ω → ℝ) ω * q ^ 2) μ :=
      hEint.mul_const _
    have hqIntegral := integral_mono hleftInt hdevInt (fun ω => by
      simpa [mul_comm] using hpoint ω)
    have hqBound : q ^ 2 * μ.real E ≤ K₀ := by
      calc
        q ^ 2 * μ.real E = (∫ ω, E.indicator (1 : Ω → ℝ) ω ∂μ) * q ^ 2 := by
          rw [hEintVal]
          ring
        _ = ∫ ω, E.indicator (1 : Ω → ℝ) ω * q ^ 2 ∂μ := by
          rw [integral_mul_const]
        _ ≤ ∫ ω, (V ω - m) ^ 2 ∂μ := hqIntegral
        _ = Var[V; μ] := hvarIntegral.symm
        _ ≤ K₀ := hVarV
    have hqg : q ^ 2 ≤ 4 * K₀ / g := by
      apply (le_div_iff₀ hgpos).2
      calc
        q ^ 2 * g ≤ q ^ 2 * (4 * μ.real E) := by
          gcongr
          linarith
        _ ≤ 4 * K₀ := by nlinarith [hqBound]
    have hqle : q ≤ Real.sqrt (4 * K₀ / g) :=
      (Real.le_sqrt hqnonneg (div_nonneg
        (mul_nonneg (by norm_num) hK₀) hgpos.le)).2 hqg
    have hmeanq : |m| ≤ A + q := by
      dsimp [q]
      have h := le_max_left (|m| - A) 0
      linarith
    dsimp [M]
    linarith
  have h1Vint : Integrable (fun ω => h₁ (V ω)) μ := by
    apply Integrable.of_bound (h₁.continuous.measurable.comp hVmeas).aestronglyMeasurable R
    filter_upwards [] with ω
    rw [Real.norm_eq_abs]
    exact scaledIdentityTest_abs_le hR (V ω)
  have h1UtoV : (fun ω => h₁ (U ω)) =ᵐ[μ] fun ω => h₁ (V ω) := by
    filter_upwards [hUV] with ω hω
    simp [hω]
  have h1Vclose : |∫ ω, h₁ (V ω) ∂μ| ≤ δ := by
    have hclose := hclose₁
    rw [integral_congr_ae h1UtoV] at hclose
    rw [integral_scaledIdentityTest_gaussian_eq_zero hR] at hclose
    simpa [h₁, h₂, R] using hclose
  have hsecond : ∫ ω, V ω ^ 2 ∂μ = Var[V; μ] + m ^ 2 := by
    have h := variance_eq_sub hVmem
    dsimp [m] at h
    linarith
  have hsecondBound : ∫ ω, V ω ^ 2 ∂μ ≤ K₀ + M ^ 2 := by
    rw [hsecond]
    have hmSq : m ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs m]
      exact (sq_le_sq₀ (abs_nonneg m) hMpos.le).2 hmeanBound
    exact add_le_add hVarV hmSq
  have hdiffInt : Integrable (fun ω => h₁ (V ω) - V ω) μ := h1Vint.sub hVint
  have hscaledInt : Integrable (fun ω => V ω ^ 2 / R) μ := by
    simpa [div_eq_mul_inv, mul_comm] using hVsqInt.const_mul R⁻¹
  have hdiffBound : |(∫ ω, h₁ (V ω) ∂μ) - m| ≤ (∫ ω, V ω ^ 2 ∂μ) / R := by
    have hpoint (ω : Ω) :
        -(V ω ^ 2 / R) ≤ h₁ (V ω) - V ω ∧ h₁ (V ω) - V ω ≤ V ω ^ 2 / R := by
      have h := scaledIdentityTest_sub_bound hR (V ω)
      have habs := abs_le.mp h
      constructor
      · have hleft := habs.1
        change -(V ω ^ 2 / R) ≤ h₁ (V ω) - V ω
        simpa [h₁] using hleft
      · have hright := habs.2
        change h₁ (V ω) - V ω ≤ V ω ^ 2 / R
        simpa [h₁] using hright
    have hupper := integral_mono hdiffInt hscaledInt (fun ω => (hpoint ω).2)
    have hlower := integral_mono hscaledInt.neg hdiffInt (fun ω => (hpoint ω).1)
    have hW : ∫ ω, V ω ^ 2 / R ∂μ = (∫ ω, V ω ^ 2 ∂μ) / R := by
      exact integral_div R (fun ω => V ω ^ 2)
    have hdiffEq : ∫ ω, h₁ (V ω) - V ω ∂μ =
        (∫ ω, h₁ (V ω) ∂μ) - m := by
      rw [integral_sub h1Vint hVint]
    change ∫ ω, -(V ω ^ 2 / R) ∂μ ≤ ∫ ω, h₁ (V ω) - V ω ∂μ at hlower
    rw [integral_neg, hdiffEq, hW] at hlower
    rw [hdiffEq, hW] at hupper
    rw [abs_le]
    constructor <;> linarith
  have herrBound : (∫ ω, V ω ^ 2 ∂μ) / R ≤ η / 2 := by
    apply (div_le_iff₀ hR).2
    have hnonneg : 0 ≤ K₀ + M ^ 2 := by positivity
    calc
      _ ≤ K₀ + M ^ 2 := hsecondBound
      _ ≤ η / 2 * R := by
        rw [show R = 1 + 2 * (K₀ + M ^ 2) / η by rfl]
        field_simp [ne_of_gt hη]
        nlinarith [hnonneg, hη]
  have hmeanSmall : |m| ≤ η := by
    have hcloseAbs : |∫ ω, h₁ (V ω) ∂μ| ≤ δ := h1Vclose
    have htriangle : |m| ≤ |(∫ ω, h₁ (V ω) ∂μ) - m| +
        |∫ ω, h₁ (V ω) ∂μ| := by
      calc
        |m| = |m - (∫ ω, h₁ (V ω) ∂μ) + ∫ ω, h₁ (V ω) ∂μ| := by congr 1; ring
        _ ≤ |m - (∫ ω, h₁ (V ω) ∂μ)| + |∫ ω, h₁ (V ω) ∂μ| := abs_add_le _ _
        _ = _ := by rw [abs_sub_comm]
    have hδeta : δ ≤ η / 2 := by dsimp [δ]; exact min_le_right _ _
    linarith [htriangle, hdiffBound.trans herrBound]
  rw [hmeanEq]
  exact hmeanSmall

end Critical2DKPZ.LogNormality

end
