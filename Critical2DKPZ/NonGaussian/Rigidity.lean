/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.AffineGaussianLaw
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Gaussian rigidity for bounded Ehrhard perturbations -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace Critical2DKPZ.NonGaussian

/-- A centered bounded perturbation `Y` of a centered Gaussian `X` equals `X` almost surely
if `Y` and `X + Y` have Ehrhard-type laws, including at zero variance; see KPZ Lemma 9.3. -/
theorem ae_eq_of_isEhrhardType_of_gaussian {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X Y : Ω → ℝ) (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (σ : NNReal) (hXlaw : P.map X = gaussianReal 0 σ) (hY0 : ∫ ω, Y ω ∂P = 0) (K : ℝ)
    (hK : ∀ᵐ ω ∂P, |Y ω - X ω| ≤ K) (hYE : IsEhrhardType (P.map Y))
    (hXYE : IsEhrhardType (P.map fun ω => X ω + Y ω)) :
    Y =ᵐ[P] X := by
  let s : ℝ := Real.sqrt σ
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hsquare : NNReal.mk (s ^ 2) (sq_nonneg s) = σ := by
    ext
    exact Real.sq_sqrt σ.coe_nonneg
  have hstd : (gaussianReal 0 1).map (fun z => s * z) = gaussianReal 0 σ := by
    have h := standardGaussian_map_affine s 0
    rw [hsquare] at h
    simpa only [add_zero] using h
  have hXstd : P.map X = (gaussianReal 0 1).map (fun z => s * z) := hXlaw.trans hstd.symm
  have hupper : ∀ᵐ ω ∂P, Y ω ≤ X ω + K := by
    filter_upwards [hK] with ω hω
    have hh := (abs_le.mp hω).2
    linarith only [hh]
  have hYeq : P.map Y = P.map X :=
    map_eq_of_isEhrhardType_of_le_gaussian P X Y hX hY s hs hXstd hY0 K hupper hYE
  have hXL : HasLaw X (gaussianReal 0 σ) P := ⟨hX, hXlaw⟩
  have hYL : HasLaw Y (gaussianReal 0 σ) P := ⟨hY, hYeq.trans hXlaw⟩
  have hXp : MemLp X 2 P := hXL.memLp (memLp_id_gaussianReal' 2 (by norm_num))
  have hYp : MemLp Y 2 P := hYL.memLp (memLp_id_gaussianReal' 2 (by norm_num))
  have hXi : Integrable X P := hXp.integrable (by norm_num)
  have hYi : Integrable Y P := hYp.integrable (by norm_num)
  have hX0 : (∫ ω, X ω ∂P) = 0 := hXL.integral_eq.trans integral_id_gaussianReal
  have hS0 : (∫ ω, X ω + Y ω ∂P) = 0 := by
    rw [integral_add hXi hYi, hX0, hY0, add_zero]
  have h2Xm : AEMeasurable (fun ω => 2 * X ω) P := aemeasurable_const.mul hX
  have hSm : AEMeasurable (fun ω => X ω + Y ω) P := hX.add hY
  have h2Xstd : P.map (fun ω => 2 * X ω) =
      (gaussianReal 0 1).map (fun z => (2 * s) * z) := by
    calc
      _ = (P.map X).map (fun x : ℝ => 2 * x) :=
        (AEMeasurable.map_map_of_aemeasurable (g := fun x : ℝ => 2 * x)
          (f := X) (by fun_prop) hX).symm
      _ = _ := by
        rw [hXstd, Measure.map_map (g := fun x : ℝ => 2 * x) (f := fun z : ℝ => s * z)
          (by fun_prop) (by fun_prop)]
        congr 1
        funext z
        dsimp only [Function.comp_apply]
        ring
  have hSumUpper : ∀ᵐ ω ∂P, X ω + Y ω ≤ 2 * X ω + K := by
    filter_upwards [hupper] with ω hω
    linarith only [hω]
  have hSumLaw : P.map (fun ω => X ω + Y ω) = P.map (fun ω => 2 * X ω) :=
    map_eq_of_isEhrhardType_of_le_gaussian P (fun ω => 2 * X ω) (fun ω => X ω + Y ω)
      h2Xm hSm (2 * s) (by positivity) h2Xstd hS0 K hSumUpper hXYE
  have hvarX : variance X P = σ := hXL.variance_eq.trans variance_id_gaussianReal
  have hvarY : variance Y P = σ := hYL.variance_eq.trans variance_id_gaussianReal
  have hSL : HasLaw (fun ω => X ω + Y ω) (P.map (fun ω => 2 * X ω)) P := ⟨hSm, hSumLaw⟩
  have h2L : HasLaw (fun ω => 2 * X ω) (P.map (fun ω => 2 * X ω)) P := ⟨h2Xm, rfl⟩
  have hvarS : variance (fun ω => X ω + Y ω) P = 4 * (σ : ℝ) := by
    rw [hSL.variance_eq.trans h2L.variance_eq.symm, variance_const_mul, hvarX]
    norm_num
  have hvarD : variance (fun ω => X ω - Y ω) P = 0 := by
    have ha := variance_fun_add hXp hYp
    have hb := variance_fun_sub hXp hYp
    rw [hvarS, hvarX, hvarY] at ha
    rw [hvarX, hvarY] at hb
    linarith only [ha, hb]
  have hDmean : (∫ ω, X ω - Y ω ∂P) = 0 := by
    rw [integral_sub hXi hYi, hX0, hY0, sub_self]
  have hD := ae_eq_integral_of_variance_eq_zero (hXp.sub hYp) hvarD
  filter_upwards [hD] with ω hω
  change X ω - Y ω = (∫ x, X x - Y x ∂P) at hω
  rw [hDmean] at hω
  linarith only [hω]

end Critical2DKPZ.NonGaussian

end
