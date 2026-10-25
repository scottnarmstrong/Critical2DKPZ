/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.HeatField
public import Critical2DKPZ.Definitions.KpzRegularizedReversed
public import Critical2DKPZ.Definitions.TestFnDilate
public import Critical2DKPZ.Definitions.IsCriticalKPZ
public import Critical2DKPZ.Definitions.ShfSigma
import Critical2DKPZ.Extensions.ScaleLimit.CheckFieldRegularization
import Critical2DKPZ.Provider.ThmToyJoint
import Critical2DKPZ.Assembly.Final
import Critical2DKPZ.Assembly.RootInputs
import Mathlib.Tactic

/-! # One jointly coupled reversed field at every smoothing width

The toy joint limit supplies one SHF-measurable field. Its finite tested laws
agree with every associated critical KPZ field. The point comparison adapts the
proof in `SmallScales.PointMatchedComparison`, keeping that same field throughout.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open Critical2DKPZ.SmallScales Critical2DKPZ.LocalSobolev
open scoped BoundedContinuousFunction ENNReal Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- A fixed reversed check field has all finite tested laws of the height field,
a quantitative regularization rate, and the uniform centered point comparison. -/
theorem exists_checkField (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z) :
    ∃ Hc : TestFn → Ω → ℝ,
      (∀ ψ, Measurable[shfSigma Z] (Hc ψ)) ∧
      (∀ H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr, IsCriticalKPZ P Z H →
        ∀ (k : ℕ) (ψ : Fin k → TestFn),
          P.map (fun ω i => Hc (ψ i) ω) = P.map (fun ω i => H 1 0 ω (ψ i))) ∧
      (∀ ψ : TestFn, ∃ C δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ ∈ Set.Ioo 0 δ₁,
        eLpNorm (fun ω => (∫ y, ψ y * kpzRegularizedReversed P Z 0 1 δ 0 y ω) -
          Hc ψ ω) 2 P ≤ ENNReal.ofReal (C * |Real.log δ| ^ (-(1 : ℝ) / 40))) ∧
      (∀ φ : TestFn, (∀ y, 0 ≤ φ y) → (∫ y, φ y) = 1 → barycentre φ = 0 →
        ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Set.Ioo 0 ε₀,
          Integrable (fun ω => Hc (φ.dilate ε 0) ω -
            (Fheat Z (ε ^ 2) 0 ω - ∫ ω', Fheat Z (ε ^ 2) 0 ω' ∂P)) P ∧
          ∫ ω, |Hc (φ.dilate ε 0) ω -
            (Fheat Z (ε ^ 2) 0 ω - ∫ ω', Fheat Z (ε ^ 2) 0 ω' ∂P)| ∂P ≤ C) := by
  let T : ℝ := 1
  have hT : 0 < T := zero_lt_one
  have hsym := Assembly.shfSymmetriesAt ϑ P Z hZ
  have hHeatStartLogInput := Assembly.heatStartLogAt_of_isCriticalSHF ϑ P Z hZ
  have hHeatStartLogFieldInput := Assembly.heatStartLogFieldAt_of_isCriticalSHF ϑ P Z hZ
  have hLatticeSmoothingEnergyInput := Assembly.latticeSmoothingErrorEnergy
  obtain ⟨X, hXm, hXrate, hXconv, _hXlat, hXlaw⟩ :=
    Critical2DKPZ.Provider.thm_toy_joint ϑ P Z hZ T hT
  let Hc : TestFn → Ω → ℝ := fun ψ => X 0 0 ψ
  refine ⟨Hc, ?_, ?_, ?_, ?_⟩
  · intro ψ
    exact hXm 0 0 ψ le_rfl hT
  · intro H hH k ψ
    have hh := hXlaw H hH k (fun _ => 0) (fun _ => 0) ψ
      (fun _ => ⟨le_rfl, hT⟩)
    simpa only [Hc, T, sub_zero] using hh
  · intro ψ
    obtain ⟨C, δ₁, hδ₁, hbound⟩ := hXrate 0 ψ 1 zero_lt_one le_rfl
    refine ⟨C, δ₁, hδ₁, ?_⟩
    intro δ hδ
    have hh := hbound δ hδ.1 hδ.2 0 le_rfl (by norm_num [T])
    simpa only [Hc, T, sub_zero, div_one] using hh
  · intro φ hφ hφ₁ hb
    let x : Plane := 0
    obtain ⟨Creg, εreg, hεreg, hreg⟩ :=
      kpzRegularizedReversed_shrinking_le_of ϑ P Z hZ hHeatStartLogInput hHeatStartLogFieldInput hLatticeSmoothingEnergyInput hT φ
    let ε₀ : ℝ := min εreg (Real.sqrt T / 2)
    have hε₀ : 0 < ε₀ := by
      dsimp [ε₀]
      exact lt_min hεreg (half_pos (Real.sqrt_pos.mpr hT))
    refine ⟨1 + max Creg 0 + ∫ y, φ y * ‖y - barycentre φ‖ ^ 2, ε₀, hε₀, ?_⟩
    intro ε hεI
    obtain ⟨hε, hε₀'⟩ := hεI
    have hεreg' : ε < εreg := lt_of_lt_of_le hε₀' (min_le_left _ _)
    have hεsqrt : ε < Real.sqrt T / 2 := lt_of_lt_of_le hε₀' (min_le_right _ _)
    have hεT : ε ^ 2 < T := by
      have hsq : ε ^ 2 < (Real.sqrt T / 2) ^ 2 := by
        nlinarith [sq_nonneg (ε - Real.sqrt T / 2)]
      rw [div_pow, Real.sq_sqrt hT.le] at hsq
      nlinarith
    let base : TestFn := φ.dilate ε x
    let Aε : Ω → ℝ := fun ω => ∫ y, base y *
      kpzRegularizedReversed P Z 0 T (ε ^ 2) 0 y ω
    let F : Ω → ℝ := fun ω => X 0 0 base ω
    let G : Ω → ℝ := fun ω => heatStartLog Z (ε ^ 2) T (ε ^ 2)
      (x + ε • barycentre φ) ω -
        ∫ ω', heatStartLog Z (ε ^ 2) T (ε ^ 2)
          (x + ε • barycentre φ) ω' ∂P
    have hconv := hXconv 0 0 base 2 (by norm_num) hT (by norm_num) (by norm_num)
    have happroxEvent : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0),
        eLpNorm (fun ω => (∫ y, base y *
          kpzRegularizedReversed P Z 0 T δ 0 y ω) - F ω) 2 P < 1 :=
      hconv.eventually (Iio_mem_nhds (by norm_num))
    have hδsmall : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), δ < ε ^ 2 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (sq_pos_of_pos hε))
    obtain ⟨δ, ⟨⟨hδconv, hδε⟩, hδpos⟩⟩ :=
      ((happroxEvent.and hδsmall).and eventually_mem_nhdsWithin).exists
    have hδle : δ ≤ ε ^ 2 := le_of_lt hδε
    let Aδ : Ω → ℝ := fun ω => ∫ y, base y *
      kpzRegularizedReversed P Z 0 T δ 0 y ω
    have happrox' : eLpNorm (fun ω => F ω -
        (∫ y, base y * kpzRegularizedReversed P Z 0 T δ 0 y ω)) 2 P ≤ ENNReal.ofReal 1 := by
      have hneg := le_of_lt hδconv
      have hEq : (fun ω => F ω -
          (∫ y, base y * kpzRegularizedReversed P Z 0 T δ 0 y ω)) =
          fun ω => -((∫ y, base y * kpzRegularizedReversed P Z 0 T δ 0 y ω) - F ω) := by
        funext ω
        ring
      rw [hEq]
      change eLpNorm (-fun ω =>
        (∫ y, base y * kpzRegularizedReversed P Z 0 T δ 0 y ω) - F ω) 2 P ≤ _
      rw [eLpNorm_neg]
      simpa using hneg
    have hreg' := hreg ε hε hεreg' x δ hδpos hδle
    have hmidAE := checkField_regularized_integral_sub_ae ϑ P Z hZ
      (T := T) (α := ε ^ 2) (β := δ) (sq_pos_of_pos hε) hεT hδpos
      (lt_of_le_of_lt hδle hεT) base
    let f₁ : Ω → ℝ := fun ω => F ω - Aδ ω
    let f₂ : Ω → ℝ := fun ω => Aδ ω - Aε ω
    let f₃ : Ω → ℝ := fun ω => Aε ω - G ω
    have hf₁bound : eLpNorm f₁ 2 P ≤ ENNReal.ofReal 1 := by
      have hEq : f₁ = fun ω => F ω -
          (∫ y, base y * kpzRegularizedReversed P Z 0 T δ 0 y ω) := by
        funext ω
        rfl
      simpa only [f₁, Aδ] using happrox'
    have hf₂bound : eLpNorm f₂ 2 P ≤ ENNReal.ofReal Creg := by
      have hEq : f₂ =ᵐ[P] fun ω => -∫ y, base y *
          (kpzRegularizedReversed P Z 0 T (ε ^ 2) 0 y ω -
            kpzRegularizedReversed P Z 0 T δ 0 y ω) := by
        filter_upwards [hmidAE] with ω hω
        dsimp [f₂, Aδ, Aε]
        rw [hω]
        ring
      calc
        eLpNorm f₂ 2 P = eLpNorm (fun ω => -∫ y, base y *
            (kpzRegularizedReversed P Z 0 T (ε ^ 2) 0 y ω -
              kpzRegularizedReversed P Z 0 T δ 0 y ω)) 2 P := eLpNorm_congr_ae hEq
        _ = eLpNorm (fun ω => ∫ y, base y *
            (kpzRegularizedReversed P Z 0 T (ε ^ 2) 0 y ω -
              kpzRegularizedReversed P Z 0 T δ 0 y ω)) 2 P := by
          change eLpNorm (-fun ω => ∫ y, base y *
            (kpzRegularizedReversed P Z 0 T (ε ^ 2) 0 y ω -
              kpzRegularizedReversed P Z 0 T δ 0 y ω)) 2 P = _
          exact eLpNorm_neg (fun ω => ∫ y, base y *
            (kpzRegularizedReversed P Z 0 T (ε ^ 2) 0 y ω -
              kpzRegularizedReversed P Z 0 T δ 0 y ω)) 2 P
        _ ≤ ENNReal.ofReal Creg := hreg'
    have hf₁ := checkField_integral_abs_le_eLpNorm_two P f₁ 1 hf₁bound
    have hf₂ := checkField_integral_abs_le_eLpNorm_two P f₂ Creg hf₂bound
    have hcenterAE := checkField_regularized_average_centered_ae ϑ P Z hZ hsym
      hT hε hεT φ hφ₁ x
    have haverage := heatStartLog_average_sub_le_of ϑ P Z hZ hsym hT φ hφ hφ₁ x hε hεT
    have hf₃eq : f₃ =ᵐ[P] fun ω => (∫ y, base y *
        heatStartLog Z (ε ^ 2) T (ε ^ 2) y ω) -
          heatStartLog Z (ε ^ 2) T (ε ^ 2)
            (x + ε • barycentre φ) ω := by
      filter_upwards [hcenterAE] with ω hω
      dsimp [f₃, Aε, G, base] at hω ⊢
      exact hω
    have hf₃ : Integrable f₃ P := haverage.1.congr hf₃eq.symm
    have hf₃bound : ∫ ω, |f₃ ω| ∂P ≤ ∫ y, φ y * ‖y - barycentre φ‖ ^ 2 := by
      calc
        ∫ ω, |f₃ ω| ∂P = ∫ ω, |(∫ y, base y *
            heatStartLog Z (ε ^ 2) T (ε ^ 2) y ω) -
              heatStartLog Z (ε ^ 2) T (ε ^ 2)
                (x + ε • barycentre φ) ω| ∂P := by
          apply integral_congr_ae
          filter_upwards [hf₃eq] with ω hω
          rw [hω]
        _ ≤ ∫ y, φ y * ‖y - barycentre φ‖ ^ 2 := haverage.2
    have hdecomp : (fun ω => F ω - G ω) = fun ω => f₁ ω + f₂ ω + f₃ ω := by
      funext ω
      simp only [f₁, f₂, f₃, Aδ, Aε]
      ring
    have hsumInt : Integrable (fun ω => f₁ ω + f₂ ω + f₃ ω) P :=
      (hf₁.1.add hf₂.1).add hf₃
    have htargetInt : Integrable (fun ω => F ω - G ω) P := hsumInt.congr
      (Filter.Eventually.of_forall fun ω => (congrFun hdecomp ω).symm)
    have hsumAbsInt : Integrable (fun ω => |f₁ ω| + |f₂ ω| + |f₃ ω|) P :=
      (hf₁.1.abs.add hf₂.1.abs).add hf₃.abs
    have hsumAbs : ∫ ω, |f₁ ω + f₂ ω + f₃ ω| ∂P ≤
        ∫ ω, (|f₁ ω| + |f₂ ω| + |f₃ ω|) ∂P := by
      apply integral_mono (hsumInt.abs) hsumAbsInt
      intro ω
      calc
        |f₁ ω + f₂ ω + f₃ ω| ≤ |f₁ ω + f₂ ω| + |f₃ ω| := abs_add_le _ _
        _ ≤ |f₁ ω| + |f₂ ω| + |f₃ ω| := by
          calc
            |f₁ ω + f₂ ω| + |f₃ ω| ≤ (|f₁ ω| + |f₂ ω|) + |f₃ ω| :=
              add_le_add (abs_add_le _ _) (le_refl _)
            _ = |f₁ ω| + |f₂ ω| + |f₃ ω| := rfl
    have hsumBound : ∫ ω, (|f₁ ω| + |f₂ ω| + |f₃ ω|) ∂P ≤
        1 + max Creg 0 + ∫ y, φ y * ‖y - barycentre φ‖ ^ 2 := by
      have h12 : (∫ ω, |f₁ ω| + |f₂ ω| ∂P) =
          (∫ ω, |f₁ ω| ∂P) + ∫ ω, |f₂ ω| ∂P := integral_add hf₁.1.abs hf₂.1.abs
      calc
        (∫ ω, (|f₁ ω| + |f₂ ω|) + |f₃ ω| ∂P) =
            (∫ ω, |f₁ ω| + |f₂ ω| ∂P) + ∫ ω, |f₃ ω| ∂P :=
          integral_add (hf₁.1.abs.add hf₂.1.abs) hf₃.abs
        _ = (∫ ω, |f₁ ω| ∂P) + ∫ ω, |f₂ ω| ∂P + ∫ ω, |f₃ ω| ∂P := by rw [h12]
        _ ≤
            max 1 0 + max Creg 0 + ∫ y, φ y * ‖y - barycentre φ‖ ^ 2 := by
          exact add_le_add (add_le_add hf₁.2 hf₂.2) hf₃bound
        _ = 1 + max Creg 0 + ∫ y, φ y * ‖y - barycentre φ‖ ^ 2 := by simp
    have hfinal : ∫ ω, |F ω - G ω| ∂P ≤
        1 + max Creg 0 + ∫ y, φ y * ‖y - barycentre φ‖ ^ 2 := by
      calc
        ∫ ω, |F ω - G ω| ∂P = ∫ ω, |f₁ ω + f₂ ω + f₃ ω| ∂P := by
          apply integral_congr_ae
          filter_upwards [] with ω
          rw [congrFun hdecomp ω]
        _ ≤ ∫ ω, (|f₁ ω| + |f₂ ω| + |f₃ ω|) ∂P := hsumAbs
        _ ≤ 1 + max Creg 0 + ∫ y, φ y * ‖y - barycentre φ‖ ^ 2 := hsumBound
    constructor
    · simpa only [F, G, base, Hc, T, x, hb, smul_zero, zero_add, heatStartLog, Fheat]
        using htargetInt
    · simpa only [F, G, base, Hc, T, x, hb, smul_zero, zero_add, heatStartLog, Fheat]
        using hfinal


end Critical2DKPZ.Extensions.ScaleLimit
