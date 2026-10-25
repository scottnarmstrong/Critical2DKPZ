/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.ConditionalThreeBlockSlice
public import Critical2DKPZ.NonGaussian.PositiveRatios
import Mathlib.Tactic

/-! # Conditional bounds for normalized Gaussian-smoothed three-block chains -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.SHF.Tsai
open scoped ENNReal

namespace Critical2DKPZ.NonGaussian

/-- For independent blocks whose middle block has heat-block mean, the normalized nonnegative
three-block chain is integrable and its conditional expectation given the outer blocks
is at most `(2πτ)⁻¹` times the last terminal mass. -/
theorem condExp_normalized_threeBlock_chain_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Fin 3 → Ω → Measure (Plane × Plane)) (hB : ∀ i, Measurable (B i))
    (hBLF : ∀ i, ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (B i ω)) (hind : iIndepFun B P)
    (f g : Plane → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε) (hmean : P.bind (B 1) = heatBlock τ)
    (hLast : (∫⁻ ω, ∫⁻ p, g p.2 ∂B 2 ω ∂P) ≠ ∞) :
    Integrable (fun ω => ((∫⁻ p, f p.1 * g p.2
      ∂chainProduct (fun k => if k = 0 then B 0 ω else if k = 1 then B 1 ω else B 2 ω)
        (fun _ => heatKernel ε) 2) / (∫⁻ p, f p.1 ∂B 0 ω)).toReal) P ∧
    P[fun ω => ((∫⁻ p, f p.1 * g p.2
      ∂chainProduct (fun k => if k = 0 then B 0 ω else if k = 1 then B 1 ω else B 2 ω)
        (fun _ => heatKernel ε) 2) / (∫⁻ p, f p.1 ∂B 0 ω)).toReal |
      MeasurableSpace.comap (B 0) inferInstance ⊔ MeasurableSpace.comap (B 2) inferInstance]
      ≤ᵐ[P] fun ω => (2 * Real.pi * τ)⁻¹ * (∫⁻ p, g p.2 ∂B 2 ω).toReal := by
  classical
  let E : CompactExhaustion (Plane × Plane) := RandomMeasure.vagueCompactExhaustion (Plane × Plane)
  let M : Measure (Plane × Plane) → Measure (Plane × Plane) :=
    RandomMeasure.locallyFiniteMeasureModification E id
  have hM : Measurable M :=
    RandomMeasure.measurable_locallyFiniteMeasureModification E id measurable_id
  have hMLF (μ : Measure (Plane × Plane)) : IsLocallyFiniteMeasure (M μ) :=
    RandomMeasure.locallyFinite_locallyFiniteMeasureModification E id μ
  let X : Ω → Measure (Plane × Plane) × Measure (Plane × Plane) := fun ω => (B 0 ω, B 2 ω)
  have hX : Measurable X := (hB 0).prodMk (hB 2)
  let C (k : ℕ) (a : Measure (Plane × Plane) × Measure (Plane × Plane)) : Measure (Plane × Plane) :=
    if k = 0 then M a.1 else if k = 1 then 0 else M a.2
  have hC (k : ℕ) (_ : k ≤ 2) : Measurable (C k) := by
    by_cases h0 : k = 0
    · simpa only [C, h0, ↓reduceIte, Function.comp_def] using hM.comp measurable_fst
    · by_cases h1 : k = 1
      · simpa only [C, h0, h1, ↓reduceIte, Nat.one_ne_zero, Function.comp_def] using (measurable_const : Measurable (fun _ => (0 : Measure (Plane × Plane))))
      · simpa only [C, h0, h1, ↓reduceIte, Nat.one_ne_zero, Function.comp_def] using hM.comp measurable_snd
  have hCLF (a) (k : ℕ) (_ : k ≤ 2) : IsLocallyFiniteMeasure (C k a) := by
    dsimp only [C]
    split_ifs
    · exact hMLF _
    · infer_instance
    · exact hMLF _
  have hC0 : ∀ᵐ ω ∂P, C 0 (X ω) = B 0 ω := by
    filter_upwards [hBLF 0] with ω hω
    exact RandomMeasure.locallyFiniteMeasureModification_apply_of_isLocallyFinite E id (B 0 ω) hω
  have hC2 : ∀ᵐ ω ∂P, C 2 (X ω) = B 2 ω := by
    filter_upwards [hBLF 2] with ω hω
    exact RandomMeasure.locallyFiniteMeasureModification_apply_of_isLocallyFinite E id (B 2 ω) hω
  have hLastC : (∫⁻ ω, ∫⁻ p, g p.2 ∂C 2 (X ω) ∂P) ≠ ∞ := by
    convert hLast using 1
    apply lintegral_congr_ae
    filter_upwards [hC2] with ω hω
    rw [hω]
  have hCE := condExp_normalized_threeBlock_slice_le P X hX (B 1) (hB 1) (hBLF 1)
    (hind.indepFun_prodMk hB 0 2 1 (by decide) (by decide)) C hC hCLF f g hf hg hτ hε hmean hLastC
  let R (ω : Ω) := ((∫⁻ p, f p.1 * g p.2
    ∂chainProduct (fun k => if k = 0 then B 0 ω else if k = 1 then B 1 ω else B 2 ω)
      (fun _ => heatKernel ε) 2) / (∫⁻ p, f p.1 ∂B 0 ω)).toReal
  let S (ω : Ω) := (∫⁻ q, (∫⁻ p, f p.1 ∂C 0 (X ω))⁻¹ *
    positiveChainBlockTest 2 1 (fun k => C k (X ω)) (fun _ => heatKernel ε)
      (fun p => f p.1 * g p.2) q ∂B 1 ω).toReal
  have hSR : S =ᵐ[P] R := by
    filter_upwards [ae_all_iff.2 hBLF, hC0, hC2] with ω hω hω0 hω2
    let μ : ℕ → Measure (Plane × Plane) :=
      fun k => if k = 0 then B 0 ω else if k = 1 then B 1 ω else B 2 ω
    have hμ (k : ℕ) : IsLocallyFiniteMeasure (μ k) := by
      dsimp only [μ]
      split_ifs
      · exact hω 0
      · exact hω 1
      · exact hω 2
    let : ∀ k, IsLocallyFiniteMeasure (μ k) := hμ
    have hCsf (k : ℕ) : IsLocallyFiniteMeasure (C k (X ω)) := by
      dsimp only [C]
      split_ifs
      · exact hMLF _
      · infer_instance
      · exact hMLF _
    let : ∀ k, IsLocallyFiniteMeasure (C k (X ω)) := hCsf
    have hslice : positiveChainBlockTest 2 1 (fun k => C k (X ω)) (fun _ => heatKernel ε)
        (fun p => f p.1 * g p.2) = positiveChainBlockTest 2 1 μ (fun _ => heatKernel ε)
          (fun p => f p.1 * g p.2) := by
      funext q
      rw [positiveChainBlockTest_three_heat_eq _ f g hf hg ε,
        positiveChainBlockTest_three_heat_eq μ f g hf hg ε, hω0, hω2]
      rfl
    change (∫⁻ q, (∫⁻ p, f p.1 ∂C 0 (X ω))⁻¹ *
      positiveChainBlockTest 2 1 (fun k => C k (X ω)) (fun _ => heatKernel ε)
        (fun p => f p.1 * g p.2) q ∂B 1 ω).toReal =
      ((∫⁻ p, f p.1 * g p.2 ∂chainProduct μ (fun _ => heatKernel ε) 2) /
        (∫⁻ p, f p.1 ∂μ 0)).toReal
    rw [normalized_threeBlock_chain_eq_slice μ f g hf hg ε, hslice, hω0]
    rfl
  refine ⟨hCE.1.congr hSR, ?_⟩
  have hcond : P[S | MeasurableSpace.comap X inferInstance] =ᵐ[P]
      P[R | MeasurableSpace.comap X inferInstance] := condExp_congr_ae hSR
  rw [show MeasurableSpace.comap X inferInstance =
    MeasurableSpace.comap (B 0) inferInstance ⊔ MeasurableSpace.comap (B 2) inferInstance from
      MeasurableSpace.comap_prodMk (B 0) (B 2)] at hCE hcond
  filter_upwards [hCE.2, hcond, hC2] with ω hω hωcond hω2
  rw [← hωcond]
  simpa only [hω2] using hω

/-- For nonnegative real pairings with almost-everywhere spatial integrability, the normalized
three-block chain is integrable and obeys the conditional bound `(2πτ)⁻¹` times the last terminal mass. -/
theorem condExp_real_normalized_threeBlock_chain_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Fin 3 → Ω → Measure (Plane × Plane)) (hB : ∀ i, Measurable (B i))
    (hBLF : ∀ i, ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (B i ω)) (hind : iIndepFun B P)
    (f g : Plane → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε) (hmean : P.bind (B 1) = heatBlock τ)
    (hLast : (∫⁻ ω, ∫⁻ p, ENNReal.ofReal (g p.2) ∂B 2 ω ∂P) ≠ ∞)
    (hnum : ∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane => f p.1 * g p.2)
      (chainProduct (fun k => if k = 0 then B 0 ω else if k = 1 then B 1 ω else B 2 ω)
        (fun _ => heatKernel ε) 2))
    (hden : ∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane => f p.1) (B 0 ω)) :
    Integrable (fun ω => (∫ p, f p.1 * g p.2
      ∂chainProduct (fun k => if k = 0 then B 0 ω else if k = 1 then B 1 ω else B 2 ω)
        (fun _ => heatKernel ε) 2) / (∫ p, f p.1 ∂B 0 ω)) P ∧
    P[fun ω => (∫ p, f p.1 * g p.2
      ∂chainProduct (fun k => if k = 0 then B 0 ω else if k = 1 then B 1 ω else B 2 ω)
        (fun _ => heatKernel ε) 2) / (∫ p, f p.1 ∂B 0 ω) |
      MeasurableSpace.comap (B 0) inferInstance ⊔ MeasurableSpace.comap (B 2) inferInstance]
      ≤ᵐ[P] fun ω => (2 * Real.pi * τ)⁻¹ * ∫ p, g p.2 ∂B 2 ω := by
  let R (ω : Ω) := ((∫⁻ p, ENNReal.ofReal (f p.1) * ENNReal.ofReal (g p.2)
    ∂chainProduct (fun k => if k = 0 then B 0 ω else if k = 1 then B 1 ω else B 2 ω)
      (fun _ => heatKernel ε) 2) / (∫⁻ p, ENNReal.ofReal (f p.1) ∂B 0 ω)).toReal
  let S (ω : Ω) := (∫ p, f p.1 * g p.2
    ∂chainProduct (fun k => if k = 0 then B 0 ω else if k = 1 then B 1 ω else B 2 ω)
      (fun _ => heatKernel ε) 2) / (∫ p, f p.1 ∂B 0 ω)
  have hRS : R =ᵐ[P] S := by
    filter_upwards [hnum, hden] with ω hωn hωd
    exact positiveTensorRatio_toReal_eq _ _ f g hf0 hg0 hωn hωd
  have hC := condExp_normalized_threeBlock_chain_le P B hB hBLF hind
    (fun x => ENNReal.ofReal (f x)) (fun x => ENNReal.ofReal (g x))
    hf.ennreal_ofReal hg.ennreal_ofReal hτ hε hmean hLast
  refine ⟨hC.1.congr hRS, ?_⟩
  have hQ : Measurable (fun ω => ∫⁻ p, ENNReal.ofReal (g p.2) ∂B 2 ω) :=
    (Measure.measurable_lintegral ((hg.comp measurable_snd).ennreal_ofReal)).comp (hB 2)
  have hfinite := ae_lt_top' hQ.aemeasurable hLast
  have hcond := condExp_congr_ae (m := MeasurableSpace.comap (B 0) inferInstance ⊔
    MeasurableSpace.comap (B 2) inferInstance) hRS
  filter_upwards [hC.2, hcond, hfinite] with ω hω hωcond hωfin
  rw [← hωcond]
  have hgi : Integrable (fun p : Plane × Plane => g p.2) (B 2 ω) :=
    (lintegral_ofReal_ne_top_iff_integrable (hg.comp measurable_snd).aestronglyMeasurable
      (Eventually.of_forall fun p => hg0 p.2)).1 hωfin.ne
  have hreal : (∫⁻ p, ENNReal.ofReal (g p.2) ∂B 2 ω).toReal = ∫ p, g p.2 ∂B 2 ω := by
    rw [← ofReal_integral_eq_lintegral_ofReal hgi (Eventually.of_forall fun p => hg0 p.2),
      ENNReal.toReal_ofReal (integral_nonneg fun p : Plane × Plane => hg0 p.2)]
  simpa only [hreal] using hω

end Critical2DKPZ.NonGaussian

end
