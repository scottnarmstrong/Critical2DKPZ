/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.ThinSlabSeparatedCompactMomentLimit
public import Critical2DKPZ.SHF.Flow.SubseqDenseMoments
public import Critical2DKPZ.SHF.Flow.SlabProductsCore
import Mathlib.Tactic.FinCases

/-! Compact moment convergence on touching polymer blocks follows from independence of consecutive slabs. -/

@[expose] public noncomputable section

open MeasureTheory Filter Set ProbabilityTheory BoundedContinuousFunction
open Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Tsai Critical2DKPZ.DeltaBose
open scoped CompactlySupported Topology BoundedContinuousFunction

namespace Critical2DKPZ.SHF.Flow

private theorem integrable_slabAdjacent_pairing_sq_of_integrable_sixth
    (f : Disorder → ℝ) (h6 : Integrable (fun ω => |f ω| ^ 6) disorderLaw)
    (hfm : Measurable f) : Integrable (fun ω => f ω ^ 2) disorderLaw := by
  have hmajor : Integrable (fun ω => 1 + |f ω| ^ 6) disorderLaw :=
    (integrable_const (1 : ℝ)).add h6
  have hsm : AEStronglyMeasurable (fun ω => f ω ^ 2) disorderLaw :=
    ((continuous_id.pow 2).comp_aestronglyMeasurable hfm.aestronglyMeasurable)
  have hpoint (ω : Disorder) : ‖f ω ^ 2‖ ≤ 1 + |f ω| ^ 6 := by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    by_cases hle : |f ω| ≤ 1
    · have hsquare : |f ω| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg _) hle
      have hpow : f ω ^ 2 = |f ω| ^ 2 := by rw [sq_abs]
      rw [hpow]
      calc
        |f ω| ^ 2 ≤ 1 := hsquare
        _ ≤ 1 + |f ω| ^ 6 := le_add_of_nonneg_right (by positivity)
    · have hge : 1 ≤ |f ω| := le_of_not_ge hle
      have hpow : |f ω| ^ 2 ≤ |f ω| ^ 6 := by
        calc
          |f ω| ^ 2 ≤ |f ω| ^ 2 * |f ω| ^ 4 := by
            exact le_mul_of_one_le_right (sq_nonneg _) (one_le_pow₀ hge)
          _ = |f ω| ^ 6 := by ring
      rw [← sq_abs]
      exact hpow.trans (le_add_of_nonneg_left (by positivity))
  exact hmajor.mono' hsm (Eventually.of_forall hpoint)

/-- The product of squared compact tensor masses on two touching polymer slabs is eventually
integrable and uniformly bounded. The sixth-moment input supplies the required second moments,
and disorder-block independence factors their product. -/
theorem eventually_slabAdjacentTensorMass_sq_bound (ϑ : ℝ)
    (hFlatSixthMomentInput : FlatSixthMomentBound ϑ) {s t u : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (htu : t < u)
    (g g' : C_c(Plane, ℝ)) (hg : ∀ x, 0 ≤ g x) (hg' : ∀ x, 0 ≤ g' x) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω =>
        (∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N s t ω) ^ 2 *
        (∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N t u ω) ^ 2) disorderLaw ∧
      ∫ ω,
        (∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N s t ω) ^ 2 *
        (∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N t u ω) ^ 2
        ∂disorderLaw ≤ C := by
  classical
  let ψ : C_c(Plane × Plane, ℝ) := compactTensorTest g g'
  let A : ℕ → Disorder → ℝ := fun N ω => ∫ p, ψ p ∂polymerMeasure ϑ N s t ω
  let B : ℕ → Disorder → ℝ := fun N ω => ∫ p, ψ p ∂polymerMeasure ϑ N t u ω
  have hAeq (N : ℕ) (ω : Disorder) : A N ω =
      ∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N s t ω := by
    simp [A, ψ, compactTensorTest_apply]
  have hBeq (N : ℕ) (ω : Disorder) : B N ω =
      ∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N t u ω := by
    simp [B, ψ, compactTensorTest_apply]
  have hAnonneg (N : ℕ) (ω : Disorder) : 0 ≤ A N ω := by
    rw [hAeq]
    exact integral_nonneg fun p => mul_nonneg (hg _) (hg' _)
  have hBnonneg (N : ℕ) (ω : Disorder) : 0 ≤ B N ω := by
    rw [hBeq]
    exact integral_nonneg fun p => mul_nonneg (hg _) (hg' _)
  let C₀ : ℝ := (u - s) / 2
  have hC₀ : 0 < C₀ := by dsimp [C₀]; linarith
  obtain ⟨CA, hCA⟩ := eventually_compactTensor_product_rpow_bound ϑ hFlatSixthMomentInput
    1 (by norm_num) (by norm_num) hs hst (fun _ : Fin 1 => g) (fun _ => g')
  obtain ⟨CB, hCB⟩ := eventually_compactTensor_product_rpow_bound ϑ hFlatSixthMomentInput
    1 (by norm_num) (by norm_num) (by linarith) htu (fun _ : Fin 1 => g) (fun _ => g')
  have hA6 : ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω => |A N ω| ^ 6) disorderLaw ∧
        ∫ ω, |A N ω| ^ 6 ∂disorderLaw ≤ CA := by
    filter_upwards [hCA] with N hN
    have heq (ω : Disorder) :
        |∏ i : Fin 1, ∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N s t ω| ^
          ((6 : ℝ) / ((1 : ℕ) : ℝ)) = |A N ω| ^ 6 := by
      have hbase : (∏ i : Fin 1,
          ∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N s t ω) = A N ω := by
        simp [hAeq]
      rw [hbase]
      norm_num [Real.rpow_natCast]
    refine ⟨hN.1.congr (Eventually.of_forall fun ω => heq ω), ?_⟩
    have hIntEq : ∫ ω, |A N ω| ^ 6 ∂disorderLaw =
        ∫ ω, |∏ i : Fin 1,
          ∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N s t ω| ^
            ((6 : ℝ) / ((1 : ℕ) : ℝ)) ∂disorderLaw := by
      apply integral_congr_ae
      exact Eventually.of_forall fun ω => (heq ω).symm
    rw [hIntEq]
    exact hN.2
  have hB6 : ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω => |B N ω| ^ 6) disorderLaw ∧
        ∫ ω, |B N ω| ^ 6 ∂disorderLaw ≤ CB := by
    filter_upwards [hCB] with N hN
    have heq (ω : Disorder) :
        |∏ i : Fin 1, ∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N t u ω| ^
          ((6 : ℝ) / ((1 : ℕ) : ℝ)) = |B N ω| ^ 6 := by
      have hbase : (∏ i : Fin 1,
          ∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N t u ω) = B N ω := by
        simp [hBeq]
      rw [hbase]
      norm_num [Real.rpow_natCast]
    refine ⟨hN.1.congr (Eventually.of_forall fun ω => heq ω), ?_⟩
    have hIntEq : ∫ ω, |B N ω| ^ 6 ∂disorderLaw =
        ∫ ω, |∏ i : Fin 1,
          ∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N t u ω| ^
            ((6 : ℝ) / ((1 : ℕ) : ℝ)) ∂disorderLaw := by
      apply integral_congr_ae
      exact Eventually.of_forall fun ω => (heq ω).symm
    rw [hIntEq]
    exact hN.2
  have hAmeas (N : ℕ) : Measurable (A N) := by
    dsimp [A]
    exact measurable_polymerPairing ϑ N s t ψ
  have hBmeas (N : ℕ) : Measurable (B N) := by
    dsimp [B]
    exact measurable_polymerPairing ϑ N t u ψ
  have hA2meas (N : ℕ) : Measurable (fun ω => A N ω ^ 2) :=
    (continuous_id.pow 2).measurable.comp (hAmeas N)
  have hB2meas (N : ℕ) : Measurable (fun ω => B N ω ^ 2) :=
    (continuous_id.pow 2).measurable.comp (hBmeas N)
  let times : Fin 3 → ℝ := ![s, t, u]
  have htimes : StrictMono times := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [times]
    linarith
  have hBlocks (N : ℕ) := iIndepFun_polymerRadonMeasure_consecutive ϑ N 2 times htimes
  have hAcont : Continuous (fun μ : RandomMeasure.PlanePairRadonMeasure =>
      RandomMeasure.vaguePairing μ ψ) := RandomMeasure.continuous_vaguePairing ψ
  have hAeqRadon (N : ℕ) (ω : Disorder) :
      A N ω = RandomMeasure.vaguePairing (polymerRadonMeasure ϑ N s t ω) ψ := by
    simp [A, RandomMeasure.vaguePairing, polymerRadonMeasure]
  have hBeqRadon (N : ℕ) (ω : Disorder) :
      B N ω = RandomMeasure.vaguePairing (polymerRadonMeasure ϑ N t u ω) ψ := by
    simp [B, RandomMeasure.vaguePairing, polymerRadonMeasure]
  have hIndep (N : ℕ) :
      (fun ω => A N ω ^ 2) ⟂ᵢ[disorderLaw] (fun ω => B N ω ^ 2) := by
    have h := (hBlocks N).indepFun (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)
    have h' : (fun ω => polymerRadonMeasure ϑ N s t ω) ⟂ᵢ[disorderLaw]
        (fun ω => polymerRadonMeasure ϑ N t u ω) := by
      simpa [times] using h
    have h'' := h'.comp hAcont.measurable hAcont.measurable
    have hPow := h''.comp (continuous_id.pow 2).measurable (continuous_id.pow 2).measurable
    have hEqPow : (fun ω => A N ω ^ 2) = fun ω =>
        (RandomMeasure.vaguePairing (polymerRadonMeasure ϑ N s t ω) ψ) ^ 2 := by
      funext ω
      rw [hAeqRadon]
    have hEqPow' : (fun ω => B N ω ^ 2) = fun ω =>
        (RandomMeasure.vaguePairing (polymerRadonMeasure ϑ N t u ω) ψ) ^ 2 := by
      funext ω
      rw [hBeqRadon]
    have hPow' : (fun ω =>
        (RandomMeasure.vaguePairing (polymerRadonMeasure ϑ N s t ω) ψ) ^ 2) ⟂ᵢ[disorderLaw]
        (fun ω =>
          (RandomMeasure.vaguePairing (polymerRadonMeasure ϑ N t u ω) ψ) ^ 2) := by
      simpa only [Function.comp_def, Pi.pow_apply, id_eq] using hPow
    rw [hEqPow, hEqPow']
    exact hPow'
  let MA : ℝ := 1 + max CA 0
  let MB : ℝ := 1 + max CB 0
  have hMA : 0 < MA := by dsimp [MA]; positivity
  have hMB : 0 < MB := by dsimp [MB]; positivity
  have hA2 : ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω => A N ω ^ 2) disorderLaw ∧
        ∫ ω, A N ω ^ 2 ∂disorderLaw ≤ MA := by
    filter_upwards [hA6] with N hN
    have hInt := integrable_slabAdjacent_pairing_sq_of_integrable_sixth (A N) hN.1 (hAmeas N)
    have hmajor : Integrable (fun ω => 1 + |A N ω| ^ 6) disorderLaw :=
      (integrable_const (1 : ℝ)).add hN.1
    have hpoint (ω : Disorder) : A N ω ^ 2 ≤ 1 + |A N ω| ^ 6 := by
      have h := hAnonneg N ω
      by_cases hle : A N ω ≤ 1
      · have hpow : (A N ω) ^ 2 ≤ 1 := pow_le_one₀ h hle
        exact hpow.trans (le_add_of_nonneg_right (by positivity))
      · have hge : 1 ≤ A N ω := le_of_not_ge hle
        have hpow : (A N ω) ^ 2 ≤ (A N ω) ^ 6 := by
          calc
            (A N ω) ^ 2 ≤ (A N ω) ^ 2 * (A N ω) ^ 4 :=
              le_mul_of_one_le_right (sq_nonneg _) (one_le_pow₀ hge)
            _ = (A N ω) ^ 6 := by ring
        rw [abs_of_nonneg h]
        exact hpow.trans (le_add_of_nonneg_left (by positivity))
    have hbound : ∫ ω, A N ω ^ 2 ∂disorderLaw ≤ MA := by
      calc
        ∫ ω, A N ω ^ 2 ∂disorderLaw ≤ ∫ ω, 1 + |A N ω| ^ 6 ∂disorderLaw :=
          integral_mono hInt hmajor (fun ω => by
            simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hpoint ω)
        _ = 1 + ∫ ω, |A N ω| ^ 6 ∂disorderLaw := by
          rw [integral_add (integrable_const _) hN.1, integral_const]
          simp [Measure.real, measure_univ]
        _ ≤ MA := by
          dsimp [MA]
          linarith [hN.2, le_max_left CA 0]
    exact ⟨hInt, hbound⟩
  have hB2 : ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω => B N ω ^ 2) disorderLaw ∧
        ∫ ω, B N ω ^ 2 ∂disorderLaw ≤ MB := by
    filter_upwards [hB6] with N hN
    have hInt := integrable_slabAdjacent_pairing_sq_of_integrable_sixth (B N) hN.1 (hBmeas N)
    have hmajor : Integrable (fun ω => 1 + |B N ω| ^ 6) disorderLaw :=
      (integrable_const (1 : ℝ)).add hN.1
    have hpoint (ω : Disorder) : B N ω ^ 2 ≤ 1 + |B N ω| ^ 6 := by
      have h := hBnonneg N ω
      by_cases hle : B N ω ≤ 1
      · have hpow : (B N ω) ^ 2 ≤ 1 := pow_le_one₀ h hle
        exact hpow.trans (le_add_of_nonneg_right (by positivity))
      · have hge : 1 ≤ B N ω := le_of_not_ge hle
        have hpow : (B N ω) ^ 2 ≤ (B N ω) ^ 6 := by
          calc
            (B N ω) ^ 2 ≤ (B N ω) ^ 2 * (B N ω) ^ 4 :=
              le_mul_of_one_le_right (sq_nonneg _) (one_le_pow₀ hge)
            _ = (B N ω) ^ 6 := by ring
        rw [abs_of_nonneg h]
        exact hpow.trans (le_add_of_nonneg_left (by positivity))
    have hbound : ∫ ω, B N ω ^ 2 ∂disorderLaw ≤ MB := by
      calc
        ∫ ω, B N ω ^ 2 ∂disorderLaw ≤ ∫ ω, 1 + |B N ω| ^ 6 ∂disorderLaw :=
          integral_mono hInt hmajor (fun ω => by
            simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hpoint ω)
        _ = 1 + ∫ ω, |B N ω| ^ 6 ∂disorderLaw := by
          rw [integral_add (integrable_const _) hN.1, integral_const]
          simp [Measure.real, measure_univ]
        _ ≤ MB := by
          dsimp [MB]
          linarith [hN.2, le_max_left CB 0]
    exact ⟨hInt, hbound⟩
  refine ⟨MA * MB, mul_pos hMA hMB, ?_⟩
  filter_upwards [hA2, hB2] with N hNA hNB
  have hprodInt := (hIndep N).integrable_mul hNA.1 hNB.1
  have hprodInt' : Integrable (fun ω =>
      (∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N s t ω) ^ 2 *
        (∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N t u ω) ^ 2) disorderLaw := by
    have hfun : (fun ω => A N ω ^ 2 * B N ω ^ 2) = fun ω =>
        (∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N s t ω) ^ 2 *
          (∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N t u ω) ^ 2 := by
      funext ω
      rw [hAeq N ω, hBeq N ω]
    exact hprodInt.congr (Eventually.of_forall fun ω => congrFun hfun ω)
  have hfactor := (hIndep N).integral_fun_mul_eq_mul_integral
    (hA2meas N).aestronglyMeasurable (hB2meas N).aestronglyMeasurable
  have hfactor' :
      ∫ ω, (∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N s t ω) ^ 2 *
        (∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N t u ω) ^ 2 ∂disorderLaw =
        (∫ ω, A N ω ^ 2 ∂disorderLaw) * (∫ ω, B N ω ^ 2 ∂disorderLaw) := by
    have hfun : (fun ω => A N ω ^ 2 * B N ω ^ 2) =
        fun ω => (∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N s t ω) ^ 2 *
          (∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N t u ω) ^ 2 := by
      funext ω
      rw [hAeq, hBeq]
    rw [← hfun]
    exact hfactor
  refine ⟨hprodInt', ?_⟩
  rw [hfactor']
  exact mul_le_mul hNA.2 hNB.2 (integral_nonneg fun ω => sq_nonneg _) hMA.le


/-- Annealed tensor moments on two touching polymer slabs factor and converge to the product
of their two-replica moment-kernel integrals.
Eventual integrability of the compact tensor products follows by domination using
`eventually_slabAdjacentTensorMass_sq_bound`. -/
theorem tendsto_slabAdjacentTensorMoment (ϑ : ℝ)
    (hPolymerMomentInput : PolymerMomentLimit ϑ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
    {s t u : ℝ} (hs : 0 ≤ s) (hst : s < t) (htu : t < u)
    (φ ψ : Fin 2 → C_c(Plane × Plane, ℝ)) :
    Tendsto
      (fun N => ∫ ω,
        slabPairingTensorFunctional φ (polymerRadonMeasure ϑ N s t ω) *
          slabPairingTensorFunctional ψ (polymerRadonMeasure ϑ N t u ω)
          ∂disorderLaw)
      atTop
      (nhds
        ((∫ x : Configuration 2, ∫ y : Configuration 2,
            (∏ i, φ i (x i, y i)) *
              (momentKernel 2 (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal) *
          (∫ x : Configuration 2, ∫ y : Configuration 2,
            (∏ i, ψ i (x i, y i)) *
              (momentKernel 2 (ϑ - Real.eulerMascheroniConstant) (u - t) x y).toReal))) := by
  let times : Fin 3 → ℝ := ![s, t, u]
  have htimes : StrictMono times := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [times]
    linarith
  have hAcont : Continuous (slabPairingTensorFunctional φ) := by
    change Continuous (fun μ =>
      RandomMeasure.vaguePairing μ (φ 0) * RandomMeasure.vaguePairing μ (φ 1))
    exact (RandomMeasure.continuous_vaguePairing (φ 0)).mul
      (RandomMeasure.continuous_vaguePairing (φ 1))
  have hBcont : Continuous (slabPairingTensorFunctional ψ) := by
    change Continuous (fun μ =>
      RandomMeasure.vaguePairing μ (ψ 0) * RandomMeasure.vaguePairing μ (ψ 1))
    exact (RandomMeasure.continuous_vaguePairing (ψ 0)).mul
      (RandomMeasure.continuous_vaguePairing (ψ 1))
  have hAmeas (N : ℕ) : Measurable
      (fun ω => slabPairingTensorFunctional φ (polymerRadonMeasure ϑ N s t ω)) :=
    hAcont.measurable.comp (measurable_polymerRadonMeasure ϑ N s t)
  have hBmeas (N : ℕ) : Measurable
      (fun ω => slabPairingTensorFunctional ψ (polymerRadonMeasure ϑ N t u ω)) :=
    hBcont.measurable.comp (measurable_polymerRadonMeasure ϑ N t u)
  have hBlocks (N : ℕ) :=
    iIndepFun_polymerRadonMeasure_consecutive ϑ N 2 times htimes
  have hIndep (N : ℕ) :
      (fun ω => slabPairingTensorFunctional φ (polymerRadonMeasure ϑ N s t ω)) ⟂ᵢ[disorderLaw]
        (fun ω => slabPairingTensorFunctional ψ (polymerRadonMeasure ϑ N t u ω)) := by
    have h := (hBlocks N).indepFun (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)
    have h' : (fun ω => polymerRadonMeasure ϑ N s t ω) ⟂ᵢ[disorderLaw]
        (fun ω => polymerRadonMeasure ϑ N t u ω) := by
      simpa [times] using h
    exact h'.comp hAcont.measurable hBcont.measurable
  let Fφ : C_c((Fin 2 → Plane × Plane), ℝ) := slabCompactPiTensorTest φ
  let Fψ : C_c((Fin 2 → Plane × Plane), ℝ) := slabCompactPiTensorTest ψ
  have hφPi := polymerMeasure_pi_moment_tendsto_of ϑ hPolymerMomentInput hFlatSixthMomentInput 2
    (by norm_num) (by norm_num) hs hst Fφ Fφ.continuous Fφ.hasCompactSupport
  have hψPi := polymerMeasure_pi_moment_tendsto_of ϑ hPolymerMomentInput hFlatSixthMomentInput 2
    (by norm_num) (by norm_num) (by linarith : 0 ≤ t) htu Fψ Fψ.continuous Fψ.hasCompactSupport
  have hφSource :
      (fun N => ∫ ω, slabPairingTensorFunctional φ
        (polymerRadonMeasure ϑ N s t ω) ∂disorderLaw) =
      (fun N => ∫ ω, ∫ q, Fφ q ∂
        (Measure.pi fun _ : Fin 2 => polymerMeasure ϑ N s t ω) ∂disorderLaw) := by
    funext N
    apply integral_congr_ae
    filter_upwards [] with ω
    have hSigma : SigmaFinite (polymerMeasure ϑ N s t ω) :=
      @MeasureTheory.sigmaFinite_of_locallyFinite (Plane × Plane) _
        (polymerMeasure ϑ N s t ω) inferInstance inferInstance
        (isLocallyFiniteMeasure_polymerMeasure ϑ N s t ω)
    have h := integral_slabCompactPiTensorTest
      (polymerMeasure ϑ N s t ω) hSigma φ
    have hpair : slabPairingTensorFunctional φ (polymerRadonMeasure ϑ N s t ω) =
        ∏ i, ∫ p, φ i p ∂polymerMeasure ϑ N s t ω := by
      simp [slabPairingTensorFunctional, RandomMeasure.vaguePairing, polymerRadonMeasure]
    have hinner : ∫ q, Fφ q ∂
        (Measure.pi fun _ : Fin 2 => polymerMeasure ϑ N s t ω) =
        ∏ i, ∫ p, φ i p ∂polymerMeasure ϑ N s t ω := by
      simpa only [Fφ, slabCompactPiTensorTest_apply] using h
    exact hpair.trans hinner.symm
  have hψSource :
      (fun N => ∫ ω, slabPairingTensorFunctional ψ
        (polymerRadonMeasure ϑ N t u ω) ∂disorderLaw) =
      (fun N => ∫ ω, ∫ q, Fψ q ∂
        (Measure.pi fun _ : Fin 2 => polymerMeasure ϑ N t u ω) ∂disorderLaw) := by
    funext N
    apply integral_congr_ae
    filter_upwards [] with ω
    have hSigma : SigmaFinite (polymerMeasure ϑ N t u ω) :=
      @MeasureTheory.sigmaFinite_of_locallyFinite (Plane × Plane) _
        (polymerMeasure ϑ N t u ω) inferInstance inferInstance
        (isLocallyFiniteMeasure_polymerMeasure ϑ N t u ω)
    have h := integral_slabCompactPiTensorTest
      (polymerMeasure ϑ N t u ω) hSigma ψ
    have hpair : slabPairingTensorFunctional ψ (polymerRadonMeasure ϑ N t u ω) =
        ∏ i, ∫ p, ψ i p ∂polymerMeasure ϑ N t u ω := by
      simp [slabPairingTensorFunctional, RandomMeasure.vaguePairing, polymerRadonMeasure]
    have hinner : ∫ q, Fψ q ∂
        (Measure.pi fun _ : Fin 2 => polymerMeasure ϑ N t u ω) =
        ∏ i, ∫ p, ψ i p ∂polymerMeasure ϑ N t u ω := by
      simpa only [Fψ, slabCompactPiTensorTest_apply] using h
    exact hpair.trans hinner.symm
  have hφLimit : Tendsto
      (fun N => ∫ ω, slabPairingTensorFunctional φ
        (polymerRadonMeasure ϑ N s t ω) ∂disorderLaw)
      atTop (nhds (∫ x : Configuration 2, ∫ y : Configuration 2,
        (∏ i, φ i (x i, y i)) *
          (momentKernel 2 (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal)) := by
    rw [hφSource]
    simpa only [Fφ, slabCompactPiTensorTest_apply] using hφPi
  have hψLimit : Tendsto
      (fun N => ∫ ω, slabPairingTensorFunctional ψ
        (polymerRadonMeasure ϑ N t u ω) ∂disorderLaw)
      atTop (nhds (∫ x : Configuration 2, ∫ y : Configuration 2,
        (∏ i, ψ i (x i, y i)) *
          (momentKernel 2 (ϑ - Real.eulerMascheroniConstant) (u - t) x y).toReal)) := by
    rw [hψSource]
    simpa only [Fψ, slabCompactPiTensorTest_apply] using hψPi
  have hfact (N : ℕ) :
      ∫ ω,
        slabPairingTensorFunctional φ (polymerRadonMeasure ϑ N s t ω) *
          slabPairingTensorFunctional ψ (polymerRadonMeasure ϑ N t u ω)
          ∂disorderLaw =
        (∫ ω, slabPairingTensorFunctional φ
          (polymerRadonMeasure ϑ N s t ω) ∂disorderLaw) *
        (∫ ω, slabPairingTensorFunctional ψ
          (polymerRadonMeasure ϑ N t u ω) ∂disorderLaw) := by
    exact (hIndep N).integral_fun_mul_eq_mul_integral
      (hAmeas N).aestronglyMeasurable (hBmeas N).aestronglyMeasurable
  have hfun :
      (fun N => ∫ ω,
        slabPairingTensorFunctional φ (polymerRadonMeasure ϑ N s t ω) *
          slabPairingTensorFunctional ψ (polymerRadonMeasure ϑ N t u ω)
          ∂disorderLaw) =
        (fun N => (∫ ω, slabPairingTensorFunctional φ
          (polymerRadonMeasure ϑ N s t ω) ∂disorderLaw) *
          (∫ ω, slabPairingTensorFunctional ψ
          (polymerRadonMeasure ϑ N t u ω) ∂disorderLaw)) := by
    funext N
    exact hfact N
  rw [hfun]
  exact hφLimit.mul hψLimit


/-- Touching four-replica tensor moments converge to the two-block kernel integral, with eventual integrability supplied by `eventually_slabAdjacentTensorMass_sq_bound`. -/
theorem tendsto_slabAdjacentTensorIntegral (ϑ : ℝ)
    (hPolymerMomentInput : PolymerMomentLimit ϑ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
    {s t u : ℝ} (hs : 0 ≤ s) (hst : s < t) (htu : t < u)
    (φ : Fin 4 → C_c(Plane × Plane, ℝ)) :
    Tendsto
      (fun N => ∫ ω, ∫ q, slabCompactPiTensorTest φ q ∂
        (slabTwoBlockPiMeasure (polymerMeasure ϑ N s t ω)
          (polymerMeasure ϑ N t u ω)) ∂disorderLaw)
      atTop
      (𝓝 (slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t)
        (slabCompactPiTensorTest φ))) := by
  let φ₁ : Fin 2 → C_c(Plane × Plane, ℝ) := fun i => φ (i.castAdd 2)
  let φ₂ : Fin 2 → C_c(Plane × Plane, ℝ) := fun i => φ (i.natAdd 2)
  have hsource (N : ℕ) :
      (∫ ω, ∫ q, slabCompactPiTensorTest φ q ∂
        (slabTwoBlockPiMeasure (polymerMeasure ϑ N s t ω)
          (polymerMeasure ϑ N t u ω)) ∂disorderLaw) =
      ∫ ω,
        slabPairingTensorFunctional φ₁ (polymerRadonMeasure ϑ N s t ω) *
          slabPairingTensorFunctional φ₂ (polymerRadonMeasure ϑ N t u ω)
          ∂disorderLaw := by
    apply integral_congr_ae
    filter_upwards [] with ω
    have hμ : SigmaFinite (polymerMeasure ϑ N s t ω) :=
      @MeasureTheory.sigmaFinite_of_locallyFinite (Plane × Plane) _
        (polymerMeasure ϑ N s t ω) inferInstance inferInstance
        (isLocallyFiniteMeasure_polymerMeasure ϑ N s t ω)
    have hν : SigmaFinite (polymerMeasure ϑ N t u ω) :=
      @MeasureTheory.sigmaFinite_of_locallyFinite (Plane × Plane) _
        (polymerMeasure ϑ N t u ω) inferInstance inferInstance
        (isLocallyFiniteMeasure_polymerMeasure ϑ N t u ω)
    have hprod := integral_slabCompactPiTensorTest_twoBlock hμ hν φ
    have hpair₁ : slabPairingTensorFunctional φ₁
        (polymerRadonMeasure ϑ N s t ω) =
        ∏ i : Fin 2, ∫ p, φ₁ i p ∂polymerMeasure ϑ N s t ω := by
      simp [slabPairingTensorFunctional, RandomMeasure.vaguePairing, polymerRadonMeasure]
    have hpair₂ : slabPairingTensorFunctional φ₂
        (polymerRadonMeasure ϑ N t u ω) =
        ∏ i : Fin 2, ∫ p, φ₂ i p ∂polymerMeasure ϑ N t u ω := by
      simp [slabPairingTensorFunctional, RandomMeasure.vaguePairing, polymerRadonMeasure]
    rw [hpair₁, hpair₂]
    simpa only [φ₁, φ₂] using hprod
  have htensor := tendsto_slabAdjacentTensorMoment ϑ hPolymerMomentInput hFlatSixthMomentInput hs hst htu φ₁ φ₂
  have htarget := integral_slabSeparatedMomentPiMeasure_tensor
    (ϑ - Real.eulerMascheroniConstant) (τ₁ := t - s) (τ₂ := u - t)
    (by linarith) (by linarith) φ
  rw [show (fun N => ∫ ω, ∫ q, slabCompactPiTensorTest φ q ∂
      (slabTwoBlockPiMeasure (polymerMeasure ϑ N s t ω)
        (polymerMeasure ϑ N t u ω)) ∂disorderLaw) =
      (fun N => ∫ ω,
        slabPairingTensorFunctional φ₁ (polymerRadonMeasure ϑ N s t ω) *
          slabPairingTensorFunctional φ₂ (polymerRadonMeasure ϑ N t u ω)
          ∂disorderLaw) from funext hsource]
  rw [htarget]
  exact htensor


private instance instThinSlabConfigurationBorel : BorelSpace (Configuration 2) := by
  infer_instance

private instance instThinSlabConfigurationPairBorel : BorelSpace (Configuration 2 × Configuration 2) := by
  infer_instance

private instance instThinSlabSeparatedArrayBorel :
    BorelSpace (Fin 2 → Configuration 2 × Configuration 2) := by
  infer_instance

private def adjacentCompactTestToBoundedContinuous {X : Type*} [TopologicalSpace X]
    (f : C_c(X, ℝ)) : X →ᵇ ℝ :=
  ofCompactSupport f f.continuous f.hasCompactSupport

private theorem measurable_integral_compact_test_for_adjacent_moments {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (f : C_c(X, ℝ)) :
    Measurable (fun μ : Measure X => ∫ x, f x ∂μ) := by
  let κ : Kernel (Measure X) X := ⟨id, measurable_id⟩
  exact (((map_continuous f).measurable).stronglyMeasurable.integral_kernel
    (κ := κ)).measurable

/-- Touching-block moment convergence extends to compact continuous four-replica tests, with an integrable majorant supplied by `eventually_slabAdjacentTensorMass_sq_bound`. -/
theorem tendsto_slabAdjacentCompactIntegral (ϑ : ℝ)
    (hPolymerMomentInput : PolymerMomentLimit ϑ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
    {s t u : ℝ} (hs : 0 ≤ s) (hst : s < t) (htu : t < u)
    (F : C_c((Fin 4 → Plane × Plane), ℝ)) :
    Tendsto
      (fun N => ∫ ω, ∫ q, F q ∂
        (slabTwoBlockPiMeasure (polymerMeasure ϑ N s t ω)
          (polymerMeasure ϑ N t u ω)) ∂disorderLaw)
      atTop
      (𝓝 (slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t) F)) := by
  classical
  obtain ⟨K₀, hK₀, htensor⟩ := exists_compactTensorProduct_uniform_approx (n := 4) (by norm_num) F
  let Ksrc : Set (Plane × Plane) := ⋃ i : Fin 4,
    (fun q : Fin 4 → Plane × Plane => q i) '' tsupport (F : (Fin 4 → Plane × Plane) → ℝ)
  have hKsrc : IsCompact Ksrc :=
    isCompact_iUnion fun i => F.hasCompactSupport.image (continuous_apply i)
  let K : Set (Plane × Plane) := Ksrc ∪ K₀
  have hK : IsCompact K := hKsrc.union hK₀
  let R : Set (Fin 4 → Plane × Plane) := Set.univ.pi fun _ => K
  have hR : IsCompact R := isCompact_univ_pi fun _ => hK
  have hFsupport : tsupport (F : (Fin 4 → Plane × Plane) → ℝ) ⊆ R := by
    intro q hq
    apply Set.mem_univ_pi.mpr
    intro i
    apply Set.mem_union_left K₀
    exact Set.mem_iUnion.mpr ⟨i, ⟨q, hq, rfl⟩⟩
  obtain ⟨g, g', hg, hg', hone⟩ := exists_compactTensor_majorant K hK
  let ρ : C_c(Plane × Plane, ℝ) := compactTensorTest g g'
  have hρnonneg (p : Plane × Plane) : 0 ≤ ρ p := by
    simp only [ρ, compactTensorTest_apply]
    exact mul_nonneg (hg _) (hg' _)
  have hρone (p : Plane × Plane) (hp : p ∈ K) : ρ p = 1 := hone p hp
  let Tψ : C_c((Fin 4 → Plane × Plane), ℝ) := slabCompactPiTensorTest (fun _ => ρ)
  have hTψnonneg (q : Fin 4 → Plane × Plane) : 0 ≤ Tψ q := by
    simp only [Tψ, slabCompactPiTensorTest_apply]
    exact Finset.prod_nonneg fun i hi => hρnonneg (q i)
  have hTψone (q : Fin 4 → Plane × Plane) (hq : q ∈ R) : Tψ q = 1 := by
    simp only [Tψ, slabCompactPiTensorTest_apply]
    apply Finset.prod_eq_one
    intro i hi
    exact hρone (q i) ((Set.mem_univ_pi.mp hq) i)
  let πN : ℕ → Disorder → Measure (Fin 4 → Plane × Plane) := fun N ω =>
    Measure.pi fun i : Fin 4 =>
      if i.val < 2 then polymerMeasure ϑ N s t ω else polymerMeasure ϑ N t u ω
  have hπMeas (N : ℕ) : Measurable (πN N) := by
    exact measurable_piMeasure_of_locallyFinite 4
      (fun i ω => if i.val < 2 then polymerMeasure ϑ N s t ω else polymerMeasure ϑ N t u ω)
      (by intro i; split_ifs <;> exact measurable_polymerMeasure ϑ N _ _)
      (by intro i ω; split_ifs <;> exact isLocallyFiniteMeasure_polymerMeasure ϑ N _ _ ω)
  have hπSigma (N : ℕ) (ω : Disorder) :
      SigmaFinite (polymerMeasure ϑ N s t ω) ∧ SigmaFinite (polymerMeasure ϑ N t u ω) := by
    exact ⟨@MeasureTheory.sigmaFinite_of_locallyFinite (Plane × Plane) _
      (polymerMeasure ϑ N s t ω) inferInstance inferInstance
      (isLocallyFiniteMeasure_polymerMeasure ϑ N s t ω),
      @MeasureTheory.sigmaFinite_of_locallyFinite (Plane × Plane) _
      (polymerMeasure ϑ N t u ω) inferInstance inferInstance
      (isLocallyFiniteMeasure_polymerMeasure ϑ N t u ω)⟩
  have hLFπ (N : ℕ) (ω : Disorder) : IsLocallyFiniteMeasure (πN N ω) := by
    obtain ⟨hσμ, hσν⟩ := hπSigma N ω
    exact @MeasureTheory.Measure.pi.isLocallyFiniteMeasure
      (Fin 4) (fun _ => Plane × Plane) inferInstance (fun _ => inferInstance)
      (fun i => if i.val < 2 then polymerMeasure ϑ N s t ω else polymerMeasure ϑ N t u ω)
      (by intro i; split_ifs <;> assumption)
      (fun _ => inferInstance)
      (by intro i; split_ifs <;> exact isLocallyFiniteMeasure_polymerMeasure ϑ N _ _ ω)
  have hImeas (H : C_c((Fin 4 → Plane × Plane), ℝ)) (N : ℕ) :
      Measurable (fun ω => ∫ q, H q ∂πN N ω) :=
    (measurable_integral_compact_test_for_adjacent_moments H).comp (hπMeas N)
  let IF : ℕ → Disorder → ℝ := fun N ω => ∫ q, F q ∂πN N ω
  let J₁ : ℕ → Disorder → ℝ := fun N ω =>
    ∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N s t ω
  let J₂ : ℕ → Disorder → ℝ := fun N ω =>
    ∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N t u ω
  let M : ℕ → Disorder → ℝ := fun N ω => (J₁ N ω) ^ 2 * (J₂ N ω) ^ 2
  have hMbound := eventually_slabAdjacentTensorMass_sq_bound ϑ hFlatSixthMomentInput hs hst htu
    g g' hg hg'
  obtain ⟨C, hC, hM⟩ := hMbound
  have hTψint (N : ℕ) (ω : Disorder) : Integrable (fun q => Tψ q) (πN N ω) :=
    integrable_compactTest_of_locallyFinite _ (hLFπ N ω) Tψ
  have hTψmass (N : ℕ) (ω : Disorder) :
      ∫ q, Tψ q ∂πN N ω = M N ω := by
    obtain ⟨hμ, hν⟩ := hπSigma N ω
    have h := integral_slabCompactPiTensorTest_twoBlock hμ hν (fun _ => ρ)
    have hρint₁ : ∫ p, ρ p ∂polymerMeasure ϑ N s t ω = J₁ N ω := by
      simp [ρ, J₁, compactTensorTest_apply]
    have hρint₂ : ∫ p, ρ p ∂polymerMeasure ϑ N t u ω = J₂ N ω := by
      simp [ρ, J₂, compactTensorTest_apply]
    calc
      _ = (∏ i : Fin 2, ∫ p, ρ p ∂polymerMeasure ϑ N s t ω) *
          ∏ i : Fin 2, ∫ p, ρ p ∂polymerMeasure ϑ N t u ω := by
        simpa only [Tψ, πN, slabTwoBlockPiMeasure] using h
      _ = M N ω := by simp [M, hρint₁, hρint₂]
  have hCompactIntegralBound (H : C_c((Fin 4 → Plane × Plane), ℝ))
      (hHs : tsupport (H : (Fin 4 → Plane × Plane) → ℝ) ⊆ R)
      (q : Fin 4 → Plane × Plane) :
      ‖H q‖ ≤ ‖adjacentCompactTestToBoundedContinuous H‖ * Tψ q := by
    by_cases hq : q ∈ R
    · rw [hTψone q hq, mul_one]
      exact (adjacentCompactTestToBoundedContinuous H).norm_coe_le_norm q
    · have hzero : H q = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        exact fun hsupp => hq (hHs hsupp)
      rw [hzero, norm_zero]
      exact mul_nonneg (norm_nonneg _) (hTψnonneg q)
  have hIntegralBound (H : C_c((Fin 4 → Plane × Plane), ℝ))
      (hHs : tsupport (H : (Fin 4 → Plane × Plane) → ℝ) ⊆ R)
      (N : ℕ) (ω : Disorder) :
      ‖∫ q, H q ∂πN N ω‖ ≤ ‖adjacentCompactTestToBoundedContinuous H‖ * M N ω := by
    have hnorm := norm_integral_le_of_norm_le
      ((hTψint N ω).const_mul ‖adjacentCompactTestToBoundedContinuous H‖)
      (Filter.Eventually.of_forall (hCompactIntegralBound H hHs))
    rw [integral_const_mul, hTψmass] at hnorm
    exact hnorm
  have hIFint (N : ℕ) (hN : Integrable (M N) disorderLaw) : Integrable (IF N) disorderLaw := by
    have hdom : Integrable (fun ω => ‖adjacentCompactTestToBoundedContinuous F‖ * M N ω) disorderLaw :=
      hN.const_mul ‖adjacentCompactTestToBoundedContinuous F‖
    exact hdom.mono' ((hImeas F N).aestronglyMeasurable) (Filter.Eventually.of_forall fun ω => by
      simpa only [IF, Real.norm_eq_abs] using hIntegralBound F hFsupport N ω)
  let ν : Fin 2 → Measure (Configuration 2 × Configuration 2) := fun i =>
    if i.val = 0 then slabMomentKernelEndpointMeasure
      (ϑ - Real.eulerMascheroniConstant) (t - s)
    else slabMomentKernelEndpointMeasure (ϑ - Real.eulerMascheroniConstant) (u - t)
  have hνloc (i : Fin 2) : IsLocallyFiniteMeasure (ν i) := by
    dsimp [ν, slabMomentKernelEndpointMeasure]
    split_ifs <;> apply locallyFinite_momentKernelMeasure <;> linarith
  have hνsigma (i : Fin 2) : SigmaFinite (ν i) :=
    @MeasureTheory.sigmaFinite_of_locallyFinite (Configuration 2 × Configuration 2) _
      (ν i) inferInstance inferInstance (hνloc i)
  have htargetLF : IsLocallyFiniteMeasure
      (slabSeparatedMomentPiMeasure (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t)) := by
    dsimp [slabSeparatedMomentPiMeasure]
    change IsLocallyFiniteMeasure (Measure.pi ν)
    exact @MeasureTheory.Measure.pi.isLocallyFiniteMeasure
      (Fin 2) (fun _ => Configuration 2 × Configuration 2) inferInstance (fun _ => inferInstance)
      ν hνsigma (fun _ => inferInstance) hνloc
  have htargetInt (H : C_c((Fin 4 → Plane × Plane), ℝ)) :
      Integrable (slabSeparatedGroupedTest H : (Fin 2 → Configuration 2 × Configuration 2) → ℝ)
        (slabSeparatedMomentPiMeasure (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t)) :=
    integrable_compactTest_of_locallyFinite _ htargetLF (slabSeparatedGroupedTest H)
  have htargetSub (H G : C_c((Fin 4 → Plane × Plane), ℝ)) :
      slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t) (H - G) =
        slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t) H -
          slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t) G := by
    unfold slabSeparatedMomentIntegral
    have hpoint (z : Fin 2 → Configuration 2 × Configuration 2) :
        slabSeparatedGroupedTest (H - G) z =
          slabSeparatedGroupedTest H z - slabSeparatedGroupedTest G z := by
      simp [slabSeparatedGroupedTest_apply]
    calc
      _ = ∫ z, (slabSeparatedGroupedTest H z - slabSeparatedGroupedTest G z)
            ∂slabSeparatedMomentPiMeasure (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hpoint
      _ = _ := integral_sub (htargetInt H) (htargetInt G)
  have htargetMassNonneg :
      0 ≤ slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t) Tψ := by
    apply integral_nonneg
    intro z
    change 0 ≤ Tψ (slabSeparatedArrayHomeomorph z)
    exact hTψnonneg _
  have hTψtargetInt := htargetInt Tψ
  have hTψtarget_nonneg := htargetMassNonneg
  have hδchoice : ∀ δ : ℝ, 0 < δ → ∃ m : ℕ, ∃ φ : Fin m → Fin 4 → C_c(Plane × Plane, ℝ),
      (∀ b i, tsupport (φ b i : Plane × Plane → ℝ) ⊆ K₀) ∧
      ∀ q, |(∑ b, ∏ i, φ b i (q i)) - F q| < δ := by
    intro δ hδ
    exact htensor δ hδ
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let M₁ : ℝ := 1 + slabSeparatedMomentIntegral
    (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t) Tψ
  let δ : ℝ := ε / (3 * (C + M₁))
  have hM₁pos : 0 < M₁ := by dsimp [M₁]; linarith [htargetMassNonneg]
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨m, φ, hφsupport, happrox⟩ := hδchoice δ hδ
  let T : Fin m → C_c((Fin 4 → Plane × Plane), ℝ) := fun b => slabCompactPiTensorTest (φ b)
  let G : C_c((Fin 4 → Plane × Plane), ℝ) := ∑ b, T b
  have hGapply (q : Fin 4 → Plane × Plane) : G q = ∑ b, ∏ i, φ b i (q i) := by
    simp [G, T, slabCompactPiTensorTest_apply]
  have hTsupport (b : Fin m) : tsupport (T b : (Fin 4 → Plane × Plane) → ℝ) ⊆ R := by
    apply closure_minimal
    · intro q hq
      apply Set.mem_univ_pi.mpr
      intro i
      by_contra hi
      have hzero : φ b i (q i) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hsupp => hi (Set.mem_union_right Ksrc
          (hφsupport b i hsupp)))
      change slabCompactPiTensorTest (φ b) q ≠ 0 at hq
      rw [slabCompactPiTensorTest_apply] at hq
      exact hq (Finset.prod_eq_zero (Finset.mem_univ i) hzero)
    · exact hR.isClosed
  have hGsupport : Function.support (G : (Fin 4 → Plane × Plane) → ℝ) ⊆ R := by
    intro q hq
    change G q ≠ 0 at hq
    apply Set.mem_univ_pi.mpr
    intro i
    by_contra hi
    have hφzero (b : Fin m) : φ b i (q i) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hsupp
      exact hi (Set.mem_union_right Ksrc (hφsupport b i hsupp))
    have hGzero : G q = 0 := by
      rw [hGapply]
      apply Finset.sum_eq_zero
      intro b hb
      exact Finset.prod_eq_zero (Finset.mem_univ i) (hφzero b)
    exact hq hGzero
  have hGtsupport : tsupport (G : (Fin 4 → Plane × Plane) → ℝ) ⊆ R :=
    closure_minimal hGsupport hR.isClosed
  have hGapprox (q : Fin 4 → Plane × Plane) : |G q - F q| ≤ δ := by
    rw [hGapply]
    exact (happrox q).le
  have hpointApprox (q : Fin 4 → Plane × Plane) :
      ‖G q - F q‖ ≤ δ * Tψ q := by
    by_cases hq : q ∈ R
    · rw [Real.norm_eq_abs, hTψone q hq, mul_one]
      exact hGapprox q
    · have hFzero : F q = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hsupp
        exact hq (hFsupport hsupp)
      have hGzero : G q = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hsupp
        exact hq (hGtsupport hsupp)
      rw [hFzero, hGzero]
      simp only [sub_self, norm_zero]
      exact mul_nonneg (le_of_lt hδ) (hTψnonneg q)
  have htargetApprox :
      |slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t) F -
        slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t) G| ≤
        δ * slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t) Tψ := by
    have hpoint (z : Fin 2 → Configuration 2 × Configuration 2) :
        ‖slabSeparatedGroupedTest (G - F) z‖ ≤ δ * slabSeparatedGroupedTest Tψ z := by
      let q := slabSeparatedArrayHomeomorph z
      have h := hpointApprox q
      simpa [slabSeparatedGroupedTest_apply, q, slabCompactPiTensorTest_apply] using h
    have hmajor : Integrable (fun z => δ * slabSeparatedGroupedTest Tψ z)
        (slabSeparatedMomentPiMeasure (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t)) :=
      htargetInt Tψ |>.const_mul δ
    have hnorm := norm_integral_le_of_norm_le hmajor
      (Filter.Eventually.of_forall hpoint)
    have hsub := htargetSub G F
    calc
      _ = |slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant)
          (t - s) (u - t) G -
          slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant)
            (t - s) (u - t) F| := abs_sub_comm _ _
      _ = ‖∫ z, slabSeparatedGroupedTest (G - F) z
            ∂slabSeparatedMomentPiMeasure (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t)‖ := by
        rw [Real.norm_eq_abs]
        change |slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant)
            (t - s) (u - t) G -
          slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant)
            (t - s) (u - t) F| =
          |slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant)
            (t - s) (u - t) (G - F)|
        rw [hsub]
      _ ≤ ∫ z, δ * slabSeparatedGroupedTest Tψ z
            ∂slabSeparatedMomentPiMeasure (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t) := hnorm
      _ = δ * slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant)
            (t - s) (u - t) Tψ := by
        change (∫ z, δ * slabSeparatedGroupedTest Tψ z
          ∂slabSeparatedMomentPiMeasure (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t)) =
          δ * (∫ z, slabSeparatedGroupedTest Tψ z
            ∂slabSeparatedMomentPiMeasure (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t))
        rw [integral_const_mul]
  have htargetApprox' :
      |slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t) F -
        slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t) G| ≤
        δ * M₁ := by
    calc
      _ ≤ δ * slabSeparatedMomentIntegral
            (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t) Tψ := htargetApprox
      _ ≤ δ * M₁ := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hδ)
        dsimp [M₁]
        linarith [htargetMassNonneg]
  have htargetSum :
      slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t) G =
        ∑ b : Fin m, slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant)
          (t - s) (u - t) (T b) := by
    unfold slabSeparatedMomentIntegral
    have hpoint (z : Fin 2 → Configuration 2 × Configuration 2) :
        slabSeparatedGroupedTest G z = ∑ b, slabSeparatedGroupedTest (T b) z := by
      simp [G, slabSeparatedGroupedTest_apply, CompactlySupportedContinuousMap.sum_apply]
    calc
      _ = ∫ z, (∑ b, slabSeparatedGroupedTest (T b) z)
            ∂slabSeparatedMomentPiMeasure (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hpoint
      _ = _ := by
        rw [integral_finsetSum]
        intro b hb
        exact htargetInt (T b)
  have hterm (b : Fin m) : Tendsto
      (fun N => ∫ ω, ∫ q, T b q ∂πN N ω ∂disorderLaw) atTop
      (𝓝 (slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t) (T b))) := by
    exact tendsto_slabAdjacentTensorIntegral ϑ hPolymerMomentInput hFlatSixthMomentInput hs hst htu (φ b)
  have hsumLimit : Tendsto
      (fun N => ∑ b : Fin m, ∫ ω, ∫ q, T b q ∂πN N ω ∂disorderLaw) atTop
      (𝓝 (∑ b : Fin m, slabSeparatedMomentIntegral
        (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t) (T b))) :=
    tendsto_finsetSum Finset.univ (fun b hb => hterm b)
  have hsumEvent : ∀ᶠ N : ℕ in atTop,
      (∫ ω, ∫ q, G q ∂πN N ω ∂disorderLaw) =
        ∑ b : Fin m, ∫ ω, ∫ q, T b q ∂πN N ω ∂disorderLaw := by
    filter_upwards [hM] with N hMN
    have htermInt (b : Fin m) : Integrable
        (fun ω => ∫ q, T b q ∂πN N ω) disorderLaw := by
      have hdom := hMN.1.const_mul ‖adjacentCompactTestToBoundedContinuous (T b)‖
      exact hdom.mono' ((hImeas (T b) N).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun ω => by
          simpa only [Real.norm_eq_abs] using hIntegralBound (T b) (hTsupport b) N ω)
    have hinner (ω : Disorder) :
        (∫ q, G q ∂πN N ω) = ∑ b : Fin m, ∫ q, T b q ∂πN N ω := by
      rw [show (fun q => G q) = fun q => ∑ b : Fin m, T b q from by
        funext q
        simp [G, CompactlySupportedContinuousMap.sum_apply]]
      rw [integral_finsetSum]
      intro b hb
      exact integrable_compactTest_of_locallyFinite _ (hLFπ N ω) (T b)
    calc
      _ = ∫ ω, ∑ b : Fin m, ∫ q, T b q ∂πN N ω ∂disorderLaw := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hinner
      _ = _ := integral_finsetSum _ (fun b hb => htermInt b)
  have hGint (N : ℕ) (hMN : Integrable (M N) disorderLaw) :
      Integrable (fun ω => ∫ q, G q ∂πN N ω) disorderLaw :=
    hMN.const_mul ‖adjacentCompactTestToBoundedContinuous G‖ |>.mono' ((hImeas G N).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => by
        simpa only [Real.norm_eq_abs] using hIntegralBound G hGtsupport N ω)
  have hcloseFinite : ∀ᶠ N : ℕ in atTop,
      |(∫ ω, IF N ω ∂disorderLaw) - ∫ ω, ∫ q, G q ∂πN N ω ∂disorderLaw| ≤
        δ * C := by
    filter_upwards [hM] with N hMN
    have hGintN := hGint N hMN.1
    have hpoint (ω : Disorder) : ‖IF N ω - ∫ q, G q ∂πN N ω‖ ≤ δ * M N ω := by
      have hμloc : IsLocallyFiniteMeasure (polymerMeasure ϑ N s t ω) :=
        isLocallyFiniteMeasure_polymerMeasure ϑ N s t ω
      have hνloc : IsLocallyFiniteMeasure (polymerMeasure ϑ N t u ω) :=
        isLocallyFiniteMeasure_polymerMeasure ϑ N t u ω
      have hcompact := @abs_integral_sub_le_slabSeparatedCompactMass
        (polymerMeasure ϑ N s t ω) (polymerMeasure ϑ N t u ω)
        hμloc hνloc K g g' hg hg' hone F G hFsupport hGtsupport δ (le_of_lt hδ)
        (fun q => by simpa only [abs_sub_comm] using hGapprox q)
      simpa [IF, πN, slabTwoBlockPiMeasure, M, J₁, J₂, ρ,
        compactTensorTest_apply, mul_assoc] using hcompact
    have hnorm := norm_integral_le_of_norm_le (hMN.1.const_mul δ)
      (Filter.Eventually.of_forall hpoint)
    have hsub := integral_sub (hIFint N hMN.1) hGintN
    calc
      _ = ‖∫ ω, (IF N ω - ∫ q, G q ∂πN N ω) ∂disorderLaw‖ := by
        rw [hsub, Real.norm_eq_abs]
      _ ≤ ∫ ω, δ * M N ω ∂disorderLaw := hnorm
      _ = δ * ∫ ω, M N ω ∂disorderLaw := integral_const_mul _ _
      _ ≤ δ * C := mul_le_mul_of_nonneg_left hMN.2 (le_of_lt hδ)
  have hmid : Tendsto
      (fun N => ∫ ω, ∫ q, G q ∂πN N ω ∂disorderLaw) atTop
      (𝓝 (slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant)
        (t - s) (u - t) G)) := by
    have hsumEvent' := hsumEvent.mono fun N hN => hN.symm
    have hsum' := hsumLimit.congr' hsumEvent'
    simpa only [htargetSum] using hsum'
  have hcloseMiddle : ∀ᶠ N : ℕ in atTop,
      |(∫ ω, ∫ q, G q ∂πN N ω ∂disorderLaw) -
        slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t) G| < ε / 3 :=
    hmid.eventually (Metric.ball_mem_nhds _ (by positivity))
  have hratioC : C / (C + M₁) ≤ 1 := by
    rw [div_le_iff₀ (by positivity : 0 < C + M₁)]
    simpa only [one_mul] using le_add_of_nonneg_right (le_of_lt hM₁pos)
  have hratioM : M₁ / (C + M₁) ≤ 1 := by
    rw [div_le_iff₀ (by positivity : 0 < C + M₁)]
    simpa only [one_mul] using le_add_of_nonneg_left hC.le
  have hfirst : δ * C ≤ ε / 3 := by
    calc
      δ * C = (ε / 3) * (C / (C + M₁)) := by dsimp [δ]; field_simp
      _ ≤ ε / 3 := by
        have h := mul_le_mul_of_nonneg_left hratioC (by positivity : 0 ≤ ε / 3)
        simpa only [mul_one] using h
  have hlast : δ * M₁ ≤ ε / 3 := by
    calc
      δ * M₁ = (ε / 3) * (M₁ / (C + M₁)) := by dsimp [δ]; field_simp
      _ ≤ ε / 3 := by
        have h := mul_le_mul_of_nonneg_left hratioM (by positivity : 0 ≤ ε / 3)
        simpa only [mul_one] using h
  have hevent : ∀ᶠ N : ℕ in atTop,
      dist (∫ ω, IF N ω ∂disorderLaw)
        (slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t) F) < ε := by
    filter_upwards [hcloseFinite, hcloseMiddle] with N hN₁ hN₂
    rw [Real.dist_eq]
    have htri :
        |(∫ ω, IF N ω ∂disorderLaw) -
          slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t) F| ≤
          |(∫ ω, IF N ω ∂disorderLaw) - ∫ ω, ∫ q, G q ∂πN N ω ∂disorderLaw| +
          |(∫ ω, ∫ q, G q ∂πN N ω ∂disorderLaw) -
            slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t) G| +
          |slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t) G -
            slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t) F| := by
      calc
        _ ≤ |(∫ ω, IF N ω ∂disorderLaw) -
            slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t) G| +
            |slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t) G -
              slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t) F| :=
          abs_sub_le _ _ _
        _ ≤ (|(∫ ω, IF N ω ∂disorderLaw) - ∫ ω, ∫ q, G q ∂πN N ω ∂disorderLaw| +
            |(∫ ω, ∫ q, G q ∂πN N ω ∂disorderLaw) -
              slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t) G|) +
            |slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t) G -
              slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t) F| := by
          exact add_le_add_left (abs_sub_le _ _ _) _
        _ = _ := by ring
    have hfinal :
        |(∫ ω, IF N ω ∂disorderLaw) -
          slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t) F| < ε := by
      have htargetApproxRev :
          |slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t) G -
            slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - t) F| ≤ δ * M₁ := by
        simpa only [abs_sub_comm] using htargetApprox'
      apply lt_of_le_of_lt htri
      linarith [hN₁, hN₂, htargetApproxRev, hfirst, hlast]
    exact hfinal
  exact eventually_atTop.mp hevent


end Critical2DKPZ.SHF.Flow

end
