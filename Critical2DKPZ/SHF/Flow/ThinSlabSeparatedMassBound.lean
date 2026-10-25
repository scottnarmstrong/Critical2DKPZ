/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.ThinSlabSeparatedTensorMoment
public import Critical2DKPZ.SHF.Flow.SubseqDenseMoments
public import Critical2DKPZ.SHF.Flow.SlabProductsCore

/-! # Uniform compact-mass bounds on separated slabs -/

@[expose] public noncomputable section

open MeasureTheory Filter ProbabilityTheory
open Critical2DKPZ.SHF.Limit
open Critical2DKPZ.SHF.Tsai
open scoped CompactlySupported

namespace Critical2DKPZ.SHF.Flow

private theorem integrable_pairing_sq_of_integrable_sixth
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

/-- The product of squared compact tensor masses on two disjoint polymer slabs is eventually
integrable and uniformly bounded. The sixth-moment input supplies the required second moments,
and disorder-block independence factors their product. -/
theorem eventually_slabSeparatedTensorMass_sq_bound (ϑ : ℝ)
    (hFlatSixthMomentInput : FlatSixthMomentBound ϑ) {s t r u : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (htr : t < r) (hru : r < u)
    (g g' : C_c(Plane, ℝ)) (hg : ∀ x, 0 ≤ g x) (hg' : ∀ x, 0 ≤ g' x) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω =>
        (∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N s t ω) ^ 2 *
        (∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N r u ω) ^ 2) disorderLaw ∧
      ∫ ω,
        (∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N s t ω) ^ 2 *
        (∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N r u ω) ^ 2
        ∂disorderLaw ≤ C := by
  classical
  let ψ : C_c(Plane × Plane, ℝ) := compactTensorTest g g'
  let A : ℕ → Disorder → ℝ := fun N ω => ∫ p, ψ p ∂polymerMeasure ϑ N s t ω
  let B : ℕ → Disorder → ℝ := fun N ω => ∫ p, ψ p ∂polymerMeasure ϑ N r u ω
  have hAeq (N : ℕ) (ω : Disorder) : A N ω =
      ∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N s t ω := by
    simp [A, ψ, compactTensorTest_apply]
  have hBeq (N : ℕ) (ω : Disorder) : B N ω =
      ∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N r u ω := by
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
    1 (by norm_num) (by norm_num) (by linarith) hru (fun _ : Fin 1 => g) (fun _ => g')
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
        |∏ i : Fin 1, ∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N r u ω| ^
          ((6 : ℝ) / ((1 : ℕ) : ℝ)) = |B N ω| ^ 6 := by
      have hbase : (∏ i : Fin 1,
          ∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N r u ω) = B N ω := by
        simp [hBeq]
      rw [hbase]
      norm_num [Real.rpow_natCast]
    refine ⟨hN.1.congr (Eventually.of_forall fun ω => heq ω), ?_⟩
    have hIntEq : ∫ ω, |B N ω| ^ 6 ∂disorderLaw =
        ∫ ω, |∏ i : Fin 1,
          ∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N r u ω| ^
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
    exact measurable_polymerPairing ϑ N r u ψ
  have hA2meas (N : ℕ) : Measurable (fun ω => A N ω ^ 2) :=
    (continuous_id.pow 2).measurable.comp (hAmeas N)
  have hB2meas (N : ℕ) : Measurable (fun ω => B N ω ^ 2) :=
    (continuous_id.pow 2).measurable.comp (hBmeas N)
  let times : Fin 4 → ℝ := ![s, t, r, u]
  have htimes : StrictMono times := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [times] <;> linarith
  have hBlocks (N : ℕ) := iIndepFun_polymerRadonMeasure_consecutive ϑ N 3 times htimes
  have hAcont : Continuous (fun μ : RandomMeasure.PlanePairRadonMeasure =>
      RandomMeasure.vaguePairing μ ψ) := RandomMeasure.continuous_vaguePairing ψ
  have hAeqRadon (N : ℕ) (ω : Disorder) :
      A N ω = RandomMeasure.vaguePairing (polymerRadonMeasure ϑ N s t ω) ψ := by
    simp [A, RandomMeasure.vaguePairing, polymerRadonMeasure]
  have hBeqRadon (N : ℕ) (ω : Disorder) :
      B N ω = RandomMeasure.vaguePairing (polymerRadonMeasure ϑ N r u ω) ψ := by
    simp [B, RandomMeasure.vaguePairing, polymerRadonMeasure]
  have hIndep (N : ℕ) :
      (fun ω => A N ω ^ 2) ⟂ᵢ[disorderLaw] (fun ω => B N ω ^ 2) := by
    have h := (hBlocks N).indepFun (i := (0 : Fin 3)) (j := (2 : Fin 3)) (by decide)
    have h' : (fun ω => polymerRadonMeasure ϑ N s t ω) ⟂ᵢ[disorderLaw]
        (fun ω => polymerRadonMeasure ϑ N r u ω) := by
      simpa [times] using h
    have h'' := h'.comp hAcont.measurable hAcont.measurable
    have hPow := h''.comp (continuous_id.pow 2).measurable (continuous_id.pow 2).measurable
    have hEqPow : (fun ω => A N ω ^ 2) = fun ω =>
        (RandomMeasure.vaguePairing (polymerRadonMeasure ϑ N s t ω) ψ) ^ 2 := by
      funext ω
      rw [hAeqRadon]
    have hEqPow' : (fun ω => B N ω ^ 2) = fun ω =>
        (RandomMeasure.vaguePairing (polymerRadonMeasure ϑ N r u ω) ψ) ^ 2 := by
      funext ω
      rw [hBeqRadon]
    have hPow' : (fun ω =>
        (RandomMeasure.vaguePairing (polymerRadonMeasure ϑ N s t ω) ψ) ^ 2) ⟂ᵢ[disorderLaw]
        (fun ω =>
          (RandomMeasure.vaguePairing (polymerRadonMeasure ϑ N r u ω) ψ) ^ 2) := by
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
    have hInt := integrable_pairing_sq_of_integrable_sixth (A N) hN.1 (hAmeas N)
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
    have hInt := integrable_pairing_sq_of_integrable_sixth (B N) hN.1 (hBmeas N)
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
        (∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N r u ω) ^ 2) disorderLaw := by
    have hfun : (fun ω => A N ω ^ 2 * B N ω ^ 2) = fun ω =>
        (∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N s t ω) ^ 2 *
          (∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N r u ω) ^ 2 := by
      funext ω
      rw [hAeq N ω, hBeq N ω]
    exact hprodInt.congr (Eventually.of_forall fun ω => congrFun hfun ω)
  have hfactor := (hIndep N).integral_fun_mul_eq_mul_integral
    (hA2meas N).aestronglyMeasurable (hB2meas N).aestronglyMeasurable
  have hfactor' :
      ∫ ω, (∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N s t ω) ^ 2 *
        (∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N r u ω) ^ 2 ∂disorderLaw =
        (∫ ω, A N ω ^ 2 ∂disorderLaw) * (∫ ω, B N ω ^ 2 ∂disorderLaw) := by
    have hfun : (fun ω => A N ω ^ 2 * B N ω ^ 2) =
        fun ω => (∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N s t ω) ^ 2 *
          (∫ p, g p.1 * g' p.2 ∂polymerMeasure ϑ N r u ω) ^ 2 := by
      funext ω
      rw [hAeq, hBeq]
    rw [← hfun]
    exact hfactor
  refine ⟨hprodInt', ?_⟩
  rw [hfactor']
  exact mul_le_mul hNA.2 hNB.2 (integral_nonneg fun ω => sq_nonneg _) hMA.le

end Critical2DKPZ.SHF.Flow

end
