/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.SubseqDenseProductLimit
public import Critical2DKPZ.SHF.Flow.SubseqDenseMollifier
public import Critical2DKPZ.SHF.Flow.SubseqDenseProducts
import Critical2DKPZ.SHF.Flow.SlabSmoothedFinite
import Critical2DKPZ.SHF.Flow.SmoothedProductCutoffTail
import Mathlib.Tactic

/-! # Dense-flow properties of subsequential limits -/

@[expose] public section

open MeasureTheory Filter
open scoped CompactlySupported Topology ENNReal

namespace Critical2DKPZ.SHF.Flow

open Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Tsai

/-- Cutoff-tail control and a uniform sixth-moment bound give a uniform second-moment bound for limiting cutoff products, with finite-scale integrability supplied by `eventually_polymerSubseq_cutoffProduct_sq_bound`. -/
theorem polymerSubseqLimit_cutoffProduct_sq_bound_of
    (ϑ : ℝ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ) (hProductCutoffTailInput : SmoothedProductCutoffTail ϑ)
    (D : Set ℝ) (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsPolymerSubseqLimit ϑ D ψ P Z)
    {s₀ s₁ s₂ : ℝ} (hs₀D : s₀ ∈ D) (hs₁D : s₁ ∈ D) (hs₂D : s₂ ∈ D)
    (hs₀ : 0 ≤ s₀) (hs₀₁ : s₀ < s₁) (hs₁₂ : s₁ < s₂)
    (Φ : C_c(Plane × Plane, ℝ)) (hΦ : ∀ p, 0 ≤ Φ p)
    (k : Plane → ℝ) (hk : Continuous k) (hkc : HasCompactSupport k)
    (hk0 : ∀ x, 0 ≤ k x) :
    ∃ R₀ B : ℝ, 0 ≤ B ∧ ∀ R ≥ R₀,
      AEMeasurable (fun ω => ∫ q, Φ (q.1.1, q.2.2) * k (q.1.2 - q.2.1) *
        ballCutoff R q.1.2 * ballCutoff R q.2.1 ∂((Z s₀ s₁ ω).prod (Z s₁ s₂ ω))) P ∧
      ∫⁻ ω, ENNReal.ofReal ((∫ q, Φ (q.1.1, q.2.2) * k (q.1.2 - q.2.1) *
        ballCutoff R q.1.2 * ballCutoff R q.2.1 ∂((Z s₀ s₁ ω).prod (Z s₁ s₂ ω))) ^ 2) ∂P ≤
        ENNReal.ofReal B := by
  classical
  let cutoffN (R : ℝ) (n : ℕ) (ω : Disorder) : ℝ :=
    ∫ q, Φ (q.1.1, q.2.2) * k (q.1.2 - q.2.1) *
      ballCutoff R q.1.2 * ballCutoff R q.2.1 ∂
        ((polymerMeasure ϑ (ψ n) s₀ s₁ ω).prod
          (polymerMeasure ϑ (ψ n) s₁ s₂ ω))
  let cutoffLim (R : ℝ) (ω : Ω) : ℝ :=
    ∫ q, Φ (q.1.1, q.2.2) * k (q.1.2 - q.2.1) *
      ballCutoff R q.1.2 * ballCutoff R q.2.1 ∂((Z s₀ s₁ ω).prod (Z s₁ s₂ ω))
  let fullN (n : ℕ) (ω : Disorder) : ℝ :=
    smoothedProductPairing (polymerMeasure ϑ (ψ n) s₀ s₁ ω) k
      (polymerMeasure ϑ (ψ n) s₁ s₂ ω) Φ
  have hkInput : ((Continuous k ∧ HasCompactSupport k ∧ ∀ x, 0 ≤ k x) ∨
      ∃ v : ℝ, 0 < v ∧ k = heatKernel v) := Or.inl ⟨hk, hkc, hk0⟩
  obtain ⟨R₀, htail⟩ := hProductCutoffTailInput hs₀ hs₀₁ hs₁₂ Φ k hkInput 1 (by norm_num)
  obtain ⟨C₀, hC₀⟩ := eventually_polymerSubseq_cutoffProduct_sq_bound
    ϑ hFlatSixthMomentInput D ψ hψ P Z hZ hs₀D hs₁D hs₂D hs₀ hs₀₁ hs₁₂ Φ hΦ k hk hk0 R₀
  have htail₀ : ∀ᶠ n : ℕ in atTop,
      ∫ ω, (fullN n ω - cutoffN R₀ n ω) ^ 2 ∂disorderLaw ≤ 1 := by
    have hN := htail R₀ le_rfl
    filter_upwards [hψ.tendsto_atTop.eventually hN] with n hn
    simpa [fullN, cutoffN] using hn
  have hfullStrong (n : ℕ) : AEStronglyMeasurable (fullN n) disorderLaw := by
    exact (measurable_smoothedProductPairing ϑ (ψ n) s₀ s₁ s₁ s₂ Φ k hk hkc).aestronglyMeasurable
  have hfullSq (n : ℕ) : Integrable (fun ω => fullN n ω ^ 2) disorderLaw := by
    exact (memLp_smoothedProductPairing_two ϑ (ψ n) s₀ s₁ s₁ s₂ Φ k hk hkc).integrable_sq
  have hdistCut (R : ℝ) : TendstoInDistribution
      (fun n (ω : Disorder) => (cutoffN R n ω,
        ∫ p, Φ p ∂polymerMeasure ϑ (ψ n) s₀ s₂ ω))
      atTop
      (fun ω => (cutoffLim R ω, ∫ p, Φ p ∂Z s₀ s₂ ω))
      (fun _ => disorderLaw) P :=
    polymerSubseqLimit_cutoffProduct_joint_tendstoInDistribution
      ϑ hFlatSixthMomentInput D ψ hψ P Z hZ hs₀D hs₁D hs₂D hs₀ hs₀₁ hs₁₂ Φ k hk R
  have hcutMeas (R : ℝ) (n : ℕ) : AEMeasurable (cutoffN R n) disorderLaw := by
    have h := measurable_fst.comp_aemeasurable ((hdistCut R).forall_aemeasurable n)
    exact h.congr (Filter.Eventually.of_forall fun ω => by simp [cutoffN])
  have hcutLimMeas (R : ℝ) : AEMeasurable (cutoffLim R) P := by
    have h := (hdistCut R).aemeasurable_limit
    exact (measurable_fst.comp_aemeasurable h).congr
      (Filter.Eventually.of_forall fun ω => by simp [cutoffLim])
  let Bfull : ℝ := 2 * (max C₀ 0 + 1)
  have hBfull : ∀ᶠ n : ℕ in atTop,
      Integrable (fun ω => fullN n ω ^ 2) disorderLaw ∧
        ∫ ω, fullN n ω ^ 2 ∂disorderLaw ≤ Bfull := by
    have hCevent := hC₀
    have hCmeas (n : ℕ) : AEStronglyMeasurable (cutoffN R₀ n) disorderLaw :=
      (hcutMeas R₀ n).aestronglyMeasurable
    have hdiffInt : ∀ᶠ n : ℕ in atTop,
        Integrable (fun ω => (fullN n ω - cutoffN R₀ n ω) ^ 2) disorderLaw := by
      filter_upwards [hCevent, htail₀] with n hn htailn
      have hnegSq : Integrable (fun ω => (-cutoffN R₀ n ω) ^ 2) disorderLaw := by
        simpa using hn.1
      have hsum := integrable_sq_add_le_two disorderLaw (hfullStrong n)
        (hCmeas n).neg (hfullSq n) hnegSq
      exact hsum.1.congr (Filter.Eventually.of_forall fun ω => by
        simp only [Pi.neg_apply]
        ring)
    have hfullBound : ∀ᶠ n : ℕ in atTop,
        ∫ ω, fullN n ω ^ 2 ∂disorderLaw ≤ 2 * (max C₀ 0 + 1) := by
      filter_upwards [hCevent, htail₀, hdiffInt] with n hn htailn hdiff
      have hsum := integrable_sq_add_le_two disorderLaw (hcutMeas R₀ n).aestronglyMeasurable
        ((hfullStrong n).sub (hcutMeas R₀ n).aestronglyMeasurable)
        hn.1 hdiff
      have hCbound : ∫ ω, cutoffN R₀ n ω ^ 2 ∂disorderLaw ≤ max C₀ 0 :=
        hn.2.trans (le_max_left _ _)
      calc
        ∫ ω, fullN n ω ^ 2 ∂disorderLaw =
            ∫ ω, (cutoffN R₀ n ω + (fullN n ω - cutoffN R₀ n ω)) ^ 2 ∂disorderLaw := by
          apply integral_congr_ae
          filter_upwards [] with ω
          ring
        _ ≤ 2 * ((∫ ω, cutoffN R₀ n ω ^ 2 ∂disorderLaw) +
            ∫ ω, (fullN n ω - cutoffN R₀ n ω) ^ 2 ∂disorderLaw) := hsum.2
        _ ≤ 2 * (max C₀ 0 + 1) := by gcongr
    filter_upwards [hfullBound] with n hn
    exact ⟨(hfullSq n), hn⟩
  have hfullLimitBound : 0 ≤ Bfull := by dsimp [Bfull]; positivity
  refine ⟨R₀, 2 * (Bfull + 1), by positivity, ?_⟩
  intro R hR
  have hCeventually := eventually_polymerSubseq_cutoffProduct_sq_bound
    ϑ hFlatSixthMomentInput D ψ hψ P Z hZ hs₀D hs₁D hs₂D hs₀ hs₀₁ hs₁₂ Φ hΦ k hk hk0 R
  obtain ⟨CR, hCR⟩ := hCeventually
  have htailR : ∀ᶠ n : ℕ in atTop,
      ∫ ω, (fullN n ω - cutoffN R n ω) ^ 2 ∂disorderLaw ≤ 1 := by
    have hN := htail R hR
    filter_upwards [hψ.tendsto_atTop.eventually hN] with n hn
    simpa [fullN, cutoffN] using hn
  have hdiffR : ∀ᶠ n : ℕ in atTop,
      Integrable (fun ω => (fullN n ω - cutoffN R n ω) ^ 2) disorderLaw := by
    filter_upwards [hCR, htailR] with n hn htailn
    have hnegSq : Integrable (fun ω => (-cutoffN R n ω) ^ 2) disorderLaw := by
      simpa using hn.1
    have hsum := integrable_sq_add_le_two disorderLaw (hfullStrong n)
      (hcutMeas R n).aestronglyMeasurable.neg (hfullSq n) hnegSq
    exact hsum.1.congr (Filter.Eventually.of_forall fun ω => by
      simp only [Pi.neg_apply]
      ring)
  have hcutBound : ∀ᶠ n : ℕ in atTop,
      ∫ ω, cutoffN R n ω ^ 2 ∂disorderLaw ≤ 2 * (Bfull + 1) := by
    filter_upwards [hCR, htailR, hdiffR, hBfull] with n hn htailn hdiff hfullbound
    have hrevDiff : Integrable (fun ω => (cutoffN R n ω - fullN n ω) ^ 2) disorderLaw := by
      exact hdiff.congr (Filter.Eventually.of_forall fun ω => by ring)
    have hsum := integrable_sq_add_le_two disorderLaw (hfullStrong n)
      ((hcutMeas R n).aestronglyMeasurable.sub (hfullStrong n)) (hfullSq n) hrevDiff
    have hbound := hsum.2
    have hfull := hfullbound.2
    have htailbound := htailn
    have htailrev :
        ∫ ω, (cutoffN R n ω - fullN n ω) ^ 2 ∂disorderLaw ≤ 1 := by
      calc
        ∫ ω, (cutoffN R n ω - fullN n ω) ^ 2 ∂disorderLaw =
            ∫ ω, (fullN n ω - cutoffN R n ω) ^ 2 ∂disorderLaw := by
          apply integral_congr_ae
          filter_upwards [] with ω
          ring
        _ ≤ 1 := htailn
    calc
      ∫ ω, cutoffN R n ω ^ 2 ∂disorderLaw =
          ∫ ω, (fullN n ω + (cutoffN R n ω - fullN n ω)) ^ 2 ∂disorderLaw := by
        apply integral_congr_ae
        filter_upwards [] with ω
        ring
      _ ≤ 2 * ((∫ ω, fullN n ω ^ 2 ∂disorderLaw) +
          ∫ ω, (cutoffN R n ω - fullN n ω) ^ 2 ∂disorderLaw) := hsum.2
      _ ≤ 2 * (Bfull + 1) := by nlinarith [hfull, htailrev]
  have hdistR : TendstoInDistribution (fun n ω => cutoffN R n ω) atTop
      (fun ω => cutoffLim R ω) (fun _ => disorderLaw) P := by
    have h := (hdistCut R).continuous_comp continuous_fst
    exact h.congr
      (fun n => Filter.Eventually.of_forall fun ω => rfl)
      (Filter.Eventually.of_forall fun ω => rfl)
  have hdistR0 : TendstoInDistribution (fun n ω => (cutoffN R n ω, (0 : ℝ))) atTop
      (fun ω => (cutoffLim R ω, (0 : ℝ))) (fun _ => disorderLaw) P := by
    have hcont : Continuous (fun p : ℝ × ℝ => (p.1, (0 : ℝ))) := by fun_prop
    have h := (hdistCut R).continuous_comp hcont
    exact TendstoInDistribution.congr
      (fun n => Filter.Eventually.of_forall fun ω => by simp)
      (Filter.Eventually.of_forall fun ω => by simp) h
  have hlimitSquare := lintegral_sq_sub_le_of_tendstoInDistribution
    (μ := fun _ => disorderLaw) (X := fun n ω => cutoffN R n ω)
    (Y := fun _ _ => (0 : ℝ)) (Xlim := fun ω => cutoffLim R ω)
    (Ylim := fun _ => (0 : ℝ))
    (C := 2 * (Bfull + 1)) hdistR0 (by
      filter_upwards [hcutBound, hCR] with n hn hcut
      refine ⟨?_, ?_⟩
      · simpa only [sub_zero] using hcut.1
      · simpa only [sub_zero] using hn)
  have hlimitBound :
      ∫⁻ ω, ENNReal.ofReal ((cutoffLim R ω) ^ 2) ∂P ≤
        ENNReal.ofReal (2 * (Bfull + 1)) := by
    simpa only [sub_zero] using hlimitSquare
  exact ⟨hcutLimMeas R, hlimitBound⟩

private theorem integrable_cutoffProduct_test
    (μ ν : Measure (Plane × Plane)) [IsLocallyFiniteMeasure μ]
    [IsLocallyFiniteMeasure ν] (Φ : C_c(Plane × Plane, ℝ))
    (k : Plane → ℝ) (hk : Continuous k) (R : ℝ) :
    Integrable (fun q : (Plane × Plane) × (Plane × Plane) =>
      Φ (q.1.1, q.2.2) * k (q.1.2 - q.2.1) *
        ballCutoff R q.1.2 * ballCutoff R q.2.1) (μ.prod ν) := by
  obtain ⟨K, hK, _, _, _, _, _, _, _, hsupport⟩ :=
    exists_cutoffProduct_compactTensor_approximation Φ k hk R
  let F : (Plane × Plane) × (Plane × Plane) → ℝ := fun q =>
    Φ (q.1.1, q.2.2) * k (q.1.2 - q.2.1) *
      ballCutoff R q.1.2 * ballCutoff R q.2.1
  have hFcont : Continuous F := by
    dsimp [F]
    have hEndpoint : Continuous
        (fun q : (Plane × Plane) × (Plane × Plane) => (q.1.1, q.2.2)) := by fun_prop
    have hMiddle : Continuous
        (fun q : (Plane × Plane) × (Plane × Plane) => q.1.2 - q.2.1) := by fun_prop
    exact (((Φ.continuous.comp hEndpoint).mul (hk.comp hMiddle)).mul
      ((continuous_ballCutoff R).comp (by fun_prop))).mul
        ((continuous_ballCutoff R).comp (by fun_prop))
  have hFcompact : HasCompactSupport F := by
    apply HasCompactSupport.of_support_subset_isCompact hK
    exact (subset_tsupport F).trans (by simpa [F] using hsupport)
  exact hFcont.integrable_of_hasCompactSupport hFcompact

/-- Uniform cutoff-tail control gives absolute integrability of nonnegative compact endpoint and connector tests against the limiting product measure. -/
theorem polymerSubseqLimit_nonnegProduct_integrable_of
    (ϑ : ℝ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ) (hProductCutoffTailInput : SmoothedProductCutoffTail ϑ)
    (D : Set ℝ) (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsPolymerSubseqLimit ϑ D ψ P Z)
    {s₀ s₁ s₂ : ℝ} (hs₀D : s₀ ∈ D) (hs₁D : s₁ ∈ D) (hs₂D : s₂ ∈ D)
    (hs₀ : 0 ≤ s₀) (hs₀₁ : s₀ < s₁) (hs₁₂ : s₁ < s₂)
    (Φ : C_c(Plane × Plane, ℝ)) (hΦ : ∀ p, 0 ≤ Φ p)
    (k : Plane → ℝ) (hk : Continuous k) (hkc : HasCompactSupport k)
    (hk0 : ∀ x, 0 ≤ k x) :
    ∀ᵐ ω ∂P,
      Integrable (fun q : (Plane × Plane) × (Plane × Plane) =>
        Φ (q.1.1, q.2.2) * k (q.1.2 - q.2.1))
        ((Z s₀ s₁ ω).prod (Z s₁ s₂ ω)) := by
  classical
  obtain ⟨R₀, B, hB0, hcutBound⟩ := polymerSubseqLimit_cutoffProduct_sq_bound_of
    ϑ hFlatSixthMomentInput hProductCutoffTailInput D ψ hψ P Z hZ hs₀D hs₁D hs₂D hs₀ hs₀₁ hs₁₂ Φ hΦ k hk hkc hk0
  let R (n : ℕ) : ℝ := R₀ + n
  let C (n : ℕ) (ω : Ω) : ℝ :=
    ∫ q, Φ (q.1.1, q.2.2) * k (q.1.2 - q.2.1) *
      ballCutoff (R n) q.1.2 * ballCutoff (R n) q.2.1 ∂
        ((Z s₀ s₁ ω).prod (Z s₁ s₂ ω))
  let M (ω : Ω) : ℝ≥0∞ := ⨆ n, ENNReal.ofReal (C n ω)
  let G (q : (Plane × Plane) × (Plane × Plane)) : ℝ :=
    Φ (q.1.1, q.2.2) * k (q.1.2 - q.2.1)
  let full (ω : Ω) : ℝ≥0∞ :=
    ∫⁻ q, ENNReal.ofReal (G q) ∂((Z s₀ s₁ ω).prod (Z s₁ s₂ ω))
  have hRmono : Monotone R := by
    intro i j hij
    dsimp [R]
    exact add_le_add_right (show (i : ℝ) ≤ j by exact_mod_cast hij) R₀
  have hRtop : Tendsto R atTop atTop := by
    simpa [R, add_comm] using tendsto_atTop_add_const_right _ R₀ tendsto_natCast_atTop_atTop
  have hCmeas (n : ℕ) : AEMeasurable (C n) P := by
    have hR := hcutBound (R n) (by dsimp [R]; linarith)
    exact hR.1.congr (Filter.Eventually.of_forall fun ω => by simp [C])
  have hCsq (n : ℕ) :
      ∫⁻ ω, ENNReal.ofReal ((C n ω) ^ 2) ∂P ≤ ENNReal.ofReal B := by
    have hR := hcutBound (R n) (by dsimp [R]; linarith)
    exact hR.2
  have hCmean (n : ℕ) :
      ∫⁻ ω, ENNReal.ofReal (C n ω) ∂P ≤ ENNReal.ofReal (1 + B) := by
    calc
      ∫⁻ ω, ENNReal.ofReal (C n ω) ∂P ≤
          ∫⁻ ω, (1 + ENNReal.ofReal ((C n ω) ^ 2)) ∂P := by
        apply lintegral_mono
        intro ω
        calc
          ENNReal.ofReal (C n ω) ≤ ENNReal.ofReal (1 + (C n ω) ^ 2) :=
            ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (C n ω - 1 / 2)])
          _ = 1 + ENNReal.ofReal ((C n ω) ^ 2) := by
            rw [ENNReal.ofReal_add (by norm_num) (sq_nonneg (C n ω)), ENNReal.ofReal_one]
      _ = 1 + ∫⁻ ω, ENNReal.ofReal ((C n ω) ^ 2) ∂P := by
        rw [lintegral_add_left' (by fun_prop)]
        simp
      _ ≤ 1 + ENNReal.ofReal B := add_le_add_right (hCsq n) 1
      _ = ENNReal.ofReal (1 + B) := by
        rw [ENNReal.ofReal_add (by norm_num) hB0, ENNReal.ofReal_one]
  have hCmono : ∀ᵐ ω ∂P, Monotone (fun n => ENNReal.ofReal (C n ω)) := by
    filter_upwards [(hZ.1 s₀ hs₀D s₁ hs₁D hs₀₁).2,
      (hZ.1 s₁ hs₁D s₂ hs₂D hs₁₂).2] with ω hω₀ hω₁
    intro i j hij
    apply ENNReal.ofReal_le_ofReal
    dsimp [C, R]
    exact @cutoffProduct_pairing_mono (Z s₀ s₁ ω) (Z s₁ s₂ ω) hω₀.1 hω₁.1
      Φ hΦ k hk hk0 (R i) (R j) (hRmono hij)
  have hMmeas : AEMeasurable M P := by
    apply AEMeasurable.iSup
    intro n
    exact ENNReal.measurable_ofReal.comp_aemeasurable (hCmeas n)
  have hMlin : ∫⁻ ω, M ω ∂P = ⨆ n, ∫⁻ ω, ENNReal.ofReal (C n ω) ∂P := by
    simpa [M] using lintegral_iSup' (μ := P)
      (fun n => ENNReal.measurable_ofReal.comp_aemeasurable (hCmeas n)) hCmono
  have hMbound : ∫⁻ ω, M ω ∂P ≤ ENNReal.ofReal (1 + B) := by
    rw [hMlin]
    exact iSup_le fun n => hCmean n
  have hMfinite : ∀ᵐ ω ∂P, M ω < ⊤ :=
    ae_lt_top' hMmeas (ne_of_lt (hMbound.trans_lt ENNReal.ofReal_lt_top))
  have hGcont : Continuous G := by
    dsimp [G]
    have hEndpoint : Continuous
        (fun q : (Plane × Plane) × (Plane × Plane) => (q.1.1, q.2.2)) := by fun_prop
    have hMiddle : Continuous
        (fun q : (Plane × Plane) × (Plane × Plane) => q.1.2 - q.2.1) := by fun_prop
    exact (Φ.continuous.comp hEndpoint).mul (hk.comp hMiddle)
  have hGnonneg (q : (Plane × Plane) × (Plane × Plane)) : 0 ≤ G q :=
    mul_nonneg (hΦ _) (hk0 _)
  have hMfull : M =ᵐ[P] full := by
    filter_upwards [hCmono, hZ.1 s₀ hs₀D s₁ hs₁D hs₀₁ |>.2,
      hZ.1 s₁ hs₁D s₂ hs₂D hs₁₂ |>.2] with ω hmono hμ hν
    let μ := Z s₀ s₁ ω
    let ν := Z s₁ s₂ ω
    have hcutEq (n : ℕ) : ENNReal.ofReal (C n ω) =
        ∫⁻ q, ENNReal.ofReal (G q * ballCutoff (R n) q.1.2 * ballCutoff (R n) q.2.1)
          ∂(μ.prod ν) := by
      let F : (Plane × Plane) × (Plane × Plane) → ℝ := fun q =>
        G q * ballCutoff (R n) q.1.2 * ballCutoff (R n) q.2.1
      have hFint : Integrable F (μ.prod ν) := by
        simpa [F, G] using
          @integrable_cutoffProduct_test μ ν hμ.1 hν.1 Φ k hk (R n)
      have hFnonneg : ∀ q, 0 ≤ F q := by
        intro q
        dsimp [F]
        exact mul_nonneg (mul_nonneg (hGnonneg q) (ballCutoff_mem_Icc (R n) _).1)
          (ballCutoff_mem_Icc (R n) _).1
      simpa [C, F, G, R, μ, ν] using
        ofReal_integral_eq_lintegral_ofReal hFint (Filter.Eventually.of_forall hFnonneg)
    have hspatial : Tendsto
        (fun n => ∫⁻ q, ENNReal.ofReal
          (G q * ballCutoff (R n) q.1.2 * ballCutoff (R n) q.2.1) ∂(μ.prod ν))
        atTop (𝓝 (full ω)) := by
      simpa [full, G, μ, ν] using
        @cutoffProduct_pairing_lintegral_tendsto μ ν hμ.1 hν.1 Φ hΦ k hk hk0 R hRmono hRtop
    have hcutTendsto : Tendsto (fun n => ENNReal.ofReal (C n ω)) atTop (𝓝 (full ω)) := by
      apply Tendsto.congr' (Filter.Eventually.of_forall fun n => (hcutEq n).symm)
      exact hspatial
    have hsupTendsto : Tendsto (fun n => ENNReal.ofReal (C n ω)) atTop
        (𝓝 (⨆ n, ENNReal.ofReal (C n ω))) := tendsto_atTop_iSup hmono
    exact tendsto_nhds_unique hsupTendsto hcutTendsto
  have hfullFinite : ∀ᵐ ω ∂P, full ω < ⊤ := by
    filter_upwards [hMfinite, hMfull] with ω hMtop hEq
    rw [← hEq]
    exact hMtop
  filter_upwards [hfullFinite] with ω hω
  refine ⟨hGcont.measurable.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hGnonneg)]
  exact hω

/-- Countable endpoint mass tests dominate every compact endpoint test, giving almost sure
absolute convergence of the smoothed product for a fixed compact connector. -/
theorem polymerSubseqLimit_smoothedProduct_wellDefined_of
    (ϑ : ℝ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ) (hProductCutoffTailInput : SmoothedProductCutoffTail ϑ)
    (D : Set ℝ) (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsPolymerSubseqLimit ϑ D ψ P Z)
    {s₀ s₁ s₂ : ℝ} (hs₀D : s₀ ∈ D) (hs₁D : s₁ ∈ D) (hs₂D : s₂ ∈ D)
    (hs₀ : 0 ≤ s₀) (hs₀₁ : s₀ < s₁) (hs₁₂ : s₁ < s₂)
    (w : Plane → ℝ) (hw : Continuous w) (hwc : HasCompactSupport w)
    (hw0 : ∀ x, 0 ≤ w x) :
    ∀ᵐ ω ∂P, SmoothedProductWellDefined (Z s₀ s₁ ω) w (Z s₁ s₂ ω) := by
  classical
  let E : CompactExhaustion Plane := RandomMeasure.vagueCompactExhaustion Plane
  have hForall (m n : ℕ) : ∀ᵐ ω ∂P,
      Integrable (fun q : (Plane × Plane) × (Plane × Plane) =>
        RandomMeasure.vagueMassTest E m q.1.1 *
          RandomMeasure.vagueMassTest E n q.2.2 * w (q.1.2 - q.2.1))
        ((Z s₀ s₁ ω).prod (Z s₁ s₂ ω)) := by
    have hΦ0 (p : Plane × Plane) :
        0 ≤ compactTensorTest (RandomMeasure.vagueMassTest E m)
          (RandomMeasure.vagueMassTest E n) p := by
      rw [compactTensorTest_apply]
      exact mul_nonneg ((RandomMeasure.vagueMassTest_spec E m).1 p.1)
        ((RandomMeasure.vagueMassTest_spec E n).1 p.2)
    simpa only [compactTensorTest_apply] using
      polymerSubseqLimit_nonnegProduct_integrable_of ϑ hFlatSixthMomentInput hProductCutoffTailInput D ψ hψ P Z hZ
        hs₀D hs₁D hs₂D hs₀ hs₀₁ hs₁₂
        (compactTensorTest (RandomMeasure.vagueMassTest E m)
          (RandomMeasure.vagueMassTest E n)) hΦ0 w hw hwc hw0
  have hForallM (m : ℕ) : ∀ᵐ ω ∂P, ∀ n : ℕ,
      Integrable (fun q : (Plane × Plane) × (Plane × Plane) =>
        RandomMeasure.vagueMassTest E m q.1.1 *
          RandomMeasure.vagueMassTest E n q.2.2 * w (q.1.2 - q.2.1))
        ((Z s₀ s₁ ω).prod (Z s₁ s₂ ω)) := by
    rw [ae_all_iff]
    intro n
    exact hForall m n
  have htests : ∀ᵐ ω ∂P, ∀ m n : ℕ,
      Integrable (fun q : (Plane × Plane) × (Plane × Plane) =>
        RandomMeasure.vagueMassTest E m q.1.1 *
          RandomMeasure.vagueMassTest E n q.2.2 * w (q.1.2 - q.2.1))
        ((Z s₀ s₁ ω).prod (Z s₁ s₂ ω)) := by
    rw [ae_all_iff]
    intro m
    exact hForallM m
  filter_upwards [htests] with ω htests
  intro f
  let K : Set (Plane × Plane) := tsupport (f : Plane × Plane → ℝ)
  have hK : IsCompact K := f.hasCompactSupport
  let A : Set Plane := Prod.fst '' K
  let B : Set Plane := Prod.snd '' K
  have hA : IsCompact A := hK.image continuous_fst
  have hB : IsCompact B := hK.image continuous_snd
  obtain ⟨m, hm⟩ := E.exists_superset_of_isCompact hA
  obtain ⟨n, hn⟩ := E.exists_superset_of_isCompact hB
  let χ : C_c(Plane, ℝ) := RandomMeasure.vagueMassTest E m
  let χ' : C_c(Plane, ℝ) := RandomMeasure.vagueMassTest E n
  let F : (Plane × Plane) × (Plane × Plane) → ℝ := fun q =>
    f (q.1.1, q.2.2) * w (q.1.2 - q.2.1)
  let H : (Plane × Plane) × (Plane × Plane) → ℝ := fun q =>
    χ q.1.1 * χ' q.2.2 * w (q.1.2 - q.2.1)
  have hFcont : Continuous F := by
    dsimp [F]
    exact (f.continuous.comp (by fun_prop)).mul (hw.comp (by fun_prop))
  have hHnonneg (q : (Plane × Plane) × (Plane × Plane)) : 0 ≤ H q := by
    dsimp [H]
    exact mul_nonneg (mul_nonneg ((RandomMeasure.vagueMassTest_spec E m).1 q.1.1)
      ((RandomMeasure.vagueMassTest_spec E n).1 q.2.2)) (hw0 _)
  have hHintegrable : Integrable H ((Z s₀ s₁ ω).prod (Z s₁ s₂ ω)) := by
    simpa [H, χ, χ'] using htests m n
  have hmajor : Integrable (fun q => ‖f.toBoundedContinuousFunction‖ * H q)
      ((Z s₀ s₁ ω).prod (Z s₁ s₂ ω)) :=
    hHintegrable.const_mul ‖f.toBoundedContinuousFunction‖
  have hbound (q : (Plane × Plane) × (Plane × Plane)) :
      ‖F q‖ ≤ ‖f.toBoundedContinuousFunction‖ * H q := by
    by_cases hfq : f (q.1.1, q.2.2) = 0
    · change ‖f (q.1.1, q.2.2) * w (q.1.2 - q.2.1)‖ ≤
        ‖f.toBoundedContinuousFunction‖ * H q
      rw [hfq, zero_mul, norm_zero]
      exact mul_nonneg (norm_nonneg _) (hHnonneg q)
    · have hq : (q.1.1, q.2.2) ∈ K :=
        subset_tsupport f (Function.mem_support.mpr hfq)
      have hχ : χ q.1.1 = 1 := by
        apply (RandomMeasure.vagueMassTest_spec E m).2.2.1
        exact hm ⟨(q.1.1, q.2.2), hq, rfl⟩
      have hχ' : χ' q.2.2 = 1 := by
        apply (RandomMeasure.vagueMassTest_spec E n).2.2.1
        exact hn ⟨(q.1.1, q.2.2), hq, rfl⟩
      have hwq : 0 ≤ w (q.1.2 - q.2.1) := hw0 _
      change ‖f (q.1.1, q.2.2) * w (q.1.2 - q.2.1)‖ ≤
        ‖f.toBoundedContinuousFunction‖ *
          (χ q.1.1 * χ' q.2.2 * w (q.1.2 - q.2.1))
      calc
        ‖f (q.1.1, q.2.2) * w (q.1.2 - q.2.1)‖ =
            ‖f (q.1.1, q.2.2)‖ * w (q.1.2 - q.2.1) := by
          rw [norm_mul, Real.norm_of_nonneg hwq]
        _ ≤ ‖f.toBoundedContinuousFunction‖ * w (q.1.2 - q.2.1) :=
          mul_le_mul_of_nonneg_right
            (f.toBoundedContinuousFunction.norm_coe_le_norm (q.1.1, q.2.2)) hwq
        _ = ‖f.toBoundedContinuousFunction‖ *
            (χ q.1.1 * χ' q.2.2 * w (q.1.2 - q.2.1)) := by
          rw [hχ, hχ']
          ring
  have hFint : Integrable F ((Z s₀ s₁ ω).prod (Z s₁ s₂ ω)) := by
    apply hmajor.mono' hFcont.aestronglyMeasurable
    filter_upwards [] with q
    exact hbound q
  exact hFint

/-- A signed compact endpoint test has an integrable square after cutoff, by domination with positive endpoint mass tests. -/
private theorem eventually_cutoffProduct_signed_sq_integrable
    (ϑ : ℝ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
    (D : Set ℝ) (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsPolymerSubseqLimit ϑ D ψ P Z)
    {s₀ s₁ s₂ : ℝ} (hs₀D : s₀ ∈ D) (hs₁D : s₁ ∈ D) (hs₂D : s₂ ∈ D)
    (hs₀ : 0 ≤ s₀) (hs₀₁ : s₀ < s₁) (hs₁₂ : s₁ < s₂)
    (f : C_c(Plane × Plane, ℝ)) (k : Plane → ℝ)
    (hk : Continuous k) (hk0 : ∀ x, 0 ≤ k x)
    (R : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      Integrable (fun ω =>
        (∫ q, f (q.1.1, q.2.2) * k (q.1.2 - q.2.1) *
          ballCutoff R q.1.2 * ballCutoff R q.2.1 ∂
            ((polymerMeasure ϑ (ψ n) s₀ s₁ ω).prod
              (polymerMeasure ϑ (ψ n) s₁ s₂ ω))) ^ 2) disorderLaw := by
  classical
  let E : CompactExhaustion Plane := RandomMeasure.vagueCompactExhaustion Plane
  let K : Set (Plane × Plane) := tsupport (f : Plane × Plane → ℝ)
  have hK : IsCompact K := f.hasCompactSupport
  let A : Set Plane := Prod.fst '' K
  let B : Set Plane := Prod.snd '' K
  have hA : IsCompact A := hK.image continuous_fst
  have hB : IsCompact B := hK.image continuous_snd
  obtain ⟨m, hm⟩ := E.exists_superset_of_isCompact hA
  obtain ⟨r, hr⟩ := E.exists_superset_of_isCompact hB
  let χ : C_c(Plane, ℝ) := RandomMeasure.vagueMassTest E m
  let χ' : C_c(Plane, ℝ) := RandomMeasure.vagueMassTest E r
  let Ψ : C_c(Plane × Plane, ℝ) := compactTensorTest χ χ'
  have hΨ0 (p : Plane × Plane) : 0 ≤ Ψ p := by
    change 0 ≤ χ p.1 * χ' p.2
    exact mul_nonneg ((RandomMeasure.vagueMassTest_spec E m).1 p.1)
      ((RandomMeasure.vagueMassTest_spec E r).1 p.2)
  obtain ⟨Cenv, hEnvSq⟩ := eventually_polymerSubseq_cutoffProduct_sq_bound
    ϑ hFlatSixthMomentInput D ψ hψ P Z hZ hs₀D hs₁D hs₂D hs₀ hs₀₁ hs₁₂ Ψ hΨ0 k hk hk0 R
  let F : ((Plane × Plane) × (Plane × Plane)) → ℝ := fun q =>
    f (q.1.1, q.2.2) * k (q.1.2 - q.2.1) *
      ballCutoff R q.1.2 * ballCutoff R q.2.1
  let H : ((Plane × Plane) × (Plane × Plane)) → ℝ := fun q =>
    Ψ (q.1.1, q.2.2) * k (q.1.2 - q.2.1) *
      ballCutoff R q.1.2 * ballCutoff R q.2.1
  let c : ℝ := ‖f.toBoundedContinuousFunction‖
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hHnonneg (q : (Plane × Plane) × (Plane × Plane)) : 0 ≤ H q := by
    dsimp [H]
    exact mul_nonneg (mul_nonneg (mul_nonneg (hΨ0 _) (hk0 _))
      (ballCutoff_mem_Icc R _).1) (ballCutoff_mem_Icc R _).1
  have hFbound (q : (Plane × Plane) × (Plane × Plane)) : ‖F q‖ ≤ c * H q := by
    by_cases hfq : f (q.1.1, q.2.2) = 0
    · simp only [F, hfq, zero_mul, norm_zero]
      exact mul_nonneg hc (hHnonneg q)
    · have hq : (q.1.1, q.2.2) ∈ K :=
        subset_tsupport f (Function.mem_support.mpr hfq)
      have hχ : χ q.1.1 = 1 := by
        apply (RandomMeasure.vagueMassTest_spec E m).2.2.1
        exact hm ⟨(q.1.1, q.2.2), hq, rfl⟩
      have hχ' : χ' q.2.2 = 1 := by
        apply (RandomMeasure.vagueMassTest_spec E r).2.2.1
        exact hr ⟨(q.1.1, q.2.2), hq, rfl⟩
      have hkq : 0 ≤ k (q.1.2 - q.2.1) := hk0 _
      have hcut₁ : 0 ≤ ballCutoff R q.1.2 := (ballCutoff_mem_Icc R _).1
      have hcut₂ : 0 ≤ ballCutoff R q.2.1 := (ballCutoff_mem_Icc R _).1
      have hfnorm : |f (q.1.1, q.2.2)| ≤ c := by
        change ‖f (q.1.1, q.2.2)‖ ≤ c
        exact f.toBoundedContinuousFunction.norm_coe_le_norm _
      change |f (q.1.1, q.2.2) * k (q.1.2 - q.2.1) *
        ballCutoff R q.1.2 * ballCutoff R q.2.1| ≤ c *
          (Ψ (q.1.1, q.2.2) * k (q.1.2 - q.2.1) *
            ballCutoff R q.1.2 * ballCutoff R q.2.1)
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hkq,
        abs_of_nonneg hcut₁, abs_of_nonneg hcut₂]
      calc
        |f (q.1.1, q.2.2)| * k (q.1.2 - q.2.1) *
            ballCutoff R q.1.2 * ballCutoff R q.2.1 ≤
          c * k (q.1.2 - q.2.1) * ballCutoff R q.1.2 * ballCutoff R q.2.1 := by
            gcongr
        _ = c * H q := by
          simp [H, Ψ, χ, χ', compactTensorTest_apply, hχ, hχ']
          ring
  have hCmeas (n : ℕ) : AEMeasurable
      (fun ω => ∫ q, F q ∂((polymerMeasure ϑ (ψ n) s₀ s₁ ω).prod
        (polymerMeasure ϑ (ψ n) s₁ s₂ ω))) disorderLaw := by
    have hdist := polymerSubseqLimit_cutoffProduct_joint_tendstoInDistribution
      ϑ hFlatSixthMomentInput D ψ hψ P Z hZ hs₀D hs₁D hs₂D hs₀ hs₀₁ hs₁₂ f k hk R
    have h := measurable_fst.comp_aemeasurable (hdist.forall_aemeasurable n)
    exact h.congr (Filter.Eventually.of_forall fun ω => by simp [F])
  filter_upwards [hEnvSq] with n hEnv
  have hEnvInt : Integrable (fun ω =>
      (∫ q, H q ∂((polymerMeasure ϑ (ψ n) s₀ s₁ ω).prod
        (polymerMeasure ϑ (ψ n) s₁ s₂ ω))) ^ 2) disorderLaw := by
    exact hEnv.1.congr (Filter.Eventually.of_forall fun ω => by simp [H])
  have hmajor : Integrable (fun ω => c ^ 2 *
      (∫ q, H q ∂((polymerMeasure ϑ (ψ n) s₀ s₁ ω).prod
        (polymerMeasure ϑ (ψ n) s₁ s₂ ω))) ^ 2) disorderLaw :=
    hEnvInt.const_mul (c ^ 2)
  have htargetSqMeas : AEStronglyMeasurable
      (fun ω => (∫ q, F q ∂((polymerMeasure ϑ (ψ n) s₀ s₁ ω).prod
        (polymerMeasure ϑ (ψ n) s₁ s₂ ω))) ^ 2) disorderLaw :=
    (continuous_id.pow 2).comp_aestronglyMeasurable (hCmeas n).aestronglyMeasurable
  apply hmajor.mono' htargetSqMeas
  filter_upwards [] with ω
  have hEnvNonneg : 0 ≤ ∫ q, H q ∂((polymerMeasure ϑ (ψ n) s₀ s₁ ω).prod
      (polymerMeasure ϑ (ψ n) s₁ s₂ ω)) :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall hHnonneg)
  have hnorm : ‖∫ q, F q ∂((polymerMeasure ϑ (ψ n) s₀ s₁ ω).prod
      (polymerMeasure ϑ (ψ n) s₁ s₂ ω))‖ ≤
      c * ∫ q, H q ∂((polymerMeasure ϑ (ψ n) s₀ s₁ ω).prod
        (polymerMeasure ϑ (ψ n) s₁ s₂ ω)) := by
    calc
      _ ≤ ∫ q, ‖F q‖ ∂((polymerMeasure ϑ (ψ n) s₀ s₁ ω).prod
        (polymerMeasure ϑ (ψ n) s₁ s₂ ω)) := norm_integral_le_integral_norm _
      _ ≤ ∫ q, c * H q ∂((polymerMeasure ϑ (ψ n) s₀ s₁ ω).prod
        (polymerMeasure ϑ (ψ n) s₁ s₂ ω)) := by
          apply integral_mono
            (@integrable_cutoffProduct_test (polymerMeasure ϑ (ψ n) s₀ s₁ ω)
              (polymerMeasure ϑ (ψ n) s₁ s₂ ω)
              (isLocallyFiniteMeasure_polymerMeasure ϑ (ψ n) s₀ s₁ ω)
              (isLocallyFiniteMeasure_polymerMeasure ϑ (ψ n) s₁ s₂ ω)
              f k hk R).norm
            ((@integrable_cutoffProduct_test (polymerMeasure ϑ (ψ n) s₀ s₁ ω)
              (polymerMeasure ϑ (ψ n) s₁ s₂ ω)
              (isLocallyFiniteMeasure_polymerMeasure ϑ (ψ n) s₀ s₁ ω)
              (isLocallyFiniteMeasure_polymerMeasure ϑ (ψ n) s₁ s₂ ω)
              Ψ k hk R).const_mul c)
          intro q
          exact hFbound q
      _ = c * ∫ q, H q ∂((polymerMeasure ϑ (ψ n) s₀ s₁ ω).prod
        (polymerMeasure ϑ (ψ n) s₁ s₂ ω)) := by rw [integral_const_mul]
  have hsq : (∫ q, F q ∂((polymerMeasure ϑ (ψ n) s₀ s₁ ω).prod
        (polymerMeasure ϑ (ψ n) s₁ s₂ ω))) ^ 2 ≤
      c ^ 2 * (∫ q, H q ∂((polymerMeasure ϑ (ψ n) s₀ s₁ ω).prod
        (polymerMeasure ϑ (ψ n) s₁ s₂ ω))) ^ 2 := by
    have hI : 0 ≤ ∫ q, H q ∂((polymerMeasure ϑ (ψ n) s₀ s₁ ω).prod
        (polymerMeasure ϑ (ψ n) s₁ s₂ ω)) := hEnvNonneg
    have hnonneg : 0 ≤ c * (∫ q, H q ∂((polymerMeasure ϑ (ψ n) s₀ s₁ ω).prod
        (polymerMeasure ϑ (ψ n) s₁ s₂ ω))) := mul_nonneg hc hI
    have hx := norm_nonneg (∫ q, F q ∂((polymerMeasure ϑ (ψ n) s₀ s₁ ω).prod
      (polymerMeasure ϑ (ψ n) s₁ s₂ ω)))
    have hsq' : ‖∫ q, F q ∂((polymerMeasure ϑ (ψ n) s₀ s₁ ω).prod
        (polymerMeasure ϑ (ψ n) s₁ s₂ ω))‖ ^ 2 ≤
        (c * ∫ q, H q ∂((polymerMeasure ϑ (ψ n) s₀ s₁ ω).prod
          (polymerMeasure ϑ (ψ n) s₁ s₂ ω))) ^ 2 := by
      nlinarith [sq_nonneg (‖∫ q, F q ∂((polymerMeasure ϑ (ψ n) s₀ s₁ ω).prod
        (polymerMeasure ϑ (ψ n) s₁ s₂ ω))‖ - c * ∫ q, H q ∂
          ((polymerMeasure ϑ (ψ n) s₀ s₁ ω).prod
            (polymerMeasure ϑ (ψ n) s₁ s₂ ω)))]
    calc
      _ = ‖∫ q, F q ∂((polymerMeasure ϑ (ψ n) s₀ s₁ ω).prod
          (polymerMeasure ϑ (ψ n) s₁ s₂ ω))‖ ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
      _ ≤ _ := hsq'
      _ = _ := by ring
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact hsq

/-- Transfer the cutoff tail and approximate-flow errors to the limiting smoothed product. -/
private theorem polymerSubseqLimit_smoothedProduct_sq_error_transfer
    (ϑ : ℝ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ) (hProductCutoffTailInput : SmoothedProductCutoffTail ϑ)
    (D : Set ℝ) (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsPolymerSubseqLimit ϑ D ψ P Z)
    {s₀ s₁ s₂ : ℝ} (hs₀D : s₀ ∈ D) (hs₁D : s₁ ∈ D) (hs₂D : s₂ ∈ D)
    (hs₀ : 0 ≤ s₀) (hs₀₁ : s₀ < s₁) (hs₁₂ : s₁ < s₂)
    (f : C_c(Plane × Plane, ℝ)) (k : Plane → ℝ)
    (hk : Continuous k) (hkc : HasCompactSupport k) (hk0 : ∀ x, 0 ≤ k x)
    (hdef : ∀ᵐ ω ∂P, SmoothedProductWellDefined (Z s₀ s₁ ω) k (Z s₁ s₂ ω))
    {ε : ℝ} (hε : 0 < ε)
    (hApprox : ∀ᶠ n : ℕ in atTop,
      ∫ ω, (smoothedProductPairing (polymerMeasure ϑ (ψ n) s₀ s₁ ω) k
          (polymerMeasure ϑ (ψ n) s₁ s₂ ω) f -
        ∫ p, f p ∂polymerMeasure ϑ (ψ n) s₀ s₂ ω) ^ 2 ∂disorderLaw ≤ ε / 4) :
    ∫⁻ ω, ENNReal.ofReal
      ((smoothedProductPairing (Z s₀ s₁ ω) k (Z s₁ s₂ ω) f -
        ∫ p, f p ∂Z s₀ s₂ ω) ^ 2) ∂P ≤ ENNReal.ofReal ε := by
  classical
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨R₀, htail⟩ := hProductCutoffTailInput hs₀ hs₀₁ hs₁₂ f k
    (Or.inl ⟨hk, hkc, hk0⟩) (ε / 4) hε4
  let A (n : ℕ) (ω : Disorder) : ℝ :=
    smoothedProductPairing (polymerMeasure ϑ (ψ n) s₀ s₁ ω) k
      (polymerMeasure ϑ (ψ n) s₁ s₂ ω) f
  let B (n : ℕ) (ω : Disorder) : ℝ :=
    ∫ p, f p ∂polymerMeasure ϑ (ψ n) s₀ s₂ ω
  let C (R : ℝ) (n : ℕ) (ω : Disorder) : ℝ :=
    ∫ q, f (q.1.1, q.2.2) * k (q.1.2 - q.2.1) *
      ballCutoff R q.1.2 * ballCutoff R q.2.1 ∂
        ((polymerMeasure ϑ (ψ n) s₀ s₁ ω).prod
          (polymerMeasure ϑ (ψ n) s₁ s₂ ω))
  let Blim (ω : Ω) : ℝ := ∫ p, f p ∂Z s₀ s₂ ω
  let Clim (R : ℝ) (ω : Ω) : ℝ :=
    ∫ q, f (q.1.1, q.2.2) * k (q.1.2 - q.2.1) *
      ballCutoff R q.1.2 * ballCutoff R q.2.1 ∂
        ((Z s₀ s₁ ω).prod (Z s₁ s₂ ω))
  let Alim (ω : Ω) : ℝ := smoothedProductPairing (Z s₀ s₁ ω) k (Z s₁ s₂ ω) f
  have hAmemLp (n : ℕ) : MemLp (A n) 2 disorderLaw := by
    simpa [A] using memLp_smoothedProductPairing_two ϑ (ψ n) s₀ s₁ s₁ s₂ f k hk hkc
  have hBmemLp (n : ℕ) : MemLp (B n) 2 disorderLaw := by
    simpa [B] using memLp_polymerPairing_two ϑ (ψ n) s₀ s₂ f
  have hAsq (n : ℕ) : Integrable (fun ω => (A n ω) ^ 2) disorderLaw := by
    exact (hAmemLp n).integrable_sq
  have hBsq (n : ℕ) : Integrable (fun ω => (B n ω) ^ 2) disorderLaw := by
    exact (hBmemLp n).integrable_sq
  have hAsmeas (n : ℕ) : AEStronglyMeasurable (A n) disorderLaw :=
    (hAmemLp n).aestronglyMeasurable
  have hBsmeas (n : ℕ) : AEStronglyMeasurable (B n) disorderLaw :=
    (hBmemLp n).aestronglyMeasurable
  have hdist (R : ℝ) : TendstoInDistribution
      (fun n ω => (C R n ω, B n ω)) atTop (fun ω => (Clim R ω, Blim ω))
      (fun _ => disorderLaw) P := by
    simpa [C, B, Clim, Blim] using
      polymerSubseqLimit_cutoffProduct_joint_tendstoInDistribution
        ϑ hFlatSixthMomentInput D ψ hψ P Z hZ hs₀D hs₁D hs₂D hs₀ hs₀₁ hs₁₂ f k hk R
  have hCmeas (R : ℝ) (n : ℕ) : AEMeasurable (C R n) disorderLaw := by
    have h := measurable_fst.comp_aemeasurable ((hdist R).forall_aemeasurable n)
    exact h.congr (Filter.Eventually.of_forall fun ω => by simp [C])
  have hBmeas : AEMeasurable Blim P := by
    have h := measurable_snd.comp_aemeasurable (hdist R₀).aemeasurable_limit
    exact h.congr (Filter.Eventually.of_forall fun ω => by simp [Blim])
  have htailN (R : ℝ) (hR : R₀ ≤ R) : ∀ᶠ n : ℕ in atTop,
      ∫ ω, (A n ω - C R n ω) ^ 2 ∂disorderLaw ≤ ε / 4 := by
    have hN := htail R hR
    filter_upwards [hψ.tendsto_atTop.eventually hN] with n hn
    simpa [A, C] using hn
  have hCutSq (R : ℝ) : ∀ᶠ n : ℕ in atTop,
      Integrable (fun ω => (C R n ω) ^ 2) disorderLaw := by
    filter_upwards [eventually_cutoffProduct_signed_sq_integrable
      ϑ hFlatSixthMomentInput D ψ hψ P Z hZ hs₀D hs₁D hs₂D hs₀ hs₀₁ hs₁₂ f k hk hk0 R]
      with n hn
    exact hn.congr (Filter.Eventually.of_forall fun ω => by simp [C])
  have hlimitR (R : ℝ) (hR : R₀ ≤ R) :
      ∫⁻ ω, ENNReal.ofReal ((Clim R ω - Blim ω) ^ 2) ∂P ≤ ENNReal.ofReal ε := by
    have hbound : ∀ᶠ n : ℕ in atTop,
        Integrable (fun ω => (C R n ω - B n ω) ^ 2) disorderLaw ∧
          ∫ ω, (C R n ω - B n ω) ^ 2 ∂disorderLaw ≤ ε := by
      filter_upwards [hCutSq R, htailN R hR, hApprox] with n hC htailNn hApproxN
      have hCnegSq : Integrable (fun ω => (-(C R n ω)) ^ 2) disorderLaw :=
        hC.congr (Filter.Eventually.of_forall fun ω => by ring)
      have hBnegSq : Integrable (fun ω => (-(B n ω)) ^ 2) disorderLaw :=
        (hBsq n).congr (Filter.Eventually.of_forall fun ω => by ring)
      have hAC := integrable_sq_add_le_two disorderLaw (hAsmeas n)
        (hCmeas R n).aestronglyMeasurable.neg (hAsq n) hCnegSq
      have hAB := integrable_sq_add_le_two disorderLaw (hAsmeas n)
        (hBsmeas n).neg (hAsq n) hBnegSq
      have hACsq : Integrable (fun ω => (A n ω - C R n ω) ^ 2) disorderLaw :=
        hAC.1.congr (Filter.Eventually.of_forall fun ω => by simp; ring)
      have hABsq : Integrable (fun ω => (A n ω - B n ω) ^ 2) disorderLaw :=
        hAB.1.congr (Filter.Eventually.of_forall fun ω => by simp; ring)
      have hACnegSq : Integrable (fun ω => (-(A n ω - C R n ω)) ^ 2) disorderLaw :=
        hACsq.congr (Filter.Eventually.of_forall fun ω => by ring)
      have hsum := integrable_sq_add_le_two disorderLaw
        ((hAsmeas n).sub (hBsmeas n)) ((hAsmeas n).sub (hCmeas R n).aestronglyMeasurable).neg
        hABsq hACnegSq
      have herrorInt : Integrable (fun ω => (C R n ω - B n ω) ^ 2) disorderLaw :=
        hsum.1.congr (Filter.Eventually.of_forall fun ω => by dsimp; ring)
      have hnegSq : ∫ ω, (-(A n ω - C R n ω)) ^ 2 ∂disorderLaw =
          ∫ ω, (A n ω - C R n ω) ^ 2 ∂disorderLaw := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω => by ring
      refine ⟨herrorInt, ?_⟩
      calc
        ∫ ω, (C R n ω - B n ω) ^ 2 ∂disorderLaw =
            ∫ ω, (A n ω - B n ω + -(A n ω - C R n ω)) ^ 2 ∂disorderLaw := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun ω => by ring
        _ ≤ 2 * (∫ ω, (A n ω - B n ω) ^ 2 ∂disorderLaw +
            ∫ ω, (-(A n ω - C R n ω)) ^ 2 ∂disorderLaw) := hsum.2
        _ ≤ 2 * (ε / 4 + ε / 4) := by
          rw [hnegSq]
          nlinarith [hApproxN, htailNn]
        _ = ε := by ring
    exact lintegral_sq_sub_le_of_tendstoInDistribution
      (μ := fun _ : ℕ => disorderLaw) (hdist R) hbound
  let Rseq (j : ℕ) : ℝ := R₀ + j
  have hRseqtop : Tendsto Rseq atTop atTop := by
    simpa [Rseq, add_comm] using tendsto_atTop_add_const_right _ R₀
      tendsto_natCast_atTop_atTop
  have hRseq (j : ℕ) : R₀ ≤ Rseq j := by
    dsimp [Rseq]
    exact le_add_of_nonneg_right (Nat.cast_nonneg j)
  have hcutLimMeas (j : ℕ) : AEMeasurable (Clim (Rseq j)) P := by
    have h := (hdist (Rseq j)).aemeasurable_limit
    have h' := measurable_fst.comp_aemeasurable h
    exact h'.congr (Filter.Eventually.of_forall fun ω => by simp [Clim])
  have hfullMeas : AEMeasurable Alim P := by
    apply aemeasurable_of_tendsto_metrizable_ae atTop hcutLimMeas
    filter_upwards [hdef] with ω hdefω
    rw [Metric.tendsto_nhds]
    intro δ hδ
    have hcut := (smoothedProductPairing_cutoff_tendsto
      (Z s₀ s₁ ω) k (Z s₁ s₂ ω) hk.measurable f hdefω).comp hRseqtop
    have hcut' : Tendsto (fun j => Clim (Rseq j) ω) atTop (𝓝 (Alim ω)) := by
      simpa only [Function.comp_def, Clim, Alim] using hcut
    exact (Metric.tendsto_nhds.mp hcut') δ hδ
  have hpointwise : ∀ᵐ ω ∂P, Tendsto
      (fun j : ℕ => ENNReal.ofReal ((Clim (Rseq j) ω - Blim ω) ^ 2)) atTop
      (𝓝 (ENNReal.ofReal ((Alim ω - Blim ω) ^ 2))) := by
    filter_upwards [hdef] with ω hdefω
    have hcut := (smoothedProductPairing_cutoff_tendsto
      (Z s₀ s₁ ω) k (Z s₁ s₂ ω) hk.measurable f hdefω).comp hRseqtop
    have hcut' : Tendsto (fun j => Clim (Rseq j) ω) atTop (𝓝 (Alim ω)) := by
      simpa only [Function.comp_def, Clim, Alim] using hcut
    have hreal := (hcut'.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => Blim ω)
      atTop (𝓝 (Blim ω)))).pow 2
    have henn := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
    simpa only [Function.comp_def] using henn
  have hseqMeas (j : ℕ) : AEMeasurable
      (fun ω => ENNReal.ofReal ((Clim (Rseq j) ω - Blim ω) ^ 2)) P := by
    exact (ENNReal.measurable_ofReal.comp_aemeasurable
      ((continuous_id.pow 2).measurable.comp_aemeasurable
        ((hcutLimMeas j).sub hBmeas)))
  have hfatou : ∫⁻ ω, ENNReal.ofReal ((Alim ω - Blim ω) ^ 2) ∂P ≤
      liminf (fun j : ℕ => ∫⁻ ω,
        ENNReal.ofReal ((Clim (Rseq j) ω - Blim ω) ^ 2) ∂P) atTop := by
    calc
      _ = ∫⁻ ω, liminf (fun j : ℕ =>
          ENNReal.ofReal ((Clim (Rseq j) ω - Blim ω) ^ 2)) atTop ∂P := by
        apply lintegral_congr_ae
        filter_upwards [hpointwise] with ω hω
        exact hω.liminf_eq.symm
      _ ≤ _ := lintegral_liminf_le' hseqMeas
  have hliminfBound : liminf (fun j : ℕ => ∫⁻ ω,
      ENNReal.ofReal ((Clim (Rseq j) ω - Blim ω) ^ 2) ∂P) atTop ≤ ENNReal.ofReal ε := by
    calc
      _ ≤ liminf (fun _ : ℕ => ENNReal.ofReal ε) atTop :=
        liminf_le_liminf (Filter.Eventually.of_forall fun j => hlimitR (Rseq j) (hRseq j))
      _ = ENNReal.ofReal ε := by simp
  exact hfatou.trans hliminfBound

/-- Cutoff integrals of a fixed limiting smoothed product converge almost surely to the full
pairing, so the pairing is measurable under the subsequential law. -/
private theorem aemeasurable_polymerSubseqLimit_smoothedProductPairing
    (ϑ : ℝ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
    (D : Set ℝ) (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsPolymerSubseqLimit ϑ D ψ P Z)
    {s₀ s₁ s₂ : ℝ} (hs₀D : s₀ ∈ D) (hs₁D : s₁ ∈ D) (hs₂D : s₂ ∈ D)
    (hs₀ : 0 ≤ s₀) (hs₀₁ : s₀ < s₁) (hs₁₂ : s₁ < s₂)
    (f : C_c(Plane × Plane, ℝ)) (k : Plane → ℝ) (hk : Continuous k)
    (hdef : ∀ᵐ ω ∂P, SmoothedProductWellDefined (Z s₀ s₁ ω) k (Z s₁ s₂ ω)) :
    AEMeasurable (fun ω => smoothedProductPairing (Z s₀ s₁ ω) k
      (Z s₁ s₂ ω) f) P := by
  let Rseq (j : ℕ) : ℝ := j
  have hRtop : Tendsto Rseq atTop atTop := by
    simpa [Rseq] using tendsto_natCast_atTop_atTop
  have hdist (R : ℝ) : TendstoInDistribution
      (fun n (ω : Disorder) =>
        (∫ q, f (q.1.1, q.2.2) * k (q.1.2 - q.2.1) *
          ballCutoff R q.1.2 * ballCutoff R q.2.1 ∂
            ((polymerMeasure ϑ (ψ n) s₀ s₁ ω).prod
              (polymerMeasure ϑ (ψ n) s₁ s₂ ω)),
         ∫ p, f p ∂polymerMeasure ϑ (ψ n) s₀ s₂ ω)) atTop
      (fun ω =>
        (∫ q, f (q.1.1, q.2.2) * k (q.1.2 - q.2.1) *
          ballCutoff R q.1.2 * ballCutoff R q.2.1 ∂
            ((Z s₀ s₁ ω).prod (Z s₁ s₂ ω)),
         ∫ p, f p ∂Z s₀ s₂ ω)) (fun _ => disorderLaw) P := by
    exact polymerSubseqLimit_cutoffProduct_joint_tendstoInDistribution
      ϑ hFlatSixthMomentInput D ψ hψ P Z hZ hs₀D hs₁D hs₂D hs₀ hs₀₁ hs₁₂ f k hk R
  have hcutMeas (j : ℕ) : AEMeasurable (fun ω =>
      ∫ q, f (q.1.1, q.2.2) * k (q.1.2 - q.2.1) *
        ballCutoff (Rseq j) q.1.2 * ballCutoff (Rseq j) q.2.1 ∂
          ((Z s₀ s₁ ω).prod (Z s₁ s₂ ω))) P := by
    have h := measurable_fst.comp_aemeasurable
      ((hdist (Rseq j)).aemeasurable_limit)
    exact h.congr (Filter.Eventually.of_forall fun ω => rfl)
  apply aemeasurable_of_tendsto_metrizable_ae atTop hcutMeas
  filter_upwards [hdef] with ω hdefω
  rw [Metric.tendsto_nhds]
  intro δ hδ
  have hcut := (smoothedProductPairing_cutoff_tendsto
    (Z s₀ s₁ ω) k (Z s₁ s₂ ω) hk.measurable f hdefω).comp hRtop
  have hcut' : Tendsto (fun j =>
      ∫ q, f (q.1.1, q.2.2) * k (q.1.2 - q.2.1) *
        ballCutoff (Rseq j) q.1.2 * ballCutoff (Rseq j) q.2.1 ∂
          ((Z s₀ s₁ ω).prod (Z s₁ s₂ ω))) atTop
      (𝓝 (smoothedProductPairing (Z s₀ s₁ ω) k (Z s₁ s₂ ω) f)) := by
    simpa only [Function.comp_def] using hcut
  exact (Metric.tendsto_nhds.mp hcut') δ hδ

/-- The dense mollifier sequence is almost surely well-defined and its smoothed products converge in measure to the direct pairing. -/
theorem polymerSubseqLimit_smoothedProduct_of (ϑ : ℝ)
    (hPolymerMomentInput : PolymerMomentLimit ϑ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
    (hProductCutoffTailInput : SmoothedProductCutoffTail ϑ) (hSmoothedApproximateFlowInput : SmoothedProductApproxFlow ϑ)
    (D : Set ℝ) (hD : D.Countable) (hD0 : ∀ s ∈ D, 0 ≤ s)
    (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsPolymerSubseqLimit ϑ D ψ P Z) :
    ∀ t₀ ∈ D, ∀ t₁ ∈ D, ∀ t₂ ∈ D, t₀ < t₁ → t₁ < t₂ →
      ∃ w : ℕ → Plane → ℝ, IsL2ApplicableMollifier w ∧
        (∀ ℓ, ∀ᵐ ω ∂P, SmoothedProductWellDefined
          (Z t₀ t₁ ω) (w ℓ) (Z t₁ t₂ ω)) ∧
        ∀ f : C_c(Plane × Plane, ℝ),
          TendstoInMeasure P
            (fun ℓ ω => smoothedProductPairing (Z t₀ t₁ ω) (w ℓ)
              (Z t₁ t₂ ω) f - ∫ p, f p ∂Z t₀ t₂ ω)
            atTop (fun _ => 0) := by
  have _momentInput : PolymerMomentLimit ϑ := hPolymerMomentInput
  have _countableTimes : D.Countable := hD
  have _nonnegativeTimes : ∀ s ∈ D, 0 ≤ s := hD0
  intro t₀ ht₀D t₁ ht₁D t₂ ht₂D ht₀₁ ht₁₂
  refine ⟨subseqDenseMollifier, isL2ApplicableMollifier_subseqDenseMollifier, ?_, ?_⟩
  · intro ℓ
    exact polymerSubseqLimit_smoothedProduct_wellDefined_of
      ϑ hFlatSixthMomentInput hProductCutoffTailInput D ψ hψ P Z hZ ht₀D ht₁D ht₂D
      (hD0 t₀ ht₀D) ht₀₁ ht₁₂ (subseqDenseMollifier ℓ)
      (subseqDenseMollifier_spec ℓ).2.1.continuous
      (subseqDenseMollifier_spec ℓ).2.2.1
      (subseqDenseMollifier_spec ℓ).1
  · intro f
    apply tendstoInMeasure_of_lintegral_sq_tendsto_zero P
    · intro ℓ
      have hdef := polymerSubseqLimit_smoothedProduct_wellDefined_of
        ϑ hFlatSixthMomentInput hProductCutoffTailInput D ψ hψ P Z hZ ht₀D ht₁D ht₂D
        (hD0 t₀ ht₀D) ht₀₁ ht₁₂ (subseqDenseMollifier ℓ)
        (subseqDenseMollifier_spec ℓ).2.1.continuous
        (subseqDenseMollifier_spec ℓ).2.2.1
        (subseqDenseMollifier_spec ℓ).1
      have hfull := aemeasurable_polymerSubseqLimit_smoothedProductPairing
        ϑ hFlatSixthMomentInput D ψ hψ P Z hZ ht₀D ht₁D ht₂D (hD0 t₀ ht₀D) ht₀₁ ht₁₂
        f (subseqDenseMollifier ℓ) (subseqDenseMollifier_spec ℓ).2.1.continuous hdef
      have hdirect : AEMeasurable (fun ω => ∫ p, f p ∂Z t₀ t₂ ω) P := by
        have hdist := polymerSubseqLimit_cutoffProduct_joint_tendstoInDistribution
          ϑ hFlatSixthMomentInput D ψ hψ P Z hZ ht₀D ht₁D ht₂D (hD0 t₀ ht₀D) ht₀₁ ht₁₂
          f (subseqDenseMollifier ℓ) (subseqDenseMollifier_spec ℓ).2.1.continuous 0
        have h := measurable_snd.comp_aemeasurable hdist.aemeasurable_limit
        exact h.congr (Filter.Eventually.of_forall fun ω => rfl)
      exact hfull.sub hdirect
    · intro ε hε
      have hε4 : 0 < ε / 4 := by positivity
      have hApprox := subseqDenseMollifier_approxFlow_eventually
        ϑ hSmoothedApproximateFlowInput (hD0 t₀ ht₀D) ht₀₁ ht₁₂ f (ε / 4) hε4
      filter_upwards [hApprox] with ℓ hApproxℓ
      have hdef := polymerSubseqLimit_smoothedProduct_wellDefined_of
        ϑ hFlatSixthMomentInput hProductCutoffTailInput D ψ hψ P Z hZ ht₀D ht₁D ht₂D
        (hD0 t₀ ht₀D) ht₀₁ ht₁₂ (subseqDenseMollifier ℓ)
        (subseqDenseMollifier_spec ℓ).2.1.continuous
        (subseqDenseMollifier_spec ℓ).2.2.1
        (subseqDenseMollifier_spec ℓ).1
      have hApproxψ : ∀ᶠ n : ℕ in atTop,
          ∫ ω, (smoothedProductPairing (polymerMeasure ϑ (ψ n) t₀ t₁ ω)
              (subseqDenseMollifier ℓ) (polymerMeasure ϑ (ψ n) t₁ t₂ ω) f -
            ∫ p, f p ∂polymerMeasure ϑ (ψ n) t₀ t₂ ω) ^ 2 ∂disorderLaw ≤ ε / 4 := by
        filter_upwards [hψ.tendsto_atTop.eventually hApproxℓ] with n hn
        simpa only [Function.comp_def] using hn
      exact polymerSubseqLimit_smoothedProduct_sq_error_transfer
        ϑ hFlatSixthMomentInput hProductCutoffTailInput D ψ hψ P Z hZ ht₀D ht₁D ht₂D
        (hD0 t₀ ht₀D) ht₀₁ ht₁₂ f (subseqDenseMollifier ℓ)
        (subseqDenseMollifier_spec ℓ).2.1.continuous
        (subseqDenseMollifier_spec ℓ).2.2.1
        (subseqDenseMollifier_spec ℓ).1 hdef hε hApproxψ

/-- A polymer subsequential limit satisfies the dense-time flow axioms under the cutoff-tail and approximate-composition hypotheses. -/
theorem isDenseSHF_of_isPolymerSubseqLimit_of_cutoff_tail_and_approximate_flow (ϑ : ℝ)
    (hPolymerMomentInput : PolymerMomentLimit ϑ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
    (hProductCutoffTailInput : SmoothedProductCutoffTail ϑ) (hSmoothedApproximateFlowInput : SmoothedProductApproxFlow ϑ)
    (D : Set ℝ) (hD : D.Countable) (hD0 : ∀ s ∈ D, 0 ≤ s)
    (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsPolymerSubseqLimit ϑ D ψ P Z) :
    IsDenseSHF (ϑ - Real.eulerMascheroniConstant) D P Z := by
  exact isDenseSHF_of_subseqLimit_components ϑ
    D hD ψ hψ P Z hZ
    (polymerSubseqLimit_smoothedProduct_of ϑ hPolymerMomentInput hFlatSixthMomentInput hProductCutoffTailInput hSmoothedApproximateFlowInput
      D hD hD0 ψ hψ P Z hZ)
    (polymerSubseqLimit_moment_formula_of ϑ hPolymerMomentInput hFlatSixthMomentInput D hD hD0 ψ hψ P Z hZ)

/-- A polymer subsequential limit satisfies the dense-time flow axioms under the approximate-composition hypothesis. -/
theorem isDenseSHF_of_isPolymerSubseqLimit_of_approximate_flow (ϑ : ℝ)
    (hPolymerMomentInput : PolymerMomentLimit ϑ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
    (hSmoothedApproximateFlowInput : SmoothedProductApproxFlow ϑ)
    (D : Set ℝ) (hD : D.Countable) (hD0 : ∀ s ∈ D, 0 ≤ s)
    (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsPolymerSubseqLimit ϑ D ψ P Z) :
    IsDenseSHF (ϑ - Real.eulerMascheroniConstant) D P Z := by
  apply isDenseSHF_of_isPolymerSubseqLimit_of_cutoff_tail_and_approximate_flow
    ϑ hPolymerMomentInput hFlatSixthMomentInput ?_ hSmoothedApproximateFlowInput D hD hD0 ψ hψ P Z hZ
  intro s t u hs hst htu Φ k hk ε hε
  exact smoothedProduct_cutoff_tail ϑ hs hst htu Φ k hk ε hε

end Critical2DKPZ.SHF.Flow

end
