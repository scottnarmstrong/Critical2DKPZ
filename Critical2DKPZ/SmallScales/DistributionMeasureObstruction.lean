/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SmallScales.LebesgueDifferentiation
public import Critical2DKPZ.SmallScales.SmallBallKernel
public import Critical2DKPZ.SmallScales.LocalMeasurePairingBound

/-! # Local measure representations contradict spatial growth -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped CompactlySupported Distributions ENNReal Topology

namespace Critical2DKPZ.SmallScales

/-- A distribution whose unit-kernel dilates grow along a vanishing sequence at almost every
point cannot agree locally with a difference of locally finite measures. -/
theorem no_local_measure_representation_of_eventually_large_dilates
    (T : Distr) (ε : ℕ → ℝ)
    (hεlim : Tendsto ε atTop (nhdsWithin 0 (Set.Ioi 0)))
    (hεpos : ∀ k, 0 < ε k)
    (hGrowth : ∀ᵐ x ∂(volume : Measure Plane),
      ∀ᶠ k : ℕ in atTop, (k : ℝ) <
        |T (Analysis.Sobolev.unitMassTestFn.dilate (ε k) x)|) :
    ∀ U : Set Plane, IsOpen U → U.Nonempty → ¬ ∃ μ ν : Measure Plane,
      (∀ K, IsCompact K → K ⊆ U → μ K < ⊤ ∧ ν K < ⊤) ∧
      ∀ φ : TestFn, tsupport φ ⊆ U →
        T φ = (∫ y, φ y ∂μ) - ∫ y, φ y ∂ν := by
  intro U hU hUnonempty hRepresentation
  obtain ⟨μ, ν, hLocal, hRep⟩ := hRepresentation
  obtain ⟨x₀, hx₀⟩ := hUnonempty
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
  let K : Set Plane := Metric.closedBall x₀ (r / 2)
  have hKU : K ⊆ U := by
    intro y hy
    apply hball
    have hy' : dist y x₀ ≤ r / 2 := by
      simpa [K, Metric.mem_closedBall] using hy
    rw [Metric.mem_ball]
    linarith
  have hKcompact : IsCompact K := by
    dsimp [K]
    exact isCompact_closedBall x₀ (r / 2)
  have hμK := hLocal K hKcompact hKU
  have hsumK : (μ + ν) K < ⊤ := by
    rw [Measure.add_apply μ ν K]
    exact ENNReal.add_lt_top.mpr ⟨hμK.1, hμK.2⟩
  let η : Measure Plane := (μ + ν).restrict K
  have hηlocallyFinite : IsLocallyFiniteMeasure η := by
    refine ⟨fun _ => ⟨Set.univ, univ_mem, ?_⟩⟩
    rw [Measure.restrict_apply_univ]
    exact hsumK
  have hdiff := @ae_exists_measure_closedBall_le_sq η hηlocallyFinite
  let V : Set Plane := Metric.ball x₀ (r / 4)
  have hVpos : volume V ≠ 0 := by
    apply ne_of_gt
    exact Metric.measure_ball_pos volume x₀ (by linarith)
  have hGood : ∀ᵐ x ∂(volume : Measure Plane),
      (∀ᶠ k : ℕ in atTop, (k : ℝ) <
        |T (Analysis.Sobolev.unitMassTestFn.dilate (ε k) x)|) ∧
      ∃ C : ℝ, ∀ᶠ δ in nhdsWithin 0 (Set.Ioi 0),
        (η (Metric.closedBall x δ)).toReal ≤ C * δ ^ 2 :=
    hGrowth.and hdiff
  have hGoodV : ∀ᵐ x ∂(volume.restrict V),
      (∀ᶠ k : ℕ in atTop, (k : ℝ) <
        |T (Analysis.Sobolev.unitMassTestFn.dilate (ε k) x)|) ∧
      ∃ C : ℝ, ∀ᶠ δ in nhdsWithin 0 (Set.Ioi 0),
        (η (Metric.closedBall x δ)).toReal ≤ C * δ ^ 2 :=
    ae_restrict_of_ae hGood
  obtain ⟨x, hxV, hxGrowth, hxDiff⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hVpos hGoodV
  obtain ⟨C, hC⟩ := hxDiff
  let C' : ℝ := max C 0
  have hεto0 : Tendsto ε atTop (nhds 0) := hεlim.mono_right nhdsWithin_le_nhds
  have hεsmall : ∀ᶠ k : ℕ in atTop, ε k < r / 8 := by
    have h := hεto0.eventually (Iio_mem_nhds (by linarith : 0 < r / 8))
    simpa only [Set.mem_Iio] using h
  have hscaled0 : Tendsto (fun k : ℕ => 2 * ε k) atTop (nhds 0) := by
    have hcont : Continuous (fun z : ℝ => 2 * z) := continuous_const.mul continuous_id
    change Tendsto ((fun z : ℝ => 2 * z) ∘ ε) atTop (nhds 0)
    simpa only [mul_zero] using hcont.continuousAt.tendsto.comp hεto0
  have hscaledpos : ∀ᶠ k : ℕ in atTop, 0 < 2 * ε k :=
    Filter.Eventually.of_forall fun k => mul_pos (by norm_num) (hεpos k)
  have hscaled : Tendsto (fun k : ℕ => 2 * ε k) atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hscaled0, hscaledpos⟩
  have hmassEvent : ∀ᶠ k : ℕ in atTop,
      (η (Metric.closedBall x (2 * ε k))).toReal ≤ C' * (2 * ε k) ^ 2 := by
    filter_upwards [hscaled.eventually hC] with k hk
    exact hk.trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (sq_nonneg (2 * ε k)))
  have hxCenter : dist x x₀ < r / 4 := by
    simpa [V, Metric.mem_ball] using hxV
  have hBsubK (k : ℕ) (hεk : ε k < r / 8) :
      Metric.closedBall x (2 * ε k) ⊆ K := by
    intro y hy
    have hyx : dist y x ≤ 2 * ε k := by
      simpa [Metric.mem_closedBall] using hy
    change dist y x₀ ≤ r / 2
    calc
      dist y x₀ ≤ dist y x + dist x x₀ := dist_triangle _ _ _
      _ ≤ 2 * ε k + r / 4 := add_le_add hyx hxCenter.le
      _ ≤ r / 2 := by linarith
  have hkernelNonneg (y : Plane) :
      0 ≤ Analysis.Sobolev.unitMassTestFn y :=
    Analysis.Sobolev.unitMassTestFn_nonneg y
  let M : ℝ := (∫ z : Plane, Critical2DKPZ.localizer 0 z)⁻¹
  have hkernelBound (y : Plane) : Analysis.Sobolev.unitMassTestFn y ≤ M := by
    exact unitMassTestFn_le y
  have hMnonneg : 0 ≤ M := le_trans (hkernelNonneg 0) (hkernelBound 0)
  have hC'nonneg : 0 ≤ C' := le_max_right C 0
  have hPairBound (k : ℕ) (hεk : ε k < r / 8)
      (hmass : (η (Metric.closedBall x (2 * ε k))).toReal ≤ C' * (2 * ε k) ^ 2) :
      |T (Analysis.Sobolev.unitMassTestFn.dilate (ε k) x)| ≤ 4 * M * C' := by
    let B : Set Plane := Metric.closedBall x (2 * ε k)
    have hBK : B ⊆ K := hBsubK k hεk
    have hBU : B ⊆ U := hBK.trans hKU
    have hBcompact : IsCompact B := by
      dsimp [B]
      exact isCompact_closedBall x (2 * ε k)
    have hBmeas : MeasurableSet B := hBcompact.isClosed.measurableSet
    have hSupportB :
        tsupport (Analysis.Sobolev.unitMassTestFn.dilate (ε k) x) ⊆ B := by
      exact tsupport_dilate_subset_closedBall Analysis.Sobolev.unitMassTestFn 2
        (ε k) x tsupport_unitMassTestFn_subset (hεpos k)
    have hSupportU :
        tsupport (Analysis.Sobolev.unitMassTestFn.dilate (ε k) x) ⊆ U :=
      hSupportB.trans hBU
    have hμB := hLocal B hBcompact hBU
    have hηB : η B = (μ + ν) B := by
      dsimp [η, B]
      rw [Measure.restrict_apply hBmeas]
      rw [Measure.add_apply μ ν (Metric.closedBall x (2 * ε k) ∩ K)]
      rw [Set.inter_eq_left.mpr hBK]
    have hrep := hRep (Analysis.Sobolev.unitMassTestFn.dilate (ε k) x) hSupportU
    have hlocalBound := abs_pairing_le_of_local_measure_representation
      T μ ν x (ε := ε k) Analysis.Sobolev.unitMassTestFn M hkernelNonneg
      hkernelBound B hBmeas hSupportB hμB.1 hμB.2 hrep
    calc
      |T (Analysis.Sobolev.unitMassTestFn.dilate (ε k) x)| ≤
          (ε k)⁻¹ ^ 2 * M * ((μ + ν) B).toReal := hlocalBound
      _ ≤ (ε k)⁻¹ ^ 2 * M * (C' * (2 * ε k) ^ 2) := by
        rw [← hηB]
        exact mul_le_mul_of_nonneg_left hmass
          (mul_nonneg (sq_nonneg ((ε k)⁻¹)) hMnonneg)
      _ = 4 * M * C' := by
        rw [← mul_assoc]
        field_simp [ne_of_gt (hεpos k)]
        ring
  have hlarge : ∀ᶠ k : ℕ in atTop, 4 * M * C' < (k : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop (4 * M * C')
  have hAll : ∀ᶠ k : ℕ in atTop,
      (k : ℝ) < |T (Analysis.Sobolev.unitMassTestFn.dilate (ε k) x)| ∧
      ε k < r / 8 ∧
      (η (Metric.closedBall x (2 * ε k))).toReal ≤ C' * (2 * ε k) ^ 2 ∧
      4 * M * C' < (k : ℝ) := by
    filter_upwards [hxGrowth, hεsmall, hmassEvent, hlarge] with k hgrowth hεk hmass hklarge
    exact ⟨hgrowth, hεk, hmass, hklarge⟩
  obtain ⟨k, hk⟩ := hAll.exists
  rcases hk with ⟨hpointGrowth, hεk, hmass, hklarge⟩
  have hupper := hPairBound k hεk hmass
  exact (lt_irrefl (4 * M * C'))
    (lt_trans hklarge (lt_of_lt_of_le hpointGrowth hupper))

end Critical2DKPZ.SmallScales

end
