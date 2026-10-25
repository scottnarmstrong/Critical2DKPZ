/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.JointConvergence.HeatStartProfileApprox
public import Critical2DKPZ.JointConvergence.HeatStartLogTails
public import Critical2DKPZ.JointConvergence.Approximation
public import Critical2DKPZ.JointConvergence.MomentConvergence
public import Critical2DKPZ.JointConvergence.HeatKernelCellApprox
public import Critical2DKPZ.Smoothing.ParityHelpers
public import Critical2DKPZ.SHF.Positivity.HeatStartMean
public import Critical2DKPZ.Polymer.ProbabilityProfiles
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Tactic

/-! # Joint heat-start log convergence -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open Critical2DKPZ.SHF.Limit
open scoped BigOperators BoundedContinuousFunction ENNReal Topology

namespace Critical2DKPZ.JointConvergence

private theorem tendstoInDistribution_of_approx_of_limit {k : ℕ} {Ω' Ω : Type*}
    [MeasurableSpace Ω'] [MeasurableSpace Ω] {μ : ℕ → Measure Ω'} {P : Measure Ω}
    [∀ N, IsProbabilityMeasure (μ N)] [IsProbabilityMeasure P]
    (X : ℕ → Ω' → Fin k → ℝ) (Y : ℕ → ℕ → Ω' → Fin k → ℝ)
    (Yl : ℕ → Ω → Fin k → ℝ) (L : Ω → Fin k → ℝ)
    (hY : ∀ j, TendstoInDistribution (fun N => Y j N) atTop (Yl j) μ P)
    (hYl : TendstoInDistribution Yl atTop L (fun _ => P) P)
    (hXY : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ᶠ N in atTop,
      ∫⁻ ω, ENNReal.ofReal ‖X N ω - Y j N ω‖ ∂(μ N) ≤ ENNReal.ofReal ε)
    (hXm : ∀ N, AEMeasurable (X N) (μ N)) (hLm : AEMeasurable L P) :
    TendstoInDistribution X atTop L μ P := by
  refine ⟨hXm, hLm, ?_⟩
  refine (tendsto_iff_forall_lipschitz_integral_tendsto (Ω := Fin k → ℝ)).2 ?_
  intro F hFbounded hFlipschitz
  obtain ⟨K, hF⟩ := hFlipschitz
  obtain ⟨M, hFbounded'⟩ := hFbounded
  have htest : Tendsto (fun N => ∫ ω, F (X N ω) ∂(μ N)) atTop
      (𝓝 (∫ ω, F (L ω) ∂P)) := by
    rw [Metric.tendsto_nhds]
    intro e he
    let η : ℝ := e / (6 * ((K : ℝ) + 1))
    have hη : 0 < η := by dsimp [η]; positivity
    have hYLtest : Tendsto (fun j => ∫ ω, F (Yl j ω) ∂P) atTop
        (𝓝 (∫ ω, F (L ω) ∂P)) := by
      have h := (tendsto_iff_forall_lipschitz_integral_tendsto.mp hYl.tendsto)
        F ⟨M, hFbounded'⟩ ⟨K, hF⟩
      have hmap (j : ℕ) :
          (∫ z, F z ∂P.map (Yl j)) = ∫ ω, F (Yl j ω) ∂P :=
        integral_map (hYl.forall_aemeasurable j)
          (hF.continuous.measurable.aestronglyMeasurable)
      have hmapLim : (∫ z, F z ∂P.map L) = ∫ ω, F (L ω) ∂P :=
        integral_map hYl.aemeasurable_limit
          (hF.continuous.measurable.aestronglyMeasurable)
      simpa only [ProbabilityMeasure.coe_mk, hmap, hmapLim] using h
    have hclose : ∀ᶠ j in atTop,
        |(∫ ω, F (Yl j ω) ∂P) - ∫ ω, F (L ω) ∂P| < e / 3 := by
      have h := (Metric.tendsto_nhds.mp hYLtest) (e / 3) (by positivity)
      simpa only [Real.dist_eq] using h
    obtain ⟨j, hjclose, hjXY⟩ := (hclose.and (hXY η hη)).exists
    have hYtest : Tendsto (fun N => ∫ ω, F (Y j N ω) ∂(μ N)) atTop
        (𝓝 (∫ ω, F (Yl j ω) ∂P)) := by
      have hmap := (tendsto_iff_forall_lipschitz_integral_tendsto.mp (hY j).tendsto)
        F ⟨M, hFbounded'⟩ ⟨K, hF⟩
      have hmapN (N : ℕ) :
          (∫ z, F z ∂(μ N).map (Y j N)) = ∫ ω, F (Y j N ω) ∂(μ N) :=
        integral_map ((hY j).forall_aemeasurable N)
          (hF.continuous.measurable.aestronglyMeasurable)
      have hmapLim :
          (∫ z, F z ∂P.map (Yl j)) = ∫ ω, F (Yl j ω) ∂P :=
        integral_map (hY j).aemeasurable_limit
          (hF.continuous.measurable.aestronglyMeasurable)
      simpa only [ProbabilityMeasure.coe_mk, hmapN, hmapLim] using hmap
    have hfirst : ∀ᶠ N in atTop,
        |(∫ ω, F (X N ω) ∂(μ N)) - (∫ ω, F (Y j N ω) ∂(μ N))| ≤ (K : ℝ) * η := by
      filter_upwards [hjXY] with N hN
      exact integral_lipschitz_comp_sub_le (μ N) (hXm N) ((hY j).forall_aemeasurable N)
        hF ⟨M, hFbounded'⟩ hη.le hN
    have hmiddle : ∀ᶠ N in atTop,
        |(∫ ω, F (Y j N ω) ∂(μ N)) - (∫ ω, F (Yl j ω) ∂P)| < e / 3 := by
      simpa only [Real.dist_eq] using
        (Metric.tendsto_nhds.mp hYtest (e / 3) (by positivity))
    have hsum : (K : ℝ) * η + 2 * (e / 3) < e := by
      dsimp [η]
      have hKnonneg : 0 ≤ (K : ℝ) := NNReal.coe_nonneg K
      have hdenPos : 0 < 6 * ((K : ℝ) + 1) := by positivity
      have hsmall : (K : ℝ) * (e / (6 * ((K : ℝ) + 1))) ≤ e / 6 := by
        calc
          (K : ℝ) * (e / (6 * ((K : ℝ) + 1))) =
              ((K : ℝ) * e) / (6 * ((K : ℝ) + 1)) := by ring
          _ ≤ e / 6 := (div_le_iff₀ hdenPos).2 (by nlinarith)
      nlinarith [hsmall]
    filter_upwards [hfirst, hmiddle] with N hfirstN hmiddleN
    calc
      |(∫ ω, F (X N ω) ∂(μ N)) - (∫ ω, F (L ω) ∂P)| ≤
          |(∫ ω, F (X N ω) ∂(μ N)) - (∫ ω, F (Y j N ω) ∂(μ N))| +
            |(∫ ω, F (Y j N ω) ∂(μ N)) - (∫ ω, F (Yl j ω) ∂P)| +
              |(∫ ω, F (Yl j ω) ∂P) - (∫ ω, F (L ω) ∂P)| := by
        calc
          _ ≤ |(∫ ω, F (X N ω) ∂(μ N)) - (∫ ω, F (Yl j ω) ∂P)| +
              |(∫ ω, F (Yl j ω) ∂P) - (∫ ω, F (L ω) ∂P)| := abs_sub_le _ _ _
          _ ≤ _ := by gcongr; exact abs_sub_le _ _ _
      _ ≤ (K : ℝ) * η + 2 * (e / 3) := by linarith [hfirstN, hmiddleN, hjclose]
      _ < e := hsum
  have hmapX (N : ℕ) :
      (∫ z, F z ∂(μ N).map (X N)) = ∫ ω, F (X N ω) ∂(μ N) :=
    integral_map (hXm N) (hF.continuous.measurable.aestronglyMeasurable)
  have hmapLim : (∫ z, F z ∂P.map L) = ∫ ω, F (L ω) ∂P :=
    integral_map hLm (hF.continuous.measurable.aestronglyMeasurable)
  simpa only [ProbabilityMeasure.coe_mk, hmapX, hmapLim] using htest

/-- The logarithm of the finite-scale polymer profile with heat-start width `δ`. -/
def heatStartLogProfile (ϑ : ℝ) (N : ℕ) (s T δ : ℝ) (x : Plane)
    (h₀ : Plane →ᵇ ℝ) : Disorder → ℝ :=
  fun ω => Real.log (profileP2Fun (criticalBeta ϑ N)
    (evenCeil (N * s)) (evenCeil (N * T))
    (fun w => srwKernel (evenCeil (N * δ)) (w - latticePoint N x))
    (cellAverage N fun y => Real.exp (h₀ y)) ω)

/-- The uniform exponential logarithmic tails give a second-moment bound, uniformly over the
spatial center at each fixed heat-start parameter. -/
theorem heatStartLogProfile_square_bound (ϑ : ℝ) {s T δ : ℝ}
    (hs : 0 ≤ s) (hsT : s < T) (hδ : 0 < δ) (h₀ : Plane →ᵇ ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ x : Plane,
        Integrable (fun ω => |heatStartLogProfile ϑ N s T δ x h₀ ω| ^ 2) disorderLaw ∧
        ∫ ω, |heatStartLogProfile ϑ N s T δ x h₀ ω| ^ 2 ∂disorderLaw ≤
          C * 2 * Real.Gamma 2 := by
  obtain ⟨C, htail⟩ :=
    measure_abs_log_profileP2Fun_heatStart_gt_le ϑ hs hsT hδ ‖h₀‖
  have hC : 0 ≤ C := by
    obtain ⟨N, hN⟩ := htail.exists
    have hbound := hN 0 h₀ le_rfl 0 le_rfl
    have hmeasure : 0 ≤ (disorderLaw {ω | 0 <
        |heatStartLogProfile ϑ N s T δ 0 h₀ ω|}).toReal := ENNReal.toReal_nonneg
    change 0 ≤ (disorderLaw {ω | 0 <
        |Real.log (profileP2Fun (criticalBeta ϑ N) (evenCeil (N * s))
          (evenCeil (N * T))
          (fun w => srwKernel (evenCeil (N * δ)) (w - latticePoint N 0))
          (cellAverage N fun y => Real.exp (h₀ y)) ω)|}).toReal at hmeasure
    simpa [Real.exp_zero, mul_one] using hmeasure.trans hbound
  refine ⟨C, hC, ?_⟩
  filter_upwards [htail] with N htailN
  intro x
  let f : Disorder → ℝ := heatStartLogProfile ϑ N s T δ x h₀
  have hf : AEMeasurable f disorderLaw := by
    dsimp [f, heatStartLogProfile]
    exact (Polymer.measurable_profileP2Fun (criticalBeta ϑ N)
      (evenCeil (N * s)) (evenCeil (N * T))
      (fun w => srwKernel (evenCeil (N * δ)) (w - latticePoint N x))
      (cellAverage N fun y => Real.exp (h₀ y))).log.aemeasurable
  have htailf : ∀ u : ℝ, 0 ≤ u →
      (disorderLaw {ω | u < |f ω|}).toReal ≤ C * Real.exp (-u) := by
    intro u hu
    simpa [f, heatStartLogProfile] using htailN x h₀ le_rfl u hu
  have hmoment := integrable_rpow_of_exp_tail hf hC (by norm_num : 0 < (2 : ℝ)) htailf
  constructor
  · simpa [f, heatStartLogProfile, Real.rpow_two] using hmoment.1
  · simpa [f, heatStartLogProfile, Real.rpow_two] using hmoment.2

/-- Every positive power of a heat-start logarithm has a uniform bound at fixed width. -/
theorem heatStartLogProfile_rpow_bound (ϑ : ℝ) {s T δ : ℝ}
    (hs : 0 ≤ s) (hsT : s < T) (hδ : 0 < δ) (x : Plane) (h₀ : Plane →ᵇ ℝ)
    {q : ℝ} (hq : 0 < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω => |heatStartLogProfile ϑ N s T δ x h₀ ω| ^ q) disorderLaw ∧
      ∫ ω, |heatStartLogProfile ϑ N s T δ x h₀ ω| ^ q ∂disorderLaw ≤ C * q * Real.Gamma q := by
  obtain ⟨C, htail⟩ :=
    measure_abs_log_profileP2Fun_heatStart_gt_le ϑ hs hsT hδ ‖h₀‖
  have hC : 0 ≤ C := by
    obtain ⟨N, hN⟩ := htail.exists
    have hbound := hN x h₀ le_rfl 0 le_rfl
    have hmeasure : 0 ≤ (disorderLaw {ω | 0 <
        |heatStartLogProfile ϑ N s T δ x h₀ ω|}).toReal := ENNReal.toReal_nonneg
    change 0 ≤ (disorderLaw {ω | 0 <
        |Real.log (profileP2Fun (criticalBeta ϑ N) (evenCeil (N * s))
          (evenCeil (N * T))
          (fun w => srwKernel (evenCeil (N * δ)) (w - latticePoint N x))
          (cellAverage N fun y => Real.exp (h₀ y)) ω)|}).toReal at hmeasure
    simpa [Real.exp_zero, mul_one] using hmeasure.trans hbound
  refine ⟨C, hC, ?_⟩
  filter_upwards [htail] with N htailN
  let f : Disorder → ℝ := heatStartLogProfile ϑ N s T δ x h₀
  have hf : AEMeasurable f disorderLaw := by
    dsimp [f, heatStartLogProfile]
    exact (Polymer.measurable_profileP2Fun (criticalBeta ϑ N)
      (evenCeil (N * s)) (evenCeil (N * T))
      (fun w => srwKernel (evenCeil (N * δ)) (w - latticePoint N x))
      (cellAverage N fun y => Real.exp (h₀ y))).log.aemeasurable
  have htailf : ∀ u : ℝ, 0 ≤ u →
      (disorderLaw {ω | u < |f ω|}).toReal ≤ C * Real.exp (-u) := by
    intro u hu
    simpa [f, heatStartLogProfile] using htailN x h₀ le_rfl u hu
  have hmoment := integrable_rpow_of_exp_tail hf hC hq htailf
  exact ⟨hmoment.1, by simpa [f, heatStartLogProfile] using hmoment.2⟩

/-- A heat-start log with width `δ` has high moments growing logarithmically in
`1 + |log δ|`, uniformly in the spatial center and the eventual lattice scale. -/
theorem heatStartLogProfile_rpow_log_width_bound (ϑ : ℝ) {t T δ₁ : ℝ}
    (ht : 0 ≤ t) (htT : t < T) (hδ₁ : 0 < δ₁) (hδ₁T : δ₁ ≤ T - t)
    (h₀ : Plane →ᵇ ℝ) (H : ℝ) (hH : ‖h₀‖ ≤ H) {q : ℝ} (hq : 0 < q) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ δ ∈ Set.Ioo 0 δ₁, ∀ᶠ N : ℕ in atTop, ∀ x : Plane,
      Integrable (fun ω => |heatStartLogProfile ϑ N (t + δ) T δ x h₀ ω| ^ q) disorderLaw ∧
      ∫ ω, |heatStartLogProfile ϑ N (t + δ) T δ x h₀ ω| ^ q ∂disorderLaw ≤
        M * (1 + Real.log (1 + |Real.log δ|)) ^ q := by
  obtain ⟨C₀, hC₀, hTail⟩ := measure_abs_log_profileP2Fun_heatStart_gt_le_log_width
    ϑ ht htT hδ₁ hδ₁T H
  let Cbar : ℝ := max C₀ 1
  let D : ℝ := Real.log Cbar
  let M : ℝ := 2 ^ q * ((D + 1) ^ q + q * Real.Gamma q)
  have hCbar : 1 ≤ Cbar := le_max_right _ _
  have hCbarpos : 0 < Cbar := lt_of_lt_of_le (by norm_num) hCbar
  have hD : 0 ≤ D := Real.log_nonneg hCbar
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  refine ⟨M, hM, ?_⟩
  intro δ hδ
  let L : ℝ := |Real.log δ|
  let B : ℝ := 1 + Real.log (1 + L)
  let Cδ : ℝ := Cbar * (1 + L)
  let R : ℝ := Real.log Cδ
  have hL : 0 ≤ L := abs_nonneg _
  have hBlog : 0 ≤ Real.log (1 + L) := Real.log_nonneg (by linarith)
  have hB : 1 ≤ B := by dsimp [B]; linarith
  have hCδ : 1 ≤ Cδ := by dsimp [Cδ]; nlinarith [hCbar, hL]
  have hR : R = D + Real.log (1 + L) := by
    dsimp [R, Cδ, D]
    rw [Real.log_mul hCbarpos.ne' (by positivity)]
  have hRB : R ≤ (D + 1) * B := by
    rw [hR]
    dsimp [B]
    have hcross : 0 ≤ D * Real.log (1 + L) := mul_nonneg hD hBlog
    nlinarith [hcross]
  have hRnonneg : 0 ≤ R := Real.log_nonneg hCδ
  have hRpow : R ^ q ≤ (D + 1) ^ q * B ^ q := by
    calc
      R ^ q ≤ ((D + 1) * B) ^ q := Real.rpow_le_rpow hRnonneg hRB hq.le
      _ = (D + 1) ^ q * B ^ q := by
        rw [Real.mul_rpow (by linarith : 0 ≤ D + 1) (by linarith : 0 ≤ B)]
  have hBpow : 1 ≤ B ^ q := Real.one_le_rpow hB hq.le
  have hgamma : 0 ≤ q * Real.Gamma q := mul_nonneg hq.le (Real.Gamma_pos_of_pos hq).le
  have hgammaBound : q * Real.Gamma q ≤ q * Real.Gamma q * B ^ q := by
    calc
      q * Real.Gamma q = (q * Real.Gamma q) * 1 := by ring
      _ ≤ (q * Real.Gamma q) * B ^ q := mul_le_mul_of_nonneg_left hBpow hgamma
  have hMomentBound (N : ℕ) (x : Plane)
      (hMoment : Integrable (fun ω => |heatStartLogProfile ϑ N (t + δ) T δ x h₀ ω| ^ q)
        disorderLaw ∧
        ∫ ω, |heatStartLogProfile ϑ N (t + δ) T δ x h₀ ω| ^ q ∂disorderLaw ≤
          2 ^ q * (R ^ q + q * Real.Gamma q)) :
      ∫ ω, |heatStartLogProfile ϑ N (t + δ) T δ x h₀ ω| ^ q ∂disorderLaw ≤
        M * B ^ q := by
    calc
      _ ≤ 2 ^ q * (R ^ q + q * Real.Gamma q) := hMoment.2
      _ ≤ 2 ^ q * ((D + 1) ^ q * B ^ q +
          (q * Real.Gamma q) * B ^ q) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) q)
        exact add_le_add hRpow hgammaBound
      _ = M * B ^ q := by dsimp [M]; ring
  have hCδbound : C₀ * (1 + L) ≤ Cδ := by
    dsimp [Cδ, Cbar]
    exact mul_le_mul_of_nonneg_right (le_max_left C₀ 1) (by linarith)
  have hTailδ := hTail δ hδ
  filter_upwards [hTailδ] with N hTailN
  intro x
  let f : Disorder → ℝ := heatStartLogProfile ϑ N (t + δ) T δ x h₀
  have hf : AEMeasurable f disorderLaw := by
    dsimp [f, heatStartLogProfile]
    exact (Polymer.measurable_profileP2Fun (criticalBeta ϑ N)
      (evenCeil (N * (t + δ))) (evenCeil (N * T))
      (fun w => srwKernel (evenCeil (N * δ)) (w - latticePoint N x))
      (cellAverage N fun y => Real.exp (h₀ y))).log.aemeasurable
  have htailf : ∀ u : ℝ, 0 ≤ u →
      (disorderLaw {ω | u < |f ω|}).toReal ≤ Cδ * Real.exp (-u) := by
    intro u hu
    have h := hTailN x h₀ hH u hu
    dsimp [f, heatStartLogProfile, Cδ, L]
    calc
      _ ≤ C₀ * (1 + |Real.log δ|) * Real.exp (-u) := h
      _ ≤ Cδ * Real.exp (-u) :=
        mul_le_mul_of_nonneg_right hCδbound (Real.exp_nonneg _)
  have hmoment := integrable_rpow_of_exp_tail_log_coefficient hf hCδ hq htailf
  have hmomentBound' := hMomentBound N x hmoment
  exact ⟨hmoment.1, by simpa [B, L] using hmomentBound'⟩

private def heatStartLogCut (R y : ℝ) : ℝ := max (-R) (min y R)

private theorem continuous_heatStartLogCut (R : ℝ) : Continuous (heatStartLogCut R) := by
  change Continuous (fun y : ℝ => max (-R) (min y R))
  fun_prop

private theorem heatStartLogCut_eq_self (R y : ℝ) (hy : |y| ≤ R) :
    heatStartLogCut R y = y := by
  dsimp [heatStartLogCut]
  rw [min_eq_left (abs_le.mp hy).2, max_eq_right (abs_le.mp hy).1]

private theorem heatStartLogCut_tendsto (y : ℝ) :
    Tendsto (fun j : ℕ => heatStartLogCut ((j : ℝ) + 1) y) atTop (𝓝 y) := by
  have hj : ∀ᶠ j : ℕ in atTop, |y| ≤ (j : ℝ) + 1 := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually
      (eventually_ge_atTop (|y|))] with j hj
    linarith
  have heq : ∀ᶠ j : ℕ in atTop, heatStartLogCut ((j : ℝ) + 1) y = y :=
    hj.mono fun j hj => heatStartLogCut_eq_self ((j : ℝ) + 1) y (by linarith)
  exact tendsto_const_nhds.congr' (heq.mono fun j hj => hj.symm)

/-- Continuous logarithm clamps of a positive finite vector converge in law to its logarithm.
The limiting logarithm is assumed measurable, as supplied by SHF positivity. -/
private theorem heatStart_logCut_tendstoInDistribution {k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {V : Ω → Fin k → ℝ}
    (hlog : AEMeasurable (fun ω i => Real.log (V ω i)) P)
    (hpos : ∀ i, ∀ᵐ ω ∂P, 0 < V ω i) :
    TendstoInDistribution
      (fun (j : ℕ) ω i => heatStartLogCut ((j : ℝ) + 1) (Real.log (V ω i)))
      atTop (fun ω i => Real.log (V ω i)) (fun _ => P) P := by
  have hXm : ∀ j : ℕ, AEMeasurable
      (fun ω i => heatStartLogCut ((j : ℝ) + 1) (Real.log (V ω i))) P := by
    intro j
    apply aemeasurable_pi_iff.mpr
    intro i
    have hcoord : AEMeasurable (fun ω => Real.log (V ω i)) P :=
      (aemeasurable_pi_iff.mp hlog) i
    exact (continuous_heatStartLogCut ((j : ℝ) + 1)).measurable.comp_aemeasurable hcoord
  have hlim : AEMeasurable (fun ω i => Real.log (V ω i)) P :=
    hlog
  have hae : ∀ᵐ ω ∂P, Tendsto
      (fun j : ℕ => fun i =>
        heatStartLogCut ((j : ℝ) + 1) (Real.log (V ω i))) atTop
      (𝓝 (fun i => Real.log (V ω i))) := by
    filter_upwards [ae_all_iff.mpr hpos] with ω hω
    apply tendsto_pi_nhds.mpr
    intro i
    exact heatStartLogCut_tendsto (Real.log (V ω i))
  exact tendstoInDistribution_of_ae_tendsto hXm hlim hae

/-- A continuous logarithm clamp, defined on the whole real line. -/
def heatStartLogClamp (R x : ℝ) : ℝ :=
  Real.log (max (Real.exp (-R)) (min x (Real.exp R)))

/-- The logarithm clamp is continuous, including at both truncation points. -/
theorem heatStartLogClamp_continuous (R : ℝ) :
    Continuous (heatStartLogClamp R) := by
  let c : ℝ → ℝ := fun x => max (Real.exp (-R)) (min x (Real.exp R))
  have hc : Continuous c := by dsimp [c]; fun_prop
  have hcpos (x : ℝ) : c x ≠ 0 := by
    apply ne_of_gt
    exact (Real.exp_pos _).trans_le (le_max_left _ _)
  have hlog : Continuous (fun x : ℝ => Real.log (c x)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (Real.continuousAt_log (hcpos x)).comp (hc.continuousAt)
  change Continuous (fun x : ℝ => Real.log (c x))
  exact hlog

private theorem heatStartLogClamp_eq_logTrunc (R x : ℝ) (hR : 0 ≤ R) (hx : 0 < x) :
    heatStartLogClamp R x = logTrunc R x := by
  have hfloorUpper : Real.exp (-R) ≤ Real.exp R :=
    Real.exp_le_exp.mpr (by linarith)
  by_cases hlo : x < Real.exp (-R)
  · have hlog : Real.log x < -R := by
      calc
        Real.log x < Real.log (Real.exp (-R)) :=
          Real.log_lt_log hx hlo
        _ = -R := Real.log_exp _
    rw [heatStartLogClamp, min_eq_left (le_trans (le_of_lt hlo) hfloorUpper),
      max_eq_left (le_of_lt hlo), Real.log_exp]
    rw [logTrunc, min_eq_left (le_trans hlog.le (by linarith : -R ≤ R)),
      max_eq_left hlog.le]
  · by_cases hupp : Real.exp R < x
    · have hlog : R < Real.log x := by
        calc
          R = Real.log (Real.exp R) := (Real.log_exp R).symm
          _ < Real.log x := Real.log_lt_log (Real.exp_pos _) hupp
      rw [heatStartLogClamp, min_eq_right (le_of_lt hupp),
        max_eq_right hfloorUpper, Real.log_exp]
      rw [logTrunc, min_eq_right hlog.le, max_eq_right (by linarith)]
    · have hlo' : Real.exp (-R) ≤ x := le_of_not_gt hlo
      have hupp' : x ≤ Real.exp R := le_of_not_gt hupp
      have hloglo : -R ≤ Real.log x := by
        calc
          -R = Real.log (Real.exp (-R)) := (Real.log_exp _).symm
          _ ≤ Real.log x := Real.log_le_log (Real.exp_pos _) hlo'
      have hloghi : Real.log x ≤ R := by
        calc
          Real.log x ≤ Real.log (Real.exp R) := Real.log_le_log hx hupp'
          _ = R := Real.log_exp _
      rw [heatStartLogClamp, min_eq_left hupp', max_eq_right hlo']
      rw [logTrunc, min_eq_left hloghi, max_eq_right hloglo]

/-- The logarithm clamp has Lipschitz constant `exp R` when `R` is nonnegative. -/
theorem heatStartLogClamp_lipschitz (R : ℝ) (hR : 0 ≤ R) :
    LipschitzWith ⟨Real.exp R, Real.exp_nonneg R⟩ (heatStartLogClamp R) := by
  let floor : ℝ := Real.exp (-R)
  let ceiling : ℝ := Real.exp R
  let c : ℝ → ℝ := fun x => max floor (min x ceiling)
  have hfloorCeiling : floor ≤ ceiling := by
    dsimp [floor, ceiling]
    exact Real.exp_le_exp.mpr (by linarith)
  have hc : LipschitzWith 1 c := by
    dsimp [c, floor, ceiling]
    exact (LipschitzWith.id.min_const _).const_max _
  have hcBounds (x : ℝ) : floor ≤ c x ∧ c x ≤ ceiling := by
    constructor
    · exact le_max_left _ _
    · exact max_le hfloorCeiling (min_le_right _ _)
  have hcPos (x : ℝ) : 0 < c x :=
    (Real.exp_pos _).trans_le (hcBounds x).1
  have hInv_of_lower {u : ℝ} (hu : floor ≤ u) : u⁻¹ ≤ Real.exp R := by
    have h := one_div_le_one_div_of_le (Real.exp_pos (-R)) hu
    simpa only [one_div, Real.exp_neg, floor, inv_inv] using h
  have hcxy (x y : ℝ) : |c x - c y| ≤ |x - y| := by
    have h := hc.dist_le_mul x y
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using h
  have hlogPair (x y : ℝ) :
      |Real.log (c x) - Real.log (c y)| ≤ Real.exp R * |x - y| := by
    have hforward {u v : ℝ} (hu : floor ≤ u) (hu' : u ≤ ceiling)
        (hv : floor ≤ v) (hv' : v ≤ ceiling) (huv : u ≤ v) :
        Real.log v - Real.log u ≤ Real.exp R * (v - u) := by
      have hu0 : 0 < u := (Real.exp_pos _).trans_le hu
      have hv0 : 0 < v := (Real.exp_pos _).trans_le hv
      have hlogdiv := Real.log_le_sub_one_of_pos (div_pos hv0 hu0)
      rw [Real.log_div hv0.ne' hu0.ne'] at hlogdiv
      have hratio : v / u - 1 = (v - u) * u⁻¹ := by
        field_simp
      rw [hratio] at hlogdiv
      calc
        Real.log v - Real.log u ≤ (v - u) * u⁻¹ := hlogdiv
        _ ≤ (v - u) * Real.exp R :=
          mul_le_mul_of_nonneg_left (hInv_of_lower hu) (sub_nonneg.mpr huv)
        _ = Real.exp R * (v - u) := by rw [mul_comm]
    have hu : floor ≤ c x := (hcBounds x).1
    have hu' : c x ≤ ceiling := (hcBounds x).2
    have hv : floor ≤ c y := (hcBounds y).1
    have hv' : c y ≤ ceiling := (hcBounds y).2
    by_cases hxy : c x ≤ c y
    · rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log (hcPos x) hxy))]
      calc
        _ = Real.log (c y) - Real.log (c x) := by ring
        _ ≤ Real.exp R * (c y - c x) :=
          hforward hu hu' hv hv' hxy
        _ ≤ Real.exp R * |c x - c y| :=
          mul_le_mul_of_nonneg_left (by
            rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
            nlinarith) (Real.exp_nonneg R)
        _ ≤ Real.exp R * |x - y| :=
          mul_le_mul_of_nonneg_left (hcxy x y) (Real.exp_nonneg R)
    · have hyx : c y ≤ c x := le_of_not_ge hxy
      have h := hforward hv hv' hu hu' hyx
      rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log (hcPos y) hyx))]
      have hxy' : |c x - c y| ≤ |x - y| := hcxy x y
      calc
        Real.log (c x) - Real.log (c y) ≤ Real.exp R * (c x - c y) := h
        _ ≤ Real.exp R * |c x - c y| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (Real.exp_nonneg R)
        _ ≤ Real.exp R * |x - y| :=
          mul_le_mul_of_nonneg_left hxy' (Real.exp_nonneg R)
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  change dist (Real.log (c x)) (Real.log (c y)) ≤ Real.exp R * dist x y
  simpa only [Real.dist_eq] using hlogPair x y

/-- For `R > 0` and `x > 0`, the clamp error satisfies `|log x - heatStartLogClamp R x| ≤ (log x)² /
R`. -/
theorem abs_log_sub_heatStartLogClamp_le (R x : ℝ) (hR : 0 < R) (hx : 0 < x) :
    |Real.log x - heatStartLogClamp R x| ≤ |Real.log x| ^ 2 / R := by
  rw [heatStartLogClamp_eq_logTrunc R x hR.le hx]
  by_cases hupper : R ≤ Real.log x
  · rw [logTrunc, min_eq_right hupper, max_eq_right (by linarith)]
    have hlogNonneg : 0 ≤ Real.log x := le_trans hR.le hupper
    rw [abs_of_nonneg (sub_nonneg.mpr hupper), abs_of_nonneg hlogNonneg]
    apply (le_div_iff₀ hR).2
    nlinarith [sq_nonneg (Real.log x - R)]
  · by_cases hlower : Real.log x ≤ -R
    · rw [logTrunc, min_eq_left (by linarith), max_eq_left hlower]
      have hdiff : Real.log x - -R = Real.log x + R := by ring
      rw [hdiff, abs_of_nonpos (by linarith : Real.log x + R ≤ 0)]
      have hlogNonpos : Real.log x ≤ 0 := le_trans hlower (by linarith)
      rw [abs_of_nonpos hlogNonpos]
      apply (le_div_iff₀ hR).2
      nlinarith [sq_nonneg (Real.log x + R)]
    · have hloglo : -R < Real.log x := lt_of_not_ge hlower
      have hloghi : Real.log x < R := lt_of_not_ge hupper
      rw [logTrunc, min_eq_left hloghi.le, max_eq_right hloglo.le]
      rw [sub_self, abs_zero]
      exact div_nonneg (sq_nonneg _) hR.le

/-- If `log f` is square integrable with `∫ (log f)² ≤ M`, the `L¹` clamp error of `log f` is at
most `M / R`. -/
theorem lintegral_abs_log_clamp_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {f : Ω → ℝ} (hf : AEMeasurable f P)
    (hpos : ∀ᵐ ω ∂P, 0 < f ω) (hlogSq : Integrable (fun ω => |Real.log (f ω)| ^ 2) P)
    {M R : ℝ} (hM : ∫ ω, |Real.log (f ω)| ^ 2 ∂P ≤ M) (hR : 0 < R) :
    ∫⁻ ω, ENNReal.ofReal |Real.log (f ω) - heatStartLogClamp R (f ω)| ∂P ≤
      ENNReal.ofReal (M / R) := by
  let g : Ω → ℝ := fun ω => |Real.log (f ω) - heatStartLogClamp R (f ω)|
  let q : Ω → ℝ := fun ω => |Real.log (f ω)| ^ 2
  have hgMeas : AEStronglyMeasurable g P := by
    have hraw : AEMeasurable
        (fun ω => Real.log (f ω) - heatStartLogClamp R (f ω)) P :=
      (Real.measurable_log.comp_aemeasurable hf).sub
        ((heatStartLogClamp_continuous R).measurable.comp_aemeasurable hf)
    change AEStronglyMeasurable (fun ω => |Real.log (f ω) - heatStartLogClamp R (f ω)|) P
    exact (measurable_abs.comp_aemeasurable hraw).aestronglyMeasurable
  have hmajor : Integrable (fun ω => R⁻¹ * q ω) P := by
    simpa only [q] using hlogSq.const_mul R⁻¹
  have hpoint : ∀ᵐ ω ∂P, g ω ≤ R⁻¹ * q ω := by
    filter_upwards [hpos] with ω hω
    dsimp [g, q]
    have h := abs_log_sub_heatStartLogClamp_le R (f ω) hR hω
    calc
      |Real.log (f ω) - heatStartLogClamp R (f ω)| ≤ |Real.log (f ω)| ^ 2 / R := h
      _ = R⁻¹ * |Real.log (f ω)| ^ 2 := by field_simp
  have hGint : Integrable g P := by
    apply hmajor.mono' hgMeas
    filter_upwards [hpoint] with ω hω
    change ‖|Real.log (f ω) - heatStartLogClamp R (f ω)|‖ ≤
      R⁻¹ * |Real.log (f ω)| ^ 2
    rw [Real.norm_of_nonneg (abs_nonneg _)]
    simpa [g, q] using hω
  have hreal : ∫ ω, g ω ∂P ≤ M / R := by
    calc
      ∫ ω, g ω ∂P ≤ ∫ ω, R⁻¹ * q ω ∂P := integral_mono_ae hGint hmajor hpoint
      _ = R⁻¹ * ∫ ω, q ω ∂P := by rw [integral_const_mul]
      _ ≤ R⁻¹ * M := mul_le_mul_of_nonneg_left hM (inv_nonneg.mpr hR.le)
      _ = M / R := by ring
  have hnonneg : ∀ᵐ ω ∂P, 0 ≤ g ω := Filter.Eventually.of_forall fun ω => abs_nonneg _
  have hlin := ofReal_integral_eq_lintegral_ofReal hGint hnonneg
  rw [show (fun ω => ENNReal.ofReal
      |Real.log (f ω) - heatStartLogClamp R (f ω)|) = fun ω => ENNReal.ofReal (g ω) by
        funext ω; rfl]
  rw [← hlin]
  exact ENNReal.ofReal_le_ofReal hreal

private theorem cellAverage_exp_lower_of_even (N : ℕ) (hN : 1 ≤ N) (h₀ : Plane →ᵇ ℝ)
    {z : Site} (hz : Even (z 0 + z 1)) :
    Real.exp (-‖h₀‖) ≤ cellAverage N (fun y => Real.exp (h₀ y)) z := by
  have hb := Smoothing.cellAverage_exp_bounds_of_even N hN h₀ hz
  have hloglo := (abs_le.mp hb.2).1
  have hexp := Real.exp_le_exp.mpr hloglo
  simpa only [Real.exp_log hb.1] using hexp

private theorem heatStart_profile_pos (ϑ : ℝ) {N : ℕ} (hN : 1 ≤ N) (s T δ : ℝ)
    (hsT : s < T) (x : Plane)
    (h₀ : Plane →ᵇ ℝ) (ω : Disorder) :
    0 < profileP2Fun (criticalBeta ϑ N) (evenCeil (N * s)) (evenCeil (N * T))
      (fun w => srwKernel (evenCeil (N * δ)) (w - latticePoint N x))
      (cellAverage N fun y => Real.exp (h₀ y)) ω := by
  let a : ℕ := evenCeil (N * s)
  let b : ℕ := evenCeil (N * T)
  let m : ℕ := evenCeil (N * δ)
  let d : ℕ := b - a
  let x₀ : Site := latticePoint N x
  let A : Finset Site := Polymer.endpoints x₀ m
  let ν : Site → ℝ := fun w => srwKernel m (w - x₀)
  let f : Site → ℝ := fun z => cellAverage N (fun y => Real.exp (h₀ y)) z
  let B : Disorder → ℝ := fun ω => profileP2Fun (criticalBeta ϑ N) a b ν (fun _ => 1) ω
  let F : Disorder → ℝ := fun ω => profileP2Fun (criticalBeta ϑ N) a b ν f ω
  have ha_le_b : a ≤ b := by
    dsimp [a, b]
    apply evenCeil_mono
    exact mul_le_mul_of_nonneg_left hsT.le (Nat.cast_nonneg N)
  have hdEven : Even d := by
    obtain ⟨ka, hka⟩ := evenCeil_even (N * s)
    obtain ⟨kb, hkb⟩ := evenCeil_even (N * T)
    have hka_le : ka ≤ kb := by
      have h : evenCeil (N * s) ≤ evenCeil (N * T) := by
        apply evenCeil_mono
        exact mul_le_mul_of_nonneg_left hsT.le (Nat.cast_nonneg N)
      rw [hka, hkb] at h
      omega
    dsimp [d, a, b]
    rw [hka, hkb]
    refine ⟨kb - ka, ?_⟩
    omega
  have hmEven : Even m := by dsimp [m]; exact evenCeil_even (N * δ)
  have hx₀Even : x₀ ∈ evenLattice := by dsimp [x₀]; exact latticePoint_mem_evenLattice N x
  have hνA : ∀ w ∉ A, ν w = 0 := by
    intro w hw
    exact Polymer.srwKernel_eq_zero_of_not_mem m x₀ w hw
  have hν0 : ∀ w, 0 ≤ ν w := by
    intro w
    exact Polymer.kernel_nonneg m (w - x₀)
  have hν1 : ∑ w ∈ A, ν w = 1 := by
    simpa [A, ν] using Polymer.sum_srwKernel_endpoints m x₀
  have htermLow : ∀ w ∈ A, ∀ z ∈ Polymer.endpoints w d, Real.exp (-‖h₀‖) ≤ f z := by
    intro w hw z hz
    have hwEven : w ∈ evenLattice := evenLattice_of_even_duration hx₀Even hmEven hw
    have hzEven : z ∈ evenLattice := evenLattice_of_even_duration hwEven hdEven hz
    change Even (z 0 + z 1) at hzEven
    exact cellAverage_exp_lower_of_even N hN h₀ hzEven
  have hmono := profileP2Fun_le_of_reachable (β := criticalBeta ϑ N) (a := a) (b := b)
    ν (fun _ => Real.exp (-‖h₀‖)) f A hνA hν0 htermLow ω
  have hprofileLow : Real.exp (-‖h₀‖) * B ω ≤ F ω := by
    simpa [B, F, profileP2Fun_const_terminal (β := criticalBeta ϑ N) a b ν A hνA
      (Real.exp (-‖h₀‖)) ω] using hmono
  have hBpos : 0 < B ω := by
    exact OnePoint.profileP2Fun_pos_of_normalized (criticalBeta ϑ N) a b ν A
      hνA hν0 hν1 ω
  have hFpos : 0 < F ω := lt_of_lt_of_le (mul_pos (Real.exp_pos _) hBpos) hprofileLow
  simpa [a, b, m, x₀, ν, f, F] using hFpos

private theorem cellAverage_exp_nonneg_le (N : ℕ) (hN : 1 ≤ N) (h₀ : Plane →ᵇ ℝ)
    (z : Site) :
    0 ≤ cellAverage N (fun y => Real.exp (h₀ y)) z ∧
      cellAverage N (fun y => Real.exp (h₀ y)) z ≤ Real.exp ‖h₀‖ := by
  by_cases hz : z ∈ evenLattice
  · change Even (z 0 + z 1) at hz
    have hb := Smoothing.cellAverage_exp_bounds_of_even N hN h₀ hz
    have hloghi := (abs_le.mp hb.2).2
    have hupp : cellAverage N (fun y => Real.exp (h₀ y)) z ≤ Real.exp ‖h₀‖ := by
      have := Real.exp_le_exp.mpr hloghi
      simpa only [Real.exp_log hb.1] using this
    exact ⟨hb.1.le, hupp⟩
  · have hEmpty : cell N z = ∅ := cell_eq_empty_of_not_even hz
    simp [cellAverage, hEmpty]
    positivity

/-- Replacing the heat-cell start weights by the walk kernel changes the polymer pairing by at
most the terminal bound times the `ℓ¹` kernel error. -/
private theorem heatStart_profile_pairing_error (ϑ : ℝ) {N : ℕ} (hN : 1 ≤ N)
    (s T δ : ℝ) (hδ : 0 < δ) (x : Plane) (h₀ : Plane →ᵇ ℝ) (η : ℝ)
    (hη : ∑' w : Site,
      |srwKernel (evenCeil ((N : ℝ) * δ)) (w - latticePoint N x) -
        ∫ y in cell N w, heatKernel δ (y - x)| ≤ η) :
    MemLp (fun ω =>
      profileP2Fun (criticalBeta ϑ N) (evenCeil (N * s)) (evenCeil (N * T))
          (fun w => srwKernel (evenCeil (N * δ)) (w - latticePoint N x))
          (cellAverage N fun y => Real.exp (h₀ y)) ω -
        ∫ p, heatKernel δ (p.1 - x) * Real.exp (h₀ p.2)
          ∂(SHF.Limit.polymerMeasure ϑ N s T ω)) 1 disorderLaw ∧
    ∫⁻ ω, ENNReal.ofReal
      |profileP2Fun (criticalBeta ϑ N) (evenCeil (N * s)) (evenCeil (N * T))
          (fun w => srwKernel (evenCeil (N * δ)) (w - latticePoint N x))
          (cellAverage N fun y => Real.exp (h₀ y)) ω -
        ∫ p, heatKernel δ (p.1 - x) * Real.exp (h₀ p.2)
          ∂(SHF.Limit.polymerMeasure ϑ N s T ω)| ∂disorderLaw ≤
      ENNReal.ofReal (Real.exp ‖h₀‖ * η) := by
  classical
  let a : ℕ := evenCeil (N * s)
  let b : ℕ := evenCeil (N * T)
  let m : ℕ := evenCeil (N * δ)
  let x₀ : Site := latticePoint N x
  let ν : Site → ℝ := fun w => srwKernel m (w - x₀)
  let μ : Site → ℝ := fun w => ∫ y in cell N w, heatKernel δ (y - x)
  let f : Site → ℝ := fun z => cellAverage N (fun y => Real.exp (h₀ y)) z
  let C : Disorder → ℝ := fun ω => profileP2Fun (criticalBeta ϑ N) a b μ f ω
  let A : Disorder → ℝ := fun ω => profileP2Fun (criticalBeta ϑ N) a b ν f ω
  let M : ℝ := Real.exp ‖h₀‖
  have hM : 0 ≤ M := by positivity
  have hν0 : ∀ w, 0 ≤ ν w := by
    intro w
    exact Polymer.kernel_nonneg m (w - x₀)
  have hνsum : (∑' w : Site, ν w) = 1 := by
    simpa [ν, m, x₀] using Polymer.tsum_srwKernel m (latticePoint N x)
  have hνabs : Summable (fun w : Site => |ν w|) :=
    Polymer.summable_probability_profile ν hν0 hνsum
  obtain ⟨hμ0, hμsum, hμabs⟩ := heatKernel_cellMass_probability hδ x
  have hdiffabs : Summable (fun w : Site => |ν w - μ w|) := by
    have hmajor : Summable (fun w : Site => |ν w| + |μ w|) := hνabs.add hμabs
    apply hmajor.of_nonneg_of_le (fun _ => by positivity)
    intro w
    calc
      |ν w - μ w| = |ν w + -μ w| := by rw [sub_eq_add_neg]
      _ ≤ |ν w| + |-μ w| := abs_add_le _ _
      _ = |ν w| + |μ w| := by rw [abs_neg]
  have hf : ∀ z, 0 ≤ f z ∧ f z ≤ M := by
    intro z
    simpa only [f, M] using cellAverage_exp_nonneg_le N hN h₀ z
  have hprofileDiff := memLp_lintegral_abs_profileP2Fun_sub_le
    (criticalBeta ϑ N) a b ν μ f hνabs hμabs hdiffabs M hM hf
  have hsumRepr :
      (∑' w : Site, ENNReal.ofReal |ν w - μ w|) =
        ENNReal.ofReal (∑' w : Site, |ν w - μ w|) := by
    exact (ENNReal.ofReal_tsum_of_nonneg (fun w => abs_nonneg _) hdiffabs).symm
  have hprofileDiff' :
      ∫⁻ ω, ENNReal.ofReal |A ω - C ω| ∂disorderLaw ≤ ENNReal.ofReal (M * η) := by
    calc
      _ ≤ ENNReal.ofReal M * ∑' w, ENNReal.ofReal |ν w - μ w| := hprofileDiff.2
      _ = ENNReal.ofReal M * ENNReal.ofReal (∑' w, |ν w - μ w|) := by rw [hsumRepr]
      _ ≤ ENNReal.ofReal M * ENNReal.ofReal η :=
        mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hη) (by positivity)
      _ = ENNReal.ofReal (M * η) := (ENNReal.ofReal_mul hM).symm
  have hkerAE := SHF.Positivity.ae_integrable_polymer_heat_start ϑ
    (by exact_mod_cast hN) s T δ hδ x
  have hPairInt : ∀ᵐ ω ∂disorderLaw,
      Integrable (fun p : Plane × Plane => heatKernel δ (p.1 - x) * Real.exp (h₀ p.2))
        (SHF.Limit.polymerMeasure ϑ N s T ω) := by
    filter_upwards [hkerAE] with ω hker
    have hmeas : AEStronglyMeasurable
        (fun p : Plane × Plane => heatKernel δ (p.1 - x) * Real.exp (h₀ p.2))
        (SHF.Limit.polymerMeasure ϑ N s T ω) := by
      have hm : Measurable (fun p : Plane × Plane =>
          heatKernel δ (p.1 - x) * Real.exp (h₀ p.2)) := by
        exact ((((continuous_heatKernel δ).comp (continuous_fst.sub continuous_const)).mul
          (Real.continuous_exp.comp (h₀.continuous.comp continuous_snd))).measurable)
      exact hm.aestronglyMeasurable
    have hmajor : Integrable
        (fun p : Plane × Plane => M * ‖heatKernel δ (p.1 - x)‖)
        (SHF.Limit.polymerMeasure ϑ N s T ω) := by
      simpa [M, mul_comm] using hker.norm.const_mul (Real.exp ‖h₀‖)
    apply hmajor.mono' hmeas
    filter_upwards [] with p
    have hg : ‖Real.exp (h₀ p.2)‖ ≤ M := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      calc
        h₀ p.2 ≤ |h₀ p.2| := le_abs_self _
        _ = ‖h₀ p.2‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖h₀‖ := h₀.norm_coe_le_norm p.2
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |heatKernel δ (p.1 - x)| * |Real.exp (h₀ p.2)| ≤
          |heatKernel δ (p.1 - x)| * M :=
        mul_le_mul_of_nonneg_left hg (abs_nonneg _)
      _ = M * ‖heatKernel δ (p.1 - x)‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg hδ.le _)]
        ring
  have hbridge : ∀ᵐ ω ∂disorderLaw, C ω =
      ∫ p, heatKernel δ (p.1 - x) * Real.exp (h₀ p.2)
      ∂(SHF.Limit.polymerMeasure ϑ N s T ω) := by
    filter_upwards [hPairInt] with ω hω
    exact profile_cellHeat_eq_polymerMeasure_pairing ϑ N s T δ x h₀ ω
      (by exact_mod_cast hN) hω
  have hbridgeLin :
      ∫⁻ ω, ENNReal.ofReal |A ω -
          ∫ p, heatKernel δ (p.1 - x) * Real.exp (h₀ p.2)
            ∂(SHF.Limit.polymerMeasure ϑ N s T ω)| ∂disorderLaw =
        ∫⁻ ω, ENNReal.ofReal |A ω - C ω| ∂disorderLaw := by
    apply lintegral_congr_ae
    filter_upwards [hbridge] with ω hω
    rw [hω]
  rw [← hbridgeLin] at hprofileDiff'
  have hmem : MemLp (fun ω =>
      A ω - ∫ p, heatKernel δ (p.1 - x) * Real.exp (h₀ p.2)
          ∂(SHF.Limit.polymerMeasure ϑ N s T ω)) 1 disorderLaw := by
    apply (memLp_congr_ae ?_).2 hprofileDiff.1
    filter_upwards [hbridge] with ω hω
    rw [← hω]
  refine ⟨?_, ?_⟩
  · simpa only [A, a, b, m, x₀, ν, μ, f, M] using hmem
  · simpa only [A, a, b, m, x₀, ν, μ, f, M] using hprofileDiff'

/-- The mean error between a finite-scale profile logarithm and the clamped polymer heat
pairing is bounded by a logarithmic tail and the kernel-cell approximation error. -/
theorem heatStart_log_clamp_pair_error (ϑ : ℝ) {N : ℕ} (hN : 1 ≤ N)
    (s T δ : ℝ) (hsT : s < T) (hδ : 0 < δ) (x : Plane) (h₀ : Plane →ᵇ ℝ)
    (η R M : ℝ) (hR : 0 < R)
    (hKernel : ∑' w : Site,
      |srwKernel (evenCeil ((N : ℝ) * δ)) (w - latticePoint N x) -
        ∫ y in cell N w, heatKernel δ (y - x)| ≤ η)
    (hLogSqInt : Integrable
      (fun ω => |heatStartLogProfile ϑ N s T δ x h₀ ω| ^ 2) disorderLaw)
    (hLogSqBound : ∫ ω, |heatStartLogProfile ϑ N s T δ x h₀ ω| ^ 2 ∂disorderLaw ≤ M) :
    ∫⁻ ω, ENNReal.ofReal
      |heatStartLogProfile ϑ N s T δ x h₀ ω -
        heatStartLogClamp R
          (∫ p, heatKernel δ (p.1 - x) * Real.exp (h₀ p.2)
            ∂(SHF.Limit.polymerMeasure ϑ N s T ω))| ∂disorderLaw ≤
      ENNReal.ofReal (M / R + Real.exp R * (Real.exp ‖h₀‖ * η)) := by
  let F : Disorder → ℝ := fun ω => profileP2Fun (criticalBeta ϑ N)
    (evenCeil (N * s)) (evenCeil (N * T))
    (fun w => srwKernel (evenCeil (N * δ)) (w - latticePoint N x))
    (cellAverage N fun y => Real.exp (h₀ y)) ω
  let G : Disorder → ℝ := fun ω =>
    ∫ p, heatKernel δ (p.1 - x) * Real.exp (h₀ p.2)
      ∂(SHF.Limit.polymerMeasure ϑ N s T ω)
  have hFmeas : AEMeasurable F disorderLaw := by
    dsimp [F]
    exact (Polymer.measurable_profileP2Fun (criticalBeta ϑ N)
      (evenCeil (N * s)) (evenCeil (N * T))
      (fun w => srwKernel (evenCeil (N * δ)) (w - latticePoint N x))
      (cellAverage N fun y => Real.exp (h₀ y))).aemeasurable
  have hFpos : ∀ ω, 0 < F ω := by
    intro ω
    exact heatStart_profile_pos ϑ hN s T δ hsT x h₀ ω
  have htail := lintegral_abs_log_clamp_le hFmeas
    (Filter.Eventually.of_forall hFpos) hLogSqInt hLogSqBound hR
  have hpair := heatStart_profile_pairing_error ϑ hN s T δ hδ x h₀ η hKernel
  have hdiffMem : MemLp (fun ω => F ω - G ω) 1 disorderLaw := by
    simpa only [F, G, heatStartLogProfile] using hpair.1
  have hdiffMeas : AEMeasurable (fun ω => ENNReal.ofReal |F ω - G ω|) disorderLaw := by
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      ((measurable_abs.comp_aemeasurable hdiffMem.aemeasurable))
  have htailMeas : AEMeasurable (fun ω => ENNReal.ofReal
      |Real.log (F ω) - heatStartLogClamp R (F ω)|) disorderLaw := by
    have hraw : AEMeasurable (fun ω =>
        Real.log (F ω) - heatStartLogClamp R (F ω)) disorderLaw :=
      (Real.measurable_log.comp_aemeasurable hFmeas).sub
        ((heatStartLogClamp_continuous R).measurable.comp_aemeasurable hFmeas)
    exact ENNReal.measurable_ofReal.comp_aemeasurable (measurable_abs.comp_aemeasurable hraw)
  have hη0 : 0 ≤ η := le_trans (tsum_nonneg fun w => abs_nonneg _) hKernel
  have hM0 : 0 ≤ M := le_trans
    (integral_nonneg (fun ω => sq_nonneg
      (|heatStartLogProfile ϑ N s T δ x h₀ ω|))) hLogSqBound
  have hExp0 : 0 ≤ Real.exp R := Real.exp_nonneg _
  have hExpH0 : 0 ≤ Real.exp ‖h₀‖ := Real.exp_nonneg _
  have hpoint (ω : Disorder) :
      |Real.log (F ω) - heatStartLogClamp R (G ω)| ≤
        |Real.log (F ω) - heatStartLogClamp R (F ω)| +
          Real.exp R * |F ω - G ω| := by
    calc
      |Real.log (F ω) - heatStartLogClamp R (G ω)| ≤
          |Real.log (F ω) - heatStartLogClamp R (F ω)| +
            |heatStartLogClamp R (F ω) - heatStartLogClamp R (G ω)| :=
        abs_sub_le _ _ _
      _ ≤ |Real.log (F ω) - heatStartLogClamp R (F ω)| +
          Real.exp R * |F ω - G ω| := by
        gcongr
        have hL := heatStartLogClamp_lipschitz R hR.le
        have h := hL.norm_sub_le (F ω) (G ω)
        change |heatStartLogClamp R (F ω) - heatStartLogClamp R (G ω)| ≤
          Real.exp R * |F ω - G ω| at h
        exact h
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal
          |Real.log (F ω) - heatStartLogClamp R (F ω)| +
          ENNReal.ofReal (Real.exp R) * ENNReal.ofReal |F ω - G ω| ∂disorderLaw := by
        apply lintegral_mono
        intro ω
        change ENNReal.ofReal
            |Real.log (F ω) - heatStartLogClamp R (G ω)| ≤
          ENNReal.ofReal |Real.log (F ω) - heatStartLogClamp R (F ω)| +
            ENNReal.ofReal (Real.exp R) * ENNReal.ofReal |F ω - G ω|
        rw [← ENNReal.ofReal_mul hExp0,
          ← ENNReal.ofReal_add (abs_nonneg _) (mul_nonneg hExp0 (abs_nonneg _))]
        exact ENNReal.ofReal_le_ofReal (hpoint ω)
    _ = (∫⁻ ω, ENNReal.ofReal
          |Real.log (F ω) - heatStartLogClamp R (F ω)| ∂disorderLaw) +
        ENNReal.ofReal (Real.exp R) *
          (∫⁻ ω, ENNReal.ofReal |F ω - G ω| ∂disorderLaw) := by
        rw [lintegral_add_left' htailMeas,
          lintegral_const_mul'' (ENNReal.ofReal (Real.exp R)) hdiffMeas]
    _ ≤ ENNReal.ofReal (M / R) +
        ENNReal.ofReal (Real.exp R) * ENNReal.ofReal (Real.exp ‖h₀‖ * η) :=
      add_le_add htail (mul_le_mul_of_nonneg_left hpair.2 (by positivity))
    _ = ENNReal.ofReal (M / R + Real.exp R * (Real.exp ‖h₀‖ * η)) := by
      rw [← ENNReal.ofReal_mul hExp0]
      rw [← ENNReal.ofReal_add (div_nonneg hM0 hR.le)
        (mul_nonneg hExp0 (mul_nonneg hExpH0 hη0))]

private theorem pi_l2_norm_le_sum_abs {k : ℕ} (v : Fin k → ℝ) :
    ‖v‖ ≤ ∑ i, |v i| := by
  rw [Pi.norm_def]
  have hsum : 0 ≤ ∑ i, |v i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hsup : Finset.univ.sup (fun i => ‖v i‖₊) ≤ Real.toNNReal (∑ i, |v i|) := by
    apply Finset.sup_le
    intro i hi
    have hsingle : |v i| ≤ ∑ j, |v j| :=
      Finset.single_le_sum (f := fun j : Fin k => |v j|) (fun j _ => abs_nonneg _)
        (Finset.mem_univ i)
    have hreal : (↑(‖v i‖₊) : ℝ) ≤ ↑(Real.toNNReal (∑ j, |v j|)) := by
      rw [coe_nnnorm, Real.coe_toNNReal (∑ j, |v j|) hsum]
      simpa only [Real.norm_eq_abs] using hsingle
    exact NNReal.coe_le_coe.mpr hreal
  calc
    ↑(Finset.univ.sup (fun i => ‖v i‖₊)) ≤ ↑(Real.toNNReal (∑ i, |v i|)) :=
      NNReal.coe_le_coe.mpr hsup
    _ = ∑ i, |v i| := Real.coe_toNNReal (∑ i, |v i|) hsum


private theorem heatStart_log_clamp_eq_cutlog {R x : ℝ} (hR : 0 < R) (hx : 0 < x) :
    heatStartLogClamp R x = heatStartLogCut R (Real.log x) := by
  rw [heatStartLogClamp_eq_logTrunc R x hR.le hx]
  rfl

private theorem lintegral_norm_pi_le_of_component_bounds
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {k : ℕ}
    (D : Ω → Fin k → ℝ) (hD : AEMeasurable D P)
    (hDint : ∀ i, Integrable (fun ω => ‖D ω i‖) P)
    (B : Fin k → ℝ) (hB : ∀ i, ∫ ω, ‖D ω i‖ ∂P ≤ B i) :
    ∫⁻ ω, ENNReal.ofReal ‖D ω‖ ∂P ≤ ENNReal.ofReal (∑ i, B i) := by
  have hsumInt : Integrable (fun ω => ∑ i : Fin k, ‖D ω i‖) P :=
    integrable_finsetSum Finset.univ (fun i hi => hDint i)
  have hnormInt : Integrable (fun ω => ‖D ω‖) P := by
    apply hsumInt.mono' hD.aestronglyMeasurable.norm
    filter_upwards [] with ω
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
      pi_l2_norm_le_sum_abs (D ω)
  have hsumBound : ∫ ω, ‖D ω‖ ∂P ≤ ∑ i, B i := by
    calc
      _ ≤ ∫ ω, ∑ i : Fin k, ‖D ω i‖ ∂P := by
        apply integral_mono hnormInt hsumInt
        intro ω
        exact pi_l2_norm_le_sum_abs (D ω)
      _ = ∑ i, ∫ ω, ‖D ω i‖ ∂P := by
        rw [integral_finsetSum Finset.univ (fun i hi => hDint i)]
      _ ≤ ∑ i, B i := Finset.sum_le_sum fun i hi => hB i
  have hnonneg : ∀ᵐ ω ∂P, 0 ≤ ‖D ω‖ := Filter.Eventually.of_forall fun ω => norm_nonneg _
  rw [← ofReal_integral_eq_lintegral_ofReal hnormInt hnonneg]
  exact ENNReal.ofReal_le_ofReal hsumBound

/-- Joint logarithmic heat-start convergence and convergence of every positive absolute moment. -/
theorem heatStart_log_tendsto_of (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (_hZ : IsCriticalSHF ϑ P Z)
    (_hpair : ∀ {s t δ : ℝ}, 0 ≤ s → s < t → 0 < δ → ∀ (x : Plane) (g : Plane →ᵇ ℝ),
      (∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane => heatKernel δ (p.1 - x) * g p.2) (Z s t ω)) ∧
      Integrable (shfPairing Z s t (fun y => heatKernel δ (y - x)) g) P ∧
      (∫ ω, |shfPairing Z s t (fun y => heatKernel δ (y - x)) g ω| ∂P ≤ ‖g‖) ∧
      TendstoInDistribution
        (fun (N : ℕ) (ω : Disorder) => ∫ p, heatKernel δ (p.1 - x) * g p.2 ∂(polymerMeasure ϑ N s t ω))
        atTop (shfPairing Z s t (fun y => heatKernel δ (y - x)) g) (fun _ => disorderLaw) P)
    (hjoint : ∀ (k : ℕ) (s t δ : Fin k → ℝ) (x : Fin k → Plane) (g : Fin k → (Plane →ᵇ ℝ)),
      (∀ i, 0 ≤ s i ∧ s i < t i ∧ 0 < δ i) →
      TendstoInDistribution
        (fun (N : ℕ) (ω : Disorder) (i : Fin k) =>
          ∫ p, heatKernel (δ i) (p.1 - x i) * g i p.2 ∂(polymerMeasure ϑ N (s i) (t i) ω))
        atTop (fun ω i => shfPairing Z (s i) (t i)
          (fun y => heatKernel (δ i) (y - x i)) (g i) ω)
        (fun _ => disorderLaw) P)
    (hpos : ∀ (s t δ : ℝ) (x : Plane) (h₀ : Plane →ᵇ ℝ), 0 ≤ s → s < t → 0 < δ →
      (∀ᵐ ω ∂P, 0 < shfPairing Z s t (fun y => heatKernel δ (y - x))
        (fun y => Real.exp (h₀ y)) ω) ∧
      AEMeasurable (fun ω =>
        Real.log (shfPairing Z s t (fun y => heatKernel δ (y - x))
          (fun y => Real.exp (h₀ y)) ω)) P)
    (T : ℝ) (h₀ : Plane →ᵇ ℝ) (k : ℕ) (s δ : Fin k → ℝ) (x : Fin k → Plane)
    (hs : ∀ i, 0 ≤ s i ∧ s i < T ∧ 0 < δ i) :
    (∀ i, ∀ᵐ ω ∂P, 0 < shfPairing Z (s i) T (fun y => heatKernel (δ i) (y - x i))
      (fun y => Real.exp (h₀ y)) ω) ∧
    TendstoInDistribution
      (fun (N : ℕ) (ω : Disorder) (i : Fin k) => Real.log (profileP2Fun (criticalBeta ϑ N)
        (evenCeil (N * s i)) (evenCeil (N * T))
        (fun w => srwKernel (evenCeil (N * δ i)) (w - latticePoint N (x i)))
        (cellAverage N fun y => Real.exp (h₀ y)) ω))
      atTop
      (fun ω i => Real.log (shfPairing Z (s i) T (fun y => heatKernel (δ i) (y - x i))
        (fun y => Real.exp (h₀ y)) ω))
      (fun _ => disorderLaw) P ∧
    ∀ (i : Fin k) (p : ℝ), 0 < p →
      Tendsto (fun N : ℕ => ∫ ω, |Real.log (profileP2Fun (criticalBeta ϑ N)
          (evenCeil (N * s i)) (evenCeil (N * T))
          (fun w => srwKernel (evenCeil (N * δ i)) (w - latticePoint N (x i)))
          (cellAverage N fun y => Real.exp (h₀ y)) ω)| ^ p ∂disorderLaw) atTop
        (𝓝 (∫ ω, |Real.log (shfPairing Z (s i) T
          (fun y => heatKernel (δ i) (y - x i))
          (fun y => Real.exp (h₀ y)) ω)| ^ p ∂P)) := by
  classical
  let V : Ω → Fin k → ℝ := fun ω i =>
    shfPairing Z (s i) T (fun y => heatKernel (δ i) (y - x i))
      (fun y => Real.exp (h₀ y)) ω
  let L : Ω → Fin k → ℝ := fun ω i => Real.log (V ω i)
  let X : ℕ → Disorder → Fin k → ℝ := fun N ω i => heatStartLogProfile ϑ N (s i) T (δ i) (x i) h₀ ω
  let Y : ℕ → ℕ → Disorder → Fin k → ℝ := fun j N ω i =>
    heatStartLogClamp ((j : ℝ) + 1)
      (∫ p, heatKernel (δ i) (p.1 - x i) * Real.exp (h₀ p.2)
        ∂(SHF.Limit.polymerMeasure ϑ N (s i) T ω))
  let Yl : ℕ → Ω → Fin k → ℝ := fun j ω i => heatStartLogClamp ((j : ℝ) + 1) (V ω i)
  let g₀ : Plane →ᵇ ℝ := BoundedContinuousFunction.mkOfBound
    ⟨fun y => Real.exp (h₀ y), by fun_prop⟩ (2 * Real.exp ‖h₀‖) (by
      intro y z
      change |Real.exp (h₀ y) - Real.exp (h₀ z)| ≤ 2 * Real.exp ‖h₀‖
      have hy : Real.exp (h₀ y) ≤ Real.exp ‖h₀‖ :=
        Real.exp_le_exp.mpr (abs_le.mp (h₀.norm_coe_le_norm y)).2
      have hz : Real.exp (h₀ z) ≤ Real.exp ‖h₀‖ :=
        Real.exp_le_exp.mpr (abs_le.mp (h₀.norm_coe_le_norm z)).2
      have hye : 0 ≤ Real.exp (h₀ y) := Real.exp_nonneg _
      have hze : 0 ≤ Real.exp (h₀ z) := Real.exp_nonneg _
      have h := abs_sub (Real.exp (h₀ y)) (Real.exp (h₀ z))
      rw [abs_of_nonneg hye, abs_of_nonneg hze] at h
      nlinarith)
  have hparams : ∀ i, 0 ≤ s i ∧ s i < T ∧ 0 < δ i := hs
  have hraw := hjoint k s (fun _ => T) δ x (fun _ => g₀) hparams
  have hcont (j : ℕ) : Continuous (fun v : Fin k → ℝ =>
      fun i => heatStartLogClamp ((j : ℝ) + 1) (v i)) := by
    apply continuous_pi
    intro i
    exact (heatStartLogClamp_continuous _).comp (continuous_apply i)
  have hY (j : ℕ) : TendstoInDistribution (fun N => Y j N) atTop (Yl j)
      (fun _ => disorderLaw) P := by
    have h := hraw.continuous_comp (hcont j)
    simpa [Y, Yl, V, Function.comp_def, g₀, BoundedContinuousFunction.mkOfBound_coe] using h
  have hposAll : ∀ i, ∀ᵐ ω ∂P, 0 < V ω i := by
    intro i
    exact hpos (s i) T (δ i) (x i) h₀ (hs i).1 (hs i).2.1 (hs i).2.2 |>.1
  have hlogMeas : AEMeasurable L P := by
    apply aemeasurable_pi_iff.mpr
    intro i
    exact hpos (s i) T (δ i) (x i) h₀ (hs i).1 (hs i).2.1 (hs i).2.2 |>.2
  have hYl : TendstoInDistribution Yl atTop L (fun _ => P) P := by
    have hcut := heatStart_logCut_tendstoInDistribution hlogMeas hposAll
    have hae (j : ℕ) : (fun ω i => heatStartLogCut ((j : ℝ) + 1) (Real.log (V ω i))) =ᵐ[P]
        Yl j := by
      filter_upwards [ae_all_iff.mpr hposAll] with ω hω
      funext i
      exact (heatStart_log_clamp_eq_cutlog (by positivity) (hω i)).symm
    exact hcut.congr hae (Filter.EventuallyEq.rfl)
  have hXm : ∀ N, AEMeasurable (X N) disorderLaw := by
    intro N
    apply aemeasurable_pi_iff.mpr
    intro i
    dsimp [X, heatStartLogProfile]
    exact (Polymer.measurable_profileP2Fun (criticalBeta ϑ N)
      (evenCeil (N * s i)) (evenCeil (N * T))
      (fun w => srwKernel (evenCeil (N * δ i)) (w - latticePoint N (x i)))
      (cellAverage N fun y => Real.exp (h₀ y))).log.aemeasurable
  let Ci : Fin k → ℝ := fun i => Classical.choose
    (heatStartLogProfile_square_bound ϑ (hs i).1 (hs i).2.1 (hs i).2.2 h₀)
  have hCi (i : Fin k) : 0 ≤ Ci i ∧ ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω => |X N ω i| ^ 2) disorderLaw ∧
      ∫ ω, |X N ω i| ^ 2 ∂disorderLaw ≤ Ci i * 2 * Real.Gamma 2 := by
    have h := Classical.choose_spec
      (heatStartLogProfile_square_bound ϑ (hs i).1 (hs i).2.1 (hs i).2.2 h₀)
    refine ⟨h.1, ?_⟩
    filter_upwards [h.2] with N hN
    simpa only [Ci, X, heatStartLogProfile] using hN (x i)
  let M : Fin k → ℝ := fun i => Ci i * 2 * Real.Gamma 2
  have hMnonneg (i : Fin k) : 0 ≤ M i := by
    dsimp [M]
    exact mul_nonneg (mul_nonneg (hCi i).1 (by norm_num))
      (Real.Gamma_pos_of_pos (by norm_num)).le
  have hMsq (i : Fin k) : ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω => |X N ω i| ^ 2) disorderLaw ∧
      ∫ ω, |X N ω i| ^ 2 ∂disorderLaw ≤ M i := by
    simpa only [M] using (hCi i).2
  let Msum : ℝ := ∑ i, M i
  let Hsum : ℝ := ∑ i : Fin k, Real.exp ‖h₀‖
  have hMsum : 0 ≤ Msum := by dsimp [Msum]; exact Finset.sum_nonneg fun i _ => hMnonneg i
  have hHsum : 0 ≤ Hsum := by dsimp [Hsum]; positivity
  have hXY : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ᶠ N in atTop,
      ∫⁻ ω, ENNReal.ofReal ‖X N ω - Y j N ω‖ ∂disorderLaw ≤ ENNReal.ofReal ε := by
    intro ε hε
    let A : ℝ := 1 + 2 * Hsum / ε
    have hAge : 1 ≤ A := by
      dsimp [A]
      have hq : 0 ≤ 2 * Hsum / ε := by positivity
      linarith
    have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hAge
    have hlargeM : ∀ᶠ j : ℕ in atTop,
        Msum / ((j : ℝ) + 1) < ε / 2 := by
      have h := tendsto_natCast_atTop_atTop.eventually
        (eventually_gt_atTop (Msum / (ε / 2)))
      filter_upwards [h] with j hj
      have hden : 0 < (j : ℝ) + 1 := by positivity
      have hhalf : 0 < ε / 2 := by positivity
      have hj' : Msum < (ε / 2) * (j : ℝ) := by
        simpa [mul_comm] using (div_lt_iff₀ hhalf).mp hj
      apply (div_lt_iff₀ hden).2
      nlinarith [hj']
    have hlargeH : ∀ᶠ j : ℕ in atTop,
        Hsum * Real.exp (-((j : ℝ) + 1)) < ε / 2 := by
      have h := tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (Real.log A))
      filter_upwards [h] with j hj
      let R : ℝ := (j : ℝ) + 1
      have hR : 0 < R := by dsimp [R]; positivity
      have hlogR : Real.log A < R := by dsimp [R]; linarith
      have hExp : A < Real.exp R := by
        rw [← Real.exp_log hApos]
        exact Real.exp_lt_exp.mpr hlogR
      have hinv : Real.exp (-R) < A⁻¹ := by
        have h' := one_div_lt_one_div_of_lt hApos hExp
        simpa [one_div, Real.exp_neg] using h'
      have hproduct : (ε / 2) * A = ε / 2 + Hsum := by
        dsimp [A]
        field_simp [hε.ne']
      have hdiv : Hsum / A ≤ ε / 2 := by
        apply (div_le_iff₀ hApos).2
        rw [hproduct]
        linarith
      by_cases hHpos : 0 < Hsum
      · calc
          Hsum * Real.exp (-R) < Hsum * A⁻¹ := mul_lt_mul_of_pos_left hinv hHpos
          _ = Hsum / A := by rw [div_eq_mul_inv]
          _ ≤ ε / 2 := hdiv
      · have hHzero : Hsum = 0 := le_antisymm (not_lt.mp hHpos) hHsum
        simp [hHzero]
        positivity
    filter_upwards [hlargeM, hlargeH] with j hjM hjH
    let R : ℝ := (j : ℝ) + 1
    let η : ℝ := Real.exp (-2 * R)
    have hR : 0 < R := by dsimp [R]; positivity
    have hη : 0 < η := Real.exp_pos _
    have hKernel (i : Fin k) : ∀ᶠ N : ℕ in atTop,
        ∑' w : Site, |srwKernel (evenCeil ((N : ℝ) * δ i) ) (w - latticePoint N (x i)) -
          ∫ y in cell N w, heatKernel (δ i) (y - x i)| ≤ η := by
      exact (srwKernel_sub_cellHeat_l1_le (δ i) (hs i).2.2 η hη).mono fun N hN => hN (x i)
    have hKernelAll : ∀ᶠ N : ℕ in atTop, ∀ i, ∑' w : Site,
        |srwKernel (evenCeil ((N : ℝ) * δ i)) (w - latticePoint N (x i)) -
          ∫ y in cell N w, heatKernel (δ i) (y - x i)| ≤ η :=
      Filter.eventually_all.mpr hKernel
    have hSqAll : ∀ᶠ N : ℕ in atTop, ∀ i,
        Integrable (fun ω => |X N ω i| ^ 2) disorderLaw ∧
        ∫ ω, |X N ω i| ^ 2 ∂disorderLaw ≤ M i :=
      Filter.eventually_all.mpr hMsq
    have hGood' : ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧ (∀ i, ∑' w : Site,
        |srwKernel (evenCeil ((N : ℝ) * δ i)) (w - latticePoint N (x i)) -
          ∫ y in cell N w, heatKernel (δ i) (y - x i)| ≤ η) ∧
        (∀ i, Integrable (fun ω => |X N ω i| ^ 2) disorderLaw ∧
          ∫ ω, |X N ω i| ^ 2 ∂disorderLaw ≤ M i) := by
      filter_upwards [eventually_ge_atTop 1, hKernelAll, hSqAll] with N hN hK hS
      exact ⟨hN, hK, hS⟩
    filter_upwards [hGood'] with N hgood
    rcases hgood with ⟨hN, hK, hS⟩
    let D : Disorder → Fin k → ℝ := fun ω => X N ω - Y j N ω
    have hDmeas : AEMeasurable D disorderLaw := by
      exact (hXm N).sub ((hY j).forall_aemeasurable N)
    have hXint (i : Fin k) : Integrable (fun ω => X N ω i) disorderLaw := by
      have hXsm : AEStronglyMeasurable (fun ω => X N ω i) disorderLaw :=
        ((aemeasurable_pi_iff.mp (hXm N)) i).aestronglyMeasurable
      have hXsq : Integrable (fun ω => (X N ω i) ^ 2) disorderLaw := by
        simpa only [sq_abs] using (hS i).1
      have hXmem : MemLp (fun ω => X N ω i) 2 disorderLaw :=
        (memLp_two_iff_integrable_sq hXsm).2 hXsq
      exact memLp_one_iff_integrable.mp (hXmem.mono_exponent (by norm_num))
    have hYint (i : Fin k) : Integrable (fun ω => Y j N ω i) disorderLaw := by
      have hYsm : AEStronglyMeasurable (fun ω => Y j N ω i) disorderLaw :=
        ((aemeasurable_pi_iff.mp ((hY j).forall_aemeasurable N)) i).aestronglyMeasurable
      apply Integrable.of_bound hYsm R
      filter_upwards [] with ω
      have hRabs : |heatStartLogClamp R
          (∫ p, heatKernel (δ i) (p.1 - x i) * Real.exp (h₀ p.2)
            ∂(SHF.Limit.polymerMeasure ϑ N (s i) T ω))| ≤ R := by
        have hlow : -R ≤ heatStartLogClamp R
            (∫ p, heatKernel (δ i) (p.1 - x i) * Real.exp (h₀ p.2)
              ∂(SHF.Limit.polymerMeasure ϑ N (s i) T ω)) := by
          dsimp [heatStartLogClamp]
          have hmaxLower : Real.exp (-R) ≤ max (Real.exp (-R)) (min
              (∫ p, heatKernel (δ i) (p.1 - x i) * Real.exp (h₀ p.2)
                ∂(SHF.Limit.polymerMeasure ϑ N (s i) T ω)) (Real.exp R)) :=
            le_max_left _ _
          have hlog : Real.log (Real.exp (-R)) ≤ Real.log (max (Real.exp (-R)) (min
              (∫ p, heatKernel (δ i) (p.1 - x i) * Real.exp (h₀ p.2)
                ∂(SHF.Limit.polymerMeasure ϑ N (s i) T ω)) (Real.exp R))) :=
            Real.log_le_log (Real.exp_pos _) hmaxLower
          simpa only [Real.log_exp] using hlog
        have hupp : heatStartLogClamp R
            (∫ p, heatKernel (δ i) (p.1 - x i) * Real.exp (h₀ p.2)
              ∂(SHF.Limit.polymerMeasure ϑ N (s i) T ω)) ≤ R := by
          dsimp [heatStartLogClamp]
          have hmax : max (Real.exp (-R)) (min
              (∫ p, heatKernel (δ i) (p.1 - x i) * Real.exp (h₀ p.2)
                ∂(SHF.Limit.polymerMeasure ϑ N (s i) T ω)) (Real.exp R)) ≤ Real.exp R :=
            max_le (Real.exp_le_exp.mpr (by linarith)) (min_le_right _ _)
          calc
            Real.log (max (Real.exp (-R)) (min _ (Real.exp R))) ≤ Real.log (Real.exp R) :=
              Real.log_le_log ((Real.exp_pos _).trans_le (le_max_left _ _)) hmax
            _ = R := Real.log_exp _
        exact abs_le.mpr ⟨hlow, hupp⟩
      simpa only [D, X, Y, heatStartLogProfile, R, Real.norm_eq_abs] using hRabs
    have hDint (i : Fin k) : Integrable (fun ω => ‖D ω i‖) disorderLaw := by
      have hX := hXint i
      have hY := hYint i
      have hDI : Integrable (fun ω => D ω i) disorderLaw := by
        change Integrable (fun ω => X N ω i - Y j N ω i) disorderLaw
        exact hX.sub hY
      exact hDI.norm
    have hB (i : Fin k) : ∫ ω, ‖D ω i‖ ∂disorderLaw ≤
        M i / R + Real.exp R * (Real.exp ‖h₀‖ * η) := by
      have hpair := heatStart_log_clamp_pair_error ϑ hN (s i) T (δ i) (hs i).2.1
        (hs i).2.2 (x i) h₀ η R (M i) hR (hK i) (hS i).1 (hS i).2
      have hInt := hDint i
      have hlin := ofReal_integral_eq_lintegral_ofReal hInt
        (Filter.Eventually.of_forall fun ω => norm_nonneg _)
      have hpair' : ∫⁻ ω, ENNReal.ofReal ‖D ω i‖ ∂disorderLaw ≤
          ENNReal.ofReal (M i / R + Real.exp R * (Real.exp ‖h₀‖ * η)) := by
        simpa only [D, Pi.sub_apply, X, Y, heatStartLogProfile, R, Real.norm_eq_abs] using hpair
      have hreal : ENNReal.ofReal (∫ ω, ‖D ω i‖ ∂disorderLaw) ≤
          ENNReal.ofReal (M i / R + Real.exp R * (Real.exp ‖h₀‖ * η)) := by
        rw [hlin]
        exact hpair'
      have hbound0 : 0 ≤ M i / R + Real.exp R * (Real.exp ‖h₀‖ * η) := by
        apply add_nonneg
        · exact div_nonneg (hMnonneg i) hR.le
        · exact mul_nonneg (Real.exp_nonneg R)
            (mul_nonneg (Real.exp_nonneg ‖h₀‖) hη.le)
      exact (ENNReal.ofReal_le_ofReal_iff hbound0).mp hreal
    have hvec := lintegral_norm_pi_le_of_component_bounds disorderLaw D hDmeas hDint
      (fun i => M i / R + Real.exp R * (Real.exp ‖h₀‖ * η)) hB
    have hExpEta : Real.exp R * η = Real.exp (-R) := by
      dsimp [η]
      rw [← Real.exp_add]
      congr 1
      ring
    have hsum : (∑ i : Fin k, (M i / R + Real.exp R * (Real.exp ‖h₀‖ * η))) =
        Msum / R + Real.exp (-R) * Hsum := by
      calc
        _ = Msum / R + (↑k : ℝ) * (Real.exp R * (Real.exp ‖h₀‖ * η)) := by
          simp [Msum, Finset.sum_add_distrib, Finset.sum_div, Finset.sum_const]
        _ = Msum / R + Real.exp (-R) * Hsum := by
          have hfactor : Real.exp R * (Real.exp ‖h₀‖ * η) =
              Real.exp (-R) * Real.exp ‖h₀‖ := by
            calc
              Real.exp R * (Real.exp ‖h₀‖ * η) =
                  (Real.exp R * η) * Real.exp ‖h₀‖ := by ring
              _ = Real.exp (-R) * Real.exp ‖h₀‖ := by rw [hExpEta]
          rw [hfactor]
          simp [Hsum, Finset.sum_const]
          ring
    have htotal : Msum / R + Real.exp (-R) * Hsum ≤ ε := by
      dsimp [R]
      have hfirst : Msum / ((j : ℝ) + 1) < ε / 2 := hjM
      have hsecond : Hsum * Real.exp (-((j : ℝ) + 1)) < ε / 2 := hjH
      nlinarith
    rw [hsum] at hvec
    exact hvec.trans (ENNReal.ofReal_le_ofReal htotal)
  have hTID : TendstoInDistribution X atTop L (fun _ => disorderLaw) P :=
    tendstoInDistribution_of_approx_of_limit X Y Yl L hY hYl hXY hXm hlogMeas
  have hposOut : ∀ i, ∀ᵐ ω ∂P, 0 <
      shfPairing Z (s i) T (fun y => heatKernel (δ i) (y - x i))
        (fun y => Real.exp (h₀ y)) ω := hposAll
  have hmoment (i : Fin k) (p : ℝ) (hp : 0 < p) :
      Tendsto (fun N : ℕ => ∫ ω, |X N ω i| ^ p ∂disorderLaw) atTop
        (𝓝 (∫ ω, |L ω i| ^ p ∂P)) := by
    have hcoord := hTID.continuous_comp (g := fun v : Fin k → ℝ => v i)
      (continuous_apply i)
    have hcoord' : TendstoInDistribution (fun N ω => X N ω i) atTop (fun ω => L ω i)
        (fun _ => disorderLaw) P := by
      simpa only [Function.comp_def] using hcoord
    obtain ⟨Cq, hCq⟩ := heatStartLogProfile_rpow_bound ϑ (hs i).1 (hs i).2.1
      (hs i).2.2 (x i) h₀ (q := p + 1) (by linarith)
    have hM : ∀ᶠ N in atTop, ∫ ω, |X N ω i| ^ (p + 1) ∂disorderLaw ≤
        Cq * (p + 1) * Real.Gamma (p + 1) := by
      filter_upwards [hCq.2] with N hN
      simpa only [X, heatStartLogProfile] using hN.2
    have hInt : ∀ᶠ N in atTop,
        Integrable (fun ω => |X N ω i| ^ (p + 1)) disorderLaw := by
      filter_upwards [hCq.2] with N hN
      simpa only [X, heatStartLogProfile] using hN.1
    exact tendsto_integral_abs_rpow_of_tendstoInDistribution hcoord' hp (by linarith) hM hInt
  refine ⟨hposOut, hTID, ?_⟩
  intro i p hp
  have h := hmoment i p hp
  simpa only [X, L, V, heatStartLogProfile] using h

end Critical2DKPZ.JointConvergence

end
