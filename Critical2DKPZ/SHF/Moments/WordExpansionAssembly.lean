/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordExpansionStageProps
public import Critical2DKPZ.SHF.Moments.CollisionWordMomentExpansion
public import Critical2DKPZ.SHF.Moments.KernelDictionary
import Critical2DKPZ.SHF.DeltaBose.MomentKernelL2Interfaces
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Tactic

/-! # Moving polymer moment limits from collision-word convergence -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped BigOperators CompactlySupported ENNReal Topology

namespace Critical2DKPZ.SHF.Moments

open Polymer DeltaBose

private theorem compactConfigTest_memLp (n : ℕ) (φ : Fin n → C_c(Plane × Plane, ℝ)) :
    ∃ F G : Configuration n → ℝ,
      MemLp F 2 volume ∧ MemLp G 2 volume ∧
      (∀ x, 0 ≤ F x) ∧ (∀ y, 0 ≤ G y) ∧
      ∀ x y : Configuration n,
        |∏ i, φ i (x i, y i)| ≤ F x * G y := by
  classical
  let Kx : Set (Configuration n) := Set.pi Set.univ
    (fun i => Prod.fst '' (tsupport (φ i)))
  let Ky : Set (Configuration n) := Set.pi Set.univ
    (fun i => Prod.snd '' (tsupport (φ i)))
  have hKx : IsCompact Kx := by
    dsimp [Kx]
    apply isCompact_univ_pi
    intro i
    exact (φ i).hasCompactSupport.image continuous_fst
  have hKy : IsCompact Ky := by
    dsimp [Ky]
    apply isCompact_univ_pi
    intro i
    exact (φ i).hasCompactSupport.image continuous_snd
  choose B hB using fun i =>
    (φ i).hasCompactSupport.exists_bound_of_continuousOn (φ i).continuous.continuousOn
  let M : ℝ := ∏ i, max (B i) 0
  let F : Configuration n → ℝ := fun x => M * Kx.indicator (fun _ => 1) x
  let G : Configuration n → ℝ := fun y => Ky.indicator (fun _ => 1) y
  have hM : 0 ≤ M := by
    dsimp [M]
    exact Finset.prod_nonneg fun i hi => le_max_right _ _
  have hF0 : MemLp (Kx.indicator (fun _ : Configuration n => (1 : ℝ))) 2 volume :=
    memLp_indicator_const (2 : ℝ≥0∞) hKx.measurableSet (1 : ℝ)
      (Or.inr (IsCompact.measure_lt_top hKx).ne)
  have hG : MemLp G 2 volume := by
    dsimp [G]
    exact memLp_indicator_const (2 : ℝ≥0∞) hKy.measurableSet (1 : ℝ)
      (Or.inr (IsCompact.measure_lt_top hKy).ne)
  have hF : MemLp F 2 volume := by
    dsimp [F]
    exact hF0.const_mul M
  have hFnn (x : Configuration n) : 0 ≤ F x := by
    dsimp [F]
    by_cases hx : x ∈ Kx <;> simp [hx, hM]
  have hGnn (y : Configuration n) : 0 ≤ G y := by
    dsimp [G]
    by_cases hy : y ∈ Ky <;> simp [hy]
  refine ⟨F, G, hF, hG, hFnn, hGnn, ?_⟩
  intro x y
  by_cases hzero : ∏ i, φ i (x i, y i) = 0
  · rw [hzero]
    simp only [abs_zero]
    exact mul_nonneg (hFnn x) (hGnn y)
  · have hprod : ∀ i, φ i (x i, y i) ≠ 0 := by
      intro i hi
      apply hzero
      exact Finset.prod_eq_zero (Finset.mem_univ i) hi
    have hx : x ∈ Kx := by
      simp only [Kx, Set.mem_pi, Set.mem_univ, true_implies]
      intro i
      have hp : (x i, y i) ∈ tsupport (φ i) :=
        subset_closure (Function.mem_support.mpr (hprod i))
      exact ⟨(x i, y i), hp, rfl⟩
    have hy : y ∈ Ky := by
      simp only [Ky, Set.mem_pi, Set.mem_univ, true_implies]
      intro i
      have hp : (x i, y i) ∈ tsupport (φ i) :=
        subset_closure (Function.mem_support.mpr (hprod i))
      exact ⟨(x i, y i), hp, rfl⟩
    have hφbound (i : Fin n) (p : Plane × Plane) : |φ i p| ≤ max (B i) 0 := by
      by_cases hp : φ i p = 0
      · simp [hp]
      · have hpt : p ∈ tsupport (φ i) := subset_closure (Function.mem_support.mpr hp)
        have hi := hB i p hpt
        rw [Real.norm_eq_abs] at hi
        exact hi.trans (le_max_left _ _)
    have hprodBound : |∏ i, φ i (x i, y i)| ≤ M := by
      rw [Finset.abs_prod]
      dsimp [M]
      exact Finset.prod_le_prod₀ (fun i hi => abs_nonneg _) (fun i hi =>
        hφbound i (x i, y i))
    simpa [F, G, hx, hy] using hprodBound

private theorem integral_test_momentKernel_eq_tsum (ϑ : ℝ) (n : ℕ) (hn4 : n ≤ 4)
    {h : ℝ} (hh : 0 < h) (φ : Fin n → C_c(Plane × Plane, ℝ)) :
    ∫ x : Configuration n, ∫ y : Configuration n,
        (∏ i, φ i (x i, y i)) *
          (momentKernel n (ϑ - Real.eulerMascheroniConstant) h x y).toReal
      = ∑' m : ℕ, ∑ w : CollisionWord n m,
        ∫ x : Configuration n, ∫ y : Configuration n,
          (∏ i, φ i (x i, y i)) *
            (diagramKernel (ϑ - Real.eulerMascheroniConstant) (List.ofFn w.1)
              h x y).toReal := by
  classical
  let θ := ϑ - Real.eulerMascheroniConstant
  let test : Configuration n × Configuration n → ℝ := fun xy =>
    ∏ i, φ i (xy.1 i, xy.2 i)
  let coeff : ℕ → Configuration n × Configuration n → ℝ≥0∞ := fun m xy =>
    continuousMomentDiagramCoefficient n m ϑ h xy.1 xy.2
  let term : ℕ → Configuration n × Configuration n → ℝ := fun m xy =>
    (coeff m xy).toReal
  let full : Configuration n × Configuration n → ℝ := fun xy =>
    (momentKernel n θ h xy.1 xy.2).toReal
  let bound : ℕ → Configuration n × Configuration n → ℝ := fun m xy =>
    |test xy| * term m xy
  obtain ⟨F, G, hF, hG, hFnn, hGnn, htest⟩ := compactConfigTest_memLp n φ
  obtain ⟨_, hform⟩ := momentKernel_L2_form_bounded n hn4 θ hh
  have hmajor : Integrable (fun xy : Configuration n × Configuration n =>
      F xy.1 * full xy * G xy.2) (volume.prod volume) :=
    (hform F G hF hG).1
  have hKparam : Measurable (fun xy : Configuration n × Configuration n =>
      ((θ, h), xy)) := by
    fun_prop
  have hKmeas : Measurable (fun xy : Configuration n × Configuration n =>
      momentKernel n θ h xy.1 xy.2) := by
    convert (measurable_momentKernel n).comp hKparam using 1
    funext xy
    rfl
  have hfullMeas : Measurable full := by
    dsimp [full]
    exact hKmeas.ennreal_toReal
  have htestMeas : Measurable test := by
    dsimp [test]
    fun_prop
  have hCoeffMeas (m : ℕ) : Measurable (coeff m) := by
    dsimp [coeff, continuousMomentDiagramCoefficient]
    apply Finset.measurable_sum
    intro w hw
    exact measurable_diagramKernel_comp (List.ofFn w.1)
      measurable_const measurable_const measurable_fst measurable_snd
  have htermMeas (m : ℕ) : Measurable (term m) := (hCoeffMeas m).ennreal_toReal
  have hKfinite : ∀ᵐ xy : Configuration n × Configuration n ∂(volume.prod volume),
      momentKernel n θ h xy.1 xy.2 ≠ ⊤ := momentKernel_ne_top n hn4 θ hh
  have hcoeffLe (m : ℕ) (xy : Configuration n × Configuration n) :
      coeff m xy ≤ momentKernel n θ h xy.1 xy.2 := by
    change continuousMomentDiagramCoefficient n m ϑ h xy.1 xy.2 ≤ _
    rw [momentKernel_eq_tsum_continuousMomentDiagramCoefficient]
    exact ENNReal.le_tsum (f := fun k => continuousMomentDiagramCoefficient n k ϑ h xy.1 xy.2) m
  have hcoeffSum (xy : Configuration n × Configuration n)
      (hfinite : momentKernel n θ h xy.1 xy.2 ≠ ⊤) :
      HasSum (fun m => term m xy) (full xy) := by
    have hsumTop : (∑' m, coeff m xy) ≠ ⊤ := by
      rw [← momentKernel_eq_tsum_continuousMomentDiagramCoefficient n ϑ h xy.1 xy.2]
      exact hfinite
    have hcoeffFinite (m : ℕ) : coeff m xy ≠ ⊤ := by
      exact ne_top_of_le_ne_top hfinite (hcoeffLe m xy)
    have hsumReal : (∑' m : ℕ, (coeff m xy).toReal) = full xy := by
      calc
        _ = (∑' m : ℕ, coeff m xy).toReal :=
          (ENNReal.tsum_toReal_eq hcoeffFinite).symm
        _ = full xy := by
          dsimp [full, θ]
          rw [momentKernel_eq_tsum_continuousMomentDiagramCoefficient]
    rw [← hsumReal]
    exact ENNReal.hasSum_toReal hsumTop
  have hboundMeas (m : ℕ) : Measurable (bound m) := by
    dsimp [bound]
    exact htestMeas.abs.mul (htermMeas m)
  have htestKernelInt : Integrable (fun xy => |test xy| * full xy) (volume.prod volume) := by
    apply hmajor.mono' ((htestMeas.abs.mul hfullMeas).aestronglyMeasurable)
    filter_upwards [] with xy
    have hnn := htest xy.1 xy.2
    have hk : 0 ≤ full xy := ENNReal.toReal_nonneg
    calc
      ‖|test xy| * full xy‖ = |test xy| * full xy := by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) hk)]
      _ ≤ (F xy.1 * G xy.2) * full xy := mul_le_mul_of_nonneg_right hnn hk
      _ = F xy.1 * full xy * G xy.2 := by ring
  have htestFullInt : Integrable (fun xy => test xy * full xy) (volume.prod volume) := by
    apply htestKernelInt.mono' ((htestMeas.mul hfullMeas).aestronglyMeasurable)
    filter_upwards [] with xy
    have hk : 0 ≤ full xy := ENNReal.toReal_nonneg
    change |test xy * full xy| ≤ |test xy| * full xy
    rw [abs_mul, abs_of_nonneg hk]
  have hboundTsumEq : (fun xy : Configuration n × Configuration n => ∑' m, bound m xy) =ᵐ[volume.prod volume]
      (fun xy => |test xy| * full xy) := by
    filter_upwards [hKfinite] with xy hfinite
    have hs := hcoeffSum xy hfinite
    dsimp [bound, term]
    rw [tsum_mul_left, hs.tsum_eq]
  have hboundTsumInt : Integrable (fun xy : Configuration n × Configuration n =>
      ∑' m, bound m xy) (volume.prod volume) := by
    exact htestKernelInt.congr hboundTsumEq.symm
  have hboundSummable : ∀ᵐ xy : Configuration n × Configuration n ∂(volume.prod volume),
      Summable (fun m => bound m xy) := by
    filter_upwards [hKfinite] with xy hfinite
    have hs := (hcoeffSum xy hfinite).summable.mul_left |test xy|
    simpa [bound, term, mul_comm] using hs
  have hboundTerms (m : ℕ) : ∀ᵐ xy : Configuration n × Configuration n ∂(volume.prod volume),
      ‖test xy * term m xy‖ ≤ bound m xy := by
    filter_upwards [] with xy
    have hnn : 0 ≤ term m xy := ENNReal.toReal_nonneg
    simp [bound, Real.norm_eq_abs, abs_of_nonneg hnn]
  have hpointwise : ∀ᵐ xy : Configuration n × Configuration n ∂(volume.prod volume),
      HasSum (fun m => test xy * term m xy) (test xy * full xy) := by
    filter_upwards [hKfinite] with xy hfinite
    exact (hcoeffSum xy hfinite).mul_left (test xy)
  have htermsAEMeas (m : ℕ) : AEStronglyMeasurable
      (fun xy => test xy * term m xy) (volume.prod volume) :=
    (htestMeas.mul (htermMeas m)).aestronglyMeasurable
  have hsumIntegral := hasSum_integral_of_dominated_convergence bound htermsAEMeas
    hboundTerms hboundSummable hboundTsumInt hpointwise
  have hwordLe (m : ℕ) (w : CollisionWord n m) (xy : Configuration n × Configuration n) :
      diagramKernel θ (List.ofFn w.1) h xy.1 xy.2 ≤ coeff m xy := by
    change diagramKernel (ϑ - Real.eulerMascheroniConstant) (List.ofFn w.1) h xy.1 xy.2 ≤
      ∑ w' : CollisionWord n m,
        diagramKernel (ϑ - Real.eulerMascheroniConstant) (List.ofFn w'.1) h xy.1 xy.2
    exact Finset.single_le_sum (fun w' hw' => (bot_le :
      (0 : ℝ≥0∞) ≤ diagramKernel (ϑ - Real.eulerMascheroniConstant)
        (List.ofFn w'.1) h xy.1 xy.2)) (Finset.mem_univ w)
  have hwordIntegrable (m : ℕ) (w : CollisionWord n m) : Integrable
      (fun xy : Configuration n × Configuration n => test xy *
        (diagramKernel θ (List.ofFn w.1) h xy.1 xy.2).toReal) (volume.prod volume) := by
    have hwordMeas : Measurable (fun xy : Configuration n × Configuration n =>
        (diagramKernel θ (List.ofFn w.1) h xy.1 xy.2).toReal) :=
      (measurable_diagramKernel_comp (List.ofFn w.1)
        measurable_const measurable_const measurable_fst measurable_snd).ennreal_toReal
    apply hmajor.mono' ((htestMeas.mul hwordMeas).aestronglyMeasurable)
    filter_upwards [hKfinite] with xy hfinite
    have hwordle : (diagramKernel θ (List.ofFn w.1) h xy.1 xy.2).toReal ≤ full xy :=
      ENNReal.toReal_mono hfinite (le_trans (hwordLe m w xy) (hcoeffLe m xy))
    have hk : 0 ≤ (diagramKernel θ (List.ofFn w.1) h xy.1 xy.2).toReal := ENNReal.toReal_nonneg
    change |test xy * (diagramKernel θ (List.ofFn w.1) h xy.1 xy.2).toReal| ≤
      F xy.1 * full xy * G xy.2
    rw [abs_mul, abs_of_nonneg hk]
    calc
      |test xy| * (diagramKernel θ (List.ofFn w.1) h xy.1 xy.2).toReal ≤
          F xy.1 * G xy.2 * (diagramKernel θ (List.ofFn w.1) h xy.1 xy.2).toReal :=
        mul_le_mul_of_nonneg_right (htest xy.1 xy.2) hk
      _ = F xy.1 * (diagramKernel θ (List.ofFn w.1) h xy.1 xy.2).toReal * G xy.2 := by ring
      _ = F xy.1 * ((diagramKernel θ (List.ofFn w.1) h xy.1 xy.2).toReal * G xy.2) := by ring
      _ ≤ F xy.1 * (full xy * G xy.2) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hwordle (hGnn xy.2)) (hFnn xy.1)
      _ = F xy.1 * full xy * G xy.2 := by ring
  have hcoeffFinite (m : ℕ) (xy : Configuration n × Configuration n)
      (hfinite : momentKernel n θ h xy.1 xy.2 ≠ ⊤) : coeff m xy ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt (hcoeffLe m xy) (lt_top_iff_ne_top.mpr hfinite))
  have hcoeffIntegralProd (m : ℕ) :
      ∑ w : CollisionWord n m, ∫ xy : Configuration n × Configuration n,
        test xy * (diagramKernel θ (List.ofFn w.1) h xy.1 xy.2).toReal ∂(volume.prod volume) =
      ∫ xy : Configuration n × Configuration n, test xy * term m xy ∂(volume.prod volume) := by
    have hcoeffToReal : ∀ᵐ xy : Configuration n × Configuration n ∂(volume.prod volume),
        term m xy = ∑ w : CollisionWord n m,
          (diagramKernel θ (List.ofFn w.1) h xy.1 xy.2).toReal := by
      filter_upwards [hKfinite] with xy hfinite
      have hwordFinite (w : CollisionWord n m) :
          diagramKernel θ (List.ofFn w.1) h xy.1 xy.2 ≠ ⊤ := by
        have hle := le_trans (hwordLe m w xy) (hcoeffLe m xy)
        exact ne_top_of_le_ne_top hfinite hle
      have hfiniteWords : ∀ w : CollisionWord n m, w ∈ Finset.univ →
          diagramKernel θ (List.ofFn w.1) h xy.1 xy.2 ≠ ⊤ := by
        intro w hw
        exact hwordFinite w
      dsimp [term, coeff, continuousMomentDiagramCoefficient]
      rw [ENNReal.toReal_sum hfiniteWords]
    calc
      _ = ∫ xy : Configuration n × Configuration n, ∑ w : CollisionWord n m,
          test xy * (diagramKernel θ (List.ofFn w.1) h xy.1 xy.2).toReal ∂(volume.prod volume) := by
        symm
        exact integral_finsetSum Finset.univ (fun w hw => hwordIntegrable m w)
      _ = ∫ xy : Configuration n × Configuration n, test xy * term m xy
          ∂(volume.prod volume) := by
        apply integral_congr_ae
        filter_upwards [hcoeffToReal] with xy hxy
        rw [hxy, Finset.mul_sum]
  have hcoeffIntegralIter (m : ℕ) :
      ∑ w : CollisionWord n m, ∫ x : Configuration n, ∫ y : Configuration n,
        test (x, y) * (diagramKernel θ (List.ofFn w.1) h x y).toReal =
      ∫ xy : Configuration n × Configuration n, test xy * term m xy ∂(volume.prod volume) := by
    calc
      _ = ∑ w : CollisionWord n m, ∫ xy : Configuration n × Configuration n,
          test xy * (diagramKernel θ (List.ofFn w.1) h xy.1 xy.2).toReal ∂(volume.prod volume) := by
        apply Finset.sum_congr rfl
        intro w hw
        symm
        exact integral_prod _ (hwordIntegrable m w)
      _ = _ := hcoeffIntegralProd m
  have hsumIntegralWordsIter :
      ∑' m : ℕ, ∑ w : CollisionWord n m, ∫ x : Configuration n, ∫ y : Configuration n,
        test (x, y) * (diagramKernel θ (List.ofFn w.1) h x y).toReal =
      ∫ x : Configuration n, ∫ y : Configuration n, test (x, y) * full (x, y) := by
    calc
      _ = ∑' m : ℕ, ∫ xy : Configuration n × Configuration n,
          test xy * term m xy ∂(volume.prod volume) := by
            congr 1
            funext m
            exact hcoeffIntegralIter m
      _ = ∫ xy : Configuration n × Configuration n, test xy * full xy
          ∂(volume.prod volume) := hsumIntegral.tsum_eq
      _ = ∫ x : Configuration n, ∫ y : Configuration n, test (x, y) * full (x, y) :=
        integral_prod _ htestFullInt
  simpa [test, θ, full] using hsumIntegralWordsIter.symm

/-- Geometric domination, vanishing non-pair remainders and individual word limits imply moving-time polymer moment convergence for one through four replicas. -/
theorem rescaledP2P_moment_tendsto_moving_of (ϑ : ℝ) (n : ℕ) (_hn : 1 ≤ n) (hn4 : n ≤ 4)
    (hdom : WordGeometricDomination ϑ n) (hnp : NonpairRemainderSmall ϑ n)
    (hlim : WordLimits ϑ n)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t)
    (sN tN : ℕ → ℝ) (hsN : Tendsto sN atTop (𝓝 s))
    (htN : Tendsto tN atTop (𝓝 t)) (hsN0 : ∀ N, 0 ≤ sN N)
    (φ : Fin n → C_c(Plane × Plane, ℝ)) :
    Tendsto (fun N : ℕ => ∫ ω, ∏ i,
      (∫ p, φ i p * rescaledP2P ϑ N (sN N) (tN N) p ω)
      ∂disorderLaw)
      atTop
      (𝓝 (∫ x : DeltaBose.Configuration n, ∫ y : DeltaBose.Configuration n,
        (∏ i, φ i (x i, y i)) *
          (DeltaBose.momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal)) := by
  classical
  let τ : ℝ := (t - s) / 2
  let T : ℝ := t + 1
  let gap : ℕ → ℝ := fun N => tN N - sN N
  let A : ℕ → ℝ := fun N =>
    ∫ ω, ∏ i, (∫ p, φ i p * rescaledP2P ϑ N (sN N) (tN N) p ω) ∂disorderLaw
  let word : ℕ → ℕ → ℝ := fun N m =>
    ∑ w : CollisionWord n m, testedBlockWord ϑ N (sN N) (tN N) φ (List.ofFn w.1)
  let wordLimit : ℕ → ℝ := fun m =>
    ∑ w : CollisionWord n m,
      ∫ x : Configuration n, ∫ y : Configuration n,
        (∏ i, φ i (x i, y i)) *
          (diagramKernel (ϑ - Real.eulerMascheroniConstant) (List.ofFn w.1)
            (t - s) x y).toReal
  have hτ : 0 < τ := by dsimp [τ]; linarith
  have hτgap : τ < t - s := by dsimp [τ]; linarith
  have htT : t < T := by dsimp [T]; linarith
  have hgap : Tendsto gap atTop (𝓝 (t - s)) := by
    dsimp [gap]
    exact htN.sub hsN
  have hgapτ : ∀ᶠ N : ℕ in atTop, τ ≤ gap N := by
    filter_upwards [hgap.eventually (Ioi_mem_nhds hτgap)] with N hN
    exact le_of_lt hN
  have htNupper : ∀ᶠ N : ℕ in atTop, tN N ≤ T :=
    (htN.eventually_lt_const htT).mono fun N hN => le_of_lt hN
  have hwindow : ∀ᶠ N : ℕ in atTop,
      0 ≤ sN N ∧ τ ≤ tN N - sN N ∧ tN N ≤ T := by
    filter_upwards [hgapτ, htNupper] with N hNτ hNT
    exact ⟨hsN0 N, hNτ, hNT⟩
  obtain ⟨C, ρ, _, hρ, hρlt, hdomN⟩ := hdom (τ := τ) (T := T) hτ φ
  have hdomWindow : ∀ᶠ N : ℕ in atTop, ∀ m, ‖word N m‖ ≤ C * ρ ^ m := by
    filter_upwards [hwindow, hdomN] with N hN hD m
    dsimp [word]
    calc
      ‖∑ w : CollisionWord n m,
          testedBlockWord ϑ N (sN N) (tN N) φ (List.ofFn w.1)‖ ≤
          ∑ w : CollisionWord n m,
            |testedBlockWord ϑ N (sN N) (tN N) φ (List.ofFn w.1)| := norm_sum_le _ _
      _ ≤ C * ρ ^ m := hD (sN N) (tN N) hN.1 hN.2.1 hN.2.2 m
  have hwordTerm (m : ℕ) : Tendsto (fun N => word N m) atTop (𝓝 (wordLimit m)) := by
    dsimp [word, wordLimit]
    apply tendsto_finsetSum
    intro w hw
    exact hlim hs hst sN tN hsN htN hsN0 φ m w
  have hboundSummable : Summable (fun m : ℕ => C * ρ ^ m) :=
    (summable_geometric_of_lt_one hρ hρlt).mul_left C
  have hwords : Tendsto (fun N => ∑' m : ℕ, word N m) atTop
      (𝓝 (∑' m : ℕ, wordLimit m)) :=
    tendsto_tsum_of_dominated_convergence hboundSummable hwordTerm hdomWindow
  have hrem : Tendsto (fun N => testedNonpairRemainder ϑ N (sN N) (tN N) φ)
      atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hε2 : 0 < ε / 2 := by linarith
    have hR := hnp (τ := τ) (T := T) hτ φ (ε / 2) hε2
    filter_upwards [hwindow, hR] with N hN hRN
    have hbound := hRN (sN N) (tN N) hN.1 hN.2.1 hN.2.2
    have hdist : dist (testedNonpairRemainder ϑ N (sN N) (tN N) φ) 0 ≤ ε / 2 := by
      simpa only [dist_eq_norm, Real.norm_eq_abs, sub_zero] using hbound
    exact lt_of_le_of_lt hdist (by linarith)
  have hdecomp : (fun N => A N) =ᶠ[atTop]
      (fun N => (∑' m : ℕ, word N m) + testedNonpairRemainder ϑ N (sN N) (tN N) φ) := by
    filter_upwards [hwindow] with N hN
    dsimp [A, word]
    have hstN : sN N < tN N := sub_pos.mp (lt_of_lt_of_le hτ hN.2.1)
    exact integral_prod_pairing_eq_wordSum ϑ N hN.1 hstN.le φ
  have htarget : ∑' m : ℕ, wordLimit m =
      ∫ x : Configuration n, ∫ y : Configuration n,
        (∏ i, φ i (x i, y i)) *
          (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal := by
    simpa [wordLimit] using
      (integral_test_momentKernel_eq_tsum ϑ n hn4 (sub_pos.mpr hst) φ).symm
  have hA : Tendsto A atTop
      (𝓝 (∫ x : Configuration n, ∫ y : Configuration n,
        (∏ i, φ i (x i, y i)) *
          (momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal)) := by
    simpa [htarget] using Tendsto.congr' hdecomp.symm (hwords.add hrem)
  simpa [A] using hA

end Critical2DKPZ.SHF.Moments

end
