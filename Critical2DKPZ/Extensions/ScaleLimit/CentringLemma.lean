/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.CentringLimits
public import Critical2DKPZ.Extensions.ScaleLimit.TightDrift
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Topology.Sequences
import Mathlib.Tactic

/-! # Identification of centring and variance from a scalar Gaussian limit

This proves the centring lemma of the scale-limit argument. Tightness first
bounds the deterministic drift. Compactness then extracts limits of both
parameters, which are identified by uniqueness of the Gaussian limit.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The centring lemma for partial sums indexed from zero. -/
theorem centring_range {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hind : iIndepFun Y P) (hm : ∀ i, AEMeasurable (Y i) P)
    (K : ℝ) (hK : ∀ i, ∀ᵐ ω ∂P, |Y i ω| ≤ K)
    (a : ℕ → ℝ) (ha : Tendsto a atTop atTop) (C : ℝ)
    (hvariance : ∀ n, variance (partialSumRange Y n) P ≤ C * a n ^ 2)
    (F : ℕ → Ω → ℝ) (hF : ∀ n, Integrable (F n) P)
    (herror : TendstoInMeasure P
      (fun n ω => (F n ω - partialSumRange Y n ω) / a n) atTop (fun _ => 0))
    (hclt : TendstoInDistribution
      (fun n ω => (F n ω - ∫ ω', F n ω' ∂P) / a n)
      atTop id (fun _ => P) (gaussianReal 0 1)) :
    Tendsto (fun n => variance (partialSumRange Y n) P / a n ^ 2) atTop (𝓝 1) ∧
      Tendsto (fun n => ((∫ ω, F n ω ∂P) - ∫ ω, partialSumRange Y n ω ∂P) / a n)
        atTop (𝓝 0) := by
  let S := partialSumRange Y
  let X : ℕ → Ω → ℝ := fun n ω => (S n ω - ∫ ω', S n ω' ∂P) / a n
  let U : ℕ → Ω → ℝ := fun n ω => (F n ω - ∫ ω', F n ω' ∂P) / a n
  let E : ℕ → Ω → ℝ := fun n ω => (F n ω - S n ω) / a n
  let V : ℕ → ℝ := fun n => variance (S n) P / a n ^ 2
  let d : ℕ → ℝ := fun n => ((∫ ω, F n ω ∂P) - ∫ ω, S n ω ∂P) / a n
  let C₀ : ℝ := max C 0
  have hS (n : ℕ) : MemLp (S n) 2 P :=
    memLp_finsetSum _ (fun i _ => memLp_of_ae_abs_le P (hm i) K (hK i) 2)
  have hXm (n : ℕ) : MemLp (X n) 2 P := by
    have hc := (hS n).sub (memLp_const (∫ ω', S n ω' ∂P))
    change MemLp (fun ω => S n ω - ∫ ω', S n ω' ∂P) 2 P at hc
    simpa only [X, div_eq_mul_inv, mul_comm] using hc.const_mul (a n)⁻¹
  have hXmean (n : ℕ) : (∫ ω, X n ω ∂P) = 0 := by
    dsimp [X]
    rw [integral_div, integral_sub ((hS n).integrable (by norm_num)) (integrable_const _)]
    simp only [integral_const, probReal_univ, one_smul, sub_self, zero_div]
  have hVX (n : ℕ) : variance (X n) P = V n := by
    dsimp [X, V]
    simp_rw [div_eq_mul_inv]
    rw [variance_mul_const, variance_sub_const (hS n).aestronglyMeasurable]
    simp only [inv_pow]
  have hV (n : ℕ) : 0 ≤ V n ∧ V n ≤ C₀ := by
    refine ⟨div_nonneg (variance_nonneg _ _) (sq_nonneg _), ?_⟩
    by_cases hn : a n = 0
    · simp only [V, hn, zero_pow (by norm_num : 2 ≠ 0), div_zero]
      exact le_max_right C 0
    · exact ((div_le_iff₀ (sq_pos_of_ne_zero hn)).mpr (hvariance n)).trans (le_max_left C 0)
  let R : ℝ := 2 * (Real.sqrt C₀ + 1)
  have hR : 0 < R := by dsimp [R]; positivity
  have hCR : C₀ / R ^ 2 ≤ 1 / 4 := by
    apply (div_le_iff₀ (sq_pos_of_pos hR)).mpr
    have hs := Real.sq_sqrt (le_max_right C 0)
    have hs0 := Real.sqrt_nonneg C₀
    dsimp [R]
    nlinarith
  have hXR (n : ℕ) : P {ω | R < |X n ω|} ≤ (1 / 4 : ℝ≥0∞) := by
    have hc := meas_ge_le_variance_div_sq (hXm n) hR
    have hsub : {ω | R < |X n ω|} ⊆ {ω | R ≤ |X n ω - ∫ ω', X n ω' ∂P|} := by
      intro ω hω
      change R < |X n ω| at hω
      change R ≤ |X n ω - ∫ ω', X n ω' ∂P|
      simpa only [hXmean, sub_zero] using hω.le
    calc
      _ ≤ ENNReal.ofReal (variance (X n) P / R ^ 2) := (measure_mono hsub).trans hc
      _ ≤ ENNReal.ofReal (C₀ / R ^ 2) := ENNReal.ofReal_le_ofReal
        (div_le_div_of_nonneg_right (by rw [hVX]; exact (hV n).2) (sq_nonneg R))
      _ ≤ ENNReal.ofReal (1 / 4) := ENNReal.ofReal_le_ofReal hCR
      _ = 1 / 4 := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]
        norm_num
  obtain ⟨D, hD, hdbound⟩ := eventually_abs_le_drift_of_tight P X U E d
    ⟨R, hR.le, hXR⟩ hclt herror (fun n ω => by dsimp [d, X, U, E]; ring)
  have hpair : Tendsto (fun n => (V n, d n)) atTop (𝓝 (1, 0)) := by
    apply tendsto_of_subseq_tendsto
    intro ns hns
    have hevent : ∀ᶠ n in atTop,
        (V (ns n), d (ns n)) ∈ Set.Icc 0 C₀ ×ˢ Set.Icc (-D) D := by
      filter_upwards [hns.eventually hdbound] with n hn
      exact ⟨hV (ns n), abs_le.mp hn⟩
    obtain ⟨z, hz, ms, hms, hlim⟩ :=
      (isCompact_Icc.prod isCompact_Icc).tendsto_subseq' hevent.frequently
    let u : ℕ → ℕ := fun n => ns (ms n)
    have hu : Tendsto u atTop atTop := hns.comp hms.tendsto_atTop
    have hv : Tendsto (fun n => variance (partialSumRange Y (u n)) P / a (u n) ^ 2)
        atTop (𝓝 z.1) := hlim.fst_nhds
    have hd : Tendsto (fun n => ((∫ ω, F (u n) ω ∂P) -
        ∫ ω, partialSumRange Y (u n) ω ∂P) / a (u n)) atTop (𝓝 z.2) := hlim.snd_nhds
    have hid := centring_parameters_of_limits P Y hind hm K hK a ha F hF herror hclt
      u hu ⟨z.1, hz.1.1⟩ z.2 hv hd
    have hz1 : z.1 = 1 := congrArg (fun v : ℝ≥0 => (v : ℝ)) hid.1
    have hzEq : z = (1, 0) := Prod.ext hz1 hid.2
    refine ⟨ms, ?_⟩
    simpa only [hzEq, Function.comp_def] using hlim
  exact ⟨hpair.fst_nhds, hpair.snd_nhds⟩

/-- Reindexing the first `n` positive integers as a range starting at zero. -/
theorem sum_range_add_one_eq_sum_Icc (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, f (i + 1)) = ∑ i ∈ Finset.Icc 1 n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega), ih]

/-- The centring lemma for the one-based partial sums in the note. -/
theorem centring {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hind : iIndepFun Y P) (hm : ∀ i, AEMeasurable (Y i) P)
    (K : ℝ) (hK : ∀ i, ∀ᵐ ω ∂P, |Y i ω| ≤ K)
    (a : ℕ → ℝ) (ha : Tendsto a atTop atTop) (C : ℝ)
    (hvariance : ∀ n, variance (fun ω => ∑ i ∈ Finset.Icc 1 n, Y i ω) P ≤ C * a n ^ 2)
    (F : ℕ → Ω → ℝ) (hF : ∀ n, Integrable (F n) P)
    (herror : TendstoInMeasure P
      (fun n ω => (F n ω - ∑ i ∈ Finset.Icc 1 n, Y i ω) / a n) atTop (fun _ => 0))
    (hclt : TendstoInDistribution
      (fun n ω => (F n ω - ∫ ω', F n ω' ∂P) / a n)
      atTop id (fun _ => P) (gaussianReal 0 1)) :
    Tendsto (fun n => variance (fun ω => ∑ i ∈ Finset.Icc 1 n, Y i ω) P / a n ^ 2)
      atTop (𝓝 1) ∧
      Tendsto (fun n => ((∫ ω, F n ω ∂P) -
        ∫ ω, (∑ i ∈ Finset.Icc 1 n, Y i ω) ∂P) / a n) atTop (𝓝 0) := by
  let Y' : ℕ → Ω → ℝ := fun i => Y (i + 1)
  have hsum (n : ℕ) : partialSumRange Y' n = (fun ω => ∑ i ∈ Finset.Icc 1 n, Y i ω) := by
    funext ω
    exact sum_range_add_one_eq_sum_Icc (fun i => Y i ω) n
  have hh := centring_range P Y' (hind.precomp Nat.succ_injective)
    (fun i => hm (i + 1)) K (fun i => hK (i + 1)) a ha C
    (by simpa only [hsum] using hvariance) F hF
    (by simpa only [hsum] using herror) hclt
  simpa only [hsum] using hh

end Critical2DKPZ.Extensions.ScaleLimit
