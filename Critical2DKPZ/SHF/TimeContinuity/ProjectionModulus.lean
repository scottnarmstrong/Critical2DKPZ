/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.TimeContinuity.DiscreteModulus
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! # Sequential estimates from slab projections -/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.SHF.TimeContinuity

/-- Extend values prescribed on a strictly increasing subsequence by their limit off it. -/
theorem extend_subsequence_real {n : ℕ → ℕ} (hn : StrictMono n) {u : ℕ → ℝ} {a : ℝ}
    (hu : Tendsto u atTop (𝓝 a)) (ha : 0 ≤ a) (hu0 : ∀ k, 0 ≤ u k) :
    ∃ v : ℕ → ℝ, Tendsto v atTop (𝓝 a) ∧ (∀ k, v (n k) = u k) ∧ ∀ m, 0 ≤ v m := by
  classical
  let v : ℕ → ℝ := fun m => if h : ∃ k, n k = m then u (Classical.choose h) else a
  have hvn (k : ℕ) : v (n k) = u k := by
    have hex : ∃ j, n j = n k := ⟨k, rfl⟩
    have hchoose : Classical.choose hex = k := hn.injective (Classical.choose_spec hex)
    simp [v, hex, hchoose]
  have hv : Tendsto v atTop (𝓝 a) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp ((Metric.tendsto_nhds.mp hu) ε hε)
    filter_upwards [Filter.eventually_atTop.2 ⟨n K, fun m hm => hm⟩] with m hm
    by_cases hex : ∃ k, n k = m
    · let k := Classical.choose hex
      have hk : K ≤ k := by
        by_contra hnot
        have hkn : k < K := Nat.lt_of_not_ge hnot
        have hmono := hn hkn
        have heq := Classical.choose_spec hex
        have heqn : n k = n (Classical.choose hex) := heq.trans (Classical.choose_spec hex).symm
        have hlt : n (Classical.choose hex) < n K := by
          simpa [heqn] using hmono
        have hle : n K ≤ n (Classical.choose hex) := hm.trans_eq (Classical.choose_spec hex).symm
        exact (not_lt_of_ge hle) hlt
      simpa [v, hex, k] using hK k hk
    · simpa [v, hex]
  have hv0 (m : ℕ) : 0 ≤ v m := by
    by_cases hex : ∃ k, n k = m
    · simp [v, hex]
      exact hu0 (Classical.choose hex)
    · simpa [v, hex] using ha
  exact ⟨v, hv, hvn, hv0⟩

/-- If the two slab identities hold and the smoothed pairing approaches the shorter pairing
in `L²`, the full pairing difference approaches zero whenever both endpoint second moments have
the same limit. -/
theorem projection_difference_sq_tendsto_zero
    (A B C : ℕ → Disorder → ℝ)
    (hB2 : ∀ n, Integrable (fun ω => B n ω ^ 2) disorderLaw)
    (hC2 : ∀ n, Integrable (fun ω => C n ω ^ 2) disorderLaw)
    (hD2 : ∀ n, Integrable (fun ω => (C n ω - B n ω) ^ 2) disorderLaw)
    (hproj : ∀ n, ∫ ω, (A n ω - B n ω) ^ 2 ∂disorderLaw =
      (∫ ω, A n ω ^ 2 ∂disorderLaw - ∫ ω, C n ω ^ 2 ∂disorderLaw) +
        ∫ ω, (C n ω - B n ω) ^ 2 ∂disorderLaw)
    {L : ℝ}
    (hA : Tendsto (fun n => ∫ ω, A n ω ^ 2 ∂disorderLaw) atTop (𝓝 L))
    (hB : Tendsto (fun n => ∫ ω, B n ω ^ 2 ∂disorderLaw) atTop (𝓝 L))
    (hD : Tendsto (fun n => ∫ ω, (C n ω - B n ω) ^ 2 ∂disorderLaw)
      atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, (A n ω - B n ω) ^ 2 ∂disorderLaw) atTop (𝓝 0) := by
  let cSq : ℕ → ℝ := fun n => ∫ ω, C n ω ^ 2 ∂disorderLaw
  let bSq : ℕ → ℝ := fun n => ∫ ω, B n ω ^ 2 ∂disorderLaw
  let dSq : ℕ → ℝ := fun n => ∫ ω, (C n ω - B n ω) ^ 2 ∂disorderLaw
  have hnonnegC (n : ℕ) : 0 ≤ cSq n := by
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun ω => sq_nonneg (C n ω))
  have hnonnegB (n : ℕ) : 0 ≤ bSq n := by
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun ω => sq_nonneg (B n ω))
  have hnonnegD (n : ℕ) : 0 ≤ dSq n := by
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun ω => sq_nonneg (C n ω - B n ω))
  have hdiffBound (n : ℕ) : |cSq n - bSq n| ≤
      Real.sqrt (dSq n) * Real.sqrt (2 * cSq n + 2 * bSq n) := by
    let U : Disorder → ℝ := fun ω => Real.sqrt ((C n ω - B n ω) ^ 2)
    let V : Disorder → ℝ := fun ω => Real.sqrt (2 * (C n ω) ^ 2 + 2 * (B n ω) ^ 2)
    have hUmeas : AEStronglyMeasurable U disorderLaw := by
      exact Real.continuous_sqrt.comp_aestronglyMeasurable (hD2 n).aestronglyMeasurable
    have hVbase : Integrable (fun ω => 2 * (C n ω) ^ 2 + 2 * (B n ω) ^ 2) disorderLaw :=
      ((hC2 n).const_mul 2).add ((hB2 n).const_mul 2)
    have hVmeas : AEStronglyMeasurable V disorderLaw := by
      exact Real.continuous_sqrt.comp_aestronglyMeasurable hVbase.aestronglyMeasurable
    have hUsqEq : (fun ω => U ω ^ 2) = fun ω => (C n ω - B n ω) ^ 2 := by
      funext ω
      simp only [U, Real.sq_sqrt (sq_nonneg (C n ω - B n ω))]
    have hUsq : Integrable (fun ω => U ω ^ 2) disorderLaw := by
      rw [hUsqEq]
      exact hD2 n
    have hVsqEq : (fun ω => V ω ^ 2) =
        fun ω => 2 * (C n ω) ^ 2 + 2 * (B n ω) ^ 2 := by
      funext ω
      have hnn : 0 ≤ 2 * (C n ω) ^ 2 + 2 * (B n ω) ^ 2 := by positivity
      change (Real.sqrt (2 * (C n ω) ^ 2 + 2 * (B n ω) ^ 2)) ^ 2 = _
      exact Real.sq_sqrt hnn
    have hVsq : Integrable (fun ω => V ω ^ 2) disorderLaw := by
      rw [hVsqEq]
      exact hVbase
    have hUmem : MemLp U 2 disorderLaw :=
      (memLp_two_iff_integrable_sq hUmeas).2 hUsq
    have hVmem : MemLp V 2 disorderLaw :=
      (memLp_two_iff_integrable_sq hVmeas).2 hVsq
    have hUmem' : MemLp U (ENNReal.ofReal (2 : ℝ)) disorderLaw := by simpa using hUmem
    have hVmem' : MemLp V (ENNReal.ofReal (2 : ℝ)) disorderLaw := by simpa using hVmem
    have hUVmem : MemLp (fun ω => U ω * V ω) 1 disorderLaw := by
      have hpq : ENNReal.HolderTriple
          (ENNReal.ofReal (2 : ℝ)) (ENNReal.ofReal (2 : ℝ)) 1 :=
        Real.HolderConjugate.two_two.ennrealOfReal
      exact @MemLp.mul Disorder inferInstance ℝ inferInstance disorderLaw
        (ENNReal.ofReal (2 : ℝ)) (ENNReal.ofReal (2 : ℝ)) 1 V U hUmem' hVmem' hpq
    have hUVint : Integrable (fun ω => U ω * V ω) disorderLaw := hUVmem.integrable (by norm_num)
    have hdiffInt : Integrable (fun ω => (C n ω) ^ 2 - (B n ω) ^ 2) disorderLaw :=
      (hC2 n).sub (hB2 n)
    have hpoint (ω : Disorder) :
        |(C n ω) ^ 2 - (B n ω) ^ 2| ≤ U ω * V ω := by
      have hU : U ω = |C n ω - B n ω| := by simp [U, Real.sqrt_sq_eq_abs]
      have hVnonneg : 0 ≤ 2 * (C n ω) ^ 2 + 2 * (B n ω) ^ 2 := by positivity
      have hsumSq : (C n ω + B n ω) ^ 2 ≤
          2 * (C n ω) ^ 2 + 2 * (B n ω) ^ 2 := by
        nlinarith [sq_nonneg (C n ω - B n ω)]
      have hsum : |C n ω + B n ω| ≤ V ω := by
        simpa [V] using Real.abs_le_sqrt hsumSq
      calc
        |(C n ω) ^ 2 - (B n ω) ^ 2| =
            |C n ω - B n ω| * |C n ω + B n ω| := by rw [← abs_mul]; congr 1; ring
        _ ≤ |C n ω - B n ω| * V ω :=
          mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
        _ = U ω * V ω := by rw [← hU]
    have hpointAE : ∀ᵐ ω ∂disorderLaw,
        |(C n ω) ^ 2 - (B n ω) ^ 2| ≤ U ω * V ω := Filter.Eventually.of_forall hpoint
    have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := disorderLaw) (p := (2 : ℝ)) (q := (2 : ℝ))
      Real.HolderConjugate.two_two
      (Filter.Eventually.of_forall fun ω => Real.sqrt_nonneg _)
      (Filter.Eventually.of_forall fun ω => Real.sqrt_nonneg _)
      hUmem' hVmem'
    have hHolder' : ∫ ω, U ω * V ω ∂disorderLaw ≤
        Real.sqrt (∫ ω, U ω ^ 2 ∂disorderLaw) *
          Real.sqrt (∫ ω, V ω ^ 2 ∂disorderLaw) := by
      simpa [U, V, Real.sqrt_eq_rpow] using hHolder
    have hUintegral : (∫ ω, U ω ^ 2 ∂disorderLaw) = dSq n := by
      calc
        _ = ∫ ω, (C n ω - B n ω) ^ 2 ∂disorderLaw := by rw [hUsqEq]
        _ = dSq n := rfl
    have hVintegration : (∫ ω, V ω ^ 2 ∂disorderLaw) = 2 * cSq n + 2 * bSq n := by
      calc
        _ = ∫ ω, 2 * (C n ω) ^ 2 + 2 * (B n ω) ^ 2 ∂disorderLaw := by rw [hVsqEq]
        _ = (2 * ∫ ω, C n ω ^ 2 ∂disorderLaw) +
            (2 * ∫ ω, B n ω ^ 2 ∂disorderLaw) := by
          rw [integral_add ((hC2 n).const_mul 2) ((hB2 n).const_mul 2),
            integral_const_mul, integral_const_mul]
        _ = 2 * cSq n + 2 * bSq n := by rfl
    calc
      |cSq n - bSq n| =
          |∫ ω, (C n ω) ^ 2 - (B n ω) ^ 2 ∂disorderLaw| := by
            congr 1
            rw [integral_sub (hC2 n) (hB2 n)]
      _ ≤ ∫ ω, |(C n ω) ^ 2 - (B n ω) ^ 2| ∂disorderLaw :=
        abs_integral_le_integral_abs
      _ ≤ ∫ ω, U ω * V ω ∂disorderLaw :=
        integral_mono_ae hdiffInt.abs hUVint hpointAE
      _ ≤ Real.sqrt (∫ ω, U ω ^ 2 ∂disorderLaw) *
          Real.sqrt (∫ ω, V ω ^ 2 ∂disorderLaw) := hHolder'
      _ = Real.sqrt (dSq n) * Real.sqrt (2 * cSq n + 2 * bSq n) := by
        rw [hUintegral, hVintegration]
  have hBbound : ∀ᶠ n : ℕ in atTop, bSq n ≤ |L| + 1 := by
    have hclose := (Metric.tendsto_nhds.mp hB) 1 (by norm_num)
    filter_upwards [hclose] with n hn
    have hn' : |bSq n - L| < 1 := by simpa only [Real.dist_eq] using hn
    have := (abs_lt.mp hn').2
    linarith [le_abs_self L]
  have hDbound : ∀ᶠ n : ℕ in atTop, dSq n ≤ 1 := by
    have hclose := (Metric.tendsto_nhds.mp hD) 1 (by norm_num)
    filter_upwards [hclose] with n hn
    have hn' : |dSq n| < 1 := by simpa only [Real.dist_eq, sub_zero] using hn
    have hn'' : dSq n < 1 := by
      simpa only [sub_zero, abs_of_nonneg (hnonnegD n)] using hn'
    exact hn''.le
  let K : ℝ := 10 + 6 * |L|
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hVbound : ∀ᶠ n : ℕ in atTop, 2 * cSq n + 2 * bSq n ≤ K := by
    filter_upwards [hBbound, hDbound] with n hBn hDn
    have hCbound : cSq n ≤ 2 * dSq n + 2 * bSq n := by
      have hpoint (ω : Disorder) : (C n ω) ^ 2 ≤
          2 * (C n ω - B n ω) ^ 2 + 2 * (B n ω) ^ 2 := by
        nlinarith [sq_nonneg (C n ω - 2 * B n ω)]
      have hraw := integral_mono_ae (hC2 n)
        ((hD2 n).const_mul 2 |>.add ((hB2 n).const_mul 2))
        (Filter.Eventually.of_forall hpoint)
      calc
        cSq n = ∫ ω, C n ω ^ 2 ∂disorderLaw := rfl
        _ ≤ ∫ ω, 2 * (C n ω - B n ω) ^ 2 + 2 * B n ω ^ 2 ∂disorderLaw := hraw
        _ = 2 * dSq n + 2 * bSq n := by
          rw [integral_add ((hD2 n).const_mul 2) ((hB2 n).const_mul 2),
            integral_const_mul, integral_const_mul]
    dsimp [K]
    nlinarith [hCbound, hDn, hBn]
  have hrootD : Tendsto (fun n => Real.sqrt (dSq n)) atTop (𝓝 0) := by
    have hD' : Tendsto dSq atTop (𝓝 0) := by simpa only [dSq] using hD
    have hcomp := Real.continuous_sqrt.continuousAt.tendsto.comp hD'
    change Tendsto (Real.sqrt ∘ dSq) atTop (𝓝 0)
    simpa only [Real.sqrt_zero] using hcomp
  have hrootVbound : ∀ᶠ n : ℕ in atTop,
      Real.sqrt (2 * cSq n + 2 * bSq n) ≤ Real.sqrt K := by
    filter_upwards [hVbound] with n hn
    exact Real.sqrt_le_sqrt hn
  have hdiff0 : Tendsto (fun n => cSq n - bSq n) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hsmall := (Metric.tendsto_nhds.mp hrootD) (ε / (Real.sqrt K + 1)) (by positivity)
    filter_upwards [hsmall, hrootVbound] with n hn hVn
    have hbound := hdiffBound n
    have habs : |cSq n - bSq n| < ε := by
      have hright :
          Real.sqrt (dSq n) * Real.sqrt (2 * cSq n + 2 * bSq n) < ε := by
        calc
          _ ≤ Real.sqrt (dSq n) * Real.sqrt K :=
            mul_le_mul_of_nonneg_left hVn (Real.sqrt_nonneg _)
          _ < ε := by
            have hn' : Real.sqrt (dSq n) < ε / (Real.sqrt K + 1) := by
              simpa only [Real.dist_eq, abs_of_nonneg (Real.sqrt_nonneg _), sub_zero] using hn
            have hn'' := (lt_div_iff₀ (by positivity : 0 < Real.sqrt K + 1)).mp hn'
            have hrootNonneg := Real.sqrt_nonneg (dSq n)
            nlinarith [Real.sqrt_nonneg K]
      exact hbound.trans_lt hright
    simpa only [Real.dist_eq, sub_zero] using habs
  have hC : Tendsto cSq atTop (𝓝 L) := by
    have hsum := hdiff0.add hB
    convert hsum using 1 <;> simp [cSq, bSq]
  have hidentity : (fun n => ∫ ω, (A n ω - B n ω) ^ 2 ∂disorderLaw) =
      fun n => (∫ ω, A n ω ^ 2 ∂disorderLaw - cSq n) + dSq n := by
    funext n
    simpa only [cSq, dSq] using hproj n
  rw [hidentity]
  have hresult : Tendsto
      (fun n => (∫ ω, A n ω ^ 2 ∂disorderLaw - cSq n) + dSq n) atTop (𝓝 0) := by
    have hAC : Tendsto
        (fun n => ∫ ω, A n ω ^ 2 ∂disorderLaw - cSq n) atTop (𝓝 0) := by
      have h := hA.sub hC
      simpa only [sub_self] using h
    have hsum := hAC.add hD
    simpa only [zero_add, dSq] using hsum
  exact hresult

end Critical2DKPZ.SHF.TimeContinuity

end
