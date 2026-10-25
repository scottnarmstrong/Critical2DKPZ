/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.FutureProfiles.EnergySeminorm
public import Critical2DKPZ.FutureProfiles.HelperExpansions
public import Critical2DKPZ.FutureProfiles.HelperIdentities
public import Critical2DKPZ.FutureProfiles.OpenCorrectorEnergy
public import Critical2DKPZ.FutureProfiles.SplitBoundInputs
public import Critical2DKPZ.FutureProfiles.WalkBounds
public import Critical2DKPZ.OnePoint.BlockRatioOriginalLawGoodSet
import Mathlib.Tactic

/-! # The block profile estimates -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators ENNReal
open ProbabilityTheory

namespace Critical2DKPZ.FutureProfiles

open Critical2DKPZ.Blocks Critical2DKPZ.OnePoint Critical2DKPZ.Polymer

/-- The square root of the future energy of a finite sum of profiles is bounded by the sum of
the individual square roots. -/
theorem sqrt_futureEnergy_finset_sum_le {ι : Type*} (β : ℝ) (a b : ℕ)
    (A : Finset Site) (I : Finset ι) (η : ι → Site → ℝ)
    (hsupp : ∀ i ∈ I, ∀ y ∉ A, η i y = 0) :
    Real.sqrt (futureEnergy β a b (∑ i ∈ I, η i)) ≤
      ∑ i ∈ I, Real.sqrt (futureEnergy β a b (η i)) := by
  classical
  have hzero : futureEnergy β a b (0 : Site → ℝ) = 0 := by
    simpa using futureEnergy_smul β a b 0 (0 : Site → ℝ) A (by simp)
  induction I using Finset.induction_on with
  | empty =>
      simp [hzero]
  | @insert i I hi ih =>
      have hsumProfile : (∑ j ∈ insert i I, η j) = η i + ∑ j ∈ I, η j := by
        ext y
        simp [Finset.sum_insert, hi]
      have hsumSupport : ∀ y ∉ A, (∑ j ∈ I, η j) y = 0 := by
        intro y hy
        classical
        simp only [Finset.sum_apply]
        apply Finset.sum_eq_zero
        intro j hj
        exact hsupp j (Finset.mem_insert_of_mem hj) y hy
      have hsuppTail : ∀ j ∈ I, ∀ y ∉ A, η j y = 0 := by
        intro j hj y hy
        exact hsupp j (Finset.mem_insert_of_mem hj) y hy
      rw [hsumProfile, Finset.sum_insert hi]
      calc
        Real.sqrt (futureEnergy β a b (η i + ∑ j ∈ I, η j)) ≤
            Real.sqrt (futureEnergy β a b (η i)) +
              Real.sqrt (futureEnergy β a b (∑ j ∈ I, η j)) :=
          sqrt_futureEnergy_add_le β a b (η i) (∑ j ∈ I, η j) A
            (fun y hy => hsupp i (Finset.mem_insert_self i I) y hy) hsumSupport
        _ ≤ Real.sqrt (futureEnergy β a b (η i)) +
            ∑ j ∈ I, Real.sqrt (futureEnergy β a b (η j)) := by
          exact add_le_add_right (ih hsuppTail) _

private theorem futureEnergy_finset_sum_le_weighted {ι : Type*} (β : ℝ) (a b : ℕ)
    (A : Finset Site) (I : Finset ι) (η : ι → Site → ℝ) (q : ι → ℝ)
    (hsupp : ∀ i ∈ I, ∀ y ∉ A, η i y = 0) (hq : ∀ i ∈ I, 0 < q i) :
    futureEnergy β a b (∑ i ∈ I, η i) ≤
      (∑ i ∈ I, q i) * ∑ i ∈ I, futureEnergy β a b (η i) / q i := by
  classical
  have hzero : futureEnergy β a b (0 : Site → ℝ) = 0 := by
    simpa using futureEnergy_smul β a b 0 (0 : Site → ℝ) A (by simp)
  have hsqrt := sqrt_futureEnergy_finset_sum_le β a b A I η hsupp
  have hsumNonneg : 0 ≤ ∑ i ∈ I, Real.sqrt (futureEnergy β a b (η i)) :=
    Finset.sum_nonneg fun i hi => Real.sqrt_nonneg _
  have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _) hsumNonneg).2 hsqrt
  have hcs := Finset.sq_sum_div_le_sum_sq_div I
    (fun i => Real.sqrt (futureEnergy β a b (η i))) (g := q) hq
  have hcs' :
      (∑ i ∈ I, Real.sqrt (futureEnergy β a b (η i))) ^ 2 /
          (∑ i ∈ I, q i) ≤
        ∑ i ∈ I, futureEnergy β a b (η i) / q i := by
    have hsumEq :
        (∑ i ∈ I, (Real.sqrt (futureEnergy β a b (η i))) ^ 2 / q i) =
          ∑ i ∈ I, futureEnergy β a b (η i) / q i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Real.sq_sqrt (futureEnergy_nonneg β a b (η i))]
    simpa only [hsumEq] using hcs
  by_cases hI : I.Nonempty
  · have hqsum : 0 < ∑ i ∈ I, q i := Finset.sum_pos hq hI
    calc
      futureEnergy β a b (∑ i ∈ I, η i) =
          Real.sqrt (futureEnergy β a b (∑ i ∈ I, η i)) ^ 2 := by
            rw [Real.sq_sqrt (futureEnergy_nonneg β a b (∑ i ∈ I, η i))]
      _ ≤ (∑ i ∈ I, Real.sqrt (futureEnergy β a b (η i))) ^ 2 := hsq
      _ ≤ (∑ i ∈ I, q i) *
          ∑ i ∈ I, futureEnergy β a b (η i) / q i :=
            by simpa only [mul_comm] using (div_le_iff₀ hqsum).mp hcs'
  · have hEmpty : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
    subst I
    simp [hzero]

private theorem measureReal_abs_gt_half_sq_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (G : Set Ω)
    (hf : Measurable f) (hfi : IntegrableOn (fun ω => f ω ^ 2) G μ) :
    (μ (G ∩ {ω | (1 / 2 : ℝ) < |f ω|})).toReal ≤
      4 * ∫ ω in G, f ω ^ 2 ∂μ := by
  let bad : Set Ω := {ω | (1 / 2 : ℝ) < |f ω|}
  have hbad : MeasurableSet bad := by
    dsimp [bad]
    exact measurableSet_lt measurable_const hf.abs
  have hfourMeas : Measurable (fun ω => ENNReal.ofReal (f ω ^ 2)) :=
    ENNReal.measurable_ofReal.comp (hf.pow_const 2)
  have hsubset : bad ⊆ {ω | ENNReal.ofReal (1 / 4 : ℝ) ≤
      ENNReal.ofReal (f ω ^ 2)} := by
    intro ω hω
    dsimp [bad] at hω
    have habs : 0 ≤ |f ω| := abs_nonneg _
    have hprod : 0 < (|f ω| - 1 / 2) * (|f ω| + 1 / 2) :=
      mul_pos (by linarith only [hω]) (by positivity)
    have hsquare : (1 / 4 : ℝ) < |f ω| ^ 2 := by nlinarith only [hprod]
    have hfour : (1 / 4 : ℝ) ≤ f ω ^ 2 := by
      simpa only [sq_abs] using hsquare.le
    exact ENNReal.ofReal_le_ofReal hfour
  have hmarkov := (measure_mono (μ := μ.restrict G) hsubset).trans
    (MeasureTheory.meas_ge_le_lintegral_div (μ := μ.restrict G)
      hfourMeas.aemeasurable (by norm_num) (by simp))
  have hrestrict : (μ.restrict G) bad = μ (G ∩ bad) := by
    rw [Measure.restrict_apply hbad]
    congr 1
    ext ω
    simp [and_comm]
  have hlin : ENNReal.ofReal (∫ ω in G, f ω ^ 2 ∂μ) =
      ∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂μ.restrict G := by
    exact ofReal_integral_eq_lintegral_ofReal hfi
      (Eventually.of_forall fun ω => by positivity)
  have hnonneg : 0 ≤ ∫ ω in G, f ω ^ 2 ∂μ :=
    integral_nonneg_of_ae (Eventually.of_forall fun ω => by positivity)
  have hdivTop : ENNReal.ofReal (∫ ω in G, f ω ^ 2 ∂μ) /
      ENNReal.ofReal (1 / 4 : ℝ) ≠ ∞ :=
    ENNReal.div_ne_top ENNReal.ofReal_ne_top (by norm_num)
  have hmarkov' := hmarkov
  rw [← hlin] at hmarkov'
  have hreal := ENNReal.toReal_mono hdivTop hmarkov'
  calc
    (μ (G ∩ bad)).toReal = ((μ.restrict G) bad).toReal := by rw [hrestrict]
    _ ≤ (ENNReal.ofReal (∫ ω in G, f ω ^ 2 ∂μ) /
        ENNReal.ofReal (1 / 4 : ℝ)).toReal := hreal
    _ = 4 * ∫ ω in G, f ω ^ 2 ∂μ := by
      rw [ENNReal.toReal_div, ENNReal.toReal_ofReal hnonneg,
        ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 4)]
      norm_num [div_eq_mul_inv]
      ring

/-- The complement of the profile good set has probability at most `B + 4 * R`, from the block bound
`B` and the ratio second-moment bound `R`. -/
theorem profileGoodSet_compl_measure_le (β : ℝ) (t : ℕ → ℕ)
    (r s : ℕ) (ht : Monotone t) (hr : 1 ≤ r) (hrs : r ≤ s)
    (B R : ℝ)
    (hblock : (disorderLaw (blockGoodSet β t r s)ᶜ).toReal ≤ B)
    (hRatio : ∫ ω in blockGoodSet β t r s,
        (blockRatio β t r s ω - 1) ^ 2 ∂disorderLaw ≤ R) :
    (disorderLaw (profileGoodSet β t r s)ᶜ).toReal ≤ B + 4 * R := by
  let G := blockGoodSet β t r s
  let f : Disorder → ℝ := fun ω => blockRatio β t r s ω - 1
  let bad : Set Disorder := {ω | (1 / 2 : ℝ) < |f ω|}
  have hden : Measurable (fun ω => ∏ i ∈ Finset.Icc r s, blockMass β t i ω) := by
    apply Finset.measurable_prod
    intro i hi
    exact (measurable_blockMass β t i).mono (Gaussian.disorderBlock_le _ _) le_rfl
  have hRatioMeas : Measurable (blockRatio β t r s) := by
    unfold blockRatio
    exact (Polymer.measurable_smoothedP2Plane β (t (r - 1)) (t s) 0).div hden
  have hf : Measurable f := by
    dsimp [f]
    exact hRatioMeas.sub measurable_const
  have hcomp : (profileGoodSet β t r s)ᶜ = Gᶜ ∪ (G ∩ bad) := by
    ext ω
    by_cases hω : ω ∈ G
    · simp [G, bad, f, profileGoodSet, hω, not_le]
    · simp [G, bad, f, profileGoodSet, hω]
  have htail : (disorderLaw (G ∩ bad)).toReal ≤
      4 * ∫ ω in G, f ω ^ 2 ∂disorderLaw := by
    exact measureReal_abs_gt_half_sq_le disorderLaw f G hf
      (OnePoint.integrableOn_blockRatio_sub_one_sq β ht hr hrs)
  calc
    (disorderLaw (profileGoodSet β t r s)ᶜ).toReal =
        (disorderLaw (Gᶜ ∪ (G ∩ bad))).toReal := by rw [hcomp]
    _ ≤ (disorderLaw Gᶜ).toReal + (disorderLaw (G ∩ bad)).toReal :=
      measureReal_union_le _ _
    _ ≤ B + 4 * (∫ ω in G, (blockRatio β t r s ω - 1) ^ 2 ∂disorderLaw) := by
      exact add_le_add hblock (by simpa [G, f] using htail)
    _ ≤ B + 4 * R := by
      exact add_le_add_right (mul_le_mul_of_nonneg_left hRatio (by norm_num)) B

/-- The future energy of a finite sum is integrable on `G` (from integrability of the summands'
energies) and its set integral is at most `(∑ q) * ∑ (∫ energy of ηᵢ) / qᵢ`. -/
theorem integrableOn_futureEnergy_finset_sum_le_weighted {ι : Type*}
    (β : ℝ) {a b : ℕ} (hab : a ≤ b) (A : Finset Site) (I : Finset ι)
    (G : Set Disorder) (η : ι → Disorder → Site → ℝ) (q : ι → ℝ)
    (hsupp : ∀ i ∈ I, ∀ ω y, y ∉ A → η i ω y = 0)
    (hmeas : ∀ i ∈ I, ∀ y, Measurable[disorderPast a] (η i · y))
    (hq : ∀ i ∈ I, 0 < q i)
    (hEi : ∀ i ∈ I, IntegrableOn (fun ω => futureEnergy β a b (η i ω)) G disorderLaw) :
    IntegrableOn (fun ω => futureEnergy β a b (fun y => ∑ i ∈ I, η i ω y)) G disorderLaw ∧
      ∫ ω in G, futureEnergy β a b (fun y => ∑ i ∈ I, η i ω y) ∂disorderLaw ≤
        (∑ i ∈ I, q i) * ∑ i ∈ I,
          (∫ ω in G, futureEnergy β a b (η i ω) ∂disorderLaw) / q i := by
  classical
  let energySum : Disorder → ℝ := fun ω =>
    futureEnergy β a b (fun y => ∑ i ∈ I, η i ω y)
  let weightedTerms : Disorder → ℝ := fun ω =>
    ∑ i ∈ I, futureEnergy β a b (η i ω) / q i
  let qsum : ℝ := ∑ i ∈ I, q i
  have hsumSupport (ω : Disorder) (y : Site) (hy : y ∉ A) :
      (fun y => ∑ i ∈ I, η i ω y) y = 0 := by
    simp only
    apply Finset.sum_eq_zero
    intro i hi
    exact hsupp i hi ω y hy
  have hsumMeas (y : Site) :
      Measurable[disorderPast a] (fun ω => ∑ i ∈ I, η i ω y) := by
    exact Finset.measurable_sum _ fun i hi => hmeas i hi y
  have henergyMeasPast :
      Measurable[disorderPast a] energySum := by
    dsimp [energySum]
    exact measurable_futureEnergy β hab _ A hsumSupport hsumMeas
  have henergyMeas : Measurable energySum :=
    henergyMeasPast.mono (by
      rw [← Gaussian.disorderBlock_zero a]
      exact Gaussian.disorderBlock_le 0 a) le_rfl
  have hweightedInt : Integrable weightedTerms (disorderLaw.restrict G) := by
    dsimp [weightedTerms]
    apply integrable_finsetSum
    intro i hi
    exact (hEi i hi).div_const (q i)
  have hqsumNonneg : 0 ≤ qsum := by
    dsimp [qsum]
    exact Finset.sum_nonneg fun i hi => (hq i hi).le
  have hrightInt : Integrable (fun ω => weightedTerms ω * qsum)
      (disorderLaw.restrict G) := hweightedInt.mul_const qsum
  have hpoint (ω : Disorder) : energySum ω ≤ weightedTerms ω * qsum := by
    have hprofile : (∑ i ∈ I, fun y => η i ω y) = fun y => ∑ i ∈ I, η i ω y := by
      ext y
      simp
    have h := futureEnergy_finset_sum_le_weighted β a b A I
      (fun i y => η i ω y) q (fun i hi y hy => hsupp i hi ω y hy) hq
    simpa [energySum, weightedTerms, qsum, hprofile, mul_comm] using h
  have htermsNonneg (ω : Disorder) : 0 ≤ weightedTerms ω := by
    dsimp [weightedTerms]
    apply Finset.sum_nonneg
    intro i hi
    exact div_nonneg (futureEnergy_nonneg β a b (η i ω)) (hq i hi).le
  have hrightNonneg (ω : Disorder) : 0 ≤ weightedTerms ω * qsum :=
    mul_nonneg (htermsNonneg ω) hqsumNonneg
  have henergyNonneg (ω : Disorder) : 0 ≤ energySum ω := by
    exact futureEnergy_nonneg β a b _
  have henergyInt : Integrable energySum (disorderLaw.restrict G) := by
    apply hrightInt.mono' henergyMeas.aestronglyMeasurable
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (henergyNonneg ω)]
    exact hpoint ω
  have hmono := integral_mono_ae henergyInt hrightInt
    (Filter.Eventually.of_forall hpoint)
  have hweightedIntegral :
      ∫ ω, weightedTerms ω ∂disorderLaw.restrict G =
        ∑ i ∈ I, (∫ ω in G, futureEnergy β a b (η i ω) ∂disorderLaw) / q i := by
    dsimp [weightedTerms]
    rw [integral_finsetSum _ (fun i hi => (hEi i hi).div_const (q i))]
    apply Finset.sum_congr rfl
    intro i hi
    calc
      ∫ ω in G, futureEnergy β a b (η i ω) / q i ∂disorderLaw =
          ∫ ω in G, futureEnergy β a b (η i ω) * (q i)⁻¹ ∂disorderLaw := by
            simp only [div_eq_mul_inv]
      _ = (∫ ω in G, futureEnergy β a b (η i ω) ∂disorderLaw) * (q i)⁻¹ :=
        by
          exact integral_mul_const _ _
      _ = _ := by rw [← div_eq_mul_inv]
  refine ⟨henergyInt, ?_⟩
  have hmono' :
      ∫ ω in G, energySum ω ∂disorderLaw ≤
        qsum * (∑ i ∈ I,
          (∫ ω in G, futureEnergy β a b (η i ω) ∂disorderLaw) / q i) := by
    calc
      ∫ ω in G, energySum ω ∂disorderLaw =
          ∫ ω, energySum ω ∂disorderLaw.restrict G := rfl
      _ ≤ ∫ ω, weightedTerms ω * qsum ∂disorderLaw.restrict G := hmono
      _ = (∫ ω, weightedTerms ω ∂disorderLaw.restrict G) * qsum := by
        exact integral_mul_const _ _
      _ = qsum * (∑ i ∈ I,
          (∫ ω in G, futureEnergy β a b (η i ω) ∂disorderLaw) / q i) := by
        rw [hweightedIntegral]
        ring
  simpa [energySum] using hmono'

private theorem sum_Icc_pow_reverse_le_inv_one_sub {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) (s : ℕ) :
    ∑ u ∈ Finset.Icc 0 s, θ ^ (s - u) ≤ 1 / (1 - θ) := by
  have hden : 0 < 1 - θ := sub_pos.mpr hθ1
  induction s with
  | zero =>
      simp only [Finset.Icc_self, Finset.sum_singleton, Nat.sub_self, pow_zero]
      exact (le_div_iff₀ hden).2 (by linarith)
  | succ s ih =>
      have hsplit :
          ∑ u ∈ Finset.Icc 0 (s + 1), θ ^ (s + 1 - u) =
            (∑ u ∈ Finset.Icc 0 s, θ ^ (s + 1 - u)) + 1 := by
        rw [Finset.sum_Icc_succ_top (by omega : 0 ≤ s + 1)]
        simp
      have hprefix :
          ∑ u ∈ Finset.Icc 0 s, θ ^ (s + 1 - u) =
            θ * ∑ u ∈ Finset.Icc 0 s, θ ^ (s - u) := by
        calc
          ∑ u ∈ Finset.Icc 0 s, θ ^ (s + 1 - u) =
              ∑ u ∈ Finset.Icc 0 s, θ * θ ^ (s - u) := by
                apply Finset.sum_congr rfl
                intro u hu
                have hu' := Finset.mem_Icc.mp hu
                rw [show s + 1 - u = (s - u) + 1 by omega, pow_succ]
                ring
          _ = θ * ∑ u ∈ Finset.Icc 0 s, θ ^ (s - u) := by rw [Finset.mul_sum]
      calc
        ∑ u ∈ Finset.Icc 0 (s + 1), θ ^ (s + 1 - u) =
            θ * ∑ u ∈ Finset.Icc 0 s, θ ^ (s - u) + 1 := by rw [hsplit, hprefix]
        _ ≤ θ * (1 / (1 - θ)) + 1 := by gcongr
        _ = 1 / (1 - θ) := by field_simp [ne_of_gt hden]; ring

/-- For `0 ≤ θ < 1`, the geometric sum `∑ u ∈ Icc r s, θ ^ (s - u)` is at most `1 / (1 - θ)`. -/
theorem sum_Icc_pow_reverse_le_inv_one_sub_of_le {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {r s : ℕ} :
    ∑ u ∈ Finset.Icc r s, θ ^ (s - u) ≤ 1 / (1 - θ) := by
  calc
    ∑ u ∈ Finset.Icc r s, θ ^ (s - u) ≤
        ∑ u ∈ Finset.Icc 0 s, θ ^ (s - u) := by
          have hsubset : Finset.Icc r s ⊆ Finset.Icc 0 s := by
            intro u hu
            exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, (Finset.mem_Icc.mp hu).2⟩
          exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
            (by intro u hu hnot; exact pow_nonneg hθ0 _)
    _ ≤ 1 / (1 - θ) := sum_Icc_pow_reverse_le_inv_one_sub hθ0 hθ1 s

/-- The common correction's future energy is integrable on the block good set, with set integral at
most `|C₀| / (1 - θ) ^ 2 / (K - s)`, from the open-corrector energy bounds. -/
theorem commonCorrection_integral_energy_le_of_openCorrector
    (β : ℝ) (t : ℕ → ℕ) (N r s K : ℕ) (ht : Monotone t)
    (hr : 1 ≤ r) (hsK : s + 2 ≤ K) (hts : t s ≤ N)
    (θ C₀ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hOpen : ∀ u : ℕ, r ≤ u → u ≤ s →
      ∫ ω in blockGoodSet β t u s,
        futureEnergy β (t s) N (openCorrector β t u s ω) ∂disorderLaw ≤
          C₀ * θ ^ (2 * (s - u)) / ((K : ℝ) - u)) :
    IntegrableOn (fun ω => futureEnergy β (t s) N (commonCorrection β t r s ω))
      (blockGoodSet β t r s) disorderLaw ∧
    ∫ ω in blockGoodSet β t r s,
        futureEnergy β (t s) N (commonCorrection β t r s ω) ∂disorderLaw ≤
      |C₀| / (1 - θ) ^ 2 / ((K : ℝ) - s) := by
  classical
  let I := Finset.Icc r s
  let G := blockGoodSet β t r s
  let A := I.biUnion (fun u => openCorrectorNumeratorSupport t u s)
  let η : ℕ → Disorder → Site → ℝ := fun u ω y => openCorrector β t u s ω y
  let q : ℕ → ℝ := fun u => θ ^ (s - u)
  have hsupp (u : ℕ) (hu : u ∈ I) (ω : Disorder) (y : Site) (hy : y ∉ A) :
      η u ω y = 0 := by
    have hyu : y ∉ openCorrectorNumeratorSupport t u s := by
      intro hymem
      exact hy (Finset.mem_biUnion.mpr ⟨u, hu, hymem⟩)
    dsimp [η, openCorrector]
    rw [openCorrectorNumerator_eq_zero_of_not_mem_support β t u s ω y hyu, zero_div]
  have hmeas (u : ℕ) (hu : u ∈ I) (y : Site) :
      Measurable[disorderPast (t s)] (η u · y) := by
    have hu' := Finset.mem_Icc.mp hu
    exact measurable_openCorrector_on_past β t ht u s (by omega) hu'.2 y
  have hq (u : ℕ) (hu : u ∈ I) : 0 < q u := by
    dsimp [q]
    exact pow_pos hθ0 _
  have hDs : 0 < (K : ℝ) - s := by
    have hNat : 0 < K - s := by omega
    rw [← Nat.cast_sub (by omega : s ≤ K)]
    exact_mod_cast hNat
  have hgeom := sum_Icc_pow_reverse_le_inv_one_sub_of_le
    hθ0.le hθ1 (r := r) (s := s)
  have hEi (u : ℕ) (hu : u ∈ I) :
      IntegrableOn (fun ω => futureEnergy β (t s) N (η u ω)) G disorderLaw := by
    have hu' := Finset.mem_Icc.mp hu
    have hbase := integrableOn_futureEnergy_openCorrector β t N u s ht (by omega)
      hu'.2 hts
    have hsubset : G ⊆ blockGoodSet β t u s := by
      intro ω hω
      simp only [G, blockGoodSet, Set.mem_ofPred_eq] at hω ⊢
      intro j hj
      apply hω j
      simp only [Finset.mem_Icc] at hj ⊢
      omega
    exact hbase.mono_set hsubset
  have hEiBound (u : ℕ) (hu : u ∈ I) :
      ∫ ω in G, futureEnergy β (t s) N (η u ω) ∂disorderLaw ≤
        |C₀| * θ ^ (2 * (s - u)) / ((K : ℝ) - u) := by
    have hu' := Finset.mem_Icc.mp hu
    have hbase := integrableOn_futureEnergy_openCorrector β t N u s ht (by omega)
      hu'.2 hts
    have hsubset : G ⊆ blockGoodSet β t u s := by
      intro ω hω
      simp only [G, blockGoodSet, Set.mem_ofPred_eq] at hω ⊢
      intro j hj
      apply hω j
      simp only [Finset.mem_Icc] at hj ⊢
      omega
    have hnonneg : 0 ≤ᵐ[disorderLaw.restrict (blockGoodSet β t u s)]
        (fun ω => futureEnergy β (t s) N (openCorrector β t u s ω)) :=
      Filter.Eventually.of_forall fun ω => futureEnergy_nonneg β (t s) N _
    have hrestrict := setIntegral_mono_set hbase hnonneg
      (Filter.Eventually.of_forall fun ω hω => hsubset hω)
    have hOpenProfileEnergyInput := hOpen u hu'.1 hu'.2
    have hDen : 0 < (K : ℝ) - u := by
      have hNat : 0 < K - u := by omega
      rw [← Nat.cast_sub (by omega : u ≤ K)]
      exact_mod_cast hNat
    calc
      ∫ ω in G, futureEnergy β (t s) N (η u ω) ∂disorderLaw ≤
          C₀ * θ ^ (2 * (s - u)) / ((K : ℝ) - u) := by
            simpa [G, η] using hrestrict.trans hOpenProfileEnergyInput
      _ ≤ |C₀| * θ ^ (2 * (s - u)) / ((K : ℝ) - u) := by
        apply div_le_div_of_nonneg_right _ hDen.le
        exact mul_le_mul_of_nonneg_right (le_abs_self C₀) (pow_nonneg hθ0.le _)
  have hEiDivBound (u : ℕ) (hu : u ∈ I) :
      (∫ ω in G, futureEnergy β (t s) N (η u ω) ∂disorderLaw) / q u ≤
        |C₀| * q u / ((K : ℝ) - s) := by
    have hu' := Finset.mem_Icc.mp hu
    have hDi : 0 < (K : ℝ) - u := by
      have hNat : 0 < K - u := by omega
      rw [← Nat.cast_sub (by omega : u ≤ K)]
      exact_mod_cast hNat
    have hDle : (K : ℝ) - s ≤ (K : ℝ) - u := by
      rw [← Nat.cast_sub (by omega : s ≤ K), ← Nat.cast_sub (by omega : u ≤ K)]
      exact_mod_cast Nat.sub_le_sub_left hu'.2 K
    calc
      (∫ ω in G, futureEnergy β (t s) N (η u ω) ∂disorderLaw) / q u ≤
          (|C₀| * θ ^ (2 * (s - u)) / ((K : ℝ) - u)) / q u :=
        div_le_div_of_nonneg_right (hEiBound u hu) (hq u hu).le
      _ = |C₀| * q u / ((K : ℝ) - u) := by
        dsimp [q]
        have hpower : 2 * (s - u) = (s - u) + (s - u) := by omega
        rw [hpower, pow_add]
        field_simp [ne_of_gt (hq u hu), ne_of_gt hDi]
      _ ≤ |C₀| * q u / ((K : ℝ) - s) := by
        apply div_le_div_of_nonneg_left
        · positivity
        · exact hDs
        · exact hDle
  have hweightedSumBound :
      (∑ u ∈ I, (∫ ω in G, futureEnergy β (t s) N (η u ω) ∂disorderLaw) / q u) ≤
        (|C₀| / ((K : ℝ) - s)) * ∑ u ∈ I, q u := by
    calc
      _ ≤ ∑ u ∈ I, (|C₀| * q u / ((K : ℝ) - s)) :=
        Finset.sum_le_sum fun u hu => hEiDivBound u hu
      _ = (|C₀| / ((K : ℝ) - s)) * ∑ u ∈ I, q u := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u hu
        ring
  have hweightedSumBound' :
      (∑ u ∈ I, (∫ ω in G, futureEnergy β (t s) N (η u ω) ∂disorderLaw) / q u) ≤
        (|C₀| / ((K : ℝ) - s)) * (1 / (1 - θ)) := by
    calc
      _ ≤ (|C₀| / ((K : ℝ) - s)) * ∑ u ∈ I, q u := hweightedSumBound
      _ ≤ (|C₀| / ((K : ℝ) - s)) * (1 / (1 - θ)) :=
        mul_le_mul_of_nonneg_left hgeom (by positivity)
  have hsum := integrableOn_futureEnergy_finset_sum_le_weighted β hts A I G η q
    hsupp hmeas hq hEi
  have hsumNonneg : 0 ≤
      ∑ u ∈ I, (∫ ω in G, futureEnergy β (t s) N (η u ω) ∂disorderLaw) / q u := by
    apply Finset.sum_nonneg
    intro u hu
    apply div_nonneg
    · exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun ω =>
        futureEnergy_nonneg β (t s) N (η u ω))
    · exact (hq u hu).le
  have hgeomNonneg : 0 ≤ 1 / (1 - θ) := by positivity
  have hsumBound :
      ∫ ω in G, futureEnergy β (t s) N (fun y => ∑ u ∈ I, η u ω y) ∂disorderLaw ≤
        |C₀| / (1 - θ) ^ 2 / ((K : ℝ) - s) := by
    calc
      _ ≤ (∑ u ∈ I, q u) *
          ∑ u ∈ I, (∫ ω in G, futureEnergy β (t s) N (η u ω) ∂disorderLaw) / q u := hsum.2
      _ ≤ (1 / (1 - θ)) *
          ((|C₀| / ((K : ℝ) - s)) * (1 / (1 - θ))) := by
        exact mul_le_mul hgeom hweightedSumBound' hsumNonneg hgeomNonneg
      _ = |C₀| / (1 - θ) ^ 2 / ((K : ℝ) - s) := by
        field_simp [ne_of_gt hDs, ne_of_gt (sub_pos.mpr hθ1)]
  constructor
  · exact hsum.1
  · exact hsumBound


/-- The block good set is measurable for the disorder in the block `(t (r - 1), t s]`. -/
theorem measurable_blockGoodSet_on_block (β : ℝ) (t : ℕ → ℕ)
    (ht : Monotone t) (r s : ℕ) :
    MeasurableSet[Gaussian.disorderBlock (t (r - 1)) (t s)]
      (blockGoodSet β t r s) := by
  let : MeasurableSpace Disorder := Gaussian.disorderBlock (t (r - 1)) (t s)
  have hblock (i : ℕ) (hi : i ∈ Finset.Icc r s) :
      Measurable[Gaussian.disorderBlock (t (r - 1)) (t s)] (blockMass β t i) := by
    have hi' := Finset.mem_Icc.mp hi
    have hstart : t (r - 1) ≤ t (i - 1) := ht (by omega)
    have hend : t i ≤ t s := ht hi'.2
    exact (measurable_blockMass β t i).mono
      (Gaussian.disorderBlock_mono hstart hend) le_rfl
  have h : MeasurableSet[Gaussian.disorderBlock (t (r - 1)) (t s)]
      (⋂ i ∈ Finset.Icc r s, {ω | |blockMass β t i ω - 1| ≤ 1 / 2}) := by
    apply Finset.measurableSet_biInter
    intro i hi
    exact MeasurableSet.preimage measurableSet_Iic
      ((hblock i hi).sub measurable_const |>.abs)
  convert h using 1
  ext ω
  simp [blockGoodSet]

/-- The block ratio is measurable for the disorder in the block `(t (r - 1), t s]`. -/
theorem measurable_blockRatio_on_block (β : ℝ) (t : ℕ → ℕ)
    (ht : Monotone t) (r s : ℕ) (hrs : r ≤ s) :
    Measurable[Gaussian.disorderBlock (t (r - 1)) (t s)] (blockRatio β t r s) := by
  let : MeasurableSpace Disorder := Gaussian.disorderBlock (t (r - 1)) (t s)
  have hnum : Measurable[Gaussian.disorderBlock (t (r - 1)) (t s)]
      (smoothedP2Plane β (t (r - 1)) (t s) 0) :=
    Polymer.measurable_smoothedP2Plane_block β (t (r - 1)) (t s)
      (by exact ht (by omega)) 0
  have hden : Measurable[Gaussian.disorderBlock (t (r - 1)) (t s)]
      (fun ω => ∏ i ∈ Finset.Icc r s, blockMass β t i ω) := by
    apply Finset.measurable_prod
    intro i hi
    have hi' := Finset.mem_Icc.mp hi
    have hstart : t (r - 1) ≤ t (i - 1) := ht (by omega)
    have hend : t i ≤ t s := ht hi'.2
    exact (measurable_blockMass β t i).mono
      (Gaussian.disorderBlock_mono hstart hend) le_rfl
  unfold blockRatio
  exact hnum.div hden

private theorem measurable_discrepancyString_block_to_last (β : ℝ) (t : ℕ → ℕ)
    (ht : Monotone t) (u k v : ℕ) (huk : u + k - 1 ≤ v) (x y : Site) :
    Measurable[Gaussian.disorderBlock (t (u - 1)) (t v)]
      (fun ω => discrepancyString β t u k x y ω) := by
  let : MeasurableSpace Disorder := Gaussian.disorderBlock (t (u - 1)) (t v)
  induction k generalizing x y with
  | zero => exact measurable_const
  | succ k ih =>
      have huk' : u + k - 1 ≤ v := by omega
      have hstart : t (u - 1) ≤ t (u + k - 1) := ht (by omega)
      have hend : t (u + k) ≤ t v := ht (by omega)
      have hsub := Gaussian.disorderBlock_mono hstart hend
      have hlast (z : Site) :
          Measurable[Gaussian.disorderBlock (t (u - 1)) (t v)]
            (fun ω => blockDiscrepancy β t (u + k) z y ω) := by
        exact (measurable_blockDiscrepancy β t (u + k) (ht (by omega)) z y).mono
          hsub le_rfl
      change Measurable[Gaussian.disorderBlock (t (u - 1)) (t v)]
        (fun ω => ∑' z, discrepancyString β t u k x z ω *
          blockDiscrepancy β t (u + k) z y ω)
      exact Measurable.tsum fun z => (ih huk' x z).mul (hlast z)

/-- Each coordinate of the open corrector is measurable for the disorder in the block `(t (u - 1), t
s]`. -/
theorem measurable_openCorrector_on_block (β : ℝ) (t : ℕ → ℕ)
    (ht : Monotone t) (u s : ℕ) (hu : 1 ≤ u) (hus : u ≤ s) (y : Site) :
    Measurable[Gaussian.disorderBlock (t (u - 1)) (t s)]
      (fun ω => openCorrector β t u s ω y) := by
  let : MeasurableSpace Disorder := Gaussian.disorderBlock (t (u - 1)) (t s)
  have hnum : Measurable[Gaussian.disorderBlock (t (u - 1)) (t s)]
      (fun ω => openCorrectorNumerator β t u s ω y) := by
    have hstr (x : Site) :
        Measurable[Gaussian.disorderBlock (t (u - 1)) (t s)]
          (fun ω => discrepancyString β t u (s + 1 - u) x y ω) := by
      exact measurable_discrepancyString_block_to_last β t ht u (s + 1 - u) s
        (by omega) x y
    change Measurable[Gaussian.disorderBlock (t (u - 1)) (t s)]
      (fun ω => ∑' x, srwKernel (t (u - 1)) x *
        discrepancyString β t u (s + 1 - u) x y ω)
    exact Measurable.tsum fun x => (hstr x).const_mul _
  have hden : Measurable[Gaussian.disorderBlock (t (u - 1)) (t s)]
      (fun ω => ∏ i ∈ Finset.Icc u s, blockMass β t i ω) := by
    apply Finset.measurable_prod
    intro i hi
    have hi' := Finset.mem_Icc.mp hi
    have hstart : t (u - 1) ≤ t (i - 1) := ht (by omega)
    have hend : t i ≤ t s := ht hi'.2
    exact (measurable_blockMass β t i).mono
      (Gaussian.disorderBlock_mono hstart hend) le_rfl
  unfold openCorrector
  exact hnum.div hden

/-- The future energy of the open corrector is measurable for the disorder in the block `(t (u - 1),
t s]`. -/
theorem measurable_futureEnergy_openCorrector_on_block (β : ℝ)
    {t : ℕ → ℕ} (ht : Monotone t) {N u s : ℕ} (hu : 1 ≤ u)
    (hus : u ≤ s) (hts : t s ≤ N) :
    Measurable[Gaussian.disorderBlock (t (u - 1)) (t s)]
      (fun ω => futureEnergy β (t s) N (openCorrector β t u s ω)) := by
  let S := openCorrectorNumeratorSupport t u s
  have hsupp (ω : Disorder) (y : Site) (hy : y ∉ S) :
      openCorrector β t u s ω y = 0 := by
    unfold openCorrector
    rw [openCorrectorNumerator_eq_zero_of_not_mem_support β t u s ω y hy, zero_div]
  have hcoord (y : Site) :
      Measurable[Gaussian.disorderBlock (t (u - 1)) (t s)]
        (fun ω => openCorrector β t u s ω y) := by
    exact measurable_openCorrector_on_block β t ht u s hu hus y
  have hsum (ω : Disorder) : futureEnergy β (t s) N (openCorrector β t u s ω) =
      ∑ x ∈ S, ∑ y ∈ S,
        openCorrector β t u s ω x * openCorrector β t u s ω y *
          pairMoment β (N - t s) x y := by
    exact futureEnergy_eq_pairMoment_sum β hts _ S (hsupp ω)
  rw [show (fun ω => futureEnergy β (t s) N (openCorrector β t u s ω)) =
      fun ω => ∑ x ∈ S, ∑ y ∈ S,
        openCorrector β t u s ω x * openCorrector β t u s ω y *
          pairMoment β (N - t s) x y by funext ω; exact hsum ω]
  exact Finset.measurable_sum _ fun x hx => Finset.measurable_sum _ fun y hy =>
    ((hcoord x).mul (hcoord y)).mul_const _

private theorem openCorrectorTerm_integral_eq_of_prefixCoefficient
    (β : ℝ) (t : ℕ → ℕ) (N r s K u : ℕ) (ht : Monotone t)
    (hr : 1 ≤ r) (hru : r ≤ u) (hus : u ≤ s) (_hsK : s + 2 ≤ K)
    (hts : t s ≤ N) (c : Disorder → ℝ)
    (hcmeas : Measurable[Gaussian.disorderBlock (t (r - 1)) (t (u - 1))] c)
    (hcSqInt : IntegrableOn (fun ω => c ω ^ 2) (blockGoodSet β t r (u - 1)) disorderLaw) :
    IntegrableOn (fun ω => futureEnergy β (t s) N (fun y =>
      c ω * openCorrector β t u s ω y)) (blockGoodSet β t r s) disorderLaw ∧
    ∫ ω in blockGoodSet β t r s,
      futureEnergy β (t s) N (fun y => c ω * openCorrector β t u s ω y) ∂disorderLaw =
      (∫ ω in blockGoodSet β t r (u - 1), c ω ^ 2 ∂disorderLaw) *
      (∫ ω in blockGoodSet β t u s,
          futureEnergy β (t s) N (openCorrector β t u s ω) ∂disorderLaw) := by
  classical
  let G := blockGoodSet β t r s
  let G₁ := blockGoodSet β t r (u - 1)
  let G₂ := blockGoodSet β t u s
  let E : Disorder → ℝ := fun ω => futureEnergy β (t s) N (openCorrector β t u s ω)
  let F : Disorder → ℝ := Set.indicator G₁ (fun ω => c ω ^ 2)
  let H : Disorder → ℝ := Set.indicator G₂ E
  have hIcc : Finset.Icc r s = Finset.Icc r (u - 1) ∪ Finset.Icc u s := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hG : G = G₁ ∩ G₂ := by
    ext ω
    change (∀ i ∈ Finset.Icc r s, |blockMass β t i ω - 1| ≤ 1 / 2) ↔
      ((∀ i ∈ Finset.Icc r (u - 1), |blockMass β t i ω - 1| ≤ 1 / 2) ∧
        ∀ i ∈ Finset.Icc u s, |blockMass β t i ω - 1| ≤ 1 / 2)
    rw [hIcc]
    constructor
    · intro h
      constructor
      · intro i hi
        exact h i (Finset.mem_union_left _ hi)
      · intro i hi
        exact h i (Finset.mem_union_right _ hi)
    · rintro ⟨h₁, h₂⟩ i hi
      rcases Finset.mem_union.mp hi with hi | hi
      · exact h₁ i hi
      · exact h₂ i hi
  have hG₁meas : MeasurableSet[Gaussian.disorderBlock (t (r - 1)) (t (u - 1))] G₁ :=
    measurable_blockGoodSet_on_block β t ht r (u - 1)
  have hG₂meas : MeasurableSet[Gaussian.disorderBlock (t (u - 1)) (t s)] G₂ :=
    measurable_blockGoodSet_on_block β t ht u s
  have hEmeas : Measurable[Gaussian.disorderBlock (t (u - 1)) (t s)] E :=
    measurable_futureEnergy_openCorrector_on_block β ht (by omega) hus hts
  have hBlock₁Global := Gaussian.disorderBlock_le (t (r - 1)) (t (u - 1))
  have hBlock₂Global := Gaussian.disorderBlock_le (t (u - 1)) (t s)
  have hG₁global : MeasurableSet G₁ := hBlock₁Global G₁ hG₁meas
  have hG₂global : MeasurableSet G₂ := hBlock₂Global G₂ hG₂meas
  have hEglobal : Measurable E := hEmeas.mono hBlock₂Global le_rfl
  have hFmeas : Measurable[Gaussian.disorderBlock (t (r - 1)) (t (u - 1))] F := by
    change Measurable[Gaussian.disorderBlock (t (r - 1)) (t (u - 1))]
      (Set.indicator G₁ (fun ω => c ω ^ 2))
    exact (hcmeas.pow_const 2).indicator hG₁meas
  have hHmeas : Measurable[Gaussian.disorderBlock (t (u - 1)) (t s)] H := by
    change Measurable[Gaussian.disorderBlock (t (u - 1)) (t s)] (Set.indicator G₂ E)
    exact hEmeas.indicator hG₂meas
  have hFglobal : Measurable F := hFmeas.mono hBlock₁Global le_rfl
  have hHglobal : Measurable H := hHmeas.mono hBlock₂Global le_rfl
  have hFint : Integrable F disorderLaw := hcSqInt.integrable_indicator hG₁global
  have hEintOn : IntegrableOn E G₂ disorderLaw :=
    integrableOn_futureEnergy_openCorrector β t N u s ht (by omega) hus hts
  have hHint : Integrable H disorderLaw := hEintOn.integrable_indicator hG₂global
  have hind : IndepFun F H disorderLaw := by
    rw [IndepFun_iff]
    intro X Y hX hY
    exact (Indep_iff _ _ _).1
      (Gaussian.indep_disorderBlock_of_le (m := t (r - 1)) (n := t (u - 1))
        (a := t (u - 1)) (b := t s) le_rfl) X Y
      (hFmeas.comap_le X hX) (hHmeas.comap_le Y hY)
  have hprodInt : Integrable (fun ω => F ω * H ω) disorderLaw :=
    hind.integrable_mul hFint hHint
  have hsupport : ∀ ω y, y ∉ openCorrectorNumeratorSupport t u s →
      openCorrector β t u s ω y = 0 := by
    intro ω y hy
    unfold openCorrector
    rw [openCorrectorNumerator_eq_zero_of_not_mem_support β t u s ω y hy, zero_div]
  have hscale (ω : Disorder) :
      futureEnergy β (t s) N (fun y => c ω * openCorrector β t u s ω y) =
        c ω ^ 2 * E ω := by
    have h := futureEnergy_smul β (t s) N (c ω) (openCorrector β t u s ω)
      (openCorrectorNumeratorSupport t u s) (hsupport ω)
    have hprofile : (fun y => c ω * openCorrector β t u s ω y) =
        c ω • openCorrector β t u s ω := by
      funext y
      rfl
    rw [hprofile]
    exact h
  have hprodEq : (fun ω => F ω * H ω) = Set.indicator G (fun ω =>
      futureEnergy β (t s) N (fun y => c ω * openCorrector β t u s ω y)) := by
    funext ω
    by_cases hω : ω ∈ G
    · have hpair : ω ∈ G₁ ∩ G₂ := by
        rw [← hG]
        exact hω
      rcases hpair with ⟨hω₁, hω₂⟩
      simp only [F, H, Set.indicator_of_mem hω₁, Set.indicator_of_mem hω₂,
        Set.indicator_of_mem hω]
      rw [← hscale ω]
    · have hnot : ¬ (ω ∈ G₁ ∧ ω ∈ G₂) := by
        intro hpair
        apply hω
        rw [hG]
        exact hpair
      rcases not_and_or.mp hnot with hω₁ | hω₂
      · simp [F, H, Set.indicator, G, hω, hω₁]
      · simp [F, H, Set.indicator, G, hω, hω₂]
  have hGmeasBlock : MeasurableSet[Gaussian.disorderBlock (t (r - 1)) (t s)] G :=
    measurable_blockGoodSet_on_block β t ht r s
  have hGglobal : MeasurableSet G :=
    Gaussian.disorderBlock_le (t (r - 1)) (t s) G hGmeasBlock
  have hprodEqAE : (fun ω => F ω * H ω) =ᵐ[disorderLaw]
      Set.indicator G (fun ω => futureEnergy β (t s) N
        (fun y => c ω * openCorrector β t u s ω y)) :=
    Filter.Eventually.of_forall fun ω => congrFun hprodEq ω
  have hEqOn : (fun ω => F ω * H ω) =ᵐ[disorderLaw.restrict G]
      (fun ω => futureEnergy β (t s) N (fun y => c ω * openCorrector β t u s ω y)) := by
    filter_upwards [ae_restrict_mem hGglobal] with ω hω
    simpa [hω] using congrFun hprodEq ω
  have htermInt : IntegrableOn (fun ω => futureEnergy β (t s) N
      (fun y => c ω * openCorrector β t u s ω y)) G disorderLaw :=
    hprodInt.integrableOn.congr hEqOn
  refine ⟨htermInt, ?_⟩
  calc
    ∫ ω in G, futureEnergy β (t s) N (fun y => c ω * openCorrector β t u s ω y)
        ∂disorderLaw = ∫ ω, F ω * H ω ∂disorderLaw := by
      calc
        _ = ∫ ω, Set.indicator G (fun ω => futureEnergy β (t s) N
              (fun y => c ω * openCorrector β t u s ω y)) ω ∂disorderLaw :=
            (integral_indicator hGglobal).symm
        _ = ∫ ω, F ω * H ω ∂disorderLaw := integral_congr_ae hprodEqAE.symm
    _ = (∫ ω, F ω ∂disorderLaw) * ∫ ω, H ω ∂disorderLaw :=
      hind.integral_fun_mul_eq_mul_integral hFglobal.aestronglyMeasurable
        hHglobal.aestronglyMeasurable
    _ = (∫ ω in G₁, c ω ^ 2 ∂disorderLaw) *
        (∫ ω in G₂, E ω ∂disorderLaw) := by
      simpa [F, H] using congrArg₂ (fun x y : ℝ => x * y)
        (integral_indicator hG₁global) (integral_indicator hG₂global)

/-- The future energy of (block ratio minus one) times the open corrector is integrable on the block
good set, with set integral at most `|C₁| * |C₀| * θ ^ (2 * (s - u)) / (K - s) ^ 2`, from the ratio
and open-corrector bounds. -/
theorem ratioFluctuationOpenCorrectorTerm_integral_le
    (β : ℝ) (t : ℕ → ℕ) (N r s K u : ℕ) (ht : Monotone t)
    (hr : 1 ≤ r) (hru : r ≤ u) (hus : u ≤ s) (hsK : s + 2 ≤ K)
    (hts : t s ≤ N) (C₀ C₁ θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hRatio : r < u →
      ∫ ω in blockGoodSet β t r (u - 1),
        (blockRatio β t r (u - 1) ω - 1) ^ 2 ∂disorderLaw ≤
          C₁ / ((K : ℝ) - (u - 1)))
    (hOpen :
      ∫ ω in blockGoodSet β t u s,
        futureEnergy β (t s) N (openCorrector β t u s ω) ∂disorderLaw ≤
          C₀ * θ ^ (2 * (s - u)) / ((K : ℝ) - u)) :
    IntegrableOn (fun ω => futureEnergy β (t s) N (fun y =>
      (blockRatio β t r (u - 1) ω - 1) * openCorrector β t u s ω y))
      (blockGoodSet β t r s) disorderLaw ∧
    ∫ ω in blockGoodSet β t r s, futureEnergy β (t s) N (fun y =>
        (blockRatio β t r (u - 1) ω - 1) * openCorrector β t u s ω y) ∂disorderLaw ≤
      |C₁| * |C₀| * θ ^ (2 * (s - u)) / ((K : ℝ) - s) ^ 2 := by
  classical
  let G₁ := blockGoodSet β t r (u - 1)
  let G₂ := blockGoodSet β t u s
  let c : Disorder → ℝ := fun ω => blockRatio β t r (u - 1) ω - 1
  have hden1 : 0 < (K : ℝ) - (u - 1) := by
    have huCast : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast (show 1 ≤ u by omega)
    have hKCast : (u : ℝ) ≤ (K : ℝ) := by exact_mod_cast (show u ≤ K by omega)
    linarith
  have hden : 0 < (K : ℝ) - s := by
    have hn : 0 < K - s := by omega
    rw [← Nat.cast_sub (by omega : s ≤ K)]
    exact_mod_cast hn
  have hdenLe2 : (K : ℝ) - s ≤ (K : ℝ) - u := by
    rw [← Nat.cast_sub (by omega : s ≤ K), ← Nat.cast_sub (by omega : u ≤ K)]
    exact_mod_cast Nat.sub_le_sub_left hus K
  have hdenLe1 : (K : ℝ) - s ≤ (K : ℝ) - (u - 1) := by
    linarith [hdenLe2]
  have hcm : Measurable[Gaussian.disorderBlock (t (r - 1)) (t (u - 1))] c := by
    dsimp [c]
    by_cases hru' : r < u
    · have hRatioMeas := measurable_blockRatio_on_block β t ht r (u - 1) (by omega)
      exact hRatioMeas.sub measurable_const
    · have hur : u = r := by omega
      subst u
      have hR : blockRatio β t r (r - 1) = fun _ => 1 := by
        funext ω
        exact blockRatio_empty β t r hr ω
      rw [hR]
      exact measurable_const.sub measurable_const
  have hcInt : IntegrableOn (fun ω => c ω ^ 2) G₁ disorderLaw := by
    by_cases hru' : r < u
    · simpa [G₁, c] using OnePoint.integrableOn_blockRatio_sub_one_sq β ht
        (by omega : 1 ≤ r) (by omega : r ≤ u - 1)
    · have hur : u = r := by omega
      subst u
      have hc : c = fun _ => 0 := by
        funext ω
        simp [c, blockRatio_empty β t r hr ω]
      rw [hc]
      simp
  have hfactor := openCorrectorTerm_integral_eq_of_prefixCoefficient β t N r s K u ht
    hr hru hus hsK hts c hcm hcInt
  refine ⟨hfactor.1, ?_⟩
  have hΔ : ∫ ω in G₁, c ω ^ 2 ∂disorderLaw ≤ |C₁| / ((K : ℝ) - (u - 1)) := by
    by_cases hru' : r < u
    · have h := hRatio hru'
      have hC : C₁ / ((K : ℝ) - (u - 1)) ≤
          |C₁| / ((K : ℝ) - (u - 1)) :=
        div_le_div_of_nonneg_right (le_abs_self C₁) hden1.le
      exact h.trans hC
    · have hur : u = r := by omega
      subst u
      have hc : c = fun _ => 0 := by
        funext ω
        simp [c, blockRatio_empty β t r hr ω]
      simpa [hc] using (div_nonneg (abs_nonneg C₁) hden1.le)
  have hdenU : 0 < (K : ℝ) - u := by
    have hn : 0 < K - u := by omega
    rw [← Nat.cast_sub (by omega : u ≤ K)]
    exact_mod_cast hn
  have hOpenAbs : ∫ ω in G₂,
      futureEnergy β (t s) N (openCorrector β t u s ω) ∂disorderLaw ≤
      |C₀| * θ ^ (2 * (s - u)) / ((K : ℝ) - u) := by
    have hpow : 0 ≤ θ ^ (2 * (s - u)) := pow_nonneg hθ0.le _
    exact hOpen.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self C₀) hpow) hdenU.le)
  have hΔnonneg : 0 ≤ ∫ ω in G₁, c ω ^ 2 ∂disorderLaw :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun ω => sq_nonneg (c ω))
  have hopenNonneg : 0 ≤ ∫ ω in G₂,
      futureEnergy β (t s) N (openCorrector β t u s ω) ∂disorderLaw :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun ω =>
      futureEnergy_nonneg β (t s) N (openCorrector β t u s ω))
  have hnumNonneg : 0 ≤ |C₁| * |C₀| * θ ^ (2 * (s - u)) := by positivity
  calc
    _ = (∫ ω in G₁, c ω ^ 2 ∂disorderLaw) *
        (∫ ω in G₂, futureEnergy β (t s) N (openCorrector β t u s ω) ∂disorderLaw) := hfactor.2
    _ ≤ (|C₁| / ((K : ℝ) - (u - 1))) *
        (|C₀| * θ ^ (2 * (s - u)) / ((K : ℝ) - u)) :=
      mul_le_mul hΔ hOpenAbs hopenNonneg (div_nonneg (abs_nonneg C₁) hden1.le)
    _ ≤ (|C₁| * |C₀| * θ ^ (2 * (s - u))) / ((K : ℝ) - s) ^ 2 := by
      have hfirst : |C₁| / ((K : ℝ) - (u - 1)) ≤ |C₁| / ((K : ℝ) - s) :=
        div_le_div_of_nonneg_left (abs_nonneg C₁) hden hdenLe1
      have hsecond : |C₀| * θ ^ (2 * (s - u)) / ((K : ℝ) - u) ≤
          |C₀| * θ ^ (2 * (s - u)) / ((K : ℝ) - s) :=
        div_le_div_of_nonneg_left (mul_nonneg (abs_nonneg C₀) (pow_nonneg hθ0.le _))
          hden hdenLe2
      have hC₀pow : 0 ≤ |C₀| * θ ^ (2 * (s - u)) / ((K : ℝ) - u) :=
        div_nonneg (mul_nonneg (abs_nonneg C₀) (pow_nonneg hθ0.le _)) hdenU.le
      calc
        _ ≤ (|C₁| / ((K : ℝ) - s)) *
            (|C₀| * θ ^ (2 * (s - u)) / ((K : ℝ) - s)) :=
          mul_le_mul hfirst hsecond hC₀pow
            (div_nonneg (abs_nonneg C₁) hden.le)
        _ = _ := by field_simp

/-- Cauchy–Schwarz on `G`: for nonnegative measurable `f`, `g` with square-integrable restrictions,
`f * g` is integrable on `G` and `∫ f * g ≤ √(∫ f²) * √(∫ g²)`. -/
theorem setIntegral_mul_le_sqrt_sq (f g : Disorder → ℝ) (G : Set Disorder)
    (hf : Measurable f) (hg : Measurable g)
    (hfnn : ∀ ω, 0 ≤ f ω) (hgnn : ∀ ω, 0 ≤ g ω)
    (hfsq : IntegrableOn (fun ω => f ω ^ 2) G disorderLaw)
    (hgsq : IntegrableOn (fun ω => g ω ^ 2) G disorderLaw) :
    IntegrableOn (fun ω => f ω * g ω) G disorderLaw ∧
    ∫ ω in G, f ω * g ω ∂disorderLaw ≤
      Real.sqrt (∫ ω in G, f ω ^ 2 ∂disorderLaw) *
        Real.sqrt (∫ ω in G, g ω ^ 2 ∂disorderLaw) := by
  let μG := disorderLaw.restrict G
  have hfInt : Integrable (fun ω => f ω ^ 2) μG := by
    change IntegrableOn (fun ω => f ω ^ 2) G disorderLaw at hfsq
    exact hfsq
  have hgInt : Integrable (fun ω => g ω ^ 2) μG := by
    change IntegrableOn (fun ω => g ω ^ 2) G disorderLaw at hgsq
    exact hgsq
  have hfStrong : AEStronglyMeasurable f μG := hf.aestronglyMeasurable.restrict
  have hgStrong : AEStronglyMeasurable g μG := hg.aestronglyMeasurable.restrict
  have hfMem : MemLp f (ENNReal.ofReal (2 : ℝ)) μG := by
    simpa using (memLp_two_iff_integrable_sq hfStrong).2 hfInt
  have hgMem : MemLp g (ENNReal.ofReal (2 : ℝ)) μG := by
    simpa using (memLp_two_iff_integrable_sq hgStrong).2 hgInt
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := μG) (p := (2 : ℝ)) (q := 2) Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall hfnn) (Filter.Eventually.of_forall hgnn) hfMem hgMem
  have hHolder' : ∫ ω in G, f ω * g ω ∂disorderLaw ≤
      Real.sqrt (∫ ω in G, f ω ^ 2 ∂disorderLaw) *
        Real.sqrt (∫ ω in G, g ω ^ 2 ∂disorderLaw) := by
    have hpow (x : ℝ) : x ^ (2 : ℝ) = x ^ (2 : ℕ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hHolderPow := hHolder
    simp only [hpow] at hHolderPow
    simpa only [μG, Real.sqrt_eq_rpow] using hHolderPow
  have hpqENN : ENNReal.HolderTriple (ENNReal.ofReal (2 : ℝ))
      (ENNReal.ofReal (2 : ℝ)) 1 := Real.HolderConjugate.two_two.ennrealOfReal
  have hprodMem : MemLp (fun ω => g ω * f ω) 1 μG :=
    @MemLp.mul Disorder inferInstance ℝ inferInstance μG
      (ENNReal.ofReal (2 : ℝ)) (ENNReal.ofReal (2 : ℝ)) 1 f g hgMem hfMem hpqENN
  have hprodInt : Integrable (fun ω => f ω * g ω) μG := by
    have h := hprodMem.integrable (by norm_num)
    simpa only [mul_comm] using h
  exact ⟨hprodInt, hHolder'⟩

/-- Jensen on `G`: for nonnegative `f` integrable on `G`, `√f` is integrable on `G` and `∫ √f ≤ √(∫
f)`. -/
theorem setIntegral_sqrt_le_sqrt (f : Disorder → ℝ) (G : Set Disorder)
    (hf : Measurable f) (hfnn : ∀ ω, 0 ≤ f ω)
    (hfi : IntegrableOn f G disorderLaw) :
    IntegrableOn (fun ω => Real.sqrt (f ω)) G disorderLaw ∧
    ∫ ω in G, Real.sqrt (f ω) ∂disorderLaw ≤
      Real.sqrt (∫ ω in G, f ω ∂disorderLaw) := by
  have hrootMeas : Measurable (fun ω => Real.sqrt (f ω)) := hf.sqrt
  have hrootSq : IntegrableOn (fun ω => Real.sqrt (f ω) ^ 2) G disorderLaw := by
    have hEq : (fun ω => Real.sqrt (f ω) ^ 2) =ᵐ[disorderLaw.restrict G] f := by
      filter_upwards [] with ω
      exact Real.sq_sqrt (hfnn ω)
    exact hfi.congr hEq.symm
  have honeInt : IntegrableOn (fun _ : Disorder => (1 : ℝ) ^ 2) G disorderLaw :=
    by simp
  have hmass : ∫ ω in G, (1 : ℝ) ^ 2 ∂disorderLaw ≤ 1 := by
    have hset : ∫ ω in G, (1 : ℝ) ∂disorderLaw ≤ ∫ ω, (1 : ℝ) ∂disorderLaw :=
      setIntegral_le_integral (integrable_const (1 : ℝ))
        (Filter.Eventually.of_forall fun _ => by norm_num)
    calc
      ∫ ω in G, (1 : ℝ) ^ 2 ∂disorderLaw = ∫ ω in G, (1 : ℝ) ∂disorderLaw := by simp
      _ ≤ ∫ ω, (1 : ℝ) ∂disorderLaw := hset
      _ = 1 := by simp
  have hCS := setIntegral_mul_le_sqrt_sq (fun ω => Real.sqrt (f ω))
    (fun _ => (1 : ℝ)) G hrootMeas measurable_const
    (fun ω => Real.sqrt_nonneg _) (fun _ => by norm_num) hrootSq honeInt
  refine ⟨?_, ?_⟩
  · have hmajor : IntegrableOn (fun ω => 1 + f ω) G disorderLaw :=
      (integrable_const (μ := disorderLaw) (1 : ℝ)).integrableOn.add hfi
    apply hmajor.mono' hrootMeas.aestronglyMeasurable
    filter_upwards [] with ω
    have hbound : Real.sqrt (f ω) ≤ 1 + f ω := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · linarith [hfnn ω]
      · nlinarith [sq_nonneg (f ω)]
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg (f ω)),
      abs_of_nonneg (by linarith [hfnn ω] : 0 ≤ 1 + f ω)] using hbound
  · calc
      ∫ ω in G, Real.sqrt (f ω) ∂disorderLaw =
          ∫ ω in G, Real.sqrt (f ω) * 1 ∂disorderLaw := by simp
      _ ≤ Real.sqrt (∫ ω in G, Real.sqrt (f ω) ^ 2 ∂disorderLaw) *
            Real.sqrt (∫ ω in G, (1 : ℝ) ^ 2 ∂disorderLaw) := hCS.2
      _ ≤ Real.sqrt (∫ ω in G, f ω ∂disorderLaw) * 1 := by
        have hrootEq : ∫ ω in G, Real.sqrt (f ω) ^ 2 ∂disorderLaw =
            ∫ ω in G, f ω ∂disorderLaw := by
          exact integral_congr_ae
            (Filter.Eventually.of_forall fun ω => Real.sq_sqrt (hfnn ω))
        rw [hrootEq]
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_one.mpr hmass)
          (Real.sqrt_nonneg _)
      _ = Real.sqrt (∫ ω in G, f ω ∂disorderLaw) := by simp

/-- Each coordinate of the common correction is measurable for the disorder up to time `t s`. -/
theorem measurable_commonCorrection_coordinate (β : ℝ) (t : ℕ → ℕ)
    (r s : ℕ) (ht : Monotone t) (hr : 1 ≤ r) (_hrs : r ≤ s) (y : Site) :
    Measurable[disorderPast (t s)] (fun ω => commonCorrection β t r s ω y) := by
  have hcoord (y : Site) :
      Measurable[disorderPast (t s)] (fun ω => commonCorrection β t r s ω y) := by
    rw [← Gaussian.disorderBlock_zero (t s)]
    unfold commonCorrection
    apply Finset.measurable_sum
    intro u hu
    have hu' := Finset.mem_Icc.mp hu
    have hlocal := measurable_openCorrector_on_block β t ht u s (by omega) hu'.2 y
    have hmono : Gaussian.disorderBlock (t (u - 1)) (t s) ≤
        Gaussian.disorderBlock 0 (t s) :=
      Gaussian.disorderBlock_mono (Nat.zero_le _) le_rfl
    exact hlocal.mono hmono le_rfl
  exact hcoord y

/-- The future energy of the common correction is measurable for the disorder up to time `t s`. -/
theorem measurable_commonCorrection_futureEnergy (β : ℝ) (t : ℕ → ℕ)
    (N r s : ℕ) (ht : Monotone t) (hr : 1 ≤ r) (hrs : r ≤ s) (hts : t s ≤ N) :
    Measurable[disorderPast (t s)]
      (fun ω => futureEnergy β (t s) N (commonCorrection β t r s ω)) := by
  classical
  let A := (Finset.Icc r s).biUnion (fun u => openCorrectorNumeratorSupport t u s)
  have hsupport (ω : Disorder) (y : Site) (hy : y ∉ A) :
      commonCorrection β t r s ω y = 0 := by
    unfold commonCorrection
    apply Finset.sum_eq_zero
    intro u hu
    have hyu : y ∉ openCorrectorNumeratorSupport t u s := by
      intro hmem
      exact hy (Finset.mem_biUnion.mpr ⟨u, hu, hmem⟩)
    unfold openCorrector
    rw [openCorrectorNumerator_eq_zero_of_not_mem_support β t u s ω y hyu, zero_div]
  have hcoord (y : Site) :
      Measurable[disorderPast (t s)] (fun ω => commonCorrection β t r s ω y) :=
    measurable_commonCorrection_coordinate β t r s ht hr hrs y
  exact measurable_futureEnergy β hts (fun ω => commonCorrection β t r s ω)
    A hsupport hcoord


end Critical2DKPZ.FutureProfiles

end
