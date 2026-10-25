/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.GridAlignment
public import Critical2DKPZ.FutureProfiles.AdaptiveLeftTail
public import Critical2DKPZ.FutureProfiles.DeterministicComparison
public import Critical2DKPZ.FutureProfiles.EndpointTailBounds
public import Critical2DKPZ.FutureProfiles.FreezingPast
public import Critical2DKPZ.FutureProfiles.HelperGeometry
public import Critical2DKPZ.FutureProfiles.HelperIdentities
public import Critical2DKPZ.FutureProfiles.OpenCorrectorEnergy
public import Critical2DKPZ.FutureProfiles.ProfileEstimateEnergy
public import Critical2DKPZ.FutureProfiles.SplitInputs
public import Critical2DKPZ.LogNormality.LatticeInputs
public import Critical2DKPZ.MomentBounds.ProfileBoxes
public import Critical2DKPZ.Polymer.BlockMeasurability
public import Critical2DKPZ.Smoothing.EndpointDistribution
import Mathlib.Tactic

/-! # Origin comparison of endpoint profiles -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators

namespace Critical2DKPZ.FutureProfiles

open Critical2DKPZ.Blocks Critical2DKPZ.OnePoint Critical2DKPZ.Polymer

private theorem integrableOn_sqrt_futureEnergy_of_integrable
    (β : ℝ) {a b : ℕ} (hab : a ≤ b) (η : Disorder → Site → ℝ)
    (S : Finset Site) (hsupp : ∀ ω y, y ∉ S → η ω y = 0)
    (hmeas : ∀ y, Measurable[disorderPast a] (η · y)) (G : Set Disorder)
    (hE : IntegrableOn (fun ω => futureEnergy β a b (η ω)) G disorderLaw) :
    IntegrableOn (fun ω => Real.sqrt (futureEnergy β a b (η ω))) G disorderLaw := by
  have hpast : disorderPast a ≤ (inferInstance : MeasurableSpace Disorder) := by
    rw [← Gaussian.disorderBlock_zero a]
    exact Gaussian.disorderBlock_le 0 a
  have hEmeas : Measurable (fun ω => futureEnergy β a b (η ω)) :=
    (measurable_futureEnergy β hab η S hsupp hmeas).mono hpast le_rfl
  have hEint : Integrable (fun ω => futureEnergy β a b (η ω)) (disorderLaw.restrict G) := hE
  have hmajor : Integrable
      (fun ω => 1 + futureEnergy β a b (η ω)) (disorderLaw.restrict G) :=
    (integrable_const (1 : ℝ)).add hEint
  have hroot : Integrable
      (fun ω => Real.sqrt (futureEnergy β a b (η ω))) (disorderLaw.restrict G) := by
    refine hmajor.mono' (Real.continuous_sqrt.measurable.comp hEmeas).aestronglyMeasurable ?_
    filter_upwards with ω
    have hnonneg := futureEnergy_nonneg β a b (η ω)
    have hsqrt := Real.sqrt_nonneg (futureEnergy β a b (η ω))
    have hbound : Real.sqrt (futureEnergy β a b (η ω)) ≤
        1 + futureEnergy β a b (η ω) := by
      apply Real.sqrt_le_iff.mpr
      constructor <;> nlinarith [sq_nonneg (futureEnergy β a b (η ω))]
    simpa only [Real.norm_eq_abs, abs_of_nonneg hsqrt,
      abs_of_nonneg (by linarith : 0 ≤ 1 + futureEnergy β a b (η ω))] using hbound
  change Integrable (fun ω => Real.sqrt (futureEnergy β a b (η ω)))
    (disorderLaw.restrict G)
  exact hroot

/-- The convolution of finitely many weights `η w` with the walk kernel is summable. -/
theorem summable_walk_convolution (d : ℕ) (S : Finset Site)
    (η : Site → ℝ) :
    Summable (fun y : Site => ∑ w ∈ S, η w * srwKernel d (y - w)) := by
  classical
  have hkernel (w : Site) : Summable (fun y : Site => srwKernel d (y - w)) := by
    apply summable_of_ne_finset_zero (s := Polymer.endpoints w d)
    intro y hy
    exact Polymer.srwKernel_eq_zero_of_not_mem d w y hy
  induction S using Finset.induction_on with
  | empty => simp
  | @insert w S hw ih =>
      simp only [Finset.sum_insert hw]
      exact (hkernel w).mul_left (η w) |>.add ih

/-- If the weights `η w`, `w ∈ S`, sum to `1`, the walk convolution sums to `1`. -/
theorem hasSum_walk_convolution_one (d : ℕ) (S : Finset Site)
    (η : Site → ℝ) (hη : ∑ w ∈ S, η w = 1) :
    HasSum (fun y : Site => ∑ w ∈ S, η w * srwKernel d (y - w)) 1 := by
  have hconv := summable_walk_convolution d S η
  have hsum : (∑' y : Site, ∑ w ∈ S, η w * srwKernel d (y - w)) = 1 := by
    have hkernel (w : Site) : Summable (fun y : Site => srwKernel d (y - w)) := by
      apply summable_of_ne_finset_zero (s := Polymer.endpoints w d)
      intro y hy
      exact Polymer.srwKernel_eq_zero_of_not_mem d w y hy
    rw [Summable.tsum_finsetSum (fun w hw => (hkernel w).mul_left (η w))]
    calc
      (∑ w ∈ S, ∑' y : Site, η w * srwKernel d (y - w)) =
          ∑ w ∈ S, η w * (∑' y : Site, srwKernel d (y - w)) := by
            apply Finset.sum_congr rfl
            intro w hw
            rw [tsum_mul_left]
      _ = 1 := by simp [hη, Polymer.tsum_srwKernel]
  exact hconv.hasSum_iff.mpr hsum

/-- The walk convolution vanishes outside the union of the endpoint sets of the sites in `S`. -/
theorem walk_convolution_eq_zero_of_not_mem (d : ℕ) (S : Finset Site)
    (η : Site → ℝ) (y : Site)
    (hy : y ∉ S.biUnion (fun w => Polymer.endpoints w d)) :
    (∑ w ∈ S, η w * srwKernel d (y - w)) = 0 := by
  apply Finset.sum_eq_zero
  intro w hw
  have hyw : y ∉ Polymer.endpoints w d := by
    intro hmem
    exact hy (Finset.mem_biUnion.mpr ⟨w, hw, hmem⟩)
  rw [Polymer.srwKernel_eq_zero_of_not_mem d w y hyw, mul_zero]

/-- For `m ≤ n`, the endpoint laws with smoothing times `0` and `m` live on a common finite set `S`,
are probability vectors there, and differ by at most `2` pointwise. -/
theorem endpoint_smoothing_difference_probability_data (β : ℝ) {m n : ℕ}
    (hmn : m ≤ n) :
    ∃ S : Finset Site,
      (∀ ω y, y ∉ S → smoothedEndpointDist β 0 n 0 ω y = 0) ∧
      (∀ ω y, y ∉ S → smoothedEndpointDist β m n 0 ω y = 0) ∧
      (∀ ω y, y ∉ S →
        smoothedEndpointDist β 0 n 0 ω y - smoothedEndpointDist β m n 0 ω y = 0) ∧
      (∀ ω, ∑ y ∈ S, smoothedEndpointDist β 0 n 0 ω y = 1) ∧
      (∀ ω, ∑ y ∈ S, smoothedEndpointDist β m n 0 ω y = 1) ∧
      (∀ ω, ∑ y ∈ S,
        (smoothedEndpointDist β 0 n 0 ω y - smoothedEndpointDist β m n 0 ω y) = 0) ∧
      (∀ ω y,
        |smoothedEndpointDist β 0 n 0 ω y - smoothedEndpointDist β m n 0 ω y| ≤ 2) := by
  classical
  let S0 := Polymer.endpoints 0 n
  let S1 := (Polymer.endpoints 0 m).biUnion (fun w => Polymer.endpoints w (n - m))
  let S := S0 ∪ S1
  have hdata0 := Smoothing.endpointDist_probability β n 0
  have hdata1 := Smoothing.smoothedEndpointDist_probability β hmn 0
  have hzero0 (ω : Disorder) (y : Site) (hy : y ∉ S0) :
      endpointDist β n 0 ω y = 0 := hdata0 ω |>.1 y hy
  have hzero1 (ω : Disorder) (y : Site) (hy : y ∉ S1) :
      smoothedEndpointDist β m n 0 ω y = 0 := by
    exact hdata1 ω |>.1 y (by simpa [S1] using hy)
  have hsum0 (ω : Disorder) : ∑ y ∈ S, endpointDist β n 0 ω y = 1 := by
    have hsubset : S0 ⊆ S := by intro y hy; exact Finset.mem_union_left _ hy
    calc
      _ = ∑ y ∈ S0, endpointDist β n 0 ω y := by
        symm
        apply Finset.sum_subset hsubset
        intro y hyS hy0
        exact hzero0 ω y hy0
      _ = 1 := hdata0 ω |>.2.2
  have hsum1 (ω : Disorder) : ∑ y ∈ S, smoothedEndpointDist β m n 0 ω y = 1 := by
    have hsubset : S1 ⊆ S := by intro y hy; exact Finset.mem_union_right _ hy
    calc
      _ = ∑ y ∈ S1, smoothedEndpointDist β m n 0 ω y := by
        symm
        apply Finset.sum_subset hsubset
        intro y hyS hy1
        exact hzero1 ω y hy1
      _ = 1 := by simpa [S1] using hdata1 ω |>.2.2
  refine ⟨S, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ω y hy
    have hy0 : y ∉ S0 := by
      intro h
      exact hy (Finset.mem_union_left _ h)
    have hzero0' : smoothedEndpointDist β 0 n 0 ω y = 0 := by
      rw [← endpointDist_eq_smoothedEndpointDist_zero β n 0 ω]
      exact hzero0 ω y hy0
    exact hzero0'
  · intro ω y hy
    have hy1 : y ∉ S1 := by
      intro h
      exact hy (Finset.mem_union_right _ h)
    exact hzero1 ω y hy1
  · intro ω y hy
    have hy0 : y ∉ S0 := by
      intro h
      exact hy (Finset.mem_union_left _ h)
    have hy1 : y ∉ S1 := by
      intro h
      exact hy (Finset.mem_union_right _ h)
    have hzero0' : smoothedEndpointDist β 0 n 0 ω y = 0 := by
      rw [← endpointDist_eq_smoothedEndpointDist_zero β n 0 ω]
      exact hzero0 ω y hy0
    rw [hzero0', hzero1 ω y hy1]
    ring
  · intro ω
    have hsum0' : ∑ y ∈ S, smoothedEndpointDist β 0 n 0 ω y = 1 := by
      simpa only [endpointDist_eq_smoothedEndpointDist_zero β n 0 ω]
        using hsum0 ω
    exact hsum0'
  · intro ω
    exact hsum1 ω
  · intro ω
    have hsum0' : ∑ y ∈ S, smoothedEndpointDist β 0 n 0 ω y = 1 := by
      simpa only [endpointDist_eq_smoothedEndpointDist_zero β n 0 ω]
        using hsum0 ω
    rw [Finset.sum_sub_distrib, hsum0', hsum1 ω]
    ring
  · intro ω y
    have hbound0 : |endpointDist β n 0 ω y| ≤ 1 := by
      have hnonneg := hdata0 ω |>.2.1 y
      by_cases hy : y ∈ S0
      · rw [abs_of_nonneg hnonneg]
        calc
          endpointDist β n 0 ω y ≤ ∑ z ∈ S0, endpointDist β n 0 ω z :=
            Finset.single_le_sum (fun z hz => hdata0 ω |>.2.1 z) hy
          _ = 1 := hdata0 ω |>.2.2
      · rw [hzero0 ω y hy]
        norm_num
    have hbound1 : |smoothedEndpointDist β m n 0 ω y| ≤ 1 := by
      have hnonneg := hdata1 ω |>.2.1 y
      by_cases hy : y ∈ S1
      · rw [abs_of_nonneg hnonneg]
        calc
          smoothedEndpointDist β m n 0 ω y ≤
              ∑ z ∈ S1, smoothedEndpointDist β m n 0 ω z :=
            Finset.single_le_sum (fun z hz => hdata1 ω |>.2.1 z) (by simpa [S1] using hy)
          _ = 1 := by simpa [S1] using hdata1 ω |>.2.2
      · rw [hzero1 ω y hy]
        norm_num
    calc
      |smoothedEndpointDist β 0 n 0 ω y - smoothedEndpointDist β m n 0 ω y| ≤
          |smoothedEndpointDist β 0 n 0 ω y| +
            |smoothedEndpointDist β m n 0 ω y| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add
        (by simpa only [endpointDist_eq_smoothedEndpointDist_zero β n 0 ω] using hbound0)
        hbound1
      _ = 2 := by norm_num

/-- Each coordinate of the difference of the two smoothed endpoint laws is
`disorderPast n`-measurable. -/
theorem measurable_endpoint_smoothing_difference_past (β : ℝ) {m n : ℕ}
    (hmn : m ≤ n) (y : Site) :
    Measurable[disorderPast n]
      (fun ω => smoothedEndpointDist β 0 n 0 ω y - smoothedEndpointDist β m n 0 ω y) := by
  rw [← Gaussian.disorderBlock_zero n]
  have h0 : Measurable[Gaussian.disorderBlock 0 n]
      (fun ω => smoothedEndpointDist β 0 n 0 ω y) :=
    Polymer.measurable_smoothedEndpointDist_block β 0 n (Nat.zero_le _) 0 y
  have h1 : Measurable[Gaussian.disorderBlock m n]
      (fun ω => smoothedEndpointDist β m n 0 ω y) :=
    Polymer.measurable_smoothedEndpointDist_block β m n hmn 0 y
  have hsub : Gaussian.disorderBlock m n ≤ Gaussian.disorderBlock 0 n :=
    Gaussian.disorderBlock_mono (Nat.zero_le _) le_rfl
  exact h0.sub (h1.mono hsub le_rfl)

private theorem sqrt_nat_mul_pow_le (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (J : ℕ) (hJ : 1 ≤ J) :
    Real.sqrt (J : ℝ) * θ ^ J ≤ 1 / (1 - θ) := by
  have hθnonneg : 0 ≤ θ := hθ0.le
  have hθle : θ ≤ 1 := hθ1.le
  have hgeom := sum_Icc_pow_reverse_le_inv_one_sub_of_le hθnonneg hθ1
    (r := 1) (s := J)
  have hcard : (Finset.Icc 1 J).card = J := by
    simp
  have hsumConst : (∑ i ∈ Finset.Icc 1 J, θ ^ J) =
      (J : ℝ) * θ ^ J := by
    rw [Finset.sum_const, hcard]
    simp [nsmul_eq_mul]
  have hpow : ∀ i ∈ Finset.Icc 1 J, θ ^ J ≤ θ ^ (J - i) := by
    intro i hi
    exact pow_le_pow_of_le_one hθnonneg hθle (Nat.sub_le J i)
  have hmul : (J : ℝ) * θ ^ J ≤ ∑ i ∈ Finset.Icc 1 J, θ ^ (J - i) := by
    rw [← hsumConst]
    exact Finset.sum_le_sum hpow
  have hJroot : Real.sqrt (J : ℝ) ≤ J := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have hJreal : (1 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ
      nlinarith
  calc
    Real.sqrt (J : ℝ) * θ ^ J ≤ (J : ℝ) * θ ^ J :=
      mul_le_mul_of_nonneg_right hJroot (pow_nonneg hθnonneg _)
    _ ≤ ∑ i ∈ Finset.Icc 1 J, θ ^ (J - i) := hmul
    _ ≤ 1 / (1 - θ) := hgeom

private theorem sum_pow_gap_le (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    {a J : ℕ} :
    ∑ u ∈ Finset.Icc 1 a, θ ^ (a + J - u) ≤ θ ^ J / (1 - θ) := by
  have hgeom := sum_Icc_pow_reverse_le_inv_one_sub_of_le hθ0 hθ1
    (r := 1) (s := a)
  have hterm (u : ℕ) (hu : u ∈ Finset.Icc 1 a) :
      θ ^ (a + J - u) = θ ^ J * θ ^ (a - u) := by
    have hu' := Finset.mem_Icc.mp hu
    rw [show a + J - u = J + (a - u) by omega, pow_add]
  calc
    _ = θ ^ J * ∑ u ∈ Finset.Icc 1 a, θ ^ (a - u) := by
      rw [Finset.sum_congr rfl hterm, Finset.mul_sum]
    _ ≤ θ ^ J * (1 / (1 - θ)) :=
      mul_le_mul_of_nonneg_left hgeom (pow_nonneg hθ0 _)
    _ = θ ^ J / (1 - θ) := by ring

private theorem integral_sqrt_futureEnergy_openCorrector_le
    (β : ℝ) (t : ℕ → ℕ) (N K J u s : ℕ)
    (ht : Monotone t) (hu : 1 ≤ u) (hus : u ≤ s) (hts : t s ≤ N)
    (hJ : 1 ≤ J) (hKu : (J : ℝ) ≤ (K : ℝ) - u)
    (θ C₀ : ℝ) (hθ0 : 0 < θ) (_hθ1 : θ < 1)
    (hOpen : ∫ ω in blockGoodSet β t u s,
      futureEnergy β (t s) N (openCorrector β t u s ω) ∂disorderLaw ≤
        C₀ * θ ^ (2 * (s - u)) / ((K : ℝ) - u))
    (G : Set Disorder) (hG : G ⊆ blockGoodSet β t u s) :
    IntegrableOn (fun ω => Real.sqrt
      (futureEnergy β (t s) N (openCorrector β t u s ω))) G disorderLaw ∧
      ∫ ω in G, Real.sqrt
        (futureEnergy β (t s) N (openCorrector β t u s ω)) ∂disorderLaw ≤
        Real.sqrt |C₀| * θ ^ (s - u) / Real.sqrt J := by
  classical
  let S := openCorrectorNumeratorSupport t u s
  let E : Disorder → ℝ := fun ω =>
    futureEnergy β (t s) N (openCorrector β t u s ω)
  have hS (ω : Disorder) (y : Site) (hy : y ∉ S) :
      openCorrector β t u s ω y = 0 := by
    unfold openCorrector
    rw [openCorrectorNumerator_eq_zero_of_not_mem_support β t u s ω y hy, zero_div]
  have hηmeas (y : Site) : Measurable[disorderPast (t s)]
      (fun ω => openCorrector β t u s ω y) :=
    measurable_openCorrector_on_past β t ht u s hu hus y
  have hpast : disorderPast (t s) ≤ (inferInstance : MeasurableSpace Disorder) := by
    rw [← Gaussian.disorderBlock_zero (t s)]
    exact Gaussian.disorderBlock_le 0 (t s)
  have hEmeas : Measurable E := by
    dsimp [E]
    exact (measurable_futureEnergy β hts (openCorrector β t u s) S
      (fun ω y hy => hS ω y hy) hηmeas).mono hpast le_rfl
  have hEintBlock := integrableOn_futureEnergy_openCorrector β t N u s ht hu hus hts
  have hEint : IntegrableOn E G disorderLaw := by
    exact hEintBlock.mono_set (by simpa [E] using hG)
  have hrootInt : IntegrableOn (fun ω => Real.sqrt (E ω)) G disorderLaw := by
    exact integrableOn_sqrt_futureEnergy_of_integrable β hts
      (openCorrector β t u s) S (fun ω y hy => hS ω y hy) hηmeas G hEint
  have henergyG : ∫ ω in G, E ω ∂disorderLaw ≤
      |C₀| * θ ^ (2 * (s - u)) / (J : ℝ) := by
    have hrestrict := setIntegral_mono_set hEintBlock
      (Filter.Eventually.of_forall fun ω =>
        futureEnergy_nonneg β (t s) N (openCorrector β t u s ω))
      (Filter.Eventually.of_forall fun ω hω => by simpa [E] using hG hω)
    have hden : 0 < (K : ℝ) - u := by
      exact lt_of_lt_of_le (by exact_mod_cast Nat.zero_lt_of_lt hJ) hKu
    have hdenJ : 0 < (J : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hJ
    calc
      ∫ ω in G, E ω ∂disorderLaw ≤
          C₀ * θ ^ (2 * (s - u)) / ((K : ℝ) - u) := by
            simpa [E] using hrestrict.trans hOpen
      _ ≤ |C₀| * θ ^ (2 * (s - u)) / ((K : ℝ) - u) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_abs_self C₀) (pow_nonneg hθ0.le _)) hden.le
      _ ≤ |C₀| * θ ^ (2 * (s - u)) / (J : ℝ) := by
        apply div_le_div_of_nonneg_left
        · positivity
        · exact hdenJ
        · exact hKu
  let T : ℝ := Real.sqrt |C₀| * θ ^ (s - u) / Real.sqrt J
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hT2 : T ^ 2 = |C₀| * θ ^ (2 * (s - u)) / (J : ℝ) := by
    dsimp [T]
    have hsqrtJ : Real.sqrt (J : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast Nat.zero_lt_of_lt hJ)).ne'
    rw [div_pow, mul_pow, Real.sq_sqrt (abs_nonneg C₀), Real.sq_sqrt
      (by exact_mod_cast (Nat.zero_le J : 0 ≤ J))]
    field_simp [hsqrtJ]
    rw [show (θ ^ (s - u)) ^ 2 = θ ^ (2 * (s - u)) by
      rw [← pow_mul]
      congr 1
      omega]
  have hEroot : Real.sqrt (∫ ω in G, E ω ∂disorderLaw) ≤ T := by
    have hnonneg : 0 ≤ ∫ ω in G, E ω ∂disorderLaw :=
      integral_nonneg_of_ae (Filter.Eventually.of_forall fun ω =>
        futureEnergy_nonneg β (t s) N (openCorrector β t u s ω))
    have hsq : (Real.sqrt (∫ ω in G, E ω ∂disorderLaw)) ^ 2 ≤ T ^ 2 := by
      rw [Real.sq_sqrt hnonneg, hT2]
      exact henergyG
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) hT0).1 hsq
  have hroot := setIntegral_sqrt_le_sqrt E G hEmeas
    (fun ω => futureEnergy_nonneg β (t s) N (openCorrector β t u s ω)) hEint
  refine ⟨hrootInt, ?_⟩
  calc
    ∫ ω in G, Real.sqrt (E ω) ∂disorderLaw ≤
        Real.sqrt (∫ ω in G, E ω ∂disorderLaw) := hroot.2
    _ ≤ T := hEroot

private theorem integrableOn_sqrt_profileResidual
    (β : ℝ) (t : ℕ → ℕ) (N K : ℕ) (ht : Monotone t)
    {r s : ℕ} (hr : 1 ≤ r) (hrs : r ≤ s) (hsK : s + 2 ≤ K)
    (hts : t s ≤ N) (θ C₀ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hOpen : ∀ u : ℕ, r ≤ u → u ≤ s →
      ∫ ω in blockGoodSet β t u s,
        futureEnergy β (t s) N (openCorrector β t u s ω) ∂disorderLaw ≤
          C₀ * θ ^ (2 * (s - u)) / ((K : ℝ) - u)) :
    IntegrableOn (fun ω => Real.sqrt (futureEnergy β (t s) N (fun y =>
      smoothedEndpointDist β (t (r - 1)) (t s) 0 ω y - srwKernel (t s) y -
        commonCorrection β t r s ω y)))
      (profileGoodSet β t r s) disorderLaw := by
  classical
  let PG := profileGoodSet β t r s
  let U : Disorder → Site → ℝ := smoothedEndpointDist β (t (r - 1)) (t s) 0
  let V : Site → ℝ := fun y => srwKernel (t s) y
  let W : Disorder → Site → ℝ := commonCorrection β t r s
  let R : Disorder → Site → ℝ := fun ω y => U ω y - V y - W ω y
  let SU : Finset Site :=
    (Polymer.endpoints 0 (t (r - 1))).biUnion
      (fun z => Polymer.endpoints z (t s - t (r - 1)))
  let SW : Finset Site := (Finset.Icc r s).biUnion
    (fun u => openCorrectorNumeratorSupport t u s)
  let S : Finset Site := SU ∪ Polymer.endpoints 0 (t s) ∪ SW
  have htimes : t (r - 1) ≤ t s := ht (by omega)
  have hUzero (ω : Disorder) (y : Site) (hy : y ∉ SU) : U ω y = 0 := by
    exact Smoothing.smoothedEndpointDist_probability β htimes 0 ω |>.1 y (by
      simpa [SU] using hy)
  have hVzero (y : Site) (hy : y ∉ S) : V y = 0 := by
    have hy' : y ∉ Polymer.endpoints 0 (t s) := by
      intro hmem
      exact hy (Finset.mem_union_left _ (Finset.mem_union_right _ hmem))
    have hzero := Polymer.srwKernel_eq_zero_of_not_mem (t s) 0 y hy'
    simpa [V, sub_zero] using hzero
  have hWzero (ω : Disorder) (y : Site) (hy : y ∉ SW) : W ω y = 0 := by
    dsimp [W, commonCorrection]
    apply Finset.sum_eq_zero
    intro u hu
    have hyu : y ∉ openCorrectorNumeratorSupport t u s := by
      intro hmem
      exact hy (Finset.mem_biUnion.mpr ⟨u, hu, hmem⟩)
    unfold openCorrector
    rw [openCorrectorNumerator_eq_zero_of_not_mem_support β t u s ω y hyu, zero_div]
  have hUzeroS (ω : Disorder) (y : Site) (hy : y ∉ S) : U ω y = 0 :=
    hUzero ω y (by
      intro hmem
      exact hy (Finset.mem_union_left _ (Finset.mem_union_left _ hmem)))
  have hWzeroS (ω : Disorder) (y : Site) (hy : y ∉ S) : W ω y = 0 :=
    hWzero ω y (by
      intro hmem
      exact hy (Finset.mem_union_right _ hmem))
  have hRzero (ω : Disorder) (y : Site) (hy : y ∉ S) : R ω y = 0 := by
    simp [R, hUzeroS ω y hy, hVzero y hy, hWzeroS ω y hy]
  have hUmeas (y : Site) : Measurable[disorderPast (t s)] (U · y) := by
    have hblock := Polymer.measurable_smoothedEndpointDist_block β
      (t (r - 1)) (t s) htimes 0 y
    have hsub := Gaussian.disorderBlock_mono
      (m := t (r - 1)) (n := t s) (a := 0) (b := t s) (Nat.zero_le _) le_rfl
    rw [← Gaussian.disorderBlock_zero (t s)]
    exact hblock.mono hsub le_rfl
  have hWmeas (y : Site) : Measurable[disorderPast (t s)] (W · y) := by
    dsimp [W]
    exact measurable_commonCorrection_coordinate β t r s ht hr hrs y
  have hRmeas (y : Site) : Measurable[disorderPast (t s)] (R · y) := by
    dsimp [R]
    exact (hUmeas y).sub measurable_const |>.sub (hWmeas y)
  have hpast : disorderPast (t s) ≤ (inferInstance : MeasurableSpace Disorder) := by
    rw [← Gaussian.disorderBlock_zero (t s)]
    exact Gaussian.disorderBlock_le 0 (t s)
  have hPGsubset : PG ⊆ blockGoodSet β t r s := fun _ hω => hω.1
  have hWenergyIntBlock := commonCorrection_integral_energy_le_of_openCorrector
    β t N r s K ht hr hsK hts θ C₀ hθ0 hθ1 hOpen
  have hWenergyInt : IntegrableOn
      (fun ω => futureEnergy β (t s) N (W ω)) PG disorderLaw := by
    exact hWenergyIntBlock.1.mono_set (by simpa [PG, W] using hPGsubset)
  have hWenergyMeas : Measurable (fun ω => futureEnergy β (t s) N (W ω)) := by
    exact (measurable_commonCorrection_futureEnergy β t N r s ht hr hrs hts).mono
      hpast le_rfl
  have hWrootInt := setIntegral_sqrt_le_sqrt
    (fun ω => futureEnergy β (t s) N (W ω)) PG hWenergyMeas
    (fun ω => futureEnergy_nonneg β (t s) N (W ω)) hWenergyInt
  have hUenergyIntGlobal := integrable_futureEnergy_smoothedEndpointDist β
    (t (r - 1)) (t s) N htimes hts 0
  have hUenergyMeas : Measurable (fun ω => futureEnergy β (t s) N (U ω)) := by
    have hUcoord : ∀ y, Measurable[disorderPast (t s)] (U · y) := hUmeas
    exact (measurable_futureEnergy β hts U SU (fun ω y hy => hUzero ω y hy)
      hUcoord).mono hpast le_rfl
  have hUenergyInt : IntegrableOn
      (fun ω => futureEnergy β (t s) N (U ω)) PG disorderLaw :=
    hUenergyIntGlobal.integrableOn
  have hUrootInt := setIntegral_sqrt_le_sqrt
    (fun ω => futureEnergy β (t s) N (U ω)) PG hUenergyMeas
    (fun ω => futureEnergy_nonneg β (t s) N (U ω)) hUenergyInt
  let EU : Disorder → ℝ := fun ω => futureEnergy β (t s) N (U ω)
  let EW : Disorder → ℝ := fun ω => futureEnergy β (t s) N (W ω)
  let EV : ℝ := futureEnergy β (t s) N V
  have hPGmeas : MeasurableSet PG := by
    have hpastSet :=
      LogNormality.measurableSet_profileGoodSet_past β ht hr hrs
    change MeasurableSet[Gaussian.disorderBlock 0 (t s)] PG at hpastSet
    exact Gaussian.disorderBlock_le 0 (t s) PG hpastSet
  have hVenergyInt : IntegrableOn (fun _ : Disorder => EV) PG disorderLaw :=
    (integrable_const EV).integrableOn
  have hRenergyMeas : Measurable (fun ω => futureEnergy β (t s) N (R ω)) := by
    exact (measurable_futureEnergy β hts R S hRzero hRmeas).mono hpast le_rfl
  have hRenergyBound (ω : Disorder) :
      futureEnergy β (t s) N (R ω) ≤ 3 * (EU ω + EV + EW ω) := by
    have hUzeroS' (y : Site) (hy : y ∉ S) : U ω y = 0 := hUzeroS ω y hy
    have hVzeroS (y : Site) (hy : y ∉ S) : V y = 0 := hVzero y hy
    have hWzeroS' (y : Site) (hy : y ∉ S) : W ω y = 0 := hWzeroS ω y hy
    have hU_V : ∀ y ∉ S, (U ω + -V) y = 0 := by
      intro y hy
      simp [hUzeroS' y hy, hVzeroS y hy]
    have hWneg : ∀ y ∉ S, (-W ω) y = 0 := by
      intro y hy
      simp [hWzeroS' y hy]
    have hdecomp : R ω = U ω + -V + -W ω := by
      ext y
      simp [R]
      ring
    have htri₁ := sqrt_futureEnergy_add_le β (t s) N (U ω) (-V) S
      (fun y hy => hUzeroS' y hy) (fun y hy => by simpa using hVzeroS y hy)
    have htri₂ := sqrt_futureEnergy_add_le β (t s) N (U ω + -V) (-W ω) S
      hU_V hWneg
    have hEnegV : futureEnergy β (t s) N (-V) = EV := by
      simpa [EV, Pi.smul_apply, smul_eq_mul] using
        (futureEnergy_smul β (t s) N (-1) V S (fun y hy => hVzero y hy))
    have hEnegW : futureEnergy β (t s) N (-W ω) = EW ω := by
      simpa [EW, Pi.smul_apply, smul_eq_mul] using
        (futureEnergy_smul β (t s) N (-1) (W ω) S (fun y hy => hWzeroS ω y hy))
    have hrootBound : Real.sqrt (futureEnergy β (t s) N (R ω)) ≤
        Real.sqrt (EU ω) + Real.sqrt EV + Real.sqrt (EW ω) := by
      rw [hdecomp]
      calc
        Real.sqrt (futureEnergy β (t s) N (U ω + -V + -W ω)) ≤
            Real.sqrt (futureEnergy β (t s) N (U ω + -V)) +
              Real.sqrt (futureEnergy β (t s) N (-W ω)) := htri₂
        _ = Real.sqrt (futureEnergy β (t s) N (U ω + -V)) + Real.sqrt (EW ω) := by
          rw [hEnegW]
        _ ≤ Real.sqrt (EU ω) + Real.sqrt (futureEnergy β (t s) N (-V)) +
              Real.sqrt (EW ω) := by gcongr
        _ = Real.sqrt (EU ω) + Real.sqrt EV + Real.sqrt (EW ω) := by rw [hEnegV]
    have hsq : (Real.sqrt (futureEnergy β (t s) N (R ω))) ^ 2 ≤
        (Real.sqrt (EU ω) + Real.sqrt EV + Real.sqrt (EW ω)) ^ 2 :=
      (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).2 hrootBound
    have hEU : (Real.sqrt (EU ω)) ^ 2 = EU ω :=
      Real.sq_sqrt (futureEnergy_nonneg β (t s) N (U ω))
    have hEV : (Real.sqrt EV) ^ 2 = EV :=
      Real.sq_sqrt (futureEnergy_nonneg β (t s) N V)
    have hEW : (Real.sqrt (EW ω)) ^ 2 = EW ω :=
      Real.sq_sqrt (futureEnergy_nonneg β (t s) N (W ω))
    rw [Real.sq_sqrt (futureEnergy_nonneg β (t s) N (R ω))] at hsq
    nlinarith [sq_nonneg (Real.sqrt (EU ω) - Real.sqrt EV),
      sq_nonneg (Real.sqrt (EU ω) - Real.sqrt (EW ω)),
      sq_nonneg (Real.sqrt EV - Real.sqrt (EW ω)), hEU, hEV, hEW]
  have hRenergyInt : IntegrableOn
      (fun ω => futureEnergy β (t s) N (R ω)) PG disorderLaw := by
    have hmajor : IntegrableOn (fun ω => 3 * (EU ω + EV + EW ω)) PG disorderLaw := by
      change Integrable (fun ω => 3 * (EU ω + EV + EW ω))
        (disorderLaw.restrict PG)
      simpa [EU, EW, EV, add_assoc] using
        (hUenergyInt.add (hVenergyInt.add hWenergyInt)).const_mul 3
    apply hmajor.mono' hRenergyMeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem hPGmeas] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (futureEnergy_nonneg β (t s) N (R ω))]
    have hEU0 : 0 ≤ EU ω := futureEnergy_nonneg β (t s) N (U ω)
    have hEV0 : 0 ≤ EV := futureEnergy_nonneg β (t s) N V
    have hEW0 : 0 ≤ EW ω := futureEnergy_nonneg β (t s) N (W ω)
    have hmajorNonneg : 0 ≤ 3 * (EU ω + EV + EW ω) := by positivity
    simpa [EU, EW, EV, Real.norm_eq_abs, abs_of_nonneg hmajorNonneg] using
      hRenergyBound ω
  exact integrableOn_sqrt_futureEnergy_of_integrable β hts R S hRzero hRmeas
    PG hRenergyInt

/-- An integrable root-energy comparison for the difference of the two endpoint laws.
The bound follows from future-energy estimates for the residual profiles and open correctors. -/
theorem endpoint_root_comparison_integral_le
    (β : ℝ) (t : ℕ → ℕ) (N K a b J : ℕ) (ht : Monotone t)
    (ht0 : t 0 = 0)
    (hJ : 2 ≤ J) (hK : K = b + J) (hba : b = a + J) (hts : t b ≤ N)
    (θ Copen Cpe : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hOpen : ∀ u : ℕ, 1 ≤ u → u ≤ b →
      ∫ ω in blockGoodSet β t u b,
        futureEnergy β (t b) N (openCorrector β t u b ω) ∂disorderLaw ≤
          Copen * θ ^ (2 * (b - u)) / ((K : ℝ) - u))
    (G : Set Disorder)
    (hG0 : G ⊆ profileGoodSet β t 1 b)
    (hG1 : G ⊆ profileGoodSet β t (a + 1) b)
    (hResidual0 : ∫ ω in profileGoodSet β t 1 b,
      Real.sqrt (futureEnergy β (t b) N (fun y =>
        smoothedEndpointDist β 0 (t b) 0 ω y - srwKernel (t b) y -
          commonCorrection β t 1 b ω y)) ∂disorderLaw ≤ Cpe / ((K : ℝ) - b))
    (hResidual1 : ∫ ω in profileGoodSet β t (a + 1) b,
      Real.sqrt (futureEnergy β (t b) N (fun y =>
        smoothedEndpointDist β (t a) (t b) 0 ω y - srwKernel (t b) y -
          commonCorrection β t (a + 1) b ω y)) ∂disorderLaw ≤ Cpe / ((K : ℝ) - b)) :
    IntegrableOn (fun ω => Real.sqrt (futureEnergy β (t b) N (fun y =>
      smoothedEndpointDist β 0 (t b) 0 ω y - smoothedEndpointDist β (t a) (t b) 0 ω y)))
      G disorderLaw ∧
    ∫ ω in G, Real.sqrt (futureEnergy β (t b) N (fun y =>
      smoothedEndpointDist β 0 (t b) 0 ω y - smoothedEndpointDist β (t a) (t b) 0 ω y))
      ∂disorderLaw ≤
        (2 * |Cpe| + Real.sqrt |Copen| / (1 - θ) ^ 2) / (J : ℝ) := by
  classical
  let m := t a
  let n := t b
  let I := Finset.Icc 1 a
  let PG0 := profileGoodSet β t 1 b
  let PG1 := profileGoodSet β t (a + 1) b
  let U0 : Disorder → Site → ℝ := smoothedEndpointDist β 0 n 0
  let U1 : Disorder → Site → ℝ := smoothedEndpointDist β m n 0
  let η : Disorder → Site → ℝ := fun ω y => U0 ω y - U1 ω y
  let R0 : Disorder → Site → ℝ := fun ω y =>
    U0 ω y - srwKernel n y - commonCorrection β t 1 b ω y
  let R1 : Disorder → Site → ℝ := fun ω y =>
    U1 ω y - srwKernel n y - commonCorrection β t (a + 1) b ω y
  let O : Disorder → Site → ℝ := fun ω y =>
    ∑ u ∈ I, openCorrector β t u b ω y
  have hab : a ≤ b := by omega
  have hmn : m ≤ n := by dsimp [m, n]; exact ht hab
  let Scorr := (Finset.Icc 1 b).biUnion (fun u => openCorrectorNumeratorSupport t u b)
  obtain ⟨Sprob, hU0zero, hU1zero, hdiffzero, hU0mass, hU1mass, hdiffmass,
      hdiffBound⟩ := endpoint_smoothing_difference_probability_data β hmn
  let S := Sprob ∪ Polymer.endpoints 0 n ∪ Scorr
  have hηzero (ω : Disorder) (y : Site) (hy : y ∉ Sprob) : η ω y = 0 := by
    exact hdiffzero ω y (by simpa [m, n, U0, U1] using hy)
  have hηmass (ω : Disorder) : ∑ y ∈ Sprob, η ω y = 0 := by
    simpa [η, U0, U1, m, n] using hdiffmass ω
  have hηbound (ω : Disorder) (y : Site) : |η ω y| ≤ 2 := by
    simpa [η, U0, U1, m, n] using hdiffBound ω y
  have hηmeas (y : Site) : Measurable[disorderPast n] (η · y) := by
    dsimp [η, U0, U1]
    exact measurable_endpoint_smoothing_difference_past β hmn y
  have hVzero (y : Site) (hy : y ∉ S) : srwKernel n y = 0 := by
    have hy' : y ∉ Polymer.endpoints 0 n := by
      intro hmem
      exact hy (Finset.mem_union_left _ (Finset.mem_union_right _ hmem))
    simpa only [sub_zero] using Polymer.srwKernel_eq_zero_of_not_mem n 0 y hy'
  have hCorrzero (r : ℕ) (hr : 1 ≤ r) (hrs : r ≤ b)
      (ω : Disorder) (y : Site) (hy : y ∉ Scorr) :
      commonCorrection β t r b ω y = 0 := by
    unfold commonCorrection
    apply Finset.sum_eq_zero
    intro u hu
    have hyu : y ∉ openCorrectorNumeratorSupport t u b := by
      intro hmem
      have hu' := Finset.mem_Icc.mp hu
      exact hy (Finset.mem_biUnion.mpr ⟨u,
        Finset.mem_Icc.mpr ⟨le_trans hr hu'.1, hu'.2⟩, hmem⟩)
    unfold openCorrector
    rw [openCorrectorNumerator_eq_zero_of_not_mem_support β t u b ω y hyu, zero_div]
  have hR0zero (ω : Disorder) (y : Site) (hy : y ∉ S) : R0 ω y = 0 := by
    have hyProb : y ∉ Sprob := by
      intro hmem
      exact hy (Finset.mem_union_left _ (Finset.mem_union_left _ hmem))
    have hU : U0 ω y = 0 := hU0zero ω y hyProb
    have hC : commonCorrection β t 1 b ω y = 0 := hCorrzero 1 (by omega) (by omega)
      ω y (by intro hmem; exact hy (Finset.mem_union_right _ hmem))
    simp [R0, U0, hU, hVzero y hy, hC]
  have hR1zero (ω : Disorder) (y : Site) (hy : y ∉ S) : R1 ω y = 0 := by
    have hyProb : y ∉ Sprob := by
      intro hmem
      exact hy (Finset.mem_union_left _ (Finset.mem_union_left _ hmem))
    have hU : U1 ω y = 0 := hU1zero ω y hyProb
    have hC : commonCorrection β t (a + 1) b ω y = 0 :=
      hCorrzero (a + 1) (by omega) (by omega) ω y
        (by intro hmem; exact hy (Finset.mem_union_right _ hmem))
    simp [R1, U1, hU, hVzero y hy, hC]
  have hOzero (ω : Disorder) (y : Site) (hy : y ∉ S) : O ω y = 0 := by
    dsimp [O]
    apply Finset.sum_eq_zero
    intro u hu
    have hyu : y ∉ openCorrectorNumeratorSupport t u b := by
      intro hmem
      have hu' := Finset.mem_Icc.mp hu
      exact hy (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨u,
        Finset.mem_Icc.mpr ⟨hu'.1, le_trans hu'.2 hab⟩, hmem⟩))
    unfold openCorrector
    rw [openCorrectorNumerator_eq_zero_of_not_mem_support β t u b ω y hyu, zero_div]
  have hdecomp (ω : Disorder) : η ω = R0 ω - R1 ω + O ω := by
    funext y
    change U0 ω y - U1 ω y =
      (U0 ω y - srwKernel n y - commonCorrection β t 1 b ω y) -
        (U1 ω y - srwKernel n y - commonCorrection β t (a + 1) b ω y) +
          ∑ u ∈ I, openCorrector β t u b ω y
    calc
      _ = (U0 ω y - srwKernel n y - commonCorrection β t 1 b ω y) -
            (U1 ω y - srwKernel n y - commonCorrection β t (a + 1) b ω y) +
              (commonCorrection β t 1 b ω y - commonCorrection β t (a + 1) b ω y) := by ring
      _ = _ := by rw [commonCorrection_sub_eq β t hab ω y]
  have hR0int := integrableOn_sqrt_profileResidual β t N K ht
    (by omega : 1 ≤ 1) (by omega : 1 ≤ b) (by omega : b + 2 ≤ K)
    hts θ Copen hθ0 hθ1 (fun u hu hus => hOpen u hu hus)
  have hR1int := integrableOn_sqrt_profileResidual β t N K ht
    (by omega : 1 ≤ a + 1) (by omega : a + 1 ≤ b) (by omega : b + 2 ≤ K)
    hts θ Copen hθ0 hθ1 (fun u hu hus => hOpen u (by omega) hus)
  have hR0PGint : IntegrableOn
      (fun ω => Real.sqrt (futureEnergy β n N (R0 ω))) PG0 disorderLaw := by
    simpa [R0, n, U0, PG0, ht0] using hR0int
  have hR1PGint : IntegrableOn
      (fun ω => Real.sqrt (futureEnergy β n N (R1 ω))) PG1 disorderLaw := by
    simpa [R1, n, m, U1, PG1] using hR1int
  have hR0Gint : IntegrableOn
      (fun ω => Real.sqrt (futureEnergy β n N (R0 ω))) G disorderLaw := by
    exact hR0PGint.mono_set (by simpa [PG0] using hG0)
  have hR1Gint : IntegrableOn
      (fun ω => Real.sqrt (futureEnergy β n N (R1 ω))) G disorderLaw := by
    exact hR1PGint.mono_set (by simpa [PG1] using hG1)
  have hηrootInt : IntegrableOn
      (fun ω => Real.sqrt (futureEnergy β n N (η ω))) G disorderLaw := by
    have hglobal := integrable_sqrt_futureEnergy β (by simpa [n] using hts) η Sprob
      (fun ω y hy => hηzero ω y hy) ⟨2, hηbound⟩ hηmeas
    exact hglobal.integrableOn
  have hGblock0 : G ⊆ blockGoodSet β t 1 b := by
    intro ω hω
    exact (hG0 hω).1
  have hOpenRoot (u : ℕ) (hu : u ∈ I) :
      IntegrableOn (fun ω => Real.sqrt (futureEnergy β n N (openCorrector β t u b ω)))
        G disorderLaw ∧
      ∫ ω in G, Real.sqrt (futureEnergy β n N (openCorrector β t u b ω)) ∂disorderLaw ≤
        Real.sqrt |Copen| * θ ^ (b - u) / Real.sqrt J := by
    have hu' := Finset.mem_Icc.mp hu
    have hus : u ≤ b := le_trans hu'.2 hab
    have hKu : (J : ℝ) ≤ (K : ℝ) - u := by
      have hNat : J ≤ K - u := by omega
      rw [← Nat.cast_sub (by omega : u ≤ K)]
      exact_mod_cast hNat
    exact integral_sqrt_futureEnergy_openCorrector_le β t N K J u b ht hu'.1 hus
      hts (by omega) hKu θ Copen hθ0 hθ1 (hOpen u hu'.1 hus) G
      (by
        intro ω hω
        have hblock := hGblock0 hω
        simp only [blockGoodSet, Set.mem_ofPred_eq] at hblock ⊢
        intro i hi
        apply hblock i
        simp only [Finset.mem_Icc] at hi ⊢
        omega)
  have hOpenInt : IntegrableOn
      (fun ω => ∑ u ∈ I, Real.sqrt (futureEnergy β n N (openCorrector β t u b ω)))
        G disorderLaw := by
    apply integrable_finsetSum
    intro u hu
    exact (hOpenRoot u hu).1
  have hpoint (ω : Disorder) : Real.sqrt (futureEnergy β n N (η ω)) ≤
      Real.sqrt (futureEnergy β n N (R0 ω)) + Real.sqrt (futureEnergy β n N (R1 ω)) +
        ∑ u ∈ I, Real.sqrt (futureEnergy β n N (openCorrector β t u b ω)) := by
    have hnegR1 : ∀ y ∉ S, (-R1 ω) y = 0 := by
      intro y hy
      simp [hR1zero ω y hy]
    have hdiffR : ∀ y ∉ S, (R0 ω - R1 ω) y = 0 := by
      intro y hy
      simp [hR0zero ω y hy, hR1zero ω y hy]
    have hnegEnergy : futureEnergy β n N (-R1 ω) = futureEnergy β n N (R1 ω) := by
      simpa [Pi.smul_apply, smul_eq_mul] using
        (futureEnergy_smul β n N (-1) (R1 ω) S (fun y hy => hR1zero ω y hy))
    have htri := sqrt_futureEnergy_add_le β n N (R0 ω) (-R1 ω) S
      (fun y hy => hR0zero ω y hy) hnegR1
    have htriO := sqrt_futureEnergy_add_le β n N (R0 ω - R1 ω) (O ω) S
      hdiffR (fun y hy => hOzero ω y hy)
    have hfin := sqrt_futureEnergy_finset_sum_le β n N S I
      (fun u y => openCorrector β t u b ω y)
      (fun u hu y hy => by
        have hu' := Finset.mem_Icc.mp hu
        have hyu : y ∉ openCorrectorNumeratorSupport t u b := by
          intro hmem
          exact hy (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨u,
            Finset.mem_Icc.mpr ⟨hu'.1, by omega⟩, hmem⟩))
        unfold openCorrector
        rw [openCorrectorNumerator_eq_zero_of_not_mem_support β t u b ω y hyu, zero_div])
    rw [hdecomp ω]
    calc
      _ = Real.sqrt (futureEnergy β n N (R0 ω - R1 ω + O ω)) := by rfl
      _ ≤ Real.sqrt (futureEnergy β n N (R0 ω - R1 ω)) +
          Real.sqrt (futureEnergy β n N (O ω)) := htriO
      _ ≤ Real.sqrt (futureEnergy β n N (R0 ω)) +
          Real.sqrt (futureEnergy β n N (-R1 ω)) +
          Real.sqrt (futureEnergy β n N (O ω)) := by
        exact add_le_add_left htri _
      _ = Real.sqrt (futureEnergy β n N (R0 ω)) +
          Real.sqrt (futureEnergy β n N (R1 ω)) +
          Real.sqrt (futureEnergy β n N (O ω)) := by rw [hnegEnergy]
      _ ≤ _ := by
        have hO : O ω = ∑ u ∈ I, fun y => openCorrector β t u b ω y := by
          funext y
          simp [O, Finset.sum_apply]
        simpa [hO] using hfin
  have hrightInt : IntegrableOn (fun ω =>
      (Real.sqrt (futureEnergy β n N (R0 ω)) +
        Real.sqrt (futureEnergy β n N (R1 ω))) +
        ∑ u ∈ I, Real.sqrt (futureEnergy β n N (openCorrector β t u b ω)))
      G disorderLaw := by
    exact (hR0Gint.add hR1Gint).add hOpenInt
  have hboundIntegral : ∫ ω in G, Real.sqrt (futureEnergy β n N (η ω)) ∂disorderLaw ≤
      ∫ ω in G, Real.sqrt (futureEnergy β n N (R0 ω)) ∂disorderLaw +
        ∫ ω in G, Real.sqrt (futureEnergy β n N (R1 ω)) ∂disorderLaw +
        ∑ u ∈ I, ∫ ω in G,
          Real.sqrt (futureEnergy β n N (openCorrector β t u b ω)) ∂disorderLaw := by
    calc
      _ ≤ ∫ ω in G,
          Real.sqrt (futureEnergy β n N (R0 ω)) +
            Real.sqrt (futureEnergy β n N (R1 ω)) +
            ∑ u ∈ I, Real.sqrt (futureEnergy β n N (openCorrector β t u b ω))
          ∂disorderLaw := integral_mono_ae hηrootInt hrightInt
            (Filter.Eventually.of_forall hpoint)
      _ = ∫ ω in G,
          Real.sqrt (futureEnergy β n N (R0 ω)) +
            (Real.sqrt (futureEnergy β n N (R1 ω)) +
              ∑ u ∈ I, Real.sqrt (futureEnergy β n N (openCorrector β t u b ω)))
          ∂disorderLaw := by
        apply integral_congr_ae
        filter_upwards [] with ω
        ring
      _ = (∫ ω in G, Real.sqrt (futureEnergy β n N (R0 ω)) ∂disorderLaw) +
          (∫ ω in G, Real.sqrt (futureEnergy β n N (R1 ω)) ∂disorderLaw) +
          (∫ ω in G, ∑ u ∈ I,
            Real.sqrt (futureEnergy β n N (openCorrector β t u b ω)) ∂disorderLaw) := by
        calc
          _ = (∫ ω in G, Real.sqrt (futureEnergy β n N (R0 ω)) ∂disorderLaw) +
              (∫ ω in G,
                Real.sqrt (futureEnergy β n N (R1 ω)) +
                  ∑ u ∈ I, Real.sqrt (futureEnergy β n N (openCorrector β t u b ω))
                ∂disorderLaw) := by
              simpa only [Pi.add_apply] using
                (integral_add hR0Gint (hR1Gint.add hOpenInt))
          _ = _ := by
            rw [show (∫ ω in G,
                Real.sqrt (futureEnergy β n N (R1 ω)) +
                  ∑ u ∈ I, Real.sqrt (futureEnergy β n N (openCorrector β t u b ω))
                ∂disorderLaw) = _ from
              (integral_add hR1Gint hOpenInt)]
            ring
      _ = _ := by
        rw [integral_finsetSum _ (fun u hu => (hOpenRoot u hu).1)]
  have hJreal : 0 < (J : ℝ) := by exact_mod_cast (by omega : 0 < J)
  have hdenEq : (K : ℝ) - b = (J : ℝ) := by
    have hNat : K - b = J := by omega
    rw [← Nat.cast_sub (by omega : b ≤ K)]
    exact_mod_cast hNat
  have hres0abs : ∫ ω in PG0,
      Real.sqrt (futureEnergy β n N (R0 ω)) ∂disorderLaw ≤ |Cpe| / (J : ℝ) := by
    calc
      _ ≤ Cpe / ((K : ℝ) - b) := by simpa [PG0, R0, n] using hResidual0
      _ ≤ |Cpe| / (J : ℝ) := by
        rw [hdenEq]
        exact div_le_div_of_nonneg_right (le_abs_self Cpe) (le_of_lt hJreal)
  have hres1abs : ∫ ω in PG1,
      Real.sqrt (futureEnergy β n N (R1 ω)) ∂disorderLaw ≤ |Cpe| / (J : ℝ) := by
    calc
      _ ≤ Cpe / ((K : ℝ) - b) := by simpa [PG1, R1, n, m] using hResidual1
      _ ≤ |Cpe| / (J : ℝ) := by
        rw [hdenEq]
        exact div_le_div_of_nonneg_right (le_abs_self Cpe) (le_of_lt hJreal)
  have hres0G : ∫ ω in G, Real.sqrt (futureEnergy β n N (R0 ω)) ∂disorderLaw ≤
      |Cpe| / (J : ℝ) := by
    calc
      _ ≤ ∫ ω in PG0, Real.sqrt (futureEnergy β n N (R0 ω)) ∂disorderLaw :=
        setIntegral_mono_set hR0PGint (Filter.Eventually.of_forall fun ω => Real.sqrt_nonneg _)
          (Filter.Eventually.of_forall fun ω hω => hG0 (by simpa [PG0] using hω))
      _ ≤ _ := hres0abs
  have hres1G : ∫ ω in G, Real.sqrt (futureEnergy β n N (R1 ω)) ∂disorderLaw ≤
      |Cpe| / (J : ℝ) := by
    calc
      _ ≤ ∫ ω in PG1, Real.sqrt (futureEnergy β n N (R1 ω)) ∂disorderLaw :=
        setIntegral_mono_set hR1PGint (Filter.Eventually.of_forall fun ω => Real.sqrt_nonneg _)
          (Filter.Eventually.of_forall fun ω hω => hG1 (by simpa [PG1] using hω))
      _ ≤ _ := hres1abs
  have hsumRoot : ∑ u ∈ I, ∫ ω in G,
      Real.sqrt (futureEnergy β n N (openCorrector β t u b ω)) ∂disorderLaw ≤
      Real.sqrt |Copen| * θ ^ J / ((1 - θ) * Real.sqrt J) := by
    calc
      _ ≤ ∑ u ∈ I, (Real.sqrt |Copen| * θ ^ (b - u) / Real.sqrt J) :=
        Finset.sum_le_sum fun u hu => (hOpenRoot u hu).2
      _ = Real.sqrt |Copen| / Real.sqrt J * ∑ u ∈ I, θ ^ (b - u) := by
        calc
          _ = ∑ u ∈ I, (Real.sqrt |Copen| / Real.sqrt J) * θ ^ (b - u) := by
            apply Finset.sum_congr rfl
            intro u hu
            ring
          _ = _ := by rw [Finset.mul_sum]
      _ ≤ Real.sqrt |Copen| / Real.sqrt J * (θ ^ J / (1 - θ)) := by
        have hgeom := sum_pow_gap_le θ hθ0.le hθ1 (a := a) (J := J)
        have hgeom' : ∑ u ∈ I, θ ^ (b - u) ≤ θ ^ J / (1 - θ) := by
          simpa [I, hba] using hgeom
        exact mul_le_mul_of_nonneg_left hgeom' (by positivity)
      _ = _ := by
        have hθ : 1 - θ ≠ 0 := ne_of_gt (sub_pos.mpr hθ1)
        have hJ' : Real.sqrt (J : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hJreal)
        field_simp [hθ, hJ']
  have hrootJ := sqrt_nat_mul_pow_le θ hθ0 hθ1 J (by omega)
  have hsumRoot' :
      Real.sqrt |Copen| * θ ^ J / ((1 - θ) * Real.sqrt J) ≤
        Real.sqrt |Copen| / ((1 - θ) ^ 2 * (J : ℝ)) := by
    have hden0 : 0 < (1 - θ) * Real.sqrt J := by positivity
    have hden1 : 0 < (1 - θ) ^ 2 * (J : ℝ) := by positivity
    apply (div_le_div_iff₀ hden0 hden1).2
    have hsqrtJ : 0 < Real.sqrt (J : ℝ) := Real.sqrt_pos.2 hJreal
    have hrootIneq : (1 - θ) * Real.sqrt (J : ℝ) * θ ^ J ≤ 1 := by
      calc
        _ = (1 - θ) * (Real.sqrt (J : ℝ) * θ ^ J) := by ring
        _ ≤ (1 - θ) * (1 / (1 - θ)) :=
          mul_le_mul_of_nonneg_left hrootJ (sub_nonneg.mpr hθ1.le)
        _ = 1 := by field_simp [ne_of_gt (sub_pos.mpr hθ1)]
    have hsqrtJ2 : (Real.sqrt (J : ℝ)) ^ 2 = (J : ℝ) :=
      Real.sq_sqrt (Nat.cast_nonneg J)
    have hcross : θ ^ J * ((1 - θ) ^ 2 * (J : ℝ)) ≤
        (1 - θ) * Real.sqrt (J : ℝ) := by
      calc
        _ = θ ^ J * ((1 - θ) ^ 2 * (Real.sqrt (J : ℝ)) ^ 2) := by rw [hsqrtJ2]
        _ = ((1 - θ) * Real.sqrt (J : ℝ) * θ ^ J) *
            ((1 - θ) * Real.sqrt (J : ℝ)) := by ring
        _ ≤ 1 * ((1 - θ) * Real.sqrt (J : ℝ)) :=
          mul_le_mul_of_nonneg_right hrootIneq (by positivity)
        _ = _ := by ring
    calc
      Real.sqrt |Copen| * θ ^ J * ((1 - θ) ^ 2 * (J : ℝ)) =
          Real.sqrt |Copen| * (θ ^ J * ((1 - θ) ^ 2 * (J : ℝ))) := by ring
      _ ≤ Real.sqrt |Copen| * ((1 - θ) * Real.sqrt (J : ℝ)) :=
        mul_le_mul_of_nonneg_left hcross (Real.sqrt_nonneg |Copen|)
  refine ⟨hηrootInt, ?_⟩
  calc
    _ ≤ |Cpe| / (J : ℝ) + |Cpe| / (J : ℝ) +
        Real.sqrt |Copen| * θ ^ J / ((1 - θ) * Real.sqrt J) := by
          exact hboundIntegral.trans (add_le_add (add_le_add hres0G hres1G) hsumRoot)
    _ ≤ 2 * |Cpe| / (J : ℝ) +
        Real.sqrt |Copen| / ((1 - θ) ^ 2 * (J : ℝ)) := by
          exact add_le_add (le_of_eq (by ring)) hsumRoot'
    _ = (2 * |Cpe| + Real.sqrt |Copen| / (1 - θ) ^ 2) / (J : ℝ) := by
      field_simp [ne_of_gt hJreal]

end Critical2DKPZ.FutureProfiles

end
