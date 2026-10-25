/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.ExpectedHeatEnergy
public import Critical2DKPZ.Analysis.Sobolev.Rellich.FrozenDistributionBound
public import Critical2DKPZ.Analysis.Sobolev.Rellich.LocalCompactnessExtraction
public import Critical2DKPZ.Analysis.Sobolev.Topology

/-! # Almost-sure local Sobolev limits -/

public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

namespace Critical2DKPZ.LocalSobolev


/-- A two-parameter expected-energy limit provides a common positive radius on which every pair
of positive smoothing parameters has small expected energy. -/
theorem exists_pos_radius_expected_localNegSobolevSq_lt
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℝ → Ω → Distr) (a : ℝ) (χ : TestFn)
    (hC : Tendsto
      (fun p : ℝ × ℝ =>
        ∫⁻ ω, localNegSobolevSq a (F p.1 ω - F p.2 ω) χ ∂P)
      (nhdsWithin 0 (Ioi 0) ×ˢ nhdsWithin 0 (Ioi 0)) (𝓝 0))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ δ δ' : ℝ, 0 < δ → δ < r → 0 < δ' → δ' < r →
      ∫⁻ ω, localNegSobolevSq a (F δ ω - F δ' ω) χ ∂P < ε := by
  have hev : ∀ᶠ p in nhdsWithin 0 (Ioi 0) ×ˢ nhdsWithin 0 (Ioi 0),
      (fun p : ℝ × ℝ =>
        ∫⁻ ω, localNegSobolevSq a (F p.1 ω - F p.2 ω) χ ∂P) p ∈ Iio ε :=
    hC.eventually (Iio_mem_nhds hε)
  obtain ⟨p, hp, q, hq, hrect⟩ := Filter.eventually_prod_iff.mp hev
  obtain ⟨r, hr, hpr⟩ := Metric.nhdsWithin_basis_ball.mem_iff.mp hp
  obtain ⟨s, hs, hqs⟩ := Metric.nhdsWithin_basis_ball.mem_iff.mp hq
  refine ⟨min r s, lt_min hr hs, ?_⟩
  intro δ δ' hδ hδr hδ' hδ'r
  apply hrect
  · apply hpr
    refine ⟨Metric.mem_ball.mpr ?_, hδ⟩
    simpa [Real.dist_eq, abs_of_pos hδ] using hδr.trans_le (min_le_left _ _)
  · apply hqs
    refine ⟨Metric.mem_ball.mpr ?_, hδ'⟩
    simpa [Real.dist_eq, abs_of_pos hδ'] using hδ'r.trans_le (min_le_right _ _)

/-- One radius works for finitely many of the canonical localizers. -/
theorem exists_pos_radius_expected_localizer_energies_lt
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℝ → Ω → Distr) (a : ℝ) (K : Finset ℕ)
    (hC : ∀ k ∈ K, Tendsto
      (fun p : ℝ × ℝ =>
        ∫⁻ ω, localNegSobolevSq a (F p.1 ω - F p.2 ω) (localizer k) ∂P)
      (nhdsWithin 0 (Ioi 0) ×ˢ nhdsWithin 0 (Ioi 0)) (𝓝 0))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ δ δ' : ℝ, 0 < δ → δ < r → 0 < δ' → δ' < r →
      ∀ k ∈ K, ∫⁻ ω, localNegSobolevSq a (F δ ω - F δ' ω) (localizer k) ∂P < ε := by
  classical
  induction K using Finset.induction_on with
  | empty =>
      refine ⟨1, by norm_num, ?_⟩
      intro δ δ' hδ hδr hδ' hδ'r k hk
      simp at hk
  | @insert k K hk ih =>
      obtain ⟨r₁, hr₁, h₁⟩ := exists_pos_radius_expected_localNegSobolevSq_lt
        P F a (localizer k) (hC k (Finset.mem_insert_self ..)) hε
      have hC' : ∀ j ∈ K, Tendsto
          (fun p : ℝ × ℝ =>
            ∫⁻ ω, localNegSobolevSq a (F p.1 ω - F p.2 ω) (localizer j) ∂P)
          (nhdsWithin 0 (Ioi 0) ×ˢ nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
        intro j hj
        exact hC j (Finset.mem_insert_of_mem hj)
      obtain ⟨r₂, hr₂, h₂⟩ := ih hC'
      refine ⟨min r₁ r₂, lt_min hr₁ hr₂, ?_⟩
      intro δ δ' hδ hδr hδ' hδ'r j hj
      have hδ₁ : δ < r₁ := hδr.trans_le (min_le_left _ _)
      have hδ'₁ : δ' < r₁ := hδ'r.trans_le (min_le_left _ _)
      have hδ₂ : δ < r₂ := hδr.trans_le (min_le_right _ _)
      have hδ'₂ : δ' < r₂ := hδ'r.trans_le (min_le_right _ _)
      rcases Finset.mem_insert.mp hj with rfl | hjK
      · exact h₁ δ δ' hδ hδ₁ hδ' hδ'₁
      · exact h₂ δ δ' hδ hδ₂ hδ' hδ'₂ j hjK

/-- From positive control radii one can choose a positive sequence tending to zero that eventually
lies below every previously specified radius. -/
theorem exists_pos_sequence_tendsto_zero_below_prefix {R : ℕ → ℝ}
    (hR : ∀ n, 0 < R n) :
    ∃ δ : ℕ → ℝ, (∀ n, 0 < δ n) ∧
      Tendsto δ atTop (nhdsWithin 0 (Ioi 0)) ∧
      ∀ j n, j ≤ n → δ n < R j := by
  let δ : ℕ → ℝ := Nat.rec (min (1 / 2 : ℝ) (R 0 / 2))
    (fun n x => min (x / 2) (min (1 / ((n : ℝ) + 2)) (R (n + 1) / 2)))
  have hδpos : ∀ n, 0 < δ n := by
    intro n
    induction n with
    | zero =>
        simp only [δ]
        apply lt_min
        · norm_num
        · exact half_pos (hR 0)
    | succ n ih =>
        simp only [δ]
        apply lt_min
        · exact half_pos ih
        · apply lt_min
          · positivity
          · exact half_pos (hR (n + 1))
  have hδle : ∀ n, δ n ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    induction n with
    | zero =>
        simp only [δ]
        norm_num
    | succ n ih =>
        have hden : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by
          norm_cast
        rw [hden]
        simp only [δ]
        exact (min_le_right _ _).trans (min_le_left _ _)
  have hδmono : ∀ n, δ (n + 1) ≤ δ n := by
    intro n
    simp only [δ]
    exact (min_le_left _ _).trans (by linarith [hδpos n])
  have hδR : ∀ n, δ n ≤ R n / 2 := by
    intro n
    induction n with
    | zero => simp only [δ]; exact min_le_right _ _
    | succ n ih =>
        simp only [δ]
        exact (min_le_right _ _).trans (min_le_right _ _)
  have hδzero : Tendsto δ atTop (𝓝 0) :=
    squeeze_zero (fun n => le_of_lt (hδpos n)) hδle
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hδwithin : Tendsto δ atTop (nhdsWithin 0 (Ioi 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hδzero, ?_⟩
    filter_upwards with n
    exact hδpos n
  refine ⟨δ, hδpos, hδwithin, ?_⟩
  intro j n hj
  have hle : δ n ≤ δ j := by
    induction hj with
    | refl => exact le_rfl
    | @step n hj ih => exact (hδmono n).trans ih
  have hsmall := hδR j
  have hhalf : R j / 2 < R j := by linarith [hR j]
  exact lt_of_le_of_lt (hle.trans hsmall) hhalf

/-- A diagonal positive sequence makes the expected local-energy increments summable on each
fixed localizer, using only the two-parameter Cauchy hypothesis. -/
theorem exists_sequence_expected_localizer_increment_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℝ → Ω → Distr)
    (hC : ∀ a : ℝ, 0 < a → ∀ χ : TestFn, Tendsto
      (fun p : ℝ × ℝ =>
        ∫⁻ ω, localNegSobolevSq a (F p.1 ω - F p.2 ω) χ ∂P)
      (nhdsWithin 0 (Ioi 0) ×ˢ nhdsWithin 0 (Ioi 0)) (𝓝 0)) :
    ∃ δ : ℕ → ℝ, (∀ n, 0 < δ n) ∧
      Tendsto δ atTop (nhdsWithin 0 (Ioi 0)) ∧
      ∀ j k, k ≤ j →
        ∫⁻ ω, localNegSobolevSq 1 (F (δ j) ω - F (δ (j + 1)) ω) (localizer k) ∂P ≤
          ENNReal.ofReal ((1 / 2 : ℝ) ^ (4 * (j + 1))) := by
  let η (j : ℕ) : ℝ := (1 / 2 : ℝ) ^ (j + 1)
  have hη (j : ℕ) : 0 < η j := by positivity
  have hexists (j : ℕ) : ∃ r : ℝ, 0 < r ∧ ∀ δ δ' : ℝ, 0 < δ → δ < r → 0 < δ' → δ' < r →
      ∀ k ∈ Finset.range (j + 1),
        ∫⁻ ω, localNegSobolevSq 1 (F δ ω - F δ' ω) (localizer k) ∂P <
          ENNReal.ofReal ((1 / 2 : ℝ) ^ (4 * (j + 1))) :=
    exists_pos_radius_expected_localizer_energies_lt P F 1 (Finset.range (j + 1))
      (fun k hk => hC 1 (by norm_num) (localizer k))
      (ε := ENNReal.ofReal ((1 / 2 : ℝ) ^ (4 * (j + 1))))
      (ENNReal.ofReal_pos.mpr (by positivity))
  let R (j : ℕ) : ℝ := Classical.choose (hexists j)
  have hR (j : ℕ) : 0 < R j := (Classical.choose_spec (hexists j)).1
  have hsmall (j : ℕ) : ∀ δ δ' : ℝ, 0 < δ → δ < R j → 0 < δ' → δ' < R j →
      ∀ k ∈ Finset.range (j + 1),
        ∫⁻ ω, localNegSobolevSq 1 (F δ ω - F δ' ω) (localizer k) ∂P <
          ENNReal.ofReal ((1 / 2 : ℝ) ^ (4 * (j + 1))) := (Classical.choose_spec (hexists j)).2
  obtain ⟨δ, hδpos, hδtend, hδsmall⟩ := exists_pos_sequence_tendsto_zero_below_prefix hR
  refine ⟨δ, hδpos, hδtend, ?_⟩
  intro j k hkj
  have hk : k ∈ Finset.range (j + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hkj)
  have hbound := hsmall j (δ j) (δ (j + 1)) (hδpos j) (hδsmall j j le_rfl)
    (hδpos (j + 1)) (hδsmall j (j + 1) (Nat.le_succ j)) k hk
  exact le_of_lt hbound

/-- On a probability space, the expected square root of a nonnegative random variable is bounded
by the square root of its expectation. -/
theorem lintegral_rpow_half_le_rpow_lintegral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : Ω → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ ω, f ω ^ (1 / 2 : ℝ) ∂P ≤ (∫⁻ ω, f ω ∂P) ^ (1 / 2 : ℝ) := by
  have hroot : Measurable (fun ω => f ω ^ (1 / 2 : ℝ)) :=
    ENNReal.continuous_rpow_const.measurable.comp hf
  have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq P Real.HolderConjugate.two_two
    (measurable_const : Measurable (fun _ : Ω => (1 : ℝ≥0∞))).aemeasurable
    hroot.aemeasurable
  have hsq (ω : Ω) : (f ω ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = f ω := by
    rw [← ENNReal.rpow_mul]
    norm_num
  calc
    ∫⁻ ω, f ω ^ (1 / 2 : ℝ) ∂P =
        ∫⁻ ω, ((1 : ℝ≥0∞) * f ω ^ (1 / 2 : ℝ)) ∂P := by simp
    _ ≤ (∫⁻ ω, (1 : ℝ≥0∞) ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) *
        (∫⁻ ω, (f ω ^ (1 / 2 : ℝ)) ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) := hCS
    _ = (∫⁻ ω, f ω ∂P) ^ (1 / 2 : ℝ) := by
      simp_rw [hsq]
      simp [IsProbabilityMeasure.measure_univ]

/-- Summable expected local-energy increments imply almost-sure summability of their local
Sobolev norms on each tail of the localizer exhaustion. -/
theorem ae_tsum_localizer_rpow_half_increment_lt_top
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → Ω → Distr) (hF : ∀ n φ, Measurable (fun ω => F n ω φ))
    (hbound : ∀ j k, k ≤ j →
      ∫⁻ ω, localNegSobolevSq 1 (F j ω - F (j + 1) ω) (localizer k) ∂P ≤
        ENNReal.ofReal ((1 / 2 : ℝ) ^ (4 * (j + 1))) )
    (k : ℕ) :
    ∀ᵐ ω ∂P, (∑' j,
      localNegSobolevSq 1 (F (j + k) ω - F (j + k + 1) ω) (localizer k) ^
        (1 / 2 : ℝ)) < ⊤ := by
  let E (j : ℕ) (ω : Ω) :=
    localNegSobolevSq 1 (F (j + k) ω - F (j + k + 1) ω) (localizer k)
  let f (j : ℕ) (ω : Ω) := E j ω ^ (1 / 2 : ℝ)
  have hEmeas (j : ℕ) : Measurable (E j) := by
    dsimp [E]
    apply measurable_localNegSobolevSq
    intro φ
    exact (hF (j + k) φ).sub (hF (j + k + 1) φ)
  have hfmeas (j : ℕ) : Measurable (f j) := by
    simpa [f, Function.comp_def] using
      (ENNReal.continuous_rpow_const.measurable.comp (hEmeas j))
  let η (j : ℕ) : ℝ := (1 / 2 : ℝ) ^ (j + 1)
  have hηpos (j : ℕ) : 0 < η j := by positivity
  have hηle (j : ℕ) : η j ≤ 1 := by
    dsimp [η]
    calc
      (1 / 2 : ℝ) ^ (j + 1) ≤ (1 : ℝ) ^ (j + 1) := by gcongr; norm_num
      _ = 1 := one_pow _
  have hηsq (j : ℕ) : η j ^ 2 ≤ η j := by
    have hmul := mul_nonpos_of_nonneg_of_nonpos (le_of_lt (hηpos j))
      (sub_nonpos.mpr (hηle j))
    nlinarith [hmul]
  have hsumη : Summable η := by
    change Summable (fun n : ℕ => ((1 : ℝ) / 2) ^ (n + 1))
    rw [summable_nat_add_iff 1]
    exact summable_geometric_two
  have hrootBound (j : ℕ) : ∫⁻ ω, f j ω ∂P ≤ ENNReal.ofReal (η (j + k)) := by
    have hroot := lintegral_rpow_half_le_rpow_lintegral P (E j) (hEmeas j)
    have hpow : η (j + k) ^ 4 = (1 / 2 : ℝ) ^ (4 * (j + k + 1)) := by
      simp [η, pow_mul, Nat.mul_comm, Nat.add_assoc]
    have henergy : ∫⁻ ω, E j ω ∂P ≤ ENNReal.ofReal (η (j + k) ^ 4) := by
      have hb := hbound (j + k) k (Nat.le_add_left k j)
      simpa [E, hpow, Nat.add_assoc] using hb
    have hsqrt : (ENNReal.ofReal (η (j + k) ^ 4)) ^ (1 / 2 : ℝ) =
        ENNReal.ofReal (η (j + k) ^ 2) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
      congr 1
      rw [← Real.sqrt_eq_rpow]
      rw [show η (j + k) ^ 4 = (η (j + k) ^ 2) ^ 2 by ring]
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc
      _ = ∫⁻ ω, E j ω ^ (1 / 2 : ℝ) ∂P := by simp [f, E]
      _ ≤ (∫⁻ ω, E j ω ∂P) ^ (1 / 2 : ℝ) := hroot
      _ ≤ (ENNReal.ofReal (η (j + k) ^ 4)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow henergy (by norm_num)
      _ = ENNReal.ofReal (η (j + k) ^ 2) := hsqrt
      _ ≤ ENNReal.ofReal (η (j + k)) := ENNReal.ofReal_le_ofReal (hηsq (j + k))
  have hsumηtail : Summable (fun j => η (j + k)) := by
    rw [summable_nat_add_iff k]
    exact hsumη
  have hsum : ∫⁻ ω, ∑' j, f j ω ∂P ≤ ∑' j, ENNReal.ofReal (η (j + k)) := by
    rw [lintegral_tsum (fun j => (hfmeas j).aemeasurable)]
    exact ENNReal.tsum_le_tsum hrootBound
  have hsumη' : ∑' j, ENNReal.ofReal (η (j + k)) = ENNReal.ofReal (∑' j, η (j + k)) :=
    (ENNReal.ofReal_tsum_of_nonneg (fun j => (hηpos (j + k)).le) hsumηtail).symm
  have hsumFinite : (∑' j, ENNReal.ofReal (η (j + k))) ≠ ⊤ := by
    rw [hsumη']
    exact ENNReal.ofReal_ne_top
  have hlinfinite : ∫⁻ ω, ∑' j, f j ω ∂P < ⊤ :=
    lt_of_le_of_lt hsum (lt_top_iff_ne_top.mpr hsumFinite)
  have hmeasTsum : Measurable (fun ω => ∑' j, f j ω) := Measurable.tsum hfmeas
  exact ae_lt_top' hmeasTsum.aemeasurable (lt_top_iff_ne_top.mp hlinfinite)


/-- Convergence of every test pairing gives pointwise convergence of the localized Fourier
transform, the input needed for Fatou on the Fourier side. -/
theorem tendsto_localizedFourier_of_pairings {T : ℕ → Distr} {Tlim : Distr}
    (hpair : ∀ φ : TestFn, Tendsto (fun n => T n φ) atTop (𝓝 (Tlim φ)))
    (χ : TestFn) (ξ : Plane) :
    Tendsto (fun n => localizedFourier (T n) χ ξ) atTop
      (𝓝 (localizedFourier Tlim χ ξ)) := by
  have hcos : Tendsto (fun n => ((T n (χ.mulCos ξ) : ℝ) : ℂ)) atTop
      (𝓝 ((Tlim (χ.mulCos ξ) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp (hpair (χ.mulCos ξ))
  have hsin : Tendsto (fun n => ((T n (χ.mulSin ξ) : ℝ) : ℂ)) atTop
      (𝓝 ((Tlim (χ.mulSin ξ) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp (hpair (χ.mulSin ξ))
  have hmul : Tendsto
      (fun n => Complex.I * ((T n (χ.mulSin ξ) : ℝ) : ℂ)) atTop
      (𝓝 (Complex.I * ((Tlim (χ.mulSin ξ) : ℝ) : ℂ))) := tendsto_const_nhds.mul hsin
  simpa only [localizedFourier] using hcos.sub hmul

/-- The local Sobolev square is lower semicontinuous under convergence of all test
pairings. This is Fatou's lemma applied to the weighted localized Fourier integral. -/
theorem localNegSobolevSq_le_liminf_of_pairings {T : ℕ → Distr} {Tlim : Distr}
    (hpair : ∀ φ : TestFn, Tendsto (fun n => T n φ) atTop (𝓝 (Tlim φ)))
    (a : ℝ) (χ : TestFn) :
    localNegSobolevSq a Tlim χ ≤
      Filter.liminf (fun n => localNegSobolevSq a (T n) χ) atTop := by
  let c : ℝ := (2 * Real.pi)⁻¹ ^ 2
  let f : ℕ → Plane → ℝ≥0∞ := fun n ξ => ENNReal.ofReal
    (c * ((1 + ‖ξ‖ ^ 2) ^ (-a) * ‖localizedFourier (T n) χ ξ‖ ^ 2))
  let fLim : Plane → ℝ≥0∞ := fun ξ => ENNReal.ofReal
    (c * ((1 + ‖ξ‖ ^ 2) ^ (-a) * ‖localizedFourier Tlim χ ξ‖ ^ 2))
  have hweight : Measurable (fun ξ : Plane => (1 + ‖ξ‖ ^ 2) ^ (-a)) := by
    apply ((continuous_const.add (continuous_norm.pow 2)).rpow_const ?_).measurable
    intro ξ
    have hpos : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by positivity
    exact Or.inl hpos.ne'
  have hmeas (n : ℕ) : Measurable (f n) := by
    dsimp [f]
    exact ((measurable_const.mul (hweight.mul
      (((continuous_localizedFourier (T n) χ).norm.pow 2).measurable))).ennreal_ofReal)
  have hfourier (ξ : Plane) := tendsto_localizedFourier_of_pairings hpair χ ξ
  have hpoint (ξ : Plane) :
      Tendsto (fun n => f n ξ) atTop (𝓝 (fLim ξ)) := by
    have hnorm : Tendsto (fun n => ‖localizedFourier (T n) χ ξ‖ ^ 2) atTop
        (𝓝 (‖localizedFourier Tlim χ ξ‖ ^ 2)) := (hfourier ξ).norm.pow 2
    have hmul : Tendsto
        (fun n => c * ((1 + ‖ξ‖ ^ 2) ^ (-a) * ‖localizedFourier (T n) χ ξ‖ ^ 2))
        atTop (𝓝 (c * ((1 + ‖ξ‖ ^ 2) ^ (-a) * ‖localizedFourier Tlim χ ξ‖ ^ 2))) :=
      tendsto_const_nhds.mul (tendsto_const_nhds.mul hnorm)
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hmul
  have hliminf (ξ : Plane) : Filter.liminf (fun n => f n ξ) atTop = fLim ξ :=
    (hpoint ξ).liminf_eq
  have henergy (S : Distr) : localNegSobolevSq a S χ = ∫⁻ ξ : Plane,
      ENNReal.ofReal (c * ((1 + ‖ξ‖ ^ 2) ^ (-a) * ‖localizedFourier S χ ξ‖ ^ 2)) := by
    rw [localNegSobolevSq, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro ξ
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ c), norm_localizedFourier_sq]
  have hFatou := lintegral_liminf_le (μ := volume) (f := f) (u := atTop) hmeas
  rw [show (fun ξ => Filter.liminf (fun n => f n ξ) atTop) = fLim from funext hliminf]
    at hFatou
  rw [← henergy Tlim] at hFatou
  have hIntEq : (fun n => ∫⁻ ξ : Plane, f n ξ) =
      fun n => localNegSobolevSq a (T n) χ := by
    funext n
    exact (henergy (T n)).symm
  rw [hIntEq] at hFatou
  exact hFatou

/-- Fatou's lemma transfers almost-sure convergence of all test pairings to an expected local
Sobolev lower bound. -/
theorem lintegral_localNegSobolevSq_le_liminf_of_ae_pairings
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℕ → Ω → Distr) (Tlim : Ω → Distr)
    (hT : ∀ n φ, Measurable (fun ω => T n ω φ))
    (hTlim : ∀ φ, Measurable (fun ω => Tlim ω φ))
    (hpair : ∀ᵐ ω ∂P, ∀ φ : TestFn,
      Tendsto (fun n => T n ω φ) atTop (𝓝 (Tlim ω φ)))
    (a : ℝ) (χ : TestFn) :
    ∫⁻ ω, localNegSobolevSq a (Tlim ω) χ ∂P ≤
      Filter.liminf (fun n => ∫⁻ ω, localNegSobolevSq a (T n ω) χ ∂P) atTop := by
  have hmeas (n : ℕ) : Measurable (fun ω => localNegSobolevSq a (T n ω) χ) :=
    measurable_localNegSobolevSq (hT n) a χ
  have hlimmeas : Measurable (fun ω => localNegSobolevSq a (Tlim ω) χ) :=
    measurable_localNegSobolevSq hTlim a χ
  have hFatou := lintegral_liminf_le (μ := P)
    (f := fun n ω => localNegSobolevSq a (T n ω) χ) (u := atTop) hmeas
  have hpoint : ∀ᵐ ω ∂P,
      localNegSobolevSq a (Tlim ω) χ ≤
        Filter.liminf (fun n => localNegSobolevSq a (T n ω) χ) atTop := by
    filter_upwards [hpair] with ω hω
    exact localNegSobolevSq_le_liminf_of_pairings (fun φ => hω φ) a χ
  calc
    ∫⁻ ω, localNegSobolevSq a (Tlim ω) χ ∂P ≤
        ∫⁻ ω, Filter.liminf (fun n => localNegSobolevSq a (T n ω) χ) atTop ∂P :=
      lintegral_mono_ae hpoint
    _ ≤ Filter.liminf (fun n => ∫⁻ ω, localNegSobolevSq a (T n ω) χ ∂P) atTop := hFatou

end Critical2DKPZ.LocalSobolev

end
