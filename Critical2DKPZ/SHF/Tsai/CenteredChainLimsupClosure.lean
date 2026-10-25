/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.CenteredBlockFourthForms
public import Critical2DKPZ.SHF.Tsai.CenteredTwoBlockFourthLimits
public import Critical2DKPZ.SHF.Tsai.CenteredThreeBlockFourthLimits
public import Critical2DKPZ.SHF.Tsai.WeightedCompactTensors
public import Critical2DKPZ.SHF.Tsai.CompactMomentTests
public import Critical2DKPZ.SHF.Tsai.ConjugatedCompactTensors

/-! # Uniform centered fourth-moment bounds for short chains

The four-particle centered-kernel estimate controls centered fourth moments for single
blocks, endpoint replacements in two-block chains, and middle replacements in three-block
chains, uniformly over the remaining durations.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology CompactlySupported
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

private theorem iterated_integral_eq_prod_integral {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    (f : X × Y → ℝ) (hI : Integrable f (μ.prod ν)) :
    (∫ x, ∫ y, f (x, y) ∂ν ∂μ) = ∫ z, f z ∂(μ.prod ν) :=
  (integral_prod f hI).symm


private noncomputable def weightedConfigurationLpNorm (p : ℝ≥0∞)
    (F : Configuration 4 → ℝ) : ℝ≥0∞ :=
  eLpNorm (fun x => F x * Real.exp (configL1Norm x)) p

private theorem weighted_pair_integral_abs_le_max
    {p : ℝ≥0∞} (α C t : ℝ) (ht : 0 < t)
    (K : Configuration 4 → Configuration 4 → ℝ) (F G : Configuration 4 → ℝ)
    (hbound : |∫ xy : Configuration 4 × Configuration 4,
        F xy.1 * K xy.1 xy.2 * G xy.2 ∂(volume.prod volume)| ≤
      C * t ^ α * (weightedConfigurationLpNorm p F).toReal *
        (weightedConfigurationLpNorm p G).toReal) :
    |∫ xy : Configuration 4 × Configuration 4,
        F xy.1 * K xy.1 xy.2 * G xy.2 ∂(volume.prod volume)| ≤
      max C 0 * t ^ α * (weightedConfigurationLpNorm p F).toReal *
        (weightedConfigurationLpNorm p G).toReal := by
  let A := t ^ α * (weightedConfigurationLpNorm p F).toReal *
    (weightedConfigurationLpNorm p G).toReal
  have hfactor : 0 ≤ A := by
    dsimp [A]
    have htPow : 0 ≤ t ^ α := Real.rpow_nonneg (le_of_lt ht) α
    have hFNorm : 0 ≤ (weightedConfigurationLpNorm p F).toReal :=
      ENNReal.toReal_nonneg
    have hGNorm : 0 ≤ (weightedConfigurationLpNorm p G).toReal :=
      ENNReal.toReal_nonneg
    exact mul_nonneg (mul_nonneg htPow hFNorm) hGNorm
  have hbound' : |∫ xy : Configuration 4 × Configuration 4,
      F xy.1 * K xy.1 xy.2 * G xy.2 ∂(volume.prod volume)| ≤ C * A := by
    simpa [A, mul_assoc] using hbound
  calc
    _ ≤ C * A := hbound'
    _ ≤ max C 0 * A := mul_le_mul_of_nonneg_right (le_max_left C 0) hfactor
    _ = max C 0 * t ^ α *
        (weightedConfigurationLpNorm p F).toReal *
          (weightedConfigurationLpNorm p G).toReal := by
      dsimp [A]
      ring

private theorem weighted_iterated_integral_abs_le_max
    {p : ℝ≥0∞} (α C : ℝ) {t : ℝ} (ht : 0 < t)
    (K : Configuration 4 → Configuration 4 → ℝ) (F G : Configuration 4 → ℝ)
    (hI : Integrable (fun xy : Configuration 4 × Configuration 4 =>
        F xy.1 * K xy.1 xy.2 * G xy.2) (volume.prod volume))
    (hbound : |∫ xy : Configuration 4 × Configuration 4,
        F xy.1 * K xy.1 xy.2 * G xy.2 ∂(volume.prod volume)| ≤
      C * t ^ α * (weightedConfigurationLpNorm p F).toReal *
        (weightedConfigurationLpNorm p G).toReal) :
    |∫ x, ∫ y, F x * K x y * G y| ≤
      max C 0 * t ^ α * (weightedConfigurationLpNorm p F).toReal *
        (weightedConfigurationLpNorm p G).toReal := by
  have hEq : (∫ x, ∫ y, F x * K x y * G y) =
      ∫ xy : Configuration 4 × Configuration 4,
        F xy.1 * K xy.1 xy.2 * G xy.2 ∂(volume.prod volume) :=
    iterated_integral_eq_prod_integral _ hI
  calc
    _ = |∫ xy : Configuration 4 × Configuration 4,
        F xy.1 * K xy.1 xy.2 * G xy.2 ∂(volume.prod volume)| := congrArg abs hEq
    _ ≤ max C 0 * t ^ α * (weightedConfigurationLpNorm p F).toReal *
        (weightedConfigurationLpNorm p G).toReal :=
      weighted_pair_integral_abs_le_max (p := p) α C t ht K F G hbound

private theorem abs_sum_centered_kernel_forms_le
    {m r : ℕ} {p : ℝ≥0∞} (θ t D : ℝ)
    (F G : Fin m → (Fin 4 → Fin r) → Configuration 4 → ℝ)
    (hterm : ∀ a q,
      |∫ x, ∫ y, F a q x * centeredMomentKernel 4 θ t x y * G a q y| ≤
        D * (weightedConfigurationLpNorm p (F a q)).toReal *
          (weightedConfigurationLpNorm p (G a q)).toReal) :
    |∑ a, ∑ q : Fin 4 → Fin r, ∫ x, ∫ y,
        F a q x * centeredMomentKernel 4 θ t x y * G a q y| ≤
      D * ∑ a, ∑ q : Fin 4 → Fin r,
        (weightedConfigurationLpNorm p (F a q)).toReal *
          (weightedConfigurationLpNorm p (G a q)).toReal := by
  classical
  let T (a : Fin m) (q : Fin 4 → Fin r) :=
    ∫ x, ∫ y, F a q x * centeredMomentKernel 4 θ t x y * G a q y
  let N (a : Fin m) (q : Fin 4 → Fin r) :=
    (weightedConfigurationLpNorm p (F a q)).toReal *
      (weightedConfigurationLpNorm p (G a q)).toReal
  have hterm' (a : Fin m) (q : Fin 4 → Fin r) : |T a q| ≤ D * N a q := by
    simpa [T, N, mul_assoc] using hterm a q
  calc
    |∑ a, ∑ q : Fin 4 → Fin r, T a q| ≤ ∑ a, |∑ q : Fin 4 → Fin r, T a q| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, ∑ q : Fin 4 → Fin r, |T a q| := by
      apply Finset.sum_le_sum
      intro a ha
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, ∑ q : Fin 4 → Fin r, D * N a q := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro q hq
      exact hterm' a q
    _ = D * ∑ a, ∑ q : Fin 4 → Fin r, N a q := by
      simp [Finset.mul_sum]
    _ = D * ∑ a, ∑ q : Fin 4 → Fin r,
        (weightedConfigurationLpNorm p (F a q)).toReal *
          (weightedConfigurationLpNorm p (G a q)).toReal := by
      rfl

private theorem memLp_weighted_rawTensor {m r : ℕ} (p : ℝ≥0∞)
    (g : Fin m → Fin r → C_c(Plane, ℝ)) (a : Fin m) (q : Fin 4 → Fin r) :
    MemLp (fun x : Configuration 4 =>
      (∏ i, g a (q i) (x i)) * Real.exp (configL1Norm x)) p := by
  have h := memLp_exp_weighted_configurationTensor (n := 4) (a := 1) p
    (fun i => g a (q i))
  simpa [mul_comm] using h

private theorem momentTensorTest_weighted_bound
    (θ : ℝ) {p : ℝ≥0∞} (a : ℝ) {t : ℝ} (ht : 0 < t) (g : Fin 4 → C_c(Plane, ℝ))
    (C : ℝ)
    (hC : eLpNorm (fun x : Configuration 4 => Real.exp (a * configL1Norm x) *
        ∫ y, (momentKernel 4 θ t x y).toReal * ∏ i, g i (y i)) p ≤ ENNReal.ofReal C) :
    MemLp (fun x : Configuration 4 =>
        momentTensorTest (by decide : 4 ≤ 4) θ ht g x * Real.exp (a * configL1Norm x)) p ∧
      (eLpNorm (fun x : Configuration 4 =>
        momentTensorTest (by decide : 4 ≤ 4) θ ht g x * Real.exp (a * configL1Norm x)) p).toReal ≤
          max C 0 := by
  have hnorm : eLpNorm (fun x : Configuration 4 =>
      momentTensorTest (by decide : 4 ≤ 4) θ ht g x * Real.exp (a * configL1Norm x)) p ≤
      ENNReal.ofReal (max C 0) := by
    rw [eLpNorm_momentTensorTest_mul_exp]
    exact hC.trans (ENNReal.ofReal_le_ofReal (le_max_left C 0))
  have hmem : MemLp (fun x : Configuration 4 =>
      momentTensorTest (by decide : 4 ≤ 4) θ ht g x * Real.exp (a * configL1Norm x)) p := by
    change eLpNorm (fun x : Configuration 4 =>
      momentTensorTest (by decide : 4 ≤ 4) θ ht g x * Real.exp (a * configL1Norm x))
        p (volume : Measure (Configuration 4)) < ⊤
    exact hnorm.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hmem, ?_⟩
  calc
    _ ≤ (ENNReal.ofReal (max C 0)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hnorm
    _ = max C 0 := ENNReal.toReal_ofReal (le_max_right C 0)

/-- For single blocks, endpoint replacements in two-block chains, and middle replacements in three-block chains, the centered-kernel bound gives a superlinear time-power bound on centered fourth moments. Integrability is supplied by `HasDeltaBoseMoments.integral_sum_centered_four_eq_form`, `tendsto_integral_sum_centeredTwoBlockPairings_four`, and `tendsto_integral_sum_centeredThreeBlockPairings_four`. -/
theorem limsup_integral_chain_centered_le_of_kernel_bounds
    (θ T : ℝ) {p : ℝ≥0∞} (hp : 6 < p) (hp' : p ≠ ⊤) {m r : ℕ}
    (g g' : Fin m → Fin r → C_c(Plane, ℝ))
    (hcentered : ∀ {p : ℝ≥0∞} (hp : 2 < p) (hp' : p ≠ ⊤) {a : ℝ}
      (ha : 0 < a) (T : ℝ), ∃ c : ℝ, ∀ t : ℝ, 0 < t → t ≤ T →
      ∀ F G : Configuration 4 → ℝ,
        MemLp (fun x => F x * Real.exp (a * configL1Norm x)) p →
        MemLp (fun y => G y * Real.exp (a * configL1Norm y)) p →
        Integrable (fun xy : Configuration 4 × Configuration 4 =>
          F xy.1 * centeredMomentKernel 4 θ t xy.1 xy.2 * G xy.2) ∧
        |∫ xy : Configuration 4 × Configuration 4,
            F xy.1 * centeredMomentKernel 4 θ t xy.1 xy.2 * G xy.2| ≤
          c * t ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) *
            (eLpNorm (fun x => F x * Real.exp (a * configL1Norm x)) p).toReal *
            (eLpNorm (fun y => G y * Real.exp (a * configL1Norm y)) p).toReal) :
    ∃ C : ℝ, ∀ (K j : ℕ),
      (K = 0 ∧ j = 0 ∨ K = 1 ∧ j ≤ 1 ∨ K = 2 ∧ j = 1) →
      ∀ τ : ℕ → ℝ, (∀ k ≤ K, 0 < τ k) →
      ∑ k ∈ Finset.range (K + 1), τ k ≤ T →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℕ → Ω → Measure (Plane × Plane)),
        (∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k)) →
        iIndepFun (fun k : Fin (K + 1) => B k) P →
        ∀ u : ℕ → ℕ → Plane → ℝ, (∀ k, IsL2ApplicableMollifier (u k)) →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ ℓ in atTop,
          ∫ ω, ∑ a, ((∑ b, ∫ q, g a b q.1 * g' a b q.2
              ∂chainProduct (fun k => B k ω) (fun k => u k ℓ) K) -
            ∑ b, ∫ q, g a b q.1 * g' a b q.2
              ∂chainProduct (Function.update (fun k => B k ω) j (heatBlock (τ j)))
                (fun k => u k ℓ) K) ^ 4 ∂P ≤
            C * τ j ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) + ε := by
  classical
  have hp2 : 2 < p := lt_trans (by norm_num : (2 : ℝ≥0∞) < 6) hp
  obtain ⟨cK, hK⟩ := hcentered hp2 hp' (a := 1) (by norm_num) T
  have hmoment : ∀ f : Fin 4 → C_c(Plane, ℝ), ∃ C : ℝ, ∀ τ : ℝ,
      0 < τ → τ ≤ T →
        eLpNorm (fun x : Configuration 4 => Real.exp (configL1Norm x) *
          ∫ y, (momentKernel 4 θ τ x y).toReal * ∏ i, f i (y i)) p ≤ ENNReal.ofReal C := by
    intro f
    simpa only [one_mul] using
      (exists_weighted_eLpNorm_momentKernel_apply_le θ T hp2 hp'
        (a := 1) (by norm_num) f)
  choose cL hL using fun a : Fin m => fun q : Fin 4 → Fin r =>
    hmoment (fun i => g a (q i))
  choose cR hR using fun a : Fin m => fun q : Fin 4 → Fin r =>
    hmoment (fun i => g' a (q i))
  let Lraw (a : Fin m) (q : Fin 4 → Fin r) : Configuration 4 → ℝ :=
    fun x => ∏ i, g a (q i) (x i)
  let Rraw (a : Fin m) (q : Fin 4 → Fin r) : Configuration 4 → ℝ :=
    fun y => ∏ i, g' a (q i) (y i)
  let NL (a : Fin m) (q : Fin 4 → Fin r) :=
    (weightedConfigurationLpNorm p (Lraw a q)).toReal
  let NR (a : Fin m) (q : Fin 4 → Fin r) :=
    (weightedConfigurationLpNorm p (Rraw a q)).toReal
  let ML (a : Fin m) (q : Fin 4 → Fin r) := max (cL a q) 0
  let MR (a : Fin m) (q : Fin 4 → Fin r) := max (cR a q) 0
  let S00 := ∑ a, ∑ q : Fin 4 → Fin r, NL a q * NR a q
  let S01 := ∑ a, ∑ q : Fin 4 → Fin r, NL a q * MR a q
  let S10 := ∑ a, ∑ q : Fin 4 → Fin r, ML a q * NR a q
  let S11 := ∑ a, ∑ q : Fin 4 → Fin r, ML a q * MR a q
  let Sall := S00 + S01 + S10 + S11
  let cKpos := max cK 0
  let C := cKpos * Sall
  have hNL (a : Fin m) (q : Fin 4 → Fin r) : 0 ≤ NL a q := ENNReal.toReal_nonneg
  have hNR (a : Fin m) (q : Fin 4 → Fin r) : 0 ≤ NR a q := ENNReal.toReal_nonneg
  have hML (a : Fin m) (q : Fin 4 → Fin r) : 0 ≤ ML a q := le_max_right _ _
  have hMR (a : Fin m) (q : Fin 4 → Fin r) : 0 ≤ MR a q := le_max_right _ _
  have hS00 : 0 ≤ S00 := by
    dsimp [S00]
    apply Finset.sum_nonneg
    intro a ha
    apply Finset.sum_nonneg
    intro q hq
    exact mul_nonneg (hNL a q) (hNR a q)
  have hS01 : 0 ≤ S01 := by
    dsimp [S01]
    apply Finset.sum_nonneg
    intro a ha
    apply Finset.sum_nonneg
    intro q hq
    exact mul_nonneg (hNL a q) (hMR a q)
  have hS10 : 0 ≤ S10 := by
    dsimp [S10]
    apply Finset.sum_nonneg
    intro a ha
    apply Finset.sum_nonneg
    intro q hq
    exact mul_nonneg (hML a q) (hNR a q)
  have hS11 : 0 ≤ S11 := by
    dsimp [S11]
    apply Finset.sum_nonneg
    intro a ha
    apply Finset.sum_nonneg
    intro q hq
    exact mul_nonneg (hML a q) (hMR a q)
  have hSall : 0 ≤ Sall := by dsimp [Sall]; linarith
  have hS00le : S00 ≤ Sall := by dsimp [Sall]; linarith
  have hS01le : S01 ≤ Sall := by dsimp [Sall]; linarith
  have hS10le : S10 ≤ Sall := by dsimp [Sall]; linarith
  have hS11le : S11 ≤ Sall := by dsimp [Sall]; linarith
  have hCnonneg : 0 ≤ C := by dsimp [C]; exact mul_nonneg (le_max_right _ _) hSall
  have hrawL (a : Fin m) (q : Fin 4 → Fin r) :
      MemLp (fun x => Lraw a q x * Real.exp (configL1Norm x)) p := by
    simpa [Lraw] using memLp_weighted_rawTensor p g a q
  have hrawR (a : Fin m) (q : Fin 4 → Fin r) :
      MemLp (fun y => Rraw a q y * Real.exp (configL1Norm y)) p := by
    simpa [Rraw] using memLp_weighted_rawTensor p g' a q
  have hleftMoment {t : ℝ} (ht : 0 < t) (htT : t ≤ T)
      (a : Fin m) (q : Fin 4 → Fin r) :
      MemLp (fun x => momentTensorTest (by decide : 4 ≤ 4) θ ht
          (fun i => g a (q i)) x * Real.exp (configL1Norm x)) p ∧
        ((weightedConfigurationLpNorm p (momentTensorTest (by decide : 4 ≤ 4) θ ht
          (fun i => g a (q i)))).toReal ≤ ML a q) := by
    have hb := hL a q t ht htT
    have hb' : eLpNorm (fun x : Configuration 4 =>
        Real.exp (1 * configL1Norm x) *
          ∫ y, (momentKernel 4 θ t x y).toReal * ∏ i, g a (q i) (y i)) p ≤
          ENNReal.ofReal (cL a q) := by
      simpa only [one_mul] using hb
    have hres := momentTensorTest_weighted_bound θ 1 ht (fun i => g a (q i)) (cL a q) hb'
    constructor
    · simpa only [one_mul] using hres.1
    · simpa only [one_mul, weightedConfigurationLpNorm, ML] using hres.2
  have hrightMoment {t : ℝ} (ht : 0 < t) (htT : t ≤ T)
      (a : Fin m) (q : Fin 4 → Fin r) :
      MemLp (fun x => momentTensorTest (by decide : 4 ≤ 4) θ ht
          (fun i => g' a (q i)) x * Real.exp (configL1Norm x)) p ∧
        ((weightedConfigurationLpNorm p (momentTensorTest (by decide : 4 ≤ 4) θ ht
          (fun i => g' a (q i)))).toReal ≤ MR a q) := by
    have hb := hR a q t ht htT
    have hb' : eLpNorm (fun x : Configuration 4 =>
        Real.exp (1 * configL1Norm x) *
          ∫ y, (momentKernel 4 θ t x y).toReal * ∏ i, g' a (q i) (y i)) p ≤
          ENNReal.ofReal (cR a q) := by
      simpa only [one_mul] using hb
    have hres := momentTensorTest_weighted_bound θ 1 ht (fun i => g' a (q i)) (cR a q) hb'
    constructor
    · simpa only [one_mul] using hres.1
    · simpa only [one_mul, weightedConfigurationLpNorm, MR] using hres.2
  have hiter {t : ℝ} (ht : 0 < t) (htT : t ≤ T)
      (F G : Configuration 4 → ℝ)
      (hF : MemLp (fun x => F x * Real.exp (configL1Norm x)) p)
      (hG : MemLp (fun y => G y * Real.exp (configL1Norm y)) p) :
      |∫ x, ∫ y, F x * centeredMomentKernel 4 θ t x y * G y| ≤
        cKpos * t ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) *
          (weightedConfigurationLpNorm p F).toReal *
          (weightedConfigurationLpNorm p G).toReal := by
    obtain ⟨hI, hb⟩ := hK t ht htT F G
      (by simpa only [one_mul] using hF) (by simpa only [one_mul] using hG)
    have hIprod : Integrable (fun xy : Configuration 4 × Configuration 4 =>
        F xy.1 * centeredMomentKernel 4 θ t xy.1 xy.2 * G xy.2) (volume.prod volume) := by
      simpa only [Measure.volume_eq_prod] using hI
    have hbprod : |∫ xy : Configuration 4 × Configuration 4,
        F xy.1 * centeredMomentKernel 4 θ t xy.1 xy.2 * G xy.2 ∂(volume.prod volume)| ≤
        cK * t ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) *
          (weightedConfigurationLpNorm p F).toReal *
          (weightedConfigurationLpNorm p G).toReal := by
      simpa only [Measure.volume_eq_prod, one_mul, weightedConfigurationLpNorm] using hb
    simpa [cKpos] using weighted_iterated_integral_abs_le_max
      (p := p) ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) cK ht
      (centeredMomentKernel 4 θ t) F G hIprod hbprod
  have htime {K : ℕ} (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k)
      (hsum : ∑ k ∈ Finset.range (K + 1), τ k ≤ T) {k : ℕ} (hk : k ≤ K) : τ k ≤ T := by
    have hmem : k ∈ Finset.range (K + 1) := Finset.mem_range.mpr (by omega)
    calc
      τ k ≤ ∑ i ∈ Finset.range (K + 1), τ i := by
        apply Finset.single_le_sum
        · intro i hi
          exact (hτ i (by have := Finset.mem_range.mp hi; omega)).le
        · exact hmem
      _ ≤ T := hsum
  have hscaled {S : ℝ} (hS : S ≤ Sall) (hS0 : 0 ≤ S) {t : ℝ} (ht : 0 < t) :
      cKpos * t ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) * S ≤
        C * t ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) := by
    have hcoef : 0 ≤ cKpos * t ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) :=
      mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (le_of_lt ht) _)
    calc
      cKpos * t ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) * S =
          (cKpos * t ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal))) * S := rfl
      _ ≤ (cKpos * t ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal))) * Sall :=
        mul_le_mul_of_nonneg_left hS hcoef
      _ = C * t ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) := by
        dsimp [C]
        ring
  have hbound00 {t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
      |centeredBlockFourthForm θ t g g'| ≤
        cKpos * t ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) * S00 := by
    have hsum := abs_sum_centered_kernel_forms_le (p := p) θ t
      (cKpos * t ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)))
      (fun a q => Lraw a q) (fun a q => Rraw a q)
      (by
        intro a q
        simpa [Lraw, NL, NR, mul_assoc] using
          hiter ht htT (Lraw a q) (Rraw a q) (hrawL a q) (hrawR a q))
    simpa [centeredBlockFourthForm, Lraw, Rraw, NL, NR, S00, mul_assoc] using hsum
  have hboundTwo (τ : ℕ → ℝ) (hτ : ∀ k ≤ 1, 0 < τ k)
      (hτT : ∀ k ≤ 1, τ k ≤ T) (j : Fin 2) :
      |centeredTwoBlockFourthLimit θ τ hτ j g g'| ≤
        cKpos * τ j ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) *
          (if (j : ℕ) = 0 then S01 else S10) := by
    have hjt : 0 < τ j := hτ j (by omega)
    have hsum := abs_sum_centered_kernel_forms_le (p := p) θ (τ j)
      (cKpos * τ j ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)))
      (fun a q => if (j : ℕ) = 0 then Lraw a q else
        momentTensorTest (by decide : 4 ≤ 4) θ (hτ 0 (by omega)) (fun i => g a (q i)))
      (fun a q => if (j : ℕ) = 0 then
          momentTensorTest (by decide : 4 ≤ 4) θ (hτ 1 (by omega)) (fun i => g' a (q i))
        else Rraw a q)
      (by
        intro a q
        fin_cases j
        · simpa [Lraw, hτ] using hiter (hτ 0 (by omega)) (hτT 0 (by omega))
            (Lraw a q)
            (momentTensorTest (by decide : 4 ≤ 4) θ (hτ 1 (by omega))
              (fun i => g' a (q i)))
            (hrawL a q) ((hrightMoment (hτ 1 (by omega)) (hτT 1 (by omega)) a q).1)
        · simpa [Rraw, hτ] using hiter (hτ 1 (by omega)) (hτT 1 (by omega))
            (momentTensorTest (by decide : 4 ≤ 4) θ (hτ 0 (by omega))
              (fun i => g a (q i)))
            (Rraw a q)
            ((hleftMoment (hτ 0 (by omega)) (hτT 0 (by omega)) a q).1) (hrawR a q))
    fin_cases j
    · have hsum' : |centeredTwoBlockFourthLimit θ τ hτ 0 g g'| ≤
          (cKpos * τ 0 ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal))) *
            ∑ a, ∑ q : Fin 4 → Fin r,
              (weightedConfigurationLpNorm p (Lraw a q)).toReal *
                (weightedConfigurationLpNorm p
                  (momentTensorTest (by decide : 4 ≤ 4) θ (hτ 1 (by omega))
                    (fun i => g' a (q i)))).toReal := by
        simpa [centeredTwoBlockFourthLimit, Lraw, Rraw] using hsum
      have hnormSum : ∑ a, ∑ q : Fin 4 → Fin r,
            (weightedConfigurationLpNorm p (Lraw a q)).toReal *
              (weightedConfigurationLpNorm p
                (momentTensorTest (by decide : 4 ≤ 4) θ (hτ 1 (by omega))
                  (fun i => g' a (q i)))).toReal ≤ S01 := by
        dsimp [S01]
        apply Finset.sum_le_sum
        intro a _
        apply Finset.sum_le_sum
        intro q _
        have hn := (hrightMoment (hτ 1 (by omega)) (hτT 1 (by omega)) a q).2
        simpa [NL, MR, Lraw, hτ] using
          mul_le_mul (le_of_eq rfl) hn ENNReal.toReal_nonneg (hNL a q)
      have hcoef : 0 ≤ cKpos * τ 0 ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) :=
        mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (le_of_lt (hτ 0 (by omega))) _)
      calc
        |centeredTwoBlockFourthLimit θ τ hτ 0 g g'| ≤
            (cKpos * τ 0 ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal))) *
              ∑ a, ∑ q : Fin 4 → Fin r,
                (weightedConfigurationLpNorm p (Lraw a q)).toReal *
                  (weightedConfigurationLpNorm p
                    (momentTensorTest (by decide : 4 ≤ 4) θ (hτ 1 (by omega))
                      (fun i => g' a (q i)))).toReal := hsum'
        _ ≤ (cKpos * τ 0 ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal))) * S01 :=
          mul_le_mul_of_nonneg_left hnormSum hcoef
        _ = cKpos * τ 0 ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) * S01 := rfl
    · have hsum' : |centeredTwoBlockFourthLimit θ τ hτ 1 g g'| ≤
          (cKpos * τ 1 ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal))) *
            ∑ a, ∑ q : Fin 4 → Fin r,
              (weightedConfigurationLpNorm p
                (momentTensorTest (by decide : 4 ≤ 4) θ (hτ 0 (by omega))
                  (fun i => g a (q i)))).toReal *
                (weightedConfigurationLpNorm p (Rraw a q)).toReal := by
        simpa [centeredTwoBlockFourthLimit, Lraw, Rraw] using hsum
      have hnormSum : ∑ a, ∑ q : Fin 4 → Fin r,
            (weightedConfigurationLpNorm p
              (momentTensorTest (by decide : 4 ≤ 4) θ (hτ 0 (by omega))
                (fun i => g a (q i)))).toReal *
              (weightedConfigurationLpNorm p (Rraw a q)).toReal ≤ S10 := by
        dsimp [S10]
        apply Finset.sum_le_sum
        intro a _
        apply Finset.sum_le_sum
        intro q _
        have hn := (hleftMoment (hτ 0 (by omega)) (hτT 0 (by omega)) a q).2
        simpa [ML, NR, Rraw, hτ] using
          mul_le_mul hn (le_of_eq rfl) ENNReal.toReal_nonneg (hML a q)
      have hcoef : 0 ≤ cKpos * τ 1 ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) :=
        mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (le_of_lt (hτ 1 (by omega))) _)
      calc
        |centeredTwoBlockFourthLimit θ τ hτ 1 g g'| ≤
            (cKpos * τ 1 ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal))) *
              ∑ a, ∑ q : Fin 4 → Fin r,
                (weightedConfigurationLpNorm p
                  (momentTensorTest (by decide : 4 ≤ 4) θ (hτ 0 (by omega))
                    (fun i => g a (q i)))).toReal *
                  (weightedConfigurationLpNorm p (Rraw a q)).toReal := hsum'
        _ ≤ (cKpos * τ 1 ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal))) * S10 :=
          mul_le_mul_of_nonneg_left hnormSum hcoef
        _ = cKpos * τ 1 ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) * S10 := rfl
  have hboundThree (τ : ℕ → ℝ) (hτ : ∀ k ≤ 2, 0 < τ k)
      (hτT : ∀ k ≤ 2, τ k ≤ T) :
      |centeredThreeBlockFourthLimit θ τ hτ g g'| ≤
        cKpos * τ 1 ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) * S11 := by
    have hsum := abs_sum_centered_kernel_forms_le (p := p) θ (τ 1)
      (cKpos * τ 1 ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)))
      (fun a q => momentTensorTest (by decide : 4 ≤ 4) θ (hτ 0 (by omega))
        (fun i => g a (q i)))
      (fun a q => momentTensorTest (by decide : 4 ≤ 4) θ (hτ 2 (by omega))
        (fun i => g' a (q i)))
      (by
        intro a q
        simpa [hτ] using hiter (hτ 1 (by omega)) (hτT 1 (by omega))
          (momentTensorTest (by decide : 4 ≤ 4) θ (hτ 0 (by omega))
            (fun i => g a (q i)))
          (momentTensorTest (by decide : 4 ≤ 4) θ (hτ 2 (by omega))
            (fun i => g' a (q i)))
          ((hleftMoment (hτ 0 (by omega)) (hτT 0 (by omega)) a q).1)
          ((hrightMoment (hτ 2 (by omega)) (hτT 2 (by omega)) a q).1))
    have hsum' : |centeredThreeBlockFourthLimit θ τ hτ g g'| ≤
        (cKpos * τ 1 ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal))) *
          ∑ a, ∑ q : Fin 4 → Fin r,
            (weightedConfigurationLpNorm p
              (momentTensorTest (by decide : 4 ≤ 4) θ (hτ 0 (by omega))
                (fun i => g a (q i)))).toReal *
              (weightedConfigurationLpNorm p
                (momentTensorTest (by decide : 4 ≤ 4) θ (hτ 2 (by omega))
                  (fun i => g' a (q i)))).toReal := by
      simpa [centeredThreeBlockFourthLimit] using hsum
    have hnormSum : ∑ a, ∑ q : Fin 4 → Fin r,
          (weightedConfigurationLpNorm p
            (momentTensorTest (by decide : 4 ≤ 4) θ (hτ 0 (by omega))
              (fun i => g a (q i)))).toReal *
            (weightedConfigurationLpNorm p
              (momentTensorTest (by decide : 4 ≤ 4) θ (hτ 2 (by omega))
                (fun i => g' a (q i)))).toReal ≤ S11 := by
      dsimp [S11]
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro q _
      have hnL := (hleftMoment (hτ 0 (by omega)) (hτT 0 (by omega)) a q).2
      have hnR := (hrightMoment (hτ 2 (by omega)) (hτT 2 (by omega)) a q).2
      simpa [ML, MR, hτ] using
        mul_le_mul hnL hnR ENNReal.toReal_nonneg (hML a q)
    have hcoef : 0 ≤ cKpos * τ 1 ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) :=
      mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (le_of_lt (hτ 1 (by omega))) _)
    calc
      |centeredThreeBlockFourthLimit θ τ hτ g g'| ≤
          (cKpos * τ 1 ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal))) *
            ∑ a, ∑ q : Fin 4 → Fin r,
              (weightedConfigurationLpNorm p
                (momentTensorTest (by decide : 4 ≤ 4) θ (hτ 0 (by omega))
                  (fun i => g a (q i)))).toReal *
                (weightedConfigurationLpNorm p
                  (momentTensorTest (by decide : 4 ≤ 4) θ (hτ 2 (by omega))
                    (fun i => g' a (q i)))).toReal := hsum'
      _ ≤ (cKpos * τ 1 ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal))) * S11 :=
        mul_le_mul_of_nonneg_left hnormSum hcoef
      _ = cKpos * τ 1 ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) * S11 := rfl
  refine ⟨C, ?_⟩
  intro K j hKj τ hτ hsumτ Ω _ P _ B hB hind u hu ε hε
  have htimeK {k : ℕ} (hk : k ≤ K) : τ k ≤ T := htime τ hτ hsumτ hk
  rcases hKj with hzero | hone | htwo
  · rcases hzero with ⟨rfl, rfl⟩
    have hform := (hB 0 (by omega)).integral_sum_centered_four_eq_form
      (hτ 0 (by omega)) g g'
    have hlim (ℓ : ℕ) :
        ∫ ω, ∑ a, ((∑ b, ∫ q, g a b q.1 * g' a b q.2
            ∂chainProduct (fun k => B k ω) (fun k => u k ℓ) 0) -
          ∑ b, ∫ q, g a b q.1 * g' a b q.2
            ∂chainProduct (Function.update (fun k => B k ω) 0 (heatBlock (τ 0)))
              (fun k => u k ℓ) 0) ^ 4 ∂P = centeredBlockFourthForm θ (τ 0) g g' := by
      simpa [chainProduct] using hform.2.2
    have hupper : centeredBlockFourthForm θ (τ 0) g g' ≤
        C * τ 0 ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) := by
      exact (le_trans (le_abs_self _) (le_trans (hbound00 (hτ 0 (by omega)) (htimeK (by omega)))
        (hscaled hS00le hS00 (hτ 0 (by omega)))))
    have hstrict : centeredBlockFourthForm θ (τ 0) g g' <
        C * τ 0 ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) + ε :=
      lt_of_le_of_lt hupper (lt_add_of_pos_right _ hε)
    filter_upwards [] with ℓ
    rw [hlim ℓ]
    exact le_of_lt hstrict
  · rcases hone with ⟨rfl, hj⟩
    have hj0 : j = 0 ∨ j = 1 := by omega
    rcases hj0 with hj0 | hj1
    · subst j
      let j₂ : Fin 2 := 0
      have hτT : ∀ k ≤ 1, τ k ≤ T := fun k hk => htimeK hk
      have hlim := tendsto_integral_sum_centeredTwoBlockPairings_four
        (θ := θ) τ (by intro k hk; exact hτ k (by omega)) B
        (by intro k hk; exact hB k (by omega)) hind j₂
        u hu g g'
      have hM0 := hlim.1
      have hbound : centeredTwoBlockFourthLimit θ τ
          (by intro k hk; exact hτ k (by omega)) j₂ g g' ≤
          C * τ 0 ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) := by
        have h0 := hboundTwo τ (by intro k hk; exact hτ k (by omega)) hτT j₂
        have hS := hscaled hS01le hS01 (hτ 0 (by omega))
        calc
          _ ≤ |centeredTwoBlockFourthLimit θ τ
              (by intro k hk; exact hτ k (by omega)) j₂ g g'| := le_abs_self _
          _ ≤ cKpos * τ 0 ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) * S01 := by
            simpa [j₂] using h0
          _ ≤ C * τ 0 ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) := hS
      have hstrict : centeredTwoBlockFourthLimit θ τ
          (by intro k hk; exact hτ k (by omega)) j₂ g g' <
          C * τ 0 ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) + ε :=
        lt_of_le_of_lt hbound (lt_add_of_pos_right _ hε)
      have hev := hlim.2.2.eventually_le_const hstrict
      filter_upwards [hev] with ℓ hℓ
      simpa [j₂, chainProduct] using hℓ
    · subst j
      let j₂ : Fin 2 := 1
      have hτT : ∀ k ≤ 1, τ k ≤ T := fun k hk => htimeK hk
      have hlim := tendsto_integral_sum_centeredTwoBlockPairings_four
        (θ := θ) τ (by intro k hk; exact hτ k (by omega)) B
        (by intro k hk; exact hB k (by omega)) hind j₂
        u hu g g'
      have hM0 := hlim.1
      have hbound : centeredTwoBlockFourthLimit θ τ
          (by intro k hk; exact hτ k (by omega)) j₂ g g' ≤
          C * τ 1 ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) := by
        have h1 := hboundTwo τ (by intro k hk; exact hτ k (by omega)) hτT j₂
        have hS := hscaled hS10le hS10 (hτ 1 (by omega))
        calc
          _ ≤ |centeredTwoBlockFourthLimit θ τ
              (by intro k hk; exact hτ k (by omega)) j₂ g g'| := le_abs_self _
          _ ≤ cKpos * τ 1 ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) * S10 := by
            simpa [j₂] using h1
          _ ≤ C * τ 1 ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) := hS
      have hstrict : centeredTwoBlockFourthLimit θ τ
          (by intro k hk; exact hτ k (by omega)) j₂ g g' <
          C * τ 1 ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) + ε :=
        lt_of_le_of_lt hbound (lt_add_of_pos_right _ hε)
      have hev := hlim.2.2.eventually_le_const hstrict
      filter_upwards [hev] with ℓ hℓ
      simpa [j₂, chainProduct] using hℓ
  · rcases htwo with ⟨rfl, rfl⟩
    have hτT : ∀ k ≤ 2, τ k ≤ T := fun k hk => htimeK hk
    have hlim := tendsto_integral_sum_centeredThreeBlockPairings_four
      (θ := θ) τ (by intro k hk; exact hτ k (by omega)) B
      (by intro k hk; exact hB k (by omega)) hind u hu g g'
    have hM0 := hlim.1
    have hbound : centeredThreeBlockFourthLimit θ τ
        (by intro k hk; exact hτ k (by omega)) g g' ≤
        C * τ 1 ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) := by
      have h1 := hboundThree τ (by intro k hk; exact hτ k (by omega)) hτT
      have hS := hscaled hS11le hS11 (hτ 1 (by omega))
      calc
        _ ≤ |centeredThreeBlockFourthLimit θ τ
            (by intro k hk; exact hτ k (by omega)) g g'| := le_abs_self _
        _ ≤ cKpos * τ 1 ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) * S11 := h1
        _ ≤ C * τ 1 ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) := hS
    have hstrict : centeredThreeBlockFourthLimit θ τ
        (by intro k hk; exact hτ k (by omega)) g g' <
        C * τ 1 ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) + ε :=
      lt_of_le_of_lt hbound (lt_add_of_pos_right _ hε)
    have hev := hlim.2.2.eventually_le_const hstrict
    filter_upwards [hev] with ℓ hℓ
    simpa [chainProduct] using hℓ

end Critical2DKPZ.SHF.Tsai

end
