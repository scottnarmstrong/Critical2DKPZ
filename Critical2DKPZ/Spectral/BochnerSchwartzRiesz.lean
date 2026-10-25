/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Spectral.BochnerSchwartzSquareCone
public import Critical2DKPZ.Spectral.SmoothTestDensity
public import Critical2DKPZ.RandomMeasure.GeneralCompactness
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-! # The positive Fourier functional on smooth compact tests -/

@[expose] public section

noncomputable section

open MeasureTheory
open Filter
open Set
open TopologicalSpace
open scoped CompactlySupported FourierTransform Topology

namespace Critical2DKPZ.Spectral

/-- The real Fourier-side functional on smooth compact tests. -/
noncomputable def fourierTestLinearMap (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (∫ z in Metric.closedBall 0 R, |C z|) ≤ A * R ^ k) : TestFn →ₗ[ℝ] ℝ where
  toFun f := ((𝓕 (kernelTemperedDistribution C hC hgrowth))
    (testFnToSchwartzMap f)).re
  map_add' f g := by
    have hmap : testFnToSchwartzMap (f + g) =
        testFnToSchwartzMap f + testFnToSchwartzMap g := by
      ext x
      simp [testFnToSchwartzMap_apply]
    rw [hmap, map_add, Complex.add_re]
  map_smul' a f := by
    have hmap : testFnToSchwartzMap (a • f) =
        (a : ℂ) • testFnToSchwartzMap f := by
      ext x
      simp [testFnToSchwartzMap_apply]
    rw [hmap, map_smul]
    change ((a : ℂ) *
      (𝓕 (kernelTemperedDistribution C hC hgrowth)) (testFnToSchwartzMap f)).re =
        (RingHom.id ℝ) a •
          ((𝓕 (kernelTemperedDistribution C hC hgrowth)) (testFnToSchwartzMap f)).re
    simp [Complex.mul_re]

/-- Nonnegative tests have nonnegative value under the Fourier-side functional. -/
theorem fourierTestLinearMap_nonneg (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (∫ z in Metric.closedBall 0 R, |C z|) ≤ A * R ^ k)
    (heven : (fun z : Plane => C (-z)) =ᵐ[volume] C)
    (hpos : ∀ φ : TestFn, 0 ≤ ∫ p : Plane × Plane,
      φ p.1 * φ p.2 * C (p.1 - p.2))
    (f : TestFn) (hf : ∀ x : Plane, 0 ≤ f x) :
    0 ≤ fourierTestLinearMap C hC hgrowth f := by
  exact fourier_kernelTemperedDistribution_re_nonneg_testFn
    C hC hgrowth heven hpos f hf

/-- A positive test functional is bounded by a fixed cutoff value in the uniform norm. -/
theorem abs_fourierTestLinearMap_le_of_uniform_bound (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (∫ z in Metric.closedBall 0 R, |C z|) ≤ A * R ^ k)
    (heven : (fun z : Plane => C (-z)) =ᵐ[volume] C)
    (hpos : ∀ φ : TestFn, 0 ≤ ∫ p : Plane × Plane,
      φ p.1 * φ p.2 * C (p.1 - p.2))
    (η φ : TestFn) (hη : ∀ x ∈ tsupport φ, η x = 1)
    (hηnonneg : ∀ x : Plane, 0 ≤ η x) (ε : ℝ) (hε : 0 ≤ ε)
    (hφ : ∀ x : Plane, |φ x| ≤ ε) :
    |fourierTestLinearMap C hC hgrowth φ| ≤
      ε * fourierTestLinearMap C hC hgrowth η := by
  let Λ := fourierTestLinearMap C hC hgrowth
  have hηpos : 0 ≤ Λ η := fourierTestLinearMap_nonneg
    C hC hgrowth heven hpos η hηnonneg
  have hplus : ∀ x : Plane, 0 ≤ ((ε • η + φ) : TestFn) x := by
    intro x
    by_cases hx : x ∈ tsupport φ
    · have hηx : η x = 1 := hη x hx
      have hφx : -ε ≤ φ x ∧ φ x ≤ ε := abs_le.mp (hφ x)
      change 0 ≤ ε * η x + φ x
      rw [hηx]
      linarith
    · have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
      change 0 ≤ ε * η x + φ x
      rw [hφx]
      simpa only [add_zero] using mul_nonneg hε (hηnonneg x)
  have hminus : ∀ x : Plane, 0 ≤ ((ε • η - φ) : TestFn) x := by
    intro x
    by_cases hx : x ∈ tsupport φ
    · have hηx : η x = 1 := hη x hx
      have hφx : -ε ≤ φ x ∧ φ x ≤ ε := abs_le.mp (hφ x)
      change 0 ≤ ε * η x - φ x
      rw [hηx]
      linarith
    · have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
      change 0 ≤ ε * η x - φ x
      rw [hφx]
      simpa only [sub_zero] using mul_nonneg hε (hηnonneg x)
  have hpluspos := fourierTestLinearMap_nonneg C hC hgrowth heven hpos
    (ε • η + φ) hplus
  have hminuspos := fourierTestLinearMap_nonneg C hC hgrowth heven hpos
    (ε • η - φ) hminus
  have hplusEq : Λ (ε • η + φ) = ε * Λ η + Λ φ := by
    rw [map_add, map_smul]
    simp only [smul_eq_mul]
  have hminusEq : Λ (ε • η - φ) = ε * Λ η - Λ φ := by
    rw [map_sub, map_smul]
    simp only [smul_eq_mul]
  rw [hplusEq] at hpluspos
  rw [hminusEq] at hminuspos
  rw [abs_le]
  constructor <;> linarith

/-- Values of the positive Fourier functional along a fixed-support uniform approximation form a
Cauchy sequence. -/
theorem fourierTestApproxValues_isCauchy (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (∫ z in Metric.closedBall 0 R, |C z|) ≤ A * R ^ k)
    (heven : (fun z : Plane => C (-z)) =ᵐ[volume] C)
    (hpos : ∀ φ : TestFn, 0 ≤ ∫ p : Plane × Plane,
      φ p.1 * φ p.2 * C (p.1 - p.2))
    (f : C_c(Plane, ℝ)) :
    CauchySeq (fun n : ℕ =>
      fourierTestLinearMap C hC hgrowth (uniformTestApproxSequence f n)) := by
  let Λ := fourierTestLinearMap C hC hgrowth
  let k := Classical.choose (exists_localizer_uniform_testFn_approx f)
  let χ : TestFn := Critical2DKPZ.localizer k
  obtain ⟨m, hm⟩ := Critical2DKPZ.exists_localizer_eq_one_on_compact
    χ.hasCompactSupport.isCompact
  let η : TestFn := Critical2DKPZ.localizer m
  have hηnonneg : ∀ x : Plane, 0 ≤ η x :=
    fun x => Critical2DKPZ.localizer_nonneg m x
  have hηvalue : 0 ≤ Λ η := fourierTestLinearMap_nonneg
    C hC hgrowth heven hpos η hηnonneg
  let D : ℝ := Λ η + 1
  have hD : 0 < D := by dsimp [D]; linarith
  have hηone (a b : ℕ) : ∀ x ∈ tsupport
      (uniformTestApproxSequence f a - uniformTestApproxSequence f b), η x = 1 := by
    intro x hx
    have hxUnion : x ∈ tsupport (uniformTestApproxSequence f a) ∪
        tsupport (uniformTestApproxSequence f b) :=
      tsupport_sub _ _ hx
    have hsupport (j : ℕ) :
        tsupport (uniformTestApproxSequence f j) ⊆ tsupport χ := by
      simpa [χ, k] using uniformTestApproxSequence_support f j
    have hxχ : x ∈ tsupport χ := by
      rcases hxUnion with hxa | hxb
      · exact hsupport a hxa
      · exact hsupport b hxb
    exact hm m le_rfl x hxχ
  have hdiff (a b : ℕ) (x : Plane) :
      |(uniformTestApproxSequence f a - uniformTestApproxSequence f b) x| ≤
        1 / ((a : ℝ) + 1) + 1 / ((b : ℝ) + 1) := by
    calc
      |(uniformTestApproxSequence f a - uniformTestApproxSequence f b) x| =
          |(uniformTestApproxSequence f a x - f x) -
            (uniformTestApproxSequence f b x - f x)| := by
              congr 1
              simp only [sub_apply]
              ring
      _ ≤ |uniformTestApproxSequence f a x - f x| +
          |uniformTestApproxSequence f b x - f x| := abs_sub _ _
      _ ≤ 1 / ((a : ℝ) + 1) + 1 / ((b : ℝ) + 1) :=
        add_le_add (le_of_lt (uniformTestApproxSequence_error f a x))
          (le_of_lt (uniformTestApproxSequence_error f b x))
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  let δ : ℝ := ε / (4 * D)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * D / ε)
  refine ⟨N, fun a ha b hb => ?_⟩
  rw [Real.dist_eq]
  have hcastA : (N : ℝ) ≤ a := by exact_mod_cast ha
  have hcastB : (N : ℝ) ≤ b := by exact_mod_cast hb
  have hdenA : 4 * D / ε < (a : ℝ) + 1 := by
    have hNat : 4 * D / ε < (N : ℝ) := hN
    linarith
  have hdenB : 4 * D / ε < (b : ℝ) + 1 := by
    have hNat : 4 * D / ε < (N : ℝ) := hN
    linarith
  have herrA : 1 / ((a : ℝ) + 1) < δ := by
    calc
      1 / ((a : ℝ) + 1) < 1 / (4 * D / ε) :=
        one_div_lt_one_div_of_lt (by positivity) hdenA
      _ = δ := by dsimp [δ]; field_simp
  have herrB : 1 / ((b : ℝ) + 1) < δ := by
    calc
      1 / ((b : ℝ) + 1) < 1 / (4 * D / ε) :=
        one_div_lt_one_div_of_lt (by positivity) hdenB
      _ = δ := by dsimp [δ]; field_simp
  let φ := uniformTestApproxSequence f a - uniformTestApproxSequence f b
  have hηone' : ∀ x ∈ tsupport φ, η x = 1 := by
    simpa [φ] using hηone a b
  have hφbound : ∀ x : Plane, |φ x| ≤ 1 / ((a : ℝ) + 1) +
      1 / ((b : ℝ) + 1) := fun x => hdiff a b x
  have hlocal := abs_fourierTestLinearMap_le_of_uniform_bound
    C hC hgrowth heven hpos η φ hηone' hηnonneg
    (1 / ((a : ℝ) + 1) + 1 / ((b : ℝ) + 1)) (by positivity) hφbound
  have hvalue : Λ φ =
      Λ (uniformTestApproxSequence f a) - Λ (uniformTestApproxSequence f b) := by
    dsimp [φ, Λ]
    exact map_sub _ _ _
  have hsum : 1 / ((a : ℝ) + 1) + 1 / ((b : ℝ) + 1) < 2 * δ := by
    calc
      _ < δ + δ := add_lt_add herrA herrB
      _ = 2 * δ := by ring
  have hestimate :
      |Λ (uniformTestApproxSequence f a) - Λ (uniformTestApproxSequence f b)| <
        ε := by
    rw [← hvalue]
    calc
      |Λ φ| ≤
          (1 / ((a : ℝ) + 1) + 1 / ((b : ℝ) + 1)) * Λ η := by
            simpa [Λ, φ] using hlocal
      _ ≤ (1 / ((a : ℝ) + 1) + 1 / ((b : ℝ) + 1)) * D := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            dsimp [D]
            linarith
      _ < (2 * δ) * D :=
            mul_lt_mul_of_pos_right hsum hD
      _ = ε / 2 := by dsimp [δ]; field_simp; ring
      _ < ε := by linarith
  simpa only [Real.dist_eq] using hestimate

/-- The value assigned to a compactly supported continuous function by the uniformly continuous
extension of the positive Fourier functional. -/
noncomputable def fourierCccValue (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (∫ z in Metric.closedBall 0 R, |C z|) ≤ A * R ^ k)
    (f : C_c(Plane, ℝ)) : ℝ :=
  Filter.limUnder atTop (fun n : ℕ =>
    fourierTestLinearMap C hC hgrowth (uniformTestApproxSequence f n))

/-- The canonical test approximations converge to the chosen extension value. -/
theorem tendsto_fourierTestApproxValues (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (∫ z in Metric.closedBall 0 R, |C z|) ≤ A * R ^ k)
    (heven : (fun z : Plane => C (-z)) =ᵐ[volume] C)
    (hpos : ∀ φ : TestFn, 0 ≤ ∫ p : Plane × Plane,
      φ p.1 * φ p.2 * C (p.1 - p.2))
    (f : C_c(Plane, ℝ)) :
    Tendsto (fun n : ℕ =>
      fourierTestLinearMap C hC hgrowth (uniformTestApproxSequence f n)) atTop
      (𝓝 (fourierCccValue C hC hgrowth f)) :=
  (fourierTestApproxValues_isCauchy C hC hgrowth heven hpos f).tendsto_limUnder

/-- Any uniformly convergent smooth-test approximation with one compact support has the same
Fourier-functional limit as the canonical sequence. -/
theorem tendsto_fourierTestValue_of_uniform_approx (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (∫ z in Metric.closedBall 0 R, |C z|) ≤ A * R ^ k)
    (heven : (fun z : Plane => C (-z)) =ᵐ[volume] C)
    (hpos : ∀ φ : TestFn, 0 ≤ ∫ p : Plane × Plane,
      φ p.1 * φ p.2 * C (p.1 - p.2))
    (f : C_c(Plane, ℝ)) (ψ : ℕ → TestFn) (K : Set Plane) (hK : IsCompact K)
    (hψsupport : ∀ n, tsupport (ψ n) ⊆ K) (e : ℕ → ℝ)
    (he : Tendsto e atTop (𝓝 0)) (hψapprox : ∀ n x, |ψ n x - f x| ≤ e n) :
    Tendsto (fun n => fourierTestLinearMap C hC hgrowth (ψ n)) atTop
      (𝓝 (fourierCccValue C hC hgrowth f)) := by
  let Λ := fourierTestLinearMap C hC hgrowth
  let k := Classical.choose (exists_localizer_uniform_testFn_approx f)
  let χ : TestFn := Critical2DKPZ.localizer k
  let K' := K ∪ tsupport χ
  have hK' : IsCompact K' := hK.union χ.hasCompactSupport.isCompact
  obtain ⟨m, hm⟩ := Critical2DKPZ.exists_localizer_eq_one_on_compact hK'
  let η : TestFn := Critical2DKPZ.localizer m
  have hηnonneg : ∀ x : Plane, 0 ≤ η x :=
    fun x => Critical2DKPZ.localizer_nonneg m x
  have hηvalue : 0 ≤ Λ η := fourierTestLinearMap_nonneg
    C hC hgrowth heven hpos η hηnonneg
  have hcanonicalSupport (n : ℕ) :
      tsupport (uniformTestApproxSequence f n) ⊆ tsupport χ := by
    simpa [χ, k] using uniformTestApproxSequence_support f n
  have hηone (n : ℕ) : ∀ x ∈ tsupport (ψ n - uniformTestApproxSequence f n), η x = 1 := by
    intro x hx
    have hxUnion : x ∈ tsupport (ψ n) ∪
        tsupport (uniformTestApproxSequence f n) := tsupport_sub _ _ hx
    have hxK' : x ∈ K' := by
      rcases hxUnion with hxψ | hxφ
      · exact Set.mem_union_left _ (hψsupport n hxψ)
      · exact Set.mem_union_right _ (hcanonicalSupport n hxφ)
    exact hm m le_rfl x hxK'
  have herror (n : ℕ) (x : Plane) :
      |(ψ n - uniformTestApproxSequence f n) x| ≤ e n + 1 / ((n : ℝ) + 1) := by
    calc
      |(ψ n - uniformTestApproxSequence f n) x| =
          |(ψ n x - f x) - (uniformTestApproxSequence f n x - f x)| := by
            congr 1
            simp only [sub_apply]
            ring
      _ ≤ |ψ n x - f x| + |uniformTestApproxSequence f n x - f x| :=
        abs_sub _ _
      _ ≤ e n + 1 / ((n : ℝ) + 1) :=
        add_le_add (hψapprox n x) (le_of_lt (uniformTestApproxSequence_error f n x))
  have hvalueBound (n : ℕ) :
      dist (Λ (ψ n)) (Λ (uniformTestApproxSequence f n)) ≤
        (e n + 1 / ((n : ℝ) + 1)) * Λ η := by
    have hlocal := abs_fourierTestLinearMap_le_of_uniform_bound
      C hC hgrowth heven hpos η (ψ n - uniformTestApproxSequence f n)
      (hηone n) hηnonneg (e n + 1 / ((n : ℝ) + 1))
      (by
        have heNonneg : 0 ≤ e n :=
          (abs_nonneg _).trans (hψapprox n (0 : Plane))
        positivity)
      (herror n)
    rw [Real.dist_eq, ← map_sub Λ (ψ n) (uniformTestApproxSequence f n)]
    simpa [Λ] using hlocal
  have hecanonical : Tendsto
      (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hboundLimit : Tendsto
      (fun n : ℕ => (e n + 1 / ((n : ℝ) + 1)) * Λ η) atTop (𝓝 0) := by
    simpa using (he.add hecanonical).mul_const (Λ η)
  have hdist : Tendsto
      (fun n => dist (Λ (ψ n)) (Λ (uniformTestApproxSequence f n)))
      atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => dist_nonneg) hvalueBound hboundLimit
  have hdist' : Tendsto
      (fun n => dist (Λ (uniformTestApproxSequence f n)) (Λ (ψ n)))
      atTop (𝓝 0) := by
    simpa only [dist_comm] using hdist
  exact (tendsto_fourierTestApproxValues C hC hgrowth heven hpos f).congr_dist hdist'

/-- The compactly supported continuous extension is positive on nonnegative functions. -/
theorem fourierCccValue_nonneg (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (∫ z in Metric.closedBall 0 R, |C z|) ≤ A * R ^ k)
    (heven : (fun z : Plane => C (-z)) =ᵐ[volume] C)
    (hpos : ∀ φ : TestFn, 0 ≤ ∫ p : Plane × Plane,
      φ p.1 * φ p.2 * C (p.1 - p.2))
    (f : C_c(Plane, ℝ)) (hf : ∀ x : Plane, 0 ≤ f x) :
    0 ≤ fourierCccValue C hC hgrowth f := by
  let Λ := fourierTestLinearMap C hC hgrowth
  let k := Classical.choose (exists_localizer_uniform_testFn_approx f)
  let χ : TestFn := Critical2DKPZ.localizer k
  obtain ⟨m, hm⟩ := Critical2DKPZ.exists_localizer_eq_one_on_compact
    χ.hasCompactSupport.isCompact
  let η : TestFn := Critical2DKPZ.localizer m
  let K := tsupport χ ∪ tsupport η
  have hK : IsCompact K := χ.hasCompactSupport.isCompact.union η.hasCompactSupport.isCompact
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let ψ : ℕ → TestFn := fun n => uniformTestApproxSequence f n + ε n • η
  have hηnonneg : ∀ x : Plane, 0 ≤ η x :=
    fun x => Critical2DKPZ.localizer_nonneg m x
  have hsupport (n : ℕ) :
      tsupport (uniformTestApproxSequence f n) ⊆ tsupport χ := by
    simpa [χ, k] using uniformTestApproxSequence_support f n
  have hψsupport (n : ℕ) : tsupport (ψ n) ⊆ K := by
    dsimp [ψ, K]
    have hsmul : tsupport (ε n • η) ⊆ tsupport η :=
      tsupport_smul_subset_right (fun _ : Plane => ε n) η
    exact (tsupport_add _ _).trans
      (union_subset ((hsupport n).trans subset_union_left)
        (hsmul.trans subset_union_right))
  have hηone (n : ℕ) : ∀ x ∈ tsupport (uniformTestApproxSequence f n), η x = 1 := by
    intro x hx
    exact hm m le_rfl x (hsupport n hx)
  have hψnonneg (n : ℕ) : ∀ x : Plane, 0 ≤ ψ n x := by
    intro x
    by_cases hx : x ∈ tsupport (uniformTestApproxSequence f n)
    · have hηx := hηone n x hx
      have happrox := uniformTestApproxSequence_error f n x
      have hlower : -ε n ≤ uniformTestApproxSequence f n x := by
        have h := (abs_le.mp (le_of_lt happrox)).1
        dsimp [ε]
        linarith [hf x]
      change 0 ≤ uniformTestApproxSequence f n x + ε n * η x
      rw [hηx]
      linarith [hlower]
    · have hzero : uniformTestApproxSequence f n x = 0 :=
        image_eq_zero_of_notMem_tsupport hx
      change 0 ≤ uniformTestApproxSequence f n x + ε n * η x
      rw [hzero]
      have hεpos : 0 ≤ ε n := by dsimp [ε]; positivity
      simpa only [zero_add] using mul_nonneg hεpos (hηnonneg x)
  have hψapprox (n : ℕ) (x : Plane) :
      |ψ n x - f x| ≤ 2 * ε n := by
    have hηabs : |η x| ≤ 1 := by
      rw [abs_of_nonneg (hηnonneg x)]
      exact Critical2DKPZ.localizer_le_one m x
    calc
      |ψ n x - f x| =
          |(uniformTestApproxSequence f n x - f x) + ε n * η x| := by
            congr 1
            change uniformTestApproxSequence f n x + ε n * η x - f x =
              (uniformTestApproxSequence f n x - f x) + ε n * η x
            ring
      _ ≤ |uniformTestApproxSequence f n x - f x| + |ε n * η x| := abs_add_le _ _
      _ ≤ ε n + ε n := by
        apply add_le_add
        · exact (uniformTestApproxSequence_error f n x).le
        · calc
            |ε n * η x| = |ε n| * |η x| := abs_mul _ _
            _ ≤ ε n * 1 := by
              have hεpos : 0 ≤ ε n := by dsimp [ε]; positivity
              rw [abs_of_nonneg hεpos]
              exact mul_le_mul_of_nonneg_left hηabs hεpos
            _ = ε n := by ring
      _ = 2 * ε n := by ring
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have herrorlim : Tendsto (fun n => 2 * ε n) atTop (𝓝 0) := by
    simpa only [mul_zero] using hεlim.const_mul 2
  have hψlim := tendsto_fourierTestValue_of_uniform_approx
    C hC hgrowth heven hpos f ψ K hK hψsupport (fun n => 2 * ε n)
    herrorlim hψapprox
  have hvaluesNonneg : ∀ n, 0 ≤ Λ (ψ n) := by
    intro n
    exact fourierTestLinearMap_nonneg C hC hgrowth heven hpos (ψ n) (hψnonneg n)
  have hlimit : fourierCccValue C hC hgrowth f ∈ Set.Ici 0 :=
    isClosed_Ici.mem_of_tendsto hψlim (Eventually.of_forall hvaluesNonneg)
  exact hlimit

/-- The compactly supported continuous extension is additive. -/
theorem fourierCccValue_add (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (∫ z in Metric.closedBall 0 R, |C z|) ≤ A * R ^ k)
    (heven : (fun z : Plane => C (-z)) =ᵐ[volume] C)
    (hpos : ∀ φ : TestFn, 0 ≤ ∫ p : Plane × Plane,
      φ p.1 * φ p.2 * C (p.1 - p.2))
    (f g : C_c(Plane, ℝ)) :
    fourierCccValue C hC hgrowth (f + g) =
      fourierCccValue C hC hgrowth f + fourierCccValue C hC hgrowth g := by
  let Λ := fourierTestLinearMap C hC hgrowth
  let ψ : ℕ → TestFn := fun n =>
    uniformTestApproxSequence f n + uniformTestApproxSequence g n
  let Kf := tsupport (Critical2DKPZ.localizer
    (Classical.choose (exists_localizer_uniform_testFn_approx f)))
  let Kg := tsupport (Critical2DKPZ.localizer
    (Classical.choose (exists_localizer_uniform_testFn_approx g)))
  let K := Kf ∪ Kg
  have hK : IsCompact K := by
    dsimp [K, Kf, Kg]
    exact (Critical2DKPZ.localizer
      (Classical.choose (exists_localizer_uniform_testFn_approx f))).hasCompactSupport.isCompact.union
      (Critical2DKPZ.localizer
        (Classical.choose (exists_localizer_uniform_testFn_approx g))).hasCompactSupport.isCompact
  have hsuppf (n : ℕ) : tsupport (uniformTestApproxSequence f n) ⊆ Kf := by
    simpa [Kf] using uniformTestApproxSequence_support f n
  have hsuppg (n : ℕ) : tsupport (uniformTestApproxSequence g n) ⊆ Kg := by
    simpa [Kg] using uniformTestApproxSequence_support g n
  have hψsupport (n : ℕ) : tsupport (ψ n) ⊆ K := by
    dsimp [ψ, K]
    exact (tsupport_add _ _).trans
      (union_subset ((hsuppf n).trans subset_union_left)
        ((hsuppg n).trans subset_union_right))
  let e : ℕ → ℝ := fun n => 2 * (1 / ((n : ℝ) + 1))
  have he : Tendsto e atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => (2 : ℝ) * (1 / ((n : ℝ) + 1))) atTop (𝓝 0)
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (2 : ℝ)
  have happrox (n : ℕ) (x : Plane) : |ψ n x - (f + g) x| ≤ e n := by
    have hferr := uniformTestApproxSequence_error f n x
    have hgerr := uniformTestApproxSequence_error g n x
    calc
      |ψ n x - (f + g) x| =
          |(uniformTestApproxSequence f n x - f x) +
            (uniformTestApproxSequence g n x - g x)| := by
              congr 1
              change uniformTestApproxSequence f n x + uniformTestApproxSequence g n x -
                  (f x + g x) =
                (uniformTestApproxSequence f n x - f x) +
                  (uniformTestApproxSequence g n x - g x)
              ring
      _ ≤ |uniformTestApproxSequence f n x - f x| +
          |uniformTestApproxSequence g n x - g x| := abs_add_le _ _
      _ ≤ e n := by
        calc
          _ ≤ 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) :=
            add_le_add hferr.le hgerr.le
          _ = e n := by dsimp [e]; ring
  have hlimitSum := tendsto_fourierTestValue_of_uniform_approx
    C hC hgrowth heven hpos (f + g) ψ K hK hψsupport e he happrox
  have hlinearLimits :
      Tendsto (fun n => Λ (ψ n)) atTop
        (𝓝 (fourierCccValue C hC hgrowth f + fourierCccValue C hC hgrowth g)) := by
    have hsum : (fun n => Λ (ψ n)) =
        fun n => Λ (uniformTestApproxSequence f n) +
          Λ (uniformTestApproxSequence g n) := by
      funext n
      simp [ψ, Λ, map_add]
    rw [hsum]
    exact (tendsto_fourierTestApproxValues C hC hgrowth heven hpos f).add
      (tendsto_fourierTestApproxValues C hC hgrowth heven hpos g)
  exact tendsto_nhds_unique hlimitSum hlinearLimits

/-- The compactly supported continuous extension is homogeneous over the reals. -/
theorem fourierCccValue_smul (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (∫ z in Metric.closedBall 0 R, |C z|) ≤ A * R ^ k)
    (heven : (fun z : Plane => C (-z)) =ᵐ[volume] C)
    (hpos : ∀ φ : TestFn, 0 ≤ ∫ p : Plane × Plane,
      φ p.1 * φ p.2 * C (p.1 - p.2))
    (a : ℝ) (f : C_c(Plane, ℝ)) :
    fourierCccValue C hC hgrowth (a • f) =
      a * fourierCccValue C hC hgrowth f := by
  let Λ := fourierTestLinearMap C hC hgrowth
  let ψ : ℕ → TestFn := fun n => a • uniformTestApproxSequence f n
  let K := tsupport (Critical2DKPZ.localizer
    (Classical.choose (exists_localizer_uniform_testFn_approx f)))
  have hK : IsCompact K := by
    dsimp [K]
    exact (Critical2DKPZ.localizer
      (Classical.choose (exists_localizer_uniform_testFn_approx f))).hasCompactSupport.isCompact
  have hψsupport (n : ℕ) : tsupport (ψ n) ⊆ K := by
    dsimp [ψ, K]
    exact (tsupport_smul_subset_right (fun _ : Plane => a)
      (uniformTestApproxSequence f n)).trans
      (uniformTestApproxSequence_support f n)
  let e : ℕ → ℝ := fun n => |a| * (1 / ((n : ℝ) + 1))
  have he : Tendsto e atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => |a| * (1 / ((n : ℝ) + 1))) atTop (𝓝 0)
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul |a|
  have happrox (n : ℕ) (x : Plane) : |ψ n x - (a • f) x| ≤ e n := by
    calc
      |ψ n x - (a • f) x| =
          |a| * |uniformTestApproxSequence f n x - f x| := by
            change |a * uniformTestApproxSequence f n x - a * f x| = _
            rw [← mul_sub, abs_mul]
      _ ≤ e n := by
        dsimp [e]
        exact mul_le_mul_of_nonneg_left
          (uniformTestApproxSequence_error f n x).le (abs_nonneg a)
  have hlimitSmul := tendsto_fourierTestValue_of_uniform_approx
    C hC hgrowth heven hpos (a • f) ψ K hK hψsupport e he happrox
  have hlinearLimits :
      Tendsto (fun n => Λ (ψ n)) atTop
        (𝓝 (a * fourierCccValue C hC hgrowth f)) := by
    have hsmul : (fun n => Λ (ψ n)) =
        fun n => a * Λ (uniformTestApproxSequence f n) := by
      funext n
      simp [ψ, Λ, map_smul, smul_eq_mul]
    rw [hsmul]
    simpa using
      (tendsto_fourierTestApproxValues C hC hgrowth heven hpos f).const_mul a
  exact tendsto_nhds_unique hlimitSmul hlinearLimits

/-- The continuous extension as a real-linear functional on compactly supported continuous
functions. -/
noncomputable def fourierCccLinearMap (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (∫ z in Metric.closedBall 0 R, |C z|) ≤ A * R ^ k)
    (heven : (fun z : Plane => C (-z)) =ᵐ[volume] C)
    (hpos : ∀ φ : TestFn, 0 ≤ ∫ p : Plane × Plane,
      φ p.1 * φ p.2 * C (p.1 - p.2)) : C_c(Plane, ℝ) →ₗ[ℝ] ℝ where
  toFun := fourierCccValue C hC hgrowth
  map_add' := fourierCccValue_add C hC hgrowth heven hpos
  map_smul' := fourierCccValue_smul C hC hgrowth heven hpos

/-- Positivity of the continuous extension as a positive linear map on compactly supported
continuous functions. -/
noncomputable def fourierCccPositiveLinearMap (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (∫ z in Metric.closedBall 0 R, |C z|) ≤ A * R ^ k)
    (heven : (fun z : Plane => C (-z)) =ᵐ[volume] C)
    (hpos : ∀ φ : TestFn, 0 ≤ ∫ p : Plane × Plane,
      φ p.1 * φ p.2 * C (p.1 - p.2)) : C_c(Plane, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀ (fourierCccLinearMap C hC hgrowth heven hpos)
    (fun f hf => fourierCccValue_nonneg C hC hgrowth heven hpos f hf)

/-- The measure representing the positive Fourier-side functional on compactly supported
continuous tests. -/
noncomputable def fourierCccRieszMeasure (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (∫ z in Metric.closedBall 0 R, |C z|) ≤ A * R ^ k)
    (heven : (fun z : Plane => C (-z)) =ᵐ[volume] C)
    (hpos : ∀ φ : TestFn, 0 ≤ ∫ p : Plane × Plane,
      φ p.1 * φ p.2 * C (p.1 - p.2)) : Measure Plane :=
  RealRMK.rieszMeasure (fourierCccPositiveLinearMap C hC hgrowth heven hpos)

/-- The Riesz measure of the extended Fourier functional is locally finite. -/
theorem fourierCccRieszMeasure_isLocallyFinite (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (∫ z in Metric.closedBall 0 R, |C z|) ≤ A * R ^ k)
    (heven : (fun z : Plane => C (-z)) =ᵐ[volume] C)
    (hpos : ∀ φ : TestFn, 0 ≤ ∫ p : Plane × Plane,
      φ p.1 * φ p.2 * C (p.1 - p.2)) :
    IsLocallyFiniteMeasure (fourierCccRieszMeasure C hC hgrowth heven hpos) := by
  let Λ := fourierCccPositiveLinearMap C hC hgrowth heven hpos
  let ν := fourierCccRieszMeasure C hC hgrowth heven hpos
  let K := Critical2DKPZ.RandomMeasure.vagueCompactExhaustion Plane
  have hfinite : IsFiniteMeasureOnCompacts ν :=
    Critical2DKPZ.RandomMeasure.rieszMeasure_isFiniteOnCompacts K Λ
  have hlocal : IsLocallyFiniteMeasure ν := by
    refine ⟨fun x => ?_⟩
    obtain ⟨L, hL, hxL⟩ := exists_compact_mem_nhds x
    exact ⟨L, hxL, hfinite.lt_top_of_isCompact hL⟩
  simpa [ν] using hlocal

/-- Regard a smooth compactly supported test as a compactly supported continuous function. -/
def testFnToCcc (f : TestFn) : C_c(Plane, ℝ) where
  toFun := f
  continuous_toFun := f.continuous
  hasCompactSupport' := f.hasCompactSupport

/-- Viewing a test function as a compactly supported continuous function preserves its values. -/
@[simp] theorem testFnToCcc_apply (f : TestFn) (x : Plane) :
    testFnToCcc f x = f x := rfl

/-- The continuous extension agrees with its original Fourier functional on smooth tests. -/
theorem fourierCccValue_testFn (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (∫ z in Metric.closedBall 0 R, |C z|) ≤ A * R ^ k)
    (heven : (fun z : Plane => C (-z)) =ᵐ[volume] C)
    (hpos : ∀ φ : TestFn, 0 ≤ ∫ p : Plane × Plane,
      φ p.1 * φ p.2 * C (p.1 - p.2))
    (f : TestFn) :
    fourierCccValue C hC hgrowth (testFnToCcc f) =
      fourierTestLinearMap C hC hgrowth f := by
  let ψ : ℕ → TestFn := fun _ => f
  let e : ℕ → ℝ := fun _ => 0
  have hK : IsCompact (tsupport f) := f.hasCompactSupport.isCompact
  have hsupport : ∀ n, tsupport (ψ n) ⊆ tsupport f :=
    fun _ => subset_rfl
  have he : Tendsto e atTop (𝓝 0) := tendsto_const_nhds
  have happrox (n : ℕ) (x : Plane) : |ψ n x - testFnToCcc f x| ≤ e n := by
    simp [ψ, e, testFnToCcc_apply]
  have hlimit := tendsto_fourierTestValue_of_uniform_approx
    C hC hgrowth heven hpos (testFnToCcc f) ψ (tsupport f) hK hsupport e he happrox
  have hconstant : Tendsto (fun _ : ℕ => fourierTestLinearMap C hC hgrowth f)
      atTop (𝓝 (fourierTestLinearMap C hC hgrowth f)) := tendsto_const_nhds
  exact tendsto_nhds_unique hlimit hconstant


/-- The Riesz measure represents the Fourier functional on every smooth compact test. -/
theorem fourierCccRieszMeasure_integral_testFn (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (∫ z in Metric.closedBall 0 R, |C z|) ≤ A * R ^ k)
    (heven : (fun z : Plane => C (-z)) =ᵐ[volume] C)
    (hpos : ∀ φ : TestFn, 0 ≤ ∫ p : Plane × Plane,
      φ p.1 * φ p.2 * C (p.1 - p.2))
    (f : TestFn) :
    (∫ x : Plane, f x ∂fourierCccRieszMeasure C hC hgrowth heven hpos) =
      fourierTestLinearMap C hC hgrowth f := by
  change (∫ x : Plane, testFnToCcc f x ∂
      RealRMK.rieszMeasure (fourierCccPositiveLinearMap C hC hgrowth heven hpos)) =
    fourierTestLinearMap C hC hgrowth f
  rw [RealRMK.integral_rieszMeasure]
  exact fourierCccValue_testFn C hC hgrowth heven hpos f

end Critical2DKPZ.Spectral

end
