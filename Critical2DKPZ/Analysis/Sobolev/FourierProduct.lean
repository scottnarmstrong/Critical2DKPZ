/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.SmoothTestIntegral
public import Critical2DKPZ.Analysis.Sobolev.WeightedFourierIntegrability
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Distribution.TemperateGrowth

/-! Multiplication by a smooth compactly supported function becomes convolution in angular Fourier coordinates, both for functions and for distribution pairings. -/

@[expose] public section

noncomputable section

open MeasureTheory
open TopologicalSpace
open scoped FourierTransform SchwartzMap

namespace Critical2DKPZ.Analysis.Sobolev

/-- The real test-function family from the cosine part of Fourier inversion after multiplying
by ψ and modulating at angular frequency ξ. -/
def fourierProductCosFamily (χ ψ : TestFn) (ξ η : Plane) : TestFn :=
  ((𝓕 (testFnSchwartz χ)) η).re • ψ.mulCos (ξ - (2 * Real.pi) • η) +
    ((𝓕 (testFnSchwartz χ)) η).im • ψ.mulSin (ξ - (2 * Real.pi) • η)

/-- The real test-function family from the sine part of Fourier inversion after multiplying
by ψ and modulating at angular frequency ξ. -/
def fourierProductSinFamily (χ ψ : TestFn) (ξ η : Plane) : TestFn :=
  ((𝓕 (testFnSchwartz χ)) η).re • ψ.mulSin (ξ - (2 * Real.pi) • η) -
    ((𝓕 (testFnSchwartz χ)) η).im • ψ.mulCos (ξ - (2 * Real.pi) • η)

private theorem iteratedFDeriv_fourierProductCosFamily_apply
    (χ ψ : TestFn) (ξ η x : Plane) (n : ℕ) :
    iteratedFDeriv ℝ n (fourierProductCosFamily χ ψ ξ η) x =
      ((𝓕 (testFnSchwartz χ)) η).re •
          iteratedFDeriv ℝ n (ψ.mulCos (ξ - (2 * Real.pi) • η)) x +
        ((𝓕 (testFnSchwartz χ)) η).im •
          iteratedFDeriv ℝ n (ψ.mulSin (ξ - (2 * Real.pi) • η)) x := by
  let a := ((𝓕 (testFnSchwartz χ)) η).re
  let b := ((𝓕 (testFnSchwartz χ)) η).im
  let z := ξ - (2 * Real.pi) • η
  have hcos : ContDiff ℝ (n : WithTop ℕ∞) (fun y : Plane => ψ.mulCos z y) :=
    (ψ.mulCos z).contDiff.of_le (by simp)
  have hsin : ContDiff ℝ (n : WithTop ℕ∞) (fun y : Plane => ψ.mulSin z y) :=
    (ψ.mulSin z).contDiff.of_le (by simp)
  have hca : ContDiff ℝ (n : WithTop ℕ∞) (fun y : Plane => a • ψ.mulCos z y) := by
    fun_prop
  have hsb : ContDiff ℝ (n : WithTop ℕ∞) (fun y : Plane => b • ψ.mulSin z y) := by
    fun_prop
  change iteratedFDeriv ℝ n
    ((fun y : Plane => a • ψ.mulCos z y) + (fun y : Plane => b • ψ.mulSin z y)) x = _
  rw [iteratedFDeriv_add_apply hca.contDiffAt hsb.contDiffAt,
    iteratedFDeriv_const_smul_apply' hcos.contDiffAt,
    iteratedFDeriv_const_smul_apply' hsin.contDiffAt]

private theorem iteratedFDeriv_fourierProductSinFamily_apply
    (χ ψ : TestFn) (ξ η x : Plane) (n : ℕ) :
    iteratedFDeriv ℝ n (fourierProductSinFamily χ ψ ξ η) x =
      ((𝓕 (testFnSchwartz χ)) η).re •
          iteratedFDeriv ℝ n (ψ.mulSin (ξ - (2 * Real.pi) • η)) x -
        ((𝓕 (testFnSchwartz χ)) η).im •
          iteratedFDeriv ℝ n (ψ.mulCos (ξ - (2 * Real.pi) • η)) x := by
  let a := ((𝓕 (testFnSchwartz χ)) η).re
  let b := ((𝓕 (testFnSchwartz χ)) η).im
  let z := ξ - (2 * Real.pi) • η
  have hsin : ContDiff ℝ (n : WithTop ℕ∞) (fun y : Plane => ψ.mulSin z y) :=
    (ψ.mulSin z).contDiff.of_le (by simp)
  have hcos : ContDiff ℝ (n : WithTop ℕ∞) (fun y : Plane => ψ.mulCos z y) :=
    (ψ.mulCos z).contDiff.of_le (by simp)
  have hsa : ContDiff ℝ (n : WithTop ℕ∞) (fun y : Plane => a • ψ.mulSin z y) := by
    fun_prop
  have hcb : ContDiff ℝ (n : WithTop ℕ∞) (fun y : Plane => b • ψ.mulCos z y) := by
    fun_prop
  change iteratedFDeriv ℝ n
    ((fun y : Plane => a • ψ.mulSin z y) - (fun y : Plane => b • ψ.mulCos z y)) x = _
  rw [iteratedFDeriv_sub_apply hsa.contDiffAt hcb.contDiffAt,
    iteratedFDeriv_const_smul_apply' hsin.contDiffAt,
    iteratedFDeriv_const_smul_apply' hcos.contDiffAt]

private theorem hasTemperateGrowth_testFnTrigKernel (ψ : TestFn) (trig : ℝ → ℝ)
    (htrig : trig.HasTemperateGrowth) :
    (fun p : Plane × Plane => ψ p.2 * trig (inner ℝ p.1 p.2)).HasTemperateGrowth := by
  have hfst : (fun p : Plane × Plane => p.1).HasTemperateGrowth := by
    exact (ContinuousLinearMap.fst ℝ Plane Plane).hasTemperateGrowth
  have hsnd : (fun p : Plane × Plane => p.2).HasTemperateGrowth := by
    exact (ContinuousLinearMap.snd ℝ Plane Plane).hasTemperateGrowth
  have hψ : (fun x : Plane => ψ x).HasTemperateGrowth :=
    ψ.hasCompactSupport.hasTemperateGrowth ψ.contDiff
  have hψ' : (fun p : Plane × Plane => ψ p.2).HasTemperateGrowth := hψ.comp hsnd
  have hangle : (fun p : Plane × Plane => inner ℝ p.1 p.2).HasTemperateGrowth :=
    (innerSL ℝ).bilinear_hasTemperateGrowth hfst hsnd
  exact hψ'.mul (htrig.comp hangle)

/-- Every spatial jet of a modulated compactly supported test function has polynomial growth in
the modulation frequency, uniformly over space. -/
private theorem exists_uniform_testFnMulTrig_jet (ψ : TestFn) (trig : ℝ → ℝ)
    (htrig : trig.HasTemperateGrowth) (f : Plane → Plane → ℝ)
    (hf : ∀ z x, f z x = ψ x * trig (inner ℝ z x))
    (hsupp : ∀ z, tsupport (f z) ⊆ tsupport ψ) (n : ℕ) :
    ∃ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ z x : Plane,
        ‖iteratedFDeriv ℝ n (f z) x‖ ≤ C * (1 + ‖z‖) ^ m := by
  let G : Plane × Plane → ℝ :=
    fun p => ψ p.2 * trig (inner ℝ p.1 p.2)
  let J : Plane →L[ℝ] Plane × Plane := ContinuousLinearMap.inr ℝ Plane Plane
  let K : Compacts Plane := ⟨tsupport ψ, ψ.hasCompactSupport.isCompact⟩
  obtain ⟨m, C, hC, hG⟩ :=
    (hasTemperateGrowth_testFnTrigKernel ψ trig htrig).norm_iteratedFDeriv_le_uniform n
  obtain ⟨R, hR⟩ := K.2.bddAbove_image continuous_norm.continuousOn
  change ∀ y ∈ (fun x : Plane => ‖x‖) '' (K : Set Plane), y ≤ R at hR
  have hR0 : 0 ≤ max R 0 := le_max_right R 0
  have hRx : ∀ x ∈ (K : Set Plane), ‖x‖ ≤ max R 0 := by
    intro x hx
    have hxR : ‖x‖ ≤ R := hR _ ⟨x, hx, rfl⟩
    exact hxR.trans (le_max_left R 0)
  have hshift : ∀ z : Plane, ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Plane × Plane => G ((z, 0) + p)) := by
    intro z
    exact ((hasTemperateGrowth_testFnTrigKernel ψ trig htrig).1).comp
      (contDiff_const.add contDiff_id)
  let D : ℝ := max ‖J‖ 1
  have hD : 0 ≤ D := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_right _ _)
  have hJ : ‖J‖ ≤ D := le_max_left _ _
  refine ⟨m, C * D ^ n * (1 + max R 0) ^ m, ?_, ?_⟩
  · positivity
  · intro z x
    by_cases hx : x ∈ (K : Set Plane)
    · have hfamily : (fun y : Plane => f z y) =
          (fun y : Plane => G ((z, 0) + J y)) := by
        funext y
        rw [hf]
        simp [G, J]
      have hfamily' : f z = (fun y : Plane => G ((z, 0) + J y)) := by
        funext y
        exact congrFun hfamily y
      have hcomp := J.iteratedFDeriv_comp_right (n := n)
        ((hshift z).of_le
          (show (n : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) by simp)) x
        (i := n) le_rfl
      have hcomp' := hcomp
      change iteratedFDeriv ℝ n (fun y : Plane => G ((z, 0) + J y)) x = _ at hcomp'
      change ‖iteratedFDeriv ℝ n (f z) x‖ ≤
        C * D ^ n * (1 + max R 0) ^ m * (1 + ‖z‖) ^ m
      rw [hfamily', hcomp']
      have hshiftJet :
          iteratedFDeriv ℝ n (fun p : Plane × Plane => G ((z, 0) + p)) (J x) =
            iteratedFDeriv ℝ n G ((z, 0) + J x) :=
        iteratedFDeriv_comp_add_left n (z, 0) (J x)
      rw [hshiftJet]
      have hnorm := (iteratedFDeriv ℝ n G ((z, 0) + J x)).norm_compContinuousLinearMap_le
        (fun _ => J)
      have hprod : (∏ _i : Fin n, ‖J‖) = ‖J‖ ^ n := by simp
      rw [hprod] at hnorm
      have hJpow : ‖J‖ ^ n ≤ D ^ n := pow_le_pow_left₀ (norm_nonneg _) hJ n
      have hpoint : ‖iteratedFDeriv ℝ n G ((z, 0) + J x)‖ ≤
          C * (1 + ‖(z, x)‖) ^ m := by
        simpa [J] using hG n (le_rfl) (z, x)
      have hpair : ‖(z, x)‖ ≤ ‖z‖ + ‖x‖ := by
        apply norm_prod_le_iff.mpr
        constructor <;> nlinarith [norm_nonneg z, norm_nonneg x]
      have hbase : 1 + ‖(z, x)‖ ≤ (1 + max R 0) * (1 + ‖z‖) := by
        have hz : 0 ≤ ‖z‖ := norm_nonneg z
        have hx' : ‖x‖ ≤ max R 0 := hRx x hx
        calc
          1 + ‖(z, x)‖ ≤ 1 + ‖z‖ + max R 0 := by linarith
          _ ≤ (1 + max R 0) * (1 + ‖z‖) := by nlinarith [mul_nonneg hR0 hz]
      have hpow : (1 + ‖(z, x)‖) ^ m ≤
          (1 + max R 0) ^ m * (1 + ‖z‖) ^ m := by
        calc
          (1 + ‖(z, x)‖) ^ m ≤ ((1 + max R 0) * (1 + ‖z‖)) ^ m :=
            pow_le_pow_left₀ (by positivity) hbase m
          _ = _ := by rw [mul_pow]
      calc
        ‖(iteratedFDeriv ℝ n G ((z, 0) + J x)).compContinuousLinearMap
            (fun _ => J)‖ ≤
          ‖iteratedFDeriv ℝ n G ((z, 0) + J x)‖ * ‖J‖ ^ n := hnorm
        _ ≤ (C * (1 + ‖(z, x)‖) ^ m) * D ^ n :=
          mul_le_mul hpoint hJpow (pow_nonneg (norm_nonneg _) _) (by positivity)
        _ ≤ (C * ((1 + max R 0) ^ m * (1 + ‖z‖) ^ m)) * D ^ n :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow (by positivity)) (pow_nonneg hD _)
        _ = (C * D ^ n * (1 + max R 0) ^ m) * (1 + ‖z‖) ^ m := by ring
    · have hzero : iteratedFDeriv ℝ n (f z) x = 0 := by
        have hts : tsupport (f z) ⊆ tsupport ψ := hsupp z
        apply image_eq_zero_of_notMem_tsupport
        intro hx'
        exact hx (hts (tsupport_iteratedFDeriv_subset n hx'))
      rw [hzero]
      simp only [norm_zero]
      positivity

private theorem exists_uniform_testFnMulCos_jet (ψ : TestFn) (n : ℕ) :
    ∃ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ z x : Plane,
        ‖iteratedFDeriv ℝ n (ψ.mulCos z) x‖ ≤ C * (1 + ‖z‖) ^ m :=
  exists_uniform_testFnMulTrig_jet ψ Real.cos Real.hasTemperateGrowth_cos
    (fun z x => ψ.mulCos z x)
    (by intro z x; simp [TestFn.mulCos_apply])
    (by
      intro z
      change tsupport (fun y : Plane => ψ y * Real.cos (inner ℝ z y)) ⊆ tsupport ψ
      exact tsupport_mul_subset_left)
    n

private theorem exists_uniform_testFnMulSin_jet (ψ : TestFn) (n : ℕ) :
    ∃ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ z x : Plane,
        ‖iteratedFDeriv ℝ n (ψ.mulSin z) x‖ ≤ C * (1 + ‖z‖) ^ m :=
  exists_uniform_testFnMulTrig_jet ψ Real.sin Real.hasTemperateGrowth_sin
    (fun z x => ψ.mulSin z x)
    (by intro z x; simp [TestFn.mulSin_apply])
    (by
      intro z
      change tsupport (fun y : Plane => ψ y * Real.sin (inner ℝ z y)) ⊆ tsupport ψ
      exact tsupport_mul_subset_left)
    n

private theorem norm_complex_smul_add_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (k : ℂ) (u v : F) :
    ‖k.re • u + k.im • v‖ ≤ 2 * ‖k‖ * max ‖u‖ ‖v‖ := by
  calc
    ‖k.re • u + k.im • v‖ ≤ ‖k.re • u‖ + ‖k.im • v‖ := norm_add_le _ _
    _ = |k.re| * ‖u‖ + |k.im| * ‖v‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ ‖k‖ * max ‖u‖ ‖v‖ + ‖k‖ * max ‖u‖ ‖v‖ := by
      exact add_le_add
        (mul_le_mul (Complex.abs_re_le_norm k) (le_max_left _ _)
          (norm_nonneg _) (norm_nonneg k))
        (mul_le_mul (Complex.abs_im_le_norm k) (le_max_right _ _)
          (norm_nonneg _) (norm_nonneg k))
    _ = 2 * ‖k‖ * max ‖u‖ ‖v‖ := by ring

private theorem norm_complex_smul_sub_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (k : ℂ) (u v : F) :
    ‖k.re • u - k.im • v‖ ≤ 2 * ‖k‖ * max ‖u‖ ‖v‖ := by
  calc
    ‖k.re • u - k.im • v‖ ≤ ‖k.re • u‖ + ‖k.im • v‖ := norm_sub_le _ _
    _ = |k.re| * ‖u‖ + |k.im| * ‖v‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ ‖k‖ * max ‖u‖ ‖v‖ + ‖k‖ * max ‖u‖ ‖v‖ := by
      exact add_le_add
        (mul_le_mul (Complex.abs_re_le_norm k) (le_max_left _ _)
          (norm_nonneg _) (norm_nonneg k))
        (mul_le_mul (Complex.abs_im_le_norm k) (le_max_right _ _)
          (norm_nonneg _) (norm_nonneg k))
    _ = 2 * ‖k‖ * max ‖u‖ ‖v‖ := by ring

/-- One integrable Fourier-weight majorant controls every spatial jet of both real Fourier
product families. -/
private theorem exists_integrable_fourierProductFamilies_jet_bound
    (χ ψ : TestFn) (ξ : Plane) (n : ℕ) :
    ∃ g : Plane → ℝ, Integrable g ∧
      ∀ η x : Plane,
        ‖iteratedFDeriv ℝ n (fourierProductCosFamily χ ψ ξ η) x‖ ≤ g η ∧
          ‖iteratedFDeriv ℝ n (fourierProductSinFamily χ ψ ξ η) x‖ ≤ g η := by
  obtain ⟨mc, Cc, hCc, hcos⟩ := exists_uniform_testFnMulCos_jet ψ n
  obtain ⟨ms, Cs, hCs, hsin⟩ := exists_uniform_testFnMulSin_jet ψ n
  let M := max mc ms
  let C := max Cc Cs
  let A : ℝ := 1 + ‖ξ‖ + 2 * Real.pi
  let D : ℝ := 2 * C * A ^ M * 2 ^ M
  let k : Plane → ℂ := fun η => (𝓕 (testFnSchwartz χ)) η
  let g : Plane → ℝ := fun η => D * ((1 + ‖η‖ ^ 2) ^ M * ‖k η‖)
  have hMcos : mc ≤ M := le_max_left _ _
  have hMsin : ms ≤ M := le_max_right _ _
  have hCcos : Cc ≤ C := le_max_left _ _
  have hCsin : Cs ≤ C := le_max_right _ _
  have hC : 0 ≤ C := le_trans hCc hCcos
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hweight : Integrable (fun η : Plane =>
      (1 + ‖η‖ ^ 2) ^ M * ‖(𝓕 (testFnSchwartz χ)) η‖) := by
    simpa only [Real.rpow_natCast] using
      (integrable_negSobolevWeight_mul_norm_fourier_testFn (a := (M : ℝ))
        (by positivity) χ)
  refine ⟨g, ?_, ?_⟩
  · simpa only [g, k] using hweight.const_mul D
  · intro η x
    let z : Plane := ξ - (2 * Real.pi) • η
    let q : ℝ := 1 + ‖z‖
    have hq : 1 ≤ q := by
      change 1 ≤ 1 + ‖z‖
      exact le_add_of_nonneg_right (norm_nonneg z)
    have hcosM : ‖iteratedFDeriv ℝ n (ψ.mulCos z) x‖ ≤ C * q ^ M := by
      calc
        ‖iteratedFDeriv ℝ n (ψ.mulCos z) x‖ ≤ Cc * q ^ mc := hcos z x
        _ ≤ C * q ^ M :=
          mul_le_mul hCcos (pow_le_pow_right₀ hq hMcos)
            (pow_nonneg (by positivity) _) (by positivity)
    have hsinM : ‖iteratedFDeriv ℝ n (ψ.mulSin z) x‖ ≤ C * q ^ M := by
      calc
        ‖iteratedFDeriv ℝ n (ψ.mulSin z) x‖ ≤ Cs * q ^ ms := hsin z x
        _ ≤ C * q ^ M :=
          mul_le_mul hCsin (pow_le_pow_right₀ hq hMsin)
            (pow_nonneg (by positivity) _) (by positivity)
    have hmax : max
        ‖iteratedFDeriv ℝ n (ψ.mulCos z) x‖
        ‖iteratedFDeriv ℝ n (ψ.mulSin z) x‖ ≤ C * q ^ M := max_le hcosM hsinM
    have hmaxSin : max
        ‖iteratedFDeriv ℝ n (ψ.mulSin z) x‖
        ‖iteratedFDeriv ℝ n (ψ.mulCos z) x‖ ≤ C * q ^ M := by
      rw [max_comm]
      exact hmax
    have hform := iteratedFDeriv_fourierProductCosFamily_apply χ ψ ξ η x n
    have hjet : ‖iteratedFDeriv ℝ n (fourierProductCosFamily χ ψ ξ η) x‖ ≤
        2 * ‖k η‖ * (C * q ^ M) := by
      calc
        ‖iteratedFDeriv ℝ n (fourierProductCosFamily χ ψ ξ η) x‖ ≤
            2 * ‖k η‖ * max
              ‖iteratedFDeriv ℝ n (ψ.mulCos z) x‖
              ‖iteratedFDeriv ℝ n (ψ.mulSin z) x‖ := by
                rw [hform]
                exact norm_complex_smul_add_le (k η) _ _
        _ ≤ 2 * ‖k η‖ * (C * q ^ M) :=
          mul_le_mul_of_nonneg_left hmax (by positivity)
    have hformSin := iteratedFDeriv_fourierProductSinFamily_apply χ ψ ξ η x n
    have hjetSin : ‖iteratedFDeriv ℝ n (fourierProductSinFamily χ ψ ξ η) x‖ ≤
        2 * ‖k η‖ * (C * q ^ M) := by
      calc
        ‖iteratedFDeriv ℝ n (fourierProductSinFamily χ ψ ξ η) x‖ ≤
            2 * ‖k η‖ * max
              ‖iteratedFDeriv ℝ n (ψ.mulSin z) x‖
              ‖iteratedFDeriv ℝ n (ψ.mulCos z) x‖ := by
                rw [hformSin]
                exact norm_complex_smul_sub_le (k η) _ _
        _ ≤ 2 * ‖k η‖ * (C * q ^ M) :=
          mul_le_mul_of_nonneg_left hmaxSin (by positivity)
    have hz : ‖z‖ ≤ ‖ξ‖ + (2 * Real.pi) * ‖η‖ := by
      dsimp [z]
      calc
        ‖ξ - (2 * Real.pi) • η‖ ≤ ‖ξ‖ + ‖(2 * Real.pi) • η‖ := norm_sub_le _ _
        _ = ‖ξ‖ + (2 * Real.pi) * ‖η‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    have hbase : q ≤ A * (1 + ‖η‖) := by
      dsimp [q, A]
      calc
        1 + ‖z‖ ≤ (1 + ‖ξ‖) + (2 * Real.pi) * ‖η‖ := by linarith
        _ ≤ (1 + ‖ξ‖ + 2 * Real.pi) * (1 + ‖η‖) := by
          have hξ : 0 ≤ ‖ξ‖ := norm_nonneg ξ
          have hη : 0 ≤ ‖η‖ := norm_nonneg η
          have hπ : 0 ≤ 2 * Real.pi := by positivity
          nlinarith [mul_nonneg hξ hη]
    have hlinear : 1 + ‖η‖ ≤ 2 * (1 + ‖η‖ ^ 2) := by
      nlinarith [sq_nonneg (‖η‖ - (1 / 4 : ℝ))]
    have hqpow : q ^ M ≤ (A * (1 + ‖η‖)) ^ M :=
      pow_le_pow_left₀ (by positivity) hbase M
    have hpow : (1 + ‖η‖) ^ M ≤ (2 * (1 + ‖η‖ ^ 2)) ^ M :=
      pow_le_pow_left₀ (by positivity) hlinear M
    have hconstant : 0 ≤ 2 * ‖k η‖ * C * A ^ M := by positivity
    have hboundCos :
        ‖iteratedFDeriv ℝ n (fourierProductCosFamily χ ψ ξ η) x‖ ≤ g η := by
      calc
        ‖iteratedFDeriv ℝ n (fourierProductCosFamily χ ψ ξ η) x‖ ≤
            2 * ‖k η‖ * (C * q ^ M) := hjet
        _ = (2 * ‖k η‖ * C) * q ^ M := by ring
        _ ≤ (2 * ‖k η‖ * C) * (A * (1 + ‖η‖)) ^ M :=
            mul_le_mul_of_nonneg_left hqpow (by positivity)
        _ = (2 * ‖k η‖ * C * A ^ M) * (1 + ‖η‖) ^ M := by
            rw [mul_pow]
            ring
        _ ≤ (2 * ‖k η‖ * C * A ^ M) *
            (2 * (1 + ‖η‖ ^ 2)) ^ M :=
            mul_le_mul_of_nonneg_left hpow hconstant
        _ = D * ((1 + ‖η‖ ^ 2) ^ M * ‖k η‖) := by
            dsimp [D]
            rw [mul_pow]
            ring
    have hboundSin :
        ‖iteratedFDeriv ℝ n (fourierProductSinFamily χ ψ ξ η) x‖ ≤ g η := by
      calc
        ‖iteratedFDeriv ℝ n (fourierProductSinFamily χ ψ ξ η) x‖ ≤
            2 * ‖k η‖ * (C * q ^ M) := hjetSin
        _ = (2 * ‖k η‖ * C) * q ^ M := by ring
        _ ≤ (2 * ‖k η‖ * C) * (A * (1 + ‖η‖)) ^ M :=
            mul_le_mul_of_nonneg_left hqpow (by positivity)
        _ = (2 * ‖k η‖ * C * A ^ M) * (1 + ‖η‖) ^ M := by
            rw [mul_pow]
            ring
        _ ≤ (2 * ‖k η‖ * C * A ^ M) *
            (2 * (1 + ‖η‖ ^ 2)) ^ M :=
            mul_le_mul_of_nonneg_left hpow hconstant
        _ = D * ((1 + ‖η‖ ^ 2) ^ M * ‖k η‖) := by
            dsimp [D]
            rw [mul_pow]
            ring
    exact ⟨hboundCos, hboundSin⟩

private def fourierProductCosFamilySupported (χ ψ : TestFn) (ξ η : Plane) :
    ContDiffMapSupportedIn Plane ℝ ⊤ ⟨tsupport ψ, ψ.hasCompactSupport.isCompact⟩ := {
  toFun := fourierProductCosFamily χ ψ ξ η
  contDiff' := (fourierProductCosFamily χ ψ ξ η).contDiff
  zero_on_compl' := by
    intro x hx
    have hψ : ψ x = 0 := image_eq_zero_of_notMem_tsupport hx
    change fourierProductCosFamily χ ψ ξ η x = 0
    simp [fourierProductCosFamily, TestFn.mulCos_apply, TestFn.mulSin_apply, hψ]
}

private def fourierProductSinFamilySupported (χ ψ : TestFn) (ξ η : Plane) :
    ContDiffMapSupportedIn Plane ℝ ⊤ ⟨tsupport ψ, ψ.hasCompactSupport.isCompact⟩ := {
  toFun := fourierProductSinFamily χ ψ ξ η
  contDiff' := (fourierProductSinFamily χ ψ ξ η).contDiff
  zero_on_compl' := by
    intro x hx
    have hψ : ψ x = 0 := image_eq_zero_of_notMem_tsupport hx
    change fourierProductSinFamily χ ψ ξ η x = 0
    simp [fourierProductSinFamily, TestFn.mulCos_apply, TestFn.mulSin_apply, hψ]
}

private theorem contDiff_fourierProductCosFamily (χ ψ : TestFn) (ξ : Plane) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Plane × Plane => fourierProductCosFamily χ ψ ξ p.1 p.2) := by
  have hFourier : ContDiff ℝ (⊤ : ℕ∞)
      (fun η : Plane => (𝓕 (testFnSchwartz χ)) η) :=
    (𝓕 (testFnSchwartz χ)).smooth ⊤
  have hRe : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Plane × Plane => ((𝓕 (testFnSchwartz χ)) p.1).re) :=
    (Complex.reCLM.contDiff.comp hFourier).comp contDiff_fst
  have hIm : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Plane × Plane => ((𝓕 (testFnSchwartz χ)) p.1).im) :=
    (Complex.imCLM.contDiff.comp hFourier).comp contDiff_fst
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (fun p : Plane × Plane => ψ p.2) :=
    ψ.contDiff.comp contDiff_snd
  have hθ : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Plane × Plane => inner ℝ (ξ - (2 * Real.pi) • p.1) p.2) := by
    have hfreq : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : Plane × Plane => ξ - (2 * Real.pi) • p.1) := by
      fun_prop
    exact contDiff_inner.comp (hfreq.prodMk contDiff_snd)
  have hcos : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Plane × Plane => ψ p.2 * Real.cos (inner ℝ (ξ - (2 * Real.pi) • p.1) p.2)) :=
    hψ.mul (Real.contDiff_cos.comp hθ)
  have hsin : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Plane × Plane => ψ p.2 * Real.sin (inner ℝ (ξ - (2 * Real.pi) • p.1) p.2)) :=
    hψ.mul (Real.contDiff_sin.comp hθ)
  change ContDiff ℝ (⊤ : ℕ∞) (fun p : Plane × Plane =>
    ((𝓕 (testFnSchwartz χ)) p.1).re *
        (ψ p.2 * Real.cos (inner ℝ (ξ - (2 * Real.pi) • p.1) p.2)) +
      ((𝓕 (testFnSchwartz χ)) p.1).im *
        (ψ p.2 * Real.sin (inner ℝ (ξ - (2 * Real.pi) • p.1) p.2)))
  exact (hRe.mul hcos).add (hIm.mul hsin)

private theorem contDiff_fourierProductSinFamily (χ ψ : TestFn) (ξ : Plane) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Plane × Plane => fourierProductSinFamily χ ψ ξ p.1 p.2) := by
  have hFourier : ContDiff ℝ (⊤ : ℕ∞)
      (fun η : Plane => (𝓕 (testFnSchwartz χ)) η) :=
    (𝓕 (testFnSchwartz χ)).smooth ⊤
  have hRe : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Plane × Plane => ((𝓕 (testFnSchwartz χ)) p.1).re) :=
    (Complex.reCLM.contDiff.comp hFourier).comp contDiff_fst
  have hIm : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Plane × Plane => ((𝓕 (testFnSchwartz χ)) p.1).im) :=
    (Complex.imCLM.contDiff.comp hFourier).comp contDiff_fst
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (fun p : Plane × Plane => ψ p.2) :=
    ψ.contDiff.comp contDiff_snd
  have hθ : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Plane × Plane => inner ℝ (ξ - (2 * Real.pi) • p.1) p.2) := by
    have hfreq : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : Plane × Plane => ξ - (2 * Real.pi) • p.1) := by
      fun_prop
    exact contDiff_inner.comp (hfreq.prodMk contDiff_snd)
  have hcos : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Plane × Plane => ψ p.2 * Real.cos (inner ℝ (ξ - (2 * Real.pi) • p.1) p.2)) :=
    hψ.mul (Real.contDiff_cos.comp hθ)
  have hsin : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Plane × Plane => ψ p.2 * Real.sin (inner ℝ (ξ - (2 * Real.pi) • p.1) p.2)) :=
    hψ.mul (Real.contDiff_sin.comp hθ)
  change ContDiff ℝ (⊤ : ℕ∞) (fun p : Plane × Plane =>
    ((𝓕 (testFnSchwartz χ)) p.1).re *
        (ψ p.2 * Real.sin (inner ℝ (ξ - (2 * Real.pi) • p.1) p.2)) -
      ((𝓕 (testFnSchwartz χ)) p.1).im *
        (ψ p.2 * Real.cos (inner ℝ (ξ - (2 * Real.pi) • p.1) p.2)))
  exact (hRe.mul hsin).sub (hIm.mul hcos)

private theorem integrable_fourierProductComplexIntegrand (χ ψ : TestFn) (ξ x : Plane) :
    Integrable (fun η : Plane =>
      (𝓕 (testFnSchwartz χ)) η * (ψ x : ℂ) *
        Complex.exp (-((inner ℝ (ξ - (2 * Real.pi) • η) x : ℂ) * Complex.I))) := by
  let k : Plane → ℂ := fun η => (𝓕 (testFnSchwartz χ)) η
  have hk : Integrable k := (𝓕 (testFnSchwartz χ)).integrable
  have hexpnorm (η : Plane) :
      ‖Complex.exp (-((inner ℝ (ξ - (2 * Real.pi) • η) x : ℂ) * Complex.I))‖ = 1 := by
    have harg :
        -((inner ℝ (ξ - (2 * Real.pi) • η) x : ℂ) * Complex.I) =
          (↑(-inner ℝ (ξ - (2 * Real.pi) • η) x) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [harg, Complex.norm_exp_ofReal_mul_I]
  have hnorm : Integrable (fun η : Plane =>
      ‖k η * (ψ x : ℂ) *
        Complex.exp (-((inner ℝ (ξ - (2 * Real.pi) • η) x : ℂ) * Complex.I))‖) := by
    have heq : (fun η : Plane =>
        ‖k η * (ψ x : ℂ) *
          Complex.exp (-((inner ℝ (ξ - (2 * Real.pi) • η) x : ℂ) * Complex.I))‖) =
        fun η => ‖k η‖ * |ψ x| := by
      funext η
      rw [norm_mul, norm_mul, hexpnorm]
      simp only [Complex.norm_real, Real.norm_eq_abs, mul_one]
    rw [heq]
    exact hk.norm.mul_const |ψ x|
  have hcont : Continuous (fun η : Plane =>
      k η * (ψ x : ℂ) *
        Complex.exp (-((inner ℝ (ξ - (2 * Real.pi) • η) x : ℂ) * Complex.I))) := by
    fun_prop
  exact (integrable_norm_iff hcont.aestronglyMeasurable).mp hnorm

private theorem exp_neg_ofReal_mul_I_re (θ : ℝ) :
    (Complex.exp (-((θ : ℂ) * Complex.I))).re = Real.cos θ := by
  have harg : -((θ : ℂ) * Complex.I) = (↑(-θ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg]
  simpa [Real.cos_neg] using Complex.exp_ofReal_mul_I_re (-θ)

private theorem exp_neg_ofReal_mul_I_im (θ : ℝ) :
    (Complex.exp (-((θ : ℂ) * Complex.I))).im = -Real.sin θ := by
  have harg : -((θ : ℂ) * Complex.I) = (↑(-θ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg]
  simpa [Real.sin_neg] using Complex.exp_ofReal_mul_I_im (-θ)



/-- Multiplication by a real cutoff expresses cosine modulation as an integrable Fourier superposition of translated cosine and sine test functions. -/
theorem fourierProductCosFamily_integral (χ ψ : TestFn) (ξ x : Plane) :
    Integrable (fun η : Plane => fourierProductCosFamily χ ψ ξ η x) ∧
      testFnMul χ ψ x * Real.cos (inner ℝ ξ x) =
        ∫ η : Plane, fourierProductCosFamily χ ψ ξ η x := by
  let k : Plane → ℂ := fun η => (𝓕 (testFnSchwartz χ)) η
  let g : Plane → ℂ := fun η =>
    k η * (ψ x : ℂ) *
      Complex.exp (-((inner ℝ (ξ - (2 * Real.pi) • η) x : ℂ) * Complex.I))
  have hk : Integrable k := (𝓕 (testFnSchwartz χ)).integrable
  have hg : Integrable g := integrable_fourierProductComplexIntegrand χ ψ ξ x
  have hInv : (χ x : ℂ) = ∫ η : Plane,
      Complex.exp ((↑(2 * Real.pi * inner ℝ η x) : ℂ) * Complex.I) * k η := by
    have h := testFn_eq_integral_fourier_inverse χ x
    have hFourier : 𝓕 (fun y : Plane => (χ y : ℂ)) = 𝓕 (testFnSchwartz χ) := by
      congr 1
    rw [hFourier] at h
    simpa only [k] using h
  have hmul : ((testFnMul χ ψ x : ℂ) *
      Complex.exp (-((inner ℝ ξ x : ℂ) * Complex.I))) = ∫ η : Plane, g η := by
    calc
      ((testFnMul χ ψ x : ℂ) *
          Complex.exp (-((inner ℝ ξ x : ℂ) * Complex.I))) =
          (∫ η : Plane,
            Complex.exp ((↑(2 * Real.pi * inner ℝ η x) : ℂ) * Complex.I) * k η) *
            ((ψ x : ℂ) * Complex.exp (-((inner ℝ ξ x : ℂ) * Complex.I))) := by
              rw [← hInv]
              simp only [testFnMul_apply, Complex.ofReal_mul]
              ring
      _ = ∫ η : Plane,
          (Complex.exp ((↑(2 * Real.pi * inner ℝ η x) : ℂ) * Complex.I) * k η) *
            ((ψ x : ℂ) * Complex.exp (-((inner ℝ ξ x : ℂ) * Complex.I))) := by
              exact (integral_mul_const _ _).symm
      _ = ∫ η : Plane, g η := by
        apply integral_congr_ae
        filter_upwards [] with η
        have hangle : inner ℝ (ξ - (2 * Real.pi) • η) x =
            inner ℝ ξ x - 2 * Real.pi * inner ℝ η x := by
          simp [inner_sub_left, inner_smul_left]
        have hphase :
            (↑(2 * Real.pi * inner ℝ η x) : ℂ) * Complex.I -
                (↑(inner ℝ ξ x) : ℂ) * Complex.I =
              -((↑(inner ℝ (ξ - (2 * Real.pi) • η) x) : ℂ) * Complex.I) := by
          rw [Complex.ofReal_mul, hangle, Complex.ofReal_sub]
          push_cast
          ring_nf
        have hphase' :
            (↑(2 * Real.pi * inner ℝ η x) : ℂ) * Complex.I +
                -((↑(inner ℝ ξ x) : ℂ) * Complex.I) =
              -((↑(inner ℝ (ξ - (2 * Real.pi) • η) x) : ℂ) * Complex.I) := by
          simpa only [sub_eq_add_neg] using hphase
        dsimp [g, k]
        calc
          Complex.exp ((↑(2 * Real.pi * inner ℝ η x) : ℂ) * Complex.I) *
              (𝓕 (testFnSchwartz χ)) η *
              ((ψ x : ℂ) * Complex.exp (-((↑(inner ℝ ξ x) : ℂ) * Complex.I))) =
              (𝓕 (testFnSchwartz χ)) η * (ψ x : ℂ) *
                (Complex.exp ((↑(2 * Real.pi * inner ℝ η x) : ℂ) * Complex.I) *
                  Complex.exp (-((↑(inner ℝ ξ x) : ℂ) * Complex.I))) := by ring
          _ = (𝓕 (testFnSchwartz χ)) η * (ψ x : ℂ) *
                Complex.exp ((↑(2 * Real.pi * inner ℝ η x) : ℂ) * Complex.I +
                  -((↑(inner ℝ ξ x) : ℂ) * Complex.I)) := by rw [← Complex.exp_add]
          _ = _ := by rw [hphase']
  have hRe : testFnMul χ ψ x * Real.cos (inner ℝ ξ x) =
      ∫ η : Plane, Complex.re (g η) := by
    have h := congrArg Complex.re hmul
    have hleft :
        testFnMul χ ψ x * Real.cos (inner ℝ ξ x) =
          Complex.re ((testFnMul χ ψ x : ℂ) *
            Complex.exp (-((inner ℝ ξ x : ℂ) * Complex.I))) := by
      simp [testFnMul_apply, Complex.mul_re, Complex.mul_im,
        exp_neg_ofReal_mul_I_re, exp_neg_ofReal_mul_I_im]
    calc
      _ = Complex.re ((testFnMul χ ψ x : ℂ) *
          Complex.exp (-((inner ℝ ξ x : ℂ) * Complex.I))) := hleft
      _ = Complex.re (∫ η : Plane, g η) := h
      _ = ∫ η : Plane, Complex.re (g η) := (integral_re hg).symm
  have hfamily : (fun η : Plane => fourierProductCosFamily χ ψ ξ η x) =
      fun η => Complex.re (g η) := by
    funext η
    simp [fourierProductCosFamily, g, k, TestFn.mulCos_apply, TestFn.mulSin_apply,
      exp_neg_ofReal_mul_I_re, exp_neg_ofReal_mul_I_im]; ring
  refine ⟨hfamily ▸ hg.re, ?_⟩
  rw [hfamily]
  exact hRe

/-- Multiplication by a real cutoff expresses sine modulation as an integrable Fourier superposition of translated cosine and sine test functions. -/
theorem fourierProductSinFamily_integral (χ ψ : TestFn) (ξ x : Plane) :
    Integrable (fun η : Plane => fourierProductSinFamily χ ψ ξ η x) ∧
      testFnMul χ ψ x * Real.sin (inner ℝ ξ x) =
        ∫ η : Plane, fourierProductSinFamily χ ψ ξ η x := by
  let k : Plane → ℂ := fun η => (𝓕 (testFnSchwartz χ)) η
  let g : Plane → ℂ := fun η =>
    k η * (ψ x : ℂ) *
      Complex.exp (-((inner ℝ (ξ - (2 * Real.pi) • η) x : ℂ) * Complex.I))
  have hg : Integrable g := integrable_fourierProductComplexIntegrand χ ψ ξ x
  have hInv : (χ x : ℂ) = ∫ η : Plane,
      Complex.exp ((↑(2 * Real.pi * inner ℝ η x) : ℂ) * Complex.I) * k η := by
    have h := testFn_eq_integral_fourier_inverse χ x
    have hFourier : 𝓕 (fun y : Plane => (χ y : ℂ)) = 𝓕 (testFnSchwartz χ) := by
      congr 1
    rw [hFourier] at h
    simpa only [k] using h
  have hmul : ((testFnMul χ ψ x : ℂ) *
      Complex.exp (-((inner ℝ ξ x : ℂ) * Complex.I))) = ∫ η : Plane, g η := by
    calc
      ((testFnMul χ ψ x : ℂ) *
          Complex.exp (-((inner ℝ ξ x : ℂ) * Complex.I))) =
          (∫ η : Plane,
            Complex.exp ((↑(2 * Real.pi * inner ℝ η x) : ℂ) * Complex.I) * k η) *
            ((ψ x : ℂ) * Complex.exp (-((inner ℝ ξ x : ℂ) * Complex.I))) := by
              rw [← hInv]
              simp only [testFnMul_apply, Complex.ofReal_mul]
              ring
      _ = ∫ η : Plane,
          (Complex.exp ((↑(2 * Real.pi * inner ℝ η x) : ℂ) * Complex.I) * k η) *
            ((ψ x : ℂ) * Complex.exp (-((inner ℝ ξ x : ℂ) * Complex.I))) := by
              exact (integral_mul_const _ _).symm
      _ = ∫ η : Plane, g η := by
        apply integral_congr_ae
        filter_upwards [] with η
        have hangle : inner ℝ (ξ - (2 * Real.pi) • η) x =
            inner ℝ ξ x - 2 * Real.pi * inner ℝ η x := by
          simp [inner_sub_left, inner_smul_left]
        have hphase :
            (↑(2 * Real.pi * inner ℝ η x) : ℂ) * Complex.I -
                (↑(inner ℝ ξ x) : ℂ) * Complex.I =
              -((↑(inner ℝ (ξ - (2 * Real.pi) • η) x) : ℂ) * Complex.I) := by
          rw [Complex.ofReal_mul, hangle, Complex.ofReal_sub]
          push_cast
          ring_nf
        have hphase' :
            (↑(2 * Real.pi * inner ℝ η x) : ℂ) * Complex.I +
                -((↑(inner ℝ ξ x) : ℂ) * Complex.I) =
              -((↑(inner ℝ (ξ - (2 * Real.pi) • η) x) : ℂ) * Complex.I) := by
          simpa only [sub_eq_add_neg] using hphase
        dsimp [g, k]
        calc
          Complex.exp ((↑(2 * Real.pi * inner ℝ η x) : ℂ) * Complex.I) *
              (𝓕 (testFnSchwartz χ)) η *
              ((ψ x : ℂ) * Complex.exp (-((↑(inner ℝ ξ x) : ℂ) * Complex.I))) =
              (𝓕 (testFnSchwartz χ)) η * (ψ x : ℂ) *
                (Complex.exp ((↑(2 * Real.pi * inner ℝ η x) : ℂ) * Complex.I) *
                  Complex.exp (-((↑(inner ℝ ξ x) : ℂ) * Complex.I))) := by ring
          _ = (𝓕 (testFnSchwartz χ)) η * (ψ x : ℂ) *
                Complex.exp ((↑(2 * Real.pi * inner ℝ η x) : ℂ) * Complex.I +
                  -((↑(inner ℝ ξ x) : ℂ) * Complex.I)) := by rw [← Complex.exp_add]
          _ = _ := by rw [hphase']
  have hIm : -testFnMul χ ψ x * Real.sin (inner ℝ ξ x) =
      ∫ η : Plane, Complex.im (g η) := by
    have h := congrArg Complex.im hmul
    have hleft :
        -testFnMul χ ψ x * Real.sin (inner ℝ ξ x) =
          Complex.im ((testFnMul χ ψ x : ℂ) *
            Complex.exp (-((inner ℝ ξ x : ℂ) * Complex.I))) := by
      simp [testFnMul_apply, Complex.mul_re, Complex.mul_im,
        exp_neg_ofReal_mul_I_re, exp_neg_ofReal_mul_I_im]
    calc
      _ = Complex.im ((testFnMul χ ψ x : ℂ) *
          Complex.exp (-((inner ℝ ξ x : ℂ) * Complex.I))) := hleft
      _ = Complex.im (∫ η : Plane, g η) := h
      _ = ∫ η : Plane, Complex.im (g η) := (integral_im hg).symm
  have hfamily : (fun η : Plane => fourierProductSinFamily χ ψ ξ η x) =
      fun η => -Complex.im (g η) := by
    funext η
    simp [fourierProductSinFamily, g, k, TestFn.mulCos_apply, TestFn.mulSin_apply,
      exp_neg_ofReal_mul_I_re, exp_neg_ofReal_mul_I_im]; ring
  have hInt : Integrable (fun η : Plane => -Complex.im (g η)) := hg.im.neg
  have hEq : testFnMul χ ψ x * Real.sin (inner ℝ ξ x) =
      ∫ η : Plane, -Complex.im (g η) := by
    rw [integral_neg]
    linarith
  refine ⟨hfamily ▸ hInt, ?_⟩
  rw [hfamily]
  exact hEq

private theorem distribution_integral_supported_plane_family
    (T : Distr) (K : Compacts Plane)
    (F : Plane → ContDiffMapSupportedIn Plane ℝ ⊤ K)
    (hF : ContDiff ℝ (⊤ : ℕ∞) (fun p : Plane × Plane => F p.1 p.2))
    (hbound : ∀ n : ℕ, ∃ g : Plane → ℝ, Integrable g ∧
      ∀ η x, ‖iteratedFDeriv ℝ n (F η) x‖ ≤ g η)
    (φ : ContDiffMapSupportedIn Plane ℝ ⊤ K)
    (hφ : ∀ x, φ x = ∫ η : Plane, F η x) :
    Integrable (fun η : Plane =>
      T (TestFunction.ofSupportedIn (Set.subset_univ _) (F η))) ∧
      T (TestFunction.ofSupportedIn (Set.subset_univ _) φ) =
        ∫ η : Plane, T (TestFunction.ofSupportedIn (Set.subset_univ _) (F η)) := by
  have hjetInt (m : ℕ) : Integrable (fun η => compactTestJet K m (F η)) volume :=
    integrable_compactTestJet_of_dominated volume K F hF hbound m
  have hDistributionInt := integrable_distribution_compact_family volume T K F hjetInt
  have hcomm := distribution_integral_smooth_test_family_of_parameter volume T K F hF
    hbound φ hφ
  exact ⟨hDistributionInt, hcomm⟩

/-- Multiplication by a smooth cutoff transfers a cosine modulation through a real distribution.
The frequency integral on the right is integrable. -/
theorem distribution_fourierProductCosFamily_integral
    (T : Distr) (χ ψ : TestFn) (ξ : Plane) :
    Integrable (fun η : Plane => T (fourierProductCosFamily χ ψ ξ η)) ∧
      T ((testFnMul χ ψ).mulCos ξ) =
        ∫ η : Plane, T (fourierProductCosFamily χ ψ ξ η) := by
  let K : Compacts Plane := ⟨tsupport ψ, ψ.hasCompactSupport.isCompact⟩
  let F : Plane → ContDiffMapSupportedIn Plane ℝ ⊤ K :=
    fun η => fourierProductCosFamilySupported χ ψ ξ η
  have hF : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Plane × Plane => F p.1 p.2) := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Plane × Plane => fourierProductCosFamily χ ψ ξ p.1 p.2)
    exact contDiff_fourierProductCosFamily χ ψ ξ
  have hbound : ∀ n : ℕ, ∃ g : Plane → ℝ, Integrable g ∧
      ∀ η x, ‖iteratedFDeriv ℝ n (F η) x‖ ≤ g η := by
    intro n
    obtain ⟨g, hg, hgb⟩ := exists_integrable_fourierProductFamilies_jet_bound χ ψ ξ n
    exact ⟨g, hg, fun η x => (hgb η x).1⟩
  let φ : ContDiffMapSupportedIn Plane ℝ ⊤ K := {
    toFun := (testFnMul χ ψ).mulCos ξ
    contDiff' := ((testFnMul χ ψ).mulCos ξ).contDiff
    zero_on_compl' := by
      intro x hx
      have hψ : ψ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [TestFn.mulCos_apply, testFnMul_apply, hψ]
  }
  have hφ : ∀ x, φ x = ∫ η : Plane, F η x := by
    intro x
    change testFnMul χ ψ x * Real.cos (inner ℝ ξ x) =
      ∫ η : Plane, fourierProductCosFamily χ ψ ξ η x
    exact (fourierProductCosFamily_integral χ ψ ξ x).2
  have hcomm := distribution_integral_supported_plane_family T K F hF hbound φ hφ
  have hco (η : Plane) :
      TestFunction.ofSupportedIn (Set.subset_univ _) (F η) =
        fourierProductCosFamily χ ψ ξ η := by
    ext x
    rfl
  have hcoφ : TestFunction.ofSupportedIn (Set.subset_univ _) φ =
      (testFnMul χ ψ).mulCos ξ := by
    ext x
    rfl
  refine ⟨?_, ?_⟩
  · exact hcomm.1.congr
      (Filter.Eventually.of_forall fun η => congrArg T (hco η))
  · calc
      T ((testFnMul χ ψ).mulCos ξ) =
          T (TestFunction.ofSupportedIn (Set.subset_univ _) φ) := by rw [hcoφ]
      _ = ∫ η : Plane,
          T (TestFunction.ofSupportedIn (Set.subset_univ _) (F η)) := hcomm.2
      _ = ∫ η : Plane, T (fourierProductCosFamily χ ψ ξ η) := by
          apply integral_congr_ae
          filter_upwards with η
          exact congrArg T (hco η)

/-- Multiplication by a smooth cutoff transfers a sine modulation through a real distribution.
The frequency integral on the right is integrable. -/
theorem distribution_fourierProductSinFamily_integral
    (T : Distr) (χ ψ : TestFn) (ξ : Plane) :
    Integrable (fun η : Plane => T (fourierProductSinFamily χ ψ ξ η)) ∧
      T ((testFnMul χ ψ).mulSin ξ) =
        ∫ η : Plane, T (fourierProductSinFamily χ ψ ξ η) := by
  let K : Compacts Plane := ⟨tsupport ψ, ψ.hasCompactSupport.isCompact⟩
  let F : Plane → ContDiffMapSupportedIn Plane ℝ ⊤ K :=
    fun η => fourierProductSinFamilySupported χ ψ ξ η
  have hF : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Plane × Plane => F p.1 p.2) := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Plane × Plane => fourierProductSinFamily χ ψ ξ p.1 p.2)
    exact contDiff_fourierProductSinFamily χ ψ ξ
  have hbound : ∀ n : ℕ, ∃ g : Plane → ℝ, Integrable g ∧
      ∀ η x, ‖iteratedFDeriv ℝ n (F η) x‖ ≤ g η := by
    intro n
    obtain ⟨g, hg, hgb⟩ := exists_integrable_fourierProductFamilies_jet_bound χ ψ ξ n
    exact ⟨g, hg, fun η x => (hgb η x).2⟩
  let φ : ContDiffMapSupportedIn Plane ℝ ⊤ K := {
    toFun := (testFnMul χ ψ).mulSin ξ
    contDiff' := ((testFnMul χ ψ).mulSin ξ).contDiff
    zero_on_compl' := by
      intro x hx
      have hψ : ψ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [TestFn.mulSin_apply, testFnMul_apply, hψ]
  }
  have hφ : ∀ x, φ x = ∫ η : Plane, F η x := by
    intro x
    change testFnMul χ ψ x * Real.sin (inner ℝ ξ x) =
      ∫ η : Plane, fourierProductSinFamily χ ψ ξ η x
    exact (fourierProductSinFamily_integral χ ψ ξ x).2
  have hcomm := distribution_integral_supported_plane_family T K F hF hbound φ hφ
  have hco (η : Plane) :
      TestFunction.ofSupportedIn (Set.subset_univ _) (F η) =
        fourierProductSinFamily χ ψ ξ η := by
    ext x
    rfl
  have hcoφ : TestFunction.ofSupportedIn (Set.subset_univ _) φ =
      (testFnMul χ ψ).mulSin ξ := by
    ext x
    rfl
  refine ⟨?_, ?_⟩
  · exact hcomm.1.congr
      (Filter.Eventually.of_forall fun η => congrArg T (hco η))
  · calc
      T ((testFnMul χ ψ).mulSin ξ) =
          T (TestFunction.ofSupportedIn (Set.subset_univ _) φ) := by rw [hcoφ]
      _ = ∫ η : Plane,
          T (TestFunction.ofSupportedIn (Set.subset_univ _) (F η)) := hcomm.2
      _ = ∫ η : Plane, T (fourierProductSinFamily χ ψ ξ η) := by
          apply integral_congr_ae
          filter_upwards with η
          exact congrArg T (hco η)

/-- Fourier localization after multiplication by a cutoff is convolution with the Fourier transform
of that cutoff. The complex frequency integrand is integrable. -/
theorem localizedFourier_testFnMul_eq_scaled_frequency_integral
    (T : Distr) (χ ψ : TestFn) (ξ : Plane) :
    Integrable (fun η : Plane => (𝓕 (testFnSchwartz χ)) η *
      localizedFourier T ψ (ξ - (2 * Real.pi) • η)) ∧
      localizedFourier T (testFnMul χ ψ) ξ =
        ∫ η : Plane, (𝓕 (testFnSchwartz χ)) η *
          localizedFourier T ψ (ξ - (2 * Real.pi) • η) := by
  let k : Plane → ℂ := fun η => (𝓕 (testFnSchwartz χ)) η
  have hcos := distribution_fourierProductCosFamily_integral T χ ψ ξ
  have hsin := distribution_fourierProductSinFamily_integral T χ ψ ξ
  have hcosComplex : Integrable (fun η : Plane =>
      (T (fourierProductCosFamily χ ψ ξ η) : ℂ)) := hcos.1.ofReal (𝕜 := ℂ)
  have hsinComplex : Integrable (fun η : Plane =>
      (T (fourierProductSinFamily χ ψ ξ η) : ℂ)) := hsin.1.ofReal (𝕜 := ℂ)
  have hcomplexCombination : Integrable (fun η : Plane =>
      (T (fourierProductCosFamily χ ψ ξ η) : ℂ) -
        Complex.I * (T (fourierProductSinFamily χ ψ ξ η) : ℂ)) := by
    exact hcosComplex.sub (hsinComplex.const_mul Complex.I)
  have hpoint : ∀ η : Plane,
      k η * localizedFourier T ψ (ξ - (2 * Real.pi) • η) =
        (T (fourierProductCosFamily χ ψ ξ η) : ℂ) -
          Complex.I * (T (fourierProductSinFamily χ ψ ξ η) : ℂ) := by
    intro η
    let z := ξ - (2 * Real.pi) • η
    have hcosEval : T (fourierProductCosFamily χ ψ ξ η) =
        ((𝓕 (testFnSchwartz χ)) η).re * T (ψ.mulCos z) +
          ((𝓕 (testFnSchwartz χ)) η).im * T (ψ.mulSin z) := by
      simp [fourierProductCosFamily, z]
    have hsinEval : T (fourierProductSinFamily χ ψ ξ η) =
        ((𝓕 (testFnSchwartz χ)) η).re * T (ψ.mulSin z) -
          ((𝓕 (testFnSchwartz χ)) η).im * T (ψ.mulCos z) := by
      simp [fourierProductSinFamily, z]
    rw [localizedFourier, hcosEval, hsinEval]
    dsimp [k]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  have hInt : Integrable (fun η : Plane =>
      k η * localizedFourier T ψ (ξ - (2 * Real.pi) • η)) := by
    have heq : (fun η : Plane =>
        k η * localizedFourier T ψ (ξ - (2 * Real.pi) • η)) =
        fun η => (T (fourierProductCosFamily χ ψ ξ η) : ℂ) -
          Complex.I * (T (fourierProductSinFamily χ ψ ξ η) : ℂ) := by
      funext η
      exact hpoint η
    rw [heq]
    exact hcomplexCombination
  have hcosIntegral :
      (∫ η : Plane, (T (fourierProductCosFamily χ ψ ξ η) : ℂ)) =
        (∫ η : Plane, T (fourierProductCosFamily χ ψ ξ η) : ℝ) :=
    integral_complex_ofReal
  have hsinIntegral :
      (∫ η : Plane, (T (fourierProductSinFamily χ ψ ξ η) : ℂ)) =
        (∫ η : Plane, T (fourierProductSinFamily χ ψ ξ η) : ℝ) :=
    integral_complex_ofReal
  refine ⟨hInt, ?_⟩
  calc
    localizedFourier T (testFnMul χ ψ) ξ =
        (∫ η : Plane, (T (fourierProductCosFamily χ ψ ξ η) : ℂ)) -
          Complex.I * (∫ η : Plane, (T (fourierProductSinFamily χ ψ ξ η) : ℂ)) := by
      rw [localizedFourier, hcos.2, hsin.2, ← hcosIntegral, ← hsinIntegral]
    _ = ∫ η : Plane,
        (T (fourierProductCosFamily χ ψ ξ η) : ℂ) -
          Complex.I * (T (fourierProductSinFamily χ ψ ξ η) : ℂ) := by
      rw [integral_sub hcosComplex (hsinComplex.const_mul Complex.I), integral_const_mul]
    _ = ∫ η : Plane, k η *
        localizedFourier T ψ (ξ - (2 * Real.pi) • η) := by
      apply integral_congr_ae
      filter_upwards with η
      exact (hpoint η).symm

end Critical2DKPZ.Analysis.Sobolev

end
