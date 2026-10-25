/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.TranslatedDistributionPairing
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Continuous directional-derivative candidates for translated distribution pairings

For a compactly supported smooth kernel, differentiating its translate gives another smooth
test-function family with the same common spatial support. The corresponding distributional
pairing is jointly continuous in the translation point and direction.
-/

@[expose] public section

noncomputable section

open TopologicalSpace
open MeasureTheory
open scoped Distributions

namespace Critical2DKPZ.Analysis.Sobolev

/-- All finite spatial jets of the product of a fixed test function and a reflected translate of
another test function admit a bound independent of the translation. -/
theorem exists_uniform_translated_product_jet_bound (φ ψ : TestFn) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a x : Plane,
      ‖iteratedFDeriv ℝ n (fun z => φ z * ψ (a - z)) x‖ ≤ C := by
  classical
  choose cφ hcφ using fun i : ℕ =>
    (φ.contDiff.continuous_iteratedFDeriv (by simp)).bounded_above_of_compact_support
      (φ.hasCompactSupport.iteratedFDeriv i)
  choose cψ hcψ using fun i : ℕ =>
    (ψ.contDiff.continuous_iteratedFDeriv (by simp)).bounded_above_of_compact_support
      (ψ.hasCompactSupport.iteratedFDeriv i)
  let Mφ : ℝ := ∑ i ∈ Finset.range (n + 1), max (cφ i) 0
  let Mψ : ℝ := ∑ i ∈ Finset.range (n + 1), max (cψ i) 0
  have hMφ : 0 ≤ Mφ := by
    exact Finset.sum_nonneg fun i _ => le_max_right _ _
  have hMψ : 0 ≤ Mψ := by
    exact Finset.sum_nonneg fun i _ => le_max_right _ _
  have hφbound (i : ℕ) (hi : i ≤ n) (x : Plane) :
      ‖iteratedFDeriv ℝ i φ x‖ ≤ Mφ := by
    calc
      _ ≤ cφ i := hcφ i x
      _ ≤ max (cφ i) 0 := le_max_left _ _
      _ ≤ Mφ := by
        unfold Mφ
        exact Finset.single_le_sum
          (fun j _ => le_max_right _ _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  have hψbound (i : ℕ) (hi : i ≤ n) (x : Plane) :
      ‖iteratedFDeriv ℝ i ψ x‖ ≤ Mψ := by
    calc
      _ ≤ cψ i := hcψ i x
      _ ≤ max (cψ i) 0 := le_max_left _ _
      _ ≤ Mψ := by
        unfold Mψ
        exact Finset.single_le_sum
          (fun j _ => le_max_right _ _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  have hreflect (a x : Plane) (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i (fun z => ψ (a - z)) x‖ ≤ Mψ := by
    have hfun : (fun z : Plane => ψ (a - z)) =
        (fun z : Plane => ψ (a + z)) ∘ (LinearIsometryEquiv.neg ℝ) := by
      funext z
      simp [sub_eq_add_neg]
    have hnorm : ‖iteratedFDeriv ℝ i (fun z => ψ (a - z)) x‖ =
        ‖iteratedFDeriv ℝ i ψ (a - x)‖ := by
      rw [hfun]
      calc
        _ = ‖iteratedFDeriv ℝ i (fun z : Plane => ψ (a + z))
            ((LinearIsometryEquiv.neg ℝ) x)‖ :=
          (LinearIsometryEquiv.neg ℝ).norm_iteratedFDeriv_comp_right
            (fun z : Plane => ψ (a + z)) x i
        _ = ‖iteratedFDeriv ℝ i ψ (a + (LinearIsometryEquiv.neg ℝ) x)‖ := by
          rw [iteratedFDeriv_comp_add_left]
        _ = ‖iteratedFDeriv ℝ i ψ (a - x)‖ := by simp [sub_eq_add_neg]
    rw [hnorm]
    exact hψbound i hi (a - x)
  let B : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  let C : ℝ := ‖B.bilinearRestrictScalars ℝ‖ *
    ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Mφ * Mψ
  have hC : 0 ≤ C := by
    apply mul_nonneg (norm_nonneg _)
    exact Finset.sum_nonneg fun i _ => by positivity
  refine ⟨C, hC, fun a x => ?_⟩
  have hψa : ContDiff ℝ (⊤ : ℕ∞) (fun z : Plane => ψ (a - z)) :=
    ψ.contDiff.comp (contDiff_const.sub contDiff_id)
  have hprod := (B.bilinearRestrictScalars ℝ).norm_iteratedFDeriv_le_of_bilinear
    φ.contDiff hψa x (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  have hprod' :
      ‖iteratedFDeriv ℝ n (fun z => φ z * ψ (a - z)) x‖ ≤
        ‖B.bilinearRestrictScalars ℝ‖ *
          ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i φ x‖ *
            ‖iteratedFDeriv ℝ (n - i) (fun z => ψ (a - z)) x‖ := by
    simpa only [ContinuousLinearMap.bilinearRestrictScalars_apply_apply,
      B, ContinuousLinearMap.lsmul_apply, smul_eq_mul] using hprod
  calc
    _ ≤ ‖B.bilinearRestrictScalars ℝ‖ *
        ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i φ x‖ *
          ‖iteratedFDeriv ℝ (n - i) (fun z => ψ (a - z)) x‖ := hprod'
    _ ≤ C := by
      unfold C
      gcongr with i hi
      · exact hφbound i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) x
      · exact hreflect a x (n - i) (Nat.sub_le n i)

/-- The fixed compact support used by the directional-derivative test family. -/
def translatedDerivativeSupport (φ : TestFn) : Compacts Plane :=
  ⟨tsupport φ, φ.hasCompactSupport.isCompact⟩

/-- The derivative support carrier is the support of the original test function. -/
@[simp] theorem translatedDerivativeSupport_coe (φ : TestFn) :
    (translatedDerivativeSupport φ : Set Plane) = tsupport φ := rfl

/-- Joint smoothness of the differentiated translated kernel family. -/
private theorem contDiff_translatedDerivativeTestFamily_uncurry (φ ρ : TestFn) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun q : (Plane × Plane) × Plane => φ q.2 * fderiv ℝ ρ (q.1.1 - q.2) q.1.2) := by
  have hFderiv : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : Plane × Plane => fderiv ℝ ρ q.1) :=
    (ρ.contDiff.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).comp contDiff_fst
  have hd : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : Plane × Plane => fderiv ℝ ρ q.1 q.2) := hFderiv.clm_apply contDiff_snd
  have hc : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : (Plane × Plane) × Plane => (q.1.1 - q.2, q.1.2)) :=
    (contDiff_fst.fst.sub contDiff_snd).prodMk contDiff_fst.snd
  exact (φ.contDiff.comp contDiff_snd).mul (hd.comp hc)

/-- The test function obtained by differentiating the translated kernel in direction `v`. -/
def translatedDerivativeTestFamily (φ ρ : TestFn) (p : Plane × Plane) :
    ContDiffMapSupportedIn Plane ℝ ⊤ (translatedDerivativeSupport φ) := {
  toFun := fun x => φ x * fderiv ℝ ρ (p.1 - x) p.2
  contDiff' := by
    have hd0 : ContDiff ℝ (⊤ : ℕ∞) (fun z : Plane => fderiv ℝ ρ z p.2) :=
      (ρ.contDiff.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply
        (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Plane => p.2))
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun x : Plane => p.1 - x) :=
      contDiff_const.sub contDiff_id
    exact φ.contDiff.mul (hd0.comp hc)
  zero_on_compl' := by
    intro x hx
    rw [translatedDerivativeSupport_coe] at hx
    have hφ : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [hφ] }

/-- The differentiated test family is additive in its direction. -/
theorem translatedDerivativeTestFamily_add_direction (φ ρ : TestFn) (y v w : Plane) :
    translatedDerivativeTestFamily φ ρ (y, v + w) =
      translatedDerivativeTestFamily φ ρ (y, v) + translatedDerivativeTestFamily φ ρ (y, w) := by
  apply ContDiffMapSupportedIn.ext
  intro x
  change φ x * fderiv ℝ ρ (y - x) (v + w) =
    φ x * fderiv ℝ ρ (y - x) v + φ x * fderiv ℝ ρ (y - x) w
  rw [map_add]
  ring

/-- The differentiated test family is homogeneous in its direction. -/
theorem translatedDerivativeTestFamily_smul_direction (φ ρ : TestFn) (y : Plane)
    (c : ℝ) (v : Plane) :
    translatedDerivativeTestFamily φ ρ (y, c • v) =
      c • translatedDerivativeTestFamily φ ρ (y, v) := by
  apply ContDiffMapSupportedIn.ext
  intro x
  change φ x * fderiv ℝ ρ (y - x) (c • v) =
    c * (φ x * fderiv ℝ ρ (y - x) v)
  rw [map_smul]
  ring

/-- The distribution paired against the directional derivative of a translated kernel. -/
def translatedDistributionPairingDirectionalDerivative (T : Distr) (φ ρ : TestFn)
    (p : Plane × Plane) : ℝ :=
  T (TestFunction.ofSupportedIn (Set.subset_univ _)
    (translatedDerivativeTestFamily φ ρ p))

/-- The distributional directional-derivative candidate is additive in the direction. -/
theorem translatedDistributionPairingDirectionalDerivative_add_direction
    (T : Distr) (φ ρ : TestFn) (y v w : Plane) :
    translatedDistributionPairingDirectionalDerivative T φ ρ (y, v + w) =
      translatedDistributionPairingDirectionalDerivative T φ ρ (y, v) +
        translatedDistributionPairingDirectionalDerivative T φ ρ (y, w) := by
  change T (TestFunction.ofSupportedIn (Set.subset_univ _)
      (translatedDerivativeTestFamily φ ρ (y, v + w))) = _
  rw [translatedDerivativeTestFamily_add_direction]
  let A := translatedDerivativeTestFamily φ ρ (y, v)
  let B := translatedDerivativeTestFamily φ ρ (y, w)
  have hmap : TestFunction.ofSupportedIn (Set.subset_univ _) (A + B) =
      TestFunction.ofSupportedIn (Set.subset_univ _) A +
        TestFunction.ofSupportedIn (Set.subset_univ _) B :=
    (TestFunction.ofSupportedInCLM ℝ (Ω := ⊤) (K := translatedDerivativeSupport φ)
      (Set.subset_univ (translatedDerivativeSupport φ : Set Plane))).map_add A B
  rw [hmap, map_add]
  rfl

/-- The distributional directional-derivative candidate is homogeneous in the direction. -/
theorem translatedDistributionPairingDirectionalDerivative_smul_direction
    (T : Distr) (φ ρ : TestFn) (y : Plane) (c : ℝ) (v : Plane) :
    translatedDistributionPairingDirectionalDerivative T φ ρ (y, c • v) =
      c * translatedDistributionPairingDirectionalDerivative T φ ρ (y, v) := by
  change T (TestFunction.ofSupportedIn (Set.subset_univ _)
      (translatedDerivativeTestFamily φ ρ (y, c • v))) = _
  rw [translatedDerivativeTestFamily_smul_direction]
  let A := translatedDerivativeTestFamily φ ρ (y, v)
  have hmap : TestFunction.ofSupportedIn (Set.subset_univ _) (c • A) =
      c • TestFunction.ofSupportedIn (Set.subset_univ _) A :=
    (TestFunction.ofSupportedInCLM ℝ (Ω := ⊤) (K := translatedDerivativeSupport φ)
      (Set.subset_univ (translatedDerivativeSupport φ : Set Plane))).map_smul c A
  rw [hmap, map_smul, smul_eq_mul]
  rfl

/-- The directional-derivative pairing candidate depends continuously on both its point and
direction parameters. -/
theorem continuous_translatedDistributionPairingDirectionalDerivative
    (T : Distr) (φ ρ : TestFn) :
    Continuous (translatedDistributionPairingDirectionalDerivative T φ ρ) := by
  let K := translatedDerivativeSupport φ
  have hF : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : (Plane × Plane) × Plane => translatedDerivativeTestFamily φ ρ q.1 q.2) := by
    exact contDiff_translatedDerivativeTestFamily_uncurry φ ρ
  have hparam := continuous_supported_test_family K (translatedDerivativeTestFamily φ ρ) hF
  have hI : Continuous (fun f : ContDiffMapSupportedIn Plane ℝ ⊤ K =>
      TestFunction.ofSupportedIn (Set.subset_univ _) f) :=
    TestFunction.continuous_ofSupportedIn (F := ℝ) (n := ⊤)
      (show (K : Set Plane) ⊆ (⊤ : Opens Plane) from fun _ _ => trivial)
  exact T.continuous.comp (hI.comp hparam)

/-- At each translation point, the continuous directional-derivative candidate is a bundled
continuous linear map in the direction. -/
noncomputable def translatedDistributionPairingFDeriv (T : Distr) (φ ρ : TestFn) (y : Plane) :
    Plane →L[ℝ] ℝ := {
  toLinearMap := {
    toFun := fun v => translatedDistributionPairingDirectionalDerivative T φ ρ (y, v)
    map_add' := fun v w => translatedDistributionPairingDirectionalDerivative_add_direction
      T φ ρ y v w
    map_smul' := fun c v => by
      simpa only [smul_eq_mul, RingHom.id_apply] using
        translatedDistributionPairingDirectionalDerivative_smul_direction T φ ρ y c v }
  cont := by
    exact (continuous_translatedDistributionPairingDirectionalDerivative T φ ρ).comp
      (continuous_const.prodMk continuous_id) }

/-- The derivative of a translated distribution pairing evaluates to its directional derivative pairing. -/
@[simp] theorem translatedDistributionPairingFDeriv_apply (T : Distr) (φ ρ : TestFn)
    (y v : Plane) :
    translatedDistributionPairingFDeriv T φ ρ y v =
      translatedDistributionPairingDirectionalDerivative T φ ρ (y, v) := rfl

end Critical2DKPZ.Analysis.Sobolev

namespace Critical2DKPZ.Analysis.Sobolev

/-- The bundled directional derivative varies continuously in the translation point in operator
norm. Finite-dimensional coordinates reduce this to continuity on two basis directions. -/
theorem continuous_translatedDistributionPairingFDeriv (T : Distr) (φ ρ : TestFn) :
    Continuous (translatedDistributionPairingFDeriv T φ ρ) := by
  let e (i : Fin 2) : Plane := EuclideanSpace.single i (1 : ℝ)
  let a (i : Fin 2) (y : Plane) :=
    translatedDistributionPairingDirectionalDerivative T φ ρ (y, e i)
  let P (i : Fin 2) : Plane →L[ℝ] ℝ := EuclideanSpace.proj i
  let A (y : Plane) : Plane →L[ℝ] ℝ := ∑ i : Fin 2, a i y • P i
  have ha (i : Fin 2) : Continuous (a i) := by
    exact (continuous_translatedDistributionPairingDirectionalDerivative T φ ρ).comp
      (continuous_id.prodMk continuous_const)
  have hA : Continuous A := by
    change Continuous (fun y : Plane => ∑ i : Fin 2, a i y • P i)
    exact continuous_finsetSum Finset.univ (fun i _ => (ha i).smul continuous_const)
  have hAe (y : Plane) : A y = translatedDistributionPairingFDeriv T φ ρ y := by
    ext v
    have hv : v = ∑ i : Fin 2, v i • e i := by
      simpa [e] using (EuclideanSpace.basisFun (Fin 2) ℝ).sum_repr v |>.symm
    change (∑ i : Fin 2, a i y * v i) =
      translatedDistributionPairingDirectionalDerivative T φ ρ (y, v)
    calc
      (∑ i : Fin 2, a i y * v i) =
          ∑ i : Fin 2, translatedDistributionPairingFDeriv T φ ρ y (v i • e i) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [a, e, translatedDistributionPairingFDeriv_apply]
            ring
      _ = translatedDistributionPairingFDeriv T φ ρ y (∑ i : Fin 2, v i • e i) := by
            rw [map_sum]
      _ = translatedDistributionPairingDirectionalDerivative T φ ρ (y, v) := by
            rw [translatedDistributionPairingFDeriv_apply]
            conv_rhs => rw [hv]
  have hfun : (fun y => translatedDistributionPairingFDeriv T φ ρ y) = A := by
    funext y
    exact (hAe y).symm
  change Continuous (fun y => translatedDistributionPairingFDeriv T φ ρ y)
  rw [hfun]
  exact hA

end Critical2DKPZ.Analysis.Sobolev

namespace Critical2DKPZ.Analysis.Sobolev

/-- The directional derivative kernel along a line segment in the translation variable. -/
def translatedPairingPathDerivativeTestFamily (φ ρ : TestFn) (y v : Plane) (s : ℝ) :
    ContDiffMapSupportedIn Plane ℝ ⊤ (translatedDerivativeSupport φ) :=
  translatedDerivativeTestFamily φ ρ (y + s • v, v)

/-- The path derivative family is jointly smooth in its parameter and spatial variables. -/
theorem contDiff_translatedPairingPathDerivativeTestFamily (φ ρ : TestFn) (y v : Plane) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun q : ℝ × Plane => translatedPairingPathDerivativeTestFamily φ ρ y v q.1 q.2) := by
  have hFderiv : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Plane => fderiv ℝ ρ z) :=
    ρ.contDiff.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have hd : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Plane => fderiv ℝ ρ z v) :=
    hFderiv.clm_apply (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Plane => v))
  have hay : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : ℝ × Plane => y + q.1 • v) :=
    contDiff_const.add (contDiff_fst.smul contDiff_const)
  have ha : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : ℝ × Plane => y + q.1 • v - q.2) := hay.sub contDiff_snd
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun q : ℝ × Plane => φ q.2 * fderiv ℝ ρ (y + q.1 • v - q.2) v)
  exact (φ.contDiff.comp contDiff_snd).mul (hd.comp ha)

/-- Pointwise, the differentiated translated kernel integrates to the endpoint difference along
the unit line segment. -/
theorem translatedKernelPath_fundamentalTheorem (φ ρ : TestFn) (y v x : Plane) :
    φ x * ρ (y + v - x) - φ x * ρ (y - x) =
      ∫ s in (0 : ℝ)..1, φ x * fderiv ℝ ρ (y + s • v - x) v := by
  have hkernel : ContDiff ℝ (⊤ : ℕ∞) (fun z : Plane => fderiv ℝ ρ z v) :=
    (ρ.contDiff.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Plane => v))
  have hpath : Continuous (fun s : ℝ => y + s • v - x) := by fun_prop
  have hcont : Continuous (fun s : ℝ => φ x * fderiv ℝ ρ (y + s • v - x) v) :=
    continuous_const.mul (hkernel.continuous.comp hpath)
  have hint : IntervalIntegrable
      (fun s : ℝ => φ x * fderiv ℝ ρ (y + s • v - x) v) volume 0 1 :=
    hcont.intervalIntegrable 0 1
  have hderiv (s : ℝ) : HasDerivAt
      (fun r : ℝ => φ x * ρ (y + r • v - x))
      (φ x * fderiv ℝ ρ (y + s • v - x) v) s := by
    let L : ℝ →L[ℝ] Plane := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v
    have hsmul : HasDerivAt (fun r : ℝ => r • v) v s := by
      have hcomp := (L.hasFDerivAt : HasFDerivAt L L s).comp_hasDerivAt s
        (hasDerivAt_id s)
      convert hcomp using 1
      · ext r
        simp [L]
      · simp [L]
    have harg : HasDerivAt (fun r : ℝ => y + r • v - x) v s :=
      hsmul.const_add y |>.sub_const x
    have hρ : HasFDerivAt ρ (fderiv ℝ ρ (y + s • v - x)) (y + s • v - x) :=
      (ρ.contDiff.differentiable (by simp) (y + s • v - x)).hasFDerivAt
    have hcomp : HasDerivAt (fun r : ℝ => ρ (y + r • v - x))
        (fderiv ℝ ρ (y + s • v - x) v) s := by
      convert hρ.comp_hasDerivAt s harg using 1; rfl
    convert (hasDerivAt_const s (φ x)).mul hcomp using 1; ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (fun s _hs => hderiv s) hint
  calc
    φ x * ρ (y + v - x) - φ x * ρ (y - x) =
        (fun s : ℝ => φ x * ρ (y + s • v - x)) 1 -
          (fun s : ℝ => φ x * ρ (y + s • v - x)) 0 := by
            simp only [one_smul, zero_smul, add_zero]
    _ = ∫ s in (0 : ℝ)..1, φ x * fderiv ℝ ρ (y + s • v - x) v := hFTC.symm

/-- The translated distribution pairing satisfies the line-segment fundamental theorem of
calculus, with derivative given by pairing against the differentiated kernel. -/
theorem translatedDistributionPairing_sub_eq_intervalIntegral_directionalDerivative
    (T : Distr) (φ ρ : TestFn) (y v : Plane) :
    translatedDistributionPairing T φ ρ (y + v) - translatedDistributionPairing T φ ρ y =
      ∫ s in (0 : ℝ)..1,
        translatedDistributionPairingDirectionalDerivative T φ ρ (y + s • v, v) := by
  classical
  let K := translatedDerivativeSupport φ
  let ψv : TestFn := {
    toFun := fun z => fderiv ℝ ρ z v
    contDiff' := (ρ.contDiff.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Plane => v))
    hasCompactSupport' := ρ.hasCompactSupport.fderiv_apply ℝ v
    tsupport_subset' := fun _ _ => trivial }
  let F (s : ℝ) : ContDiffMapSupportedIn Plane ℝ ⊤ K :=
    translatedPairingPathDerivativeTestFamily φ ρ y v s
  let μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  have hF : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × Plane => F q.1 q.2) :=
    contDiff_translatedPairingPathDerivativeTestFamily φ ρ y v
  have hbound : ∀ n : ℕ, ∃ g : ℝ → ℝ, Integrable g μ ∧
      ∀ s x, ‖iteratedFDeriv ℝ n (F s) x‖ ≤ g s := by
    intro n
    obtain ⟨C, hC, hjet⟩ := exists_uniform_translated_product_jet_bound φ ψv n
    refine ⟨fun _ => C, ?_, fun s x => ?_⟩
    · exact integrableOn_const (μ := volume) (s := Set.Ioc (0 : ℝ) 1) (by simp)
    · change ‖iteratedFDeriv ℝ n
        (fun z : Plane => φ z * ψv (y + s • v - z)) x‖ ≤ C
      exact hjet (y + s • v) x
  let G (s : ℝ) : ContDiffMapSupportedIn Plane ℝ ⊤ K := {
    toFun := fun x => φ x * ρ (y + s • v - x)
    contDiff' := by
      have ha : ContDiff ℝ (⊤ : ℕ∞) (fun z : Plane => y + s • v - z) :=
        (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Plane => y + s • v)).sub
          contDiff_id
      exact φ.contDiff.mul (ρ.contDiff.comp ha)
    zero_on_compl' := by
      intro x hx
      rw [translatedDerivativeSupport_coe] at hx
      have hφ : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hφ] }
  let ψ : ContDiffMapSupportedIn Plane ℝ ⊤ K := G 1 - G 0
  have hpoint (x : Plane) : ψ x = ∫ s, F s x ∂μ := by
    have hGapply (s : ℝ) : G s x = φ x * ρ (y + s • v - x) := rfl
    have hFapply (s : ℝ) : F s x = φ x * fderiv ℝ ρ (y + s • v - x) v := rfl
    change G 1 x - G 0 x = _
    rw [hGapply, hGapply]
    rw [show (∫ s, F s x ∂μ) =
      ∫ s in (0 : ℝ)..1, φ x * fderiv ℝ ρ (y + s • v - x) v by
        rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        rfl]
    simpa only [one_smul, zero_smul, add_zero] using
      translatedKernelPath_fundamentalTheorem φ ρ y v x
  have hcomm := distribution_integral_smooth_test_family_of_parameter
    (P := ℝ) μ T K F hF hbound ψ hpoint
  have hψmap : TestFunction.ofSupportedIn (Ω := (⊤ : Opens Plane))
        (Set.subset_univ (K : Set Plane)) ψ =
      TestFunction.ofSupportedIn (Ω := (⊤ : Opens Plane))
          (Set.subset_univ (K : Set Plane)) (G 1) -
        TestFunction.ofSupportedIn (Ω := (⊤ : Opens Plane))
          (Set.subset_univ (K : Set Plane)) (G 0) := by
    change TestFunction.ofSupportedIn (Ω := (⊤ : Opens Plane))
      (Set.subset_univ (K : Set Plane)) (G 1 - G 0) = _
    exact (TestFunction.ofSupportedInCLM ℝ (Ω := ⊤) (K := K)
      (Set.subset_univ (K : Set Plane))).map_sub (G 1) (G 0)
  have hG1 : TestFunction.ofSupportedIn (Ω := (⊤ : Opens Plane))
        (Set.subset_univ (K : Set Plane)) (G 1) =
      TestFunction.ofSupportedIn (Ω := (⊤ : Opens Plane))
        (Set.subset_univ (compactTestSupport φ : Set Plane)) (translatedTestFamily φ ρ (y + v)) := by
    apply TestFunction.ext
    intro x
    change φ x * ρ (y + 1 • v - x) = φ x * ρ (y + v - x)
    simp only [one_smul]
  have hG0 : TestFunction.ofSupportedIn (Ω := (⊤ : Opens Plane))
        (Set.subset_univ (K : Set Plane)) (G 0) =
      TestFunction.ofSupportedIn (Ω := (⊤ : Opens Plane))
        (Set.subset_univ (compactTestSupport φ : Set Plane)) (translatedTestFamily φ ρ y) := by
    apply TestFunction.ext
    intro x
    change φ x * ρ (y + 0 • v - x) = φ x * ρ (y - x)
    simp only [zero_smul, add_zero]
  calc
    translatedDistributionPairing T φ ρ (y + v) - translatedDistributionPairing T φ ρ y
        = T (TestFunction.ofSupportedIn (Ω := (⊤ : Opens Plane))
            (Set.subset_univ (K : Set Plane)) ψ) := by
            rw [hψmap, hG1, hG0]
            rw [translatedDistributionPairing_apply, translatedDistributionPairing_apply]
            exact (map_sub T _ _).symm
    _ = ∫ s, T (TestFunction.ofSupportedIn (Ω := (⊤ : Opens Plane))
          (Set.subset_univ (K : Set Plane)) (F s)) ∂μ := hcomm
    _ = ∫ s in (0 : ℝ)..1,
          translatedDistributionPairingDirectionalDerivative T φ ρ (y + s • v, v) := by
            rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
            rfl

end Critical2DKPZ.Analysis.Sobolev

namespace Critical2DKPZ.Analysis.Sobolev

/-- The Fréchet remainder of the translated pairing is the integral of the change in its
directional-derivative operator along the segment. -/
theorem translatedDistributionPairing_remainder_eq_intervalIntegral
    (T : Distr) (φ ρ : TestFn) (y h : Plane) :
    translatedDistributionPairing T φ ρ (y + h) - translatedDistributionPairing T φ ρ y -
        translatedDistributionPairingFDeriv T φ ρ y h =
      ∫ t in (0 : ℝ)..1,
        (translatedDistributionPairingFDeriv T φ ρ (y + t • h) -
          translatedDistributionPairingFDeriv T φ ρ y) h := by
  have hDcont : Continuous
      (fun t : ℝ => translatedDistributionPairingDirectionalDerivative T φ ρ (y + t • h, h)) := by
    have hp : Continuous (fun t : ℝ => (y + t • h, h)) :=
      (continuous_const.add (continuous_id.smul continuous_const)).prodMk continuous_const
    exact (continuous_translatedDistributionPairingDirectionalDerivative T φ ρ).comp hp
  have hDint : IntervalIntegrable
      (fun t : ℝ => translatedDistributionPairingDirectionalDerivative T φ ρ (y + t • h, h))
      volume 0 1 := hDcont.intervalIntegrable 0 1
  have hcint : IntervalIntegrable
      (fun _ : ℝ => translatedDistributionPairingFDeriv T φ ρ y h) volume 0 1 :=
    continuous_const.intervalIntegrable 0 1
  calc
    translatedDistributionPairing T φ ρ (y + h) - translatedDistributionPairing T φ ρ y -
        translatedDistributionPairingFDeriv T φ ρ y h
        = (∫ t in (0 : ℝ)..1,
            translatedDistributionPairingDirectionalDerivative T φ ρ (y + t • h, h)) -
            ∫ t in (0 : ℝ)..1, translatedDistributionPairingFDeriv T φ ρ y h := by
              rw [translatedDistributionPairing_sub_eq_intervalIntegral_directionalDerivative]
              rw [intervalIntegral.integral_const]
              simp [translatedDistributionPairingFDeriv_apply]
    _ = ∫ t in (0 : ℝ)..1,
          translatedDistributionPairingDirectionalDerivative T φ ρ (y + t • h, h) -
            translatedDistributionPairingFDeriv T φ ρ y h :=
          (intervalIntegral.integral_sub hDint hcint).symm
    _ = ∫ t in (0 : ℝ)..1,
          (translatedDistributionPairingFDeriv T φ ρ (y + t • h) -
            translatedDistributionPairingFDeriv T φ ρ y) h := by
          congr 1

/-- The continuous directional-derivative candidate is the Fréchet derivative of the translated
distribution pairing. -/
theorem hasFDerivAt_translatedDistributionPairing (T : Distr) (φ ρ : TestFn) (y : Plane) :
    HasFDerivAt (translatedDistributionPairing T φ ρ)
      (translatedDistributionPairingFDeriv T φ ρ y) y := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  have hcontAt : ContinuousAt (translatedDistributionPairingFDeriv T φ ρ) y :=
    (continuous_translatedDistributionPairingFDeriv T φ ρ).continuousAt
  obtain ⟨δ, hδ, hclose⟩ :=
    (Metric.continuousAt_iff.mp hcontAt) ε hε
  filter_upwards [Metric.ball_mem_nhds (0 : Plane) hδ] with h hh
  have hhnorm : ‖h‖ < δ := by
    simpa [Metric.mem_ball] using hh
  have hbound (t : ℝ) (ht : t ∈ Set.uIoc (0 : ℝ) 1) :
      ‖(translatedDistributionPairingFDeriv T φ ρ (y + t • h) -
          translatedDistributionPairingFDeriv T φ ρ y) h‖ ≤ ε * ‖h‖ := by
    have ht' : t ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht
    have htNorm : ‖t‖ ≤ 1 := by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [ht'.1], ht'.2⟩
    have hnear : dist (y + t • h) y < δ := by
      rw [dist_eq_norm]
      have hsub : y + t • h - y = t • h := by abel
      rw [hsub, norm_smul]
      calc
        ‖t‖ * ‖h‖ ≤ 1 * ‖h‖ := mul_le_mul_of_nonneg_right htNorm (norm_nonneg _)
        _ = ‖h‖ := one_mul _
        _ < δ := hhnorm
    have hclose' := hclose hnear
    have hop :
        ‖translatedDistributionPairingFDeriv T φ ρ (y + t • h) -
          translatedDistributionPairingFDeriv T φ ρ y‖ < ε := by
      simpa only [dist_eq_norm] using hclose'
    calc
      _ ≤ ‖translatedDistributionPairingFDeriv T φ ρ (y + t • h) -
          translatedDistributionPairingFDeriv T φ ρ y‖ * ‖h‖ :=
            ContinuousLinearMap.le_opNorm _ _
      _ ≤ ε * ‖h‖ := mul_le_mul_of_nonneg_right hop.le (norm_nonneg _)
  rw [translatedDistributionPairing_remainder_eq_intervalIntegral]
  calc
    ‖∫ t in (0 : ℝ)..1,
        (translatedDistributionPairingFDeriv T φ ρ (y + t • h) -
          translatedDistributionPairingFDeriv T φ ρ y) h‖ ≤
      (ε * ‖h‖) * |(1 : ℝ) - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ = ε * ‖h‖ := by simp

/-- The translated pairing is continuously differentiable, with the continuous linear derivative
candidate proved above. -/
theorem contDiffOne_translatedDistributionPairing (T : Distr) (φ ρ : TestFn) :
    ContDiff ℝ 1 (translatedDistributionPairing T φ ρ) := by
  rw [contDiff_one_iff_hasFDerivAt]
  exact ⟨translatedDistributionPairingFDeriv T φ ρ,
    continuous_translatedDistributionPairingFDeriv T φ ρ,
    hasFDerivAt_translatedDistributionPairing T φ ρ⟩

end Critical2DKPZ.Analysis.Sobolev

end
