/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.FutureProfiles.DeterministicComparison
public import Critical2DKPZ.FutureProfiles.EndpointTailBounds
public import Critical2DKPZ.FutureProfiles.FreezingPast
public import Critical2DKPZ.FutureProfiles.HelperGeometry
public import Critical2DKPZ.FutureProfiles.OriginComparison
import Mathlib.Tactic

/-! # Weighted drift estimate for the endpoint origin comparison -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace Critical2DKPZ.FutureProfiles

open Critical2DKPZ.Blocks Critical2DKPZ.OnePoint Critical2DKPZ.Polymer

/-- If `B` equals the finite set `T`, the sum of `|q|` over `B` is at most `√|T|` times the `ℓ²`
norm of `q`. The `tsum` is a genuine finite sum, since the indicator is supported in `T`. -/
theorem tsum_indicator_abs_le_sqrt_card_mul_l2 (q : Site → ℝ) (B : Set Site)
    (T : Finset Site) (hBT : ∀ y ∈ B, y ∈ T) (hTB : ∀ y ∈ T, y ∈ B)
    (hqSq : Summable (fun y => q y ^ 2)) :
    ∑' y, B.indicator (fun y => |q y|) y ≤
      Real.sqrt (T.card : ℝ) * Real.sqrt (∑' y, q y ^ 2) := by
  have hlocal : (∑' y, B.indicator (fun y => |q y|) y) =
      ∑ y ∈ T, |q y| := by
    calc
      _ = ∑ y ∈ T, B.indicator (fun y => |q y|) y := by
        apply tsum_eq_sum
        intro y hy
        by_cases hyB : y ∈ B
        · exact (hy (hBT y hyB)).elim
        · simp [Set.indicator, hyB]
      _ = ∑ y ∈ T, |q y| := by
        apply Finset.sum_congr rfl
        intro y hy
        simp [Set.indicator, hTB y hy]
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt T (fun _ => (1 : ℝ)) (fun y => |q y|)
  have hcs' : (∑ y ∈ T, |q y|) ≤
      Real.sqrt (T.card : ℝ) * Real.sqrt (∑ y ∈ T, q y ^ 2) := by
    simpa [sq_abs] using hcs
  have hsum : (∑ y ∈ T, q y ^ 2) ≤ ∑' y, q y ^ 2 :=
    hqSq.sum_le_tsum T (fun y _ => sq_nonneg _)
  calc
    _ = ∑ y ∈ T, |q y| := hlocal
    _ ≤ Real.sqrt (T.card : ℝ) * Real.sqrt (∑ y ∈ T, q y ^ 2) := hcs'
    _ ≤ Real.sqrt (T.card : ℝ) * Real.sqrt (∑' y, q y ^ 2) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsum) (Real.sqrt_nonneg _)

/-- A site whose planar norm is at most `r` lies in the box of radius `⌈r⌉₊`. -/
theorem mem_boxSites_ceil_of_norm_le {y : Site} {r : ℝ}
    (hr0 : 0 ≤ r) (hy : ‖siteToPlane y‖ ≤ r) :
    y ∈ MomentBounds.boxSites ⌈r⌉₊ := by
  have hradSq := MomentBounds.latticeRadius_sq_le_norm_sq y
  have hnormSq : ‖siteToPlane y‖ ^ 2 ≤ r ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hr0).2 hy
  have hrad : (MomentBounds.latticeRadius y : ℝ) ≤ r :=
    (sq_le_sq₀ (Nat.cast_nonneg _) hr0).1 (hradSq.trans hnormSq)
  have hradceil : MomentBounds.latticeRadius y ≤ ⌈r⌉₊ := by
    exact_mod_cast hrad.trans (Nat.le_ceil r)
  have hcoord (a : ℤ) : (-(⌈r⌉₊ : ℤ) ≤ a ∧ a ≤ ⌈r⌉₊) ↔ a.natAbs ≤ ⌈r⌉₊ := by
    rw [← abs_le, ← Int.natCast_natAbs, Nat.cast_le]
  simp only [MomentBounds.boxSites, Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  have hnat : (y i).natAbs ≤ ⌈r⌉₊ := by
    fin_cases i
    · exact (le_max_left _ _).trans hradceil
    · exact (le_max_right _ _).trans hradceil
  exact (hcoord (y i)).2 hnat

/-- The convolution of finitely supported weights `ν` on `S` with the walk kernel `srwKernel d`. -/
def finiteWalkConvolution (d : ℕ) (S : Finset Site) (ν : Site → ℝ) : Site → ℝ :=
  fun y => ∑ w ∈ S, ν w * srwKernel d (y - w)

private def weightedTailConvolution (d : ℕ) (S : Finset Site)
    (ν : Disorder → Site → ℝ) (B : Set Site) : Disorder → ℝ :=
  fun ω => ∑' y, Bᶜ.indicator (fun y => ∑ w ∈ S, ν ω w * srwKernel d (y - w)) y

/-- The mean drift of the weighted profile comparison is controlled by its local squared
convolution energy and the smoothed endpoint tail. Integrability of the tail is supplied separately
by `integral_smoothedEndpointTailMass_le`. -/
theorem weighted_origin_drift_le (β : ℝ) (m n N : ℕ) (S : Finset Site)
    (U₀ U₁ η : Disorder → Site → ℝ) (G : Set Disorder) (f : Site → ℝ) (M R cE Cball : ℝ)
    (Ctail ctail Rcore : ℝ) (J : ℕ)
    (hCardBall : ∀ r : ℝ, 1 ≤ r →
      (((Critical2DKPZ.MomentBounds.boxSites ⌈r⌉₊).filter
        fun y => ‖siteToPlane y‖ ≤ r).card : ℝ) ≤ Cball * r ^ 2)
    (hnN : n ≤ N) (hN : 1 ≤ N) (hcE : 0 < cE) (hCball : 0 ≤ Cball)
    (hηsupport : ∀ ω y, y ∉ S → η ω y = 0)
    (hηbound : ∃ B : ℝ, ∀ ω y, |η ω y| ≤ B)
    (hηmeas : ∀ y, Measurable[disorderPast n] (η · y))
    (hU₁support : ∀ ω y, y ∉ S → U₁ ω y = 0)
    (hU₀mass : ∀ ω, ∑ y ∈ S, U₀ ω y = 1)
    (hU₁mass : ∀ ω, ∑ y ∈ S, U₁ ω y = 1)
    (hU₀nonneg : ∀ ω y, 0 ≤ U₀ ω y) (hU₁nonneg : ∀ ω y, 0 ≤ U₁ ω y)
    (hU₁eq : ∀ ω y, U₁ ω y = smoothedEndpointDist β m n 0 ω y)
    (hηdiff : ∀ ω y, η ω y = U₀ ω y - U₁ ω y)
    (hRootInt : IntegrableOn (fun ω => Real.sqrt (futureEnergy β n N (η ω))) G disorderLaw)
    (hRootBound : ∫ ω in G, Real.sqrt (futureEnergy β n N (η ω)) ∂disorderLaw ≤ Rcore / J)
    (hEnergy : ∀ ω, cE * (N : ℝ) *
      (∑' y, (finiteWalkConvolution (N - n) S (η ω) y) ^ 2) ≤
        futureEnergy β n N (η ω))
    (hTailInt : Integrable (smoothedEndpointTailMass β m n N R) disorderLaw)
    (hTailBound : ∫ ω, smoothedEndpointTailMass β m n N R ω ∂disorderLaw ≤
      Ctail * Real.exp (-ctail * R ^ 2))
    (hR : 1 ≤ R) (hf : ∀ y, |f y| ≤ M) :
    IntegrableOn (fun ω =>
      |∑' y, (finiteWalkConvolution (N - n) S (η ω) y) * f y|) G disorderLaw ∧
    ∫ ω in G, |∑' y, (finiteWalkConvolution (N - n) S (η ω) y) * f y| ∂disorderLaw ≤
      2 * M * ((Real.sqrt Cball * R / Real.sqrt cE) * (Rcore / J) +
        |Ctail| * Real.exp (-ctail * R ^ 2)) := by
  classical
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hf 0)
  let d : ℕ := N - n
  let r : ℝ := R * Real.sqrt N
  let B : Set Site := {y | ‖siteToPlane y‖ ≤ r}
  let T : Finset Site :=
    (Critical2DKPZ.MomentBounds.boxSites ⌈r⌉₊).filter fun y => ‖siteToPlane y‖ ≤ r
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hrge1 : 1 ≤ r := by
    dsimp [r]
    have hNsqrt : 1 ≤ Real.sqrt (N : ℝ) := by
      apply (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (Real.sqrt_nonneg _)).1
      rw [Real.sq_sqrt (by exact_mod_cast (show 0 ≤ N by omega))]
      exact_mod_cast hN
    exact one_le_mul_of_one_le_of_one_le hR hNsqrt
  have hTcard : (T.card : ℝ) ≤ Cball * r ^ 2 := by
    simpa [T] using hCardBall r hrge1
  have hBtoT : ∀ y ∈ B, y ∈ T := by
    intro y hy
    exact Finset.mem_filter.mpr ⟨mem_boxSites_ceil_of_norm_le hr0 hy, hy⟩
  have hTtoB : ∀ y ∈ T, y ∈ B := by
    intro y hy
    exact (Finset.mem_filter.mp hy).2
  let q : Disorder → Site → ℝ := fun ω => finiteWalkConvolution d S (η ω)
  have hqSqSummable (ω : Disorder) : Summable (fun y => q ω y ^ 2) := by
    apply summable_of_ne_finset_zero (s := S.biUnion fun w => Polymer.endpoints w d)
    intro y hy
    have hzero := walk_convolution_eq_zero_of_not_mem d S (η ω) y hy
    simp [q, finiteWalkConvolution, hzero]
  have hqHasSum₀ (ω : Disorder) : HasSum (finiteWalkConvolution d S (U₀ ω)) 1 := by
    change HasSum (fun y => ∑ w ∈ S, U₀ ω w * srwKernel d (y - w)) 1
    exact hasSum_walk_convolution_one d S (U₀ ω) (hU₀mass ω)
  have hqHasSum₁ (ω : Disorder) : HasSum (finiteWalkConvolution d S (U₁ ω)) 1 := by
    change HasSum (fun y => ∑ w ∈ S, U₁ ω w * srwKernel d (y - w)) 1
    exact hasSum_walk_convolution_one d S (U₁ ω) (hU₁mass ω)
  have hμ₀nonneg (ω y : _) : 0 ≤ finiteWalkConvolution d S (U₀ ω) y := by
    unfold finiteWalkConvolution
    apply Finset.sum_nonneg
    intro w hw
    exact mul_nonneg (hU₀nonneg ω w) (Polymer.kernel_nonneg d (y - w))
  have hμ₁nonneg (ω y : _) : 0 ≤ finiteWalkConvolution d S (U₁ ω) y := by
    unfold finiteWalkConvolution
    apply Finset.sum_nonneg
    intro w hw
    exact mul_nonneg (hU₁nonneg ω w) (Polymer.kernel_nonneg d (y - w))
  have hμdiff (ω y : _) :
      finiteWalkConvolution d S (U₀ ω) y - finiteWalkConvolution d S (U₁ ω) y = q ω y := by
    change (∑ w ∈ S, U₀ ω w * srwKernel d (y - w)) -
        (∑ w ∈ S, U₁ ω w * srwKernel d (y - w)) =
      ∑ w ∈ S, η ω w * srwKernel d (y - w)
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro w hw
    rw [hηdiff ω w]
    ring
  have hTlocal (ω : Disorder) :
      (∑' y, B.indicator (fun y => |q ω y|) y) ≤
        Real.sqrt (T.card : ℝ) * Real.sqrt (∑' y, q ω y ^ 2) :=
    tsum_indicator_abs_le_sqrt_card_mul_l2 (q ω) B T hBtoT hTtoB (hqSqSummable ω)
  have henergySq (ω : Disorder) :
      (∑' y, q ω y ^ 2) ≤ futureEnergy β n N (η ω) / (cE * (N : ℝ)) := by
    have hden : 0 < cE * (N : ℝ) := mul_pos hcE (by exact_mod_cast (show 0 < N by omega))
    apply (le_div_iff₀ hden).2
    calc
      (∑' y, q ω y ^ 2) * (cE * (N : ℝ)) =
          (cE * (N : ℝ)) * (∑' y, q ω y ^ 2) := by ring
      _ ≤ futureEnergy β n N (η ω) := by
        simpa [q, d] using hEnergy ω
  have hlocalBound (ω : Disorder) :
      (∑' y, B.indicator (fun y => |q ω y|) y) ≤
        (Real.sqrt Cball * R / Real.sqrt cE) *
          Real.sqrt (futureEnergy β n N (η ω)) := by
    have hE : 0 ≤ futureEnergy β n N (η ω) := futureEnergy_nonneg β n N (η ω)
    have hcardSqrt : Real.sqrt (T.card : ℝ) ≤ Real.sqrt (Cball * r ^ 2) :=
      Real.sqrt_le_sqrt hTcard
    have hqSqrt : Real.sqrt (∑' y, q ω y ^ 2) ≤
        Real.sqrt (futureEnergy β n N (η ω) / (cE * (N : ℝ))) :=
      Real.sqrt_le_sqrt (henergySq ω)
    calc
      _ ≤ Real.sqrt (T.card : ℝ) * Real.sqrt (∑' y, q ω y ^ 2) := hTlocal ω
      _ ≤ Real.sqrt (Cball * r ^ 2) *
          Real.sqrt (futureEnergy β n N (η ω) / (cE * (N : ℝ))) :=
        mul_le_mul hcardSqrt hqSqrt (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = (Real.sqrt Cball * R / Real.sqrt cE) *
          Real.sqrt (futureEnergy β n N (η ω)) := by
        rw [Real.sqrt_mul hCball, Real.sqrt_sq_eq_abs, abs_of_nonneg hr0,
          Real.sqrt_div' _ (le_of_lt (mul_pos hcE (by exact_mod_cast (show 0 < N by omega)))),
          Real.sqrt_mul hcE.le]
        have hsqrtN : 0 < Real.sqrt (N : ℝ) :=
          Real.sqrt_pos.2 (by exact_mod_cast (show 0 < N by omega))
        have hsqrct : 0 < Real.sqrt cE := Real.sqrt_pos.2 hcE
        dsimp [r]
        field_simp
  let localTerm : Disorder → ℝ := fun ω =>
    ∑ y ∈ T, |q ω y|
  have hlocalRep (ω : Disorder) :
      localTerm ω = ∑' y, B.indicator (fun y => |q ω y|) y := by
    symm
    calc
      _ = ∑ y ∈ T, B.indicator (fun y => |q ω y|) y := by
        apply tsum_eq_sum
        intro y hy
        by_cases hyB : y ∈ B
        · exact (hy (hBtoT y hyB)).elim
        · simp [Set.indicator, hyB]
      _ = localTerm ω := by
        dsimp [localTerm]
        apply Finset.sum_congr rfl
        intro y hy
        simp [Set.indicator, hTtoB y hy]
  have hqMeas (y : Site) : Measurable[disorderPast n] (q · y) := by
    dsimp [q, finiteWalkConvolution]
    exact Finset.measurable_sum _ fun w hw => (hηmeas w).mul_const _
  have hlocalMeasPast : Measurable[disorderPast n] localTerm := by
    dsimp [localTerm]
    fun_prop
  have hpast : disorderPast n ≤ (inferInstance : MeasurableSpace Disorder) := by
    rw [← Gaussian.disorderBlock_zero n]
    exact Gaussian.disorderBlock_le 0 n
  have hlocalMeas : Measurable localTerm := hlocalMeasPast.mono hpast le_rfl
  have hlocalInt : IntegrableOn localTerm G disorderLaw := by
    have hboundInt := hRootInt.const_mul (Real.sqrt Cball * R / Real.sqrt cE)
    refine hboundInt.mono' hlocalMeas.aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun y hy => abs_nonneg (q ω y))]
    calc
      localTerm ω = ∑' y, B.indicator (fun y => |q ω y|) y := hlocalRep ω
      _ ≤ (Real.sqrt Cball * R / Real.sqrt cE) *
          Real.sqrt (futureEnergy β n N (η ω)) := hlocalBound ω
  have hlocalIntegral :
      ∫ ω in G, localTerm ω ∂disorderLaw ≤
        (Real.sqrt Cball * R / Real.sqrt cE) * (Rcore / J) := by
    let κ : ℝ := Real.sqrt Cball * R / Real.sqrt cE
    have hκ : 0 ≤ κ := by dsimp [κ]; positivity
    calc
      _ ≤ ∫ ω in G, κ * Real.sqrt (futureEnergy β n N (η ω)) ∂disorderLaw :=
        integral_mono hlocalInt (hRootInt.const_mul κ)
          (fun ω => by
            calc
              localTerm ω = ∑' y, B.indicator (fun y => |q ω y|) y := hlocalRep ω
              _ ≤ κ * Real.sqrt (futureEnergy β n N (η ω)) := by
                simpa [κ] using hlocalBound ω)
      _ = κ * ∫ ω in G, Real.sqrt (futureEnergy β n N (η ω)) ∂disorderLaw := by
        rw [integral_const_mul]
      _ ≤ κ * (Rcore / J) := mul_le_mul_of_nonneg_left hRootBound hκ
      _ = (Real.sqrt Cball * R / Real.sqrt cE) * (Rcore / J) := by rfl
  let tailTerm : Disorder → ℝ := weightedTailConvolution d S U₁ B
  have hμ₁tsum (ω : Disorder) (y : Site) :
      finiteWalkConvolution d S (U₁ ω) y =
        ∑' w, U₁ ω w * srwKernel d (y - w) := by
    symm
    apply tsum_eq_sum
    intro w hw
    rw [hU₁support ω w hw, zero_mul]
  have htailEq (ω : Disorder) :
      tailTerm ω = smoothedEndpointTailMass β m n N R ω := by
    unfold tailTerm weightedTailConvolution smoothedEndpointTailMass
    apply tsum_congr
    intro y
    have hsmSupport (w : Site) (hw : w ∉ S) :
        smoothedEndpointDist β m n 0 ω w = 0 := by
      rw [← hU₁eq ω w]
      exact hU₁support ω w hw
    have hsmConv :
        (∑ w ∈ S, smoothedEndpointDist β m n 0 ω w * srwKernel (N - n) (y - w)) =
          ∑' w, smoothedEndpointDist β m n 0 ω w * srwKernel (N - n) (y - w) := by
      symm
      apply tsum_eq_sum
      intro w hw
      rw [hsmSupport w hw, zero_mul]
    by_cases hy : R * Real.sqrt N < ‖siteToPlane y‖ <;>
      simp [B, r, Set.indicator, hy, hsmConv, hU₁eq, d]
  have htailInt : Integrable tailTerm disorderLaw := by
    refine hTailInt.congr ?_
    exact Filter.Eventually.of_forall fun ω => (htailEq ω).symm
  have htailNonneg (ω : Disorder) : 0 ≤ tailTerm ω := by
    unfold tailTerm weightedTailConvolution
    apply tsum_nonneg
    intro y
    by_cases hy : y ∈ Bᶜ
    · simp [Set.indicator, hy]
      apply Finset.sum_nonneg
      intro w hw
      exact mul_nonneg (hU₁nonneg ω w) (Polymer.kernel_nonneg d (y - w))
    · simp [Set.indicator, hy]
  have htailIntegral :
      ∫ ω in G, tailTerm ω ∂disorderLaw ≤ Ctail * Real.exp (-ctail * R ^ 2) := by
    calc
      _ ≤ ∫ ω in Set.univ, tailTerm ω ∂disorderLaw :=
        setIntegral_mono_set htailInt.integrableOn
          (Filter.Eventually.of_forall htailNonneg)
          (Filter.Eventually.of_forall fun _ _ => Set.mem_univ _)
      _ = ∫ ω, tailTerm ω ∂disorderLaw := by simp
      _ = ∫ ω, smoothedEndpointTailMass β m n N R ω ∂disorderLaw := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall htailEq
      _ ≤ Ctail * Real.exp (-ctail * R ^ 2) := hTailBound
  let μ₀ : Disorder → Site → ℝ := fun ω => finiteWalkConvolution d S (U₀ ω)
  let μ₁ : Disorder → Site → ℝ := fun ω => finiteWalkConvolution d S (U₁ ω)
  have hμdiff (ω : Disorder) (y : Site) : μ₀ ω y - μ₁ ω y = q ω y := by
    exact hμdiff ω y
  have hμ₀sum (ω : Disorder) : HasSum (μ₀ ω) 1 := by
    simpa [μ₀] using hqHasSum₀ ω
  have hμ₁sum (ω : Disorder) : HasSum (μ₁ ω) 1 := by
    simpa [μ₁] using hqHasSum₁ ω
  have hμ₀nn (ω y : _) : 0 ≤ μ₀ ω y := hμ₀nonneg ω y
  have hμ₁nn (ω y : _) : 0 ≤ μ₁ ω y := hμ₁nonneg ω y
  let drift : Disorder → ℝ := fun ω =>
    |∑' y, q ω y * f y|
  have hdriftInt : IntegrableOn drift G disorderLaw := by
    -- This integrability is also part of the weighted-profile companion.
    let hcomp := integrableOn_abs_profileP2Fun_weighted_le β hnN η S
      hηsupport hηbound hηmeas f M hf G
    have hsumInt := hcomp.2
    have hrootScaled := hRootInt.const_mul M
    have hsumEq : (fun ω =>
        |∑' y, q ω y * f y| + M * Real.sqrt (futureEnergy β n N (η ω))) =
        (fun ω =>
          |∑' y, (∑ w ∈ S, η ω w * srwKernel (N - n) (y - w)) * f y| +
            M * Real.sqrt (futureEnergy β n N (η ω))) := by
      funext ω
      simp [q, finiteWalkConvolution, d]
    have hsumInt' : IntegrableOn (fun ω => drift ω +
        M * Real.sqrt (futureEnergy β n N (η ω))) G disorderLaw := by
      simpa [drift] using hsumEq ▸ hsumInt
    exact (integrable_add_iff_integrable_left' hrootScaled).1 hsumInt'
  have hdriftPoint (ω : Disorder) : drift ω ≤
      M * (2 * localTerm ω + 2 * tailTerm ω) := by
    have hprob := smoothed_l1_le_ball_add_tail (μ₀ ω) (μ₁ ω)
      (hμ₀nn ω) (hμ₁nn ω) (hμ₀sum ω) (hμ₁sum ω) B
    have hqNorm : Summable (fun y => |q ω y|) := (summable_walk_convolution d S (η ω)).abs
    have hqf : Summable (fun y => q ω y * f y) := by
      apply (hqNorm.mul_left M).of_norm_bounded
      intro y
      rw [Real.norm_eq_abs, abs_mul]
      calc
        |q ω y| * |f y| ≤ |q ω y| * M :=
          mul_le_mul_of_nonneg_left (hf y) (abs_nonneg _)
        _ = M * |q ω y| := by ring
    have htsumBound : |∑' y, q ω y * f y| ≤ M * ∑' y, |q ω y| := by
      calc
        _ = ‖∑' y, q ω y * f y‖ := by rw [Real.norm_eq_abs]
        _ ≤ ∑' y, ‖q ω y * f y‖ := norm_tsum_le_tsum_norm hqf.norm
        _ = ∑' y, |q ω y * f y| := by simp only [Real.norm_eq_abs]
        _ ≤ ∑' y, M * |q ω y| := hqf.norm.tsum_le_tsum (fun y => by
          rw [abs_mul]
          calc
            |q ω y| * |f y| ≤ |q ω y| * M :=
              mul_le_mul_of_nonneg_left (hf y) (abs_nonneg _)
            _ = M * |q ω y| := by ring)
            (hqNorm.mul_left M)
        _ = M * ∑' y, |q ω y| := by rw [tsum_mul_left]
    have hlocal :
        (∑' y, B.indicator (fun y => |μ₀ ω y - μ₁ ω y|) y) = localTerm ω := by
      rw [show (fun y => B.indicator (fun y => |μ₀ ω y - μ₁ ω y|) y) =
          (fun y => B.indicator (fun y => |q ω y|) y) from by
            funext y
            by_cases hy : y ∈ B <;> simp [Set.indicator, hy, hμdiff ω y]]
      exact (hlocalRep ω).symm
    have htotal : (∑' y, |μ₀ ω y - μ₁ ω y|) = ∑' y, |q ω y| := by
      apply tsum_congr
      intro y
      rw [hμdiff ω y]
    have htail :
        (∑' y, Bᶜ.indicator (μ₁ ω) y) = tailTerm ω := by
      unfold tailTerm weightedTailConvolution
      apply tsum_congr
      intro y
      change Bᶜ.indicator (finiteWalkConvolution d S (U₁ ω)) y =
        Bᶜ.indicator (fun z => ∑ w ∈ S, U₁ ω w * srwKernel d (z - w)) y
      rfl
    rw [hlocal, htail, htotal] at hprob
    exact htsumBound.trans (mul_le_mul_of_nonneg_left hprob hM)
  have hsumBoundInt : IntegrableOn
      (fun ω => (2 * M) * localTerm ω + (2 * M) * tailTerm ω) G disorderLaw :=
    (hlocalInt.const_mul (2 * M)).add (htailInt.integrableOn.const_mul (2 * M))
  have hdriftIntegral :
      ∫ ω in G, drift ω ∂disorderLaw ≤
        (2 * M) * (∫ ω in G, localTerm ω ∂disorderLaw) +
          (2 * M) * (∫ ω in G, tailTerm ω ∂disorderLaw) := by
    calc
      _ ≤ ∫ ω in G, (2 * M) * localTerm ω + (2 * M) * tailTerm ω ∂disorderLaw :=
        integral_mono hdriftInt hsumBoundInt
          (fun ω => by
            calc
              drift ω ≤ M * (2 * localTerm ω + 2 * tailTerm ω) := hdriftPoint ω
              _ = (2 * M) * localTerm ω + (2 * M) * tailTerm ω := by ring)
      _ = _ := by
        rw [integral_add (hlocalInt.const_mul (2 * M))
          (htailInt.integrableOn.const_mul (2 * M)), integral_const_mul, integral_const_mul]
  have hdriftFinal :
      ∫ ω in G, drift ω ∂disorderLaw ≤
        2 * M * ((Real.sqrt Cball * R / Real.sqrt cE) * (Rcore / J) +
          |Ctail| * Real.exp (-ctail * R ^ 2)) := by
    calc
      _ ≤ 2 * M * ((Real.sqrt Cball * R / Real.sqrt cE) * (Rcore / J) +
          Ctail * Real.exp (-ctail * R ^ 2)) := by
        calc
          _ ≤ (2 * M) * (∫ ω in G, localTerm ω ∂disorderLaw) +
              (2 * M) * (∫ ω in G, tailTerm ω ∂disorderLaw) := hdriftIntegral
          _ ≤ (2 * M) * (Real.sqrt Cball * R / Real.sqrt cE * (Rcore / J)) +
              (2 * M) * (Ctail * Real.exp (-ctail * R ^ 2)) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hlocalIntegral (by positivity))
              (mul_le_mul_of_nonneg_left htailIntegral (by positivity))
          _ = _ := by ring
      _ ≤ 2 * M * ((Real.sqrt Cball * R / Real.sqrt cE) * (Rcore / J) +
          |Ctail| * Real.exp (-ctail * R ^ 2)) := by
        apply mul_le_mul_of_nonneg_left
        · exact add_le_add le_rfl
            (mul_le_mul_of_nonneg_right (le_abs_self Ctail) (Real.exp_nonneg _))
        · positivity
  exact ⟨hdriftInt, hdriftFinal⟩

end Critical2DKPZ.FutureProfiles

end
