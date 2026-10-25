/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.FutureProfiles.ProfileLogTails
public import Critical2DKPZ.FutureProfiles.SmoothedEndpointProfile
public import Critical2DKPZ.OnePoint.OnePointInverseMomentComparison
public import Critical2DKPZ.Polymer.ChapmanKolmogorov
public import Critical2DKPZ.Polymer.ProfileCovariance
public import Critical2DKPZ.Polymer.WalkKernel
public import Critical2DKPZ.Smoothing.EndpointDistribution
public import Critical2DKPZ.MomentBounds.AiiKNormMGF
public import Critical2DKPZ.Polymer.ProbabilityProfiles
import Mathlib.Tactic

/-! # Gaussian tails for smoothed endpoint profiles -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open Critical2DKPZ.OnePoint

namespace Critical2DKPZ.FutureProfiles

private theorem integral_div_le_sqrt_mul_sqrt
    (Z D : Disorder → ℝ) (hZmeas : Measurable Z) (hDmeas : Measurable D)
    (hZint : Integrable Z disorderLaw) (hDinvint : Integrable (fun ω => (D ω)⁻¹) disorderLaw)
    (hZnonneg : ∀ ω, 0 ≤ Z ω) (hDpos : ∀ ω, 0 < D ω)
    (hZD : ∀ ω, Z ω ≤ D ω) :
    Integrable (fun ω => Z ω / D ω) disorderLaw ∧
      ∫ ω, Z ω / D ω ∂disorderLaw ≤
        Real.sqrt (∫ ω, Z ω ∂disorderLaw) *
          Real.sqrt (∫ ω, (D ω)⁻¹ ∂disorderLaw) := by
  let f : Disorder → ℝ := fun ω => Real.sqrt (Z ω)
  let g : Disorder → ℝ := fun ω => Real.sqrt ((D ω)⁻¹)
  have hfmeas : Measurable f := Real.continuous_sqrt.measurable.comp hZmeas
  have hgmeas : Measurable g := Real.continuous_sqrt.measurable.comp (hDmeas.inv)
  have hfsqEq : (fun ω => f ω ^ 2) = Z := by
    funext ω
    simp [f, Real.sq_sqrt (hZnonneg ω)]
  have hgsqEq : (fun ω => g ω ^ 2) = fun ω => (D ω)⁻¹ := by
    funext ω
    dsimp [g]
    rw [Real.sqrt_inv, inv_pow, Real.sq_sqrt (hDpos ω).le]
  have hfsq : Integrable (fun ω => f ω ^ 2) disorderLaw := by
    rw [hfsqEq]
    exact hZint
  have hgsq : Integrable (fun ω => g ω ^ 2) disorderLaw := by
    rw [hgsqEq]
    exact hDinvint
  have hfmem : MemLp f 2 disorderLaw :=
    (memLp_two_iff_integrable_sq hfmeas.aestronglyMeasurable).2 hfsq
  have hgmem : MemLp g 2 disorderLaw :=
    (memLp_two_iff_integrable_sq hgmeas.aestronglyMeasurable).2 hgsq
  have hfmem' : MemLp f (ENNReal.ofReal (2 : ℝ)) disorderLaw := by simpa using hfmem
  have hgmem' : MemLp g (ENNReal.ofReal (2 : ℝ)) disorderLaw := by simpa using hgmem
  have hfnn : ∀ᵐ ω ∂disorderLaw, 0 ≤ f ω :=
    Filter.Eventually.of_forall fun ω => Real.sqrt_nonneg _
  have hgnn : ∀ᵐ ω ∂disorderLaw, 0 ≤ g ω :=
    Filter.Eventually.of_forall fun ω => Real.sqrt_nonneg _
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := disorderLaw) (p := (2 : ℝ)) (q := (2 : ℝ)) Real.HolderConjugate.two_two
    hfnn hgnn hfmem' hgmem'
  have hprodint : Integrable (fun ω => f ω * g ω) disorderLaw := by
    have hpqENN : ENNReal.HolderTriple
        (ENNReal.ofReal (2 : ℝ)) (ENNReal.ofReal (2 : ℝ)) 1 :=
      Real.HolderConjugate.two_two.ennrealOfReal
    have hprodmem : MemLp (fun ω => g ω * f ω) 1 disorderLaw :=
      @MemLp.mul Disorder inferInstance ℝ inferInstance disorderLaw
        (ENNReal.ofReal (2 : ℝ)) (ENNReal.ofReal (2 : ℝ)) 1 f g hgmem' hfmem' hpqENN
    have hprodint' : Integrable (fun ω => g ω * f ω) disorderLaw :=
      hprodmem.integrable (by norm_num)
    simpa only [mul_comm] using hprodint'
  have hratioMeas : Measurable (fun ω => Z ω / D ω) := hZmeas.div hDmeas
  have hratioNonneg (ω : Disorder) : 0 ≤ Z ω / D ω :=
    div_nonneg (hZnonneg ω) (hDpos ω).le
  have hratioLeOne (ω : Disorder) : Z ω / D ω ≤ 1 :=
    (div_le_one (hDpos ω)).2 (hZD ω)
  have hprod_eq (ω : Disorder) : f ω * g ω = Real.sqrt (Z ω / D ω) := by
    dsimp [f, g]
    calc
      Real.sqrt (Z ω) * Real.sqrt ((D ω)⁻¹) =
          Real.sqrt (Z ω) * (Real.sqrt (D ω))⁻¹ := by rw [Real.sqrt_inv]
      _ = Real.sqrt (Z ω) / Real.sqrt (D ω) := by rw [div_eq_mul_inv]
      _ = Real.sqrt (Z ω / D ω) := (Real.sqrt_div' (Z ω) (hDpos ω).le).symm
  have hratioLe (ω : Disorder) : Z ω / D ω ≤ f ω * g ω := by
    rw [hprod_eq]
    apply (Real.le_sqrt (hratioNonneg ω) (hratioNonneg ω)).2
    have hmul := mul_nonneg (hratioNonneg ω) (sub_nonneg.mpr (hratioLeOne ω))
    nlinarith
  have hratioInt : Integrable (fun ω => Z ω / D ω) disorderLaw := by
    refine Integrable.mono' hprodint hratioMeas.aestronglyMeasurable ?_
    filter_upwards [ae_of_all disorderLaw hratioLe] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (hratioNonneg ω)]
    exact hω
  have hHolder' :
      ∫ ω, f ω * g ω ∂disorderLaw ≤
        Real.sqrt (∫ ω, f ω ^ 2 ∂disorderLaw) *
          Real.sqrt (∫ ω, g ω ^ 2 ∂disorderLaw) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    have hIf :
        (∫ ω, Real.rpow (f ω) (2 : ℝ) ∂disorderLaw) =
          ∫ ω, f ω ^ 2 ∂disorderLaw := by
      apply integral_congr_ae
      exact ae_of_all disorderLaw fun ω => Real.rpow_natCast (f ω) 2
    have hIg :
        (∫ ω, Real.rpow (g ω) (2 : ℝ) ∂disorderLaw) =
          ∫ ω, g ω ^ 2 ∂disorderLaw := by
      apply integral_congr_ae
      exact ae_of_all disorderLaw fun ω => Real.rpow_natCast (g ω) 2
    calc
      _ ≤ (∫ ω, Real.rpow (f ω) (2 : ℝ) ∂disorderLaw) ^ (1 / 2 : ℝ) *
            (∫ ω, Real.rpow (g ω) (2 : ℝ) ∂disorderLaw) ^ (1 / 2 : ℝ) := hHolder
      _ = _ := by rw [hIf, hIg]
  refine ⟨hratioInt, ?_⟩
  calc
    ∫ ω, Z ω / D ω ∂disorderLaw ≤ ∫ ω, f ω * g ω ∂disorderLaw :=
      integral_mono hratioInt hprodint hratioLe
    _ ≤ Real.sqrt (∫ ω, f ω ^ 2 ∂disorderLaw) *
          Real.sqrt (∫ ω, g ω ^ 2 ∂disorderLaw) := hHolder'
    _ = Real.sqrt (∫ ω, Z ω ∂disorderLaw) *
          Real.sqrt (∫ ω, (D ω)⁻¹ ∂disorderLaw) := by
      rw [hfsqEq, hgsqEq]

private theorem integral_inv_smoothedP2Plane_le_sq (β : ℝ) (hβ : 0 ≤ β)
    (m n : ℕ) :
    Integrable (fun ω => (smoothedP2Plane β m n 0 ω)⁻¹) disorderLaw ∧
      (∫ ω, (smoothedP2Plane β m n 0 ω)⁻¹ ∂disorderLaw) ≤
        ∫ ω, smoothedP2Plane β m n 0 ω ^ 2 ∂disorderLaw := by
  let ν : Site → ℝ := fun w => srwKernel m (w - 0)
  let S : Finset Site := Polymer.endpoints 0 m
  have hνS : ∀ w ∉ S, ν w = 0 := by
    intro w hw
    have h := Polymer.srwKernel_eq_zero_of_not_mem m 0 w (by simpa [S] using hw)
    simpa [ν] using h
  have hνnonneg : ∀ w, 0 ≤ ν w := fun w => Polymer.kernel_nonneg m (w - 0)
  have hνsum : ∑ w ∈ S, ν w = 1 := by
    simpa [ν, S] using Polymer.sum_srwKernel_endpoints m 0
  have hProfileInverseMomentInput := OnePoint.integral_rpow_neg_profileP2Fun_le (β := β)
    hβ m n ν S hνS hνnonneg hνsum (p := 1) (by norm_num)
  have hflat (ω : Disorder) :
      profileP2Fun β m n ν (fun _ => 1) ω = smoothedP2Plane β m n 0 ω := by
    dsimp [ν]
    exact Polymer.profileP2Fun_srw_flat β m n 0 ω
  have hexp : (1 : ℝ) * (1 + 1) / 2 = 1 := by norm_num
  have hbound :
      (∫ ω, (smoothedP2Plane β m n 0 ω)⁻¹ ∂disorderLaw) ≤
        ∫ ω, smoothedP2Plane β m n 0 ω ^ 2 ∂disorderLaw := by
    simpa only [hflat, Real.rpow_neg_one, Real.rpow_one, hexp] using hProfileInverseMomentInput
  have hinvint : Integrable (fun ω => smoothedP2Plane β m n 0 ω ^ (-1 : ℝ))
      disorderLaw := OnePoint.integrable_rpow_smoothedP2Plane β m n 0 (-1)
  have hinvint' : Integrable (fun ω => (smoothedP2Plane β m n 0 ω)⁻¹) disorderLaw := by
    simpa only [Real.rpow_neg_one] using hinvint
  exact ⟨hinvint', hbound⟩

/-- A Gaussian upper bound for the annealed simple random walk tail. -/
theorem exists_srwKernel_tail_le_gaussian_constant :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ (R : ℝ), 0 ≤ R → ∀ (N : ℕ), 1 ≤ N →
      (∑' y : Site,
        {y : Site | R * Real.sqrt N < ‖siteToPlane y‖}.indicator (fun _ => (1 : ℝ)) y *
          srwKernel N y) ≤ c * Real.exp (-R ^ 2 / (8 * c)) := by
  obtain ⟨c, hc, hmgf⟩ := Critical2DKPZ.MomentBounds.tsum_exp_mul_norm_srwKernel_le
  refine ⟨c, hc, ?_⟩
  intro R hR N hN
  have hNcast : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hsqrtN : 0 < Real.sqrt N := Real.sqrt_pos.2 hNcast
  let t : ℝ := R / (4 * c * Real.sqrt N)
  have ht : 0 ≤ t := by
    dsimp [t]
    positivity
  let S : Finset Site := Polymer.endpoints 0 N
  let B : Set Site := {y : Site | R * Real.sqrt N < ‖siteToPlane y‖}
  have htailSum :
      (∑' y : Site, B.indicator (fun _ => (1 : ℝ)) y * srwKernel N y) =
        ∑ y ∈ S, B.indicator (fun _ => (1 : ℝ)) y * srwKernel N y := by
    apply tsum_eq_sum
    intro y hy
    have hq := Polymer.srwKernel_eq_zero_of_not_mem N 0 y (by simpa [S] using hy)
    rw [show srwKernel N y = 0 by simpa only [sub_zero] using hq]
    simp
  have hmgfSum :
      (∑' y : Site, Real.exp (t * ‖siteToPlane y‖) * srwKernel N y) =
        ∑ y ∈ S, Real.exp (t * ‖siteToPlane y‖) * srwKernel N y := by
    apply tsum_eq_sum
    intro y hy
    have hq := Polymer.srwKernel_eq_zero_of_not_mem N 0 y (by simpa [S] using hy)
    rw [show srwKernel N y = 0 by simpa only [sub_zero] using hq]
    simp
  have hpoint (y : Site) (hy : y ∈ S) :
      B.indicator (fun _ => (1 : ℝ)) y * srwKernel N y ≤
        Real.exp (-t * (R * Real.sqrt N)) *
          (Real.exp (t * ‖siteToPlane y‖) * srwKernel N y) := by
    by_cases hyB : y ∈ B
    · have hexp : 0 ≤ -t * (R * Real.sqrt N) + t * ‖siteToPlane y‖ := by
        dsimp [B] at hyB
        have hgap : 0 ≤ ‖siteToPlane y‖ - R * Real.sqrt N :=
          sub_nonneg.mpr (le_of_lt hyB)
        have hprod := mul_nonneg ht hgap
        nlinarith
      rw [Set.indicator_of_mem hyB]
      have he : 1 ≤ Real.exp (-t * (R * Real.sqrt N)) *
          Real.exp (t * ‖siteToPlane y‖) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp hexp
      have hq : 0 ≤ srwKernel N y := Polymer.kernel_nonneg N y
      calc
        1 * srwKernel N y ≤ (Real.exp (-t * (R * Real.sqrt N)) *
              Real.exp (t * ‖siteToPlane y‖)) * srwKernel N y :=
          mul_le_mul_of_nonneg_right he hq
        _ = _ := by ring
    · simp [Set.indicator, hyB]
      exact mul_nonneg (Real.exp_nonneg _)
        (mul_nonneg (Real.exp_nonneg _) (Polymer.kernel_nonneg N y))
  have hfinite :
      (∑ y ∈ S, B.indicator (fun _ => (1 : ℝ)) y * srwKernel N y) ≤
        Real.exp (-t * (R * Real.sqrt N)) *
          ∑ y ∈ S, Real.exp (t * ‖siteToPlane y‖) * srwKernel N y := by
    calc
      _ ≤ ∑ y ∈ S,
          Real.exp (-t * (R * Real.sqrt N)) *
            (Real.exp (t * ‖siteToPlane y‖) * srwKernel N y) :=
        Finset.sum_le_sum fun y hy => hpoint y hy
      _ = _ := by rw [Finset.mul_sum]
  have hM := (hmgf t ht N).1
  rw [hmgfSum] at hM
  have hrootSq : (Real.sqrt N) ^ 2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
  have htR : t * R * Real.sqrt N = R ^ 2 / (4 * c) := by
    dsimp [t]
    field_simp
  have htSq : 2 * c * t ^ 2 * N = R ^ 2 / (8 * c) := by
    dsimp [t]
    field_simp
    nlinarith [hrootSq]
  have hexponent :
      -t * (R * Real.sqrt N) + 2 * c * t ^ 2 * N = -R ^ 2 / (8 * c) := by
    have hleft : t * (R * Real.sqrt N) = R ^ 2 / (4 * c) := by
      nlinarith [htR]
    calc
      _ = -(R ^ 2 / (4 * c)) + R ^ 2 / (8 * c) := by nlinarith [hleft, htSq]
      _ = _ := by ring
  calc
    _ = ∑ y ∈ S, B.indicator (fun _ => (1 : ℝ)) y * srwKernel N y := htailSum
    _ ≤ Real.exp (-t * (R * Real.sqrt N)) *
          ∑ y ∈ S, Real.exp (t * ‖siteToPlane y‖) * srwKernel N y := hfinite
    _ ≤ Real.exp (-t * (R * Real.sqrt N)) *
          (c * Real.exp (2 * c * t ^ 2 * N)) :=
        mul_le_mul_of_nonneg_left hM (Real.exp_nonneg _)
    _ = c * Real.exp (-R ^ 2 / (8 * c)) := by
      calc
        _ = c * (Real.exp (-t * (R * Real.sqrt N)) *
            Real.exp (2 * c * t ^ 2 * N)) := by ring
        _ = c * Real.exp (-t * (R * Real.sqrt N) + 2 * c * t ^ 2 * N) := by
          rw [← Real.exp_add]
        _ = _ := by rw [hexponent]

private def endpointTailWeight (R : ℝ) (N k : ℕ) (z : Site) : ℝ :=
  ∑' y : Site,
    {y : Site | R * Real.sqrt N < ‖siteToPlane y‖}.indicator (fun _ => (1 : ℝ)) y *
      srwKernel k (y - z)

private theorem endpointTailWeight_bounds (R : ℝ) (N k : ℕ) (z : Site) :
    0 ≤ endpointTailWeight R N k z ∧ endpointTailWeight R N k z ≤ 1 := by
  classical
  let S := Polymer.endpoints z k
  let B := {y : Site | R * Real.sqrt N < ‖siteToPlane y‖}
  have htail :
      endpointTailWeight R N k z =
        ∑ y ∈ S, B.indicator (fun _ => (1 : ℝ)) y * srwKernel k (y - z) := by
    unfold endpointTailWeight
    apply tsum_eq_sum
    intro y hy
    rw [Polymer.srwKernel_eq_zero_of_not_mem k z y (by simpa [S] using hy)]
    simp
  constructor
  · rw [htail]
    exact Finset.sum_nonneg fun y hy => mul_nonneg
      (by by_cases hyB : y ∈ B <;> simp [Set.indicator, hyB])
      (Polymer.kernel_nonneg k (y - z))
  · rw [htail]
    calc
      _ ≤ ∑ y ∈ S, srwKernel k (y - z) := by
        apply Finset.sum_le_sum
        intro y hy
        by_cases hyB : y ∈ B <;> simp [Set.indicator, hyB]
        exact Polymer.kernel_nonneg k (y - z)
      _ = 1 := Polymer.sum_srwKernel_endpoints k z

private theorem srwKernel_twoStage_tail (R : ℝ) (N p k : ℕ) (x : Site) :
    (∑' z : Site, srwKernel p (z - x) * endpointTailWeight R N k z) =
      ∑' y : Site,
        {y : Site | R * Real.sqrt N < ‖siteToPlane y‖}.indicator (fun _ => (1 : ℝ)) y *
          srwKernel (p + k) (y - x) := by
  classical
  let S := Polymer.endpoints x p
  let T := S.biUnion (fun z => Polymer.endpoints z k)
  let B := {y : Site | R * Real.sqrt N < ‖siteToPlane y‖}
  let F : Site → Site → ℝ := fun z y =>
    srwKernel p (z - x) * (B.indicator (fun _ => (1 : ℝ)) y * srwKernel k (y - z))
  have hdouble : Summable (Function.uncurry F) := by
    apply summable_of_ne_finset_zero (s := S ×ˢ T)
    intro q hq
    rcases q with ⟨z, y⟩
    simp only [Finset.mem_product] at hq
    by_cases hz : z ∈ S
    · have hyT : y ∉ T := fun hyT => hq ⟨hz, hyT⟩
      have hyK : y ∉ Polymer.endpoints z k := by
        intro hyK
        exact hyT (Finset.mem_biUnion.mpr ⟨z, hz, hyK⟩)
      have hqk := Polymer.srwKernel_eq_zero_of_not_mem k z y hyK
      simp [F, hqk]
    · have hqp := Polymer.srwKernel_eq_zero_of_not_mem p x z hz
      simp [F, hqp]
  calc
    _ = ∑' z, ∑' y, F z y := by
      apply tsum_congr
      intro z
      dsimp [F, endpointTailWeight]
      rw [← tsum_mul_left]
    _ = ∑' y, ∑' z, F z y :=
      (Summable.tsum_comm (f := F) hdouble).symm
    _ = _ := by
      apply tsum_congr
      intro y
      dsimp [F, B]
      calc
        _ = ∑' z, ({y : Site | R * Real.sqrt N < ‖siteToPlane y‖}.indicator
              (fun _ => (1 : ℝ)) y) *
                (srwKernel p (z - x) * srwKernel k (y - z)) := by
            apply tsum_congr
            intro z
            ring
        _ = _ := by
          rw [tsum_mul_left, Polymer.srwKernel_convolution p k x y]

/-! The smoothed endpoint law mass outside the ball of radius `R * sqrt N`. -/
/-- The smoothed endpoint tail mass is the endpoint probability beyond the specified diffusive radius after further walk evolution. -/
def smoothedEndpointTailMass (β : ℝ) (m n N : ℕ) (R : ℝ)
    (ω : Disorder) : ℝ :=
  ∑' y : Site,
    {y : Site | R * Real.sqrt N < ‖siteToPlane y‖}.indicator (fun _ => (1 : ℝ)) y *
      ∑' w, smoothedEndpointDist β m n 0 ω w * srwKernel (N - n) (y - w)

/-- An integral bound for the smoothed endpoint tail mass. The first conjunct supplies the
integrability needed to interpret the bound. -/
theorem integral_smoothedEndpointTailMass_le
    (β : ℝ) (hβ : 0 ≤ β) (m n N : ℕ) (hmn : m ≤ n) (hnN : n ≤ N)
    (R : ℝ) (cwalk : ℝ) (hcwalk : 1 ≤ cwalk)
    (hwalk : (∑' y : Site,
      {y : Site | R * Real.sqrt N < ‖siteToPlane y‖}.indicator (fun _ => (1 : ℝ)) y *
        srwKernel N y) ≤ cwalk * Real.exp (-R ^ 2 / (8 * cwalk)))
    (M : ℝ) (_hM : 0 ≤ M)
    (hDinv : ∫ ω, (smoothedP2Plane β m n 0 ω)⁻¹ ∂disorderLaw ≤ M) :
    Integrable (smoothedEndpointTailMass β m n N R) disorderLaw ∧
      ∫ ω, smoothedEndpointTailMass β m n N R ω ∂disorderLaw ≤
        Real.sqrt cwalk * Real.sqrt M * Real.exp (-R ^ 2 / (16 * cwalk)) := by
  classical
  let ν : Site → ℝ := fun w => srwKernel m (w - 0)
  let S : Finset Site := Polymer.endpoints 0 m
  let D : Disorder → ℝ := smoothedP2Plane β m n 0
  let Z : Disorder → ℝ := profileP2Fun β m n ν
    (endpointTailWeight R N (N - n))
  let Support : Finset Site := S.biUnion (fun y => Polymer.endpoints y (n - m))
  let OutSupport : Finset Site := Support.biUnion (fun w => Polymer.endpoints w (N - n))
  let B : Set Site := {y : Site | R * Real.sqrt N < ‖siteToPlane y‖}
  have hνzero : ∀ w ∉ S, ν w = 0 := by
    intro w hw
    have h := Polymer.srwKernel_eq_zero_of_not_mem m 0 w (by simpa [S] using hw)
    simpa [ν] using h
  have hνnonneg : ∀ w, 0 ≤ ν w := fun w => Polymer.kernel_nonneg m (w - 0)
  have hνsum : ∑' w, ν w = 1 := by
    simpa [ν, sub_zero] using Polymer.tsum_srwKernel m 0
  have hKnonneg (w : Site) : 0 ≤ endpointTailWeight R N (N - n) w :=
    (endpointTailWeight_bounds R N (N - n) w).1
  have hKle (w : Site) : endpointTailWeight R N (N - n) w ≤ 1 :=
    (endpointTailWeight_bounds R N (N - n) w).2
  have hKabs : ∀ w, |endpointTailWeight R N (N - n) w| ≤ 1 := by
    intro w
    rw [abs_of_nonneg (hKnonneg w)]
    exact hKle w
  have hDpos (ω : Disorder) : 0 < D ω := by
    dsimp [D]
    exact Polymer.smoothedP2Plane_pos β m n 0 ω
  have hDmeas : Measurable D := by
    dsimp [D]
    exact Polymer.measurable_smoothedP2Plane β m n 0
  have hZmeas : Measurable Z := by
    dsimp [Z]
    exact Polymer.measurable_profileP2Fun β m n ν (endpointTailWeight R N (N - n))
  have hZmem : MemLp Z 1 disorderLaw := by
    dsimp [Z]
    exact Polymer.memLp_profile_probability β m n ν
      (endpointTailWeight R N (N - n)) hνnonneg hνsum
      1 (by norm_num) hKabs 1 (by simp)
  have hZint : Integrable Z disorderLaw := memLp_one_iff_integrable.mp hZmem
  have hZnonneg (ω : Disorder) : 0 ≤ Z ω := by
    dsimp [Z]
    rw [Polymer.profileP2Fun_eq_sum β m n ν (endpointTailWeight R N (N - n))
      S hνzero ω]
    apply Finset.sum_nonneg
    intro w hw
    apply mul_nonneg (hνnonneg w)
    apply tsum_nonneg
    intro y
    exact mul_nonneg (Polymer.pointToPoint_nonneg β m (n - m) w y ω)
      (hKnonneg y)
  have hZexpand (ω : Disorder) :
      Z ω = ∑ w ∈ S, ν w *
        ∑' z, pointToPoint β m (n - m) w z ω * endpointTailWeight R N (N - n) z := by
    dsimp [Z]
    exact Polymer.profileP2Fun_eq_sum β m n ν (endpointTailWeight R N (N - n))
      S hνzero ω
  have hDexpand (ω : Disorder) : D ω =
      ∑ w ∈ S, ν w * pointToPlane β m (n - m) w ω := by
    have hflat : profileP2Fun β m n ν (fun _ => 1) ω = D ω := by
      dsimp [ν, D]
      exact Polymer.profileP2Fun_srw_flat β m n 0 ω
    rw [← hflat, Polymer.profileP2Fun_eq_sum β m n ν (fun _ => 1) S hνzero ω]
    simp only [mul_one, Polymer.tsum_pointToPoint]
  have htermLe (w : Site) (ω : Disorder) :
      (∑' z, pointToPoint β m (n - m) w z ω * endpointTailWeight R N (N - n) z) ≤
        pointToPlane β m (n - m) w ω := by
    have habs := Polymer.terminalProfile_abs_le β m (n - m) w
      (endpointTailWeight R N (N - n)) 1 hKabs ω
    calc
      _ ≤ |∑' z, pointToPoint β m (n - m) w z ω *
          endpointTailWeight R N (N - n) z| := le_abs_self _
      _ ≤ pointToPlane β m (n - m) w ω := by simpa using habs
  have hZD (ω : Disorder) : Z ω ≤ D ω := by
    rw [hZexpand ω, hDexpand ω]
    apply Finset.sum_le_sum
    intro w hw
    exact mul_le_mul_of_nonneg_left (htermLe w ω) (hνnonneg w)
  have hInv := integral_inv_smoothedP2Plane_le_sq β hβ m n
  have hCS := integral_div_le_sqrt_mul_sqrt Z D hZmeas hDmeas hZint hInv.1
    hZnonneg hDpos hZD
  have hmuSupport (ω : Disorder) (w : Site) (hw : w ∉ Support) :
      smoothedEndpointDist β m n 0 ω w = 0 := by
    dsimp [Support] at *
    exact Smoothing.smoothedEndpointDist_eq_zero_of_not_mem β 0 w ω (by simpa using hw)
  have hdouble (ω : Disorder) : Summable (Function.uncurry (fun w y =>
      smoothedEndpointDist β m n 0 ω w *
        (B.indicator (fun _ => (1 : ℝ)) y * srwKernel (N - n) (y - w)))) := by
    apply summable_of_ne_finset_zero (s := Support ×ˢ OutSupport)
    intro q hq
    rcases q with ⟨w, y⟩
    simp only [Finset.mem_product] at hq
    by_cases hw : w ∈ Support
    · have hyOut : y ∉ OutSupport := fun hyOut => hq ⟨hw, hyOut⟩
      have hyKernel : y ∉ Polymer.endpoints w (N - n) := by
        intro hyKernel
        exact hyOut (Finset.mem_biUnion.mpr ⟨w, hw, hyKernel⟩)
      have hqKernel := Polymer.srwKernel_eq_zero_of_not_mem (N - n) w y hyKernel
      simp [hqKernel]
    · simp [hmuSupport ω w hw]
  have hI (ω : Disorder) : smoothedEndpointTailMass β m n N R ω =
      ∑' w, smoothedEndpointDist β m n 0 ω w * endpointTailWeight R N (N - n) w := by
    let μω : Site → ℝ := smoothedEndpointDist β m n 0 ω
    let F : Site → Site → ℝ := fun w y =>
      μω w * (B.indicator (fun _ => (1 : ℝ)) y * srwKernel (N - n) (y - w))
    calc
      _ = ∑' y, ∑' w, μω w *
          (B.indicator (fun _ => (1 : ℝ)) y * srwKernel (N - n) (y - w)) := by
        unfold smoothedEndpointTailMass
        apply tsum_congr
        intro y
        rw [← tsum_mul_left]
        apply tsum_congr
        intro w
        ring
      _ = ∑' w, ∑' y, μω w *
          (B.indicator (fun _ => (1 : ℝ)) y * srwKernel (N - n) (y - w)) :=
        (Summable.tsum_comm (f := fun w y =>
          μω w * (B.indicator (fun _ => (1 : ℝ)) y * srwKernel (N - n) (y - w)))
            (hdouble ω))
      _ = _ := by
        apply tsum_congr
        intro w
        dsimp [endpointTailWeight]
        exact tsum_mul_left
  have hself (ω : Disorder) :
      profileP2Fun β n n (smoothedEndpointDist β m n 0 ω)
        (endpointTailWeight R N (N - n)) ω =
        ∑' w, smoothedEndpointDist β m n 0 ω w * endpointTailWeight R N (N - n) w := by
    simp [profileP2Fun, Polymer.pointToPoint_zero]
  have hIprofile (ω : Disorder) :
      smoothedEndpointTailMass β m n N R ω =
      profileP2Fun β n n (smoothedEndpointDist β m n 0 ω)
          (endpointTailWeight R N (N - n)) ω := by
    rw [hI ω, hself ω]
  have hCK (ω : Disorder) :
      Z ω = D ω * profileP2Fun β n n (smoothedEndpointDist β m n 0 ω)
          (endpointTailWeight R N (N - n)) ω := by
    have h := Smoothing.profileP2Fun_srwKernel_eq_mul β hmn (Nat.le_refl n)
      0 (endpointTailWeight R N (N - n)) ω
    simpa [Z, D, ν] using h
  have hratio (ω : Disorder) :
      smoothedEndpointTailMass β m n N R ω = Z ω / D ω := by
    rw [hIprofile ω, hCK ω]
    field_simp [ne_of_gt (hDpos ω)]
  have hZmean :
      (∫ ω, Z ω ∂disorderLaw) =
        ∑ w ∈ S, ν w *
          ∑' z, srwKernel (n - m) (z - w) * endpointTailWeight R N (N - n) z := by
    dsimp [Z]
    exact Polymer.integral_profileP2Fun_finset β m n ν
      (endpointTailWeight R N (N - n)) S hνzero
  have hfirst (w : Site) :
      (∑' z, srwKernel (n - m) (z - w) * endpointTailWeight R N (N - n) z) =
        endpointTailWeight R N (N - m) w := by
    have htime : (n - m) + (N - n) = N - m := by omega
    simpa [endpointTailWeight, htime] using
      srwKernel_twoStage_tail R N (n - m) (N - n) w
  have hsecond :
      (∑' w, ν w * endpointTailWeight R N (N - m) w) =
        ∑' y, B.indicator (fun _ => (1 : ℝ)) y * srwKernel N y := by
    have htime : m + (N - m) = N := Nat.add_sub_of_le (le_trans hmn hnN)
    simpa [ν, endpointTailWeight, sub_zero, htime] using
      srwKernel_twoStage_tail R N m (N - m) 0
  have hZmeanTail :
      (∫ ω, Z ω ∂disorderLaw) =
        ∑' y, B.indicator (fun _ => (1 : ℝ)) y * srwKernel N y := by
    rw [hZmean]
    calc
      _ = ∑ w ∈ S, ν w * endpointTailWeight R N (N - m) w := by
        apply Finset.sum_congr rfl
        intro w hw
        rw [hfirst w]
      _ = ∑' w, ν w * endpointTailWeight R N (N - m) w := by
        symm
        apply tsum_eq_sum
        intro w hw
        rw [hνzero w hw, zero_mul]
      _ = _ := hsecond
  have hZbound :
      ∫ ω, Z ω ∂disorderLaw ≤ cwalk * Real.exp (-R ^ 2 / (8 * cwalk)) := by
    rw [hZmeanTail]
    exact hwalk
  have hmassInt : Integrable (smoothedEndpointTailMass β m n N R) disorderLaw := by
    rw [show smoothedEndpointTailMass β m n N R = fun ω => Z ω / D ω from funext hratio]
    exact hCS.1
  have hmassBound :
      ∫ ω, smoothedEndpointTailMass β m n N R ω ∂disorderLaw ≤
        Real.sqrt cwalk * Real.sqrt M * Real.exp (-R ^ 2 / (16 * cwalk)) := by
    rw [show smoothedEndpointTailMass β m n N R = fun ω => Z ω / D ω from funext hratio]
    calc
      _ ≤ Real.sqrt (∫ ω, Z ω ∂disorderLaw) *
          Real.sqrt (∫ ω, (D ω)⁻¹ ∂disorderLaw) := hCS.2
      _ ≤ Real.sqrt (cwalk * Real.exp (-R ^ 2 / (8 * cwalk))) * Real.sqrt M := by
        gcongr
      _ = Real.sqrt cwalk * Real.sqrt M * Real.exp (-R ^ 2 / (16 * cwalk)) := by
        have hcwalk0 : 0 ≤ cwalk := le_trans (by norm_num) hcwalk
        have hsqrtExp : Real.sqrt (Real.exp (-R ^ 2 / (8 * cwalk))) =
            Real.exp (-R ^ 2 / (16 * cwalk)) := by
          rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
          congr 1
          ring
        rw [Real.sqrt_mul hcwalk0, hsqrtExp]
        ring
  exact ⟨hmassInt, hmassBound⟩

/-- The inverse smoothed partition function has uniformly bounded expectation for small smoothing scales and critical parameters in a compact interval. -/
theorem smoothedEndpoint_inverseMoment_smallDelta (A : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ δ : ℝ, 0 < δ → δ < 1 / 256 →
      ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A,
        1 ≤ N ∧ evenCeil (δ * N) ≤ evenCeil (Real.sqrt δ * N) ∧
        evenCeil (Real.sqrt δ * N) ≤ N ∧
        (∫ ω, (smoothedP2Plane (criticalBeta ϑ N) (evenCeil (δ * N))
          (evenCeil (Real.sqrt δ * N)) 0 ω)⁻¹ ∂disorderLaw) ≤ M := by
  obtain ⟨C₂, hC₂⟩ := OnePoint.smoothedP2Plane_secondMoment_le_uniform A 1
  obtain ⟨C_R, hC_R⟩ := OnePoint.replicaOverlap_sub_log_bounded
  have hCR : 0 ≤ C_R := by
    have h := hC_R 0 0 (by omega)
    simpa using h
  have hlog9 : 0 < Real.log 9 := Real.log_pos (by norm_num)
  let K : ℝ := (2 + C_R / Real.log 9) / Real.pi
  let M : ℝ := 1 + |C₂| * K
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨M, hM, ?_⟩
  intro δ hδ hδsmall
  have hδlt1 : δ < 1 := by norm_num at hδsmall ⊢; linarith
  have hrootpos : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hrootlt : Real.sqrt δ < 1 / 16 := by
    have hrootlt' : Real.sqrt δ < Real.sqrt (1 / 256 : ℝ) :=
      (Real.sqrt_lt_sqrt_iff hδ.le).2 hδsmall
    have hsqrt : Real.sqrt (1 / 256 : ℝ) = 1 / 16 := by norm_num
    rw [hsqrt] at hrootlt'
    exact hrootlt'
  have hx : 16 < 1 / Real.sqrt δ := by
    rw [lt_div_iff₀ hrootpos]
    nlinarith
  have hδsqrt : δ ≤ Real.sqrt δ := by
    exact (Real.le_sqrt hδ.le hδ.le).2 (by nlinarith [hδlt1])
  have hδN : ∀ᶠ N : ℕ in atTop, 1 ≤ δ * (N : ℝ) :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop hδ).eventually_ge_atTop 1
  have hrootN : ∀ᶠ N : ℕ in atTop,
      2 ≤ Real.sqrt δ * (N : ℝ) :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop hrootpos).eventually_ge_atTop 2
  have hmeshRoot : ∀ᶠ N : ℕ in atTop,
      2 ≤ (1 - Real.sqrt δ) * (N : ℝ) :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop (sub_pos.mpr (by linarith))).eventually_ge_atTop 2
  filter_upwards [hC₂, hδN, hrootN, hmeshRoot] with N hC₂N hδN hrootN hmeshRoot
  intro ϑ hϑ
  let m : ℕ := evenCeil (δ * N)
  let n : ℕ := evenCeil (Real.sqrt δ * N)
  let β : ℝ := criticalBeta ϑ N
  have hN1 : 1 ≤ N := by
    have hNreal : (1 : ℝ) ≤ (N : ℝ) := by nlinarith [hδN, hδlt1]
    exact_mod_cast hNreal
  have hδcast : δ * (N : ℝ) ≤ (m : ℝ) := by
    dsimp [m]
    exact Critical2DKPZ.le_evenCeil _
  have hmpos : 1 ≤ m := by
    have hmreal : (1 : ℝ) ≤ (m : ℝ) := hδN.trans hδcast
    exact_mod_cast hmreal
  have hrootcast : Real.sqrt δ * (N : ℝ) ≤ (n : ℝ) := by
    dsimp [n]
    exact Critical2DKPZ.le_evenCeil _
  have hrootUpper : (n : ℝ) ≤ 2 * Real.sqrt δ * (N : ℝ) := by
    have hround := Critical2DKPZ.evenCeil_lt_add_two
      (show 0 ≤ Real.sqrt δ * (N : ℝ) from mul_nonneg (Real.sqrt_nonneg δ) (Nat.cast_nonneg N))
    have hcast : (n : ℝ) ≤ Real.sqrt δ * (N : ℝ) + 2 := by
      dsimp [n]
      exact hround.le
    have hrootNreal : (2 : ℝ) ≤ Real.sqrt δ * (N : ℝ) := hrootN
    nlinarith
  have hnUpper : n ≤ N := by
    have hround := Critical2DKPZ.evenCeil_lt_add_two
      (show 0 ≤ Real.sqrt δ * (N : ℝ) from mul_nonneg (Real.sqrt_nonneg δ) (Nat.cast_nonneg N))
    have hcast : (n : ℝ) ≤ Real.sqrt δ * (N : ℝ) + 2 := by
      dsimp [n]
      exact hround.le
    have hNupper : Real.sqrt δ * (N : ℝ) + 2 ≤ (N : ℝ) := by
      nlinarith [hmeshRoot]
    exact_mod_cast hcast.trans hNupper
  have hmn : m ≤ n := by
    dsimp [m, n]
    apply Critical2DKPZ.evenCeil_mono
    exact mul_le_mul_of_nonneg_right hδsqrt (Nat.cast_nonneg N)
  have hnpos : 0 < (n : ℝ) := by
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (by exact_mod_cast hmpos.trans hmn)
  have hmposReal : 0 < (m : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hmpos)
  have hsquare : (Real.sqrt δ) ^ 2 = δ := Real.sq_sqrt hδ.le
  have hratio : (n : ℝ) / m ≤ 2 / Real.sqrt δ := by
    apply (div_le_div_iff₀ hmposReal hrootpos).2
    have hmul : (n : ℝ) * Real.sqrt δ ≤ 2 * (m : ℝ) := by
      calc
        _ ≤ (2 * Real.sqrt δ * (N : ℝ)) * Real.sqrt δ :=
          mul_le_mul_of_nonneg_right hrootUpper hrootpos.le
        _ = 2 * δ * (N : ℝ) := by nlinarith [hsquare]
        _ = 2 * (δ * (N : ℝ)) := by ring
        _ ≤ 2 * (m : ℝ) := mul_le_mul_of_nonneg_left hδcast (by norm_num)
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hNratio : 1 / (2 * Real.sqrt δ) ≤ (N : ℝ) / n := by
    apply (div_le_div_iff₀ (by positivity) hnpos).2
    nlinarith [hrootUpper]
  have hratioPos : 0 < (n : ℝ) / m := div_pos (by exact_mod_cast (Nat.zero_lt_of_lt (le_trans hmpos hmn))) hmposReal
  let x : ℝ := 1 / Real.sqrt δ
  have hquad : 2 * x ≤ (1 + x / 2) ^ 2 := by
    nlinarith [sq_nonneg (x - 2)]
  have hlogRatio : Real.log ((n : ℝ) / m) ≤
      2 * Real.log (1 + (N : ℝ) / n) := by
    have hfirst : Real.log ((n : ℝ) / m) ≤ Real.log (2 * x) := by
      apply Real.log_le_log hratioPos
      simpa [x, div_eq_mul_inv] using hratio
    have hquadlog : Real.log (2 * x) ≤ 2 * Real.log (1 + x / 2) := by
      calc
        _ ≤ Real.log ((1 + x / 2) ^ 2) :=
          Real.log_le_log (by dsimp [x]; positivity) (by nlinarith [hquad])
        _ = _ := by rw [Real.log_pow]; norm_num
    have hxhalf : x / 2 = 1 / (2 * Real.sqrt δ) := by dsimp [x]; ring
    have hlast : Real.log (1 + x / 2) ≤ Real.log (1 + (N : ℝ) / n) := by
      apply Real.log_le_log (by positivity)
      rw [hxhalf]
      linarith [hNratio]
    linarith
  have hlog9le : Real.log 9 ≤ Real.log (1 + (N : ℝ) / n) := by
    apply Real.log_le_log (by norm_num)
    have hx8 : 8 < 1 / (2 * Real.sqrt δ) := by
      rw [lt_div_iff₀ (by positivity)]
      nlinarith [hx]
    linarith [hNratio]
  have hdenpos : 0 < Real.log (1 + (N : ℝ) / n) :=
    lt_of_lt_of_le hlog9 hlog9le
  have hRdiffnonneg : 0 ≤ Critical2DKPZ.replicaOverlap n -
      Critical2DKPZ.replicaOverlap m := by
    rw [OnePoint.replicaOverlap_sub_eq_sum m n hmn]
    exact Finset.sum_nonneg fun r _ => Critical2DKPZ.srwKernel_nonneg (2 * r) 0
  have happrox := hC_R m n hmn
  have happrox' : |Real.pi * (Critical2DKPZ.replicaOverlap n -
      Critical2DKPZ.replicaOverlap m) - Real.log ((n : ℝ) / m)| ≤ C_R := by
    simpa [show max m 1 = m by omega, show max n 1 = n by omega] using happrox
  have hpiDiff : Real.pi * (Critical2DKPZ.replicaOverlap n -
      Critical2DKPZ.replicaOverlap m) ≤
        2 * Real.log (1 + (N : ℝ) / n) + C_R := by
    have hupper := (abs_le.mp happrox').2
    linarith [hlogRatio]
  have hCRscale : C_R ≤
      (C_R / Real.log 9) * Real.log (1 + (N : ℝ) / n) := by
    calc
      _ = (C_R / Real.log 9) * Real.log 9 := by
        field_simp [ne_of_gt hlog9]
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog9le
        (div_nonneg hCR hlog9.le)
  have hdiffBound : Critical2DKPZ.replicaOverlap n - Critical2DKPZ.replicaOverlap m ≤
      K * Real.log (1 + (N : ℝ) / n) := by
    have hpiBound : Real.pi * (Critical2DKPZ.replicaOverlap n -
        Critical2DKPZ.replicaOverlap m) ≤
          (2 + C_R / Real.log 9) * Real.log (1 + (N : ℝ) / n) := by
      nlinarith [hpiDiff, hCRscale]
    dsimp [K]
    calc
      _ ≤ ((2 + C_R / Real.log 9) * Real.log (1 + (N : ℝ) / n)) / Real.pi := by
        apply (le_div_iff₀ Real.pi_pos).2
        nlinarith [hpiBound]
      _ = _ := by ring
  have hratioBound :
      (Critical2DKPZ.replicaOverlap n - Critical2DKPZ.replicaOverlap m) /
        Real.log (1 + (N : ℝ) / n) ≤ K := by
    exact (div_le_iff₀ hdenpos).2 (by simpa [mul_comm] using hdiffBound)
  have hβ : 0 ≤ β := by dsimp [β, criticalBeta]; positivity
  have hnreal : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnUpper
  have hnreal' : (n : ℝ) ≤ (1 : ℝ) * (N : ℝ) := by simpa using hnreal
  have hsecond := hC₂N ϑ hϑ m n hmn (by omega) hnreal'
  have hsecond' :
      (∫ ω, smoothedP2Plane β m n 0 ω ^ 2 ∂disorderLaw) ≤ M := by
    have hratioNonneg : 0 ≤
        (Critical2DKPZ.replicaOverlap n - Critical2DKPZ.replicaOverlap m) /
          Real.log (1 + (N : ℝ) / n) := div_nonneg hRdiffnonneg hdenpos.le
    calc
      _ ≤ 1 + C₂ * (Critical2DKPZ.replicaOverlap n -
          Critical2DKPZ.replicaOverlap m) / Real.log (1 + (N : ℝ) / n) := by
        simpa [β, mul_div_assoc] using hsecond
      _ = 1 + C₂ * ((Critical2DKPZ.replicaOverlap n -
          Critical2DKPZ.replicaOverlap m) / Real.log (1 + (N : ℝ) / n)) := by ring
      _ ≤ 1 + |C₂| * K := by
        have hcoeff₁ := mul_le_mul_of_nonneg_right (le_abs_self C₂) hratioNonneg
        have hcoeff₂ := mul_le_mul_of_nonneg_left hratioBound (abs_nonneg C₂)
        dsimp [M, K]
        linarith
  have hinv := integral_inv_smoothedP2Plane_le_sq β hβ m n
  have hDinv :
      (∫ ω, (smoothedP2Plane β m n 0 ω)⁻¹ ∂disorderLaw) ≤ M :=
    hinv.2.trans hsecond'
  exact ⟨hN1, hmn, hnUpper, by simpa [β, m, n] using hDinv⟩

/-- The annealed smoothed endpoint tail has a Gaussian bound, uniformly over the critical window.
The integrand is integrable by `integral_smoothedEndpointTailMass_le`, applied with the inverse
moment bound established in this theorem. -/
theorem integral_smoothedEndpoint_tail_le (A : ℝ) :
    ∃ δ₁ C c : ℝ, 0 < δ₁ ∧ 0 < c ∧
      ∀ δ : ℝ, 0 < δ → δ < δ₁ → ∀ᶠ N : ℕ in atTop,
        ∀ ϑ ∈ Set.Icc (-A) A, ∀ R : ℝ, 1 ≤ R →
          ∫ ω, ∑' y, {y : Site | R * Real.sqrt N < ‖siteToPlane y‖}.indicator
            (fun y => ∑' w, smoothedEndpointDist (criticalBeta ϑ N)
              (evenCeil (δ * N)) (evenCeil (Real.sqrt δ * N)) 0 ω w *
              srwKernel (N - evenCeil (Real.sqrt δ * N)) (y - w)) y ∂disorderLaw ≤
            C * Real.exp (-c * R ^ 2) := by
  obtain ⟨M, hM, hInv⟩ := smoothedEndpoint_inverseMoment_smallDelta A
  obtain ⟨cwalk, hcwalk, hwalkAll⟩ := exists_srwKernel_tail_le_gaussian_constant
  let C : ℝ := Real.sqrt cwalk * Real.sqrt M
  let c : ℝ := 1 / (16 * cwalk)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  refine ⟨1 / 256, C, c, by norm_num, hc, ?_⟩
  intro δ hδ hδsmall
  filter_upwards [hInv δ hδ hδsmall] with N hNinv
  intro ϑ hϑ R hR
  rcases hNinv ϑ hϑ with ⟨hN, hmn, hnN, hDinv⟩
  let m : ℕ := evenCeil (δ * N)
  let n : ℕ := evenCeil (Real.sqrt δ * N)
  let β : ℝ := criticalBeta ϑ N
  have hβ : 0 ≤ β := by dsimp [β, criticalBeta]; positivity
  have hwalk := hwalkAll R (by linarith) N hN
  have hmass := integral_smoothedEndpointTailMass_le β hβ m n N hmn hnN R
    cwalk hcwalk hwalk M hM (by simpa [β, m, n] using hDinv)
  have htailEq (ω : Disorder) :
      (∑' y, {y : Site | R * Real.sqrt N < ‖siteToPlane y‖}.indicator
        (fun y => ∑' w, smoothedEndpointDist β m n 0 ω w *
          srwKernel (N - n) (y - w)) y) = smoothedEndpointTailMass β m n N R ω := by
    unfold smoothedEndpointTailMass
    apply tsum_congr
    intro y
    by_cases hy : R * Real.sqrt N < ‖siteToPlane y‖
    · simp [Set.indicator, hy]
    · simp [Set.indicator, hy]
  have htailBound :
      (∫ ω, smoothedEndpointTailMass β m n N R ω ∂disorderLaw) ≤
        C * Real.exp (-c * R ^ 2) := by
    have hexp : -R ^ 2 / (16 * cwalk) = -c * R ^ 2 := by
      dsimp [c]
      ring
    calc
      _ ≤ Real.sqrt cwalk * Real.sqrt M * Real.exp (-R ^ 2 / (16 * cwalk)) := hmass.2
      _ = C * Real.exp (-c * R ^ 2) := by
        rw [hexp]
  calc
    _ = ∫ ω, smoothedEndpointTailMass β m n N R ω ∂disorderLaw := by
      apply integral_congr_ae
      exact ae_of_all disorderLaw fun ω => by simpa [β, m, n] using htailEq ω
    _ ≤ _ := htailBound


end Critical2DKPZ.FutureProfiles
