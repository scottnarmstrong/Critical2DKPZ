/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Limit.Marginal
public import Critical2DKPZ.SHF.Positivity.HeatStartMean
public import Critical2DKPZ.SHF.Positivity.PolymerHeatSecondMoment
public import Critical2DKPZ.SHF.Positivity.MeasurablePairing
public import Critical2DKPZ.SHF.DeltaBose.SupBlockBounds
public import Critical2DKPZ.MomentBounds.CSZ25Variance
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! # Exponential profile bounds for the discrete polymer -/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory
open Critical2DKPZ.SHF.Limit

noncomputable section

namespace Critical2DKPZ.SHF.TimeContinuity

private def exponentialStartProfile (N : ℕ) (w : Site) : ℝ :=
  ∫ x in cell N w, Real.exp (-‖x‖)

private theorem exponentialStartProfile_bounds {N : ℕ} (hN : 1 ≤ N) :
    (∀ w, 0 ≤ exponentialStartProfile N w) ∧
    Summable (exponentialStartProfile N) ∧
    (∑' w, exponentialStartProfile N w) ≤ 8 ∧
    (∀ w, exponentialStartProfile N w ≤ 4 / (N : ℝ)) := by
  let f : Plane → ℝ := fun x => Real.exp (-‖x‖)
  let a : ℝ := (Real.sqrt 2)⁻¹
  have ha : 0 < a := by dsimp [a]; positivity
  have hmajor : Integrable (fun x : Plane => Real.exp (-a * Critical2DKPZ.DeltaBose.planeOneNorm x)) :=
    Critical2DKPZ.DeltaBose.integrable_exp_neg_planeOneNorm ha
  have hnormLe (x : Plane) : a * Critical2DKPZ.DeltaBose.planeOneNorm x ≤ ‖x‖ := by
    have hone : 0 ≤ Critical2DKPZ.DeltaBose.planeOneNorm x :=
      add_nonneg (abs_nonneg _) (abs_nonneg _)
    have hsq := Critical2DKPZ.DeltaBose.planeOneNorm_sq_le x
    have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have haSq : a ^ 2 = 1 / 2 := by
      dsimp [a]
      rw [inv_pow, hsqrt]
      norm_num
    have hsq' : (a * Critical2DKPZ.DeltaBose.planeOneNorm x) ^ 2 ≤ ‖x‖ ^ 2 := by
      nlinarith [hsq, haSq]
    exact (sq_le_sq₀ (mul_nonneg ha.le hone) (norm_nonneg _)).mp hsq'
  have hle (x : Plane) : f x ≤ Real.exp (-a * Critical2DKPZ.DeltaBose.planeOneNorm x) :=
    Real.exp_le_exp.mpr (by nlinarith [hnormLe x])
  have hf : Integrable f volume := by
    apply hmajor.mono' (Real.measurable_exp.comp (measurable_norm.neg)).aestronglyMeasurable
    filter_upwards [] with x
    change ‖f x‖ ≤ Real.exp (-a * Critical2DKPZ.DeltaBose.planeOneNorm x)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    exact hle x
  have hmassLe : (∫ x, f x) ≤ 8 := by
    calc
      (∫ x, f x) ≤ ∫ x, Real.exp (-a * Critical2DKPZ.DeltaBose.planeOneNorm x) :=
        integral_mono hf hmajor hle
      _ = (2 / a) ^ 2 := Critical2DKPZ.DeltaBose.integral_exp_neg_planeOneNorm ha
      _ = 8 := by
        dsimp [a]
        rw [div_eq_mul_inv, inv_inv, mul_pow,
          Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
  have hνnonneg : ∀ w, 0 ≤ exponentialStartProfile N w := by
    intro w
    exact setIntegral_nonneg (measurableSet_cell N w) fun x hx =>
      le_of_lt (Real.exp_pos _)
  have hcover : (⋃ w : Site, cell N w) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨latticePoint N x, mem_cell_latticePoint N x⟩
  have hνHasSum : HasSum (exponentialStartProfile N) (∫ x, f x) := by
    have h := hasSum_integral_iUnion (fun w : Site => measurableSet_cell N w)
      (pairwise_disjoint_cell N) hf.integrableOn
    change HasSum (fun w : Site => ∫ x in cell N w, f x) (∫ x, f x)
    simpa only [exponentialStartProfile, f, hcover, setIntegral_univ] using h
  have hνsum : Summable (exponentialStartProfile N) := hνHasSum.summable
  have hνmass : (∑' w, exponentialStartProfile N w) = ∫ x, f x := hνHasSum.tsum_eq
  have hνbound : ∀ w, exponentialStartProfile N w ≤ 4 / (N : ℝ) := by
    intro w
    by_cases hw : w ∈ evenLattice
    · have hNpos : 0 < N := by omega
      have hvol := volume_cell_lt_top hNpos hw
      have hconst : IntegrableOn (fun _ : Plane => (1 : ℝ)) (cell N w) volume :=
        integrableOn_const hvol.ne
      calc
        exponentialStartProfile N w ≤ ∫ x in cell N w, (1 : ℝ) := by
          apply setIntegral_mono_on hf.integrableOn hconst (measurableSet_cell N w)
          intro x hx
          dsimp [f]
          exact Real.exp_le_one_iff.mpr (by linarith [norm_nonneg x])
        _ = 4 / (N : ℝ) := by
          rw [setIntegral_const, measureReal_def, smul_eq_mul,
            volume_cell_toReal hNpos hw]
          norm_num
    · change (∫ x in cell N w, Real.exp (-‖x‖)) ≤ 4 / (N : ℝ)
      rw [cell_eq_empty_of_not_even hw]
      simp
      positivity
  exact ⟨hνnonneg, hνsum, hνmass.trans_le hmassLe, hνbound⟩

private theorem greenEnergy_le_of_profile_cell_bound {L : ℕ}
    (ν : Site → ℝ) (hν0 : ∀ w, 0 ≤ ν w) (hνsum : Summable ν)
    (M K : ℝ) (hM : (∑' w, ν w) ≤ M) (hK : 0 ≤ K)
    (hνbound : ∀ w, ν w ≤ K) :
    MomentBounds.greenEnergy L ν ≤ (L : ℝ) * K * M := by
  have hkernelTermSummable (z : Site) (n : ℕ) (hn : n ∈ Finset.Icc 1 L) :
      Summable (fun w : Site => srwKernel (2 * n) (z - w)) := by
    apply summable_of_ne_finset_zero (s := Polymer.endpoints z (2 * n))
    intro w hw
    rw [Polymer.srwKernel_sub_swap (2 * n) z w]
    exact Polymer.srwKernel_eq_zero_of_not_mem (2 * n) z w hw
  have hkernelTerm (z : Site) (n : ℕ) :
      (∑' w : Site, srwKernel (2 * n) (z - w)) = 1 := by
    have heq : (fun w : Site => srwKernel (2 * n) (z - w)) =
        fun w => srwKernel (2 * n) (w - z) := by
      funext w
      exact Polymer.srwKernel_sub_swap (2 * n) z w
    rw [heq]
    exact Polymer.tsum_srwKernel (2 * n) z
  have hkernelSummable (z : Site) :
      Summable (fun w : Site => MomentBounds.truncatedGreen L (z - w)) := by
    apply summable_of_ne_finset_zero
      (s := (Finset.Icc 1 L).biUnion fun n => Polymer.endpoints z (2 * n))
    intro w hw
    simp only [Finset.mem_biUnion, not_exists, not_and] at hw
    simp only [MomentBounds.truncatedGreen]
    apply Finset.sum_eq_zero
    intro n hn
    have hnot : w ∉ Polymer.endpoints z (2 * n) := hw n hn
    rw [Polymer.srwKernel_sub_swap (2 * n) z w]
    exact Polymer.srwKernel_eq_zero_of_not_mem (2 * n) z w hnot
  have hkernel (z : Site) :
      (∑' w : Site, MomentBounds.truncatedGreen L (z - w)) = L := by
    have hfinite := Summable.tsum_finsetSum (fun n hn => hkernelTermSummable z n hn)
    change (∑' w : Site, ∑ n ∈ Finset.Icc 1 L, srwKernel (2 * n) (z - w)) = L
    rw [hfinite]
    simp_rw [hkernelTerm]
    simp
  have hkerNonneg (z w : Site) : 0 ≤ MomentBounds.truncatedGreen L (z - w) :=
    MomentBounds.truncatedGreen_nonneg L (z - w)
  have hinner (z : Site) :
      (∑' w : Site, MomentBounds.truncatedGreen L (z - w) * ν w) ≤ K * L := by
    have hk := hkernel z
    have hterm0 (w : Site) :
        0 ≤ MomentBounds.truncatedGreen L (z - w) * ν w :=
      mul_nonneg (hkerNonneg z w) (hν0 w)
    have htermle (w : Site) :
        MomentBounds.truncatedGreen L (z - w) * ν w ≤
          K * MomentBounds.truncatedGreen L (z - w) := by
      calc
        _ ≤ MomentBounds.truncatedGreen L (z - w) * K :=
          mul_le_mul_of_nonneg_left (hνbound w) (hkerNonneg z w)
        _ = _ := by ring
    have hmajor : Summable (fun w : Site => K * MomentBounds.truncatedGreen L (z - w)) :=
      (hkernelSummable z).mul_left K
    have hterms : Summable (fun w : Site =>
        MomentBounds.truncatedGreen L (z - w) * ν w) :=
      Summable.of_nonneg_of_le hterm0 htermle hmajor
    have hle := hterms.tsum_le_tsum htermle hmajor
    have hright : (∑' w : Site, K * MomentBounds.truncatedGreen L (z - w)) = K * L := by
      rw [tsum_mul_left, hk]
    rw [hright] at hle
    exact hle
  have houterNonneg (z : Site) :
      0 ≤ ∑' w : Site, ν z * MomentBounds.truncatedGreen L (z - w) * ν w :=
    tsum_nonneg fun w => mul_nonneg (mul_nonneg (hν0 z) (hkerNonneg z w)) (hν0 w)
  have houterBound (z : Site) :
      (∑' w : Site, ν z * MomentBounds.truncatedGreen L (z - w) * ν w) ≤
        ν z * (K * L) := by
    calc
      _ = ∑' w : Site, ν z *
          (MomentBounds.truncatedGreen L (z - w) * ν w) := by
        congr 1
        funext w
        ring
      _ = ν z * (∑' w : Site, MomentBounds.truncatedGreen L (z - w) * ν w) :=
        tsum_mul_left
      _ ≤ _ := mul_le_mul_of_nonneg_left (hinner z) (hν0 z)
  have houterMajor : Summable (fun z : Site => ν z * (K * L)) := hνsum.mul_right (K * L)
  have houterSummable : Summable (fun z : Site =>
      ∑' w : Site, ν z * MomentBounds.truncatedGreen L (z - w) * ν w) :=
    Summable.of_nonneg_of_le houterNonneg houterBound houterMajor
  unfold MomentBounds.greenEnergy
  calc
    _ ≤ ∑' z : Site, ν z * (K * L) := houterSummable.tsum_le_tsum houterBound houterMajor
    _ = (∑' z : Site, ν z) * (K * L) := by rw [tsum_mul_right]
    _ ≤ M * (K * L) := mul_le_mul_of_nonneg_right hM (mul_nonneg hK (Nat.cast_nonneg _))
    _ = (L : ℝ) * K * M := by ring

private theorem firstExponentialPairing_profile_ae (ϑ : ℝ) {N : ℕ} (hN : 1 ≤ N)
    {s t : ℝ} (hst : s < t) : ∀ᵐ ω ∂disorderLaw,
      (∫ x, Real.exp (-‖x‖) ∂((polymerMeasure ϑ N s t ω).map Prod.fst)) =
        profileP2Fun (criticalBeta ϑ N) (evenCeil (N * s)) (evenCeil (N * t))
          (exponentialStartProfile N) (fun _ => 1) ω := by
  let f : Plane → ℝ := fun x => Real.exp (-‖x‖)
  have hmajor : Integrable (fun x : Plane =>
      Real.exp (-(Real.sqrt 2)⁻¹ * Critical2DKPZ.DeltaBose.planeOneNorm x)) :=
    Critical2DKPZ.DeltaBose.integrable_exp_neg_planeOneNorm (by positivity)
  have hnormLe (x : Plane) : (Real.sqrt 2)⁻¹ *
      Critical2DKPZ.DeltaBose.planeOneNorm x ≤ ‖x‖ := by
    have hone : 0 ≤ Critical2DKPZ.DeltaBose.planeOneNorm x :=
      add_nonneg (abs_nonneg _) (abs_nonneg _)
    have hsq := Critical2DKPZ.DeltaBose.planeOneNorm_sq_le x
    have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have haSq : ((Real.sqrt 2)⁻¹) ^ 2 = 1 / 2 := by
      rw [inv_pow, hsqrt]
      norm_num
    have hsq' : ((Real.sqrt 2)⁻¹ * Critical2DKPZ.DeltaBose.planeOneNorm x) ^ 2 ≤
        ‖x‖ ^ 2 := by nlinarith [hsq, haSq]
    exact (sq_le_sq₀ (mul_nonneg (by positivity) hone) (norm_nonneg _)).mp hsq'
  have hle (x : Plane) : f x ≤
      Real.exp (-(Real.sqrt 2)⁻¹ * Critical2DKPZ.DeltaBose.planeOneNorm x) :=
    Real.exp_le_exp.mpr (by nlinarith [hnormLe x])
  have hf : Integrable f volume := by
    apply hmajor.mono' (Real.measurable_exp.comp (measurable_norm.neg)).aestronglyMeasurable
    filter_upwards [] with x
    change ‖f x‖ ≤ Real.exp (-(Real.sqrt 2)⁻¹ * Critical2DKPZ.DeltaBose.planeOneNorm x)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    exact hle x
  let H : Plane × Disorder → ℝ := fun q => f q.1 * rescaledP2Plane ϑ N s t q.1 q.2
  have hH : Integrable H (volume.prod disorderLaw) := by
    exact integrable_flatPairingProduct ϑ N s t hf
  have hslice := hH.swap.prod_right_ae
  filter_upwards [hslice] with ω hω
  have hInt : Integrable (fun x : Plane => f x * rescaledP2Plane ϑ N s t x ω) volume := by
    simpa only [H, Prod.fst, Prod.snd, Function.comp_apply, Prod.swap_prod_mk] using hω
  let a := evenCeil ((N : ℝ) * s)
  let b := evenCeil ((N : ℝ) * t)
  have hab : a ≤ b := by
    dsimp [a, b]
    exact evenCeil_mono (mul_le_mul_of_nonneg_left hst.le (Nat.cast_nonneg N))
  let L := b - a
  have hcover : (⋃ w : Site, cell N w) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨latticePoint N x, mem_cell_latticePoint N x⟩
  have hcellHasSum : HasSum (fun w : Site =>
      ∫ x in cell N w, f x * rescaledP2Plane ϑ N s t x ω)
      (∫ x, f x * rescaledP2Plane ϑ N s t x ω) := by
    have h := hasSum_integral_iUnion (fun w : Site => measurableSet_cell N w)
      (pairwise_disjoint_cell N) hInt.integrableOn
    simpa only [hcover, setIntegral_univ] using h
  have hcellTerm (w : Site) :
      (∫ x in cell N w, f x * rescaledP2Plane ϑ N s t x ω) =
        exponentialStartProfile N w *
          pointToPlane (criticalBeta ϑ N) a (b - a) w ω := by
    calc
      _ = ∫ x in cell N w,
          f x * pointToPlane (criticalBeta ϑ N) a (b - a) w ω := by
        apply setIntegral_congr_fun (measurableSet_cell N w)
        intro x hx
        rw [mem_cell_iff] at hx
        simp [rescaledP2Plane, a, b, hx]
      _ = _ := by
        rw [show (fun x : Plane => f x *
            pointToPlane (criticalBeta ϑ N) a (b - a) w ω) =
            fun x => pointToPlane (criticalBeta ϑ N) a (b - a) w ω * f x by
              funext x
              ring]
        simp only [exponentialStartProfile]
        rw [integral_const_mul]
        ring
  have hsumProfile : HasSum (fun w : Site => exponentialStartProfile N w *
      pointToPlane (criticalBeta ϑ N) a (b - a) w ω)
      (∫ x, f x * rescaledP2Plane ϑ N s t x ω) := by
    exact hcellHasSum.congr_fun (fun w => (hcellTerm w).symm)
  have hprofile : profileP2Fun (criticalBeta ϑ N) a b
      (exponentialStartProfile N) (fun _ => 1) ω =
      ∫ x, f x * rescaledP2Plane ϑ N s t x ω := by
    calc
      _ = ∑' w : Site, exponentialStartProfile N w *
          pointToPlane (criticalBeta ϑ N) a (b - a) w ω := by
        unfold profileP2Fun
        apply tsum_congr
        intro w
        simp only [mul_one, Polymer.tsum_pointToPoint]
      _ = _ := hsumProfile.tsum_eq
  rw [integral_map_fst_polymerMeasure ϑ hN s t ω f]
  simpa only [f, a, b] using hprofile.symm

private theorem firstExponentialPairing_sq_integral_bounded (ϑ T : ℝ) :
    ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ T →
      Integrable (fun ω =>
        (∫ x, Real.exp (-‖x‖) ∂((polymerMeasure ϑ N s t ω).map Prod.fst)) ^ 2)
        disorderLaw ∧
      ∫ ω, (∫ x, Real.exp (-‖x‖)
        ∂((polymerMeasure ϑ N s t ω).map Prod.fst)) ^ 2 ∂disorderLaw ≤ C := by
  let H : ℝ := max T 0 + 1
  have hH : 0 < H := by dsimp [H]; linarith [le_max_right T 0]
  obtain ⟨C₀, hC₀⟩ := OnePoint.sigmaSq_secondMoment_le_uniform |ϑ| H
  have hN : ∀ᶠ N : ℕ in atTop, 2 ≤ N := Filter.eventually_atTop.2 ⟨2, fun _ h => h⟩
  let C : ℝ := 64 + 32 * H *
    (max C₀ 0 / Real.log (1 + 1 / H))
  have hden : 0 < Real.log (1 + 1 / H) := by
    apply Real.log_pos
    have : 0 < 1 / H := one_div_pos.mpr hH
    linarith
  refine ⟨C, ?_⟩
  filter_upwards [hN, hC₀] with N hN hmoment
  intro s t hs hst ht
  have hNreal : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : 0 < (N : ℝ) := lt_of_lt_of_le (by norm_num) hNreal
  let a := evenCeil ((N : ℝ) * s)
  let b := evenCeil ((N : ℝ) * t)
  have hab : a ≤ b := by
    dsimp [a, b]
    exact evenCeil_mono (mul_le_mul_of_nonneg_left hst.le (Nat.cast_nonneg N))
  let L := b - a
  have hLcast : (L : ℝ) = (b : ℝ) - a := by
    dsimp [L]
    exact Nat.cast_sub hab
  have hsN : 0 ≤ (N : ℝ) * s := mul_nonneg (Nat.cast_nonneg N) hs
  have htNonneg : 0 ≤ t := le_trans hs hst.le
  have htN : 0 ≤ (N : ℝ) * t := mul_nonneg (Nat.cast_nonneg N) htNonneg
  have hround := evenCeil_duration_error hsN htN
  have hLround : |(L : ℝ) - (N : ℝ) * (t - s)| < 2 := by
    have heq : (L : ℝ) - (N : ℝ) * (t - s) =
        (evenCeil ((N : ℝ) * t) : ℝ) - evenCeil ((N : ℝ) * s) -
          ((N : ℝ) * t - (N : ℝ) * s) := by
      rw [hLcast]
      dsimp [a, b]
      ring
    rw [heq]
    exact hround
  have hTpos : 0 < T := by linarith
  have hHval : T + 1 = H := by simp [H, max_eq_left hTpos.le]
  have hgapLe : t - s ≤ T := by linarith
  have hLupper : (L : ℝ) ≤ H * N := by
    have hroundUpper := (abs_lt.mp hLround).2
    have hroundUpper' : (L : ℝ) < (N : ℝ) * (t - s) + 2 := by linarith
    have hNgap : (N : ℝ) * (t - s) ≤ (N : ℝ) * T :=
      mul_le_mul_of_nonneg_left hgapLe (Nat.cast_nonneg N)
    apply le_of_lt
    calc
      (L : ℝ) < (N : ℝ) * (t - s) + 2 := hroundUpper'
      _ ≤ (N : ℝ) * T + (N : ℝ) := by nlinarith [hNgap, hNreal]
      _ = (N : ℝ) * (T + 1) := by ring
      _ = H * N := by rw [hHval]; ring
  have hLnonneg : 0 ≤ (L : ℝ) := Nat.cast_nonneg _
  let ν : Site → ℝ := exponentialStartProfile N
  obtain ⟨hν0, hνsum, hνmass, hνbound⟩ := exponentialStartProfile_bounds (by omega : 1 ≤ N)
  have hνabs : Summable (fun w : Site => |ν w|) := by
    simpa only [ν, abs_of_nonneg (hν0 _)] using hνsum
  let F : Disorder → ℝ := profileP2Fun (criticalBeta ϑ N) 0 L ν (fun _ => 1)
  let G : Disorder → ℝ := profileP2Fun (criticalBeta ϑ N) a b ν (fun _ => 1)
  have hFmeas : Measurable F := by
    dsimp [F]
    exact Polymer.measurable_profileP2Fun (criticalBeta ϑ N) 0 L ν (fun _ => 1)
  have hFmem : MemLp F 2 disorderLaw := by
    dsimp [F]
    exact Polymer.memLp_profileP2Fun_summable (criticalBeta ϑ N) 0 L ν (fun _ => 1)
      hνabs 1 zero_le_one (fun _ => by simp) 2 (by norm_num)
  have hFmean : (∫ ω, F ω ∂disorderLaw) = ∑' w, ν w := by
    dsimp [F]
    rw [Polymer.integral_profileP2Fun_summable (criticalBeta ϑ N) 0 L ν (fun _ => 1)
      hνabs 1 zero_le_one (fun _ => by simp)]
    simp only [mul_one, Polymer.tsum_srwKernel]
  have hFpow : Integrable (fun ω => F ω ^ 2) disorderLaw := by
    have h := hFmem.integrable_norm_pow'
    apply h.congr
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, sq_abs]
  have hFsecond : (∫ ω, F ω ^ 2 ∂disorderLaw) = Var[F; disorderLaw] +
      (∑' w, ν w) ^ 2 := by
    have hpow : (fun ω => F ω ^ 2) = F ^ 2 := rfl
    rw [hpow, variance_eq_sub hFmem, hFmean]
    ring
  have hGmeas : Measurable G := by
    dsimp [G]
    exact Polymer.measurable_profileP2Fun (criticalBeta ϑ N) a b ν (fun _ => 1)
  have hGmem : MemLp G 2 disorderLaw := by
    dsimp [G]
    exact Polymer.memLp_profileP2Fun_summable (criticalBeta ϑ N) a b ν (fun _ => 1)
      hνabs 1 zero_le_one (fun _ => by simp) 2 (by norm_num)
  have hGpow : Integrable (fun ω => G ω ^ 2) disorderLaw := by
    have h := hGmem.integrable_norm_pow'
    apply h.congr
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, sq_abs]
  have hGmean : (∫ ω, G ω ∂disorderLaw) = ∑' w, ν w := by
    dsimp [G]
    rw [Polymer.integral_profileP2Fun_summable (criticalBeta ϑ N) a b ν (fun _ => 1)
      hνabs 1 zero_le_one (fun _ => by simp)]
    simp only [mul_one, Polymer.tsum_srwKernel]
  have hGsecond : (∫ ω, G ω ^ 2 ∂disorderLaw) = Var[G; disorderLaw] +
      (∑' w, ν w) ^ 2 := by
    have hpow : (fun ω => G ω ^ 2) = G ^ 2 := rfl
    rw [hpow, variance_eq_sub hGmem, hGmean]
    ring
  have hshift : G = fun ω => F (Smoothing.shiftEnvironment a ω) := by
    funext ω
    dsimp [F, G]
    have htime := Smoothing.profileP2Fun_timeShift_sub (criticalBeta ϑ N)
      (d := a) (a := a) (b := b) (ν := ν) (f := fun _ => (1 : ℝ)) (ω := ω)
      (by omega) hab
    simpa only [Nat.sub_self] using htime
  have hvarEq : Var[F; disorderLaw] = Var[G; disorderLaw] := by
    rw [hshift]
    exact ((Smoothing.measurePreserving_shiftEnvironment a).variance_fun_comp
      hFmeas.aemeasurable).symm
  have hvariance := MomentBounds.variance_profileP2Fun_bounds
    (criticalBeta ϑ N) L ν hν0 hνsum
  have hqnonneg : 0 ≤ Polymer.sigmaSq (criticalBeta ϑ N) *
      Renewal.freeSecondMoment (criticalBeta ϑ N) L := by
    apply mul_nonneg
    · unfold Polymer.sigmaSq
      exact sub_nonneg.mpr (Real.one_le_exp (sq_nonneg _))
    · rw [Renewal.freeSecondMoment]
      exact integral_nonneg fun ω => sq_nonneg _
  have hgreen0 : 0 ≤ MomentBounds.greenEnergy L ν :=
    MomentBounds.greenEnergy_nonneg L ν hν0
  have hK : 0 ≤ 4 / (N : ℝ) := by positivity
  have hgreen : MomentBounds.greenEnergy L ν ≤
      (L : ℝ) * (4 / (N : ℝ)) * 8 :=
    greenEnergy_le_of_profile_cell_bound ν hν0 hνsum 8 (4 / (N : ℝ))
      hνmass hK hνbound
  have hratio : (L : ℝ) / N ≤ H := (div_le_iff₀ hNpos).2 (by nlinarith [hLupper])
  have hgreenScale : (L : ℝ) * (4 / (N : ℝ)) * 8 ≤ 32 * H := by
    calc
      (L : ℝ) * (4 / (N : ℝ)) * 8 = 32 * ((L : ℝ) / N) := by
        field_simp [ne_of_gt hNpos]
        ring
      _ ≤ 32 * H := mul_le_mul_of_nonneg_left hratio (by norm_num)
  have hvarBound : Var[F; disorderLaw] ≤
      32 * H * (max C₀ 0 / Real.log (1 + 1 / H)) := by
    by_cases hLpos : 1 ≤ L
    · have hLrealpos : 0 < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
      have hlogCompare : Real.log (1 + 1 / H) ≤ Real.log (1 + (N : ℝ) / L) := by
        apply Real.log_le_log
        · positivity
        · have hratio : 1 / H ≤ (N : ℝ) / L := by
            apply (div_le_div_iff₀ hH hLrealpos).2
            nlinarith [hLupper]
          linarith
      have hdenL : 0 < Real.log (1 + (N : ℝ) / L) :=
        lt_of_lt_of_le hden hlogCompare
      have hscaleMoment : Polymer.sigmaSq (criticalBeta ϑ N) *
          Renewal.freeSecondMoment (criticalBeta ϑ N) L ≤
          C₀ / Real.log (1 + (N : ℝ) / L) := by
        have hbound := hmoment ϑ ⟨neg_abs_le ϑ, le_abs_self ϑ⟩ L hLpos hLupper
        simpa only [Renewal.freeSecondMoment] using hbound
      have hqBound : Polymer.sigmaSq (criticalBeta ϑ N) *
          Renewal.freeSecondMoment (criticalBeta ϑ N) L ≤
          max C₀ 0 / Real.log (1 + 1 / H) := by
        by_cases hC₀nonneg : 0 ≤ C₀
        · calc
            _ ≤ C₀ / Real.log (1 + (N : ℝ) / L) := hscaleMoment
            _ ≤ C₀ / Real.log (1 + 1 / H) :=
              div_le_div_of_nonneg_left hC₀nonneg hden hlogCompare
            _ ≤ max C₀ 0 / Real.log (1 + 1 / H) :=
              div_le_div_of_nonneg_right (le_max_left _ _) hden.le
        · have hC₀nonpos : C₀ ≤ 0 := le_of_not_ge hC₀nonneg
          have hCquot : C₀ / Real.log (1 + (N : ℝ) / L) ≤ 0 :=
            (div_le_iff₀ hdenL).2 (by simpa using hC₀nonpos)
          have hqle : Polymer.sigmaSq (criticalBeta ϑ N) *
              Renewal.freeSecondMoment (criticalBeta ϑ N) L ≤ 0 := hscaleMoment.trans hCquot
          have hqeq : Polymer.sigmaSq (criticalBeta ϑ N) *
              Renewal.freeSecondMoment (criticalBeta ϑ N) L = 0 := le_antisymm hqle hqnonneg
          rw [hqeq]
          positivity
      have hQnonneg : 0 ≤ max C₀ 0 / Real.log (1 + 1 / H) :=
        div_nonneg (le_max_right _ _) hden.le
      calc
        _ ≤ MomentBounds.greenEnergy L ν *
            (Polymer.sigmaSq (criticalBeta ϑ N) *
              Renewal.freeSecondMoment (criticalBeta ϑ N) L) := by
          simpa only [mul_assoc] using hvariance.2
        _ ≤ (MomentBounds.greenEnergy L ν) *
            (max C₀ 0 / Real.log (1 + 1 / H)) :=
          mul_le_mul_of_nonneg_left hqBound hgreen0
        _ ≤ ((L : ℝ) * (4 / (N : ℝ)) * 8) *
            (max C₀ 0 / Real.log (1 + 1 / H)) :=
          mul_le_mul_of_nonneg_right hgreen hQnonneg
        _ ≤ (32 * H) * (max C₀ 0 / Real.log (1 + 1 / H)) :=
          mul_le_mul_of_nonneg_right hgreenScale (by positivity)
        _ = _ := by ring
    · have hLzero : L = 0 := by omega
      have hgreenZero : MomentBounds.greenEnergy 0 ν = 0 := by
        simp [MomentBounds.greenEnergy, MomentBounds.truncatedGreen]
      have hzeroBound : Var[F; disorderLaw] ≤ 0 := by
        have hvarUpper := hvariance.2
        rw [hLzero, hgreenZero] at hvarUpper
        simpa [F, hLzero] using hvarUpper
      exact hzeroBound.trans (by positivity)
  have hmassNonneg : 0 ≤ ∑' w : Site, ν w := tsum_nonneg fun w => hν0 w
  have hmassSq : (∑' w : Site, ν w) ^ 2 ≤ 64 := by
    have hmassUpper : ∑' w : Site, ν w ≤ 8 := hνmass
    nlinarith [sq_nonneg ((∑' w : Site, ν w) - 8)]
  have hGsecondBound : (∫ ω, G ω ^ 2 ∂disorderLaw) ≤ C := by
    rw [hGsecond, ← hvarEq]
    dsimp [C]
    linarith [hvarBound, hmassSq]
  let B : Disorder → ℝ := fun ω =>
    ∫ x, Real.exp (-‖x‖) ∂((polymerMeasure ϑ N s t ω).map Prod.fst)
  have hBprofile : B =ᵐ[disorderLaw] G := by
    filter_upwards [firstExponentialPairing_profile_ae ϑ (by omega : 1 ≤ N) hst]
      with ω hω
    dsimp [B, G]
    simpa only [ν, a, b] using hω
  have hBpow : Integrable (fun ω => B ω ^ 2) disorderLaw := by
    apply hGpow.congr
    filter_upwards [hBprofile] with ω hω
    rw [hω]
  have hBbound : (∫ ω, B ω ^ 2 ∂disorderLaw) ≤ C := by
    calc
      _ = ∫ ω, G ω ^ 2 ∂disorderLaw := by
        apply integral_congr_ae
        filter_upwards [hBprofile] with ω hω
        rw [hω]
      _ ≤ C := hGsecondBound
  exact ⟨hBpow, by simpa only [B] using hBbound⟩

/-- A uniform second-moment bound for the exponential envelope, obtained by dominating it with
the first-marginal exponential profile and applying the lattice variance estimate. -/
theorem polymerMeasure_expEnvelope_sq_integral_le (ϑ T : ℝ) :
    ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ T →
      Integrable (fun ω =>
        (∫ p, Real.exp (-(‖p.1‖ + ‖p.2‖))
          ∂(polymerMeasure ϑ N s t ω)) ^ 2) disorderLaw ∧
      ∫ ω, (∫ p, Real.exp (-(‖p.1‖ + ‖p.2‖))
        ∂(polymerMeasure ϑ N s t ω)) ^ 2 ∂disorderLaw ≤ C := by
  obtain ⟨C, hC⟩ := firstExponentialPairing_sq_integral_bounded ϑ T
  have hN : ∀ᶠ N : ℕ in atTop, 1 ≤ N := Filter.eventually_atTop.2 ⟨1, fun _ h => h⟩
  refine ⟨C, ?_⟩
  filter_upwards [hC, hN] with N hC hN
  intro s t hs hst ht
  have hfirst := hC s t hs hst ht
  let μ : Disorder → Measure (Plane × Plane) := polymerMeasure ϑ N s t
  let f : Plane → ℝ := fun x => Real.exp (-‖x‖)
  let E : Plane × Plane → ℝ := fun p => Real.exp (-(‖p.1‖ + ‖p.2‖))
  let A : Disorder → ℝ := fun ω => ∫ p, E p ∂μ ω
  let B : Disorder → ℝ := fun ω => ∫ x, f x ∂((μ ω).map Prod.fst)
  have hfmeas : Measurable f := by
    dsimp [f]
    fun_prop
  have hEmeas : Measurable E := by
    dsimp [E]
    fun_prop
  have hMargIntegrable : ∀ᵐ ω ∂disorderLaw, Integrable f ((μ ω).map Prod.fst) := by
    let H : Plane × Disorder → ℝ := fun q => f q.1 * rescaledP2Plane ϑ N s t q.1 q.2
    have hH : Integrable H (volume.prod disorderLaw) := by
      have hf : Integrable f volume := by
        have hmajor := Critical2DKPZ.DeltaBose.integrable_exp_neg_planeOneNorm
          (show 0 < (Real.sqrt 2)⁻¹ by positivity)
        apply hmajor.mono' (hfmeas.aestronglyMeasurable)
        filter_upwards [] with x
        have hone : 0 ≤ Critical2DKPZ.DeltaBose.planeOneNorm x :=
          add_nonneg (abs_nonneg _) (abs_nonneg _)
        have hsq := Critical2DKPZ.DeltaBose.planeOneNorm_sq_le x
        have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
        have haSq : ((Real.sqrt 2)⁻¹) ^ 2 = 1 / 2 := by
          rw [inv_pow, hsqrt]
          norm_num
        have hnorm : (Real.sqrt 2)⁻¹ * Critical2DKPZ.DeltaBose.planeOneNorm x ≤ ‖x‖ := by
          have hsq' : ((Real.sqrt 2)⁻¹ * Critical2DKPZ.DeltaBose.planeOneNorm x) ^ 2 ≤ ‖x‖ ^ 2 :=
            by nlinarith [hsq, haSq]
          exact (sq_le_sq₀ (mul_nonneg (by positivity) hone) (norm_nonneg _)).mp hsq'
        change ‖f x‖ ≤ Real.exp (-(Real.sqrt 2)⁻¹ * Critical2DKPZ.DeltaBose.planeOneNorm x)
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
        exact Real.exp_le_exp.mpr (by nlinarith [hnorm])
      exact integrable_flatPairingProduct ϑ N s t hf
    have hslice := hH.swap.prod_right_ae
    filter_upwards [hslice] with ω hω
    have hslice' : Integrable (fun x : Plane =>
        f x * rescaledP2Plane ϑ N s t x ω) volume := by
      simpa only [H, Prod.fst, Prod.snd, Function.comp_apply, Prod.swap_prod_mk] using hω
    have hdensity : Measurable (fun x : Plane => ENNReal.ofReal
        (rescaledP2Plane ϑ N s t x ω)) :=
      ENNReal.measurable_ofReal.comp
        (measurable_uncurry_rescaledP2Plane ϑ N s t).of_uncurry_right
    have hmap : Integrable f ((μ ω).map Prod.fst) := by
      rw [map_fst_polymerMeasure ϑ hN s t ω]
      apply (integrable_withDensity_iff hdensity
        (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)).2
      simpa only [ENNReal.toReal_ofReal
        (rescaledP2Plane_nonneg ϑ N s t _ _)] using hslice'
    exact hmap
  have hAint : ∀ᵐ ω ∂disorderLaw, Integrable E (μ ω) := by
    filter_upwards [hMargIntegrable] with ω hω
    have hFstInt : Integrable (fun p : Plane × Plane => f p.1) (μ ω) :=
      (integrable_map_measure hfmeas.aestronglyMeasurable measurable_fst.aemeasurable).mp hω
    apply hFstInt.mono' (hEmeas.aestronglyMeasurable)
    filter_upwards [] with p
    change ‖Real.exp (-(‖p.1‖ + ‖p.2‖))‖ ≤ Real.exp (-‖p.1‖)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    apply Real.exp_le_exp.mpr
    linarith [norm_nonneg p.2]
  have hAmeas : AEMeasurable A disorderLaw := by
    exact Critical2DKPZ.SHF.Positivity.aemeasurable_integral_of_measurable_measure
      disorderLaw μ (measurable_polymerMeasure ϑ N s t) E hEmeas hAint
  have hAsqMeas : AEStronglyMeasurable (fun ω => A ω ^ 2) disorderLaw :=
    hAmeas.aestronglyMeasurable.pow 2
  have hAsqBound : ∀ᵐ ω ∂disorderLaw, A ω ^ 2 ≤ B ω ^ 2 := by
    filter_upwards [hAint, hMargIntegrable] with ω hωA hωB
    have hFstInt : Integrable (fun p : Plane × Plane => f p.1) (μ ω) :=
      (integrable_map_measure hfmeas.aestronglyMeasurable measurable_fst.aemeasurable).mp hωB
    have hAmono : A ω ≤ ∫ p, f p.1 ∂μ ω := by
      dsimp [A]
      exact integral_mono hωA hFstInt (fun p => by
        change E p ≤ f p.1
        dsimp [E, f]
        apply Real.exp_le_exp.mpr
        linarith [norm_nonneg p.2])
    have hmap : (∫ p, f p.1 ∂μ ω) = B ω := by
      dsimp [B]
      exact (integral_map measurable_fst.aemeasurable hfmeas.aestronglyMeasurable).symm
    have hAnonneg : 0 ≤ A ω := by
      dsimp [A]
      exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun p =>
        le_of_lt (Real.exp_pos _))
    have hBnonneg : 0 ≤ B ω := by
      dsimp [B]
      exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun x =>
        le_of_lt (Real.exp_pos _))
    rw [hmap] at hAmono
    exact (sq_le_sq₀ hAnonneg hBnonneg).mpr hAmono
  have hAsqInt : Integrable (fun ω => A ω ^ 2) disorderLaw := by
    apply hfirst.1.mono' hAsqMeas
    filter_upwards [hAsqBound] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (A ω))]
    exact hω
  have hAsqIntegralBound : (∫ ω, A ω ^ 2 ∂disorderLaw) ≤ C := by
    calc
      _ ≤ ∫ ω, B ω ^ 2 ∂disorderLaw :=
        integral_mono_ae hAsqInt hfirst.1 hAsqBound
      _ ≤ C := hfirst.2
  exact ⟨by simpa only [A, E, μ] using hAsqInt,
    by simpa only [A, E, μ] using hAsqIntegralBound⟩

end Critical2DKPZ.SHF.TimeContinuity

end
