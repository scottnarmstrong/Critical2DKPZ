/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.OnePoint.FiniteProfileGaussian
public import Critical2DKPZ.Polymer.BlockMeasurability
public import Critical2DKPZ.Polymer.WalkKernel
public import Critical2DKPZ.Gaussian.TimeBlocks
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.Tactic

/-! # Annealing monotonicity for reciprocal smoothed polymer masses -/

@[expose] public noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.OnePoint

private theorem pointToPoint_resample_before_future (β : ℝ) {s s' n : ℕ}
    (hss' : s ≤ s') (_hs'n : s' ≤ n) (y z : Site) (ω ξ : Disorder) :
    Critical2DKPZ.pointToPoint β s (s' - s) y z
        (Gaussian.resample (Gaussian.timeBlock s' n) ω ξ) =
      Critical2DKPZ.pointToPoint β s (s' - s) y z ξ := by
  rw [Polymer.pointToPoint_eq_sum, Polymer.pointToPoint_eq_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hweight : Polymer.pathWeight β s y p
      (Gaussian.resample (Gaussian.timeBlock s' n) ω ξ) =
        Polymer.pathWeight β s y p ξ := by
    unfold Polymer.pathWeight
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_Icc.mp hj
    have htime : (s + j, Critical2DKPZ.walkPosition y p j) ∉ Gaussian.timeBlock s' n := by
      simp [Gaussian.timeBlock]
      omega
    simp [Gaussian.resample, htime]
  rw [hweight]

private theorem pointToPlane_resample_in_future (β : ℝ) {s' n : ℕ}
    (hs'n : s' ≤ n) (z : Site) (ω ξ : Disorder) :
    Critical2DKPZ.pointToPlane β s' (n - s') z
        (Gaussian.resample (Gaussian.timeBlock s' n) ω ξ) =
      Critical2DKPZ.pointToPlane β s' (n - s') z ω := by
  rw [Polymer.pointToPlane_eq_sum, Polymer.pointToPlane_eq_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hweight : Polymer.pathWeight β s' z p
      (Gaussian.resample (Gaussian.timeBlock s' n) ω ξ) =
        Polymer.pathWeight β s' z p ω := by
    unfold Polymer.pathWeight
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_Icc.mp hj
    have htime : (s' + j, Critical2DKPZ.walkPosition z p j) ∈ Gaussian.timeBlock s' n := by
      simp [Gaussian.timeBlock]
      constructor <;> omega
    simp [Gaussian.resample, htime]
  rw [hweight]

private theorem smoothed_resample_future_formula (β : ℝ) (s s' n : ℕ)
    (hss' : s ≤ s') (hs'n : s' ≤ n) (x : Site) (ω ξ : Disorder) :
    Critical2DKPZ.smoothedP2Plane β s n x
        (Gaussian.resample (Gaussian.timeBlock s' n) ω ξ) =
      ∑ y ∈ Polymer.endpoints x s, Critical2DKPZ.srwKernel s (y - x) *
        ∑' z, Critical2DKPZ.pointToPoint β s (s' - s) y z ξ *
          Critical2DKPZ.pointToPlane β s' (n - s') z ω := by
  rw [Polymer.smoothedP2Plane_eq_sum]
  apply Finset.sum_congr rfl
  intro y hy
  have hsplit : n - s = (s' - s) + (n - s') := by omega
  rw [hsplit, Polymer.pointToPlane_chapmanKolmogorov]
  have hstart : s + (s' - s) = s' := by omega
  rw [hstart]
  congr 1
  apply tsum_congr
  intro z
  rw [pointToPoint_resample_before_future β hss' hs'n,
    pointToPlane_resample_in_future β hs'n]

private theorem integral_smoothed_resample_future (β : ℝ) (s s' n : ℕ)
    (hss' : s ≤ s') (hs'n : s' ≤ n) (x : Site) (ω : Disorder) :
    ∫ ξ, Critical2DKPZ.smoothedP2Plane β s n x
        (Gaussian.resample (Gaussian.timeBlock s' n) ω ξ) ∂disorderLaw =
      Critical2DKPZ.smoothedP2Plane β s' n x ω := by
  simp_rw [smoothed_resample_future_formula β s s' n hss' hs'n x ω]
  let A := Polymer.endpoints x s
  let m := s' - s
  let U := Polymer.endpoints x (s + m)
  have hm : s + m = s' := by dsimp [m]; omega
  have hU : U = Polymer.endpoints x s' := by simp [U, hm]
  have hcompose (y z : Site) (hy : y ∈ A)
      (hz : z ∈ Polymer.endpoints y m) : z ∈ U := by
    have ⟨p, hp⟩ := (Polymer.mem_endpoints_iff x y s).mp (by simpa [A] using hy)
    have ⟨q, hq⟩ := (Polymer.mem_endpoints_iff y z m).mp hz
    apply (Polymer.mem_endpoints_iff x z (s + m)).2
    refine ⟨Fin.append p q, ?_⟩
    rw [Polymer.walkPosition_append_end, hp]
    exact hq
  have hqSupport (y : Site) (hy : y ∈ A) {z : Site} (hz : z ∉ U) :
      Critical2DKPZ.srwKernel m (z - y) = 0 := by
    apply Polymer.srwKernel_eq_zero_of_not_mem
    intro hz'
    exact hz (hcompose y z hy hz')
  have hqConv (z : Site) :
      (∑ y ∈ A, Critical2DKPZ.srwKernel s (y - x) * Critical2DKPZ.srwKernel m (z - y)) =
        Critical2DKPZ.srwKernel (s + m) (z - x) := by
    have hconv := Polymer.srwKernel_convolution s m x z
    have hsum : (∑' y, Critical2DKPZ.srwKernel s (y - x) * Critical2DKPZ.srwKernel m (z - y)) =
        ∑ y ∈ A, Critical2DKPZ.srwKernel s (y - x) * Critical2DKPZ.srwKernel m (z - y) := by
      apply tsum_eq_sum
      intro y hy
      rw [Polymer.srwKernel_eq_zero_of_not_mem s x y (by simpa [A] using hy), zero_mul]
    calc
      _ = ∑' y, Critical2DKPZ.srwKernel s (y - x) * Critical2DKPZ.srwKernel m (z - y) :=
        hsum.symm
      _ = Critical2DKPZ.srwKernel (s + m) (z - x) := hconv.symm
  have hright : Critical2DKPZ.smoothedP2Plane β s' n x ω =
      ∑ z ∈ U, Critical2DKPZ.srwKernel s' (z - x) *
        Critical2DKPZ.pointToPlane β s' (n - s') z ω := by
    rw [hU]
    exact Polymer.smoothedP2Plane_eq_sum β s' n x ω
  calc
    _ = ∑ y ∈ A, Critical2DKPZ.srwKernel s (y - x) *
          ∑' z, Critical2DKPZ.srwKernel m (z - y) *
            Critical2DKPZ.pointToPlane β s' (n - s') z ω := by
          rw [integral_finsetSum _ fun y _ =>
            (memLp_one_iff_integrable.mp
              (Polymer.memLp_terminalProfile β s m y
                (fun z => Critical2DKPZ.pointToPlane β s' (n - s') z ω)
                1 (by norm_num))).const_mul _]
          apply Finset.sum_congr rfl
          intro y hy
          rw [integral_const_mul, Polymer.integral_terminalProfile]
    _ = ∑ z ∈ U, Critical2DKPZ.srwKernel s' (z - x) *
          Critical2DKPZ.pointToPlane β s' (n - s') z ω := by
          calc
            _ = ∑ y ∈ A, ∑ z ∈ U,
                  Critical2DKPZ.srwKernel s (y - x) * Critical2DKPZ.srwKernel m (z - y) *
                    Critical2DKPZ.pointToPlane β s' (n - s') z ω := by
                    apply Finset.sum_congr rfl
                    intro y hy
                    rw [tsum_eq_sum (s := U)]
                    · rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro z hz
                      ring
                    · intro z hz
                      rw [hqSupport y hy hz]
                      simp
            _ = ∑ z ∈ U, ∑ y ∈ A,
                  Critical2DKPZ.srwKernel s (y - x) * Critical2DKPZ.srwKernel m (z - y) *
                    Critical2DKPZ.pointToPlane β s' (n - s') z ω := by
                    rw [Finset.sum_comm]
            _ = ∑ z ∈ U, Critical2DKPZ.srwKernel s' (z - x) *
                  Critical2DKPZ.pointToPlane β s' (n - s') z ω := by
                    apply Finset.sum_congr rfl
                    intro z hz
                    rw [← Finset.sum_mul]
                    rw [hqConv, hm]
    _ = Critical2DKPZ.smoothedP2Plane β s' n x ω := hright.symm

/-- Reciprocal moments decrease as more initial time slabs are annealed. -/
theorem integral_inv_smoothedP2Plane_anti (β : ℝ) (x : Site) {s s' n : ℕ}
    (hss' : s ≤ s') (hs'n : s' ≤ n) :
      ∫ ω, (Critical2DKPZ.smoothedP2Plane β s' n x ω)⁻¹ ∂disorderLaw ≤
      ∫ ω, (Critical2DKPZ.smoothedP2Plane β s n x ω)⁻¹ ∂disorderLaw := by
  let X := Critical2DKPZ.smoothedP2Plane β s n x
  let Y := Critical2DKPZ.smoothedP2Plane β s' n x
  have hXpos (ω : Disorder) : 0 < X ω := Polymer.smoothedP2Plane_pos β s n x ω
  have hYpos (ω : Disorder) : 0 < Y ω := Polymer.smoothedP2Plane_pos β s' n x ω
  have hXnonneg (ω : Disorder) : 0 ≤ X ω := (hXpos ω).le
  have hXmeas : Measurable X := Polymer.measurable_smoothedP2Plane β s n x
  have hXint : Integrable X disorderLaw := by
    exact memLp_one_iff_integrable.mp
      (Polymer.memLp_smoothedP2Plane β s n x 1 (by norm_num))
  have hYint : Integrable Y disorderLaw := by
    exact memLp_one_iff_integrable.mp
      (Polymer.memLp_smoothedP2Plane β s' n x 1 (by norm_num))
  have hXinvInt : Integrable (fun ω => (X ω)⁻¹) disorderLaw := by
    have h := integrable_rpow_smoothedP2Plane β s n x (-1)
    have heq : (fun ω => X ω ^ (-1 : ℝ)) = fun ω => (X ω)⁻¹ := by
      funext ω
      exact Real.rpow_neg_one _
    rw [← heq]
    exact h
  have hYinvInt : Integrable (fun ω => (Y ω)⁻¹) disorderLaw := by
    have h := integrable_rpow_smoothedP2Plane β s' n x (-1)
    have heq : (fun ω => Y ω ^ (-1 : ℝ)) = fun ω => (Y ω)⁻¹ := by
      funext ω
      exact Real.rpow_neg_one _
    rw [← heq]
    exact h
  have hYinvSqInt : Integrable (fun ω => (Y ω)⁻¹ ^ 2) disorderLaw := by
    have h := integrable_rpow_smoothedP2Plane β s' n x (-2)
    have heq : (fun ω => Y ω ^ (-2 : ℝ)) = fun ω => (Y ω)⁻¹ ^ 2 := by
      funext ω
      rw [show (-2 : ℝ) = (-1 : ℝ) * 2 by norm_num,
        Real.rpow_mul (hYpos ω).le, Real.rpow_neg_one]
      exact Real.rpow_natCast _ 2
    rw [← heq]
    exact h
  have hCE := Gaussian.condExp_disorderBlock_ae_eq s' n hXmeas hXint
  have hm : Gaussian.disorderBlock s' n ≤
      (inferInstance : MeasurableSpace Disorder) := Gaussian.disorderBlock_le s' n
  have hshiftInt (ε : ℝ) (hε : 0 < ε) (Z : Disorder → ℝ) (hZmeas : Measurable Z)
      (hZnonneg : ∀ ω, 0 ≤ Z ω) :
      Integrable (fun ω => (ε + Z ω)⁻¹) disorderLaw := by
    apply (integrable_const (ε⁻¹)).mono'
    · have hmeas : Measurable (fun ω : Disorder => ε + Z ω) :=
          (measurable_const : Measurable (fun _ : Disorder => ε)).add hZmeas
      exact hmeas.inv.aestronglyMeasurable
    · filter_upwards with ω
      have hden : 0 < ε + Z ω := by linarith [hε, hZnonneg ω]
      have hbound : (ε + Z ω)⁻¹ ≤ ε⁻¹ := by
        apply (inv_le_inv₀ hden hε).2
        linarith [hZnonneg ω]
      simpa only [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hden),
        abs_of_pos (inv_pos.mpr hε)] using hbound
  have hshift (ε : ℝ) (hε : 0 < ε) :
      ∫ ω, (ε + Y ω)⁻¹ ∂disorderLaw ≤
        ∫ ω, (ε + X ω)⁻¹ ∂disorderLaw := by
    let φ : ℝ → ℝ := fun z => (ε + z)⁻¹
    let shift : ℝ →ᵃ[ℝ] ℝ :=
      (AffineMap.toConstProdLinearMap ℝ).symm (ε, LinearMap.id)
    have hshift_apply (z : ℝ) : shift z = ε + z := by
      simp [shift, AffineMap.toConstProdLinearMap_symm_apply]
      ring
    have hdomain : Set.Ici (0 : ℝ) ⊆ shift ⁻¹' Set.Ioi 0 := by
      intro z hz
      simp only [Set.mem_preimage, Set.mem_Ioi]
      rw [hshift_apply]
      have hz' : 0 ≤ z := hz
      linarith
    have hconv : ConvexOn ℝ (Set.Ici (0 : ℝ)) φ := by
      have h := (convexOn_zpow (-1 : ℤ)).comp_affineMap shift
      have h := h.subset hdomain (convex_Ici (0 : ℝ))
      have hfun : (fun z : ℝ => z ^ (-1 : ℤ)) ∘ shift = φ := by
        funext z
        rw [Function.comp_apply, hshift_apply, zpow_neg_one]
      rw [hfun] at h
      exact h
    have hcont : ContinuousOn φ (Set.Ici (0 : ℝ)) := by
      change ContinuousOn (fun z : ℝ => (ε + z)⁻¹) (Set.Ici 0)
      apply ContinuousOn.inv₀ (continuous_const.continuousOn.add continuousOn_id)
      intro z hz
      have hz' : 0 ≤ z := hz
      exact (by linarith [hε, hz'] : ε + z ≠ 0)
    have hphiInt : Integrable (fun ω => φ (X ω)) disorderLaw := by
      simpa only [φ] using hshiftInt ε hε X hXmeas hXnonneg
    have hJ := hconv.map_condExp_le hm hcont.lowerSemicontinuousOn
      (Filter.Eventually.of_forall hXnonneg) isClosed_Ici hXint hphiInt
    have hCEY : disorderLaw[X | Gaussian.disorderBlock s' n] =ᵐ[disorderLaw] Y := by
      filter_upwards [hCE] with ω hω
      rw [hω]
      exact integral_smoothed_resample_future β s s' n hss' hs'n x ω
    have hCEφ := hCEY.fun_comp φ
    have hleftInt : Integrable
        (fun ω => φ (disorderLaw[X | Gaussian.disorderBlock s' n] ω)) disorderLaw := by
      apply (hshiftInt ε hε Y
        (Polymer.measurable_smoothedP2Plane β s' n x) (fun ω => (hYpos ω).le)).congr
      exact hCEφ.symm
    calc
      _ = ∫ ω, φ (disorderLaw[X | Gaussian.disorderBlock s' n] ω) ∂disorderLaw := by
            apply integral_congr_ae
            exact hCEφ.symm
      _ ≤ ∫ ω, disorderLaw[φ ∘ X | Gaussian.disorderBlock s' n] ω ∂disorderLaw :=
            integral_mono_ae hleftInt integrable_condExp hJ
      _ = ∫ ω, φ (X ω) ∂disorderLaw := integral_condExp hm
  let IX := ∫ ω, (X ω)⁻¹ ∂disorderLaw
  let IY := ∫ ω, (Y ω)⁻¹ ∂disorderLaw
  let M := ∫ ω, (Y ω)⁻¹ ^ 2 ∂disorderLaw
  have hMnonneg : 0 ≤ M := integral_nonneg fun ω => sq_nonneg ((Y ω)⁻¹)
  have hbound (ε : ℝ) (hε : 0 < ε) : IY ≤ IX + ε * M := by
    have hshiftY := hshiftInt ε hε Y
      (Polymer.measurable_smoothedP2Plane β s' n x) (fun ω => (hYpos ω).le)
    have hshiftX := hshiftInt ε hε X hXmeas hXnonneg
    have happrox (ω : Disorder) :
        (Y ω)⁻¹ ≤ (ε + Y ω)⁻¹ + ε * (Y ω)⁻¹ ^ 2 := by
      have hy : 0 < Y ω := hYpos ω
      have hden : 0 < ε + Y ω := by linarith [hε, hy]
      have hiden : (ε + Y ω)⁻¹ + ε * (Y ω)⁻¹ ^ 2 - (Y ω)⁻¹ =
          ε ^ 2 / ((Y ω) ^ 2 * (ε + Y ω)) := by
        field_simp [ne_of_gt hy, ne_of_gt hden]
        ring
      rw [← sub_nonneg]
      rw [hiden]
      positivity
    have hsumInt : Integrable
        (fun ω => (ε + Y ω)⁻¹ + ε * (Y ω)⁻¹ ^ 2) disorderLaw :=
      hshiftY.add (hYinvSqInt.const_mul ε)
    have hmono := integral_mono_ae hYinvInt hsumInt
      (Filter.Eventually.of_forall happrox)
    have hsum := integral_add hshiftY (hYinvSqInt.const_mul ε)
    rw [hsum, integral_const_mul] at hmono
    have hpoint (ω : Disorder) : (ε + X ω)⁻¹ ≤ (X ω)⁻¹ := by
      have hden : 0 < ε + X ω := by linarith [hε, hXpos ω]
      apply (inv_le_inv₀ hden (hXpos ω)).2
      linarith
    have hmonoX := integral_mono_ae hshiftX hXinvInt
      (Filter.Eventually.of_forall hpoint)
    have hshiftXY := hshift ε hε
    calc
      IY ≤ (∫ ω, (ε + Y ω)⁻¹ ∂disorderLaw) + ε * M := by
        dsimp [IY, M]
        linarith
      _ ≤ (∫ ω, (ε + X ω)⁻¹ ∂disorderLaw) + ε * M := add_le_add hshiftXY le_rfl
      _ ≤ IX + ε * M := by
        dsimp [IX]
        nlinarith [hmonoX]
  by_contra hnot
  have hlt : IX < IY := lt_of_not_ge hnot
  let ε := (IY - IX) / (M + 1)
  have hε : 0 < ε := div_pos (sub_pos.mpr hlt) (by linarith [hMnonneg])
  have hratio : M / (M + 1) < 1 := by
    apply (div_lt_iff₀ (by linarith [hMnonneg] : 0 < M + 1)).2
    linarith
  have hprod : ε * M < IY - IX := by
    calc
      ε * M = (IY - IX) * (M / (M + 1)) := by dsimp [ε]; ring
      _ < (IY - IX) * 1 := mul_lt_mul_of_pos_left hratio (sub_pos.mpr hlt)
      _ = IY - IX := by ring
  have hfinal := hbound ε hε
  dsimp [IX, IY] at hlt hfinal
  linarith

end Critical2DKPZ.OnePoint

end
