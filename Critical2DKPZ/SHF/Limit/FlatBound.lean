/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Limit.LocalFinite
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # The annealed flat-pairing bound -/

@[expose] public section

open MeasureTheory
open scoped CompactlySupported ENNReal Topology

noncomputable section

namespace Critical2DKPZ.SHF.Limit

private theorem measurable_uncurry_pointToPlane (β : ℝ) (a n : ℕ) :
    Measurable (fun q : Site × Disorder => pointToPlane β a n q.1 q.2) :=
  measurable_from_prod_countable_right
    (f := fun q : Site × Disorder => pointToPlane β a n q.1 q.2)
    (fun w => Polymer.measurable_pointToPlane β a n w)

/-- The rescaled point-to-plane partition function is jointly measurable in the starting point and disorder. -/
theorem measurable_uncurry_rescaledP2Plane (ϑ : ℝ) (N : ℕ) (s t : ℝ) :
    Measurable (fun q : Plane × Disorder => rescaledP2Plane ϑ N s t q.1 q.2) := by
  simpa only [rescaledP2Plane, Function.comp_def] using
   (measurable_uncurry_pointToPlane (criticalBeta ϑ N)
      (evenCeil ((N : ℝ) * s))
      (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s))).comp
    ((((measurable_latticePoint N).comp measurable_fst).prodMk measurable_snd))

/-- For integrable `f`, the flat pairing integrand `f x * rescaledP2Plane ϑ N s t x ω` is
integrable on `Plane × Disorder`: the density is nonnegative with unit annealed mean. -/
theorem integrable_flatPairingProduct (ϑ : ℝ) (N : ℕ) (s t : ℝ)
    {f : Plane → ℝ} (hf : Integrable f) :
    Integrable (fun q : Plane × Disorder => f q.1 * rescaledP2Plane ϑ N s t q.1 q.2)
      (volume.prod disorderLaw) := by
  have hden := measurable_uncurry_rescaledP2Plane ϑ N s t
  have hm : AEStronglyMeasurable (fun q : Plane × Disorder =>
      f q.1 * rescaledP2Plane ϑ N s t q.1 q.2) (volume.prod disorderLaw) :=
    hf.aestronglyMeasurable.comp_fst.mul hden.aestronglyMeasurable
  apply (integrable_prod_iff hm).2
  constructor
  · exact Filter.Eventually.of_forall fun x => by
      change Integrable (fun ω => f x * pointToPlane (criticalBeta ϑ N)
        (evenCeil ((N : ℝ) * s)) (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s))
        (latticePoint N x) ω) disorderLaw
      simpa only [mul_comm] using
        (Polymer.integrable_pointToPlane (criticalBeta ϑ N)
          (evenCeil ((N : ℝ) * s))
          (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s))
          (latticePoint N x)).const_mul (f x)
  · have hmean (x : Plane) :
        (∫ ω, ‖f x * rescaledP2Plane ϑ N s t x ω‖ ∂disorderLaw) = |f x| := by
      simp_rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (rescaledP2Plane_nonneg ϑ N s t x _)]
      rw [integral_const_mul, integral_rescaledP2Plane, mul_one]
    change Integrable (fun x : Plane =>
      ∫ ω, ‖f x * rescaledP2Plane ϑ N s t x ω‖ ∂disorderLaw) volume
    simp_rw [hmean]
    exact hf.norm

private theorem integrable_abs_flatKernelPairing (ϑ : ℝ) (N : ℕ) (s t : ℝ)
    {f : Plane → ℝ} (hf : Integrable f) :
    Integrable (fun ω : Disorder =>
      |∫ x, f x * rescaledP2Plane ϑ N s t x ω ∂volume|) disorderLaw := by
  let G : Plane × Disorder → ℝ :=
    fun q => f q.1 * rescaledP2Plane ϑ N s t q.1 q.2
  have hG : Integrable G (volume.prod disorderLaw) :=
    integrable_flatPairingProduct ϑ N s t hf
  have hGswap : Integrable (fun q : Disorder × Plane => G (q.2, q.1))
      (disorderLaw.prod volume) := hG.swap
  have hPair : AEStronglyMeasurable (fun ω : Disorder =>
      ∫ x, G (x, ω) ∂volume) disorderLaw := by
    simpa only [G, Prod.fst, Prod.snd] using
      hGswap.aestronglyMeasurable.integral_prod_right'
  have hUpper : Integrable (fun ω : Disorder =>
      ∫ x, ‖G (x, ω)‖ ∂volume) disorderLaw :=
    (integrable_prod_iff hGswap.aestronglyMeasurable).mp hGswap |>.2
  have hAbs : Integrable (fun ω : Disorder =>
      |∫ x, G (x, ω) ∂volume|) disorderLaw := by
    apply hUpper.mono'
    · simpa only [Real.norm_eq_abs] using hPair.norm
    · filter_upwards [] with ω
      calc
        ‖|∫ x, G (x, ω) ∂volume|‖ = |∫ x, G (x, ω) ∂volume| := by simp
        _ = ‖∫ x, G (x, ω) ∂volume‖ := by rw [Real.norm_eq_abs]
        _ ≤ ∫ x, ‖G (x, ω)‖ ∂volume := norm_integral_le_integral_norm _
  simpa only [G] using hAbs

/-- The absolute value of a flat polymer pairing with an integrable initial test is integrable in disorder. -/
theorem integrable_flat_polymerMeasure_pairing (ϑ : ℝ) {N : ℕ} (hN : 1 ≤ N)
    (s t : ℝ) (f : Plane → ℝ) (hf : Integrable f) :
    Integrable (fun ω =>
      |∫ x, f x ∂((polymerMeasure ϑ N s t ω).map Prod.fst)|) disorderLaw := by
  have hKernel := integrable_abs_flatKernelPairing ϑ N s t hf
  have hEq : (fun ω =>
      |∫ x, f x ∂((polymerMeasure ϑ N s t ω).map Prod.fst)|) =ᵐ[disorderLaw]
      (fun ω => |∫ x, f x * rescaledP2Plane ϑ N s t x ω ∂volume|) := by
    filter_upwards [] with ω
    rw [integral_map_fst_polymerMeasure ϑ hN s t ω f]
  exact hKernel.congr hEq.symm

/-- Every natural power of the flat pairing against a compactly supported
test is integrable. The finite endpoint-site support reduces this to the
point-to-plane moment bounds. -/
theorem integrable_flat_polymerMeasure_pow (ϑ : ℝ) (N : ℕ) (s t : ℝ)
    (χ : C_c(Plane, ℝ)) (p : ℕ) :
    Integrable (fun ω =>
      (∫ x, |χ x| ∂((polymerMeasure ϑ N s t ω).map Prod.fst)) ^ p) disorderLaw := by
  classical
  let f : Plane → ℝ := fun x => |χ x|
  let H : Disorder → ℝ := fun ω =>
    ∫ x, f x ∂((polymerMeasure ϑ N s t ω).map Prod.fst)
  change Integrable (fun ω => H ω ^ p) disorderLaw
  by_cases hN0 : N = 0
  · subst N
    have hzero (ω : Disorder) : polymerMeasure ϑ 0 s t ω = 0 := by
      rw [polymerMeasure]
      ext A hA
      simp [rescaledP2P]
    have hHzero : H = 0 := by
      funext ω
      simp [H, hzero]
    simp [hHzero]
  · have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
    have hf : Integrable f volume := by
      simpa [f] using (χ.continuous.integrable_of_hasCompactSupport
        χ.hasCompactSupport).norm
    have hfnonneg (x : Plane) : 0 ≤ f x := abs_nonneg _
    let K : Set Plane := tsupport (χ : Plane → ℝ)
    have hK : IsCompact K := χ.hasCompactSupport
    let sites : Finset Site :=
      (finite_latticePoint_image_of_bounded (N := N) hK.isBounded).toFinset
    let β := criticalBeta ϑ N
    let a := evenCeil ((N : ℝ) * s)
    let n := evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)
    let S : Disorder → ℝ := fun ω =>
      ∑ z ∈ sites, pointToPlane β a n z ω
    have hSnonneg (ω : Disorder) : 0 ≤ S ω := by
      apply Finset.sum_nonneg
      intro z hz
      exact (Polymer.pointToPlane_pos β a n z ω).le
    have hV : 0 ≤ ∫ x, f x := integral_nonneg (fun x => hfnonneg x)
    have hbound (ω : Disorder) : H ω ≤ (∫ x, f x) * S ω := by
      have hkernel (x : Plane) :
          f x * rescaledP2Plane ϑ N s t x ω ≤ f x * S ω := by
        by_cases hx : χ x = 0
        · simp [f, hx]
        · have hxSupport : x ∈ Function.support (χ : Plane → ℝ) :=
            Function.mem_support.mpr hx
          have hxK : x ∈ K := subset_closure hxSupport
          have hsite : latticePoint N x ∈ sites := by
            have hfinite := finite_latticePoint_image_of_bounded (N := N) hK.isBounded
            have hxImage : latticePoint N x ∈ latticePoint N '' K := ⟨x, hxK, rfl⟩
            change latticePoint N x ∈ hfinite.toFinset
            exact hfinite.mem_toFinset.mpr hxImage
          have hsum : pointToPlane β a n (latticePoint N x) ω ≤ S ω :=
            Finset.single_le_sum
              (fun z hz => (Polymer.pointToPlane_pos β a n z ω).le) hsite
          change |χ x| * pointToPlane β a n (latticePoint N x) ω ≤ _
          exact mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
      have hres : Measurable (fun x : Plane => rescaledP2Plane ϑ N s t x ω) :=
        (measurable_uncurry_rescaledP2Plane ϑ N s t).of_uncurry_right
      have hGmeas : Measurable (fun x : Plane => f x * rescaledP2Plane ϑ N s t x ω) :=
        (χ.continuous.abs.measurable).mul hres
      have hupper : Integrable (fun x : Plane => f x * S ω) volume := by
        simpa only [f, mul_comm] using hf.const_mul (S ω)
      have hG : Integrable (fun x : Plane => f x * rescaledP2Plane ϑ N s t x ω)
          volume := by
        apply hupper.mono' hGmeas.aestronglyMeasurable
        filter_upwards [] with x
        have hkernelNonneg : 0 ≤ rescaledP2Plane ϑ N s t x ω :=
          rescaledP2Plane_nonneg ϑ N s t x ω
        calc
          ‖f x * rescaledP2Plane ϑ N s t x ω‖ =
              f x * rescaledP2Plane ϑ N s t x ω := by
                rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hfnonneg x) hkernelNonneg)]
          _ ≤ f x * S ω := hkernel x
      calc
        H ω = ∫ x, f x * rescaledP2Plane ϑ N s t x ω :=
          integral_map_fst_polymerMeasure ϑ hN s t ω f
        _ ≤ ∫ x, f x * S ω := by
          apply integral_mono_ae hG hupper
          exact Filter.Eventually.of_forall hkernel
        _ = (∫ x, f x) * S ω := by rw [integral_mul_const]
    have hsumLp : MemLp S (p : ℝ≥0∞) disorderLaw := by
      exact memLp_finsetSum _ fun z hz =>
        Polymer.memLp_pointToPlane β a n z (p : ℝ≥0∞) (by simp)
    have hsumPow : Integrable (fun ω => S ω ^ p) disorderLaw := by
      have hpow := hsumLp.integrable_norm_pow'
      apply hpow.congr
      filter_upwards [] with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (hSnonneg ω)]
    have hupperPow : Integrable (fun ω => (∫ x, f x) ^ p * S ω ^ p) disorderLaw := by
      simpa only [mul_comm] using hsumPow.const_mul ((∫ x, f x) ^ p)
    have hH : Integrable H disorderLaw := by
      have h := integrable_flat_polymerMeasure_pairing ϑ hN s t f hf
      apply h.congr
      filter_upwards [] with ω
      dsimp [H]
      rw [abs_of_nonneg (integral_nonneg (fun x => hfnonneg x))]
    apply hupperPow.mono' (hH.aestronglyMeasurable.pow p)
    filter_upwards [] with ω
    have hHnonneg : 0 ≤ H ω := integral_nonneg (fun x => hfnonneg x)
    have hboundPow : H ω ^ p ≤ (∫ x, f x) ^ p * S ω ^ p := by
      calc
        H ω ^ p ≤ ((∫ x, f x) * S ω) ^ p :=
          pow_le_pow_left₀ hHnonneg (hbound ω) p
        _ = (∫ x, f x) ^ p * S ω ^ p := mul_pow _ _ _
    calc
      ‖H ω ^ p‖ = H ω ^ p := by rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hHnonneg _)]
      _ ≤ (∫ x, f x) ^ p * S ω ^ p := hboundPow

/-- A flat pairing with the rescaled point-to-plane density is almost everywhere measurable. -/
theorem aemeasurable_rescaledP2Plane_pairing (ϑ : ℝ) (N : ℕ) (s t : ℝ)
    (f : C_c(Plane, ℝ)) :
    AEMeasurable (fun ω => ∫ x, f x * rescaledP2Plane ϑ N s t x ω ∂volume)
      disorderLaw := by
  have hf : Integrable (f : Plane → ℝ) :=
    f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  let G : Plane × Disorder → ℝ :=
    fun q => f q.1 * rescaledP2Plane ϑ N s t q.1 q.2
  have hG : Integrable G (volume.prod disorderLaw) :=
    integrable_flatPairingProduct ϑ N s t hf
  have hswap : Integrable (fun q : Disorder × Plane => G (q.2, q.1))
      (disorderLaw.prod volume) := hG.swap
  simpa only [G, Prod.fst, Prod.snd] using
    hswap.aestronglyMeasurable.integral_prod_right'.aemeasurable


end Critical2DKPZ.SHF.Limit

end
