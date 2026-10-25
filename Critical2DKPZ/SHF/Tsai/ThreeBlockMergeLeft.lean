/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ThreeBlockMergeRight

/-! # Composition of the initial two blocks

At a fixed terminal connector, the initial two flow increments compose in expectations of
bounded smooth observables. Conditioning on the terminal block gives `L²` endpoint tests
for the two-increment composition limit.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology CompactlySupported BoundedContinuousFunction

namespace Critical2DKPZ.SHF.Tsai

/-- At a fixed right connector, the left two flow increments merge in tested expectation. -/
theorem tendsto_integral_threeBlockPairing_merge_left {θ : ℝ} (D : Set ℝ) {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane)) (hZ' : IsDenseSHF θ D P' Z')
    (C : Ω → Measure (Plane × Plane)) {τC : ℝ} (hτC : 0 < τC) (hC : HasDeltaBoseMoments θ τC P C)
    {s a b : ℝ} (hs : s ∈ D) (ha : a ∈ D) (hb : b ∈ D) (hsa : s < a) (hab : a < b)
    (u : ℕ → Plane → ℝ) (hu : IsL2ApplicableMollifier u) {m r : ℕ} (g g' : Fin m → Fin r → C_c(Plane, ℝ))
    (H : (Fin m → ℝ) → ℝ) (hH : ContDiff ℝ 4 H) (CH : ℝ) (hCH : ∀ k ≤ 4, ∀ x, ‖iteratedFDeriv ℝ k H x‖ ≤ CH)
    (ℓ : ℕ) :
    Tendsto (fun ℓ'' => ∫ ω, H (threeBlockPairing ![fun ω : Ω' × Ω => Z' s a ω.1, fun ω => Z' a b ω.1,
        fun ω => C ω.2] u g g' ℓ'' ℓ ω) ∂(P'.prod P)) atTop
      (𝓝 (∫ ω, H (fun i => ∑ k, ∫ p, g i k p.1 * g' i k p.2 ∂(smoothedProductMeasure (Z' s b ω.1) (u ℓ)
        (C ω.2))) ∂(P'.prod P))) := by
  classical
  let Q := P.prod P'
  let Bs (i : Fin 2) := if (i : ℕ) = 0 then Z' s a else Z' a b
  have hBs (i : Fin 2) : Measurable (Bs i) := by
    fin_cases i
    · exact (hZ'.1 s hs a ha hsa).1
    · exact (hZ'.1 a ha b hb hab).1
  let E3 (i : Fin 3) (ω : Ω × Ω') :=
    Fin.snoc (α := fun _ : Fin 3 => Measure (Plane × Plane)) (fun j => Bs j ω.2) (C ω.1) i
  let σ : Fin 3 → ℝ := ![a - s, b - a, τC]
  have hσ (i : Fin 3) : 0 < σ i := by
    fin_cases i
    · exact sub_pos.mpr hsa
    · exact sub_pos.mpr hab
    · exact hτC
  have hE3 (i : Fin 3) : HasDeltaBoseMoments θ (σ i) Q (E3 i) := by
    fin_cases i
    · exact (hZ'.hasDeltaBoseMoments hs ha hsa).comp_measurePreserving measurePreserving_snd
    · exact (hZ'.hasDeltaBoseMoments ha hb hab).comp_measurePreserving measurePreserving_snd
    · exact hC.comp_measurePreserving measurePreserving_fst
  have hindE3 : iIndepFun E3 Q := iIndepFun_fin_snoc_prod P' P C Bs hC.1 hBs
    (hZ'.iIndepFun_twoConsecutive hs ha hb hsa hab)
  let E2 (i : Fin 2) (ω : Ω × Ω') :=
    Fin.snoc (α := fun _ : Fin 2 => Measure (Plane × Plane)) (fun _ => Z' s b ω.2) (C ω.1) i
  let κ : Fin 2 → ℝ := ![b - s, τC]
  have hκ (i : Fin 2) : 0 < κ i := by
    fin_cases i
    · exact sub_pos.mpr (hsa.trans hab)
    · exact hτC
  have hE2 (i : Fin 2) : HasDeltaBoseMoments θ (κ i) Q (E2 i) := by
    fin_cases i
    · exact (hZ'.hasDeltaBoseMoments hs hb (hsa.trans hab)).comp_measurePreserving measurePreserving_snd
    · exact hC.comp_measurePreserving measurePreserving_fst
  have hind1 : iIndepFun (fun _ : Fin 1 => Z' s b) P' := by
    let : Subsingleton (Fin 1) := ⟨fun i j => Fin.ext (by omega)⟩
    exact iIndepFun.of_subsingleton
  have hindE2 : iIndepFun E2 Q := iIndepFun_fin_snoc_prod P' P C (fun _ : Fin 1 => Z' s b) hC.1
    (fun _ => (hZ'.1 s hs b hb (hsa.trans hab)).1) hind1
  let X (n : ℕ) (ω : Ω × Ω') (i : Fin m × Fin r) := ∫ p, g i.1 i.2 p.1 * g' i.1 i.2 p.2
    ∂smoothedProductMeasure (smoothedProductMeasure (Z' s a ω.2) (u n) (Z' a b ω.2)) (u ℓ) (C ω.1)
  let Y (ω : Ω × Ω') (i : Fin m × Fin r) := ∫ p, g i.1 i.2 p.1 * g' i.1 i.2 p.2
    ∂smoothedProductMeasure (Z' s b ω.2) (u ℓ) (C ω.1)
  have hg (i : Fin m × Fin r) : MemLp (g i.1 i.2) 2 :=
    (map_continuous (g i.1 i.2)).memLp_of_hasCompactSupport (g i.1 i.2).hasCompactSupport
  have hg' (i : Fin m × Fin r) : MemLp (g' i.1 i.2) 2 :=
    (map_continuous (g' i.1 i.2)).memLp_of_hasCompactSupport (g' i.1 i.2).hasCompactSupport
  have hEqX (n : ℕ) (ω : Ω × Ω') :
      chainProduct (fun k => E3 (Fin.ofNat 3 k) ω) (fun k => u (if k = 0 then n else ℓ)) 2 =
      smoothedProductMeasure (smoothedProductMeasure (Z' s a ω.2) (u n) (Z' a b ω.2)) (u ℓ) (C ω.1) := rfl
  have hEqY (ω : Ω × Ω') : chainProduct (fun k => E2 (Fin.ofNat 2 k) ω) (fun _ => u ℓ) 1 =
      smoothedProductMeasure (Z' s b ω.2) (u ℓ) (C ω.1) := rfl
  have hXmoms (n : ℕ) (i : Fin m × Fin r) :
      (∀ᵐ ω ∂Q, Integrable (fun p : Plane × Plane => g i.1 i.2 p.1 * g' i.1 i.2 p.2)
        (smoothedProductMeasure (smoothedProductMeasure (Z' s a ω.2) (u n) (Z' a b ω.2)) (u ℓ) (C ω.1))) ∧
      MemLp (fun ω => X n ω i) 4 Q := by
    have h := chainPairing_four_finiteBlocks 2 σ hσ E3 hE3 hindE3
      (fun _ => u) (fun _ => hu) (fun k => if k = 0 then n else ℓ)
      (g i.1 i.2) (g' i.1 i.2) (hg i) (hg' i)
    simpa only [hEqX] using h
  have hYmoms (i : Fin m × Fin r) :
      (∀ᵐ ω ∂Q, Integrable (fun p : Plane × Plane => g i.1 i.2 p.1 * g' i.1 i.2 p.2)
        (smoothedProductMeasure (Z' s b ω.2) (u ℓ) (C ω.1))) ∧ MemLp (fun ω => Y ω i) 4 Q := by
    have h := chainPairing_four_finiteBlocks 1 κ hκ E2 hE2 hindE2
      (fun _ => u) (fun _ => hu) (fun _ => ℓ) (g i.1 i.2) (g' i.1 i.2) (hg i) (hg' i)
    simpa only [hEqY] using h
  have hXmeas (n) : AEStronglyMeasurable (X n) Q :=
    (AEMeasurable.of_eval (fun i => (hXmoms n i).2.aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
  have hYmeas : AEStronglyMeasurable Y Q :=
    (AEMeasurable.of_eval (fun i => (hYmoms i).2.aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
  have hXI : ∀ᵐ z ∂P, ∀ (n : ℕ) (i : Fin m × Fin r), ∀ᵐ ω ∂P', Integrable
      (fun p : Plane × Plane => g i.1 i.2 p.1 * g' i.1 i.2 p.2)
      (smoothedProductMeasure (smoothedProductMeasure (Z' s a ω) (u n) (Z' a b ω)) (u ℓ) (C z)) := by
    apply ae_all_iff.2
    intro n
    apply ae_all_iff.2
    intro i
    exact Measure.ae_ae_of_ae_prod (hXmoms n i).1
  have hYI : ∀ᵐ z ∂P, ∀ i : Fin m × Fin r, ∀ᵐ ω ∂P', Integrable
      (fun p : Plane × Plane => g i.1 i.2 p.1 * g' i.1 i.2 p.2)
      (smoothedProductMeasure (Z' s b ω) (u ℓ) (C z)) := by
    apply ae_all_iff.2
    intro i
    exact Measure.ae_ae_of_ae_prod (hYmoms i).1
  have htests : ∀ᵐ z ∂P, ∀ i : Fin m × Fin r,
      MemLp (fun y => ∫ p, u ℓ (y - p.1) * g' i.1 i.2 p.2 ∂C z) 2 := by
    apply ae_all_iff.2
    intro i
    exact (hC.ae_memLp_weighted_right_test hτC (g' i.1 i.2) (u ℓ)
      ((hu.2.1 ℓ).measurable) (hu.2.2.1 ℓ)).mono (fun _ h => h.1)
  have hprob : ∀ᵐ z ∂P, TendstoInMeasure P' (fun n ω => X n (z, ω)) atTop (fun ω => Y (z, ω)) := by
    filter_upwards [hC.2.1, htests, hXI, hYI] with z hz htest hzX hzY
    let : IsLocallyFiniteMeasure (C z) := hz
    apply tendstoInMeasure_fintype_pi
    intro i
    let f (y : Plane) := ∫ p, u ℓ (y - p.1) * g' i.1 i.2 p.2 ∂C z
    have hfour := isDenseSHF_smoothedProduct_tendsto_tensor θ D P' Z' hZ' hs ha hb hsa hab
      u hu (g i.1 i.2) f (hg i) (htest i)
    have hp := tendstoInMeasure_of_integrable_fourth_moments P' _ _ hfour.1 hfour.2
    have hleft (n : ℕ) : (fun ω => X n (z, ω) i) =ᵐ[P']
        fun ω => ∫ p, g i.1 i.2 p.1 * f p.2 ∂smoothedProductMeasure (Z' s a ω) (u n) (Z' a b ω) := by
      filter_upwards [hzX n i, (hZ'.1 s hs a ha hsa).2, (hZ'.1 a ha b hb hab).2]
        with ω hω hLF₁ hLF₂
      let : IsLocallyFiniteMeasure (Z' s a ω) := hLF₁
      let : IsLocallyFiniteMeasure (Z' a b ω) := hLF₂
      let : SFinite (smoothedProductMeasure (Z' s a ω) (u n) (Z' a b ω)) := by
        dsimp only [smoothedProductMeasure]
        infer_instance
      exact (integral_smoothedProduct_tensor_eq_right_average
        (smoothedProductMeasure (Z' s a ω) (u n) (Z' a b ω)) (C z)
        (u ℓ) (hu.1 ℓ) ((hu.2.1 ℓ).measurable) (g i.1 i.2) (g' i.1 i.2)
        (map_continuous _).measurable (map_continuous _).measurable hω).2
    have hright : (fun ω => Y (z, ω) i) =ᵐ[P'] fun ω => ∫ p, g i.1 i.2 p.1 * f p.2 ∂Z' s b ω := by
      filter_upwards [hzY i, (hZ'.1 s hs b hb (hsa.trans hab)).2] with ω hω hLF
      let : IsLocallyFiniteMeasure (Z' s b ω) := hLF
      exact (integral_smoothedProduct_tensor_eq_right_average (Z' s b ω) (C z)
        (u ℓ) (hu.1 ℓ) ((hu.2.1 ℓ).measurable) (g i.1 i.2) (g' i.1 i.2)
        (map_continuous _).measurable (map_continuous _).measurable hω).2
    exact hp.congr (fun n => (hleft n).symm) hright.symm
  have hH0 (x) : ‖H x‖ ≤ CH := by
    simpa only [norm_iteratedFDeriv_zero] using hCH 0 (by omega) x
  let J (x : (Fin m × Fin r) → ℝ) := H (fun a => ∑ b, x (a, b))
  have hJ : Continuous J := hH.continuous.comp
    (continuous_pi (fun a => continuous_finsetSum _ (fun b _ => continuous_apply (a, b))))
  let Hb : ((Fin m × Fin r) → ℝ) →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfBound ⟨J, hJ⟩ (2 * CH) (by
      intro x y
      exact (dist_le_norm_add_norm _ _).trans
        ((add_le_add (hH0 _) (hH0 _)).trans_eq (two_mul CH).symm))
  have h := tendsto_integral_prod_boundedContinuous_of_fiberwise_tendstoInMeasure P' P X Y
    hXmeas hYmeas hprob Hb
  have hXfun (n : ℕ) (ω : Ω' × Ω) : Hb (X n ω.swap) =
      H (threeBlockPairing ![fun ω : Ω' × Ω => Z' s a ω.1,
        fun ω => Z' a b ω.1, fun ω => C ω.2] u g g' n ℓ ω) := by
    change H (fun i => ∑ k, X n ω.swap (i, k)) = _
    congr 1
  have hXswap (n : ℕ) : (∫ ω, Hb (X n ω) ∂P.prod P') =
      ∫ ω, H (threeBlockPairing ![fun ω : Ω' × Ω => Z' s a ω.1,
        fun ω => Z' a b ω.1, fun ω => C ω.2] u g g' n ℓ ω) ∂P'.prod P := by
    calc
      _ = ∫ ω : Ω' × Ω, Hb (X n ω.swap) ∂P'.prod P :=
        integral_prod_swap (fun ω : Ω' × Ω => Hb (X n ω.swap))
      _ = _ := integral_congr_ae (Eventually.of_forall (hXfun n))
  have hYfun (ω : Ω' × Ω) : Hb (Y ω.swap) =
      H (fun i => ∑ k, ∫ p, g i k p.1 * g' i k p.2
        ∂smoothedProductMeasure (Z' s b ω.1) (u ℓ) (C ω.2)) := by
    rfl
  have hYswap : (∫ ω, Hb (Y ω) ∂P.prod P') =
      ∫ ω, H (fun i => ∑ k, ∫ p, g i k p.1 * g' i k p.2
        ∂smoothedProductMeasure (Z' s b ω.1) (u ℓ) (C ω.2)) ∂P'.prod P := by
    calc
      _ = ∫ ω : Ω' × Ω, Hb (Y ω.swap) ∂P'.prod P :=
        integral_prod_swap (fun ω : Ω' × Ω => Hb (Y ω.swap))
      _ = _ := integral_congr_ae (Eventually.of_forall hYfun)
  have hlim := h.2.2
  simpa only [hXswap, hYswap] using hlim

end Critical2DKPZ.SHF.Tsai

end
