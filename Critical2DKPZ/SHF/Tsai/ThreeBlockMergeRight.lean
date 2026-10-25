/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ThreeBlockLimits
public import Critical2DKPZ.SHF.Tsai.TwoIncrementLimits
public import Critical2DKPZ.SHF.Tsai.ChainPairingIndices
public import Critical2DKPZ.SHF.Tsai.BlockMomentTransport
public import Critical2DKPZ.SHF.Tsai.CouplingIndependence
public import Critical2DKPZ.SHF.Tsai.ConditionalExpectationLimits
public import Critical2DKPZ.SHF.Tsai.WeightedBlockTests
public import Critical2DKPZ.SHF.Tsai.ProductTensorAverages
public import Critical2DKPZ.SHF.Tsai.FourthMomentProbability

/-! # Composition of the terminal two blocks

At a fixed initial connector, the terminal two flow increments compose in expectations of
bounded smooth observables. Conditioning on the initial block gives `L²` endpoint tests
for the two-increment composition limit.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology CompactlySupported BoundedContinuousFunction

namespace Critical2DKPZ.SHF.Tsai

/-- At a fixed left connector, the right two flow increments merge in tested expectation. -/
theorem tendsto_integral_threeBlockPairing_merge_right {θ : ℝ} (D : Set ℝ) {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsDenseSHF θ D P Z)
    (A : Ω' → Measure (Plane × Plane)) {τA : ℝ} (hτA : 0 < τA) (hA : HasDeltaBoseMoments θ τA P' A)
    {a b t : ℝ} (ha : a ∈ D) (hb : b ∈ D) (ht : t ∈ D) (hab : a < b) (hbt : b < t)
    (u : ℕ → Plane → ℝ) (hu : IsL2ApplicableMollifier u) {m r : ℕ} (g g' : Fin m → Fin r → C_c(Plane, ℝ))
    (H : (Fin m → ℝ) → ℝ) (hH : ContDiff ℝ 4 H) (CH : ℝ) (hCH : ∀ k ≤ 4, ∀ x, ‖iteratedFDeriv ℝ k H x‖ ≤ CH)
    (ℓ : ℕ) :
    Tendsto (fun ℓ' => ∫ ω, H (threeBlockPairing ![fun ω : Ω' × Ω => A ω.1, fun ω => Z a b ω.2,
        fun ω => Z b t ω.2] u g g' ℓ ℓ' ω) ∂(P'.prod P)) atTop
      (𝓝 (∫ ω, H (fun i => ∑ k, ∫ p, g i k p.1 * g' i k p.2 ∂(smoothedProductMeasure (A ω.1) (u ℓ)
        (Z a t ω.2))) ∂(P'.prod P))) := by
  classical
  let Q := P'.prod P
  let Bs (i : Fin 2) := if (i : ℕ) = 0 then Z a b else Z b t
  have hBs (i : Fin 2) : Measurable (Bs i) := by
    fin_cases i
    · exact (hZ.1 a ha b hb hab).1
    · exact (hZ.1 b hb t ht hbt).1
  let C (i : Fin 3) (ω : Ω' × Ω) :=
    Fin.cons (α := fun _ : Fin 3 => Measure (Plane × Plane)) (A ω.1) (fun j => Bs j ω.2) i
  let σ : Fin 3 → ℝ := ![τA, b - a, t - b]
  have hσ (i : Fin 3) : 0 < σ i := by
    fin_cases i
    · exact hτA
    · exact sub_pos.mpr hab
    · exact sub_pos.mpr hbt
  have hC (i : Fin 3) : HasDeltaBoseMoments θ (σ i) Q (C i) := by
    fin_cases i
    · exact hA.comp_measurePreserving measurePreserving_fst
    · exact (hZ.hasDeltaBoseMoments ha hb hab).comp_measurePreserving measurePreserving_snd
    · exact (hZ.hasDeltaBoseMoments hb ht hbt).comp_measurePreserving measurePreserving_snd
  have hindC : iIndepFun C Q := iIndepFun_fin_cons_prod P P' A Bs hA.1 hBs
    (hZ.iIndepFun_twoConsecutive ha hb ht hab hbt)
  let C₂ (i : Fin 2) (ω : Ω' × Ω) :=
    Fin.cons (α := fun _ : Fin 2 => Measure (Plane × Plane)) (A ω.1)
      (fun _ => Z a t ω.2) i
  let κ : Fin 2 → ℝ := ![τA, t - a]
  have hκ (i : Fin 2) : 0 < κ i := by
    fin_cases i
    · exact hτA
    · exact sub_pos.mpr (hab.trans hbt)
  have hD (i : Fin 2) : HasDeltaBoseMoments θ (κ i) Q (C₂ i) := by
    fin_cases i
    · exact hA.comp_measurePreserving measurePreserving_fst
    · exact (hZ.hasDeltaBoseMoments ha ht (hab.trans hbt)).comp_measurePreserving measurePreserving_snd
  have hind1 : iIndepFun (fun _ : Fin 1 => Z a t) P := by
    let : Subsingleton (Fin 1) := ⟨fun i j => Fin.ext (by omega)⟩
    exact iIndepFun.of_subsingleton
  have hindD : iIndepFun C₂ Q := iIndepFun_fin_cons_prod P P' A (fun _ : Fin 1 => Z a t) hA.1
    (fun _ => (hZ.1 a ha t ht (hab.trans hbt)).1) hind1
  let X (n : ℕ) (ω : Ω' × Ω) (i : Fin m × Fin r) := ∫ p, g i.1 i.2 p.1 * g' i.1 i.2 p.2
    ∂smoothedProductMeasure (smoothedProductMeasure (A ω.1) (u ℓ) (Z a b ω.2)) (u n) (Z b t ω.2)
  let Y (ω : Ω' × Ω) (i : Fin m × Fin r) := ∫ p, g i.1 i.2 p.1 * g' i.1 i.2 p.2
    ∂smoothedProductMeasure (A ω.1) (u ℓ) (Z a t ω.2)
  have hg (i : Fin m × Fin r) : MemLp (g i.1 i.2) 2 :=
    (map_continuous (g i.1 i.2)).memLp_of_hasCompactSupport (g i.1 i.2).hasCompactSupport
  have hg' (i : Fin m × Fin r) : MemLp (g' i.1 i.2) 2 :=
    (map_continuous (g' i.1 i.2)).memLp_of_hasCompactSupport (g' i.1 i.2).hasCompactSupport
  have hEqX (n : ℕ) (ω : Ω' × Ω) :
      chainProduct (fun k => C (Fin.ofNat 3 k) ω)
        (fun k => u (if k = 0 then ℓ else n)) 2 =
      smoothedProductMeasure (smoothedProductMeasure (A ω.1) (u ℓ) (Z a b ω.2)) (u n) (Z b t ω.2) := rfl
  have hEqY (ω : Ω' × Ω) : chainProduct (fun k => C₂ (Fin.ofNat 2 k) ω) (fun _ => u ℓ) 1 =
      smoothedProductMeasure (A ω.1) (u ℓ) (Z a t ω.2) := rfl
  have hXmoms (n : ℕ) (i : Fin m × Fin r) :
      (∀ᵐ ω ∂Q, Integrable (fun p : Plane × Plane => g i.1 i.2 p.1 * g' i.1 i.2 p.2)
        (smoothedProductMeasure (smoothedProductMeasure (A ω.1) (u ℓ) (Z a b ω.2)) (u n) (Z b t ω.2))) ∧
      MemLp (fun ω => X n ω i) 4 Q := by
    have h := chainPairing_four_finiteBlocks 2 σ hσ C hC hindC
      (fun _ => u) (fun _ => hu) (fun k => if k = 0 then ℓ else n)
      (g i.1 i.2) (g' i.1 i.2) (hg i) (hg' i)
    simpa only [hEqX] using h
  have hYmoms (i : Fin m × Fin r) :
      (∀ᵐ ω ∂Q, Integrable (fun p : Plane × Plane => g i.1 i.2 p.1 * g' i.1 i.2 p.2)
        (smoothedProductMeasure (A ω.1) (u ℓ) (Z a t ω.2))) ∧ MemLp (fun ω => Y ω i) 4 Q := by
    have h := chainPairing_four_finiteBlocks 1 κ hκ C₂ hD hindD
      (fun _ => u) (fun _ => hu) (fun _ => ℓ) (g i.1 i.2) (g' i.1 i.2) (hg i) (hg' i)
    simpa only [hEqY] using h
  have hXmeas (n) : AEStronglyMeasurable (X n) Q :=
    (AEMeasurable.of_eval (fun i => (hXmoms n i).2.aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
  have hYmeas : AEStronglyMeasurable Y Q :=
    (AEMeasurable.of_eval (fun i => (hYmoms i).2.aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
  have hXI : ∀ᵐ z ∂P', ∀ (n : ℕ) (i : Fin m × Fin r), ∀ᵐ ω ∂P, Integrable
      (fun p : Plane × Plane => g i.1 i.2 p.1 * g' i.1 i.2 p.2)
      (smoothedProductMeasure (smoothedProductMeasure (A z) (u ℓ) (Z a b ω)) (u n) (Z b t ω)) := by
    apply ae_all_iff.2
    intro n
    apply ae_all_iff.2
    intro i
    exact Measure.ae_ae_of_ae_prod (hXmoms n i).1
  have hYI : ∀ᵐ z ∂P', ∀ i : Fin m × Fin r, ∀ᵐ ω ∂P, Integrable
      (fun p : Plane × Plane => g i.1 i.2 p.1 * g' i.1 i.2 p.2)
      (smoothedProductMeasure (A z) (u ℓ) (Z a t ω)) := by
    apply ae_all_iff.2
    intro i
    exact Measure.ae_ae_of_ae_prod (hYmoms i).1
  have htests : ∀ᵐ z ∂P', ∀ i : Fin m × Fin r,
      MemLp (fun y => ∫ p, g i.1 i.2 p.1 * u ℓ (p.2 - y) ∂A z) 2 := by
    apply ae_all_iff.2
    intro i
    exact (hA.ae_memLp_weighted_left_test hτA (g i.1 i.2) (u ℓ)
      ((hu.2.1 ℓ).measurable) (hu.2.2.1 ℓ)).mono (fun _ h => h.1)
  have hprob : ∀ᵐ z ∂P', TendstoInMeasure P (fun n ω => X n (z, ω)) atTop (fun ω => Y (z, ω)) := by
    filter_upwards [hA.2.1, htests, hXI, hYI] with z hz htest hzX hzY
    let : IsLocallyFiniteMeasure (A z) := hz
    apply tendstoInMeasure_fintype_pi
    intro i
    let f (y : Plane) := ∫ p, g i.1 i.2 p.1 * u ℓ (p.2 - y) ∂A z
    have hfour := isDenseSHF_smoothedProduct_tendsto_tensor θ D P Z hZ ha hb ht hab hbt
      u hu f (g' i.1 i.2) (htest i) (hg' i)
    have hp := tendstoInMeasure_of_integrable_fourth_moments P _ _ hfour.1 hfour.2
    have hleft (n : ℕ) : (fun ω => X n (z, ω) i) =ᵐ[P]
        fun ω => ∫ p, f p.1 * g' i.1 i.2 p.2 ∂smoothedProductMeasure (Z a b ω) (u n) (Z b t ω) := by
      filter_upwards [hzX n i, (hZ.1 a ha b hb hab).2, (hZ.1 b hb t ht hbt).2]
        with ω hω hLF₁ hLF₂
      let : IsLocallyFiniteMeasure (Z a b ω) := hLF₁
      let : IsLocallyFiniteMeasure (Z b t ω) := hLF₂
      exact (integral_threeBlock_tensor_eq_left_average (A z) (Z a b ω) (Z b t ω)
        (u ℓ) (u n) (hu.1 ℓ) ((hu.2.1 ℓ).measurable) ((hu.2.1 n).measurable)
        (g i.1 i.2) (g' i.1 i.2) (map_continuous _).measurable (map_continuous _).measurable hω).2
    have hright : (fun ω => Y (z, ω) i) =ᵐ[P] fun ω => ∫ p, f p.1 * g' i.1 i.2 p.2 ∂Z a t ω := by
      filter_upwards [hzY i, (hZ.1 a ha t ht (hab.trans hbt)).2] with ω hω hLF
      let : IsLocallyFiniteMeasure (Z a t ω) := hLF
      exact (integral_smoothedProduct_tensor_eq_left_average (A z) (Z a t ω)
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
  have h := tendsto_integral_prod_boundedContinuous_of_fiberwise_tendstoInMeasure P P' X Y
    hXmeas hYmeas hprob Hb
  exact h.2.2

end Critical2DKPZ.SHF.Tsai

end
