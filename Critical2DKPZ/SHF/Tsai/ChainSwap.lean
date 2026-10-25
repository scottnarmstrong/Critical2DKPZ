/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ChainTaylorModification
public import Critical2DKPZ.SHF.Tsai.ChainTestCongruence
public import Critical2DKPZ.SHF.Tsai.ChainNonlinearIntegrability

/-! # Fourth-moment bounds for replacement of a chain block

Replacing an independent block by another with the same first four delta-Bose moments
preserves centered fourth moments and bounds smooth nonlinear expectation differences
by the centered fourth remainder with coefficient `1/12`.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Tsai

/-- Replacing an independent block with matching delta-Bose moments preserves centered fourth moments and gives a nonlinear expectation bound with coefficient `1/12`. Integrability of the observables and fourth remainder is supplied by `integrable_comp_chain_swap`. -/
theorem abs_integral_comp_chain_swap_le {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (K j : ℕ) (hj : j ≤ K) (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k)
    (B : ℕ → Ω → Measure (Plane × Plane)) (B' : Ω → Measure (Plane × Plane))
    (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k)) (hB' : HasDeltaBoseMoments θ (τ j) P B')
    (hind : iIndepFun (fun k : Fin (K + 2) => if (k : ℕ) ≤ K then B k else B') P)
    (u : ℕ → Plane → ℝ) (hu : ∀ k, ∃ w : ℕ → Plane → ℝ, IsL2ApplicableMollifier w ∧ ∃ ℓ, u k = w ℓ)
    {m r : ℕ} (g g' : Fin m → Fin r → Plane → ℝ) (hg : ∀ a b, MemLp (g a b) 2)
    (hg' : ∀ a b, MemLp (g' a b) 2) (H : (Fin m → ℝ) → ℝ) (hH : ContDiff ℝ 4 H) (CH : ℝ)
    (hCH : ∀ k ≤ 4, ∀ x, ‖iteratedFDeriv ℝ k H x‖ ≤ CH) :
    (∫ ω, ∑ a, ((∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂(chainProduct (fun k => B k ω) u K)) -
        ∑ b, ∫ p, g a b p.1 * g' a b p.2
          ∂(chainProduct (Function.update (fun k => B k ω) j (heatBlock (τ j))) u K)) ^ 4 ∂P =
      ∫ ω, ∑ a, ((∑ b, ∫ p, g a b p.1 * g' a b p.2
          ∂(chainProduct (Function.update (fun k => B k ω) j (B' ω)) u K)) -
        ∑ b, ∫ p, g a b p.1 * g' a b p.2
          ∂(chainProduct (Function.update (fun k => B k ω) j (heatBlock (τ j))) u K)) ^ 4 ∂P) ∧
    |(∫ ω, H (fun a => ∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂(chainProduct (fun k => B k ω) u K)) ∂P) -
        ∫ ω, H (fun a => ∑ b, ∫ p, g a b p.1 * g' a b p.2
          ∂(chainProduct (Function.update (fun k => B k ω) j (B' ω)) u K)) ∂P| ≤
      CH / 12 * ∫ ω, ∑ a, ((∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂(chainProduct (fun k => B k ω) u K)) -
        ∑ b, ∫ p, g a b p.1 * g' a b p.2
          ∂(chainProduct (Function.update (fun k => B k ω) j (heatBlock (τ j))) u K)) ^ 4 ∂P := by
  classical
  refine ⟨integral_sum_centeredChainPairings_pow_four_eq_of_swap
    K j hj τ hτ B B' hB hB' hind u hu g g' hg hg', ?_⟩
  let G (a : Fin m) (b : Fin r) := (hg a b).aestronglyMeasurable.aemeasurable.mk (g a b)
  let G' (a : Fin m) (b : Fin r) := (hg' a b).aestronglyMeasurable.aemeasurable.mk (g' a b)
  have hGm (a b) : Measurable (G a b) := (hg a b).aestronglyMeasurable.aemeasurable.measurable_mk
  have hG'm (a b) : Measurable (G' a b) := (hg' a b).aestronglyMeasurable.aemeasurable.measurable_mk
  have heq (a b) : g a b =ᵐ[volume] G a b := (hg a b).aestronglyMeasurable.aemeasurable.ae_eq_mk
  have heq' (a b) : g' a b =ᵐ[volume] G' a b := (hg' a b).aestronglyMeasurable.aemeasurable.ae_eq_mk
  have hG (a b) : MemLp (G a b) 2 := (memLp_congr_ae (heq a b)).1 (hg a b)
  have hG' (a b) : MemLp (G' a b) 2 := (memLp_congr_ae (heq' a b)).1 (hg' a b)
  have h := (abs_integral_comp_chain_swap_le_of_measurable K j hj τ hτ B B' hB hB'
    hind u hu G G' hG hG' H hH CH hCH hGm hG'm).2
  choose w hw q hq using hu
  let v (k ℓ : ℕ) := w k (ℓ + q k)
  have hv (k) : IsL2ApplicableMollifier (v k) :=
    (hw k).comp_tendsto (tendsto_add_atTop_nat (q k))
  have hvu : (fun k => v k 0) = u := by
    funext k
    simpa only [v, Nat.zero_add] using (hq k).symm
  let D (k : ℕ) (ω : Ω) := Function.update (fun k => B k ω) j (B' ω) k
  have hD (k) (hk : k ≤ K) : HasDeltaBoseMoments θ (τ k) P (D k) := by
    by_cases hkj : k = j
    · subst k
      simpa only [D, Function.update_self] using hB'
    · simpa only [D, Function.update_of_ne hkj] using hB k hk
  have hindB := iIndepFun_prefix_of_extra K B B' hind
  have hindD : iIndepFun (fun k : Fin (K + 1) => D k) P :=
    iIndepFun_update_of_extra K j hj B B' hind
  have hTensor (a b) : (fun p : Plane × Plane => g a b p.1 * g' a b p.2) =ᵐ[volume]
      fun p => G a b p.1 * G' a b p.2 := by
    rw [Measure.volume_eq_prod]
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (heq a b),
      Measure.quasiMeasurePreserving_snd.ae (heq' a b)] with p hp hp'
    rw [hp, hp']
  have hRaw (a b) := ae_integral_chainProduct_congr K τ hτ B hB hindB v hv 0 _ _ (hTensor a b)
  have hRep (a b) := ae_integral_chainProduct_congr K τ hτ D hD hindD v hv 0 _ _ (hTensor a b)
  have hHeat (a b) := ae_integral_chainProduct_update_heat_congr K j hj τ hτ B hB hindB v hv 0 _ _ (hTensor a b)
  simp only [hvu] at hRaw hRep hHeat
  let R (μ : Measure (Plane × Plane)) (a : Fin m) := ∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂μ
  let S (μ : Measure (Plane × Plane)) (a : Fin m) := ∑ b, ∫ p, G a b p.1 * G' a b p.2 ∂μ
  have hRawRead : (fun ω => R (chainProduct (fun k => B k ω) u K)) =ᵐ[P]
      fun ω => S (chainProduct (fun k => B k ω) u K) := by
    filter_upwards [ae_all_iff.2 (fun a => ae_all_iff.2 (hRaw a))] with ω hω
    funext a
    exact Finset.sum_congr rfl (fun b _ => hω a b)
  have hRepRead : (fun ω => R (chainProduct (Function.update (fun k => B k ω) j (B' ω)) u K)) =ᵐ[P]
      fun ω => S (chainProduct (Function.update (fun k => B k ω) j (B' ω)) u K) := by
    filter_upwards [ae_all_iff.2 (fun a => ae_all_iff.2 (hRep a))] with ω hω
    funext a
    exact Finset.sum_congr rfl (fun b _ => hω a b)
  have hHeatRead : (fun ω => R (chainProduct (Function.update (fun k => B k ω) j (heatBlock (τ j))) u K)) =ᵐ[P]
      fun ω => S (chainProduct (Function.update (fun k => B k ω) j (heatBlock (τ j))) u K) := by
    filter_upwards [ae_all_iff.2 (fun a => ae_all_iff.2 (hHeat a))] with ω hω
    funext a
    exact Finset.sum_congr rfl (fun b _ => hω a b)
  have hRawInt := integral_congr_ae (hRawRead.fun_comp H)
  have hRepInt := integral_congr_ae (hRepRead.fun_comp H)
  simp only [Function.comp_def] at hRawInt hRepInt
  have hFourthInt : (∫ ω, ∑ a, (R (chainProduct (fun k => B k ω) u K) a -
      R (chainProduct (Function.update (fun k => B k ω) j (heatBlock (τ j))) u K) a) ^ 4 ∂P) =
      ∫ ω, ∑ a, (S (chainProduct (fun k => B k ω) u K) a -
        S (chainProduct (Function.update (fun k => B k ω) j (heatBlock (τ j))) u K) a) ^ 4 ∂P := by
    apply integral_congr_ae
    filter_upwards [hRawRead, hHeatRead] with ω hω hω'
    rw [hω, hω']
  rw [hRawInt, hRepInt, hFourthInt]
  exact h

/-- Integrability of both nonlinear readouts and the centered fourth moment in the swap estimate. -/
theorem integrable_comp_chain_swap {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (K j : ℕ) (hj : j ≤ K) (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k)
    (B : ℕ → Ω → Measure (Plane × Plane)) (B' : Ω → Measure (Plane × Plane))
    (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k)) (hB' : HasDeltaBoseMoments θ (τ j) P B')
    (hind : iIndepFun (fun k : Fin (K + 2) => if (k : ℕ) ≤ K then B k else B') P)
    (u : ℕ → Plane → ℝ) (hu : ∀ k, ∃ w : ℕ → Plane → ℝ, IsL2ApplicableMollifier w ∧ ∃ ℓ, u k = w ℓ)
    {m r : ℕ} (g g' : Fin m → Fin r → Plane → ℝ) (hg : ∀ a b, MemLp (g a b) 2)
    (hg' : ∀ a b, MemLp (g' a b) 2) (H : (Fin m → ℝ) → ℝ) (hH : ContDiff ℝ 4 H) (CH : ℝ)
    (hCH : ∀ k ≤ 4, ∀ x, ‖iteratedFDeriv ℝ k H x‖ ≤ CH) :
    Integrable (fun ω => H (fun a => ∑ b, ∫ p, g a b p.1 * g' a b p.2
      ∂chainProduct (fun k => B k ω) u K)) P ∧
    Integrable (fun ω => H (fun a => ∑ b, ∫ p, g a b p.1 * g' a b p.2
      ∂chainProduct (Function.update (fun k => B k ω) j (B' ω)) u K)) P ∧
    Integrable (fun ω => ∑ a, ((∑ b, ∫ p, g a b p.1 * g' a b p.2
      ∂chainProduct (fun k => B k ω) u K) -
      ∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂chainProduct
        (Function.update (fun k => B k ω) j (heatBlock (τ j))) u K) ^ 4) P := by
  classical
  choose w hw q hq using hu
  let v (k ℓ : ℕ) := w k (ℓ + q k)
  have hv (k) : IsL2ApplicableMollifier (v k) :=
    (hw k).comp_tendsto (tendsto_add_atTop_nat (q k))
  have hvu : (fun k => v k 0) = u := by
    funext k
    simpa only [v, Nat.zero_add] using (hq k).symm
  let D (k : ℕ) (ω : Ω) := Function.update (fun k => B k ω) j (B' ω) k
  have hD (k) (hk : k ≤ K) : HasDeltaBoseMoments θ (τ k) P (D k) := by
    by_cases hkj : k = j
    · subst k
      simpa only [D, Function.update_self] using hB'
    · simpa only [D, Function.update_of_ne hkj] using hB k hk
  have hindB := iIndepFun_prefix_of_extra K B B' hind
  have hindD : iIndepFun (fun k : Fin (K + 1) => D k) P :=
    iIndepFun_update_of_extra K j hj B B' hind
  have hH0 (z) : ‖H z‖ ≤ CH := by
    simpa only [norm_iteratedFDeriv_zero] using hCH 0 (by omega) z
  have hRaw := integrable_comp_chainPairings P K τ hτ B hB hindB v hv 0 g g' hg hg'
    H hH.continuous CH hH0
  have hRep := integrable_comp_chainPairings P K τ hτ D hD hindD v hv 0 g g' hg hg'
    H hH.continuous CH hH0
  have hFourth := integrable_sum_centeredChainPairings_pow_four P K j hj τ hτ B hB hindB
    v hv 0 g g' hg hg'
  rw [hvu] at hRaw hRep hFourth
  exact ⟨hRaw, hRep, hFourth⟩

end Critical2DKPZ.SHF.Tsai

end
