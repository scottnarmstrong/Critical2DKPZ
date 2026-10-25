/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ChainTaylorComparison

/-! # Removing everywhere local finiteness from block replacement

Canonical locally finite modifications preserve moments, independence and
almost every original chain. Their replacement estimate therefore transfers
to the literal blocks, which are locally finite only almost surely.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Tsai

/-- The replacement bound for measurable endpoint tests and almost-surely locally finite blocks.
The fourth-moment integrability is supplied by
`integral_sum_centeredChainPairings_pow_four_eq_of_moments`. -/
theorem abs_integral_comp_chain_swap_le_of_measurable {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (K j : ℕ) (hj : j ≤ K) (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k)
    (B : ℕ → Ω → Measure (Plane × Plane)) (B' : Ω → Measure (Plane × Plane))
    (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k)) (hB' : HasDeltaBoseMoments θ (τ j) P B')
    (hind : iIndepFun (fun k : Fin (K + 2) => if (k : ℕ) ≤ K then B k else B') P)
    (u : ℕ → Plane → ℝ) (hu : ∀ k, ∃ w : ℕ → Plane → ℝ, IsL2ApplicableMollifier w ∧ ∃ ℓ, u k = w ℓ)
    {m r : ℕ} (g g' : Fin m → Fin r → Plane → ℝ) (hg : ∀ a b, MemLp (g a b) 2)
    (hg' : ∀ a b, MemLp (g' a b) 2) (H : (Fin m → ℝ) → ℝ) (hH : ContDiff ℝ 4 H) (CH : ℝ)
    (hCH : ∀ k ≤ 4, ∀ x, ‖iteratedFDeriv ℝ k H x‖ ≤ CH)
    (hgm : ∀ a b, Measurable (g a b)) (hg'm : ∀ a b, Measurable (g' a b)) :
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
  let E := CompactExhaustion.choice (Plane × Plane)
  let C (k : ℕ) := RandomMeasure.locallyFiniteMeasureModification E (B k)
  let C' := RandomMeasure.locallyFiniteMeasureModification E B'
  have hC (k) (hk : k ≤ K) : HasDeltaBoseMoments θ (τ k) P (C k) :=
    (hB k hk).locallyFiniteMeasureModification E
  have hC' : HasDeltaBoseMoments θ (τ j) P C' := hB'.locallyFiniteMeasureModification E
  have hClf (k) (_hk : k ≤ K) (ω) : IsLocallyFiniteMeasure (C k ω) :=
    RandomMeasure.locallyFinite_locallyFiniteMeasureModification E (B k) ω
  have hC'lf (ω) : IsLocallyFiniteMeasure (C' ω) :=
    RandomMeasure.locallyFinite_locallyFiniteMeasureModification E B' ω
  have heq (k) (hk : k ≤ K) : B k =ᵐ[P] C k :=
    (RandomMeasure.ae_eq_radonValuedModification E P (B k) (hB k hk).2.1).symm
  have heq' : B' =ᵐ[P] C' := (RandomMeasure.ae_eq_radonValuedModification E P B' hB'.2.1).symm
  have hindC : iIndepFun (fun k : Fin (K + 2) => if (k : ℕ) ≤ K then C k else C') P := by
    apply hind.congr
    intro k
    by_cases hk : (k : ℕ) ≤ K
    · simpa only [ite_eq_left hk] using heq k hk
    · simpa only [ite_eq_right hk] using heq'
  have h := (abs_integral_comp_chain_swap_le_of_locallyFinite K j hj τ hτ C C' hC hC'
    hindC u hu g g' hg hg' H hH CH hCH hClf hC'lf hgm hg'm).2
  have hPrefix : ∀ᵐ ω ∂P, ∀ k ≤ K, B k ω = C k ω :=
    ae_all_iff.2 fun k => ae_all_iff.2 fun hk => heq k hk
  have hRaw := chainProduct_congr_ae K B C heq u
  have hRep : (fun ω => chainProduct (Function.update (fun k => B k ω) j (B' ω)) u K) =ᵐ[P]
      fun ω => chainProduct (Function.update (fun k => C k ω) j (C' ω)) u K := by
    filter_upwards [hPrefix, heq'] with ω hω hω'
    apply chainProduct_congr_prefix
    intro k hk
    by_cases hkj : k = j
    · subst k
      simpa only [Function.update_self] using hω'
    · simpa only [Function.update_of_ne hkj] using hω k hk
  have hHeat : (fun ω => chainProduct (Function.update (fun k => B k ω) j (heatBlock (τ j))) u K) =ᵐ[P]
      fun ω => chainProduct (Function.update (fun k => C k ω) j (heatBlock (τ j))) u K := by
    filter_upwards [hPrefix] with ω hω
    apply chainProduct_congr_prefix
    intro k hk
    by_cases hkj : k = j
    · subst k
      simp only [Function.update_self]
    · simpa only [Function.update_of_ne hkj] using hω k hk
  let R (μ : Measure (Plane × Plane)) (a : Fin m) := ∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂μ
  have hRawInt : (∫ ω, H (R (chainProduct (fun k => B k ω) u K)) ∂P) =
      ∫ ω, H (R (chainProduct (fun k => C k ω) u K)) ∂P :=
    integral_congr_ae (hRaw.fun_comp (fun μ => H (R μ)))
  have hRepInt : (∫ ω, H (R (chainProduct (Function.update (fun k => B k ω) j (B' ω)) u K)) ∂P) =
      ∫ ω, H (R (chainProduct (Function.update (fun k => C k ω) j (C' ω)) u K)) ∂P :=
    integral_congr_ae (hRep.fun_comp (fun μ => H (R μ)))
  have hFourthInt : (∫ ω, ∑ a, (R (chainProduct (fun k => B k ω) u K) a -
      R (chainProduct (Function.update (fun k => B k ω) j (heatBlock (τ j))) u K) a) ^ 4 ∂P) =
      ∫ ω, ∑ a, (R (chainProduct (fun k => C k ω) u K) a -
        R (chainProduct (Function.update (fun k => C k ω) j (heatBlock (τ j))) u K) a) ^ 4 ∂P := by
    apply integral_congr_ae
    filter_upwards [hRaw, hHeat] with ω hω hω'
    rw [hω, hω']
  change |(∫ ω, H (R (chainProduct (fun k => B k ω) u K)) ∂P) -
    ∫ ω, H (R (chainProduct (Function.update (fun k => B k ω) j (B' ω)) u K)) ∂P| ≤ _
  rw [hRawInt, hRepInt, hFourthInt]
  exact h

end Critical2DKPZ.SHF.Tsai

end
