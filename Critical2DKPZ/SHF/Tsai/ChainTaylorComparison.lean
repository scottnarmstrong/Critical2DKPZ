/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.SplitChainTaylorComparison
public import Critical2DKPZ.SHF.Tsai.ChainCopyExpectations
public import Critical2DKPZ.SHF.Tsai.ChainSwapFourthMoment

/-! # Block replacement on the original probability space

Independent copies preserve the nonlinear expectations and centered fourth
moments. The conditional bound transfers back to the original coupling;
matching fourth moments changes the coefficient from `1/24` to `1/12`.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Tsai

/-- The replacement estimate for globally locally finite blocks and measurable endpoint tests.
The fourth-moment integrability is supplied by
`integral_sum_centeredChainPairings_pow_four_eq_of_moments`. -/
theorem abs_integral_comp_chain_swap_le_of_locallyFinite {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (K j : ℕ) (hj : j ≤ K) (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k)
    (B : ℕ → Ω → Measure (Plane × Plane)) (B' : Ω → Measure (Plane × Plane))
    (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k)) (hB' : HasDeltaBoseMoments θ (τ j) P B')
    (hind : iIndepFun (fun k : Fin (K + 2) => if (k : ℕ) ≤ K then B k else B') P)
    (u : ℕ → Plane → ℝ) (hu : ∀ k, ∃ w : ℕ → Plane → ℝ, IsL2ApplicableMollifier w ∧ ∃ ℓ, u k = w ℓ)
    {m r : ℕ} (g g' : Fin m → Fin r → Plane → ℝ) (hg : ∀ a b, MemLp (g a b) 2)
    (hg' : ∀ a b, MemLp (g' a b) 2) (H : (Fin m → ℝ) → ℝ) (hH : ContDiff ℝ 4 H) (CH : ℝ)
    (hCH : ∀ k ≤ 4, ∀ x, ‖iteratedFDeriv ℝ k H x‖ ≤ CH)
    (hlf : ∀ k ≤ K, ∀ ω, IsLocallyFiniteMeasure (B k ω))
    (hlf' : ∀ ω, IsLocallyFiniteMeasure (B' ω))
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
  have hFourth := integral_sum_centeredChainPairings_pow_four_eq_of_swap
    K j hj τ hτ B B' hB hB' hind u hu g g' hg hg'
  refine ⟨hFourth, ?_⟩
  choose w hw q hq using hu
  let v (k ℓ : ℕ) := w k (ℓ + q k)
  have hv (k) : IsL2ApplicableMollifier (v k) :=
    (hw k).comp_tendsto (tendsto_add_atTop_nat (q k))
  have hvu : (fun k => v k 0) = u := by
    funext k
    simpa only [v, Nat.zero_add] using (hq k).symm
  let jf : Fin (K + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  let D := Function.update B j B'
  have hDj : D jf = B' := Function.update_self _ _ _
  have hD (k) (hk : k ≤ K) : HasDeltaBoseMoments θ (τ k) P (D k) := by
    by_cases hkj : k = j
    · subst k
      simpa only [D, Function.update_self] using hB'
    · simpa only [D, Function.update_of_ne hkj] using hB k hk
  have hDlf (k) (hk : k ≤ K) (ω : Ω) : IsLocallyFiniteMeasure (D k ω) := by
    by_cases hkj : k = j
    · subst k
      simpa only [D, Function.update_self] using hlf' ω
    · simpa only [D, Function.update_of_ne hkj] using hlf k hk ω
  have hDpoint (ω : Ω) : (fun k => D k ω) = Function.update (fun k => B k ω) j (B' ω) := by
    funext k
    by_cases hkj : k = j
    · subst k
      simp only [D, Function.update_self]
    · simp only [D, Function.update_of_ne hkj]
  have hindB := iIndepFun_prefix_of_extra K B B' hind
  have hDFamily : (fun k : Fin (K + 1) => D k) =
      fun (k : Fin (K + 1)) ω => Function.update (fun k => B k ω) j (B' ω) k := by
    funext k ω
    exact congrFun (hDpoint ω) k
  have hindD : iIndepFun (fun k : Fin (K + 1) => D k) P := by
    rw [hDFamily]
    exact iIndepFun_update_of_extra K j hj B B' hind
  have hOuter : outerCopyBlock K jf D = outerCopyBlock K jf B := outerCopyBlock_update K jf B B'
  have hRaw := integral_comp_chain_eq_splitCopies P K jf B (fun k hk => (hB k hk).1)
    hlf hindB u (fun k => by rw [← hvu]; exact ((hv k).2.1 0).measurable)
    g g' hgm hg'm H hH.continuous.measurable
  have hRep := integral_comp_chain_eq_splitCopies P K jf D (fun k hk => (hD k hk).1)
    hDlf hindD u (fun k => by rw [← hvu]; exact ((hv k).2.1 0).measurable)
    g g' hgm hg'm H hH.continuous.measurable
  have hVB := integral_sum_centered_chain_eq_splitCopies P K jf τ hτ B hB hindB v hv 0 g g' hg hg'
  have hVD := integral_sum_centered_chain_eq_splitCopies P K jf τ hτ D hD hindD v hv 0 g g' hg hg'
  rw [hvu] at hVB hVD
  simp only [hOuter, hDj] at hRep hVD
  simp only [hDpoint] at hRep hVD
  simp only [jf, Function.update_idem] at hVD
  have hH0 (z) : ‖H z‖ ≤ CH := by
    simpa only [norm_iteratedFDeriv_zero] using hCH 0 (by omega) z
  have hSplit := abs_integral_splitChain_swap_le P K jf τ hτ B hB hlf B' hB' hlf'
    v hv 0 g g' hgm hg'm hg hg' H hH CH hH0 (hCH 4 le_rfl)
  dsimp only at hSplit
  rw [hvu] at hSplit
  have hBound := hSplit.2.2
  rw [← hRaw, ← hRep, ← hVB, ← hVD, ← hFourth] at hBound
  exact hBound.trans_eq (by ring)

end Critical2DKPZ.SHF.Tsai

end
