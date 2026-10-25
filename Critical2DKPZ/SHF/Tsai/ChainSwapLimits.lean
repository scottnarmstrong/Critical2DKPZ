/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ChainSwap
public import Critical2DKPZ.SHF.Tsai.CenteredFourthLimits
public import Critical2DKPZ.SHF.Tsai.NonlinearChainLimits
import Critical2DKPZ.SHF.Tsai.BlockReplacementIndependence

/-! # The finite-chain replacement estimate at the limit

The original and replaced chains have convergent bounded nonlinear readouts.
Their common heat-centered fourth remainder also converges. Passing the exact
Taylor estimate to these limits gives the same comparison for every finite
chain, including both endpoint replacement cases.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Tsai

/-- Original and replaced finite-chain expectations have limits controlled by the actual centered fourth-moment limit. -/
theorem exists_chain_swap_limit_comparison {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K j : ℕ) (hj : j ≤ K)
    (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k)
    (B : ℕ → Ω → Measure (Plane × Plane)) (B' : Ω → Measure (Plane × Plane))
    (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hB' : HasDeltaBoseMoments θ (τ j) P B')
    (hind : iIndepFun (fun k : Fin (K + 2) => if (k : ℕ) ≤ K then B k else B') P)
    (w : ℕ → ℕ → Plane → ℝ) (hw : ∀ k, IsL2ApplicableMollifier (w k))
    {m r : ℕ} (g g' : Fin m → Fin r → Plane → ℝ)
    (hg : ∀ a b, MemLp (g a b) 2) (hg' : ∀ a b, MemLp (g' a b) 2)
    (H : (Fin m → ℝ) → ℝ) (hH : ContDiff ℝ 4 H) (CH : ℝ)
    (hCH : ∀ k ≤ 4, ∀ x, ‖iteratedFDeriv ℝ k H x‖ ≤ CH) :
    let A (ℓ : ℕ) (ω : Ω) (a : Fin m) := ∑ b, ∫ p, g a b p.1 * g' a b p.2
      ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K
    let R (ℓ : ℕ) (ω : Ω) (a : Fin m) := ∑ b, ∫ p, g a b p.1 * g' a b p.2
      ∂chainProduct (Function.update (fun k => B k ω) j (B' ω)) (fun k => w k ℓ) K
    let E (ℓ : ℕ) (ω : Ω) (a : Fin m) := ∑ b, ∫ p, g a b p.1 * g' a b p.2
      ∂chainProduct (Function.update (fun k => B k ω) j (heatBlock (τ j))) (fun k => w k ℓ) K
    ∃ La Lb M : ℝ, 0 ≤ M ∧
      (∀ ℓ, Integrable (fun ω => H (A ℓ ω)) P) ∧
      (∀ ℓ, Integrable (fun ω => H (R ℓ ω)) P) ∧
      (∀ ℓ, Integrable (fun ω => ∑ a, (A ℓ ω a - E ℓ ω a) ^ 4) P) ∧
      Tendsto (fun ℓ => ∫ ω, H (A ℓ ω) ∂P) atTop (𝓝 La) ∧
      Tendsto (fun ℓ => ∫ ω, H (R ℓ ω) ∂P) atTop (𝓝 Lb) ∧
      Tendsto (fun ℓ => ∫ ω, ∑ a, (A ℓ ω a - E ℓ ω a) ^ 4 ∂P) atTop (𝓝 M) ∧
      |La - Lb| ≤ CH / 12 * M := by
  classical
  dsimp only
  have hindB := iIndepFun_prefix_of_extra K B B' hind
  let C (k : ℕ) (ω : Ω) := Function.update (fun k => B k ω) j (B' ω) k
  have hC (k : ℕ) (hk : k ≤ K) : HasDeltaBoseMoments θ (τ k) P (C k) := by
    by_cases hkj : k = j
    · subst k
      simpa only [C, Function.update_self] using hB'
    · simpa only [C, Function.update_of_ne hkj] using hB k hk
  have hindC : iIndepFun (fun k : Fin (K + 1) => C k) P :=
    iIndepFun_update_of_extra K j hj B B' hind
  have hH0 (z) : ‖H z‖ ≤ CH := by
    simpa only [norm_iteratedFDeriv_zero] using hCH 0 (by omega) z
  obtain ⟨La, hIA, hLa⟩ := exists_integral_comp_chainPairings_limit P K τ hτ B hB hindB
    w hw g g' hg hg' H hH.continuous CH hH0
  obtain ⟨Lb, hIB, hLb⟩ := exists_integral_comp_chainPairings_limit P K τ hτ C hC hindC
    w hw g g' hg hg' H hH.continuous CH hH0
  obtain ⟨M, hM, hML⟩ := exists_integral_sum_centeredChainPairings_four_limit K j hj τ hτ
    B hB hindB g g' hg hg'
  have hMoment := hML w hw
  refine ⟨La, Lb, M, hM, hIA, hIB, hMoment.1, hLa, hLb, hMoment.2, ?_⟩
  apply le_of_tendsto_of_tendsto ((hLa.sub hLb).abs) (hMoment.2.const_mul (CH / 12))
  apply Eventually.of_forall
  intro ℓ
  exact (abs_integral_comp_chain_swap_le K j hj τ hτ B B' hB hB' hind (fun k => w k ℓ)
    (fun k => ⟨w k, hw k, ℓ, rfl⟩) g g' hg hg' H hH CH hCH).2

end Critical2DKPZ.SHF.Tsai

end
