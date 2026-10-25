/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.UniversalChainLimits
public import Critical2DKPZ.SHF.Tsai.FourthMomentProbability
public import Critical2DKPZ.SHF.Tsai.FiniteVectorConvergence
public import Critical2DKPZ.SHF.Tsai.ChainNonlinearIntegrability

/-! # Bounded continuous observables of chain pairings

Common fourth-moment limits give convergence in probability of finite vectors of chain
pairings. Their bounded continuous observables are integrable and have convergent expectations.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction

namespace Critical2DKPZ.SHF.Tsai

/-- Bounded continuous functions of finite tensor chain pairings have integrable convergent expectations. -/
theorem exists_integral_comp_chainPairings_limit {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ) (τ : ℕ → ℝ)
    (hτ : ∀ k ≤ K, 0 < τ k) (B : ℕ → Ω → Measure (Plane × Plane))
    (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hind : iIndepFun (fun k : Fin (K + 1) => B k) P)
    (w : ℕ → ℕ → Plane → ℝ) (hw : ∀ k, IsL2ApplicableMollifier (w k))
    {m r : ℕ} (g g' : Fin m → Fin r → Plane → ℝ)
    (hg : ∀ a b, MemLp (g a b) 2) (hg' : ∀ a b, MemLp (g' a b) 2)
    (H : (Fin m → ℝ) → ℝ) (hH : Continuous H) (CH : ℝ) (hCH : ∀ z, ‖H z‖ ≤ CH) :
    ∃ L : ℝ,
      (∀ ℓ, Integrable (fun ω => H (fun a => ∑ b, ∫ p, g a b p.1 * g' a b p.2
        ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K)) P) ∧
      Tendsto (fun ℓ => ∫ ω, H (fun a => ∑ b, ∫ p, g a b p.1 * g' a b p.2
        ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K) ∂P) atTop (𝓝 L) := by
  classical
  choose F hF hLimit using fun i : Fin m × Fin r =>
    exists_chainPairing_four_limit_universal K τ hτ B hB hind w hw
      (g i.1 i.2) (g' i.1 i.2) (hg i.1 i.2) (hg' i.1 i.2)
  let X (ℓ : ℕ) (ω : Ω) (i : Fin m × Fin r) := ∫ p, g i.1 i.2 p.1 * g' i.1 i.2 p.2
    ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K
  have hm (ℓ : ℕ) (i : Fin m × Fin r) : MemLp (fun ω => X ℓ ω i) 4 P :=
    memLp_chainPairing_four K τ hτ B hB hind w hw ℓ _ _ (hg _ _) (hg' _ _)
  have hProb (i : Fin m × Fin r) : TendstoInMeasure P (fun ℓ ω => X ℓ ω i) atTop (F i) :=
    tendstoInMeasure_of_integrable_fourth_moments P _ _ (hLimit i w hw).1 (hLimit i w hw).2
  let J (z : (Fin m × Fin r) → ℝ) := H (fun a => ∑ b, z (a, b))
  have hJ : Continuous J := hH.comp (continuous_pi fun a =>
    continuous_finsetSum _ (fun b _ => continuous_apply (a, b)))
  let Hb : ((Fin m × Fin r) → ℝ) →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfBound ⟨J, hJ⟩ (2 * CH) (by
      intro x y
      exact (dist_le_norm_add_norm _ _).trans
        ((add_le_add (hCH _) (hCH _)).trans_eq (two_mul CH).symm))
  refine ⟨∫ ω, H (fun a => ∑ b, F (a, b) ω) ∂P,
    (fun ℓ => integrable_comp_chainPairings P K τ hτ B hB hind w hw ℓ g g' hg hg' H hH CH hCH), ?_⟩
  exact tendsto_integral_boundedContinuous_of_coordinatewise_tendstoInMeasure P X (fun ω i => F i ω)
    (fun ℓ i => (hm ℓ i).aestronglyMeasurable.aemeasurable) hProb Hb

end Critical2DKPZ.SHF.Tsai

end
