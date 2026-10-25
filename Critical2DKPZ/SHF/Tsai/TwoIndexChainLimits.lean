/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.UniversalChainLimits
public import Critical2DKPZ.SHF.Tsai.FourthMomentProbability

/-! # Chain limits with two connector indices

Allowing one connector a separate diverging index preserves convergence in probability
to the common chain-pairing limit.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Tsai

/-- Giving one connector its own index preserves the common chain limit jointly in both indices. -/
theorem exists_chainPairing_twoIndex_limit {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (K j : ℕ) (τ : ℕ → ℝ)
    (hτ : ∀ k ≤ K, 0 < τ k) (B : ℕ → Ω → Measure (Plane × Plane))
    (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hind : iIndepFun (fun k : Fin (K + 1) => B k) P)
    (w : ℕ → ℕ → Plane → ℝ) (hw : ∀ k, IsL2ApplicableMollifier (w k))
    (g g' : Plane → ℝ) (hg : MemLp g 2) (hg' : MemLp g' 2) :
    ∃ F : Ω → ℝ, MemLp F 4 P ∧
      TendstoInMeasure P (fun q : ℕ × ℕ => fun ω => ∫ p, g p.1 * g' p.2
        ∂chainProduct (fun k => B k ω) (fun k => w k (if k = j then q.2 else q.1)) K) atTop F := by
  classical
  obtain ⟨F, hF, hLimit⟩ := exists_chainPairing_four_limit_universal K τ hτ B hB hind w hw g g' hg hg'
  refine ⟨F, hF, ?_⟩
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  apply Filter.tendsto_iff_seq_tendsto.2
  intro q hq
  have hqprod : Tendsto q atTop (atTop ×ˢ atTop : Filter (ℕ × ℕ)) := by
    rwa [prod_atTop_atTop_eq]
  let v (k n : ℕ) := w k (if k = j then (q n).2 else (q n).1)
  have hv (k : ℕ) : IsL2ApplicableMollifier (v k) := by
    by_cases hkj : k = j
    · have heq : v k = fun n => w k (q n).2 := by funext n x; simp only [v, ite_eq_left hkj]
      rw [heq]
      exact (hw k).comp_tendsto hqprod.snd
    · have heq : v k = fun n => w k (q n).1 := by funext n x; simp only [v, ite_eq_right hkj]
      rw [heq]
      exact (hw k).comp_tendsto hqprod.fst
  have hconv := tendstoInMeasure_of_integrable_fourth_moments P _ F (hLimit v hv).1 (hLimit v hv).2
  simpa only [v, Function.comp_def] using (tendstoInMeasure_iff_dist.1 hconv) ε hε

end Critical2DKPZ.SHF.Tsai

end
