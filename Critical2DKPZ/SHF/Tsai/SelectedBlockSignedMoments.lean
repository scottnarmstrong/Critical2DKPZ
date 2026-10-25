/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ChainBlockTests
public import Critical2DKPZ.SHF.Tsai.BlockTestMoments

/-! # Signed selected-block moments with fixed outer chain measures

Actual chain integrability gives the selected-block representation almost
surely. The integrable joint endpoint test then evaluates its product under
the full block moment measure. No spatial L2 condition is imposed on the
conditional endpoint tests.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- With fixed outer blocks, integrable signed chain products are evaluated by the selected block moment. -/
theorem HasDeltaBoseMoments.integral_prod_chain_update_eq {θ τ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {B : Ω → Measure (Plane × Plane)}
    (hB : HasDeltaBoseMoments θ τ P B) (hτ : 0 < τ)
    (μ : ℕ → Measure (Plane × Plane)) [∀ k, SigmaFinite (μ k)]
    (K : ℕ) (j : Fin (K + 1)) {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 4)
    (w : Fin n → ℕ → Plane → ℝ) (hw : ∀ i k, Measurable (w i k))
    (F : Fin n → Plane × Plane → ℝ)
    (hchainI : ∀ᵐ ω ∂P, ∀ i, Integrable (F i) (chainProduct (Function.update μ j (B ω)) (w i) K))
    (hI : Integrable (fun q : Configuration n × Configuration n =>
      ∏ i, chainBlockTest K j μ (w i) (F i) (q.1 i, q.2 i))
        (volume.withDensity (Function.uncurry (momentKernel n θ τ)))) :
    Integrable (fun ω => ∏ i, ∫ p, F i p ∂chainProduct (Function.update μ j (B ω)) (w i) K) P ∧
    (∫ ω, ∏ i, (∫ p, F i p ∂chainProduct (Function.update μ j (B ω)) (w i) K) ∂P) =
      ∫ q : Configuration n × Configuration n,
        ∏ i, chainBlockTest K j μ (w i) (F i) (q.1 i, q.2 i)
          ∂volume.withDensity (Function.uncurry (momentKernel n θ τ)) := by
  classical
  obtain ⟨houter, hmoment⟩ := hB.integral_prod_tests_eq hτ hn1 hn
    (fun i => chainBlockTest K j μ (w i) (F i)) hI
  have hprod : (fun ω => ∏ i, ∫ p, F i p
      ∂chainProduct (Function.update μ j (B ω)) (w i) K) =ᵐ[P]
      fun ω => ∏ i, ∫ p, chainBlockTest K j μ (w i) (F i) p ∂B ω := by
    filter_upwards [hB.2.1, hchainI] with ω hω hωI
    let : IsLocallyFiniteMeasure (B ω) := hω
    have hsf (k : ℕ) : SigmaFinite (Function.update μ j (B ω) k) := by
      by_cases hk : k = (j : ℕ)
      · subst k
        rw [Function.update_self]
        infer_instance
      · rw [Function.update_of_ne hk]
        infer_instance
    let : ∀ k, SigmaFinite (Function.update μ j (B ω) k) := hsf
    apply Finset.prod_congr rfl
    intro i _
    have h := (integral_chainProduct_eq_integral_blockTest _ (hw i) K j (F i) (hωI i)).2
    rw [chainBlockTest_update, Function.update_self] at h
    exact h
  exact ⟨houter.congr hprod.symm, (integral_congr_ae hprod).trans hmoment⟩

end Critical2DKPZ.SHF.Tsai

end
