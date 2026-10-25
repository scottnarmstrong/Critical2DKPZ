/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.TupleChainPaths
public import Critical2DKPZ.SHF.Tsai.IndependentBlockTuples

/-! # Positive stochastic chain moments as moment-kernel path integrals

The deterministic regrouping writes particle chains as block tuple paths.
Independence and the joint tuple moment law then replace the random block
measures by their actual moment-kernel measures. Canonical modifications
justify the calculation under almost-sure local finiteness.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- The full positive product moment of chains is the moment-kernel path integral. -/
theorem lintegral_prod_chainProduct_eq_lintegral_momentPaths
    {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (K : ℕ) (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k)
    (B : ℕ → Ω → Measure (Plane × Plane))
    (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hind : iIndepFun (fun k : Fin (K + 1) => B k) P)
    {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 4)
    (w : Fin n → ℕ → Plane → ℝ) (hwm : ∀ i k, Measurable (w i k))
    (H : Fin n → Plane × Plane → ℝ≥0∞) (hH : ∀ i, Measurable (H i)) :
    (∫⁻ ω, ∏ i, ∫⁻ p, H i p ∂chainProduct (fun k => B k ω) (w i) K ∂P) =
      ∫⁻ p, tupleChainPathTest K w H p
        ∂Measure.pi (fun k : Fin (K + 1) =>
          volume.withDensity (Function.uncurry (momentKernel n θ (τ k)))) := by
  let E := CompactExhaustion.choice (Plane × Plane)
  let B' k := RandomMeasure.locallyFiniteMeasureModification E (B k)
  have hlf (k) (ω) : IsLocallyFiniteMeasure (B' k ω) :=
    RandomMeasure.locallyFinite_locallyFiniteMeasureModification E (B k) ω
  have hB' (k) (hk : k ≤ K) : HasDeltaBoseMoments θ (τ k) P (B' k) :=
    (hB k hk).locallyFiniteMeasureModification E
  have hEq (k) (hk : k ≤ K) : B k =ᵐ[P] B' k :=
    (RandomMeasure.ae_eq_radonValuedModification E P (B k) (hB k hk).2.1).symm
  have hchains (i : Fin n) := chainProduct_congr_ae K B B' hEq (w i)
  have hprod : (fun ω => ∏ i, ∫⁻ p, H i p ∂chainProduct (fun k => B k ω) (w i) K) =ᵐ[P]
      fun ω => ∏ i, ∫⁻ p, H i p ∂chainProduct (fun k => B' k ω) (w i) K := by
    filter_upwards [ae_all_iff.2 hchains] with ω hω
    apply Finset.prod_congr rfl
    intro i _
    rw [hω i]
  have hdet (ω) : (∏ i, ∫⁻ p, H i p ∂chainProduct (fun k => B' k ω) (w i) K) =
      ∫⁻ p, tupleChainPathTest K w H p
        ∂Measure.pi (fun k : Fin (K + 1) => blockTupleMeasure n (B' k ω)) := by
    let : ∀ k, IsLocallyFiniteMeasure (B' k ω) := fun k => hlf k ω
    exact lintegral_prod_chainProduct_eq_lintegral_tuplePaths K (fun k => B' k ω) w hwm H hH
  have hBm (k : Fin (K + 1)) : Measurable (B' k) := (hB' k (Nat.le_of_lt_succ k.is_lt)).1
  have hpathm := measurable_pi_blockTupleMeasure (K + 1) n (fun k => B' k) hBm (fun k => hlf k)
  have hmean := bind_pi_blockTupleModification_eq P (K + 1) hn1 hn
    (fun k => τ k) (fun k => hτ k (Nat.le_of_lt_succ k.is_lt)) (fun k => B k)
    (fun k => hB k (Nat.le_of_lt_succ k.is_lt)) hind E
  calc
    _ = ∫⁻ ω, ∏ i, ∫⁻ p, H i p ∂chainProduct (fun k => B' k ω) (w i) K ∂P := lintegral_congr_ae hprod
    _ = ∫⁻ ω, ∫⁻ p, tupleChainPathTest K w H p
        ∂Measure.pi (fun k : Fin (K + 1) => blockTupleMeasure n (B' k ω)) ∂P :=
      lintegral_congr hdet
    _ = ∫⁻ p, tupleChainPathTest K w H p
        ∂P.bind (fun ω => Measure.pi (fun k : Fin (K + 1) => blockTupleMeasure n (B' k ω))) :=
      (Measure.lintegral_bind hpathm.aemeasurable (measurable_tupleChainPathTest K hwm hH).aemeasurable).symm
    _ = _ := by rw [hmean]

end Critical2DKPZ.SHF.Tsai

end
