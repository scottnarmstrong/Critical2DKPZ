/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.MixedChainTuples
public import Critical2DKPZ.SHF.Tsai.TupleChainPaths

/-! # Mixed chain moments as deterministic kernel path integrals

The literal particle-dependent chains are regrouped into endpoint tuple
paths. Canonical modifications preserve their values almost surely, while
independence replaces each tuple by its full or partially heat-replaced
moment measure.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- Positive mixed chain moments are the path integral with the selected mixed block kernel. -/
theorem lintegral_prod_chainProduct_update_heat_eq_lintegral_momentPaths
    {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (K j : ℕ) (hj : j ≤ K) (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k)
    (B : ℕ → Ω → Measure (Plane × Plane))
    (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hind : iIndepFun (fun k : Fin (K + 1) => B k) P)
    {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 4) (S : Finset (Fin n))
    (w : Fin n → ℕ → Plane → ℝ) (hwm : ∀ i k, Measurable (w i k))
    (H : Fin n → Plane × Plane → ℝ≥0∞) (hH : ∀ i, Measurable (H i)) :
    (∫⁻ ω, ∏ i, (∫⁻ p, H i p ∂chainProduct
      (if i ∈ S then (fun k => B k ω) else Function.update (fun k => B k ω) j (heatBlock (τ j)))
      (w i) K) ∂P) =
      ∫⁻ p, tupleChainPathTest K w H p ∂Measure.pi (fun k : Fin (K + 1) =>
        volume.withDensity (Function.uncurry (Function.update (fun k => momentKernel n θ (τ k)) j
          (mixedBlockKernel n θ (τ j) S) k))) := by
  classical
  let E := CompactExhaustion.choice (Plane × Plane)
  let B' k := RandomMeasure.locallyFiniteMeasureModification E (B k)
  have hlf (k ω) : IsLocallyFiniteMeasure (B' k ω) :=
    RandomMeasure.locallyFinite_locallyFiniteMeasureModification E (B k) ω
  have hBm (k) (hk : k ≤ K) : Measurable (B' k) :=
    ((hB k hk).locallyFiniteMeasureModification E).1
  have hEq (k) (hk : k ≤ K) : B k =ᵐ[P] B' k :=
    (RandomMeasure.ae_eq_radonValuedModification E P (B k) (hB k hk).2.1).symm
  let C (i : Fin n) (k : ℕ) (ω : Ω) :=
    if k = j then (if i ∈ S then B k ω else heatBlock (τ k)) else B k ω
  let C' (i : Fin n) (k : ℕ) (ω : Ω) :=
    if k = j then (if i ∈ S then B' k ω else heatBlock (τ k)) else B' k ω
  have hCeq (i) (k) (hk : k ≤ K) : C i k =ᵐ[P] C' i k := by
    filter_upwards [hEq k hk] with ω hω
    dsimp only [C, C']
    rw [hω]
  have hchains (i) := chainProduct_congr_ae K (C i) (C' i) (hCeq i) (w i)
  have hactual (i : Fin n) (ω : Ω) :
      (if i ∈ S then (fun k => B k ω) else Function.update (fun k => B k ω) j (heatBlock (τ j))) =
        fun k => C i k ω := by
    funext k
    by_cases hi : i ∈ S
    · simp only [ite_eq_left hi, C]
      split_ifs <;> rfl
    · simp only [ite_eq_right hi, C]
      by_cases hk : k = j
      · subst k
        simp
      · simp only [Function.update_of_ne hk, ite_eq_right hk]
  have hprod : (fun ω => ∏ i, ∫⁻ p, H i p ∂chainProduct
      (if i ∈ S then (fun k => B k ω) else Function.update (fun k => B k ω) j (heatBlock (τ j)))
      (w i) K) =ᵐ[P] fun ω => ∏ i, ∫⁻ p, H i p ∂chainProduct (fun k => C' i k ω) (w i) K := by
    filter_upwards [ae_all_iff.2 hchains] with ω hω
    apply Finset.prod_congr rfl
    intro i _
    rw [hactual i ω, hω i]
  have hClf (i k ω) : IsLocallyFiniteMeasure (C' i k ω) := by
    dsimp only [C']
    split_ifs
    · exact hlf k ω
    · exact locallyFinite_heatBlock (τ k)
    · exact hlf k ω
  have hdet (ω) : (∏ i, ∫⁻ p, H i p ∂chainProduct (fun k => C' i k ω) (w i) K) =
      ∫⁻ p, tupleChainPathTest K w H p
        ∂Measure.pi (fun k : Fin (K + 1) => endpointTupleMeasure (fun i => C' i k ω)) := by
    have hsf (i k) : SigmaFinite (C' i k ω) := by
      let : IsLocallyFiniteMeasure (C' i k ω) := hClf i k ω
      infer_instance
    let : ∀ i k, SigmaFinite (C' i k ω) := hsf
    exact lintegral_prod_chainProduct_eq_lintegral_endpointTuplePaths K (fun i k => C' i k ω)
      w hwm H hH
  have hCm (k : Fin (K + 1)) (i) : Measurable (C' i k) := by
    dsimp only [C']
    split_ifs
    · exact hBm k (Nat.le_of_lt_succ k.is_lt)
    · exact measurable_const
    · exact hBm k (Nat.le_of_lt_succ k.is_lt)
  have hpathm := measurable_pi_endpointTupleMeasure (K + 1) n (fun k i => C' i k)
    hCm (fun k i ω => hClf i k ω)
  let j' : Fin (K + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  have hmean := bind_pi_endpointTupleModification_update_heat_eq P (K + 1) j' hn1 hn S
    (fun k => τ k) (fun k => hτ k (Nat.le_of_lt_succ k.is_lt)) (fun k => B k)
    (fun k => hB k (Nat.le_of_lt_succ k.is_lt)) hind E
  have hmeasure (ω) :
      Measure.pi (fun k : Fin (K + 1) => endpointTupleMeasure (fun i => C' i k ω)) =
        Measure.pi (fun k : Fin (K + 1) => endpointTupleMeasure (fun i : Fin n =>
          if k = j' then (if i ∈ S then B' k ω else heatBlock (τ k)) else B' k ω)) := by
    congr 1
    funext k
    congr 1
    funext i
    dsimp only [C']
    have hiff : (k : ℕ) = j ↔ k = j' := by
      constructor
      · intro hk
        exact Fin.ext hk
      · intro hk
        exact congrArg Fin.val hk
    simp only [hiff]
  have hkernel : (fun k : Fin (K + 1) => volume.withDensity (Function.uncurry
      (Function.update (fun k : Fin (K + 1) => momentKernel n θ (τ k)) j'
        (mixedBlockKernel n θ (τ j') S) k))) =
      fun k : Fin (K + 1) => volume.withDensity (Function.uncurry
        (Function.update (fun k : ℕ => momentKernel n θ (τ k)) j
          (mixedBlockKernel n θ (τ j) S) k)) := by
    funext k
    by_cases hk : k = j'
    · subst k
      simp only [Function.update_self, j']
    · have hkn : (k : ℕ) ≠ j := by
        intro h
        exact hk (Fin.ext h)
      rw [Function.update_of_ne hk, Function.update_of_ne hkn]
  have hmean' : P.bind (fun ω => Measure.pi (fun k : Fin (K + 1) =>
      endpointTupleMeasure (fun i => C' i k ω))) =
        Measure.pi (fun k : Fin (K + 1) => volume.withDensity (Function.uncurry
          (Function.update (fun k : ℕ => momentKernel n θ (τ k)) j
            (mixedBlockKernel n θ (τ j) S) k))) := by
    simp_rw [hmeasure]
    exact hmean.trans (congrArg Measure.pi hkernel)
  calc
    _ = ∫⁻ ω, ∏ i, ∫⁻ p, H i p ∂chainProduct (fun k => C' i k ω) (w i) K ∂P :=
      lintegral_congr_ae hprod
    _ = ∫⁻ ω, ∫⁻ p, tupleChainPathTest K w H p
        ∂Measure.pi (fun k : Fin (K + 1) => endpointTupleMeasure (fun i => C' i k ω)) ∂P :=
      lintegral_congr hdet
    _ = ∫⁻ p, tupleChainPathTest K w H p ∂P.bind (fun ω => Measure.pi
        (fun k : Fin (K + 1) => endpointTupleMeasure (fun i => C' i k ω))) :=
      (Measure.lintegral_bind hpathm.aemeasurable
        (measurable_tupleChainPathTest K hwm hH).aemeasurable).symm
    _ = _ := by rw [hmean']

end Critical2DKPZ.SHF.Tsai

end
