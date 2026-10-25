/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ChainLpFour
public import Critical2DKPZ.SHF.Tsai.MollifierSubsequences

/-! # Actual chain moments with independently chosen connector indices

Shifting each applicable family places any prescribed finite collection of
connector indices at the common index zero. The signed chain moments and
`L⁴` membership therefore apply to the actual chain with those connectors.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

section Indexed

variable {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (K : ℕ) (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k)
  (B : ℕ → Ω → Measure (Plane × Plane)) (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
  (hind : iIndepFun (fun k : Fin (K + 1) => B k) P)
  (u : ℕ → ℕ → Plane → ℝ) (hu : ∀ k, IsL2ApplicableMollifier (u k))
  (q : ℕ → ℕ) (g g' : Plane → ℝ) (hg : MemLp g 2) (hg' : MemLp g' 2)

include hτ hB hind hu hg hg'

/-- Any individual choice of connector indices has a genuine fourth moment. -/
theorem memLp_chainPairing_four_at_indices :
    MemLp (fun ω => ∫ p, g p.1 * g' p.2
      ∂chainProduct (fun k => B k ω) (fun k => u k (q k)) K) 4 P := by
  let v (k j : ℕ) := u k (j + q k)
  have hv (k) : IsL2ApplicableMollifier (v k) := (hu k).comp_tendsto (tendsto_add_atTop_nat (q k))
  simpa only [v, Nat.zero_add] using memLp_chainPairing_four K τ hτ B hB hind v hv 0 g g' hg hg'

/-- The actual endpoint test is integrable inside a chain with any connector indices almost surely. -/
theorem ae_integrable_chainPairing_at_indices :
    ∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane => g p.1 * g' p.2)
      (chainProduct (fun k => B k ω) (fun k => u k (q k)) K) := by
  let v (k j : ℕ) := u k (j + q k)
  have hv (k) : IsL2ApplicableMollifier (v k) := (hu k).comp_tendsto (tendsto_add_atTop_nat (q k))
  have h := (integral_prod_chainProduct_eq K τ hτ B hB hind (n := 1) (by norm_num) (by norm_num)
    (fun _ => v) (fun _ => hv) 0 (fun _ => g) (fun _ => g') (fun _ => hg) (fun _ => hg')).1
  have h0 := h.mono (fun _ hω => hω 0)
  simpa only [v, Nat.zero_add] using h0

end Indexed

/-- Finite arrays of independent moment blocks give integrable actual endpoint tests
and `L⁴` pairings, at any independently chosen connector indices. -/
theorem chainPairing_four_finiteBlocks {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (K : ℕ) (τ : Fin (K + 1) → ℝ)
    (hτ : ∀ i, 0 < τ i) (B : Fin (K + 1) → Ω → Measure (Plane × Plane))
    (hB : ∀ i, HasDeltaBoseMoments θ (τ i) P (B i)) (hind : iIndepFun B P)
    (u : ℕ → ℕ → Plane → ℝ) (hu : ∀ k, IsL2ApplicableMollifier (u k)) (q : ℕ → ℕ)
    (g g' : Plane → ℝ) (hg : MemLp g 2) (hg' : MemLp g' 2) :
    (∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane => g p.1 * g' p.2)
      (chainProduct (fun k => B (Fin.ofNat (K + 1) k) ω) (fun k => u k (q k)) K)) ∧
    MemLp (fun ω => ∫ p, g p.1 * g' p.2
      ∂chainProduct (fun k => B (Fin.ofNat (K + 1) k) ω) (fun k => u k (q k)) K) 4 P := by
  let Bn (k : ℕ) := B (Fin.ofNat (K + 1) k)
  let τn (k : ℕ) := τ (Fin.ofNat (K + 1) k)
  have hτn (k : ℕ) (_ : k ≤ K) : 0 < τn k := hτ _
  have hBn (k : ℕ) (_ : k ≤ K) : HasDeltaBoseMoments θ (τn k) P (Bn k) := hB _
  have hindn : iIndepFun (fun k : Fin (K + 1) => Bn k) P := by
    simpa only [Bn, Fin.ofNat_eq_cast, Fin.cast_val_eq_self] using hind
  exact ⟨ae_integrable_chainPairing_at_indices K τn hτn Bn hBn hindn u hu q g g' hg hg',
    memLp_chainPairing_four_at_indices K τn hτn Bn hBn hindn u hu q g g' hg hg'⟩

end Critical2DKPZ.SHF.Tsai

end
