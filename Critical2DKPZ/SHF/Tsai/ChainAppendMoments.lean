/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ChainPairingIndices
public import Critical2DKPZ.SHF.Tsai.BlockMomentTransport
import Critical2DKPZ.SHF.Tsai.CouplingIndependence
import Critical2DKPZ.SHF.Tsai.ChainMeasurability

/-! # Moments for a chain with an independent appended block

Finite-block moment bounds apply to the literal product of a prefix chain
and an independent final block, with independently selected connector indices.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace Critical2DKPZ.SHF.Tsai

/-- Appending an independent block gives integrable endpoint tests and a genuine fourth moment. -/
theorem chainPairing_four_append_prod {θ τ : ℝ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (K : ℕ) (σ : Fin (K + 1) → ℝ) (hσ : ∀ i, 0 < σ i)
    (B : Fin (K + 1) → Ω → Measure (Plane × Plane))
    (hB : ∀ i, HasDeltaBoseMoments θ (σ i) P (B i)) (hind : iIndepFun B P)
    (A : Ω' → Measure (Plane × Plane)) (hA : HasDeltaBoseMoments θ τ P' A) (hτ : 0 < τ)
    (u : ℕ → ℕ → Plane → ℝ) (hu : ∀ k, IsL2ApplicableMollifier (u k))
    (q : ℕ → ℕ) (g g' : Plane → ℝ) (hg : MemLp g 2) (hg' : MemLp g' 2) :
    (∀ᵐ ω : Ω' × Ω ∂P'.prod P, Integrable (fun p : Plane × Plane => g p.1 * g' p.2)
      (smoothedProductMeasure
        (chainProduct (fun k => B (Fin.ofNat (K + 1) k) ω.2) (fun k => u k (q k)) K)
        (u K (q K)) (A ω.1))) ∧
    MemLp (fun ω : Ω' × Ω => ∫ p, g p.1 * g' p.2 ∂smoothedProductMeasure
      (chainProduct (fun k => B (Fin.ofNat (K + 1) k) ω.2) (fun k => u k (q k)) K)
      (u K (q K)) (A ω.1)) 4 (P'.prod P) := by
  let σ' : Fin (K + 2) → ℝ := Fin.snoc σ τ
  let B' (i : Fin (K + 2)) (ω : Ω' × Ω) :=
    Fin.snoc (α := fun _ : Fin (K + 2) => Measure (Plane × Plane))
      (fun j => B j ω.2) (A ω.1) i
  have hσ' (i : Fin (K + 2)) : 0 < σ' i := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [σ', Fin.snoc_last] using hτ
    · simpa only [σ', Fin.snoc_castSucc] using hσ j
  have hB' (i : Fin (K + 2)) : HasDeltaBoseMoments θ (σ' i) (P'.prod P) (B' i) :=
    hasDeltaBoseMoments_fin_snoc_prod P P' A hA σ B hB i
  have hind' : iIndepFun B' (P'.prod P) :=
    iIndepFun_fin_snoc_prod P P' A B hA.1 (fun i => (hB i).1) hind
  have h := chainPairing_four_finiteBlocks (K + 1) σ' hσ' B' hB' hind' u hu q g g' hg hg'
  simpa only [B', chainProduct_fin_snoc] using h

end Critical2DKPZ.SHF.Tsai

end
