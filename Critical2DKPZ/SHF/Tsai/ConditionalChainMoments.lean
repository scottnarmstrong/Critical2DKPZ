/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConditionalChainTestIntegrability
public import Critical2DKPZ.SHF.Tsai.SelectedBlockSignedMoments
public import Critical2DKPZ.SHF.Tsai.SignedChainMoments
public import Critical2DKPZ.SHF.Tsai.MomentKernelMeasureFiniteness

/-! # Conditional signed moments of coordinate-copy chains

Conditioning on all but one independent block gives integrable selected-block chain
moments evaluated by the full endpoint moment kernel.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- Almost every outer sample has the integrable selected-block chain moment given by the full endpoint kernel. -/
theorem ae_integral_prod_chain_update_eq {θ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ) (j : Fin (K + 1))
    (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k) (B : ℕ → Ω → Measure (Plane × Plane))
    (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hlf : ∀ k ≤ K, ∀ ω, IsLocallyFiniteMeasure (B k ω))
    {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 4)
    (w : Fin n → ℕ → ℕ → Plane → ℝ) (hw : ∀ i k, IsL2ApplicableMollifier (w i k)) (ℓ : ℕ)
    (g g' : Fin n → Plane → ℝ) (hgm : ∀ i, Measurable (g i)) (hg'm : ∀ i, Measurable (g' i))
    (hg : ∀ i, MemLp (g i) 2) (hg' : ∀ i, MemLp (g' i) 2) :
    ∀ᵐ a : Fin K → Ω ∂Measure.pi (fun _ : Fin K => P),
      Integrable (fun ω => ∏ i, ∫ p, g i p.1 * g' i p.2
        ∂chainProduct (Function.update (outerCopyBlock K j B a) j (B j ω)) (fun k => w i k ℓ) K) P ∧
      (∫ ω, ∏ i, (∫ p, g i p.1 * g' i p.2
        ∂chainProduct (Function.update (outerCopyBlock K j B a) j (B j ω)) (fun k => w i k ℓ) K) ∂P) =
        ∫ q : Configuration n × Configuration n,
          ∏ i, chainBlockTest K j (outerCopyBlock K j B a) (fun k => w i k ℓ)
            (fun p => g i p.1 * g' i p.2) (q.1 i, q.2 i)
              ∂volume.withDensity (Function.uncurry (momentKernel n θ (τ j))) := by
  classical
  let Q := Measure.pi (fun _ : Fin K => P)
  let R := Measure.pi (fun _ : Fin (K + 1) => P)
  let ν := volume.withDensity (Function.uncurry (momentKernel n θ (τ j)))
  let : IsLocallyFiniteMeasure ν := locallyFinite_momentKernelMeasure n θ (hτ j (Nat.le_of_lt_succ j.is_lt))
  let C (k : ℕ) (ω : Fin (K + 1) → Ω) := coordinateCopyBlock K B ω k
  have hCB (k) (hk : k ≤ K) : HasDeltaBoseMoments θ (τ k) R (C k) :=
    hasDeltaBoseMoments_coordinateCopyBlock P K τ B hB k hk
  have hindC : iIndepFun (fun k : Fin (K + 1) => C k) R :=
    iIndepFun_coordinateCopyBlock P K B (fun k hk => (hB k hk).1)
  have hinnerCopy := (integral_prod_chainProduct_eq K τ hτ C hCB hindC hn1 hn w hw ℓ g g' hg hg').1
  let φ (q : (Fin K → Ω) × Ω) := Fin.insertNth (α := fun _ : Fin (K + 1) => Ω) j q.2 q.1
  have hφ : MeasurePreserving φ (Q.prod P) R := measurePreserving_insertCopyCoordinate P K j
  have hinnerSplit : ∀ᵐ aω : (Fin K → Ω) × Ω ∂Q.prod P, ∀ i,
      Integrable (fun p : Plane × Plane => g i p.1 * g' i p.2)
        (chainProduct (Function.update (outerCopyBlock K j B aω.1) j (B j aω.2))
          (fun k => w i k ℓ) K) := by
    have h := hφ.quasiMeasurePreserving.ae hinnerCopy
    simpa only [C, φ, coordinateCopyBlock_insertNth_eq_update_outer] using h
  have hinnerRows := Measure.ae_ae_of_ae_prod hinnerSplit
  have hΓI := integrable_prod_chainBlockTests P K j τ hτ B hB hlf hn1 hn w hw ℓ
    g g' hgm hg'm hg hg'
  have hΓRows := hΓI.prod_right_ae
  filter_upwards [hinnerRows, hΓRows] with a hchainI htestI
  have houter (k : ℕ) : IsLocallyFiniteMeasure (outerCopyBlock K j B a k) :=
    locallyFinite_outerCopyBlock K j B hlf a k
  let : ∀ k, IsLocallyFiniteMeasure (outerCopyBlock K j B a k) := houter
  exact (hB j (Nat.le_of_lt_succ j.is_lt)).integral_prod_chain_update_eq
    (hτ j (Nat.le_of_lt_succ j.is_lt)) (outerCopyBlock K j B a) K j hn1 hn
    (fun i k => w i k ℓ) (fun i k => ((hw i k).2.1 ℓ).measurable)
    (fun i p => g i p.1 * g' i p.2) hchainI htestI

end Critical2DKPZ.SHF.Tsai

end
