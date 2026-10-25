/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.CoordinateBlockMoments
public import Critical2DKPZ.SHF.Tsai.SplitCopyBlocks
public import Critical2DKPZ.SHF.Tsai.SelectedBlockPositiveMoments
public import Critical2DKPZ.SHF.Tsai.ChainAbsoluteMoments

/-! # Finite absolute moments of the conditional selected-block tests

The outer samples are the remaining independent coordinate copies. Inserting
the selected sample preserves product probability. The selected-block moment
identity therefore turns their unconditional positive chain moment into the
integral of the conditional endpoint tests against the moment measure.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- Conditional positive absolute endpoint tests have finite joint moment integral over the outer samples. -/
theorem lintegral_prod_positiveChainBlockTests_lt_top {θ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ) (j : Fin (K + 1))
    (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k) (B : ℕ → Ω → Measure (Plane × Plane))
    (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hlf : ∀ k ≤ K, ∀ ω, IsLocallyFiniteMeasure (B k ω))
    {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 4)
    (w : Fin n → ℕ → ℕ → Plane → ℝ) (hw : ∀ i k, IsL2ApplicableMollifier (w i k)) (ℓ : ℕ)
    (g g' : Fin n → Plane → ℝ) (hgm : ∀ i, Measurable (g i)) (hg'm : ∀ i, Measurable (g' i))
    (hg : ∀ i, MemLp (g i) 2) (hg' : ∀ i, MemLp (g' i) 2) :
    (∫⁻ a : Fin K → Ω, (∫⁻ q : Configuration n × Configuration n,
      momentKernel n θ (τ j) q.1 q.2 * ∏ i,
        positiveChainBlockTest K j (outerCopyBlock K j B a) (fun k => w i k ℓ)
          (fun p => ENNReal.ofReal |g i p.1| * ENNReal.ofReal |g' i p.2|) (q.1 i, q.2 i) ∂volume)
      ∂Measure.pi (fun _ : Fin K => P)) < ⊤ := by
  classical
  let Q := Measure.pi (fun _ : Fin K => P)
  let R := Measure.pi (fun _ : Fin (K + 1) => P)
  let C (k : ℕ) (ω : Fin (K + 1) → Ω) := coordinateCopyBlock K B ω k
  have hCm (k) (hk : k ≤ K) : Measurable (C k) :=
    measurable_coordinateCopyBlock K B (fun k hk => (hB k hk).1) k hk
  have hClf (ω : Fin (K + 1) → Ω) (k) (hk : k ≤ K) : IsLocallyFiniteMeasure (C k ω) := by
    simp only [C, coordinateCopyBlock, dite_eq_left hk]
    exact hlf k hk _
  have hCB (k) (hk : k ≤ K) : HasDeltaBoseMoments θ (τ k) R (C k) :=
    hasDeltaBoseMoments_coordinateCopyBlock P K τ B hB k hk
  have hindC : iIndepFun (fun k : Fin (K + 1) => C k) R :=
    iIndepFun_coordinateCopyBlock P K B (fun k hk => (hB k hk).1)
  let F (i : Fin n) (p : Plane × Plane) := ENNReal.ofReal |g i p.1| * ENNReal.ofReal |g' i p.2|
  have hF (i) : Measurable (F i) := by
    simpa only [F, Real.norm_eq_abs, Function.comp_def, Pi.mul_def] using
      (((hgm i).norm.ennreal_ofReal.comp measurable_fst).mul
        ((hg'm i).norm.ennreal_ofReal.comp measurable_snd))
  let L (ω : Fin (K + 1) → Ω) := ∏ i, ∫⁻ p, F i p
    ∂chainProduct (fun k => C k ω) (fun k => w i k ℓ) K
  have hL : Measurable L := Finset.measurable_prod _ fun i _ =>
    measurable_lintegral_chainProduct K C hCm hClf _
      (fun k => ((hw i k).2.1 ℓ).measurable) _ (hF i)
  have hfinite : (∫⁻ ω, L ω ∂R) < ⊤ :=
    lintegral_prod_abs_chainPairings_lt_top K τ hτ C hCB hindC hn1 hn w hw ℓ g g' hgm hg'm hg hg'
  let φ (q : (Fin K → Ω) × Ω) := Fin.insertNth (α := fun _ : Fin (K + 1) => Ω) j q.2 q.1
  have hφ : MeasurePreserving φ (Q.prod P) R := measurePreserving_insertCopyCoordinate P K j
  have hsplit (a : Fin K → Ω) : (∫⁻ ω, L (φ (a, ω)) ∂P) =
      ∫⁻ q : Configuration n × Configuration n, momentKernel n θ (τ j) q.1 q.2 *
        ∏ i, positiveChainBlockTest K j (outerCopyBlock K j B a) (fun k => w i k ℓ) (F i)
          (q.1 i, q.2 i) := by
    have houter (k : ℕ) : IsLocallyFiniteMeasure (outerCopyBlock K j B a k) :=
      locallyFinite_outerCopyBlock K j B hlf a k
    let : ∀ k, IsLocallyFiniteMeasure (outerCopyBlock K j B a k) := houter
    have heq (ω) : L (φ (a, ω)) = ∏ i, ∫⁻ p, F i p
        ∂chainProduct (Function.update (outerCopyBlock K j B a) j (B j ω)) (fun k => w i k ℓ) K := by
      dsimp only [L, φ, C]
      rw [coordinateCopyBlock_insertNth_eq_update_outer]
    calc
      _ = ∫⁻ ω, ∏ i, ∫⁻ p, F i p
          ∂chainProduct (Function.update (outerCopyBlock K j B a) j (B j ω)) (fun k => w i k ℓ) K ∂P :=
        lintegral_congr heq
      _ = _ := (hB j (Nat.le_of_lt_succ j.is_lt)).lintegral_prod_chain_update_eq
        (hτ j (Nat.le_of_lt_succ j.is_lt)) (outerCopyBlock K j B a) K j hn1 hn
        (fun i k => w i k ℓ) (fun i k => ((hw i k).2.1 ℓ).measurable) F hF
  have heq : (∫⁻ a : Fin K → Ω, (∫⁻ q : Configuration n × Configuration n,
      momentKernel n θ (τ j) q.1 q.2 * ∏ i,
        positiveChainBlockTest K j (outerCopyBlock K j B a) (fun k => w i k ℓ) (F i) (q.1 i, q.2 i) ∂volume)
      ∂Q) = ∫⁻ ω, L ω ∂R := by
    calc
      _ = ∫⁻ a, ∫⁻ ω, L (φ (a, ω)) ∂P ∂Q := lintegral_congr (fun a => (hsplit a).symm)
      _ = ∫⁻ q, L (φ q) ∂Q.prod P :=
        (lintegral_prod _ (hL.comp hφ.measurable).aemeasurable).symm
      _ = _ := hφ.lintegral_comp hL
  exact heq.trans_lt hfinite

end Critical2DKPZ.SHF.Tsai

end
