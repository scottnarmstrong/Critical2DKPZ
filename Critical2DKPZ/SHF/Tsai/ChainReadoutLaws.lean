/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ChainMeasurability
public import Critical2DKPZ.RandomMeasure.GeneralRandom
import Mathlib.Probability.Kernel.MeasurableIntegral

/-! # Chain pairing laws from finite block tuple laws

Locally finite modifications give measurable pairing maps on all finite measure tuples,
agreeing with chain pairings on locally finite inputs. Equal block tuple laws therefore
give equal joint laws of finite families of endpoint pairings.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace Critical2DKPZ.SHF.Tsai

/-- The chain pairing map on all finite measure tuples after locally finite modification of each input. -/
def modifiedChainReadout (E : CompactExhaustion (Plane × Plane)) (K : ℕ)
    (w : ℕ → Plane → ℝ) (F : Plane × Plane → ℝ) (μ : Fin (K + 1) → Measure (Plane × Plane)) : ℝ :=
  ∫ p, F p ∂chainProduct (fun k => if hk : k ≤ K then
    RandomMeasure.locallyFiniteMeasureModification E id (μ ⟨k, Nat.lt_succ_of_le hk⟩) else 0) w K

/-- A measurable endpoint test gives a measurable modified chain pairing map. -/
theorem measurable_modifiedChainReadout (E : CompactExhaustion (Plane × Plane)) (K : ℕ)
    (w : ℕ → Plane → ℝ) (hw : ∀ k, Measurable (w k))
    (F : Plane × Plane → ℝ) (hF : Measurable F) : Measurable (modifiedChainReadout E K w F) := by
  classical
  let B (k : ℕ) (μ : Fin (K + 1) → Measure (Plane × Plane)) := if hk : k ≤ K then
    RandomMeasure.locallyFiniteMeasureModification E id (μ ⟨k, Nat.lt_succ_of_le hk⟩) else 0
  have hBm (k) (hk : k ≤ K) : Measurable (B k) := by
    simp only [B, dite_eq_left hk]
    exact (RandomMeasure.measurable_locallyFiniteMeasureModification E id measurable_id).comp
      (measurable_pi_apply _)
  have hBlf (μ : Fin (K + 1) → Measure (Plane × Plane)) (k) (hk : k ≤ K) :
      IsLocallyFiniteMeasure (B k μ) := by
    simp only [B, dite_eq_left hk]
    exact RandomMeasure.locallyFinite_locallyFiniteMeasureModification E id _
  have hchain := measurable_chainProduct K B hBm hBlf w hw
  let κ : Kernel (Measure (Plane × Plane)) (Plane × Plane) := ⟨id, measurable_id⟩
  have hread : Measurable (fun μ : Measure (Plane × Plane) => ∫ p, F p ∂μ) :=
    (hF.stronglyMeasurable.integral_kernel (κ := κ)).measurable
  exact hread.comp hchain

/-- For locally finite inputs the modified pairing equals the integral against the chain measure. -/
theorem modifiedChainReadout_eq_of_locallyFinite (E : CompactExhaustion (Plane × Plane)) (K : ℕ)
    (μ : ℕ → Measure (Plane × Plane)) (hlf : ∀ k ≤ K, IsLocallyFiniteMeasure (μ k))
    (w : ℕ → Plane → ℝ) (F : Plane × Plane → ℝ) :
    modifiedChainReadout E K w F (fun k => μ k) = ∫ p, F p ∂chainProduct μ w K := by
  classical
  have hchain : chainProduct (fun k => if hk : k ≤ K then
      RandomMeasure.locallyFiniteMeasureModification E id (μ k) else 0) w K =
      chainProduct μ w K := by
    apply chainProduct_congr_prefix
    intro k hk
    simp only [dite_eq_left hk]
    exact RandomMeasure.locallyFiniteMeasureModification_apply_of_isLocallyFinite E id _ (hlf k hk)
  exact congrArg (fun ν : Measure (Plane × Plane) => ∫ p, F p ∂ν) hchain

/-- For a finite tuple of locally finite measures the modified pairing equals the finite-block chain pairing. -/
theorem modifiedChainReadout_eq_finiteBlocks (E : CompactExhaustion (Plane × Plane)) (K : ℕ)
    (μ : Fin (K + 1) → Measure (Plane × Plane)) (hlf : ∀ i, IsLocallyFiniteMeasure (μ i))
    (w : ℕ → Plane → ℝ) (F : Plane × Plane → ℝ) :
    modifiedChainReadout E K w F μ =
      ∫ p, F p ∂chainProduct (fun k => μ (Fin.ofNat (K + 1) k)) w K := by
  have h := modifiedChainReadout_eq_of_locallyFinite E K (fun k => μ (Fin.ofNat (K + 1) k))
    (fun k _ => hlf _) w F
  simpa only [Fin.ofNat_eq_cast, Fin.cast_val_eq_self] using h

/-- Equal finite block tuple laws give equal joint laws of measurable endpoint chain pairings. -/
theorem map_chainReadouts_eq_of_block_law {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω') (K : ℕ)
    (B : ℕ → Ω → Measure (Plane × Plane)) (C : ℕ → Ω' → Measure (Plane × Plane))
    (hB : ∀ k ≤ K, Measurable (B k)) (hC : ∀ k ≤ K, Measurable (C k))
    (hlfB : ∀ k ≤ K, ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (B k ω))
    (hlfC : ∀ k ≤ K, ∀ᵐ ω ∂P', IsLocallyFiniteMeasure (C k ω))
    (hLaw : P.map (fun ω (k : Fin (K + 1)) => B k ω) =
      P'.map (fun ω (k : Fin (K + 1)) => C k ω))
    (w : ℕ → Plane → ℝ) (hw : ∀ k, Measurable (w k)) {ι : Type*}
    (F : ι → Plane × Plane → ℝ) (hF : ∀ i, Measurable (F i)) :
    P.map (fun ω i => ∫ p, F i p ∂chainProduct (fun k => B k ω) w K) =
      P'.map (fun ω i => ∫ p, F i p ∂chainProduct (fun k => C k ω) w K) := by
  let E := CompactExhaustion.choice (Plane × Plane)
  let Φ (μ : Fin (K + 1) → Measure (Plane × Plane)) (i : ι) := modifiedChainReadout E K w (F i) μ
  have hΦ : Measurable Φ := Measurable.of_eval fun i => measurable_modifiedChainReadout E K w hw (F i) (hF i)
  have hBm : Measurable (fun ω (k : Fin (K + 1)) => B k ω) :=
    Measurable.of_eval fun k => hB k (Nat.le_of_lt_succ k.is_lt)
  have hCm : Measurable (fun ω (k : Fin (K + 1)) => C k ω) :=
    Measurable.of_eval fun k => hC k (Nat.le_of_lt_succ k.is_lt)
  have heqB : (fun ω i => ∫ p, F i p ∂chainProduct (fun k => B k ω) w K) =ᵐ[P]
      fun ω => Φ (fun k => B k ω) := by
    filter_upwards [ae_all_iff.2 (fun k => ae_all_iff.2 (fun hk => hlfB k hk))] with ω hω
    funext i
    exact (modifiedChainReadout_eq_of_locallyFinite E K (fun k => B k ω) hω w (F i)).symm
  have heqC : (fun ω i => ∫ p, F i p ∂chainProduct (fun k => C k ω) w K) =ᵐ[P']
      fun ω => Φ (fun k => C k ω) := by
    filter_upwards [ae_all_iff.2 (fun k => ae_all_iff.2 (fun hk => hlfC k hk))] with ω hω
    funext i
    exact (modifiedChainReadout_eq_of_locallyFinite E K (fun k => C k ω) hω w (F i)).symm
  rw [Measure.map_congr heqB, Measure.map_congr heqC]
  have hmap := congrArg (fun ν : Measure (Fin (K + 1) → Measure (Plane × Plane)) => ν.map Φ) hLaw
  rw [Measure.map_map hΦ hBm, Measure.map_map hΦ hCm] at hmap
  exact hmap

end Critical2DKPZ.SHF.Tsai

end
