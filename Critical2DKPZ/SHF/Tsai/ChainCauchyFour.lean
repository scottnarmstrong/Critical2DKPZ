/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ChainLpFour
public import Critical2DKPZ.SHF.Tsai.MollifierSubsequences
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! # Cauchy convergence of actual chain pairings in `L⁴`

The fourth-moment comparison applies after any two diverging reindexings of
the mollifiers. The sequential characterization of the two-index limit
therefore gives the `L⁴` Cauchy criterion.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace Critical2DKPZ.SHF.Tsai

local instance instFactOneLeFourENNReal : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The actual endpoint pairings, as `L⁴` classes, form a Cauchy sequence. -/
theorem cauchySeq_chainPairing_toLp_four {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (K : ℕ) (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k)
    (B : ℕ → Ω → Measure (Plane × Plane)) (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hind : iIndepFun (fun k : Fin (K + 1) => B k) P)
    (w : ℕ → ℕ → Plane → ℝ) (hw : ∀ k, IsL2ApplicableMollifier (w k))
    (g g' : Plane → ℝ) (hg : MemLp g 2) (hg' : MemLp g' 2) :
    CauchySeq (fun ℓ => (memLp_chainPairing_four K τ hτ B hB hind w hw ℓ g g' hg hg').toLp
      (fun ω => ∫ p, g p.1 * g' p.2 ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K)) := by
  let φ (ℓ : ℕ) (ω : Ω) := ∫ p, g p.1 * g' p.2
    ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K
  have hφ (ℓ) : MemLp (φ ℓ) 4 P := memLp_chainPairing_four K τ hτ B hB hind w hw ℓ g g' hg hg'
  let X (ℓ : ℕ) := (hφ ℓ).toLp (φ ℓ)
  change CauchySeq X
  apply cauchySeq_iff_tendsto_dist_atTop_0.2
  apply Filter.tendsto_iff_seq_tendsto.2
  intro r hr
  have hrprod : Tendsto r atTop (atTop ×ˢ atTop : Filter (ℕ × ℕ)) := by
    rwa [prod_atTop_atTop_eq]
  let σ (j : ℕ) := (r j).1
  let ρ (j : ℕ) := (r j).2
  have hσ : Tendsto σ atTop atTop := hrprod.fst
  have hρ : Tendsto ρ atTop atTop := hrprod.snd
  have hdiff := tendsto_integral_chainProduct_sub_pow_four K τ hτ B hB hind
    (fun k j => w k (σ j)) (fun k j => w k (ρ j))
    (fun k => (hw k).comp_tendsto hσ) (fun k => (hw k).comp_tendsto hρ) g g' hg hg'
  let δ (j : ℕ) (ω : Ω) := φ (σ j) ω - φ (ρ j) ω
  have hδ (j) : MemLp (δ j) 4 P := (hφ (σ j)).sub (hφ (ρ j))
  have hnorm := tendsto_eLpNorm_four_of_integral_pow_four P δ
    (fun j => (hδ j).aestronglyMeasurable) hdiff.1 hdiff.2
  have hreal := (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hnorm
  simp only [ENNReal.toReal_zero] at hreal
  have hdist (j) : dist (X (σ j)) (X (ρ j)) = (eLpNorm (δ j) 4 P).toReal := by
    change dist ((hφ (σ j)).toLp (φ (σ j))) ((hφ (ρ j)).toLp (φ (ρ j))) = _
    rw [Lp.dist_edist, Lp.edist_toLp_toLp]
    rfl
  change Tendsto (fun j => dist (X (σ j)) (X (ρ j))) atTop (𝓝 0)
  simpa only [hdist, Function.comp_def] using hreal

/-- Every applicable chain family has a genuine `L⁴` limit. -/
theorem exists_chainPairing_toLp_four_limit {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (K : ℕ) (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k)
    (B : ℕ → Ω → Measure (Plane × Plane)) (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hind : iIndepFun (fun k : Fin (K + 1) => B k) P)
    (w : ℕ → ℕ → Plane → ℝ) (hw : ∀ k, IsL2ApplicableMollifier (w k))
    (g g' : Plane → ℝ) (hg : MemLp g 2) (hg' : MemLp g' 2) :
    ∃ F : Lp ℝ 4 P, Tendsto
      (fun ℓ => (memLp_chainPairing_four K τ hτ B hB hind w hw ℓ g g' hg hg').toLp
        (fun ω => ∫ p, g p.1 * g' p.2 ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K))
      atTop (𝓝 F) :=
  cauchySeq_tendsto_of_complete (cauchySeq_chainPairing_toLp_four K τ hτ B hB hind w hw g g' hg hg')

end Critical2DKPZ.SHF.Tsai

end
