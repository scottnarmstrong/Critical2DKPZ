/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.CenteredChainComparison
public import Critical2DKPZ.SHF.Tsai.CoordinateBlockMoments
public import Critical2DKPZ.SHF.Tsai.SplitCopyBlocks

/-! # Fourth moments after splitting one probability coordinate

The centered moments of the independent full copy family are integrable.
The measure-preserving insertion of the selected coordinate transfers this
integrability to the outer/inner probability space used for conditioning.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace Critical2DKPZ.SHF.Tsai

/-- The sum of centered fourth tensor moments is integrable on the split copy space. -/
theorem integrable_sum_centered_splitChain_pow_four {θ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ) (j : Fin (K + 1))
    (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k) (B : ℕ → Ω → Measure (Plane × Plane))
    (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (w : ℕ → ℕ → Plane → ℝ) (hw : ∀ k, IsL2ApplicableMollifier (w k)) (ℓ : ℕ)
    {m r : ℕ} (g g' : Fin m → Fin r → Plane → ℝ)
    (hg : ∀ a b, MemLp (g a b) 2) (hg' : ∀ a b, MemLp (g' a b) 2) :
    Integrable (fun q : (Fin K → Ω) × Ω => ∑ a,
      ((∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂chainProduct
        (Function.update (outerCopyBlock K j B q.1) j (B j q.2)) (fun k => w k ℓ) K) -
      ∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂chainProduct
        (Function.update (outerCopyBlock K j B q.1) j (heatBlock (τ j))) (fun k => w k ℓ) K) ^ 4)
      ((Measure.pi (fun _ : Fin K => P)).prod P) := by
  classical
  let R := Measure.pi (fun _ : Fin (K + 1) => P)
  let C (k : ℕ) (ω : Fin (K + 1) → Ω) := coordinateCopyBlock K B ω k
  have hC (k) (hk : k ≤ K) : HasDeltaBoseMoments θ (τ k) R (C k) :=
    hasDeltaBoseMoments_coordinateCopyBlock P K τ B hB k hk
  have hind : iIndepFun (fun k : Fin (K + 1) => C k) R :=
    iIndepFun_coordinateCopyBlock P K B (fun k hk => (hB k hk).1)
  have hI (a : Fin m) := (integral_sum_centeredChainPairings_pow_four_eq_of_moments
    K j (Nat.le_of_lt_succ j.is_lt) τ hτ C C hC hC hind hind w hw ℓ
      (g a) (g' a) (hg a) (hg' a)).1
  have hSum := integrable_finsetSum Finset.univ (fun a _ => hI a)
  have hSplit := (measurePreserving_insertCopyCoordinate P K j).integrable_comp_of_integrable hSum
  simpa only [Function.comp_def, C, coordinateCopyBlock_insertNth_eq_update_outer,
    Function.update_idem, Finset.sum_sub_distrib] using hSplit

/-- Both original and replacement split chains have integrable centered fourth moments. -/
theorem integrable_sum_centered_splitChain_swap_pow_four {θ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ) (j : Fin (K + 1))
    (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k) (B : ℕ → Ω → Measure (Plane × Plane))
    (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (B' : Ω → Measure (Plane × Plane)) (hB' : HasDeltaBoseMoments θ (τ j) P B')
    (w : ℕ → ℕ → Plane → ℝ) (hw : ∀ k, IsL2ApplicableMollifier (w k)) (ℓ : ℕ)
    {m r : ℕ} (g g' : Fin m → Fin r → Plane → ℝ)
    (hg : ∀ a b, MemLp (g a b) 2) (hg' : ∀ a b, MemLp (g' a b) 2) :
    Integrable (fun q : (Fin K → Ω) × Ω => ∑ a,
      ((∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂chainProduct
        (Function.update (outerCopyBlock K j B q.1) j (B j q.2)) (fun k => w k ℓ) K) -
      ∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂chainProduct
        (Function.update (outerCopyBlock K j B q.1) j (heatBlock (τ j))) (fun k => w k ℓ) K) ^ 4)
      ((Measure.pi (fun _ : Fin K => P)).prod P) ∧
    Integrable (fun q : (Fin K → Ω) × Ω => ∑ a,
      ((∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂chainProduct
        (Function.update (outerCopyBlock K j B q.1) j (B' q.2)) (fun k => w k ℓ) K) -
      ∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂chainProduct
        (Function.update (outerCopyBlock K j B q.1) j (heatBlock (τ j))) (fun k => w k ℓ) K) ^ 4)
      ((Measure.pi (fun _ : Fin K => P)).prod P) := by
  classical
  refine ⟨integrable_sum_centered_splitChain_pow_four P K j τ hτ B hB w hw ℓ g g' hg hg', ?_⟩
  let D := Function.update B j B'
  have hDj : D j = B' := Function.update_self _ _ _
  have hD (k) (hk : k ≤ K) : HasDeltaBoseMoments θ (τ k) P (D k) := by
    by_cases hkj : k = (j : ℕ)
    · subst k
      simpa only [hDj] using hB'
    · simpa only [D, Function.update_of_ne hkj] using hB k hk
  have hOuter : outerCopyBlock K j D = outerCopyBlock K j B := outerCopyBlock_update K j B B'
  have h := integrable_sum_centered_splitChain_pow_four P K j τ hτ D hD w hw ℓ g g' hg hg'
  simpa only [hOuter, hDj] using h

/-- Independent original blocks and split copies have the same actual centered fourth moments. -/
theorem integral_sum_centered_chain_eq_splitCopies {θ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ) (j : Fin (K + 1))
    (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k) (B : ℕ → Ω → Measure (Plane × Plane))
    (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hind : iIndepFun (fun k : Fin (K + 1) => B k) P)
    (w : ℕ → ℕ → Plane → ℝ) (hw : ∀ k, IsL2ApplicableMollifier (w k)) (ℓ : ℕ)
    {m r : ℕ} (g g' : Fin m → Fin r → Plane → ℝ)
    (hg : ∀ a b, MemLp (g a b) 2) (hg' : ∀ a b, MemLp (g' a b) 2) :
    (∫ ω, ∑ a, ((∑ b, ∫ p, g a b p.1 * g' a b p.2
      ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K) -
      ∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂chainProduct
        (Function.update (fun k => B k ω) j (heatBlock (τ j))) (fun k => w k ℓ) K) ^ 4 ∂P) =
    ∫ q : (Fin K → Ω) × Ω, ∑ a,
      ((∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂chainProduct
        (Function.update (outerCopyBlock K j B q.1) j (B j q.2)) (fun k => w k ℓ) K) -
      ∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂chainProduct
        (Function.update (outerCopyBlock K j B q.1) j (heatBlock (τ j))) (fun k => w k ℓ) K) ^ 4
      ∂(Measure.pi (fun _ : Fin K => P)).prod P := by
  classical
  let R := Measure.pi (fun _ : Fin (K + 1) => P)
  let C (k : ℕ) (ω : Fin (K + 1) → Ω) := coordinateCopyBlock K B ω k
  have hC (k) (hk : k ≤ K) : HasDeltaBoseMoments θ (τ k) R (C k) :=
    hasDeltaBoseMoments_coordinateCopyBlock P K τ B hB k hk
  have hindC : iIndepFun (fun k : Fin (K + 1) => C k) R :=
    iIndepFun_coordinateCopyBlock P K B (fun k hk => (hB k hk).1)
  have hData (a : Fin m) := integral_sum_centeredChainPairings_pow_four_eq_of_moments
    K j (Nat.le_of_lt_succ j.is_lt) τ hτ B C hB hC hind hindC w hw ℓ
      (g a) (g' a) (hg a) (hg' a)
  let V (ω : Fin (K + 1) → Ω) := ∑ a,
    (∑ b, ((∫ p, g a b p.1 * g' a b p.2 ∂chainProduct (fun k => C k ω) (fun k => w k ℓ) K) -
      ∫ p, g a b p.1 * g' a b p.2 ∂chainProduct
        (Function.update (fun k => C k ω) j (heatBlock (τ j))) (fun k => w k ℓ) K)) ^ 4
  have hVI : Integrable V R := integrable_finsetSum _ (fun a _ => (hData a).2.1)
  have hEq : (∫ ω, ∑ a, ((∑ b, ∫ p, g a b p.1 * g' a b p.2
      ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K) -
      ∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂chainProduct
        (Function.update (fun k => B k ω) j (heatBlock (τ j))) (fun k => w k ℓ) K) ^ 4 ∂P) =
      ∫ ω, V ω ∂R := by
    simp only [V, Finset.sum_sub_distrib] at hData ⊢
    rw [integral_finsetSum _ (fun a _ => (hData a).1),
      integral_finsetSum _ (fun a _ => (hData a).2.1)]
    exact Finset.sum_congr rfl (fun a _ => (hData a).2.2)
  have hφ := measurePreserving_insertCopyCoordinate P K j
  have hVm : AEStronglyMeasurable V
      (Measure.map (fun q : (Fin K → Ω) × Ω =>
        Fin.insertNth (α := fun _ : Fin (K + 1) => Ω) j q.2 q.1)
          ((Measure.pi (fun _ : Fin K => P)).prod P)) := by
    rw [hφ.map_eq]
    exact hVI.aestronglyMeasurable
  have hSplit := integral_map hφ.measurable.aemeasurable hVm
  rw [hφ.map_eq] at hSplit
  exact hEq.trans (by
    simpa only [V, C, coordinateCopyBlock_insertNth_eq_update_outer,
      Function.update_idem, Finset.sum_sub_distrib] using hSplit)

end Critical2DKPZ.SHF.Tsai

end
