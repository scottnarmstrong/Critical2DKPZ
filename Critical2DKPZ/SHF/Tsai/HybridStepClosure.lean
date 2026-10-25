/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.HybridRemainderLimits
public import Critical2DKPZ.SHF.Tsai.HybridEndpointComparison
public import Critical2DKPZ.SHF.Tsai.WholeIntervalComparison

/-! # Quantitative hybrid increments from centered-chain bounds

The endpoint and interior comparison theorems reduce each hybrid increment
to a centered fourth-moment limit. The limsup estimate bounds those limits
uniformly by the corresponding interval length.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology CompactlySupported ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

universe uΞ vΞ

/-- Uniform centered-chain fourth-moment bounds give the superlinear hybrid increment estimate. -/
theorem isDenseSHF_hybridValue_step_le_of_limsup_integral_chain_centered_le
    (θ B : ℝ) (D : Set ℝ) (hD : D ⊆ Set.Icc 0 B)
    {Ω : Type uΞ} {Ω' : Type vΞ} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane))
    (hZ : IsDenseSHF θ D P Z) (hZ' : IsDenseSHF θ D P' Z')
    {s t : ℝ} (hs : s ∈ D) (ht : t ∈ D) (hst : s < t)
    {m r : ℕ} (g g' : Fin m → Fin r → C_c(Plane, ℝ))
    (H : (Fin m → ℝ) → ℝ) (hH : ContDiff ℝ 4 H) (CH : ℝ)
    (hCH : ∀ k ≤ 4, ∀ x, ‖iteratedFDeriv ℝ k H x‖ ≤ CH)
    {p : ℝ≥0∞} (_hp : 6 < p) (_hp' : p ≠ ⊤)
    (hLsup : ∃ C : ℝ, ∀ (K j : ℕ),
      (K = 0 ∧ j = 0 ∨ K = 1 ∧ j ≤ 1 ∨ K = 2 ∧ j = 1) →
      ∀ τ : ℕ → ℝ, (∀ k ≤ K, 0 < τ k) →
      ∑ k ∈ Finset.range (K + 1), τ k ≤ B →
      ∀ {Ξ : Type (max vΞ uΞ)} [MeasurableSpace Ξ] (Q : Measure Ξ) [IsProbabilityMeasure Q]
        (A : ℕ → Ξ → Measure (Plane × Plane)),
        (∀ k ≤ K, HasDeltaBoseMoments θ (τ k) Q (A k)) →
        iIndepFun (fun k : Fin (K + 1) => A k) Q →
        ∀ u : ℕ → ℕ → Plane → ℝ, (∀ k, IsL2ApplicableMollifier (u k)) →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ ℓ in atTop,
          ∫ ω, ∑ a, ((∑ b, ∫ q, g a b q.1 * g' a b q.2
              ∂chainProduct (fun k => A k ω) (fun k => u k ℓ) K) -
            ∑ b, ∫ q, g a b q.1 * g' a b q.2
              ∂chainProduct (Function.update (fun k => A k ω) j (heatBlock (τ j)))
                (fun k => u k ℓ) K) ^ 4 ∂Q ≤
            C * τ j ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) + ε) :
    ∃ C : ℝ, ∀ a ∈ D, ∀ b ∈ D, s ≤ a → a < b → b ≤ t → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ ℓ in atTop,
        |hybridValue P P' Z Z' s t g g' H a ℓ -
          hybridValue P P' Z Z' s t g g' H b ℓ| ≤
            C * (b - a) ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) + ε := by
  obtain ⟨C₀, hLsup⟩ := hLsup
  have hCH0 : 0 ≤ CH := (norm_nonneg _).trans (hCH 0 (by omega) 0)
  have hCweight : 0 ≤ CH / 12 := div_nonneg hCH0 (by norm_num)
  have hstepLimitBound {K j : ℕ}
      (hshape : K = 0 ∧ j = 0 ∨ K = 1 ∧ j ≤ 1 ∨ K = 2 ∧ j = 1)
      (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k)
      (hsum : ∑ k ∈ Finset.range (K + 1), τ k ≤ B)
      {Ξ : Type (max vΞ uΞ)} [MeasurableSpace Ξ] (Q : Measure Ξ) [IsProbabilityMeasure Q]
      (A : ℕ → Ξ → Measure (Plane × Plane))
      (hA : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) Q (A k))
      (hind : iIndepFun (fun k : Fin (K + 1) => A k) Q)
      (u : ℕ → ℕ → Plane → ℝ) (hu : ∀ k, IsL2ApplicableMollifier (u k))
      (M : ℝ)
      (hM : Tendsto (fun ℓ => ∫ ω, ∑ a, ((∑ b, ∫ q, g a b q.1 * g' a b q.2
          ∂chainProduct (fun k => A k ω) (fun k => u k ℓ) K) -
        ∑ b, ∫ q, g a b q.1 * g' a b q.2
          ∂chainProduct (Function.update (fun k => A k ω) j (heatBlock (τ j)))
            (fun k => u k ℓ) K) ^ 4 ∂Q) atTop (𝓝 M))
      (hM0 : 0 ≤ M) : M ≤ C₀ * τ j ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) := by
    apply le_of_forall_pos_le_add
    intro ε hε
    exact le_of_tendsto hM (hLsup K j hshape τ hτ hsum Q A hA hind u hu ε hε)
  have hsB : s ∈ Set.Icc 0 B := hD hs
  have htB : t ∈ Set.Icc 0 B := hD ht
  have hSeq0 (a b : ℝ) (La Lb : ℝ)
      (hLa : Tendsto (fun ℓ => hybridValue P P' Z Z' s t g g' H a ℓ) atTop (𝓝 La))
      (hLb : Tendsto (fun ℓ => hybridValue P P' Z Z' s t g g' H b ℓ) atTop (𝓝 Lb))
      (hbound : |La - Lb| ≤ (CH / 12) * C₀ * (b - a) ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)))
      (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ ℓ in atTop,
        |hybridValue P P' Z Z' s t g g' H a ℓ -
          hybridValue P P' Z Z' s t g g' H b ℓ| ≤
            (CH / 12 * C₀) * (b - a) ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) + ε := by
    have hdiff := (hLa.sub hLb).abs
    have hstrict : |La - Lb| <
        (CH / 12 * C₀) * (b - a) ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) + ε := by
      exact lt_of_le_of_lt (by simpa only [mul_assoc] using hbound)
        (lt_add_of_pos_right _ hε)
    exact hdiff.eventually_le_const hstrict
  have hconstantEndpoints (hbound :
      |hybridValue P P' Z Z' s t g g' H s 0 -
        hybridValue P P' Z Z' s t g g' H t 0| ≤
          (CH / 12 * C₀) * (t - s) ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)))
      (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ ℓ in atTop,
        |hybridValue P P' Z Z' s t g g' H s ℓ -
          hybridValue P P' Z Z' s t g g' H t ℓ| ≤
            (CH / 12 * C₀) * (t - s) ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) + ε := by
    filter_upwards with ℓ
    rw [hybridValue_left, hybridValue_right P P' Z Z' hst]
    have hb := hbound
    rw [hybridValue_left, hybridValue_right P P' Z Z' hst] at hb
    exact hb.trans (le_add_of_nonneg_right hε.le)
  refine ⟨CH / 12 * C₀, ?_⟩
  intro a ha b hb hsa hab hbt ε hε
  by_cases haeq : a = s
  · subst a
    by_cases hbeq : b = t
    · subst b
      have hτ : 0 < t - s := sub_pos.mpr hst
      have hBlock : HasDeltaBoseMoments θ (t - s) P (Z s t) := hZ.hasDeltaBoseMoments hs ht hst
      obtain ⟨_hI₁, _hI₂, _hI₃, hswap⟩ := integrable_and_abs_integral_block_swap_le
        P P' (Z s t) (Z' s t) hBlock (hZ'.hasDeltaBoseMoments hs ht hst) hτ
        (fun i k => g i k) (fun i k => g' i k)
        (fun i k => (g i k).continuous.memLp_of_hasCompactSupport (g i k).hasCompactSupport)
        (fun i k => (g' i k).continuous.memLp_of_hasCompactSupport (g' i k).hasCompactSupport)
        H hH CH hCH
      let A (k : ℕ) (ω : Ω) := Z s t ω
      let τ (k : ℕ) := t - s
      have hA (k : ℕ) (hk : k ≤ 0) : HasDeltaBoseMoments θ (τ k) P (A k) := by
        simpa [A, τ] using hBlock
      have hind : iIndepFun (fun k : Fin (0 + 1) => A k) P := by
        change iIndepFun (fun _ : Fin 1 => Z s t) P
        exact iIndepFun.of_subsingleton
      let M : ℝ := ∫ ω, ∑ i, ((∑ k, ∫ q, g i k q.1 * g' i k q.2
          ∂Z s t ω) -
            ∑ k, ∫ q, g i k q.1 * g' i k q.2 ∂heatBlock (t - s)) ^ 4 ∂P
      have hM : Tendsto (fun ℓ => ∫ ω, ∑ i, ((∑ k, ∫ q, g i k q.1 * g' i k q.2
          ∂chainProduct (fun k => A k ω) (fun k => heatMollifier ℓ) 0) -
        ∑ k, ∫ q, g i k q.1 * g' i k q.2
          ∂chainProduct (Function.update (fun k => A k ω) 0 (heatBlock (τ 0)))
            (fun k => heatMollifier ℓ) 0) ^ 4 ∂P) atTop (𝓝 M) := by
        simp [M, chainProduct, A, τ]
      let A' (k : ℕ) (ω : Ω' × Ω) := Z s t ω.2
      have hA' (k : ℕ) (hk : k ≤ 0) :
          HasDeltaBoseMoments θ (τ k) (P'.prod P) (A' k) := by
        simpa [A', τ] using hBlock.comp_measurePreserving
          (measurePreserving_snd : MeasurePreserving Prod.snd (P'.prod P) P)
      have hind' : iIndepFun (fun k : Fin (0 + 1) => A' k) (P'.prod P) := by
        change iIndepFun (fun _ : Fin 1 => fun ω : Ω' × Ω => Z s t ω.2) (P'.prod P)
        exact iIndepFun.of_subsingleton
      have heq (ℓ : ℕ) :
          (∫ ω : Ω' × Ω, ∑ i, ((∑ k, ∫ q, g i k q.1 * g' i k q.2
            ∂chainProduct (fun k => A' k ω) (fun k => heatMollifier ℓ) 0) -
          ∑ k, ∫ q, g i k q.1 * g' i k q.2
            ∂chainProduct (Function.update (fun k => A' k ω) 0 (heatBlock (τ 0)))
              (fun k => heatMollifier ℓ) 0) ^ 4 ∂(P'.prod P)) =
          ∫ ω : Ω, ∑ i, ((∑ k, ∫ q, g i k q.1 * g' i k q.2
            ∂chainProduct (fun k => A k ω) (fun k => heatMollifier ℓ) 0) -
          ∑ k, ∫ q, g i k q.1 * g' i k q.2
            ∂chainProduct (Function.update (fun k => A k ω) 0 (heatBlock (τ 0)))
              (fun k => heatMollifier ℓ) 0) ^ 4 ∂P := by
        simpa [A', A, τ, chainProduct, measureReal_def, measure_univ,
          ENNReal.toReal_one, one_smul] using
          (integral_fun_snd (μ := P') (ν := P) (fun ω : Ω => ∑ i,
            ((∑ k, ∫ q, g i k q.1 * g' i k q.2 ∂Z s t ω) -
              ∑ k, ∫ q, g i k q.1 * g' i k q.2 ∂heatBlock (t - s)) ^ 4))
      have hM' : Tendsto (fun ℓ => ∫ ω : Ω' × Ω, ∑ i, ((∑ k, ∫ q, g i k q.1 * g' i k q.2
          ∂chainProduct (fun k => A' k ω) (fun k => heatMollifier ℓ) 0) -
        ∑ k, ∫ q, g i k q.1 * g' i k q.2
          ∂chainProduct (Function.update (fun k => A' k ω) 0 (heatBlock (τ 0)))
            (fun k => heatMollifier ℓ) 0) ^ 4 ∂(P'.prod P)) atTop (𝓝 M) := by
        exact (tendsto_congr' (Eventually.of_forall heq)).2 hM
      have hM0 : 0 ≤ M := by
        unfold M
        exact integral_nonneg (fun ω => Finset.sum_nonneg
          (fun i _ => Even.pow_nonneg (by decide) _))
      have hMbound := hstepLimitBound (K := 0) (j := 0) (Or.inl ⟨rfl, rfl⟩) τ
        (fun k hk => by simpa [τ] using hτ) (by simp [τ]; linarith [hsB.1, htB.2])
        (P'.prod P) A' hA' hind' (fun _ => heatMollifier)
        (fun _ => isL2ApplicableMollifier_heatMollifier)
        M hM' hM0
      have hpowpos : 0 < (t - s) ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) :=
        Real.rpow_pos_of_pos hτ _
      have hC₀ : 0 ≤ C₀ := by
        by_contra hn
        have hneg : C₀ * (t - s) ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) < 0 :=
          mul_neg_of_neg_of_pos (lt_of_not_ge hn) hpowpos
        exact (not_lt_of_ge (le_trans hM0 hMbound)) hneg
      have hbound :
          |hybridValue P P' Z Z' s t g g' H s 0 - hybridValue P P' Z Z' s t g g' H t 0| ≤
            (CH / 12 * C₀) * (t - s) ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) := by
        calc
          _ ≤ (CH / 12) * M := by
            simpa [hybridValue, ne_of_gt hst, M] using hswap
          _ ≤ _ := by
            exact mul_le_mul_of_nonneg_left hMbound hCweight
          _ = _ := by ring
      exact hconstantEndpoints hbound ε hε
    · have hsb : s < b := hab
      have hbst : b < t := lt_of_le_of_ne hbt hbeq
      obtain ⟨Lb, M, hM0, hHybrid, _hI, hMlim, hcomp⟩ :=
        exists_hybrid_leftEndpoint_limit_comparison D P P' Z Z' hZ hZ'
          hs hb ht hsb hbst g g' H hH CH hCH
      let A (k : ℕ) (ω : Ω' × Ω) := if k = 0 then Z s b ω.2 else Z b t ω.2
      let τ (k : ℕ) := if k = 0 then b - s else t - b
      have hA (k : ℕ) (hk : k ≤ 1) : HasDeltaBoseMoments θ (τ k) (P'.prod P) (A k) := by
        interval_cases k
        · exact (hZ.hasDeltaBoseMoments hs hb hsb).comp_measurePreserving measurePreserving_snd
        · exact (hZ.hasDeltaBoseMoments hb ht hbst).comp_measurePreserving measurePreserving_snd
      have hind3 := hZ.iIndepFun_hybridSwap_leftEndpoint P P' Z Z' hZ' hs hb ht
        hsb hbst
      have heq : (fun k : Fin 2 => A k) =
          (fun k : Fin 2 => (![fun ω : Ω' × Ω => Z s b ω.2, fun ω => Z b t ω.2,
            fun ω => Z' s b ω.1] : Fin 3 → Ω' × Ω → Measure (Plane × Plane)) k.castSucc) := by
        funext k ω
        fin_cases k <;> rfl
      have hind : iIndepFun (fun k : Fin 2 => A k) (P'.prod P) := by
        rw [heq]
        exact hind3.precomp (Fin.castSucc_injective 2)
      have hMbound := hstepLimitBound (K := 1) (j := 0)
        (Or.inr (Or.inl ⟨rfl, by omega⟩)) τ
        (by intro k hk; interval_cases k <;> dsimp [τ] <;> positivity)
        (by simp [Finset.sum_range_succ, τ]; linarith [hsB.1, htB.2])
        (P'.prod P) A hA hind (fun _ => heatMollifier)
        (fun _ => isL2ApplicableMollifier_heatMollifier) M
        (by simpa [A, τ, chainProduct] using hMlim) hM0
      have hpowpos : 0 < (b - s) ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) :=
        Real.rpow_pos_of_pos (sub_pos.mpr hsb) _
      have hC₀ : 0 ≤ C₀ := by
        by_contra hn
        have hneg : C₀ * (b - s) ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) < 0 :=
          mul_neg_of_neg_of_pos (lt_of_not_ge hn) hpowpos
        exact (not_lt_of_ge (le_trans hM0 hMbound)) hneg
      have hbound : |hybridValue P P' Z Z' s t g g' H s 0 - Lb| ≤
          (CH / 12 * C₀) * (b - s) ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) := by
        calc
          _ ≤ CH / 12 * M := hcomp
          _ ≤ CH / 12 * (C₀ * (b - s) ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal))) :=
            mul_le_mul_of_nonneg_left hMbound hCweight
          _ = _ := by ring
      have hseq := ((tendsto_const_nhds : Tendsto
        (fun _ : ℕ => hybridValue P P' Z Z' s t g g' H s 0) atTop
        (𝓝 (hybridValue P P' Z Z' s t g g' H s 0))).sub hHybrid).abs
      have hstrict : |hybridValue P P' Z Z' s t g g' H s 0 - Lb| <
          (CH / 12 * C₀) * (b - s) ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) + ε :=
        lt_of_le_of_lt hbound (lt_add_of_pos_right _ hε)
      have hev := hseq.eventually_le_const hstrict
      filter_upwards [hev] with ℓ hℓ
      simpa only [hybridValue_left] using hℓ
  · have hslt : s < a := lt_of_le_of_ne hsa (by intro h; exact haeq h.symm)
    by_cases hbeq : b = t
    · subst b
      have hat : a < t := hab
      obtain ⟨La, M, hM0, hHybrid, _hI, hMlim, hcomp⟩ :=
        exists_hybrid_rightEndpoint_limit_comparison D P P' Z Z' hZ hZ'
          hs ha ht hslt hat g g' H hH CH hCH
      let A (k : ℕ) (ω : Ω' × Ω) := if k = 0 then Z' s a ω.1 else Z a t ω.2
      let τ (k : ℕ) := if k = 0 then a - s else t - a
      have hA (k : ℕ) (hk : k ≤ 1) : HasDeltaBoseMoments θ (τ k) (P'.prod P) (A k) := by
        interval_cases k
        · exact (hZ'.hasDeltaBoseMoments hs ha hslt).comp_measurePreserving measurePreserving_fst
        · exact (hZ.hasDeltaBoseMoments ha ht hat).comp_measurePreserving measurePreserving_snd
      have hind3 := hZ.iIndepFun_hybridSwap_rightEndpoint P P' Z Z' hZ' hs ha ht hslt hat
      have heq : (fun k : Fin 2 => A k) =
          (fun k : Fin 2 => (![fun ω : Ω' × Ω => Z' s a ω.1, fun ω => Z a t ω.2,
            fun ω => Z' a t ω.1] : Fin 3 → Ω' × Ω → Measure (Plane × Plane)) k.castSucc) := by
        funext k ω
        fin_cases k <;> rfl
      have hind : iIndepFun (fun k : Fin 2 => A k) (P'.prod P) := by
        rw [heq]
        exact hind3.precomp (Fin.castSucc_injective 2)
      have hMbound := hstepLimitBound (K := 1) (j := 1)
        (Or.inr (Or.inl ⟨rfl, by omega⟩)) τ
        (by intro k hk; interval_cases k <;> dsimp [τ] <;> positivity)
        (by simp [Finset.sum_range_succ, τ]; linarith [hsB.1, htB.2])
        (P'.prod P) A hA hind (fun _ => heatMollifier)
        (fun _ => isL2ApplicableMollifier_heatMollifier) M
        (by simpa [A, τ, chainProduct] using hMlim) hM0
      have hpowpos : 0 < (t - a) ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) :=
        Real.rpow_pos_of_pos (sub_pos.mpr hat) _
      have hC₀ : 0 ≤ C₀ := by
        by_contra hn
        have hneg : C₀ * (t - a) ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) < 0 :=
          mul_neg_of_neg_of_pos (lt_of_not_ge hn) hpowpos
        exact (not_lt_of_ge (le_trans hM0 hMbound)) hneg
      have hbound : |La - hybridValue P P' Z Z' s t g g' H t 0| ≤
          (CH / 12 * C₀) * (t - a) ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) := by
        calc
          _ ≤ CH / 12 * M := hcomp
          _ ≤ CH / 12 * (C₀ * (t - a) ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal))) :=
            mul_le_mul_of_nonneg_left hMbound hCweight
          _ = _ := by ring
      have hseq := (hHybrid.sub (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => hybridValue P P' Z Z' s t g g' H t 0) atTop
        (𝓝 (hybridValue P P' Z Z' s t g g' H t 0)))).abs
      have hstrict : |La - hybridValue P P' Z Z' s t g g' H t 0| <
          (CH / 12 * C₀) * (t - a) ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) + ε :=
        lt_of_le_of_lt hbound (lt_add_of_pos_right _ hε)
      have hev := hseq.eventually_le_const hstrict
      filter_upwards [hev] with ℓ hℓ
      simpa only [hybridValue_right P P' Z Z' (by linarith : s < t)] using hℓ
    · have hbt : b < t := lt_of_le_of_ne hbt hbeq
      have hsa : s < a := hslt
      obtain ⟨La, Lb, M, hM0, hLa, hLb, _hI, hMlim, hcomp⟩ :=
        exists_hybrid_adjacent_limit_comparison D P P' Z Z' hZ hZ'
          hs ha hb ht hsa hab hbt g g' H hH CH hCH
      let A (k : ℕ) (ω : Ω' × Ω) := if k = 0 then Z' s a ω.1 else
        if k = 1 then Z a b ω.2 else Z b t ω.2
      let τ (k : ℕ) := if k = 0 then a - s else if k = 1 then b - a else t - b
      have hA (k : ℕ) (hk : k ≤ 2) : HasDeltaBoseMoments θ (τ k) (P'.prod P) (A k) := by
        interval_cases k
        · exact (hZ'.hasDeltaBoseMoments hs ha hsa).comp_measurePreserving measurePreserving_fst
        · exact (hZ.hasDeltaBoseMoments ha hb hab).comp_measurePreserving measurePreserving_snd
        · exact (hZ.hasDeltaBoseMoments hb ht hbt).comp_measurePreserving measurePreserving_snd
      have hind4 := hZ.iIndepFun_hybridSwap P P' Z Z' hZ' hs ha hb ht hsa hab hbt
      have heq : (fun k : Fin 3 => A k) =
          (fun k : Fin 3 => (![fun ω : Ω' × Ω => Z' s a ω.1, fun ω => Z a b ω.2,
            fun ω => Z b t ω.2, fun ω => Z' a b ω.1] : Fin 4 → Ω' × Ω → Measure (Plane × Plane)) k.castSucc) := by
        funext k ω
        fin_cases k <;> rfl
      have hind : iIndepFun (fun k : Fin 3 => A k) (P'.prod P) := by
        rw [heq]
        exact hind4.precomp (Fin.castSucc_injective 3)
      have hMbound := hstepLimitBound (K := 2) (j := 1)
        (Or.inr (Or.inr ⟨rfl, rfl⟩)) τ
        (by intro k hk; interval_cases k <;> dsimp [τ] <;> positivity)
        (by simp [Finset.sum_range_succ, τ]; linarith [hsB.1, htB.2])
        (P'.prod P) A hA hind (fun _ => heatMollifier)
        (fun _ => isL2ApplicableMollifier_heatMollifier) M
        (by simpa [hybridCenteredFourth, threeBlockPairing, A, τ, chainProduct] using hMlim) hM0
      have hpowpos : 0 < (b - a) ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) :=
        Real.rpow_pos_of_pos (sub_pos.mpr hab) _
      have hC₀ : 0 ≤ C₀ := by
        by_contra hn
        have hneg : C₀ * (b - a) ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) < 0 :=
          mul_neg_of_neg_of_pos (lt_of_not_ge hn) hpowpos
        exact (not_lt_of_ge (le_trans hM0 hMbound)) hneg
      have hbound : |La - Lb| ≤
          (CH / 12 * C₀) * (b - a) ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) := by
        calc
          _ ≤ CH / 12 * M := hcomp
          _ ≤ CH / 12 * (C₀ * (b - a) ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal))) :=
            mul_le_mul_of_nonneg_left hMbound hCweight
          _ = _ := by ring
      exact hSeq0 a b La Lb hLa hLb hbound ε hε

end Critical2DKPZ.SHF.Tsai

end
