/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.UniversalChainLimits
public import Critical2DKPZ.SHF.Tsai.FiniteVectorConvergence

/-! # Joint connector limits for three-block expectations

Finite vectors of three-block tensor pairings have fourth-moment limits independent of
how the two connector indices tend to infinity, giving joint limits of bounded continuous
observables.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology CompactlySupported BoundedContinuousFunction

namespace Critical2DKPZ.SHF.Tsai

/-- Three blocks `B 0, B 1, B 2` joined by connectors `u ℓ, u ℓ'`. -/
def threeBlockPairing {Ω : Type*} (B : Fin 3 → Ω → Measure (Plane × Plane)) (u : ℕ → Plane → ℝ)
    {m r : ℕ} (g g' : Fin m → Fin r → C_c(Plane, ℝ)) (ℓ ℓ' : ℕ) (ω : Ω) : Fin m → ℝ :=
  fun i => ∑ k, ∫ p, g i k p.1 * g' i k p.2 ∂(smoothedProductMeasure
    (smoothedProductMeasure (B 0 ω) (u ℓ) (B 1 ω)) (u ℓ') (B 2 ω))

/-- Expectations of a bounded smooth test of three-block tensor pairings have a joint
limit as both connector indices tend to infinity. -/
theorem tendsto_integral_threeBlockPairing {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (τ : Fin 3 → ℝ) (hτ : ∀ k, 0 < τ k) (B : Fin 3 → Ω → Measure (Plane × Plane))
    (hB : ∀ k, HasDeltaBoseMoments θ (τ k) P (B k)) (hind : iIndepFun B P)
    (u : ℕ → Plane → ℝ) (hu : IsL2ApplicableMollifier u) {m r : ℕ} (g g' : Fin m → Fin r → C_c(Plane, ℝ))
    (H : (Fin m → ℝ) → ℝ) (hH : ContDiff ℝ 4 H) (CH : ℝ) (hCH : ∀ k ≤ 4, ∀ x, ‖iteratedFDeriv ℝ k H x‖ ≤ CH) :
    ∃ L : ℝ, Tendsto (fun q : ℕ × ℕ => ∫ ω, H (threeBlockPairing B u g g' q.1 q.2 ω) ∂P) atTop (𝓝 L) := by
  classical
  let Bn (k : ℕ) := B (Fin.ofNat 3 k)
  let τn (k : ℕ) := τ (Fin.ofNat 3 k)
  have hτn (k : ℕ) (_ : k ≤ 2) : 0 < τn k := hτ _
  have hBn (k : ℕ) (_ : k ≤ 2) : HasDeltaBoseMoments θ (τn k) P (Bn k) := hB _
  have hindn : iIndepFun (fun k : Fin (2 + 1) => Bn k) P := by
    simpa only [Bn, Fin.ofNat_eq_cast, Fin.cast_val_eq_self] using hind
  have hg (i : Fin m × Fin r) : MemLp (g i.1 i.2) 2 :=
    (g i.1 i.2).continuous.memLp_of_hasCompactSupport (g i.1 i.2).hasCompactSupport
  have hg' (i : Fin m × Fin r) : MemLp (g' i.1 i.2) 2 :=
    (g' i.1 i.2).continuous.memLp_of_hasCompactSupport (g' i.1 i.2).hasCompactSupport
  choose F hF hlimit using fun i : Fin m × Fin r =>
    exists_chainPairing_four_limit_universal 2 τn hτn Bn hBn hindn
      (fun _ => u) (fun _ => hu) (g i.1 i.2) (g' i.1 i.2) (hg i) (hg' i)
  let V (q : ℕ × ℕ) (ω : Ω) (i : Fin m × Fin r) := ∫ p, g i.1 i.2 p.1 * g' i.1 i.2 p.2
    ∂smoothedProductMeasure (smoothedProductMeasure (B 0 ω) (u q.1) (B 1 ω)) (u q.2) (B 2 ω)
  let J (x : (Fin m × Fin r) → ℝ) := H (fun a => ∑ b, x (a, b))
  have hJ : Continuous J := by
    apply hH.continuous.comp
    apply continuous_pi
    intro a
    exact continuous_finsetSum _ (fun b _ => continuous_apply (a, b))
  have hH0 (x) : ‖H x‖ ≤ CH := by
    simpa only [norm_iteratedFDeriv_zero] using hCH 0 (by omega) x
  let Hb : ((Fin m × Fin r) → ℝ) →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfBound ⟨J, hJ⟩ (2 * CH) (by
      intro x y
      exact (dist_le_norm_add_norm _ _).trans
        ((add_le_add (hH0 _) (hH0 _)).trans_eq (two_mul CH).symm))
  refine ⟨∫ ω, H (fun a => ∑ b, F (a, b) ω) ∂P, ?_⟩
  apply Filter.tendsto_iff_seq_tendsto.2
  intro q hq
  have hqprod : Tendsto q atTop (atTop ×ˢ atTop : Filter (ℕ × ℕ)) := by
    rwa [prod_atTop_atTop_eq]
  let v (k j : ℕ) : Plane → ℝ := if k = 0 then u (q j).1 else u (q j).2
  have hv (k : ℕ) : IsL2ApplicableMollifier (v k) := by
    by_cases hk : k = 0
    · have heq : v k = fun j => u (q j).1 := by funext j x; simp only [v, ite_eq_left hk]
      rw [heq]
      exact hu.comp_tendsto hqprod.fst
    · have heq : v k = fun j => u (q j).2 := by funext j x; simp only [v, ite_eq_right hk]
      rw [heq]
      exact hu.comp_tendsto hqprod.snd
  have hpair (i : Fin m × Fin r) (j : ℕ) (ω : Ω) :
      (∫ p, g i.1 i.2 p.1 * g' i.1 i.2 p.2
        ∂chainProduct (fun k => Bn k ω) (fun k => v k j) 2) = V (q j) ω i := by
    rfl
  have hmem (j : ℕ) (i : Fin m × Fin r) : MemLp (fun ω => V (q j) ω i) 4 P := by
    have h := memLp_chainPairing_four 2 τn hτn Bn hBn hindn v hv j _ _ (hg i) (hg' i)
    simpa only [hpair] using h
  have hprob (i : Fin m × Fin r) :
      TendstoInMeasure P (fun j ω => V (q j) ω i) atTop (F i) := by
    have hlim := hlimit i v hv
    have hI (j) : Integrable (fun ω => (V (q j) ω i - F i ω) ^ 4) P := by
      simpa only [hpair] using hlim.1 j
    have hlim' : Tendsto (fun j => ∫ ω, (V (q j) ω i - F i ω) ^ 4 ∂P) atTop (𝓝 0) := by
      simpa only [hpair] using hlim.2
    have hnorm := tendsto_eLpNorm_four_of_integral_pow_four P
      (fun j ω => V (q j) ω i - F i ω)
      (fun j => ((hmem j i).sub (hF i)).aestronglyMeasurable) hI hlim'
    exact tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (4 : ℝ≥0∞) ≠ 0) hnorm
  have hInt := tendsto_integral_boundedContinuous_of_coordinatewise_tendstoInMeasure P
    (fun j ω i => V (q j) ω i) (fun ω i => F i ω)
    (fun j i => (hmem j i).aestronglyMeasurable.aemeasurable) hprob Hb
  exact hInt

end Critical2DKPZ.SHF.Tsai

end
