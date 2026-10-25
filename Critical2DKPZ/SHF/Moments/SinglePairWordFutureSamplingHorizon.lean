/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordFutureHorizon
public import Critical2DKPZ.SHF.Moments.SinglePairWordFutureCutoff
public import Critical2DKPZ.SHF.Moments.EntranceUniform
public import Mathlib.Tactic
import Mathlib.Tactic

/-! # Phase-correct future and entrance limits on arbitrary finite horizons -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory Filter Polymer
open scoped CompactlySupported Topology

/-- The phase-correct future extension converges along all moving collision
points in the interior of any finite horizon. -/
theorem tendsto_pairTwoFutureSampleProfile_moving_horizon
    (ϑ T : ℝ) (L : ℕ → ℕ)
    (hL : Tendsto (fun N => (L N : ℝ) / N) atTop (𝓝 T))
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (xN : ℕ → Fin 2 → Site)
    (hx : ∀ᶠ N : ℕ in atTop, ∀ i : Fin 2, xN N i ∈ evenLattice)
    (a : Fin 2 → Plane)
    (ha : ∀ i : Fin 2, Tendsto (fun N => latticeRepresentative N (xN N i)) atTop (𝓝 (a i)))
    (pN : ℕ → ℝ × Plane) (p : ℝ × Plane) (hpN : Tendsto pN atTop (𝓝 p))
    (hp : 0 < p.1) (hpT : p.1 < T) :
    Tendsto (fun N => pairTwoFutureSampleProfile ϑ N (L N) φ (xN N) (pN N)) atTop
      (𝓝 (pairTwoContinuumFuture (ϑ - Real.eulerMascheroniConstant) (T - p.1) φ a p.2)) := by
  let rN : ℕ → ℕ := fun N => L N - Nat.floor ((N : ℝ) * (pN N).1)
  have hr := tendsto_remaining_floor L hL (fun N => (pN N).1) (continuous_fst.tendsto p |>.comp hpN) hp hpT
  have hz := tendsto_pairTwoFutureSampleSite rN (fun N => (pN N).2) p.2
    (continuous_snd.tendsto p |>.comp hpN)
  exact tendsto_pairTwoFutureTestedTail_moving ϑ (T - p.1) (sub_pos.mpr hpT) rN hr φ xN hx a ha
    (fun N => pairTwoFutureSampleSite N (rN N) (pN N).2) p.2 hz
    (Eventually.of_forall fun N => pairTwoFutureSampleSite_phase N (rN N) (pN N).2)

/-- Uniform future-profile approximation on compact interior collision sets,
with a moving microscopic horizon and moving incoming test locations. -/
theorem tendstoUniformlyOn_pairTwoFutureSampleProfile_horizon
    (ϑ T : ℝ) (L : ℕ → ℕ)
    (hL : Tendsto (fun N => (L N : ℝ) / N) atTop (𝓝 T))
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (xN : ℕ → Fin 2 → Site)
    (hx : ∀ᶠ N : ℕ in atTop, ∀ i : Fin 2, xN N i ∈ evenLattice)
    (a : Fin 2 → Plane)
    (ha : ∀ i : Fin 2, Tendsto (fun N => latticeRepresentative N (xN N i)) atTop (𝓝 (a i)))
    {K : Set (ℝ × Plane)} (hK : IsCompact K)
    (hKT : ∀ p ∈ K, 0 < p.1 ∧ p.1 < T) :
    TendstoUniformlyOn (fun N p => pairTwoFutureSampleProfile ϑ N (L N) φ (xN N) p)
      (fun p => pairTwoContinuumFuture (ϑ - Real.eulerMascheroniConstant) (T - p.1) φ a p.2)
      atTop K := by
  apply tendstoUniformlyOn_of_moving_tests hK
  · intro p hp
    have hc := continuousAt_pairTwoContinuumFuture (ϑ - Real.eulerMascheroniConstant)
      φ (T - p.1, a, p.2) (sub_pos.mpr (hKT p hp).2)
    have harg : ContinuousAt (fun p' : ℝ × Plane => (T - p'.1, a, p'.2)) p :=
      (continuousAt_const.sub continuousAt_fst).prodMk
        (continuousAt_const.prodMk continuousAt_snd)
    exact (ContinuousAt.comp'
      (f := fun p' : ℝ × Plane => (T - p'.1, a, p'.2))
      (g := fun q : ℝ × (Fin 2 → Plane) × Plane =>
        pairTwoContinuumFuture (ϑ - Real.eulerMascheroniConstant) q.1 φ q.2.1 q.2.2)
      hc harg).continuousWithinAt
  · intro p hp pN _hpNK hpN
    exact tendsto_pairTwoFutureSampleProfile_moving_horizon ϑ T L hL φ xN hx a ha
      pN p hpN (hKT p hp).1 (hKT p hp).2

/-- After an interior compact cutoff the moving future approximation converges
uniformly on the entire collision time-space plane. -/
theorem tendstoUniformly_pairTwoFutureSampleProfile_cutoff_horizon
    (ϑ T : ℝ) (L : ℕ → ℕ)
    (hL : Tendsto (fun N => (L N : ℝ) / N) atTop (𝓝 T))
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (xN : ℕ → Fin 2 → Site)
    (hx : ∀ᶠ N : ℕ in atTop, ∀ i : Fin 2, xN N i ∈ evenLattice)
    (a : Fin 2 → Plane)
    (ha : ∀ i : Fin 2, Tendsto (fun N => latticeRepresentative N (xN N i)) atTop (𝓝 (a i)))
    (η : C_c(ℝ × Plane, ℝ))
    (hη : ∀ p ∈ tsupport η, 0 < p.1 ∧ p.1 < T) :
    TendstoUniformly (fun N p => η p * pairTwoFutureSampleProfile ϑ N (L N) φ (xN N) p)
      (fun p => η p * pairTwoContinuumFuture (ϑ - Real.eulerMascheroniConstant) (T - p.1) φ a p.2)
      atTop := by
  have hu := tendstoUniformlyOn_pairTwoFutureSampleProfile_horizon ϑ T L hL φ xN hx a ha
    η.hasCompactSupport hη
  rw [← tendstoUniformlyOn_univ, Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let M : ℝ := ‖η.toBoundedContinuousFunction‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have he := Metric.tendstoUniformlyOn_iff.mp hu (ε / M) (div_pos hε hM)
  filter_upwards [he] with N hN
  intro p _hp
  by_cases hp : p ∈ tsupport η
  · have hnorm : |η p| ≤ M :=
      (η.toBoundedContinuousFunction.norm_coe_le_norm p).trans (by dsimp [M]; linarith)
    have hdiff := hN p hp
    rw [Real.dist_eq, ← mul_sub, abs_mul]
    calc
      |η p| * |pairTwoContinuumFuture (ϑ - Real.eulerMascheroniConstant) (T - p.1) φ a p.2 -
          pairTwoFutureSampleProfile ϑ N (L N) φ (xN N) p| ≤
          M * |pairTwoContinuumFuture (ϑ - Real.eulerMascheroniConstant) (T - p.1) φ a p.2 -
            pairTwoFutureSampleProfile ϑ N (L N) φ (xN N) p| :=
        mul_le_mul_of_nonneg_right hnorm (abs_nonneg _)
      _ < M * (ε / M) := mul_lt_mul_of_pos_left hdiff hM
      _ = ε := mul_div_cancel₀ ε hM.ne'
  · have hz : η p = 0 := image_eq_zero_of_notMem_tsupport hp
    simpa only [hz, zero_mul, dist_self] using hε

/-- The entrance local limit applies to the complete future profile with an interior compact collision cutoff and moving horizons and locations. -/
theorem tendsto_pairTwoFutureSampleProfile_collisionEntrance_cutoff_horizon
    (ϑ T : ℝ) (L : ℕ → ℕ)
    (hL : Tendsto (fun N => (L N : ℝ) / N) atTop (𝓝 T))
    {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (M₀ M₁ : ℕ → ℕ)
    (hM₀ : Tendsto (fun N : ℕ => (M₀ N : ℝ) / N) atTop (𝓝 s))
    (hM₁ : Tendsto (fun N : ℕ => (M₁ N : ℝ) / N) atTop (𝓝 t))
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (xN : ℕ → Fin 2 → Site)
    (hx : ∀ N, ∀ i : Fin 2, xN N i ∈ evenLattice)
    (a : Fin 2 → Plane)
    (ha : ∀ i : Fin 2, Tendsto (fun N => latticeRepresentative N (xN N i)) atTop (𝓝 (a i)))
    (η : C_c(ℝ × Plane, ℝ))
    (hη : ∀ p ∈ tsupport η, 0 < p.1 ∧ p.1 < T) :
    Tendsto (fun N => collisionEntrance N (M₀ N + 1) (M₁ N) (xN N 0) (xN N 1)
      (fun p => η p * pairTwoFutureSampleProfile ϑ N (L N) φ (xN N) p)) atTop
      (𝓝 (4 * (∫ u in s..t, heatKernelPairProfileIntegral u (a 0) (a 1)
        (fun p => η p * pairTwoContinuumFuture (ϑ - Real.eulerMascheroniConstant)
          (T - p.1) φ a p.2)))) := by
  let θ := ϑ - Real.eulerMascheroniConstant
  let G : ℝ × Plane → ℝ := fun p => pairTwoContinuumFuture θ (T - p.1) φ a p.2
  have hc : Continuous (fun p => η p * G p) :=
    continuous_pairTwoContinuumFuture_cutoff θ T φ a η (fun p hp => (hη p hp).2)
  have hcompact : HasCompactSupport (fun p => η p * G p) := η.hasCompactSupport.mul_right
  let F : C_c(ℝ × Plane, ℝ) := ⟨⟨fun p => η p * G p, hc⟩, hcompact⟩
  obtain ⟨R, hR⟩ := (η.hasCompactSupport.image continuous_snd).isBounded.exists_norm_le
  have hsupport (u : ℝ) (z : Plane) (hz : F (u, z) ≠ 0) : ‖z‖ ≤ R := by
    have hηz : η (u, z) ≠ 0 := fun hzero => hz (by change η (u, z) * G (u, z) = 0; rw [hzero, zero_mul])
    exact hR z ⟨(u, z), subset_closure (Function.mem_support.mpr hηz), rfl⟩
  have hu := tendstoUniformly_pairTwoFutureSampleProfile_cutoff_horizon ϑ T L hL φ xN
    (Eventually.of_forall hx) a ha η hη
  exact tendsto_collisionEntrance_spatial_test_away_zero_moving_window_of_uniform hs hst
    M₀ M₁ hM₀ hM₁ (fun N => xN N 0) (fun N => xN N 1)
    (fun N => hx N 0) (fun N => hx N 1) (a 0) (a 1) (ha 0) (ha 1)
    F R ‖F.toBoundedContinuousFunction‖ (norm_nonneg _) F.continuous
    (fun u z => F.toBoundedContinuousFunction.norm_coe_le_norm (u, z)) hsupport
    (fun N p => η p * pairTwoFutureSampleProfile ϑ N (L N) φ (xN N) p) hu

end Critical2DKPZ.SHF.Moments
