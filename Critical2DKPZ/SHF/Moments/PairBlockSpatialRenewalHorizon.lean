/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.PairBlockSpatialRenewalLimit
import Critical2DKPZ.SHF.Moments.KernelDictionary
import Critical2DKPZ.PolymerCalculus.ClockTuningAlong
import Critical2DKPZ.SHF.DeltaBose.BlockTransport
public import Critical2DKPZ.SHF.Moments.EntranceScaling
public import Critical2DKPZ.Analysis.Lattice.Sampling
import Mathlib.Tactic

/-! # Spatial renewal local limits on arbitrary bounded time horizons -/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Moments

private theorem horizon_scalarDensity_continuousAt_pos (θ u : ℝ) (hu : 0 < u) :
    ContinuousAt (fun p : ℝ × ℝ => DeltaBose.scalarDensity p.1 p.2) (θ, u) := by
  have hposOpen : IsOpen {p : ℝ × ℝ | 0 < p.2} :=
    isOpen_lt continuous_const continuous_snd
  have hjoint := DeltaBose.continuousOn_scalarDensity
  exact hjoint.continuousAt (hposOpen.mem_nhds hu)

private theorem horizon_tendsto_heatKernel_time_space (u : ℝ) (hu : 0 < u) (y : Plane)
    (tN : ℕ → ℝ) (htN : Tendsto tN atTop (𝓝 u))
    (yN : ℕ → Plane) (hyN : Tendsto yN atTop (𝓝 y)) :
    Tendsto (fun N : ℕ => heatKernel (tN N) (yN N)) atTop
      (𝓝 (heatKernel u y)) := by
  have hc : ContinuousAt (fun p : ℝ × Plane => heatKernel p.1 p.2) (u, y) :=
    DeltaBose.continuousOn_heatKernel.continuousAt
      ((isOpen_lt continuous_const continuous_fst).mem_nhds hu)
  exact hc.tendsto.comp (htN.prodMk_nhds hyN)

/-- The moving spatial renewal local limit along arbitrary diverging lattice scales. -/
private theorem spatialRenewal_parameter_unit_error
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (θ : ℕ → ℝ) (ϑ u : ℝ) (hθ : Tendsto θ atTop (𝓝 ϑ)) (hu : 0 < u) (hu1 : u < 1)
    (rN : ℕ → ℕ) (hr : Tendsto (fun N : ℕ => (rN N : ℝ) / M N) atTop (𝓝 u))
    (zN : ℕ → Site) (y : Plane)
    (hz : Tendsto (fun N : ℕ => latticeRepresentative (M N) (zN N)) atTop (𝓝 y))
    (hphase : ∀ᶠ N : ℕ in atTop, Even ((rN N : ℤ) + zN N 0 + zN N 1)) :
Tendsto (fun N : ℕ =>
      ((M N : ℝ) / 4) * ((M N) / Real.log (M N)) *
        Collision.spatialRenewal (criticalSigmaSq (θ N) (M N)) (rN N) (zN N) -
      DeltaBose.scalarDensity (θ N - Real.eulerMascheroniConstant)
        ((rN N : ℝ) / M N) *
      heatKernel ((rN N : ℝ) / (2 * M N))
        (latticeRepresentative (M N) (zN N))) atTop (𝓝 0) := by
  let A : ℝ := |ϑ| + 1
  let δ : ℝ := u / 2
  let R : ℝ := ‖y‖ + 1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by dsimp [δ]; linarith
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have htimeEvent : ∀ᶠ N : ℕ in atTop,
      u / 2 < (rN N : ℝ) / M N ∧ (rN N : ℝ) / M N < 1 := by
    filter_upwards [hr.eventually (Ioo_mem_nhds (a := u / 2) (b := 1)
      (by linarith) hu1)] with N hN
    exact hN
  have hnormTendsto : Tendsto
      (fun N : ℕ => ‖latticeRepresentative (M N) (zN N)‖) atTop (𝓝 ‖y‖) :=
    continuous_norm.continuousAt.tendsto.comp hz
  have hspaceEvent : ∀ᶠ N : ℕ in atTop,
      ‖latticeRepresentative (M N) (zN N)‖ ≤ R := by
    filter_upwards [hnormTendsto.eventually
        (Iio_mem_nhds (by change ‖y‖ < ‖y‖ + 1; linarith))] with N hN
    exact hN.le
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hRenewalSpatialLimitInput := spatialRenewal_localLimit A δ R (by dsimp [δ]; positivity) hδ1
    (ε / 2) (by positivity)
  filter_upwards [hM.eventually hRenewalSpatialLimitInput, htimeEvent, hspaceEvent,
      hphase, hθ.eventually (Ioo_mem_nhds (a := -A) (b := A) (by dsimp [A]; linarith [neg_abs_le ϑ]) (by dsimp [A]; linarith [le_abs_self ϑ])), hM.eventually (eventually_gt_atTop 0)] with N hRenewalSpatialLimitInputN htime hspace hphaseN hθN hN
  have hNreal : (0 : ℝ) < M N := by exact_mod_cast hN
  have hratioLower : δ * (M N : ℝ) ≤ (rN N : ℝ) := by
    have hstrict := (lt_div_iff₀ hNreal).mp (by simpa [δ] using htime.1)
    exact hstrict.le
  have hnLower : δ * M N ≤ rN N := by exact_mod_cast hratioLower
  have hnUpper : rN N ≤ M N := by
    have hstrict := (div_lt_one hNreal).mp htime.2
    exact_mod_cast hstrict.le
  have hθbox : θ N ∈ Set.Icc (-A) A := ⟨hθN.1.le, hθN.2.le⟩
  have hrepSq := norm_latticeRepresentative_sq (M N) (zN N)
  have hrepSqBound : ‖latticeRepresentative (M N) (zN N)‖ ^ 2 ≤ R ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hR).2 hspace
  have hsiteSqBound : ‖siteToPlane (zN N)‖ ^ 2 ≤
      ((M N : ℝ) / 2) * R ^ 2 := by
    rw [hrepSq] at hrepSqBound
    have hmul := mul_le_mul_of_nonneg_left hrepSqBound (by positivity)
    have hNr : (M N : ℝ) ≠ 0 := hNreal.ne'
    field_simp [hNr] at hmul
    nlinarith
  have hzbound : ‖siteToPlane (zN N)‖ ≤ R * Real.sqrt (M N) := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hR (Real.sqrt_nonneg _))).1
    have hsqrtSq : (Real.sqrt (M N : ℝ)) ^ 2 = (M N : ℝ) := Real.sq_sqrt hNreal.le
    nlinarith [hsiteSqBound, sq_nonneg R]
  have hbound := hRenewalSpatialLimitInputN (θ N) hθbox (rN N) hnLower hnUpper (zN N) hphaseN hzbound
  have hbound' : |((M N : ℝ) / 4) * ((M N) / Real.log (M N)) *
        Collision.spatialRenewal (criticalSigmaSq (θ N) (M N)) (rN N) (zN N) -
      DeltaBose.scalarDensity (θ N - Real.eulerMascheroniConstant)
        ((rN N : ℝ) / M N) *
      heatKernel ((rN N : ℝ) / (2 * M N))
        (latticeRepresentative (M N) (zN N))| ≤ ε / 2 := by
    simpa [δ, latticeRepresentative] using hbound
  have hhalf : ε / 2 < ε := by linarith
  have hdist : dist
      ((((M N : ℝ) / 4) * ((M N) / Real.log (M N)) *
        Collision.spatialRenewal (criticalSigmaSq (θ N) (M N)) (rN N) (zN N) -
      DeltaBose.scalarDensity (θ N - Real.eulerMascheroniConstant)
        ((rN N : ℝ) / M N) *
      heatKernel ((rN N : ℝ) / (2 * M N))
        (latticeRepresentative (M N) (zN N)))) 0 ≤ ε / 2 := by
    simpa only [Real.dist_eq, sub_zero] using hbound'
  exact lt_of_le_of_lt hdist hhalf

/-- The spatial renewal local limit with moving coupling along diverging lattice scales,
for a limiting time strictly between zero and one. -/
theorem tendsto_scaled_spatialRenewal_parameter_moving_unit
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (θ : ℕ → ℝ) (ϑ u : ℝ) (hθ : Tendsto θ atTop (𝓝 ϑ)) (hu : 0 < u) (hu1 : u < 1)
    (rN : ℕ → ℕ) (hr : Tendsto (fun N : ℕ => (rN N : ℝ) / M N) atTop (𝓝 u))
    (zN : ℕ → Site) (y : Plane)
    (hz : Tendsto (fun N : ℕ => latticeRepresentative (M N) (zN N)) atTop (𝓝 y))
    (hphase : ∀ᶠ N : ℕ in atTop, Even ((rN N : ℤ) + zN N 0 + zN N 1)) :
    Tendsto (fun N : ℕ => ((M N : ℝ) / 4) * ((M N) / Real.log (M N)) *
        Collision.spatialRenewal (criticalSigmaSq (θ N) (M N)) (rN N) (zN N)) atTop
      (𝓝 (DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) u *
        heatKernel (u / 2) y)) := by
  have herr := spatialRenewal_parameter_unit_error M hM θ ϑ u hθ hu hu1 rN hr zN y hz hphase
  have hratioHalf : Tendsto
      (fun N : ℕ => (rN N : ℝ) / (2 * M N)) atTop (𝓝 (u / 2)) := by
    have h := hr.div_const 2
    have heq : (fun N : ℕ => (rN N : ℝ) / (2 * M N)) =ᶠ[atTop]
        fun N : ℕ => ((rN N : ℝ) / M N) / 2 := by
      filter_upwards [hM.eventually (eventually_gt_atTop 0)] with N hN
      have hNreal : (0 : ℝ) < M N := by exact_mod_cast hN
      field_simp [hNreal.ne']
    exact h.congr' heq.symm
  have hscalar : Tendsto
      (fun N : ℕ => DeltaBose.scalarDensity (θ N - Real.eulerMascheroniConstant)
        ((rN N : ℝ) / M N)) atTop
        (𝓝 (DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) u)) := by
    change Tendsto ((fun p : ℝ × ℝ => DeltaBose.scalarDensity p.1 p.2) ∘
      (fun N => (θ N - Real.eulerMascheroniConstant, (rN N : ℝ) / M N))) atTop _
    exact (horizon_scalarDensity_continuousAt_pos (ϑ - Real.eulerMascheroniConstant) u hu).tendsto.comp
      ((hθ.sub_const Real.eulerMascheroniConstant).prodMk_nhds hr)
  have hheat : Tendsto
      (fun N : ℕ => heatKernel ((rN N : ℝ) / (2 * M N))
        (latticeRepresentative (M N) (zN N))) atTop (𝓝 (heatKernel (u / 2) y)) := by
    exact horizon_tendsto_heatKernel_time_space (u / 2) (half_pos hu) y
      (fun N => (rN N : ℝ) / (2 * M N)) hratioHalf
      (fun N => latticeRepresentative (M N) (zN N)) hz
  have hprod := hscalar.mul hheat
  have hsum := herr.add hprod
  simpa only [sub_add_cancel, zero_add] using hsum


/-- Exact retuning preserves the coupling, rather than just its leading asymptotic. -/
theorem criticalSigmaSq_horizon_retune (σ : ℝ) {M : ℕ}
    (hM : 2 ≤ M) :
    criticalSigmaSq (Real.log M * (σ * replicaOverlap M - 1)) M =
      σ := by
  have hlog : Real.log (M : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hM)).ne'
  have hR := (replicaOverlap_pos (by omega : 1 ≤ M)).ne'
  simp only [criticalSigmaSq]
  field_simp
  ring

private theorem latticeRepresentative_mul_scale (B K : ℕ) (z : Site) :
    latticeRepresentative (B * K) z =
      (Real.sqrt (B : ℝ))⁻¹ • latticeRepresentative K z := by
  simp only [latticeRepresentative, Nat.cast_mul, mul_div_assoc, Real.sqrt_mul
    (Nat.cast_nonneg B), mul_inv_rev, smul_smul]
  congr 1
  ring

/-- Moving critical parameters and arbitrary cofinal lattice scales admit the
spatial renewal limit on every positive finite horizon. -/
theorem tendsto_scaled_spatialRenewal_parameter_moving_horizon
    (K : ℕ → ℕ) (hK : Tendsto K atTop atTop)
    (θ : ℕ → ℝ) (ϑ u : ℝ) (hθ : Tendsto θ atTop (𝓝 ϑ)) (hu : 0 < u)
    (r : ℕ → ℕ) (hr : Tendsto (fun j => (r j : ℝ) / K j) atTop (𝓝 u))
    (z : ℕ → Site) (y : Plane)
    (hz : Tendsto (fun j => latticeRepresentative (K j) (z j)) atTop (𝓝 y))
    (hp : ∀ᶠ j in atTop, Even ((r j : ℤ) + z j 0 + z j 1)) :
    Tendsto (fun j => ((K j : ℝ) / 4) * (K j / Real.log (K j)) *
      Collision.spatialRenewal (criticalSigmaSq (θ j) (K j)) (r j) (z j)) atTop
      (𝓝 (DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) u * heatKernel (u / 2) y)) := by
  obtain ⟨B, hB⟩ := exists_nat_gt (max u 1)
  have hBu : u < (B : ℝ) := (le_max_left _ _).trans_lt hB
  have hB1 : (1 : ℝ) < B := (le_max_right _ _).trans_lt hB
  have hBpos : (0 : ℝ) < B := lt_trans zero_lt_one hB1
  have hBn : 0 < B := by exact_mod_cast hBpos
  let M : ℕ → ℕ := fun j => B * K j
  let θ' : ℕ → ℝ := fun j => Real.log (M j) *
    (criticalSigmaSq (θ j) (K j) * replicaOverlap (M j) - 1)
  have hratio : Tendsto (fun j => (M j : ℝ) / K j) atTop (𝓝 (B : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hK.eventually (eventually_gt_atTop 0)] with j hj
    dsimp [M]
    rw [Nat.cast_mul, mul_div_cancel_right₀ _ (by exact_mod_cast hj.ne')]
  have hM : Tendsto M atTop atTop := by
    apply tendsto_atTop_mono (fun j => Nat.le_mul_of_pos_left (K j) hBn) hK
  have htune := PolymerCalculus.tendsto_critical_clock_tuning_along hBpos hK hratio hθ
  have hθ' : Tendsto θ' atTop (𝓝 (ϑ + Real.log B)) := by
    have hh := htune.add (hθ.add_const (Real.log B))
    simp only [zero_add] at hh
    convert hh using 1
    funext j
    dsimp only [θ']
    ring
  have hr' : Tendsto (fun j => (r j : ℝ) / M j) atTop (𝓝 (u / B)) := by
    convert hr.div_const (B : ℝ) using 1
    funext j
    dsimp only [M]
    rw [Nat.cast_mul]
    field_simp
  have hz' : Tendsto (fun j => latticeRepresentative (M j) (z j)) atTop
      (𝓝 ((Real.sqrt (B : ℝ))⁻¹ • y)) := by
    simpa only [M, latticeRepresentative_mul_scale] using hz.const_smul ((Real.sqrt (B : ℝ))⁻¹)
  have hunit := tendsto_scaled_spatialRenewal_parameter_moving_unit M hM θ'
    (ϑ + Real.log B) (u / B) hθ' (div_pos hu hBpos)
    ((div_lt_one hBpos).mpr hBu) r hr' z _ hz' hp
  have hlog : Tendsto (fun j => Real.log (M j) / Real.log (K j)) atTop (𝓝 1) := by
    have base : Tendsto (fun N : ℕ => Real.log (B * N : ℕ) / Real.log N) atTop (𝓝 1) :=
      PolymerCalculus.tendsto_log_clock_div_log hBpos (by
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_gt_atTop 0] with N hN
        rw [Nat.cast_mul, mul_div_cancel_right₀ _ (by exact_mod_cast hN.ne')])
    exact base.comp hK
  have hlimit := ((hlog.const_mul ((B : ℝ)^2)⁻¹).mul hunit)
  have hscalar := scalarDensity_horizon_rescale_critical ϑ B u hBpos hu
  have hheat := DeltaBose.heatKernel_scale (a := (B : ℝ)⁻¹) (t := u / 2)
    (inv_pos.mpr hBpos) y
  rw [Real.sqrt_inv] at hheat
  have hvalue : ((B : ℝ)^2)⁻¹ * 1 *
      (DeltaBose.scalarDensity (ϑ + Real.log B - Real.eulerMascheroniConstant) (u / B) *
        heatKernel (u / B / 2) ((Real.sqrt (B : ℝ))⁻¹ • y)) =
      DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) u * heatKernel (u / 2) y := by
    rw [show u / B / 2 = (B : ℝ)⁻¹ * (u / 2) by ring, hheat, inv_inv]
    calc
      _ = ((B : ℝ)⁻¹ * DeltaBose.scalarDensity
        (ϑ + Real.log B - Real.eulerMascheroniConstant) (u / B)) * heatKernel (u / 2) y := by
          field_simp
      _ = _ := by rw [hscalar]
  rw [hvalue] at hlimit
  apply hlimit.congr'
  filter_upwards [hK.eventually (eventually_ge_atTop 2), hM.eventually (eventually_ge_atTop 2)]
    with j hj hjM
  rw [show criticalSigmaSq (θ' j) (M j) = criticalSigmaSq (θ j) (K j) from
    criticalSigmaSq_horizon_retune (criticalSigmaSq (θ j) (K j)) hjM]
  have hlogK : Real.log (K j : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hj)).ne'
  have hlogM : Real.log (M j : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hjM)).ne'
  dsimp only [M]
  push_cast
  have hlogM' : Real.log ((B : ℝ) * K j) ≠ 0 := by simpa only [M, Nat.cast_mul] using hlogM
  field_simp [hBpos.ne', hlogK, hlogM']

private theorem horizon_space_bound {N : ℕ} (hN : 0 < N) {R : ℝ} {z : Site}
    (hz : ‖siteToPlane z‖ ≤ R * Real.sqrt N) :
    ‖latticeRepresentative N z‖ ≤ 2 * |R| + 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hR : 0 ≤ R := by
    by_contra hn
    have := mul_neg_of_neg_of_pos (lt_of_not_ge hn) (Real.sqrt_pos.mpr hNr)
    exact (not_lt_of_ge (norm_nonneg _)) (hz.trans_lt this)
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hR (Real.sqrt_nonneg _))).mpr hz
  rw [mul_pow, Real.sq_sqrt hNr.le] at hs
  have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 / (N : ℝ) by positivity)
  have he : (2 / (N : ℝ)) * (R ^ 2 * N) = 2 * R ^ 2 := by field_simp
  rw [he, ← norm_latticeRepresentative_sq] at hh
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2 * |R| + 1)).mp
  rw [abs_of_nonneg hR]
  nlinarith only [hh, sq_nonneg R, hR]

/-- The spatial renewal local limit holds uniformly on every compact positive-time interval. -/
theorem spatialRenewal_localLimit_horizon (A t₀ T R : ℝ) (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A, ∀ n : ℕ,
      t₀ * N ≤ n → (n : ℝ) ≤ T * N → ∀ z : Site,
      Even ((n : ℤ) + z 0 + z 1) → ‖siteToPlane z‖ ≤ R * Real.sqrt N →
        |(N / 4 : ℝ) * (N / Real.log N) *
            Collision.spatialRenewal (criticalSigmaSq ϑ N) n z -
          DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (n / N) *
            heatKernel (n / (2 * N))
              ((Real.sqrt (N / 2))⁻¹ • siteToPlane z)| ≤ ε := by
  classical
  intro ε hε
  have _hT := ht₀.trans_le ht₀T
  by_contra hn
  have hbad : ∀ j : ℕ, ∃ N : ℕ, j + 1 ≤ N ∧ ∃ θ ∈ Set.Icc (-A) A,
      ∃ n : ℕ, t₀ * N ≤ n ∧ (n : ℝ) ≤ T * N ∧ ∃ z : Site,
        Even ((n : ℤ) + z 0 + z 1) ∧ ‖siteToPlane z‖ ≤ R * Real.sqrt N ∧
        ε < |(N / 4 : ℝ) * (N / Real.log N) *
          Collision.spatialRenewal (criticalSigmaSq θ N) n z -
          DeltaBose.scalarDensity (θ - Real.eulerMascheroniConstant) (n / N) *
            heatKernel (n / (2 * N)) (latticeRepresentative N z)| := by
    have hf := hn
    rw [Filter.not_eventually] at hf
    intro j
    obtain ⟨N, hNj, hN⟩ := Filter.frequently_atTop.mp hf (j + 1)
    push Not at hN
    obtain ⟨θ, hθ, n, hlo, hhi, z, hp, hz, he⟩ := hN
    exact ⟨N, hNj, θ, hθ, n, hlo, hhi, z, hp, hz, he⟩
  choose K hK θ hθ r hlo hhi z hp hz he using hbad
  have hKtop : Tendsto K atTop atTop := tendsto_atTop_mono (fun j => (Nat.le_succ j).trans (hK j)) tendsto_id
  let q : ℕ → ℝ × (ℝ × Plane) := fun j => (θ j, ((r j : ℝ) / K j, latticeRepresentative (K j) (z j)))
  let S := Set.Icc (-A) A ×ˢ (Set.Icc t₀ T ×ˢ Metric.closedBall (0 : Plane) (2 * |R| + 1))
  have hS : IsCompact S := isCompact_Icc.prod (isCompact_Icc.prod (isCompact_closedBall _ _))
  have hq : ∀ j, q j ∈ S := by
    intro j
    have hpos : (0 : ℝ) < K j := by exact_mod_cast (show 0 < K j by have := hK j; omega)
    refine ⟨hθ j, ⟨?_, ?_⟩, ?_⟩
    · exact (le_div_iff₀ hpos).mpr (hlo j)
    · exact (div_le_iff₀ hpos).mpr (hhi j)
    · rw [Metric.mem_closedBall, dist_zero_right]
      exact horizon_space_bound (by have := hK j; omega) (hz j)
  obtain ⟨p, hpmem, f, hf, hlim⟩ := hS.tendsto_subseq hq
  have hscale := hKtop.comp hf.tendsto_atTop
  have hparam := (continuous_fst.tendsto p).comp hlim
  have htime := (continuous_fst.tendsto p.2).comp ((continuous_snd.tendsto p).comp hlim)
  have hspace := (continuous_snd.tendsto p.2).comp ((continuous_snd.tendsto p).comp hlim)
  have hupos : 0 < p.2.1 := ht₀.trans_le hpmem.2.1.1
  have hrenewal := tendsto_scaled_spatialRenewal_parameter_moving_horizon
    (K ∘ f) hscale (θ ∘ f) p.1 p.2.1 hparam hupos (r ∘ f) htime (z ∘ f) p.2.2 hspace
    (Eventually.of_forall fun j => hp (f j))
  have hdensity := (horizon_scalarDensity_continuousAt_pos
    (p.1 - Real.eulerMascheroniConstant) p.2.1 hupos).tendsto.comp
    ((hparam.sub_const Real.eulerMascheroniConstant).prodMk_nhds htime)
  have htimehalf : Tendsto (fun j => (r (f j) : ℝ) / (2 * K (f j))) atTop (𝓝 (p.2.1 / 2)) := by
    convert htime.div_const 2 using 1
    funext j
    dsimp only [q, Function.comp_apply]
    ring
  have hheat := horizon_tendsto_heatKernel_time_space (p.2.1 / 2) (half_pos hupos) p.2.2
    _ htimehalf _ hspace
  have herr := (hrenewal.sub (hdensity.mul hheat)).abs
  simp only [sub_self, abs_zero] at herr
  have hsmall := herr.eventually (Iio_mem_nhds hε)
  obtain ⟨j, hj⟩ := hsmall.exists
  exact (not_lt_of_gt (he (f j))) hj

/-- The spatial renewal moving local limit has no upper restriction on time. -/
theorem tendsto_scaled_spatialRenewal_moving_horizon
    (ϑ u : ℝ) (hu : 0 < u)
    (rN : ℕ → ℕ) (hr : Tendsto (fun N : ℕ => (rN N : ℝ) / N) atTop (𝓝 u))
    (zN : ℕ → Site) (y : Plane)
    (hz : Tendsto (fun N : ℕ => latticeRepresentative N (zN N)) atTop (𝓝 y))
    (hphase : ∀ᶠ N : ℕ in atTop, Even ((rN N : ℤ) + zN N 0 + zN N 1)) :
    Tendsto (fun N : ℕ => ((N : ℝ) / 4) * (N / Real.log N) *
        Collision.spatialRenewal (criticalSigmaSq ϑ N) (rN N) (zN N)) atTop
      (𝓝 (DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) u *
        heatKernel (u / 2) y)) := by
  exact tendsto_scaled_spatialRenewal_parameter_moving_horizon id tendsto_id
    (fun _ => ϑ) ϑ u tendsto_const_nhds hu rN hr zN y hz hphase

end Critical2DKPZ.SHF.Moments

end
