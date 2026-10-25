/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordTimeProfile
import Mathlib.Tactic

/-! # Moving tested renewal-time profiles on arbitrary finite horizons -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory Filter Polymer
open scoped CompactlySupported Topology Uniformity

private theorem tendsto_pairTwoTestedSpatialSlice_along_horizon
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (ϑ v q : ℝ) (hv : 0 < v) (hq : 0 < q)
    (rN kN : ℕ → ℕ)
    (hr : Tendsto (fun N : ℕ => (rN N : ℝ) / M N) atTop (𝓝 v))
    (hk : Tendsto (fun N : ℕ => (kN N : ℝ) / M N) atTop (𝓝 q))
    (zN : ℕ → Site) (z : Plane)
    (hz : Tendsto (fun N : ℕ => latticeRepresentative (M N) (zN N)) atTop (𝓝 z))
    (hphase : ∀ᶠ N : ℕ in atTop,
      Even (zN N 0 + zN N 1 + (rN N : ℤ) + (kN N : ℤ)))
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (xN : ℕ → Fin 2 → Site)
    (hx : ∀ᶠ N : ℕ in atTop, ∀ i : Fin 2, xN N i ∈ evenLattice)
    (a : Fin 2 → Plane)
    (ha : ∀ i : Fin 2, Tendsto (fun N : ℕ => latticeRepresentative (M N) (xN N i))
      atTop (𝓝 (a i))) :
    Tendsto (fun N : ℕ => pairTwoTestedSpatialSlice ϑ (M N) (rN N) (kN N) φ (xN N) (zN N))
      atTop (𝓝 (pairTwoTestedSpatialProfile (ϑ - Real.eulerMascheroniConstant) v q φ a z)) := by
  have h := tendsto_pairTwo_tested_spatialSlice_along_horizon M hM ϑ v q hv hq
    rN kN hr hk zN z hz hphase φ xN hx a ha
  have heq : pairTwoTestedSpatialProfile (ϑ - Real.eulerMascheroniConstant) v q φ a z =
      16 * Real.pi * ∫ d : Plane,
        (DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) v * heatKernel (v / 2) d) *
        pairTwoTerminalConvolution (φ 0) q (a 0) (z + d) *
        pairTwoTerminalConvolution (φ 1) q (a 1) (z + d) := by
    unfold pairTwoTestedSpatialProfile
    rw [mul_assoc, ← integral_const_mul]
    apply congrArg (fun r : ℝ => (16 * Real.pi) * r)
    apply integral_congr_ae
    exact Eventually.of_forall fun d => by ring
  rw [heq]
  exact h

/-- Along moving interior renewal times, the sampled spatial profile has the
corresponding continuum spatial convolution as its limit. -/
theorem tendsto_pairTwoTestedSpatialSliceProfile_along_horizon
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (ϑ H : ℝ) (L : ℕ → ℕ)
    (hL : Tendsto (fun N : ℕ => (L N : ℝ) / N) atTop (𝓝 H))
    (uN : ℕ → ℝ) {u : ℝ} (huN : Tendsto uN atTop (𝓝 u))
    (hu : 0 < u) (huH : u < H)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (xN : ℕ → Fin 2 → Site)
    (hx : ∀ᶠ N : ℕ in atTop, ∀ i : Fin 2, xN N i ∈ evenLattice)
    (a : Fin 2 → Plane)
    (ha : ∀ i : Fin 2, Tendsto (fun N : ℕ => latticeRepresentative N (xN N i)) atTop (𝓝 (a i)))
    (zN : ℕ → Site) (z : Plane)
    (hz : Tendsto (fun N : ℕ => latticeRepresentative N (zN N)) atTop (𝓝 z))
    (hphase : ∀ᶠ N : ℕ in atTop, Even (zN N 0 + zN N 1 + (L N : ℤ))) :
    Tendsto (fun N : ℕ => pairTwoTestedSpatialSliceProfile ϑ (M N) (L (M N))
      φ (xN (M N)) (zN (M N)) (uN N)) atTop
      (𝓝 (pairTwoTestedSpatialProfile (ϑ - Real.eulerMascheroniConstant) u (H - u) φ a z)) := by
  let rN : ℕ → ℕ := fun N => Nat.floor ((M N : ℝ) * uN N)
  let kN : ℕ → ℕ := fun N => L (M N) - rN N
  have hr : Tendsto (fun N : ℕ => (rN N : ℝ) / M N) atTop (𝓝 u) :=
    tendsto_floor_scaled_moving M hM uN huN hu
  have hL' : Tendsto (fun N : ℕ => (L (M N) : ℝ) / M N) atTop (𝓝 H) := hL.comp hM
  have hle : ∀ᶠ N : ℕ in atTop, rN N ≤ L (M N) := by
    filter_upwards [hr.eventually (Iio_mem_nhds (show u < (u + H) / 2 by linarith)),
      hL'.eventually (Ioi_mem_nhds (show (u + H) / 2 < H by linarith)),
      hM.eventually (eventually_gt_atTop 0)] with N hrN hLN hN
    have hNr : (0 : ℝ) < M N := by exact_mod_cast hN
    have h : (rN N : ℝ) / M N < (L (M N) : ℝ) / M N := hrN.trans hLN
    have h' := (div_lt_div_iff_of_pos_right hNr).mp h
    exact_mod_cast h'.le
  have hk : Tendsto (fun N : ℕ => (kN N : ℝ) / M N) atTop (𝓝 (H - u)) := by
    apply (hL'.sub hr).congr'
    filter_upwards [hle] with N hN
    simp only [kN, Nat.cast_sub hN, sub_div]
  have hp : ∀ᶠ N : ℕ in atTop,
      Even (zN (M N) 0 + zN (M N) 1 + (rN N : ℤ) + (kN N : ℤ)) := by
    filter_upwards [hM.eventually hphase, hle] with N hpN hN
    rw [Int.even_iff] at hpN ⊢
    dsimp [kN]
    rw [Nat.cast_sub hN]
    omega
  exact tendsto_pairTwoTestedSpatialSlice_along_horizon M hM ϑ u (H - u) hu
    (sub_pos.mpr huH) rN kN hr hk (fun N => zN (M N)) z (hz.comp hM) hp
    φ (fun N => xN (M N)) (hM.eventually hx) a (fun i => (ha i).comp hM)

/-- The future spatial slices converge locally uniformly in interior renewal
time. The microscopic horizon, incoming sites and collision site may move. -/
theorem tendstoLocallyUniformlyOn_pairTwoTestedSpatialSliceProfile_horizon
    (ϑ H : ℝ) (L : ℕ → ℕ)
    (hL : Tendsto (fun N : ℕ => (L N : ℝ) / N) atTop (𝓝 H))
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (xN : ℕ → Fin 2 → Site)
    (hx : ∀ᶠ N : ℕ in atTop, ∀ i : Fin 2, xN N i ∈ evenLattice)
    (a : Fin 2 → Plane)
    (ha : ∀ i : Fin 2, Tendsto (fun N : ℕ => latticeRepresentative N (xN N i)) atTop (𝓝 (a i)))
    (zN : ℕ → Site) (z : Plane)
    (hz : Tendsto (fun N : ℕ => latticeRepresentative N (zN N)) atTop (𝓝 z))
    (hphase : ∀ᶠ N : ℕ in atTop, Even (zN N 0 + zN N 1 + (L N : ℤ))) :
    TendstoLocallyUniformlyOn
      (fun N u => pairTwoTestedSpatialSliceProfile ϑ N (L N) φ (xN N) (zN N) u)
      (fun u => pairTwoTestedSpatialProfile (ϑ - Real.eulerMascheroniConstant) u (H - u) φ a z)
      atTop (Set.Ioo 0 (H)) := by
  apply isOpen_Ioo.tendstoLocallyUniformlyOn_iff_forall_tendsto.mpr
  intro u hu
  have hu0 : 0 < u := hu.1
  have huH : u < H := hu.2
  rw [tendsto_iff_seq_tendsto]
  intro p hp
  rcases tendsto_prod_iff'.mp hp with ⟨hM, huN⟩
  let M : ℕ → ℕ := fun k => (p k).1
  let uN : ℕ → ℝ := fun k => (p k).2
  have hM' : Tendsto M atTop atTop := hM
  have huN' : Tendsto uN atTop (𝓝 u) := huN
  have hdiscrete := tendsto_pairTwoTestedSpatialSliceProfile_along_horizon M hM'
    ϑ H L hL uN huN' hu0 huH φ xN hx a ha zN z hz hphase
  have hcontinuum : Tendsto
      (fun k => pairTwoTestedSpatialProfile (ϑ - Real.eulerMascheroniConstant)
        (uN k) (H - uN k) φ a z) atTop
      (𝓝 (pairTwoTestedSpatialProfile (ϑ - Real.eulerMascheroniConstant) u (H - u) φ a z)) := by
    have hc := continuousAt_pairTwoTestedSpatialProfile
      (ϑ - Real.eulerMascheroniConstant) φ ((u, H - u), a, z) hu0 (sub_pos.mpr huH)
    have harg : Tendsto (fun k => ((uN k, H - uN k), a, z)) atTop
        (𝓝 (((u, H - u), a, z) : (ℝ × ℝ) × (Fin 2 → Plane) × Plane)) :=
      (huN'.prodMk_nhds (tendsto_const_nhds.sub huN')).prodMk_nhds tendsto_const_nhds
    exact Tendsto.comp
      (g := fun p' : (ℝ × ℝ) × (Fin 2 → Plane) × Plane =>
        pairTwoTestedSpatialProfile (ϑ - Real.eulerMascheroniConstant)
          p'.1.1 p'.1.2 φ p'.2.1 p'.2.2)
      (f := fun k => ((uN k, H - uN k), a, z)) hc.tendsto harg
  have hdist : Tendsto (fun k => dist
      (pairTwoTestedSpatialProfile (ϑ - Real.eulerMascheroniConstant) (uN k) (H - uN k) φ a z)
      (pairTwoTestedSpatialSliceProfile ϑ (M k) (L (M k)) φ (xN (M k)) (zN (M k)) (uN k)))
      atTop (𝓝 0) := by
    simpa only [dist_self] using hcontinuum.dist hdiscrete
  have hpair : Tendsto (fun k =>
      (pairTwoTestedSpatialProfile (ϑ - Real.eulerMascheroniConstant) (uN k) (H - uN k) φ a z,
        pairTwoTestedSpatialSliceProfile ϑ (M k) (L (M k)) φ (xN (M k)) (zN (M k)) (uN k)))
      atTop (𝓤 ℝ) := by
    rw [Metric.uniformity_basis_dist.tendsto_right_iff]
    intro ε hε
    exact hdist.eventually (Iio_mem_nhds hε)
  simpa only [Function.comp_def, M, uN] using hpair

/-- Compact interior renewal-time slabs have uniform convergence of the full
spatial convolution, with no spatial truncation. -/
theorem tendstoUniformlyOn_pairTwoTestedSpatialSliceProfile_Icc_horizon
    (ϑ H : ℝ) (L : ℕ → ℕ)
    (hL : Tendsto (fun N : ℕ => (L N : ℝ) / N) atTop (𝓝 H))
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (xN : ℕ → Fin 2 → Site)
    (hx : ∀ᶠ N : ℕ in atTop, ∀ i : Fin 2, xN N i ∈ evenLattice)
    (a : Fin 2 → Plane)
    (ha : ∀ i : Fin 2, Tendsto (fun N : ℕ => latticeRepresentative N (xN N i)) atTop (𝓝 (a i)))
    (zN : ℕ → Site) (z : Plane)
    (hz : Tendsto (fun N : ℕ => latticeRepresentative N (zN N)) atTop (𝓝 z))
    (hphase : ∀ᶠ N : ℕ in atTop, Even (zN N 0 + zN N 1 + (L N : ℤ)))
    {u₀ u₁ : ℝ} (hu₀ : 0 < u₀) (hu₁ : u₁ < H) :
    TendstoUniformlyOn
      (fun N u => pairTwoTestedSpatialSliceProfile ϑ N (L N) φ (xN N) (zN N) u)
      (fun u => pairTwoTestedSpatialProfile (ϑ - Real.eulerMascheroniConstant) u (H - u) φ a z)
      atTop (Set.Icc u₀ u₁) := by
  have hlocal := tendstoLocallyUniformlyOn_pairTwoTestedSpatialSliceProfile_horizon
    ϑ H L hL φ xN hx a ha zN z hz hphase
  have hsub : Set.Icc u₀ u₁ ⊆ Set.Ioo 0 (H) := by
    intro u hu
    exact ⟨hu₀.trans_le hu.1, hu.2.trans_lt hu₁⟩
  exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
    (isCompact_Icc : IsCompact (Set.Icc u₀ u₁))).mp (hlocal.mono hsub)

end Critical2DKPZ.SHF.Moments
