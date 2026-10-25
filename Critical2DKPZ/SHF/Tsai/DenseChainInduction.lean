/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.DenseGridBlocks
public import Critical2DKPZ.SHF.Tsai.PrefixChainCouplingLimits
import Critical2DKPZ.SHF.Tsai.GridIntervalFactors
import Critical2DKPZ.SHF.Tsai.TwoIndexChainLimits
import Critical2DKPZ.SHF.Tsai.IteratedProbabilityLimits
import Critical2DKPZ.SHF.Tsai.TwoIncrementLimits

/-! # Identifying the next finite-chain limit

The fixed-final-connector limits identify the iterated probability limit.
The universal joint chain limit then agrees almost surely with the coarse
increment by two-increment composition. Its diagonal gives the next chain.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology CompactlySupported

namespace Critical2DKPZ.SHF.Tsai

/-- The finite-chain induction step on compact endpoint tests. -/
theorem IsDenseSHF.tendstoInMeasure_chain_succ_compact {θ : ℝ} {D : Set ℝ} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsDenseSHF θ D P Z)
    (K : ℕ) (t : ℕ → ℝ) (ht : StrictMono t) (htD : ∀ k ≤ K + 2, t k ∈ D)
    (w : ℕ → ℕ → Plane → ℝ) (hw : ∀ k, IsL2ApplicableMollifier (w k))
    (hIH : ∀ g g' : Plane → ℝ, MemLp g 2 → MemLp g' 2 →
      TendstoInMeasure P (fun n ω => ∫ p, g p.1 * g' p.2
        ∂chainProduct (fun k => Z (t k) (t (k + 1)) ω) (fun k => w k n) K) atTop
          (fun ω => ∫ p, g p.1 * g' p.2 ∂Z (t 0) (t (K + 1)) ω))
    (g g' : C_c(Plane, ℝ)) :
    TendstoInMeasure P (fun n ω => ∫ p, g p.1 * g' p.2
      ∂chainProduct (fun k => Z (t k) (t (k + 1)) ω) (fun k => w k n) (K + 1)) atTop
        (fun ω => ∫ p, g p.1 * g' p.2 ∂Z (t 0) (t (K + 2)) ω) := by
  have hg : MemLp g 2 := g.continuous.memLp_of_hasCompactSupport g.hasCompactSupport
  have hg' : MemLp g' 2 := g'.continuous.memLp_of_hasCompactSupport g'.hasCompactSupport
  let B (k : ℕ) := Z (t k) (t (k + 1))
  let τ (k : ℕ) := t (k + 1) - t k
  have hτ (k : ℕ) (_ : k ≤ K + 1) : 0 < τ k := sub_pos.2 (ht (Nat.lt_succ_self k))
  have hB (k : ℕ) (hk : k ≤ K + 1) : HasDeltaBoseMoments θ (τ k) P (B k) :=
    hZ.hasDeltaBoseMoments_natConsecutive (K + 1) t ht htD k hk
  have hind : iIndepFun (fun k : Fin (K + 2) => B k) P :=
    hZ.iIndepFun_natConsecutive (K + 1) t ht htD
  have hC := hZ.hasDeltaBoseMoments (htD 0 (by omega)) (htD (K + 1) (by omega))
    (ht (by omega : 0 < K + 1))
  obtain ⟨φ, hφ, _hφLF, hFactor⟩ := hZ.exists_grid_interval_factor P Z (K + 1) t ht
    (fun k hk => htD k (by omega)) (by omega : 0 < K + 1) le_rfl
  have hfinite (J : ℕ) (v : ℕ → Plane → ℝ) (ω : Ω) :
      chainProduct (fun k => Z (t (Fin.ofNat (J + 1) k))
        (t ((Fin.ofNat (J + 1) k : ℕ) + 1)) ω) v J =
      chainProduct (fun k => Z (t k) (t (k + 1)) ω) v J :=
    chainProduct_fin_restrict J (fun k => Z (t k) (t (k + 1)) ω) v
  have hInner (r : ℕ) := tendstoInMeasure_chain_coarse_prefix P K
    (fun i : Fin (K + 2) => τ i) (fun i => hτ i (Nat.le_of_lt_succ i.is_lt))
    (fun i : Fin (K + 2) => B i) (fun i => hB i (Nat.le_of_lt_succ i.is_lt)) hind
    (Z (t 0) (t (K + 1))) hC (sub_pos.2 (ht (by omega : 0 < K + 1)))
    φ hφ hFactor w hw r g g' (fun f hf => by
      simpa only [B, Fin.val_castSucc, hfinite] using hIH g f hg hf)
  have hInner' (r : ℕ) : TendstoInMeasure P (fun n ω => ∫ p, g p.1 * g' p.2
      ∂chainProduct (fun k => B k ω) (fun k => w k (if k = K then r else n)) (K + 1)) atTop
      (fun ω => ∫ p, g p.1 * g' p.2 ∂smoothedProductMeasure
        (Z (t 0) (t (K + 1)) ω) (w K r) (Z (t (K + 1)) (t (K + 2)) ω)) := by
    simpa only [B, hfinite, Fin.val_last] using hInner r
  obtain ⟨F, _hF, hJoint⟩ := exists_chainPairing_twoIndex_limit (K + 1) K τ hτ B hB hind
    w hw g g' hg hg'
  have hOuter := tendstoInMeasure_of_joint_of_iterated P _ _ F hJoint hInner'
  have hTwo := isDenseSHF_smoothedProduct_tendsto_tensor θ D P Z hZ
    (htD 0 (by omega)) (htD (K + 1) (by omega)) (htD (K + 2) le_rfl)
    (ht (by omega : 0 < K + 1)) (ht (by omega : K + 1 < K + 2)) (w K) (hw K) g g' hg hg'
  have hCoarse := tendstoInMeasure_of_integrable_fourth_moments P _ _ hTwo.1 hTwo.2
  have hFEq := tendstoInMeasure_ae_unique hOuter hCoarse
  have hDiag := (hJoint.comp tendsto_atTop_diagonal).congr_right hFEq
  simpa only [Function.comp_def, ite_self, B] using hDiag

end Critical2DKPZ.SHF.Tsai

end
