/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.DenseChainInduction
import Critical2DKPZ.SHF.Tsai.ChainTensorEndpointExtension
import Critical2DKPZ.SHF.Tsai.ChainLimitIdentification

/-! # Dense-flow chain convergence for all L² tensors

Induction identifies the probability limit on compact tensor tests. Uniform
endpoint bounds extend it to arbitrary L² representatives, and the chain
Cauchy theorem upgrades it to actual fourth-moment convergence.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- Every finite chain converges in probability to its coarse increment on all L² tensors. -/
theorem IsDenseSHF.tendstoInMeasure_chain_tensor {θ : ℝ} {D : Set ℝ} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsDenseSHF θ D P Z)
    (K : ℕ) (t : ℕ → ℝ) (ht : StrictMono t) (htD : ∀ k ≤ K + 1, t k ∈ D)
    (w : ℕ → ℕ → Plane → ℝ) (hw : ∀ k, IsL2ApplicableMollifier (w k))
    (g g' : Plane → ℝ) (hg : MemLp g 2) (hg' : MemLp g' 2) :
    TendstoInMeasure P (fun n ω => ∫ p, g p.1 * g' p.2
      ∂chainProduct (fun k => Z (t k) (t (k + 1)) ω) (fun k => w k n) K) atTop
        (fun ω => ∫ p, g p.1 * g' p.2 ∂Z (t 0) (t (K + 1)) ω) := by
  induction K generalizing g g' with
  | zero =>
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    simpa only [chainProduct, dist_self, not_le.mpr hε, Set.ofPred_false, measure_empty] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
  | succ K ih =>
    have hτ (k : ℕ) (_ : k ≤ K + 1) : 0 < t (k + 1) - t k :=
      sub_pos.2 (ht (Nat.lt_succ_self k))
    have hB := hZ.hasDeltaBoseMoments_natConsecutive (K + 1) t ht htD
    have hind := hZ.iIndepFun_natConsecutive (K + 1) t ht htD
    have hC := hZ.hasDeltaBoseMoments (htD 0 (by omega)) (htD (K + 2) (by omega))
      (ht (by omega : 0 < K + 2))
    apply tendstoInMeasure_chain_tensor_of_compact (K + 1) (fun k => t (k + 1) - t k) hτ
      (fun k => Z (t k) (t (k + 1))) hB hind w hw (Z (t 0) (t (K + 2))) hC
      (sub_pos.2 (ht (by omega : 0 < K + 2))) _ g g' hg hg'
    intro f f'
    exact hZ.tendstoInMeasure_chain_succ_compact P Z K t ht htD w hw
      (fun a b ha hb => ih (fun k hk => htD k (by omega)) a b ha hb) f f'


end Critical2DKPZ.SHF.Tsai

end
