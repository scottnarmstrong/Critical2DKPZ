/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonModelDiagonal
public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonArrayVarianceClt
import Mathlib.Tactic

/-! # The scalar quasi-critical lattice CLT for exact cell coefficients -/

@[expose] public noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators NNReal

namespace Critical2DKPZ.Extensions.GffTangent

/-- Actual cell-weighted time blocks are independent at every finite scale. -/
theorem iIndepFun_cellBlockFluctuation (β l : ℝ) (N n M : ℕ) (f : TestFn) :
    iIndepFun (fun i : ℕ => cellBlockFluctuation β l N n M i f) disorderLaw := by
  apply iIndepFun_latticeWindowFluctuation β (Real.sqrt l)
    (quasiCriticalBlockClock n M) (fun i => quasiCriticalBlockClock n M (i + 1))
    (fun i => monotone_quasiCriticalBlockClock n M (Nat.le_succ i)) ?_
    (fun _ => fixedHorizonCellSites N f) (fun _ => signedCellProfile N f)
  intro i j hij
  apply Set.disjoint_left.mpr
  intro k hki hkj
  rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
  · have hh := monotone_quasiCriticalBlockClock n M (show i + 1 ≤ j by omega)
    exact (not_lt_of_ge (hki.2.trans hh)) hkj.1
  · have hh := monotone_quasiCriticalBlockClock n M (show j + 1 ≤ i by omega)
    exact (not_lt_of_ge (hkj.2.trans hh)) hki.1

/-- CCR25's quasi-critical scalar CLT in the library's actual polymer
objects, with exact even-cell integration and the 4*pi covariance. -/
theorem tendstoInDistribution_sqrt_finiteEntranceFluctuation
    (l β : ℕ → ℝ) (hl : Tendsto l atTop atTop)
    (hratio : Tendsto (fun N => l N / Real.log (N : ℝ)) atTop (𝓝 0))
    (hβ : ∀ᶠ N : ℕ in atTop, 0 < β N)
    (hσ : ∀ᶠ N : ℕ in atTop, Polymer.sigmaSq (β N) = criticalSigmaSq (-l N) N)
    (n : ℕ → ℕ) {T : ℝ} (hT : 0 < T)
    (hn : Tendsto (fun N : ℕ => (n N : ℝ) / N) atTop (𝓝 T)) (f : TestFn) :
    TendstoInDistribution (fun N => finiteEntranceFluctuation (β N) (Real.sqrt (l N))
      0 (n N) (fixedHorizonCellSites N f) (signedCellProfile N f)) atTop id
      (fun _ => disorderLaw) (gaussianReal 0 (Real.toNNReal
        (4 * Real.pi * ∫ t in Ioo 0 T, ∫ p : Plane × Plane,
          f p.1 * f p.2 * heatKernel (2 * t) (p.2 - p.1) ∂(volume.prod volume)))) := by
  obtain ⟨M, _, _, herr, hvar, hfourth⟩ :=
    exists_slow_cellBlock_partition l β hl hratio hβ hσ n hT hn f
  let W : (N : ℕ) → Fin (M N) → Disorder → ℝ := fun N i =>
    cellBlockFluctuation (β N) (l N) N (n N) (M N) i f
  let v := 4 * Real.pi * ∫ t in Ioo 0 T, ∫ p : Plane × Plane,
    f p.1 * f p.2 * heatKernel (2 * t) (p.2 - p.1) ∂(volume.prod volume)
  have hv : 0 ≤ v := ge_of_tendsto hvar (Eventually.of_forall (fun N =>
    Finset.sum_nonneg (fun i _ => integral_nonneg (fun _ => sq_nonneg _))))
  have hmem (N : ℕ) (i : Fin (M N)) : MemLp (W N i) 4 disorderLaw :=
    memLp_latticeWindowFluctuation _ _ _ _ _ _ 4 (by norm_num)
  have hind (N : ℕ) : iIndepFun (W N) disorderLaw :=
    (iIndepFun_cellBlockFluctuation (β N) (l N) N (n N) (M N) f).precomp Fin.val_injective
  have hmean (N : ℕ) (i : Fin (M N)) : (∫ ω, W N i ω ∂disorderLaw) = 0 :=
    integral_latticeWindowFluctuation _ _ _ _ _ _
  have hclt := tendstoInDistribution_fin_sum_of_variance_fourth disorderLaw atTop M W
    (Real.toNNReal v) hind (fun N i => (hmem N i).aemeasurable) hmem hmean
    (by simpa only [Real.coe_toNNReal v hv] using hvar) hfourth
  let X := fun N => finiteEntranceFluctuation (β N) (Real.sqrt (l N)) 0 (n N)
    (fixedHorizonCellSites N f) (signedCellProfile N f)
  have hX (N : ℕ) : MemLp (X N) 2 disorderLaw :=
    memLp_finiteEntranceFluctuation _ _ _ _ _ _ 2 (by norm_num)
  have hdiff : TendstoInMeasure disorderLaw
      (fun N ω => X N ω - ∑ i, W N i ω) atTop (fun _ => 0) :=
    ScaleLimit.tendstoInMeasure_zero_of_integral_sq disorderLaw atTop _
      (fun N => (hX N).sub (memLp_finsetSum _ (fun i _ =>
        (hmem N i).mono_exponent (by norm_num)))) herr
  exact tendstoInDistribution_of_tendstoInMeasure_sub X id hclt hdiff
    (fun N => (hX N).aemeasurable)

end Critical2DKPZ.Extensions.GffTangent
