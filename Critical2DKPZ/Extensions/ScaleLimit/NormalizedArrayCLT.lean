/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.FiniteRowTransport
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Tactic

/-! # Lyapunov convergence of finite independent arrays

The uniform bounded-continuous-test estimate gives convergence along an arbitrary
filter. No sequence reduction is needed for this scalar array theorem.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Independent centred arrays with variance tending to one and vanishing absolute
third-moment sum converge to the standard Gaussian, along any index filter. -/
theorem tendstoInDistribution_sum_of_lyapunov {κ Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (l : Filter κ)
    (n : κ → ℕ) (Y : κ → ℕ → Ω → ℝ)
    (hind : ∀ L, iIndepFun (Y L) P)
    (hm : ∀ L i, AEMeasurable (Y L i) P)
    (hmem : ∀ L i, MemLp (Y L i) 3 P)
    (hmean : ∀ L i, (∫ ω, Y L i ω ∂P) = 0)
    (hvar : Tendsto (fun L => ∑ i ∈ Finset.range (n L), ∫ ω, Y L i ω ^ 2 ∂P)
      l (𝓝 1))
    (hthird : Tendsto (fun L => ∑ i ∈ Finset.range (n L), ∫ ω, |Y L i ω| ^ 3 ∂P)
      l (𝓝 0)) :
    TendstoInDistribution (fun L ω => ∑ i ∈ Finset.range (n L), Y L i ω)
      l id (fun _ => P) (gaussianReal 0 1) := by
  have hsum (L : κ) : AEMeasurable (fun ω => ∑ i ∈ Finset.range (n L), Y L i ω) P := by
    exact Finset.aemeasurable_fun_sum (Finset.range (n L)) (fun i _ => hm L i)
  apply (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ hsum
    (measurable_id.aemeasurable : AEMeasurable id (gaussianReal 0 1))).mpr
  intro h
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := exists_lyapunov_clt_bound_fin h (half_pos hε)
  have hv : ∀ᶠ L in l,
      |(∑ i ∈ Finset.range (n L), ∫ ω, Y L i ω ^ 2 ∂P) - 1| ≤ δ := by
    filter_upwards [hvar.eventually (Metric.ball_mem_nhds 1 hδ)] with L hL
    exact (by simpa only [Metric.mem_ball, Real.dist_eq] using hL :
      |(∑ i ∈ Finset.range (n L), ∫ ω, Y L i ω ^ 2 ∂P) - 1| < δ).le
  have ht : ∀ᶠ L in l,
      (∑ i ∈ Finset.range (n L), ∫ ω, |Y L i ω| ^ 3 ∂P) ≤ δ :=
    (hthird.eventually (Iio_mem_nhds hδ)).mono fun _ hL => hL.le
  filter_upwards [hv, ht] with L hvL htL
  have hb := hbound P (n L) (fun i => Y L i.val) 1 zero_lt_one
    ((hind L).precomp Fin.val_injective) (fun i => hm L i) (fun i => hmem L i)
    (fun i => hmean L i)
    (by rw [Fin.sum_univ_eq_sum_range (fun i => ∫ ω, Y L i ω ^ 2 ∂P)]; simpa only [one_pow, mul_one] using hvL)
    (by rw [Fin.sum_univ_eq_sum_range (fun i => ∫ ω, |Y L i ω| ^ 3 ∂P)]; simpa only [one_pow, mul_one] using htL)
  have hb' : |(∫ ω, h (∑ i ∈ Finset.range (n L), Y L i ω) ∂P) -
      (∫ y, h y ∂gaussianReal 0 1)| ≤ ε / 2 := by
    have heq (ω : Ω) : (∑ i : Fin (n L), Y L i.val ω) =
        ∑ i ∈ Finset.range (n L), Y L i ω :=
      Fin.sum_univ_eq_sum_range (fun i => Y L i ω) (n L)
    simpa only [heq, div_one] using hb
  exact lt_of_le_of_lt (by simpa only [Real.dist_eq, id_eq] using hb') (half_lt_self hε)

end Critical2DKPZ.Extensions.ScaleLimit
