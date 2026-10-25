/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A. Bou-Rabee, Scott Armstrong
Modified for Critical2DKPZ, 2026.
-/
module

import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.Analysis.Calculus.MeanValue
public import Critical2DKPZ.Analysis.Sobolev.Rellich.RellichNet
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Finite nets for uniformly bounded derivative families on a common compact support.

Adapted from work of A. Bou-Rabee, licensed under Apache 2.0. -/

@[expose] public section

noncomputable section

open Set Metric
open scoped ENNReal

namespace Critical2DKPZ.Analysis.Sobolev.Rellich

/-- A vector-valued uniformly bounded Lipschitz family has finite sup-nets. -/
theorem exists_finite_vector_supNet {α F : Type*}
    [PseudoMetricSpace α] [CompactSpace α] [NormedAddCommGroup F] [ProperSpace F]
    (S : Set (BoundedContinuousFunction α F)) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ f ∈ S, ∀ x, ‖f x‖ ≤ C)
    (hlip : ∀ f ∈ S, ∀ x y, dist (f x) (f y) ≤ C * dist x y)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Set (BoundedContinuousFunction α F), T ⊆ S ∧ T.Finite ∧
      ∀ f ∈ S, ∃ g ∈ T, dist f g ≤ ε := by
  have hcomp : IsCompact (closure S) :=
    BoundedContinuousFunction.arzela_ascoli (closedBall 0 C)
      (isCompact_closedBall 0 C) S
      (fun f x hf => by simpa only [mem_closedBall, dist_zero_right] using hb f hf x)
      (by
        intro x
        refine Metric.equicontinuousAt_iff.mpr ?_
        intro η hη
        refine ⟨η / (C + 1), by positivity, fun y hy i => ?_⟩
        have h1 := hlip i i.2 x y
        have hden : (0 : ℝ) < C + 1 := by linarith
        have h2 : dist x y < η / (C + 1) := by rwa [dist_comm] at hy
        have h3 : C * (η / (C + 1)) < η := by
          rw [← mul_div_assoc, div_lt_iff₀ hden]
          nlinarith [hη]
        have h4 := mul_le_mul_of_nonneg_left (le_of_lt h2) hC
        linarith)
  have htb : TotallyBounded S := hcomp.totallyBounded.subset subset_closure
  rw [EMetric.totallyBounded_iff'] at htb
  obtain ⟨T, hTS, hTfin, hTcov⟩ :=
    htb (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
  refine ⟨T, hTS, hTfin, ?_⟩
  intro f hf
  obtain ⟨g, hgT, hfg⟩ := Set.mem_iUnion₂.1 (hTcov hf)
  refine ⟨g, hgT, ?_⟩
  rw [Metric.mem_eball, edist_dist, ENNReal.ofReal_lt_ofReal_iff hε] at hfg
  exact le_of_lt hfg

private theorem jet_finiteDimensional (d k : ℕ) :
    FiniteDimensional ℝ (Space d [×k]→L[ℝ] ℝ) := by
  exact FiniteDimensional.of_injective
    (ContinuousMultilinearMap.toMultilinearMapLinear :
      (Space d [×k]→L[ℝ] ℝ) →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin k => Space d) ℝ)
    ContinuousMultilinearMap.toMultilinearMap_injective

/-- Simultaneous finite derivative-net, with centres in `S` and global error control. -/
theorem exists_finite_simultaneous_jet_net {d : ℕ} {K : Set (Space d)}
    (hK : IsCompact K) (S : Set (Space d → ℝ))
    (hsm : ∀ f ∈ S, ContDiff ℝ (⊤ : ℕ∞) f)
    (hsupp : ∀ f ∈ S, tsupport f ⊆ K) (m : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ f ∈ S, ∀ k ≤ m + 1, ∀ x, ‖iteratedFDeriv ℝ k f x‖ ≤ C)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Set (Space d → ℝ), T ⊆ S ∧ T.Finite ∧
      ∀ f ∈ S, ∃ g ∈ T, ∀ k ≤ m, ∀ x,
        ‖iteratedFDeriv ℝ k (fun y => f y - g y) x‖ ≤ ε := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let J := (i : Fin (m + 1)) → Space d [×i.val]→L[ℝ] ℝ
  let : ∀ i : Fin (m + 1),
      FiniteDimensional ℝ (Space d [×i.val]→L[ℝ] ℝ) :=
    fun i => jet_finiteDimensional d i.val
  let jet (f : S) : BoundedContinuousFunction K J :=
    BoundedContinuousFunction.mkOfCompact
      ⟨fun x i => iteratedFDeriv ℝ i.val f.val x.val,
        continuous_pi fun i =>
          ((hsm f.val f.property).continuous_iteratedFDeriv
            (ENat.natCast_le_of_coe_top_le_withTop le_rfl _)).comp
            continuous_subtype_val⟩
  have hjetb : ∀ f ∈ Set.range jet, ∀ x, ‖f x‖ ≤ C := by
    rintro _ ⟨f, rfl⟩ x
    exact (pi_norm_le_iff_of_nonneg hC).2 fun i =>
      hb f.val f.property i.val (by omega) x.val
  have hjetlip : ∀ f ∈ Set.range jet, ∀ x y, dist (f x) (f y) ≤ C * dist x y := by
    rintro _ ⟨f, rfl⟩ x y
    refine (dist_pi_le_iff (mul_nonneg hC dist_nonneg)).2 fun i => ?_
    have hdiff : Differentiable ℝ (iteratedFDeriv ℝ i.val f.val) :=
      (hsm f.val f.property).differentiable_iteratedFDeriv
        (ENat.natCast_lt_of_coe_top_le_withTop le_rfl _)
    have hbd : ∀ z, ‖fderiv ℝ (iteratedFDeriv ℝ i.val f.val) z‖ ≤ C := by
      intro z
      rw [norm_fderiv_iteratedFDeriv]
      exact hb f.val f.property (i.val + 1) (by omega) z
    have hl := lipschitzWith_of_nnnorm_fderiv_le
      (C := ⟨C, hC⟩) hdiff (fun z => hbd z)
    exact hl.dist_le_mul x.val y.val
  obtain ⟨T, hTS, hTfin, hTnet⟩ :=
    exists_finite_vector_supNet (Set.range jet) hC hjetb hjetlip hε
  let : Fintype T := hTfin.fintype
  have hpre : ∀ g : T, ∃ f : S, jet f = g.val := fun g => hTS g.property
  choose pick hpick using hpre
  let U : Set (Space d → ℝ) := Set.range (fun g : T => (pick g).val)
  refine ⟨U, ?_, Set.finite_range _, ?_⟩
  · rintro f ⟨g, rfl⟩
    exact (pick g).property
  · intro f hf
    obtain ⟨g, hg, hfg⟩ := hTnet (jet ⟨f, hf⟩) ⟨⟨f, hf⟩, rfl⟩
    let q : T := ⟨g, hg⟩
    refine ⟨(pick q).val, ⟨q, rfl⟩, ?_⟩
    intro k hk x
    rw [show (fun y => f y - (pick q).val y) = f - (pick q).val from rfl]
    rw [iteratedFDeriv_sub_apply
      ((hsm f hf).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _)).contDiffAt
      ((hsm (pick q).val (pick q).property).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl _)).contDiffAt]
    by_cases hx : x ∈ K
    · have hpoint := BoundedContinuousFunction.dist_coe_le_dist
        (f := jet ⟨f, hf⟩) (g := g) ⟨x, hx⟩
      have hcomp := (dist_pi_le_iff hε.le).1 (hpoint.trans hfg)
        (⟨k, by omega⟩ : Fin (m + 1))
      have hq : jet (pick q) = g := hpick q
      rw [← hq] at hcomp
      change dist (iteratedFDeriv ℝ k f x)
        (iteratedFDeriv ℝ k (pick q).val x) ≤ ε at hcomp
      simpa only [dist_eq_norm] using hcomp
    · have hfzero : iteratedFDeriv ℝ k f x = 0 := by
        by_contra hn
        exact hx (hsupp f hf (support_iteratedFDeriv_subset k hn))
      have hgzero : iteratedFDeriv ℝ k (pick q).val x = 0 := by
        by_contra hn
        exact hx (hsupp (pick q).val (pick q).property
          (support_iteratedFDeriv_subset k hn))
      rw [hfzero, hgzero, sub_self, norm_zero]
      exact hε.le

/-- Common compact support and uniform derivative bounds give finite Sobolev nets. -/
theorem exists_finite_sobolev_net_of_uniform_jets {d : ℕ} {K : Set (Space d)}
    (hK : IsCompact K) (S : Set (Space d → ℝ))
    (hsm : ∀ f ∈ S, ContDiff ℝ (⊤ : ℕ∞) f)
    (hsupp : ∀ f ∈ S, tsupport f ⊆ K)
    (hjets : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ f ∈ S, ∀ k ≤ m, ∀ x, ‖iteratedFDeriv ℝ k f x‖ ≤ C)
    (s₀ : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ T : Set (Space d → ℝ), T ⊆ S ∧ T.Finite ∧
      ∀ f ∈ S, ∃ g ∈ T,
        sobolevNormSq d s₀ (fun x => f x - g x) ≤ ENNReal.ofReal η := by
  obtain ⟨m, A, hA, hres⟩ := rkResidual_diff_bound hK s₀
  obtain ⟨C, hC, hbound⟩ := hjets (m + 1)
  let ε := min 1 (η / (A + 1))
  have hε : 0 < ε := lt_min zero_lt_one (div_pos hη (by linarith))
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεA : ε ≤ η / (A + 1) := min_le_right _ _
  have herror : A * ε ^ 2 ≤ η := by
    have hsq : ε ^ 2 ≤ ε := by nlinarith [hε.le, hε1]
    have hmul := (le_div_iff₀ (by linarith : 0 < A + 1)).1 hεA
    nlinarith
  obtain ⟨T, hTS, hTfin, hnet⟩ :=
    exists_finite_simultaneous_jet_net hK S hsm hsupp m hC hbound hε
  refine ⟨T, hTS, hTfin, ?_⟩
  intro f hf
  obtain ⟨g, hg, hfg⟩ := hnet f hf
  refine ⟨g, hg, (hres (fun x => f x - g x)
    ((hsm f hf).sub (hsm g (hTS hg)))
    ((tsupport_sub f g).trans (Set.union_subset (hsupp f hf) (hsupp g (hTS hg))))
    ε hε hfg).trans (ENNReal.ofReal_le_ofReal herror)⟩

end Critical2DKPZ.Analysis.Sobolev.Rellich

end
