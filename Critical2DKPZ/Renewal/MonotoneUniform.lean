/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic.Linarith

/-!
# Joint convergence for monotone two-parameter families

Pointwise convergence of coordinatewise monotone functions to a continuous limit
implies joint convergence as the cutoff tends to infinity and the parameters vary.
The neighborhood formulation gives local uniform convergence on compact subsets.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace Critical2DKPZ.Renewal

/-- A two-parameter monotone family with continuous pointwise limit converges jointly. -/
theorem tendsto_joint_of_eventually_monotone {F : ℕ → ℝ × ℝ → ℝ} {f : ℝ × ℝ → ℝ}
    {p : ℝ × ℝ} {K : Set (ℝ × ℝ)} (hK : K ∈ nhds p)
    (hmono : ∀ᶠ N : ℕ in atTop, MonotoneOn (F N) K)
    (hlim : ∀ q ∈ K, Tendsto (fun N => F N q) atTop (nhds (f q)))
    (hf : ContinuousAt f p) :
    Tendsto (fun z : ℕ × (ℝ × ℝ) => F z.1 z.2) (atTop ×ˢ nhds p) (nhds (f p)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hU : {q | dist (f q) (f p) < ε / 2} ∩ K ∈ nhds p :=
    Filter.inter_mem (hf (Metric.ball_mem_nhds _ (by positivity))) hK
  rw [nhds_prod_eq] at hU
  obtain ⟨A, hA, B, hB, hAB⟩ := Filter.mem_prod_iff.mp hU
  obtain ⟨a, b, hab, haA⟩ := mem_nhds_iff_exists_Ioo_subset.mp hA
  obtain ⟨c, d, hcd, hcB⟩ := mem_nhds_iff_exists_Ioo_subset.mp hB
  let lo : ℝ × ℝ := ((a + p.1) / 2, (c + p.2) / 2)
  let hi : ℝ × ℝ := ((p.1 + b) / 2, (p.2 + d) / 2)
  have hloA : lo.1 ∈ A := haA ⟨by dsimp only [lo]; linarith only [hab.1],
    by dsimp only [lo]; linarith only [hab.1, hab.2]⟩
  have hloB : lo.2 ∈ B := hcB ⟨by dsimp only [lo]; linarith only [hcd.1],
    by dsimp only [lo]; linarith only [hcd.1, hcd.2]⟩
  have hhiA : hi.1 ∈ A := haA ⟨by dsimp only [hi]; linarith only [hab.1, hab.2],
    by dsimp only [hi]; linarith only [hab.2]⟩
  have hhiB : hi.2 ∈ B := hcB ⟨by dsimp only [hi]; linarith only [hcd.1, hcd.2],
    by dsimp only [hi]; linarith only [hcd.2]⟩
  have hlo := hAB ⟨hloA, hloB⟩
  have hhi := hAB ⟨hhiA, hhiB⟩
  have hbox : Set.Icc lo hi ∈ nhds p := by
    have h1 : Icc lo.1 hi.1 ∈ nhds p.1 := Icc_mem_nhds
      (by dsimp only [lo]; linarith only [hab.1]) (by dsimp only [hi]; linarith only [hab.2])
    have h2 : Icc lo.2 hi.2 ∈ nhds p.2 := Icc_mem_nhds
      (by dsimp only [lo]; linarith only [hcd.1]) (by dsimp only [hi]; linarith only [hcd.2])
    rw [nhds_prod_eq]
    exact Filter.mem_prod_iff.mpr ⟨_, h1, _, h2, fun q hq => ⟨⟨hq.1.1, hq.2.1⟩, ⟨hq.1.2, hq.2.2⟩⟩⟩
  have hN := hmono.and ((Metric.tendsto_nhds.mp (hlim lo hlo.2) (ε / 2) (by positivity)).and
    (Metric.tendsto_nhds.mp (hlim hi hhi.2) (ε / 2) (by positivity)))
  have hq : K ∩ Icc lo hi ∈ nhds p := Filter.inter_mem hK hbox
  have hp := hN.prod_mk hq
  filter_upwards [hp] with z hz
  have hlower := hz.1.1 hlo.2 hz.2.1 hz.2.2.1
  have hupper := hz.1.1 hz.2.1 hhi.2 hz.2.2.2
  have hl := hz.1.2.1
  have hh := hz.1.2.2
  have hfl := hlo.1
  have hfh := hhi.1
  change dist (f lo) (f p) < ε / 2 at hfl
  change dist (f hi) (f p) < ε / 2 at hfh
  rw [Real.dist_eq, abs_lt] at hl hh hfl hfh ⊢
  constructor <;> linarith only [hl.1, hh.2, hfl.1, hfh.2, hlower, hupper]

end Critical2DKPZ.Renewal

end
