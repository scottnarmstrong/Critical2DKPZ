/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ContinuousTensorAlgebra
import Mathlib.Algebra.BigOperators.Fin

/-! # Finite presentations of continuous tensor approximations

Span induction gives actual finite endpoint families for every member of
the tensor algebra. Scalars are absorbed into the first endpoint, and
addition concatenates the finite families.
-/

@[expose] public noncomputable section

namespace Critical2DKPZ.SHF.Tsai

/-- Every continuous tensor-span element has a finite sum presentation. -/
theorem exists_sum_continuousTensorTest_of_mem_span {f : C(Plane × Plane, ℝ)}
    (hf : f ∈ continuousTensorSpan) :
    ∃ r : ℕ, ∃ g g' : Fin r → C(Plane, ℝ), f = ∑ b, continuousTensorTest (g b) (g' b) := by
  classical
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨⟨g, g'⟩, rfl⟩ := hf
    exact ⟨1, (fun _ => g), (fun _ => g'), by simp⟩
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | add f h hf hh ihf ihh =>
    obtain ⟨m, g, g', hfg⟩ := ihf
    obtain ⟨n, a, a', hha⟩ := ihh
    refine ⟨m + n, Fin.addCases g a, Fin.addCases g' a', ?_⟩
    rw [Fin.sum_univ_add]
    simpa only [Fin.addCases_left, Fin.addCases_right] using congrArg₂ (· + ·) hfg hha
  | smul c f hf ih =>
    obtain ⟨m, g, g', hfg⟩ := ih
    refine ⟨m, (fun i => c • g i), g', ?_⟩
    rw [hfg, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ext p
    simp only [continuousTensorTest, ContinuousMap.coe_mk, ContinuousMap.smul_apply, smul_eq_mul]
    ring

/-- Compact-window approximation by explicit finite sums of continuous endpoint tests. -/
theorem exists_continuousTensorSum_approx (f : C(Plane × Plane, ℝ))
    {K : Set (Plane × Plane)} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℕ, ∃ g g' : Fin r → C(Plane, ℝ),
      ∀ p ∈ K, |(∑ b, g b p.1 * g' b p.2) - f p| < ε := by
  obtain ⟨a, ha, happrox⟩ := exists_continuousTensorSpan_approx f hK hε
  obtain ⟨r, g, g', rfl⟩ := exists_sum_continuousTensorTest_of_mem_span ha
  exact ⟨r, g, g', by simpa only [ContinuousMap.sum_apply, continuousTensorTest, ContinuousMap.coe_mk] using happrox⟩

end Critical2DKPZ.SHF.Tsai

end
