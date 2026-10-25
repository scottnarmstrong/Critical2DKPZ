/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.LocalizedEnergy
public import Critical2DKPZ.Analysis.Sobolev.Topology

/-! Every sufficiently large cutoff in the countable exhaustion preserves the localized negative Sobolev energy at a fixed test function. -/

public section

open Filter MeasureTheory TopologicalSpace

open scoped Distributions
open scoped Topology

namespace Critical2DKPZ.Analysis.Sobolev

/-- Cutting off a distribution by the countable exhaustion eventually preserves its local negative Sobolev energy at any fixed test function. -/
theorem exists_eventually_localizer_energy_eq (a : ℝ) (T : Distr) (χ : TestFn) :
    ∃ N : ℕ, ∀ n ≥ N,
      localNegSobolevSq a (localizeDistr (localizer n) T) χ = localNegSobolevSq a T χ := by
  obtain ⟨N, hN⟩ := exists_testFnMul_localizer_eq χ
  refine ⟨N, fun n hn => ?_⟩
  have hF : localizedFourier (localizeDistr (localizer n) T) χ =
      localizedFourier T χ := by
    funext ξ
    rw [localizedFourier_localizeDistr, hN n hn]
  have hsum (ξ : Plane) :
      (localizeDistr (localizer n) T (χ.mulCos ξ)) ^ 2 +
        (localizeDistr (localizer n) T (χ.mulSin ξ)) ^ 2 =
      (T (χ.mulCos ξ)) ^ 2 + (T (χ.mulSin ξ)) ^ 2 := by
    have hnorm := congrArg norm (congrFun hF ξ)
    have hnorm2 := congrArg (fun z : ℝ => z ^ 2) hnorm
    rw [norm_localizedFourier_sq, norm_localizedFourier_sq] at hnorm2
    exact hnorm2
  unfold localNegSobolevSq
  congr 1
  apply lintegral_congr
  intro ξ
  rw [hsum ξ]

/-- A distribution has finite local negative Sobolev energy if and only if every cutoff in the countable exhaustion yields a distribution with that property. -/
theorem memLocalNegSobolev_iff_all_localizer_localizations
    (a : ℝ) (T : Distr) :
    MemLocalNegSobolev a T ↔
      ∀ n : ℕ, MemLocalNegSobolev a (localizeDistr (localizer n) T) := by
  constructor
  · intro hT n χ
    rw [localNegSobolevSq_localizeDistr]
    exact hT (testFnMul (localizer n) χ)
  · intro hlocal χ
    obtain ⟨N, hN⟩ := exists_testFnMul_localizer_eq χ
    have hfinite := hlocal N χ
    rw [localNegSobolevSq_localizeDistr] at hfinite
    rw [hN N le_rfl] at hfinite
    exact hfinite

/-- Convergence after multiplication by every cutoff in the countable exhaustion implies convergence in the local negative Sobolev topology. -/
theorem tendsto_locNegSobolevTop_of_tendsto_localizer_differences
    {ι : Type*} {l : Filter ι} {a : ℝ}
    {S : ι → LocNegSobolevTop a} {T : LocNegSobolevTop a}
    (h : ∀ n : ℕ, Tendsto
      (fun i => (localizeDistr (localizer n) ((S i).toDistr - T.toDistr) :
        LocNegSobolevTop a))
      l (@nhds (LocNegSobolevTop a) (LocNegSobolevTop.topologicalSpace a)
        ((0 : Distr) : LocNegSobolevTop a))) :
    Tendsto S l (𝓝 T) := by
  apply tendsto_locNegSobolevTop_of_localNegSobolevSq
  intro χ
  obtain ⟨N, hN⟩ := exists_testFnMul_localizer_eq χ
  have hlocal := tendsto_localNegSobolevSq_of_locNegSobolevTop (h N) χ
  have hlocal' : Tendsto (fun i => localNegSobolevSq a
      (localizeDistr (localizer N) ((S i).toDistr - T.toDistr)) χ) l (𝓝 0) := by
    simpa only [LocNegSobolevTop.toDistr, sub_zero] using hlocal
  have hEq : (fun i => localNegSobolevSq a
      ((S i).toDistr - T.toDistr) χ) =
      fun i => localNegSobolevSq a
        (localizeDistr (localizer N) ((S i).toDistr - T.toDistr)) χ := by
    funext i
    rw [localNegSobolevSq_localizeDistr, hN N le_rfl]
  exact hEq ▸ hlocal'

/-- Convergence in the local negative Sobolev topology is equivalent to convergence after multiplication by every cutoff in the countable exhaustion. -/
theorem tendsto_locNegSobolevTop_iff_tendsto_localizer_differences
    {ι : Type*} {l : Filter ι} {a : ℝ}
    {S : ι → LocNegSobolevTop a} {T : LocNegSobolevTop a} :
    Tendsto S l (𝓝 T) ↔ ∀ n : ℕ, Tendsto
      (fun i => (localizeDistr (localizer n) ((S i).toDistr - T.toDistr) :
        LocNegSobolevTop a))
      l (@nhds (LocNegSobolevTop a) (LocNegSobolevTop.topologicalSpace a)
        ((0 : Distr) : LocNegSobolevTop a)) := by
  constructor
  · intro h n
    let D : ι → Distr := fun i => (S i).toDistr - T.toDistr
    let U : ι → LocNegSobolevTop a :=
      fun i => localizeDistr (localizer n) (D i)
    change Tendsto U l _
    apply tendsto_locNegSobolevTop_of_localNegSobolevSq
    intro ψ
    have hψ := tendsto_localNegSobolevSq_of_locNegSobolevTop h
      (testFnMul (localizer n) ψ)
    have hEq :
        (fun i => localNegSobolevSq a (localizeDistr (localizer n) (D i)) ψ) =
        (fun i => localNegSobolevSq a (D i)
          (testFnMul (localizer n) ψ)) := by
      funext i
      exact localNegSobolevSq_localizeDistr a (localizer n) ψ
        (D i)
    have hlocalized : Tendsto
        (fun i => localNegSobolevSq a (localizeDistr (localizer n) (D i)) ψ)
        l (𝓝 0) := hEq ▸ hψ
    simpa only [U, LocNegSobolevTop.toDistr, sub_zero] using hlocalized
  · exact tendsto_locNegSobolevTop_of_tendsto_localizer_differences

end Critical2DKPZ.Analysis.Sobolev

end
