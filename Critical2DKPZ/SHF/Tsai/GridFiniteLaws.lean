/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.CommonGridFactors
public import Critical2DKPZ.SHF.Tsai.ConsecutiveLaws

/-! # Finite-dimensional laws on a common grid

Every requested grid interval is the same measurable function of the full
fine-block tuple for both processes. Equality of elementary block laws then
passes through the resulting finite vector of coarse-interval factors.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set

namespace Critical2DKPZ.SHF.Tsai

/-- Equal interval marginals determine the joint law of arbitrary strict subintervals of a common finite grid. -/
theorem isDenseSHF_grid_fdd_eq_of_law_eq {θ : ℝ} {D : Set ℝ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane))
    (hZ : IsDenseSHF θ D P Z) (hZ' : IsDenseSHF θ D P' Z')
    (hlaw : ∀ s ∈ D, ∀ t ∈ D, s < t → P.map (Z s t) = P'.map (Z' s t))
    (m : ℕ) (t : Fin (m + 1) → ℝ) (ht : StrictMono t) (htD : ∀ i, t i ∈ D)
    (k : ℕ) (a b : Fin k → Fin (m + 1)) (hab : ∀ i, a i < b i) :
    P.map (fun ω i => Z (t (a i)) (t (b i)) ω) =
      P'.map (fun ω i => Z' (t (a i)) (t (b i)) ω) := by
  classical
  let T (n : ℕ) := t ⟨min n m, by omega⟩
  have hTval (i : Fin (m + 1)) : T i = t i := by
    dsimp only [T]
    simp only [Nat.min_eq_left (Nat.le_of_lt_succ i.is_lt)]
  have hTon : StrictMonoOn T (Iic m) := by
    intro i hi j hj hij
    change i ≤ m at hi
    change j ≤ m at hj
    dsimp only [T]
    simp only [Nat.min_eq_left hi, Nat.min_eq_left hj]
    exact ht hij
  have hTD (n : ℕ) (hn : n ≤ m) : T n ∈ D := by
    change T (⟨n, by omega⟩ : Fin (m + 1)) ∈ D
    rw [hTval]
    exact htD _
  have hFactor (i : Fin k) := exists_common_grid_interval_factor P P' Z Z' hZ hZ' hlaw
    m T hTon hTD (a := a i) (b := b i) (hab i) (Nat.le_of_lt_succ (b i).is_lt)
  choose φ hφ _hφlf hφAE hφAE' using hFactor
  let Φ (μ : Fin m → Measure (Plane × Plane)) (i : Fin k) := φ i μ
  have hΦ : Measurable Φ := Measurable.of_eval hφ
  have hfine (Y : ℝ → ℝ → Measure (Plane × Plane)) :
      (fun j : Fin m => Y (T j) (T (j + 1))) =
        fun j : Fin m => Y (t j.castSucc) (t j.succ) := by
    funext j
    rw [show T (j : ℕ) = t j.castSucc from hTval j.castSucc,
      show T ((j : ℕ) + 1) = t j.succ from hTval j.succ]
  have hAE (i : Fin k) : Z (t (a i)) (t (b i)) =ᵐ[P]
      fun ω => φ i (fun j : Fin m => Z (t j.castSucc) (t j.succ) ω) := by
    filter_upwards [hφAE i] with ω hω
    rw [hTval, hTval, hfine (fun s t => Z s t ω)] at hω
    exact hω
  have hAE' (i : Fin k) : Z' (t (a i)) (t (b i)) =ᵐ[P']
      fun ω => φ i (fun j : Fin m => Z' (t j.castSucc) (t j.succ) ω) := by
    filter_upwards [hφAE' i] with ω hω
    rw [hTval, hTval, hfine (fun s t => Z' s t ω)] at hω
    exact hω
  have hVec : (fun ω i => Z (t (a i)) (t (b i)) ω) =ᵐ[P]
      Φ ∘ (fun ω j => Z (t j.castSucc) (t j.succ) ω) := by
    filter_upwards [ae_all_iff.2 hAE] with ω hω
    funext i
    exact hω i
  have hVec' : (fun ω i => Z' (t (a i)) (t (b i)) ω) =ᵐ[P']
      Φ ∘ (fun ω j => Z' (t j.castSucc) (t j.succ) ω) := by
    filter_upwards [ae_all_iff.2 hAE'] with ω hω
    funext i
    exact hω i
  have hm : Measurable (fun ω (j : Fin m) => Z (t j.castSucc) (t j.succ) ω) :=
    Measurable.of_eval fun j => (hZ.1 _ (htD j.castSucc) _ (htD j.succ) (ht j.castSucc_lt_succ)).1
  have hm' : Measurable (fun ω (j : Fin m) => Z' (t j.castSucc) (t j.succ) ω) :=
    Measurable.of_eval fun j => (hZ'.1 _ (htD j.castSucc) _ (htD j.succ) (ht j.castSucc_lt_succ)).1
  have hFineLaw := isDenseSHF_consecutive_law_eq_of_law_eq θ D P P' Z Z' hZ hZ' hlaw m t ht htD
  have hMap := congrArg (fun ν : Measure (Fin m → Measure (Plane × Plane)) => ν.map Φ) hFineLaw
  rw [Measure.map_map hΦ hm, Measure.map_map hΦ hm'] at hMap
  rw [Measure.map_congr hVec, Measure.map_congr hVec']
  exact hMap

end Critical2DKPZ.SHF.Tsai

end
