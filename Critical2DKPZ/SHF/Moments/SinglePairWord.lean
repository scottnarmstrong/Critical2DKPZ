/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordExpansion
public import Critical2DKPZ.SHF.Flow.SlabProductsCore
public import Critical2DKPZ.SHF.Moments.KernelLimit
public import Critical2DKPZ.SHF.Moments.PairBlockSpatialRenewalLimit
public import Critical2DKPZ.SHF.Moments.EntranceScaling
public import Critical2DKPZ.Analysis.Lattice.Sampling
public import Mathlib.Tactic
public import Critical2DKPZ.SHF.Moments.MovingFirstMoment
public import Critical2DKPZ.SHF.Moments.EntranceMoving
public import Critical2DKPZ.Renewal.CriticalWindow
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # The two-replica one-collision word -/

@[expose] public section

noncomputable section

open scoped BigOperators CompactlySupported

namespace Critical2DKPZ.SHF.Moments

open Polymer DeltaBose
open MeasureTheory
open Filter
open scoped Topology

private theorem tsum_eq_sum_piFinset_of_eq_zero {h : ℕ}
    (S : Fin h → Finset Site) (f : (Fin h → Site) → ℝ)
    (hzero : ∀ x, x ∉ Fintype.piFinset S → f x = 0) :
    ∑' x : Fin h → Site, f x = ∑ x ∈ Fintype.piFinset S, f x := by
  classical
  apply tsum_eq_sum
  intro x hx
  exact hzero x (by simpa using hx)

private theorem tsum_pair_rect_eq_sum {h : ℕ}
    (S T : Fin h → Finset Site) (f : (Fin h → Site) → (Fin h → Site) → ℝ)
    (hzeroS : ∀ x, x ∉ Fintype.piFinset S → ∀ y, f x y = 0)
    (hzeroT : ∀ x y, y ∉ Fintype.piFinset T → f x y = 0) :
    (∑' x : Fin h → Site, ∑' y : Fin h → Site, f x y) =
      ∑ x ∈ Fintype.piFinset S, ∑ y ∈ Fintype.piFinset T, f x y := by
  have hinner (x : Fin h → Site) :
      (∑' y : Fin h → Site, f x y) =
        ∑ y ∈ Fintype.piFinset T, f x y :=
    tsum_eq_sum_piFinset_of_eq_zero T (f x) (hzeroT x)
  rw [show (fun x : Fin h → Site => ∑' y : Fin h → Site, f x y) =
      fun x => ∑ y ∈ Fintype.piFinset T, f x y from funext hinner]
  apply tsum_eq_sum
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  exact hzeroS x (by simpa using hx) y

/-- The one-letter two-replica word, with its collision pair and free terminal
kernel written explicitly. -/
theorem blockWordKernel_pairTwo_explicit (σ : ℝ) (n : ℕ)
    (x y : Fin 2 → Site) :
    blockWordKernel σ [pairTwo] n x y =
      ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
        ∑' u : Fin 2 → Site, ∑' v : Fin 2 → Site,
          (if u 0 = u 1 ∧ v 0 = v 1 then (1 : ℝ) else 0) *
            (∏ i, srwKernel s (u i - x i)) * σ *
            Collision.spatialRenewal σ r (v 0 - u 0) *
            (∏ i, if i = 0 ∨ i = 1 then (1 : ℝ) else srwKernel r (v i - u i)) *
            (∏ i, srwKernel (n - s - r) (y i - v i)) := by
  rfl

/-- On a finite two-replica support, summing over pair-coincident configurations
is exactly a sum over the common collision site. -/
theorem sum_pairTwo_config_diagonal (S₀ S₁ : Finset Site)
    (f : (Fin 2 → Site) → ℝ) :
    (∑ u ∈ Fintype.piFinset
      (fun i : Fin 2 => if i = 0 then S₀ else S₁),
        if u 0 = u 1 then f u else 0) =
      ∑ z ∈ S₀ ∩ S₁, f (fun _ => z) := by
  classical
  let S : Finset (Fin 2 → Site) := Fintype.piFinset
    (fun i : Fin 2 => if i = 0 then S₀ else S₁)
  have hsum :
      (∑ u ∈ S, if u 0 = u 1 then f u else 0) =
        ∑ z ∈ S₀ ∩ S₁, f (fun _ => z) := by
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun u _ => u 0) ?_ ?_ ?_ ?_
    · intro u hu
      have hu' := (Finset.mem_filter.mp hu).1
      have hdiag := (Finset.mem_filter.mp hu).2
      have hp := Fintype.mem_piFinset.mp hu'
      have h₀ : u 0 ∈ S₀ := by simpa using hp 0
      have h₁ : u 1 ∈ S₁ := by simpa using hp 1
      exact Finset.mem_inter.mpr ⟨h₀, by simpa [hdiag.symm] using h₁⟩
    · intro u hu v hv huv
      funext i
      fin_cases i
      · exact huv
      · have hdiag := (Finset.mem_filter.mp hu).2
        have hdiagV := (Finset.mem_filter.mp hv).2
        calc
          u 1 = u 0 := hdiag.symm
          _ = v 0 := huv
          _ = v 1 := hdiagV
    · intro z hz
      have hz' := Finset.mem_inter.mp hz
      refine ⟨fun _ => z, ?_, rfl⟩
      apply Finset.mem_filter.mpr
      constructor
      · apply Fintype.mem_piFinset.mpr
        intro i
        fin_cases i
        · exact hz'.1
        · exact hz'.2
      · rfl
    · intro u hu
      have hdiag := (Finset.mem_filter.mp hu).2
      have hu_eq : u = fun _ => u 0 := by
        funext i
        fin_cases i
        · rfl
        · exact hdiag.symm
      rw [hu_eq]
  simpa only [S] using hsum

/-- Collapsing both replica diagonals turns a finite rectangular configuration
sum into a sum over the two common endpoint sites. -/
private theorem sum_pairTwo_config_diagonal_both
    (S₀ S₁ T₀ T₁ : Finset Site)
    (f : (Fin 2 → Site) → (Fin 2 → Site) → ℝ) :
    (∑ u ∈ Fintype.piFinset
        (fun i : Fin 2 => if i = 0 then S₀ else S₁),
      ∑ v ∈ Fintype.piFinset
        (fun i : Fin 2 => if i = 0 then T₀ else T₁),
        if u 0 = u 1 ∧ v 0 = v 1 then f u v else 0) =
      ∑ w ∈ T₀ ∩ T₁, ∑ z ∈ S₀ ∩ S₁,
        f (fun _ => z) (fun _ => w) := by
  classical
  let U : Fin 2 → Finset Site := fun i => if i = 0 then S₀ else S₁
  let V : Fin 2 → Finset Site := fun i => if i = 0 then T₀ else T₁
  have hU : U = fun i : Fin 2 =>
      if i = 0 then S₀ else S₁ := rfl
  have hV : V = fun i : Fin 2 =>
      if i = 0 then T₀ else T₁ := rfl
  have hcollapse (v : Fin 2 → Site) :
      (∑ u ∈ Fintype.piFinset U,
        if u 0 = u 1 ∧ v 0 = v 1 then f u v else 0) =
      ∑ z ∈ S₀ ∩ S₁, if v 0 = v 1 then f (fun _ => z) v else 0 := by
    have hpoint (u : Fin 2 → Site) :
        (if u 0 = u 1 ∧ v 0 = v 1 then f u v else 0) =
        (if u 0 = u 1 then if v 0 = v 1 then f u v else 0 else 0) := by
      by_cases hu : u 0 = u 1 <;> by_cases hv : v 0 = v 1 <;> simp [hu, hv]
    simp only [hU]
    simp_rw [hpoint]
    rw [sum_pairTwo_config_diagonal]
  calc
    _ = ∑ v ∈ Fintype.piFinset V, ∑ u ∈ Fintype.piFinset U,
          if u 0 = u 1 ∧ v 0 = v 1 then f u v else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ v ∈ Fintype.piFinset V,
          ∑ z ∈ S₀ ∩ S₁, if v 0 = v 1 then f (fun _ => z) v else 0 := by
      apply Finset.sum_congr rfl
      intro v hv
      exact hcollapse v
    _ = ∑ w ∈ T₀ ∩ T₁, ∑ z ∈ S₀ ∩ S₁,
          f (fun _ => z) (fun _ => w) := by
      have hfactor (v : Fin 2 → Site) :
          (∑ z ∈ S₀ ∩ S₁, if v 0 = v 1 then f (fun _ => z) v else 0) =
          if v 0 = v 1 then ∑ z ∈ S₀ ∩ S₁, f (fun _ => z) v else 0 := by
        by_cases hv : v 0 = v 1 <;> simp [hv]
      simp_rw [hfactor]
      rw [hV, sum_pairTwo_config_diagonal]



/-- For fixed free, collision, and terminal durations, both configuration
sums are finite and their collision diagonals reduce to common walk endpoints. -/
private theorem pairTwo_blockTerm_finite
    (σ : ℝ) (s r k : ℕ) (x y : Fin 2 → Site) :
    (∑' u : Fin 2 → Site, ∑' v : Fin 2 → Site,
      (if u 0 = u 1 ∧ v 0 = v 1 then (1 : ℝ) else 0) *
        (∏ i, srwKernel s (u i - x i)) * σ *
        Collision.spatialRenewal σ r (v 0 - u 0) *
        (∏ i, if i = 0 ∨ i = 1 then (1 : ℝ) else srwKernel r (v i - u i)) *
        (∏ i, srwKernel k (y i - v i))) =
      ∑ w ∈ Polymer.endpoints (y 0) k ∩ Polymer.endpoints (y 1) k,
        ∑ z ∈ Polymer.endpoints (x 0) s ∩ Polymer.endpoints (x 1) s,
          (srwKernel s (z - x 0) * srwKernel s (z - x 1)) * σ *
            Collision.spatialRenewal σ r (w - z) *
            (srwKernel k (y 0 - w) * srwKernel k (y 1 - w)) := by
  classical
  let S : Fin 2 → Finset Site := fun i => Polymer.endpoints (x i) s
  let T : Fin 2 → Finset Site := fun i => Polymer.endpoints (y i) k
  let H : (Fin 2 → Site) → (Fin 2 → Site) → ℝ := fun u v =>
    (∏ i, srwKernel s (u i - x i)) * σ *
      Collision.spatialRenewal σ r (v 0 - u 0) *
      (∏ i, if i = 0 ∨ i = 1 then (1 : ℝ) else srwKernel r (v i - u i)) *
      (∏ i, srwKernel k (y i - v i))
  let g : (Fin 2 → Site) → (Fin 2 → Site) → ℝ := fun u v =>
    if u 0 = u 1 ∧ v 0 = v 1 then H u v else 0
  have hpoint (u v : Fin 2 → Site) :
      (if u 0 = u 1 ∧ v 0 = v 1 then (1 : ℝ) else 0) *
        (∏ i, srwKernel s (u i - x i)) * σ *
        Collision.spatialRenewal σ r (v 0 - u 0) *
        (∏ i, if i = 0 ∨ i = 1 then (1 : ℝ) else srwKernel r (v i - u i)) *
        (∏ i, srwKernel k (y i - v i)) = g u v := by
    by_cases hdiag : u 0 = u 1 ∧ v 0 = v 1
    · simp [g, H, hdiag]
    · simp [g, hdiag]
  have hzeroS : ∀ u, u ∉ Fintype.piFinset S → ∀ v, g u v = 0 := by
    intro u hu v
    have hmiss : ∃ i : Fin 2, u i ∉ Polymer.endpoints (x i) s := by
      by_contra hn
      apply hu
      apply Fintype.mem_piFinset.mpr
      intro i
      by_contra hi
      exact hn ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hmiss
    have hk : srwKernel s (u i - x i) = 0 :=
      Polymer.srwKernel_eq_zero_of_not_mem s (x i) (u i) hi
    have hp : (∏ j, srwKernel s (u j - x j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hk])
    by_cases hdiag : u 0 = u 1 ∧ v 0 = v 1
    · simp only [g, ite_eq_left hdiag]
      dsimp [H]
      rw [hp]
      ring
    · simp [g, hdiag]
  have hzeroT : ∀ u v, v ∉ Fintype.piFinset T → g u v = 0 := by
    intro u v hv
    have hmiss : ∃ i : Fin 2, v i ∉ Polymer.endpoints (y i) k := by
      by_contra hn
      apply hv
      apply Fintype.mem_piFinset.mpr
      intro i
      by_contra hi
      exact hn ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hmiss
    have hnot : y i ∉ Polymer.endpoints (v i) k := by
      intro hmem
      exact hi (Critical2DKPZ.SHF.Flow.mem_endpoints_reverse hmem)
    have hk : srwKernel k (y i - v i) = 0 :=
      Polymer.srwKernel_eq_zero_of_not_mem k (v i) (y i) hnot
    have hp : (∏ j, srwKernel k (y j - v j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hk])
    by_cases hdiag : u 0 = u 1 ∧ v 0 = v 1
    · simp only [g, ite_eq_left hdiag]
      dsimp [H]
      rw [hp]
      ring
    · simp [g, hdiag]
  have hrect := tsum_pair_rect_eq_sum S T g hzeroS hzeroT
  calc
    _ = ∑' u : Fin 2 → Site, ∑' v : Fin 2 → Site, g u v := by
      apply tsum_congr
      intro u
      apply tsum_congr
      intro v
      exact hpoint u v
    _ = _ := hrect
  have hS : S = fun i : Fin 2 =>
      if i = 0 then Polymer.endpoints (x 0) s else Polymer.endpoints (x 1) s := by
    funext i
    fin_cases i <;> simp [S]
  have hT : T = fun i : Fin 2 =>
      if i = 0 then Polymer.endpoints (y 0) k else Polymer.endpoints (y 1) k := by
    funext i
    fin_cases i <;> simp [T]
  rw [hS, hT, sum_pairTwo_config_diagonal_both]
  simp [H, Fin.prod_univ_two]

/-- The complete one-letter two-particle word is a finite sum over free-run times
and the two common endpoint sites. -/
theorem blockWordKernel_pairTwo_endpointExpansion (σ : ℝ) (n : ℕ)
    (x y : Fin 2 → Site) :
    blockWordKernel σ [pairTwo] n x y =
      ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
        ∑ w ∈ Polymer.endpoints (y 0) (n - s - r) ∩
            Polymer.endpoints (y 1) (n - s - r),
          ∑ z ∈ Polymer.endpoints (x 0) s ∩ Polymer.endpoints (x 1) s,
            (srwKernel s (z - x 0) * srwKernel s (z - x 1)) * σ *
              Collision.spatialRenewal σ r (w - z) *
              (srwKernel (n - s - r) (y 0 - w) *
                srwKernel (n - s - r) (y 1 - w)) := by
  rw [blockWordKernel_pairTwo_explicit]
  simp_rw [pairTwo_blockTerm_finite]

/-- The future two-particle collision tail from a fixed collision site and time. -/
def pairTwoFutureTest (σ : ℝ) (n : ℕ) (y : Fin 2 → Site)
    (s : ℕ) (z : Site) : ℝ :=
  σ * ∑ r ∈ Finset.range (n - s + 1),
    ∑ w ∈ Polymer.endpoints (y 0) (n - s - r) ∩
        Polymer.endpoints (y 1) (n - s - r),
      Collision.spatialRenewal σ r (w - z) *
        (srwKernel (n - s - r) (y 0 - w) * srwKernel (n - s - r) (y 1 - w))





private theorem pairTwoFutureTest_factor (σ : ℝ) (n s : ℕ) (y : Fin 2 → Site)
    (z x₀ x₁ : Site) :
    ∑ r ∈ Finset.range (n - s + 1),
      ∑ w ∈ Polymer.endpoints (y 0) (n - s - r) ∩
          Polymer.endpoints (y 1) (n - s - r),
        (srwKernel s (z - x₀) * srwKernel s (z - x₁)) * σ *
          Collision.spatialRenewal σ r (w - z) *
          (srwKernel (n - s - r) (y 0 - w) * srwKernel (n - s - r) (y 1 - w)) =
      (srwKernel s (z - x₀) * srwKernel s (z - x₁)) *
        pairTwoFutureTest σ n y s z := by
  let q : ℝ := srwKernel s (z - x₀) * srwKernel s (z - x₁)
  calc
    _ = ∑ r ∈ Finset.range (n - s + 1),
        q * σ *
          ∑ w ∈ Polymer.endpoints (y 0) (n - s - r) ∩
              Polymer.endpoints (y 1) (n - s - r),
            Collision.spatialRenewal σ r (w - z) *
              (srwKernel (n - s - r) (y 0 - w) * srwKernel (n - s - r) (y 1 - w)) := by
      apply Finset.sum_congr rfl
      intro r hr
      calc
        _ = ∑ w ∈ Polymer.endpoints (y 0) (n - s - r) ∩
              Polymer.endpoints (y 1) (n - s - r),
              q * σ * (Collision.spatialRenewal σ r (w - z) *
                (srwKernel (n - s - r) (y 0 - w) * srwKernel (n - s - r) (y 1 - w))) := by
          apply Finset.sum_congr rfl
          intro w hw
          dsimp [q]
          ring
        _ = q * σ * ∑ w ∈ Polymer.endpoints (y 0) (n - s - r) ∩
              Polymer.endpoints (y 1) (n - s - r),
              Collision.spatialRenewal σ r (w - z) *
                (srwKernel (n - s - r) (y 0 - w) * srwKernel (n - s - r) (y 1 - w)) :=
          (Finset.mul_sum _ _ _).symm
    _ = q * (σ * ∑ r ∈ Finset.range (n - s + 1),
          ∑ w ∈ Polymer.endpoints (y 0) (n - s - r) ∩
              Polymer.endpoints (y 1) (n - s - r),
            Collision.spatialRenewal σ r (w - z) *
              (srwKernel (n - s - r) (y 0 - w) * srwKernel (n - s - r) (y 1 - w))) := by
      calc
        _ = ∑ r ∈ Finset.range (n - s + 1),
            q * (σ * ∑ w ∈ Polymer.endpoints (y 0) (n - s - r) ∩
                Polymer.endpoints (y 1) (n - s - r),
              Collision.spatialRenewal σ r (w - z) *
                (srwKernel (n - s - r) (y 0 - w) * srwKernel (n - s - r) (y 1 - w))) := by
          apply Finset.sum_congr rfl
          intro r hr
          dsimp [q]
          ring
        _ = q * ∑ r ∈ Finset.range (n - s + 1),
            σ * ∑ w ∈ Polymer.endpoints (y 0) (n - s - r) ∩
                Polymer.endpoints (y 1) (n - s - r),
              Collision.spatialRenewal σ r (w - z) *
                (srwKernel (n - s - r) (y 0 - w) * srwKernel (n - s - r) (y 1 - w)) :=
          (Finset.mul_sum _ _ _).symm
        _ = q * (σ * ∑ r ∈ Finset.range (n - s + 1),
              ∑ w ∈ Polymer.endpoints (y 0) (n - s - r) ∩
                  Polymer.endpoints (y 1) (n - s - r),
                Collision.spatialRenewal σ r (w - z) *
                  (srwKernel (n - s - r) (y 0 - w) * srwKernel (n - s - r) (y 1 - w))) := by
          congr 1
          exact (Finset.mul_sum _ _ _).symm
    _ = _ := by rw [pairTwoFutureTest]

/-- The one-letter two-particle word is a first collision entrance followed by the
resummed renewal block and the terminal free runs. -/
private theorem blockWordKernel_pairTwo_firstEntranceExpansion
    (σ : ℝ) (n : ℕ) (x y : Fin 2 → Site) :
    blockWordKernel σ [pairTwo] n x y =
      ∑ s ∈ Finset.Icc 1 n,
        collisionSlice s (x 0) (x 1) (pairTwoFutureTest σ n y s) := by
  rw [blockWordKernel_pairTwo_endpointExpansion]
  apply Finset.sum_congr rfl
  intro s hs
  let R := Finset.range (n - s + 1)
  let Z := Polymer.endpoints (x 0) s ∩ Polymer.endpoints (x 1) s
  have hcomm :
      (∑ r ∈ R, ∑ w ∈ Polymer.endpoints (y 0) (n - s - r) ∩
          Polymer.endpoints (y 1) (n - s - r),
        ∑ z ∈ Z,
          (srwKernel s (z - x 0) * srwKernel s (z - x 1)) * σ *
            Collision.spatialRenewal σ r (w - z) *
            (srwKernel (n - s - r) (y 0 - w) * srwKernel (n - s - r) (y 1 - w))) =
        ∑ z ∈ Z, ∑ r ∈ R,
          ∑ w ∈ Polymer.endpoints (y 0) (n - s - r) ∩
              Polymer.endpoints (y 1) (n - s - r),
            (srwKernel s (z - x 0) * srwKernel s (z - x 1)) * σ *
              Collision.spatialRenewal σ r (w - z) *
              (srwKernel (n - s - r) (y 0 - w) * srwKernel (n - s - r) (y 1 - w)) := by
    calc
      _ = ∑ r ∈ R, ∑ z ∈ Z,
          ∑ w ∈ Polymer.endpoints (y 0) (n - s - r) ∩
              Polymer.endpoints (y 1) (n - s - r),
            (srwKernel s (z - x 0) * srwKernel s (z - x 1)) * σ *
              Collision.spatialRenewal σ r (w - z) *
              (srwKernel (n - s - r) (y 0 - w) * srwKernel (n - s - r) (y 1 - w)) := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [Finset.sum_comm]
      _ = _ := by rw [Finset.sum_comm]
  calc
    _ = ∑ z ∈ Z, ∑ r ∈ R,
          ∑ w ∈ Polymer.endpoints (y 0) (n - s - r) ∩
              Polymer.endpoints (y 1) (n - s - r),
            (srwKernel s (z - x 0) * srwKernel s (z - x 1)) * σ *
              Collision.spatialRenewal σ r (w - z) *
              (srwKernel (n - s - r) (y 0 - w) * srwKernel (n - s - r) (y 1 - w)) := hcomm
    _ = ∑ z ∈ Z,
          (srwKernel s (z - x 0) * srwKernel s (z - x 1)) *
            pairTwoFutureTest σ n y s z := by
      apply Finset.sum_congr rfl
      intro z hz
      exact pairTwoFutureTest_factor σ n s y z (x 0) (x 1)
    _ = collisionSlice s (x 0) (x 1) (pairTwoFutureTest σ n y s) := by
      have hsubset : Z ⊆ Polymer.endpoints (x 0) s := Finset.inter_subset_left
      have hsum :
          (∑ z ∈ Z,
            srwKernel s (z - x 0) * srwKernel s (z - x 1) *
              pairTwoFutureTest σ n y s z) =
          ∑ z ∈ Polymer.endpoints (x 0) s,
            srwKernel s (z - x 0) * srwKernel s (z - x 1) *
              pairTwoFutureTest σ n y s z := by
        apply Finset.sum_subset hsubset
        intro z hz hznot
        have hz₁ : z ∉ Polymer.endpoints (x 1) s := by
          intro hmem
          exact hznot (Finset.mem_inter.mpr ⟨hz, hmem⟩)
        rw [Polymer.srwKernel_eq_zero_of_not_mem s (x 1) z hz₁]
        ring
      unfold collisionSlice
      exact hsum




/-- Compact support turns the tested two-particle word into a finite sum over its
start and terminal lattice configurations. -/
private theorem testedBlockWord_pairTwo_cellConfigExpansion (ϑ : ℝ) (N : ℕ)
    (s t : ℝ) (φ : Fin 2 → C_c(Plane × Plane, ℝ)) :
    testedBlockWord ϑ N s t φ [pairTwo] =
      ∑ x ∈ Fintype.piFinset
          (fun i : Fin 2 =>
            ((Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N (φ i)).toFinset.image
              Prod.fst)),
        ∑ y ∈ Fintype.piFinset
          (fun i : Fin 2 =>
            ((Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N (φ i)).toFinset.image
              Prod.snd)),
          (∏ i, cellTestWeight N (φ i) (x i) (y i)) *
            blockWordKernel (sigmaSq (criticalBeta ϑ N)) [pairTwo]
              (evenCeil (N * t) - evenCeil (N * s)) x y := by
  classical
  let Q : Fin 2 → Finset (Site × Site) := fun i =>
    (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N (φ i)).toFinset
  let S : Fin 2 → Finset Site := fun i => (Q i).image Prod.fst
  let T : Fin 2 → Finset Site := fun i => (Q i).image Prod.snd
  let G : (Fin 2 → Site) → (Fin 2 → Site) → ℝ := fun x y =>
    (∏ i, cellTestWeight N (φ i) (x i) (y i)) *
      blockWordKernel (sigmaSq (criticalBeta ϑ N)) [pairTwo]
        (evenCeil (N * t) - evenCeil (N * s)) x y
  have hzeroX (i : Fin 2) (a : Site) (ha : a ∉ S i) (b : Site) :
      cellTestWeight N (φ i) a b = 0 := by
    have hq : (a, b) ∉ Q i := by
      intro hmem
      exact ha (Finset.mem_image.mpr ⟨(a, b), hmem, rfl⟩)
    have hint : (∫ p in cell N a ×ˢ cell N b, φ i p) = 0 := by
      by_contra hne
      exact hq ((Critical2DKPZ.SHF.Flow.finite_support_cellPairTest
        N (φ i)).mem_toFinset.mpr hne)
    simp [cellTestWeight, hint]
  have hzeroY (i : Fin 2) (b : Site) (hb : b ∉ T i) (a : Site) :
      cellTestWeight N (φ i) a b = 0 := by
    have hq : (a, b) ∉ Q i := by
      intro hmem
      exact hb (Finset.mem_image.mpr ⟨(a, b), hmem, rfl⟩)
    have hint : (∫ p in cell N a ×ˢ cell N b, φ i p) = 0 := by
      by_contra hne
      exact hq ((Critical2DKPZ.SHF.Flow.finite_support_cellPairTest
        N (φ i)).mem_toFinset.mpr hne)
    simp [cellTestWeight, hint]
  have hzeroS : ∀ x, x ∉ Fintype.piFinset S → ∀ y, G x y = 0 := by
    intro x hx y
    have hmiss : ∃ i : Fin 2, x i ∉ S i := by
      by_contra hn
      apply hx
      apply Fintype.mem_piFinset.mpr
      intro i
      by_contra hi
      exact hn ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hmiss
    have hw := hzeroX i (x i) hi (y i)
    dsimp [G]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hw]
    simp
  have hzeroT : ∀ x y, y ∉ Fintype.piFinset T → G x y = 0 := by
    intro x y hy
    have hmiss : ∃ i : Fin 2, y i ∉ T i := by
      by_contra hn
      apply hy
      apply Fintype.mem_piFinset.mpr
      intro i
      by_contra hi
      exact hn ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hmiss
    have hw := hzeroY i (y i) hi (x i)
    dsimp [G]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hw]
    simp
  have hrect := tsum_pair_rect_eq_sum S T G hzeroS hzeroT
  unfold testedBlockWord
  calc
    _ = ∑ x ∈ Fintype.piFinset S, ∑ y ∈ Fintype.piFinset T,
          (∏ i, cellTestWeight N (φ i) (x i) (y i)) *
            blockWordKernel (sigmaSq (criticalBeta ϑ N)) [pairTwo]
              (evenCeil (N * t) - evenCeil (N * s)) x y := hrect


/-- Expand the tested singleton pair word by its first collision entrance. -/
theorem testedBlockWord_pairTwo_firstEntranceExpansion (ϑ : ℝ) (N : ℕ)
    (s t : ℝ) (φ : Fin 2 → C_c(Plane × Plane, ℝ)) :
    testedBlockWord ϑ N s t φ [pairTwo] =
      ∑ x ∈ Fintype.piFinset
          (fun i : Fin 2 =>
            ((Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N (φ i)).toFinset.image
              Prod.fst)),
        ∑ y ∈ Fintype.piFinset
          (fun i : Fin 2 =>
            ((Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N (φ i)).toFinset.image
              Prod.snd)),
          (∏ i, cellTestWeight N (φ i) (x i) (y i)) *
            ∑ q ∈ Finset.Icc 1
                (evenCeil (N * t) - evenCeil (N * s)),
              collisionSlice q (x 0) (x 1)
                (pairTwoFutureTest (sigmaSq (criticalBeta ϑ N))
                  (evenCeil (N * t) - evenCeil (N * s)) y q) := by
  rw [testedBlockWord_pairTwo_cellConfigExpansion]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [blockWordKernel_pairTwo_firstEntranceExpansion]













private theorem sum_piFinset_eq_prod_sums_two
    (S : Fin 2 → Finset Site) (f : Fin 2 → Site → ℝ) :
    (∑ x ∈ Fintype.piFinset S, ∏ i, f i (x i)) =
      ∏ i, ∑ a ∈ S i, f i a := by
  classical
  let Sub : Fin 2 → Type := fun i => {a : Site // a ∈ S i}
  let encode : (∀ i, Sub i) → Fin 2 → Site := fun x i => (x i).1
  have himage : Finset.image encode Finset.univ = Fintype.piFinset S := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · rintro ⟨y, rfl⟩ i
      exact (y i).2
    · intro hx
      exact ⟨fun i => ⟨x i, hx i⟩, by funext i; rfl⟩
  have hinj : Function.Injective encode := by
    intro x y hxy
    funext i
    apply Subtype.ext
    exact congrFun hxy i
  calc
    _ = ∑ x ∈ Finset.image encode Finset.univ, ∏ i, f i (x i) := by rw [← himage]
    _ = ∑ x : (∀ i, Sub i), ∏ i, f i (x i).1 := by
      rw [Finset.sum_image (fun x hx y hy hxy => hinj hxy)]
    _ = ∏ i, ∑ a : Sub i, f i a.1 := by
      symm
      exact Fintype.prod_sum (f := fun (i : Fin 2) (a : Sub i) => f i a.1)
    _ = ∏ i, ∑ a ∈ S i, f i a := by
      apply Finset.prod_congr rfl
      intro i hi
      exact Finset.sum_coe_sort (S i) (fun a => f i a)

/-- One replica's terminal cell-test profile at a fixed collision site. -/
def pairTwoFutureTerminalCellFactor (N k : ℕ)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (x : Fin 2 → Site)
    (w : Site) (i : Fin 2) : ℝ :=
  ∑ y ∈ ((Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N (φ i)).toFinset.image
      Prod.snd),
    (if w ∈ Polymer.endpoints y k then
      cellTestWeight N (φ i) (x i) y * srwKernel k (y - w) else 0)

/-- At a fixed collision site and terminal duration, averaging the two
terminal endpoints factors into the product of the two one-replica cell
profiles. The endpoint reachability constraints factor as well. -/
theorem pairTwoFutureTerminalCellFactorization (N k : ℕ)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (x : Fin 2 → Site) (w : Site) :
    (∑ y ∈ Fintype.piFinset (fun i : Fin 2 =>
        ((Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N (φ i)).toFinset.image
          Prod.snd)),
      (∏ i, cellTestWeight N (φ i) (x i) (y i)) *
        (if w ∈ Polymer.endpoints (y 0) k ∩ Polymer.endpoints (y 1) k then
          srwKernel k (y 0 - w) * srwKernel k (y 1 - w) else 0)) =
      ∏ i : Fin 2, pairTwoFutureTerminalCellFactor N k φ x w i := by
  classical
  let Y : Fin 2 → Finset Site := fun i =>
    ((Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N (φ i)).toFinset.image Prod.snd)
  let f : Fin 2 → Site → ℝ := fun i y =>
    if w ∈ Polymer.endpoints y k then
      cellTestWeight N (φ i) (x i) y * srwKernel k (y - w) else 0
  have hterm (y : Fin 2 → Site) :
      (∏ i, cellTestWeight N (φ i) (x i) (y i)) *
        (if w ∈ Polymer.endpoints (y 0) k ∩ Polymer.endpoints (y 1) k then
          srwKernel k (y 0 - w) * srwKernel k (y 1 - w) else 0) =
      ∏ i, f i (y i) := by
    by_cases h₀ : w ∈ Polymer.endpoints (y 0) k <;>
      by_cases h₁ : w ∈ Polymer.endpoints (y 1) k <;>
      simp [f, Finset.mem_inter, h₀, h₁, Fin.prod_univ_two]; ring
  calc
    _ = ∑ y ∈ Fintype.piFinset Y, ∏ i, f i (y i) := by
      apply Finset.sum_congr rfl
      intro y hy
      exact hterm y
    _ = ∏ i : Fin 2, ∑ a ∈ Y i, f i a :=
      sum_piFinset_eq_prod_sums_two Y f
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i hi
      simp [Y, f, pairTwoFutureTerminalCellFactor]





end Critical2DKPZ.SHF.Moments

end
