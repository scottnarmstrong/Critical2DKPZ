/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.EntranceDiagonalLimit
import Mathlib.Tactic

/-! # Short entrance strips for two starts with one limiting center -/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Moments

/-- A mixed collision slice is controlled by the average of the two diagonal slices
with the absolute test. This is the pointwise inequality `ab ≤ (a²+b²)/2`
applied to the two walk kernels. -/
theorem collisionSlice_abs_le_diagonal_average (r : ℕ) (a b : Site) (f : Site → ℝ) :
    |collisionSlice r a b f| ≤
      (collisionSlice r a a (fun z => |f z|) +
        collisionSlice r b b (fun z => |f z|)) / 2 := by
  classical
  let Ea := Polymer.endpoints a r
  let Eb := Polymer.endpoints b r
  let E := Ea ∪ Eb
  let qa : Site → ℝ := fun z => srwKernel r (z - a)
  let qb : Site → ℝ := fun z => srwKernel r (z - b)
  have hqa (z : Site) : 0 ≤ qa z := by
    exact Critical2DKPZ.srwKernel_nonneg _ _
  have hqb (z : Site) : 0 ≤ qb z := by
    exact Critical2DKPZ.srwKernel_nonneg _ _
  have hqa_zero (z : Site) (hz : z ∈ E) (hza : z ∉ Ea) : qa z = 0 := by
    exact Polymer.srwKernel_eq_zero_of_not_mem r a z (by simpa [Ea] using hza)
  have hqb_zero (z : Site) (hz : z ∈ E) (hzb : z ∉ Eb) : qb z = 0 := by
    exact Polymer.srwKernel_eq_zero_of_not_mem r b z (by simpa [Eb] using hzb)
  have hmixed : collisionSlice r a b f =
      ∑ z ∈ E, qa z * qb z * f z := by
    change (∑ z ∈ Ea, qa z * qb z * f z) = _
    apply Finset.sum_subset Finset.subset_union_left (by
      intro z hz hnot
      change qa z * qb z * f z = 0
      rw [hqa_zero z hz hnot]
      ring)
  have hdiagA : collisionSlice r a a (fun z => |f z|) =
      ∑ z ∈ E, qa z ^ 2 * |f z| := by
    change (∑ z ∈ Ea, qa z * qa z * |f z|) = _
    calc
      _ = ∑ z ∈ E, qa z * qa z * |f z| :=
        Finset.sum_subset Finset.subset_union_left (by
          intro z hz hnot
          change qa z * qa z * |f z| = 0
          rw [hqa_zero z hz hnot]
          simp)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [pow_two]
  have hdiagB : collisionSlice r b b (fun z => |f z|) =
      ∑ z ∈ E, qb z ^ 2 * |f z| := by
    change (∑ z ∈ Eb, qb z * qb z * |f z|) = _
    calc
      _ = ∑ z ∈ E, qb z * qb z * |f z| :=
        Finset.sum_subset Finset.subset_union_right (by
          intro z hz hnot
          change qb z * qb z * |f z| = 0
          rw [hqb_zero z hz hnot]
          simp)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [pow_two]
  calc
    |collisionSlice r a b f| ≤
        ∑ z ∈ E, |qa z * qb z * f z| := by rw [hmixed]; exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ z ∈ E, qa z * qb z * |f z| := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [abs_mul, abs_of_nonneg (mul_nonneg (hqa z) (hqb z))]
    _ ≤ ∑ z ∈ E, (qa z ^ 2 * |f z| + qb z ^ 2 * |f z|) / 2 :=
      Finset.sum_le_sum fun z hz => by
        have hquad : 0 ≤ qa z ^ 2 + qb z ^ 2 - 2 * qa z * qb z := by
          nlinarith [sq_nonneg (qa z - qb z)]
        have := mul_nonneg hquad (abs_nonneg (f z))
        nlinarith
    _ = (collisionSlice r a a (fun z => |f z|) +
        collisionSlice r b b (fun z => |f z|)) / 2 := by
      calc
        _ = ((∑ z ∈ E, qa z ^ 2 * |f z|) +
            (∑ z ∈ E, qb z ^ 2 * |f z|)) / 2 := by
          rw [← Finset.sum_div, Finset.sum_add_distrib]
        _ = _ := by rw [← hdiagA, ← hdiagB]

/-- The finite-time entrance with two starts is bounded by the average of the
corresponding diagonal entrances tested against `|F|`. -/
theorem collisionEntrance_abs_le_diagonal_average (N lo hi : ℕ) (a b : Site)
    (F : ℝ × Plane → ℝ) :
    |collisionEntrance N lo hi a b F| ≤
      (collisionEntrance N lo hi a a (fun p => |F p|) +
        collisionEntrance N lo hi b b (fun p => |F p|)) / 2 := by
  unfold collisionEntrance
  calc
    |∑ r ∈ Finset.Icc lo hi,
        collisionSlice r a b (fun z => F ((r : ℝ) / N, latticeRepresentative N z))| ≤
      ∑ r ∈ Finset.Icc lo hi,
        |collisionSlice r a b (fun z => F ((r : ℝ) / N, latticeRepresentative N z))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ Finset.Icc lo hi,
        (collisionSlice r a a (fun z => |F ((r : ℝ) / N, latticeRepresentative N z)|) +
          collisionSlice r b b (fun z => |F ((r : ℝ) / N, latticeRepresentative N z)|)) / 2 :=
      Finset.sum_le_sum fun r hr => collisionSlice_abs_le_diagonal_average r a b _
    _ = _ := by
      calc
        _ = ((∑ r ∈ Finset.Icc lo hi,
            collisionSlice r a a (fun z => |F ((r : ℝ) / N, latticeRepresentative N z)|)) +
            (∑ r ∈ Finset.Icc lo hi,
              collisionSlice r b b (fun z => |F ((r : ℝ) / N, latticeRepresentative N z)|))) / 2 := by
          rw [← Finset.sum_div, Finset.sum_add_distrib]
        _ = _ := rfl
  

private theorem collisionEntrance_diagonal_nonneg (N K : ℕ) (a : Site)
    (F : ℝ × Plane → ℝ) (hF : ∀ p, 0 ≤ F p) :
    0 ≤ collisionEntrance N 0 K a a F := by
  unfold collisionEntrance
  apply Finset.sum_nonneg
  intro r hr
  exact collisionSlice_nonneg r a a (fun z => hF _)

private theorem collisionEntrance_diagonal_mono (N K K' : ℕ) (a : Site)
    (F : ℝ × Plane → ℝ) (hF : ∀ p, 0 ≤ F p) (hKK' : K ≤ K') :
    collisionEntrance N 0 K a a F ≤ collisionEntrance N 0 K' a a F := by
  unfold collisionEntrance
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc_right hKK') (by
      intro r hr hnot
      exact collisionSlice_nonneg r a a (fun z => hF _))

/-- A linearly vanishing test has a negligible short entrance strip when both
microscopic starts approach its limiting center at rate `o(1/log N)`. The
starts need not coincide. -/
theorem eventually_collisionEntrance_coalescing_short_strip_small
    (aN bN : ℕ → Site) (c : Plane)
    (hcenterA : Tendsto
      (fun N : ℕ => ‖latticeRepresentative N (aN N) - c‖ *
        Real.log ((N : ℝ) + 2)) atTop (𝓝 0))
    (hcenterB : Tendsto
      (fun N : ℕ => ‖latticeRepresentative N (bN N) - c‖ *
        Real.log ((N : ℝ) + 2)) atTop (𝓝 0))
    (F : ℝ × Plane → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hF : ∀ u x, 0 ≤ u → |F (u, x)| ≤ L * (u + ‖x - c‖))
    (δmax : ℝ) (hδmax : 0 < δmax) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ δ ≤ δmax ∧ ∀ᶠ N : ℕ in atTop,
      |collisionEntrance N 0 (evenCeil ((N : ℝ) * δ)) (aN N) (bN N) F| < ε := by
  intro ε hε
  let Fabs : ℝ × Plane → ℝ := fun p => |F p|
  have hFabs : ∀ u x, 0 ≤ u → |Fabs (u, x)| ≤ L * (u + ‖x - c‖) := by
    intro u x hu
    simp only [Fabs, abs_abs]
    exact hF u x hu
  obtain ⟨δA, hδA, hδAmax, hsmallA⟩ :=
    eventually_collisionEntrance_diagonal_short_strip_small aN c L hL Fabs hFabs
      hcenterA δmax hδmax ε hε
  obtain ⟨δB, hδB, hδBmax, hsmallB⟩ :=
    eventually_collisionEntrance_diagonal_short_strip_small bN c L hL Fabs hFabs
      hcenterB δmax hδmax ε hε
  let δ := min δA δB
  have hδ : 0 < δ := by dsimp [δ]; exact lt_min hδA hδB
  have hδmax' : δ ≤ δmax := by
    dsimp [δ]
    exact min_le_iff.mpr (Or.inl hδAmax)
  have hδA' : δ ≤ δA := min_le_left _ _
  have hδB' : δ ≤ δB := min_le_right _ _
  have hsmall := hsmallA.and hsmallB
  refine ⟨δ, hδ, hδmax', ?_⟩
  filter_upwards [hsmall] with N hN
  have hKmonoA : evenCeil ((N : ℝ) * δ) ≤ evenCeil ((N : ℝ) * δA) := by
    apply Critical2DKPZ.evenCeil_mono
    exact mul_le_mul_of_nonneg_left hδA' (Nat.cast_nonneg N)
  have hKmonoB : evenCeil ((N : ℝ) * δ) ≤ evenCeil ((N : ℝ) * δB) := by
    apply Critical2DKPZ.evenCeil_mono
    exact mul_le_mul_of_nonneg_left hδB' (Nat.cast_nonneg N)
  have hFA : ∀ p, 0 ≤ Fabs p := by intro p; exact abs_nonneg _
  have hdiagA0 := collisionEntrance_diagonal_nonneg N
    (evenCeil ((N : ℝ) * δ)) (aN N) Fabs hFA
  have hdiagB0 := collisionEntrance_diagonal_nonneg N
    (evenCeil ((N : ℝ) * δ)) (bN N) Fabs hFA
  have hdiagA := collisionEntrance_diagonal_mono N
    (evenCeil ((N : ℝ) * δ)) (evenCeil ((N : ℝ) * δA)) (aN N) Fabs hFA hKmonoA
  have hdiagB := collisionEntrance_diagonal_mono N
    (evenCeil ((N : ℝ) * δ)) (evenCeil ((N : ℝ) * δB)) (bN N) Fabs hFA hKmonoB
  have hsmallDiagA : collisionEntrance N 0 (evenCeil ((N : ℝ) * δ))
      (aN N) (aN N) Fabs < ε := by
    have h := hN.1
    have hnonneg := collisionEntrance_diagonal_nonneg N
      (evenCeil ((N : ℝ) * δA)) (aN N) Fabs hFA
    rw [abs_of_nonneg hnonneg] at h
    exact lt_of_le_of_lt hdiagA h
  have hsmallDiagB : collisionEntrance N 0 (evenCeil ((N : ℝ) * δ))
      (bN N) (bN N) Fabs < ε := by
    have h := hN.2
    have hnonneg := collisionEntrance_diagonal_nonneg N
      (evenCeil ((N : ℝ) * δB)) (bN N) Fabs hFA
    rw [abs_of_nonneg hnonneg] at h
    exact lt_of_le_of_lt hdiagB h
  have hbound := collisionEntrance_abs_le_diagonal_average N 0
    (evenCeil ((N : ℝ) * δ)) (aN N) (bN N) F
  dsimp [Fabs] at hsmallDiagA hsmallDiagB
  change |collisionEntrance N 0 (evenCeil ((N : ℝ) * δ)) (aN N) (bN N) F| < ε
  calc
    _ ≤ (collisionEntrance N 0 (evenCeil ((N : ℝ) * δ))
          (aN N) (aN N) Fabs +
        collisionEntrance N 0 (evenCeil ((N : ℝ) * δ))
          (bN N) (bN N) Fabs) / 2 := by simpa [Fabs] using hbound
    _ < ε := by linarith

end Critical2DKPZ.SHF.Moments

end
