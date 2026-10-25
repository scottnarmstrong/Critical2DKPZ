/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.BlockResampling
public import Critical2DKPZ.Polymer.BlockMeasurability
public import Critical2DKPZ.Polymer.ChapmanKolmogorov
public import Critical2DKPZ.SHF.Limit.SlabMean
import Mathlib.Tactic

/-! # Exact polymer projection through an annealed time slab -/

@[expose] public noncomputable section

open MeasureTheory

namespace Critical2DKPZ.SHF.Flow

/-- A function measurable on a time interval is unchanged when a disjoint interval is resampled. -/
theorem blockMeasurable_resample_outside {a b c d : ℕ} {F : Disorder → ℝ}
    (hdisj : Disjoint (Set.Ioc a b) (Set.Ioc c d))
    (hF : Measurable[Gaussian.disorderBlock a b] F) (ω η : Disorder) :
    F (Gaussian.resample (Gaussian.timeBlock c d) η ω) = F ω := by
  change Measurable[MeasurableSpace.comap
    (fun ξ (j : Gaussian.timeBlock a b) => ξ j) inferInstance] F at hF
  apply hF.factorsThrough
  funext j
  have hj : (j : ℕ × Site) ∉ Gaussian.timeBlock c d := by
    intro hj
    have hja : j.val.1 ∈ Set.Ioc a b := by
      change a < j.val.1 ∧ j.val.1 ≤ b
      exact j.property
    have hjcd : j.val.1 ∈ Set.Ioc c d := by
      change c < j.val.1 ∧ j.val.1 ≤ d at hj
      exact hj
    exact (Set.disjoint_left.mp hdisj hja hjcd).elim
  simp only [Gaussian.resample, hj, ite_false]

/-- Resampling a middle slab replaces exactly its point-to-point factor in the lattice
Chapman–Kolmogorov expansion. -/
theorem pointToPoint_resample_slab (β : ℝ) {a b c d : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (x z : Site) (ω η : Disorder) :
    pointToPoint β a (d - a) x z
        (Gaussian.resample (Gaussian.timeBlock b c) η ω) =
      ∑' w, ∑' y, pointToPoint β a (b - a) x w ω *
        pointToPoint β b (c - b) w y η * pointToPoint β c (d - c) y z ω := by
  have htotal : d - a = (b - a) + (d - b) := by omega
  have htail : d - b = (c - b) + (d - c) := by omega
  have hfirst (w : Site) :
      pointToPoint β a (b - a) x w
          (Gaussian.resample (Gaussian.timeBlock b c) η ω) =
        pointToPoint β a (b - a) x w ω := by
    apply blockMeasurable_resample_outside
      (a := a) (b := b) (c := b) (d := c)
      (Set.disjoint_left.mpr fun n hn ht => by
        simp only [Set.mem_Ioc] at hn ht
        omega)
    convert Polymer.measurable_pointToPoint_block β a (b - a) x w using 1
    rw [Nat.add_sub_of_le hab]
  have hmiddle (w y : Site) :
      pointToPoint β b (c - b) w y
          (Gaussian.resample (Gaussian.timeBlock b c) η ω) =
        pointToPoint β b (c - b) w y η := by
    apply Blocks.blockMeasurable_resample_keep
    convert Polymer.measurable_pointToPoint_block β b (c - b) w y using 1
    rw [Nat.add_sub_of_le hbc]
  have hlast (y z : Site) :
      pointToPoint β c (d - c) y z
          (Gaussian.resample (Gaussian.timeBlock b c) η ω) =
        pointToPoint β c (d - c) y z ω := by
    apply blockMeasurable_resample_outside
      (a := c) (b := d) (c := b) (d := c)
      (Set.disjoint_left.mpr fun n hn ht => by
        simp only [Set.mem_Ioc] at hn ht
        omega)
    convert Polymer.measurable_pointToPoint_block β c (d - c) y z using 1
    rw [Nat.add_sub_of_le hcd]
  calc
    _ = ∑' w, pointToPoint β a (b - a) x w
          (Gaussian.resample (Gaussian.timeBlock b c) η ω) *
        pointToPoint β b (d - b) w z
          (Gaussian.resample (Gaussian.timeBlock b c) η ω) := by
      rw [htotal, Polymer.pointToPoint_chapmanKolmogorov]
      apply tsum_congr
      intro w
      rw [Nat.add_sub_of_le hab]
    _ = ∑' w, pointToPoint β a (b - a) x w ω *
          ∑' y, pointToPoint β b (c - b) w y η *
            pointToPoint β c (d - c) y z ω := by
      apply tsum_congr
      intro w
      rw [htail, Polymer.pointToPoint_chapmanKolmogorov]
      rw [Nat.add_sub_of_le hbc]
      rw [hfirst w]
      apply congrArg (fun r : ℝ => pointToPoint β a (b - a) x w ω * r)
      apply tsum_congr
      intro y
      rw [hmiddle w y, hlast y z]
    _ = ∑' w, ∑' y, pointToPoint β a (b - a) x w ω *
          pointToPoint β b (c - b) w y η * pointToPoint β c (d - c) y z ω := by
      apply tsum_congr
      intro w
      conv_lhs => rw [← tsum_mul_left]
      apply tsum_congr
      intro y
      ring

/-- Averaging the resampled middle slab replaces its point-to-point kernel by the walk kernel. -/
theorem integrable_pointToPoint_resample_slab (β : ℝ) {a b c d : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (x z : Site) (ω : Disorder) :
    Integrable (fun η => pointToPoint β a (d - a) x z
      (Gaussian.resample (Gaussian.timeBlock b c) η ω)) disorderLaw := by
  classical
  let W : Finset Site := Polymer.endpoints x (b - a)
  let V (w : Site) : Finset Site := Polymer.endpoints w (c - b)
  let G : Disorder → ℝ := fun η =>
    ∑ w ∈ W, ∑ y ∈ V w,
      pointToPoint β a (b - a) x w ω *
        pointToPoint β b (c - b) w y η *
        pointToPoint β c (d - c) y z ω
  have hfirst_zero {w : Site} (hw : w ∉ W) :
      pointToPoint β a (b - a) x w ω = 0 := by
    exact Polymer.pointToPoint_eq_zero_of_not_mem β a (b - a) x w ω (by simpa [W] using hw)
  have hmiddle_zero (w : Site) {y : Site} (hy : y ∉ V w) (η : Disorder) :
      pointToPoint β b (c - b) w y η = 0 := by
    exact Polymer.pointToPoint_eq_zero_of_not_mem β b (c - b) w y η (by simpa [V] using hy)
  have hsum (η : Disorder) :
      (∑' w, ∑' y, pointToPoint β a (b - a) x w ω *
        pointToPoint β b (c - b) w y η * pointToPoint β c (d - c) y z ω) = G η := by
    simp only [G]
    rw [tsum_eq_sum (s := W) (fun w hw => by rw [hfirst_zero hw]; simp)]
    apply Finset.sum_congr rfl
    intro w hw
    rw [tsum_eq_sum (s := V w) (fun y hy => by rw [hmiddle_zero w hy η]; simp)]
  have hpoint (η : Disorder) :
      pointToPoint β a (d - a) x z (Gaussian.resample (Gaussian.timeBlock b c) η ω) = G η := by
    rw [pointToPoint_resample_slab β hab hbc hcd x z ω η, hsum]
  have hGint : Integrable G disorderLaw := by
    dsimp [G]
    apply integrable_finsetSum
    intro w hw
    apply integrable_finsetSum
    intro y hy
    have hmid := Polymer.integrable_pointToPoint β b (c - b) w y
    have h := hmid.const_mul
      (pointToPoint β a (b - a) x w ω * pointToPoint β c (d - c) y z ω)
    apply h.congr
    filter_upwards [] with η
    ring
  apply hGint.congr
  filter_upwards [] with η
  exact (hpoint η).symm

/-- Averaging the resampled middle slab replaces its point-to-point kernel by the walk kernel. -/
theorem integral_pointToPoint_resample_slab (β : ℝ) {a b c d : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (x z : Site) (ω : Disorder) :
    ∫ η, pointToPoint β a (d - a) x z
        (Gaussian.resample (Gaussian.timeBlock b c) η ω) ∂disorderLaw =
      ∑' w, ∑' y, pointToPoint β a (b - a) x w ω *
        srwKernel (c - b) (y - w) * pointToPoint β c (d - c) y z ω := by
  classical
  let W : Finset Site := Polymer.endpoints x (b - a)
  let V (w : Site) : Finset Site := Polymer.endpoints w (c - b)
  let G : Disorder → ℝ := fun η =>
    ∑ w ∈ W, ∑ y ∈ V w,
      pointToPoint β a (b - a) x w ω *
        pointToPoint β b (c - b) w y η *
        pointToPoint β c (d - c) y z ω
  have hfirst_zero {w : Site} (hw : w ∉ W) :
      pointToPoint β a (b - a) x w ω = 0 := by
    exact Polymer.pointToPoint_eq_zero_of_not_mem β a (b - a) x w ω (by simpa [W] using hw)
  have hmiddle_zero (w : Site) {y : Site} (hy : y ∉ V w) (η : Disorder) :
      pointToPoint β b (c - b) w y η = 0 := by
    exact Polymer.pointToPoint_eq_zero_of_not_mem β b (c - b) w y η (by simpa [V] using hy)
  have hsum (η : Disorder) :
      (∑' w, ∑' y, pointToPoint β a (b - a) x w ω *
        pointToPoint β b (c - b) w y η * pointToPoint β c (d - c) y z ω) = G η := by
    simp only [G]
    rw [tsum_eq_sum (s := W) (fun w hw => by rw [hfirst_zero hw]; simp)]
    apply Finset.sum_congr rfl
    intro w hw
    rw [tsum_eq_sum (s := V w) (fun y hy => by rw [hmiddle_zero w hy η]; simp)]
  have hpoint (η : Disorder) :
      pointToPoint β a (d - a) x z (Gaussian.resample (Gaussian.timeBlock b c) η ω) = G η := by
    rw [pointToPoint_resample_slab β hab hbc hcd x z ω η, hsum]
  calc
    _ = ∫ η, G η ∂disorderLaw := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = ∑ w ∈ W, ∑ y ∈ V w,
        pointToPoint β a (b - a) x w ω * srwKernel (c - b) (y - w) *
          pointToPoint β c (d - c) y z ω := by
      dsimp [G]
      rw [integral_finsetSum _ (fun w hw => by
        apply integrable_finsetSum
        intro y hy
        have hmid := Polymer.integrable_pointToPoint β b (c - b) w y
        have h := hmid.const_mul
          (pointToPoint β a (b - a) x w ω * pointToPoint β c (d - c) y z ω)
        apply h.congr
        filter_upwards [] with η
        ring)]
      apply Finset.sum_congr rfl
      intro w hw
      rw [integral_finsetSum _ (fun y hy => by
        have hmid := Polymer.integrable_pointToPoint β b (c - b) w y
        simpa only [mul_assoc, mul_left_comm, mul_comm] using hmid.const_mul
          (pointToPoint β a (b - a) x w ω * pointToPoint β c (d - c) y z ω))]
      apply Finset.sum_congr rfl
      intro y hy
      have heq : (fun η =>
          pointToPoint β a (b - a) x w ω *
            pointToPoint β b (c - b) w y η *
            pointToPoint β c (d - c) y z ω) =
          fun η => (pointToPoint β a (b - a) x w ω *
            pointToPoint β c (d - c) y z ω) *
            pointToPoint β b (c - b) w y η := by
        funext η
        ring
      rw [heq, integral_const_mul]
      rw [Polymer.integral_pointToPoint]
      ring
    _ = ∑' w, ∑' y,
        pointToPoint β a (b - a) x w ω * srwKernel (c - b) (y - w) *
          pointToPoint β c (d - c) y z ω := by
      symm
      rw [tsum_eq_sum (s := W) (fun w hw => by rw [hfirst_zero hw]; simp)]
      apply Finset.sum_congr rfl
      intro w hw
      rw [tsum_eq_sum (s := V w) (fun y hy => by
        have hyzero : srwKernel (c - b) (y - w) = 0 := by
          exact Polymer.srwKernel_eq_zero_of_not_mem (c - b) w y (by simpa [V] using hy)
        rw [hyzero]
        ring)]


end Critical2DKPZ.SHF.Flow

end
