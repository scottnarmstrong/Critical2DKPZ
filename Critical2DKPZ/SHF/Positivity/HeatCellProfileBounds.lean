/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Lattice.Volume
public import Critical2DKPZ.MomentBounds.CSZ25GreenCalculus
public import Critical2DKPZ.Polymer.Profiles
public import Critical2DKPZ.Polymer.WalkKernel
public import Critical2DKPZ.Polymer.Endpoints
public import Critical2DKPZ.Analysis.Heat.Semigroup
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! # Mass and size of the heat-start lattice profile -/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Critical2DKPZ.SHF.Positivity

/-- The heat kernel's cell masses form a probability profile and each cell mass is bounded by
the cell volume times the heat-kernel maximum. -/
theorem heatCellProfile_bounds {N : ℕ} (hN : 1 ≤ N) {δ : ℝ} (hδ : 0 < δ) (x : Plane) :
    (∀ w, 0 ≤ ∫ y in cell N w, heatKernel δ (y - x)) ∧
    Summable (fun w : Site => ∫ y in cell N w, heatKernel δ (y - x)) ∧
    (∑' w : Site, ∫ y in cell N w, heatKernel δ (y - x)) = 1 ∧
    (∀ w, ∫ y in cell N w, heatKernel δ (y - x) ≤
      (4 / (N : ℝ)) * (2 * Real.pi * δ)⁻¹) := by
  let H : Plane → ℝ := fun y => heatKernel δ (y - x)
  let ν : Site → ℝ := fun w => ∫ y in cell N w, H y
  have hH : Integrable H := (integrable_heatKernel hδ).comp_sub_right x
  have hcover : (⋃ w : Site, cell N w) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    exact Set.mem_iUnion.mpr ⟨latticePoint N y, mem_cell_latticePoint N y⟩
  have hsum : HasSum ν 1 := by
    have h := hasSum_integral_iUnion (fun w => measurableSet_cell N w)
      (pairwise_disjoint_cell N) hH.integrableOn
    have h' : HasSum ν (∫ y, H y) := by
      simpa only [ν, H, hcover, setIntegral_univ] using h
    have htotal : (∫ y, H y) = 1 := by
      simpa only [H] using integral_heatKernel_sub hδ x
    rw [htotal] at h'
    exact h'
  have hνnonneg : ∀ w, 0 ≤ ν w := by
    intro w
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun y => heatKernel_nonneg hδ.le _)
  have hνsum : Summable ν := hsum.summable
  have hνmass : ∑' w, ν w = 1 := hsum.tsum_eq
  have hkernelBound (y : Plane) : H y ≤ (2 * Real.pi * δ)⁻¹ := by
    dsimp [H, heatKernel]
    have hexp : Real.exp (-‖y - x‖ ^ 2 / (2 * δ)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hn : 0 ≤ ‖y - x‖ ^ 2 := sq_nonneg _
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hn) (by positivity)
    calc
      (2 * Real.pi * δ)⁻¹ * Real.exp (-‖y - x‖ ^ 2 / (2 * δ)) ≤
          (2 * Real.pi * δ)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = (2 * Real.pi * δ)⁻¹ := by ring
  have hνbound : ∀ w, ν w ≤ (4 / (N : ℝ)) * (2 * Real.pi * δ)⁻¹ := by
    intro w
    by_cases hw : w ∈ evenLattice
    · have hvol := volume_cell_lt_top (by omega : 0 < N) hw
      have hconst : IntegrableOn (fun _ : Plane => (2 * Real.pi * δ)⁻¹)
          (cell N w) volume := integrableOn_const hvol.ne
      calc
        ν w ≤ ∫ y in cell N w, (2 * Real.pi * δ)⁻¹ :=
          setIntegral_mono_on hH.integrableOn hconst (measurableSet_cell N w)
            (fun y _ => hkernelBound y)
        _ = (2 * Real.pi * δ)⁻¹ * (4 / (N : ℝ)) := by
          rw [setIntegral_const, measureReal_def, smul_eq_mul,
            volume_cell_toReal (by omega : 0 < N) hw]
          ring
        _ = (4 / (N : ℝ)) * (2 * Real.pi * δ)⁻¹ := by ring
    · have hcell : cell N w = ∅ := cell_eq_empty_of_not_even hw
      simp [ν, hcell]
      positivity
  exact ⟨hνnonneg, hνsum, hνmass, hνbound⟩

/-- The Green energy of a heat-cell profile is at most `L` times the cell-volume bound
`(4/N)(2πδ)⁻¹` on each cell mass. The double series is summable by
`MomentBounds.summable_greenEnergy_terms`, using `heatCellProfile_bounds`. -/
theorem greenEnergy_heatCell_le (L : ℕ) {N : ℕ} (hN : 1 ≤ N) {δ : ℝ}
    (hδ : 0 < δ) (x : Plane) :
    MomentBounds.greenEnergy L (fun w => ∫ y in cell N w, heatKernel δ (y - x)) ≤
      (L : ℝ) * ((4 / (N : ℝ)) * (2 * Real.pi * δ)⁻¹) := by
  obtain ⟨hν0, hνsum, hν1, hνbound⟩ := heatCellProfile_bounds hN hδ x
  let ν : Site → ℝ := fun w => ∫ y in cell N w, heatKernel δ (y - x)
  let C : ℝ := (4 / (N : ℝ)) * (2 * Real.pi * δ)⁻¹
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hkernelTermSummable (z : Site) (n : ℕ) (hn : n ∈ Finset.Icc 1 L) :
      Summable (fun w : Site => srwKernel (2 * n) (z - w)) := by
    apply summable_of_ne_finset_zero (s := Polymer.endpoints z (2 * n))
    intro w hw
    rw [Polymer.srwKernel_sub_swap (2 * n) z w]
    exact Polymer.srwKernel_eq_zero_of_not_mem (2 * n) z w hw
  have hkernelTerm (z : Site) (n : ℕ) :
      (∑' w : Site, srwKernel (2 * n) (z - w)) = 1 := by
      have heq : (fun w : Site => srwKernel (2 * n) (z - w)) =
          fun w => srwKernel (2 * n) (w - z) := by
        funext w
        exact Polymer.srwKernel_sub_swap (2 * n) z w
      rw [heq]
      exact Polymer.tsum_srwKernel (2 * n) z
  have hkernelSummable (z : Site) :
      Summable (fun w : Site => MomentBounds.truncatedGreen L (z - w)) := by
    apply summable_of_ne_finset_zero
      (s := (Finset.Icc 1 L).biUnion fun n => Polymer.endpoints z (2 * n))
    intro w hw
    simp only [Finset.mem_biUnion, not_exists, not_and] at hw
    simp only [MomentBounds.truncatedGreen]
    apply Finset.sum_eq_zero
    intro n hn
    have hnot : w ∉ Polymer.endpoints z (2 * n) := hw n hn
    rw [Polymer.srwKernel_sub_swap (2 * n) z w]
    exact Polymer.srwKernel_eq_zero_of_not_mem (2 * n) z w hnot
  have hkernel (z : Site) :
      (∑' w : Site, MomentBounds.truncatedGreen L (z - w)) = L := by
    have hfinite := Summable.tsum_finsetSum (fun n hn => hkernelTermSummable z n hn)
    change (∑' w : Site, ∑ n ∈ Finset.Icc 1 L, srwKernel (2 * n) (z - w)) = L
    rw [hfinite]
    simp_rw [hkernelTerm]
    simp
  have hkernel0 (z w : Site) : 0 ≤ MomentBounds.truncatedGreen L (z - w) :=
    MomentBounds.truncatedGreen_nonneg L (z - w)
  have hinner (z : Site) :
      ∑' w : Site, ν z * MomentBounds.truncatedGreen L (z - w) * ν w ≤ ν z * C * L := by
    have hk := hkernel z
    have hweightedNonneg (w : Site) :
        0 ≤ MomentBounds.truncatedGreen L (z - w) * ν w :=
      mul_nonneg (hkernel0 z w) (hν0 w)
    have hweightedLe (w : Site) :
        MomentBounds.truncatedGreen L (z - w) * ν w ≤
          C * MomentBounds.truncatedGreen L (z - w) := by
      calc
        MomentBounds.truncatedGreen L (z - w) * ν w ≤
            MomentBounds.truncatedGreen L (z - w) *
              ((4 / (N : ℝ)) * (2 * Real.pi * δ)⁻¹) :=
          mul_le_mul_of_nonneg_left (hνbound w) (hkernel0 z w)
        _ = C * MomentBounds.truncatedGreen L (z - w) := by
          dsimp [C]
          ring
    have hweight : Summable (fun w : Site => C * MomentBounds.truncatedGreen L (z - w)) := by
      simpa only [mul_comm] using (hkernelSummable z).mul_left C
    have hweighted : Summable (fun w : Site =>
        MomentBounds.truncatedGreen L (z - w) * ν w) :=
      Summable.of_nonneg_of_le hweightedNonneg hweightedLe hweight
    have hsum : (∑' w : Site,
        MomentBounds.truncatedGreen L (z - w) * ν w) ≤ C * L := by
      have h := hweighted.tsum_le_tsum hweightedLe hweight
      have hright : (∑' w : Site,
          C * MomentBounds.truncatedGreen L (z - w)) = C * L := by
        rw [tsum_mul_left, hk]
      rw [hright] at h
      exact h
    calc
      _ = ∑' w : Site, ν z *
          (MomentBounds.truncatedGreen L (z - w) * ν w) := by
        congr 1
        funext w
        ring
      _ = ν z * ∑' w : Site,
          MomentBounds.truncatedGreen L (z - w) * ν w := by
        rw [tsum_mul_left]
      _ ≤ ν z * (C * L) := mul_le_mul_of_nonneg_left hsum (hν0 z)
      _ = ν z * C * L := by ring
  have houterNonneg (z : Site) :
      0 ≤ ∑' w : Site, ν z * MomentBounds.truncatedGreen L (z - w) * ν w :=
    tsum_nonneg fun w => mul_nonneg (mul_nonneg (hν0 z) (hkernel0 z w)) (hν0 w)
  have houterLe (z : Site) :
      (∑' w : Site, ν z * MomentBounds.truncatedGreen L (z - w) * ν w) ≤
        ν z * (C * L) := by
    simpa only [mul_assoc] using hinner z
  have hmajorSummable : Summable (fun z : Site => ν z * (C * L)) :=
    hνsum.mul_right (C * L)
  have houterSummable : Summable (fun z : Site =>
      ∑' w : Site, ν z * MomentBounds.truncatedGreen L (z - w) * ν w) :=
    Summable.of_nonneg_of_le houterNonneg houterLe hmajorSummable
  unfold MomentBounds.greenEnergy
  calc
    _ ≤ ∑' z : Site, ν z * (C * L) := houterSummable.tsum_le_tsum houterLe hmajorSummable
    _ = C * L := by rw [tsum_mul_right, hν1, one_mul]
    _ = (L : ℝ) * ((4 / (N : ℝ)) * (2 * Real.pi * δ)⁻¹) := by
          simp only [C]
          ring

end Critical2DKPZ.SHF.Positivity

end
