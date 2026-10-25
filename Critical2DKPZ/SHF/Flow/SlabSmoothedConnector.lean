/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.SlabSmoothedFinite
public import Critical2DKPZ.Polymer.SummableCovariance

/-! # Cell formulas for smoothed slab connectors -/

@[expose] public noncomputable section

open MeasureTheory
open Critical2DKPZ.SHF.Limit
open Critical2DKPZ.SHF.Tsai
open scoped CompactlySupported

namespace Critical2DKPZ.SHF.Flow

/-- A one-dimensional lattice-step integral is the sum of its exact cell integrals. -/
theorem integral_latticeStep_eq_cellTsum (N : ℕ) (ψ : C_c(Plane, ℝ))
    (G : Site → ℝ) (C : ℝ) (hG : ∀ z, ‖G z‖ ≤ C) :
    ∫ x : Plane, ψ x * G (latticePoint N x) =
      ∑' z : Site, (∫ x in cell N z, ψ x) * G z := by
  classical
  let S : Set Site := latticePoint N '' tsupport ψ
  have hS : S.Finite := finite_latticePoint_image_of_bounded (N := N)
    ψ.hasCompactSupport.isBounded
  let H : Plane → ℝ := fun x => ψ x * G (latticePoint N x)
  have hHm : Measurable H := by
    dsimp [H]
    exact ψ.measurable.mul
      ((measurable_of_countable G).comp (measurable_latticePoint N))
  have hHint : Integrable H := by
    apply (ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport).norm.const_mul C |>.mono'
      hHm.aestronglyMeasurable
    filter_upwards [] with x
    calc
      ‖H x‖ = ‖ψ x‖ * ‖G (latticePoint N x)‖ := by simp [H, norm_mul]
      _ ≤ ‖ψ x‖ * C := mul_le_mul_of_nonneg_left (hG _) (norm_nonneg _)
      _ = C * ‖ψ x‖ := by ring
  have hcover : (⋃ z : Site, cell N z) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨latticePoint N x, mem_cell_latticePoint N x⟩
  have hdisj : Pairwise (fun z z' : Site => Disjoint (cell N z) (cell N z')) := by
    intro z z' hzz'
    exact pairwise_disjoint_cell N hzz'
  have hsum := integral_iUnion (fun z : Site => measurableSet_cell N z) hdisj hHint.integrableOn
  rw [hcover, setIntegral_univ] at hsum
  have hcell (z : Site) :
      ∫ x in cell N z, H x = (∫ x in cell N z, ψ x) * G z := by
    calc
      ∫ x in cell N z, H x = ∫ x in cell N z, ψ x * G z := by
        apply setIntegral_congr_fun (measurableSet_cell N z)
        intro x hx
        simp only [mem_cell_iff] at hx
        simp [H, hx]
      _ = _ := by rw [integral_mul_const]
  calc
    ∫ x : Plane, ψ x * G (latticePoint N x) = ∑' z : Site, ∫ x in cell N z, H x := hsum
    _ = ∑' z : Site, (∫ x in cell N z, ψ x) * G z := by
      apply tsum_congr
      exact hcell

/-- Translating a compactly supported continuous function by `a - y` preserves compact support. -/
def translatedSmoothedTest (w : Plane → ℝ) (hw : Continuous w) (hwc : HasCompactSupport w)
    (a : Plane) : C_c(Plane, ℝ) where
  toContinuousMap := ⟨fun y => w (a - y), hw.comp (Homeomorph.subLeft a).continuous⟩
  hasCompactSupport' := hwc.comp_homeomorph (Homeomorph.subLeft a)

/-- The translated test has the expected pointwise formula. -/
theorem translatedSmoothedTest_apply (w : Plane → ℝ) (hw : Continuous w)
    (hwc : HasCompactSupport w) (a y : Plane) : translatedSmoothedTest w hw hwc a y = w (a - y) := rfl

/-- Convolving the mean slab kernel against a compactly supported connector is its exact
one-dimensional cell sum. -/
theorem slabSmoothedConnector_eq_cellTsum (ϑ : ℝ) (N : ℕ) (t t' : ℝ)
    (a b : Plane) (w : Plane → ℝ) (hw : Continuous w) (hwc : HasCompactSupport w) :
    (∫ y, w (a - y) * slabMeanKernel ϑ N t t' y b) =
      (N : ℝ) / 4 * ∑' r : Site,
        (∫ y in cell N r, w (a - y)) *
        srwKernel (evenCeil ((N : ℝ) * t') - evenCeil ((N : ℝ) * t))
            (latticePoint N b - r) := by
  let ψ := translatedSmoothedTest w hw hwc a
  let G : Site → ℝ := fun r =>
    srwKernel (evenCeil ((N : ℝ) * t') - evenCeil ((N : ℝ) * t))
      (latticePoint N b - r)
  have hG : ∀ r, ‖G r‖ ≤ 1 := by
    intro r
    change ‖srwKernel (evenCeil ((N : ℝ) * t') - evenCeil ((N : ℝ) * t))
      (latticePoint N b - r)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (Polymer.kernel_nonneg _ _)]
    exact Polymer.srwKernel_le_one _ _
  have hpoint (y : Plane) :
      w (a - y) * slabMeanKernel ϑ N t t' y b =
        (N : ℝ) / 4 * (ψ y * G (latticePoint N y)) := by
    rw [slabMeanKernel_eq_srwKernel ϑ N t t' y b]
    simp only [ψ, translatedSmoothedTest_apply, G]
    ring
  calc
    _ = ∫ y, (N : ℝ) / 4 * (ψ y * G (latticePoint N y)) := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact hpoint y
    _ = (N : ℝ) / 4 * ∫ y, ψ y * G (latticePoint N y) := by
      rw [integral_const_mul]
    _ = _ := by
      rw [integral_latticeStep_eq_cellTsum N ψ G 1 hG]
      rfl

/-- Integrating the smoothed slab connector over two lattice cells leaves the middle-cell
connector integrals, with the endpoint cell volume cancelling the slab normalization. -/
theorem slabSmoothedConnector_cellPair_eq_sum (ϑ : ℝ) (N : ℕ) (hN : 0 < N)
    (t t' : ℝ) (a b : Site) (hb : b ∈ evenLattice)
    (w : Plane → ℝ) (hw : Continuous w) (hwc : HasCompactSupport w) :
    ∫ p in cell N a ×ˢ cell N b,
        (∫ y, w (p.1 - y) * slabMeanKernel ϑ N t t' y p.2) =
      ∑ r ∈ Polymer.endpoints b (evenCeil ((N : ℝ) * t') - evenCeil ((N : ℝ) * t)),
        (∫ p in cell N a ×ˢ cell N r, w (p.1 - p.2)) *
          srwKernel (evenCeil ((N : ℝ) * t') - evenCeil ((N : ℝ) * t)) (b - r) := by
  classical
  let m := evenCeil ((N : ℝ) * t') - evenCeil ((N : ℝ) * t)
  let R := Polymer.endpoints b m
  let fr : Site → Plane → ℝ := fun r x => ∫ y in cell N r, w (x - y)
  let μ : Measure (Plane × Plane) := volume
  let A : Set Plane := cell N a
  let B : Set Plane := cell N b
  obtain ⟨Cw, hwbound⟩ := hw.bounded_above_of_compact_support hwc
  have hCw : 0 ≤ Cw := (norm_nonneg _).trans (hwbound 0)
  have hcellFinite (r : Site) : volume (cell N r) < ⊤ := by
    by_cases hr : r ∈ evenLattice
    · exact volume_cell_lt_top hN hr
    · simp [cell_eq_empty_of_not_even hr]
  have hpairFinite (r q : Site) : μ (cell N r ×ˢ cell N q) < ⊤ := by
    dsimp [μ]
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_lt_top (hcellFinite r) (hcellFinite q)
  have hfrMeas (r : Site) : Measurable (fr r) := by
    change Measurable (fun x => ∫ y in cell N r, w (x - y))
    have hsm : StronglyMeasurable (fun p : Plane × Plane => w (p.1 - p.2)) := by
      exact (by fun_prop : Continuous (fun p : Plane × Plane => w (p.1 - p.2))).stronglyMeasurable
    have hsm' := hsm.integral_prod_right' (ν := volume.restrict (cell N r))
    exact hsm'.measurable
  have hfrBound (r : Site) (x : Plane) :
      ‖fr r x‖ ≤ Cw * (volume (cell N r)).toReal := by
    have hconst : Integrable (fun _ : Plane => Cw) (volume.restrict (cell N r)) := by
      simpa [IntegrableOn] using
        (integrableOn_const (μ := volume) (s := cell N r) (C := Cw) (hcellFinite r).ne)
    have hnorm := norm_integral_le_of_norm_le hconst
      (Filter.Eventually.of_forall fun y => by
        exact hwbound (x - y))
    dsimp [fr]
    calc
      ‖∫ y in cell N r, w (x - y)‖ ≤ ∫ y, Cw ∂(volume.restrict (cell N r)) := hnorm
      _ = Cw * (volume (cell N r)).toReal := by
        rw [integral_const, measureReal_restrict_apply_univ, smul_eq_mul, measureReal_def]
        ring
  have hfrBoundNonneg (r : Site) : 0 ≤ Cw * (volume (cell N r)).toReal :=
    mul_nonneg hCw (ENNReal.toReal_nonneg)
  have hcellConnector (p : Plane × Plane) (hp : p ∈ cell N a ×ˢ cell N b) :
      (∫ y, w (p.1 - y) * slabMeanKernel ϑ N t t' y p.2) =
        (N : ℝ) / 4 * ∑ r ∈ R, fr r p.1 * srwKernel m (b - r) := by
    rw [slabSmoothedConnector_eq_cellTsum ϑ N t t' p.1 p.2 w hw hwc]
    have hpB : latticePoint N p.2 = b := (mem_cell_iff N b p.2).mp hp.2
    simp only [m, R, fr, hpB]
    rw [tsum_eq_sum (s := R) fun r hr => by
      have hzero : srwKernel (evenCeil ((N : ℝ) * t') - evenCeil ((N : ℝ) * t))
          (b - r) = 0 := by
        apply Polymer.srwKernel_eq_zero_of_not_mem _ r b
        intro hbR
        exact hr (mem_endpoints_reverse hbR)
      simp [hzero]]
  have htermIntegrable (r : Site) : Integrable (fun p : Plane × Plane =>
      fr r p.1 * srwKernel m (b - r)) (μ.restrict (A ×ˢ B)) := by
    have hkernelNonneg : 0 ≤ srwKernel m (b - r) := Polymer.kernel_nonneg _ _
    have hkernelBound : ‖srwKernel m (b - r)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg hkernelNonneg]
      exact Polymer.srwKernel_le_one _ _
    have hbound (p : Plane × Plane) :
        ‖fr r p.1 * srwKernel m (b - r)‖ ≤ Cw * (volume (cell N r)).toReal := by
      rw [norm_mul]
      calc
        ‖fr r p.1‖ * ‖srwKernel m (b - r)‖ ≤
            (Cw * (volume (cell N r)).toReal) * ‖srwKernel m (b - r)‖ :=
          mul_le_mul_of_nonneg_right (hfrBound r p.1) (norm_nonneg _)
        _ ≤ Cw * (volume (cell N r)).toReal :=
          calc
            _ ≤ Cw * (volume (cell N r)).toReal * 1 :=
              mul_le_mul_of_nonneg_left hkernelBound (hfrBoundNonneg r)
            _ = _ := by ring
    have hmeas : Measurable (fun p : Plane × Plane =>
        fr r p.1 * srwKernel m (b - r)) := (hfrMeas r).comp measurable_fst |>.mul measurable_const
    exact (IntegrableOn.of_bound (by simpa [A, B] using hpairFinite a b)
      hmeas.aestronglyMeasurable (Cw * (volume (cell N r)).toReal)
      (Filter.Eventually.of_forall hbound)).integrable
  have htermEq (r : Site) :
      ∫ p in cell N a ×ˢ cell N b, fr r p.1 * srwKernel m (b - r) =
        (∫ p in cell N a ×ˢ cell N r, w (p.1 - p.2)) *
          (volume (cell N b)).toReal * srwKernel m (b - r) := by
    calc
      _ = (∫ x in cell N a, fr r x) *
            (∫ y in cell N b, srwKernel m (b - r)) := by
              change ∫ p in cell N a ×ˢ cell N b,
                  fr r p.1 * srwKernel m (b - r) ∂((volume : Measure Plane).prod volume) = _
              exact setIntegral_prod_mul (fun x => fr r x) (fun _ => srwKernel m (b - r))
                (cell N a) (cell N b)
      _ = (∫ p in cell N a ×ˢ cell N r, w (p.1 - p.2)) *
            (volume (cell N b)).toReal * srwKernel m (b - r) := by
              rw [integral_const, measureReal_restrict_apply_univ, smul_eq_mul, measureReal_def]
              have hcell := integral_cellPair_eq_iterated N hN
                (fun p : Plane × Plane => w (p.1 - p.2)) (by fun_prop)
                Cw (by
                  intro p
                  exact hwbound (p.1 - p.2))
                a r
              have hcell' :
                  ∫ p in cell N a ×ˢ cell N r, w (p.1 - p.2) = ∫ x in cell N a, fr r x := by
                simpa [fr] using hcell
              rw [← hcell']
              ring
  have hsumIntegrable : ∀ r ∈ R, Integrable (fun p : Plane × Plane =>
      fr r p.1 * srwKernel m (b - r)) (μ.restrict (A ×ˢ B)) :=
    fun r _ => htermIntegrable r
  calc
    ∫ p in cell N a ×ˢ cell N b,
        (∫ y, w (p.1 - y) * slabMeanKernel ϑ N t t' y p.2) =
      ∫ p in cell N a ×ˢ cell N b,
        (N : ℝ) / 4 * ∑ r ∈ R, fr r p.1 * srwKernel m (b - r) := by
          apply setIntegral_congr_fun ((measurableSet_cell N a).prod (measurableSet_cell N b))
          intro p hp
          exact hcellConnector p hp
    _ = (N : ℝ) / 4 * ∑ r ∈ R,
          ∫ p in cell N a ×ˢ cell N b, fr r p.1 * srwKernel m (b - r) := by
            rw [integral_const_mul, integral_finsetSum]
            intro r hr
            exact hsumIntegrable r hr
    _ = _ := by
      have hterms : (∑ r ∈ R,
          ∫ p in cell N a ×ˢ cell N b, fr r p.1 * srwKernel m (b - r)) =
          ∑ r ∈ R,
            (∫ p in cell N a ×ˢ cell N r, w (p.1 - p.2)) *
              (volume (cell N b)).toReal * srwKernel m (b - r) := by
        apply Finset.sum_congr rfl
        intro r hr
        exact htermEq r
      rw [hterms, volume_cell_toReal hN hb]
      simp only [R, m]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      field_simp [hNne]

end Critical2DKPZ.SHF.Flow

end
