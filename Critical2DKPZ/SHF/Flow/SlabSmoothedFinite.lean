/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.SlabProductsIdentities

/-! # Finite cell expansions for smoothed polymer products -/

@[expose] public noncomputable section

open MeasureTheory
open Critical2DKPZ.SHF.Limit
open Critical2DKPZ.SHF.Tsai
open scoped CompactlySupported ENNReal

namespace Critical2DKPZ.SHF.Flow

/-- The four-variable test used in a smoothed polymer product. -/
def smoothedProductFourTest (Φ : C_c(Plane × Plane, ℝ)) (w : Plane → ℝ)
    (p : (Plane × Plane) × (Plane × Plane)) : ℝ :=
  Φ (p.1.1, p.2.2) * w (p.1.2 - p.2.1)

/-- The lattice coefficient in the finite four-cell expansion of a smoothed polymer product. -/
def smoothedProductSiteCoefficient (ϑ : ℝ) (N : ℕ) (s t t' u : ℝ) (ω : Disorder)
    (q : (Site × Site) × (Site × Site)) : ℝ :=
  ((N : ℝ) / 4 * pointToPoint (criticalBeta ϑ N)
      (evenCeil ((N : ℝ) * s))
      (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) q.1.1 q.1.2 ω) *
    ((N : ℝ) / 4 * pointToPoint (criticalBeta ϑ N)
      (evenCeil ((N : ℝ) * t'))
      (evenCeil ((N : ℝ) * u) - evenCeil ((N : ℝ) * t')) q.2.1 q.2.2 ω)

/-- The smoothed polymer product is a finite sum whose coefficient is the exact four-cell
integral of `Φ(x,z) w(a-y)`. -/
theorem smoothedProductPairing_polymer_eq_finiteCellSum (ϑ : ℝ) (N : ℕ) (hN : 0 < N)
    (s t t' u : ℝ) (ω : Disorder) (Φ : C_c(Plane × Plane, ℝ)) (w : Plane → ℝ)
    (hw : Continuous w) (hwc : HasCompactSupport w)
    (Q : Finset ((Site × Site) × (Site × Site)))
    (hzero : ∀ q ∉ Q, ∀ p ∈
      (cell N q.1.1 ×ˢ cell N q.1.2) ×ˢ (cell N q.2.1 ×ˢ cell N q.2.2),
        smoothedProductFourTest Φ w p * smoothedProductSiteCoefficient ϑ N s t t' u ω q = 0) :
    smoothedProductPairing (polymerMeasure ϑ N s t ω) w
      (polymerMeasure ϑ N t' u ω) Φ =
    ∑ q ∈ Q,
      (∫ p in (cell N q.1.1 ×ˢ cell N q.1.2) ×ˢ
          (cell N q.2.1 ×ˢ cell N q.2.2),
        smoothedProductFourTest Φ w p
        ∂((volume : Measure (Plane × Plane)).prod volume)) *
        (((N : ℝ) / 4 * pointToPoint (criticalBeta ϑ N)
            (evenCeil ((N : ℝ) * s))
            (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) q.1.1 q.1.2 ω) *
          ((N : ℝ) / 4 * pointToPoint (criticalBeta ϑ N)
            (evenCeil ((N : ℝ) * t'))
            (evenCeil ((N : ℝ) * u) - evenCeil ((N : ℝ) * t')) q.2.1 q.2.2 ω)) := by
  classical
  let F := smoothedProductFourTest Φ w
  let G := smoothedProductSiteCoefficient ϑ N s t t' u ω
  have hFc : Continuous F := by
    change Continuous (fun p : (Plane × Plane) × (Plane × Plane) =>
      Φ (p.1.1, p.2.2) * w (p.1.2 - p.2.1))
    fun_prop
  obtain ⟨CΦ, hΦbound⟩ := Φ.continuous.bounded_above_of_compact_support Φ.hasCompactSupport
  obtain ⟨Cw, hwbound⟩ := hw.bounded_above_of_compact_support hwc
  have hΦnonneg : 0 ≤ CΦ := by
    have h := hΦbound (0 : Plane × Plane)
    exact (norm_nonneg _).trans h
  have hwnonneg : 0 ≤ Cw := by
    have h := hwbound (0 : Plane)
    exact (norm_nonneg _).trans h
  have hFbound : ∀ p, ‖F p‖ ≤ CΦ * Cw := by
    intro p
    dsimp [F, smoothedProductFourTest]
    calc
      ‖Φ (p.1.1, p.2.2) * w (p.1.2 - p.2.1)‖ =
          ‖Φ (p.1.1, p.2.2)‖ * ‖w (p.1.2 - p.2.1)‖ := norm_mul _ _
      _ ≤ CΦ * ‖w (p.1.2 - p.2.1)‖ :=
        mul_le_mul_of_nonneg_right (hΦbound _) (norm_nonneg _)
      _ ≤ CΦ * Cw := mul_le_mul_of_nonneg_left (hwbound _) hΦnonneg
  have hsum := integral_finiteLatticeFourStep_test_eq_cellSum N hN F hFc.measurable
    (CΦ * Cw) hFbound G Q (by simpa [F, G] using hzero)
  have hdensity := kernelProductPairing_polymer_eq_densityIntegral ϑ N s t t' u ω
    (fun a b => w (a - b)) Φ
  have hintegrand :
      (fun p : (Plane × Plane) × (Plane × Plane) =>
        (rescaledP2P ϑ N s t p.1 ω * rescaledP2P ϑ N t' u p.2 ω) *
          (Φ (p.1.1, p.2.2) * w (p.1.2 - p.2.1))) =
      (fun p => F p * G ((latticePoint N p.1.1, latticePoint N p.1.2),
        (latticePoint N p.2.1, latticePoint N p.2.2))) := by
    funext p
    simp only [F, G, smoothedProductFourTest, smoothedProductSiteCoefficient, rescaledP2P]
    ring
  calc
    _ = kernelProductPairing (polymerMeasure ϑ N s t ω) (fun a b => w (a - b))
        (polymerMeasure ϑ N t' u ω) Φ := by
      rfl
    _ = ∫ p : (Plane × Plane) × (Plane × Plane),
        (rescaledP2P ϑ N s t p.1 ω * rescaledP2P ϑ N t' u p.2 ω) *
          (Φ (p.1.1, p.2.2) * w (p.1.2 - p.2.1))
        ∂((volume : Measure (Plane × Plane)).prod volume) := hdensity
    _ = ∫ p : (Plane × Plane) × (Plane × Plane),
        F p * G ((latticePoint N p.1.1, latticePoint N p.1.2),
          (latticePoint N p.2.1, latticePoint N p.2.2))
        ∂((volume : Measure (Plane × Plane)).prod volume) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (congrFun hintegrand)
    _ = ∑ q ∈ Q,
        (∫ p in (cell N q.1.1 ×ˢ cell N q.1.2) ×ˢ
          (cell N q.2.1 ×ˢ cell N q.2.2), F p
          ∂((volume : Measure (Plane × Plane)).prod volume)) * G q := hsum
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q hq
      rfl

/-- The smoothed finite cell expansion also holds when the two polymer intervals use different
disorder configurations. -/
theorem smoothedProductPairing_polymer_eq_finiteCellSum_mixed (ϑ : ℝ) (N : ℕ) (hN : 0 < N)
    (s t t' u : ℝ) (ω₁ ω₂ : Disorder) (Φ : C_c(Plane × Plane, ℝ)) (w : Plane → ℝ)
    (hw : Continuous w) (hwc : HasCompactSupport w)
    (Q : Finset ((Site × Site) × (Site × Site)))
    (hzero : ∀ q ∉ Q, ∀ p ∈
      (cell N q.1.1 ×ˢ cell N q.1.2) ×ˢ (cell N q.2.1 ×ˢ cell N q.2.2),
        smoothedProductFourTest Φ w p *
          (((N : ℝ) / 4 * pointToPoint (criticalBeta ϑ N)
              (evenCeil ((N : ℝ) * s))
              (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) q.1.1 q.1.2 ω₁) *
            ((N : ℝ) / 4 * pointToPoint (criticalBeta ϑ N)
              (evenCeil ((N : ℝ) * t'))
              (evenCeil ((N : ℝ) * u) - evenCeil ((N : ℝ) * t')) q.2.1 q.2.2 ω₂)) = 0) :
    smoothedProductPairing (polymerMeasure ϑ N s t ω₁) w
      (polymerMeasure ϑ N t' u ω₂) Φ =
    ∑ q ∈ Q,
      (∫ p in (cell N q.1.1 ×ˢ cell N q.1.2) ×ˢ
          (cell N q.2.1 ×ˢ cell N q.2.2),
        smoothedProductFourTest Φ w p
        ∂((volume : Measure (Plane × Plane)).prod volume)) *
        (((N : ℝ) / 4 * pointToPoint (criticalBeta ϑ N)
            (evenCeil ((N : ℝ) * s))
            (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) q.1.1 q.1.2 ω₁) *
          ((N : ℝ) / 4 * pointToPoint (criticalBeta ϑ N)
            (evenCeil ((N : ℝ) * t'))
            (evenCeil ((N : ℝ) * u) - evenCeil ((N : ℝ) * t')) q.2.1 q.2.2 ω₂)) := by
  classical
  let F := smoothedProductFourTest Φ w
  let G : ((Site × Site) × (Site × Site)) → ℝ := fun q =>
    ((N : ℝ) / 4 * pointToPoint (criticalBeta ϑ N)
      (evenCeil ((N : ℝ) * s))
      (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) q.1.1 q.1.2 ω₁) *
    ((N : ℝ) / 4 * pointToPoint (criticalBeta ϑ N)
      (evenCeil ((N : ℝ) * t'))
      (evenCeil ((N : ℝ) * u) - evenCeil ((N : ℝ) * t')) q.2.1 q.2.2 ω₂)
  have hFc : Continuous F := by
    change Continuous (fun p : (Plane × Plane) × (Plane × Plane) =>
      Φ (p.1.1, p.2.2) * w (p.1.2 - p.2.1))
    fun_prop
  obtain ⟨CΦ, hΦbound⟩ := Φ.continuous.bounded_above_of_compact_support Φ.hasCompactSupport
  obtain ⟨Cw, hwbound⟩ := hw.bounded_above_of_compact_support hwc
  have hΦnonneg : 0 ≤ CΦ := (norm_nonneg _).trans (hΦbound 0)
  have hwnonneg : 0 ≤ Cw := (norm_nonneg _).trans (hwbound 0)
  have hFbound : ∀ p, ‖F p‖ ≤ CΦ * Cw := by
    intro p
    dsimp [F, smoothedProductFourTest]
    calc
      ‖Φ (p.1.1, p.2.2) * w (p.1.2 - p.2.1)‖ =
          ‖Φ (p.1.1, p.2.2)‖ * ‖w (p.1.2 - p.2.1)‖ := norm_mul _ _
      _ ≤ CΦ * ‖w (p.1.2 - p.2.1)‖ :=
        mul_le_mul_of_nonneg_right (hΦbound _) (norm_nonneg _)
      _ ≤ CΦ * Cw := mul_le_mul_of_nonneg_left (hwbound _) hΦnonneg
  have hsum := integral_finiteLatticeFourStep_test_eq_cellSum N hN F hFc.measurable
    (CΦ * Cw) hFbound G Q (by simpa [F, G] using hzero)
  have hd₁ : Measurable (fun p : Plane × Plane =>
      ENNReal.ofReal (rescaledP2P ϑ N s t p ω₁)) :=
    ENNReal.measurable_ofReal.comp
      (SHF.Moments.measurable_uncurry_rescaledP2P ϑ N s t |>.of_uncurry_right)
  have hd₂ : Measurable (fun p : Plane × Plane =>
      ENNReal.ofReal (rescaledP2P ϑ N t' u p ω₂)) :=
    ENNReal.measurable_ofReal.comp
      (SHF.Moments.measurable_uncurry_rescaledP2P ϑ N t' u |>.of_uncurry_right)
  have hdens : Measurable (fun q : (Plane × Plane) × (Plane × Plane) =>
      ENNReal.ofReal (rescaledP2P ϑ N s t q.1 ω₁) *
        ENNReal.ofReal (rescaledP2P ϑ N t' u q.2 ω₂)) := by
    exact (hd₁.comp measurable_fst).mul (hd₂.comp measurable_snd)
  have hdensity : smoothedProductPairing (polymerMeasure ϑ N s t ω₁) w
      (polymerMeasure ϑ N t' u ω₂) Φ =
      ∫ q : (Plane × Plane) × (Plane × Plane),
        (rescaledP2P ϑ N s t q.1 ω₁ * rescaledP2P ϑ N t' u q.2 ω₂) *
          smoothedProductFourTest Φ w q
          ∂((volume : Measure (Plane × Plane)).prod volume) := by
    rw [smoothedProductPairing, polymerMeasure, polymerMeasure,
      prod_withDensity hd₁ hd₂,
      integral_withDensity_eq_integral_toReal_smul hdens]
    · apply integral_congr_ae
      filter_upwards [] with q
      have h₁ := SHF.Moments.rescaledP2P_nonneg ϑ N s t q.1 ω₁
      have h₂ := SHF.Moments.rescaledP2P_nonneg ϑ N t' u q.2 ω₂
      rw [← ENNReal.ofReal_mul h₁, ENNReal.toReal_ofReal (mul_nonneg h₁ h₂)]
      simp only [smul_eq_mul]
      simp only [smoothedProductFourTest]
    · filter_upwards [] with q
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hintegrand :
      (fun p : (Plane × Plane) × (Plane × Plane) =>
        (rescaledP2P ϑ N s t p.1 ω₁ * rescaledP2P ϑ N t' u p.2 ω₂) *
          smoothedProductFourTest Φ w p) =
      (fun p => F p * G ((latticePoint N p.1.1, latticePoint N p.1.2),
        (latticePoint N p.2.1, latticePoint N p.2.2))) := by
    funext p
    simp only [F, G, smoothedProductFourTest, rescaledP2P]
    ring
  calc
    _ = ∫ p : (Plane × Plane) × (Plane × Plane),
        (rescaledP2P ϑ N s t p.1 ω₁ * rescaledP2P ϑ N t' u p.2 ω₂) *
          smoothedProductFourTest Φ w p
        ∂((volume : Measure (Plane × Plane)).prod volume) := hdensity
    _ = ∫ p : (Plane × Plane) × (Plane × Plane),
        F p * G ((latticePoint N p.1.1, latticePoint N p.1.2),
          (latticePoint N p.2.1, latticePoint N p.2.2))
        ∂((volume : Measure (Plane × Plane)).prod volume) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (congrFun hintegrand)
    _ = ∑ q ∈ Q,
        (∫ p in (cell N q.1.1 ×ˢ cell N q.1.2) ×ˢ
          (cell N q.2.1 ×ˢ cell N q.2.2), F p
          ∂((volume : Measure (Plane × Plane)).prod volume)) * G q := hsum
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q hq
      rfl

/-- Fubini on a pair of finite lattice cells. -/
theorem integral_cellPair_eq_iterated (N : ℕ) (hN : 0 < N)
    (G : Plane × Plane → ℝ) (hGm : Measurable G) (C : ℝ)
    (hGbound : ∀ p, ‖G p‖ ≤ C) (a b : Site) :
    ∫ p in cell N a ×ˢ cell N b, G p =
      ∫ x in cell N a, ∫ y in cell N b, G (x, y) := by
  classical
  have hcellFinite (r : Site) : volume (cell N r) < ⊤ := by
    by_cases hr : r ∈ evenLattice
    · exact volume_cell_lt_top hN hr
    · simp [cell_eq_empty_of_not_even hr]
  have hprodFinite : (volume.restrict (cell N a)).prod
      (volume.restrict (cell N b)) Set.univ < ⊤ := by
    rw [← Set.univ_prod_univ, Measure.prod_prod,
      Measure.restrict_apply_univ, Measure.restrict_apply_univ]
    exact ENNReal.mul_lt_top (hcellFinite a) (hcellFinite b)
  have hGint : Integrable G ((volume.restrict (cell N a)).prod
      (volume.restrict (cell N b))) := by
    have hconst : Integrable (fun _ : Plane × Plane => C)
        ((volume.restrict (cell N a)).prod (volume.restrict (cell N b))) := by
      simpa [IntegrableOn] using
        (integrableOn_const (μ := (volume.restrict (cell N a)).prod
          (volume.restrict (cell N b))) (s := Set.univ) (C := C) hprodFinite.ne)
    apply hconst.mono' hGm.aestronglyMeasurable
    filter_upwards [] with p
    exact hGbound p
  have hrestrict : (volume : Measure (Plane × Plane)).restrict
      (cell N a ×ˢ cell N b) =
        (volume.restrict (cell N a)).prod (volume.restrict (cell N b)) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  calc
    ∫ p in cell N a ×ˢ cell N b, G p =
        ∫ p, G p ∂((volume.restrict (cell N a)).prod (volume.restrict (cell N b))) := by
          rw [← hrestrict]
    _ = ∫ x, ∫ y, G (x, y) ∂(volume.restrict (cell N b))
        ∂(volume.restrict (cell N a)) := integral_prod _ hGint
    _ = ∫ x in cell N a, ∫ y in cell N b, G (x, y) := rfl

/-- The four-cell smoothed test factors into its outer endpoint test and its middle connector
test. This is the cellwise factorization used to identify annealing with the continuum kernel
pairing. -/
theorem smoothedProductFourTest_integral_cell_factor (N : ℕ) (hN : 0 < N)
    (Φ : C_c(Plane × Plane, ℝ)) (w : Plane → ℝ) (hw : Continuous w)
    (hwc : HasCompactSupport w) (x a y z : Site) :
    ∫ p in (cell N x ×ˢ cell N a) ×ˢ (cell N y ×ˢ cell N z),
        smoothedProductFourTest Φ w p ∂((volume : Measure (Plane × Plane)).prod volume) =
      (∫ p in cell N x ×ˢ cell N z, Φ p) *
        (∫ p in cell N a ×ˢ cell N y, w (p.1 - p.2)) := by
  classical
  let μ : Measure (Plane × Plane) := volume
  let A : Set (Plane × Plane) := cell N x ×ˢ cell N a
  let B : Set (Plane × Plane) := cell N y ×ˢ cell N z
  let F : (Plane × Plane) × (Plane × Plane) → ℝ := smoothedProductFourTest Φ w
  have hcellFinite (r : Site) : volume (cell N r) < ⊤ := by
    by_cases hr : r ∈ evenLattice
    · exact volume_cell_lt_top hN hr
    · simp [cell_eq_empty_of_not_even hr]
  have hpairFinite (r q : Site) : μ (cell N r ×ˢ cell N q) < ⊤ := by
    dsimp [μ]
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_lt_top (hcellFinite r) (hcellFinite q)
  have hprodFinite : (μ.restrict A).prod (μ.restrict B) Set.univ < ⊤ := by
    rw [← Set.univ_prod_univ, Measure.prod_prod,
      Measure.restrict_apply_univ, Measure.restrict_apply_univ]
    exact ENNReal.mul_lt_top (by simpa [A, μ] using hpairFinite x a)
      (by simpa [B, μ] using hpairFinite y z)
  obtain ⟨CΦ, hΦbound⟩ := Φ.continuous.bounded_above_of_compact_support Φ.hasCompactSupport
  obtain ⟨Cw, hwbound⟩ := hw.bounded_above_of_compact_support hwc
  have hCΦ : 0 ≤ CΦ := (norm_nonneg _).trans (hΦbound 0)
  have hCw : 0 ≤ Cw := (norm_nonneg _).trans (hwbound 0)
  have hFbound (p : (Plane × Plane) × (Plane × Plane)) : ‖F p‖ ≤ CΦ * Cw := by
    dsimp [F, smoothedProductFourTest]
    calc
      ‖Φ (p.1.1, p.2.2) * w (p.1.2 - p.2.1)‖ =
          ‖Φ (p.1.1, p.2.2)‖ * ‖w (p.1.2 - p.2.1)‖ := norm_mul _ _
      _ ≤ CΦ * ‖w (p.1.2 - p.2.1)‖ :=
        mul_le_mul_of_nonneg_right (hΦbound _) (norm_nonneg _)
      _ ≤ CΦ * Cw := mul_le_mul_of_nonneg_left (hwbound _) hCΦ
  have hFmeas : Measurable F := by
    change Measurable (fun p : (Plane × Plane) × (Plane × Plane) =>
      Φ (p.1.1, p.2.2) * w (p.1.2 - p.2.1))
    fun_prop
  have hFint : Integrable F ((μ.restrict A).prod (μ.restrict B)) := by
    have hconst : Integrable (fun _ : (Plane × Plane) × (Plane × Plane) => CΦ * Cw)
        ((μ.restrict A).prod (μ.restrict B)) := by
      simpa [IntegrableOn] using
        (integrableOn_const (μ := (μ.restrict A).prod (μ.restrict B)) (s := Set.univ)
          (C := CΦ * Cw) hprodFinite.ne)
    apply hconst.mono' hFmeas.aestronglyMeasurable
    filter_upwards [] with p
    exact hFbound p
  have hinner (r : Plane × Plane) :
      ∫ q, F (r, q) ∂(μ.restrict B) =
        (∫ y' in cell N y, w (r.2 - y')) * (∫ z' in cell N z, Φ (r.1, z')) := by
    have hB : μ.restrict B = (volume.restrict (cell N y)).prod
        (volume.restrict (cell N z)) := by
      dsimp [μ, B]
      rw [Measure.volume_eq_prod, Measure.prod_restrict]
    rw [hB]
    calc
      ∫ q, F (r, q) ∂(volume.restrict (cell N y)).prod (volume.restrict (cell N z)) =
          ∫ q, w (r.2 - q.1) * Φ (r.1, q.2)
            ∂(volume.restrict (cell N y)).prod (volume.restrict (cell N z)) := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun q => by
                dsimp [F, smoothedProductFourTest]
                ring
      _ = (∫ y' in cell N y, w (r.2 - y')) *
            (∫ z' in cell N z, Φ (r.1, z')) := by
              exact (integral_prod_mul (μ := volume.restrict (cell N y))
                (ν := volume.restrict (cell N z))
                (fun y' => w (r.2 - y')) (fun z' => Φ (r.1, z')))
  calc
    _ = ∫ r : Plane × Plane in A, ∫ q in B, F (r, q) ∂μ ∂μ := by
          rw [← Measure.prod_restrict A B]
          rw [integral_prod _ hFint]
    _ = ∫ r : Plane × Plane in A,
          (∫ y' in cell N y, w (r.2 - y')) * (∫ z' in cell N z, Φ (r.1, z')) ∂μ := by
            apply setIntegral_congr_fun ((measurableSet_cell N x).prod
              (measurableSet_cell N a))
            intro r hr
            exact hinner r
    _ = (∫ x' in cell N x, ∫ z' in cell N z, Φ (x', z')) *
          (∫ a' in cell N a, ∫ y' in cell N y, w (a' - y')) := by
            calc
              _ = ∫ r : Plane × Plane in cell N x ×ˢ cell N a,
                    (∫ z' in cell N z, Φ (r.1, z')) *
                    (∫ y' in cell N y, w (r.2 - y')) ∂μ := by
                      apply setIntegral_congr_fun ((measurableSet_cell N x).prod
                        (measurableSet_cell N a))
                      intro r hr
                      ring
              _ = _ := by
                exact setIntegral_prod_mul
                  (fun x' : Plane => ∫ z' in cell N z, Φ (x', z'))
                  (fun a' : Plane => ∫ y' in cell N y, w (a' - y'))
                  (cell N x) (cell N a)
    _ = _ := by
      rw [← integral_cellPair_eq_iterated N hN Φ Φ.continuous.measurable CΦ hΦbound x z]
      have hWm : Measurable (fun p : Plane × Plane => w (p.1 - p.2)) := by fun_prop
      have hWbound : ∀ p : Plane × Plane, ‖w (p.1 - p.2)‖ ≤ Cw :=
        fun p => hwbound (p.1 - p.2)
      rw [← integral_cellPair_eq_iterated N hN (fun p : Plane × Plane => w (p.1 - p.2))
        hWm Cw hWbound a y]

/-- A finite four-cell support set for any compact outer test and compact connector. -/
theorem exists_smoothedProductSiteSupport (ϑ : ℝ) (N : ℕ) (s t t' u : ℝ)
    (Φ : C_c(Plane × Plane, ℝ)) :
    ∃ Q : Finset ((Site × Site) × (Site × Site)),
      ∀ ω w q, q ∉ Q → ∀ p ∈
        (cell N q.1.1 ×ˢ cell N q.1.2) ×ˢ (cell N q.2.1 ×ˢ cell N q.2.2),
          smoothedProductFourTest Φ w p *
            smoothedProductSiteCoefficient ϑ N s t t' u ω q = 0 := by
  classical
  let Sx : Finset Site := (finite_latticePoint_image_of_bounded (N := N)
    (Φ.hasCompactSupport.image continuous_fst).isBounded).toFinset
  let Sz : Finset Site := (finite_latticePoint_image_of_bounded (N := N)
    (Φ.hasCompactSupport.image continuous_snd).isBounded).toFinset
  let n₁ := evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)
  let n₂ := evenCeil ((N : ℝ) * u) - evenCeil ((N : ℝ) * t')
  let Q : Finset ((Site × Site) × (Site × Site)) :=
    (Sx.product Sz).biUnion fun xz =>
      ((Polymer.endpoints xz.1 n₁).product (Polymer.endpoints xz.2 n₂)).image
        (fun ay => ((xz.1, ay.1), (ay.2, xz.2)))
  refine ⟨Q, ?_⟩
  intro ω w q hq p hp
  by_cases hΦ : Φ (p.1.1, p.2.2) = 0
  · simp [smoothedProductFourTest, hΦ]
  by_cases hcoef : smoothedProductSiteCoefficient ϑ N s t t' u ω q = 0
  · simp [hcoef]
  have hcoef' :
      (((N : ℝ) / 4) * pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s)) n₁
        q.1.1 q.1.2 ω) *
      (((N : ℝ) / 4) * pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * t')) n₂
        q.2.1 q.2.2 ω) ≠ 0 := by
    simpa only [smoothedProductSiteCoefficient] using hcoef
  have hleft : ((N : ℝ) / 4) * pointToPoint (criticalBeta ϑ N)
      (evenCeil ((N : ℝ) * s)) n₁ q.1.1 q.1.2 ω ≠ 0 :=
    (mul_ne_zero_iff.mp hcoef').1
  have hright : ((N : ℝ) / 4) * pointToPoint (criticalBeta ϑ N)
      (evenCeil ((N : ℝ) * t')) n₂ q.2.1 q.2.2 ω ≠ 0 :=
    (mul_ne_zero_iff.mp hcoef').2
  have hpt₁ : pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s)) n₁
      q.1.1 q.1.2 ω ≠ 0 := by
    intro hz
    apply hleft
    simp [hz]
  have hpt₂ : pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * t')) n₂
      q.2.1 q.2.2 ω ≠ 0 := by
    intro hz
    apply hright
    simp [hz]
  have hreach₁ : Polymer.Reachable n₁ q.1.1 q.1.2 := by
    by_contra hn
    exact hpt₁ ((Polymer.pointToPoint_eq_zero_iff _ _ _ _ _ _).2 hn)
  have hreach₂ : Polymer.Reachable n₂ q.2.1 q.2.2 := by
    by_contra hn
    exact hpt₂ ((Polymer.pointToPoint_eq_zero_iff _ _ _ _ _ _).2 hn)
  have hpK : (p.1.1, p.2.2) ∈ tsupport Φ :=
    subset_closure (Function.mem_support.mpr hΦ)
  have hfirst : q.1.1 ∈ Sx := by
    apply (finite_latticePoint_image_of_bounded (N := N)
      (Φ.hasCompactSupport.image continuous_fst).isBounded).mem_toFinset.mpr
    exact ⟨p.1.1, ⟨(p.1.1, p.2.2), hpK, rfl⟩,
      (mem_cell_iff N q.1.1 p.1.1).mp hp.1.1⟩
  have hlast : q.2.2 ∈ Sz := by
    apply (finite_latticePoint_image_of_bounded (N := N)
      (Φ.hasCompactSupport.image continuous_snd).isBounded).mem_toFinset.mpr
    exact ⟨p.2.2, ⟨(p.1.1, p.2.2), hpK, rfl⟩,
      (mem_cell_iff N q.2.2 p.2.2).mp hp.2.2⟩
  have hmid₁ : q.1.2 ∈ Polymer.endpoints q.1.1 n₁ :=
    (Polymer.mem_endpoints_iff _ _ _).2 hreach₁
  have hmid₂ : q.2.1 ∈ Polymer.endpoints q.2.2 n₂ :=
    mem_endpoints_reverse ((Polymer.mem_endpoints_iff _ _ _).2 hreach₂)
  have hqQ : q ∈ Q := by
    have hmem : q ∈ (Sx.product Sz).biUnion (fun xz =>
      ((Polymer.endpoints xz.1 n₁).product (Polymer.endpoints xz.2 n₂)).image
        (fun ay => ((xz.1, ay.1), (ay.2, xz.2))))
      := Finset.mem_biUnion.mpr ⟨(q.1.1, q.2.2),
      Finset.mem_product.mpr ⟨hfirst, hlast⟩,
      Finset.mem_image.mpr ⟨(q.1.2, q.2.1),
        Finset.mem_product.mpr ⟨hmid₁, hmid₂⟩, rfl⟩⟩
    simpa only [Q] using hmem
  exact (hq hqQ).elim

/-- A smoothed product of two finite-scale polymer measures is square-integrable; its finite
four-cell expansion is given by `smoothedProductPairing_polymer_eq_finiteCellSum`. -/
theorem memLp_smoothedProductPairing_two (ϑ : ℝ) (N : ℕ) (s t t' u : ℝ)
    (Φ : C_c(Plane × Plane, ℝ)) (w : Plane → ℝ) (hw : Continuous w)
    (hwc : HasCompactSupport w) :
    MemLp (fun ω => smoothedProductPairing (polymerMeasure ϑ N s t ω) w
      (polymerMeasure ϑ N t' u ω) Φ) 2 disorderLaw := by
  classical
  by_cases hN : N = 0
  · subst N
    simp [smoothedProductPairing, polymerMeasure_zero_at_zero]
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    obtain ⟨Q, hQ⟩ := exists_smoothedProductSiteSupport ϑ N s t t' u Φ
    let c : ((Site × Site) × (Site × Site)) → ℝ := fun q =>
      ∫ p in (cell N q.1.1 ×ˢ cell N q.1.2) ×ˢ (cell N q.2.1 ×ˢ cell N q.2.2),
        smoothedProductFourTest Φ w p
        ∂((volume : Measure (Plane × Plane)).prod volume)
    have hsum (ω : Disorder) :
        smoothedProductPairing (polymerMeasure ϑ N s t ω) w
          (polymerMeasure ϑ N t' u ω) Φ =
          ∑ q ∈ Q, c q * smoothedProductSiteCoefficient ϑ N s t t' u ω q := by
      exact smoothedProductPairing_polymer_eq_finiteCellSum ϑ N hNpos s t t' u ω Φ w hw hwc Q
        (by simpa only [smoothedProductSiteCoefficient] using hQ ω w)
    have hterm (q : (Site × Site) × (Site × Site)) :
        MemLp (fun ω => c q * smoothedProductSiteCoefficient ϑ N s t t' u ω q)
          2 disorderLaw := by
      have hpt₁ : MemLp (fun ω => pointToPoint (criticalBeta ϑ N)
          (evenCeil ((N : ℝ) * s))
          (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) q.1.1 q.1.2 ω)
          ((2 : ENNReal) * 2) disorderLaw :=
        Polymer.memLp_pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s))
          (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) q.1.1 q.1.2
          ((2 : ENNReal) * 2) (by norm_num)
      have hpt₂ : MemLp (fun ω => pointToPoint (criticalBeta ϑ N)
          (evenCeil ((N : ℝ) * t'))
          (evenCeil ((N : ℝ) * u) - evenCeil ((N : ℝ) * t')) q.2.1 q.2.2 ω)
          ((2 : ENNReal) * 2) disorderLaw :=
        Polymer.memLp_pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * t'))
          (evenCeil ((N : ℝ) * u) - evenCeil ((N : ℝ) * t')) q.2.1 q.2.2
          ((2 : ENNReal) * 2) (by norm_num)
      have hscale₁ := hpt₁.const_mul ((N : ℝ) / 4)
      have hscale₂ := hpt₂.const_mul ((N : ℝ) / 4)
      have hproduct := Polymer.memLp_mul_double (2 : ℝ≥0∞) hscale₁ hscale₂
      have hconst := hproduct.const_mul (c q)
      convert hconst using 1
      funext ω
      simp only [smoothedProductSiteCoefficient]
    have hsumLp : MemLp (fun ω =>
        ∑ q ∈ Q, c q * smoothedProductSiteCoefficient ϑ N s t t' u ω q)
        2 disorderLaw := by
      apply memLp_finsetSum
      intro q hq
      exact hterm q
    have heq : (fun ω => smoothedProductPairing (polymerMeasure ϑ N s t ω) w
        (polymerMeasure ϑ N t' u ω) Φ) = fun ω =>
          ∑ q ∈ Q, c q * smoothedProductSiteCoefficient ϑ N s t t' u ω q := by
      funext ω
      exact hsum ω
    rw [heq]
    exact hsumLp

/-- A finite-scale smoothed polymer pairing is measurable by its finite four-cell expansion. -/
theorem measurable_smoothedProductPairing (ϑ : ℝ) (N : ℕ) (s t t' u : ℝ)
    (Φ : C_c(Plane × Plane, ℝ)) (w : Plane → ℝ) (hw : Continuous w)
    (hwc : HasCompactSupport w) :
    Measurable (fun ω => smoothedProductPairing (polymerMeasure ϑ N s t ω) w
      (polymerMeasure ϑ N t' u ω) Φ) := by
  classical
  by_cases hN : N = 0
  · subst N
    simp [smoothedProductPairing, polymerMeasure_zero_at_zero]
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    obtain ⟨Q, hQ⟩ := exists_smoothedProductSiteSupport ϑ N s t t' u Φ
    let c : ((Site × Site) × (Site × Site)) → ℝ := fun q =>
      ∫ p in (cell N q.1.1 ×ˢ cell N q.1.2) ×ˢ (cell N q.2.1 ×ˢ cell N q.2.2),
        smoothedProductFourTest Φ w p
        ∂((volume : Measure (Plane × Plane)).prod volume)
    have hsum (ω : Disorder) :
        smoothedProductPairing (polymerMeasure ϑ N s t ω) w
          (polymerMeasure ϑ N t' u ω) Φ =
          ∑ q ∈ Q, c q * smoothedProductSiteCoefficient ϑ N s t t' u ω q := by
      exact smoothedProductPairing_polymer_eq_finiteCellSum ϑ N hNpos s t t' u ω Φ w hw hwc Q
        (by simpa only [smoothedProductSiteCoefficient] using hQ ω w)
    rw [show (fun ω => smoothedProductPairing (polymerMeasure ϑ N s t ω) w
        (polymerMeasure ϑ N t' u ω) Φ) = fun ω =>
          ∑ q ∈ Q, c q * smoothedProductSiteCoefficient ϑ N s t t' u ω q by
      funext ω
      exact hsum ω]
    apply Q.measurable_fun_sum
    intro q hq
    have hpt₁ := Polymer.measurable_pointToPoint (criticalBeta ϑ N)
      (evenCeil ((N : ℝ) * s))
      (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) q.1.1 q.1.2
    have hpt₂ := Polymer.measurable_pointToPoint (criticalBeta ϑ N)
      (evenCeil ((N : ℝ) * t'))
      (evenCeil ((N : ℝ) * u) - evenCeil ((N : ℝ) * t')) q.2.1 q.2.2
    change Measurable (fun ω => c q *
      (((N : ℝ) / 4 * pointToPoint (criticalBeta ϑ N)
        (evenCeil ((N : ℝ) * s))
        (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) q.1.1 q.1.2 ω) *
       ((N : ℝ) / 4 * pointToPoint (criticalBeta ϑ N)
        (evenCeil ((N : ℝ) * t'))
        (evenCeil ((N : ℝ) * u) - evenCeil ((N : ℝ) * t')) q.2.1 q.2.2 ω)))
    exact measurable_const.mul
      ((measurable_const.mul hpt₁).mul (measurable_const.mul hpt₂))

end Critical2DKPZ.SHF.Flow

end
