/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.SlabSmoothedConnector

/-! # Conditional expectation for smoothed polymer products -/

@[expose] public noncomputable section

open MeasureTheory
open Critical2DKPZ.SHF.Limit
open Critical2DKPZ.SHF.Tsai
open scoped CompactlySupported

namespace Critical2DKPZ.SHF.Flow

/-- Convolving a compact connector with the annealed slab kernel. -/
def slabSmoothedConnector (ϑ : ℝ) (N : ℕ) (t t' : ℝ) (w : Plane → ℝ)
    (a b : Plane) : ℝ :=
  ∫ y, w (a - y) * slabMeanKernel ϑ N t t' y b

/-- The convolved slab connector is measurable, as a countable sum of cell integrals. -/
theorem measurable_slabSmoothedConnector (ϑ : ℝ) (N : ℕ) (t t' : ℝ)
    (w : Plane → ℝ) (hw : Continuous w) (hwc : HasCompactSupport w) :
    Measurable (fun p : Plane × Plane => slabSmoothedConnector ϑ N t t' w p.1 p.2) := by
  let ψ : Site → Plane → ℝ := fun r a => ∫ y in cell N r, w (a - y)
  let m := evenCeil ((N : ℝ) * t') - evenCeil ((N : ℝ) * t)
  have hψ (r : Site) : Measurable (ψ r) := by
    change Measurable (fun a => ∫ y in cell N r, w (a - y))
    have hsm : StronglyMeasurable (fun p : Plane × Plane => w (p.1 - p.2)) := by
      exact (by fun_prop : Continuous (fun p : Plane × Plane => w (p.1 - p.2))).stronglyMeasurable
    exact (hsm.integral_prod_right' (ν := volume.restrict (cell N r))).measurable
  have hterm (r : Site) : Measurable (fun p : Plane × Plane =>
      ψ r p.1 * srwKernel m (latticePoint N p.2 - r)) := by
    exact (hψ r).comp measurable_fst |>.mul
      ((measurable_of_countable (fun z : Site => srwKernel m (z - r))).comp
        ((measurable_latticePoint N).comp measurable_snd))
  have heq :
      (fun p : Plane × Plane => slabSmoothedConnector ϑ N t t' w p.1 p.2) =
        fun p => (N : ℝ) / 4 * ∑' r : Site,
          ψ r p.1 * srwKernel m (latticePoint N p.2 - r) := by
    funext p
    rw [slabSmoothedConnector, slabSmoothedConnector_eq_cellTsum ϑ N t t'
      p.1 p.2 w hw hwc]
  rw [heq]
  exact measurable_const.mul (Measurable.tsum hterm)

/-- The convolved slab connector is uniformly bounded at each fixed lattice scale. -/
theorem exists_slabSmoothedConnector_bound (ϑ : ℝ) (N : ℕ) (hN : 0 < N)
    (t t' : ℝ) (w : Plane → ℝ) (hw : Continuous w) (hwc : HasCompactSupport w) :
    ∃ C : ℝ, ∀ a b, ‖slabSmoothedConnector ϑ N t t' w a b‖ ≤ C := by
  classical
  obtain ⟨Cw, hwbnd⟩ := hw.bounded_above_of_compact_support hwc
  have hCw : 0 ≤ Cw := (norm_nonneg _).trans (hwbnd 0)
  let m := evenCeil ((N : ℝ) * t') - evenCeil ((N : ℝ) * t)
  let M : ℝ := Fintype.card (Fin m → Fin 4)
  let C : ℝ := ((N : ℝ) / 4) * (M * (Cw * (4 / (N : ℝ))))
  refine ⟨C, ?_⟩
  intro a b
  let R : Finset Site := Polymer.endpoints (latticePoint N b) m
  have hcellFinite (r : Site) : volume (cell N r) < ⊤ := by
    by_cases hr : r ∈ evenLattice
    · exact volume_cell_lt_top hN hr
    · simp [cell_eq_empty_of_not_even hr]
  have hvol (r : Site) : (volume (cell N r)).toReal ≤ 4 / (N : ℝ) := by
    by_cases hr : r ∈ evenLattice
    · rw [volume_cell_toReal hN hr]
    · simp [cell_eq_empty_of_not_even hr]
      positivity
  have hcellInt (r : Site) :
      ‖∫ y in cell N r, w (a - y)‖ ≤ Cw * (4 / (N : ℝ)) := by
    have hconst : Integrable (fun _ : Plane => Cw)
        (volume.restrict (cell N r)) := by
      simpa [IntegrableOn] using
        (integrableOn_const (μ := volume) (s := cell N r) (C := Cw) (hcellFinite r).ne)
    have hnorm := norm_integral_le_of_norm_le hconst
      (Filter.Eventually.of_forall fun y => hwbnd (a - y))
    have hconstIntegral :
        (∫ y, Cw ∂(volume.restrict (cell N r))) =
          Cw * (volume (cell N r)).toReal := by
      rw [integral_const, measureReal_restrict_apply_univ, smul_eq_mul, measureReal_def]
      ring
    calc
      ‖∫ y in cell N r, w (a - y)‖ ≤ Cw * (volume (cell N r)).toReal := by
        simpa [hconstIntegral] using hnorm
      _ ≤ Cw * (4 / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left (hvol r) hCw
  have hkernelNonneg (r : Site) : 0 ≤ srwKernel m (latticePoint N b - r) :=
    Polymer.kernel_nonneg _ _
  have hkernelBound (r : Site) :
      ‖srwKernel m (latticePoint N b - r)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hkernelNonneg r)]
    exact Polymer.srwKernel_le_one _ _
  have htermBound (r : Site) :
      ‖(∫ y in cell N r, w (a - y)) * srwKernel m (latticePoint N b - r)‖ ≤
        Cw * (4 / (N : ℝ)) := by
    rw [norm_mul]
    calc
      ‖∫ y in cell N r, w (a - y)‖ *
          ‖srwKernel m (latticePoint N b - r)‖ ≤
        (Cw * (4 / (N : ℝ))) * ‖srwKernel m (latticePoint N b - r)‖ :=
          mul_le_mul_of_nonneg_right (hcellInt r) (norm_nonneg _)
      _ ≤ Cw * (4 / (N : ℝ)) := by
        calc
          _ ≤ (Cw * (4 / (N : ℝ))) * 1 :=
            mul_le_mul_of_nonneg_left (hkernelBound r) (by positivity)
          _ = _ := by ring
  have htsum : (∑' r : Site,
      (∫ y in cell N r, w (a - y)) * srwKernel m (latticePoint N b - r)) =
        ∑ r ∈ R,
          (∫ y in cell N r, w (a - y)) * srwKernel m (latticePoint N b - r) := by
    rw [tsum_eq_sum (s := R)]
    intro r hr
    have hz : srwKernel m (latticePoint N b - r) = 0 := by
      rw [Polymer.srwKernel_sub_swap]
      apply Polymer.srwKernel_eq_zero_of_not_mem
      simpa [R] using hr
    simp [hz]
  have hcard : R.card ≤ Fintype.card (Fin m → Fin 4) := by
    dsimp [R, Polymer.endpoints]
    exact Finset.card_image_le.trans (by simp)
  have hsumBound :
      ‖∑ r ∈ R,
        (∫ y in cell N r, w (a - y)) * srwKernel m (latticePoint N b - r)‖ ≤
        (R.card : ℝ) * (Cw * (4 / (N : ℝ))) := by
    calc
      _ ≤ ∑ r ∈ R,
          ‖(∫ y in cell N r, w (a - y)) * srwKernel m (latticePoint N b - r)‖ :=
            norm_sum_le _ _
      _ ≤ ∑ _r ∈ R, Cw * (4 / (N : ℝ)) :=
            Finset.sum_le_sum fun r hr => htermBound r
      _ = (R.card : ℝ) * (Cw * (4 / (N : ℝ))) := by simp
  rw [slabSmoothedConnector, slabSmoothedConnector_eq_cellTsum ϑ N t t' a b w hw hwc,
    htsum]
  dsimp [C, M]
  calc
    ‖((N : ℝ) / 4) * ∑ r ∈ R,
        (∫ y in cell N r, w (a - y)) * srwKernel m (latticePoint N b - r)‖ =
      |(N : ℝ) / 4| * ‖∑ r ∈ R,
        (∫ y in cell N r, w (a - y)) * srwKernel m (latticePoint N b - r)‖ := norm_mul _ _
    _ = ((N : ℝ) / 4) * ‖∑ r ∈ R,
        (∫ y in cell N r, w (a - y)) * srwKernel m (latticePoint N b - r)‖ := by
      rw [abs_of_nonneg (by positivity)]
    _ ≤ ((N : ℝ) / 4) * ((R.card : ℝ) * (Cw * (4 / (N : ℝ)))) :=
      mul_le_mul_of_nonneg_left hsumBound (by positivity)
    _ ≤ ((N : ℝ) / 4) *
        ((Fintype.card (Fin m → Fin 4) : ℝ) * (Cw * (4 / (N : ℝ)))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)



/-- Averaging a resampled polymer interval whose first subinterval is empty leaves the walk
kernel for the annealed initial slab followed by the final polymer interval. -/
theorem integral_pointToPoint_resample_startSlab (β : ℝ) {b c d : ℕ}
    (hbc : b ≤ c) (hcd : c ≤ d) (y z : Site) (ω : Disorder) :
    ∫ η, pointToPoint β b (d - b) y z
      (Gaussian.resample (Gaussian.timeBlock b c) η ω) ∂disorderLaw =
      ∑' v, srwKernel (c - b) (v - y) * pointToPoint β c (d - c) v z ω := by
  rw [integral_pointToPoint_resample_slab β (le_rfl) hbc hcd y z ω]
  simp only [Nat.sub_self, Polymer.pointToPoint_zero]
  calc
    _ = ∑' w : Site, if w = y then
          ∑' v : Site, srwKernel (c - b) (v - y) *
            pointToPoint β c (d - c) v z ω else 0 := by
          apply tsum_congr
          intro w
          by_cases hw : w = y
          · subst w
            simp
          · have hwy : y ≠ w := fun h => hw h.symm
            simp [hw, hwy]
    _ = _ := by
          rw [tsum_eq_single y]
          · simp
          · intro w hw
            simp [hw]

/-- The finite endpoint sites selected by the compact support of the outer test. -/
def smoothedBridgeStartSites (N : ℕ) (Φ : C_c(Plane × Plane, ℝ)) : Finset Site :=
  (finite_latticePoint_image_of_bounded (N := N)
    (Φ.hasCompactSupport.image continuous_fst).isBounded).toFinset

/-- The finite terminal sites selected by the compact support of the outer test. -/
def smoothedBridgeEndSites (N : ℕ) (Φ : C_c(Plane × Plane, ℝ)) : Finset Site :=
  (finite_latticePoint_image_of_bounded (N := N)
    (Φ.hasCompactSupport.image continuous_snd).isBounded).toFinset

/-- Reachable first-slab endpoints over the compact start support. -/
def smoothedBridgeLeftSites (N : ℕ) (s t : ℝ) (Φ : C_c(Plane × Plane, ℝ)) : Finset Site :=
  (smoothedBridgeStartSites N Φ).biUnion fun x =>
    Polymer.endpoints x (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s))

/-- A common finite set of middle sites for the resampled product and continuum connector. -/
def smoothedBridgeMiddleSites (N : ℕ) (t t' u : ℝ)
    (Φ : C_c(Plane × Plane, ℝ)) : Finset Site :=
  (smoothedBridgeEndSites N Φ).biUnion fun z =>
    Polymer.endpoints z (evenCeil ((N : ℝ) * u) - evenCeil ((N : ℝ) * t)) ∪
      (Polymer.endpoints z (evenCeil ((N : ℝ) * u) - evenCeil ((N : ℝ) * t')) ∪
        (Polymer.endpoints z (evenCeil ((N : ℝ) * u) - evenCeil ((N : ℝ) * t'))).biUnion
          fun b => Polymer.endpoints b
            (evenCeil ((N : ℝ) * t') - evenCeil ((N : ℝ) * t)))

/-- A common finite set of four-site indices for the smoothed resampling expansion and its
continuum conditional mean. -/
def smoothedProductBridgeSupport (N : ℕ) (s t t' u : ℝ)
    (Φ : C_c(Plane × Plane, ℝ)) : Finset ((Site × Site) × (Site × Site)) :=
  ((smoothedBridgeStartSites N Φ).product (smoothedBridgeLeftSites N s t Φ)).product
    ((smoothedBridgeMiddleSites N t t' u Φ).product (smoothedBridgeEndSites N Φ))


/-- The common support contains every nonzero resampled smoothed-product cell term when the two
outer polymer intervals use different disorder configurations. -/
theorem smoothedProductBridgeSupport_left_mixed (ϑ : ℝ) (N : ℕ) (s t t' u : ℝ)
    (Φ : C_c(Plane × Plane, ℝ)) (ω₁ ω₂ : Disorder) (w : Plane → ℝ)
    (q : (Site × Site) × (Site × Site))
    (hq : q ∉ smoothedProductBridgeSupport N s t t' u Φ)
    (p : (Plane × Plane) × (Plane × Plane))
    (hp : p ∈ (cell N q.1.1 ×ˢ cell N q.1.2) ×ˢ
      (cell N q.2.1 ×ˢ cell N q.2.2)) :
    smoothedProductFourTest Φ w p *
      (((N : ℝ) / 4 * pointToPoint (criticalBeta ϑ N)
          (evenCeil ((N : ℝ) * s))
          (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) q.1.1 q.1.2 ω₁) *
        ((N : ℝ) / 4 * pointToPoint (criticalBeta ϑ N)
          (evenCeil ((N : ℝ) * t))
          (evenCeil ((N : ℝ) * u) - evenCeil ((N : ℝ) * t)) q.2.1 q.2.2 ω₂)) = 0 := by
  classical
  let Sx : Finset Site := (finite_latticePoint_image_of_bounded (N := N)
    (Φ.hasCompactSupport.image continuous_fst).isBounded).toFinset
  let Sz : Finset Site := (finite_latticePoint_image_of_bounded (N := N)
    (Φ.hasCompactSupport.image continuous_snd).isBounded).toFinset
  let n₁ := evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)
  let n₂ := evenCeil ((N : ℝ) * u) - evenCeil ((N : ℝ) * t)
  let n₃ := evenCeil ((N : ℝ) * u) - evenCeil ((N : ℝ) * t')
  let m := evenCeil ((N : ℝ) * t') - evenCeil ((N : ℝ) * t)
  let A : Finset Site := Sx.biUnion fun x => Polymer.endpoints x n₁
  let V : Finset Site := Sz.biUnion fun z =>
    Polymer.endpoints z n₂ ∪
      (Polymer.endpoints z n₃ ∪
        (Polymer.endpoints z n₃).biUnion fun b => Polymer.endpoints b m)
  change q ∉ (Sx.product A).product (V.product Sz) at hq
  by_cases hΦ : Φ (p.1.1, p.2.2) = 0
  · simp [smoothedProductFourTest, hΦ]
  by_cases hfirst : pointToPoint (criticalBeta ϑ N)
      (evenCeil ((N : ℝ) * s)) n₁ q.1.1 q.1.2 ω₁ = 0
  · simp [n₁, hfirst]
  by_cases hlast : pointToPoint (criticalBeta ϑ N)
      (evenCeil ((N : ℝ) * t)) n₂ q.2.1 q.2.2 ω₂ = 0
  · simp [n₂, hlast]
  have hpK : (p.1.1, p.2.2) ∈ tsupport Φ :=
    subset_closure (Function.mem_support.mpr hΦ)
  have hxS : q.1.1 ∈ Sx := by
    apply (finite_latticePoint_image_of_bounded (N := N)
      (Φ.hasCompactSupport.image continuous_fst).isBounded).mem_toFinset.mpr
    exact ⟨p.1.1, ⟨(p.1.1, p.2.2), hpK, rfl⟩,
      (mem_cell_iff N q.1.1 p.1.1).mp hp.1.1⟩
  have hzS : q.2.2 ∈ Sz := by
    apply (finite_latticePoint_image_of_bounded (N := N)
      (Φ.hasCompactSupport.image continuous_snd).isBounded).mem_toFinset.mpr
    exact ⟨p.2.2, ⟨(p.1.1, p.2.2), hpK, rfl⟩,
      (mem_cell_iff N q.2.2 p.2.2).mp hp.2.2⟩
  have hfirstPos : 0 < pointToPoint (criticalBeta ϑ N)
      (evenCeil ((N : ℝ) * s)) n₁ q.1.1 q.1.2 ω₁ :=
    lt_of_le_of_ne (Polymer.pointToPoint_nonneg _ _ _ _ _ _) (Ne.symm hfirst)
  have hfirstReach : Polymer.Reachable n₁ q.1.1 q.1.2 :=
    (Polymer.pointToPoint_pos_iff _ _ _ _ _ _).mp hfirstPos
  have hlastPos : 0 < pointToPoint (criticalBeta ϑ N)
      (evenCeil ((N : ℝ) * t)) n₂ q.2.1 q.2.2 ω₂ :=
    lt_of_le_of_ne (Polymer.pointToPoint_nonneg _ _ _ _ _ _) (Ne.symm hlast)
  have hlastReach : Polymer.Reachable n₂ q.2.1 q.2.2 :=
    (Polymer.pointToPoint_pos_iff _ _ _ _ _ _).mp hlastPos
  have haA : q.1.2 ∈ A := by
    apply Finset.mem_biUnion.mpr
    exact ⟨q.1.1, hxS, (Polymer.mem_endpoints_iff _ _ _).2 hfirstReach⟩
  have hyV : q.2.1 ∈ V := by
    apply Finset.mem_biUnion.mpr
    refine ⟨q.2.2, hzS, Finset.mem_union_left _ ?_⟩
    exact mem_endpoints_reverse ((Polymer.mem_endpoints_iff _ _ _).2 hlastReach)
  have hqmem : q ∈ (Sx.product A).product (V.product Sz) := by
    exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hxS, haA⟩,
      Finset.mem_product.mpr ⟨hyV, hzS⟩⟩
  exact (hq hqmem).elim

/-- The same common finite support contains every nonzero four-cell term of the continuum
conditional mean. -/
theorem smoothedProductBridgeSupport_right (ϑ : ℝ) (N : ℕ) (s t t' u : ℝ)
    (Φ : C_c(Plane × Plane, ℝ)) (κ : Plane × Plane → ℝ)
    (ω : Disorder) (q : (Site × Site) × (Site × Site))
    (hq : q ∉ smoothedProductBridgeSupport N s t t' u Φ)
    (p : (Plane × Plane) × (Plane × Plane))
    (hp : p ∈ (cell N q.1.1 ×ˢ cell N q.1.2) ×ˢ
      (cell N q.2.1 ×ˢ cell N q.2.2)) :
    Φ (p.1.1, p.2.2) * κ (p.1.2, p.2.1) *
      smoothedProductSiteCoefficient ϑ N s t t' u ω q = 0 := by
  classical
  let Sx : Finset Site := (finite_latticePoint_image_of_bounded (N := N)
    (Φ.hasCompactSupport.image continuous_fst).isBounded).toFinset
  let Sz : Finset Site := (finite_latticePoint_image_of_bounded (N := N)
    (Φ.hasCompactSupport.image continuous_snd).isBounded).toFinset
  let n₁ := evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)
  let n₃ := evenCeil ((N : ℝ) * u) - evenCeil ((N : ℝ) * t')
  let A : Finset Site := Sx.biUnion fun x => Polymer.endpoints x n₁
  let V : Finset Site := Sz.biUnion fun z =>
    Polymer.endpoints z (evenCeil ((N : ℝ) * u) - evenCeil ((N : ℝ) * t)) ∪
      (Polymer.endpoints z n₃ ∪
        (Polymer.endpoints z n₃).biUnion fun b =>
          Polymer.endpoints b (evenCeil ((N : ℝ) * t') - evenCeil ((N : ℝ) * t)))
  change q ∉ (Sx.product A).product (V.product Sz) at hq
  by_cases hΦ : Φ (p.1.1, p.2.2) = 0
  · simp [hΦ]
  by_cases hfirst : pointToPoint (criticalBeta ϑ N)
      (evenCeil ((N : ℝ) * s)) n₁ q.1.1 q.1.2 ω = 0
  · simp [smoothedProductSiteCoefficient, n₁, hfirst]
  by_cases hlast : pointToPoint (criticalBeta ϑ N)
      (evenCeil ((N : ℝ) * t')) n₃ q.2.1 q.2.2 ω = 0
  · simp [smoothedProductSiteCoefficient, n₃, hlast]
  have hpK : (p.1.1, p.2.2) ∈ tsupport Φ :=
    subset_closure (Function.mem_support.mpr hΦ)
  have hxS : q.1.1 ∈ Sx := by
    apply (finite_latticePoint_image_of_bounded (N := N)
      (Φ.hasCompactSupport.image continuous_fst).isBounded).mem_toFinset.mpr
    exact ⟨p.1.1, ⟨(p.1.1, p.2.2), hpK, rfl⟩,
      (mem_cell_iff N q.1.1 p.1.1).mp hp.1.1⟩
  have hzS : q.2.2 ∈ Sz := by
    apply (finite_latticePoint_image_of_bounded (N := N)
      (Φ.hasCompactSupport.image continuous_snd).isBounded).mem_toFinset.mpr
    exact ⟨p.2.2, ⟨(p.1.1, p.2.2), hpK, rfl⟩,
      (mem_cell_iff N q.2.2 p.2.2).mp hp.2.2⟩
  have hfirstPos : 0 < pointToPoint (criticalBeta ϑ N)
      (evenCeil ((N : ℝ) * s)) n₁ q.1.1 q.1.2 ω :=
    lt_of_le_of_ne (Polymer.pointToPoint_nonneg _ _ _ _ _ _) (Ne.symm hfirst)
  have hfirstReach : Polymer.Reachable n₁ q.1.1 q.1.2 :=
    (Polymer.pointToPoint_pos_iff _ _ _ _ _ _).mp hfirstPos
  have hlastPos : 0 < pointToPoint (criticalBeta ϑ N)
      (evenCeil ((N : ℝ) * t')) n₃ q.2.1 q.2.2 ω :=
    lt_of_le_of_ne (Polymer.pointToPoint_nonneg _ _ _ _ _ _) (Ne.symm hlast)
  have hlastReach : Polymer.Reachable n₃ q.2.1 q.2.2 :=
    (Polymer.pointToPoint_pos_iff _ _ _ _ _ _).mp hlastPos
  have haA : q.1.2 ∈ A := by
    apply Finset.mem_biUnion.mpr
    exact ⟨q.1.1, hxS, (Polymer.mem_endpoints_iff _ _ _).2 hfirstReach⟩
  have hbV : q.2.1 ∈ V := by
    apply Finset.mem_biUnion.mpr
    refine ⟨q.2.2, hzS, Finset.mem_union_right _ (Finset.mem_union_left _ ?_)⟩
    exact mem_endpoints_reverse ((Polymer.mem_endpoints_iff _ _ _).2 hlastReach)
  have hqmem : q ∈ (Sx.product A).product (V.product Sz) := by
    exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hxS, haA⟩,
      Finset.mem_product.mpr ⟨hbV, hzS⟩⟩
  exact (hq hqmem).elim

/-- Every site in the common bridge support is on the even lattice, so all cell volumes in its
connector expansion have the normalized area `4/N`. -/
theorem smoothedProductBridgeSupport_even (N : ℕ) (s t t' u : ℝ)
    (hst : s ≤ t) (htt' : t ≤ t') (htu : t' ≤ u) (Φ : C_c(Plane × Plane, ℝ))
    {q : (Site × Site) × (Site × Site)}
    (hq : q ∈ smoothedProductBridgeSupport N s t t' u Φ) :
    q.1.1 ∈ evenLattice ∧ q.1.2 ∈ evenLattice ∧
      q.2.1 ∈ evenLattice ∧ q.2.2 ∈ evenLattice := by
  classical
  let Sx : Finset Site := (finite_latticePoint_image_of_bounded (N := N)
    (Φ.hasCompactSupport.image continuous_fst).isBounded).toFinset
  let Sz : Finset Site := (finite_latticePoint_image_of_bounded (N := N)
    (Φ.hasCompactSupport.image continuous_snd).isBounded).toFinset
  let n₁ := evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)
  let n₂ := evenCeil ((N : ℝ) * u) - evenCeil ((N : ℝ) * t)
  let n₃ := evenCeil ((N : ℝ) * u) - evenCeil ((N : ℝ) * t')
  let m := evenCeil ((N : ℝ) * t') - evenCeil ((N : ℝ) * t)
  let A : Finset Site := Sx.biUnion fun x => Polymer.endpoints x n₁
  let V : Finset Site := Sz.biUnion fun z =>
    Polymer.endpoints z n₂ ∪
      (Polymer.endpoints z n₃ ∪
        (Polymer.endpoints z n₃).biUnion fun b => Polymer.endpoints b m)
  have hn₁ : Even n₁ := by
    dsimp [n₁]
    exact Critical2DKPZ.Smoothing.evenCeil_sub_even
      (mul_le_mul_of_nonneg_left hst (Nat.cast_nonneg N))
  have hn₂ : Even n₂ := by
    dsimp [n₂]
    exact Critical2DKPZ.Smoothing.evenCeil_sub_even
      (mul_le_mul_of_nonneg_left (htt'.trans htu) (Nat.cast_nonneg N))
  have hn₃ : Even n₃ := by
    dsimp [n₃]
    exact Critical2DKPZ.Smoothing.evenCeil_sub_even
      (mul_le_mul_of_nonneg_left htu (Nat.cast_nonneg N))
  have hm : Even m := by
    dsimp [m]
    exact Critical2DKPZ.Smoothing.evenCeil_sub_even
      (mul_le_mul_of_nonneg_left htt' (Nat.cast_nonneg N))
  change q ∈ (Sx.product A).product (V.product Sz) at hq
  rcases Finset.mem_product.mp hq with ⟨hq₁, hq₂⟩
  rcases Finset.mem_product.mp hq₁ with ⟨hxS, haA⟩
  rcases Finset.mem_product.mp hq₂ with ⟨hyV, hzS⟩
  have hstartEven (x : Site) (hx : x ∈ Sx) : x ∈ evenLattice := by
    obtain ⟨x', hx', hEq⟩ :=
      (finite_latticePoint_image_of_bounded (N := N)
        (Φ.hasCompactSupport.image continuous_fst).isBounded).mem_toFinset.mp hx
    rw [← hEq]
    exact latticePoint_mem_evenLattice N x'
  have hendEven (z : Site) (hz : z ∈ Sz) : z ∈ evenLattice := by
    obtain ⟨z', hz', hEq⟩ :=
      (finite_latticePoint_image_of_bounded (N := N)
        (Φ.hasCompactSupport.image continuous_snd).isBounded).mem_toFinset.mp hz
    rw [← hEq]
    exact latticePoint_mem_evenLattice N z'
  have hxEven : q.1.1 ∈ evenLattice := hstartEven q.1.1 hxS
  have hzEven : q.2.2 ∈ evenLattice := hendEven q.2.2 hzS
  have haEven : q.1.2 ∈ evenLattice := by
    rcases Finset.mem_biUnion.mp haA with ⟨x, hx, ha⟩
    exact even_mem_endpoints_of_even (hstartEven x hx) hn₁ ha
  have hyEven : q.2.1 ∈ evenLattice := by
    rcases Finset.mem_biUnion.mp hyV with ⟨z, hz, hy⟩
    rcases Finset.mem_union.mp hy with hy₂ | hyRest
    · exact even_mem_endpoints_of_even (hendEven z hz) hn₂ hy₂
    · rcases Finset.mem_union.mp hyRest with hy₃ | hyMiddle
      · exact even_mem_endpoints_of_even (hendEven z hz) hn₃ hy₃
      · rcases Finset.mem_biUnion.mp hyMiddle with ⟨b, hb, hyb⟩
        have hbEven := even_mem_endpoints_of_even (hendEven z hz) hn₃ hb
        exact even_mem_endpoints_of_even hbEven hm
          hyb
  exact ⟨hxEven, haEven, hyEven, hzEven⟩

/-- Finite Fubini for the two middle lattice sites in an annealed connector. -/
theorem finiteSiteConvolution_fubini (X A V Z : Finset Site)
    (F : Site → Site → Site → ℝ) (W B K : Site → Site → ℝ) :
    ∑ x ∈ X, ∑ a ∈ A, ∑ y ∈ V, ∑ z ∈ Z,
      F x a z * W a y * ∑ b ∈ V, K b y * B b z =
    ∑ x ∈ X, ∑ a ∈ A, ∑ b ∈ V, ∑ z ∈ Z,
      F x a z * B b z * ∑ y ∈ V, W a y * K b y := by
  classical
  calc
    _ = ∑ x ∈ X, ∑ a ∈ A, ∑ y ∈ V, ∑ z ∈ Z, ∑ b ∈ V,
          F x a z * W a y * K b y * B b z := by
            apply Finset.sum_congr rfl
            intro x hx
            apply Finset.sum_congr rfl
            intro a ha
            apply Finset.sum_congr rfl
            intro y hy
            apply Finset.sum_congr rfl
            intro z hz
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b hb
            ring
    _ = ∑ x ∈ X, ∑ a ∈ A, ∑ z ∈ Z, ∑ y ∈ V, ∑ b ∈ V,
          F x a z * W a y * K b y * B b z := by
            apply Finset.sum_congr rfl
            intro x hx
            apply Finset.sum_congr rfl
            intro a ha
            exact Finset.sum_comm
    _ = ∑ x ∈ X, ∑ a ∈ A, ∑ z ∈ Z, ∑ b ∈ V, ∑ y ∈ V,
          F x a z * W a y * K b y * B b z := by
            apply Finset.sum_congr rfl
            intro x hx
            apply Finset.sum_congr rfl
            intro a ha
            apply Finset.sum_congr rfl
            intro z hz
            exact Finset.sum_comm
    _ = ∑ x ∈ X, ∑ a ∈ A, ∑ b ∈ V, ∑ z ∈ Z, ∑ y ∈ V,
          F x a z * W a y * K b y * B b z := by
            apply Finset.sum_congr rfl
            intro x hx
            apply Finset.sum_congr rfl
            intro a ha
            exact Finset.sum_comm
    _ = ∑ x ∈ X, ∑ a ∈ A, ∑ b ∈ V, ∑ z ∈ Z,
          F x a z * B b z * ∑ y ∈ V, W a y * K b y := by
            apply Finset.sum_congr rfl
            intro x hx
            apply Finset.sum_congr rfl
            intro a ha
            apply Finset.sum_congr rfl
            intro b hb
            apply Finset.sum_congr rfl
            intro z hz
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro y hy
            ring

/-- Sum expansion for the rectangular four-site support used in the slab bridge. -/
theorem sum_siteQuad_eq_nested (X A V Z : Finset Site)
    (f : ((Site × Site) × (Site × Site)) → ℝ) :
    ∑ q ∈ (X ×ˢ A) ×ˢ (V ×ˢ Z), f q =
      ∑ x ∈ X, ∑ a ∈ A, ∑ y ∈ V, ∑ z ∈ Z, f ((x, a), (y, z)) := by
  classical
  calc
    _ = ∑ u ∈ X ×ˢ A, ∑ v ∈ V ×ˢ Z, f (u, v) :=
      Finset.sum_product' (X ×ˢ A) (V ×ˢ Z) (fun u v => f (u, v))
    _ = ∑ x ∈ X, ∑ a ∈ A, ∑ v ∈ V ×ˢ Z, f ((x, a), v) := by
      simpa only [Prod.eta] using
        (Finset.sum_product' X A (fun x a => ∑ v ∈ V ×ˢ Z, f ((x, a), v)))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_product' V Z (fun y z => f ((x, a), (y, z)))

/-- A continuum polymer kernel pairing with a bounded measurable connector is an exact finite sum
over four lattice cells whenever its lattice density coefficients and outer test have finite
support. -/
theorem kernelProductPairing_polymer_eq_finiteFourCellSum (ϑ : ℝ) (N : ℕ) (hN : 0 < N)
    (s t t' u : ℝ) (ω : Disorder) (Φ : C_c(Plane × Plane, ℝ))
    (κ : Plane × Plane → ℝ) (hκm : Measurable κ) (C : ℝ)
    (hFbound : ∀ p : (Plane × Plane) × (Plane × Plane),
      ‖Φ (p.1.1, p.2.2) * κ (p.1.2, p.2.1)‖ ≤ C)
    (Q : Finset ((Site × Site) × (Site × Site)))
    (hzero : ∀ q ∉ Q, ∀ p ∈
      (cell N q.1.1 ×ˢ cell N q.1.2) ×ˢ (cell N q.2.1 ×ˢ cell N q.2.2),
        Φ (p.1.1, p.2.2) * κ (p.1.2, p.2.1) *
          (((N : ℝ) / 4 * pointToPoint (criticalBeta ϑ N)
              (evenCeil ((N : ℝ) * s))
              (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) q.1.1 q.1.2 ω) *
            ((N : ℝ) / 4 * pointToPoint (criticalBeta ϑ N)
              (evenCeil ((N : ℝ) * t'))
              (evenCeil ((N : ℝ) * u) - evenCeil ((N : ℝ) * t')) q.2.1 q.2.2 ω)) = 0) :
    kernelProductPairing (polymerMeasure ϑ N s t ω) (fun a b => κ (a, b))
        (polymerMeasure ϑ N t' u ω) Φ =
      ∑ q ∈ Q,
        (∫ p in (cell N q.1.1 ×ˢ cell N q.1.2) ×ˢ
          (cell N q.2.1 ×ˢ cell N q.2.2),
          Φ (p.1.1, p.2.2) * κ (p.1.2, p.2.1)
          ∂((volume : Measure (Plane × Plane)).prod volume)) *
        (((N : ℝ) / 4 * pointToPoint (criticalBeta ϑ N)
            (evenCeil ((N : ℝ) * s))
            (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) q.1.1 q.1.2 ω) *
          ((N : ℝ) / 4 * pointToPoint (criticalBeta ϑ N)
            (evenCeil ((N : ℝ) * t'))
            (evenCeil ((N : ℝ) * u) - evenCeil ((N : ℝ) * t')) q.2.1 q.2.2 ω)) := by
  classical
  let F : (Plane × Plane) × (Plane × Plane) → ℝ := fun p =>
    Φ (p.1.1, p.2.2) * κ (p.1.2, p.2.1)
  let G : ((Site × Site) × (Site × Site)) → ℝ := fun q =>
    ((N : ℝ) / 4 * pointToPoint (criticalBeta ϑ N)
      (evenCeil ((N : ℝ) * s))
      (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) q.1.1 q.1.2 ω) *
    ((N : ℝ) / 4 * pointToPoint (criticalBeta ϑ N)
      (evenCeil ((N : ℝ) * t'))
      (evenCeil ((N : ℝ) * u) - evenCeil ((N : ℝ) * t')) q.2.1 q.2.2 ω)
  have hFm : Measurable F := by
    dsimp [F]
    have houter : Measurable
        (fun p : (Plane × Plane) × (Plane × Plane) => (p.1.1, p.2.2)) := by fun_prop
    have hmiddle : Measurable
        (fun p : (Plane × Plane) × (Plane × Plane) => (p.1.2, p.2.1)) := by fun_prop
    exact (Φ.measurable.comp houter).mul (hκm.comp hmiddle)
  have hsum := integral_finiteLatticeFourStep_test_eq_cellSum N hN F hFm C hFbound G Q
    (by simpa only [F, G] using hzero)
  have hdensity := kernelProductPairing_polymer_eq_densityIntegral ϑ N s t t' u ω
    (fun a b => κ (a, b)) Φ
  have hintegrand :
      (fun p : (Plane × Plane) × (Plane × Plane) =>
        (rescaledP2P ϑ N s t p.1 ω * rescaledP2P ϑ N t' u p.2 ω) *
          (Φ (p.1.1, p.2.2) * κ (p.1.2, p.2.1))) =
      (fun p => F p * G ((latticePoint N p.1.1, latticePoint N p.1.2),
        (latticePoint N p.2.1, latticePoint N p.2.2))) := by
    funext p
    simp only [F, G, rescaledP2P]
    ring
  calc
    _ = ∫ p : (Plane × Plane) × (Plane × Plane),
        (rescaledP2P ϑ N s t p.1 ω * rescaledP2P ϑ N t' u p.2 ω) *
          (Φ (p.1.1, p.2.2) * κ (p.1.2, p.2.1))
        ∂((volume : Measure (Plane × Plane)).prod volume) := hdensity
    _ = ∫ p : (Plane × Plane) × (Plane × Plane),
        F p * G ((latticePoint N p.1.1, latticePoint N p.1.2),
          (latticePoint N p.2.1, latticePoint N p.2.2))
        ∂((volume : Measure (Plane × Plane)).prod volume) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (congrFun hintegrand)
    _ = _ := hsum

/-- On four finite lattice cells, an endpoint test and a connector test factor into their
separate two-cell integrals. -/
theorem integral_fourCell_endpoint_factor (N : ℕ) (hN : 0 < N)
    (Φ : C_c(Plane × Plane, ℝ)) (κ : Plane × Plane → ℝ) (hκm : Measurable κ)
    (Cκ : ℝ) (hκbound : ∀ p, ‖κ p‖ ≤ Cκ)
    (x a b z : Site) :
    ∫ p in (cell N x ×ˢ cell N a) ×ˢ (cell N b ×ˢ cell N z),
        Φ (p.1.1, p.2.2) * κ (p.1.2, p.2.1)
        ∂((volume : Measure (Plane × Plane)).prod volume) =
      (∫ p in cell N x ×ˢ cell N z, Φ p) *
        (∫ p in cell N a ×ˢ cell N b, κ p) := by
  classical
  let μ : Measure (Plane × Plane) := volume
  let A : Set (Plane × Plane) := cell N x ×ˢ cell N a
  let B : Set (Plane × Plane) := cell N b ×ˢ cell N z
  let F : (Plane × Plane) × (Plane × Plane) → ℝ := fun p =>
    Φ (p.1.1, p.2.2) * κ (p.1.2, p.2.1)
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
      (by simpa [B, μ] using hpairFinite b z)
  obtain ⟨CΦ, hΦbound⟩ := Φ.continuous.bounded_above_of_compact_support Φ.hasCompactSupport
  have hCΦ : 0 ≤ CΦ := (norm_nonneg _).trans (hΦbound 0)
  have hFbound (p : (Plane × Plane) × (Plane × Plane)) :
      ‖F p‖ ≤ CΦ * Cκ := by
    dsimp [F]
    calc
      ‖Φ (p.1.1, p.2.2) * κ (p.1.2, p.2.1)‖ =
          ‖Φ (p.1.1, p.2.2)‖ * ‖κ (p.1.2, p.2.1)‖ := norm_mul _ _
      _ ≤ CΦ * ‖κ (p.1.2, p.2.1)‖ :=
        mul_le_mul_of_nonneg_right (hΦbound _) (norm_nonneg _)
      _ ≤ CΦ * Cκ := mul_le_mul_of_nonneg_left (hκbound _) hCΦ
  have hFmeas : Measurable F := by
    dsimp [F]
    have houter : Measurable
        (fun p : (Plane × Plane) × (Plane × Plane) => (p.1.1, p.2.2)) := by fun_prop
    have hmiddle : Measurable
        (fun p : (Plane × Plane) × (Plane × Plane) => (p.1.2, p.2.1)) := by fun_prop
    exact (Φ.measurable.comp houter).mul (hκm.comp hmiddle)
  have hFint : Integrable F ((μ.restrict A).prod (μ.restrict B)) := by
    have hconst : Integrable (fun _ : (Plane × Plane) × (Plane × Plane) => CΦ * Cκ)
        ((μ.restrict A).prod (μ.restrict B)) := by
      simpa [IntegrableOn] using
        (integrableOn_const (μ := (μ.restrict A).prod (μ.restrict B)) (s := Set.univ)
          (C := CΦ * Cκ) hprodFinite.ne)
    apply hconst.mono' hFmeas.aestronglyMeasurable
    filter_upwards [] with p
    exact hFbound p
  have hinner (r : Plane × Plane) :
      ∫ q, F (r, q) ∂(μ.restrict B) =
        (∫ b' in cell N b, κ (r.2, b')) *
          (∫ z' in cell N z, Φ (r.1, z')) := by
    have hB : μ.restrict B = (volume.restrict (cell N b)).prod
        (volume.restrict (cell N z)) := by
      dsimp [μ, B]
      rw [Measure.volume_eq_prod, Measure.prod_restrict]
    rw [hB]
    calc
      ∫ q, F (r, q) ∂(volume.restrict (cell N b)).prod (volume.restrict (cell N z)) =
          ∫ q, κ (r.2, q.1) * Φ (r.1, q.2)
            ∂(volume.restrict (cell N b)).prod (volume.restrict (cell N z)) := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun q => by
                dsimp [F]
                ring
      _ = (∫ b' in cell N b, κ (r.2, b')) *
            (∫ z' in cell N z, Φ (r.1, z')) := by
              exact integral_prod_mul (μ := volume.restrict (cell N b))
                (ν := volume.restrict (cell N z))
                (fun b' => κ (r.2, b')) (fun z' => Φ (r.1, z'))
  calc
    _ = ∫ r : Plane × Plane in A, ∫ q in B, F (r, q) ∂μ ∂μ := by
          rw [← Measure.prod_restrict A B]
          rw [integral_prod _ hFint]
    _ = ∫ r : Plane × Plane in A,
          (∫ b' in cell N b, κ (r.2, b')) *
            (∫ z' in cell N z, Φ (r.1, z')) ∂μ := by
          apply setIntegral_congr_fun ((measurableSet_cell N x).prod
            (measurableSet_cell N a))
          intro r hr
          exact hinner r
    _ = (∫ x' in cell N x, ∫ z' in cell N z, Φ (x', z')) *
          (∫ a' in cell N a, ∫ b' in cell N b, κ (a', b')) := by
          calc
            _ = ∫ r : Plane × Plane in cell N x ×ˢ cell N a,
                  (∫ z' in cell N z, Φ (r.1, z')) *
                    (∫ b' in cell N b, κ (r.2, b')) ∂μ := by
                    apply setIntegral_congr_fun ((measurableSet_cell N x).prod
                      (measurableSet_cell N a))
                    intro r hr
                    ring
            _ = _ := by
              exact setIntegral_prod_mul
                (fun x' : Plane => ∫ z' in cell N z, Φ (x', z'))
                (fun a' : Plane => ∫ b' in cell N b, κ (a', b'))
                (cell N x) (cell N a)
    _ = _ := by
      rw [← integral_cellPair_eq_iterated N hN Φ Φ.continuous.measurable CΦ hΦbound x z]
      have hκpairm : Measurable (fun p : Plane × Plane => κ p) := hκm
      rw [← integral_cellPair_eq_iterated N hN κ hκpairm Cκ hκbound a b]

end Critical2DKPZ.SHF.Flow

end
