/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.SlabSmoothedBridge

/-! # Conditional mean of the smoothed polymer product -/

@[expose] public noncomputable section

open MeasureTheory
open Critical2DKPZ.SHF.Limit
open Critical2DKPZ.SHF.Tsai
open scoped CompactlySupported

namespace Critical2DKPZ.SHF.Flow

/-- The outer test integral over the two lattice endpoint cells. -/
def smoothedBridgeOuterCell (N : ℕ) (Φ : C_c(Plane × Plane, ℝ)) (x z : Site) : ℝ :=
  ∫ p in cell N x ×ˢ cell N z, Φ p

/-- The connector test integral over two lattice cells. -/
def smoothedBridgeConnectorCell (N : ℕ) (w : Plane → ℝ) (x y : Site) : ℝ :=
  ∫ p in cell N x ×ˢ cell N y, w (p.1 - p.2)

/-- The first polymer's cell density coefficient. -/
def smoothedBridgeFirstDensity (ϑ : ℝ) (N : ℕ) (s t : ℝ) (ω : Disorder)
    (x y : Site) : ℝ :=
  (N : ℝ) / 4 * pointToPoint (criticalBeta ϑ N)
    (evenCeil ((N : ℝ) * s))
    (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) x y ω

/-- The final polymer's cell density coefficient. -/
def smoothedBridgeLastDensity (ϑ : ℝ) (N : ℕ) (t' u : ℝ) (ω : Disorder)
    (x y : Site) : ℝ :=
  (N : ℝ) / 4 * pointToPoint (criticalBeta ϑ N)
    (evenCeil ((N : ℝ) * t'))
    (evenCeil ((N : ℝ) * u) - evenCeil ((N : ℝ) * t')) x y ω

/-- The annealed resampled smoothed product has this exact finite nested cell expansion. -/
theorem integral_smoothedProductPairing_resample_slab_finiteExpansion
    (ϑ : ℝ) (N : ℕ) (hN : 0 < N) {s t t' u : ℝ}
    (_hs : 0 ≤ s) (hst : s < t) (htt' : t < t') (ht'u : t' < u)
    (Φ : C_c(Plane × Plane, ℝ)) (w : Plane → ℝ) (hw : Continuous w)
    (hwc : HasCompactSupport w) (ω : Disorder) :
    ∫ η, smoothedProductPairing (polymerMeasure ϑ N s t ω) w
      (polymerMeasure ϑ N t u
        (Gaussian.resample (Gaussian.timeBlock (evenCeil ((N : ℝ) * t))
          (evenCeil ((N : ℝ) * t'))) η ω)) Φ ∂disorderLaw =
      ∑ x ∈ smoothedBridgeStartSites N Φ,
          ∑ x₁ ∈ smoothedBridgeLeftSites N s t Φ,
            ∑ y ∈ smoothedBridgeMiddleSites N t t' u Φ,
              ∑ z ∈ smoothedBridgeEndSites N Φ,
                (((N : ℝ) / 4 * smoothedBridgeOuterCell N Φ x z) *
                    smoothedBridgeFirstDensity ϑ N s t ω x x₁) *
                  smoothedBridgeConnectorCell N w x₁ y *
                  ∑ b' ∈ smoothedBridgeMiddleSites N t t' u Φ,
                    srwKernel (evenCeil ((N : ℝ) * t') - evenCeil ((N : ℝ) * t))
                        (b' - y) *
                      pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * t'))
                        (evenCeil ((N : ℝ) * u) - evenCeil ((N : ℝ) * t')) b' z ω := by
  classical
  let a := evenCeil ((N : ℝ) * s)
  let b := evenCeil ((N : ℝ) * t)
  let c := evenCeil ((N : ℝ) * t')
  let d := evenCeil ((N : ℝ) * u)
  have hab : a ≤ b := by
    dsimp [a, b]
    exact Critical2DKPZ.evenCeil_mono
      (mul_le_mul_of_nonneg_left (le_of_lt hst) (Nat.cast_nonneg N))
  have hbc : b ≤ c := by
    dsimp [b, c]
    exact Critical2DKPZ.evenCeil_mono
      (mul_le_mul_of_nonneg_left (le_of_lt htt') (Nat.cast_nonneg N))
  have hcd : c ≤ d := by
    dsimp [c, d]
    exact Critical2DKPZ.evenCeil_mono
      (mul_le_mul_of_nonneg_left (le_of_lt ht'u) (Nat.cast_nonneg N))
  let X := smoothedBridgeStartSites N Φ
  let Z := smoothedBridgeEndSites N Φ
  let n₁ := b - a
  let n₂ := d - b
  let n₃ := d - c
  let m := c - b
  let A := smoothedBridgeLeftSites N s t Φ
  let V := smoothedBridgeMiddleSites N t t' u Φ
  let Q := smoothedProductBridgeSupport N s t t' u Φ
  have hQdef : Q = (X.product A).product (V.product Z) := by rfl
  have hQsum {f : ((Site × Site) × (Site × Site)) → ℝ} :
      ∑ q ∈ Q, f q = ∑ x ∈ X, ∑ x₁ ∈ A, ∑ y ∈ V, ∑ z ∈ Z,
        f ((x, x₁), (y, z)) := by
    rw [hQdef]
    exact sum_siteQuad_eq_nested X A V Z f
  let Y : Disorder → ℝ := fun η =>
    smoothedProductPairing (polymerMeasure ϑ N s t ω) w
      (polymerMeasure ϑ N t u (Gaussian.resample (Gaussian.timeBlock b c) η ω)) Φ
  have hpoint (η : Disorder) : Y η =
      ∑ q ∈ Q,
        (∫ p in (cell N q.1.1 ×ˢ cell N q.1.2) ×ˢ
          (cell N q.2.1 ×ˢ cell N q.2.2),
          smoothedProductFourTest Φ w p
          ∂((volume : Measure (Plane × Plane)).prod volume)) *
        (smoothedBridgeFirstDensity ϑ N s t ω q.1.1 q.1.2 *
          ((N : ℝ) / 4 * pointToPoint (criticalBeta ϑ N) b n₂
            q.2.1 q.2.2 (Gaussian.resample (Gaussian.timeBlock b c) η ω))) := by
    dsimp [Y]
    apply smoothedProductPairing_polymer_eq_finiteCellSum_mixed
      ϑ N hN s t t u ω (Gaussian.resample (Gaussian.timeBlock b c) η ω)
      Φ w hw hwc Q
    intro q hq p hp
    exact smoothedProductBridgeSupport_left_mixed ϑ N s t t' u Φ ω
      (Gaussian.resample (Gaussian.timeBlock b c) η ω) w q
      (by change q ∉ smoothedProductBridgeSupport N s t t' u Φ at hq; exact hq) p hp
  have hcellFactor (q : (Site × Site) × (Site × Site)) :
      (∫ p in (cell N q.1.1 ×ˢ cell N q.1.2) ×ˢ
        (cell N q.2.1 ×ˢ cell N q.2.2),
        smoothedProductFourTest Φ w p
        ∂((volume : Measure (Plane × Plane)).prod volume)) =
      smoothedBridgeOuterCell N Φ q.1.1 q.2.2 *
        smoothedBridgeConnectorCell N w q.1.2 q.2.1 := by
    exact smoothedProductFourTest_integral_cell_factor N hN Φ w hw hwc
      q.1.1 q.1.2 q.2.1 q.2.2
  let Cterm : ((Site × Site) × (Site × Site)) → ℝ := fun q =>
    smoothedBridgeOuterCell N Φ q.1.1 q.2.2 *
      smoothedBridgeConnectorCell N w q.1.2 q.2.1 *
      smoothedBridgeFirstDensity ϑ N s t ω q.1.1 q.1.2 * ((N : ℝ) / 4)
  have hYfinite (η : Disorder) : Y η =
      ∑ q ∈ Q, Cterm q * pointToPoint (criticalBeta ϑ N) b n₂
        q.2.1 q.2.2 (Gaussian.resample (Gaussian.timeBlock b c) η ω) := by
    rw [hpoint η]
    apply Finset.sum_congr rfl
    intro q hq
    rw [hcellFactor q]
    simp only [Cterm]
    ring
  have htermInt (q : (Site × Site) × (Site × Site)) :
      Integrable (fun η => Cterm q * pointToPoint (criticalBeta ϑ N) b n₂
        q.2.1 q.2.2 (Gaussian.resample (Gaussian.timeBlock b c) η ω)) disorderLaw := by
    have hpt := integrable_pointToPoint_resample_slab (criticalBeta ϑ N)
      (a := b) (b := b) (c := c) (d := d) le_rfl hbc hcd q.2.1 q.2.2 ω
    have h := hpt.const_mul (Cterm q)
    convert h using 1
  have hleft : ∫ η, Y η ∂disorderLaw =
      ∑ q ∈ Q,
        smoothedBridgeOuterCell N Φ q.1.1 q.2.2 *
          smoothedBridgeConnectorCell N w q.1.2 q.2.1 *
          smoothedBridgeFirstDensity ϑ N s t ω q.1.1 q.1.2 *
          ((N : ℝ) / 4 * ∑' y : Site,
            srwKernel m (y - q.2.1) *
              pointToPoint (criticalBeta ϑ N) c n₃ y q.2.2 ω) := by
    calc
      _ = ∫ η, ∑ q ∈ Q, Cterm q *
          pointToPoint (criticalBeta ϑ N) b n₂ q.2.1 q.2.2
            (Gaussian.resample (Gaussian.timeBlock b c) η ω) ∂disorderLaw := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hYfinite
      _ = ∑ q ∈ Q, ∫ η, Cterm q *
          pointToPoint (criticalBeta ϑ N) b n₂ q.2.1 q.2.2
            (Gaussian.resample (Gaussian.timeBlock b c) η ω) ∂disorderLaw := by
        rw [integral_finsetSum _ (fun q hq => htermInt q)]
      _ = ∑ q ∈ Q, Cterm q *
          (∫ η, pointToPoint (criticalBeta ϑ N) b n₂ q.2.1 q.2.2
            (Gaussian.resample (Gaussian.timeBlock b c) η ω) ∂disorderLaw) := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [integral_const_mul]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [integral_pointToPoint_resample_startSlab (criticalBeta ϑ N)
          hbc hcd q.2.1 q.2.2 ω]
        simp only [Cterm]
        ring
  have hQmem (x : Site) (hx : x ∈ X) (x₁ : Site) (hx₁ : x₁ ∈ A)
      (y : Site) (hy : y ∈ V) (z : Site) (hz : z ∈ Z) :
      ((x, x₁), (y, z)) ∈ Q := by
    rw [hQdef]
    exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hx, hx₁⟩,
      Finset.mem_product.mpr ⟨hy, hz⟩⟩
  have hleftTruncate (q : (Site × Site) × (Site × Site)) (hq : q ∈ Q) :
      (∑' y : Site, srwKernel m (y - q.2.1) *
        pointToPoint (criticalBeta ϑ N) c n₃ y q.2.2 ω) =
      ∑ y ∈ V, srwKernel m (y - q.2.1) *
        pointToPoint (criticalBeta ϑ N) c n₃ y q.2.2 ω := by
    rw [tsum_eq_sum (s := V)]
    intro y hy
    have hzero : pointToPoint (criticalBeta ϑ N) c n₃ y q.2.2 ω = 0 := by
      by_contra hne
      have hpos : 0 < pointToPoint (criticalBeta ϑ N) c n₃ y q.2.2 ω :=
        lt_of_le_of_ne (Polymer.pointToPoint_nonneg _ _ _ _ _ _) (Ne.symm hne)
      have hreach := (Polymer.pointToPoint_pos_iff _ _ _ _ _ _).mp hpos
      have hyend : y ∈ Polymer.endpoints q.2.2 n₃ :=
        mem_endpoints_reverse ((Polymer.mem_endpoints_iff _ _ _).2 hreach)
      have hzdata := (Finset.mem_product.mp (Finset.mem_product.mp hq).2).2
      have hyV : y ∈ V := by
        apply Finset.mem_biUnion.mpr
        exact ⟨q.2.2, hzdata, Finset.mem_union_right _
          (Finset.mem_union_left _ hyend)⟩
      exact hy hyV
    simp [hzero]
  have hleftFinite : ∫ η, Y η ∂disorderLaw =
      ∑ x ∈ X, ∑ x₁ ∈ A, ∑ y ∈ V, ∑ z ∈ Z,
          (((N : ℝ) / 4 * smoothedBridgeOuterCell N Φ x z) *
              smoothedBridgeFirstDensity ϑ N s t ω x x₁) *
            smoothedBridgeConnectorCell N w x₁ y *
            ∑ b' ∈ V, srwKernel m (b' - y) *
              pointToPoint (criticalBeta ϑ N) c n₃ b' z ω := by
    rw [hleft, hQsum]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro x₁ hx₁
    apply Finset.sum_congr rfl
    intro y hy
    apply Finset.sum_congr rfl
    intro z hz
    rw [hleftTruncate ((x, x₁), (y, z)) (hQmem x hx x₁ hx₁ y hy z hz)]
    ring
  simpa only [X, A, V, Z, a, c, n₃, m] using hleftFinite

/-- The continuum kernel pairing with the convolved slab connector has the matching finite cell
expansion. -/
theorem kernelProductPairing_slabSmoothedConnector_finiteExpansion
    (ϑ : ℝ) (N : ℕ) (hN : 0 < N) {s t t' u : ℝ}
    (hst : s < t) (htt' : t < t') (ht'u : t' < u)
    (Φ : C_c(Plane × Plane, ℝ)) (w : Plane → ℝ) (hw : Continuous w)
    (hwc : HasCompactSupport w) (ω : Disorder) :
    kernelProductPairing (polymerMeasure ϑ N s t ω)
      (fun a b => slabSmoothedConnector ϑ N t t' w a b)
      (polymerMeasure ϑ N t' u ω) Φ =
      ∑ x ∈ smoothedBridgeStartSites N Φ,
        ∑ x₁ ∈ smoothedBridgeLeftSites N s t Φ,
          ∑ b' ∈ smoothedBridgeMiddleSites N t t' u Φ,
            ∑ z ∈ smoothedBridgeEndSites N Φ,
              (((N : ℝ) / 4 * smoothedBridgeOuterCell N Φ x z) *
                  smoothedBridgeFirstDensity ϑ N s t ω x x₁) *
                pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * t'))
                  (evenCeil ((N : ℝ) * u) - evenCeil ((N : ℝ) * t')) b' z ω *
                ∑ y ∈ smoothedBridgeMiddleSites N t t' u Φ,
                  smoothedBridgeConnectorCell N w x₁ y *
                    srwKernel (evenCeil ((N : ℝ) * t') - evenCeil ((N : ℝ) * t))
                      (b' - y) := by
  classical
  let a := evenCeil ((N : ℝ) * s)
  let b := evenCeil ((N : ℝ) * t)
  let c := evenCeil ((N : ℝ) * t')
  let d := evenCeil ((N : ℝ) * u)
  have hab : a ≤ b := by
    dsimp [a, b]
    exact Critical2DKPZ.evenCeil_mono
      (mul_le_mul_of_nonneg_left (le_of_lt hst) (Nat.cast_nonneg N))
  have hbc : b ≤ c := by
    dsimp [b, c]
    exact Critical2DKPZ.evenCeil_mono
      (mul_le_mul_of_nonneg_left (le_of_lt htt') (Nat.cast_nonneg N))
  have hcd : c ≤ d := by
    dsimp [c, d]
    exact Critical2DKPZ.evenCeil_mono
      (mul_le_mul_of_nonneg_left (le_of_lt ht'u) (Nat.cast_nonneg N))
  let X := smoothedBridgeStartSites N Φ
  let Z := smoothedBridgeEndSites N Φ
  let n₁ := b - a
  let n₃ := d - c
  let m := c - b
  let A := smoothedBridgeLeftSites N s t Φ
  let V := smoothedBridgeMiddleSites N t t' u Φ
  let Q := smoothedProductBridgeSupport N s t t' u Φ
  have hQdef : Q = (X.product A).product (V.product Z) := by rfl
  have hQsum {f : ((Site × Site) × (Site × Site)) → ℝ} :
      ∑ q ∈ Q, f q = ∑ x ∈ X, ∑ x₁ ∈ A, ∑ y ∈ V, ∑ z ∈ Z,
        f ((x, x₁), (y, z)) := by
    rw [hQdef]
    exact sum_siteQuad_eq_nested X A V Z f
  let connector : Plane × Plane → ℝ := fun p =>
    slabSmoothedConnector ϑ N t t' w p.1 p.2
  let firstDensity : Site → Site → ℝ := fun x y =>
    smoothedBridgeFirstDensity ϑ N s t ω x y
  let lastDensity : Site → Site → ℝ := fun x y =>
    smoothedBridgeLastDensity ϑ N t' u ω x y
  have hκmeas : Measurable connector :=
    measurable_slabSmoothedConnector ϑ N t t' w hw hwc
  obtain ⟨Cκ, hκbound⟩ := exists_slabSmoothedConnector_bound ϑ N hN t t' w hw hwc
  obtain ⟨CΦ, hΦbound⟩ := Φ.continuous.bounded_above_of_compact_support Φ.hasCompactSupport
  have hCΦ : 0 ≤ CΦ := (norm_nonneg _).trans (hΦbound 0)
  have hprodBound (p : (Plane × Plane) × (Plane × Plane)) :
      ‖Φ (p.1.1, p.2.2) * connector (p.1.2, p.2.1)‖ ≤ CΦ * Cκ := by
    rw [norm_mul]
    calc
      ‖Φ (p.1.1, p.2.2)‖ * ‖connector (p.1.2, p.2.1)‖ ≤
          CΦ * ‖connector (p.1.2, p.2.1)‖ :=
        mul_le_mul_of_nonneg_right (hΦbound _) (norm_nonneg _)
      _ ≤ CΦ * Cκ := mul_le_mul_of_nonneg_left (hκbound _ _) hCΦ
  have hright : kernelProductPairing (polymerMeasure ϑ N s t ω)
      (fun x y => connector (x, y)) (polymerMeasure ϑ N t' u ω) Φ =
      ∑ q ∈ Q,
        (∫ p in (cell N q.1.1 ×ˢ cell N q.1.2) ×ˢ
          (cell N q.2.1 ×ˢ cell N q.2.2),
          Φ (p.1.1, p.2.2) * connector (p.1.2, p.2.1)
          ∂((volume : Measure (Plane × Plane)).prod volume)) *
        (firstDensity q.1.1 q.1.2 * lastDensity q.2.1 q.2.2) := by
    apply kernelProductPairing_polymer_eq_finiteFourCellSum
      ϑ N hN s t t' u ω Φ connector hκmeas (CΦ * Cκ) hprodBound Q
    intro q hq p hp
    exact smoothedProductBridgeSupport_right ϑ N s t t' u Φ connector ω q
      (by change q ∉ smoothedProductBridgeSupport N s t t' u Φ at hq; exact hq) p hp
  have houterFactor (q : (Site × Site) × (Site × Site)) :
      (∫ p in (cell N q.1.1 ×ˢ cell N q.1.2) ×ˢ
        (cell N q.2.1 ×ˢ cell N q.2.2),
        Φ (p.1.1, p.2.2) * connector (p.1.2, p.2.1)
        ∂((volume : Measure (Plane × Plane)).prod volume)) =
      smoothedBridgeOuterCell N Φ q.1.1 q.2.2 *
        (∫ p in cell N q.1.2 ×ˢ cell N q.2.1, connector p) := by
    have hκbound' : ∀ p : Plane × Plane, ‖connector p‖ ≤ Cκ := by
      intro p
      exact hκbound p.1 p.2
    exact integral_fourCell_endpoint_factor N hN Φ connector hκmeas Cκ hκbound'
      q.1.1 q.1.2 q.2.1 q.2.2
  have hconnectorCell (q : (Site × Site) × (Site × Site)) (hq : q ∈ Q) :
      (∫ p in cell N q.1.2 ×ˢ cell N q.2.1, connector p) =
      ∑ r ∈ Polymer.endpoints q.2.1 m,
        smoothedBridgeConnectorCell N w q.1.2 r * srwKernel m (q.2.1 - r) := by
    have heven := smoothedProductBridgeSupport_even N s t t' u
      (le_of_lt hst) (le_of_lt htt') (le_of_lt ht'u) Φ (by
        change q ∈ smoothedProductBridgeSupport N s t t' u Φ at hq
        exact hq)
    exact slabSmoothedConnector_cellPair_eq_sum ϑ N hN t t' q.1.2 q.2.1
      heven.2.2.1 w hw hwc
  have hright' : kernelProductPairing (polymerMeasure ϑ N s t ω)
      (fun x y => connector (x, y)) (polymerMeasure ϑ N t' u ω) Φ =
      ∑ q ∈ Q,
        (smoothedBridgeOuterCell N Φ q.1.1 q.2.2 * firstDensity q.1.1 q.1.2) *
          ((∑ r ∈ Polymer.endpoints q.2.1 m,
            smoothedBridgeConnectorCell N w q.1.2 r * srwKernel m (q.2.1 - r)) *
            lastDensity q.2.1 q.2.2) := by
    rw [hright]
    apply Finset.sum_congr rfl
    intro q hq
    rw [houterFactor q, hconnectorCell q hq]
    simp only [firstDensity, lastDensity]
    ring
  have hrightWeighted (q : (Site × Site) × (Site × Site)) (hq : q ∈ Q) :
      (∑ r ∈ Polymer.endpoints q.2.1 m,
        smoothedBridgeConnectorCell N w q.1.2 r * srwKernel m (q.2.1 - r)) *
        lastDensity q.2.1 q.2.2 =
      (∑ r ∈ V,
        smoothedBridgeConnectorCell N w q.1.2 r * srwKernel m (q.2.1 - r)) *
        lastDensity q.2.1 q.2.2 := by
    by_cases hlast : lastDensity q.2.1 q.2.2 = 0
    · simp [hlast]
    · have hlastpt : pointToPoint (criticalBeta ϑ N) c n₃ q.2.1 q.2.2 ω ≠ 0 := by
        intro hzero
        have hptEq : pointToPoint (criticalBeta ϑ N)
            (evenCeil ((N : ℝ) * t'))
            (evenCeil ((N : ℝ) * u) - evenCeil ((N : ℝ) * t'))
            q.2.1 q.2.2 ω = 0 := by
          exact hzero
        have hlastEq : lastDensity q.2.1 q.2.2 = 0 := by
          unfold lastDensity smoothedBridgeLastDensity
          exact mul_eq_zero.mpr (Or.inr hptEq)
        exact hlast hlastEq
      have hpos := lt_of_le_of_ne
        (Polymer.pointToPoint_nonneg _ _ _ _ _ _) (Ne.symm hlastpt)
      have hreach := (Polymer.pointToPoint_pos_iff _ _ _ _ _ _).mp hpos
      have hbEnd : q.2.1 ∈ Polymer.endpoints q.2.2 n₃ :=
        mem_endpoints_reverse ((Polymer.mem_endpoints_iff _ _ _).2 hreach)
      have hzdata := (Finset.mem_product.mp (Finset.mem_product.mp hq).2).2
      have hsub : Polymer.endpoints q.2.1 m ⊆ V := by
        intro r hr
        apply Finset.mem_biUnion.mpr
        refine ⟨q.2.2, hzdata, Finset.mem_union_right _
          (Finset.mem_union_right _ ?_)⟩
        apply Finset.mem_biUnion.mpr
        exact ⟨q.2.1, hbEnd, hr⟩
      have hzero (r : Site) (hr : r ∈ V)
          (hrnot : r ∉ Polymer.endpoints q.2.1 m) :
          smoothedBridgeConnectorCell N w q.1.2 r * srwKernel m (q.2.1 - r) = 0 := by
        have hnot : q.2.1 ∉ Polymer.endpoints r m := by
          intro hmem
          exact hrnot (mem_endpoints_reverse hmem)
        rw [Polymer.srwKernel_eq_zero_of_not_mem m r q.2.1 hnot]
        simp
      have hsum := Finset.sum_subset hsub hzero
      rw [hsum]
  have hQmem (x : Site) (hx : x ∈ X) (x₁ : Site) (hx₁ : x₁ ∈ A)
      (y : Site) (hy : y ∈ V) (z : Site) (hz : z ∈ Z) :
      ((x, x₁), (y, z)) ∈ Q := by
    rw [hQdef]
    exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hx, hx₁⟩,
      Finset.mem_product.mpr ⟨hy, hz⟩⟩
  have hrightFinite : kernelProductPairing (polymerMeasure ϑ N s t ω)
      (fun x y => connector (x, y)) (polymerMeasure ϑ N t' u ω) Φ =
      ∑ x ∈ X, ∑ x₁ ∈ A, ∑ b' ∈ V, ∑ z ∈ Z,
        (((N : ℝ) / 4 * smoothedBridgeOuterCell N Φ x z) *
            firstDensity x x₁) *
          pointToPoint (criticalBeta ϑ N) c n₃ b' z ω *
          ∑ y ∈ V, smoothedBridgeConnectorCell N w x₁ y * srwKernel m (b' - y) := by
    rw [hright', hQsum]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro x₁ hx₁
    apply Finset.sum_congr rfl
    intro b' hb'
    apply Finset.sum_congr rfl
    intro z hz
    rw [hrightWeighted ((x, x₁), (b', z))
      (hQmem x hx x₁ hx₁ b' hb' z hz)]
    simp only [firstDensity, lastDensity, smoothedBridgeFirstDensity,
      smoothedBridgeLastDensity]
    ring
  simpa only [X, A, V, Z, firstDensity, lastDensity, a, b, c, d, n₁, n₃, m]
    using hrightFinite

/-- Annealing the middle disorder slab in a smoothed polymer product gives the polymer pairing
with the slab-smoothed connector. -/
theorem integral_smoothedProductPairing_resample_slab_eq_kernelProductPairing
    (ϑ : ℝ) (N : ℕ) (hN : 0 < N) {s t t' u : ℝ}
    (_hs : 0 ≤ s) (hst : s < t) (htt' : t < t') (ht'u : t' < u)
    (Φ : C_c(Plane × Plane, ℝ)) (w : Plane → ℝ) (hw : Continuous w)
    (hwc : HasCompactSupport w) (ω : Disorder) :
    ∫ η, smoothedProductPairing (polymerMeasure ϑ N s t ω) w
      (polymerMeasure ϑ N t u
        (Gaussian.resample (Gaussian.timeBlock (evenCeil ((N : ℝ) * t))
          (evenCeil ((N : ℝ) * t'))) η ω)) Φ ∂disorderLaw =
      kernelProductPairing (polymerMeasure ϑ N s t ω)
        (fun a b => slabSmoothedConnector ϑ N t t' w a b)
        (polymerMeasure ϑ N t' u ω) Φ := by
  rw [integral_smoothedProductPairing_resample_slab_finiteExpansion
    ϑ N hN _hs hst htt' ht'u Φ w hw hwc ω]
  rw [kernelProductPairing_slabSmoothedConnector_finiteExpansion
    ϑ N hN hst htt' ht'u Φ w hw hwc ω]
  simpa only [smoothedBridgeFirstDensity] using
    (finiteSiteConvolution_fubini
      (smoothedBridgeStartSites N Φ) (smoothedBridgeLeftSites N s t Φ)
      (smoothedBridgeMiddleSites N t t' u Φ) (smoothedBridgeEndSites N Φ)
      (fun x x₁ z => ((N : ℝ) / 4 * smoothedBridgeOuterCell N Φ x z) *
        smoothedBridgeFirstDensity ϑ N s t ω x x₁)
      (fun x y => smoothedBridgeConnectorCell N w x y)
      (fun b' z => pointToPoint (criticalBeta ϑ N)
        (evenCeil ((N : ℝ) * t'))
        (evenCeil ((N : ℝ) * u) - evenCeil ((N : ℝ) * t')) b' z ω)
      (fun b' y => srwKernel
        (evenCeil ((N : ℝ) * t') - evenCeil ((N : ℝ) * t)) (b' - y)))

/-- Annealing the middle disorder slab makes the smoothed polymer pairing a conditional mean;
the squared error is exactly the loss of its second moment. -/
theorem integral_sq_sub_slabSmoothedProduct (ϑ : ℝ) (N : ℕ) {s t t' u : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (htt' : t < t') (ht'u : t' < u)
    (Φ : C_c(Plane × Plane, ℝ)) (w : Plane → ℝ) (hw : Continuous w)
    (hwc : HasCompactSupport w) :
    Integrable (fun ω => smoothedProductPairing (polymerMeasure ϑ N s t ω) w
      (polymerMeasure ϑ N t u ω) Φ ^ 2) disorderLaw ∧
    Integrable (fun ω => kernelProductPairing (polymerMeasure ϑ N s t ω)
      (fun a b => ∫ y, w (a - y) * slabMeanKernel ϑ N t t' y b)
      (polymerMeasure ϑ N t' u ω) Φ ^ 2) disorderLaw ∧
    ∫ ω, (smoothedProductPairing (polymerMeasure ϑ N s t ω) w
      (polymerMeasure ϑ N t u ω) Φ - kernelProductPairing (polymerMeasure ϑ N s t ω)
        (fun a b => ∫ y, w (a - y) * slabMeanKernel ϑ N t t' y b)
        (polymerMeasure ϑ N t' u ω) Φ) ^ 2 ∂disorderLaw =
      ∫ ω, smoothedProductPairing (polymerMeasure ϑ N s t ω) w
        (polymerMeasure ϑ N t u ω) Φ ^ 2 ∂disorderLaw -
      ∫ ω, kernelProductPairing (polymerMeasure ϑ N s t ω)
        (fun a b => ∫ y, w (a - y) * slabMeanKernel ϑ N t t' y b)
        (polymerMeasure ϑ N t' u ω) Φ ^ 2 ∂disorderLaw := by
  classical
  by_cases hN : N = 0
  · subst N
    simp [polymerMeasure_zero_at_zero, kernelProductPairing]
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    let b : ℕ := evenCeil ((N : ℝ) * t)
    let c : ℕ := evenCeil ((N : ℝ) * t')
    let a : ℕ := evenCeil ((N : ℝ) * s)
    have hab : a ≤ b := by
      dsimp [a, b]
      exact Critical2DKPZ.evenCeil_mono
        (mul_le_mul_of_nonneg_left (le_of_lt hst) (Nat.cast_nonneg N))
    have hbc : b ≤ c := by
      dsimp [b, c]
      exact Critical2DKPZ.evenCeil_mono
        (mul_le_mul_of_nonneg_left (le_of_lt htt') (Nat.cast_nonneg N))
    let Y : Disorder → ℝ := fun ω => smoothedProductPairing
      (polymerMeasure ϑ N s t ω) w (polymerMeasure ϑ N t u ω) Φ
    let S : Disorder → ℝ := fun ω => kernelProductPairing (polymerMeasure ϑ N s t ω)
      (fun a b => ∫ y, w (a - y) * slabMeanKernel ϑ N t t' y b)
      (polymerMeasure ϑ N t' u ω) Φ
    have hY : MemLp Y 2 disorderLaw :=
      memLp_smoothedProductPairing_two ϑ N s t t u Φ w hw hwc
    have hYm : Measurable Y := by
      dsimp [Y]
      exact measurable_smoothedProductPairing ϑ N s t t u Φ w hw hwc
    have hYint : Integrable Y disorderLaw := hY.integrable (by norm_num)
    let m : MeasurableSpace Disorder :=
      Gaussian.coordinateSigma (fun _ : ℕ × Site => ℝ) (Gaussian.timeBlock b c)ᶜ
    have hm : m ≤ MeasurableSpace.pi := by
      dsimp only [m]
      exact Gaussian.coordinateSigma_le (fun _ : ℕ × Site => ℝ) (Gaussian.timeBlock b c)ᶜ
    have hCEbase := Gaussian.condExp_coordinateSigma_ae_eq
      (fun _ : ℕ × Site => ProbabilityTheory.gaussianReal 0 1)
      (Gaussian.timeBlock b c)ᶜ hYm hYint
    have hCE : disorderLaw[Y | m] =ᵐ[disorderLaw]
        fun ω => ∫ η, Y (Gaussian.resample (Gaussian.timeBlock b c)ᶜ ω η) ∂disorderLaw := by
      simpa only [disorderLaw, m] using hCEbase
    have hCEresample : disorderLaw[Y | m] =ᵐ[disorderLaw]
        fun ω => ∫ η, Y (Gaussian.resample (Gaussian.timeBlock b c) η ω) ∂disorderLaw := by
      filter_upwards [hCE] with ω hω
      rw [hω]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun η => congrArg Y
        (resample_compl_eq_swapped (Gaussian.timeBlock b c) ω η)
    have hbridge (ω : Disorder) :
        (∫ η, Y (Gaussian.resample (Gaussian.timeBlock b c) η ω) ∂disorderLaw) = S ω := by
      have hfirst (x y : Site) (η : Disorder) :
          pointToPoint (criticalBeta ϑ N) a (b - a) x y
            (Gaussian.resample (Gaussian.timeBlock b c) η ω) =
          pointToPoint (criticalBeta ϑ N) a (b - a) x y ω := by
        apply blockMeasurable_resample_outside
          (a := a) (b := b) (c := b) (d := c)
          (Set.disjoint_left.mpr fun n hn hc => by
            simp only [Set.mem_Ioc] at hn hc
            omega)
        convert Polymer.measurable_pointToPoint_block (criticalBeta ϑ N)
          a (b - a) x y using 1
        rw [Nat.add_sub_of_le hab]
      have hμ (η : Disorder) :
          polymerMeasure ϑ N s t (Gaussian.resample (Gaussian.timeBlock b c) η ω) =
            polymerMeasure ϑ N s t ω := by
        have hdensity : (fun p : Plane × Plane => ENNReal.ofReal
            (rescaledP2P ϑ N s t p (Gaussian.resample (Gaussian.timeBlock b c) η ω))) =
            fun p => ENNReal.ofReal (rescaledP2P ϑ N s t p ω) := by
          funext p
          congr 1
          simpa only [rescaledP2P] using congrArg
            (fun r : ℝ => (N : ℝ) / 4 * r) (hfirst _ _ η)
        change (volume : Measure (Plane × Plane)).withDensity _ =
          (volume : Measure (Plane × Plane)).withDensity _
        rw [hdensity]
      calc
        _ = ∫ η, smoothedProductPairing (polymerMeasure ϑ N s t ω) w
              (polymerMeasure ϑ N t u (Gaussian.resample (Gaussian.timeBlock b c) η ω)) Φ
              ∂disorderLaw := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun η => by
              dsimp [Y]
              rw [hμ η]
        _ = S ω := by
            dsimp [S, b, c]
            exact integral_smoothedProductPairing_resample_slab_eq_kernelProductPairing
              ϑ N hNpos hs hst htt' ht'u Φ w hw hwc ω
    have hSce : S =ᵐ[disorderLaw] disorderLaw[Y | m] := by
      filter_upwards [hCEresample] with ω hω
      exact (hω.trans (hbridge ω)).symm
    have hCE2 := hY.condExpL2_ae_eq_condExp (E := ℝ) (𝕜 := ℝ)
      (m₀ := MeasurableSpace.pi) hm
    have hCE2S :
        (fun ω => (condExpL2 ℝ ℝ hm (hY.toLp Y) : Disorder → ℝ) ω) =ᵐ[disorderLaw] S :=
      hCE2.trans hSce.symm
    have hS : MemLp S 2 disorderLaw := by
      have hcond : MemLp (disorderLaw[Y | m]) 2 disorderLaw := hY.condExp (by norm_num)
      exact hcond.ae_eq hSce.symm
    have hSmCE : AEStronglyMeasurable[m]
        (fun ω => (condExpL2 ℝ ℝ hm (hY.toLp Y) : Disorder → ℝ) ω) disorderLaw :=
      aestronglyMeasurable_condExpL2 hm _
    have hSm : AEStronglyMeasurable[m] S disorderLaw := hSmCE.congr hCE2S
    have hdecomp := integral_sq_sub_condExp_eq (Ω := Disorder)
      (mΩ := MeasurableSpace.pi) disorderLaw hm hY hS hSm hSce
    have hYsq : Integrable (fun ω => Y ω ^ 2) disorderLaw := by
      have h := hY.integrable_norm_pow'
      apply h.congr
      filter_upwards [] with ω
      rw [Real.norm_eq_abs, sq_abs]
    have hSsq : Integrable (fun ω => S ω ^ 2) disorderLaw := by
      have h := hS.integrable_norm_pow'
      apply h.congr
      filter_upwards [] with ω
      rw [Real.norm_eq_abs, sq_abs]
    refine ⟨?_, ⟨?_, ?_⟩⟩
    · simpa only [Y] using hYsq
    · simpa only [S] using hSsq
    · simpa only [Y, S] using hdecomp.2

end Critical2DKPZ.SHF.Flow

end
