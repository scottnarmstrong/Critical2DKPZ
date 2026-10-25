/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.SlabProductsLattice
public import Critical2DKPZ.SHF.Tsai.Defs
public import Critical2DKPZ.SHF.Limit.SlabMean
public import Critical2DKPZ.SHF.Limit.LocalFinite
public import Critical2DKPZ.Analysis.Lattice.Volume
public import Critical2DKPZ.SHF.Flow.SlabProjection
public import Critical2DKPZ.Smoothing.SmoothingClockBounds
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Integral.Prod

/-! # Polymer pairings through an annealed slab -/

@[expose] public noncomputable section

open MeasureTheory
open scoped CompactlySupported

namespace Critical2DKPZ.SHF.Flow

open Critical2DKPZ.SHF.Limit

/-- `∫ μ(dx dw) κ(w, y) ν(dy dz) f(x, z)`: the product of `μ` and `ν` through a two-variable connector. -/
def kernelProductPairing (μ : Measure (Plane × Plane)) (κ : Plane → Plane → ℝ)
    (ν : Measure (Plane × Plane)) (f : Plane × Plane → ℝ) : ℝ :=
  ∫ q, f (q.1.1, q.2.2) * κ q.1.2 q.2.1 ∂(μ.prod ν)

/-- Unfolding the two polymer densities turns their continuum product pairing into a single
Lebesgue integral on the four endpoint variables. -/
theorem kernelProductPairing_polymer_eq_densityIntegral (ϑ : ℝ) (N : ℕ)
    (s t t' u : ℝ) (ω : Disorder) (κ : Plane → Plane → ℝ) (Φ : Plane × Plane → ℝ) :
    kernelProductPairing (polymerMeasure ϑ N s t ω) κ (polymerMeasure ϑ N t' u ω) Φ =
      ∫ q : (Plane × Plane) × (Plane × Plane),
        (rescaledP2P ϑ N s t q.1 ω * rescaledP2P ϑ N t' u q.2 ω) *
          (Φ (q.1.1, q.2.2) * κ q.1.2 q.2.1)
          ∂((volume : Measure (Plane × Plane)).prod volume) := by
  have hd₁ : Measurable (fun p : Plane × Plane =>
      ENNReal.ofReal (rescaledP2P ϑ N s t p ω)) :=
    ENNReal.measurable_ofReal.comp
      (SHF.Moments.measurable_uncurry_rescaledP2P ϑ N s t |>.of_uncurry_right)
  have hd₂ : Measurable (fun p : Plane × Plane =>
      ENNReal.ofReal (rescaledP2P ϑ N t' u p ω)) :=
    ENNReal.measurable_ofReal.comp
      (SHF.Moments.measurable_uncurry_rescaledP2P ϑ N t' u |>.of_uncurry_right)
  have hdens : Measurable (fun q : (Plane × Plane) × (Plane × Plane) =>
      ENNReal.ofReal (rescaledP2P ϑ N s t q.1 ω) *
        ENNReal.ofReal (rescaledP2P ϑ N t' u q.2 ω)) := by
    exact (hd₁.comp measurable_fst).mul (hd₂.comp measurable_snd)
  rw [kernelProductPairing, polymerMeasure, polymerMeasure,
    prod_withDensity hd₁ hd₂,
    integral_withDensity_eq_integral_toReal_smul hdens]
  · apply integral_congr_ae
    filter_upwards [] with q
    have h₁ := SHF.Moments.rescaledP2P_nonneg ϑ N s t q.1 ω
    have h₂ := SHF.Moments.rescaledP2P_nonneg ϑ N t' u q.2 ω
    rw [← ENNReal.ofReal_mul h₁, ENNReal.toReal_ofReal (mul_nonneg h₁ h₂)]
    simp only [smul_eq_mul]
  · filter_upwards [] with q
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- A polymer kernel product with a lattice-cell-constant connector is the exact finite cell sum.
The two middle-cell volumes cancel the two density normalizations when the connector itself is
an annealed polymer slab. -/
theorem kernelProductPairing_polymer_eq_cellSum (ϑ : ℝ) (N : ℕ) (hN : 0 < N)
    (s t t' u : ℝ) (ω : Disorder) (k : Site → Site → ℝ)
    (κ : Plane → Plane → ℝ)
    (hκ : ∀ a b, κ a b = k (latticePoint N a) (latticePoint N b))
    (Φ : C_c(Plane × Plane, ℝ)) :
    kernelProductPairing (polymerMeasure ϑ N s t ω) κ
        (polymerMeasure ϑ N t' u ω) Φ =
      ∑' q : (Site × Site) × (Site × Site),
        (∫ p in cell N q.1.1 ×ˢ cell N q.2.2, Φ p) *
          ((N : ℝ) / 4 * pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s))
            (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) q.1.1 q.1.2 ω) *
          ((N : ℝ) / 4 * pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * t'))
            (evenCeil ((N : ℝ) * u) - evenCeil ((N : ℝ) * t')) q.2.1 q.2.2 ω) *
          k q.1.2 q.2.1 *
          ((volume (cell N q.1.2)).toReal * (volume (cell N q.2.1)).toReal) := by
  classical
  let K : Set (Plane × Plane) := tsupport Φ
  let Sx : Set Site := latticePoint N '' (Prod.fst '' K)
  let Sz : Set Site := latticePoint N '' (Prod.snd '' K)
  have hSx : Sx.Finite := by
    apply finite_latticePoint_image_of_bounded
    exact (Φ.hasCompactSupport.image continuous_fst).isBounded
  have hSz : Sz.Finite := by
    apply finite_latticePoint_image_of_bounded
    exact (Φ.hasCompactSupport.image continuous_snd).isBounded
  let a := evenCeil ((N : ℝ) * s)
  let b := evenCeil ((N : ℝ) * t)
  let c := evenCeil ((N : ℝ) * t')
  let d := evenCeil ((N : ℝ) * u)
  let coeff : ((Site × Site) × (Site × Site)) → ℝ := fun q =>
    ((N : ℝ) / 4 * pointToPoint (criticalBeta ϑ N) a (b - a) q.1.1 q.1.2 ω) *
      ((N : ℝ) / 4 * pointToPoint (criticalBeta ϑ N) c (d - c) q.2.1 q.2.2 ω) *
      k q.1.2 q.2.1
  let G : ((Site × Site) × (Site × Site)) → ℝ := fun q =>
    if q.1.1 ∈ Sx ∧ q.2.2 ∈ Sz then coeff q else 0
  let Souter : Finset (Site × Site) := hSx.toFinset.product hSz.toFinset
  let Q : Finset ((Site × Site) × (Site × Site)) := Souter.biUnion fun xz =>
    ((Polymer.endpoints xz.1 (b - a)).product
      (Polymer.endpoints xz.2 (d - c))).image
        (fun wy => ((xz.1, wy.1), (wy.2, xz.2)))
  have hG : {q : (Site × Site) × (Site × Site) | G q ≠ 0}.Finite := by
    apply Q.finite_toSet.subset
    intro q hq
    have houter : q.1.1 ∈ Sx ∧ q.2.2 ∈ Sz := by
      by_contra h
      have hz : G q = 0 := by simp [G, h]
      exact hq hz
    have hcoeff : coeff q ≠ 0 := by
      intro hz
      apply hq
      simp [G, houter, hz]
    have hp1 : pointToPoint (criticalBeta ϑ N) a (b - a)
        q.1.1 q.1.2 ω ≠ 0 := by
      intro hz
      apply hcoeff
      simp [coeff, hz]
    have hp2 : pointToPoint (criticalBeta ϑ N) c (d - c)
        q.2.1 q.2.2 ω ≠ 0 := by
      intro hz
      apply hcoeff
      simp [coeff, hz]
    have hreach1 : Polymer.Reachable (b - a) q.1.1 q.1.2 := by
      by_contra hn
      exact hp1 ((Polymer.pointToPoint_eq_zero_iff _ _ _ _ _ _).2 hn)
    have hreach2 : Polymer.Reachable (d - c) q.2.1 q.2.2 := by
      by_contra hn
      exact hp2 ((Polymer.pointToPoint_eq_zero_iff _ _ _ _ _ _).2 hn)
    have hw : q.1.2 ∈ Polymer.endpoints q.1.1 (b - a) :=
      (Polymer.mem_endpoints_iff _ _ _).2 hreach1
    have hy' : q.2.2 ∈ Polymer.endpoints q.2.1 (d - c) :=
      (Polymer.mem_endpoints_iff _ _ _).2 hreach2
    have hy : q.2.1 ∈ Polymer.endpoints q.2.2 (d - c) := mem_endpoints_reverse hy'
    have houterFin : (q.1.1, q.2.2) ∈ Souter := by
      exact Finset.mem_product.mpr
        ⟨hSx.mem_toFinset.mpr houter.1, hSz.mem_toFinset.mpr houter.2⟩
    have hmiddle : (q.1.2, q.2.1) ∈
        (Polymer.endpoints q.1.1 (b - a)).product
          (Polymer.endpoints q.2.2 (d - c)) :=
      Finset.mem_product.mpr ⟨hw, hy⟩
    change q ∈ Q
    exact Finset.mem_biUnion.mpr ⟨(q.1.1, q.2.2), houterFin,
      Finset.mem_image.mpr ⟨(q.1.2, q.2.1), hmiddle, rfl⟩⟩
  have hcellzero_left (x z : Site) (hx : x ∉ Sx) :
      ∫ p in cell N x ×ˢ cell N z, Φ p = 0 := by
    have hzero (p : Plane × Plane) (hp : p ∈ cell N x ×ˢ cell N z) : Φ p = 0 := by
      rcases Set.mem_prod.mp hp with ⟨hp₁, hp₂⟩
      by_contra hΦ
      have hpK : p ∈ K := subset_closure (Function.mem_support.mpr hΦ)
      apply hx
      exact ⟨p.1, ⟨p, hpK, rfl⟩, (mem_cell_iff N x p.1).mp hp₁⟩
    calc
      _ = ∫ p in cell N x ×ˢ cell N z, (0 : Plane × Plane → ℝ) p := by
        apply setIntegral_congr_fun ((measurableSet_cell N x).prod (measurableSet_cell N z))
        exact hzero
      _ = 0 := by simp
  have hcellzero_right (x z : Site) (hz : z ∉ Sz) :
      ∫ p in cell N x ×ˢ cell N z, Φ p = 0 := by
    have hzero (p : Plane × Plane) (hp : p ∈ cell N x ×ˢ cell N z) : Φ p = 0 := by
      rcases Set.mem_prod.mp hp with ⟨hp₁, hp₂⟩
      by_contra hΦ
      have hpK : p ∈ K := subset_closure (Function.mem_support.mpr hΦ)
      apply hz
      exact ⟨p.2, ⟨p, hpK, rfl⟩, (mem_cell_iff N z p.2).mp hp₂⟩
    calc
      _ = ∫ p in cell N x ×ˢ cell N z, (0 : Plane × Plane → ℝ) p := by
        apply setIntegral_congr_fun ((measurableSet_cell N x).prod (measurableSet_cell N z))
        exact hzero
      _ = 0 := by simp
  have hterm (q : (Site × Site) × (Site × Site)) :
      (∫ p in cell N q.1.1 ×ˢ cell N q.2.2, Φ p) * G q *
        ((volume (cell N q.1.2)).toReal * (volume (cell N q.2.1)).toReal) =
      (∫ p in cell N q.1.1 ×ˢ cell N q.2.2, Φ p) * coeff q *
        ((volume (cell N q.1.2)).toReal * (volume (cell N q.2.1)).toReal) := by
    by_cases houter : q.1.1 ∈ Sx ∧ q.2.2 ∈ Sz
    · simp [G, houter]
    · rcases not_and_or.mp houter with hx | hz
      · rw [hcellzero_left q.1.1 q.2.2 hx]
        simp
      · rw [hcellzero_right q.1.1 q.2.2 hz]
        simp
  have hstep (p : (Plane × Plane) × (Plane × Plane)) :
      (rescaledP2P ϑ N s t p.1 ω * rescaledP2P ϑ N t' u p.2 ω) *
        (Φ (p.1.1, p.2.2) * κ p.1.2 p.2.1) =
      Φ (p.1.1, p.2.2) * G
        ((latticePoint N p.1.1, latticePoint N p.1.2),
          (latticePoint N p.2.1, latticePoint N p.2.2)) := by
    by_cases hΦ : Φ (p.1.1, p.2.2) = 0
    · simp [G, hΦ]
    · have hpK : (p.1.1, p.2.2) ∈ K :=
        subset_closure (Function.mem_support.mpr hΦ)
      have hx : latticePoint N p.1.1 ∈ Sx :=
        ⟨p.1.1, ⟨(p.1.1, p.2.2), hpK, rfl⟩, rfl⟩
      have hz : latticePoint N p.2.2 ∈ Sz :=
        ⟨p.2.2, ⟨(p.1.1, p.2.2), hpK, rfl⟩, rfl⟩
      rw [hκ]
      simp [rescaledP2P, G, coeff, hx, hz, a, b, c, d]
      ring
  calc
    _ = ∫ p : (Plane × Plane) × (Plane × Plane),
        (rescaledP2P ϑ N s t p.1 ω * rescaledP2P ϑ N t' u p.2 ω) *
          (Φ (p.1.1, p.2.2) * κ p.1.2 p.2.1)
          ∂((volume : Measure (Plane × Plane)).prod volume) := by
      exact kernelProductPairing_polymer_eq_densityIntegral ϑ N s t t' u ω κ Φ
    _ = ∫ p : (Plane × Plane) × (Plane × Plane),
        Φ (p.1.1, p.2.2) * G
          ((latticePoint N p.1.1, latticePoint N p.1.2),
            (latticePoint N p.2.1, latticePoint N p.2.2))
          ∂((volume : Measure (Plane × Plane)).prod volume) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hstep
    _ = ∑ q ∈ hG.toFinset,
        (∫ p in cell N q.1.1 ×ˢ cell N q.2.2, Φ p) * G q *
          ((volume (cell N q.1.2)).toReal * (volume (cell N q.2.1)).toReal) :=
      integral_finiteLatticeFourStep_eq_cellSum N hN Φ G hG
    _ = ∑ q ∈ hG.toFinset,
        (∫ p in cell N q.1.1 ×ˢ cell N q.2.2, Φ p) * coeff q *
          ((volume (cell N q.1.2)).toReal * (volume (cell N q.2.1)).toReal) := by
      apply Finset.sum_congr rfl
      intro q hq
      exact hterm q
    _ = ∑' q : (Site × Site) × (Site × Site),
        (∫ p in cell N q.1.1 ×ˢ cell N q.2.2, Φ p) * coeff q *
          ((volume (cell N q.1.2)).toReal * (volume (cell N q.2.1)).toReal) := by
      rw [tsum_eq_sum (s := hG.toFinset) (fun q hq => by
        have hGzero : G q = 0 := by
          by_contra hne
          exact hq (hG.mem_toFinset.mpr hne)
        by_cases houter : q.1.1 ∈ Sx ∧ q.2.2 ∈ Sz
        · have hcoeffzero : coeff q = 0 := by
            have heq : G q = coeff q := by simp [G, houter]
            rw [heq] at hGzero
            exact hGzero
          rw [hcoeffzero]
          simp
        · rcases not_and_or.mp houter with hx | hz
          · rw [hcellzero_left q.1.1 q.2.2 hx]
            simp
          · rw [hcellzero_right q.1.1 q.2.2 hz]
            simp)]
    _ = _ := by
      apply tsum_congr
      intro q
      dsimp [coeff, a, b, c, d]
      ring

/-- The preceding expansion identifies the continuum pairing through an annealed slab with the
finite lattice Chapman--Kolmogorov coefficients. -/
theorem kernelProductPairing_slabMean_eq_cellSum (ϑ : ℝ) (N : ℕ) (hN : 0 < N)
    (s t t' u : ℝ) (ω : Disorder) (Φ : C_c(Plane × Plane, ℝ)) :
    kernelProductPairing (polymerMeasure ϑ N s t ω) (slabMeanKernel ϑ N t t')
        (polymerMeasure ϑ N t' u ω) Φ =
      ∑' q : (Site × Site) × (Site × Site),
        (∫ p in cell N q.1.1 ×ˢ cell N q.2.2, Φ p) *
          ((N : ℝ) / 4 * pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s))
            (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) q.1.1 q.1.2 ω) *
          ((N : ℝ) / 4 * pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * t'))
            (evenCeil ((N : ℝ) * u) - evenCeil ((N : ℝ) * t')) q.2.1 q.2.2 ω) *
          ((N : ℝ) / 4 * srwKernel
            (evenCeil ((N : ℝ) * t') - evenCeil ((N : ℝ) * t))
            (q.2.1 - q.1.2)) *
          ((volume (cell N q.1.2)).toReal * (volume (cell N q.2.1)).toReal) := by
  apply kernelProductPairing_polymer_eq_cellSum ϑ N hN s t t' u ω
    (fun w y => (N : ℝ) / 4 * srwKernel
      (evenCeil ((N : ℝ) * t') - evenCeil ((N : ℝ) * t)) (y - w))
    (slabMeanKernel ϑ N t t') ?_ Φ
  intro a b
  exact slabMeanKernel_eq_srwKernel ϑ N t t' a b

/-- On every four-cell term, the two middle cell volumes cancel the two extra density
normalizations in the continuum polymer product. -/
private theorem slabMean_cellTerm_eq_endpointTerm (ϑ : ℝ) (N : ℕ) (hN : 0 < N)
    {s t t' u : ℝ} (hst : s ≤ t) (ht'u : t' ≤ u)
    (ω : Disorder) (Φ : C_c(Plane × Plane, ℝ))
    (q : (Site × Site) × (Site × Site)) :
    (∫ p in cell N q.1.1 ×ˢ cell N q.2.2, Φ p) *
        ((N : ℝ) / 4 * pointToPoint (criticalBeta ϑ N)
          (evenCeil ((N : ℝ) * s))
          (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) q.1.1 q.1.2 ω) *
        ((N : ℝ) / 4 * pointToPoint (criticalBeta ϑ N)
          (evenCeil ((N : ℝ) * t'))
          (evenCeil ((N : ℝ) * u) - evenCeil ((N : ℝ) * t')) q.2.1 q.2.2 ω) *
        ((N : ℝ) / 4 * srwKernel
          (evenCeil ((N : ℝ) * t') - evenCeil ((N : ℝ) * t)) (q.2.1 - q.1.2)) *
        ((volume (cell N q.1.2)).toReal * (volume (cell N q.2.1)).toReal) =
      (∫ p in cell N q.1.1 ×ˢ cell N q.2.2, Φ p) * ((N : ℝ) / 4) *
        (pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s))
          (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) q.1.1 q.1.2 ω *
        srwKernel (evenCeil ((N : ℝ) * t') - evenCeil ((N : ℝ) * t))
          (q.2.1 - q.1.2) *
        pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * t'))
          (evenCeil ((N : ℝ) * u) - evenCeil ((N : ℝ) * t')) q.2.1 q.2.2 ω) := by
  classical
  by_cases hΦ : (∫ p in cell N q.1.1 ×ˢ cell N q.2.2, Φ p) = 0
  · simp [hΦ]
  by_cases hfirst : pointToPoint (criticalBeta ϑ N)
      (evenCeil ((N : ℝ) * s))
      (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) q.1.1 q.1.2 ω = 0
  · simp [hfirst]
  by_cases hlast : pointToPoint (criticalBeta ϑ N)
      (evenCeil ((N : ℝ) * t'))
      (evenCeil ((N : ℝ) * u) - evenCeil ((N : ℝ) * t')) q.2.1 q.2.2 ω = 0
  · simp [hlast]
  have houter₁ : q.1.1 ∈ evenLattice := by
    by_contra hx
    have he := cell_eq_empty_of_not_even (N := N) hx
    simp [he] at hΦ
  have houter₂ : q.2.2 ∈ evenLattice := by
    by_contra hz
    have he := cell_eq_empty_of_not_even (N := N) hz
    simp [he] at hΦ
  have hn₁ : Even (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) :=
    Critical2DKPZ.Smoothing.evenCeil_sub_even
      (mul_le_mul_of_nonneg_left hst (Nat.cast_nonneg N))
  have hn₃ : Even (evenCeil ((N : ℝ) * u) - evenCeil ((N : ℝ) * t')) :=
    Critical2DKPZ.Smoothing.evenCeil_sub_even
      (mul_le_mul_of_nonneg_left ht'u (Nat.cast_nonneg N))
  have hreach₁ : Polymer.Reachable
      (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) q.1.1 q.1.2 := by
    by_contra hn
    exact hfirst ((Polymer.pointToPoint_eq_zero_iff _ _ _ _ _ _).2 hn)
  have hreach₃ : Polymer.Reachable
      (evenCeil ((N : ℝ) * u) - evenCeil ((N : ℝ) * t')) q.2.1 q.2.2 := by
    by_contra hn
    exact hlast ((Polymer.pointToPoint_eq_zero_iff _ _ _ _ _ _).2 hn)
  have hmid₁ : q.1.2 ∈ evenLattice :=
    even_mem_endpoints_of_even houter₁ hn₁
      ((Polymer.mem_endpoints_iff _ _ _).2 hreach₁)
  have hterminal : q.2.2 ∈ Polymer.endpoints q.2.1
      (evenCeil ((N : ℝ) * u) - evenCeil ((N : ℝ) * t')) :=
    (Polymer.mem_endpoints_iff _ _ _).2 hreach₃
  have hreverse := mem_endpoints_reverse hterminal
  have hmid₂ : q.2.1 ∈ evenLattice := even_mem_endpoints_of_even houter₂ hn₃ hreverse
  rw [volume_cell_toReal hN hmid₁, volume_cell_toReal hN hmid₂]
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp [hNne]

/-- The continuum cell expansion of the product through the annealed slab is the same finite
Chapman--Kolmogorov sum as averaging the resampled polymer pairing. -/
private theorem kernelProductPairing_slabMean_eq_resampleCellSum (ϑ : ℝ) (N : ℕ)
    (hN : 0 < N) {s t t' u : ℝ} (hst : s ≤ t) (ht'u : t' ≤ u)
    (ω : Disorder) (Φ : C_c(Plane × Plane, ℝ)) :
    kernelProductPairing (polymerMeasure ϑ N s t ω) (slabMeanKernel ϑ N t t')
        (polymerMeasure ϑ N t' u ω) Φ =
      (N : ℝ) / 4 * ∑ q ∈ (finite_support_cellPairTest N Φ).toFinset,
        (∫ p in cell N q.1 ×ˢ cell N q.2, Φ p) *
          ∑' w, ∑' y,
            pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s))
              (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) q.1 w ω *
            srwKernel (evenCeil ((N : ℝ) * t') - evenCeil ((N : ℝ) * t)) (y - w) *
            pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * t'))
              (evenCeil ((N : ℝ) * u) - evenCeil ((N : ℝ) * t')) y q.2 ω := by
  classical
  let S : Finset (Site × Site) := (finite_support_cellPairTest N Φ).toFinset
  let cellTest : Site × Site → ℝ := fun q => ∫ p in cell N q.1 ×ˢ cell N q.2, Φ p
  let n₁ := evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)
  let m := evenCeil ((N : ℝ) * t') - evenCeil ((N : ℝ) * t)
  let n₃ := evenCeil ((N : ℝ) * u) - evenCeil ((N : ℝ) * t')
  let W : Site × Site → Finset Site := fun q => Polymer.endpoints q.1 n₁
  let Z : Site × Site → Finset Site := fun q => Polymer.endpoints q.2 n₃
  let f : (Site × Site) × (Site × Site) → ℝ := fun p =>
    cellTest p.1 * ((N : ℝ) / 4) *
      (pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s)) n₁ p.1.1 p.2.1 ω *
        srwKernel m (p.2.2 - p.2.1) *
        pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * t')) n₃ p.2.2 p.1.2 ω)
  let Q : Finset ((Site × Site) × (Site × Site)) :=
    S.biUnion fun q => ((W q).product (Z q)).image fun r => (q, r)
  have hcellzero {q : Site × Site} (hq : q ∉ S) : cellTest q = 0 := by
    dsimp [S, cellTest] at *
    by_contra hne
    exact hq ((finite_support_cellPairTest N Φ).mem_toFinset.mpr hne)
  have hinner (q : Site × Site) : Summable (fun r : Site × Site => f (q, r)) := by
    apply summable_of_ne_finset_zero (s := (W q).product (Z q))
    intro r hr
    by_cases hw : r.1 ∈ W q
    · have hy : r.2 ∉ Z q := by
        intro hy
        exact hr (Finset.mem_product.mpr ⟨hw, hy⟩)
      have hlast : pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * t')) n₃
          r.2 q.2 ω = 0 := by
        apply Polymer.pointToPoint_eq_zero_of_not_mem
        intro hreach
        exact hy (mem_endpoints_reverse hreach)
      simp [f, hlast]
    · have hfirst : pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s)) n₁
          q.1 r.1 ω = 0 :=
        Polymer.pointToPoint_eq_zero_of_not_mem (criticalBeta ϑ N)
          (evenCeil ((N : ℝ) * s)) n₁ q.1 r.1 ω (by simpa [W] using hw)
      simp [f, hfirst]
  have hprod : Summable f := by
    apply summable_of_ne_finset_zero (s := Q)
    rintro ⟨q, r⟩ hqr
    by_cases hq : q ∈ S
    · have hr : r ∉ (W q).product (Z q) := by
        intro hr
        apply hqr
        exact Finset.mem_biUnion.mpr ⟨q, hq,
          Finset.mem_image.mpr ⟨r, hr, rfl⟩⟩
      have hr' : ¬ (r.1 ∈ W q ∧ r.2 ∈ Z q) := by
        intro hm
        exact hr (Finset.mem_product.mpr hm)
      by_cases hw : r.1 ∈ W q
      · have hy : r.2 ∉ Z q := fun hy => hr' ⟨hw, hy⟩
        have hlast : pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * t')) n₃
            r.2 q.2 ω = 0 := by
          apply Polymer.pointToPoint_eq_zero_of_not_mem
          intro hreach
          exact hy (mem_endpoints_reverse hreach)
        simp [f, hlast]
      · have hfirst : pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s)) n₁
            q.1 r.1 ω = 0 :=
          Polymer.pointToPoint_eq_zero_of_not_mem (criticalBeta ϑ N)
            (evenCeil ((N : ℝ) * s)) n₁ q.1 r.1 ω (by simpa [W] using hw)
        simp [f, hfirst]
    · simp [f, hcellzero hq]
  let e : ((Site × Site) × (Site × Site)) ≃ ((Site × Site) × (Site × Site)) :=
    { toFun := fun q => ((q.1.1, q.2.2), (q.1.2, q.2.1))
      invFun := fun q => ((q.1.1, q.2.1), (q.2.2, q.1.2))
      left_inv := by intro q; cases q with | mk a b => cases a; cases b; rfl
      right_inv := by intro q; cases q with | mk a b => cases a; cases b; rfl }
  -- The inverse keeps the four coordinates in their original order, arranged as the
  -- outer cell pair and the two middle endpoints.
  have heq : ∀ q : (Site × Site) × (Site × Site),
      (∫ p in cell N q.1.1 ×ˢ cell N q.2.2, Φ p) *
          ((N : ℝ) / 4 * pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s)) n₁
            q.1.1 q.1.2 ω) *
          ((N : ℝ) / 4 * pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * t')) n₃
            q.2.1 q.2.2 ω) *
          ((N : ℝ) / 4 * srwKernel m (q.2.1 - q.1.2)) *
          ((volume (cell N q.1.2)).toReal * (volume (cell N q.2.1)).toReal) =
        f (e q) := by
    intro q
    dsimp [f, cellTest, n₁, m, n₃, e]
    exact slabMean_cellTerm_eq_endpointTerm ϑ N hN hst ht'u ω Φ q
  calc
    _ = ∑' q : (Site × Site) × (Site × Site),
        (∫ p in cell N q.1.1 ×ˢ cell N q.2.2, Φ p) *
          ((N : ℝ) / 4 * pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s)) n₁
            q.1.1 q.1.2 ω) *
          ((N : ℝ) / 4 * pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * t')) n₃
            q.2.1 q.2.2 ω) *
          ((N : ℝ) / 4 * srwKernel m (q.2.1 - q.1.2)) *
          ((volume (cell N q.1.2)).toReal * (volume (cell N q.2.1)).toReal) :=
      kernelProductPairing_slabMean_eq_cellSum ϑ N hN s t t' u ω Φ
    _ = ∑' q, f (e q) := by
      apply tsum_congr
      exact heq
    _ = ∑' q, f q := e.tsum_eq f
    _ = ∑' q, ∑' r, f (q, r) := hprod.tsum_prod' hinner
    _ = ∑' q, cellTest q * ((N : ℝ) / 4) *
          ∑' w, ∑' y,
            pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s)) n₁ q.1 w ω *
              srwKernel m (y - w) *
              pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * t')) n₃ y q.2 ω := by
      apply tsum_congr
      intro q
      calc
        _ = ∑' w, ∑' y, f (q, (w, y)) := (hinner q).tsum_prod
        _ = _ := by
          simp only [f]
          calc
            _ = ∑' w, cellTest q * ((N : ℝ) / 4) *
                ∑' y,
                  pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s)) n₁ q.1 w ω *
                    srwKernel m (y - w) *
                    pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * t')) n₃ y q.2 ω := by
              apply tsum_congr
              intro w
              rw [← tsum_mul_left]
            _ = cellTest q * ((N : ℝ) / 4) *
                ∑' w, ∑' y,
                  pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s)) n₁ q.1 w ω *
                    srwKernel m (y - w) *
                    pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * t')) n₃ y q.2 ω := by
              rw [← tsum_mul_left]
    _ = (N : ℝ) / 4 * ∑ q ∈ S, cellTest q *
          ∑' w, ∑' y,
            pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s)) n₁ q.1 w ω *
              srwKernel m (y - w) *
              pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * t')) n₃ y q.2 ω := by
      rw [tsum_eq_sum (s := S) (fun q hq => by rw [hcellzero hq]; simp)]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring

/-- Resampling the middle time block and integrating it gives the continuum product through
the annealed slab kernel. -/
theorem integral_polymerPairing_resample_slab_eq_kernelProductPairing
    (ϑ : ℝ) (N : ℕ) (hN : 0 < N) {s t t' u : ℝ}
    (hst : s ≤ t) (htt' : t ≤ t') (ht'u : t' ≤ u)
    (Φ : C_c(Plane × Plane, ℝ)) (ω : Disorder) :
    ∫ η, (∫ p, Φ p ∂(polymerMeasure ϑ N s u
      (Gaussian.resample (Gaussian.timeBlock (evenCeil ((N : ℝ) * t))
        (evenCeil ((N : ℝ) * t'))) η ω))) ∂disorderLaw =
      kernelProductPairing (polymerMeasure ϑ N s t ω) (slabMeanKernel ϑ N t t')
        (polymerMeasure ϑ N t' u ω) Φ := by
  classical
  let a := evenCeil ((N : ℝ) * s)
  let b := evenCeil ((N : ℝ) * t)
  let c := evenCeil ((N : ℝ) * t')
  let d := evenCeil ((N : ℝ) * u)
  have hab : a ≤ b := by
    dsimp [a, b]
    exact Critical2DKPZ.evenCeil_mono
      (mul_le_mul_of_nonneg_left hst (Nat.cast_nonneg N))
  have hbc : b ≤ c := by
    dsimp [b, c]
    exact Critical2DKPZ.evenCeil_mono
      (mul_le_mul_of_nonneg_left htt' (Nat.cast_nonneg N))
  have hcd : c ≤ d := by
    dsimp [c, d]
    exact Critical2DKPZ.evenCeil_mono
      (mul_le_mul_of_nonneg_left ht'u (Nat.cast_nonneg N))
  rw [integral_polymerPairing_resample_slab_cellSum ϑ N hst htt' ht'u Φ ω]
  rw [kernelProductPairing_slabMean_eq_resampleCellSum ϑ N hN hst ht'u ω Φ]

/-- Reversing which sample supplies the slab and its complement identifies the resampling
used in conditional expectation with the polymer slab resampling. -/
theorem resample_compl_eq_swapped (T : Set (ℕ × Site)) (ω η : Disorder) :
    Gaussian.resample Tᶜ ω η = Gaussian.resample T η ω := by
  funext i
  by_cases hi : i ∈ T
  · simp [Gaussian.resample, hi]
  · simp [Gaussian.resample, hi]

/-- The zero scale gives the zero polymer measure. -/
theorem polymerMeasure_zero_at_zero (ϑ : ℝ) (s t : ℝ) (ω : Disorder) :
    polymerMeasure ϑ 0 s t ω = 0 := by
  rw [polymerMeasure]
  ext A hA
  simp [rescaledP2P]

/-- A square-integrable conditional mean is the orthogonal projection in `L²`, giving the exact
variance decomposition used when a finite disorder slab is annealed. -/
theorem integral_sq_sub_condExp_eq (Ω : Type*) [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {Y S : Ω → ℝ} (hY : MemLp Y 2 μ) (hS : MemLp S 2 μ)
    (hSm : AEStronglyMeasurable[m] S μ) (hSce : S =ᵐ[μ] μ[Y | m]) :
    Integrable (fun ω => (Y ω - S ω) ^ 2) μ ∧
    ∫ ω, (Y ω - S ω) ^ 2 ∂μ = ∫ ω, Y ω ^ 2 ∂μ - ∫ ω, S ω ^ 2 ∂μ := by
  have hYsq : Integrable (fun ω => Y ω ^ 2) μ := by
    have h := hY.integrable_norm_pow'
    apply h.congr
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, sq_abs]
  have hSsq : Integrable (fun ω => S ω ^ 2) μ := by
    have h := hS.integrable_norm_pow'
    apply h.congr
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, sq_abs]
  have hdiff : MemLp (fun ω => Y ω - S ω) 2 μ := hY.sub hS
  have hdiffsq : Integrable (fun ω => (Y ω - S ω) ^ 2) μ := by
    have h := hdiff.integrable_norm_pow'
    apply h.congr
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, sq_abs]
  have hcross : Integrable (fun ω => Y ω * S ω) μ := hY.integrable_mul hS
  have hCE := hY.condExpL2_ae_eq_condExp (E := ℝ) (𝕜 := ℝ)
    (m₀ := mΩ) hm
  have hCEs : (condExpL2 ℝ ℝ hm (hY.toLp Y) : Ω → ℝ) =ᵐ[μ] S := hCE.trans hSce.symm
  have hYto : (hY.toLp Y : Ω → ℝ) =ᵐ[μ] Y := hY.coeFn_toLp
  have hSto : (hS.toLp S : Ω → ℝ) =ᵐ[μ] S := hS.coeFn_toLp
  have hSmLp : AEStronglyMeasurable[m] (hS.toLp S : Ω → ℝ) μ := hSm.congr hSto.symm
  have hinner := inner_condExpL2_eq_inner_fun (E := ℝ) (𝕜 := ℝ)
    hm (hY.toLp Y) (hS.toLp S) hSmLp
  rw [L2.inner_def, L2.inner_def] at hinner
  simp only [Real.inner_apply] at hinner
  have hinnerInt :
      (∫ ω, (condExpL2 ℝ ℝ hm (hY.toLp Y) : Ω → ℝ) ω * S ω ∂μ) =
        ∫ ω, Y ω * S ω ∂μ := by
    calc
      ∫ ω, (condExpL2 ℝ ℝ hm (hY.toLp Y) : Ω → ℝ) ω * S ω ∂μ =
          ∫ ω, (condExpL2 ℝ ℝ hm (hY.toLp Y) : Ω → ℝ) ω * (hS.toLp S) ω ∂μ := by
            apply integral_congr_ae
            filter_upwards [hSto] with ω hs
            rw [hs]
      _ = ∫ ω, (hY.toLp Y) ω * (hS.toLp S) ω ∂μ := by
            change (∫ ω, (condExpL2 ℝ ℝ hm (hY.toLp Y) : Ω → ℝ) ω *
              (hS.toLp S) ω ∂μ) = _ at hinner
            exact hinner
      _ = ∫ ω, Y ω * S ω ∂μ := by
            apply integral_congr_ae
            filter_upwards [hYto, hSto] with ω hy hs
            rw [hy, hs]
  have hcrossEq : (∫ ω, Y ω * S ω ∂μ) = ∫ ω, S ω ^ 2 ∂μ := by
    calc
      ∫ ω, Y ω * S ω ∂μ =
          ∫ ω, (condExpL2 ℝ ℝ hm (hY.toLp Y) : Ω → ℝ) ω * S ω ∂μ := hinnerInt.symm
      _ = ∫ ω, S ω ^ 2 ∂μ := by
            apply integral_congr_ae
            filter_upwards [hCEs] with ω hc
            rw [hc]
            ring
  have hdecomp (ω : Ω) : (Y ω - S ω) ^ 2 =
      Y ω ^ 2 - 2 * (Y ω * S ω) + S ω ^ 2 := by ring
  refine ⟨hdiffsq, ?_⟩
  calc
    ∫ ω, (Y ω - S ω) ^ 2 ∂μ =
        ∫ ω, (Y ω ^ 2 - 2 * (Y ω * S ω) + S ω ^ 2) ∂μ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hdecomp
    _ = (∫ ω, Y ω ^ 2 ∂μ) - 2 * (∫ ω, Y ω * S ω ∂μ) +
        ∫ ω, S ω ^ 2 ∂μ := by
          calc
            _ = (∫ ω, Y ω ^ 2 - 2 * (Y ω * S ω) ∂μ) +
                ∫ ω, S ω ^ 2 ∂μ := integral_add (hYsq.sub (hcross.const_mul 2)) hSsq
            _ = _ := by rw [integral_sub hYsq (hcross.const_mul 2), integral_const_mul]
    _ = ∫ ω, Y ω ^ 2 ∂μ - ∫ ω, S ω ^ 2 ∂μ := by rw [hcrossEq]; ring

end Critical2DKPZ.SHF.Flow

end
