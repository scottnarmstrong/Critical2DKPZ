/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

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

/-! # Lattice cell expansions for polymer slab pairings -/

@[expose] public noncomputable section

open MeasureTheory
open scoped CompactlySupported

namespace Critical2DKPZ.SHF.Flow

open Critical2DKPZ.SHF.Limit

/-- A compact test paired with a function constant on lattice cell pairs is the sum of its cell
integrals times those lattice values. The statement is valid also at the zero scale. -/
theorem integral_latticePairing_eq_cellTsum (N : ℕ) (Φ : C_c(Plane × Plane, ℝ))
    (G : Site → Site → ℝ) :
    ∫ p : Plane × Plane, Φ p * G (latticePoint N p.1) (latticePoint N p.2) =
      ∑' q : Site × Site,
        (∫ p in cell N q.1 ×ˢ cell N q.2, Φ p) * G q.1 q.2 := by
  classical
  let K : Set (Plane × Plane) := tsupport Φ
  have hK : IsCompact K := Φ.hasCompactSupport
  let K₁ : Set Plane := Prod.fst '' K
  let K₂ : Set Plane := Prod.snd '' K
  have hK₁ : IsCompact K₁ := by
    exact hK.image continuous_fst
  have hK₂ : IsCompact K₂ := by
    exact hK.image continuous_snd
  let S₁ : Set Site := latticePoint N '' K₁
  let S₂ : Set Site := latticePoint N '' K₂
  have hS₁ : S₁.Finite := by
    exact finite_latticePoint_image_of_bounded hK₁.isBounded
  have hS₂ : S₂.Finite := by
    exact finite_latticePoint_image_of_bounded hK₂.isBounded
  let V : Set ℝ := (fun q : Site × Site => |G q.1 q.2|) '' (S₁ ×ˢ S₂)
  have hV : V.Finite := (hS₁.prod hS₂).image _
  obtain ⟨B, hB⟩ := hV.bddAbove
  let C : ℝ := max B 0
  have hC : 0 ≤ C := le_max_right _ _
  have hGbound (x y : Site) (hx : x ∈ S₁) (hy : y ∈ S₂) : |G x y| ≤ C := by
    have hval : |G x y| ∈ V := ⟨(x, y), ⟨hx, hy⟩, rfl⟩
    exact (hB hval).trans (le_max_left _ _)
  let H : Plane × Plane → ℝ := fun p =>
    Φ p * G (latticePoint N p.1) (latticePoint N p.2)
  have hHm : Measurable H := by
    dsimp [H]
    exact Φ.measurable.mul ((measurable_of_countable (fun q : Site × Site => G q.1 q.2)).comp
      (((measurable_latticePoint N).comp measurable_fst).prodMk
        ((measurable_latticePoint N).comp measurable_snd)))
  have hH : Integrable H := by
    apply ((Φ.continuous.integrable_of_hasCompactSupport Φ.hasCompactSupport).norm.const_mul C).mono'
      hHm.aestronglyMeasurable
    filter_upwards [] with p
    by_cases hp : Φ p = 0
    · simp [H, hp]
    · have hpK : p ∈ K := subset_closure (Function.mem_support.mpr hp)
      have hx : latticePoint N p.1 ∈ S₁ :=
        ⟨p.1, ⟨p, hpK, rfl⟩, rfl⟩
      have hy : latticePoint N p.2 ∈ S₂ :=
        ⟨p.2, ⟨p, hpK, rfl⟩, rfl⟩
      have hbound := hGbound _ _ hx hy
      calc
        ‖H p‖ = ‖Φ p‖ * |G (latticePoint N p.1) (latticePoint N p.2)| := by
          dsimp [H]
          simp only [abs_mul]
        _ ≤ ‖Φ p‖ * C := mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
        _ = C * ‖Φ p‖ := by ring
  have hcover : (⋃ q : Site × Site, cell N q.1 ×ˢ cell N q.2) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro p
    exact Set.mem_iUnion.mpr ⟨(latticePoint N p.1, latticePoint N p.2),
      ⟨mem_cell_latticePoint N p.1, mem_cell_latticePoint N p.2⟩⟩
  have hdisj : Pairwise (fun q r : Site × Site =>
      Disjoint (cell N q.1 ×ˢ cell N q.2) (cell N r.1 ×ˢ cell N r.2)) := by
    intro q r hqr
    apply Set.disjoint_left.mpr
    intro p hpq hpr
    rcases Set.mem_prod.mp hpq with ⟨hx, hy⟩
    rcases Set.mem_prod.mp hpr with ⟨hx', hy'⟩
    by_cases hfirst : q.1 = r.1
    · have hsecond : q.2 ≠ r.2 := by
        intro heq
        apply hqr
        exact Prod.ext hfirst heq
      exact (Set.disjoint_left.mp (pairwise_disjoint_cell N hsecond)) hy hy'
    · exact (Set.disjoint_left.mp (pairwise_disjoint_cell N hfirst)) hx hx'
  have hsum := integral_iUnion
    (fun q : Site × Site => (measurableSet_cell N q.1).prod (measurableSet_cell N q.2))
    hdisj hH.integrableOn
  rw [hcover, setIntegral_univ] at hsum
  have hcell (q : Site × Site) :
      ∫ p in cell N q.1 ×ˢ cell N q.2, H p =
        (∫ p in cell N q.1 ×ˢ cell N q.2, Φ p) * G q.1 q.2 := by
    calc
      ∫ p in cell N q.1 ×ˢ cell N q.2, H p =
          ∫ p in cell N q.1 ×ˢ cell N q.2, Φ p * G q.1 q.2 := by
            apply setIntegral_congr_fun
              ((measurableSet_cell N q.1).prod (measurableSet_cell N q.2))
            intro p hp
            rcases Set.mem_prod.mp hp with ⟨hp₁, hp₂⟩
            simp only [mem_cell_iff] at hp₁ hp₂
            simp [H, hp₁, hp₂]
      _ = (∫ p in cell N q.1 ×ˢ cell N q.2, Φ p) * G q.1 q.2 := by
          rw [integral_mul_const]
  calc
    _ = ∑' q : Site × Site, ∫ p in cell N q.1 ×ˢ cell N q.2, H p := by
      exact hsum
    _ = ∑' q : Site × Site,
        (∫ p in cell N q.1 ×ˢ cell N q.2, Φ p) * G q.1 q.2 := by
      apply tsum_congr
      exact hcell

/-- Integrating a finitely supported lattice step function gives the exact sum of its cell
values times cell-pair volumes. This is the middle-variable counterpart of
`integral_latticePairing_eq_cellTsum`. -/
theorem integral_finiteLatticeStep_eq_cellSum (N : ℕ) (hN : 0 < N)
    (G : Site → Site → ℝ) (hG : {q : Site × Site | G q.1 q.2 ≠ 0}.Finite) :
    ∫ p : Plane × Plane, G (latticePoint N p.1) (latticePoint N p.2) =
      ∑ q ∈ hG.toFinset, G q.1 q.2 * (volume (cell N q.1 ×ˢ cell N q.2)).toReal := by
  classical
  let S : Finset (Site × Site) := hG.toFinset
  let A : Site × Site → Set (Plane × Plane) := fun q => cell N q.1 ×ˢ cell N q.2
  let H : Plane × Plane → ℝ := fun p => G (latticePoint N p.1) (latticePoint N p.2)
  have hAmeas (q : Site × Site) : MeasurableSet (A q) := by
    exact (measurableSet_cell N q.1).prod (measurableSet_cell N q.2)
  have hcellVolume (z : Site) : volume (cell N z) < ⊤ := by
    by_cases hz : z ∈ evenLattice
    · exact volume_cell_lt_top hN hz
    · simp [cell_eq_empty_of_not_even hz]
  have hAfin (q : Site × Site) : volume (A q) < ⊤ := by
    change volume (cell N q.1 ×ˢ cell N q.2) < ⊤
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_lt_top (hcellVolume q.1) (hcellVolume q.2)
  have hrepr (p : Plane × Plane) :
      H p = ∑ q ∈ S, Set.indicator (A q) (fun _ => G q.1 q.2) p := by
    classical
    let q₀ : Site × Site := (latticePoint N p.1, latticePoint N p.2)
    change G q₀.1 q₀.2 = _
    rw [Finset.sum_eq_single q₀]
    · by_cases hq₀ : q₀ ∈ S
      · have hp₀ : p ∈ A q₀ := by
          exact ⟨mem_cell_latticePoint N p.1, mem_cell_latticePoint N p.2⟩
        simp [A, hp₀]
      · have hG₀ : G q₀.1 q₀.2 = 0 := by
          by_contra hne
          exact hq₀ (hG.mem_toFinset.mpr hne)
        simp [hG₀]
    · intro q hq hqne
      have hnot : p ∉ A q := by
        intro hp
        have hq₀ : q₀ = q := by
          apply Prod.ext
          · exact (mem_cell_iff N q.1 p.1).mp hp.1
          · exact (mem_cell_iff N q.2 p.2).mp hp.2
        exact hqne hq₀.symm
      simp [Set.indicator, hnot]
    · intro hq₀
      have hG₀ : G q₀.1 q₀.2 = 0 := by
        by_contra hne
        exact hq₀ (hG.mem_toFinset.mpr hne)
      simp [hG₀]
  have hHintegrable : Integrable H := by
    rw [show H = fun p => ∑ q ∈ S, Set.indicator (A q) (fun _ => G q.1 q.2) p by
      funext p
      exact hrepr p]
    apply integrable_finsetSum
    intro q hq
    rw [integrable_indicator_iff (hAmeas q)]
    exact integrableOn_const (hAfin q).ne
  have hcover : (⋃ q : Site × Site, A q) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro p
    exact Set.mem_iUnion.mpr ⟨(latticePoint N p.1, latticePoint N p.2),
      ⟨mem_cell_latticePoint N p.1, mem_cell_latticePoint N p.2⟩⟩
  have hdisj : Pairwise (fun q r : Site × Site => Disjoint (A q) (A r)) := by
    intro q r hqr
    apply Set.disjoint_left.mpr
    intro p hpq hpr
    rcases Set.mem_prod.mp hpq with ⟨hx, hy⟩
    rcases Set.mem_prod.mp hpr with ⟨hx', hy'⟩
    by_cases hfirst : q.1 = r.1
    · have hsecond : q.2 ≠ r.2 := by
        intro heq
        exact hqr (Prod.ext hfirst heq)
      exact (Set.disjoint_left.mp (pairwise_disjoint_cell N hsecond)) hy hy'
    · exact (Set.disjoint_left.mp (pairwise_disjoint_cell N hfirst)) hx hx'
  have hsum := integral_iUnion hAmeas hdisj hHintegrable.integrableOn
  rw [hcover, setIntegral_univ] at hsum
  have hcell (q : Site × Site) :
      ∫ p in A q, H p = G q.1 q.2 * (volume (A q)).toReal := by
    calc
      ∫ p in A q, H p = ∫ p in A q, (fun _ : Plane × Plane => G q.1 q.2) p := by
        apply setIntegral_congr_fun (hAmeas q)
        intro p hp
        simp only [H, A, Set.mem_prod] at hp ⊢
        rw [(mem_cell_iff N q.1 p.1).mp hp.1, (mem_cell_iff N q.2 p.2).mp hp.2]
      _ = G q.1 q.2 * (volume (A q)).toReal := by
        rw [setIntegral_const, smul_eq_mul, measureReal_def]
        ring
  calc
    ∫ p : Plane × Plane, H p = ∑' q : Site × Site, ∫ p in A q, H p := by
      exact hsum
    _ = ∑ q ∈ S, ∫ p in A q, H p := by
      rw [tsum_eq_sum (s := S) (fun q hq => by
        have hzero : G q.1 q.2 = 0 := by
          by_contra hne
          exact hq (hG.mem_toFinset.mpr hne)
        rw [hcell, hzero]
        simp)]
    _ = ∑ q ∈ S, G q.1 q.2 * (volume (A q)).toReal := by
      apply Finset.sum_congr rfl
      intro q hq
      exact hcell q
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q hq
      rfl

/-- On a product of four lattice cells, a test depending on the two outer variables integrates
to its outer cell integral times the two middle cell volumes. -/
theorem integral_fourCellTest (N : ℕ) (hN : 0 < N) (q : (Site × Site) × (Site × Site))
    (Φ : C_c(Plane × Plane, ℝ)) :
    ∫ p in (cell N q.1.1 ×ˢ cell N q.1.2) ×ˢ (cell N q.2.1 ×ˢ cell N q.2.2),
        Φ (p.1.1, p.2.2) ∂((volume : Measure (Plane × Plane)).prod volume) =
      (volume (cell N q.1.2)).toReal * (volume (cell N q.2.1)).toReal *
        ∫ p in cell N q.1.1 ×ˢ cell N q.2.2, Φ p := by
  classical
  let A₁ : Set (Plane × Plane) := cell N q.1.1 ×ˢ cell N q.1.2
  let A₂ : Set (Plane × Plane) := cell N q.2.1 ×ˢ cell N q.2.2
  have hcellFinite (z : Site) : volume (cell N z) < ⊤ := by
    by_cases hz : z ∈ evenLattice
    · exact volume_cell_lt_top hN hz
    · simp [cell_eq_empty_of_not_even hz]
  obtain ⟨C, hC⟩ := Φ.continuous.bounded_above_of_compact_support Φ.hasCompactSupport
  have hpairFinite (a b : Site) :
      (volume : Measure (Plane × Plane)) (cell N a ×ˢ cell N b) < ⊤ := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_lt_top (hcellFinite a) (hcellFinite b)
  have hAfinite :
      ((volume : Measure (Plane × Plane)).prod volume) (A₁ ×ˢ A₂) < ⊤ := by
    dsimp only [A₁, A₂]
    rw [Measure.prod_prod]
    exact ENNReal.mul_lt_top (hpairFinite q.1.1 q.1.2) (hpairFinite q.2.1 q.2.2)
  have hFint : IntegrableOn (fun p : (Plane × Plane) × (Plane × Plane) =>
      Φ (p.1.1, p.2.2)) (A₁ ×ˢ A₂)
      ((volume : Measure (Plane × Plane)).prod volume) := by
    have hconst : IntegrableOn (fun _ : (Plane × Plane) × (Plane × Plane) => C)
        (A₁ ×ˢ A₂) ((volume : Measure (Plane × Plane)).prod volume) :=
      integrableOn_const hAfinite.ne
    apply hconst.mono'
    · exact ((Φ.continuous.comp (by fun_prop)).aestronglyMeasurable)
    · filter_upwards [] with p
      have h := hC (p.1.1, p.2.2)
      exact h
  have hcellRestr (a b : Site) :
      (volume : Measure (Plane × Plane)).restrict (cell N a ×ˢ cell N b) =
        (volume.restrict (cell N a)).prod (volume.restrict (cell N b)) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  have houterInt : IntegrableOn Φ (cell N q.1.1 ×ˢ cell N q.2.2)
      (volume : Measure (Plane × Plane)) := by
    have hconst : IntegrableOn (fun _ : Plane × Plane => C)
        (cell N q.1.1 ×ˢ cell N q.2.2) (volume : Measure (Plane × Plane)) := by
      exact integrableOn_const (by
        rw [Measure.volume_eq_prod, Measure.prod_prod]
        exact (ENNReal.mul_lt_top (hcellFinite q.1.1) (hcellFinite q.2.2)).ne) (by finiteness)
    apply hconst.mono'
    · exact Φ.continuous.aestronglyMeasurable
    · filter_upwards [] with p
      have h := hC p
      exact h
  have houterProdInt : Integrable Φ
      ((volume.restrict (cell N q.1.1)).prod (volume.restrict (cell N q.2.2))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact houterInt
  calc
    _ = ∫ p, Φ (p.1.1, p.2.2) ∂
        ((volume.restrict A₁).prod (volume.restrict A₂)) := by
      rw [← Measure.prod_restrict]
    _ = ∫ p : Plane × Plane, ∫ r : Plane × Plane, Φ (p.1, r.2)
          ∂(volume.restrict A₂) ∂(volume.restrict A₁) := by
      apply integral_prod
      rw [Measure.prod_restrict]
      exact hFint
    _ = _ := by
      rw [hcellRestr q.2.1 q.2.2, hcellRestr q.1.1 q.1.2]
      have hinner (p : Plane × Plane) :
          ∫ r : Plane × Plane, Φ (p.1, r.2)
              ∂(volume.restrict (cell N q.2.1)).prod (volume.restrict (cell N q.2.2)) =
            (volume.restrict (cell N q.2.1)).real Set.univ •
              ∫ z, Φ (p.1, z) ∂(volume.restrict (cell N q.2.2)) := by
        exact integral_fun_snd (fun z : Plane => Φ (p.1, z))
      have hdouble :
          ∫ x, ∫ z, Φ (x, z) ∂(volume.restrict (cell N q.2.2))
              ∂(volume.restrict (cell N q.1.1)) =
            ∫ p in cell N q.1.1 ×ˢ cell N q.2.2, Φ p := by
        calc
          _ = ∫ p, Φ p ∂
              ((volume.restrict (cell N q.1.1)).prod
                (volume.restrict (cell N q.2.2))) := (integral_prod _ houterProdInt).symm
          _ = ∫ p in cell N q.1.1 ×ˢ cell N q.2.2, Φ p := by
            rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
      calc
        _ = ∫ p : Plane × Plane,
            (volume.restrict (cell N q.2.1)).real Set.univ •
              ∫ z, Φ (p.1, z) ∂(volume.restrict (cell N q.2.2))
              ∂((volume.restrict (cell N q.1.1)).prod
                (volume.restrict (cell N q.1.2))) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hinner
        _ = (volume.restrict (cell N q.2.1)).real Set.univ •
              ∫ p : Plane × Plane, (∫ z, Φ (p.1, z)
                ∂(volume.restrict (cell N q.2.2)))
                ∂((volume.restrict (cell N q.1.1)).prod
                  (volume.restrict (cell N q.1.2))) := by
            simp only [smul_eq_mul]
            rw [integral_const_mul]
        _ = (volume.restrict (cell N q.2.1)).real Set.univ •
              ((volume.restrict (cell N q.1.2)).real Set.univ •
                ∫ x, ∫ z, Φ (x, z) ∂(volume.restrict (cell N q.2.2))
                  ∂(volume.restrict (cell N q.1.1))) := by
            congr 1
            exact integral_fun_fst (fun x : Plane =>
              ∫ z, Φ (x, z) ∂(volume.restrict (cell N q.2.2)))
        _ = _ := by
            rw [hdouble]
            simp only [smul_eq_mul, measureReal_def, Measure.restrict_apply_univ]
            ring

/-- The finite walk endpoint relation is symmetric in its two sites. -/
theorem mem_endpoints_reverse {n : ℕ} {x y : Site}
    (hy : y ∈ Polymer.endpoints x n) : x ∈ Polymer.endpoints y n := by
  rw [Polymer.mem_endpoints_iff] at hy ⊢
  rcases hy with ⟨s, hs⟩
  refine ⟨fun i => Polymer.oppositeStep (s i), ?_⟩
  rw [Polymer.walkPosition_end] at hs ⊢
  have hsum : (∑ i, srwStep (Polymer.oppositeStep (s i))) =
      -(∑ i, srwStep (s i)) := by
    simp only [Polymer.srwStep_opposite, Finset.sum_neg_distrib]
  rw [hsum, ← hs]
  abel

/-- An even number of nearest-neighbour steps preserves the even sublattice. -/
theorem even_mem_endpoints_of_even {n : ℕ} {x y : Site}
    (hx : Even (x 0 + x 1)) (hn : Even n) (hy : y ∈ Polymer.endpoints x n) :
    Even (y 0 + y 1) := by
  obtain ⟨s, hs⟩ := (Polymer.mem_endpoints_iff x y n).mp hy
  rw [← hs]
  have hmod := Polymer.walkPosition_parity x s
  change (walkPosition x s n 0 + walkPosition x s n 1) % 2 =
    (x 0 + x 1 + n) % 2 at hmod
  have hright : Even (x 0 + x 1 + n) := by
    simp [Int.even_add, hx, Int.even_coe_nat, hn]
  apply Int.even_iff.mpr
  rw [hmod]
  exact Int.even_iff.mp hright


/-- A finitely supported four-site lattice coefficient can be integrated against a compact
outer test by summing its exact four-cell contributions. -/
theorem integral_finiteLatticeFourStep_eq_cellSum (N : ℕ) (hN : 0 < N)
    (Φ : C_c(Plane × Plane, ℝ)) (G : (Site × Site) × (Site × Site) → ℝ)
    (hG : {q : (Site × Site) × (Site × Site) | G q ≠ 0}.Finite) :
    ∫ p : (Plane × Plane) × (Plane × Plane),
        Φ (p.1.1, p.2.2) *
          G ((latticePoint N p.1.1, latticePoint N p.1.2),
            (latticePoint N p.2.1, latticePoint N p.2.2))
          ∂((volume : Measure (Plane × Plane)).prod volume) =
      ∑ q ∈ hG.toFinset,
        (∫ x in cell N q.1.1 ×ˢ cell N q.2.2, Φ x) * G q *
          ((volume (cell N q.1.2)).toReal * (volume (cell N q.2.1)).toReal) := by
  classical
  let S : Finset ((Site × Site) × (Site × Site)) := hG.toFinset
  let A : ((Site × Site) × (Site × Site)) → Set ((Plane × Plane) × (Plane × Plane)) :=
    fun q => (cell N q.1.1 ×ˢ cell N q.1.2) ×ˢ (cell N q.2.1 ×ˢ cell N q.2.2)
  let H : ((Plane × Plane) × (Plane × Plane)) → ℝ := fun p =>
    Φ (p.1.1, p.2.2) *
      G ((latticePoint N p.1.1, latticePoint N p.1.2),
        (latticePoint N p.2.1, latticePoint N p.2.2))
  obtain ⟨C, hC⟩ := Φ.continuous.bounded_above_of_compact_support Φ.hasCompactSupport
  have hCnonneg : 0 ≤ C := by
    have h := hC (0 : Plane × Plane)
    exact (norm_nonneg _).trans h
  have hcellFinite (z : Site) : volume (cell N z) < ⊤ := by
    by_cases hz : z ∈ evenLattice
    · exact volume_cell_lt_top hN hz
    · simp [cell_eq_empty_of_not_even hz]
  have hpairFinite (a b : Site) :
      (volume : Measure (Plane × Plane)) (cell N a ×ˢ cell N b) < ⊤ := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_lt_top (hcellFinite a) (hcellFinite b)
  have hAmeas (q : (Site × Site) × (Site × Site)) : MeasurableSet (A q) := by
    exact ((measurableSet_cell N q.1.1).prod (measurableSet_cell N q.1.2)).prod
      ((measurableSet_cell N q.2.1).prod (measurableSet_cell N q.2.2))
  have hAfin (q : (Site × Site) × (Site × Site)) :
      ((volume : Measure (Plane × Plane)).prod volume) (A q) < ⊤ := by
    change ((volume : Measure (Plane × Plane)).prod volume)
      ((cell N q.1.1 ×ˢ cell N q.1.2) ×ˢ (cell N q.2.1 ×ˢ cell N q.2.2)) < ⊤
    rw [Measure.prod_prod]
    exact ENNReal.mul_lt_top (hpairFinite q.1.1 q.1.2) (hpairFinite q.2.1 q.2.2)
  have hcellTestInt (q : (Site × Site) × (Site × Site)) : IntegrableOn
      (fun p : (Plane × Plane) × (Plane × Plane) => Φ (p.1.1, p.2.2) * G q)
      (A q) ((volume : Measure (Plane × Plane)).prod volume) := by
    have hconst : IntegrableOn (fun _ : (Plane × Plane) × (Plane × Plane) => C * |G q|)
        (A q) ((volume : Measure (Plane × Plane)).prod volume) :=
      integrableOn_const (hAfin q).ne
    apply hconst.mono'
    · exact ((Φ.continuous.comp (by fun_prop)).mul continuous_const).aestronglyMeasurable
    · filter_upwards [] with p
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hC (p.1.1, p.2.2)) (abs_nonneg _)
  have hrepr (p : (Plane × Plane) × (Plane × Plane)) :
      H p = ∑ q ∈ S, Set.indicator (A q) (fun _ => Φ (p.1.1, p.2.2) * G q) p := by
    let q₀ : (Site × Site) × (Site × Site) :=
      ((latticePoint N p.1.1, latticePoint N p.1.2),
        (latticePoint N p.2.1, latticePoint N p.2.2))
    change Φ (p.1.1, p.2.2) * G q₀ = _
    rw [Finset.sum_eq_single q₀]
    · by_cases hq₀ : q₀ ∈ S
      · have hp₀ : p ∈ A q₀ := by
          exact ⟨⟨mem_cell_latticePoint N p.1.1, mem_cell_latticePoint N p.1.2⟩,
            ⟨mem_cell_latticePoint N p.2.1, mem_cell_latticePoint N p.2.2⟩⟩
        simp [A, hp₀]
      · have hG₀ : G q₀ = 0 := by
          by_contra hne
          exact hq₀ (hG.mem_toFinset.mpr hne)
        simp [hG₀]
    · intro q hq hqne
      have hnot : p ∉ A q := by
        intro hp
        have hq₀ : q₀ = q := by
          apply Prod.ext
          · apply Prod.ext
            · exact (mem_cell_iff N q.1.1 p.1.1).mp hp.1.1
            · exact (mem_cell_iff N q.1.2 p.1.2).mp hp.1.2
          · apply Prod.ext
            · exact (mem_cell_iff N q.2.1 p.2.1).mp hp.2.1
            · exact (mem_cell_iff N q.2.2 p.2.2).mp hp.2.2
        exact hqne hq₀.symm
      simp [Set.indicator, hnot]
    · intro hq₀
      have hG₀ : G q₀ = 0 := by
        by_contra hne
        exact hq₀ (hG.mem_toFinset.mpr hne)
      simp [hG₀]
  have hHint : Integrable H := by
    rw [show H = fun p => ∑ q ∈ S,
        Set.indicator (A q) (fun _ => Φ (p.1.1, p.2.2) * G q) p by
      funext p
      exact hrepr p]
    apply integrable_finsetSum
    intro q hq
    exact (integrable_indicator_iff (hAmeas q)).2 (hcellTestInt q)
  have hcover : (⋃ q : (Site × Site) × (Site × Site), A q) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro p
    exact Set.mem_iUnion.mpr ⟨
      ((latticePoint N p.1.1, latticePoint N p.1.2),
        (latticePoint N p.2.1, latticePoint N p.2.2)),
      ⟨⟨mem_cell_latticePoint N p.1.1, mem_cell_latticePoint N p.1.2⟩,
        ⟨mem_cell_latticePoint N p.2.1, mem_cell_latticePoint N p.2.2⟩⟩⟩
  have hdisj : Pairwise (fun q r : (Site × Site) × (Site × Site) =>
      Disjoint (A q) (A r)) := by
    have hpairDisj {v w : Site × Site} (hvw : v ≠ w) :
        Disjoint (cell N v.1 ×ˢ cell N v.2) (cell N w.1 ×ˢ cell N w.2) := by
      apply Set.disjoint_left.mpr
      intro p hp hp'
      rcases Set.mem_prod.mp hp with ⟨hp₁, hp₂⟩
      rcases Set.mem_prod.mp hp' with ⟨hp₁', hp₂'⟩
      by_cases heq : v.1 = w.1
      · have hne : v.2 ≠ w.2 := by
          intro h
          exact hvw (Prod.ext heq h)
        exact (Set.disjoint_left.mp (pairwise_disjoint_cell N hne)) hp₂ hp₂'
      · exact (Set.disjoint_left.mp (pairwise_disjoint_cell N heq)) hp₁ hp₁'
    intro q r hqr
    apply Set.disjoint_left.mpr
    intro p hpq hpr
    rcases Set.mem_prod.mp hpq with ⟨hp₁, hp₂⟩
    rcases Set.mem_prod.mp hpr with ⟨hr₁, hr₂⟩
    by_cases hfirst : q.1 = r.1
    · have hsecond : q.2 ≠ r.2 := by
        intro heq
        exact hqr (Prod.ext hfirst heq)
      exact Set.disjoint_left.mp (hpairDisj hsecond) hp₂ hr₂
    · exact Set.disjoint_left.mp (hpairDisj hfirst) hp₁ hr₁
  have hsum := integral_iUnion hAmeas hdisj hHint.integrableOn
  rw [hcover, setIntegral_univ] at hsum
  have hcell (q : (Site × Site) × (Site × Site)) :
      ∫ p in A q, H p =
        (∫ x in cell N q.1.1 ×ˢ cell N q.2.2, Φ x) * G q *
          ((volume (cell N q.1.2)).toReal * (volume (cell N q.2.1)).toReal) := by
    calc
      ∫ p in A q, H p =
          ∫ p in A q, (Φ (p.1.1, p.2.2) * G q) := by
            apply setIntegral_congr_fun (hAmeas q)
            intro p hp
            simp only [H, A, Set.mem_prod] at hp ⊢
            rw [(mem_cell_iff N q.1.1 p.1.1).mp hp.1.1,
              (mem_cell_iff N q.1.2 p.1.2).mp hp.1.2,
              (mem_cell_iff N q.2.1 p.2.1).mp hp.2.1,
              (mem_cell_iff N q.2.2 p.2.2).mp hp.2.2]
      _ = (∫ p in A q, Φ (p.1.1, p.2.2)) * G q := by rw [integral_mul_const]
      _ = (∫ p in (cell N q.1.1 ×ˢ cell N q.1.2) ×ˢ
            (cell N q.2.1 ×ˢ cell N q.2.2),
            Φ (p.1.1, p.2.2)
            ∂((volume : Measure (Plane × Plane)).prod volume)) * G q := by
        dsimp only [A]
        rw [← Measure.volume_eq_prod]
      _ = _ := by
        rw [integral_fourCellTest N hN q Φ]
        ring
  calc
    _ = ∑' q : (Site × Site) × (Site × Site), ∫ p in A q, H p := hsum
    _ = ∑ q ∈ S,
        (∫ x in cell N q.1.1 ×ˢ cell N q.2.2, Φ x) * G q *
          ((volume (cell N q.1.2)).toReal * (volume (cell N q.2.1)).toReal) := by
      rw [tsum_eq_sum (s := S) (fun q hq => by
        have hzero : G q = 0 := by
          by_contra hne
          exact hq (hG.mem_toFinset.mpr hne)
        rw [hcell, hzero]
        simp)]
      apply Finset.sum_congr rfl
      intro q hq
      exact hcell q
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q hq
      rfl

/-- Only finitely many lattice cell pairs have a nonzero integral against a compactly supported
test. -/
theorem finite_support_cellPairTest (N : ℕ) (Φ : C_c(Plane × Plane, ℝ)) :
    {q : Site × Site | ∫ p in cell N q.1 ×ˢ cell N q.2, Φ p ≠ 0}.Finite := by
  classical
  let K : Set (Plane × Plane) := tsupport Φ
  have hK : IsCompact K := Φ.hasCompactSupport
  let K₁ : Set Plane := Prod.fst '' K
  let K₂ : Set Plane := Prod.snd '' K
  have hK₁ : IsCompact K₁ := hK.image continuous_fst
  have hK₂ : IsCompact K₂ := hK.image continuous_snd
  let S₁ : Set Site := latticePoint N '' K₁
  let S₂ : Set Site := latticePoint N '' K₂
  have hS₁ : S₁.Finite := finite_latticePoint_image_of_bounded hK₁.isBounded
  have hS₂ : S₂.Finite := finite_latticePoint_image_of_bounded hK₂.isBounded
  have hsub : {q : Site × Site |
      ∫ p in cell N q.1 ×ˢ cell N q.2, Φ p ≠ 0} ⊆ S₁ ×ˢ S₂ := by
    intro q hq
    by_contra hnot
    have hfirst : q.1 ∉ S₁ ∨ q.2 ∉ S₂ := by
      exact not_and_or.mp hnot
    have hzero (p : Plane × Plane) (hp : p ∈ cell N q.1 ×ˢ cell N q.2) : Φ p = 0 := by
      rcases Set.mem_prod.mp hp with ⟨hp₁, hp₂⟩
      simp only [mem_cell_iff] at hp₁ hp₂
      by_contra hΦ
      have hpK : p ∈ K := by
        exact subset_closure (Function.mem_support.mpr hΦ)
      rcases hfirst with hfirst | hsecond
      · apply hfirst
        exact ⟨p.1, ⟨p, hpK, rfl⟩, hp₁⟩
      · apply hsecond
        exact ⟨p.2, ⟨p, hpK, rfl⟩, hp₂⟩
    have hcellzero : ∫ p in cell N q.1 ×ˢ cell N q.2, Φ p = 0 := by
      calc
        _ = ∫ p in cell N q.1 ×ˢ cell N q.2, (0 : Plane × Plane → ℝ) p := by
          apply setIntegral_congr_fun
            ((measurableSet_cell N q.1).prod (measurableSet_cell N q.2))
          exact hzero
        _ = 0 := by simp
    exact hq hcellzero
  exact (hS₁.prod hS₂).subset hsub

/-- A finite-scale polymer pairing is the lattice endpoint sum weighted by the Lebesgue
integrals of the test over the corresponding cell pairs. -/
theorem integral_polymerMeasure_cellTsum (ϑ : ℝ) (N : ℕ) (s t : ℝ) (ω : Disorder)
    (Φ : C_c(Plane × Plane, ℝ)) :
    ∫ p, Φ p ∂(polymerMeasure ϑ N s t ω) =
      ∑' q : Site × Site,
        (∫ p in cell N q.1 ×ˢ cell N q.2, Φ p) *
          ((N : ℝ) / 4 * pointToPoint (criticalBeta ϑ N)
            (evenCeil ((N : ℝ) * s))
            (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s))
            q.1 q.2 ω) := by
  rw [integral_polymerMeasure]
  change (∫ p : Plane × Plane,
      Φ p * ((N : ℝ) / 4 * pointToPoint (criticalBeta ϑ N)
        (evenCeil ((N : ℝ) * s))
        (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s))
        (latticePoint N p.1) (latticePoint N p.2) ω)) = _
  calc
    _ = (N : ℝ) / 4 * ∫ p : Plane × Plane,
        Φ p * pointToPoint (criticalBeta ϑ N)
          (evenCeil ((N : ℝ) * s))
          (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s))
          (latticePoint N p.1) (latticePoint N p.2) ω := by
      rw [show (fun p : Plane × Plane => Φ p * ((N : ℝ) / 4 *
          pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s))
            (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s))
            (latticePoint N p.1) (latticePoint N p.2) ω)) =
          fun p => (N : ℝ) / 4 * (Φ p * pointToPoint (criticalBeta ϑ N)
            (evenCeil ((N : ℝ) * s))
            (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s))
            (latticePoint N p.1) (latticePoint N p.2) ω) by
        funext p
        ring]
      rw [integral_const_mul]
    _ = (N : ℝ) / 4 * ∑' q : Site × Site,
        (∫ p in cell N q.1 ×ˢ cell N q.2, Φ p) *
          pointToPoint (criticalBeta ϑ N)
            (evenCeil ((N : ℝ) * s))
            (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s))
            q.1 q.2 ω := by
      congr 1
      exact integral_latticePairing_eq_cellTsum N Φ
        (fun x y => pointToPoint (criticalBeta ϑ N)
          (evenCeil ((N : ℝ) * s))
          (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) x y ω)
    _ = ∑' q : Site × Site,
        (N : ℝ) / 4 * ((∫ p in cell N q.1 ×ˢ cell N q.2, Φ p) *
          pointToPoint (criticalBeta ϑ N)
            (evenCeil ((N : ℝ) * s))
            (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s))
            q.1 q.2 ω) := by
      rw [← tsum_mul_left]
    _ = _ := by
      apply tsum_congr
      intro q
      ring

/-- Compact polymer pairings are square-integrable at every finite scale. The finite cell
expansion reduces this to the finite-path moment bound. -/
theorem memLp_polymerPairing_two (ϑ : ℝ) (N : ℕ) (s t : ℝ)
    (Φ : C_c(Plane × Plane, ℝ)) :
    MemLp (fun ω => ∫ p, Φ p ∂(polymerMeasure ϑ N s t ω)) 2 disorderLaw := by
  classical
  let S : Finset (Site × Site) := (finite_support_cellPairTest N Φ).toFinset
  let cellTest : Site × Site → ℝ := fun q => ∫ p in cell N q.1 ×ˢ cell N q.2, Φ p
  have hcellzero {q : Site × Site} (hq : q ∉ S) : cellTest q = 0 := by
    dsimp [cellTest, S] at *
    by_contra hne
    exact hq ((finite_support_cellPairTest N Φ).mem_toFinset.mpr hne)
  have hsum (ω : Disorder) :
      (∫ p, Φ p ∂(polymerMeasure ϑ N s t ω)) =
        ∑ q ∈ S, cellTest q * ((N : ℝ) / 4 *
          pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s))
            (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) q.1 q.2 ω) := by
    rw [integral_polymerMeasure_cellTsum]
    rw [tsum_eq_sum (s := S) (fun q hq => by
      have hz := hcellzero hq
      change (∫ p in cell N q.1 ×ˢ cell N q.2, Φ p) = 0 at hz
      rw [hz]
      simp)]
  have hterm (q : Site × Site) :
      MemLp (fun ω => cellTest q * ((N : ℝ) / 4 *
        pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s))
          (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) q.1 q.2 ω))
        2 disorderLaw := by
    have hp := Polymer.memLp_pointToPoint (criticalBeta ϑ N)
      (evenCeil ((N : ℝ) * s))
      (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) q.1 q.2
      (2 : ENNReal) (by norm_num)
    have hbase := hp.const_mul (cellTest q * ((N : ℝ) / 4))
    convert hbase using 1
    funext ω
    ring
  have hsumLp : MemLp (fun ω => ∑ q ∈ S, cellTest q * ((N : ℝ) / 4 *
      pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s))
        (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) q.1 q.2 ω))
      2 disorderLaw := by
    apply memLp_finsetSum
    intro q hq
    exact hterm q
  convert hsumLp using 1
  funext ω
  exact hsum ω

/-- A compact polymer pairing is measurable because its cell expansion is a finite sum of
measurable point-to-point partition functions. -/
theorem measurable_polymerPairing (ϑ : ℝ) (N : ℕ) (s t : ℝ)
    (Φ : C_c(Plane × Plane, ℝ)) :
    Measurable (fun ω => ∫ p, Φ p ∂(polymerMeasure ϑ N s t ω)) := by
  classical
  let S : Finset (Site × Site) := (finite_support_cellPairTest N Φ).toFinset
  let cellTest : Site × Site → ℝ := fun q =>
    ∫ p in cell N q.1 ×ˢ cell N q.2, Φ p
  have hcellzero {q : Site × Site} (hq : q ∉ S) : cellTest q = 0 := by
    dsimp [cellTest, S] at *
    by_contra hne
    exact hq ((finite_support_cellPairTest N Φ).mem_toFinset.mpr hne)
  have hsum (ω : Disorder) :
      (∫ p, Φ p ∂(polymerMeasure ϑ N s t ω)) =
        ∑ q ∈ S, cellTest q * ((N : ℝ) / 4 *
          pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s))
            (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) q.1 q.2 ω) := by
    rw [integral_polymerMeasure_cellTsum]
    rw [tsum_eq_sum (s := S) (fun q hq => by
      have hz := hcellzero hq
      change (∫ p in cell N q.1 ×ˢ cell N q.2, Φ p) = 0 at hz
      rw [hz]
      simp)]
  rw [show (fun ω => ∫ p, Φ p ∂(polymerMeasure ϑ N s t ω)) =
      fun ω => ∑ q ∈ S, cellTest q * ((N : ℝ) / 4 *
        pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s))
          (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) q.1 q.2 ω) by
    funext ω
    exact hsum ω]
  apply S.measurable_fun_sum
  intro q hq
  exact measurable_const.mul (measurable_const.mul
    (Polymer.measurable_pointToPoint (criticalBeta ϑ N)
    (evenCeil ((N : ℝ) * s))
    (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) q.1 q.2))

/-- Averaging a polymer pairing after resampling a middle slab gives its finite lattice
Chapman--Kolmogorov cell expansion. -/
theorem integral_polymerPairing_resample_slab_cellSum (ϑ : ℝ) (N : ℕ)
    {s t t' u : ℝ} (hst : s ≤ t) (htt' : t ≤ t') (ht'u : t' ≤ u)
    (Φ : C_c(Plane × Plane, ℝ)) (ω : Disorder) :
    ∫ η, (∫ p, Φ p ∂(polymerMeasure ϑ N s u
        (Gaussian.resample (Gaussian.timeBlock (evenCeil ((N : ℝ) * t))
          (evenCeil ((N : ℝ) * t'))) η ω))) ∂disorderLaw =
      (N : ℝ) / 4 * ∑ q ∈ (finite_support_cellPairTest N Φ).toFinset,
        (∫ p in cell N q.1 ×ˢ cell N q.2, Φ p) *
          ∑' w, ∑' z,
            pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s))
              (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) q.1 w ω *
            srwKernel (evenCeil ((N : ℝ) * t') - evenCeil ((N : ℝ) * t)) (z - w) *
            pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * t'))
              (evenCeil ((N : ℝ) * u) - evenCeil ((N : ℝ) * t')) z q.2 ω := by
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
  let S := (finite_support_cellPairTest N Φ).toFinset
  let cellTest : Site × Site → ℝ := fun q => ∫ p in cell N q.1 ×ˢ cell N q.2, Φ p
  let full : Site → Site → Disorder → ℝ := fun x z η =>
    pointToPoint (criticalBeta ϑ N) a (d - a) x z
      (Gaussian.resample (Gaussian.timeBlock b c) η ω)
  have hcellzero {q : Site × Site} (hq : q ∉ S) : cellTest q = 0 := by
    dsimp [cellTest, S] at *
    by_contra hne
    exact hq ((finite_support_cellPairTest N Φ).mem_toFinset.mpr hne)
  have hpointwise (η : Disorder) :
      (∫ p, Φ p ∂(polymerMeasure ϑ N s u
        (Gaussian.resample (Gaussian.timeBlock b c) η ω))) =
        (N : ℝ) / 4 * ∑ q ∈ S, cellTest q * full q.1 q.2 η := by
    rw [integral_polymerMeasure_cellTsum]
    have htsum : (∑' q : Site × Site,
        cellTest q * ((N : ℝ) / 4 * full q.1 q.2 η)) =
        ∑ q ∈ S, cellTest q * ((N : ℝ) / 4 * full q.1 q.2 η) := by
      rw [tsum_eq_sum (s := S) (fun q hq => by rw [hcellzero hq]; simp)]
    rw [htsum]
    symm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    ring
  have htermInt (q : Site × Site) : Integrable (fun η => cellTest q * full q.1 q.2 η)
      disorderLaw := by
    dsimp [full, cellTest, a, b, c, d]
    exact (integrable_pointToPoint_resample_slab (criticalBeta ϑ N)
      (a := evenCeil ((N : ℝ) * s)) (b := evenCeil ((N : ℝ) * t))
      (c := evenCeil ((N : ℝ) * t')) (d := evenCeil ((N : ℝ) * u))
      hab hbc hcd q.1 q.2 ω).const_mul _
  have hfiniteInt : Integrable (fun η =>
      (N : ℝ) / 4 * ∑ q ∈ S, cellTest q * full q.1 q.2 η) disorderLaw := by
    apply (integrable_finsetSum _ (fun q hq => htermInt q)).const_mul _
  have hpairInt : Integrable (fun η =>
      ∫ p, Φ p ∂(polymerMeasure ϑ N s u
        (Gaussian.resample (Gaussian.timeBlock b c) η ω))) disorderLaw := by
    apply hfiniteInt.congr
    filter_upwards [] with η
    exact (hpointwise η).symm
  calc
    _ = ∫ η, (N : ℝ) / 4 * ∑ q ∈ S, cellTest q * full q.1 q.2 η ∂disorderLaw := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpointwise
    _ = (N : ℝ) / 4 * ∑ q ∈ S, cellTest q *
        (∫ η, full q.1 q.2 η ∂disorderLaw) := by
      rw [integral_const_mul, integral_finsetSum _ (fun q hq => htermInt q)]
      apply congrArg
      apply Finset.sum_congr rfl
      intro q hq
      rw [integral_const_mul]
    _ = _ := by
      apply congrArg
      apply Finset.sum_congr rfl
      intro q hq
      dsimp [full, a, b, c, d]
      rw [integral_pointToPoint_resample_slab
        (criticalBeta ϑ N) hab hbc hcd q.1 q.2 ω]

end Critical2DKPZ.SHF.Flow
