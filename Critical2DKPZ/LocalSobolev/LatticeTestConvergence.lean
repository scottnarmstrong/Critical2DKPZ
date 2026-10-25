/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.LocalSobolev.Inputs
public import Critical2DKPZ.LocalSobolev.RegularizedPairingMeasurability
public import Critical2DKPZ.JointConvergence.ThmToyJointLimit
import Critical2DKPZ.Analysis.Lattice.Volume
import Critical2DKPZ.JointConvergence.KPZRegularizedReversal
import Critical2DKPZ.JointConvergence.LogHeatFieldMeasurability
import Critical2DKPZ.SHF.Symmetries.DenseTransportHelpers
import Critical2DKPZ.Smoothing.Measurability
import Mathlib.Tactic

/-! The lattice KPZ test pairings converge jointly in distribution. -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open Critical2DKPZ.SHF.Limit
open scoped BoundedContinuousFunction ENNReal Topology

universe u

namespace Critical2DKPZ.LocalSobolev

private def latticePathStart {n : ℕ} (z : Site) (s : Fin n → Fin 4) : Site :=
  z - walkPosition 0 s n

private def latticePathSum (ϑ : ℝ) (N : ℕ) (t : ℝ) (h₀ : Plane →ᵇ ℝ)
    (ω : Disorder) (z : Site) : ℝ :=
  ∑ s : Fin (evenCeil ((N : ℝ) * t)) → Fin 4,
    (4 : ℝ)⁻¹ ^ evenCeil ((N : ℝ) * t) *
      Polymer.pathWeight (criticalBeta ϑ N) 0
        (latticePathStart z s) s ω *
      cellAverage N (fun y => Real.exp (h₀ y)) (latticePathStart z s)

private theorem integral_kpzLattice_numerator_eq_pathSum (ϑ : ℝ) {N : ℕ}
    (hN : 0 < N) (t : ℝ) (h₀ : Plane →ᵇ ℝ) (x : Plane) (ω : Disorder) :
    (∫ y, Real.exp (h₀ y) * rescaledP2P ϑ N 0 t (y, x) ω) =
      latticePathSum ϑ N t h₀ ω (latticePoint N x) := by
  classical
  let n : ℕ := evenCeil ((N : ℝ) * t)
  let β : ℝ := criticalBeta ϑ N
  let z : Site := latticePoint N x
  let start : (Fin n → Fin 4) → Site := fun s => z - walkPosition 0 s n
  have hstartEven (s : Fin n → Fin 4) : start s ∈ evenLattice := by
    have hz : z ∈ evenLattice := by dsimp [z]; exact latticePoint_mem_evenLattice N x
    have hn : Even n := by
      refine ⟨⌈((N : ℝ) * t) / 2⌉₊, ?_⟩
      simp [n, evenCeil, two_mul]
    have hnZ : Even (n : ℤ) := by exact_mod_cast hn
    have hnmod : (n : ℤ) ≡ 0 [ZMOD 2] := by
      change (n : ℤ) % 2 = 0
      exact Int.even_iff.mp hnZ
    have hwalkmod :
        (walkPosition 0 s n 0 + walkPosition 0 s n 1) ≡ 0 [ZMOD 2] :=
      (Polymer.walkPosition_parity 0 s).trans (by
        simpa only [Pi.zero_apply, zero_add] using hnmod)
    simp only [evenLattice, Set.mem_ofPred_eq] at hz ⊢
    have hzmod : (z 0 + z 1) ≡ 0 [ZMOD 2] := by
      change (z 0 + z 1) % 2 = 0
      exact Int.even_iff.mp hz
    have hcoords : start s 0 + start s 1 =
        (z 0 + z 1) - (walkPosition 0 s n 0 + walkPosition 0 s n 1) := by
      simp only [start, Pi.sub_apply]
      ring
    have hsmod : start s 0 + start s 1 ≡ 0 [ZMOD 2] := by
      rw [hcoords]
      simpa using hzmod.sub hwalkmod
    apply Int.even_iff.mpr
    change (start s 0 + start s 1) % 2 = 0
    exact hsmod
  have hcond (s : Fin n → Fin 4) (y : Plane) :
      walkPosition (latticePoint N y) s n = z ↔ y ∈ cell N (start s) := by
    rw [Polymer.walkPosition_eq_start_add, mem_cell_iff]
    dsimp [start]
    constructor
    · intro h
      apply eq_sub_iff_add_eq.mpr
      exact h
    · intro h
      exact eq_sub_iff_add_eq.mp h
  have hfun (y : Plane) :
      Real.exp (h₀ y) * rescaledP2P ϑ N 0 t (y, x) ω =
        ∑ s : Fin n → Fin 4,
          (cell N (start s)).indicator
            (fun y => ((N : ℝ) / 4) * (4 : ℝ)⁻¹ ^ n *
              Polymer.pathWeight β 0 (start s) s ω * Real.exp (h₀ y)) y := by
    have hzero : evenCeil ((N : ℝ) * 0) = 0 := by simp [evenCeil]
    simp only [rescaledP2P, hzero, Nat.sub_zero, β, n]
    rw [Polymer.pointToPoint_eq_sum]
    simp_rw [mul_assoc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    by_cases he : walkPosition (latticePoint N y) s n = z
    · have hy : y ∈ cell N (start s) := (hcond s y).mp he
      have hyz : latticePoint N y = start s := (mem_cell_iff N (start s) y).mp hy
      have hends : walkPosition (start s) s n = z := by
        rw [Polymer.walkPosition_eq_start_add]
        dsimp [start]
        simp
      simp only [Set.indicator, hy, ite_true]
      rw [hyz]
      rw [hends]
      simp [z]
      ring_nf
    · have hy : y ∉ cell N (start s) := fun h => he ((hcond s y).mpr h)
      simp [Set.indicator, he, hy, z, n]
  have hbound (s : Fin n → Fin 4) (y : Plane) :
      ‖((N : ℝ) / 4) * (4 : ℝ)⁻¹ ^ n *
        Polymer.pathWeight β 0 (start s) s ω * Real.exp (h₀ y)‖ ≤
        |((N : ℝ) / 4) * (4 : ℝ)⁻¹ ^ n *
          Polymer.pathWeight β 0 (start s) s ω| * Real.exp ‖h₀‖ := by
    calc
      ‖((N : ℝ) / 4) * (4 : ℝ)⁻¹ ^ n *
          Polymer.pathWeight β 0 (start s) s ω * Real.exp (h₀ y)‖ =
        |((N : ℝ) / 4) * (4 : ℝ)⁻¹ ^ n *
          Polymer.pathWeight β 0 (start s) s ω| * Real.exp (h₀ y) := by
            calc
              ‖((N : ℝ) / 4) * (4 : ℝ)⁻¹ ^ n *
                  Polymer.pathWeight β 0 (start s) s ω * Real.exp (h₀ y)‖ =
                |((N : ℝ) / 4) * (4 : ℝ)⁻¹ ^ n *
                  Polymer.pathWeight β 0 (start s) s ω * Real.exp (h₀ y)| :=
                    Real.norm_eq_abs _
              _ = |((N : ℝ) / 4) * (4 : ℝ)⁻¹ ^ n *
                  Polymer.pathWeight β 0 (start s) s ω| * Real.exp (h₀ y) := by
                    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      _ ≤ |((N : ℝ) / 4) * (4 : ℝ)⁻¹ ^ n *
          Polymer.pathWeight β 0 (start s) s ω| * Real.exp ‖h₀‖ := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            apply Real.exp_le_exp.mpr
            calc
              h₀ y ≤ |h₀ y| := le_abs_self _
              _ = ‖h₀ y‖ := (Real.norm_eq_abs _).symm
              _ ≤ ‖h₀‖ := h₀.norm_coe_le_norm y
  have htermInt (s : Fin n → Fin 4) : Integrable
      (fun y : Plane => (cell N (start s)).indicator
        (fun y => ((N : ℝ) / 4) * (4 : ℝ)⁻¹ ^ n *
          Polymer.pathWeight β 0 (start s) s ω * Real.exp (h₀ y)) y) volume := by
    refine (integrable_indicator_iff (measurableSet_cell N (start s))).2 ?_
    have hm : Measurable (fun y : Plane =>
        ((N : ℝ) / 4) * (4 : ℝ)⁻¹ ^ n *
          Polymer.pathWeight β 0 (start s) s ω * Real.exp (h₀ y)) := by
      exact measurable_const.mul
        (Real.continuous_exp.measurable.comp h₀.continuous.measurable)
    apply volume.integrableOn_of_bounded
      (M := |((N : ℝ) / 4) * (4 : ℝ)⁻¹ ^ n *
        Polymer.pathWeight β 0 (start s) s ω| * Real.exp ‖h₀‖)
      (volume_cell_lt_top hN (hstartEven s)).ne
      hm.aestronglyMeasurable
    filter_upwards [] with y
    exact hbound s y
  have hintegrable : Integrable
      (fun y : Plane => ∑ s : Fin n → Fin 4,
        (cell N (start s)).indicator
          (fun y => ((N : ℝ) / 4) * (4 : ℝ)⁻¹ ^ n *
            Polymer.pathWeight β 0 (start s) s ω * Real.exp (h₀ y)) y) volume :=
    integrable_finsetSum _ (fun s _ => htermInt s)
  rw [show (fun y : Plane => Real.exp (h₀ y) * rescaledP2P ϑ N 0 t (y, x) ω) =
      fun y => ∑ s : Fin n → Fin 4,
        (cell N (start s)).indicator
          (fun y => ((N : ℝ) / 4) * (4 : ℝ)⁻¹ ^ n *
            Polymer.pathWeight β 0 (start s) s ω * Real.exp (h₀ y)) y from funext hfun]
  rw [integral_finsetSum _ (fun s _ => htermInt s)]
  dsimp [latticePathSum, n, β, z, start, latticePathStart]
  apply Finset.sum_congr rfl
  intro s hs
  rw [integral_indicator (measurableSet_cell N (start s)), integral_const_mul]
  have hv := volume_cell_toReal hN (hstartEven s)
  rw [cellAverage, hv]
  have hcell : (∫ y in cell N (start s), Real.exp (h₀ y)) =
      cellAverage N (fun y => Real.exp (h₀ y)) (start s) * (4 / (N : ℝ)) := by
    dsimp [cellAverage]
    rw [hv]
    field_simp
  rw [hcell]
  have hNne : (N : ℝ) ≠ 0 := by positivity
  field_simp

private theorem measurable_latticePathSum_param (ϑ : ℝ) (N : ℕ) (t : ℝ)
    (h₀ : Plane →ᵇ ℝ) :
    Measurable (fun q : Disorder × Site => latticePathSum ϑ N t h₀ q.1 q.2) := by
  classical
  let n : ℕ := evenCeil ((N : ℝ) * t)
  let β : ℝ := criticalBeta ϑ N
  let f : Site → ℝ := cellAverage N fun y => Real.exp (h₀ y)
  have hterm (s : Fin n → Fin 4) :
      Measurable (fun q : Disorder × Site =>
        (4 : ℝ)⁻¹ ^ n * Polymer.pathWeight β 0
          (q.2 - walkPosition 0 s n) s q.1 * f (q.2 - walkPosition 0 s n)) := by
    let d : Site := walkPosition 0 s n
    have hEq (q : Disorder × Site) :
        (4 : ℝ)⁻¹ ^ n * Polymer.pathWeight β 0 (q.2 - d) s q.1 * f (q.2 - d) =
          ∑' w : Site, if q.2 - d = w then
            (4 : ℝ)⁻¹ ^ n * Polymer.pathWeight β 0 w s q.1 * f w else 0 := by
      symm
      rw [tsum_eq_single (q.2 - d)]
      · simp
      · intro w hw
        simp [hw.symm]
    have hsum : Measurable (fun q : Disorder × Site =>
        ∑' w : Site, if q.2 - d = w then
          (4 : ℝ)⁻¹ ^ n * Polymer.pathWeight β 0 w s q.1 * f w else 0) := by
      apply Measurable.tsum
      intro w
      have hset : MeasurableSet {q : Disorder × Site | q.2 - d = w} :=
        measurableSet_eq_fun (measurable_snd.sub_const d) measurable_const
      have hval : Measurable (fun q : Disorder × Site =>
          (4 : ℝ)⁻¹ ^ n * Polymer.pathWeight β 0 w s q.1 * f w) := by
        exact (measurable_const.mul
          ((Polymer.measurable_pathWeight β 0 w s).comp measurable_fst)).mul_const (f w)
      exact Measurable.ite hset hval measurable_const
    have hEqFun : (fun q : Disorder × Site =>
        (4 : ℝ)⁻¹ ^ n * Polymer.pathWeight β 0 (q.2 - d) s q.1 * f (q.2 - d)) =
          fun q => ∑' w : Site, if q.2 - d = w then
            (4 : ℝ)⁻¹ ^ n * Polymer.pathWeight β 0 w s q.1 * f w else 0 :=
      funext hEq
    rw [hEqFun]
    simpa [d] using hsum
  change Measurable (fun q : Disorder × Site =>
    ∑ s : Fin n → Fin 4,
      (4 : ℝ)⁻¹ ^ n * Polymer.pathWeight β 0
        (q.2 - walkPosition 0 s n) s q.1 * f (q.2 - walkPosition 0 s n))
  apply Finset.measurable_sum
  intro s hs
  exact hterm s

private theorem measurable_kpzLattice_param (ϑ : ℝ) (N : ℕ) (t : ℝ)
    (h₀ : Plane →ᵇ ℝ) :
    Measurable (fun q : Disorder × Plane => kpzLattice ϑ N t h₀ q.2 q.1) := by
  by_cases hN : N = 0
  · subst N
    have heq : (fun q : Disorder × Plane => kpzLattice ϑ 0 t h₀ q.2 q.1) =
        fun _ => Real.log 0 - kpzLatticeCentring ϑ 0 t := by
      funext q
      simp [kpzLattice, rescaledP2P]
    rw [heq]
    exact measurable_const
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    have hsites : Measurable (fun q : Disorder × Plane =>
        (q.1, latticePoint N q.2)) :=
      measurable_fst.prodMk ((measurable_latticePoint N).comp measurable_snd)
    have hpaths := measurable_latticePathSum_param ϑ N t h₀
    have hraw : Measurable (fun q : Disorder × Plane =>
        Real.log (latticePathSum ϑ N t h₀ q.1 (latticePoint N q.2)) -
          kpzLatticeCentring ϑ N t) := by
      exact (Real.measurable_log.comp (hpaths.comp hsites)).sub_const _
    have heq : (fun q : Disorder × Plane => kpzLattice ϑ N t h₀ q.2 q.1) =
        fun q => Real.log (latticePathSum ϑ N t h₀ q.1 (latticePoint N q.2)) -
          kpzLatticeCentring ϑ N t := by
      funext q
      simp only [kpzLattice]
      rw [integral_kpzLattice_numerator_eq_pathSum ϑ hNpos t h₀ q.2 q.1]
    rw [heq]
    exact hraw

private theorem aemeasurable_integral_kpzLattice (ϑ : ℝ) (N : ℕ) (t : ℝ)
    (h₀ : Plane →ᵇ ℝ) (φ : TestFn) :
    AEMeasurable (fun ω => ∫ x, φ x * kpzLattice ϑ N t h₀ x ω)
      disorderLaw := by
  have hφ : Measurable (φ : Plane → ℝ) := φ.continuous.measurable
  have hmeas : Measurable (fun q : Disorder × Plane =>
      φ q.2 * kpzLattice ϑ N t h₀ q.2 q.1) :=
    (hφ.comp measurable_snd).mul (measurable_kpzLattice_param ϑ N t h₀)
  exact hmeas.stronglyMeasurable.integral_prod_right'.aemeasurable

/-- The forward lattice test pairings converge jointly in distribution to those of the critical KPZ process. -/
theorem kpzLattice_testFn_tendsto_of (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (_hsym : ShfSymmetriesAt ϑ P Z) (hC12 : ToyJointAt ϑ P Z)
    (hrevN : LatticeReverseLawClose ϑ)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (k : ℕ) (t : Fin k → ℝ) (h₀ : Fin k → (Plane →ᵇ ℝ))
    (φ : Fin k → TestFn) (ht : ∀ i, 0 < t i) :
    TendstoInDistribution
      (fun (N : ℕ) (ω : Disorder) (i : Fin k) =>
        ∫ x, φ i x * kpzLattice ϑ N (t i) (h₀ i) x ω)
      atTop (fun ω i => H (t i) (h₀ i) ω (φ i)) (fun _ => disorderLaw) P := by
  let T : ℝ := 1 + ∑ i : Fin k, |t i|
  have hT : 0 < T := by
    dsimp [T]
    have hs : 0 ≤ ∑ i : Fin k, |t i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith
  let u : Fin k → ℝ := fun i => T - t i
  have huC12 (i : Fin k) : 0 ≤ u i ∧ u i < T := by
    have hsum : |t i| ≤ ∑ j : Fin k, |t j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (t j)) (Finset.mem_univ i)
    constructor
    · dsimp [u, T]
      linarith [le_abs_self (t i)]
    · dsimp [u]
      linarith [ht i]
  have huRev (i : Fin k) : 0 < u i ∧ u i ≤ T := by
    have hsum : |t i| ≤ ∑ j : Fin k, |t j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (t j)) (Finset.mem_univ i)
    constructor
    · dsimp [u, T]
      linarith [le_abs_self (t i)]
    · dsimp [u]
      linarith [ht i]
  have htRev (i : Fin k) : 0 < t i ∧ t i ≤ T := by
    constructor
    · exact ht i
    · dsimp [T]
      have hsum : |t i| ≤ ∑ j : Fin k, |t j| :=
        Finset.single_le_sum (fun j _ => abs_nonneg (t j)) (Finset.mem_univ i)
      linarith [le_abs_self (t i)]
  obtain ⟨X, hXm, hRate, hLp, hRev, hLaw⟩ := hC12 T hT
  let Xlim : Ω → Fin k → ℝ := fun ω i => X (u i) (h₀ i) (φ i) ω
  let Y : Ω → Fin k → ℝ := fun ω i => H (t i) (h₀ i) ω (φ i)
  have hRev' := hRev k u h₀ φ huC12
  have hLaw' := hLaw H hH k u h₀ φ huC12
  have hXY : (fun ω i => H (T - u i) (h₀ i) ω (φ i)) = Y := by
    funext ω i
    simp [Y, u]
  have hLawXY : P.map Xlim = P.map Y := by
    change P.map (fun ω i => X (u i) (h₀ i) (φ i) ω) = P.map Y
    rw [← hXY]
    exact hLaw'
  have hYmeas : AEMeasurable Y P := by
    apply AEMeasurable.of_eval
    intro i
    let δseq : ℕ → ℝ := fun n => t i / ((n : ℝ) + 2)
    have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    have hδnhds : Tendsto δseq atTop (𝓝 0) := by
      have hconst : Tendsto (fun _ : ℕ => t i) atTop (𝓝 (t i)) := tendsto_const_nhds
      have h := hconst.div_atTop hden
      simpa [δseq] using h
    have hδpos (n : ℕ) : 0 < δseq n := by
      dsimp [δseq]
      exact div_pos (ht i) (by positivity)
    have hδlt (n : ℕ) : δseq n < t i := by
      dsimp [δseq]
      have hn : (1 : ℝ) < (n : ℝ) + 2 := by
        have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
        linarith
      exact div_lt_self (ht i) hn
    have hδtendsto : Tendsto δseq atTop (nhdsWithin 0 (Set.Ioi 0)) := by
      apply tendsto_nhdsWithin_iff.2
      exact ⟨hδnhds, Filter.Eventually.of_forall hδpos⟩
    have hconv := (hH (t i) (ht i) (h₀ i) (φ i)).comp hδtendsto
    have hmeas : ∀ n, AEMeasurable
        (fun ω => ∫ x, φ i x * kpzRegularized P Z (t i) (δseq n) (h₀ i) x ω) P := by
      intro n
      exact aemeasurable_integral_kpzRegularized_of ϑ P Z hZ
        (hδpos n) (hδlt n) (h₀ i) (φ i)
    have hlimit := TendstoInMeasure.aemeasurable hmeas hconv
    simpa [Y] using hlimit
  have hFmeas : ∀ N, AEMeasurable
      (fun ω i => ∫ x, φ i x * kpzLattice ϑ N (t i) (h₀ i) x ω) disorderLaw := by
    intro N
    apply AEMeasurable.of_eval
    intro i
    exact aemeasurable_integral_kpzLattice ϑ N (t i) (h₀ i) (φ i)
  let R : ℕ → Disorder → Fin k → ℝ := fun N ω i =>
    ∫ x, φ i x * kpzLatticeReversed ϑ N (u i) T (h₀ i) x ω
  let F : ℕ → Disorder → Fin k → ℝ := fun N ω i =>
    ∫ x, φ i x * kpzLattice ϑ N (t i) (h₀ i) x ω
  have hRevDist : TendstoInDistribution R atTop Xlim (fun _ => disorderLaw) P := by
    simpa [R, Xlim] using hRev'
  have hlimmeas := hRevDist.aemeasurable_limit
  have hconvBCF (g : (Fin k → ℝ) →ᵇ ℝ) :
      Tendsto (fun N => ∫ ω, g (F N ω) ∂disorderLaw)
        atTop (𝓝 (∫ ω, g (Y ω) ∂P)) := by
    have hdiff := hrevN T k t h₀ φ htRev g
    have hRconv :=
      (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
        hRevDist.forall_aemeasurable hlimmeas).1 hRevDist g
    have hmapIntegral : (∫ ω, g (Xlim ω) ∂P) = ∫ ω, g (Y ω) ∂P := by
      calc
        (∫ ω, g (Xlim ω) ∂P) = ∫ z, g z ∂P.map Xlim :=
          (integral_map hlimmeas (g.continuous.measurable.aestronglyMeasurable)).symm
        _ = ∫ z, g z ∂P.map Y := by rw [hLawXY]
        _ = ∫ ω, g (Y ω) ∂P :=
          integral_map hYmeas (g.continuous.measurable.aestronglyMeasurable)
    have hadd := hdiff.add hRconv
    have heq : (fun N => ∫ ω, g (F N ω) ∂disorderLaw) =
        fun N => (∫ ω, g (F N ω) ∂disorderLaw - ∫ ω, g (R N ω) ∂disorderLaw) +
          ∫ ω, g (R N ω) ∂disorderLaw := by
      funext N
      ring
    have hsumlim : Tendsto
        (fun N => (∫ ω, g (F N ω) ∂disorderLaw - ∫ ω, g (R N ω) ∂disorderLaw) +
          ∫ ω, g (R N ω) ∂disorderLaw)
        atTop (𝓝 (∫ ω, g (Y ω) ∂P)) := by
      simpa [F, R, u, hmapIntegral] using hadd
    exact Tendsto.congr' (Filter.Eventually.of_forall fun N => (congrFun heq N).symm) hsumlim
  refine (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ hFmeas hYmeas).2 ?_
  intro g
  exact hconvBCF g

end Critical2DKPZ.LocalSobolev

end
