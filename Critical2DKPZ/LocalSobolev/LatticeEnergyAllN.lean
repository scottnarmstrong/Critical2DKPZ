/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.LocalSobolev.LatticeMoment
public import Critical2DKPZ.Analysis.Sobolev.FunctionBound
public import Critical2DKPZ.Analysis.Sobolev.LocalizedMoment
import Critical2DKPZ.LocalSobolev.DistributionValuedLimits
import Critical2DKPZ.Gaussian.DisorderLaws
import Mathlib.Tactic

/-! # Fixed-index and all-index lattice local-energy bounds -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BoundedContinuousFunction ENNReal

namespace Critical2DKPZ.LocalSobolev

private theorem testFn_norm_data_fixed (χ : TestFn) :
    ∃ B : ℝ, 0 ≤ B ∧ (∀ x : Plane, ‖χ x‖ ≤ B) ∧
      Integrable (fun x : Plane => ‖χ x‖) volume := by
  have hK : IsCompact (tsupport χ) := χ.hasCompactSupport.isCompact
  have hImage : IsCompact ((fun x : Plane => ‖χ x‖) '' tsupport χ) :=
    hK.image χ.continuous.norm
  obtain ⟨M, hM⟩ := hImage.bddAbove
  refine ⟨max M 0, le_max_right _ _, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ tsupport χ
    · exact (hM ⟨x, hx, rfl⟩).trans (le_max_left _ _)
    · have hx0 : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hx0]
  · exact (χ.continuous.integrable_of_hasCompactSupport χ.hasCompactSupport).norm

private theorem integrable_rescaledP2P_flat_spatial_fixed (ϑ : ℝ) {N : ℕ}
    (hN : 0 < N) (t : ℝ) (x : Plane) (ω : Disorder) :
    Integrable (fun y : Plane => rescaledP2P ϑ N 0 t (y, x) ω) volume := by
  let n := evenCeil ((N : ℝ) * t)
  have hnEven : Even n := by simpa [n] using evenCeil_even ((N : ℝ) * t)
  have hcoeff : ∀ q : (Fin n → Fin 4) × (Fin n → Fin 4),
      0 ≤ flatMassPathCoeff q := by
    intro q
    dsimp [flatMassPathCoeff]
    split_ifs <;> positivity
  have hcoeffPos : ∃ q : (Fin n → Fin 4) × (Fin n → Fin 4),
      0 < flatMassPathCoeff q := by
    let s : Fin n → Fin 4 := fun _ => 0
    refine ⟨(s, s), ?_⟩
    simp [flatMassPathCoeff, s]
  have hmassPos := PolymerCalculus.finitePathMass_pos (criticalBeta ϑ N) 0 n
    (fun s => flatMassPathStart (latticePoint N x) s) hcoeff hcoeffPos ω
  have hmassEq := integral_rescaledP2P_flat_eq_finitePathMass ϑ hN t x ω hnEven
  by_contra hnot
  rw [integral_undef hnot] at hmassEq
  exact (ne_of_gt hmassPos) hmassEq.symm

private theorem kpzLattice_initialShift_bound_fixed (ϑ : ℝ) {N : ℕ}
    (hN : 0 < N) (t : ℝ) (h₀ : Plane →ᵇ ℝ) (x : Plane) (ω : Disorder) :
    |kpzLattice ϑ N t h₀ x ω - kpzLattice ϑ N t 0 x ω| ≤ ‖h₀‖ := by
  let f : Plane → ℝ := fun y => rescaledP2P ϑ N 0 t (y, x) ω
  let zh : ℝ := ∫ y : Plane, Real.exp (h₀ y) * f y
  let z0 : ℝ := ∫ y : Plane, f y
  have hfInt : Integrable f volume := integrable_rescaledP2P_flat_spatial_fixed ϑ hN t x ω
  have hfNonneg : ∀ y, 0 ≤ f y := by
    intro y
    dsimp [f]
    simpa [rescaledP2P] using
      mul_nonneg (by positivity : 0 ≤ (N / 4 : ℝ))
        (Polymer.pointToPoint_nonneg (criticalBeta ϑ N) 0
          (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * 0))
          (latticePoint N y) (latticePoint N x) ω)
  have hcoeff : ∀ q : (Fin (evenCeil ((N : ℝ) * t)) → Fin 4) ×
      (Fin (evenCeil ((N : ℝ) * t)) → Fin 4), 0 ≤ flatMassPathCoeff q := by
    intro q
    dsimp [flatMassPathCoeff]
    split_ifs <;> positivity
  have hcoeffPos : ∃ q : (Fin (evenCeil ((N : ℝ) * t)) → Fin 4) ×
      (Fin (evenCeil ((N : ℝ) * t)) → Fin 4),
      0 < flatMassPathCoeff q := by
    let s : Fin (evenCeil ((N : ℝ) * t)) → Fin 4 := fun _ => 0
    refine ⟨(s, s), ?_⟩
    simp [flatMassPathCoeff, s]
  have hz0Pos : 0 < z0 := by
    dsimp [z0, f]
    rw [integral_rescaledP2P_flat_eq_finitePathMass ϑ hN t x ω
      (evenCeil_even ((N : ℝ) * t))]
    exact PolymerCalculus.finitePathMass_pos (criticalBeta ϑ N) 0
      (evenCeil ((N : ℝ) * t))
      (fun s => flatMassPathStart (latticePoint N x) s) hcoeff hcoeffPos ω
  let c := ‖h₀‖
  have hexpUpper (y : Plane) : Real.exp (h₀ y) ≤ Real.exp c := by
    apply Real.exp_le_exp.mpr
    exact (abs_le.mp (h₀.norm_coe_le_norm y)).2
  have hexpLower (y : Plane) : Real.exp (-c) ≤ Real.exp (h₀ y) := by
    apply Real.exp_le_exp.mpr
    exact (abs_le.mp (h₀.norm_coe_le_norm y)).1
  let upper : Plane → ℝ := fun y => Real.exp c * f y
  let lower : Plane → ℝ := fun y => Real.exp (-c) * f y
  have hupperInt : Integrable upper volume := by
    dsimp [upper]
    exact hfInt.const_mul (Real.exp c)
  have hlowerInt : Integrable lower volume := by
    dsimp [lower]
    exact hfInt.const_mul (Real.exp (-c))
  have hweightedAES : AEStronglyMeasurable (fun y => Real.exp (h₀ y) * f y) volume :=
    (Real.continuous_exp.comp h₀.continuous).measurable.aestronglyMeasurable.mul
      hfInt.aestronglyMeasurable
  have hweightedInt : Integrable (fun y => Real.exp (h₀ y) * f y) volume := by
    refine hupperInt.mono' hweightedAES ?_
    filter_upwards [] with y
    have hnonneg := hfNonneg y
    simpa [upper, abs_of_nonneg hnonneg] using
      mul_le_mul_of_nonneg_right (hexpUpper y) hnonneg
  have hupper : zh ≤ ∫ y, upper y := by
    dsimp [zh, upper]
    exact integral_mono hweightedInt hupperInt (fun y =>
      mul_le_mul_of_nonneg_right (hexpUpper y) (hfNonneg y))
  have hlower : ∫ y, lower y ≤ zh := by
    dsimp [zh, lower]
    exact integral_mono hlowerInt hweightedInt (fun y =>
      mul_le_mul_of_nonneg_right (hexpLower y) (hfNonneg y))
  have hupper' : zh ≤ Real.exp c * z0 := by
    calc
      zh ≤ ∫ y, upper y := hupper
      _ = Real.exp c * z0 := by simp only [upper]; rw [integral_const_mul]
  have hlower' : Real.exp (-c) * z0 ≤ zh := by
    calc
      Real.exp (-c) * z0 = ∫ y, lower y := by simp only [lower]; rw [integral_const_mul]
      _ ≤ zh := hlower
  have hzhPos : 0 < zh := lt_of_lt_of_le (mul_pos (Real.exp_pos _) hz0Pos) hlower'
  have hlogLower := Real.log_le_log (mul_pos (Real.exp_pos _) hz0Pos) hlower'
  have hlogUpper := Real.log_le_log hzhPos hupper'
  have hlogLower' : -c + Real.log z0 ≤ Real.log zh := by
    rw [Real.log_mul (Real.exp_pos (-c)).ne' hz0Pos.ne', Real.log_exp] at hlogLower
    exact hlogLower
  have hlogUpper' : Real.log zh ≤ c + Real.log z0 := by
    rw [Real.log_mul (Real.exp_pos c).ne' hz0Pos.ne', Real.log_exp] at hlogUpper
    exact hlogUpper
  have hrepr : kpzLattice ϑ N t h₀ x ω - kpzLattice ϑ N t 0 x ω =
      Real.log zh - Real.log z0 := by simp [kpzLattice, zh, z0, f]
  rw [hrepr, abs_le]
  constructor <;> linarith [hlogLower', hlogUpper']

private theorem memLp_kpzLattice_flat_fixed (ϑ : ℝ) {N : ℕ} (hN : 0 < N)
    {t : ℝ} (hnt : 1 ≤ evenCeil ((N : ℝ) * t)) (x : Plane) :
    MemLp (fun ω => kpzLattice ϑ N t 0 x ω) 2 disorderLaw := by
  let m := evenCeil ((N : ℝ) * t)
  let z := latticePoint N x
  let β := criticalBeta ϑ N
  let rev := PolymerCalculus.reversedDisorder m
  let F : Disorder → ℝ := fun ω => Real.log (pointToPlane β 0 (m - 1) z (rev ω))
  let D : Disorder → ℝ := fun ω => β * ω (m, z)
  let c : ℝ := β ^ 2 / 2 + kpzLatticeCentring ϑ N t
  have hF : MemLp F 2 disorderLaw := by
    dsimp [F, rev, β, z, m]
    exact (memLp_log_pointToPlane _ _ _ _).comp_measurePreserving
      (PolymerCalculus.measurePreserving_reversedDisorder _)
  have hcoord := Gaussian.hasLaw_disorder_eval (m, z)
  have hcoordMem : MemLp (fun ω : Disorder => ω (m, z)) 2 disorderLaw :=
    hcoord.memLp (memLp_id_gaussianReal 2)
  have hD : MemLp D 2 disorderLaw := by
    dsimp [D]
    simpa only [mul_comm] using hcoordMem.const_mul β
  have hc : MemLp (fun _ : Disorder => c) 2 disorderLaw := memLp_const c
  have hrepr : (fun ω => kpzLattice ϑ N t 0 x ω) = fun ω => F ω + D ω - c := by
    funext ω
    dsimp [F, D, c, β, z, m, rev]
    rw [kpzLattice_flat_log_eq_timeReversedPlane ϑ hN t x ω (by simpa [m] using hnt)]
    ring
  rw [hrepr]
  exact (hF.add hD).sub hc

private theorem kpzLattice_flat_translate_fixed (ϑ : ℝ) {N : ℕ} (hN : 0 < N)
    {t : ℝ} (hnt : 1 ≤ evenCeil ((N : ℝ) * t)) (x : Plane) (ω : Disorder) :
    kpzLattice ϑ N t 0 x ω =
      kpzLattice ϑ N t 0 0 (fun p => ω (p.1, p.2 + latticePoint N x)) := by
  let m := evenCeil ((N : ℝ) * t)
  let z := latticePoint N x
  let β := criticalBeta ϑ N
  let τ : Disorder → Disorder := fun ω p => ω (p.1, p.2 + z)
  have hcomm (ω : Disorder) :
      PolymerCalculus.reversedDisorder m (τ ω) = τ (PolymerCalculus.reversedDisorder m ω) := by
    funext p
    rfl
  have hptp :
      pointToPlane β 0 (m - 1) z (PolymerCalculus.reversedDisorder m ω) =
        pointToPlane β 0 (m - 1) 0
          (PolymerCalculus.reversedDisorder m (τ ω)) := by
    rw [hcomm]
    simpa [z] using Polymer.pointToPlane_translate β 0 (m - 1) 0 z
      (PolymerCalculus.reversedDisorder m ω)
  have hcoord : (τ ω) (m, 0) = ω (m, z) := by simp [τ, z]
  have hsite0 : latticePoint N (0 : Plane) = 0 := by simp [latticePoint, nearestEven]
  rw [kpzLattice_flat_log_eq_timeReversedPlane ϑ hN t x ω (by simpa [m] using hnt),
    kpzLattice_flat_log_eq_timeReversedPlane ϑ hN t 0 (τ ω) (by simpa [m] using hnt)]
  rw [hptp, hsite0, ← hcoord]

private theorem integral_kpzLattice_flat_sq_eq_zeroSite_fixed (ϑ : ℝ) {N : ℕ}
    (hN : 0 < N) {t : ℝ} (hnt : 1 ≤ evenCeil ((N : ℝ) * t)) (x : Plane) :
    (∫ ω, kpzLattice ϑ N t 0 x ω ^ 2 ∂disorderLaw) =
      ∫ ω, kpzLattice ϑ N t 0 0 ω ^ 2 ∂disorderLaw := by
  let τ : Disorder → Disorder := fun ω p => ω (p.1, p.2 + latticePoint N x)
  let e := Gaussian.spatialTranslation (latticePoint N x)
  let eD : Disorder ≃ᵐ Disorder :=
    MeasurableEquiv.piCongrLeft (fun _ : ℕ × Site => ℝ) e.symm
  have hefun : Gaussian.reindexDisorder e = eD := by
    funext ω p
    change ω (e p) = eD ω p
    symm
    have h := MeasurableEquiv.piCongrLeft_apply_apply e.symm
      (β := fun _ : ℕ × Site => ℝ) ω (e p)
    simpa [eD] using h
  have hτeq : τ = eD := by
    funext ω p
    change ω (e p) = eD ω p
    symm
    have h := MeasurableEquiv.piCongrLeft_apply_apply e.symm
      (β := fun _ : ℕ × Site => ℝ) ω (e p)
    simpa [τ, eD, e, Gaussian.spatialTranslation] using h
  have hmp : MeasurePreserving eD disorderLaw disorderLaw := by
    rw [← hefun]
    exact Gaussian.measurePreserving_reindexDisorder e
  have htranslate (ω : Disorder) :
      kpzLattice ϑ N t 0 x ω = kpzLattice ϑ N t 0 0 (τ ω) := by
    exact kpzLattice_flat_translate_fixed ϑ hN hnt x ω
  calc
    _ = ∫ ω, kpzLattice ϑ N t 0 0 (τ ω) ^ 2 ∂disorderLaw := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => congrArg (fun y : ℝ => y ^ 2) (htranslate ω)
    _ = _ := by
      rw [hτeq]
      exact hmp.integral_comp' (fun ω : Disorder => kpzLattice ϑ N t 0 0 ω ^ 2)

private theorem kpzLattice_flat_uniform_secondMoment_fixed (ϑ : ℝ) {N : ℕ}
    (hN : 0 < N) {t : ℝ} (hnt : 1 ≤ evenCeil ((N : ℝ) * t)) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x : Plane,
      (∫⁻ ω, ENNReal.ofReal (kpzLattice ϑ N t 0 x ω ^ 2) ∂disorderLaw) ≤ C := by
  let C : ℝ≥0∞ := ENNReal.ofReal
    (∫ ω, kpzLattice ϑ N t 0 0 ω ^ 2 ∂disorderLaw)
  have hmem := memLp_kpzLattice_flat_fixed ϑ hN hnt (0 : Plane)
  have hsquare : Integrable (fun ω => kpzLattice ϑ N t 0 0 ω ^ 2) disorderLaw :=
    hmem.integrable_sq
  have hCeq : C = ∫⁻ ω, ENNReal.ofReal (kpzLattice ϑ N t 0 0 ω ^ 2) ∂disorderLaw := by
    dsimp [C]
    exact ofReal_integral_eq_lintegral_ofReal hsquare
      (Filter.Eventually.of_forall fun ω => sq_nonneg _)
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    exact ENNReal.ofReal_lt_top
  · intro x
    have hmemx := memLp_kpzLattice_flat_fixed ϑ hN hnt x
    have hsquarex : Integrable (fun ω => kpzLattice ϑ N t 0 x ω ^ 2) disorderLaw :=
      hmemx.integrable_sq
    have hconvx := ofReal_integral_eq_lintegral_ofReal hsquarex
      (Filter.Eventually.of_forall fun ω => sq_nonneg _)
    calc
      _ = ENNReal.ofReal (∫ ω, kpzLattice ϑ N t 0 x ω ^ 2 ∂disorderLaw) := hconvx.symm
      _ = C := by rw [integral_kpzLattice_flat_sq_eq_zeroSite_fixed ϑ hN hnt x]
      _ ≤ C := le_rfl

private theorem kpzLattice_uniform_secondMoment_fixed (ϑ : ℝ) (N : ℕ) (t : ℝ)
    (ht : 0 < t) (h₀ : Plane →ᵇ ℝ) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x : Plane,
      (∫⁻ ω, ENNReal.ofReal (kpzLattice ϑ N t h₀ x ω ^ 2) ∂disorderLaw) ≤ C := by
  by_cases hN : N = 0
  · subst N
    refine ⟨0, by simp, ?_⟩
    intro x
    have hzero (ω : Disorder) : kpzLattice ϑ 0 t h₀ x ω = 0 := by
      simp [kpzLattice, kpzLatticeCentring, rescaledP2P]
    simp [hzero]
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    have htime : 0 < (N : ℝ) * t := mul_pos (by exact_mod_cast hNpos) ht
    have hnt : 1 ≤ evenCeil ((N : ℝ) * t) := by
      have hceil : 1 ≤ ⌈((N : ℝ) * t) / 2⌉₊ :=
        Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by positivity)).ne'
      unfold evenCeil
      omega
    obtain ⟨Cflat, hCflat, hflat⟩ := kpzLattice_flat_uniform_secondMoment_fixed ϑ hNpos hnt
    let c : ℝ := ‖h₀‖
    let C : ℝ≥0∞ := 2 * (Cflat + ENNReal.ofReal (c ^ 2))
    have hC : C < ⊤ := by
      dsimp [C]
      exact ENNReal.mul_lt_top (by norm_num) (ENNReal.add_lt_top.mpr
        ⟨hCflat, ENNReal.ofReal_lt_top⟩)
    refine ⟨C, hC, ?_⟩
    intro x
    have hpoint (ω : Disorder) :
        ENNReal.ofReal (kpzLattice ϑ N t h₀ x ω ^ 2) ≤
          2 * (ENNReal.ofReal (kpzLattice ϑ N t 0 x ω ^ 2) +
            ENNReal.ofReal (c ^ 2)) := by
      have habs : |kpzLattice ϑ N t h₀ x ω| ≤
          |kpzLattice ϑ N t 0 x ω| + c := by
        calc
          |kpzLattice ϑ N t h₀ x ω| =
              |(kpzLattice ϑ N t h₀ x ω - kpzLattice ϑ N t 0 x ω) +
                kpzLattice ϑ N t 0 x ω| := by
                  congr 1
                  ring
          _ ≤ |kpzLattice ϑ N t h₀ x ω - kpzLattice ϑ N t 0 x ω| +
              |kpzLattice ϑ N t 0 x ω| := abs_add_le _ _
          _ ≤ |kpzLattice ϑ N t 0 x ω| + c := by
            have hshift :
                |kpzLattice ϑ N t h₀ x ω - kpzLattice ϑ N t 0 x ω| ≤ c := by
              simpa [c] using kpzLattice_initialShift_bound_fixed ϑ hNpos t h₀ x ω
            calc
              _ = |kpzLattice ϑ N t 0 x ω| +
                  |kpzLattice ϑ N t h₀ x ω - kpzLattice ϑ N t 0 x ω| := by ac_rfl
              _ ≤ |kpzLattice ϑ N t 0 x ω| + c := by nlinarith [hshift]
      have hc : 0 ≤ c := norm_nonneg _
      have hsq : kpzLattice ϑ N t h₀ x ω ^ 2 ≤
          2 * (kpzLattice ϑ N t 0 x ω ^ 2 + c ^ 2) := by
        have hupperSq : |kpzLattice ϑ N t h₀ x ω| ^ 2 ≤
            (|kpzLattice ϑ N t 0 x ω| + c) ^ 2 :=
          (sq_le_sq₀ (abs_nonneg _) (add_nonneg (abs_nonneg _) hc)).2 habs
        calc
          _ = |kpzLattice ϑ N t h₀ x ω| ^ 2 := (sq_abs _).symm
          _ ≤ (|kpzLattice ϑ N t 0 x ω| + c) ^ 2 := hupperSq
          _ ≤ 2 * (|kpzLattice ϑ N t 0 x ω| ^ 2 + c ^ 2) := by
            nlinarith [sq_nonneg (|kpzLattice ϑ N t 0 x ω| - c)]
          _ = 2 * (kpzLattice ϑ N t 0 x ω ^ 2 + c ^ 2) := by rw [sq_abs]
      calc
        _ ≤ ENNReal.ofReal
            (2 * (kpzLattice ϑ N t 0 x ω ^ 2 + c ^ 2)) := ENNReal.ofReal_le_ofReal hsq
        _ = _ := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
          norm_num
    calc
      _ ≤ ∫⁻ ω, 2 * (ENNReal.ofReal (kpzLattice ϑ N t 0 x ω ^ 2) +
          ENNReal.ofReal (c ^ 2)) ∂disorderLaw := by
            apply lintegral_mono
            intro ω
            exact hpoint ω
      _ = 2 * (∫⁻ ω, ENNReal.ofReal (kpzLattice ϑ N t 0 x ω ^ 2) ∂disorderLaw +
          ENNReal.ofReal (c ^ 2)) := by
            rw [lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
              lintegral_add_right _ (measurable_const :
                Measurable (fun _ : Disorder => ENNReal.ofReal (c ^ 2)))]
            simp
      _ ≤ C := by
        dsimp [C]
        gcongr
        exact hflat x

theorem kpzLattice_expected_localEnergy_lt_top (ϑ : ℝ) (N : ℕ) (t : ℝ)
    (ht : 0 < t) (h₀ : Plane →ᵇ ℝ) {a : ℝ} (ha : 0 ≤ a) (χ : TestFn) :
    (∫⁻ ω, localNegSobolevSq a
      (Distribution.ofFun ⊤ (fun x => kpzLattice ϑ N t h₀ x ω) volume ⊤) χ
        ∂disorderLaw) < ⊤ := by
  obtain ⟨C, hC, hXC⟩ := kpzLattice_uniform_secondMoment_fixed ϑ N t ht h₀
  let X : Disorder → Plane → ℝ := fun ω x => kpzLattice ϑ N t h₀ x ω
  have hX : Measurable (fun q : Disorder × Plane => X q.1 q.2) :=
    measurable_kpzLattice_joint ϑ N t h₀
  let f : Disorder × Plane → ℝ≥0∞ := fun q => ENNReal.ofReal ((χ q.2 * X q.1 q.2) ^ 2)
  have hχmeas : Measurable (fun q : Disorder × Plane => χ q.2) :=
    χ.continuous.measurable.comp measurable_snd
  have hf : Measurable f := by
    apply ENNReal.measurable_ofReal.comp
    exact (hχmeas.mul hX).pow_const 2
  obtain ⟨B, hB0, hBχ, hBint⟩ := testFn_norm_data_fixed χ
  let Mχ : ℝ≥0∞ := ∫⁻ x : Plane, ENNReal.ofReal ‖χ x‖
  have hMχtop : Mχ < ⊤ := by
    have heq : Mχ = ENNReal.ofReal (∫ x : Plane, ‖χ x‖) := by
      dsimp [Mχ]
      simpa only [Real.norm_eq_abs] using
        (ofReal_integral_eq_lintegral_ofReal hBint
          (Filter.Eventually.of_forall fun x => norm_nonneg (χ x))).symm
    rw [heq]
    exact ENNReal.ofReal_lt_top
  have hχsq :
      (∫⁻ x : Plane, ENNReal.ofReal (χ x ^ 2)) ≤ ENNReal.ofReal B * Mχ := by
    calc
      _ ≤ ∫⁻ x : Plane, ENNReal.ofReal B * ENNReal.ofReal ‖χ x‖ := by
        apply lintegral_mono
        intro x
        change ENNReal.ofReal (χ x ^ 2) ≤
          ENNReal.ofReal B * ENNReal.ofReal ‖χ x‖
        rw [← ENNReal.ofReal_mul hB0]
        apply ENNReal.ofReal_le_ofReal
        have habs : |χ x| ≤ B := by simpa only [Real.norm_eq_abs] using hBχ x
        have hbound : χ x ^ 2 ≤ B * |χ x| := by
          rw [← sq_abs]
          nlinarith [abs_nonneg (χ x)]
        simpa [Real.norm_eq_abs, mul_comm] using hbound
      _ = ENNReal.ofReal B * Mχ := by
        dsimp [Mχ]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hχsqtop : (∫⁻ x : Plane, ENNReal.ofReal (χ x ^ 2)) < ⊤ := by
    exact lt_of_le_of_lt hχsq
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hMχtop)
  have hinner (x : Plane) :
      (∫⁻ ω, f (ω, x) ∂disorderLaw) ≤ ENNReal.ofReal (χ x ^ 2) * C := by
    have hfactor : (fun ω : Disorder => f (ω, x)) = fun ω =>
        ENNReal.ofReal (χ x ^ 2) * ENNReal.ofReal (X ω x ^ 2) := by
      funext ω
      simp [f, mul_pow, ENNReal.ofReal_mul (sq_nonneg (χ x))]
    rw [hfactor, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc
      _ = (∫⁻ ω, ENNReal.ofReal (X ω x ^ 2) ∂disorderLaw) *
          ENNReal.ofReal (χ x ^ 2) := by rw [mul_comm]
      _ ≤ C * ENNReal.ofReal (χ x ^ 2) := mul_le_mul_left (hXC x) _
      _ = _ := by rw [mul_comm]
  have hlocal (ω : Disorder) :
      localNegSobolevSq a (Distribution.ofFun ⊤ (X ω) volume ⊤) χ ≤
        ∫⁻ x : Plane, f (ω, x) := by
    exact localNegSobolevSq_ofFun_le_lintegral ha
      (kpzLattice_locallyIntegrable ϑ N t h₀ ω) χ
  calc
    _ ≤ ∫⁻ ω, ∫⁻ x : Plane, f (ω, x) ∂volume ∂disorderLaw := by
      apply lintegral_mono
      intro ω
      exact hlocal ω
    _ = ∫⁻ x : Plane, ∫⁻ ω, f (ω, x) ∂disorderLaw ∂volume := by
      have hfun : (Function.uncurry (fun ω : Disorder => fun x : Plane => f (ω, x))) = f := by
        funext p
        rfl
      rw [lintegral_lintegral_swap (hfun ▸ hf.aemeasurable)]
    _ ≤ ∫⁻ x : Plane, ENNReal.ofReal (χ x ^ 2) * C := by
      apply lintegral_mono
      intro x
      exact hinner x
    _ < ⊤ := by
      have hEq : (∫⁻ x : Plane, ENNReal.ofReal (χ x ^ 2) * C) =
          C * ∫⁻ x : Plane, ENNReal.ofReal (χ x ^ 2) := by
        calc
          _ = ∫⁻ x : Plane, C * ENNReal.ofReal (χ x ^ 2) := by
            congr 1
            funext x
            exact mul_comm _ _
          _ = _ := lintegral_const_mul' _ _ hC.ne
      rw [hEq]
      exact ENNReal.mul_lt_top hC hχsqtop

/-- The lattice field has a uniform bound on expected local negative Sobolev energy at every index. -/
theorem kpzLattice_negSobolev_moment_le_allN_of (hVD : Smoothing.PropVDBound) (ϑ : ℝ)
    {t : ℝ} (ht : 0 < t) (h₀ : Plane →ᵇ ℝ) {a : ℝ} (ha : 0 < a) (χ : TestFn) :
    ∃ C : ℝ, ∀ N : ℕ,
      (∫⁻ ω, localNegSobolevSq a
        (Distribution.ofFun ⊤ (fun x => kpzLattice ϑ N t h₀ x ω) volume ⊤) χ
          ∂disorderLaw) ≤ ENNReal.ofReal C := by
  classical
  let E : ℕ → ℝ≥0∞ := fun N =>
    ∫⁻ ω, localNegSobolevSq a
      (Distribution.ofFun ⊤ (fun x => kpzLattice ϑ N t h₀ x ω) volume ⊤) χ
        ∂disorderLaw
  have hEfinite (N : ℕ) : E N < ⊤ := by
    exact kpzLattice_expected_localEnergy_lt_top ϑ N t ht h₀ ha.le χ
  obtain ⟨Ceventual, hCeventual⟩ := kpzLattice_negSobolev_moment_le_of hVD ϑ
    ht h₀ ha χ
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hCeventual
  let Cearly : ℝ := ∑ N ∈ Finset.range N₀, (E N).toReal
  let C : ℝ := max Ceventual 0 + Cearly
  have hCearly_nonneg : 0 ≤ Cearly := by
    dsimp [Cearly]
    apply Finset.sum_nonneg
    intro N hN
    exact ENNReal.toReal_nonneg
  refine ⟨C, fun N => ?_⟩
  by_cases hlarge : N₀ ≤ N
  · have heventual : E N ≤ ENNReal.ofReal Ceventual := by
      simpa [E] using hN₀ N hlarge
    exact heventual.trans (ENNReal.ofReal_le_ofReal (by
      dsimp [C]
      linarith [le_max_left Ceventual 0, hCearly_nonneg]))
  · have hsmall : N < N₀ := Nat.lt_of_not_ge hlarge
    have hsum : (E N).toReal ≤ Cearly := by
      dsimp [Cearly]
      exact Finset.single_le_sum (f := fun j => (E j).toReal)
        (fun j hj => ENNReal.toReal_nonneg) (Finset.mem_range.mpr hsmall)
    have hErepr : E N = ENNReal.ofReal (E N).toReal :=
      (ENNReal.ofReal_toReal (ne_of_lt (hEfinite N))).symm
    change E N ≤ ENNReal.ofReal C
    rw [hErepr]
    apply ENNReal.ofReal_le_ofReal
    dsimp [C]
    linarith [hsum, hCearly_nonneg, le_max_right Ceventual 0]

end Critical2DKPZ.LocalSobolev

end
