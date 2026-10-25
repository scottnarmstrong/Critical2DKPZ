/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SmallScales.ShrinkingReversedLattice
public import Critical2DKPZ.JointConvergence.ThmToyJointConvergence
public import Critical2DKPZ.JointConvergence.HeatStartLogFieldConvergence
public import Critical2DKPZ.LocalSobolev.Inputs
public import Critical2DKPZ.SHF.Positivity.BoundedPairingConvergence
public import Critical2DKPZ.SHF.Positivity.HeatPairingEhrhard
public import Critical2DKPZ.SHF.Limit.Basic

/-! # The continuum shrinking-width comparison -/

@[expose] public section

open MeasureTheory Filter
open scoped BoundedContinuousFunction ENNReal Topology

universe u

namespace Critical2DKPZ.SmallScales

open Critical2DKPZ.JointConvergence Critical2DKPZ.LocalSobolev Critical2DKPZ.SHF.Limit

private theorem integral_latticePoint_sub_eq_local {φ : TestFn} (N : ℕ) (f g : Site → ℝ) :
    (∫ x, φ x * (f (latticePoint N x) - g (latticePoint N x))) =
      (∫ x, φ x * f (latticePoint N x)) - (∫ x, φ x * g (latticePoint N x)) := by
  classical
  obtain ⟨S, hS⟩ := exists_finite_heatStartCells (fun _ : Fin 1 => φ) N
  have hSites : ∀ x, φ x ≠ 0 → latticePoint N x ∈ S := by
    intro x hx
    exact hS 0 x hx
  have hsub := integral_mul_latticePoint_piecewise φ.continuous φ.hasCompactSupport N
    (fun z => f z - g z) S hSites
  have hf := integral_mul_latticePoint_piecewise φ.continuous φ.hasCompactSupport N f S hSites
  have hg := integral_mul_latticePoint_piecewise φ.continuous φ.hasCompactSupport N g S hSites
  rw [hsub, hf, hg]
  calc
    (∑ z ∈ S, (∫ x in cell N z, φ x) * (f z - g z)) =
        ∑ z ∈ S, ((∫ x in cell N z, φ x) * f z - (∫ x in cell N z, φ x) * g z) := by
      apply Finset.sum_congr rfl
      intro z hz
      ring
    _ = (∑ z ∈ S, (∫ x in cell N z, φ x) * f z) -
        (∑ z ∈ S, (∫ x in cell N z, φ x) * g z) := by
      rw [Finset.sum_sub_distrib]

private theorem integral_latticeReversed_error_sub_eq (ϑ : ℝ) (N : ℕ) (T η : ℝ)
    (φ : TestFn) (ω : Disorder) :
    (∫ y, φ y * (kpzLatticeReversed ϑ N 0 T 0 y ω -
        kpzLatticeReversedReg ϑ N 0 T η 0 y ω)) =
      (∫ y, φ y * kpzLatticeReversed ϑ N 0 T 0 y ω) -
        (∫ y, φ y * kpzLatticeReversedReg ϑ N 0 T η 0 y ω) := by
  let β := criticalBeta ϑ N
  let a := evenCeil (N * T)
  let m := evenCeil (η * N)
  let raw : Site → ℝ := fun z =>
    Real.log (profileP2Fun β (evenCeil (N * 0)) a
        (fun w => if w = z then 1 else 0)
        (cellAverage N fun y => Real.exp ((0 : Plane →ᵇ ℝ) y)) ω)
      - ∫ ω', Real.log (profileP2Fun β (evenCeil (N * 0)) a
          (fun w => if w = z then 1 else 0) (fun _ => 1) ω') ∂disorderLaw
  let reg : Site → ℝ := fun z =>
    Real.log (profileP2Fun β (evenCeil (N * η)) a
        (fun w => srwKernel m (w - z))
        (cellAverage N fun y => Real.exp ((0 : Plane →ᵇ ℝ) y)) ω)
      - ∫ ω', Real.log (profileP2Fun β (evenCeil (N * η)) a
          (fun w => srwKernel m (w - z)) (fun _ => 1) ω') ∂disorderLaw
  have hrawpoint (y : Plane) :
      kpzLatticeReversed ϑ N 0 T 0 y ω = raw (latticePoint N y) := by
    simp [raw, β, a, kpzLatticeReversed, evenCeil_zero]
  have hregpoint (y : Plane) :
      kpzLatticeReversedReg ϑ N 0 T η 0 y ω = reg (latticePoint N y) := by
    simp [reg, β, a, m, kpzLatticeReversedReg, zero_add]
  have hrawInt : (∫ y, φ y * raw (latticePoint N y)) =
      ∫ y, φ y * kpzLatticeReversed ϑ N 0 T 0 y ω := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      change φ y * raw (latticePoint N y) = _
      rw [← hrawpoint y]
  have hregInt : (∫ y, φ y * reg (latticePoint N y)) =
      ∫ y, φ y * kpzLatticeReversedReg ϑ N 0 T η 0 y ω := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      change φ y * reg (latticePoint N y) = _
      rw [← hregpoint y]
  calc
    (∫ y, φ y * (kpzLatticeReversed ϑ N 0 T 0 y ω -
        kpzLatticeReversedReg ϑ N 0 T η 0 y ω)) =
        ∫ y, φ y * (raw (latticePoint N y) - reg (latticePoint N y)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        change φ y * (kpzLatticeReversed ϑ N 0 T 0 y ω -
          kpzLatticeReversedReg ϑ N 0 T η 0 y ω) = _
        rw [hrawpoint y, hregpoint y]
    _ = (∫ y, φ y * raw (latticePoint N y)) -
        (∫ y, φ y * reg (latticePoint N y)) := integral_latticePoint_sub_eq_local N raw reg
    _ = (∫ y, φ y * kpzLatticeReversed ϑ N 0 T 0 y ω) -
        (∫ y, φ y * kpzLatticeReversedReg ϑ N 0 T η 0 y ω) := by rw [hrawInt, hregInt]

/-- The averaged regularized reversed field has a uniformly bounded `L²` difference between widths at most the squared test scale. -/
theorem kpzRegularizedReversed_shrinking_le_of (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hHeatStartLogInput : HeatStartLogAt ϑ P Z) (hHeatStartLogFieldInput : HeatStartLogFieldAt ϑ P Z)
    (hLatticeSmoothingEnergyInput : LatticeSmoothingErrorEnergy)
    {T : ℝ} (hT : 0 < T) (φ : TestFn) :
    ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ x : Plane, ∀ δ : ℝ,
      0 < δ → δ ≤ ε ^ 2 →
        eLpNorm (fun ω => ∫ y, φ.dilate ε x y *
          (kpzRegularizedReversed P Z 0 T (ε ^ 2) 0 y ω -
            kpzRegularizedReversed P Z 0 T δ 0 y ω)) 2 P ≤ ENNReal.ofReal C := by
  have _hHeatStartLogInputAvailable : HeatStartLogAt ϑ P Z := hHeatStartLogInput
  have _hHeatStartLogInputFieldAvailable : HeatStartLogFieldAt ϑ P Z := hHeatStartLogFieldInput
  obtain ⟨C₀, ε₁, hC₀, hε₁, hraw⟩ :=
    kpzLatticeReversed_error_le_uniform_of hLatticeSmoothingEnergyInput ϑ T hT φ
  let ε₀ : ℝ := min ε₁ (Real.sqrt T / 2)
  let C : ℝ := 2 * C₀
  have hε₀ : 0 < ε₀ := by dsimp [ε₀]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, ε₀, hε₀, ?_⟩
  intro ε hε hεsmall x δ hδ hδε
  have hεlt : ε < ε₁ := lt_of_lt_of_le hεsmall (min_le_left _ _)
  have hεsqrt : ε < Real.sqrt T / 2 := lt_of_lt_of_le hεsmall (min_le_right _ _)
  have hεT : ε ^ 2 < T := by
    have hsq : ε ^ 2 < (Real.sqrt T / 2) ^ 2 := by
      nlinarith [sq_nonneg (ε - Real.sqrt T / 2)]
    rw [div_pow, Real.sq_sqrt hT.le] at hsq
    nlinarith
  have hδT : δ < T := lt_of_le_of_lt hδε hεT
  have hRawδ := hraw ε hε hεlt x δ hδ hδε
  have hRawε := hraw ε hε hεlt x (ε ^ 2) (sq_pos_of_pos hε) le_rfl
  let base : TestFn := φ.dilate ε x
  let ts : Fin 2 → ℝ := fun _ => 0
  let ds : Fin 2 → ℝ := fun i => if i = 0 then ε ^ 2 else δ
  let h₀s : Fin 2 → Plane →ᵇ ℝ := fun _ => 0
  let φs : Fin 2 → TestFn := fun _ => base
  have hpair : ∀ {s t δ' : ℝ}, 0 ≤ s → s < t → 0 < δ' → ∀ (z : Plane)
      (g : Plane →ᵇ ℝ),
      (∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane =>
        heatKernel δ' (p.1 - z) * g p.2) (Z s t ω)) ∧
      Integrable (shfPairing Z s t (fun y => heatKernel δ' (y - z)) g) P ∧
      (∫ ω, |shfPairing Z s t (fun y => heatKernel δ' (y - z)) g ω| ∂P ≤ ‖g‖) ∧
      TendstoInDistribution
        (fun (N : ℕ) (ω : Disorder) =>
          ∫ p, heatKernel δ' (p.1 - z) * g p.2 ∂(polymerMeasure ϑ N s t ω))
        atTop (shfPairing Z s t (fun y => heatKernel δ' (y - z)) g)
        (fun _ => disorderLaw) P := by
    intro s t δ' hs hst hδ' z g
    exact SHF.Positivity.isCriticalSHF_heat_bounded_pairing ϑ P Z hZ hs hst hδ' z g
  have hjoint := SHF.Positivity.isCriticalSHF_heat_bounded_pairing_joint ϑ P Z hZ
  have hpos : ∀ (s t δ' : ℝ) (z : Plane) (g : Plane →ᵇ ℝ), 0 ≤ s → s < t →
      0 < δ' →
      (∀ᵐ ω ∂P, 0 < shfPairing Z s t (fun y => heatKernel δ' (y - z))
        (fun y => Real.exp (g y)) ω) ∧
      AEMeasurable (fun ω => Real.log (shfPairing Z s t
        (fun y => heatKernel δ' (y - z)) (fun y => Real.exp (g y)) ω)) P := by
    intro s t δ' z g hs hst hδ'
    have h := SHF.Positivity.isCriticalSHF_heat_pairing_pos_isEhrhardType
      ϑ P Z hZ s t δ' z g hs hst hδ'
    exact ⟨h.1, h.2.1⟩
  have htimes : ∀ i : Fin 2, 0 ≤ ts i ∧ 0 < ds i ∧ ts i + ds i < T := by
    intro i
    fin_cases i
    · simp [ts, ds]; exact ⟨sq_pos_of_pos hε, by linarith⟩
    · simp [ts, ds]; exact ⟨hδ, hδT⟩
  have hreg := JointConvergence.kpzLatticeReversedReg_tendstoInDistribution
    ϑ P Z hZ hpair hjoint hpos ts T h₀s ds φs htimes
  have hregSub := hreg.continuous_comp
    (g := fun v : Fin 2 → ℝ => v 0 - v 1) (by fun_prop)
  have hregSub' : TendstoInDistribution
      (fun N ω =>
        (∫ y, base y * kpzLatticeReversedReg ϑ N 0 T (ε ^ 2) 0 y ω) -
          (∫ y, base y * kpzLatticeReversedReg ϑ N 0 T δ 0 y ω))
      atTop
      (fun ω =>
        (∫ y, base y * kpzRegularizedReversed P Z 0 T (ε ^ 2) 0 y ω) -
          (∫ y, base y * kpzRegularizedReversed P Z 0 T δ 0 y ω))
      (fun _ => disorderLaw) P := by
    simpa [ts, ds, h₀s, φs, Function.comp_def] using hregSub
  let E : ℝ → ℕ → Disorder → ℝ := fun η N ω =>
    ∫ y, base y * (kpzLatticeReversed ϑ N 0 T 0 y ω -
      kpzLatticeReversedReg ϑ N 0 T η 0 y ω)
  have hId (N : ℕ) :
      (fun ω =>
        (∫ y, base y * kpzLatticeReversedReg ϑ N 0 T (ε ^ 2) 0 y ω) -
          (∫ y, base y * kpzLatticeReversedReg ϑ N 0 T δ 0 y ω)) =
      fun ω => E δ N ω - E (ε ^ 2) N ω := by
    funext ω
    have hδ' := integral_latticeReversed_error_sub_eq ϑ N T δ base ω
    have hε' := integral_latticeReversed_error_sub_eq ϑ N T (ε ^ 2) base ω
    dsimp [E]
    rw [hδ', hε']
    ring
  have hEevent : ∀ᶠ N : ℕ in atTop,
      eLpNorm (fun ω => E δ N ω - E (ε ^ 2) N ω) 2 disorderLaw ≤ ENNReal.ofReal C := by
    filter_upwards [hRawδ, hRawε] with N hδN hεN
    have htri : eLpNorm (fun ω => E δ N ω - E (ε ^ 2) N ω) 2 disorderLaw ≤
        eLpNorm (E δ N) 2 disorderLaw + eLpNorm (E (ε ^ 2) N) 2 disorderLaw := by
      exact eLpNorm_sub_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hsum := add_le_add hδN hεN
    have hsum' : eLpNorm (E δ N) 2 disorderLaw + eLpNorm (E (ε ^ 2) N) 2 disorderLaw ≤
        ENNReal.ofReal C₀ + ENNReal.ofReal C₀ := hsum
    rw [← ENNReal.ofReal_add hC₀ hC₀] at hsum'
    have hCeq : C₀ + C₀ = C := by dsimp [C]; ring
    rw [hCeq] at hsum'
    exact htri.trans hsum'
  have hliminf := JointConvergence.eLpNorm_two_le_liminf_of_tendstoInDistribution hregSub'
  have hseqEq : (fun N => eLpNorm
      (fun ω =>
        (∫ y, base y * kpzLatticeReversedReg ϑ N 0 T (ε ^ 2) 0 y ω) -
          (∫ y, base y * kpzLatticeReversedReg ϑ N 0 T δ 0 y ω)) 2 disorderLaw) =
      fun N => eLpNorm (fun ω => E δ N ω - E (ε ^ 2) N ω) 2 disorderLaw := by
    funext N
    apply eLpNorm_congr_ae
    exact Filter.Eventually.of_forall fun ω => congrFun (hId N) ω
  rw [hseqEq] at hliminf
  let q : ℕ → ℝ≥0∞ := fun N => eLpNorm (fun ω => E δ N ω - E (ε ^ 2) N ω) 2 disorderLaw
  have hbounded : IsBoundedUnder (· ≤ ·) atTop q :=
    ⟨⊤, Filter.Eventually.of_forall fun _ => le_top⟩
  have hlimsup : Filter.limsup q atTop ≤ ENNReal.ofReal C :=
    Filter.limsup_le_of_le (by isBoundedDefault) hEevent
  have hliminfle : atTop.liminf q ≤ ENNReal.ofReal C :=
    (Filter.liminf_le_limsup hbounded).trans hlimsup
  have htargetEq :
      (fun ω => ∫ y, base y * (kpzRegularizedReversed P Z 0 T (ε ^ 2) 0 y ω -
        kpzRegularizedReversed P Z 0 T δ 0 y ω)) =ᵐ[P]
      fun ω => (∫ y, base y * kpzRegularizedReversed P Z 0 T (ε ^ 2) 0 y ω) -
        (∫ y, base y * kpzRegularizedReversed P Z 0 T δ 0 y ω) := by
    have hlogInt (σ : ℝ) (hσ : 0 < σ) (hσT : σ < T) : ∀ᵐ ω ∂P,
        Integrable (fun y => base y * Real.log (shfPairing Z σ T
          (fun u => heatKernel σ (u - y))
          (fun y => Real.exp ((0 : Plane →ᵇ ℝ) y)) ω)) := by
      let μ : Ω → Measure (Plane × Plane) := Z σ T
      have hlocal : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) := by
        filter_upwards [hZ.2.1 σ T (le_of_lt hσ) hσT] with ω hω
        exact hω.1
      have hg : Measurable (fun y : Plane => Real.exp ((0 : Plane →ᵇ ℝ) y)) := by
        fun_prop
      have hF : AEMeasurable (fun q : Plane × Ω => Real.log
          (shfPairing Z σ T (fun y => heatKernel σ (y - q.1))
            (fun y => Real.exp ((0 : Plane →ᵇ ℝ) y)) q.2))
          (volume.prod P) :=
        JointConvergence.aemeasurable_log_heatPairing_joint P μ
          (hZ.1 σ T (le_of_lt hσ) hσT) hlocal σ hσ
          (fun y => Real.exp ((0 : Plane →ᵇ ℝ) y)) hg (fun y => (Real.exp_nonneg _))
      have hFsec (x : Plane) : AEStronglyMeasurable
          (fun ω => Real.log (shfPairing Z σ T
            (fun y => heatKernel σ (y - x))
            (fun y => Real.exp ((0 : Plane →ᵇ ℝ) y)) ω)) P :=
        (hpos σ T σ x 0 (le_of_lt hσ) hσT hσ).2.aestronglyMeasurable
      obtain ⟨M, hM, hSq⟩ := JointConvergence.shf_heatStartLogField_square_bound
        ϑ P Z hZ hpair hjoint hpos T 0 (s := σ) (δ := σ) (le_of_lt hσ) hσT hσ
      have hprod := JointConvergence.integrable_test_mul_joint P hF hFsec hM hSq base
      exact Integrable.prod_left_ae hprod
    have hlogE : ∀ᵐ ω ∂P, Integrable (fun y => base y * Real.log
        (shfPairing Z (ε ^ 2) T (fun u => heatKernel (ε ^ 2) (u - y))
          (fun _ => (1 : ℝ)) ω)) := by
      simpa [Real.exp_zero] using hlogInt (ε ^ 2) (sq_pos_of_pos hε) hεT
    have hlogD : ∀ᵐ ω ∂P, Integrable (fun y => base y * Real.log
        (shfPairing Z δ T (fun u => heatKernel δ (u - y))
          (fun _ => (1 : ℝ)) ω)) := by
      simpa [Real.exp_zero] using hlogInt δ hδ hδT
    filter_upwards [hlogE, hlogD] with ω hlogEω hlogDω
    let cE : ℝ := ∫ ω', Real.log (shfPairing Z (ε ^ 2) T
      (fun y => heatKernel (ε ^ 2) y) (fun _ => (1 : ℝ)) ω') ∂P
    let cD : ℝ := ∫ ω', Real.log (shfPairing Z δ T
      (fun y => heatKernel δ y) (fun _ => (1 : ℝ)) ω') ∂P
    have hbase : Integrable (fun y : Plane => base y) :=
      base.continuous.integrable_of_hasCompactSupport base.hasCompactSupport
    have hfieldE : Integrable (fun y => base y *
        kpzRegularizedReversed P Z 0 T (ε ^ 2) 0 y ω) := by
      have heq : (fun y => base y * kpzRegularizedReversed P Z 0 T (ε ^ 2) 0 y ω) =
          fun y => base y * Real.log (shfPairing Z (ε ^ 2) T
              (fun u => heatKernel (ε ^ 2) (u - y)) (fun _ => (1 : ℝ)) ω) - base y * cE := by
        funext y
        simp [cE, kpzRegularizedReversed, Real.exp_zero, zero_add]
        ring
      rw [heq]
      exact hlogEω.sub (hbase.mul_const cE)
    have hfieldD : Integrable (fun y => base y *
        kpzRegularizedReversed P Z 0 T δ 0 y ω) := by
      have heq : (fun y => base y * kpzRegularizedReversed P Z 0 T δ 0 y ω) =
          fun y => base y * Real.log (shfPairing Z δ T
              (fun u => heatKernel δ (u - y)) (fun _ => (1 : ℝ)) ω) - base y * cD := by
        funext y
        simp [cD, kpzRegularizedReversed, Real.exp_zero, zero_add]
        ring
      rw [heq]
      exact hlogDω.sub (hbase.mul_const cD)
    have hfun : (fun y => base y *
        (kpzRegularizedReversed P Z 0 T (ε ^ 2) 0 y ω -
          kpzRegularizedReversed P Z 0 T δ 0 y ω)) =
        fun y => base y * kpzRegularizedReversed P Z 0 T (ε ^ 2) 0 y ω -
          base y * kpzRegularizedReversed P Z 0 T δ 0 y ω := by
      funext y
      ring
    rw [hfun, integral_sub hfieldE hfieldD]
  have hliminf' : eLpNorm (fun ω => ∫ y, base y *
      (kpzRegularizedReversed P Z 0 T (ε ^ 2) 0 y ω -
        kpzRegularizedReversed P Z 0 T δ 0 y ω)) 2 P ≤ ENNReal.ofReal C := by
    have hnorm : eLpNorm (fun ω => ∫ y, base y *
        (kpzRegularizedReversed P Z 0 T (ε ^ 2) 0 y ω -
          kpzRegularizedReversed P Z 0 T δ 0 y ω)) 2 P =
        eLpNorm (fun ω =>
          (∫ y, base y * kpzRegularizedReversed P Z 0 T (ε ^ 2) 0 y ω) -
            (∫ y, base y * kpzRegularizedReversed P Z 0 T δ 0 y ω)) 2 P := by
      apply eLpNorm_congr_ae
      exact htargetEq
    rw [hnorm]
    exact hliminf.trans hliminfle
  simpa [base, C] using hliminf'

end Critical2DKPZ.SmallScales

end
