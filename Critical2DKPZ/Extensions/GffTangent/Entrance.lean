/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.Fields
public import Critical2DKPZ.Extensions.GffTangent.Locality
public import Critical2DKPZ.Extensions.GffTangent.Scales
public import Critical2DKPZ.Definitions.TestFnScale
public import Critical2DKPZ.Extensions.GffTangent.ProfileIdentities
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Critical2DKPZ.SmallScales.ShrinkingReversedLattice
import Critical2DKPZ.Assembly.RootInputs
import Critical2DKPZ.Extensions.GffTangent.ProfileLemmaFlow
import Critical2DKPZ.Extensions.GffTangent.Localisation
import Critical2DKPZ.Extensions.GffTangent.CompareFutures

/-! # Entrance mass variances and centred logarithmic second moments -/

public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal BoundedContinuousFunction

namespace Critical2DKPZ.Extensions.GffTangent

universe u


/-- Centring converts the locality variance estimate to a genuine second-moment
estimate. The constant precedes the flow, scales, probability space and test. -/
theorem lField_second_moment_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (l a T : ℝ), 0 < a → a < T → 0 < l - Real.log T →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (_hZ : IsCriticalSHF (-l) P Z)
        (f : TestFn) (B : ℝ), 0 ≤ B → (∀ x, |f x| ≤ B) → (∫ x, f x) = 0 →
        MemLp (lField Z a T f) 2 P ∧
          (∫ ω, lField Z a T f ω ^ 2 ∂P) ≤
            C * (∫ x, |f x|) * B * T *
              (1 + Real.log (T / a) / (l - Real.log T)) ^ 3 *
                Real.sqrt (1 + Real.log (1 + Real.log (T / a) / (l - Real.log T))) := by
  obtain ⟨C, hC, hb⟩ := variance_entrance_log_pairing_le.{u}
  refine ⟨C, hC, ?_⟩
  intro l a T ha haT hl Ω _ P _ Z hZ f B hB hbound hf
  obtain ⟨_, hm, hv⟩ := hb l a T ha haT hl P Z hZ f B hB hbound
  change MemLp (lField Z a T f) 2 P at hm
  change variance (lField Z a T f) P ≤ _ at hv
  rw [variance_eq_sub hm, lField_centred (-l) P Z hZ T ha haT f hf, zero_pow (by decide : 2 ≠ 0),
    sub_zero] at hv
  exact ⟨hm, hv⟩

/-- A coarse mass with a small variance ratio has a uniformly bounded second moment. -/
theorem entrance_mass_second_moment_le (l : ℝ) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF (-l) P Z)
    {a T v : ℝ} (ha : 0 < a) (haT : a < T) (hl : 0 < l - Real.log T)
    (hv : Real.log (T / a) / (l - Real.log T) ≤ v) (x : Plane) :
    Integrable (fun ω => shfPairing Z a T
      (fun y => heatKernel a (y - x)) (fun _ => 1) ω ^ 2) P ∧
      (∫ ω, shfPairing Z a T (fun y => heatKernel a (y - x)) (fun _ => 1) ω ^ 2 ∂P) ≤ 1 + v :=
  ⟨(heatStartMass_memLp_two (-l) P Z hZ ha haT x).integrable_sq,
    (massCovariance_formula_and_bound l P Z hZ ha haT hl x x).2.2.trans
      (add_le_add (le_refl 1) hv)⟩

open Smoothing

theorem eLpNorm_lattice_difference_eq_smoothingError (ϑ : ℝ) (N : ℕ)
    {T η : ℝ} (hη : 0 < η) (hηT : η < T) (φ : TestFn) :
    eLpNorm (fun ω => ∫ y, φ y *
      (kpzLatticeReversed ϑ N 0 T 0 y ω - kpzLatticeReversedReg ϑ N 0 T η 0 y ω))
      2 disorderLaw =
    eLpNorm (latticeSmoothingError (criticalBeta ϑ N) N (evenCeil (N * T))
      (evenCeil (N * η)) (evenCeil (η * N)) 0 φ) 2 disorderLaw := by
  let f : Disorder → ℝ := fun ω => ∫ y, φ y *
    (kpzLatticeReversed ϑ N 0 T 0 y ω - kpzLatticeReversedReg ϑ N 0 T η 0 y ω)
  let g : Disorder → ℝ := latticeSmoothingError (criticalBeta ϑ N) N
    (evenCeil (N * T)) (evenCeil (N * η)) (evenCeil (η * N)) 0 φ
  have hfg : f = g ∘ shiftEnvironment 0 := by
    funext ω
    have hdiff := kpzLattice_difference_timeShift ϑ N (t := (0 : ℝ)) (T := T) (δ := η)
      (by norm_num) hη (by simpa using hηT) 0 φ ω
    change (∫ y, φ y * (kpzLatticeReversed ϑ N 0 T 0 y ω -
      kpzLatticeReversedReg ϑ N 0 T η 0 y ω)) = _
    rw [hdiff]
    simp [g, evenCeil_zero]
  have hfm : Measurable f := by
    rw [hfg]
    exact (measurable_latticeSmoothingError (criticalBeta ϑ N) N
      (evenCeil (N * T)) (evenCeil (N * η)) (evenCeil (η * N)) 0
      (φ := φ) φ.continuous.measurable).comp (measurable_shiftEnvironment 0)
  have hgm : Measurable g := measurable_latticeSmoothingError (criticalBeta ϑ N) N
    (evenCeil (N * T)) (evenCeil (N * η)) (evenCeil (η * N)) 0
    (φ := φ) φ.continuous.measurable
  have hmap (F : Disorder → ℝ) (hF : Measurable F) :
      eLpNorm F 2 disorderLaw = eLpNorm (fun x : ℝ => x) 2 (disorderLaw.map F) := by
    symm
    simpa only [Function.comp_def] using
      (eLpNorm_map_measure (μ := disorderLaw) (p := (2 : ENNReal))
        (f := F) (g := fun x : ℝ => x) measurable_id.aestronglyMeasurable
        hF.aemeasurable)
  calc
    eLpNorm f 2 disorderLaw = eLpNorm (fun x : ℝ => x) 2 (disorderLaw.map f) := hmap f hfm
    _ = eLpNorm (fun x : ℝ => x) 2 (disorderLaw.map g) := by
      rw [kpzLattice_difference_timeShift_law ϑ N (t := (0 : ℝ)) (T := T) (δ := η)
        (by norm_num) hη (by simpa using hηT) 0 φ]
      simp [g, evenCeil_zero]
    _ = eLpNorm g 2 disorderLaw := (hmap g hgm).symm


/-- Lower semicontinuity plus an eventual lattice estimate with vanishing
slack.  This is the exact reusable core of the 10(a) two-width passage. -/
theorem eLpNorm_two_le_of_tendstoInDistribution_eventually_ofReal_add
    {Ω' Ω : Type*} [MeasurableSpace Ω'] [MeasurableSpace Ω]
    {μ : ℕ → Measure Ω'} {P : Measure Ω}
    [∀ N, IsProbabilityMeasure (μ N)] [IsProbabilityMeasure P]
    {Y : ℕ → Ω' → ℝ} {X : Ω → ℝ} (R : ℝ)
    (hY : TendstoInDistribution Y atTop X μ P)
    (hbound : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      eLpNorm (Y N) 2 (μ N) ≤ ENNReal.ofReal (R + ε)) :
    eLpNorm X 2 P ≤ ENNReal.ofReal R := by
  have hliminf :=
    JointConvergence.eLpNorm_two_le_liminf_of_tendstoInDistribution hY
  have hlimsup (ε : ℝ) (hε : 0 < ε) :
      Filter.limsup (fun N => eLpNorm (Y N) 2 (μ N)) atTop ≤
        ENNReal.ofReal (R + ε) :=
    Filter.limsup_le_of_le (by isBoundedDefault) (hbound ε hε)
  let u : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (R + 1 / ((n : ℝ) + 1))
  have hu : Tendsto u atTop (𝓝 (ENNReal.ofReal R)) := by
    have hn : Tendsto (fun n : ℕ => R + 1 / ((n : ℝ) + 1)) atTop (𝓝 R) := by
      have hden : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa only [add_zero] using hden.const_add R
    simpa only [u, Function.comp_def] using
      (ENNReal.continuous_ofReal.continuousAt.tendsto (x := R)).comp hn
  have hbounded : IsBoundedUnder (· ≤ ·) atTop
      (fun N => eLpNorm (Y N) 2 (μ N)) :=
    ⟨⊤, Filter.Eventually.of_forall fun _ => le_top⟩
  have hliminf_le (n : ℕ) :
      atTop.liminf (fun N => eLpNorm (Y N) 2 (μ N)) ≤ u n := by
    apply (Filter.liminf_le_limsup hbounded).trans
    simpa only [u] using hlimsup (1 / ((n : ℝ) + 1)) (by positivity)
  exact hliminf.trans (ge_of_tendsto hu (Filter.Eventually.of_forall hliminf_le))

/-- Two individual lattice error estimates imply the exact two-width flow
estimate.  In the 10(a) application `E η N` is raw minus width-η and
`R η` is the heat-energy expression. -/
theorem two_width_flow_bound_of_lattice_errors
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ) (Y : ℝ → ℕ → Disorder → ℝ)
    (R : ℝ → ℝ) {δ δ' : ℝ}
    (hconv : TendstoInDistribution
      (fun N ω => Y δ' N ω - Y δ N ω) atTop
      (fun ω => X δ ω - X δ' ω) (fun _ => disorderLaw) P)
    (hδ : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      eLpNorm (Y δ N) 2 disorderLaw ≤ ENNReal.ofReal (R δ + ε))
    (hδ' : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      eLpNorm (Y δ' N) 2 disorderLaw ≤ ENNReal.ofReal (R δ' + ε))
    (hRδ : 0 ≤ R δ) (hRδ' : 0 ≤ R δ') :
    eLpNorm (fun ω => X δ ω - X δ' ω) 2 P ≤
      ENNReal.ofReal (R δ + R δ') := by
  apply eLpNorm_two_le_of_tendstoInDistribution_eventually_ofReal_add
    (R δ + R δ') hconv
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  filter_upwards [hδ (ε / 2) hhalf, hδ' (ε / 2) hhalf] with N hN hN'
  calc
    eLpNorm (fun ω => Y δ' N ω - Y δ N ω) 2 disorderLaw ≤
        eLpNorm (Y δ' N) 2 disorderLaw + eLpNorm (Y δ N) 2 disorderLaw :=
      eLpNorm_sub_le (by norm_num)
    _ ≤ ENNReal.ofReal (R δ' + ε / 2) + ENNReal.ofReal (R δ + ε / 2) :=
      add_le_add hN' hN
    _ = ENNReal.ofReal (R δ + R δ' + ε) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-- Passing a two-width estimate to the selected `L²` limit. -/
theorem eLpNorm_sub_limit_le_of_two_width
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ → Ω → ℝ) (K : Ω → ℝ)
    (R : ℝ → ℝ) {δ : ℝ}
    (hXK : Tendsto (fun η => eLpNorm (fun ω => X η ω - K ω) 2 P)
      (𝓝[>] 0) (𝓝 0))
    (hpair : ∀ᶠ η in 𝓝[>] (0 : ℝ),
      eLpNorm (fun ω => X δ ω - X η ω) 2 P ≤
        ENNReal.ofReal (R δ + R η))
    (hR : Tendsto R (𝓝[>] 0) (𝓝 0)) (_hRδ : 0 ≤ R δ) :
    eLpNorm (fun ω => X δ ω - K ω) 2 P ≤ ENNReal.ofReal (R δ) := by
  have htri : ∀ᶠ η in 𝓝[>] (0 : ℝ),
      eLpNorm (fun ω => X δ ω - K ω) 2 P ≤
        ENNReal.ofReal (R δ + R η) +
          eLpNorm (fun ω => X η ω - K ω) 2 P := by
    filter_upwards [hpair] with η hη
    calc
      eLpNorm (fun ω => X δ ω - K ω) 2 P =
          eLpNorm (fun ω => (X δ ω - X η ω) + (X η ω - K ω)) 2 P := by
        apply eLpNorm_congr_ae
        filter_upwards [] with ω
        ring
      _ ≤ eLpNorm (fun ω => X δ ω - X η ω) 2 P +
          eLpNorm (fun ω => X η ω - K ω) 2 P := eLpNorm_add_le (by norm_num)
      _ ≤ _ := add_le_add hη le_rfl
  have hright : Tendsto (fun η => ENNReal.ofReal (R δ + R η) +
      eLpNorm (fun ω => X η ω - K ω) 2 P) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (R δ))) := by
    have hfirst : Tendsto (fun η => ENNReal.ofReal (R δ + R η)) (𝓝[>] 0)
        (𝓝 (ENNReal.ofReal (R δ))) := by
      have hr : Tendsto (fun η => R δ + R η) (𝓝[>] 0) (𝓝 (R δ)) := by
        simpa only [add_zero] using (tendsto_const_nhds (x := R δ)).add hR
      simpa only [add_zero, Function.comp_def] using
        (ENNReal.continuous_ofReal.continuousAt.tendsto (x := R δ)).comp hr
    simpa only [add_zero] using hfirst.add hXK
  exact ge_of_tendsto hright htri

/-- On the even subsequence the unit-horizon lattice smoothing input applies
without any spatial or parameter rescaling. -/
theorem latticeReversed_error_energy_eventually_even
    (A : ℝ) {C δ₁ : ℝ}
    (hinput : ∀ δ : ℝ, 0 < δ → δ < δ₁ →
      ∀ φ : Plane → ℝ, Measurable φ → HasCompactSupport φ →
      Integrable φ → (∃ B : ℝ, ∀ x, |φ x| ≤ B) →
      ∀ c₀ c₁ : ℝ, 0 < c₀ → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ M : ℕ in atTop, Even M → ∀ c ∈ Set.Icc c₀ c₁,
      ∀ ϑ ∈ Set.Icc (-A) A, ∀ j k : ℕ, Even j → Even k →
      (j : ℤ) ≤ evenCeil (δ * M) + 6 →
      (evenCeil (δ * M) : ℤ) ≤ j + 6 →
      (k : ℤ) ≤ evenCeil (δ * M) + 6 →
      (evenCeil (δ * M) : ℤ) ≤ k + 6 →
      ∀ h₀ : Plane →ᵇ ℝ, ‖h₀‖ ≤ 0 →
      eLpNorm (Smoothing.latticeSmoothingError (criticalBeta ϑ M) M M k j h₀
        (fun y => c * φ (Real.sqrt c • y))) 2 disorderLaw ≤
      ENNReal.ofReal (Real.sqrt
          (C * Smoothing.heatEnergy (Real.sqrt δ)
            (fun y => c * φ (Real.sqrt c • y)) / |Real.log δ|) +
        C * (∫ x, |c * φ (Real.sqrt c • x)|) *
          |Real.log δ| ^ (-(1 : ℝ) / 40) + ε))
    {ϑ η ε : ℝ} (hϑ : ϑ ∈ Set.Icc (-A) A)
    (hη : 0 < η) (hηsmall : η < δ₁) (hηone : η < 1)
    (hε : 0 < ε) (f : TestFn) :
    ∀ᶠ n : ℕ in atTop,
      eLpNorm (fun ω => ∫ y, f y *
        (kpzLatticeReversed ϑ (2 * n) 0 1 0 y ω -
          kpzLatticeReversedReg ϑ (2 * n) 0 1 η 0 y ω))
        2 disorderLaw ≤
      ENNReal.ofReal (Real.sqrt
          (C * Smoothing.heatEnergy (Real.sqrt η) f / |Real.log η|) +
        C * (∫ x, |f x|) * |Real.log η| ^ (-(1 : ℝ) / 40) + ε) := by
  obtain ⟨B, hBraw⟩ := f.hasCompactSupport.exists_bound_of_continuous f.continuous
  have hB : ∀ x : Plane, |f x| ≤ B := by
    simpa only [Real.norm_eq_abs] using hBraw
  have hfI : Integrable (f : Plane → ℝ) :=
    f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hraw := hinput η hη hηsmall f f.continuous.measurable
    f.hasCompactSupport hfI ⟨B, hB⟩ 1 1 zero_lt_one ε hε
  have heven : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_mono (fun n => by omega : ∀ n : ℕ, n ≤ 2 * n) tendsto_id
  have hrawEven := heven.eventually hraw
  filter_upwards [hrawEven, eventually_gt_atTop 0] with n hn hnpos
  let N : ℕ := 2 * n
  let j : ℕ := evenCeil (η * N)
  have hNeven : Even N := by exact even_two_mul n
  have hj : Even j := evenCeil_even _
  have hunit := hn hNeven 1 (by simp) ϑ hϑ j j hj hj
    (by dsimp only [j, N]; omega) (by dsimp only [j, N]; omega)
    (by dsimp only [j, N]; omega) (by dsimp only [j, N]; omega) 0 (by simp)
  have hnorm := eLpNorm_lattice_difference_eq_smoothingError ϑ N hη hηone f
  rw [show evenCeil ((N : ℝ) * 1) = N by
    simpa only [mul_one] using profile_evenCeil_natCast hNeven] at hnorm
  rw [hnorm]
  simpa only [N, j, one_mul, Real.sqrt_one, one_smul, mul_comm] using hunit

theorem integral_latticePoint_sub_eq
    {φ : TestFn}
    (N : ℕ) (f g : Site → ℝ) :
    (∫ x, φ x * (f (latticePoint N x) - g (latticePoint N x))) =
      (∫ x, φ x * f (latticePoint N x)) - (∫ x, φ x * g (latticePoint N x)) := by
  classical
  obtain ⟨S, hS⟩ := JointConvergence.exists_finite_heatStartCells (fun _ : Fin 1 => φ) N
  have hSites : ∀ x, φ x ≠ 0 → latticePoint N x ∈ S := by
    intro x hx
    exact hS 0 x hx
  have hsub := JointConvergence.integral_mul_latticePoint_piecewise φ.continuous φ.hasCompactSupport N
    (fun z => f z - g z) S hSites
  have hf := JointConvergence.integral_mul_latticePoint_piecewise φ.continuous φ.hasCompactSupport N f S hSites
  have hg := JointConvergence.integral_mul_latticePoint_piecewise φ.continuous φ.hasCompactSupport N g S hSites
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


/-- The actual two-width regularisation estimate retains its test-energy
term through the lattice-to-flow passage, with a constant uniform in the
bounded parameter interval. -/
theorem kpzRegularizedReversed_two_width_energy (A : ℝ) :
    ∃ C δ₁ : ℝ, 0 < C ∧ 0 < δ₁ ∧
    ∀ (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
      (_hZ : IsCriticalSHF ϑ P Z), ϑ ∈ Set.Icc (-A) A →
    ∀ f : TestFn, ∀ δ ∈ Set.Ioo (0 : ℝ) δ₁,
      ∀ δ' ∈ Set.Ioo (0 : ℝ) δ₁,
      eLpNorm (fun ω =>
        (∫ x, f x * kpzRegularizedReversed P Z 0 1 δ 0 x ω) -
        (∫ x, f x * kpzRegularizedReversed P Z 0 1 δ' 0 x ω)) 2 P ≤
      ENNReal.ofReal
        ((Real.sqrt (C * heatEnergy (Real.sqrt δ) f / |Real.log δ|) +
            C * (∫ x, |f x|) * |Real.log δ| ^ (-(1 : ℝ) / 40)) +
         (Real.sqrt (C * heatEnergy (Real.sqrt δ') f / |Real.log δ'|) +
            C * (∫ x, |f x|) * |Real.log δ'| ^ (-(1 : ℝ) / 40))) := by
  classical
  obtain ⟨Craw, δraw, hδraw, hinput⟩ := Assembly.latticeSmoothingErrorEnergy A 0
  let C := max Craw 1
  let δ₁ := min δraw (Real.exp (-1))
  have hC : 0 < C := zero_lt_one.trans_le (le_max_right _ _)
  have hCC : Craw ≤ C := le_max_left _ _
  have hδ₁ : 0 < δ₁ := lt_min hδraw (Real.exp_pos _)
  refine ⟨C, δ₁, hC, hδ₁, ?_⟩
  intro ϑ Ω _ P _ Z hZ hϑ f δ hδ δ' hδ'
  let R : ℝ → ℝ := fun η =>
    Real.sqrt (C * heatEnergy (Real.sqrt η) f / |Real.log η|) +
      C * (∫ x, |f x|) * |Real.log η| ^ (-(1 : ℝ) / 40)
  have henergy (η : ℝ) : 0 ≤ heatEnergy (Real.sqrt η) f := by
    apply integral_nonneg
    intro p
    apply mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    apply mul_nonneg (by norm_num)
    apply intervalIntegral.integral_nonneg (Real.sqrt_nonneg _)
    intro r hr
    exact heatKernel_nonneg (mul_nonneg (by norm_num) hr.1) _
  have hunit (η : ℝ) (hη : η ∈ Set.Ioo (0 : ℝ) δ₁) (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ n : ℕ in atTop,
      eLpNorm (fun ω => ∫ y, f y *
        (kpzLatticeReversed ϑ (2*n) 0 1 0 y ω -
          kpzLatticeReversedReg ϑ (2*n) 0 1 η 0 y ω)) 2 disorderLaw ≤
        ENNReal.ofReal (R η + ε) := by
    have hηone : η < 1 := hη.2.trans_le (min_le_right _ _) |>.trans
      (Real.exp_lt_one_iff.mpr (by norm_num : (-1 : ℝ) < 0))
    have hb := latticeReversed_error_energy_eventually_even A hinput hϑ
      hη.1 (hη.2.trans_le (min_le_left _ _)) hηone hε f
    filter_upwards [hb] with n hn
    apply hn.trans
    apply ENNReal.ofReal_le_ofReal
    dsimp only [R]
    refine add_le_add ?_ le_rfl
    apply add_le_add
    · apply Real.sqrt_le_sqrt
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCC (henergy η))
        (abs_nonneg _)
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCC (integral_nonneg fun _ => abs_nonneg _))
        (Real.rpow_nonneg (abs_nonneg _) _)
  have hδone : δ < 1 := (hδ.2.trans_le (min_le_right _ _)).trans
    (Real.exp_lt_one_iff.mpr (by norm_num : (-1 : ℝ) < 0))
  have hδ'one : δ' < 1 := (hδ'.2.trans_le (min_le_right _ _)).trans
    (Real.exp_lt_one_iff.mpr (by norm_num : (-1 : ℝ) < 0))
  let ds : Fin 2 → ℝ := fun i => if i = 0 then δ else δ'
  have hpos (s t η : ℝ) (x : Plane) (g : Plane →ᵇ ℝ)
      (hs : 0 ≤ s) (hst : s < t) (hη : 0 < η) :=
    let h := SHF.Positivity.isCriticalSHF_heat_pairing_pos_isEhrhardType
      ϑ P Z hZ s t η x g hs hst hη
    And.intro h.1 h.2.1
  have hreg := JointConvergence.kpzLatticeReversedReg_tendstoInDistribution
    ϑ P Z hZ (fun hs hst hη x g =>
      SHF.Positivity.isCriticalSHF_heat_bounded_pairing ϑ P Z hZ hs hst hη x g)
    (SHF.Positivity.isCriticalSHF_heat_bounded_pairing_joint ϑ P Z hZ)
    hpos (fun _ : Fin 2 => 0) 1 (fun _ => 0) ds (fun _ => f) (by
      intro i
      fin_cases i
      · simpa [ds] using (show (0 : ℝ) ≤ 0 ∧ 0 < δ ∧ 0 + δ < 1 from
          ⟨le_rfl, hδ.1, by simpa only [zero_add] using hδone⟩)
      · simpa [ds] using (show (0 : ℝ) ≤ 0 ∧ 0 < δ' ∧ 0 + δ' < 1 from
          ⟨le_rfl, hδ'.1, by simpa only [zero_add] using hδ'one⟩))
  have hsub := hreg.continuous_comp
    (g := fun v : Fin 2 → ℝ => v 0 - v 1) (by fun_prop)
  have heven : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_mono (fun n => by omega : ∀ n : ℕ, n ≤ 2 * n) tendsto_id
  have hsub' : TendstoInDistribution
      (fun n ω =>
        (∫ x, f x * kpzLatticeReversedReg ϑ (2*n) 0 1 δ 0 x ω) -
        (∫ x, f x * kpzLatticeReversedReg ϑ (2*n) 0 1 δ' 0 x ω)) atTop
      (fun ω =>
        (∫ x, f x * kpzRegularizedReversed P Z 0 1 δ 0 x ω) -
        (∫ x, f x * kpzRegularizedReversed P Z 0 1 δ' 0 x ω))
      (fun _ => disorderLaw) P := by
    have hs : TendstoInDistribution
        (fun N ω =>
          (∫ x, f x * kpzLatticeReversedReg ϑ N 0 1 δ 0 x ω) -
          (∫ x, f x * kpzLatticeReversedReg ϑ N 0 1 δ' 0 x ω)) atTop
        (fun ω =>
          (∫ x, f x * kpzRegularizedReversed P Z 0 1 δ 0 x ω) -
          (∫ x, f x * kpzRegularizedReversed P Z 0 1 δ' 0 x ω))
        (fun _ => disorderLaw) P := by
      simpa [ds, Function.comp_def] using hsub
    exact ⟨fun n => hs.forall_aemeasurable (2*n), hs.aemeasurable_limit,
      hs.tendsto.comp heven⟩
  let E : ℝ → ℕ → Disorder → ℝ := fun η n ω =>
    ∫ x, f x * (kpzLatticeReversed ϑ (2*n) 0 1 0 x ω -
      kpzLatticeReversedReg ϑ (2*n) 0 1 η 0 x ω)
  have hErr (η : ℝ) (N : ℕ) (ω : Disorder) : E η N ω =
      (∫ x, f x * kpzLatticeReversed ϑ (2*N) 0 1 0 x ω) -
        (∫ x, f x * kpzLatticeReversedReg ϑ (2*N) 0 1 η 0 x ω) := by
    let raw : Site → ℝ := fun z =>
      Real.log (profileP2Fun (criticalBeta ϑ (2*N)) (evenCeil ((2*N : ℕ) * (0 : ℝ))) (evenCeil ((2*N : ℕ) * (1 : ℝ)))
        (fun w => if w = z then 1 else 0) (cellAverage (2*N) fun y => Real.exp ((0 : Plane →ᵇ ℝ) y)) ω) -
        ∫ ω', Real.log (profileP2Fun (criticalBeta ϑ (2*N)) (evenCeil ((2*N : ℕ) * (0 : ℝ)))
          (evenCeil ((2*N : ℕ) * (1 : ℝ))) (fun w => if w = z then 1 else 0) (fun _ => 1) ω') ∂disorderLaw
    let reg (η : ℝ) : Site → ℝ := fun z =>
      Real.log (profileP2Fun (criticalBeta ϑ (2*N)) (evenCeil ((2*N : ℕ) * (0 + η)))
        (evenCeil ((2*N : ℕ) * (1 : ℝ))) (fun w => srwKernel (evenCeil (η * (2*N : ℕ))) (w - z))
        (cellAverage (2*N) fun y => Real.exp ((0 : Plane →ᵇ ℝ) y)) ω) -
        ∫ ω', Real.log (profileP2Fun (criticalBeta ϑ (2*N)) (evenCeil ((2*N : ℕ) * (0 + η)))
          (evenCeil ((2*N : ℕ) * (1 : ℝ))) (fun w => srwKernel (evenCeil (η * (2*N : ℕ))) (w - z))
          (fun _ => 1) ω') ∂disorderLaw
    have hsplit := integral_latticePoint_sub_eq (φ := f) (2*N) raw (reg η)
    simpa [E, raw, reg, kpzLatticeReversed, kpzLatticeReversedReg] using hsplit
  have hId (N : ℕ) : (fun ω =>
      (∫ x, f x * kpzLatticeReversedReg ϑ (2*N) 0 1 δ 0 x ω) -
        (∫ x, f x * kpzLatticeReversedReg ϑ (2*N) 0 1 δ' 0 x ω)) =
      fun ω => E δ' N ω - E δ N ω := by
    funext ω
    rw [hErr δ N ω, hErr δ' N ω]
    ring
  have hconv : TendstoInDistribution (fun N ω => E δ' N ω - E δ N ω) atTop
      (fun ω =>
        (∫ x, f x * kpzRegularizedReversed P Z 0 1 δ 0 x ω) -
        (∫ x, f x * kpzRegularizedReversed P Z 0 1 δ' 0 x ω))
      (fun _ => disorderLaw) P := by
    convert hsub' using 1
    funext N
    exact (hId N).symm
  exact two_width_flow_bound_of_lattice_errors P
    (fun η ω => ∫ x, f x * kpzRegularizedReversed P Z 0 1 η 0 x ω)
    E R hconv (hunit δ hδ) (hunit δ' hδ')
    (by dsimp only [R]; positivity) (by dsimp only [R]; positivity)

/-- For a fixed compact smooth test, the explicit smoothing-energy rate
vanishes as the width tends to zero. -/
theorem tendsto_regularization_energy_rhs (C : ℝ) (f : TestFn) :
    Tendsto (fun η : ℝ =>
      Real.sqrt (C * heatEnergy (Real.sqrt η) f / |Real.log η|) +
      C * (∫ x, |f x|) * |Real.log η| ^ (-(1 : ℝ) / 40))
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨B, hB⟩ := f.hasCompactSupport.exists_bound_of_continuous f.continuous
  have hfI : Integrable (f : Plane → ℝ) :=
    f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hfB : ∀ x : Plane, |f x| ≤ B := by
    simpa only [Real.norm_eq_abs] using hB
  have hsqrt : Tendsto (fun η : ℝ => Real.sqrt η) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id :
        Tendsto (fun η : ℝ => η) (𝓝[>] 0) (𝓝 0)).sqrt
  have he : Tendsto (fun η : ℝ => heatEnergy (Real.sqrt η) f) (𝓝[>] 0) (𝓝 0) := by
    have hb : Tendsto (fun η : ℝ => 4 * Real.sqrt η * B * ∫ x, |f x|)
        (𝓝[>] 0) (𝓝 0) := by
      simpa only [mul_zero, zero_mul] using ((hsqrt.const_mul 4).mul_const B).mul_const
        (∫ x, |f x|)
    apply squeeze_zero' ?_ ?_ hb
    · filter_upwards [self_mem_nhdsWithin] with η hη
      exact (heatEnergy_le_of_bounded f f.continuous.measurable hfI B hfB
        (Real.sqrt_pos.2 hη)).1
    · filter_upwards [self_mem_nhdsWithin] with η hη
      exact (heatEnergy_le_of_bounded f f.continuous.measurable hfI B hfB
        (Real.sqrt_pos.2 hη)).2
  have hlog : Tendsto (fun η : ℝ => |Real.log η|) (𝓝[>] 0) atTop :=
    tendsto_abs_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hinv := tendsto_inv_atTop_zero.comp hlog
  have hquot : Tendsto (fun η => C * heatEnergy (Real.sqrt η) f / |Real.log η|)
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero, zero_mul] using
      (he.const_mul C).mul hinv
  have hpow : Tendsto (fun η : ℝ => |Real.log η| ^ (-(1 : ℝ) / 40))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [Function.comp_def, neg_div] using
      (tendsto_rpow_neg_atTop (y := (1 : ℝ) / 40) (by norm_num)).comp hlog
  simpa only [Real.sqrt_zero, mul_zero, add_zero] using
    hquot.sqrt.add (hpow.const_mul (C * ∫ x, |f x|))

/-- Unit-horizon regularisation error with explicit dependence on the test.
The centring disappears for zero-mass tests, exactly as in the UV consumer. -/
theorem kField_sub_lField_eLpNorm_two_le_energy (A : ℝ) :
    ∃ C δ₁ : ℝ, 0 < C ∧ 0 < δ₁ ∧
      ∀ (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
        (P : Measure Ω) [IsProbabilityMeasure P]
        (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
        (hZ : IsCriticalSHF ϑ P Z), ϑ ∈ Set.Icc (-A) A →
      ∀ f : TestFn, (∫ x, f x) = 0 → ∀ δ ∈ Set.Ioo (0 : ℝ) (min δ₁ 1),
        eLpNorm (fun ω => kField ϑ P Z hZ 1 zero_lt_one f ω -
          lField Z δ 1 f ω) 2 P ≤ ENNReal.ofReal
          (Real.sqrt (C * heatEnergy (Real.sqrt δ) f / |Real.log δ|) +
            C * (∫ x, |f x|) * |Real.log δ| ^ (-(1 : ℝ) / 40)) := by
  obtain ⟨C, δ₁, hC, hδ₁, hb⟩ := kpzRegularizedReversed_two_width_energy A
  refine ⟨C, δ₁, hC, hδ₁, ?_⟩
  intro ϑ Ω _ P _ Z hZ hϑ f hf δ hδ
  let X : ℝ → Ω → ℝ := fun η ω => ∫ x, f x * kpzRegularizedReversed P Z 0 1 η 0 x ω
  let R : ℝ → ℝ := fun η =>
    Real.sqrt (C * heatEnergy (Real.sqrt η) f / |Real.log η|) +
      C * (∫ x, |f x|) * |Real.log η| ^ (-(1 : ℝ) / 40)
  have hp : ∀ᶠ η in 𝓝[>] (0 : ℝ),
      eLpNorm (fun ω => X δ ω - X η ω) 2 P ≤ ENNReal.ofReal (R δ + R η) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hδ₁).filter_mono nhdsWithin_le_nhds] with η hη hηsmall
    exact hb ϑ P Z hZ hϑ f δ ⟨hδ.1, hδ.2.trans_le (min_le_left _ _)⟩ η ⟨hη, hηsmall⟩
  have hbound := eLpNorm_sub_limit_le_of_two_width P X
    (kField ϑ P Z hZ 1 zero_lt_one f) R
    (kField_regularized_limit ϑ P Z hZ 1 zero_lt_one f 2 (by norm_num) (by norm_num))
    hp (tendsto_regularization_energy_rhs C f) (by dsimp only [R]; positivity)
  have heq := lField_eq_regularized_ae ϑ P Z hZ 1 hδ.1
    (hδ.2.trans_le (min_le_right _ _)) f hf
  calc
    _ = eLpNorm (fun ω => lField Z δ 1 f ω -
        kField ϑ P Z hZ 1 zero_lt_one f ω) 2 P := eLpNorm_sub_comm _ _ _ _
    _ = eLpNorm (fun ω => X δ ω -
        kField ϑ P Z hZ 1 zero_lt_one f ω) 2 P := by
      apply eLpNorm_congr_ae
      filter_upwards [heq] with ω hω
      rw [hω]
    _ ≤ _ := hbound


/-- The test appearing after scaling a horizon `H` to one. -/
@[expose] noncomputable def horizonScaledTest (H : ℝ) (f : TestFn) : TestFn := f.scale H⁻¹

@[simp] theorem horizonScaledTest_apply {H : ℝ} (hH : 0 < H)
    (f : TestFn) (x : Plane) :
    horizonScaledTest H f x = H * f (Real.sqrt H • x) := by
  change (Real.sqrt H⁻¹)⁻¹ ^ 2 * f ((Real.sqrt H⁻¹)⁻¹ • x) = _
  rw [Real.sqrt_inv, inv_inv, Real.sq_sqrt hH.le]

/-- Horizon scaling preserves the integral of a test. -/
theorem integral_horizonScaledTest {H : ℝ} (hH : 0 < H) (f : TestFn) :
    (∫ x : Plane, horizonScaledTest H f x) = ∫ x : Plane, f x := by
  rw [show (fun x : Plane => horizonScaledTest H f x) =
      fun x => H * f (Real.sqrt H • x) by funext x; rw [horizonScaledTest_apply hH]]
  rw [integral_const_mul, Measure.integral_comp_smul volume]
  have hs : (Real.sqrt H) ^ Module.finrank ℝ Plane = H := by
    simp only [Plane, finrank_euclideanSpace, Fintype.card_fin, Real.sq_sqrt hH.le]
  rw [hs, abs_of_pos (inv_pos.mpr hH), smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ hH.ne', one_mul]

/-- The logarithmic entrance average is pathwise invariant under horizon
scaling.  This is the bridge needed to apply the unit-horizon energy estimate. -/
theorem lField_horizon_scaled
    { Ω : Type*} (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    {H : ℝ} (hH : 0 < H) (a : ℝ) (f : TestFn) (ω : Ω) :
    let Z' := fun s t ω => ENNReal.ofReal H⁻¹ •
      (Z (H * s) (H * t) ω).map
        (fun p => ((Real.sqrt H)⁻¹ • p.1, (Real.sqrt H)⁻¹ • p.2))
    lField Z' (a / H) 1 (horizonScaledTest H f) ω = lField Z a H f ω := by
  dsimp only
  unfold lField
  let F : Plane → ℝ := fun x => f x * Real.log
    (shfPairing Z a H (fun y => heatKernel a (y - x)) (fun _ => 1) ω)
  have hpair (z : Plane) :
      shfPairing (fun s t ω => ENNReal.ofReal H⁻¹ •
        (Z (H * s) (H * t) ω).map
          (fun p => ((Real.sqrt H)⁻¹ • p.1, (Real.sqrt H)⁻¹ • p.2)))
        (a / H) 1 (fun y => heatKernel (a / H) (y - z)) (fun _ => 1) ω =
      shfPairing Z a H
        (fun y => heatKernel a (y - Real.sqrt H • z)) (fun _ => 1) ω := by
    have h := shfPairing_scaled_eq Z hH a H (Real.sqrt H • z) ω
    have hone : H / H = 1 := div_self hH.ne'
    have hcancel : (Real.sqrt H)⁻¹ • (Real.sqrt H • z) = z := by
      rw [← mul_smul, inv_mul_cancel₀ (Real.sqrt_pos.2 hH).ne', one_smul]
    simpa only [hone, hcancel] using h
  rw [show (fun z : Plane => horizonScaledTest H f z * Real.log
      (shfPairing (fun s t ω => ENNReal.ofReal H⁻¹ •
        (Z (H * s) (H * t) ω).map
          (fun p => ((Real.sqrt H)⁻¹ • p.1, (Real.sqrt H)⁻¹ • p.2)))
        (a / H) 1 (fun y => heatKernel (a / H) (y - z)) (fun _ => 1) ω)) =
      fun z => H * F (Real.sqrt H • z) by
        funext z
        rw [horizonScaledTest_apply hH, hpair]
        exact mul_assoc _ _ _,
      integral_const_mul, Measure.integral_comp_smul volume]
  have hs : (Real.sqrt H) ^ Module.finrank ℝ Plane = H := by
    simp only [Plane, finrank_euclideanSpace, Fintype.card_fin, Real.sq_sqrt hH.le]
  rw [hs, abs_of_pos (inv_pos.mpr hH), smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ hH.ne', one_mul]


theorem kField_horizon_scaled_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {c l : ℝ} (hc : 0 < c)
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF (-l) P Z) (f : TestFn) (hfzero : (∫ x, f x) = 0) :
    let H := c * Real.exp l
    let Z' := fun s t ω => ENNReal.ofReal H⁻¹ •
      (Z (H * s) (H * t) ω).map
        (fun p => ((Real.sqrt H)⁻¹ • p.1, (Real.sqrt H)⁻¹ • p.2))
    kField (Real.log c) P Z'
      (isCriticalSHF_profile_horizon_scaled P hc Z hZ) 1 (by norm_num)
      (horizonScaledTest H f) =ᵐ[P]
    kField (-l) P Z hZ H (mul_pos hc (Real.exp_pos l)) f := by
  dsimp only
  let H : ℝ := c * Real.exp l
  let Z' := fun s t ω => ENNReal.ofReal H⁻¹ •
    (Z (H * s) (H * t) ω).map
      (fun p => ((Real.sqrt H)⁻¹ • p.1, (Real.sqrt H)⁻¹ • p.2))
  have hH : 0 < H := mul_pos hc (Real.exp_pos l)
  have hZ' : IsCriticalSHF (Real.log c) P Z' :=
    isCriticalSHF_profile_horizon_scaled P hc Z hZ
  have hfzero' : (∫ x, horizonScaledTest H f x) = 0 := by
    rw [integral_horizonScaledTest hH f, hfzero]
  let K' := kField (Real.log c) P Z' hZ' 1 (by norm_num)
    (horizonScaledTest H f)
  let K := kField (-l) P Z hZ H hH f
  let Y : ℝ → Ω → ℝ := fun η => lField Z (H * η) H f
  have hmul : Tendsto (fun η : ℝ => H * η) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hi : Tendsto (fun η : ℝ => η) (𝓝[>] 0) (𝓝 0) :=
        tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
      simpa only [mul_zero] using hi.const_mul H
    · filter_upwards [self_mem_nhdsWithin] with η hη
      exact mul_pos hH hη
  have hlimK : Tendsto
      (fun η : ℝ => eLpNorm (fun ω => Y η ω - K ω) 2 P)
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [Y, K, Function.comp_def] using
      (kField_l2_limit (-l) P Z hZ H hH f hfzero).comp hmul
  have hlimK' : Tendsto
      (fun η : ℝ => eLpNorm (fun ω => Y η ω - K' ω) 2 P)
      (𝓝[>] 0) (𝓝 0) := by
    have hu := kField_l2_limit (Real.log c) P Z' hZ' 1 (by norm_num)
      (horizonScaledTest H f) hfzero'
    apply hu.congr'
    filter_upwards [self_mem_nhdsWithin] with η hη
    apply eLpNorm_congr_ae
    filter_upwards [] with ω
    have hscale := lField_horizon_scaled Z hH (H * η) f ω
    have hcancel : H * η / H = η := by field_simp
    rw [hcancel] at hscale
    simpa only [Y, K', Z'] using congrArg (fun z : ℝ => z - K' ω) hscale
  have hsum : Tendsto
      (fun η : ℝ =>
        eLpNorm (fun ω => Y η ω - K ω) 2 P +
          eLpNorm (fun ω => Y η ω - K' ω) 2 P)
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_add] using hlimK.add hlimK'
  have hbound : ∀ᶠ η : ℝ in 𝓝[>] 0,
      eLpNorm (fun ω => K ω - K' ω) 2 P ≤
        eLpNorm (fun ω => Y η ω - K ω) 2 P +
          eLpNorm (fun ω => Y η ω - K' ω) 2 P := by
    filter_upwards [] with η
    calc
      eLpNorm (fun ω => K ω - K' ω) 2 P ≤
          eLpNorm (fun ω => K ω - Y η ω) 2 P +
            eLpNorm (fun ω => Y η ω - K' ω) 2 P :=
        by
          calc
            _ = eLpNorm (fun ω => (K ω - Y η ω) + (Y η ω - K' ω)) 2 P := by
              apply eLpNorm_congr_ae
              filter_upwards [] with ω
              ring
            _ ≤ _ := eLpNorm_add_le (by norm_num)
      _ = eLpNorm (fun ω => Y η ω - K ω) 2 P +
            eLpNorm (fun ω => Y η ω - K' ω) 2 P := by
        rw [show eLpNorm (fun ω => K ω - Y η ω) 2 P =
          eLpNorm (fun ω => Y η ω - K ω) 2 P from eLpNorm_sub_comm _ _ _ _]
  have hconst : Tendsto
      (fun _ : ℝ => eLpNorm (fun ω => K ω - K' ω) 2 P)
      (𝓝[>] 0) (𝓝 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Filter.Eventually.of_forall fun _ => bot_le) hbound
  have hzero : eLpNorm (fun ω => K ω - K' ω) 2 P = 0 := by
    exact (tendsto_nhds_unique hconst tendsto_const_nhds).symm
  have hK : MemLp K 2 P := by
    simpa only [K] using kField_memLp (-l) P Z hZ H hH f 2 (by norm_num) (by norm_num)
  have hK' : MemLp K' 2 P := by
    simpa only [K'] using kField_memLp (Real.log c) P Z' hZ' 1 (by norm_num)
      (horizonScaledTest H f) 2 (by norm_num) (by norm_num)
  have _hstrong : AEStronglyMeasurable (fun ω => K ω - K' ω) P :=
    (hK.sub hK').aestronglyMeasurable
  have hae := (eLpNorm_eq_zero_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0)).mp hzero
  filter_upwards [hae] with ω hω
  exact (sub_eq_zero.mp hω).symm

/-- Horizon dilation preserves the L¹ norm of the test. -/
theorem integral_abs_horizonScaledTest (f : TestFn) {H : ℝ} (hH : 0 < H) :
    (∫ z : Plane, |H * f (Real.sqrt H • z)|) = ∫ x : Plane, |f x| := by
  exact Smoothing.integral_abs_dilate_eq (f : Plane → ℝ)
    (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport) hH

/-- Simultaneously dilating the test and the heat scale changes the energy
horizon from `sqrt (a/H)` to `sqrt (aH)`. -/
theorem heatEnergy_horizonScaledTest (f : TestFn) (B : ℝ)
    (hB : ∀ x, |f x| ≤ B) {a H : ℝ} (ha : 0 < a) (hH : 0 < H) :
    Smoothing.heatEnergy (Real.sqrt (a / H))
      (fun z : Plane => H * f (Real.sqrt H • z)) =
        Smoothing.heatEnergy (Real.sqrt (a * H)) f := by
  rw [Smoothing.heatEnergy_dilate_eq (f : Plane → ℝ)
    f.continuous.measurable
    (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)
    B hB hH (Real.sqrt_pos.2 (div_pos ha hH))]
  congr 1
  have hleft : 0 ≤ H * Real.sqrt (a / H) := by positivity
  have hright : 0 ≤ Real.sqrt (a * H) := Real.sqrt_nonneg _
  have hsq : (H * Real.sqrt (a / H)) ^ 2 = (Real.sqrt (a * H)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (div_nonneg ha.le hH.le),
      Real.sq_sqrt (mul_nonneg ha.le hH.le)]
    field_simp [hH.ne']
  nlinarith


/-- The square-root energy scale at the rounded fine entrance is negligible
after multiplication by the ultraviolet parameter. -/
theorem uvFineEntrance_sqrt_horizon_rate_tendsto
    {c ρ : ℝ} (hc : 0 < c) (hρ : 1 < ρ) :
    Tendsto (fun l : ℝ => l * Real.sqrt
      (uvFineEntrance c ρ l * (c * Real.exp l))) atTop (𝓝 0) := by
  have href : Tendsto (fun l : ℝ => Real.sqrt c * (l ^ 1 * Real.exp (-l)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul (Real.sqrt c)
  apply squeeze_zero' ?_ ?_ href
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with l hl
    exact mul_nonneg hl (Real.sqrt_nonneg _)
  · filter_upwards [uv_targets_fit hc, eventually_ge_atTop (3 : ℝ)] with l hfit hl
    have hl0 : 0 ≤ l := by linarith
    have ha := (uvFineEntrance_bounds hc hρ hfit.2.1).2
    have hprod : uvFineEntrance c ρ l * (c * Real.exp l) ≤
        c * Real.exp (-2 * l) := by
      have hpow : 3 * l ≤ l ^ 40 := by
        have hsq : 3 * l ≤ l ^ 2 := by nlinarith
        exact hsq.trans (pow_le_pow_right₀ (by linarith : 1 ≤ l) (by norm_num : 2 ≤ 40))
      calc
        uvFineEntrance c ρ l * (c * Real.exp l) ≤
            Real.exp (-(l ^ 40)) * (c * Real.exp l) :=
          mul_le_mul_of_nonneg_right ha (by positivity)
        _ = c * Real.exp (l - l ^ 40) := by
          rw [show l - l ^ 40 = l + -(l ^ 40) by ring, Real.exp_add]
          ring
        _ ≤ c * Real.exp (-2 * l) := by
          gcongr
          linarith
    have hsqrt := Real.sqrt_le_sqrt hprod
    have hsqrtR : Real.sqrt (c * Real.exp (-2 * l)) =
        Real.sqrt c * Real.exp (-l) := by
      rw [Real.sqrt_mul hc.le,
        show Real.exp (-2 * l) = (Real.exp (-l)) ^ 2 by
          rw [pow_two, ← Real.exp_add]
          congr 1
          ring,
        Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [hsqrtR] at hsqrt
    calc
      l * Real.sqrt (uvFineEntrance c ρ l * (c * Real.exp l)) ≤
          l * (Real.sqrt c * Real.exp (-l)) :=
        mul_le_mul_of_nonneg_left hsqrt hl0
      _ = Real.sqrt c * (l ^ 1 * Real.exp (-l)) := by ring

/-- The fine-entrance regularization squared-error budget tends to zero. -/
theorem uvFineEntrance_regularization_budget_tendsto
    {c ρ : ℝ} (hc : 0 < c) (hρ : 1 < ρ) :
    Tendsto (fun l : ℝ => l *
      (Real.sqrt (uvFineEntrance c ρ l * (c * Real.exp l)) +
        (Real.log ((c * Real.exp l) / uvFineEntrance c ρ l)) ^
          (-(1 : ℝ) / 20))) atTop (𝓝 0) := by
  have hfirst := uvFineEntrance_sqrt_horizon_rate_tendsto hc hρ
  have hsecond := uvFineEntrance_rate_tendsto hc hρ
  simpa only [mul_add, add_zero] using hfirst.add hsecond

/-- The unit-horizon estimate transported back to the original horizon.  The
constant is uniform in `l` and in the critical flow; its only scale parameter
is the fixed prefactor `c`. -/
theorem kField_sub_lField_eLpNorm_two_le_energy_horizon
    (c : ℝ) (hc : 0 < c) :
    ∃ C δ₁ : ℝ, 0 < C ∧ 0 < δ₁ ∧
      ∀ (l : ℝ) {Ω : Type*} [MeasurableSpace Ω]
        (P : Measure Ω) [IsProbabilityMeasure P]
        (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
        (hZ : IsCriticalSHF (-l) P Z) (f : TestFn),
        (∫ x, f x) = 0 → ∀ a : ℝ, 0 < a →
        a / (c * Real.exp l) ∈ Set.Ioo (0 : ℝ) (min δ₁ 1) →
        eLpNorm (fun ω =>
          kField (-l) P Z hZ (c * Real.exp l)
              (mul_pos hc (Real.exp_pos l)) f ω -
            lField Z a (c * Real.exp l) f ω) 2 P ≤
          ENNReal.ofReal
            (Real.sqrt (C * Smoothing.heatEnergy
                (Real.sqrt (a * (c * Real.exp l))) f /
                  |Real.log (a / (c * Real.exp l))|) +
              C * (∫ x, |f x|) *
                |Real.log (a / (c * Real.exp l))| ^ (-(1 : ℝ) / 40)) := by
  obtain ⟨C, δ₁, hC, hδ₁, hunit⟩ :=
    kField_sub_lField_eLpNorm_two_le_energy |Real.log c|
  refine ⟨C, δ₁, hC, hδ₁, ?_⟩
  intro l Ω _ P _ Z hZ f hf a ha hratio
  let H : ℝ := c * Real.exp l
  let Z' : ℝ → ℝ → Ω → Measure (Plane × Plane) := fun s t ω =>
    ENNReal.ofReal H⁻¹ • (Z (H * s) (H * t) ω).map
      (fun p => ((Real.sqrt H)⁻¹ • p.1, (Real.sqrt H)⁻¹ • p.2))
  have hH : 0 < H := mul_pos hc (Real.exp_pos l)
  have hZ' : IsCriticalSHF (Real.log c) P Z' := by
    simpa only [H, Z'] using isCriticalSHF_profile_horizon_scaled P hc Z hZ
  have hparam : Real.log c ∈ Set.Icc (-|Real.log c|) |Real.log c| :=
    (abs_le.mp le_rfl)
  have hf' : (∫ x, horizonScaledTest H f x) = 0 := by
    rw [integral_horizonScaledTest hH f, hf]
  have hu := hunit (Real.log c) P Z' hZ' hparam
    (horizonScaledTest H f) hf' (a / H) (by simpa only [H] using hratio)
  have hK := kField_horizon_scaled_ae P hc Z hZ f hf
  have hL : lField Z' (a / H) 1 (horizonScaledTest H f) =ᵐ[P]
      lField Z a H f := by
    filter_upwards [] with ω
    exact lField_horizon_scaled Z hH a f ω
  have heq : (fun ω =>
      kField (Real.log c) P Z' hZ' 1 zero_lt_one
          (horizonScaledTest H f) ω -
        lField Z' (a / H) 1 (horizonScaledTest H f) ω) =ᵐ[P]
      fun ω => kField (-l) P Z hZ H hH f ω - lField Z a H f ω := by
    filter_upwards [hK, hL] with ω hKω hLω
    rw [hKω, hLω]
  rw [eLpNorm_congr_ae heq] at hu
  obtain ⟨B, hB⟩ := f.hasCompactSupport.exists_bound_of_continuous f.continuous
  have hfbd : ∀ x : Plane, |f x| ≤ B := by
    simpa only [Real.norm_eq_abs] using hB
  have henergy : heatEnergy (Real.sqrt (a / H)) (horizonScaledTest H f) =
      heatEnergy (Real.sqrt (a * H)) f := by
    rw [show (horizonScaledTest H f : Plane → ℝ) =
      fun x => H * f (Real.sqrt H • x) by
        funext x
        exact horizonScaledTest_apply hH f x]
    exact heatEnergy_horizonScaledTest f B hfbd ha hH
  have hmass : (∫ x, |horizonScaledTest H f x|) = ∫ x, |f x| := by
    rw [show (fun x : Plane => |horizonScaledTest H f x|) =
      fun x => |H * f (Real.sqrt H • x)| by
        funext x; rw [horizonScaledTest_apply hH]]
    exact integral_abs_horizonScaledTest f hH
  rw [henergy, hmass] at hu
  simpa only [H] using hu


/-- The deterministic squared right-hand side of the transported estimate is
negligible at the rounded fine entrance. -/
theorem tendsto_fine_horizon_energy_rhs_sq
    (c ρ C B M : ℝ) (hc : 0 < c) (hρ : 1 < ρ)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hM : 0 ≤ M) :
    Tendsto (fun l : ℝ => l *
      (Real.sqrt (C *
          (4 * Real.sqrt (uvFineEntrance c ρ l * (c * Real.exp l)) * B * M) /
          |Real.log (uvFineEntrance c ρ l / (c * Real.exp l))|) +
        C * M * |Real.log (uvFineEntrance c ρ l / (c * Real.exp l))| ^
          (-(1 : ℝ) / 40)) ^ 2) atTop (𝓝 0) := by
  let d : ℝ → ℝ := fun l =>
    Real.log ((c * Real.exp l) / uvFineEntrance c ρ l)
  have hd := uvFineEntrance_regularization_budget_tendsto hc hρ
  have hclock := uvFineEntrance_clock hc hρ
  have hdom : ∀ᶠ l : ℝ in atTop,
      0 ≤ l *
        (Real.sqrt (C * (4 * Real.sqrt (uvFineEntrance c ρ l *
          (c * Real.exp l)) * B * M) /
          |Real.log (uvFineEntrance c ρ l / (c * Real.exp l))|) +
        C * M * |Real.log (uvFineEntrance c ρ l / (c * Real.exp l))| ^
          (-(1 : ℝ) / 40)) ^ 2 ∧
      l *
        (Real.sqrt (C * (4 * Real.sqrt (uvFineEntrance c ρ l *
          (c * Real.exp l)) * B * M) /
          |Real.log (uvFineEntrance c ρ l / (c * Real.exp l))|) +
        C * M * |Real.log (uvFineEntrance c ρ l / (c * Real.exp l))| ^
          (-(1 : ℝ) / 40)) ^ 2 ≤
        (2 * (4 * C * B * M + (C * M) ^ 2)) *
          (l * (Real.sqrt (uvFineEntrance c ρ l * (c * Real.exp l)) +
            d l ^ (-(1 : ℝ) / 20))) := by
    filter_upwards [hclock, eventually_ge_atTop (1 : ℝ), uv_targets_fit hc]
      with l hdl hl hfit
    have ha : 0 < uvFineEntrance c ρ l :=
      uvGridPoint_pos (mul_pos hc (Real.exp_pos _)) (zero_lt_one.trans hρ)
    have hH : 0 < c * Real.exp l := mul_pos hc (Real.exp_pos _)
    have hlogeq : |Real.log (uvFineEntrance c ρ l / (c * Real.exp l))| = d l := by
      dsimp [d]
      rw [Real.log_div ha.ne' hH.ne', Real.log_div hH.ne' ha.ne']
      rw [abs_of_nonpos]
      · ring
      · have hh := hdl
        rw [Real.log_div hH.ne' ha.ne'] at hh
        linarith only [hh, pow_nonneg (zero_le_one.trans hl) 40]
    rw [hlogeq]
    have hd1 : 1 ≤ d l := (one_le_pow₀ hl).trans hdl
    constructor
    · positivity
    · have hsqrtdiv :
          Real.sqrt (C * (4 * Real.sqrt (uvFineEntrance c ρ l *
            (c * Real.exp l)) * B * M) / d l) ^ 2 ≤
            4 * C * B * M * Real.sqrt
              (uvFineEntrance c ρ l * (c * Real.exp l)) := by
          rw [Real.sq_sqrt (by positivity)]
          apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hd1)).2
          have hm : 0 ≤ 4 * C * B * M * Real.sqrt
              (uvFineEntrance c ρ l * (c * Real.exp l)) := by positivity
          convert le_mul_of_one_le_right hm hd1 using 1; ring
      have htail : (C * M * (d l) ^ (-(1 : ℝ) / 40)) ^ 2 =
          (C * M) ^ 2 * (d l) ^ (-(1 : ℝ) / 20) := by
        rw [mul_pow]
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ d l)]
        norm_num
      have hab :
          (Real.sqrt (C * (4 * Real.sqrt (uvFineEntrance c ρ l *
            (c * Real.exp l)) * B * M) / d l) +
            C * M * (d l) ^ (-(1 : ℝ) / 40)) ^ 2 ≤
          2 * (Real.sqrt (C * (4 * Real.sqrt (uvFineEntrance c ρ l *
            (c * Real.exp l)) * B * M) / d l) ^ 2 +
            (C * M * (d l) ^ (-(1 : ℝ) / 40)) ^ 2) := by
        nlinarith [sq_nonneg (Real.sqrt (C * (4 * Real.sqrt
          (uvFineEntrance c ρ l * (c * Real.exp l)) * B * M) / d l) -
            C * M * (d l) ^ (-(1 : ℝ) / 40))]
      rw [htail] at hab
      have hsmall := hab.trans (mul_le_mul_of_nonneg_left
        (add_le_add hsqrtdiv le_rfl) (by norm_num : (0 : ℝ) ≤ 2))
      have hscalar (a b t u : ℝ) (hh : 0 ≤ a * u + b * t) :
          2 * (a * t + b * u) ≤ (2 * (a + b)) * (t + u) := by
        nlinarith only [hh]
      have hc := hscalar (4 * C * B * M) ((C * M) ^ 2)
        (Real.sqrt (uvFineEntrance c ρ l * (c * Real.exp l)))
        (d l ^ (-(1 : ℝ) / 20)) (by positivity)
      have hm := mul_le_mul_of_nonneg_left (hsmall.trans hc) (zero_le_one.trans hl)
      convert hm using 1; ring
  apply squeeze_zero' (hdom.mono fun _ h => h.1) (hdom.mono fun _ h => h.2)
  simpa only [d, mul_zero] using
    hd.const_mul (2 * (4 * C * B * M + (C * M) ^ 2))

/-- The full-horizon fine-entrance approximation is negligible in rescaled
second moment. This is Step 1 before the separate localisation to `S`. -/
theorem fine_entrance_fullHorizon_second_moment_tendsto
    {c ρ : ℝ} (hc : 0 < c) (hρ : 1 < ρ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : ∀ l, IsCriticalSHF (-l) P (Z l))
    (f : TestFn) (hf : (∫ x, f x) = 0) :
    Tendsto (fun l => l * ∫ ω,
      (kField (-l) P (Z l) (hZ l) (c * Real.exp l)
          (mul_pos hc (Real.exp_pos l)) f ω -
        lField (Z l) (uvFineEntrance c ρ l) (c * Real.exp l) f ω) ^ 2 ∂P)
      atTop (𝓝 0) := by
  obtain ⟨C, δ₁, hC, hδ₁, hbound⟩ :=
    kField_sub_lField_eLpNorm_two_le_energy_horizon c hc
  obtain ⟨B, hB⟩ := f.hasCompactSupport.exists_bound_of_continuous f.continuous
  have hfbd : ∀ x : Plane, |f x| ≤ B := by
    simpa only [Real.norm_eq_abs] using hB
  have hB0 : 0 ≤ B := (abs_nonneg (f 0)).trans (hfbd 0)
  let M : ℝ := ∫ x : Plane, |f x|
  have hM0 : 0 ≤ M := integral_nonneg fun _ => abs_nonneg _
  let R : ℝ → ℝ := fun l =>
    Real.sqrt (C * (4 * Real.sqrt (uvFineEntrance c ρ l * (c * Real.exp l)) * B * M) /
      |Real.log (uvFineEntrance c ρ l / (c * Real.exp l))|) +
    C * M * |Real.log (uvFineEntrance c ρ l / (c * Real.exp l))| ^ (-(1 : ℝ) / 40)
  have hR : Tendsto (fun l => l * (R l) ^ 2) atTop (𝓝 0) :=
    tendsto_fine_horizon_energy_rhs_sq c ρ C B M hc hρ hC.le hB0 hM0
  have hH : Tendsto (fun l : ℝ => c * Real.exp l) atTop atTop :=
    Real.tendsto_exp_atTop.const_mul_atTop hc
  have hratio : Tendsto (fun l => uvFineEntrance c ρ l / (c * Real.exp l))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using
      (uvFineEntrance_tendsto_zero hc hρ).mul (tendsto_inv_atTop_zero.comp hH)
  apply squeeze_zero' (g := fun l => l * (R l) ^ 2) ?_ ?_ hR
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with l hl
    exact mul_nonneg hl (integral_nonneg fun _ => sq_nonneg _)
  · filter_upwards [eventually_ge_atTop (0 : ℝ),
      hratio.eventually (gt_mem_nhds (lt_min hδ₁ zero_lt_one))] with l hl hsmall
    have ha : 0 < uvFineEntrance c ρ l :=
      uvGridPoint_pos (mul_pos hc (Real.exp_pos _)) (zero_lt_one.trans hρ)
    have hHH : 0 < c * Real.exp l := mul_pos hc (Real.exp_pos l)
    have hb := hbound l P (Z l) (hZ l) f hf (uvFineEntrance c ρ l) ha
      ⟨div_pos ha hHH, hsmall⟩
    have hE := (heatEnergy_le_of_bounded f f.continuous.measurable
      (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport) B hfbd
      (Real.sqrt_pos.2 (mul_pos ha hHH))).2
    have hbR : eLpNorm (fun ω =>
        kField (-l) P (Z l) (hZ l) (c * Real.exp l)
            (mul_pos hc (Real.exp_pos l)) f ω -
          lField (Z l) (uvFineEntrance c ρ l) (c * Real.exp l) f ω) 2 P ≤
        ENNReal.ofReal (R l) := by
      apply hb.trans
      apply ENNReal.ofReal_le_ofReal
      apply add_le_add _ le_rfl
      apply Real.sqrt_le_sqrt
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hE hC.le) (abs_nonneg _)
    have hm : MemLp (fun ω =>
        kField (-l) P (Z l) (hZ l) (c * Real.exp l)
            (mul_pos hc (Real.exp_pos l)) f ω -
          lField (Z l) (uvFineEntrance c ρ l) (c * Real.exp l) f ω) 2 P :=
      hbR.trans_lt ENNReal.ofReal_lt_top
    exact mul_le_mul_of_nonneg_left
      (profile_integral_sq_le_of_eLpNorm_two hm
        (by dsimp only [R]; positivity) hbR) hl

theorem uvFineEntrance_eq_gridEntrance_of_le
    {c ρ l : ℝ} (_hρ : 1 < ρ)
    (hidx : gridIndex c ρ l ≤
      uvGridIndex (c * Real.exp l) ρ (Real.exp (-(l ^ 40)))) :
    uvFineEntrance c ρ l = gridEntrance c ρ l
      (uvGridIndex (c * Real.exp l) ρ (Real.exp (-(l ^ 40))) - gridIndex c ρ l) := by
  rw [uvFineEntrance, uvGridPoint, gridEntrance, gridPoint]
  rw [div_div, ← pow_add, Nat.add_sub_of_le hidx]

theorem eventually_uvFineEntrance_eq_gridEntrance
    {c ρ : ℝ} (hc : 0 < c) (hρ : 1 < ρ) :
    ∀ᶠ l : ℝ in atTop, ∃ j : ℕ,
      uvFineEntrance c ρ l = gridEntrance c ρ l j := by
  filter_upwards [uv_targets_fit hc, eventually_gt_atTop (1 : ℝ),
    (Real.tendsto_exp_atTop.const_mul_atTop hc).eventually_ge_atTop 0,
    eventually_grid_time_order hc hρ (show (0:ℝ)<1/4 by norm_num) (by norm_num)] with l hfit hl _ htimes
  have hgp := htimes.2.2.2
  have hf := (uvFineEntrance_bounds hc hρ hfit.2.1).2
  have hfg : uvFineEntrance c ρ l < gridPoint c ρ l := by
    have he : Real.exp (-(l ^ 40)) < l ^ 2 := by
      have he1 : Real.exp (-(l ^ 40)) < 1 :=
        Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (pow_pos (zero_lt_one.trans hl) _))
      have hl2 : 1 < l ^ 2 := by nlinarith
      exact he1.trans hl2
    exact hf.trans_lt (he.trans_le hgp)
  let H := c * Real.exp l
  let ka := uvGridIndex H ρ (Real.exp (-(l ^ 40)))
  let kg := gridIndex c ρ l
  have hH : 0 < H := mul_pos hc (Real.exp_pos l)
  have hidx : kg < ka := by
    apply index_lt_of_div_pow_lt hH hρ
    simpa only [H, ka, kg, uvFineEntrance, uvGridPoint, gridPoint] using hfg
  exact ⟨ka - kg, uvFineEntrance_eq_gridEntrance_of_le hρ hidx.le⟩

/- Auxiliary lemmas and the final Step-One-S assembly candidate. -/

theorem tendstoInMeasure_zero_of_integral_sq_eventually
    {ι Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {u : Filter ι} {X : ι → Ω → ℝ}
    (hX : ∀ᶠ i in u, MemLp (X i) 2 P)
    (h2 : Tendsto (fun i => ∫ ω, X i ω ^ 2 ∂P) u (𝓝 0)) :
    TendstoInMeasure P X u (fun _ => 0) := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  have hlim : Tendsto (fun i => (∫ ω, X i ω ^ 2 ∂P) / ε ^ 2) u (𝓝 0) := by
    simpa only [zero_div] using h2.div_const (ε ^ 2)
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _ hlim
  filter_upwards [hX] with i hi
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun ω => sq_nonneg (X i ω)))
    ((memLp_two_iff_integrable_sq hi.aestronglyMeasurable).mp hi) (ε ^ 2)
  have hsub : {ω | ε ≤ ‖X i ω - 0‖} ⊆ {ω | ε ^ 2 ≤ X i ω ^ 2} := by
    intro ω hω
    have hh : ε ≤ |X i ω| := by
      simpa only [Set.mem_ofPred_eq, sub_zero, Real.norm_eq_abs] using hω
    simpa only [Set.mem_ofPred_eq, sq_abs] using pow_le_pow_left₀ hε.le hh 2
  exact (measureReal_mono hsub).trans ((le_div_iff₀ (sq_pos_of_pos hε)).mpr
    (by simpa only [mul_comm] using hmarkov))

theorem tendstoInMeasure_add_zero_real
    {ι Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {u : Filter ι}
    {X Y : ι → Ω → ℝ}
    (hX : TendstoInMeasure P X u (fun _ => 0))
    (hY : TendstoInMeasure P Y u (fun _ => 0)) :
    TendstoInMeasure P (fun i ω => X i ω + Y i ω) u (fun _ => 0) := by
  rw [tendstoInMeasure_iff_measureReal_norm] at hX hY ⊢
  intro ε hε
  have hx := hX (ε / 2) (half_pos hε)
  have hy := hY (ε / 2) (half_pos hε)
  have hs : Tendsto (fun i =>
      P.real {ω | ε / 2 ≤ ‖X i ω - 0‖} +
      P.real {ω | ε / 2 ≤ ‖Y i ω - 0‖}) u (𝓝 0) := by
    simpa only [zero_add] using hx.add hy
  apply squeeze_zero (fun _ => measureReal_nonneg) _ hs
  intro i
  have hsub : {ω | ε ≤ ‖X i ω + Y i ω - 0‖} ⊆
      {ω | ε / 2 ≤ ‖X i ω - 0‖} ∪ {ω | ε / 2 ≤ ‖Y i ω - 0‖} := by
    intro ω hω
    by_contra hn
    have hx' : ‖X i ω‖ < ε / 2 := by simpa using fun h => hn (Or.inl h)
    have hy' : ‖Y i ω‖ < ε / 2 := by simpa using fun h => hn (Or.inr h)
    have ht := norm_add_le (X i ω) (Y i ω)
    simp only [Set.mem_ofPred_eq, sub_zero] at hω
    linarith
  exact (measureReal_mono hsub).trans (measureReal_union_le _ _)

/-- Fine-entrance approximation and localisation use one common choice of
horizon parameters, selected before the test function. -/
theorem stepOne_fine_entrance_and_localisation {c : ℝ} (hc : 0 < c) :
    ∃ ρ₀ q : ℝ, 1 < ρ₀ ∧ 0 < q ∧ q < 1 / 2 ∧ ∀ (ρ : ℝ) (_hρle : ρ₀ ≤ ρ) (hρ : 1 < ρ),
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (Z : ℝ → ℝ → ℝ → Ω → Measure (Plane × Plane))
      (hZ : ∀ l, IsCriticalSHF (-l) P (Z l))
      (f : TestFn) (_hfzero : (∫ x, f x) = 0),
      TendstoInMeasure P (fun l ω => Real.sqrt l *
        (kField (-l) P (Z l) (hZ l) (c * Real.exp l)
            (mul_pos hc (Real.exp_pos l)) f ω -
          kField (-l) P (Z l) (hZ l) (S c ρ q l)
            (gridHorizon_pos hc (zero_lt_one.trans hρ) q l) f ω))
        atTop (fun _ => 0) ∧
      TendstoInMeasure P (fun l ω => Real.sqrt l *
        (kField (-l) P (Z l) (hZ l) (S c ρ q l)
            (gridHorizon_pos hc (zero_lt_one.trans (hρ)) q l) f ω -
          lField (Z l) (uvFineEntrance c ρ l) (S c ρ q l) f ω))
        atTop (fun _ => 0) := by
  obtain ⟨ρ₀, q, hρ₀, hq0, hqHalf, hUniform⟩ := localisation_uniform_entrance hc
  refine ⟨ρ₀, q, hρ₀, hq0, hqHalf, ?_⟩
  intro ρ hρle hρ Ω _ P _ Z hZ f hfzero
  let H : ℝ → ℝ := fun l => c * Real.exp l
  let a : ℝ → ℝ := uvFineEntrance c ρ
  let T : ℝ → ℝ := S c ρ q
  let KH : ℝ → Ω → ℝ := fun l =>
    kField (-l) P (Z l) (hZ l) (H l) (mul_pos hc (Real.exp_pos l)) f
  let KS : ℝ → Ω → ℝ := fun l =>
    kField (-l) P (Z l) (hZ l) (T l)
      (gridHorizon_pos hc (zero_lt_one.trans hρ) q l) f
  let LH : ℝ → Ω → ℝ := fun l => lField (Z l) (a l) (H l) f
  let LS : ℝ → Ω → ℝ := fun l => lField (Z l) (a l) (T l) f
  obtain ⟨R, hR, hSupport⟩ := f.hasCompactSupport.isCompact.isBounded.exists_pos_norm_lt
  have hsupp : ∀ x, f x ≠ 0 → ∀ i : Fin 2, |x i| ≤ R := by
    intro x hx i
    have hi : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i
    exact hi.trans (hSupport x (subset_tsupport f hx)).le
  have hKloc : TendstoInMeasure P (fun l ω => Real.sqrt l * (KH l ω - KS l ω))
      atTop (fun _ => 0) := by
    rw [tendstoInMeasure_iff_norm]
    intro ε hε
    have hU := hUniform ρ hρle P Z hZ f f.continuous.measurable
      (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)
      (integrable_firstMoment_testFn f) hfzero R hR.le hsupp
      (ε / 4) (by linarith)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU
      (Eventually.of_forall fun _ => zero_le)
    filter_upwards [eventually_grid_time_order hc hρ hq0 hqHalf] with l ht
    have hg := profile_gridEntrance_tendsto_zero hρ ht.1
    have hF := (kField_l2_limit (-l) P (Z l) (hZ l) (H l)
      (mul_pos hc (Real.exp_pos l)) f hfzero).comp hg
    have hG := (kField_l2_limit (-l) P (Z l) (hZ l) (T l)
      (gridHorizon_pos hc (zero_lt_one.trans hρ) q l) f hfzero).comp hg
    have htail := profile_limit_tail_le_iSup P
      (profile_scaled_difference_tendstoInMeasure P (Real.sqrt l) hF hG) (half_pos hε)
    have hsub : {ω | ε ≤ ‖Real.sqrt l * (KH l ω - KS l ω) - 0‖} ⊆
        {ω | ε / 2 < |Real.sqrt l * (KH l ω - KS l ω)|} := by
      intro ω hw
      simp only [Set.mem_ofPred_eq, sub_zero, Real.norm_eq_abs] at hw ⊢
      linarith
    apply (measure_mono hsub).trans
    convert htail using 1
    congr 1
    funext j
    congr 1
    ext ω
    simp only [Set.mem_ofPred_eq, H, T, lField, profileLogPairing]
    rw [show ε / 2 / 2 = ε / 4 by ring, abs_mul,
      abs_of_nonneg (Real.sqrt_nonneg _)]
  have hFineMoment := fine_entrance_fullHorizon_second_moment_tendsto
    hc hρ P Z hZ f hfzero
  have hFineMem : ∀ᶠ l : ℝ in atTop,
      MemLp (fun ω => Real.sqrt l * (KH l ω - LH l ω)) 2 P := by
    obtain ⟨C, δ, _, hδ, hb⟩ := kField_sub_lField_eLpNorm_two_le_energy_horizon c hc
    have hHtop : Tendsto H atTop atTop := Real.tendsto_exp_atTop.const_mul_atTop hc
    have hr : Tendsto (fun l => a l / H l) atTop (𝓝 0) := by
      simpa only [a, Function.comp_def, div_eq_mul_inv, mul_zero] using
        (uvFineEntrance_tendsto_zero hc hρ).mul (tendsto_inv_atTop_zero.comp hHtop)
    filter_upwards [hr.eventually (gt_mem_nhds (lt_min hδ zero_lt_one))] with l hl
    have ha : 0 < a l := uvGridPoint_pos (mul_pos hc (Real.exp_pos l)) (zero_lt_one.trans hρ)
    have he := hb l P (Z l) (hZ l) f hfzero (a l) ha
      ⟨div_pos ha (mul_pos hc (Real.exp_pos l)), hl⟩
    have hm : MemLp (fun ω => KH l ω - LH l ω) 2 P :=
      he.trans_lt ENNReal.ofReal_lt_top
    exact hm.const_mul _
  have hFineSq : Tendsto (fun l => ∫ ω,
      (Real.sqrt l * (KH l ω - LH l ω)) ^ 2 ∂P) atTop (𝓝 0) := by
    apply hFineMoment.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with l hl
    simp only [KH, LH, H, a, mul_pow, Real.sq_sqrt hl, integral_const_mul]
  have hFine := tendstoInMeasure_zero_of_integral_sq_eventually hFineMem hFineSq
  have hKlocNeg : TendstoInMeasure P
      (fun l ω => -(Real.sqrt l * (KH l ω - KS l ω))) atTop (fun _ => 0) := by
    rw [tendstoInMeasure_iff_norm] at hKloc ⊢
    simpa only [sub_zero, Real.norm_eq_abs, abs_neg] using hKloc
  have hGrid := eventually_uvFineEntrance_eq_gridEntrance hc hρ
  have hLocal : TendstoInMeasure P
      (fun l ω => Real.sqrt l * (LH l ω - LS l ω)) atTop (fun _ => 0) := by
    rw [tendstoInMeasure_iff_norm]
    intro ε hε
    have hU := hUniform ρ hρle P Z hZ f f.continuous.measurable
      (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)
      (integrable_firstMoment_testFn f) hfzero R hR.le hsupp (ε / 2) (half_pos hε)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU
      (Eventually.of_forall fun _ => zero_le)
    filter_upwards [hGrid] with l hgrid
    obtain ⟨j, hj⟩ := hgrid
    calc
      P {ω | ε ≤ ‖Real.sqrt l * (LH l ω - LS l ω) - 0‖} ≤
          P {ω | ε / 2 < Real.sqrt l *
            |profileLogPairing (Z l) (gridEntrance c ρ l j) (H l) f ω -
             profileLogPairing (Z l) (gridEntrance c ρ l j) (T l) f ω|} := by
        apply measure_mono
        intro ω hw
        simp only [Set.mem_ofPred_eq, sub_zero, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (Real.sqrt_nonneg _), LH, LS, H, T, a,
          lField, profileLogPairing, hj] at hw ⊢
        exact lt_of_lt_of_le (half_lt_self hε) hw
      _ ≤ ⨆ j : ℕ, P {ω | ε / 2 < Real.sqrt l *
            |profileLogPairing (Z l) (gridEntrance c ρ l j) (H l) f ω -
             profileLogPairing (Z l) (gridEntrance c ρ l j) (T l) f ω|} :=
        le_iSup_of_le j le_rfl
  have hsum := tendstoInMeasure_add_zero_real hKlocNeg
    (tendstoInMeasure_add_zero_real hFine hLocal)
  refine ⟨hKloc, ?_⟩
  apply hsum.congr' _ EventuallyEq.rfl
  filter_upwards [] with l
  filter_upwards [] with ω
  dsimp only [KH, KS, LH, LS, H, T, a]
  ring


end Critical2DKPZ.Extensions.GffTangent
