/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.CovarianceKernel.RegularizedSpecification
public import Critical2DKPZ.JointConvergence.ThmToyJointConvergence
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Moments.Covariance
import Mathlib.Tactic

/-! # Covariance convergence for tested KPZ fields -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BoundedContinuousFunction ENNReal Topology

universe u

namespace Critical2DKPZ.CovarianceKernel

set_option linter.style.haveILetI false in
private theorem covariance_tendsto_of_eLpNorm_sub_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ι : Type*} {l : Filter ι}
    (X Y : Ω → ℝ) (X' Y' : ι → Ω → ℝ)
    (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    (hX' : ∀ i, MemLp (X' i) 2 P) (hY' : ∀ i, MemLp (Y' i) 2 P)
    (hXlim : Tendsto (fun i => eLpNorm (fun ω => X' i ω - X ω) 2 P) l (𝓝 0))
    (hYlim : Tendsto (fun i => eLpNorm (fun ω => Y' i ω - Y ω) 2 P) l (𝓝 0)) :
    Tendsto (fun i => cov[X' i, Y' i; P]) l (𝓝 (cov[X, Y; P])) := by
  let p : ℝ≥0∞ := 2
  letI : ENNReal.HolderConjugate p p := by
    dsimp [p]
    simpa using Real.HolderConjugate.two_two.ennrealOfReal
  letI : Fact (1 ≤ p) := ⟨by norm_num [p]⟩
  let B : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.mul ℝ ℝ
  let pair : Lp ℝ p P →L[ℝ] Lp ℝ p P →L[ℝ] ℝ := B.lpPairing P p p
  have hXmem (i : ι) : MemLp (X' i) p P := by simpa [p] using hX' i
  have hYmem (i : ι) : MemLp (Y' i) p P := by simpa [p] using hY' i
  have hXmem0 : MemLp X p P := by simpa [p] using hX
  have hYmem0 : MemLp Y p P := by simpa [p] using hY
  have hone : MemLp (fun _ : Ω => (1 : ℝ)) p P := by
    simpa [p] using (memLp_const (1 : ℝ) : MemLp (fun _ : Ω => (1 : ℝ)) 2 P)
  let one : Lp ℝ p P := hone.toLp (fun _ => 1)
  let x : Lp ℝ p P := hXmem0.toLp X
  let y : Lp ℝ p P := hYmem0.toLp Y
  let x' : ι → Lp ℝ p P := fun i => (hXmem i).toLp (X' i)
  let y' : ι → Lp ℝ p P := fun i => (hYmem i).toLp (Y' i)
  have hnormX : Tendsto (fun i => (eLpNorm (fun ω => X' i ω - X ω) p P).toReal)
      l (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hXlim
    simpa only [Function.comp_def, ENNReal.toReal_zero] using h
  have hnormY : Tendsto (fun i => (eLpNorm (fun ω => Y' i ω - Y ω) p P).toReal)
      l (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hYlim
    simpa only [Function.comp_def, ENNReal.toReal_zero] using h
  have hxlim : Tendsto x' l (𝓝 x) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hnormX.eventually (Iio_mem_nhds hε)] with i hi
    have hdist : dist (x' i) x = (eLpNorm (fun ω => X' i ω - X ω) p P).toReal := by
      rw [Lp.dist_def]
      apply congrArg ENNReal.toReal
      apply eLpNorm_congr_ae
      exact (hXmem i).coeFn_toLp.sub hXmem0.coeFn_toLp
    rw [hdist]
    exact hi
  have hylim : Tendsto y' l (𝓝 y) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hnormY.eventually (Iio_mem_nhds hε)] with i hi
    have hdist : dist (y' i) y = (eLpNorm (fun ω => Y' i ω - Y ω) p P).toReal := by
      rw [Lp.dist_def]
      apply congrArg ENNReal.toReal
      apply eLpNorm_congr_ae
      exact (hYmem i).coeFn_toLp.sub hYmem0.coeFn_toLp
    rw [hdist]
    exact hi
  have hpaircont : Continuous (fun q : Lp ℝ p P × Lp ℝ p P => pair q.1 q.2) :=
    pair.continuous₂.comp₂ continuous_fst continuous_snd
  have hmeanLeftCont : Continuous (fun q : Lp ℝ p P × Lp ℝ p P => pair q.1 one) :=
    pair.continuous₂.comp₂ continuous_fst continuous_const
  have hmeanRightCont : Continuous (fun q : Lp ℝ p P × Lp ℝ p P => pair one q.2) :=
    pair.continuous₂.comp₂ continuous_const continuous_snd
  let covPair : Lp ℝ p P × Lp ℝ p P → ℝ := fun q =>
    pair q.1 q.2 - pair q.1 one * pair one q.2
  have hcovcont : Continuous covPair := by
    change Continuous (fun q : Lp ℝ p P × Lp ℝ p P =>
      pair q.1 q.2 - pair q.1 one * pair one q.2)
    exact hpaircont.sub (hmeanLeftCont.mul hmeanRightCont)
  have hpairX (i : ι) : pair (x' i) (y' i) = ∫ ω, X' i ω * Y' i ω ∂P := by
    dsimp [pair, x', y', B]
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [(hXmem i).coeFn_toLp, (hYmem i).coeFn_toLp] with ω hx hy
    simp [hx, hy]
  have hpair0 : pair x y = ∫ ω, X ω * Y ω ∂P := by
    dsimp [pair, x, y, B]
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [hXmem0.coeFn_toLp, hYmem0.coeFn_toLp] with ω hx hy
    simp [hx, hy]
  have hmeanX (i : ι) : pair (x' i) one = ∫ ω, X' i ω ∂P := by
    dsimp [pair, x', one, B]
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [(hXmem i).coeFn_toLp, hone.coeFn_toLp] with ω hx ho
    simp [hx]
  have hmeanY (i : ι) : pair one (y' i) = ∫ ω, Y' i ω ∂P := by
    dsimp [pair, y', one, B]
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [hone.coeFn_toLp, (hYmem i).coeFn_toLp] with ω ho hy
    simp [hy]
  have hmeanX0 : pair x one = ∫ ω, X ω ∂P := by
    dsimp [pair, x, one, B]
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [hXmem0.coeFn_toLp, hone.coeFn_toLp] with ω hx ho
    simp [hx]
  have hmeanY0 : pair one y = ∫ ω, Y ω ∂P := by
    dsimp [pair, y, one, B]
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [hone.coeFn_toLp, hYmem0.coeFn_toLp] with ω ho hy
    simp [hy]
  have hxy : Tendsto (fun i => (x' i, y' i)) l (𝓝 (x, y)) :=
    hxlim.prodMk_nhds hylim
  have hcv : Tendsto (fun i => covPair (x' i, y' i)) l (𝓝 (covPair (x, y))) := by
    exact hcovcont.continuousAt.tendsto.comp hxy
  have hcovId (i : ι) : cov[X' i, Y' i; P] =
      covPair (x' i, y' i) := by
    rw [covariance_eq_sub (hX' i) (hY' i)]
    change (∫ ω, X' i ω * Y' i ω ∂P) -
      (∫ ω, X' i ω ∂P) * ∫ ω, Y' i ω ∂P = _
    rw [← hpairX i, ← hmeanX i, ← hmeanY i]
  have hcovId0 : cov[X, Y; P] = covPair (x, y) := by
    rw [covariance_eq_sub hX hY]
    change (∫ ω, X ω * Y ω ∂P) -
      (∫ ω, X ω ∂P) * ∫ ω, Y ω ∂P = _
    rw [← hpair0, ← hmeanX0, ← hmeanY0]
  simpa only [hcovId, hcovId0] using hcv

/-- The forward regularized field tested against a test function is square-integrable whenever
the regularization scale is below the observation time. -/
private theorem kpzRegularized_test_memLp_of
    {Ω : Type u} [MeasurableSpace Ω] (ϑ : ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : LocalSobolev.ShfSymmetriesAt ϑ P Z)
    (hrevL : SmallScales.ShfReversalLawAt P Z)
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) (φ : TestFn) :
    MemLp (fun ω => ∫ x, φ x * kpzRegularized P Z t δ 0 x ω) 2 P := by
  classical
  let T : ℝ := t - δ
  let M : Ω → Measure (Plane × Plane) := fun ω => Z 0 T ω
  let S : Ω → Measure (Plane × Plane) := fun ω => (M ω).map Prod.swap
  let X : Plane × Ω → ℝ := fun q => kpzRegularized P Z t δ 0 q.1 q.2
  let c : ℝ := ∫ ω, swappedHeatStartLog Z t δ 0 ω ∂P
  have hTpos : 0 < T := by dsimp [T]; linarith
  obtain ⟨B, hB, hMom⟩ := kpzRegularized_uniform_second_moment_of
    ϑ P Z hZ hsym hrevL hδ hδt
  have hlogMem : MemLp (swappedHeatStartLog Z t δ 0) 2 P :=
    swappedHeatStartLog_memLp_two_of ϑ P Z hZ hsym hrevL hδ hδt 0
  have hmean0 : (∫ ω, kpzRegularized P Z t δ 0 0 ω ∂P) = 0 := by
    rw [kpzRegularized_eq_swappedHeatStartLog_sub_mean P Z 0]
    rw [integral_sub (hlogMem.integrable (by norm_num)) (integrable_const c)]
    simp [c]
  have hMmeas : Measurable M := by
    exact hZ.1 0 T le_rfl hTpos
  have hSmeas : Measurable S := by
    exact (Measure.measurable_map Prod.swap measurable_swap).comp hMmeas
  have hSlocal : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (S ω) := by
    filter_upwards [hZ.2.1 0 T le_rfl hTpos] with ω hω
    exact locallyFinite_map_homeomorph (Homeomorph.prodComm Plane Plane) (M ω) hω.1
  have hVmeas : AEMeasurable
      (fun q : Plane × Ω => swappedHeatStartLog Z t δ q.1 q.2) (volume.prod P) := by
    have h := JointConvergence.aemeasurable_log_heatPairing_joint P S hSmeas hSlocal
      δ hδ (fun _ : Plane => (1 : ℝ)) measurable_const (fun _ => by norm_num)
    simpa [swappedHeatStartLog, S, M, T] using h
  have hXae : AEMeasurable X (volume.prod P) := by
    have hbase : AEMeasurable
        (fun q : Plane × Ω => swappedHeatStartLog Z t δ q.1 q.2 - c) (volume.prod P) :=
      hVmeas.sub aemeasurable_const
    have hEq : X =ᵐ[volume.prod P]
        fun q : Plane × Ω => swappedHeatStartLog Z t δ q.1 q.2 - c := by
      filter_upwards [] with q
      have heq := kpzRegularized_eq_swappedHeatStartLog_sub_mean P Z (t := t) (δ := δ) q.1
      simpa [X, c] using congrFun heq q.2
    exact hbase.congr hEq.symm
  have hXsec (x : Plane) : AEStronglyMeasurable (fun ω => X (x, ω)) P := by
    have hm := (hMom x).1
    change AEStronglyMeasurable (kpzRegularized P Z t δ 0 x) P
    exact hm.aestronglyMeasurable
  have hXsq (x : Plane) : Integrable (fun ω => |X (x, ω)| ^ 2) P ∧
      (∫ ω, |X (x, ω)| ^ 2 ∂P) ≤ B := by
    have hsquare := (hMom x).2.1
    have hbound := (hMom x).2.2
    constructor
    · simpa only [X, Real.norm_eq_abs, sq_abs] using hsquare
    · simpa only [X, sq_abs] using le_of_eq hbound
  have hcenter := JointConvergence.memLp_centered_integral_test_of_uniform_square
    P hXae hXsec hB hXsq φ
  simpa only [X, hmean0, sub_zero] using hcenter

/-- A reversed regularized tested field has a measurable version in the SHF σ-algebra, hence
is a.e. measurable on the ambient probability space. -/
private theorem kpzRegularizedReversed_test_aemeasurable_of
    {Ω : Type u} [MeasurableSpace Ω] (ϑ : ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {t T δ : ℝ} (ht : 0 ≤ t) (hδ : 0 < δ) (htδT : t + δ < T)
    (φ : TestFn) :
    AEMeasurable
      (fun ω => ∫ x, φ x * kpzRegularizedReversed P Z t T δ 0 x ω) P := by
  obtain ⟨v, hv, hvAE⟩ :=
    JointConvergence.exists_shfSigma_measurable_kpzRegularizedReversed_integral
      ϑ P Z hZ t T δ ht hδ htδT 0 φ
  have hSigmaLe : shfSigma Z ≤ (inferInstance : MeasurableSpace Ω) := by
    dsimp [shfSigma]
    apply iSup_le
    intro s
    apply iSup_le
    intro u
    apply iSup_le
    intro hsu
    exact (hZ.1 s u hsu.1 hsu.2).comap_le
  have hvAmbient : Measurable v := by
    intro s hs
    exact hSigmaLe (v ⁻¹' s) (hv hs)
  exact hvAmbient.aemeasurable.congr hvAE

/-- Identically distributed pairs with square-integrable coordinates have equal covariance. -/
private theorem covariance_eq_of_identDistrib_pair
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y X' Y' : Ω → ℝ}
    (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    (hXid : IdentDistrib X X' P P) (hYid : IdentDistrib Y Y' P P)
    (hXYid : IdentDistrib (fun ω => X ω * Y ω) (fun ω => X' ω * Y' ω) P P) :
    cov[X, Y; P] = cov[X', Y'; P] := by
  have hX' : MemLp X' 2 P := hXid.memLp_snd hX
  have hY' : MemLp Y' 2 P := hYid.memLp_snd hY
  rw [covariance_eq_sub hX hY, covariance_eq_sub hX' hY']
  change (∫ ω, X ω * Y ω ∂P) - (∫ ω, X ω ∂P) * ∫ ω, Y ω ∂P =
    (∫ ω, X' ω * Y' ω ∂P) - (∫ ω, X' ω ∂P) * ∫ ω, Y' ω ∂P
  rw [hXYid.integral_eq, hXid.integral_eq, hYid.integral_eq]

/-- A law identity for a pair of real random variables preserves their covariance. -/
private theorem covariance_eq_of_identDistrib_prod
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y X' Y' : Ω → ℝ}
    (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    (hpair : IdentDistrib (fun ω => (X ω, Y ω)) (fun ω => (X' ω, Y' ω)) P P) :
    cov[X, Y; P] = cov[X', Y'; P] := by
  have hXid := hpair.comp measurable_fst
  have hYid := hpair.comp measurable_snd
  have hXYid := hpair.comp (by fun_prop : Measurable (fun q : ℝ × ℝ => q.1 * q.2))
  exact covariance_eq_of_identDistrib_pair P hX hY hXid hYid hXYid

/-- The two coordinates of a `Fin 2` vector, packaged as an ordered pair. -/
private def finTwoPair (v : Fin 2 → ℝ) : ℝ × ℝ := (v 0, v 1)

private theorem measurable_finTwoPair : Measurable finTwoPair := by
  exact (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)

/-- The covariance of the tested forward fields converges to the KPZ covariance as the
regularization scale decreases to zero. The regularized tested fields are in `L²` by
`kpzRegularized_test_memLp_of`; the proof transports this property to the reversed fields
and the limiting KPZ pairings using identical distributions. -/
theorem kpz_cov_tendsto_of (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : LocalSobolev.ShfSymmetriesAt ϑ P Z)
    (hrevL : SmallScales.ShfReversalLawAt P Z) (hC12 : LocalSobolev.ToyJointAt ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H) {t : ℝ} (ht : 0 < t)
    (f g : TestFn) :
    MemLp (fun ω => H t 0 ω f) 2 P ∧
      Tendsto (fun δ => cov[fun ω => ∫ x, f x * kpzRegularized P Z t δ 0 x ω,
          fun ω => ∫ x, g x * kpzRegularized P Z t δ 0 x ω; P]) (nhdsWithin 0 (Set.Ioi 0))
        (𝓝 (cov[fun ω => H t 0 ω f, fun ω => H t 0 ω g; P])) := by
  classical
  let T : ℝ := 2 * t
  let phi : Fin 2 → TestFn := fun i => if i = 0 then f else g
  let Fwd : ℝ → Ω → Fin 2 → ℝ := fun δ ω i =>
    ∫ x, phi i x * kpzRegularized P Z t δ 0 x ω
  let Rev : ℝ → Ω → Fin 2 → ℝ := fun δ ω i =>
    ∫ x, phi i x * kpzRegularizedReversed P Z t T δ 0 x ω
  have hTpos : 0 < T := by dsimp [T]; linarith
  obtain ⟨X₀, hX₀meas, hRate, hConv, _hLattice, hLaw⟩ := hC12 T hTpos
  let hSigmaLe : shfSigma Z ≤ (inferInstance : MeasurableSpace Ω) := by
    dsimp [shfSigma]
    apply iSup_le
    intro s
    apply iSup_le
    intro u
    apply iSup_le
    intro hsu
    exact (hZ.1 s u hsu.1 hsu.2).comap_le
  have hXmeas (ψ : TestFn) : Measurable (X₀ t 0 ψ) := by
    intro s hs
    exact hSigmaLe ((X₀ t 0 ψ) ⁻¹' s)
      (hX₀meas t 0 ψ (le_of_lt ht) (by dsimp [T]; linarith) hs)
  have hHae (ψ : TestFn) : AEMeasurable (fun ω => H t 0 ω ψ) P := by
    let δn : ℕ → ℝ := fun n => t / ((n : ℝ) + 2)
    have hInv : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (tendsto_add_atTop_nat 1)
      convert h using 1
      ext n
      simp [Nat.cast_add]
      ring
    have hδn : Tendsto δn atTop (𝓝 0) := by
      simpa [δn, div_eq_mul_inv, mul_comm] using hInv.const_mul t
    have hδnPos (n : ℕ) : 0 < δn n := by
      dsimp [δn]
      positivity
    have hδnLt (n : ℕ) : δn n < t := by
      dsimp [δn]
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hden : (1 : ℝ) < (n : ℝ) + 2 := by linarith
      exact div_lt_self ht hden
    have hδnWithin : Tendsto δn atTop (nhdsWithin 0 (Set.Ioi 0)) := by
      apply tendsto_nhdsWithin_iff.mpr
      exact ⟨hδn, Filter.Eventually.of_forall (fun n => hδnPos n)⟩
    have hmeas (n : ℕ) :
        AEMeasurable (fun ω => ∫ x, ψ x * kpzRegularized P Z t (δn n) 0 x ω) P :=
      (kpzRegularized_test_memLp_of ϑ P Z hZ hsym hrevL (hδnPos n) (hδnLt n) ψ).aemeasurable
    have hlim : TendstoInMeasure P
        (fun n ω => ∫ x, ψ x * kpzRegularized P Z t (δn n) 0 x ω)
        atTop (fun ω => H t 0 ω ψ) := by
      exact (hH t ht 0 ψ).comp hδnWithin
    exact TendstoInMeasure.aemeasurable hmeas hlim
  have hLimitData := hRate
  have hLimitMem (ψ : TestFn) : MemLp (X₀ t 0 ψ) 2 P := by
    obtain ⟨C, δ₁, hδ₁, hBound⟩ := hLimitData 0 ψ (t / 2) (by linarith) (by dsimp [T]; linarith)
    let δ₀ : ℝ := min (δ₁ / 2) (t / 2)
    have hδ₀ : 0 < δ₀ := by
      dsimp [δ₀]
      exact lt_min (by linarith) (by linarith)
    have hδ₀δ₁ : δ₀ < δ₁ := by dsimp [δ₀]; exact (min_le_left _ _).trans_lt (by linarith)
    have hδ₀t : δ₀ < t := by dsimp [δ₀]; exact (min_le_right _ _).trans_lt (by linarith)
    have hFmem : MemLp (fun ω => ∫ x, ψ x * kpzRegularized P Z t δ₀ 0 x ω) 2 P :=
      kpzRegularized_test_memLp_of ϑ P Z hZ hsym hrevL hδ₀ hδ₀t ψ
    have hRae : AEMeasurable
        (fun ω => ∫ x, ψ x * kpzRegularizedReversed P Z t T δ₀ 0 x ω) P :=
      kpzRegularizedReversed_test_aemeasurable_of ϑ P Z hZ ht.le hδ₀
        (by dsimp [T]; linarith) ψ
    have hLaw₁ := JointConvergence.kpzRegularized_reverse_law_of
      ϑ P Z hZ T (hrevL T) 1 (fun _ => t) (fun _ => δ₀) (fun _ => 0)
      (fun _ => ψ) (by intro i; exact ⟨hδ₀, hδ₀t, by dsimp [T]; linarith⟩)
    let F : Ω → Fin 1 → ℝ := fun ω _ => ∫ x, ψ x * kpzRegularized P Z t δ₀ 0 x ω
    let R : Ω → Fin 1 → ℝ := fun ω _ =>
      ∫ x, ψ x * kpzRegularizedReversed P Z t T δ₀ 0 x ω
    have hLaw₁' : P.map F = P.map R := by
      have hTt : T - t = t := by dsimp [T]; ring
      simpa [F, R, T, hTt] using hLaw₁
    have hFAE : AEMeasurable F P := by
      apply aemeasurable_pi_iff.mpr
      intro i
      fin_cases i
      exact hFmem.aemeasurable
    have hRAE : AEMeasurable R P := by
      apply aemeasurable_pi_iff.mpr
      intro i
      fin_cases i
      exact hRae
    have hVecIdent : IdentDistrib F R P P := ⟨hFAE, hRAE, hLaw₁'⟩
    have hScalarIdent := hVecIdent.comp (measurable_pi_apply (0 : Fin 1))
    have hIdent : IdentDistrib
        (fun ω => ∫ x, ψ x * kpzRegularized P Z t δ₀ 0 x ω)
        (fun ω => ∫ x, ψ x * kpzRegularizedReversed P Z t T δ₀ 0 x ω) P P :=
      by simpa only [Function.comp_def, F, R] using hScalarIdent
    have hRmem : MemLp
        (fun ω => ∫ x, ψ x * kpzRegularizedReversed P Z t T δ₀ 0 x ω) 2 P :=
      hIdent.memLp_snd hFmem
    have hDiffBound : eLpNorm (fun ω =>
        (∫ x, ψ x * kpzRegularizedReversed P Z t T δ₀ 0 x ω) - X₀ t 0 ψ ω) 2 P ≤
        ENNReal.ofReal (C * |Real.log (δ₀ / (T - t))| ^ (-(1 : ℝ) / 40)) := by
      apply hBound δ₀ hδ₀ hδ₀δ₁ t (le_of_lt ht)
      dsimp [T]
      linarith
    have hDiffMem : MemLp (fun ω =>
        (∫ x, ψ x * kpzRegularizedReversed P Z t T δ₀ 0 x ω) - X₀ t 0 ψ ω) 2 P := by
      rw [memLp_iff]
      exact hDiffBound.trans_lt ENNReal.ofReal_lt_top
    have hXmem' := hRmem.sub hDiffMem
    have heqX : (fun ω =>
        (∫ x, ψ x * kpzRegularizedReversed P Z t T δ₀ 0 x ω) -
          ((∫ x, ψ x * kpzRegularizedReversed P Z t T δ₀ 0 x ω) - X₀ t 0 ψ ω)) =
        X₀ t 0 ψ := by
      funext ω
      ring
    exact heqX ▸ hXmem'
  have hFwdMem (δ : Set.Ioo (0 : ℝ) t) (i : Fin 2) : MemLp (Fwd δ · i) 2 P := by
    simpa [Fwd] using kpzRegularized_test_memLp_of
      ϑ P Z hZ hsym hrevL δ.2.1 δ.2.2 (phi i)
  have hRevAemeas (δ : Set.Ioo (0 : ℝ) t) (i : Fin 2) : AEMeasurable (Rev δ · i) P := by
    simpa [Rev, T] using kpzRegularizedReversed_test_aemeasurable_of
      ϑ P Z hZ ht.le δ.2.1 (by linarith [δ.2.2, ht]) (phi i)
  have hRevMem (δ : Set.Ioo (0 : ℝ) t) (i : Fin 2) : MemLp (Rev δ · i) 2 P := by
    let R : Ω → Fin 2 → ℝ := Rev δ
    let F : Ω → Fin 2 → ℝ := Fwd δ
    have hFae : AEMeasurable F P := by
      apply aemeasurable_pi_iff.mpr
      intro j
      exact (hFwdMem δ j).aemeasurable
    have hRae : AEMeasurable R P := by
      apply aemeasurable_pi_iff.mpr
      intro j
      exact hRevAemeas δ j
    have hLaw₂ := JointConvergence.kpzRegularized_reverse_law_of
      ϑ P Z hZ T (hrevL T) 2 (fun _ => t) (fun _ => (δ : ℝ)) (fun _ => 0)
      phi (by intro j; exact ⟨δ.2.1, δ.2.2, by dsimp [T]; linarith⟩)
    have hLaw₂' : P.map F = P.map R := by
      have hTt : T - t = t := by dsimp [T]; ring
      simpa [F, R, Fwd, Rev, T, hTt] using hLaw₂
    have hIdent : IdentDistrib F R P P := ⟨hFae, hRae, hLaw₂'⟩
    have hcoord := hIdent.comp (measurable_pi_apply i)
    change MemLp (fun ω => Rev δ ω i) 2 P
    exact hcoord.memLp_snd (hFwdMem δ i)
  have hXmemF : MemLp (X₀ t 0 f) 2 P := hLimitMem f
  have hXmemG : MemLp (X₀ t 0 g) 2 P := hLimitMem g
  have hHmemF : MemLp (fun ω => H t 0 ω f) 2 P := by
    let F : Ω → Fin 2 → ℝ := fun ω i => X₀ t 0 (phi i) ω
    let G : Ω → Fin 2 → ℝ := fun ω i => H t 0 ω (phi i)
    have hFae : AEMeasurable F P := by
      apply aemeasurable_pi_iff.mpr
      intro i
      exact (hXmeas (phi i)).aemeasurable
    have hGae : AEMeasurable G P := by
      apply aemeasurable_pi_iff.mpr
      intro i
      exact hHae (phi i)
    have hLaw₂ := hLaw H hH 2 (fun _ => t) (fun _ => 0) phi
      (by intro i; exact ⟨le_of_lt ht, by dsimp [T]; linarith⟩)
    have hTt : T - t = t := by dsimp [T]; ring
    have hIdent : IdentDistrib F G P P := ⟨hFae, hGae, by
      simpa [F, G, hTt] using hLaw₂⟩
    have hcoord := hIdent.comp (measurable_pi_apply (0 : Fin 2))
    have hmem : MemLp (F · 0) 2 P := by
      simpa [F, phi] using hXmemF
    simpa [Function.comp_def, G, phi] using hcoord.memLp_snd hmem
  have hHmemG : MemLp (fun ω => H t 0 ω g) 2 P := by
    let F : Ω → Fin 2 → ℝ := fun ω i => X₀ t 0 (phi i) ω
    let G : Ω → Fin 2 → ℝ := fun ω i => H t 0 ω (phi i)
    have hFae : AEMeasurable F P := by
      apply aemeasurable_pi_iff.mpr
      intro i
      exact (hXmeas (phi i)).aemeasurable
    have hGae : AEMeasurable G P := by
      apply aemeasurable_pi_iff.mpr
      intro i
      exact hHae (phi i)
    have hLaw₂ := hLaw H hH 2 (fun _ => t) (fun _ => 0) phi
      (by intro i; exact ⟨le_of_lt ht, by dsimp [T]; linarith⟩)
    have hTt : T - t = t := by dsimp [T]; ring
    have hIdent : IdentDistrib F G P P := ⟨hFae, hGae, by
      simpa [F, G, hTt] using hLaw₂⟩
    have hcoord := hIdent.comp (measurable_pi_apply (1 : Fin 2))
    have hmem : MemLp (F · 1) 2 P := by
      simpa [F, phi] using hXmemG
    simpa [Function.comp_def, G, phi] using hcoord.memLp_snd hmem
  have hXHcov : cov[X₀ t 0 f, X₀ t 0 g; P] =
      cov[fun ω => H t 0 ω f, fun ω => H t 0 ω g; P] := by
    let F : Ω → Fin 2 → ℝ := fun ω i => X₀ t 0 (phi i) ω
    let G : Ω → Fin 2 → ℝ := fun ω i => H t 0 ω (phi i)
    have hFae : AEMeasurable F P := by
      apply aemeasurable_pi_iff.mpr
      intro i
      exact (hXmeas (phi i)).aemeasurable
    have hGae : AEMeasurable G P := by
      apply aemeasurable_pi_iff.mpr
      intro i
      exact hHae (phi i)
    have hLaw₂ := hLaw H hH 2 (fun _ => t) (fun _ => 0) phi
      (by intro i; exact ⟨le_of_lt ht, by dsimp [T]; linarith⟩)
    have hTt : T - t = t := by dsimp [T]; ring
    have hIdent : IdentDistrib F G P P := ⟨hFae, hGae, by
      simpa [F, G, hTt] using hLaw₂⟩
    have hPair : IdentDistrib (fun ω => (F ω 0, F ω 1))
        (fun ω => (G ω 0, G ω 1)) P P := by
      simpa only [Function.comp_def, finTwoPair] using hIdent.comp measurable_finTwoPair
    have hmemF0 : MemLp (F · 0) 2 P := by simpa [F, phi] using hXmemF
    have hmemF1 : MemLp (F · 1) 2 P := by simpa [F, phi] using hXmemG
    have hcov := covariance_eq_of_identDistrib_prod P hmemF0 hmemF1 hPair
    simpa [F, G, phi] using hcov
  have hConvF : Tendsto (fun δ : Set.Ioo (0 : ℝ) t =>
      eLpNorm (fun ω => Rev δ ω 0 - X₀ t 0 f ω) 2 P)
      (Filter.comap (Subtype.val : Set.Ioo (0 : ℝ) t → ℝ)
        (nhdsWithin 0 (Set.Ioi 0))) (𝓝 0) := by
    have hval := Filter.tendsto_comap
      (f := (Subtype.val : Set.Ioo (0 : ℝ) t → ℝ))
      (x := nhdsWithin 0 (Set.Ioi 0))
    have h := hConv t 0 f 2 (le_of_lt ht) (by dsimp [T]; linarith) (by norm_num) (by norm_num)
    simpa [Function.comp_def, Rev, phi, T] using h.comp hval
  have hConvG : Tendsto (fun δ : Set.Ioo (0 : ℝ) t =>
      eLpNorm (fun ω => Rev δ ω 1 - X₀ t 0 g ω) 2 P)
      (Filter.comap (Subtype.val : Set.Ioo (0 : ℝ) t → ℝ)
        (nhdsWithin 0 (Set.Ioi 0))) (𝓝 0) := by
    have hval := Filter.tendsto_comap
      (f := (Subtype.val : Set.Ioo (0 : ℝ) t → ℝ))
      (x := nhdsWithin 0 (Set.Ioi 0))
    have h := hConv t 0 g 2 (le_of_lt ht) (by dsimp [T]; linarith) (by norm_num) (by norm_num)
    simpa [Function.comp_def, Rev, phi, T] using h.comp hval
  have hRevCovLimit := covariance_tendsto_of_eLpNorm_sub_tendsto_zero P
    (X₀ t 0 f) (X₀ t 0 g)
    (fun δ : Set.Ioo (0 : ℝ) t => fun ω => Rev (δ : ℝ) ω 0)
    (fun δ : Set.Ioo (0 : ℝ) t => fun ω => Rev (δ : ℝ) ω 1)
    hXmemF hXmemG (fun δ => hRevMem δ 0) (fun δ => hRevMem δ 1) hConvF hConvG
  have hRevFwdCov (δ : Set.Ioo (0 : ℝ) t) :
      cov[(fun ω => Fwd δ ω 0), (fun ω => Fwd δ ω 1); P] =
        cov[(fun ω => Rev δ ω 0), (fun ω => Rev δ ω 1); P] := by
    let F : Ω → Fin 2 → ℝ := Fwd δ
    let G : Ω → Fin 2 → ℝ := Rev δ
    have hFae : AEMeasurable F P := by
      apply aemeasurable_pi_iff.mpr
      intro i
      exact (hFwdMem δ i).aemeasurable
    have hGae : AEMeasurable G P := by
      apply aemeasurable_pi_iff.mpr
      intro i
      exact hRevAemeas δ i
    have hLaw₂ := JointConvergence.kpzRegularized_reverse_law_of
      ϑ P Z hZ T (hrevL T) 2 (fun _ => t) (fun _ => (δ : ℝ)) (fun _ => 0)
      phi (by intro i; exact ⟨δ.2.1, δ.2.2, by dsimp [T]; linarith⟩)
    have hTt : T - t = t := by dsimp [T]; ring
    have hIdent : IdentDistrib F G P P := ⟨hFae, hGae, by
      simpa [F, G, Fwd, Rev, T, hTt] using hLaw₂⟩
    have hPair : IdentDistrib (fun ω => (F ω 0, F ω 1))
        (fun ω => (G ω 0, G ω 1)) P P := by
      simpa only [Function.comp_def, finTwoPair] using hIdent.comp measurable_finTwoPair
    exact covariance_eq_of_identDistrib_prod P (hFwdMem δ 0) (hFwdMem δ 1) hPair
  have hRevFwdCovFun : (fun δ : Set.Ioo (0 : ℝ) t => cov[(fun ω => Fwd δ ω 0), (fun ω => Fwd δ ω 1); P]) =
      (fun δ : Set.Ioo (0 : ℝ) t => cov[(fun ω => Rev δ ω 0), (fun ω => Rev δ ω 1); P]) := by
    funext δ
    exact hRevFwdCov δ
  have hCovOnSubtype : Tendsto (fun δ : Set.Ioo (0 : ℝ) t =>
      cov[(fun ω => Fwd δ ω 0), (fun ω => Fwd δ ω 1); P])
      (Filter.comap (Subtype.val : Set.Ioo (0 : ℝ) t → ℝ)
        (nhdsWithin 0 (Set.Ioi 0)))
      (𝓝 (cov[fun ω => H t 0 ω f, fun ω => H t 0 ω g; P])) := by
    rw [hRevFwdCovFun]
    simpa only [hXHcov] using hRevCovLimit
  have hRange : Set.range (Subtype.val : Set.Ioo (0 : ℝ) t → ℝ) ∈
      nhdsWithin 0 (Set.Ioi 0) := by
    rw [mem_nhdsWithin_iff_eventually]
    filter_upwards [Iio_mem_nhds ht] with δ hδ
    intro hδpos
    exact ⟨⟨δ, hδpos, hδ⟩, rfl⟩
  have hCov : Tendsto (fun δ : ℝ => cov[
      fun ω => ∫ x, f x * kpzRegularized P Z t δ 0 x ω,
      fun ω => ∫ x, g x * kpzRegularized P Z t δ 0 x ω; P])
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (cov[fun ω => H t 0 ω f, fun ω => H t 0 ω g; P])) := by
    apply (Filter.tendsto_comap'_iff hRange).mp
    simpa [Function.comp_def, Fwd, phi] using hCovOnSubtype
  exact ⟨hHmemF, hCov⟩

end Critical2DKPZ.CovarianceKernel

end
