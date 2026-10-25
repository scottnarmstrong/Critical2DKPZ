/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordTerminal
public import Mathlib.Tactic
public import Critical2DKPZ.SHF.Moments.EntranceBridge
import Critical2DKPZ.Blocks.StringSumPropagation
public import Critical2DKPZ.SHF.Moments.PairBlockScaledEnvelopeHorizon
import Mathlib.Tactic

/-! # Spatial integration of the tested two-particle renewal profile -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.SHF.Moments

open MeasureTheory Filter Polymer
open scoped CompactlySupported Topology

private theorem renewal_shifted_endpoint_even {r : ℕ} {q d : Site}
    (hq : Even ((r : ℤ) + q 0 + q 1)) (hd : d ∈ endpoints 0 r) :
    d - q ∈ evenLattice := by
  have hp := endpoints_accessible_phase r 0 d hd
  change Even ((d - q) 0 + (d - q) 1)
  rw [Int.even_iff] at hq hp ⊢
  simp only [Pi.sub_apply, Pi.zero_apply] at hp ⊢
  omega

/-- Exact integration on the shifted parity cells for a finitely supported
renewal slice, including integrability of the lattice step function. -/
private theorem integral_shifted_renewal_step
    {N : ℕ} (hN : 0 < N) (r : ℕ) (q : Site)
    (hq : Even ((r : ℤ) + q 0 + q 1)) (g : Site → ℝ)
    (hzero : ∀ d : Site, d ∉ endpoints 0 r → g d = 0) :
    Integrable (fun y : Plane => g (latticePoint N y + q)) ∧
      (∫ y : Plane, g (latticePoint N y + q)) =
        (4 / (N : ℝ)) * ∑ d ∈ endpoints 0 r, g d := by
  classical
  let E := (endpoints 0 r).image (fun d => d - q)
  have heven (e : Site) (he : e ∈ E) : e ∈ evenLattice := by
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    exact renewal_shifted_endpoint_even hq hd
  have hcellInt (e : Site) (he : e ∈ E) :
      Integrable ((cell N e).indicator (fun _ : Plane => g (e + q))) := by
    exact (integrableOn_const (C := g (e + q)) (volume_cell_lt_top hN (heven e he)).ne).integrable_indicator (measurableSet_cell N e)
  have hrepr : (fun y : Plane => g (latticePoint N y + q)) =
      fun y => ∑ e ∈ E, (cell N e).indicator (fun _ : Plane => g (e + q)) y := by
    funext y
    simp only [Set.indicator_apply, mem_cell_iff]
    by_cases hy : latticePoint N y ∈ E
    · simp [hy]
    · have hd : latticePoint N y + q ∉ endpoints 0 r := by
        intro hd
        apply hy
        exact Finset.mem_image.mpr ⟨latticePoint N y + q, hd, by simp⟩
      simp [hy, hzero _ hd]
  have hint : Integrable (fun y : Plane => g (latticePoint N y + q)) := by
    rw [hrepr]
    exact integrable_finsetSum _ hcellInt
  refine ⟨hint, ?_⟩
  rw [hrepr, integral_finsetSum _ hcellInt]
  have hcell (e : Site) (he : e ∈ E) :
      (∫ y : Plane, (cell N e).indicator (fun _ : Plane => g (e + q)) y) =
        (4 / (N : ℝ)) * g (e + q) := by
    rw [integral_indicator (measurableSet_cell N e), setIntegral_const,
      measureReal_def, smul_eq_mul, volume_cell_toReal hN (heven e he)]
  simp_rw [Finset.sum_congr rfl hcell]
  rw [← Finset.mul_sum]
  congr 1
  dsimp [E]
  rw [Finset.sum_image]
  · simp only [sub_add_cancel]
  · intro a ha b hb hab
    exact sub_left_injective hab

/-- The bounded parity correction vanishes at diffusive scale. -/
theorem tendsto_entranceParityShift_along (rN : ℕ → ℕ) :
    Tendsto (fun N : ℕ => latticeRepresentative N (entranceParityShift (rN N)))
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [(tendsto_latticeRepresentative_fixed_site ![1, 0]).eventually
    (Metric.ball_mem_nhds 0 hε)] with N hN
  by_cases hr : rN N % 2 = 0
  · have hzero : siteToPlane (0 : Site) = 0 := by
      ext i
      simp [siteToPlane]
    simpa [entranceParityShift, hr, latticeRepresentative, hzero] using hε
  · simpa [entranceParityShift, hr] using hN




private theorem exists_shifted_gaussian_product_majorant
    (C c B₀ B₁ : ℝ) (hC : 0 ≤ C) (hc : 0 < c) (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) :
    ∃ B : Plane → ℝ, Integrable B ∧ ∀ N : ℕ, 0 < N →
      ∀ δ : Plane, ‖δ‖ ≤ 1 → ∀ y : Plane, ∀ a b₀ b₁ : ℝ,
        |a| ≤ C * Real.exp (-c * ‖cellSample N y + δ‖ ^ 2) →
        |b₀| ≤ B₀ → |b₁| ≤ B₁ → ‖a * b₀ * b₁‖ ≤ B y := by
  let K : ℝ := C * B₀ * B₁ * Real.exp (9 * c)
  let B : Plane → ℝ := fun y => K * Real.exp (-(c / 2) * ‖y‖ ^ 2)
  have hgauss : Integrable (fun y : Plane => Real.exp (-(c / 2) * ‖y‖ ^ 2)) := by
    have hb : 0 < (((c / 2 : ℝ) : ℂ).re) := by simpa only [Complex.ofReal_re] using half_pos hc
    have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add hb 0 (0 : Plane)).re
    simpa only [zero_mul, add_zero, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      ← Complex.ofReal_neg, RCLike.re_eq_complex_re, Complex.exp_ofReal_re] using h
  refine ⟨B, hgauss.const_mul K, ?_⟩
  intro N hN δ hδ y a b₀ b₁ ha hb₀ hb₁
  let x := cellSample N y + δ
  have hdist : dist y x ≤ 3 := by
    calc
      dist y x ≤ dist y (cellSample N y) + dist (cellSample N y) x := dist_triangle _ _ _
      _ ≤ 2 + ‖δ‖ := by
        apply add_le_add (by simpa only [dist_comm] using dist_cellSample_le_two hN y)
        dsimp [x]
        rw [dist_eq_norm, show cellSample N y - (cellSample N y + δ) = -δ by abel, norm_neg]
      _ ≤ 3 := by linarith only [hδ]
  have hnorm : ‖y‖ ≤ ‖x‖ + 3 := by
    calc
      ‖y‖ ≤ dist y x + ‖x‖ := norm_le_norm_sub_add y x
      _ ≤ 3 + ‖x‖ := add_le_add hdist le_rfl
      _ = ‖x‖ + 3 := add_comm _ _
  have hsq : ‖y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 18 := by
    have h := pow_le_pow_left₀ (norm_nonneg y) hnorm 2
    nlinarith only [h, sq_nonneg (‖x‖ - 3)]
  have hexp : Real.exp (-c * ‖x‖ ^ 2) ≤
      Real.exp (9 * c) * Real.exp (-(c / 2) * ‖y‖ ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hsq hc.le
    nlinarith only [h]
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  calc
    |a| * |b₀| * |b₁| ≤ (C * Real.exp (-c * ‖x‖ ^ 2)) * B₀ * B₁ := by
      exact mul_le_mul (mul_le_mul ha hb₀ (abs_nonneg _) (by positivity))
        hb₁ (abs_nonneg _) (by positivity)
    _ = (C * B₀ * B₁) * Real.exp (-c * ‖x‖ ^ 2) := by ring
    _ ≤ (C * B₀ * B₁) *
        (Real.exp (9 * c) * Real.exp (-(c / 2) * ‖y‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = B y := by dsimp [B, K]; ring

private theorem tendsto_entranceParityShift_scale_along (M : ℕ → ℕ) (hM : Tendsto M atTop atTop) (rN : ℕ → ℕ) :
    Tendsto (fun N : ℕ => latticeRepresentative (M N) (entranceParityShift (rN N)))
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [((tendsto_latticeRepresentative_fixed_site ![1, 0]).comp hM).eventually
    (Metric.ball_mem_nhds 0 hε)] with N hN
  by_cases hr : rN N % 2 = 0
  · have hzero : siteToPlane (0 : Site) = 0 := by
      ext i
      simp [siteToPlane]
    simpa [entranceParityShift, hr, latticeRepresentative, hzero] using hε
  · simpa [entranceParityShift, hr] using hN

private theorem eventually_scaled_spatialRenewal_gaussian_along
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (ϑ v T : ℝ) (hv : 0 < v) (hvT : v < T) (rN : ℕ → ℕ)
    (hr : Tendsto (fun N : ℕ => (rN N : ℝ) / M N) atTop (𝓝 v)) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ᶠ N : ℕ in atTop, ∀ d : Site,
      Even ((rN N : ℤ) + d 0 + d 1) →
      0 ≤ (M N / 4 : ℝ) * (M N / Real.log (M N)) *
        Collision.spatialRenewal (criticalSigmaSq ϑ (M N)) (rN N) d ∧
      (M N / 4 : ℝ) * (M N / Real.log (M N)) *
        Collision.spatialRenewal (criticalSigmaSq ϑ (M N)) (rN N) d ≤
          C * Real.exp (-c * ‖latticeRepresentative (M N) d‖ ^ 2) := by
  obtain ⟨C, c, hC, hc, N₀, henv⟩ :=
    exists_eventually_scaled_spatialRenewal_le_gaussian_horizon |ϑ| (v / 2) T (half_pos hv) (hv.trans hvT)
  refine ⟨C, c, hC, hc, ?_⟩
  filter_upwards [hM.eventually (eventually_ge_atTop N₀), hM.eventually (eventually_ge_atTop 2),
    hM.eventually (Renewal.criticalSigmaSq_eventually_pos ϑ),
    hr.eventually (Ioo_mem_nhds (half_lt_self hv) hvT)] with N hN₀ hN hσ ht
  intro d hd
  have hNr : (0 : ℝ) < M N := by exact_mod_cast (by omega : 0 < M N)
  have hlo : (v / 2) * M N ≤ (rN N : ℝ) := ((lt_div_iff₀ hNr).mp ht.1).le
  have hhi : (rN N : ℝ) ≤ T * M N := ((div_lt_iff₀ hNr).mp ht.2).le
  have hlog : 0 < Real.log (M N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < M N))
  refine ⟨mul_nonneg (by positivity) (Blocks.spatialRenewal_nonneg hσ.le _ _), ?_⟩
  exact henv (M N) hN₀ ϑ ⟨neg_abs_le ϑ, le_abs_self ϑ⟩ (rN N) hlo hhi d hd

/-- The full spatial slice limit along arbitrary diverging lattice scales. -/
private theorem tendsto_pairTwo_tested_spatialSlice_along_below
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (ϑ v q Hmax : ℝ) (hv : 0 < v) (hvT : v < Hmax) (hq : 0 < q)
    (rN kN : ℕ → ℕ)
    (hr : Tendsto (fun N : ℕ => (rN N : ℝ) / M N) atTop (𝓝 v))
    (hk : Tendsto (fun N : ℕ => (kN N : ℝ) / M N) atTop (𝓝 q))
    (zN : ℕ → Site) (z : Plane)
    (hz : Tendsto (fun N : ℕ => latticeRepresentative (M N) (zN N)) atTop (𝓝 z))
    (hphase : ∀ᶠ N : ℕ in atTop,
      Even (zN N 0 + zN N 1 + (rN N : ℤ) + (kN N : ℤ)))
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (xN : ℕ → Fin 2 → Site)
    (hx : ∀ᶠ N : ℕ in atTop, ∀ i : Fin 2, xN N i ∈ evenLattice)
    (a : Fin 2 → Plane)
    (ha : ∀ i : Fin 2, Tendsto (fun N : ℕ => latticeRepresentative (M N) (xN N i))
      atTop (𝓝 (a i))) :
    Tendsto (fun N : ℕ => (M N : ℝ) ^ 3 * criticalSigmaSq ϑ (M N) *
      ∑ d ∈ endpoints 0 (rN N), Collision.spatialRenewal (criticalSigmaSq ϑ (M N)) (rN N) d *
        pairTwoFutureTerminalCellFactor (M N) (kN N) φ (xN N) (zN N + d) 0 *
        pairTwoFutureTerminalCellFactor (M N) (kN N) φ (xN N) (zN N + d) 1) atTop
      (𝓝 (16 * Real.pi * ∫ d : Plane,
        (DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) v * heatKernel (v / 2) d) *
        (∫ y : Plane, φ 0 (a 0, y) * heatKernel q (y - (z + d))) *
        (∫ y : Plane, φ 1 (a 1, y) * heatKernel q (y - (z + d))))) := by
  let Q : ℕ → Site := fun N => entranceParityShift (rN N)
  let δ : ℕ → Plane := fun N => latticeRepresentative (M N) (Q N)
  have hδ : Tendsto δ atTop (𝓝 0) := tendsto_entranceParityShift_scale_along M hM rN
  have hQ (N : ℕ) : Even ((rN N : ℤ) + Q N 0 + Q N 1) := by
    have h := entranceParityShift_phase (rN N) (a := 0) (by change Even ((0 : ℤ) + 0); simp)
    rw [Int.even_iff] at h ⊢
    simp only [Pi.sub_apply, Pi.zero_apply, sub_zero] at h
    dsimp [Q]
    omega
  let A : ℕ → Site → ℝ := fun N d => (M N / 4 : ℝ) * (M N / Real.log (M N)) *
    Collision.spatialRenewal (criticalSigmaSq ϑ (M N)) (rN N) d
  let T : Fin 2 → ℕ → Site → ℝ := fun i N w => (M N : ℝ) *
    pairTwoFutureTerminalCellFactor (M N) (kN N) φ (xN N) w i
  let g : ℕ → Site → ℝ := fun N d => A N d *
    T 0 N (zN N + d) * T 1 N (zN N + d)
  let f : ℕ → Plane → ℝ := fun N y => g N (latticePoint (M N) y + Q N)
  let G : Plane → ℝ := fun d =>
    (DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) v * heatKernel (v / 2) d) *
    (∫ y : Plane, φ 0 (a 0, y) * heatKernel q (y - (z + d))) *
    (∫ y : Plane, φ 1 (a 1, y) * heatKernel q (y - (z + d)))
  have hdphase (N : ℕ) (y : Plane) :
      Even ((rN N : ℤ) + (latticePoint (M N) y + Q N) 0 + (latticePoint (M N) y + Q N) 1) := by
    have hp := latticePoint_mem_evenLattice (M N) y
    change Even (latticePoint (M N) y 0 + latticePoint (M N) y 1) at hp
    have hqN := hQ N
    rw [Int.even_iff] at hp hqN ⊢
    simp only [Pi.add_apply]
    omega
  obtain ⟨C, c, hC, hc, hA⟩ := eventually_scaled_spatialRenewal_gaussian_along M hM ϑ v Hmax hv hvT rN hr
  let P : Fin 2 → ℝ := fun i => ‖(φ i).toBoundedContinuousFunction‖
  have hP (i : Fin 2) : 0 ≤ P i := norm_nonneg _
  have hT (N : ℕ) (hN : 0 < M N) (w : Site) (i : Fin 2) : |T i N w| ≤ 4 * P i := by
    have he := abs_pairTwoFutureTerminalCellFactor_le (k := kN N) hN φ (xN N) w i (P i) (hP i)
      (fun p => (φ i).toBoundedContinuousFunction.norm_coe_le_norm p)
    have hNr : (M N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    dsimp [T]
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (M N))]
    calc
      _ ≤ (M N : ℝ) * (4 * P i / M N) := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg (M N))
      _ = 4 * P i := by field_simp
  obtain ⟨B, hB, hBbound⟩ := exists_shifted_gaussian_product_majorant
    C c (4 * P 0) (4 * P 1) hC.le hc (by positivity) (by positivity)
  have hmeas (N : ℕ) : AEStronglyMeasurable (f N) :=
    ((measurable_of_countable (fun e : Site => g N (e + Q N))).comp
      (measurable_latticePoint (M N))).aestronglyMeasurable
  have hdom : ∀ᶠ N : ℕ in atTop, ∀ y : Plane, ‖f N y‖ ≤ B y := by
    filter_upwards [hA, hM.eventually (eventually_gt_atTop 0),
      hδ.norm.eventually (Iio_mem_nhds (by simp : ‖(0 : Plane)‖ < (1 : ℝ)))]
        with N hAN hN hδN
    intro y
    let d := latticePoint (M N) y + Q N
    have hrep : latticeRepresentative (M N) d = cellSample (M N) y + δ N := by
      simp only [d, latticeRepresentative_add, cellSample, δ]
    have haN := hAN d (hdphase N y)
    change ‖A N d * T 0 N (zN N + d) *
      T 1 N (zN N + d)‖ ≤ B y
    exact hBbound (M N) hN (δ N) hδN.le y _ _ _
      (by rw [abs_of_nonneg haN.1]; simpa only [hrep] using haN.2)
      (hT N hN _ 0) (hT N hN _ 1)
  have hpoint (y : Plane) : Tendsto (fun N => f N y) atTop (𝓝 (16 * G y)) := by
    let dN : ℕ → Site := fun N => latticePoint (M N) y + Q N
    let wN : ℕ → Site := fun N => zN N + dN N
    have hd : Tendsto (fun N => latticeRepresentative (M N) (dN N)) atTop (𝓝 y) := by
      have h := ((tendsto_cellSample y).comp hM).add hδ
      simpa only [dN, latticeRepresentative_add, add_zero, cellSample, δ, Function.comp_apply] using h
    have hw : Tendsto (fun N => latticeRepresentative (M N) (wN N)) atTop (𝓝 (z + y)) := by
      simpa only [wN, latticeRepresentative_add] using hz.add hd
    have hpR : ∀ᶠ N : ℕ in atTop, Even ((rN N : ℤ) + dN N 0 + dN N 1) :=
      Eventually.of_forall fun N => hdphase N y
    have hpT : ∀ᶠ N : ℕ in atTop, Even (wN N 0 + wN N 1 + (kN N : ℤ)) := by
      filter_upwards [hphase] with N hp
      have hdN := hdphase N y
      rw [Int.even_iff] at hp hdN ⊢
      simp only [wN, dN, Pi.add_apply]
      dsimp [dN] at hdN
      omega
    have hR := tendsto_scaled_spatialRenewal_parameter_moving_horizon M hM (fun _ => ϑ) ϑ v tendsto_const_nhds hv rN hr dN y hd hpR
    have hterminal (i : Fin 2) := tendsto_pairTwoFutureTerminalCellFactor_moving_along M hM
      hq kN hk wN (z + y) hw hpT φ xN i (hx.mono fun N hN => hN i) (a i) (ha i)
    have hprod := (hR.mul (hterminal 0)).mul (hterminal 1)
    convert hprod using 1
    apply congrArg (fun t : ℝ => 𝓝 t)
    dsimp [G]
    ring
  have hlim : Tendsto (fun N => ∫ y : Plane, f N y) atTop (𝓝 (∫ y : Plane, 16 * G y)) := by
    apply tendsto_integral_filter_of_dominated_convergence B
    · exact Eventually.of_forall hmeas
    · exact hdom.mono fun N hN => Eventually.of_forall hN
    · exact hB
    · exact Eventually.of_forall hpoint
  rw [integral_const_mul] at hlim
  have hS := (Renewal.tendsto_sigma_mul_log ϑ).comp hM
  have hprod := hS.mul hlim
  have heq : (fun N : ℕ => (M N : ℝ) ^ 3 * criticalSigmaSq ϑ (M N) *
      ∑ d ∈ endpoints 0 (rN N), Collision.spatialRenewal (criticalSigmaSq ϑ (M N)) (rN N) d *
        pairTwoFutureTerminalCellFactor (M N) (kN N) φ (xN N) (zN N + d) 0 *
        pairTwoFutureTerminalCellFactor (M N) (kN N) φ (xN N) (zN N + d) 1) =ᶠ[atTop]
      fun N => (criticalSigmaSq ϑ (M N) * Real.log (M N)) * ∫ y : Plane, f N y := by
    filter_upwards [hM.eventually (eventually_gt_atTop 1)] with N hN
    have hNr : (M N : ℝ) ≠ 0 := by exact_mod_cast (by omega : M N ≠ 0)
    have hlog : Real.log (M N : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (by omega : 1 < M N))).ne'
    have hi := integral_shifted_renewal_step (by omega : 0 < M N) (rN N) (Q N) (hQ N)
      (g N) (fun d hd => by simp [g, A, spatialRenewal_eq_zero_of_not_mem_endpoints _ _ _ hd])
    change _ = (criticalSigmaSq ϑ (M N) * Real.log (M N)) * (∫ y : Plane, g N (latticePoint (M N) y + Q N))
    rw [hi.2]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    dsimp [g, A, T]
    field_simp
  have hlimit : Real.pi * (16 * ∫ y : Plane, G y) =
      16 * Real.pi * ∫ y : Plane, G y := by ring
  rw [hlimit] at hprod
  exact hprod.congr' heq.symm


/-- The full spatial slice limit at arbitrary positive renewal and terminal
 times, along any diverging lattice scales. -/
theorem tendsto_pairTwo_tested_spatialSlice_along_horizon
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (ϑ v q : ℝ) (hv : 0 < v) (hq : 0 < q)
    (rN kN : ℕ → ℕ)
    (hr : Tendsto (fun N : ℕ => (rN N : ℝ) / M N) atTop (𝓝 v))
    (hk : Tendsto (fun N : ℕ => (kN N : ℝ) / M N) atTop (𝓝 q))
    (zN : ℕ → Site) (z : Plane)
    (hz : Tendsto (fun N : ℕ => latticeRepresentative (M N) (zN N)) atTop (𝓝 z))
    (hphase : ∀ᶠ N : ℕ in atTop,
      Even (zN N 0 + zN N 1 + (rN N : ℤ) + (kN N : ℤ)))
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (xN : ℕ → Fin 2 → Site)
    (hx : ∀ᶠ N : ℕ in atTop, ∀ i : Fin 2, xN N i ∈ evenLattice)
    (a : Fin 2 → Plane)
    (ha : ∀ i : Fin 2, Tendsto (fun N : ℕ => latticeRepresentative (M N) (xN N i))
      atTop (𝓝 (a i))) :
    Tendsto (fun N : ℕ => (M N : ℝ) ^ 3 * criticalSigmaSq ϑ (M N) *
      ∑ d ∈ endpoints 0 (rN N), Collision.spatialRenewal (criticalSigmaSq ϑ (M N)) (rN N) d *
        pairTwoFutureTerminalCellFactor (M N) (kN N) φ (xN N) (zN N + d) 0 *
        pairTwoFutureTerminalCellFactor (M N) (kN N) φ (xN N) (zN N + d) 1) atTop
      (𝓝 (16 * Real.pi * ∫ d : Plane,
        (DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) v * heatKernel (v / 2) d) *
        (∫ y : Plane, φ 0 (a 0, y) * heatKernel q (y - (z + d))) *
        (∫ y : Plane, φ 1 (a 1, y) * heatKernel q (y - (z + d))))) := by
  exact tendsto_pairTwo_tested_spatialSlice_along_below M hM ϑ v q (v + 1) hv (lt_add_one v) hq
    rN kN hr hk zN z hz hphase φ xN hx a ha



end Critical2DKPZ.SHF.Moments

end
