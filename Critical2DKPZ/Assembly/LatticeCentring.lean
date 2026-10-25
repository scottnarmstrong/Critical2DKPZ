/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.KpzLatticeCentring
public import Critical2DKPZ.Analysis.Lattice.Volume
public import Critical2DKPZ.LocalSobolev.TimeReversalMass
public import Critical2DKPZ.Polymer.Locality
public import Critical2DKPZ.LocalSobolev.LatticeCovarianceBase
public import Critical2DKPZ.Gaussian.TimeBlocks
public import Critical2DKPZ.Smoothing.PolymerLogMomentBounds
public import Critical2DKPZ.OnePoint.FiniteProfileGaussian
public import Critical2DKPZ.Provider.SecondMomentCriticalWindow
public import Critical2DKPZ.SHF.Moments.CriticalBoundary
import Critical2DKPZ.SHF.Symmetries.LatticeReversalDiscrete
import Mathlib.Tactic

/-! # Lattice centring and the point-to-plane logarithmic mean -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter

namespace Critical2DKPZ.Assembly

/-- A single disorder coordinate is integrable. -/
private theorem integrable_coordinate (i : ℕ × Site) :
    Integrable (fun ω : Disorder => ω i) disorderLaw :=
  (Polymer.coordinate_hasLaw i).integrable (by
    simpa using (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl)

/-- A single disorder coordinate has mean zero. -/
private theorem integral_coordinate (i : ℕ × Site) :
    ∫ ω : Disorder, ω i ∂disorderLaw = 0 := by
  rw [(Polymer.coordinate_hasLaw i).integral_eq]
  simp

/-- The log of a point-to-plane mass is integrable. -/
private theorem integrable_log_p2plane (β : ℝ) (a n : ℕ) (w : Site) :
    Integrable (fun ω => Real.log (pointToPlane β a n w ω)) disorderLaw :=
  (LocalSobolev.memLp_log_pointToPlane β a n w).integrable (by norm_num)

/-- The log of a point-to-plane mass has mean at least `-n β² / 2` (Jensen over the paths). -/
private theorem neg_le_integral_log_pointToPlane (β : ℝ) (a n : ℕ) (w : Site) :
    -((n : ℝ) * β ^ 2 / 2) ≤ ∫ ω, Real.log (pointToPlane β a n w ω) ∂disorderLaw := by
  let E : (Fin n → Fin 4) → Disorder → ℝ := fun s ω =>
    ∑ j ∈ Finset.Icc 1 n, (β * ω (a + j, walkPosition w s j) - β ^ 2 / 2)
  have hterm : ∀ (s : Fin n → Fin 4) (j : ℕ), Integrable
      (fun ω : Disorder => β * ω (a + j, walkPosition w s j) - β ^ 2 / 2) disorderLaw :=
    fun s j => ((integrable_coordinate _).const_mul β).sub (integrable_const _)
  have hEint : ∀ s, Integrable (E s) disorderLaw := fun s =>
    integrable_finsetSum _ fun j _ => hterm s j
  have hEmean : ∀ s, ∫ ω, E s ω ∂disorderLaw = -((n : ℝ) * β ^ 2 / 2) := by
    intro s
    simp only [E]
    rw [integral_finsetSum _ fun j _ => hterm s j]
    have : ∀ j ∈ Finset.Icc 1 n, ∫ ω : Disorder,
        (β * ω (a + j, walkPosition w s j) - β ^ 2 / 2) ∂disorderLaw = -(β ^ 2 / 2) := by
      intro j _
      rw [integral_sub ((integrable_coordinate _).const_mul β) (integrable_const _),
        integral_const_mul, integral_coordinate]
      simp
    rw [Finset.sum_congr rfl this]
    simp
    ring
  have hpt : ∀ ω, ∑ s, (4 : ℝ)⁻¹ ^ n * E s ω ≤ Real.log (pointToPlane β a n w ω) := by
    intro ω
    have hJ := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum
      (t := (Finset.univ : Finset (Fin n → Fin 4))) (w := fun _ => (4 : ℝ)⁻¹ ^ n)
      (p := fun s => Real.exp (E s ω)) (fun _ _ => by positivity)
      (by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
        rw [← mul_pow, mul_inv_cancel₀ (by norm_num : (4 : ℝ) ≠ 0), one_pow])
      (fun s _ => Real.exp_pos _)
    simpa [smul_eq_mul, Real.log_exp, pointToPlane, E] using hJ
  have hlow : ∫ ω, ∑ s, (4 : ℝ)⁻¹ ^ n * E s ω ∂disorderLaw = -((n : ℝ) * β ^ 2 / 2) := by
    rw [integral_finsetSum _ fun s _ => (hEint s).const_mul _]
    simp only [integral_const_mul, hEmean, Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ (by norm_num : (4 : ℝ) ≠ 0), one_pow, one_mul]
  rw [← hlow]
  exact integral_mono (integrable_finsetSum _ fun s _ => (hEint s).const_mul _)
    (integrable_log_p2plane β a n w) hpt

/-- Functions measurable with respect to the past and the next slice are independent. -/
private theorem indepFun_past_block (m : ℕ) {f g : Disorder → ℝ}
    (hf : Measurable[Gaussian.disorderBlock 0 m] f)
    (hg : Measurable[Gaussian.disorderBlock m (m + 1)] g) :
    IndepFun f g disorderLaw := by
  rw [IndepFun_iff]
  intro s t hs ht
  exact (Indep_iff _ _ _).1
    (Gaussian.indep_disorderBlock_of_le (m := 0) (n := m) (a := m) (b := m + 1) le_rfl)
    s t (hf.comap_le s hs) (hg.comap_le t ht)

/-- Adding one more time slice changes the mean log point-to-plane mass by an amount in
`[-β²/2, 0]`: the new factor is a conditional average of mean-one lognormal-type variables. -/
private theorem integral_log_pointToPlane_succ_sub (β : ℝ) (m : ℕ) :
    -(β ^ 2 / 2) ≤ (∫ ω, Real.log (pointToPlane β 0 (m + 1) 0 ω) ∂disorderLaw) -
        ∫ ω, Real.log (pointToPlane β 0 m 0 ω) ∂disorderLaw ∧
      (∫ ω, Real.log (pointToPlane β 0 (m + 1) 0 ω) ∂disorderLaw) -
        ∫ ω, Real.log (pointToPlane β 0 m 0 ω) ∂disorderLaw ≤ 0 := by
  classical
  set E : Finset Site := Polymer.endpoints (0 : Site) m with hE
  let P : Site → Disorder → ℝ := fun z ω => pointToPoint β 0 m 0 z ω
  let Y : Disorder → ℝ := fun ω => pointToPlane β 0 m 0 ω
  let Q : Site → Disorder → ℝ := fun z ω => pointToPlane β m 1 z ω
  let μ : Site → Disorder → ℝ := fun z ω => P z ω / Y ω
  have hYpos : ∀ ω, 0 < Y ω := fun ω => Polymer.pointToPlane_pos _ _ _ _ _
  have hY : ∀ ω, Y ω = ∑ z ∈ E, P z ω := by
    intro ω
    show pointToPlane β 0 m 0 ω = _
    rw [← Polymer.tsum_pointToPoint]
    exact tsum_eq_sum fun z hz => Polymer.pointToPoint_eq_zero_of_not_mem _ _ _ _ _ _ hz
  have hZ : ∀ ω, pointToPlane β 0 (m + 1) 0 ω = ∑ z ∈ E, P z ω * Q z ω := by
    intro ω
    rw [Polymer.pointToPlane_chapmanKolmogorov β 0 m 1 0 ω]
    simp only [zero_add]
    exact tsum_eq_sum fun z hz => by
      rw [Polymer.pointToPoint_eq_zero_of_not_mem _ _ _ _ _ _ hz, zero_mul]
  have hμ0 : ∀ z ω, 0 ≤ μ z ω := fun z ω =>
    div_nonneg (Polymer.pointToPoint_nonneg _ _ _ _ _ _) (hYpos ω).le
  have hμ1 : ∀ z ω, μ z ω ≤ 1 := fun z ω =>
    (div_le_one (hYpos ω)).2 (Polymer.pointToPoint_le_pointToPlane _ _ _ _ _ _)
  have hμsum : ∀ ω, ∑ z ∈ E, μ z ω = 1 := by
    intro ω
    simp only [μ, ← Finset.sum_div]
    rw [← hY ω, div_self (hYpos ω).ne']
  have hratio : ∀ ω, pointToPlane β 0 (m + 1) 0 ω / Y ω = ∑ z ∈ E, μ z ω * Q z ω := by
    intro ω
    rw [hZ ω, Finset.sum_div]
    exact Finset.sum_congr rfl fun z _ => by simp only [μ]; ring
  have hmeasμ : ∀ z, Measurable[Gaussian.disorderBlock 0 m] (μ z) := fun z =>
    (Polymer.measurable_pointToPoint_past β m 0 z).div (Polymer.measurable_pointToPlane_past β m 0)
  have hmeasQ : ∀ z, Measurable[Gaussian.disorderBlock m (m + 1)] (Q z) := fun z =>
    Polymer.measurable_pointToPlane_block β m 1 z
  have hind : ∀ z, IndepFun (μ z) (Q z) disorderLaw := fun z =>
    indepFun_past_block m (hmeasμ z) (hmeasQ z)
  have hindlog : ∀ z, IndepFun (μ z) (fun ω => Real.log (Q z ω)) disorderLaw := fun z =>
    indepFun_past_block m (hmeasμ z) (hmeasQ z).log
  have hμm : ∀ z, Measurable (μ z) := fun z =>
    (hmeasμ z).mono (Gaussian.disorderBlock_le 0 m) le_rfl
  have hμint : ∀ z, Integrable (μ z) disorderLaw := fun z =>
    (integrable_const (1 : ℝ)).mono' (hμm z).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hμ0 z ω)]; exact hμ1 z ω)
  have hμQint : ∀ z, Integrable (fun ω => μ z ω * Q z ω) disorderLaw := fun z =>
    (Polymer.integrable_pointToPlane β m 1 z).bdd_mul (hμm z).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hμ0 z ω)]; exact hμ1 z ω)
  have hlogQint : ∀ z, Integrable (fun ω => Real.log (Q z ω)) disorderLaw := fun z =>
    integrable_log_p2plane β m 1 z
  have hμlogint : ∀ z, Integrable (fun ω => μ z ω * Real.log (Q z ω)) disorderLaw := fun z =>
    (hlogQint z).bdd_mul (hμm z).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hμ0 z ω)]; exact hμ1 z ω)
  have hsumμ : ∑ z ∈ E, ∫ ω, μ z ω ∂disorderLaw = 1 := by
    rw [← integral_finsetSum _ fun z _ => hμint z]
    simp [hμsum]
  have hlogZint := integrable_log_p2plane β 0 (m + 1) 0
  have hlogYint := integrable_log_p2plane β 0 m 0
  have hdiff : (∫ ω, Real.log (pointToPlane β 0 (m + 1) 0 ω) ∂disorderLaw) -
      ∫ ω, Real.log (pointToPlane β 0 m 0 ω) ∂disorderLaw =
      ∫ ω, (Real.log (pointToPlane β 0 (m + 1) 0 ω) - Real.log (Y ω)) ∂disorderLaw :=
    (integral_sub hlogZint hlogYint).symm
  have hlogratio : ∀ ω, Real.log (pointToPlane β 0 (m + 1) 0 ω) - Real.log (Y ω) =
      Real.log (∑ z ∈ E, μ z ω * Q z ω) := by
    intro ω
    rw [← hratio ω, Real.log_div (Polymer.pointToPlane_pos _ _ _ _ _).ne' (hYpos ω).ne']
  rw [hdiff]
  simp only [hlogratio]
  have hint : Integrable (fun ω => Real.log (∑ z ∈ E, μ z ω * Q z ω)) disorderLaw :=
    (hlogZint.sub hlogYint).congr (Filter.Eventually.of_forall fun ω => hlogratio ω)
  constructor
  · -- lower bound by Jensen
    have hpt : ∀ ω, ∑ z ∈ E, μ z ω * Real.log (Q z ω) ≤ Real.log (∑ z ∈ E, μ z ω * Q z ω) := by
      intro ω
      have hJ := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum (t := E) (w := fun z => μ z ω)
        (p := fun z => Q z ω) (fun z _ => hμ0 z ω) (hμsum ω)
        (fun z _ => Polymer.pointToPlane_pos _ _ _ _ _)
      simpa [smul_eq_mul] using hJ
    have h1 : ∫ ω, ∑ z ∈ E, μ z ω * Real.log (Q z ω) ∂disorderLaw =
        ∑ z ∈ E, (∫ ω, μ z ω ∂disorderLaw) * ∫ ω, Real.log (Q z ω) ∂disorderLaw := by
      rw [integral_finsetSum _ fun z _ => hμlogint z]
      refine Finset.sum_congr rfl fun z _ => ?_
      exact (hind z |>.comp measurable_id (Real.measurable_log)).integral_mul_eq_mul_integral
        (hμm z).aestronglyMeasurable (hlogQint z).aestronglyMeasurable
    have h2 : ∑ z ∈ E, (∫ ω, μ z ω ∂disorderLaw) * ∫ ω, Real.log (Q z ω) ∂disorderLaw ≥
        -(β ^ 2 / 2) := by
      calc -(β ^ 2 / 2) = ∑ z ∈ E, (∫ ω, μ z ω ∂disorderLaw) * (-(β ^ 2 / 2)) := by
            rw [← Finset.sum_mul, hsumμ, one_mul]
        _ ≤ _ := by
          refine Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left ?_
            (integral_nonneg (hμ0 z))
          have := neg_le_integral_log_pointToPlane β m 1 z
          simpa using this
    calc -(β ^ 2 / 2) ≤ ∫ ω, ∑ z ∈ E, μ z ω * Real.log (Q z ω) ∂disorderLaw := by
          rw [h1]; exact h2
      _ ≤ _ := integral_mono (integrable_finsetSum _ fun z _ => hμlogint z) hint hpt
  · have hpt : ∀ ω, Real.log (∑ z ∈ E, μ z ω * Q z ω) ≤ (∑ z ∈ E, μ z ω * Q z ω) - 1 := by
      intro ω
      apply Real.log_le_sub_one_of_pos
      rw [← hratio ω]
      exact div_pos (Polymer.pointToPlane_pos _ _ _ _ _) (hYpos ω)
    have h1 : ∫ ω, ∑ z ∈ E, μ z ω * Q z ω ∂disorderLaw = 1 := by
      rw [integral_finsetSum _ fun z _ => hμQint z]
      have : ∀ z ∈ E, ∫ ω, μ z ω * Q z ω ∂disorderLaw = ∫ ω, μ z ω ∂disorderLaw := by
        intro z _
        have h := (hind z).integral_mul_eq_mul_integral (hμm z).aestronglyMeasurable
          (Polymer.integrable_pointToPlane β m 1 z).aestronglyMeasurable
        have hQ : ∫ ω, Q z ω ∂disorderLaw = 1 := Polymer.integral_pointToPlane β m 1 z
        change ∫ ω, μ z ω * Q z ω ∂disorderLaw = _
        rw [show (∫ ω, μ z ω * Q z ω ∂disorderLaw) =
          (∫ ω, μ z ω ∂disorderLaw) * ∫ ω, Q z ω ∂disorderLaw from h, hQ, mul_one]
      rw [Finset.sum_congr rfl this, hsumμ]
    calc _ ≤ ∫ ω, ((∑ z ∈ E, μ z ω * Q z ω) - 1) ∂disorderLaw :=
          integral_mono hint ((integrable_finsetSum _ fun z _ => hμQint z).sub
            (integrable_const _)) hpt
      _ = 0 := by
          rw [integral_sub (integrable_finsetSum _ fun z _ => hμQint z) (integrable_const _), h1]
          simp

/-- Every nonzero point-to-point mass ending at the origin starts at one of finitely many
sites. -/
private theorem pointToPoint_start_mem (β : ℝ) (n : ℕ) (w : Site) (ω : Disorder)
    (h : pointToPoint β 0 n w 0 ω ≠ 0) :
    w ∈ (Finset.univ : Finset (Fin n → Fin 4)).image
      (fun s : Fin n → Fin 4 => -∑ i, srwStep (s i)) := by
  have hr : Polymer.Reachable n w 0 := by
    by_contra hr
    exact h ((Polymer.pointToPoint_eq_zero_iff β 0 n w 0 ω).2 hr)
  obtain ⟨s, hs⟩ := hr
  rw [Polymer.walkPosition_end] at hs
  refine Finset.mem_image.2 ⟨s, Finset.mem_univ _, ?_⟩
  exact (eq_neg_of_add_eq_zero_left hs).symm

/-- A nonzero point-to-point mass between sites at an even time distance starts at an even
site, when it ends at the origin. -/
private theorem pointToPoint_start_even (β : ℝ) {n : ℕ} (hn : Even n) (w : Site) (ω : Disorder)
    (h : pointToPoint β 0 n w 0 ω ≠ 0) : w ∈ evenLattice := by
  by_contra hw
  apply h
  apply Polymer.pointToPoint_eq_zero_of_parity
  obtain ⟨k, hk⟩ := hn
  simp only [Int.ModEq, Pi.zero_apply, evenLattice, Set.mem_ofPred_eq] at hw ⊢
  rw [hk]
  push_cast
  rw [Int.even_iff] at hw
  omega

/-- The cell integral of the rescaled point-to-point mass is the total mass of the lattice
masses: each even cell has area `4 / N`, which cancels the prefactor `N / 4`. -/
private theorem integral_rescaledP2P_eq (ϑ : ℝ) {N : ℕ} (hN : 0 < N) (t : ℝ) (ω : Disorder) :
    ∫ y, rescaledP2P ϑ N 0 t (y, 0) ω =
      ∑' w, pointToPoint (criticalBeta ϑ N) 0 (evenCeil (N * t)) w 0 ω := by
  classical
  set β := criticalBeta ϑ N with hβ
  set n := evenCeil (N * t) with hn
  have hnev : Even n := ⟨⌈(N * t) / 2⌉₊, by simp [hn, evenCeil]; ring⟩
  have h0 : evenCeil ((N : ℝ) * 0) = 0 := by simp [evenCeil]
  have hlp : latticePoint N (0 : Plane) = 0 := by
    ext i
    fin_cases i <;> simp [latticePoint, nearestEven]
  let g : Site → ℝ := fun w => (N / 4 : ℝ) * pointToPoint β 0 n w 0 ω
  have hint : ∀ y, rescaledP2P ϑ N 0 t (y, 0) ω = g (latticePoint N y) := by
    intro y
    simp only [rescaledP2P, h0, hlp, Nat.sub_zero, g]
    rfl
  simp_rw [hint]
  set F : Finset Site := ((Finset.univ : Finset (Fin n → Fin 4)).image
      (fun s : Fin n → Fin 4 => -∑ i, srwStep (s i))).filter (· ∈ evenLattice) with hF
  have hsupp : ∀ w, w ∉ F → pointToPoint β 0 n w 0 ω = 0 := by
    intro w hw
    by_contra h
    exact hw (Finset.mem_filter.2 ⟨pointToPoint_start_mem β n w ω h,
      pointToPoint_start_even β hnev w ω h⟩)
  have hgsupp : ∀ w, w ∉ F → g w = 0 := fun w hw => by simp [g, hsupp w hw]
  have hG : ∀ y, g (latticePoint N y) =
      ∑ z ∈ F, (cell N z).indicator (fun _ => g z) y := by
    intro y
    by_cases hy : latticePoint N y ∈ F
    · rw [Finset.sum_eq_single (latticePoint N y)]
      · simp [Set.indicator, cell]
      · intro z _ hz
        have : y ∉ cell N z := fun h => hz (by simpa [cell] using h.symm)
        simp [this]
      · exact fun h => absurd hy h
    · rw [hgsupp _ hy]
      symm
      apply Finset.sum_eq_zero
      intro z hz
      have : y ∉ cell N z := fun h => hy (by
        have : latticePoint N y = z := by simpa [cell] using h
        rwa [this])
      simp [this]
  have hvol : ∀ z ∈ F, (volume (cell N z)).toReal = 4 / N := fun z hz =>
    volume_cell_toReal hN (Finset.mem_filter.1 hz).2
  have hfin : ∀ z ∈ F, Integrable ((cell N z).indicator (fun _ => g z)) volume := by
    intro z hz
    refine (integrable_indicator_iff (measurableSet_cell N z)).2 ?_
    refine integrableOn_const ?_ 
    rw [volume_cell hN (Finset.mem_filter.1 hz).2]
    exact ENNReal.ofReal_ne_top
  simp_rw [hG]
  rw [integral_finsetSum _ hfin]
  rw [tsum_eq_sum (s := F) (fun w hw => hsupp w hw)]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [integral_indicator_const _ (measurableSet_cell N z), measureReal_def, hvol z hz]
  simp only [g, smul_eq_mul]
  have : (N : ℝ) ≠ 0 := by positivity
  field_simp

/-- Reversing time turns the mean log of the total backward mass into the mean log of the
point-to-plane mass with the last slice removed, minus `β² / 2`. -/
private theorem integral_log_tsum_start (β : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ∫ ω, Real.log (∑' w, pointToPoint β 0 n w 0 ω) ∂disorderLaw =
      -(β ^ 2 / 2) + ∫ ω, Real.log (pointToPlane β 0 (n - 1) 0 ω) ∂disorderLaw := by
  have hmp := PolymerCalculus.measurePreserving_reversedDisorder n
  have hlogint := integrable_log_p2plane β 0 (n - 1) 0
  have hrevint : Integrable (fun ω => Real.log (pointToPlane β 0 (n - 1) 0
      (PolymerCalculus.reversedDisorder n ω))) disorderLaw :=
    hmp.integrable_comp_of_integrable hlogint
  have hrev : ∫ ω, Real.log (pointToPlane β 0 (n - 1) 0
      (PolymerCalculus.reversedDisorder n ω)) ∂disorderLaw =
      ∫ ω, Real.log (pointToPlane β 0 (n - 1) 0 ω) ∂disorderLaw := by
    have h := integral_map (μ := disorderLaw) (φ := PolymerCalculus.reversedDisorder n)
      hmp.measurable.aemeasurable
      (f := fun ω => Real.log (pointToPlane β 0 (n - 1) 0 ω))
      (by rw [hmp.map_eq]; exact hlogint.aestronglyMeasurable)
    rw [hmp.map_eq] at h
    exact h.symm
  have hpt : ∀ ω, Real.log (∑' w, pointToPoint β 0 n w 0 ω) =
      β * ω (n, 0) - β ^ 2 / 2 + Real.log (pointToPlane β 0 (n - 1) 0
        (PolymerCalculus.reversedDisorder n ω)) := by
    intro ω
    rw [LocalSobolev.tsum_pointToPoint_start_time_reversal β hn 0 ω,
      Real.log_mul (Real.exp_pos _).ne' (Polymer.pointToPlane_pos _ _ _ _ _).ne',
      Real.log_exp]
  simp_rw [hpt]
  have hc : Integrable (fun ω : Disorder => β * ω (n, 0) - β ^ 2 / 2) disorderLaw :=
    ((integrable_coordinate _).const_mul β).sub (integrable_const _)
  rw [integral_add hc hrevint, hrev, integral_sub ((integrable_coordinate _).const_mul β)
    (integrable_const _), integral_const_mul, integral_coordinate]
  simp

/-- **Backward versus forward.** At every lattice scale `N ≥ 1` and time `t > 0`, the lattice
centring differs from the mean log point-to-plane mass by at most `β_N² / 2`. Both means are
integrals of integrable functions:
`LocalSobolev.memLp_log_pointToPlane` puts the log point-to-plane mass in every `Lᵖ`. -/
theorem kpzLatticeCentring_sub_logPointToPlane_le_of_pos (ϑ t : ℝ) (ht : 0 < t)
    {N : ℕ} (hN : 1 ≤ N) :
    |kpzLatticeCentring ϑ N t -
      ∫ ω, Real.log (pointToPlane (criticalBeta ϑ N) 0 (evenCeil (N * t)) 0 ω) ∂disorderLaw| ≤
      criticalBeta ϑ N ^ 2 / 2 := by
  set β := criticalBeta ϑ N with hβ
  have hpos : 0 < (N : ℝ) * t := mul_pos (by exact_mod_cast hN) ht
  have hn1 : 1 ≤ evenCeil ((N : ℝ) * t) := by
    have : 1 ≤ ⌈(N * t) / 2⌉₊ := Nat.one_le_iff_ne_zero.2
      (Nat.ceil_pos.2 (by positivity)).ne'
    unfold evenCeil
    omega
  obtain ⟨m, hm⟩ : ∃ m, evenCeil ((N : ℝ) * t) = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hn1).symm⟩
  have hcentre : kpzLatticeCentring ϑ N t =
      -(β ^ 2 / 2) + ∫ ω, Real.log (pointToPlane β 0 m 0 ω) ∂disorderLaw := by
    unfold kpzLatticeCentring
    simp_rw [integral_rescaledP2P_eq ϑ (show 0 < N by omega) t]
    rw [← hβ]
    rw [hm]
    have := integral_log_tsum_start β (n := m + 1) (by omega)
    simpa using this
  rw [hm, hcentre]
  obtain ⟨h1, h2⟩ := integral_log_pointToPlane_succ_sub β m
  rw [abs_le]
  constructor <;> linarith

/-- The same centering comparison at an explicitly specified even lattice clock. Unlike
`kpzLatticeCentring_sub_logPointToPlane_le`, this form is uniform over clock sequences whose
macroscopic times vary with `N`. -/
theorem kpzLatticeCentring_clock_sub_logPointToPlane_le (ϑ : ℝ) {N m : ℕ}
    (hN : 0 < N) (hmEven : Even m) (hm : 1 ≤ m) :
    |kpzLatticeCentring ϑ N ((m : ℝ) / N) -
      ∫ ω, Real.log (pointToPlane (criticalBeta ϑ N) 0 m 0 ω) ∂disorderLaw| ≤
        (criticalBeta ϑ N) ^ 2 / 2 := by
  set β := criticalBeta ϑ N with hβ
  have hclock : evenCeil ((N : ℝ) * ((m : ℝ) / N)) = m :=
    Critical2DKPZ.SHF.Symmetries.evenCeil_scaled_nat_div hN hmEven
  have hcentre : kpzLatticeCentring ϑ N ((m : ℝ) / N) =
      -(β ^ 2 / 2) +
        ∫ ω, Real.log (pointToPlane β 0 (m - 1) 0 ω) ∂disorderLaw := by
    unfold kpzLatticeCentring
    simp_rw [integral_rescaledP2P_eq ϑ hN ((m : ℝ) / N)]
    rw [hclock]
    have hstart := integral_log_tsum_start β (n := m) hm
    simpa only [β] using hstart
  have hstep := integral_log_pointToPlane_succ_sub β (m - 1)
  have hmEq : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have hstep' :
      -(β ^ 2 / 2) ≤
          (∫ ω, Real.log (pointToPlane β 0 m 0 ω) ∂disorderLaw) -
            ∫ ω, Real.log (pointToPlane β 0 (m - 1) 0 ω) ∂disorderLaw ∧
        (∫ ω, Real.log (pointToPlane β 0 m 0 ω) ∂disorderLaw) -
            ∫ ω, Real.log (pointToPlane β 0 (m - 1) 0 ω) ∂disorderLaw ≤ 0 := by
    simpa only [hmEq] using hstep
  rw [abs_le, hcentre]
  constructor <;> linarith [hstep'.1, hstep'.2]
/-- **Backward versus forward**, eventually in `N`: the form used by
`kpzLatticeCentring_asymptotic_of` (the per-`N` bound is
`kpzLatticeCentring_sub_logPointToPlane_le_of_pos`). -/
theorem kpzLatticeCentring_sub_logPointToPlane_le (ϑ t : ℝ) (ht : 0 < t) :
    ∀ᶠ N : ℕ in atTop,
      |kpzLatticeCentring ϑ N t -
        ∫ ω, Real.log (pointToPlane (criticalBeta ϑ N) 0 (evenCeil (N * t)) 0 ω) ∂disorderLaw| ≤
        criticalBeta ϑ N ^ 2 / 2 := by
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact kpzLatticeCentring_sub_logPointToPlane_le_of_pos ϑ t ht hN

/-- The point-to-plane mass has positive inverse and second moments satisfying the logarithmic moment inequalities. -/
private theorem pointToPlane_log_moment_bounds (β : ℝ) (n : ℕ) :
    Real.log (∫ ω, (pointToPlane β 0 n 0 ω)⁻¹ ∂disorderLaw) ≤
        -2 * ∫ ω, Real.log (pointToPlane β 0 n 0 ω) ∂disorderLaw ∧
      -2 * ∫ ω, Real.log (pointToPlane β 0 n 0 ω) ∂disorderLaw ≤
        Real.log (∫ ω, pointToPlane β 0 n 0 ω ^ 2 ∂disorderLaw) ∧
      0 < ∫ ω, (pointToPlane β 0 n 0 ω)⁻¹ ∂disorderLaw ∧
      0 < ∫ ω, pointToPlane β 0 n 0 ω ^ 2 ∂disorderLaw := by
  classical
  let ν : Site → ℝ := fun w => if w = 0 then 1 else 0
  have hνA : ∀ w ∉ ({0} : Finset Site), ν w = 0 := by
    intro w hw
    have hwz : w ≠ 0 := by simpa using hw
    simp [ν, hwz]
  have hν0 : ∀ w, 0 ≤ ν w := by
    intro w
    by_cases hw : w = 0 <;> simp [ν, hw]
  have hν1 : ∑ w ∈ ({0} : Finset Site), ν w = 1 := by simp [ν]
  have hEq : ∀ ω, profileP2Fun β 0 n ν (fun _ => 1) ω = pointToPlane β 0 n 0 ω := by
    intro ω
    rw [Polymer.profileP2Fun_eq_sum β 0 n ν (fun _ => 1) {0} hνA ω]
    simp only [Finset.sum_singleton]
    rw [show ν 0 = 1 by simp [ν], one_mul, Nat.sub_zero]
    simpa only [mul_one] using Polymer.tsum_pointToPoint β 0 n 0 ω
  have hb := OnePoint.profileP2Fun_log_moment_bounds β 0 n ν {0} hνA hν0 hν1
  have hdom := OnePoint.integrableExpSet_log_profileP2Fun_eq_univ β 0 n ν {0} hνA hν0 hν1
  simp only [hEq] at hb hdom
  obtain ⟨hD, hVar, hm2, hneg, -⟩ := hb
  have hpos : ∀ ω, 0 < pointToPlane β 0 n 0 ω := fun ω => Polymer.pointToPlane_pos _ _ _ _ _
  have htwo : mgf (fun ω => Real.log (pointToPlane β 0 n 0 ω)) disorderLaw 2 =
      ∫ ω, pointToPlane β 0 n 0 ω ^ 2 ∂disorderLaw := by
    rw [OnePoint.mgf_log_eq_integral_rpow hpos 2]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => Real.rpow_natCast _ 2)
  have hone : mgf (fun ω => Real.log (pointToPlane β 0 n 0 ω)) disorderLaw (-1) =
      ∫ ω, (pointToPlane β 0 n 0 ω)⁻¹ ∂disorderLaw := by
    rw [OnePoint.mgf_log_eq_integral_rpow hpos (-1)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => Real.rpow_neg_one _)
  have hmem : ∀ q : ℝ, q ∈ integrableExpSet
      (fun ω => Real.log (pointToPlane β 0 n 0 ω)) disorderLaw := fun q => by
    rw [hdom]; exact Set.mem_univ q
  have h1 := hneg 1 (by norm_num)
  rw [hone] at h1
  rw [htwo] at hm2
  refine ⟨?_, hm2, ?_, ?_⟩
  · linarith
  · rw [← hone]; exact mgf_pos (hmem _)
  · rw [← htwo]; exact mgf_pos (hmem _)

/-- The even ceiling lies between `x` and `x + 2`, for `x ≥ 0`. -/
private theorem evenCeil_bounds {x : ℝ} (hx : 0 ≤ x) :
    x ≤ (evenCeil x : ℝ) ∧ (evenCeil x : ℝ) ≤ x + 2 ∧ Even (evenCeil x) := by
  have h1 := Nat.le_ceil (x / 2)
  have h2 := Nat.ceil_lt_add_one (show 0 ≤ x / 2 by positivity)
  refine ⟨?_, ?_, ⟨⌈x / 2⌉₊, by simp [evenCeil]; ring⟩⟩ <;>
    simp only [evenCeil, Nat.cast_mul, Nat.cast_ofNat] <;> linarith

/-- The integrable log point-to-plane mass has mean `-½ log log N + O(1)` at critical coupling, with integrability supplied by `LocalSobolev.memLp_log_pointToPlane`. -/
theorem logPointToPlane_mean_asymptotic_of (hVD : Smoothing.PropVDBound) (ϑ t : ℝ) (ht : 0 < t) :
    ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
      |(∫ ω, Real.log (pointToPlane (criticalBeta ϑ N) 0 (evenCeil (N * t)) 0 ω) ∂disorderLaw) +
        (1 / 2) * Real.log (Real.log N)| ≤ C := by
  obtain ⟨hA, -⟩ := hVD |ϑ|
  obtain ⟨C₁, hC₁⟩ := hA t (t + 2) ht (by linarith)
  obtain ⟨c, hc, hlim⟩ := (Provider.secondMoment_criticalWindow ϑ).1 t ht
  have hlog := hlim.log hc.ne'
  have hev := (Metric.tendsto_nhds.1 hlog) 1 one_pos
  refine ⟨|C₁| / 2 + (|Real.log c| + 1) / 2, ?_⟩
  filter_upwards [hC₁, hev, eventually_ge_atTop 3] with N hN hdist hN3
  set β := criticalBeta ϑ N with hβ
  set n := evenCeil ((N : ℝ) * t) with hn
  have hNpos : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  obtain ⟨hlo, hhi, hev'⟩ := evenCeil_bounds (x := (N : ℝ) * t) (by positivity)
  obtain ⟨-, -, hratio⟩ := hN ϑ ⟨neg_abs_le ϑ, le_abs_self ϑ⟩ 0 0 n (by decide) hev'
    (Nat.zero_le _) (by rw [mul_comm]; exact hlo) (by nlinarith)
  simp only [LocalSobolev.smoothedP2Plane_zero_eq_pointToPlane] at hratio
  obtain ⟨hk1, hk2, hb, ha⟩ := pointToPlane_log_moment_bounds β n
  set a := ∫ ω, pointToPlane β 0 n 0 ω ^ 2 ∂disorderLaw with ha_def
  set b := ∫ ω, (pointToPlane β 0 n 0 ω)⁻¹ ∂disorderLaw with hb_def
  set m := ∫ ω, Real.log (pointToPlane β 0 n 0 ω) ∂disorderLaw with hm_def
  rw [Real.log_div ha.ne' hb.ne'] at hratio
  have hlogN : 0 < Real.log N := Real.log_pos (by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN3
    linarith)
  rw [Real.dist_eq, Real.log_div ha.ne' hlogN.ne'] at hdist
  have hcl := abs_lt.1 hdist
  have hc1 := neg_abs_le (Real.log c)
  have hc2 := le_abs_self (Real.log c)
  have hC1 := le_abs_self C₁
  rw [abs_le]
  constructor <;> nlinarith [abs_nonneg C₁, abs_nonneg (Real.log c)]

/-- The lattice centring is `-½ log log N + O(1)`. -/
theorem kpzLatticeCentring_asymptotic_of (hVD : Smoothing.PropVDBound) (ϑ t : ℝ) (ht : 0 < t) :
    ∃ C : ℝ, ∀ᶠ N in atTop, |kpzLatticeCentring ϑ N t + (1 / 2) * Real.log (Real.log N)| ≤ C := by
  obtain ⟨C, hC⟩ := logPointToPlane_mean_asymptotic_of hVD ϑ t ht
  have hβ := ((SHF.Moments.tendsto_criticalBeta_zero ϑ).pow 2).eventually
    (gt_mem_nhds (show (0 : ℝ) ^ 2 < 1 by norm_num))
  refine ⟨C + 1 / 2, ?_⟩
  filter_upwards [hC, hβ, kpzLatticeCentring_sub_logPointToPlane_le ϑ t ht] with N h1 h2 h3
  have h4 := abs_le.1 h3
  have h5 := abs_le.1 h1
  rw [abs_le]
  constructor <;> linarith

end Critical2DKPZ.Assembly

end

end
