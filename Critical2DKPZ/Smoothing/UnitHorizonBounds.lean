/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Smoothing.Decomposition
public import Critical2DKPZ.Smoothing.GlobalLogErrorBounds
public import Critical2DKPZ.Smoothing.LocalLogL2Bounds
public import Critical2DKPZ.Smoothing.SpatialL2
public import Critical2DKPZ.Smoothing.ParityHelpers
public import Critical2DKPZ.Smoothing.CenteredLogL2
public import Critical2DKPZ.Analysis.Lattice.Basic
public import Critical2DKPZ.PolymerCalculus.Clocks
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Tactic

/-! # Unit-horizon smoothing bounds -/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal BoundedContinuousFunction

namespace Critical2DKPZ.Smoothing

/-- A measurable bounded function with compact support is integrable against planar volume.
The compact support localizes the bound to a finite-volume ball. -/
theorem integrable_of_measurable_compactSupport_bounded {φ : Plane → ℝ}
    (hφ : Measurable φ) (hφc : HasCompactSupport φ)
    (hφb : ∃ B : ℝ, ∀ x, |φ x| ≤ B) : Integrable φ := by
  classical
  obtain ⟨B, hB⟩ := hφb
  obtain ⟨R₀, hR₀⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : Plane)).mp hφc.isBounded
  let R := max R₀ 0
  have hR : 0 ≤ R := le_max_right _ _
  have htsupp (x : Plane) (hx : φ x ≠ 0) : ‖x‖ ≤ R := by
    have h := hR₀ (subset_tsupport φ hx)
    rw [Metric.mem_closedBall, dist_zero_right] at h
    exact h.trans (le_max_left _ _)
  have hballFinite : volume (Metric.closedBall (0 : Plane) R) ≠ ⊤ :=
    measure_closedBall_lt_top.ne
  have hφOn : IntegrableOn φ (Metric.closedBall (0 : Plane) R) volume := by
    apply Measure.integrableOn_of_bounded hballFinite hφ.aestronglyMeasurable
      (M := max B 0)
    filter_upwards [] with x
    rw [Real.norm_eq_abs]
    exact (hB x).trans (le_max_left _ _)
  have hφzero (x : Plane) (hx : x ∉ Metric.closedBall (0 : Plane) R) : φ x = 0 := by
    by_contra hne
    have hxR := htsupp x hne
    have hnot : ¬ ‖x‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    exact hnot hxR
  exact hφOn.integrable_of_forall_notMem_eq_zero hφzero

private theorem measurable_globalLogError_disorder_site (β : ℝ) (m n N : ℕ)
    (f : Site → ℝ) :
    Measurable (fun p : Disorder × Site => globalLogError β m n N f p.2 p.1) := by
  apply measurable_from_prod_countable_left
  intro z
  exact measurable_globalLogError β m n N f z

/-- The spatial integral of the centered global error inherits a uniform bound from the two
pointwise weighted global error bounds. The product field is measurable because its site coordinate is countable. -/
theorem eLpNorm_integral_centeredGlobal_le (β : ℝ) (m n N : ℕ) (f : Site → ℝ)
    (φ : Plane → ℝ) (hφ : Measurable φ) (hφint : Integrable φ)
    (R : ℝ) (hR : 0 ≤ R)
    (hF : ∀ z, eLpNorm (globalLogError β m n N f z) 2 disorderLaw ≤ ENNReal.ofReal R)
    (hG : ∀ z, eLpNorm (globalLogError β m n N (fun _ => 1) z) 2 disorderLaw ≤
      ENNReal.ofReal R) :
    Integrable (fun ω => ∫ x, φ x * (globalLogError β m n N f (latticePoint N x) ω -
      ∫ ω', globalLogError β m n N (fun _ => 1) (latticePoint N x) ω' ∂disorderLaw))
      disorderLaw ∧
    eLpNorm (fun ω => ∫ x, φ x * (globalLogError β m n N f (latticePoint N x) ω -
      ∫ ω', globalLogError β m n N (fun _ => 1) (latticePoint N x) ω' ∂disorderLaw))
      2 disorderLaw ≤ ENNReal.ofReal (2 * R * ∫ x, |φ x|) := by
  let F : Disorder → Site → ℝ := fun ω z => globalLogError β m n N f z ω
  let G : Disorder → Site → ℝ := fun ω z => globalLogError β m n N (fun _ => 1) z ω
  let c : Site → ℝ := fun z => ∫ ω', G ω' z ∂disorderLaw
  let Z : Disorder → Plane → ℝ := fun ω x => F ω (latticePoint N x) - c (latticePoint N x)
  have hFjoint : Measurable (fun p : Disorder × Site => F p.1 p.2) := by
    exact measurable_globalLogError_disorder_site β m n N f
  have hc : Measurable c := measurable_of_countable _
  have hZ : Measurable (fun p : Disorder × Plane => Z p.1 p.2) := by
    dsimp [Z, F]
    have hpair : Measurable (fun p : Disorder × Plane =>
        (p.1, latticePoint N p.2)) :=
      measurable_fst.prodMk ((measurable_latticePoint N).comp measurable_snd)
    exact (hFjoint.comp hpair).sub
      (hc.comp ((measurable_latticePoint N).comp measurable_snd))
  have hZbound (x : Plane) :
      eLpNorm (fun ω => Z ω x) 2 disorderLaw ≤ ENNReal.ofReal (2 * R) := by
    have hGmem : MemLp (fun ω => G ω (latticePoint N x)) 2 disorderLaw := by
      apply (memLp_iff).2
      exact lt_of_le_of_lt (hG (latticePoint N x)) (by simp)
    have hcenter := eLpNorm_sub_integral_le disorderLaw
      (fun ω => F ω (latticePoint N x)) (fun ω => G ω (latticePoint N x)) hGmem
    calc
      _ = eLpNorm (fun ω => F ω (latticePoint N x) -
          ∫ ω', G ω' (latticePoint N x) ∂disorderLaw) 2 disorderLaw := by
            simp [Z, c]
      _ ≤ eLpNorm (fun ω => F ω (latticePoint N x)) 2 disorderLaw +
          eLpNorm (fun ω => G ω (latticePoint N x)) 2 disorderLaw := hcenter
      _ ≤ ENNReal.ofReal R + ENNReal.ofReal R := add_le_add
          (hF (latticePoint N x)) (hG (latticePoint N x))
      _ = ENNReal.ofReal (2 * R) := by
        rw [← ENNReal.ofReal_add hR hR]
        congr 1
        ring
  have hZmem (x : Plane) : MemLp (fun ω => Z ω x) 2 disorderLaw :=
    (memLp_iff).2 ((hZbound x).trans_lt ENNReal.ofReal_lt_top)
  have hZsq (x : Plane) : Integrable (fun ω => Z ω x ^ 2) disorderLaw ∧
      (∫ ω, Z ω x ^ 2 ∂disorderLaw) ≤ (2 * R) ^ 2 :=
    integral_sq_le_of_eLpNorm_le disorderLaw (hZmem x) (2 * R) (by positivity) (hZbound x)
  have hspatial := eLpNorm_integral_mul_le_of_uniform_secondMoment disorderLaw φ hφ hφint
    hZ hZmem ((2 * R) ^ 2) (by positivity) hZsq
  refine ⟨hspatial.1, ?_⟩
  calc
    _ ≤ ENNReal.ofReal (Real.sqrt ((2 * R) ^ 2) * ∫ x, |φ x|) := hspatial.2
    _ = ENNReal.ofReal (2 * R * ∫ x, |φ x|) := by
      congr 1
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) hR)]

/-- At equal smoothing clocks, local heat-energy and weighted global estimates bound the unit-horizon logarithmic error. -/
theorem latticeSmoothingError_diagonal_unit_le_of (hVD : PropVDBound)
    (hO : FutureProfiles.PropPFOriginBound) (hL : FutureProfiles.LogTailsOriginBound)
    (A H M₁ M₂ : ℝ) :
    ∃ C δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₁ → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ M : ℕ in atTop, Even M → ∀ ϑ ∈ Set.Icc (-A) A,
        ∀ h₀ : Plane →ᵇ ℝ, ‖h₀‖ ≤ H →
        ∀ φ : Plane → ℝ, Measurable φ → HasCompactSupport φ →
        (∫ x, |φ x| ≤ M₁) → (∀ x, |φ x| ≤ M₂) →
        eLpNorm (latticeSmoothingError (criticalBeta ϑ M) M M
          (evenCeil (δ * M)) (evenCeil (δ * M)) h₀ φ)
          2 disorderLaw ≤ ENNReal.ofReal (C * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε) := by
  obtain ⟨CLraw, δL, hδL, hLocal⟩ := localLogError_L2_le_of hVD A M₁ M₂ 2 (by norm_num)
  obtain ⟨CGraw, δG, hδG, hGlobal⟩ := globalLogError_L2_le_of hO hL A H
  let CL := |CLraw| + 1
  let CG := |CGraw| + 1
  let δ₁ := min δL (min δG (Real.exp (-1)))
  let C := CL + 2 * |M₁| * CG
  have hδ₁ : 0 < δ₁ := by dsimp [δ₁]; positivity
  have hCL : 0 < CL := by dsimp [CL]; positivity
  have hCG : 0 < CG := by dsimp [CG]; positivity
  have hC : 0 < C := by dsimp [C, CL, CG]; positivity
  refine ⟨C, δ₁, hδ₁, ?_⟩
  intro δ hδ hδlt ε hε
  have hδL' : δ ≤ δL := (le_of_lt hδlt).trans (min_le_left _ _)
  have hδG' : δ ≤ δG := (le_of_lt hδlt).trans (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδexp : δ < Real.exp (-1) := lt_of_lt_of_le hδlt
    (le_trans (min_le_right _ _) (min_le_right _ _))
  have hδone : δ < 1 := by
    exact lt_trans hδexp (by norm_num [Real.exp_lt_one_iff])
  have hroot : δ ≤ Real.sqrt δ := Real.le_sqrt_self_iff.mpr hδone.le
  have hrootone : Real.sqrt δ < 1 := by
    simpa using Real.sqrt_lt_sqrt hδ.le hδone
  have hLpos : 0 < |Real.log δ| := by
    apply abs_pos.mpr
    have hlog : Real.log δ < -1 := by
      calc
        Real.log δ < Real.log (Real.exp (-1)) := Real.log_lt_log hδ hδexp
        _ = -1 := Real.log_exp _
    linarith
  have hLone : 1 ≤ |Real.log δ| := by
    have hlog : Real.log δ < -1 := by
      calc
        Real.log δ < Real.log (Real.exp (-1)) := Real.log_lt_log hδ hδexp
        _ = -1 := Real.log_exp _
    rw [abs_of_neg (by linarith)]
    linarith
  have hpow : |Real.log δ| ^ (-(1 : ℝ) / 8) ≤
      |Real.log δ| ^ (-(1 : ℝ) / 40) :=
    Real.rpow_le_rpow_of_exponent_le hLone (by norm_num)
  let εG := ε / (4 * (|M₁| + 1))
  have hεG : 0 < εG := by dsimp [εG]; positivity
  have hLocalEv := hLocal δ hδ hδL' (ε / 2) (by linarith)
  have hGlobalEv := hGlobal δ hδ hδG' εG hεG
  have hScaleEv : ∀ᶠ M : ℕ in atTop, 2 ≤ δ * (M : ℝ) := by
    have hev := (tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 / δ))
    filter_upwards [hev] with M hM
    have hM' := (div_le_iff₀ hδ).mp hM
    simpa [mul_comm] using hM'
  filter_upwards [hLocalEv, hGlobalEv, hScaleEv] with M hLocal hGlobal hScale
  intro hMeven ϑ hϑ h₀ h₀bound φ hφ hφc hφL1 hφM
  have hφint := integrable_of_measurable_compactSupport_bounded hφ hφc ⟨M₂, hφM⟩
  have hNcast : 0 ≤ (M : ℝ) := Nat.cast_nonneg _
  have hδM : 0 ≤ δ * (M : ℝ) := mul_nonneg hδ.le hNcast
  let m := evenCeil (δ * (M : ℝ))
  let n := evenCeil (Real.sqrt δ * (M : ℝ))
  have hmEven : Even m := evenCeil_even _
  have hnEven : Even n := evenCeil_even _
  have hmle : m ≤ n := evenCeil_mono (mul_le_mul_of_nonneg_right hroot hNcast)
  have hceilM : evenCeil (M : ℝ) = M := by
    obtain ⟨q, hq⟩ := hMeven
    rw [hq]
    simp [evenCeil, two_mul]
  have hnle : n ≤ M := by
    have hceil : evenCeil (Real.sqrt δ * (M : ℝ)) ≤ evenCeil (M : ℝ) :=
      evenCeil_mono (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hrootone.le hNcast)
    simpa [n, hceilM] using hceil
  have hmnReal : δ * (M : ℝ) ≤ (m : ℝ) := le_evenCeil _
  have hmUpper : (m : ℝ) ≤ 2 * δ * (M : ℝ) := by
    have hround := evenCeil_lt_add_two hδM
    dsimp [m]
    nlinarith [hround, hScale]
  have hLocalBound := hLocal ϑ hϑ m hmEven hmnReal hmUpper φ hφ hφint hφL1 hφM
  have hH : 0 ≤ H := le_trans (norm_nonneg _) h₀bound
  have hcell (z : Site) : 0 < evenExtension (cellAverage M
      (fun y => Real.exp (h₀ y))) z ∧
      |Real.log (evenExtension (cellAverage M (fun y => Real.exp (h₀ y))) z)| ≤ H := by
    by_cases hz : Even (z 0 + z 1)
    · have hMone : 1 ≤ M := by
        have hδMleM : δ * (M : ℝ) ≤ (M : ℝ) :=
          by simpa only [one_mul] using mul_le_mul_of_nonneg_right hδone.le hNcast
        have hMr : (1 : ℝ) ≤ (M : ℝ) := by nlinarith [hScale, hδMleM]
        exact_mod_cast hMr
      have h := cellAverage_exp_bounds_of_even M hMone h₀ hz
      refine ⟨?_, ?_⟩
      · simpa [evenExtension, hz] using h.1
      · simpa [evenExtension, hz] using h.2.trans h₀bound
    ·
      constructor
      · simp [evenExtension, hz]
      · simpa [evenExtension, hz] using hH
  have hGf : ∀ z, eLpNorm (globalLogError (criticalBeta ϑ M) m n M
      (evenExtension (cellAverage M fun y => Real.exp (h₀ y))) z) 2 disorderLaw ≤
      ENNReal.ofReal (CG * |Real.log δ| ^ (-(1 : ℝ) / 40) + εG) := by
    intro z
    have hraw := hGlobal ϑ hϑ
      (evenExtension (cellAverage M fun y => Real.exp (h₀ y))) hcell z
    exact hraw.trans (ENNReal.ofReal_le_ofReal (by
      have hp : 0 ≤ |Real.log δ| ^ (-(1 : ℝ) / 40) := Real.rpow_nonneg hLpos.le _
      have hcoeff := mul_le_mul_of_nonneg_right (le_abs_self CGraw) hp
      dsimp [CG]
      linarith))
  have hG1 : ∀ z, eLpNorm (globalLogError (criticalBeta ϑ M) m n M
      (fun _ => 1) z) 2 disorderLaw ≤
      ENNReal.ofReal (CG * |Real.log δ| ^ (-(1 : ℝ) / 40) + εG) := by
    intro z
    have hraw := hGlobal ϑ hϑ (fun _ : Site => 1) (by
      intro z
      exact ⟨by norm_num, by simpa [Real.log_one] using hH⟩) z
    exact hraw.trans (ENNReal.ofReal_le_ofReal (by
      have hp : 0 ≤ |Real.log δ| ^ (-(1 : ℝ) / 40) := Real.rpow_nonneg hLpos.le _
      have hcoeff := mul_le_mul_of_nonneg_right (le_abs_self CGraw) hp
      dsimp [CG]
      linarith))
  let R := CG * |Real.log δ| ^ (-(1 : ℝ) / 40) + εG
  have hR : 0 ≤ R := by dsimp [R]; positivity
  let globalTerm : Disorder → ℝ := fun ω => ∫ x, φ x *
    (globalLogError (criticalBeta ϑ M) m n M
      (evenExtension (cellAverage M fun y => Real.exp (h₀ y))) (latticePoint M x) ω -
      ∫ ω', globalLogError (criticalBeta ϑ M) m n M (fun _ => 1)
        (latticePoint M x) ω' ∂disorderLaw)
  have hGlobalSpatial := eLpNorm_integral_centeredGlobal_le (criticalBeta ϑ M) m n M
    (evenExtension (cellAverage M fun y => Real.exp (h₀ y))) φ hφ hφint R hR hGf hG1
  have hsum : eLpNorm (fun ω => localLogError (criticalBeta ϑ M) M m n φ ω +
      globalTerm ω) 2 disorderLaw ≤
      eLpNorm (fun ω => localLogError (criticalBeta ϑ M) M m n φ ω) 2 disorderLaw +
        eLpNorm globalTerm 2 disorderLaw := by
    exact eLpNorm_add_le (by norm_num)
  have hdecomp (ω : Disorder) := latticeSmoothingError_eq_local_add_global
    (criticalBeta ϑ M) hmEven hnEven hMeven hmle hnle h₀ φ hφ hφc ⟨M₂, hφM⟩ ω
  have hresult := calc
    eLpNorm (latticeSmoothingError (criticalBeta ϑ M) M M m m h₀ φ) 2 disorderLaw =
        eLpNorm (fun ω => localLogError (criticalBeta ϑ M) M m n φ ω +
          globalTerm ω) 2 disorderLaw := by
          apply eLpNorm_congr_ae
          exact Filter.Eventually.of_forall fun ω => by
            simpa [globalTerm] using hdecomp ω
    _ ≤ eLpNorm (fun ω => localLogError (criticalBeta ϑ M) M m n φ ω)
        2 disorderLaw + eLpNorm globalTerm 2 disorderLaw := hsum
  have hM1nonneg : 0 ≤ M₁ := le_trans
    (integral_nonneg (fun x => abs_nonneg (φ x))) hφL1
  have hLocalReal : eLpNorm (fun ω => localLogError (criticalBeta ϑ M) M m n φ ω)
      2 disorderLaw ≤ ENNReal.ofReal
      (CL * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε / 2) := by
    exact hLocalBound.trans (ENNReal.ofReal_le_ofReal (by
      have hp : 0 ≤ |Real.log δ| ^ (-(1 : ℝ) / 40) := Real.rpow_nonneg hLpos.le _
      have hcoeff₁ : CLraw * |Real.log δ| ^ (-(1 : ℝ) / 8) ≤
          |CLraw| * |Real.log δ| ^ (-(1 : ℝ) / 8) :=
        mul_le_mul_of_nonneg_right (le_abs_self CLraw) (by positivity)
      have hcoeff₂ : |CLraw| * |Real.log δ| ^ (-(1 : ℝ) / 8) ≤
          CL * |Real.log δ| ^ (-(1 : ℝ) / 40) := by
        dsimp [CL]
        calc
          _ ≤ |CLraw| * |Real.log δ| ^ (-(1 : ℝ) / 40) :=
            mul_le_mul_of_nonneg_left hpow (abs_nonneg CLraw)
          _ ≤ _ := mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)) hp
      linarith))
  have hGlobalReal : eLpNorm globalTerm 2 disorderLaw ≤ ENNReal.ofReal (2 * R * M₁) := by
    refine (hGlobalSpatial.2.trans (ENNReal.ofReal_le_ofReal ?_))
    exact mul_le_mul_of_nonneg_left hφL1 (by positivity)
  have hsumReal : eLpNorm (fun ω => localLogError (criticalBeta ϑ M) M m n φ ω)
      2 disorderLaw + eLpNorm globalTerm 2 disorderLaw ≤ ENNReal.ofReal
      ((CL + 2 * |M₁| * CG) * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε) := by
    calc
      _ ≤ ENNReal.ofReal (CL * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε / 2) +
          ENNReal.ofReal (2 * R * M₁) := add_le_add hLocalReal hGlobalReal
      _ = ENNReal.ofReal (CL * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε / 2 +
          2 * R * M₁) := by
            exact (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ ≤ ENNReal.ofReal
          ((CL + 2 * |M₁| * CG) * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε) := by
            apply ENNReal.ofReal_le_ofReal
            have hMabs : M₁ ≤ |M₁| := le_abs_self _
            have hpow0 : 0 ≤ |Real.log δ| ^ (-(1 : ℝ) / 40) := Real.rpow_nonneg hLpos.le _
            have hεsmall : 2 * M₁ * (ε / (4 * (|M₁| + 1))) ≤ ε / 2 := by
              have hden : 0 < 4 * (|M₁| + 1) := by positivity
              have hcoef : 2 * M₁ ≤ 2 * (|M₁| + 1) := by nlinarith [hMabs]
              have hdiv : 0 ≤ ε / (4 * (|M₁| + 1)) := by positivity
              calc
                _ ≤ 2 * (|M₁| + 1) * (ε / (4 * (|M₁| + 1))) :=
                  mul_le_mul_of_nonneg_right hcoef hdiv
                _ = ε / 2 := by
                  field_simp [ne_of_gt hden]
                  norm_num
            have hmain : 2 * M₁ * CG * |Real.log δ| ^ (-(1 : ℝ) / 40) ≤
                2 * |M₁| * CG * |Real.log δ| ^ (-(1 : ℝ) / 40) := by
              calc
                _ = M₁ * (2 * CG * |Real.log δ| ^ (-(1 : ℝ) / 40)) := by ring
                _ ≤ |M₁| * (2 * CG * |Real.log δ| ^ (-(1 : ℝ) / 40)) :=
                  mul_le_mul_of_nonneg_right hMabs (by positivity)
                _ = _ := by ring
            have hglobal : 2 * R * M₁ ≤
                2 * |M₁| * CG * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε / 2 := by
              dsimp [R, εG]
              calc
                _ = 2 * M₁ * CG * |Real.log δ| ^ (-(1 : ℝ) / 40) +
                    2 * M₁ * (ε / (4 * (|M₁| + 1)) ) := by ring
                _ ≤ _ := add_le_add hmain hεsmall
            calc
              _ ≤ CL * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε / 2 +
                  (2 * |M₁| * CG * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε / 2) :=
                    by
                      simpa [add_comm, add_left_comm, add_assoc] using
                        add_le_add_right hglobal
                          (CL * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε / 2)
              _ = (CL + 2 * |M₁| * CG) * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε := by ring
  have hresult' := hresult.trans hsumReal
  simpa [C, m] using hresult'


end Critical2DKPZ.Smoothing

end
