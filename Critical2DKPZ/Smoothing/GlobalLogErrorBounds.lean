/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Smoothing.Basic
public import Critical2DKPZ.Smoothing.Decomposition
public import Critical2DKPZ.Smoothing.Measurability
public import Critical2DKPZ.FutureProfiles.FreezingPast
public import Critical2DKPZ.FutureProfiles.ConditionalNegativeMoments
public import Critical2DKPZ.FutureProfiles.EndpointTranslation
public import Critical2DKPZ.FutureProfiles.SplitInputs
public import Critical2DKPZ.Polymer.BlockMeasurability
public import Critical2DKPZ.Smoothing.LogLpHelpers
public import Critical2DKPZ.Definitions.DisorderLawIsProbabilityMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! # Deterministic bounds for weighted global logarithmic errors -/

@[expose] public section

open MeasureTheory Filter

namespace Critical2DKPZ.Smoothing

/-- A positive constant `C` chosen so that, for `u v > 0`, `|log u - log v|` is at most
`C * |u - v| ^ (1/3) * (u ^ (-1/3) + v ^ (-1/3))`. -/
noncomputable def logHolderConstant : ℝ :=
  Classical.choose abs_log_sub_log_le_rpow

/-- The constant `logHolderConstant` is positive. -/
theorem logHolderConstant_pos : 0 < logHolderConstant :=
  (Classical.choose_spec abs_log_sub_log_le_rpow).1

private theorem abs_log_sub_log_le_rpow_fixed (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    |Real.log u - Real.log v| ≤
      logHolderConstant * |u - v| ^ ((1 : ℝ) / 3) *
        (u ^ (-(1 : ℝ) / 3) + v ^ (-(1 : ℝ) / 3)) :=
  (Classical.choose_spec abs_log_sub_log_le_rpow).2 u v hu hv

/-- The global logarithmic error is measurable in the disorder variable. -/
theorem measurable_globalLogError (β : ℝ) (m n N : ℕ) (f : Site → ℝ) (z : Site) :
    Measurable (globalLogError β m n N f z) := by
  have hν : ∀ w, Measurable (fun ω : Disorder => endpointDist β n z ω w) := by
    intro w
    exact Polymer.measurable_endpointDist β n z w
  have hη : ∀ w, Measurable (fun ω : Disorder => smoothedEndpointDist β m n z ω w) := by
    intro w
    exact Polymer.measurable_smoothedEndpointDist β m n z w
  have hX := measurable_profileP2Fun_param β n N f hν measurable_id
  have hY := measurable_profileP2Fun_param β n N f hη measurable_id
  unfold globalLogError
  exact hX.log.sub hY.log

/-- Spatial translation moves the starting site of the global error to the origin. -/
theorem globalLogError_translate (β : ℝ) (m n N : ℕ) (f : Site → ℝ) (z : Site)
    (ω : Disorder) :
    globalLogError β m n N f z ω =
      globalLogError β m n N (fun w => f (w + z)) 0
        (fun p => ω (p.1, p.2 + z)) := by
  unfold globalLogError
  rw [FutureProfiles.profileP2Fun_endpointDist_translate,
    FutureProfiles.profileP2Fun_smoothedEndpointDist_translate]

/-- The global error has the same `L²` norm at every site as the correspondingly translated
terminal weight at the origin. -/
theorem globalLogError_eLpNorm_translate (β : ℝ) (m n N : ℕ) (f : Site → ℝ) (z : Site) :
    eLpNorm (globalLogError β m n N f z) 2 disorderLaw =
      eLpNorm (globalLogError β m n N (fun w => f (w + z)) 0) 2 disorderLaw := by
  let shift : Disorder → Disorder := fun ω p => ω (p.1, p.2 + z)
  have hmp := FutureProfiles.measurePreserving_disorderShift z
  have hmeas : AEStronglyMeasurable
      (globalLogError β m n N (fun w => f (w + z)) 0) disorderLaw :=
    (measurable_globalLogError β m n N (fun w => f (w + z)) 0).aestronglyMeasurable
  calc
    eLpNorm (globalLogError β m n N f z) 2 disorderLaw =
        eLpNorm (fun ω => globalLogError β m n N (fun w => f (w + z)) 0 (shift ω))
          2 disorderLaw := by
            apply eLpNorm_congr_ae
            exact Filter.Eventually.of_forall (globalLogError_translate β m n N f z)
    _ = eLpNorm (globalLogError β m n N (fun w => f (w + z)) 0) 2 disorderLaw := by
      exact eLpNorm_comp_measurePreserving hmeas hmp

/-- Changing a normalized profile's terminal weight changes its log by at most the terminal
log bound. Applied twice, this controls the difference between weighted and flat global errors. -/
theorem abs_globalLogError_weighted_sub_flat_le (β : ℝ) (n N : ℕ)
    (ν ν' : Site → ℝ) (A B : Finset Site)
    (hνA : ∀ w ∉ A, ν w = 0) (hν'A : ∀ w ∉ B, ν' w = 0)
    (hν0 : ∀ w, 0 ≤ ν w) (hν'0 : ∀ w, 0 ≤ ν' w)
    (hν1 : ∑ w ∈ A, ν w = 1) (hν'1 : ∑ w ∈ B, ν' w = 1)
    (f : Site → ℝ) (H : ℝ) (hf : ∀ w, 0 < f w ∧ |Real.log (f w)| ≤ H)
    (ω : Disorder) :
    |(Real.log (profileP2Fun β n N ν f ω) -
        Real.log (profileP2Fun β n N ν' f ω)) -
      (Real.log (profileP2Fun β n N ν (fun _ => 1) ω) -
        Real.log (profileP2Fun β n N ν' (fun _ => 1) ω))| ≤ 2 * H := by
  have hν := FutureProfiles.abs_log_profileP2Fun_sub_le β n N ν A hνA hν0 hν1 f H hf ω
  have hν' := FutureProfiles.abs_log_profileP2Fun_sub_le β n N ν' B hν'A hν'0 hν'1 f H hf ω
  have halg :
      (Real.log (profileP2Fun β n N ν f ω) - Real.log (profileP2Fun β n N ν' f ω)) -
          (Real.log (profileP2Fun β n N ν (fun _ => 1) ω) -
            Real.log (profileP2Fun β n N ν' (fun _ => 1) ω)) =
        (Real.log (profileP2Fun β n N ν f ω) -
            Real.log (profileP2Fun β n N ν (fun _ => 1) ω)) -
          (Real.log (profileP2Fun β n N ν' f ω) -
            Real.log (profileP2Fun β n N ν' (fun _ => 1) ω)) := by ring
  rw [halg]
  calc
    _ ≤ |Real.log (profileP2Fun β n N ν f ω) -
          Real.log (profileP2Fun β n N ν (fun _ => 1) ω)| +
        |Real.log (profileP2Fun β n N ν' f ω) -
          Real.log (profileP2Fun β n N ν' (fun _ => 1) ω)| := abs_sub _ _
    _ ≤ H + H := add_le_add hν hν'
    _ = 2 * H := by ring

/-- On an event, the expected logarithmic difference is bounded by a fractional moment of the difference and inverse half-moments; the logarithmic difference is integrable on that event. -/
theorem integrableOn_abs_log_sub_le_of_neg_half {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (G : Set Ω) (X Y : Ω → ℝ)
    (hXmeas : Measurable X) (hYmeas : Measurable Y)
    (hXpos : ∀ ω, 0 < X ω) (hYpos : ∀ ω, 0 < Y ω)
    (hDint : Integrable (fun ω => |X ω - Y ω|) (μ.restrict G))
    (hXnegint : Integrable (fun ω => X ω ^ (-(1 : ℝ) / 2)) (μ.restrict G))
    (hYnegint : Integrable (fun ω => Y ω ^ (-(1 : ℝ) / 2)) (μ.restrict G)) :
    Integrable (fun ω => |Real.log (X ω) - Real.log (Y ω)|) (μ.restrict G) ∧
      ∫ ω, |Real.log (X ω) - Real.log (Y ω)| ∂(μ.restrict G) ≤
        logHolderConstant * (∫ ω, |X ω - Y ω| ∂(μ.restrict G)) ^ ((1 : ℝ) / 3) *
          ((∫ ω, X ω ^ (-(1 : ℝ) / 2) ∂(μ.restrict G)) ^ ((2 : ℝ) / 3) +
            (∫ ω, Y ω ^ (-(1 : ℝ) / 2) ∂(μ.restrict G)) ^ ((2 : ℝ) / 3)) := by
  classical
  let D : Ω → ℝ := fun ω => |X ω - Y ω|
  let IX : Ω → ℝ := fun ω => X ω ^ (-(1 : ℝ) / 2)
  let IY : Ω → ℝ := fun ω => Y ω ^ (-(1 : ℝ) / 2)
  let F : Ω → ℝ := fun ω => D ω ^ ((1 : ℝ) / 3)
  let GX : Ω → ℝ := fun ω => IX ω ^ ((2 : ℝ) / 3)
  let GY : Ω → ℝ := fun ω => IY ω ^ ((2 : ℝ) / 3)
  have hDnonneg (ω : Ω) : 0 ≤ D ω := by simp [D]
  have hIXpos (ω : Ω) : 0 < IX ω := by
    dsimp [IX]
    exact Real.rpow_pos_of_pos (hXpos ω) _
  have hIYpos (ω : Ω) : 0 < IY ω := by
    dsimp [IY]
    exact Real.rpow_pos_of_pos (hYpos ω) _
  have hDmem1 : MemLp D 1 (μ.restrict G) := by
    exact (memLp_one_iff_integrable).2 (by simpa [D] using hDint)
  have hIXmem1 : MemLp IX 1 (μ.restrict G) := by
    exact (memLp_one_iff_integrable).2 (by simpa [IX] using hXnegint)
  have hIYmem1 : MemLp IY 1 (μ.restrict G) := by
    exact (memLp_one_iff_integrable).2 (by simpa [IY] using hYnegint)
  have hFmem : MemLp F (ENNReal.ofReal 3) (μ.restrict G) := by
    have h := hDmem1.norm_rpow_div (ENNReal.ofReal ((1 : ℝ) / 3))
    simpa [F, D, hDnonneg, ENNReal.toReal_ofReal (by norm_num : 0 ≤ (1 : ℝ) / 3)] using h
  have hGXmem : MemLp GX (ENNReal.ofReal ((3 : ℝ) / 2)) (μ.restrict G) := by
    have h := hIXmem1.norm_rpow_div (ENNReal.ofReal ((2 : ℝ) / 3))
    have hq : (ENNReal.ofReal ((2 : ℝ) / 3))⁻¹ = ENNReal.ofReal ((3 : ℝ) / 2) := by
      rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2 / 3)]
      norm_num
    have h' : MemLp (fun ω => |IX ω| ^ ((2 : ℝ) / 3))
        (ENNReal.ofReal ((3 : ℝ) / 2)) (μ.restrict G) := by
      simpa [IX, hq, ENNReal.toReal_ofReal (by norm_num : 0 ≤ (2 : ℝ) / 3)] using h
    have heq : (fun ω => |IX ω| ^ ((2 : ℝ) / 3)) = GX := by
      funext ω
      simp [GX, abs_of_pos (hIXpos ω)]
    rw [heq] at h'
    exact h'
  have hGYmem : MemLp GY (ENNReal.ofReal ((3 : ℝ) / 2)) (μ.restrict G) := by
    have h := hIYmem1.norm_rpow_div (ENNReal.ofReal ((2 : ℝ) / 3))
    have hq : (ENNReal.ofReal ((2 : ℝ) / 3))⁻¹ = ENNReal.ofReal ((3 : ℝ) / 2) := by
      rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2 / 3)]
      norm_num
    have h' : MemLp (fun ω => |IY ω| ^ ((2 : ℝ) / 3))
        (ENNReal.ofReal ((3 : ℝ) / 2)) (μ.restrict G) := by
      simpa [IY, hq, ENNReal.toReal_ofReal (by norm_num : 0 ≤ (2 : ℝ) / 3)] using h
    have heq : (fun ω => |IY ω| ^ ((2 : ℝ) / 3)) = GY := by
      funext ω
      simp [GY, abs_of_pos (hIYpos ω)]
    rw [heq] at h'
    exact h'
  have hFnonneg : ∀ᵐ ω ∂(μ.restrict G), 0 ≤ F ω :=
    Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (hDnonneg ω) _
  have hGXnonneg : ∀ᵐ ω ∂(μ.restrict G), 0 ≤ GX ω :=
    Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (hIXpos ω).le _
  have hGYnonneg : ∀ᵐ ω ∂(μ.restrict G), 0 ≤ GY ω :=
    Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (hIYpos ω).le _
  have hconj : (3 : ℝ).HolderConjugate ((3 : ℝ) / 2) := by
    apply Real.holderConjugate_iff.mpr
    constructor <;> norm_num
  have hHolderX := integral_mul_le_Lp_mul_Lq_of_nonneg hconj hFnonneg hGXnonneg
    hFmem hGXmem
  have hHolderY := integral_mul_le_Lp_mul_Lq_of_nonneg hconj hFnonneg hGYnonneg
    hFmem hGYmem
  have hFpow (ω : Ω) : F ω ^ (3 : ℝ) = D ω := by
    dsimp [F]
    rw [← Real.rpow_mul (hDnonneg ω)]
    norm_num
  have hGXpow (ω : Ω) : GX ω ^ ((3 : ℝ) / 2) = IX ω := by
    dsimp [GX]
    rw [← Real.rpow_mul (hIXpos ω).le]
    norm_num
  have hGYpow (ω : Ω) : GY ω ^ ((3 : ℝ) / 2) = IY ω := by
    dsimp [GY]
    rw [← Real.rpow_mul (hIYpos ω).le]
    norm_num
  have hHolderX' :
      ∫ ω, F ω * GX ω ∂(μ.restrict G) ≤
        (∫ ω, D ω ∂(μ.restrict G)) ^ ((1 : ℝ) / 3) *
          (∫ ω, IX ω ∂(μ.restrict G)) ^ ((2 : ℝ) / 3) := by
    calc
      _ ≤ (∫ ω, F ω ^ (3 : ℝ) ∂(μ.restrict G)) ^ ((1 : ℝ) / 3) *
          (∫ ω, GX ω ^ ((3 : ℝ) / 2) ∂(μ.restrict G)) ^ (1 / ((3 : ℝ) / 2)) := hHolderX
      _ = _ := by
        rw [integral_congr_ae (Filter.Eventually.of_forall hFpow),
          integral_congr_ae (Filter.Eventually.of_forall hGXpow)]
        norm_num
  have hHolderY' :
      ∫ ω, F ω * GY ω ∂(μ.restrict G) ≤
        (∫ ω, D ω ∂(μ.restrict G)) ^ ((1 : ℝ) / 3) *
          (∫ ω, IY ω ∂(μ.restrict G)) ^ ((2 : ℝ) / 3) := by
    calc
      _ ≤ (∫ ω, F ω ^ (3 : ℝ) ∂(μ.restrict G)) ^ ((1 : ℝ) / 3) *
          (∫ ω, GY ω ^ ((3 : ℝ) / 2) ∂(μ.restrict G)) ^ (1 / ((3 : ℝ) / 2)) := hHolderY
      _ = _ := by
        rw [integral_congr_ae (Filter.Eventually.of_forall hFpow),
          integral_congr_ae (Filter.Eventually.of_forall hGYpow)]
        norm_num
  have hmulX : Integrable (fun ω => F ω * GX ω) (μ.restrict G) := by
    have htriple : ENNReal.HolderTriple (ENNReal.ofReal ((3 : ℝ) / 2))
        (ENNReal.ofReal 3) 1 := by
      simpa [add_comm] using hconj.ennrealOfReal.symm
    have hmem : MemLp (fun ω => F ω * GX ω) 1 (μ.restrict G) := by
      convert (@MemLp.mul Ω inferInstance ℝ inferInstance (μ.restrict G)
        (ENNReal.ofReal ((3 : ℝ) / 2)) (ENNReal.ofReal 3) 1 F GX hGXmem hFmem htriple) using 1
      ext ω
      rw [Pi.mul_apply, mul_comm]
    exact (memLp_one_iff_integrable.mp hmem).congr (Filter.Eventually.of_forall fun ω => by ring)
  have hmulY : Integrable (fun ω => F ω * GY ω) (μ.restrict G) := by
    have htriple : ENNReal.HolderTriple (ENNReal.ofReal ((3 : ℝ) / 2))
        (ENNReal.ofReal 3) 1 := by
      simpa [add_comm] using hconj.ennrealOfReal.symm
    have hmem : MemLp (fun ω => F ω * GY ω) 1 (μ.restrict G) := by
      convert (@MemLp.mul Ω inferInstance ℝ inferInstance (μ.restrict G)
        (ENNReal.ofReal ((3 : ℝ) / 2)) (ENNReal.ofReal 3) 1 F GY hGYmem hFmem htriple) using 1
      ext ω
      rw [Pi.mul_apply, mul_comm]
    exact (memLp_one_iff_integrable.mp hmem).congr (Filter.Eventually.of_forall fun ω => by ring)
  have hbound (ω : Ω) :
      |Real.log (X ω) - Real.log (Y ω)| ≤
        logHolderConstant * (F ω * GX ω + F ω * GY ω) := by
    have h := abs_log_sub_log_le_rpow_fixed (X ω) (Y ω) (hXpos ω) (hYpos ω)
    have hGX : GX ω = (X ω) ^ (-(1 : ℝ) / 3) := by
      dsimp [GX, IX]
      rw [← Real.rpow_mul (hXpos ω).le]
      congr 1
      ring
    have hGY : GY ω = (Y ω) ^ (-(1 : ℝ) / 3) := by
      dsimp [GY, IY]
      rw [← Real.rpow_mul (hYpos ω).le]
      congr 1
      ring
    dsimp [F, D]
    rw [hGX, hGY]
    calc
      |Real.log (X ω) - Real.log (Y ω)| ≤
          logHolderConstant * |X ω - Y ω| ^ ((1 : ℝ) / 3) *
            (X ω ^ (-(1 : ℝ) / 3) + Y ω ^ (-(1 : ℝ) / 3)) := h
      _ = logHolderConstant * (|X ω - Y ω| ^ ((1 : ℝ) / 3) * X ω ^ (-(1 : ℝ) / 3) +
            |X ω - Y ω| ^ ((1 : ℝ) / 3) * Y ω ^ (-(1 : ℝ) / 3)) := by ring
  have hmajor : Integrable
      (fun ω => logHolderConstant * (F ω * GX ω + F ω * GY ω))
      (μ.restrict G) := by
    exact (hmulX.add hmulY).const_mul logHolderConstant
  have hlogmeas : Measurable (fun ω => |Real.log (X ω) - Real.log (Y ω)|) :=
    (hXmeas.log.sub hYmeas.log).abs
  have hlogint : Integrable (fun ω => |Real.log (X ω) - Real.log (Y ω)|)
      (μ.restrict G) := by
    refine hmajor.mono' hlogmeas.aestronglyMeasurable ?_
    filter_upwards [] with ω
    have hF0 : 0 ≤ F ω := Real.rpow_nonneg (hDnonneg ω) _
    have hGX0 : 0 ≤ GX ω := Real.rpow_nonneg (hIXpos ω).le _
    have hGY0 : 0 ≤ GY ω := Real.rpow_nonneg (hIYpos ω).le _
    have hmaj : 0 ≤ logHolderConstant * (F ω * GX ω + F ω * GY ω) :=
      mul_nonneg logHolderConstant_pos.le
        (add_nonneg (mul_nonneg hF0 hGX0) (mul_nonneg hF0 hGY0))
    simpa only [Real.norm_eq_abs, abs_abs, abs_of_nonneg hmaj] using hbound ω
  refine ⟨hlogint, ?_⟩
  have hIntegral := integral_mono hlogint hmajor hbound
  calc
    _ ≤ logHolderConstant * (∫ ω, F ω * GX ω ∂(μ.restrict G) +
          ∫ ω, F ω * GY ω ∂(μ.restrict G)) := by
        simpa [integral_add hmulX hmulY, integral_const_mul] using hIntegral
    _ ≤ logHolderConstant * ((∫ ω, D ω ∂(μ.restrict G)) ^ ((1 : ℝ) / 3) *
            (∫ ω, IX ω ∂(μ.restrict G)) ^ ((2 : ℝ) / 3) +
          (∫ ω, D ω ∂(μ.restrict G)) ^ ((1 : ℝ) / 3) *
            (∫ ω, IY ω ∂(μ.restrict G)) ^ ((2 : ℝ) / 3)) := by
        apply mul_le_mul_of_nonneg_left (add_le_add hHolderX' hHolderY')
          logHolderConstant_pos.le
    _ = _ := by ring

/-- On a subevent of a probability space, an integrable nonnegative energy controls its
three-eighths moment by the same power of its integral. -/
private theorem integrableOn_rpow_three_eighth_le (G : Set Disorder)
    (E : Disorder → ℝ) (hE0 : ∀ ω, 0 ≤ E ω)
    (hEint : IntegrableOn E G disorderLaw) :
    IntegrableOn (fun ω => E ω ^ ((3 : ℝ) / 8)) G disorderLaw ∧
      ∫ ω in G, E ω ^ ((3 : ℝ) / 8) ∂disorderLaw ≤
        (∫ ω in G, E ω ∂disorderLaw) ^ ((3 : ℝ) / 8) := by
  let μG := disorderLaw.restrict G
  have hEmem : MemLp E 1 μG := memLp_one_iff_integrable.mpr hEint
  let F : Disorder → ℝ := fun ω => E ω ^ ((3 : ℝ) / 8)
  have hq : (ENNReal.ofReal ((3 : ℝ) / 8))⁻¹ = ENNReal.ofReal ((8 : ℝ) / 3) := by
    rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 3 / 8)]
    norm_num
  have hFmem : MemLp F (ENNReal.ofReal ((8 : ℝ) / 3)) μG := by
    have h := hEmem.norm_rpow_div (ENNReal.ofReal ((3 : ℝ) / 8))
    have h' : MemLp (fun ω => |E ω| ^ ((3 : ℝ) / 8))
        (ENNReal.ofReal ((8 : ℝ) / 3)) μG := by
      simpa [hq, ENNReal.toReal_ofReal (by norm_num : 0 ≤ (3 : ℝ) / 8)] using h
    have heq : (fun ω => |E ω| ^ ((3 : ℝ) / 8)) = F := by
      funext ω
      simp [F, abs_of_nonneg (hE0 ω)]
    rw [heq] at h'
    exact h'
  have hFint : Integrable F μG :=
    memLp_one_iff_integrable.mp (hFmem.mono_exponent (by norm_num))
  have hFnonneg : ∀ᵐ ω ∂μG, 0 ≤ F ω :=
    Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (hE0 ω) _
  have h1mem : MemLp (fun _ : Disorder => (1 : ℝ))
      (ENNReal.ofReal ((8 : ℝ) / 5)) μG := memLp_const 1
  have h1nonneg : ∀ᵐ ω ∂μG, 0 ≤ (1 : ℝ) := Filter.Eventually.of_forall fun _ => zero_le_one
  have hconj : ((8 : ℝ) / 3).HolderConjugate ((8 : ℝ) / 5) := by
    apply Real.holderConjugate_iff.mpr
    constructor <;> norm_num
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg hconj hFnonneg h1nonneg
    hFmem h1mem
  have hFpow (ω : Disorder) : F ω ^ ((8 : ℝ) / 3) = E ω := by
    dsimp [F]
    rw [← Real.rpow_mul (hE0 ω)]
    norm_num
  have hmass : (μG Set.univ).toReal ≤ 1 := by
    have hmeasure : μG Set.univ ≤ 1 := by
      change disorderLaw.restrict G Set.univ ≤ 1
      rw [Measure.restrict_apply_univ]
      calc
        disorderLaw G ≤ disorderLaw Set.univ := measure_mono (Set.subset_univ G)
        _ = 1 := by simp
    exact ENNReal.toReal_mono ENNReal.one_ne_top hmeasure
  have hmassR : 0 ≤ (μG Set.univ).toReal := ENNReal.toReal_nonneg
  have hmassPow : (μG Set.univ).toReal ^ ((5 : ℝ) / 8) ≤ 1 :=
    Real.rpow_le_one hmassR hmass (by norm_num)
  have hEintNonneg : 0 ≤ ∫ ω in G, E ω ∂disorderLaw := integral_nonneg_of_ae
    (Filter.Eventually.of_forall hE0)
  have hMoment :
      ∫ ω in G, F ω ∂disorderLaw ≤
        (∫ ω in G, E ω ∂disorderLaw) ^ ((3 : ℝ) / 8) := by
    have hEqF : (∫ ω, F ω ∂μG) = ∫ ω in G, F ω ∂disorderLaw := rfl
    have hEqPow : (∫ ω, F ω ^ ((8 : ℝ) / 3) ∂μG) = ∫ ω in G, E ω ∂disorderLaw :=
      integral_congr_ae (Filter.Eventually.of_forall hFpow)
    have hEqOne : (∫ ω, (1 : ℝ) ^ ((8 : ℝ) / 5) ∂μG) = (μG Set.univ).toReal := by
      simp [μG, Measure.real]
    have h := hHolder
    simp only [mul_one] at h
    rw [hEqPow, hEqOne] at h
    have hpow : 1 / ((8 : ℝ) / 3) = (3 : ℝ) / 8 := by norm_num
    rw [hpow] at h
    have hpow' : 1 / ((8 : ℝ) / 5) = (5 : ℝ) / 8 := by norm_num
    rw [hpow'] at h
    have hleft : 0 ≤ (∫ ω in G, E ω ∂disorderLaw) ^ ((3 : ℝ) / 8) :=
      Real.rpow_nonneg hEintNonneg _
    have hscaled := mul_le_mul_of_nonneg_left hmassPow hleft
    have hbound := h.trans (by simpa [mul_one] using hscaled)
    calc
      ∫ ω in G, F ω ∂disorderLaw = ∫ ω, F ω ∂μG := hEqF.symm
      _ ≤ _ := hbound
  have hFOn : IntegrableOn F G disorderLaw := by
    change Integrable F (disorderLaw.restrict G)
    exact hFint
  refine ⟨?_, hMoment⟩
  simpa [F] using hFOn

/-- Conditional negative moments give the inverse-half moment needed by the log-Hölder estimate;
the companion proves that the restricted inverse moment is integrable. -/
theorem integrableOn_inv_sqrt_profileP2Fun_le (β : ℝ) (hβ : 0 ≤ β)
    {a b : ℕ} (hab : a ≤ b) (η : Disorder → Site → ℝ) (A : Finset Site)
    (hsupp : ∀ ω w, w ∉ A → η ω w = 0)
    (hnn : ∀ ω w, 0 ≤ η ω w) (hmass : ∀ ω, ∑ w ∈ A, η ω w = 1)
    (hmeas : ∀ w, Measurable[disorderPast a] (η · w)) (G : Set Disorder)
    (hG : MeasurableSet[disorderPast a] G) :
    IntegrableOn (fun ω => profileP2Fun β a b (η ω) (fun _ => 1) ω ^ (-(1 : ℝ) / 2))
        G disorderLaw ∧
      ∫ ω in G, profileP2Fun β a b (η ω) (fun _ => 1) ω ^ (-(1 : ℝ) / 2)
          ∂disorderLaw ≤
        (∫ ω in G, FutureProfiles.futureEnergy β a b (η ω) ∂disorderLaw) ^ ((3 : ℝ) / 8) := by
  have hbdd : ∃ B : ℝ, ∀ ω w, |η ω w| ≤ B := by
    refine ⟨1, ?_⟩
    intro ω w
    rw [abs_of_nonneg (hnn ω w)]
    by_cases hw : w ∈ A
    · exact (Finset.single_le_sum (fun v hv => hnn ω v) hw).trans_eq (hmass ω)
    · rw [hsupp ω w hw]
      norm_num
  have hnegInt : Integrable
      (fun ω => profileP2Fun β a b (η ω) (fun _ => 1) ω ^ (-(1 : ℝ) / 2)) disorderLaw :=
    by
      have h := FutureProfiles.integrableOn_rpow_neg_profileP2Fun_pastFrozen β hab η A hsupp hnn
        hmass hmeas (by norm_num : 0 ≤ (1 : ℝ) / 2)
      have hexp : (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) := by ring
      simpa only [hexp] using h
  have henergyData := FutureProfiles.integrableOn_profileP2Fun_sq_eq β hab η A hsupp hbdd
    hmeas G
  have hEnergyInt : IntegrableOn (fun ω => FutureProfiles.futureEnergy β a b (η ω))
      G disorderLaw := henergyData.2
  have hroot := integrableOn_rpow_three_eighth_le G
    (fun ω => FutureProfiles.futureEnergy β a b (η ω))
    (fun ω => FutureProfiles.futureEnergy_nonneg β a b (η ω)) hEnergyInt
  have hK := FutureProfiles.setIntegral_rpow_neg_profileP2Fun_le β hβ hab η A hsupp hnn
    hmass hmeas G hG (p := (1 : ℝ) / 2) (by norm_num)
  have hK' :
      ∫ ω in G, profileP2Fun β a b (η ω) (fun _ => 1) ω ^ (-(1 : ℝ) / 2)
          ∂disorderLaw ≤
        ∫ ω in G, FutureProfiles.futureEnergy β a b (η ω) ^ ((3 : ℝ) / 8)
          ∂disorderLaw := by
    convert hK using 1 <;> norm_num
  refine ⟨hnegInt.integrableOn, ?_⟩
  exact hK'.trans hroot.2

/-- A bounded positive terminal weight changes an inverse square-root profile moment by at
most its deterministic exponential factor. The integrability conclusion accompanies the
restricted integral bound. -/
theorem integrableOn_inv_sqrt_weighted_profileP2Fun_le
    (β : ℝ) (a b : ℕ) (η : Disorder → Site → ℝ) (A : Finset Site)
    (hsupp : ∀ ω w, w ∉ A → η ω w = 0)
    (hnn : ∀ ω w, 0 ≤ η ω w) (hmass : ∀ ω, ∑ w ∈ A, η ω w = 1)
    (f : Site → ℝ) (H : ℝ)
    (hf : ∀ w, 0 < f w ∧ |Real.log (f w)| ≤ H)
    (G : Set Disorder)
    (hflatInv : IntegrableOn
      (fun ω => profileP2Fun β a b (η ω) (fun _ => 1) ω ^ (-(1 : ℝ) / 2))
      G disorderLaw)
    (hweightedMeas : Measurable
      (fun ω => profileP2Fun β a b (η ω) f ω)) :
    IntegrableOn
      (fun ω => profileP2Fun β a b (η ω) f ω ^ (-(1 : ℝ) / 2))
      G disorderLaw ∧
      ∫ ω in G, profileP2Fun β a b (η ω) f ω ^ (-(1 : ℝ) / 2) ∂disorderLaw ≤
        Real.exp (H / 2) *
          ∫ ω in G, profileP2Fun β a b (η ω) (fun _ => 1) ω ^ (-(1 : ℝ) / 2)
            ∂disorderLaw := by
  have hpos (ω : Disorder) :
      0 < profileP2Fun β a b (η ω) (fun _ => 1) ω :=
    OnePoint.profileP2Fun_pos_of_normalized β a b (η ω) A (hsupp ω) (hnn ω)
      (hmass ω) ω
  have hweightPos (ω : Disorder) : 0 < profileP2Fun β a b (η ω) f ω := by
    have hνpos : ∃ w ∈ A, 0 < η ω w := by
      have hsum : 0 < ∑ w ∈ A, η ω w := by rw [hmass ω]; norm_num
      exact (Finset.sum_pos_iff_of_nonneg (fun w hw => hnn ω w)).mp hsum
    exact profileP2Fun_pos_terminal β a b (η ω) f A (hsupp ω) (hnn ω)
      hνpos (fun w => (hf w).1) ω
  have hlogbound (ω : Disorder) :=
    FutureProfiles.abs_log_profileP2Fun_sub_le β a b (η ω) A (hsupp ω)
      (hnn ω) (hmass ω) f H hf ω
  have hpoint (ω : Disorder) :
      profileP2Fun β a b (η ω) f ω ^ (-(1 : ℝ) / 2) ≤
        Real.exp (H / 2) *
          profileP2Fun β a b (η ω) (fun _ => 1) ω ^ (-(1 : ℝ) / 2) := by
    have hlog :
        Real.log (profileP2Fun β a b (η ω) (fun _ => 1) ω) -
            Real.log (profileP2Fun β a b (η ω) f ω) ≤ H := by
      exact (abs_le.mp (by simpa [abs_sub_comm] using hlogbound ω)).2
    have hlog' := mul_le_mul_of_nonneg_left hlog
      (show (0 : ℝ) ≤ (1 : ℝ) / 2 by norm_num)
    have hexpWeighted := Real.rpow_def_of_pos (hweightPos ω)
      (-(1 : ℝ) / 2)
    have hexpFlat := Real.rpow_def_of_pos (hpos ω)
      (-(1 : ℝ) / 2)
    rw [hexpWeighted, hexpFlat]
    calc
      Real.exp (Real.log (profileP2Fun β a b (η ω) f ω) * (-(1 : ℝ) / 2)) ≤
          Real.exp (H / 2 +
            Real.log (profileP2Fun β a b (η ω) (fun _ => 1) ω) *
              (-(1 : ℝ) / 2)) := by
                apply Real.exp_le_exp.mpr
                nlinarith [hlog']
      _ = Real.exp (H / 2) *
          Real.exp (Real.log (profileP2Fun β a b (η ω) (fun _ => 1) ω) *
            (-(1 : ℝ) / 2)) := by rw [Real.exp_add]
  have hweightedMeas' :
      Measurable (fun ω => profileP2Fun β a b (η ω) f ω ^ (-(1 : ℝ) / 2)) := by
    have heq : (fun ω => profileP2Fun β a b (η ω) f ω ^ (-(1 : ℝ) / 2)) =
        fun ω => Real.exp (-(1 : ℝ) / 2 *
          Real.log (profileP2Fun β a b (η ω) f ω)) := by
      funext ω
      rw [Real.rpow_def_of_pos (hweightPos ω)]
      congr 1
      ring
    rw [heq]
    exact Real.measurable_exp.comp (measurable_const.mul hweightedMeas.log)
  have hmajor : IntegrableOn
      (fun ω => Real.exp (H / 2) *
        profileP2Fun β a b (η ω) (fun _ => 1) ω ^ (-(1 : ℝ) / 2))
      G disorderLaw := hflatInv.const_mul _
  have hweightedInt : IntegrableOn
      (fun ω => profileP2Fun β a b (η ω) f ω ^ (-(1 : ℝ) / 2))
      G disorderLaw := by
    refine hmajor.mono' hweightedMeas'.aestronglyMeasurable ?_
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hweightPos ω).le _)]
    have hmajorNonneg : 0 ≤ Real.exp (H / 2) *
        profileP2Fun β a b (η ω) (fun _ => 1) ω ^ (-(1 : ℝ) / 2) :=
      mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg (hpos ω).le _)
    simpa only [Real.norm_eq_abs, abs_of_nonneg hmajorNonneg] using hpoint ω
  have hIntegral := integral_mono hweightedInt hmajor hpoint
  refine ⟨hweightedInt, ?_⟩
  calc
    ∫ ω in G, profileP2Fun β a b (η ω) f ω ^ (-(1 : ℝ) / 2) ∂disorderLaw ≤
        ∫ ω in G, Real.exp (H / 2) *
          profileP2Fun β a b (η ω) (fun _ => 1) ω ^ (-(1 : ℝ) / 2) ∂disorderLaw :=
      hIntegral
    _ = Real.exp (H / 2) *
        ∫ ω in G, profileP2Fun β a b (η ω) (fun _ => 1) ω ^ (-(1 : ℝ) / 2)
          ∂disorderLaw := by rw [integral_const_mul]

/-- On a past event, the weighted global error has an integrable logarithm and the expected
log-Hölder bound in terms of the profile difference and inverse half moments. -/
private theorem integrableOn_globalLogError_good_event (β : ℝ) (hβ : 0 ≤ β)
    {m n N : ℕ} (hmn : m ≤ n) (hnN : n ≤ N) (f : Site → ℝ) (H : ℝ)
    (hf : ∀ w, 0 < f w ∧ |Real.log (f w)| ≤ H)
    (G : Set Disorder) (hG : MeasurableSet[disorderPast n] G)
    (Kη Kξ : ℝ)
    (hηsq : ∫ ω in G,
      profileP2Fun β n N (endpointDist β n 0 ω) (fun _ => 1) ω ^ 2 ∂disorderLaw ≤ Kη)
    (hξsq : ∫ ω in G,
      profileP2Fun β n N (smoothedEndpointDist β m n 0 ω) (fun _ => 1) ω ^ 2
        ∂disorderLaw ≤ Kξ) :
    IntegrableOn (fun ω => |globalLogError β m n N f 0 ω|) G disorderLaw ∧
      ∫ ω in G, |globalLogError β m n N f 0 ω| ∂disorderLaw ≤
          logHolderConstant * (∫ ω in G,
            |profileP2Fun β n N (endpointDist β n 0 ω) f ω -
              profileP2Fun β n N (smoothedEndpointDist β m n 0 ω) f ω|
              ∂disorderLaw) ^ ((1 : ℝ) / 3) *
          ((Real.exp (H / 2) * Kη ^ ((3 : ℝ) / 8)) ^ ((2 : ℝ) / 3) +
            (Real.exp (H / 2) * Kξ ^ ((3 : ℝ) / 8)) ^ ((2 : ℝ) / 3)) := by
  classical
  let η : Disorder → Site → ℝ := fun ω w => endpointDist β n 0 ω w
  let ξ : Disorder → Site → ℝ := fun ω w => smoothedEndpointDist β m n 0 ω w
  let A : Finset Site := Polymer.endpoints 0 n
  let B : Finset Site := (Polymer.endpoints 0 m).biUnion
    (fun y => Polymer.endpoints y (n - m))
  have hηsupp : ∀ ω w, w ∉ A → η ω w = 0 := by
    intro ω w hw
    exact (endpointDist_probability β n 0 ω).1 w (by simpa [A] using hw)
  have hηnonneg : ∀ ω w, 0 ≤ η ω w := by
    intro ω w
    exact (endpointDist_probability β n 0 ω).2.1 w
  have hηmass : ∀ ω, ∑ w ∈ A, η ω w = 1 := by
    intro ω
    exact (endpointDist_probability β n 0 ω).2.2
  have hξsupp : ∀ ω w, w ∉ B → ξ ω w = 0 := by
    intro ω w hw
    exact (smoothedEndpointDist_probability β hmn 0 ω).1 w (by simpa [B] using hw)
  have hξnonneg : ∀ ω w, 0 ≤ ξ ω w := by
    intro ω w
    exact (smoothedEndpointDist_probability β hmn 0 ω).2.1 w
  have hξmass : ∀ ω, ∑ w ∈ B, ξ ω w = 1 := by
    intro ω
    exact (smoothedEndpointDist_probability β hmn 0 ω).2.2
  have hηpast : ∀ w, Measurable[disorderPast n] (η · w) := by
    intro w
    exact Polymer.measurable_endpointDist_past β n 0 w
  have hξpast : ∀ w, Measurable[disorderPast n] (ξ · w) := by
    intro w
    have hblock := Polymer.measurable_smoothedEndpointDist_block β m n hmn 0 w
    have hle : Gaussian.disorderBlock m n ≤ disorderPast n := by
      rw [← Gaussian.disorderBlock_zero n]
      exact Gaussian.disorderBlock_mono (Nat.zero_le m) (Nat.le_refl n)
    exact hblock.mono hle le_rfl
  have hηbdd : ∃ K : ℝ, ∀ ω w, |η ω w| ≤ K := by
    refine ⟨1, ?_⟩
    intro ω w
    rw [abs_of_nonneg (hηnonneg ω w)]
    by_cases hw : w ∈ A
    · exact (Finset.single_le_sum (fun v hv => hηnonneg ω v) hw).trans_eq (hηmass ω)
    · rw [hηsupp ω w hw]
      norm_num
  have hξbdd : ∃ K : ℝ, ∀ ω w, |ξ ω w| ≤ K := by
    refine ⟨1, ?_⟩
    intro ω w
    rw [abs_of_nonneg (hξnonneg ω w)]
    by_cases hw : w ∈ B
    · exact (Finset.single_le_sum (fun v hv => hξnonneg ω v) hw).trans_eq (hξmass ω)
    · rw [hξsupp ω w hw]
      norm_num
  have hlogUpper (w : Site) : Real.log (f w) ≤ H := (abs_le.mp (hf w).2).2
  have hfBound : ∀ w, |f w| ≤ Real.exp H := by
    intro w
    rw [abs_of_pos (hf w).1]
    calc
      f w = Real.exp (Real.log (f w)) := (Real.exp_log (hf w).1).symm
      _ ≤ Real.exp H := Real.exp_le_exp.mpr (hlogUpper w)
  have hηabsInt := FutureProfiles.integrableOn_abs_profileP2Fun_weighted_le
    β hnN η A hηsupp hηbdd hηpast f (Real.exp H) hfBound G
  have hξabsInt := FutureProfiles.integrableOn_abs_profileP2Fun_weighted_le
    β hnN ξ B hξsupp hξbdd hξpast f (Real.exp H) hfBound G
  have hXmeas : Measurable (fun ω => profileP2Fun β n N (η ω) f ω) := by
    exact measurable_profileP2Fun_param β n N f
      (fun w => Polymer.measurable_endpointDist β n 0 w) measurable_id
  have hYmeas : Measurable (fun ω => profileP2Fun β n N (ξ ω) f ω) := by
    exact measurable_profileP2Fun_param β n N f
      (fun w => Polymer.measurable_smoothedEndpointDist β m n 0 w) measurable_id
  have hDmeas : Measurable (fun ω =>
      |profileP2Fun β n N (η ω) f ω - profileP2Fun β n N (ξ ω) f ω|) :=
    (hXmeas.sub hYmeas).abs
  have hDint : IntegrableOn (fun ω =>
      |profileP2Fun β n N (η ω) f ω - profileP2Fun β n N (ξ ω) f ω|)
      G disorderLaw := by
    refine (hηabsInt.1.add hξabsInt.1).mono' hDmeas.aestronglyMeasurable ?_
    filter_upwards [] with ω
    simpa only [Real.norm_eq_abs, abs_abs, Pi.add_apply] using
      abs_sub (profileP2Fun β n N (η ω) f ω)
        (profileP2Fun β n N (ξ ω) f ω)
  have hflatηinv := integrableOn_inv_sqrt_profileP2Fun_le β hβ hnN
    η A hηsupp hηnonneg hηmass hηpast G hG
  have hflatξinv := integrableOn_inv_sqrt_profileP2Fun_le β hβ hnN
    ξ B hξsupp hξnonneg hξmass hξpast G hG
  have hηEnergyEq := FutureProfiles.setIntegral_profileP2Fun_sq_eq β hnN η A
    hηsupp hηbdd hηpast G hG
  have hξEnergyEq := FutureProfiles.setIntegral_profileP2Fun_sq_eq β hnN ξ B
    hξsupp hξbdd hξpast G hG
  have hηEnergyBound : ∫ ω in G, FutureProfiles.futureEnergy β n N (η ω) ∂disorderLaw ≤ Kη := by
    calc
      ∫ ω in G, FutureProfiles.futureEnergy β n N (η ω) ∂disorderLaw =
          ∫ ω in G, profileP2Fun β n N (η ω) (fun _ => 1) ω ^ 2 ∂disorderLaw :=
        hηEnergyEq.symm
      _ ≤ Kη := by simpa [η, A] using hηsq
  have hξEnergyBound : ∫ ω in G, FutureProfiles.futureEnergy β n N (ξ ω) ∂disorderLaw ≤ Kξ := by
    calc
      ∫ ω in G, FutureProfiles.futureEnergy β n N (ξ ω) ∂disorderLaw =
          ∫ ω in G, profileP2Fun β n N (ξ ω) (fun _ => 1) ω ^ 2 ∂disorderLaw :=
        hξEnergyEq.symm
      _ ≤ Kξ := by simpa [ξ, B] using hξsq
  have hηEnergyNonneg : 0 ≤
      ∫ ω in G, FutureProfiles.futureEnergy β n N (η ω) ∂disorderLaw :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun ω =>
      FutureProfiles.futureEnergy_nonneg β n N (η ω))
  have hξEnergyNonneg : 0 ≤
      ∫ ω in G, FutureProfiles.futureEnergy β n N (ξ ω) ∂disorderLaw :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun ω =>
      FutureProfiles.futureEnergy_nonneg β n N (ξ ω))
  have hηflatInvBound :
      ∫ ω in G, profileP2Fun β n N (η ω) (fun _ => 1) ω ^ (-(1 : ℝ) / 2)
        ∂disorderLaw ≤ Kη ^ ((3 : ℝ) / 8) := by
    exact hflatηinv.2.trans (Real.rpow_le_rpow hηEnergyNonneg hηEnergyBound (by norm_num))
  have hξflatInvBound :
      ∫ ω in G, profileP2Fun β n N (ξ ω) (fun _ => 1) ω ^ (-(1 : ℝ) / 2)
        ∂disorderLaw ≤ Kξ ^ ((3 : ℝ) / 8) := by
    exact hflatξinv.2.trans (Real.rpow_le_rpow hξEnergyNonneg hξEnergyBound (by norm_num))
  have hηweightedInv := integrableOn_inv_sqrt_weighted_profileP2Fun_le
    β n N η A hηsupp hηnonneg hηmass f H hf G hflatηinv.1 hXmeas
  have hξweightedInv := integrableOn_inv_sqrt_weighted_profileP2Fun_le
    β n N ξ B hξsupp hξnonneg hξmass f H hf G hflatξinv.1 hYmeas
  have hηweightedInvBound :
      ∫ ω in G, profileP2Fun β n N (η ω) f ω ^ (-(1 : ℝ) / 2) ∂disorderLaw ≤
        Real.exp (H / 2) * Kη ^ ((3 : ℝ) / 8) := by
    exact hηweightedInv.2.trans (mul_le_mul_of_nonneg_left hηflatInvBound
      (Real.exp_nonneg _))
  have hξweightedInvBound :
      ∫ ω in G, profileP2Fun β n N (ξ ω) f ω ^ (-(1 : ℝ) / 2) ∂disorderLaw ≤
        Real.exp (H / 2) * Kξ ^ ((3 : ℝ) / 8) := by
    exact hξweightedInv.2.trans (mul_le_mul_of_nonneg_left hξflatInvBound
      (Real.exp_nonneg _))
  have hηpos (ω : Disorder) : 0 < profileP2Fun β n N (η ω) f ω := by
    have hνpos : ∃ w ∈ A, 0 < η ω w := by
      have hsum : 0 < ∑ w ∈ A, η ω w := by rw [hηmass ω]; norm_num
      exact (Finset.sum_pos_iff_of_nonneg (fun w hw => hηnonneg ω w)).mp hsum
    exact profileP2Fun_pos_terminal β n N (η ω) f A (hηsupp ω) (hηnonneg ω)
      hνpos (fun w => (hf w).1) ω
  have hξpos (ω : Disorder) : 0 < profileP2Fun β n N (ξ ω) f ω := by
    have hνpos : ∃ w ∈ B, 0 < ξ ω w := by
      have hsum : 0 < ∑ w ∈ B, ξ ω w := by rw [hξmass ω]; norm_num
      exact (Finset.sum_pos_iff_of_nonneg (fun w hw => hξnonneg ω w)).mp hsum
    exact profileP2Fun_pos_terminal β n N (ξ ω) f B (hξsupp ω) (hξnonneg ω)
      hνpos (fun w => (hf w).1) ω
  have hlogData := integrableOn_abs_log_sub_le_of_neg_half disorderLaw G
    (fun ω => profileP2Fun β n N (η ω) f ω)
    (fun ω => profileP2Fun β n N (ξ ω) f ω)
    hXmeas hYmeas hηpos hξpos hDint
    hηweightedInv.1 hξweightedInv.1
  refine ⟨?_, ?_⟩
  · change Integrable
      (fun ω => |globalLogError β m n N f 0 ω|) (disorderLaw.restrict G)
    simpa [globalLogError, η, ξ] using hlogData.1
  · calc
      ∫ ω in G, |globalLogError β m n N f 0 ω| ∂disorderLaw ≤
          logHolderConstant *
            (∫ ω in G,
              |profileP2Fun β n N (η ω) f ω - profileP2Fun β n N (ξ ω) f ω|
                ∂disorderLaw) ^ ((1 : ℝ) / 3) *
            ((∫ ω in G, profileP2Fun β n N (η ω) f ω ^ (-(1 : ℝ) / 2)
                ∂disorderLaw) ^ ((2 : ℝ) / 3) +
              (∫ ω in G, profileP2Fun β n N (ξ ω) f ω ^ (-(1 : ℝ) / 2)
                ∂disorderLaw) ^ ((2 : ℝ) / 3)) := by
          simpa [globalLogError, η, ξ] using hlogData.2
      _ ≤ logHolderConstant *
            (∫ ω in G,
              |profileP2Fun β n N (η ω) f ω - profileP2Fun β n N (ξ ω) f ω|
                ∂disorderLaw) ^ ((1 : ℝ) / 3) *
            ((Real.exp (H / 2) * Kη ^ ((3 : ℝ) / 8)) ^ ((2 : ℝ) / 3) +
              (Real.exp (H / 2) * Kξ ^ ((3 : ℝ) / 8)) ^ ((2 : ℝ) / 3)) := by
          have hDnonneg : 0 ≤ ∫ ω in G,
              |profileP2Fun β n N (η ω) f ω - profileP2Fun β n N (ξ ω) f ω|
                ∂disorderLaw := integral_nonneg_of_ae
                  (Filter.Eventually.of_forall fun ω => abs_nonneg _)
          have hηinvnonneg : 0 ≤ ∫ ω in G,
              profileP2Fun β n N (η ω) f ω ^ (-(1 : ℝ) / 2) ∂disorderLaw :=
            integral_nonneg_of_ae (Filter.Eventually.of_forall fun ω =>
              Real.rpow_nonneg (hηpos ω).le _)
          have hξinvnonneg : 0 ≤ ∫ ω in G,
              profileP2Fun β n N (ξ ω) f ω ^ (-(1 : ℝ) / 2) ∂disorderLaw :=
            integral_nonneg_of_ae (Filter.Eventually.of_forall fun ω =>
              Real.rpow_nonneg (hξpos ω).le _)
          have hηpow :
              (∫ ω in G, profileP2Fun β n N (η ω) f ω ^ (-(1 : ℝ) / 2)
                ∂disorderLaw) ^ ((2 : ℝ) / 3) ≤
                (Real.exp (H / 2) * Kη ^ ((3 : ℝ) / 8)) ^ ((2 : ℝ) / 3) :=
            Real.rpow_le_rpow hηinvnonneg hηweightedInvBound (by norm_num)
          have hξpow :
              (∫ ω in G, profileP2Fun β n N (ξ ω) f ω ^ (-(1 : ℝ) / 2)
                ∂disorderLaw) ^ ((2 : ℝ) / 3) ≤
                (Real.exp (H / 2) * Kξ ^ ((3 : ℝ) / 8)) ^ ((2 : ℝ) / 3) :=
            Real.rpow_le_rpow hξinvnonneg hξweightedInvBound (by norm_num)
          have hcoef : 0 ≤ logHolderConstant *
              (∫ ω in G,
                |profileP2Fun β n N (η ω) f ω - profileP2Fun β n N (ξ ω) f ω|
                  ∂disorderLaw) ^ ((1 : ℝ) / 3) :=
            mul_nonneg logHolderConstant_pos.le (Real.rpow_nonneg hDnonneg _)
          exact mul_le_mul_of_nonneg_left (add_le_add hηpow hξpow) hcoef

/-- Split an `L²` estimate into the good-event integral and the bad-event measure. The integral
and `L⁴` hypotheses include the integrability needed for the `L¹`–`L⁴` interpolation. -/
private theorem eLpNorm_two_le_good_bad {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : Ω → ℝ) (G : Set Ω)
    (hG : MeasurableSet G) (hF : AEStronglyMeasurable F μ)
    (Bgood Bfour p : ℝ) (hBgood : 0 ≤ Bgood) (hBfour : 0 ≤ Bfour) (hp : 0 ≤ p)
    (hGoodInt : IntegrableOn (fun ω => |F ω|) G μ)
    (hGood : ∫ ω in G, |F ω| ∂μ ≤ Bgood)
    (hFour : eLpNorm F 4 μ ≤ ENNReal.ofReal Bfour)
    (hBadMeasure : μ Gᶜ ≤ ENNReal.ofReal p) :
    eLpNorm F 2 μ ≤
      ENNReal.ofReal ((Bgood + Bfour * p ^ ((3 : ℝ) / 4)) ^ ((1 : ℝ) / 3) *
        Bfour ^ ((2 : ℝ) / 3)) := by
  have hFgoodMeas : AEStronglyMeasurable F (μ.restrict G) :=
    hF.mono_measure Measure.restrict_le_self
  have hFbadMeas : AEStronglyMeasurable F (μ.restrict Gᶜ) :=
    hF.mono_measure Measure.restrict_le_self
  have hNormGoodInt : Integrable (fun ω => |F ω|) (μ.restrict G) := by
    simpa only [IntegrableOn] using hGoodInt
  have hFgoodInt : Integrable F (μ.restrict G) := by
    exact (integrable_norm_iff hFgoodMeas).mp hNormGoodInt
  have hGoodNorm : eLpNorm (G.indicator F) 1 μ ≤ ENNReal.ofReal Bgood := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hG]
    rw [eLpNorm_one_eq_lintegral_enorm hFgoodMeas]
    rw [← ofReal_integral_norm_eq_lintegral_enorm hFgoodInt]
    exact ENNReal.ofReal_le_ofReal (by simpa only [Real.norm_eq_abs] using hGood)
  have hExp : (1 : ENNReal) ≤ (4 : ENNReal) := by norm_num
  have hCompare := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hExp hFbadMeas
  have hexp : 1 / (1 : ENNReal).toReal - 1 / (4 : ENNReal).toReal = (3 : ℝ) / 4 := by
    norm_num
  rw [hexp, Measure.restrict_apply_univ] at hCompare
  have hFfourBad : eLpNorm F 4 (μ.restrict Gᶜ) ≤ ENNReal.ofReal Bfour :=
    (eLpNorm_mono_measure F Measure.restrict_le_self).trans hFour
  have hbadPow : (μ Gᶜ) ^ ((3 : ℝ) / 4) ≤
      ENNReal.ofReal (p ^ ((3 : ℝ) / 4)) := by
    calc
      (μ Gᶜ) ^ ((3 : ℝ) / 4) ≤
          ENNReal.ofReal p ^ ((3 : ℝ) / 4) :=
        ENNReal.rpow_le_rpow hBadMeasure (by norm_num)
      _ = ENNReal.ofReal (p ^ ((3 : ℝ) / 4)) := by
        rw [← ENNReal.ofReal_rpow_of_nonneg hp (by norm_num)]
  have hBadNorm : eLpNorm (Gᶜ.indicator F) 1 μ ≤
      ENNReal.ofReal (Bfour * p ^ ((3 : ℝ) / 4)) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hG.compl]
    calc
      eLpNorm F 1 (μ.restrict Gᶜ) ≤
          eLpNorm F 4 (μ.restrict Gᶜ) * (μ Gᶜ) ^ ((3 : ℝ) / 4) := hCompare
      _ ≤ ENNReal.ofReal Bfour * ENNReal.ofReal (p ^ ((3 : ℝ) / 4)) :=
        mul_le_mul hFfourBad hbadPow (by positivity) (by positivity)
      _ = ENNReal.ofReal (Bfour * p ^ ((3 : ℝ) / 4)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
  have hFsplit : F = G.indicator F + Gᶜ.indicator F := by
    funext ω
    by_cases hω : ω ∈ G <;> simp [hω]
  have hOne : eLpNorm F 1 μ ≤
      ENNReal.ofReal Bgood + ENNReal.ofReal (Bfour * p ^ ((3 : ℝ) / 4)) := by
    rw [hFsplit]
    exact (eLpNorm_add_le (by norm_num : (1 : ENNReal) ≤ 1)).trans
      (add_le_add hGoodNorm hBadNorm)
  have hOne' : eLpNorm F 1 μ ≤
      ENNReal.ofReal (Bgood + Bfour * p ^ ((3 : ℝ) / 4)) := by
    calc
      _ ≤ ENNReal.ofReal Bgood + ENNReal.ofReal (Bfour * p ^ ((3 : ℝ) / 4)) := hOne
      _ = _ := by
        rw [← ENNReal.ofReal_add hBgood (mul_nonneg hBfour (Real.rpow_nonneg hp _))]
  have hInterp := eLpNorm_two_le_interpolation μ F hF
  have hboundInterp :
      eLpNorm F 1 μ ^ ((1 : ℝ) / 3) * eLpNorm F 4 μ ^ ((2 : ℝ) / 3) ≤
        ENNReal.ofReal ((Bgood + Bfour * p ^ ((3 : ℝ) / 4)) ^ ((1 : ℝ) / 3) *
          Bfour ^ ((2 : ℝ) / 3)) := by
    calc
      _ ≤ ENNReal.ofReal (Bgood + Bfour * p ^ ((3 : ℝ) / 4)) ^ ((1 : ℝ) / 3) *
          ENNReal.ofReal Bfour ^ ((2 : ℝ) / 3) := by
            exact mul_le_mul
              (ENNReal.rpow_le_rpow hOne' (by norm_num))
              (ENNReal.rpow_le_rpow hFour (by norm_num)) (by positivity) (by positivity)
      _ = _ := by
        rw [ENNReal.ofReal_rpow_of_nonneg
              (add_nonneg hBgood (mul_nonneg hBfour (Real.rpow_nonneg hp _))) (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg hBfour (by norm_num),
          ← ENNReal.ofReal_mul (by positivity)]
  exact hInterp.trans hboundInterp

private theorem abs_globalLogError_weighted_flat_le_endpoint (β : ℝ) {m n N : ℕ}
    (hmn : m ≤ n) (f : Site → ℝ) (H : ℝ)
    (hf : ∀ w, 0 < f w ∧ |Real.log (f w)| ≤ H) (ω : Disorder) :
    |(globalLogError β m n N f 0 ω) -
      globalLogError β m n N (fun _ => 1) 0 ω| ≤ 2 * H := by
  let η : Disorder → Site → ℝ := fun ω w => endpointDist β n 0 ω w
  let ξ : Disorder → Site → ℝ := fun ω w => smoothedEndpointDist β m n 0 ω w
  let A : Finset Site := Polymer.endpoints 0 n
  let B : Finset Site := (Polymer.endpoints 0 m).biUnion
    (fun y => Polymer.endpoints y (n - m))
  have hηnonneg : ∀ w, 0 ≤ η ω w := fun w => (endpointDist_probability β n 0 ω).2.1 w
  have hξnonneg : ∀ w, 0 ≤ ξ ω w := fun w => (smoothedEndpointDist_probability β hmn 0 ω).2.1 w
  have hηmass : ∑ w ∈ A, η ω w = 1 := by
    simpa [η, A] using (endpointDist_probability β n 0 ω).2.2
  have hξmass : ∑ w ∈ B, ξ ω w = 1 := by
    simpa [ξ, B] using (smoothedEndpointDist_probability β hmn 0 ω).2.2
  have hηzero : ∀ w ∉ A, η ω w = 0 := by
    intro w hw
    exact (endpointDist_probability β n 0 ω).1 w (by simpa [η, A] using hw)
  have hξzero : ∀ w ∉ B, ξ ω w = 0 := by
    intro w hw
    exact (smoothedEndpointDist_probability β hmn 0 ω).1 w (by simpa [ξ, B] using hw)
  simpa [globalLogError, η, ξ] using
    (abs_globalLogError_weighted_sub_flat_le β n N (η ω) (ξ ω) A B
      hηzero hξzero hηnonneg hξnonneg hηmass hξmass f H hf ω)

/-- A fixed power of the logarithm is eventually bounded by any positive power. -/
theorem log_rpow_le_rpow_eventually (r s : ℝ) (hs : 0 < s) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ r ≤ x ^ s := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop r hs).eventuallyLE
  filter_upwards [hsmall, eventually_ge_atTop (Real.exp 1)] with x hx hxexp
  have hlog : 1 ≤ Real.log x := by
    calc
      1 = Real.log (Real.exp 1) := by rw [Real.log_exp]
      _ ≤ Real.log x := Real.log_le_log (Real.exp_pos 1) hxexp
  have hlog0 : 0 ≤ Real.log x := le_trans (by norm_num) hlog
  have hx0 : 0 ≤ x := le_trans (Real.exp_pos 1).le hxexp
  simpa only [Real.norm_of_nonneg (Real.rpow_nonneg hlog0 r),
    Real.norm_of_nonneg (Real.rpow_nonneg hx0 s)] using hx

/-- Origin moment and good-event bounds control the `L²` norm of the weighted global logarithmic error. -/
theorem globalLogError_L2_le_of (hO : FutureProfiles.PropPFOriginBound)
    (hL : FutureProfiles.LogTailsOriginBound) (A H : ℝ) :
    ∃ C δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A, ∀ f : Site → ℝ,
        (∀ z, 0 < f z ∧ |Real.log (f z)| ≤ H) → ∀ z : Site,
          eLpNorm (globalLogError (criticalBeta ϑ N) (evenCeil (δ * N))
            (evenCeil (Real.sqrt δ * N)) N f z) 2 disorderLaw ≤
              ENNReal.ofReal (C * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε) := by
  obtain ⟨δO, CO, hδOpos, hδOlt, hOmain⟩ := hO A
  obtain ⟨CL, δL, hδLpos, hLmain⟩ :=
    hL A (4 : ENNReal) (by norm_num) (by norm_num)
  have hlogPower := log_rpow_le_rpow_eventually 1 ((1 : ℝ) / 360) (by norm_num)
  obtain ⟨Lpower, hLpower⟩ := (eventually_atTop.1 hlogPower)
  let Lstar : ℝ := max Lpower (Real.exp 1)
  have hLstarpos : 0 < Lstar := lt_of_lt_of_le (Real.exp_pos 1) (le_max_right _ _)
  let cO : ℝ := |CO| + 1
  let cT : ℝ := |CL| + 1
  let Kgood : ℝ := 2 * logHolderConstant * (cO * Real.exp |H|) ^ ((1 : ℝ) / 3) *
    Real.exp (|H| / 2) ^ ((2 : ℝ) / 3) * cO ^ ((1 : ℝ) / 4)
  let Kfour : ℝ := 2 * (cT + |H|)
  let Kbad : ℝ := Kfour * cO ^ ((3 : ℝ) / 4)
  let Ksum : ℝ := Kgood + Kbad
  let C : ℝ := Ksum ^ ((1 : ℝ) / 3) * Kfour ^ ((2 : ℝ) / 3)
  let δ₀ : ℝ := min δO (min (δL / 2) (Real.exp (-Lstar) / 2))
  have hcO : 0 < cO := by dsimp [cO]; positivity
  have hcT : 0 < cT := by dsimp [cT]; positivity
  have hKfour : 0 < Kfour := by dsimp [Kfour]; positivity
  have hLogHolderPos : 0 < logHolderConstant := logHolderConstant_pos
  have hKgood : 0 < Kgood := by dsimp [Kgood]; positivity
  have hKbad : 0 < Kbad := by dsimp [Kbad]; positivity
  have hKsum : 0 < Ksum := by dsimp [Ksum]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hδ₀pos : 0 < δ₀ := by
    dsimp [δ₀]
    positivity
  have hδ₀lt : δ₀ < 1 := (min_le_left _ _).trans_lt hδOlt
  refine ⟨C, δ₀, hδ₀pos, ?_⟩
  intro δ hδpos hδle ε hεpos
  have hδO : δ ≤ δO := le_trans hδle (min_le_left _ _)
  have hδL : δ < δL := by
    have hhalf : δ ≤ δL / 2 :=
      le_trans hδle (le_trans (min_le_right _ _) (min_le_left _ _))
    linarith
  have hδlog : δ < Real.exp (-Lstar) := by
    have hhalf : δ ≤ Real.exp (-Lstar) / 2 :=
      le_trans hδle (le_trans (min_le_right _ _) (min_le_right _ _))
    have hExpPos := Real.exp_pos (-Lstar)
    linarith
  have hlogδ : Real.log δ < -Lstar := by
    calc
      Real.log δ < Real.log (Real.exp (-Lstar)) := Real.log_lt_log hδpos hδlog
      _ = -Lstar := Real.log_exp _
  have hLpos : 0 < |Real.log δ| := abs_pos.mpr (by linarith)
  have hLlower : Lstar ≤ |Real.log δ| := by
    rw [abs_of_neg (by linarith)]
    linarith
  have hLlarge : Lpower ≤ |Real.log δ| := le_trans (le_max_left _ _) hLlower
  have hlogLone : 1 ≤ Real.log |Real.log δ| := by
    calc
      1 = Real.log (Real.exp 1) := by rw [Real.log_exp]
      _ ≤ Real.log |Real.log δ| := Real.log_le_log (Real.exp_pos 1)
        (le_trans (le_max_right _ _) hLlower)
  have hlogLnonneg : 0 ≤ Real.log |Real.log δ| := le_trans (by norm_num) hlogLone
  have hlogLpow : Real.log |Real.log δ| ≤
      |Real.log δ| ^ ((1 : ℝ) / 360) := by
    have h := hLpower |Real.log δ| hLlarge
    simpa only [Real.rpow_one] using h
  have hδlt1 : δ < 1 := lt_of_le_of_lt hδle hδ₀lt
  have hδsqrt : δ ≤ Real.sqrt δ := Real.le_sqrt_self_iff.mpr hδlt1.le
  have hrootlt : Real.sqrt δ < 1 := by
    simpa using Real.sqrt_lt_sqrt hδpos.le hδlt1
  have hNscale : ∀ᶠ N : ℕ in atTop,
      (2 : ℝ) ≤ (N : ℝ) * (1 - Real.sqrt δ) := by
    have h := (tendsto_natCast_atTop_atTop.const_mul_atTop (sub_pos.mpr hrootlt)).eventually
      (eventually_ge_atTop (2 : ℝ))
    simpa only [mul_comm] using h
  have hNtime : ∀ᶠ N : ℕ in atTop,
      evenCeil (δ * N) ≤ evenCeil (Real.sqrt δ * N) ∧
        evenCeil (Real.sqrt δ * N) ≤ N := by
    filter_upwards [hNscale] with N hscale
    constructor
    · exact evenCeil_mono (mul_le_mul_of_nonneg_right hδsqrt (Nat.cast_nonneg N))
    · have hround := evenCeil_lt_add_two
        (mul_nonneg (Real.sqrt_nonneg δ) (Nat.cast_nonneg N))
      have hcast : (evenCeil (Real.sqrt δ * N) : ℝ) ≤ (N : ℝ) := by
        have hNcast : (2 : ℝ) ≤ (N : ℝ) * (1 - Real.sqrt δ) := hscale
        linarith
      exact_mod_cast hcast
  have hOevent := hOmain δ hδpos hδO
  have hLevent := hLmain δ hδpos hδL
  have hNall := hNtime.and (hOevent.and hLevent)
  filter_upwards [hNall] with N hNall
  rcases hNall with ⟨⟨hmn, hnN⟩, hOevent, hLevent⟩
  intro ϑ hϑ f hf z
  have hOdata := hOevent ϑ hϑ
  rcases hOdata with ⟨G, hG, hBadReal, hDflat, hEtaSq, hXiSq, hWeighted⟩
  rcases hLevent ϑ hϑ with ⟨hEndpointTail, hSmoothedTail⟩
  let β : ℝ := criticalBeta ϑ N
  let m : ℕ := evenCeil (δ * N)
  let n : ℕ := evenCeil (Real.sqrt δ * N)
  let fz : Site → ℝ := fun w => f (w + z)
  have hβ : 0 ≤ β := by dsimp [β, criticalBeta]; exact Real.sqrt_nonneg _
  have hmn' : m ≤ n := by simpa [m, n] using hmn
  have hnN' : n ≤ N := by simpa [n] using hnN
  have hfz : ∀ w, 0 < fz w ∧ |Real.log (fz w)| ≤ H := by
    intro w
    simpa [fz] using hf (w + z)
  have hHnonneg : 0 ≤ H := (abs_nonneg (Real.log (f 0))).trans (hf 0).2
  have hHabs : |H| = H := abs_of_nonneg hHnonneg
  have hcOupper : CO ≤ cO := by dsimp [cO]; exact le_trans (le_abs_self _) (by linarith)
  have hcTupper : CL ≤ cT := by dsimp [cT]; exact le_trans (le_abs_self _) (by linarith)
  have hq : 1 ≤ Real.log |Real.log δ| := hlogLone
  have hqnonneg : 0 ≤ Real.log |Real.log δ| := hlogLnonneg
  have hqpos : 0 < Real.log |Real.log δ| := lt_of_lt_of_le (by norm_num) hq
  let L : ℝ := |Real.log δ|
  let q : ℝ := Real.log L
  have hLpos' : 0 < L := by simpa [L] using hLpos
  have hLone : 1 ≤ L := by
    dsimp [L]
    have : Real.exp 1 ≤ |Real.log δ| := le_trans (le_max_right _ _) hLlower
    linarith [Real.exp_one_gt_d9]
  have hqone : 1 ≤ q := by simpa [q, L] using hlogLone
  have hqnonneg' : 0 ≤ q := le_trans (by norm_num) hqone
  have hLpower' : Lpower ≤ L := by simpa [L] using hLlarge
  have hqpow : q ≤ L ^ ((1 : ℝ) / 360) := by
    have h := hLpower L hLpower'
    simpa [q, L, Real.rpow_one] using h
  let cO' : ℝ := cO
  let cT' : ℝ := cT
  have hcOpos : 0 < cO' := by simpa [cO'] using hcO
  have hcTpos : 0 < cT' := by simpa [cT'] using hcT
  have hKfour' : Kfour = 2 * (cT' + |H|) := by rfl
  have hKgood' : Kgood = 2 * logHolderConstant * (cO' * Real.exp |H|) ^ ((1 : ℝ) / 3) *
      Real.exp (|H| / 2) ^ ((2 : ℝ) / 3) * cO' ^ ((1 : ℝ) / 4) := by rfl
  have hKfourNonneg : 0 ≤ Kfour := le_of_lt hKfour
  have hKgoodNonneg : 0 ≤ Kgood := le_of_lt hKgood
  have hKsumNonneg : 0 ≤ Ksum := le_of_lt hKsum
  have hCnonneg : 0 ≤ C := le_of_lt hC
  have hDweight :
      ∫ ω in G, |profileP2Fun β n N (endpointDist β n 0 ω) fz ω -
        profileP2Fun β n N (smoothedEndpointDist β m n 0 ω) fz ω| ∂disorderLaw ≤
          cO' * Real.exp |H| * q / L := by
    have hweight := hWeighted fz (Real.exp |H|) (by
      intro w
      rw [abs_of_pos (hfz w).1]
      calc
        fz w = Real.exp (Real.log (fz w)) := (Real.exp_log (hfz w).1).symm
        _ ≤ Real.exp |H| := Real.exp_le_exp.mpr
          ((abs_le.mp (hfz w).2).2.trans (le_abs_self H)))
    have hrootq : Real.sqrt q ≤ q := (Real.sqrt_le_self_iff).2 (Or.inr hqone)
    have hfirst :
        CO * Real.exp |H| * Real.sqrt q / L ≤
          cO' * Real.exp |H| * Real.sqrt q / L := by
      apply div_le_div_of_nonneg_right ?_ hLpos'.le
      calc
        CO * Real.exp |H| * Real.sqrt q = CO * (Real.exp |H| * Real.sqrt q) := by ring
        _ ≤ cO' * (Real.exp |H| * Real.sqrt q) :=
          mul_le_mul_of_nonneg_right hcOupper (by positivity)
        _ = cO' * Real.exp |H| * Real.sqrt q := by ring
    have hsecond :
        cO' * Real.exp |H| * Real.sqrt q / L ≤ cO' * Real.exp |H| * q / L := by
      apply div_le_div_of_nonneg_right ?_ hLpos'.le
      calc
        cO' * Real.exp |H| * Real.sqrt q =
            (cO' * Real.exp |H|) * Real.sqrt q := by ring
        _ ≤ (cO' * Real.exp |H|) * q :=
          mul_le_mul_of_nonneg_left hrootq (by positivity)
        _ = cO' * Real.exp |H| * q := by ring
    calc
      _ ≤ CO * Real.exp |H| * Real.sqrt q / L := by
        simpa [β, m, n, q, L] using hweight
      _ ≤ cO' * Real.exp |H| * Real.sqrt q / L := hfirst
      _ ≤ cO' * Real.exp |H| * q / L := hsecond
  have hEtaSq' : ∫ ω in G,
      profileP2Fun β n N (endpointDist β n 0 ω) (fun _ => 1) ω ^ 2 ∂disorderLaw ≤ cO' * L := by
    calc
      _ ≤ CO * L := by simpa [β, n, L] using hEtaSq
      _ ≤ cO' * L := mul_le_mul_of_nonneg_right hcOupper hLpos'.le
  have hXiSq' : ∫ ω in G,
      profileP2Fun β n N (smoothedEndpointDist β m n 0 ω) (fun _ => 1) ω ^ 2
        ∂disorderLaw ≤ cO' * L := by
    calc
      _ ≤ CO * L := by simpa [β, m, n, L] using hXiSq
      _ ≤ cO' * L := mul_le_mul_of_nonneg_right hcOupper hLpos'.le
  let X : Disorder → ℝ := fun ω =>
    Real.log (profileP2Fun β n N (endpointDist β n 0 ω) (fun _ => 1) ω)
  let Y : Disorder → ℝ := fun ω =>
    Real.log (profileP2Fun β n N (smoothedEndpointDist β m n 0 ω) (fun _ => 1) ω)
  let W : Disorder → ℝ := globalLogError β m n N fz 0
  let Flat : Disorder → ℝ := globalLogError β m n N (fun _ => 1) 0
  have hWmeas : AEStronglyMeasurable W disorderLaw := by
    exact (measurable_globalLogError β m n N fz 0).aestronglyMeasurable
  have hFlatmeas : AEStronglyMeasurable Flat disorderLaw := by
    exact (measurable_globalLogError β m n N (fun _ => 1) 0).aestronglyMeasurable
  have hXtail : eLpNorm X 4 disorderLaw ≤ ENNReal.ofReal (cT' * q) := by
    calc
      eLpNorm X 4 disorderLaw ≤ ENNReal.ofReal (CL * q) := by
        simpa [X, β, n, q, L] using hEndpointTail
      _ ≤ ENNReal.ofReal (cT' * q) := ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hcTupper hqnonneg')
  have hYtail : eLpNorm Y 4 disorderLaw ≤ ENNReal.ofReal (cT' * q) := by
    calc
      eLpNorm Y 4 disorderLaw ≤ ENNReal.ofReal (CL * q) := by
        simpa [Y, β, m, n, q, L] using hSmoothedTail
      _ ≤ ENNReal.ofReal (cT' * q) := ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hcTupper hqnonneg')
  have hFlat4 : eLpNorm Flat 4 disorderLaw ≤ ENNReal.ofReal (2 * cT' * q) := by
    have htriangle := eLpNorm_add_le (μ := disorderLaw) (p := (4 : ENNReal))
      (by norm_num : (1 : ENNReal) ≤ 4) (f := X) (g := -Y)
    calc
      eLpNorm Flat 4 disorderLaw = eLpNorm (X + -Y) 4 disorderLaw := by
        apply eLpNorm_congr_ae
        filter_upwards [] with ω
        dsimp [Flat, X, Y, globalLogError]
        ring
      _ ≤ eLpNorm X 4 disorderLaw + eLpNorm (-Y) 4 disorderLaw := htriangle
      _ ≤ ENNReal.ofReal (cT' * q) + ENNReal.ofReal (cT' * q) :=
        add_le_add hXtail (by simpa using hYtail)
      _ = ENNReal.ofReal (2 * cT' * q) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
  have hWdiff : ∀ ω, |W ω - Flat ω| ≤ 2 * H := by
    intro ω
    simpa [W, Flat, β, m, n] using
      (abs_globalLogError_weighted_flat_le_endpoint β hmn' fz H hfz ω)
  have hDiff4 : eLpNorm (W - Flat) 4 disorderLaw ≤ ENNReal.ofReal (2 * |H|) := by
    have hmeas : AEStronglyMeasurable (W - Flat) disorderLaw := hWmeas.sub hFlatmeas
    calc
      eLpNorm (W - Flat) 4 disorderLaw ≤ eLpNorm (fun _ : Disorder => 2 * |H|) 4 disorderLaw :=
        eLpNorm_mono_real hmeas (fun ω => by
          simpa [Real.norm_eq_abs, hHabs] using hWdiff ω)
      _ = ENNReal.ofReal (2 * |H|) := by
        calc
          eLpNorm (fun _ : Disorder => 2 * |H|) 4 disorderLaw =
              ‖(2 * |H| : ℝ)‖ₑ * disorderLaw Set.univ ^ ((1 : ℝ) / 4) :=
            eLpNorm_const' (c := (2 * |H| : ℝ)) (p := (4 : ENNReal))
              (by norm_num) (by norm_num)
          _ = ENNReal.ofReal (2 * |H|) := by
            rw [Real.enorm_eq_ofReal (by positivity)]
            simp
  have hW4 : eLpNorm W 4 disorderLaw ≤ ENNReal.ofReal (Kfour * q) := by
    have htriangle := eLpNorm_add_le (μ := disorderLaw) (p := (4 : ENNReal))
      (by norm_num : (1 : ENNReal) ≤ 4) (f := Flat) (g := W - Flat)
    have hsplit : W = fun ω => Flat ω + (W ω - Flat ω) := by
      funext ω
      ring
    have hsplitNorm := congrArg (fun F : Disorder → ℝ => eLpNorm F 4 disorderLaw) hsplit
    calc
      eLpNorm W 4 disorderLaw =
          eLpNorm (Flat + (W - Flat)) 4 disorderLaw := hsplitNorm
      _ ≤ eLpNorm Flat 4 disorderLaw + eLpNorm (W - Flat) 4 disorderLaw := htriangle
      _ ≤ ENNReal.ofReal (2 * cT' * q) + ENNReal.ofReal (2 * |H|) :=
        add_le_add hFlat4 hDiff4
      _ ≤ ENNReal.ofReal (Kfour * q) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        rw [hKfour']
        calc
          2 * cT' * q + 2 * |H| ≤ 2 * cT' * q + 2 * |H| * q :=
            add_le_add le_rfl
              (by
                simpa only [mul_one] using
                  mul_le_mul_of_nonneg_left hqone
                    (by positivity : 0 ≤ 2 * |H|))
          _ = 2 * (cT' + |H|) * q := by ring
  have hGoodData := integrableOn_globalLogError_good_event β hβ hmn' hnN' fz H hfz
    G hG (cO' * L) (cO' * L) hEtaSq' hXiSq'
  have hGoodInt : IntegrableOn (fun ω => |W ω|) G disorderLaw := by
    simpa [W, β, m, n] using hGoodData.1
  have hDnonneg : 0 ≤ ∫ ω in G,
      |profileP2Fun β n N (endpointDist β n 0 ω) fz ω -
        profileP2Fun β n N (smoothedEndpointDist β m n 0 ω) fz ω| ∂disorderLaw :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun ω => abs_nonneg _)
  have hBgood :
      ∫ ω in G, |W ω| ∂disorderLaw ≤ Kgood * q * L ^ (-(1 : ℝ) / 12) := by
    have hInv : 0 ≤ (Real.exp (H / 2) * (cO' * L) ^ ((3 : ℝ) / 8)) ^ ((2 : ℝ) / 3) := by
      positivity
    have hDpow :
        (∫ ω in G,
          |profileP2Fun β n N (endpointDist β n 0 ω) fz ω -
            profileP2Fun β n N (smoothedEndpointDist β m n 0 ω) fz ω|
            ∂disorderLaw) ^ ((1 : ℝ) / 3) ≤
          (cO' * Real.exp |H| * q / L) ^ ((1 : ℝ) / 3) :=
      Real.rpow_le_rpow hDnonneg hDweight (by norm_num)
    have hRaw :
        ∫ ω in G, |W ω| ∂disorderLaw ≤
          logHolderConstant * (cO' * Real.exp |H| * q / L) ^ ((1 : ℝ) / 3) *
            (2 * (Real.exp (H / 2) * (cO' * L) ^ ((3 : ℝ) / 8)) ^ ((2 : ℝ) / 3)) := by
      calc
        _ ≤ logHolderConstant *
            (∫ ω in G,
              |profileP2Fun β n N (endpointDist β n 0 ω) fz ω -
                profileP2Fun β n N (smoothedEndpointDist β m n 0 ω) fz ω|
                ∂disorderLaw) ^ ((1 : ℝ) / 3) *
            ((Real.exp (H / 2) * (cO' * L) ^ ((3 : ℝ) / 8)) ^ ((2 : ℝ) / 3) +
              (Real.exp (H / 2) * (cO' * L) ^ ((3 : ℝ) / 8)) ^ ((2 : ℝ) / 3)) := hGoodData.2
        _ ≤ logHolderConstant * (cO' * Real.exp |H| * q / L) ^ ((1 : ℝ) / 3) *
            ((Real.exp (H / 2) * (cO' * L) ^ ((3 : ℝ) / 8)) ^ ((2 : ℝ) / 3) +
              (Real.exp (H / 2) * (cO' * L) ^ ((3 : ℝ) / 8)) ^ ((2 : ℝ) / 3)) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hDpow logHolderConstant_pos.le) (by positivity)
        _ = _ := by ring
    have hnegThird : L ^ (-(1 : ℝ) / 3) = (L ^ ((1 : ℝ) / 3))⁻¹ := by
      simpa only [neg_div] using Real.rpow_neg hLpos'.le ((1 : ℝ) / 3)
    have hDfactor :
        (cO' * Real.exp |H| * q / L) ^ ((1 : ℝ) / 3) =
          (cO' * Real.exp |H|) ^ ((1 : ℝ) / 3) * q ^ ((1 : ℝ) / 3) *
            L ^ (-(1 : ℝ) / 3) := by
      calc
        _ = ((cO' * Real.exp |H|) * q) ^ ((1 : ℝ) / 3) /
            L ^ ((1 : ℝ) / 3) := by
              exact Real.div_rpow (by positivity) hLpos'.le _
        _ = ((cO' * Real.exp |H|) ^ ((1 : ℝ) / 3) * q ^ ((1 : ℝ) / 3)) /
            L ^ ((1 : ℝ) / 3) := by
              rw [Real.mul_rpow (by positivity) hqnonneg']
        _ = (cO' * Real.exp |H|) ^ ((1 : ℝ) / 3) * q ^ ((1 : ℝ) / 3) *
            L ^ (-(1 : ℝ) / 3) := by
              rw [div_eq_mul_inv, ← hnegThird]
    have hInvfactor :
        (Real.exp (|H| / 2) * (cO' * L) ^ ((3 : ℝ) / 8)) ^ ((2 : ℝ) / 3) =
          Real.exp (|H| / 2) ^ ((2 : ℝ) / 3) * cO' ^ ((1 : ℝ) / 4) *
            L ^ ((1 : ℝ) / 4) := by
      calc
        _ = Real.exp (|H| / 2) ^ ((2 : ℝ) / 3) *
            ((cO' * L) ^ ((3 : ℝ) / 8)) ^ ((2 : ℝ) / 3) := by
              rw [Real.mul_rpow (Real.exp_nonneg _) (by positivity)]
        _ = Real.exp (|H| / 2) ^ ((2 : ℝ) / 3) *
            (cO' * L) ^ ((1 : ℝ) / 4) := by
              congr 1
              rw [← Real.rpow_mul (by positivity : 0 ≤ cO' * L)]
              congr 1
              norm_num
        _ = Real.exp (|H| / 2) ^ ((2 : ℝ) / 3) *
            (cO' ^ ((1 : ℝ) / 4) * L ^ ((1 : ℝ) / 4)) := by
              rw [Real.mul_rpow hcOpos.le hLpos'.le]
        _ = _ := by ring
    have hLfactor : L ^ (-(1 : ℝ) / 3) * L ^ ((1 : ℝ) / 4) =
        L ^ (-(1 : ℝ) / 12) := by
      calc
        _ = L ^ (-(1 : ℝ) / 3 + (1 : ℝ) / 4) :=
          (Real.rpow_add hLpos' _ _).symm
        _ = L ^ (-(1 : ℝ) / 12) := by congr 1; ring
    have hqpow : q ^ ((1 : ℝ) / 3) ≤ q := by
      calc
        q ^ ((1 : ℝ) / 3) ≤ q ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hqone (by norm_num)
        _ = q := Real.rpow_one _
    rw [← hHabs] at hRaw
    simp only [abs_abs] at hRaw
    calc
      _ ≤ logHolderConstant *
          (cO' * Real.exp |H| * q / L) ^ ((1 : ℝ) / 3) *
          (2 * (Real.exp (|H| / 2) * (cO' * L) ^ ((3 : ℝ) / 8)) ^ ((2 : ℝ) / 3)) := hRaw
      _ = logHolderConstant * (cO' * Real.exp |H|) ^ ((1 : ℝ) / 3) *
          q ^ ((1 : ℝ) / 3) * L ^ (-(1 : ℝ) / 3) *
          (2 * (Real.exp (|H| / 2) * (cO' * L) ^ ((3 : ℝ) / 8)) ^ ((2 : ℝ) / 3)) := by
            rw [hDfactor]
            ring
      _ = Kgood * q ^ ((1 : ℝ) / 3) * L ^ (-(1 : ℝ) / 12) := by
            rw [hInvfactor]
            calc
              _ = (2 * logHolderConstant * (cO' * Real.exp |H|) ^ ((1 : ℝ) / 3) *
                    Real.exp (|H| / 2) ^ ((2 : ℝ) / 3) * cO' ^ ((1 : ℝ) / 4)) *
                    q ^ ((1 : ℝ) / 3) *
                    (L ^ (-(1 : ℝ) / 3) * L ^ ((1 : ℝ) / 4)) := by ring
              _ = Kgood * q ^ ((1 : ℝ) / 3) * L ^ (-(1 : ℝ) / 12) := by
                rw [hLfactor, hKgood']
      _ ≤ Kgood * q * L ^ (-(1 : ℝ) / 12) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hqpow hKgoodNonneg)
              (Real.rpow_nonneg hLpos'.le _)
  have hGoodBound :
      ∫ ω in G, |W ω| ∂disorderLaw ≤ Kgood * q * L ^ (-(1 : ℝ) / 12) := hBgood
  have hBadReal' : (disorderLaw Gᶜ).toReal ≤ cO' / L := by
    calc
      (disorderLaw Gᶜ).toReal ≤ CO / L := by simpa [L] using hBadReal
      _ ≤ cO' / L := div_le_div_of_nonneg_right hcOupper hLpos'.le
  have hBadENN : disorderLaw Gᶜ ≤ ENNReal.ofReal (cO' / L) := by
    calc
      disorderLaw Gᶜ = ENNReal.ofReal (disorderLaw Gᶜ).toReal :=
        (ENNReal.ofReal_toReal (measure_ne_top disorderLaw Gᶜ)).symm
      _ ≤ ENNReal.ofReal (cO' / L) := ENNReal.ofReal_le_ofReal hBadReal'
  have hBfour : 0 ≤ Kfour * q := mul_nonneg hKfourNonneg hqnonneg'
  have hBgoodNonneg : 0 ≤ Kgood * q * L ^ (-(1 : ℝ) / 12) := by positivity
  have hBadpow : (cO' / L) ^ ((3 : ℝ) / 4) ≤
      cO' ^ ((3 : ℝ) / 4) * L ^ (-(3 : ℝ) / 4) := by
    calc
      _ = cO' ^ ((3 : ℝ) / 4) / L ^ ((3 : ℝ) / 4) :=
        Real.div_rpow hcOpos.le hLpos'.le _
      _ = cO' ^ ((3 : ℝ) / 4) * L ^ (-(3 : ℝ) / 4) := by
        have hneg : L ^ (-(3 : ℝ) / 4) = (L ^ ((3 : ℝ) / 4))⁻¹ := by
          simpa only [neg_div] using Real.rpow_neg hLpos'.le ((3 : ℝ) / 4)
        calc
          _ = cO' ^ ((3 : ℝ) / 4) * (L ^ ((3 : ℝ) / 4))⁻¹ := by
            rw [div_eq_mul_inv]
          _ = cO' ^ ((3 : ℝ) / 4) * L ^ (-(3 : ℝ) / 4) := by
            exact congrArg (fun x : ℝ => cO' ^ ((3 : ℝ) / 4) * x) hneg.symm
      _ ≤ cO' ^ ((3 : ℝ) / 4) * L ^ (-(3 : ℝ) / 4) := le_rfl
  have hLpowBad : L ^ (-(3 : ℝ) / 4) ≤ L ^ (-(1 : ℝ) / 12) :=
    Real.rpow_le_rpow_of_exponent_le hLone (by norm_num)
  have hBadPiece : Kfour * q * (cO' / L) ^ ((3 : ℝ) / 4) ≤
      Kbad * q * L ^ (-(1 : ℝ) / 12) := by
    calc
      _ ≤ Kfour * q * (cO' ^ ((3 : ℝ) / 4) * L ^ (-(3 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_left hBadpow (mul_nonneg hKfourNonneg hqnonneg')
      _ ≤ Kfour * q * (cO' ^ ((3 : ℝ) / 4) * L ^ (-(1 : ℝ) / 12)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hLpowBad (Real.rpow_nonneg hcOpos.le _))
          (mul_nonneg hKfourNonneg hqnonneg')
      _ = Kbad * q * L ^ (-(1 : ℝ) / 12) := by
        dsimp [Kbad]
        ring
  have hBadL1 : Kfour * q * (cO' / L) ^ ((3 : ℝ) / 4) ≤
      Kbad * q * L ^ (-(1 : ℝ) / 12) := hBadPiece
  have hTotalSum : Kgood * q * L ^ (-(1 : ℝ) / 12) +
      Kfour * q * (cO' / L) ^ ((3 : ℝ) / 4) ≤ Ksum * q * L ^ (-(1 : ℝ) / 12) := by
    calc
      _ ≤ Kgood * q * L ^ (-(1 : ℝ) / 12) +
          Kbad * q * L ^ (-(1 : ℝ) / 12) := add_le_add le_rfl hBadL1
      _ = Ksum * q * L ^ (-(1 : ℝ) / 12) := by dsimp [Ksum]; ring
  have hPastLe : disorderPast n ≤ (inferInstance : MeasurableSpace Disorder) := by
    rw [← Gaussian.disorderBlock_zero n]
    exact Gaussian.disorderBlock_le 0 n
  have hGordinary : MeasurableSet G := hPastLe G hG
  have hInterp := eLpNorm_two_le_good_bad disorderLaw W G hGordinary
    hWmeas (Kgood * q * L ^ (-(1 : ℝ) / 12)) (Kfour * q) (cO' / L)
    hBgoodNonneg hBfour (by positivity) hGoodInt hGoodBound hW4 hBadENN
  have hsumPow :
      (Ksum * q * L ^ (-(1 : ℝ) / 12)) ^ ((1 : ℝ) / 3) =
        Ksum ^ ((1 : ℝ) / 3) * q ^ ((1 : ℝ) / 3) * L ^ (-(1 : ℝ) / 36) := by
    calc
      _ = (Ksum * q) ^ ((1 : ℝ) / 3) * (L ^ (-(1 : ℝ) / 12)) ^ ((1 : ℝ) / 3) :=
        Real.mul_rpow (mul_nonneg hKsumNonneg hqnonneg')
          (Real.rpow_nonneg hLpos'.le _)
      _ = Ksum ^ ((1 : ℝ) / 3) * q ^ ((1 : ℝ) / 3) *
          L ^ (-(1 : ℝ) / 36) := by
        rw [Real.mul_rpow hKsumNonneg hqnonneg', ← Real.rpow_mul hLpos'.le]
        congr 1
        norm_num
  have hfourPow : (Kfour * q) ^ ((2 : ℝ) / 3) =
      Kfour ^ ((2 : ℝ) / 3) * q ^ ((2 : ℝ) / 3) :=
    Real.mul_rpow hKfourNonneg hqnonneg'
  have hqcombine : q ^ ((1 : ℝ) / 3) * q ^ ((2 : ℝ) / 3) = q := by
    calc
      _ = q ^ ((1 : ℝ) / 3 + (2 : ℝ) / 3) :=
        (Real.rpow_add hqpos _ _).symm
      _ = q := by rw [show (1 : ℝ) / 3 + (2 : ℝ) / 3 = 1 by ring, Real.rpow_one]
  have hRealBound :
      (Kgood * q * L ^ (-(1 : ℝ) / 12) +
        Kfour * q * (cO' / L) ^ ((3 : ℝ) / 4)) ^ ((1 : ℝ) / 3) *
        (Kfour * q) ^ ((2 : ℝ) / 3) ≤ C * q * L ^ (-(1 : ℝ) / 36) := by
    calc
      _ ≤ (Ksum * q * L ^ (-(1 : ℝ) / 12)) ^ ((1 : ℝ) / 3) *
          (Kfour * q) ^ ((2 : ℝ) / 3) := by
            exact mul_le_mul_of_nonneg_right
              (Real.rpow_le_rpow (by positivity) hTotalSum (by norm_num))
              (Real.rpow_nonneg hBfour _)
      _ = C * q * L ^ (-(1 : ℝ) / 36) := by
            rw [hsumPow, hfourPow]
            calc
              _ = Ksum ^ ((1 : ℝ) / 3) * Kfour ^ ((2 : ℝ) / 3) *
                    (q ^ ((1 : ℝ) / 3) * q ^ ((2 : ℝ) / 3)) *
                    L ^ (-(1 : ℝ) / 36) := by ring
              _ = C * q * L ^ (-(1 : ℝ) / 36) := by
                    rw [hqcombine]
  have hOrigin : eLpNorm W 2 disorderLaw ≤
      ENNReal.ofReal (C * L ^ (-(1 : ℝ) / 40)) := by
    calc
      eLpNorm W 2 disorderLaw ≤ ENNReal.ofReal
          ((Kgood * q * L ^ (-(1 : ℝ) / 12) +
            Kfour * q * (cO' / L) ^ ((3 : ℝ) / 4)) ^ ((1 : ℝ) / 3) *
            (Kfour * q) ^ ((2 : ℝ) / 3)) := hInterp
      _ ≤ ENNReal.ofReal (C * q * L ^ (-(1 : ℝ) / 36)) :=
        ENNReal.ofReal_le_ofReal hRealBound
      _ ≤ ENNReal.ofReal (C * L ^ (-(1 : ℝ) / 40)) := by
        apply ENNReal.ofReal_le_ofReal
        have hLexp : L ^ ((1 : ℝ) / 360) * L ^ (-(1 : ℝ) / 36) =
            L ^ (-(1 : ℝ) / 40) := by
          calc
            _ = L ^ ((1 : ℝ) / 360 + -(1 : ℝ) / 36) :=
              (Real.rpow_add hLpos' _ _).symm
            _ = L ^ (-(1 : ℝ) / 40) := by congr 1; ring
        calc
          C * q * L ^ (-(1 : ℝ) / 36) ≤
              C * L ^ ((1 : ℝ) / 360) * L ^ (-(1 : ℝ) / 36) := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hqpow hCnonneg)
                  (Real.rpow_nonneg hLpos'.le _)
          _ = C * L ^ (-(1 : ℝ) / 40) := by
            calc
              _ = C * (L ^ ((1 : ℝ) / 360) * L ^ (-(1 : ℝ) / 36)) := by ring
              _ = C * L ^ (-(1 : ℝ) / 40) := by rw [hLexp]
  have hOriginTarget : eLpNorm W 2 disorderLaw ≤
      ENNReal.ofReal (C * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε) := by
    calc
      _ ≤ ENNReal.ofReal (C * L ^ (-(1 : ℝ) / 40)) := hOrigin
      _ ≤ ENNReal.ofReal (C * L ^ (-(1 : ℝ) / 40) + ε) :=
        ENNReal.ofReal_le_ofReal (by linarith [hεpos])
      _ = ENNReal.ofReal (C * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε) := by
        simp [L]
  rw [globalLogError_eLpNorm_translate β m n N f z]
  simpa [W, β, m, n, fz] using hOriginTarget

end Critical2DKPZ.Smoothing

end
