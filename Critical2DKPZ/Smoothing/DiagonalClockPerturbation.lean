/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Smoothing.ClockWidthPerturbation
public import Critical2DKPZ.Smoothing.ShortClockVarianceRefined
public import Critical2DKPZ.Smoothing.ShortClockEndpointL2
public import Critical2DKPZ.Smoothing.RandomProfileTerminalL2
public import Critical2DKPZ.Smoothing.ProfileInverseL1
public import Critical2DKPZ.Smoothing.ProfileLogIntegrability
import Mathlib.Tactic

/-! # Diagonal smoothing clocks with bounded terminal weights -/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Critical2DKPZ.Smoothing

/-- A short change of the initial clock splits into the centered short mass and a future profile
with a random endpoint law. Its `L²` estimate is recorded with all integral hypotheses exposed. -/
theorem eLpNorm_log_diagonal_profile_shift_le
    (β H F : ℝ) (hβ : 0 ≤ β) (hH : 0 ≤ H) (hF : 0 ≤ F)
    {d u M : ℕ} (hdu : d ≤ u) (huM : u ≤ M) (x : Site) (f : Site → ℝ)
    (hf : ∀ z, 0 < f z ∧ |Real.log (f z)| ≤ H)
    (hfb : ∀ z, |f z| ≤ F)
    (Qvar : ℝ)
    (hvarInt : Integrable
      (fun ω => (smoothedP2Plane β d u x ω - 1) ^ 2) disorderLaw)
    (hvar : (∫ ω, (smoothedP2Plane β d u x ω - 1) ^ 2 ∂disorderLaw) ≤ Qvar)
    (R : ℝ) (hR : 0 ≤ R)
    (hkernel : ∀ z, srwKernel u (z - x) ≤ R)
    (K : ℝ) (hK : 0 ≤ K)
    (hcollision : (∑ r ∈ Finset.Icc 1 (M - u),
      Polymer.sigmaSq β *
        (∫ ω, pointToPlane β 0 (M - u - r) 0 ω ^ 2 ∂disorderLaw)) ≤ K)
    (Qflat : ℝ) (hQflat : 0 ≤ Qflat)
    (hflatInt : Integrable
      (fun ω => profileP2Fun β u M (fun w => srwKernel u (w - x))
        (fun _ => 1) ω ^ 2) disorderLaw)
    (hflat : (∫ ω, profileP2Fun β u M (fun w => srwKernel u (w - x))
      (fun _ => 1) ω ^ 2 ∂disorderLaw) ≤ Qflat) :
    eLpNorm (fun ω =>
      Real.log (profileP2Fun β d M (fun w => srwKernel d (w - x)) f ω) -
        Real.log (profileP2Fun β u M (fun w => srwKernel u (w - x)) f ω))
      2 disorderLaw ≤
      ENNReal.ofReal logHolderConstant *
          ENNReal.ofReal (Real.sqrt Qvar) ^ ((1 : ℝ) / 3) *
          ((ENNReal.ofReal (1 + Qvar)) ^ ((1 : ℝ) / 3) + 1) +
        ENNReal.ofReal logHolderConstant *
          ENNReal.ofReal (Real.sqrt (F ^ 2 *
            ((∫ ω, shortClockEndpointTV β d u x ω ^ 2 ∂disorderLaw) +
              (∫ ω, ∑ w ∈ Polymer.endpoints x u,
                (smoothedEndpointDist β d u x ω w - srwKernel u (w - x)) ^ 2
                  ∂disorderLaw) * K))) ^ ((1 : ℝ) / 3) *
          ((ENNReal.ofReal (Real.exp H * (2 * Qflat +
              2 * ((∫ ω, shortClockEndpointTV β d u x ω ^ 2 ∂disorderLaw) +
                (∫ ω, ∑ w ∈ Polymer.endpoints x u,
                  (smoothedEndpointDist β d u x ω w - srwKernel u (w - x)) ^ 2
                    ∂disorderLaw) * K)))) ^ ((1 : ℝ) / 3) +
            (ENNReal.ofReal (Real.exp H * Qflat)) ^ ((1 : ℝ) / 3)) := by
  classical
  let A := Polymer.endpoints x u
  let Aη := (Polymer.endpoints x d).biUnion (fun y => Polymer.endpoints y (u - d))
  let η : Disorder → Site → ℝ := smoothedEndpointDist β d u x
  let ν : Site → ℝ := fun w => srwKernel u (w - x)
  let X : Disorder → ℝ := fun ω => profileP2Fun β u M (η ω) f ω
  let Y : Disorder → ℝ := fun ω => profileP2Fun β u M ν f ω
  let X₀ : Disorder → ℝ := fun ω => profileP2Fun β u M (η ω) (fun _ => 1) ω
  let Y₀ : Disorder → ℝ := fun ω => profileP2Fun β u M ν (fun _ => 1) ω
  have hAη : Aη ⊆ A := by
    intro z hz
    rcases Finset.mem_biUnion.mp hz with ⟨y, hy, hz⟩
    have h := shortClock_endpoints_add hy hz
    simpa [A, Nat.add_sub_of_le hdu] using h
  have hηA (ω : Disorder) (w : Site) (hw : w ∉ A) : η ω w = 0 := by
    apply (smoothedEndpointDist_probability β hdu x ω).1
    intro hwη
    exact hw (hAη hwη)
  have hνA (w : Site) (hw : w ∉ A) : ν w = 0 := by
    exact Polymer.srwKernel_eq_zero_of_not_mem u x w (by simpa [A, ν] using hw)
  have hη0 (ω : Disorder) (w : Site) : 0 ≤ η ω w :=
    (smoothedEndpointDist_probability β hdu x ω).2.1 w
  have hν0 (w : Site) : 0 ≤ ν w :=
    Polymer.kernel_nonneg u (w - x)
  have hη1 (ω : Disorder) : ∑ w ∈ A, η ω w = 1 := by
    calc
      _ = ∑ w ∈ Aη, η ω w := by
        symm
        apply Finset.sum_subset hAη
        intro w hw hwAη
        exact (smoothedEndpointDist_probability β hdu x ω).1 w hwAη
      _ = 1 := (smoothedEndpointDist_probability β hdu x ω).2.2
  have hν1 : ∑ w ∈ A, ν w = 1 := by
    simpa [A, ν] using Polymer.sum_srwKernel_endpoints u x
  have hηpast : ∀ w, Measurable[Gaussian.disorderBlock d u] (η · w) := by
    intro w
    exact Polymer.measurable_smoothedEndpointDist_block β d u hdu x w
  have hPast : Gaussian.disorderBlock d u ≤ disorderPast u := by
    rw [← Gaussian.disorderBlock_zero u]
    exact Gaussian.disorderBlock_mono (by omega) le_rfl
  have hηpast' : ∀ w, Measurable[disorderPast u] (η · w) := by
    intro w
    exact (hηpast w).mono hPast le_rfl
  have hpastFull : disorderPast u ≤ (inferInstance : MeasurableSpace Disorder) := by
    rw [← Gaussian.disorderBlock_zero u]
    exact Gaussian.disorderBlock_le 0 u
  have hηmeasFull : ∀ w, Measurable (η · w) := by
    intro w
    exact (hηpast' w).mono hpastFull le_rfl
  have hνpast : ∀ w, Measurable[disorderPast u] (fun _ : Disorder => ν w) := by
    intro w
    exact measurable_const
  have hηbdd : ∃ B : ℝ, ∀ ω w, |η ω w| ≤ B := by
    refine ⟨1, ?_⟩
    intro ω w
    rw [abs_of_nonneg (hη0 ω w)]
    by_cases hw : w ∈ A
    · exact (Finset.single_le_sum (fun z hz => hη0 ω z) hw).trans_eq (hη1 ω)
    · rw [hηA ω w hw]
      norm_num
  have hTV := integral_shortClockEndpointTV_sq_le β hdu x Qvar hvarInt hvar
  have hCoord := integral_shortClockEndpoint_coordinate_sq_le β hdu x Qvar R hR
    hvarInt hvar hkernel
  let T : ℝ := (∫ ω, shortClockEndpointTV β d u x ω ^ 2 ∂disorderLaw)
  let Ccoord : ℝ := (∫ ω, ∑ w ∈ A,
      (η ω w - ν w) ^ 2 ∂disorderLaw)
  let Dflat : ℝ := T + Ccoord * K
  have hT : T ≤ 16 * (Real.exp (((u - d : ℕ) : ℝ) * β ^ 2) - 1) + 16 * Qvar := by
    exact hTV.2
  have hCcoord : Ccoord ≤
      8 * (R * (Real.exp (((u - d : ℕ) : ℝ) * β ^ 2) - 1)) +
        8 * R * Qvar + 8 * Qvar := by
    exact hCoord.2
  have hDflat : Dflat ≤
      (16 * (Real.exp (((u - d : ℕ) : ℝ) * β ^ 2) - 1) + 16 * Qvar) +
        (8 * (R * (Real.exp (((u - d : ℕ) : ℝ) * β ^ 2) - 1)) +
          8 * R * Qvar + 8 * Qvar) * K := by
    dsimp [Dflat, T, Ccoord]
    exact add_le_add hT (mul_le_mul_of_nonneg_right hCcoord hK)
  have hTnonneg : 0 ≤ T := by
    dsimp [T]
    exact integral_nonneg fun ω => sq_nonneg _
  have hCcoordnonneg : 0 ≤ Ccoord := by
    dsimp [Ccoord]
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun ω =>
      Finset.sum_nonneg fun w hw => sq_nonneg _)
  have hDflatnonneg : 0 ≤ Dflat := by dsimp [Dflat]; positivity
  have hDflatInt : Integrable (fun ω =>
      (X₀ ω - Y₀ ω) ^ 2) disorderLaw := by
    have h := integral_random_probability_profile_difference_sq_le_terminal_of_coord_sq
      β huM η (fun _ => ν) A (fun ω w hw => hηA ω w hw)
      (fun _ w hw => hνA w hw) hη0 (fun _ w => hν0 w) hη1 (fun _ => hν1)
      hηpast' hνpast (fun _ => 1) 1 (by norm_num)
      (by intro z; simp) 
    simpa [X₀, Y₀, T, Ccoord, η, ν, shortClockEndpointTV] using h.1
  have hDflatBound :
      (∫ ω, (X₀ ω - Y₀ ω) ^ 2 ∂disorderLaw) ≤ Dflat := by
    have h := integral_random_probability_profile_difference_sq_le_terminal_of_coord_sq
      β huM η (fun _ => ν) A (fun ω w hw => hηA ω w hw)
      (fun _ w hw => hνA w hw) hη0 (fun _ w => hν0 w) hη1 (fun _ => hν1)
      hηpast' hνpast (fun _ => 1) 1 (by norm_num)
      (by intro z; simp)
    have hraw : (∫ ω, (X₀ ω - Y₀ ω) ^ 2 ∂disorderLaw) ≤
        T + Ccoord *
          (∑ r ∈ Finset.Icc 1 (M - u), Polymer.sigmaSq β *
            (∫ ω, pointToPlane β 0 (M - u - r) 0 ω ^ 2 ∂disorderLaw)) := by
      simpa [X₀, Y₀, T, Ccoord, η, ν, shortClockEndpointTV] using h.2
    calc
      _ ≤ T + Ccoord *
          (∑ r ∈ Finset.Icc 1 (M - u), Polymer.sigmaSq β *
            (∫ ω, pointToPlane β 0 (M - u - r) 0 ω ^ 2 ∂disorderLaw)) := hraw
      _ ≤ Dflat := by
        dsimp [Dflat]
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hcollision hCcoordnonneg)
  have hX₀int : Integrable (fun ω => X₀ ω ^ 2) disorderLaw := by
    have hdata := FutureProfiles.integrableOn_profileP2Fun_sq_eq β huM η A
      (fun ω w hw => hηA ω w hw) hηbdd hηpast' Set.univ
    simpa [X₀, MeasureTheory.IntegrableOn, Measure.restrict_univ] using hdata.1
  have hEnergyInt : Integrable
      (fun ω => FutureProfiles.futureEnergy β u M (η ω)) disorderLaw := by
    have hdata := FutureProfiles.integrableOn_profileP2Fun_sq_eq β huM η A
      (fun ω w hw => hηA ω w hw) hηbdd hηpast' Set.univ
    simpa only [IntegrableOn, Measure.restrict_univ] using hdata.2
  have hEnergyEq := FutureProfiles.setIntegral_profileP2Fun_sq_eq β huM η A
    (fun ω w hw => hηA ω w hw) hηbdd hηpast' Set.univ MeasurableSet.univ
  have hEnergyEq' : (∫ ω, X₀ ω ^ 2 ∂disorderLaw) =
      ∫ ω, FutureProfiles.futureEnergy β u M (η ω) ∂disorderLaw := by
    simpa only [X₀, MeasureTheory.setIntegral_univ] using hEnergyEq
  have hX₀bound : (∫ ω, X₀ ω ^ 2 ∂disorderLaw) ≤ 2 * Qflat + 2 * Dflat := by
    have hmajorInt : Integrable (fun ω => 2 * Y₀ ω ^ 2 +
        2 * (X₀ ω - Y₀ ω) ^ 2) disorderLaw :=
      (hflatInt.const_mul 2).add (hDflatInt.const_mul 2)
    calc
      _ = ∫ ω, X₀ ω ^ 2 ∂disorderLaw := rfl
      _ ≤ ∫ ω, (2 * Y₀ ω ^ 2 + 2 * (X₀ ω - Y₀ ω) ^ 2) ∂disorderLaw := by
        apply integral_mono hX₀int hmajorInt
        intro ω
        dsimp [X₀, Y₀]
        nlinarith [sq_nonneg (X₀ ω - 2 * Y₀ ω)]
      _ = 2 * (∫ ω, Y₀ ω ^ 2 ∂disorderLaw) +
            2 * (∫ ω, (X₀ ω - Y₀ ω) ^ 2 ∂disorderLaw) := by
        rw [integral_add (hflatInt.const_mul 2) (hDflatInt.const_mul 2),
          integral_const_mul, integral_const_mul]
      _ ≤ 2 * Qflat + 2 * Dflat := by
        exact add_le_add (mul_le_mul_of_nonneg_left hflat (by norm_num))
          (mul_le_mul_of_nonneg_left hDflatBound (by norm_num))
  have hEnergy :
      (∫ ω, FutureProfiles.futureEnergy β u M (η ω) ∂disorderLaw) ≤
        2 * Qflat + 2 * Dflat := by
    rw [← hEnergyEq']
    exact hX₀bound
  let Qη : ℝ := 2 * Qflat + 2 * Dflat
  have hQη : 0 ≤ Qη := by dsimp [Qη]; positivity
  have hXinv := eLpNorm_inv_random_probability_profile_terminal_le_of_futureEnergy
    β hβ huM η A (fun ω w hw => hηA ω w hw) hη0 hη1 hηpast' hEnergyInt
    Qη hQη (by simpa [Qη] using hEnergy) f H hf
  have hYinv := eLpNorm_inv_profile_terminal_le_of_secondMoment β hβ u M ν A
    (fun w hw => hνA w hw) hν0 hν1 f H hf Qflat
    ⟨hflatInt, hflat⟩
  have hYinvMem : MemLp (fun ω => (Y ω)⁻¹) 1 disorderLaw := by
    rw [memLp_iff]
    exact hYinv.trans_lt ENNReal.ofReal_lt_top
  have hYinvInt : Integrable (fun ω => (Y ω)⁻¹) disorderLaw :=
    hYinvMem.integrable (by norm_num)
  have hXpos (ω : Disorder) : 0 < X ω := by
    exact profileP2Fun_pos_terminal β u M (η ω) f A (hηA ω) (hη0 ω)
      (by
        have hsum : 0 < ∑ w ∈ A, η ω w := by rw [hη1 ω]; norm_num
        exact (Finset.sum_pos_iff_of_nonneg (fun w hw => hη0 ω w)).mp hsum)
      (fun z => (hf z).1) ω
  have hYpos (ω : Disorder) : 0 < Y ω := by
    exact profileP2Fun_pos_terminal β u M ν f A
      hνA hν0
      (by
        have hsum : 0 < ∑ w ∈ A, ν w := by rw [hν1]; norm_num
        exact (Finset.sum_pos_iff_of_nonneg (fun w hw => hν0 w)).mp hsum)
      (fun z => (hf z).1) ω
  have hXmeas : Measurable X := by
    dsimp [X, η]
    exact measurable_profileP2Fun_param β u M f hηmeasFull measurable_id
  have hYmeas : Measurable Y := by
    dsimp [Y]
    exact measurable_profileP2Fun_param β u M f (fun _ => measurable_const) measurable_id
  have hFmem : MemLp (fun ω => Real.log (profileP2Fun β d M
      (fun w => srwKernel d (w - x)) f ω)) 2 disorderLaw := by
    apply memLp_log_profileP2Fun_of_bounded_terminal β d M
      (fun w => srwKernel d (w - x)) (Polymer.endpoints x d)
      (fun w hw => Polymer.srwKernel_eq_zero_of_not_mem d x w hw)
      (fun w => Polymer.kernel_nonneg d (w - x))
      (Polymer.sum_srwKernel_endpoints d x) f H hH hf
  have hGmem : MemLp (fun ω => Real.log (Y ω)) 2 disorderLaw := by
    dsimp [Y]
    exact memLp_log_profileP2Fun_of_bounded_terminal β u M ν A
      hνA hν0 hν1 f H hH hf
  have hDprof := integral_random_probability_profile_difference_sq_le_terminal_of_coord_sq
    β huM η (fun _ => ν) A (fun ω w hw => hηA ω w hw)
    (fun _ w hw => hνA w hw) hη0 (fun _ w => hν0 w) hη1 (fun _ => hν1)
    hηpast' hνpast f F hF hfb
  have hDprofBound :
      (∫ ω, (X ω - Y ω) ^ 2 ∂disorderLaw) ≤
        F ^ 2 * ((T + Ccoord * K)) := by
    have hraw : (∫ ω, (X ω - Y ω) ^ 2 ∂disorderLaw) ≤
        F ^ 2 * ((∫ ω, shortClockEndpointTV β d u x ω ^ 2 ∂disorderLaw) +
          (∫ ω, ∑ w ∈ Polymer.endpoints x u,
            (η ω w - ν w) ^ 2 ∂disorderLaw) *
            (∑ r ∈ Finset.Icc 1 (M - u), Polymer.sigmaSq β *
              (∫ ω, pointToPlane β 0 (M - u - r) 0 ω ^ 2 ∂disorderLaw))) := by
      simpa [X, Y, η, ν, shortClockEndpointTV] using hDprof.2
    calc
      _ ≤ F ^ 2 * ((∫ ω, shortClockEndpointTV β d u x ω ^ 2 ∂disorderLaw) +
          (∫ ω, ∑ w ∈ Polymer.endpoints x u,
            (η ω w - ν w) ^ 2 ∂disorderLaw) *
            (∑ r ∈ Finset.Icc 1 (M - u), Polymer.sigmaSq β *
              (∫ ω, pointToPlane β 0 (M - u - r) 0 ω ^ 2 ∂disorderLaw))) := hraw
      _ ≤ F ^ 2 * (T + Ccoord * K) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg F)
        dsimp [T, Ccoord]
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hcollision hCcoordnonneg)
  have hDprofInt : Integrable (fun ω => (X ω - Y ω) ^ 2) disorderLaw := by
    simpa [X, Y, η, ν] using hDprof.1
  have hDprofNonneg : 0 ≤ F ^ 2 * (T + Ccoord * K) := by positivity
  have hDmem : MemLp (fun ω => X ω - Y ω) 2 disorderLaw := by
    apply (memLp_two_iff_integrable_sq (hXmeas.sub hYmeas).aestronglyMeasurable).2
    exact hDprofInt
  have hDnorm : eLpNorm (fun ω => X ω - Y ω) 2 disorderLaw ≤
      ENNReal.ofReal (Real.sqrt (F ^ 2 * (T + Ccoord * K))) :=
    eLpNorm_le_of_integral_sq_le disorderLaw hDmem hDprofBound
  have hlog := eLpNorm_log_sub_le_of_sq_diff_inv disorderLaw
    (fun ω => X ω) (fun ω => Y ω) hXmeas hYmeas hXpos hYpos hDprofInt
    hXinv.1 hYinvInt
  have hDnormTop : eLpNorm (fun ω => X ω - Y ω) 2 disorderLaw < ⊤ :=
    hDnorm.trans_lt ENNReal.ofReal_lt_top
  have hXinvTop : eLpNorm (fun ω => (X ω)⁻¹) 1 disorderLaw < ⊤ :=
    hXinv.2.trans_lt ENNReal.ofReal_lt_top
  have hYinvTop : eLpNorm (fun ω => (Y ω)⁻¹) 1 disorderLaw < ⊤ :=
    hYinv.trans_lt ENNReal.ofReal_lt_top
  have hlogTop : ENNReal.ofReal logHolderConstant *
      eLpNorm (fun ω => X ω - Y ω) 2 disorderLaw ^ ((1 : ℝ) / 3) *
      (eLpNorm (fun ω => (X ω)⁻¹) 1 disorderLaw ^ ((1 : ℝ) / 3) +
        eLpNorm (fun ω => (Y ω)⁻¹) 1 disorderLaw ^ ((1 : ℝ) / 3)) < ⊤ := by
    apply ENNReal.mul_lt_top
    · apply ENNReal.mul_lt_top
      · exact ENNReal.ofReal_lt_top
      · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hDnormTop.ne
    · exact ENNReal.add_lt_top.mpr ⟨
        ENNReal.rpow_lt_top_of_nonneg (by norm_num) hXinvTop.ne,
        ENNReal.rpow_lt_top_of_nonneg (by norm_num) hYinvTop.ne⟩
  have hDlogmem : MemLp (fun ω => Real.log (X ω) - Real.log (Y ω))
      2 disorderLaw := by
    rw [memLp_iff]
    exact hlog.trans_lt hlogTop
  have hXmem : MemLp (fun ω => Real.log (X ω)) 2 disorderLaw := by
    have heq : (fun ω => Real.log (X ω)) =
        (fun ω => Real.log (Y ω)) + (fun ω => Real.log (X ω) - Real.log (Y ω)) := by
      funext ω
      change Real.log (X ω) = Real.log (Y ω) +
        (Real.log (X ω) - Real.log (Y ω))
      ring
    rw [heq]
    exact hGmem.add hDlogmem
  have hcent := eLpNorm_centered_sub_le_two disorderLaw
    (fun ω => Real.log (X ω)) (fun ω => Real.log (Y ω)) hXmem hGmem
  have hZmem : MemLp (fun ω => smoothedP2Plane β d u x ω) 2 disorderLaw :=
    Polymer.memLp_smoothedP2Plane β d u x 2 (by norm_num)
  have hZsqInt : Integrable (fun ω => smoothedP2Plane β d u x ω ^ 2) disorderLaw := by
    have h := hZmem.integrable_norm_pow'
    simpa only [Real.norm_eq_abs, sq_abs] using h
  have hvar2 : (∫ ω, smoothedP2Plane β d u x ω ^ 2 ∂disorderLaw) ≤ 1 + Qvar := by
    have hZint : Integrable (fun ω => smoothedP2Plane β d u x ω) disorderLaw :=
      hZmem.integrable (by norm_num)
    have hmean : (∫ ω, smoothedP2Plane β d u x ω ∂disorderLaw) = 1 :=
      Polymer.integral_smoothedP2Plane β d u x
    have hlinInt : Integrable (fun ω => 2 * smoothedP2Plane β d u x ω - 1) disorderLaw :=
      (hZint.const_mul 2).sub (integrable_const 1)
    have hlin : (∫ ω, 2 * smoothedP2Plane β d u x ω - 1 ∂disorderLaw) = 1 := by
      rw [integral_sub (hZint.const_mul 2) (integrable_const 1), integral_const_mul, hmean]
      norm_num
    have hiden : (∫ ω, smoothedP2Plane β d u x ω ^ 2 ∂disorderLaw) =
        (∫ ω, (smoothedP2Plane β d u x ω - 1) ^ 2 ∂disorderLaw) + 1 := by
      calc
        _ = ∫ ω, (smoothedP2Plane β d u x ω - 1) ^ 2 +
              (2 * smoothedP2Plane β d u x ω - 1) ∂disorderLaw := by
          apply integral_congr_ae
          filter_upwards [] with ω
          ring
        _ = _ := by rw [integral_add hvarInt hlinInt, hlin]
    rw [hiden]
    linarith
  let νd : Site → ℝ := fun w => srwKernel d (w - x)
  let Ad := Polymer.endpoints x d
  have hνdA (w : Site) (hw : w ∉ Ad) : νd w = 0 := by
    exact Polymer.srwKernel_eq_zero_of_not_mem d x w (by simpa [Ad] using hw)
  have hνd0 (w : Site) : 0 ≤ νd w := Polymer.kernel_nonneg d (w - x)
  have hνd1 : ∑ w ∈ Ad, νd w = 1 := by
    simpa [νd, Ad] using Polymer.sum_srwKernel_endpoints d x
  have hZflatEq (ω : Disorder) :
      profileP2Fun β d u νd (fun _ => 1) ω = smoothedP2Plane β d u x ω := by
    simpa [νd] using Polymer.profileP2Fun_srw_flat β d u x ω
  have hZflatSq : Integrable
        (fun ω => profileP2Fun β d u νd (fun _ => 1) ω ^ 2) disorderLaw ∧
      (∫ ω, profileP2Fun β d u νd (fun _ => 1) ω ^ 2 ∂disorderLaw) ≤ 1 + Qvar := by
    constructor
    · simpa only [hZflatEq] using hZsqInt
    · simpa only [hZflatEq] using hvar2
  have hZinv := eLpNorm_inv_profile_terminal_le_of_secondMoment β hβ d u νd Ad
    hνdA hνd0 hνd1 (fun _ => 1) 0 (by intro z; simp)
    (1 + Qvar) hZflatSq
  have hZinvBound : eLpNorm (fun ω => (smoothedP2Plane β d u x ω)⁻¹)
      1 disorderLaw ≤ ENNReal.ofReal (1 + Qvar) := by
    simpa [hZflatEq] using hZinv
  have hZinvMem : MemLp (fun ω => (smoothedP2Plane β d u x ω)⁻¹)
      1 disorderLaw := by
    rw [memLp_iff]
    exact hZinvBound.trans_lt ENNReal.ofReal_lt_top
  have hZinvInt : Integrable (fun ω => (smoothedP2Plane β d u x ω)⁻¹)
      disorderLaw := hZinvMem.integrable (by norm_num)
  have hZdiffmem : MemLp
      (fun ω => smoothedP2Plane β d u x ω - 1) 2 disorderLaw := by
    change MemLp ((fun ω => smoothedP2Plane β d u x ω) - (fun _ => (1 : ℝ)))
      2 disorderLaw
    exact hZmem.sub (memLp_const (1 : ℝ))
  have hZdiffnorm : eLpNorm
      (fun ω => smoothedP2Plane β d u x ω - 1) 2 disorderLaw ≤
        ENNReal.ofReal (Real.sqrt Qvar) :=
    eLpNorm_le_of_integral_sq_le disorderLaw hZdiffmem hvar
  have hZlog := eLpNorm_log_sub_le_of_sq_diff_inv disorderLaw
    (fun ω => smoothedP2Plane β d u x ω) (fun _ => 1)
    (Polymer.measurable_smoothedP2Plane β d u x) measurable_const
    (fun ω => Polymer.smoothedP2Plane_pos β d u x ω) (by intro ω; norm_num)
    hvarInt hZinvInt (by simp)
  have hdisorderLawNe : disorderLaw ≠ 0 := by
    intro hzero
    have h := congrArg (fun μ : Measure Disorder => μ Set.univ) hzero
    simp at h
  have hnormOne : eLpNorm (fun _ : Disorder => (1 : ℝ)) 1 disorderLaw = 1 := by
    rw [eLpNorm_const (1 : ℝ) (by norm_num) hdisorderLawNe]
    simp
  have hZlogBound : eLpNorm
      (fun ω => Real.log (smoothedP2Plane β d u x ω)) 2 disorderLaw ≤
        ENNReal.ofReal logHolderConstant * ENNReal.ofReal (Real.sqrt Qvar) ^
            ((1 : ℝ) / 3) *
          ((ENNReal.ofReal (1 + Qvar)) ^ ((1 : ℝ) / 3) + 1) := by
    calc
      _ = eLpNorm (fun ω => Real.log (smoothedP2Plane β d u x ω) - Real.log 1)
          2 disorderLaw := by congr 1; funext ω; simp
      _ ≤ ENNReal.ofReal logHolderConstant *
          eLpNorm (fun ω => smoothedP2Plane β d u x ω - 1) 2 disorderLaw ^
            ((1 : ℝ) / 3) *
          (eLpNorm (fun ω => (smoothedP2Plane β d u x ω)⁻¹) 1 disorderLaw ^
              ((1 : ℝ) / 3) +
            eLpNorm (fun _ : Disorder => (1 : ℝ)⁻¹) 1 disorderLaw ^
              ((1 : ℝ) / 3)) := hZlog
      _ ≤ _ := by
        gcongr
        have hconstInv : (fun _ : Disorder => (1 : ℝ)⁻¹) = fun _ => 1 := by
          funext ω
          norm_num
        rw [hconstInv]
        rw [hnormOne]
        norm_num
  have hXinvBound : eLpNorm (fun ω => (X ω)⁻¹) 1 disorderLaw ≤ ENNReal.ofReal
      (Real.exp H * (2 * Qflat + 2 * (T + Ccoord * K))) := by
    simpa [X, Qη, Dflat] using hXinv.2
  have hlogBound : eLpNorm (fun ω => Real.log (X ω) - Real.log (Y ω)) 2 disorderLaw ≤
      ENNReal.ofReal logHolderConstant *
        ENNReal.ofReal (Real.sqrt (F ^ 2 * (T + Ccoord * K))) ^ ((1 : ℝ) / 3) *
        ((ENNReal.ofReal (Real.exp H * (2 * Qflat + 2 * (T + Ccoord * K)))) ^
            ((1 : ℝ) / 3) +
          (ENNReal.ofReal (Real.exp H * Qflat)) ^ ((1 : ℝ) / 3)) := by
    calc
      _ ≤ ENNReal.ofReal logHolderConstant *
          eLpNorm (fun ω => X ω - Y ω) 2 disorderLaw ^ ((1 : ℝ) / 3) *
          (eLpNorm (fun ω => (X ω)⁻¹) 1 disorderLaw ^ ((1 : ℝ) / 3) +
            eLpNorm (fun ω => (Y ω)⁻¹) 1 disorderLaw ^ ((1 : ℝ) / 3)) := hlog
      _ ≤ _ := by gcongr
  let Z : Disorder → ℝ := fun ω => smoothedP2Plane β d u x ω
  let Sraw : Disorder → ℝ := fun ω =>
    Real.log (profileP2Fun β d M (fun w => srwKernel d (w - x)) f ω) -
      Real.log (profileP2Fun β u M ν f ω)
  have hrawdecomp : Sraw =
      (fun ω => Real.log (Z ω)) + (fun ω => Real.log (X ω) - Real.log (Y ω)) := by
    funext ω
    dsimp [Sraw, Z, X, Y, η, ν]
    rw [log_profileP2Fun_srwKernel_shortClock_decomp β hdu huM x f
      (fun z => (hf z).1) ω]
    ring
  have hrawsum : eLpNorm (fun ω =>
      Real.log (profileP2Fun β d M (fun w => srwKernel d (w - x)) f ω) -
        Real.log (profileP2Fun β u M ν f ω)) 2 disorderLaw ≤
      ENNReal.ofReal logHolderConstant * ENNReal.ofReal (Real.sqrt Qvar) ^
          ((1 : ℝ) / 3) *
        ((ENNReal.ofReal (1 + Qvar)) ^ ((1 : ℝ) / 3) + 1) +
      ENNReal.ofReal logHolderConstant *
        ENNReal.ofReal (Real.sqrt (F ^ 2 * (T + Ccoord * K))) ^ ((1 : ℝ) / 3) *
        ((ENNReal.ofReal (Real.exp H * (2 * Qflat + 2 * (T + Ccoord * K))) ^
            ((1 : ℝ) / 3)) +
          (ENNReal.ofReal (Real.exp H * Qflat)) ^ ((1 : ℝ) / 3)) := by
    change eLpNorm Sraw 2 disorderLaw ≤ _
    calc
      _ = eLpNorm ((fun ω => Real.log (Z ω)) +
          (fun ω => Real.log (X ω) - Real.log (Y ω))) 2 disorderLaw := by
            rw [hrawdecomp]
      _ ≤ eLpNorm (fun ω => Real.log (Z ω)) 2 disorderLaw +
          eLpNorm (fun ω => Real.log (X ω) - Real.log (Y ω)) 2 disorderLaw :=
            eLpNorm_add_le (by norm_num)
      _ ≤ _ := add_le_add hZlogBound hlogBound
  simpa [T, Ccoord, Dflat, Qη] using hrawsum

end Critical2DKPZ.Smoothing

end
