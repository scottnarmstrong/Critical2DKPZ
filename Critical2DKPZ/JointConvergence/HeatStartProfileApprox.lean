/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.JointConvergence.ProfileL1Bound
public import Critical2DKPZ.Analysis.Lattice.Volume
public import Critical2DKPZ.Analysis.Heat.Semigroup
public import Critical2DKPZ.SHF.Limit.FirstMoment
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Tactic

/-! # Cell formula for a lattice heat-start profile -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators BoundedContinuousFunction ENNReal

namespace Critical2DKPZ.JointConvergence

/-- Pairing the polymer measure with a heat start and a cell-averaged terminal weight is the
profile pairing whose initial weights are the heat masses of the lattice cells. -/
theorem profile_cellHeat_eq_polymerMeasure_pairing (ϑ : ℝ) (N : ℕ) (s T δ : ℝ)
    (x : Plane) (h₀ : Plane →ᵇ ℝ) (ω : Disorder) (hN : 0 < N)
    (hInt : Integrable
      (fun p : Plane × Plane => heatKernel δ (p.1 - x) * Real.exp (h₀ p.2))
      (SHF.Limit.polymerMeasure ϑ N s T ω)) :
    profileP2Fun (criticalBeta ϑ N) (evenCeil (N * s)) (evenCeil (N * T))
      (fun w => ∫ y in cell N w, heatKernel δ (y - x))
      (fun z => cellAverage N (fun y => Real.exp (h₀ y)) z) ω =
      ∫ p, heatKernel δ (p.1 - x) * Real.exp (h₀ p.2)
        ∂(SHF.Limit.polymerMeasure ϑ N s T ω) := by
  classical
  let β : ℝ := criticalBeta ϑ N
  let a : ℕ := evenCeil (N * s)
  let b : ℕ := evenCeil (N * T)
  let H : Plane → ℝ := fun y => heatKernel δ (y - x)
  let G : Plane → ℝ := fun y => Real.exp (h₀ y)
  let ν : Site → ℝ := fun w => ∫ y in cell N w, H y
  let f : Site → ℝ := fun z => cellAverage N G z
  let C : Site × Site → Set (Plane × Plane) := fun q => cell N q.1 ×ˢ cell N q.2
  have hden : Measurable (fun p : Plane × Plane =>
      ENNReal.ofReal (rescaledP2P ϑ N s T p ω)) := by
    exact ENNReal.measurable_ofReal.comp
      (SHF.Moments.measurable_uncurry_rescaledP2P ϑ N s T |>.of_uncurry_right)
  have hdenFinite : ∀ᵐ p ∂(volume : Measure (Plane × Plane)),
      ENNReal.ofReal (rescaledP2P ϑ N s T p ω) < ⊤ := by
    filter_upwards [] with p
    exact ENNReal.ofReal_lt_top
  have hvolInt : Integrable (fun p : Plane × Plane =>
      (H p.1 * G p.2) * rescaledP2P ϑ N s T p ω) (volume : Measure (Plane × Plane)) := by
    change Integrable (fun p : Plane × Plane => H p.1 * G p.2)
      ((volume : Measure (Plane × Plane)).withDensity
        (fun p => ENNReal.ofReal (rescaledP2P ϑ N s T p ω))) at hInt
    have h := (integrable_withDensity_iff hden hdenFinite).mp hInt
    simpa only [ENNReal.toReal_ofReal (SHF.Moments.rescaledP2P_nonneg ϑ N s T _ ω)] using h
  have hcover : ⋃ q : Site × Site, C q = Set.univ := by
    apply Set.eq_univ_of_forall
    intro p
    refine Set.mem_iUnion.mpr ⟨(latticePoint N p.1, latticePoint N p.2), ?_⟩
    exact ⟨mem_cell_latticePoint N p.1, mem_cell_latticePoint N p.2⟩
  have hCmeas : ∀ q : Site × Site, MeasurableSet (C q) := by
    intro q
    exact (measurableSet_cell N q.1).prod (measurableSet_cell N q.2)
  have hCdisj : Pairwise (fun q r => Disjoint (C q) (C r)) := by
    intro q r hqr
    apply Set.disjoint_left.mpr
    rintro p ⟨hp₁, hp₂⟩ ⟨hr₁, hr₂⟩
    by_cases hfirst : q.1 = r.1
    · have hsecond : q.2 ≠ r.2 := by
        intro h
        exact hqr (Prod.ext hfirst h)
      exact (pairwise_disjoint_cell N hsecond).le_bot ⟨hp₂, hr₂⟩
    · exact (pairwise_disjoint_cell N hfirst).le_bot ⟨hp₁, hr₁⟩
  have hcellHasSum : HasSum
      (fun q : Site × Site => ∫ p in C q,
        (H p.1 * G p.2) * rescaledP2P ϑ N s T p ω
          ∂(volume : Measure (Plane × Plane)))
      (∫ p, (H p.1 * G p.2) * rescaledP2P ϑ N s T p ω
        ∂(volume : Measure (Plane × Plane))) := by
    have h := hasSum_integral_iUnion hCmeas hCdisj hvolInt.integrableOn
    simpa only [hcover, setIntegral_univ] using h
  have hdecomp := integral_iUnion hCmeas hCdisj hvolInt.integrableOn
  rw [hcover, setIntegral_univ] at hdecomp
  have hcell (w z : Site) :
      (∫ p in C (w, z), (H p.1 * G p.2) * rescaledP2P ϑ N s T p ω
        ∂(volume : Measure (Plane × Plane))) =
      ν w * f z * pointToPoint β a (b - a) w z ω := by
    have hconst (p : Plane × Plane) (hp : p ∈ C (w, z)) :
      rescaledP2P ϑ N s T p ω = (N : ℝ) / 4 *
          pointToPoint β a (b - a) w z ω := by
      have hp' : p.1 ∈ cell N w ∧ p.2 ∈ cell N z := hp
      have hfirst : latticePoint N p.1 = w := (mem_cell_iff N w p.1).mp hp'.1
      have hsecond : latticePoint N p.2 = z := (mem_cell_iff N z p.2).mp hp'.2
      rw [rescaledP2P, hfirst, hsecond]
    rw [Measure.volume_eq_prod]
    rw [setIntegral_congr_fun (hCmeas (w, z)) (fun p hp => by rw [hconst p hp])]
    rw [show (fun p : Plane × Plane =>
        H p.1 * G p.2 * ((N : ℝ) / 4 *
          pointToPoint β a (b - a) w z ω)) =
        fun p => (H p.1 * G p.2) * ((N : ℝ) / 4 *
          pointToPoint β a (b - a) w z ω) by funext p; ring]
    rw [integral_mul_const, setIntegral_prod_mul]
    have hfcell : (N : ℝ) / 4 * (∫ y in cell N z, G y) = f z := by
      by_cases hz : z ∈ evenLattice
      · have hv := volume_cell_toReal hN hz
        dsimp [f, cellAverage]
        rw [hv]
        field_simp
      · have hcellEmpty : cell N z = ∅ := cell_eq_empty_of_not_even hz
        simp [f, cellAverage, hcellEmpty]
    dsimp [ν]
    rw [← hfcell]
    ring
  have hpairSummable : Summable (fun q : Site × Site =>
      ν q.1 * (pointToPoint β a (b - a) q.1 q.2 ω * f q.2)) := by
    apply hcellHasSum.summable.congr
    intro q
    rcases q with ⟨w, z⟩
    rw [hcell]
    ring
  have hinnerSummable (w : Site) : Summable (fun z : Site =>
      ν w * (pointToPoint β a (b - a) w z ω * f z)) := by
    apply Summable.mul_left
    apply summable_of_ne_finset_zero (s := Polymer.endpoints w (b - a))
    intro z hz
    rw [Polymer.pointToPoint_eq_zero_of_not_mem β a (b - a) w z ω hz]
    simp
  calc
    _ = ∑' q : Site × Site, ∫ p in C q,
        (H p.1 * G p.2) * rescaledP2P ϑ N s T p ω
          ∂(volume : Measure (Plane × Plane)) := by
      unfold profileP2Fun
      calc
        (∑' w : Site, ν w * ∑' z : Site,
            pointToPoint β a (b - a) w z ω * f z) =
          ∑' w : Site, ∑' z : Site,
            ν w * (pointToPoint β a (b - a) w z ω * f z) := by
              congr 1
              funext w
              rw [← tsum_mul_left]
        _ = ∑' q : Site × Site,
            ν q.1 * (pointToPoint β a (b - a) q.1 q.2 ω * f q.2) :=
              (hpairSummable.tsum_prod' hinnerSummable).symm
        _ = ∑' q : Site × Site, ∫ p in C q,
            (H p.1 * G p.2) * rescaledP2P ϑ N s T p ω
              ∂(volume : Measure (Plane × Plane)) := by
                apply tsum_congr
                rintro ⟨w, z⟩
                rw [hcell]
                ring
    _ = ∫ p, H p.1 * G p.2 ∂(SHF.Limit.polymerMeasure ϑ N s T ω) := by
      rw [SHF.Limit.integral_polymerMeasure]
      simpa only [H, G] using hdecomp.symm

/-- Heat-kernel cell masses form a probability profile. -/
theorem heatKernel_cellMass_probability {N : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (x : Plane) :
    (∀ w : Site, 0 ≤ ∫ y in cell N w, heatKernel δ (y - x)) ∧
      (∑' w : Site, ∫ y in cell N w, heatKernel δ (y - x)) = 1 ∧
      Summable (fun w : Site => |∫ y in cell N w, heatKernel δ (y - x)|) := by
  have hcover : ⋃ w : Site, cell N w = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    exact Set.mem_iUnion.mpr ⟨latticePoint N y, mem_cell_latticePoint N y⟩
  have hhasSum : HasSum
      (fun w : Site => ∫ y in cell N w, heatKernel δ (y - x))
      (∫ y : Plane, heatKernel δ (y - x)) := by
    have h := hasSum_integral_iUnion (fun w : Site => measurableSet_cell N w)
      (pairwise_disjoint_cell N) ((integrable_heatKernel hδ).comp_sub_right x).integrableOn
    simpa only [hcover, setIntegral_univ] using h
  have htotal : (∑' w : Site, ∫ y in cell N w, heatKernel δ (y - x)) = 1 := by
    rw [hhasSum.tsum_eq, integral_heatKernel_sub hδ x]
  have hnonneg : ∀ w : Site, 0 ≤ ∫ y in cell N w, heatKernel δ (y - x) := by
    intro w
    exact integral_nonneg (fun y => heatKernel_nonneg hδ.le (y - x))
  have habs : Summable (fun w : Site => |∫ y in cell N w, heatKernel δ (y - x)|) := by
    apply hhasSum.summable.congr
    intro w
    exact (abs_of_nonneg (hnonneg w)).symm
  exact ⟨hnonneg, htotal, habs⟩

/-- The mean absolute change of a polymer profile is bounded by the `ℓ¹` change in its initial
weights. The `MemLp` conjunct records integrability of the difference. -/
theorem memLp_lintegral_abs_profileP2Fun_sub_le (β : ℝ) (a b : ℕ)
    (ν μ f : Site → ℝ) (hν : Summable (fun w => |ν w|))
    (hμ : Summable (fun w => |μ w|)) (hνμ : Summable (fun w => |ν w - μ w|))
    (M : ℝ) (hM : 0 ≤ M) (hf : ∀ z, 0 ≤ f z ∧ f z ≤ M) :
    MemLp (fun ω => profileP2Fun β a b ν f ω - profileP2Fun β a b μ f ω)
        1 disorderLaw ∧
      ∫⁻ ω, ENNReal.ofReal
          |profileP2Fun β a b ν f ω - profileP2Fun β a b μ f ω| ∂disorderLaw ≤
        ENNReal.ofReal M * ∑' w, ENNReal.ofReal |ν w - μ w| := by
  classical
  have hfabs : ∀ z, |f z| ≤ M := by
    intro z
    rw [abs_of_nonneg (hf z).1]
    exact (hf z).2
  let term (η : Site → ℝ) (w : Site) (ω : Disorder) : ℝ :=
    η w * ∑' z, pointToPoint β a (b - a) w z ω * f z
  let F (η : Site → ℝ) (w : Site) : Lp ℝ 1 disorderLaw :=
    ((Polymer.memLp_terminalProfile β a (b - a) w f 1 (by norm_num)).const_mul
      (η w)).toLp (term η w)
  have htermAE (η : Site → ℝ) (w : Site) :
      (F η w : Disorder → ℝ) =ᵐ[disorderLaw] term η w := by
    exact ((Polymer.memLp_terminalProfile β a (b - a) w f 1 (by norm_num)).const_mul
      (η w)).coeFn_toLp
  have hsumFinite (η : Site → ℝ) (hη : Summable (fun w => |η w|)) :
      (∑' w, ‖F η w‖ₑ) ≠ ∞ := by
    have h := Polymer.profile_term_norms_ne_top β a b η f hη M hM hfabs 1 (by norm_num)
    simpa only [F, term, Lp.enorm_toLp] using h
  have hFsum (η : Site → ℝ) (hη : Summable (fun w => |η w|)) : Summable (F η) :=
    Summable.of_enorm (hsumFinite η hη)
  have hseries (η : Site → ℝ) (hη : Summable (fun w => |η w|)) :
      (fun ω => (∑' w, F η w) ω) =ᵐ[disorderLaw]
        fun ω => profileP2Fun β a b η f ω := by
    have hcoe := Lp.coeFn_tsum (f := F η) (hsumFinite η hη)
    have htermAll : ∀ᵐ ω ∂disorderLaw, ∀ w, (F η w : Disorder → ℝ) ω = term η w ω :=
      ae_all_iff.2 (htermAE η)
    filter_upwards [hcoe, htermAll] with ω hω hall
    rw [hω]
    calc
      ∑' w, (F η w : Disorder → ℝ) ω = ∑' w, term η w ω := tsum_congr hall
      _ = profileP2Fun β a b η f ω := by simp only [term, profileP2Fun]
  have htermSub (w : Site) : F ν w - F μ w = F (fun z => ν z - μ z) w := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub (F ν w) (F μ w), htermAE ν w, htermAE μ w,
      htermAE (fun z => ν z - μ z) w] with ω hsub hνw hμw hdiffw
    calc
      (F ν w - F μ w : Lp ℝ 1 disorderLaw) ω =
          (F ν w : Disorder → ℝ) ω - (F μ w) ω := hsub
      _ = term ν w ω - term μ w ω := by rw [hνw, hμw]
      _ = term (fun z => ν z - μ z) w ω := by dsimp [term]; ring
      _ = (F (fun z => ν z - μ z) w : Disorder → ℝ) ω := hdiffw.symm
  have hsumSub : (∑' w, F ν w) - (∑' w, F μ w) =
      ∑' w, F (fun z => ν z - μ z) w := by
    calc
      (∑' w, F ν w) - (∑' w, F μ w) = ∑' w, (F ν w - F μ w) :=
        ((hFsum ν hν).tsum_sub (hFsum μ hμ)).symm
      _ = ∑' w, F (fun z => ν z - μ z) w := tsum_congr htermSub
  have hprofileSub :
      (fun ω => profileP2Fun β a b ν f ω - profileP2Fun β a b μ f ω) =ᵐ[disorderLaw]
        fun ω => profileP2Fun β a b (fun z => ν z - μ z) f ω := by
    have hsumSubAE := Lp.ext_iff.mp hsumSub
    have hsubAE := Lp.coeFn_sub (∑' w, F ν w) (∑' w, F μ w)
    filter_upwards [hseries ν hν, hseries μ hμ, hseries (fun z => ν z - μ z) hνμ,
      hsumSubAE, hsubAE] with ω hνeq hμeq hdiffEq hsumω hsubω
    calc
      profileP2Fun β a b ν f ω - profileP2Fun β a b μ f ω =
          (∑' w, F ν w) ω - (∑' w, F μ w) ω := by rw [hνeq, hμeq]
      _ = ((∑' w, F ν w) - (∑' w, F μ w) : Lp ℝ 1 disorderLaw) ω := hsubω.symm
      _ = (∑' w, F (fun z => ν z - μ z) w) ω := hsumω
      _ = profileP2Fun β a b (fun z => ν z - μ z) f ω := hdiffEq
  have hdiffMem : MemLp (profileP2Fun β a b (fun z => ν z - μ z) f) 1 disorderLaw :=
    Polymer.memLp_profileP2Fun_summable β a b (fun z => ν z - μ z) f hνμ M hM hfabs
      1 (by norm_num)
  have hbound := memLp_one_profileP2Fun_le_of_summable β a b
    (fun z => ν z - μ z) f hνμ M hM hf
  have hdiffBound := hbound.2
  have hMem : MemLp
      (fun ω => profileP2Fun β a b ν f ω - profileP2Fun β a b μ f ω)
      1 disorderLaw := (memLp_congr_ae hprofileSub).2 hdiffMem
  refine ⟨hMem, ?_⟩
  calc
    ∫⁻ ω, ENNReal.ofReal
        |profileP2Fun β a b ν f ω - profileP2Fun β a b μ f ω| ∂disorderLaw =
      ∫⁻ ω, ‖profileP2Fun β a b ν f ω - profileP2Fun β a b μ f ω‖ₑ ∂disorderLaw := by
        apply lintegral_congr
        intro ω
        exact (Real.enorm_eq_ofReal_abs _).symm
    _ = eLpNorm (fun ω => profileP2Fun β a b ν f ω - profileP2Fun β a b μ f ω)
        1 disorderLaw := (eLpNorm_one_eq_lintegral_enorm hMem.aestronglyMeasurable).symm
    _ = eLpNorm (profileP2Fun β a b (fun z => ν z - μ z) f) 1 disorderLaw :=
      eLpNorm_congr_ae hprofileSub
    _ ≤ ENNReal.ofReal M * ∑' w, ENNReal.ofReal |ν w - μ w| := hdiffBound

/-- An exponential tail controls every positive absolute moment. The first conjunct is the
integrability companion for the integral bound. -/
theorem integrable_rpow_of_exp_tail {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {f : Ω → ℝ} {C p : ℝ}
    (hf : AEMeasurable f P) (hC : 0 ≤ C) (hp : 0 < p)
    (htail : ∀ u : ℝ, 0 ≤ u → (P {ω | u < |f ω|}).toReal ≤ C * Real.exp (-u)) :
    Integrable (fun ω => |f ω| ^ p) P ∧
      ∫ ω, |f ω| ^ p ∂P ≤ C * p * Real.Gamma p := by
  have habs : AEMeasurable (fun ω => |f ω|) P := measurable_abs.aemeasurable.comp_aemeasurable hf
  have htailENN (u : ℝ) (hu : 0 < u) :
      P {ω | u < |f ω|} ≤ ENNReal.ofReal (C * Real.exp (-u)) := by
    have hfin : P {ω | u < |f ω|} ≠ ∞ := measure_ne_top P _
    have hnonneg : 0 ≤ C * Real.exp (-u) := mul_nonneg hC (Real.exp_nonneg _)
    rw [← ENNReal.ofReal_toReal hfin]
    exact ENNReal.ofReal_le_ofReal (htail u hu.le)
  have htailFormula := lintegral_rpow_eq_lintegral_meas_lt_mul P
    (Filter.Eventually.of_forall fun ω => abs_nonneg (f ω)) habs hp
  have hGammaIntegrable : IntegrableOn
      (fun t : ℝ => C * (Real.exp (-t) * t ^ (p - 1))) (Set.Ioi 0) := by
    exact (Real.GammaIntegral_convergent hp).const_mul C
  have hGammaEval :
      (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * t ^ (p - 1)) = Real.Gamma p := by
    have h := integral_rpow_mul_exp_neg_rpow (p := 1) (q := p - 1) one_pos
      (by linarith : -1 < p - 1)
    calc
      (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * t ^ (p - 1)) =
          ∫ t in Set.Ioi (0 : ℝ), t ^ (p - 1) * Real.exp (-t) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro t ht
            ring
      _ = Real.Gamma p := by simpa using h
  have hGammaReal :
      (∫ t in Set.Ioi (0 : ℝ), C * (Real.exp (-t) * t ^ (p - 1))) =
        C * Real.Gamma p := by
    rw [integral_const_mul, hGammaEval]
  have hGammaAE : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      0 ≤ C * (Real.exp (-t) * t ^ (p - 1)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact mul_nonneg hC (mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg ht.le _))
  have hGammaLin :
      ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal
          (C * (Real.exp (-t) * t ^ (p - 1))) =
        ENNReal.ofReal (C * Real.Gamma p) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hGammaIntegrable hGammaAE, hGammaReal]
  have htailInt :
      ∫⁻ t in Set.Ioi (0 : ℝ), P {ω | t < |f ω|} * ENNReal.ofReal (t ^ (p - 1)) ≤
        ENNReal.ofReal (C * Real.Gamma p) := by
    calc
      _ ≤ ∫⁻ t in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (C * Real.exp (-t)) * ENNReal.ofReal (t ^ (p - 1)) := by
            apply lintegral_mono_ae
            filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
            exact mul_le_mul_of_nonneg_right (htailENN t ht)
              (by positivity)
      _ = ∫⁻ t in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (C * (Real.exp (-t) * t ^ (p - 1))) := by
            apply lintegral_congr_ae
            filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
            rw [← ENNReal.ofReal_mul (mul_nonneg hC (Real.exp_nonneg _))]
            congr 1
            ring
      _ = ENNReal.ofReal (C * Real.Gamma p) := hGammaLin
  have hmomentLin :
      ∫⁻ ω, ENNReal.ofReal (|f ω| ^ p) ∂P ≤
        ENNReal.ofReal (C * p * Real.Gamma p) := by
    rw [htailFormula]
    calc
      ENNReal.ofReal p *
          ∫⁻ t in Set.Ioi (0 : ℝ), P {ω | t < |f ω|} * ENNReal.ofReal (t ^ (p - 1)) ≤
          ENNReal.ofReal p * ENNReal.ofReal (C * Real.Gamma p) :=
            mul_le_mul_of_nonneg_left htailInt (by positivity)
      _ = ENNReal.ofReal (C * p * Real.Gamma p) := by
        rw [← ENNReal.ofReal_mul hp.le]
        congr 1
        ring
  have hpowMeas : AEStronglyMeasurable (fun ω => |f ω| ^ p) P := by
    exact ((Real.continuous_rpow_const hp.le).comp continuous_abs).aestronglyMeasurable.comp_aemeasurable hf
  have hpowNonneg : ∀ ω, 0 ≤ |f ω| ^ p := fun ω => Real.rpow_nonneg (abs_nonneg _) _
  have hpowInt : Integrable (fun ω => |f ω| ^ p) P := by
    refine ⟨hpowMeas, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hpowNonneg)]
    exact (lt_of_le_of_lt hmomentLin ENNReal.ofReal_lt_top)
  have hmomentReal : C * p * Real.Gamma p ≥ 0 := by positivity
  have hrealBound :
      ENNReal.ofReal (∫ ω, |f ω| ^ p ∂P) ≤ ENNReal.ofReal (C * p * Real.Gamma p) := by
    rw [ofReal_integral_eq_lintegral_ofReal hpowInt
      (Filter.Eventually.of_forall hpowNonneg)]
    exact hmomentLin
  refine ⟨hpowInt, ?_⟩
  have hboundToReal := ENNReal.toReal_mono (ENNReal.ofReal_ne_top (r :=
    C * p * Real.Gamma p)) hrealBound
  rw [ENNReal.toReal_ofReal (integral_nonneg_of_ae
    (Filter.Eventually.of_forall hpowNonneg)), ENNReal.toReal_ofReal hmomentReal] at hboundToReal
  exact hboundToReal

/-- Shifting an exponential tail by the logarithm of its prefactor gives a moment bound whose
growth is logarithmic in that prefactor. The first conjunct records integrability. -/
theorem integrable_rpow_of_exp_tail_log_coefficient {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {f : Ω → ℝ} {C p : ℝ}
    (hf : AEMeasurable f P) (hC : 1 ≤ C) (hp : 0 < p)
    (htail : ∀ u : ℝ, 0 ≤ u → (P {ω | u < |f ω|}).toReal ≤ C * Real.exp (-u)) :
    Integrable (fun ω => |f ω| ^ p) P ∧
      ∫ ω, |f ω| ^ p ∂P ≤
        2 ^ p * (Real.log C ^ p + p * Real.Gamma p) := by
  let R : ℝ := Real.log C
  let g : Ω → ℝ := fun ω => max (|f ω| - R) 0
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have hR : 0 ≤ R := Real.log_nonneg hC
  have hg : AEMeasurable g P := by
    exact (by fun_prop : Continuous fun x : ℝ => max (|x| - R) 0).measurable.comp_aemeasurable hf
  have hg0 (ω : Ω) : 0 ≤ g ω := by dsimp [g]; positivity
  have hgtail : ∀ u : ℝ, 0 ≤ u →
      (P {ω | u < |g ω|}).toReal ≤ Real.exp (-u) := by
    intro u hu
    have hsubset : {ω | u < |g ω|} ⊆ {ω | u + R < |f ω|} := by
      intro ω hω
      have hω' : u < max (|f ω| - R) 0 := by
        simpa [g, abs_of_nonneg (hg0 ω)] using hω
      rcases (lt_max_iff).mp hω' with hleft | hright
      · change u + R < |f ω|
        linarith
      · exact False.elim ((not_lt_of_ge hu) hright)
    calc
      (P {ω | u < |g ω|}).toReal ≤ (P {ω | u + R < |f ω|}).toReal :=
        measureReal_mono hsubset
      _ ≤ C * Real.exp (-(u + R)) := htail (u + R) (by linarith)
      _ = Real.exp (-u) := by
        rw [show -(u + R) = -u - R by ring, Real.exp_sub, Real.exp_log hCpos]
        field_simp [hCpos.ne']
  have hgmoment := integrable_rpow_of_exp_tail hg (by norm_num : 0 ≤ (1 : ℝ)) hp
    (by simpa using hgtail)
  have hpoint (ω : Ω) : |f ω| ≤ R + g ω := by
    by_cases hω : |f ω| ≤ R
    · simp [g, hω]
    · have hnonneg : 0 ≤ |f ω| - R := by linarith
      rw [show g ω = |f ω| - R by simp [g, max_eq_left hnonneg]]
      linarith
  have hpowpoint (ω : Ω) : |f ω| ^ p ≤ 2 ^ p * (R ^ p + |g ω| ^ p) := by
    have hsum : R + g ω ≤ 2 * max R (g ω) := by
      have hRmax : R ≤ max R (g ω) := le_max_left _ _
      have hgmax : g ω ≤ max R (g ω) := le_max_right _ _
      linarith
    have hmain := Real.rpow_le_rpow (abs_nonneg (f ω)) (hpoint ω) hp.le
    have hscale := Real.rpow_le_rpow (by positivity : 0 ≤ R + g ω) hsum hp.le
    have hmaxpow : max R (g ω) ^ p ≤ R ^ p + |g ω| ^ p := by
      by_cases h : R ≤ g ω
      · rw [max_eq_right h, abs_of_nonneg (hg0 ω)]
        exact le_add_of_nonneg_left (Real.rpow_nonneg hR _)
      · rw [max_eq_left (le_of_not_ge h), abs_of_nonneg (hg0 ω)]
        exact le_add_of_nonneg_right (Real.rpow_nonneg (hg0 ω) _)
    calc
      |f ω| ^ p ≤ (R + g ω) ^ p := hmain
      _ ≤ (2 * max R (g ω)) ^ p := hscale
      _ = 2 ^ p * max R (g ω) ^ p := by
        have hmaxnonneg : 0 ≤ max R (g ω) := by positivity
        rw [Real.mul_rpow (by norm_num) hmaxnonneg]
      _ ≤ 2 ^ p * (R ^ p + |g ω| ^ p) :=
        mul_le_mul_of_nonneg_left hmaxpow (Real.rpow_nonneg (by norm_num) _)
  have hmajor : Integrable (fun ω => 2 ^ p * (R ^ p + |g ω| ^ p)) P := by
    have hsum : Integrable (fun ω => R ^ p + |g ω| ^ p) P :=
      (integrable_const _).add hgmoment.1
    exact hsum.const_mul (2 ^ p)
  have hfpower : AEStronglyMeasurable (fun ω => |f ω| ^ p) P := by
    exact ((Real.continuous_rpow_const hp.le).comp continuous_abs).comp_aestronglyMeasurable
      hf.aestronglyMeasurable
  have hfpowerInt : Integrable (fun ω => |f ω| ^ p) P := by
    apply hmajor.mono' hfpower
    filter_upwards [] with ω
    have hleft : 0 ≤ |f ω| ^ p := Real.rpow_nonneg (abs_nonneg _) _
    have hright : 0 ≤ 2 ^ p * (R ^ p + |g ω| ^ p) := by positivity
    simpa [Real.norm_eq_abs, abs_of_nonneg hleft, abs_of_nonneg hright] using hpowpoint ω
  refine ⟨hfpowerInt, ?_⟩
  calc
    ∫ ω, |f ω| ^ p ∂P ≤ ∫ ω, 2 ^ p * (R ^ p + |g ω| ^ p) ∂P :=
      integral_mono hfpowerInt hmajor hpowpoint
    _ = 2 ^ p * (R ^ p + ∫ ω, |g ω| ^ p ∂P) := by
      rw [integral_const_mul, integral_add (integrable_const _) hgmoment.1, integral_const]
      simp
    _ ≤ 2 ^ p * (R ^ p + p * Real.Gamma p) := by
      have hcoef : 0 ≤ (2 : ℝ) ^ p := Real.rpow_nonneg (by norm_num) p
      have hgmoment' : ∫ ω, |g ω| ^ p ∂P ≤ p * Real.Gamma p := by
        simpa using hgmoment.2
      exact mul_le_mul_of_nonneg_left
        (add_le_add (le_refl (R ^ p)) hgmoment') hcoef

end Critical2DKPZ.JointConvergence

end
