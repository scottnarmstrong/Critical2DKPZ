/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Smoothing.CenteredWidthLogL2
public import Critical2DKPZ.Smoothing.Measurability
public import Critical2DKPZ.Smoothing.ParityHelpers
public import Critical2DKPZ.Smoothing.EvenExtension
public import Critical2DKPZ.Smoothing.SpatialL2
public import Critical2DKPZ.Analysis.Lattice.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Tactic

/-! # Integrating pointwise bounds for smoothing-width changes -/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal BoundedContinuousFunction

namespace Critical2DKPZ.Smoothing

private theorem integrable_mul_latticePoint_of_compactSupport (N : ℕ) (hN : 0 < N)
    {φ : Plane → ℝ} (hφ : Measurable φ) (hφc : HasCompactSupport φ)
    (hφint : Integrable φ) (g : Site → ℝ) :
    Integrable (fun x => φ x * g (latticePoint N x)) := by
  classical
  obtain ⟨R₀, hR₀⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : Plane)).mp hφc.isBounded
  let R := max R₀ 0
  have hR : 0 ≤ R := le_max_right _ _
  have htsupp (x : Plane) (hx : φ x ≠ 0) : ‖x‖ ≤ R := by
    have h := hR₀ (subset_tsupport φ hx)
    rw [Metric.mem_closedBall, dist_zero_right] at h
    exact h.trans (le_max_left _ _)
  have hscale : 0 < Real.sqrt (N / 2) := Real.sqrt_pos.mpr (by positivity)
  let L := 1 + Real.sqrt (N / 2) * R
  have hL : 0 ≤ L := by positivity
  let K : ℤ := (Nat.ceil L : ℕ)
  have hLK : L ≤ (K : ℝ) := by
    dsimp [K]
    exact_mod_cast (Nat.le_ceil L)
  let I : Set ℤ := Set.Icc (-K) K
  have hIfinite : I.Finite := Set.finite_Icc _ _
  let S : Set Site := {z | ∀ i : Fin 2, z i ∈ I}
  have hSfinite : S.Finite := by
    simpa only [S, Site] using (Set.Finite.pi' (fun _ : Fin 2 => hIfinite))
  have hsiteImage (x : Plane) (hx : φ x ≠ 0) : latticePoint N x ∈ S := by
    intro i
    change latticePoint N x i ∈ Set.Icc (-K) K
    rw [Set.mem_Icc]
    have hxR := htsupp x hx
    have hround : ‖(Real.sqrt (N / 2)) • x - siteToPlane (latticePoint N x)‖ ≤ 1 := by
      simpa only [latticePoint] using norm_sub_nearestEven_le_one
        ((Real.sqrt (N / 2)) • x)
    have hsite : ‖siteToPlane (latticePoint N x)‖ ≤ L := by
      calc
        ‖siteToPlane (latticePoint N x)‖ ≤
            ‖siteToPlane (latticePoint N x) - (Real.sqrt (N / 2)) • x‖ +
              ‖(Real.sqrt (N / 2)) • x‖ := norm_le_norm_sub_add _ _
        _ = ‖(Real.sqrt (N / 2)) • x - siteToPlane (latticePoint N x)‖ +
              ‖(Real.sqrt (N / 2)) • x‖ := by rw [norm_sub_rev]
        _ ≤ 1 + Real.sqrt (N / 2) * R := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_pos hscale]
              exact add_le_add hround (mul_le_mul_of_nonneg_left hxR (Real.sqrt_nonneg _))
    have hi := (PiLp.norm_apply_le (siteToPlane (latticePoint N x)) i).trans hsite
    have hi' : |((latticePoint N x) i : ℝ)| ≤ (K : ℝ) := by
      simpa only [siteToPlane, Real.norm_eq_abs] using hi.trans hLK
    have hbounds := abs_le.mp hi'
    constructor
    · exact_mod_cast hbounds.1
    · exact_mod_cast hbounds.2
  let C₀ : ℝ := ∑ z ∈ hSfinite.toFinset, |g z|
  let C := max C₀ 0
  have hg (z : Site) (hz : z ∈ S) : |g z| ≤ C := by
    dsimp [C, C₀]
    exact (Finset.single_le_sum (fun y hy => abs_nonneg (g y))
      (hSfinite.mem_toFinset.mpr hz)).trans (le_max_left _ _)
  have hmeas : Measurable (fun x => φ x * g (latticePoint N x)) := by
    apply hφ.mul
    exact (measurable_of_countable g).comp (measurable_latticePoint N)
  apply (hφint.norm.const_mul C).mono' hmeas.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
  by_cases hx : φ x = 0
  · simp [hx]
  · calc
      |φ x| * |g (latticePoint N x)| ≤ |φ x| * C :=
        mul_le_mul_of_nonneg_left (hg _ (hsiteImage x hx)) (abs_nonneg (φ x))
      _ = C * |φ x| := by ring

/-- If each sitewise centered logarithmic width change has an `L²` bound, then its integral
against a compactly supported test has the corresponding spatial `L¹` factor. The integrability
conjunct records that the resulting `L²` bound is meaningful. -/
theorem latticeSmoothingError_sameStart_width_le_of (β : ℝ) (M k j d : ℕ)
    (hM : Even M) (hk : Even k) (hj : Even j) (hd : Even d)
    (hMpos : 0 < M) (hkM : k ≤ M)
    (h₀ : Plane →ᵇ ℝ) (φ : Plane → ℝ) (hφ : Measurable φ)
    (hφc : HasCompactSupport φ) (hφint : Integrable φ) (R : ℝ) (hR : 0 ≤ R)
    (hwidth : ∀ z : Site,
      eLpNorm (fun ω =>
        (Real.log (profileP2Fun β k M (fun w => srwKernel j (w - z))
            (evenExtension (cellAverage M fun y => Real.exp (h₀ y))) ω) -
          ∫ ω', Real.log (profileP2Fun β k M (fun w => srwKernel j (w - z))
              (fun _ => 1) ω') ∂disorderLaw) -
        (Real.log (profileP2Fun β k M (fun w => srwKernel d (w - z))
            (evenExtension (cellAverage M fun y => Real.exp (h₀ y))) ω) -
          ∫ ω', Real.log (profileP2Fun β k M (fun w => srwKernel d (w - z))
              (fun _ => 1) ω') ∂disorderLaw))
        2 disorderLaw ≤ ENNReal.ofReal R) :
    Integrable (fun ω => latticeSmoothingError β M M k j h₀ φ ω -
      latticeSmoothingError β M M k d h₀ φ ω) disorderLaw ∧
    eLpNorm (fun ω => latticeSmoothingError β M M k j h₀ φ ω -
      latticeSmoothingError β M M k d h₀ φ ω) 2 disorderLaw ≤
        ENNReal.ofReal (R * ∫ x, |φ x|) := by
  classical
  let f : Site → ℝ := cellAverage M (fun y => Real.exp (h₀ y))
  let F : Site → ℝ := evenExtension f
  let νj : Disorder × Plane → Site → ℝ := fun p w =>
    srwKernel j (w - latticePoint M p.2)
  let νd : Disorder × Plane → Site → ℝ := fun p w =>
    srwKernel d (w - latticePoint M p.2)
  let Cj : Disorder × Plane → ℝ := fun p =>
    Real.log (profileP2Fun β k M (νj p) F p.1) -
      ∫ ω', Real.log (profileP2Fun β k M (νj p) (fun _ => 1) ω') ∂disorderLaw
  let Cd : Disorder × Plane → ℝ := fun p =>
    Real.log (profileP2Fun β k M (νd p) F p.1) -
      ∫ ω', Real.log (profileP2Fun β k M (νd p) (fun _ => 1) ω') ∂disorderLaw
  let Z : Disorder → Plane → ℝ := fun ω x => Cj (ω, x) - Cd (ω, x)
  have hνj (w : Site) : Measurable (fun p : Disorder × Plane => νj p w) := by
    exact (measurable_of_countable (fun z : Site => srwKernel j (w - z))).comp
      ((measurable_latticePoint M).comp measurable_snd)
  have hνd (w : Site) : Measurable (fun p : Disorder × Plane => νd p w) := by
    exact (measurable_of_countable (fun z : Site => srwKernel d (w - z))).comp
      ((measurable_latticePoint M).comp measurable_snd)
  have hCj : Measurable Cj := by
    dsimp [Cj]
    exact measurable_centered_profile_log_param β k M F hνj measurable_fst
  have hCd : Measurable Cd := by
    dsimp [Cd]
    exact measurable_centered_profile_log_param β k M F hνd measurable_fst
  have hZ : Measurable (fun p : Disorder × Plane => Z p.1 p.2) := by
    dsimp [Z]
    exact (hCj.sub hCd).comp (measurable_fst.prodMk measurable_snd)
  have hZbound (x : Plane) :
      eLpNorm (fun ω => Z ω x) 2 disorderLaw ≤ ENNReal.ofReal R := by
    simpa [Z, Cj, Cd, νj, νd, F] using hwidth (latticePoint M x)
  have hZmem (x : Plane) : MemLp (fun ω => Z ω x) 2 disorderLaw := by
    apply (memLp_iff).2
    exact lt_of_le_of_lt (hZbound x) (by simp)
  have hZsq (x : Plane) : Integrable (fun ω => Z ω x ^ 2) disorderLaw ∧
      (∫ ω, Z ω x ^ 2 ∂disorderLaw) ≤ R ^ 2 :=
    integral_sq_le_of_eLpNorm_le disorderLaw (hZmem x) R hR (hZbound x)
  have hspatial := eLpNorm_integral_mul_le_of_uniform_secondMoment disorderLaw
    φ hφ hφint hZ hZmem (R ^ 2) (sq_nonneg R) hZsq
  have hcoarse (ω : Disorder) : Integrable (fun x => φ x *
      (Real.log (profileP2Fun β 0 M (fun w =>
          if w = latticePoint M x then 1 else 0) f ω) -
        ∫ ω', Real.log (profileP2Fun β 0 M (fun w =>
          if w = latticePoint M x then 1 else 0) (fun _ => 1) ω') ∂disorderLaw)) := by
    exact integrable_mul_latticePoint_of_compactSupport M hMpos hφ hφc hφint
      (fun z => Real.log (profileP2Fun β 0 M (fun w => if w = z then 1 else 0) f ω) -
        ∫ ω', Real.log (profileP2Fun β 0 M (fun w => if w = z then 1 else 0)
          (fun _ => 1) ω') ∂disorderLaw)
  have hsmooth (r : ℕ) (ω : Disorder) : Integrable (fun x => φ x *
      (Real.log (profileP2Fun β k M (fun w => srwKernel r (w - latticePoint M x)) f ω) -
        ∫ ω', Real.log (profileP2Fun β k M (fun w => srwKernel r (w - latticePoint M x))
          (fun _ => 1) ω') ∂disorderLaw)) := by
    exact integrable_mul_latticePoint_of_compactSupport M hMpos hφ hφc hφint
      (fun z => Real.log (profileP2Fun β k M (fun w => srwKernel r (w - z)) f ω) -
        ∫ ω', Real.log (profileP2Fun β k M (fun w => srwKernel r (w - z))
          (fun _ => 1) ω') ∂disorderLaw)
  have herror (r : ℕ) (ω : Disorder) : latticeSmoothingError β M M k r h₀ φ ω =
      (∫ x, φ x *
        (Real.log (profileP2Fun β 0 M (fun w =>
            if w = latticePoint M x then 1 else 0) f ω) -
          ∫ ω', Real.log (profileP2Fun β 0 M (fun w =>
            if w = latticePoint M x then 1 else 0) (fun _ => 1) ω') ∂disorderLaw)) -
      ∫ x, φ x *
        (Real.log (profileP2Fun β k M (fun w => srwKernel r (w - latticePoint M x)) f ω) -
          ∫ ω', Real.log (profileP2Fun β k M (fun w => srwKernel r (w - latticePoint M x))
            (fun _ => 1) ω') ∂disorderLaw) := by
    unfold latticeSmoothingError
    rw [← integral_sub (hcoarse ω) (hsmooth r ω)]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  have hsiteEven (x : Plane) : Even ((latticePoint M x) 0 + (latticePoint M x) 1) := by
    exact latticePoint_mem_evenLattice M x
  have hkmEven : Even (M - k) := (Nat.even_sub hkM).2 ⟨fun _ => hk, fun _ => hM⟩
  have hνjEven (x : Plane) (w : Site)
      (hw : srwKernel j (w - latticePoint M x) ≠ 0) : Even (w 0 + w 1) := by
    have hreach : w ∈ Critical2DKPZ.Polymer.endpoints (latticePoint M x) j := by
      by_contra hnot
      exact hw (Critical2DKPZ.Polymer.srwKernel_eq_zero_of_not_mem j
        (latticePoint M x) w hnot)
    exact reachable_even_of_even (hsiteEven x) hj hreach
  have hνdEven (x : Plane) (w : Site)
      (hw : srwKernel d (w - latticePoint M x) ≠ 0) : Even (w 0 + w 1) := by
    have hreach : w ∈ Critical2DKPZ.Polymer.endpoints (latticePoint M x) d := by
      by_contra hnot
      exact hw (Critical2DKPZ.Polymer.srwKernel_eq_zero_of_not_mem d
        (latticePoint M x) w hnot)
    exact reachable_even_of_even (hsiteEven x) hd hreach
  have hfEven (w : Site) (hw : Even (w 0 + w 1)) : f w = F w := by
    simp [F, evenExtension, hw]
  have hprofilej (x : Plane) (ω : Disorder) :
      profileP2Fun β k M (fun w => srwKernel j (w - latticePoint M x)) f ω =
        profileP2Fun β k M (fun w => srwKernel j (w - latticePoint M x)) F ω := by
    apply profileP2Fun_congr_of_even β (by omega) hkmEven
    · exact hνjEven x
    · exact hfEven
  have hprofiled (x : Plane) (ω : Disorder) :
      profileP2Fun β k M (fun w => srwKernel d (w - latticePoint M x)) f ω =
        profileP2Fun β k M (fun w => srwKernel d (w - latticePoint M x)) F ω := by
    apply profileP2Fun_congr_of_even β (by omega) hkmEven
    · exact hνdEven x
    · exact hfEven
  have hwidthAt (x : Plane) (ω : Disorder) :
      (Real.log (profileP2Fun β k M (fun w => srwKernel j (w - latticePoint M x)) f ω) -
        ∫ ω', Real.log (profileP2Fun β k M (fun w => srwKernel j
            (w - latticePoint M x)) (fun _ => 1) ω') ∂disorderLaw) -
      (Real.log (profileP2Fun β k M (fun w => srwKernel d (w - latticePoint M x)) f ω) -
        ∫ ω', Real.log (profileP2Fun β k M (fun w => srwKernel d
            (w - latticePoint M x)) (fun _ => 1) ω') ∂disorderLaw) = Z ω x := by
    rw [hprofilej, hprofiled]
  have hdiff (ω : Disorder) :
      latticeSmoothingError β M M k j h₀ φ ω - latticeSmoothingError β M M k d h₀ φ ω =
        -∫ x, φ x * Z ω x := by
    rw [herror j ω, herror d ω]
    have hcancel :
        ((∫ x, φ x *
          (Real.log (profileP2Fun β 0 M (fun w =>
              if w = latticePoint M x then 1 else 0) f ω) -
            ∫ ω', Real.log (profileP2Fun β 0 M (fun w =>
              if w = latticePoint M x then 1 else 0) (fun _ => 1) ω')
              ∂disorderLaw)) -
          ∫ x, φ x *
            (Real.log (profileP2Fun β k M (fun w => srwKernel j
                (w - latticePoint M x)) f ω) -
              ∫ ω', Real.log (profileP2Fun β k M (fun w => srwKernel j
                (w - latticePoint M x)) (fun _ => 1) ω') ∂disorderLaw)) -
         ((∫ x, φ x *
          (Real.log (profileP2Fun β 0 M (fun w =>
              if w = latticePoint M x then 1 else 0) f ω) -
            ∫ ω', Real.log (profileP2Fun β 0 M (fun w =>
              if w = latticePoint M x then 1 else 0) (fun _ => 1) ω')
              ∂disorderLaw)) -
          ∫ x, φ x *
            (Real.log (profileP2Fun β k M (fun w => srwKernel d
                (w - latticePoint M x)) f ω) -
              ∫ ω', Real.log (profileP2Fun β k M (fun w => srwKernel d
                (w - latticePoint M x)) (fun _ => 1) ω') ∂disorderLaw)) =
        -((∫ x, φ x *
            (Real.log (profileP2Fun β k M (fun w => srwKernel j
                (w - latticePoint M x)) f ω) -
              ∫ ω', Real.log (profileP2Fun β k M (fun w => srwKernel j
                (w - latticePoint M x)) (fun _ => 1) ω') ∂disorderLaw)) -
          ∫ x, φ x *
            (Real.log (profileP2Fun β k M (fun w => srwKernel d
                (w - latticePoint M x)) f ω) -
              ∫ ω', Real.log (profileP2Fun β k M (fun w => srwKernel d
                (w - latticePoint M x)) (fun _ => 1) ω') ∂disorderLaw)) := by ring
    rw [hcancel, ← integral_sub (hsmooth j ω) (hsmooth d ω)]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with x
    calc
      _ = φ x *
          ((Real.log (profileP2Fun β k M (fun w =>
              srwKernel j (w - latticePoint M x)) f ω) -
            ∫ ω', Real.log (profileP2Fun β k M (fun w =>
              srwKernel j (w - latticePoint M x)) (fun _ => 1) ω') ∂disorderLaw) -
           (Real.log (profileP2Fun β k M (fun w =>
              srwKernel d (w - latticePoint M x)) f ω) -
            ∫ ω', Real.log (profileP2Fun β k M (fun w =>
              srwKernel d (w - latticePoint M x)) (fun _ => 1) ω') ∂disorderLaw)) := by ring
      _ = φ x * Z ω x := by rw [hwidthAt]
  refine ⟨?_, ?_⟩
  · have hInt := hspatial.1
    have hfun : (fun ω => latticeSmoothingError β M M k j h₀ φ ω -
        latticeSmoothingError β M M k d h₀ φ ω) =
        fun ω => -∫ x, φ x * Z ω x := funext hdiff
    rw [hfun]
    exact hInt.neg
  · have hnorm := hspatial.2
    have hfun : (fun ω => latticeSmoothingError β M M k j h₀ φ ω -
        latticeSmoothingError β M M k d h₀ φ ω) =
        fun ω => -∫ x, φ x * Z ω x := funext hdiff
    rw [hfun]
    calc
      _ = eLpNorm (fun ω => ∫ x, φ x * Z ω x) 2 disorderLaw := by
        have hneg : (fun ω => -∫ x, φ x * Z ω x) =
            -(fun ω => ∫ x, φ x * Z ω x) := by
          funext ω
          rfl
        rw [hneg, eLpNorm_neg]
      _ ≤ ENNReal.ofReal (Real.sqrt (R ^ 2) * ∫ x, |φ x|) := hnorm
      _ = ENNReal.ofReal (R * ∫ x, |φ x|) := by
        congr 1
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hR]


end Critical2DKPZ.Smoothing

end
