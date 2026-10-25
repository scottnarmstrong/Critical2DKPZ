/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Smoothing.Basic
public import Critical2DKPZ.Polymer.ChapmanKolmogorov
public import Critical2DKPZ.PolymerCalculus.PathConvexity
public import Critical2DKPZ.Definitions.LogMGFRatio
public import Critical2DKPZ.Definitions.GaussianityDefect
import Critical2DKPZ.Gaussian.DisorderLaws
import Critical2DKPZ.OnePoint.FinitePathGaussian
import Critical2DKPZ.OnePoint.FiniteProfileGaussian
import Critical2DKPZ.PolymerCalculus.PathAssociation
import Critical2DKPZ.PolymerCalculus.ScalarBounds
import Mathlib.Tactic

/-! # Weighted Chapman–Kolmogorov formulas for smoothed profiles -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Critical2DKPZ.Smoothing

/-- Weighted Chapman–Kolmogorov at time `n` for a point start. -/
theorem profileP2Fun_point_eq_mul (β : ℝ) {n M : ℕ} (hnM : n ≤ M) (z : Site)
    (f : Site → ℝ) (ω : Disorder) :
    profileP2Fun β 0 M (fun w => if w = z then 1 else 0) f ω =
      pointToPlane β 0 n z ω * profileP2Fun β n M (endpointDist β n z ω) f ω := by
  classical
  let E := Polymer.endpoints z n
  have hleft : profileP2Fun β 0 M (fun w => if w = z then 1 else 0) f ω =
      ∑' w, pointToPoint β 0 M z w ω * f w := by
    rw [profileP2Fun]
    simp only [ite_mul, one_mul, zero_mul, tsum_ite_eq, Nat.sub_zero]
  have hsplit : n + (M - n) = M := Nat.add_sub_of_le hnM
  have hCK : profileP2Fun β 0 M (fun w => if w = z then 1 else 0) f ω =
      ∑ y ∈ E, pointToPoint β 0 n z y ω *
        (∑' w, pointToPoint β n (M - n) y w ω * f w) := by
    rw [hleft]
    calc
      (∑' w, pointToPoint β 0 M z w ω * f w) =
          ∑' w, pointToPoint β 0 (n + (M - n)) z w ω * f w := by rw [hsplit]
      _ = ∑' y, pointToPoint β 0 n z y ω *
          (∑' w, pointToPoint β (0 + n) (M - n) y w ω * f w) :=
            Polymer.terminalProfile_chapmanKolmogorov β 0 n (M - n) z f ω
      _ = ∑' y, pointToPoint β 0 n z y ω *
          (∑' w, pointToPoint β n (M - n) y w ω * f w) := by
            simp only [Nat.zero_add]
      _ = ∑ y ∈ E, pointToPoint β 0 n z y ω *
          (∑' w, pointToPoint β n (M - n) y w ω * f w) := by
            rw [Polymer.tsum_pointToPoint_mul_eq_sum]
  have hsupport : ∀ w ∉ E, endpointDist β n z ω w = 0 := by
    intro w hw
    exact Polymer.endpointDist_eq_zero_of_not_mem β n z w ω hw
  have htail := Polymer.profileP2Fun_eq_sum β n M (endpointDist β n z ω) f E hsupport ω
  have hfactor :
      (∑ y ∈ E, pointToPoint β 0 n z y ω *
        (∑' w, pointToPoint β n (M - n) y w ω * f w)) =
      pointToPlane β 0 n z ω * profileP2Fun β n M (endpointDist β n z ω) f ω := by
    rw [htail]
    symm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    unfold endpointDist
    field_simp [ne_of_gt (Polymer.pointToPlane_pos β 0 n z ω)]
  exact hCK.trans hfactor

/-- Weighted Chapman–Kolmogorov at time `n` for a smoothed start. -/
theorem profileP2Fun_srwKernel_eq_mul (β : ℝ) {m n M : ℕ} (hmn : m ≤ n) (hnM : n ≤ M)
    (z : Site) (f : Site → ℝ) (ω : Disorder) :
    profileP2Fun β m M (fun w => srwKernel m (w - z)) f ω =
      smoothedP2Plane β m n z ω *
        profileP2Fun β n M (smoothedEndpointDist β m n z ω) f ω := by
  classical
  let A := Polymer.endpoints z m
  let B := A.biUnion (fun y => Polymer.endpoints y (n - m))
  let q : Site → ℝ := fun y => srwKernel m (y - z)
  let U : Site → ℝ := fun w => ∑' y, q y * pointToPoint β m (n - m) y w ω
  have hqA : ∀ y ∉ A, q y = 0 := by
    intro y hy
    exact Polymer.srwKernel_eq_zero_of_not_mem m z y hy
  have hUA (w : Site) : U w =
      ∑ y ∈ A, q y * pointToPoint β m (n - m) y w ω := by
    dsimp [U]
    apply tsum_eq_sum
    intro y hy
    rw [hqA y hy, zero_mul]
  have hBsubset (y : Site) (hy : y ∈ A) :
      Polymer.endpoints y (n - m) ⊆ B := by
    intro w hw
    exact Finset.mem_biUnion.mpr ⟨y, hy, hw⟩
  have hUzero (w : Site) (hw : w ∉ B) : U w = 0 := by
    rw [hUA]
    apply Finset.sum_eq_zero
    intro y hy
    have hwy : w ∉ Polymer.endpoints y (n - m) := by
      intro hreach
      exact hw (Finset.mem_biUnion.mpr ⟨y, hy, hreach⟩)
    rw [Polymer.pointToPoint_eq_zero_of_not_mem β m (n - m) y w ω hwy, mul_zero]
  have hUdist (w : Site) : smoothedEndpointDist β m n z ω w =
      U w / smoothedP2Plane β m n z ω := by
    unfold smoothedEndpointDist
    rw [show (∑' y, srwKernel m (y - z) * pointToPoint β m (n - m) y w ω) = U w by
      rfl]
  have hdistB : ∀ w ∉ B, smoothedEndpointDist β m n z ω w = 0 := by
    intro w hw
    rw [hUdist, hUzero w hw, zero_div]
  have hleft : profileP2Fun β m M q f ω =
      ∑ y ∈ A, q y * (∑' w, pointToPoint β m (M - m) y w ω * f w) := by
    exact Polymer.profileP2Fun_eq_sum β m M q f A hqA ω
  have hsplit : n - m + (M - n) = M - m := by omega
  have hmiddle (y : Site) :
      (∑' w, pointToPoint β m (M - m) y w ω * f w) =
        ∑ u ∈ Polymer.endpoints y (n - m),
          pointToPoint β m (n - m) y u ω *
            (∑' w, pointToPoint β n (M - n) u w ω * f w) := by
    rw [← hsplit, Polymer.terminalProfile_chapmanKolmogorov]
    simp only [show m + (n - m) = n by omega]
    rw [Polymer.tsum_pointToPoint_mul_eq_sum]
  have hleftB : profileP2Fun β m M q f ω =
      ∑ u ∈ B, U u * (∑' w, pointToPoint β n (M - n) u w ω * f w) := by
    rw [hleft]
    have hsub (y : Site) (hy : y ∈ A) : Polymer.endpoints y (n - m) ⊆ B :=
      hBsubset y hy
    simp_rw [hmiddle]
    calc
      (∑ y ∈ A, q y *
          ∑ u ∈ Polymer.endpoints y (n - m),
            pointToPoint β m (n - m) y u ω *
              (∑' w, pointToPoint β n (M - n) u w ω * f w)) =
        ∑ y ∈ A, q y *
          ∑ u ∈ B,
            pointToPoint β m (n - m) y u ω *
              (∑' w, pointToPoint β n (M - n) u w ω * f w) := by
                apply Finset.sum_congr rfl
                intro y hy
                rw [Finset.sum_subset (hsub y hy)]
                intro u huB huNot
                rw [Polymer.pointToPoint_eq_zero_of_not_mem β m (n - m) y u ω huNot, zero_mul]
      _ = ∑ u ∈ B, ∑ y ∈ A,
            q y * pointToPoint β m (n - m) y u ω *
              (∑' w, pointToPoint β n (M - n) u w ω * f w) := by
                simp_rw [Finset.mul_sum]
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro u hu
                rw [Finset.sum_congr rfl]
                intro y hy
                ring
      _ = ∑ u ∈ B, U u * (∑' w, pointToPoint β n (M - n) u w ω * f w) := by
                apply Finset.sum_congr rfl
                intro u hu
                rw [hUA]
                rw [Finset.sum_mul]
  have hfactor : smoothedP2Plane β m n z ω *
      profileP2Fun β n M (smoothedEndpointDist β m n z ω) f ω =
        ∑ u ∈ B, U u * (∑' w, pointToPoint β n (M - n) u w ω * f w) := by
    have htail := Polymer.profileP2Fun_eq_sum β n M
      (smoothedEndpointDist β m n z ω) f B hdistB ω
    rw [htail]
    symm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    rw [hUdist]
    field_simp [ne_of_gt (Polymer.smoothedP2Plane_pos β m n z ω)]
  exact hleftB.trans hfactor.symm

/-- The normalized log-MGF ratio remains convex for a sum of two finite polymer log masses.
The two path families are embedded into the union of their finite disorder-coordinate sets. -/
theorem logMGFRatio_add_finitePathMass_convex
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (β γ : ℝ) (a n b m : ℕ) (w : ι → Site) (v : κ → Site)
    {c : ι × (Fin n → Fin 4) → ℝ} {d : κ × (Fin m → Fin 4) → ℝ}
    (hc : ∀ p, 0 ≤ c p) (hpc : ∃ p, 0 < c p)
    (hd : ∀ p, 0 ≤ d p) (hpd : ∃ p, 0 < d p) :
    let F := fun ω => Real.log (PolymerCalculus.finitePathMass β a n w c ω)
    let G := fun ω => Real.log (PolymerCalculus.finitePathMass γ b m v d ω)
    integrableExpSet (F + G) disorderLaw = univ ∧
      ConvexOn ℝ (integrableExpSet (F + G) disorderLaw)
        (logMGFRatio disorderLaw (F + G)) := by
  classical
  dsimp only
  let S := PolymerCalculus.finitePathCoordinates a n w ∪
    PolymerCalculus.finitePathCoordinates b m v
  let e : Fin S.card → ℕ × Site := fun i => (S.equivFin.symm i).val
  let π : Disorder → EuclideanSpace ℝ (Fin S.card) :=
    PolymerCalculus.disorderSliceCoordinates e
  let L : EuclideanSpace ℝ (Fin S.card) →ₗ[ℝ] Disorder := {
    toFun := fun x p => if hp : p ∈ S then x (S.equivFin ⟨p, hp⟩) else 0
    map_add' := by
      intro x y
      funext p
      by_cases hp : p ∈ S <;> simp [hp, Pi.add_apply]
    map_smul' := by
      intro r x
      funext p
      by_cases hp : p ∈ S <;> simp [hp, smul_eq_mul]
  }
  let F : Disorder → ℝ := fun ω =>
    Real.log (PolymerCalculus.finitePathMass β a n w c ω)
  let G : Disorder → ℝ := fun ω =>
    Real.log (PolymerCalculus.finitePathMass γ b m v d ω)
  let Fv : EuclideanSpace ℝ (Fin S.card) → ℝ := fun x => F (L x)
  let Gv : EuclideanSpace ℝ (Fin S.card) → ℝ := fun x => G (L x)
  let H : EuclideanSpace ℝ (Fin S.card) → ℝ := fun x => Fv x + Gv x
  have he : Function.Injective e := by
    intro i j hij
    have hsub : S.equivFin.symm i = S.equivFin.symm j := Subtype.ext hij
    exact S.equivFin.symm.injective hsub
  have hπlaw : HasLaw π (stdGaussian (EuclideanSpace ℝ (Fin S.card))) disorderLaw := by
    change HasLaw (PolymerCalculus.disorderSliceCoordinates e)
      (stdGaussian (EuclideanSpace ℝ (Fin S.card))) disorderLaw
    exact PolymerCalculus.hasLaw_disorderSliceCoordinates e he
  have hπmeas : Measurable π := by
    change Measurable (fun ω : Disorder => WithLp.toLp 2 (fun i => ω (e i)))
    have hraw : Measurable (fun ω : Disorder => fun i => ω (e i)) :=
      measurable_pi_iff.mpr (fun i => Gaussian.measurable_disorder_eval (e i))
    have hto : Measurable (fun x : (Fin S.card → ℝ) => WithLp.toLp 2 x) := by fun_prop
    exact hto.comp hraw
  have hcoordEq (ω : Disorder) (p : ℕ × Site) (hp : p ∈ S) : L (π ω) p = ω p := by
    change (if h : p ∈ S then π ω (S.equivFin ⟨p, h⟩) else 0) = ω p
    simp [π, PolymerCalculus.disorderSliceCoordinates, e, hp]
  have hmassEqF (ω : Disorder) :
      PolymerCalculus.finitePathMass β a n w c (L (π ω)) =
        PolymerCalculus.finitePathMass β a n w c ω := by
    apply PolymerCalculus.dependsOn_finitePathMass β a n w c
    intro p hp
    exact hcoordEq ω p (Finset.mem_union_left _ hp)
  have hmassEqG (ω : Disorder) :
      PolymerCalculus.finitePathMass γ b m v d (L (π ω)) =
        PolymerCalculus.finitePathMass γ b m v d ω := by
    apply PolymerCalculus.dependsOn_finitePathMass γ b m v d
    intro p hp
    exact hcoordEq ω p (Finset.mem_union_right _ hp)
  have hFcomp : F = fun ω => Fv (π ω) := by
    funext ω
    dsimp [Fv, F]
    exact congrArg Real.log (hmassEqF ω).symm
  have hGcomp : G = fun ω => Gv (π ω) := by
    funext ω
    dsimp [Gv, G]
    exact congrArg Real.log (hmassEqG ω).symm
  have hsumComp : F + G = fun ω => H (π ω) := by
    funext ω
    change F ω + G ω = Fv (π ω) + Gv (π ω)
    rw [← congrFun hFcomp ω, ← congrFun hGcomp ω]
  have hconvF : ConvexOn ℝ univ F := by
    simpa only [F] using
      PolymerCalculus.convexOn_log_finitePathMass β a n w hc hpc
  have hconvG : ConvexOn ℝ univ G := by
    simpa only [G] using
      PolymerCalculus.convexOn_log_finitePathMass γ b m v hd hpd
  have hconvFG : ConvexOn ℝ univ (F + G) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ u t hu ht hut
    change F (u • x + t • y) + G (u • x + t • y) ≤
      u * (F x + G x) + t * (F y + G y)
    calc
      _ ≤ (u • F x + t • F y) + (u • G x + t • G y) := by
        exact add_le_add
          (hconvF.2 (mem_univ x) (mem_univ y) hu ht hut)
          (hconvG.2 (mem_univ x) (mem_univ y) hu ht hut)
      _ = _ := by ring
  have hLmeas : Measurable L := by
    apply measurable_pi_iff.mpr
    intro p
    dsimp [L]
    split_ifs <;> fun_prop
  have hFmeas : Measurable F := by
    simpa only [F] using PolymerCalculus.measurable_log_finitePathMass β a n w c
  have hGmeas : Measurable G := by
    simpa only [G] using PolymerCalculus.measurable_log_finitePathMass γ b m v d
  have hFvmeas : Measurable Fv := hFmeas.comp hLmeas
  have hGvmeas : Measurable Gv := hGmeas.comp hLmeas
  have hHmeas : Measurable H := hFvmeas.add hGvmeas
  have hconvH : ConvexOn ℝ univ H := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ u t hu ht hut
    change F (L (u • x + t • y)) + G (L (u • x + t • y)) ≤
      u * (F (L x) + G (L x)) + t * (F (L y) + G (L y))
    have hlin : L (u • x + t • y) = u • L x + t • L y := by simp
    rw [hlin]
    exact hconvFG.2 (mem_univ _) (mem_univ _) hu ht hut
  have hFmom (q : ℝ) :
      Integrable (fun ω => Real.exp (q * F ω)) disorderLaw := by
    simpa only [F] using
      PolymerCalculus.integrable_exp_mul_log_finitePathMass β a n w hc hpc q
  have hGmom (q : ℝ) :
      Integrable (fun ω => Real.exp (q * G ω)) disorderLaw := by
    simpa only [G] using
      PolymerCalculus.integrable_exp_mul_log_finitePathMass γ b m v hd hpd q
  have hFmomVec (q : ℝ) : Integrable
      (fun x => Real.exp (q * Fv x))
      (stdGaussian (EuclideanSpace ℝ (Fin S.card))) := by
    have hcomp : Integrable (fun ω => Real.exp (q * Fv (π ω))) disorderLaw := by
      simpa only [hFcomp, Function.comp_apply] using hFmom q
    have hmeas : Measurable (fun x => Real.exp (q * Fv x)) := (hFvmeas.const_mul q).exp
    rw [← hπlaw.map_eq]
    exact (integrable_map_measure hmeas.aestronglyMeasurable hπlaw.aemeasurable).2 hcomp
  have hGmomVec (q : ℝ) : Integrable
      (fun x => Real.exp (q * Gv x))
      (stdGaussian (EuclideanSpace ℝ (Fin S.card))) := by
    have hcomp : Integrable (fun ω => Real.exp (q * Gv (π ω))) disorderLaw := by
      simpa only [hGcomp, Function.comp_apply] using hGmom q
    have hmeas : Measurable (fun x => Real.exp (q * Gv x)) := (hGvmeas.const_mul q).exp
    rw [← hπlaw.map_eq]
    exact (integrable_map_measure hmeas.aestronglyMeasurable hπlaw.aemeasurable).2 hcomp
  have hHmom (q : ℝ) : Integrable (fun x => Real.exp (q * H x))
      (stdGaussian (EuclideanSpace ℝ (Fin S.card))) := by
    have hmajor := (hFmomVec (2 * q)).add (hGmomVec (2 * q)) |>.const_mul (1 / 2 : ℝ)
    apply hmajor.mono'
    · exact (hHmeas.const_mul q |>.exp).aestronglyMeasurable
    · filter_upwards with x
      change |Real.exp (q * (Fv x + Gv x))| ≤ _
      rw [abs_of_pos (Real.exp_pos _)]
      change Real.exp (q * (Fv x + Gv x)) ≤
        (1 / 2 : ℝ) * (Real.exp (2 * q * Fv x) + Real.exp (2 * q * Gv x))
      have hmul : Real.exp (q * (Fv x + Gv x)) =
          Real.exp (q * Fv x) * Real.exp (q * Gv x) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hsqF : Real.exp (2 * q * Fv x) = Real.exp (q * Fv x) ^ 2 := by
        rw [show 2 * q * Fv x = q * Fv x + q * Fv x by ring, Real.exp_add]
        ring
      have hsqG : Real.exp (2 * q * Gv x) = Real.exp (q * Gv x) ^ 2 := by
        rw [show 2 * q * Gv x = q * Gv x + q * Gv x by ring, Real.exp_add]
        ring
      rw [hmul, hsqF, hsqG]
      nlinarith [sq_nonneg (Real.exp (q * Fv x) - Real.exp (q * Gv x))]
  have hC1 := Critical2DKPZ.Provider.gaussian_convexity
    (stdGaussian (EuclideanSpace ℝ (Fin S.card))) H hconvH
    (fun q hq => hHmom q)
  have hsumMeas : Measurable (F + G) := hFmeas.add hGmeas
  have hmeasure : disorderLaw.map (F + G) =
      (stdGaussian (EuclideanSpace ℝ (Fin S.card))).map H := by
    rw [hsumComp]
    calc
      disorderLaw.map (fun ω => H (π ω)) = disorderLaw.map (H ∘ π) := rfl
      _ = (disorderLaw.map π).map H := (Measure.map_map hHmeas hπmeas).symm
      _ = _ := by rw [hπlaw.map_eq]
  have hratio (q : ℝ) :
      logMGFRatio disorderLaw (F + G) q =
        logMGFRatio (stdGaussian (EuclideanSpace ℝ (Fin S.card))) H q := by
    calc
      logMGFRatio disorderLaw (F + G) q =
          logMGFRatio (disorderLaw.map (F + G)) id q :=
            (GaussianConvexity.logMGFRatio_map disorderLaw (F + G) hsumMeas q).symm
      _ = logMGFRatio
          ((stdGaussian (EuclideanSpace ℝ (Fin S.card))).map H) id q := by rw [hmeasure]
      _ = logMGFRatio (stdGaussian (EuclideanSpace ℝ (Fin S.card))) H q :=
            GaussianConvexity.logMGFRatio_map _ H hHmeas q
  have hfun : logMGFRatio disorderLaw (F + G) =
      logMGFRatio (stdGaussian (EuclideanSpace ℝ (Fin S.card))) H := funext hratio
  have hdom : integrableExpSet (F + G) disorderLaw = univ := by
    ext q
    simp only [mem_univ, iff_true, integrableExpSet]
    have hmajor := (hFmom (2 * q)).add (hGmom (2 * q)) |>.const_mul (1 / 2 : ℝ)
    apply hmajor.mono'
    · exact (hsumMeas.const_mul q |>.exp).aestronglyMeasurable
    · filter_upwards with ω
      change |Real.exp (q * (F ω + G ω))| ≤ _
      rw [abs_of_pos (Real.exp_pos _)]
      change Real.exp (q * (F ω + G ω)) ≤
        (1 / 2 : ℝ) * (Real.exp (2 * q * F ω) + Real.exp (2 * q * G ω))
      have hmul : Real.exp (q * (F ω + G ω)) =
          Real.exp (q * F ω) * Real.exp (q * G ω) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hsqF : Real.exp (2 * q * F ω) = Real.exp (q * F ω) ^ 2 := by
        rw [show 2 * q * F ω = q * F ω + q * F ω by ring, Real.exp_add]
        ring
      have hsqG : Real.exp (2 * q * G ω) = Real.exp (q * G ω) ^ 2 := by
        rw [show 2 * q * G ω = q * G ω + q * G ω by ring, Real.exp_add]
        ring
      rw [hmul, hsqF, hsqG]
      nlinarith [sq_nonneg (Real.exp (q * F ω) - Real.exp (q * G ω))]
  refine ⟨hdom, ?_⟩
  rw [hdom, hfun]
  exact hC1

/-- The two-point polymer log covariance satisfies the Gaussian defect bound of equation (3.12). -/
theorem covariance_log_smoothedP2Plane_le {β : ℝ} (hβ : 0 ≤ β) (s n : ℕ) (x y : Site) :
    0 ≤ cov[fun ω => Real.log (smoothedP2Plane β s n x ω),
      fun ω => Real.log (smoothedP2Plane β s n y ω); disorderLaw] ∧
      cov[fun ω => Real.log (smoothedP2Plane β s n x ω),
        fun ω => Real.log (smoothedP2Plane β s n y ω); disorderLaw] ≤
        Real.log (∫ ω, smoothedP2Plane β s n x ω * smoothedP2Plane β s n y ω
          ∂disorderLaw) +
          gaussianityDefect disorderLaw (fun ω => Real.log (smoothedP2Plane β s n x ω)) +
          gaussianityDefect disorderLaw (fun ω => Real.log (smoothedP2Plane β s n y ω)) := by
  classical
  let Ax := Polymer.endpoints x s
  let Ay := Polymer.endpoints y s
  let Ix := {u : Site // u ∈ Ax}
  let Iy := {v : Site // v ∈ Ay}
  let wx : Ix → Site := fun u => u.1
  let wy : Iy → Site := fun v => v.1
  let cx : Ix × (Fin (n - s) → Fin 4) → ℝ := fun p =>
    srwKernel s (p.1.1 - x) * ((4 : ℝ)⁻¹ ^ (n - s))
  let cy : Iy × (Fin (n - s) → Fin 4) → ℝ := fun p =>
    srwKernel s (p.1.1 - y) * ((4 : ℝ)⁻¹ ^ (n - s))
  have hνxA : ∀ u ∉ Ax, srwKernel s (u - x) = 0 := by
    intro u hu
    exact Polymer.srwKernel_eq_zero_of_not_mem s x u hu
  have hνyA : ∀ v ∉ Ay, srwKernel s (v - y) = 0 := by
    intro v hv
    exact Polymer.srwKernel_eq_zero_of_not_mem s y v hv
  have hcx : ∀ p, 0 ≤ cx p := by
    intro p
    exact mul_nonneg (Polymer.kernel_nonneg s (p.1.1 - x)) (by positivity)
  have hcy : ∀ p, 0 ≤ cy p := by
    intro p
    exact mul_nonneg (Polymer.kernel_nonneg s (p.1.1 - y)) (by positivity)
  have hqposx : ∃ u ∈ Ax, 0 < srwKernel s (u - x) := by
    have hsum : 0 < ∑ u ∈ Ax, srwKernel s (u - x) := by
      rw [Polymer.sum_srwKernel_endpoints]
      norm_num
    exact (Finset.sum_pos_iff_of_nonneg
      (fun u _ => Polymer.kernel_nonneg s (u - x))).mp hsum
  have hqposy : ∃ v ∈ Ay, 0 < srwKernel s (v - y) := by
    have hsum : 0 < ∑ v ∈ Ay, srwKernel s (v - y) := by
      rw [Polymer.sum_srwKernel_endpoints]
      norm_num
    exact (Finset.sum_pos_iff_of_nonneg
      (fun v _ => Polymer.kernel_nonneg s (v - y))).mp hsum
  have hpcx : ∃ p, 0 < cx p := by
    obtain ⟨u, hu, hqu⟩ := hqposx
    refine ⟨(⟨u, hu⟩, fun _ => 0), ?_⟩
    dsimp [cx]
    positivity
  have hpcy : ∃ p, 0 < cy p := by
    obtain ⟨v, hv, hqv⟩ := hqposy
    refine ⟨(⟨v, hv⟩, fun _ => 0), ?_⟩
    dsimp [cy]
    positivity
  have hrepX (ω : Disorder) : smoothedP2Plane β s n x ω =
      PolymerCalculus.finitePathMass β s (n - s) wx cx ω := by
    calc
      smoothedP2Plane β s n x ω =
          profileP2Fun β s n (fun u => srwKernel s (u - x)) (fun _ => 1) ω :=
            (Polymer.profileP2Fun_srw_flat β s n x ω).symm
      _ = PolymerCalculus.finitePathMass β s (n - s) wx cx ω := by
            simpa only [Ix, wx, cx] using
              OnePoint.profileP2Fun_eq_finitePathMass β s n
                (fun u => srwKernel s (u - x)) Ax hνxA ω
  have hrepY (ω : Disorder) : smoothedP2Plane β s n y ω =
      PolymerCalculus.finitePathMass β s (n - s) wy cy ω := by
    calc
      smoothedP2Plane β s n y ω =
          profileP2Fun β s n (fun v => srwKernel s (v - y)) (fun _ => 1) ω :=
            (Polymer.profileP2Fun_srw_flat β s n y ω).symm
      _ = PolymerCalculus.finitePathMass β s (n - s) wy cy ω := by
            simpa only [Iy, wy, cy] using
              OnePoint.profileP2Fun_eq_finitePathMass β s n
                (fun v => srwKernel s (v - y)) Ay hνyA ω
  let Fx : Disorder → ℝ := fun ω => Real.log (smoothedP2Plane β s n x ω)
  let Gy : Disorder → ℝ := fun ω => Real.log (smoothedP2Plane β s n y ω)
  have hlogX : (fun ω => Real.log
      (PolymerCalculus.finitePathMass β s (n - s) wx cx ω)) = Fx := by
    funext ω
    dsimp [Fx]
    rw [← hrepX ω]
  have hlogY : (fun ω => Real.log
      (PolymerCalculus.finitePathMass β s (n - s) wy cy ω)) = Gy := by
    funext ω
    dsimp [Gy]
    rw [← hrepY ω]
  have hmemXmass := PolymerCalculus.memLp_log_finitePathMass β s (n - s) wx hcx hpcx 2
  have hmemYmass := PolymerCalculus.memLp_log_finitePathMass β s (n - s) wy hcy hpcy 2
  have hmemX : MemLp Fx 2 disorderLaw := by
    simpa only [hlogX, ENNReal.coe_ofNat] using hmemXmass
  have hmemY : MemLp Gy 2 disorderLaw := by
    simpa only [hlogY, ENNReal.coe_ofNat] using hmemYmass
  have hsumEq : Fx + Gy =
      (fun ω => Real.log (PolymerCalculus.finitePathMass β s (n - s) wx cx ω)) +
        (fun ω => Real.log (PolymerCalculus.finitePathMass β s (n - s) wy cy ω)) := by
    funext ω
    simp only [Pi.add_apply, Fx, Gy]
    rw [hrepX ω, hrepY ω]
  have hjoint := logMGFRatio_add_finitePathMass_convex β β s (n - s) s (n - s)
    wx wy hcx hpcx hcy hpcy
  have hdom : integrableExpSet (Fx + Gy) disorderLaw = univ := by
    simpa only [← hsumEq] using hjoint.1
  have hconv : ConvexOn ℝ (integrableExpSet (Fx + Gy) disorderLaw)
      (logMGFRatio disorderLaw (Fx + Gy)) := by
    simpa only [← hsumEq] using hjoint.2
  have h0 : 0 ∈ interior (integrableExpSet (Fx + Gy) disorderLaw) := by
    rw [hdom]
    simp
  have h1 : 1 ∈ integrableExpSet (Fx + Gy) disorderLaw := by
    rw [hdom]
    simp
  have hupper := PolymerCalculus.covariance_le_log_joint_moment_add_defects_of_convex
    hmemX hmemY hconv h0 h1
  have hmgf : mgf (Fx + Gy) disorderLaw 1 =
      ∫ ω, smoothedP2Plane β s n x ω * smoothedP2Plane β s n y ω ∂disorderLaw := by
    rw [mgf]
    congr 1
    funext ω
    simp only [Pi.add_apply, Fx, Gy, one_mul, Real.exp_add,
      Real.exp_log (Polymer.smoothedP2Plane_pos β s n x ω),
      Real.exp_log (Polymer.smoothedP2Plane_pos β s n y ω)]
  have hlow := PolymerCalculus.covariance_log_finitePathMass_nonneg hβ hβ
    s (n - s) s (n - s) wx wy hcx hpcx hcy hpcy
  constructor
  · simpa only [hlogX, hlogY] using hlow
  · rw [hmgf] at hupper
    exact hupper

end Critical2DKPZ.Smoothing

end
