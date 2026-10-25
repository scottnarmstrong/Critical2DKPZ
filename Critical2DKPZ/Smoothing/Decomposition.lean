/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Smoothing.Basic
public import Critical2DKPZ.Smoothing.ChapmanKolmogorov
public import Critical2DKPZ.Smoothing.ParityHelpers
public import Critical2DKPZ.Smoothing.EvenExtension
public import Critical2DKPZ.Smoothing.EndpointDistribution
public import Critical2DKPZ.OnePoint.FiniteProfileGaussian
import Mathlib.Tactic

/-! # The exact split of the unit-horizon smoothing error -/

@[expose] public section

open MeasureTheory
open scoped BigOperators
open scoped BoundedContinuousFunction

namespace Critical2DKPZ.Smoothing

private theorem profileP2Fun_eq_finitePathMass_terminal
    (β : ℝ) (a b : ℕ) (ν f : Site → ℝ)
    (A : Finset Site) (hνA : ∀ w ∉ A, ν w = 0) (ω : Disorder) :
    profileP2Fun β a b ν f ω =
      PolymerCalculus.finitePathMass β a (b - a)
        (fun w : {y // y ∈ A} => w.1)
        (fun p : {y // y ∈ A} × (Fin (b - a) → Fin 4) =>
          (ν p.1.1 * ((4 : ℝ)⁻¹ ^ (b - a)) *
            f (walkPosition p.1.1 p.2 (b - a)))) ω := by
  classical
  let Starts := {y // y ∈ A}
  let w : Starts → Site := fun y => y.1
  let c : Starts × (Fin (b - a) → Fin 4) → ℝ := fun p =>
    ν p.1.1 * ((4 : ℝ)⁻¹ ^ (b - a)) * f (walkPosition p.1.1 p.2 (b - a))
  have hprofile : profileP2Fun β a b ν f ω =
      ∑ y ∈ A, ν y * ∑ s : Fin (b - a) → Fin 4,
        (4 : ℝ)⁻¹ ^ (b - a) * Polymer.pathWeight β a y s ω *
          f (walkPosition y s (b - a)) := by
    rw [Polymer.profileP2Fun_eq_sum β a b ν f A hνA]
    apply Finset.sum_congr rfl
    intro y hy
    rw [Polymer.tsum_pointToPoint_mul]
  have hstart : (Finset.univ : Finset Starts) = A.attach := by
    ext y
    simp [Starts]
  change profileP2Fun β a b ν f ω =
      ∑ p : Starts × (Fin (b - a) → Fin 4),
        c p * Real.exp (PolymerCalculus.pathEnergy β a (w p.1) p.2 ω)
  rw [hprofile]
  calc
    (∑ y ∈ A, ν y * ∑ s : Fin (b - a) → Fin 4,
        (4 : ℝ)⁻¹ ^ (b - a) * Polymer.pathWeight β a y s ω *
          f (walkPosition y s (b - a))) =
      ∑ y ∈ A.attach, ν y.1 * ∑ s : Fin (b - a) → Fin 4,
        (4 : ℝ)⁻¹ ^ (b - a) * Polymer.pathWeight β a y.1 s ω *
          f (walkPosition y.1 s (b - a)) := by
            exact (Finset.sum_attach A (fun y => ν y *
              ∑ s : Fin (b - a) → Fin 4,
                (4 : ℝ)⁻¹ ^ (b - a) * Polymer.pathWeight β a y s ω *
                  f (walkPosition y s (b - a)))).symm
    _ = ∑ y : Starts, ν y.1 * ∑ s : Fin (b - a) → Fin 4,
          (4 : ℝ)⁻¹ ^ (b - a) * Polymer.pathWeight β a y.1 s ω *
          f (walkPosition y.1 s (b - a)) := by
            rw [← hstart]
    _ = ∑ y : Starts, ∑ s : Fin (b - a) → Fin 4,
        c (y, s) * Real.exp (PolymerCalculus.pathEnergy β a (w y) s ω) := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s hs
          dsimp [c, w, Starts, PolymerCalculus.pathEnergy, Polymer.pathWeight]
          ring
    _ = ∑ p : Starts × (Fin (b - a) → Fin 4),
        c p * Real.exp (PolymerCalculus.pathEnergy β a (w p.1) p.2 ω) := by
          rw [← Finset.univ_product_univ, Finset.sum_product]

private theorem integrable_log_profileP2Fun_terminal
    (β : ℝ) (a b : ℕ) (ν f : Site → ℝ) (A : Finset Site)
    (hνA : ∀ w ∉ A, ν w = 0) (hν0 : ∀ w, 0 ≤ ν w)
    (hνpos : ∃ w ∈ A, 0 < ν w) (hf : ∀ z, 0 < f z) :
    Integrable (fun ω => Real.log (profileP2Fun β a b ν f ω)) disorderLaw := by
  classical
  let Starts := {y // y ∈ A}
  let w : Starts → Site := fun y => y.1
  let c : Starts × (Fin (b - a) → Fin 4) → ℝ := fun p =>
    ν p.1.1 * ((4 : ℝ)⁻¹ ^ (b - a)) * f (walkPosition p.1.1 p.2 (b - a))
  have hc : ∀ p, 0 ≤ c p := by
    intro p
    dsimp [c]
    exact mul_nonneg (mul_nonneg (hν0 _) (by positivity)) (hf _).le
  have hpos : ∃ p, 0 < c p := by
    obtain ⟨y, hyA, hy⟩ := hνpos
    refine ⟨(⟨y, hyA⟩, fun _ => 0), ?_⟩
    dsimp [c]
    exact mul_pos (mul_pos hy (by positivity)) (hf _)
  let Z := PolymerCalculus.finitePathMass β a (b - a) w c
  have hEq (ω : Disorder) : profileP2Fun β a b ν f ω = Z ω := by
    exact profileP2Fun_eq_finitePathMass_terminal β a b ν f A hνA ω
  have hZpos (ω : Disorder) : 0 < Z ω :=
    PolymerCalculus.finitePathMass_pos β a (b - a) w hc hpos ω
  have hmass : Integrable Z disorderLaw := by
    have h := PolymerCalculus.integrable_exp_mul_log_finitePathMass
      β a (b - a) w hc hpos 1
    have hEq' : (fun ω => Real.exp (1 * Real.log (Z ω))) = Z := by
      funext ω
      rw [one_mul, Real.exp_log (hZpos ω)]
    rw [hEq'] at h
    exact h
  have hinv : Integrable (fun ω => (Z ω)⁻¹) disorderLaw := by
    have h := PolymerCalculus.integrable_exp_mul_log_finitePathMass
      β a (b - a) w hc hpos (-1)
    have hEq' : (fun ω => Real.exp (-1 * Real.log (Z ω))) = fun ω => (Z ω)⁻¹ := by
      funext ω
      rw [neg_one_mul, ← Real.log_inv (Z ω), Real.exp_log (inv_pos.mpr (hZpos ω))]
    rw [hEq'] at h
    exact h
  have hlogMeas : AEStronglyMeasurable (fun ω => Real.log (Z ω)) disorderLaw :=
    (PolymerCalculus.measurable_log_finitePathMass β a (b - a) w c).aestronglyMeasurable
  have hlogBound (ω : Disorder) : |Real.log (Z ω)| ≤ Z ω + (Z ω)⁻¹ := by
    have hz := hZpos ω
    by_cases hlog : 0 ≤ Real.log (Z ω)
    · rw [abs_of_nonneg hlog]
      calc
        Real.log (Z ω) ≤ Z ω - 1 := Real.log_le_sub_one_of_pos hz
        _ ≤ Z ω + (Z ω)⁻¹ := by
          have hinvpos : 0 ≤ (Z ω)⁻¹ := inv_nonneg.mpr hz.le
          linarith
    · rw [abs_of_neg (lt_of_not_ge hlog)]
      have hlogInv : Real.log ((Z ω)⁻¹) = -Real.log (Z ω) := Real.log_inv (Z ω)
      rw [← hlogInv]
      calc
        Real.log ((Z ω)⁻¹) ≤ (Z ω)⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr hz)
        _ ≤ Z ω + (Z ω)⁻¹ := by
          have hzpos' : 0 ≤ Z ω := hz.le
          linarith
  have hlogInt : Integrable (fun ω => Real.log (Z ω)) disorderLaw := by
    apply (hmass.add hinv).mono' hlogMeas
    filter_upwards [] with ω
    rw [Real.norm_eq_abs]
    exact hlogBound ω
  have hEqLog : (fun ω => Real.log (profileP2Fun β a b ν f ω)) =
      fun ω => Real.log (Z ω) := by
    funext ω
    rw [hEq]
  rw [hEqLog]
  exact hlogInt

/-- A nonzero nonnegative finite initial profile and positive terminal test give a positive polymer pairing. -/
theorem profileP2Fun_pos_terminal
    (β : ℝ) (a b : ℕ) (ν f : Site → ℝ) (A : Finset Site)
    (hνA : ∀ w ∉ A, ν w = 0) (hν0 : ∀ w, 0 ≤ ν w)
    (hνpos : ∃ w ∈ A, 0 < ν w) (hf : ∀ z, 0 < f z) (ω : Disorder) :
    0 < profileP2Fun β a b ν f ω := by
  classical
  let Starts := {y // y ∈ A}
  let w : Starts → Site := fun y => y.1
  let c : Starts × (Fin (b - a) → Fin 4) → ℝ := fun p =>
    ν p.1.1 * ((4 : ℝ)⁻¹ ^ (b - a)) * f (walkPosition p.1.1 p.2 (b - a))
  have hc : ∀ p, 0 ≤ c p := by
    intro p
    dsimp [c]
    exact mul_nonneg (mul_nonneg (hν0 _) (by positivity)) (hf _).le
  have hpos : ∃ p, 0 < c p := by
    obtain ⟨y, hyA, hy⟩ := hνpos
    refine ⟨(⟨y, hyA⟩, fun _ => 0), ?_⟩
    dsimp [c]
    exact mul_pos (mul_pos hy (by positivity)) (hf _)
  rw [profileP2Fun_eq_finitePathMass_terminal β a b ν f A hνA]
  exact PolymerCalculus.finitePathMass_pos β a (b - a) w hc hpos ω

private theorem endpointDist_exists_positive (β : ℝ) (n : ℕ) (z : Site) (ω : Disorder) :
    ∃ w ∈ Polymer.endpoints z n, 0 < endpointDist β n z ω w := by
  let ν := endpointDist β n z ω
  let A := Polymer.endpoints z n
  have hA : ∀ w ∉ A, ν w = 0 := by
    intro w hw
    exact Polymer.endpointDist_eq_zero_of_not_mem β n z w ω (by simpa [A] using hw)
  have h0 : ∀ w, 0 ≤ ν w := fun w => Polymer.endpointDist_nonneg β n z w ω
  have hsum : ∑ w ∈ A, ν w = 1 := by
    calc
      ∑ w ∈ A, ν w = ∑' w, ν w := by
        symm
        exact tsum_eq_sum fun w hw => hA w (by simpa [A] using hw)
      _ = 1 := Polymer.tsum_endpointDist β n z ω
  have hs : 0 < ∑ w ∈ A, ν w := by rw [hsum]; norm_num
  exact (Finset.sum_pos_iff_of_nonneg (fun w hw => h0 w)).mp hs

private theorem smoothedEndpointDist_exists_positive (β : ℝ) {m n : ℕ}
    (hmn : m ≤ n) (z : Site) (ω : Disorder) :
    ∃ w ∈ (Polymer.endpoints z m).biUnion (fun y => Polymer.endpoints y (n - m)),
      0 < smoothedEndpointDist β m n z ω w := by
  let ν := smoothedEndpointDist β m n z ω
  let A := (Polymer.endpoints z m).biUnion (fun y => Polymer.endpoints y (n - m))
  have hA : ∀ w ∉ A, ν w = 0 := by
    intro w hw
    exact smoothedEndpointDist_eq_zero_of_not_mem β z w ω (by simpa [A] using hw)
  have h0 : ∀ w, 0 ≤ ν w := fun w => smoothedEndpointDist_nonneg β z w ω
  have hsum : ∑ w ∈ A, ν w = 1 := by
    calc
      ∑ w ∈ A, ν w = ∑' w, ν w := by
        symm
        exact tsum_eq_sum fun w hw => hA w (by simpa [A] using hw)
      _ = 1 := tsum_smoothedEndpointDist β hmn z ω
  have hs : 0 < ∑ w ∈ A, ν w := by rw [hsum]; norm_num
  exact (Finset.sum_pos_iff_of_nonneg (fun w hw => h0 w)).mp hs

private theorem integrable_log_pointToPlane (β : ℝ) (n : ℕ) (z : Site) :
    Integrable (fun ω => Real.log (pointToPlane β 0 n z ω)) disorderLaw := by
  let ν : Site → ℝ := fun w => if w = z then 1 else 0
  have hνA : ∀ w ∉ ({z} : Finset Site), ν w = 0 := by
    intro w hw
    have hwz : w ≠ z := by simpa using hw
    simp [ν, hwz]
  have hν0 : ∀ w, 0 ≤ ν w := by
    intro w
    by_cases hw : w = z <;> simp [ν, hw]
  have hνpos : ∃ w ∈ ({z} : Finset Site), 0 < ν w := by
    exact ⟨z, Finset.mem_singleton_self _, by simp [ν]⟩
  have hInt := integrable_log_profileP2Fun_terminal β 0 n ν (fun _ => 1)
    {z} hνA hν0 hνpos (fun _ => one_pos)
  have hEq : (fun ω => profileP2Fun β 0 n ν (fun _ => 1) ω) =
      fun ω => pointToPlane β 0 n z ω := by
    funext ω
    rw [Polymer.profileP2Fun_eq_sum β 0 n ν (fun _ => 1) {z} hνA ω]
    simp only [Finset.sum_singleton]
    rw [show ν z = 1 by simp [ν], one_mul, Nat.sub_zero]
    simpa only [mul_one] using Polymer.tsum_pointToPoint β 0 n z ω
  have hlogEq : (fun ω => Real.log (profileP2Fun β 0 n ν (fun _ => 1) ω)) =
      fun ω => Real.log (pointToPlane β 0 n z ω) := by
    funext ω
    exact congrArg Real.log (congrFun hEq ω)
  rw [← hlogEq]
  exact hInt

/-- The logarithm of a smoothed point-to-plane mass is integrable. -/
theorem integrable_log_smoothedP2Plane (β : ℝ) {m n : ℕ} (z : Site) :
    Integrable (fun ω => Real.log (smoothedP2Plane β m n z ω)) disorderLaw := by
  let ν : Site → ℝ := fun w => srwKernel m (w - z)
  let A := Polymer.endpoints z m
  have hνA : ∀ w ∉ A, ν w = 0 := by
    intro w hw
    exact Polymer.srwKernel_eq_zero_of_not_mem m z w (by simpa [A] using hw)
  have hν0 : ∀ w, 0 ≤ ν w := fun w => Polymer.kernel_nonneg m (w - z)
  have hνsum : ∑ w ∈ A, ν w = 1 := by
    exact Polymer.sum_srwKernel_endpoints m z
  have hνpos : ∃ w ∈ A, 0 < ν w := by
    have hs : 0 < ∑ w ∈ A, ν w := by rw [hνsum]; norm_num
    exact (Finset.sum_pos_iff_of_nonneg (fun w hw => hν0 w)).mp hs
  have hInt := integrable_log_profileP2Fun_terminal β m n ν (fun _ => 1)
    A hνA hν0 hνpos (fun _ => one_pos)
  have hEq : (fun ω => profileP2Fun β m n ν (fun _ => 1) ω) =
      fun ω => smoothedP2Plane β m n z ω := by
    funext ω
    exact Polymer.profileP2Fun_srw_flat β m n z ω
  have hlogEq : (fun ω => Real.log (profileP2Fun β m n ν (fun _ => 1) ω)) =
      fun ω => Real.log (smoothedP2Plane β m n z ω) := by
    funext ω
    exact congrArg Real.log (congrFun hEq ω)
  rw [← hlogEq]
  exact hInt

/-- Multiplying any lattice function by a bounded compactly supported measurable test is integrable. -/
theorem integrable_mul_siteFunction_latticePoint (N : ℕ) (hN : 0 < N)
    {φ : Plane → ℝ} (hφ : Measurable φ) (hφc : HasCompactSupport φ)
    (hb : ∃ B : ℝ, ∀ x, |φ x| ≤ B) (g : Site → ℝ) :
    Integrable (fun x => φ x * g (latticePoint N x)) := by
  classical
  obtain ⟨B, hB⟩ := hb
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
  have hφInt : Integrable φ volume := hφOn.integrable_of_forall_notMem_eq_zero hφzero
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
    have hround : ‖(Real.sqrt (N / 2)) • x -
        siteToPlane (latticePoint N x)‖ ≤ 1 := by
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
  have hC : 0 ≤ C := le_max_right _ _
  have hg (z : Site) (hz : z ∈ S) : |g z| ≤ C := by
    dsimp [C, C₀]
    exact (Finset.single_le_sum (fun y hy => abs_nonneg (g y))
      (hSfinite.mem_toFinset.mpr hz)).trans (le_max_left _ _)
  have hmeas : Measurable (fun x => φ x * g (latticePoint N x)) := by
    apply hφ.mul
    exact (measurable_of_countable g).comp (measurable_latticePoint N)
  apply (hφInt.norm.const_mul C).mono' hmeas.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
  by_cases hx : φ x = 0
  · simp [hx]
  · calc
      |φ x| * |g (latticePoint N x)| ≤ |φ x| * C :=
        mul_le_mul_of_nonneg_left (hg _ (hsiteImage x hx)) (abs_nonneg (φ x))
      _ = C * |φ x| := by ring

/-- At a unit time horizon, the smoothing error splits into local and centered global terms as in equation (5.12). -/
theorem latticeSmoothingError_eq_local_add_global (β : ℝ) {M m n : ℕ}
    (hm : Even m) (hn : Even n) (hM : Even M) (hmn : m ≤ n) (hnM : n ≤ M)
    (h₀ : Plane →ᵇ ℝ) (φ : Plane → ℝ) (hφ : Measurable φ)
    (hφc : HasCompactSupport φ) (hφb : ∃ B : ℝ, ∀ x, |φ x| ≤ B) (ω : Disorder) :
    latticeSmoothingError β M M m m h₀ φ ω =
      localLogError β M m n φ ω +
        ∫ x, φ x * (globalLogError β m n M
            (evenExtension (cellAverage M fun y => Real.exp (h₀ y)))
            (latticePoint M x) ω -
          ∫ ω', globalLogError β m n M (fun _ => 1) (latticePoint M x) ω' ∂disorderLaw) := by
  classical
  by_cases hMzero : M = 0
  · subst M
    have hmzero : m = 0 := by omega
    have hnzero : n = 0 := by omega
    subst m
    subst n
    have hkernel (z w : Site) :
        srwKernel 0 (w - z) = (if w = z then (1 : ℝ) else 0) := by
      simp [srwKernel_zero, sub_eq_zero, eq_comm]
    have hsmoothed (z : Site) (ω' : Disorder) :
        smoothedP2Plane β 0 0 z ω' = 1 := by
      have hend : Polymer.endpoints z 0 = {z} := by
        simp [Polymer.endpoints, Critical2DKPZ.walkPosition]
      rw [Polymer.smoothedP2Plane_eq_sum]
      rw [hend]
      simp [srwKernel_zero, sub_eq_zero]
    have hdist (z : Site) (ω' : Disorder) :
        endpointDist β 0 z ω' = smoothedEndpointDist β 0 0 z ω' := by
      funext w
      simp [endpointDist, smoothedEndpointDist, hsmoothed, srwKernel_zero,
        sub_eq_zero, eq_comm]
    simp [latticeSmoothingError, localLogError, globalLogError, hkernel, hdist,
      hsmoothed]
  · have hMpos : 0 < M := Nat.pos_of_ne_zero hMzero
    have hMone : 1 ≤ M := Nat.succ_le_iff.mpr hMpos
    let f : Site → ℝ := evenExtension (cellAverage M fun y => Real.exp (h₀ y))
    have hf : ∀ w, 0 < f w := by
      intro w
      by_cases hw : Even (w 0 + w 1)
      · simpa [f, evenExtension, hw] using (cellAverage_exp_bounds_of_even M hMone h₀ hw).1
      · simp [f, evenExtension, hw]
    have hdelta (z : Site) :
        ∀ w ∉ ({z} : Finset Site), (if w = z then (1 : ℝ) else 0) = 0 := by
      intro w hw
      have hwz : w ≠ z := by simpa using hw
      simp [hwz]
    have hkernelPos (z : Site) :
        ∃ y ∈ Polymer.endpoints z m, 0 < srwKernel m (y - z) := by
      have hsum : ∑ y ∈ Polymer.endpoints z m, srwKernel m (y - z) = 1 :=
        Polymer.sum_srwKernel_endpoints m z
      have hs : 0 < ∑ y ∈ Polymer.endpoints z m, srwKernel m (y - z) := by
        rw [hsum]
        norm_num
      exact (Finset.sum_pos_iff_of_nonneg (fun y hy => Polymer.kernel_nonneg m (y - z))).mp hs
    have hsplit (x : Plane) :
        (Real.log (profileP2Fun β 0 M
            (fun w => if w = latticePoint M x then 1 else 0)
            (cellAverage M fun y => Real.exp (h₀ y)) ω) -
          ∫ ω', Real.log (profileP2Fun β 0 M
            (fun w => if w = latticePoint M x then 1 else 0) (fun _ => 1) ω') ∂disorderLaw) -
        (Real.log (profileP2Fun β m M
            (fun w => srwKernel m (w - latticePoint M x))
            (cellAverage M fun y => Real.exp (h₀ y)) ω) -
          ∫ ω', Real.log (profileP2Fun β m M
            (fun w => srwKernel m (w - latticePoint M x)) (fun _ => 1) ω') ∂disorderLaw) =
        ((Real.log (pointToPlane β 0 n (latticePoint M x) ω) -
            Real.log (smoothedP2Plane β m n (latticePoint M x) ω)) -
          ∫ ω', (Real.log (pointToPlane β 0 n (latticePoint M x) ω') -
            Real.log (smoothedP2Plane β m n (latticePoint M x) ω')) ∂disorderLaw) +
        (globalLogError β m n M f (latticePoint M x) ω -
          ∫ ω', globalLogError β m n M (fun _ => 1) (latticePoint M x) ω' ∂disorderLaw) := by
      let z := latticePoint M x
      let δz : Site → ℝ := fun w => if w = z then 1 else 0
      let κz : Site → ℝ := fun w => srwKernel m (w - z)
      let μ : Site → ℝ := endpointDist β n z ω
      let η : Site → ℝ := smoothedEndpointDist β m n z ω
      let Aδ : Finset Site := {z}
      let Aκ : Finset Site := Polymer.endpoints z m
      let Aμ : Finset Site := Polymer.endpoints z n
      let Aη : Finset Site := (Polymer.endpoints z m).biUnion
        (fun y => Polymer.endpoints y (n - m))
      have hδA : ∀ w ∉ Aδ, δz w = 0 := by
        intro w hw
        exact hdelta z w (by simpa [Aδ, δz] using hw)
      have hδ0 : ∀ w, 0 ≤ δz w := by
        intro w
        by_cases hw : w = z <;> simp [δz, hw]
      have hδpos : ∃ w ∈ Aδ, 0 < δz w := by
        exact ⟨z, by simp [Aδ], by simp [δz]⟩
      have hκA : ∀ w ∉ Aκ, κz w = 0 := by
        intro w hw
        exact Polymer.srwKernel_eq_zero_of_not_mem m z w (by simpa [Aκ, κz] using hw)
      have hκ0 : ∀ w, 0 ≤ κz w := by
        intro w
        exact Polymer.kernel_nonneg m (w - z)
      obtain ⟨wκ, hwκ, hκpos⟩ := hkernelPos z
      have hκpos' : ∃ w ∈ Aκ, 0 < κz w := by
        exact ⟨wκ, by simpa [Aκ] using hwκ, by simpa [κz] using hκpos⟩
      have hμA : ∀ w ∉ Aμ, μ w = 0 := by
        intro w hw
        exact Polymer.endpointDist_eq_zero_of_not_mem β n z w ω
          (by simpa [Aμ] using hw)
      have hμ0 : ∀ w, 0 ≤ μ w := by
        intro w
        exact Polymer.endpointDist_nonneg β n z w ω
      obtain ⟨wμ, hwμ, hμpos⟩ := endpointDist_exists_positive β n z ω
      have hμpos' : ∃ w ∈ Aμ, 0 < μ w := by
        exact ⟨wμ, by simpa [Aμ] using hwμ, by simpa [μ] using hμpos⟩
      have hηA : ∀ w ∉ Aη, η w = 0 := by
        intro w hw
        exact smoothedEndpointDist_eq_zero_of_not_mem β z w ω
          (by simpa [Aη] using hw)
      have hη0 : ∀ w, 0 ≤ η w := by
        intro w
        exact smoothedEndpointDist_nonneg β z w ω
      obtain ⟨wη, hwη, hηpos⟩ :=
        smoothedEndpointDist_exists_positive β hmn z ω
      have hηpos' : ∃ w ∈ Aη, 0 < η w := by
        exact ⟨wη, by simpa [Aη] using hwη, by simpa [η] using hηpos⟩
      have hzEven : Even (z 0 + z 1) := by
        have hzmem : z ∈ Critical2DKPZ.evenLattice :=
          Critical2DKPZ.latticePoint_mem_evenLattice M x
        simpa only [Critical2DKPZ.evenLattice, Set.mem_ofPred_eq] using hzmem
      have hMsubn : Even (M - n) := by
        exact (Nat.even_sub hnM).2 ⟨fun _ => hn, fun _ => hM⟩
      have hμEven : ∀ w, μ w ≠ 0 → Even (w 0 + w 1) := by
        intro w hw
        by_contra hnot
        exact hw (endpointDist_eq_zero_of_odd β hn hzEven ω hnot)
      have hηEven : ∀ w, η w ≠ 0 → Even (w 0 + w 1) := by
        intro w hw
        by_contra hnot
        exact hw (smoothedEndpointDist_eq_zero_of_odd β hm hn hmn hzEven ω hnot)
      have hμCell : ∀ ω' : Disorder,
          profileP2Fun β n M μ (cellAverage M fun y => Real.exp (h₀ y)) ω' =
            profileP2Fun β n M μ f ω' := by
        intro ω'
        apply profileP2Fun_congr_of_even β hnM hMsubn μ
          (cellAverage M fun y => Real.exp (h₀ y)) f hμEven
        intro w hw
        simp [f, evenExtension, hw]
      have hηCell : ∀ ω' : Disorder,
          profileP2Fun β n M η (cellAverage M fun y => Real.exp (h₀ y)) ω' =
            profileP2Fun β n M η f ω' := by
        intro ω'
        apply profileP2Fun_congr_of_even β hnM hMsubn η
          (cellAverage M fun y => Real.exp (h₀ y)) f hηEven
        intro w hw
        simp [f, evenExtension, hw]
      have hμInt : Integrable (fun ω' => Real.log (profileP2Fun β n M μ f ω')) disorderLaw :=
        integrable_log_profileP2Fun_terminal β n M μ f Aμ hμA hμ0 hμpos' hf
      have hμ1Int : Integrable (fun ω' =>
          Real.log (profileP2Fun β n M μ (fun _ => 1) ω')) disorderLaw :=
        integrable_log_profileP2Fun_terminal β n M μ (fun _ => 1) Aμ hμA hμ0 hμpos'
          (fun _ => one_pos)
      have hηInt : Integrable (fun ω' => Real.log (profileP2Fun β n M η f ω')) disorderLaw :=
        integrable_log_profileP2Fun_terminal β n M η f Aη hηA hη0 hηpos' hf
      have hη1Int : Integrable (fun ω' =>
          Real.log (profileP2Fun β n M η (fun _ => 1) ω')) disorderLaw :=
        integrable_log_profileP2Fun_terminal β n M η (fun _ => 1) Aη hηA hη0 hηpos'
          (fun _ => one_pos)
      have hpInt := integrable_log_pointToPlane β n z
      have hqInt := integrable_log_smoothedP2Plane β (m := m) (n := n) z
      have hδ1Int : Integrable (fun ω' =>
          Real.log (profileP2Fun β 0 M δz (fun _ => 1) ω')) disorderLaw :=
        integrable_log_profileP2Fun_terminal β 0 M δz (fun _ => 1) Aδ hδA hδ0 hδpos
          (fun _ => one_pos)
      have hκ1Int : Integrable (fun ω' =>
          Real.log (profileP2Fun β m M κz (fun _ => 1) ω')) disorderLaw :=
        integrable_log_profileP2Fun_terminal β m M κz (fun _ => 1) Aκ hκA hκ0 hκpos'
          (fun _ => one_pos)
      have hpFactor :
          Real.log (profileP2Fun β 0 M δz (cellAverage M fun y => Real.exp (h₀ y)) ω) =
            Real.log (pointToPlane β 0 n z ω) +
              Real.log (profileP2Fun β n M μ f ω) := by
        rw [profileP2Fun_point_eq_mul β hnM z
          (cellAverage M fun y => Real.exp (h₀ y)) ω]
        have hμCell' := hμCell ω
        dsimp [μ] at hμCell'
        rw [hμCell']
        rw [Real.log_mul (Polymer.pointToPlane_pos β 0 n z ω).ne'
          (profileP2Fun_pos_terminal β n M μ f Aμ hμA hμ0 hμpos' hf ω).ne']
      have hqFactor :
          Real.log (profileP2Fun β m M κz (cellAverage M fun y => Real.exp (h₀ y)) ω) =
            Real.log (smoothedP2Plane β m n z ω) +
              Real.log (profileP2Fun β n M η f ω) := by
        rw [profileP2Fun_srwKernel_eq_mul β hmn hnM z
          (cellAverage M fun y => Real.exp (h₀ y)) ω]
        have hηCell' := hηCell ω
        dsimp [η] at hηCell'
        rw [hηCell']
        rw [Real.log_mul (Polymer.smoothedP2Plane_pos β m n z ω).ne'
          (profileP2Fun_pos_terminal β n M η f Aη hηA hη0 hηpos' hf ω).ne']
      have hμ'A (ω' : Disorder) :
          ∀ w ∉ Aμ, endpointDist β n z ω' w = 0 := by
        intro w hw
        exact Polymer.endpointDist_eq_zero_of_not_mem β n z w ω' (by simpa [Aμ] using hw)
      have hμ'0 (ω' : Disorder) :
          ∀ w, 0 ≤ endpointDist β n z ω' w := fun w =>
        Polymer.endpointDist_nonneg β n z w ω'
      have hμ'pos (ω' : Disorder) :
          ∃ w ∈ Aμ, 0 < endpointDist β n z ω' w := by
        obtain ⟨w, hw, hpos⟩ := endpointDist_exists_positive β n z ω'
        exact ⟨w, by simpa [Aμ] using hw, hpos⟩
      have hη'A (ω' : Disorder) :
          ∀ w ∉ Aη, smoothedEndpointDist β m n z ω' w = 0 := by
        intro w hw
        exact smoothedEndpointDist_eq_zero_of_not_mem β z w ω'
          (by simpa [Aη] using hw)
      have hη'0 (ω' : Disorder) :
          ∀ w, 0 ≤ smoothedEndpointDist β m n z ω' w := fun w =>
        smoothedEndpointDist_nonneg β z w ω'
      have hη'pos (ω' : Disorder) :
          ∃ w ∈ Aη, 0 < smoothedEndpointDist β m n z ω' w := by
        obtain ⟨w, hw, hpos⟩ := smoothedEndpointDist_exists_positive β hmn z ω'
        exact ⟨w, by simpa [Aη] using hw, hpos⟩
      have hpCenter (ω' : Disorder) :
          Real.log (profileP2Fun β 0 M δz (fun _ => 1) ω') =
            Real.log (pointToPlane β 0 n z ω') +
              Real.log (profileP2Fun β n M (endpointDist β n z ω') (fun _ => 1) ω') := by
        rw [profileP2Fun_point_eq_mul β hnM z (fun _ => 1) ω']
        rw [Real.log_mul (Polymer.pointToPlane_pos β 0 n z ω').ne'
          (profileP2Fun_pos_terminal β n M (endpointDist β n z ω') (fun _ => 1)
            Aμ (hμ'A ω') (hμ'0 ω') (hμ'pos ω') (fun _ => one_pos) ω').ne']
      have hqCenter (ω' : Disorder) :
          Real.log (profileP2Fun β m M κz (fun _ => 1) ω') =
            Real.log (smoothedP2Plane β m n z ω') +
              Real.log (profileP2Fun β n M (smoothedEndpointDist β m n z ω')
                (fun _ => 1) ω') := by
        rw [profileP2Fun_srwKernel_eq_mul β hmn hnM z (fun _ => 1) ω']
        rw [Real.log_mul (Polymer.smoothedP2Plane_pos β m n z ω').ne'
          (profileP2Fun_pos_terminal β n M (smoothedEndpointDist β m n z ω')
            (fun _ => 1) Aη (hη'A ω') (hη'0 ω') (hη'pos ω') (fun _ => one_pos) ω').ne']
      have hcenterPointwise (ω' : Disorder) :
          Real.log (profileP2Fun β 0 M δz (fun _ => 1) ω') -
              Real.log (profileP2Fun β m M κz (fun _ => 1) ω') =
            (Real.log (pointToPlane β 0 n z ω') -
                Real.log (smoothedP2Plane β m n z ω')) +
              globalLogError β m n M (fun _ => 1) z ω' := by
        rw [hpCenter ω', hqCenter ω']
        dsimp [globalLogError]
        ring
      have hglobalFun :
          (fun ω' => globalLogError β m n M (fun _ => 1) z ω') =
            (fun ω' =>
              (Real.log (profileP2Fun β 0 M δz (fun _ => 1) ω') -
                Real.log (profileP2Fun β m M κz (fun _ => 1) ω')) -
              (Real.log (pointToPlane β 0 n z ω') -
                Real.log (smoothedP2Plane β m n z ω'))) := by
        funext ω'
        linarith [hcenterPointwise ω']
      have hglobalInt : Integrable
          (fun ω' => globalLogError β m n M (fun _ => 1) z ω') disorderLaw := by
        rw [hglobalFun]
        exact (hδ1Int.sub hκ1Int).sub (hpInt.sub hqInt)
      have hcenterSplit :
          (∫ ω', Real.log (profileP2Fun β 0 M δz (fun _ => 1) ω') ∂disorderLaw) -
              ∫ ω', Real.log (profileP2Fun β m M κz (fun _ => 1) ω') ∂disorderLaw =
            (∫ ω', (Real.log (pointToPlane β 0 n z ω') -
                Real.log (smoothedP2Plane β m n z ω')) ∂disorderLaw) +
              ∫ ω', globalLogError β m n M (fun _ => 1) z ω' ∂disorderLaw := by
        calc
          _ = ∫ ω', (Real.log (profileP2Fun β 0 M δz (fun _ => 1) ω') -
                Real.log (profileP2Fun β m M κz (fun _ => 1) ω')) ∂disorderLaw :=
              (integral_sub hδ1Int hκ1Int).symm
          _ = ∫ ω', ((Real.log (pointToPlane β 0 n z ω') -
                Real.log (smoothedP2Plane β m n z ω')) +
                globalLogError β m n M (fun _ => 1) z ω') ∂disorderLaw := by
              apply integral_congr_ae
              filter_upwards [] with ω'
              exact hcenterPointwise ω'
          _ = _ := integral_add (hpInt.sub hqInt) hglobalInt
      rw [hpFactor, hqFactor]
      calc
        _ = (Real.log (pointToPlane β 0 n z ω) -
              Real.log (smoothedP2Plane β m n z ω)) +
            (Real.log (profileP2Fun β n M μ f ω) -
              Real.log (profileP2Fun β n M η f ω)) -
            ((∫ ω', Real.log (profileP2Fun β 0 M δz (fun _ => 1) ω') ∂disorderLaw) -
              ∫ ω', Real.log (profileP2Fun β m M κz (fun _ => 1) ω') ∂disorderLaw) := by
                ring
        _ = (Real.log (pointToPlane β 0 n z ω) -
              Real.log (smoothedP2Plane β m n z ω)) +
            (Real.log (profileP2Fun β n M μ f ω) -
              Real.log (profileP2Fun β n M η f ω)) -
            ((∫ ω', (Real.log (pointToPlane β 0 n z ω') -
                Real.log (smoothedP2Plane β m n z ω')) ∂disorderLaw) +
              ∫ ω', globalLogError β m n M (fun _ => 1) z ω' ∂disorderLaw) := by
                rw [hcenterSplit]
        _ = _ := by
              dsimp [globalLogError]
              ring
    let localAt : Site → ℝ := fun z =>
      (Real.log (pointToPlane β 0 n z ω) - Real.log (smoothedP2Plane β m n z ω)) -
        ∫ ω', (Real.log (pointToPlane β 0 n z ω') -
          Real.log (smoothedP2Plane β m n z ω')) ∂disorderLaw
    let globalAt : Site → ℝ := fun z =>
      globalLogError β m n M f z ω -
        ∫ ω', globalLogError β m n M (fun _ => 1) z ω' ∂disorderLaw
    have hlocalInt := integrable_mul_siteFunction_latticePoint M hMpos hφ hφc hφb localAt
    have hglobalInt := integrable_mul_siteFunction_latticePoint M hMpos hφ hφc hφb globalAt
    unfold latticeSmoothingError
    calc
      (∫ x, φ x *
          ((Real.log (profileP2Fun β 0 M
                (fun w => if w = latticePoint M x then 1 else 0)
                (cellAverage M fun y => Real.exp (h₀ y)) ω) -
              ∫ ω', Real.log (profileP2Fun β 0 M
                (fun w => if w = latticePoint M x then 1 else 0) (fun _ => 1) ω') ∂disorderLaw) -
            (Real.log (profileP2Fun β m M
                (fun w => srwKernel m (w - latticePoint M x))
                (cellAverage M fun y => Real.exp (h₀ y)) ω) -
              ∫ ω', Real.log (profileP2Fun β m M
                (fun w => srwKernel m (w - latticePoint M x)) (fun _ => 1) ω') ∂disorderLaw))) =
          (∫ x, φ x * (localAt (latticePoint M x) + globalAt (latticePoint M x))) := by
            apply integral_congr_ae
            filter_upwards [] with x
            exact congrArg (fun u => φ x * u) (hsplit x)
      _ = (∫ x, φ x * localAt (latticePoint M x)) +
          ∫ x, φ x * globalAt (latticePoint M x) := by
            calc
              _ = ∫ x, (φ x * localAt (latticePoint M x)) +
                    (φ x * globalAt (latticePoint M x)) := by
                      apply integral_congr_ae
                      filter_upwards [] with x
                      ring
              _ = _ := integral_add hlocalInt hglobalInt
      _ = localLogError β M m n φ ω +
          ∫ x, φ x * (globalLogError β m n M f (latticePoint M x) ω -
            ∫ ω', globalLogError β m n M (fun _ => 1) (latticePoint M x) ω' ∂disorderLaw) := by
            simp only [localLogError, localAt, globalAt]
  
  

end Critical2DKPZ.Smoothing

end
