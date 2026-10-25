/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.RandomWalk.Estimates
public import Critical2DKPZ.Polymer.FirstCollision
import Critical2DKPZ.Collision.WeightedTerminal
public import Critical2DKPZ.Collision.ConditionalFlat
import Critical2DKPZ.Polymer.Locality
import Mathlib.Tactic

/-! # Spatial renewal profiles and parity-correct Gaussian envelopes -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.Collision

/-- The spatial collision renewal density of equation (A.2), with coupling `σ²`, in the last-renewal convention. -/
def spatialRenewal (σ2 : ℝ) (n : ℕ) (x : Site) : ℝ :=
  if h : n = 0 then (if x = 0 then 1 else 0) else
    ∑ m : Fin n, ∑' z, spatialRenewal σ2 m z * σ2 * srwKernel (n - m) (x - z) ^ 2
termination_by n
decreasing_by exact m.isLt

/-- The spatial renewal kernel at time zero is the point mass at the origin. -/
@[simp] theorem spatialRenewal_zero (σ2 : ℝ) (x : Site) :
    spatialRenewal σ2 0 x = if x = 0 then 1 else 0 := by
  simp [spatialRenewal]

/-- The spatial renewal kernel satisfies the convolution recursion over earlier times and sites. -/
theorem spatialRenewal_succ (σ2 : ℝ) (n : ℕ) (x : Site) :
    spatialRenewal σ2 (n + 1) x =
      ∑ m : Fin (n + 1), ∑' z,
        spatialRenewal σ2 m z * σ2 * srwKernel (n + 1 - m) (x - z) ^ 2 := by
  rw [spatialRenewal]
  simp

/-- The parity-restricted Gaussian envelope of equation (A.8), extended at time zero by the point mass at the origin. -/
def hatGaussian (c : ℝ) (n : ℕ) (x : Site) : ℝ :=
  if n = 0 then (if x = 0 then 1 else 0) else
    (n : ℝ)⁻¹ * Real.exp (-c * ‖siteToPlane x‖ ^ 2 / n) *
      (if Even ((n : ℤ) + x 0 + x 1) then 1 else 0)

/-- The simple random walk kernel vanishes when time and site have incompatible parity. -/
theorem srwKernel_eq_zero_of_not_hatGaussianParity {n : ℕ} {x : Site}
    (h : ¬ Even ((n : ℤ) + x 0 + x 1)) : srwKernel n x = 0 := by
  rw [srwKernel_eq_srwHeat]
  apply LatticeProb.srwHeat_eq_zero_of_parity
  intro hpar
  apply h
  apply (ZMod.intCast_eq_zero_iff_even).mp
  have hsum : (x 0 : ZMod 2) + (x 1 : ZMod 2) =
      ((LatticeProb.graphNorm x : ℕ) : ZMod 2) := by
    rw [LatticeProb.graphNorm_cast_zmod, Fin.sum_univ_two, Int.cast_add]
  rw [Int.cast_add, Int.cast_add, Int.cast_natCast]
  rw [add_assoc, hsum, hpar]
  exact CharTwo.add_self_eq_zero _

/-- The simple random walk kernel has a uniform Gaussian upper bound for sufficiently small positive rates. -/
theorem exists_srwKernel_le_hatGaussian :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, 0 < c → c ≤ c₀ → ∃ C : ℝ, 0 < C ∧
      ∀ n x, srwKernel n x ≤ C * hatGaussian c n x := by
  obtain ⟨A, a, ha, hbound⟩ := srwKernel_gaussianBound
  refine ⟨a, ha, fun c hc hca => ⟨max A 1, by positivity, ?_⟩⟩
  intro n x
  by_cases hn : n = 0
  · subst n
    by_cases hx : x = 0
    · simp [hatGaussian, srwKernel_zero, hx]
    · simp [hatGaussian, srwKernel_zero, hx]
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    by_cases hpar : Even ((n : ℤ) + x 0 + x 1)
    · simp [hatGaussian, hn, hpar]
      have hgauss := hbound n hn1 x
      have hcoef : A / (n : ℝ) ≤ max A 1 / (n : ℝ) :=
        div_le_div_of_nonneg_right (le_max_left A 1) (by positivity)
      have hexparg : -a * ‖siteToPlane x‖ ^ 2 / n ≤
          -c * ‖siteToPlane x‖ ^ 2 / n := by
        apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ (n : ℝ))
        have hmul := mul_le_mul_of_nonneg_right hca (sq_nonneg ‖siteToPlane x‖)
        nlinarith
      have hexp : Real.exp (-a * ‖siteToPlane x‖ ^ 2 / n) ≤
          Real.exp (-c * ‖siteToPlane x‖ ^ 2 / n) :=
        Real.exp_le_exp.mpr hexparg
      have hscale : A / (n : ℝ) * Real.exp (-a * ‖siteToPlane x‖ ^ 2 / n) ≤
          max A 1 / (n : ℝ) * Real.exp (-c * ‖siteToPlane x‖ ^ 2 / n) := by
        calc
          _ ≤ max A 1 / (n : ℝ) * Real.exp (-a * ‖siteToPlane x‖ ^ 2 / n) :=
            mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _)
          _ ≤ max A 1 / (n : ℝ) * Real.exp (-c * ‖siteToPlane x‖ ^ 2 / n) :=
            mul_le_mul_of_nonneg_left hexp
              (div_nonneg (le_trans (by norm_num) (le_max_right A 1)) (by positivity))
      have hexp' : Real.exp (-c * ‖siteToPlane x‖ ^ 2 / n) =
          Real.exp (-(c * ‖siteToPlane x‖ ^ 2) / n) := by
        congr 1
        ring
      calc
        srwKernel n x ≤ A / n * Real.exp (-a * ‖siteToPlane x‖ ^ 2 / n) := hgauss
        _ ≤ max A 1 / n * Real.exp (-c * ‖siteToPlane x‖ ^ 2 / n) := hscale
        _ = max A 1 * ((n : ℝ)⁻¹ * Real.exp (-(c * ‖siteToPlane x‖ ^ 2) / n)) := by
          rw [← hexp']
          ring
    · simp [hatGaussian, hn, hpar,
        srwKernel_eq_zero_of_not_hatGaussianParity hpar]

/-- The second moment of the point to point partition function is invariant under spatial translation. -/
theorem pointToPoint_sq_integral_translate (β : ℝ) (n : ℕ) (w x : Site) :
    ∫ ω, pointToPoint β 0 n w x ω ^ 2 ∂disorderLaw =
      ∫ ω, pointToPoint β 0 n 0 (x - w) ω ^ 2 ∂disorderLaw := by
  let shift : Disorder → Disorder := fun ω p => ω (p.1, p.2 + w)
  have hfun : (fun ω : Disorder =>
      pointToPoint β 0 n w x ω ^ 2) =
        fun ω => pointToPoint β 0 n 0 (x - w) (shift ω) ^ 2 := by
    funext ω
    have h := Polymer.pointToPoint_translate β 0 n 0 (x - w) w ω
    simpa only [zero_add, sub_add_cancel] using congrArg (fun z => z ^ 2) h
  rw [hfun]
  let e : Disorder ≃ᵐ Disorder :=
    MeasurableEquiv.piCongrLeft (fun _ : ℕ × Site => ℝ)
      (Gaussian.spatialTranslation w).symm
  have he' : (MeasurableEquiv.piCongrLeft (fun _ : ℕ × Site => ℝ)
      (Gaussian.spatialTranslation w).symm : Disorder → Disorder) =
        Gaussian.reindexDisorder (Gaussian.spatialTranslation w) := by
    funext ω p
    simp only [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast,
      Equiv.symm_symm, cast_eq, Gaussian.reindexDisorder]
  have hshift : shift = Gaussian.reindexDisorder (Gaussian.spatialTranslation w) := by
    funext ω p
    rfl
  have he : shift = e := hshift.trans he'.symm
  have hmp : MeasurePreserving e disorderLaw disorderLaw := by
    rw [← he]
    exact Gaussian.measurePreserving_disorder_translation w
  rw [he]
  exact hmp.integral_comp e.measurableEmbedding
    (fun ω => pointToPoint β 0 n 0 (x - w) ω ^ 2)

/-- Delta terminal profiles reduce a diagonal pair moment to the point to point second moment. -/
theorem terminalPairMoment_delta_eq_pointToPoint_sq (β : ℝ) (n : ℕ) (w x : Site) :
    terminalPairMoment β n w w (fun z => if z = x then 1 else 0)
      (fun z => if z = x then 1 else 0) =
        ∫ ω, pointToPoint β 0 n w x ω ^ 2 ∂disorderLaw := by
  unfold terminalPairMoment
  simp only [mul_ite, mul_one, mul_zero, tsum_ite_eq]
  congr 1
  funext ω
  ring

/-- The point to point second moment decomposes into the free walk term and the first collision renewal sum. -/
theorem pointToPoint_secondMoment_firstCollision (β : ℝ) (n : ℕ) (x : Site) :
    ∫ ω, pointToPoint β 0 n 0 x ω ^ 2 ∂disorderLaw =
      srwKernel n x ^ 2 + Polymer.sigmaSq β *
        ∑ r ∈ Finset.Icc 1 n, ∑' z,
          srwKernel r z ^ 2 *
            (∫ ω, pointToPoint β 0 (n - r) 0 (x - z) ω ^ 2 ∂disorderLaw) := by
  let δ : Site → ℝ := fun z => if z = x then 1 else 0
  have hfc := terminalPairMoment_firstCollision β n 0 0 δ δ
  have hdelta (m : ℕ) (w : Site) :
      terminalPairMoment β m w w δ δ =
        ∫ ω, pointToPoint β 0 m w x ω ^ 2 ∂disorderLaw := by
    simpa only [δ] using terminalPairMoment_delta_eq_pointToPoint_sq β m w x
  have hmean : terminalWalkMean n 0 δ = srwKernel n x := by
    simp only [terminalWalkMean, δ, sub_zero, mul_ite, mul_one, mul_zero, tsum_ite_eq]
  have hheat (r : ℕ) :
      terminalCollisionHeat r 0 0
          (fun z => terminalPairMoment β (n - r) z z δ δ) =
        ∑' z, srwKernel r z ^ 2 *
          (∫ ω, pointToPoint β 0 (n - r) 0 (x - z) ω ^ 2 ∂disorderLaw) := by
    unfold terminalCollisionHeat
    apply tsum_congr
    intro z
    change srwKernel r (z - 0) * srwKernel r (z - 0) *
        terminalPairMoment β (n - r) z z δ δ = _
    rw [sub_zero, hdelta, pointToPoint_sq_integral_translate]
    ring
  rw [hdelta n 0, hmean] at hfc
  simp_rw [hheat] at hfc
  simpa only [pow_two] using hfc

private theorem sum_Icc_one_succ_eq_fin {n : ℕ} (f : ℕ → ℝ) :
    ∑ r ∈ Finset.Icc 1 (n + 1), f r = ∑ m : Fin (n + 1), f (n + 1 - m.val) := by
  classical
  refine Finset.sum_bij (fun r hr => ⟨n + 1 - r, by
    have hr := Finset.mem_Icc.mp hr
    omega⟩) ?_ ?_ ?_ ?_
  · intro r hr
    simp
  · intro r₁ hr₁ r₂ hr₂ heq
    have hr₁' : r₁ ≤ n + 1 := (Finset.mem_Icc.mp hr₁).2
    have hr₂' : r₂ ≤ n + 1 := (Finset.mem_Icc.mp hr₂).2
    have hval : n + 1 - r₁ = n + 1 - r₂ := by
      exact congrArg Fin.val heq
    exact (tsub_right_inj hr₁' hr₂').mp hval
  · intro m hm
    refine ⟨n + 1 - m.val, ?_, ?_⟩
    · have hm' := m.isLt
      simp only [Finset.mem_Icc]
      omega
    · apply Fin.ext
      change n + 1 - (n + 1 - m.val) = m.val
      exact Nat.sub_sub_self (by omega)
  · intro r hr
    have hrle : r ≤ n + 1 := (Finset.mem_Icc.mp hr).2
    change f r = f (n + 1 - (n + 1 - r))
    congr 1
    exact (Nat.sub_sub_self hrle).symm

private def siteReflection (x : Site) : Site ≃ Site where
  toFun z := x - z
  invFun z := x - z
  left_inv z := by
    ext i
    simp only [Pi.sub_apply]
    omega
  right_inv z := by
    ext i
    simp only [Pi.sub_apply]
    omega

private theorem tsum_reflect_site {F : Site → ℝ} (r : ℕ) (x : Site) :
    ∑' z, srwKernel r z ^ 2 * F (x - z) =
      ∑' y, srwKernel r (x - y) ^ 2 * F y := by
  let e := siteReflection x
  calc
    _ = ∑' y, srwKernel r (e y) ^ 2 * F (x - e y) :=
      (e.tsum_eq (fun z => srwKernel r z ^ 2 * F (x - z))).symm
    _ = _ := by
      apply tsum_congr
      intro y
      simp only [e, siteReflection, Equiv.coe_fn_mk]
      have hy : x - (x - y) = y := by abel
      rw [hy]

private theorem pointToPoint_secondMoment_firstCollision_fin (β : ℝ) (n : ℕ) (x : Site) :
    ∫ ω, pointToPoint β 0 (n + 1) 0 x ω ^ 2 ∂disorderLaw =
      srwKernel (n + 1) x ^ 2 + Polymer.sigmaSq β *
        ∑ m : Fin (n + 1), ∑' y,
          srwKernel (n + 1 - m) (x - y) ^ 2 *
            (∫ ω, pointToPoint β 0 m 0 y ω ^ 2 ∂disorderLaw) := by
  rw [pointToPoint_secondMoment_firstCollision]
  let f : ℕ → ℝ := fun r => ∑' z, srwKernel r z ^ 2 *
    (∫ ω, pointToPoint β 0 (n + 1 - r) 0 (x - z) ω ^ 2 ∂disorderLaw)
  have hsum := sum_Icc_one_succ_eq_fin (n := n) f
  rw [show (fun r => ∑' z, srwKernel r z ^ 2 *
      (∫ ω, pointToPoint β 0 (n + 1 - r) 0 (x - z) ω ^ 2 ∂disorderLaw)) = f by rfl] at hsum
  rw [hsum]
  apply congrArg (fun s : ℝ => srwKernel (n + 1) x ^ 2 + Polymer.sigmaSq β * s)
  apply Finset.sum_congr rfl
  intro m hm
  have htime : n + 1 - (n + 1 - m.val) = m.val :=
    Nat.sub_sub_self (by omega)
  simp only [f]
  rw [htime]
  exact tsum_reflect_site
    (F := fun y => ∫ ω, pointToPoint β 0 m.val 0 y ω ^ 2 ∂disorderLaw)
    (n + 1 - m.val) x

private theorem pointToPoint_zero_secondMoment (β : ℝ) (x : Site) :
    ∫ ω, pointToPoint β 0 0 0 x ω ^ 2 ∂disorderLaw = if x = 0 then 1 else 0 := by
  by_cases hx : x = 0 <;> simp [Polymer.pointToPoint_zero, hx, eq_comm]

/-- The diagonal point-to-point second moment is the normalized spatial renewal profile.
The nonzero-coupling assumption makes the normalization by `sigmaSq` well-defined. -/
theorem spatialRenewal_secondMoment {β : ℝ} (hβ : β ≠ 0) {n : ℕ} (hn : 1 ≤ n) (x : Site) :
    ∫ ω, pointToPoint β 0 n 0 x ω ^ 2 ∂disorderLaw =
      (1 + Polymer.sigmaSq β) / Polymer.sigmaSq β *
        spatialRenewal (Polymer.sigmaSq β) n x := by
  revert hn x
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn x
    have hσ : 0 < Polymer.sigmaSq β := by
      unfold Polymer.sigmaSq
      rw [sub_pos]
      exact Real.one_lt_exp_iff.mpr (sq_pos_of_ne_zero hβ)
    cases n with
    | zero => omega
    | succ k =>
      let c : ℝ := (1 + Polymer.sigmaSq β) / Polymer.sigmaSq β
      have hc : Polymer.sigmaSq β * c = 1 + Polymer.sigmaSq β := by
        dsimp [c]
        field_simp [hσ.ne']
      have hIH (m : Fin k) (y : Site) :
          ∫ ω, pointToPoint β 0 (m.val + 1) 0 y ω ^ 2 ∂disorderLaw =
            c * spatialRenewal (Polymer.sigmaSq β) (m.val + 1) y := by
        exact ih (m.val + 1) (by have := m.isLt; omega) (by omega) y
      rw [pointToPoint_secondMoment_firstCollision_fin β k x,
        spatialRenewal_succ (Polymer.sigmaSq β) k x,
        Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp only [Fin.val_zero, Nat.sub_zero, Fin.val_succ, Nat.succ_sub_succ_eq_sub]
      simp only [pointToPoint_zero_secondMoment]
      simp only [mul_ite, mul_one, mul_zero, tsum_ite_eq, sub_zero]
      have hbase : ∑' z, spatialRenewal (Polymer.sigmaSq β) 0 z *
          Polymer.sigmaSq β * srwKernel (k + 1) (x - z) ^ 2 =
          Polymer.sigmaSq β * srwKernel (k + 1) x ^ 2 := by
        simp [spatialRenewal_zero, tsum_ite_eq]
      rw [hbase]
      -- The positive-gap summands agree by the induction hypothesis; the zero-gap atom
      -- contributes the extra `srwKernel (k+1) x ^ 2` in the first-collision formula.
      have hpos : Polymer.sigmaSq β *
          (∑ m : Fin k, ∑' y, srwKernel (k - m.val) (x - y) ^ 2 *
            (∫ ω, pointToPoint β 0 (m.val + 1) 0 y ω ^ 2 ∂disorderLaw)) =
          c * (∑ m : Fin k, ∑' y,
            spatialRenewal (Polymer.sigmaSq β) (m.val + 1) y * Polymer.sigmaSq β *
              srwKernel (k - m.val) (x - y) ^ 2) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        calc
          _ = ∑' y, Polymer.sigmaSq β *
                (srwKernel (k - m.val) (x - y) ^ 2 *
                  (∫ ω, pointToPoint β 0 (m.val + 1) 0 y ω ^ 2 ∂disorderLaw)) := by
                  rw [← tsum_mul_left]
          _ = ∑' y, c *
                (spatialRenewal (Polymer.sigmaSq β) (m.val + 1) y *
                  Polymer.sigmaSq β * srwKernel (k - m.val) (x - y) ^ 2) := by
                  apply tsum_congr
                  intro y
                  rw [hIH m y]
                  dsimp [c]
                  ring
          _ = c * ∑' y,
                spatialRenewal (Polymer.sigmaSq β) (m.val + 1) y *
                  Polymer.sigmaSq β * srwKernel (k - m.val) (x - y) ^ 2 := by
                  rw [tsum_mul_left]
      change srwKernel (k + 1) x ^ 2 + Polymer.sigmaSq β *
          (srwKernel (k + 1) x ^ 2 +
            ∑ m : Fin k, ∑' y, srwKernel (k - m.val) (x - y) ^ 2 *
              (∫ ω, pointToPoint β 0 (m.val + 1) 0 y ω ^ 2 ∂disorderLaw)) =
        c * (Polymer.sigmaSq β * srwKernel (k + 1) x ^ 2 +
          ∑ m : Fin k, ∑' y,
            spatialRenewal (Polymer.sigmaSq β) (m.val + 1) y * Polymer.sigmaSq β *
              srwKernel (k - m.val) (x - y) ^ 2)
      calc
        _ = (1 + Polymer.sigmaSq β) * srwKernel (k + 1) x ^ 2 +
            Polymer.sigmaSq β *
              (∑ m : Fin k, ∑' y, srwKernel (k - m.val) (x - y) ^ 2 *
                (∫ ω, pointToPoint β 0 (m.val + 1) 0 y ω ^ 2 ∂disorderLaw)) := by ring
        _ = (1 + Polymer.sigmaSq β) * srwKernel (k + 1) x ^ 2 +
            c * (∑ m : Fin k, ∑' y,
              spatialRenewal (Polymer.sigmaSq β) (m.val + 1) y * Polymer.sigmaSq β *
                srwKernel (k - m.val) (x - y) ^ 2) := by rw [hpos]
        _ = c * (Polymer.sigmaSq β * srwKernel (k + 1) x ^ 2 +
            ∑ m : Fin k, ∑' y,
              spatialRenewal (Polymer.sigmaSq β) (m.val + 1) y * Polymer.sigmaSq β *
                srwKernel (k - m.val) (x - y) ^ 2) := by
              rw [← hc]
              ring

end Critical2DKPZ.Collision

end
