/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Symmetries.LatticeReversalDiscrete
public import Critical2DKPZ.PolymerCalculus.KernelReversal
public import Critical2DKPZ.PolymerCalculus.TimeReversal
public import Critical2DKPZ.Polymer.Moments
public import Critical2DKPZ.RandomMeasure.PlanePairInterface
public import Critical2DKPZ.SHF.Moments.CriticalBoundary
public import Critical2DKPZ.SHF.Moments.TimeRounding
public import Critical2DKPZ.SHF.Positivity.CompactConvergence
public import Critical2DKPZ.SHF.Tsai.ConvergenceApproximation
public import Critical2DKPZ.SHF.Tsai.SecondMomentApproximation
public import Critical2DKPZ.SHF.Flow.SlabProductsIdentities
public import Critical2DKPZ.SHF.Moments.WordDominationFlatPairMoment
import Mathlib.Tactic
import Critical2DKPZ.SHF.Moments.WordDominationPositivity

/-! # Finite-scale lattice reversal and the SHF reversed finite-dimensional laws -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Moments Critical2DKPZ.SHF.Tsai
open scoped CompactlySupported Topology

namespace Critical2DKPZ.SHF.Symmetries

/-- The centered path weight has second moment `exp (n * β ^ 2) - 1`. -/
theorem integral_sq_pathWeight_sub_one (β : ℝ) (a : ℕ) (w : Site)
    {n : ℕ} (s : Fin n → Fin 4) :
    ∫ ω, (Polymer.pathWeight β a w s ω - 1) ^ 2 ∂disorderLaw =
      Real.exp ((n : ℝ) * β ^ 2) - 1 := by
  have hW := Polymer.integrable_pathWeight β a w s
  have hW2 : Integrable (fun ω => Polymer.pathWeight β a w s ω ^ 2) disorderLaw := by
    have h := (Polymer.memLp_pathWeight β a w s (2 : ENNReal) (by norm_num)).integrable_norm_pow'
    simpa only [Real.norm_eq_abs,
      abs_of_pos (Polymer.pathWeight_pos β a w s _)] using h
  have hmean := Polymer.integral_pathWeight β a w s
  have hsecond :
      ∫ ω, Polymer.pathWeight β a w s ω * Polymer.pathWeight β a w s ω
          ∂disorderLaw = Real.exp ((n : ℝ) * β ^ 2) := by
    rw [Polymer.integral_pathWeight_mul]
    -- Each of the `n` distinct time coordinates contributes the same Gaussian factor.
    have hprod (m : ℕ) :
        (∏ j ∈ Finset.Icc 1 m, Real.exp (β ^ 2)) =
          Real.exp ((m : ℝ) * β ^ 2) := by
      induction m with
      | zero => simp
      | succ m ih =>
          rw [Finset.prod_Icc_succ_top (a := 1) (b := m) (by omega)]
          rw [ih]
          rw [show ((m + 1 : ℕ) : ℝ) * β ^ 2 = (m : ℝ) * β ^ 2 + β ^ 2 by push_cast; ring,
            Real.exp_add]
    simpa using hprod n
  have heq (ω : Disorder) :
      (Polymer.pathWeight β a w s ω - 1) ^ 2 =
        Polymer.pathWeight β a w s ω ^ 2 - 2 * Polymer.pathWeight β a w s ω + 1 := by
    ring
  calc
    _ = ∫ ω, (Polymer.pathWeight β a w s ω ^ 2 -
        2 * Polymer.pathWeight β a w s ω) + 1 ∂disorderLaw := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall heq
    _ = (∫ ω, Polymer.pathWeight β a w s ω ^ 2 ∂disorderLaw) -
        2 * (∫ ω, Polymer.pathWeight β a w s ω ∂disorderLaw) + 1 := by
          have hAdd :
              (∫ ω, (Polymer.pathWeight β a w s ω ^ 2 -
                2 * Polymer.pathWeight β a w s ω) + 1 ∂disorderLaw) =
              (∫ ω, Polymer.pathWeight β a w s ω ^ 2 -
                2 * Polymer.pathWeight β a w s ω ∂disorderLaw) +
                ∫ ω, (1 : ℝ) ∂disorderLaw := by
            simpa only [Pi.add_apply, Pi.sub_apply] using
              (integral_add (μ := disorderLaw)
                (hW2.sub (hW.const_mul 2)) (integrable_const (1 : ℝ)))
          rw [hAdd, integral_sub hW2 (hW.const_mul 2), integral_const_mul,
            integral_const]
          have hprob : disorderLaw.real Set.univ = 1 := by simp
          rw [hprob]
          rw [hmean]
          ring
    _ = _ := by
      have hsecond' : ∫ ω, Polymer.pathWeight β a w s ω ^ 2 ∂disorderLaw =
          Real.exp ((n : ℝ) * β ^ 2) := by simpa only [pow_two] using hsecond
      rw [hsecond', hmean]
      ring






private theorem integrable_sq_exp_coordinate_sub_one (β : ℝ) (i : ℕ × Site) :
    Integrable (fun ω => (Real.exp (β * ω i) - 1) ^ 2) disorderLaw := by
  have hB : Integrable (fun ω => Real.exp (β * ω i)) disorderLaw :=
    Integrable.of_integral_ne_zero (by
      rw [Polymer.integral_exp_coordinate]
      exact Real.exp_ne_zero _)
  have hB2 : Integrable (fun ω => Real.exp ((2 * β) * ω i)) disorderLaw :=
    Integrable.of_integral_ne_zero (by
      rw [Polymer.integral_exp_coordinate]
      exact Real.exp_ne_zero _)
  have hEq (ω : Disorder) : (Real.exp (β * ω i) - 1) ^ 2 =
      (Real.exp ((2 * β) * ω i) - 2 * Real.exp (β * ω i)) + 1 := by
    calc
      (Real.exp (β * ω i) - 1) ^ 2 =
          Real.exp (β * ω i) * Real.exp (β * ω i) -
            2 * Real.exp (β * ω i) + 1 := by ring
      _ = Real.exp (β * ω i + β * ω i) - 2 * Real.exp (β * ω i) + 1 := by
        rw [← Real.exp_add]
      _ = (Real.exp ((2 * β) * ω i) - 2 * Real.exp (β * ω i)) + 1 := by
        congr 1
        congr 1
        ring_nf
  have hIntegrable : Integrable (fun ω =>
      (Real.exp ((2 * β) * ω i) - 2 * Real.exp (β * ω i)) + 1) disorderLaw :=
    (hB2.sub (hB.const_mul 2)).add (integrable_const (1 : ℝ))
  exact hIntegrable.congr (Filter.Eventually.of_forall fun ω => (hEq ω).symm)

private theorem integral_sq_exp_coordinate_sub_one (β : ℝ) (i : ℕ × Site) :
    ∫ ω, (Real.exp (β * ω i) - 1) ^ 2 ∂disorderLaw =
      Real.exp (2 * β ^ 2) - 2 * Real.exp (β ^ 2 / 2) + 1 := by
  have hB : Integrable (fun ω => Real.exp (β * ω i)) disorderLaw :=
    Integrable.of_integral_ne_zero (by
      rw [Polymer.integral_exp_coordinate]
      exact Real.exp_ne_zero _)
  have hB2 : Integrable (fun ω => Real.exp ((2 * β) * ω i)) disorderLaw :=
    Integrable.of_integral_ne_zero (by
      rw [Polymer.integral_exp_coordinate]
      exact Real.exp_ne_zero _)
  have hEq (ω : Disorder) : (Real.exp (β * ω i) - 1) ^ 2 =
      (Real.exp ((2 * β) * ω i) - 2 * Real.exp (β * ω i)) + 1 := by
    calc
      (Real.exp (β * ω i) - 1) ^ 2 =
          Real.exp (β * ω i) * Real.exp (β * ω i) -
            2 * Real.exp (β * ω i) + 1 := by ring
      _ = Real.exp (β * ω i + β * ω i) - 2 * Real.exp (β * ω i) + 1 := by
        rw [← Real.exp_add]
      _ = (Real.exp ((2 * β) * ω i) - 2 * Real.exp (β * ω i)) + 1 := by
        congr 1
        congr 1
        ring_nf
  calc
    _ = ∫ ω, (Real.exp ((2 * β) * ω i) -
        2 * Real.exp (β * ω i)) + 1 ∂disorderLaw := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hEq
    _ = (∫ ω, Real.exp ((2 * β) * ω i) ∂disorderLaw) -
        2 * (∫ ω, Real.exp (β * ω i) ∂disorderLaw) + 1 := by
      have hAdd :
          (∫ ω, (Real.exp ((2 * β) * ω i) - 2 * Real.exp (β * ω i)) +
            1 ∂disorderLaw) =
          (∫ ω, Real.exp ((2 * β) * ω i) -
            2 * Real.exp (β * ω i) ∂disorderLaw) + ∫ ω, (1 : ℝ) ∂disorderLaw := by
        simpa only [Pi.add_apply, Pi.sub_apply] using
          (integral_add (μ := disorderLaw) (hB2.sub (hB.const_mul 2))
            (integrable_const (1 : ℝ)))
      rw [hAdd, integral_sub hB2 (hB.const_mul 2), integral_const_mul, integral_const]
      simp
    _ = _ := by
      rw [Polymer.integral_exp_coordinate, Polymer.integral_exp_coordinate]
      rw [show ((2 * β) ^ 2 / 2 : ℝ) = 2 * β ^ 2 by ring]

private theorem integral_abs_le_sqrt_integral_sq (f : Disorder → ℝ)
    (hfmeas : Measurable f) (hf : Integrable (fun ω => f ω ^ 2) disorderLaw) :
    ∫ ω, |f ω| ∂disorderLaw ≤ Real.sqrt (∫ ω, f ω ^ 2 ∂disorderLaw) := by
  have hfmem : MemLp f (ENNReal.ofReal (2 : ℝ)) disorderLaw := by
    have hfmem' : MemLp f 2 disorderLaw :=
      (memLp_two_iff_integrable_sq hfmeas.aestronglyMeasurable).2 (by
        simpa only [Real.norm_eq_abs, sq_abs] using hf)
    simpa using hfmem'
  have hAbsMem : MemLp (fun ω => |f ω|) (ENNReal.ofReal (2 : ℝ)) disorderLaw := by
    have h := hfmem.norm
    simpa only [Real.norm_eq_abs] using h
  have honeMem : MemLp (fun _ : Disorder => (1 : ℝ))
      (ENNReal.ofReal (2 : ℝ)) disorderLaw := by
    exact memLp_const 1
  have honeNonneg : 0 ≤ᵐ[disorderLaw] (fun _ : Disorder => (1 : ℝ)) :=
    Filter.Eventually.of_forall fun _ => by norm_num
  have hAbsNonneg : 0 ≤ᵐ[disorderLaw] (fun ω => |f ω|) :=
    Filter.Eventually.of_forall fun ω => abs_nonneg _
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := disorderLaw) (p := (2 : ℝ)) (q := (2 : ℝ))
    Real.HolderConjugate.two_two honeNonneg hAbsNonneg honeMem hAbsMem
  have hOne : ∫ ω, (1 : ℝ) ^ 2 ∂disorderLaw = 1 := by simp
  have hSq : ∫ ω, |f ω| ^ 2 ∂disorderLaw = ∫ ω, f ω ^ 2 ∂disorderLaw := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω => by
      simpa only [Pi.pow_apply] using (sq_abs (f ω))
  calc
    _ = ∫ ω, (1 : ℝ) * |f ω| ∂disorderLaw := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun _ => by ring
    _ ≤ (∫ ω, (1 : ℝ) ^ 2 ∂disorderLaw) ^ (1 / 2 : ℝ) *
        (∫ ω, |f ω| ^ 2 ∂disorderLaw) ^ (1 / 2 : ℝ) := by
      simpa only [Real.rpow_two] using hHolder
    _ = Real.sqrt (∫ ω, f ω ^ 2 ∂disorderLaw) := by
      calc
        _ = 1 ^ (1 / 2 : ℝ) * (∫ ω, |f ω| ^ 2 ∂disorderLaw) ^ (1 / 2 : ℝ) := by
          exact congrArg (fun q : ℝ => q ^ (1 / 2 : ℝ) *
            (∫ ω, |f ω| ^ 2 ∂disorderLaw) ^ (1 / 2 : ℝ)) hOne
        _ = (∫ ω, |f ω| ^ 2 ∂disorderLaw) ^ (1 / 2 : ℝ) := by simp
        _ = (∫ ω, f ω ^ 2 ∂disorderLaw) ^ (1 / 2 : ℝ) :=
          congrArg (fun q : ℝ => q ^ (1 / 2 : ℝ)) hSq
        _ = Real.sqrt (∫ ω, f ω ^ 2 ∂disorderLaw) := by
          exact (Real.sqrt_eq_rpow _).symm


private theorem indepFun_coordinate_pointToPoint (β : ℝ) (a n : ℕ) (x y : Site) :
    IndepFun (fun ω : Disorder => ω (a, x))
      (pointToPoint β a n x y) disorderLaw := by
  let S : Set (ℕ × Site) := {(a, x)}
  let T : Set (ℕ × Site) := Gaussian.timeBlock a (a + n)
  have hdisj : Disjoint S T := by
    rw [Set.disjoint_left]
    intro i hi hT
    simp only [S, Set.mem_singleton_iff] at hi
    subst i
    exact (Nat.lt_irrefl a) hT.1
  have hspace : Indep (Gaussian.coordinateSigma
      (fun _ : ℕ × Site => ℝ) S) (Gaussian.disorderBlock a (a + n)) disorderLaw := by
    change Indep
      (MeasurableSpace.comap (fun ω : Disorder => S.domRestrict ω) MeasurableSpace.pi)
      (MeasurableSpace.comap (fun ω : Disorder => T.domRestrict ω) MeasurableSpace.pi)
      disorderLaw
    exact (IndepFun_iff_Indep _ _ _).mp
      (Gaussian.indepFun_restrict_infinitePi (fun _ : ℕ × Site => gaussianReal 0 1)
        S T hdisj)
  have hcoord : Measurable[Gaussian.coordinateSigma
      (fun _ : ℕ × Site => ℝ) S] (fun ω : Disorder => ω (a, x)) := by
    change Measurable[(MeasurableSpace.pi).comap
      (fun ω : Disorder => S.domRestrict ω)] (fun ω => ω (a, x))
    exact (measurable_pi_apply (⟨(a, x), by simp [S]⟩ : S)).comp
      (comap_measurable (fun ω : Disorder => S.domRestrict ω))
  have hkernel : Measurable[Gaussian.disorderBlock a (a + n)]
      (pointToPoint β a n x y) :=
    Polymer.measurable_pointToPoint_block β a n x y
  exact ProbabilityTheory.indep_of_indep_of_le hspace hcoord.comap_le hkernel.comap_le

private theorem integral_abs_exp_sub_one_mul_pointToPoint (β : ℝ) (a n : ℕ)
    (x y : Site) :
    ∫ ω, |Real.exp (β * ω (a, x)) - 1| * pointToPoint β a n x y ω ∂disorderLaw =
      (∫ ω, |Real.exp (β * ω (a, x)) - 1| ∂disorderLaw) * srwKernel n (y - x) := by
  have hExp : Integrable (fun ω => Real.exp (β * ω (a, x))) disorderLaw :=
    Integrable.of_integral_ne_zero (by
      rw [Polymer.integral_exp_coordinate]
      exact Real.exp_ne_zero _)
  have hAbs : Integrable (fun ω => |Real.exp (β * ω (a, x)) - 1|) disorderLaw :=
    (hExp.sub (integrable_const (1 : ℝ))).norm
  have hPoint : Integrable (pointToPoint β a n x y) disorderLaw :=
    Polymer.integrable_pointToPoint β a n x y
  have hind := (indepFun_coordinate_pointToPoint β a n x y).comp
    (show Measurable (fun z : ℝ => |Real.exp (β * z) - 1|) by fun_prop)
    measurable_id
  have hfactor : ∫ ω, |Real.exp (β * ω (a, x)) - 1| *
      pointToPoint β a n x y ω ∂disorderLaw =
      (∫ ω, |Real.exp (β * ω (a, x)) - 1| ∂disorderLaw) *
        ∫ ω, pointToPoint β a n x y ω ∂disorderLaw := by
    simpa [Function.comp_apply] using
      hind.integral_fun_mul_eq_mul_integral hAbs.aestronglyMeasurable
        hPoint.aestronglyMeasurable
  rw [hfactor, Polymer.integral_pointToPoint]

/-- The compactly supported cell-kernel sum has a uniform bound and finite support at each scale. -/
theorem exists_tsum_compactAbs_cellKernel_bound {ε : ℝ}
    (hε : 0 < ε) (φ : C_c(Plane × Plane, ℝ)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ N n : ℕ, ε * N ≤ n →
        (∑' q : Site × Site,
          cellTestWeight N (compactAbs φ) q.1 q.2 * srwKernel n (q.2 - q.1)) ≤
          C * ∫ p, compactAbs φ p := by
  obtain ⟨C, hC, hscaled⟩ := Critical2DKPZ.SHF.Moments.scaled_srwKernel_bound hε
  refine ⟨C, hC, ?_⟩
  intro N n hgap
  let ψ : C_c(Plane × Plane, ℝ) := compactAbs φ
  let K : Plane × Plane → ℝ := fun p =>
    ((N : ℝ) / 4) * srwKernel n (latticePoint N p.2 - latticePoint N p.1)
  have hψInt : Integrable (fun p => ψ p) volume :=
    ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
  have hψNonneg (p : Plane × Plane) : 0 ≤ ψ p := by
    change 0 ≤ |φ p|
    exact abs_nonneg _
  have hKmeas : Measurable K := by
    dsimp [K]
    exact measurable_const.mul ((measurable_of_countable
      (fun z : Site => srwKernel n z)).comp
      (((measurable_latticePoint N).comp measurable_snd).sub
        ((measurable_latticePoint N).comp measurable_fst)))
  have hKle (p : Plane × Plane) : K p ≤ C := by
    dsimp [K]
    exact hscaled N n hgap (latticePoint N p.2 - latticePoint N p.1)
  have hKnonneg (p : Plane × Plane) : 0 ≤ K p := by
    dsimp [K]
    exact mul_nonneg (by positivity) (srwKernel_nonneg _ _)
  have hKnorm (p : Plane × Plane) : ‖K p‖ ≤ C := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hKnonneg p)]
    exact hKle p
  have hprodInt : Integrable (fun p => ψ p * K p) volume :=
    hψInt.mul_bdd hKmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hKnorm)
  have hmajorInt : Integrable (fun p => C * ψ p) volume := hψInt.const_mul C
  have hmassEq :
      (∑' q : Site × Site,
        cellTestWeight N ψ q.1 q.2 * srwKernel n (q.2 - q.1)) =
      ∫ p, ψ p * K p := by
    calc
      _ = ((N : ℝ) / 4) *
          (∑' q : Site × Site,
            (∫ p in cell N q.1 ×ˢ cell N q.2, ψ p) * srwKernel n (q.2 - q.1)) := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro q
        simp only [cellTestWeight]
        ring
      _ = ((N : ℝ) / 4) *
          (∫ p, ψ p * srwKernel n (latticePoint N p.2 - latticePoint N p.1)) := by
        congr 1
        simpa only [Function.comp_apply] using
          (Critical2DKPZ.SHF.Flow.integral_latticePairing_eq_cellTsum N ψ
            (fun x y => srwKernel n (y - x))).symm
      _ = ∫ p, ψ p * K p := by
        calc
          _ = ∫ p, ((N : ℝ) / 4) *
              (ψ p * srwKernel n (latticePoint N p.2 - latticePoint N p.1)) :=
            (integral_const_mul _ _).symm
          _ = ∫ p, ψ p *
              (((N : ℝ) / 4) * srwKernel n
                (latticePoint N p.2 - latticePoint N p.1)) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun p => by ring
          _ = ∫ p, ψ p * K p := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun p => by rfl
  rw [hmassEq]
  calc
    (∫ p, ψ p * K p) ≤ ∫ p, C * ψ p := by
      apply integral_mono hprodInt hmajorInt
      intro p
      calc
        ψ p * K p ≤ ψ p * C := mul_le_mul_of_nonneg_left (hKle p) (hψNonneg p)
        _ = C * ψ p := by ring
    _ = C * ∫ p, ψ p := integral_const_mul C ψ

/-- The tested start-endpoint error is integrable and has the stated kernel-mass bound. -/
theorem integral_abs_pairing_startEndpoint_error_le (ϑ : ℝ) {N : ℕ}
    {s t : ℝ} (φ : C_c(Plane × Plane, ℝ)) (C : ℝ)
    (hkernelMass : ∑' q : Site × Site,
        cellTestWeight N (compactAbs φ) q.1 q.2 *
          srwKernel (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) (q.2 - q.1) ≤
        C * ∫ p, compactAbs φ p) :
    Integrable (fun ω => ∫ p, φ p *
      ((Real.exp (criticalBeta ϑ N * ω
          (evenCeil ((N : ℝ) * s), latticePoint N p.1)) - 1) *
        rescaledP2P ϑ N s t p ω)) disorderLaw ∧
      (∫ ω, |∫ p, φ p *
        ((Real.exp (criticalBeta ϑ N * ω
            (evenCeil ((N : ℝ) * s), latticePoint N p.1)) - 1) *
          rescaledP2P ϑ N s t p ω)| ∂disorderLaw) ≤
        Real.sqrt (Real.exp (2 * (criticalBeta ϑ N) ^ 2) -
          2 * Real.exp ((criticalBeta ϑ N) ^ 2 / 2) + 1) * C *
          ∫ p, compactAbs φ p := by
  let a := evenCeil ((N : ℝ) * s)
  let n := evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)
  let β := criticalBeta ϑ N
  let S := (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N φ).toFinset
  let ψ : C_c(Plane × Plane, ℝ) := compactAbs φ
  let W : Site × Site → ℝ := fun q => cellTestWeight N φ q.1 q.2
  let F : Site × Site → Disorder → ℝ := fun q ω =>
    W q * ((Real.exp (β * ω (a, q.1)) - 1) *
      pointToPoint β a n q.1 q.2 ω)
  have hpairSum (ω : Disorder) :
      (∫ p, φ p *
        ((Real.exp (β * ω (a, latticePoint N p.1)) - 1) *
          rescaledP2P ϑ N s t p ω)) = ∑ q ∈ S, F q ω := by
    rw [pairing_startEndpoint_error_eq_tsum]
    change (∑' q : Site × Site, F q ω) = ∑ q ∈ S, F q ω
    apply tsum_eq_sum
    intro q hq
    have hzero : W q = 0 := by
      exact cellTestWeight_eq_zero_of_not_mem N φ q (by simpa [S] using hq)
    change W q * ((Real.exp (β * ω (a, q.1)) - 1) *
      pointToPoint β a n q.1 q.2 ω) = 0
    rw [hzero]
    ring
  have hterm (q : Site × Site) : Integrable (F q) disorderLaw := by
    have hExp : Integrable (fun ω => Real.exp (β * ω (a, q.1))) disorderLaw :=
      Integrable.of_integral_ne_zero (by
        rw [Polymer.integral_exp_coordinate]
        exact Real.exp_ne_zero _)
    have hNoise : Integrable (fun ω => Real.exp (β * ω (a, q.1)) - 1) disorderLaw :=
      hExp.sub (integrable_const (1 : ℝ))
    have hPoint : Integrable (pointToPoint β a n q.1 q.2) disorderLaw :=
      Polymer.integrable_pointToPoint β a n q.1 q.2
    have hind := (indepFun_coordinate_pointToPoint β a n q.1 q.2).comp
      (show Measurable (fun z : ℝ => Real.exp (β * z) - 1) by fun_prop) measurable_id
    exact (hind.integrable_mul hNoise hPoint).const_mul (W q)
  have hpairInt : Integrable (fun ω =>
      ∫ p, φ p * ((Real.exp (β * ω (a, latticePoint N p.1)) - 1) *
        rescaledP2P ϑ N s t p ω)) disorderLaw := by
    have hsumInt : Integrable (fun ω => ∑ q ∈ S, F q ω) disorderLaw :=
      integrable_finsetSum _ fun q hq => hterm q
    exact hsumInt.congr (Filter.Eventually.of_forall fun ω => (hpairSum ω).symm)
  have hsumAbsInt : Integrable (fun ω => ∑ q ∈ S, |F q ω|) disorderLaw :=
    integrable_finsetSum _ fun q hq => (hterm q).norm
  have hnoiseL1 (x : Site) :
      ∫ ω, |Real.exp (β * ω (a, x)) - 1| ∂disorderLaw ≤
        Real.sqrt (Real.exp (2 * β ^ 2) - 2 * Real.exp (β ^ 2 / 2) + 1) := by
    calc
      _ ≤ Real.sqrt (∫ ω, (Real.exp (β * ω (a, x)) - 1) ^ 2 ∂disorderLaw) :=
        integral_abs_le_sqrt_integral_sq _ (by fun_prop)
          (integrable_sq_exp_coordinate_sub_one β (a, x))
      _ = _ := by rw [integral_sq_exp_coordinate_sub_one]
  have htermAbs (q : Site × Site) :
      ∫ ω, |F q ω| ∂disorderLaw ≤
        |W q| * (Real.sqrt (Real.exp (2 * β ^ 2) -
          2 * Real.exp (β ^ 2 / 2) + 1) * srwKernel n (q.2 - q.1)) := by
    have hfactor :
        ∫ ω, |F q ω| ∂disorderLaw =
          |W q| * (∫ ω, |Real.exp (β * ω (a, q.1)) - 1| *
            pointToPoint β a n q.1 q.2 ω ∂disorderLaw) := by
      change (∫ ω, |W q * ((Real.exp (β * ω (a, q.1)) - 1) *
        pointToPoint β a n q.1 q.2 ω)| ∂disorderLaw) = _
      calc
        _ = ∫ ω, |W q| *
            (|Real.exp (β * ω (a, q.1)) - 1| *
              pointToPoint β a n q.1 q.2 ω) ∂disorderLaw := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun ω => by
            change |W q * ((Real.exp (β * ω (a, q.1)) - 1) *
              pointToPoint β a n q.1 q.2 ω)| =
              |W q| * (|Real.exp (β * ω (a, q.1)) - 1| *
                pointToPoint β a n q.1 q.2 ω)
            rw [abs_mul, abs_mul,
              abs_of_nonneg (Polymer.pointToPoint_nonneg β a n q.1 q.2 ω)]
        _ = _ := integral_const_mul _ _
    rw [hfactor, integral_abs_exp_sub_one_mul_pointToPoint]
    have hkernel : 0 ≤ srwKernel n (q.2 - q.1) := srwKernel_nonneg _ _
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (hnoiseL1 q.1) hkernel) (abs_nonneg _)
  have hψzero (q : Site × Site)
      (hq : q ∉ (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N ψ).toFinset) :
      cellTestWeight N ψ q.1 q.2 = 0 :=
    cellTestWeight_eq_zero_of_not_mem N ψ q hq
  have hψSumm : Summable (fun q : Site × Site =>
      cellTestWeight N ψ q.1 q.2 * srwKernel n (q.2 - q.1)) := by
    apply summable_of_ne_finset_zero
      (s := (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N ψ).toFinset)
    intro q hq
    rw [hψzero q hq]
    simp
  have hcoeff :
      (∑ q ∈ S, |W q| * srwKernel n (q.2 - q.1)) ≤
        ∑' q : Site × Site,
          cellTestWeight N ψ q.1 q.2 * srwKernel n (q.2 - q.1) := by
    calc
      _ ≤ ∑ q ∈ S, cellTestWeight N ψ q.1 q.2 * srwKernel n (q.2 - q.1) := by
        apply Finset.sum_le_sum
        intro q hq
        dsimp [W, ψ]
        exact mul_le_mul_of_nonneg_right
          (abs_cellTestWeight_le_abs_test N φ q.1 q.2) (srwKernel_nonneg _ _)
      _ ≤ _ := hψSumm.sum_le_tsum S (fun q hq =>
        mul_nonneg (cellTestWeight_nonneg N ψ (by
          intro p
          dsimp [ψ]
          exact abs_nonneg _) q.1 q.2) (srwKernel_nonneg _ _))
  have hrootNonneg : 0 ≤ Real.sqrt (Real.exp (2 * β ^ 2) -
      2 * Real.exp (β ^ 2 / 2) + 1) := Real.sqrt_nonneg _
  have hsumBound :
      (∑ q ∈ S, |W q| * (Real.sqrt (Real.exp (2 * β ^ 2) -
        2 * Real.exp (β ^ 2 / 2) + 1) * srwKernel n (q.2 - q.1))) ≤
        Real.sqrt (Real.exp (2 * β ^ 2) - 2 * Real.exp (β ^ 2 / 2) + 1) *
          C * ∫ p, ψ p := by
    calc
      _ = Real.sqrt (Real.exp (2 * β ^ 2) - 2 * Real.exp (β ^ 2 / 2) + 1) *
          (∑ q ∈ S, |W q| * srwKernel n (q.2 - q.1)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        ring
      _ ≤ Real.sqrt (Real.exp (2 * β ^ 2) - 2 * Real.exp (β ^ 2 / 2) + 1) *
          (∑' q : Site × Site,
            cellTestWeight N ψ q.1 q.2 * srwKernel n (q.2 - q.1)) :=
        mul_le_mul_of_nonneg_left hcoeff hrootNonneg
      _ ≤ _ := by
        calc
          _ ≤ Real.sqrt (Real.exp (2 * β ^ 2) - 2 * Real.exp (β ^ 2 / 2) + 1) *
              (C * ∫ p, compactAbs φ p) :=
            mul_le_mul_of_nonneg_left hkernelMass hrootNonneg
          _ = _ := by simp [ψ, mul_assoc]
  have hmain :
      (∫ ω, |∫ p, φ p *
        ((Real.exp (β * ω (a, latticePoint N p.1)) - 1) *
          rescaledP2P ϑ N s t p ω)| ∂disorderLaw) ≤
        ∑ q ∈ S, |W q| *
          (Real.sqrt (Real.exp (2 * β ^ 2) - 2 * Real.exp (β ^ 2 / 2) + 1) *
            srwKernel n (q.2 - q.1)) := by
    calc
      _ ≤ ∫ ω, ∑ q ∈ S, |F q ω| ∂disorderLaw := by
        apply integral_mono hpairInt.norm hsumAbsInt
        intro ω
        change |∫ p, φ p *
          ((Real.exp (β * ω (a, latticePoint N p.1)) - 1) *
            rescaledP2P ϑ N s t p ω)| ≤ ∑ q ∈ S, |F q ω|
        rw [hpairSum ω]
        exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ q ∈ S, ∫ ω, |F q ω| ∂disorderLaw := by
        simpa only [Real.norm_eq_abs] using
          (integral_finsetSum S (fun q hq => (hterm q).norm))
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro q hq
        exact htermAbs q
  refine ⟨hpairInt, ?_⟩
  simpa [a, n, β, S, ψ, W, compactAbs] using hmain.trans hsumBound


/-- The square-root endpoint-factor error tends to zero as the lattice scale grows. -/
theorem tendsto_expPairingError_root (ϑ : ℝ) :
    Tendsto (fun N : ℕ => Real.sqrt (Real.exp (2 * (criticalBeta ϑ N) ^ 2) -
      2 * Real.exp ((criticalBeta ϑ N) ^ 2 / 2) + 1)) atTop (𝓝 0) := by
  have hβ := Critical2DKPZ.SHF.Moments.tendsto_criticalBeta_zero ϑ
  have hβsq : Tendsto (fun N : ℕ => (criticalBeta ϑ N) ^ 2) atTop (𝓝 0) := by
    simpa using hβ.pow 2
  have hdouble : Tendsto (fun N : ℕ => 2 * (criticalBeta ϑ N) ^ 2)
      atTop (𝓝 0) := by simpa using hβsq.const_mul 2
  have hhalf : Tendsto (fun N : ℕ => (criticalBeta ϑ N) ^ 2 / 2)
      atTop (𝓝 0) := by simpa using hβsq.div_const 2
  have hexpDouble := Real.continuous_exp.continuousAt.tendsto.comp hdouble
  have hexpHalf := Real.continuous_exp.continuousAt.tendsto.comp hhalf
  have hmoment : Tendsto (fun N : ℕ => Real.exp (2 * (criticalBeta ϑ N) ^ 2) -
      2 * Real.exp ((criticalBeta ϑ N) ^ 2 / 2) + 1) atTop (𝓝 0) := by
    have h := (hexpDouble.sub (hexpHalf.const_mul 2)).add_const 1
    convert h using 1 <;> norm_num [Real.exp_zero]
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp hmoment
  change Tendsto ((fun x : ℝ => Real.sqrt x) ∘
    (fun N : ℕ => Real.exp (2 * (criticalBeta ϑ N) ^ 2) -
      2 * Real.exp ((criticalBeta ϑ N) ^ 2 / 2) + 1)) atTop (𝓝 0)
  rw [Real.sqrt_zero] at hroot
  exact hroot


end Critical2DKPZ.SHF.Symmetries

end
