/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.SummableCovariance
public import Critical2DKPZ.Polymer.BlockMeasurability
public import Critical2DKPZ.Gaussian.TimeBlocks
import Critical2DKPZ.Polymer.ConstrainedReplica
import Critical2DKPZ.RandomWalk.KernelBridge
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic

/-! # Conditional flat-terminal collision formula

Conditioning on the disorder through time `a` freezes a past-measurable initial profile and
integrates the independent future slab.  This file gives the finite-support version directly,
including the zero-mass signed case.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open ProbabilityTheory
open scoped BigOperators

namespace Critical2DKPZ.Collision

open Critical2DKPZ.Polymer

/-- A past-measurable scalar is unchanged when the future coordinates are resampled. -/
theorem pastMeasurable_resample_eq {a : ℕ} {f : Disorder → ℝ}
    (hf : Measurable[disorderPast a] f) (ω ξ : Disorder) :
    f (Gaussian.resample (Gaussian.timeBlock 0 a) ω ξ) = f ω := by
  change Measurable[MeasurableSpace.comap
      (fun η (j : {p : ℕ × Site // 0 < p.1 ∧ p.1 ≤ a}) => η j) inferInstance] f at hf
  have hf' : Measurable[MeasurableSpace.comap
      (fun η (j : {p : ℕ × Site // 0 < p.1 ∧ p.1 ≤ a}) => η j) inferInstance] f := hf
  apply hf'.factorsThrough
  funext j
  have hj : (j : ℕ × Site) ∈ Gaussian.timeBlock 0 a := j.property
  simp [Gaussian.resample, hj]

/-- A polymer slab is unchanged when its coordinates are copied from the resampled sample. -/
theorem pointToPlane_resamplePast (β : ℝ) (a n : ℕ) (w : Site) (ω ξ : Disorder) :
    pointToPlane β a n w (Gaussian.resample (Gaussian.timeBlock 0 a) ω ξ) =
      pointToPlane β a n w ξ := by
  unfold pointToPlane
  apply Finset.sum_congr rfl
  intro s hs
  congr 2
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_Icc.mp hj
  have htime : ¬ (a + j, walkPosition w s j) ∈ Gaussian.timeBlock 0 a := by
    simp [Gaussian.timeBlock]
    omega
  simp [Gaussian.resample, htime]

/-- A terminally tested polymer slab is unchanged when its future coordinates are resampled. -/
theorem terminalProfile_resamplePast (β : ℝ) (a n : ℕ) (w : Site)
    (f : Site → ℝ) (ω ξ : Disorder) :
    (∑' z, pointToPoint β a n w z
        (Gaussian.resample (Gaussian.timeBlock 0 a) ω ξ) * f z) =
      ∑' z, pointToPoint β a n w z ξ * f z := by
  rw [tsum_pointToPoint_mul, tsum_pointToPoint_mul]
  apply Finset.sum_congr rfl
  intro s hs
  have hweight : pathWeight β a w s
      (Gaussian.resample (Gaussian.timeBlock 0 a) ω ξ) = pathWeight β a w s ξ := by
    unfold pathWeight
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_Icc.mp hj
    have htime : ¬ (a + j, walkPosition w s j) ∈ Gaussian.timeBlock 0 a := by
      simp [Gaussian.timeBlock]
      omega
    simp [Gaussian.resample, htime]
  rw [hweight]

/-- A finitely supported random profile tested against a terminal function. -/
def randomTerminalProfilePolymer (β : ℝ) (a b : ℕ)
    (η : Disorder → Site → ℝ) (f : Site → ℝ) (ω : Disorder) : ℝ :=
  profileP2Fun β a b (η ω) f ω

/-- Conditional annealing of a finitely supported past-measurable profile with terminal data. -/
theorem condExp_randomTerminalProfilePolymer (β : ℝ) (a b : ℕ) (_hab : a ≤ b)
    (A : Finset Site) (η : Disorder → Site → ℝ) (f : Site → ℝ)
    (hsupp : ∀ ω w, w ∉ A → η ω w = 0)
    (hmeasη : ∀ w, Measurable[disorderPast a] (η · w))
    (hXmeas : Measurable (randomTerminalProfilePolymer β a b η f))
    (hXint : Integrable (randomTerminalProfilePolymer β a b η f) disorderLaw) :
    disorderLaw[randomTerminalProfilePolymer β a b η f | disorderPast a] =ᵐ[disorderLaw]
      fun ω => ∑ w ∈ A, η ω w * ∑' z, srwKernel (b - a) (z - w) * f z := by
  have hce := Gaussian.condExp_disorderBlock_ae_eq 0 a hXmeas hXint
  rw [Gaussian.disorderBlock_zero] at hce
  filter_upwards [hce] with ω hω
  rw [hω]
  have heval (ξ : Disorder) :
      randomTerminalProfilePolymer β a b η f
          (Gaussian.resample (Gaussian.timeBlock 0 a) ω ξ) =
        ∑ w ∈ A, η ω w *
          (∑' z, pointToPoint β a (b - a) w z ξ * f z) := by
    rw [randomTerminalProfilePolymer, profileP2Fun_eq_sum β a b _ _ A (hsupp _)]
    apply Finset.sum_congr rfl
    intro w hw
    rw [pastMeasurable_resample_eq (hmeasη w) ω ξ, terminalProfile_resamplePast]
  simp_rw [heval]
  rw [integral_finsetSum _ fun w _ =>
    (memLp_one_iff_integrable.mp
      (memLp_terminalProfile β a (b - a) w f 1 (by simp))).const_mul _]
  apply Finset.sum_congr rfl
  intro w hw
  rw [integral_const_mul, integral_terminalProfile]

/-- Annealed product of two terminally tested polymer profiles. The integrand is integrable by
`integrable_terminalPairProduct`. -/
def terminalPairMoment (β : ℝ) (n : ℕ) (w v : Site) (f g : Site → ℝ) : ℝ :=
  ∫ ω, (∑' z, pointToPoint β 0 n w z ω * f z) *
    (∑' z, pointToPoint β 0 n v z ω * g z) ∂disorderLaw

/-- The terminal pair moment is invariant under a common shift of the disorder time interval. -/
theorem terminalPairMoment_timeShift (β : ℝ) (a n : ℕ) (w v : Site)
    (f g : Site → ℝ) :
    (∫ ω, (∑' z, pointToPoint β a n w z ω * f z) *
      (∑' z, pointToPoint β a n v z ω * g z) ∂disorderLaw) =
      terminalPairMoment β n w v f g := by
  unfold terminalPairMoment
  rw [terminalProfile_two_replica β a n w v f g,
    terminalProfile_two_replica β 0 n w v f g]

/-- A terminally tested partition function is measurable with respect to its disorder block. -/
theorem measurable_terminalProfile_block (β : ℝ) (a n : ℕ) (w : Site)
    (f : Site → ℝ) :
    Measurable[Gaussian.disorderBlock a (a + n)]
      (fun ω => ∑' z, pointToPoint β a n w z ω * f z) := by
  let : MeasurableSpace Disorder := Gaussian.disorderBlock a (a + n)
  have heq : (fun ω => ∑' z, pointToPoint β a n w z ω * f z) =
      fun ω => ∑ z ∈ endpoints w n, pointToPoint β a n w z ω * f z := by
    funext ω
    exact tsum_pointToPoint_mul_eq_sum β a n w f ω
  rw [heq]
  exact Finset.measurable_sum _ fun z hz =>
    (measurable_pointToPoint_block β a n w z).mul_const _

/-- One-step recursion for the annealed two-replica moment with terminal data. -/
theorem terminalPairMoment_succ (β : ℝ) (n : ℕ) (w v : Site) (f g : Site → ℝ) :
    terminalPairMoment β (n + 1) w v f g =
      ∑ i : Fin 4, ∑ j : Fin 4,
        ((4 : ℝ)⁻¹ * (4 : ℝ)⁻¹) *
          (if w + srwStep i = v + srwStep j then Real.exp (β ^ 2) else 1) *
          terminalPairMoment β n (w + srwStep i) (v + srwStep j) f g := by
  let A (i j : Fin 4) (ω : Disorder) :=
    boltzmann β (1, w + srwStep i) ω * boltzmann β (1, v + srwStep j) ω
  let B (i j : Fin 4) (ω : Disorder) :=
    (∑' z, pointToPoint β 1 n (w + srwStep i) z ω * f z) *
      (∑' z, pointToPoint β 1 n (v + srwStep j) z ω * g z)
  have hAm (i j : Fin 4) : Measurable[Gaussian.disorderBlock 0 1] (A i j) := by
    have hc (z : Site) := measurable_block_coordinate 0 1 (1, z) (by omega)
    exact ((measurable_const.mul (hc _)).sub measurable_const).exp.mul
      (((measurable_const.mul (hc _)).sub measurable_const).exp)
  have hBm (i j : Fin 4) : Measurable[Gaussian.disorderBlock 1 (1 + n)] (B i j) := by
    exact (measurable_terminalProfile_block β 1 n _ f).mul
      (measurable_terminalProfile_block β 1 n _ g)
  have hind (i j : Fin 4) : IndepFun (A i j) (B i j) disorderLaw := by
    rw [IndepFun_iff]
    intro s t hs ht
    exact (Indep_iff _ _ _).1
      (Gaussian.indep_disorderBlock_of_le (show 1 ≤ 1 from le_rfl)) s t
      ((hAm i j).comap_le s hs) ((hBm i j).comap_le t ht)
  have hint (i j : Fin 4) : Integrable (fun ω => A i j ω * B i j ω) disorderLaw := by
    have hA : MemLp (A i j) 2 disorderLaw := memLp_mul_double 2
      (memLp_boltzmann β _ (2 * 2) (by norm_num))
      (memLp_boltzmann β _ (2 * 2) (by norm_num))
    have hB : MemLp (B i j) 2 disorderLaw := memLp_mul_double 2
      (by simpa only [mul_one] using
        (memLp_terminalProfile β 1 n _ f (2 * 2) (by norm_num)))
      (by simpa only [mul_one] using
        (memLp_terminalProfile β 1 n _ g (2 * 2) (by norm_num)))
    exact memLp_one_iff_integrable.mp (memLp_mul_double 1
      (by simpa only [mul_one] using hA) (by simpa only [mul_one] using hB))
  have heq (ω : Disorder) :
      (∑' z, pointToPoint β 0 (n + 1) w z ω * f z) *
        (∑' z, pointToPoint β 0 (n + 1) v z ω * g z) =
      ∑ i : Fin 4, ∑ j : Fin 4, ((4 : ℝ)⁻¹ * (4 : ℝ)⁻¹) *
        (A i j ω * B i j ω) := by
    rw [terminalProfile_succ, terminalProfile_succ, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [A, B, boltzmann, Nat.zero_add]
    ring
  change (∫ ω, (∑' z, pointToPoint β 0 (n + 1) w z ω * f z) *
      (∑' z, pointToPoint β 0 (n + 1) v z ω * g z) ∂disorderLaw) =
    ∑ i : Fin 4, ∑ j : Fin 4,
      ((4 : ℝ)⁻¹ * (4 : ℝ)⁻¹) *
        (if w + srwStep i = v + srwStep j then Real.exp (β ^ 2) else 1) *
          terminalPairMoment β n (w + srwStep i) (v + srwStep j) f g
  simp_rw [heq]
  rw [integral_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun j _ => (hint i j).const_mul _]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ fun j _ => (hint i j).const_mul _]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_const_mul, (hind i j).integral_fun_mul_eq_mul_integral
    ((hAm i j).mono (Gaussian.disorderBlock_le _ _) le_rfl).aestronglyMeasurable
    ((hBm i j).mono (Gaussian.disorderBlock_le _ _) le_rfl).aestronglyMeasurable]
  change (4⁻¹ * 4⁻¹) *
    ((∫ ω, boltzmann β _ ω * boltzmann β _ ω ∂disorderLaw) *
      (∫ ω, (∑' z, pointToPoint β 1 n _ z ω * f z) *
        (∑' z, pointToPoint β 1 n _ z ω * g z) ∂disorderLaw)) = _
  rw [integral_boltzmann_mul, terminalPairMoment_timeShift]
  simp only [Prod.mk.injEq, true_and]
  ring

/-- The free-walk average of terminal data over a duration `n`. -/
def terminalWalkMean (n : ℕ) (w : Site) (f : Site → ℝ) : ℝ :=
  ∑' z, srwKernel n (z - w) * f z

/-- The walk kernel weighted terminal profile is summable because the walk has finite support. -/
theorem summable_terminalWalkMean (n : ℕ) (w : Site) (f : Site → ℝ) :
    Summable (fun z => srwKernel n (z - w) * f z) := by
  apply summable_of_ne_finset_zero (s := endpoints w n)
  intro z hz
  rw [srwKernel_eq_zero_of_not_mem n w z hz, zero_mul]

/-- The free-walk average obeys the one-step heat recursion. -/
theorem terminalWalkMean_succ (n : ℕ) (w : Site) (f : Site → ℝ) :
    terminalWalkMean (n + 1) w f =
      ∑ i : Fin 4, (4 : ℝ)⁻¹ * terminalWalkMean n (w + srwStep i) f := by
  unfold terminalWalkMean
  calc
    _ = ∑' z, ∑ i : Fin 4,
        ((4 : ℝ)⁻¹ * srwKernel n (z - (w + srwStep i))) * f z := by
      apply tsum_congr
      intro z
      rw [Critical2DKPZ.srwKernel_succ, Finset.sum_div, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [div_eq_mul_inv]
      rw [← sub_add_eq_sub_sub]
      ring
    _ = ∑ i : Fin 4, ∑' z,
        ((4 : ℝ)⁻¹ * srwKernel n (z - (w + srwStep i))) * f z := by
      have hs (i : Fin 4) (_hi : i ∈ Finset.univ) :
          Summable (fun z =>
            ((4 : ℝ)⁻¹ * srwKernel n (z - (w + srwStep i))) * f z) := by
        simpa only [mul_assoc] using
          (summable_terminalWalkMean n (w + srwStep i) f).mul_left (4 : ℝ)⁻¹
      exact Summable.tsum_finsetSum (s := Finset.univ) hs
    _ = ∑ i : Fin 4, (4 : ℝ)⁻¹ *
        terminalWalkMean n (w + srwStep i) f := by
      apply Finset.sum_congr rfl
      intro i hi
      change (∑' z, ((4 : ℝ)⁻¹ * srwKernel n
        (z - (w + srwStep i))) * f z) =
          (4 : ℝ)⁻¹ * (∑' z, srwKernel n (z - (w + srwStep i)) * f z)
      calc
        _ = ∑' z, (4 : ℝ)⁻¹ *
            (srwKernel n (z - (w + srwStep i)) * f z) := by
          apply tsum_congr
          intro z
          ring
        _ = _ := tsum_mul_left

/-- The terminal pair recursion separates its free step and its selected collision. -/
theorem terminalPairMoment_recurrence (β : ℝ) (n : ℕ) (w v : Site)
    (f g : Site → ℝ) :
    terminalPairMoment β (n + 1) w v f g =
      pairStep (fun x y => terminalPairMoment β n x y f g) w v +
        sigmaSq β * pairStep
          (fun x y => if x = y then terminalPairMoment β n x y f g else 0) w v := by
  rw [terminalPairMoment_succ]
  unfold pairStep
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : w + srwStep i = v + srwStep j
  · simp [h, sigmaSq]
    ring
  · simp [h]

/-- The product of two terminally tested partition functions is integrable under the disorder law. -/
theorem integrable_terminalPairProduct (β : ℝ) (a n : ℕ) (w v : Site)
    (f g : Site → ℝ) :
    Integrable (fun ω =>
      (∑' z, pointToPoint β a n w z ω * f z) *
        (∑' z, pointToPoint β a n v z ω * g z)) disorderLaw := by
  apply memLp_one_iff_integrable.mp
  apply memLp_mul_double 1
  · simpa only [mul_one] using
      (memLp_terminalProfile β a n w f 2 (by norm_num) :
        MemLp (fun ω => ∑' z, pointToPoint β a n w z ω * f z) 2 disorderLaw)
  · simpa only [mul_one] using
      (memLp_terminalProfile β a n v g 2 (by norm_num) :
        MemLp (fun ω => ∑' z, pointToPoint β a n v z ω * g z) 2 disorderLaw)

/-- A bounded terminal function is controlled pathwise by the flat polymer mass. -/
theorem terminalProfile_abs_le_pointToPlane (β : ℝ) (a n : ℕ) (w : Site)
    (f : Site → ℝ) (B : ℝ) (hf : ∀ z, |f z| ≤ B) (ω : Disorder) :
    |∑' z, pointToPoint β a n w z ω * f z| ≤ B * pointToPlane β a n w ω := by
  have hplane : pointToPlane β a n w ω =
      ∑ z ∈ endpoints w n, pointToPoint β a n w z ω := by
    calc
      pointToPlane β a n w ω = ∑' z, pointToPoint β a n w z ω :=
        (tsum_pointToPoint β a n w ω).symm
      _ = ∑ z ∈ endpoints w n, pointToPoint β a n w z ω := by
        simpa using
          (tsum_pointToPoint_mul_eq_sum β a n w (fun _ => 1) ω)
  rw [tsum_pointToPoint_mul_eq_sum β a n w f ω]
  calc
    |∑ z ∈ endpoints w n, pointToPoint β a n w z ω * f z|
        ≤ ∑ z ∈ endpoints w n,
            |pointToPoint β a n w z ω * f z| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ z ∈ endpoints w n, pointToPoint β a n w z ω * B := by
      apply Finset.sum_le_sum
      intro z hz
      rw [abs_mul, abs_of_nonneg (pointToPoint_nonneg β a n w z ω)]
      exact mul_le_mul_of_nonneg_left (hf z) (pointToPoint_nonneg β a n w z ω)
    _ = B * pointToPlane β a n w ω := by
      rw [← Finset.sum_mul, hplane]
      ring

/-- Both integrands in `terminalProfile_secondMoment_le` are integrable under the disorder law. -/
theorem terminalProfile_secondMoment_integrable (β : ℝ) (a n : ℕ) (w : Site)
    (f : Site → ℝ) :
    Integrable (fun ω => (∑' z, pointToPoint β a n w z ω * f z) ^ 2) disorderLaw ∧
      Integrable (fun ω => pointToPlane β a n w ω ^ 2) disorderLaw := by
  constructor
  · simpa only [pow_two] using integrable_terminalPairProduct β a n w w f f
  · exact integrable_pow_pointToPlane β a n w 2

/-- The future second moment with bounded terminal data is controlled by the flat one.
Integrability of both sides is stated in `terminalProfile_secondMoment_integrable`. -/
theorem terminalProfile_secondMoment_le (β : ℝ) (a n : ℕ) (w : Site)
    (f : Site → ℝ) (B : ℝ) (hB : 0 ≤ B) (hf : ∀ z, |f z| ≤ B) :
    (∫ ω, (∑' z, pointToPoint β a n w z ω * f z) ^ 2 ∂disorderLaw) ≤
      B ^ 2 * ∫ ω, pointToPlane β a n w ω ^ 2 ∂disorderLaw := by
  have hInt := terminalProfile_secondMoment_integrable β a n w f
  have hT := hInt.1
  have hP := hInt.2
  have hpoint (ω : Disorder) :
      (∑' z, pointToPoint β a n w z ω * f z) ^ 2 ≤
        B ^ 2 * pointToPlane β a n w ω ^ 2 := by
    have hbound := terminalProfile_abs_le_pointToPlane β a n w f B hf ω
    have hnonneg : 0 ≤ B * pointToPlane β a n w ω :=
      mul_nonneg hB (pointToPlane_pos β a n w ω).le
    have hmul := mul_nonneg (sub_nonneg.mpr hbound)
      (add_nonneg (abs_nonneg (∑' z : Site,
        pointToPoint β a n w z ω * f z)) hnonneg)
    nlinarith [sq_abs (∑' z, pointToPoint β a n w z ω * f z),
      sq_abs (B * pointToPlane β a n w ω)]
  calc
    _ ≤ ∫ ω, B ^ 2 * pointToPlane β a n w ω ^ 2 ∂disorderLaw :=
      integral_mono hT (hP.const_mul _) hpoint
    _ = B ^ 2 * ∫ ω, pointToPlane β a n w ω ^ 2 ∂disorderLaw := integral_const_mul _ _

/-- Conditional second moment of a finitely supported past profile with terminal data. -/
theorem condExp_randomTerminalProfilePolymer_mul (β : ℝ) (a b : ℕ) (_hab : a ≤ b)
    (A : Finset Site) (η : Disorder → Site → ℝ) (f g : Site → ℝ)
    (hsupp : ∀ ω w, w ∉ A → η ω w = 0)
    (hmeasη : ∀ w, Measurable[disorderPast a] (η · w))
    (hXmeas : Measurable (fun ω =>
      randomTerminalProfilePolymer β a b η f ω * randomTerminalProfilePolymer β a b η g ω))
    (hXint : Integrable (fun ω =>
      randomTerminalProfilePolymer β a b η f ω * randomTerminalProfilePolymer β a b η g ω)
        disorderLaw) :
    disorderLaw[(fun ω =>
      randomTerminalProfilePolymer β a b η f ω * randomTerminalProfilePolymer β a b η g ω)
      | disorderPast a] =ᵐ[disorderLaw] fun ω =>
        ∑ w ∈ A, ∑ v ∈ A, η ω w * η ω v * terminalPairMoment β (b - a) w v f g := by
  have hce := Gaussian.condExp_disorderBlock_ae_eq 0 a hXmeas hXint
  rw [Gaussian.disorderBlock_zero] at hce
  filter_upwards [hce] with ω hω
  rw [hω]
  have heval (ξ : Disorder) :
      randomTerminalProfilePolymer β a b η f
          (Gaussian.resample (Gaussian.timeBlock 0 a) ω ξ) =
        ∑ w ∈ A, η ω w *
          (∑' z, pointToPoint β a (b - a) w z ξ * f z) := by
    rw [randomTerminalProfilePolymer, profileP2Fun_eq_sum β a b _ _ A (hsupp _)]
    apply Finset.sum_congr rfl
    intro w hw
    rw [pastMeasurable_resample_eq (hmeasη w) ω ξ, terminalProfile_resamplePast]
  have hevalG (ξ : Disorder) :
      randomTerminalProfilePolymer β a b η g
          (Gaussian.resample (Gaussian.timeBlock 0 a) ω ξ) =
        ∑ w ∈ A, η ω w *
          (∑' z, pointToPoint β a (b - a) w z ξ * g z) := by
    rw [randomTerminalProfilePolymer, profileP2Fun_eq_sum β a b _ _ A (hsupp _)]
    apply Finset.sum_congr rfl
    intro w hw
    rw [pastMeasurable_resample_eq (hmeasη w) ω ξ, terminalProfile_resamplePast]
  simp_rw [heval, hevalG]
  have hfun (ξ : Disorder) :
      (∑ w ∈ A, η ω w * (∑' z, pointToPoint β a (b - a) w z ξ * f z)) *
        (∑ v ∈ A, η ω v * (∑' z, pointToPoint β a (b - a) v z ξ * g z)) =
      ∑ w ∈ A, ∑ v ∈ A, (η ω w * η ω v) *
        ((∑' z, pointToPoint β a (b - a) w z ξ * f z) *
          (∑' z, pointToPoint β a (b - a) v z ξ * g z)) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro w hw
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hfun)]
  rw [integral_finsetSum _ fun w _ =>
    integrable_finsetSum _ fun v _ =>
      (integrable_terminalPairProduct β a (b - a) w v f g).const_mul _]
  apply Finset.sum_congr rfl
  intro w hw
  rw [integral_finsetSum _ fun v _ =>
    (integrable_terminalPairProduct β a (b - a) w v f g).const_mul _]
  apply Finset.sum_congr rfl
  intro v hv
  rw [integral_const_mul]
  unfold terminalPairMoment
  rw [terminalProfile_two_replica β a (b - a) w v f g,
    terminalProfile_two_replica β 0 (b - a) w v f g]

/-- Resampling the future disorder leaves a past-measurable initial profile unchanged. -/
theorem profileP2Fun_resamplePast (β : ℝ) (a b : ℕ)
    (A : Finset Site) (η : Disorder → Site → ℝ)
    (hsupp : ∀ ω w, w ∉ A → η ω w = 0)
    (hmeas : ∀ w, Measurable[disorderPast a] (η · w)) (ω ξ : Disorder) :
    profileP2Fun β a b (η (Gaussian.resample (Gaussian.timeBlock 0 a) ω ξ))
        (fun _ => 1) (Gaussian.resample (Gaussian.timeBlock 0 a) ω ξ) =
      ∑ w ∈ A, η ω w * pointToPlane β a (b - a) w ξ := by
  rw [profileP2Fun_eq_sum β a b _ _ A (hsupp _)]
  simp only [mul_one, tsum_pointToPoint]
  apply Finset.sum_congr rfl
  intro w hw
  rw [pastMeasurable_resample_eq (hmeas w) ω ξ, pointToPlane_resamplePast]

/-- The polymer started from a random profile whose coefficients depend only on the past. -/
def randomFlatProfilePolymer (β : ℝ) (a b : ℕ)
    (η : Disorder → Site → ℝ) (ω : Disorder) : ℝ :=
  profileP2Fun β a b (η ω) (fun _ => 1) ω

/-- Conditional annealing of a finitely supported past-measurable profile. -/
theorem condExp_randomFlatProfilePolymer (β : ℝ) (a b : ℕ) (_hab : a ≤ b)
    (A : Finset Site) (η : Disorder → Site → ℝ)
    (hsupp : ∀ ω w, w ∉ A → η ω w = 0)
    (hmeasη : ∀ w, Measurable[disorderPast a] (η · w))
    (hXmeas : Measurable (randomFlatProfilePolymer β a b η))
    (hXint : Integrable (randomFlatProfilePolymer β a b η) disorderLaw) :
    disorderLaw[randomFlatProfilePolymer β a b η | disorderPast a] =ᵐ[disorderLaw]
      fun ω => ∑ w ∈ A, η ω w := by
  have hce := Gaussian.condExp_disorderBlock_ae_eq 0 a hXmeas hXint
  rw [Gaussian.disorderBlock_zero] at hce
  filter_upwards [hce] with ω hω
  rw [hω]
  have heval (ξ : Disorder) :
      randomFlatProfilePolymer β a b η
          (Gaussian.resample (Gaussian.timeBlock 0 a) ω ξ) =
        ∑ w ∈ A, η ω w * pointToPlane β a (b - a) w ξ := by
    exact profileP2Fun_resamplePast β a b A η hsupp hmeasη ω ξ
  simp_rw [heval]
  rw [integral_finsetSum _ fun w _ =>
    (integrable_pointToPlane β a (b - a) w).const_mul _]
  simp only [integral_const_mul, integral_pointToPlane, mul_one]

/-- Conditional second moment of a finitely supported past-measurable profile. -/
theorem condExp_randomFlatProfilePolymer_sq (β : ℝ) (a b : ℕ) (_hab : a ≤ b)
    (A : Finset Site) (η : Disorder → Site → ℝ)
    (hsupp : ∀ ω w, w ∉ A → η ω w = 0)
    (hmeasη : ∀ w, Measurable[disorderPast a] (η · w))
    (hXmeas : Measurable (fun ω => randomFlatProfilePolymer β a b η ω ^ 2))
    (hXint : Integrable (fun ω => randomFlatProfilePolymer β a b η ω ^ 2) disorderLaw) :
    disorderLaw[(fun ω => randomFlatProfilePolymer β a b η ω ^ 2) | disorderPast a] =ᵐ[
      disorderLaw] fun ω =>
        ∑ w ∈ A, ∑ v ∈ A,
          η ω w * η ω v * pairMoment β (b - a) w v := by
  have hce := Gaussian.condExp_disorderBlock_ae_eq 0 a hXmeas hXint
  rw [Gaussian.disorderBlock_zero] at hce
  filter_upwards [hce] with ω hω
  rw [hω]
  have heval (ξ : Disorder) :
      randomFlatProfilePolymer β a b η
          (Gaussian.resample (Gaussian.timeBlock 0 a) ω ξ) =
        ∑ w ∈ A, η ω w * pointToPlane β a (b - a) w ξ := by
    exact profileP2Fun_resamplePast β a b A η hsupp hmeasη ω ξ
  simp_rw [heval]
  have hfun (ξ : Disorder) :
      (∑ w ∈ A, η ω w * pointToPlane β a (b - a) w ξ) ^ 2 =
        ∑ w ∈ A, ∑ v ∈ A,
          (η ω w * η ω v) *
            (pointToPlane β a (b - a) w ξ * pointToPlane β a (b - a) v ξ) := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro w hw
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    ring
  simp_rw [hfun]
  rw [integral_finsetSum _ fun w _ =>
    integrable_finsetSum _ fun v _ =>
      (integrable_pairProduct β a (b - a) w v).const_mul _]
  apply Finset.sum_congr rfl
  intro w hw
  rw [integral_finsetSum _ fun v _ =>
    (integrable_pairProduct β a (b - a) w v).const_mul _]
  apply Finset.sum_congr rfl
  intro v hv
  rw [integral_const_mul, integral_pairMoment]

/-- Free heat evolution of a finitely supported signed profile. -/
def heatEvolveFinite (r : ℕ) (A : Finset Site) (ν : Site → ℝ) (z : Site) : ℝ :=
  ∑ w ∈ A, ν w * srwKernel r (z - w)

/-- The collision-kernel quadratic form equals the squared spatial heat profile. -/
theorem collisionProfileSquared_tsum (r : ℕ) (A : Finset Site) (ν : Site → ℝ) :
    (∑ w ∈ A, ∑ v ∈ A, ν w * ν v * srwKernel (2 * r) (v - w)) =
      ∑' z, (heatEvolveFinite r A ν z) ^ 2 := by
  let C : Finset Site := A.biUnion fun w => endpoints w r
  have hsupport (z : Site) (hz : z ∉ C) : heatEvolveFinite r A ν z = 0 := by
    unfold heatEvolveFinite
    apply Finset.sum_eq_zero
    intro w hw
    have hzw : z ∉ endpoints w r := by
      intro hz'
      exact hz (Finset.mem_biUnion.mpr ⟨w, hw, hz'⟩)
    rw [srwKernel_eq_zero_of_not_mem r w z hzw, mul_zero]
  have hcollision (w v : Site) (hw : w ∈ A) (hv : v ∈ A) :
      (∑ z ∈ C, srwKernel r (z - w) * srwKernel r (z - v)) =
        srwKernel (2 * r) (v - w) := by
    have hzero (z : Site) (hz : z ∉ C) :
        srwKernel r (z - w) * srwKernel r (z - v) = 0 := by
      have hzw : z ∉ endpoints w r := by
        intro hz'
        exact hz (Finset.mem_biUnion.mpr ⟨w, hw, hz'⟩)
      rw [srwKernel_eq_zero_of_not_mem r w z hzw, zero_mul]
    rw [← tsum_eq_sum (β := Site) (L := SummationFilter.unconditional Site)
      (f := fun z : Site =>
      srwKernel r (z - w) * srwKernel r (z - v)) (s := C) hzero,
      srwKernel_collision]
  have hpoint (z : Site) : (heatEvolveFinite r A ν z) ^ 2 =
      ∑ w ∈ A, ∑ v ∈ A,
        (ν w * ν v) * (srwKernel r (z - w) * srwKernel r (z - v)) := by
    unfold heatEvolveFinite
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro w hw
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    ring
  have hsupport2 (z : Site) (hz : z ∉ C) :
      (heatEvolveFinite r A ν z) ^ 2 = 0 := by rw [hsupport z hz]; simp
  rw [tsum_eq_sum (s := C) hsupport2]
  simp_rw [hpoint]
  calc
    _ = ∑ w ∈ A, ∑ v ∈ A, (ν w * ν v) *
          ∑ z ∈ C, srwKernel r (z - w) * srwKernel r (z - v) := by
      apply Finset.sum_congr rfl
      intro w hw
      apply Finset.sum_congr rfl
      intro v hv
      rw [← hcollision w v hw hv]
    _ = ∑ w ∈ A, ∑ z ∈ C, ∑ v ∈ A,
          (ν w * ν v) * (srwKernel r (z - w) * srwKernel r (z - v)) := by
      apply Finset.sum_congr rfl
      intro w hw
      calc
        _ = ∑ v ∈ A, ∑ z ∈ C,
              (ν w * ν v) * (srwKernel r (z - w) * srwKernel r (z - v)) := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [Finset.mul_sum]
        _ = ∑ z ∈ C, ∑ v ∈ A,
              (ν w * ν v) * (srwKernel r (z - w) * srwKernel r (z - v)) :=
          Finset.sum_comm
    _ = ∑ z ∈ C, ∑ w ∈ A, ∑ v ∈ A,
          (ν w * ν v) * (srwKernel r (z - w) * srwKernel r (z - v)) := by
      rw [Finset.sum_comm]
    _ = _ := rfl

/-- Scalar multiples of the collision form retain the same spatial representation. -/
theorem collisionProfileWeighted_tsum (r : ℕ) (A : Finset Site) (ν : Site → ℝ) (c : ℝ) :
    (∑ w ∈ A, ∑ v ∈ A,
      ν w * ν v * srwKernel (2 * r) (v - w) * c) =
      c * ∑' z, (heatEvolveFinite r A ν z) ^ 2 := by
  calc
    _ = (∑ w ∈ A, ∑ v ∈ A,
          ν w * ν v * srwKernel (2 * r) (v - w)) * c := by
      calc
        _ = ∑ w ∈ A, ∑ v ∈ A,
            (ν w * ν v * srwKernel (2 * r) (v - w)) * c := by
          apply Finset.sum_congr rfl
          intro w hw
          apply Finset.sum_congr rfl
          intro v hv
          ring
        _ = ∑ w ∈ A,
            (∑ v ∈ A, ν w * ν v * srwKernel (2 * r) (v - w)) * c := by
          apply Finset.sum_congr rfl
          intro w hw
          rw [← Finset.sum_mul]
        _ = _ := by rw [← Finset.sum_mul]
    _ = _ := by rw [collisionProfileSquared_tsum]; ring

/-- The conditional variance of a polymer started from a finitely supported signed past-measurable profile equals its first-collision expansion, with no zero-mass assumption on the profile. -/
theorem condVar_randomFlatProfilePolymer_eq_firstCollision (β : ℝ) (a b : ℕ)
    (hab : a ≤ b) (A : Finset Site) (η : Disorder → Site → ℝ)
    (hsupp : ∀ ω w, w ∉ A → η ω w = 0)
    (hmeasη : ∀ w, Measurable[disorderPast a] (η · w))
    (hXmeas : Measurable (randomFlatProfilePolymer β a b η))
    (hXint : Integrable (randomFlatProfilePolymer β a b η) disorderLaw)
    (hX2meas : Measurable (fun ω => randomFlatProfilePolymer β a b η ω ^ 2))
    (hX2int : Integrable (fun ω => randomFlatProfilePolymer β a b η ω ^ 2) disorderLaw) :
    disorderLaw[(fun ω => randomFlatProfilePolymer β a b η ω ^ 2) | disorderPast a] -
      (disorderLaw[randomFlatProfilePolymer β a b η | disorderPast a]) ^ 2 =ᵐ[
        disorderLaw] fun ω =>
          ∑ r ∈ Finset.Icc 1 (b - a),
            ∑ w ∈ A, ∑ v ∈ A,
              η ω w * η ω v * srwKernel (2 * r) (v - w) * sigmaSq β *
                pairMoment β (b - a - r) 0 0 := by
  have hmean := condExp_randomFlatProfilePolymer β a b hab A η hsupp hmeasη hXmeas hXint
  have hsecond := condExp_randomFlatProfilePolymer_sq β a b hab A η hsupp hmeasη
    hX2meas hX2int
  filter_upwards [hmean, hsecond] with ω hm hs
  change disorderLaw[(fun ω => randomFlatProfilePolymer β a b η ω ^ 2) | disorderPast a] ω -
      (disorderLaw[randomFlatProfilePolymer β a b η | disorderPast a] ω) ^ 2 = _
  rw [hs, hm]
  have h := profile_firstCollision_finset β a (b - a) (η ω) (η ω) A A
    (hsupp ω) (hsupp ω)
  have hba : a + (b - a) = b := Nat.add_sub_of_le hab
  rw [hba] at h
  have hbase :
      (∫ ξ, profileP2Fun β a b (η ω) (fun _ => 1) ξ ^ 2 ∂disorderLaw) =
        ∑ w ∈ A, ∑ v ∈ A, η ω w * η ω v * pairMoment β (b - a) w v := by
    rw [← hba]
    simp_rw [pow_two]
    rw [integral_profile_product_finset β a (b - a) (η ω) (η ω) A A
      (hsupp ω) (hsupp ω)]
    simp only [Nat.add_sub_cancel_left]
  calc
    _ = (∫ ξ, profileP2Fun β a b (η ω) (fun _ => 1) ξ ^ 2 ∂disorderLaw) -
          (∑ w ∈ A, η ω w) * (∑ v ∈ A, η ω v) := by rw [hbase, pow_two]
    _ = _ := by simpa only [pow_two, pairMoment_eq_secondMoment] using h

/-- The conditional first-collision variance identity expressed through the evolved spatial heat profile. -/
theorem condVar_randomFlatProfilePolymer_eq_spatialFirstCollision (β : ℝ) (a b : ℕ)
    (hab : a ≤ b) (A : Finset Site) (η : Disorder → Site → ℝ)
    (hsupp : ∀ ω w, w ∉ A → η ω w = 0)
    (hmeasη : ∀ w, Measurable[disorderPast a] (η · w))
    (hXmeas : Measurable (randomFlatProfilePolymer β a b η))
    (hXint : Integrable (randomFlatProfilePolymer β a b η) disorderLaw)
    (hX2meas : Measurable (fun ω => randomFlatProfilePolymer β a b η ω ^ 2))
    (hX2int : Integrable (fun ω => randomFlatProfilePolymer β a b η ω ^ 2) disorderLaw) :
    disorderLaw[(fun ω => randomFlatProfilePolymer β a b η ω ^ 2) | disorderPast a] -
      (disorderLaw[randomFlatProfilePolymer β a b η | disorderPast a]) ^ 2 =ᵐ[
        disorderLaw] fun ω =>
          ∑ r ∈ Finset.Icc 1 (b - a),
            (sigmaSq β * pairMoment β (b - a - r) 0 0) *
              ∑' z, (heatEvolveFinite r A (η ω) z) ^ 2 := by
  have hpair := condVar_randomFlatProfilePolymer_eq_firstCollision β a b hab A η
    hsupp hmeasη hXmeas hXint hX2meas hX2int
  filter_upwards [hpair] with ω hω
  rw [hω]
  apply Finset.sum_congr rfl
  intro r hr
  have hc := collisionProfileWeighted_tsum r A (η ω)
    (sigmaSq β * pairMoment β (b - a - r) 0 0)
  calc
    _ = ∑ w ∈ A, ∑ v ∈ A,
          η ω w * η ω v * srwKernel (2 * r) (v - w) *
            (sigmaSq β * pairMoment β (b - a - r) 0 0) := by
          apply Finset.sum_congr rfl
          intro w hw
          apply Finset.sum_congr rfl
          intro v hv
          ring
    _ = _ := hc

end Critical2DKPZ.Collision

end
