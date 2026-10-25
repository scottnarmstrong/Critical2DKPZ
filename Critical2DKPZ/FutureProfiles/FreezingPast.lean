/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Collision.WeightedTerminal
public import Critical2DKPZ.FutureProfiles.Basic
public import Critical2DKPZ.Polymer.ProfileCovariance
public import Critical2DKPZ.Smoothing.EndpointDistribution
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Tactic

/-! # Freezing finite profiles with respect to the past -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Critical2DKPZ.FutureProfiles

open Critical2DKPZ.Polymer
open Critical2DKPZ.Collision

private theorem disorderPast_le (a : ℕ) :
    disorderPast a ≤ (inferInstance : MeasurableSpace Disorder) := by
  rw [← Gaussian.disorderBlock_zero a]
  exact Gaussian.disorderBlock_le 0 a

/-- The future energy of a finite profile is its finite two-replica moment sum. -/
theorem futureEnergy_eq_pairMoment_sum (β : ℝ) {a b : ℕ} (hab : a ≤ b)
    (η : Site → ℝ) (A : Finset Site) (hsupp : ∀ w ∉ A, η w = 0) :
    futureEnergy β a b η =
      ∑ w ∈ A, ∑ v ∈ A, η w * η v * pairMoment β (b - a) w v := by
  have h := integral_profile_product_finset β a (b - a) η η A A hsupp hsupp
  simpa only [futureEnergy, pow_two, Nat.add_sub_of_le hab] using h

/-- The future energy of a bounded past profile is past-measurable. -/
theorem measurable_futureEnergy (β : ℝ) {a b : ℕ} (hab : a ≤ b)
    (η : Disorder → Site → ℝ) (A : Finset Site)
    (hsupp : ∀ ω w, w ∉ A → η ω w = 0)
    (hmeasη : ∀ w, Measurable[disorderPast a] (η · w)) :
    Measurable[disorderPast a] (fun ω => futureEnergy β a b (η ω)) := by
  have heq (ω : Disorder) : futureEnergy β a b (η ω) =
      ∑ w ∈ A, ∑ v ∈ A, η ω w * η ω v * pairMoment β (b - a) w v :=
    futureEnergy_eq_pairMoment_sum β hab (η ω) A (hsupp ω)
  rw [show (fun ω => futureEnergy β a b (η ω)) =
      fun ω => ∑ w ∈ A, ∑ v ∈ A,
        η ω w * η ω v * pairMoment β (b - a) w v by funext ω; exact heq ω]
  exact Finset.measurable_sum _ fun w hw => Finset.measurable_sum _ fun v hv =>
    ((hmeasη w).mul (hmeasη v)).mul_const (pairMoment β (b - a) w v)

/-- Future energy is nonnegative. -/
theorem futureEnergy_nonneg (β : ℝ) (a b : ℕ) (η : Site → ℝ) :
    0 ≤ futureEnergy β a b η := by
  unfold futureEnergy
  exact integral_nonneg fun ω => sq_nonneg _

/-- A finite past profile with bounded coefficients and bounded terminal data is measurable. -/
theorem measurable_randomTerminalProfilePolymer (β : ℝ) (a b : ℕ)
    (A : Finset Site) (η : Disorder → Site → ℝ) (f : Site → ℝ)
    (hsupp : ∀ ω w, w ∉ A → η ω w = 0)
    (hmeasη : ∀ w, Measurable[disorderPast a] (η · w)) :
    Measurable (randomTerminalProfilePolymer β a b η f) := by
  have hpast : disorderPast a ≤ (inferInstance : MeasurableSpace Disorder) := by
    rw [← Gaussian.disorderBlock_zero a]
    exact Gaussian.disorderBlock_le 0 a
  have hη (w : Site) : Measurable (η · w) := (hmeasη w).mono hpast le_rfl
  have heq (ω : Disorder) :
      randomTerminalProfilePolymer β a b η f ω =
        ∑ w ∈ A, η ω w * (∑' z, pointToPoint β a (b - a) w z ω * f z) := by
    rw [randomTerminalProfilePolymer, profileP2Fun_eq_sum β a b _ _ A (hsupp _)]
  change Measurable (fun ω => randomTerminalProfilePolymer β a b η f ω)
  have hfun : (fun ω => randomTerminalProfilePolymer β a b η f ω) =
      fun ω => ∑ w ∈ A, η ω w *
        (∑' z, pointToPoint β a (b - a) w z ω * f z) := by
    funext ω
    exact heq ω
  rw [hfun]
  exact Finset.measurable_sum _ fun w hw => (hη w).mul <| Measurable.tsum fun z =>
    (measurable_pointToPoint β a (b - a) w z).mul_const (f z)

/-- A polymer pairing with a bounded, finitely supported past-measurable initial profile and bounded terminal weights belongs to every finite `Lᵖ` space. -/
theorem memLp_randomTerminalProfilePolymer (β : ℝ) (a b : ℕ)
    (A : Finset Site) (η : Disorder → Site → ℝ) (f : Site → ℝ)
    (hsupp : ∀ ω w, w ∉ A → η ω w = 0)
    (hbdd : ∃ B : ℝ, ∀ ω w, |η ω w| ≤ B)
    (hmeasη : ∀ w, Measurable[disorderPast a] (η · w))
    (M : ℝ) (hf : ∀ z, |f z| ≤ M) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (randomTerminalProfilePolymer β a b η f) p disorderLaw := by
  let B : ℝ := Classical.choose hbdd
  have hB : ∀ ω w, |η ω w| ≤ B := Classical.choose_spec hbdd
  have hB0 : 0 ≤ B := (abs_nonneg (η 0 0)).trans (hB 0 0)
  have hM0 : 0 ≤ M := (abs_nonneg (f 0)).trans (hf 0)
  let S : Disorder → ℝ := fun ω =>
    ∑ w ∈ A, pointToPlane β a (b - a) w ω
  have hS : MemLp S p disorderLaw := by
    exact memLp_finsetSum _ fun w hw => memLp_pointToPlane β a (b - a) w p hp
  have hmeas : Measurable (randomTerminalProfilePolymer β a b η f) :=
    measurable_randomTerminalProfilePolymer β a b A η f hsupp hmeasη
  have hprofile (ω : Disorder) :
      randomTerminalProfilePolymer β a b η f ω =
        ∑ w ∈ A, η ω w * (∑' z, pointToPoint β a (b - a) w z ω * f z) := by
    rw [randomTerminalProfilePolymer, profileP2Fun_eq_sum β a b _ _ A (hsupp _)]
  have hbound (ω : Disorder) :
      ‖randomTerminalProfilePolymer β a b η f ω‖ ≤ (B * M) * ‖S ω‖ := by
    have hSnonneg : 0 ≤ S ω := Finset.sum_nonneg fun w hw =>
      (pointToPlane_pos β a (b - a) w ω).le
    have hterms : ∀ w ∈ A,
        |η ω w * (∑' z, pointToPoint β a (b - a) w z ω * f z)| ≤
          (B * M) * pointToPlane β a (b - a) w ω := by
      intro w hw
      rw [abs_mul]
      calc
        |η ω w| * |∑' z, pointToPoint β a (b - a) w z ω * f z|
            ≤ B * (M * pointToPlane β a (b - a) w ω) := by
              exact mul_le_mul (hB ω w)
                (terminalProfile_abs_le_pointToPlane β a (b - a) w f M hf ω)
                (abs_nonneg _) hB0
        _ = (B * M) * pointToPlane β a (b - a) w ω := by ring
    have hsum :
        |∑ w ∈ A, η ω w * (∑' z, pointToPoint β a (b - a) w z ω * f z)| ≤
          ∑ w ∈ A, (B * M) * pointToPlane β a (b - a) w ω := by
      calc
        _ ≤ ∑ w ∈ A,
            |η ω w * (∑' z, pointToPoint β a (b - a) w z ω * f z)| :=
              Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := Finset.sum_le_sum fun w hw => hterms w hw
    calc
      ‖randomTerminalProfilePolymer β a b η f ω‖ =
          |randomTerminalProfilePolymer β a b η f ω| := by rw [Real.norm_eq_abs]
      _ = |∑ w ∈ A, η ω w *
          (∑' z, pointToPoint β a (b - a) w z ω * f z)| := by rw [hprofile ω]
      _ ≤ ∑ w ∈ A, (B * M) * pointToPlane β a (b - a) w ω := hsum
      _ = (B * M) * S ω := by
        simp only [S]
        rw [Finset.mul_sum]
      _ = (B * M) * ‖S ω‖ := by rw [Real.norm_eq_abs, abs_of_nonneg hSnonneg]
  exact hS.of_le_mul hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => hbound ω)

/-- Integrability of a bounded finite random terminal profile. -/
theorem integrable_randomTerminalProfilePolymer (β : ℝ) (a b : ℕ)
    (A : Finset Site) (η : Disorder → Site → ℝ) (f : Site → ℝ)
    (hsupp : ∀ ω w, w ∉ A → η ω w = 0)
    (hbdd : ∃ B : ℝ, ∀ ω w, |η ω w| ≤ B)
    (hmeasη : ∀ w, Measurable[disorderPast a] (η · w))
    (M : ℝ) (hf : ∀ z, |f z| ≤ M) :
    Integrable (randomTerminalProfilePolymer β a b η f) disorderLaw :=
  memLp_one_iff_integrable.mp <| memLp_randomTerminalProfilePolymer β a b A η f
    hsupp hbdd hmeasη M hf 1 (by norm_num)

/-- Integrability of the square of a bounded finite random terminal profile. -/
theorem integrable_sq_randomTerminalProfilePolymer (β : ℝ) (a b : ℕ)
    (A : Finset Site) (η : Disorder → Site → ℝ) (f : Site → ℝ)
    (hsupp : ∀ ω w, w ∉ A → η ω w = 0)
    (hbdd : ∃ B : ℝ, ∀ ω w, |η ω w| ≤ B)
    (hmeasη : ∀ w, Measurable[disorderPast a] (η · w))
    (M : ℝ) (hf : ∀ z, |f z| ≤ M) :
    Integrable (fun ω => randomTerminalProfilePolymer β a b η f ω ^ 2) disorderLaw := by
  have h := (memLp_randomTerminalProfilePolymer β a b A η f hsupp hbdd hmeasη
    M hf 2 (by norm_num)).integrable_norm_pow'
  simpa only [Real.norm_eq_abs, sq_abs] using h

/-- The conditional second moment of a finite profile is integrable. -/
theorem integrable_futureEnergy (β : ℝ) {a b : ℕ} (hab : a ≤ b)
    (η : Disorder → Site → ℝ) (A : Finset Site)
    (hsupp : ∀ ω w, w ∉ A → η ω w = 0)
    (hbdd : ∃ B : ℝ, ∀ ω w, |η ω w| ≤ B)
    (hmeasη : ∀ w, Measurable[disorderPast a] (η · w)) :
    Integrable (fun ω => futureEnergy β a b (η ω)) disorderLaw := by
  have hXmeas : Measurable (randomFlatProfilePolymer β a b η) := by
    change Measurable (randomTerminalProfilePolymer β a b η (fun _ => 1))
    exact measurable_randomTerminalProfilePolymer β a b A η (fun _ => 1) hsupp hmeasη
  have hX2int : Integrable (fun ω => randomFlatProfilePolymer β a b η ω ^ 2) disorderLaw := by
    simpa only [randomFlatProfilePolymer, randomTerminalProfilePolymer] using
      integrable_sq_randomTerminalProfilePolymer β a b A η (fun _ => 1) hsupp hbdd
        hmeasη 1 (by intro z; simp)
  have hX2meas : Measurable (fun ω => randomFlatProfilePolymer β a b η ω ^ 2) :=
    hXmeas.pow_const 2
  have hCE := condExp_randomFlatProfilePolymer_sq β a b hab A η hsupp hmeasη
    hX2meas hX2int
  have hCEeq : disorderLaw[(fun ω => randomFlatProfilePolymer β a b η ω ^ 2) |
      disorderPast a] =ᵐ[disorderLaw] fun ω => futureEnergy β a b (η ω) := by
    filter_upwards [hCE] with ω hω
    rw [hω, futureEnergy_eq_pairMoment_sum β hab (η ω) A (hsupp ω)]
  have hCEint := integrable_condExp (μ := disorderLaw)
    (f := fun ω => randomFlatProfilePolymer β a b η ω ^ 2)
    (m := disorderPast a)
  exact hCEint.congr hCEeq

/-- The square root of a finite profile's future energy is integrable. -/
theorem integrable_sqrt_futureEnergy (β : ℝ) {a b : ℕ} (hab : a ≤ b)
    (η : Disorder → Site → ℝ) (A : Finset Site)
    (hsupp : ∀ ω w, w ∉ A → η ω w = 0)
    (hbdd : ∃ B : ℝ, ∀ ω w, |η ω w| ≤ B)
    (hmeasη : ∀ w, Measurable[disorderPast a] (η · w)) :
    Integrable (fun ω => Real.sqrt (futureEnergy β a b (η ω))) disorderLaw := by
  have hEint := integrable_futureEnergy β hab η A hsupp hbdd hmeasη
  have hEmeas := measurable_futureEnergy β hab η A hsupp hmeasη
  have hmajor : Integrable (fun ω => 1 + futureEnergy β a b (η ω)) disorderLaw :=
    (integrable_const (1 : ℝ)).add hEint
  refine hmajor.mono' ((hEmeas.mono (disorderPast_le a) le_rfl).sqrt.aestronglyMeasurable) ?_
  filter_upwards with ω
  have hE := futureEnergy_nonneg β a b (η ω)
  have hsqrt := Real.sqrt_nonneg (futureEnergy β a b (η ω))
  have hbound : Real.sqrt (futureEnergy β a b (η ω)) ≤
      1 + futureEnergy β a b (η ω) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · linarith
    · nlinarith [sq_nonneg (futureEnergy β a b (η ω))]
  simpa only [Real.norm_eq_abs, abs_of_nonneg hsqrt,
    abs_of_nonneg (by linarith : 0 ≤ 1 + futureEnergy β a b (η ω))] using hbound

/-- Integrability companion for `setIntegral_profileP2Fun_sq_eq`. -/
theorem integrableOn_profileP2Fun_sq_eq (β : ℝ) {a b : ℕ} (hab : a ≤ b)
    (η : Disorder → Site → ℝ) (A : Finset Site) (hsupp : ∀ ω w, w ∉ A → η ω w = 0)
    (hbdd : ∃ M : ℝ, ∀ ω w, |η ω w| ≤ M)
    (hmeasη : ∀ w, Measurable[disorderPast a] (η · w)) (G : Set Disorder) :
    IntegrableOn (fun ω => profileP2Fun β a b (η ω) (fun _ => 1) ω ^ 2) G disorderLaw ∧
      IntegrableOn (fun ω => futureEnergy β a b (η ω)) G disorderLaw := by
  have hleft : Integrable
      (fun ω => profileP2Fun β a b (η ω) (fun _ => 1) ω ^ 2) disorderLaw := by
    simpa only [randomFlatProfilePolymer, randomTerminalProfilePolymer] using
      integrable_sq_randomTerminalProfilePolymer β a b A η (fun _ => 1) hsupp hbdd
        hmeasη 1 (by intro z; simp)
  exact ⟨hleft.integrableOn,
    (integrable_futureEnergy β hab η A hsupp hbdd hmeasη).integrableOn⟩

/-- Integrating the conditional second moment on a past event gives the second-moment integral.
Integrability of both integrands follows from `integrableOn_profileP2Fun_sq_eq`. -/
theorem setIntegral_profileP2Fun_sq_eq (β : ℝ) {a b : ℕ} (hab : a ≤ b)
    (η : Disorder → Site → ℝ) (A : Finset Site) (hsupp : ∀ ω w, w ∉ A → η ω w = 0)
    (hbdd : ∃ M : ℝ, ∀ ω w, |η ω w| ≤ M)
    (hmeasη : ∀ w, Measurable[disorderPast a] (η · w))
    (G : Set Disorder) (hG : MeasurableSet[disorderPast a] G) :
    ∫ ω in G, profileP2Fun β a b (η ω) (fun _ => 1) ω ^ 2 ∂disorderLaw =
      ∫ ω in G, futureEnergy β a b (η ω) ∂disorderLaw := by
  have hXmeas : Measurable (randomFlatProfilePolymer β a b η) := by
    change Measurable (randomTerminalProfilePolymer β a b η (fun _ => 1))
    exact measurable_randomTerminalProfilePolymer β a b A η (fun _ => 1) hsupp hmeasη
  have hX2int : Integrable (fun ω => randomFlatProfilePolymer β a b η ω ^ 2) disorderLaw := by
    simpa only [randomFlatProfilePolymer, randomTerminalProfilePolymer] using
      integrable_sq_randomTerminalProfilePolymer β a b A η (fun _ => 1) hsupp hbdd
        hmeasη 1 (by intro z; simp)
  have hX2meas : Measurable (fun ω => randomFlatProfilePolymer β a b η ω ^ 2) :=
    hXmeas.pow_const 2
  have hCE := condExp_randomFlatProfilePolymer_sq β a b hab A η hsupp hmeasη
    hX2meas hX2int
  have hCEeq : disorderLaw[(fun ω => randomFlatProfilePolymer β a b η ω ^ 2) |
      disorderPast a] =ᵐ[disorderLaw] fun ω => futureEnergy β a b (η ω) := by
    filter_upwards [hCE] with ω hω
    rw [hω, futureEnergy_eq_pairMoment_sum β hab (η ω) A (hsupp ω)]
  calc
    ∫ ω in G, profileP2Fun β a b (η ω) (fun _ => 1) ω ^ 2 ∂disorderLaw =
        ∫ ω in G, disorderLaw[(fun ω => randomFlatProfilePolymer β a b η ω ^ 2) |
          disorderPast a] ω ∂disorderLaw := by
            simpa only [randomFlatProfilePolymer] using
              (setIntegral_condExp (disorderPast_le a) hX2int hG).symm
    _ = ∫ ω in G, futureEnergy β a b (η ω) ∂disorderLaw :=
      setIntegral_congr_ae ((disorderPast_le a) G hG)
        (hCEeq.mono fun _ h _ => h)

/-- The future energy of a bounded smoothed endpoint profile is integrable. -/
theorem integrable_futureEnergy_smoothedEndpointDist (β : ℝ) (m n N : ℕ)
    (hmn : m ≤ n) (hnN : n ≤ N) (x : Site) :
    Integrable (fun ω => futureEnergy β n N (smoothedEndpointDist β m n x ω)) disorderLaw := by
  classical
  let A := (Polymer.endpoints x m).biUnion (fun y => Polymer.endpoints y (n - m))
  have hsupp (ω : Disorder) (w : Site) (hw : w ∉ A) :
      smoothedEndpointDist β m n x ω w = 0 := by
    exact Smoothing.smoothedEndpointDist_eq_zero_of_not_mem β x w ω (by simpa [A] using hw)
  have hnonneg (ω : Disorder) (w : Site) :
      0 ≤ smoothedEndpointDist β m n x ω w :=
    Smoothing.smoothedEndpointDist_nonneg β x w ω
  have hmass (ω : Disorder) :
      ∑ w ∈ A, smoothedEndpointDist β m n x ω w = 1 := by
    calc
      _ = ∑' w, smoothedEndpointDist β m n x ω w := by
        symm
        exact tsum_eq_sum fun w hw => hsupp ω w hw
      _ = 1 := Smoothing.tsum_smoothedEndpointDist β hmn x ω
  have hbdd : ∃ M : ℝ, ∀ ω w,
      |smoothedEndpointDist β m n x ω w| ≤ M := by
    refine ⟨1, fun ω w => ?_⟩
    rw [abs_of_nonneg (hnonneg ω w)]
    by_cases hw : w ∈ A
    · calc
        smoothedEndpointDist β m n x ω w ≤
            ∑ z ∈ A, smoothedEndpointDist β m n x ω z :=
          Finset.single_le_sum (fun z hz => hnonneg ω z) hw
        _ = 1 := hmass ω
    · rw [hsupp ω w hw]
      norm_num
  have hPastBlock : Gaussian.disorderBlock m n ≤ disorderPast n := by
    rw [← Gaussian.disorderBlock_zero n]
    exact Gaussian.disorderBlock_mono (Nat.zero_le _) le_rfl
  have hmeas (w : Site) :
      Measurable[disorderPast n] (fun ω => smoothedEndpointDist β m n x ω w) := by
    exact (Polymer.measurable_smoothedEndpointDist_block β m n hmn x w).mono
      hPastBlock le_rfl
  exact integrable_futureEnergy β hnN (fun ω => smoothedEndpointDist β m n x ω)
    A hsupp hbdd hmeas


/-- The expected absolute finite-profile polymer is bounded by the conditional energy root.
Integrability follows from `integrable_randomTerminalProfilePolymer` and
`integrable_sqrt_futureEnergy`. -/
theorem setIntegral_abs_profileP2Fun_le (β : ℝ) {a b : ℕ} (hab : a ≤ b)
    (η : Disorder → Site → ℝ) (A : Finset Site) (hsupp : ∀ ω w, w ∉ A → η ω w = 0)
    (hbdd : ∃ M : ℝ, ∀ ω w, |η ω w| ≤ M)
    (hmeasη : ∀ w, Measurable[disorderPast a] (η · w))
    (G : Set Disorder) (hG : MeasurableSet[disorderPast a] G) :
    ∫ ω in G, |profileP2Fun β a b (η ω) (fun _ => 1) ω| ∂disorderLaw ≤
      ∫ ω in G, Real.sqrt (futureEnergy β a b (η ω)) ∂disorderLaw := by
  let X : Disorder → ℝ := randomFlatProfilePolymer β a b η
  let Y : Disorder → ℝ := fun ω => |X ω|
  have hXmeas : Measurable X := by
    dsimp [X]
    change Measurable (randomTerminalProfilePolymer β a b η (fun _ => 1))
    exact measurable_randomTerminalProfilePolymer β a b A η (fun _ => 1) hsupp hmeasη
  have hXint : Integrable X disorderLaw := by
    dsimp [X]
    change Integrable (randomTerminalProfilePolymer β a b η (fun _ => 1)) disorderLaw
    exact integrable_randomTerminalProfilePolymer β a b A η (fun _ => 1) hsupp hbdd
      hmeasη 1 (by intro z; simp)
  have hX2int : Integrable (fun ω => X ω ^ 2) disorderLaw := by
    dsimp [X]
    change Integrable (fun ω => randomTerminalProfilePolymer β a b η (fun _ => 1) ω ^ 2)
      disorderLaw
    exact integrable_sq_randomTerminalProfilePolymer β a b A η (fun _ => 1) hsupp hbdd
      hmeasη 1 (by intro z; simp)
  have hY2int : Integrable (fun ω => ‖Y ω‖ ^ (2 : ℝ)) disorderLaw := by
    have hEq : (fun ω => X ω ^ 2) =ᵐ[disorderLaw]
        fun ω => ‖Y ω‖ ^ (2 : ℝ) := by
      filter_upwards with ω
      simp [Y, Real.norm_eq_abs]
    exact hX2int.congr hEq
  have hJ := Integrable.norm_condExp_rpow_le (m := disorderPast a) (μ := disorderLaw)
    (f := Y) (p := 2) (by norm_num) hY2int
  have hceYnonneg : 0 ≤ᵐ[disorderLaw] disorderLaw[Y | disorderPast a] :=
    condExp_nonneg (Filter.Eventually.of_forall fun ω => abs_nonneg (X ω))
  have hnormSqEq : (fun ω => ‖Y ω‖ ^ (2 : ℝ)) =ᵐ[disorderLaw] fun ω => X ω ^ 2 :=
    Filter.Eventually.of_forall fun ω => by
      simp [Y, Real.norm_eq_abs]
  have hceNormSq := condExp_congr_ae (m := disorderPast a) hnormSqEq
  have hX2meas : Measurable (fun ω => X ω ^ 2) := (hXmeas.pow_const 2)
  have hX2ce : disorderLaw[(fun ω => X ω ^ 2) | disorderPast a] =ᵐ[disorderLaw]
      fun ω => futureEnergy β a b (η ω) := by
    have h := condExp_randomFlatProfilePolymer_sq β a b hab A η hsupp hmeasη
      hX2meas hX2int
    filter_upwards [h] with ω hω
    change disorderLaw[(fun ω => randomFlatProfilePolymer β a b η ω ^ 2) |
      disorderPast a] ω = _ at hω
    rw [hω, futureEnergy_eq_pairMoment_sum β hab (η ω) A (hsupp ω)]
  have hpoint : (fun ω => disorderLaw[Y | disorderPast a] ω) ≤ᵐ[disorderLaw]
      fun ω => Real.sqrt (futureEnergy β a b (η ω)) := by
    filter_upwards [hJ, hceYnonneg, hceNormSq, hX2ce] with ω hJω hYω hnormEq hX2ω
    apply (Real.le_sqrt hYω (futureEnergy_nonneg β a b (η ω))).2
    calc
      disorderLaw[Y | disorderPast a] ω ^ 2 =
          ‖disorderLaw[Y | disorderPast a] ω‖ ^ (2 : ℝ) := by
            rw [Real.norm_eq_abs, abs_of_nonneg hYω, Real.rpow_two]
      _ ≤ disorderLaw[(fun ω => ‖Y ω‖ ^ (2 : ℝ)) | disorderPast a] ω := hJω
      _ = futureEnergy β a b (η ω) := hnormEq.trans hX2ω
  have hsqrtInt := integrable_sqrt_futureEnergy β hab η A hsupp hbdd hmeasη
  have hYint : Integrable Y disorderLaw := by
    dsimp [Y]
    exact hXint.norm
  calc
    ∫ ω in G, |X ω| ∂disorderLaw =
        ∫ ω in G, disorderLaw[Y | disorderPast a] ω ∂disorderLaw := by
          simpa only [Y, X, randomFlatProfilePolymer] using
            (setIntegral_condExp (disorderPast_le a) hYint hG).symm
    _ ≤ ∫ ω in G, Real.sqrt (futureEnergy β a b (η ω)) ∂disorderLaw :=
      integral_mono_ae (integrable_condExp.integrableOn)
        hsqrtInt.integrableOn (ae_restrict_of_ae hpoint)

/-- A bounded terminal test bounds each diagonal terminal pair moment by the flat one. -/
private theorem terminalPairMoment_diagonal_le (β : ℝ) (n : ℕ) (z : Site)
    (f : Site → ℝ) (M : ℝ) (hM : 0 ≤ M) (hf : ∀ y, |f y| ≤ M) :
    terminalPairMoment β n z z f f ≤ M ^ 2 * pairMoment β n 0 0 := by
  have hbound := terminalProfile_secondMoment_le β 0 n z f M hM hf
  have hleft :
      (∫ ω, (∑' y, pointToPoint β 0 n z y ω * f y) ^ 2 ∂disorderLaw) =
        terminalPairMoment β n z z f f := by
    unfold terminalPairMoment
    simp only [pow_two]
  have hright :
      (∫ ω, pointToPlane β 0 n z ω ^ 2 ∂disorderLaw) = pairMoment β n z z := by
    rw [← integral_pairMoment β 0 n z z]
    congr 1
    funext ω
    rw [pow_two]
  calc
    terminalPairMoment β n z z f f =
        ∫ ω, (∑' y, pointToPoint β 0 n z y ω * f y) ^ 2 ∂disorderLaw := hleft.symm
    _ ≤ M ^ 2 * ∫ ω, pointToPlane β 0 n z ω ^ 2 ∂disorderLaw := hbound
    _ = M ^ 2 * pairMoment β n z z := by rw [hright]
    _ = M ^ 2 * pairMoment β n 0 0 := by rw [pairMoment_diagonal]

/-- The spatial weighted collision sum is controlled by the flat future energy. -/
private theorem heatEvolveFinite_terminalMoment_le (β : ℝ) (r n : ℕ)
    (A : Finset Site) (η : Site → ℝ) (f : Site → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hf : ∀ y, |f y| ≤ M) :
    (∑' z, (heatEvolveFinite r A η z) ^ 2 *
        terminalPairMoment β n z z f f) ≤
      M ^ 2 * pairMoment β n 0 0 * ∑' z, (heatEvolveFinite r A η z) ^ 2 := by
  let C : Finset Site := A.biUnion fun w => endpoints w r
  have hsupport (z : Site) (hz : z ∉ C) : heatEvolveFinite r A η z = 0 := by
    unfold heatEvolveFinite
    apply Finset.sum_eq_zero
    intro w hw
    have hzw : z ∉ endpoints w r := by
      intro hmem
      exact hz (Finset.mem_biUnion.mpr ⟨w, hw, hmem⟩)
    rw [srwKernel_eq_zero_of_not_mem r w z hzw, mul_zero]
  have hheatSqzero (z : Site) (hz : z ∉ C) :
      (heatEvolveFinite r A η z) ^ 2 = 0 := by
    rw [hsupport z hz]
    simp
  have hleftzero (z : Site) (hz : z ∉ C) :
      (heatEvolveFinite r A η z) ^ 2 * terminalPairMoment β n z z f f = 0 := by
    rw [hsupport z hz]
    simp
  have hsumle :
      (∑ z ∈ C, (heatEvolveFinite r A η z) ^ 2 *
          terminalPairMoment β n z z f f) ≤
        M ^ 2 * pairMoment β n 0 0 * ∑ z ∈ C, (heatEvolveFinite r A η z) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro z hz
    calc
      (heatEvolveFinite r A η z) ^ 2 * terminalPairMoment β n z z f f ≤
          (heatEvolveFinite r A η z) ^ 2 * (M ^ 2 * pairMoment β n 0 0) :=
            mul_le_mul_of_nonneg_left
              (terminalPairMoment_diagonal_le β n z f M hM hf)
              (sq_nonneg (heatEvolveFinite r A η z))
      _ = M ^ 2 * pairMoment β n 0 0 * (heatEvolveFinite r A η z) ^ 2 := by ring
  rw [tsum_eq_sum (s := C) hleftzero]
  calc
    _ ≤ M ^ 2 * pairMoment β n 0 0 * ∑ z ∈ C,
          (heatEvolveFinite r A η z) ^ 2 := hsumle
    _ = M ^ 2 * pairMoment β n 0 0 *
          ∑' z, (heatEvolveFinite r A η z) ^ 2 := by
            rw [tsum_eq_sum (s := C) hheatSqzero]

/-- The free-walk mean of bounded terminal data is bounded by its uniform bound. -/
private theorem terminalWalkMean_abs_le (n : ℕ) (w : Site) (f : Site → ℝ)
    (M : ℝ) (hf : ∀ z, |f z| ≤ M) : |terminalWalkMean n w f| ≤ M := by
  have h := terminalProfile_abs_le_pointToPlane 0 0 n w f M hf 0
  simpa only [terminalWalkMean, pointToPoint_zero_beta, pointToPlane_zero_beta,
    mul_one] using h

/-- The convolution in the weighted comparison is the annealed terminal-profile mean. -/
private theorem finiteProfile_terminalMean_eq_convolution (n : ℕ) (A : Finset Site)
    (η : Disorder → Site → ℝ) (f : Site → ℝ) (ω : Disorder) :
    (∑' y, (∑ w ∈ A, η ω w * srwKernel n (y - w)) * f y) =
      ∑ w ∈ A, η ω w * terminalWalkMean n w f := by
  let C : Finset Site := A.biUnion fun w => endpoints w n
  have hzero (y : Site) (hy : y ∉ C) :
      (∑ w ∈ A, η ω w * srwKernel n (y - w)) * f y = 0 := by
    rw [Finset.sum_eq_zero]
    · simp
    · intro w hw
      have hyw : y ∉ endpoints w n := by
        intro hmem
        exact hy (Finset.mem_biUnion.mpr ⟨w, hw, hmem⟩)
      rw [srwKernel_eq_zero_of_not_mem n w y hyw, mul_zero]
  have hmean (w : Site) (hw : w ∈ A) :
      terminalWalkMean n w f = ∑ y ∈ C, srwKernel n (y - w) * f y := by
    unfold terminalWalkMean
    apply tsum_eq_sum (β := Site) (L := SummationFilter.unconditional Site) (s := C)
    intro y hy
    have hyw : y ∉ endpoints w n := by
      intro hmem
      exact hy (Finset.mem_biUnion.mpr ⟨w, hw, hmem⟩)
    rw [srwKernel_eq_zero_of_not_mem n w y hyw, zero_mul]
  calc
    _ = ∑ y ∈ C, (∑ w ∈ A, η ω w * srwKernel n (y - w)) * f y :=
        tsum_eq_sum (s := C) hzero
    _ = ∑ y ∈ C, ∑ w ∈ A, η ω w * (srwKernel n (y - w) * f y) := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro w hw
      ring
    _ = ∑ w ∈ A, ∑ y ∈ C, η ω w * (srwKernel n (y - w) * f y) := Finset.sum_comm
    _ = ∑ w ∈ A, η ω w * terminalWalkMean n w f := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [← Finset.mul_sum, ← hmean w hw]

/-- The conditional variance of a terminally weighted polymer pairing is bounded by the squared terminal bound times its unweighted future energy. -/
private theorem ae_weighted_condVar_le_futureEnergy (β : ℝ) {a b : ℕ} (hab : a ≤ b)
    (η : Disorder → Site → ℝ) (A : Finset Site)
    (hsupp : ∀ ω w, w ∉ A → η ω w = 0)
    (hbdd : ∃ B : ℝ, ∀ ω w, |η ω w| ≤ B)
    (hmeasη : ∀ w, Measurable[disorderPast a] (η · w))
    (hzero : ∀ ω, ∑ w ∈ A, η ω w = 0) (f : Site → ℝ) (M : ℝ)
    (hf : ∀ z, |f z| ≤ M) :
    (fun ω => disorderLaw[(fun ξ => randomTerminalProfilePolymer β a b η f ξ ^ 2) |
        disorderPast a] ω -
      (disorderLaw[randomTerminalProfilePolymer β a b η f | disorderPast a] ω) ^ 2) ≤ᵐ[
        disorderLaw] fun ω => M ^ 2 * futureEnergy β a b (η ω) := by
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hf 0)
  have hσ : 0 ≤ sigmaSq β := by
    unfold sigmaSq
    exact sub_nonneg.mpr (Real.one_le_exp (sq_nonneg β))
  have hXmeas : Measurable (randomTerminalProfilePolymer β a b η f) :=
    measurable_randomTerminalProfilePolymer β a b A η f hsupp hmeasη
  have hXint : Integrable (randomTerminalProfilePolymer β a b η f) disorderLaw :=
    integrable_randomTerminalProfilePolymer β a b A η f hsupp hbdd hmeasη M hf
  have hX2int : Integrable
      (fun ω => randomTerminalProfilePolymer β a b η f ω ^ 2) disorderLaw :=
    integrable_sq_randomTerminalProfilePolymer β a b A η f hsupp hbdd hmeasη M hf
  have hX2meas : Measurable
      (fun ω => randomTerminalProfilePolymer β a b η f ω ^ 2) := hXmeas.pow_const 2
  have hWFC := condVar_randomTerminalProfilePolymer_eq_WFC β a b hab A η f
    hsupp hmeasη hXmeas hXint hX2meas hX2int
  have hflatMeas : Measurable (randomFlatProfilePolymer β a b η) := by
    change Measurable (randomTerminalProfilePolymer β a b η (fun _ => 1))
    exact measurable_randomTerminalProfilePolymer β a b A η (fun _ => 1) hsupp hmeasη
  have hflatInt : Integrable (randomFlatProfilePolymer β a b η) disorderLaw := by
    change Integrable (randomTerminalProfilePolymer β a b η (fun _ => 1)) disorderLaw
    exact integrable_randomTerminalProfilePolymer β a b A η (fun _ => 1) hsupp hbdd
      hmeasη 1 (by intro z; simp)
  have hflat2Int : Integrable
      (fun ω => randomFlatProfilePolymer β a b η ω ^ 2) disorderLaw := by
    change Integrable (fun ω => randomTerminalProfilePolymer β a b η (fun _ => 1) ω ^ 2)
      disorderLaw
    exact integrable_sq_randomTerminalProfilePolymer β a b A η (fun _ => 1) hsupp hbdd
      hmeasη 1 (by intro z; simp)
  have hflat2Meas : Measurable
      (fun ω => randomFlatProfilePolymer β a b η ω ^ 2) := hflatMeas.pow_const 2
  have hflatSq := condExp_randomFlatProfilePolymer_sq β a b hab A η hsupp hmeasη
    hflat2Meas hflat2Int
  have hflatSqEnergy : disorderLaw[(fun ω => randomFlatProfilePolymer β a b η ω ^ 2) |
      disorderPast a] =ᵐ[disorderLaw] fun ω => futureEnergy β a b (η ω) := by
    filter_upwards [hflatSq] with ω hω
    rw [hω, futureEnergy_eq_pairMoment_sum β hab (η ω) A (hsupp ω)]
  have hflatMean := condExp_randomFlatProfilePolymer β a b hab A η hsupp hmeasη
    hflatMeas hflatInt
  have hflatMeanZero : disorderLaw[randomFlatProfilePolymer β a b η | disorderPast a] =ᵐ[
      disorderLaw] fun _ => 0 := by
    filter_upwards [hflatMean] with ω hω
    rw [hω, hzero ω]
  have hflatVar := condVar_randomFlatProfilePolymer_eq_spatialFirstCollision β a b hab A η
    hsupp hmeasη hflatMeas hflatInt hflat2Meas hflat2Int
  have hflatEnergyWFC : (fun ω => futureEnergy β a b (η ω)) =ᵐ[disorderLaw]
      fun ω => ∑ r ∈ Finset.Icc 1 (b - a),
        (sigmaSq β * pairMoment β (b - a - r) 0 0) *
          ∑' z, (heatEvolveFinite r A (η ω) z) ^ 2 := by
    filter_upwards [hflatSqEnergy, hflatMeanZero, hflatVar] with ω hs hm hv
    calc
      futureEnergy β a b (η ω) =
          disorderLaw[(fun ξ => randomFlatProfilePolymer β a b η ξ ^ 2) |
            disorderPast a] ω := hs.symm
      _ = disorderLaw[(fun ξ => randomFlatProfilePolymer β a b η ξ ^ 2) |
            disorderPast a] ω -
            (disorderLaw[randomFlatProfilePolymer β a b η | disorderPast a] ω) ^ 2 := by
              rw [hm]
              simp
      _ = ∑ r ∈ Finset.Icc 1 (b - a),
            (sigmaSq β * pairMoment β (b - a - r) 0 0) *
              ∑' z, (heatEvolveFinite r A (η ω) z) ^ 2 := hv
  have hvarianceBound :
      (fun ω => disorderLaw[(fun ξ => randomTerminalProfilePolymer β a b η f ξ ^ 2) |
          disorderPast a] ω -
        (disorderLaw[randomTerminalProfilePolymer β a b η f | disorderPast a] ω) ^ 2) ≤ᵐ[
          disorderLaw] fun ω => M ^ 2 * futureEnergy β a b (η ω) := by
    filter_upwards [hWFC, hflatEnergyWFC] with ω hWFCω henergyω
    rw [hWFCω]
    have hsum : sigmaSq β *
          ∑ r ∈ Finset.Icc 1 (b - a), ∑' z,
            (heatEvolveFinite r A (η ω) z) ^ 2 *
              terminalPairMoment β (b - a - r) z z f f ≤
        M ^ 2 * ∑ r ∈ Finset.Icc 1 (b - a),
          (sigmaSq β * pairMoment β (b - a - r) 0 0) *
            ∑' z, (heatEvolveFinite r A (η ω) z) ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro r hr
      calc
        sigmaSq β * ∑' z,
            (heatEvolveFinite r A (η ω) z) ^ 2 *
              terminalPairMoment β (b - a - r) z z f f ≤
            sigmaSq β * (M ^ 2 * pairMoment β (b - a - r) 0 0 *
              ∑' z, (heatEvolveFinite r A (η ω) z) ^ 2) := by
                exact mul_le_mul_of_nonneg_left
                  (heatEvolveFinite_terminalMoment_le β r (b - a - r) A (η ω)
                    f M hM hf) hσ
        _ = M ^ 2 * ((sigmaSq β * pairMoment β (b - a - r) 0 0) *
              ∑' z, (heatEvolveFinite r A (η ω) z) ^ 2) := by ring
    calc
      sigmaSq β *
          ∑ r ∈ Finset.Icc 1 (b - a), ∑' z,
            (heatEvolveFinite r A (η ω) z) ^ 2 *
              terminalPairMoment β (b - a - r) z z f f ≤
          M ^ 2 * ∑ r ∈ Finset.Icc 1 (b - a),
            (sigmaSq β * pairMoment β (b - a - r) 0 0) *
              ∑' z, (heatEvolveFinite r A (η ω) z) ^ 2 := hsum
      _ = M ^ 2 * futureEnergy β a b (η ω) := by rw [← henergyω]
  exact hvarianceBound

/-- Integrability companion for `setIntegral_abs_profileP2Fun_weighted_le`. -/
theorem integrableOn_abs_profileP2Fun_weighted_le (β : ℝ) {a b : ℕ} (hab : a ≤ b)
    (η : Disorder → Site → ℝ) (A : Finset Site)
    (hsupp : ∀ ω w, w ∉ A → η ω w = 0)
    (hbdd : ∃ B : ℝ, ∀ ω w, |η ω w| ≤ B)
    (hmeasη : ∀ w, Measurable[disorderPast a] (η · w))
    (f : Site → ℝ) (M : ℝ) (hf : ∀ z, |f z| ≤ M) (G : Set Disorder) :
    IntegrableOn (fun ω => |profileP2Fun β a b (η ω) f ω|) G disorderLaw ∧
      IntegrableOn (fun ω =>
        |∑' y, (∑ w ∈ A, η ω w * srwKernel (b - a) (y - w)) * f y| +
          M * Real.sqrt (futureEnergy β a b (η ω))) G disorderLaw := by
  have hprofile : Integrable
      (fun ω => profileP2Fun β a b (η ω) f ω) disorderLaw := by
    change Integrable (randomTerminalProfilePolymer β a b η f) disorderLaw
    exact integrable_randomTerminalProfilePolymer β a b A η f hsupp hbdd hmeasη M hf
  have hconv : Integrable (fun ω =>
      ∑' y, (∑ w ∈ A, η ω w * srwKernel (b - a) (y - w)) * f y) disorderLaw := by
    let B : ℝ := Classical.choose hbdd
    have hB : ∀ ω w, |η ω w| ≤ B := Classical.choose_spec hbdd
    have hB0 : 0 ≤ B := (abs_nonneg (η 0 0)).trans (hB 0 0)
    have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hf 0)
    let m : Disorder → ℝ := fun ω =>
      ∑ w ∈ A, η ω w * terminalWalkMean (b - a) w f
    have hmPast : Measurable[disorderPast a] m := by
      dsimp [m]
      exact Finset.measurable_sum _ fun w hw => (hmeasη w).mul_const _
    have hmMeas : Measurable m := hmPast.mono (disorderPast_le a) le_rfl
    have hmeanBound : ∀ ω, |m ω| ≤ (A.card : ℝ) * (B * M) := by
      intro ω
      calc
        |m ω| ≤ ∑ w ∈ A, |η ω w * terminalWalkMean (b - a) w f| := by
          dsimp [m]
          exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ w ∈ A, B * M := Finset.sum_le_sum fun w hw => by
          rw [abs_mul]
          exact mul_le_mul (hB ω w) (terminalWalkMean_abs_le (b - a) w f M hf)
            (abs_nonneg _) hB0
        _ = (A.card : ℝ) * (B * M) := by simp
    let K : ℝ := (A.card : ℝ) * (B * M)
    have hK : 0 ≤ K := mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hB0 hM)
    have hmInt : Integrable m disorderLaw := by
      refine (integrable_const K).mono' hmMeas.aestronglyMeasurable ?_
      filter_upwards with ω
      simpa only [Real.norm_eq_abs, abs_of_nonneg hK, K] using hmeanBound ω
    have hconvEq : (fun ω =>
        ∑' y, (∑ w ∈ A, η ω w * srwKernel (b - a) (y - w)) * f y) = m := by
      funext ω
      exact finiteProfile_terminalMean_eq_convolution (b - a) A η f ω
    simpa only [hconvEq.symm] using hmInt
  have hroot := integrable_sqrt_futureEnergy β hab η A hsupp hbdd hmeasη
  have hbound : Integrable (fun ω =>
      |∑' y, (∑ w ∈ A, η ω w * srwKernel (b - a) (y - w)) * f y| +
        M * Real.sqrt (futureEnergy β a b (η ω))) disorderLaw := by
    have hconvAbs : Integrable (fun ω =>
        |∑' y, (∑ w ∈ A, η ω w * srwKernel (b - a) (y - w)) * f y|) disorderLaw := by
      simpa only [Real.norm_eq_abs] using hconv.norm
    exact hconvAbs.add (hroot.const_mul M)
  exact ⟨hprofile.norm.integrableOn, hbound.integrableOn⟩

/-- The weighted absolute profile is bounded by its annealed drift and its future energy.
Integrability of both integrands follows from `integrableOn_abs_profileP2Fun_weighted_le`. -/
theorem setIntegral_abs_profileP2Fun_weighted_le (β : ℝ) {a b : ℕ} (hab : a ≤ b)
    (η : Disorder → Site → ℝ) (A : Finset Site)
    (hsupp : ∀ ω w, w ∉ A → η ω w = 0)
    (hbdd : ∃ B : ℝ, ∀ ω w, |η ω w| ≤ B)
    (hmeasη : ∀ w, Measurable[disorderPast a] (η · w))
    (hzero : ∀ ω, ∑ w ∈ A, η ω w = 0) (f : Site → ℝ) (M : ℝ)
    (hf : ∀ z, |f z| ≤ M)
    (G : Set Disorder) (hG : MeasurableSet[disorderPast a] G) :
    ∫ ω in G, |profileP2Fun β a b (η ω) f ω| ∂disorderLaw ≤
      ∫ ω in G,
        (|∑' y, (∑ w ∈ A, η ω w * srwKernel (b - a) (y - w)) * f y| +
          M * Real.sqrt (futureEnergy β a b (η ω))) ∂disorderLaw := by
  let B : ℝ := Classical.choose hbdd
  have hB : ∀ ω w, |η ω w| ≤ B := Classical.choose_spec hbdd
  have hB0 : 0 ≤ B := (abs_nonneg (η 0 0)).trans (hB 0 0)
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hf 0)
  let X : Disorder → ℝ := randomTerminalProfilePolymer β a b η f
  let m : Disorder → ℝ := fun ω => ∑ w ∈ A, η ω w * terminalWalkMean (b - a) w f
  let D : Disorder → ℝ := fun ω => X ω - m ω
  let Y : Disorder → ℝ := fun ω => |D ω|
  have hXmeas : Measurable X := by
    dsimp [X]
    exact measurable_randomTerminalProfilePolymer β a b A η f hsupp hmeasη
  have hXint : Integrable X disorderLaw := by
    dsimp [X]
    exact integrable_randomTerminalProfilePolymer β a b A η f hsupp hbdd hmeasη M hf
  have hX2int : Integrable (fun ω => X ω ^ 2) disorderLaw := by
    dsimp [X]
    exact integrable_sq_randomTerminalProfilePolymer β a b A η f hsupp hbdd hmeasη M hf
  have hmPast : Measurable[disorderPast a] m := by
    dsimp [m]
    exact Finset.measurable_sum _ fun w hw => (hmeasη w).mul_const _
  have hmMeas : Measurable m := hmPast.mono (disorderPast_le a) le_rfl
  have hmeanBound : ∀ ω, |m ω| ≤ (A.card : ℝ) * (B * M) := by
    intro ω
    calc
      |m ω| ≤ ∑ w ∈ A, |η ω w * terminalWalkMean (b - a) w f| := by
        dsimp [m]
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ w ∈ A, B * M := Finset.sum_le_sum fun w hw => by
        rw [abs_mul]
        exact mul_le_mul (hB ω w) (terminalWalkMean_abs_le (b - a) w f M hf)
          (abs_nonneg _) hB0
      _ = (A.card : ℝ) * (B * M) := by simp
  let K : ℝ := (A.card : ℝ) * (B * M)
  have hK : 0 ≤ K := mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hB0 hM)
  have hmInt : Integrable m disorderLaw := by
    refine (integrable_const K).mono' hmMeas.aestronglyMeasurable ?_
    filter_upwards with ω
    simpa only [Real.norm_eq_abs, abs_of_nonneg hK, K] using hmeanBound ω
  have hm2Meas : Measurable (fun ω => m ω ^ 2) := hmMeas.pow_const 2
  have hm2Int : Integrable (fun ω => m ω ^ 2) disorderLaw := by
    refine (integrable_const (K ^ 2)).mono' hm2Meas.aestronglyMeasurable ?_
    filter_upwards with ω
    have hle : |m ω| ≤ K := by simpa only [K] using hmeanBound ω
    have hsq := mul_le_mul hle hle (abs_nonneg (m ω)) hK
    have hsq' : m ω ^ 2 ≤ K ^ 2 := by
      nlinarith [hsq, sq_abs (m ω), sq_abs K]
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (m ω)),
      abs_of_nonneg (sq_nonneg K)] using hsq'
  have hMXmeas : Measurable (fun ω => m ω * X ω) := hmMeas.mul hXmeas
  have hMXint : Integrable (fun ω => m ω * X ω) disorderLaw := by
    refine (hXint.norm.const_mul K).mono' hMXmeas.aestronglyMeasurable ?_
    filter_upwards with ω
    have hle : |m ω| ≤ K := by simpa only [K] using hmeanBound ω
    have hmul := mul_le_mul_of_nonneg_right hle (abs_nonneg (X ω))
    simpa only [Real.norm_eq_abs, abs_mul] using hmul
  have hDmeas : Measurable D := by
    dsimp [D]
    exact hXmeas.sub hmMeas
  have hDint : Integrable D disorderLaw := by
    dsimp [D]
    exact hXint.sub hmInt
  have hD2Meas : Measurable (fun ω => D ω ^ 2) := hDmeas.pow_const 2
  have hD2Int : Integrable (fun ω => D ω ^ 2) disorderLaw := by
    have hmajor : Integrable (fun ω => 2 * X ω ^ 2 + 2 * m ω ^ 2) disorderLaw :=
      (hX2int.const_mul 2).add (hm2Int.const_mul 2)
    refine hmajor.mono' hD2Meas.aestronglyMeasurable ?_
    filter_upwards with ω
    have hineq : D ω ^ 2 ≤ 2 * X ω ^ 2 + 2 * m ω ^ 2 := by
      change (X ω - m ω) ^ 2 ≤ 2 * X ω ^ 2 + 2 * m ω ^ 2
      nlinarith [sq_nonneg (X ω + m ω)]
    have hmaj : 0 ≤ 2 * X ω ^ 2 + 2 * m ω ^ 2 := by positivity
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (D ω)),
      abs_of_nonneg hmaj] using hineq
  have h2MXint : Integrable (fun ω => 2 * (m ω * X ω)) disorderLaw := hMXint.const_mul 2
  have hsubInt : Integrable (fun ω => X ω ^ 2 - 2 * (m ω * X ω)) disorderLaw :=
    hX2int.sub h2MXint
  have hD2Expand : (fun ω => D ω ^ 2) =ᵐ[disorderLaw]
      fun ω => X ω ^ 2 - 2 * (m ω * X ω) + m ω ^ 2 := by
    filter_upwards with ω
    dsimp [D]
    ring
  have hD2CEExpand := condExp_congr_ae (m := disorderPast a) hD2Expand
  have hCEadd := condExp_add hsubInt hm2Int (disorderPast a)
  have hCEsub := condExp_sub hX2int h2MXint (disorderPast a)
  have hCEsmul := condExp_smul (μ := disorderLaw)
    (m₀ := (inferInstance : MeasurableSpace Disorder))
    (2 : ℝ) (fun ω => m ω * X ω) (disorderPast a)
  have hCEpull := condExp_mul_of_aestronglyMeasurable_left
    (m := disorderPast a) hmPast.aestronglyMeasurable hMXint hXint
  have hm2Past : Measurable[disorderPast a] (fun ω => m ω ^ 2) := hmPast.pow_const 2
  have hCEm2 := condExp_of_aestronglyMeasurable'
    (disorderPast_le a) hm2Past.aestronglyMeasurable hm2Int
  have hmean := condExp_randomTerminalProfilePolymer β a b hab A η f hsupp hmeasη
    hXmeas hXint
  have hD2CEvar : disorderLaw[(fun ω => D ω ^ 2) | disorderPast a] =ᵐ[disorderLaw]
      fun ω => disorderLaw[(fun ξ => X ξ ^ 2) | disorderPast a] ω -
        (disorderLaw[X | disorderPast a] ω) ^ 2 := by
    filter_upwards [hD2CEExpand, hCEadd, hCEsub, hCEsmul, hCEpull, hCEm2, hmean]
      with ω hExpand hAdd hSub hSmul hPull hM2 hMean
    have hSubω :
        disorderLaw[(fun ξ => X ξ ^ 2 - 2 * (m ξ * X ξ)) | disorderPast a] ω =
          disorderLaw[(fun ξ => X ξ ^ 2) | disorderPast a] ω -
            disorderLaw[(fun ξ => 2 * (m ξ * X ξ)) | disorderPast a] ω := by
      change disorderLaw[((fun ξ => X ξ ^ 2) - fun ξ => 2 * (m ξ * X ξ)) |
        disorderPast a] ω = _
      exact hSub
    have hSmulω :
        disorderLaw[(fun ξ => 2 * (m ξ * X ξ)) | disorderPast a] ω =
          2 * disorderLaw[(fun ξ => m ξ * X ξ) | disorderPast a] ω := by
      have hfun : (fun ξ => 2 * (m ξ * X ξ)) =
          (2 : ℝ) • (fun ξ => m ξ * X ξ) := by
        funext ξ
        simp
      rw [hfun]
      simpa only [Pi.smul_apply, smul_eq_mul] using hSmul
    have hPullω : disorderLaw[(fun ξ => m ξ * X ξ) | disorderPast a] ω =
        m ω * disorderLaw[X | disorderPast a] ω := by
      have hfun : (fun ξ => m ξ * X ξ) = m * X := by
        funext ξ
        rfl
      rw [hfun]
      simpa only [Pi.mul_apply] using hPull
    calc
      disorderLaw[(fun ξ => D ξ ^ 2) | disorderPast a] ω =
          disorderLaw[(fun ξ => X ξ ^ 2 - 2 * (m ξ * X ξ) + m ξ ^ 2) |
            disorderPast a] ω := hExpand
      _ = disorderLaw[(fun ξ => X ξ ^ 2 - 2 * (m ξ * X ξ)) | disorderPast a] ω +
            disorderLaw[(fun ξ => m ξ ^ 2) | disorderPast a] ω := hAdd
      _ = (disorderLaw[(fun ξ => X ξ ^ 2) | disorderPast a] ω -
            disorderLaw[(fun ξ => 2 * (m ξ * X ξ)) | disorderPast a] ω) +
            disorderLaw[(fun ξ => m ξ ^ 2) | disorderPast a] ω :=
              congrArg (fun z : ℝ => z + disorderLaw[(fun ξ => m ξ ^ 2) |
                disorderPast a] ω) hSubω
      _ = (disorderLaw[(fun ξ => X ξ ^ 2) | disorderPast a] ω -
            2 * disorderLaw[(fun ξ => m ξ * X ξ) | disorderPast a] ω) +
            disorderLaw[(fun ξ => m ξ ^ 2) | disorderPast a] ω :=
              congrArg (fun z : ℝ =>
                (disorderLaw[(fun ξ => X ξ ^ 2) | disorderPast a] ω - z) +
                  disorderLaw[(fun ξ => m ξ ^ 2) | disorderPast a] ω) hSmulω
      _ = (disorderLaw[(fun ξ => X ξ ^ 2) | disorderPast a] ω -
            2 * (m ω * disorderLaw[X | disorderPast a] ω)) + m ω ^ 2 := by
              rw [hM2]
              exact congrArg (fun z : ℝ =>
                (disorderLaw[(fun ξ => X ξ ^ 2) | disorderPast a] ω - 2 * z) +
                  m ω ^ 2) hPullω
      _ = disorderLaw[(fun ξ => X ξ ^ 2) | disorderPast a] ω -
            (disorderLaw[X | disorderPast a] ω) ^ 2 := by
              rw [hMean]
              dsimp [m, terminalWalkMean]
              ring
  have hvarBound := ae_weighted_condVar_le_futureEnergy β hab η A hsupp hbdd hmeasη
    hzero f M hf
  have hD2CEbound : disorderLaw[(fun ω => D ω ^ 2) | disorderPast a] ≤ᵐ[disorderLaw]
      fun ω => M ^ 2 * futureEnergy β a b (η ω) := by
    filter_upwards [hD2CEvar, hvarBound] with ω hEq hBound
    rw [hEq]
    exact hBound
  have hY2Int : Integrable (fun ω => ‖Y ω‖ ^ (2 : ℝ)) disorderLaw := by
    have hEq : (fun ω => D ω ^ 2) =ᵐ[disorderLaw]
        fun ω => ‖Y ω‖ ^ (2 : ℝ) := by
      filter_upwards with ω
      simp [Y, Real.norm_eq_abs]
    exact hD2Int.congr hEq
  have hJ := Integrable.norm_condExp_rpow_le (m := disorderPast a) (μ := disorderLaw)
    (f := Y) (p := 2) (by norm_num) hY2Int
  have hYCE_nonneg : 0 ≤ᵐ[disorderLaw] disorderLaw[Y | disorderPast a] :=
    condExp_nonneg (Filter.Eventually.of_forall fun ω => abs_nonneg (D ω))
  have hD2CE_nonneg : 0 ≤ᵐ[disorderLaw]
      disorderLaw[(fun ω => D ω ^ 2) | disorderPast a] :=
    condExp_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg (D ω))
  have hYnormSqEq : (fun ω => ‖Y ω‖ ^ (2 : ℝ)) =ᵐ[disorderLaw]
      fun ω => D ω ^ 2 := by
    filter_upwards with ω
    simp [Y, Real.norm_eq_abs]
  have hCEYnormSq := condExp_congr_ae (m := disorderPast a) hYnormSqEq
  have hCEY_le_sqrt_D2 : (fun ω => disorderLaw[Y | disorderPast a] ω) ≤ᵐ[disorderLaw]
      fun ω => Real.sqrt (disorderLaw[(fun ξ => D ξ ^ 2) | disorderPast a] ω) := by
    filter_upwards [hJ, hYCE_nonneg, hD2CE_nonneg, hCEYnormSq] with ω hJω hYω hD2ω hEq
    apply (Real.le_sqrt hYω hD2ω).2
    calc
      disorderLaw[Y | disorderPast a] ω ^ 2 =
          ‖disorderLaw[Y | disorderPast a] ω‖ ^ (2 : ℝ) := by
            rw [Real.norm_eq_abs, abs_of_nonneg hYω, Real.rpow_two]
      _ ≤ disorderLaw[(fun ξ => ‖Y ξ‖ ^ (2 : ℝ)) | disorderPast a] ω := hJω
      _ = disorderLaw[(fun ξ => D ξ ^ 2) | disorderPast a] ω := hEq
  have hCEY_le : (fun ω => disorderLaw[Y | disorderPast a] ω) ≤ᵐ[disorderLaw]
      fun ω => M * Real.sqrt (futureEnergy β a b (η ω)) := by
    filter_upwards [hCEY_le_sqrt_D2, hD2CEbound] with ω hJω hBound
    calc
      disorderLaw[Y | disorderPast a] ω ≤
          Real.sqrt (disorderLaw[(fun ξ => D ξ ^ 2) | disorderPast a] ω) := hJω
      _ ≤ Real.sqrt (M ^ 2 * futureEnergy β a b (η ω)) :=
        Real.sqrt_le_sqrt hBound
      _ = M * Real.sqrt (futureEnergy β a b (η ω)) := by
        rw [Real.sqrt_mul (sq_nonneg M), show M ^ 2 = M * M by ring,
          Real.sqrt_mul_self_eq_abs, abs_of_nonneg hM]
  have hYint : Integrable Y disorderLaw := by
    dsimp [Y, D]
    exact hXint.sub hmInt |>.norm
  have hsqrtInt := integrable_sqrt_futureEnergy β hab η A hsupp hbdd hmeasη
  have hMrootInt : Integrable
      (fun ω => M * Real.sqrt (futureEnergy β a b (η ω))) disorderLaw :=
    hsqrtInt.const_mul M
  have hmAbsInt : Integrable (fun ω => |m ω|) disorderLaw := hmInt.norm
  have hYCEint : Integrable (disorderLaw[Y | disorderPast a]) disorderLaw :=
    integrable_condExp
  have hconv : (fun ω => ∑' y,
      (∑ w ∈ A, η ω w * srwKernel (b - a) (y - w)) * f y) = m := by
    funext ω
    exact finiteProfile_terminalMean_eq_convolution (b - a) A η f ω
  have hconvAbsInt : Integrable (fun ω =>
      |∑' y, (∑ w ∈ A, η ω w * srwKernel (b - a) (y - w)) * f y|) disorderLaw := by
    simpa only [hconv.symm] using hmAbsInt
  have htriangle : ∀ ω, |X ω| ≤ |m ω| + |D ω| := by
    intro ω
    calc
      |X ω| = |(X ω - m ω) + m ω| := by congr 1; ring
      _ ≤ |X ω - m ω| + |m ω| := abs_add_le _ _
      _ = |m ω| + |D ω| := by rw [show X ω - m ω = D ω by rfl]; ring
  have htriInt : Integrable (fun ω => |m ω| + |D ω|) disorderLaw :=
    hmAbsInt.add hYint
  have hsqrtIntSet : IntegrableOn
      (fun ω => Real.sqrt (futureEnergy β a b (η ω))) G disorderLaw := hsqrtInt.integrableOn
  calc
    ∫ ω in G, |profileP2Fun β a b (η ω) f ω| ∂disorderLaw ≤
        ∫ ω in G, (|m ω| + |D ω|) ∂disorderLaw := by
          apply integral_mono_ae hXint.norm.integrableOn htriInt.integrableOn
          exact ae_restrict_of_ae (Filter.Eventually.of_forall htriangle)
    _ = (∫ ω in G, |m ω| ∂disorderLaw) +
          ∫ ω in G, |D ω| ∂disorderLaw := by
            rw [integral_add hmAbsInt.integrableOn hYint.integrableOn]
    _ ≤ (∫ ω in G, |m ω| ∂disorderLaw) +
          M * ∫ ω in G, Real.sqrt (futureEnergy β a b (η ω)) ∂disorderLaw := by
            gcongr
            calc
              ∫ ω in G, |D ω| ∂disorderLaw =
                  ∫ ω in G, disorderLaw[Y | disorderPast a] ω ∂disorderLaw := by
                    simpa only [Y, D] using
                      (setIntegral_condExp (disorderPast_le a) hYint hG).symm
              _ ≤ ∫ ω in G, M * Real.sqrt (futureEnergy β a b (η ω)) ∂disorderLaw :=
                integral_mono_ae hYCEint.integrableOn hMrootInt.integrableOn
                  (ae_restrict_of_ae hCEY_le)
              _ = M * ∫ ω in G, Real.sqrt (futureEnergy β a b (η ω)) ∂disorderLaw :=
                integral_const_mul _ _
    _ = ∫ ω in G,
          (|∑' y, (∑ w ∈ A, η ω w * srwKernel (b - a) (y - w)) * f y| +
            M * Real.sqrt (futureEnergy β a b (η ω))) ∂disorderLaw := by
          calc
            _ = (∫ ω in G,
                  |∑' y, (∑ w ∈ A, η ω w * srwKernel (b - a) (y - w)) * f y|
                    ∂disorderLaw) + M *
                  ∫ ω in G, Real.sqrt (futureEnergy β a b (η ω)) ∂disorderLaw := by
                    congr 1
                    exact setIntegral_congr_ae ((disorderPast_le a) G hG)
                      (Filter.Eventually.of_forall fun ω _ =>
                        congrArg abs (congrFun hconv ω).symm)
            _ = (∫ ω in G,
                  |∑' y, (∑ w ∈ A, η ω w * srwKernel (b - a) (y - w)) * f y|
                    ∂disorderLaw) +
                  ∫ ω in G, M * Real.sqrt (futureEnergy β a b (η ω)) ∂disorderLaw := by
                    rw [← integral_const_mul]
            _ = _ := by
              rw [integral_add hconvAbsInt.integrableOn hMrootInt.integrableOn]

/-- Positive terminal weights with bounded logarithm change a normalized profile's logarithm
by at most the same bound. -/
theorem abs_log_profileP2Fun_sub_le (β : ℝ) (a b : ℕ) (ν : Site → ℝ) (A : Finset Site)
    (hνA : ∀ w ∉ A, ν w = 0) (hν0 : ∀ w, 0 ≤ ν w) (hν1 : ∑ w ∈ A, ν w = 1)
    (f : Site → ℝ) (L : ℝ) (hf : ∀ z, 0 < f z ∧ |Real.log (f z)| ≤ L) (ω : Disorder) :
    |Real.log (profileP2Fun β a b ν f ω) -
      Real.log (profileP2Fun β a b ν (fun _ => 1) ω)| ≤ L := by
  let terminal (g : Site → ℝ) (w : Site) : ℝ :=
    ∑' z, pointToPoint β a (b - a) w z ω * g z
  have hflo (z : Site) : Real.exp (-L) ≤ f z := by
    have hlog := (abs_le.mp (hf z).2).1
    calc
      Real.exp (-L) ≤ Real.exp (Real.log (f z)) := Real.exp_le_exp.mpr hlog
      _ = f z := Real.exp_log (hf z).1
  have hfhi (z : Site) : f z ≤ Real.exp L := by
    have hlog := (abs_le.mp (hf z).2).2
    calc
      f z = Real.exp (Real.log (f z)) := (Real.exp_log (hf z).1).symm
      _ ≤ Real.exp L := Real.exp_le_exp.mpr hlog
  have hplane (w : Site) : pointToPlane β a (b - a) w ω =
      ∑ z ∈ endpoints w (b - a), pointToPoint β a (b - a) w z ω := by
    calc
      pointToPlane β a (b - a) w ω = ∑' z, pointToPoint β a (b - a) w z ω :=
        (tsum_pointToPoint β a (b - a) w ω).symm
      _ = ∑ z ∈ endpoints w (b - a), pointToPoint β a (b - a) w z ω := by
        simpa only [mul_one] using
          (tsum_pointToPoint_mul_eq_sum β a (b - a) w (fun _ => 1) ω)
  have hterminalSum (g : Site → ℝ) (w : Site) :
      terminal g w = ∑ z ∈ endpoints w (b - a),
        pointToPoint β a (b - a) w z ω * g z := by
    dsimp [terminal]
    exact tsum_pointToPoint_mul_eq_sum β a (b - a) w g ω
  have hterminalLo (w : Site) :
      Real.exp (-L) * pointToPlane β a (b - a) w ω ≤ terminal f w := by
    rw [hterminalSum, hplane, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro z hz
    calc
      Real.exp (-L) * pointToPoint β a (b - a) w z ω ≤
          f z * pointToPoint β a (b - a) w z ω :=
        mul_le_mul_of_nonneg_right (hflo z)
          (pointToPoint_nonneg β a (b - a) w z ω)
      _ = pointToPoint β a (b - a) w z ω * f z := by ring
  have hterminalHi (w : Site) :
      terminal f w ≤ Real.exp L * pointToPlane β a (b - a) w ω := by
    rw [hterminalSum, hplane, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro z hz
    calc
      pointToPoint β a (b - a) w z ω * f z =
          f z * pointToPoint β a (b - a) w z ω := by ring
      _ ≤ Real.exp L * pointToPoint β a (b - a) w z ω :=
        mul_le_mul_of_nonneg_right (hfhi z)
          (pointToPoint_nonneg β a (b - a) w z ω)
  have hflatRep : profileP2Fun β a b ν (fun _ => 1) ω =
      ∑ w ∈ A, ν w * pointToPlane β a (b - a) w ω := by
    rw [profileP2Fun_eq_sum β a b ν (fun _ => 1) A hνA]
    simp only [mul_one, tsum_pointToPoint]
  have hweightedRep : profileP2Fun β a b ν f ω =
      ∑ w ∈ A, ν w * terminal f w := by
    rw [profileP2Fun_eq_sum β a b ν f A hνA]
  have hflatPos : 0 < profileP2Fun β a b ν (fun _ => 1) ω := by
    have hνpos : ∃ w ∈ A, 0 < ν w := by
      have hsum : 0 < ∑ w ∈ A, ν w := by rw [hν1]; norm_num
      exact (Finset.sum_pos_iff_of_nonneg (fun w hw => hν0 w)).mp hsum
    obtain ⟨w, hwA, hw⟩ := hνpos
    rw [hflatRep]
    apply (Finset.sum_pos_iff_of_nonneg (fun z hz =>
      mul_nonneg (hν0 z) (pointToPlane_pos β a (b - a) z ω).le)).2
    exact ⟨w, hwA, mul_pos hw (pointToPlane_pos β a (b - a) w ω)⟩
  have hscaleLo : Real.exp (-L) *
      (∑ w ∈ A, ν w * pointToPlane β a (b - a) w ω) =
        ∑ w ∈ A, ν w * (Real.exp (-L) * pointToPlane β a (b - a) w ω) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w hw
    ring
  have hscaleHi :
      (∑ w ∈ A, ν w * (Real.exp L * pointToPlane β a (b - a) w ω)) =
        Real.exp L * (∑ w ∈ A, ν w * pointToPlane β a (b - a) w ω) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w hw
    ring
  have hprofileLo :
      Real.exp (-L) * profileP2Fun β a b ν (fun _ => 1) ω ≤
        profileP2Fun β a b ν f ω := by
    rw [hflatRep, hweightedRep, hscaleLo]
    exact Finset.sum_le_sum fun w hw =>
      mul_le_mul_of_nonneg_left (hterminalLo w) (hν0 w)
  have hprofileHi :
      profileP2Fun β a b ν f ω ≤
        Real.exp L * profileP2Fun β a b ν (fun _ => 1) ω := by
    rw [hflatRep, hweightedRep, ← hscaleHi]
    exact Finset.sum_le_sum fun w hw =>
      mul_le_mul_of_nonneg_left (hterminalHi w) (hν0 w)
  have hfprofile : 0 < profileP2Fun β a b ν f ω :=
    lt_of_lt_of_le (mul_pos (Real.exp_pos _) hflatPos) hprofileLo
  have hlogLo := Real.log_le_log (mul_pos (Real.exp_pos _) hflatPos) hprofileLo
  have hlogHi := Real.log_le_log hfprofile hprofileHi
  rw [Real.log_mul (Real.exp_pos _).ne' hflatPos.ne', Real.log_exp] at hlogLo
  rw [Real.log_mul (Real.exp_pos _).ne' hflatPos.ne', Real.log_exp] at hlogHi
  rw [abs_le]
  constructor <;> linarith

end Critical2DKPZ.FutureProfiles

end
