/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.DiscrepancyMoments
public import Critical2DKPZ.Collision.ConditionalFlat
public import Critical2DKPZ.FutureProfiles.HelperEndpointProfiles
public import Critical2DKPZ.FutureProfiles.FreezingPast
public import Critical2DKPZ.FutureProfiles.SplitBoundInputs
public import Critical2DKPZ.FutureProfiles.WalkBounds
import Mathlib.Tactic

/-! # Future-energy bounds for open correctors -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators

namespace Critical2DKPZ.FutureProfiles

open Critical2DKPZ.Blocks Critical2DKPZ.Collision Critical2DKPZ.Polymer

private theorem disorderPast_le_local (a : ℕ) :
    disorderPast a ≤ (inferInstance : MeasurableSpace Disorder) := by
  rw [← Gaussian.disorderBlock_zero a]
  exact Gaussian.disorderBlock_le 0 a

private theorem measurable_discrepancyString_block_to_last (β : ℝ) (t : ℕ → ℕ)
    (ht : Monotone t) (u k v : ℕ) (huk : u + k - 1 ≤ v) (x y : Site) :
    Measurable[Gaussian.disorderBlock (t (u - 1)) (t v)]
      (fun ω => discrepancyString β t u k x y ω) := by
  let : MeasurableSpace Disorder := Gaussian.disorderBlock (t (u - 1)) (t v)
  induction k generalizing x y with
  | zero => exact measurable_const
  | succ k ih =>
      have huk' : u + k - 1 ≤ v := by omega
      have hstart : t (u - 1) ≤ t (u + k - 1) := ht (by omega)
      have htime : u + k ≤ v := by omega
      have hend : t (u + k) ≤ t v := ht htime
      have hsub := Gaussian.disorderBlock_mono hstart hend
      have hlast (z : Site) :
          Measurable[Gaussian.disorderBlock (t (u - 1)) (t v)]
            (fun ω => blockDiscrepancy β t (u + k) z y ω) := by
        exact (measurable_blockDiscrepancy β t (u + k) (ht (by omega)) z y).mono
          hsub le_rfl
      change Measurable[Gaussian.disorderBlock (t (u - 1)) (t v)]
        (fun ω => ∑' z, discrepancyString β t u k x z ω *
          blockDiscrepancy β t (u + k) z y ω)
      exact Measurable.tsum fun z => (ih huk' x z).mul (hlast z)

/-- An open corrector through block `s` is measurable with respect to the disorder through `t s`. -/
theorem measurable_openCorrector_on_past (β : ℝ) (t : ℕ → ℕ) (ht : Monotone t)
    (u s : ℕ) (hu : 1 ≤ u) (hus : u ≤ s) (y : Site) :
    Measurable[disorderPast (t s)] (fun ω => openCorrector β t u s ω y) := by
  have hnumMeas : Measurable[disorderPast (t s)]
      (fun ω => openCorrectorNumerator β t u s ω y) := by
    let : MeasurableSpace Disorder := disorderPast (t s)
    have hstr (x : Site) : Measurable[disorderPast (t s)]
        (fun ω => discrepancyString β t u (s + 1 - u) x y ω) := by
      have h := measurable_discrepancyString_block_to_last β t ht u
        (s + 1 - u) s (by omega) x y
      exact h.mono (Gaussian.disorderBlock_mono (Nat.zero_le _) le_rfl) le_rfl
    change Measurable[disorderPast (t s)] (fun ω =>
      ∑' x, srwKernel (t (u - 1)) x * discrepancyString β t u (s + 1 - u) x y ω)
    exact Measurable.tsum fun x => (hstr x).const_mul _
  have hdenMeas : Measurable[disorderPast (t s)] (fun ω =>
      ∏ i ∈ Finset.Icc u s, blockMass β t i ω) := by
    let : MeasurableSpace Disorder := disorderPast (t s)
    apply Finset.measurable_prod
    intro i hi
    have hti : t i ≤ t s := ht (Finset.mem_Icc.mp hi).2
    exact (measurable_blockMass β t i).mono
      (Gaussian.disorderBlock_mono (Nat.zero_le _) hti) le_rfl
  unfold openCorrector
  exact hnumMeas.div hdenMeas

private theorem setIntegral_profileP2Fun_sq_eq_of_integrable (β : ℝ) {a b : ℕ}
    (hab : a ≤ b) (η : Disorder → Site → ℝ) (A : Finset Site)
    (hsupp : ∀ ω w, w ∉ A → η ω w = 0)
    (hmeasη : ∀ w, Measurable[disorderPast a] (η · w))
    (hXmeas : Measurable (fun ω => randomFlatProfilePolymer β a b η ω ^ 2))
    (hXint : Integrable (fun ω => randomFlatProfilePolymer β a b η ω ^ 2) disorderLaw)
    (G : Set Disorder) (hG : MeasurableSet[disorderPast a] G) :
    ∫ ω in G, profileP2Fun β a b (η ω) (fun _ => 1) ω ^ 2 ∂disorderLaw =
      ∫ ω in G, futureEnergy β a b (η ω) ∂disorderLaw := by
  have hCE := condExp_randomFlatProfilePolymer_sq β a b hab A η hsupp hmeasη
    hXmeas hXint
  have hCEeq : disorderLaw[(fun ω => randomFlatProfilePolymer β a b η ω ^ 2) |
      disorderPast a] =ᵐ[disorderLaw] fun ω => futureEnergy β a b (η ω) := by
    filter_upwards [hCE] with ω hω
    rw [hω, futureEnergy_eq_pairMoment_sum β hab (η ω) A (hsupp ω)]
  calc
    ∫ ω in G, profileP2Fun β a b (η ω) (fun _ => 1) ω ^ 2 ∂disorderLaw =
        ∫ ω in G, disorderLaw[(fun ω => randomFlatProfilePolymer β a b η ω ^ 2) |
          disorderPast a] ω ∂disorderLaw := by
            simpa only [randomFlatProfilePolymer] using
              (setIntegral_condExp (disorderPast_le_local a) hXint hG).symm
    _ = ∫ ω in G, futureEnergy β a b (η ω) ∂disorderLaw :=
      setIntegral_congr_ae ((disorderPast_le_local a) G hG)
        (hCEeq.mono fun _ h _ => h)

/-- An integrable squared flat-profile polymer has an integrable conditional future energy. -/
theorem integrable_futureEnergy_of_randomFlatProfilePolymer_sq (β : ℝ) {a b : ℕ}
    (hab : a ≤ b) (η : Disorder → Site → ℝ) (A : Finset Site)
    (hsupp : ∀ ω w, w ∉ A → η ω w = 0)
    (hmeasη : ∀ w, Measurable[disorderPast a] (η · w))
    (hXmeas : Measurable (fun ω => randomFlatProfilePolymer β a b η ω ^ 2))
    (hXint : Integrable (fun ω => randomFlatProfilePolymer β a b η ω ^ 2) disorderLaw) :
    Integrable (fun ω => futureEnergy β a b (η ω)) disorderLaw := by
  have hCE := condExp_randomFlatProfilePolymer_sq β a b hab A η hsupp hmeasη
    hXmeas hXint
  have hCEeq : disorderLaw[(fun ω => randomFlatProfilePolymer β a b η ω ^ 2) |
      disorderPast a] =ᵐ[disorderLaw] fun ω => futureEnergy β a b (η ω) := by
    filter_upwards [hCE] with ω hω
    rw [hω, futureEnergy_eq_pairMoment_sum β hab (η ω) A (hsupp ω)]
  exact integrable_condExp.congr hCEeq

/-- The future energy of an open corrector is integrable on its block-good event. -/
theorem integrableOn_futureEnergy_openCorrector (β : ℝ) (t : ℕ → ℕ) (N u s : ℕ)
    (ht : Monotone t) (hu : 1 ≤ u) (hus : u ≤ s) (hts : t s ≤ N) :
    IntegrableOn (fun ω => futureEnergy β (t s) N (openCorrector β t u s ω))
      (blockGoodSet β t u s) disorderLaw := by
  classical
  let G := blockGoodSet β t u s
  let η : Disorder → Site → ℝ := fun ω y => if ω ∈ G then openCorrector β t u s ω y else 0
  let S := openCorrectorNumeratorSupport t u s
  have hGmeas : MeasurableSet[disorderPast (t s)] G := by
    let : MeasurableSpace Disorder := disorderPast (t s)
    have hblock (i : ℕ) (hi : i ∈ Finset.Icc u s) :
        Measurable[disorderPast (t s)] (blockMass β t i) := by
      have hti : t i ≤ t s := ht (Finset.mem_Icc.mp hi).2
      exact (measurable_blockMass β t i).mono
        (Gaussian.disorderBlock_mono (Nat.zero_le _) hti) le_rfl
    have h : MeasurableSet[disorderPast (t s)]
        (⋂ i ∈ Finset.Icc u s, {ω | |blockMass β t i ω - 1| ≤ 1 / 2}) := by
      apply Finset.measurableSet_biInter
      intro i hi
      have habs : Measurable[disorderPast (t s)]
          (fun ω => |blockMass β t i ω - 1|) := (hblock i hi).sub measurable_const |>.abs
      exact MeasurableSet.preimage measurableSet_Iic habs
    convert h using 1
    ext ω
    simp [G, blockGoodSet]
  have hηsupport : ∀ ω y, y ∉ S → η ω y = 0 := by
    intro ω y hy
    by_cases hω : ω ∈ G
    · simp only [η, hω, ite_true]
      unfold openCorrector
      rw [openCorrectorNumerator_eq_zero_of_not_mem_support β t u s ω y hy, zero_div]
    · simp [η, hω]
  have hOpenMeas (y : Site) : Measurable[disorderPast (t s)]
      (fun ω => openCorrector β t u s ω y) := by
    exact measurable_openCorrector_on_past β t ht u s hu hus y
  have hηMeas (y : Site) : Measurable[disorderPast (t s)] (η · y) := by
    change Measurable[disorderPast (t s)]
      (fun ω => if ω ∈ G then openCorrector β t u s ω y else 0)
    exact Measurable.ite hGmeas (hOpenMeas y) measurable_const
  have hXmeas : Measurable (fun ω => randomFlatProfilePolymer β (t s) N η ω ^ 2) := by
    have hprofile := measurable_randomTerminalProfilePolymer β (t s) N S η (fun _ => 1)
      hηsupport hηMeas
    simpa only [randomFlatProfilePolymer, randomTerminalProfilePolymer] using hprofile.pow_const 2
  have hprofileEq (ω : Disorder) : randomFlatProfilePolymer β (t s) N η ω =
      if ω ∈ G then openDiscrepancyMass β t N u (s + 1) ω /
          ∏ i ∈ Finset.Icc u s, blockMass β t i ω else 0 := by
    by_cases hω : ω ∈ G
    · have heta : η ω = openCorrector β t u s ω := by
        funext y
        simp [η, hω]
      rw [randomFlatProfilePolymer, heta, ite_eq_left hω]
      exact profileP2Fun_openCorrector_eq β ht N hu hus hts ω
    · simp [randomFlatProfilePolymer, η, hω, profileP2Fun]
  have hdenlower (ω : Disorder) (hω : ω ∈ G) :
      (1 / 2 : ℝ) ^ (s - u + 1) ≤ ∏ i ∈ Finset.Icc u s, blockMass β t i ω := by
    have hfactor (i : ℕ) (hi : i ∈ Finset.Icc u s) :
        (1 / 2 : ℝ) ≤ blockMass β t i ω := by
      have hGprop : ∀ i ∈ Finset.Icc u s, |blockMass β t i ω - 1| ≤ 1 / 2 := by
        simpa [G, blockGoodSet] using hω
      linarith [(abs_le.mp (hGprop i hi)).1]
    calc
      (1 / 2 : ℝ) ^ (s - u + 1) = ∏ _i ∈ Finset.Icc u s, (1 / 2 : ℝ) := by
        rw [Finset.prod_const]
        have hcard : (Finset.Icc u s).card = s - u + 1 := by
          simp [Nat.card_Icc]
          omega
        rw [hcard]
      _ ≤ ∏ i ∈ Finset.Icc u s, blockMass β t i ω := by
        apply Finset.prod_le_prod₀
        · intro i hi
          positivity
        · intro i hi
          exact hfactor i hi
  have hratioBound (ω : Disorder) (hω : ω ∈ G) :
      |openDiscrepancyMass β t N u (s + 1) ω /
        ∏ i ∈ Finset.Icc u s, blockMass β t i ω| ^ 2 ≤
          (4 : ℝ) ^ (s - u + 1) * openDiscrepancyMass β t N u (s + 1) ω ^ 2 := by
    have hprod := hdenlower ω hω
    have hprodpos : 0 < ∏ i ∈ Finset.Icc u s, blockMass β t i ω :=
      Finset.prod_pos fun i hi => blockMass_pos β t i ω
    have hinv : (∏ i ∈ Finset.Icc u s, blockMass β t i ω)⁻¹ ≤
        (2 : ℝ) ^ (s - u + 1) := by
      have hrecip := (inv_le_inv₀ hprodpos (pow_pos (by norm_num) _)).2 hprod
      have hbase : ((1 / 2 : ℝ) ^ (s - u + 1))⁻¹ = (2 : ℝ) ^ (s - u + 1) := by
        rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, inv_pow, inv_inv]
      simpa [hbase] using hrecip
    rw [div_eq_mul_inv, sq_abs, mul_pow]
    have hinvSq : (∏ i ∈ Finset.Icc u s, blockMass β t i ω)⁻¹ ^ 2 ≤
        ((2 : ℝ) ^ (s - u + 1)) ^ 2 :=
      (sq_le_sq₀ (inv_nonneg.mpr hprodpos.le) (by positivity)).2 hinv
    calc
      _ ≤ openDiscrepancyMass β t N u (s + 1) ω ^ 2 *
          ((2 : ℝ) ^ (s - u + 1)) ^ 2 := mul_le_mul_of_nonneg_left hinvSq (sq_nonneg _)
      _ = (4 : ℝ) ^ (s - u + 1) * openDiscrepancyMass β t N u (s + 1) ω ^ 2 := by
        rw [show ((2 : ℝ) ^ (s - u + 1)) ^ 2 = (4 : ℝ) ^ (s - u + 1) by
          calc
            _ = (2 : ℝ) ^ ((s - u + 1) * 2) := by rw [← pow_mul]
            _ = (2 : ℝ) ^ (2 * (s - u + 1)) := by congr 1; omega
            _ = ((2 : ℝ) ^ 2) ^ (s - u + 1) := by rw [pow_mul]
            _ = _ := by norm_num]
        ring
  have hOpenInt : Integrable
      (fun ω => openDiscrepancyMass β t N u (s + 1) ω ^ 2) disorderLaw := by
    rw [show (fun ω => openDiscrepancyMass β t N u (s + 1) ω ^ 2) =
        (fun ω => closedDiscrepancy β (Function.update t (s + 1) N) u (s + 1) ω ^ 2) by
      funext ω
      exact congrArg (fun z : ℝ => z ^ 2)
        (openDiscrepancyMass_eq_closedDiscrepancy_update β t N hu (by omega) ω)]
    exact integrable_sq_closedDiscrepancy β (Function.update t (s + 1) N) u (s + 1)
  have hXbound (ω : Disorder) :
      ‖randomFlatProfilePolymer β (t s) N η ω ^ 2‖ ≤
        (4 : ℝ) ^ (s - u + 1) * openDiscrepancyMass β t N u (s + 1) ω ^ 2 := by
    by_cases hω : ω ∈ G
    · rw [hprofileEq ω, ite_eq_left hω]
      have h := hratioBound ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      rw [← sq_abs]
      exact h
    · rw [hprofileEq ω, ite_eq_right hω]
      have hnonneg : 0 ≤ (4 : ℝ) ^ (s - u + 1) *
          openDiscrepancyMass β t N u (s + 1) ω ^ 2 := by positivity
      simpa [Real.norm_eq_abs] using hnonneg
  have hXint : Integrable (fun ω => randomFlatProfilePolymer β (t s) N η ω ^ 2)
      disorderLaw := (hOpenInt.const_mul ((4 : ℝ) ^ (s - u + 1))).mono'
        hXmeas.aestronglyMeasurable (Filter.Eventually.of_forall hXbound)
  have hηEnergyInt := integrable_futureEnergy_of_randomFlatProfilePolymer_sq β
    (by omega) η S hηsupport hηMeas hXmeas hXint
  have hGmeasGlobal := disorderPast_le_local (t s) G hGmeas
  have hηeq (ω : Disorder) (hω : ω ∈ G) : η ω = openCorrector β t u s ω := by
    funext y
    simp [η, hω]
  apply hηEnergyInt.integrableOn.congr
  filter_upwards [ae_restrict_mem hGmeasGlobal] with ω hω
  rw [hηeq ω hω]

/-- The squared open-discrepancy bound implies an integrated future-energy bound for the open corrector.

Its `IntegrableOn` companion is `integrableOn_futureEnergy_openCorrector`. -/
theorem setIntegral_futureEnergy_openCorrector_le_of (hDiscrepancyStringInput : OpenStringBound) (A : ℝ) :
    ∃ ρ₀ θ : ℝ, 1 < ρ₀ ∧ 0 < θ ∧ θ < 1 ∧ ∀ ρ₁ : ℝ, ∃ C : ℝ, ∀ ρ ∈ Set.Icc ρ₀ ρ₁,
      ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A, ∀ u s : ℕ, 1 ≤ u → u ≤ s → s + 2 ≤ blockCount N ρ →
        ∫ ω in blockGoodSet (criticalBeta ϑ N) (blockTime N ρ) u s,
            futureEnergy (criticalBeta ϑ N) (blockTime N ρ s) N
              (openCorrector (criticalBeta ϑ N) (blockTime N ρ) u s ω) ∂disorderLaw ≤
          C * θ ^ (2 * (s - u)) / ((blockCount N ρ : ℝ) - u) := by
  obtain ⟨C₀K, ε, hε, hDiscrepancyStringInputA⟩ := hDiscrepancyStringInput A
  let ρ₀ : ℝ := Real.exp (4 * ε ^ 2) + 2
  let θ : ℝ := 2 * ε / Real.sqrt (Real.log ρ₀)
  have hρ₀ : 1 < ρ₀ := by
    dsimp [ρ₀]
    nlinarith [Real.exp_pos (4 * ε ^ 2)]
  have hlogρ₀ : 0 < Real.log ρ₀ := Real.log_pos hρ₀
  have hθpos : 0 < θ := by
    dsimp [θ]
    positivity
  have hθlt : θ < 1 := by
    dsimp [θ, ρ₀]
    have hlog : 4 * ε ^ 2 < Real.log (Real.exp (4 * ε ^ 2) + 2) :=
      (Real.lt_log_iff_exp_lt (by positivity)).2 (by
        exact lt_add_of_pos_right _ (by norm_num))
    have hrootSq : (2 * ε) ^ 2 <
        Real.sqrt (Real.log (Real.exp (4 * ε ^ 2) + 2)) ^ 2 := by
      rw [Real.sq_sqrt hlogρ₀.le]
      nlinarith
    have hroot : 2 * ε < Real.sqrt (Real.log (Real.exp (4 * ε ^ 2) + 2)) := by
      apply lt_of_not_ge
      intro hnot
      have hsqle := (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity : 0 ≤ 2 * ε)).2 hnot
      linarith
    exact (div_lt_one (Real.sqrt_pos.2 hlogρ₀)).2 hroot
  refine ⟨ρ₀, θ, hρ₀, hθpos, hθlt, ?_⟩
  intro ρ₁
  refine ⟨4 * C₀K ^ 2, ?_⟩
  intro ρ hρmem
  have hρ : Real.exp (ε ^ 2) < ρ := by
    have hexpMono : Real.exp (ε ^ 2) ≤ Real.exp (4 * ε ^ 2) :=
      Real.exp_le_exp.mpr (by nlinarith [sq_nonneg ε])
    have hexpAdd : Real.exp (4 * ε ^ 2) < ρ₀ := by
      dsimp [ρ₀]
      exact lt_add_of_pos_right _ (by norm_num)
    exact (hexpMono.trans_lt hexpAdd).trans_le hρmem.1
  have hρpos : 0 < ρ := by linarith [hρmem.1]
  have hlogρ : Real.log ρ₀ ≤ Real.log ρ := Real.log_le_log (by linarith) hρmem.1
  have hθρ : 2 * (ε / Real.sqrt (Real.log ρ)) ≤ θ := by
    dsimp [θ]
    have hroot : Real.sqrt (Real.log ρ₀) ≤ Real.sqrt (Real.log ρ) :=
      Real.sqrt_le_sqrt hlogρ
    have hroot0 : 0 < Real.sqrt (Real.log ρ₀) := Real.sqrt_pos.2 hlogρ₀
    have hrootρ : 0 < Real.sqrt (Real.log ρ) :=
      Real.sqrt_pos.2 (lt_of_lt_of_le hlogρ₀ hlogρ)
    have hfrac : ε / Real.sqrt (Real.log ρ) ≤ ε / Real.sqrt (Real.log ρ₀) :=
      div_le_div_of_nonneg_left hε.le hroot0 hroot
    calc
      2 * (ε / Real.sqrt (Real.log ρ)) ≤ 2 * (ε / Real.sqrt (Real.log ρ₀)) :=
        mul_le_mul_of_nonneg_left hfrac (by norm_num)
      _ = 2 * ε / Real.sqrt (Real.log ρ₀) := by ring
  have hKevent := hDiscrepancyStringInputA ρ hρ
  have hρstrict : 1 < ρ := lt_of_lt_of_le hρ₀ hρmem.1
  filter_upwards [hKevent, blockTime_monotone hρstrict,
      eventually_ge_atTop 1] with N hKN hmono hKpos
  classical
  intro ϑ hϑ u s hu hus hsK
  let β := criticalBeta ϑ N
  let t := blockTime N ρ
  let G := blockGoodSet β t u s
  let η : Disorder → Site → ℝ := fun ω y => if ω ∈ G then openCorrector β t u s ω y else 0
  let S := openCorrectorNumeratorSupport t u s
  have hKnat : 1 ≤ blockCount N ρ := by unfold blockCount; omega
  have hmonoUS : Monotone t := hmono
  have htS : t s ≤ N := by
    have hle := hmonoUS (show s ≤ s + 2 by omega)
    have hleK := hmonoUS hsK
    have hterminal : t (blockCount N ρ) = N := by
      simp [t, blockTime, Nat.ne_of_gt (by omega : 0 < blockCount N ρ)]
    rw [hterminal] at hleK
    exact hle.trans hleK
  have htStart : t (u - 1) ≤ t s := hmonoUS (by omega)
  have htU : t (u - 1) ≤ t s := htStart
  have hGmeas : MeasurableSet[disorderPast (t s)] G := by
    let : MeasurableSpace Disorder := disorderPast (t s)
    have hblock (i : ℕ) (hi : i ∈ Finset.Icc u s) :
        Measurable[disorderPast (t s)] (blockMass β t i) := by
      have hti : t i ≤ t s := hmonoUS (Finset.mem_Icc.mp hi).2
      exact (measurable_blockMass β t i).mono
        (Gaussian.disorderBlock_mono (Nat.zero_le _) hti) le_rfl
    have h : MeasurableSet[disorderPast (t s)]
        (⋂ i ∈ Finset.Icc u s, {ω | |blockMass β t i ω - 1| ≤ 1 / 2}) := by
      apply Finset.measurableSet_biInter
      intro i hi
      have habs : Measurable[disorderPast (t s)]
          (fun ω => |blockMass β t i ω - 1|) :=
        (hblock i hi).sub measurable_const |>.abs
      exact MeasurableSet.preimage measurableSet_Iic habs
    convert h using 1
    ext ω
    simp [G, blockGoodSet]
  have hGmeas' : MeasurableSet[disorderPast (t s)] G := hGmeas
  have hηsupport : ∀ ω y, y ∉ S → η ω y = 0 := by
    intro ω y hy
    by_cases hω : ω ∈ G
    · simp only [η, hω, ite_true]
      unfold openCorrector
      rw [openCorrectorNumerator_eq_zero_of_not_mem_support β t u s ω y hy, zero_div]
    · simp [η, hω]
  have hnumMeas (y : Site) : Measurable[disorderPast (t s)]
      (fun ω => openCorrectorNumerator β t u s ω y) := by
    let : MeasurableSpace Disorder := disorderPast (t s)
    have hstr (x : Site) : Measurable[disorderPast (t s)]
        (fun ω => discrepancyString β t u (s + 1 - u) x y ω) := by
      have h := measurable_discrepancyString_block_to_last β t hmonoUS u
        (s + 1 - u) s (by omega) x y
      have hfield := Gaussian.disorderBlock_mono (Nat.zero_le (t (u - 1))) (le_rfl : t s ≤ t s)
      exact h.mono hfield le_rfl
    change Measurable[disorderPast (t s)] (fun ω =>
      ∑' x, srwKernel (t (u - 1)) x * discrepancyString β t u (s + 1 - u) x y ω)
    exact Measurable.tsum fun x => (hstr x).const_mul _
  have hdenMeas : Measurable[disorderPast (t s)] (fun ω =>
      ∏ i ∈ Finset.Icc u s, blockMass β t i ω) := by
    let : MeasurableSpace Disorder := disorderPast (t s)
    apply Finset.measurable_prod
    intro i hi
    have hti : t i ≤ t s := hmonoUS (Finset.mem_Icc.mp hi).2
    exact (measurable_blockMass β t i).mono
      (Gaussian.disorderBlock_mono (Nat.zero_le _) hti) le_rfl
  have hOpenMeas (y : Site) : Measurable[disorderPast (t s)]
      (fun ω => openCorrector β t u s ω y) := by
    unfold openCorrector
    exact (hnumMeas y).div hdenMeas
  have hηMeas (y : Site) : Measurable[disorderPast (t s)] (η · y) := by
    change Measurable[disorderPast (t s)]
      (fun ω => if ω ∈ G then openCorrector β t u s ω y else 0)
    exact Measurable.ite hGmeas (hOpenMeas y) measurable_const
  have hXmeas : Measurable (fun ω => randomFlatProfilePolymer β (t s) N η ω ^ 2) := by
    have hprofile := measurable_randomTerminalProfilePolymer β (t s) N S η (fun _ => 1)
      hηsupport hηMeas
    simpa only [randomFlatProfilePolymer, randomTerminalProfilePolymer] using hprofile.pow_const 2
  have hprofileEq (ω : Disorder) : randomFlatProfilePolymer β (t s) N η ω =
      if ω ∈ G then openDiscrepancyMass β t N u (s + 1) ω /
          ∏ i ∈ Finset.Icc u s, blockMass β t i ω else 0 := by
    by_cases hω : ω ∈ G
    · have heta : η ω = openCorrector β t u s ω := by
        funext y
        simp [η, hω]
      rw [randomFlatProfilePolymer, heta]
      rw [ite_eq_left hω]
      exact profileP2Fun_openCorrector_eq β hmonoUS N hu hus htS ω
    · simp [randomFlatProfilePolymer, η, hω, profileP2Fun]
  have hdenlower (ω : Disorder) (hω : ω ∈ G) :
      (1 / 2 : ℝ) ^ (s - u + 1) ≤ ∏ i ∈ Finset.Icc u s, blockMass β t i ω := by
    have hfactor (i : ℕ) (hi : i ∈ Finset.Icc u s) :
        (1 / 2 : ℝ) ≤ blockMass β t i ω := by
      have hGprop : ∀ i ∈ Finset.Icc u s, |blockMass β t i ω - 1| ≤ 1 / 2 := by
        simpa [G, blockGoodSet] using hω
      have hiω := hGprop i hi
      have := (abs_le.mp hiω).1
      linarith
    calc
      (1 / 2 : ℝ) ^ (s - u + 1) = ∏ _i ∈ Finset.Icc u s, (1 / 2 : ℝ) := by
        rw [Finset.prod_const]
        have hcard : (Finset.Icc u s).card = s - u + 1 := by
          simp [Nat.card_Icc]
          omega
        rw [hcard]
      _ ≤ ∏ i ∈ Finset.Icc u s, blockMass β t i ω := by
        apply Finset.prod_le_prod₀
        · intro i hi
          exact (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
        · intro i hi
          exact hfactor i hi
  have hproductpos (ω : Disorder) : 0 < ∏ i ∈ Finset.Icc u s, blockMass β t i ω :=
    Finset.prod_pos fun i hi => blockMass_pos β t i ω
  have hratioBound (ω : Disorder) (hω : ω ∈ G) :
      |openDiscrepancyMass β t N u (s + 1) ω /
        ∏ i ∈ Finset.Icc u s, blockMass β t i ω| ^ 2 ≤
          (4 : ℝ) ^ (s - u + 1) * openDiscrepancyMass β t N u (s + 1) ω ^ 2 := by
    have hprod := hdenlower ω hω
    have hprodpos := hproductpos ω
    have hinv : (∏ i ∈ Finset.Icc u s, blockMass β t i ω)⁻¹ ≤
        (2 : ℝ) ^ (s - u + 1) := by
      have hbasepos : 0 < (1 / 2 : ℝ) ^ (s - u + 1) := pow_pos (by norm_num) _
      have hrecip := (inv_le_inv₀ hprodpos hbasepos).2 hprod
      have hbaseinv : ((1 / 2 : ℝ) ^ (s - u + 1))⁻¹ =
          (2 : ℝ) ^ (s - u + 1) := by
        rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, inv_pow, inv_inv]
      simpa [hbaseinv] using hrecip
    have hsq : |openDiscrepancyMass β t N u (s + 1) ω /
        ∏ i ∈ Finset.Icc u s, blockMass β t i ω| ^ 2 =
          openDiscrepancyMass β t N u (s + 1) ω ^ 2 *
            (∏ i ∈ Finset.Icc u s, blockMass β t i ω)⁻¹ ^ 2 := by
      rw [sq_abs, div_eq_mul_inv, mul_pow]
    rw [hsq]
    have hinvnonneg : 0 ≤ (∏ i ∈ Finset.Icc u s, blockMass β t i ω)⁻¹ := inv_nonneg.mpr hprodpos.le
    have hsquare : (∏ i ∈ Finset.Icc u s, blockMass β t i ω)⁻¹ ^ 2 ≤
        ((2 : ℝ) ^ (s - u + 1)) ^ 2 :=
      (sq_le_sq₀ hinvnonneg (by positivity)).2 hinv
    calc
      _ ≤ openDiscrepancyMass β t N u (s + 1) ω ^ 2 *
          ((2 : ℝ) ^ (s - u + 1)) ^ 2 :=
            mul_le_mul_of_nonneg_left hsquare (sq_nonneg _)
      _ = (4 : ℝ) ^ (s - u + 1) * openDiscrepancyMass β t N u (s + 1) ω ^ 2 := by
            have hp : ((2 : ℝ) ^ (s - u + 1)) ^ 2 =
                (4 : ℝ) ^ (s - u + 1) := by
              calc
                _ = (2 : ℝ) ^ ((s - u + 1) * 2) := by rw [← pow_mul]
                _ = (2 : ℝ) ^ (2 * (s - u + 1)) := by congr 1; omega
                _ = ((2 : ℝ) ^ 2) ^ (s - u + 1) := by rw [pow_mul]
                _ = _ := by norm_num
            rw [hp, mul_comm]
  have hXbound (ω : Disorder) :
      ‖randomFlatProfilePolymer β (t s) N η ω ^ 2‖ ≤
        (4 : ℝ) ^ (s - u + 1) *
          openDiscrepancyMass β t N u (s + 1) ω ^ 2 := by
    by_cases hω : ω ∈ G
    · rw [hprofileEq ω, ite_eq_left hω]
      have hbound := hratioBound ω hω
      have hnormX : ‖(openDiscrepancyMass β t N u (s + 1) ω /
          ∏ i ∈ Finset.Icc u s, blockMass β t i ω) ^ 2‖ =
          |openDiscrepancyMass β t N u (s + 1) ω /
            ∏ i ∈ Finset.Icc u s, blockMass β t i ω| ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact (sq_abs _).symm
      rw [hnormX]
      exact hbound
    · rw [hprofileEq ω, ite_eq_right hω]
      have hnonneg : 0 ≤ (4 : ℝ) ^ (s - u + 1) *
          openDiscrepancyMass β t N u (s + 1) ω ^ 2 := by positivity
      have hmassnonneg : 0 ≤ openDiscrepancyMass β t N u (s + 1) ω ^ 2 := sq_nonneg _
      simpa [Real.norm_eq_abs, abs_of_nonneg hmassnonneg]
  have hOpenInt : Integrable
      (fun ω => openDiscrepancyMass β t N u (s + 1) ω ^ 2) disorderLaw := by
    rw [show (fun ω => openDiscrepancyMass β t N u (s + 1) ω ^ 2) =
        (fun ω => closedDiscrepancy β (Function.update t (s + 1) N) u (s + 1) ω ^ 2) by
      funext ω
      exact congrArg (fun z : ℝ => z ^ 2)
        (openDiscrepancyMass_eq_closedDiscrepancy_update β t N hu
          (by omega : u ≤ s + 1) ω)]
    exact integrable_sq_closedDiscrepancy β (Function.update t (s + 1) N) u (s + 1)
  have hXint : Integrable
      (fun ω => randomFlatProfilePolymer β (t s) N η ω ^ 2) disorderLaw :=
    (hOpenInt.const_mul ((4 : ℝ) ^ (s - u + 1))).mono' hXmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => hXbound ω)
  have henergyEq := setIntegral_profileP2Fun_sq_eq_of_integrable β
    (by omega) η S hηsupport hηMeas hXmeas hXint G hGmeas'
  have hDiscrepancyStringInputN := hKN ϑ hϑ u (s + 1) hu (by omega) (by omega)
  have hDiscrepancyStringInputN' : ∫ ω, openDiscrepancyMass β t N u (s + 1) ω ^ 2 ∂disorderLaw ≤
      (C₀K * (ε / Real.sqrt (Real.log ρ)) ^ (s - u)) ^ 2 /
        ((blockCount N ρ : ℝ) - u) := by
    have hexp : s + 1 - u - 1 = s - u := by omega
    simpa only [β, t, hexp] using hDiscrepancyStringInputN
  have hdenom := by
    have hKlower : 0 < (blockCount N ρ : ℝ) - u := by
      have hnat : u < blockCount N ρ := by omega
      rw [← Nat.cast_sub (Nat.le_of_lt hnat)]
      exact_mod_cast Nat.sub_pos_of_lt hnat
    have hθpow : (2 * (ε / Real.sqrt (Real.log ρ))) ^ (2 * (s - u)) ≤
        θ ^ (2 * (s - u)) := by
      exact pow_le_pow_left₀ (by positivity) hθρ (2 * (s - u))
    have hGmeasGlobal := disorderPast_le_local (t s) G hGmeas'
    calc
      ∫ ω in G, futureEnergy β (t s) N (openCorrector β t u s ω) ∂disorderLaw
          = ∫ ω in G, futureEnergy β (t s) N (η ω) ∂disorderLaw := by
              apply setIntegral_congr_ae hGmeasGlobal
              filter_upwards [] with ω hω
              have heta : η ω = openCorrector β t u s ω := by
                funext y
                simp [η, hω]
              rw [heta]
      _ = ∫ ω in G, profileP2Fun β (t s) N (η ω) (fun _ => 1) ω ^ 2 ∂disorderLaw :=
            henergyEq.symm
      _ = ∫ ω in G, randomFlatProfilePolymer β (t s) N η ω ^ 2 ∂disorderLaw := by
            simp only [randomFlatProfilePolymer]
      _ ≤ (4 : ℝ) ^ (s - u + 1) *
            ∫ ω in G, openDiscrepancyMass β t N u (s + 1) ω ^ 2 ∂disorderLaw := by
              calc
                _ ≤ ∫ ω in G,
                    (4 : ℝ) ^ (s - u + 1) *
                      openDiscrepancyMass β t N u (s + 1) ω ^ 2 ∂disorderLaw := by
                    apply setIntegral_mono_on hXint.integrableOn
                      (hOpenInt.const_mul ((4 : ℝ) ^ (s - u + 1))).integrableOn
                      hGmeasGlobal
                    intro ω hω
                    have h := hratioBound ω hω
                    rw [hprofileEq ω, ite_eq_left hω]
                    simpa [Real.norm_eq_abs, sq_abs] using h
                _ = (4 : ℝ) ^ (s - u + 1) *
                    ∫ ω in G, openDiscrepancyMass β t N u (s + 1) ω ^ 2 ∂disorderLaw := by
                      rw [integral_const_mul]
      _ ≤ (4 : ℝ) ^ (s - u + 1) *
            ∫ ω, openDiscrepancyMass β t N u (s + 1) ω ^ 2 ∂disorderLaw := by
              exact mul_le_mul_of_nonneg_left
                (setIntegral_le_integral hOpenInt
                  (Filter.Eventually.of_forall fun ω => sq_nonneg _)) (by positivity)
      _ ≤ (4 : ℝ) ^ (s - u + 1) *
            ((C₀K * (ε / Real.sqrt (Real.log ρ)) ^ (s - u)) ^ 2 /
              ((blockCount N ρ : ℝ) - u)) := by
              exact mul_le_mul_of_nonneg_left hDiscrepancyStringInputN' (by positivity)
      _ = 4 * C₀K ^ 2 *
            (2 * (ε / Real.sqrt (Real.log ρ))) ^ (2 * (s - u)) /
              ((blockCount N ρ : ℝ) - u) := by
              let d : ℕ := s - u
              let e : ℝ := ε / Real.sqrt (Real.log ρ)
              have hd : d = s - u := rfl
              have he : e = ε / Real.sqrt (Real.log ρ) := rfl
              have hpow : (C₀K * e ^ d) ^ 2 = C₀K ^ 2 * e ^ (2 * d) := by
                rw [mul_pow, ← pow_mul, Nat.mul_comm]
              have hdouble : (2 * e) ^ (2 * d) = 4 ^ d * e ^ (2 * d) := by
                rw [mul_pow, pow_mul]
                norm_num
              rw [show s - u + 1 = d + 1 by simp [d]]
              rw [pow_succ, hpow, hdouble]
              rw [he]
              ring
      _ ≤ 4 * C₀K ^ 2 * θ ^ (2 * (s - u)) /
            ((blockCount N ρ : ℝ) - u) := by
              apply div_le_div_of_nonneg_right _ hKlower.le
              apply mul_le_mul_of_nonneg_left hθpow
              positivity
  exact hdenom

end Critical2DKPZ.FutureProfiles

end
