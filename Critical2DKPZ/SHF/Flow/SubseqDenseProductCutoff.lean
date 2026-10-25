/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.SubseqDenseInputs
public import Critical2DKPZ.SHF.Limit.FlatBound
public import Critical2DKPZ.SHF.Tsai.CompactTensorApproximation
public import Critical2DKPZ.SHF.Tsai.Cutoff
public import Critical2DKPZ.SHF.Flow.SubseqDenseMoments
public import Critical2DKPZ.SHF.Flow.SubseqDenseProductTransfer
public import Critical2DKPZ.SHF.Flow.SubseqDenseProducts
public import Critical2DKPZ.SHF.Flow.CutoffConvergence
public import Critical2DKPZ.JointConvergence.Approximation
public import Critical2DKPZ.RandomMeasure.GeneralTests
import Critical2DKPZ.SHF.Flow.SlabSmoothedFinite
import Mathlib.Tactic

/-! # Product pairings in dense subsequential limits -/

@[expose] public section

open MeasureTheory Filter
open scoped BoundedContinuousFunction CompactlySupported Topology

namespace Critical2DKPZ.SHF.Flow

open Critical2DKPZ.SHF.Limit
open Critical2DKPZ.SHF.Tsai

/-- Two square-integrable real observables have an integrable product. -/
theorem integrable_mul_of_integrable_sq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {X Y : Ω → ℝ}
    (hX : AEStronglyMeasurable X P) (hY : AEStronglyMeasurable Y P)
    (hX2 : Integrable (fun ω => X ω ^ 2) P)
    (hY2 : Integrable (fun ω => Y ω ^ 2) P) :
    Integrable (fun ω => X ω * Y ω) P := by
  let G : Ω → ℝ := fun ω => X ω ^ 2 + Y ω ^ 2
  have hG : Integrable G P := by
    change Integrable ((fun ω => X ω ^ 2) + (fun ω => Y ω ^ 2)) P
    exact hX2.add hY2
  have hXYsm : AEStronglyMeasurable (fun ω => X ω * Y ω) P := hX.mul hY
  refine hG.mono' hXYsm ?_
  filter_upwards [] with ω
  have hYoung : |X ω * Y ω| ≤ X ω ^ 2 + Y ω ^ 2 := by
    have h := sq_nonneg (|X ω| - |Y ω|)
    rw [abs_mul]
    nlinarith [sq_abs (X ω), sq_abs (Y ω)]
  calc
    ‖X ω * Y ω‖ = |X ω * Y ω| := Real.norm_eq_abs _
    _ ≤ X ω ^ 2 + Y ω ^ 2 := hYoung
    _ = G ω := rfl

/-- The integral of a product of two square-integrable observables is bounded by their quadratic moments; product integrability is supplied by `integrable_mul_of_integrable_sq`. -/
theorem integral_mul_le_sq_integrals {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {X Y : Ω → ℝ}
    (hX : AEStronglyMeasurable X P) (hY : AEStronglyMeasurable Y P)
    (hX2 : Integrable (fun ω => X ω ^ 2) P)
    (hY2 : Integrable (fun ω => Y ω ^ 2) P) :
    ∫ ω, X ω * Y ω ∂P ≤
      (∫ ω, X ω ^ 2 ∂P) + ∫ ω, Y ω ^ 2 ∂P := by
  have hXY : Integrable (fun ω => X ω * Y ω) P :=
    integrable_mul_of_integrable_sq P hX hY hX2 hY2
  calc
    ∫ ω, X ω * Y ω ∂P ≤ ∫ ω, X ω ^ 2 + Y ω ^ 2 ∂P := by
      apply integral_mono hXY (hX2.add hY2)
      intro ω
      change X ω * Y ω ≤ X ω ^ 2 + Y ω ^ 2
      nlinarith [sq_nonneg (X ω - Y ω), sq_nonneg (X ω), sq_nonneg (Y ω)]
    _ = (∫ ω, X ω ^ 2 ∂P) + ∫ ω, Y ω ^ 2 ∂P :=
      integral_add hX2 hY2

private theorem integrable_abs_sub_le_product_sq_moments
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {A B U V : Ω → ℝ} {c M_U M_V : ℝ}
    (hA : AEStronglyMeasurable A P) (hB : AEStronglyMeasurable B P)
    (hU : AEStronglyMeasurable U P) (hV : AEStronglyMeasurable V P)
    (hU2 : Integrable (fun ω => U ω ^ 2) P)
    (hV2 : Integrable (fun ω => V ω ^ 2) P)
    (hUbound : ∫ ω, U ω ^ 2 ∂P ≤ M_U)
    (hVbound : ∫ ω, V ω ^ 2 ∂P ≤ M_V)
    (hc : 0 ≤ c)
    (hpoint : ∀ᵐ ω ∂P, |A ω - B ω| ≤ c * (U ω * V ω)) :
    Integrable (fun ω => |A ω - B ω|) P ∧
      ∫ ω, |A ω - B ω| ∂P ≤ c * (max M_U 0 + max M_V 0) := by
  have hUVint : Integrable (fun ω => U ω * V ω) P :=
    integrable_mul_of_integrable_sq P hU hV hU2 hV2
  have hUVbound : ∫ ω, U ω * V ω ∂P ≤ max M_U 0 + max M_V 0 := by
    calc
      ∫ ω, U ω * V ω ∂P ≤ (∫ ω, U ω ^ 2 ∂P) + ∫ ω, V ω ^ 2 ∂P :=
        integral_mul_le_sq_integrals P hU hV hU2 hV2
      _ ≤ max M_U 0 + max M_V 0 :=
        add_le_add (hUbound.trans (le_max_left _ _)) (hVbound.trans (le_max_left _ _))
  have hmajor : Integrable (fun ω => c * (U ω * V ω)) P := hUVint.const_mul c
  have hdiffMeas : AEStronglyMeasurable (fun ω => |A ω - B ω|) P :=
    (hA.sub hB).norm
  have hdiff : Integrable (fun ω => |A ω - B ω|) P := by
    refine hmajor.mono' hdiffMeas ?_
    filter_upwards [hpoint] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
    exact hω
  refine ⟨hdiff, ?_⟩
  calc
    ∫ ω, |A ω - B ω| ∂P ≤ ∫ ω, c * (U ω * V ω) ∂P :=
      integral_mono_ae hdiff hmajor hpoint
    _ = c * ∫ ω, U ω * V ω ∂P := integral_const_mul _ _
    _ ≤ c * (max M_U 0 + max M_V 0) :=
      mul_le_mul_of_nonneg_left hUVbound hc

/-- A finite tensor sum is integrable against a product of locally finite pair measures, and its
integral is the corresponding sum of products of pairings. -/
theorem integrable_integral_finiteTensorSum_eq
    (μ ν : Measure (Plane × Plane)) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν]
    (r : ℕ) (f g : Fin r → C_c(Plane × Plane, ℝ)) :
    Integrable (fun q : (Plane × Plane) × (Plane × Plane) =>
      ∑ i, f i q.1 * g i q.2) (μ.prod ν) ∧
    (∫ q : (Plane × Plane) × (Plane × Plane),
      ∑ i, f i q.1 * g i q.2 ∂(μ.prod ν)) =
      ∑ i, (∫ p, f i p ∂μ) * ∫ p, g i p ∂ν := by
  have hterm (i : Fin r) : Integrable
      (fun q : (Plane × Plane) × (Plane × Plane) => f i q.1 * g i q.2) (μ.prod ν) := by
    exact (integrable_compactTest_of_locallyFinite μ ‹_› (f i)).mul_prod
      (integrable_compactTest_of_locallyFinite ν ‹_› (g i))
  have hsum : Integrable
      (fun q : (Plane × Plane) × (Plane × Plane) => ∑ i, f i q.1 * g i q.2)
      (μ.prod ν) := integrable_finsetSum _ (fun i hi => hterm i)
  refine ⟨hsum, ?_⟩
  rw [integral_finsetSum _ (fun i hi => hterm i)]
  apply Finset.sum_congr rfl
  intro i hi
  exact integral_prod_mul (f i) (g i)


/-- A uniform sixth-moment bound controls the second moments of compact flat marginals along the chosen subsequence. -/
theorem eventually_polymerSubseq_flatMarginal_secondMoment_of (ϑ : ℝ)
    (hFlatSixthMomentInput : FlatSixthMomentBound ϑ) (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (χ : C_c(Plane, ℝ))
    (hχ : ∀ x, 0 ≤ χ x) :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      Integrable (fun ω => (∫ x, χ x ∂
        ((polymerMeasure ϑ (ψ n) s t ω).map Prod.fst)) ^ 2) disorderLaw ∧
      ∫ ω, (∫ x, χ x ∂
        ((polymerMeasure ϑ (ψ n) s t ω).map Prod.fst)) ^ 2 ∂disorderLaw ≤ C := by
  let τ : ℝ := (t - s) / 2
  have hτ : 0 < τ := by dsimp [τ]; linarith
  obtain ⟨C, hC⟩ := hFlatSixthMomentInput χ (τ := τ) (T := t) hτ
  have hCevent : ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω => (∫ x, |χ x| ∂
        ((polymerMeasure ϑ N s t ω).map Prod.fst)) ^ 6) disorderLaw ∧
      ∫ ω, (∫ x, |χ x| ∂
        ((polymerMeasure ϑ N s t ω).map Prod.fst)) ^ 6 ∂disorderLaw ≤ C := by
    filter_upwards [hC] with N hN
    exact hN s t hs (by dsimp [τ]; linarith) le_rfl
  have hψpos : ∀ᶠ n : ℕ in atTop, 1 ≤ ψ n :=
    hψ.tendsto_atTop.eventually (eventually_ge_atTop 1)
  refine ⟨1 + max C 0, ?_⟩
  filter_upwards [hψpos, hψ.tendsto_atTop.eventually hCevent] with n hnpos hn
  let U : Disorder → ℝ := fun ω => ∫ x, χ x ∂
    ((polymerMeasure ϑ (ψ n) s t ω).map Prod.fst)
  have hUmeas : AEMeasurable U disorderLaw := by
    have hraw := aemeasurable_rescaledP2Plane_pairing ϑ (ψ n) s t χ
    have hEq : U =ᵐ[disorderLaw] fun ω =>
        ∫ x, χ x * rescaledP2Plane ϑ (ψ n) s t x ω := by
      filter_upwards [] with ω
      exact integral_map_fst_polymerMeasure ϑ hnpos s t ω χ
    exact hraw.congr hEq.symm
  have hUnonneg (ω : Disorder) : 0 ≤ U ω := integral_nonneg fun x => hχ x
  have hUabsEq : ∀ ω : Disorder,
      ∫ x, |χ x| ∂((polymerMeasure ϑ (ψ n) s t ω).map Prod.fst) = U ω := by
    intro ω
    apply integral_congr_ae
    filter_upwards [] with x
    rw [abs_of_nonneg (hχ x)]
  have hU6Eq : (fun ω =>
      (∫ x, |χ x| ∂((polymerMeasure ϑ (ψ n) s t ω).map Prod.fst)) ^ 6) =
      fun ω => U ω ^ 6 := by
    funext ω
    rw [hUabsEq ω]
  have hU6Int : Integrable (fun ω => U ω ^ 6) disorderLaw :=
    hn.1.congr (Filter.Eventually.of_forall fun ω => congrFun hU6Eq ω)
  have hU6bound : ∫ ω, U ω ^ 6 ∂disorderLaw ≤ max C 0 := by
    have hle : ∫ ω, U ω ^ 6 ∂disorderLaw ≤ C := by
      calc
        ∫ ω, U ω ^ 6 ∂disorderLaw =
            ∫ ω, (∫ x, |χ x| ∂
              ((polymerMeasure ϑ (ψ n) s t ω).map Prod.fst)) ^ 6 ∂disorderLaw :=
          integral_congr_ae
            (Filter.Eventually.of_forall fun ω => (congrFun hU6Eq ω).symm)
        _ ≤ C := hn.2
    exact hle.trans (le_max_left _ _)
  have hmajorInt : Integrable (fun ω => 1 + U ω ^ 6) disorderLaw :=
    (integrable_const (1 : ℝ)).add hU6Int
  have hUsqMeas : AEStronglyMeasurable (fun ω => U ω ^ 2) disorderLaw :=
    (continuous_id.pow 2).comp_aestronglyMeasurable hUmeas.aestronglyMeasurable
  have hUsqInt : Integrable (fun ω => U ω ^ 2) disorderLaw := by
    refine hmajorInt.mono' hUsqMeas ?_
    filter_upwards [] with ω
    rw [Real.norm_of_nonneg (sq_nonneg (U ω))]
    have hu := hUnonneg ω
    by_cases hu1 : U ω ≤ 1
    · have hu2 : U ω ^ 2 ≤ 1 := by nlinarith
      nlinarith [pow_nonneg hu 6]
    · have hu1 : 1 ≤ U ω := le_of_not_ge hu1
      have hpow : 1 ≤ U ω ^ 4 := one_le_pow₀ hu1
      have hu2 : U ω ^ 2 ≤ U ω ^ 6 := by
        have hmul := mul_nonneg (sq_nonneg (U ω)) (sub_nonneg.mpr hpow)
        nlinarith
      nlinarith
  have hUsqbound : ∫ ω, U ω ^ 2 ∂disorderLaw ≤ 1 + max C 0 := by
    calc
      ∫ ω, U ω ^ 2 ∂disorderLaw ≤ ∫ ω, (1 + U ω ^ 6) ∂disorderLaw := by
        apply integral_mono hUsqInt hmajorInt
        intro ω
        have hu := hUnonneg ω
        by_cases hu1 : U ω ≤ 1
        · have hu2 : U ω ^ 2 ≤ 1 := by nlinarith
          nlinarith [pow_nonneg hu 6]
        · have hu1 : 1 ≤ U ω := le_of_not_ge hu1
          have hpow : 1 ≤ U ω ^ 4 := one_le_pow₀ hu1
          have hu2 : U ω ^ 2 ≤ U ω ^ 6 := by
            have hmul := mul_nonneg (sq_nonneg (U ω)) (sub_nonneg.mpr hpow)
            nlinarith
          nlinarith
      _ = 1 + ∫ ω, U ω ^ 6 ∂disorderLaw := by
        rw [integral_add (integrable_const (1 : ℝ)) hU6Int, integral_const]
        simp
      _ ≤ 1 + max C 0 := by linarith [hU6bound]
  exact ⟨hUsqInt, hUsqbound⟩

/-- A uniform sixth-moment bound also controls the fourth moments of compact flat marginals along the chosen subsequence. -/
theorem eventually_polymerSubseq_flatMarginal_fourthMoment_of (ϑ : ℝ)
    (hFlatSixthMomentInput : FlatSixthMomentBound ϑ) (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (χ : C_c(Plane, ℝ))
    (hχ : ∀ x, 0 ≤ χ x) :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      Integrable (fun ω => (∫ x, χ x ∂
        ((polymerMeasure ϑ (ψ n) s t ω).map Prod.fst)) ^ 4) disorderLaw ∧
      ∫ ω, (∫ x, χ x ∂
        ((polymerMeasure ϑ (ψ n) s t ω).map Prod.fst)) ^ 4 ∂disorderLaw ≤ C := by
  let τ : ℝ := (t - s) / 2
  have hτ : 0 < τ := by dsimp [τ]; linarith
  obtain ⟨C, hC⟩ := hFlatSixthMomentInput χ (τ := τ) (T := t) hτ
  have hCevent : ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω => (∫ x, |χ x| ∂
        ((polymerMeasure ϑ N s t ω).map Prod.fst)) ^ 6) disorderLaw ∧
      ∫ ω, (∫ x, |χ x| ∂
        ((polymerMeasure ϑ N s t ω).map Prod.fst)) ^ 6 ∂disorderLaw ≤ C := by
    filter_upwards [hC] with N hN
    exact hN s t hs (by dsimp [τ]; linarith) le_rfl
  have hψpos : ∀ᶠ n : ℕ in atTop, 1 ≤ ψ n :=
    hψ.tendsto_atTop.eventually (eventually_ge_atTop 1)
  refine ⟨1 + max C 0, ?_⟩
  filter_upwards [hψpos, hψ.tendsto_atTop.eventually hCevent] with n hnpos hn
  let U : Disorder → ℝ := fun ω => ∫ x, χ x ∂
    ((polymerMeasure ϑ (ψ n) s t ω).map Prod.fst)
  have hUmeas : AEMeasurable U disorderLaw := by
    have hraw := aemeasurable_rescaledP2Plane_pairing ϑ (ψ n) s t χ
    have hEq : U =ᵐ[disorderLaw] fun ω =>
        ∫ x, χ x * rescaledP2Plane ϑ (ψ n) s t x ω := by
      filter_upwards [] with ω
      exact integral_map_fst_polymerMeasure ϑ hnpos s t ω χ
    exact hraw.congr hEq.symm
  have hUnonneg (ω : Disorder) : 0 ≤ U ω := integral_nonneg fun x => hχ x
  have hUabsEq : ∀ ω : Disorder,
      ∫ x, |χ x| ∂((polymerMeasure ϑ (ψ n) s t ω).map Prod.fst) = U ω := by
    intro ω
    apply integral_congr_ae
    filter_upwards [] with x
    rw [abs_of_nonneg (hχ x)]
  have hU6Eq : (fun ω =>
      (∫ x, |χ x| ∂((polymerMeasure ϑ (ψ n) s t ω).map Prod.fst)) ^ 6) =
      fun ω => U ω ^ 6 := by
    funext ω
    rw [hUabsEq ω]
  have hU6Int : Integrable (fun ω => U ω ^ 6) disorderLaw :=
    hn.1.congr (Filter.Eventually.of_forall fun ω => congrFun hU6Eq ω)
  have hU6bound : ∫ ω, U ω ^ 6 ∂disorderLaw ≤ max C 0 := by
    have hle : ∫ ω, U ω ^ 6 ∂disorderLaw ≤ C := by
      calc
        ∫ ω, U ω ^ 6 ∂disorderLaw =
            ∫ ω, (∫ x, |χ x| ∂
              ((polymerMeasure ϑ (ψ n) s t ω).map Prod.fst)) ^ 6 ∂disorderLaw :=
          integral_congr_ae
            (Filter.Eventually.of_forall fun ω => (congrFun hU6Eq ω).symm)
        _ ≤ C := hn.2
    exact hle.trans (le_max_left _ _)
  have hmajorInt : Integrable (fun ω => 1 + U ω ^ 6) disorderLaw :=
    (integrable_const (1 : ℝ)).add hU6Int
  have hU4meas : AEStronglyMeasurable (fun ω => U ω ^ 4) disorderLaw :=
    (continuous_id.pow 4).comp_aestronglyMeasurable hUmeas.aestronglyMeasurable
  have hU4Int : Integrable (fun ω => U ω ^ 4) disorderLaw := by
    refine hmajorInt.mono' hU4meas ?_
    filter_upwards [] with ω
    rw [Real.norm_of_nonneg (pow_nonneg (hUnonneg ω) 4)]
    by_cases hu : U ω ≤ 1
    · exact (pow_le_one₀ (hUnonneg ω) hu).trans (le_add_of_nonneg_right (pow_nonneg (hUnonneg ω) 6))
    · have hu : 1 ≤ U ω := le_of_not_ge hu
      have hle : U ω ^ 4 ≤ U ω ^ 6 := by
        calc
          U ω ^ 4 = U ω ^ 4 * 1 := by ring
          _ ≤ U ω ^ 4 * U ω ^ 2 :=
            mul_le_mul_of_nonneg_left (one_le_pow₀ hu) (pow_nonneg (hUnonneg ω) 4)
          _ = U ω ^ 6 := by ring
      exact hle.trans (le_add_of_nonneg_left zero_le_one)
  have hU4bound : ∫ ω, U ω ^ 4 ∂disorderLaw ≤ 1 + max C 0 := by
    calc
      ∫ ω, U ω ^ 4 ∂disorderLaw ≤ ∫ ω, (1 + U ω ^ 6) ∂disorderLaw := by
        apply integral_mono hU4Int hmajorInt
        intro ω
        by_cases hu : U ω ≤ 1
        · exact (pow_le_one₀ (hUnonneg ω) hu).trans
            (le_add_of_nonneg_right (pow_nonneg (hUnonneg ω) 6))
        · have hu : 1 ≤ U ω := le_of_not_ge hu
          have hle : U ω ^ 4 ≤ U ω ^ 6 := by
            calc
              U ω ^ 4 = U ω ^ 4 * 1 := by ring
              _ ≤ U ω ^ 4 * U ω ^ 2 :=
                mul_le_mul_of_nonneg_left (one_le_pow₀ hu) (pow_nonneg (hUnonneg ω) 4)
              _ = U ω ^ 6 := by ring
          exact hle.trans (le_add_of_nonneg_left zero_le_one)
      _ = 1 + ∫ ω, U ω ^ 6 ∂disorderLaw := by
        rw [integral_add (integrable_const (1 : ℝ)) hU6Int, integral_const]
        simp
      _ ≤ 1 + max C 0 := by linarith [hU6bound]
  exact ⟨hU4Int, hU4bound⟩

/-- A compactly cut off smoothed-product test is uniformly approximable by finite sums
of products of compact tests on the two adjacent pair spaces. -/
theorem exists_cutoffProduct_compactTensor_approximation
    (Φ : C_c(Plane × Plane, ℝ)) (k : Plane → ℝ) (hk : Continuous k) (R : ℝ) :
    ∃ K : Set ((Plane × Plane) × (Plane × Plane)), IsCompact K ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∃ m : ℕ → ℕ,
        ∃ f g : (j : ℕ) → Fin (m j) → C_c(Plane × Plane, ℝ),
          (∀ (j : ℕ) (q : (Plane × Plane) × (Plane × Plane)),
            |(∑ i, f j i q.1 * g j i q.2) -
            (Φ (q.1.1, q.2.2) * k (q.1.2 - q.2.1) *
              ballCutoff R q.1.2 * ballCutoff R q.2.1)| ≤ C / ((j : ℝ) + 1)) ∧
          (∀ j, tsupport (fun q => ∑ i, f j i q.1 * g j i q.2) ⊆ K) ∧
          tsupport (fun q : (Plane × Plane) × (Plane × Plane) =>
            Φ (q.1.1, q.2.2) * k (q.1.2 - q.2.1) *
              ballCutoff R q.1.2 * ballCutoff R q.2.1) ⊆ K := by
  classical
  let cutoffTest : C_c(Plane, ℝ) :=
    ⟨⟨ballCutoff R, continuous_ballCutoff R⟩, hasCompactSupport_ballCutoff R⟩
  let B : C_c(Plane × Plane, ℝ) :=
    ⟨⟨fun q => (cutoffTest q.1 * cutoffTest q.2) * k (q.1 - q.2), by fun_prop⟩,
      by
      have hc : HasCompactSupport (fun q : Plane × Plane => cutoffTest q.1 * cutoffTest q.2) :=
        (compactTensorTest cutoffTest cutoffTest).hasCompactSupport
      exact hc.mul_right⟩
  let A : C_c(Plane × Plane, ℝ) := Φ
  obtain ⟨KA, hKA, ra, fa, fa', hfa, ha⟩ := exists_compactTensorSum_sequence A
  obtain ⟨KB, hKB, rb, fb, fb', hfb, hb⟩ := exists_compactTensorSum_sequence B
  let Aseq (j : ℕ) : C_c(Plane × Plane, ℝ) :=
    ∑ a : Fin (ra j), compactTensorTest (fa j a) (fa' j a)
  let Bseq (j : ℕ) : C_c(Plane × Plane, ℝ) :=
    ∑ b : Fin (rb j), compactTensorTest (fb j b) (fb' j b)
  have hKA' : IsCompact (KA ∪ tsupport (A : Plane × Plane → ℝ)) :=
    hKA.union A.hasCompactSupport
  have hKB' : IsCompact (KB ∪ tsupport (B : Plane × Plane → ℝ)) :=
    hKB.union B.hasCompactSupport
  let m (j : ℕ) := Fintype.card (Fin (ra j) × Fin (rb j))
  let e (j : ℕ) : Fin (m j) ≃ Fin (ra j) × Fin (rb j) :=
    (Fintype.equivFin (Fin (ra j) × Fin (rb j))).symm
  let f (j : ℕ) (i : Fin (m j)) : C_c(Plane × Plane, ℝ) :=
    compactTensorTest (fa j (e j i).1) (fb j (e j i).2)
  let g (j : ℕ) (i : Fin (m j)) : C_c(Plane × Plane, ℝ) :=
    compactTensorTest (fb' j (e j i).2) (fa' j (e j i).1)
  have hsum (j : ℕ) (q : (Plane × Plane) × (Plane × Plane)) :
      (∑ i, f j i q.1 * g j i q.2) =
        Aseq j (q.1.1, q.2.2) * Bseq j (q.1.2, q.2.1) := by
    calc
      (∑ i, f j i q.1 * g j i q.2) =
          ∑ ab : Fin (ra j) × Fin (rb j),
            (fa j ab.1 q.1.1 * fb j ab.2 q.1.2) *
              (fb' j ab.2 q.2.1 * fa' j ab.1 q.2.2) := by
        let T (ab : Fin (ra j) × Fin (rb j)) :=
          (fa j ab.1 q.1.1 * fb j ab.2 q.1.2) *
            (fb' j ab.2 q.2.1 * fa' j ab.1 q.2.2)
        change (∑ i : Fin (m j), T (e j i)) = ∑ ab, T ab
        exact (e j).sum_comp T
      _ = (∑ a : Fin (ra j), fa j a q.1.1 * fa' j a q.2.2) *
          (∑ b : Fin (rb j), fb j b q.1.2 * fb' j b q.2.1) := by
        rw [Fintype.sum_prod_type]
        calc
          (∑ a, ∑ b,
              (fa j a q.1.1 * fb j b q.1.2) *
                (fb' j b q.2.1 * fa' j a q.2.2)) =
              ∑ a, ∑ b,
                (fa j a q.1.1 * fa' j a q.2.2) *
                  (fb j b q.1.2 * fb' j b q.2.1) := by
            apply Finset.sum_congr rfl
            intro a ha
            apply Finset.sum_congr rfl
            intro b hb
            ring
          _ = _ := (Fintype.sum_mul_sum _ _).symm
      _ = Aseq j (q.1.1, q.2.2) * Bseq j (q.1.2, q.2.1) := by
        simp [Aseq, Bseq, compactTensorTest_apply,
          CompactlySupportedContinuousMap.sum_apply]
  have hAerr (j : ℕ) (p : Plane × Plane) :
      |Aseq j p - A p| ≤ 1 / ((j : ℝ) + 1) := by
    exact ha j p
  have hBerr (j : ℕ) (p : Plane × Plane) :
      |Bseq j p - B p| ≤ 1 / ((j : ℝ) + 1) := by
    exact hb j p
  have hAabs (p : Plane × Plane) : |A p| ≤ ‖A.toBoundedContinuousFunction‖ := by
    have h := A.toBoundedContinuousFunction.norm_coe_le_norm p
    change |A p| ≤ ‖A.toBoundedContinuousFunction‖ at h
    exact h
  have hBabs (p : Plane × Plane) : |B p| ≤ ‖B.toBoundedContinuousFunction‖ := by
    have h := B.toBoundedContinuousFunction.norm_coe_le_norm p
    change |B p| ≤ ‖B.toBoundedContinuousFunction‖ at h
    exact h
  have hAseqAbs (j : ℕ) (p : Plane × Plane) :
      |Aseq j p| ≤ ‖A.toBoundedContinuousFunction‖ + 1 := by
    have htri := abs_add_le (Aseq j p - A p) (A p)
    have hrepr : Aseq j p = (Aseq j p - A p) + A p := by ring
    rw [← hrepr] at htri
    calc
      |Aseq j p| ≤ |Aseq j p - A p| + |A p| := htri
      _ ≤ 1 / ((j : ℝ) + 1) + ‖A.toBoundedContinuousFunction‖ :=
        add_le_add (hAerr j p) (hAabs p)
      _ ≤ ‖A.toBoundedContinuousFunction‖ + 1 := by
        have hj : 1 / ((j : ℝ) + 1) ≤ 1 := by
          apply (div_le_iff₀ (by positivity)).2
          have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
          linarith
        linarith
  have hBseqAbs (j : ℕ) (p : Plane × Plane) :
      |Bseq j p| ≤ ‖B.toBoundedContinuousFunction‖ + 1 := by
    have htri := abs_add_le (Bseq j p - B p) (B p)
    have hrepr : Bseq j p = (Bseq j p - B p) + B p := by ring
    rw [← hrepr] at htri
    calc
      |Bseq j p| ≤ |Bseq j p - B p| + |B p| := htri
      _ ≤ 1 / ((j : ℝ) + 1) + ‖B.toBoundedContinuousFunction‖ :=
        add_le_add (hBerr j p) (hBabs p)
      _ ≤ ‖B.toBoundedContinuousFunction‖ + 1 := by
        have hj : 1 / ((j : ℝ) + 1) ≤ 1 := by
          apply (div_le_iff₀ (by positivity)).2
          have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
          linarith
        linarith
  let rearrange : ((Plane × Plane) × (Plane × Plane)) ≃
      ((Plane × Plane) × (Plane × Plane)) :=
    { toFun := fun q => ((q.1.1, q.2.2), (q.1.2, q.2.1))
      invFun := fun q => ((q.1.1, q.2.1), (q.2.2, q.1.2))
      left_inv := by
        intro q
        rcases q with ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩
        rfl
      right_inv := by
        intro q
        rcases q with ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩
        rfl }
  have hrearrange : Continuous rearrange := by
    change Continuous (fun q : (Plane × Plane) × (Plane × Plane) =>
      ((q.1.1, q.2.2), (q.1.2, q.2.1)))
    fun_prop
  have hsymm : Continuous rearrange.symm := by
    change Continuous (fun q : (Plane × Plane) × (Plane × Plane) =>
      ((q.1.1, q.2.1), (q.2.2, q.1.2)))
    fun_prop
  let K := rearrange.symm '' ((KA ∪ tsupport (A : Plane × Plane → ℝ)) ×ˢ
    (KB ∪ tsupport (B : Plane × Plane → ℝ)))
  have hK : IsCompact K :=
    (hKA'.prod hKB').image hsymm
  have htarget (q : (Plane × Plane) × (Plane × Plane)) :
      Φ (q.1.1, q.2.2) * k (q.1.2 - q.2.1) * ballCutoff R q.1.2 * ballCutoff R q.2.1 =
        A (q.1.1, q.2.2) * B (q.1.2, q.2.1) := by
    dsimp [A, B, cutoffTest]
    ring
  have hpoint (j : ℕ) (q : (Plane × Plane) × (Plane × Plane)) :
      |(∑ i, f j i q.1 * g j i q.2) -
        (Φ (q.1.1, q.2.2) * k (q.1.2 - q.2.1) *
          ballCutoff R q.1.2 * ballCutoff R q.2.1)| ≤
        (‖B.toBoundedContinuousFunction‖ + 1 +
          ‖A.toBoundedContinuousFunction‖) / ((j : ℝ) + 1) := by
    rw [hsum j q, htarget q]
    let a' := Aseq j (q.1.1, q.2.2)
    let a := A (q.1.1, q.2.2)
    let b' := Bseq j (q.1.2, q.2.1)
    let b := B (q.1.2, q.2.1)
    have ha' : |a' - a| ≤ 1 / ((j : ℝ) + 1) := hAerr j _
    have hb' : |b' - b| ≤ 1 / ((j : ℝ) + 1) := hBerr j _
    have haa' : |a'| ≤ ‖A.toBoundedContinuousFunction‖ + 1 := hAseqAbs j _
    have hbb' : |b'| ≤ ‖B.toBoundedContinuousFunction‖ + 1 := hBseqAbs j _
    have hab : |a| ≤ ‖A.toBoundedContinuousFunction‖ := hAabs _
    calc
      |a' * b' - a * b| = |(a' - a) * b' + a * (b' - b)| := by
        congr 1
        ring
      _ ≤ |(a' - a) * b'| + |a * (b' - b)| := abs_add_le _ _
      _ = |a' - a| * |b'| + |a| * |b' - b| := by rw [abs_mul, abs_mul]
      _ ≤ (1 / ((j : ℝ) + 1)) * (‖B.toBoundedContinuousFunction‖ + 1) +
          ‖A.toBoundedContinuousFunction‖ * (1 / ((j : ℝ) + 1)) := by
        exact add_le_add
          (mul_le_mul ha' hbb' (abs_nonneg _) (by positivity))
          (mul_le_mul hab hb' (abs_nonneg _) (by positivity))
      _ = (‖B.toBoundedContinuousFunction‖ + 1 +
          ‖A.toBoundedContinuousFunction‖) / ((j : ℝ) + 1) := by ring
  have hseq_support (j : ℕ) :
      tsupport (fun q => ∑ i, f j i q.1 * g j i q.2) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro q hq
    have hsumne : (∑ i, f j i q.1 * g j i q.2) ≠ 0 := hq
    have hprodne : Aseq j (q.1.1, q.2.2) * Bseq j (q.1.2, q.2.1) ≠ 0 := by
      rw [← hsum j q]
      exact hsumne
    have hAne : Aseq j (q.1.1, q.2.2) ≠ 0 := left_ne_zero_of_mul hprodne
    have hBne : Bseq j (q.1.2, q.2.1) ≠ 0 := right_ne_zero_of_mul hprodne
    have hAts : (q.1.1, q.2.2) ∈ tsupport (Aseq j : Plane × Plane → ℝ) :=
      subset_tsupport _ hAne
    have hBts : (q.1.2, q.2.1) ∈ tsupport (Bseq j : Plane × Plane → ℝ) :=
      subset_tsupport _ hBne
    have hArect : (q.1.1, q.2.2) ∈
        KA ∪ tsupport (A : Plane × Plane → ℝ) := by
      exact Or.inl (hfa j hAts)
    have hBrect : (q.1.2, q.2.1) ∈
        KB ∪ tsupport (B : Plane × Plane → ℝ) := by
      exact Or.inl (hfb j hBts)
    exact ⟨rearrange q, ⟨hArect, hBrect⟩, by simp [rearrange]⟩
  have htest_support :
      tsupport (fun q : (Plane × Plane) × (Plane × Plane) =>
        Φ (q.1.1, q.2.2) * k (q.1.2 - q.2.1) *
          ballCutoff R q.1.2 * ballCutoff R q.2.1) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro q hq
    have hne : A (q.1.1, q.2.2) * B (q.1.2, q.2.1) ≠ 0 := by
      rw [← htarget q]
      exact hq
    have hAne : A (q.1.1, q.2.2) ≠ 0 := left_ne_zero_of_mul hne
    have hBne : B (q.1.2, q.2.1) ≠ 0 := right_ne_zero_of_mul hne
    have hArect : (q.1.1, q.2.2) ∈
        KA ∪ tsupport (A : Plane × Plane → ℝ) :=
      Or.inr (subset_tsupport _ hAne)
    have hBrect : (q.1.2, q.2.1) ∈
        KB ∪ tsupport (B : Plane × Plane → ℝ) :=
      Or.inr (subset_tsupport _ hBne)
    exact ⟨rearrange q, ⟨hArect, hBrect⟩, by simp [rearrange]⟩
  exact ⟨K, hK, ‖B.toBoundedContinuousFunction‖ + 1 +
      ‖A.toBoundedContinuousFunction‖, by positivity, m, f, g,
    hpoint, hseq_support, htest_support⟩

/-- A compact window in two adjacent pair spaces is controlled by compact first-marginal
cutoffs on the two factors. -/
theorem compact_product_mass_le_flatCutoffs
    (K : Set ((Plane × Plane) × (Plane × Plane))) (hK : IsCompact K) :
    ∃ χμ χν : C_c(Plane, ℝ), (∀ x, 0 ≤ χμ x) ∧ (∀ x, 0 ≤ χν x) ∧
      ∀ (μ ν : Measure (Plane × Plane)) [_hν : IsLocallyFiniteMeasure ν],
        IsLocallyFiniteMeasure (μ.map Prod.fst) →
        IsLocallyFiniteMeasure (ν.map Prod.fst) →
        (μ.prod ν).real K ≤
          (∫ x, χμ x ∂(μ.map Prod.fst)) * ∫ x, χν x ∂(ν.map Prod.fst) := by
  let E : CompactExhaustion Plane := RandomMeasure.vagueCompactExhaustion Plane
  let A : Set Plane := (fun q : (Plane × Plane) × (Plane × Plane) => q.1.1) '' K
  let B : Set Plane := (fun q : (Plane × Plane) × (Plane × Plane) => q.2.1) '' K
  have hA : IsCompact A := hK.image (by fun_prop)
  have hB : IsCompact B := hK.image (by fun_prop)
  obtain ⟨m, hm⟩ := E.exists_superset_of_isCompact hA
  obtain ⟨n, hn⟩ := E.exists_superset_of_isCompact hB
  let χμ : C_c(Plane, ℝ) := RandomMeasure.vagueMassTest E m
  let χν : C_c(Plane, ℝ) := RandomMeasure.vagueMassTest E n
  refine ⟨χμ, χν, (RandomMeasure.vagueMassTest_spec E m).1,
    (RandomMeasure.vagueMassTest_spec E n).1, ?_⟩
  intro μ ν hν hμflat hνflat
  let U : Set (Plane × Plane) := {p | p.1 ∈ E m}
  let V : Set (Plane × Plane) := {p | p.1 ∈ E n}
  have hUV : K ⊆ U ×ˢ V := by
    intro q hq
    exact ⟨hm ⟨q, hq, rfl⟩, hn ⟨q, hq, rfl⟩⟩
  have hU : MeasurableSet U := (E.isCompact m).isClosed.measurableSet.preimage measurable_fst
  have hV : MeasurableSet V := (E.isCompact n).isClosed.measurableSet.preimage measurable_fst
  have hμmap : (μ.map Prod.fst) (E m) = μ U := by
    rw [Measure.map_apply measurable_fst (E.isCompact m).isClosed.measurableSet]
    rfl
  have hνmap : (ν.map Prod.fst) (E n) = ν V := by
    rw [Measure.map_apply measurable_fst (E.isCompact n).isClosed.measurableSet]
    rfl
  have hμflatCompact : IsFiniteMeasureOnCompacts (μ.map Prod.fst) :=
    @isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure Plane _ _ _ hμflat
  have hνflatCompact : IsFiniteMeasureOnCompacts (ν.map Prod.fst) :=
    @isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure Plane _ _ _ hνflat
  have hμU : μ U < ⊤ := by
    rw [← hμmap]
    exact hμflatCompact.lt_top_of_isCompact (E.isCompact m)
  have hνV : ν V < ⊤ := by
    rw [← hνmap]
    exact hνflatCompact.lt_top_of_isCompact (E.isCompact n)
  have hUVfinite : (μ.prod ν) (U ×ˢ V) ≠ ⊤ := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top hμU.ne hνV.ne
  have hμwindow : μ.real U ≤ ∫ x, χμ x ∂(μ.map Prod.fst) := by
    rw [measureReal_def, ← hμmap]
    exact RandomMeasure.vague_window_mass_le_test E ⟨μ.map Prod.fst, hμflat⟩ m
  have hνwindow : ν.real V ≤ ∫ x, χν x ∂(ν.map Prod.fst) := by
    rw [measureReal_def, ← hνmap]
    exact RandomMeasure.vague_window_mass_le_test E ⟨ν.map Prod.fst, hνflat⟩ n
  calc
    (μ.prod ν).real K ≤ (μ.prod ν).real (U ×ˢ V) := measureReal_mono hUV hUVfinite
    _ = μ.real U * ν.real V := by rw [measureReal_prod_prod]
    _ ≤ (∫ x, χμ x ∂(μ.map Prod.fst)) *
        ∫ x, χν x ∂(ν.map Prod.fst) :=
      mul_le_mul hμwindow hνwindow (measureReal_nonneg) (integral_nonneg (fun x =>
        (RandomMeasure.vagueMassTest_spec E m).1 x))

/-- A finite tensor-sum pairing on adjacent time intervals converges jointly in distribution with the compact pairing over their full interval. -/
theorem polymerSubseqLimit_cutoffTensorSum_joint_tendstoInDistribution
    (ϑ : ℝ) (D : Set ℝ) (ψ : ℕ → ℕ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsPolymerSubseqLimit ϑ D ψ P Z)
    {s₀ s₁ s₂ : ℝ} (hs₀ : s₀ ∈ D) (hs₁ : s₁ ∈ D) (hs₂ : s₂ ∈ D)
    (hs₀₁ : s₀ < s₁) (hs₁₂ : s₁ < s₂) (r : ℕ)
    (f g : Fin r → C_c(Plane × Plane, ℝ)) (Φ : C_c(Plane × Plane, ℝ)) :
    TendstoInDistribution
      (fun n (ω : Disorder) =>
        (∑ i : Fin r,
          (∫ p, f i p ∂polymerMeasure ϑ (ψ n) s₀ s₁ ω) *
            (∫ p, g i p ∂polymerMeasure ϑ (ψ n) s₁ s₂ ω),
          ∫ p, Φ p ∂polymerMeasure ϑ (ψ n) s₀ s₂ ω))
      atTop
      (fun ω =>
        (∑ i : Fin r, (∫ p, f i p ∂Z s₀ s₁ ω) * (∫ p, g i p ∂Z s₁ s₂ ω),
          ∫ p, Φ p ∂Z s₀ s₂ ω))
      (fun _ => disorderLaw) P := by
  let tail : Fin (r + r) → ℝ := Fin.addCases (fun _ => s₀) (fun _ => s₁)
  let endTail : Fin (r + r) → ℝ := Fin.addCases (fun _ => s₁) (fun _ => s₂)
  let s : Fin (r + r + 1) → ℝ := Fin.cons s₀ tail
  let t : Fin (r + r + 1) → ℝ := Fin.cons s₂ endTail
  let φ : Fin (r + r + 1) → C_c(Plane × Plane, ℝ) := Fin.cons Φ (Fin.addCases f g)
  let χ : Fin (r + r + 1) → C_c(Plane, ℝ) := fun _ => 0
  have htimes : ∀ i : Fin (r + r + 1), s i ∈ D ∧ t i ∈ D ∧ s i < t i := by
    intro i
    refine Fin.cases ?_ ?_ i
    · simp only [s, t, Fin.cons_zero]
      exact ⟨hs₀, hs₂, by linarith⟩
    · intro j
      simp only [s, t, Fin.cons_succ]
      refine Fin.addCases ?_ ?_ j
      · intro i
        simp only [tail, endTail, Fin.addCases_left]
        exact ⟨hs₀, hs₁, hs₀₁⟩
      · intro i
        simp only [tail, endTail, Fin.addCases_right]
        exact ⟨hs₁, hs₂, hs₁₂⟩
  let H : (Fin (r + r + 1) → ℝ × ℝ) → ℝ × ℝ := fun v =>
    (∑ i : Fin r,
        (v (Fin.succ (Fin.castAdd r i))).1 *
          (v (Fin.succ (Fin.natAdd r i))).1,
      (v 0).1)
  have hH : Continuous H := by fun_prop
  have hdist := hZ.2 (r + r + 1) s t htimes φ χ
  have hcomp := hdist.continuous_comp hH
  have hAdd (i : Fin r) : i.addNat r = Fin.natAdd r i := by
    ext
    simp [Fin.natAdd, Fin.addNat, Nat.add_comm]
  simpa only [Function.comp_def, H, s, t, tail, endTail, φ, χ,
    Fin.cons_zero, Fin.cons_succ, Fin.addCases_left, Fin.addCases_right] using hcomp

/-- Both pairings are integrable, and their tensor-approximation error is controlled by the uniform approximation error and the compact-window mass. -/
theorem cutoffProduct_tensorSum_integral_error
    (μ ν : Measure (Plane × Plane))
    [hμ : IsLocallyFiniteMeasure μ] [hν : IsLocallyFiniteMeasure ν]
    (K : Set ((Plane × Plane) × (Plane × Plane))) (hK : IsCompact K)
    (C : ℝ)
    (F : ((Plane × Plane) × (Plane × Plane)) → ℝ)
    (hFcont : Continuous F) (hFsupport : tsupport F ⊆ K)
    (m : ℕ → ℕ)
    (f g : (j : ℕ) → Fin (m j) → C_c(Plane × Plane, ℝ))
    (happrox : ∀ j q, |(∑ i, f j i q.1 * g j i q.2) - F q| ≤ C / ((j : ℝ) + 1))
    (hsupport : ∀ j, tsupport (fun q => ∑ i, f j i q.1 * g j i q.2) ⊆ K)
    (j : ℕ) :
    Integrable F (μ.prod ν) ∧
      Integrable (fun q => ∑ i, f j i q.1 * g j i q.2) (μ.prod ν) ∧
      |(∫ q, F q ∂(μ.prod ν)) -
        ∫ q, (∑ i, f j i q.1 * g j i q.2) ∂(μ.prod ν)| ≤
        C / ((j : ℝ) + 1) * (μ.prod ν).real K := by
  classical
  let H (j : ℕ) (q : (Plane × Plane) × (Plane × Plane)) : ℝ :=
    ∑ i, f j i q.1 * g j i q.2
  have hHcont : Continuous (H j) := by fun_prop
  have hFcompact : HasCompactSupport F := by
    apply HasCompactSupport.of_support_subset_isCompact hK
    exact (subset_tsupport F).trans hFsupport
  have hHcompact : HasCompactSupport (H j) := by
    apply HasCompactSupport.of_support_subset_isCompact hK
    exact (subset_tsupport (H j)).trans (by simpa [H] using hsupport j)
  have hFint : Integrable F (μ.prod ν) :=
    hFcont.integrable_of_hasCompactSupport hFcompact
  have hHint : Integrable (H j) (μ.prod ν) :=
    hHcont.integrable_of_hasCompactSupport hHcompact
  have hprodCompact : IsFiniteMeasureOnCompacts (μ.prod ν) :=
    @isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
      ((Plane × Plane) × (Plane × Plane)) _ _ _ inferInstance
  have hKfinite : (μ.prod ν) K < ⊤ := hprodCompact.lt_top_of_isCompact hK
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hHsupport : tsupport (H j) ⊆ K := by simpa [H] using hsupport j
  have hmajorInt : Integrable (K.indicator (fun _ => C / ((j : ℝ) + 1))) (μ.prod ν) := by
    apply (integrableOn_const hKfinite.ne).integrable_indicator hKmeas
  have hmajor (q : (Plane × Plane) × (Plane × Plane)) :
      |F q - H j q| ≤ K.indicator (fun _ => C / ((j : ℝ) + 1)) q := by
    by_cases hq : q ∈ K
    · rw [Set.indicator_of_mem hq]
      change |F q - ∑ i, f j i q.1 * g j i q.2| ≤ C / ((j : ℝ) + 1)
      rw [abs_sub_comm]
      exact happrox j q
    · have hFzero : F q = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro h
        exact hq (hFsupport h)
      have hHzero : H j q = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro h
        exact hq (hHsupport h)
      rw [Set.indicator_of_notMem hq, hFzero, hHzero]
      simp
  have hmajorIntVal :
      (∫ q, K.indicator (fun _ => C / ((j : ℝ) + 1)) q ∂(μ.prod ν)) =
        C / ((j : ℝ) + 1) * (μ.prod ν).real K := by
    simpa [Measure.real, smul_eq_mul, mul_comm] using
      (integral_indicator_const (C / ((j : ℝ) + 1)) hKmeas
        (μ := μ.prod ν) (s := K))
  refine ⟨hFint, hHint, ?_⟩
  rw [← integral_sub hFint hHint]
  calc
    |∫ q, (F q - H j q) ∂(μ.prod ν)| =
        ‖∫ q, (F q - H j q) ∂(μ.prod ν)‖ := by rw [Real.norm_eq_abs]
    _ ≤ ∫ q, ‖F q - H j q‖ ∂(μ.prod ν) := norm_integral_le_integral_norm _
    _ = ∫ q, |F q - H j q| ∂(μ.prod ν) := by
      simp only [Real.norm_eq_abs]
    _ ≤ ∫ q, K.indicator (fun _ => C / ((j : ℝ) + 1)) q ∂(μ.prod ν) :=
      integral_mono (hFint.sub hHint).norm hmajorInt hmajor
    _ = C / ((j : ℝ) + 1) * (μ.prod ν).real K := hmajorIntVal

/-- Joint convergence of a compactly cut off smoothed product and the direct long-block pairing.
The compact tensor approximation is controlled in L¹ by the flat-marginal second moments. -/
theorem polymerSubseqLimit_cutoffProduct_joint_tendstoInDistribution
    (ϑ : ℝ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ) (D : Set ℝ) (ψ : ℕ → ℕ)
    (hψ : StrictMono ψ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsPolymerSubseqLimit ϑ D ψ P Z)
    {s₀ s₁ s₂ : ℝ} (hs₀D : s₀ ∈ D) (hs₁D : s₁ ∈ D) (hs₂D : s₂ ∈ D)
    (hs₀ : 0 ≤ s₀) (hs₀₁ : s₀ < s₁) (hs₁₂ : s₁ < s₂)
    (Φ : C_c(Plane × Plane, ℝ)) (k : Plane → ℝ) (hk : Continuous k) (R : ℝ) :
    TendstoInDistribution
      (fun n (ω : Disorder) =>
        (∫ q, Φ (q.1.1, q.2.2) * k (q.1.2 - q.2.1) *
            ballCutoff R q.1.2 * ballCutoff R q.2.1 ∂
              ((polymerMeasure ϑ (ψ n) s₀ s₁ ω).prod
                (polymerMeasure ϑ (ψ n) s₁ s₂ ω)),
          ∫ p, Φ p ∂polymerMeasure ϑ (ψ n) s₀ s₂ ω))
      atTop
      (fun ω =>
        (∫ q, Φ (q.1.1, q.2.2) * k (q.1.2 - q.2.1) *
            ballCutoff R q.1.2 * ballCutoff R q.2.1 ∂((Z s₀ s₁ ω).prod (Z s₁ s₂ ω)),
          ∫ p, Φ p ∂Z s₀ s₂ ω))
      (fun _ => disorderLaw) P := by
  classical
  obtain ⟨K, hK, C, hC, m, f, g, happrox, hsumSupport, hFsupport⟩ :=
    exists_cutoffProduct_compactTensor_approximation Φ k hk R
  let F : ((Plane × Plane) × (Plane × Plane)) → ℝ := fun q =>
    Φ (q.1.1, q.2.2) * k (q.1.2 - q.2.1) *
      ballCutoff R q.1.2 * ballCutoff R q.2.1
  have hΦouter : Continuous (fun q : (Plane × Plane) × (Plane × Plane) =>
      (q.1.1, q.2.2)) := by fun_prop
  have hkdiff : Continuous (fun q : (Plane × Plane) × (Plane × Plane) =>
      q.1.2 - q.2.1) := by fun_prop
  have hFcont : Continuous F := by
    change Continuous (fun q : (Plane × Plane) × (Plane × Plane) =>
      Φ (q.1.1, q.2.2) * k (q.1.2 - q.2.1) *
        ballCutoff R q.1.2 * ballCutoff R q.2.1)
    exact (((Φ.continuous.comp hΦouter).mul (hk.comp hkdiff)).mul
      ((continuous_ballCutoff R).comp (by fun_prop))).mul
        ((continuous_ballCutoff R).comp (by fun_prop))
  have hFsupport' : tsupport F ⊆ K := by simpa [F] using hFsupport
  obtain ⟨χ₀, χ₁, hχ₀, hχ₁, hmass⟩ := compact_product_mass_le_flatCutoffs K hK
  obtain ⟨C₀, hC₀N⟩ := eventually_polymerSubseq_flatMarginal_secondMoment_of
    ϑ hFlatSixthMomentInput ψ hψ hs₀ hs₀₁ χ₀ hχ₀
  have hs₁ : 0 ≤ s₁ := hs₀.trans hs₀₁.le
  obtain ⟨C₁, hC₁N⟩ := eventually_polymerSubseq_flatMarginal_secondMoment_of
    ϑ hFlatSixthMomentInput ψ hψ hs₁ hs₁₂ χ₁ hχ₁
  obtain ⟨C₀L, hC₀LInt, hC₀Lbound⟩ := polymerSubseqLimit_flatMarginal_secondMoment_of
    ϑ hFlatSixthMomentInput D ψ hψ P Z hZ hs₀D hs₁D hs₀₁ hs₀ χ₀ hχ₀
  obtain ⟨C₁L, hC₁LInt, hC₁Lbound⟩ := polymerSubseqLimit_flatMarginal_secondMoment_of
    ϑ hFlatSixthMomentInput D ψ hψ P Z hZ hs₁D hs₂D hs₁₂ hs₁ χ₁ hχ₁
  let s : Fin 2 → ℝ := fun i => if (i : ℕ) = 0 then s₀ else s₁
  let t : Fin 2 → ℝ := fun i => if (i : ℕ) = 0 then s₁ else s₂
  let χ : Fin 2 → C_c(Plane, ℝ) := fun i => if (i : ℕ) = 0 then χ₀ else χ₁
  let φ : Fin 2 → C_c(Plane × Plane, ℝ) := fun _ => 0
  have htimes : ∀ i : Fin 2, s i ∈ D ∧ t i ∈ D ∧ s i < t i := by
    intro i
    fin_cases i <;> simp [s, t, hs₀D, hs₁D, hs₂D, hs₀₁, hs₁₂]
  let Hflat : (Fin 2 → ℝ × ℝ) → (Fin 2 → ℝ) := fun v i => (v i).2
  have hHflat : Continuous Hflat := by fun_prop
  have hflatDist : TendstoInDistribution
      (fun n (ω : Disorder) (i : Fin 2) =>
        ∫ x, χ i x ∂((polymerMeasure ϑ (ψ n) (s i) (t i) ω).map Prod.fst))
      atTop
      (fun ω i => ∫ x, χ i x ∂((Z (s i) (t i) ω).map Prod.fst))
      (fun _ => disorderLaw) P := by
    have h := (hZ.2 2 s t htimes φ χ).continuous_comp hHflat
    apply h.congr
    · intro n
      filter_upwards [] with ω
      funext i
      simp [Hflat, s, t, φ, χ]
    · filter_upwards [] with ω
      funext i
      simp [Hflat, s, t, φ, χ]
  let U : ℕ → Disorder → ℝ := fun n ω =>
    ∫ x, χ₀ x ∂((polymerMeasure ϑ (ψ n) s₀ s₁ ω).map Prod.fst)
  let V : ℕ → Disorder → ℝ := fun n ω =>
    ∫ x, χ₁ x ∂((polymerMeasure ϑ (ψ n) s₁ s₂ ω).map Prod.fst)
  let UL : Ω → ℝ := fun ω => ∫ x, χ₀ x ∂((Z s₀ s₁ ω).map Prod.fst)
  let VL : Ω → ℝ := fun ω => ∫ x, χ₁ x ∂((Z s₁ s₂ ω).map Prod.fst)
  have hUmeas (n : ℕ) : AEMeasurable (U n) disorderLaw := by
    have h := (measurable_pi_apply (0 : Fin 2)).comp_aemeasurable
      (hflatDist.forall_aemeasurable n)
    exact h.congr (Filter.Eventually.of_forall fun ω => by simp [U, s, t, χ])
  have hVmeas (n : ℕ) : AEMeasurable (V n) disorderLaw := by
    have h := (measurable_pi_apply (1 : Fin 2)).comp_aemeasurable
      (hflatDist.forall_aemeasurable n)
    exact h.congr (Filter.Eventually.of_forall fun ω => by simp [V, s, t, χ])
  have hULmeas : AEMeasurable UL P := by
    have h := (measurable_pi_apply (0 : Fin 2)).comp_aemeasurable
      hflatDist.aemeasurable_limit
    exact h.congr (Filter.Eventually.of_forall fun ω => by simp [UL, s, t, χ])
  have hVLmeas : AEMeasurable VL P := by
    have h := (measurable_pi_apply (1 : Fin 2)).comp_aemeasurable
      hflatDist.aemeasurable_limit
    exact h.congr (Filter.Eventually.of_forall fun ω => by simp [VL, s, t, χ])
  let μN : ℕ → Disorder → Measure (Plane × Plane) := fun n ω =>
    polymerMeasure ϑ (ψ n) s₀ s₁ ω
  let νN : ℕ → Disorder → Measure (Plane × Plane) := fun n ω =>
    polymerMeasure ϑ (ψ n) s₁ s₂ ω
  let TL : Ω → ℝ := fun ω => ∫ q, F q ∂((Z s₀ s₁ ω).prod (Z s₁ s₂ ω))
  let TN : ℕ → Disorder → ℝ := fun n ω => ∫ q, F q ∂((μN n ω).prod (νN n ω))
  let YN : ℕ → Disorder → ℝ := fun n ω => ∫ p, Φ p ∂polymerMeasure ϑ (ψ n) s₀ s₂ ω
  let YL : Ω → ℝ := fun ω => ∫ p, Φ p ∂Z s₀ s₂ ω
  let TjN : ℕ → ℕ → Disorder → ℝ := fun j n ω =>
    ∑ i, (∫ p, f j i p ∂μN n ω) * ∫ p, g j i p ∂νN n ω
  let TjL : ℕ → Ω → ℝ := fun j ω =>
    ∑ i, (∫ p, f j i p ∂Z s₀ s₁ ω) * ∫ p, g j i p ∂Z s₁ s₂ ω
  let H : ℕ → ((Plane × Plane) × (Plane × Plane)) → ℝ := fun j q =>
    ∑ i, f j i q.1 * g j i q.2
  let encode (p : ℝ × ℝ) : Fin 2 → ℝ := Fin.cons p.1 (fun _ => p.2)
  have hencode : Continuous encode := by fun_prop
  let X : ℕ → Disorder → Fin 2 → ℝ := fun n ω => encode (TN n ω, YN n ω)
  let Y : ℕ → ℕ → Disorder → Fin 2 → ℝ := fun j n ω => encode (TjN j n ω, YN n ω)
  let Ylim : ℕ → Ω → Fin 2 → ℝ := fun j ω => encode (TjL j ω, YL ω)
  let L : Ω → Fin 2 → ℝ := fun ω => encode (TL ω, YL ω)
  have hjoint (j : ℕ) : TendstoInDistribution
      (fun n ω => (TjN j n ω, YN n ω)) atTop (fun ω => (TjL j ω, YL ω))
      (fun _ => disorderLaw) P := by
    simpa [TjN, TjL, YN, YL, μN, νN] using
      polymerSubseqLimit_cutoffTensorSum_joint_tendstoInDistribution
        ϑ D ψ P Z hZ hs₀D hs₁D hs₂D hs₀₁ hs₁₂ (m j) (f j) (g j) Φ
  have hY (j : ℕ) : TendstoInDistribution (Y j) atTop (Ylim j)
      (fun _ => disorderLaw) P := by
    have h := (hjoint j).continuous_comp hencode
    exact h.congr
      (fun n => Filter.Eventually.of_forall fun ω => by simp [Y])
      (Filter.Eventually.of_forall fun ω => by simp [Ylim])
  have hYjNmeas (j n : ℕ) : AEMeasurable (TjN j n) disorderLaw := by
    have h := (measurable_fst.comp_aemeasurable ((hjoint j).forall_aemeasurable n))
    exact h.congr (Filter.Eventually.of_forall fun ω => by simp [TjN, μN, νN])
  have hYjLmeas (j : ℕ) : AEMeasurable (TjL j) P := by
    have h := measurable_fst.comp_aemeasurable (hjoint j).aemeasurable_limit
    exact h.congr (Filter.Eventually.of_forall fun ω => by simp [TjL])
  have hTnmeas (n : ℕ) : AEMeasurable (TN n) disorderLaw := by
    apply aemeasurable_of_tendsto_metrizable_ae atTop (fun j => hYjNmeas j n)
    filter_upwards [] with ω
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hμ : IsLocallyFiniteMeasure (μN n ω) :=
      isLocallyFiniteMeasure_polymerMeasure ϑ (ψ n) s₀ s₁ ω
    have hν : IsLocallyFiniteMeasure (νN n ω) :=
      isLocallyFiniteMeasure_polymerMeasure ϑ (ψ n) s₁ s₂ ω
    have hlarge : ∀ᶠ j : ℕ in atTop,
        C * ((μN n ω).prod (νN n ω)).real K / ε < j :=
      tendsto_natCast_atTop_atTop.eventually
        (eventually_gt_atTop (C * ((μN n ω).prod (νN n ω)).real K / ε))
    filter_upwards [hlarge] with j hj
    have hApproxJ := @cutoffProduct_tensorSum_integral_error
      (μN n ω) (νN n ω) hμ hν K hK C F hFcont hFsupport' m f g happrox hsumSupport j
    have hInt := @integrable_integral_finiteTensorSum_eq
      (μN n ω) (νN n ω) hμ hν (m j) (f j) (g j)
    have hmass : ((μN n ω).prod (νN n ω)).real K ≥ 0 := measureReal_nonneg
    have hj' : C * ((μN n ω).prod (νN n ω)).real K < ε * (j : ℝ) := by
      simpa only [mul_comm] using (div_lt_iff₀ hε).mp hj
    have hden : 0 < (j : ℝ) + 1 := by positivity
    have hsmall : C / ((j : ℝ) + 1) * ((μN n ω).prod (νN n ω)).real K < ε := by
      have hrewrite : C / ((j : ℝ) + 1) * ((μN n ω).prod (νN n ω)).real K =
          C * ((μN n ω).prod (νN n ω)).real K / ((j : ℝ) + 1) := by ring
      rw [hrewrite]
      apply (div_lt_iff₀ hden).2
      nlinarith
    have hpoint : |TN n ω - TjN j n ω| ≤
        C / ((j : ℝ) + 1) * ((μN n ω).prod (νN n ω)).real K := by
      change |(∫ q, F q ∂(μN n ω).prod (νN n ω)) -
          ∑ i, (∫ p, f j i p ∂μN n ω) * ∫ p, g j i p ∂νN n ω| ≤ _
      rw [← hInt.2]
      exact hApproxJ.2.2
    calc
      dist (TjN j n ω) (TN n ω) = |TN n ω - TjN j n ω| := by
        rw [Real.dist_eq, abs_sub_comm]
      _ ≤ C / ((j : ℝ) + 1) * ((μN n ω).prod (νN n ω)).real K := hpoint
      _ < ε := hsmall
  have hTLmeas : AEMeasurable TL P := by
    apply aemeasurable_of_tendsto_metrizable_ae atTop hYjLmeas
    filter_upwards [(hZ.1 s₀ hs₀D s₁ hs₁D hs₀₁).2,
      (hZ.1 s₁ hs₁D s₂ hs₂D hs₁₂).2] with ω hloc₀ hloc₁
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hlarge : ∀ᶠ j : ℕ in atTop,
        C * ((Z s₀ s₁ ω).prod (Z s₁ s₂ ω)).real K / ε < j :=
      tendsto_natCast_atTop_atTop.eventually
        (eventually_gt_atTop (C * ((Z s₀ s₁ ω).prod (Z s₁ s₂ ω)).real K / ε))
    filter_upwards [hlarge] with j hj
    have hApproxJ := @cutoffProduct_tensorSum_integral_error
      (Z s₀ s₁ ω) (Z s₁ s₂ ω) hloc₀.1 hloc₁.1 K hK C F hFcont hFsupport' m f g
      happrox hsumSupport j
    have hInt := @integrable_integral_finiteTensorSum_eq
      (Z s₀ s₁ ω) (Z s₁ s₂ ω) hloc₀.1 hloc₁.1 (m j) (f j) (g j)
    have hj' : C * ((Z s₀ s₁ ω).prod (Z s₁ s₂ ω)).real K < ε * (j : ℝ) :=
      by simpa only [mul_comm] using (div_lt_iff₀ hε).mp hj
    have hden : 0 < (j : ℝ) + 1 := by positivity
    have hsmall : C / ((j : ℝ) + 1) *
        ((Z s₀ s₁ ω).prod (Z s₁ s₂ ω)).real K < ε := by
      have hrewrite : C / ((j : ℝ) + 1) *
          ((Z s₀ s₁ ω).prod (Z s₁ s₂ ω)).real K =
            C * ((Z s₀ s₁ ω).prod (Z s₁ s₂ ω)).real K / ((j : ℝ) + 1) := by ring
      rw [hrewrite]
      apply (div_lt_iff₀ hden).2
      nlinarith
    have hpoint : |TL ω - TjL j ω| ≤
        C / ((j : ℝ) + 1) * ((Z s₀ s₁ ω).prod (Z s₁ s₂ ω)).real K := by
      change |(∫ q, F q ∂(Z s₀ s₁ ω).prod (Z s₁ s₂ ω)) -
          ∑ i, (∫ p, f j i p ∂Z s₀ s₁ ω) * ∫ p, g j i p ∂Z s₁ s₂ ω| ≤ _
      rw [← hInt.2]
      exact hApproxJ.2.2
    calc
      dist (TjL j ω) (TL ω) = |TL ω - TjL j ω| := by
        rw [Real.dist_eq, abs_sub_comm]
      _ ≤ C / ((j : ℝ) + 1) * ((Z s₀ s₁ ω).prod (Z s₁ s₂ ω)).real K := hpoint
      _ < ε := hsmall
  have hmassN (n : ℕ) (ω : Disorder) :
      ((μN n ω).prod (νN n ω)).real K ≤ U n ω * V n ω := by
    have hμ : IsLocallyFiniteMeasure (μN n ω) :=
      isLocallyFiniteMeasure_polymerMeasure ϑ (ψ n) s₀ s₁ ω
    have hν : IsLocallyFiniteMeasure (νN n ω) :=
      isLocallyFiniteMeasure_polymerMeasure ϑ (ψ n) s₁ s₂ ω
    have h := @hmass (μN n ω) (νN n ω) hν
      (isLocallyFiniteMeasure_polymerMarginal ϑ (ψ n) s₀ s₁ ω)
      (isLocallyFiniteMeasure_polymerMarginal ϑ (ψ n) s₁ s₂ ω)
    simpa [U, V, μN, νN] using h
  have hloc₀ : ∀ᵐ ω ∂P,
      IsLocallyFiniteMeasure (Z s₀ s₁ ω) ∧
        IsLocallyFiniteMeasure ((Z s₀ s₁ ω).map Prod.fst) :=
    (hZ.1 s₀ hs₀D s₁ hs₁D hs₀₁).2
  have hloc₁ : ∀ᵐ ω ∂P,
      IsLocallyFiniteMeasure (Z s₁ s₂ ω) ∧
        IsLocallyFiniteMeasure ((Z s₁ s₂ ω).map Prod.fst) :=
    (hZ.1 s₁ hs₁D s₂ hs₂D hs₁₂).2
  have hmassL : ∀ᵐ ω ∂P,
      ((Z s₀ s₁ ω).prod (Z s₁ s₂ ω)).real K ≤ UL ω * VL ω := by
    filter_upwards [hloc₀, hloc₁] with ω h₀ h₁
    have h := @hmass (Z s₀ s₁ ω) (Z s₁ s₂ ω) h₁.1 h₀.2 h₁.2
    simpa [UL, VL] using h
  have hTNpoint (j n : ℕ) (ω : Disorder) :
      |TN n ω - TjN j n ω| ≤
        C / ((j : ℝ) + 1) * ((μN n ω).prod (νN n ω)).real K := by
    have hμ : IsLocallyFiniteMeasure (μN n ω) :=
      isLocallyFiniteMeasure_polymerMeasure ϑ (ψ n) s₀ s₁ ω
    have hν : IsLocallyFiniteMeasure (νN n ω) :=
      isLocallyFiniteMeasure_polymerMeasure ϑ (ψ n) s₁ s₂ ω
    have hApproxJ := @cutoffProduct_tensorSum_integral_error
      (μN n ω) (νN n ω) hμ hν K hK C F hFcont hFsupport' m f g happrox hsumSupport j
    have hInt := @integrable_integral_finiteTensorSum_eq
      (μN n ω) (νN n ω) hμ hν (m j) (f j) (g j)
    change |(∫ q, F q ∂(μN n ω).prod (νN n ω)) -
        ∑ i, (∫ p, f j i p ∂μN n ω) * ∫ p, g j i p ∂νN n ω| ≤ _
    rw [← hInt.2]
    exact hApproxJ.2.2
  have hTLpoint (j : ℕ) (ω : Ω)
      (h₀ : IsLocallyFiniteMeasure (Z s₀ s₁ ω))
      (h₁ : IsLocallyFiniteMeasure (Z s₁ s₂ ω)) :
      |TL ω - TjL j ω| ≤
        C / ((j : ℝ) + 1) * ((Z s₀ s₁ ω).prod (Z s₁ s₂ ω)).real K := by
    have hApproxJ := @cutoffProduct_tensorSum_integral_error
      (Z s₀ s₁ ω) (Z s₁ s₂ ω) h₀ h₁ K hK C F hFcont hFsupport' m f g
      happrox hsumSupport j
    have hInt := @integrable_integral_finiteTensorSum_eq
      (Z s₀ s₁ ω) (Z s₁ s₂ ω) h₀ h₁ (m j) (f j) (g j)
    change |(∫ q, F q ∂(Z s₀ s₁ ω).prod (Z s₁ s₂ ω)) -
        ∑ i, (∫ p, f j i p ∂Z s₀ s₁ ω) * ∫ p, g j i p ∂Z s₁ s₂ ω| ≤ _
    rw [← hInt.2]
    exact hApproxJ.2.2
  have hnormEncode (a b c : ℝ) :
      ‖encode (a, b) - encode (c, b)‖ ≤ |a - c| := by
    rw [Pi.norm_def]
    have hs : Finset.univ.sup
        (fun i : Fin 2 => ‖(encode (a, b) - encode (c, b)) i‖₊) ≤ ‖a - c‖₊ := by
      apply Finset.sup_le
      intro i hi
      fin_cases i <;> simp [encode]
    calc
      ↑(Finset.univ.sup (fun i : Fin 2 => ‖(encode (a, b) - encode (c, b)) i‖₊)) ≤
          ↑‖a - c‖₊ := by exact_mod_cast hs
      _ = |a - c| := by simp
  have hXY : ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop, ∀ᶠ n : ℕ in atTop,
      ∫⁻ ω, ENNReal.ofReal ‖X n ω - Y j n ω‖ ∂disorderLaw ≤ ENNReal.ofReal ε := by
    intro ε hε
    let B : ℝ := C * (max C₀ 0 + max C₁ 0)
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hlarge : ∀ᶠ j : ℕ in atTop, B / ε < (j : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (B / ε))
    filter_upwards [hlarge] with j hj
    have hj' : B < ε * (j : ℝ) := by
      simpa only [mul_comm] using (div_lt_iff₀ hε).mp hj
    have hden : 0 < (j : ℝ) + 1 := by positivity
    have hsmall : B / ((j : ℝ) + 1) ≤ ε := by
      apply (div_le_iff₀ hden).2
      dsimp [B]
      nlinarith
    filter_upwards [hC₀N.and hC₁N] with n hn
    have hU2 : Integrable (fun ω => U n ω ^ 2) disorderLaw := by
      simpa [U] using hn.1.1
    have hV2 : Integrable (fun ω => V n ω ^ 2) disorderLaw := by
      simpa [V] using hn.2.1
    have hUbound : ∫ ω, U n ω ^ 2 ∂disorderLaw ≤ C₀ := by
      simpa [U] using hn.1.2
    have hVbound : ∫ ω, V n ω ^ 2 ∂disorderLaw ≤ C₁ := by
      simpa [V] using hn.2.2
    have hc : 0 ≤ C / ((j : ℝ) + 1) := by positivity
    have hpoint : ∀ᵐ ω ∂disorderLaw,
        |TN n ω - TjN j n ω| ≤ C / ((j : ℝ) + 1) * (U n ω * V n ω) :=
      Filter.Eventually.of_forall fun ω =>
        (hTNpoint j n ω).trans
          (mul_le_mul_of_nonneg_left (hmassN n ω) hc)
    obtain ⟨hInt, hbound⟩ := integrable_abs_sub_le_product_sq_moments
      disorderLaw (hTnmeas n).aestronglyMeasurable
      (hYjNmeas j n).aestronglyMeasurable (hUmeas n).aestronglyMeasurable
      (hVmeas n).aestronglyMeasurable hU2 hV2 hUbound hVbound hc hpoint
    have hbound' : ∫ ω, |TN n ω - TjN j n ω| ∂disorderLaw ≤ B / ((j : ℝ) + 1) := by
      calc
        _ ≤ C / ((j : ℝ) + 1) * (max C₀ 0 + max C₁ 0) := hbound
        _ = B / ((j : ℝ) + 1) := by dsimp [B]; ring
    have hlin : ∫⁻ ω, ENNReal.ofReal |TN n ω - TjN j n ω| ∂disorderLaw ≤
        ENNReal.ofReal (B / ((j : ℝ) + 1)) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hInt
        (Filter.Eventually.of_forall fun ω => abs_nonneg _)]
      exact ENNReal.ofReal_le_ofReal hbound'
    calc
      ∫⁻ ω, ENNReal.ofReal ‖X n ω - Y j n ω‖ ∂disorderLaw ≤
          ∫⁻ ω, ENNReal.ofReal |TN n ω - TjN j n ω| ∂disorderLaw := by
        apply lintegral_mono
        intro ω
        exact ENNReal.ofReal_le_ofReal (by
          simpa [X, Y] using hnormEncode (TN n ω) (YN n ω) (TjN j n ω))
      _ ≤ ENNReal.ofReal (B / ((j : ℝ) + 1)) := hlin
      _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hsmall
  have hYlim : ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
      ∫⁻ ω, ENNReal.ofReal ‖Ylim j ω - L ω‖ ∂P ≤ ENNReal.ofReal ε := by
    intro ε hε
    let B : ℝ := C * (max C₀L 0 + max C₁L 0)
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hlarge : ∀ᶠ j : ℕ in atTop, B / ε < (j : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (B / ε))
    filter_upwards [hlarge] with j hj
    have hj' : B < ε * (j : ℝ) := by
      simpa only [mul_comm] using (div_lt_iff₀ hε).mp hj
    have hden : 0 < (j : ℝ) + 1 := by positivity
    have hsmall : B / ((j : ℝ) + 1) ≤ ε := by
      apply (div_le_iff₀ hden).2
      dsimp [B]
      nlinarith
    have hc : 0 ≤ C / ((j : ℝ) + 1) := by positivity
    have hpoint : ∀ᵐ ω ∂P,
        |TjL j ω - TL ω| ≤ C / ((j : ℝ) + 1) * (UL ω * VL ω) := by
      filter_upwards [hloc₀, hloc₁, hmassL] with ω h₀ h₁ hmassω
      calc
        |TjL j ω - TL ω| = |TL ω - TjL j ω| := abs_sub_comm _ _
        _ ≤ C / ((j : ℝ) + 1) * ((Z s₀ s₁ ω).prod (Z s₁ s₂ ω)).real K :=
          hTLpoint j ω h₀.1 h₁.1
        _ ≤ C / ((j : ℝ) + 1) * (UL ω * VL ω) :=
          mul_le_mul_of_nonneg_left hmassω hc
    have hU2 : Integrable (fun ω => UL ω ^ 2) P := by simpa [UL] using hC₀LInt
    have hV2 : Integrable (fun ω => VL ω ^ 2) P := by simpa [VL] using hC₁LInt
    have hUbound : ∫ ω, UL ω ^ 2 ∂P ≤ C₀L := by simpa [UL] using hC₀Lbound
    have hVbound : ∫ ω, VL ω ^ 2 ∂P ≤ C₁L := by simpa [VL] using hC₁Lbound
    obtain ⟨hInt, hbound⟩ := integrable_abs_sub_le_product_sq_moments
      P (hYjLmeas j).aestronglyMeasurable hTLmeas.aestronglyMeasurable
      hULmeas.aestronglyMeasurable hVLmeas.aestronglyMeasurable
      hU2 hV2 hUbound hVbound hc hpoint
    have hbound' : ∫ ω, |TjL j ω - TL ω| ∂P ≤ B / ((j : ℝ) + 1) := by
      calc
        _ ≤ C / ((j : ℝ) + 1) * (max C₀L 0 + max C₁L 0) := hbound
        _ = B / ((j : ℝ) + 1) := by dsimp [B]; ring
    have hlin : ∫⁻ ω, ENNReal.ofReal |TjL j ω - TL ω| ∂P ≤
        ENNReal.ofReal (B / ((j : ℝ) + 1)) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hInt
        (Filter.Eventually.of_forall fun ω => abs_nonneg _)]
      exact ENNReal.ofReal_le_ofReal hbound'
    calc
      ∫⁻ ω, ENNReal.ofReal ‖Ylim j ω - L ω‖ ∂P ≤
          ∫⁻ ω, ENNReal.ofReal |TjL j ω - TL ω| ∂P := by
        apply lintegral_mono
        intro ω
        exact ENNReal.ofReal_le_ofReal (by
          simpa [Ylim, L] using hnormEncode (TjL j ω) (YL ω) (TL ω))
      _ ≤ ENNReal.ofReal (B / ((j : ℝ) + 1)) := hlin
      _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hsmall
  let sDirect : Fin 1 → ℝ := fun _ => s₀
  let tDirect : Fin 1 → ℝ := fun _ => s₂
  let φDirect : Fin 1 → C_c(Plane × Plane, ℝ) := fun _ => Φ
  let χDirect : Fin 1 → C_c(Plane, ℝ) := fun _ => 0
  have hDirectTimes : ∀ i : Fin 1,
      sDirect i ∈ D ∧ tDirect i ∈ D ∧ sDirect i < tDirect i := by
    intro i
    fin_cases i
    exact ⟨hs₀D, hs₂D, by linarith⟩
  have hDirectDist := hZ.2 1 sDirect tDirect hDirectTimes φDirect χDirect
  have hYNmeas (n : ℕ) : AEMeasurable (YN n) disorderLaw := by
    have h := measurable_fst.comp_aemeasurable
      ((measurable_pi_apply (0 : Fin 1)).comp_aemeasurable
        (hDirectDist.forall_aemeasurable n))
    exact h.congr (Filter.Eventually.of_forall fun ω => by
      simp [YN, φDirect, sDirect, tDirect, χDirect])
  have hYLmeas : AEMeasurable YL P := by
    have h := measurable_fst.comp_aemeasurable
      ((measurable_pi_apply (0 : Fin 1)).comp_aemeasurable
        hDirectDist.aemeasurable_limit)
    exact h.congr (Filter.Eventually.of_forall fun ω => by
      simp [YL, φDirect, sDirect, tDirect, χDirect])
  have hXm (n : ℕ) : AEMeasurable (X n) disorderLaw := by
    exact hencode.measurable.comp_aemeasurable ((hTnmeas n).prodMk (hYNmeas n))
  have hLm : AEMeasurable L P := by
    exact hencode.measurable.comp_aemeasurable (hTLmeas.prodMk hYLmeas)
  have hencoded := Critical2DKPZ.JointConvergence.tendstoInDistribution_of_approx
    X Y Ylim L hY hYlim hXY hXm hLm
  have hdecode : Continuous (fun v : Fin 2 → ℝ => (v 0, v 1)) := by fun_prop
  have hpair := hencoded.continuous_comp hdecode
  exact hpair.congr
    (fun n => Filter.Eventually.of_forall fun ω => by
      simp [X, encode, TN, YN, μN, νN, F])
    (Filter.Eventually.of_forall fun ω => by
      simp [L, encode, TL, YL, F])

end Critical2DKPZ.SHF.Flow

end
