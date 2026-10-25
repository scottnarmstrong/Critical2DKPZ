/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.EndpointBounds
public import Critical2DKPZ.NonGaussian.EndpointEhrhard
public import Critical2DKPZ.NonGaussian.Rigidity
public import Critical2DKPZ.RandomMeasure.GeneralProduct
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Tactic

/-! # Vanishing endpoint-field perturbations -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open Critical2DKPZ.JointConvergence Critical2DKPZ.SHF.Positivity
open Critical2DKPZ.SHF.Limit Critical2DKPZ.LocalSobolev
open scoped BoundedContinuousFunction ENNReal Topology

universe u

namespace Critical2DKPZ.NonGaussian

private noncomputable def endpointLogTerminal (f : Plane →ᵇ ℝ) {c : ℝ} (hc : 0 < c)
    (hf : ∀ y, c ≤ f y) : Plane →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun y => Real.log (f y), by
      apply continuous_iff_continuousAt.mpr
      intro y
      exact (Real.continuousAt_log (ne_of_gt (lt_of_lt_of_le hc (hf y)))).comp
        f.continuous.continuousAt⟩
    (2 * max |Real.log c| |Real.log ‖f‖|) (by
      intro x y
      rw [Real.dist_eq]
      let B : ℝ := max |Real.log c| |Real.log ‖f‖|
      have hB : 0 ≤ B := by dsimp [B]; positivity
      have hnorm (z : Plane) : f z ≤ ‖f‖ :=
        le_trans (le_abs_self (f z)) (f.norm_coe_le_norm z)
      have hbound (z : Plane) : |Real.log (f z)| ≤ B := by
        have hlow : Real.log c ≤ Real.log (f z) := Real.log_le_log hc (hf z)
        have hhigh : Real.log (f z) ≤ Real.log ‖f‖ :=
          Real.log_le_log (lt_of_lt_of_le hc (hf z)) (hnorm z)
        apply abs_le.mpr
        constructor
        · calc
            -B ≤ -|Real.log c| := by dsimp [B]; exact neg_le_neg (le_max_left _ _)
            _ ≤ Real.log c := neg_abs_le _
            _ ≤ Real.log (f z) := hlow
        · exact hhigh.trans ((le_abs_self _).trans (le_max_right _ _))
      calc
        |Real.log (f x) - Real.log (f y)| ≤
            |Real.log (f x)| + |Real.log (f y)| := abs_sub _ _
        _ ≤ B + B := add_le_add (hbound x) (hbound y)
        _ = 2 * B := by ring)

private theorem endpointLogTerminal_exp (f : Plane →ᵇ ℝ) {c : ℝ} (hc : 0 < c)
    (hf : ∀ y, c ≤ f y) (y : Plane) :
    Real.exp (endpointLogTerminal f hc hf y) = f y := by
  simp only [endpointLogTerminal, BoundedContinuousFunction.mkOfBound_coe]
  exact Real.exp_log (lt_of_lt_of_le hc (hf y))


private theorem bounded_tendsto_eLpNorm {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {D : ℕ → Ω → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hDmeas : ∀ n, AEMeasurable (D n) P)
    (hDbound : ∀ n, ∀ᵐ ω ∂P, |D n ω| ≤ K)
    (hDconv : TendstoInMeasure P D atTop fun _ => 0)
    {p : ℝ≥0∞} (hpTop : p ≠ ∞) :
    Tendsto (fun n => eLpNorm (D n) p P) atTop (𝓝 0) := by
  by_cases hpZero : p = 0
  · subst p
    have hz (n : ℕ) : eLpNorm (D n) 0 P = 0 :=
      eLpNorm_exponent_zero (hDmeas n).aestronglyMeasurable
    simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞))
      atTop (𝓝 (0 : ℝ≥0∞)))
  have hMem (q : ℝ≥0∞) : ∀ n, MemLp (D n) q P := by
    intro n
    apply MemLp.of_bound (hDmeas n).aestronglyMeasurable K
    filter_upwards [hDbound n] with ω hω
    simpa only [Real.norm_eq_abs] using hω
  have hUI (q : ℝ≥0∞) (hqOne : 1 ≤ q) (hqTop : q ≠ ∞) :
      UnifIntegrable D q P := by
    apply unifIntegrable_of hqOne hqTop (fun n => (hDmeas n).aestronglyMeasurable)
    intro ε hε
    let C : NNReal := ⟨K + 1, add_nonneg hK zero_le_one⟩
    have hCK : K < (C : ℝ) := by
      dsimp [C]
      exact lt_add_of_pos_right K zero_lt_one
    refine ⟨C, fun n => ?_⟩
    have hcut : ({ω | C ≤ ‖D n ω‖₊}.indicator (D n)) =ᵐ[P] fun _ => 0 := by
      filter_upwards [hDbound n] with ω hω
      by_cases hmem : C ≤ ‖D n ω‖₊
      · have hmemR : (C : ℝ) ≤ ‖D n ω‖ := by exact_mod_cast hmem
        have hnorm : ‖D n ω‖ ≤ K := by simpa only [Real.norm_eq_abs] using hω
        exact False.elim ((not_le_of_gt (lt_of_le_of_lt hnorm hCK)) hmemR)
      · have hnot : ω ∉ {ω | C ≤ ‖D n ω‖₊} := by
          change ¬ C ≤ ‖D n ω‖₊
          exact hmem
        rw [Set.indicator_of_notMem hnot]
    rw [eLpNorm_congr_ae hcut]
    simp
  have hConvOne : Tendsto (fun n => eLpNorm (D n) 1 P) atTop (𝓝 0) := by
    have h := (tendstoInMeasure_iff_tendsto_Lp_finite (μ := P)
      (p := (1 : ℝ≥0∞)) le_rfl (by norm_num) (hMem 1)
      (MemLp.zero' : MemLp (fun _ : Ω => (0 : ℝ)) 1 P)).mp
      ⟨hDconv, hUI 1 le_rfl (by norm_num)⟩
    have heq : (fun n => eLpNorm (D n - (fun _ : Ω => (0 : ℝ))) 1 P) =
        fun n => eLpNorm (D n) 1 P := by
      funext n
      congr 1
      funext ω
      simp
    exact heq ▸ h
  by_cases hpOne : 1 ≤ p
  · have h := (tendstoInMeasure_iff_tendsto_Lp_finite (μ := P) hpOne hpTop
      (hMem p) (MemLp.zero' : MemLp (fun _ : Ω => (0 : ℝ)) p P)).mp
      ⟨hDconv, hUI p hpOne hpTop⟩
    have heq : (fun n => eLpNorm (D n - (fun _ : Ω => (0 : ℝ))) p P) =
        fun n => eLpNorm (D n) p P := by
      funext n
      congr 1
      funext ω
      simp
    exact heq ▸ h
  · have hpLtOne : p < 1 := lt_of_not_ge hpOne
    have hcmp (n : ℕ) : eLpNorm (D n) p P ≤ eLpNorm (D n) 1 P := by
      have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpLtOne.le
        (hDmeas n).aestronglyMeasurable
      simpa using h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hConvOne
      (fun _ => zero_le) hcmp

private noncomputable def clippedDifference (K : ℝ) (hK : 0 ≤ K) : (ℝ × ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun z => max (-K) (min K (z.2 - z.1)), by fun_prop⟩ (2 * K) (by
      intro z w
      rw [Real.dist_eq]
      have hbound (q : ℝ × ℝ) : |max (-K) (min K (q.2 - q.1))| ≤ K := by
        apply abs_le.mpr
        constructor
        · exact le_max_left _ _
        · exact max_le (by linarith) (min_le_left _ _)
      calc
        |max (-K) (min K (z.2 - z.1)) - max (-K) (min K (w.2 - w.1))|
            ≤ |max (-K) (min K (z.2 - z.1))| +
              |max (-K) (min K (w.2 - w.1))| := abs_sub _ _
        _ ≤ K + K := add_le_add (hbound z) (hbound w)
        _ = 2 * K := by ring)

private theorem clippedDifference_eq {K : ℝ} (hK : 0 ≤ K) (z : ℝ × ℝ)
    (hbound : |z.2 - z.1| ≤ K) : clippedDifference K hK z = z.2 - z.1 := by
  have hlow : -K ≤ z.2 - z.1 := (abs_le.mp hbound).1
  have hupp : z.2 - z.1 ≤ K := (abs_le.mp hbound).2
  change max (-K) (min K (z.2 - z.1)) = z.2 - z.1
  rw [min_eq_right hupp, max_eq_right hlow]

private theorem endpoint_pair_laws_tight {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X Y : ℕ → Ω → ℝ} {K : ℝ}
    (hX : ∀ n, AEMeasurable (X n) P) (hY : ∀ n, AEMeasurable (Y n) P)
    (hbound : ∀ n, ∀ᵐ ω ∂P, |Y n ω - X n ω| ≤ K)
    (hXtight : IsTightMeasureSet (Set.range fun n => P.map (X n))) :
    IsTightMeasureSet (Set.range fun n =>
      (P.map fun ω => (X n ω, Y n ω)) : Set (Measure (ℝ × ℝ))) := by
  classical
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hXtight
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨KX, hKX, hKXtail⟩ := hXtight ε hε
  let KD : Set ℝ := Set.Icc (-K) K
  let KY : Set ℝ := (fun z : ℝ × ℝ => z.1 + z.2) '' (KX ×ˢ KD)
  let Kpair : Set (ℝ × ℝ) := KX ×ˢ KY
  have hKD : IsCompact KD := by
    dsimp [KD]
    exact isCompact_Icc
  have hKXKD : IsCompact (KX ×ˢ KD) := hKX.prod hKD
  have hKY : IsCompact KY := by
    dsimp [KY]
    exact hKXKD.image (by fun_prop)
  have hKpair : IsCompact Kpair := by
    dsimp [Kpair]
    exact hKX.prod hKY
  refine ⟨Kpair, hKpair, ?_⟩
  rintro μ ⟨n, rfl⟩
  have hpair : AEMeasurable (fun ω => (X n ω, Y n ω)) P := (hX n).prodMk (hY n)
  have hbad : P {ω | ¬ |Y n ω - X n ω| ≤ K} = 0 := ae_iff.mp (hbound n)
  have hcover : (fun ω => (X n ω, Y n ω)) ⁻¹' Kpairᶜ ⊆
      (X n) ⁻¹' KXᶜ ∪ {ω | ¬ |Y n ω - X n ω| ≤ K} := by
    intro ω hω
    by_cases hx : X n ω ∈ KX
    · by_cases hb : |Y n ω - X n ω| ≤ K
      · have hd : Y n ω - X n ω ∈ KD := (abs_le.mp hb)
        have hy : Y n ω ∈ KY := by
          refine ⟨(X n ω, Y n ω - X n ω), ⟨hx, hd⟩, ?_⟩
          dsimp
          ring
        exact False.elim (hω ⟨hx, hy⟩)
      · exact Or.inr hb
    · exact Or.inl hx
  have hKpairClosed : IsClosed Kpair := hKpair.isClosed
  have hmap : (P.map fun ω => (X n ω, Y n ω)) Kpairᶜ =
      P ((fun ω => (X n ω, Y n ω)) ⁻¹' Kpairᶜ) :=
    Measure.map_apply_of_aemeasurable hpair hKpairClosed.measurableSet.compl
  calc
    (P.map fun ω => (X n ω, Y n ω)) Kpairᶜ =
        P ((fun ω => (X n ω, Y n ω)) ⁻¹' Kpairᶜ) := hmap
    _ ≤ P ((X n) ⁻¹' KXᶜ ∪ {ω | ¬ |Y n ω - X n ω| ≤ K}) := measure_mono hcover
    _ ≤ P ((X n) ⁻¹' KXᶜ) + P {ω | ¬ |Y n ω - X n ω| ≤ K} := measure_union_le _ _
    _ = P ((X n) ⁻¹' KXᶜ) := by rw [hbad, add_zero]
    _ = (P.map (X n)) KXᶜ :=
      (Measure.map_apply_of_aemeasurable (hX n) hKX.isClosed.measurableSet.compl).symm
    _ ≤ ε := hKXtail _ ⟨n, rfl⟩

private theorem endpoint_map_pair {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {X Y : Ω → ℝ} (hpair : AEMeasurable (fun ω => (X ω, Y ω)) P)
    {g : ℝ × ℝ → ℝ} (hg : Measurable g) :
    (P.map fun ω => (X ω, Y ω)).map g = P.map (fun ω => g (X ω, Y ω)) := by
  rw [AEMeasurable.map_map_of_aemeasurable hg.aemeasurable hpair]
  rfl

set_option linter.style.haveILetI false in
private theorem endpoint_exists_rigidity_subsequence {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {Xn Yn : ℕ → Ω → ℝ} {X : Ω → ℝ}
    {K : ℝ} (σ : NNReal) (hK : 0 ≤ K) (hXn : ∀ n, AEMeasurable (Xn n) P)
    (hYn : ∀ n, AEMeasurable (Yn n) P) (hXmem : MemLp X 2 P)
    (hXlaw : P.map X = gaussianReal 0 σ)
    (hXconv : Tendsto (fun n => eLpNorm (Xn n - X) 2 P) atTop (𝓝 0))
    (hXcenter : ∀ n, Integrable (Xn n) P ∧ (∫ ω, Xn n ω ∂P) = 0)
    (hYcenter : ∀ n, Integrable (Yn n) P ∧ (∫ ω, Yn n ω ∂P) = 0)
    (hbound : ∀ n, ∀ᵐ ω ∂P, |Yn n ω - Xn n ω| ≤ K)
    (hYE : ∀ n, IsEhrhardType (P.map (Yn n)))
    (hXYE : ∀ n, IsEhrhardType (P.map fun ω => Xn n ω + Yn n ω)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoInMeasure P (fun n ω => Yn (φ n) ω - Xn (φ n) ω) atTop fun _ => 0 := by
  classical
  letI : IsCompletelyMetrizableSpace ℝ := inferInstance
  letI : PseudoMetrizableSpace ℝ := inferInstance
  letI : SeparableSpace ℝ := inferInstance
  letI : MetrizableSpace (ProbabilityMeasure ℝ) := inferInstance
  letI : IsCompletelyMetrizableSpace (ℝ × ℝ) := inferInstance
  letI : PseudoMetrizableSpace (ℝ × ℝ) := inferInstance
  letI : SeparableSpace (ℝ × ℝ) := inferInstance
  letI : MetrizableSpace (ProbabilityMeasure (ℝ × ℝ)) := inferInstance
  have hXmeas : AEMeasurable X P := hXmem.aemeasurable
  have hXconvMeasure : TendstoInMeasure P Xn atTop X :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hXconv
  have hXdist : TendstoInDistribution Xn atTop X (fun _ => P) P :=
    hXconvMeasure.tendstoInDistribution_of_aemeasurable hXn hXmeas
  let Xlaw : ℕ → ProbabilityMeasure ℝ := fun n => ⟨P.map (Xn n), inferInstance⟩
  have hXweak : Tendsto Xlaw atTop (𝓝 ⟨P.map X, inferInstance⟩) := by
    simpa [Xlaw] using hXdist.tendsto
  have hXcompactInsert : IsCompact (insert ⟨P.map X, inferInstance⟩ (Set.range Xlaw)) :=
    hXweak.isCompact_insert_range
  have hXclosureSub : closure (Set.range Xlaw) ⊆
      insert ⟨P.map X, inferInstance⟩ (Set.range Xlaw) :=
    closure_minimal (by intro μ hμ; exact Or.inr hμ) hXcompactInsert.isClosed
  have hXcompactClosure : IsCompact (closure (Set.range Xlaw)) :=
    hXcompactInsert.of_isClosed_subset isClosed_closure hXclosureSub
  have hXtight := isTightMeasureSet_of_isCompact_closure (S := Set.range Xlaw)
    hXcompactClosure
  have hXtightMeasure : IsTightMeasureSet (Set.range fun n => P.map (Xn n)) := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hXtight ⊢
    intro ε hε
    obtain ⟨C, hC, htail⟩ := hXtight ε hε
    refine ⟨C, hC, ?_⟩
    rintro μ ⟨n, rfl⟩
    apply htail (Xlaw n)
    exact ⟨Xlaw n, ⟨n, rfl⟩, rfl⟩
  have hpairTight := endpoint_pair_laws_tight P hXn hYn hbound hXtightMeasure
  let pair : ℕ → Ω → ℝ × ℝ := fun n ω => (Xn n ω, Yn n ω)
  have hpairMeas (n : ℕ) : AEMeasurable (pair n) P := (hXn n).prodMk (hYn n)
  let ν : ℕ → ProbabilityMeasure (ℝ × ℝ) := fun n => ⟨P.map (pair n), inferInstance⟩
  obtain ⟨φ, νlim, hφ, hνlim⟩ :=
    Critical2DKPZ.RandomMeasure.exists_subseq_tendsto_of_tight_probability_laws ν hpairTight
  let νsub : ℕ → ProbabilityMeasure (ℝ × ℝ) := fun n => ν (φ n)
  have hνsub : Tendsto νsub atTop (𝓝 νlim) := by simpa [νsub] using hνlim
  have hpairMargX (n : ℕ) : (ν n).map Prod.fst = Xlaw n := by
    apply Subtype.ext
    change (P.map (pair n)).map Prod.fst = P.map (Xn n)
    rw [endpoint_map_pair P (hpairMeas n) (by fun_prop)]
  have hνfirst : Tendsto (fun n => (νsub n).map Prod.fst) atTop
      (𝓝 (νlim.map Prod.fst)) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous νsub νlim hνsub (by fun_prop)
  have hXweakSub : Tendsto (fun n => Xlaw (φ n)) atTop
      (𝓝 ⟨P.map X, inferInstance⟩) := hXweak.comp hφ.tendsto_atTop
  have hνfirst' : Tendsto (fun n => Xlaw (φ n)) atTop
      (𝓝 (νlim.map Prod.fst)) := by
    apply hνfirst.congr'
    filter_upwards [] with n
    exact hpairMargX (φ n)
  have hfirstEq : νlim.map Prod.fst = ⟨P.map X, inferInstance⟩ :=
    tendsto_nhds_unique hνfirst' hXweakSub
  have hXlawLim : (νlim.map Prod.fst : Measure ℝ) = gaussianReal 0 σ := by
    calc
      (νlim.map Prod.fst : Measure ℝ) = P.map X := congrArg Subtype.val hfirstEq
      _ = gaussianReal 0 σ := hXlaw
  let Ylaw : ℕ → ProbabilityMeasure ℝ := fun n => (νsub n).map Prod.snd
  let YlawLim : ProbabilityMeasure ℝ := νlim.map Prod.snd
  have hYweak : Tendsto Ylaw atTop (𝓝 YlawLim) := by
    simpa [Ylaw, YlawLim] using
      ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous νsub νlim hνsub (by fun_prop)
  have hpairMargY (n : ℕ) : (νsub n).map Prod.snd =
      (⟨P.map (Yn (φ n)), inferInstance⟩ : ProbabilityMeasure ℝ) := by
    apply Subtype.ext
    change (P.map (pair (φ n))).map Prod.snd = P.map (Yn (φ n))
    rw [endpoint_map_pair P (hpairMeas (φ n)) (by fun_prop)]
  have hYlawFinite (n : ℕ) : IsEhrhardType (Ylaw n : Measure ℝ) := by
    rw [show (Ylaw n : Measure ℝ) = P.map (Yn (φ n)) from congrArg Subtype.val (hpairMargY n)]
    exact hYE (φ n)
  have hYEhrhard := Provider.ehrhardType_weakClosure Ylaw YlawLim hYweak hYlawFinite
  let Sumlaw : ℕ → ProbabilityMeasure ℝ := fun n =>
    (νsub n).map (fun z : ℝ × ℝ => z.1 + z.2)
  let SumlawLim : ProbabilityMeasure ℝ :=
    νlim.map (fun z : ℝ × ℝ => z.1 + z.2)
  have hSumweak : Tendsto Sumlaw atTop (𝓝 SumlawLim) := by
    simpa [Sumlaw, SumlawLim] using
      ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous νsub νlim hνsub (by fun_prop)
  have hpairMargSum (n : ℕ) : (νsub n).map (fun z : ℝ × ℝ => z.1 + z.2) =
      (⟨P.map (fun ω => Xn (φ n) ω + Yn (φ n) ω), inferInstance⟩ : ProbabilityMeasure ℝ) := by
    apply Subtype.ext
    dsimp [νsub, ν]
    change (P.map (pair (φ n))).map (fun z : ℝ × ℝ => z.1 + z.2) =
      P.map (fun ω => Xn (φ n) ω + Yn (φ n) ω)
    rw [endpoint_map_pair P (hpairMeas (φ n)) (by fun_prop)]
  have hSumFinite (n : ℕ) : IsEhrhardType (Sumlaw n : Measure ℝ) := by
    rw [show (Sumlaw n : Measure ℝ) = P.map (fun ω => Xn (φ n) ω + Yn (φ n) ω) from
      congrArg Subtype.val (hpairMargSum n)]
    exact hXYE (φ n)
  have hSumEhrhard := Provider.ehrhardType_weakClosure Sumlaw SumlawLim hSumweak hSumFinite
  let xlim : ℝ × ℝ → ℝ := fun z => z.1
  let ylim : ℝ × ℝ → ℝ := fun z => z.2
  let dlim : ℝ × ℝ → ℝ := fun z => z.2 - z.1
  let Q : Measure (ℝ × ℝ) := νlim
  have hdiffCont : Continuous (fun z : ℝ × ℝ => |z.2 - z.1|) := by fun_prop
  let Cbound : Set (ℝ × ℝ) := {z | |z.2 - z.1| ≤ K}
  have hCboundClosed : IsClosed Cbound := by
    dsimp [Cbound]
    exact isClosed_Iic.preimage hdiffCont
  have hCboundn (n : ℕ) : (νsub n : Measure (ℝ × ℝ)) Cbound = 1 := by
    have hbad : P {ω | ¬ |Yn (φ n) ω - Xn (φ n) ω| ≤ K} = 0 :=
      ae_iff.mp (hbound (φ n))
    have hcomp : P ((pair (φ n)) ⁻¹' Cbound)ᶜ = 0 := by
      have hset : ((pair (φ n)) ⁻¹' Cbound)ᶜ =
          {ω | ¬ |Yn (φ n) ω - Xn (φ n) ω| ≤ K} := by
        ext ω
        simp [Cbound, pair]
      rw [hset]
      exact hbad
    change (P.map (pair (φ n))) Cbound = 1
    rw [Measure.map_apply_of_aemeasurable (hpairMeas (φ n)) hCboundClosed.measurableSet]
    rw [measure_of_measure_compl_eq_zero hcomp, measure_univ]
  have hportBound := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto
    hνsub hCboundClosed
  have hlimBoundMass : 1 ≤ Q Cbound := by
    have hlimsup : atTop.limsup (fun n => (νsub n : Measure (ℝ × ℝ)) Cbound) = 1 := by
      simp only [hCboundn, limsup_const]
    rw [hlimsup] at hportBound
    exact hportBound
  have hlimBoundMassEq : Q Cbound = 1 := by
    apply le_antisymm
    · calc
        Q Cbound ≤ Q Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    · exact hlimBoundMass
  have hlimBoundComp : Q Cboundᶜ = 0 := by
    calc
      Q Cboundᶜ = Q Set.univ - Q Cbound :=
        measure_compl hCboundClosed.measurableSet (measure_ne_top _ _)
      _ = 0 := by rw [measure_univ, hlimBoundMassEq]; simp
  have hlimBound : ∀ᵐ z ∂Q, |ylim z - xlim z| ≤ K := by
    rw [ae_iff]
    change Q Cboundᶜ = 0
    exact hlimBoundComp
  have hDmem : MemLp dlim 1 Q := by
    apply MemLp.of_bound (by fun_prop) K
    filter_upwards [hlimBound] with z hz
    simpa [dlim, Real.norm_eq_abs] using hz
  have hDint : Integrable dlim Q := hDmem.integrable (by norm_num)
  let q : (ℝ × ℝ) →ᵇ ℝ := clippedDifference K hK
  have hqFinite (n : ℕ) : ∫ z, q z ∂(ν n : Measure (ℝ × ℝ)) = 0 := by
    have hDmean : ∫ ω, Yn n ω - Xn n ω ∂P = 0 := by
      rw [integral_sub (hYcenter n).1 (hXcenter n).1, (hYcenter n).2, (hXcenter n).2]
      simp
    calc
      _ = ∫ ω, q (pair n ω) ∂P :=
        integral_map (hpairMeas n) q.continuous.measurable.aestronglyMeasurable
      _ = ∫ ω, Yn n ω - Xn n ω ∂P := by
        apply integral_congr_ae
        filter_upwards [hbound n] with ω hω
        exact clippedDifference_eq hK (pair n ω) (by simpa [pair] using hω)
      _ = 0 := hDmean
  have hqTend := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hνsub) q
  have hqFiniteSub (n : ℕ) : ∫ z, q z ∂(νsub n : Measure (ℝ × ℝ)) = 0 := by
    simpa [νsub] using hqFinite (φ n)
  have hqZero : Tendsto (fun n => ∫ z, q z ∂(νsub n : Measure (ℝ × ℝ))) atTop (𝓝 0) := by
    simpa only [hqFiniteSub] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hqLimZero : (∫ z, q z ∂Q) = 0 := by
    exact tendsto_nhds_unique hqTend hqZero
  have hqDlim : q =ᵐ[Q] dlim := by
    filter_upwards [hlimBound] with z hz
    change clippedDifference K hK z = z.2 - z.1
    exact clippedDifference_eq hK z (by simpa [dlim, ylim, xlim] using hz)
  have hDmeanLim : (∫ z, dlim z ∂Q) = 0 := by
    calc
      _ = ∫ z, q z ∂Q := integral_congr_ae hqDlim.symm
      _ = 0 := hqLimZero
  have hXlimAEM : AEMeasurable xlim Q := by fun_prop
  have hYlimAEM : AEMeasurable ylim Q := by fun_prop
  have hXlawOnQ : Q.map xlim = gaussianReal 0 σ := by
    simpa [Q, xlim] using hXlawLim
  have hXhas : HasLaw xlim (gaussianReal 0 σ) Q :=
    ⟨hXlimAEM, hXlawOnQ⟩
  have hXlimMem : MemLp xlim 2 Q :=
    hXhas.memLp (memLp_id_gaussianReal' 2 (by norm_num))
  have hXlimInt : Integrable xlim Q := hXlimMem.integrable (by norm_num)
  have hYlimInt : Integrable ylim Q := by
    have hEq : (fun z : ℝ × ℝ => ylim z) = fun z => xlim z + dlim z := by
      funext z
      simp [ylim, xlim, dlim]
    change Integrable (fun z => ylim z) Q
    rw [hEq]
    exact hXlimInt.add hDint
  have hYlimZero : (∫ z, ylim z ∂Q) = 0 := by
    have hEq : (fun z : ℝ × ℝ => ylim z) = fun z => xlim z + dlim z := by
      funext z
      simp [ylim, xlim, dlim]
    rw [hEq, integral_add hXlimInt hDint]
    rw [hXhas.integral_eq, integral_id_gaussianReal, hDmeanLim]
    simp
  have hsumMap : Q.map (fun z : ℝ × ℝ => xlim z + ylim z) =
      (νlim.map (fun z : ℝ × ℝ => z.1 + z.2) : Measure ℝ) := by
    rfl
  have hYEhrhardLim : IsEhrhardType (Q.map ylim) := by
    simpa [Q, ylim, YlawLim] using hYEhrhard
  have hXYEhrhardLim : IsEhrhardType (Q.map fun z : ℝ × ℝ => xlim z + ylim z) := by
    simpa [Q, xlim, ylim, SumlawLim] using hSumEhrhard
  have hRigid := ae_eq_of_isEhrhardType_of_gaussian Q xlim ylim hXlimAEM hYlimAEM
    σ hXlawOnQ hYlimZero K hlimBound hYEhrhardLim hXYEhrhardLim
  have hDzero : dlim =ᵐ[Q] fun _ => 0 := by
    filter_upwards [hRigid] with z hz
    change z.2 - z.1 = 0
    have hz' : z.2 = z.1 := by simpa [ylim, xlim] using hz
    linarith
  have hdlimAEM : AEMeasurable dlim Q := by
    dsimp [dlim]
    fun_prop
  have hDlawZero (ε : ℝ) (hε : 0 < ε) :
      (νlim.map dlim : Measure ℝ) {x | ε ≤ |x|} = 0 := by
    change Q.map dlim {x | ε ≤ |x|} = 0
    have hset : {x : ℝ | ε ≤ |x|} = (fun x : ℝ => |x|) ⁻¹' Set.Ici ε := by
      ext x
      rfl
    rw [hset, Measure.map_apply_of_aemeasurable hdlimAEM
      (isClosed_Ici.preimage continuous_abs).measurableSet]
    have hbadzero : Q {z | dlim z ≠ 0} = 0 := by
      apply ae_iff.mp
      filter_upwards [hDzero] with z hz
      simpa using hz
    apply measure_mono_null
    · intro z hz
      change ε ≤ |dlim z| at hz
      change dlim z ≠ 0
      intro hzero
      rw [hzero] at hz
      exact (not_le_of_gt hε) (by simpa using hz)
    · exact hbadzero
  have hDlaw : Tendsto (fun n => (νsub n).map dlim) atTop (𝓝 (νlim.map dlim)) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous νsub νlim hνsub (by fun_prop)
  have hDconv : TendstoInMeasure P (fun n ω => Yn (φ n) ω - Xn (φ n) ω) atTop fun _ => 0 := by
    rw [tendstoInMeasure_iff_norm]
    intro ε hε
    let E : Set ℝ := {x | ε ≤ |x|}
    have hEclosed : IsClosed E := by
      dsimp [E]
      exact isClosed_Ici.preimage continuous_abs
    have hfront : (νlim.map dlim : Measure ℝ) (frontier E) = 0 := by
      apply measure_mono_null (frontier_subset_closure.trans ?_) (hDlawZero ε hε)
      rw [hEclosed.closure_eq]
    have hmeasure := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
      (E := E) hDlaw hfront
    have hmeasure' : Tendsto (fun n => P {ω | ε ≤ |Yn (φ n) ω - Xn (φ n) ω|})
        atTop (𝓝 0) := by
      have heq (n : ℕ) : P {ω | ε ≤ |Yn (φ n) ω - Xn (φ n) ω|} =
          ((νsub n).map dlim : Measure ℝ) E := by
        change P {ω | ε ≤ |Yn (φ n) ω - Xn (φ n) ω|} =
          ((P.map (pair (φ n))).map dlim) E
        rw [endpoint_map_pair P (hpairMeas (φ n)) (by fun_prop)]
        rw [Measure.map_apply_of_aemeasurable (by fun_prop) hEclosed.measurableSet]
        rfl
      have h := hmeasure.congr' (Filter.Eventually.of_forall fun n => (heq n).symm)
      have hlimzero : ((νlim.map dlim : Measure ℝ) E) = 0 := by
        simpa [E] using hDlawZero ε hε
      simpa only [hlimzero] using h
    simpa [Real.norm_eq_abs] using hmeasure'
  exact ⟨φ, hφ, hDconv⟩

private theorem endpoint_bounded_ehrhard_rigidity {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {Xn Yn : ℕ → Ω → ℝ} {X : Ω → ℝ}
    {K : ℝ} (σ : NNReal) (hK : 0 ≤ K) (hXn : ∀ n, AEMeasurable (Xn n) P)
    (hYn : ∀ n, AEMeasurable (Yn n) P) (hXmem : MemLp X 2 P)
    (hXlaw : P.map X = gaussianReal 0 σ)
    (hXconv : Tendsto (fun n => eLpNorm (Xn n - X) 2 P) atTop (𝓝 0))
    (hXcenter : ∀ n, Integrable (Xn n) P ∧ (∫ ω, Xn n ω ∂P) = 0)
    (hYcenter : ∀ n, Integrable (Yn n) P ∧ (∫ ω, Yn n ω ∂P) = 0)
    (hbound : ∀ n, ∀ᵐ ω ∂P, |Yn n ω - Xn n ω| ≤ K)
    (hYE : ∀ n, IsEhrhardType (P.map (Yn n)))
    (hXYE : ∀ n, IsEhrhardType (P.map fun ω => Xn n ω + Yn n ω)) :
    TendstoInMeasure P (fun n ω => Yn n ω - Xn n ω) atTop fun _ => 0 := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  let a : ℕ → ℝ≥0∞ := fun n => P {ω | ε ≤ |Yn n ω - Xn n ω|}
  have ha : Tendsto a atTop (𝓝 0) := by
    apply tendsto_of_subseq_tendsto (x := a)
    intro ψ hψ
    have hXconvψ : Tendsto (fun n => eLpNorm (Xn (ψ n) - X) 2 P) atTop (𝓝 0) :=
      hXconv.comp hψ
    obtain ⟨φ, hφ, hconv⟩ := endpoint_exists_rigidity_subsequence P σ hK
      (fun n => hXn (ψ n)) (fun n => hYn (ψ n)) hXmem hXlaw hXconvψ
      (fun n => hXcenter (ψ n)) (fun n => hYcenter (ψ n))
      (fun n => hbound (ψ n)) (fun n => hYE (ψ n)) (fun n => hXYE (ψ n))
    have hmeasure := (tendstoInMeasure_iff_norm.mp hconv) ε hε
    refine ⟨φ, ?_⟩
    simpa [a, Real.norm_eq_abs, Function.comp_def] using hmeasure
  simpa [a, Real.norm_eq_abs] using ha

/-- Gaussianity of the flat-initial KPZ test pairing forces the centered log-field difference
for any bounded continuous terminal bounded away from zero to tend to zero in every finite Lᵖ exponent;
see KPZ (9.6). -/
theorem avgLogField_sub_tendsto_of (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) (hC12 : ToyJointAt ϑ P Z)
    (hHeatStartLogInput : HeatStartLogAt ϑ P Z) (hHeatStartLogFieldInput : HeatStartLogFieldAt ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    {t : ℝ} (ht : 0 < t) (ψ : TestFn) (hψ : ∀ x, 0 ≤ ψ x)
    (hψ₁ : ∫ x, ψ x = 1)
    (hG : ∃ (m : ℝ) (v : NNReal),
      P.map (fun ω => H t 0 ω ψ) = gaussianReal m v)
    (f : Plane →ᵇ ℝ) {c : ℝ} (hc : 0 < c) (hf : ∀ y, c ≤ f y)
    (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    Tendsto (fun r => eLpNorm (fun ω => avgLogField P Z r t ψ f ω -
      avgLogField P Z r t ψ (fun _ => 1) ω) p P)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  classical
  rw [tendsto_iff_seq_tendsto]
  intro rseq hrseq
  obtain ⟨X, hXlaw, hXmem, hXcenter, hXconv⟩ :=
    avgLogField_one_tendsto_of ϑ P Z hZ hsym hC12 hHeatStartLogInput H hH ht ψ
  obtain ⟨m, v, hG⟩ := hG
  have hXhas : HasLaw X (gaussianReal m v) P :=
    ⟨hXmem.aemeasurable, hXlaw.trans hG⟩
  have hmeanX : (∫ ω, X ω ∂P) = m := by
    calc
      _ = ∫ x, x ∂(gaussianReal m v) := hXhas.integral_eq
      _ = m := integral_id_gaussianReal
  have hm : m = 0 := by rw [hXcenter] at hmeanX; linarith
  have hXlaw0 : P.map X = gaussianReal 0 v := by
    simpa [hm] using hXlaw.trans hG
  have hpos : ∀ᶠ n in atTop, 0 < rseq n :=
    hrseq.eventually self_mem_nhdsWithin
  have hlt : ∀ᶠ n in atTop, rseq n < t :=
    hrseq.eventually (nhdsWithin_le_nhds (Iio_mem_nhds ht))
  let good : ℕ → Prop := fun n => 0 < rseq n ∧ rseq n < t
  have hgood : ∀ᶠ n in atTop, good n := by
    filter_upwards [hpos, hlt] with n hn₀ hnt
    exact ⟨hn₀, hnt⟩
  let ρ : ℕ → ℝ := fun n => if good n then rseq n else t / 2
  have hρpos (n : ℕ) : 0 < ρ n := by
    dsimp [ρ]
    split_ifs with h
    · exact h.1
    · exact half_pos ht
  have hρlt (n : ℕ) : ρ n < t := by
    dsimp [ρ]
    split_ifs with h
    · exact h.2
    · exact half_lt_self ht
  have hρtend : Tendsto ρ atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    apply hrseq.congr'
    filter_upwards [hgood] with n hn
    simp [ρ, good, hn]
  let Xn : ℕ → Ω → ℝ := fun n ω => avgLogField P Z (ρ n) t ψ (fun _ => 1) ω
  let Yn : ℕ → Ω → ℝ := fun n ω => avgLogField P Z (ρ n) t ψ f ω
  have hXcenterSeq (n : ℕ) : Integrable (Xn n) P ∧ (∫ ω, Xn n ω ∂P) = 0 := by
    have h := avgLogField_integral_eq_zero_of ϑ P Z hZ hsym (hρpos n) (hρlt n)
      ψ (0 : Plane →ᵇ ℝ)
    simpa [Xn, Real.exp_zero] using h
  have hYcenterSeq (n : ℕ) : Integrable (Yn n) P ∧ (∫ ω, Yn n ω ∂P) = 0 := by
    have h := avgLogField_integral_eq_zero_of ϑ P Z hZ hsym (hρpos n) (hρlt n)
      ψ (endpointLogTerminal f hc hf)
    simpa [Yn, endpointLogTerminal_exp] using h
  have hXmeas (n : ℕ) : AEMeasurable (Xn n) P :=
    (hXcenterSeq n).1.aestronglyMeasurable.aemeasurable
  have hYmeas (n : ℕ) : AEMeasurable (Yn n) P :=
    (hYcenterSeq n).1.aestronglyMeasurable.aemeasurable
  have hYeh (n : ℕ) : IsEhrhardType (P.map (Yn n)) ∧
      IsEhrhardType (P.map fun ω => Xn n ω + Yn n ω) := by
    have h := avgLogField_isEhrhardType_of ϑ P Z hZ hsym hHeatStartLogInput hHeatStartLogFieldInput
      (hρpos n) (hρlt n) ψ hψ f hc hf
    exact ⟨by simpa [Yn] using h.2.1, by simpa [Xn, Yn] using h.2.2⟩
  have hcNorm : c ≤ ‖f‖ := by
    calc
      c ≤ f 0 := hf 0
      _ ≤ |f 0| := le_abs_self _
      _ = ‖f 0‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖f‖ := f.norm_coe_le_norm 0
  have hNormBounds : ∀ y, c ≤ f y ∧ f y ≤ ‖f‖ := by
    intro y
    exact ⟨hf y, (le_abs_self _).trans (f.norm_coe_le_norm y)⟩
  let K : ℝ := Real.log (‖f‖ / c)
  have hK : 0 ≤ K := by
    dsimp [K]
    apply Real.log_nonneg
    exact (one_le_div hc).2 hcNorm
  have hbound (n : ℕ) : ∀ᵐ ω ∂P, |Yn n ω - Xn n ω| ≤ K := by
    have h := avgLogField_sub_le_of ϑ P Z hZ hsym hHeatStartLogInput
      (hρpos n) (hρlt n) ψ hψ hψ₁ f hc hNormBounds
    simpa [Xn, Yn, K] using h
  have hXconvSeq : Tendsto (fun n => eLpNorm (Xn n - X) 2 P) atTop (𝓝 0) := by
    change Tendsto (fun n => eLpNorm
      (fun ω => avgLogField P Z (ρ n) t ψ (fun _ => 1) ω - X ω) 2 P)
      atTop (𝓝 0)
    exact hXconv.comp hρtend
  have hDconv : TendstoInMeasure P (fun n ω => Yn n ω - Xn n ω) atTop fun _ => 0 :=
    endpoint_bounded_ehrhard_rigidity P v hK hXmeas hYmeas hXmem hXlaw0 hXconvSeq
      hXcenterSeq hYcenterSeq hbound (fun n => (hYeh n).1) (fun n => (hYeh n).2)
  have hDmeas (n : ℕ) : AEMeasurable (fun ω => Yn n ω - Xn n ω) P :=
    (hYmeas n).sub (hXmeas n)
  have hLpSeq := bounded_tendsto_eLpNorm P hK hDmeas hbound hDconv hp
  have hLpOriginal : Tendsto (fun n => eLpNorm
      (fun ω => avgLogField P Z (rseq n) t ψ f ω -
        avgLogField P Z (rseq n) t ψ (fun _ => 1) ω) p P) atTop (𝓝 0) := by
    apply hLpSeq.congr'
    filter_upwards [hgood] with n hn
    simp [Xn, Yn, ρ, good, hn]
  simpa [Function.comp_def] using hLpOriginal

end Critical2DKPZ.NonGaussian

end
