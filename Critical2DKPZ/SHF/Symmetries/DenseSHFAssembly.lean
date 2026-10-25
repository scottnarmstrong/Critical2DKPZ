/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Symmetries.DenseTransport
public import Critical2DKPZ.SHF.Symmetries.DenseTransportScale
public import Critical2DKPZ.SHF.Existence.FiniteDimensionalLaws
public import Critical2DKPZ.SHF.Existence.ProjectiveLawSupport
public import Critical2DKPZ.SHF.Tsai.ConvergenceApproximation
public import Critical2DKPZ.Definitions.ShfPairing
public import Critical2DKPZ.Definitions.IsEhrhardType

/-! # Characterization and symmetries of the critical stochastic heat flow -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.SHF.Tsai Critical2DKPZ.SHF.Existence
open Critical2DKPZ.SHF.Limit
open scoped Topology CompactlySupported ENNReal BoundedContinuousFunction

namespace Critical2DKPZ.SHF.Symmetries

universe u v

/-- There exists a critical stochastic heat flow satisfying the SHF conditions on every bounded countable dense time window. -/
def ExistsDenseCriticalSHF (ϑ : ℝ) : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)), IsCriticalSHF ϑ P Z ∧
    ∀ B : ℝ, 0 < B → ∀ D : Set ℝ, D.Countable → D ⊆ Set.Icc 0 B →
      Set.Icc 0 B ⊆ closure D → IsDenseSHF (ϑ - Real.eulerMascheroniConstant) D P Z

private theorem measurable_measurePairing {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X]
    (f : C_c(X, ℝ)) : Measurable (fun μ : Measure X => ∫ x, f x ∂μ) := by
  let κ : Kernel (Measure X) X := ⟨id, measurable_id⟩
  exact (((map_continuous f).measurable).stronglyMeasurable.integral_kernel
    (κ := κ)).measurable

/-- The `IsCriticalSHF` definition is equivalent, given finite-dimensional law uniqueness and
existence of one dense critical process, to the dense-time Tsai axioms at the prescribed shift. -/
theorem isCriticalSHF_iff_isDenseSHF_of (ϑ : ℝ)
    (hT : DenseSHFUnique.{u, 0} (ϑ - Real.eulerMascheroniConstant))
    (hE : ExistsDenseCriticalSHF ϑ) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) :
    IsCriticalSHF ϑ P Z ↔
      (∀ s t, 0 ≤ s → s < t → Measurable (Z s t)) ∧
      (∀ s t, 0 ≤ s → s < t → ∀ᵐ ω ∂P,
        IsLocallyFiniteMeasure (Z s t ω) ∧ IsLocallyFiniteMeasure ((Z s t ω).map Prod.fst)) ∧
      ∀ D : Set ℝ, D.Countable → (∀ s ∈ D, 0 ≤ s) →
        IsDenseSHF (ϑ - Real.eulerMascheroniConstant) D P Z := by
  constructor
  · intro hZ
    rcases hE with ⟨Ω₀, mΩ₀, P₀, hP₀, Z₀, hZ₀, hDense₀⟩
    refine ⟨hZ.1, hZ.2.1, ?_⟩
    intro D hD hDnonneg
    classical
    have hQexists (m : ℕ) : ∃ Q : Set ℝ,
        Q.Countable ∧ Q ⊆ Set.Icc (0 : ℝ) (m + 1) ∧
          Set.Icc (0 : ℝ) (m + 1) ⊆ closure Q :=
      TopologicalSpace.exists_countable_dense_subset (Set.Icc (0 : ℝ) (m + 1))
    let Q (m : ℕ) := Classical.choose (hQexists m)
    have hQspec (m : ℕ) := Classical.choose_spec (hQexists m)
    have hQcount (m : ℕ) : (Q m).Countable := (hQspec m).1
    have hQsub (m : ℕ) : Q m ⊆ Set.Icc (0 : ℝ) (m + 1) := (hQspec m).2.1
    have hQdense (m : ℕ) : Set.Icc (0 : ℝ) (m + 1) ⊆ closure (Q m) :=
      (hQspec m).2.2
    let Rm (m : ℕ) : Set ℝ := ⋃ j ∈ Finset.range (m + 1), Q j
    let Dm (m : ℕ) : Set ℝ := (D ∩ Set.Icc (0 : ℝ) (m + 1)) ∪ Rm m
    have hRcount (m : ℕ) : (Rm m).Countable := by
      have hrange : (Finset.range (m + 1) : Set ℕ).Countable :=
        (Finset.range (m + 1)).finite_toSet.countable
      exact hrange.biUnion (fun j _ => hQcount j)
    have hDmcount (m : ℕ) : (Dm m).Countable := by
      apply (hD.mono Set.inter_subset_left).union
      exact hRcount m
    have hDmSub (m : ℕ) : Dm m ⊆ Set.Icc (0 : ℝ) (m + 1) := by
      intro x hx
      rcases hx with hx | hx
      · exact hx.2
      · rcases Set.mem_iUnion.mp hx with ⟨j, hj⟩
        rcases Set.mem_iUnion.mp hj with ⟨hjrange, hxj⟩
        have hjle : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hjrange)
        rcases hQsub j hxj with ⟨hx0, hxj⟩
        refine ⟨hx0, ?_⟩
        calc
          x ≤ (j : ℝ) + 1 := hxj
          _ ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hjle 1
    have hDmDense (m : ℕ) : Set.Icc (0 : ℝ) (m + 1) ⊆ closure (Dm m) := by
      have hQm : Q m ⊆ Dm m := by
        intro x hx
        right
        simp only [Rm, Set.mem_iUnion]
        exact ⟨m, Finset.mem_range.mpr (Nat.lt_succ_self _), hx⟩
      exact (hQdense m).trans (closure_mono hQm)
    have hmono : Monotone Dm := by
      intro m n hmn x hx
      rcases hx with hx | hx
      · left
        refine ⟨hx.1, hx.2.1, ?_⟩
        exact le_trans hx.2.2 (by exact_mod_cast Nat.add_le_add_right hmn 1)
      · right
        rcases Set.mem_iUnion.mp hx with ⟨j, hj⟩
        rcases Set.mem_iUnion.mp hj with ⟨hjrange, hxj⟩
        have hjle : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hjrange)
        simp only [Rm, Set.mem_iUnion]
        exact ⟨j, Finset.mem_range.mpr (lt_of_le_of_lt (le_trans hjle hmn)
          (Nat.lt_succ_self _)), hxj⟩
    have hDcover : D ⊆ ⋃ m, Dm m := by
      intro x hx
      obtain ⟨m, hxm⟩ := exists_nat_gt x
      apply Set.mem_iUnion.mpr ⟨m, ?_⟩
      left
      exact ⟨hx, hDnonneg x hx, le_trans hxm.le (by exact_mod_cast Nat.le_succ m)⟩
    have hstage (m : ℕ) : IsDenseSHF (ϑ - Real.eulerMascheroniConstant) (Dm m) P Z := by
      have hbase := hDense₀ (m + 1) (by positivity) (Dm m) (hDmcount m)
        (hDmSub m) (hDmDense m)
      apply isDenseSHF_of_fdd_eq hbase
        (fun s hs t ht hst => hZ.1 s t (hDmSub m hs).1 hst)
      intro k s t hst
      have htimes : ∀ i, 0 ≤ s i ∧ s i < t i := by
        intro i
        exact ⟨(hDmSub m (hst i).1).1, (hst i).2.2⟩
      exact isCriticalSHF_fdd_eq ϑ P₀ P Z₀ Z hZ₀ hZ k s t htimes
    exact isDenseSHF_of_iUnion Dm hmono hDcover hstage
  · rintro ⟨hmeas, hlocal, hdense⟩
    rcases hE with ⟨Ω₀, mΩ₀, P₀, hP₀, Z₀, hZ₀, hDense₀⟩
    refine ⟨hmeas, hlocal, ?_⟩
    intro k s t htimes φ ψ
    obtain ⟨B, hB, D, hD, hDB, hdenseD, htimesD⟩ :=
      exists_countable_dense_interval_with_finite_times s t htimes
    let hZD : IsDenseSHF (ϑ - Real.eulerMascheroniConstant) D P Z :=
      hdense D hD (fun r hr => (hDB hr).1)
    let hZ₀D : IsDenseSHF (ϑ - Real.eulerMascheroniConstant) D P₀ Z₀ :=
      hDense₀ B hB D hD hDB hdenseD
    have hLaw := hT B hB D hDB hdenseD P P₀ Z Z₀ hZD hZ₀D k s t (fun i =>
      ⟨htimesD i |>.1, htimesD i |>.2, htimes i |>.2⟩)
    let X : (Fin k → Measure (Plane × Plane)) → Fin k → ℝ × ℝ := fun m i =>
      (∫ p, φ i p ∂m i, ∫ x, ψ i x ∂(m i).map Prod.fst)
    have hX : Measurable X := by
      apply measurable_pi_iff.mpr
      intro i
      have hflat : Measurable (fun μ : Measure (Plane × Plane) =>
          ∫ x, ψ i x ∂μ.map Prod.fst) :=
        (measurable_measurePairing (ψ i)).comp
          (Measure.measurable_map Prod.fst measurable_fst)
      exact (measurable_measurePairing (φ i)).comp (measurable_pi_apply i) |>.prodMk
        (hflat.comp (measurable_pi_apply i))
    let Zvec : Ω → Fin k → Measure (Plane × Plane) := fun ω i => Z (s i) (t i) ω
    let Z₀vec : Ω₀ → Fin k → Measure (Plane × Plane) := fun ω i => Z₀ (s i) (t i) ω
    have hZvec : Measurable Zvec := by
      apply measurable_pi_iff.mpr
      intro i
      exact hmeas (s i) (t i) (htimes i).1 (htimes i).2
    have hZ₀vec : Measurable Z₀vec := by
      apply measurable_pi_iff.mpr
      intro i
      exact hZ₀.1 (s i) (t i) (htimes i).1 (htimes i).2
    have hreadLaw : P.map (fun ω => X (Zvec ω)) = P₀.map (fun ω => X (Z₀vec ω)) := by
      calc
        P.map (fun ω => X (Zvec ω)) = (P.map Zvec).map X := by
          rw [Measure.map_map hX hZvec]
          rfl
        _ = (P₀.map Z₀vec).map X := by rw [hLaw]
        _ = P₀.map (fun ω => X (Z₀vec ω)) := by
          rw [Measure.map_map hX hZ₀vec]
          simp only [Function.comp_def]
    have hconv := hZ₀.2.2 k s t htimes φ ψ
    refine ⟨hconv.forall_aemeasurable, (hX.comp hZvec).aemeasurable, ?_⟩
    have hprob : (⟨P.map (fun ω => X (Zvec ω)), inferInstance⟩ :
        ProbabilityMeasure (Fin k → ℝ × ℝ)) =
      ⟨P₀.map (fun ω => X (Z₀vec ω)), inferInstance⟩ := Subtype.ext hreadLaw
    rw [hprob]
    exact hconv.tendsto

private theorem criticalSHF_firstMarginal_localFinite_of_dense
    (ϑ : ℝ) (hT : DenseSHFUnique.{u, 0}
      (ϑ - Real.eulerMascheroniConstant))
    (hE : ExistsDenseCriticalSHF ϑ) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hDense : ∀ D : Set ℝ, D.Countable → (∀ s ∈ D, 0 ≤ s) →
      IsDenseSHF (ϑ - Real.eulerMascheroniConstant) D P Z)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    ∀ᵐ ω ∂P, IsLocallyFiniteMeasure ((Z s t ω).map Prod.fst) := by
  rcases exists_countable_dense_interval_with_finite_times
      (fun _ : Fin 1 => s) (fun _ => t) (fun _ => ⟨hs, hst⟩) with
    ⟨B, hB, D, hD, hDB, hDdense, htimes⟩
  rcases hE with ⟨Ω₀, mΩ₀, P₀, hP₀, Z₀, hZ₀, hDense₀⟩
  have hD₀ : IsDenseSHF (ϑ - Real.eulerMascheroniConstant) D P₀ Z₀ :=
    hDense₀ B hB D hD hDB hDdense
  have hDZ : IsDenseSHF (ϑ - Real.eulerMascheroniConstant) D P Z :=
    hDense D hD (fun r hr => (hDB hr).1)
  have hlawVec := hT B hB D hDB hDdense P P₀ Z Z₀ hDZ hD₀ 1
    (fun _ => s) (fun _ => t) (fun i =>
      ⟨(htimes i).1, (htimes i).2, hst⟩)
  let V₀ : Ω₀ → Fin 1 → Measure (Plane × Plane) := fun ω _ => Z₀ s t ω
  let V : Ω → Fin 1 → Measure (Plane × Plane) := fun ω _ => Z s t ω
  let ev : (Fin 1 → Measure (Plane × Plane)) → Measure (Plane × Plane) := fun m => m 0
  have hV₀ : Measurable V₀ := by
    apply measurable_pi_iff.mpr
    intro i
    simpa only [V₀] using hZ₀.1 s t hs hst
  have hV : Measurable V := by
    apply measurable_pi_iff.mpr
    intro i
    simpa only [V] using (hDZ.1 s (htimes 0).1 t (htimes 0).2 hst).1
  have hev : Measurable ev := measurable_pi_apply 0
  have hLaw : P.map (fun ω => Z s t ω) = P₀.map (fun ω => Z₀ s t ω) := by
    calc
      P.map (fun ω => Z s t ω) = (P.map V).map ev := by
        rw [Measure.map_map hev hV]
        simp only [Function.comp_def, V, ev]
      _ = (P₀.map V₀).map ev := by rw [hlawVec]
      _ = P₀.map (fun ω => Z₀ s t ω) := by
        rw [Measure.map_map hev hV₀]
        simp only [Function.comp_def, V₀, ev]
  let M : Measure (Plane × Plane) → Measure Plane := fun μ => μ.map Prod.fst
  let F₀ : Ω₀ → Measure Plane := fun ω => M (Z₀ s t ω)
  let F : Ω → Measure Plane := fun ω => M (Z s t ω)
  have hM : Measurable M := Measure.measurable_map Prod.fst measurable_fst
  have hLawM : P.map F = P₀.map F₀ := by
    calc
      P.map F = (P.map (fun ω => Z s t ω)).map M := by
        rw [Measure.map_map hM (hDZ.1 s (htimes 0).1 t (htimes 0).2 hst).1]
        rfl
      _ = (P₀.map (fun ω => Z₀ s t ω)).map M := by rw [hLaw]
      _ = P₀.map F₀ := by
        rw [Measure.map_map hM
          (hZ₀.1 s t hs hst)]
        rfl
  have hLF₀ : ∀ᵐ ω ∂P₀, IsLocallyFiniteMeasure (F₀ ω) := by
    exact (hZ₀.2.1 s t hs hst).mono fun ω hω => hω.2
  exact ae_locallyFinite_of_map_eq P₀ P F₀ F
    (hM.comp (hZ₀.1 s t hs hst))
    (hM.comp (hDZ.1 s (htimes 0).1 t (htimes 0).2 hst).1)
    hLawM.symm hLF₀

private theorem criticalSHF_of_dense_all (ϑ : ℝ)
    (hT : DenseSHFUnique.{u, 0} (ϑ - Real.eulerMascheroniConstant))
    (hE : ExistsDenseCriticalSHF ϑ) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hDense : ∀ D : Set ℝ, D.Countable → (∀ s ∈ D, 0 ≤ s) →
      IsDenseSHF (ϑ - Real.eulerMascheroniConstant) D P Z) :
    IsCriticalSHF ϑ P Z := by
  have hmeas : ∀ s t, 0 ≤ s → s < t → Measurable (Z s t) := by
    intro s t hs hst
    let D : Set ℝ := {s, t}
    have hD : D.Countable := by
      have hfin : D.Finite := by simp [D]
      exact hfin.countable
    have hsD : s ∈ D := by simp [D]
    have htD : t ∈ D := by simp [D]
    have hDnonneg : ∀ r ∈ D, 0 ≤ r := by
      intro r hr
      simp only [D, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
      rcases hr with rfl | rfl
      · exact hs
      · linarith
    exact (hDense D hD hDnonneg).1 s hsD t htD hst |>.1
  have hlocal : ∀ s t, 0 ≤ s → s < t → ∀ᵐ ω ∂P,
      IsLocallyFiniteMeasure (Z s t ω) ∧
        IsLocallyFiniteMeasure ((Z s t ω).map Prod.fst) := by
    intro s t hs hst
    let D : Set ℝ := {s, t}
    have hD : D.Countable := by
      have hfin : D.Finite := by simp [D]
      exact hfin.countable
    have hsD : s ∈ D := by simp [D]
    have htD : t ∈ D := by simp [D]
    have hDnonneg : ∀ r ∈ D, 0 ≤ r := by
      intro r hr
      simp only [D, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
      rcases hr with rfl | rfl
      · exact hs
      · linarith
    have hpair := (hDense D hD hDnonneg).1 s hsD t htD hst |>.2
    have hlf : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (Z s t ω) := hpair
    have hflat := criticalSHF_firstMarginal_localFinite_of_dense ϑ
      hT hE P Z hDense hs hst
    filter_upwards [hlf, hflat] with ω hω hω'
    exact ⟨hω, hω'⟩
  exact (isCriticalSHF_iff_isDenseSHF_of ϑ hT hE P Z).2
    ⟨hmeas, hlocal, hDense⟩

/-- The SHF symmetries follow from dense-time uniqueness, the L² modulus, and positivity. -/
theorem shf_symmetries_of (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF ϑ P Z)
    (hT : ∀ ϑ' : ℝ, DenseSHFUnique.{u, u}
      (ϑ' - Real.eulerMascheroniConstant))
    (hT0 : ∀ ϑ' : ℝ, DenseSHFUnique.{u, 0}
      (ϑ' - Real.eulerMascheroniConstant))
    (hE : ∀ ϑ' : ℝ, ExistsDenseCriticalSHF ϑ')
    (hL2 : ∀ (Φ : C_c(Plane × Plane, ℝ)) {τ T : ℝ}, 0 < τ →
      ∀ ε > 0, ∃ η > 0, ∀ s t s' t' : ℝ, 0 ≤ s → τ ≤ t - s → t ≤ T →
        0 ≤ s' → τ ≤ t' - s' → t' ≤ T → |s - s'| + |t - t'| ≤ η →
          Integrable (fun ω => (∫ p, Φ p ∂(Z s t ω) -
            ∫ p, Φ p ∂(Z s' t' ω)) ^ 2) P ∧
          ∫ ω, (∫ p, Φ p ∂(Z s t ω) -
            ∫ p, Φ p ∂(Z s' t' ω)) ^ 2 ∂P ≤ ε)
    (hpos : ∀ (s t δ : ℝ) (x : Plane) (h₀ : Plane →ᵇ ℝ), 0 ≤ s → s < t →
      0 < δ →
      (∀ᵐ ω ∂P, 0 < shfPairing Z s t
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω) ∧
      AEMeasurable (fun ω => Real.log (shfPairing Z s t
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω)) P ∧
      IsEhrhardType (P.map fun ω => Real.log (shfPairing Z s t
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω))) :
    (∀ z : Plane, IsCriticalSHF ϑ P fun s t ω =>
      (Z s t ω).map fun p => (p.1 + z, p.2 + z)) ∧
    (∀ R : Plane ≃ₗᵢ[ℝ] Plane,
      LinearMap.det (R.toLinearEquiv : Plane →ₗ[ℝ] Plane) = 1 →
        IsCriticalSHF ϑ P fun s t ω => (Z s t ω).map fun p => (R p.1, R p.2)) ∧
    (∀ u : ℝ, 0 ≤ u → IsCriticalSHF ϑ P fun s t ω => Z (s + u) (t + u) ω) ∧
    (∀ a : ℝ, 0 < a → IsCriticalSHF (ϑ + Real.log a) P fun s t ω =>
      ENNReal.ofReal a⁻¹ • (Z (a * s) (a * t) ω).map fun p =>
        ((Real.sqrt a)⁻¹ • p.1, (Real.sqrt a)⁻¹ • p.2)) ∧
    (∀ (T : ℝ) (k : ℕ) (s t : Fin k → ℝ),
      (∀ i, 0 ≤ s i ∧ s i < t i ∧ t i ≤ T) →
      ∀ φ : Fin k → C_c(Plane × Plane, ℝ),
        P.map (fun ω i => ∫ p, φ i (p.2, p.1) ∂(Z (T - t i) (T - s i) ω)) =
          P.map (fun ω i => ∫ p, φ i p ∂(Z (s i) (t i) ω))) ∧
    (∀ (φ : C_c(Plane × Plane, ℝ)) (s t : ℝ), 0 ≤ s → s < t →
      TendstoInMeasure P (fun (q : ℝ × ℝ) ω => ∫ p, φ p ∂(Z q.1 q.2 ω))
        (nhdsWithin (s, t) {q | 0 ≤ q.1 ∧ q.1 < q.2})
        (fun ω => ∫ p, φ p ∂(Z s t ω))) ∧
    (∀ (s t δ : ℝ) (x : Plane) (h₀ : Plane →ᵇ ℝ), 0 ≤ s → s < t →
      0 < δ →
      (∀ᵐ ω ∂P, 0 < shfPairing Z s t
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω) ∧
      AEMeasurable (fun ω => Real.log (shfPairing Z s t
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω)) P ∧
      IsEhrhardType (P.map fun ω => Real.log (shfPairing Z s t
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω))) := by
  have hDenseZ := (isCriticalSHF_iff_isDenseSHF_of ϑ (hT0 ϑ) (hE ϑ) P Z).1 hZ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hpos⟩
  · intro z
    apply criticalSHF_of_dense_all ϑ (hT0 ϑ) (hE ϑ) P
      (fun s t ω => (Z s t ω).map fun p => (p.1 + z, p.2 + z))
    intro D hD hDnonneg
    exact isDenseSHF_map_translate (hDenseZ.2.2 D hD hDnonneg) z
  · intro R hdet
    apply criticalSHF_of_dense_all ϑ (hT0 ϑ) (hE ϑ) P
      (fun s t ω => (Z s t ω).map fun p => (R p.1, R p.2))
    intro D hD hDnonneg
    exact isDenseSHF_map_linearIsometry (hDenseZ.2.2 D hD hDnonneg) R
  · intro u hu
    apply criticalSHF_of_dense_all ϑ (hT0 ϑ) (hE ϑ) P
      (fun s t ω => Z (s + u) (t + u) ω)
    intro D hD hDnonneg
    let D' : Set ℝ := (fun r => r + u) '' D
    have hD' : D'.Countable := hD.image (fun r => r + u)
    have hD'nonneg : ∀ r ∈ D', 0 ≤ r := by
      rintro r ⟨q, hq, rfl⟩
      exact add_nonneg (hDnonneg q hq) hu
    have hbase := hDenseZ.2.2 D' hD' hD'nonneg
    have hshift := isDenseSHF_timeShift hbase u
    let DshiftNonneg : Set ℝ := {r | 0 ≤ r ∧ r + u ∈ D'}
    have hshiftNonneg := isDenseSHF_mono
      (show DshiftNonneg ⊆ {r | r + u ∈ D'} from fun _ hr => hr.2) hshift
    apply isDenseSHF_mono ?_ hshiftNonneg
    intro r hr
    refine ⟨hDnonneg r hr, ?_⟩
    exact ⟨r, hr, rfl⟩
  · intro a ha
    apply criticalSHF_of_dense_all (ϑ + Real.log a) (hT0 (ϑ + Real.log a))
      (hE (ϑ + Real.log a)) P
      (fun s t ω => ENNReal.ofReal a⁻¹ • (Z (a * s) (a * t) ω).map
        (fun p => ((Real.sqrt a)⁻¹ • p.1, (Real.sqrt a)⁻¹ • p.2)))
    intro D hD hDnonneg
    let D' : Set ℝ := (fun r => a * r) '' D
    have hD' : D'.Countable := hD.image (fun r => a * r)
    have hD'nonneg : ∀ r ∈ D', 0 ≤ r := by
      rintro r ⟨q, hq, rfl⟩
      exact mul_nonneg ha.le (hDnonneg q hq)
    have hbase := hDenseZ.2.2 D' hD' hD'nonneg
    have hscaled := isDenseSHF_scale hbase ha
    have hscaled' : IsDenseSHF
        ((ϑ + Real.log a) - Real.eulerMascheroniConstant) D P
        (fun s t ω => ENNReal.ofReal a⁻¹ • (Z (a * s) (a * t) ω).map
          (fun p => ((Real.sqrt a)⁻¹ • p.1, (Real.sqrt a)⁻¹ • p.2))) := by
      have hsub : D ⊆ {r | a * r ∈ D'} := by
        intro r hr
        exact ⟨r, hr, rfl⟩
      have hm := isDenseSHF_mono hsub hscaled
      have hparam : (ϑ - Real.eulerMascheroniConstant) + Real.log a =
          (ϑ + Real.log a) - Real.eulerMascheroniConstant := by ring
      rw [hparam] at hm
      exact hm
    exact hscaled'
  · intro T k s t htimes φ
    by_cases hk : k = 0
    · subst k
      have hfun :
          (fun ω : Ω => fun i : Fin 0 =>
            ∫ p, φ i (p.2, p.1) ∂Z (T - t i) (T - s i) ω) =
          (fun ω : Ω => fun i : Fin 0 =>
            ∫ p, φ i p ∂Z (s i) (t i) ω) := by
        funext ω i
        exact Fin.elim0 i
      rw [hfun]
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      let i₀ : Fin k := ⟨0, hkpos⟩
      have hTpos : 0 < T := by
        linarith [(htimes i₀).1, (htimes i₀).2.1, (htimes i₀).2.2]
      obtain ⟨Q, hQc, hQsub, hQdense⟩ :=
        TopologicalSpace.exists_countable_dense_subset (Set.Icc (0 : ℝ) T)
      let A : Set ℝ := (Q ∪ Set.range s) ∪ Set.range t
      let D : Set ℝ := A ∪ (fun r => T - r) '' A
      have hAcount : A.Countable :=
        (hQc.union (Set.countable_range s)).union (Set.countable_range t)
      have hAsub : A ⊆ Set.Icc (0 : ℝ) T := by
        intro r hr
        simp only [A, Set.mem_union] at hr
        rcases hr with hr | hr
        · rcases hr with hq | hs
          · exact hQsub hq
          · obtain ⟨i, rfl⟩ := Set.mem_range.mp hs
            exact ⟨(htimes i).1, le_trans (le_of_lt (htimes i).2.1) (htimes i).2.2⟩
        · obtain ⟨i, rfl⟩ := Set.mem_range.mp hr
          exact ⟨le_trans (htimes i).1 (le_of_lt (htimes i).2.1),
            (htimes i).2.2⟩
      have hDcount : D.Countable := hAcount.union (hAcount.image (fun r => T - r))
      have hDsub : D ⊆ Set.Icc (0 : ℝ) T := by
        intro r hr
        rcases hr with hr | hr
        · exact hAsub hr
        · obtain ⟨q, hq, rfl⟩ := hr
          rcases hAsub hq with ⟨hq0, hqT⟩
          constructor <;> linarith
      have hQinD : Q ⊆ D := by
        intro q hq
        apply Or.inl
        apply Or.inl
        exact Or.inl hq
      have hDdense : Set.Icc (0 : ℝ) T ⊆ closure D :=
        hQdense.trans (closure_mono hQinD)
      have hDstable : ∀ r ∈ D, T - r ∈ D := by
        intro r hr
        rcases hr with hr | hr
        · exact Or.inr ⟨r, hr, rfl⟩
        · obtain ⟨q, hq, hqr⟩ := hr
          rw [← hqr]
          have hcancel : T - (T - q) = q := by ring
          rw [hcancel]
          exact Or.inl hq
      have hsA (i : Fin k) : s i ∈ A := by
        simp only [A, Set.mem_union, Set.mem_range]
        exact Or.inl (Or.inr ⟨i, rfl⟩)
      have htA (i : Fin k) : t i ∈ A := by
        simp only [A, Set.mem_union, Set.mem_range]
        exact Or.inr ⟨i, rfl⟩
      have hsD (i : Fin k) : s i ∈ D := Or.inl (hsA i)
      have htD (i : Fin k) : t i ∈ D := Or.inl (htA i)
      have hDnonneg : ∀ r ∈ D, 0 ≤ r := fun r hr => (hDsub hr).1
      have hbase := hDenseZ.2.2 D hDcount hDnonneg
      let Y : ℝ → ℝ → Ω → Measure (Plane × Plane) := fun r q ω =>
        (Z (T - q) (T - r) ω).map Prod.swap
      have hrevBase := isDenseSHF_reverse hbase T
      let DrevNonneg : Set ℝ := {r | 0 ≤ r ∧ T - r ∈ D}
      have hrevNonneg := isDenseSHF_mono
        (show DrevNonneg ⊆ {r | T - r ∈ D} from fun _ hr => hr.2) hrevBase
      have hDrevNonneg : D ⊆ DrevNonneg := by
        intro r hr
        exact ⟨(hDsub hr).1, hDstable r hr⟩
      have hrev := isDenseSHF_mono hDrevNonneg hrevNonneg
      have hY : IsDenseSHF (ϑ - Real.eulerMascheroniConstant) D P Y := hrev
      have htimesD : ∀ i, s i ∈ D ∧ t i ∈ D ∧ s i < t i := by
        intro i
        exact ⟨hsD i, htD i, (htimes i).2.1⟩
      have hlaw := hT ϑ T hTpos D hDsub hDdense P P Z Y hbase hY k s t htimesD
      let Yvec : Ω → Fin k → Measure (Plane × Plane) := fun ω i => Y (s i) (t i) ω
      let Zvec : Ω → Fin k → Measure (Plane × Plane) := fun ω i => Z (s i) (t i) ω
      have hYvec : Measurable Yvec := by
        apply measurable_pi_iff.mpr
        intro i
        have h0 : 0 ≤ T - t i := by linarith [(htimes i).2.2]
        have hlt : T - t i < T - s i := by linarith [(htimes i).2.1]
        exact (Measure.measurable_map pairSwapMeas pairSwapMeas.measurable).comp
          (hZ.1 (T - t i) (T - s i) h0 hlt)
      have hZvec : Measurable Zvec := by
        apply measurable_pi_iff.mpr
        intro i
        exact hZ.1 (s i) (t i) (htimes i).1 (htimes i).2.1
      let X : (Fin k → Measure (Plane × Plane)) → Fin k → ℝ :=
        fun m i => ∫ p, φ i p ∂m i
      have hX : Measurable X := by
        apply measurable_pi_iff.mpr
        intro i
        exact (measurable_measurePairing (φ i)).comp (measurable_pi_apply i)
      have hreadLaw :
          P.map (fun ω i => ∫ p, φ i p ∂Y (s i) (t i) ω) =
            P.map (fun ω i => ∫ p, φ i p ∂Z (s i) (t i) ω) := by
        calc
          P.map (fun ω => X (Yvec ω)) = (P.map Yvec).map X := by
            rw [Measure.map_map hX hYvec]
            rfl
          _ = (P.map Zvec).map X := by rw [hlaw]
          _ = P.map (fun ω => X (Zvec ω)) := by
            rw [Measure.map_map hX hZvec]
            rfl
      have htargetEq :
          (fun ω i => ∫ p, φ i (p.2, p.1) ∂Z (T - t i) (T - s i) ω) =ᵐ[P]
          (fun ω i => ∫ p, φ i p ∂Y (s i) (t i) ω) := by
        have hpoint : ∀ᵐ ω ∂P, ∀ i,
            ∫ p, φ i (p.2, p.1) ∂Z (T - t i) (T - s i) ω =
              ∫ p, φ i p ∂Y (s i) (t i) ω := by
          apply ae_all_iff.2
          intro i
          have hLF : ∀ᵐ ω ∂P,
              IsLocallyFiniteMeasure (Z (T - t i) (T - s i) ω) :=
            (hZ.2.1 (T - t i) (T - s i) (by linarith [(htimes i).2.2])
              (by linarith [(htimes i).2.1])).mono fun _ hω => hω.1
          filter_upwards [hLF] with ω hω
          let _ : IsLocallyFiniteMeasure (Z (T - t i) (T - s i) ω) := hω
          have hswap := (integral_pairSwapTest_map
            (Z (T - t i) (T - s i) ω) (φ i)).2
          have hmap : (Z (T - t i) (T - s i) ω).map Prod.swap =
              (Z (T - t i) (T - s i) ω).map pairSwapMeas := by
            apply Measure.map_congr
            filter_upwards [] with p
            exact (pairSwapMeas_apply p).symm
          change (∫ p, φ i (p.2, p.1) ∂Z (T - t i) (T - s i) ω) =
            ∫ p, φ i p ∂((Z (T - t i) (T - s i) ω).map Prod.swap)
          rw [hmap]
          simpa only [pairSwapTest_apply] using hswap.symm
        filter_upwards [hpoint] with ω hω
        funext i
        exact hω i
      calc
        P.map (fun ω i => ∫ p, φ i (p.2, p.1) ∂Z (T - t i) (T - s i) ω) =
            P.map (fun ω i => ∫ p, φ i p ∂Y (s i) (t i) ω) :=
          Measure.map_congr htargetEq
        _ = P.map (fun ω i => ∫ p, φ i p ∂Z (s i) (t i) ω) := hreadLaw
  · intro φ s t hs hst
    rw [tendstoInMeasure_iff_measureReal_dist]
    intro ε hε
    apply tendsto_order.2
    constructor
    · intro a ha
      exact Eventually.of_forall fun q => lt_of_lt_of_le ha measureReal_nonneg
    · intro δ hδ
      let τ : ℝ := (t - s) / 3
      obtain ⟨η, hη, hL2bound⟩ := hL2 φ (τ := τ) (T := t + 1)
        (by dsimp [τ]; linarith) (δ * ε ^ 2 / 2) (by positivity)
      let r : ℝ := min (η / 4) (min ((t - s) / 12) (1 / 2))
      have hr : 0 < r := by
        dsimp [r]
        positivity
      have hrη : 2 * r ≤ η := by
        dsimp [r]
        have hle : min (η / 4) (min ((t - s) / 12) (1 / 2)) ≤ η / 4 :=
          min_le_left _ _
        linarith
      have hrgap : r ≤ (t - s) / 12 := by
        dsimp [r]
        exact le_trans (min_le_right _ _) (min_le_left _ _)
      have hrhalf : r ≤ (1 : ℝ) / 2 := by
        dsimp [r]
        exact le_trans (min_le_right _ _) (min_le_right _ _)
      have hnearN : ∀ᶠ q : ℝ × ℝ in 𝓝 (s, t), dist q (s, t) < r :=
        Metric.ball_mem_nhds _ hr
      have hnear : ∀ᶠ q : ℝ × ℝ in
          nhdsWithin (s, t) {q | 0 ≤ q.1 ∧ q.1 < q.2},
          dist q (s, t) < r :=
        hnearN.filter_mono nhdsWithin_le_nhds
      filter_upwards [hnear, self_mem_nhdsWithin] with q hq hqdom
      have hcoords : dist q.1 s < r ∧ dist q.2 t < r := by
        simpa only [Prod.dist_eq, max_lt_iff] using hq
      have hq1 : |q.1 - s| < r := by
        simpa only [Real.dist_eq] using hcoords.1
      have hq2 : |q.2 - t| < r := by
        simpa only [Real.dist_eq] using hcoords.2
      have hq1lo : s - r < q.1 := by
        rw [abs_lt] at hq1
        linarith
      have hq1hi : q.1 < s + r := by
        rw [abs_lt] at hq1
        linarith
      have hq2lo : t - r < q.2 := by
        rw [abs_lt] at hq2
        linarith
      have hq2hi : q.2 < t + r := by
        rw [abs_lt] at hq2
        linarith
      have hclose : |s - q.1| + |t - q.2| ≤ η := by
        have hfirst : |s - q.1| = |q.1 - s| := abs_sub_comm _ _
        have hsecond : |t - q.2| = |q.2 - t| := abs_sub_comm _ _
        rw [hfirst, hsecond]
        linarith [hq1, hq2, hrη]
      have hgap : τ ≤ q.2 - q.1 := by
        dsimp [τ]
        have hmargin : t - s - 2 * r ≥ (t - s) / 3 := by
          have hgap' : 0 ≤ t - s := le_of_lt (sub_pos.mpr hst)
          linarith [hrgap, hgap']
        linarith [hq1hi, hq2lo, hmargin]
      have hq2T : q.2 ≤ t + 1 := by
        linarith [hq2hi, hrhalf]
      have hmean := hL2bound s t q.1 q.2 hs
        (by dsimp [τ]; linarith [hst]) (by linarith) hqdom.1 hgap hq2T hclose
      have hmarkov := measureReal_dist_ge_le_integral_sq P
        (fun ω => ∫ p, φ p ∂Z s t ω)
        (fun ω => ∫ p, φ p ∂Z q.1 q.2 ω) hmean.1 hε
      have hprob : P.real {ω | ε ≤ dist
              (∫ p, φ p ∂Z q.1 q.2 ω) (∫ p, φ p ∂Z s t ω)} ≤ δ / 2 := by
        calc
          P.real {ω | ε ≤ dist
              (∫ p, φ p ∂Z q.1 q.2 ω) (∫ p, φ p ∂Z s t ω)} ≤
              (∫ ω, ((∫ p, φ p ∂Z s t ω) -
                (∫ p, φ p ∂Z q.1 q.2 ω)) ^ 2 ∂P) / ε ^ 2 := by
                  simpa only [dist_comm] using hmarkov
          _ ≤ (δ * ε ^ 2 / 2) / ε ^ 2 :=
            div_le_div_of_nonneg_right hmean.2 (sq_nonneg ε)
          _ = δ / 2 := by
            field_simp [ne_of_gt (sq_pos_of_pos hε)]
      exact lt_of_le_of_lt hprob (by linarith)

end Critical2DKPZ.SHF.Symmetries

end
