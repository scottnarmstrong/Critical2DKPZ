/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.JointConvergence.Approximation
public import Critical2DKPZ.JointConvergence.HeatStartLogFieldAssembly
public import Critical2DKPZ.JointConvergence.KPZRegularizedReverseLaw
public import Critical2DKPZ.JointConvergence.L2Limit
public import Critical2DKPZ.JointConvergence.L2ToLp
public import Critical2DKPZ.JointConvergence.LawUniqueness
public import Critical2DKPZ.JointConvergence.MomentConvergence
public import Critical2DKPZ.FutureProfiles.EndpointTranslation
public import Critical2DKPZ.Definitions.ShfSigma
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic

/-! # Joint convergence of the KPZ field -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open Critical2DKPZ.SHF.Limit
open scoped BoundedContinuousFunction ENNReal Topology

namespace Critical2DKPZ.JointConvergence

private theorem integral_eq_of_map_eq_aux {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {X Y : Ω → ℝ} (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (hlaw : P.map X = P.map Y) : (∫ ω, X ω ∂P) = ∫ ω, Y ω ∂P := by
  let hidX : AEStronglyMeasurable (fun x : ℝ => x) (P.map X) :=
    measurable_id.aestronglyMeasurable
  let hidY : AEStronglyMeasurable (fun x : ℝ => x) (P.map Y) :=
    measurable_id.aestronglyMeasurable
  by_cases hIX : Integrable X P
  · have hIpushX : Integrable (fun x : ℝ => x) (P.map X) := by
      have h := (integrable_map_measure hidX hX).2 hIX
      simpa only [Function.comp_def] using h
    have hIpushY : Integrable (fun x : ℝ => x) (P.map Y) := by
      rw [← hlaw]
      exact hIpushX
    have hIY : Integrable Y P := by
      have h := (integrable_map_measure hidY hY).1 hIpushY
      simpa only [Function.comp_def] using h
    have hmapX := integral_map hX hidX
    have hmapY := integral_map hY hidY
    calc
      (∫ ω, X ω ∂P) = ∫ x, x ∂P.map X := hmapX.symm
      _ = ∫ x, x ∂P.map Y := by rw [hlaw]
      _ = ∫ ω, Y ω ∂P := hmapY
  · have hIpushX : ¬ Integrable (fun x : ℝ => x) (P.map X) := by
      intro h
      apply hIX
      have h' := (integrable_map_measure hidX hX).1 h
      simpa only [Function.comp_def] using h'
    have hIpushY : ¬ Integrable (fun x : ℝ => x) (P.map Y) := by
      intro h
      apply hIpushX
      rw [← hlaw] at h
      exact h
    have hIY : ¬ Integrable Y P := by
      intro h
      apply hIpushY
      have h' := (integrable_map_measure hidY hY).2 h
      simpa only [Function.comp_def] using h'
    rw [integral_undef hIX, integral_undef hIY]

private theorem integral_log_profile_heatStart_translate (β : ℝ) (a b m : ℕ)
    (x : Site) :
    (∫ ω, Real.log (profileP2Fun β a b (fun w => srwKernel m (w - x))
      (fun _ => 1) ω) ∂disorderLaw) =
      ∫ ω, Real.log (profileP2Fun β a b (fun w => srwKernel m w)
        (fun _ => 1) ω) ∂disorderLaw := by
  let τ : Disorder → Disorder := fun ω p => ω (p.1, p.2 + x)
  let F : Disorder → ℝ := fun ω => Real.log
    (profileP2Fun β a b (fun w => srwKernel m w) (fun _ => 1) ω)
  let G : Disorder → ℝ := fun ω => Real.log
    (profileP2Fun β a b (fun w => srwKernel m (w - x)) (fun _ => 1) ω)
  have hF : Measurable F := by
    dsimp [F]
    exact Real.measurable_log.comp
      (Polymer.measurable_profileP2Fun β a b (fun w => srwKernel m w) (fun _ => 1))
  have hτ := FutureProfiles.measurePreserving_disorderShift x
  have hG_eq : G = fun ω => F (τ ω) := by
    funext ω
    dsimp [F, G, τ]
    rw [FutureProfiles.profileP2Fun_translate β a b x (fun w => srwKernel m w)
      (fun _ => 1) ω]
  have hlaw : disorderLaw.map G = disorderLaw.map F := by
    calc
      disorderLaw.map G = disorderLaw.map (F ∘ τ) := by
        rw [hG_eq]
        rfl
      _ = (disorderLaw.map τ).map F := (Measure.map_map hF hτ.measurable).symm
      _ = disorderLaw.map F := by rw [hτ.map_eq]
  have hG : AEMeasurable G disorderLaw := by
    rw [hG_eq]
    exact hF.comp_aemeasurable hτ.measurable.aemeasurable
  exact integral_eq_of_map_eq_aux disorderLaw hG hF.aemeasurable hlaw

private theorem profileP2Fun_heatStart_one_eq (β : ℝ) (N a b m : ℕ)
    (hN : 0 < N) (hm : Even m) (hab : Even (b - a)) (ω : Disorder) :
    profileP2Fun β a b (fun w => srwKernel m w)
        (cellAverage N fun _ => (1 : ℝ)) ω =
      profileP2Fun β a b (fun w => srwKernel m w) (fun _ => 1) ω := by
  let A : Finset Site := Polymer.endpoints 0 m
  let ν : Site → ℝ := fun w => srwKernel m w
  let f : Site → ℝ := fun z => cellAverage N (fun _ => (1 : ℝ)) z
  let g : Site → ℝ := fun _ => 1
  have hνA : ∀ w ∉ A, ν w = 0 := by
    intro w hw
    dsimp [ν, A] at hw ⊢
    have h := Polymer.srwKernel_eq_zero_of_not_mem m 0 w hw
    simpa only [sub_zero] using h
  have hAeven (w : Site) (hw : w ∈ A) : w ∈ evenLattice := by
    exact evenLattice_of_even_duration (by simp [evenLattice]) hm hw
  have hterminal (w : Site) (hw : w ∈ A) (z : Site)
      (hz : z ∈ Polymer.endpoints w (b - a)) : f z = g z := by
    dsimp [f, g]
    rw [cellAverage_const hN
      (evenLattice_of_even_duration (hAeven w hw) hab hz) 1]
  have hν0 : ∀ w, 0 ≤ ν w := fun w => by dsimp [ν]; exact srwKernel_nonneg _ _
  have hle := @profileP2Fun_le_of_reachable β a b ν f g A hνA hν0
    (by intro w hw z hz; exact (hterminal w hw z hz).le) ω
  have hge := @profileP2Fun_le_of_reachable β a b ν g f A hνA hν0
    (by intro w hw z hz; exact (hterminal w hw z hz).symm.le) ω
  exact le_antisymm hle hge

/-- The disorder means of a fixed-width heat-start log profile converge to the corresponding SHF
mean. The square-integrability companion is `heatStartLogProfile_square_bound`. -/
theorem tendsto_heatStartLogProfile_mean (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hpair : ∀ {s t δ : ℝ}, 0 ≤ s → s < t → 0 < δ → ∀ (x : Plane) (g : Plane →ᵇ ℝ),
      (∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane =>
        heatKernel δ (p.1 - x) * g p.2) (Z s t ω)) ∧
      Integrable (shfPairing Z s t (fun y => heatKernel δ (y - x)) g) P ∧
      (∫ ω, |shfPairing Z s t (fun y => heatKernel δ (y - x)) g ω| ∂P ≤ ‖g‖) ∧
      TendstoInDistribution
        (fun (N : ℕ) (ω : Disorder) =>
          ∫ p, heatKernel δ (p.1 - x) * g p.2 ∂(polymerMeasure ϑ N s t ω))
        atTop (shfPairing Z s t (fun y => heatKernel δ (y - x)) g)
        (fun _ => disorderLaw) P)
    (hjoint : ∀ (k : ℕ) (s t δ : Fin k → ℝ) (x : Fin k → Plane)
      (g : Fin k → (Plane →ᵇ ℝ)),
      (∀ i, 0 ≤ s i ∧ s i < t i ∧ 0 < δ i) →
      TendstoInDistribution
        (fun (N : ℕ) (ω : Disorder) (i : Fin k) =>
          ∫ p, heatKernel (δ i) (p.1 - x i) * g i p.2
            ∂(polymerMeasure ϑ N (s i) (t i) ω))
        atTop (fun ω i => shfPairing Z (s i) (t i)
          (fun y => heatKernel (δ i) (y - x i)) (g i) ω)
        (fun _ => disorderLaw) P)
    (hpos : ∀ (s t δ : ℝ) (x : Plane) (h₀ : Plane →ᵇ ℝ),
      0 ≤ s → s < t → 0 < δ →
      (∀ᵐ ω ∂P, 0 < shfPairing Z s t
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω) ∧
      AEMeasurable (fun ω => Real.log (shfPairing Z s t
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω)) P)
    (T s δ : ℝ) (h₀ : Plane →ᵇ ℝ) (x : Plane)
    (hs : 0 ≤ s) (hsT : s < T) (hδ : 0 < δ) :
    Tendsto (fun N : ℕ => ∫ ω, heatStartLogProfile ϑ N s T δ x h₀ ω ∂disorderLaw)
      atTop (𝓝 (∫ ω, Real.log (shfPairing Z s T
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω) ∂P)) := by
  have hfield := heatStart_log_tendsto_of ϑ P Z hZ hpair hjoint hpos T h₀ 1
    (fun _ => s) (fun _ => δ) (fun _ => x)
    (by intro i; exact ⟨hs, hsT, hδ⟩)
  have hdist := hfield.2.1.continuous_comp (g := fun v : Fin 1 → ℝ => v 0)
    (continuous_apply 0)
  have hdist' : TendstoInDistribution
      (fun N ω => heatStartLogProfile ϑ N s T δ x h₀ ω) atTop
      (fun ω => Real.log (shfPairing Z s T
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω))
      (fun _ => disorderLaw) P := by
    simpa [heatStartLogProfile, Function.comp_def] using hdist
  obtain ⟨C, _hC, hCN⟩ := heatStartLogProfile_square_bound ϑ hs hsT hδ h₀
  have hM : ∀ᶠ N : ℕ in atTop,
      ∫ ω, |heatStartLogProfile ϑ N s T δ x h₀ ω| ^ (2 : ℝ) ∂disorderLaw ≤
        C * 2 * Real.Gamma 2 := by
    filter_upwards [hCN] with N hN
    calc
      ∫ ω, |heatStartLogProfile ϑ N s T δ x h₀ ω| ^ (2 : ℝ) ∂disorderLaw =
          ∫ ω, |heatStartLogProfile ϑ N s T δ x h₀ ω| ^ 2 ∂disorderLaw := by
        congr 1
        funext ω
        exact Real.rpow_natCast _ 2
      _ ≤ C * 2 * Real.Gamma 2 := (hN x).2
  have hInt : ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω => |heatStartLogProfile ϑ N s T δ x h₀ ω| ^ (2 : ℝ)) disorderLaw := by
    filter_upwards [hCN] with N hN
    have heq : (fun ω => |heatStartLogProfile ϑ N s T δ x h₀ ω| ^ (2 : ℝ)) =
        fun ω => |heatStartLogProfile ϑ N s T δ x h₀ ω| ^ 2 := by
      funext ω
      exact Real.rpow_natCast _ 2
    rw [heq]
    exact (hN x).1
  exact tendsto_integral_of_tendstoInDistribution hdist' (by norm_num : 1 < (2 : ℝ)) hM hInt


private theorem disorderCenter_eq_heatStart_mean
    (ϑ : ℝ) (N : ℕ) (t T δ : ℝ) (hN : 0 < N) :
    (∫ ω', Real.log (profileP2Fun (criticalBeta ϑ N)
      (evenCeil (N * (t + δ))) (evenCeil (N * T))
      (fun w => srwKernel (evenCeil (N * δ)) w) (fun _ => 1) ω') ∂disorderLaw) =
      ∫ ω', heatStartLogProfile ϑ N (t + δ) T δ 0 0 ω' ∂disorderLaw := by
  let a : ℕ := evenCeil (N * (t + δ))
  let b : ℕ := evenCeil (N * T)
  let m : ℕ := evenCeil (N * δ)
  have hm : Even m := by dsimp [m]; exact evenCeil_even (N * δ)
  have hab : Even (b - a) := by
    dsimp [a, b]
    exact (evenCeil_even (N * T)).tsub (evenCeil_even (N * (t + δ)))
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω => by
    have hzero : latticePoint N (0 : Plane) = 0 := by
      simp [latticePoint, nearestEven]
    have hprofile := profileP2Fun_heatStart_one_eq (criticalBeta ϑ N) N a b m
      hN hm hab ω
    dsimp [a, b, m, heatStartLogProfile]
    rw [hzero]
    simp only [sub_zero, Real.exp_zero]
    exact congrArg Real.log hprofile.symm

/-- The integrated regularized lattice field is the heat-start log field shifted by its finite
lattice centering. This identity has no positive-scale hypothesis. -/
private theorem integral_kpzLatticeReversedReg_eq_heatStartLogProfile_sub_center
    (ϑ : ℝ) (N : ℕ) (t T δ : ℝ) (h₀ : Plane →ᵇ ℝ) (φ : TestFn)
    (ω : Disorder) :
    (∫ x, φ x * kpzLatticeReversedReg ϑ N t T δ h₀ x ω) =
      (∫ x, φ x * heatStartLogProfile ϑ N (t + δ) T δ x h₀ ω) -
        (∫ ω', Real.log (profileP2Fun (criticalBeta ϑ N)
          (evenCeil (N * (t + δ))) (evenCeil (N * T))
          (fun w => srwKernel (evenCeil (N * δ)) w) (fun _ => 1) ω') ∂disorderLaw) *
          (∫ x, φ x) := by
  classical
  let a : ℕ := evenCeil (N * (t + δ))
  let b : ℕ := evenCeil (N * T)
  let m : ℕ := evenCeil (N * δ)
  let f : Site → ℝ := fun z => Real.log (profileP2Fun (criticalBeta ϑ N) a b
    (fun w => srwKernel m (w - z)) (cellAverage N fun y => Real.exp (h₀ y)) ω)
  let c : ℝ := ∫ ω', Real.log (profileP2Fun (criticalBeta ϑ N) a b
    (fun w => srwKernel m w) (fun _ => 1) ω') ∂disorderLaw
  obtain ⟨S, hS⟩ := exists_finite_heatStartCells (fun _ : Fin 1 => φ) N
  have hSites : ∀ x, φ x ≠ 0 → latticePoint N x ∈ S := by
    intro x hx
    exact hS 0 x hx
  have hRaw := integral_mul_latticePoint_piecewise φ.continuous φ.hasCompactSupport N f S hSites
  have hReg := integral_mul_latticePoint_piecewise φ.continuous φ.hasCompactSupport N
    (fun z => f z - c) S hSites
  have hOne := integral_mul_latticePoint_piecewise φ.continuous φ.hasCompactSupport N
    (fun _ : Site => 1) S hSites
  have hmcomm : evenCeil (δ * N) = m := by
    dsimp [m]
    congr 1
    ring
  have hraw' :
      (∫ x, φ x * heatStartLogProfile ϑ N (t + δ) T δ x h₀ ω) =
        ∑ z ∈ S, (∫ x in cell N z, φ x) * f z := by
    simpa [f, a, b, m, heatStartLogProfile] using hRaw
  have hreg' :
      (∫ x, φ x * kpzLatticeReversedReg ϑ N t T δ h₀ x ω) =
        ∑ z ∈ S, (∫ x in cell N z, φ x) * (f z - c) := by
    calc
      (∫ x, φ x * kpzLatticeReversedReg ϑ N t T δ h₀ x ω) =
          ∫ x, φ x * (f (latticePoint N x) - c) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          have hshift := integral_log_profile_heatStart_translate (criticalBeta ϑ N) a b m
            (latticePoint N x)
          dsimp [kpzLatticeReversedReg, f, c, a, b, m]
          rw [hmcomm]
          rw [hshift]
      _ = ∑ z ∈ S, (∫ x in cell N z, φ x) * (f z - c) := hReg
  have hOne' : (∫ x, φ x) = ∑ z ∈ S, (∫ x in cell N z, φ x) * (1 : ℝ) := by
    simpa only [mul_one] using hOne
  calc
    (∫ x, φ x * kpzLatticeReversedReg ϑ N t T δ h₀ x ω) =
        ∑ z ∈ S, (∫ x in cell N z, φ x) * (f z - c) := hreg'
    _ = (∑ z ∈ S, (∫ x in cell N z, φ x) * f z) -
        c * (∑ z ∈ S, (∫ x in cell N z, φ x) * (1 : ℝ)) := by
      calc
        _ = ∑ z ∈ S,
            ((∫ x in cell N z, φ x) * f z - (∫ x in cell N z, φ x) * c) := by
          apply Finset.sum_congr rfl
          intro z hz
          ring
        _ = _ := by
          rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
          simp only [mul_one]
          ring
    _ = (∫ x, φ x * heatStartLogProfile ϑ N (t + δ) T δ x h₀ ω) -
          c * (∫ x, φ x) := by rw [← hraw', ← hOne']
    _ = _ := by rfl

/-- A convergent deterministic shift can be passed through joint convergence in distribution. -/
theorem tendstoInDistribution_sub_tendsto {k : ℕ} {Ω' Ω : Type*}
    [MeasurableSpace Ω'] [MeasurableSpace Ω]
    {μ : ℕ → Measure Ω'} {P : Measure Ω}
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure P]
    (X : ℕ → Ω' → Fin k → ℝ) (L : Ω → Fin k → ℝ)
    (D : ℕ → Fin k → ℝ) (D₀ : Fin k → ℝ)
    (hX : TendstoInDistribution X atTop L μ P)
    (hD : Tendsto D atTop (𝓝 D₀)) :
    TendstoInDistribution (fun n ω => X n ω - D n) atTop
      (fun ω => L ω - D₀) μ P := by
  let Y : ℕ → ℕ → Ω' → Fin k → ℝ := fun _ n ω => X n ω - D₀
  let Yl : ℕ → Ω → Fin k → ℝ := fun _ ω => L ω - D₀
  have hY (j : ℕ) : TendstoInDistribution (fun n ω => Y j n ω) atTop (Yl j)
      μ P := by
    simpa [Y, Yl, Function.comp_def] using
      hX.continuous_comp (by fun_prop : Continuous fun v : Fin k → ℝ => v - D₀)
  have hYl : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
      ∫⁻ ω, ENNReal.ofReal ‖Yl j ω - (fun ω => L ω - D₀) ω‖ ∂P ≤
        ENNReal.ofReal ε := by
    intro ε hε
    filter_upwards [] with j
    simp [Yl]
  have hXY : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ᶠ n in atTop,
      ∫⁻ ω, ENNReal.ofReal ‖(fun ω => X n ω - D n) ω - Y j n ω‖ ∂(μ n) ≤
        ENNReal.ofReal ε := by
    intro ε hε
    have hDclose : ∀ᶠ n in atTop, ‖D n - D₀‖ < ε := by
      exact (Metric.tendsto_nhds.mp hD) ε hε
    filter_upwards [] with j
    filter_upwards [hDclose] with n hn
    have hpoint (ω : Ω') :
        ENNReal.ofReal ‖(fun ω => X n ω - D n) ω - Y j n ω‖ ≤ ENNReal.ofReal ε := by
      rw [show (X n ω - D n) - (X n ω - D₀) = D₀ - D n by ring]
      rw [norm_sub_rev]
      exact ENNReal.ofReal_le_ofReal hn.le
    calc
      _ ≤ ∫⁻ _ω : Ω', ENNReal.ofReal ε ∂(μ n) := lintegral_mono fun ω => hpoint ω
      _ = ENNReal.ofReal ε := by simp
  have hXm : ∀ n, AEMeasurable (fun ω => X n ω - D n) (μ n) := by
    intro n
    exact (hX.forall_aemeasurable n).sub aemeasurable_const
  have hLm : AEMeasurable (fun ω => L ω - D₀) P :=
    hX.aemeasurable_limit.sub aemeasurable_const
  exact tendstoInDistribution_of_approx (fun n ω => X n ω - D n) Y Yl
    (fun ω => L ω - D₀) hY hYl hXY hXm hLm

/-- Under the pairing, joint-convergence and positivity hypotheses, the `φ`-integrated
reversed lattice regularizations converge in distribution jointly in `i : Fin k`
to those of `kpzRegularizedReversed`. -/
theorem kpzLatticeReversedReg_tendstoInDistribution
    (ϑ : ℝ) {k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF ϑ P Z)
    (hpair : ∀ {s t δ : ℝ}, 0 ≤ s → s < t → 0 < δ → ∀ (x : Plane) (g : Plane →ᵇ ℝ),
      (∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane =>
        heatKernel δ (p.1 - x) * g p.2) (Z s t ω)) ∧
      Integrable (shfPairing Z s t (fun y => heatKernel δ (y - x)) g) P ∧
      (∫ ω, |shfPairing Z s t (fun y => heatKernel δ (y - x)) g ω| ∂P ≤ ‖g‖) ∧
      TendstoInDistribution
        (fun (N : ℕ) (ω : Disorder) =>
          ∫ p, heatKernel δ (p.1 - x) * g p.2 ∂(polymerMeasure ϑ N s t ω))
        atTop (shfPairing Z s t (fun y => heatKernel δ (y - x)) g)
        (fun _ => disorderLaw) P)
    (hjoint : ∀ (k : ℕ) (s t δ : Fin k → ℝ) (x : Fin k → Plane)
      (g : Fin k → (Plane →ᵇ ℝ)),
      (∀ i, 0 ≤ s i ∧ s i < t i ∧ 0 < δ i) →
      TendstoInDistribution
        (fun (N : ℕ) (ω : Disorder) (i : Fin k) =>
          ∫ p, heatKernel (δ i) (p.1 - x i) * g i p.2
            ∂(polymerMeasure ϑ N (s i) (t i) ω))
        atTop (fun ω i => shfPairing Z (s i) (t i)
          (fun y => heatKernel (δ i) (y - x i)) (g i) ω)
        (fun _ => disorderLaw) P)
    (hpos : ∀ (s t δ : ℝ) (x : Plane) (h₀ : Plane →ᵇ ℝ),
      0 ≤ s → s < t → 0 < δ →
      (∀ᵐ ω ∂P, 0 < shfPairing Z s t (fun y => heatKernel δ (y - x))
        (fun y => Real.exp (h₀ y)) ω) ∧
      AEMeasurable (fun ω => Real.log (shfPairing Z s t
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω)) P)
    (t : Fin k → ℝ) (T : ℝ) (h₀ : Fin k → (Plane →ᵇ ℝ)) (δ : Fin k → ℝ)
    (φ : Fin k → TestFn)
    (ht : ∀ i, 0 ≤ t i ∧ 0 < δ i ∧ t i + δ i < T) :
    TendstoInDistribution
      (fun N ω i => ∫ x, φ i x * kpzLatticeReversedReg ϑ N (t i) T (δ i)
        (h₀ i) x ω)
      atTop
      (fun ω i => ∫ x, φ i x * kpzRegularizedReversed P Z (t i) T (δ i)
        (h₀ i) x ω)
      (fun _ => disorderLaw) P := by
  classical
  let X : ℕ → Disorder → Fin k → ℝ := fun N ω i =>
    ∫ x, φ i x * heatStartLogProfile ϑ N (t i + δ i) T (δ i) x (h₀ i) ω
  let L : Ω → Fin k → ℝ := fun ω i =>
    ∫ x, φ i x * Real.log (shfPairing Z (t i + δ i) T
      (fun y => heatKernel (δ i) (y - x)) (fun y => Real.exp (h₀ i y)) ω)
  let D : ℕ → Fin k → ℝ := fun N i =>
    (∫ ω, Real.log (profileP2Fun (criticalBeta ϑ N)
      (evenCeil (N * (t i + δ i))) (evenCeil (N * T))
      (fun w => srwKernel (evenCeil (N * δ i)) w) (fun _ => 1) ω) ∂disorderLaw) *
      (∫ x, φ i x)
  let D₀ : Fin k → ℝ := fun i =>
    (∫ ω, Real.log (shfPairing Z (t i + δ i) T
      (fun y => heatKernel (δ i) y) (fun _ => 1) ω) ∂P) * (∫ x, φ i x)
  have hparams : ∀ i, 0 ≤ t i + δ i ∧ t i + δ i < T ∧ 0 < δ i := by
    intro i
    have hi := ht i
    exact ⟨by linarith, hi.2.2, hi.2.1⟩
  have hX := heatStart_logField_tendsto_of ϑ P Z hZ hpair hjoint hpos
    T k h₀ (fun i => t i + δ i) δ φ hparams
  have hD : Tendsto D atTop (𝓝 D₀) := by
    apply tendsto_pi_nhds.mpr
    intro i
    have hi := ht i
    have hcenter : ∀ᶠ N : ℕ in atTop,
        (∫ ω, Real.log (profileP2Fun (criticalBeta ϑ N)
          (evenCeil (N * (t i + δ i))) (evenCeil (N * T))
          (fun w => srwKernel (evenCeil (N * δ i)) w) (fun _ => 1) ω) ∂disorderLaw) =
          ∫ ω, heatStartLogProfile ϑ N (t i + δ i) T (δ i) 0 0 ω ∂disorderLaw := by
      filter_upwards [eventually_atTop.2 ⟨1, fun N hN => hN⟩] with N hN
      exact disorderCenter_eq_heatStart_mean ϑ N (t i) T (δ i) (by exact_mod_cast hN)
    have hmean := tendsto_heatStartLogProfile_mean ϑ P Z hZ hpair hjoint hpos
      T (t i + δ i) (δ i) 0 0 (by linarith) hi.2.2 hi.2.1
    have hcenter' := hcenter.mono fun N hN => hN.symm
    have hcenterT := Tendsto.congr' hcenter' hmean
    simpa [D, D₀, mul_comm] using hcenterT.const_mul (∫ x, φ i x)
  have hshift := tendstoInDistribution_sub_tendsto X L D D₀ hX hD
  have heqN : ∀ N : ℕ,
      (fun ω i => X N ω i - D N i) =ᵐ[disorderLaw]
        fun ω i => ∫ x, φ i x * kpzLatticeReversedReg ϑ N (t i) T (δ i)
          (h₀ i) x ω := by
    intro N
    apply Filter.Eventually.of_forall
    intro ω
    funext i
    exact (integral_kpzLatticeReversedReg_eq_heatStartLogProfile_sub_center
      ϑ N (t i) T (δ i) (h₀ i) (φ i) ω).symm
  have heqL : (fun ω i => L ω i - D₀ i) =ᵐ[P]
      fun ω i => ∫ x, φ i x * kpzRegularizedReversed P Z (t i) T (δ i)
        (h₀ i) x ω := by
    have hInt (i : Fin k) : ∀ᵐ ω ∂P,
        Integrable (fun x => φ i x * Real.log (shfPairing Z (t i + δ i) T
          (fun y => heatKernel (δ i) (y - x)) (fun y => Real.exp (h₀ i y)) ω)) := by
      let s : ℝ := t i + δ i
      have hs : 0 ≤ s := by dsimp [s]; linarith [(ht i).1, (ht i).2.1]
      have hsT : s < T := by dsimp [s]; exact (ht i).2.2
      have hlocal : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (Z s T ω) := by
        filter_upwards [hZ.2.1 s T hs hsT] with ω hω
        exact hω.1
      have hg : Measurable (fun y : Plane => Real.exp (h₀ i y)) :=
        Real.continuous_exp.measurable.comp (h₀ i).continuous.measurable
      have hF : AEMeasurable (fun q : Plane × Ω => Real.log
          (shfPairing Z s T (fun y => heatKernel (δ i) (y - q.1))
            (fun y => Real.exp (h₀ i y)) q.2)) (volume.prod P) :=
        aemeasurable_log_heatPairing_joint P (Z s T) (hZ.1 s T hs hsT) hlocal
          (δ i) (by exact (ht i).2.1) (fun y => Real.exp (h₀ i y)) hg
          (fun y => (Real.exp_pos (h₀ i y)).le)
      have hFsec (x : Plane) : AEStronglyMeasurable
          (fun ω => Real.log (shfPairing Z s T (fun y => heatKernel (δ i) (y - x))
            (fun y => Real.exp (h₀ i y)) ω)) P :=
        (hpos s T (δ i) x (h₀ i) hs hsT (ht i).2.1).2.aestronglyMeasurable
      obtain ⟨M, hM, hSq⟩ := shf_heatStartLogField_square_bound ϑ P Z hZ hpair
        hjoint hpos T (h₀ i) (s := s) (δ := δ i) hs hsT (ht i).2.1
      have hProd := integrable_test_mul_joint P hF hFsec hM hSq (φ i)
      exact Integrable.prod_left_ae hProd
    filter_upwards [ae_all_iff.mpr hInt] with ω hω
    funext i
    have hωi := hω i
    let c : ℝ := ∫ ω', Real.log (shfPairing Z (t i + δ i) T
      (fun y => heatKernel (δ i) y) (fun _ => 1) ω') ∂P
    have hφ : Integrable (φ i) volume :=
      (φ i).continuous.integrable_of_hasCompactSupport (φ i).hasCompactSupport
    have hc : Integrable (fun x => φ i x * c) volume := hφ.mul_const c
    change (∫ x, φ i x * Real.log (shfPairing Z (t i + δ i) T
      (fun y => heatKernel (δ i) (y - x)) (fun y => Real.exp (h₀ i y)) ω)) -
      c * (∫ x, φ i x) =
      ∫ x, φ i x * (Real.log (shfPairing Z (t i + δ i) T
        (fun y => heatKernel (δ i) (y - x)) (fun y => Real.exp (h₀ i y)) ω) - c)
    calc
      _ = ∫ x, (φ i x * Real.log (shfPairing Z (t i + δ i) T
          (fun y => heatKernel (δ i) (y - x)) (fun y => Real.exp (h₀ i y)) ω) -
          φ i x * c) := by
        rw [integral_sub hωi hc, integral_mul_const]
        congr 1
        ring
      _ = _ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by ring
  exact hshift.congr heqN heqL

/-- The second moment of a weak limit is lower semicontinuous. -/
theorem eLpNorm_two_le_liminf_of_tendstoInDistribution
    {Ω' Ω : Type*} [MeasurableSpace Ω'] [MeasurableSpace Ω]
    {μ : ℕ → Measure Ω'} {P : Measure Ω} [∀ N, IsProbabilityMeasure (μ N)]
    [IsProbabilityMeasure P] {Y : ℕ → Ω' → ℝ} {X : Ω → ℝ}
    (hY : TendstoInDistribution Y atTop X μ P) :
    eLpNorm X 2 P ≤ atTop.liminf (fun N => eLpNorm (Y N) 2 (μ N)) := by
  let f : ℝ → ℝ := fun x => |x| ^ (2 : ℕ)
  have hf : Continuous f := by fun_prop
  have hfnonneg (x : ℝ) : 0 ≤ f x := by positivity
  have hOpen : ∀ G, IsOpen G → (P.map X) G ≤
      atTop.liminf (fun N => ((μ N).map (Y N)) G) := by
    intro G hG
    exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto hY.tendsto hG
  have hMoment := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    hf hfnonneg hOpen
  have hYmap (N : ℕ) : eLpNorm (id : ℝ → ℝ) 2 ((μ N).map (Y N)) =
      eLpNorm (Y N) 2 (μ N) := by
    rw [eLpNorm_map_measure (p := (2 : ℝ≥0∞)) (measurable_id.aestronglyMeasurable)
      (hY.forall_aemeasurable N)]
    rfl
  have hXmap : eLpNorm (id : ℝ → ℝ) 2 (P.map X) = eLpNorm X 2 P := by
    rw [eLpNorm_map_measure (p := (2 : ℝ≥0∞)) (measurable_id.aestronglyMeasurable)
      hY.aemeasurable_limit]
    rfl
  have hNormSq (ν : Measure ℝ) :
      (eLpNorm (id : ℝ → ℝ) 2 ν) ^ (2 : ℕ) =
        ∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ (2 : ℕ)) ∂ν := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2 : ℝ≥0∞)) (by norm_num)
      (by simp) (measurable_id.aestronglyMeasurable)]
    simp only [ENNReal.toReal_ofNat, one_div]
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul,
      inv_mul_cancel₀ (two_ne_zero : (2 : ℝ) ≠ 0), ENNReal.rpow_one]
    apply lintegral_congr
    intro x
    calc
      ‖id x‖ₑ ^ (2 : ℝ) = ‖id x‖ₑ ^ (2 : ℕ) := ENNReal.rpow_natCast _ _
      _ = ENNReal.ofReal |x| ^ (2 : ℕ) := by
        rw [← ofReal_norm]
        simp only [id_eq, Real.norm_eq_abs]
      _ = ENNReal.ofReal (|x| ^ (2 : ℕ)) :=
        (ENNReal.ofReal_pow (abs_nonneg x) (2 : ℕ)).symm
  have hmomentEq (N : ℕ) :
      ∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ (2 : ℕ)) ∂((μ N).map (Y N)) =
        (eLpNorm (Y N) 2 (μ N)) ^ (2 : ℕ) := by
    rw [← hNormSq, hYmap]
  have hmomentEqX :
      ∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ (2 : ℕ)) ∂(P.map X) =
        (eLpNorm X 2 P) ^ (2 : ℕ) := by
    rw [← hNormSq, hXmap]
  rw [hmomentEqX] at hMoment
  have hmomentSeq :
      (fun N => ∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ (2 : ℕ)) ∂((μ N).map (Y N))) =
        fun N => (eLpNorm (Y N) 2 (μ N)) ^ (2 : ℕ) := by
    funext N
    exact hmomentEq N
  rw [hmomentSeq] at hMoment
  have hmap :
      (atTop.liminf (fun N => eLpNorm (Y N) 2 (μ N))) ^ (2 : ℕ) =
        atTop.liminf (fun N => (eLpNorm (Y N) 2 (μ N)) ^ (2 : ℕ)) :=
    Monotone.map_liminf_of_continuousAt
      (f_incr := fun a b hab => ENNReal.pow_le_pow_left hab)
      (a := fun N => eLpNorm (Y N) 2 (μ N))
      (f_cont := (ENNReal.continuous_pow 2).continuousAt)
  rw [← hmap] at hMoment
  exact (ENNReal.pow_le_pow_left_iff (n := 2) (by norm_num)).mp hMoment

private theorem integral_latticePoint_sub_eq
    {φ : TestFn}
    (N : ℕ) (f g : Site → ℝ) :
    (∫ x, φ x * (f (latticePoint N x) - g (latticePoint N x))) =
      (∫ x, φ x * f (latticePoint N x)) - (∫ x, φ x * g (latticePoint N x)) := by
  classical
  obtain ⟨S, hS⟩ := exists_finite_heatStartCells (fun _ : Fin 1 => φ) N
  have hSites : ∀ x, φ x ≠ 0 → latticePoint N x ∈ S := by
    intro x hx
    exact hS 0 x hx
  have hsub := integral_mul_latticePoint_piecewise φ.continuous φ.hasCompactSupport N
    (fun z => f z - g z) S hSites
  have hf := integral_mul_latticePoint_piecewise φ.continuous φ.hasCompactSupport N f S hSites
  have hg := integral_mul_latticePoint_piecewise φ.continuous φ.hasCompactSupport N g S hSites
  rw [hsub, hf, hg]
  calc
    (∑ z ∈ S, (∫ x in cell N z, φ x) * (f z - g z)) =
        ∑ z ∈ S, ((∫ x in cell N z, φ x) * f z - (∫ x in cell N z, φ x) * g z) := by
      apply Finset.sum_congr rfl
      intro z hz
      ring
    _ = (∑ z ∈ S, (∫ x in cell N z, φ x) * f z) -
        (∑ z ∈ S, (∫ x in cell N z, φ x) * g z) := by
      rw [Finset.sum_sub_distrib]

/-- The lattice approximation bound implies that the tested reversed regularizations are Cauchy in `L²`, with bound `C (|log δ|^(-1/40) + |log δ'|^(-1/40))` for sufficiently small positive widths. -/
theorem kpzRegularizedReversed_eLpNorm_sub_le_of_lattice_smoothing
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF ϑ P Z) (hpair : ∀ {s t δ : ℝ}, 0 ≤ s → s < t → 0 < δ →
      ∀ (x : Plane) (g : Plane →ᵇ ℝ),
        (∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane =>
          heatKernel δ (p.1 - x) * g p.2) (Z s t ω)) ∧
        Integrable (shfPairing Z s t (fun y => heatKernel δ (y - x)) g) P ∧
        (∫ ω, |shfPairing Z s t (fun y => heatKernel δ (y - x)) g ω| ∂P ≤ ‖g‖) ∧
        TendstoInDistribution
          (fun (N : ℕ) (ω : Disorder) =>
            ∫ p, heatKernel δ (p.1 - x) * g p.2 ∂(polymerMeasure ϑ N s t ω))
          atTop (shfPairing Z s t (fun y => heatKernel δ (y - x)) g)
          (fun _ => disorderLaw) P)
    (hjoint : ∀ (k : ℕ) (s t δ : Fin k → ℝ) (x : Fin k → Plane)
      (g : Fin k → (Plane →ᵇ ℝ)),
      (∀ i, 0 ≤ s i ∧ s i < t i ∧ 0 < δ i) →
      TendstoInDistribution
        (fun (N : ℕ) (ω : Disorder) (i : Fin k) =>
          ∫ p, heatKernel (δ i) (p.1 - x i) * g i p.2
            ∂(polymerMeasure ϑ N (s i) (t i) ω))
        atTop (fun ω i => shfPairing Z (s i) (t i)
          (fun y => heatKernel (δ i) (y - x i)) (g i) ω)
        (fun _ => disorderLaw) P)
    (hpos : ∀ (s t δ : ℝ) (x : Plane) (h₀ : Plane →ᵇ ℝ),
      0 ≤ s → s < t → 0 < δ →
      (∀ᵐ ω ∂P, 0 < shfPairing Z s t
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω) ∧
      AEMeasurable (fun ω => Real.log (shfPairing Z s t
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω)) P)
    (hC11 : ExtensionApproxBound) (T a : ℝ) (ha : 0 < a) (haT : a ≤ T)
    (h₀ : Plane →ᵇ ℝ) (φ : TestFn) :
    ∃ C δ₁ : ℝ, 0 ≤ C ∧ 0 < δ₁ ∧
      ∀ δ δ' : ℝ, 0 < δ → 0 < δ' → δ < δ₁ → δ' < δ₁ →
        ∀ t : ℝ, 0 ≤ t → t ≤ T - a → t + δ < T → t + δ' < T →
          eLpNorm (fun ω =>
            (∫ x, φ x * kpzRegularizedReversed P Z t T δ h₀ x ω) -
              (∫ x, φ x * kpzRegularizedReversed P Z t T δ' h₀ x ω)) 2 P ≤
            ENNReal.ofReal (C * (|Real.log δ| ^ (-(1 : ℝ) / 40) +
              |Real.log δ'| ^ (-(1 : ℝ) / 40))) := by
  classical
  obtain ⟨C₁, δc, hδc, hC11b⟩ := hC11 h₀ φ a T |ϑ| ha haT
  let C : ℝ := max C₁ 0
  let δ₁ : ℝ := min δc (1 / 2)
  have hδ₁ : 0 < δ₁ := by dsimp [δ₁]; positivity
  have hδ₁c : δ₁ ≤ δc := by dsimp [δ₁]; exact min_le_left _ _
  have hδ₁half : δ₁ ≤ 1 / 2 := by dsimp [δ₁]; exact min_le_right _ _
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hϑ : ϑ ∈ Set.Icc (-|ϑ|) |ϑ| := abs_le.mp (le_rfl : |ϑ| ≤ |ϑ|)
  refine ⟨C, δ₁, hC, hδ₁, ?_⟩
  intro δ δ' hδ hδ' hδlt hδ'lt t ht htT hδT hδ'T
  let α : ℝ := -(1 : ℝ) / 40
  let r : ℝ := C * (|Real.log δ| ^ α + |Real.log δ'| ^ α)
  have hpowδ : 0 ≤ |Real.log δ| ^ α := Real.rpow_nonneg (abs_nonneg _) _
  have hpowδ' : 0 ≤ |Real.log δ'| ^ α := Real.rpow_nonneg (abs_nonneg _) _
  have htRange : T - t ∈ Set.Icc a T := by
    constructor
    · linarith
    · linarith
  let ds : Fin 2 → ℝ := fun i => if i = 0 then δ else δ'
  let hs : Fin 2 → ℝ := fun _ => t
  let h0s : Fin 2 → Plane →ᵇ ℝ := fun _ => h₀
  let φs : Fin 2 → TestFn := fun _ => φ
  have hregTID := kpzLatticeReversedReg_tendstoInDistribution ϑ P Z hZ hpair hjoint hpos
    hs T h0s ds φs (by
      intro i
      fin_cases i
      · simpa [ds, hs] using ⟨ht, hδ, hδT⟩
      · simpa [ds, hs] using ⟨ht, hδ', hδ'T⟩)
  have hregSub := hregTID.continuous_comp
    (g := fun v : Fin 2 → ℝ => v 0 - v 1) (by fun_prop)
  have hregSub' : TendstoInDistribution
      (fun N ω =>
        (∫ x, φ x * kpzLatticeReversedReg ϑ N t T δ h₀ x ω) -
          (∫ x, φ x * kpzLatticeReversedReg ϑ N t T δ' h₀ x ω))
      atTop
      (fun ω =>
        (∫ x, φ x * kpzRegularizedReversed P Z t T δ h₀ x ω) -
          (∫ x, φ x * kpzRegularizedReversed P Z t T δ' h₀ x ω))
      (fun _ => disorderLaw) P := by
    simpa [ds, hs, h0s, φs, Function.comp_def] using hregSub
  let E : ℝ → ℕ → Disorder → ℝ := fun ε N ω =>
    ∫ x, φ x * (kpzLatticeReversed ϑ N t T h₀ x ω -
      kpzLatticeReversedReg ϑ N t T ε h₀ x ω)
  have hErr (η : ℝ) (N : ℕ) (ω : Disorder) : E η N ω =
      (∫ x, φ x * kpzLatticeReversed ϑ N t T h₀ x ω) -
        (∫ x, φ x * kpzLatticeReversedReg ϑ N t T η h₀ x ω) := by
    let raw : Site → ℝ := fun z =>
      Real.log (profileP2Fun (criticalBeta ϑ N) (evenCeil (N * t)) (evenCeil (N * T))
        (fun w => if w = z then 1 else 0) (cellAverage N fun y => Real.exp (h₀ y)) ω) -
        ∫ ω', Real.log (profileP2Fun (criticalBeta ϑ N) (evenCeil (N * t))
          (evenCeil (N * T)) (fun w => if w = z then 1 else 0) (fun _ => 1) ω') ∂disorderLaw
    let reg (η : ℝ) : Site → ℝ := fun z =>
      Real.log (profileP2Fun (criticalBeta ϑ N) (evenCeil (N * (t + η)))
        (evenCeil (N * T)) (fun w => srwKernel (evenCeil (η * N)) (w - z))
        (cellAverage N fun y => Real.exp (h₀ y)) ω) -
        ∫ ω', Real.log (profileP2Fun (criticalBeta ϑ N) (evenCeil (N * (t + η)))
          (evenCeil (N * T)) (fun w => srwKernel (evenCeil (η * N)) (w - z))
          (fun _ => 1) ω') ∂disorderLaw
    have hsplit := integral_latticePoint_sub_eq (φ := φ) N raw (reg η)
    simpa [E, raw, reg, kpzLatticeReversed, kpzLatticeReversedReg] using hsplit
  have hId (N : ℕ) : (fun ω =>
      (∫ x, φ x * kpzLatticeReversedReg ϑ N t T δ h₀ x ω) -
        (∫ x, φ x * kpzLatticeReversedReg ϑ N t T δ' h₀ x ω)) =
      fun ω => E δ' N ω - E δ N ω := by
    funext ω
    rw [hErr δ N ω, hErr δ' N ω]
    ring
  have hbound : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      eLpNorm (fun ω => E δ' N ω - E δ N ω) 2 disorderLaw ≤ ENNReal.ofReal (r + 2 * ε) := by
    intro ε hε
    have hδc' : δ < δc := lt_of_lt_of_le hδlt hδ₁c
    have hδ'c' : δ' < δc := lt_of_lt_of_le hδ'lt hδ₁c
    have heδ := hC11b δ hδ hδc' ϑ hϑ t T ht htRange ε hε
    have heδ' := hC11b δ' hδ' hδ'c' ϑ hϑ t T ht htRange ε hε
    filter_upwards [heδ, heδ'] with N heδN heδ'N
    have htriangle : eLpNorm (fun ω => E δ' N ω - E δ N ω) 2 disorderLaw ≤
        eLpNorm (E δ' N) 2 disorderLaw + eLpNorm (E δ N) 2 disorderLaw := by
      exact eLpNorm_sub_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hC1 : C₁ ≤ C := le_max_left _ _
    have hb1 : eLpNorm (E δ N) 2 disorderLaw ≤
        ENNReal.ofReal (C * |Real.log δ| ^ α + ε) := by
      refine heδN.trans ?_
      have hcoeff := mul_le_mul_of_nonneg_right hC1 hpowδ
      have hcoeff' : C₁ * |Real.log δ| ^ (-(1 : ℝ) / 40) ≤
          C * |Real.log δ| ^ α := by simpa [α] using hcoeff
      exact ENNReal.ofReal_le_ofReal (add_le_add_left hcoeff' ε)
    have hb2 : eLpNorm (E δ' N) 2 disorderLaw ≤
        ENNReal.ofReal (C * |Real.log δ'| ^ α + ε) := by
      refine heδ'N.trans ?_
      have hcoeff := mul_le_mul_of_nonneg_right hC1 hpowδ'
      have hcoeff' : C₁ * |Real.log δ'| ^ (-(1 : ℝ) / 40) ≤
          C * |Real.log δ'| ^ α := by simpa [α] using hcoeff
      exact ENNReal.ofReal_le_ofReal (add_le_add_left hcoeff' ε)
    have hsum : (C * |Real.log δ| ^ α + ε) +
        (C * |Real.log δ'| ^ α + ε) = r + 2 * ε := by
      dsimp [r, C]
      ring
    have hsum_nonneg : 0 ≤ (C * |Real.log δ| ^ α + ε) := by positivity
    have hsum'_nonneg : 0 ≤ (C * |Real.log δ'| ^ α + ε) := by positivity
    have hsumENN : ENNReal.ofReal (C * |Real.log δ| ^ α + ε) +
        ENNReal.ofReal (C * |Real.log δ'| ^ α + ε) ≤ ENNReal.ofReal (r + 2 * ε) := by
      rw [← ENNReal.ofReal_add hsum_nonneg hsum'_nonneg, hsum]
    calc
      _ ≤ eLpNorm (E δ N) 2 disorderLaw + eLpNorm (E δ' N) 2 disorderLaw := by
        simpa [add_comm] using htriangle
      _ ≤ _ := add_le_add hb1 hb2
      _ ≤ _ := hsumENN
  have hliminf := eLpNorm_two_le_liminf_of_tendstoInDistribution hregSub'
  have hseqNorm : (fun N => eLpNorm (fun ω =>
      (∫ x, φ x * kpzLatticeReversedReg ϑ N t T δ h₀ x ω) -
        (∫ x, φ x * kpzLatticeReversedReg ϑ N t T δ' h₀ x ω)) 2 disorderLaw) =
      fun N => eLpNorm (fun ω => E δ' N ω - E δ N ω) 2 disorderLaw := by
    funext N
    apply eLpNorm_congr_ae
    filter_upwards [] with ω
    exact congrFun (hId N) ω
  rw [hseqNorm] at hliminf
  have hlimsup (ε : ℝ) (hε : 0 < ε) :
      Filter.limsup (fun N => eLpNorm (fun ω => E δ' N ω - E δ N ω) 2 disorderLaw) atTop ≤
        ENNReal.ofReal (r + 2 * ε) :=
    Filter.limsup_le_of_le (by isBoundedDefault) (hbound ε hε)
  have hbound_lim : atTop.liminf
      (fun N => eLpNorm (fun ω => E δ' N ω - E δ N ω) 2 disorderLaw) ≤ ENNReal.ofReal r := by
    let u : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (r + 2 / ((n : ℝ) + 1))
    have hu : Tendsto u atTop (𝓝 (ENNReal.ofReal r)) := by
      have hn : Tendsto (fun n : ℕ => r + 2 / ((n : ℝ) + 1)) atTop (𝓝 r) := by
        have hden : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        simpa [div_eq_mul_inv, mul_comm] using hden.const_mul 2 |>.const_add r
      simpa [u, Function.comp_def] using
        (ENNReal.continuous_ofReal.continuousAt.tendsto (x := r)).comp hn
    have hlimsup_le (n : ℕ) : Filter.limsup
        (fun N => eLpNorm (fun ω => E δ' N ω - E δ N ω) 2 disorderLaw) atTop ≤ u n := by
      have h := hlimsup (1 / ((n : ℝ) + 1)) (by positivity)
      refine h.trans_eq ?_
      simp only [u]
      congr 1
      ring
    have hbounded : IsBoundedUnder (· ≤ ·) atTop
        (fun N => eLpNorm (fun ω => E δ' N ω - E δ N ω) 2 disorderLaw) :=
      ⟨⊤, Filter.Eventually.of_forall fun _ => le_top⟩
    have hliminf_le (n : ℕ) : atTop.liminf
        (fun N => eLpNorm (fun ω => E δ' N ω - E δ N ω) 2 disorderLaw) ≤ u n :=
      (Filter.liminf_le_limsup hbounded).trans (hlimsup_le n)
    exact ge_of_tendsto hu (Filter.Eventually.of_forall hliminf_le)
  have hregBound : eLpNorm (fun ω =>
      (∫ x, φ x * kpzRegularizedReversed P Z t T δ h₀ x ω) -
        (∫ x, φ x * kpzRegularizedReversed P Z t T δ' h₀ x ω)) 2 P ≤ ENNReal.ofReal r :=
    hliminf.trans hbound_lim
  simpa [r, α] using hregBound

private theorem memLp_integral_test_of_uniform_square
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {F : Plane × Ω → ℝ} (hF : AEMeasurable F (volume.prod P))
    (hFsec : ∀ x, AEStronglyMeasurable (fun ω => F (x, ω)) P)
    {M : ℝ} (hM : 0 ≤ M)
    (hSq : ∀ x, Integrable (fun ω => |F (x, ω)| ^ 2) P ∧
      ∫ ω, |F (x, ω)| ^ 2 ∂P ≤ M) (φ : TestFn) :
    MemLp (fun ω => ∫ x, φ x * F (x, ω)) 2 P := by
  classical
  let K : Set Plane := tsupport (φ : Plane → ℝ)
  have hKcompact : IsCompact K := φ.hasCompactSupport
  have hKmeas : MeasurableSet K := hKcompact.isClosed.measurableSet
  have hφzero (x : Plane) (hx : x ∉ K) : φ x = 0 := by
    by_contra hne
    have hxSupp : x ∈ Function.support (φ : Plane → ℝ) := by
      simpa [Function.mem_support] using hne
    exact hx (by simpa [K] using subset_tsupport (φ : Plane → ℝ) hxSupp)
  have hKvol : volume K < ∞ := hKcompact.measure_lt_top
  have hKvolNe : volume K ≠ ∞ := hKvol.ne
  let K2 : Set (Plane × Ω) := K ×ˢ Set.univ
  have hK2 : MeasurableSet K2 := hKmeas.prod MeasurableSet.univ
  let G : Plane × Ω → ℝ := K2.indicator (fun q => |F q| ^ 2)
  have hFsq : AEMeasurable (fun q => |F q| ^ 2) (volume.prod P) :=
    ((continuous_abs.pow 2).measurable.comp_aemeasurable hF)
  have hGsm : AEStronglyMeasurable G (volume.prod P) := by
    dsimp [G]
    exact hFsq.aestronglyMeasurable.indicator hK2
  have hGsec (x : Plane) : Integrable (fun ω => G (x, ω)) P := by
    by_cases hx : x ∈ K
    · simpa [G, K2, hx] using (hSq x).1
    · simp [G, K2, hx]
  let H : Plane → ℝ := fun x => ∫ ω, ‖G (x, ω)‖ ∂P
  have hHmeas : AEMeasurable H volume := hGsm.norm.integral_prod_right'.aemeasurable
  have hHbound (x : Plane) : H x ≤ K.indicator (fun _ => M) x := by
    by_cases hx : x ∈ K
    · simpa [H, G, K2, hx, Real.norm_eq_abs] using (hSq x).2
    · simp [H, G, K2, hx]
  have hmajorOn : IntegrableOn (fun _ : Plane => M) K volume := integrableOn_const hKvolNe
  have hmajor : Integrable (K.indicator (fun _ => M)) volume :=
    hmajorOn.integrable_indicator hKmeas
  have hHint : Integrable H volume := by
    apply hmajor.mono' hHmeas.aestronglyMeasurable
    filter_upwards [] with x
    have hHnonneg : 0 ≤ H x := integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun ω => norm_nonneg (G (x, ω)))
    by_cases hx : x ∈ K
    · simpa [Real.norm_eq_abs, abs_of_nonneg hHnonneg, abs_of_nonneg hM, hx] using
        hHbound x
    · have hHzero : H x = 0 := by
        apply le_antisymm
        · simpa [K, hx] using hHbound x
        · exact integral_nonneg_of_ae
            (Filter.Eventually.of_forall fun ω => norm_nonneg (G (x, ω)))
      simp [hx, hHzero]
  have hGint : Integrable G (volume.prod P) :=
    (integrable_prod_iff hGsm).2 ⟨Filter.Eventually.of_forall hGsec, hHint⟩
  have hGsecAE : ∀ᵐ ω ∂P, Integrable (fun x => G (x, ω)) volume :=
    hGint.prod_left_ae
  have hFsecAE : ∀ᵐ ω ∂P, AEStronglyMeasurable (fun x => F (x, ω)) volume :=
    hF.aestronglyMeasurable.prod_swap.prodMk_left
  have hHomega : Integrable (fun ω => ∫ x, ‖G (x, ω)‖ ∂volume) P :=
    hGint.integral_norm_prod_right
  let μK : Measure Plane := volume.restrict K
  have hGintEq (ω : Ω) : (∫ x, ‖G (x, ω)‖ ∂volume) =
      ∫ x, |F (x, ω)| ^ 2 ∂μK := by
    have hpoint : (fun x : Plane => ‖G (x, ω)‖) =
        K.indicator (fun x => |F (x, ω)| ^ 2) := by
      funext x
      by_cases hx : x ∈ K
      · simp [G, K2, hx, Real.norm_eq_abs]
      · simp [G, K2, hx]
    rw [hpoint, ← integral_indicator hKmeas]
  let A : ℝ := ∫ x, |φ x| ^ 2 ∂μK
  have hφsquare : Integrable (fun x => |φ x| ^ 2) volume := by
    have habsSupport : HasCompactSupport (fun x : Plane => |φ x|) :=
      φ.hasCompactSupport.abs
    have hmulSupport : HasCompactSupport (fun x : Plane => |φ x| * |φ x|) :=
      habsSupport.mul_left
    have hmul : Integrable (fun x : Plane => |φ x| * |φ x|) volume :=
      (φ.continuous.abs.mul φ.continuous.abs).integrable_of_hasCompactSupport hmulSupport
    simpa only [pow_two] using hmul
  have hφmemSq : MemLp (fun x : Plane => ‖φ x‖ ^ (2 : ℝ)) 1 volume := by
    apply memLp_one_iff_integrable.mpr
    simpa [Real.norm_eq_abs, sq_abs] using hφsquare
  have hφmem : MemLp (fun x : Plane => φ x) 2 volume := by
    have hdiv : (2 : ℝ≥0∞) / 2 = 1 := ENNReal.div_self (by simp) (by simp)
    have hφmemSq' : MemLp (fun x : Plane => ‖φ x‖ ^ (ENNReal.toReal (2 : ℝ≥0∞)))
        ((2 : ℝ≥0∞) / 2) volume := by simpa [hdiv] using hφmemSq
    have h := (memLp_norm_rpow_iff (f := fun x : Plane => φ x) (p := (2 : ℝ≥0∞))
      (q := (2 : ℝ≥0∞)) φ.continuous.measurable.aestronglyMeasurable
      (by norm_num) (by simp)).mp hφmemSq'
    simpa using h
  have hφmemK : MemLp (fun x : Plane => φ x) 2 μK :=
    hφmem.mono_measure Measure.restrict_le_self
  have hProd : Integrable (fun q : Plane × Ω => φ q.1 * F q) (volume.prod P) :=
    integrable_test_mul_joint P hF hFsec hM hSq φ
  have hProdSecAE : ∀ᵐ ω ∂P, Integrable (fun x => φ x * F (x, ω)) volume :=
    hProd.prod_left_ae
  have hYsqAE : ∀ᵐ ω ∂P,
      |∫ x, φ x * F (x, ω)| ^ 2 ≤ A * ∫ x, |F (x, ω)| ^ 2 ∂μK := by
    filter_upwards [hGsecAE, hFsecAE, hProdSecAE] with ω hGω hFω hProdω
    have hGω' : Integrable (K.indicator (fun x => |F (x, ω)| ^ 2)) volume := by
      convert hGω using 1
      ext x
      by_cases hx : x ∈ K <;> simp [G, K2, hx]
    have hF2K : Integrable (fun x => |F (x, ω)| ^ 2) μK := by
      simpa only [μK, IntegrableOn] using
        (integrable_indicator_iff hKmeas).mp hGω'
    have hFmemSq : MemLp (fun x : Plane => ‖F (x, ω)‖ ^ (2 : ℝ)) 1 μK := by
      apply memLp_one_iff_integrable.mpr
      simpa [Real.norm_eq_abs, sq_abs] using hF2K
    have hFmem : MemLp (fun x : Plane => F (x, ω)) 2 μK := by
      have hdiv : (2 : ℝ≥0∞) / 2 = 1 := ENNReal.div_self (by simp) (by simp)
      have hFmemSq' : MemLp (fun x : Plane => ‖F (x, ω)‖ ^ (ENNReal.toReal (2 : ℝ≥0∞)))
          ((2 : ℝ≥0∞) / 2) μK := by simpa [hdiv] using hFmemSq
      have h := (memLp_norm_rpow_iff (f := fun x : Plane => F (x, ω)) (p := (2 : ℝ≥0∞))
        (q := (2 : ℝ≥0∞)) (hFω.mono_measure Measure.restrict_le_self)
        (by norm_num) (by simp)).mp hFmemSq'
      simpa using h
    have hHolder : (2 : ℝ).HolderConjugate 2 := by
      rw [Real.holderConjugate_iff]
      norm_num
    have hφmemK' : MemLp (fun x : Plane => φ x) (ENNReal.ofReal (2 : ℝ)) μK := by
      simpa using hφmemK
    have hFmem' : MemLp (fun x : Plane => F (x, ω)) (ENNReal.ofReal (2 : ℝ)) μK := by
      simpa using hFmem
    have hCS := integral_mul_norm_le_Lp_mul_Lq (p := 2) (q := 2)
      hHolder hφmemK' hFmem'
    have htestInt : Integrable (fun x => φ x * F (x, ω)) volume := hProdω
    have htestK : Integrable (fun x => φ x * F (x, ω)) μK :=
      htestInt.mono_measure Measure.restrict_le_self
    have hset : (∫ x in K, φ x * F (x, ω) ∂volume) =
        ∫ x, φ x * F (x, ω) ∂volume :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by rw [hφzero x hx]; simp
    have hCS' : ‖∫ x, φ x * F (x, ω) ∂volume‖ ≤
        A ^ (1 / 2 : ℝ) * (∫ x, |F (x, ω)| ^ 2 ∂μK) ^ (1 / 2 : ℝ) := by
      rw [← hset]
      calc
        _ ≤ ∫ x in K, ‖φ x * F (x, ω)‖ ∂volume :=
          norm_integral_le_integral_norm (fun x => φ x * F (x, ω))
        _ = ∫ x, ‖φ x‖ * ‖F (x, ω)‖ ∂μK := by
          simp only [μK]
          congr 1
          ext x
          exact norm_mul _ _
        _ ≤ _ := by
          simpa [A, Real.norm_eq_abs, Real.rpow_natCast] using hCS
    have hYsq : |(∫ x, φ x * F (x, ω) ∂volume)| ^ 2 ≤
        A * (∫ x, |F (x, ω)| ^ 2 ∂μK) := by
      have hA : 0 ≤ A := integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => sq_nonneg _)
      have hB : 0 ≤ ∫ x, |F (x, ω)| ^ 2 ∂μK :=
        integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => sq_nonneg _)
      have hnonneg : 0 ≤ A ^ (1 / 2 : ℝ) *
          (∫ x, |F (x, ω)| ^ 2 ∂μK) ^ (1 / 2 : ℝ) := by positivity
      have hbound := hCS'
      rw [Real.norm_eq_abs] at hbound
      have hrootA : (A ^ (1 / 2 : ℝ)) ^ 2 = A := by
        rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hA]
      have hrootB : ((∫ x, |F (x, ω)| ^ 2 ∂μK) ^ (1 / 2 : ℝ)) ^ 2 =
          ∫ x, |F (x, ω)| ^ 2 ∂μK := by
        rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hB]
      calc
        |∫ x, φ x * F (x, ω) ∂volume| ^ 2 ≤
            (A ^ (1 / 2 : ℝ) *
              (∫ x, |F (x, ω)| ^ 2 ∂μK) ^ (1 / 2 : ℝ)) ^ 2 :=
          (sq_le_sq₀ (abs_nonneg _) hnonneg).2 hbound
        _ = A * ∫ x, |F (x, ω)| ^ 2 ∂μK := by
          rw [mul_pow, hrootA, hrootB]
    exact hYsq
  have hYsqInt : Integrable (fun ω => |∫ x, φ x * F (x, ω)| ^ 2) P := by
    have hHomega' : Integrable (fun ω => ∫ x, |F (x, ω)| ^ 2 ∂μK) P :=
      hHomega.congr (Filter.Eventually.of_forall hGintEq)
    have hmajorω : Integrable (fun ω => A * ∫ x, |F (x, ω)| ^ 2 ∂μK) P :=
      hHomega'.const_mul A
    have hYae : AEStronglyMeasurable (fun ω => ∫ x, φ x * F (x, ω)) P :=
      hProd.aestronglyMeasurable.prod_swap.integral_prod_right'
    have hYsqMeas : AEStronglyMeasurable
        (fun ω => |∫ x, φ x * F (x, ω)| ^ 2) P :=
      ((continuous_abs.pow 2).measurable.comp_aemeasurable hYae.aemeasurable).aestronglyMeasurable
    apply hmajorω.mono' hYsqMeas
    filter_upwards [hYsqAE] with ω hω
    calc
      ‖|∫ x, φ x * F (x, ω)| ^ 2‖ = |∫ x, φ x * F (x, ω)| ^ 2 := by
        rw [Real.norm_eq_abs]
        exact abs_of_nonneg (sq_nonneg _)
      _ ≤ A * ∫ x, |F (x, ω)| ^ 2 ∂μK := hω
  have hYmemSq : MemLp (fun ω => ‖∫ x, φ x * F (x, ω)‖ ^ (2 : ℝ)) 1 P := by
    apply memLp_one_iff_integrable.mpr
    simpa [Real.norm_eq_abs, sq_abs] using hYsqInt
  have hYmem : MemLp (fun ω => ∫ x, φ x * F (x, ω)) 2 P := by
    have hYae : AEStronglyMeasurable (fun ω => ∫ x, φ x * F (x, ω)) P :=
      hProd.aestronglyMeasurable.prod_swap.integral_prod_right'
    have hdiv : (2 : ℝ≥0∞) / 2 = 1 := ENNReal.div_self (by simp) (by simp)
    have hYmemSq' : MemLp (fun ω => ‖∫ x, φ x * F (x, ω)‖ ^ (ENNReal.toReal (2 : ℝ≥0∞)))
        ((2 : ℝ≥0∞) / 2) P := by simpa [hdiv] using hYmemSq
    exact (memLp_norm_rpow_iff (f := fun ω => ∫ x, φ x * F (x, ω))
      (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) hYae
      (by norm_num) (by simp)).mp hYmemSq'
  exact hYmem

/-- If `E |F (x, ·)|² ≤ M` uniformly in `x` and `c² ≤ M`, then `ω ↦ ∫ φ x * (F (x, ω) - c)`
lies in `L²(P)`. -/
theorem memLp_integral_test_sub_const_of_uniform_square
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {F : Plane × Ω → ℝ} (hF : AEMeasurable F (volume.prod P))
    (hFsec : ∀ x, AEStronglyMeasurable (fun ω => F (x, ω)) P)
    {M : ℝ} (hM : 0 ≤ M)
    (hSq : ∀ x, Integrable (fun ω => |F (x, ω)| ^ 2) P ∧
      ∫ ω, |F (x, ω)| ^ 2 ∂P ≤ M)
    {c : ℝ} (hcSq : c ^ 2 ≤ M) (φ : TestFn) :
    MemLp (fun ω => ∫ x, φ x * (F (x, ω) - c)) 2 P := by
  let G : Plane × Ω → ℝ := fun q => F q - c
  have hG : AEMeasurable G (volume.prod P) := hF.sub aemeasurable_const
  have hGsec (x : Plane) : AEStronglyMeasurable (fun ω => G (x, ω)) P :=
    (hFsec x).sub aestronglyMeasurable_const
  have hGsq (x : Plane) : Integrable (fun ω => |G (x, ω)| ^ 2) P := by
    have hFmem : MemLp (fun ω => F (x, ω)) 2 P := by
      apply (memLp_two_iff_integrable_sq (hFsec x)).2
      simpa [sq_abs] using (hSq x).1
    have hGmem : MemLp (fun ω => G (x, ω)) 2 P := by
      change MemLp (fun ω => F (x, ω) - c) 2 P
      exact hFmem.sub (memLp_const c)
    have hGmem' := (memLp_two_iff_integrable_sq (hGsec x)).1 hGmem
    simpa [sq_abs] using hGmem'
  have hGbound (x : Plane) : ∫ ω, |G (x, ω)| ^ 2 ∂P ≤ 4 * M := by
    have hmajor : Integrable (fun ω => 2 * |F (x, ω)| ^ 2 + 2 * c ^ 2) P :=
      ((hSq x).1.const_mul 2).add (integrable_const (2 * c ^ 2))
    have hle : ∀ ω, |G (x, ω)| ^ 2 ≤ 2 * |F (x, ω)| ^ 2 + 2 * c ^ 2 := by
      intro ω
      dsimp [G]
      have habs : |F (x, ω) - c| ≤ |F (x, ω)| + |c| := by
        simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (F (x, ω)) (-c)
      calc
        |F (x, ω) - c| ^ 2 ≤ (|F (x, ω)| + |c|) ^ 2 := by
          exact pow_le_pow_left₀ (abs_nonneg _) habs 2
        _ ≤ 2 * |F (x, ω)| ^ 2 + 2 * c ^ 2 := by
          nlinarith [sq_nonneg (|F (x, ω)| - |c|), sq_abs (c)]
    calc
      ∫ ω, |G (x, ω)| ^ 2 ∂P ≤ ∫ ω, 2 * |F (x, ω)| ^ 2 + 2 * c ^ 2 ∂P :=
        integral_mono (hGsq x) hmajor hle
      _ = 2 * (∫ ω, |F (x, ω)| ^ 2 ∂P) + 2 * c ^ 2 := by
        rw [integral_add ((hSq x).1.const_mul 2) (integrable_const (2 * c ^ 2)),
          integral_const_mul, integral_const]
        simp
      _ ≤ 4 * M := by nlinarith [(hSq x).2, hM]
  have hM' : 0 ≤ 4 * M := by positivity
  exact memLp_integral_test_of_uniform_square P hG hGsec hM'
    (fun x => ⟨hGsq x, hGbound x⟩) φ

set_option linter.style.haveILetI false in
/-- Representatives `Y δ` that are `m`-measurable a.e. and `L²`-Cauchy at rate `ε δ + ε δ'`
have an `m`-measurable `L²` limit `X` with `‖Y δ - X‖₂ ≤ ε δ`. -/
theorem exists_L2_limit_of_cauchy_ae_representatives
    {Ω : Type*} [m0 : MeasurableSpace Ω] (m : MeasurableSpace Ω)
    (hm : m ≤ m0) (P : @Measure Ω m0) [IsProbabilityMeasure P]
    (Y : ℝ → Ω → ℝ) (ε : ℝ → ℝ) (δ₁ : ℝ)
    (hrep : ∀ δ ∈ Set.Ioo 0 δ₁, ∃ f : Ω → ℝ,
      Measurable[m] f ∧ f =ᵐ[P] Y δ)
    (hmem : ∀ δ ∈ Set.Ioo 0 δ₁, MemLp (Y δ) 2 P)
    (hε : Tendsto ε (𝓝[>] 0) (𝓝 0))
    (hε0 : ∀ δ ∈ Set.Ioo 0 δ₁, 0 ≤ ε δ)
    (hC : ∀ δ ∈ Set.Ioo 0 δ₁, ∀ δ' ∈ Set.Ioo 0 δ₁,
      eLpNorm (fun ω => Y δ ω - Y δ' ω) 2 P ≤ ENNReal.ofReal (ε δ + ε δ')) :
    ∃ X : Ω → ℝ, Measurable[m] X ∧ ∀ δ ∈ Set.Ioo 0 δ₁,
      eLpNorm (fun ω => Y δ ω - X ω) 2 P ≤ ENNReal.ofReal (ε δ) := by
  letI : MeasurableSpace Ω := m0
  classical
  let R : ℝ → Ω → ℝ := fun δ =>
    if hδ : δ ∈ Set.Ioo 0 δ₁ then Classical.choose (hrep δ hδ) else fun _ => 0
  have hRspec (δ : ℝ) (hδ : δ ∈ Set.Ioo 0 δ₁) :
      Measurable[m] (R δ) ∧ R δ =ᵐ[P] Y δ := by
    dsimp [R]
    rw [dite_eq_left hδ]
    exact Classical.choose_spec (hrep δ hδ)
  have hRmeas (δ : ℝ) (hδ : δ ∈ Set.Ioo 0 δ₁) : Measurable[m] (R δ) :=
    (hRspec δ hδ).1
  have hRmem (δ : ℝ) (hδ : δ ∈ Set.Ioo 0 δ₁) : MemLp (R δ) 2 P := by
    have hYsm : AEStronglyMeasurable (Y δ) P := (hmem δ hδ).aestronglyMeasurable
    have hRsm : AEStronglyMeasurable (R δ) P := hYsm.congr (hRspec δ hδ).2.symm
    apply (hmem δ hδ).congr_enorm hRsm
    filter_upwards [(hRspec δ hδ).2] with ω hω
    rw [hω]
  have hRC : ∀ δ ∈ Set.Ioo 0 δ₁, ∀ δ' ∈ Set.Ioo 0 δ₁,
      eLpNorm (fun ω => R δ ω - R δ' ω) 2 P ≤ ENNReal.ofReal (ε δ + ε δ') := by
    intro δ hδ δ' hδ'
    calc
      eLpNorm (fun ω => R δ ω - R δ' ω) 2 P =
          eLpNorm (fun ω => Y δ ω - Y δ' ω) 2 P := by
        apply eLpNorm_congr_ae
        filter_upwards [(hRspec δ hδ).2, (hRspec δ' hδ').2] with ω hω hω'
        rw [hω, hω']
      _ ≤ ENNReal.ofReal (ε δ + ε δ') := hC δ hδ δ' hδ'
  obtain ⟨X, hXm, hRateR⟩ := @exists_L2_limit_of_cauchy Ω m0 m hm P inferInstance R ε δ₁
    (fun δ hδ => ⟨hRmeas δ hδ, hRmem δ hδ⟩) hε hε0 hRC
  refine ⟨X, hXm, ?_⟩
  intro δ hδ
  calc
    eLpNorm (fun ω => Y δ ω - X ω) 2 P =
        eLpNorm (fun ω => R δ ω - X ω) 2 P := by
      apply eLpNorm_congr_ae
      filter_upwards [(hRspec δ hδ).2] with ω hω
      rw [← hω]
    _ ≤ ENNReal.ofReal (ε δ) := hRateR δ hδ

/-- If `E |G (x, ·)|² ≤ M` uniformly in `x`, then `ω ↦ ∫ φ x * (G (x, ω) - E G (0, ·))`
lies in `L²(P)`. -/
theorem memLp_centered_integral_test_of_uniform_square
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {G : Plane × Ω → ℝ} (hG : AEMeasurable G (volume.prod P))
    (hGsec : ∀ x, AEStronglyMeasurable (fun ω => G (x, ω)) P)
    {M : ℝ} (hM : 0 ≤ M)
    (hSq : ∀ x, Integrable (fun ω => |G (x, ω)| ^ 2) P ∧
      ∫ ω, |G (x, ω)| ^ 2 ∂P ≤ M) (φ : TestFn) :
    MemLp (fun ω => ∫ x, φ x * (G (x, ω) - ∫ ω', G (0, ω') ∂P)) 2 P := by
  have hG0mem : MemLp (fun ω => G (0, ω)) 2 P := by
    apply (memLp_two_iff_integrable_sq (hGsec 0)).2
    simpa [sq_abs] using (hSq 0).1
  have hHolder : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hG0mem' : MemLp (fun ω => G (0, ω)) (ENNReal.ofReal (2 : ℝ)) P := by
    simpa using hG0mem
  have honeMem : MemLp (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) P := by
    simpa using (memLp_const (1 : ℝ) : MemLp (fun _ : Ω => (1 : ℝ)) 2 P)
  have hCS := integral_mul_norm_le_Lp_mul_Lq hHolder hG0mem' honeMem
  let c : ℝ := ∫ ω, G (0, ω) ∂P
  have hcSq : c ^ 2 ≤ M := by
    have hcAbs : |c| ≤ (∫ ω, |G (0, ω)| ^ 2 ∂P) ^ (1 / 2 : ℝ) := by
      calc
        |c| = ‖∫ ω, G (0, ω) ∂P‖ := by simp [c, Real.norm_eq_abs]
        _ ≤ ∫ ω, ‖G (0, ω)‖ ∂P := norm_integral_le_integral_norm _
        _ = ∫ ω, ‖G (0, ω)‖ * ‖(1 : ℝ)‖ ∂P := by simp
        _ ≤ (∫ ω, ‖G (0, ω)‖ ^ 2 ∂P) ^ (1 / 2 : ℝ) *
            (∫ ω, ‖(1 : ℝ)‖ ^ 2 ∂P) ^ (1 / 2 : ℝ) := hCS
        _ = (∫ ω, |G (0, ω)| ^ 2 ∂P) ^ (1 / 2 : ℝ) := by
          simp [Real.norm_eq_abs]
    have hB : 0 ≤ ∫ ω, |G (0, ω)| ^ 2 ∂P :=
      integral_nonneg_of_ae (Filter.Eventually.of_forall fun ω => sq_nonneg _)
    have hroot : ((∫ ω, |G (0, ω)| ^ 2 ∂P) ^ (1 / 2 : ℝ)) ^ 2 =
        ∫ ω, |G (0, ω)| ^ 2 ∂P := by
      rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hB]
    have hcAbsSq : |c| ^ 2 ≤ (∫ ω, |G (0, ω)| ^ 2 ∂P) := by
      calc
        |c| ^ 2 ≤ ((∫ ω, |G (0, ω)| ^ 2 ∂P) ^ (1 / 2 : ℝ)) ^ 2 :=
          (sq_le_sq₀ (abs_nonneg _) (Real.rpow_nonneg hB _) ).2 hcAbs
        _ = _ := hroot
    nlinarith [sq_abs c, (hSq 0).2]
  have hmem := memLp_integral_test_sub_const_of_uniform_square P hG hGsec hM hSq hcSq φ
  simpa [c] using hmem

set_option linter.style.haveILetI false in
/-- The Cauchy bound `C (|log δ|^(-1/40) + |log δ'|^(-1/40))` on `m`-measurable a.e.
representatives gives an `m`-measurable `L²` limit `X` with `‖Y δ - X‖₂ ≤ C |log δ|^(-1/40)`. -/
theorem exists_L2_limit_of_log_cauchy_ae_representatives
    {Ω : Type*} [m0 : MeasurableSpace Ω] (m : MeasurableSpace Ω)
    (hm : m ≤ m0) (P : @Measure Ω m0) [IsProbabilityMeasure P]
    (Y : ℝ → Ω → ℝ) (C δ₁ : ℝ) (hC : 0 ≤ C)
    (hrep : ∀ δ ∈ Set.Ioo 0 δ₁, ∃ f : Ω → ℝ,
      Measurable[m] f ∧ f =ᵐ[P] Y δ)
    (hmem : ∀ δ ∈ Set.Ioo 0 δ₁, MemLp (Y δ) 2 P)
    (hCauchy : ∀ δ ∈ Set.Ioo 0 δ₁, ∀ δ' ∈ Set.Ioo 0 δ₁,
      @eLpNorm Ω ℝ _ _ m0 (fun ω => Y δ ω - Y δ' ω) 2 P ≤
        ENNReal.ofReal (C * (|Real.log δ| ^ (-(1 : ℝ) / 40) +
          |Real.log δ'| ^ (-(1 : ℝ) / 40)))) :
    ∃ X : Ω → ℝ, Measurable[m] X ∧ ∀ δ ∈ Set.Ioo 0 δ₁,
      @eLpNorm Ω ℝ _ _ m0 (fun ω => Y δ ω - X ω) 2 P ≤
        ENNReal.ofReal (C * |Real.log δ| ^ (-(1 : ℝ) / 40)) := by
  letI : MeasurableSpace Ω := m0
  let ε : ℝ → ℝ := fun δ => C * |Real.log δ| ^ (-(1 : ℝ) / 40)
  have hlog : Tendsto (fun δ : ℝ => |Real.log δ|) (𝓝[>] 0) atTop :=
    tendsto_abs_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hε : Tendsto ε (𝓝[>] 0) (𝓝 0) := by
    have hpow := (tendsto_rpow_neg_atTop (y := (1 : ℝ) / 40) (by norm_num)).comp hlog
    have hpow' : Tendsto (fun δ : ℝ => |Real.log δ| ^ (-(1 : ℝ) / 40))
        (𝓝[>] 0) (𝓝 0) := by
      have hexp : -(1 : ℝ) / 40 = -(1 / 40 : ℝ) := by ring
      simpa only [Function.comp_def, hexp] using hpow
    simpa [ε] using hpow'.const_mul C
  have hε0 : ∀ δ ∈ Set.Ioo 0 δ₁, 0 ≤ ε δ := by
    intro δ _
    dsimp [ε]
    exact mul_nonneg hC (Real.rpow_nonneg (abs_nonneg _) _)
  exact @exists_L2_limit_of_cauchy_ae_representatives Ω m0 m hm P inferInstance Y ε δ₁
    hrep hmem hε hε0 (by
      intro δ hδ δ' hδ'
      simpa [ε, mul_add] using hCauchy δ hδ δ' hδ')

set_option linter.style.haveILetI false in
private theorem locallyFinite_of_closedBall_mass (μ : Measure (Plane × Plane))
    (hμ : ∀ n : ℕ, μ (Metric.closedBall (0 : Plane × Plane) (n : ℝ)) < ∞) :
    IsLocallyFiniteMeasure μ := by
  have hfc : IsFiniteMeasureOnCompacts μ := by
    refine ⟨?_⟩
    intro K hK
    obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : Plane × Plane)
    obtain ⟨n, hn⟩ := exists_nat_gt r
    calc
      μ K ≤ μ (Metric.closedBall (0 : Plane × Plane) r) := measure_mono hr
      _ ≤ μ (Metric.closedBall (0 : Plane × Plane) (n : ℝ)) :=
        measure_mono (Metric.closedBall_subset_closedBall (le_of_lt hn))
      _ < ∞ := hμ n
  letI : IsFiniteMeasureOnCompacts μ := hfc
  infer_instance

set_option linter.style.haveILetI false in
/-- A regularized spatial log pairing has a version measurable with respect to the sigma algebra
generated by the SHF coordinates. -/
theorem exists_shfSigma_measurable_kpzRegularizedReversed_integral
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (t T δ : ℝ) (ht : 0 ≤ t) (hδ : 0 < δ) (hsT : t + δ < T)
    (h₀ : Plane →ᵇ ℝ) (φ : TestFn) :
    ∃ f : Ω → ℝ,
      Measurable[shfSigma Z] f ∧
      f =ᵐ[P] (fun ω => ∫ x, φ x * kpzRegularizedReversed P Z t T δ h₀ x ω) := by
  classical
  let s : ℝ := t + δ
  have hs : 0 ≤ s := by dsimp [s]; linarith
  have hsT' : s < T := by dsimp [s]; exact hsT
  let ν : Measure (Measure (Plane × Plane)) := P.map (Z s T)
  have hcoord : Measurable (Z s T) := hZ.1 s T hs hsT'
  have hcoordA : AEMeasurable (Z s T) P := hcoord.aemeasurable
  let K : ℕ → Set (Plane × Plane) := fun n => Metric.closedBall 0 (n : ℝ)
  have hKmeas (n : ℕ) : MeasurableSet (K n) := Metric.isClosed_closedBall.measurableSet
  let S : Set (Measure (Plane × Plane)) := {m | ∀ n, m (K n) < ∞}
  have hSmeas : MeasurableSet S := by
    simp only [S, Set.ofPred_forall]
    exact MeasurableSet.iInter fun n =>
      measurableSet_lt ((Measure.measurable_coe (hKmeas n))) measurable_const
  have hsource : ∀ᵐ ω ∂P, ∀ n, (Z s T ω) (K n) < ∞ := by
    filter_upwards [(hZ.2.1 s T hs hsT').mono fun ω hω => hω.1] with ω hω
    intro n
    letI : IsLocallyFiniteMeasure (Z s T ω) := hω
    exact (isCompact_closedBall (0 : Plane × Plane) (n : ℝ)).measure_lt_top
  have hmassLaw : ∀ᵐ m ∂ν, m ∈ S :=
    (ae_map_iff hcoordA hSmeas).2 hsource
  have hlocalLaw : ∀ᵐ m ∂ν, IsLocallyFiniteMeasure m := by
    filter_upwards [hmassLaw] with m hm
    apply locallyFinite_of_closedBall_mass
    intro n
    exact hm n
  let c : ℝ := ∫ ω, Real.log (shfPairing Z s T
    (fun y => heatKernel δ y) (fun _ => 1) ω) ∂P
  let g : Plane → ℝ := fun y => Real.exp (h₀ y)
  let F : Measure (Plane × Plane) → ℝ := fun m =>
    ∫ x, φ x * (Real.log (∫ p, heatKernel δ (p.1 - x) * g p.2 ∂m) - c)
  have hg : Measurable g := Real.continuous_exp.measurable.comp h₀.continuous.measurable
  have hgn (y : Plane) : 0 ≤ g y := (Real.exp_pos _).le
  have hφ : Measurable (φ : Plane → ℝ) := φ.continuous.measurable
  have hF : AEMeasurable F ν := by
    exact aemeasurable_integral_log_heatPairing ν (fun m => m) measurable_id
      hlocalLaw δ c hδ g φ hg hgn hφ
  let Fm : Measure (Plane × Plane) → ℝ := hF.mk F
  have hFm : Measurable Fm := hF.measurable_mk
  have hle : MeasurableSpace.comap (Z s T) inferInstance ≤ Critical2DKPZ.shfSigma Z := by
    dsimp [Critical2DKPZ.shfSigma]
    apply le_iSup_of_le s
    apply le_iSup_of_le T
    exact le_iSup_of_le ⟨hs, hsT'⟩ le_rfl
  have hcoordSigma : Measurable[Critical2DKPZ.shfSigma Z] (Z s T) :=
    Measurable.of_comap_le hle
  have hAE : (F ∘ Z s T) =ᵐ[P] (Fm ∘ Z s T) :=
    ae_eq_comp hcoordA hF.ae_eq_mk
  refine ⟨Fm ∘ Z s T, hFm.comp hcoordSigma, ?_⟩
  filter_upwards [hAE.symm] with ω hω
  rw [hω]
  simp [F, g, c, s, kpzRegularizedReversed, shfPairing]

end Critical2DKPZ.JointConvergence

end
