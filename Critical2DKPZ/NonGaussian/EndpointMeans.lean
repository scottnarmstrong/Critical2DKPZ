/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.JointConvergence.HeatStartLogConvergence
public import Critical2DKPZ.LocalSobolev.Inputs
public import Critical2DKPZ.FutureProfiles.EndpointTranslation
import Mathlib.Tactic

/-! # Spatial constancy of heat-start logarithmic means -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.JointConvergence
open scoped BoundedContinuousFunction ENNReal Topology

namespace Critical2DKPZ.NonGaussian

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

private theorem profileP2Fun_heatStart_one_eq (β : ℝ) (N a b m : ℕ)
    (hN : 0 < N) (hm : Even m) (hab : Even (b - a)) (x : Plane) (ω : Disorder) :
    profileP2Fun β a b (fun w => srwKernel m (w - latticePoint N x))
        (cellAverage N fun _ => (1 : ℝ)) ω =
      profileP2Fun β a b (fun w => srwKernel m (w - latticePoint N x))
        (fun _ => 1) ω := by
  let A : Finset Site := Polymer.endpoints (latticePoint N x) m
  let ν : Site → ℝ := fun w => srwKernel m (w - latticePoint N x)
  let f : Site → ℝ := fun z => cellAverage N (fun _ => (1 : ℝ)) z
  let g : Site → ℝ := fun _ => 1
  have hνA : ∀ w ∉ A, ν w = 0 := by
    intro w hw
    dsimp [ν, A]
    exact Polymer.srwKernel_eq_zero_of_not_mem m (latticePoint N x) w hw
  have hν0 : ∀ w, 0 ≤ ν w := fun w => by
    dsimp [ν]
    exact srwKernel_nonneg _ _
  have hxEven : latticePoint N x ∈ evenLattice := latticePoint_mem_evenLattice N x
  have hterminal (w : Site) (hw : w ∈ A) (z : Site)
      (hz : z ∈ Polymer.endpoints w (b - a)) : f z = g z := by
    dsimp [f, g]
    have hwEven : w ∈ evenLattice := evenLattice_of_even_duration hxEven hm hw
    have hzEven : z ∈ evenLattice := evenLattice_of_even_duration hwEven hab hz
    exact cellAverage_const hN hzEven 1
  have hterminalLe (w : Site) (hw : w ∈ A) (z : Site)
      (hz : z ∈ Polymer.endpoints w (b - a)) : f z ≤ g z :=
    (hterminal w hw z hz).le
  have hle := profileP2Fun_le_of_reachable (β := β) (a := a) (b := b)
    ν f g A hνA hν0 hterminalLe ω
  have hge := profileP2Fun_le_of_reachable (β := β) (a := a) (b := b)
    ν g f A hνA hν0 (by
      intro w hw z hz
      exact (hterminal w hw z hz).symm.le) ω
  exact le_antisymm hle hge

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
    rw [FutureProfiles.profileP2Fun_translate β a b x
      (fun w => srwKernel m w) (fun _ => 1) ω]
  have hlaw : disorderLaw.map G = disorderLaw.map F := by
    calc
      disorderLaw.map G = disorderLaw.map (F ∘ τ) := by rw [hG_eq]; rfl
      _ = (disorderLaw.map τ).map F :=
        (Measure.map_map hF hτ.measurable).symm
      _ = disorderLaw.map F := by rw [hτ.map_eq]
  have hG : AEMeasurable G disorderLaw := by
    rw [hG_eq]
    exact hF.comp_aemeasurable hτ.measurable.aemeasurable
  exact integral_eq_of_map_eq_aux disorderLaw hG hF.aemeasurable hlaw

/-- Convergence of heat-start logarithms and uniform square-moment bounds imply that their limiting mean is independent of the spatial centre. -/
theorem integral_log_heatPairing_eq_of_heatStartLogAt (ϑ : ℝ) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hHeatStartLogInput : LocalSobolev.HeatStartLogAt ϑ P Z)
    {s T δ : ℝ} (hs : 0 ≤ s) (hsT : s < T) (hδ : 0 < δ) (x : Plane) :
    (∫ ω, Real.log (shfPairing Z s T (fun y => heatKernel δ (y - x))
      (fun _ => (1 : ℝ)) ω) ∂P) =
      ∫ ω, Real.log (shfPairing Z s T (fun y => heatKernel δ y)
        (fun _ => (1 : ℝ)) ω) ∂P := by
  let h₀ : Plane →ᵇ ℝ := 0
  let Lx : Ω → ℝ := fun ω => Real.log (shfPairing Z s T
    (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω)
  let L0 : Ω → ℝ := fun ω => Real.log (shfPairing Z s T
    (fun y => heatKernel δ y) (fun y => Real.exp (h₀ y)) ω)
  let XN : ℕ → Disorder → ℝ := fun N ω => heatStartLogProfile ϑ N s T δ x h₀ ω
  let XN0 : ℕ → Disorder → ℝ := fun N ω => heatStartLogProfile ϑ N s T δ 0 h₀ ω
  have hparams : ∀ i : Fin 1, 0 ≤ (fun _ : Fin 1 => s) i ∧
      (fun _ : Fin 1 => s) i < T ∧ 0 < (fun _ : Fin 1 => δ) i := by
    intro i
    exact ⟨hs, hsT, hδ⟩
  have hKx := hHeatStartLogInput T h₀ 1 (fun _ => s) (fun _ => δ) (fun _ => x) hparams
  have hK0 := hHeatStartLogInput T h₀ 1 (fun _ => s) (fun _ => δ) (fun _ => 0) hparams
  have hdistX : TendstoInDistribution XN atTop Lx
      (fun _ : ℕ => disorderLaw) P := by
    have h := hKx.2.1.continuous_comp (g := fun v : Fin 1 → ℝ => v 0)
      (continuous_apply 0)
    simpa [XN, Lx, h₀, heatStartLogProfile, Function.comp_def] using h
  have hdist0 : TendstoInDistribution XN0 atTop L0
      (fun _ : ℕ => disorderLaw) P := by
    have h := hK0.2.1.continuous_comp (g := fun v : Fin 1 → ℝ => v 0)
      (continuous_apply 0)
    simpa [XN0, L0, h₀, heatStartLogProfile, Function.comp_def] using h
  obtain ⟨C, hC, hCN⟩ := heatStartLogProfile_square_bound ϑ hs hsT hδ h₀
  let M : ℝ := C * 2 * Real.Gamma 2
  have hM : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg (mul_nonneg hC (by norm_num))
      (Real.Gamma_pos_of_pos (by norm_num)).le
  have hmeanX : Tendsto (fun N => ∫ ω, XN N ω ∂disorderLaw) atTop (𝓝 (∫ ω, Lx ω ∂P)) := by
    have hbound : ∀ᶠ N : ℕ in atTop,
        ∫ ω, |XN N ω| ^ (2 : ℝ) ∂disorderLaw ≤ M := by
      filter_upwards [hCN] with N hN
      simpa [XN, M, heatStartLogProfile, Real.rpow_natCast] using (hN x).2
    have hint : ∀ᶠ N : ℕ in atTop,
        Integrable (fun ω => |XN N ω| ^ (2 : ℝ)) disorderLaw := by
      filter_upwards [hCN] with N hN
      simpa [XN, heatStartLogProfile, Real.rpow_natCast] using (hN x).1
    exact tendsto_integral_of_tendstoInDistribution hdistX (by norm_num) hbound hint
  have hmean0 : Tendsto (fun N => ∫ ω, XN0 N ω ∂disorderLaw) atTop (𝓝 (∫ ω, L0 ω ∂P)) := by
    have hbound : ∀ᶠ N : ℕ in atTop,
        ∫ ω, |XN0 N ω| ^ (2 : ℝ) ∂disorderLaw ≤ M := by
      filter_upwards [hCN] with N hN
      simpa [XN0, M, heatStartLogProfile, Real.rpow_natCast] using (hN 0).2
    have hint : ∀ᶠ N : ℕ in atTop,
        Integrable (fun ω => |XN0 N ω| ^ (2 : ℝ)) disorderLaw := by
      filter_upwards [hCN] with N hN
      simpa [XN0, heatStartLogProfile, Real.rpow_natCast] using (hN 0).1
    exact tendsto_integral_of_tendstoInDistribution hdist0 (by norm_num) hbound hint
  have hmeanEq : ∀ᶠ N : ℕ in atTop,
      (∫ ω, XN N ω ∂disorderLaw) = ∫ ω, XN0 N ω ∂disorderLaw := by
    filter_upwards [eventually_atTop.2 ⟨1, fun N hN => hN⟩] with N hN
    let a := evenCeil (N * s)
    let b := evenCeil (N * T)
    let m := evenCeil (N * δ)
    have hNpos : 0 < N := by omega
    have hm : Even m := by dsimp [m]; exact evenCeil_even (N * δ)
    have hab : Even (b - a) := by
      dsimp [a, b]
      exact (evenCeil_even (N * T)).tsub (evenCeil_even (N * s))
    have hprofX : ∀ ω, XN N ω = Real.log
        (profileP2Fun (criticalBeta ϑ N) a b
          (fun w => srwKernel m (w - latticePoint N x)) (fun _ => 1) ω) := by
      intro ω
      simpa [XN, heatStartLogProfile, h₀, a, b, m] using congrArg Real.log
        (profileP2Fun_heatStart_one_eq (criticalBeta ϑ N) N a b m
          hNpos hm hab x ω)
    have hprof0 : ∀ ω, XN0 N ω = Real.log
        (profileP2Fun (criticalBeta ϑ N) a b
          (fun w => srwKernel m w) (fun _ => 1) ω) := by
      intro ω
      have hzero : latticePoint N (0 : Plane) = 0 := by
        simp [latticePoint, nearestEven]
      simpa [XN0, heatStartLogProfile, h₀, a, b, m, hzero] using congrArg Real.log
        (profileP2Fun_heatStart_one_eq (criticalBeta ϑ N) N a b m
          hNpos hm hab 0 ω)
    have htranslate := integral_log_profile_heatStart_translate
      (criticalBeta ϑ N) a b m (latticePoint N x)
    rw [show (fun ω => XN N ω) = _ from funext hprofX,
      show (fun ω => XN0 N ω) = _ from funext hprof0]
    simpa [a, b, m] using htranslate
  have hmeanX' : Tendsto (fun N => ∫ ω, XN0 N ω ∂disorderLaw) atTop
      (𝓝 (∫ ω, Lx ω ∂P)) := Tendsto.congr' hmeanEq hmeanX
  have heq := tendsto_nhds_unique hmean0 hmeanX'
  simpa [Lx, L0, h₀, Real.exp_zero] using heq.symm

end Critical2DKPZ.NonGaussian

end
