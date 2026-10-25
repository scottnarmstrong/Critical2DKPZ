/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.JointConvergence.ThmToyJointLimitEstimates
import Mathlib.Tactic

/-! # Joint lattice convergence to the reversed regularized-field limit -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open Critical2DKPZ.SHF.Limit
open scoped BoundedContinuousFunction ENNReal Topology

namespace Critical2DKPZ.JointConvergence

private theorem tendsto_abs_log_inv40_lattice :
    Tendsto (fun δ : ℝ => |Real.log δ| ^ (-(1 : ℝ) / 40))
      (𝓝[>] 0) (𝓝 0) := by
  have hlog : Tendsto (fun δ : ℝ => |Real.log δ|) (𝓝[>] 0) atTop :=
    tendsto_abs_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hpow := (tendsto_rpow_neg_atTop (y := (1 : ℝ) / 40) (by norm_num)).comp hlog
  have hexp : -(1 : ℝ) / 40 = -(1 / 40 : ℝ) := by ring
  simpa only [Function.comp_def, hexp] using hpow

private theorem integral_latticePoint_sub_eq_lattice
    {φ : TestFn} (N : ℕ) (f g : Site → ℝ) :
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

/-- Given a family `X` with the `L²` log-width rate to the reversed regularized fields, the reversed
lattice fields tested against `φ i` converge jointly in law to `X (t i) (h₀ i) (φ i)`. -/
theorem thm_toy_joint_lattice_limit_of
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (T : ℝ) (hT : 0 < T)
    (hpair : ∀ {s t δ : ℝ}, 0 ≤ s → s < t → 0 < δ → ∀ (x : Plane) (g : Plane →ᵇ ℝ),
      (∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane => heatKernel δ (p.1 - x) * g p.2) (Z s t ω)) ∧
      Integrable (shfPairing Z s t (fun y => heatKernel δ (y - x)) g) P ∧
      (∫ ω, |shfPairing Z s t (fun y => heatKernel δ (y - x)) g ω| ∂P ≤ ‖g‖) ∧
      TendstoInDistribution
        (fun (N : ℕ) (ω : Disorder) =>
          ∫ p, heatKernel δ (p.1 - x) * g p.2 ∂(polymerMeasure ϑ N s t ω)) atTop
        (shfPairing Z s t (fun y => heatKernel δ (y - x)) g) (fun _ => disorderLaw) P)
    (hjoint : ∀ (k : ℕ) (s t δ : Fin k → ℝ) (x : Fin k → Plane)
      (g : Fin k → (Plane →ᵇ ℝ)),
      (∀ i, 0 ≤ s i ∧ s i < t i ∧ 0 < δ i) →
      TendstoInDistribution
        (fun (N : ℕ) (ω : Disorder) (i : Fin k) =>
          ∫ p, heatKernel (δ i) (p.1 - x i) * g i p.2
            ∂(polymerMeasure ϑ N (s i) (t i) ω)) atTop
        (fun ω i => shfPairing Z (s i) (t i)
          (fun y => heatKernel (δ i) (y - x i)) (g i) ω) (fun _ => disorderLaw) P)
    (hpos : ∀ (s t δ : ℝ) (x : Plane) (h₀ : Plane →ᵇ ℝ),
      0 ≤ s → s < t → 0 < δ →
      (∀ᵐ ω ∂P, 0 < shfPairing Z s t (fun y => heatKernel δ (y - x))
        (fun y => Real.exp (h₀ y)) ω) ∧
      AEMeasurable (fun ω => Real.log (shfPairing Z s t
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω)) P)
    (hC11 : ExtensionApproxBound)
    (X : ℝ → (Plane →ᵇ ℝ) → TestFn → Ω → ℝ)
    (hXm : ∀ (t : ℝ) (h₀ : Plane →ᵇ ℝ) (φ : TestFn), 0 ≤ t → t < T →
      Measurable[shfSigma Z] (X t h₀ φ))
    (hRate : ∀ (h₀ : Plane →ᵇ ℝ) (φ : TestFn) (a : ℝ), 0 < a → a ≤ T →
      ∃ C δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₁ → ∀ t : ℝ,
        0 ≤ t → t ≤ T - a →
        eLpNorm (fun ω => (∫ x, φ x * kpzRegularizedReversed P Z t T δ h₀ x ω) -
          X t h₀ φ ω) 2 P ≤ ENNReal.ofReal
            (C * |Real.log (δ / (T - t))| ^ (-(1 : ℝ) / 40))) :
    ∀ (k : ℕ) (t : Fin k → ℝ) (h₀ : Fin k → (Plane →ᵇ ℝ)) (φ : Fin k → TestFn),
      (∀ i, 0 ≤ t i ∧ t i < T) →
      TendstoInDistribution
        (fun (N : ℕ) (ω : Disorder) (i : Fin k) =>
          ∫ x, φ i x * kpzLatticeReversed ϑ N (t i) T (h₀ i) x ω)
        atTop (fun ω i => X (t i) (h₀ i) (φ i) ω) (fun _ => disorderLaw) P := by
  classical
  intro k t h₀ φ ht
  let a : Fin k → ℝ := fun i => (T - t i) / 2
  have ha (i : Fin k) : 0 < a i := by
    dsimp [a]
    linarith [(ht i).2]
  have haT (i : Fin k) : a i ≤ T := by
    dsimp [a]
    linarith [(ht i).1, hT]
  have hRatePack (i : Fin k) :
      ∃ C d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ < d →
        eLpNorm (fun ω => (∫ x, φ i x * kpzRegularizedReversed P Z (t i) T δ (h₀ i) x ω) -
          X (t i) (h₀ i) (φ i) ω) 2 P ≤ ENNReal.ofReal
            (C * |Real.log (δ / (T - t i))| ^ (-(1 : ℝ) / 40)) := by
    obtain ⟨C, d, hd, hb⟩ := hRate (h₀ i) (φ i) (a i) (ha i) (haT i)
    refine ⟨C, d, hd, ?_⟩
    intro δ hδ hδd
    exact hb δ hδ hδd (t i) (ht i).1 (by dsimp [a]; linarith [(ht i).2])
  choose Cr dr hdr hRateBound using hRatePack
  have hC11Pack (i : Fin k) :
      ∃ C d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ < d → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ N : ℕ in atTop,
          eLpNorm (fun ω => ∫ x, φ i x *
            (kpzLatticeReversed ϑ N (t i) T (h₀ i) x ω -
              kpzLatticeReversedReg ϑ N (t i) T δ (h₀ i) x ω)) 2 disorderLaw ≤
            ENNReal.ofReal (C * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε) := by
    obtain ⟨C, d, hd, hb⟩ := hC11 (h₀ i) (φ i) (a i) T |ϑ| (ha i) (haT i)
    refine ⟨C, d, hd, ?_⟩
    intro δ hδ hδd ε hε
    have hϑ : ϑ ∈ Set.Icc (-|ϑ|) |ϑ| := abs_le.mp (le_rfl : |ϑ| ≤ |ϑ|)
    have htime : T - t i ∈ Set.Icc (a i) T := by
      constructor
      · change (T - t i) / 2 ≤ T - t i
        linarith [(ht i).2]
      · change T - t i ≤ T
        linarith [(ht i).1]
    exact hb δ hδ hδd ϑ hϑ (t i) T (ht i).1 htime ε hε
  choose Cc dc hdc hC11Bound using hC11Pack
  let d : Fin k → ℝ := fun i => min (dr i) (min (dc i) (a i)) / 2
  have hd (i : Fin k) : 0 < d i := by
    dsimp [d]
    have h1 := hdr i
    have h2 := hdc i
    have h3 := ha i
    positivity
  let δseq : ℕ → Fin k → ℝ := fun j i => d i / ((j : ℝ) + 1)
  have hδseqpos (j : ℕ) (i : Fin k) : 0 < δseq j i := by
    dsimp [δseq]
    have hdi := hd i
    positivity
  have hδseqRate (j : ℕ) (i : Fin k) : δseq j i < dr i := by
    have hdle : d i ≤ dr i / 2 := by
      dsimp [d]
      have := min_le_left (dr i) (min (dc i) (a i))
      linarith
    have hj : (1 : ℝ) ≤ (j : ℝ) + 1 := by exact_mod_cast Nat.le_add_left 1 j
    dsimp [δseq]
    have hden : 1 ≤ (j : ℝ) + 1 := hj
    calc
      d i / ((j : ℝ) + 1) ≤ d i := by
        exact div_le_self (le_of_lt (hd i)) hden
      _ ≤ dr i / 2 := hdle
      _ < dr i := by linarith [hdr i]
  have hδseqC11 (j : ℕ) (i : Fin k) : δseq j i < dc i := by
    have hdle : d i ≤ dc i / 2 := by
      dsimp [d]
      have hmin : min (dr i) (min (dc i) (a i)) ≤ dc i :=
        (min_le_right _ _).trans (min_le_left _ _)
      exact div_le_div_of_nonneg_right hmin (by norm_num)
    have hj : (1 : ℝ) ≤ (j : ℝ) + 1 := by exact_mod_cast Nat.le_add_left 1 j
    dsimp [δseq]
    calc
      d i / ((j : ℝ) + 1) ≤ d i := by exact div_le_self (le_of_lt (hd i)) hj
      _ ≤ dc i / 2 := hdle
      _ < dc i := by linarith [hdc i]
  have hδseqTime (j : ℕ) (i : Fin k) : t i + δseq j i < T := by
    have hdle : d i ≤ a i / 2 := by
      dsimp [d]
      have hmin : min (dc i) (a i) ≤ a i := min_le_right _ _
      exact div_le_div_of_nonneg_right (le_trans (min_le_right _ _) hmin) (by norm_num)
    have hj : (1 : ℝ) ≤ (j : ℝ) + 1 := by exact_mod_cast Nat.le_add_left 1 j
    have hδle : δseq j i ≤ a i / 2 := by
      dsimp [δseq]
      exact (div_le_self (le_of_lt (hd i)) hj).trans hdle
    dsimp [a] at hδle ⊢
    linarith [(ht i).2]
  have hδseqZero (i : Fin k) : Tendsto (fun j : ℕ => δseq j i) atTop (𝓝 0) := by
    have hrecip : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hmul := hrecip.const_mul (d i)
    simpa [δseq, div_eq_mul_inv, mul_comm] using hmul
  have hδseqPosFilter (i : Fin k) :
      Tendsto (fun j : ℕ => δseq j i) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hδseqZero i, ?_⟩
    filter_upwards [Filter.Eventually.of_forall (fun j => hδseqpos j i)] with j hj
    exact hj
  let Y : ℕ → ℕ → Disorder → Fin k → ℝ := fun j N ω i =>
    ∫ x, φ i x * kpzLatticeReversedReg ϑ N (t i) T (δseq j i) (h₀ i) x ω
  let Yl : ℕ → Ω → Fin k → ℝ := fun j ω i =>
    ∫ x, φ i x * kpzRegularizedReversed P Z (t i) T (δseq j i) (h₀ i) x ω
  let L : Ω → Fin k → ℝ := fun ω i => X (t i) (h₀ i) (φ i) ω
  let XN : ℕ → Disorder → Fin k → ℝ := fun N ω i =>
    ∫ x, φ i x * kpzLatticeReversed ϑ N (t i) T (h₀ i) x ω
  have hY (j : ℕ) : TendstoInDistribution (fun N => Y j N) atTop (Yl j)
      (fun _ => disorderLaw) P := by
    apply kpzLatticeReversedReg_tendstoInDistribution ϑ P Z hZ hpair hjoint hpos
      (t := t) (T := T) (h₀ := h₀) (δ := δseq j) (φ := φ)
    intro i
    exact ⟨(ht i).1, hδseqpos j i, hδseqTime j i⟩
  have hL2Tendsto (i : Fin k) :
      Tendsto (fun j : ℕ => eLpNorm
        (fun ω => Yl j ω i - L ω i) 2 P) atTop (𝓝 0) := by
    let Q : ℝ → Ω → ℝ := fun δ ω =>
      (∫ x, φ i x * kpzRegularizedReversed P Z (t i) T δ (h₀ i) x ω) -
        X (t i) (h₀ i) (φ i) ω
    have hpow : Tendsto (fun j : ℕ =>
        |Real.log (δseq j i / (T - t i))| ^ (-(1 : ℝ) / 40)) atTop (𝓝 0) := by
      have hratio0 : Tendsto (fun j : ℕ => δseq j i / (T - t i)) atTop (𝓝 0) := by
        have hcont : Continuous fun x : ℝ => x / (T - t i) := by fun_prop
        have hcomp := hcont.continuousAt.tendsto.comp (hδseqZero i)
        have hfun : (fun x : ℝ => x / (T - t i)) ∘ (fun j : ℕ => δseq j i) =
            fun j => δseq j i / (T - t i) := rfl
        rw [hfun] at hcomp
        simpa only [zero_div] using hcomp
      have hratioPos : Tendsto (fun j : ℕ => δseq j i / (T - t i)) atTop (𝓝[>] 0) := by
        apply tendsto_nhdsWithin_iff.mpr
        refine ⟨hratio0, ?_⟩
        filter_upwards [Filter.Eventually.of_forall (fun j => hδseqpos j i)] with j hj
        exact div_pos (hδseqpos j i) (by linarith [(ht i).2])
      simpa only [Function.comp_def] using tendsto_abs_log_inv40_lattice.comp hratioPos
    have hpowENN : Tendsto (fun j : ℕ => ENNReal.ofReal
        (Cr i * |Real.log (δseq j i / (T - t i))| ^ (-(1 : ℝ) / 40))) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal (hpow.const_mul (Cr i))
    have hbound : ∀ᶠ j : ℕ in atTop,
        eLpNorm (Q (δseq j i)) 2 P ≤ ENNReal.ofReal
          (Cr i * |Real.log (δseq j i / (T - t i))| ^ (-(1 : ℝ) / 40)) := by
      filter_upwards [Filter.Eventually.of_forall (fun j => hδseqRate j i)] with j hj
      exact hRateBound i (δseq j i) (hδseqpos j i) (hδseqRate j i)
    have hnorm : Tendsto (fun j : ℕ => eLpNorm (Q (δseq j i)) 2 P) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hpowENN
        (Filter.Eventually.of_forall fun _ => bot_le) hbound
    simpa [Q, Yl, L] using hnorm
  have hYlConverges : ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
      ∫⁻ ω, ENNReal.ofReal ‖Yl j ω - L ω‖ ∂P ≤ ENNReal.ofReal ε := by
    intro ε hε
    let m : ℝ := Fintype.card (Fin k)
    let η : ℝ := ε / (m + 1)
    have hm : 0 ≤ m := by dsimp [m]; positivity
    have hη : 0 < η := by dsimp [η]; positivity
    have hcoordEventually (i : Fin k) : ∀ᶠ j : ℕ in atTop,
        eLpNorm (fun ω => Yl j ω i - L ω i) 2 P ≤ ENNReal.ofReal η :=
      (hL2Tendsto i).eventually (Iic_mem_nhds (ENNReal.ofReal_pos.mpr hη))
    have hall : ∀ᶠ j : ℕ in atTop, ∀ i ∈ Finset.univ, 
        eLpNorm (fun ω => Yl j ω i - L ω i) 2 P ≤ ENNReal.ofReal η := by
      rw [eventually_all_finset]
      intro i hi
      exact hcoordEventually i
    filter_upwards [hall] with j hj
    have hvec := lintegral_norm_pi_sub_le_of_uniform_coordinate_eLpNorm k P
      (Yl j) L (fun i => hj i (Finset.mem_univ i))
    have hscale : (Fintype.card (Fin k) : ℝ) * η ≤ ε := by
      dsimp [m, η]
      have hm' : 0 ≤ (Fintype.card (Fin k) : ℝ) := by positivity
      have hden : 0 < (Fintype.card (Fin k) : ℝ) + 1 := by positivity
      calc
        (Fintype.card (Fin k) : ℝ) * (ε / ((Fintype.card (Fin k) : ℝ) + 1)) =
            ε * ((Fintype.card (Fin k) : ℝ) / ((Fintype.card (Fin k) : ℝ) + 1)) := by ring
        _ ≤ ε := by
          apply mul_le_of_le_one_right hε.le
          apply (div_le_one hden).2
          linarith
    exact hvec.trans (ENNReal.ofReal_le_ofReal hscale)
  have hXY : ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
      ∫⁻ ω, ENNReal.ofReal ‖XN N ω - Y j N ω‖ ∂disorderLaw ≤ ENNReal.ofReal ε := by
    intro ε hε
    let m : ℝ := Fintype.card (Fin k)
    let η : ℝ := ε / (2 * (m + 1))
    have hm : 0 ≤ m := by dsimp [m]; positivity
    have hη : 0 < η := by dsimp [η]; positivity
    have hrateEventually (i : Fin k) : ∀ᶠ j : ℕ in atTop,
        max (Cc i) 0 * |Real.log (δseq j i)| ^ (-(1 : ℝ) / 40) ≤ η := by
      have hpow0 : Tendsto (fun j : ℕ => |Real.log (δseq j i)| ^ (-(1 : ℝ) / 40))
          atTop (𝓝 0) := by
        simpa only [Function.comp_def] using tendsto_abs_log_inv40_lattice.comp (hδseqPosFilter i)
      have hpow := hpow0.const_mul (max (Cc i) 0)
      have hpow' : Tendsto (fun j : ℕ =>
          max (Cc i) 0 * |Real.log (δseq j i)| ^ (-(1 : ℝ) / 40))
          atTop (𝓝 0) := by
        simpa only [mul_zero] using hpow
      have hη' : ∀ᶠ j : ℕ in atTop,
          max (Cc i) 0 * |Real.log (δseq j i)| ^ (-(1 : ℝ) / 40) ≤ η :=
        hpow'.eventually (Iic_mem_nhds hη)
      exact hη'
    have hrateAll : ∀ᶠ j : ℕ in atTop, ∀ i ∈ Finset.univ,
        max (Cc i) 0 * |Real.log (δseq j i)| ^ (-(1 : ℝ) / 40) ≤ η := by
      rw [eventually_all_finset]
      intro i hi
      exact hrateEventually i
    filter_upwards [hrateAll] with j hj
    have hcoordN (i : Fin k) : ∀ᶠ N : ℕ in atTop,
        eLpNorm (fun ω => XN N ω i - Y j N ω i) 2 disorderLaw ≤ ENNReal.ofReal (2 * η) := by
      have hc := hC11Bound i (δseq j i) (hδseqpos j i) (hδseqC11 j i) η hη
      filter_upwards [hc] with N hN
      have hpowNonneg : 0 ≤ |Real.log (δseq j i)| ^ (-(1 : ℝ) / 40) :=
        Real.rpow_nonneg (abs_nonneg _) _
      have hcoef : Cc i * |Real.log (δseq j i)| ^ (-(1 : ℝ) / 40) ≤ η := by
        calc
          _ ≤ max (Cc i) 0 * |Real.log (δseq j i)| ^ (-(1 : ℝ) / 40) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hpowNonneg
          _ ≤ η := hj i (Finset.mem_univ i)
      have hboundReal : Cc i * |Real.log (δseq j i)| ^ (-(1 : ℝ) / 40) + η ≤ 2 * η := by
        linarith
      have hN' := hN.trans (ENNReal.ofReal_le_ofReal hboundReal)
      have hsplit (ω : Disorder) :
          (∫ x, φ i x * (kpzLatticeReversed ϑ N (t i) T (h₀ i) x ω -
            kpzLatticeReversedReg ϑ N (t i) T (δseq j i) (h₀ i) x ω)) =
          XN N ω i - Y j N ω i := by
        simpa [XN, Y, kpzLatticeReversed, kpzLatticeReversedReg] using
          (integral_latticePoint_sub_eq_lattice (φ := φ i) N
            (fun z : Site => Real.log (profileP2Fun (criticalBeta ϑ N)
              (evenCeil (N * (t i))) (evenCeil (N * T)) (fun w => if w = z then 1 else 0)
              (cellAverage N fun y => Real.exp (h₀ i y)) ω) -
                ∫ ω', Real.log (profileP2Fun (criticalBeta ϑ N)
                  (evenCeil (N * (t i))) (evenCeil (N * T))
                  (fun w => if w = z then 1 else 0) (fun _ => 1) ω') ∂disorderLaw)
            (fun z : Site => Real.log (profileP2Fun (criticalBeta ϑ N)
              (evenCeil (N * ((t i) + (δseq j i)))) (evenCeil (N * T))
              (fun w => srwKernel (evenCeil (δseq j i * N)) (w - z))
              (cellAverage N fun y => Real.exp (h₀ i y)) ω) -
                ∫ ω', Real.log (profileP2Fun (criticalBeta ϑ N)
                  (evenCeil (N * ((t i) + (δseq j i)))) (evenCeil (N * T))
                  (fun w => srwKernel (evenCeil (δseq j i * N)) (w - z))
                  (fun _ => 1) ω') ∂disorderLaw))
      have hfun : (fun ω : Disorder => XN N ω i - Y j N ω i) =
          fun ω => ∫ x, φ i x *
            (kpzLatticeReversed ϑ N (t i) T (h₀ i) x ω -
              kpzLatticeReversedReg ϑ N (t i) T (δseq j i) (h₀ i) x ω) := by
        funext ω
        exact (hsplit ω).symm
      rw [hfun]
      exact hN'
    have hallN : ∀ᶠ N : ℕ in atTop, ∀ i ∈ Finset.univ,
        eLpNorm (fun ω => XN N ω i - Y j N ω i) 2 disorderLaw ≤ ENNReal.ofReal (2 * η) := by
      rw [eventually_all_finset]
      intro i hi
      exact hcoordN i
    filter_upwards [hallN] with N hN
    have hvec := lintegral_norm_pi_sub_le_of_uniform_coordinate_eLpNorm k disorderLaw
      (XN N) (Y j N) (fun i => hN i (Finset.mem_univ i))
    have hscale : (Fintype.card (Fin k) : ℝ) * (2 * η) ≤ ε := by
      dsimp [m, η]
      have hm' : 0 ≤ (Fintype.card (Fin k) : ℝ) := by positivity
      have hden : 0 < (Fintype.card (Fin k) : ℝ) + 1 := by positivity
      have hfac : 2 * (ε / (2 * ((Fintype.card (Fin k) : ℝ) + 1))) =
          ε / ((Fintype.card (Fin k) : ℝ) + 1) := by
        field_simp
      rw [hfac]
      have hfrac := (div_le_one hden).2 (by linarith :
        (Fintype.card (Fin k) : ℝ) ≤ (Fintype.card (Fin k) : ℝ) + 1)
      calc
        (Fintype.card (Fin k) : ℝ) *
            (ε / ((Fintype.card (Fin k) : ℝ) + 1)) =
              ε * ((Fintype.card (Fin k) : ℝ) / ((Fintype.card (Fin k) : ℝ) + 1)) := by ring
        _ ≤ ε := mul_le_of_le_one_right hε.le hfrac
    exact hvec.trans (ENNReal.ofReal_le_ofReal hscale)
  have hXNmeas : ∀ N : ℕ, AEMeasurable (XN N) disorderLaw := by
    intro N
    have hm : Measurable (XN N) := by
      apply measurable_pi_iff.mpr
      intro i
      obtain ⟨S, hS⟩ := exists_finite_heatStartCells (fun _ : Fin 1 => φ i) N
      have hSites : ∀ x, φ i x ≠ 0 → latticePoint N x ∈ S := by
        intro x hx
        exact hS 0 x hx
      let G : Disorder → Site → ℝ := fun ω z =>
        Real.log (profileP2Fun (criticalBeta ϑ N) (evenCeil (N * t i))
          (evenCeil (N * T)) (fun w => if w = z then 1 else 0)
          (cellAverage N fun y => Real.exp (h₀ i y)) ω) -
        ∫ ω', Real.log (profileP2Fun (criticalBeta ϑ N) (evenCeil (N * t i))
          (evenCeil (N * T)) (fun w => if w = z then 1 else 0) (fun _ => 1) ω') ∂disorderLaw
      have hG (z : Site) : Measurable (fun ω => G ω z) := by
        dsimp [G]
        exact (Real.measurable_log.comp (Polymer.measurable_profileP2Fun
          (criticalBeta ϑ N) (evenCeil (N * t i)) (evenCeil (N * T))
          (fun w => if w = z then 1 else 0)
          (cellAverage N fun y => Real.exp (h₀ i y)))).sub measurable_const
      have hformula : (fun ω => XN N ω i) = fun ω =>
          ∑ z ∈ S, (∫ x in cell N z, φ i x) * G ω z := by
        funext ω
        have hp := integral_mul_latticePoint_piecewise (φ i).continuous
          (φ i).hasCompactSupport N (G ω) S hSites
        simpa [XN, G, kpzLatticeReversed] using hp
      rw [hformula]
      apply Finset.measurable_sum
      intro z hz
      exact measurable_const.mul (hG z)
    exact hm.aemeasurable
  have hLm : AEMeasurable L P := by
    apply aemeasurable_pi_iff.mpr
    intro i
    have hm : shfSigma Z ≤ (inferInstance : MeasurableSpace Ω) := by
      dsimp [shfSigma]
      apply iSup_le
      intro s
      apply iSup_le
      intro u
      apply iSup_le
      intro hsu
      exact (hZ.1 s u hsu.1 hsu.2).comap_le
    exact ((hXm (t i) (h₀ i) (φ i) (ht i).1 (ht i).2).mono hm le_rfl).aemeasurable
  exact tendstoInDistribution_of_approx XN Y Yl L hY hYlConverges hXY
    hXNmeas hLm

end Critical2DKPZ.JointConvergence

end
