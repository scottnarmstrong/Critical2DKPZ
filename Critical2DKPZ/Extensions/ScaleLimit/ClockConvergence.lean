/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.CovarianceAsymptotic
public import Critical2DKPZ.Extensions.ScaleLimit.WidthClock
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-! # Covariance convergence on the doubly logarithmic scale -/

public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction

namespace Critical2DKPZ.Extensions.ScaleLimit

variable (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P]
  (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
  (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
  (t : ℝ) (ht : 0 < t) (φ ψ : TestFn)
  (hφ : ∀ u, 0 ≤ φ u) (hψ : ∀ v, 0 ≤ ψ v)
  (hφmass : (∫ u, φ u) = 1) (hψmass : (∫ v, ψ v) = 1) (x : Plane)

include hZ hH ht hφ hψ hφmass hψmass

/-- Exchanging tests puts the larger width first, uniformly in both widths. -/
theorem covariance_max_width_error {η : ℝ} (hη : 0 < η) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ (a b : ℝ), 0 < a → 0 < b → max a b ≤ a₀ →
      |cov[fun ω => H t 0 ω (φ.dilate a x), fun ω => H t 0 ω (ψ.dilate b x); P] /
        Real.log (Real.log (max a b)⁻¹) - 1| ≤ η := by
  obtain ⟨a₁, ha₁, h₁⟩ := covariance_diagonal_asymptotic
    ϑ P Z hZ H hH t ht φ ψ hφ hψ hφmass hψmass x hη
  obtain ⟨a₂, ha₂, h₂⟩ := covariance_diagonal_asymptotic
    ϑ P Z hZ H hH t ht ψ φ hψ hφ hψmass hφmass x hη
  refine ⟨min a₁ a₂, lt_min ha₁ ha₂, ?_⟩
  intro a b ha hb hab
  rcases le_total b a with hba | hab'
  · rw [max_eq_left hba] at hab ⊢
    exact h₁ a ⟨ha, hab.trans (min_le_left _ _)⟩ b ⟨hb, hba⟩
  · rw [max_eq_right hab'] at hab ⊢
    rw [covariance_comm]
    exact h₂ b ⟨hb, hab.trans (min_le_right _ _)⟩ a ⟨ha, hab'⟩

/-- Proposition 5.1 for general positive widths in the ordinary logarithm domain. -/
theorem covariance_clock {a b : Set.Ioi (0 : ℝ) → ℝ} {s s' : ℝ}
    (ha : ∀ L, 0 < a L) (hb : ∀ L, 0 < b L)
    (haone : ∀ᶠ L in atTop, a L < 1) (hbone : ∀ᶠ L in atTop, b L < 1)
    (hs : 0 < s) (hs' : 0 < s')
    (hclocka : Tendsto (fun L : Set.Ioi (0 : ℝ) =>
      (L : ℝ)⁻¹ * Real.log (Real.log (a L)⁻¹)) atTop (𝓝 s))
    (hclockb : Tendsto (fun L : Set.Ioi (0 : ℝ) =>
      (L : ℝ)⁻¹ * Real.log (Real.log (b L)⁻¹)) atTop (𝓝 s')) :
    Tendsto (fun L : Set.Ioi (0 : ℝ) => (L : ℝ)⁻¹ *
      cov[fun ω => H t 0 ω (φ.dilate (a L) x), fun ω => H t 0 ω (ψ.dilate (b L) x); P])
      atTop (𝓝 (min s s')) := by
  let q : Set.Ioi (0 : ℝ) → ℝ := fun L => Real.log (Real.log (max (a L) (b L))⁻¹)
  let c : Set.Ioi (0 : ℝ) → ℝ := fun L =>
    cov[fun ω => H t 0 ω (φ.dilate (a L) x), fun ω => H t 0 ω (ψ.dilate (b L) x); P]
  have hwidtha := width_tendsto_zero_of_clock ha haone hs hclocka
  have hwidthb := width_tendsto_zero_of_clock hb hbone hs' hclockb
  have hwidth : Tendsto (fun L => max (a L) (b L)) atTop (𝓝 0) := by
    simpa only [max_self] using hwidtha.max hwidthb
  have hclock : Tendsto (fun L : Set.Ioi (0 : ℝ) => (L : ℝ)⁻¹ * q L)
      atTop (𝓝 (min s s')) := by
    apply (hclocka.min hclockb).congr'
    filter_upwards [haone, hbone] with L haL hbL
    dsimp only [q]
    rw [loglog_inv_max ⟨ha L, haL⟩ ⟨hb L, hbL⟩,
      mul_min_of_nonneg _ _ (inv_nonneg.mpr L.property.le)]
  have hratio : Tendsto (fun L => c L / q L) atTop (𝓝 1) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨a₀, ha₀, hbound⟩ := covariance_max_width_error
      ϑ P Z hZ H hH t ht φ ψ hφ hψ hφmass hψmass x (half_pos hε)
    filter_upwards [hwidth.eventually (Iio_mem_nhds ha₀)] with L hL
    exact (hbound (a L) (b L) (ha L) (hb L) hL.le).trans_lt (half_lt_self hε)
  have hproduct : Tendsto (fun L : Set.Ioi (0 : ℝ) =>
      ((L : ℝ)⁻¹ * q L) * (c L / q L)) atTop (𝓝 (min s s')) := by
    simpa only [mul_one] using hclock.mul hratio
  apply hproduct.congr'
  filter_upwards [hclock.eventually (Ioi_mem_nhds (lt_min hs hs'))] with L hL
  have hq : 0 < q L := (mul_pos_iff_of_pos_left (inv_pos.mpr L.property)).mp hL
  change ((L : ℝ)⁻¹ * q L) * (c L / q L) = (L : ℝ)⁻¹ * c L
  field_simp [hq.ne']

/-- The canonical covariance clock converges uniformly on every positive scale-time window. -/
theorem covariance_clock_uniform (s₀ S : ℝ) (hs₀ : 0 < s₀) :
    TendstoUniformlyOn (fun L : Set.Ioi (0 : ℝ) => fun p : ℝ × ℝ => (L : ℝ)⁻¹ *
      cov[fun ω => H t 0 ω (φ.dilate (scaleRadius L p.1) x),
        fun ω => H t 0 ω (ψ.dilate (scaleRadius L p.2) x); P])
      (fun p => min p.1 p.2) atTop (Set.Icc s₀ S ×ˢ Set.Icc s₀ S) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  let M : ℝ := |S| + 1
  have hM : 0 < M := add_pos_of_nonneg_of_pos (abs_nonneg S) zero_lt_one
  let η := ε / (2 * M)
  have hη : 0 < η := div_pos hε (mul_pos (by norm_num) hM)
  obtain ⟨a₀, ha₀, hb⟩ := covariance_max_width_error
    ϑ P Z hZ H hH t ht φ ψ hφ hψ hφmass hψmass x hη
  filter_upwards [(scaleRadius_tendsto_zero hs₀).eventually (Iio_mem_nhds ha₀)] with L hL
  intro p hp
  let m := min p.1 p.2
  have hm : 0 < m := lt_min (hs₀.trans_le hp.1.1) (hs₀.trans_le hp.2.1)
  have hmM : m ≤ M := (min_le_left _ _).trans
    (hp.1.2.trans ((le_abs_self S).trans (le_add_of_nonneg_right zero_le_one)))
  have hwidth : max (scaleRadius L p.1) (scaleRadius L p.2) ≤ a₀ := by
    apply max_le
    · exact ((scaleRadius_antitone L.property.le) hp.1.1).trans hL.le
    · exact ((scaleRadius_antitone L.property.le) hp.2.1).trans hL.le
  have herr := hb (scaleRadius L p.1) (scaleRadius L p.2)
    (scaleRadius_pos L p.1) (scaleRadius_pos L p.2) hwidth
  have hq : Real.log (Real.log (max (scaleRadius L p.1) (scaleRadius L p.2))⁻¹) =
      (L : ℝ) * m := by
    rw [loglog_inv_max ⟨scaleRadius_pos L p.1, scaleRadius_lt_one L p.1⟩
      ⟨scaleRadius_pos L p.2, scaleRadius_lt_one L p.2⟩,
      log_log_inv_scaleRadius, log_log_inv_scaleRadius,
      ← mul_min_of_nonneg _ _ L.property.le]
  rw [hq] at herr
  let c := cov[fun ω => H t 0 ω (φ.dilate (scaleRadius L p.1) x),
    fun ω => H t 0 ω (ψ.dilate (scaleRadius L p.2) x); P]
  have halg : (L : ℝ)⁻¹ * c - m = m * (c / ((L : ℝ) * m) - 1) := by
    field_simp [L.property.ne', hm.ne']
  have hdist : dist m ((L : ℝ)⁻¹ * c) ≤ M * η := by
    rw [Real.dist_eq, abs_sub_comm, halg, abs_mul, abs_of_pos hm]
    exact (mul_le_mul_of_nonneg_left herr hm.le).trans
      (mul_le_mul_of_nonneg_right hmM hη.le)
  have hhalf : M * η = ε / 2 := by dsimp [η]; field_simp
  exact hdist.trans_lt (hhalf.symm ▸ half_lt_self hε)

end Critical2DKPZ.Extensions.ScaleLimit
