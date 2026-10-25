/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CSZ25AtMostCritical
public import Critical2DKPZ.MomentBounds.CSZ25DampedSecondMoment
public import Critical2DKPZ.MomentBounds.CSZ25DampingChoice
public import Critical2DKPZ.MomentBounds.CSZ25Interpolation
public import Critical2DKPZ.MomentBounds.CSZ25SecondMoment
public import Critical2DKPZ.MomentBounds.CSZ25Variance
public import Critical2DKPZ.MomentBounds.CSZ25GreenDoubling
public import Critical2DKPZ.MomentBounds.CSZ25ReturnWeights
public import Critical2DKPZ.RandomWalk.ReplicaOverlap
import Mathlib.Tactic

/-! # Deterministic and low-moment lemmas for the CSZ25 moment assembly -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal

namespace Critical2DKPZ.MomentBounds

/-- The moment-bound hypothesis records CSZ25 Theorem 5.7's fixed-exponent estimate for terminal profile `1`, with centered integrability supplied by `integrable_centeredMoment_profileP2Fun`. -/
def CCRMomentBound (h : ℕ) : Prop :=
  ∀ t : ℝ, 0 < t → ∃ σ₀ K : ℝ, 0 < σ₀ ∧ 0 < K ∧ ∀ lam : ℝ, 0 ≤ lam → ∃ C : ℝ, 0 < C ∧
    ∀ β : ℝ, Polymer.sigmaSq β ≤ σ₀ → ∀ L : ℕ, t ^ 2 ≤ L →
    Polymer.sigmaSq β * dampedOverlap (lam / L) L < 1 → ∀ p q : ℝ, p.HolderConjugate q →
    p * q * (K * Polymer.sigmaSq β / (1 - Polymer.sigmaSq β * dampedOverlap (lam / L) L)) < 1 →
    ∀ (φ : Site → ℝ) (A : Finset Site), (∀ z, 0 ≤ φ z) → (∀ z ∉ A, φ z = 0) →
      |∫ ω, (profileP2Fun β 0 L φ (fun _ => 1) ω -
          ∫ ω', profileP2Fun β 0 L φ (fun _ => 1) ω' ∂disorderLaw) ^ h ∂disorderLaw| ≤
        C * (p * q * (K * Polymer.sigmaSq β / (1 - Polymer.sigmaSq β * dampedOverlap (lam / L) L))) ^
              ((h : ℝ) / 2) /
            (1 - p * q * (K * Polymer.sigmaSq β / (1 - Polymer.sigmaSq β * dampedOverlap (lam / L) L))) *
          (∑ z ∈ A, φ z * Real.exp (t * ‖siteToPlane z‖ / Real.sqrt L)) *
          finiteLpNorm A p (fun z => φ z * Real.exp (t * ‖siteToPlane z‖ / Real.sqrt L)) ^ (h - 1) *
          ((L : ℝ) / t ^ 2) ^ (((h : ℝ) - 1) / q)

/-- One damping rate bounds the disorder variance and damped overlap for all sufficiently large horizons. -/
theorem exists_dampingRate (θ M σ₀ : ℝ) (hσ₀ : 0 < σ₀) :
    ∃ (lam : ℝ) (L₀ : ℕ), 1 ≤ lam ∧ lam ≤ L₀ ∧ ∀ β : ℝ, ∀ L : ℕ, L₀ ≤ L →
      Polymer.sigmaSq β * (replicaOverlap L - θ) ≤ 1 →
        Polymer.sigmaSq β ≤ σ₀ ∧ Polymer.sigmaSq β * (dampedOverlap (lam / L) L + M) ≤ 1 := by
  obtain ⟨aLo, aHi, haLo, haLe, hreturn⟩ := srwKernel_two_mul_zero_bounds
  let lam : ℝ := 2 * Real.exp (2 / aLo * max (θ + M) 0)
  have hlam1 : 1 ≤ lam := by
    dsimp [lam]
    have hexp : 0 ≤ 2 / aLo * max (θ + M) 0 := by positivity
    have hone : 1 ≤ Real.exp (2 / aLo * max (θ + M) 0) :=
      Real.one_le_exp_iff.mpr hexp
    nlinarith
  have hlamLog : θ + M ≤ aLo / 2 * Real.log (lam / 2) := by
    have hratio : lam / 2 = Real.exp (2 / aLo * max (θ + M) 0) := by
      dsimp [lam]
      ring
    rw [hratio, Real.log_exp]
    have hmax : θ + M ≤ max (θ + M) 0 := le_max_left _ _
    have ha : aLo ≠ 0 := ne_of_gt haLo
    field_simp [ha]
    nlinarith
  obtain ⟨B, hB⟩ := Critical2DKPZ.replicaOverlap_log_bound
  have hlog : ∀ᶠ L : ℕ in atTop,
      Real.log (L : ℝ) > Real.pi * (θ + 1 / σ₀ + B) := by
    have htend : Tendsto (fun L : ℕ => Real.log (L : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact htend.eventually_gt_atTop _
  obtain ⟨Lg, hLg⟩ := (eventually_atTop.1 hlog)
  let L₀ := max Lg ⌈lam⌉₊
  refine ⟨lam, L₀, hlam1, ?_, ?_⟩
  · exact le_trans (Nat.le_ceil lam) (by exact_mod_cast (Nat.le_max_right Lg ⌈lam⌉₊))
  · intro β L hL hcrit
    have hLlarge : Lg ≤ L := le_trans (Nat.le_max_left _ _) hL
    have hlamL : lam ≤ (L : ℝ) := by
      have hceilL : (⌈lam⌉₊ : ℝ) ≤ L := by
        exact_mod_cast (le_trans (Nat.le_max_right Lg ⌈lam⌉₊) hL)
      exact (Nat.le_ceil lam).trans hceilL
    have hLpos : 1 ≤ L := by exact_mod_cast (le_trans hlam1 hlamL)
    have hlogL := hLg L hLlarge
    have hratio : θ + 1 / σ₀ + B < (1 / Real.pi) * Real.log (L : ℝ) := by
      rw [show (1 / Real.pi) * Real.log (L : ℝ) = Real.log (L : ℝ) / Real.pi by ring]
      apply (lt_div_iff₀ Real.pi_pos).2
      nlinarith [hlogL]
    have herror := hB L hLpos
    have hrep : θ + 1 / σ₀ ≤ replicaOverlap L := by
      have hlow := (abs_le.mp herror).1
      linarith
    have hrep' : 1 / σ₀ ≤ replicaOverlap L - θ := by linarith
    have hσ : 0 ≤ Polymer.sigmaSq β :=
      sub_nonneg.2 (Real.one_le_exp_iff.2 (sq_nonneg β))
    have hσmul : Polymer.sigmaSq β * (1 / σ₀) ≤ 1 := by
      calc
        _ ≤ Polymer.sigmaSq β * (replicaOverlap L - θ) :=
          mul_le_mul_of_nonneg_left hrep' hσ
        _ ≤ 1 := hcrit
    have hσbound : Polymer.sigmaSq β ≤ σ₀ := by
      calc
        Polymer.sigmaSq β = (Polymer.sigmaSq β * (1 / σ₀)) * σ₀ := by
          field_simp [ne_of_gt hσ₀]
        _ ≤ 1 * σ₀ := mul_le_mul_of_nonneg_right hσmul hσ₀.le
        _ = σ₀ := by ring
    have hdam := dampedOverlap_le_replicaOverlap_sub_log
      haLo.le (fun n hn => (hreturn n hn).1) hlam1 hlamL
    have hdam' : dampedOverlap (lam / L) L + M ≤ replicaOverlap L - θ := by
      linarith
    have hσdam : Polymer.sigmaSq β * (dampedOverlap (lam / L) L + M) ≤ 1 := by
      calc
        _ ≤ Polymer.sigmaSq β * (replicaOverlap L - θ) :=
          mul_le_mul_of_nonneg_left hdam' hσ
        _ ≤ 1 := hcrit
    exact ⟨hσbound, hσdam⟩

/-- Steps (b)–(c) of CSZ25 Lemma 5.6: choose `q` and the two uniform constants. -/
theorem exists_q_choice (η K c₂' c₃ aHi : ℝ) (hη : 0 < η) (hK : 0 < K)
    (hc₂ : 0 < c₂') (hc₃ : 0 < c₃) (haHi : 0 ≤ aHi) :
    ∃ C C' : ℝ, 0 < C ∧ 0 < C' ∧ ∀ Γ Rh RL V X : ℝ, 0 < Γ → Γ ≤ 1 / 16 → η ≤ Rh → Rh ≤ RL →
      RL ≤ Rh + aHi → Γ * Rh ≤ 2 * K * V → V ≤ c₃ → 0 < X → Real.log X ≤ c₂' * RL →
        ∃ q : ℝ, 4 ≤ q ∧ 2 * q * Γ ≤ 1 / 2 ∧ 2 * q * Γ ≤ C * V ∧ X ^ (1 / q) ≤ C' := by
  let a : ℝ := min (4 / η) (1 / (8 * K * c₃))
  let d : ℝ := a / (1 + aHi / η)
  let C : ℝ := 16 * K / η
  let C' : ℝ := Real.exp (c₂' / d)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hd : 0 < d := by
    dsimp [d]
    positivity
  refine ⟨C, C', ?_, Real.exp_pos _, ?_⟩
  · dsimp [C]
    positivity
  intro Γ Rh RL V X hΓ hΓ16 hηRh hRhRL hRL hΓV hVc hX hlogX
  have hRhpos : 0 < Rh := lt_of_lt_of_le hη hηRh
  have hq1 : 4 ≤ 4 * Rh / η := by
    rw [le_div_iff₀ hη]
    nlinarith
  have hq2 : 4 ≤ 1 / (4 * Γ) := by
    rw [le_div_iff₀ (by positivity : 0 < 4 * Γ)]
    nlinarith
  let q := min (4 * Rh / η) (1 / (4 * Γ))
  have hq4 : 4 ≤ q := by
    dsimp [q]
    exact le_min hq1 hq2
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num) hq4
  have hqGamma : 2 * q * Γ ≤ 1 / 2 := by
    have hqle : q ≤ 1 / (4 * Γ) := min_le_right _ _
    calc
      2 * q * Γ = (2 * Γ) * q := by ring
      _ ≤ (2 * Γ) * (1 / (4 * Γ)) := mul_le_mul_of_nonneg_left hqle (by positivity)
      _ = 1 / 2 := by field_simp; norm_num
  have hqV : 2 * q * Γ ≤ C * V := by
    have hqle : q ≤ 4 * Rh / η := min_le_left _ _
    have hfirst : 2 * q * Γ ≤ (8 / η) * (Γ * Rh) := by
      calc
        2 * q * Γ ≤ 2 * (4 * Rh / η) * Γ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hqle (by norm_num)) hΓ.le
        _ = (8 / η) * (Γ * Rh) := by ring
    have hsecond : (8 / η) * (Γ * Rh) ≤ C * V := by
      calc
        (8 / η) * (Γ * Rh) ≤ (8 / η) * (2 * K * V) :=
          mul_le_mul_of_nonneg_left hΓV (by positivity)
        _ = C * V := by dsimp [C]; ring
    exact hfirst.trans hsecond
  have hqLowerFirst : a * Rh ≤ 4 * Rh / η := by
    have ha_le : a ≤ 4 / η := min_le_left _ _
    calc
      a * Rh ≤ (4 / η) * Rh := mul_le_mul_of_nonneg_right ha_le hRhpos.le
      _ = 4 * Rh / η := by ring
  have hqLowerSecond : a * Rh ≤ 1 / (4 * Γ) := by
    have hΓRh : Γ * Rh ≤ 2 * K * c₃ := by
      calc
        Γ * Rh ≤ 2 * K * V := hΓV
        _ ≤ 2 * K * c₃ := mul_le_mul_of_nonneg_left hVc (by positivity)
    have ha_le : a ≤ 1 / (8 * K * c₃) := min_le_right _ _
    have hcompare : Rh / (8 * K * c₃) ≤ 1 / (4 * Γ) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    calc
      a * Rh ≤ (1 / (8 * K * c₃)) * Rh := mul_le_mul_of_nonneg_right ha_le hRhpos.le
      _ = Rh / (8 * K * c₃) := by ring
      _ ≤ 1 / (4 * Γ) := hcompare
  have hqRh : a * Rh ≤ q := by
    dsimp [q]
    exact le_min hqLowerFirst hqLowerSecond
  have hfac : RL ≤ Rh * (1 + aHi / η) := by
    calc
      RL ≤ Rh + aHi := hRL
      _ ≤ Rh * (1 + aHi / η) := by
        have hratio : 1 ≤ Rh / η := (one_le_div hη).2 hηRh
        have hηRh' : aHi ≤ Rh * (aHi / η) := by
          calc
            aHi = 1 * aHi := by ring
            _ ≤ (Rh / η) * aHi := mul_le_mul_of_nonneg_right hratio haHi
            _ = Rh * (aHi / η) := by ring
        calc
          Rh + aHi ≤ Rh + Rh * (aHi / η) := add_le_add le_rfl hηRh'
          _ = Rh * (1 + aHi / η) := by ring
  have hqRL : d * RL ≤ q := by
    calc
      d * RL ≤ d * (Rh * (1 + aHi / η)) := mul_le_mul_of_nonneg_left hfac hd.le
      _ = a * Rh := by dsimp [d]; field_simp
      _ ≤ q := hqRh
  have hRLq : RL / q ≤ 1 / d := by
    rw [div_le_div_iff₀ hqpos hd]
    simpa only [one_mul, mul_comm] using hqRL
  have hlogq : Real.log X / q ≤ c₂' / d := by
    calc
      Real.log X / q ≤ c₂' * RL / q := div_le_div_of_nonneg_right hlogX hqpos.le
      _ = c₂' * (RL / q) := by ring
      _ ≤ c₂' * (1 / d) := mul_le_mul_of_nonneg_left hRLq hc₂.le
      _ = c₂' / d := by ring
  refine ⟨q, hq4, hqGamma, hqV, ?_⟩
  rw [Real.rpow_def_of_pos hX]
  apply Real.exp_le_exp.mpr
  calc
    Real.log X * (1 / q) = Real.log X / q := by ring
    _ ≤ c₂' / d := hlogq

/-- The centered-moment comparison for the exponents `h ≤ 2`. The profile is integrable by
`Polymer.memLp_profile_probability`, and the centered powers by
`integrable_centeredMoment_profileP2Fun`. -/
theorem abs_centeredMoment_le_variance_pow_of_le_two {h : ℕ} (hh : h ≤ 2) (β : ℝ) (L : ℕ)
    (φ : Site → ℝ) (hφ : ∀ z, 0 ≤ φ z) (hφ1 : HasSum φ 1) :
    |∫ ω, (profileP2Fun β 0 L φ (fun _ => 1) ω -
        ∫ ω', profileP2Fun β 0 L φ (fun _ => 1) ω' ∂disorderLaw) ^ h ∂disorderLaw| ≤
      Var[fun ω => profileP2Fun β 0 L φ (fun _ => 1) ω; disorderLaw] ^ ((h : ℝ) / 2) := by
  have hmean : (∫ ω, profileP2Fun β 0 L φ (fun _ => 1) ω ∂disorderLaw) = 1 :=
    Polymer.integral_profile_flat_probability β 0 L φ hφ hφ1.tsum_eq
  have hmem : MemLp (profileP2Fun β 0 L φ (fun _ => 1)) 1 disorderLaw :=
    Polymer.memLp_profile_probability β 0 L φ (fun _ => 1) hφ hφ1.tsum_eq
      1 (by norm_num) (by intro z; norm_num) 1 (by simp)
  have hvariance : 0 ≤ Var[fun ω => profileP2Fun β 0 L φ (fun _ => 1) ω; disorderLaw] :=
    variance_nonneg _ _
  interval_cases h
  · simp [integral_const]
  · have hcenter :
        (∫ ω, (profileP2Fun β 0 L φ (fun _ => 1) ω -
          ∫ ω', profileP2Fun β 0 L φ (fun _ => 1) ω' ∂disorderLaw) ∂disorderLaw) = 0 := by
      rw [hmean]
      rw [integral_sub (hmem.integrable (by norm_num)) (integrable_const 1)]
      simp [hmean]
    have hmoment : (∫ ω, (profileP2Fun β 0 L φ (fun _ => 1) ω -
        ∫ ω', profileP2Fun β 0 L φ (fun _ => 1) ω' ∂disorderLaw) ^ (1 : ℕ)
          ∂disorderLaw) = 0 := by simpa only [pow_one] using hcenter
    rw [hmoment]
    simp only [abs_zero]
    exact Real.rpow_nonneg hvariance _
  · have hsecond := profileP2Fun_abs_sq_eq_variance β L φ hφ hφ1
    have hnonneg : 0 ≤ ∫ ω,
        (profileP2Fun β 0 L φ (fun _ => 1) ω -
          ∫ ω', profileP2Fun β 0 L φ (fun _ => 1) ω' ∂disorderLaw) ^ 2 ∂disorderLaw :=
      integral_nonneg (fun ω => sq_nonneg _)
    have hintegral :
        (∫ ω,
          (profileP2Fun β 0 L φ (fun _ => 1) ω -
            ∫ ω', profileP2Fun β 0 L φ (fun _ => 1) ω' ∂disorderLaw) ^ 2 ∂disorderLaw) =
          ∫ ω,
            |profileP2Fun β 0 L φ (fun _ => 1) ω -
              ∫ ω', profileP2Fun β 0 L φ (fun _ => 1) ω' ∂disorderLaw| ^ 2 ∂disorderLaw := by
      apply integral_congr_ae
      filter_upwards [] with ω
      exact (sq_abs _).symm
    rw [abs_of_nonneg hnonneg, hintegral, hsecond]
    rw [show ((2 : ℕ) : ℝ) / 2 = 1 by norm_num, Real.rpow_one]

/-- The sites of sup-norm at most `n`. -/
def boxSites (n : ℕ) : Finset Site :=
  Fintype.piFinset fun _ : Fin 2 => Finset.Icc (-(n : ℤ)) n

/-- The sets `boxSites n` increase with `n`. -/
theorem boxSites_mono {m n : ℕ} (hmn : m ≤ n) : boxSites m ⊆ boxSites n := by
  intro z hz
  simp only [boxSites, Fintype.mem_piFinset, Finset.mem_Icc] at hz ⊢
  have hmnZ : (m : ℤ) ≤ n := by exact_mod_cast hmn
  intro i
  constructor
  · exact (neg_le_neg hmnZ).trans (hz i).1
  · exact (hz i).2.trans hmnZ

/-- Every finite set of sites lies in some `boxSites n`. -/
theorem exists_boxSites_superset (A : Finset Site) :
    ∃ n, A ⊆ boxSites n := by
  let bound (z : Site) := max (z 0).natAbs (z 1).natAbs
  let n := A.sup bound
  refine ⟨n, ?_⟩
  intro z hz
  simp only [boxSites, Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  have hbound : bound z ≤ n := Finset.le_sup hz
  have hcoord : (z i).natAbs ≤ n := by
    fin_cases i
    · exact (Nat.le_max_left _ _).trans hbound
    · exact (Nat.le_max_right _ _).trans hbound
  have hcoord' : ((z i).natAbs : ℤ) ≤ (n : ℤ) := by exact_mod_cast hcoord
  have habs : |z i| ≤ (n : ℤ) := by simpa only [Int.natCast_natAbs] using hcoord'
  exact abs_le.mp habs

/-- The sets `boxSites n` exhaust the lattice: they tend to `atTop` along `n → ∞`. -/
theorem tendsto_boxSites_atTop : Tendsto boxSites atTop atTop := by
  refine tendsto_atTop.2 fun A => ?_
  obtain ⟨n, hn⟩ := exists_boxSites_superset A
  filter_upwards [eventually_ge_atTop n] with m hm
  exact hn.trans (boxSites_mono hm)

/-- Truncating the start profile to `boxSites n` converges in every centred moment and in the variance. -/
theorem tendsto_centeredMoment_profileP2Fun_truncate (β : ℝ) (L h : ℕ) (φ : Site → ℝ)
    (hφ : ∀ z, 0 ≤ φ z) (hsum : Summable φ) :
    Tendsto (fun n : ℕ =>
        ∫ ω, (profileP2Fun β 0 L ((↑(boxSites n) : Set Site).indicator φ) (fun _ => 1) ω -
          ∫ ω', profileP2Fun β 0 L ((↑(boxSites n) : Set Site).indicator φ) (fun _ => 1) ω'
            ∂disorderLaw) ^ h ∂disorderLaw) atTop
      (𝓝 (∫ ω, (profileP2Fun β 0 L φ (fun _ => 1) ω -
        ∫ ω', profileP2Fun β 0 L φ (fun _ => 1) ω' ∂disorderLaw) ^ h ∂disorderLaw)) ∧
    Tendsto (fun n : ℕ =>
        Var[fun ω => profileP2Fun β 0 L ((↑(boxSites n) : Set Site).indicator φ) (fun _ => 1) ω;
          disorderLaw]) atTop
      (𝓝 (Var[fun ω => profileP2Fun β 0 L φ (fun _ => 1) ω; disorderLaw])) := by
  classical
  let F : Disorder → ℝ := profileP2Fun β 0 L φ (fun _ => 1)
  let φn (n : ℕ) : Site → ℝ := (↑(boxSites n) : Set Site).indicator φ
  let Fn (n : ℕ) : Disorder → ℝ := profileP2Fun β 0 L (φn n) (fun _ => 1)
  let mass : ℝ := ∑' z, φ z
  let massn (n : ℕ) : ℝ := ∑ z ∈ boxSites n, φ z
  have hφabs : Summable (fun z => |φ z|) := by
    simpa only [abs_of_nonneg (hφ _)] using hsum
  have hbox := tendsto_boxSites_atTop
  have hmass : Tendsto massn atTop (𝓝 mass) := by
    have ht : Tendsto (fun A : Finset Site => ∑ z ∈ A, φ z) atTop (𝓝 mass) := by
      have hs := hsum.hasSum
      change Tendsto (fun A : Finset Site => ∑ z ∈ A, φ z) atTop
        (𝓝 (∑' z, φ z)) at hs
      simpa only [mass] using hs
    change Tendsto (fun n : ℕ => ∑ z ∈ boxSites n, φ z) atTop (𝓝 mass)
    have hseq : (fun n : ℕ => ∑ z ∈ boxSites n, φ z) =
        (fun A : Finset Site => ∑ z ∈ A, φ z) ∘ boxSites := by
      funext n
      rfl
    rw [hseq]
    exact ht.comp hbox
  have hFn_sum (n : ℕ) (ω : Disorder) :
      Fn n ω = ∑ z ∈ boxSites n, φ z * pointToPlane β 0 L z ω := by
    have hsupp : ∀ z ∉ boxSites n, φn n z = 0 := by
      intro z hz
      simp [φn, hz]
    rw [show Fn n = profileP2Fun β 0 L (φn n) (fun _ => 1) by rfl,
      Polymer.profileP2Fun_eq_sum β 0 L (φn n) (fun _ => 1) (boxSites n) hsupp ω]
    simp only [Nat.sub_zero, mul_one, Polymer.tsum_pointToPoint]
    apply Finset.sum_congr rfl
    intro z hz
    rw [show φn n z = φ z by
      dsimp [φn]
      exact Set.indicator_of_mem (Finset.mem_coe.mpr hz) φ]
  have hF_series (ω : Disorder) :
      F ω = ∑' z, φ z * pointToPlane β 0 L z ω := by
    simp only [F, profileP2Fun]
    simp_rw [Nat.sub_zero, mul_one, Polymer.tsum_pointToPoint]
  have hmassFn (n : ℕ) : (∫ ω, Fn n ω ∂disorderLaw) = massn n := by
    rw [show Fn n = profileP2Fun β 0 L (φn n) (fun _ => 1) by rfl,
      Polymer.integral_profileP2Fun_finset β 0 L (φn n) (fun _ => 1) (boxSites n) (by
        intro z hz
        simp [φn, hz])]
    simp only [Nat.sub_zero, mul_one, Polymer.tsum_srwKernel]
    simp only [massn]
    apply Finset.sum_congr rfl
    intro z hz
    rw [show φn n z = φ z by
      dsimp [φn]
      exact Set.indicator_of_mem (Finset.mem_coe.mpr hz) φ]
  have hmassF : (∫ ω, F ω ∂disorderLaw) = mass := by
    rw [show F = profileP2Fun β 0 L φ (fun _ => 1) by rfl,
      Polymer.integral_profileP2Fun_summable β 0 L φ (fun _ => 1) hφabs 1 (by norm_num)
        (by intro z; norm_num)]
    simp only [Nat.sub_zero, mul_one, Polymer.tsum_srwKernel, mass]
  have htermnorm :
      (∑' z : Site, eLpNorm (fun ω => φ z * pointToPlane β 0 L z ω)
        (1 : ℝ≥0∞) disorderLaw) ≠ ⊤ := by
    simpa only [Nat.sub_zero, mul_one, Polymer.tsum_pointToPoint] using
      Polymer.profile_term_norms_ne_top β 0 L φ (fun _ => 1) hφabs 1 (by norm_num)
        (by intro z; norm_num) 1 (by simp)
  have hterms_ae : ∀ᵐ ω ∂disorderLaw, Summable (fun z => ‖φ z * pointToPlane β 0 L z ω‖) :=
    MeasureTheory.summable_norm_of_tsum_eLpNorm_ne_top (p := 1) (by norm_num) htermnorm
  have hpointwise : ∀ᵐ ω ∂disorderLaw,
      Tendsto (fun n => Fn n ω) atTop (𝓝 (F ω)) := by
    filter_upwards [hterms_ae] with ω hω
    have hs := hω.of_norm.hasSum
    change Tendsto (fun A : Finset Site =>
        ∑ z ∈ A, φ z * pointToPlane β 0 L z ω) atTop
        (𝓝 (∑' z, φ z * pointToPlane β 0 L z ω)) at hs
    have ht := hs
    have htc := ht.comp hbox
    have hseq : (fun n : ℕ => Fn n ω) =
        (fun A : Finset Site => ∑ z ∈ A, φ z * pointToPlane β 0 L z ω) ∘ boxSites := by
      funext n
      rw [hFn_sum]
      rfl
    rw [hseq, hF_series]
    exact htc
  have hFn_nonneg (n : ℕ) (ω : Disorder) : 0 ≤ Fn n ω := by
    rw [hFn_sum]
    apply Finset.sum_nonneg
    intro z _
    exact mul_nonneg (hφ z) (Polymer.pointToPlane_pos β 0 L z ω).le
  have hF_nonneg (ω : Disorder) : 0 ≤ F ω := by
    rw [hF_series]
    exact tsum_nonneg fun z => mul_nonneg (hφ z) (Polymer.pointToPlane_pos β 0 L z ω).le
  have hFn_le_F : ∀ n, ∀ᵐ ω ∂disorderLaw, Fn n ω ≤ F ω := by
    intro n
    filter_upwards [hterms_ae] with ω hω
    rw [hFn_sum, hF_series]
    exact hω.of_norm.sum_le_tsum (boxSites n) (fun z _ =>
      mul_nonneg (hφ z) (Polymer.pointToPlane_pos β 0 L z ω).le)
  have hmean_nonneg : 0 ≤ mass := tsum_nonneg hφ
  have hmassn_nonneg (n : ℕ) : 0 ≤ massn n :=
    Finset.sum_nonneg fun z _ => hφ z
  have hmassn_le_mass (n : ℕ) : massn n ≤ mass := by
    change (∑ z ∈ boxSites n, φ z) ≤ ∑' z, φ z
    exact hsum.sum_le_tsum (boxSites n) (fun z _ => hφ z)
  have hF_memLp (p : ℝ≥0∞) (hp : p ≠ ∞) : MemLp F p disorderLaw := by
    rw [show F = profileP2Fun β 0 L φ (fun _ => 1) by rfl]
    exact Polymer.memLp_profileP2Fun_summable β 0 L φ (fun _ => 1) hφabs 1
      (by norm_num) (by intro z; norm_num) p hp
  have hmoment (k : ℕ) (hk : 1 ≤ k) :
      Tendsto (fun n => ∫ ω, (Fn n ω - massn n) ^ k ∂disorderLaw) atTop
        (𝓝 (∫ ω, (F ω - mass) ^ k ∂disorderLaw)) := by
    let p : ℝ≥0∞ := k
    have hp1 : 1 ≤ p := by dsimp [p]; exact_mod_cast hk
    have hpne : p ≠ ∞ := by simp [p]
    have hboundMem : MemLp (fun ω => F ω + mass) p disorderLaw :=
      (hF_memLp p hpne).add (memLp_const mass)
    have hboundInt : Integrable (fun ω => (F ω + mass) ^ k) disorderLaw := by
      simpa only [Real.norm_of_nonneg (add_nonneg (hF_nonneg _) hmean_nonneg)] using
        hboundMem.integrable_norm_pow (by omega)
    have hFnmeas (n : ℕ) : AEStronglyMeasurable (fun ω => (Fn n ω - massn n) ^ k) disorderLaw := by
      have hm : Measurable (Fn n) := by
        dsimp [Fn]
        exact Polymer.measurable_profileP2Fun β 0 L (φn n) (fun _ => 1)
      exact ((hm.sub_const _).pow_const k).aestronglyMeasurable
    apply tendsto_integral_of_dominated_convergence (fun ω => (F ω + mass) ^ k)
    · exact hFnmeas
    · exact hboundInt
    · intro n
      filter_upwards [hFn_le_F n] with ω hω
      have hdiff : |Fn n ω - massn n| ≤ F ω + mass := by
        rw [abs_le]
        constructor <;> linarith [hFn_nonneg n ω, hFn_le_F n, hmassn_nonneg n,
          hmassn_le_mass n, hF_nonneg ω, hmean_nonneg]
      calc
        ‖(Fn n ω - massn n) ^ k‖ = |Fn n ω - massn n| ^ k := by rw [Real.norm_eq_abs, abs_pow]
        _ ≤ (F ω + mass) ^ k := by
          exact pow_le_pow_left₀ (abs_nonneg _) hdiff k
    · filter_upwards [hpointwise] with ω hω
      have hmω : Tendsto (fun n => massn n) atTop (𝓝 mass) := hmass
      have hs := hω.sub hmω
      exact hs.pow k
  have hmoment0 : Tendsto (fun n => ∫ ω, (Fn n ω - massn n) ^ 0 ∂disorderLaw) atTop
      (𝓝 (∫ ω, (F ω - mass) ^ 0 ∂disorderLaw)) := by
    simp only [pow_zero, integral_const, probReal_univ]
    exact tendsto_const_nhds
  have hmoment_h : Tendsto (fun n => ∫ ω, (Fn n ω - massn n) ^ h ∂disorderLaw) atTop
      (𝓝 (∫ ω, (F ω - mass) ^ h ∂disorderLaw)) := by
    by_cases hh0 : h = 0
    · simp [hh0]
    · exact hmoment h (Nat.one_le_iff_ne_zero.mpr hh0)
  have hvar : Tendsto (fun n => Var[Fn n; disorderLaw]) atTop
      (𝓝 (Var[F; disorderLaw])) := by
    have hmom2 := hmoment 2 (by norm_num)
    have hvarn (n : ℕ) : Var[Fn n; disorderLaw] = ∫ ω, (Fn n ω - massn n) ^ 2 ∂disorderLaw := by
      rw [variance_eq_integral]
      · rw [hmassFn]
      · exact (Polymer.measurable_profileP2Fun β 0 L (φn n) (fun _ => 1)).aemeasurable
    have hvarF : Var[F; disorderLaw] = ∫ ω, (F ω - mass) ^ 2 ∂disorderLaw := by
      rw [variance_eq_integral]
      · rw [hmassF]
      · exact (Polymer.measurable_profileP2Fun β 0 L φ (fun _ => 1)).aemeasurable
    simpa only [hvarn, hvarF] using hmom2
  constructor
  · simpa only [F, Fn, φn, hmassFn, hmassF] using hmoment_h
  · simpa only [F, Fn, φn] using hvar

private theorem centeredMoment_translate_finiteSupport {h : ℕ} (β : ℝ) (L : ℕ)
    (φ : Site → ℝ) (A : Finset Site) (hφA : ∀ z ∉ A, φ z = 0)
    (hmass : ∑ z ∈ A, φ z = 1) (z₀ : Site) :
    (∫ ω, (profileP2Fun β 0 L φ (fun _ => 1) ω -
        ∫ ω', profileP2Fun β 0 L φ (fun _ => 1) ω' ∂disorderLaw) ^ h ∂disorderLaw) =
      ∫ ω, (profileP2Fun β 0 L (fun z => φ (z + z₀)) (fun _ => 1) ω -
        ∫ ω', profileP2Fun β 0 L (fun z => φ (z + z₀)) (fun _ => 1) ω'
          ∂disorderLaw) ^ h ∂disorderLaw := by
  classical
  let A' := A.image (fun z => z - z₀)
  let τ : Disorder → Disorder := fun ω p => ω (p.1, p.2 + z₀)
  let τeq : Disorder ≃ᵐ Disorder :=
    MeasurableEquiv.piCongrLeft (fun _ : ℕ × Site => ℝ)
      (Gaussian.spatialTranslation z₀).symm
  have hτeq : τ = τeq := by
    funext ω p
    simp [τ, τeq, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
      Gaussian.spatialTranslation]
  have hτmeas : MeasurableEmbedding τ := hτeq ▸ τeq.measurableEmbedding
  have hinj : Set.InjOn (fun z : Site => z - z₀) A := by
    intro z hz w hw hzw
    have := congrArg (fun x : Site => x + z₀) hzw
    simpa using this
  have hφ'A : ∀ z ∉ A', φ (z + z₀) = 0 := by
    intro z hz
    apply hφA
    intro hmem
    apply hz
    exact Finset.mem_image.mpr ⟨z + z₀, hmem, by simp⟩
  have hmass' : ∑ z ∈ A', φ (z + z₀) = 1 := by
    change ∑ z ∈ A.image (fun z => z - z₀), φ (z + z₀) = 1
    rw [Finset.sum_image hinj]
    simpa using hmass
  have hprofile (ω : Disorder) :
      profileP2Fun β 0 L φ (fun _ => 1) ω =
        profileP2Fun β 0 L (fun z => φ (z + z₀)) (fun _ => 1) (τ ω) := by
    rw [Polymer.profileP2Fun_eq_sum β 0 L φ (fun _ => 1) A hφA ω,
      Polymer.profileP2Fun_eq_sum β 0 L (fun z => φ (z + z₀)) (fun _ => 1) A' hφ'A (τ ω)]
    simp only [Nat.sub_zero, mul_one, Polymer.tsum_pointToPoint]
    calc
      ∑ z ∈ A, φ z * pointToPlane β 0 L z ω =
          ∑ z ∈ A, φ ((z - z₀) + z₀) * pointToPlane β 0 L (z - z₀) (τ ω) := by
        apply Finset.sum_congr rfl
        intro z hz
        have hφz : φ ((z - z₀) + z₀) = φ z := by congr 1; abel
        have hPz : pointToPlane β 0 L (z - z₀) (τ ω) = pointToPlane β 0 L z ω := by
          have hp := Polymer.pointToPlane_translate β 0 L (z - z₀) z₀ ω
          simpa only [sub_add_cancel] using hp.symm
        rw [hφz, hPz]
      _ = ∑ z ∈ A', φ (z + z₀) * pointToPlane β 0 L z (τ ω) :=
        (Finset.sum_image (s := A) (g := fun z : Site => z - z₀)
          (f := fun z => φ (z + z₀) * pointToPlane β 0 L z (τ ω)) hinj).symm
  have hmean (ψ : Site → ℝ) (B : Finset Site) (hsupp : ∀ z ∉ B, ψ z = 0)
      (hm : ∑ z ∈ B, ψ z = 1) :
      (∫ ω, profileP2Fun β 0 L ψ (fun _ => 1) ω ∂disorderLaw) = 1 := by
    rw [Polymer.integral_profileP2Fun_finset β 0 L ψ (fun _ => 1) B hsupp]
    calc
      ∑ z ∈ B, ψ z * ∑' w, srwKernel L (w - z) * 1 = ∑ z ∈ B, ψ z := by
        apply Finset.sum_congr rfl
        intro z hz
        simp [Polymer.tsum_srwKernel]
      _ = 1 := hm
  have hmeanφ :
      (∫ ω, profileP2Fun β 0 L φ (fun _ => 1) ω ∂disorderLaw) = 1 :=
    hmean φ A hφA hmass
  have hmeanψ :
      (∫ ω, profileP2Fun β 0 L (fun z => φ (z + z₀)) (fun _ => 1) ω ∂disorderLaw) = 1 :=
    hmean _ A' hφ'A hmass'
  have hMP := Gaussian.measurePreserving_disorder_translation z₀
  calc
    _ = ∫ ω, (profileP2Fun β 0 L (fun z => φ (z + z₀)) (fun _ => 1) (τ ω) - 1) ^ h
        ∂disorderLaw := by
      apply integral_congr_ae
      filter_upwards [] with ω
      have heq := congrArg (fun x : ℝ => (x - 1) ^ h) (hprofile ω)
      simpa only [hmeanφ, hmeanψ] using heq
    _ = _ := by
      calc
        _ = ∫ ω, (profileP2Fun β 0 L (fun z => φ (z + z₀)) (fun _ => 1) ω - 1) ^ h
            ∂disorderLaw := hMP.integral_comp hτmeas
              (fun ω => (profileP2Fun β 0 L (fun z => φ (z + z₀)) (fun _ => 1) ω - 1) ^ h)
        _ = ∫ ω, (profileP2Fun β 0 L (fun z => φ (z + z₀)) (fun _ => 1) ω -
            ∫ ω', profileP2Fun β 0 L (fun z => φ (z + z₀)) (fun _ => 1) ω'
              ∂disorderLaw) ^ h ∂disorderLaw := by rw [hmeanψ]

private theorem finiteLpNorm_weightedProfile_bound
    (t : ℝ) (ht : 0 < t) (L : ℕ) (htL : t ^ 2 ≤ L) (q : ℝ) (hq : 4 ≤ q)
    (φ : Site → ℝ) (A : Finset Site) (hφ : ∀ z, 0 ≤ φ z)
    (hmass : ∑ z ∈ A, φ z = 1) (z₀ : Site) :
    finiteLpNorm A (q / (q - 1))
        (fun z => φ z * Real.exp (t * ‖siteToPlane (z - z₀)‖ / Real.sqrt L)) ≤
      (∑ z ∈ A, φ z * Real.exp (2 * t * ‖siteToPlane (z - z₀)‖ / Real.sqrt L)) ^
          (1 - 2 / q) *
        (∑ z ∈ A, φ z ^ 2) ^ (1 / q) := by
  let p : ℝ := q / (q - 1)
  let r : ℝ := q / (q - 2)
  let w : Site → ℝ := fun z => Real.exp (t * ‖siteToPlane (z - z₀)‖ / Real.sqrt L)
  let w2 : Site → ℝ := fun z => Real.exp (2 * t * ‖siteToPlane (z - z₀)‖ / Real.sqrt L)
  let N : ℝ := ∑ z ∈ A, φ z ^ 2
  let S : ℝ := ∑ z ∈ A, φ z * w2 z
  have hq1 : 0 < q := by linarith
  have hq2 : 2 < q := by linarith
  have hp1 : 1 < p := by
    dsimp [p]
    rw [lt_div_iff₀ (by linarith only [hq] : 0 < q - 1)]
    linarith only
  have hpq : p.HolderConjugate q := by
    rw [Real.holderConjugate_iff]
    constructor
    · exact hp1
    · dsimp [p]
      field_simp
      ring
  have hWnonneg : ∀ z, 0 ≤ w z := fun z => Real.exp_nonneg _
  have hWone : ∀ z, 1 ≤ w z := by
    intro z
    apply Real.one_le_exp_iff.mpr
    positivity
  have hr_le : r ≤ 2 := by
    dsimp [r]
    rw [div_le_iff₀ (by linarith only [hq] : 0 < q - 2)]
    linarith only [hq]
  have hwr : ∀ z, w z ^ r ≤ w z ^ (2 : ℝ) := fun z =>
    Real.rpow_le_rpow_of_exponent_le (hWone z) hr_le
  have hw2 : ∀ z, w z ^ (2 : ℝ) = w2 z := by
    intro z
    change Real.exp (t * ‖siteToPlane (z - z₀)‖ / Real.sqrt L) ^ (2 : ℝ) =
      Real.exp (2 * t * ‖siteToPlane (z - z₀)‖ / Real.sqrt L)
    rw [← Real.exp_mul]
    congr 1
    ring
  have hNnonneg : 0 ≤ N := by
    dsimp [N]
    exact Finset.sum_nonneg fun z hz => sq_nonneg (φ z)
  have hSnonneg : 0 ≤ S := by
    dsimp [S]
    apply Finset.sum_nonneg
    intro z hz
    exact mul_nonneg (hφ z) (Real.exp_nonneg _)
  have hSone : 1 ≤ S := by
    dsimp [S, w2]
    calc
      1 = ∑ z ∈ A, φ z := hmass.symm
      _ ≤ ∑ z ∈ A, φ z * Real.exp (2 * t * ‖siteToPlane (z - z₀)‖ / Real.sqrt L) := by
        apply Finset.sum_le_sum
        intro z hz
        have he : 1 ≤ Real.exp (2 * t * ‖siteToPlane (z - z₀)‖ / Real.sqrt L) := by
          apply Real.one_le_exp_iff.mpr
          have htden : 0 < Real.sqrt L :=
            Real.sqrt_pos.2 (lt_of_lt_of_le (sq_pos_of_pos ht) htL)
          positivity
        simpa using mul_le_mul_of_nonneg_left he (hφ z)
  have hsumPow : (∑ z ∈ A, |φ z| * w z ^ r) ≤ S := by
    calc
      _ ≤ ∑ z ∈ A, φ z * w z ^ (2 : ℝ) := by
        apply Finset.sum_le_sum
        intro z hz
        rw [abs_of_nonneg (hφ z)]
        exact mul_le_mul_of_nonneg_left (hwr z) (hφ z)
      _ = S := by simp [S, hw2]
  have hinterp := finiteLpNorm_mul_le_interpolation A hpq hq2 φ w
    (fun z => hWnonneg z)
  have hnorm2 : finiteLpNorm A 2 φ = N ^ (1 / 2 : ℝ) := by
    simp [finiteLpNorm, N, abs_of_nonneg (hφ _)]
  have hnormBound : finiteLpNorm A p (fun z => φ z * w z) ≤
      S ^ (1 - 2 / q) * N ^ (1 / q) := by
    calc
      _ ≤ (∑ z ∈ A, |φ z| * w z ^ r) ^ (1 - 2 / q) *
          finiteLpNorm A 2 φ ^ (2 / q) := hinterp
      _ ≤ S ^ (1 - 2 / q) * N ^ (1 / q) := by
        have hfirst : (∑ z ∈ A, |φ z| * w z ^ r) ^ (1 - 2 / q) ≤
            S ^ (1 - 2 / q) :=
          Real.rpow_le_rpow
            (Finset.sum_nonneg fun z hz =>
              mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (hWnonneg z) _))
            hsumPow (by
              have hq4 : 2 / q ≤ 1 := (div_le_one hq1).2 (by linarith)
              linarith)
        have hexp : (N ^ (1 / 2 : ℝ)) ^ (2 / q) = N ^ (1 / q) := by
          rw [← Real.rpow_mul hNnonneg]
          congr 1
          ring
        rw [hnorm2, hexp]
        exact mul_le_mul hfirst le_rfl (Real.rpow_nonneg hNnonneg _)
          (Real.rpow_nonneg hSnonneg _)
  simpa only [p, w, S, N] using hnormBound

private theorem finiteWeight_factor_bound {h : ℕ} (hh : 3 ≤ h)
    (t : ℝ) (ht : 0 < t) (L : ℕ) (htL : t ^ 2 ≤ L) (q : ℝ) (hq : 4 ≤ q)
    (A A' : Finset Site) (f f' : Site → ℝ) (N S W : ℝ)
    (hN : 0 ≤ N) (hS : 0 ≤ S) (hSone : 1 ≤ S) (hW : W ≤ S)
    (hnormTrans : finiteLpNorm A' (q / (q - 1)) f' =
      finiteLpNorm A (q / (q - 1)) f)
    (hnorm : finiteLpNorm A (q / (q - 1)) f ≤
      S ^ (1 - 2 / q) * N ^ (1 / q)) :
    W * finiteLpNorm A' (q / (q - 1)) f' ^ (h - 1) *
        ((L : ℝ) / t ^ 2) ^ (((h : ℝ) - 1) / q) ≤
      max 1 (1 / t ^ 2) ^ h * S ^ h * ((L : ℝ) * N) ^ (((h : ℝ) - 1) / q) := by
  let p : ℝ := q / (q - 1)
  let s : ℝ := ((h : ℝ) - 1) / q
  have hq1 : 0 < q := by linarith
  have hq2 : 2 < q := by linarith
  have hp_le_two : p ≤ 2 := by
    dsimp [p]
    rw [div_le_iff₀ (by linarith only [hq] : 0 < q - 1)]
    linarith only [hq]
  have hnormCoarse : finiteLpNorm A p f ≤ S * N ^ (1 / q) := by
    calc
      _ ≤ S ^ (1 - 2 / q) * N ^ (1 / q) := by simpa [p] using hnorm
      _ ≤ S * N ^ (1 / q) := by
        apply mul_le_mul_of_nonneg_right
        · have hdiv : 0 ≤ 2 / q := div_nonneg (by norm_num) hq1.le
          have ha : 1 - 2 / q ≤ 1 := by linarith
          simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hSone ha
        · exact Real.rpow_nonneg hN _
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    apply div_nonneg
    · have hh1 : 1 ≤ (h : ℝ) := by exact_mod_cast (show 1 ≤ h by omega)
      linarith
    · exact hq1.le
  have hs_eq : s = (1 / q) * ((h - 1 : ℕ) : ℝ) := by
    dsimp [s]
    rw [Nat.cast_sub (by omega : 1 ≤ h)]
    push_cast
    ring
  have hNpow : (N ^ (1 / q)) ^ (h - 1) = N ^ s := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN]
    congr 1
    rw [hs_eq]
  have hM : 1 ≤ max 1 (1 / t ^ 2) := le_max_left _ _
  have hs_le_h : s ≤ (h : ℝ) := by
    dsimp [s]
    rw [div_le_iff₀ hq1]
    have hhreal : 0 ≤ (h : ℝ) := by exact_mod_cast (Nat.zero_le h)
    have hqge : 1 ≤ q := by linarith
    have hprod : (h : ℝ) ≤ (h : ℝ) * q := by
      calc
        (h : ℝ) = (h : ℝ) * 1 := by ring
        _ ≤ (h : ℝ) * q := mul_le_mul_of_nonneg_left hqge hhreal
    exact le_trans (by linarith) hprod
  have htmax : (1 / t ^ 2) ^ s ≤ max 1 (1 / t ^ 2) ^ h := by
    calc
      (1 / t ^ 2) ^ s ≤ max 1 (1 / t ^ 2) ^ s := by
        apply Real.rpow_le_rpow
        · positivity
        · exact le_max_right _ _
        · exact hs_nonneg
      _ ≤ (max 1 (1 / t ^ 2)) ^ (h : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hM hs_le_h
      _ = max 1 (1 / t ^ 2) ^ h := by simp [Real.rpow_natCast]
  have hLpos : 0 < (L : ℝ) := lt_of_lt_of_le (sq_pos_of_pos ht) htL
  have hdivide : ((L : ℝ) / t ^ 2) ^ s = (L : ℝ) ^ s * (1 / t ^ 2) ^ s := by
    rw [div_eq_mul_inv, Real.mul_rpow hLpos.le (inv_nonneg.mpr (sq_nonneg t)), one_div]
  calc
    _ = W * (finiteLpNorm A p f) ^ (h - 1) * ((L : ℝ) / t ^ 2) ^ s := by
      simp only [p, s, hnormTrans]
    _ ≤ S * (S * N ^ (1 / q)) ^ (h - 1) * ((L : ℝ) / t ^ 2) ^ s := by
      have hnormPow : (finiteLpNorm A p f) ^ (h - 1) ≤
          (S * N ^ (1 / q)) ^ (h - 1) :=
        pow_le_pow_left₀ (finiteLpNorm_nonneg A p f) hnormCoarse _
      have hnormPowNonneg : 0 ≤ (finiteLpNorm A p f) ^ (h - 1) :=
        pow_nonneg (finiteLpNorm_nonneg A p f) _
      have hTnonneg : 0 ≤ ((L : ℝ) / t ^ 2) ^ s :=
        Real.rpow_nonneg (div_nonneg hLpos.le (sq_nonneg t)) _
      calc
        _ = (W * (finiteLpNorm A p f) ^ (h - 1)) * ((L : ℝ) / t ^ 2) ^ s := by ring
        _ ≤ (S * (finiteLpNorm A p f) ^ (h - 1)) * ((L : ℝ) / t ^ 2) ^ s :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hW hnormPowNonneg) hTnonneg
        _ ≤ (S * ((S * N ^ (1 / q)) ^ (h - 1))) * ((L : ℝ) / t ^ 2) ^ s :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hnormPow hS) hTnonneg
        _ = S * (S * N ^ (1 / q)) ^ (h - 1) * ((L : ℝ) / t ^ 2) ^ s := by ring
    _ = S ^ h * N ^ s * ((L : ℝ) / t ^ 2) ^ s := by
      rw [mul_pow, hNpow]
      have hhsub : h - 1 + 1 = h := by omega
      have hpowS : S * S ^ (h - 1) = S ^ h := by
        calc
          S * S ^ (h - 1) = S ^ (h - 1) * S := by ring
          _ = S ^ (h - 1 + 1) := by rw [pow_succ]
          _ = S ^ h := by rw [hhsub]
      calc
        S * (S ^ (h - 1) * N ^ s) * ((L : ℝ) / t ^ 2) ^ s
            = (S * S ^ (h - 1)) * N ^ s * ((L : ℝ) / t ^ 2) ^ s := by ring
        _ = S ^ h * N ^ s * ((L : ℝ) / t ^ 2) ^ s := by rw [hpowS]
    _ = S ^ h * ((L : ℝ) * N) ^ s * (1 / t ^ 2) ^ s := by
      rw [hdivide]
      calc
        _ = S ^ h * (N ^ s * (L : ℝ) ^ s) * (1 / t ^ 2) ^ s := by ring
        _ = S ^ h * ((L : ℝ) * N) ^ s * (1 / t ^ 2) ^ s := by
          have hLN : N ^ s * (L : ℝ) ^ s = ((L : ℝ) * N) ^ s := by
            rw [← Real.mul_rpow hN hLpos.le]
            congr 1
            ring
          rw [hLN]
    _ ≤ S ^ h * ((L : ℝ) * N) ^ s * max 1 (1 / t ^ 2) ^ h := by
      calc
        _ = (S ^ h * ((L : ℝ) * N) ^ s) * (1 / t ^ 2) ^ s := by ring
        _ ≤ (S ^ h * ((L : ℝ) * N) ^ s) * max 1 (1 / t ^ 2) ^ h :=
          mul_le_mul_of_nonneg_left htmax
            (mul_nonneg (pow_nonneg hS _) (Real.rpow_nonneg (mul_nonneg hLpos.le hN) _))
    _ = max 1 (1 / t ^ 2) ^ h * S ^ h * ((L : ℝ) * N) ^ s := by ring

private theorem centeredMoment_final_calc {M M' C B B' V V' : ℝ}
    (hM : M = M') (hbase : M' ≤ C * B * V)
    (hcoeff : C * B ≤ C * B') (hV : V ≤ V')
    (hVnonneg : 0 ≤ V) (hCB' : 0 ≤ C * B') : M ≤ C * B' * V' := by
  calc
    M = M' := hM
    _ ≤ C * B * V := hbase
    _ ≤ C * B' * V := mul_le_mul_of_nonneg_right hcoeff hVnonneg
    _ ≤ C * B' * V' := mul_le_mul_of_nonneg_left hV hCB'

/-- CSZ25 Proposition 5.9 from Theorem 5.7, with the translated start profile centred at `z₀`. -/
theorem abs_centeredMoment_profileP2Fun_le_improved_of_ccr {h : ℕ} (hh : 3 ≤ h)
    (hccr : CCRMomentBound h) (t : ℝ) (ht : 0 < t) :
    ∃ σ₀ K : ℝ, 0 < σ₀ ∧ 0 < K ∧ ∀ lam : ℝ, 0 ≤ lam → ∃ C : ℝ, 0 < C ∧
      ∀ β : ℝ, Polymer.sigmaSq β ≤ σ₀ → ∀ L : ℕ, t ^ 2 ≤ L →
      Polymer.sigmaSq β * dampedOverlap (lam / L) L < 1 → ∀ q : ℝ, 4 ≤ q →
      2 * q * (K * Polymer.sigmaSq β / (1 - Polymer.sigmaSq β * dampedOverlap (lam / L) L)) < 1 →
      ∀ (φ : Site → ℝ) (A : Finset Site), (∀ z, 0 ≤ φ z) → (∀ z ∉ A, φ z = 0) →
        ∑ z ∈ A, φ z = 1 → ∀ z₀ : Site,
        |∫ ω, (profileP2Fun β 0 L φ (fun _ => 1) ω -
            ∫ ω', profileP2Fun β 0 L φ (fun _ => 1) ω' ∂disorderLaw) ^ h ∂disorderLaw| ≤
          C * (2 * q * (K * Polymer.sigmaSq β / (1 - Polymer.sigmaSq β * dampedOverlap (lam / L) L))) ^
                ((h : ℝ) / 2) /
              (1 - 2 * q * (K * Polymer.sigmaSq β / (1 - Polymer.sigmaSq β * dampedOverlap (lam / L) L))) *
            ((L : ℝ) * ∑ z ∈ A, φ z ^ 2) ^ (((h : ℝ) - 1) / q) *
            (∑ z ∈ A, φ z * Real.exp (2 * t * ‖siteToPlane (z - z₀)‖ / Real.sqrt L)) ^ h := by
  obtain ⟨σ₀, K, hσ₀, hK, hccr_t⟩ := hccr t ht
  refine ⟨σ₀, K, hσ₀, hK, fun lam hlam => ?_⟩
  obtain ⟨C, hC, hccr_lam⟩ := hccr_t lam hlam
  let C' := C * max 1 (1 / t ^ 2) ^ h
  have hC' : 0 < C' := by
    dsimp [C']
    exact mul_pos hC (pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _)
  refine ⟨C', hC', ?_⟩
  intro β hσ₀β L htL hdam q hq hsmall φ A hφ hφA hmass z₀
  let A' := A.image (fun z : Site => z - z₀)
  let ψ : Site → ℝ := fun z => φ (z + z₀)
  let p : ℝ := q / (q - 1)
  let x : ℝ := K * Polymer.sigmaSq β / (1 - Polymer.sigmaSq β * dampedOverlap (lam / L) L)
  let r : ℝ := q / (q - 2)
  let s : ℝ := ((h : ℝ) - 1) / q
  let w (z : Site) := Real.exp (t * ‖siteToPlane (z - z₀)‖ / Real.sqrt L)
  let w0 (z : Site) := Real.exp (t * ‖siteToPlane z‖ / Real.sqrt L)
  let w2 (z : Site) := Real.exp (2 * t * ‖siteToPlane (z - z₀)‖ / Real.sqrt L)
  let N : ℝ := ∑ z ∈ A, φ z ^ 2
  let S : ℝ := ∑ z ∈ A, φ z * w2 z
  have hinj : Set.InjOn (fun z : Site => z - z₀) A := by
    intro a ha b hb hab
    exact sub_left_inj.mp hab
  have hσ : 0 ≤ Polymer.sigmaSq β :=
    sub_nonneg.2 (Real.one_le_exp_iff.2 (sq_nonneg β))
  have hden : 0 < 1 - Polymer.sigmaSq β * dampedOverlap (lam / L) L :=
    sub_pos.mpr hdam
  have hx : 0 ≤ x := by dsimp [x]; exact div_nonneg (mul_nonneg hK.le hσ) hden.le
  have hq1 : 0 < q := by linarith
  have hq2 : 2 < q := by linarith
  have ha : 0 ≤ 1 - 2 / q := by
    have hq4 : 2 / q ≤ 1 := (div_le_one hq1).2 (by linarith)
    linarith
  have hp1 : 1 < p := by
    dsimp [p]
    rw [lt_div_iff₀ (by linarith only [hq] : 0 < q - 1)]
    linarith only
  have hpq : p.HolderConjugate q := by
    rw [Real.holderConjugate_iff]
    constructor
    · exact hp1
    · dsimp [p]
      field_simp
      ring
  have hp_le_two : p ≤ 2 := by
    dsimp [p]
    rw [div_le_iff₀ (by linarith only [hq] : 0 < q - 1)]
    linarith only [hq]
  have hpqx : p * q * x ≤ 2 * q * x := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hp_le_two hq1.le) hx
  have hpqxlt : p * q * x < 1 := lt_of_le_of_lt hpqx hsmall
  have hA'supp : ∀ z ∉ A', ψ z = 0 := by
    intro z hz
    apply hφA
    intro hmem
    apply hz
    exact Finset.mem_image.mpr ⟨z + z₀, hmem, by simp⟩
  have hmass' : ∑ z ∈ A', ψ z = 1 := by
    change ∑ z ∈ A.image (fun z => z - z₀), φ (z + z₀) = 1
    rw [Finset.sum_image hinj]
    simpa [sub_add_cancel] using hmass
  have hbase := hccr_lam β hσ₀β L htL hdam p q hpq hpqxlt ψ A' (fun z => hφ (z + z₀))
    hA'supp
  have htranslate := centeredMoment_translate_finiteSupport (h := h) β L φ A hφA hmass z₀
  have hsumImage (f : Site → ℝ) :
      (∑ z ∈ A', f z) = ∑ z ∈ A, f (z - z₀) := by
    dsimp [A']
    exact Finset.sum_image hinj
  have hψshift (z : Site) : ψ (z - z₀) = φ z := by
    dsimp [ψ]
    congr 1; abel
  have hW : (∑ z ∈ A', ψ z * w0 z) = ∑ z ∈ A, φ z * w z := by
    rw [hsumImage]
    apply Finset.sum_congr rfl
    intro z hz
    rw [hψshift]
  have hN : (∑ z ∈ A', ψ z ^ 2) = N := by
    rw [hsumImage]
    apply Finset.sum_congr rfl
    intro z hz
    rw [hψshift]
  have hnormTrans :
      finiteLpNorm A' p (fun z => ψ z * w0 z) =
        finiteLpNorm A p (fun z => φ z * w z) := by
    unfold finiteLpNorm
    congr 1
    rw [hsumImage]
    apply Finset.sum_congr rfl
    intro z hz
    change |ψ (z - z₀) * w0 (z - z₀)| ^ p = |φ z * w z| ^ p
    rw [hψshift]
  have hNnonneg : 0 ≤ N := by
    dsimp [N]
    exact Finset.sum_nonneg fun z hz => sq_nonneg (φ z)
  have hSnonneg : 0 ≤ S := by
    dsimp [S]
    apply Finset.sum_nonneg
    intro z hz
    exact mul_nonneg (hφ z) (Real.exp_nonneg _)
  have hSone : 1 ≤ S := by
    dsimp [S, w2]
    calc
      1 = ∑ z ∈ A, φ z := hmass.symm
      _ ≤ ∑ z ∈ A, φ z * Real.exp (2 * t * ‖siteToPlane (z - z₀)‖ / Real.sqrt L) := by
        apply Finset.sum_le_sum
        intro z hz
        have he : 1 ≤ Real.exp (2 * t * ‖siteToPlane (z - z₀)‖ / Real.sqrt L) := by
          apply Real.one_le_exp_iff.mpr
          have htden : 0 < Real.sqrt L :=
            Real.sqrt_pos.2 (lt_of_lt_of_le (sq_pos_of_pos ht) htL)
          positivity
        simpa using mul_le_mul_of_nonneg_left he (hφ z)
  have hnormBound := finiteLpNorm_weightedProfile_bound t ht L htL q hq φ A hφ hmass z₀
  have hnormBound' : finiteLpNorm A p (fun z => φ z * w z) ≤
      S ^ (1 - 2 / q) * N ^ (1 / q) := by
    simpa [p, w, S, N] using hnormBound
  have hsmall' : 2 * q * x < 1 := hsmall
  have hfrac :
      (p * q * x) ^ ((h : ℝ) / 2) / (1 - p * q * x) ≤
        (2 * q * x) ^ ((h : ℝ) / 2) / (1 - 2 * q * x) := by
    have hnum : (p * q * x) ^ ((h : ℝ) / 2) ≤ (2 * q * x) ^ ((h : ℝ) / 2) := by
      apply Real.rpow_le_rpow
        (mul_nonneg (mul_nonneg (le_trans (by norm_num) hp1.le) hq1.le) hx)
      · exact hpqx
      · exact div_nonneg (by exact_mod_cast (Nat.zero_le h)) (by norm_num)
    have hdenP : 0 < 1 - p * q * x := sub_pos.mpr hpqxlt
    have hdenQ : 0 < 1 - 2 * q * x := sub_pos.mpr hsmall
    calc
      _ = (p * q * x) ^ ((h : ℝ) / 2) * (1 / (1 - p * q * x)) := by rw [div_eq_mul_inv, one_div]
      _ ≤ (2 * q * x) ^ ((h : ℝ) / 2) * (1 / (1 - 2 * q * x)) := by
        exact mul_le_mul hnum
          (one_div_le_one_div_of_le hdenQ (by linarith [hpqx]))
          (one_div_nonneg.mpr (sub_nonneg.mpr hpqxlt.le))
          (Real.rpow_nonneg
            (mul_nonneg (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) hq1.le) hx) _)
      _ = _ := by simp only [div_eq_mul_inv, one_mul]
  have hWsum : (∑ z ∈ A', ψ z * w0 z) ≤ S := by
    rw [hW]
    dsimp [S, w2]
    apply Finset.sum_le_sum
    intro z hz
    have harg : 0 ≤ t * ‖siteToPlane (z - z₀)‖ / Real.sqrt L :=
      div_nonneg (mul_nonneg ht.le (norm_nonneg _)) (Real.sqrt_nonneg _)
    have htwice : 2 * t * ‖siteToPlane (z - z₀)‖ / Real.sqrt L =
        2 * (t * ‖siteToPlane (z - z₀)‖ / Real.sqrt L) := by ring
    have hle : t * ‖siteToPlane (z - z₀)‖ / Real.sqrt L ≤
        2 * t * ‖siteToPlane (z - z₀)‖ / Real.sqrt L := by
      rw [htwice]
      linarith only [harg]
    dsimp [w]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) (hφ z)
  have hfactor := finiteWeight_factor_bound hh t ht L htL q hq A A'
    (fun z => φ z * w z) (fun z => ψ z * w0 z) N S
    (∑ z ∈ A', ψ z * w0 z) hNnonneg hSnonneg hSone hWsum hnormTrans hnormBound'
  have hdenQ : 0 < 1 - 2 * q * x := sub_pos.mpr hsmall
  have hfracP_nonneg :
      0 ≤ (p * q * x) ^ ((h : ℝ) / 2) / (1 - p * q * x) :=
    div_nonneg (Real.rpow_nonneg (mul_nonneg (mul_nonneg (by positivity) hq1.le) hx) _)
      (sub_nonneg.mpr hpqxlt.le)
  have hcoeff :
      C * ((p * q * x) ^ ((h : ℝ) / 2) / (1 - p * q * x)) ≤
        C * ((2 * q * x) ^ ((h : ℝ) / 2) / (1 - 2 * q * x)) :=
    mul_le_mul_of_nonneg_left hfrac hC.le
  have holdWeightNonneg :
      0 ≤ (∑ z ∈ A', ψ z * w0 z) *
        finiteLpNorm A' p (fun z => ψ z * w0 z) ^ (h - 1) *
        ((L : ℝ) / t ^ 2) ^ (((h : ℝ) - 1) / q) := by
    have hsumNonneg : 0 ≤ ∑ z ∈ A', ψ z * w0 z := by
      apply Finset.sum_nonneg
      intro z hz
      exact mul_nonneg (hφ (z + z₀)) (Real.exp_nonneg _)
    have hnormNonneg : 0 ≤ finiteLpNorm A' p (fun z => ψ z * w0 z) :=
      finiteLpNorm_nonneg A' p _
    have hnormPow : 0 ≤ finiteLpNorm A' p (fun z => ψ z * w0 z) ^ (h - 1) :=
      pow_nonneg hnormNonneg _
    have hclock : 0 ≤ ((L : ℝ) / t ^ 2) ^ (((h : ℝ) - 1) / q) :=
      Real.rpow_nonneg (div_nonneg (by positivity) (sq_nonneg t)) _
    exact mul_nonneg (mul_nonneg hsumNonneg hnormPow) hclock
  have hnewCoefficientNonneg :
      0 ≤ C * ((2 * q * x) ^ ((h : ℝ) / 2) / (1 - 2 * q * x)) := by
    apply mul_nonneg hC.le
    exact div_nonneg (Real.rpow_nonneg (mul_nonneg (mul_nonneg (by positivity) hq1.le) hx) _)
      hdenQ.le
  have htranslateAbs :
      |∫ ω, (profileP2Fun β 0 L φ (fun _ => 1) ω -
          ∫ ω', profileP2Fun β 0 L φ (fun _ => 1) ω' ∂disorderLaw) ^ h ∂disorderLaw| =
        |∫ ω, (profileP2Fun β 0 L ψ (fun _ => 1) ω -
          ∫ ω', profileP2Fun β 0 L ψ (fun _ => 1) ω' ∂disorderLaw) ^ h ∂disorderLaw| :=
    congrArg abs htranslate
  have hbase' :
      |∫ ω, (profileP2Fun β 0 L ψ (fun _ => 1) ω -
          ∫ ω', profileP2Fun β 0 L ψ (fun _ => 1) ω' ∂disorderLaw) ^ h ∂disorderLaw| ≤
        C * ((p * q * x) ^ ((h : ℝ) / 2) / (1 - p * q * x)) *
          ((∑ z ∈ A', ψ z * w0 z) *
            finiteLpNorm A' p (fun z => ψ z * w0 z) ^ (h - 1) *
            ((L : ℝ) / t ^ 2) ^ (((h : ℝ) - 1) / q)) := by
    convert hbase using 1; dsimp [x]; ring
  have hfinal := centeredMoment_final_calc htranslateAbs hbase' hcoeff hfactor
    holdWeightNonneg hnewCoefficientNonneg
  convert hfinal using 1; dsimp [C', x, N, S]; ring

/-- CSZ25 Theorem 5.2 from Theorem 5.7, with finite support and a site-centred localization bound. -/
theorem abs_centeredMoment_le_variance_pow_of_greenEnergy_of_ccr {h : ℕ} (hh : 3 ≤ h)
    (hccr : CCRMomentBound h) (t c₁ c₂' c₃ : ℝ) (ht : 0 < t) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂')
    (hc₃ : 0 < c₃) :
    ∃ (L₀ : ℕ) (C : ℝ), ∀ β : ℝ, ∀ L : ℕ, L₀ ≤ L → ∀ (φ : Site → ℝ) (A : Finset Site),
      (∀ z, 0 ≤ φ z) → (∀ z ∉ A, φ z = 0) → HasSum φ 1 →
      (∃ z₀ : Site, ∑ z ∈ A, φ z * Real.exp (2 * t * ‖siteToPlane (z - z₀)‖ / Real.sqrt L) ≤ c₁) →
      Real.log (L * ∑ z ∈ A, φ z ^ 2) ≤ c₂' * greenEnergy L φ →
      Var[fun ω => profileP2Fun β 0 L φ (fun _ => 1) ω; disorderLaw] ≤ c₃ →
      |∫ ω, (profileP2Fun β 0 L φ (fun _ => 1) ω -
          ∫ ω', profileP2Fun β 0 L φ (fun _ => 1) ω' ∂disorderLaw) ^ h ∂disorderLaw| ≤
        C * Var[fun ω => profileP2Fun β 0 L φ (fun _ => 1) ω; disorderLaw] ^ ((h : ℝ) / 2) := by
  obtain ⟨aLo, aHi, haLo, haLoHi, ha⟩ := srwKernel_two_mul_zero_bounds
  have haHi : 0 < aHi := haLo.trans_le haLoHi
  obtain ⟨θ, hθ, hθbound⟩ := sigmaSq_mul_replicaOverlap_sub_le_one t c₁ c₃ ht hc₁ hc₃
  obtain ⟨σ₀, K, hσ₀, hK, himproved⟩ :=
    abs_centeredMoment_profileP2Fun_le_improved_of_ccr hh hccr t ht
  let M : ℝ := max (16 * K) (4 * aHi)
  obtain ⟨lam, Lrate, hlam, hlamRate, hrate⟩ := exists_dampingRate θ M σ₀ hσ₀
  obtain ⟨Cimp, hCimp, himprovedLam⟩ := himproved lam (le_trans (by norm_num) hlam)
  obtain ⟨η, hη, hgreenHalf⟩ := greenEnergy_half_ge t c₁ ht hc₁
  obtain ⟨Cq, Cq', hCq, hCq', hqUniform⟩ :=
    exists_q_choice η K c₂' c₃ aHi hη hK hc₂ hc₃ haHi.le
  let L₀ : ℕ := max Lrate (max 2 ⌈t ^ 2⌉₊)
  let Cfinal : ℝ := Cimp * 2 * Cq ^ ((h : ℝ) / 2) * Cq' ^ (h - 1) * c₁ ^ h
  have hCfinal : 0 < Cfinal := by
    dsimp [Cfinal]
    positivity
  refine ⟨L₀, Cfinal, fun β L hL φ A hφ hφA hmass hlocalized hlog hvar => ?_⟩
  have hLrate : Lrate ≤ L := (le_max_left _ _).trans hL
  have hLaux : max 2 ⌈t ^ 2⌉₊ ≤ L := (le_max_right _ _).trans hL
  have hLtwo : 2 ≤ L := (le_max_left _ _).trans hLaux
  have hceilL : ⌈t ^ 2⌉₊ ≤ L := (le_max_right _ _).trans hLaux
  have htL : t ^ 2 ≤ (L : ℝ) := by
    calc
      t ^ 2 ≤ (⌈t ^ 2⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ L := by exact_mod_cast hceilL
  have hsumFin : HasSum φ (∑ z ∈ A, φ z) :=
    hasSum_sum_of_ne_finset_zero (s := A) (f := φ) (fun z hz => hφA z hz)
  have hmassFin : (∑ z ∈ A, φ z) = 1 := hsumFin.unique hmass
  have hσnonneg : 0 ≤ Polymer.sigmaSq β := by
    unfold Polymer.sigmaSq
    have h := Real.one_le_exp (sq_nonneg β)
    linarith
  by_cases hσzero : Polymer.sigmaSq β = 0
  · have hβzero : β = 0 := by
      have hExp : Real.exp (β ^ 2) = Real.exp 0 := by
        unfold Polymer.sigmaSq at hσzero
        have h1 : Real.exp (β ^ 2) = 1 := by linarith
        simpa using h1
      have hsq : β ^ 2 = 0 := Real.exp_injective hExp
      exact sq_eq_zero_iff.mp hsq
    have hprofile (ω : Disorder) : profileP2Fun β 0 L φ (fun _ => 1) ω = 1 := by
      rw [hβzero, Polymer.profileP2Fun_eq_sum (0 : ℝ) 0 L φ (fun _ => 1) A hφA ω]
      simp only [Nat.sub_zero, mul_one, Polymer.tsum_pointToPoint, Polymer.pointToPlane_zero_beta]
      exact hmassFin
    have hmean : (∫ ω, profileP2Fun β 0 L φ (fun _ => 1) ω ∂disorderLaw) = 1 := by
      simp_rw [hprofile]
      simp
    have hmoment :
        (∫ ω, (profileP2Fun β 0 L φ (fun _ => 1) ω -
          ∫ ω', profileP2Fun β 0 L φ (fun _ => 1) ω' ∂disorderLaw) ^ h ∂disorderLaw) = 0 := by
      rw [hmean]
      simp_rw [hprofile]
      simp [show h ≠ 0 by omega]
    have hvariance : Var[fun ω => profileP2Fun β 0 L φ (fun _ => 1) ω; disorderLaw] = 0 := by
      have hconst : (fun ω : Disorder => profileP2Fun β 0 L φ (fun _ => 1) ω) =
          fun _ => (1 : ℝ) := by
        funext ω
        exact hprofile ω
      rw [hconst, variance_eq_integral (by fun_prop)]
      simp
    have hexp : 0 < ((h : ℝ) / 2) := by positivity
    rw [hmoment, hvariance]
    simp [Real.zero_rpow (ne_of_gt hexp)]
  · have hσpos : 0 < Polymer.sigmaSq β := lt_of_le_of_ne hσnonneg (Ne.symm hσzero)
    obtain ⟨z₀, hweighted⟩ := hlocalized
    let fLocal : Site → ℝ := fun z =>
      φ z * Real.exp (2 * t * ‖siteToPlane z - siteToPlane z₀‖ / Real.sqrt L)
    have hfLocalSupport : ∀ z ∉ A, fLocal z = 0 := by
      intro z hz
      simp [fLocal, hφA z hz]
    have hsub (x y : Site) : siteToPlane (y - x) = siteToPlane y - siteToPlane x := by
      ext i
      simp [siteToPlane]
    have hlocalSum : HasSum fLocal (∑ z ∈ A, fLocal z) :=
      hasSum_sum_of_ne_finset_zero (s := A) (f := fLocal) hfLocalSupport
    have hlocal : ExpLocalized t c₁ L φ := by
      refine ⟨siteToPlane z₀, hlocalSum.summable, ?_⟩
      rw [hlocalSum.tsum_eq]
      calc
        (∑ z ∈ A, fLocal z) =
            ∑ z ∈ A, φ z * Real.exp
              (2 * t * ‖siteToPlane (z - z₀)‖ / Real.sqrt L) := by
          apply Finset.sum_congr rfl
          intro z hz
          dsimp [fLocal]
          rw [← hsub z₀ z]
        _ ≤ c₁ := by simpa [siteToPlane] using hweighted
    have hcritical := hθbound β L φ hφ hmass hlocal hvar
    obtain ⟨hσ₀β, hdamp⟩ := hrate β L hLrate hcritical
    let D : ℝ := dampedOverlap (lam / L) L
    let Γ : ℝ := K * Polymer.sigmaSq β / (1 - Polymer.sigmaSq β * D)
    have hMgeK : 16 * K ≤ M := by dsimp [M]; exact le_max_left _ _
    have hMgeHi : 4 * aHi ≤ M := by dsimp [M]; exact le_max_right _ _
    have hdampsplit : Polymer.sigmaSq β * (D + M) ≤ 1 := by
      simpa [D] using hdamp
    have hMpositive : 0 < M := lt_of_lt_of_le (by positivity : 0 < 16 * K) hMgeK
    have hdamstrict : Polymer.sigmaSq β * D < 1 := by
      linarith only [mul_pos hσpos hMpositive, hdampsplit]
    have hden : 0 < 1 - Polymer.sigmaSq β * D := sub_pos.mpr hdamstrict
    have hGammaPos : 0 < Γ := by
      dsimp [Γ]
      exact div_pos (mul_pos hK hσpos) hden
    have hdenLower : Polymer.sigmaSq β * M ≤ 1 - Polymer.sigmaSq β * D := by
      linarith only [hdampsplit]
    have hGammaSmall : Γ ≤ 1 / 16 := by
      dsimp [Γ]
      rw [div_le_iff₀ hden]
      have h16 : 16 * K * Polymer.sigmaSq β ≤ Polymer.sigmaSq β * M :=
        by
          calc
            16 * K * Polymer.sigmaSq β = Polymer.sigmaSq β * (16 * K) := by ring
            _ ≤ Polymer.sigmaSq β * M := mul_le_mul_of_nonneg_left hMgeK hσnonneg
      linarith only [hdenLower, h16]
    have hfourDamp : Polymer.sigmaSq β * (D + 4 * aHi) ≤ 1 := by
      have hle : D + 4 * aHi ≤ D + M := by linarith [hMgeHi]
      exact (mul_le_mul_of_nonneg_left hle hσnonneg).trans hdampsplit
    have haUpper : ∀ n : ℕ, 1 ≤ n → srwKernel (2 * n) 0 ≤ aHi / n :=
      fun n hn => (ha n hn).2
    have hFhalf := inv_two_mul_le_freeSecondMoment_half haUpper β L
      (le_trans (by norm_num) hlam) hfourDamp
    have hRhNonneg : 0 ≤ greenEnergy (L / 2) φ := greenEnergy_nonneg _ _ hφ
    have hRhVar := (variance_profileP2Fun_bounds β L φ hφ hmass.summable).1
    have hprodLower :
        greenEnergy (L / 2) φ * Polymer.sigmaSq β *
          (1 / (2 * (1 - Polymer.sigmaSq β * D))) ≤
        Var[fun ω => profileP2Fun β 0 L φ (fun _ => 1) ω; disorderLaw] := by
      calc
        _ ≤ greenEnergy (L / 2) φ * Polymer.sigmaSq β * Renewal.freeSecondMoment β (L / 2) :=
          mul_le_mul_of_nonneg_left hFhalf (mul_nonneg hRhNonneg hσnonneg)
        _ ≤ _ := hRhVar
    have hGammaRh : Γ * greenEnergy (L / 2) φ ≤
        2 * K * Var[fun ω => profileP2Fun β 0 L φ (fun _ => 1) ω; disorderLaw] := by
      have heq : Γ * greenEnergy (L / 2) φ =
          2 * K * (greenEnergy (L / 2) φ * Polymer.sigmaSq β *
            (1 / (2 * (1 - Polymer.sigmaSq β * D)))) := by
        dsimp [Γ]
        field_simp [ne_of_gt hden]
      rw [heq]
      exact mul_le_mul_of_nonneg_left hprodLower (by positivity)
    have hRhRL : greenEnergy (L / 2) φ ≤ greenEnergy L φ :=
      greenEnergy_mono (Nat.div_le_self L 2) φ hφ hmass.summable
    have hRLsub : greenEnergy L φ - greenEnergy (L / 2) φ ≤ aHi :=
      greenEnergy_sub_half_le haUpper L φ hφ hmass
    have hRhlower : η ≤ greenEnergy (L / 2) φ := hgreenHalf L hLtwo φ hφ hmass hlocal
    let X : ℝ := (L : ℝ) * ∑ z ∈ A, φ z ^ 2
    have hNnonneg : 0 ≤ ∑ z ∈ A, φ z ^ 2 :=
      Finset.sum_nonneg fun z hz => sq_nonneg (φ z)
    have hAcard : 1 ≤ A.card := by
      by_contra hnot
      have hzero : A.card = 0 := by omega
      have hAempty : A = ∅ := Finset.card_eq_zero.mp hzero
      simp [hAempty] at hmassFin
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq A (fun _ => (1 : ℝ)) φ
    have hcs' : (1 : ℝ) ≤ (A.card : ℝ) * ∑ z ∈ A, φ z ^ 2 := by
      simpa [hmassFin] using hcs
    have hNpos : 0 < ∑ z ∈ A, φ z ^ 2 := by
      by_contra hn
      have hNzero : ∑ z ∈ A, φ z ^ 2 = 0 :=
        le_antisymm (le_of_not_gt hn) hNnonneg
      rw [hNzero] at hcs'
      norm_num at hcs'
    have hXpos : 0 < X := by
      dsimp [X]
      exact mul_pos (by exact_mod_cast (show 0 < L by omega)) hNpos
    obtain ⟨q, hq, hqΓhalf, hqΓV, hqX⟩ := hqUniform Γ
      (greenEnergy (L / 2) φ) (greenEnergy L φ)
      (Var[fun ω => profileP2Fun β 0 L φ (fun _ => 1) ω; disorderLaw]) X
      hGammaPos hGammaSmall hRhlower hRhRL (by linarith [hRLsub]) hGammaRh hvar hXpos
      (by simpa [X] using hlog)
    have hqΓsmall : 2 * q * Γ < 1 := lt_of_le_of_lt hqΓhalf (by norm_num)
    have hImp := himprovedLam β hσ₀β L htL hdamstrict q hq hqΓsmall φ A hφ hφA hmassFin z₀
    let W : ℝ := ∑ z ∈ A, φ z *
      Real.exp (2 * t * ‖siteToPlane (z - z₀)‖ / Real.sqrt L)
    have hWnonneg : 0 ≤ W := by
      dsimp [W]
      exact Finset.sum_nonneg fun z hz => mul_nonneg (hφ z) (Real.exp_nonneg _)
    have hWle : W ≤ c₁ := by simpa [W] using hweighted
    have hVnonneg : 0 ≤ Var[fun ω => profileP2Fun β 0 L φ (fun _ => 1) ω; disorderLaw] :=
      variance_nonneg _ _
    have hnumPow : (2 * q * Γ) ^ ((h : ℝ) / 2) ≤
        (Cq * Var[fun ω => profileP2Fun β 0 L φ (fun _ => 1) ω; disorderLaw]) ^ ((h : ℝ) / 2) :=
      Real.rpow_le_rpow (by positivity) hqΓV (by positivity)
    have hsplitPow :
        (Cq * Var[fun ω => profileP2Fun β 0 L φ (fun _ => 1) ω; disorderLaw]) ^ ((h : ℝ) / 2) =
          Cq ^ ((h : ℝ) / 2) *
            Var[fun ω => profileP2Fun β 0 L φ (fun _ => 1) ω; disorderLaw] ^ ((h : ℝ) / 2) :=
      Real.mul_rpow hCq.le hVnonneg
    have hs : (((h : ℝ) - 1) / q) = (1 / q) * ((h - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ h)]
      ring
    have hXpow : X ^ (((h : ℝ) - 1) / q) ≤ Cq' ^ (h - 1) := by
      have heq : X ^ (((h : ℝ) - 1) / q) = (X ^ (1 / q)) ^ (h - 1) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hXpos.le]
        congr 1
      rw [heq]
      exact pow_le_pow_left₀ (Real.rpow_nonneg hXpos.le _) hqX _
    have hWpow : W ^ h ≤ c₁ ^ h := pow_le_pow_left₀ hWnonneg hWle h
    have hWpowNonneg : 0 ≤ W ^ h := pow_nonneg hWnonneg h
    have hXpowNonneg : 0 ≤ X ^ (((h : ℝ) - 1) / q) := Real.rpow_nonneg hXpos.le _
    have hrecip : 1 / (1 - 2 * q * Γ) ≤ 2 := by
      calc
        _ ≤ 1 / (1 / 2 : ℝ) :=
          one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2)
            (by linarith [hqΓhalf])
        _ = 2 := by norm_num
    have hcoef1 :
        Cimp * (2 * q * Γ) ^ ((h : ℝ) / 2) / (1 - 2 * q * Γ) ≤
          Cimp * (2 * q * Γ) ^ ((h : ℝ) / 2) * 2 := by
      calc
        _ = (Cimp * (2 * q * Γ) ^ ((h : ℝ) / 2)) * (1 / (1 - 2 * q * Γ)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hrecip
          (mul_nonneg hCimp.le (Real.rpow_nonneg (by positivity) _))
    have hcoef2 :
        Cimp * (2 * q * Γ) ^ ((h : ℝ) / 2) * 2 ≤
          Cimp * (Cq * Var[fun ω => profileP2Fun β 0 L φ (fun _ => 1) ω; disorderLaw]) ^
            ((h : ℝ) / 2) * 2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hnumPow hCimp.le) (by norm_num)
    have hrest : X ^ (((h : ℝ) - 1) / q) * W ^ h ≤ Cq' ^ (h - 1) * c₁ ^ h := by
      calc
        _ ≤ Cq' ^ (h - 1) * W ^ h := mul_le_mul_of_nonneg_right hXpow hWpowNonneg
        _ ≤ _ := mul_le_mul_of_nonneg_left hWpow (pow_nonneg (by positivity : 0 ≤ Cq') _)
    have hfull :
        Cimp * (2 * q * Γ) ^ ((h : ℝ) / 2) / (1 - 2 * q * Γ) *
          X ^ (((h : ℝ) - 1) / q) * W ^ h ≤
        Cfinal * Var[fun ω => profileP2Fun β 0 L φ (fun _ => 1) ω; disorderLaw] ^ ((h : ℝ) / 2) := by
      calc
        _ = (Cimp * (2 * q * Γ) ^ ((h : ℝ) / 2) / (1 - 2 * q * Γ)) *
              (X ^ (((h : ℝ) - 1) / q) * W ^ h) := by ring
        _ ≤ (Cimp * (2 * q * Γ) ^ ((h : ℝ) / 2) * 2) *
              (Cq' ^ (h - 1) * c₁ ^ h) :=
            mul_le_mul hcoef1 hrest (mul_nonneg hXpowNonneg hWpowNonneg)
              (mul_nonneg (mul_nonneg hCimp.le (Real.rpow_nonneg (by positivity) _)) (by norm_num))
        _ ≤ (Cimp * (Cq * Var[fun ω => profileP2Fun β 0 L φ (fun _ => 1) ω; disorderLaw]) ^
                ((h : ℝ) / 2) * 2) * (Cq' ^ (h - 1) * c₁ ^ h) :=
            mul_le_mul_of_nonneg_right hcoef2 (mul_nonneg (pow_nonneg (by positivity : 0 ≤ Cq') _) (pow_nonneg hc₁.le _))
        _ = Cfinal * Var[fun ω => profileP2Fun β 0 L φ (fun _ => 1) ω; disorderLaw] ^ ((h : ℝ) / 2) := by
          rw [hsplitPow]
          dsimp [Cfinal]
          ring
    exact hImp.trans hfull

end Critical2DKPZ.MomentBounds

end
