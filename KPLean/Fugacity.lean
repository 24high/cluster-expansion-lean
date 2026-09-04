/-
Copyright (c) 2026 Dennis Michael Heine. All rights reserved.
Released under the CC BY-NC-SA 4.0 license as described in the file LICENSE.
Authors: Dennis Michael Heine
-/
import KPLean.ThermodynamicLimit
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.ChangeOrigin

/-!
# Die Fugazitätsentwicklung und die Analytizität des Drucks

Skaliert man alle Gewichte mit einer Fugazität `z`, so ist die Ordnung
`n` der Cluster-Reihe homogen vom Grad `n + 1`:

`clusterOrderSum (z · w) n = z^(n+1) · clusterOrderSum w n`

(`clusterOrderSum_scale`) — jedes Tupel hat genau `n + 1` Einträge. Die
Cluster-Reihe wird damit zu einer echten **Potenzreihe in `z`** mit
volumenabhängigen, aber `z`-freien Koeffizienten (`fugacityCoeff`).

Die Kotecký-Preiss-Bedingung ist unter Skalierung mit `‖z‖ ≤ 1` stabil
(`KPCondition.scale`), also gilt auf der ganzen abgeschlossenen
Einheitskreisscheibe alles bisher Bewiesene: absolute Konvergenz,
`Z = exp (…)` und damit `Z ≠ 0`.

Daraus folgt die **Analytizität**: die Potenzreihe hat
Konvergenzradius `≥ 1` (`one_le_radius_fugacitySeries`), stellt die
Cluster-Reihe auf der offenen Einheitskreisscheibe dar
(`hasFPowerSeriesOnBall_clusterSeries`), und die Cluster-Reihe — für
reelle Gewichte also `log Z` — ist dort analytisch
(`analyticOnNhd_clusterSeries`). Das ist die klassische Analytizität des
Drucks in der Aktivität, in der abstrakten Polymer-Fassung.

Kein `sorry` in dieser Datei.
-/

open Finset Filter Topology

open scoped ENNReal NNReal

set_option linter.style.openClassical false

open scoped Classical

namespace ClusterExpansion

variable {K : Type*} [RCLike K]
variable {ι : Type*} [DecidableEq ι] (P : PolymerSystem ι)

/-! ## Homogenität in der Fugazität -/

omit [DecidableEq ι] in
/-- **Homogenität der Ordnungssumme**: ein Tupel der Ordnung `n` hat
`n + 1` Einträge, also skaliert die Ordnungssumme mit `z^(n+1)`. -/
theorem clusterOrderSum_scale (w : ι → K) (z : K) (Λ : Finset ι) (n : ℕ) :
    clusterOrderSum P (fun γ => z * w γ) Λ n
      = z ^ (n + 1) * clusterOrderSum P w Λ n := by
  unfold clusterOrderSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  ring

omit [DecidableEq ι] in
/-- Dasselbe für das Reihenglied. -/
theorem clusterCoeff_scale (w : ι → K) (z : K) (Λ : Finset ι) (n : ℕ) :
    clusterCoeff P (fun γ => z * w γ) Λ n
      = z ^ (n + 1) * clusterCoeff P w Λ n := by
  unfold clusterCoeff
  rw [clusterOrderSum_scale, mul_div_assoc]

/-! ## Stabilität der Kotecký-Preiss-Bedingung -/

omit [DecidableEq ι] in
/-- Die Kotecký-Preiss-Bedingung überlebt das Herunterskalieren der
Gewichte: die Nachbarschaftssumme wird nur kleiner. -/
theorem KPCondition.scale {w : ι → K} {a : ι → ℝ} {Λ : Finset ι} {z : K}
    (hz : ‖z‖ ≤ 1) (h : KPCondition P w a Λ) :
    KPCondition P (fun γ => z * w γ) a Λ := by
  obtain ⟨hpos, hsum⟩ := h
  refine ⟨hpos, fun γ hγ => le_trans (Finset.sum_le_sum fun δ _ => ?_) (hsum γ hγ)⟩
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  exact mul_le_of_le_one_left (norm_nonneg _) hz

omit [DecidableEq ι] in
/-- Ebenso für die globale Bedingung. -/
theorem GlobalKPCondition.scale {w : ι → K} {a : ι → ℝ} {z : K}
    (hz : ‖z‖ ≤ 1) (h : GlobalKPCondition P w a) :
    GlobalKPCondition P (fun γ => z * w γ) a := by
  obtain ⟨hpos, hsum⟩ := h
  refine ⟨hpos, fun γ Λ => le_trans (Finset.sum_le_sum fun δ _ => ?_) (hsum γ Λ)⟩
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  exact mul_le_of_le_one_left (norm_nonneg _) hz

/-! ## Die Potenzreihe in der Fugazität -/

/-- Die Koeffizienten der Fugazitätsreihe: `z^0` trägt nicht bei (die
leere Konfiguration liefert `log 1 = 0`), und `z^(n+1)` trägt das
`n`-te Glied der Cluster-Reihe. -/
noncomputable def fugacityCoeff (w : ι → K) (Λ : Finset ι) : ℕ → K
  | 0 => 0
  | (n + 1) => clusterCoeff P w Λ n

omit [DecidableEq ι] in
@[simp]
theorem fugacityCoeff_zero (w : ι → K) (Λ : Finset ι) :
    fugacityCoeff P w Λ 0 = 0 := rfl

omit [DecidableEq ι] in
@[simp]
theorem fugacityCoeff_succ (w : ι → K) (Λ : Finset ι) (n : ℕ) :
    fugacityCoeff P w Λ (n + 1) = clusterCoeff P w Λ n := rfl

omit [DecidableEq ι] in
/-- Das `(n+1)`-te Glied der Potenzreihe ist das `n`-te Glied der
Cluster-Reihe zu den skalierten Gewichten. -/
theorem fugacityCoeff_mul_pow (w : ι → K) (Λ : Finset ι) (z : K) (n : ℕ) :
    fugacityCoeff P w Λ (n + 1) * z ^ (n + 1)
      = clusterCoeff P (fun γ => z * w γ) Λ n := by
  rw [fugacityCoeff_succ, clusterCoeff_scale]
  ring

omit [DecidableEq ι] in
/-- Absolute Summierbarkeit der Fugazitätskoeffizienten unter der
Kotecký-Preiss-Bedingung. -/
theorem summable_norm_fugacityCoeff_of_kp (w : ι → K) (a : ι → ℝ)
    (Λ : Finset ι) (hKP : KPCondition P w a Λ) :
    Summable fun n => ‖fugacityCoeff P w Λ n‖ := by
  refine (summable_nat_add_iff 1).mp ?_
  simpa only [fugacityCoeff_succ] using
    summable_abs_clusterCoeff_of_kp P w a Λ hKP

omit [DecidableEq ι] in
/-- **Die Fugazitätsreihe konvergiert gegen die Cluster-Reihe** der
skalierten Gewichte, für jede Fugazität in der abgeschlossenen
Einheitskreisscheibe. -/
theorem hasSum_fugacity_of_kp (w : ι → K) (a : ι → ℝ) (Λ : Finset ι)
    (hKP : KPCondition P w a Λ) (z : K) (hz : ‖z‖ ≤ 1) :
    HasSum (fun n => fugacityCoeff P w Λ n * z ^ n)
      (clusterSeries P (fun γ => z * w γ) Λ) := by
  have hKPz : KPCondition P (fun γ => z * w γ) a Λ :=
    KPCondition.scale P hz hKP
  have hsum : Summable fun n => clusterCoeff P (fun γ => z * w γ) Λ n :=
    (summable_abs_clusterCoeff_of_kp P (fun γ => z * w γ) a Λ hKPz).of_norm
  have h1 : HasSum (fun n => clusterCoeff P (fun γ => z * w γ) Λ n)
      (clusterSeries P (fun γ => z * w γ) Λ) := hsum.hasSum
  have hfun : (fun n => fugacityCoeff P w Λ (n + 1) * z ^ (n + 1))
      = fun n => clusterCoeff P (fun γ => z * w γ) Λ n :=
    funext fun n => fugacityCoeff_mul_pow P w Λ z n
  have h2 := (hasSum_nat_add_iff
    (f := fun n => fugacityCoeff P w Λ n * z ^ n) 1).mp (by rw [hfun]; exact h1)
  simpa using h2

omit [DecidableEq ι] in
/-- Die Cluster-Reihe der skalierten Gewichte als Potenzreihe in `z`. -/
theorem clusterSeries_scale_eq_tsum (w : ι → K) (a : ι → ℝ) (Λ : Finset ι)
    (hKP : KPCondition P w a Λ) (z : K) (hz : ‖z‖ ≤ 1) :
    clusterSeries P (fun γ => z * w γ) Λ
      = ∑' n, fugacityCoeff P w Λ n * z ^ n :=
  (hasSum_fugacity_of_kp P w a Λ hKP z hz).tsum_eq.symm

/-- **Die Zustandssumme als Exponential einer Potenzreihe**: auf der
abgeschlossenen Einheitskreisscheibe der Fugazität. Insbesondere hat `Z`
dort keine Nullstelle — das ist die Lee-Yang-freie Region, die die
Kotecký-Preiss-Bedingung liefert. -/
theorem exp_fugacity_eq_Z_of_kp (w : ι → K) (a : ι → ℝ) (Λ : Finset ι)
    (hKP : KPCondition P w a Λ) (z : K) (hz : ‖z‖ ≤ 1) :
    NormedSpace.exp (∑' n, fugacityCoeff P w Λ n * z ^ n)
      = Z P (fun γ => z * w γ) Λ := by
  rw [← clusterSeries_scale_eq_tsum P w a Λ hKP z hz]
  exact exp_clusterSeries_eq_Z_of_kp P (fun γ => z * w γ) a Λ
    (KPCondition.scale P hz hKP)

/-! ## Analytizität -/

/-- Die formale Potenzreihe der Fugazitätsentwicklung. -/
noncomputable def fugacitySeries (w : ι → K) (Λ : Finset ι) :
    FormalMultilinearSeries K K K :=
  FormalMultilinearSeries.ofScalars K (fugacityCoeff P w Λ)

omit [DecidableEq ι] in
/-- **Konvergenzradius mindestens `1`**: die Kotecký-Preiss-Bedingung
liefert absolute Summierbarkeit der Koeffizienten. -/
theorem one_le_radius_fugacitySeries (w : ι → K) (a : ι → ℝ) (Λ : Finset ι)
    (hKP : KPCondition P w a Λ) :
    (1 : ℝ≥0∞) ≤ (fugacitySeries P w Λ).radius := by
  have h := summable_norm_fugacityCoeff_of_kp P w a Λ hKP
  have := FormalMultilinearSeries.le_radius_of_summable_norm
    (r := 1) (fugacitySeries P w Λ) (by
      simpa [fugacitySeries, FormalMultilinearSeries.ofScalars_norm] using h)
  simpa using this

omit [DecidableEq ι] in
/-- **Die Fugazitätsentwicklung stellt die Cluster-Reihe dar**: auf der
offenen Einheitskreisscheibe ist `z ↦ clusterSeries (z · w)` die Summe
der Potenzreihe `fugacitySeries`. -/
theorem hasFPowerSeriesOnBall_clusterSeries (w : ι → K) (a : ι → ℝ)
    (Λ : Finset ι) (hKP : KPCondition P w a Λ) :
    HasFPowerSeriesOnBall
      (fun z : K => clusterSeries P (fun γ => z * w γ) Λ)
      (fugacitySeries P w Λ) 0 1 where
  r_le := one_le_radius_fugacitySeries P w a Λ hKP
  r_pos := one_pos
  hasSum := by
    intro y hy
    have hy1 : ‖y‖ ≤ 1 := by
      rw [mem_eball_zero_iff] at hy
      have : ‖y‖ₑ < 1 := hy
      rw [← ofReal_norm] at this
      have := (ENNReal.ofReal_lt_one).mp this
      exact this.le
    have h := hasSum_fugacity_of_kp P w a Λ hKP y hy1
    rw [zero_add]
    refine HasSum.congr_fun h ?_
    intro n
    rw [fugacitySeries, FormalMultilinearSeries.ofScalars_apply_eq,
      smul_eq_mul]

omit [DecidableEq ι] in
/-- **Analytizität der Cluster-Reihe in der Fugazität**: auf der offenen
Einheitskreisscheibe ist `z ↦ clusterSeries (z · w) Λ` analytisch. Für
reelle Gewichte ist das die Analytizität von `log Z` in der Aktivität;
für komplexe Gewichte die Holomorphie. -/
theorem analyticOnNhd_clusterSeries (w : ι → K) (a : ι → ℝ) (Λ : Finset ι)
    (hKP : KPCondition P w a Λ) :
    AnalyticOnNhd K (fun z : K => clusterSeries P (fun γ => z * w γ) Λ)
      (Metric.eball (0 : K) 1) :=
  (hasFPowerSeriesOnBall_clusterSeries P w a Λ hKP).analyticOnNhd

/-! ## Gleichmäßigkeit im Volumen -/

/-- **Die Volumendifferenzschranke, gleichmäßig in der Fugazität**: die
rechte Seite enthält `z` nicht mehr. Damit ist die Konvergenz gegen den
thermodynamischen Limes gleichmäßig auf der abgeschlossenen
Einheitskreisscheibe — die Voraussetzung, unter der sich Analytizität
auf den Limes vererbt. -/
theorem norm_clusterSeries_scale_sub_le_of_gkp (w : ι → K) (a : ι → ℝ)
    (hKP : GlobalKPCondition P w a) {z : K} (hz : ‖z‖ ≤ 1)
    {Λ Λ' : Finset ι} (hsub : Λ ⊆ Λ') :
    ‖clusterSeries P (fun γ => z * w γ) Λ'
        - clusterSeries P (fun γ => z * w γ) Λ‖
      ≤ ∑ γ ∈ Λ' \ Λ, ‖w γ‖ * Real.exp (a γ) := by
  refine le_trans (norm_clusterSeries_sub_le_of_gkp P (fun γ => z * w γ) a
    (GlobalKPCondition.scale P hz hKP) hsub) ?_
  refine Finset.sum_le_sum fun γ _ => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_left (norm_nonneg _) hz) (Real.exp_pos _).le

/-- **Analytizität von `log Z` in der Aktivität**: für reelle Gewichte
ist der Druck auf `(−1, 1)` eine analytische Funktion der Fugazität. -/
theorem analyticOnNhd_log_Z (w : ι → ℝ) (a : ι → ℝ) (Λ : Finset ι)
    (hKP : KPCondition P w a Λ) :
    AnalyticOnNhd ℝ (fun z : ℝ => Real.log (Z P (fun γ => z * w γ) Λ))
      (Metric.eball (0 : ℝ) 1) := by
  refine AnalyticOnNhd.congr Metric.isOpen_eball
    (analyticOnNhd_clusterSeries P w a Λ hKP) fun z hz => ?_
  have hz1 : ‖z‖ ≤ 1 := by
    rw [mem_eball_zero_iff] at hz
    have h : ‖z‖ₑ < 1 := hz
    rw [← ofReal_norm] at h
    exact (ENNReal.ofReal_lt_one.mp h).le
  exact (log_Z_eq_clusterSeries_of_kp P (fun γ => z * w γ) a Λ
    (KPCondition.scale P hz1 hKP)).symm

end ClusterExpansion
