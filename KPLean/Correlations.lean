/-
Copyright (c) 2026 Dennis Michael Heine. All rights reserved.
Released under the CC BY-NC-SA 4.0 license as described in the file LICENSE.
Authors: Dennis Michael Heine
-/
import KPLean.LimitAnalyticity

/-!
# Ableitungen des Drucks: die Korrelationsfunktionen

Die Fugazitätsentwicklung macht den Druck zu einer analytischen Funktion
von `z`. Ihre Ableitungen sind die thermodynamisch interessanten Größen:
`z ∂_z log Z` ist die mittlere Polymerdichte, die höheren Ableitungen
sind die Korrelationsfunktionen. Diese Datei zieht daraus, was ohne
weitere Arbeit folgt.

* **Erste Ableitung im Ursprung** (`deriv_clusterSeries_scale_zero`):
  `∂_z log Z(z·w)|_{z=0} = ∑_{γ ∈ Λ} w γ` — der Druck beginnt in
  erster Ordnung mit der Gesamtaktivität. Das ist zugleich eine
  Kontrollrechnung: die Entwicklung ist die Taylorreihe des Drucks, und
  ihr erstes Glied ist das, was man erwartet.

* **Alle Ableitungen sind analytisch** in endlichem Volumen
  (`analyticOnNhd_deriv_clusterSeries`,
  `analyticOnNhd_iterated_deriv_clusterSeries`).

* **Konvergenz der Korrelationsfunktionen**
  (`tendstoLocallyUniformlyOn_deriv_clusterSeries`): die Ableitungen in
  endlichem Volumen konvergieren lokal gleichmäßig gegen die Ableitung
  des thermodynamischen Limes, und dieser ist selbst analytisch
  (`analyticOnNhd_deriv_clusterLimit`). Das ist der Satz von Weierstraß
  in seiner zweiten Hälfte: aus gleichmäßiger Konvergenz der Funktionen
  folgt lokal gleichmäßige Konvergenz der Ableitungen.

Kein `sorry` in dieser Datei.
-/

open Finset Filter Topology

open scoped ENNReal NNReal

set_option linter.style.openClassical false

open scoped Classical

namespace ClusterExpansion

variable {K : Type*} [RCLike K]
variable {ι : Type*} [DecidableEq ι] (P : PolymerSystem ι)

/-! ## Die Potenzreihe am Ursprung -/

omit [DecidableEq ι] in
/-- Die Fugazitätsentwicklung als Potenzreihe **im Punkt** `0`. -/
theorem hasFPowerSeriesAt_clusterSeries (w : ι → K) (a : ι → ℝ)
    (Λ : Finset ι) (hKP : KPCondition P w a Λ) :
    HasFPowerSeriesAt (fun z : K => clusterSeries P (fun γ => z * w γ) Λ)
      (fugacitySeries P w Λ) 0 :=
  ⟨1, hasFPowerSeriesOnBall_clusterSeries P w a Λ hKP⟩

omit [DecidableEq ι] in
/-- **Die erste Ableitung im Ursprung ist die Gesamtaktivität**:
`∂_z log Z(z·w)|_{z=0} = ∑_{γ ∈ Λ} w γ`.

In erster Ordnung ist der Druck die Summe der Gewichte — jedes Polymer
zählt einmal, Wechselwirkungen kommen erst in zweiter Ordnung. Das ist
die Probe darauf, dass die Cluster-Entwicklung wirklich die Taylorreihe
des Drucks ist. -/
theorem deriv_clusterSeries_scale_zero (w : ι → K) (a : ι → ℝ)
    (Λ : Finset ι) (hKP : KPCondition P w a Λ) :
    deriv (fun z : K => clusterSeries P (fun γ => z * w γ) Λ) 0
      = ∑ γ ∈ Λ, w γ := by
  rw [(hasFPowerSeriesAt_clusterSeries P w a Λ hKP).deriv, fugacitySeries,
    FormalMultilinearSeries.ofScalars_apply_eq, pow_one, smul_eq_mul,
    mul_one, fugacityCoeff_succ]
  unfold clusterCoeff
  rw [clusterOrderSum_zero]
  simp

/-! ## Analytizität der Ableitungen in endlichem Volumen -/

omit [DecidableEq ι] in
/-- Die Ableitung des Drucks ist auf der Einheitskreisscheibe wieder
analytisch. -/
theorem analyticOnNhd_deriv_clusterSeries (w : ι → K) (a : ι → ℝ)
    (Λ : Finset ι) (hKP : KPCondition P w a Λ) :
    AnalyticOnNhd K
      (deriv fun z : K => clusterSeries P (fun γ => z * w γ) Λ)
      (Metric.eball (0 : K) 1) :=
  (analyticOnNhd_clusterSeries P w a Λ hKP).deriv_of_isOpen
    Metric.isOpen_eball

omit [DecidableEq ι] in
/-- Ebenso alle höheren Ableitungen — die Korrelationsfunktionen jeder
Ordnung sind analytisch in der Fugazität. -/
theorem analyticOnNhd_iterated_deriv_clusterSeries (w : ι → K) (a : ι → ℝ)
    (Λ : Finset ι) (hKP : KPCondition P w a Λ) (n : ℕ) :
    AnalyticOnNhd K
      (deriv^[n] fun z : K => clusterSeries P (fun γ => z * w γ) Λ)
      (Metric.eball (0 : K) 1) :=
  (analyticOnNhd_clusterSeries P w a Λ hKP).iterated_deriv n

/-! ## Konvergenz der Korrelationsfunktionen -/

omit [DecidableEq ι] in
/-- **Die Ableitungen konvergieren mit**: die Korrelationsfunktionen in
endlichem Volumen konvergieren lokal gleichmäßig auf der
Einheitskreisscheibe gegen die Ableitung des thermodynamischen Limes.

Das ist die zweite Hälfte des Weierstraßschen Konvergenzsatzes und der
Grund, warum die gleichmäßige Konvergenz aus
`tendstoUniformlyOn_clusterSeries` mehr wert ist als bloße punktweise:
sie überträgt sich auf jede Ableitungsordnung. -/
theorem tendstoLocallyUniformlyOn_deriv_clusterSeries (w : ι → ℂ)
    (a : ι → ℝ) (hKP : GlobalKPCondition P w a)
    (hsum : Summable fun γ => ‖w γ‖ * Real.exp (a γ)) :
    TendstoLocallyUniformlyOn
      (deriv ∘ fun (Λ : Finset ι) (z : ℂ) =>
        clusterSeries P (fun γ => z * w γ) Λ)
      (deriv (clusterLimit P w)) atTop (Metric.eball (0 : ℂ) 1) := by
  have hU : IsOpen (Metric.eball (0 : ℂ) 1) := Metric.isOpen_eball
  have hdiff : ∀ Λ : Finset ι, DifferentiableOn ℂ
      (fun z : ℂ => clusterSeries P (fun γ => z * w γ) Λ)
      (Metric.eball (0 : ℂ) 1) := fun Λ =>
    (analyticOnNhd_clusterSeries P w a Λ (hKP.toKP P Λ)).differentiableOn
  exact (tendstoUniformlyOn_clusterSeries P w a hKP hsum).tendstoLocallyUniformlyOn.deriv
    (Filter.Eventually.of_forall hdiff) hU

omit [DecidableEq ι] in
/-- Die Korrelationsfunktion im thermodynamischen Limes ist analytisch. -/
theorem analyticOnNhd_deriv_clusterLimit (w : ι → ℂ) (a : ι → ℝ)
    (hKP : GlobalKPCondition P w a)
    (hsum : Summable fun γ => ‖w γ‖ * Real.exp (a γ)) :
    AnalyticOnNhd ℂ (deriv (clusterLimit P w)) (Metric.eball (0 : ℂ) 1) :=
  (analyticOnNhd_clusterLimit P w a hKP hsum).deriv_of_isOpen
    Metric.isOpen_eball

omit [DecidableEq ι] in
/-- Und ebenso jede höhere Ableitung im Limes. -/
theorem analyticOnNhd_iterated_deriv_clusterLimit (w : ι → ℂ) (a : ι → ℝ)
    (hKP : GlobalKPCondition P w a)
    (hsum : Summable fun γ => ‖w γ‖ * Real.exp (a γ)) (n : ℕ) :
    AnalyticOnNhd ℂ (deriv^[n] (clusterLimit P w))
      (Metric.eball (0 : ℂ) 1) :=
  (analyticOnNhd_clusterLimit P w a hKP hsum).iterated_deriv n


/-! ## Die Cluster-Koeffizienten sind die Taylor-Koeffizienten -/

omit [DecidableEq ι] in
/-- **Die Cluster-Entwicklung ist die Taylorreihe des Drucks**: die
`n`-te Ableitung im Ursprung ist `n!` mal dem `n`-ten
Fugazitätskoeffizienten.

`deriv_clusterSeries_scale_zero` ist der Fall `n = 1`; hier steht die
Aussage für jede Ordnung. Damit ist die Identifikation vollstaendig:
was die Kombinatorik als Cluster-Summe erzeugt, ist genau das, was die
Analysis als Taylor-Koeffizient aus dem Druck herausliest. -/
theorem iteratedDeriv_clusterSeries_scale_zero (w : ι → K) (a : ι → ℝ)
    (Λ : Finset ι) (hKP : KPCondition P w a Λ) (n : ℕ) :
    iteratedDeriv n (fun z : K => clusterSeries P (fun γ => z * w γ) Λ) 0
      = (Nat.factorial n : K) * fugacityCoeff P w Λ n := by
  have h := (hasFPowerSeriesOnBall_clusterSeries P w a Λ hKP).factorial_smul
    (y := 1) n
  rw [iteratedDeriv_eq_iteratedFDeriv, ← h, fugacitySeries,
    FormalMultilinearSeries.ofScalars_apply_eq, one_pow, smul_eq_mul,
    mul_one, nsmul_eq_mul]

omit [DecidableEq ι] in
/-- Dasselbe, mit dem Cluster-Koeffizienten ausgeschrieben: die
`(n+1)`-te Ableitung des Drucks im Ursprung ist `(n+1)!` mal dem
Glied der Ordnung `n` der Cluster-Reihe. -/
theorem iteratedDeriv_succ_clusterSeries_scale_zero (w : ι → K) (a : ι → ℝ)
    (Λ : Finset ι) (hKP : KPCondition P w a Λ) (n : ℕ) :
    iteratedDeriv (n + 1) (fun z : K => clusterSeries P (fun γ => z * w γ) Λ) 0
      = (Nat.factorial (n + 1) : K) * clusterCoeff P w Λ n := by
  rw [iteratedDeriv_clusterSeries_scale_zero P w a Λ hKP, fugacityCoeff_succ]

omit [DecidableEq ι] in
/-- Bei verschwindender Fugazität ist der Druck null — die leere
Konfiguration hat `Z = 1`. Das ist der Fall `n = 0`. -/
theorem clusterSeries_scale_zero (w : ι → K) (a : ι → ℝ) (Λ : Finset ι)
    (hKP : KPCondition P w a Λ) :
    clusterSeries P (fun γ => (0 : K) * w γ) Λ = 0 := by
  have h := iteratedDeriv_clusterSeries_scale_zero P w a Λ hKP 0
  rw [iteratedDeriv_zero, fugacityCoeff_zero, mul_zero] at h
  exact h

end ClusterExpansion
