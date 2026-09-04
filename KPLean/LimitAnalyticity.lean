/-
Copyright (c) 2026 Dennis Michael Heine. All rights reserved.
Released under the CC BY-NC-SA 4.0 license as described in the file LICENSE.
Authors: Dennis Michael Heine
-/
import KPLean.Fugacity
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Analytizität der freien Energie im thermodynamischen Limes

In endlichem Volumen ist die Cluster-Reihe eine Potenzreihe in der
Fugazität mit Konvergenzradius `≥ 1` (`KPLean/Fugacity.lean`). Die
Schranke `1` hängt **nicht vom Volumen ab**, und die
Volumendifferenzschranke ist ebenfalls gleichmäßig in `z`
(`norm_clusterSeries_scale_sub_le_of_gkp`). Also konvergiert die
Cluster-Reihe **gleichmäßig auf der Kreisscheibe** gegen ihren
thermodynamischen Limes.

Nach dem Weierstraßschen Konvergenzsatz — in Mathlib
`TendstoLocallyUniformlyOn.differentiableOn` — ist der Limes damit
holomorph, also analytisch:

`AnalyticOnNhd ℂ (clusterLimit P w) (eball 0 1)`

(`analyticOnNhd_clusterLimit`). Das ist die Analytizität des Drucks im
unendlichen Volumen: im Kotecký-Preiss-Regime gibt es keinen
Phasenübergang in der Fugazität.

Die Aussage ist komplex, nicht reell: der Weierstraßsche Satz ist ein
Satz der Funktionentheorie. Für reelle Gewichte liest man sie auf der
reellen Achse ab.

Kein `sorry` in dieser Datei.
-/

open Finset Filter Topology Metric

open scoped ENNReal NNReal

set_option linter.style.openClassical false

open scoped Classical

namespace ClusterExpansion

variable {ι : Type*} [DecidableEq ι] (P : PolymerSystem ι)

/-! ## Die skalierte Gewichtsschranke -/

omit [DecidableEq ι] in
/-- Skalieren mit `‖z‖ ≤ 1` erhält die Summierbarkeit der
Gewichtsschranke, und zwar mit derselben Majorante. -/
theorem summable_scale_weight {w : ι → ℂ} {a : ι → ℝ}
    (hsum : Summable fun γ => ‖w γ‖ * Real.exp (a γ)) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Summable fun γ => ‖z * w γ‖ * Real.exp (a γ) := by
  refine Summable.of_nonneg_of_le
    (fun γ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) (fun γ => ?_) hsum
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_left (norm_nonneg _) hz) (Real.exp_pos _).le

/-! ## Die Grenzfunktion -/

/-- Die freie Energie im thermodynamischen Limes, als Funktion der
Fugazität. Außerhalb des Konvergenzbereichs ist der Wert bedeutungslos
(`limUnder` liefert dort irgendetwas); innerhalb der abgeschlossenen
Einheitskreisscheibe ist er der Limes (`tendsto_clusterLimit`). -/
noncomputable def clusterLimit (w : ι → ℂ) (z : ℂ) : ℂ :=
  limUnder atTop fun Λ : Finset ι => clusterSeries P (fun γ => z * w γ) Λ

omit [DecidableEq ι] in
/-- Auf der abgeschlossenen Einheitskreisscheibe ist `clusterLimit`
tatsächlich der Limes der endlichen Cluster-Reihen. -/
theorem tendsto_clusterLimit (w : ι → ℂ) (a : ι → ℝ)
    (hKP : GlobalKPCondition P w a)
    (hsum : Summable fun γ => ‖w γ‖ * Real.exp (a γ)) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Tendsto (fun Λ : Finset ι => clusterSeries P (fun γ => z * w γ) Λ) atTop
      (𝓝 (clusterLimit P w z)) := by
  obtain ⟨L, hL⟩ := exists_tendsto_clusterSeries_of_gkp P (fun γ => z * w γ) a
    (GlobalKPCondition.scale P hz hKP) (summable_scale_weight hsum hz)
  rw [clusterLimit, hL.limUnder_eq]
  exact hL

omit [DecidableEq ι] in
/-- **Die Restgliedschranke, gleichmäßig in der Fugazität**: der Abstand
zwischen endlichem Volumen und Limes ist durch den Schwanz der
Gewichtssumme beschränkt, und diese Schranke enthält `z` nicht. -/
theorem norm_clusterLimit_sub_le (w : ι → ℂ) (a : ι → ℝ)
    (hKP : GlobalKPCondition P w a)
    (hsum : Summable fun γ => ‖w γ‖ * Real.exp (a γ)) {z : ℂ} (hz : ‖z‖ ≤ 1)
    (Λ : Finset ι) :
    ‖clusterLimit P w z - clusterSeries P (fun γ => z * w γ) Λ‖
      ≤ (∑' γ, ‖w γ‖ * Real.exp (a γ)) - ∑ γ ∈ Λ, ‖w γ‖ * Real.exp (a γ) := by
  have hnn : ∀ γ, 0 ≤ ‖w γ‖ * Real.exp (a γ) := fun γ =>
    mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hL := tendsto_clusterLimit P w a hKP hsum hz
  refine le_of_tendsto ((hL.sub_const _).norm) ?_
  refine Filter.eventually_atTop.mpr ⟨Λ, fun Λ' hΛ' => ?_⟩
  have hsub : Λ ⊆ Λ' := hΛ'
  refine le_trans
    (norm_clusterSeries_scale_sub_le_of_gkp P w a hKP hz hsub) ?_
  have hsplit : ∑ γ ∈ Λ' \ Λ, ‖w γ‖ * Real.exp (a γ)
      = (∑ γ ∈ Λ', ‖w γ‖ * Real.exp (a γ))
        - ∑ γ ∈ Λ, ‖w γ‖ * Real.exp (a γ) := by
    rw [eq_sub_iff_add_eq, Finset.sum_sdiff hsub]
  rw [hsplit]
  exact sub_le_sub_right (hsum.sum_le_tsum Λ' (fun γ _ => hnn γ)) _

/-! ## Gleichmäßige Konvergenz und Analytizität -/

omit [DecidableEq ι] in
/-- **Gleichmäßige Konvergenz auf der Kreisscheibe**: das ist der Punkt,
an dem die Volumenunabhängigkeit der Kotecký-Preiss-Schranken bezahlt
macht. -/
theorem tendstoUniformlyOn_clusterSeries (w : ι → ℂ) (a : ι → ℝ)
    (hKP : GlobalKPCondition P w a)
    (hsum : Summable fun γ => ‖w γ‖ * Real.exp (a γ)) :
    TendstoUniformlyOn
      (fun (Λ : Finset ι) (z : ℂ) => clusterSeries P (fun γ => z * w γ) Λ)
      (clusterLimit P w) atTop (Metric.eball (0 : ℂ) 1) := by
  refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε => ?_
  -- Der Schwanz der Gewichtssumme geht gegen null.
  have htail : Tendsto
      (fun Λ : Finset ι =>
        (∑' γ, ‖w γ‖ * Real.exp (a γ)) - ∑ γ ∈ Λ, ‖w γ‖ * Real.exp (a γ))
      atTop (𝓝 0) := by
    have h := hsum.hasSum
    have := (tendsto_const_nhds (x := ∑' γ, ‖w γ‖ * Real.exp (a γ))
      (f := (atTop : Filter (Finset ι)))).sub h
    simpa using this
  have hev := htail.eventually (gt_mem_nhds hε)
  filter_upwards [hev] with Λ hΛ z hz
  have hz1 : ‖z‖ ≤ 1 := by
    rw [mem_eball_zero_iff] at hz
    have h : ‖z‖ₑ < 1 := hz
    rw [← ofReal_norm] at h
    exact (ENNReal.ofReal_lt_one.mp h).le
  rw [dist_eq_norm]
  exact lt_of_le_of_lt
    (norm_clusterLimit_sub_le P w a hKP hsum hz1 Λ) hΛ

omit [DecidableEq ι] in
/-- **Analytizität der freien Energie im thermodynamischen Limes**: der
Grenzwert der Cluster-Reihen ist auf der offenen Einheitskreisscheibe
der Fugazität analytisch. Im Kotecký-Preiss-Regime ist der Druck also
eine analytische Funktion der Aktivität — kein Phasenübergang.

Der Beweis ist der Weierstraßsche Konvergenzsatz: jede endliche
Cluster-Reihe ist dort holomorph (`analyticOnNhd_clusterSeries`), die
Konvergenz ist gleichmäßig, also ist der Limes holomorph und damit
analytisch. -/
theorem analyticOnNhd_clusterLimit (w : ι → ℂ) (a : ι → ℝ)
    (hKP : GlobalKPCondition P w a)
    (hsum : Summable fun γ => ‖w γ‖ * Real.exp (a γ)) :
    AnalyticOnNhd ℂ (clusterLimit P w) (Metric.eball (0 : ℂ) 1) := by
  have hU : IsOpen (Metric.eball (0 : ℂ) 1) := Metric.isOpen_eball
  have hdiff : ∀ Λ : Finset ι, DifferentiableOn ℂ
      (fun z : ℂ => clusterSeries P (fun γ => z * w γ) Λ)
      (Metric.eball (0 : ℂ) 1) := fun Λ =>
    (analyticOnNhd_clusterSeries P w a Λ (hKP.toKP P Λ)).differentiableOn
  have hlim := (tendstoUniformlyOn_clusterSeries P w a hKP
    hsum).tendstoLocallyUniformlyOn
  exact (hlim.differentiableOn (Filter.Eventually.of_forall hdiff) hU).analyticOnNhd hU

end ClusterExpansion
