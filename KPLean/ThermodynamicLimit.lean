/-
Copyright (c) 2026 Dennis Michael Heine. All rights reserved.
Released under the CC BY-NC-SA 4.0 license as described in the file LICENSE.
Authors: Dennis Michael Heine
-/
import KPLean.Locality

/-!
# Der thermodynamische Limes

Die Lokalitätsschranke `abs_clusterSeries_sub_erase_le_of_kp` kontrolliert
das Entfernen **eines** Polymers unabhängig vom Volumen. Aufsummiert
über die Differenzmenge wird daraus die **Volumendifferenzschranke**

`‖clusterSeries Λ' − clusterSeries Λ‖ ≤ ∑_{γ ∈ Λ' \ Λ} ‖w γ‖ · exp (a γ)`

für `Λ ⊆ Λ'` (`norm_clusterSeries_sub_le_of_gkp`). Ist die rechte Seite
über den ganzen Indextyp summierbar, so ist `Λ ↦ clusterSeries Λ` ein
Cauchy-Netz entlang `Finset.atTop`, und da `K` vollständig ist,
konvergiert es. Das ist der thermodynamische Limes in der abstrakten
Polymer-Fassung: die freie Energie existiert, und für reelle Gewichte ist
sie der Limes von `log Z`.

Die Voraussetzung ist die **globale** Kotecký-Preiss-Bedingung
(`GlobalKPCondition`): dieselbe Ungleichung wie bisher, aber gleichmäßig
in allen endlichen Volumina. Sie liefert `KPCondition` für jedes einzelne
Volumen (`GlobalKPCondition.toKP`), und damit greift die ganze bisherige
Maschinerie.

Kein `sorry` in dieser Datei.
-/

open Finset Filter Topology

set_option linter.style.openClassical false

open scoped Classical

namespace ClusterExpansion

variable {K : Type*} [RCLike K]
variable {ι : Type*} (P : PolymerSystem ι)

/-! ## Die globale Kotecký-Preiss-Bedingung -/

/-- Die **globale Kotecký-Preiss-Bedingung**: die Nachbarschaftssumme ist
gleichmäßig über alle endlichen Volumina durch `a γ` beschränkt. Für
jedes einzelne Volumen ist das die gewöhnliche Bedingung. -/
def GlobalKPCondition (w : ι → K) (a : ι → ℝ) : Prop :=
  (∀ γ, 0 ≤ a γ) ∧
  ∀ γ, ∀ Λ : Finset ι,
    ∑ δ ∈ Λ.filter (fun δ => P.incomp γ δ = true), ‖w δ‖ * Real.exp (a δ) ≤ a γ

/-- Die globale Bedingung liefert die gewöhnliche in jedem Volumen. -/
theorem GlobalKPCondition.toKP {w : ι → K} {a : ι → ℝ}
    (h : GlobalKPCondition P w a) (Λ : Finset ι) : KPCondition P w a Λ :=
  ⟨fun γ _ => h.1 γ, fun γ _ => h.2 γ Λ⟩

/-! ## Die Volumendifferenzschranke -/

/-- Hilfsschritt: die Schranke, nach der Kardinalität der
Differenzmenge induziert. -/
private theorem norm_clusterSeries_sub_le_aux (w : ι → K) (a : ι → ℝ)
    (hKP : GlobalKPCondition P w a) :
    ∀ (n : ℕ) (Λ Λ' : Finset ι), Λ ⊆ Λ' → (Λ' \ Λ).card = n →
      ‖clusterSeries P w Λ' - clusterSeries P w Λ‖
        ≤ ∑ γ ∈ Λ' \ Λ, ‖w γ‖ * Real.exp (a γ) := by
  intro n
  induction n with
  | zero =>
    intro Λ Λ' hsub hcard
    have hemp : Λ' \ Λ = ∅ := Finset.card_eq_zero.mp hcard
    have heq : Λ' = Λ := by
      refine Finset.Subset.antisymm (fun x hx => ?_) hsub
      by_contra hxn
      have : x ∈ Λ' \ Λ := Finset.mem_sdiff.mpr ⟨hx, hxn⟩
      rw [hemp] at this
      exact absurd this (Finset.notMem_empty x)
    rw [heq, sub_self, norm_zero, Finset.sdiff_self, Finset.sum_empty]
  | succ n ih =>
    intro Λ Λ' hsub hcard
    have hne : (Λ' \ Λ).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨γ₀, hγ₀⟩ := hne
    obtain ⟨hγ₀Λ', hγ₀Λ⟩ := Finset.mem_sdiff.mp hγ₀
    have hsub' : Λ ⊆ Λ'.erase γ₀ := fun x hx =>
      Finset.mem_erase.mpr ⟨fun h => hγ₀Λ (h ▸ hx), hsub hx⟩
    have hsd : (Λ'.erase γ₀) \ Λ = (Λ' \ Λ).erase γ₀ := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_erase]
      tauto
    have hcard' : ((Λ'.erase γ₀) \ Λ).card = n := by
      rw [hsd, Finset.card_erase_of_mem hγ₀, hcard]
      omega
    have hloc := abs_clusterSeries_sub_erase_le_of_kp P w a Λ' γ₀ hγ₀Λ'
      (hKP.toKP P Λ')
    calc ‖clusterSeries P w Λ' - clusterSeries P w Λ‖
        = ‖(clusterSeries P w Λ' - clusterSeries P w (Λ'.erase γ₀))
            + (clusterSeries P w (Λ'.erase γ₀) - clusterSeries P w Λ)‖ := by
          congr 1
          ring
      _ ≤ ‖clusterSeries P w Λ' - clusterSeries P w (Λ'.erase γ₀)‖
            + ‖clusterSeries P w (Λ'.erase γ₀) - clusterSeries P w Λ‖ :=
          norm_add_le _ _
      _ ≤ ‖w γ₀‖ * Real.exp (a γ₀)
            + ∑ γ ∈ (Λ' \ Λ).erase γ₀, ‖w γ‖ * Real.exp (a γ) := by
          refine add_le_add hloc ?_
          have := ih Λ (Λ'.erase γ₀) hsub' hcard'
          rwa [hsd] at this
      _ = ∑ γ ∈ Λ' \ Λ, ‖w γ‖ * Real.exp (a γ) :=
          Finset.add_sum_erase (Λ' \ Λ)
            (fun γ => ‖w γ‖ * Real.exp (a γ)) hγ₀

/-- **Die Volumendifferenzschranke**: vergrößert man das Volumen, so
ändert sich die Cluster-Reihe um höchstens die Gewichtssumme über die
hinzugekommenen Polymere — unabhängig von den beteiligten Volumina.
Das ist die aufsummierte Lokalitätsschranke. -/
theorem norm_clusterSeries_sub_le_of_gkp (w : ι → K) (a : ι → ℝ)
    (hKP : GlobalKPCondition P w a) {Λ Λ' : Finset ι} (hsub : Λ ⊆ Λ') :
    ‖clusterSeries P w Λ' - clusterSeries P w Λ‖
      ≤ ∑ γ ∈ Λ' \ Λ, ‖w γ‖ * Real.exp (a γ) :=
  norm_clusterSeries_sub_le_aux P w a hKP _ Λ Λ' hsub rfl

/-- Zwei beliebige Volumina, über ihren Schnitt verglichen. -/
theorem norm_clusterSeries_sub_le_of_gkp' (w : ι → K) (a : ι → ℝ)
    (hKP : GlobalKPCondition P w a) (Λ₁ Λ₂ : Finset ι) :
    ‖clusterSeries P w Λ₁ - clusterSeries P w Λ₂‖
      ≤ (∑ γ ∈ Λ₁ \ (Λ₁ ∩ Λ₂), ‖w γ‖ * Real.exp (a γ))
        + ∑ γ ∈ Λ₂ \ (Λ₁ ∩ Λ₂), ‖w γ‖ * Real.exp (a γ) := by
  have h1 := norm_clusterSeries_sub_le_of_gkp P w a hKP
    (Finset.inter_subset_left : Λ₁ ∩ Λ₂ ⊆ Λ₁)
  have h2 := norm_clusterSeries_sub_le_of_gkp P w a hKP
    (Finset.inter_subset_right : Λ₁ ∩ Λ₂ ⊆ Λ₂)
  calc ‖clusterSeries P w Λ₁ - clusterSeries P w Λ₂‖
      = ‖(clusterSeries P w Λ₁ - clusterSeries P w (Λ₁ ∩ Λ₂))
          - (clusterSeries P w Λ₂ - clusterSeries P w (Λ₁ ∩ Λ₂))‖ := by
        congr 1
        ring
    _ ≤ ‖clusterSeries P w Λ₁ - clusterSeries P w (Λ₁ ∩ Λ₂)‖
          + ‖clusterSeries P w Λ₂ - clusterSeries P w (Λ₁ ∩ Λ₂)‖ :=
        norm_sub_le _ _
    _ ≤ _ := add_le_add h1 h2

/-! ## Konvergenz -/

/-- Unter der globalen Kotecký-Preiss-Bedingung und Summierbarkeit der
Gewichtsschranke ist die Cluster-Reihe ein Cauchy-Netz in den Volumina. -/
theorem cauchySeq_clusterSeries_of_gkp (w : ι → K) (a : ι → ℝ)
    (hKP : GlobalKPCondition P w a)
    (hsum : Summable fun γ => ‖w γ‖ * Real.exp (a γ)) :
    CauchySeq fun Λ : Finset ι => clusterSeries P w Λ := by
  refine Metric.cauchySeq_iff'.mpr fun ε hε => ?_
  obtain ⟨Λ₀, hΛ₀⟩ := summable_iff_vanishing_norm.mp hsum ε hε
  refine ⟨Λ₀, fun Λ hΛ => ?_⟩
  have hsub : Λ₀ ⊆ Λ := hΛ
  have hdisj : Disjoint (Λ \ Λ₀) Λ₀ := Finset.sdiff_disjoint
  have hlt := hΛ₀ (Λ \ Λ₀) hdisj
  have hnn : ∀ γ, 0 ≤ ‖w γ‖ * Real.exp (a γ) := fun γ =>
    mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have habs : ‖∑ γ ∈ Λ \ Λ₀, ‖w γ‖ * Real.exp (a γ)‖
      = ∑ γ ∈ Λ \ Λ₀, ‖w γ‖ * Real.exp (a γ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun γ _ => hnn γ)]
  rw [dist_eq_norm]
  exact lt_of_le_of_lt (norm_clusterSeries_sub_le_of_gkp P w a hKP hsub)
    (habs ▸ hlt)

/-- **Der thermodynamische Limes der Cluster-Reihe**: unter der globalen
Kotecký-Preiss-Bedingung und Summierbarkeit der Gewichtsschranke
konvergiert `clusterSeries Λ`, wenn das Volumen den ganzen Indextyp
ausschöpft. Für komplexe wie für reelle Gewichte. -/
theorem exists_tendsto_clusterSeries_of_gkp (w : ι → K) (a : ι → ℝ)
    (hKP : GlobalKPCondition P w a)
    (hsum : Summable fun γ => ‖w γ‖ * Real.exp (a γ)) :
    ∃ L : K, Tendsto (fun Λ : Finset ι => clusterSeries P w Λ) atTop (𝓝 L) :=
  cauchySeq_tendsto_of_complete (cauchySeq_clusterSeries_of_gkp P w a hKP hsum)

/-- **Der thermodynamische Limes der freien Energie**: für reelle
Gewichte konvergiert `log Z Λ`. Der Limes ist zugleich der Limes der
Cluster-Reihe — die Entwicklung überlebt den Grenzübergang. -/
theorem exists_tendsto_log_Z_of_gkp (w : ι → ℝ) (a : ι → ℝ)
    (hKP : GlobalKPCondition P w a)
    (hsum : Summable fun γ => |w γ| * Real.exp (a γ)) :
    ∃ L : ℝ, Tendsto (fun Λ : Finset ι => Real.log (Z P w Λ)) atTop (𝓝 L) := by
  have hsum' : Summable fun γ => ‖w γ‖ * Real.exp (a γ) :=
    hsum.congr fun γ => by rw [Real.norm_eq_abs]
  obtain ⟨L, hL⟩ := exists_tendsto_clusterSeries_of_gkp P w a hKP hsum'
  refine ⟨L, hL.congr fun Λ => ?_⟩
  exact (log_Z_eq_clusterSeries_of_kp P w a Λ (hKP.toKP P Λ)).symm

/-! ## Schranken am Limes -/

/-- Der Limes erbt die volumenlineare Schranke: er ist durch die
Gesamtgewichtssumme beschränkt. -/
theorem norm_limit_le_of_gkp (w : ι → K) (a : ι → ℝ)
    (hKP : GlobalKPCondition P w a)
    (hsum : Summable fun γ => ‖w γ‖ * Real.exp (a γ))
    {L : K} (hL : Tendsto (fun Λ : Finset ι => clusterSeries P w Λ) atTop (𝓝 L)) :
    ‖L‖ ≤ ∑' γ, ‖w γ‖ * Real.exp (a γ) := by
  have hnn : ∀ γ, 0 ≤ ‖w γ‖ * Real.exp (a γ) := fun γ =>
    mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  refine le_of_tendsto (hL.norm) (Filter.Eventually.of_forall fun Λ => ?_)
  refine le_trans (abs_clusterSeries_le_of_kp P w a Λ (hKP.toKP P Λ)) ?_
  exact hsum.sum_le_tsum Λ (fun γ _ => hnn γ)

/-- **Lokalität am Limes**: der Abstand des Limes zur endlichen
Cluster-Reihe ist durch das Gewicht außerhalb des Volumens beschränkt.
Das ist die Fehlerschranke, mit der man in einer Renormierungsgruppen-
Rechnung ein endliches Volumen gegen den Limes eintauscht. -/
theorem norm_limit_sub_le_of_gkp (w : ι → K) (a : ι → ℝ)
    (hKP : GlobalKPCondition P w a)
    (hsum : Summable fun γ => ‖w γ‖ * Real.exp (a γ))
    {L : K} (hL : Tendsto (fun Λ : Finset ι => clusterSeries P w Λ) atTop (𝓝 L))
    (Λ : Finset ι) :
    ‖L - clusterSeries P w Λ‖
      ≤ (∑' γ, ‖w γ‖ * Real.exp (a γ)) - ∑ γ ∈ Λ, ‖w γ‖ * Real.exp (a γ) := by
  have hnn : ∀ γ, 0 ≤ ‖w γ‖ * Real.exp (a γ) := fun γ =>
    mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  refine le_of_tendsto ((hL.sub_const _).norm) ?_
  refine Filter.eventually_atTop.mpr ⟨Λ, fun Λ' hΛ' => ?_⟩
  have hsub : Λ ⊆ Λ' := hΛ'
  refine le_trans (norm_clusterSeries_sub_le_of_gkp P w a hKP hsub) ?_
  have hsplit : ∑ γ ∈ Λ' \ Λ, ‖w γ‖ * Real.exp (a γ)
      = (∑ γ ∈ Λ', ‖w γ‖ * Real.exp (a γ))
        - ∑ γ ∈ Λ, ‖w γ‖ * Real.exp (a γ) := by
    rw [eq_sub_iff_add_eq, Finset.sum_sdiff hsub]
  rw [hsplit]
  exact sub_le_sub_right (hsum.sum_le_tsum Λ' (fun γ _ => hnn γ)) _

end ClusterExpansion
