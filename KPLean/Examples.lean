/-
Copyright (c) 2026 Dennis Michael Heine. All rights reserved.
Released under the CC BY-NC-SA 4.0 license as described in the file LICENSE.
Authors: Dennis Michael Heine
-/
import KPLean.LimitAnalyticity

/-!
# Beispiele und Gegenproben zur Leere

Sätze über eine unerfüllbare Voraussetzung sind wahr und wertlos. Diese
Datei zeigt an einem ausgeschriebenen Beispiel, dass die Voraussetzungen
der Hauptsätze erfüllbar sind, und prüft nebenbei, dass `Z` das ist, was
es sein soll.

Das Beispielsystem ist das **freie Polymersystem** `freeSystem`: nur ein
Polymer mit sich selbst ist unverträglich, sonst nichts. Dort ist jede
Teilmenge zulässig, also

`Z Λ = ∏_{γ ∈ Λ} (1 + w γ)`

(`Z_freeSystem`) — ein Ende-zu-Ende-Test der Definition von `Z`. Die
Kotecký-Preiss-Bedingung reduziert sich auf `‖w γ‖ · e ≤ 1`
(`globalKP_freeSystem`), und mit `w n = e⁻¹ · 2⁻ⁿ` auf `ℕ` ist die
Gewichtsschranke summierbar. Damit greifen alle Hauptsätze
nichtleer — der thermodynamische Limes existiert und die freie Energie
ist in der Fugazität analytisch (`example`s am Ende).

Kein `sorry` in dieser Datei.
-/

open Finset Filter Topology

set_option linter.style.openClassical false

open scoped Classical

namespace ClusterExpansion

/-! ## Das freie Polymersystem -/

/-- Das **freie Polymersystem**: unverträglich ist nur ein Polymer mit
sich selbst. Das ist die minimale zulässige Relation. -/
def freeSystem (ι : Type*) [DecidableEq ι] : PolymerSystem ι where
  incomp γ δ := decide (γ = δ)
  symm γ δ := by
    by_cases h : γ = δ
    · simp [h]
    · simp [h, Ne.symm h]
  refl γ := by simp

@[simp]
theorem freeSystem_incomp {ι : Type*} [DecidableEq ι] (γ δ : ι) :
    (freeSystem ι).incomp γ δ = decide (γ = δ) := rfl

/-- Im freien System ist jede Teilmenge zulässig. -/
theorem indep_freeSystem {ι : Type*} [DecidableEq ι] (S : Finset ι) :
    Indep (freeSystem ι) S := by
  intro γ _ δ _ hne
  simpa using hne

/-- **Ende-zu-Ende-Test der Zustandssumme**: im freien System ist `Z` das
Produkt `∏ (1 + w γ)`. Das ist die Zustandssumme, die man von Hand
ausrechnet, und sie kommt hier aus der allgemeinen Definition. -/
theorem Z_freeSystem {ι : Type*} [DecidableEq ι] {R : Type*} [CommRing R]
    (w : ι → R) (Λ : Finset ι) :
    Z (freeSystem ι) w Λ = ∏ γ ∈ Λ, (1 + w γ) := by
  unfold Z
  rw [Finset.filter_true_of_mem (fun S _ => indep_freeSystem S)]
  have h : ∏ γ ∈ Λ, (1 + w γ) = ∏ γ ∈ Λ, (w γ + 1) :=
    Finset.prod_congr rfl fun γ _ => add_comm _ _
  rw [h, Finset.prod_add]
  exact Finset.sum_congr rfl fun S _ => by
    rw [Finset.prod_const_one, mul_one]

/-! ## Die Kotecký-Preiss-Bedingung ist erfüllbar -/

/-- Im freien System reduziert sich die globale Kotecký-Preiss-Bedingung
auf `‖w γ‖ · e ≤ 1` — die Nachbarschaft eines Polymers besteht nur aus
ihm selbst. -/
theorem globalKP_freeSystem {ι : Type*} [DecidableEq ι] {K : Type*}
    [RCLike K] (w : ι → K) (hw : ∀ γ, ‖w γ‖ * Real.exp 1 ≤ 1) :
    GlobalKPCondition (freeSystem ι) w (fun _ => 1) := by
  refine ⟨fun _ => zero_le_one, fun γ Λ => ?_⟩
  have hsub : Λ.filter (fun δ => (freeSystem ι).incomp γ δ = true) ⊆ {γ} := by
    intro δ hδ
    obtain ⟨-, h⟩ := Finset.mem_filter.mp hδ
    rw [freeSystem_incomp, decide_eq_true_eq] at h
    simp [h]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_) ?_
  · exact fun δ _ _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  · rw [Finset.sum_singleton]
    exact hw γ

/-! ## Ein vollständiges, nichtleeres Beispiel -/

/-- Die Beispielgewichte auf `ℕ`: `w n = e⁻¹ · 2⁻ⁿ`, komplexwertig. -/
noncomputable def exampleWeight (n : ℕ) : ℂ :=
  (Real.exp 1)⁻¹ * (2 : ℂ)⁻¹ ^ n

theorem norm_exampleWeight (n : ℕ) :
    ‖exampleWeight n‖ = (Real.exp 1)⁻¹ * (2 : ℝ)⁻¹ ^ n := by
  unfold exampleWeight
  rw [norm_mul, norm_pow]
  congr 1
  · rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Real.exp_pos 1).le)]
  · rw [norm_inv, Complex.norm_ofNat]

/-- Die Beispielgewichte erfüllen die Kotecký-Preiss-Schranke. -/
theorem exampleWeight_bound (n : ℕ) :
    ‖exampleWeight n‖ * Real.exp 1 ≤ 1 := by
  rw [norm_exampleWeight]
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h2 : ((2 : ℝ)⁻¹) ^ n ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  calc (Real.exp 1)⁻¹ * (2 : ℝ)⁻¹ ^ n * Real.exp 1
      = (2 : ℝ)⁻¹ ^ n := by field_simp
    _ ≤ 1 := h2

/-- Das Beispielsystem erfüllt die globale Kotecký-Preiss-Bedingung. -/
theorem globalKP_example :
    GlobalKPCondition (freeSystem ℕ) exampleWeight (fun _ => 1) :=
  globalKP_freeSystem exampleWeight exampleWeight_bound

/-- Die Gewichtsschranke des Beispiels ist summierbar. -/
theorem summable_example :
    Summable fun n : ℕ => ‖exampleWeight n‖ * Real.exp 1 := by
  have hgeom : Summable fun n : ℕ => ((2 : ℝ)⁻¹) ^ n :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  refine hgeom.congr fun n => ?_
  rw [norm_exampleWeight]
  field_simp

/-! ## Die Hauptsätze, nichtleer angewandt -/

/-- Die Zustandssumme des Beispiels verschwindet in keinem Volumen. -/
example (Λ : Finset ℕ) : Z (freeSystem ℕ) exampleWeight Λ ≠ 0 :=
  Z_ne_zero_of_kp (freeSystem ℕ) exampleWeight (fun _ => 1) Λ
    (globalKP_example.toKP (freeSystem ℕ) Λ)

/-- Die Exponentialformel gilt für das Beispiel. -/
example (Λ : Finset ℕ) :
    Complex.exp (clusterSeries (freeSystem ℕ) exampleWeight Λ)
      = Z (freeSystem ℕ) exampleWeight Λ :=
  exp_clusterSeries_eq_Z_of_kp_complex (freeSystem ℕ) exampleWeight
    (fun _ => 1) Λ (globalKP_example.toKP (freeSystem ℕ) Λ)

/-- Der thermodynamische Limes des Beispiels existiert. -/
example : ∃ L : ℂ, Tendsto
    (fun Λ : Finset ℕ => clusterSeries (freeSystem ℕ) exampleWeight Λ)
    atTop (𝓝 L) :=
  exists_tendsto_clusterSeries_of_gkp (freeSystem ℕ) exampleWeight
    (fun _ => 1) globalKP_example summable_example

/-- Die freie Energie des Beispiels ist in der Fugazität analytisch. -/
example : AnalyticOnNhd ℂ (clusterLimit (freeSystem ℕ) exampleWeight)
    (Metric.eball (0 : ℂ) 1) :=
  analyticOnNhd_clusterLimit (freeSystem ℕ) exampleWeight (fun _ => 1)
    globalKP_example summable_example

end ClusterExpansion
