/-
Copyright (c) 2026 Dennis Michael Heine. All rights reserved.
Released under the CC BY-NC-SA 4.0 license as described in the file LICENSE.
Authors: Dennis Michael Heine
-/
import KPLean.SharpKP

/-!
# Die Exponentialformel unter der Kotecký-Preiss-Bedingung

Die Exponentialformel `log Z = clusterSeries` war bisher an das
Kleinheitsregime `e · ∑_Λ |w| < 1` gebunden, die scharfe
Summierbarkeitsschranke dagegen an die schwächere
Kotecký-Preiss-Bedingung. Diese Datei schließt die Lücke: da der Beweis
der Exponentialformel von der Kleinheit nur die absolute Konvergenz der
Reihe braucht, und die scharfe Schranke genau diese liefert, gilt

* `exp_clusterSeries_eq_Z_of_kp` : `Z = exp (clusterSeries)`,
* `Z_pos_of_kp` : `Z > 0` — schärfer als `Z_ne_zero_of_kp`,
* `log_Z_eq_clusterSeries_of_kp` : `log Z = clusterSeries`

allein unter der Kotecký-Preiss-Bedingung. Die Konvergenzschranke ist
`∑_{γ ∈ Λ} |w γ| · exp (a γ)` — dieselbe volumenlineare Größe, die
`abs_log_abs_Z_le_of_kp` schon als Schranke für `|log |Z||` liefert.
-/

open Finset

set_option linter.style.openClassical false

open scoped Classical

namespace ClusterExpansion

variable {K : Type*} [RCLike K]
variable {ι : Type*} (P : PolymerSystem ι)

/-- Der Beitrag einer Ordnung, nach dem Wert der ersten Koordinate
zerlegt: jedes Tupel ist bei genau einem Polymer verankert. -/
theorem abs_clusterOrderSum_le_sum_pinned (w : ι → K) (Λ : Finset ι)
    (n : ℕ) :
    ‖clusterOrderSum P w Λ n‖
      ≤ ∑ γ₀ ∈ Λ, pinnedOrderSum P w Λ γ₀ n := by
  have hmaps : ∀ γ ∈ Fintype.piFinset fun _ : Fin (n + 1) => Λ, γ 0 ∈ Λ :=
    fun γ hγ => Fintype.mem_piFinset.mp hγ 0
  calc ‖clusterOrderSum P w Λ n‖
      ≤ ∑ γ ∈ Fintype.piFinset fun _ : Fin (n + 1) => Λ,
          ‖(ursellInt P γ : K) * ∏ i, w (γ i)‖ :=
        norm_sum_le _ _
    _ = ∑ γ ∈ Fintype.piFinset fun _ : Fin (n + 1) => Λ,
          ‖(ursellInt P γ : K)‖ * ∏ i, ‖w (γ i)‖ :=
        Finset.sum_congr rfl fun γ _ => by rw [norm_mul, norm_prod]
    _ = ∑ γ₀ ∈ Λ, ∑ γ ∈ (Fintype.piFinset fun _ : Fin (n + 1) => Λ).filter
          (fun γ => γ 0 = γ₀), ‖(ursellInt P γ : K)‖ * ∏ i, ‖w (γ i)‖ :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm

/-- Eine Summe durch eine Konstante geteilt. -/
private theorem sum_div_eq {α : Type*} (s : Finset α) (f : α → ℝ) (c : ℝ) :
    (∑ x ∈ s, f x) / c = ∑ x ∈ s, f x / c := by
  rw [div_eq_mul_inv, Finset.sum_mul]
  exact Finset.sum_congr rfl fun x _ => (div_eq_mul_inv _ _).symm

/-- **Absolute Konvergenz der Cluster-Reihe unter der
Kotecký-Preiss-Bedingung**: die scharfe verankerte Schranke summiert
sich über die Anker zu `∑_{γ ∈ Λ} |w γ| · exp (a γ)`, und das ist
gerade die volumenlineare Schranke aus `abs_log_abs_Z_le_of_kp`. -/
theorem sum_range_abs_clusterCoeff_le_of_kp (w : ι → K) (a : ι → ℝ)
    (Λ : Finset ι) (hKP : KPCondition P w a Λ) (N : ℕ) :
    ∑ n ∈ Finset.range N, ‖clusterCoeff P w Λ n‖
      ≤ ∑ γ₀ ∈ Λ, ‖w γ₀‖ * Real.exp (a γ₀) := by
  have hstep : ∀ n ∈ Finset.range N, ‖clusterCoeff P w Λ n‖
      ≤ ∑ γ₀ ∈ Λ, pinnedOrderSum P w Λ γ₀ n / (Nat.factorial n : ℝ) := by
    intro n _
    have hfacpos : (0 : ℝ) < (Nat.factorial n : ℝ) := by positivity
    have hfacpos' : (0 : ℝ) < (Nat.factorial (n + 1) : ℝ) := by positivity
    have hfacle : (Nat.factorial n : ℝ) ≤ (Nat.factorial (n + 1) : ℝ) := by
      exact_mod_cast Nat.factorial_le (Nat.le_succ n)
    unfold clusterCoeff
    rw [norm_div, RCLike.norm_natCast]
    calc ‖clusterOrderSum P w Λ n‖ / (Nat.factorial (n + 1) : ℝ)
        ≤ ‖clusterOrderSum P w Λ n‖ / (Nat.factorial n : ℝ) :=
          div_le_div_of_nonneg_left (norm_nonneg _) hfacpos hfacle
      _ ≤ (∑ γ₀ ∈ Λ, pinnedOrderSum P w Λ γ₀ n) / (Nat.factorial n : ℝ) :=
          div_le_div_of_nonneg_right
            (abs_clusterOrderSum_le_sum_pinned P w Λ n) hfacpos.le
      _ = ∑ γ₀ ∈ Λ, pinnedOrderSum P w Λ γ₀ n / (Nat.factorial n : ℝ) :=
          sum_div_eq _ _ _
  calc ∑ n ∈ Finset.range N, ‖clusterCoeff P w Λ n‖
      ≤ ∑ n ∈ Finset.range N,
          ∑ γ₀ ∈ Λ, pinnedOrderSum P w Λ γ₀ n / (Nat.factorial n : ℝ) :=
        Finset.sum_le_sum hstep
    _ = ∑ γ₀ ∈ Λ, ∑ n ∈ Finset.range N,
          pinnedOrderSum P w Λ γ₀ n / (Nat.factorial n : ℝ) :=
        Finset.sum_comm
    _ ≤ ∑ γ₀ ∈ Λ, ‖w γ₀‖ * Real.exp (a γ₀) :=
        Finset.sum_le_sum fun γ₀ hγ₀ =>
          sum_range_pinned_le_of_kp P w a Λ γ₀ hγ₀ hKP N

/-- **Absolute Konvergenz der Cluster-Reihe unter der
Kotecký-Preiss-Bedingung**. -/
theorem summable_abs_clusterCoeff_of_kp (w : ι → K) (a : ι → ℝ)
    (Λ : Finset ι) (hKP : KPCondition P w a Λ) :
    Summable fun n => ‖clusterCoeff P w Λ n‖ :=
  summable_of_sum_range_le (fun _ => norm_nonneg _)
    (sum_range_abs_clusterCoeff_le_of_kp P w a Λ hKP)

/-- **Volumenlineare Schranke an die Cluster-Reihe** unter der
Kotecký-Preiss-Bedingung. -/
theorem abs_clusterSeries_le_of_kp (w : ι → K) (a : ι → ℝ) (Λ : Finset ι)
    (hKP : KPCondition P w a Λ) :
    ‖clusterSeries P w Λ‖ ≤ ∑ γ ∈ Λ, ‖w γ‖ * Real.exp (a γ) := by
  have habs := summable_abs_clusterCoeff_of_kp P w a Λ hKP
  have h1 : ‖clusterSeries P w Λ‖ ≤ ∑' n, ‖clusterCoeff P w Λ n‖ :=
    norm_tsum_le_tsum_norm (f := fun n => clusterCoeff P w Λ n) habs
  exact h1.trans (Real.tsum_le_of_sum_range_le (fun _ => norm_nonneg _)
    (sum_range_abs_clusterCoeff_le_of_kp P w a Λ hKP))

/-- **Die Exponentialformel unter der Kotecký-Preiss-Bedingung**: die
Kleinheitsvoraussetzung entfällt. Die Aussage gilt über jedem
`RCLike`-Körper, also für reelle wie für komplexe Gewichte. -/
theorem exp_clusterSeries_eq_Z_of_kp (w : ι → K) (a : ι → ℝ) (Λ : Finset ι)
    (hKP : KPCondition P w a Λ) :
    NormedSpace.exp (clusterSeries P w Λ) = Z P w Λ :=
  exp_clusterSeries_eq_Z P w Λ (summable_abs_clusterCoeff_of_kp P w a Λ hKP)

/-- Die Exponentialformel unter Kotecký-Preiss, reell. -/
theorem exp_clusterSeries_eq_Z_of_kp_real (w : ι → ℝ) (a : ι → ℝ)
    (Λ : Finset ι) (hKP : KPCondition P w a Λ) :
    Real.exp (clusterSeries P w Λ) = Z P w Λ := by
  rw [Real.exp_eq_exp_ℝ]
  exact exp_clusterSeries_eq_Z_of_kp P w a Λ hKP

/-- Die Exponentialformel unter Kotecký-Preiss, komplex. Hier gibt es
keinen Logarithmus mehr, wohl aber die Identität `Z = exp (…)` — und
damit insbesondere `Z ≠ 0`. -/
theorem exp_clusterSeries_eq_Z_of_kp_complex (w : ι → ℂ) (a : ι → ℝ)
    (Λ : Finset ι) (hKP : KPCondition P w a Λ) :
    Complex.exp (clusterSeries P w Λ) = Z P w Λ := by
  rw [Complex.exp_eq_exp_ℂ]
  exact exp_clusterSeries_eq_Z_of_kp P w a Λ hKP

/-- Unter der Kotecký-Preiss-Bedingung ist die Zustandssumme strikt
positiv — schärfer als das bloße Nichtverschwinden `Z_ne_zero_of_kp`. -/
theorem Z_pos_of_kp (w : ι → ℝ) (a : ι → ℝ) (Λ : Finset ι)
    (hKP : KPCondition P w a Λ) : 0 < Z P w Λ := by
  rw [← exp_clusterSeries_eq_Z_of_kp_real P w a Λ hKP]
  exact Real.exp_pos _

/-- **`log Z` ist die Cluster-Reihe, unter der
Kotecký-Preiss-Bedingung**. Damit schließt sich die Lücke zwischen der
Exponentialformel, die bisher Kleinheit verlangte, und der scharfen
Summierbarkeitsschranke: dieselbe Bedingung, unter der die klassischen
Kriterien `Z ≠ 0` liefern, macht die Cluster-Reihe zur exakten
Entwicklung von `log Z`. -/
theorem log_Z_eq_clusterSeries_of_kp (w : ι → ℝ) (a : ι → ℝ) (Λ : Finset ι)
    (hKP : KPCondition P w a Λ) :
    Real.log (Z P w Λ) = clusterSeries P w Λ := by
  rw [← exp_clusterSeries_eq_Z_of_kp_real P w a Λ hKP, Real.log_exp]

/-- **Volumenlineare Kontrolle des Logarithmus, aus der Reihe**: unter
der Kotecký-Preiss-Bedingung ist `|log Z Λ| ≤ ∑_{γ ∈ Λ} |w γ| · exp (a γ)`.
Dieselbe Schranke liefert `abs_log_abs_Z_le_of_kp` aus der
Teleskop-Induktion — hier fällt sie als Nebenprodukt der
Reihendarstellung ab, was beide Wege gegeneinander prüft. -/
theorem abs_log_Z_le_of_kp (w : ι → ℝ) (a : ι → ℝ) (Λ : Finset ι)
    (hKP : KPCondition P w a Λ) :
    |Real.log (Z P w Λ)| ≤ ∑ γ ∈ Λ, |w γ| * Real.exp (a γ) := by
  rw [log_Z_eq_clusterSeries_of_kp P w a Λ hKP]
  have h := abs_clusterSeries_le_of_kp P w a Λ hKP
  simpa only [Real.norm_eq_abs] using h

end ClusterExpansion
