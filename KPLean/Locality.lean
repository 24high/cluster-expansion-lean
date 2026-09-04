/-
Copyright (c) 2026 Dennis Michael Heine. All rights reserved.
Released under the CC BY-NC-SA 4.0 license as described in the file LICENSE.
Authors: Dennis Michael Heine
-/
import KPLean.KPExponential
import KPLean.UrsellSymmetry

/-!
# Lokalität: das Entfernen eines Polymers

Wie stark ändert sich `log Z`, wenn ein einzelnes Polymer aus dem
Volumen genommen wird? Unter der Kotecký-Preiss-Bedingung höchstens um
`|w γ₀| · exp (a γ₀)` — unabhängig vom Volumen. Das ist die zweiseitige
Verschärfung der Quotientenschranke `Z_ratio_bound_of_kp` und die Form,
in der Abschneidefehler in Renormierungsgruppen-Argumenten kontrolliert
werden.

Der Beweis läuft über die Cluster-Reihe: die Differenz der Reihen für
`Λ` und `Λ ∖ {γ₀}` ist die Reihe über die Cluster, die `γ₀` verwenden,
und die wird von der verankerten Schranke `tsum_pinned_le_of_kp`
beherrscht. Der Übergang von „`γ₀` kommt irgendwo vor" zu „`γ₀` steht
an erster Stelle" kostet den Faktor `n + 1`, den die Fakultät gerade
schluckt.
-/

open Finset

set_option linter.style.openClassical false

open scoped Classical

namespace ClusterExpansion

variable {ι : Type*} (P : PolymerSystem ι)

/-- Die Kotecký-Preiss-Bedingung vererbt sich auf Teilmengen: die
Nachbarschaftssumme läuft über weniger nichtnegative Terme. -/
theorem KPCondition.mono {w : ι → ℝ} {a : ι → ℝ} {Λ' Λ : Finset ι}
    (hsub : Λ' ⊆ Λ) (h : KPCondition P w a Λ) : KPCondition P w a Λ' := by
  obtain ⟨hpos, hsum⟩ := h
  refine ⟨fun γ hγ => hpos γ (hsub hγ), fun γ hγ => ?_⟩
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset_filter _ hsub) ?_) (hsum γ (hsub hγ))
  exact fun δ _ _ => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le

/-- **Lokalitätsschranke**:
Entfernt man ein Polymer aus dem Volumen, so ändert sich die
Cluster-Reihe um höchstens `|w γ₀| · exp (a γ₀)` — unabhängig vom
Volumen. -/
theorem abs_clusterSeries_sub_erase_le_of_kp (w : ι → ℝ) (a : ι → ℝ)
    (Λ : Finset ι) (γ₀ : ι) (hγ₀ : γ₀ ∈ Λ) (hKP : KPCondition P w a Λ)
 :
    |clusterSeries P w Λ - clusterSeries P w (Λ.erase γ₀)|
      ≤ |w γ₀| * Real.exp (a γ₀) := by
  have hdiff : ∀ n : ℕ,
      |clusterOrderSum P w Λ n - clusterOrderSum P w (Λ.erase γ₀) n|
        ≤ ((n : ℝ) + 1) * pinnedOrderSum P w Λ γ₀ n :=
    fun n => abs_clusterOrderSum_sub_le P w Λ γ₀ n
  -- Termweise Schranke: der Faktor `n + 1` kürzt die Fakultät zu `n!`.
  have hd : ∀ n : ℕ,
      |clusterCoeff P w Λ n - clusterCoeff P w (Λ.erase γ₀) n|
        ≤ pinnedOrderSum P w Λ γ₀ n / (Nat.factorial n : ℝ) := by
    intro n
    have hfacpos : (0 : ℝ) < (Nat.factorial (n + 1) : ℝ) := by positivity
    have hfac : (Nat.factorial (n + 1) : ℝ) = ((n : ℝ) + 1) * Nat.factorial n := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    unfold clusterCoeff
    rw [div_sub_div_same, abs_div, abs_of_pos hfacpos]
    calc |clusterOrderSum P w Λ n - clusterOrderSum P w (Λ.erase γ₀) n|
          / (Nat.factorial (n + 1) : ℝ)
        ≤ (((n : ℝ) + 1) * pinnedOrderSum P w Λ γ₀ n)
            / (Nat.factorial (n + 1) : ℝ) :=
          div_le_div_of_nonneg_right (hdiff n) hfacpos.le
      _ = pinnedOrderSum P w Λ γ₀ n / (Nat.factorial n : ℝ) := by
          rw [hfac]
          have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
          have hnf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
          field_simp
  -- Summierbarkeit der Differenzfolge.
  have hpin := summable_pinned_of_kp P w a Λ γ₀ hγ₀ hKP
  have hsumd : Summable fun n =>
      |clusterCoeff P w Λ n - clusterCoeff P w (Λ.erase γ₀) n| :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) hd hpin
  have h1 : Summable fun n => clusterCoeff P w Λ n :=
    (summable_abs_clusterCoeff_of_kp P w a Λ hKP).of_abs
  have h2 : Summable fun n => clusterCoeff P w (Λ.erase γ₀) n :=
    (summable_abs_clusterCoeff_of_kp P w a (Λ.erase γ₀)
      (KPCondition.mono P (Finset.erase_subset γ₀ Λ) hKP)).of_abs
  -- Die Differenz der Reihen ist die Reihe der Differenzen.
  have hseries : clusterSeries P w Λ - clusterSeries P w (Λ.erase γ₀)
      = ∑' n, (clusterCoeff P w Λ n - clusterCoeff P w (Λ.erase γ₀) n) := by
    unfold clusterSeries
    exact (h1.tsum_sub h2).symm
  rw [hseries]
  calc |∑' n, (clusterCoeff P w Λ n - clusterCoeff P w (Λ.erase γ₀) n)|
      ≤ ∑' n, |clusterCoeff P w Λ n - clusterCoeff P w (Λ.erase γ₀) n| := by
        have hn := norm_tsum_le_tsum_norm
          (f := fun n => clusterCoeff P w Λ n - clusterCoeff P w (Λ.erase γ₀) n)
          (by simpa [Real.norm_eq_abs] using hsumd)
        simpa [Real.norm_eq_abs] using hn
    _ ≤ ∑' n, pinnedOrderSum P w Λ γ₀ n / (Nat.factorial n : ℝ) :=
        Summable.tsum_le_tsum hd hsumd hpin
    _ ≤ |w γ₀| * Real.exp (a γ₀) := tsum_pinned_le_of_kp P w a Λ γ₀ hγ₀ hKP

/-- **Lokalität von `log Z`**: das Entfernen eines Polymers ändert `log Z` um höchstens
`|w γ₀| · exp (a γ₀)`, unabhängig vom Volumen. Das ist die zweiseitige
Verschärfung der Quotientenschranke `Z_ratio_bound_of_kp`. -/
theorem abs_log_Z_sub_erase_le_of_kp (w : ι → ℝ) (a : ι → ℝ) (Λ : Finset ι)
    (γ₀ : ι) (hγ₀ : γ₀ ∈ Λ) (hKP : KPCondition P w a Λ)
 :
    |Real.log (Z P w Λ) - Real.log (Z P w (Λ.erase γ₀))|
      ≤ |w γ₀| * Real.exp (a γ₀) := by
  rw [log_Z_eq_clusterSeries_of_kp P w a Λ hKP,
    log_Z_eq_clusterSeries_of_kp P w a (Λ.erase γ₀)
      (KPCondition.mono P (Finset.erase_subset γ₀ Λ) hKP)]
  exact abs_clusterSeries_sub_erase_le_of_kp P w a Λ γ₀ hγ₀ hKP

end ClusterExpansion
