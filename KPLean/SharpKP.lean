/-
Copyright (c) 2026 Dennis Michael Heine. All rights reserved.
Released under the CC BY-NC-SA 4.0 license as described in the file LICENSE.
Authors: Dennis Michael Heine
-/
import KPLean.TreePeel
import KPLean.TreeRelabel
import KPLean.TreeLink

/-!
# Die scharfe Kotecký-Preiss-Summierbarkeitsschranke

Aus der Zerlegung an der Wurzel, der Umbenennungsinvarianz und der
Multinomialzählung folgt die Rekursionsungleichung für die
Baumkoeffizienten; die Kotecký-Preiss-Bedingung macht daraus per
Induktion über die Abschneidehöhe die Schranke `exp (a γ)`. Zusammen mit
der Baumgraphen-Schranke ergibt das die verankerte Summierbarkeit
`|w γ₀| · exp (a γ₀)` — gleichmäßig im Volumen und ohne
Kleinheitsvoraussetzung.
-/

open Finset

set_option linter.style.openClassical false

open scoped Classical

namespace ClusterExpansion

variable {ι J : Type*} [DecidableEq ι] [DecidableEq J] [Fintype J]
variable (P : PolymerSystem ι)

/-! ## Die Rekursionsungleichung

Zerlegung an der Wurzel und Umbenennungsinvarianz zusammen mit der
Multinomialzählung `sum_partitionsOf_card` ergeben die
Rekursionsungleichung, die die Kotecký-Preiss-Induktion antreibt. -/


/-- Das Blockfunktional der Rekursion: der Beitrag eines Blocks der
Größe `m`, in dem jeder seiner `m` Knoten die Wurzel des Teilbaums sein
kann. -/
noncomputable def blockTerm (w : ι → ℝ) (Λ : Finset ι) (γ₀ : ι) (m : ℕ) : ℝ :=
  (m : ℝ) * ∑ δ ∈ incompNbhd P Λ γ₀, |w δ| * treeCoeff P w Λ δ (m - 1)

omit [DecidableEq ι] [DecidableEq J] [Fintype J] in
/-- Normiert ist das Blockfunktional genau der Nachbarterm. -/
theorem blockTerm_div (w : ι → ℝ) (Λ : Finset ι) (γ₀ : ι) {m : ℕ}
    (hm : m ≠ 0) :
    blockTerm P w Λ γ₀ m / (Nat.factorial m : ℝ) = nbhdTerm P w Λ γ₀ m := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  unfold blockTerm nbhdTerm
  rw [Nat.factorial_succ, Nat.add_sub_cancel]
  push_cast
  have hj1 : ((j : ℝ) + 1) ≠ 0 := by positivity
  rw [mul_div_mul_left _ _ hj1, div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun δ _ => ?_
  rw [div_eq_mul_inv, mul_assoc]

omit [DecidableEq ι] [DecidableEq J] [Fintype J] in
/-- **Die Rekursionsungleichung** für die Baumkoeffizienten: aus der
Zerlegung an der Wurzel und der Umbenennungsinvarianz folgt, dass der
normierte Baumkoeffizient der Ordnung `n` durch die nach Blockzahl und
Größenprofil sortierte Kompositionssumme der Nachbarterme beschränkt
ist. -/
theorem treeCoeff_div_le (w : ι → ℝ) (Λ : Finset ι) (γ₀ : ι) (n : ℕ)
 :
    treeCoeff P w Λ γ₀ n / (Nat.factorial n : ℝ)
      ≤ ∑ k ∈ Finset.range (n + 1), (Nat.factorial k : ℝ)⁻¹ *
          ∑ c ∈ compositionsF n k, ∏ j, nbhdTerm P w Λ γ₀ (c j) := by
  have hcard : (Finset.univ.erase (0 : Fin (n + 1))).card = n := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]
    omega
  -- Blockweise: die innere Doppelsumme ist das Blockfunktional.
  have hblock : ∀ (C : Finset (Finset (Fin (n + 1)))),
      (∀ B ∈ C, B.Nonempty) →
      ∏ B ∈ C, blockFactor P w Λ γ₀ B
        = ∏ B ∈ C, blockTerm P w Λ γ₀ B.card := by
    intro C hne
    refine Finset.prod_congr rfl fun B hB => ?_
    unfold blockFactor
    have hval : ∀ c ∈ B, ∑ δ ∈ incompNbhd P Λ γ₀,
        |w δ| * treeSum P w Λ δ c (B.erase c)
          = ∑ δ ∈ incompNbhd P Λ γ₀,
              |w δ| * treeCoeff P w Λ δ (B.card - 1) := by
      intro c hc
      exact Finset.sum_congr rfl fun δ _ => by
        rw [treeSum_eq_treeCoeff P w Λ δ hc]
    rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
    rfl
  -- Die Multinomialzählung anwenden.
  have hstep : treeCoeff P w Λ γ₀ n
      ≤ ∑ k ∈ Finset.range (n + 1), (Nat.factorial k : ℝ)⁻¹ *
          ∑ c ∈ compositionsF n k,
            ((Nat.factorial n : ℝ) / ∏ j, (Nat.factorial (c j) : ℝ)) *
              ∏ j, blockTerm P w Λ γ₀ (c j) := by
    unfold treeCoeff
    have hDecomp := treeSum_le_sum_partitions P w Λ γ₀
      (fun r A hr a₀ ha₀ => treeSum_le_peel P w Λ γ₀ r hr ha₀)
      (0 : Fin (n + 1))
      (Finset.notMem_erase (0 : Fin (n + 1)) Finset.univ)
    refine hDecomp.trans (le_of_eq ?_)
    have hcongr : ∑ C ∈ partitionsOf (Finset.univ.erase (0 : Fin (n + 1))),
        ∏ B ∈ C, blockFactor P w Λ γ₀ B
        = ∑ C ∈ partitionsOf (Finset.univ.erase (0 : Fin (n + 1))),
            ∏ B ∈ C, blockTerm P w Λ γ₀ B.card := by
      refine Finset.sum_congr rfl fun C hC => ?_
      obtain ⟨-, hICC, -⟩ := mem_partitionsOf.mp hC
      exact hblock C hICC.1
    rw [hcongr, sum_partitionsOf_card, hcard]
  -- Durch `n!` teilen und die Fakultäten in die Produkte ziehen.
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (Nat.factorial n : ℝ))]
  refine hstep.trans (le_of_eq ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_assoc, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun c hc => ?_
  obtain ⟨hpos, -⟩ := mem_compositionsF.mp hc
  have hfacne : (∏ j, (Nat.factorial (c j) : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ =>
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hterm : ∏ j, nbhdTerm P w Λ γ₀ (c j)
      = (∏ j, blockTerm P w Λ γ₀ (c j)) / ∏ j, (Nat.factorial (c j) : ℝ) := by
    rw [← Finset.prod_div_distrib]
    exact Finset.prod_congr rfl fun j _ => (blockTerm_div P w Λ γ₀ (hpos j)).symm
  rw [hterm]
  field_simp

/-! ## Die scharfe Summierbarkeitsschranke -/

omit [DecidableEq ι] [DecidableEq J] [Fintype J] in
/-- **Scharfe Kotecký-Preiss-Summierbarkeit** (modulo Rekursion und
Verknüpfung): unter der KP-Bedingung ist die bei `γ₀` verankerte
Betragsreihe der Cluster-Entwicklung durch `|w γ₀| · exp (a γ₀)`
beschränkt — gleichmäßig im Volumen und ohne Kleinheitsvoraussetzung. -/
theorem sum_range_pinned_le_of_kp (w : ι → ℝ) (a : ι → ℝ) (Λ : Finset ι)
    (γ₀ : ι) (hγ₀ : γ₀ ∈ Λ) (hKP : KPCondition P w a Λ) (N : ℕ) :
    ∑ n ∈ Finset.range N, pinnedOrderSum P w Λ γ₀ n / (Nat.factorial n : ℝ)
      ≤ |w γ₀| * Real.exp (a γ₀) := by
  have hRec : ∀ γ ∈ Λ, ∀ n : ℕ,
      treeCoeff P w Λ γ n / (Nat.factorial n : ℝ)
        ≤ ∑ k ∈ Finset.range (n + 1), (Nat.factorial k : ℝ)⁻¹ *
            ∑ c ∈ compositionsF n k, ∏ j, nbhdTerm P w Λ γ (c j) :=
    fun γ _ n => treeCoeff_div_le P w Λ γ n
  · have hstep : ∀ n ∈ Finset.range N,
        pinnedOrderSum P w Λ γ₀ n / (Nat.factorial n : ℝ)
          ≤ |w γ₀| * (treeCoeff P w Λ γ₀ n / (Nat.factorial n : ℝ)) := by
      intro n _
      calc pinnedOrderSum P w Λ γ₀ n / (Nat.factorial n : ℝ)
          ≤ (|w γ₀| * treeCoeff P w Λ γ₀ n) / (Nat.factorial n : ℝ) := by
            gcongr
            exact pinnedOrderSum_le_treeCoeff P w Λ γ₀ n
        _ = |w γ₀| * (treeCoeff P w Λ γ₀ n / (Nat.factorial n : ℝ)) := by
            rw [mul_div_assoc]
    have htail : ∑ n ∈ Finset.range N,
        (treeCoeff P w Λ γ₀ n / (Nat.factorial n : ℝ))
          ≤ treeTrunc P w Λ γ₀ N := by
      unfold treeTrunc
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro x hx
        rw [Finset.mem_range] at hx ⊢
        omega
      · intro n _ _
        exact div_nonneg (treeCoeff_nonneg P w Λ γ₀ n) (by positivity)
    calc ∑ n ∈ Finset.range N, pinnedOrderSum P w Λ γ₀ n / (Nat.factorial n : ℝ)
        ≤ ∑ n ∈ Finset.range N,
            |w γ₀| * (treeCoeff P w Λ γ₀ n / (Nat.factorial n : ℝ)) :=
          Finset.sum_le_sum hstep
      _ = |w γ₀| * ∑ n ∈ Finset.range N,
            (treeCoeff P w Λ γ₀ n / (Nat.factorial n : ℝ)) := by
          rw [Finset.mul_sum]
      _ ≤ |w γ₀| * treeTrunc P w Λ γ₀ N :=
          mul_le_mul_of_nonneg_left htail (abs_nonneg _)
      _ ≤ |w γ₀| * Real.exp (a γ₀) :=
          mul_le_mul_of_nonneg_left
            (treeTrunc_le_exp P w a Λ hKP hRec N γ₀ hγ₀) (abs_nonneg _)

omit [DecidableEq J] [Fintype J] in
/-- Unter der Kotecký-Preiss-Bedingung ist die verankerte Betragsreihe
summierbar. -/
theorem summable_pinned_of_kp (w : ι → ℝ) (a : ι → ℝ) (Λ : Finset ι)
    (γ₀ : ι) (hγ₀ : γ₀ ∈ Λ) (hKP : KPCondition P w a Λ) :
    Summable fun n => pinnedOrderSum P w Λ γ₀ n / (Nat.factorial n : ℝ) :=
  summable_of_sum_range_le
    (fun n => div_nonneg (pinnedOrderSum_nonneg P w Λ γ₀ n) (by positivity))
    (sum_range_pinned_le_of_kp P w a Λ γ₀ hγ₀ hKP)

omit [DecidableEq J] [Fintype J] in
/-- **Scharfe Kotecký-Preiss-Summierbarkeit**: unter der KP-Bedingung
ist die bei `γ₀` verankerte Betragsreihe der Cluster-Entwicklung durch
`|w γ₀| · exp (a γ₀)` beschränkt — gleichmäßig im Volumen und ohne
Kleinheitsvoraussetzung. -/
theorem tsum_pinned_le_of_kp (w : ι → ℝ) (a : ι → ℝ) (Λ : Finset ι)
    (γ₀ : ι) (hγ₀ : γ₀ ∈ Λ) (hKP : KPCondition P w a Λ) :
    ∑' n, pinnedOrderSum P w Λ γ₀ n / (Nat.factorial n : ℝ)
      ≤ |w γ₀| * Real.exp (a γ₀) :=
  Real.tsum_le_of_sum_range_le
    (fun n => div_nonneg (pinnedOrderSum_nonneg P w Λ γ₀ n) (by positivity))
    (sum_range_pinned_le_of_kp P w a Λ γ₀ hγ₀ hKP)

end ClusterExpansion
