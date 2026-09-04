/-
Copyright (c) 2026 Dennis Michael Heine. All rights reserved.
Released under the CC BY-NC-SA 4.0 license as described in the file LICENSE.
Authors: Dennis Michael Heine
-/
import KPLean.Trees

/-!
# Von der Ursell-Summe zur Baumsumme

Die Baumgraphen-Schranke, in die Sprache der Elternabbildungen übersetzt:
die Baumzahl eines Trägers ist durch die Anzahl der Wurzelbäume mit
Kanten im Träger beschränkt (`treeCount_le_card_rootedTrees`, per
Injektion `T ↦ Penrose-Elternabbildung`), und damit ist der bei `γ₀`
verankerte Ursell-Beitrag durch `‖w γ₀‖` mal dem Baumkoeffizienten
beschränkt (`pinnedOrderSum_le_treeCoeff`).
-/

open Finset

set_option linter.style.openClassical false

open scoped Classical

namespace ClusterExpansion

variable {K : Type*} [RCLike K]
variable {ι : Type*} [DecidableEq ι] (P : PolymerSystem ι)


/-! ## Die Wurzel von `Fin (n+1)` und ihre Elternabbildung

Die Penrose-Wurzel ist das kleinste Element der Knotenmenge; über
`Fin (n+1)` ist das der Index `0`. Die zugehörige, an der Wurzel
festgenagelte Elternabbildung `parMap` ist die Brücke zwischen den
aufspannenden Bäumen aus `Ursell.lean` und den Wurzelbäumen aus
`Trees.lean`. -/

/-- Die Penrose-Wurzel von `Fin (n+1)` ist der Index `0`. -/
theorem root_fin (n : ℕ) : root (Fin (n + 1)) = 0 :=
  le_antisymm (Finset.min'_le _ _ (Finset.mem_univ 0)) (Fin.zero_le _)

/-- Die an der Wurzel `0` festgenagelte Penrose-Elternabbildung eines
Kantenzugs über `Fin (n+1)`. -/
noncomputable def parMap {n : ℕ} (T : Finset (Sym2 (Fin (n + 1))))
    (v : Fin (n + 1)) : Fin (n + 1) :=
  if v = 0 then 0 else par T v

/-- Die Wurzel zeigt auf sich selbst. -/
theorem parMap_zero {n : ℕ} (T : Finset (Sym2 (Fin (n + 1)))) :
    parMap T 0 = 0 :=
  if_pos rfl

/-- Außerhalb der Wurzel ist `parMap` der Penrose-Elternknoten. -/
theorem parMap_of_ne {n : ℕ} {T : Finset (Sym2 (Fin (n + 1)))}
    {v : Fin (n + 1)} (hv : v ≠ 0) : parMap T v = par T v :=
  if_neg hv

/-! ## Von der Baumzahl zur Wurzelbaum-Zählung -/

/-- **Baumzahl unter Wurzelbaum-Zahl**: die aufspannenden Bäume eines
diagonalfreien Trägers `H` sind höchstens so zahlreich wie die
Wurzelbäume auf `Fin (n+1)` mit Wurzel `0`, deren Elternkanten sämtlich
in `H` liegen. Die Injektion ist `T ↦ parMap T`: der Penrose-Baum eines
Baums ist der Baum selbst (`penroseTree_of_isTree`) und zugleich das
Bild seiner Elternabbildung, also ist `T` aus `parMap T`
rekonstruierbar. -/
theorem treeCount_le_card_rootedTrees {n : ℕ}
    (H : Finset (Sym2 (Fin (n + 1)))) (hH : ∀ e ∈ H, ¬ e.IsDiag) :
    treeCount H
      ≤ ((rootedTrees (Finset.univ.erase (0 : Fin (n + 1))) 0).filter
          (fun p => ∀ v ∈ Finset.univ.erase (0 : Fin (n + 1)),
            s(v, p v) ∈ H)).card := by
  unfold treeCount
  refine Finset.card_le_card_of_injOn parMap ?_ ?_
  -- Schritt 1: `parMap T` ist ein Wurzelbaum mit Kanten in `H`.
  · intro T hT
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hT
    obtain ⟨hTH, hTtree⟩ := hT
    have hconn : EdgeConn T := hTtree.connected
    have hvr : ∀ v : Fin (n + 1), v ≠ 0 → v ≠ root (Fin (n + 1)) := by
      intro v hv
      rw [root_fin n]
      exact hv
    have huniv : insert (0 : Fin (n + 1)) (Finset.univ.erase (0 : Fin (n + 1)))
        = Finset.univ := Finset.insert_erase (Finset.mem_univ 0)
    -- Erreichbarkeit der Wurzel: Induktion über die BFS-Schicht, denn
    -- der Elternknoten liegt eine Schicht tiefer (`par_spec`).
    have hreach : ∀ m : ℕ, ∀ v : Fin (n + 1), lvl T v = m →
        ∃ k, (parMap T)^[k] v = 0 := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro v hval
        by_cases hv : v = 0
        · exact ⟨0, by rw [Function.iterate_zero_apply, hv]⟩
        · have hlvl := (par_spec hconn (hvr v hv)).2
          obtain ⟨k, hk⟩ := ih (lvl T (par T v)) (by omega) (par T v) rfl
          refine ⟨k + 1, ?_⟩
          rw [Function.iterate_succ_apply, parMap_of_ne hv]
          exact hk
    refine Finset.mem_coe.mpr
      (Finset.mem_filter.mpr ⟨mem_rootedTrees.mpr ⟨?_, ?_, ?_, ?_⟩, ?_⟩)
    · intro v
      rw [huniv]
      exact Finset.mem_univ _
    · exact parMap_zero T
    · intro v hv
      exact absurd (by rw [huniv]; exact Finset.mem_univ v) hv
    · intro v _
      exact hreach (lvl T v) v rfl
    · intro v hv
      have hv0 : v ≠ 0 := (Finset.mem_erase.mp hv).1
      rw [parMap_of_ne hv0]
      refine hTH ?_
      have hmem := (graphOf_adj.mp (par_spec hconn (hvr v hv0)).1).1
      rwa [Sym2.eq_swap]
  -- Schritt 2: Injektivität — wie in `treeCount_le_pow`.
  · intro T₁ h₁ T₂ h₂ heq
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at h₁ h₂
    have hd₁ : ∀ e ∈ T₁, ¬ e.IsDiag := fun e he => hH e (h₁.1 he)
    have hd₂ : ∀ e ∈ T₂, ¬ e.IsDiag := fun e he => hH e (h₂.1 he)
    have hpar : ∀ v : Fin (n + 1), v ≠ 0 → par T₁ v = par T₂ v := by
      intro v hv
      have h := congrFun heq v
      rwa [parMap_of_ne hv, parMap_of_ne hv] at h
    calc T₁ = penroseTree T₁ := (penroseTree_of_isTree hd₁ h₁.2).symm
      _ = penroseTree T₂ := by
          refine Finset.image_congr fun v hv => ?_
          have hv' : v ≠ root (Fin (n + 1)) :=
            (Finset.mem_erase.mp (Finset.mem_coe.mp hv)).1
          rw [hpar v (by rwa [root_fin n] at hv')]
      _ = T₂ := penroseTree_of_isTree hd₂ h₂.2

/-! ## Ursell-Betragssumme unter der Baumsumme -/

/-- **Die Ursell-Betragssumme unter der Baumsumme**: der bei `γ₀`
verankerte Betrags-Beitrag der Ordnung `n + 1` ist durch `‖w γ₀‖` mal
dem Baumkoeffizienten beschränkt.

Drei Schritte: je Tupel ersetzt die Baumgraphen-Schranke
`abs_ursellInt_le_treeCount` den Ursell-Betrag durch die Baumzahl des
Unverträglichkeitsgraphen, `treeCount_le_card_rootedTrees` diese durch
die Anzahl passender Wurzelbäume; das Gewichtsprodukt spaltet den Anker
`‖w γ₀‖` ab, und nach Vertauschen von Tupel- und Baumsumme steht rechts
genau die Baumsumme. -/
theorem pinnedOrderSum_le_treeCoeff (w : ι → K) (Λ : Finset ι) (γ₀ : ι)
    (n : ℕ) :
    pinnedOrderSum P w Λ γ₀ n ≤ ‖w γ₀‖ * treeCoeff P w Λ γ₀ n := by
  -- Je verankertem Tupel: Betrag durch die Wurzelbaum-Zahl ersetzen und
  -- als Indikatorsumme über die Wurzelbäume schreiben.
  have hterm : ∀ γ ∈ (Fintype.piFinset fun _ : Fin (n + 1) => Λ).filter
      (fun γ => γ 0 = γ₀),
      ‖(ursellInt P γ : K)‖ * ∏ i, ‖w (γ i)‖
        ≤ ∑ p ∈ rootedTrees (Finset.univ.erase (0 : Fin (n + 1))) 0,
            ‖w γ₀‖ * ((∏ v ∈ Finset.univ.erase (0 : Fin (n + 1)), ‖w (γ v)‖) *
              (if TreeIncompatible P γ (Finset.univ.erase 0) p then 1 else 0)) := by
    intro γ hγ
    have hpin : γ 0 = γ₀ := (Finset.mem_filter.mp hγ).2
    -- Der Anker spaltet sich aus dem Gewichtsprodukt ab.
    have hsplit : ∏ i, ‖w (γ i)‖
        = ‖w γ₀‖ * ∏ v ∈ Finset.univ.erase (0 : Fin (n + 1)), ‖w (γ v)‖ := by
      rw [← hpin]
      exact (Finset.mul_prod_erase Finset.univ (fun i => ‖w (γ i)‖)
        (Finset.mem_univ 0)).symm
    -- Baumgraphen-Schranke, dann Wurzelbaum-Zählung.
    have hcard : ‖(ursellInt P γ : K)‖
        ≤ (((rootedTrees (Finset.univ.erase (0 : Fin (n + 1))) 0).filter
            (fun p => ∀ v ∈ Finset.univ.erase (0 : Fin (n + 1)),
              s(v, p v) ∈ clusterEdges P γ)).card : ℝ) := by
      have h2 := treeCount_le_card_rootedTrees (clusterEdges P γ)
        (clusterEdges_not_isDiag P γ)
      calc ‖(ursellInt P γ : K)‖ = ((|ursellInt P γ| : ℤ) : ℝ) := by
            rw [norm_intCast_eq_abs, Int.cast_abs]
        _ ≤ ((treeCount (clusterEdges P γ) : ℤ) : ℝ) := by
            exact_mod_cast abs_ursellInt_le_treeCount P γ
        _ ≤ _ := by exact_mod_cast h2
    calc ‖(ursellInt P γ : K)‖ * ∏ i, ‖w (γ i)‖
        ≤ (((rootedTrees (Finset.univ.erase (0 : Fin (n + 1))) 0).filter
              (fun p => ∀ v ∈ Finset.univ.erase (0 : Fin (n + 1)),
                s(v, p v) ∈ clusterEdges P γ)).card : ℝ)
            * (‖w γ₀‖ * ∏ v ∈ Finset.univ.erase (0 : Fin (n + 1)), ‖w (γ v)‖) := by
          rw [hsplit]
          exact mul_le_mul_of_nonneg_right hcard
            (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun v _ => norm_nonneg _))
      _ = ∑ _p ∈ (rootedTrees (Finset.univ.erase (0 : Fin (n + 1))) 0).filter
              (fun p => ∀ v ∈ Finset.univ.erase (0 : Fin (n + 1)),
                s(v, p v) ∈ clusterEdges P γ),
            ‖w γ₀‖ * ∏ v ∈ Finset.univ.erase (0 : Fin (n + 1)), ‖w (γ v)‖ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      -- Eine Kante `s(v, p v)` des Unverträglichkeitsgraphen heißt genau,
      -- dass `γ v` und `γ (p v)` unverträglich sind.
      _ ≤ ∑ p ∈ rootedTrees (Finset.univ.erase (0 : Fin (n + 1))) 0,
            ‖w γ₀‖ * ((∏ v ∈ Finset.univ.erase (0 : Fin (n + 1)), ‖w (γ v)‖) *
              (if TreeIncompatible P γ (Finset.univ.erase 0) p then 1 else 0)) := by
          rw [Finset.sum_filter]
          refine Finset.sum_le_sum fun p _ => ?_
          by_cases hcl : ∀ v ∈ Finset.univ.erase (0 : Fin (n + 1)),
              s(v, p v) ∈ clusterEdges P γ
          · have hTI : TreeIncompatible P γ (Finset.univ.erase 0) p :=
              fun v hv => ((mem_clusterEdges P).mp (hcl v hv)).2
            rw [if_pos hcl, if_pos hTI, mul_one]
          · rw [if_neg hcl]
            refine mul_nonneg (norm_nonneg _) (mul_nonneg ?_ ?_)
            · exact Finset.prod_nonneg fun v _ => norm_nonneg _
            · split <;> norm_num
  -- Summieren, Anker ausklammern, Tupel- und Baumsumme vertauschen.
  unfold pinnedOrderSum treeCoeff treeSum
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [Finset.mul_sum]
  -- Die verankerten Tupel sind festgenagelte Belegungen.
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro γ hγ
    rw [Finset.mem_filter] at hγ
    obtain ⟨hmem, hpin⟩ := hγ
    refine mem_pinnedTuples.mpr
      ⟨fun j _ => Fintype.mem_piFinset.mp hmem j, fun j hj => ?_⟩
    have hj0 : j = 0 := by
      by_contra hne
      exact hj (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ j⟩)
    rw [hj0, hpin]
  · intro h _ _
    refine mul_nonneg (norm_nonneg _) (mul_nonneg ?_ ?_)
    · exact Finset.prod_nonneg fun v _ => norm_nonneg _
    · split <;> norm_num

end ClusterExpansion
