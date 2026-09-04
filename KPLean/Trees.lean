/-
Copyright (c) 2026 Dennis Michael Heine. All rights reserved.
Released under the CC BY-NC-SA 4.0 license as described in the file LICENSE.
Authors: Dennis Michael Heine
-/
import KPLean.Exponential

/-!
# Wurzelbäume als Elternabbildungen

Grundlage der scharfen Kotecký-Preiss-Schranke. Statt Bäume als
Kantenmengen zu führen, werden sie als **Elternabbildungen**
`p : J → J` dargestellt: jeder Knoten außer der Wurzel zeigt auf seinen
Elternknoten, und von jedem Knoten führt die Iteration von `p` zur
Wurzel. Das ist dieselbe Darstellung, über die `treeCount_le_pow`
bereits die Baumzahl abschätzt.

* `rootedTrees A r`: die Elternabbildungen auf `insert r A` mit Wurzel
  `r` (außerhalb auf `r` festgenagelt, damit die Menge endlich und
  eindeutig ist);
* `subtreeOf p c`: der Teilbaum unter einem Kind `c` der Wurzel — die
  Knoten, deren Elternkette `r` über `c` erreicht;
* `treeSum`: die gewichtete Summe über Wurzelbäume und Belegungen, deren
  Kanten alle unverträglich sind — die Größe, die die scharfe
  Summierbarkeitsschranke kontrolliert.

Für die Schranke wird nur eine **Injektion** von den aufspannenden
Bäumen in die Elternabbildungen gebraucht, keine exakte Zählung; die
Prüfer-Korrespondenz und Cayleys Formel bleiben damit außen vor.
-/

open Finset

set_option linter.style.openClassical false

open scoped Classical

namespace ClusterExpansion

variable {ι J : Type*} [DecidableEq ι] [DecidableEq J] [Fintype J]

/-! ## Wurzelbäume -/

/-- Die Elternabbildungen auf `insert r A` mit Wurzel `r`: `r` zeigt auf
sich selbst, jeder Knoten von `A` erreicht `r` durch Iteration, und
außerhalb ist alles auf `r` festgenagelt. -/
noncomputable def rootedTrees (A : Finset J) (r : J) : Finset (J → J) :=
  (Fintype.piFinset fun _ => insert r A).filter
    (fun p => p r = r ∧ (∀ v ∉ insert r A, p v = r) ∧ ∀ v ∈ A, ∃ k, p^[k] v = r)

theorem mem_rootedTrees {A : Finset J} {r : J} {p : J → J} :
    p ∈ rootedTrees A r
      ↔ (∀ v, p v ∈ insert r A) ∧ p r = r
          ∧ (∀ v ∉ insert r A, p v = r) ∧ ∀ v ∈ A, ∃ k, p^[k] v = r := by
  unfold rootedTrees
  rw [Finset.mem_filter, Fintype.mem_piFinset]

/-- Über der leeren Knotenmenge gibt es genau den trivialen Baum. -/
theorem rootedTrees_empty (r : J) :
    rootedTrees (∅ : Finset J) r = {fun _ => r} := by
  ext p
  rw [mem_rootedTrees, Finset.mem_singleton]
  constructor
  · rintro ⟨-, hr, hout, -⟩
    funext v
    by_cases hv : v = r
    · rw [hv, hr]
    · exact hout v (by simp [hv])
  · rintro rfl
    exact ⟨fun _ => Finset.mem_insert_self r ∅, rfl, fun _ _ => rfl,
      fun v hv => absurd hv (Finset.notMem_empty v)⟩

/-- Die Iteration der Elternabbildung bleibt in `insert r A`. -/
theorem iterate_mem_rootedTrees {A : Finset J} {r : J} {p : J → J}
    (hp : p ∈ rootedTrees A r) (v : J) (k : ℕ) :
    k ≠ 0 → p^[k] v ∈ insert r A := by
  obtain ⟨hpi, -, -, -⟩ := mem_rootedTrees.mp hp
  intro hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Function.iterate_succ_apply']
  exact hpi _

/-! ## Der Teilbaum unter einem Kind der Wurzel -/

/-- Die Knoten von `A`, deren Elternkette die Wurzel über `c` erreicht:
der Teilbaum unter dem Kind `c`. -/
noncomputable def subtreeOf (A : Finset J) (r : J) (p : J → J) (c : J) :
    Finset J :=
  A.filter (fun v => ∃ k, p^[k] v = c ∧ p^[k + 1] v = r)

omit [DecidableEq J] [Fintype J] in
theorem mem_subtreeOf {A : Finset J} {r : J} {p : J → J} {c v : J} :
    v ∈ subtreeOf A r p c
      ↔ v ∈ A ∧ ∃ k, p^[k] v = c ∧ p^[k + 1] v = r :=
  Finset.mem_filter

omit [DecidableEq J] [Fintype J] in
theorem subtreeOf_subset {A : Finset J} {r : J} {p : J → J} {c : J} :
    subtreeOf A r p c ⊆ A :=
  Finset.filter_subset _ _

omit [DecidableEq J] [Fintype J] in
/-- Ein Kind der Wurzel liegt in seinem eigenen Teilbaum. -/
theorem self_mem_subtreeOf {A : Finset J} {r : J} {p : J → J} {c : J}
    (hc : c ∈ A) (hpc : p c = r) : c ∈ subtreeOf A r p c :=
  mem_subtreeOf.mpr ⟨hc, 0, rfl, hpc⟩

/-- Die Kinder der Wurzel. -/
noncomputable def rootChildren (A : Finset J) (r : J) (p : J → J) :
    Finset J :=
  A.filter (fun v => p v = r)

omit [Fintype J] in
theorem mem_rootChildren {A : Finset J} {r : J} {p : J → J} {v : J} :
    v ∈ rootChildren A r p ↔ v ∈ A ∧ p v = r :=
  Finset.mem_filter

/-! ## Die gewichtete Baumsumme -/

variable (P : PolymerSystem ι)

/-- Alle Kanten des Wurzelbaums verbinden unverträgliche Polymere. -/
def TreeIncompatible (h : J → ι) (A : Finset J) (p : J → J) : Prop :=
  ∀ v ∈ A, P.incomp (h v) (h (p v)) = true

/-- **Die gewichtete Baum-Tupel-Summe**: Summe über die Wurzelbäume auf
`insert r A` und die Belegungen mit Wurzelwert `γ₀`, gewichtet mit den
Beträgen der Gewichte und eingeschränkt auf unverträgliche Kanten. Das
ist die Größe, die die scharfe Summierbarkeitsschranke kontrolliert. -/
noncomputable def treeSum (w : ι → ℝ) (Λ : Finset ι) (γ₀ : ι) (r : J)
    (A : Finset J) : ℝ :=
  ∑ p ∈ rootedTrees A r, ∑ h ∈ pinnedTuples Λ γ₀ A,
    (∏ v ∈ A, |w (h v)|) *
      (if TreeIncompatible P h A p then 1 else 0)

omit [DecidableEq ι] in
theorem treeSum_nonneg (w : ι → ℝ) (Λ : Finset ι) (γ₀ : ι) (r : J)
    (A : Finset J) : 0 ≤ treeSum P w Λ γ₀ r A := by
  unfold treeSum
  refine Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun h _ => ?_
  refine mul_nonneg (Finset.prod_nonneg fun v _ => abs_nonneg _) ?_
  split <;> norm_num

omit [DecidableEq ι] in
/-- Über der leeren Knotenmenge ist die Baumsumme `1`. -/
theorem treeSum_empty (w : ι → ℝ) (Λ : Finset ι) (γ₀ : ι) (r : J) :
    treeSum P w Λ γ₀ r (∅ : Finset J) = 1 := by
  unfold treeSum
  rw [rootedTrees_empty, Finset.sum_singleton, pinnedTuples_empty,
    Finset.sum_singleton, Finset.prod_empty, one_mul, if_pos]
  intro v hv
  exact absurd hv (Finset.notMem_empty v)

/-! ## Der kanonische Baumkoeffizient

Alle Baumsummen mit `n` Nichtwurzelknoten stimmen überein — die
Knotenmenge geht nur über ihre Kardinalität ein. Als Normalform dient
die Baumsumme über `Fin (n+1)` mit Wurzel `0`. -/

/-- Der Baumkoeffizient der Ordnung `n`: die gewichtete Baumsumme über
`n` Nichtwurzelknoten mit Wurzelwert `δ`. -/
noncomputable def treeCoeff (w : ι → ℝ) (Λ : Finset ι) (δ : ι) (n : ℕ) : ℝ :=
  treeSum P w Λ δ (0 : Fin (n + 1)) (Finset.univ.erase 0)

omit [DecidableEq ι] [DecidableEq J] [Fintype J] in
theorem treeCoeff_nonneg (w : ι → ℝ) (Λ : Finset ι) (δ : ι) (n : ℕ) :
    0 ≤ treeCoeff P w Λ δ n :=
  treeSum_nonneg P w Λ δ _ _

omit [DecidableEq ι] [DecidableEq J] [Fintype J] in
/-- Ordnung `0`: nur die Wurzel, also der Wert `1`. -/
theorem treeCoeff_zero (w : ι → ℝ) (Λ : Finset ι) (δ : ι) :
    treeCoeff P w Λ δ 0 = 1 := by
  unfold treeCoeff
  have hempty : (Finset.univ.erase (0 : Fin 1)) = (∅ : Finset (Fin 1)) := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro v hv
    exact (Finset.mem_erase.mp hv).1 (Subsingleton.elim v 0)
  rw [hempty, treeSum_empty]

/-- Die mit `γ₀` unverträglichen Polymere von `Λ` — die Nachbarschaft,
über die die Kotecký-Preiss-Bedingung summiert. -/
noncomputable def incompNbhd (Λ : Finset ι) (γ₀ : ι) : Finset ι :=
  Λ.filter (fun δ => P.incomp γ₀ δ = true)

omit [DecidableEq ι] [DecidableEq J] [Fintype J] in
theorem mem_incompNbhd {Λ : Finset ι} {γ₀ δ : ι} :
    δ ∈ incompNbhd P Λ γ₀ ↔ δ ∈ Λ ∧ P.incomp γ₀ δ = true :=
  Finset.mem_filter

end ClusterExpansion
