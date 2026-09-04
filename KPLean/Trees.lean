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

variable {K : Type*} [RCLike K]
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
noncomputable def treeSum (w : ι → K) (Λ : Finset ι) (γ₀ : ι) (r : J)
    (A : Finset J) : ℝ :=
  ∑ p ∈ rootedTrees A r, ∑ h ∈ pinnedTuples Λ γ₀ A,
    (∏ v ∈ A, ‖w (h v)‖) *
      (if TreeIncompatible P h A p then 1 else 0)

omit [DecidableEq ι] in
theorem treeSum_nonneg (w : ι → K) (Λ : Finset ι) (γ₀ : ι) (r : J)
    (A : Finset J) : 0 ≤ treeSum P w Λ γ₀ r A := by
  unfold treeSum
  refine Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun h _ => ?_
  refine mul_nonneg (Finset.prod_nonneg fun v _ => norm_nonneg _) ?_
  split <;> norm_num

omit [DecidableEq ι] in
/-- Über der leeren Knotenmenge ist die Baumsumme `1`. -/
theorem treeSum_empty (w : ι → K) (Λ : Finset ι) (γ₀ : ι) (r : J) :
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
noncomputable def treeCoeff (w : ι → K) (Λ : Finset ι) (δ : ι) (n : ℕ) : ℝ :=
  treeSum P w Λ δ (0 : Fin (n + 1)) (Finset.univ.erase 0)

omit [DecidableEq ι] [DecidableEq J] [Fintype J] in
theorem treeCoeff_nonneg (w : ι → K) (Λ : Finset ι) (δ : ι) (n : ℕ) :
    0 ≤ treeCoeff P w Λ δ n :=
  treeSum_nonneg P w Λ δ _ _

omit [DecidableEq ι] [DecidableEq J] [Fintype J] in
/-- Ordnung `0`: nur die Wurzel, also der Wert `1`. -/
theorem treeCoeff_zero (w : ι → K) (Λ : Finset ι) (δ : ι) :
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

/-! ## Die Kotecký-Preiss-Induktion

Aus der Rekursionsungleichung für die Baumkoeffizienten folgt unter der
Kotecký-Preiss-Bedingung die Schranke `exp (a γ)` für jede
abgeschnittene Baumreihe — gleichmäßig in der Abschneidehöhe und damit
im Volumen. -/


/-- Der Beitrag der Ordnung `m ≥ 1` eines Nachbarn: Gewicht mal
normiertem Baumkoeffizienten des Teilbaums. -/
noncomputable def nbhdTerm (w : ι → K) (Λ : Finset ι) (γ : ι) (m : ℕ) : ℝ :=
  ∑ δ ∈ incompNbhd P Λ γ,
    ‖w δ‖ * (treeCoeff P w Λ δ (m - 1) / (Nat.factorial (m - 1) : ℝ))

omit [DecidableEq ι] [DecidableEq J] [Fintype J] in
theorem nbhdTerm_nonneg (w : ι → K) (Λ : Finset ι) (γ : ι) (m : ℕ) :
    0 ≤ nbhdTerm P w Λ γ m := by
  unfold nbhdTerm
  refine Finset.sum_nonneg fun δ _ => mul_nonneg (norm_nonneg _) ?_
  exact div_nonneg (treeCoeff_nonneg P w Λ δ _) (by positivity)

/-- Die abgeschnittene Baumreihe: die normierten Baumkoeffizienten bis
zur Ordnung `N`. -/
noncomputable def treeTrunc (w : ι → K) (Λ : Finset ι) (γ : ι) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1),
    treeCoeff P w Λ γ n / (Nat.factorial n : ℝ)

omit [DecidableEq ι] [DecidableEq J] [Fintype J] in
theorem treeTrunc_nonneg (w : ι → K) (Λ : Finset ι) (γ : ι) (N : ℕ) :
    0 ≤ treeTrunc P w Λ γ N :=
  Finset.sum_nonneg fun n _ =>
    div_nonneg (treeCoeff_nonneg P w Λ γ n) (by positivity)

omit [DecidableEq ι] [DecidableEq J] [Fintype J] in
/-- Die Nachbarterme summieren sich zur abgeschnittenen Reihe der
Nachbarn: `∑_{m=1}^{N+1} nbhdTerm m = ∑_{δ ≁ γ} ‖w δ‖ · treeTrunc δ N`. -/
theorem sum_nbhdTerm (w : ι → K) (Λ : Finset ι) (γ : ι) (N : ℕ) :
    ∑ m ∈ Finset.Icc 1 (N + 1), nbhdTerm P w Λ γ m
      = ∑ δ ∈ incompNbhd P Λ γ, ‖w δ‖ * treeTrunc P w Λ δ N := by
  unfold nbhdTerm treeTrunc
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun δ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_nbij' (fun m => m - 1) (fun n => n + 1) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hm
    exact Finset.mem_range.mpr (by omega)
  · intro n hn
    have := Finset.mem_range.mp hn
    exact Finset.mem_Icc.mpr (by omega)
  · intro m hm
    obtain ⟨h1, -⟩ := Finset.mem_Icc.mp hm
    omega
  · intro n _
    omega
  · intro m _
    rfl

/-- Die Kompositionen aller Gesamtgewichte bis `N` liegen in den Tupeln
mit Einträgen aus `[1, N]`. -/
private theorem sum_compositions_le_pow (N k : ℕ) (x : ℕ → ℝ)
    (hx : ∀ m, 0 ≤ x m) :
    ∑ n ∈ Finset.range (N + 1), ∑ c ∈ compositionsF n k, ∏ j, x (c j)
      ≤ (∑ m ∈ Finset.Icc 1 N, x m) ^ k := by
  set D : Finset (Fin k → ℕ) :=
    (Fintype.piFinset fun _ : Fin k => Finset.Icc 1 N).filter
      (fun c => ∑ j, c j ≤ N) with hD
  have hmaps : ∀ c ∈ D, (∑ j, c j) ∈ Finset.range (N + 1) := by
    intro c hc
    exact Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Finset.mem_filter.mp hc).2)
  have hfib : ∀ n ∈ Finset.range (N + 1),
      D.filter (fun c => ∑ j, c j = n) = compositionsF n k := by
    intro n hn
    have hnN := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    ext c
    rw [Finset.mem_filter, hD, Finset.mem_filter, Fintype.mem_piFinset,
      mem_compositionsF]
    constructor
    · rintro ⟨⟨hpi, -⟩, hsum⟩
      refine ⟨fun j => ?_, hsum⟩
      have := Finset.mem_Icc.mp (hpi j)
      omega
    · rintro ⟨hne, hsum⟩
      have hle : ∀ j, c j ≤ n := by
        intro j
        have := Finset.single_le_sum (f := c) (fun i _ => Nat.zero_le (c i))
          (Finset.mem_univ j)
        omega
      refine ⟨⟨fun j => Finset.mem_Icc.mpr ⟨?_, ?_⟩, by omega⟩, hsum⟩
      · exact Nat.one_le_iff_ne_zero.mpr (hne j)
      · exact (hle j).trans hnN
  have hstep : ∑ n ∈ Finset.range (N + 1), ∑ c ∈ compositionsF n k, ∏ j, x (c j)
      = ∑ c ∈ D, ∏ j, x (c j) := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun c => ∏ j, x (c j))]
    exact Finset.sum_congr rfl fun n hn => by rw [hfib n hn]
  rw [hstep]
  have hpow : (∑ m ∈ Finset.Icc 1 N, x m) ^ k
      = ∑ c ∈ Fintype.piFinset fun _ : Fin k => Finset.Icc 1 N, ∏ j, x (c j) := by
    have h := Finset.prod_univ_sum
      (fun _ : Fin k => Finset.Icc 1 N) (fun _ m => x m)
    rw [← h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hpow]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
  exact fun c _ _ => Finset.prod_nonneg fun j _ => hx (c j)

omit [DecidableEq ι] [DecidableEq J] [Fintype J] in
/-- **Die Kotecký-Preiss-Induktion**: unter der KP-Bedingung ist jede
abgeschnittene Baumreihe durch `exp (a γ)` beschränkt. Der Beweis ist
eine Induktion über die Abschneidehöhe: die Rekursionsungleichung
entwickelt die Ordnung `n` in Kompositionen, deren Teile über die
Nachbarschaft laufen, und die Induktionsvoraussetzung ersetzt die
Nachbarterme durch `exp (a δ)`, was die KP-Bedingung zu `a γ`
zusammenzieht. -/
theorem treeTrunc_le_exp (w : ι → K) (a : ι → ℝ) (Λ : Finset ι)
    (hKP : KPCondition P w a Λ)
    (hRec : ∀ γ ∈ Λ, ∀ n : ℕ,
      treeCoeff P w Λ γ n / (Nat.factorial n : ℝ)
        ≤ ∑ k ∈ Finset.range (n + 1), (Nat.factorial k : ℝ)⁻¹ *
            ∑ c ∈ compositionsF n k, ∏ j, nbhdTerm P w Λ γ (c j)) :
    ∀ N : ℕ, ∀ γ ∈ Λ, treeTrunc P w Λ γ N ≤ Real.exp (a γ) := by
  obtain ⟨hapos, hasum⟩ := hKP
  intro N
  induction N with
  | zero =>
    intro γ hγ
    unfold treeTrunc
    rw [Finset.range_one, Finset.sum_singleton, treeCoeff_zero,
      Nat.factorial_zero, Nat.cast_one, div_one]
    exact Real.one_le_exp (hapos γ hγ)
  | succ N IH =>
    intro γ hγ
    -- Abschätzung jeder Ordnung durch die Kompositionssumme.
    have hterm : ∀ n ∈ Finset.range (N + 2),
        treeCoeff P w Λ γ n / (Nat.factorial n : ℝ)
          ≤ ∑ k ∈ Finset.range (N + 2), (Nat.factorial k : ℝ)⁻¹ *
              ∑ c ∈ compositionsF n k, ∏ j, nbhdTerm P w Λ γ (c j) := by
      intro n hn
      refine (hRec γ hγ n).trans ?_
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · have hnN := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
        intro x hx
        rw [Finset.mem_range] at hx ⊢
        omega
      · intro k _ _
        refine mul_nonneg (by positivity) (Finset.sum_nonneg fun c _ => ?_)
        exact Finset.prod_nonneg fun j _ => nbhdTerm_nonneg P w Λ γ _
    -- Summieren über die Ordnungen und Vertauschen mit der Kompositionszahl.
    have hsum : treeTrunc P w Λ γ (N + 1)
        ≤ ∑ k ∈ Finset.range (N + 2), (Nat.factorial k : ℝ)⁻¹ *
            ∑ n ∈ Finset.range (N + 2),
              ∑ c ∈ compositionsF n k, ∏ j, nbhdTerm P w Λ γ (c j) := by
      unfold treeTrunc
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [Finset.sum_comm]
      refine le_of_eq (Finset.sum_congr rfl fun k _ => ?_)
      rw [Finset.mul_sum]
    -- Die innere Doppelsumme durch die Potenz der Nachbarsumme abschätzen.
    set S : ℝ := ∑ m ∈ Finset.Icc 1 (N + 1), nbhdTerm P w Λ γ m with hS
    have hSnn : 0 ≤ S :=
      Finset.sum_nonneg fun m _ => nbhdTerm_nonneg P w Λ γ m
    have hinner : ∀ k, ∑ n ∈ Finset.range (N + 2),
        ∑ c ∈ compositionsF n k, ∏ j, nbhdTerm P w Λ γ (c j) ≤ S ^ k :=
      fun k => sum_compositions_le_pow (N + 1) k _
        (fun m => nbhdTerm_nonneg P w Λ γ m)
    have hpow : treeTrunc P w Λ γ (N + 1)
        ≤ ∑ k ∈ Finset.range (N + 2), (Nat.factorial k : ℝ)⁻¹ * S ^ k := by
      refine hsum.trans (Finset.sum_le_sum fun k _ => ?_)
      exact mul_le_mul_of_nonneg_left (hinner k) (by positivity)
    -- Die Partialsumme der Exponentialreihe.
    have hexpS : ∑ k ∈ Finset.range (N + 2), (Nat.factorial k : ℝ)⁻¹ * S ^ k
        ≤ Real.exp S := by
      have h := Real.sum_le_exp_of_nonneg hSnn (N + 2)
      refine le_trans (le_of_eq ?_) h
      exact Finset.sum_congr rfl fun k _ => by
        rw [div_eq_inv_mul]
    -- Die Induktionsvoraussetzung und die KP-Bedingung.
    have hSle : S ≤ a γ := by
      rw [hS, sum_nbhdTerm]
      refine le_trans (Finset.sum_le_sum fun δ hδ => ?_) (hasum γ hγ)
      obtain ⟨hδΛ, -⟩ := (mem_incompNbhd P).mp hδ
      exact mul_le_mul_of_nonneg_left (IH δ hδΛ) (norm_nonneg _)
    exact (hpow.trans hexpS).trans (Real.exp_le_exp.mpr hSle)

/-- **Der Blockfaktor**: der Beitrag eines Blocks zur Wurzelzerlegung —
Wahl der Blockwurzel `c`, Wahl des mit `γ₀` unverträglichen Wertes `δ`
an dieser Wurzel, und die Baumsumme des Teilbaums. -/
noncomputable def blockFactor (w : ι → K) (Λ : Finset ι) (γ₀ : ι)
    (B : Finset J) : ℝ :=
  ∑ c ∈ B, ∑ δ ∈ incompNbhd P Λ γ₀,
    ‖w δ‖ * treeSum P w Λ δ c (B.erase c)

omit [DecidableEq ι] in
theorem blockFactor_nonneg (w : ι → K) (Λ : Finset ι) (γ₀ : ι)
    (B : Finset J) : 0 ≤ blockFactor P w Λ γ₀ B :=
  Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun δ _ =>
    mul_nonneg (norm_nonneg _) (treeSum_nonneg P w Λ δ c _)

end ClusterExpansion
