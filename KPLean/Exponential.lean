/-
Copyright (c) 2026 Dennis Michael Heine. All rights reserved.
Released under the CC BY-NC-SA 4.0 license as described in the file LICENSE.
Authors: Dennis Michael Heine
-/
import KPLean.ClusterSeries

/-!
# Die Exponentialformel: Grundgerüst

Definitionen und Basislemmata für die Identifikation
`log Z Λ = clusterSeries P w Λ` im Konvergenzregime:

* `PolymerSystem.pull`: das entlang einer Belegung `h : J → ι`
  zurückgezogene Polymersystem auf der Indexmenge `J`;
* `partitionsOf A`: die Partitionen von `A` als Cluster-Kollektionen
  mit Vereinigung `A`;
* `pinnedTuples Λ γ⋆ K`: Belegungen `J → ι` mit Werten in `Λ` auf `K`
  und Wert `γ⋆` außerhalb — die endliche Indexmenge der Tupelsummen;
* `tupleZ`, `tupleU`: die Tupelsummen der Ordnung `|K|` mit
  Unabhängigkeits-Indikator bzw. Ursell-Gewicht;
* Kombinier- und Einschränkungsabbildungen samt Lokalitätslemmata.

Die eigentliche Beweiskette (Partitionsidentität, Blockzerlegung,
Zählung, analytischer Schritt) liegt in den darauf aufbauenden
Abschnitten dieser Datei.
-/

open Finset

set_option linter.style.openClassical false

open scoped Classical

namespace ClusterExpansion

/-- Das entlang `h : J → ι` zurückgezogene Polymersystem auf `J`:
`i` und `j` sind unverträglich, wenn ihre Bilder es sind. -/
def PolymerSystem.pull {ι J : Type*} (P : PolymerSystem ι) (h : J → ι) :
    PolymerSystem J where
  incomp i j := P.incomp (h i) (h j)
  symm i j := P.symm (h i) (h j)
  refl i := P.refl (h i)

variable {ι J : Type*} [DecidableEq ι] [DecidableEq J] (P : PolymerSystem ι)

/-! ## Partitionen als Cluster-Kollektionen -/

/-- Die Partitionen von `A`: Cluster-Kollektionen (paarweise disjunkte,
nichtleere Blöcke) mit Vereinigung `A`. -/
noncomputable def partitionsOf (A : Finset J) : Finset (Finset (Finset J)) :=
  A.powerset.powerset.filter (fun C => IsClusterCollection C ∧ C.sup id = A)

theorem mem_partitionsOf {A : Finset J} {C : Finset (Finset J)} :
    C ∈ partitionsOf A
      ↔ (∀ B ∈ C, B ⊆ A) ∧ IsClusterCollection C ∧ C.sup id = A := by
  unfold partitionsOf
  rw [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨hpow, hC, hsup⟩
    exact ⟨fun B hB => Finset.mem_powerset.mp (hpow hB), hC, hsup⟩
  · rintro ⟨hsub, hC, hsup⟩
    exact ⟨fun B hB => Finset.mem_powerset.mpr (hsub B hB), hC, hsup⟩

/-- Die einzige Partition der leeren Menge ist die leere Kollektion. -/
theorem partitionsOf_empty : partitionsOf (∅ : Finset J) = {∅} := by
  ext C
  rw [mem_partitionsOf, Finset.mem_singleton]
  constructor
  · rintro ⟨hsub, hC, -⟩
    rw [Finset.eq_empty_iff_forall_notMem]
    intro B hB
    have hne := hC.1 B hB
    have hBe : B = ∅ := Finset.subset_empty.mp (hsub B hB)
    exact Finset.not_nonempty_empty (hBe ▸ hne)
  · rintro rfl
    refine ⟨fun B hB => absurd hB (Finset.notMem_empty B),
      ⟨fun B hB => absurd hB (Finset.notMem_empty B),
       fun B₁ h₁ => absurd h₁ (Finset.notMem_empty B₁)⟩, ?_⟩
    rw [Finset.sup_empty]
    rfl

/-- Die Vereinigung einer Kollektion als `biUnion`. -/
theorem sup_id_eq_biUnion (C : Finset (Finset J)) :
    C.sup id = C.biUnion id :=
  (Finset.sup_eq_biUnion C id)

/-! ## Festgenagelte Belegungen -/

variable [Fintype J]

/-- Belegungen `J → ι` mit Werten in `Λ` auf `K` und dem festen Wert
`γ⋆` außerhalb von `K`. -/
noncomputable def pinnedTuples (Λ : Finset ι) (γstar : ι) (K : Finset J) :
    Finset (J → ι) :=
  Fintype.piFinset (fun j => if j ∈ K then Λ else {γstar})

omit [DecidableEq ι] in
theorem mem_pinnedTuples {Λ : Finset ι} {γstar : ι} {K : Finset J}
    {h : J → ι} :
    h ∈ pinnedTuples Λ γstar K
      ↔ (∀ j ∈ K, h j ∈ Λ) ∧ ∀ j ∉ K, h j = γstar := by
  unfold pinnedTuples
  rw [Fintype.mem_piFinset]
  constructor
  · intro hall
    constructor
    · intro j hj
      have := hall j
      rwa [if_pos hj] at this
    · intro j hj
      have := hall j
      rwa [if_neg hj, Finset.mem_singleton] at this
  · rintro ⟨hin, hout⟩ j
    by_cases hj : j ∈ K
    · rw [if_pos hj]
      exact hin j hj
    · rw [if_neg hj, Finset.mem_singleton]
      exact hout j hj

omit [DecidableEq ι] in
/-- Über der leeren Blockmenge gibt es genau die konstante Belegung. -/
theorem pinnedTuples_empty (Λ : Finset ι) (γstar : ι) :
    pinnedTuples Λ γstar (∅ : Finset J) = {fun _ => γstar} := by
  ext h
  rw [mem_pinnedTuples, Finset.mem_singleton]
  constructor
  · rintro ⟨-, hout⟩
    funext j
    exact hout j (Finset.notMem_empty j)
  · rintro rfl
    exact ⟨fun j hj => absurd hj (Finset.notMem_empty j), fun _ _ => rfl⟩

/-- Kombinieren zweier Belegungen entlang einer Blockmenge. -/
def combineOn (B : Finset J) (h₁ h₂ : J → ι) : J → ι :=
  fun j => if j ∈ B then h₁ j else h₂ j

/-- Einschränken einer Belegung auf eine Blockmenge (außerhalb `γ⋆`). -/
def restrictOn (B : Finset J) (γstar : ι) (h : J → ι) : J → ι :=
  fun j => if j ∈ B then h j else γstar

omit [DecidableEq ι] in
theorem restrictOn_mem_pinnedTuples {Λ : Finset ι} {γstar : ι}
    {K B : Finset J} {h : J → ι} (hB : B ⊆ K)
    (hh : h ∈ pinnedTuples Λ γstar K) :
    restrictOn B γstar h ∈ pinnedTuples Λ γstar B := by
  obtain ⟨hin, -⟩ := mem_pinnedTuples.mp hh
  refine mem_pinnedTuples.mpr ⟨fun j hj => ?_, fun j hj => ?_⟩
  · rw [restrictOn, if_pos hj]
    exact hin j (hB hj)
  · rw [restrictOn, if_neg hj]

/-! ## Die Tupelsummen -/

/-- Tupelsumme mit Unabhängigkeits-Indikator: die Ordnung-`|K|`-Schicht
der Zustandssumme in Tupelform. -/
noncomputable def tupleZ (w : ι → ℝ) (Λ : Finset ι) (γstar : ι)
    (K : Finset J) : ℝ :=
  ∑ h ∈ pinnedTuples Λ γstar K, (∏ j ∈ K, w (h j)) *
    (if Indep (P.pull h) K then 1 else 0)

/-- Tupelsumme mit Ursell-Gewicht: der Block-Beitrag der Cluster-Reihe
in Tupelform. -/
noncomputable def tupleU (w : ι → ℝ) (Λ : Finset ι) (γstar : ι)
    (B : Finset J) : ℝ :=
  ∑ h ∈ pinnedTuples Λ γstar B, (∏ j ∈ B, w (h j)) *
    (ursellSetSum (P.pull h) B : ℝ)

omit [DecidableEq ι] in
/-- Die leere Tupelsumme ist `1`. -/
theorem tupleZ_empty (w : ι → ℝ) (Λ : Finset ι) (γstar : ι) :
    tupleZ P w Λ γstar (∅ : Finset J) = 1 := by
  unfold tupleZ
  rw [pinnedTuples_empty, Finset.sum_singleton, Finset.prod_empty, one_mul,
    if_pos]
  intro γ hγ
  exact absurd hγ (Finset.notMem_empty γ)

/-! ## Lokalität in der Belegung -/

omit [DecidableEq ι] [Fintype J] in
/-- Die Unverträglichkeitskanten des zurückgezogenen Systems innerhalb
`B` hängen nur von der Belegung auf `B` ab. -/
theorem incompatEdges_pull_congr {h h' : J → ι} {B : Finset J}
    (hagree : ∀ j ∈ B, h j = h' j) :
    incompatEdges (P.pull h) B = incompatEdges (P.pull h') B := by
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    rw [mem_incompatEdges, mem_incompatEdges]
    constructor
    · rintro ⟨hu, hv, hne, hinc⟩
      refine ⟨hu, hv, hne, ?_⟩
      show P.incomp (h' u) (h' v) = true
      rw [← hagree u hu, ← hagree v hv]
      exact hinc
    · rintro ⟨hu, hv, hne, hinc⟩
      refine ⟨hu, hv, hne, ?_⟩
      show P.incomp (h u) (h v) = true
      rw [hagree u hu, hagree v hv]
      exact hinc

omit [Fintype J] in
/-- Die mengenwertige Ursell-Summe hängt nur von den Kanten innerhalb
des Blocks ab. -/
theorem ursellSetSum_congr_edges {R : Type*} [CommRing R]
    {Q Q' : PolymerSystem J} {B : Finset J}
    (h : incompatEdges Q B = incompatEdges Q' B) :
    (ursellSetSum Q B : R) = ursellSetSum Q' B := by
  unfold ursellSetSum
  rw [h]

omit [DecidableEq ι] [Fintype J] in
/-- Die Ursell-Summe des zurückgezogenen Systems innerhalb `B` hängt
nur von der Belegung auf `B` ab. -/
theorem ursellSetSum_pull_congr {R : Type*} [CommRing R] {h h' : J → ι}
    {B : Finset J} (hagree : ∀ j ∈ B, h j = h' j) :
    (ursellSetSum (P.pull h) B : R) = ursellSetSum (P.pull h') B :=
  ursellSetSum_congr_edges (incompatEdges_pull_congr P hagree)

omit [Fintype J] in
/-- Ganzzahl-Einbettung der mengenwertigen Ursell-Summe. -/
theorem intCast_ursellSetSum {R : Type*} [CommRing R] (Q : PolymerSystem J)
    (B : Finset J) :
    ((ursellSetSum Q B : ℤ) : R) = ursellSetSum Q B := by
  unfold ursellSetSum
  push_cast
  rfl

omit [DecidableEq ι] [DecidableEq J] [Fintype J] in
/-- Unabhängigkeit unter dem zurückgezogenen System hängt nur von der
Belegung auf der Blockmenge ab. -/
theorem indep_pull_congr {h h' : J → ι} {K : Finset J}
    (hagree : ∀ j ∈ K, h j = h' j) :
    Indep (P.pull h) K ↔ Indep (P.pull h') K := by
  constructor <;> intro hI i hi j hj hne
  · have := hI i hi j hj hne
    show P.incomp (h' i) (h' j) = false
    rw [← hagree i hi, ← hagree j hj]
    exact this
  · have := hI i hi j hj hne
    show P.incomp (h i) (h j) = false
    rw [hagree i hi, hagree j hj]
    exact this

/-! ## Kompositionen -/

/-- Die Kompositionen von `m` in `k` positive Teile, als Tupel. -/
noncomputable def compositionsF (m k : ℕ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset fun _ : Fin k => Finset.range (m + 1)).filter
    (fun c => (∀ i, c i ≠ 0) ∧ ∑ i, c i = m)

theorem mem_compositionsF {m k : ℕ} {c : Fin k → ℕ} :
    c ∈ compositionsF m k ↔ (∀ i, c i ≠ 0) ∧ ∑ i, c i = m := by
  unfold compositionsF
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨-, hpos, hsum⟩
    exact ⟨hpos, hsum⟩
  · rintro ⟨hpos, hsum⟩
    refine ⟨fun i => Finset.mem_range.mpr ?_, hpos, hsum⟩
    have hle : c i ≤ ∑ j, c j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (c j)) (Finset.mem_univ i)
    omega

/-- In einer Komposition von `m` in positive Teile gibt es höchstens `m`
Teile. -/
theorem card_le_of_mem_compositionsF {m k : ℕ} {c : Fin k → ℕ}
    (hc : c ∈ compositionsF m k) : k ≤ m := by
  obtain ⟨hpos, hsum⟩ := mem_compositionsF.mp hc
  calc k = ∑ _i : Fin k, 1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
          mul_one]
    _ ≤ ∑ i, c i := Finset.sum_le_sum fun i _ => Nat.one_le_iff_ne_zero.mpr (hpos i)
    _ = m := hsum

end ClusterExpansion
