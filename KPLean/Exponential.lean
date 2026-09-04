/-
Copyright (c) 2026 Dennis Michael Heine. All rights reserved.
Released under the CC BY-NC-SA 4.0 license as described in the file LICENSE.
Authors: Dennis Michael Heine
-/
import KPLean.ClusterSeries
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Die Exponentialformel: `log Z` als Cluster-Reihe

Die Bausteine der Identifikation `log Z Λ = clusterSeries P w Λ` im
Konvergenzregime. Grundbegriffe:

* `PolymerSystem.pull`: das entlang einer Belegung `h : J → ι`
  zurückgezogene Polymersystem auf der Indexmenge `J`;
* `partitionsOf A`: die Partitionen von `A` als Cluster-Kollektionen
  mit Vereinigung `A`;
* `pinnedTuples Λ γ⋆ K`: Belegungen `J → ι` mit Werten in `Λ` auf `K`
  und Wert `γ⋆` außerhalb — die endliche Indexmenge der Tupelsummen;
* `tupleZ`, `tupleU`: die Tupelsummen der Ordnung `|K|` mit
  Unabhängigkeits-Indikator bzw. Ursell-Gewicht;
* `compositionsF m k`: die Kompositionen von `m` in `k` positive Teile.

Darauf die Beweiskette:

* `indep_indicator_eq_sum_partitions`: der **Unabhängigkeits-Indikator
  als Partitionssumme** `[Indep Q A] = ∑_{Partitionen von A} ∏ φ(B)` —
  Koeffizientenvergleich beim Grad `|A|` in der Cluster-Faktorisierung
  über `Polynomial ℤ`;
* `tupleZ_eq_sum_partitions`: die **Blockzerlegung**
  `tupleZ K = ∑_{Partitionen von K} ∏ tupleU B` — Belegungssummen
  faktorisieren über disjunkte Blöcke;
* `tupleU_eq_clusterOrderSum`: die **Blockreduktion**
  `tupleU B = clusterOrderSum (|B| - 1)` — über die
  Ordnungsbijektion `Fin |B| ≃o B` und das Brückenlemma;
* `tupleZ_univ_eq`, `Z_eq_sum_tupleZ`: die **Schichtzählung**
  `tupleZ (univ : Fin m) = m! · (m-Schicht von Z)`, also
  `Z = ∑_m tupleZ_m / m!`;
* `exp_tsum_eq`: der **analytische Exponentialschritt** — `exp` einer
  absolut konvergenten Reihe als nach Gesamtgewicht umgruppierte
  Kompositionssumme.
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

omit [DecidableEq ι] [Fintype J] in
/-- Die Blockgrößen einer Partition addieren sich zur Kardinalität der
Grundmenge. -/
theorem sum_card_of_mem_partitionsOf {A : Finset J} {C : Finset (Finset J)}
    (hC : C ∈ partitionsOf A) : ∑ B ∈ C, B.card = A.card := by
  obtain ⟨-, hICC, hsup⟩ := mem_partitionsOf.mp hC
  rw [← hsup, sup_id_eq_biUnion]
  exact (Finset.card_biUnion fun x hx y hy hxy => hICC.2 x hx y hy hxy).symm

omit [DecidableEq ι] [Fintype J] in
/-- Eine Partition von `A` hat höchstens `|A|` Blöcke: die Blöcke sind
nichtleer, ihre Größen addieren sich zu `|A|`. -/
theorem card_le_of_mem_partitionsOf {A : Finset J} {C : Finset (Finset J)}
    (hC : C ∈ partitionsOf A) : C.card ≤ A.card := by
  obtain ⟨-, hICC, -⟩ := mem_partitionsOf.mp hC
  calc C.card = ∑ _B ∈ C, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    _ ≤ ∑ B ∈ C, B.card :=
        Finset.sum_le_sum fun B hB => Finset.card_pos.mpr (hICC.1 B hB)
    _ = A.card := sum_card_of_mem_partitionsOf hC

/-! ## Geordnete Partitionen -/

/-- Geordnete Partitionen: `k`-Tupel paarweise disjunkter, nichtleerer
Blöcke mit Vereinigung `A`. -/
noncomputable def orderedPartitionsF (A : Finset J) (k : ℕ) :
    Finset (Fin k → Finset J) :=
  (Fintype.piFinset fun _ : Fin k => A.powerset).filter
    (fun T => (∀ i, (T i).Nonempty) ∧ (∀ i j, i ≠ j → Disjoint (T i) (T j)) ∧
      Finset.univ.sup T = A)

omit [DecidableEq ι] [Fintype J] in
theorem mem_orderedPartitionsF {A : Finset J} {k : ℕ} {T : Fin k → Finset J} :
    T ∈ orderedPartitionsF A k
      ↔ (∀ i, (T i).Nonempty) ∧ (∀ i j, i ≠ j → Disjoint (T i) (T j)) ∧
          Finset.univ.sup T = A := by
  unfold orderedPartitionsF
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨-, hne, hdisj, hsup⟩
    exact ⟨hne, hdisj, hsup⟩
  · rintro ⟨hne, hdisj, hsup⟩
    refine ⟨fun i => Finset.mem_powerset.mpr ?_, hne, hdisj, hsup⟩
    rw [← hsup]
    exact Finset.le_sup (Finset.mem_univ i)

omit [DecidableEq ι] [Fintype J] in
/-- Die Blockgrößen einer geordneten Partition addieren sich zur
Kardinalität der Grundmenge. -/
theorem sum_card_of_mem_orderedPartitionsF {A : Finset J} {k : ℕ}
    {T : Fin k → Finset J} (hT : T ∈ orderedPartitionsF A k) :
    ∑ i, (T i).card = A.card := by
  obtain ⟨-, hdisj, hsup⟩ := mem_orderedPartitionsF.mp hT
  have hbi : Finset.univ.sup T = Finset.univ.biUnion T :=
    Finset.sup_eq_biUnion Finset.univ T
  rw [← hsup, hbi]
  exact (Finset.card_biUnion fun x _ y _ hxy => hdisj x y hxy).symm

omit [DecidableEq ι] [Fintype J] in
/-- Die Blockgrößen einer geordneten Partition bilden eine Komposition
von `|A|`. -/
theorem card_mem_compositionsF {A : Finset J} {k : ℕ}
    {T : Fin k → Finset J} (hT : T ∈ orderedPartitionsF A k) :
    (fun i => (T i).card) ∈ compositionsF A.card k := by
  obtain ⟨hne, -, -⟩ := mem_orderedPartitionsF.mp hT
  exact mem_compositionsF.mpr
    ⟨fun i => (Finset.card_pos.mpr (hne i)).ne',
     sum_card_of_mem_orderedPartitionsF hT⟩

/-! ## Die Partitionsidentität des Unabhängigkeits-Indikators -/

omit [DecidableEq ι] [Fintype J] in
/-- Ganzzahlige Fassung der Partitionsidentität: der
Unabhängigkeits-Indikator als Summe über alle Partitionen von `A` mit
Ursell-Blockgewichten. Beweis durch Koeffizientenvergleich beim Grad
`|A|` in der Cluster-Faktorisierung über `Polynomial ℤ` mit dem
konstanten Gewicht `X`. -/
private theorem indep_indicator_eq_sum_partitions_int
    (Q : PolymerSystem J) (A : Finset J) :
    (if Indep Q A then (1 : ℤ) else 0)
      = ∑ C ∈ partitionsOf A, ∏ B ∈ C, (ursellSetSum Q B : ℤ) := by
  -- Linke Seite: der `|A|`-Koeffizient der Zustandssumme ist der
  -- Indikator, denn nur `S = A` erreicht den vollen Grad.
  have hL : (Z Q (fun _ => (Polynomial.X : Polynomial ℤ)) A).coeff A.card
      = (if Indep Q A then (1 : ℤ) else 0) := by
    unfold Z
    rw [Polynomial.finsetSum_coeff]
    have hterm : ∀ S ∈ A.powerset.filter (fun S => Indep Q S),
        (∏ _γ ∈ S, (Polynomial.X : Polynomial ℤ)).coeff A.card
          = if A.card = S.card then (1 : ℤ) else 0 := by
      intro S _
      rw [Finset.prod_const, Polynomial.coeff_X_pow]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
    have hset : (A.powerset.filter (fun S => Indep Q S)).filter
        (fun S => A.card = S.card)
        = if Indep Q A then ({A} : Finset (Finset J)) else ∅ := by
      ext S
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_powerset]
      constructor
      · rintro ⟨⟨hSA, hind⟩, hcard⟩
        have hSeq : S = A := Finset.eq_of_subset_of_card_le hSA hcard.le
        subst hSeq
        rw [if_pos hind]
        exact Finset.mem_singleton_self S
      · intro hS
        by_cases hind : Indep Q A
        · rw [if_pos hind, Finset.mem_singleton] at hS
          subst hS
          exact ⟨⟨Finset.Subset.rfl, hind⟩, rfl⟩
        · rw [if_neg hind] at hS
          exact absurd hS (Finset.notMem_empty S)
    rw [hset]
    by_cases hind : Indep Q A
    · rw [if_pos hind, if_pos hind, Finset.sum_singleton]
    · rw [if_neg hind, if_neg hind, Finset.sum_empty]
  -- Rechte Seite: der `|A|`-Koeffizient eines Kollektionsbeitrags
  -- überlebt genau für die Partitionen von `A`.
  have hR : (∑ C ∈ A.powerset.powerset.filter IsClusterCollection,
        ∏ B ∈ C, ((∏ _γ ∈ B, (Polynomial.X : Polynomial ℤ))
          * ursellSetSum Q B)).coeff A.card
      = ∑ C ∈ partitionsOf A, ∏ B ∈ C, (ursellSetSum Q B : ℤ) := by
    rw [Polynomial.finsetSum_coeff]
    have hterm : ∀ C ∈ A.powerset.powerset.filter IsClusterCollection,
        (∏ B ∈ C, ((∏ _γ ∈ B, (Polynomial.X : Polynomial ℤ))
            * ursellSetSum Q B)).coeff A.card
          = if C.sup id = A then ∏ B ∈ C, (ursellSetSum Q B : ℤ)
            else 0 := by
      intro C hC
      obtain ⟨hCpp, hICC⟩ := Finset.mem_filter.mp hC
      -- Die Blockkardinalitäten addieren sich zur Kardinalität der
      -- Vereinigung, da die Blöcke paarweise disjunkt sind.
      have hcardsum : ∑ B ∈ C, B.card = (C.sup id).card := by
        rw [sup_id_eq_biUnion]
        exact (Finset.card_biUnion
          (fun x hx y hy hxy => hICC.2 x hx y hy hxy)).symm
      -- Der Kollektionsbeitrag ist `X ^ |⋃ C| · C(∏ φ(B))`.
      have hCcast : ∀ B : Finset J, (ursellSetSum Q B : Polynomial ℤ)
          = Polynomial.C (ursellSetSum Q B : ℤ) := by
        intro B
        rw [← intCast_ursellSetSum (R := Polynomial ℤ) Q B]
        simp
      have hprod : ∏ B ∈ C, ((∏ _γ ∈ B, (Polynomial.X : Polynomial ℤ))
            * ursellSetSum Q B)
          = Polynomial.C (∏ B ∈ C, (ursellSetSum Q B : ℤ))
            * Polynomial.X ^ (C.sup id).card := by
        calc ∏ B ∈ C, ((∏ _γ ∈ B, (Polynomial.X : Polynomial ℤ))
              * ursellSetSum Q B)
            = ∏ B ∈ C, (Polynomial.X ^ B.card
                * Polynomial.C (ursellSetSum Q B : ℤ)) := by
              refine Finset.prod_congr rfl fun B _ => ?_
              rw [Finset.prod_const, hCcast]
          _ = (∏ B ∈ C, Polynomial.X ^ B.card)
                * ∏ B ∈ C, Polynomial.C (ursellSetSum Q B : ℤ) :=
              Finset.prod_mul_distrib
          _ = Polynomial.C (∏ B ∈ C, (ursellSetSum Q B : ℤ))
                * Polynomial.X ^ (C.sup id).card := by
              rw [Finset.prod_pow_eq_pow_sum, hcardsum, ← map_prod, mul_comm]
      rw [hprod, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      have hsub : C.sup id ⊆ A := Finset.sup_le fun B hB =>
        Finset.mem_powerset.mp (Finset.mem_powerset.mp hCpp hB)
      by_cases hEq : C.sup id = A
      · rw [if_pos hEq, if_pos (by rw [hEq]), mul_one]
      · rw [if_neg hEq, if_neg (fun hcard =>
          hEq (Finset.eq_of_subset_of_card_le hsub hcard.le)), mul_zero]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
    have hset : (A.powerset.powerset.filter IsClusterCollection).filter
        (fun C => C.sup id = A) = partitionsOf A := by
      ext C
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_powerset,
        mem_partitionsOf]
      constructor
      · rintro ⟨⟨hpp, hICC⟩, hsup⟩
        exact ⟨fun B hB => Finset.mem_powerset.mp (hpp hB), hICC, hsup⟩
      · rintro ⟨hsub, hICC, hsup⟩
        exact ⟨⟨fun B hB => Finset.mem_powerset.mpr (hsub B hB), hICC⟩, hsup⟩
    rw [hset]
  rw [← hL, ← hR]
  exact congrArg (fun p => p.coeff A.card)
    (Z_eq_sum_clusterCollections Q (fun _ => (Polynomial.X : Polynomial ℤ)) A)

omit [DecidableEq ι] [Fintype J] in
/-- **Partitionsidentität des Unabhängigkeits-Indikators**: in jedem
kommutativen Ring ist der Indikator von `Indep Q A` die Summe über alle
Partitionen von `A` der Produkte der Ursell-Blockgewichte. Der Beweis
extrahiert den Koeffizienten beim Grad `|A|` aus der
Cluster-Faktorisierung über `Polynomial ℤ` und hebt die ganzzahlige
Identität per `Int.cast` nach `R`. -/
theorem indep_indicator_eq_sum_partitions {R : Type*} [CommRing R]
    (Q : PolymerSystem J) (A : Finset J) :
    (if Indep Q A then (1 : R) else 0)
      = ∑ C ∈ partitionsOf A, ∏ B ∈ C, ursellSetSum Q B := by
  have h := congrArg (Int.cast : ℤ → R)
    (indep_indicator_eq_sum_partitions_int Q A)
  rw [apply_ite (Int.cast : ℤ → R), Int.cast_one, Int.cast_zero] at h
  rw [h, Int.cast_sum]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [Int.cast_prod]
  exact Finset.prod_congr rfl fun B _ => intCast_ursellSetSum Q B

/-! ## Blockzerlegung der Belegungssummen -/

omit [DecidableEq ι] in
/-- Aufspalten einer festgenagelten Belegungssumme entlang einer
disjunkten Zerlegung `B ∪ S` des Trägers. -/
theorem sum_pinnedTuples_union (Λ : Finset ι) (γstar : ι) {B S : Finset J}
    (hdisj : Disjoint B S) (φ : (J → ι) → ℝ) :
    ∑ h ∈ pinnedTuples Λ γstar (B ∪ S), φ h
      = ∑ p ∈ pinnedTuples Λ γstar B ×ˢ pinnedTuples Λ γstar S,
          φ (combineOn B p.1 p.2) := by
  refine Finset.sum_nbij'
    (fun h => (restrictOn B γstar h, restrictOn S γstar h))
    (fun p => combineOn B p.1 p.2) ?_ ?_ ?_ ?_ ?_
  · intro h hh
    exact Finset.mem_product.mpr
      ⟨restrictOn_mem_pinnedTuples Finset.subset_union_left hh,
       restrictOn_mem_pinnedTuples Finset.subset_union_right hh⟩
  · rintro ⟨h₁, h₂⟩ hp
    rw [Finset.mem_product] at hp
    obtain ⟨hin₁, hout₁⟩ := mem_pinnedTuples.mp hp.1
    obtain ⟨hin₂, hout₂⟩ := mem_pinnedTuples.mp hp.2
    refine mem_pinnedTuples.mpr ⟨fun j hj => ?_, fun j hj => ?_⟩
    · rcases Finset.mem_union.mp hj with hjB | hjS
      · simp only [combineOn]
        rw [if_pos hjB]
        exact hin₁ j hjB
      · by_cases hjB : j ∈ B
        · simp only [combineOn]
          rw [if_pos hjB]
          exact hin₁ j hjB
        · simp only [combineOn]
          rw [if_neg hjB]
          exact hin₂ j hjS
    · rw [Finset.mem_union] at hj
      push Not at hj
      simp only [combineOn]
      rw [if_neg hj.1]
      exact hout₂ j hj.2
  · intro h hh
    obtain ⟨-, hout⟩ := mem_pinnedTuples.mp hh
    funext j
    simp only [combineOn, restrictOn]
    by_cases hjB : j ∈ B
    · rw [if_pos hjB, if_pos hjB]
    · rw [if_neg hjB]
      by_cases hjS : j ∈ S
      · rw [if_pos hjS]
      · rw [if_neg hjS]
        exact (hout j (fun hmem => by
          rcases Finset.mem_union.mp hmem with h1 | h1
          · exact hjB h1
          · exact hjS h1)).symm
  · rintro ⟨h₁, h₂⟩ hp
    rw [Finset.mem_product] at hp
    obtain ⟨-, hout₁⟩ := mem_pinnedTuples.mp hp.1
    obtain ⟨-, hout₂⟩ := mem_pinnedTuples.mp hp.2
    have e₁ : restrictOn B γstar (combineOn B h₁ h₂) = h₁ := by
      funext j
      simp only [restrictOn, combineOn]
      by_cases hjB : j ∈ B
      · rw [if_pos hjB, if_pos hjB]
      · rw [if_neg hjB]
        exact (hout₁ j hjB).symm
    have e₂ : restrictOn S γstar (combineOn B h₁ h₂) = h₂ := by
      funext j
      simp only [restrictOn, combineOn]
      by_cases hjS : j ∈ S
      · have hjB : j ∉ B := Finset.disjoint_right.mp hdisj hjS
        rw [if_pos hjS, if_neg hjB]
      · rw [if_neg hjS]
        exact (hout₂ j hjS).symm
    exact Prod.ext e₁ e₂
  · intro h hh
    obtain ⟨-, hout⟩ := mem_pinnedTuples.mp hh
    have e : combineOn B (restrictOn B γstar h) (restrictOn S γstar h) = h := by
      funext j
      simp only [combineOn, restrictOn]
      by_cases hjB : j ∈ B
      · rw [if_pos hjB, if_pos hjB]
      · rw [if_neg hjB]
        by_cases hjS : j ∈ S
        · rw [if_pos hjS]
        · rw [if_neg hjS]
          exact (hout j (fun hmem => by
            rcases Finset.mem_union.mp hmem with h1 | h1
            · exact hjB h1
            · exact hjS h1)).symm
    rw [e]

omit [DecidableEq ι] in
/-- Blockzerlegung: eine festgenagelte Belegungssumme eines Produkts
blocklokaler Funktionale über eine disjunkte Kollektion faktorisiert
in das Produkt der Blocksummen. -/
theorem sum_pinnedTuples_prod_blocks (Λ : Finset ι) (γstar : ι)
    (C : Finset (Finset J))
    (hdisj : ∀ B₁ ∈ C, ∀ B₂ ∈ C, B₁ ≠ B₂ → Disjoint B₁ B₂)
    (F : Finset J → (J → ι) → ℝ)
    (hF : ∀ B ∈ C, ∀ h h' : J → ι, (∀ j ∈ B, h j = h' j) → F B h = F B h') :
    ∑ h ∈ pinnedTuples Λ γstar (C.sup id), ∏ B ∈ C, F B h
      = ∏ B ∈ C, ∑ h ∈ pinnedTuples Λ γstar B, F B h := by
  induction C using Finset.induction_on with
  | empty =>
    rw [Finset.sup_empty, Finset.prod_empty]
    have hbot : (⊥ : Finset J) = (∅ : Finset J) := rfl
    rw [hbot, pinnedTuples_empty, Finset.sum_singleton, Finset.prod_empty]
  | @insert B₀ C hB₀C IH =>
    have hdisj' : ∀ B₁ ∈ C, ∀ B₂ ∈ C, B₁ ≠ B₂ → Disjoint B₁ B₂ :=
      fun B₁ h₁ B₂ h₂ hne =>
        hdisj B₁ (Finset.mem_insert_of_mem h₁) B₂ (Finset.mem_insert_of_mem h₂) hne
    have hF' : ∀ B ∈ C, ∀ h h' : J → ι, (∀ j ∈ B, h j = h' j) → F B h = F B h' :=
      fun B hB => hF B (Finset.mem_insert_of_mem hB)
    have hB₀disj : Disjoint B₀ (C.sup id) := by
      rw [Finset.disjoint_sup_right]
      intro B hB
      have hne : B₀ ≠ B := fun h => hB₀C (h ▸ hB)
      exact hdisj B₀ (Finset.mem_insert_self B₀ C) B
        (Finset.mem_insert_of_mem hB) hne
    rw [Finset.sup_insert, id_eq]
    calc ∑ h ∈ pinnedTuples Λ γstar (B₀ ∪ C.sup id), ∏ B ∈ insert B₀ C, F B h
        = ∑ p ∈ pinnedTuples Λ γstar B₀ ×ˢ pinnedTuples Λ γstar (C.sup id),
            ∏ B ∈ insert B₀ C, F B (combineOn B₀ p.1 p.2) :=
          sum_pinnedTuples_union Λ γstar hB₀disj _
      _ = ∑ p ∈ pinnedTuples Λ γstar B₀ ×ˢ pinnedTuples Λ γstar (C.sup id),
            F B₀ p.1 * ∏ B ∈ C, F B p.2 := by
          refine Finset.sum_congr rfl fun p hp => ?_
          rw [Finset.mem_product] at hp
          rw [Finset.prod_insert hB₀C]
          congr 1
          · refine hF B₀ (Finset.mem_insert_self B₀ C) _ _ fun j hj => ?_
            rw [combineOn, if_pos hj]
          · refine Finset.prod_congr rfl fun B hB => ?_
            refine hF B (Finset.mem_insert_of_mem hB) _ _ fun j hj => ?_
            have hjB₀ : j ∉ B₀ := by
              have hjsup : j ∈ C.sup id := by
                have hle : id B ≤ C.sup id := Finset.le_sup hB
                exact hle hj
              exact Finset.disjoint_right.mp hB₀disj hjsup
            rw [combineOn, if_neg hjB₀]
      _ = (∑ h ∈ pinnedTuples Λ γstar B₀, F B₀ h) *
            ∑ h ∈ pinnedTuples Λ γstar (C.sup id), ∏ B ∈ C, F B h := by
          rw [Finset.sum_product]
          dsimp only
          rw [← Finset.sum_mul_sum]
      _ = ∏ B ∈ insert B₀ C, ∑ h ∈ pinnedTuples Λ γstar B, F B h := by
          rw [IH hdisj' hF', Finset.prod_insert hB₀C]

omit [DecidableEq ι] in
/-- **Tupel-Faktorisierung**: die Tupelsumme mit
Unabhängigkeits-Indikator zerfällt in die Summe über die Partitionen
des Trägers der Produkte der Ursell-Blocksummen. -/
theorem tupleZ_eq_sum_partitions (w : ι → ℝ) (Λ : Finset ι)
    (γstar : ι) (K : Finset J) :
    tupleZ P w Λ γstar K
      = ∑ C ∈ partitionsOf K, ∏ B ∈ C, tupleU P w Λ γstar B := by
  unfold tupleZ
  rw [Finset.sum_congr rfl (fun h _ => by
      rw [indep_indicator_eq_sum_partitions (P.pull h) K, Finset.mul_sum]),
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun C hC => ?_
  obtain ⟨-, hICC, hsup⟩ := mem_partitionsOf.mp hC
  have hdisj := hICC.2
  -- Gewichtsprodukt über die Blöcke aufspalten.
  have hprod : ∀ h : J → ι,
      ∏ j ∈ K, w (h j) = ∏ B ∈ C, ∏ j ∈ B, w (h j) := by
    intro h
    have hpd : (↑C : Set (Finset J)).PairwiseDisjoint id :=
      fun B₁ h₁ B₂ h₂ hne =>
        hdisj B₁ (Finset.mem_coe.mp h₁) B₂ (Finset.mem_coe.mp h₂) hne
    rw [← hsup, sup_id_eq_biUnion, Finset.prod_biUnion hpd]
    simp only [id_eq]
  have hstep : ∀ h : J → ι,
      (∏ j ∈ K, w (h j)) * ∏ B ∈ C, ursellSetSum (P.pull h) B
        = ∏ B ∈ C, ((∏ j ∈ B, w (h j)) * ursellSetSum (P.pull h) B) := by
    intro h
    rw [hprod h, ← Finset.prod_mul_distrib]
  have hloc : ∀ B ∈ C, ∀ h h' : J → ι, (∀ j ∈ B, h j = h' j) →
      (∏ j ∈ B, w (h j)) * ursellSetSum (P.pull h) B
        = (∏ j ∈ B, w (h' j)) * ursellSetSum (P.pull h') B := by
    intro B _ h h' hagree
    have h1 : ∏ j ∈ B, w (h j) = ∏ j ∈ B, w (h' j) :=
      Finset.prod_congr rfl fun j hj => by rw [hagree j hj]
    have h2 : (ursellSetSum (P.pull h) B : ℝ) = ursellSetSum (P.pull h') B :=
      ursellSetSum_pull_congr P hagree
    rw [h1, h2]
  have hkey := sum_pinnedTuples_prod_blocks (Λ := Λ) (γstar := γstar) C hdisj
    (fun B h => (∏ j ∈ B, w (h j)) * ursellSetSum (P.pull h) B) hloc
  rw [Finset.sum_congr rfl fun h _ => hstep h, ← hsup, hkey]
  rfl

/-! ## Blockreduktion: die Ursell-Tupelsumme eines Blocks -/

omit [DecidableEq ι] [DecidableEq J] [Fintype J] in
/-- Die Trägerkanten des zurückgezogenen Systems entlang `f` sind die
Trägerkanten des Originalsystems entlang `h ∘ f`. -/
theorem clusterEdges_pull {n : ℕ} (h : J → ι) (f : Fin n → J) :
    clusterEdges (P.pull h) f = clusterEdges P (h ∘ f) := by
  ext e
  induction e using Sym2.ind with
  | _ i j =>
    rw [mem_clusterEdges, mem_clusterEdges]
    rfl

omit [DecidableEq ι] in
/-- **Blockreduktion**: die Ursell-Tupelsumme eines nichtleeren Blocks
`B` ist der Reihenbeitrag der Ordnung `|B|`. Der Beweis transportiert
die Summationsbereiche entlang der Ordnungsbijektion
`Fin |B| ≃o B`: festgenagelte Belegungen entsprechen genau den
`|B|`-Tupeln aus `Λ`, und das Brückenlemma identifiziert die
mengenwertige Ursell-Summe des zurückgezogenen Systems mit der
Ursell-Funktion des Bildtupels. -/
theorem tupleU_eq_clusterOrderSum [LinearOrder J] (w : ι → ℝ) (Λ : Finset ι)
    (γstar : ι) {B : Finset J} (hB : B.Nonempty) :
    tupleU P w Λ γstar B = clusterOrderSum P w Λ (B.card - 1) := by
  obtain ⟨n, hn⟩ : ∃ n, B.card = n + 1 :=
    ⟨B.card - 1, by have := Finset.card_pos.mpr hB; omega⟩
  have hcard : B.card - 1 = n := by omega
  rw [hcard]
  set oi := B.orderIsoOfFin hn
  set f : Fin (n + 1) → J := fun i => (oi i : J)
  have hinj : Function.Injective f := fun a b hab =>
    oi.toEquiv.injective (Subtype.coe_injective hab)
  have hfB : ∀ i, f i ∈ B := fun i => (oi i).2
  have hfsymm : ∀ j, ∀ hj : j ∈ B, f (oi.symm ⟨j, hj⟩) = j := by
    intro j hj
    show ((oi (oi.symm ⟨j, hj⟩) : {x // x ∈ B}) : J) = j
    rw [OrderIso.apply_symm_apply]
  have hsymmf : ∀ i, ∀ hi : f i ∈ B, oi.symm ⟨f i, hi⟩ = i := by
    intro i hi
    have hval : (⟨f i, hi⟩ : {x // x ∈ B}) = oi i := Subtype.ext rfl
    rw [hval, OrderIso.symm_apply_apply]
  have himg : (Finset.univ : Finset (Fin (n + 1))).image f = B := by
    ext j
    rw [Finset.mem_image]
    constructor
    · rintro ⟨i, -, rfl⟩
      exact hfB i
    · intro hj
      exact ⟨oi.symm ⟨j, hj⟩, Finset.mem_univ _, hfsymm j hj⟩
  -- Brückenlemma: mengenwertige Ursell-Summe des Pullbacks = Ursell-Funktion
  -- des Bildtupels.
  have hUrsell : ∀ h : J → ι,
      (ursellSetSum (P.pull h) B : ℝ) = ((ursellInt P (h ∘ f) : ℤ) : ℝ) := by
    intro h
    have h1 : (ursellInt (P.pull h) f : ℤ) = ursellSetSum (P.pull h) B := by
      have h0 := ursellInt_eq_ursellSetSum (P.pull h) hinj
      rwa [himg] at h0
    have h2 : ursellInt (P.pull h) f = ursellInt P (h ∘ f) := by
      unfold ursellInt
      rw [clusterEdges_pull]
    rw [← intCast_ursellSetSum, ← h1, h2]
  -- Gewichtsprodukt entlang der Bijektion.
  have hprod : ∀ h : J → ι, ∏ j ∈ B, w (h j) = ∏ i, w (h (f i)) := by
    intro h
    rw [← himg, Finset.prod_image fun a _ b _ hab => hinj hab]
  unfold tupleU clusterOrderSum
  refine Finset.sum_nbij' (fun h => h ∘ f)
    (fun γ j => if hj : j ∈ B then γ (oi.symm ⟨j, hj⟩) else γstar)
    ?_ ?_ ?_ ?_ ?_
  -- Hinrichtung: festgenagelte Belegungen liefern Tupel aus `Λ`.
  · intro h hh
    exact Fintype.mem_piFinset.mpr fun i =>
      (mem_pinnedTuples.mp hh).1 (f i) (hfB i)
  -- Rückrichtung: Tupel liefern festgenagelte Belegungen.
  · intro γ hγ
    refine mem_pinnedTuples.mpr ⟨fun j hj => ?_, fun j hj => ?_⟩
    · show (if hj : j ∈ B then γ (oi.symm ⟨j, hj⟩) else γstar) ∈ Λ
      rw [dif_pos hj]
      exact Fintype.mem_piFinset.mp hγ _
    · show (if hj : j ∈ B then γ (oi.symm ⟨j, hj⟩) else γstar) = γstar
      rw [dif_neg hj]
  -- Linksinverse.
  · intro h hh
    funext j
    show (if hj : j ∈ B then (h ∘ f) (oi.symm ⟨j, hj⟩) else γstar) = h j
    by_cases hj : j ∈ B
    · rw [dif_pos hj]
      exact congrArg h (hfsymm j hj)
    · rw [dif_neg hj]
      exact ((mem_pinnedTuples.mp hh).2 j hj).symm
  -- Rechtsinverse.
  · intro γ _
    funext i
    show (if hj : f i ∈ B then γ (oi.symm ⟨f i, hj⟩) else γstar) = γ i
    rw [dif_pos (hfB i), hsymmf i (hfB i)]
  -- Die Summanden stimmen überein.
  · intro h _
    show (∏ j ∈ B, w (h j)) * (ursellSetSum (P.pull h) B : ℝ)
        = ((ursellInt P (h ∘ f) : ℤ) : ℝ) * ∏ i, w ((h ∘ f) i)
    rw [hUrsell h, hprod h]
    exact mul_comm _ _

/-! ## Schichtzählung: die Tupel-Z-Summe und `Z` -/

omit [DecidableEq ι] in
/-- Über der vollen Blockmenge sind die festgenagelten Belegungen genau
alle Tupel mit Werten in `Λ`. -/
theorem pinnedTuples_univ (Λ : Finset ι) (γstar : ι) (m : ℕ) :
    pinnedTuples Λ γstar (Finset.univ : Finset (Fin m))
      = Fintype.piFinset fun _ => Λ := by
  ext h
  rw [mem_pinnedTuples, Fintype.mem_piFinset]
  constructor
  · rintro ⟨hin, -⟩ j
    exact hin j (Finset.mem_univ j)
  · intro hall
    exact ⟨fun j _ => hall j, fun j hj => absurd (Finset.mem_univ j) hj⟩

/-- Unabhängigkeit des zurückgezogenen Systems auf ganz `Fin m` heißt:
die Belegung ist injektiv und ihr Bild unabhängig. -/
theorem indep_pull_univ_iff {m : ℕ} (h : Fin m → ι) :
    Indep (P.pull h) (Finset.univ : Finset (Fin m))
      ↔ Function.Injective h ∧ Indep P (Finset.univ.image h) := by
  constructor
  · intro hI
    have hinj : Function.Injective h := by
      intro i j hij
      by_contra hne
      have hfalse := hI i (Finset.mem_univ i) j (Finset.mem_univ j) hne
      have htrue : (P.pull h).incomp i j = true := by
        show P.incomp (h i) (h j) = true
        rw [hij]
        exact P.refl (h j)
      rw [hfalse] at htrue
      exact Bool.noConfusion htrue
    refine ⟨hinj, ?_⟩
    intro γ hγ δ hδ hne
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hγ
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hδ
    exact hI i (Finset.mem_univ i) j (Finset.mem_univ j)
      (fun hij => hne (congrArg h hij))
  · rintro ⟨hinj, hind⟩ i _ j _ hne
    show P.incomp (h i) (h j) = false
    exact hind (h i) (Finset.mem_image_of_mem h (Finset.mem_univ i))
      (h j) (Finset.mem_image_of_mem h (Finset.mem_univ j))
      (fun heq => hne (hinj heq))

/-- Faser-Charakterisierung: über einer unabhängigen Menge `S ⊆ Λ` besteht
die Faser genau aus den injektiven Belegungen mit Bild `S`. -/
private theorem mem_fiber_iff {Λ S : Finset ι} {m : ℕ} (hSsub : S ⊆ Λ)
    (hSind : Indep P S) (h : Fin m → ι) :
    h ∈ ((Fintype.piFinset fun _ : Fin m => Λ).filter
        (fun h => Function.Injective h ∧ Indep P (Finset.univ.image h))).filter
        (fun h => Finset.univ.image h = S)
      ↔ Function.Injective h ∧ Finset.univ.image h = S := by
  rw [Finset.mem_filter, Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨⟨-, hinj, -⟩, himg⟩
    exact ⟨hinj, himg⟩
  · rintro ⟨hinj, himg⟩
    refine ⟨⟨fun i =>
      hSsub (himg ▸ Finset.mem_image_of_mem h (Finset.mem_univ i)), hinj, ?_⟩,
      himg⟩
    rw [himg]
    exact hSind

/-- Faserkardinalität: die injektiven Belegungen `Fin m → ι` mit Bild `S`
(bei `|S| = m`) entsprechen den Einbettungen `Fin m ↪ S` — es gibt `m!`. -/
private theorem card_fiber_eq {Λ S : Finset ι} {m : ℕ} (hSsub : S ⊆ Λ)
    (hSind : Indep P S) (hScard : S.card = m) :
    (((Fintype.piFinset fun _ : Fin m => Λ).filter
        (fun h => Function.Injective h ∧ Indep P (Finset.univ.image h))).filter
        (fun h => Finset.univ.image h = S)).card
      = Nat.factorial m := by
  have hbij : (((Fintype.piFinset fun _ : Fin m => Λ).filter
      (fun h => Function.Injective h ∧ Indep P (Finset.univ.image h))).filter
      (fun h => Finset.univ.image h = S)).card
      = Fintype.card (Fin m ↪ {x // x ∈ S}) := by
    rw [← Finset.card_univ]
    refine Finset.card_bij'
      (fun h hh => ⟨fun i => ⟨h i, ?_⟩, ?_⟩)
      (fun e _ => fun i => (e i : ι)) ?_ ?_ ?_ ?_
    -- Werte liegen in `S`.
    · obtain ⟨-, himg⟩ := (mem_fiber_iff P hSsub hSind h).mp hh
      exact himg ▸ Finset.mem_image_of_mem h (Finset.mem_univ i)
    -- Injektivität der Einbettung.
    · obtain ⟨hinj, -⟩ := (mem_fiber_iff P hSsub hSind h).mp hh
      exact fun i j hij => hinj (congrArg Subtype.val hij)
    -- Hinrichtung: alles landet in `univ`.
    · exact fun h hh => Finset.mem_univ _
    -- Rückrichtung: `i ↦ e i` liegt in der Faser.
    · intro e _
      have hinj : Function.Injective (fun i => (e i : ι)) :=
        fun i j hij => e.injective (Subtype.val_injective hij)
      refine (mem_fiber_iff P hSsub hSind _).mpr ⟨hinj, ?_⟩
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro γ hγ
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hγ
        exact (e i).2
      · refine le_of_eq ?_
        rw [Finset.card_image_of_injective _ hinj, Finset.card_univ,
          Fintype.card_fin, hScard]
    -- Linksinverse.
    · intro h _
      rfl
    -- Rechtsinverse.
    · intro e _
      exact Function.Embedding.ext fun i => Subtype.ext rfl
  rw [hbij, Fintype.card_embedding_eq, Fintype.card_coe, Fintype.card_fin,
    hScard, Nat.descFactorial_self]

/-- Auswertung einer Faser: die injektiven Belegungen mit Bild `S`
summieren sich zu `m! · ∏_{γ ∈ S} w γ`. -/
private theorem fiber_sum_eq (w : ι → ℝ) {Λ S : Finset ι} {m : ℕ}
    (hSsub : S ⊆ Λ) (hSind : Indep P S) (hScard : S.card = m) :
    ∑ h ∈ ((Fintype.piFinset fun _ : Fin m => Λ).filter
        (fun h => Function.Injective h ∧ Indep P (Finset.univ.image h))).filter
        (fun h => Finset.univ.image h = S),
      ∏ j, w (h j)
    = (Nat.factorial m : ℝ) * ∏ γ ∈ S, w γ := by
  have hval : ∀ h ∈ ((Fintype.piFinset fun _ : Fin m => Λ).filter
      (fun h => Function.Injective h ∧ Indep P (Finset.univ.image h))).filter
      (fun h => Finset.univ.image h = S),
      ∏ j, w (h j) = ∏ γ ∈ S, w γ := by
    intro h hh
    obtain ⟨hinj, himg⟩ := (mem_fiber_iff P hSsub hSind h).mp hh
    rw [← himg, Finset.prod_image (fun i _ j _ hij => hinj hij)]
  rw [Finset.sum_congr rfl hval, Finset.sum_const,
    card_fiber_eq P hSsub hSind hScard, nsmul_eq_mul]

/-- **Die Tupel-Z-Summe zählt die Z-Schichten mit Faktor `m!`**: über der
vollen Blockmenge ist `tupleZ` das `m!`-fache der Summe über die
unabhängigen `m`-elementigen Teilmengen von `Λ`. -/
theorem tupleZ_univ_eq (w : ι → ℝ) (Λ : Finset ι) (γstar : ι) (m : ℕ) :
    tupleZ P w Λ γstar (Finset.univ : Finset (Fin m))
      = (Nat.factorial m : ℝ) *
          ∑ S ∈ Λ.powerset.filter (fun S => Indep P S ∧ S.card = m),
            ∏ γ ∈ S, w γ := by
  have hstep1 : tupleZ P w Λ γstar (Finset.univ : Finset (Fin m))
      = ∑ h ∈ (Fintype.piFinset fun _ : Fin m => Λ).filter
          (fun h => Function.Injective h ∧ Indep P (Finset.univ.image h)),
        ∏ j, w (h j) := by
    unfold tupleZ
    rw [pinnedTuples_univ, Finset.sum_filter]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [mul_ite, mul_one, mul_zero]
    exact if_congr (indep_pull_univ_iff P h) rfl rfl
  have hmaps : ∀ h ∈ (Fintype.piFinset fun _ : Fin m => Λ).filter
      (fun h => Function.Injective h ∧ Indep P (Finset.univ.image h)),
      Finset.univ.image h
        ∈ Λ.powerset.filter (fun S => Indep P S ∧ S.card = m) := by
    intro h hh
    obtain ⟨hpi, hinj, hind⟩ := Finset.mem_filter.mp hh
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, hind, ?_⟩
    · intro γ hγ
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hγ
      exact Fintype.mem_piFinset.mp hpi i
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ,
        Fintype.card_fin]
  rw [hstep1, ← Finset.sum_fiberwise_of_maps_to hmaps (fun h => ∏ j, w (h j)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  obtain ⟨hSpow, hSind, hScard⟩ := Finset.mem_filter.mp hS
  exact fiber_sum_eq P w (Finset.mem_powerset.mp hSpow) hSind hScard

/-- **Z als Summe der Tupel-Schichten**: die Zustandssumme ist die Summe
der durch `m!` normierten Tupel-Z-Summen aller Ordnungen `m ≤ M`. -/
theorem Z_eq_sum_tupleZ (w : ι → ℝ) (Λ : Finset ι) (γstar : ι) {M : ℕ}
    (hM : Λ.card ≤ M) :
    Z P w Λ = ∑ m ∈ Finset.range (M + 1),
      tupleZ P w Λ γstar (Finset.univ : Finset (Fin m))
        / (Nat.factorial m : ℝ) := by
  have hmaps : ∀ S ∈ Λ.powerset.filter (fun S => Indep P S),
      S.card ∈ Finset.range (M + 1) := by
    intro S hS
    obtain ⟨hSpow, -⟩ := Finset.mem_filter.mp hS
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le
      ((Finset.card_le_card (Finset.mem_powerset.mp hSpow)).trans hM))
  unfold Z
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun S => ∏ γ ∈ S, w γ)]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hfac : (Nat.factorial m : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  rw [tupleZ_univ_eq, mul_div_cancel_left₀ _ hfac, Finset.filter_filter]

/-! ## Die verschobene Koeffizientenfolge -/

omit [DecidableEq ι] [DecidableEq J] [Fintype J] in
/-- Über der leeren Polymermenge verschwindet jeder Reihenbeitrag. -/
theorem clusterOrderSum_of_empty (w : ι → ℝ) (n : ℕ) :
    clusterOrderSum P w (∅ : Finset ι) n = 0 := by
  unfold clusterOrderSum
  have hempty : (Fintype.piFinset fun _ : Fin (n + 1) => (∅ : Finset ι))
      = (∅ : Finset (Fin (n + 1) → ι)) := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro γ hγ
    exact Finset.notMem_empty _ (Fintype.mem_piFinset.mp hγ 0)
  rw [hempty, Finset.sum_empty]

omit [DecidableEq ι] [DecidableEq J] [Fintype J] in
/-- Über der leeren Polymermenge ist die Cluster-Reihe null. -/
theorem clusterSeries_empty (w : ι → ℝ) :
    clusterSeries P w (∅ : Finset ι) = 0 := by
  unfold clusterSeries clusterCoeff
  rw [tsum_congr fun n => by rw [clusterOrderSum_of_empty, zero_div]]
  exact tsum_zero

/-- Die um eins verschobene Koeffizientenfolge der Cluster-Reihe:
`v 0 = 0`, `v (n+1) = clusterCoeff n`. Sie erfüllt die Voraussetzung
`v 0 = 0` des Exponentialschritts. -/
noncomputable def seriesSeq (w : ι → ℝ) (Λ : Finset ι) (j : ℕ) : ℝ :=
  if j = 0 then 0 else clusterCoeff P w Λ (j - 1)

omit [DecidableEq ι] [DecidableEq J] [Fintype J] in
theorem seriesSeq_zero (w : ι → ℝ) (Λ : Finset ι) : seriesSeq P w Λ 0 = 0 :=
  rfl

omit [DecidableEq ι] [DecidableEq J] [Fintype J] in
theorem seriesSeq_succ (w : ι → ℝ) (Λ : Finset ι) (n : ℕ) :
    seriesSeq P w Λ (n + 1) = clusterCoeff P w Λ n := by
  unfold seriesSeq
  rw [if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel]

omit [DecidableEq ι] [DecidableEq J] [Fintype J] in
theorem abs_seriesSeq_le (w : ι → ℝ) (Λ : Finset ι) (j : ℕ) :
    |seriesSeq P w Λ j| ≤ (Real.exp 1 * ∑ x ∈ Λ, |w x|) ^ j := by
  cases j with
  | zero =>
    rw [seriesSeq_zero, abs_zero, pow_zero]
    exact zero_le_one
  | succ n =>
    rw [seriesSeq_succ]
    exact abs_clusterCoeff_le P w Λ n

omit [DecidableEq ι] [DecidableEq J] [Fintype J] in
theorem summable_seriesSeq (w : ι → ℝ) (Λ : Finset ι)
    (h : Real.exp 1 * ∑ x ∈ Λ, |w x| < 1) :
    Summable fun j => seriesSeq P w Λ j := by
  have hr0 : (0 : ℝ) ≤ Real.exp 1 * ∑ x ∈ Λ, |w x| :=
    mul_nonneg (Real.exp_pos 1).le (Finset.sum_nonneg fun x _ => abs_nonneg _)
  exact Summable.of_abs (Summable.of_nonneg_of_le (fun j => abs_nonneg _)
    (fun j => abs_seriesSeq_le P w Λ j) (summable_geometric_of_lt_one hr0 h))

omit [DecidableEq ι] [DecidableEq J] [Fintype J] in
/-- Die verschobene Folge summiert sich zur Cluster-Reihe. -/
theorem tsum_seriesSeq (w : ι → ℝ) (Λ : Finset ι)
    (h : Real.exp 1 * ∑ x ∈ Λ, |w x| < 1) :
    ∑' j, seriesSeq P w Λ j = clusterSeries P w Λ := by
  rw [(summable_seriesSeq P w Λ h).tsum_eq_zero_add, seriesSeq_zero, zero_add]
  unfold clusterSeries
  refine tsum_congr fun n => ?_
  rw [seriesSeq_succ]

/-! ## Der analytische Exponentialschritt

`exp` einer absolut konvergenten Reihe als nach Gesamtgewicht
umgruppierte Kompositionssumme: Potenzen werden als Tupelsummen
entwickelt, Tupel mit Nullkomponenten verschwinden, und die
verbleibenden Beiträge werden über `compositionsF` nach dem
Gesamtgewicht `m` gebündelt. -/

/-- Die Betrags-Produktfamilie über `k`-Tupel ist summierbar. -/
theorem summable_tupleProd (u : ℕ → ℝ) (hu : Summable fun j => |u j|) (k : ℕ) :
    Summable fun c : Fin k → ℕ => ∏ i, |u (c i)| := by
  induction k with
  | zero => exact .of_finite
  | succ k ih =>
    have hp : Summable fun p : ℕ × (Fin k → ℕ) => |u p.1| * ∏ i, |u (p.2 i)| :=
      Summable.mul_of_nonneg (f := fun j => |u j|)
        (g := fun c : Fin k → ℕ => ∏ i, |u (c i)|) hu ih
        (fun _ => abs_nonneg _)
        (fun _ => Finset.prod_nonneg fun _ _ => abs_nonneg _)
    refine (Equiv.summable_iff (Fin.consEquiv fun _ : Fin (k + 1) => ℕ)).mp
      (hp.congr fun p => ?_)
    simp [Fin.prod_univ_succ]

/-- Potenzen einer absolut konvergenten Reihe als Tupelsummen. -/
theorem tsum_pow_eq_tsum_tuple (u : ℕ → ℝ) (hu : Summable fun j => |u j|)
    (k : ℕ) :
    (∑' j, u j) ^ k = ∑' c : Fin k → ℕ, ∏ i, u (c i) := by
  induction k with
  | zero =>
    rw [pow_zero, tsum_fintype]
    simp
  | succ k ih =>
    have hnu : Summable fun j => ‖u j‖ := by
      simpa [Real.norm_eq_abs] using hu
    have hnt : Summable fun c : Fin k → ℕ => ‖∏ i, u (c i)‖ :=
      (summable_tupleProd u hu k).congr fun c => by
        rw [Real.norm_eq_abs, Finset.abs_prod]
    calc (∑' j, u j) ^ (k + 1)
        = (∑' j, u j) * (∑' j, u j) ^ k := pow_succ' _ _
      _ = (∑' j, u j) * ∑' c : Fin k → ℕ, ∏ i, u (c i) := by rw [ih]
      _ = ∑' p : ℕ × (Fin k → ℕ), u p.1 * ∏ i, u (p.2 i) :=
          tsum_mul_tsum_of_summable_norm (f := u)
            (g := fun c : Fin k → ℕ => ∏ i, u (c i)) hnu hnt
      _ = ∑' p : ℕ × (Fin k → ℕ),
            (fun c : Fin (k + 1) → ℕ => ∏ i, u (c i))
              ((Fin.consEquiv fun _ : Fin (k + 1) => ℕ) p) :=
          tsum_congr fun p => by simp [Fin.prod_univ_succ]
      _ = ∑' c : Fin (k + 1) → ℕ, ∏ i, u (c i) :=
          Equiv.tsum_eq (Fin.consEquiv fun _ : Fin (k + 1) => ℕ)
            (fun c : Fin (k + 1) → ℕ => ∏ i, u (c i))

/-- Einbettung der Kompositions-Sigma-Menge in die `k`-Tupel. -/
def compEmb (k : ℕ) :
    (Σ m : ℕ, {c : Fin k → ℕ // c ∈ compositionsF m k}) → (Fin k → ℕ) :=
  fun x => x.2.val

/-- `compEmb` ist injektiv: das Gesamtgewicht ist durch das Tupel
bestimmt. -/
theorem compEmb_injective (k : ℕ) : Function.Injective (compEmb k) := by
  rintro ⟨m, c, hc⟩ ⟨m', c', hc'⟩ h
  have hcc : c = c' := h
  obtain rfl : m = m' := by
    rw [← (mem_compositionsF.mp hc).2, ← (mem_compositionsF.mp hc').2, hcc]
  exact congrArg (Sigma.mk m) (Subtype.ext hcc)

/-- Träger der Produktfamilie: wegen `u 0 = 0` tragen nur Tupel mit
lauter positiven Einträgen bei, und diese liegen im Bild von
`compEmb`. -/
theorem support_subset_range_compEmb (u : ℕ → ℝ) (hu0 : u 0 = 0) (k : ℕ) :
    Function.support (fun c : Fin k → ℕ => ∏ i, u (c i))
      ⊆ Set.range (compEmb k) := by
  intro c hc
  have hc' : ∏ i, u (c i) ≠ 0 := hc
  have hne : ∀ i, c i ≠ 0 := by
    intro i hi0
    exact hc' (Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi0, hu0]))
  exact ⟨⟨∑ i, c i, c, mem_compositionsF.mpr ⟨hne, rfl⟩⟩, rfl⟩

/-- Die Tupelsumme, nach dem Gesamtgewicht gebündelt. -/
theorem tsum_tuple_eq_tsum_compositions (u : ℕ → ℝ) (hu0 : u 0 = 0)
    (hu : Summable fun j => |u j|) (k : ℕ) :
    ∑' c : Fin k → ℕ, ∏ i, u (c i)
      = ∑' m : ℕ, ∑ c ∈ compositionsF m k, ∏ i, u (c i) := by
  have habs : Summable fun c : Fin k → ℕ => |∏ i, u (c i)| :=
    (summable_tupleProd u hu k).congr fun c => (Finset.abs_prod _ _).symm
  have hsig : Summable
      fun x : Σ m : ℕ, {c : Fin k → ℕ // c ∈ compositionsF m k} =>
      ∏ i, u (x.2.val i) :=
    habs.of_abs.comp_injective (compEmb_injective k)
  calc ∑' c : Fin k → ℕ, ∏ i, u (c i)
      = ∑' x : Σ m : ℕ, {c : Fin k → ℕ // c ∈ compositionsF m k},
          ∏ i, u (x.2.val i) :=
        ((compEmb_injective k).tsum_eq
          (support_subset_range_compEmb u hu0 k)).symm
    _ = ∑' m : ℕ, ∑' c : {c : Fin k → ℕ // c ∈ compositionsF m k},
          ∏ i, u (c.val i) := hsig.tsum_sigma
    _ = ∑' m : ℕ, ∑ c ∈ compositionsF m k, ∏ i, u (c i) :=
        tsum_congr fun m => Finset.tsum_subtype (compositionsF m k)
          (fun c => ∏ i, u (c i))

/-- Summierbarkeit der nach Gesamtgewicht gebündelten Betragsreihe. -/
theorem summable_compositions_abs (u : ℕ → ℝ)
    (hu : Summable fun j => |u j|) (k : ℕ) :
    Summable fun m : ℕ => ∑ c ∈ compositionsF m k, ∏ i, |u (c i)| := by
  have hsig : Summable
      fun x : Σ m : ℕ, {c : Fin k → ℕ // c ∈ compositionsF m k} =>
      ∏ i, |u (x.2.val i)| :=
    (summable_tupleProd u hu k).comp_injective (compEmb_injective k)
  exact hsig.sigma.congr fun m => Finset.tsum_subtype (compositionsF m k)
    (fun c => ∏ i, |u (c i)|)

/-- Wert der gebündelten Betragsreihe: die `k`-te Potenz der
Betragssumme. -/
theorem tsum_compositions_abs (u : ℕ → ℝ) (hu0 : u 0 = 0)
    (hu : Summable fun j => |u j|) (k : ℕ) :
    ∑' m : ℕ, ∑ c ∈ compositionsF m k, ∏ i, |u (c i)|
      = (∑' j, |u j|) ^ k := by
  have hw : Summable fun j => abs |u j| :=
    hu.congr fun j => (abs_abs (u j)).symm
  have hw0 : |u 0| = 0 := by rw [hu0, abs_zero]
  calc ∑' m : ℕ, ∑ c ∈ compositionsF m k, ∏ i, |u (c i)|
      = ∑' c : Fin k → ℕ, ∏ i, |u (c i)| :=
        (tsum_tuple_eq_tsum_compositions (fun j => |u j|) hw0 hw k).symm
    _ = (∑' j, |u j|) ^ k :=
        (tsum_pow_eq_tsum_tuple (fun j => |u j|) hw k).symm

/-- **Der analytische Exponentialschritt**: `exp` einer absolut
konvergenten Reihe ist die nach dem Gesamtgewicht `m` umgruppierte
Kompositionssumme. -/
theorem exp_tsum_eq (v : ℕ → ℝ) (hv0 : v 0 = 0) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) (hbound : ∀ j, |v j| ≤ r ^ j) :
    Real.exp (∑' j, v j)
      = ∑' m, ∑ k ∈ Finset.range (m + 1), (Nat.factorial k : ℝ)⁻¹ *
          ∑ c ∈ compositionsF m k, ∏ i, v (c i) := by
  have habs : Summable fun j => |v j| :=
    Summable.of_nonneg_of_le (fun j => abs_nonneg _) hbound
      (summable_geometric_of_lt_one hr0 hr1)
  have hfac : ∀ k : ℕ, (0 : ℝ) ≤ (Nat.factorial k : ℝ)⁻¹ := fun k =>
    inv_nonneg.mpr (Nat.cast_nonneg _)
  -- Summierbarkeit der Betrags-Majorante über dem Produktgitter.
  have hHpos : ∀ p : ℕ × ℕ, 0 ≤ (Nat.factorial p.1 : ℝ)⁻¹ *
      ∑ c ∈ compositionsF p.2 p.1, ∏ i, |v (c i)| := fun p =>
    mul_nonneg (hfac p.1) (Finset.sum_nonneg fun c _ =>
      Finset.prod_nonneg fun i _ => abs_nonneg _)
  have hH : Summable fun p : ℕ × ℕ => (Nat.factorial p.1 : ℝ)⁻¹ *
      ∑ c ∈ compositionsF p.2 p.1, ∏ i, |v (c i)| := by
    refine (summable_prod_of_nonneg hHpos).mpr ⟨fun k => ?_, ?_⟩
    · show Summable fun m : ℕ => (Nat.factorial k : ℝ)⁻¹ *
        ∑ c ∈ compositionsF m k, ∏ i, |v (c i)|
      exact (summable_compositions_abs v habs k).mul_left _
    · show Summable fun k : ℕ => ∑' m : ℕ, (Nat.factorial k : ℝ)⁻¹ *
        ∑ c ∈ compositionsF m k, ∏ i, |v (c i)|
      have hgeom : Summable fun k : ℕ =>
          (Nat.factorial k : ℝ)⁻¹ * (∑' j, |v j|) ^ k :=
        (Real.summable_pow_div_factorial (∑' j, |v j|)).congr fun k =>
          (inv_mul_eq_div _ _).symm
      refine hgeom.congr fun k => ?_
      rw [tsum_mul_left, tsum_compositions_abs v hv0 habs k]
  -- Absolute Schranke für die vorzeichenbehaftete Familie.
  have hGabs : ∀ p : ℕ × ℕ,
      |(Nat.factorial p.1 : ℝ)⁻¹ * ∑ c ∈ compositionsF p.2 p.1, ∏ i, v (c i)|
        ≤ (Nat.factorial p.1 : ℝ)⁻¹ *
            ∑ c ∈ compositionsF p.2 p.1, ∏ i, |v (c i)| := by
    intro p
    rw [abs_mul, abs_of_nonneg (hfac p.1)]
    refine mul_le_mul_of_nonneg_left ?_ (hfac p.1)
    calc |∑ c ∈ compositionsF p.2 p.1, ∏ i, v (c i)|
        ≤ ∑ c ∈ compositionsF p.2 p.1, |∏ i, v (c i)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ c ∈ compositionsF p.2 p.1, ∏ i, |v (c i)| :=
          Finset.sum_congr rfl fun c _ => Finset.abs_prod _ _
  have hG : Summable fun p : ℕ × ℕ => (Nat.factorial p.1 : ℝ)⁻¹ *
      ∑ c ∈ compositionsF p.2 p.1, ∏ i, v (c i) :=
    (Summable.of_nonneg_of_le (fun p => abs_nonneg _) hGabs hH).of_abs
  calc Real.exp (∑' j, v j)
      = ∑' k : ℕ, (∑' j, v j) ^ k / (Nat.factorial k : ℝ) := by
        simp only [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    _ = ∑' k : ℕ, ∑' m : ℕ, (Nat.factorial k : ℝ)⁻¹ *
          ∑ c ∈ compositionsF m k, ∏ i, v (c i) := by
        refine tsum_congr fun k => ?_
        rw [div_eq_inv_mul, tsum_pow_eq_tsum_tuple v habs k,
          tsum_tuple_eq_tsum_compositions v hv0 habs k, ← tsum_mul_left]
    _ = ∑' m : ℕ, ∑' k : ℕ, (Nat.factorial k : ℝ)⁻¹ *
          ∑ c ∈ compositionsF m k, ∏ i, v (c i) :=
        (Summable.tsum_comm (f := fun k m => (Nat.factorial k : ℝ)⁻¹ *
          ∑ c ∈ compositionsF m k, ∏ i, v (c i)) hG).symm
    _ = ∑' m : ℕ, ∑ k ∈ Finset.range (m + 1), (Nat.factorial k : ℝ)⁻¹ *
          ∑ c ∈ compositionsF m k, ∏ i, v (c i) := by
        refine tsum_congr fun m => ?_
        refine tsum_eq_sum fun k hk => ?_
        rw [Finset.mem_range] at hk
        have hempty : compositionsF m k = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro c hc
          have := card_le_of_mem_compositionsF hc
          omega
        rw [hempty, Finset.sum_empty, mul_zero]

end ClusterExpansion
