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
  Kompositionssumme;
* `sum_orderedPartitionsF_eq`, `sum_orderedPartitionsF_eq_compositions`,
  `sum_partitionsOf_card`: die **Multinomialzählung** — geordnete
  Partitionen mit Größenprofil `c` gibt es `|A|!/∏ cᵢ!` viele, ungeordnete
  um den Faktor `k!` weniger.

Hauptresultat: `exp_clusterSeries_eq_Z` und `log_Z_eq_clusterSeries` —
im Kleinheitsregime `e · ∑_Λ |w| < 1` ist `Z` das Exponential der
Cluster-Reihe, also `log Z Λ = clusterSeries P w Λ`; insbesondere ist
`Z > 0` (`Z_pos_of_small`).

Kein `sorry` in dieser Datei. Bewusst offen (nur genannt, nichts
Unbewiesenes behauptet): die scharfe Kotecký-Preiss-Summierbarkeit über
Baumzahlen mit vorgeschriebenen Graden, die das Kleinheitsregime durch
die KP-Bedingung ersetzen würde.

Referenzen: Kotecký-Preiss (Comm. Math. Phys. 103, 1986); Ueltschi
(Moscow Math. J. 4, 2004); Friedli-Velenik, Kap. 5.
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

variable {𝕂 : Type*} [RCLike 𝕂]
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
noncomputable def tupleZ (w : ι → 𝕂) (Λ : Finset ι) (γstar : ι)
    (K : Finset J) : 𝕂 :=
  ∑ h ∈ pinnedTuples Λ γstar K, (∏ j ∈ K, w (h j)) *
    (if Indep (P.pull h) K then 1 else 0)

/-- Tupelsumme mit Ursell-Gewicht: der Block-Beitrag der Cluster-Reihe
in Tupelform. -/
noncomputable def tupleU (w : ι → 𝕂) (Λ : Finset ι) (γstar : ι)
    (B : Finset J) : 𝕂 :=
  ∑ h ∈ pinnedTuples Λ γstar B, (∏ j ∈ B, w (h j)) *
    (ursellSetSum (P.pull h) B : 𝕂)

omit [DecidableEq ι] in
/-- Die leere Tupelsumme ist `1`. -/
theorem tupleZ_empty (w : ι → 𝕂) (Λ : Finset ι) (γstar : ι) :
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
      change P.incomp (h' u) (h' v) = true
      rw [← hagree u hu, ← hagree v hv]
      exact hinc
    · rintro ⟨hu, hv, hne, hinc⟩
      refine ⟨hu, hv, hne, ?_⟩
      change P.incomp (h u) (h v) = true
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
    change P.incomp (h' i) (h' j) = false
    rw [← hagree i hi, ← hagree j hj]
    exact this
  · have := hI i hi j hj hne
    change P.incomp (h i) (h j) = false
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

/-! ## Geordnete gegen ungeordnete Partitionen: der Faktor `k!`

Die Faserzählung über die Abbildung `T ↦ Bild von T`: jede geordnete
Partition `T : Fin k → Finset J` hat als Bild eine Partition mit genau
`k` Blöcken, und über jeder solchen Partition liegen genau `k!` viele
geordnete Partitionen — die Einbettungen `Fin k ↪ C`. -/

omit [DecidableEq ι] [Fintype J] in
/-- Eine geordnete Partition ist als Abbildung injektiv: zwei gleiche
Blöcke an verschiedenen Stellen wären zu sich selbst disjunkt, also
leer — im Widerspruch zur Nichtleerheit. -/
theorem injective_of_mem_orderedPartitionsF {A : Finset J} {k : ℕ}
    {T : Fin k → Finset J} (hT : T ∈ orderedPartitionsF A k) :
    Function.Injective T := by
  obtain ⟨hne, hdisj, -⟩ := mem_orderedPartitionsF.mp hT
  intro i j hij
  by_contra hij'
  have hd : Disjoint (T i) (T i) := by
    have := hdisj i j hij'
    rwa [← hij] at this
  rw [Finset.disjoint_self_iff_empty] at hd
  exact Finset.not_nonempty_iff_eq_empty.mpr hd (hne i)

omit [DecidableEq ι] [Fintype J] in
/-- Das Bild einer geordneten Partition ist eine Partition der
Grundmenge mit genau `k` Blöcken. -/
theorem image_mem_partitionsOf {A : Finset J} {k : ℕ}
    {T : Fin k → Finset J} (hT : T ∈ orderedPartitionsF A k) :
    Finset.univ.image T ∈ (partitionsOf A).filter (fun C => C.card = k) := by
  obtain ⟨hne, hdisj, hsup⟩ := mem_orderedPartitionsF.mp hT
  have hsupimg : (Finset.univ.image T).sup id = Finset.univ.sup T :=
    Finset.sup_image _ _ _
  refine Finset.mem_filter.mpr
    ⟨mem_partitionsOf.mpr ⟨?_, ⟨?_, ?_⟩, hsupimg.trans hsup⟩, ?_⟩
  · intro B hB
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hB
    rw [← hsup]
    exact Finset.le_sup (Finset.mem_univ i)
  · intro B hB
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hB
    exact hne i
  · intro B₁ h₁ B₂ h₂ hne12
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp h₁
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp h₂
    exact hdisj i j fun hij => hne12 (congrArg T hij)
  · rw [Finset.card_image_of_injective _
      (injective_of_mem_orderedPartitionsF hT),
      Finset.card_univ, Fintype.card_fin]

omit [DecidableEq ι] [Fintype J] in
/-- Rückrichtung der Faserzählung: aus einer Einbettung `Fin k ↪ C`
wird eine geordnete Partition mit Bildkollektion `C`. Nichtleerheit und
Disjunktheit erbt sie von `C`, die Bildgleichung folgt aus
Injektivität und `|C| = k`. -/
theorem mem_fiber_of_embedding {A : Finset J} {k : ℕ}
    {C : Finset (Finset J)} (hC : C ∈ partitionsOf A) (hCcard : C.card = k)
    (e : Fin k ↪ {x // x ∈ C}) :
    (fun i => ((e i : Finset J))) ∈ (orderedPartitionsF A k).filter
      (fun T => Finset.univ.image T = C) := by
  obtain ⟨-, hICC, hsup⟩ := mem_partitionsOf.mp hC
  have hinj : Function.Injective fun i => ((e i : Finset J)) :=
    fun i j hij => e.injective (Subtype.val_injective hij)
  have himg : Finset.univ.image (fun i => ((e i : Finset J))) = C := by
    refine Finset.eq_of_subset_of_card_le ?_ (le_of_eq ?_)
    · intro B hB
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hB
      exact (e i).2
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ,
        Fintype.card_fin, hCcard]
  have hsupimg : (Finset.univ.image (fun i => ((e i : Finset J)))).sup id
      = Finset.univ.sup (fun i => ((e i : Finset J))) :=
    Finset.sup_image _ _ _
  refine Finset.mem_filter.mpr ⟨mem_orderedPartitionsF.mpr ⟨?_, ?_, ?_⟩, himg⟩
  · exact fun i => hICC.1 _ (e i).2
  · exact fun i j hij => hICC.2 _ (e i).2 _ (e j).2
      fun h => hij (e.injective (Subtype.ext h))
  · rw [← hsupimg, himg]
    exact hsup

omit [DecidableEq ι] [Fintype J] in
/-- Faserkardinalität: die geordneten Partitionen mit Bildkollektion `C`
entsprechen genau den Einbettungen `Fin k ↪ C` — es gibt `k!` viele. -/
theorem card_fiber_orderedPartitionsF {A : Finset J} {k : ℕ}
    {C : Finset (Finset J)} (hC : C ∈ partitionsOf A) (hCcard : C.card = k) :
    ((orderedPartitionsF A k).filter
        (fun T => Finset.univ.image T = C)).card
      = Nat.factorial k := by
  have hbij : ((orderedPartitionsF A k).filter
      (fun T => Finset.univ.image T = C)).card
      = Fintype.card (Fin k ↪ {x // x ∈ C}) := by
    rw [← Finset.card_univ]
    refine Finset.card_bij'
      (fun T hT => ⟨fun i => ⟨T i, ?_⟩, ?_⟩)
      (fun e _ => fun i => ((e i : Finset J))) ?_ ?_ ?_ ?_
    -- Werte liegen in `C`.
    · exact (Finset.mem_filter.mp hT).2 ▸
        Finset.mem_image_of_mem T (Finset.mem_univ i)
    -- Injektivität der Einbettung.
    · exact fun i j hij =>
        injective_of_mem_orderedPartitionsF (Finset.mem_filter.mp hT).1
          (congrArg Subtype.val hij)
    -- Hinrichtung: alles landet in `univ`.
    · exact fun T _ => Finset.mem_univ _
    -- Rückrichtung: die Einbettung liefert eine geordnete Partition.
    · exact fun e _ => mem_fiber_of_embedding hC hCcard e
    -- Linksinverse.
    · intro T _
      rfl
    -- Rechtsinverse.
    · intro e _
      exact Function.Embedding.ext fun i => Subtype.ext rfl
  rw [hbij, Fintype.card_embedding_eq, Fintype.card_coe, Fintype.card_fin,
    hCcard, Nat.descFactorial_self]

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

omit [DecidableEq ι] [Fintype J] in
omit [CharZero 𝕜] in
/-- **Geordnete gegen ungeordnete Partitionen**: die Summe eines nur von
den Blockgrößen abhängenden Produkts über die geordneten Partitionen ist
das `k!`-fache der Summe über die Partitionen mit `k` Blöcken. -/
theorem sum_orderedPartitionsF_eq (A : Finset J) (k : ℕ) (f : ℕ → 𝕜) :
    ∑ T ∈ orderedPartitionsF A k, ∏ i, f (T i).card
      = (Nat.factorial k : 𝕜) *
          ∑ C ∈ (partitionsOf A).filter (fun C => C.card = k),
            ∏ B ∈ C, f B.card := by
  have hmaps : ∀ T ∈ orderedPartitionsF A k,
      Finset.univ.image T ∈ (partitionsOf A).filter (fun C => C.card = k) :=
    fun _ hT => image_mem_partitionsOf hT
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun T => ∏ i, f (T i).card),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun C hC => ?_
  obtain ⟨hCmem, hCcard⟩ := Finset.mem_filter.mp hC
  have hval : ∀ T ∈ (orderedPartitionsF A k).filter
      (fun T => Finset.univ.image T = C),
      ∏ i, f (T i).card = ∏ B ∈ C, f B.card := by
    intro T hT
    obtain ⟨hTmem, himg⟩ := Finset.mem_filter.mp hT
    rw [← himg, Finset.prod_image
      (fun i _ j _ hij => injective_of_mem_orderedPartitionsF hTmem hij)]
  rw [Finset.sum_congr rfl hval, Finset.sum_const,
    card_fiber_orderedPartitionsF hCmem hCcard, nsmul_eq_mul]

/-! ## Das Größenprofil geordneter Partitionen -/

omit [DecidableEq ι] [Fintype J] in
/-- Die Vereinigung eines mit `Fin.cons` vorangestellten Blocks. -/
theorem sup_univ_cons (B₀ : Finset J) {k : ℕ} (T : Fin k → Finset J) :
    Finset.univ.sup (Fin.cons B₀ T : Fin (k + 1) → Finset J)
      = B₀ ∪ Finset.univ.sup T := by
  refine le_antisymm (Finset.sup_le fun i _ => ?_) (Finset.union_subset ?_ ?_)
  · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · rw [Fin.cons_zero]
      exact Finset.subset_union_left
    · rw [Fin.cons_succ]
      exact (Finset.le_sup (f := T) (Finset.mem_univ j)).trans
        Finset.subset_union_right
  · have h := Finset.le_sup (f := (Fin.cons B₀ T : Fin (k + 1) → Finset J))
      (Finset.mem_univ (0 : Fin (k + 1)))
    rwa [Fin.cons_zero] at h
  · refine Finset.sup_le fun j _ => ?_
    have h := Finset.le_sup (f := (Fin.cons B₀ T : Fin (k + 1) → Finset J))
      (Finset.mem_univ j.succ)
    rwa [Fin.cons_succ] at h

omit [DecidableEq ι] [Fintype J] in
/-- Zugehörigkeit eines vorangestellten Blocks zu den geordneten
Partitionen: `Fin.cons B₀ T'` partitioniert `A` genau dann, wenn `B₀`
ein nichtleerer Teil von `A` ist und `T'` den Rest `A \ B₀`
partitioniert. -/
theorem mem_cons_orderedPartitionsF {A : Finset J} {k : ℕ} {B₀ : Finset J}
    {T' : Fin k → Finset J} :
    (Fin.cons B₀ T' : Fin (k + 1) → Finset J) ∈ orderedPartitionsF A (k + 1)
      ↔ B₀.Nonempty ∧ B₀ ⊆ A ∧ T' ∈ orderedPartitionsF (A \ B₀) k := by
  rw [mem_orderedPartitionsF, mem_orderedPartitionsF, sup_univ_cons]
  constructor
  · rintro ⟨hne, hdisj, hsup⟩
    have hB₀ne : B₀.Nonempty := by
      have h := hne 0
      rwa [Fin.cons_zero] at h
    have hT'ne : ∀ i, (T' i).Nonempty := by
      intro i
      have h := hne i.succ
      rwa [Fin.cons_succ] at h
    have hT'disj : ∀ i j, i ≠ j → Disjoint (T' i) (T' j) := by
      intro i j hij
      have h := hdisj i.succ j.succ fun hs => hij (Fin.succ_injective k hs)
      rwa [Fin.cons_succ, Fin.cons_succ] at h
    have hd0 : Disjoint B₀ (Finset.univ.sup T') := by
      rw [Finset.disjoint_sup_right]
      intro i _
      have h := hdisj 0 i.succ (Ne.symm (Fin.succ_ne_zero i))
      rwa [Fin.cons_zero, Fin.cons_succ] at h
    refine ⟨hB₀ne, ?_, hT'ne, hT'disj, ?_⟩
    · rw [← hsup]
      exact Finset.subset_union_left
    · rw [← hsup]
      exact (Finset.union_sdiff_cancel_left hd0).symm
  · rintro ⟨hB₀ne, hB₀sub, hT'ne, hT'disj, hT'sup⟩
    have hsubdiff : ∀ i, T' i ⊆ A \ B₀ := by
      intro i
      rw [← hT'sup]
      exact Finset.le_sup (Finset.mem_univ i)
    have hB₀T' : ∀ i, Disjoint B₀ (T' i) := by
      intro i
      refine Finset.disjoint_left.mpr fun x hxB hxT => ?_
      exact (Finset.mem_sdiff.mp (hsubdiff i hxT)).2 hxB
    refine ⟨fun i => ?_, fun i j hij => ?_, ?_⟩
    · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · rwa [Fin.cons_zero]
      · rw [Fin.cons_succ]
        exact hT'ne j
    · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨ii, rfl⟩ <;>
        rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨jj, rfl⟩
      · exact absurd rfl hij
      · rw [Fin.cons_zero, Fin.cons_succ]
        exact hB₀T' jj
      · rw [Fin.cons_zero, Fin.cons_succ]
        exact (hB₀T' ii).symm
      · rw [Fin.cons_succ, Fin.cons_succ]
        exact hT'disj ii jj fun h => hij (congrArg Fin.succ h)
    · rw [hT'sup]
      exact Finset.union_sdiff_of_subset hB₀sub

omit [DecidableEq ι] [Fintype J] in
omit [CharZero 𝕜] in
/-- **Zerlegung geordneter Partitionen nach dem ersten Block**: die
Summe über `orderedPartitionsF A (k+1)` zerfällt in die Doppelsumme über
den nichtleeren ersten Block `B₀ ⊆ A` und die geordneten Partitionen des
Rests `A \ B₀`. -/
theorem sum_orderedPartitionsF_succ (A : Finset J) (k : ℕ)
    (g : (Fin (k + 1) → Finset J) → 𝕜) :
    ∑ T ∈ orderedPartitionsF A (k + 1), g T
      = ∑ B₀ ∈ A.powerset.filter (fun B => B.Nonempty),
          ∑ T' ∈ orderedPartitionsF (A \ B₀) k, g (Fin.cons B₀ T') := by
  refine Eq.trans ?_ (Finset.sum_sigma'
    (A.powerset.filter (fun B => B.Nonempty))
    (fun B₀ => orderedPartitionsF (A \ B₀) k)
    (fun B₀ T' => g (Fin.cons B₀ T'))).symm
  refine Finset.sum_nbij'
    (fun T => (⟨T 0, Fin.tail T⟩ : (_ : Finset J) × (Fin k → Finset J)))
    (fun x => Fin.cons x.1 x.2) ?_ ?_ ?_ ?_ ?_
  · intro T hT
    have hT' : (Fin.cons (T 0) (Fin.tail T) : Fin (k + 1) → Finset J)
        ∈ orderedPartitionsF A (k + 1) := by
      rw [Fin.cons_self_tail]
      exact hT
    obtain ⟨hne, hsub, hmem⟩ := mem_cons_orderedPartitionsF.mp hT'
    exact Finset.mem_sigma.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, hne⟩, hmem⟩
  · rintro ⟨B₀, T'⟩ hx
    obtain ⟨hB₀, hT'⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hpow, hne⟩ := Finset.mem_filter.mp hB₀
    exact mem_cons_orderedPartitionsF.mpr
      ⟨hne, Finset.mem_powerset.mp hpow, hT'⟩
  · intro T _
    exact Fin.cons_self_tail T
  · rintro ⟨B₀, T'⟩ _
    simp only [Fin.cons_zero, Fin.tail_cons]
  · intro T _
    rw [Fin.cons_self_tail]

omit [DecidableEq ι] [DecidableEq J] [Fintype J] in
/-- Zugehörigkeit einer vorangestellten Zahl zu den Kompositionen:
`Fin.cons d c'` ist genau dann eine Komposition von `m` in `k+1` Teile,
wenn `1 ≤ d ≤ m` gilt und `c'` eine Komposition von `m - d` ist. -/
theorem mem_cons_compositionsF {m k d : ℕ} {c' : Fin k → ℕ} :
    (Fin.cons d c' : Fin (k + 1) → ℕ) ∈ compositionsF m (k + 1)
      ↔ 1 ≤ d ∧ d ≤ m ∧ c' ∈ compositionsF (m - d) k := by
  have hsum : ∑ i, (Fin.cons d c' : Fin (k + 1) → ℕ) i = d + ∑ i, c' i := by
    rw [Fin.sum_univ_succ, Fin.cons_zero]
    exact congrArg _ (Finset.sum_congr rfl fun i _ => by rw [Fin.cons_succ])
  rw [mem_compositionsF, mem_compositionsF, hsum]
  constructor
  · rintro ⟨hne, hs⟩
    have hd : d ≠ 0 := by
      have h := hne 0
      rwa [Fin.cons_zero] at h
    have hc' : ∀ i, c' i ≠ 0 := by
      intro i
      have h := hne i.succ
      rwa [Fin.cons_succ] at h
    exact ⟨Nat.one_le_iff_ne_zero.mpr hd, by omega, hc', by omega⟩
  · rintro ⟨hd1, hd2, hc'ne, hc'sum⟩
    refine ⟨fun i => ?_, by omega⟩
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · rw [Fin.cons_zero]
      omega
    · rw [Fin.cons_succ]
      exact hc'ne j

omit [DecidableEq ι] [DecidableEq J] [Fintype J] in
omit [CharZero 𝕜] in
/-- **Zerlegung der Kompositionen nach dem ersten Teil**: die Summe über
`compositionsF m (k+1)` zerfällt in die Doppelsumme über den ersten Teil
`d ∈ [1, m]` und die Kompositionen von `m - d` in `k` Teile. -/
theorem sum_compositionsF_succ (m k : ℕ) (g : (Fin (k + 1) → ℕ) → 𝕜) :
    ∑ c ∈ compositionsF m (k + 1), g c
      = ∑ d ∈ Finset.Icc 1 m, ∑ c' ∈ compositionsF (m - d) k,
          g (Fin.cons d c') := by
  refine Eq.trans ?_ (Finset.sum_sigma' (Finset.Icc 1 m)
    (fun d => compositionsF (m - d) k) (fun d c' => g (Fin.cons d c'))).symm
  refine Finset.sum_nbij'
    (fun c => (⟨c 0, Fin.tail c⟩ : (_ : ℕ) × (Fin k → ℕ)))
    (fun x => Fin.cons x.1 x.2) ?_ ?_ ?_ ?_ ?_
  · intro c hc
    have hc' : (Fin.cons (c 0) (Fin.tail c) : Fin (k + 1) → ℕ)
        ∈ compositionsF m (k + 1) := by
      rw [Fin.cons_self_tail]
      exact hc
    obtain ⟨h1, h2, h3⟩ := mem_cons_compositionsF.mp hc'
    exact Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨h1, h2⟩, h3⟩
  · rintro ⟨d, c'⟩ hx
    obtain ⟨hd, hc'⟩ := Finset.mem_sigma.mp hx
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hd
    exact mem_cons_compositionsF.mpr ⟨h1, h2, hc'⟩
  · intro c _
    exact Fin.cons_self_tail c
  · rintro ⟨d, c'⟩ _
    simp only [Fin.cons_zero, Fin.tail_cons]
  · intro c _
    rw [Fin.cons_self_tail]

omit [DecidableEq ι] [DecidableEq J] [Fintype J] in
omit [CharZero 𝕜] in
/-- Eine nur von der Größe abhängige Summe über die nichtleeren
Teilmengen von `A` bündelt sich zu einer Summe über die Größen mit den
Binomialkoeffizienten als Vielfachheiten. -/
theorem sum_powerset_nonempty_card (A : Finset J) (g : ℕ → 𝕜) :
    ∑ B ∈ A.powerset.filter (fun B => B.Nonempty), g B.card
      = ∑ d ∈ Finset.Icc 1 A.card, (A.card.choose d : 𝕜) * g d := by
  have hmaps : ∀ B ∈ A.powerset.filter (fun B => B.Nonempty),
      B.card ∈ Finset.Icc 1 A.card := by
    intro B hB
    obtain ⟨hpow, hne⟩ := Finset.mem_filter.mp hB
    exact Finset.mem_Icc.mpr ⟨Finset.card_pos.mpr hne,
      Finset.card_le_card (Finset.mem_powerset.mp hpow)⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun B => g B.card)]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨hd1, -⟩ := Finset.mem_Icc.mp hd
  have hfil : (A.powerset.filter (fun B => B.Nonempty)).filter
      (fun B => B.card = d) = A.powersetCard d := by
    ext B
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_powerset,
      Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hsub, -⟩, hcard⟩
      exact ⟨hsub, hcard⟩
    · rintro ⟨hsub, hcard⟩
      exact ⟨⟨hsub, Finset.card_pos.mp (by omega)⟩, hcard⟩
  rw [hfil, Finset.sum_congr rfl
      (fun B hB => congrArg g (Finset.mem_powersetCard.mp hB).2),
    Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]

omit [DecidableEq ι] [DecidableEq J] [Fintype J] in
/-- Der Multinomial-Schritt in `𝕜`: Binomialkoeffizient mal
Restfakultät über einem Nenner ist die volle Fakultät über dem um `d!`
erweiterten Nenner. -/
theorem choose_mul_factorial_div {m d : ℕ} (hd : d ≤ m) {Q : 𝕜} (hQ : Q ≠ 0) :
    (m.choose d : 𝕜) * ((Nat.factorial (m - d) : 𝕜) / Q)
      = (Nat.factorial m : 𝕜) / ((Nat.factorial d : 𝕜) * Q) := by
  have hfd : (Nat.factorial d : 𝕜) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)
  have hfr : (Nat.factorial (m - d) : 𝕜) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m - d))
  rw [Nat.cast_choose 𝕜 hd]
  field_simp

omit [DecidableEq ι] [Fintype J] in
/-- **Größenprofil geordneter Partitionen**: eine nur von den
Blockgrößen abhängige Summe über die geordneten Partitionen von `A` in
`k` Blöcke ist die mit Multinomialkoeffizienten gewichtete Summe über
die Kompositionen von `|A|` in `k` positive Teile. Beweis durch
Induktion über `k` bei mitlaufendem `A`: Abspalten des ersten Blocks,
Bündelung nach seiner Größe (Binomialkoeffizient) und die
Multinomial-Identität `C(m,d) · (m−d)!/∏ = m!/(d!·∏)`. -/
theorem sum_orderedPartitionsF_eq_compositions (A : Finset J) (k : ℕ)
    (f : ℕ → 𝕜) :
    ∑ T ∈ orderedPartitionsF A k, ∏ i, f (T i).card
      = ∑ c ∈ compositionsF A.card k,
          ((Nat.factorial A.card : 𝕜) / ∏ i, (Nat.factorial (c i) : 𝕜)) *
            ∏ i, f (c i) := by
  induction k generalizing A with
  | zero =>
    by_cases hA : A = ∅
    · subst hA
      have h1 : orderedPartitionsF (∅ : Finset J) 0
          = {(Fin.elim0 : Fin 0 → Finset J)} := by
        ext T
        rw [mem_orderedPartitionsF, Finset.mem_singleton]
        constructor
        · rintro -
          funext i
          exact i.elim0
        · rintro rfl
          refine ⟨fun i => i.elim0, fun i => i.elim0, ?_⟩
          rw [Finset.univ_eq_empty, Finset.sup_empty]
          rfl
      have h2 : compositionsF 0 0 = {(Fin.elim0 : Fin 0 → ℕ)} := by
        ext c
        rw [mem_compositionsF, Finset.mem_singleton]
        constructor
        · rintro -
          funext i
          exact i.elim0
        · rintro rfl
          exact ⟨fun i => i.elim0,
            by rw [Finset.univ_eq_empty, Finset.sum_empty]⟩
      rw [h1, Finset.card_empty, h2, Finset.sum_singleton, Finset.sum_singleton,
        Finset.univ_eq_empty, Finset.prod_empty, Finset.prod_empty,
        Finset.prod_empty, Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
    · have h1 : orderedPartitionsF A 0 = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro T hT
        obtain ⟨-, -, hsup⟩ := mem_orderedPartitionsF.mp hT
        rw [Finset.univ_eq_empty, Finset.sup_empty] at hsup
        exact hA hsup.symm
      have h2 : compositionsF A.card 0 = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro c hc
        obtain ⟨-, hsum⟩ := mem_compositionsF.mp hc
        rw [Finset.univ_eq_empty, Finset.sum_empty] at hsum
        exact hA (Finset.card_eq_zero.mp hsum.symm)
      rw [h1, h2, Finset.sum_empty, Finset.sum_empty]
  | succ k IH =>
    have hconsCard : ∀ (B₀ : Finset J) (T' : Fin k → Finset J),
        (∏ i, f ((Fin.cons B₀ T' : Fin (k + 1) → Finset J) i).card)
          = f B₀.card * ∏ i, f (T' i).card := by
      intro B₀ T'
      rw [Fin.prod_univ_succ, Fin.cons_zero]
      exact congrArg _ (Finset.prod_congr rfl fun i _ => by rw [Fin.cons_succ])
    have hconsFac : ∀ (d : ℕ) (c' : Fin k → ℕ),
        (∏ i, (Nat.factorial ((Fin.cons d c' : Fin (k + 1) → ℕ) i) : 𝕜))
          = (Nat.factorial d : 𝕜) * ∏ i, (Nat.factorial (c' i) : 𝕜) := by
      intro d c'
      rw [Fin.prod_univ_succ, Fin.cons_zero]
      exact congrArg _ (Finset.prod_congr rfl fun i _ => by rw [Fin.cons_succ])
    have hconsF : ∀ (d : ℕ) (c' : Fin k → ℕ),
        (∏ i, f ((Fin.cons d c' : Fin (k + 1) → ℕ) i))
          = f d * ∏ i, f (c' i) := by
      intro d c'
      rw [Fin.prod_univ_succ, Fin.cons_zero]
      exact congrArg _ (Finset.prod_congr rfl fun i _ => by rw [Fin.cons_succ])
    calc ∑ T ∈ orderedPartitionsF A (k + 1), ∏ i, f (T i).card
        = ∑ B₀ ∈ A.powerset.filter (fun B => B.Nonempty),
            ∑ T' ∈ orderedPartitionsF (A \ B₀) k,
              ∏ i, f ((Fin.cons B₀ T' : Fin (k + 1) → Finset J) i).card :=
          sum_orderedPartitionsF_succ A k
            (fun T : Fin (k + 1) → Finset J => ∏ i, f (T i).card)
      _ = ∑ B₀ ∈ A.powerset.filter (fun B => B.Nonempty),
            f B₀.card * ∑ c' ∈ compositionsF (A.card - B₀.card) k,
              ((Nat.factorial (A.card - B₀.card) : 𝕜)
                  / ∏ i, (Nat.factorial (c' i) : 𝕜)) * ∏ i, f (c' i) := by
          refine Finset.sum_congr rfl fun B₀ hB₀ => ?_
          have hsub : B₀ ⊆ A :=
            Finset.mem_powerset.mp (Finset.mem_filter.mp hB₀).1
          have hstep : ∑ T' ∈ orderedPartitionsF (A \ B₀) k,
                ∏ i, f ((Fin.cons B₀ T' : Fin (k + 1) → Finset J) i).card
              = f B₀.card
                  * ∑ T' ∈ orderedPartitionsF (A \ B₀) k,
                      ∏ i, f (T' i).card := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun T' _ => hconsCard B₀ T'
          rw [hstep, IH (A \ B₀), Finset.card_sdiff_of_subset hsub]
      _ = ∑ d ∈ Finset.Icc 1 A.card, (A.card.choose d : 𝕜) *
            (f d * ∑ c' ∈ compositionsF (A.card - d) k,
              ((Nat.factorial (A.card - d) : 𝕜)
                  / ∏ i, (Nat.factorial (c' i) : 𝕜)) * ∏ i, f (c' i)) :=
          sum_powerset_nonempty_card A (fun d : ℕ =>
            f d * ∑ c' ∈ compositionsF (A.card - d) k,
              ((Nat.factorial (A.card - d) : 𝕜)
                  / ∏ i, (Nat.factorial (c' i) : 𝕜)) * ∏ i, f (c' i))
      _ = ∑ d ∈ Finset.Icc 1 A.card, ∑ c' ∈ compositionsF (A.card - d) k,
            ((Nat.factorial A.card : 𝕜)
                / ∏ i, (Nat.factorial
                    ((Fin.cons d c' : Fin (k + 1) → ℕ) i) : 𝕜))
              * ∏ i, f ((Fin.cons d c' : Fin (k + 1) → ℕ) i) := by
          refine Finset.sum_congr rfl fun d hd => ?_
          obtain ⟨-, hd2⟩ := Finset.mem_Icc.mp hd
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun c' _ => ?_
          have hQ : (∏ i, (Nat.factorial (c' i) : 𝕜)) ≠ 0 :=
            Finset.prod_ne_zero_iff.mpr fun i _ =>
              Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
          rw [hconsFac d c', hconsF d c', ← choose_mul_factorial_div hd2 hQ]
          ring
      _ = ∑ c ∈ compositionsF A.card (k + 1),
            ((Nat.factorial A.card : 𝕜) / ∏ i, (Nat.factorial (c i) : 𝕜)) *
              ∏ i, f (c i) :=
          (sum_compositionsF_succ A.card k (fun c : Fin (k + 1) → ℕ =>
            ((Nat.factorial A.card : 𝕜) / ∏ i, (Nat.factorial (c i) : 𝕜)) *
              ∏ i, f (c i))).symm

omit [DecidableEq ι] [Fintype J] in
/-- **Multinomialzählung der Partitionen**: eine nur von den Blockgrößen
abhängige Summe über alle Partitionen von `A` ist die nach Blockzahl und
Größenprofil sortierte Kompositionssumme. Das ist die kombinatorische
Brücke zwischen der Partitionsform der Zustandssumme und der
Kompositionsform des Exponentials. -/
theorem sum_partitionsOf_card (A : Finset J) (f : ℕ → 𝕜) :
    ∑ C ∈ partitionsOf A, ∏ B ∈ C, f B.card
      = ∑ k ∈ Finset.range (A.card + 1), (Nat.factorial k : 𝕜)⁻¹ *
          ∑ c ∈ compositionsF A.card k,
            ((Nat.factorial A.card : 𝕜) / ∏ i, (Nat.factorial (c i) : 𝕜)) *
              ∏ i, f (c i) := by
  have hmaps : ∀ C ∈ partitionsOf A, C.card ∈ Finset.range (A.card + 1) :=
    fun C hC =>
      Finset.mem_range.mpr (Nat.lt_succ_of_le (card_le_of_mem_partitionsOf hC))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun C => ∏ B ∈ C, f B.card)]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hfac : (Nat.factorial k : 𝕜) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  rw [← sum_orderedPartitionsF_eq_compositions A k f,
    sum_orderedPartitionsF_eq A k f, ← mul_assoc, inv_mul_cancel₀ hfac, one_mul]

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
theorem sum_pinnedTuples_union {R : Type*} [CommRing R] (Λ : Finset ι)
    (γstar : ι) {B S : Finset J} (hdisj : Disjoint B S) (φ : (J → ι) → R) :
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
theorem sum_pinnedTuples_prod_blocks {R : Type*} [CommRing R] (Λ : Finset ι)
    (γstar : ι) (C : Finset (Finset J))
    (hdisj : ∀ B₁ ∈ C, ∀ B₂ ∈ C, B₁ ≠ B₂ → Disjoint B₁ B₂)
    (F : Finset J → (J → ι) → R)
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
theorem tupleZ_eq_sum_partitions (w : ι → 𝕂) (Λ : Finset ι)
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
    have h2 : (ursellSetSum (P.pull h) B : 𝕂) = ursellSetSum (P.pull h') B :=
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
theorem tupleU_eq_clusterOrderSum [LinearOrder J] (w : ι → 𝕂) (Λ : Finset ι)
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
    change ((oi (oi.symm ⟨j, hj⟩) : {x // x ∈ B}) : J) = j
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
      (ursellSetSum (P.pull h) B : 𝕂) = ((ursellInt P (h ∘ f) : ℤ) : 𝕂) := by
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
    change (if hj : f i ∈ B then γ (oi.symm ⟨f i, hj⟩) else γstar) = γ i
    rw [dif_pos (hfB i), hsymmf i (hfB i)]
  -- Die Summanden stimmen überein.
  · intro h _
    show (∏ j ∈ B, w (h j)) * (ursellSetSum (P.pull h) B : 𝕂)
        = ((ursellInt P (h ∘ f) : ℤ) : 𝕂) * ∏ i, w ((h ∘ f) i)
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
        change P.incomp (h i) (h j) = true
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
    change P.incomp (h i) (h j) = false
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
private theorem fiber_sum_eq (w : ι → 𝕂) {Λ S : Finset ι} {m : ℕ}
    (hSsub : S ⊆ Λ) (hSind : Indep P S) (hScard : S.card = m) :
    ∑ h ∈ ((Fintype.piFinset fun _ : Fin m => Λ).filter
        (fun h => Function.Injective h ∧ Indep P (Finset.univ.image h))).filter
        (fun h => Finset.univ.image h = S),
      ∏ j, w (h j)
    = (Nat.factorial m : 𝕂) * ∏ γ ∈ S, w γ := by
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
theorem tupleZ_univ_eq (w : ι → 𝕂) (Λ : Finset ι) (γstar : ι) (m : ℕ) :
    tupleZ P w Λ γstar (Finset.univ : Finset (Fin m))
      = (Nat.factorial m : 𝕂) *
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
theorem Z_eq_sum_tupleZ (w : ι → 𝕂) (Λ : Finset ι) (γstar : ι) {M : ℕ}
    (hM : Λ.card ≤ M) :
    Z P w Λ = ∑ m ∈ Finset.range (M + 1),
      tupleZ P w Λ γstar (Finset.univ : Finset (Fin m))
        / (Nat.factorial m : 𝕂) := by
  have hmaps : ∀ S ∈ Λ.powerset.filter (fun S => Indep P S),
      S.card ∈ Finset.range (M + 1) := by
    intro S hS
    obtain ⟨hSpow, -⟩ := Finset.mem_filter.mp hS
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le
      ((Finset.card_le_card (Finset.mem_powerset.mp hSpow)).trans hM))
  unfold Z
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun S => ∏ γ ∈ S, w γ)]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hfac : (Nat.factorial m : 𝕂) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  rw [tupleZ_univ_eq, mul_div_cancel_left₀ _ hfac, Finset.filter_filter]

/-! ## Die verschobene Koeffizientenfolge -/

omit [DecidableEq ι] [DecidableEq J] [Fintype J] in
/-- Über der leeren Polymermenge verschwindet jeder Reihenbeitrag. -/
theorem clusterOrderSum_of_empty (w : ι → 𝕂) (n : ℕ) :
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
theorem clusterSeries_empty (w : ι → 𝕂) :
    clusterSeries P w (∅ : Finset ι) = 0 := by
  unfold clusterSeries clusterCoeff
  rw [tsum_congr fun n => by rw [clusterOrderSum_of_empty, zero_div]]
  exact tsum_zero

/-- Die um eins verschobene Koeffizientenfolge der Cluster-Reihe:
`v 0 = 0`, `v (n+1) = clusterCoeff n`. Sie erfüllt die Voraussetzung
`v 0 = 0` des Exponentialschritts. -/
noncomputable def seriesSeq (w : ι → 𝕂) (Λ : Finset ι) (j : ℕ) : 𝕂 :=
  if j = 0 then 0 else clusterCoeff P w Λ (j - 1)

omit [DecidableEq ι] [DecidableEq J] [Fintype J] in
theorem seriesSeq_zero (w : ι → 𝕂) (Λ : Finset ι) : seriesSeq P w Λ 0 = 0 :=
  rfl

omit [DecidableEq ι] [DecidableEq J] [Fintype J] in
theorem seriesSeq_succ (w : ι → 𝕂) (Λ : Finset ι) (n : ℕ) :
    seriesSeq P w Λ (n + 1) = clusterCoeff P w Λ n := by
  unfold seriesSeq
  rw [if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel]

omit [DecidableEq ι] [DecidableEq J] [Fintype J] in
theorem abs_seriesSeq_le (w : ι → 𝕂) (Λ : Finset ι) (j : ℕ) :
    ‖seriesSeq P w Λ j‖ ≤ (Real.exp 1 * ∑ x ∈ Λ, ‖w x‖) ^ j := by
  cases j with
  | zero =>
    rw [seriesSeq_zero, norm_zero, pow_zero]
    exact zero_le_one
  | succ n =>
    rw [seriesSeq_succ]
    exact abs_clusterCoeff_le P w Λ n

omit [DecidableEq ι] [DecidableEq J] [Fintype J] in
/-- Absolute Summierbarkeit der Reihenglieder überträgt sich auf die
verschobene Folge: das nullte Glied ist null. -/
theorem summable_abs_seriesSeq (w : ι → 𝕂) (Λ : Finset ι)
    (h : Summable fun n => ‖clusterCoeff P w Λ n‖) :
    Summable fun j => ‖seriesSeq P w Λ j‖ := by
  refine (summable_nat_add_iff 1).mp (h.congr fun n => ?_)
  rw [seriesSeq_succ]

omit [DecidableEq ι] [DecidableEq J] [Fintype J] in
theorem summable_seriesSeq (w : ι → 𝕂) (Λ : Finset ι)
    (h : Summable fun n => ‖clusterCoeff P w Λ n‖) :
    Summable fun j => seriesSeq P w Λ j :=
  Summable.of_norm (summable_abs_seriesSeq P w Λ h)

omit [DecidableEq ι] [DecidableEq J] [Fintype J] in
/-- Die verschobene Folge summiert sich zur Cluster-Reihe. -/
theorem tsum_seriesSeq (w : ι → 𝕂) (Λ : Finset ι)
    (h : Summable fun n => ‖clusterCoeff P w Λ n‖) :
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
theorem summable_tupleProd (u : ℕ → 𝕂) (hu : Summable fun j => ‖u j‖) (k : ℕ) :
    Summable fun c : Fin k → ℕ => ∏ i, ‖u (c i)‖ := by
  induction k with
  | zero => exact .of_finite
  | succ k ih =>
    have hp : Summable fun p : ℕ × (Fin k → ℕ) => ‖u p.1‖ * ∏ i, ‖u (p.2 i)‖ :=
      Summable.mul_of_nonneg (f := fun j => ‖u j‖)
        (g := fun c : Fin k → ℕ => ∏ i, ‖u (c i)‖) hu ih
        (fun _ => norm_nonneg _)
        (fun _ => Finset.prod_nonneg fun _ _ => norm_nonneg _)
    refine (Equiv.summable_iff (Fin.consEquiv fun _ : Fin (k + 1) => ℕ)).mp
      (hp.congr fun p => ?_)
    simp [Fin.prod_univ_succ]

/-- Potenzen einer absolut konvergenten Reihe als Tupelsummen. -/
theorem tsum_pow_eq_tsum_tuple (u : ℕ → 𝕂) (hu : Summable fun j => ‖u j‖)
    (k : ℕ) :
    (∑' j, u j) ^ k = ∑' c : Fin k → ℕ, ∏ i, u (c i) := by
  induction k with
  | zero =>
    rw [pow_zero, tsum_fintype]
    simp
  | succ k ih =>
    have hnu : Summable fun j => ‖u j‖ := by
      exact hu
    have hnt : Summable fun c : Fin k → ℕ => ‖∏ i, u (c i)‖ :=
      (summable_tupleProd u hu k).congr fun c => by
        rw [norm_prod]
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
theorem support_subset_range_compEmb (u : ℕ → 𝕂) (hu0 : u 0 = 0) (k : ℕ) :
    Function.support (fun c : Fin k → ℕ => ∏ i, u (c i))
      ⊆ Set.range (compEmb k) := by
  intro c hc
  have hc' : ∏ i, u (c i) ≠ 0 := hc
  have hne : ∀ i, c i ≠ 0 := by
    intro i hi0
    exact hc' (Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi0, hu0]))
  exact ⟨⟨∑ i, c i, c, mem_compositionsF.mpr ⟨hne, rfl⟩⟩, rfl⟩

/-- Die Tupelsumme, nach dem Gesamtgewicht gebündelt. -/
theorem tsum_tuple_eq_tsum_compositions (u : ℕ → 𝕂) (hu0 : u 0 = 0)
    (hu : Summable fun j => ‖u j‖) (k : ℕ) :
    ∑' c : Fin k → ℕ, ∏ i, u (c i)
      = ∑' m : ℕ, ∑ c ∈ compositionsF m k, ∏ i, u (c i) := by
  have habs : Summable fun c : Fin k → ℕ => ‖∏ i, u (c i)‖ :=
    (summable_tupleProd u hu k).congr fun c => (norm_prod _ _).symm
  have hsig : Summable
      fun x : Σ m : ℕ, {c : Fin k → ℕ // c ∈ compositionsF m k} =>
      ∏ i, u (x.2.val i) :=
    habs.of_norm.comp_injective (compEmb_injective k)
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
theorem summable_compositions_abs (u : ℕ → 𝕂)
    (hu : Summable fun j => ‖u j‖) (k : ℕ) :
    Summable fun m : ℕ => ∑ c ∈ compositionsF m k, ∏ i, ‖u (c i)‖ := by
  have hsig : Summable
      fun x : Σ m : ℕ, {c : Fin k → ℕ // c ∈ compositionsF m k} =>
      ∏ i, ‖u (x.2.val i)‖ :=
    (summable_tupleProd u hu k).comp_injective (compEmb_injective k)
  exact hsig.sigma.congr fun m => Finset.tsum_subtype (compositionsF m k)
    (fun c => ∏ i, ‖u (c i)‖)

/-- Wert der gebündelten Betragsreihe: die `k`-te Potenz der
Betragssumme. -/
theorem tsum_compositions_abs (u : ℕ → 𝕂) (hu0 : u 0 = 0)
    (hu : Summable fun j => ‖u j‖) (k : ℕ) :
    ∑' m : ℕ, ∑ c ∈ compositionsF m k, ∏ i, ‖u (c i)‖
      = (∑' j, ‖u j‖) ^ k := by
  have hw : Summable fun j => ‖‖u j‖‖ :=
    hu.congr fun j => (norm_norm (u j)).symm
  have hw0 : ‖u 0‖ = 0 := by rw [hu0, norm_zero]
  calc ∑' m : ℕ, ∑ c ∈ compositionsF m k, ∏ i, ‖u (c i)‖
      = ∑' c : Fin k → ℕ, ∏ i, ‖u (c i)‖ :=
        (tsum_tuple_eq_tsum_compositions (fun j => ‖u j‖) hw0 hw k).symm
    _ = (∑' j, ‖u j‖) ^ k :=
        (tsum_pow_eq_tsum_tuple (fun j => ‖u j‖) hw k).symm

/-- **Der analytische Exponentialschritt**: `exp` einer absolut
konvergenten Reihe ist die nach dem Gesamtgewicht `m` umgruppierte
Kompositionssumme. -/
theorem exp_tsum_eq (v : ℕ → 𝕂) (hv0 : v 0 = 0)
    (habs : Summable fun j => ‖v j‖) :
    NormedSpace.exp (∑' j, v j)
      = ∑' m, ∑ k ∈ Finset.range (m + 1), (Nat.factorial k : 𝕂)⁻¹ *
          ∑ c ∈ compositionsF m k, ∏ i, v (c i) := by
  have hnn : ∀ k : ℕ, ‖((Nat.factorial k : 𝕂))⁻¹‖ = (Nat.factorial k : ℝ)⁻¹ := by
    intro k
    rw [norm_inv, ← RCLike.ofReal_natCast, RCLike.norm_ofReal,
      abs_of_nonneg (Nat.cast_nonneg _)]
  have hfac : ∀ k : ℕ, (0 : ℝ) ≤ (Nat.factorial k : ℝ)⁻¹ := fun k =>
    inv_nonneg.mpr (Nat.cast_nonneg _)
  -- Summierbarkeit der Betrags-Majorante über dem Produktgitter.
  have hHpos : ∀ p : ℕ × ℕ, 0 ≤ (Nat.factorial p.1 : ℝ)⁻¹ *
      ∑ c ∈ compositionsF p.2 p.1, ∏ i, ‖v (c i)‖ := fun p =>
    mul_nonneg (hfac p.1) (Finset.sum_nonneg fun c _ =>
      Finset.prod_nonneg fun i _ => norm_nonneg _)
  have hH : Summable fun p : ℕ × ℕ => (Nat.factorial p.1 : ℝ)⁻¹ *
      ∑ c ∈ compositionsF p.2 p.1, ∏ i, ‖v (c i)‖ := by
    refine (summable_prod_of_nonneg hHpos).mpr ⟨fun k => ?_, ?_⟩
    · change Summable fun m : ℕ => (Nat.factorial k : ℝ)⁻¹ *
        ∑ c ∈ compositionsF m k, ∏ i, ‖v (c i)‖
      exact (summable_compositions_abs v habs k).mul_left _
    · change Summable fun k : ℕ => ∑' m : ℕ, (Nat.factorial k : ℝ)⁻¹ *
        ∑ c ∈ compositionsF m k, ∏ i, ‖v (c i)‖
      have hgeom : Summable fun k : ℕ =>
          (Nat.factorial k : ℝ)⁻¹ * (∑' j, ‖v j‖) ^ k :=
        (Real.summable_pow_div_factorial (∑' j, ‖v j‖)).congr fun k =>
          (inv_mul_eq_div _ _).symm
      refine hgeom.congr fun k => ?_
      rw [tsum_mul_left, tsum_compositions_abs v hv0 habs k]
  -- Absolute Schranke für die vorzeichenbehaftete Familie.
  have hGabs : ∀ p : ℕ × ℕ,
      ‖(Nat.factorial p.1 : 𝕂)⁻¹ * ∑ c ∈ compositionsF p.2 p.1, ∏ i, v (c i)‖
        ≤ (Nat.factorial p.1 : ℝ)⁻¹ *
            ∑ c ∈ compositionsF p.2 p.1, ∏ i, ‖v (c i)‖ := by
    intro p
    rw [norm_mul, hnn p.1]
    refine mul_le_mul_of_nonneg_left ?_ (hfac p.1)
    calc ‖∑ c ∈ compositionsF p.2 p.1, ∏ i, v (c i)‖
        ≤ ∑ c ∈ compositionsF p.2 p.1, ‖∏ i, v (c i)‖ :=
          norm_sum_le _ _
      _ = ∑ c ∈ compositionsF p.2 p.1, ∏ i, ‖v (c i)‖ :=
          Finset.sum_congr rfl fun c _ => norm_prod _ _
  have hG : Summable fun p : ℕ × ℕ => (Nat.factorial p.1 : 𝕂)⁻¹ *
      ∑ c ∈ compositionsF p.2 p.1, ∏ i, v (c i) :=
    (Summable.of_nonneg_of_le (fun p => norm_nonneg _) hGabs hH).of_norm
  calc NormedSpace.exp (∑' j, v j)
      = ∑' k : ℕ, (∑' j, v j) ^ k / (Nat.factorial k : 𝕂) := by
        simp only [NormedSpace.exp_eq_tsum_div]
    _ = ∑' k : ℕ, ∑' m : ℕ, (Nat.factorial k : 𝕂)⁻¹ *
          ∑ c ∈ compositionsF m k, ∏ i, v (c i) := by
        refine tsum_congr fun k => ?_
        rw [div_eq_inv_mul, tsum_pow_eq_tsum_tuple v habs k,
          tsum_tuple_eq_tsum_compositions v hv0 habs k, ← tsum_mul_left]
    _ = ∑' m : ℕ, ∑' k : ℕ, (Nat.factorial k : 𝕂)⁻¹ *
          ∑ c ∈ compositionsF m k, ∏ i, v (c i) :=
        (Summable.tsum_comm (f := fun k m => (Nat.factorial k : 𝕂)⁻¹ *
          ∑ c ∈ compositionsF m k, ∏ i, v (c i)) hG).symm
    _ = ∑' m : ℕ, ∑ k ∈ Finset.range (m + 1), (Nat.factorial k : 𝕂)⁻¹ *
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

/-! ## Die Exponentialformel -/

omit [DecidableEq ι] [DecidableEq J] [Fintype J] in
/-- Oberhalb der Kardinalität von `Λ` verschwindet die Tupel-Z-Summe:
es gibt keine `m`-elementigen unabhängigen Teilmengen mehr. -/
theorem tupleZ_univ_vanish (w : ι → 𝕂) (Λ : Finset ι) (γstar : ι) {m : ℕ}
    (hm : Λ.card < m) :
    tupleZ P w Λ γstar (Finset.univ : Finset (Fin m)) = 0 := by
  rw [tupleZ_univ_eq]
  have hempty : Λ.powerset.filter (fun S => Indep P S ∧ S.card = m) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro S hS
    obtain ⟨hSpow, -, hScard⟩ := Finset.mem_filter.mp hS
    have := Finset.card_le_card (Finset.mem_powerset.mp hSpow)
    omega
  rw [hempty, Finset.sum_empty, mul_zero]

omit [DecidableEq J] [Fintype J] in
/-- **Exponentialformel der Cluster-Entwicklung**: im Kleinheitsregime
`e · ∑_Λ |w| < 1` ist die Zustandssumme das Exponential der
Cluster-Reihe.

Der Beweis führt die fünf Bausteine zusammen: der analytische
Exponentialschritt (`exp_tsum_eq`) entwickelt `exp` der Reihe in
Kompositionen; die Multinomialzählung (`sum_partitionsOf_card`)
übersetzt sie in Partitionssummen; Blockzerlegung
(`tupleZ_eq_sum_partitions`) und Blockreduktion
(`tupleU_eq_clusterOrderSum`) identifizieren diese mit `tupleZ`; und
die Schichtzählung (`Z_eq_sum_tupleZ`) summiert die Schichten zu `Z`.
Die Reihe bricht bei `|Λ|` ab, weil es keine größeren unabhängigen
Mengen gibt. -/
theorem exp_clusterSeries_eq_Z (w : ι → 𝕂) (Λ : Finset ι)
    (hconv : Summable fun n => ‖clusterCoeff P w Λ n‖) :
    NormedSpace.exp (clusterSeries P w Λ) = Z P w Λ := by
  rcases Λ.eq_empty_or_nonempty with rfl | hne
  · rw [clusterSeries_empty, NormedSpace.exp_zero, Z_empty]
  obtain ⟨γstar, -⟩ := hne
  -- Schritt 1: `exp` der Reihe als umgruppierte Kompositionssumme.
  have hexp := exp_tsum_eq (seriesSeq P w Λ) (seriesSeq_zero P w Λ)
    (summable_abs_seriesSeq P w Λ hconv)
  rw [tsum_seriesSeq P w Λ hconv] at hexp
  -- Schritt 2: das `m`-te Glied ist `tupleZ (univ : Fin m) / m!`.
  have hterm : ∀ m : ℕ,
      (∑ k ∈ Finset.range (m + 1), (Nat.factorial k : 𝕂)⁻¹ *
        ∑ c ∈ compositionsF m k, ∏ i, seriesSeq P w Λ (c i))
      = tupleZ P w Λ γstar (Finset.univ : Finset (Fin m))
          / (Nat.factorial m : 𝕂) := by
    intro m
    have hcard : (Finset.univ : Finset (Fin m)).card = m := by
      rw [Finset.card_univ, Fintype.card_fin]
    have h1 : tupleZ P w Λ γstar (Finset.univ : Finset (Fin m))
        = ∑ C ∈ partitionsOf (Finset.univ : Finset (Fin m)),
            ∏ B ∈ C, (fun s => clusterOrderSum P w Λ (s - 1)) B.card := by
      rw [tupleZ_eq_sum_partitions P w Λ γstar]
      refine Finset.sum_congr rfl fun C hC => ?_
      obtain ⟨-, hICC, -⟩ := mem_partitionsOf.mp hC
      exact Finset.prod_congr rfl fun B hB =>
        tupleU_eq_clusterOrderSum P w Λ γstar (hICC.1 B hB)
    rw [h1, sum_partitionsOf_card (Finset.univ : Finset (Fin m))
      (fun s => clusterOrderSum P w Λ (s - 1)), hcard]
    have hmne : (Nat.factorial m : 𝕂) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
    rw [eq_div_iff hmne, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun c hc => ?_
    obtain ⟨hpos, -⟩ := mem_compositionsF.mp hc
    have hv : ∀ i, seriesSeq P w Λ (c i)
        = clusterOrderSum P w Λ (c i - 1) / (Nat.factorial (c i) : 𝕂) := by
      intro i
      unfold seriesSeq
      rw [if_neg (hpos i)]
      unfold clusterCoeff
      have hci : c i - 1 + 1 = c i := by have := hpos i; omega
      rw [hci]
    rw [Finset.prod_congr rfl fun i _ => hv i, Finset.prod_div_distrib]
    have hfacne : (∏ i, (Nat.factorial (c i) : 𝕂)) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
      exact_mod_cast (Nat.factorial_pos (c i)).ne'
    field_simp
  -- Schritt 3: die Reihe bricht bei `|Λ|` ab und ist die Zustandssumme.
  have hvanish : ∀ m ∉ Finset.range (Λ.card + 1),
      tupleZ P w Λ γstar (Finset.univ : Finset (Fin m))
        / (Nat.factorial m : 𝕂) = 0 := by
    intro m hm
    rw [Finset.mem_range] at hm
    rw [tupleZ_univ_vanish P w Λ γstar (by omega), zero_div]
  calc NormedSpace.exp (clusterSeries P w Λ)
      = ∑' m, ∑ k ∈ Finset.range (m + 1), (Nat.factorial k : 𝕂)⁻¹ *
          ∑ c ∈ compositionsF m k, ∏ i, seriesSeq P w Λ (c i) := hexp
    _ = ∑' m, tupleZ P w Λ γstar (Finset.univ : Finset (Fin m))
          / (Nat.factorial m : 𝕂) := tsum_congr hterm
    _ = ∑ m ∈ Finset.range (Λ.card + 1),
          tupleZ P w Λ γstar (Finset.univ : Finset (Fin m))
            / (Nat.factorial m : 𝕂) := tsum_eq_sum hvanish
    _ = Z P w Λ := (Z_eq_sum_tupleZ P w Λ γstar le_rfl).symm

omit [DecidableEq J] [Fintype J] in
/-- **Die Exponentialformel für reelle Gewichte.** -/
theorem exp_clusterSeries_eq_Z_real (w : ι → ℝ) (Λ : Finset ι)
    (hconv : Summable fun n => |clusterCoeff P w Λ n|) :
    Real.exp (clusterSeries P w Λ) = Z P w Λ := by
  rw [Real.exp_eq_exp_ℝ]
  exact exp_clusterSeries_eq_Z P w Λ (hconv.congr fun n => (Real.norm_eq_abs _).symm)

omit [DecidableEq J] [Fintype J] in
/-- **Die Exponentialformel für komplexe Gewichte.** -/
theorem exp_clusterSeries_eq_Z_complex (w : ι → ℂ) (Λ : Finset ι)
    (hconv : Summable fun n => ‖clusterCoeff P w Λ n‖) :
    Complex.exp (clusterSeries P w Λ) = Z P w Λ := by
  rw [Complex.exp_eq_exp_ℂ]
  exact exp_clusterSeries_eq_Z P w Λ hconv

omit [DecidableEq J] [Fintype J] in
/-- Im Kleinheitsregime ist die Zustandssumme strikt positiv — sie ist
ein reelles Exponential. Insbesondere ist sie nichtnull, ohne Umweg über
die Konvergenzkriterien. -/
theorem Z_pos_of_summable (w : ι → ℝ) (Λ : Finset ι)
    (hconv : Summable fun n => |clusterCoeff P w Λ n|) :
    0 < Z P w Λ := by
  rw [← exp_clusterSeries_eq_Z_real P w Λ hconv]
  exact Real.exp_pos _

omit [DecidableEq J] [Fintype J] in
/-- **`log Z` ist die Cluster-Reihe**: im Kleinheitsregime stimmt der
Logarithmus der Zustandssumme mit der Cluster-Reihe überein. Zusammen
mit `abs_clusterSeries_le` liefert das die volumenlineare Kontrolle von
`log Z` direkt aus der Reihe. -/
theorem log_Z_eq_clusterSeries (w : ι → ℝ) (Λ : Finset ι)
    (hconv : Summable fun n => |clusterCoeff P w Λ n|) :
    Real.log (Z P w Λ) = clusterSeries P w Λ := by
  rw [← exp_clusterSeries_eq_Z_real P w Λ hconv, Real.log_exp]

omit [DecidableEq J] [Fintype J] in
/-- **Die Exponentialformel im Kleinheitsregime**: für
`e · ∑_Λ ‖w‖ < 1` ist `Z` das Exponential der Cluster-Reihe. Die
Aussage gilt über jedem `RCLike`-Körper, also reell wie komplex. -/
theorem exp_clusterSeries_eq_Z_of_small (w : ι → 𝕂) (Λ : Finset ι)
    (hsmall : Real.exp 1 * ∑ x ∈ Λ, ‖w x‖ < 1) :
    NormedSpace.exp (clusterSeries P w Λ) = Z P w Λ :=
  exp_clusterSeries_eq_Z P w Λ (summable_abs_clusterCoeff P w Λ hsmall)

omit [DecidableEq J] [Fintype J] in
/-- Im Kleinheitsregime ist die Zustandssumme strikt positiv. -/
theorem Z_pos_of_small (w : ι → ℝ) (Λ : Finset ι)
    (hsmall : Real.exp 1 * ∑ x ∈ Λ, |w x| < 1) :
    0 < Z P w Λ :=
  Z_pos_of_summable P w Λ
    ((summable_abs_clusterCoeff P w Λ
      (by simpa only [Real.norm_eq_abs] using hsmall)).congr
      fun n => Real.norm_eq_abs _)

omit [DecidableEq J] [Fintype J] in
/-- **`log Z` ist die Cluster-Reihe** im Kleinheitsregime. -/
theorem log_Z_eq_clusterSeries_of_small (w : ι → ℝ) (Λ : Finset ι)
    (hsmall : Real.exp 1 * ∑ x ∈ Λ, |w x| < 1) :
    Real.log (Z P w Λ) = clusterSeries P w Λ :=
  log_Z_eq_clusterSeries P w Λ
    ((summable_abs_clusterCoeff P w Λ
      (by simpa only [Real.norm_eq_abs] using hsmall)).congr
      fun n => Real.norm_eq_abs _)

end ClusterExpansion
