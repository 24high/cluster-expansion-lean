/-
Copyright (c) 2026 Dennis Michael Heine. All rights reserved.
Released under the CC BY-NC-SA 4.0 license as described in the file LICENSE.
Authors: Dennis Michael Heine
-/
import KPLean.Trees

/-!
# Die Zerlegung eines Wurzelbaums an seiner Wurzel

Der kombinatorische Kern der scharfen Kotecký-Preiss-Schranke: die
Teilbäume unter den Kindern der Wurzel bilden eine Partition der
Nichtwurzelknoten (`subtreeOf_image_mem_partitionsOf`), jeder Teilbaum
ist selbst ein Wurzelbaum (`restrictParent_mem_rootedTrees`), und Gewicht
wie Kantenbedingung zerfallen blockweise (`prod_eq_prod_blocks`,
`treeIncompatible_restrict`, `block_weight_le`).
-/

open Finset

set_option linter.style.openClassical false

open scoped Classical

namespace ClusterExpansion


variable {J : Type*} [DecidableEq J] [Fintype J]

/-! ## Die Wurzel ist ein Fixpunkt -/

omit [DecidableEq J] [Fintype J] in
/-- Ist die Wurzel einmal erreicht, bleibt sie erreicht: aus `p^[k] v = r`
und `p r = r` folgt `p^[j] v = r` für alle `j ≥ k`. -/
theorem iterate_eq_root_of_le {r : J} {p : J → J} (hpr : p r = r) {v : J}
    {k j : ℕ} (hk : p^[k] v = r) (hj : k ≤ j) : p^[j] v = r := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [Nat.add_comm, Function.iterate_add_apply, hk, Function.iterate_fixed hpr]

/-! ## Das Kind der Wurzel über einem Knoten -/

/-- **Der Wurzelvorfahr**: jeder Knoten von `A` liegt im Teilbaum eines
Kindes der Wurzel. Genommen wird das kleinste `k` mit `p^[k+1] v = r`;
dann ist `p^[k] v` das gesuchte Kind. -/
theorem exists_rootChild_mem_subtreeOf {A : Finset J} {r : J} {p : J → J}
    (hp : p ∈ rootedTrees A r) {v : J} (hv : v ∈ A) :
    ∃ c ∈ rootChildren A r p, v ∈ subtreeOf A r p c := by
  obtain ⟨-, hpr, -, hreach⟩ := mem_rootedTrees.mp hp
  have hex : ∃ k, p^[k + 1] v = r := by
    obtain ⟨k, hk⟩ := hreach v hv
    exact ⟨k, iterate_eq_root_of_le hpr hk (Nat.le_succ k)⟩
  obtain ⟨k, hk, hmin⟩ : ∃ k, p^[k + 1] v = r ∧ ∀ j < k, p^[j + 1] v ≠ r :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hcA : p^[k] v ∈ A := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0, Function.iterate_zero_apply]
      exact hv
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rcases Finset.mem_insert.mp (iterate_mem_rootedTrees hp v (j + 1)
        (Nat.succ_ne_zero j)) with hrr | hAA
      · exact absurd hrr (hmin j (by omega))
      · exact hAA
  exact ⟨p^[k] v, mem_rootChildren.mpr
    ⟨hcA, (Function.iterate_succ_apply' p k v).symm.trans hk⟩,
    mem_subtreeOf.mpr ⟨hv, k, rfl, hk⟩⟩

/-! ## Eindeutigkeit des Kindes -/

omit [DecidableEq J] [Fintype J] in
/-- **Eindeutigkeit**: ein Knoten liegt im Teilbaum höchstens eines
Kindes der Wurzel. Wäre die eine Kette echt kürzer, so hätte die längere
die Wurzel schon überschritten. -/
theorem subtreeOf_unique {A : Finset J} {r : J} {p : J → J} (hpr : p r = r)
    (hr : r ∉ A) {c c' v : J} (hc : c ∈ A) (hc' : c' ∈ A)
    (hv : v ∈ subtreeOf A r p c) (hv' : v ∈ subtreeOf A r p c') : c = c' := by
  obtain ⟨-, k, hkc, hkr⟩ := mem_subtreeOf.mp hv
  obtain ⟨-, l, hlc, hlr⟩ := mem_subtreeOf.mp hv'
  rcases lt_trichotomy k l with hlt | rfl | hgt
  · exfalso
    have hrl : p^[l] v = r := iterate_eq_root_of_le hpr hkr (by omega)
    have : c' = r := hlc.symm.trans hrl
    rw [this] at hc'
    exact hr hc'
  · rw [← hkc, ← hlc]
  · exfalso
    have hrk : p^[k] v = r := iterate_eq_root_of_le hpr hlr (by omega)
    have : c = r := hkc.symm.trans hrk
    rw [this] at hc
    exact hr hc

/-! ## Die Teilbäume bilden eine Partition -/

/-- **Die Wurzelzerlegung**: die Teilbäume unter den Kindern der Wurzel
bilden eine Partition der Nichtwurzelknoten. -/
theorem subtreeOf_image_mem_partitionsOf {A : Finset J} {r : J} {p : J → J}
    (hp : p ∈ rootedTrees A r) (hr : r ∉ A) :
    (rootChildren A r p).image (subtreeOf A r p) ∈ partitionsOf A := by
  obtain ⟨-, hpr, -, -⟩ := mem_rootedTrees.mp hp
  refine mem_partitionsOf.mpr ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · intro B hB
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hB
    exact subtreeOf_subset
  · intro B hB
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨hcA, hpc⟩ := mem_rootChildren.mp hc
    exact ⟨c, self_mem_subtreeOf hcA hpc⟩
  · intro B₁ h₁ B₂ h₂ hne
    obtain ⟨c₁, hc₁, rfl⟩ := Finset.mem_image.mp h₁
    obtain ⟨c₂, hc₂, rfl⟩ := Finset.mem_image.mp h₂
    rw [Finset.disjoint_left]
    intro v hv₁ hv₂
    exact hne (congrArg (subtreeOf A r p)
      (subtreeOf_unique hpr hr (mem_rootChildren.mp hc₁).1
        (mem_rootChildren.mp hc₂).1 hv₁ hv₂))
  · refine le_antisymm (Finset.sup_le fun B hB => ?_) ?_
    · obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hB
      exact subtreeOf_subset
    · intro v hv
      obtain ⟨c, hc, hvc⟩ := exists_rootChild_mem_subtreeOf hp hv
      exact Finset.mem_sup.mpr
        ⟨subtreeOf A r p c, Finset.mem_image_of_mem _ hc, hvc⟩

/-- Verschiedene Kinder der Wurzel haben verschiedene Teilbäume. -/
theorem subtreeOf_injOn_rootChildren {A : Finset J} {r : J} {p : J → J}
    (hp : p ∈ rootedTrees A r) (hr : r ∉ A) :
    Set.InjOn (subtreeOf A r p) (rootChildren A r p) := by
  obtain ⟨-, hpr, -, -⟩ := mem_rootedTrees.mp hp
  intro c₁ h₁ c₂ h₂ heq
  obtain ⟨hc₁, hp₁⟩ := mem_rootChildren.mp (Finset.mem_coe.mp h₁)
  obtain ⟨hc₂, -⟩ := mem_rootChildren.mp (Finset.mem_coe.mp h₂)
  exact subtreeOf_unique hpr hr hc₁ hc₂ (self_mem_subtreeOf hc₁ hp₁)
    (heq ▸ self_mem_subtreeOf hc₁ hp₁)

/-! ## Der Teilbaum ist selbst ein Wurzelbaum -/

/-- Der Elternknoten eines von `c` verschiedenen Knotens des Teilbaums
liegt wieder in diesem Teilbaum. -/
theorem parent_mem_subtreeOf {A : Finset J} {r : J} {p : J → J}
    (hp : p ∈ rootedTrees A r) (hr : r ∉ A) {c v : J} (hc : c ∈ A)
    (hv : v ∈ subtreeOf A r p c) (hvc : v ≠ c) : p v ∈ subtreeOf A r p c := by
  obtain ⟨hpi, hpr, -, -⟩ := mem_rootedTrees.mp hp
  obtain ⟨-, k, hkc, hkr⟩ := mem_subtreeOf.mp hv
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact absurd hkc hvc
    · exact ⟨k - 1, by omega⟩
  have hkc' : p^[j] (p v) = c := (Function.iterate_succ_apply p j v).symm.trans hkc
  have hkr' : p^[j + 1] (p v) = r :=
    (Function.iterate_succ_apply p (j + 1) v).symm.trans hkr
  refine mem_subtreeOf.mpr ⟨?_, j, hkc', hkr'⟩
  rcases Finset.mem_insert.mp (hpi v) with hrr | hAA
  · exact absurd (by rw [← hkc', hrr, Function.iterate_fixed hpr] : c = r) fun h =>
      hr (h ▸ hc)
  · exact hAA

/-- Die auf einen Teilbaum eingeschränkte Elternabbildung: außerhalb des
Teilbaums und an dessen Wurzel `c` ist alles auf `c` festgenagelt. -/
noncomputable def restrictParent (A : Finset J) (r : J) (p : J → J) (c : J) :
    J → J :=
  fun v => if v ∈ (subtreeOf A r p c).erase c then p v else c

/-- Solange die `p`-Kette den Teilbaum nicht verlässt, stimmen die
Iterationen der eingeschränkten Elternabbildung mit denen von `p` überein. -/
theorem iterate_restrictParent {A : Finset J} {r : J} {p : J → J}
    (hp : p ∈ rootedTrees A r) (hr : r ∉ A) {c : J} (hc : c ∈ A)
    (hpc : p c = r) :
    ∀ (k : ℕ) (v : J), v ∈ subtreeOf A r p c → p^[k] v = c → p^[k + 1] v = r →
      (restrictParent A r p c)^[k] v = c := by
  obtain ⟨-, hpr, -, -⟩ := mem_rootedTrees.mp hp
  intro k
  induction k with
  | zero =>
    intro v _ hkc _
    exact hkc
  | succ k IH =>
    intro v hv hkc hkr
    have hvc : v ≠ c := by
      intro hvc0
      refine hr ?_
      have hcr : c = r := by
        rw [← hkc, hvc0, Function.iterate_succ_apply, hpc,
          Function.iterate_fixed hpr]
      exact hcr ▸ hc
    have hstep : restrictParent A r p c v = p v :=
      if_pos (Finset.mem_erase.mpr ⟨hvc, hv⟩)
    rw [Function.iterate_succ_apply, hstep]
    exact IH (p v) (parent_mem_subtreeOf hp hr hc hv hvc)
      ((Function.iterate_succ_apply p k v).symm.trans hkc)
      ((Function.iterate_succ_apply p (k + 1) v).symm.trans hkr)

/-- **Der Teilbaum ist ein Wurzelbaum**: die auf `subtreeOf A r p c`
eingeschränkte Elternabbildung ist ein Wurzelbaum über
`(subtreeOf A r p c).erase c` mit Wurzel `c`. -/
theorem restrictParent_mem_rootedTrees {A : Finset J} {r : J} {p : J → J}
    (hp : p ∈ rootedTrees A r) (hr : r ∉ A) {c : J}
    (hc : c ∈ rootChildren A r p) :
    restrictParent A r p c ∈ rootedTrees ((subtreeOf A r p c).erase c) c := by
  obtain ⟨hcA, hpc⟩ := mem_rootChildren.mp hc
  have hcB : c ∈ subtreeOf A r p c := self_mem_subtreeOf hcA hpc
  have hins : insert c ((subtreeOf A r p c).erase c) = subtreeOf A r p c :=
    Finset.insert_erase hcB
  refine mem_rootedTrees.mpr ⟨fun v => ?_, ?_, fun v hv => ?_, fun v hv => ?_⟩
  · rw [hins]
    by_cases hvB : v ∈ (subtreeOf A r p c).erase c
    · obtain ⟨hvc, hvS⟩ := Finset.mem_erase.mp hvB
      rw [show restrictParent A r p c v = p v from if_pos hvB]
      exact parent_mem_subtreeOf hp hr hcA hvS hvc
    · rw [show restrictParent A r p c v = c from if_neg hvB]
      exact hcB
  · exact if_neg (Finset.notMem_erase c _)
  · rw [hins] at hv
    exact if_neg fun hmem => hv (Finset.mem_of_mem_erase hmem)
  · have hvS : v ∈ subtreeOf A r p c := Finset.mem_of_mem_erase hv
    obtain ⟨-, k, hkc, hkr⟩ := mem_subtreeOf.mp hvS
    exact ⟨k, iterate_restrictParent hp hr hcA hpc k v hvS hkc hkr⟩

omit [Fintype J] in
/-- Ein Produkt über die Grundmenge zerfällt entlang einer Partition in
das Produkt der Blockprodukte. -/
theorem prod_eq_prod_blocks {M : Type*} [CommMonoid M] {A : Finset J}
    {C : Finset (Finset J)} (hC : C ∈ partitionsOf A) (f : J → M) :
    ∏ v ∈ A, f v = ∏ B ∈ C, ∏ v ∈ B, f v := by
  obtain ⟨-, hICC, hsup⟩ := mem_partitionsOf.mp hC
  have hpd : (↑C : Set (Finset J)).PairwiseDisjoint id :=
    fun B₁ h₁ B₂ h₂ hne =>
      hICC.2 B₁ (Finset.mem_coe.mp h₁) B₂ (Finset.mem_coe.mp h₂) hne
  rw [← hsup, sup_id_eq_biUnion, Finset.prod_biUnion hpd]
  simp only [id_eq]

/-! ## Bausteine der Baumsummenschranke -/

section Polymer

variable {ι : Type*} (P : PolymerSystem ι)

/-- **Fasern nach der Wurzelzerlegung**: die Baumsumme sortiert ihre
Wurzelbäume nach der Partition, die sie an der Wurzel erzeugen. -/
theorem treeSum_eq_sum_fiber (w : ι → ℝ) (Λ : Finset ι) (γ₀ : ι) (r : J)
    {A : Finset J} (hr : r ∉ A) :
    treeSum P w Λ γ₀ r A
      = ∑ C ∈ partitionsOf A,
          ∑ p ∈ (rootedTrees A r).filter
              (fun p => (rootChildren A r p).image (subtreeOf A r p) = C),
            ∑ h ∈ pinnedTuples Λ γ₀ A, (∏ v ∈ A, |w (h v)|) *
              (if TreeIncompatible P h A p then 1 else 0) := by
  unfold treeSum
  exact (Finset.sum_fiberwise_of_maps_to
    (fun _ hp => subtreeOf_image_mem_partitionsOf hp hr) _).symm

/-- **Die Kante zur Wurzel**: der Wert der Belegung an einem Kind der
Wurzel ist ein mit `γ₀` unverträgliches Polymer aus `Λ` — genau die
Bedingung, über die die Kotecký-Preiss-Schranke summiert. -/
theorem val_rootChild_mem_incompNbhd {Λ : Finset ι} {γ₀ : ι} {A : Finset J}
    {r : J} {p : J → J} {h : J → ι} (hr : r ∉ A)
    (hh : h ∈ pinnedTuples Λ γ₀ A) (hinc : TreeIncompatible P h A p)
    {c : J} (hc : c ∈ rootChildren A r p) : h c ∈ incompNbhd P Λ γ₀ := by
  obtain ⟨hcA, hpc⟩ := mem_rootChildren.mp hc
  obtain ⟨hin, hout⟩ := mem_pinnedTuples.mp hh
  refine (mem_incompNbhd P).mpr ⟨hin c hcA, ?_⟩
  have hedge := hinc c hcA
  rw [hpc, hout r hr] at hedge
  rw [P.symm]
  exact hedge

/-- Die auf einen Block eingeschränkte Belegung ist eine festgenagelte
Belegung mit frei wählbarem Wurzelwert. -/
theorem restrictOn_mem_pinnedTuples_pin {Λ : Finset ι} {γ₀ : ι}
    {A S : Finset J} {h : J → ι} (hS : S ⊆ A) (hh : h ∈ pinnedTuples Λ γ₀ A)
    (δ : ι) : restrictOn S δ h ∈ pinnedTuples Λ δ S := by
  obtain ⟨hin, -⟩ := mem_pinnedTuples.mp hh
  refine mem_pinnedTuples.mpr ⟨fun j hj => ?_, fun j hj => ?_⟩
  · rw [restrictOn, if_pos hj]
    exact hin j (hS hj)
  · rw [restrictOn, if_neg hj]

/-- **Der Teilbaum erbt die Unverträglichkeit**: eingeschränkte
Elternabbildung und eingeschränkte Belegung erfüllen die
Kantenbedingung wieder. Die Kante eines Knotens, dessen Elternknoten die
Blockwurzel `c` ist, wird durch den festgenagelten Wert `h c` getroffen. -/
theorem treeIncompatible_restrict {A : Finset J} {r : J} {p : J → J}
    {h : J → ι} (hp : p ∈ rootedTrees A r) (hr : r ∉ A)
    (hinc : TreeIncompatible P h A p) {c : J} (hc : c ∈ rootChildren A r p) :
    TreeIncompatible P (restrictOn ((subtreeOf A r p c).erase c) (h c) h)
      ((subtreeOf A r p c).erase c) (restrictParent A r p c) := by
  obtain ⟨hcA, -⟩ := mem_rootChildren.mp hc
  intro v hv
  obtain ⟨hvc, hvB⟩ := Finset.mem_erase.mp hv
  have hqv : restrictParent A r p c v = p v := if_pos hv
  have hgv : restrictOn ((subtreeOf A r p c).erase c) (h c) h v = h v := if_pos hv
  have hgp : restrictOn ((subtreeOf A r p c).erase c) (h c) h (p v) = h (p v) := by
    by_cases hpv : p v ∈ (subtreeOf A r p c).erase c
    · exact if_pos hpv
    · have hpvc : p v = c := by
        have := parent_mem_subtreeOf hp hr hcA hvB hvc
        by_contra hne
        exact hpv (Finset.mem_erase.mpr ⟨hne, this⟩)
      rw [hpvc]
      exact if_neg (Finset.notMem_erase c _)
  rw [hqv, hgv, hgp]
  exact hinc v (subtreeOf_subset hvB)

/-- **Der Blockbeitrag eines einzelnen Baumes**: das Gewicht eines Blocks
unter einer festen Belegung wird vom zugehörigen Faktor der rechten Seite
dominiert — der Blockfaktor enthält den Summanden mit dem Wurzelkind `c`,
dem Nachbarn `h c` und dem eingeschränkten Baum. -/
theorem block_weight_le (w : ι → ℝ) (Λ : Finset ι) (γ₀ : ι) {A : Finset J}
    {r : J} {p : J → J} {h : J → ι} (hp : p ∈ rootedTrees A r) (hr : r ∉ A)
    (hh : h ∈ pinnedTuples Λ γ₀ A) (hinc : TreeIncompatible P h A p)
    {c : J} (hc : c ∈ rootChildren A r p) :
    ∏ v ∈ subtreeOf A r p c, |w (h v)|
      ≤ ∑ c' ∈ subtreeOf A r p c, ∑ δ ∈ incompNbhd P Λ γ₀,
          |w δ| * treeSum P w Λ δ c' ((subtreeOf A r p c).erase c') := by
  obtain ⟨hcA, hpc⟩ := mem_rootChildren.mp hc
  set S : Finset J := (subtreeOf A r p c).erase c with hSdef
  set g : J → ι := restrictOn S (h c) h with hgdef
  have hgS : ∀ v ∈ S, g v = h v := fun v hv => if_pos hv
  have hgmem : g ∈ pinnedTuples Λ (h c) S :=
    restrictOn_mem_pinnedTuples_pin
      (fun x hx => subtreeOf_subset (Finset.mem_of_mem_erase hx)) hh (h c)
  have hqmem : restrictParent A r p c ∈ rootedTrees S c :=
    restrictParent_mem_rootedTrees hp hr hc
  have hnn : ∀ q : J → J, ∀ h' : J → ι,
      0 ≤ (∏ v ∈ S, |w (h' v)|) *
        (if TreeIncompatible P h' S q then 1 else 0) := by
    intro q h'
    refine mul_nonneg (Finset.prod_nonneg fun v _ => abs_nonneg _) ?_
    split <;> norm_num
  -- Die Baumsumme des Blocks enthält den Summanden des eingeschränkten Baumes.
  have htree : ∏ v ∈ S, |w (h v)| ≤ treeSum P w Λ (h c) c S := by
    have hinner : (∏ v ∈ S, |w (g v)|) *
        (if TreeIncompatible P g S (restrictParent A r p c) then 1 else 0)
        ≤ ∑ h' ∈ pinnedTuples Λ (h c) S, (∏ v ∈ S, |w (h' v)|) *
            (if TreeIncompatible P h' S (restrictParent A r p c) then 1 else 0) :=
      Finset.single_le_sum (fun h' _ => hnn _ h') hgmem
    have houter : (∑ h' ∈ pinnedTuples Λ (h c) S, (∏ v ∈ S, |w (h' v)|) *
          (if TreeIncompatible P h' S (restrictParent A r p c) then 1 else 0))
        ≤ treeSum P w Λ (h c) c S :=
      Finset.single_le_sum
        (fun q _ => Finset.sum_nonneg fun h' _ => hnn q h') hqmem
    refine le_trans (le_of_eq ?_) (hinner.trans houter)
    rw [if_pos (treeIncompatible_restrict P hp hr hinc hc), mul_one]
    exact Finset.prod_congr rfl fun v hv => by rw [hgS v hv]
  -- Der Summand mit `c' = c` und `δ = h c` steht in der rechten Seite.
  have hδ : h c ∈ incompNbhd P Λ γ₀ :=
    val_rootChild_mem_incompNbhd P hr hh hinc hc
  have hcB : c ∈ subtreeOf A r p c := self_mem_subtreeOf hcA hpc
  have hnn2 : ∀ c' ∈ subtreeOf A r p c, (0 : ℝ) ≤ ∑ δ ∈ incompNbhd P Λ γ₀,
      |w δ| * treeSum P w Λ δ c' ((subtreeOf A r p c).erase c') :=
    fun c' _ => Finset.sum_nonneg fun δ _ =>
      mul_nonneg (abs_nonneg _) (treeSum_nonneg P w Λ δ c' _)
  refine le_trans ?_ (Finset.single_le_sum hnn2 hcB)
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun δ => |w δ| * treeSum P w Λ δ c S)
    (fun δ _ => mul_nonneg (abs_nonneg _) (treeSum_nonneg P w Λ δ c S)) hδ)
  rw [← Finset.mul_prod_erase _ _ hcB, ← hSdef]
  exact mul_le_mul_of_nonneg_left htree (abs_nonneg _)

/-- **Die termweise Schranke**: das Gewicht einer einzelnen
Baum-Belegungs-Paarung wird vom Produkt der Blockfaktoren über der von
ihr erzeugten Partition dominiert. Das ist die multiplikative Hälfte der
scharfen Kotecký-Preiss-Schranke; offen bleibt die Abzählung der Fasern. -/
theorem tree_weight_le_prod_blocks (w : ι → ℝ) (Λ : Finset ι) (γ₀ : ι)
    {A : Finset J} {r : J} {p : J → J} {h : J → ι} (hp : p ∈ rootedTrees A r)
    (hr : r ∉ A) (hh : h ∈ pinnedTuples Λ γ₀ A)
    (hinc : TreeIncompatible P h A p) :
    ∏ v ∈ A, |w (h v)|
      ≤ ∏ B ∈ (rootChildren A r p).image (subtreeOf A r p),
          ∑ c ∈ B, ∑ δ ∈ incompNbhd P Λ γ₀,
            |w δ| * treeSum P w Λ δ c (B.erase c) := by
  rw [prod_eq_prod_blocks (subtreeOf_image_mem_partitionsOf hp hr)
    (fun v => |w (h v)|)]
  refine Finset.prod_le_prod (fun B _ => Finset.prod_nonneg fun v _ => abs_nonneg _)
    fun B hB => ?_
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hB
  exact block_weight_le P w Λ γ₀ hp hr hh hinc hc

end Polymer

end ClusterExpansion
