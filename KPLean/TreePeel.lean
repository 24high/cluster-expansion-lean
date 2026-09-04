/-
Copyright (c) 2026 Dennis Michael Heine. All rights reserved.
Released under the CC BY-NC-SA 4.0 license as described in the file LICENSE.
Authors: Dennis Michael Heine
-/
import KPLean.TreeDecomp

/-!
# Die Faserabzählung der Wurzelzerlegung

`TreeDecomp` zeigt, dass die Teilbäume unter den Kindern der Wurzel eine
Partition bilden, und führt die scharfe Schranke auf **eine** Peel-Ungleichung
zurück (`treeSum_le_sum_partitions`, dort noch als Hypothese `hpeel`). Diese
Datei beweist die Peel-Ungleichung und schließt die Schranke damit ab.

Die Summe über Wurzelbäume und Belegungen wird nach dem Tripel

* `subtreeOf A r p (rootAbove A r p a₀)` — der Block, in dem `a₀` liegt,
* `rootAbove A r p a₀` — dessen Blockwurzel,
* der Belegungswert an dieser Blockwurzel

gefasert. Für ein festes Tripel zerfällt jedes Paar `(p, h)` in **Blockdaten**
(eingeschränkte Elternabbildung `restrictParent`, eingeschränkte Belegung) und
**Restdaten** (`outerParent` auf `A \ B₀`, eingeschränkte Belegung). Diese
Zuordnung ist injektiv — aus den vier Teilen lässt sich `(p, h)` zurückgewinnen —,
das Gewicht faktorisiert, und die Zielmenge ist ein Produkt zweier
Baum-Belegungs-Mengen. Damit ist die Faser durch
`‖w δ‖ · treeSum(Block) · treeSum(Rest)` beschränkt (`fibre_sum_le`), und die
Summation über alle Tripel liefert `treeSum_le_peel`.

Hauptresultate: `treeSum_le_peel`, `treeSum_peel` und die unbedingte Fassung
`treeSum_le_sum_partitions'`.
-/

open Finset

set_option linter.style.openClassical false

open scoped Classical

namespace ClusterExpansion

variable {J : Type*} [DecidableEq J] [Fintype J]

/-! ## Der Block eines festen Knotens -/

omit [DecidableEq J] [Fintype J] in
/-- Liegt der Elternknoten in einem Teilbaum, so auch der Knoten selbst. -/
theorem mem_subtreeOf_of_parent {A : Finset J} {r : J} {p : J → J} {c v : J}
    (hv : v ∈ A) (hpv : p v ∈ subtreeOf A r p c) : v ∈ subtreeOf A r p c := by
  obtain ⟨-, k, hkc, hkr⟩ := mem_subtreeOf.mp hpv
  refine mem_subtreeOf.mpr ⟨hv, k + 1, ?_, ?_⟩
  · rw [Function.iterate_succ_apply]
    exact hkc
  · rw [Function.iterate_succ_apply]
    exact hkr

/-- Das Wurzelkind, unter dem ein fester Knoten `a₀` hängt. Außerhalb der
Wurzelbäume ist der Wert bedeutungslos. -/
noncomputable def rootAbove (A : Finset J) (r : J) (p : J → J) (a₀ : J) : J :=
  if h : ∃ c, c ∈ rootChildren A r p ∧ a₀ ∈ subtreeOf A r p c then h.choose else a₀

/-- `rootAbove` leistet, was sein Name sagt. -/
theorem rootAbove_spec {A : Finset J} {r : J} {p : J → J}
    (hp : p ∈ rootedTrees A r) {a₀ : J} (ha₀ : a₀ ∈ A) :
    rootAbove A r p a₀ ∈ rootChildren A r p ∧
      a₀ ∈ subtreeOf A r p (rootAbove A r p a₀) := by
  have h : ∃ c, c ∈ rootChildren A r p ∧ a₀ ∈ subtreeOf A r p c := by
    obtain ⟨c, hc, hmem⟩ := exists_rootChild_mem_subtreeOf hp ha₀
    exact ⟨c, hc, hmem⟩
  rw [rootAbove, dif_pos h]
  exact h.choose_spec

/-- Das Wurzelkind über `a₀` ist eindeutig. -/
theorem eq_rootAbove {A : Finset J} {r : J} {p : J → J}
    (hp : p ∈ rootedTrees A r) (hr : r ∉ A) {a₀ c : J} (ha₀ : a₀ ∈ A)
    (hc : c ∈ rootChildren A r p) (hmem : a₀ ∈ subtreeOf A r p c) :
    c = rootAbove A r p a₀ := by
  obtain ⟨-, hpr, -, -⟩ := mem_rootedTrees.mp hp
  obtain ⟨hc', hmem'⟩ := rootAbove_spec hp ha₀
  exact subtreeOf_unique hpr hr (mem_rootChildren.mp hc).1
    (mem_rootChildren.mp hc').1 hmem hmem'

/-! ## Die Elternabbildung nach dem Abtrennen eines Wurzelblocks -/

/-- Die Elternabbildung des Restbaums: außerhalb von `A \ B₀` auf die
Wurzel festgenagelt. -/
noncomputable def outerParent (A B₀ : Finset J) (r : J) (p : J → J) : J → J :=
  fun v => if v ∈ A \ B₀ then p v else r

/-- Verlässt ein Knoten den Block, so auch sein Elternknoten. -/
theorem parent_mem_sdiff {A : Finset J} {r : J} {p : J → J}
    (hp : p ∈ rootedTrees A r) {c v : J} (hv : v ∈ A \ subtreeOf A r p c) :
    p v ∈ insert r (A \ subtreeOf A r p c) := by
  obtain ⟨hpi, -, -, -⟩ := mem_rootedTrees.mp hp
  obtain ⟨hvA, hvB⟩ := Finset.mem_sdiff.mp hv
  rcases Finset.mem_insert.mp (hpi v) with hrr | hAA
  · exact Finset.mem_insert.mpr (Or.inl hrr)
  · refine Finset.mem_insert.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hAA, fun hcon => ?_⟩))
    exact hvB (mem_subtreeOf_of_parent hvA hcon)

/-- Die Iterationen des Restbaums erreichen die Wurzel, sobald es die
Iterationen von `p` tun. -/
theorem iterate_outerParent {A : Finset J} {r : J} {p : J → J}
    (hp : p ∈ rootedTrees A r) (hr : r ∉ A) {c : J} :
    ∀ (k : ℕ) (v : J), v ∈ A \ subtreeOf A r p c → p^[k] v = r →
      (outerParent A (subtreeOf A r p c) r p)^[k] v = r := by
  have hrout : outerParent A (subtreeOf A r p c) r p r = r :=
    if_neg fun hmem => hr (Finset.mem_sdiff.mp hmem).1
  intro k
  induction k with
  | zero =>
    intro v _ hkr
    exact hkr
  | succ k IH =>
    intro v hv hkr
    have hstep : outerParent A (subtreeOf A r p c) r p v = p v := if_pos hv
    rw [Function.iterate_succ_apply, hstep]
    by_cases hpv : p v ∈ A \ subtreeOf A r p c
    · exact IH (p v) hpv ((Function.iterate_succ_apply p k v).symm.trans hkr)
    · have hpvr : p v = r := by
        rcases Finset.mem_insert.mp (parent_mem_sdiff hp hv) with h | h
        · exact h
        · exact absurd h hpv
      rw [hpvr, Function.iterate_fixed hrout]

/-- **Der Restbaum ist ein Wurzelbaum**: nach dem Abtrennen des Blocks
`subtreeOf A r p c` bleibt ein Wurzelbaum über `A \ subtreeOf A r p c`. -/
theorem outerParent_mem_rootedTrees {A : Finset J} {r : J} {p : J → J}
    (hp : p ∈ rootedTrees A r) (hr : r ∉ A) {c : J} :
    outerParent A (subtreeOf A r p c) r p
      ∈ rootedTrees (A \ subtreeOf A r p c) r := by
  refine mem_rootedTrees.mpr ⟨fun v => ?_, ?_, fun v hv => ?_, fun v hv => ?_⟩
  · by_cases hvA : v ∈ A \ subtreeOf A r p c
    · rw [show outerParent A (subtreeOf A r p c) r p v = p v from if_pos hvA]
      exact parent_mem_sdiff hp hvA
    · rw [show outerParent A (subtreeOf A r p c) r p v = r from if_neg hvA]
      exact Finset.mem_insert_self r _
  · exact if_neg fun hmem => hr (Finset.mem_sdiff.mp hmem).1
  · exact if_neg fun hmem => hv (Finset.mem_insert_of_mem hmem)
  · obtain ⟨-, -, -, hreach⟩ := mem_rootedTrees.mp hp
    obtain ⟨k, hk⟩ := hreach v (Finset.mem_sdiff.mp hv).1
    exact ⟨k, iterate_outerParent hp hr k v hv hk⟩

/-! ## Die Faserabschätzung -/

section Polymer

variable {K : Type*} [RCLike K]
variable {ι : Type*} [DecidableEq ι] (P : PolymerSystem ι)

omit [DecidableEq ι] in
/-- Die Restdaten erben die Unverträglichkeit aller Kanten. -/
theorem treeIncompatible_outer {A : Finset J} {r : J} {p : J → J} {h : J → ι}
    {Λ : Finset ι} {γ₀ : ι} (hp : p ∈ rootedTrees A r) (hr : r ∉ A)
    (hh : h ∈ pinnedTuples Λ γ₀ A) (hinc : TreeIncompatible P h A p) (c : J) :
    TreeIncompatible P (restrictOn (A \ subtreeOf A r p c) γ₀ h)
      (A \ subtreeOf A r p c) (outerParent A (subtreeOf A r p c) r p) := by
  obtain ⟨-, hout⟩ := mem_pinnedTuples.mp hh
  intro v hv
  have hqv : outerParent A (subtreeOf A r p c) r p v = p v := if_pos hv
  have hgv : restrictOn (A \ subtreeOf A r p c) γ₀ h v = h v := if_pos hv
  have hgp : restrictOn (A \ subtreeOf A r p c) γ₀ h (p v) = h (p v) := by
    by_cases hpv : p v ∈ A \ subtreeOf A r p c
    · exact if_pos hpv
    · have hpvr : p v = r := by
        rcases Finset.mem_insert.mp (parent_mem_sdiff hp hv) with h1 | h1
        · exact h1
        · exact absurd h1 hpv
      rw [hpvr, hout r hr]
      exact if_neg fun hmem => hr (Finset.mem_sdiff.mp hmem).1
  rw [hqv, hgv, hgp]
  exact hinc v (Finset.mem_sdiff.mp hv).1

omit [DecidableEq ι] in
/-- Die Paarsumme über Bäume und Belegungen ist die Baumsumme. -/
theorem sum_product_eq_treeSum (w : ι → K) (Λ : Finset ι) (γ : ι) (r : J)
    (A : Finset J) :
    ∑ z ∈ rootedTrees A r ×ˢ pinnedTuples Λ γ A,
        (∏ v ∈ A, ‖w (z.2 v)‖) *
          (if TreeIncompatible P z.2 A z.1 then 1 else 0)
      = treeSum P w Λ γ r A := by
  rw [Finset.sum_product]
  rfl

omit [DecidableEq ι] in
/-- **Die Faserabschätzung**: eine Faser der Wurzelzerlegung — fester Block
`B₀` mit Blockwurzel `c` und festem Belegungswert `δ` an dieser Wurzel —
injiziert in das Produkt aus Blockdaten und Restdaten. Aus dem Paar
`(p, h)` werden der eingeschränkte Baum auf `B₀.erase c`, der Restbaum auf
`A \ B₀` und die beiden eingeschränkten Belegungen; aus diesen vier Daten
lässt sich `(p, h)` zurückgewinnen, also ist die Abbildung injektiv. -/
theorem fibre_sum_le (w : ι → K) (Λ : Finset ι) (γ₀ : ι) (r : J)
    {A : Finset J} (hr : r ∉ A) {B₀ : Finset J} {c : J} {δ : ι}
    (F : Finset ((J → J) × (J → ι)))
    (hF : ∀ x ∈ F, x.1 ∈ rootedTrees A r ∧ x.2 ∈ pinnedTuples Λ γ₀ A ∧
      TreeIncompatible P x.2 A x.1 ∧ c ∈ rootChildren A r x.1 ∧
      subtreeOf A r x.1 c = B₀ ∧ x.2 c = δ) :
    ∑ x ∈ F, ∏ v ∈ A, ‖w (x.2 v)‖
      ≤ ‖w δ‖ * (treeSum P w Λ δ c (B₀.erase c) *
          treeSum P w Λ γ₀ r (A \ B₀)) := by
  set Φ : (J → J) × (J → ι) → ((J → J) × (J → ι)) × ((J → J) × (J → ι)) :=
    fun x => ((restrictParent A r x.1 c, restrictOn (B₀.erase c) δ x.2),
      (outerParent A B₀ r x.1, restrictOn (A \ B₀) γ₀ x.2)) with hΦ
  set G : ((J → J) × (J → ι)) × ((J → J) × (J → ι)) → ℝ := fun z =>
    ‖w δ‖ * (((∏ v ∈ B₀.erase c, ‖w (z.1.2 v)‖) *
        (if TreeIncompatible P z.1.2 (B₀.erase c) z.1.1 then 1 else 0)) *
      ((∏ v ∈ A \ B₀, ‖w (z.2.2 v)‖) *
        (if TreeIncompatible P z.2.2 (A \ B₀) z.2.1 then 1 else 0))) with hG
  -- Die Bilder liegen in der Zielmenge.
  have hmaps : ∀ x ∈ F, Φ x ∈
      (rootedTrees (B₀.erase c) c ×ˢ pinnedTuples Λ δ (B₀.erase c)) ×ˢ
        (rootedTrees (A \ B₀) r ×ˢ pinnedTuples Λ γ₀ (A \ B₀)) := by
    intro x hx
    obtain ⟨hp, hh, hinc, hc, hB, -⟩ := hF x hx
    have hB₀sub : B₀ ⊆ A := hB ▸ subtreeOf_subset
    refine Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩,
      Finset.mem_product.mpr ⟨?_, ?_⟩⟩
    · have hmem := restrictParent_mem_rootedTrees hp hr hc
      rwa [hB] at hmem
    · exact restrictOn_mem_pinnedTuples_pin
        (fun j hj => hB₀sub (Finset.mem_of_mem_erase hj)) hh δ
    · have hmem := outerParent_mem_rootedTrees hp hr (c := c)
      rwa [hB] at hmem
    · exact restrictOn_mem_pinnedTuples Finset.sdiff_subset hh
  -- Die Gewichte stimmen überein.
  have hval : ∀ x ∈ F, ∏ v ∈ A, ‖w (x.2 v)‖ = G (Φ x) := by
    intro x hx
    obtain ⟨hp, hh, hinc, hc, hB, hδ⟩ := hF x hx
    have hB₀sub : B₀ ⊆ A := hB ▸ subtreeOf_subset
    have hcB₀ : c ∈ B₀ :=
      hB ▸ self_mem_subtreeOf (mem_rootChildren.mp hc).1 (mem_rootChildren.mp hc).2
    have hi1 : TreeIncompatible P (restrictOn (B₀.erase c) δ x.2) (B₀.erase c)
        (restrictParent A r x.1 c) := by
      have hthis := treeIncompatible_restrict P hp hr hinc hc
      rwa [hB, hδ] at hthis
    have hi2 : TreeIncompatible P (restrictOn (A \ B₀) γ₀ x.2) (A \ B₀)
        (outerParent A B₀ r x.1) := by
      have hthis := treeIncompatible_outer P hp hr hh hinc c
      rwa [hB] at hthis
    have e1 : ∏ v ∈ B₀.erase c, ‖w (restrictOn (B₀.erase c) δ x.2 v)‖
        = ∏ v ∈ B₀.erase c, ‖w (x.2 v)‖ :=
      Finset.prod_congr rfl fun v hv => by
        rw [show restrictOn (B₀.erase c) δ x.2 v = x.2 v from if_pos hv]
    have e2 : ∏ v ∈ A \ B₀, ‖w (restrictOn (A \ B₀) γ₀ x.2 v)‖
        = ∏ v ∈ A \ B₀, ‖w (x.2 v)‖ :=
      Finset.prod_congr rfl fun v hv => by
        rw [show restrictOn (A \ B₀) γ₀ x.2 v = x.2 v from if_pos hv]
    rw [hG, hΦ]
    simp only
    rw [if_pos hi1, if_pos hi2, mul_one, mul_one, e1, e2, ← hδ,
      ← Finset.prod_sdiff hB₀sub, ← Finset.mul_prod_erase B₀ _ hcB₀]
    ring
  -- Die Abbildung ist injektiv.
  have hinj : Set.InjOn Φ F := by
    intro x hx y hy heq
    obtain ⟨hpx, hhx, -, hcx, hBx, hδx⟩ := hF x (Finset.mem_coe.mp hx)
    obtain ⟨hpy, hhy, -, hcy, hBy, hδy⟩ := hF y (Finset.mem_coe.mp hy)
    obtain ⟨-, hprx, houtx, -⟩ := mem_rootedTrees.mp hpx
    obtain ⟨-, hpry, houty, -⟩ := mem_rootedTrees.mp hpy
    obtain ⟨-, hhoutx⟩ := mem_pinnedTuples.mp hhx
    obtain ⟨-, hhouty⟩ := mem_pinnedTuples.mp hhy
    have hq : restrictParent A r x.1 c = restrictParent A r y.1 c :=
      congrArg (fun z => z.1.1) heq
    have hg : restrictOn (B₀.erase c) δ x.2 = restrictOn (B₀.erase c) δ y.2 :=
      congrArg (fun z => z.1.2) heq
    have ho : outerParent A B₀ r x.1 = outerParent A B₀ r y.1 :=
      congrArg (fun z => z.2.1) heq
    have hk : restrictOn (A \ B₀) γ₀ x.2 = restrictOn (A \ B₀) γ₀ y.2 :=
      congrArg (fun z => z.2.2) heq
    have h1 : x.1 = y.1 := by
      funext v
      by_cases hvA : v ∈ A
      · by_cases hvB : v ∈ B₀
        · by_cases hvc : v = c
          · rw [hvc, (mem_rootChildren.mp hcx).2, (mem_rootChildren.mp hcy).2]
          · have hve : v ∈ B₀.erase c := Finset.mem_erase.mpr ⟨hvc, hvB⟩
            calc x.1 v
                = restrictParent A r x.1 c v :=
                  (if_pos (show v ∈ (subtreeOf A r x.1 c).erase c by
                    rw [hBx]; exact hve)).symm
              _ = restrictParent A r y.1 c v := by rw [hq]
              _ = y.1 v := if_pos (show v ∈ (subtreeOf A r y.1 c).erase c by
                    rw [hBy]; exact hve)
        · have hvd : v ∈ A \ B₀ := Finset.mem_sdiff.mpr ⟨hvA, hvB⟩
          calc x.1 v = outerParent A B₀ r x.1 v := (if_pos hvd).symm
            _ = outerParent A B₀ r y.1 v := by rw [ho]
            _ = y.1 v := if_pos hvd
      · by_cases hvr : v = r
        · rw [hvr, hprx, hpry]
        · have hvi : v ∉ insert r A := fun hmem => by
            rcases Finset.mem_insert.mp hmem with h | h
            · exact hvr h
            · exact hvA h
          rw [houtx v hvi, houty v hvi]
    have h2 : x.2 = y.2 := by
      funext v
      by_cases hvA : v ∈ A
      · by_cases hvB : v ∈ B₀
        · by_cases hvc : v = c
          · rw [hvc, hδx, hδy]
          · have hve : v ∈ B₀.erase c := Finset.mem_erase.mpr ⟨hvc, hvB⟩
            calc x.2 v = restrictOn (B₀.erase c) δ x.2 v := (if_pos hve).symm
              _ = restrictOn (B₀.erase c) δ y.2 v := by rw [hg]
              _ = y.2 v := if_pos hve
        · have hvd : v ∈ A \ B₀ := Finset.mem_sdiff.mpr ⟨hvA, hvB⟩
          calc x.2 v = restrictOn (A \ B₀) γ₀ x.2 v := (if_pos hvd).symm
            _ = restrictOn (A \ B₀) γ₀ y.2 v := by rw [hk]
            _ = y.2 v := if_pos hvd
      · rw [hhoutx v hvA, hhouty v hvA]
    exact Prod.ext h1 h2
  -- Nichtnegativität auf der Zielmenge.
  have hGnn : ∀ z, 0 ≤ G z := by
    intro z
    rw [hG]
    refine mul_nonneg (norm_nonneg _) (mul_nonneg ?_ ?_) <;>
      refine mul_nonneg (Finset.prod_nonneg fun v _ => norm_nonneg _) ?_ <;>
      · split <;> norm_num
  calc ∑ x ∈ F, ∏ v ∈ A, ‖w (x.2 v)‖
      = ∑ x ∈ F, G (Φ x) := Finset.sum_congr rfl hval
    _ = ∑ z ∈ F.image Φ, G z := (Finset.sum_image hinj).symm
    _ ≤ ∑ z ∈ (rootedTrees (B₀.erase c) c ×ˢ pinnedTuples Λ δ (B₀.erase c)) ×ˢ
          (rootedTrees (A \ B₀) r ×ˢ pinnedTuples Λ γ₀ (A \ B₀)), G z :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.image_subset_iff.mpr hmaps) (fun z _ _ => hGnn z)
    _ = ‖w δ‖ * (treeSum P w Λ δ c (B₀.erase c) *
          treeSum P w Λ γ₀ r (A \ B₀)) := by
        rw [hG]
        simp only
        rw [← Finset.mul_sum, Finset.sum_product]
        dsimp only
        rw [← sum_product_eq_treeSum P w Λ δ c (B₀.erase c),
          ← sum_product_eq_treeSum P w Λ γ₀ r (A \ B₀), Finset.sum_mul_sum]

/-! ## Das Abschäl-Lemma -/

omit [DecidableEq ι] in
/-- **Das Abschäl-Lemma**: schält man den Block ab, in dem ein fester
Knoten `a₀` liegt, so wird die Baumsumme vom Produkt aus Blockfaktor und
Baumsumme des Restes dominiert. Die Summe über die Wurzelbäume wird nach
dem Tripel (Block von `a₀`, Blockwurzel, Belegungswert dort) gefasert;
jede Faser wird von `fibre_sum_le` abgeschätzt. -/
theorem treeSum_le_peel (w : ι → K) (Λ : Finset ι) (γ₀ : ι) (r : J)
    {A : Finset J} (hr : r ∉ A) {a₀ : J} (ha₀ : a₀ ∈ A) :
    treeSum P w Λ γ₀ r A
      ≤ ∑ B₀ ∈ A.powerset.filter (fun B => a₀ ∈ B),
          blockFactor P w Λ γ₀ B₀ * treeSum P w Λ γ₀ r (A \ B₀) := by
  -- Nur die verträglichkeitstreuen Paare tragen bei.
  have h1 : ∀ x ∈ rootedTrees A r ×ˢ pinnedTuples Λ γ₀ A,
      (∏ v ∈ A, ‖w (x.2 v)‖) *
        (if TreeIncompatible P x.2 A x.1 then 1 else 0) ≠ 0 →
      TreeIncompatible P x.2 A x.1 := by
    intro x _ hne
    by_contra hcon
    exact hne (by rw [if_neg hcon, mul_zero])
  have hstart : treeSum P w Λ γ₀ r A
      = ∑ x ∈ (rootedTrees A r ×ˢ pinnedTuples Λ γ₀ A).filter
          (fun x => TreeIncompatible P x.2 A x.1), ∏ v ∈ A, ‖w (x.2 v)‖ := by
    rw [← sum_product_eq_treeSum P w Λ γ₀ r A, ← Finset.sum_filter_of_ne h1]
    exact Finset.sum_congr rfl fun x hx => by
      rw [if_pos (Finset.mem_filter.mp hx).2, mul_one]
  -- Das Faserungstripel.
  have hmaps : ∀ x ∈ (rootedTrees A r ×ˢ pinnedTuples Λ γ₀ A).filter
      (fun x => TreeIncompatible P x.2 A x.1),
      (subtreeOf A r x.1 (rootAbove A r x.1 a₀), rootAbove A r x.1 a₀,
          x.2 (rootAbove A r x.1 a₀))
        ∈ (A.powerset.filter (fun B => a₀ ∈ B)) ×ˢ A ×ˢ incompNbhd P Λ γ₀ := by
    intro x hx
    obtain ⟨hmem, hinc⟩ := Finset.mem_filter.mp hx
    obtain ⟨hp, hh⟩ := Finset.mem_product.mp hmem
    obtain ⟨hc, hsub⟩ := rootAbove_spec hp ha₀
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr subtreeOf_subset, hsub⟩,
      Finset.mem_product.mpr ⟨(mem_rootChildren.mp hc).1,
        val_rootChild_mem_incompNbhd P hr hh hinc hc⟩⟩
  -- Die rechte Seite als Summe über dasselbe Tripel.
  have hRHS : ∀ B₀ ∈ A.powerset.filter (fun B => a₀ ∈ B),
      ∑ y ∈ A ×ˢ incompNbhd P Λ γ₀,
          (if y.1 ∈ B₀ then ‖w y.2‖ *
            (treeSum P w Λ y.2 y.1 (B₀.erase y.1) *
              treeSum P w Λ γ₀ r (A \ B₀)) else 0)
        = blockFactor P w Λ γ₀ B₀ * treeSum P w Λ γ₀ r (A \ B₀) := by
    intro B₀ hB₀
    have hB₀sub : B₀ ⊆ A := Finset.mem_powerset.mp (Finset.mem_filter.mp hB₀).1
    have hfilt : A.filter (fun c => c ∈ B₀) = B₀ := by
      ext c
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hB₀sub h, h⟩⟩
    calc ∑ y ∈ A ×ˢ incompNbhd P Λ γ₀,
          (if y.1 ∈ B₀ then ‖w y.2‖ *
            (treeSum P w Λ y.2 y.1 (B₀.erase y.1) *
              treeSum P w Λ γ₀ r (A \ B₀)) else 0)
        = ∑ c ∈ A, ∑ δ ∈ incompNbhd P Λ γ₀,
            (if c ∈ B₀ then ‖w δ‖ * (treeSum P w Λ δ c (B₀.erase c) *
              treeSum P w Λ γ₀ r (A \ B₀)) else 0) := by
          rw [Finset.sum_product]
      _ = ∑ c ∈ A, (if c ∈ B₀ then ∑ δ ∈ incompNbhd P Λ γ₀,
            ‖w δ‖ * (treeSum P w Λ δ c (B₀.erase c) *
              treeSum P w Λ γ₀ r (A \ B₀)) else 0) :=
          Finset.sum_congr rfl fun c _ => by by_cases hc : c ∈ B₀ <;> simp [hc]
      _ = ∑ c ∈ B₀, ∑ δ ∈ incompNbhd P Λ γ₀,
            ‖w δ‖ * (treeSum P w Λ δ c (B₀.erase c) *
              treeSum P w Λ γ₀ r (A \ B₀)) := by
          rw [← Finset.sum_filter, hfilt]
      _ = blockFactor P w Λ γ₀ B₀ * treeSum P w Λ γ₀ r (A \ B₀) := by
          unfold blockFactor
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun c _ => by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun δ _ => (mul_assoc _ _ _).symm
  rw [hstart, ← Finset.sum_fiberwise_of_maps_to hmaps
    (fun x => ∏ v ∈ A, ‖w (x.2 v)‖), Finset.sum_product]
  refine Finset.sum_le_sum fun B₀ hB₀ => ?_
  rw [← hRHS B₀ hB₀]
  refine Finset.sum_le_sum fun y _ => ?_
  by_cases hcB : y.1 ∈ B₀
  · rw [if_pos hcB]
    refine fibre_sum_le P w Λ γ₀ r hr _ ?_
    intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    obtain ⟨hmem, hinc⟩ := Finset.mem_filter.mp hx1
    obtain ⟨hp, hh⟩ := Finset.mem_product.mp hmem
    have e1 : subtreeOf A r x.1 (rootAbove A r x.1 a₀) = B₀ :=
      congrArg (fun z => z.1) hx2
    have e2 : rootAbove A r x.1 a₀ = y.1 := congrArg (fun z => z.2.1) hx2
    have e3 : x.2 (rootAbove A r x.1 a₀) = y.2 := congrArg (fun z => z.2.2) hx2
    obtain ⟨hc, -⟩ := rootAbove_spec hp ha₀
    rw [e2] at hc e1 e3
    exact ⟨hp, hh, hinc, hc, e1, e3⟩
  · rw [if_neg hcB]
    refine le_of_eq (Finset.sum_eq_zero fun x hx => ?_)
    exfalso
    apply hcB
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    obtain ⟨hmem, -⟩ := Finset.mem_filter.mp hx1
    obtain ⟨hp, -⟩ := Finset.mem_product.mp hmem
    have e1 : subtreeOf A r x.1 (rootAbove A r x.1 a₀) = B₀ :=
      congrArg (fun z => z.1) hx2
    have e2 : rootAbove A r x.1 a₀ = y.1 := congrArg (fun z => z.2.1) hx2
    obtain ⟨hc, -⟩ := rootAbove_spec hp ha₀
    have hmemB := self_mem_subtreeOf (mem_rootChildren.mp hc).1
      (mem_rootChildren.mp hc).2
    rw [e1, e2] at hmemB
    exact hmemB

/-! ## Die scharfe Wurzelzerlegungsschranke -/

omit [DecidableEq ι] in
/-- Das Abschäl-Lemma in genau der Form, die
`treeSum_le_sum_partitions` als Hypothese `hpeel` verlangt. -/
theorem treeSum_peel (w : ι → K) (Λ : Finset ι) (γ₀ : ι) :
    ∀ (r : J) (A : Finset J), r ∉ A → ∀ a₀ ∈ A,
      treeSum P w Λ γ₀ r A
        ≤ ∑ B₀ ∈ A.powerset.filter (fun B => a₀ ∈ B),
            blockFactor P w Λ γ₀ B₀ * treeSum P w Λ γ₀ r (A \ B₀) :=
  fun r _ hr _ ha₀ => treeSum_le_peel P w Λ γ₀ r hr ha₀

omit [DecidableEq ι] in
/-- **Die scharfe Wurzelzerlegungsschranke ohne Zusatzannahme**: die
Baumsumme über `A` wird von der Summe über alle Partitionen von `A` der
Produkte der Blockfaktoren dominiert. Das Abschäl-Lemma entlastet die
Hypothese von `treeSum_le_sum_partitions`. -/
theorem treeSum_le_sum_partitions' (w : ι → K) (Λ : Finset ι) (γ₀ : ι) (r : J)
    {A : Finset J} (hr : r ∉ A) :
    treeSum P w Λ γ₀ r A
      ≤ ∑ C ∈ partitionsOf A, ∏ B ∈ C, blockFactor P w Λ γ₀ B :=
  treeSum_le_sum_partitions P w Λ γ₀ (treeSum_peel P w Λ γ₀) r hr

end Polymer

end ClusterExpansion
