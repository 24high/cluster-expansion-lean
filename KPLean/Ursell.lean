/-
Copyright (c) 2026 Dennis Michael Heine. All rights reserved.
Released under the CC BY-NC-SA 4.0 license as described in the file LICENSE.
Authors: Dennis Michael Heine
-/
import KPLean.ClusterExpansion
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Finset.Interval

/-!
# Ursell-Funktionen und die Penrose-Baumgraphen-Schranke

Erster Baustein der Ursell-Reihe (Cluster-Reihe) von `log Z`: die
Ursell-Funktion eines Polymer-Tupels als alternierende Summe über
zusammenhängende aufspannende Teilgraphen des Unverträglichkeitsgraphen,
und die **Baumgraphen-Schranke** — der Betrag der Ursell-Summe ist durch
die Anzahl der aufspannenden Bäume im Träger beschränkt.

Beweis über das **Penrose-Partitionsschema**: jedem zusammenhängenden
aufspannenden Teilgraphen `G` wird über BFS-Schichten von einer festen
Wurzel aus ein aufspannender Baum `penroseTree G` zugeordnet (jeder
Knoten hängt am kleinsten Nachbarn der darunterliegenden Schicht).
Die Faser über einem Baum `T` ist ein Mengenintervall
`[T, penroseExt H T]`; auf einem nichttrivialen Intervall verschwindet
die alternierende Summe, also überleben höchstens die Fixpunkte des
Schemas — und davon gibt es höchstens so viele wie aufspannende Bäume.

Hauptresultate:

* `abs_ursellSum_le_treeCount`: `|∑_{G ⊆ H zusammenhängend} (-1)^{|G|}|
  ≤ #{aufspannende Bäume in H}`;
* `ursellInt`, `abs_ursellInt_le_treeCount`: dieselbe Schranke für die
  Ursell-Funktion eines Polymer-Tupels im Sinne der Cluster-Entwicklung.

Kein `sorry` in dieser Datei. Bewusst offen (nur genannt, nichts
Unbewiesenes behauptet): die Exponentialformel und die Konvergenz der
Cluster-Reihe von `log Z` unter der Kotecký-Preiss-Bedingung.

Referenzen: Penrose, *Convergence of fugacity expansions for classical
systems* (1967); Friedli–Velenik, Kap. 5; Scott–Sokal (J. Stat.
Phys. 118, 2005), §2.2.
-/

open Finset

-- Zusammenhang (`EdgeConn`) und die Penrose-Zulässigkeit sind Prädikate,
-- über die wir nur summieren, nie rechnen: bewusst klassisch.
set_option linter.style.openClassical false

open scoped Classical

namespace ClusterExpansion

/-! ## Graphen aus endlichen Kantenmengen -/

section EdgeSets

variable {V : Type*}

/-- Der von einer endlichen Kantenmenge erzeugte einfache Graph
(Diagonalkanten werden ignoriert). -/
def graphOf (G : Finset (Sym2 V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet ↑G

theorem graphOf_adj {G : Finset (Sym2 V)} {u v : V} :
    (graphOf G).Adj u v ↔ s(u, v) ∈ G ∧ u ≠ v := by
  simp [graphOf, SimpleGraph.fromEdgeSet_adj]

theorem graphOf_mono {G₁ G₂ : Finset (Sym2 V)} (h : G₁ ⊆ G₂) :
    graphOf G₁ ≤ graphOf G₂ :=
  SimpleGraph.fromEdgeSet_mono (Finset.coe_subset.mpr h)

/-- Zusammenhang einer Kantenmenge: der erzeugte Graph ist (aufspannend)
zusammenhängend auf ganz `V`. -/
def EdgeConn (G : Finset (Sym2 V)) : Prop :=
  (graphOf G).Connected

theorem EdgeConn.mono {G₁ G₂ : Finset (Sym2 V)} (h : G₁ ⊆ G₂)
    (hc : EdgeConn G₁) : EdgeConn G₂ :=
  SimpleGraph.Connected.mono (graphOf_mono h) hc

/-- Kantenmenge des erzeugten Graphen: bei diagonalfreiem `G` genau `G`. -/
theorem edgeSet_graphOf {G : Finset (Sym2 V)} (hG : ∀ e ∈ G, ¬ e.IsDiag) :
    (graphOf G).edgeSet = ↑G := by
  rw [graphOf, SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  simp only [Set.mem_sdiff, Finset.mem_coe, Sym2.mem_diagSet, and_iff_left_iff_imp]
  exact fun he => hG e he

/-- Die Ursell-Summe über der Trägerkantenmenge `H`: alternierende Summe
über alle zusammenhängenden aufspannenden Teilgraphen. -/
noncomputable def ursellSum [Fintype V] (H : Finset (Sym2 V)) : ℤ :=
  ∑ G ∈ H.powerset.filter EdgeConn, (-1 : ℤ) ^ G.card

/-- Anzahl der aufspannenden Bäume innerhalb der Trägerkantenmenge `H`. -/
noncomputable def treeCount [Fintype V] (H : Finset (Sym2 V)) : ℕ :=
  (H.powerset.filter (fun T => (graphOf T).IsTree)).card

end EdgeSets

/-! ## Das Intervall-Lemma

Auf einem nichttrivialen Mengenintervall `[A, B]` verschwindet die
alternierende Summe `∑ (-1)^{|S|}` — der kombinatorische Kern jedes
Partitionsschemas. -/

theorem sum_Icc_neg_one_pow {α : Type*} [DecidableEq α] {A B : Finset α}
    (hAB : A ⊆ B) (hne : A ≠ B) :
    ∑ S ∈ Finset.Icc A B, (-1 : ℤ) ^ S.card = 0 := by
  have h1 : ∑ S ∈ Finset.Icc A B, (-1 : ℤ) ^ S.card
      = ∑ T ∈ (B \ A).powerset, (-1 : ℤ) ^ (A ∪ T).card := by
    refine Finset.sum_nbij' (fun S => S \ A) (fun T => A ∪ T) ?_ ?_ ?_ ?_ ?_
    · intro S hS
      rw [Finset.mem_Icc] at hS
      exact Finset.mem_powerset.mpr (Finset.sdiff_subset_sdiff hS.2 Finset.Subset.rfl)
    · intro T hT
      rw [Finset.mem_powerset] at hT
      rw [Finset.mem_Icc]
      exact ⟨Finset.subset_union_left,
        Finset.union_subset hAB (hT.trans Finset.sdiff_subset)⟩
    · intro S hS
      rw [Finset.mem_Icc] at hS
      exact Finset.union_sdiff_of_subset hS.1
    · intro T hT
      rw [Finset.mem_powerset] at hT
      exact Finset.union_sdiff_cancel_left
        (Finset.disjoint_left.mpr fun a haA haT =>
          (Finset.mem_sdiff.mp (hT haT)).2 haA)
    · intro S hS
      rw [Finset.mem_Icc] at hS
      rw [Finset.union_sdiff_of_subset hS.1]
  have h2 : ∀ T ∈ (B \ A).powerset,
      (-1 : ℤ) ^ (A ∪ T).card = (-1 : ℤ) ^ A.card * (-1 : ℤ) ^ T.card := by
    intro T hT
    rw [Finset.mem_powerset] at hT
    rw [Finset.card_union_of_disjoint, pow_add]
    exact Finset.disjoint_left.mpr fun a haA haT =>
      (Finset.mem_sdiff.mp (hT haT)).2 haA
  rw [h1, Finset.sum_congr rfl h2, ← Finset.mul_sum,
    Finset.sum_powerset_neg_one_pow_card_of_nonempty
      (Finset.sdiff_nonempty.mpr fun h => hne (Finset.Subset.antisymm hAB h)),
    mul_zero]

/-! ## BFS-Schichten und der Penrose-Elternknoten

Fest gewählte Wurzel: das kleinste Element von `V`. `lvl G v` ist der
Graphabstand von der Wurzel, `par G v` der kleinste Nachbar von `v` in
der darunterliegenden Schicht — der Elternknoten des Penrose-Baums. -/

section Penrose

variable {V : Type*} [Fintype V] [LinearOrder V] [Nonempty V]

/-- Die Wurzel: das kleinste Element von `V`. -/
def root (V : Type*) [Fintype V] [LinearOrder V] [Nonempty V] : V :=
  Finset.univ.min' Finset.univ_nonempty

/-- BFS-Schicht: Graphabstand von der Wurzel im Graphen von `G`. -/
noncomputable def lvl (G : Finset (Sym2 V)) (v : V) : ℕ :=
  (graphOf G).dist (root V) v

theorem lvl_root (G : Finset (Sym2 V)) : lvl G (root V) = 0 :=
  SimpleGraph.dist_self

/-- Die Nachbarn von `v` in der darunterliegenden BFS-Schicht. -/
noncomputable def parentSet (G : Finset (Sym2 V)) (v : V) : Finset V :=
  Finset.univ.filter (fun u => (graphOf G).Adj u v ∧ lvl G u + 1 = lvl G v)

/-- Der Penrose-Elternknoten: kleinster Nachbar in der darunterliegenden
Schicht (Müllwert `root V`, falls es keinen gibt). -/
noncomputable def par (G : Finset (Sym2 V)) (v : V) : V :=
  if h : (parentSet G v).Nonempty then (parentSet G v).min' h else root V

/-- In einem zusammenhängenden Graphen hat jeder Knoten außer der Wurzel
einen Nachbarn in der darunterliegenden Schicht. -/
theorem parentSet_nonempty {G : Finset (Sym2 V)} (hG : EdgeConn G) {v : V}
    (hv : v ≠ root V) : (parentSet G v).Nonempty := by
  have hd : 0 < lvl G v := hG.pos_dist_of_ne (Ne.symm hv)
  obtain ⟨p, hp⟩ := ((hG.preconnected (root V) v).symm).exists_walk_length_eq_dist
  cases p with
  | nil => exact absurd rfl hv
  | @cons _ u _ hadj q =>
    refine ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ u, hadj.symm, ?_⟩⟩
    have h1 : (graphOf G).dist (root V) u ≤ q.length :=
      SimpleGraph.dist_le q.reverse |>.trans (by rw [SimpleGraph.Walk.length_reverse])
    have h2 : (graphOf G).dist v (root V) = q.length + 1 := by
      simpa [SimpleGraph.Walk.length_cons] using hp.symm
    have h3 : lvl G v ≤ lvl G u + 1 := by
      have htri : (graphOf G).dist (root V) v
          ≤ (graphOf G).dist (root V) u + (graphOf G).dist u v :=
        hG.dist_triangle
      have hd1 : (graphOf G).dist u v ≤ 1 :=
        (SimpleGraph.dist_eq_one_iff_adj.mpr hadj.symm).le
      unfold lvl
      omega
    have h4 : lvl G v = q.length + 1 := by
      unfold lvl
      rw [SimpleGraph.dist_comm]
      exact h2
    unfold lvl at h3 ⊢
    unfold lvl at h4
    omega

/-- Spezifikation des Penrose-Elternknotens: Nachbar eine Schicht tiefer. -/
theorem par_spec {G : Finset (Sym2 V)} (hG : EdgeConn G) {v : V}
    (hv : v ≠ root V) :
    (graphOf G).Adj (par G v) v ∧ lvl G (par G v) + 1 = lvl G v := by
  have hne := parentSet_nonempty hG hv
  have hmem : par G v ∈ parentSet G v := by
    rw [par, dif_pos hne]
    exact Finset.min'_mem _ hne
  exact (Finset.mem_filter.mp hmem).2

/-- Minimalität des Penrose-Elternknotens. -/
theorem par_min {G : Finset (Sym2 V)} (hG : EdgeConn G) {v : V}
    (hv : v ≠ root V) {u : V} (hu : u ∈ parentSet G v) : par G v ≤ u := by
  have hne := parentSet_nonempty hG hv
  rw [par, dif_pos hne]
  exact Finset.min'_le _ u hu

theorem par_ne {G : Finset (Sym2 V)} (hG : EdgeConn G) {v : V}
    (hv : v ≠ root V) : par G v ≠ v := by
  have h := (par_spec hG hv).2
  intro he
  rw [he] at h
  omega

/-! ## Der Penrose-Baum -/

/-- Der Penrose-Baum eines zusammenhängenden Graphen: jeder Knoten außer
der Wurzel hängt an seinem Penrose-Elternknoten. -/
noncomputable def penroseTree (G : Finset (Sym2 V)) : Finset (Sym2 V) :=
  (Finset.univ.erase (root V)).image (fun v => s(v, par G v))

theorem mem_penroseTree_of_ne {G : Finset (Sym2 V)} {v : V} (hv : v ≠ root V) :
    s(v, par G v) ∈ penroseTree G :=
  Finset.mem_image_of_mem _ (Finset.mem_erase.mpr ⟨hv, Finset.mem_univ v⟩)

theorem penroseTree_subset {G : Finset (Sym2 V)} (hG : EdgeConn G) :
    penroseTree G ⊆ G := by
  intro e he
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp he
  have hv' : v ≠ root V := (Finset.mem_erase.mp hv).1
  have hmem := (graphOf_adj.mp (par_spec hG hv').1).1
  rwa [Sym2.eq_swap]

theorem penroseTree_not_isDiag {G : Finset (Sym2 V)} (hG : EdgeConn G) :
    ∀ e ∈ penroseTree G, ¬ e.IsDiag := by
  intro e he
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp he
  have hv' : v ≠ root V := (Finset.mem_erase.mp hv).1
  rw [Sym2.mk_isDiag_iff]
  exact fun h => par_ne hG hv' h.symm

theorem penroseTree_adj {G : Finset (Sym2 V)} (hG : EdgeConn G) {v : V}
    (hv : v ≠ root V) : (graphOf (penroseTree G)).Adj v (par G v) :=
  graphOf_adj.mpr ⟨mem_penroseTree_of_ne hv, (par_ne hG hv).symm⟩

/-- Der Penrose-Baum ist zusammenhängend: jeder Knoten erreicht die
Wurzel durch Abstieg entlang der Elternkanten. -/
theorem penroseTree_conn {G : Finset (Sym2 V)} (hG : EdgeConn G) :
    EdgeConn (penroseTree G) := by
  have key : ∀ n : ℕ, ∀ v : V, lvl G v = n →
      (graphOf (penroseTree G)).Reachable v (root V) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro v hval
      by_cases hv : v = root V
      · subst hv
        exact SimpleGraph.Reachable.refl _
      · have hspec := par_spec hG hv
        have hadj := penroseTree_adj hG hv
        exact hadj.reachable.trans
          (ih (lvl G (par G v)) (by omega) (par G v) rfl)
  exact SimpleGraph.Connected.mk fun u v => (key _ u rfl).trans (key _ v rfl).symm

/-- Der Penrose-Baum erhält die BFS-Schichten des Ausgangsgraphen. -/
theorem lvl_penroseTree {G : Finset (Sym2 V)} (hG : EdgeConn G) (v : V) :
    lvl (penroseTree G) v = lvl G v := by
  have hle : lvl G v ≤ lvl (penroseTree G) v :=
    SimpleGraph.Reachable.dist_anti (graphOf_mono (penroseTree_subset hG))
      ((penroseTree_conn hG).preconnected _ _)
  have hge : ∀ n : ℕ, ∀ v : V, lvl G v = n → lvl (penroseTree G) v ≤ n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro v hval
      by_cases hv : v = root V
      · subst hv
        rw [lvl_root]
        omega
      · have hspec := par_spec hG hv
        have hadj := penroseTree_adj hG hv
        have h1 : lvl (penroseTree G) v ≤ lvl (penroseTree G) (par G v) + 1 := by
          have htri : (graphOf (penroseTree G)).dist (root V) v
              ≤ (graphOf (penroseTree G)).dist (root V) (par G v)
                + (graphOf (penroseTree G)).dist (par G v) v :=
            (penroseTree_conn hG).dist_triangle
          have hd1 : (graphOf (penroseTree G)).dist (par G v) v ≤ 1 :=
            (SimpleGraph.dist_eq_one_iff_adj.mpr hadj.symm).le
          unfold lvl
          omega
        have h2 := ih (lvl G (par G v)) (by omega) (par G v) rfl
        omega
  exact le_antisymm (hge _ v rfl) hle

/-- Im Penrose-Baum ist der einzige Nachbar eine Schicht tiefer der
Penrose-Elternknoten des Ausgangsgraphen. -/
theorem parentSet_penroseTree {G : Finset (Sym2 V)} (hG : EdgeConn G) {v : V}
    (hv : v ≠ root V) : parentSet (penroseTree G) v = {par G v} := by
  have hspec := par_spec hG hv
  ext u
  simp only [parentSet, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hadj, hlvl⟩
    have hmem := (graphOf_adj.mp hadj).1
    obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp hmem
    have hw' : w ≠ root V := (Finset.mem_erase.mp hw).1
    have hwspec := par_spec hG hw'
    rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exfalso
      rw [h1] at h2
      have hlv := hwspec.2
      rw [h1, h2] at hlv
      rw [lvl_penroseTree hG, lvl_penroseTree hG] at hlvl
      omega
    · rw [← h2, h1]
  · rintro rfl
    refine ⟨(penroseTree_adj hG hv).symm, ?_⟩
    rw [lvl_penroseTree hG, lvl_penroseTree hG]
    exact hspec.2

/-- Berechnung von `par` aus einer einelementigen Elternmenge. -/
theorem par_eq_of_parentSet_eq {G : Finset (Sym2 V)} {v u : V}
    (h : parentSet G v = {u}) : par G v = u := by
  unfold par
  rw [h, dif_pos (Finset.singleton_nonempty _)]
  exact Finset.min'_singleton _

theorem par_penroseTree {G : Finset (Sym2 V)} (hG : EdgeConn G) {v : V}
    (hv : v ≠ root V) : par (penroseTree G) v = par G v :=
  par_eq_of_parentSet_eq (parentSet_penroseTree hG hv)

/-- Berechnung von `par` aus Element und Minimalität. -/
theorem par_eq_of_mem_of_min {G : Finset (Sym2 V)} {v u : V}
    (hmem : u ∈ parentSet G v) (hmin : ∀ w ∈ parentSet G v, u ≤ w) :
    par G v = u := by
  have hne : (parentSet G v).Nonempty := ⟨u, hmem⟩
  unfold par
  rw [dif_pos hne]
  exact le_antisymm (Finset.min'_le _ _ hmem) (Finset.le_min' _ _ _ hmin)

/-- Der Penrose-Baum hat genau `|V| - 1` Kanten. -/
theorem penroseTree_card {G : Finset (Sym2 V)} (hG : EdgeConn G) :
    (penroseTree G).card + 1 = Fintype.card V := by
  have hinj : Set.InjOn (fun v => s(v, par G v)) ↑(Finset.univ.erase (root V)) := by
    intro a ha b hb hab
    simp only [Finset.coe_erase, Set.mem_sdiff, Set.mem_singleton_iff,
      Finset.coe_univ, Set.mem_univ, true_and] at ha hb
    rcases Sym2.eq_iff.mp hab with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact h1
    · have hsa := (par_spec hG ha).2
      have hsb := (par_spec hG hb).2
      rw [h2] at hsa
      rw [← h1] at hsb
      omega
  rw [penroseTree, Finset.card_image_of_injOn hinj,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  have := Fintype.card_pos (α := V)
  omega

/-- Der Penrose-Baum ist ein aufspannender Baum. -/
theorem penroseTree_isTree {G : Finset (Sym2 V)} (hG : EdgeConn G) :
    (graphOf (penroseTree G)).IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨penroseTree_conn hG, ?_⟩
  rw [edgeSet_graphOf (penroseTree_not_isDiag hG), Nat.card_coe_set_eq,
    Set.ncard_coe_finset, Nat.card_eq_fintype_card]
  exact penroseTree_card hG

/-! ## Das Penrose-Intervall -/

/-- Zulässigkeit eines Kantenpaars relativ zum Baum `T`: gleiche Schicht,
oder vertikal mit unterem Endpunkt nicht unterhalb des Penrose-Elternknotens. -/
def allowedPair (T : Finset (Sym2 V)) (u v : V) : Prop :=
  lvl T u = lvl T v
    ∨ (lvl T u + 1 = lvl T v ∧ par T v ≤ u)
    ∨ (lvl T v + 1 = lvl T u ∧ par T u ≤ v)

theorem allowedPair_symm {T : Finset (Sym2 V)} {u v : V} :
    allowedPair T u v ↔ allowedPair T v u := by
  unfold allowedPair
  tauto

/-- Das obere Ende des Penrose-Intervalls über `T`: alle relativ zu `T`
zulässigen Kanten des Trägers `H`. -/
noncomputable def penroseExt (H T : Finset (Sym2 V)) : Finset (Sym2 V) :=
  H.filter (fun e => ¬ e.IsDiag ∧ ∀ u v, e = s(u, v) → allowedPair T u v)

theorem penroseExt_subset {H T : Finset (Sym2 V)} : penroseExt H T ⊆ H :=
  Finset.filter_subset _ _

theorem mem_penroseExt {H T : Finset (Sym2 V)} {u v : V} :
    s(u, v) ∈ penroseExt H T ↔ s(u, v) ∈ H ∧ u ≠ v ∧ allowedPair T u v := by
  simp only [penroseExt, Finset.mem_filter, Sym2.mk_isDiag_iff]
  constructor
  · rintro ⟨hH, hdiag, hall⟩
    exact ⟨hH, hdiag, hall u v rfl⟩
  · rintro ⟨hH, hne, hallow⟩
    refine ⟨hH, hne, fun a b hab => ?_⟩
    rcases Sym2.eq_iff.mp hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]
      exact hallow
    · rw [← h1, ← h2]
      exact allowedPair_symm.mp hallow

/-- Vorwärtsrichtung des Penrose-Schemas: jeder zusammenhängende
aufspannende Teilgraph liegt im Intervall seines Penrose-Baums. -/
theorem penrose_forward {H G : Finset (Sym2 V)} (hH : ∀ e ∈ H, ¬ e.IsDiag)
    (hGH : G ⊆ H) (hG : EdgeConn G) :
    penroseTree G ⊆ G ∧ G ⊆ penroseExt H (penroseTree G) := by
  refine ⟨penroseTree_subset hG, fun e he => ?_⟩
  induction e using Sym2.ind with
  | _ u v =>
    have hne : u ≠ v := fun h => hH _ (hGH he) (Sym2.mk_isDiag_iff.mpr h)
    have hadj : (graphOf G).Adj u v := graphOf_adj.mpr ⟨he, hne⟩
    rw [mem_penroseExt]
    refine ⟨hGH he, hne, ?_⟩
    have hlvlT : ∀ x, lvl (penroseTree G) x = lvl G x := lvl_penroseTree hG
    have htri := hadj.diff_dist_adj (u := root V)
    unfold allowedPair
    rcases htri with h | h | h
    · left
      simp only [hlvlT]
      unfold lvl
      omega
    · right; left
      have hvroot : v ≠ root V := by
        intro hv
        rw [hv, SimpleGraph.dist_self] at h
        omega
      have humem : u ∈ parentSet G v :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj, by unfold lvl; omega⟩
      refine ⟨by simp only [hlvlT]; unfold lvl; omega, ?_⟩
      rw [par_penroseTree hG hvroot]
      exact par_min hG hvroot humem
    · by_cases hu0 : (graphOf G).dist (root V) u = 0
      · left
        simp only [hlvlT]
        unfold lvl
        omega
      · right; right
        have huroot : u ≠ root V := by
          intro hu
          rw [hu] at hu0
          exact hu0 SimpleGraph.dist_self
        have hvmem : v ∈ parentSet G u :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj.symm, by unfold lvl; omega⟩
        refine ⟨by simp only [hlvlT]; unfold lvl; omega, ?_⟩
        rw [par_penroseTree hG huroot]
        exact par_min hG huroot hvmem

/-- Rückwärtsrichtung des Penrose-Schemas: jedes Element des Intervalls
`[penroseTree G₀, penroseExt H (penroseTree G₀)]` ist zusammenhängend und
hat denselben Penrose-Baum wie `G₀`. -/
theorem penrose_backward {H G₀ G : Finset (Sym2 V)} (hG₀ : EdgeConn G₀)
    (hTG : penroseTree G₀ ⊆ G) (hGE : G ⊆ penroseExt H (penroseTree G₀)) :
    EdgeConn G ∧ penroseTree G = penroseTree G₀ := by
  have hconnT : EdgeConn (penroseTree G₀) := penroseTree_conn hG₀
  have hconnG : EdgeConn G := hconnT.mono hTG
  refine ⟨hconnG, ?_⟩
  -- Schritt 1: Jede Kante von `G` springt in den `T`-Schichten um höchstens 1.
  have hstep : ∀ u v : V, (graphOf G).Adj u v →
      lvl (penroseTree G₀) v ≤ lvl (penroseTree G₀) u + 1 := by
    intro u v hadj
    have hmem := (graphOf_adj.mp hadj).1
    have hall := (mem_penroseExt.mp (hGE hmem)).2.2
    unfold allowedPair at hall
    rcases hall with h | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  have hwalk : ∀ (u v : V) (p : (graphOf G).Walk u v),
      lvl (penroseTree G₀) v ≤ lvl (penroseTree G₀) u + p.length := by
    intro u v p
    induction p with
    | nil => simp
    | cons hadj q ih =>
      have := hstep _ _ hadj
      rw [SimpleGraph.Walk.length_cons]
      omega
  -- Schritt 2: Die Schichten von `G` stimmen mit denen von `T` überein.
  have hlvlGT : ∀ v, lvl G v = lvl (penroseTree G₀) v := by
    intro v
    have h1 : lvl G v ≤ lvl (penroseTree G₀) v :=
      SimpleGraph.Reachable.dist_anti (graphOf_mono hTG)
        (hconnT.preconnected _ _)
    have h2 : lvl (penroseTree G₀) v ≤ lvl G v := by
      obtain ⟨p, hp⟩ :=
        (hconnG.preconnected (root V) v).exists_walk_length_eq_dist
      have hw := hwalk _ _ p
      rw [hp, lvl_root] at hw
      unfold lvl at hw ⊢
      omega
    omega
  -- Schritt 3: Die Penrose-Elternknoten stimmen mit denen von `G₀` überein.
  have hpar : ∀ v : V, v ≠ root V → par G v = par G₀ v := by
    intro v hv
    have hspec₀ := par_spec hG₀ hv
    have hadjG : (graphOf G).Adj (par G₀ v) v := by
      refine graphOf_adj.mpr ⟨?_, par_ne hG₀ hv⟩
      rw [Sym2.eq_swap]
      exact hTG (mem_penroseTree_of_ne hv)
    have hlvlv : lvl G (par G₀ v) + 1 = lvl G v := by
      simp only [hlvlGT, lvl_penroseTree hG₀]
      exact hspec₀.2
    have hmemG : par G₀ v ∈ parentSet G v :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadjG, hlvlv⟩
    have hlow : ∀ u ∈ parentSet G v, par G₀ v ≤ u := by
      intro u hu
      obtain ⟨-, hadj, hlvl⟩ := Finset.mem_filter.mp hu
      have hmem := (graphOf_adj.mp hadj).1
      have hall := (mem_penroseExt.mp (hGE hmem)).2.2
      have hlvlT' : lvl (penroseTree G₀) u + 1 = lvl (penroseTree G₀) v := by
        rw [← hlvlGT, ← hlvlGT]
        exact hlvl
      unfold allowedPair at hall
      rcases hall with h | ⟨h, hle⟩ | ⟨h, hle⟩
      · omega
      · rwa [par_penroseTree hG₀ hv] at hle
      · omega
    exact par_eq_of_mem_of_min hmemG hlow
  -- Schritt 4: Gleiche Elternknoten, gleicher Baum.
  unfold penroseTree
  refine Finset.image_congr fun v hv => ?_
  have hv' : v ≠ root V := (Finset.mem_erase.mp (Finset.mem_coe.mp hv)).1
  rw [hpar v hv']

/-! ## Die Baumgraphen-Schranke -/

/-- **Baumgraphen-Schranke (Penrose).** Der Betrag der alternierenden
Summe über die zusammenhängenden aufspannenden Teilgraphen von `H` ist
durch die Anzahl der aufspannenden Bäume in `H` beschränkt:
die zusammenhängenden Teilgraphen zerfallen in Penrose-Intervalle, auf
nichttrivialen Intervallen hebt sich die Summe weg, und jedes Intervall
gehört zu einem aufspannenden Baum. -/
theorem abs_ursellSum_le_treeCount (H : Finset (Sym2 V))
    (hH : ∀ e ∈ H, ¬ e.IsDiag) :
    |ursellSum H| ≤ (treeCount H : ℤ) := by
  set C := H.powerset.filter EdgeConn with hC
  have hmaps : ∀ G ∈ C, penroseTree G ∈ C.image penroseTree :=
    fun G hG => Finset.mem_image_of_mem _ hG
  have hsum : ursellSum H
      = ∑ T ∈ C.image penroseTree,
          ∑ G ∈ C.filter (fun G => penroseTree G = T), (-1 : ℤ) ^ G.card := by
    unfold ursellSum
    rw [← hC]
    exact (Finset.sum_fiberwise_of_maps_to hmaps _).symm
  have hIcc : ∀ T ∈ C.image penroseTree,
      C.filter (fun G => penroseTree G = T)
        = Finset.Icc T (penroseExt H T) := by
    intro T hT
    obtain ⟨G₀, hG₀C, rfl⟩ := Finset.mem_image.mp hT
    rw [hC] at hG₀C
    obtain ⟨hG₀H, hG₀conn⟩ := Finset.mem_filter.mp hG₀C
    rw [Finset.mem_powerset] at hG₀H
    ext G
    simp only [hC, Finset.mem_filter, Finset.mem_powerset, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hGH, hGconn⟩, hpen⟩
      have hfwd := penrose_forward hH hGH hGconn
      rw [hpen] at hfwd
      exact hfwd
    · rintro ⟨hTG, hGE⟩
      have hbwd := penrose_backward hG₀conn hTG hGE
      exact ⟨⟨hGE.trans penroseExt_subset, hbwd.1⟩, hbwd.2⟩
  have hTsub : ∀ T ∈ C.image penroseTree, T ⊆ penroseExt H T := by
    intro T hT
    obtain ⟨G₀, hG₀C, rfl⟩ := Finset.mem_image.mp hT
    rw [hC] at hG₀C
    obtain ⟨hG₀H, hG₀conn⟩ := Finset.mem_filter.mp hG₀C
    rw [Finset.mem_powerset] at hG₀H
    have hfwd := penrose_forward hH hG₀H hG₀conn
    exact hfwd.1.trans hfwd.2
  rw [hsum, Finset.sum_congr rfl (fun T hT => by rw [hIcc T hT])]
  calc |∑ T ∈ C.image penroseTree,
          ∑ G ∈ Finset.Icc T (penroseExt H T), (-1 : ℤ) ^ G.card|
      ≤ ∑ T ∈ C.image penroseTree,
          |∑ G ∈ Finset.Icc T (penroseExt H T), (-1 : ℤ) ^ G.card| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _T ∈ C.image penroseTree, (1 : ℤ) := by
        refine Finset.sum_le_sum fun T hT => ?_
        by_cases hfix : T = penroseExt H T
        · rw [← hfix, Finset.Icc_self, Finset.sum_singleton]
          simp [abs_pow]
        · rw [sum_Icc_neg_one_pow (hTsub T hT) hfix]
          simp
    _ = ((C.image penroseTree).card : ℤ) := by simp
    _ ≤ (treeCount H : ℤ) := by
        have hsub : C.image penroseTree
            ⊆ H.powerset.filter (fun T => (graphOf T).IsTree) := by
          intro T hT
          obtain ⟨G₀, hG₀C, rfl⟩ := Finset.mem_image.mp hT
          rw [hC] at hG₀C
          obtain ⟨hG₀H, hG₀conn⟩ := Finset.mem_filter.mp hG₀C
          rw [Finset.mem_powerset] at hG₀H
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_powerset.mpr ((penroseTree_subset hG₀conn).trans hG₀H),
              penroseTree_isTree hG₀conn⟩
        unfold treeCount
        exact_mod_cast Finset.card_le_card hsub

/-! ## Zählen der aufspannenden Bäume

Die Penrose-Elternabbildung bestimmt jeden aufspannenden Baum
vollständig: ein Baum ist sein eigener Penrose-Baum, und der ist das
Bild der Elternabbildung. Daraus folgt die grobe Wurzelbaum-Schranke
`treeCount H ≤ |V| ^ (|V| - 1)` — höchstens so viele Bäume wie
Elternabbildungen `V ∖ {Wurzel} → V`. -/

/-- Ein aufspannender Baum (ohne Diagonalkanten) ist sein eigener
Penrose-Baum: die Elternkanten sind Baumkanten, und beide Mengen haben
`|V| - 1` Elemente. -/
theorem penroseTree_of_isTree {T : Finset (Sym2 V)}
    (hdiag : ∀ e ∈ T, ¬ e.IsDiag) (hT : (graphOf T).IsTree) :
    penroseTree T = T := by
  have hconn : EdgeConn T := hT.connected
  have hcardT : T.card + 1 = Fintype.card V := by
    have h := (SimpleGraph.isTree_iff_connected_and_card.mp hT).2
    rwa [edgeSet_graphOf hdiag, Nat.card_coe_set_eq, Set.ncard_coe_finset,
      Nat.card_eq_fintype_card] at h
  have hcardP := penroseTree_card hconn
  exact Finset.eq_of_subset_of_card_le (penroseTree_subset hconn) (by omega)

/-- **Wurzelbaum-Schranke an die Baumzahl**: in jedem diagonalfreien
Träger gibt es höchstens `|V| ^ (|V| - 1)` aufspannende Bäume, denn
jeder ist durch seine Penrose-Elternabbildung auf `V ∖ {Wurzel}`
festgelegt. -/
theorem treeCount_le_pow (H : Finset (Sym2 V))
    (hH : ∀ e ∈ H, ¬ e.IsDiag) :
    treeCount H ≤ Fintype.card V ^ (Fintype.card V - 1) := by
  have hinj : Set.InjOn
      (fun T => fun v : ↥(Finset.univ.erase (root V)) => par T v.1)
      ↑(H.powerset.filter (fun T => (graphOf T).IsTree)) := by
    intro T₁ h₁ T₂ h₂ heq
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at h₁ h₂
    have hd₁ : ∀ e ∈ T₁, ¬ e.IsDiag := fun e he => hH e (h₁.1 he)
    have hd₂ : ∀ e ∈ T₂, ¬ e.IsDiag := fun e he => hH e (h₂.1 he)
    have hpar : ∀ v ∈ Finset.univ.erase (root V), par T₁ v = par T₂ v :=
      fun v hv => congrFun heq ⟨v, hv⟩
    calc T₁ = penroseTree T₁ := (penroseTree_of_isTree hd₁ h₁.2).symm
      _ = penroseTree T₂ := Finset.image_congr (fun v hv => by
            rw [hpar v (Finset.mem_coe.mp hv)])
      _ = T₂ := penroseTree_of_isTree hd₂ h₂.2
  have hkey := Finset.card_le_card_of_injOn
    (t := (Finset.univ : Finset (↥(Finset.univ.erase (root V)) → V)))
    (fun T => fun v : ↥(Finset.univ.erase (root V)) => par T v.1)
    (fun T _ => Finset.mem_coe.mpr (Finset.mem_univ _)) hinj
  unfold treeCount
  rwa [Finset.card_univ, Fintype.card_fun, Fintype.card_coe,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at hkey

end Penrose

/-! ## Beispiele: die kleinsten Träger -/

section Examples

/-- Leerer Träger auf einpunktiger Knotenmenge: Ursell-Summe `1`
(nur der leere Graph, und er ist zusammenhängend). -/
theorem ursellSum_empty {V : Type*} [Fintype V] [Subsingleton V] [Nonempty V] :
    ursellSum (∅ : Finset (Sym2 V)) = 1 := by
  have hconn : EdgeConn (∅ : Finset (Sym2 V)) :=
    SimpleGraph.Connected.mk fun u v => by
      rw [Subsingleton.elim u v]
  unfold ursellSum
  rw [Finset.powerset_empty, Finset.filter_singleton, if_pos hconn,
    Finset.sum_singleton, Finset.card_empty, pow_zero]

/-- Genau eine Kante auf zwei Knoten: Ursell-Summe `-1`. -/
theorem ursellSum_pair_edge :
    ursellSum ({s((0 : Fin 2), (1 : Fin 2))} : Finset (Sym2 (Fin 2))) = -1 := by
  have hne : (0 : Fin 2) ≠ 1 := by decide
  have hadj : (graphOf ({s((0 : Fin 2), (1 : Fin 2))} : Finset (Sym2 (Fin 2)))).Adj 0 1 :=
    graphOf_adj.mpr ⟨Finset.mem_singleton_self _, hne⟩
  have hconn : EdgeConn ({s((0 : Fin 2), (1 : Fin 2))} : Finset (Sym2 (Fin 2))) := by
    refine SimpleGraph.Connected.mk fun u v => ?_
    fin_cases u <;> fin_cases v
    · exact SimpleGraph.Reachable.refl _
    · exact hadj.reachable
    · exact hadj.symm.reachable
    · exact SimpleGraph.Reachable.refl _
  have hnotconn : ¬ EdgeConn (∅ : Finset (Sym2 (Fin 2))) := by
    intro hcon
    have hbot : graphOf (∅ : Finset (Sym2 (Fin 2))) = ⊥ := by
      rw [graphOf, Finset.coe_empty, SimpleGraph.fromEdgeSet_empty]
    have hpos := hcon.pos_dist_of_ne hne
    rw [hbot, SimpleGraph.dist_bot] at hpos
    exact absurd hpos (lt_irrefl 0)
  have hpow : ({s((0 : Fin 2), (1 : Fin 2))} : Finset (Sym2 (Fin 2))).powerset
      = {∅, {s((0 : Fin 2), (1 : Fin 2))}} := by
    ext S
    simp [Finset.subset_singleton_iff]
  unfold ursellSum
  rw [hpow, Finset.filter_insert, if_neg hnotconn, Finset.filter_singleton,
    if_pos hconn, Finset.sum_singleton, Finset.card_singleton, pow_one]

end Examples

/-! ## Die Ursell-Funktion eines Polymer-Tupels -/

section UrsellPolymer

variable {ι : Type*} (P : PolymerSystem ι)

/-- Trägerkanten eines Polymer-Tupels: die Indexpaare unverträglicher
Polymere. -/
def clusterEdges {n : ℕ} (γ : Fin n → ι) : Finset (Sym2 (Fin n)) :=
  ((Finset.univ : Finset (Fin n × Fin n)).filter
    (fun p => p.1 ≠ p.2 ∧ P.incomp (γ p.1) (γ p.2) = true)).image
    (fun p => s(p.1, p.2))

theorem mem_clusterEdges {n : ℕ} {γ : Fin n → ι} {i j : Fin n} :
    s(i, j) ∈ clusterEdges P γ ↔ i ≠ j ∧ P.incomp (γ i) (γ j) = true := by
  constructor
  · intro h
    unfold clusterEdges at h
    rw [Finset.mem_image] at h
    obtain ⟨⟨a, b⟩, hab, heq⟩ := h
    obtain ⟨-, hne, hinc⟩ := Finset.mem_filter.mp hab
    rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]
      exact ⟨hne, hinc⟩
    · rw [← h2, ← h1]
      exact ⟨hne.symm, (P.symm _ _).trans hinc⟩
  · rintro ⟨hne, hinc⟩
    unfold clusterEdges
    exact Finset.mem_image_of_mem _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ (i, j), hne, hinc⟩)

theorem clusterEdges_not_isDiag {n : ℕ} (γ : Fin n → ι) :
    ∀ e ∈ clusterEdges P γ, ¬ e.IsDiag := by
  intro e
  induction e using Sym2.ind with
  | _ i j =>
    intro he
    rw [Sym2.mk_isDiag_iff]
    exact ((mem_clusterEdges P).mp he).1

/-- Die (ganzzahlige) Ursell-Funktion eines Polymer-Tupels: die
alternierende Summe über die zusammenhängenden aufspannenden Teilgraphen
des Unverträglichkeitsgraphen der Indizes. In der Cluster-Reihe von
`log Z` trägt das Tupel `γ` mit `ursellInt P γ / (n+1)! · ∏ w (γ i)` bei. -/
noncomputable def ursellInt {n : ℕ} (γ : Fin (n + 1) → ι) : ℤ :=
  ursellSum (clusterEdges P γ)

/-- **Baumgraphen-Schranke für Ursell-Funktionen**: der Betrag ist durch
die Anzahl der aufspannenden Bäume im Unverträglichkeitsgraphen
beschränkt. -/
theorem abs_ursellInt_le_treeCount {n : ℕ} (γ : Fin (n + 1) → ι) :
    |ursellInt P γ| ≤ (treeCount (clusterEdges P γ) : ℤ) :=
  abs_ursellSum_le_treeCount _ (clusterEdges_not_isDiag P γ)

/-- **Wurzelbaum-Schranke für Ursell-Funktionen**:
`|φᵀ(γ₁, …, γ_{n+1})| ≤ (n + 1) ^ n` — die Baumzahl des
Unverträglichkeitsgraphen, abgeschätzt durch die Anzahl der
Elternabbildungen. -/
theorem abs_ursellInt_le_pow {n : ℕ} (γ : Fin (n + 1) → ι) :
    |ursellInt P γ| ≤ ((n + 1) ^ n : ℤ) := by
  refine (abs_ursellInt_le_treeCount P γ).trans ?_
  have h := treeCount_le_pow (clusterEdges P γ) (clusterEdges_not_isDiag P γ)
  rw [Fintype.card_fin] at h
  exact_mod_cast h

/-- Ein einzelnes Polymer: `φᵀ(γ₁) = 1`. -/
theorem ursellInt_single (γ : Fin 1 → ι) : ursellInt P γ = 1 := by
  have h : clusterEdges P γ = ∅ := by
    ext e
    induction e using Sym2.ind with
    | _ i j =>
      simp [mem_clusterEdges, Subsingleton.elim i j]
  have : Subsingleton (Fin (0 + 1)) := ⟨fun a b => by omega⟩
  unfold ursellInt
  rw [h]
  exact ursellSum_empty

/-- Zwei unverträgliche Polymere: `φᵀ(γ₁, γ₂) = -1`. -/
theorem ursellInt_pair (γ : Fin 2 → ι) (h : P.incomp (γ 0) (γ 1) = true) :
    ursellInt P γ = -1 := by
  have hsymm : P.incomp (γ 1) (γ 0) = true := (P.symm _ _).trans h
  have hedges : clusterEdges P γ = {s((0 : Fin 2), (1 : Fin 2))} := by
    ext e
    induction e using Sym2.ind with
    | _ i j =>
      fin_cases i <;> fin_cases j <;>
        simp [mem_clusterEdges, h, hsymm]
  unfold ursellInt
  rw [hedges]
  exact ursellSum_pair_edge

end UrsellPolymer

end ClusterExpansion
