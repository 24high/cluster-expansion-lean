/-
Copyright (c) 2026 Dennis Michael Heine. All rights reserved.
Released under the CC BY-NC-SA 4.0 license as described in the file LICENSE.
Authors: Dennis Michael Heine
-/
import KPLean.Ursell

/-!
# Mayer-Entwicklung und Cluster-Rekursion

Die endliche, rein algebraische Schicht der Exponentialformel der
Cluster-Entwicklung, vollständig bewiesen über beliebigen kommutativen
Ringen:

* die **Mayer-Entwicklung** (`Z_eq_sum_graphs`): die Zustandssumme als
  Doppelsumme über Teilmengen und Graphen,

  `Z Λ = ∑_{S ⊆ Λ} (∏_{γ∈S} w γ) · ∑_{G ⊆ E(S)} (-1)^{|G|}`,

  wobei `E(S)` die Unverträglichkeitskanten innerhalb `S` sind — der
  harte Kern `∑_{G ⊆ E} (-1)^{|G|} = [E = ∅]` ersetzt den
  Unabhängigkeits-Indikator;

* die **Cluster-Rekursion** (`Z_cluster_recursion`): Aufspaltung nach
  der Zusammenhangskomponente eines festen Polymers `γ₀`,

  `Z Λ = Z (Λ ∖ {γ₀}) + ∑_{γ₀ ∈ B ⊆ Λ} (∏_{γ∈B} w γ) · φ(B) · Z (Λ ∖ B)`,

  mit der mengenwertigen Ursell-Vorzeichensumme
  `φ(B) = ∑_{G ⊆ E(B) zusammenhängend aufspannend auf B} (-1)^{|G|}`
  (`ursellSetSum`). Das ist die endliche Exponentialstruktur der
  Cluster-Entwicklung: iteriert erzeugt sie die Cluster-Reihe von
  `log Z`;

* das **Brückenlemma** (`ursellInt_eq_ursellSetSum`): für injektive
  Tupel stimmt die Ursell-Funktion der Tupelebene mit der
  mengenwertigen Ursell-Summe des Bildes überein — `Sym2.map γ` ist
  eine vorzeichenerhaltende Bijektion der Summationsbereiche;

* die **Cluster-Faktorisierung** (`Z_eq_sum_clusterCollections`): das
  geschlossene Iterat der Rekursion,

  `Z Λ = ∑_C ∏_{B ∈ C} (∏_{γ∈B} w γ) · φ(B)`,

  Summe über alle Kollektionen `C` paarweise disjunkter, nichtleerer
  Cluster in `Λ` (`IsClusterCollection`) — die endliche
  Exponentialformel in Mengenform, per Induktion über die Kardinalität
  entlang `Z_cluster_recursion`.

Kein `sorry` in dieser Datei. Bewusst offen (nur genannt, nichts
Unbewiesenes behauptet): der Logarithmus- und Konvergenzschritt —
die Identifikation der Cluster-Reihe mit `log Z`
unter der Kotecký-Preiss-Bedingung.

Referenzen: Mayer–Montroll (J. Chem. Phys. 9, 1941); Friedli–Velenik,
Kap. 5; Scott–Sokal (J. Stat. Phys. 118, 2005), §2.
-/

open Finset

set_option linter.style.openClassical false

open scoped Classical

namespace ClusterExpansion

variable {ι : Type*} [DecidableEq ι] (P : PolymerSystem ι)

/-! ## Unverträglichkeitskanten -/

/-- Die Unverträglichkeitskanten innerhalb `S`: ungeordnete Paare
verschiedener, unverträglicher Polymere aus `S`. -/
def incompatEdges (S : Finset ι) : Finset (Sym2 ι) :=
  ((S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧ P.incomp p.1 p.2 = true)).image
    (fun p => s(p.1, p.2))

theorem mem_incompatEdges {S : Finset ι} {u v : ι} :
    s(u, v) ∈ incompatEdges P S
      ↔ u ∈ S ∧ v ∈ S ∧ u ≠ v ∧ P.incomp u v = true := by
  constructor
  · intro h
    unfold incompatEdges at h
    rw [Finset.mem_image] at h
    obtain ⟨⟨a, b⟩, hab, heq⟩ := h
    obtain ⟨hmem, hne, hinc⟩ := Finset.mem_filter.mp hab
    rw [Finset.mem_product] at hmem
    rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]
      exact ⟨hmem.1, hmem.2, hne, hinc⟩
    · rw [← h2, ← h1]
      exact ⟨hmem.2, hmem.1, hne.symm, (P.symm _ _).trans hinc⟩
  · rintro ⟨hu, hv, hne, hinc⟩
    unfold incompatEdges
    exact Finset.mem_image_of_mem _
      (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu, hv⟩, hne, hinc⟩)

theorem incompatEdges_not_isDiag {S : Finset ι} :
    ∀ e ∈ incompatEdges P S, ¬ e.IsDiag := by
  intro e
  induction e using Sym2.ind with
  | _ u v =>
    intro he
    rw [Sym2.mk_isDiag_iff]
    exact ((mem_incompatEdges P).mp he).2.2.1

theorem incompatEdges_mem_of_mem {S : Finset ι} {e : Sym2 ι}
    (he : e ∈ incompatEdges P S) : ∀ y ∈ e, y ∈ S := by
  induction e using Sym2.ind with
  | _ u v =>
    obtain ⟨hu, hv, -, -⟩ := (mem_incompatEdges P).mp he
    intro y hy
    rcases Sym2.mem_iff.mp hy with rfl | rfl
    · exact hu
    · exact hv

theorem incompatEdges_mono {S T : Finset ι} (h : S ⊆ T) :
    incompatEdges P S ⊆ incompatEdges P T := by
  intro e
  induction e using Sym2.ind with
  | _ u v =>
    intro he
    obtain ⟨hu, hv, hne, hinc⟩ := (mem_incompatEdges P).mp he
    exact (mem_incompatEdges P).mpr ⟨h hu, h hv, hne, hinc⟩

/-- Innerhalb `S ⊆ Λ` sind die Unverträglichkeitskanten genau die
globalen Kanten, deren Endpunkte in `S` liegen. -/
theorem incompatEdges_eq_filter {S Λ : Finset ι} (hS : S ⊆ Λ) :
    incompatEdges P S
      = (incompatEdges P Λ).filter (fun e => ∀ y ∈ e, y ∈ S) := by
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    rw [Finset.mem_filter, mem_incompatEdges, mem_incompatEdges]
    constructor
    · rintro ⟨hu, hv, hne, hinc⟩
      refine ⟨⟨hS hu, hS hv, hne, hinc⟩, ?_⟩
      intro y hy
      rcases Sym2.mem_iff.mp hy with rfl | rfl
      · exact hu
      · exact hv
    · rintro ⟨⟨-, -, hne, hinc⟩, hin⟩
      exact ⟨hin u (Sym2.mem_mk_left u v), hin v (Sym2.mem_mk_right u v),
        hne, hinc⟩

/-- `S` ist genau dann unabhängig, wenn es innerhalb `S` keine
Unverträglichkeitskanten gibt. -/
theorem indep_iff_incompatEdges_eq_empty {S : Finset ι} :
    Indep P S ↔ incompatEdges P S = ∅ := by
  constructor
  · intro h
    rw [Finset.eq_empty_iff_forall_notMem]
    intro e
    induction e using Sym2.ind with
    | _ u v =>
      intro he
      obtain ⟨hu, hv, hne, hinc⟩ := (mem_incompatEdges P).mp he
      rw [h u hu v hv hne] at hinc
      exact Bool.noConfusion hinc
  · intro h γ hγ δ hδ hne
    rcases Bool.eq_false_or_eq_true (P.incomp γ δ) with ht | hf
    · exfalso
      have : s(γ, δ) ∈ incompatEdges P S :=
        (mem_incompatEdges P).mpr ⟨hγ, hδ, hne, ht⟩
      rw [h] at this
      exact Finset.notMem_empty _ this
    · exact hf

/-! ## Die Mayer-Entwicklung -/

/-- Die alternierende Powerset-Summe in einem beliebigen kommutativen
Ring: `1` für die leere Menge, sonst `0`. -/
theorem sum_powerset_neg_one_pow_card_ring {α R : Type*} [DecidableEq α]
    [CommRing R] (E : Finset α) :
    ∑ G ∈ E.powerset, (-1 : R) ^ G.card = if E = ∅ then 1 else 0 := by
  have h := Finset.sum_powerset_neg_one_pow_card (x := E)
  have h2 : (((∑ G ∈ E.powerset, (-1 : ℤ) ^ G.card) : ℤ) : R)
      = ∑ G ∈ E.powerset, (-1 : R) ^ G.card := by
    push_cast
    rfl
  rw [← h2, h]
  split <;> simp

/-- **Mayer-Entwicklung**: die Zustandssumme als Doppelsumme über
Teilmengen und Teilgraphen ihrer Unverträglichkeitskanten. Die innere
alternierende Summe ersetzt den Unabhängigkeits-Indikator. -/
theorem Z_eq_sum_graphs {R : Type*} [CommRing R] (w : ι → R) (Λ : Finset ι) :
    Z P w Λ = ∑ S ∈ Λ.powerset, (∏ γ ∈ S, w γ) *
      ∑ G ∈ (incompatEdges P S).powerset, (-1 : R) ^ G.card := by
  unfold Z
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [sum_powerset_neg_one_pow_card_ring]
  by_cases h : Indep P S
  · rw [if_pos h, if_pos ((indep_iff_incompatEdges_eq_empty P).mp h), mul_one]
  · rw [if_neg h,
      if_neg (fun he => h ((indep_iff_incompatEdges_eq_empty P).mpr he)),
      mul_zero]

/-! ## Zusammenhangskomponenten -/

/-- Die Zusammenhangskomponente von `x` innerhalb `S` bezüglich der
Kantenmenge `G`. -/
noncomputable def component (G : Finset (Sym2 ι)) (x : ι) (S : Finset ι) :
    Finset ι :=
  S.filter (fun v => (graphOf G).Reachable x v)

omit [DecidableEq ι] in
theorem mem_component {G : Finset (Sym2 ι)} {x v : ι} {S : Finset ι} :
    v ∈ component G x S ↔ v ∈ S ∧ (graphOf G).Reachable x v :=
  Finset.mem_filter

omit [DecidableEq ι] in
theorem component_subset {G : Finset (Sym2 ι)} {x : ι} {S : Finset ι} :
    component G x S ⊆ S :=
  Finset.filter_subset _ _

omit [DecidableEq ι] in
theorem self_mem_component {G : Finset (Sym2 ι)} {x : ι} {S : Finset ι}
    (hx : x ∈ S) : x ∈ component G x S :=
  mem_component.mpr ⟨hx, SimpleGraph.Reachable.refl x⟩

omit [DecidableEq ι] in
/-- Läuft ein Weg von einem Punkt einer kantenabgeschlossenen Menge los,
bleibt er in ihr. -/
theorem walk_stays {G : Finset (Sym2 ι)} {A : Finset ι}
    (hA : ∀ u v : ι, s(u, v) ∈ G → u ∈ A → v ∈ A) :
    ∀ {u v : ι}, (graphOf G).Walk u v → u ∈ A → v ∈ A := by
  intro u v p
  induction p with
  | nil => exact fun h => h
  | cons hadj q ih =>
    intro hu
    exact ih (hA _ _ (graphOf_adj.mp hadj).1 hu)

omit [DecidableEq ι] in
/-- Ein Weg, der in einer kantenabgeschlossenen Menge startet, existiert
auch im auf diese Menge eingeschränkten Graphen. -/
theorem walk_transfer {G : Finset (Sym2 ι)} {A : Finset ι}
    (hA : ∀ u v : ι, s(u, v) ∈ G → u ∈ A → v ∈ A) :
    ∀ {u v : ι}, (graphOf G).Walk u v → u ∈ A →
      (graphOf (G.filter (fun e => ∀ y ∈ e, y ∈ A))).Reachable u v := by
  intro u v p
  induction p with
  | nil => exact fun _ => SimpleGraph.Reachable.refl _
  | @cons a b c hadj q ih =>
    intro ha
    have he := (graphOf_adj.mp hadj).1
    have hb : b ∈ A := hA _ _ he ha
    have hmem : s(a, b) ∈ G.filter (fun e => ∀ y ∈ e, y ∈ A) := by
      refine Finset.mem_filter.mpr ⟨he, ?_⟩
      intro y hy
      rcases Sym2.mem_iff.mp hy with rfl | rfl
      · exact ha
      · exact hb
    have hadj' : (graphOf (G.filter (fun e => ∀ y ∈ e, y ∈ A))).Adj a b :=
      graphOf_adj.mpr ⟨hmem, (graphOf_adj.mp hadj).2⟩
    exact hadj'.reachable.trans (ih hb)

omit [DecidableEq ι] in
/-- Kanten von `G` mit einem Endpunkt in der Komponente liegen ganz in
ihr. -/
theorem component_closed {G : Finset (Sym2 ι)} {x : ι} {S : Finset ι}
    (hin : ∀ e ∈ G, ∀ y ∈ e, y ∈ S) :
    ∀ u v : ι, s(u, v) ∈ G → u ∈ component G x S → v ∈ component G x S := by
  intro u v he hu
  by_cases hne : u = v
  · rwa [← hne]
  · obtain ⟨-, hreach⟩ := mem_component.mp hu
    have hadj : (graphOf G).Adj u v := graphOf_adj.mpr ⟨he, hne⟩
    exact mem_component.mpr
      ⟨hin _ he v (Sym2.mem_mk_right u v), hreach.trans hadj.reachable⟩

omit [DecidableEq ι] in
/-- Die Einschränkung von `G` auf die Komponente verbindet je zwei
Komponentenpunkte. -/
theorem component_conn {G : Finset (Sym2 ι)} {x : ι} {S : Finset ι}
    (hin : ∀ e ∈ G, ∀ y ∈ e, y ∈ S) :
    ∀ u ∈ component G x S, ∀ v ∈ component G x S,
      (graphOf (G.filter
        (fun e => ∀ y ∈ e, y ∈ component G x S))).Reachable u v := by
  intro u hu v hv
  obtain ⟨-, hru⟩ := mem_component.mp hu
  obtain ⟨-, hrv⟩ := mem_component.mp hv
  obtain ⟨p⟩ := hru.symm.trans hrv
  exact walk_transfer (component_closed hin) p hu

/-- Besteht `G` aus einem `B`-inneren, `B` verbindenden Teil und einem
von `B` disjunkten Rest, ist die Komponente von `x ∈ B` genau `B`. -/
theorem component_union {Gb Gr : Finset (Sym2 ι)} {x : ι} {B S : Finset ι}
    (hxB : x ∈ B) (hBS : B ⊆ S)
    (hGb : ∀ e ∈ Gb, ∀ y ∈ e, y ∈ B)
    (hconn : ∀ u ∈ B, ∀ v ∈ B, (graphOf Gb).Reachable u v)
    (hGr : ∀ e ∈ Gr, ∀ y ∈ e, y ∉ B) :
    component (Gb ∪ Gr) x S = B := by
  ext v
  rw [mem_component]
  constructor
  · rintro ⟨hvS, hreach⟩
    obtain ⟨p⟩ := hreach
    refine walk_stays (G := Gb ∪ Gr) (A := B) ?_ p hxB
    intro a b hab haB
    rcases Finset.mem_union.mp hab with h | h
    · exact hGb _ h b (Sym2.mem_mk_right a b)
    · exact absurd haB (hGr _ h a (Sym2.mem_mk_left a b))
  · intro hvB
    exact ⟨hBS hvB,
      (hconn x hxB v hvB).mono (graphOf_mono Finset.subset_union_left)⟩

/-! ## Die mengenwertige Ursell-Summe -/

/-- Potenzmenge eines Filters = Filter der Potenzmenge. -/
theorem powerset_filter_eq {α : Type*} (A : Finset α)
    (p : α → Prop) [DecidablePred p] :
    (A.filter p).powerset
      = A.powerset.filter (fun G => ∀ e ∈ G, p e) := by
  ext G
  simp only [Finset.mem_powerset, Finset.mem_filter]
  constructor
  · intro h
    exact ⟨fun e he => (Finset.mem_filter.mp (h he)).1,
      fun e he => (Finset.mem_filter.mp (h he)).2⟩
  · rintro ⟨hGA, hp⟩ e he
    exact Finset.mem_filter.mpr ⟨hGA he, hp e he⟩

/-- Die mengenwertige Ursell-Vorzeichensumme: alternierende Summe über
die `B` zusammenhängend aufspannenden Teilgraphen der
Unverträglichkeitskanten von `B`. -/
noncomputable def ursellSetSum {R : Type*} [CommRing R] (B : Finset ι) : R :=
  ∑ G ∈ (incompatEdges P B).powerset.filter
      (fun G => ∀ u ∈ B, ∀ v ∈ B, (graphOf G).Reachable u v),
    (-1 : R) ^ G.card

/-- Ein einzelnes Polymer: `φ({γ}) = 1`. -/
theorem ursellSetSum_singleton {R : Type*} [CommRing R] (γ : ι) :
    (ursellSetSum P {γ} : R) = 1 := by
  have hE : incompatEdges P {γ} = ∅ := by
    rw [← indep_iff_incompatEdges_eq_empty]
    intro a ha b hb hne
    rw [Finset.mem_singleton] at ha hb
    exact absurd (ha.trans hb.symm) hne
  have hcon : ∀ u ∈ ({γ} : Finset ι), ∀ v ∈ ({γ} : Finset ι),
      (graphOf (∅ : Finset (Sym2 ι))).Reachable u v := by
    intro u hu v hv
    rw [Finset.mem_singleton] at hu hv
    subst hu
    subst hv
    exact SimpleGraph.Reachable.refl _
  unfold ursellSetSum
  rw [hE, Finset.powerset_empty, Finset.filter_singleton, if_pos hcon,
    Finset.sum_singleton, Finset.card_empty, pow_zero]

/-- Zwei unverträgliche Polymere: `φ({γ, δ}) = -1`. -/
theorem ursellSetSum_pair {R : Type*} [CommRing R] {γ δ : ι}
    (hne : γ ≠ δ) (hinc : P.incomp γ δ = true) :
    (ursellSetSum P {γ, δ} : R) = -1 := by
  have hE : incompatEdges P {γ, δ} = {s(γ, δ)} := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      rw [mem_incompatEdges, Finset.mem_singleton, Sym2.eq_iff]
      constructor
      · rintro ⟨hu, hv, hne', hinc'⟩
        rcases Finset.mem_insert.mp hu with rfl | hu'
        · rcases Finset.mem_insert.mp hv with rfl | hv'
          · exact absurd rfl hne'
          · rw [Finset.mem_singleton] at hv'
            exact Or.inl ⟨rfl, hv'⟩
        · rw [Finset.mem_singleton] at hu'
          rcases Finset.mem_insert.mp hv with rfl | hv'
          · exact Or.inr ⟨hu', rfl⟩
          · rw [Finset.mem_singleton] at hv'
            rw [hu', hv'] at hne'
            exact absurd rfl hne'
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact ⟨Finset.mem_insert_self _ _,
            Finset.mem_insert_of_mem (Finset.mem_singleton_self _), hne, hinc⟩
        · exact ⟨Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
            Finset.mem_insert_self _ _, hne.symm, (P.symm _ _).trans hinc⟩
  have hadj : (graphOf ({s(γ, δ)} : Finset (Sym2 ι))).Adj γ δ :=
    graphOf_adj.mpr ⟨Finset.mem_singleton_self _, hne⟩
  have hconn : ∀ u ∈ ({γ, δ} : Finset ι), ∀ v ∈ ({γ, δ} : Finset ι),
      (graphOf ({s(γ, δ)} : Finset (Sym2 ι))).Reachable u v := by
    intro u hu v hv
    rcases Finset.mem_insert.mp hu with rfl | hu' <;>
      rcases Finset.mem_insert.mp hv with rfl | hv'
    · exact SimpleGraph.Reachable.refl _
    · rw [Finset.mem_singleton] at hv'
      rw [hv']
      exact hadj.reachable
    · rw [Finset.mem_singleton] at hu'
      rw [hu']
      exact hadj.symm.reachable
    · rw [Finset.mem_singleton] at hu' hv'
      rw [hu', hv']
  have hnotconn : ¬ ∀ u ∈ ({γ, δ} : Finset ι), ∀ v ∈ ({γ, δ} : Finset ι),
      (graphOf (∅ : Finset (Sym2 ι))).Reachable u v := by
    intro h
    have hreach := h γ (Finset.mem_insert_self _ _) δ
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have hbot : graphOf (∅ : Finset (Sym2 ι)) = ⊥ := by
      rw [graphOf, Finset.coe_empty, SimpleGraph.fromEdgeSet_empty]
    rw [hbot] at hreach
    have hd : (⊥ : SimpleGraph ι).dist γ δ = 0 := SimpleGraph.dist_bot
    exact hne (hreach.dist_eq_zero_iff.mp hd)
  have hpow : ({s(γ, δ)} : Finset (Sym2 ι)).powerset = {∅, {s(γ, δ)}} := by
    ext S
    simp [Finset.subset_singleton_iff]
  unfold ursellSetSum
  rw [hE, hpow, Finset.filter_insert, if_neg hnotconn, Finset.filter_singleton,
    if_pos hconn, Finset.sum_singleton, Finset.card_singleton, pow_one]

/-! ## Die Cluster-Rekursion -/

/-- Mayer-Entwicklung in Paarform: Summe über Paare `(S, G)` aus
Teilmenge und Teilgraph. -/
theorem Z_eq_sum_pairs {R : Type*} [CommRing R] (w : ι → R) (M : Finset ι) :
    Z P w M = ∑ p ∈ (M.powerset ×ˢ (incompatEdges P M).powerset).filter
        (fun p => ∀ e ∈ p.2, ∀ y ∈ e, y ∈ p.1),
      (∏ γ ∈ p.1, w γ) * (-1 : R) ^ p.2.card := by
  rw [Z_eq_sum_graphs]
  have hchar : ∀ p : Finset ι × Finset (Sym2 ι),
      p ∈ (M.powerset ×ˢ (incompatEdges P M).powerset).filter
          (fun p => ∀ e ∈ p.2, ∀ y ∈ e, y ∈ p.1)
        ↔ p.1 ∈ M.powerset ∧ p.2 ∈ (incompatEdges P p.1).powerset := by
    rintro ⟨S, G⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset]
    constructor
    · rintro ⟨⟨hSM, hGM⟩, hin⟩
      refine ⟨hSM, ?_⟩
      rw [incompatEdges_eq_filter P hSM]
      exact fun e he => Finset.mem_filter.mpr ⟨hGM he, hin e he⟩
    · rintro ⟨hSM, hGS⟩
      exact ⟨⟨hSM, fun e he => incompatEdges_mono P hSM (hGS he)⟩,
        fun e he => incompatEdges_mem_of_mem P (hGS he)⟩
  rw [Finset.sum_congr rfl (fun S _ => by rw [Finset.mul_sum])]
  exact (Finset.sum_finset_product' _ _ _ hchar).symm

/-- Jede Kante liegt entweder ganz in der Komponente `B` oder ganz
außerhalb. -/
private theorem fiber_split {γ₀ : ι} {B S : Finset ι} {G : Finset (Sym2 ι)}
    (hin : ∀ e ∈ G, ∀ y ∈ e, y ∈ S) (hcomp : component G γ₀ S = B) :
    ∀ e ∈ G, (∀ y ∈ e, y ∈ B) ∨ (∀ y ∈ e, y ∈ S \ B) := by
  have hclosed : ∀ u v : ι, s(u, v) ∈ G → u ∈ B → v ∈ B := by
    have := component_closed (x := γ₀) hin
    rwa [hcomp] at this
  intro e
  induction e using Sym2.ind with
  | _ u v =>
    intro he
    by_cases hu : u ∈ B
    · left
      have hv := hclosed u v he hu
      intro y hy
      rcases Sym2.mem_iff.mp hy with rfl | rfl
      · exact hu
      · exact hv
    · by_cases hv : v ∈ B
      · have he' : s(v, u) ∈ G := by rwa [Sym2.eq_swap]
        exact absurd (hclosed v u he' hv) hu
      · right
        intro y hy
        have hyS : y ∈ S := hin _ he y hy
        rcases Sym2.mem_iff.mp hy with rfl | rfl
        · exact Finset.mem_sdiff.mpr ⟨hyS, hu⟩
        · exact Finset.mem_sdiff.mpr ⟨hyS, hv⟩

/-- Auswertung einer Komponentenfaser: die Paare mit Komponente `B`
summieren sich zu `(∏_B w) · φ(B) · Z(Λ ∖ B)`. -/
private theorem fiber_sum {R : Type*} [CommRing R] (w : ι → R)
    {Λ : Finset ι} {γ₀ : ι} {B : Finset ι} (hBΛ : B ⊆ Λ) (hγB : γ₀ ∈ B) :
    ∑ p ∈ ((Λ.powerset ×ˢ (incompatEdges P Λ).powerset).filter
        (fun p => γ₀ ∈ p.1 ∧ ∀ e ∈ p.2, ∀ y ∈ e, y ∈ p.1)).filter
        (fun p => component p.2 γ₀ p.1 = B),
      (∏ γ ∈ p.1, w γ) * (-1 : R) ^ p.2.card
    = (∏ γ ∈ B, w γ) * ursellSetSum P B * Z P w (Λ \ B) := by
  have hstep1 :
      ∑ p ∈ ((Λ.powerset ×ˢ (incompatEdges P Λ).powerset).filter
          (fun p => γ₀ ∈ p.1 ∧ ∀ e ∈ p.2, ∀ y ∈ e, y ∈ p.1)).filter
          (fun p => component p.2 γ₀ p.1 = B),
        (∏ γ ∈ p.1, w γ) * (-1 : R) ^ p.2.card
      = ∑ q ∈ ((incompatEdges P B).powerset.filter
            (fun G => ∀ u ∈ B, ∀ v ∈ B, (graphOf G).Reachable u v)) ×ˢ
          (((Λ \ B).powerset ×ˢ (incompatEdges P (Λ \ B)).powerset).filter
            (fun q => ∀ e ∈ q.2, ∀ y ∈ e, y ∈ q.1)),
        ((∏ γ ∈ B, w γ) * (-1 : R) ^ q.1.card)
          * ((∏ γ ∈ q.2.1, w γ) * (-1 : R) ^ q.2.2.card) := by
    refine Finset.sum_nbij'
      (fun p => (p.2.filter (fun e => ∀ y ∈ e, y ∈ B),
        (p.1 \ B, p.2.filter (fun e => ¬ ∀ y ∈ e, y ∈ B))))
      (fun q => (B ∪ q.2.1, q.1 ∪ q.2.2)) ?_ ?_ ?_ ?_ ?_
    · -- Hinrichtung: die Faser landet im Produkt
      rintro ⟨S, G⟩ hp
      obtain ⟨hp', hcomp⟩ := Finset.mem_filter.mp hp
      obtain ⟨hmem, hγS, hin⟩ := Finset.mem_filter.mp hp'
      rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hmem
      obtain ⟨hSΛ, hGΛ⟩ := hmem
      have hBS : B ⊆ S := hcomp ▸ component_subset
      have hsplit := fiber_split hin hcomp
      rw [Finset.mem_product]
      constructor
      · -- G ∩ B-innen ist zusammenhängend aufspannend auf B
        rw [Finset.mem_filter, Finset.mem_powerset]
        constructor
        · rw [incompatEdges_eq_filter P hBΛ]
          exact Finset.filter_subset_filter _ hGΛ
        · have hcc := component_conn (x := γ₀) hin
          simp only [hcomp] at hcc
          exact hcc
      · -- Rest ist ein Mayer-Paar auf Λ ∖ B
        rw [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset,
          Finset.mem_powerset]
        have hrest : ∀ e ∈ G.filter (fun e => ¬ ∀ y ∈ e, y ∈ B),
            ∀ y ∈ e, y ∈ S \ B := by
          intro e he
          obtain ⟨heG, hnot⟩ := Finset.mem_filter.mp he
          rcases hsplit e heG with h | h
          · exact absurd h hnot
          · exact h
        refine ⟨⟨Finset.sdiff_subset_sdiff hSΛ Finset.Subset.rfl, ?_⟩, ?_⟩
        · intro e he
          have heG := Finset.mem_filter.mp he |>.1
          have hyS := hrest e he
          induction e using Sym2.ind with
          | _ u v =>
            obtain ⟨-, -, hne, hinc⟩ := (mem_incompatEdges P).mp (hGΛ heG)
            refine (mem_incompatEdges P).mpr ⟨?_, ?_, hne, hinc⟩
            · exact Finset.mem_sdiff.mpr
                ⟨hSΛ (Finset.mem_sdiff.mp (hyS u (Sym2.mem_mk_left u v))).1,
                 (Finset.mem_sdiff.mp (hyS u (Sym2.mem_mk_left u v))).2⟩
            · exact Finset.mem_sdiff.mpr
                ⟨hSΛ (Finset.mem_sdiff.mp (hyS v (Sym2.mem_mk_right u v))).1,
                 (Finset.mem_sdiff.mp (hyS v (Sym2.mem_mk_right u v))).2⟩
        · exact hrest
    · -- Rückrichtung: das Produkt landet in der Faser
      rintro ⟨Gb, S', G'⟩ hq
      rw [Finset.mem_product] at hq
      obtain ⟨hGb, hq'⟩ := hq
      rw [Finset.mem_filter, Finset.mem_powerset] at hGb
      obtain ⟨hGbB, hconn⟩ := hGb
      rw [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset,
        Finset.mem_powerset] at hq'
      obtain ⟨⟨hS', hG'⟩, hin'⟩ := hq'
      have hGbIn : ∀ e ∈ Gb, ∀ y ∈ e, y ∈ B :=
        fun e he => incompatEdges_mem_of_mem P (hGbB he)
      have hG'notB : ∀ e ∈ G', ∀ y ∈ e, y ∉ B := by
        intro e he y hy
        exact fun hyB =>
          (Finset.mem_sdiff.mp (hS' (hin' e he y hy))).2 hyB
      rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset,
          Finset.mem_powerset]
        refine ⟨⟨Finset.union_subset hBΛ
          (hS'.trans Finset.sdiff_subset), ?_⟩,
          Finset.mem_union_left _ hγB, ?_⟩
        · intro e he
          rcases Finset.mem_union.mp he with h | h
          · exact incompatEdges_mono P hBΛ (hGbB h)
          · exact incompatEdges_mono P Finset.sdiff_subset (hG' h)
        · intro e he y hy
          rcases Finset.mem_union.mp he with h | h
          · exact Finset.mem_union_left _ (hGbIn e h y hy)
          · exact Finset.mem_union_right _ (hin' e h y hy)
      · exact component_union hγB Finset.subset_union_left hGbIn hconn hG'notB
    · -- Linksinverse
      rintro ⟨S, G⟩ hp
      obtain ⟨hp', hcomp⟩ := Finset.mem_filter.mp hp
      obtain ⟨hmem, hγS, hin⟩ := Finset.mem_filter.mp hp'
      have hBS : B ⊆ S := hcomp ▸ component_subset
      have h1 : B ∪ S \ B = S := Finset.union_sdiff_of_subset hBS
      have h2 : G.filter (fun e => ∀ y ∈ e, y ∈ B)
          ∪ G.filter (fun e => ¬ ∀ y ∈ e, y ∈ B) = G := by
        rw [← Finset.filter_or]
        exact Finset.filter_true_of_mem fun e _ => em _
      exact Prod.ext h1 h2
    · -- Rechtsinverse
      rintro ⟨Gb, S', G'⟩ hq
      rw [Finset.mem_product] at hq
      obtain ⟨hGb, hq'⟩ := hq
      rw [Finset.mem_filter, Finset.mem_powerset] at hGb
      obtain ⟨hGbB, -⟩ := hGb
      rw [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset,
        Finset.mem_powerset] at hq'
      obtain ⟨⟨hS', hG'⟩, hin'⟩ := hq'
      have hGbIn : ∀ e ∈ Gb, ∀ y ∈ e, y ∈ B :=
        fun e he => incompatEdges_mem_of_mem P (hGbB he)
      have hG'notB : ∀ e ∈ G', ¬ ∀ y ∈ e, y ∈ B := by
        intro e he
        induction e using Sym2.ind with
        | _ u v =>
          intro hall
          exact (Finset.mem_sdiff.mp
            (hS' (hin' _ he u (Sym2.mem_mk_left u v)))).2
            (hall u (Sym2.mem_mk_left u v))
      have hdisj : Disjoint B S' := Finset.disjoint_left.mpr
        (fun a haB haS' => (Finset.mem_sdiff.mp (hS' haS')).2 haB)
      have h1 : (Gb ∪ G').filter (fun e => ∀ y ∈ e, y ∈ B) = Gb := by
        rw [Finset.filter_union, Finset.filter_true_of_mem hGbIn,
          Finset.filter_false_of_mem hG'notB, Finset.union_empty]
      have h2 : (B ∪ S') \ B = S' := Finset.union_sdiff_cancel_left hdisj
      have h3 : (Gb ∪ G').filter (fun e => ¬ ∀ y ∈ e, y ∈ B) = G' := by
        rw [Finset.filter_union,
          Finset.filter_false_of_mem (fun e he h => h (hGbIn e he)),
          Finset.filter_true_of_mem hG'notB, Finset.empty_union]
      exact Prod.ext h1 (Prod.ext h2 h3)
    · -- Gewichte faktorisieren
      rintro ⟨S, G⟩ hp
      obtain ⟨hp', hcomp⟩ := Finset.mem_filter.mp hp
      obtain ⟨hmem, hγS, hin⟩ := Finset.mem_filter.mp hp'
      have hBS : B ⊆ S := hcomp ▸ component_subset
      have hprod : ∏ γ ∈ S, w γ = (∏ γ ∈ B, w γ) * ∏ γ ∈ S \ B, w γ := by
        rw [mul_comm, Finset.prod_sdiff hBS]
      have hcard : G.card
          = (G.filter (fun e => ∀ y ∈ e, y ∈ B)).card
            + (G.filter (fun e => ¬ ∀ y ∈ e, y ∈ B)).card :=
        (Finset.card_filter_add_card_filter_not _).symm
      rw [hprod, hcard, pow_add]
      ring
  rw [hstep1, Finset.sum_product]
  dsimp only
  rw [← Finset.sum_mul_sum, ← Finset.mul_sum, ← Z_eq_sum_pairs]
  unfold ursellSetSum
  rfl

/-- **Cluster-Rekursion**: die Zustandssumme, aufgespalten nach der
Zusammenhangskomponente des festen Polymers `γ₀` in der
Mayer-Entwicklung. Für `γ₀ ∉ Λ` ist die Summe leer und die Identität
trivial. Iteriert erzeugt diese Identität die Cluster-Reihe von `log Z`. -/
theorem Z_cluster_recursion {R : Type*} [CommRing R] (w : ι → R)
    (Λ : Finset ι) (γ₀ : ι) :
    Z P w Λ = Z P w (Λ.erase γ₀)
      + ∑ B ∈ Λ.powerset.filter (fun B => γ₀ ∈ B),
          (∏ γ ∈ B, w γ) * ursellSetSum P B * Z P w (Λ \ B) := by
  rw [Z_eq_sum_graphs,
    ← Finset.sum_filter_add_sum_filter_not Λ.powerset (fun S => γ₀ ∈ S)]
  have hnotpart :
      Λ.powerset.filter (fun S => ¬ γ₀ ∈ S) = (Λ.erase γ₀).powerset := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_erase]
  rw [hnotpart, ← Z_eq_sum_graphs, add_comm]
  congr 1
  have hchar : ∀ p : Finset ι × Finset (Sym2 ι),
      p ∈ (Λ.powerset ×ˢ (incompatEdges P Λ).powerset).filter
          (fun p => γ₀ ∈ p.1 ∧ ∀ e ∈ p.2, ∀ y ∈ e, y ∈ p.1)
        ↔ p.1 ∈ Λ.powerset.filter (fun S => γ₀ ∈ S)
          ∧ p.2 ∈ (incompatEdges P p.1).powerset := by
    rintro ⟨S, G⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset]
    constructor
    · rintro ⟨⟨hSΛ, hGΛ⟩, hγ, hin⟩
      refine ⟨⟨hSΛ, hγ⟩, ?_⟩
      rw [incompatEdges_eq_filter P hSΛ]
      exact fun e he => Finset.mem_filter.mpr ⟨hGΛ he, hin e he⟩
    · rintro ⟨⟨hSΛ, hγ⟩, hGS⟩
      exact ⟨⟨hSΛ, fun e he => incompatEdges_mono P hSΛ (hGS he)⟩, hγ,
        fun e he => incompatEdges_mem_of_mem P (hGS he)⟩
  rw [Finset.sum_congr rfl (fun S _ => by rw [Finset.mul_sum]),
    ← Finset.sum_finset_product' _ _ _ hchar]
  have hmaps : ∀ p ∈ (Λ.powerset ×ˢ (incompatEdges P Λ).powerset).filter
      (fun p => γ₀ ∈ p.1 ∧ ∀ e ∈ p.2, ∀ y ∈ e, y ∈ p.1),
      component p.2 γ₀ p.1 ∈ Λ.powerset.filter (fun B => γ₀ ∈ B) := by
    rintro ⟨S, G⟩ hp
    obtain ⟨hmem, hγ, -⟩ := Finset.mem_filter.mp hp
    rw [Finset.mem_product] at hmem
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr
        (component_subset.trans (Finset.mem_powerset.mp hmem.1)),
       self_mem_component hγ⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  exact Finset.sum_congr rfl fun B hB => by
    obtain ⟨hBpow, hγB⟩ := Finset.mem_filter.mp hB
    exact fiber_sum P w (Finset.mem_powerset.mp hBpow) hγB

/-! ## Das Brückenlemma: Tupel- und Mengenebene

Für ein injektives Polymer-Tupel `γ : Fin (n+1) → ι` stimmt die
Ursell-Funktion der Tupelebene (`ursellInt`) mit der mengenwertigen
Ursell-Vorzeichensumme (`ursellSetSum`) des Bildes überein:
`Sym2.map γ` liefert eine kardinalitäts- und damit
vorzeichenerhaltende Bijektion der beiden Summationsbereiche. -/

/-- Ein Weg im Graphen einer Kantenmenge überträgt sich entlang einer
injektiven Abbildung auf das Bild der Kantenmenge. -/
theorem walk_map {α β : Type*} [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) {G : Finset (Sym2 α)} :
    ∀ {u v : α}, (graphOf G).Walk u v →
      (graphOf (G.image (Sym2.map f))).Reachable (f u) (f v) := by
  intro u v p
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c hadj q ih =>
    obtain ⟨hmem, hne⟩ := graphOf_adj.mp hadj
    have himg : s(f a, f b) ∈ G.image (Sym2.map f) := by
      have h := Finset.mem_image_of_mem (Sym2.map f) hmem
      rwa [Sym2.map_mk] at h
    have hadj' : (graphOf (G.image (Sym2.map f))).Adj (f a) (f b) :=
      graphOf_adj.mpr ⟨himg, fun h => hne (hf h)⟩
    exact hadj'.reachable.trans ih

/-- Ein Weg zwischen Punkten einer kantenabgeschlossenen Menge `B` zieht
sich entlang einer Abbildung `f` mit Schnitt `g` (also `g ∘ f = id` auf
`B`) auf das Bild der Kantenmenge zurück. -/
theorem walk_pull {α β : Type*} [DecidableEq β] {g : β → α} {f : α → β}
    {B : Finset α} {G : Finset (Sym2 α)}
    (hin : ∀ e ∈ G, ∀ y ∈ e, y ∈ B) (hgf : ∀ x ∈ B, g (f x) = x) :
    ∀ {u v : α}, (graphOf G).Walk u v → u ∈ B →
      (graphOf (G.image (Sym2.map f))).Reachable (f u) (f v) := by
  intro u v p
  induction p with
  | nil => exact fun _ => SimpleGraph.Reachable.refl _
  | @cons a b c hadj q ih =>
    intro ha
    obtain ⟨hmem, hne⟩ := graphOf_adj.mp hadj
    have hb : b ∈ B := hin _ hmem b (Sym2.mem_mk_right a b)
    have himg : s(f a, f b) ∈ G.image (Sym2.map f) := by
      have h := Finset.mem_image_of_mem (Sym2.map f) hmem
      rwa [Sym2.map_mk] at h
    have hne' : f a ≠ f b := fun heq => hne (by rw [← hgf a ha, ← hgf b hb, heq])
    have hadj' : (graphOf (G.image (Sym2.map f))).Adj (f a) (f b) :=
      graphOf_adj.mpr ⟨himg, hne'⟩
    exact hadj'.reachable.trans (ih hb)

/-- **Brückenlemma zwischen Tupel- und Mengenebene**: für ein injektives
Polymer-Tupel `γ` stimmt die Ursell-Funktion `ursellInt P γ` mit der
mengenwertigen Ursell-Vorzeichensumme des Bildes überein. Der Beweis
transportiert die Summationsbereiche mit `G ↦ G.image (Sym2.map γ)`
(Rückrichtung entlang einer Inversen von `γ` auf dem Bild); die Bijektion
erhält Kardinalitäten und damit die Vorzeichen. -/
theorem ursellInt_eq_ursellSetSum {n : ℕ} {γ : Fin (n + 1) → ι}
    (hinj : Function.Injective γ) :
    (ursellInt P γ : ℤ) = ursellSetSum P (Finset.univ.image γ) := by
  set B : Finset ι := Finset.univ.image γ with hB
  obtain ⟨δ, hδγ⟩ : ∃ δ : ι → Fin (n + 1), ∀ i, δ (γ i) = i :=
    ⟨Function.invFun γ, fun i => Function.leftInverse_invFun hinj i⟩
  have hγδ : ∀ x ∈ B, γ (δ x) = x := by
    intro x hx
    rw [hB] at hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    rw [hδγ]
  have hmemB : ∀ i, γ i ∈ B := by
    intro i
    rw [hB]
    exact Finset.mem_image_of_mem γ (Finset.mem_univ i)
  have hcomp : ∀ e : Sym2 (Fin (n + 1)), Sym2.map δ (Sym2.map γ e) = e := by
    intro e
    induction e using Sym2.ind with
    | _ i j => rw [Sym2.map_mk, Sym2.map_mk, hδγ, hδγ]
  -- Kanten-Korrespondenz zwischen den beiden Trägern.
  have hedge : ∀ i j : Fin (n + 1),
      s(γ i, γ j) ∈ incompatEdges P B ↔ s(i, j) ∈ clusterEdges P γ := by
    intro i j
    rw [mem_incompatEdges, mem_clusterEdges]
    constructor
    · rintro ⟨-, -, hne, hinc⟩
      exact ⟨fun heq => hne (congrArg γ heq), hinc⟩
    · rintro ⟨hne, hinc⟩
      exact ⟨hmemB i, hmemB j, fun heq => hne (hinj heq), hinc⟩
  unfold ursellInt ursellSum ursellSetSum
  refine Finset.sum_nbij' (fun G => G.image (Sym2.map γ))
    (fun G' => G'.image (Sym2.map δ)) ?_ ?_ ?_ ?_ ?_
  -- Hinrichtung: das Bild eines zusammenhängenden Teilgraphen verbindet `B`.
  · intro G hG
    obtain ⟨hGpow, hGconn⟩ := Finset.mem_filter.mp hG
    have hGsub := Finset.mem_powerset.mp hGpow
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩
    · intro e he
      obtain ⟨e₀, he₀, rfl⟩ := Finset.mem_image.mp he
      revert he₀
      induction e₀ using Sym2.ind with
      | _ i j =>
        intro he₀
        rw [Sym2.map_mk]
        exact (hedge i j).mpr (hGsub he₀)
    · intro u hu v hv
      rw [hB] at hu hv
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨p⟩ := hGconn.preconnected i j
      exact walk_map hinj p
  -- Rückrichtung: das Urbild eines `B` verbindenden Graphen ist zusammenhängend.
  · intro G' hG'
    obtain ⟨hG'pow, hG'reach⟩ := Finset.mem_filter.mp hG'
    have hG'sub := Finset.mem_powerset.mp hG'pow
    have hin : ∀ e ∈ G', ∀ y ∈ e, y ∈ B :=
      fun e he => incompatEdges_mem_of_mem P (hG'sub he)
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩
    · intro e he
      obtain ⟨e₀, he₀, rfl⟩ := Finset.mem_image.mp he
      revert he₀
      induction e₀ using Sym2.ind with
      | _ u v =>
        intro he₀
        obtain ⟨huB, hvB, hne, hinc⟩ := (mem_incompatEdges P).mp (hG'sub he₀)
        rw [Sym2.map_mk]
        refine (mem_clusterEdges P).mpr ⟨?_, ?_⟩
        · intro heq
          exact hne (by rw [← hγδ u huB, ← hγδ v hvB, heq])
        · rw [hγδ u huB, hγδ v hvB]
          exact hinc
    · refine SimpleGraph.Connected.mk fun i j => ?_
      obtain ⟨p⟩ := hG'reach (γ i) (hmemB i) (γ j) (hmemB j)
      have h := walk_pull hin hγδ p (hmemB i)
      rwa [hδγ i, hδγ j] at h
  -- Linksinverse: `Sym2.map δ ∘ Sym2.map γ = id`.
  · intro G _
    show (G.image (Sym2.map γ)).image (Sym2.map δ) = G
    rw [Finset.image_image]
    exact (Finset.image_congr fun e _ => hcomp e).trans Finset.image_id
  -- Rechtsinverse: auf Kanten mit Endpunkten in `B` ist `γ ∘ δ = id`.
  · intro G' hG'
    have hG'sub := Finset.mem_powerset.mp (Finset.mem_filter.mp hG').1
    change (G'.image (Sym2.map δ)).image (Sym2.map γ) = G'
    rw [Finset.image_image]
    refine (Finset.image_congr ?_).trans Finset.image_id
    intro e he
    rw [Finset.mem_coe] at he
    revert he
    induction e using Sym2.ind with
    | _ u v =>
      intro he
      obtain ⟨huB, hvB, -, -⟩ := (mem_incompatEdges P).mp (hG'sub he)
      change Sym2.map γ (Sym2.map δ s(u, v)) = s(u, v)
      rw [Sym2.map_mk, Sym2.map_mk, hγδ u huB, hγδ v hvB]
  -- Werte: die Bijektion erhält die Kardinalität, also das Vorzeichen.
  · intro G _
    change ((-1 : ℤ)) ^ G.card = (-1 : ℤ) ^ (G.image (Sym2.map γ)).card
    rw [Finset.card_image_of_injective G (Function.LeftInverse.injective hcomp)]

/-! ## Cluster-Kollektionen und die Cluster-Faktorisierung -/

/-- Eine Cluster-Kollektion: eine endliche Menge paarweise disjunkter,
nichtleerer Cluster. -/
def IsClusterCollection (C : Finset (Finset ι)) : Prop :=
  (∀ B ∈ C, B.Nonempty) ∧ ∀ B₁ ∈ C, ∀ B₂ ∈ C, B₁ ≠ B₂ → Disjoint B₁ B₂

omit [DecidableEq ι] in
/-- Die Kollektionseigenschaft vererbt sich auf Teilkollektionen. -/
theorem IsClusterCollection.mono {C D : Finset (Finset ι)} (hCD : C ⊆ D)
    (hD : IsClusterCollection D) : IsClusterCollection C :=
  ⟨fun B hB => hD.1 B (hCD hB),
   fun B₁ h₁ B₂ h₂ hne => hD.2 B₁ (hCD h₁) B₂ (hCD h₂) hne⟩

/-- Einfügen eines nichtleeren, zu allen Blöcken disjunkten Blocks
erhält die Kollektionseigenschaft. -/
theorem isClusterCollection_insert {B₀ : Finset ι}
    {C : Finset (Finset ι)} (hB₀ : B₀.Nonempty) (hC : IsClusterCollection C)
    (hdisj : ∀ B ∈ C, Disjoint B₀ B) : IsClusterCollection (insert B₀ C) := by
  constructor
  · intro B hB
    rcases mem_insert.mp hB with rfl | hB'
    · exact hB₀
    · exact hC.1 B hB'
  · intro B₁ h₁ B₂ h₂ hne
    rcases mem_insert.mp h₁ with rfl | h₁' <;>
      rcases mem_insert.mp h₂ with rfl | h₂'
    · exact absurd rfl hne
    · exact hdisj B₂ h₂'
    · exact (hdisj B₁ h₁').symm
    · exact hC.2 B₁ h₁' B₂ h₂' hne

/-- In einer Cluster-Kollektion enthält höchstens ein Block ein festes
Polymer: der Filter nach `γ₀ ∈ B` ist ein Singleton. -/
theorem filter_mem_eq_singleton {C : Finset (Finset ι)} {γ₀ : ι}
    {B₀ : Finset ι} (hC : IsClusterCollection C) (hB₀ : B₀ ∈ C)
    (hγ : γ₀ ∈ B₀) : C.filter (fun B => γ₀ ∈ B) = {B₀} := by
  ext B
  rw [mem_filter, mem_singleton]
  constructor
  · rintro ⟨hBC, hγB⟩
    by_contra hne
    exact disjoint_left.mp (hC.2 B hBC B₀ hB₀ hne) hγB hγ
  · rintro rfl
    exact ⟨hB₀, hγ⟩

/-- Die Zustandssumme der leeren Polymermenge ist `1` — in jedem
kommutativen Ring. -/
private theorem Z_empty_comm {R : Type*} [CommRing R] (w : ι → R) :
    Z P w (∅ : Finset ι) = 1 := by
  have hind : Indep P (∅ : Finset ι) := fun γ hγ => absurd hγ (notMem_empty γ)
  simp [Z, filter_singleton, hind]

/-- Über der leeren Polymermenge überlebt nur die leere Kollektion:
`{∅}` verletzt die Nichtleerheit, und das leere Produkt ist `1`. -/
private theorem sum_clusterCollections_empty {R : Type*} [CommRing R]
    (w : ι → R) :
    ∑ C ∈ (∅ : Finset ι).powerset.powerset.filter IsClusterCollection,
      ∏ B ∈ C, ((∏ γ ∈ B, w γ) * ursellSetSum P B) = 1 := by
  have hyes : IsClusterCollection (∅ : Finset (Finset ι)) :=
    ⟨fun B hB => absurd hB (notMem_empty B),
     fun B₁ h₁ => absurd h₁ (notMem_empty B₁)⟩
  have hno : ¬ IsClusterCollection ({∅} : Finset (Finset ι)) :=
    fun h => not_nonempty_empty (h.1 ∅ (mem_singleton_self ∅))
  have hpp : ((∅ : Finset ι).powerset.powerset : Finset (Finset (Finset ι)))
      = {∅, {∅}} := by
    rw [powerset_empty]
    ext C
    rw [mem_powerset, subset_singleton_iff, mem_insert, mem_singleton]
  rw [hpp, filter_insert, if_pos hyes,
    filter_singleton, if_neg hno, insert_empty, sum_singleton, prod_empty]

/-- Kern der Induktion: die Cluster-Faktorisierung für alle `Λ` mit
`Λ.card ≤ n`, per starker Induktion über `n`. Der Schritt spaltet mit
`Z_cluster_recursion` nach dem `γ₀`-Block auf: Kollektionen ohne
`γ₀`-Block leben über `Λ ∖ {γ₀}`; Kollektionen mit (genau einem)
`γ₀`-Block `B₀` zerfallen bijektiv in `B₀` und eine Restkollektion
über `Λ ∖ B₀`. -/
private theorem Z_eq_sum_clusterCollections_aux {R : Type*} [CommRing R]
    (w : ι → R) :
    ∀ n : ℕ, ∀ Λ : Finset ι, Λ.card ≤ n →
      Z P w Λ = ∑ C ∈ Λ.powerset.powerset.filter IsClusterCollection,
        ∏ B ∈ C, ((∏ γ ∈ B, w γ) * ursellSetSum P B) := by
  intro n
  induction n with
  | zero =>
    intro Λ hcard
    have hΛ : Λ = ∅ := card_eq_zero.mp (Nat.le_zero.mp hcard)
    subst hΛ
    rw [Z_empty_comm, sum_clusterCollections_empty]
  | succ n IHn =>
    intro Λ hcard
    rcases Λ.eq_empty_or_nonempty with rfl | hne
    · rw [Z_empty_comm, sum_clusterCollections_empty]
    obtain ⟨γ₀, hγ₀⟩ := hne
    rw [Z_cluster_recursion P w Λ γ₀,
      ← sum_filter_add_sum_filter_not
        (Λ.powerset.powerset.filter IsClusterCollection)
        (fun C => ∀ B ∈ C, γ₀ ∉ B)]
    congr 1
    -- Teil (i): Kollektionen ohne `γ₀`-Block ↔ Kollektionen über `Λ ∖ {γ₀}`.
    · have hidx : (Λ.powerset.powerset.filter IsClusterCollection).filter
          (fun C => ∀ B ∈ C, γ₀ ∉ B)
          = (Λ.erase γ₀).powerset.powerset.filter IsClusterCollection := by
        ext C
        constructor
        · intro hC
          obtain ⟨hC', hno⟩ := mem_filter.mp hC
          obtain ⟨hCpp, hICC⟩ := mem_filter.mp hC'
          refine mem_filter.mpr
            ⟨mem_powerset.mpr fun B hB => mem_powerset.mpr ?_, hICC⟩
          exact subset_erase.mpr
            ⟨mem_powerset.mp (mem_powerset.mp hCpp hB), hno B hB⟩
        · intro hC
          obtain ⟨hCpp, hICC⟩ := mem_filter.mp hC
          have hsub : ∀ B ∈ C, B ⊆ Λ.erase γ₀ :=
            fun B hB => mem_powerset.mp (mem_powerset.mp hCpp hB)
          refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_powerset.mpr fun B hB =>
            mem_powerset.mpr ((hsub B hB).trans (erase_subset γ₀ Λ)), hICC⟩,
            fun B hB hγB => (mem_erase.mp (hsub B hB hγB)).1 rfl⟩
      rw [hidx]
      have hcard' : (Λ.erase γ₀).card ≤ n := by
        have h1 := card_erase_of_mem hγ₀
        omega
      exact IHn (Λ.erase γ₀) hcard'
    -- Teil (ii): Kollektionen mit `γ₀`-Block ↔ Paare (Block, Rest).
    · have hcard2 : ∀ B₀ ∈ Λ.powerset.filter (fun B => γ₀ ∈ B),
          (Λ \ B₀).card ≤ n := by
        intro B₀ hB₀
        obtain ⟨-, hγ⟩ := mem_filter.mp hB₀
        have hsub : Λ \ B₀ ⊆ Λ.erase γ₀ := by
          intro x hx
          obtain ⟨hxΛ, hxB⟩ := mem_sdiff.mp hx
          exact mem_erase.mpr ⟨fun h => hxB (h ▸ hγ), hxΛ⟩
        have h1 := card_le_card hsub
        have h2 := card_erase_of_mem hγ₀
        omega
      calc ∑ B₀ ∈ Λ.powerset.filter (fun B => γ₀ ∈ B),
            (∏ γ ∈ B₀, w γ) * ursellSetSum P B₀ * Z P w (Λ \ B₀)
          = ∑ B₀ ∈ Λ.powerset.filter (fun B => γ₀ ∈ B),
              ∑ C' ∈ (Λ \ B₀).powerset.powerset.filter IsClusterCollection,
                (∏ γ ∈ B₀, w γ) * ursellSetSum P B₀
                  * ∏ B ∈ C', ((∏ γ ∈ B, w γ) * ursellSetSum P B) := by
            refine sum_congr rfl fun B₀ hB₀ => ?_
            rw [IHn (Λ \ B₀) (hcard2 B₀ hB₀), mul_sum]
        _ = ∑ q ∈ (Λ.powerset.filter (fun B => γ₀ ∈ B)).sigma
              (fun B₀ =>
                (Λ \ B₀).powerset.powerset.filter IsClusterCollection),
              (∏ γ ∈ q.1, w γ) * ursellSetSum P q.1
                * ∏ B ∈ q.2, ((∏ γ ∈ B, w γ) * ursellSetSum P B) :=
            sum_sigma' _ _ _
        _ = ∑ C ∈ (Λ.powerset.powerset.filter IsClusterCollection).filter
              (fun C => ¬ ∀ B ∈ C, γ₀ ∉ B),
              ∏ B ∈ C, ((∏ γ ∈ B, w γ) * ursellSetSum P B) := by
            symm
            refine sum_nbij'
              (fun C => ⟨(C.filter (fun B => γ₀ ∈ B)).sup id,
                C.filter (fun B => γ₀ ∉ B)⟩)
              (fun q => insert q.1 q.2) ?_ ?_ ?_ ?_ ?_
            -- Hinrichtung: die Faser landet in der Sigma-Menge.
            · intro C hC
              obtain ⟨hC', hnot⟩ := mem_filter.mp hC
              obtain ⟨hCpp, hICC⟩ := mem_filter.mp hC'
              have hCpow : C ⊆ Λ.powerset := mem_powerset.mp hCpp
              push Not at hnot
              obtain ⟨B₀, hB₀C, hγB₀⟩ := hnot
              have hsup : (C.filter (fun B => γ₀ ∈ B)).sup id = B₀ := by
                rw [filter_mem_eq_singleton hICC hB₀C hγB₀, sup_singleton,
                  id_eq]
              refine mem_sigma.mpr ⟨?_, ?_⟩
              · dsimp only
                rw [hsup]
                exact mem_filter.mpr ⟨hCpow hB₀C, hγB₀⟩
              · dsimp only
                rw [hsup]
                refine mem_filter.mpr ⟨mem_powerset.mpr fun B hB => ?_,
                  hICC.mono (filter_subset _ _)⟩
                obtain ⟨hBC, hγnB⟩ := mem_filter.mp hB
                have hne : B ≠ B₀ := fun h => hγnB (h ▸ hγB₀)
                refine mem_powerset.mpr fun x hx => mem_sdiff.mpr
                  ⟨mem_powerset.mp (hCpow hBC) hx,
                   disjoint_left.mp (hICC.2 B hBC B₀ hB₀C hne) hx⟩
            -- Rückrichtung: `insert B₀ C'` liegt in der Faser.
            · rintro ⟨B₀, C'⟩ hq
              obtain ⟨hB₀, hC'⟩ := mem_sigma.mp hq
              obtain ⟨hB₀pow, hγB₀⟩ := mem_filter.mp hB₀
              have hB₀Λ : B₀ ⊆ Λ := mem_powerset.mp hB₀pow
              obtain ⟨hC'pp, hICC'⟩ := mem_filter.mp hC'
              have hC'sub : ∀ B ∈ C', B ⊆ Λ \ B₀ :=
                fun B hB => mem_powerset.mp (mem_powerset.mp hC'pp hB)
              have hdisj : ∀ B ∈ C', Disjoint B₀ B :=
                fun B hB => disjoint_right.mpr
                  fun x hx => (mem_sdiff.mp (hC'sub B hB hx)).2
              refine mem_filter.mpr
                ⟨mem_filter.mpr ⟨mem_powerset.mpr ?_, ?_⟩, ?_⟩
              · intro B hB
                rcases mem_insert.mp hB with rfl | hB'
                · exact mem_powerset.mpr hB₀Λ
                · exact mem_powerset.mpr ((hC'sub B hB').trans sdiff_subset)
              · exact isClusterCollection_insert ⟨γ₀, hγB₀⟩ hICC' hdisj
              · intro hall
                exact hall B₀ (mem_insert_self B₀ C') hγB₀
            -- Linksinverse: Wiederzusammensetzen liefert `C`.
            · intro C hC
              obtain ⟨hC', hnot⟩ := mem_filter.mp hC
              obtain ⟨-, hICC⟩ := mem_filter.mp hC'
              push Not at hnot
              obtain ⟨B₀, hB₀C, hγB₀⟩ := hnot
              have hfil : C.filter (fun B => γ₀ ∈ B) = {B₀} :=
                filter_mem_eq_singleton hICC hB₀C hγB₀
              dsimp only
              rw [hfil, sup_singleton, id_eq, ← singleton_union, ← hfil,
                filter_union_filter_not_eq]
            -- Rechtsinverse: Zerlegen von `insert B₀ C'` liefert `(B₀, C')`.
            · rintro ⟨B₀, C'⟩ hq
              obtain ⟨hB₀, hC'⟩ := mem_sigma.mp hq
              obtain ⟨-, hγB₀⟩ := mem_filter.mp hB₀
              obtain ⟨hC'pp, hICC'⟩ := mem_filter.mp hC'
              have hC'sub : ∀ B ∈ C', B ⊆ Λ \ B₀ :=
                fun B hB => mem_powerset.mp (mem_powerset.mp hC'pp hB)
              have hγnot : ∀ B ∈ C', γ₀ ∉ B :=
                fun B hB hγB => (mem_sdiff.mp (hC'sub B hB hγB)).2 hγB₀
              have hdisj : ∀ B ∈ C', Disjoint B₀ B :=
                fun B hB => disjoint_right.mpr
                  fun x hx => (mem_sdiff.mp (hC'sub B hB hx)).2
              have hICCins : IsClusterCollection (insert B₀ C') :=
                isClusterCollection_insert ⟨γ₀, hγB₀⟩ hICC' hdisj
              have h1 : ((insert B₀ C').filter (fun B => γ₀ ∈ B)).sup id
                  = B₀ := by
                rw [filter_mem_eq_singleton hICCins
                  (mem_insert_self B₀ C') hγB₀, sup_singleton, id_eq]
              have h2 : (insert B₀ C').filter (fun B => γ₀ ∉ B) = C' := by
                rw [filter_insert, if_neg (not_not_intro hγB₀),
                  filter_true_of_mem hγnot]
              dsimp only
              rw [h1, h2]
            -- Die Summanden stimmen überein: `Finset.prod_insert`.
            · intro C hC
              obtain ⟨hC', hnot⟩ := mem_filter.mp hC
              obtain ⟨-, hICC⟩ := mem_filter.mp hC'
              push Not at hnot
              obtain ⟨B₀, hB₀C, hγB₀⟩ := hnot
              have hfil : C.filter (fun B => γ₀ ∈ B) = {B₀} :=
                filter_mem_eq_singleton hICC hB₀C hγB₀
              have hnotmem : B₀ ∉ C.filter (fun B => γ₀ ∉ B) :=
                fun h => (mem_filter.mp h).2 hγB₀
              have hrepr : insert B₀ (C.filter (fun B => γ₀ ∉ B)) = C := by
                rw [← singleton_union, ← hfil, filter_union_filter_not_eq]
              dsimp only
              rw [hfil, sup_singleton, id_eq]
              conv_lhs => rw [← hrepr]
              rw [prod_insert hnotmem]

/-- **Cluster-Faktorisierung**: die Zustandssumme als Summe über
Kollektionen paarweise disjunkter, nichtleerer Cluster — die endliche
Exponentialformel in Mengenform. Jede Kollektion trägt das Produkt
ihrer Blockgewichte `(∏_{γ ∈ B} w γ) · φ(B)` bei. -/
theorem Z_eq_sum_clusterCollections {R : Type*} [CommRing R] (w : ι → R)
    (Λ : Finset ι) :
    Z P w Λ = ∑ C ∈ Λ.powerset.powerset.filter IsClusterCollection,
      ∏ B ∈ C, ((∏ γ ∈ B, w γ) * ursellSetSum P B) :=
  Z_eq_sum_clusterCollections_aux P w Λ.card Λ le_rfl

end ClusterExpansion
