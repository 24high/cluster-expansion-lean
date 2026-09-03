/-
Copyright (c) 2026 Dennis Michael Heine. All rights reserved.
Released under the CC BY-NC-SA 4.0 license as described in the file LICENSE.
Authors: Dennis Michael Heine
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Cluster-Entwicklung: Rekursion, Dobrushin- und Kotecký-Preiss-Kriterium

Abstraktes Polymersystem, Zustandssumme über unabhängige Polymermengen,
die Fundamentalrekursion `Z Λ = Z (Λ ∖ {γ}) + w γ * Z (Λ ohne N(γ))`
über beliebigen kommutativen Ringen, und vollständig bewiesen:

* das **Dobrushin-Kriterium** in Produktform: unter
  `|w γ| · ∏_{δ ≁ γ} (1 + μ δ) ≤ μ γ` gilt `Z ≠ 0` samt
  Quotientenschranke `|Z (Λ ∖ {γ})| ≤ (1 + μ γ) · |Z Λ|`;
* das klassische **Kotecký-Preiss-Kriterium** in Summenform: unter
  `∑_{δ ≁ γ} |w δ| · exp (a δ) ≤ a γ` gilt `Z ≠ 0` und
  `|Z (Λ ∖ {γ})| ≤ exp (a γ) · |Z Λ|` — per Bedingungsvergleich
  `μ γ = |w γ| · exp (a γ)` mit `1 + x ≤ exp x`;
* **volumenlineare Kontrolle des Logarithmus**:
  `|log |Z Λ|| ≤ ∑_{γ ∈ Λ} log (1 + μ γ) ≤ ∑_{γ ∈ Λ} μ γ`,
  aus zweiseitigen Schranken `(∏ (1 + μ))⁻¹ ≤ |Z Λ| ≤ ∏ (1 + μ)`;
* die **Fernández-Procacci-Bedingung** samt Hierarchie
  `KP ⟹ Dobrushin ⟹ FP`.

Kein `sorry` in dieser Datei. Bewusst offen (nur definiert bzw. genannt,
nichts Unbewiesenes behauptet): die Ursell-Reihe von `log Z` mit
Baumgraphen-Schranken und der FP-Konvergenzsatz.

Kontext: DEGRALBA §17.1, „Balaban als Lean-Blueprint“.
Referenzen: Kotecký–Preiss (Comm. Math. Phys. 103, 1986);
Friedli–Velenik, *Statistical Mechanics of Lattice Systems*, Kap. 5;
Scott–Sokal (J. Stat. Phys. 118, 2005); Fernández–Procacci
(Comm. Math. Phys. 274, 2007).
-/

open Finset

namespace ClusterExpansion

variable {ι : Type*} [DecidableEq ι]

/-- Ein abstraktes Polymersystem über `ι`: eine symmetrische, reflexive
Unverträglichkeitsrelation (`Bool`-wertig, damit alles entscheidbar ist). -/
structure PolymerSystem (ι : Type*) where
  /-- `incomp γ δ = true` heißt: die Polymere `γ` und `δ` sind unverträglich. -/
  incomp : ι → ι → Bool
  /-- Unverträglichkeit ist symmetrisch. -/
  symm : ∀ γ δ, incomp γ δ = incomp δ γ
  /-- Jedes Polymer ist mit sich selbst unverträglich. -/
  refl : ∀ γ, incomp γ γ = true

variable (P : PolymerSystem ι)

/-- `S` ist zulässig (unabhängig): paarweise verträglich. -/
def Indep (S : Finset ι) : Prop :=
  ∀ γ ∈ S, ∀ δ ∈ S, γ ≠ δ → P.incomp γ δ = false

instance (S : Finset ι) : Decidable (Indep P S) := by
  unfold Indep; infer_instance

/-- Unabhängigkeit vererbt sich auf Teilmengen. -/
theorem Indep.mono {S T : Finset ι} (hT : T ⊆ S) (hS : Indep P S) : Indep P T :=
  fun γ hγ δ hδ hne => hS γ (hT hγ) δ (hT hδ) hne

variable {R : Type*} [CommRing R] (w : ι → R)

/-- Zustandssumme des Polymersystems auf `Λ`: Summe über alle unabhängigen
`S ⊆ Λ` der Produkte der Gewichte (die leere Menge trägt `1` bei). -/
def Z (Λ : Finset ι) : R :=
  ∑ S ∈ Λ.powerset.filter (fun S => Indep P S), ∏ γ ∈ S, w γ

/-- Die mit `γ` verträglichen Polymere in `Λ` (ohne `γ` selbst):
`Λ` ohne die geschlossene Nachbarschaft von `γ`. -/
def compat (Λ : Finset ι) (γ : ι) : Finset ι :=
  (Λ.erase γ).filter (fun δ => P.incomp γ δ = false)

theorem compat_subset_erase (Λ : Finset ι) (γ : ι) :
    compat P Λ γ ⊆ Λ.erase γ := filter_subset _ _

theorem notMem_compat (Λ : Finset ι) (γ : ι) : γ ∉ compat P Λ γ := by
  intro h
  exact (mem_erase.mp (compat_subset_erase P Λ γ h)).1 rfl

/-- Kernlemma für den Bijektionsschritt: `insert γ T` ist genau dann
unabhängig, wenn `T` unabhängig ist — sofern `T ⊆ compat P Λ γ`. -/
theorem indep_insert_iff {Λ : Finset ι} {γ : ι} {T : Finset ι}
    (hT : T ⊆ compat P Λ γ) : Indep P (insert γ T) ↔ Indep P T := by
  constructor
  · exact fun h => h.mono P (subset_insert γ T)
  · intro h α hα β hβ hne
    rcases mem_insert.mp hα with rfl | hαT
    · rcases mem_insert.mp hβ with rfl | hβT
      · exact absurd rfl hne
      · exact (mem_filter.mp (hT hβT)).2
    · rcases mem_insert.mp hβ with rfl | hβT
      · rw [P.symm]
        exact (mem_filter.mp (hT hαT)).2
      · exact h α hαT β hβT hne

/-- **Fundamentalrekursion der Cluster-Entwicklung.**
Aufspalten der Zustandssumme nach „`γ ∈ S` oder nicht“: die `S` ohne `γ`
liefern `Z (Λ \ {γ})`; die `S` mit `γ` stehen via `S ↦ S \ {γ}` in Bijektion
zu den unabhängigen Teilmengen der mit `γ` verträglichen Polymere. -/
theorem Z_recursion (Λ : Finset ι) (γ : ι) (hγ : γ ∈ Λ) :
    Z P w Λ = Z P w (Λ.erase γ) + w γ * Z P w (compat P Λ γ) := by
  classical
  unfold Z
  rw [mul_sum,
    ← sum_filter_add_sum_filter_not (Λ.powerset.filter fun S => Indep P S)
      (fun S => γ ∈ S), add_comm]
  congr 1
  -- Teil 1: die `S` ohne `γ` sind genau die unabhängigen Teilmengen von `Λ \ {γ}`.
  · refine sum_congr ?_ fun _ _ => rfl
    ext S
    constructor
    · intro hS
      have h1 := mem_filter.mp hS
      have h2 := mem_filter.mp h1.1
      exact mem_filter.mpr
        ⟨mem_powerset.mpr (subset_erase.mpr ⟨mem_powerset.mp h2.1, h1.2⟩), h2.2⟩
    · intro hS
      have h1 := mem_filter.mp hS
      have h2 := subset_erase.mp (mem_powerset.mp h1.1)
      exact mem_filter.mpr
        ⟨mem_filter.mpr ⟨mem_powerset.mpr h2.1, h1.2⟩, h2.2⟩
  -- Teil 2: Bijektion `S ↦ S \ {γ}` gegen `T ↦ insert γ T`.
  · refine sum_bij' (fun S _ => S.erase γ) (fun T _ => insert γ T)
      ?_ ?_ ?_ ?_ ?_
    -- Bild von `i` liegt in der Zielmenge.
    · intro S hS
      have h1 := mem_filter.mp hS
      have h2 := mem_filter.mp h1.1
      have hsub := mem_powerset.mp h2.1
      refine mem_filter.mpr ⟨mem_powerset.mpr ?_, (h2.2).mono P (erase_subset γ S)⟩
      intro δ hδ
      have hδm := mem_erase.mp hδ
      refine mem_filter.mpr ⟨mem_erase.mpr ⟨hδm.1, hsub hδm.2⟩, ?_⟩
      rw [P.symm]
      exact h2.2 δ hδm.2 γ h1.2 hδm.1
    -- Bild von `j` liegt in der Startmenge.
    · intro T hT
      have h1 := mem_filter.mp hT
      have hsub := mem_powerset.mp h1.1
      have hins : insert γ T ⊆ Λ := by
        intro δ hδ
        rcases mem_insert.mp hδ with rfl | hδT
        · exact hγ
        · exact mem_of_mem_erase (compat_subset_erase P Λ γ (hsub hδT))
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_powerset.mpr hins,
        (indep_insert_iff P hsub).mpr h1.2⟩, mem_insert_self γ T⟩
    -- `j ∘ i = id`.
    · intro S hS
      exact insert_erase (mem_filter.mp hS).2
    -- `i ∘ j = id`.
    · intro T hT
      have h1 := mem_filter.mp hT
      exact erase_insert
        (fun hmem => notMem_compat P Λ γ ((mem_powerset.mp h1.1) hmem))
    -- Die Summanden stimmen überein.
    · intro S hS
      have hγS : γ ∈ S := (mem_filter.mp hS).2
      conv_lhs => rw [← insert_erase hγS]
      exact prod_insert (notMem_erase γ S)

section Dobrushin
/-!
## Das Dobrushin-Kriterium, vollständig bewiesen

Ab hier reelle Gewichte. Bewiesen wird das Konvergenzkriterium in
Produktform (Dobrushin; vgl. Scott–Sokal): Existiert `μ ≥ 0` mit
`|w γ| · ∏_{δ ≁ γ} (1 + μ δ) ≤ μ γ` für alle `γ ∈ Λ`, so ist `Z Λ ≠ 0`,
und Entfernen eines Polymers ändert `|Z|` höchstens um den Faktor
`1 + μ γ`. Der Beweis ist die Ratio-Teleskop-Induktion über `Λ.card`
mittels `Z_recursion`.

Aus der Produktform folgen anschließend die zweiseitigen Schranken an
`|Z|` und die Logarithmus-Kontrolle; im nächsten Abschnitt liefert der
Bedingungsvergleich daraus auch die klassische Summenform.
-/

variable (wr : ι → ℝ) (μ : ι → ℝ)

/-- Dobrushin-Bedingung (Produktform) auf `Λ`: `μ ≥ 0` und für jedes
`γ ∈ Λ` gilt `|w γ| · ∏_{δ ∈ Λ, δ ≁ γ} (1 + μ δ) ≤ μ γ`; das Produkt
läuft über die geschlossene Unverträglichkeits-Nachbarschaft von `γ`. -/
def DobrushinCondition (Λ : Finset ι) : Prop :=
  (∀ γ ∈ Λ, 0 ≤ μ γ) ∧
  ∀ γ ∈ Λ,
    |wr γ| * ∏ δ ∈ Λ.filter (fun δ => P.incomp γ δ = true), (1 + μ δ) ≤ μ γ

private theorem one_le_prod_one_add :
    ∀ s : Finset ι, (∀ δ ∈ s, 0 ≤ μ δ) → (1:ℝ) ≤ ∏ δ ∈ s, (1 + μ δ) := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | @insert δ s hδs IH =>
    intro hpos
    rw [prod_insert hδs]
    have h1 : (1:ℝ) ≤ 1 + μ δ := by
      have := hpos δ (mem_insert_self δ s); linarith
    have h2 : (1:ℝ) ≤ ∏ x ∈ s, (1 + μ x) :=
      IH fun x hx => hpos x (mem_insert_of_mem hx)
    nlinarith

/-- Die Dobrushin-Bedingung vererbt sich auf Teilmengen: die Produkte
verlieren nur Faktoren `≥ 1`. -/
theorem DobrushinCondition.mono {Λ' Λ : Finset ι} (hsub : Λ' ⊆ Λ)
    (h : DobrushinCondition P wr μ Λ) : DobrushinCondition P wr μ Λ' := by
  obtain ⟨hpos, hbd⟩ := h
  refine ⟨fun γ hγ => hpos γ (hsub hγ), fun γ hγ => ?_⟩
  have hfsub : Λ'.filter (fun δ => P.incomp γ δ = true)
      ⊆ Λ.filter (fun δ => P.incomp γ δ = true) :=
    filter_subset_filter _ hsub
  have hprodle : ∏ δ ∈ Λ'.filter (fun δ => P.incomp γ δ = true), (1 + μ δ)
      ≤ ∏ δ ∈ Λ.filter (fun δ => P.incomp γ δ = true), (1 + μ δ) := by
    rw [← prod_sdiff hfsub]
    have hone : (1:ℝ) ≤ ∏ δ ∈ (Λ.filter (fun δ => P.incomp γ δ = true))
        \ (Λ'.filter (fun δ => P.incomp γ δ = true)), (1 + μ δ) :=
      one_le_prod_one_add μ _
        (fun δ hδ => hpos δ (mem_filter.mp (mem_sdiff.mp hδ).1).1)
    have hpr : (1:ℝ) ≤ ∏ δ ∈ Λ'.filter (fun δ => P.incomp γ δ = true), (1 + μ δ) :=
      one_le_prod_one_add μ _
        (fun δ hδ => hpos δ (hsub (mem_filter.mp hδ).1))
    nlinarith
  calc |wr γ| * ∏ δ ∈ Λ'.filter (fun δ => P.incomp γ δ = true), (1 + μ δ)
      ≤ |wr γ| * ∏ δ ∈ Λ.filter (fun δ => P.incomp γ δ = true), (1 + μ δ) :=
        mul_le_mul_of_nonneg_left hprodle (abs_nonneg _)
    _ ≤ μ γ := hbd γ (hsub hγ)

@[simp] theorem Z_empty : Z P wr (∅ : Finset ι) = 1 := by
  have hind : Indep P (∅ : Finset ι) := fun γ hγ => absurd hγ (notMem_empty γ)
  simp [Z, filter_singleton, hind]

/-- Kern der Induktion: unter der Dobrushin-Bedingung ist die
Zustandssumme nichtnull, und für jedes `γ ∈ Λ` gilt
`|Z (Λ ∖ {γ})| ≤ (1 + μ γ) · |Z Λ|`. Beweis: starke Induktion über die
Kardinalität; die Quotienten werden entlang der Nachbarschaft von `γ`
teleskopiert und mit `Z_recursion` geschlossen. -/
theorem dobrushin_aux :
    ∀ n : ℕ, ∀ Λ : Finset ι, Λ.card ≤ n → DobrushinCondition P wr μ Λ →
      Z P wr Λ ≠ 0 ∧
      ∀ γ ∈ Λ, |Z P wr (Λ.erase γ)| ≤ (1 + μ γ) * |Z P wr Λ| := by
  intro n
  induction n with
  | zero =>
    intro Λ hcard _
    have hΛ : Λ = ∅ := card_eq_zero.mp (Nat.le_zero.mp hcard)
    subst hΛ
    exact ⟨by rw [Z_empty]; exact one_ne_zero,
      fun γ hγ => absurd hγ (notMem_empty γ)⟩
  | succ n IHn =>
    intro Λ hcard h
    rcases Λ.eq_empty_or_nonempty with rfl | hne
    · exact ⟨by rw [Z_empty]; exact one_ne_zero,
        fun γ hγ => absurd hγ (notMem_empty γ)⟩
    -- Teleskop: Entfernen einer Menge E kostet höchstens den Faktor
    -- ∏_{δ ∈ E} (1 + μ δ).
    have telescope : ∀ E S : Finset ι, E ⊆ S → S ⊆ Λ → S.card ≤ n →
        |Z P wr (S \ E)| ≤ (∏ δ ∈ E, (1 + μ δ)) * |Z P wr S| := by
      intro E
      induction E using Finset.induction_on with
      | empty => intro S _ _ _; simp
      | @insert δ E' hδE' IHe =>
        intro S hES hSΛ hScard
        have hδS : δ ∈ S := hES (mem_insert_self δ E')
        have hE'S : E' ⊆ S := fun x hx => hES (mem_insert_of_mem hx)
        have hset : S \ insert δ E' = (S \ E').erase δ := by
          ext x
          simp only [mem_sdiff, mem_erase, mem_insert]
          tauto
        have hδSE' : δ ∈ S \ E' := mem_sdiff.mpr ⟨hδS, hδE'⟩
        have hsub' : S \ E' ⊆ S := sdiff_subset
        have hcard' : (S \ E').card ≤ n := le_trans (card_le_card hsub') hScard
        have hDC' : DobrushinCondition P wr μ (S \ E') :=
          h.mono P wr μ (hsub'.trans hSΛ)
        have hratio := (IHn (S \ E') hcard' hDC').2 δ hδSE'
        have hμδ : 0 ≤ μ δ := h.1 δ (hSΛ hδS)
        calc |Z P wr (S \ insert δ E')|
            = |Z P wr ((S \ E').erase δ)| := by rw [hset]
          _ ≤ (1 + μ δ) * |Z P wr (S \ E')| := hratio
          _ ≤ (1 + μ δ) * ((∏ δ' ∈ E', (1 + μ δ')) * |Z P wr S|) := by
              apply mul_le_mul_of_nonneg_left (IHe S hE'S hSΛ hScard)
              linarith
          _ = (∏ δ' ∈ insert δ E', (1 + μ δ')) * |Z P wr S| := by
              rw [prod_insert hδE']; ring
    -- Quotientenschranke für jedes γ ∈ Λ, ganz ohne Division.
    have hratio : ∀ γ ∈ Λ, |Z P wr (Λ.erase γ)| ≤ (1 + μ γ) * |Z P wr Λ| := by
      intro γ hγ
      have herasecard : (Λ.erase γ).card ≤ n := by
        have h1 := card_erase_of_mem hγ
        omega
      have hcompat : (Λ.erase γ)
          \ ((Λ.erase γ).filter (fun δ => P.incomp γ δ = true))
          = compat P Λ γ := by
        rw [← filter_not]
        simp only [compat, Bool.not_eq_true]
      have htel := telescope ((Λ.erase γ).filter (fun δ => P.incomp γ δ = true))
        (Λ.erase γ) (filter_subset _ _) (erase_subset γ Λ) herasecard
      rw [hcompat] at htel
      -- Nachbarschaft in Λ = {γ} ∪ (Nachbarn in Λ ∖ {γ}).
      have hsplit : Λ.filter (fun δ => P.incomp γ δ = true)
          = insert γ ((Λ.erase γ).filter (fun δ => P.incomp γ δ = true)) := by
        ext δ
        simp only [mem_filter, mem_insert, mem_erase]
        constructor
        · rintro ⟨hδΛ, hinc⟩
          by_cases hδγ : δ = γ
          · exact Or.inl hδγ
          · exact Or.inr ⟨⟨hδγ, hδΛ⟩, hinc⟩
        · rintro (hδγ | ⟨⟨_, hδΛ⟩, hinc⟩)
          · rw [hδγ]; exact ⟨hγ, P.refl γ⟩
          · exact ⟨hδΛ, hinc⟩
      have hγD : γ ∉ (Λ.erase γ).filter (fun δ => P.incomp γ δ = true) :=
        fun hm => (mem_erase.mp ((filter_subset _ _) hm)).1 rfl
      have hDC := h.2 γ hγ
      rw [hsplit, prod_insert hγD] at hDC
      -- Rekursion und Dreiecksungleichung.
      have hrec := Z_recursion P wr Λ γ hγ
      have habs : |Z P wr (Λ.erase γ)|
          ≤ |Z P wr Λ| + |wr γ| * |Z P wr (compat P Λ γ)| := by
        have hz : Z P wr (Λ.erase γ)
            = Z P wr Λ - wr γ * Z P wr (compat P Λ γ) := by
          rw [hrec]; ring
        calc |Z P wr (Λ.erase γ)|
            = |Z P wr Λ - wr γ * Z P wr (compat P Λ γ)| := by rw [hz]
          _ ≤ |Z P wr Λ| + |wr γ * Z P wr (compat P Λ γ)| := by
              have := abs_add_le (Z P wr Λ)
                (-(wr γ * Z P wr (compat P Λ γ)))
              simpa [sub_eq_add_neg, abs_neg] using this
          _ = |Z P wr Λ| + |wr γ| * |Z P wr (compat P Λ γ)| := by
              rw [abs_mul]
      -- Arithmetischer Abschluss.
      have hprodpos : (0:ℝ) ≤ ∏ δ ∈ (Λ.erase γ).filter
          (fun δ => P.incomp γ δ = true), (1 + μ δ) :=
        le_trans zero_le_one (one_le_prod_one_add μ _
          (fun δ hδ => h.1 δ (mem_of_mem_erase ((filter_subset _ _) hδ))))
      have hkey1 : |Z P wr (Λ.erase γ)| ≤ |Z P wr Λ| +
          (|wr γ| * ∏ δ ∈ (Λ.erase γ).filter
            (fun δ => P.incomp γ δ = true), (1 + μ δ)) * |Z P wr (Λ.erase γ)| := by
        have hstep : |wr γ| * |Z P wr (compat P Λ γ)| ≤
            (|wr γ| * ∏ δ ∈ (Λ.erase γ).filter
              (fun δ => P.incomp γ δ = true), (1 + μ δ)) * |Z P wr (Λ.erase γ)| := by
          calc |wr γ| * |Z P wr (compat P Λ γ)|
              ≤ |wr γ| * ((∏ δ ∈ (Λ.erase γ).filter
                  (fun δ => P.incomp γ δ = true), (1 + μ δ)) * |Z P wr (Λ.erase γ)|) :=
                mul_le_mul_of_nonneg_left htel (abs_nonneg _)
            _ = (|wr γ| * ∏ δ ∈ (Λ.erase γ).filter
                  (fun δ => P.incomp γ δ = true), (1 + μ δ)) * |Z P wr (Λ.erase γ)| := by
                ring
        linarith [habs, hstep]
      have hkey2 : (|wr γ| * ∏ δ ∈ (Λ.erase γ).filter
          (fun δ => P.incomp γ δ = true), (1 + μ δ)) * (1 + μ γ) ≤ μ γ := by
        calc (|wr γ| * ∏ δ ∈ (Λ.erase γ).filter
              (fun δ => P.incomp γ δ = true), (1 + μ δ)) * (1 + μ γ)
            = |wr γ| * ((1 + μ γ) * ∏ δ ∈ (Λ.erase γ).filter
              (fun δ => P.incomp γ δ = true), (1 + μ δ)) := by ring
          _ ≤ μ γ := hDC
      have hμγ : 0 ≤ μ γ := h.1 γ hγ
      have h1m : (0:ℝ) ≤ 1 + μ γ := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hkey1 h1m,
        mul_le_mul_of_nonneg_right hkey2 (abs_nonneg (Z P wr (Λ.erase γ))),
        abs_nonneg (Z P wr Λ), abs_nonneg (Z P wr (Λ.erase γ)),
        mul_nonneg (mul_nonneg (abs_nonneg (wr γ)) hprodpos)
          (abs_nonneg (Z P wr (Λ.erase γ)))]
    -- Nichtnull über ein beliebiges γ₀ ∈ Λ.
    obtain ⟨γ0, hγ0⟩ := hne
    have herasecard0 : (Λ.erase γ0).card ≤ n := by
      have h1 := card_erase_of_mem hγ0
      omega
    have h0 : Z P wr (Λ.erase γ0) ≠ 0 :=
      (IHn (Λ.erase γ0) herasecard0 (h.mono P wr μ (erase_subset γ0 Λ))).1
    have hb : 0 < |Z P wr (Λ.erase γ0)| := abs_pos.mpr h0
    have hAne : Z P wr Λ ≠ 0 := by
      intro hz
      have hr0 := hratio γ0 hγ0
      rw [hz] at hr0
      simp only [abs_zero, mul_zero] at hr0
      linarith
    exact ⟨hAne, hratio⟩

/-- **Dobrushin-Kriterium, Teil 1:** unter der Produktbedingung
verschwindet die Zustandssumme nicht. -/
theorem Z_ne_zero_of_dobrushin (Λ : Finset ι)
    (h : DobrushinCondition P wr μ Λ) : Z P wr Λ ≠ 0 :=
  (dobrushin_aux P wr μ Λ.card Λ le_rfl h).1

/-- **Dobrushin-Kriterium, Teil 2:** Entfernen eines Polymers ändert die
Zustandssumme höchstens um den Faktor `1 + μ γ`. -/
theorem Z_ratio_bound_of_dobrushin (Λ : Finset ι)
    (h : DobrushinCondition P wr μ Λ) (γ : ι) (hγ : γ ∈ Λ) :
    |Z P wr (Λ.erase γ)| ≤ (1 + μ γ) * |Z P wr Λ| :=
  (dobrushin_aux P wr μ Λ.card Λ le_rfl h).2 γ hγ

/-- Teleskopierte Quotientenschranke: Entfernen einer ganzen Teilmenge
`E ⊆ Λ` ändert `|Z|` höchstens um den Faktor `∏_{δ ∈ E} (1 + μ δ)`. -/
theorem Z_sdiff_bound_of_dobrushin (Λ : Finset ι)
    (h : DobrushinCondition P wr μ Λ) :
    ∀ E : Finset ι, E ⊆ Λ →
      |Z P wr (Λ \ E)| ≤ (∏ δ ∈ E, (1 + μ δ)) * |Z P wr Λ| := by
  intro E
  induction E using Finset.induction_on with
  | empty => intro _; simp
  | @insert δ E' hδE' IH =>
    intro hE
    have hδΛ : δ ∈ Λ := hE (mem_insert_self δ E')
    have hE'Λ : E' ⊆ Λ := fun x hx => hE (mem_insert_of_mem hx)
    have hset : Λ \ insert δ E' = (Λ \ E').erase δ := by
      ext x
      simp only [mem_sdiff, mem_erase, mem_insert]
      tauto
    have hδmem : δ ∈ Λ \ E' := mem_sdiff.mpr ⟨hδΛ, hδE'⟩
    have hDC' : DobrushinCondition P wr μ (Λ \ E') :=
      h.mono P wr μ sdiff_subset
    have hratio := Z_ratio_bound_of_dobrushin P wr μ (Λ \ E') hDC' δ hδmem
    have hμδ : 0 ≤ μ δ := h.1 δ hδΛ
    calc |Z P wr (Λ \ insert δ E')|
        = |Z P wr ((Λ \ E').erase δ)| := by rw [hset]
      _ ≤ (1 + μ δ) * |Z P wr (Λ \ E')| := hratio
      _ ≤ (1 + μ δ) * ((∏ δ' ∈ E', (1 + μ δ')) * |Z P wr Λ|) := by
          apply mul_le_mul_of_nonneg_left (IH hE'Λ)
          linarith
      _ = (∏ δ' ∈ insert δ E', (1 + μ δ')) * |Z P wr Λ| := by
          rw [prod_insert hδE']; ring

/-- Untere Schranke: `(∏_{γ ∈ Λ} (1 + μ γ))⁻¹ ≤ |Z Λ|`.
Teleskop mit `E = Λ` und `Z ∅ = 1`. -/
theorem prod_inv_le_abs_Z_of_dobrushin (Λ : Finset ι)
    (h : DobrushinCondition P wr μ Λ) :
    (∏ γ ∈ Λ, (1 + μ γ))⁻¹ ≤ |Z P wr Λ| := by
  have htel := Z_sdiff_bound_of_dobrushin P wr μ Λ h Λ (Finset.Subset.refl Λ)
  rw [sdiff_self, bot_eq_empty, Z_empty] at htel
  have hP : (0:ℝ) < ∏ γ ∈ Λ, (1 + μ γ) :=
    lt_of_lt_of_le one_pos (one_le_prod_one_add μ Λ h.1)
  have h1 : (1:ℝ) ≤ (∏ γ ∈ Λ, (1 + μ γ)) * |Z P wr Λ| := by
    simpa using htel
  have h2 := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hP.le)
  rwa [mul_one, ← mul_assoc, inv_mul_cancel₀ hP.ne', one_mul] at h2

private theorem abs_Z_le_prod_aux :
    ∀ n : ℕ, ∀ Λ : Finset ι, Λ.card ≤ n → DobrushinCondition P wr μ Λ →
      |Z P wr Λ| ≤ ∏ γ ∈ Λ, (1 + μ γ) := by
  intro n
  induction n with
  | zero =>
    intro Λ hcard _
    have hΛ : Λ = ∅ := card_eq_zero.mp (Nat.le_zero.mp hcard)
    subst hΛ
    simp
  | succ n IHn =>
    intro Λ hcard h
    rcases Λ.eq_empty_or_nonempty with rfl | hne
    · simp
    obtain ⟨γ, hγ⟩ := hne
    have herasecard : (Λ.erase γ).card ≤ n := by
      have h1 := card_erase_of_mem hγ
      omega
    have hDCe : DobrushinCondition P wr μ (Λ.erase γ) :=
      h.mono P wr μ (erase_subset γ Λ)
    have hcompat : (Λ.erase γ)
        \ ((Λ.erase γ).filter (fun δ => P.incomp γ δ = true))
        = compat P Λ γ := by
      rw [← filter_not]
      simp only [compat, Bool.not_eq_true]
    have htel := Z_sdiff_bound_of_dobrushin P wr μ (Λ.erase γ) hDCe
      ((Λ.erase γ).filter (fun δ => P.incomp γ δ = true)) (filter_subset _ _)
    rw [hcompat] at htel
    have hsplit : Λ.filter (fun δ => P.incomp γ δ = true)
        = insert γ ((Λ.erase γ).filter (fun δ => P.incomp γ δ = true)) := by
      ext δ
      simp only [mem_filter, mem_insert, mem_erase]
      constructor
      · rintro ⟨hδΛ, hinc⟩
        by_cases hδγ : δ = γ
        · exact Or.inl hδγ
        · exact Or.inr ⟨⟨hδγ, hδΛ⟩, hinc⟩
      · rintro (hδγ | ⟨⟨_, hδΛ⟩, hinc⟩)
        · rw [hδγ]; exact ⟨hγ, P.refl γ⟩
        · exact ⟨hδΛ, hinc⟩
    have hγD : γ ∉ (Λ.erase γ).filter (fun δ => P.incomp γ δ = true) :=
      fun hm => (mem_erase.mp ((filter_subset _ _) hm)).1 rfl
    have hDC := h.2 γ hγ
    rw [hsplit, prod_insert hγD] at hDC
    have hμγ : 0 ≤ μ γ := h.1 γ hγ
    have hPDone : (1:ℝ) ≤ ∏ δ ∈ (Λ.erase γ).filter
        (fun δ => P.incomp γ δ = true), (1 + μ δ) :=
      one_le_prod_one_add μ _
        (fun δ hδ => h.1 δ (mem_of_mem_erase ((filter_subset _ _) hδ)))
    have hkey : |wr γ| * ∏ δ ∈ (Λ.erase γ).filter
        (fun δ => P.incomp γ δ = true), (1 + μ δ) ≤ μ γ := by
      nlinarith [mul_nonneg (mul_nonneg (abs_nonneg (wr γ)) hμγ)
        (le_trans zero_le_one hPDone), abs_nonneg (wr γ)]
    have hrec := Z_recursion P wr Λ γ hγ
    have habs : |Z P wr Λ|
        ≤ |Z P wr (Λ.erase γ)| + |wr γ| * |Z P wr (compat P Λ γ)| := by
      rw [hrec]
      calc |Z P wr (Λ.erase γ) + wr γ * Z P wr (compat P Λ γ)|
          ≤ |Z P wr (Λ.erase γ)| + |wr γ * Z P wr (compat P Λ γ)| :=
            abs_add_le _ _
        _ = |Z P wr (Λ.erase γ)| + |wr γ| * |Z P wr (compat P Λ γ)| := by
            rw [abs_mul]
    have hcompat_le : |wr γ| * |Z P wr (compat P Λ γ)|
        ≤ μ γ * |Z P wr (Λ.erase γ)| := by
      calc |wr γ| * |Z P wr (compat P Λ γ)|
          ≤ |wr γ| * ((∏ δ ∈ (Λ.erase γ).filter
              (fun δ => P.incomp γ δ = true), (1 + μ δ)) * |Z P wr (Λ.erase γ)|) :=
            mul_le_mul_of_nonneg_left htel (abs_nonneg _)
        _ = (|wr γ| * ∏ δ ∈ (Λ.erase γ).filter
              (fun δ => P.incomp γ δ = true), (1 + μ δ)) * |Z P wr (Λ.erase γ)| := by
            ring
        _ ≤ μ γ * |Z P wr (Λ.erase γ)| :=
            mul_le_mul_of_nonneg_right hkey (abs_nonneg _)
    have hIH := IHn (Λ.erase γ) herasecard hDCe
    have hexpand : (1 + μ γ) * |Z P wr (Λ.erase γ)|
        = |Z P wr (Λ.erase γ)| + μ γ * |Z P wr (Λ.erase γ)| := by ring
    have hfinal : |Z P wr Λ| ≤ (1 + μ γ) * |Z P wr (Λ.erase γ)| := by
      rw [hexpand]
      linarith
    calc |Z P wr Λ|
        ≤ (1 + μ γ) * |Z P wr (Λ.erase γ)| := hfinal
      _ ≤ (1 + μ γ) * ∏ δ ∈ Λ.erase γ, (1 + μ δ) := by
          apply mul_le_mul_of_nonneg_left hIH
          linarith
      _ = ∏ δ ∈ Λ, (1 + μ δ) := mul_prod_erase Λ (fun δ => 1 + μ δ) hγ

/-- Obere Schranke: `|Z Λ| ≤ ∏_{γ ∈ Λ} (1 + μ γ)` unter der
Dobrushin-Bedingung. -/
theorem abs_Z_le_prod_of_dobrushin (Λ : Finset ι)
    (h : DobrushinCondition P wr μ Λ) :
    |Z P wr Λ| ≤ ∏ γ ∈ Λ, (1 + μ γ) :=
  abs_Z_le_prod_aux P wr μ Λ.card Λ le_rfl h

private theorem log_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    Real.log x ≤ Real.log y := by
  rw [← Real.exp_le_exp, Real.exp_log hx, Real.exp_log (lt_of_lt_of_le hx hxy)]
  exact hxy

/-- **Volumenlineare Kontrolle des Logarithmus der Zustandssumme:**
unter der Dobrushin-Bedingung gilt
`|log |Z Λ|| ≤ ∑_{γ ∈ Λ} log (1 + μ γ)` — obere und untere Schranke an
`|Z|` in einem. Das ist der Konvergenzgehalt der Cluster-Entwicklung auf
Schrankenniveau: `log |Z|` wächst höchstens linear im Volumen,
gleichmäßig unter der Bedingung. -/
theorem abs_log_abs_Z_le_of_dobrushin (Λ : Finset ι)
    (h : DobrushinCondition P wr μ Λ) :
    |Real.log (|Z P wr Λ|)| ≤ ∑ γ ∈ Λ, Real.log (1 + μ γ) := by
  have hZpos : 0 < |Z P wr Λ| :=
    abs_pos.mpr (Z_ne_zero_of_dobrushin P wr μ Λ h)
  have hPpos : (0:ℝ) < ∏ γ ∈ Λ, (1 + μ γ) :=
    lt_of_lt_of_le one_pos (one_le_prod_one_add μ Λ h.1)
  have hlogprod : Real.log (∏ γ ∈ Λ, (1 + μ γ))
      = ∑ γ ∈ Λ, Real.log (1 + μ γ) :=
    Real.log_prod (fun γ hγ => by
      have hμ := h.1 γ hγ
      have hpos : (0:ℝ) < 1 + μ γ := by linarith
      exact hpos.ne')
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have hlow := prod_inv_le_abs_Z_of_dobrushin P wr μ Λ h
    have hlog := log_mono (inv_pos.mpr hPpos) hlow
    rw [Real.log_inv, hlogprod] at hlog
    exact hlog
  · have hup := abs_Z_le_prod_of_dobrushin P wr μ Λ h
    have hlog := log_mono hZpos hup
    rw [hlogprod] at hlog
    exact hlog

/-- Additive Fassung: `|log |Z Λ|| ≤ ∑_{γ ∈ Λ} μ γ`
(mittels `log (1 + x) ≤ x`). -/
theorem abs_log_abs_Z_le_sum_of_dobrushin (Λ : Finset ι)
    (h : DobrushinCondition P wr μ Λ) :
    |Real.log (|Z P wr Λ|)| ≤ ∑ γ ∈ Λ, μ γ := by
  refine le_trans (abs_log_abs_Z_le_of_dobrushin P wr μ Λ h)
    (Finset.sum_le_sum fun γ hγ => ?_)
  have hμ := h.1 γ hγ
  have hpos : (0:ℝ) < 1 + μ γ := by linarith
  have := Real.log_le_sub_one_of_pos hpos
  linarith

end Dobrushin

section KoteckyPreiss
/-!
## Die klassische Summenform, bewiesen per Bedingungsvergleich

Eine frühere Fassung dieser Datei behauptete, die Summenform sei aus der
Produktform nicht zu gewinnen. Das war zu kurz gedacht: mit
`μ γ = |w γ| · exp (a γ)` und `1 + x ≤ exp x` impliziert die
KP-Bedingung die Dobrushin-Bedingung (`KPCondition.dobrushin`), und
Nichtverschwinden samt klassischer Quotientenschranke `exp (a γ)` folgen
als Korollare. Der umgekehrte Weg scheitert wirklich: die Produktform
ist echt allgemeiner (Beispiel: ein selbst-unverträgliches Polymer mit
`|w| = 1/2` erfüllt Dobrushin mit `μ = 1`, aber `e^a/2 ≤ a` hat keine
Lösung). Offen bleibt die Ursell-Reihe von `log Z`; sie braucht die
Baumgraphen-Induktion und mehr als Schranken.
-/

variable (wr : ι → ℝ) (a : ι → ℝ)

/-- Kotecký-Preiss-Bedingung (Summenform) auf `Λ`:
`∑_{δ ≁ γ} |w δ| · exp (a δ) ≤ a γ` für alle `γ ∈ Λ`, mit `a ≥ 0`. -/
def KPCondition (Λ : Finset ι) : Prop :=
  (∀ γ ∈ Λ, 0 ≤ a γ) ∧
  ∀ γ ∈ Λ,
    ∑ δ ∈ Λ.filter (fun δ => P.incomp γ δ = true), |wr δ| * Real.exp (a δ) ≤ a γ

omit [DecidableEq ι] in
/-- **Vergleich der Bedingungen:** die Kotecký-Preiss-Summenbedingung
impliziert die Dobrushin-Produktbedingung mit `μ γ := |w γ| · exp (a γ)`.
Kernungleichung ist `1 + x ≤ exp x`; vgl. Fernández–Procacci
(Comm. Math. Phys. 274, 2007) und Scott–Sokal. -/
theorem KPCondition.dobrushin {Λ : Finset ι} (h : KPCondition P wr a Λ) :
    DobrushinCondition P wr (fun γ => |wr γ| * Real.exp (a γ)) Λ := by
  obtain ⟨hpos, hsum⟩ := h
  refine ⟨fun γ _ => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le,
    fun γ hγ => ?_⟩
  change |wr γ| * ∏ δ ∈ Λ.filter (fun δ => P.incomp γ δ = true),
      (1 + |wr δ| * Real.exp (a δ)) ≤ |wr γ| * Real.exp (a γ)
  have hprod_le : ∏ δ ∈ Λ.filter (fun δ => P.incomp γ δ = true),
      (1 + |wr δ| * Real.exp (a δ))
      ≤ Real.exp (∑ δ ∈ Λ.filter (fun δ => P.incomp γ δ = true),
          |wr δ| * Real.exp (a δ)) := by
    rw [Real.exp_sum]
    refine Finset.prod_le_prod (fun δ _ => by positivity) (fun δ _ => ?_)
    have := Real.add_one_le_exp (|wr δ| * Real.exp (a δ))
    linarith
  have hexp_le : Real.exp (∑ δ ∈ Λ.filter (fun δ => P.incomp γ δ = true),
      |wr δ| * Real.exp (a δ)) ≤ Real.exp (a γ) :=
    Real.exp_le_exp.mpr (hsum γ hγ)
  exact mul_le_mul_of_nonneg_left (le_trans hprod_le hexp_le) (abs_nonneg _)

/-- **Kotecký-Preiss-Kriterium, Teil 1:** unter der Summenbedingung
verschwindet die Zustandssumme nicht. -/
theorem Z_ne_zero_of_kp (Λ : Finset ι) (h : KPCondition P wr a Λ) :
    Z P wr Λ ≠ 0 :=
  Z_ne_zero_of_dobrushin P wr _ Λ h.dobrushin

/-- **Kotecký-Preiss-Kriterium, Teil 2:** die klassische
Quotientenschranke — Entfernen von `γ` ändert `|Z|` höchstens um den
Faktor `exp (a γ)`. Benutzt, dass die Summenbedingung wegen `γ ≁ γ` den
Term `|w γ| · exp (a γ) ≤ a γ` enthält. -/
theorem Z_ratio_bound_of_kp (Λ : Finset ι) (h : KPCondition P wr a Λ)
    (γ : ι) (hγ : γ ∈ Λ) :
    |Z P wr (Λ.erase γ)| ≤ Real.exp (a γ) * |Z P wr Λ| := by
  have hbase := Z_ratio_bound_of_dobrushin P wr
    (fun γ => |wr γ| * Real.exp (a γ)) Λ h.dobrushin γ hγ
  have hγN : γ ∈ Λ.filter (fun δ => P.incomp γ δ = true) :=
    mem_filter.mpr ⟨hγ, P.refl γ⟩
  have hterm : |wr γ| * Real.exp (a γ) ≤ a γ :=
    le_trans (Finset.single_le_sum
      (f := fun δ => |wr δ| * Real.exp (a δ))
      (fun δ _ => by positivity) hγN) (h.2 γ hγ)
  have hfac : 1 + |wr γ| * Real.exp (a γ) ≤ Real.exp (a γ) := by
    have h1 := Real.add_one_le_exp (a γ)
    linarith
  calc |Z P wr (Λ.erase γ)|
      ≤ (1 + |wr γ| * Real.exp (a γ)) * |Z P wr Λ| := hbase
    _ ≤ Real.exp (a γ) * |Z P wr Λ| :=
        mul_le_mul_of_nonneg_right hfac (abs_nonneg _)

/-- Logarithmus-Schranke in KP-Form:
`|log |Z Λ|| ≤ ∑_{γ ∈ Λ} |w γ| · exp (a γ)`. -/
theorem abs_log_abs_Z_le_of_kp (Λ : Finset ι) (h : KPCondition P wr a Λ) :
    |Real.log (|Z P wr Λ|)| ≤ ∑ γ ∈ Λ, |wr γ| * Real.exp (a γ) :=
  abs_log_abs_Z_le_sum_of_dobrushin P wr _ Λ h.dobrushin

end KoteckyPreiss

section FernandezProcacci
/-!
## Die Fernández-Procacci-Verfeinerung: Bedingung und Hierarchie

Die FP-Bedingung ersetzt im Dobrushin-Produkt `∏ (1 + μ δ)` durch das
Unabhängigkeitspolynom der Nachbarschaft — die Summe läuft nur noch über
unabhängige Teilmengen statt über alle. Das ist genau `Z` mit den
Gewichten `μ`, es braucht also keine neue Definition. Bewiesen wird hier
die Hierarchie der Bedingungen `KP ⟹ Dobrushin ⟹ FP` über
`Z_A(μ) ≤ ∏_{δ ∈ A} (1 + μ δ)`. Der FP-Konvergenzsatz selbst
(Nichtverschwinden von `Z` unter der FP-Bedingung, Fernández–Procacci,
Comm. Math. Phys. 274, 2007) ist der nächste offene Baustein; er braucht
eine verfeinerte Induktion und wird hier bewusst nicht behauptet.
-/

variable (wr : ι → ℝ) (μ : ι → ℝ)

/-- Fernández-Procacci-Bedingung auf `Λ`: für jedes `γ ∈ Λ` gilt
`|w γ| · Ξ ≤ μ γ`, wobei `Ξ = Z_N(μ)` das Unabhängigkeitspolynom der
geschlossenen Nachbarschaft `N` von `γ` in `Λ` ist. -/
def FPCondition (Λ : Finset ι) : Prop :=
  (∀ γ ∈ Λ, 0 ≤ μ γ) ∧
  ∀ γ ∈ Λ,
    |wr γ| * Z P μ (Λ.filter (fun δ => P.incomp γ δ = true)) ≤ μ γ

/-- Das Unabhängigkeitspolynom liegt unter dem vollen Produkt:
`Z_A(μ) ≤ ∏_{δ ∈ A} (1 + μ δ)` für `μ ≥ 0` auf `A` — Summe über
unabhängige Teilmengen gegen Summe über alle Teilmengen. -/
theorem Z_le_prod_one_add (A : Finset ι) (hpos : ∀ δ ∈ A, 0 ≤ μ δ) :
    Z P μ A ≤ ∏ δ ∈ A, (1 + μ δ) := by
  have hexp : ∏ δ ∈ A, (1 + μ δ) = ∑ S ∈ A.powerset, ∏ δ ∈ S, μ δ := by
    calc ∏ δ ∈ A, (1 + μ δ)
        = ∏ δ ∈ A, (μ δ + 1) := prod_congr rfl fun δ _ => by ring
      _ = ∑ S ∈ A.powerset, (∏ δ ∈ S, μ δ) * ∏ δ ∈ A \ S, 1 :=
          prod_add _ _ _
      _ = ∑ S ∈ A.powerset, ∏ δ ∈ S, μ δ :=
          sum_congr rfl fun S _ => by rw [prod_const_one, mul_one]
  rw [hexp]
  unfold Z
  refine sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun S hS _ => ?_
  exact prod_nonneg fun δ hδ => hpos δ (mem_powerset.mp hS hδ)

/-- Dobrushin ⟹ FP: die FP-Bedingung ist die schwächere Voraussetzung. -/
theorem DobrushinCondition.fp {Λ : Finset ι}
    (h : DobrushinCondition P wr μ Λ) : FPCondition P wr μ Λ := by
  obtain ⟨hpos, hbd⟩ := h
  refine ⟨hpos, fun γ hγ => le_trans ?_ (hbd γ hγ)⟩
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  exact Z_le_prod_one_add P μ _ fun δ hδ => hpos δ (mem_filter.mp hδ).1

/-- Die volle Hierarchie: KP ⟹ Dobrushin ⟹ FP, mit
`μ γ = |w γ| · exp (a γ)`. -/
theorem KPCondition.fp {Λ : Finset ι} {a : ι → ℝ}
    (h : KPCondition P wr a Λ) :
    FPCondition P wr (fun γ => |wr γ| * Real.exp (a γ)) Λ :=
  h.dobrushin.fp

end FernandezProcacci

end ClusterExpansion
