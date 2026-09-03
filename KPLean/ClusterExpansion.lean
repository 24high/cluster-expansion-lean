/-
Copyright (c) 2026 Dennis Michael Heine. All rights reserved.
Released under the CC BY-NC-SA 4.0 license as described in the file LICENSE.
Authors: Dennis Michael Heine
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Cluster-Entwicklung: Fundamentalrekursion und Dobrushin-Kriterium

Abstraktes Polymersystem, Zustandssumme über unabhängige Polymermengen,
die Fundamentalrekursion `Z Λ = Z (Λ ∖ {γ}) + w γ * Z (Λ ohne N*(γ))`
über beliebigen kommutativen Ringen, und das vollständig bewiesene
Dobrushin-Konvergenzkriterium in Produktform: unter
`|w γ| · ∏_{δ ≁ γ} (1 + μ δ) ≤ μ γ` gilt `Z ≠ 0` und
`|Z (Λ ∖ {γ})| ≤ (1 + μ γ) · |Z Λ|`. Kein `sorry` in dieser Datei.

Die klassische Kotecký-Preiss-Summenform ist als Bedingung definiert;
ihr Satz braucht die Cluster- bzw. Baumgraphen-Induktion und ist der
nächste Baustein.

Kontext: DEGRALBA §17.1, „Balaban als Lean-Blueprint“.
Referenzen: Kotecký–Preiss (Comm. Math. Phys. 103, 1986);
Friedli–Velenik, *Statistical Mechanics of Lattice Systems*, Kap. 5;
Scott–Sokal (J. Stat. Phys. 118, 2005) zur Produktform.
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

Bewusst offen (kein `sorry`, nur nicht behauptet): die klassische
Summenform von Kotecký–Preiss (`KPCondition` unten). Sie folgt NICHT aus
der Teleskop-Induktion, denn Summen kontrollieren die dort auftretenden
Produkte nicht; sie braucht die Cluster- bzw. Baumgraphen-Induktion.
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

end Dobrushin

section KoteckyPreiss
/-!
## Die klassische Summenform (Definition; Satz noch offen)

Die Kotecký-Preiss-Bedingung in Summenform. Ihr Konvergenzsatz folgt
nicht aus der obigen Teleskop-Induktion (Summen kontrollieren keine
Produkte); der vorgesehene Weg ist die Cluster- bzw.
Baumgraphen-Induktion. Hier wird deshalb nur die Bedingung definiert,
ohne unbewiesene Behauptung im Code.
-/

variable (wr : ι → ℝ) (a : ι → ℝ)

/-- Kotecký-Preiss-Bedingung (Summenform) auf `Λ`:
`∑_{δ ≁ γ} |w δ| · exp (a δ) ≤ a γ` für alle `γ ∈ Λ`, mit `a ≥ 0`. -/
def KPCondition (Λ : Finset ι) : Prop :=
  (∀ γ ∈ Λ, 0 ≤ a γ) ∧
  ∀ γ ∈ Λ,
    ∑ δ ∈ Λ.filter (fun δ => P.incomp γ δ = true), |wr δ| * Real.exp (a δ) ≤ a γ

end KoteckyPreiss

end ClusterExpansion
