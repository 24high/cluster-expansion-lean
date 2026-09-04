/-
Copyright (c) 2026 Dennis Michael Heine. All rights reserved.
Released under the CC BY-NC-SA 4.0 license as described in the file LICENSE.
Authors: Dennis Michael Heine
-/
import KPLean.ClusterSeries

/-!
# Symmetrie der Ursell-Funktion

Die Ursell-Funktion hängt nur vom Polymer-Tupel bis auf Umordnung ab
(`ursellInt_comp_perm`). Grundlage ist die Umbenennungsinvarianz der
Ursell-Summe (`ursellSum_image_equiv`): eine Bijektion der Knotenmenge
transportiert die zusammenhängenden aufspannenden Teilgraphen
kardinalitätstreu, lässt also die alternierende Summe unverändert.

Die Symmetrie ist der Schritt, mit dem sich „das Polymer `γ₀` kommt im
Cluster irgendwo vor" auf „es steht an erster Stelle" zurückführen
lässt — zum Preis eines Faktors `n + 1`, den die Fakultät der
Cluster-Reihe gerade schluckt (`abs_clusterOrderSum_sub_le`).
-/

open Finset

set_option linter.style.openClassical false

open scoped Classical

namespace ClusterExpansion

/-! ## Umbenennungsinvarianz -/

/-- `Sym2.map` der Umkehrabbildung macht `Sym2.map` einer Äquivalenz rückgängig. -/
theorem sym2_map_symm_map {V W : Type*} (e : V ≃ W) (x : Sym2 V) :
    Sym2.map e.symm (Sym2.map e x) = x := by
  induction x using Sym2.ind with
  | _ i j =>
    rw [Sym2.map_mk, Sym2.map_mk, e.symm_apply_apply, e.symm_apply_apply]

/-- Zusammenhang überträgt sich entlang einer Äquivalenz auf das Bild. -/
theorem edgeConn_image {V W : Type*} [DecidableEq W] (e : V ≃ W)
    {G : Finset (Sym2 V)} (hG : EdgeConn G) :
    EdgeConn (G.image (Sym2.map e)) := by
  have hne : Nonempty W := ⟨e hG.nonempty.some⟩
  refine SimpleGraph.Connected.mk fun u v => ?_
  obtain ⟨p⟩ := hG.preconnected (e.symm u) (e.symm v)
  have h := walk_map (f := (e : V → W)) e.injective p
  rwa [e.apply_symm_apply, e.apply_symm_apply] at h

/-- **Umbenennungsinvarianz der Ursell-Summe**: eine Bijektion der
Knotenmenge lässt die alternierende Summe über die zusammenhängenden
aufspannenden Teilgraphen unverändert. -/
theorem ursellSum_image_equiv {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq W] (e : V ≃ W) (H : Finset (Sym2 V)) :
    ursellSum (H.image (Sym2.map e)) = ursellSum H := by
  have hVW : ∀ x : Sym2 V, Sym2.map e.symm (Sym2.map e x) = x :=
    sym2_map_symm_map e
  have hWV : ∀ y : Sym2 W, Sym2.map e (Sym2.map e.symm y) = y := by
    intro y
    have h := sym2_map_symm_map e.symm y
    rwa [e.symm_symm] at h
  have hinjW : Function.Injective (Sym2.map (e.symm : W → V)) :=
    Function.LeftInverse.injective hWV
  have hcanc : ∀ G : Finset (Sym2 V),
      (G.image (Sym2.map e)).image (Sym2.map e.symm) = G := by
    intro G
    rw [Finset.image_image]
    exact (Finset.image_congr fun x _ => hVW x).trans Finset.image_id
  have hcanc' : ∀ G : Finset (Sym2 W),
      (G.image (Sym2.map e.symm)).image (Sym2.map e) = G := by
    intro G
    rw [Finset.image_image]
    exact (Finset.image_congr fun y _ => hWV y).trans Finset.image_id
  unfold ursellSum
  refine Finset.sum_nbij' (fun G' => G'.image (Sym2.map e.symm))
    (fun G => G.image (Sym2.map e)) ?_ ?_ ?_ ?_ ?_
  · intro G' hG'
    obtain ⟨hpow, hconn⟩ := Finset.mem_filter.mp hG'
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩
    · have h := Finset.image_subset_image (f := Sym2.map (e.symm : W → V))
        (Finset.mem_powerset.mp hpow)
      rwa [hcanc H] at h
    · exact edgeConn_image e.symm hconn
  · intro G hG
    obtain ⟨hpow, hconn⟩ := Finset.mem_filter.mp hG
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr
        (Finset.image_subset_image (Finset.mem_powerset.mp hpow)),
       edgeConn_image e hconn⟩
  · intro G' _
    exact hcanc' G'
  · intro G _
    exact hcanc G
  · intro G' _
    rw [Finset.card_image_of_injective G' hinjW]

/-! ## Symmetrie der Ursell-Funktion -/

theorem clusterEdges_comp_perm {ι : Type*} (P : PolymerSystem ι) {n : ℕ}
    (γ : Fin (n + 1) → ι) (σ : Equiv.Perm (Fin (n + 1))) :
    clusterEdges P γ = (clusterEdges P (γ ∘ σ)).image (Sym2.map σ) := by
  ext x
  induction x using Sym2.ind with
  | _ i j =>
    constructor
    · intro hx
      obtain ⟨hne, hinc⟩ := (mem_clusterEdges P).mp hx
      have hmem : s(σ.symm i, σ.symm j) ∈ clusterEdges P (γ ∘ σ) := by
        refine (mem_clusterEdges P).mpr ⟨?_, ?_⟩
        · exact fun h => hne (by rw [← σ.apply_symm_apply i, ← σ.apply_symm_apply j, h])
        · simpa [Function.comp_apply, σ.apply_symm_apply] using hinc
      have h := Finset.mem_image_of_mem (Sym2.map (σ : Fin (n + 1) → Fin (n + 1))) hmem
      rwa [Sym2.map_mk, σ.apply_symm_apply, σ.apply_symm_apply] at h
    · intro hx
      obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx
      revert hy hxy
      induction y using Sym2.ind with
      | _ a b =>
        intro hy hxy
        obtain ⟨hne, hinc⟩ := (mem_clusterEdges P).mp hy
        rw [Sym2.map_mk] at hxy
        rw [← hxy]
        exact (mem_clusterEdges P).mpr
          ⟨fun h => hne (σ.injective h), hinc⟩

/-- **Symmetrie der Ursell-Funktion**: der Wert hängt nur vom Tupel bis auf
Umordnung ab. -/
theorem ursellInt_comp_perm {ι : Type*} (P : PolymerSystem ι) {n : ℕ}
    (γ : Fin (n + 1) → ι) (σ : Equiv.Perm (Fin (n + 1))) :
    ursellInt P (γ ∘ σ) = ursellInt P γ := by
  unfold ursellInt
  rw [clusterEdges_comp_perm P γ σ, ursellSum_image_equiv]

/-! ## Die Ordnungs-Differenzschranke -/


variable {ι : Type*} (P : PolymerSystem ι)

/-- Die an einer beliebigen Stelle `i` verankerte Ordnungssumme stimmt
mit der an der ersten Stelle verankerten überein: das Vertauschen von
`i` und `0` lässt Ursell-Betrag und Gewichtsprodukt unverändert. -/
theorem sum_pinned_at (w : ι → ℝ) (Λ : Finset ι) (γ₀ : ι) (n : ℕ)
    (i : Fin (n + 1)) :
    ∑ γ ∈ (Fintype.piFinset fun _ : Fin (n + 1) => Λ).filter
        (fun γ => γ i = γ₀), |(ursellInt P γ : ℝ)| * ∏ j, |w (γ j)|
      = pinnedOrderSum P w Λ γ₀ n := by
  unfold pinnedOrderSum
  have hswap : ∀ γ : Fin (n + 1) → ι, ∀ j,
      (γ ∘ Equiv.swap i 0) j = γ (Equiv.swap i 0 j) := fun _ _ => rfl
  refine Finset.sum_nbij' (fun γ => γ ∘ Equiv.swap i 0)
    (fun γ => γ ∘ Equiv.swap i 0) ?_ ?_ ?_ ?_ ?_
  · intro γ hγ
    obtain ⟨hmem, hpin⟩ := Finset.mem_filter.mp hγ
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun j => ?_, ?_⟩
    · exact Fintype.mem_piFinset.mp hmem _
    · rw [hswap, Equiv.swap_apply_right]
      exact hpin
  · intro γ hγ
    obtain ⟨hmem, hpin⟩ := Finset.mem_filter.mp hγ
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun j => ?_, ?_⟩
    · exact Fintype.mem_piFinset.mp hmem _
    · rw [hswap, Equiv.swap_apply_left]
      exact hpin
  · intro γ _
    funext j
    rw [hswap, hswap, Equiv.swap_apply_self]
  · intro γ _
    funext j
    rw [hswap, hswap, Equiv.swap_apply_self]
  · intro γ _
    rw [ursellInt_comp_perm P γ (Equiv.swap i 0)]
    congr 1
    simp only [Function.comp_apply]
    exact (Equiv.prod_comp (Equiv.swap i 0) fun j => |w (γ j)|).symm

/-- **Die Ordnungs-Differenzschranke**: der Beitrag der Ordnung `n + 1`
ändert sich beim Entfernen von `γ₀` um höchstens `n + 1` mal den bei
`γ₀` verankerten Beitrag — denn ein Tupel, das `γ₀` verwendet, tut das
an einer der `n + 1` Stellen, und die Symmetrie der Ursell-Funktion
macht alle Stellen gleichwertig. -/
theorem abs_clusterOrderSum_sub_le (w : ι → ℝ) (Λ : Finset ι) (γ₀ : ι)
    (n : ℕ) :
    |clusterOrderSum P w Λ n - clusterOrderSum P w (Λ.erase γ₀) n|
      ≤ ((n : ℝ) + 1) * pinnedOrderSum P w Λ γ₀ n := by
  set T := Fintype.piFinset fun _ : Fin (n + 1) => Λ with hT
  set S := Fintype.piFinset fun _ : Fin (n + 1) => Λ.erase γ₀ with hS
  have hsub : S ⊆ T := by
    intro γ hγ
    rw [hS, Fintype.mem_piFinset] at hγ
    exact Fintype.mem_piFinset.mpr fun j => Finset.mem_of_mem_erase (hγ j)
  -- Die Differenz ist die Summe über die Tupel, die `γ₀` verwenden.
  have hdiff : clusterOrderSum P w Λ n - clusterOrderSum P w (Λ.erase γ₀) n
      = ∑ γ ∈ T \ S, (ursellInt P γ : ℝ) * ∏ j, w (γ j) := by
    unfold clusterOrderSum
    exact (eq_sub_of_add_eq (Finset.sum_sdiff hsub)).symm
  -- Ein solches Tupel trägt `γ₀` an mindestens einer Stelle.
  have hex : ∀ γ ∈ T \ S, ∃ i : Fin (n + 1), γ i = γ₀ := by
    intro γ hγ
    obtain ⟨hmemT, hnotS⟩ := Finset.mem_sdiff.mp hγ
    by_contra hcon
    push Not at hcon
    exact hnotS (Fintype.mem_piFinset.mpr fun j =>
      Finset.mem_erase.mpr ⟨hcon j, Fintype.mem_piFinset.mp hmemT j⟩)
  have hnn : ∀ (γ : Fin (n + 1) → ι) (i : Fin (n + 1)),
      0 ≤ (if γ i = γ₀ then |(ursellInt P γ : ℝ)| * ∏ j, |w (γ j)| else 0) := by
    intro γ i
    split
    · exact mul_nonneg (abs_nonneg _) (Finset.prod_nonneg fun j _ => abs_nonneg _)
    · exact le_rfl
  rw [hdiff]
  calc |∑ γ ∈ T \ S, (ursellInt P γ : ℝ) * ∏ j, w (γ j)|
      ≤ ∑ γ ∈ T \ S, |(ursellInt P γ : ℝ)| * ∏ j, |w (γ j)| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun γ _ => by rw [abs_mul, Finset.abs_prod]
    _ ≤ ∑ γ ∈ T \ S, ∑ i : Fin (n + 1),
          (if γ i = γ₀ then |(ursellInt P γ : ℝ)| * ∏ j, |w (γ j)| else 0) := by
        refine Finset.sum_le_sum fun γ hγ => ?_
        obtain ⟨i, hi⟩ := hex γ hγ
        refine le_trans (le_of_eq ?_)
          (Finset.single_le_sum (fun k _ => hnn γ k) (Finset.mem_univ i))
        rw [if_pos hi]
    _ ≤ ∑ γ ∈ T, ∑ i : Fin (n + 1),
          (if γ i = γ₀ then |(ursellInt P γ : ℝ)| * ∏ j, |w (γ j)| else 0) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset ?_
        exact fun γ _ _ => Finset.sum_nonneg fun i _ => hnn γ i
    _ = ∑ i : Fin (n + 1), ∑ γ ∈ T,
          (if γ i = γ₀ then |(ursellInt P γ : ℝ)| * ∏ j, |w (γ j)| else 0) :=
        Finset.sum_comm
    _ = ∑ _i : Fin (n + 1), pinnedOrderSum P w Λ γ₀ n := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_filter]
        exact sum_pinned_at P w Λ γ₀ n i
    _ = ((n : ℝ) + 1) * pinnedOrderSum P w Λ γ₀ n := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

end ClusterExpansion
