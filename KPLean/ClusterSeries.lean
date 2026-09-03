/-
Copyright (c) 2026 Dennis Michael Heine. All rights reserved.
Released under the CC BY-NC-SA 4.0 license as described in the file LICENSE.
Authors: Dennis Michael Heine
-/
import KPLean.Mayer
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Die Cluster-Reihe: Definition und Konvergenz im Kleinheitsregime

Erster analytischer Baustein der Cluster-Reihe von `log Z`: die Reihe
selbst als Objekt, und ihre absolute Konvergenz.

* `clusterOrderSum P w Λ n`: der Beitrag der Ordnung `n + 1`, die Summe
  über alle `(n+1)`-Tupel aus `Λ` von Ursell-Wert mal Gewichtsprodukt;
* `clusterCoeff`: das Reihenglied `clusterOrderSum / (n+1)!`;
* `clusterSeries`: die Cluster-Reihe `∑' n, clusterCoeff` — der
  Kandidat für `log Z Λ`;
* `abs_clusterCoeff_le`: die geometrische Schranke
  `|clusterCoeff n| ≤ (e · ∑_Λ |w|) ^ (n+1)`, über die
  Wurzelbaum-Schranke `|φᵀ| ≤ (n+1)ⁿ` (`abs_ursellInt_le_pow`) und
  `(n+1)ⁿ / (n+1)! ≤ e^{n+1}`;
* `summable_abs_clusterCoeff`, `summable_clusterCoeff`,
  `abs_clusterSeries_le`: absolute Konvergenz samt geometrischer
  Schranke im Kleinheitsregime `e · ∑_{γ ∈ Λ} |w γ| < 1`.

Kein `sorry` in dieser Datei. Bewusst offen (nur genannt, nichts
Unbewiesenes behauptet): die scharfe Kotecký-Preiss-Summierbarkeit
(über Baumzahlen mit vorgeschriebenen Graden) und die Identifikation
`clusterSeries = log Z` — die Exponentialformel.

Referenzen: Kotecký–Preiss (Comm. Math. Phys. 103, 1986); Ueltschi
(Moscow Math. J. 4, 2004); Friedli–Velenik, Kap. 5.
-/

open Finset

set_option linter.style.openClassical false

open scoped Classical

namespace ClusterExpansion

variable {ι : Type*} (P : PolymerSystem ι)

/-! ## Die Reihe -/

/-- Beitrag der Ordnung `n + 1` zur Cluster-Reihe von `log Z` auf `Λ`:
Summe über alle `(n+1)`-Tupel aus `Λ` von Ursell-Wert mal
Gewichtsprodukt. -/
noncomputable def clusterOrderSum (w : ι → ℝ) (Λ : Finset ι) (n : ℕ) : ℝ :=
  ∑ γ ∈ Fintype.piFinset fun _ : Fin (n + 1) => Λ,
    (ursellInt P γ : ℝ) * ∏ i, w (γ i)

/-- Das Glied der Cluster-Reihe: Ordnung `n + 1`, geteilt durch die
Symmetriezahl `(n + 1)!` der Tupel. -/
noncomputable def clusterCoeff (w : ι → ℝ) (Λ : Finset ι) (n : ℕ) : ℝ :=
  clusterOrderSum P w Λ n / (Nat.factorial (n + 1) : ℝ)

/-- Die Cluster-Reihe — der Kandidat für `log Z Λ`. -/
noncomputable def clusterSeries (w : ι → ℝ) (Λ : Finset ι) : ℝ :=
  ∑' n, clusterCoeff P w Λ n

/-- Ordnung `1` ist die Summe der Gewichte: `φᵀ(γ) = 1` für einzelne
Polymere. -/
theorem clusterOrderSum_zero (w : ι → ℝ) (Λ : Finset ι) :
    clusterOrderSum P w Λ 0 = ∑ x ∈ Λ, w x := by
  unfold clusterOrderSum
  refine Finset.sum_nbij' (fun γ => γ 0) (fun x => fun _ => x) ?_ ?_ ?_ ?_ ?_
  · intro γ hγ
    exact Fintype.mem_piFinset.mp hγ 0
  · intro x hx
    exact Fintype.mem_piFinset.mpr fun _ => hx
  · intro γ _
    funext i
    have h : i = 0 := by omega
    rw [h]
  · intro x _
    rfl
  · intro γ _
    rw [ursellInt_single, Int.cast_one, one_mul, Fin.prod_univ_one]

/-! ## Die geometrische Schranke -/

/-- Betragsschranke für den Beitrag der Ordnung `n + 1`:
Wurzelbaum-Schranke je Tupel, Gewichtssumme über die Tupel. -/
theorem abs_clusterOrderSum_le (w : ι → ℝ) (Λ : Finset ι) (n : ℕ) :
    |clusterOrderSum P w Λ n|
      ≤ ((n : ℝ) + 1) ^ n * (∑ x ∈ Λ, |w x|) ^ (n + 1) := by
  have hterm : ∀ γ ∈ Fintype.piFinset fun _ : Fin (n + 1) => Λ,
      |(ursellInt P γ : ℝ) * ∏ i, w (γ i)|
        ≤ ((n : ℝ) + 1) ^ n * ∏ i, |w (γ i)| := by
    intro γ _
    rw [abs_mul, Finset.abs_prod]
    refine mul_le_mul_of_nonneg_right ?_
      (Finset.prod_nonneg fun i _ => abs_nonneg _)
    calc |(ursellInt P γ : ℝ)| = ((|ursellInt P γ| : ℤ) : ℝ) := by
          rw [Int.cast_abs]
      _ ≤ ((((n + 1) ^ n : ℕ) : ℤ) : ℝ) := by
          exact_mod_cast abs_ursellInt_le_pow P γ
      _ = ((n : ℝ) + 1) ^ n := by push_cast; ring
  calc |clusterOrderSum P w Λ n|
      ≤ ∑ γ ∈ Fintype.piFinset fun _ : Fin (n + 1) => Λ,
          |(ursellInt P γ : ℝ) * ∏ i, w (γ i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ γ ∈ Fintype.piFinset fun _ : Fin (n + 1) => Λ,
          ((n : ℝ) + 1) ^ n * ∏ i, |w (γ i)| :=
        Finset.sum_le_sum hterm
    _ = ((n : ℝ) + 1) ^ n * ∑ γ ∈ Fintype.piFinset fun _ : Fin (n + 1) => Λ,
          ∏ i, |w (γ i)| := by
        rw [Finset.mul_sum]
    _ = ((n : ℝ) + 1) ^ n * (∑ x ∈ Λ, |w x|) ^ (n + 1) := by
        have hpow := Finset.prod_univ_sum
          (fun _ : Fin (n + 1) => Λ) (fun _ x => |w x|)
        rw [← hpow, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Stirling-artige Schranke: `(n + 1)ⁿ / n! ≤ e^{n+1}` — der Term
`i = n` der Exponentialreihe an der Stelle `n + 1`. -/
private theorem pow_div_factorial_le' (n : ℕ) :
    ((n : ℝ) + 1) ^ n / (Nat.factorial n : ℝ)
      ≤ Real.exp ((n : ℝ) + 1) := by
  have hx : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have hsingle : ((n : ℝ) + 1) ^ n / (Nat.factorial n : ℝ)
      ≤ ∑ i ∈ Finset.range (n + 2), ((n : ℝ) + 1) ^ i / (Nat.factorial i : ℝ) :=
    Finset.single_le_sum
      (f := fun i => ((n : ℝ) + 1) ^ i / (Nat.factorial i : ℝ))
      (fun i _ => by positivity) (Finset.mem_range.mpr (by omega))
  exact hsingle.trans (Real.sum_le_exp_of_nonneg hx (n + 2))

/-- Abgeschwächte Form mit `(n + 1)!` im Nenner. -/
private theorem pow_div_factorial_le (n : ℕ) :
    ((n : ℝ) + 1) ^ n / (Nat.factorial (n + 1) : ℝ)
      ≤ Real.exp ((n : ℝ) + 1) := by
  have hmono : ((n : ℝ) + 1) ^ n / (Nat.factorial (n + 1) : ℝ)
      ≤ ((n : ℝ) + 1) ^ n / (Nat.factorial n : ℝ) := by
    gcongr
    exact Nat.le_succ n
  exact hmono.trans (pow_div_factorial_le' n)

/-- **Geometrische Schranke für die Reihenglieder**:
`|clusterCoeff n| ≤ (e · ∑_{γ ∈ Λ} |w γ|) ^ (n+1)`. -/
theorem abs_clusterCoeff_le (w : ι → ℝ) (Λ : Finset ι) (n : ℕ) :
    |clusterCoeff P w Λ n| ≤ (Real.exp 1 * ∑ x ∈ Λ, |w x|) ^ (n + 1) := by
  have hfac : (0 : ℝ) < (Nat.factorial (n + 1) : ℝ) := by positivity
  unfold clusterCoeff
  rw [abs_div, abs_of_pos hfac]
  calc |clusterOrderSum P w Λ n| / (Nat.factorial (n + 1) : ℝ)
      ≤ (((n : ℝ) + 1) ^ n * (∑ x ∈ Λ, |w x|) ^ (n + 1))
          / (Nat.factorial (n + 1) : ℝ) := by
        gcongr
        exact abs_clusterOrderSum_le P w Λ n
    _ = ((n : ℝ) + 1) ^ n / (Nat.factorial (n + 1) : ℝ)
          * (∑ x ∈ Λ, |w x|) ^ (n + 1) := by
        ring
    _ ≤ Real.exp ((n : ℝ) + 1) * (∑ x ∈ Λ, |w x|) ^ (n + 1) :=
        mul_le_mul_of_nonneg_right (pow_div_factorial_le n)
          (pow_nonneg (Finset.sum_nonneg fun x _ => abs_nonneg _) _)
    _ = Real.exp 1 ^ (n + 1) * (∑ x ∈ Λ, |w x|) ^ (n + 1) := by
        rw [Real.exp_one_pow]
        push_cast
        ring_nf
    _ = (Real.exp 1 * ∑ x ∈ Λ, |w x|) ^ (n + 1) := (mul_pow _ _ _).symm

/-! ## Absolute Konvergenz im Kleinheitsregime -/

/-- **Absolute Summierbarkeit der Cluster-Reihe** unter der
Kleinheitsbedingung `e · ∑_{γ ∈ Λ} |w γ| < 1`: die Glieder sind durch
eine geometrische Reihe majorisiert. -/
theorem summable_abs_clusterCoeff (w : ι → ℝ) (Λ : Finset ι)
    (h : Real.exp 1 * ∑ x ∈ Λ, |w x| < 1) :
    Summable fun n => |clusterCoeff P w Λ n| := by
  have hr0 : (0 : ℝ) ≤ Real.exp 1 * ∑ x ∈ Λ, |w x| :=
    mul_nonneg (Real.exp_pos 1).le (Finset.sum_nonneg fun x _ => abs_nonneg _)
  have hgeom : Summable fun n : ℕ =>
      (Real.exp 1 * ∑ x ∈ Λ, |w x|) * (Real.exp 1 * ∑ x ∈ Λ, |w x|) ^ n :=
    (summable_geometric_of_lt_one hr0 h).mul_left _
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_) hgeom
  calc |clusterCoeff P w Λ n|
      ≤ (Real.exp 1 * ∑ x ∈ Λ, |w x|) ^ (n + 1) := abs_clusterCoeff_le P w Λ n
    _ = (Real.exp 1 * ∑ x ∈ Λ, |w x|)
          * (Real.exp 1 * ∑ x ∈ Λ, |w x|) ^ n := by
        rw [pow_succ']

/-- Die Cluster-Reihe konvergiert im Kleinheitsregime. -/
theorem summable_clusterCoeff (w : ι → ℝ) (Λ : Finset ι)
    (h : Real.exp 1 * ∑ x ∈ Λ, |w x| < 1) :
    Summable fun n => clusterCoeff P w Λ n :=
  (summable_abs_clusterCoeff P w Λ h).of_abs

/-- **Geometrische Schranke für die Cluster-Reihe** im
Kleinheitsregime: mit `r = e · ∑_{γ ∈ Λ} |w γ| < 1` gilt
`|clusterSeries| ≤ r / (1 - r)`. -/
theorem abs_clusterSeries_le (w : ι → ℝ) (Λ : Finset ι)
    (h : Real.exp 1 * ∑ x ∈ Λ, |w x| < 1) :
    |clusterSeries P w Λ|
      ≤ (Real.exp 1 * ∑ x ∈ Λ, |w x|)
          / (1 - Real.exp 1 * ∑ x ∈ Λ, |w x|) := by
  have hr0 : (0 : ℝ) ≤ Real.exp 1 * ∑ x ∈ Λ, |w x| :=
    mul_nonneg (Real.exp_pos 1).le (Finset.sum_nonneg fun x _ => abs_nonneg _)
  have habs := summable_abs_clusterCoeff P w Λ h
  have hgeom : Summable fun n : ℕ =>
      (Real.exp 1 * ∑ x ∈ Λ, |w x|) * (Real.exp 1 * ∑ x ∈ Λ, |w x|) ^ n :=
    (summable_geometric_of_lt_one hr0 h).mul_left _
  have h1 : |clusterSeries P w Λ| ≤ ∑' n, |clusterCoeff P w Λ n| := by
    have hn := norm_tsum_le_tsum_norm
      (f := fun n => clusterCoeff P w Λ n)
      (by simpa [Real.norm_eq_abs] using habs)
    simpa [Real.norm_eq_abs, clusterSeries] using hn
  have h2 : ∑' n, |clusterCoeff P w Λ n|
      ≤ ∑' n : ℕ, (Real.exp 1 * ∑ x ∈ Λ, |w x|)
          * (Real.exp 1 * ∑ x ∈ Λ, |w x|) ^ n := by
    refine Summable.tsum_le_tsum (fun n => ?_) habs hgeom
    calc |clusterCoeff P w Λ n|
        ≤ (Real.exp 1 * ∑ x ∈ Λ, |w x|) ^ (n + 1) := abs_clusterCoeff_le P w Λ n
      _ = (Real.exp 1 * ∑ x ∈ Λ, |w x|)
            * (Real.exp 1 * ∑ x ∈ Λ, |w x|) ^ n := by
          rw [pow_succ']
  have h3 : ∑' n : ℕ, (Real.exp 1 * ∑ x ∈ Λ, |w x|)
        * (Real.exp 1 * ∑ x ∈ Λ, |w x|) ^ n
      = (Real.exp 1 * ∑ x ∈ Λ, |w x|)
          * (1 - Real.exp 1 * ∑ x ∈ Λ, |w x|)⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 h]
  calc |clusterSeries P w Λ|
      ≤ ∑' n, |clusterCoeff P w Λ n| := h1
    _ ≤ ∑' n : ℕ, (Real.exp 1 * ∑ x ∈ Λ, |w x|)
          * (Real.exp 1 * ∑ x ∈ Λ, |w x|) ^ n := h2
    _ = (Real.exp 1 * ∑ x ∈ Λ, |w x|)
          * (1 - Real.exp 1 * ∑ x ∈ Λ, |w x|)⁻¹ := h3
    _ = (Real.exp 1 * ∑ x ∈ Λ, |w x|)
          / (1 - Real.exp 1 * ∑ x ∈ Λ, |w x|) := by
        rw [div_eq_mul_inv]

/-! ## Die verankerte Reihe

Für die Volumendifferenzen `log Z Λ - log Z (Λ ∖ {γ₀})` zählt nur der
Teil der Reihe, dessen Tupel `γ₀` verwenden. Hier die grobe Form seiner
Summierbarkeit, normiert mit `1/n!` für die Tupel mit **erster**
Koordinate `γ₀`: das ist die für die Differenz maßgebliche Normierung,
denn ein Tupel der Ordnung `n + 1`, das `γ₀` (mindestens) einmal
verwendet, hat `n + 1` mögliche Ankerpositionen, und
`(n + 1) · 1/(n+1)! = 1/n!`. Die Betragsreihe ist im Kleinheitsregime
durch `e · |w γ₀| / (1 - e · ∑_Λ |w|)` beschränkt — proportional zum
Gewicht des Ankers, gleichmäßig im Volumen. -/

/-- Der bei `γ₀` verankerte Betrags-Beitrag der Ordnung `n + 1`: Summe
über die Tupel aus `Λ` mit erster Koordinate `γ₀`. -/
noncomputable def pinnedOrderSum (w : ι → ℝ) (Λ : Finset ι) (γ₀ : ι)
    (n : ℕ) : ℝ :=
  ∑ γ ∈ (Fintype.piFinset fun _ : Fin (n + 1) => Λ).filter
      fun γ => γ 0 = γ₀,
    |(ursellInt P γ : ℝ)| * ∏ i, |w (γ i)|

theorem pinnedOrderSum_nonneg (w : ι → ℝ) (Λ : Finset ι) (γ₀ : ι) (n : ℕ) :
    0 ≤ pinnedOrderSum P w Λ γ₀ n :=
  Finset.sum_nonneg fun _γ _ => mul_nonneg (abs_nonneg _)
    (Finset.prod_nonneg fun _i _ => abs_nonneg _)

/-- Gewichtsschranke für den verankerten Beitrag: Wurzelbaum-Schranke je
Tupel, ein Faktor `|w γ₀|` für den Anker, die Gewichtssumme für die
übrigen `n` Koordinaten. -/
theorem pinnedOrderSum_le (w : ι → ℝ) (Λ : Finset ι) (γ₀ : ι) (n : ℕ) :
    pinnedOrderSum P w Λ γ₀ n
      ≤ ((n : ℝ) + 1) ^ n * |w γ₀| * (∑ x ∈ Λ, |w x|) ^ n := by
  have hterm : ∀ γ ∈ (Fintype.piFinset fun _ : Fin (n + 1) => Λ).filter
      fun γ => γ 0 = γ₀,
      |(ursellInt P γ : ℝ)| * ∏ i, |w (γ i)|
        ≤ ((n : ℝ) + 1) ^ n * |w γ₀| * ∏ i : Fin n, |w (γ i.succ)| := by
    intro γ hγ
    have hpin : γ 0 = γ₀ := (Finset.mem_filter.mp hγ).2
    have hsplit : ∏ i, |w (γ i)| = |w γ₀| * ∏ i : Fin n, |w (γ i.succ)| := by
      rw [Fin.prod_univ_succ, hpin]
    rw [hsplit, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_
      (abs_nonneg _)) (Finset.prod_nonneg fun i _ => abs_nonneg _)
    calc |(ursellInt P γ : ℝ)| = ((|ursellInt P γ| : ℤ) : ℝ) := by
          rw [Int.cast_abs]
      _ ≤ ((((n + 1) ^ n : ℕ) : ℤ) : ℝ) := by
          exact_mod_cast abs_ursellInt_le_pow P γ
      _ = ((n : ℝ) + 1) ^ n := by push_cast; ring
  have hsum : ∑ γ ∈ (Fintype.piFinset fun _ : Fin (n + 1) => Λ).filter
        fun γ => γ 0 = γ₀, ∏ i : Fin n, |w (γ i.succ)|
      ≤ (∑ x ∈ Λ, |w x|) ^ n := by
    by_cases hγ₀ : γ₀ ∈ Λ
    · have hbij : ∑ γ ∈ (Fintype.piFinset fun _ : Fin (n + 1) => Λ).filter
            fun γ => γ 0 = γ₀, ∏ i : Fin n, |w (γ i.succ)|
          = ∑ g ∈ Fintype.piFinset fun _ : Fin n => Λ,
              ∏ i : Fin n, |w (g i)| := by
        refine Finset.sum_nbij' (fun γ => Fin.tail γ)
          (fun g => Fin.cons γ₀ g) ?_ ?_ ?_ ?_ ?_
        · intro γ hγ
          have hmem := (Finset.mem_filter.mp hγ).1
          exact Fintype.mem_piFinset.mpr fun i =>
            Fintype.mem_piFinset.mp hmem i.succ
        · intro g hg
          refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i => ?_,
            Fin.cons_zero _ _⟩
          induction i using Fin.cases with
          | zero => rw [Fin.cons_zero]; exact hγ₀
          | succ j => rw [Fin.cons_succ]; exact Fintype.mem_piFinset.mp hg j
        · intro γ hγ
          have hpin : γ 0 = γ₀ := (Finset.mem_filter.mp hγ).2
          rw [← hpin]
          exact Fin.cons_self_tail γ
        · intro g _
          exact Fin.tail_cons (α := fun _ => ι) γ₀ g
        · intro γ _
          rfl
      rw [hbij]
      have hpow := Finset.prod_univ_sum
        (fun _ : Fin n => Λ) (fun _ x => |w x|)
      rw [← hpow, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    · have hempty : (Fintype.piFinset fun _ : Fin (n + 1) => Λ).filter
          (fun γ => γ 0 = γ₀) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro γ hγ
        obtain ⟨hmem, hpin⟩ := Finset.mem_filter.mp hγ
        exact hγ₀ (hpin ▸ Fintype.mem_piFinset.mp hmem 0)
      rw [hempty, Finset.sum_empty]
      exact pow_nonneg (Finset.sum_nonneg fun x _ => abs_nonneg _) n
  calc pinnedOrderSum P w Λ γ₀ n
      ≤ ∑ γ ∈ (Fintype.piFinset fun _ : Fin (n + 1) => Λ).filter
          fun γ => γ 0 = γ₀,
          ((n : ℝ) + 1) ^ n * |w γ₀| * ∏ i : Fin n, |w (γ i.succ)| :=
        Finset.sum_le_sum hterm
    _ = ((n : ℝ) + 1) ^ n * |w γ₀|
          * ∑ γ ∈ (Fintype.piFinset fun _ : Fin (n + 1) => Λ).filter
              fun γ => γ 0 = γ₀, ∏ i : Fin n, |w (γ i.succ)| := by
        rw [Finset.mul_sum]
    _ ≤ ((n : ℝ) + 1) ^ n * |w γ₀| * (∑ x ∈ Λ, |w x|) ^ n :=
        mul_le_mul_of_nonneg_left hsum
          (mul_nonneg (by positivity) (abs_nonneg _))

/-- Geometrische Schranke für das verankerte Reihenglied, in der
`1/n!`-Normierung. -/
theorem pinnedCoeff_le (w : ι → ℝ) (Λ : Finset ι) (γ₀ : ι) (n : ℕ) :
    pinnedOrderSum P w Λ γ₀ n / (Nat.factorial n : ℝ)
      ≤ Real.exp 1 * |w γ₀| * (Real.exp 1 * ∑ x ∈ Λ, |w x|) ^ n := by
  have hfac : (0 : ℝ) < (Nat.factorial n : ℝ) := by positivity
  calc pinnedOrderSum P w Λ γ₀ n / (Nat.factorial n : ℝ)
      ≤ (((n : ℝ) + 1) ^ n * |w γ₀| * (∑ x ∈ Λ, |w x|) ^ n)
          / (Nat.factorial n : ℝ) := by
        gcongr
        exact pinnedOrderSum_le P w Λ γ₀ n
    _ = ((n : ℝ) + 1) ^ n / (Nat.factorial n : ℝ)
          * (|w γ₀| * (∑ x ∈ Λ, |w x|) ^ n) := by
        ring
    _ ≤ Real.exp ((n : ℝ) + 1) * (|w γ₀| * (∑ x ∈ Λ, |w x|) ^ n) :=
        mul_le_mul_of_nonneg_right (pow_div_factorial_le' n)
          (mul_nonneg (abs_nonneg _)
            (pow_nonneg (Finset.sum_nonneg fun x _ => abs_nonneg _) n))
    _ = Real.exp 1 * |w γ₀| * (Real.exp 1 * ∑ x ∈ Λ, |w x|) ^ n := by
        have hexp : Real.exp ((n : ℝ) + 1) = Real.exp 1 * Real.exp 1 ^ n := by
          rw [Real.exp_add, ← Real.exp_one_pow]
          ring
        rw [hexp, mul_pow]
        ring

/-- **Verankerte Summierbarkeit (grobe Form)**: im Kleinheitsregime ist
die bei `γ₀` verankerte Betragsreihe in der `1/n!`-Normierung durch
`e · |w γ₀| / (1 - e · W)` beschränkt — proportional zum Gewicht des
Ankers, gleichmäßig im Volumen. Die scharfe Kotecký-Preiss-Form ersetzt
die Wurzelbaum-Zählung durch Baumzahlen mit vorgeschriebenen Graden. -/
theorem tsum_pinned_le (w : ι → ℝ) (Λ : Finset ι) (γ₀ : ι)
    (h : Real.exp 1 * ∑ x ∈ Λ, |w x| < 1) :
    ∑' n, pinnedOrderSum P w Λ γ₀ n / (Nat.factorial n : ℝ)
      ≤ Real.exp 1 * |w γ₀|
          / (1 - Real.exp 1 * ∑ x ∈ Λ, |w x|) := by
  have hr0 : (0 : ℝ) ≤ Real.exp 1 * ∑ x ∈ Λ, |w x| :=
    mul_nonneg (Real.exp_pos 1).le (Finset.sum_nonneg fun x _ => abs_nonneg _)
  have hgeom : Summable fun n : ℕ =>
      Real.exp 1 * |w γ₀| * (Real.exp 1 * ∑ x ∈ Λ, |w x|) ^ n :=
    (summable_geometric_of_lt_one hr0 h).mul_left _
  have hpinned : Summable fun n =>
      pinnedOrderSum P w Λ γ₀ n / (Nat.factorial n : ℝ) :=
    Summable.of_nonneg_of_le
      (fun n => div_nonneg (pinnedOrderSum_nonneg P w Λ γ₀ n) (by positivity))
      (fun n => pinnedCoeff_le P w Λ γ₀ n) hgeom
  calc ∑' n, pinnedOrderSum P w Λ γ₀ n / (Nat.factorial n : ℝ)
      ≤ ∑' n : ℕ, Real.exp 1 * |w γ₀|
          * (Real.exp 1 * ∑ x ∈ Λ, |w x|) ^ n :=
        Summable.tsum_le_tsum (fun n => pinnedCoeff_le P w Λ γ₀ n)
          hpinned hgeom
    _ = Real.exp 1 * |w γ₀|
          * (1 - Real.exp 1 * ∑ x ∈ Λ, |w x|)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 h]
    _ = Real.exp 1 * |w γ₀|
          / (1 - Real.exp 1 * ∑ x ∈ Λ, |w x|) := by
        rw [div_eq_mul_inv]

end ClusterExpansion
