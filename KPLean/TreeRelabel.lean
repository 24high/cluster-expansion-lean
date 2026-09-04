/-
Copyright (c) 2026 Dennis Michael Heine. All rights reserved.
Released under the CC BY-NC-SA 4.0 license as described in the file LICENSE.
Authors: Dennis Michael Heine
-/
import KPLean.Trees

/-!
# Umbenennungsinvarianz der Baumsumme

Die Baumsumme hängt nur von der Anzahl der Nichtwurzelknoten ab: beide
Summationsebenen — Wurzelbäume und festgenagelte Belegungen — lassen
sich entlang einer Umnummerierung `Fin (m+1) → B` transportieren, die
die Blockwurzel auf `0` schickt (`treeSum_eq_treeCoeff`).
-/

open Finset

set_option linter.style.openClassical false

open scoped Classical

namespace ClusterExpansion

variable {ι : Type*} [DecidableEq ι] (P : PolymerSystem ι)


/-! ## Umbenennungsinvarianz der Baumsumme -/

/-- **Die Umnummerierung**: zu einem ausgezeichneten Element `c ∈ B` mit
`|B.erase c| = m` gibt es eine Bijektion `Fin (m+1) → B`, die `0` auf `c`
schickt, zusammen mit ihrer Umkehrung auf `B`. -/
private theorem exists_relabel {J : Type*} [DecidableEq J] {B : Finset J}
    {c : J} (hc : c ∈ B) {m : ℕ} (hm : (B.erase c).card = m) :
    ∃ (e : Fin (m + 1) → J) (e' : J → Fin (m + 1)),
      e 0 = c ∧ (∀ i, e i ∈ B) ∧ (∀ i : Fin (m + 1), i ≠ 0 → e i ∈ B.erase c)
        ∧ (∀ i, e' (e i) = i) ∧ (∀ v ∈ B, e (e' v) = v)
        ∧ ∀ v ∈ B.erase c, e' v ≠ 0 := by
  obtain ⟨oi⟩ : Nonempty (Fin m ≃ {x // x ∈ B.erase c}) :=
    ⟨((B.erase c).equivFinOfCardEq hm).symm⟩
  have hcons0 : (Fin.cons c fun i => (oi i : J) : Fin (m + 1) → J) 0 = c :=
    Fin.cons_zero _ _
  have hconss : ∀ j : Fin m,
      (Fin.cons c fun i => (oi i : J) : Fin (m + 1) → J) j.succ = (oi j : J) :=
    fun j => Fin.cons_succ _ _ _
  refine ⟨(Fin.cons c fun i => (oi i : J) : Fin (m + 1) → J),
    fun v => if hv : v ∈ B.erase c then (oi.symm ⟨v, hv⟩).succ else 0,
    hcons0, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · rw [hcons0]
      exact hc
    · rw [hconss j]
      exact Finset.mem_of_mem_erase (oi j).2
  · intro i hi
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · exact absurd rfl hi
    · rw [hconss j]
      exact (oi j).2
  · intro i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · rw [hcons0]
      change (if hv : c ∈ B.erase c then (oi.symm ⟨c, hv⟩).succ else 0) = 0
      rw [dif_neg (Finset.notMem_erase c B)]
    · rw [hconss j]
      change (if hv : (oi j : J) ∈ B.erase c then (oi.symm ⟨(oi j : J), hv⟩).succ
        else 0) = j.succ
      rw [dif_pos (oi j).2]
      congr 1
      rw [Subtype.coe_eta, Equiv.symm_apply_apply]
  · intro v hv
    by_cases hvc : v = c
    · subst hvc
      change (Fin.cons v fun i => (oi i : J) : Fin (m + 1) → J)
        (if hw : v ∈ B.erase v then (oi.symm ⟨v, hw⟩).succ else 0) = v
      rw [dif_neg (Finset.notMem_erase v B), hcons0]
    · have hve : v ∈ B.erase c := Finset.mem_erase.mpr ⟨hvc, hv⟩
      change (Fin.cons c fun i => (oi i : J) : Fin (m + 1) → J)
        (if hw : v ∈ B.erase c then (oi.symm ⟨v, hw⟩).succ else 0) = v
      rw [dif_pos hve, hconss]
      exact congrArg Subtype.val (oi.apply_symm_apply ⟨v, hve⟩)
  · intro v hv
    change (if hw : v ∈ B.erase c then (oi.symm ⟨v, hw⟩).succ else 0) ≠ 0
    rw [dif_pos hv]
    exact Fin.succ_ne_zero _

/-- **Konjugation der Elterniteration**, Hinrichtung: entsteht `q` aus `p`
durch Umnummerierung, so ist die Iteration von `q` die umnummerierte
Iteration von `p`. -/
private theorem iterate_relabel {J J' : Type*} {S : Finset J} {e : J' → J}
    {e' : J → J'} {p : J → J} {q : J' → J'} (hq : ∀ i, q i = e' (p (e i)))
    (hpS : ∀ v, p v ∈ S) (heS : ∀ i, e i ∈ S) (hee' : ∀ v ∈ S, e (e' v) = v)
    (he'e : ∀ i, e' (e i) = i) (i : J') (k : ℕ) :
    q^[k] i = e' (p^[k] (e i)) := by
  have hmem : ∀ k, p^[k] (e i) ∈ S := by
    intro k
    cases k with
    | zero => exact heS i
    | succ k =>
      rw [Function.iterate_succ_apply']
      exact hpS _
  induction k with
  | zero => exact (he'e i).symm
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, hq, hee' _ (hmem k),
      Function.iterate_succ_apply']

/-- **Konjugation der Elterniteration**, Rückrichtung: stimmt `p` auf `S`
mit der Umnummerierung von `q` überein, so ist die Iteration von `p` die
umnummerierte Iteration von `q`. -/
private theorem iterate_relabel' {J J' : Type*} {S : Finset J} {e : J' → J}
    {e' : J → J'} {p : J → J} {q : J' → J'} (hp : ∀ v ∈ S, p v = e (q (e' v)))
    (heS : ∀ i, e i ∈ S) (hee' : ∀ v ∈ S, e (e' v) = v)
    (he'e : ∀ i, e' (e i) = i) {v : J} (hv : v ∈ S) (k : ℕ) :
    p^[k] v = e (q^[k] (e' v)) := by
  induction k with
  | zero => exact (hee' v hv).symm
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, hp _ (heS _), he'e,
      Function.iterate_succ_apply']

omit [DecidableEq ι] in
/-- **Umbenennungsinvarianz der Baumsumme**: die Baumsumme über der
Knotenmenge `B.erase c` mit Wurzel `c` hängt nur von der Anzahl der
Nichtwurzelknoten ab und ist damit der kanonische Baumkoeffizient. Der
Beweis transportiert beide Summationsebenen — Wurzelbäume und
festgenagelte Belegungen — entlang einer Umnummerierung
`Fin (|B|) → B`, die `0` auf `c` schickt. -/
theorem treeSum_eq_treeCoeff {J : Type*} [DecidableEq J] [Fintype J]
    (w : ι → ℝ) (Λ : Finset ι) (δ : ι) {B : Finset J} {c : J} (hc : c ∈ B) :
    treeSum P w Λ δ c (B.erase c) = treeCoeff P w Λ δ (B.card - 1) := by
  obtain ⟨m, hm⟩ : ∃ m, B.card = m + 1 :=
    ⟨B.card - 1, by have := Finset.card_pos.mpr ⟨c, hc⟩; omega⟩
  have hcard : B.card - 1 = m := by omega
  have hAcard : (B.erase c).card = m := by
    rw [Finset.card_erase_of_mem hc, hm, Nat.add_sub_cancel]
  obtain ⟨e, e', he0, heB, heA, he'e, hee', he'B⟩ := exists_relabel hc hAcard
  -- Grundtatsachen der Umnummerierung.
  have heinj : Function.Injective e := Function.LeftInverse.injective he'e
  have he'c : e' c = 0 := by rw [← he0]; exact he'e 0
  have hinsB : insert c (B.erase c) = B := Finset.insert_erase hc
  have hinsU : insert (0 : Fin (m + 1)) (Finset.univ.erase (0 : Fin (m + 1)))
      = Finset.univ :=
    Finset.insert_erase (Finset.mem_univ (0 : Fin (m + 1)))
  have himg : (Finset.univ.erase (0 : Fin (m + 1))).image e = B.erase c := by
    ext v
    rw [Finset.mem_image]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact heA i (Finset.mem_erase.mp hi).1
    · intro hv
      exact ⟨e' v, Finset.mem_erase.mpr ⟨he'B v hv, Finset.mem_univ _⟩,
        hee' v (Finset.mem_of_mem_erase hv)⟩
  rw [hcard]
  unfold treeCoeff treeSum
  refine Finset.sum_nbij' (fun p i => e' (p (e i)))
    (fun q v => if v ∈ B then e (q (e' v)) else c) ?_ ?_ ?_ ?_ ?_
  -- Hinrichtung: umnummerierte Wurzelbäume sind Wurzelbäume.
  · intro p hp
    obtain ⟨hpi, hpc, -, hpk⟩ := mem_rootedTrees.mp hp
    rw [hinsB] at hpi
    show (fun i => e' (p (e i))) ∈ rootedTrees (Finset.univ.erase 0) 0
    refine mem_rootedTrees.mpr ⟨fun i => ?_, ?_, fun i hi => ?_, fun i hi => ?_⟩
    · rw [hinsU]
      exact Finset.mem_univ _
    · change e' (p (e 0)) = 0
      rw [he0, hpc, he'c]
    · rw [hinsU] at hi
      exact absurd (Finset.mem_univ i) hi
    · have hi0 : i ≠ 0 := (Finset.mem_erase.mp hi).1
      obtain ⟨k, hk⟩ := hpk (e i) (heA i hi0)
      refine ⟨k, ?_⟩
      rw [iterate_relabel (q := fun i => e' (p (e i))) (fun _ => rfl) hpi heB
        hee' he'e i k, hk, he'c]
  -- Rückrichtung: zurücknummerierte Wurzelbäume sind Wurzelbäume.
  · intro q hq
    obtain ⟨-, hq0, -, hqk⟩ := mem_rootedTrees.mp hq
    show (fun v => if v ∈ B then e (q (e' v)) else c) ∈ rootedTrees (B.erase c) c
    have hpval : ∀ v ∈ B, (if v ∈ B then e (q (e' v)) else c) = e (q (e' v)) :=
      fun v hv => if_pos hv
    refine mem_rootedTrees.mpr ⟨fun v => ?_, ?_, fun v hv => ?_, fun v hv => ?_⟩
    · rw [hinsB]
      show (if v ∈ B then e (q (e' v)) else c) ∈ B
      split
      · exact heB _
      · exact hc
    · show (if c ∈ B then e (q (e' c)) else c) = c
      rw [if_pos hc, he'c, hq0, he0]
    · rw [hinsB] at hv
      show (if v ∈ B then e (q (e' v)) else c) = c
      rw [if_neg hv]
    · obtain ⟨k, hk⟩ := hqk (e' v)
        (Finset.mem_erase.mpr ⟨he'B v hv, Finset.mem_univ _⟩)
      refine ⟨k, ?_⟩
      rw [iterate_relabel' (p := fun v => if v ∈ B then e (q (e' v)) else c)
        hpval heB hee' he'e (Finset.mem_of_mem_erase hv) k, hk, he0]
  -- Linksinverse auf den Wurzelbäumen.
  · intro p hp
    obtain ⟨hpi, -, hpout, -⟩ := mem_rootedTrees.mp hp
    rw [hinsB] at hpi hpout
    funext v
    change (if v ∈ B then e (e' (p (e (e' v)))) else c) = p v
    by_cases hv : v ∈ B
    · rw [if_pos hv, hee' v hv, hee' _ (hpi v)]
    · rw [if_neg hv]
      exact (hpout v hv).symm
  -- Rechtsinverse auf den Wurzelbäumen.
  · intro q _
    funext i
    change e' (if e i ∈ B then e (q (e' (e i))) else c) = q i
    rw [if_pos (heB i)]
    simp only [he'e]
  -- Die inneren Summen über die Belegungen.
  · intro p hp
    obtain ⟨hpi, -, -, -⟩ := mem_rootedTrees.mp hp
    rw [hinsB] at hpi
    refine Finset.sum_nbij' (fun h i => h (e i))
      (fun g v => if v ∈ B.erase c then g (e' v) else δ) ?_ ?_ ?_ ?_ ?_
    -- Hinrichtung: umnummerierte Belegungen sind festgenagelt.
    · intro h hh
      obtain ⟨hin, hout⟩ := mem_pinnedTuples.mp hh
      refine mem_pinnedTuples.mpr ⟨fun i hi => ?_, fun i hi => ?_⟩
      · exact hin _ (heA i (Finset.mem_erase.mp hi).1)
      · have hi0 : i = 0 := by
          by_contra h0
          exact hi (Finset.mem_erase.mpr ⟨h0, Finset.mem_univ _⟩)
        subst hi0
        change h (e 0) = δ
        rw [he0]
        exact hout c (Finset.notMem_erase c B)
    -- Rückrichtung: zurücknummerierte Belegungen sind festgenagelt.
    · intro g hg
      obtain ⟨hin, -⟩ := mem_pinnedTuples.mp hg
      refine mem_pinnedTuples.mpr ⟨fun v hv => ?_, fun v hv => ?_⟩
      · show (if v ∈ B.erase c then g (e' v) else δ) ∈ Λ
        rw [if_pos hv]
        exact hin _ (Finset.mem_erase.mpr ⟨he'B v hv, Finset.mem_univ _⟩)
      · show (if v ∈ B.erase c then g (e' v) else δ) = δ
        rw [if_neg hv]
    -- Linksinverse auf den Belegungen.
    · intro h hh
      obtain ⟨-, hout⟩ := mem_pinnedTuples.mp hh
      funext v
      change (if v ∈ B.erase c then h (e (e' v)) else δ) = h v
      by_cases hv : v ∈ B.erase c
      · rw [if_pos hv, hee' v (Finset.mem_of_mem_erase hv)]
      · rw [if_neg hv]
        exact (hout v hv).symm
    -- Rechtsinverse auf den Belegungen.
    · intro g hg
      obtain ⟨-, hout⟩ := mem_pinnedTuples.mp hg
      funext i
      change (if e i ∈ B.erase c then g (e' (e i)) else δ) = g i
      by_cases hi : i = 0
      · subst hi
        have hni : e 0 ∉ B.erase c := by
          rw [he0]
          exact Finset.notMem_erase c B
        rw [if_neg hni]
        exact (hout 0 (Finset.notMem_erase 0 Finset.univ)).symm
      · rw [if_pos (heA i hi), he'e]
    -- Die Summanden stimmen überein.
    · intro h _
      change (∏ v ∈ B.erase c, |w (h v)|)
            * (if TreeIncompatible P h (B.erase c) p then 1 else 0)
          = (∏ i ∈ Finset.univ.erase (0 : Fin (m + 1)), |w (h (e i))|)
            * (if TreeIncompatible P (fun i => h (e i))
                (Finset.univ.erase 0) (fun i => e' (p (e i))) then 1 else 0)
      have hprod : ∏ v ∈ B.erase c, |w (h v)|
          = ∏ i ∈ Finset.univ.erase (0 : Fin (m + 1)), |w (h (e i))| := by
        rw [← himg, Finset.prod_image fun a _ b _ hab => heinj hab]
      have hincomp : TreeIncompatible P h (B.erase c) p
          ↔ TreeIncompatible P (fun i => h (e i)) (Finset.univ.erase 0)
              (fun i => e' (p (e i))) := by
        constructor
        · intro hT i hi
          have hiA : e i ∈ B.erase c := heA i (Finset.mem_erase.mp hi).1
          change P.incomp (h (e i)) (h (e (e' (p (e i))))) = true
          rw [hee' _ (hpi (e i))]
          exact hT (e i) hiA
        · intro hT v hv
          have hvi := hT (e' v)
            (Finset.mem_erase.mpr ⟨he'B v hv, Finset.mem_univ _⟩)
          change P.incomp (h v) (h (p v)) = true
          rw [show h v = h (e (e' v)) from
            congrArg h (hee' v (Finset.mem_of_mem_erase hv)).symm]
          rw [show h (p v) = h (e (e' (p (e (e' v))))) from ?_]
          · exact hvi
          · rw [hee' v (Finset.mem_of_mem_erase hv), hee' _ (hpi v)]
      rw [hprod]
      exact congrArg _ (if_congr hincomp rfl rfl)

end ClusterExpansion
