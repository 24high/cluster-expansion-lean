# Roadmap

The long-term aim of this project is machine-checked infrastructure for
the convergence estimates used in rigorous renormalisation group
analyses of lattice field theories. The path there runs through the
cluster expansion; the milestones below track how much of it is
formalised, with no `sorry`s at any completed step.

## Done

- [x] **Deletion recursion** over arbitrary commutative rings
      (`Z_recursion`).
- [x] **Dobrushin criterion** (product form): nonvanishing and the ratio
      bound `|Z (Λ \ {γ})| ≤ (1 + μ γ) · |Z Λ|`
      (`Z_ne_zero_of_dobrushin`, `Z_ratio_bound_of_dobrushin`).
- [x] **Kotecký–Preiss criterion** (sum form): nonvanishing and the
      classical `exp (a γ)` ratio bound, via the comparison of hypotheses
      `μ γ = |w γ| · exp (a γ)` (`Z_ne_zero_of_kp`,
      `Z_ratio_bound_of_kp`, `KPCondition.dobrushin`).
- [x] **Two-sided volume-linear bounds** on `|Z|` and `log |Z|`:
      `(∏ (1 + μ))⁻¹ ≤ |Z Λ| ≤ ∏ (1 + μ)`, hence
      `|log |Z Λ|| ≤ Σ log (1 + μ γ) ≤ Σ μ γ`
      (`prod_inv_le_abs_Z_of_dobrushin`, `abs_Z_le_prod_of_dobrushin`,
      `abs_log_abs_Z_le_of_dobrushin`, `abs_log_abs_Z_le_of_kp`).
- [x] **The hierarchy** KP ⟹ Dobrushin ⟹ Fernández–Procacci
      (`KPCondition.dobrushin`, `DobrushinCondition.fp`, `KPCondition.fp`,
      `Z_le_prod_one_add`).
- [x] **Fernández–Procacci criterion**: nonvanishing and ratio bound
      under the weakest of the three hypotheses, via Fialho's inductive
      proof — positivity of the alternating gas and the Scott–Sokal
      comparison (`Z_ne_zero_of_fp`, `Z_ratio_bound_of_fp`,
      `Z_neg_pos_of_fp`).
- [x] **Ursell functions and the Penrose tree–graph bound**: the Ursell
      function as an alternating sum over connected spanning subgraphs,
      and `|φᵀ| ≤ #{spanning trees}` via a complete formalisation of the
      Penrose partition scheme (`ursellInt`, `abs_ursellInt_le_treeCount`,
      `abs_ursellSum_le_treeCount`).
- [x] **Mayer expansion and the finite cluster recursion**, over any
      commutative ring: the graph expansion
      `Z Λ = Σ_{S ⊆ Λ} (∏_S w) · Σ_{G ⊆ E(S)} (−1)^{|G|}`
      (`Z_eq_sum_graphs`), and the cluster recursion
      `Z Λ = Z (Λ ∖ {γ₀}) + Σ_{γ₀ ∈ B ⊆ Λ} (∏_B w) · φ(B) · Z (Λ ∖ B)`
      (`Z_cluster_recursion`) — the finite exponential structure of the
      expansion.

## Next

- [ ] **The analytic layer of the cluster series for `log Z`.** Two
      steps remain, both requiring new infrastructure:
  - the **exponential formula**: identify the iterated cluster recursion
    (`Z_cluster_recursion`) with the convergent cluster series, so that
    `log Z Λ = Σ_{clusters} (1/n!) · φᵀ · ∏ w`;
  - the **Kotecký–Preiss summability estimate** over clusters, bounding
    the series via counts of labelled trees with prescribed degrees —
    where the tree–graph bound (`abs_ursellInt_le_treeCount`) supplies
    the per-cluster input.

## Beyond

The convergence machinery above is the workhorse estimate behind
rigorous renormalisation group arguments. The longer-term target is a
machine-checked treatment of Balaban's method, in the sense of the
expositions by Dimock (arXiv:1108.1335, 1212.5562, 1304.0705).

Contributions and corrections are welcome; please open an issue.
