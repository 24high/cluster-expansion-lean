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
- [x] **Root-tree bound**: a spanning tree is its own Penrose tree, so
      the parent map is injective on spanning trees and
      `treeCount H ≤ |V| ^ (|V| − 1)`; per cluster,
      `|φᵀ(γ₁, …, γ_{n+1})| ≤ (n+1)ⁿ` (`penroseTree_of_isTree`,
      `treeCount_le_pow`, `abs_ursellInt_le_pow`).
- [x] **The cluster series as an analytic object, convergent in the
      small-weight regime**: the series `Σ' n, (1/(n+1)!) ·
      Σ_{(n+1)-tuples} φᵀ · ∏ w` (`clusterOrderSum`, `clusterCoeff`,
      `clusterSeries`), the geometric term bound
      `|clusterCoeff n| ≤ (e · Σ_Λ |w|)^{n+1}` (`abs_clusterCoeff_le`),
      and absolute convergence with the tail bound `r/(1−r)` whenever
      `e · Σ_{γ ∈ Λ} |w γ| < 1` (`summable_clusterCoeff`,
      `abs_clusterSeries_le`).
- [x] **Anchored (pinned) summability, crude form**: the absolute series
      of the tuples anchored at a fixed polymer `γ₀` is bounded by
      `e · |w γ₀| / (1 − e · Σ_Λ |w|)` — proportional to the anchor
      weight, uniformly in the volume (`pinnedOrderSum`,
      `pinnedOrderSum_le`, `tsum_pinned_le`).
- [x] **The structural sub-steps of the exponential formula**, over any
      commutative ring: the **bridge lemma** — for injective tuples the
      tuple-level Ursell function equals the set-level Ursell sum of the
      image (`ursellInt_eq_ursellSetSum`) — and the **cluster
      factorisation**, the closed iterate of the cluster recursion
      `Z Λ = Σ_C ∏_{B ∈ C} (∏_B w) · φ(B)` over all collections of
      pairwise disjoint nonempty clusters
      (`IsClusterCollection`, `Z_eq_sum_clusterCollections`) — the
      finite exponential formula in set form.

## Next

- [ ] **The exponential formula**: identify the cluster series with
      `log Z`, i.e. `log Z Λ = clusterSeries P w Λ` in the convergence
      regime. With the set-level factorisation and the bridge lemma in
      place, what remains is the symmetrisation over labelled tuples
      (multinomial regrouping of ordered set partitions, with repeats)
      and the log/exp identification itself.
- [ ] **The sharp Kotecký–Preiss summability estimate** over clusters:
      replace the root-tree count `(n+1)ⁿ` by counts of labelled trees
      with prescribed degrees, so that the anchored series is controlled
      under the KP condition `Σ_{δ ≁ γ} |w δ| · exp (a δ) ≤ a γ` rather
      than only in the small-weight regime — the tree–graph bound
      (`abs_ursellInt_le_treeCount`) supplies the per-cluster input.

## Beyond

The convergence machinery above is the workhorse estimate behind
rigorous renormalisation group arguments. The longer-term target is a
machine-checked treatment of Balaban's method, in the sense of the
expositions by Dimock (arXiv:1108.1335, 1212.5562, 1304.0705).

Contributions and corrections are welcome; please open an issue.
