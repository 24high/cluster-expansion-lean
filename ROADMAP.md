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

- [x] **The building blocks of the exponential formula**
      (`KPLean/Exponential.lean`), all proved: the polymer system pulled
      back along an assignment (`PolymerSystem.pull`) and the tuple sums
      `tupleZ`, `tupleU` built on it; the **partition identity of the
      independence indicator** `[Indep Q A] = Σ_{partitions of A} ∏ φ(B)`
      (`indep_indicator_eq_sum_partitions`, by comparing degree-`|A|`
      coefficients in the cluster factorisation over `Polynomial ℤ`);
      the **block decomposition**
      `tupleZ K = Σ_{partitions of K} ∏ tupleU B`
      (`tupleZ_eq_sum_partitions`); the **block reduction**
      `tupleU B = clusterOrderSum (|B| − 1)`
      (`tupleU_eq_clusterOrderSum`, via `Fin |B| ≃o B` and the bridge
      lemma); the **layer count** `tupleZ_m = m! · (m-th layer of Z)`,
      hence `Z = Σ_m tupleZ_m / m!` (`tupleZ_univ_eq`,
      `Z_eq_sum_tupleZ`); and the **analytic exponential step**
      (`exp_tsum_eq`) expanding `exp` of an absolutely convergent series
      into compositions grouped by total weight.

- [x] **The multinomial count of partitions**, proved from scratch
      (Mathlib does not have it: `Multiset.bell` is defined
      multinomially and the statement that it counts partitions is an
      explicit TODO there). Ordered partitions with size profile `c`
      number `|A|!/∏ cᵢ!` (`sum_orderedPartitionsF_eq_compositions`, by
      induction on the number of blocks), and unordered ones a further
      `k!` fewer (`sum_orderedPartitionsF_eq`, by fibring over the image
      and counting embeddings `Fin k ↪ C`); together
      `sum_partitionsOf_card`.
- [x] **The exponential formula**:
      `log Z Λ = clusterSeries P w Λ` in the small-weight regime
      `e · Σ_{γ ∈ Λ} |w γ| < 1` (`exp_clusterSeries_eq_Z`,
      `log_Z_eq_clusterSeries`), with `Z Λ > 0` as a by-product
      (`Z_pos_of_small`). The convergent cluster series of `log Z` is
      thereby identified with `log Z` itself, and the geometric bound
      `abs_clusterSeries_le` becomes a bound on `log Z`.

- [x] **The sharp Kotecký–Preiss summability estimate**: under the KP
      condition `Σ_{δ ≁ γ} |w δ| · exp (a δ) ≤ a γ`, the anchored
      absolute series obeys
      `Σ'_n pinnedOrderSum(γ₀, n)/n! ≤ |w γ₀| · exp (a γ₀)`
      (`tsum_pinned_le_of_kp`) — uniformly in the volume and with no
      smallness hypothesis. Trees are carried as **parent maps**
      (`rootedTrees`, `treeSum`, `treeCoeff`), which is what makes this
      cheap: a *bound* only needs an injection from spanning trees into
      parent maps, and the Penrose scheme already supplies one
      (`treeCount_le_card_rootedTrees`), so neither Cayley's formula nor
      the Prüfer correspondence is required. The chain is: the
      decomposition of a rooted tree at its root
      (`subtreeOf_image_mem_partitionsOf`), the peel inequality
      splitting off one block (`treeSum_le_peel`, via `fibre_sum_le`),
      relabelling invariance (`treeSum_eq_treeCoeff`), the multinomial
      count reused from the exponential formula
      (`treeCoeff_div_le`), and induction on the truncation height
      (`treeTrunc_le_exp`).

- [x] **The exponential formula under the Kotecký–Preiss condition**:
      `log Z Λ = clusterSeries P w Λ` and `Z Λ > 0` under the KP
      condition alone (`log_Z_eq_clusterSeries_of_kp`, `Z_pos_of_kp`,
      `exp_clusterSeries_eq_Z_of_kp`), with no smallness hypothesis. No
      analytic continuation was needed: smallness entered the proof of
      the exponential formula at exactly two points, both of which want
      nothing but absolute convergence of the series, so the hypotheses
      were weakened rather than the proof rerun. The sharp anchored
      bound, summed over the anchors, supplies that convergence with
      constant `Σ_{γ ∈ Λ} |w γ| · exp (a γ)` — the same volume-linear
      quantity `abs_log_abs_Z_le_of_kp` already bounds `|log |Z||` by
      (`summable_abs_clusterCoeff_of_kp`). This also sharpens
      nonvanishing (`Z_ne_zero_of_kp`) to positivity.

- [x] **Weights in a normed field**: the Dobrushin, Kotecký–Preiss and
      Fernández–Procacci criteria now hold for weights in any normed
      field, so **complex weights** — the case contour activities take —
      are covered. Statement shapes and theorem names are unchanged, and
      nothing downstream needed touching: over `ℝ` the norm and the
      absolute value are definitionally equal. The alternating-gas
      lemmas stay real, since they carry order arguments (positivity,
      monotonicity, submultiplicativity) that a normed field has no room
      for.
- [x] **Symmetry of the Ursell function**: `ursellSum_image_equiv` —
      a bijection of the vertex set leaves the alternating sum
      unchanged — hence `ursellInt_comp_perm`: the Ursell function
      depends on the tuple only up to reordering.
- [x] **Locality**: under the Kotecký–Preiss condition, removing a
      single polymer changes the cluster series, and hence `log Z`, by
      at most `|w γ₀| · exp (a γ₀)` — independently of the volume
      (`abs_clusterSeries_sub_erase_le_of_kp`,
      `abs_log_Z_sub_erase_le_of_kp`). This is the two-sided sharpening
      of `Z_ratio_bound_of_kp` and the form in which truncation errors
      are controlled in renormalisation group arguments. Together with
      `abs_clusterSeries_le_of_kp` it also re-derives the volume-linear
      bound `|log Z| ≤ Σ_Λ |w| · exp a` from the series, which the
      telescoping induction already gave — the two routes agree.
- [x] **The analytic layer over complex weights**: the cluster series,
      the exponential formula, the sharp Kotecký–Preiss estimate and
      locality now all hold for weights in any `RCLike` field, that is
      for `ℝ` and `ℂ` alike. `clusterOrderSum`, `clusterCoeff` and
      `clusterSeries` take values in the field while every bound stays
      real and norm-based. `Real.exp` is replaced by `NormedSpace.exp`
      in the general statement, with `Real.exp` and `Complex.exp`
      corollaries bridged by `Real.exp_eq_exp_ℝ` and
      `Complex.exp_eq_exp_ℂ` (`exp_clusterSeries_eq_Z`,
      `exp_clusterSeries_eq_Z_of_kp`,
      `exp_clusterSeries_eq_Z_of_kp_complex`). For complex weights `Z`
      has no logarithm, so `Z = exp (clusterSeries)` is the sharp form
      of the statement — and it gives nonvanishing on the nose.
      `Real.log`-valued results (`log_Z_eq_clusterSeries_of_kp`,
      `abs_log_Z_le_of_kp`, `abs_log_Z_sub_erase_le_of_kp`) and the
      positivity `Z_pos_of_kp` stay real, as they must.

      `RCLike`, not a general normed field, is the right hypothesis
      here: the proof needs `‖(m : K)‖ = |m|` for integer casts —
      the Ursell function is integer-valued — and that fails in, say,
      a `p`-adic field.
- [x] **The thermodynamic limit**: summing the locality bound over the
      polymers that are added gives the **volume-difference bound**
      `‖clusterSeries Λ' − clusterSeries Λ‖ ≤ Σ_{γ ∈ Λ' \ Λ} ‖w γ‖ · exp (a γ)`
      for `Λ ⊆ Λ'` (`norm_clusterSeries_sub_le_of_gkp`), which depends
      on neither volume. Under the **global** Kotecký–Preiss condition
      (`GlobalKPCondition` — the same inequality, uniformly over all
      finite volumes, hence `KPCondition` in each of them) together with
      summability of `Σ_γ ‖w γ‖ · exp (a γ)` over the whole index type,
      the net `Λ ↦ clusterSeries Λ` is Cauchy along `Finset.atTop` and
      therefore converges (`cauchySeq_clusterSeries_of_gkp`,
      `exists_tendsto_clusterSeries_of_gkp`); for real weights that is
      the convergence of `log Z Λ` (`exists_tendsto_log_Z_of_gkp`) — the
      free energy exists. The limit inherits the volume-linear bound
      (`norm_limit_le_of_gkp`) and, in the form needed to trade a finite
      volume for the limit in an estimate, the tail bound
      `‖L − clusterSeries Λ‖ ≤ Σ'_γ − Σ_{γ ∈ Λ}` (`norm_limit_sub_le_of_gkp`).
- [x] **The fugacity expansion and analyticity of the pressure**: an
      order-`n` cluster has `n + 1` polymers, so scaling all weights by a
      fugacity `z` scales the order-`n` term by `z^(n+1)`
      (`clusterOrderSum_scale`) — the cluster series is a genuine power
      series in `z` whose coefficients do not depend on `z`
      (`fugacityCoeff`). The Kotecký–Preiss condition survives scaling by
      `‖z‖ ≤ 1` (`KPCondition.scale`), so everything proved so far holds
      on the whole closed unit disc, and the power series has radius of
      convergence `≥ 1` (`one_le_radius_fugacitySeries`) — **uniformly in
      the volume**. Hence `z ↦ clusterSeries (z·w) Λ` is analytic on the
      open disc (`hasFPowerSeriesOnBall_clusterSeries`,
      `analyticOnNhd_clusterSeries`), and for real weights so is
      `log Z` (`analyticOnNhd_log_Z`).
- [x] **Analyticity of the free energy in the thermodynamic limit**: the
      volume-difference bound is uniform in `z` on the disc
      (`norm_clusterSeries_scale_sub_le_of_gkp`), so the convergence to
      the limit is uniform there (`tendstoUniformlyOn_clusterSeries`).
      By the Weierstrass convergence theorem the limit is holomorphic,
      hence analytic: `AnalyticOnNhd ℂ (clusterLimit P w) (eball 0 1)`
      (`analyticOnNhd_clusterLimit`). In the Kotecký–Preiss regime the
      pressure is an analytic function of the activity — no phase
      transition. This is the payoff of every volume-independent bound
      proved along the way.
- [x] **Worked example, against vacuity** (`KPLean/Examples.lean`).
      Theorems about an unsatisfiable hypothesis are true and worthless,
      so the hypotheses are exhibited: in the *free* polymer system,
      where only a polymer is incompatible with itself, `Z` is
      `∏ (1 + w γ)` (`Z_freeSystem`, an end-to-end test of the
      definition of `Z`), the Kotecký–Preiss condition reduces to
      `‖w γ‖ · e ≤ 1` (`globalKP_freeSystem`), and `w n = e⁻¹ · 2⁻ⁿ`
      on `ℕ` satisfies it summably. Every headline theorem is then
      applied to that system.

      Writing the example exposed a real defect: the downstream theorems
      had `Classical.propDecidable` baked into their statements, so none
      of them could be applied to a concrete polymer type, which has its
      own `DecidableEq` instance. Fixed by carrying `[DecidableEq ι]` as
      a section variable through the whole chain.

## Next

Nothing scheduled. The convergence machinery the roadmap set out to
formalise is complete and `sorry`-free: the three criteria, the
tree–graph bound, the Mayer expansion, the cluster factorisation, the
exponential formula, the sharp Kotecký–Preiss estimate, the
identification of `log Z` with the cluster series under that same
condition, locality, the thermodynamic limit, and analyticity of the
free energy in the fugacity.

Everything is stated over `ℝ` and `ℂ` alike, so contour activities are
covered.

Natural continuations, in rough order of size: the translation-invariant
setting, where the free energy *density* and its limit make sense;
derivatives of the pressure — the correlation functions — for which the
power series is now available; and, further out, the Balaban-style
renormalisation group estimates this infrastructure was built for.

## Beyond

The convergence machinery above is the workhorse estimate behind
rigorous renormalisation group arguments. The longer-term target is a
machine-checked treatment of Balaban's method, in the sense of the
expositions by Dimock (arXiv:1108.1335, 1212.5562, 1304.0705).

Contributions and corrections are welcome; please open an issue.
