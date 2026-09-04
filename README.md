# Cluster expansions in Lean 4

A formalisation of the convergence core of the cluster expansion method
for abstract polymer systems, built on
[mathlib](https://github.com/leanprover-community/mathlib4).
There are no `sorry`s in this repository.

## The problem

An abstract polymer system consists of a finite set Λ of *polymers*, a
symmetric and reflexive *incompatibility* relation, and *weights*
`w γ`. The partition function

```
Z Λ = Σ_{S ⊆ Λ pairwise compatible} Π_{γ ∈ S} w γ
```

is the basic object of rigorous statistical mechanics in its polymer
formulation: lattice gases, contour models of phase transitions, and the
effective activities produced at each step of a renormalisation group
analysis all take this shape. Every use of the method rests on the same
analytic question:

> Under which explicit, checkable conditions on the weights is
> `Z Λ ≠ 0`, with quantitative control of how `Z` changes when a polymer
> is removed, and with bounds on `log |Z Λ|` that grow at most linearly
> in the volume — uniformly in Λ?

Nonvanishing is what makes `log Z` and ratios of partition functions
well-defined; the ratio and log bounds are the input to thermodynamic
limits, analyticity of free energies, and the convergence estimates of
the expansion. This repository machine-checks the three classical
answers — the criteria of Kotecký–Preiss, Dobrushin, and
Fernández–Procacci — together with the recursion they all rest on, and
the cluster series itself: Ursell functions, the Penrose tree–graph
bound, the Mayer expansion with its finite cluster recursion, the
exponential formula identifying `log Z` with the cluster series, the
sharp Kotecký–Preiss summability estimate, and the locality of `log Z`
under removal of a single polymer. Weights may be real or complex
throughout.

## Main results

All in `KPLean/ClusterExpansion.lean`, namespace `ClusterExpansion`:

- the **fundamental deletion recursion**

  `Z Λ = Z (Λ \ {γ}) + w γ * Z (Λ \ N*(γ))`

  (`Z_recursion`), proved for weights in an arbitrary commutative ring;

**Complex weights are covered throughout.** The three criteria hold for
weights in an arbitrary **normed field**; the cluster series, the
exponential formula, the sharp estimate and locality hold over any
`RCLike` field, that is over `ℝ` and `ℂ` alike. The comparison
functions `μ`, `a` and every bound stay real. Over `ℝ` the norm and the
absolute value coincide definitionally, so the real statements are
literally the `K = ℝ` case.

- the **Dobrushin criterion** (product form): if `μ ≥ 0` and
  `|w γ| * ∏_{δ ≁ γ} (1 + μ δ) ≤ μ γ` for every polymer `γ` in `Λ`, then
  `Z Λ ≠ 0` (`Z_ne_zero_of_dobrushin`) and deleting a polymer changes
  `|Z|` by at most the factor `1 + μ γ`
  (`Z_ratio_bound_of_dobrushin`);

- the **Kotecký–Preiss criterion** (sum form): if `a ≥ 0` and
  `Σ_{δ ≁ γ} |w δ| * exp (a δ) ≤ a γ` for every `γ` in `Λ`, then
  `Z Λ ≠ 0` (`Z_ne_zero_of_kp`) with the classical ratio bound
  `|Z (Λ \ {γ})| ≤ exp (a γ) * |Z Λ|` (`Z_ratio_bound_of_kp`) —
  obtained from the product form via the comparison
  `μ γ = |w γ| * exp (a γ)` and `1 + x ≤ exp x`
  (`KPCondition.dobrushin`);

- **volume-linear control of the logarithm**: two-sided bounds
  `(∏ (1 + μ γ))⁻¹ ≤ |Z Λ| ≤ ∏ (1 + μ γ)`
  (`prod_inv_le_abs_Z_of_dobrushin`, `abs_Z_le_prod_of_dobrushin`),
  hence `|log |Z Λ|| ≤ Σ log (1 + μ γ) ≤ Σ μ γ`
  (`abs_log_abs_Z_le_of_dobrushin`, `abs_log_abs_Z_le_sum_of_dobrushin`),
  and in Kotecký–Preiss form
  `|log |Z Λ|| ≤ Σ |w γ| * exp (a γ)` (`abs_log_abs_Z_le_of_kp`);

- the **Fernández–Procacci criterion**, the sharpest of the three: the
  FP condition (`FPCondition`) replaces the Dobrushin product by the
  independence polynomial of the neighbourhood — which is `Z` itself at
  the weights `μ` — and still implies `Z Λ ≠ 0`
  (`Z_ne_zero_of_fp`) with the ratio bound
  `|Z (Λ \ {x})| ≤ (1 + μ x) * |Z Λ|` (`Z_ratio_bound_of_fp`). The
  proof follows the inductive argument of Fialho (J. Stat. Phys. 178,
  2020): positivity of the alternating gas `Z(-|w|)`
  (`Z_neg_pos_of_fp`), via submultiplicativity of the independence
  polynomial (`Z_union_le_mul`), followed by the comparison
  `Z(-|w|) ≤ |Z(w)|` in the style of Scott–Sokal;

- the **hierarchy of hypotheses** KP ⟹ Dobrushin ⟹ Fernández–Procacci
  (`KPCondition.dobrushin`, `DobrushinCondition.fp`, `KPCondition.fp`)
  via `Z_A(μ) ≤ ∏_{δ ∈ A} (1 + μ δ)` (`Z_le_prod_one_add`); since the
  FP condition is the weakest, nonvanishing under FP subsumes the other
  two criteria;

- **Ursell functions and the Penrose tree–graph bound**
  (`KPLean/Ursell.lean`): the Ursell function of a polymer tuple as the
  alternating sum over connected spanning subgraphs of its
  incompatibility graph (`ursellInt`, with the sanity values
  `φᵀ(γ₁) = 1` and `φᵀ(γ₁, γ₂) = −1`), and the tree–graph inequality

  `|φᵀ(γ₁, …, γₙ)| ≤ #{spanning trees of the incompatibility graph}`

  (`abs_ursellInt_le_treeCount`, from the general
  `abs_ursellSum_le_treeCount`). The proof formalises **Penrose's
  partition scheme**: a BFS layer structure from a fixed root assigns to
  every connected spanning subgraph a spanning tree (`penroseTree`, each
  vertex hanging on its least neighbour in the layer below), the fibres
  of this map are set intervals `[T, penroseExt H T]`, and the
  alternating sum vanishes on every nontrivial interval — so at most one
  `±1` survives per spanning tree;

- **the Mayer expansion and the finite cluster recursion**
  (`KPLean/Mayer.lean`), over any commutative ring: the graph expansion

  `Z Λ = Σ_{S ⊆ Λ} (Π_{γ ∈ S} w γ) · Σ_{G ⊆ E(S)} (−1)^{|G|}`

  (`Z_eq_sum_graphs`, where `E(S)` are the incompatibility edges inside
  `S` — the inner alternating sum replaces the independence indicator),
  and, splitting each Mayer pair `(S, G)` along the connected component
  of a fixed polymer `γ₀`, the **cluster recursion**

  `Z Λ = Z (Λ ∖ {γ₀}) + Σ_{γ₀ ∈ B ⊆ Λ} (Π_{γ ∈ B} w γ) · φ(B) · Z (Λ ∖ B)`

  (`Z_cluster_recursion`), with `φ(B)` the set-level Ursell sign sum
  over connected spanning subgraphs of `B`'s incompatibility graph
  (`ursellSetSum`; `φ({γ}) = 1`, `φ({γ, δ}) = −1` for an incompatible
  pair). This is the finite exponential structure of the cluster
  expansion: iterating it generates the cluster series of `log Z`.
  The closed iterate is proved as the **cluster factorisation**

  `Z Λ = Σ_C Π_{B ∈ C} (Π_{γ ∈ B} w γ) · φ(B)`

  over all collections `C` of pairwise disjoint nonempty clusters in
  `Λ` (`IsClusterCollection`, `Z_eq_sum_clusterCollections`) — the
  finite exponential formula in set form; and the **bridge lemma**
  `ursellInt_eq_ursellSetSum` identifies the tuple-level Ursell
  function of an injective tuple with the set-level sign sum of its
  image;

- **the cluster series as a convergent analytic object**
  (`KPLean/ClusterSeries.lean`): the series

  `clusterSeries = Σ'_{n} (1/(n+1)!) Σ_{(γ₁, …, γ_{n+1}) ∈ Λ^{n+1}} φᵀ(γ) Π w(γᵢ)`

  as a genuine `tsum` (`clusterOrderSum`, `clusterCoeff`,
  `clusterSeries`), with the **root-tree bound**
  `|φᵀ(γ₁, …, γ_{n+1})| ≤ (n+1)ⁿ` (`abs_ursellInt_le_pow`, from
  `treeCount_le_pow`: a spanning tree is its own Penrose tree, so trees
  are determined by their parent maps), the geometric term bound
  `|clusterCoeff n| ≤ (e Σ_Λ |w|)^{n+1}` (`abs_clusterCoeff_le`), and
  absolute convergence with tail bound `r/(1−r)` in the small-weight
  regime `e · Σ_{γ ∈ Λ} |w γ| < 1` (`summable_clusterCoeff`,
  `abs_clusterSeries_le`). The series anchored at a fixed polymer `γ₀`
  is bounded by `e |w γ₀| / (1 − e Σ_Λ |w|)`, proportionally to the
  anchor weight and uniformly in the volume (`tsum_pinned_le`) — the
  crude form of the Kotecký–Preiss summability over clusters;

- **the exponential formula** (`KPLean/Exponential.lean`): in the
  small-weight regime `e · Σ_{γ ∈ Λ} ‖w γ‖ < 1`,

  `Z Λ = exp (clusterSeries P w Λ)`, hence `log Z Λ = clusterSeries`

  (`exp_clusterSeries_eq_Z`, `log_Z_eq_clusterSeries`), with
  `Z Λ > 0` as a by-product (`Z_pos_of_small`). The convergent series
  of the previous item is thereby identified with `log Z` itself, so
  `abs_clusterSeries_le` becomes a bound on `log Z`. The proof runs
  through the polymer system pulled back along an assignment
  (`PolymerSystem.pull`) with the tuple sums `tupleZ`, `tupleU` built on
  it, and four identities linking them to `Z` and to the series —

  `[Indep Q A] = Σ_{partitions of A} Π φ(B)`
  (`indep_indicator_eq_sum_partitions`, by comparing degree-`|A|`
  coefficients in the cluster factorisation over `Polynomial ℤ`),

  `tupleZ K = Σ_{partitions of K} Π tupleU B`
  (`tupleZ_eq_sum_partitions`, block decomposition of pinned assignment
  sums), `tupleU B = clusterOrderSum (|B| − 1)`
  (`tupleU_eq_clusterOrderSum`, via the order isomorphism `Fin |B| ≃ B`
  and the bridge lemma), and `Z = Σ_m tupleZ_m / m!`
  (`tupleZ_univ_eq`, `Z_eq_sum_tupleZ`, counting the fibres of
  assignments by embeddings) — together with the analytic step
  `exp_tsum_eq`, which expands `exp` of an absolutely convergent series
  into compositions grouped by total weight, and the **multinomial
  count** `sum_partitionsOf_card`: ordered partitions with size profile
  `c` number `|A|!/Π cᵢ!` and unordered ones a further `k!` fewer. That
  count is proved from scratch — Mathlib's `Multiset.bell` is *defined*
  multinomially, and the statement that it counts partitions is an
  explicit TODO there.;

- **the sharp Kotecký–Preiss summability estimate**
  (`KPLean/SharpKP.lean`): under the Kotecký–Preiss condition
  `Σ_{δ ≁ γ} |w δ| exp (a δ) ≤ a γ`, the anchored absolute series of the
  cluster expansion satisfies

  `Σ'_n pinnedOrderSum(γ₀, n)/n! ≤ |w γ₀| · exp (a γ₀)`

  (`tsum_pinned_le_of_kp`), uniformly in the volume and with no
  smallness hypothesis. The point that makes this affordable is the
  representation of trees by their **parent maps**: a bound needs only
  an injection from spanning trees into parent maps, which the Penrose
  scheme already provides (`treeCount_le_card_rootedTrees`), so neither
  Cayley's formula nor the Prüfer correspondence — absent from Mathlib —
  is needed. The proof decomposes a rooted tree at its root
  (`subtreeOf_image_mem_partitionsOf`), peels off one block at a time
  (`treeSum_le_peel`), uses relabelling invariance
  (`treeSum_eq_treeCoeff`) and the multinomial count carried over from
  the exponential formula, and closes by induction on the truncation
  height (`treeTrunc_le_exp`);

- **the exponential formula under that same condition**
  (`KPLean/KPExponential.lean`): summing the sharp anchored bound over
  the anchors shows the cluster series converges absolutely under the
  Kotecký–Preiss condition, with constant `Σ_{γ ∈ Λ} |w γ| exp (a γ)`
  (`summable_abs_clusterCoeff_of_kp`) — the same volume-linear quantity
  that already bounded `|log |Z||`. Since smallness entered the
  exponential formula only through convergence, this gives

  `Z Λ = exp (clusterSeries)`, `log Z Λ = clusterSeries`, `Z Λ > 0`

  (`exp_clusterSeries_eq_Z_of_kp`, `log_Z_eq_clusterSeries_of_kp`,
  `Z_pos_of_kp`) under the Kotecký–Preiss condition alone. So the very
  condition under which the classical criteria give `Z ≠ 0` also makes
  the cluster series the exact expansion of `log Z`, and sharpens
  nonvanishing to positivity. The identity `Z = exp (clusterSeries)` is
  stated with `NormedSpace.exp` and holds over `ℝ` and `ℂ` alike, with
  `Real.exp` and `Complex.exp` corollaries
  (`exp_clusterSeries_eq_Z_of_kp_real`,
  `exp_clusterSeries_eq_Z_of_kp_complex`). For complex weights there is
  no logarithm to take, and `Z = exp (…)` is the sharp form of the
  statement — nonvanishing follows on the nose;

- **symmetry and locality** (`KPLean/UrsellSymmetry.lean`,
  `KPLean/Locality.lean`): a bijection of the vertex set leaves the
  Ursell sum unchanged (`ursellSum_image_equiv`), so the Ursell
  function depends on its tuple only up to reordering
  (`ursellInt_comp_perm`). That symmetry lets a cluster containing `γ₀`
  anywhere be reduced to one anchored at `γ₀`, at the price of a factor
  `n + 1` which the factorial absorbs
  (`abs_clusterOrderSum_sub_le`). Hence **locality**: under the
  Kotecký–Preiss condition, removing one polymer from the volume
  changes the cluster series — and therefore `log Z` — by at most

  `‖w γ₀‖ · exp (a γ₀)`

  independently of `Λ` (`abs_clusterSeries_sub_erase_le_of_kp`,
  `abs_log_Z_sub_erase_le_of_kp`). This is the two-sided sharpening of
  the ratio bound `Z_ratio_bound_of_kp`, and the form in which
  truncation errors are controlled in renormalisation group arguments.

The hierarchy is strict: a single self-incompatible polymer of weight
`1/2` satisfies the Dobrushin condition with `μ = 1`, while
`e^a / 2 ≤ a` has no solution. An earlier version of this repository
claimed that the sum form was not obtainable from the product form; the
formalisation of the comparison argument refuted that claim, and the
episode is documented in the accompanying note in [`paper/`](paper/).

## Building

Install [elan](https://github.com/leanprover/elan), then:

```
lake exe cache get
lake build
```

The toolchain (`lean-toolchain`) and the mathlib revision
(`lake-manifest.json`) are pinned; the build is checked by CI.

## Repository layout

| Path | Contents |
| --- | --- |
| `KPLean/ClusterExpansion.lean` | polymer systems, `Z`, the recursion, the Dobrushin and Kotecký–Preiss criteria, log-bounds, the FP hierarchy |
| `KPLean/Ursell.lean` | Ursell functions, the Penrose partition scheme, the tree–graph bound |
| `KPLean/Mayer.lean` | Mayer expansion, the finite cluster recursion, the bridge lemma, the cluster factorisation |
| `KPLean/ClusterSeries.lean` | the cluster series, the root-tree bound, convergence and anchored bounds in the small-weight regime |
| `KPLean/Exponential.lean` | pulled-back polymer systems, tuple sums, the partition identity, block decomposition and reduction, the layer count, the analytic exponential step |
| `KPLean/Trees.lean` | rooted trees as parent maps, subtrees, the weighted tree sum and its coefficients |
| `KPLean/TreeDecomp.lean` | decomposition of a rooted tree at its root; peeling a block off a partition sum |
| `KPLean/TreePeel.lean` | the peel inequality for tree sums, by fibring over the block of a fixed vertex |
| `KPLean/TreeRelabel.lean` | relabelling invariance of the tree sum |
| `KPLean/TreeLink.lean` | the tree–graph bound in parent-map form |
| `KPLean/SharpKP.lean` | the recursion inequality, the Kotecký–Preiss induction, the sharp estimate |
| `KPLean/KPExponential.lean` | convergence of the cluster series under the KP condition, and `log Z = clusterSeries` there |
| `KPLean/UrsellSymmetry.lean` | invariance of the Ursell sum under relabelling; symmetry of the Ursell function |
| `KPLean/Locality.lean` | the volume-independent effect of removing one polymer on `log Z` |
| `paper/kp-formalisation.tex` | LaTeX note describing the formalisation |

## Background

Cluster expansions control the logarithm of polymer partition functions
and are a basic tool of rigorous statistical mechanics and constructive
field theory; see Kotecký–Preiss (Comm. Math. Phys. 103, 1986),
Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (CUP, 2017),
Chapter 5, Scott–Sokal (J. Stat. Phys. 118, 2005), and
Fernández–Procacci (Comm. Math. Phys. 274, 2007) for the criteria
treated here; the formalised proof of the Fernández–Procacci criterion
follows the inductive argument of Fialho
([arXiv:2001.00652](https://arxiv.org/abs/2001.00652), J. Stat. Phys.
178, 2020). The tree–graph bound goes back to Penrose, *Convergence of
fugacity expansions for classical systems* (in *Statistical Mechanics:
Foundations and Applications*, Benjamin, 1967); the partition-scheme
view is as in Scott–Sokal, §2.2. The longer-term aim of this project is machine-checked
infrastructure for the convergence estimates used in rigorous
renormalisation group analyses of lattice field theories, in the sense
of the expositions of Balaban's method by Dimock (arXiv:1108.1335,
1212.5562, 1304.0705).

## Origin

This repository is the residue of a boundary-drawing exercise. It grew
out of DEGRALBA (*Dimensionserweiterte graduierte Algebra*), a private
research notebook on a graded arithmetic in which division by zero is
total and deficits book as surplus one level up; an interactive
companion is published as
[Stufenrechnung](https://claude.ai/code/artifact/d5fd412a-d671-4fa7-aace-935635f8669a).
The notebook's final section asks which open problems such a system
could and could not attack, and answers honestly: none of the famous
ones. What survived that exercise was the question of the smallest step
toward constructive field theory that can be machine-checked today with
no overclaiming — and the answer was: the convergence criteria of the
cluster expansion, the workhorse estimate behind every rigorous
renormalisation group argument. Formalising them promptly falsified one
of our own claims (see above), which we take as the method working as
intended.

## Roadmap

Every milestone the roadmap set out is formalised, up to and including
locality and the carry-over of the analytic layer to complex weights.
See
[`ROADMAP.md`](ROADMAP.md) for the full list with the relevant theorem
names, and for the natural continuations.

Contributions and corrections are welcome; please open an issue.

## Citation

```bibtex
@misc{heine2026cluster,
  author = {Heine, Dennis Michael},
  title  = {Cluster expansions in Lean 4},
  year   = {2026},
  url    = {https://github.com/24high/cluster-expansion-lean}
}
```

## License

Copyright (c) 2026 Dennis Michael Heine. Released under the
[CC BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/)
license; the full legal code is in [LICENSE](LICENSE). Note that this
license is not compatible with mathlib's Apache 2.0; a relicensing of
individual lemmas would be required before any upstreaming.

## Acknowledgements

The formalisation was produced with substantial assistance from an AI
system (Claude, Anthropic), including proof drafting and literature
checks. All errors are the author's.
