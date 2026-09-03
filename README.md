# Cluster expansions in Lean 4

A formalisation of the combinatorial and analytic core of the cluster
expansion method for abstract polymer systems, built on
[mathlib](https://github.com/leanprover-community/mathlib4).

The repository contains complete, machine-checked proofs of:

- the **fundamental deletion recursion** for the polymer partition function,

  `Z Λ = Z (Λ \ {γ}) + w γ * Z (Λ \ N*(γ))`

  (`ClusterExpansion.Z_recursion`), proved for weights in an arbitrary
  commutative ring;

- the **Dobrushin convergence criterion** in product form: if `μ ≥ 0` and
  `|w γ| * ∏_{δ ≁ γ} (1 + μ δ) ≤ μ γ` for every polymer `γ` in `Λ`, then
  `Z Λ ≠ 0` (`ClusterExpansion.Z_ne_zero_of_dobrushin`) and deleting a
  polymer changes `|Z|` by at most the factor `1 + μ γ`
  (`ClusterExpansion.Z_ratio_bound_of_dobrushin`).

There are no `sorry`s in this repository.

The classical Kotecký–Preiss criterion in *sum* form
(`ClusterExpansion.KPCondition`) is stated as a definition only. It is not
a corollary of the product form — the ratio-telescoping induction used here
produces products over incompatibility neighbourhoods, which a sum
hypothesis does not control — and its formalisation via the cluster-tree
induction is the next milestone. See the accompanying note in
[`paper/`](paper/) for a discussion, including a two-polymer example
separating the two criteria.

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
| `KPLean/ClusterExpansion.lean` | polymer systems, `Z`, the recursion, the Dobrushin criterion |
| `paper/kp-formalisation.tex` | LaTeX note describing the formalisation |

## Background

Cluster expansions control the logarithm of polymer partition functions and
are a basic tool of rigorous statistical mechanics and constructive field
theory; see Kotecký–Preiss (Comm. Math. Phys. 103, 1986), Friedli–Velenik,
*Statistical Mechanics of Lattice Systems* (CUP, 2017), Chapter 5, and
Scott–Sokal (J. Stat. Phys. 118, 2005) for the criterion proved here. The
longer-term aim of this project is machine-checked infrastructure for the
convergence estimates used in rigorous renormalisation group analyses of
lattice field theories, in the sense of the expositions of Balaban's method
by Dimock (arXiv:1108.1335, 1212.5562, 1304.0705).

## Roadmap

- [x] deletion recursion over commutative rings
- [x] Dobrushin criterion (product form): nonvanishing and ratio bound
- [ ] Kotecký–Preiss criterion (sum form) via the cluster-tree induction
- [ ] convergent expansion of `log Z`
- [ ] Fernández–Procacci refinement

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
system (Claude, Anthropic), including proof drafting and literature checks.
All errors are the author's.
