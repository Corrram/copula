# Read the formal statements

The API reference is generated directly from the Lean library by `doc-gen4`.
It displays declarations, assumptions, documentation comments, imports,
and links to source code.

<p><a class="md-button md-button--primary" href="../api/Copula.html">Open the Copula API</a>
<a class="md-button" href="../api/search.html">Search declarations</a></p>

## A simple reading workflow

1. Start with a theorem in the [handbook](handbook/foundations.md).
2. Follow **Formal statement** to inspect every assumption and the precise
   conclusion. The displayed signature is authoritative for the formal result.
3. Follow **Source and proof** to read the Lean proof.
4. To inspect intermediate proof states, open that source file locally in
   VS Code with the Lean extension. Move the cursor through the proof to
   see the assumptions and goals in the Infoview.

The handbook search and API search serve different purposes: handbook search
finds explanations, while API search finds declaration names across Copula
and the dependencies documented with it. For Copula-specific results, try
`ProbabilityTheory.Copula`, `ordinalSum`, or `spearmanRho`.

## Reading common Lean notation

| Lean | Mathematical reading |
| --- | --- |
| `(C : Copula 2)` | Let $C$ be a bivariate copula. |
| `(a : I)` | Let $a\in[0,1]$. |
| `(ha0 : 0 < a)` | Assume $a>0$. |
| `C.cdf ![u, v]` | $C(u,v)$. |
| `P ↔ Q` | $P$ if and only if $Q$. |
| `∃! x, P x` | There exists exactly one $x$ satisfying $P$. |
| `∀ᵐ x ∂C.toMeasure, P x` | $P$ holds almost surely under the copula law. |
| `:= by` | The formal proof begins here. |

The generated API contains **Lean notation**, not an automatic translation
into prose. The handbook supplies mathematical explanations while keeping
the formal declaration one click away.

## Mathlib

The documentation build includes imported mathlib declarations at the
version used by this package. For the latest upstream library, use
[mathlib's own documentation](https://leanprover-community.github.io/mathlib4_docs/).
Its latest version may differ from the one pinned by Copula.
