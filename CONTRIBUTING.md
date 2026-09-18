# Contributing

Please open an issue for substantial definition or API changes. Link related
Lean Zulip discussions, mathematical references, or mathlib issues so the
reasoning remains discoverable.

Follow [mathlib's style guide](https://leanprover-community.github.io/contribute/style.html)
and [naming conventions](https://leanprover-community.github.io/contribute/naming.html).
Keep declarations in `ProbabilityTheory.Copula`, use focused imports, document
definitions, and avoid global notation specific to this project. Add authors to
the relevant file headers when contributing substantial mathematical content.

Before submitting:

```sh
lake exe cache get
lake build
lake test
```

Proofs must be complete: no `sorry`, `admit`, or added axioms. Keep unfinished
theorems in the roadmap instead of introducing trusted placeholders. Add small
public API examples when they cover a new mathematical boundary case or
construction. In particular, check whether a theorem needs a positive dimension.

The project tracks a released mathlib version. Update `lean-toolchain`, the
mathlib revision in `lakefile.toml`, and `lake-manifest.json` together; build the
library and examples before submitting the update.

For upstreaming, first discuss the concrete definition and scope on
[Lean Zulip](https://leanprover.zulipchat.com/). Start with independently useful
generic lemmas if any are needed, then propose the basic copula definition and
small groups of results. Follow mathlib's current review guidance. Once a
result is available in the pinned mathlib version, remove its local copy and
import the upstream module. Record any required migration in the README.

Contributions are licensed under Apache 2.0, as described in [LICENSE](LICENSE).
