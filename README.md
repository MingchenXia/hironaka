# Hironaka

Lean 4 / Mathlib proofs of principalization and resolution of singularities
in complex-analytic geometry, including canonical marked-ideal resolution.

Finite global results assume the compactness conditions stated in each theorem.
See the [public API](docs/API.md) for the geometric setting and precise hypotheses.

## Build and use

The project pins Lean 4.33.1 and Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`.

```sh
lake exe cache get
lake build --wfail
lake test
```

```lean
import Hironaka
```

The library uses the standard axioms `propext`, `Classical.choice` and
`Quot.sound`, with no custom axioms or proof placeholders.
Verification records are kept in [audit/](audit/).

## Documentation

- [Public API and geometric setting](docs/API.md)
- [Verified native scope and synchronization status](STATUS.md)
- [Mathematical blueprint](blueprint/extensions.tex)

Released under [Apache 2.0](LICENSE). Original modules credit Claude;
continuation modules retain their contributor credits.
