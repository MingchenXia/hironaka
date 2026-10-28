# Hironaka

Lean 4 / Mathlib proofs of principalization and resolution of singularities
in complex-analytic geometry, including canonical marked-ideal resolution,
and de Jong's alteration theorem for schemes over every field.

Finite global results assume the compactness conditions stated in each theorem.
See the [public API](docs/API.md) for the geometric setting and precise hypotheses.
These compactness conditions concern the original complex-analytic API. The
separate [de Jong API](docs/DEJONG.md) applies to integral separated finite-type
schemes over arbitrary, possibly imperfect fields.

## Build and use

The project pins Lean 4.33.1 and Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`.

```sh
python3 scripts/check_dejong_source.py
lake exe cache get
lake build
lake test
```

```lean
import Hironaka
```

The algebraic alteration API can also be imported separately:

```lean
import Hironaka.DeJong

#check Hironaka.deJongAlterationTheorem
#check Hironaka.exists_alterationWithBoundary
```

For any prescribed proper closed subset, it produces a genuine alteration,
a regular projective compactification, and the complete strict normal-crossings
boundary. No perfectness or geometric-integrality assumption is required.
The proof is supplied by the local vendored `DeJongAlterations` package; see
[source provenance and verification](docs/DEJONG.md#source-and-verification).

Warnings in the root `Hironaka` package are treated as errors by its build
configuration. The unmodified vendored proof retains its upstream warnings;
their inventory is recorded with the integration checks. Use the commands above
without applying a global `--wfail` to dependencies.

The library uses the standard axioms `propext`, `Classical.choice` and
`Quot.sound`, with no custom axioms or proof placeholders.
Verification records are kept in [audit/](audit/).

## Documentation

- [Public API and geometric setting](docs/API.md)
- [De Jong alterations over arbitrary fields](docs/DEJONG.md)
- [Verified scope and remaining gaps](STATUS.md)
- [Mathematical blueprint](blueprint/extensions.tex)

Released under [Apache 2.0](LICENSE). Original modules credit Claude;
continuation modules retain their contributor credits.
