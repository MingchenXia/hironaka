# Hironaka

Lean 4 / Mathlib proofs of principalization and resolution of singularities
in complex-analytic geometry, including canonical marked-ideal resolution,
and de Jong's alteration theorem for schemes over every field.

Each finite global result states its hypotheses, including any compactness
or common stage bounds.
See the [public API](docs/API.md) for the geometric setting and precise hypotheses.
The noncompact embedded resolution uses a proper projection with a locally
finite atlas of certified finite histories. See the [current scope](STATUS.md).
The [de Jong API](docs/DEJONG.md) applies to integral separated finite-type
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
The proof is part of the Hironaka library under `Hironaka.Algebra` and
`Hironaka.Geometry`. See [source provenance and verification](docs/DEJONG.md#source-and-verification).

The build treats warnings in Hironaka as errors.

The library uses the standard axioms `propext`, `Classical.choice` and
`Quot.sound`, with no custom axioms or proof placeholders.
Verification records are kept in [audit/](audit/).

## Documentation

- [Public API and geometric setting](docs/API.md)
- [De Jong alterations over arbitrary fields](docs/DEJONG.md)
- [Verified scope and remaining gaps](STATUS.md)
- [Mathematical blueprint](blueprint/extensions.tex)
- [Intrinsic comparison and noncompact embedded resolution](blueprint/g1-g8.tex)

## Contributors

- Mingchen Xia
- Jian Wang
- Siqi He

Released under [Apache 2.0](LICENSE). Original modules credit Claude;
continuation modules retain their contributor credits.
