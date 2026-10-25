import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Etale.StandardEtale
import DeJongAlterations.StableModification.Valuation.Bounded

/-!
# The valuation-theoretic input of Temkin's §4: the interface statement (M3)

This file states, as a proposition (`UniformizationEtaleStatement`), the form of Temkin's
*uniformization of one-dimensional valued fields* that the curve part of the stable modification
theorem consumes. It is an **interface, not a theorem**: nothing here is proved about it. The
curve lanes may assume `UniformizationEtaleStatement` as a hypothesis while its proof (plan
`PLAN-SM-VAL.md`, node M3, from Theorem 2.1.8 and Lemma 2.1.1 of the source) is in progress.

Source: M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010),
`references/temkin10-stable-modification/source/semi-stable.tex`:

* Theorem 2.1.8 (`valunif`, l. 2056–2061): let `L/K` be a finitely generated extension of valued
  fields of transcendence degree one, with `K` separably closed, such that the valuation ring
  `K·O` is centred on a smooth point of the normal projective `K`-model of `L`. Then there is a
  transcendence basis `{T}` of `L/K` such that `L/K(T)` is unramified.
* Lemma 2.1.1 (`finhtlem`, l. 1904–1915) and Lemma 2.1.6 (`etalelem`, l. 2035–2043): over a
  valuation ring of finite height, "unramified" upgrades to "étale".
* The consumer, Proposition 4.3.3 (`locunifprop`, l. 3048–3081, the call is l. 3059–3061):
  "there exists an element `T ∈ L` such that `L` is unramified over `K(T)`, and so `O` is étale
  over `O ∩ K(T)` by Lemma 2.1.1".

## The hypotheses (`UniformizationHypotheses K L O`)

* `K` is separably closed and `O ∩ K` has finite height (finitely many primes). In the consumer
  `O ∩ K` is a localization of the base valuation ring `R`, of height at most `dim S`.
* `K` and the residue field of `O ∩ K` have the same exponential characteristic
  (equicharacteristic; automatic when the valuation is trivial on a ground field `k₀ ⊆ K`, which is
  always the case for de Jong's bases of finite type over a field, plan §2).
* `L/K` is finitely generated and has a separating transcendence element `x`: `L` is separable
  algebraic over `K(x)`. Hence `trdeg (L/K) = 1` (`UniformizationHypotheses.trdeg_eq_one`). This
  is the separability of `L/K` coming from the smoothness of the generic fibre `C_η`.
* Centre condition (Temkin's "`K·O` is centred on a smooth point"): either `K·O = L` (the generic
  point, `L/K` bounded) or `K·O` is a discrete valuation ring whose residue field is `K` (a smooth
  closed point of a curve over the separably closed field `K`). Here `K·O` is
  `baseLocalization K O`, the localization of `O` at the nonzero elements of `O ∩ K`.

## The conclusion (`UniformizationConclusion K L O`)

There is `T ∈ L`, transcendental over `K`, such that `O` is a **standard étale** algebra over
`O ∩ K(T)` (Mathlib's `Algebra.IsStandardEtale`: `O ≅ (O ∩ K(T))[X]_g/(f)` with `f` monic and
`f'` invertible), in particular étale (`UniformizationConclusion.exists_etale`). The algebra
structure is the inclusion `O ∩ K(T) → O` (`instAlgebraComap`).

This is the statement M3 of `PLAN-SM-VAL.md` §9.1 with the Mathlib forms fixed: `hfg` is
`(⊤ : IntermediateField K L).FG`, `hsep` is a separating transcendence element, `htr` is
derived, and the conclusion is the standard étale form (the plan's "explicit
`IsStandardEtale`-localization form").
-/

noncomputable section

open IsLocalRing

namespace DeJongAlterations.StableModification.Valuation

universe u v

/-- The hypotheses of the consumer form of Temkin's Theorem 2.1.8 (`semi-stable.tex`
l. 2056–2061, as used at l. 3059–3061), for a field extension `L/K` and a valuation subring `O` of
`L`; see the module docstring. -/
structure UniformizationHypotheses (K L : Type*) [Field K] [Field L] [Algebra K L]
    (O : ValuationSubring L) : Prop where
  /-- The base field is separably closed. -/
  isSepClosed : IsSepClosed K
  /-- The valuation ring `O ∩ K` of `K` has finite height. -/
  finite_primeSpectrum : Finite (PrimeSpectrum (O.comap (algebraMap K L)))
  /-- Equal (exponential) characteristic of `K` and of the residue field of `O ∩ K`. -/
  expChar : ∃ p : ℕ, ExpChar K p ∧ ExpChar (ResidueField (O.comap (algebraMap K L))) p
  /-- `L` is finitely generated over `K` as a field. -/
  fg : (⊤ : IntermediateField K L).FG
  /-- `L` has a separating transcendence element over `K`. -/
  exists_separating :
    ∃ x : L, Transcendental K x ∧ Algebra.IsSeparable (IntermediateField.adjoin K {x}) L
  /-- Centre condition: `K·O = L`, or `K·O` is a discrete valuation ring with residue field `K`. -/
  center : baseLocalization K O = ⊤ ∨
    (IsDiscreteValuationRing (baseLocalization K O) ∧
      Function.Bijective ((residue (baseLocalization K O)).comp (toBaseLocalization K O)))

/-- The conclusion of the consumer form of Temkin's Theorem 2.1.8 combined with Lemma 2.1.1
(`semi-stable.tex` l. 3059–3061): some `T ∈ L` transcendental over `K` such that `O` is a standard
étale algebra over `O ∩ K(T)`. -/
def UniformizationConclusion (K L : Type*) [Field K] [Field L] [Algebra K L]
    (O : ValuationSubring L) : Prop :=
  ∃ T : L, Transcendental K T ∧
    Algebra.IsStandardEtale (O.comap (algebraMap (IntermediateField.adjoin K {T}) L)) O

/-- **Interface statement M3** (plan `PLAN-SM-VAL.md` §9.1): Temkin's uniformization of
one-dimensional valued fields (Theorem 2.1.8, `semi-stable.tex` l. 2056–2061) in the étale form
consumed by Proposition 4.3.3 (l. 3059–3061). This is a proposition to be proved, not an axiom;
consumers take it as a hypothesis. -/
def UniformizationEtaleStatement : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] (O : ValuationSubring L),
    UniformizationHypotheses K L O → UniformizationConclusion K L O

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {O : ValuationSubring L}

/-- The conclusion gives an étale algebra `O ∩ K(T) → O`. -/
theorem UniformizationConclusion.exists_etale (h : UniformizationConclusion K L O) :
    ∃ T : L, Transcendental K T ∧
      Algebra.Etale (O.comap (algebraMap (IntermediateField.adjoin K {T}) L)) O := by
  obtain ⟨T, hT, h⟩ := h
  exact ⟨T, hT, inferInstance⟩

/-- Under the hypotheses, `L/K` has transcendence degree one. -/
theorem UniformizationHypotheses.trdeg_eq_one (h : UniformizationHypotheses K L O) :
    Algebra.trdeg K L = 1 := by
  obtain ⟨x, hx, hsep⟩ := h.exists_separating
  have hind : AlgebraicIndependent K (fun _ : Unit ↦ x) :=
    algebraicIndependent_unique_type_iff.mpr hx
  have hrange : Set.range (fun _ : Unit ↦ x) = {x} := Set.range_const
  have halg : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range fun _ : Unit ↦ x)) L := by
    rw [hrange, ← IntermediateField.isAlgebraic_adjoin_iff_top]
    exact Algebra.IsSeparable.isAlgebraic _ _
  have hb : IsTranscendenceBasis K (fun _ : Unit ↦ x) :=
    hind.isTranscendenceBasis_iff_isAlgebraic.mpr halg
  simpa using hb.lift_cardinalMk_eq_trdeg.symm

end DeJongAlterations.StableModification.Valuation
