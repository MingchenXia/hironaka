import DeJongAlterations.StableModification.BlowDown.NoClosedExc
import DeJongAlterations.StableModification.Projectivity.Reduction

/-!
# The published statements of the global assembly

The interfaces through which the lanes of `PLAN-T5.md` (§1.3) run in parallel: the producers of
Temkin's Proposition 4.5.1 over a valuation ring (existence and uniqueness of the stable
modification, lane T45B), of Proposition 4.4.6 (the blow-down, lane T44B) and of Lemma 5.1 (ii)
(spreading of stability to an open neighbourhood, node G4) publish their results as the plain
propositions below, and the global assembly (Temkin §5, T:3379–3399, lane T5G) takes them as
hypotheses. Nothing here asserts them. Source: M. Temkin, *Stable modification of relative
curves*, J. Algebraic Geom. 19 (2010) (`references/temkin10-stable-modification/source/
semi-stable.tex`, cited `T:<line>`).

## Numerical stability

Temkin's stability (T:1687–1690, `Curves.IsStableModification`) excludes *exceptional
components*: images of closed immersions of `ℙ¹` contracted by `β` with at most two special
points (`Curves.IsExceptionalComponent`). The blow-down of Appendix B and §4.4 works numerically
(`ℙ¹`-trees are trees of components of arithmetic genus `0`), and the positivity of `ω(D')`
needed for projectivity (PLAN-OM3, M5) uses degrees. We therefore publish the numerical form
(`PLAN-T5.md` §1.3, obligation E4 of PLAN-OM3 §6):

* `NumericallyStableFibre β g D' a` (an abbreviation of lane T44A3's integrated
  `BlowDown.NoClosedExc.NumericallyStableFibre`, so that the two notions cannot diverge): every
  irreducible component `Z` of the geometric fibre `C'_a` (`a : Spec K → S`) contracted by `β_a`
  whose reduced induced subscheme `Z_red` has arithmetic genus `p_a(Z_red) = 1 − χ(𝒪_{Z_red}) = 0`
  (`CurvesField.Genus.arithmeticGenus`) contains at least three points lying on `D'` or not
  smooth in `C'_a`. The genus is only defined for quasi-compact separated `Z_red` (it is computed
  by Čech cohomology of a finite affine cover); for the proper families to which the notion is
  applied this is automatic, and the condition is stated under these instances.
* `IsNumericallyStableAt β g D' s`, `IsNumericallyStable β g D'`: the condition over the
  geometric points over `s`, resp. over all geometric points.
* `not_isExceptionalComponent_of_numericallyStableFibre`: numerical stability excludes
  exceptional components (an embedded `ℙ¹_K` is its own reduced component, of arithmetic genus
  `0`; lane T44A3's `BlowDown.NoClosedExc.not_numericallyStableFibre_of_isExceptionalComponent`).

## Producer propositions

* `IsValuationCurve φ D`: the situation of Temkin's §4.5 in our case: `C` integral, flat, of
  finite presentation and projective over a valuation ring `W`, smooth over the generic point,
  with flat marks `D` and semi-stable generic pair.
* `ValuationStableExistence` (Temkin Prop. 4.5.1 existence, T:3233–3266, with Thm 1.1 over `W`):
  over a finite-height valuation ring of equal characteristic with algebraically closed fraction
  field, a stable, numerically stable η-modification projective over `W` exists (lane T45B; the
  projectivity conjunct is obligation E5 of PLAN-OM3, in strong form).
* `ValuationStableUniqueness` (Temkin Thm 1.2 over `W` via Prop. 4.5.1, T:3233–3266):
  two such modifications are isomorphic over `C`.
* `BlowDownStable` (Temkin Prop. 4.4.6 iterated with Lemma 4.4.4, T:3158–3229; lane T44B):
  a projective semi-stable η-modification dominates (factors through) a stable and numerically
  stable one, projective over `W`.
* `StableOpenNbhd k` (Temkin Lemma 5.1 (ii), T:3282–3311, in the form used by the proof of
  Thm 1.5; node G4): numerical stability of a projective semi-stable family over one geometric
  point spreads to an open neighbourhood.

## The deliverable to the projectivity argument

* `HasLocallyProjectiveStableModification k pS g D` (`PLAN-T5.md` §1.2): obligations E1–E4 of
  PLAN-OM3 §6: an alteration `ψ : S' ⟶ S` with `S'` integral, normal and projective over `k`
  (E1), a stable η-modification `β` of `C ×_S S'` (E2) which is locally relatively projective
  over `k` in the sense of lane OM3A's integrated `Projectivity.LocallyRelativelyProjective`
  (E3) and numerically stable (E4), with finite marks and an isomorphism over a nonempty open
  of `S'` (the remaining inputs of the bridge
  `Curves.hasStableModification_of_isStableModification`).
* `StableModificationProjectivity k` (Temkin Thm 1.1 for our families, PLAN-OM3 §4, lane OM3D's
  `isRelativelyProjective_of_isStableModification`, with E4 among its hypotheses): local
  relative projectivity of such a stable modification is global relative projectivity.

Blueprint: `sm-global.tex` (`def:sm-global-numerically-stable`,
`lem:sm-global-numerically-stable-exceptional`, `def:sm-global-valuation-existence`,
`def:sm-global-valuation-uniqueness`, `def:sm-global-blowdown-stable`,
`def:sm-global-stable-open`, `def:sm-global-locally-projective-stable`,
`def:sm-global-stable-projectivity`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.StableModification.Global

universe u

open DeJong (IsSemistablePair IsSmoothAt IsMultipointedCurve IsRelativelyProjective)
open Curves (IsStableModification IsEtaModification IsExceptionalComponent pullbackCompMap
  genericMarksClosure)
open Cohomology (structureCoeff)
open CurvesField.Genus (arithmeticGenus)

section Numerical

/-- The *reduced induced closed subscheme* on a closed subset `Z ⊆ X` (the quotient by the
vanishing ideal of `Z`). -/
abbrev reducedSubscheme {X : Scheme.{u}} (Z : Set X) (hZ : IsClosed Z) : Scheme.{u} :=
  (Scheme.IdealSheafData.vanishingIdeal ⟨Z, hZ⟩).subscheme

/-- The closed immersion of the reduced induced subscheme. -/
abbrev reducedSubschemeι {X : Scheme.{u}} (Z : Set X) (hZ : IsClosed Z) :
    reducedSubscheme Z hZ ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal ⟨Z, hZ⟩).subschemeι

variable {C C' S : Scheme.{u}}

/-- The *special points* of the geometric fibre `C'_a` of `(C', D') ⟶ S` over `a : Spec K → S`:
the points lying on the marks `D'` or at which `C'_a ⟶ Spec K` is not smooth (Temkin T:1687);
lane T44A3's `BlowDown.ExcSpecialize.specialPoints` for `β ≫ g`. -/
abbrev specialPoints (β : C' ⟶ C) (g : C ⟶ S) (D' : C'.IdealSheafData) {K : Type u} [Field K]
    (a : Spec (.of K) ⟶ S) : Set (pullback (C := Scheme.{u}) (β ≫ g) a) :=
  BlowDown.ExcSpecialize.specialPoints (β ≫ g) D' a

/-- **Numerical stability of a geometric fibre** (`PLAN-T5.md` §1.3; Temkin T:1687–1690 in the
numerical form of Appendix B, T:4411–4441). Every irreducible component `Z` of `C'_a` contracted
by `β_a : C'_a ⟶ C_a` whose reduced induced subscheme has arithmetic genus `0` contains at least
three special points (`specialPoints`). This is lane T44A3's integrated
`BlowDown.NoClosedExc.NumericallyStableFibre`. -/
abbrev NumericallyStableFibre (β : C' ⟶ C) (g : C ⟶ S) (D' : C'.IdealSheafData) {K : Type u}
    [Field K] (a : Spec (.of K) ⟶ S) : Prop :=
  BlowDown.NoClosedExc.NumericallyStableFibre β g D' a

/-- The defining property of `NumericallyStableFibre`, in terms of the reduced induced
subschemes of the contracted components. -/
theorem numericallyStableFibre_iff (β : C' ⟶ C) (g : C ⟶ S) (D' : C'.IdealSheafData)
    {K : Type u} [Field K] (a : Spec (.of K) ⟶ S) :
    NumericallyStableFibre β g D' a ↔
      ∀ (Z : Set (pullback (C := Scheme.{u}) (β ≫ g) a))
        (hZ : Z ∈ irreducibleComponents (pullback (C := Scheme.{u}) (β ≫ g) a)),
        (pullbackCompMap β g a '' Z).Subsingleton →
        ∀ [CompactSpace (reducedSubscheme Z (isClosed_of_mem_irreducibleComponents Z hZ))]
          [IsSeparated (terminal.from
            (reducedSubscheme Z (isClosed_of_mem_irreducibleComponents Z hZ)))],
          arithmeticGenus (reducedSubscheme Z (isClosed_of_mem_irreducibleComponents Z hZ))
              (structureCoeff (reducedSubschemeι Z (isClosed_of_mem_irreducibleComponents Z hZ) ≫
                pullback.snd (β ≫ g) a)) = 0 →
            3 ≤ (Z ∩ specialPoints β g D' a).encard :=
  Iff.rfl

/-- **Numerical stability over a point** `s ∈ S`: every geometric fibre over `s` is numerically
stable (`NumericallyStableFibre`). -/
def IsNumericallyStableAt (β : C' ⟶ C) (g : C ⟶ S) (D' : C'.IdealSheafData) (s : S) : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S),
    (∀ z, a z = s) → NumericallyStableFibre β g D' a

/-- **Numerical stability** (`PLAN-T5.md` §1.3, obligation E4 of PLAN-OM3 §6): every geometric
fibre is numerically stable. -/
def IsNumericallyStable (β : C' ⟶ C) (g : C ⟶ S) (D' : C'.IdealSheafData) : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S), NumericallyStableFibre β g D' a

theorem isNumericallyStable_iff (β : C' ⟶ C) (g : C ⟶ S) (D' : C'.IdealSheafData) :
    IsNumericallyStable β g D' ↔ ∀ s, IsNumericallyStableAt β g D' s := by
  refine ⟨fun h s K _ _ a _ ↦ h K a, fun h K _ _ a ↦ ?_⟩
  obtain ⟨z⟩ : Nonempty (Spec (.of K)) := inferInstance
  exact h (a z) K a fun z' ↦ by rw [Subsingleton.elim z' z]

/-- The reduced induced subscheme of a closed subset whose closed points are the image of a
closed immersion from a reduced scheme is isomorphic to it: the kernel of the immersion is the
vanishing ideal of its image. -/
theorem ker_eq_vanishingIdeal_of_isClosedImmersion {T X : Scheme.{u}} [IsReduced T]
    (i : T ⟶ X) [IsClosedImmersion i] (Z : Set X) (hZ : IsClosed Z) (hrange : Set.range i = Z) :
    i.ker = Scheme.IdealSheafData.vanishingIdeal ⟨Z, hZ⟩ := by
  rw [← Scheme.IdealSheafData.map_bot, ← Scheme.nilradical_eq_bot,
    ← Scheme.IdealSheafData.vanishingIdeal_top, Scheme.IdealSheafData.map_vanishingIdeal]
  congr 1
  ext x
  simp only [Closeds.coe_closure, Closeds.coe_top, Set.image_univ, hrange, hZ.closure_eq]
  rfl

/-- The isomorphism `T ≅ Z_red` for a closed immersion `i : T ⟶ X` whose kernel is the
vanishing ideal of `Z`. -/
def isoReducedSubschemeOfKer {T X : Scheme.{u}} (i : T ⟶ X) [IsClosedImmersion i]
    (Z : Set X) (hZ : IsClosed Z) (hker : i.ker = Scheme.IdealSheafData.vanishingIdeal ⟨Z, hZ⟩) :
    T ≅ reducedSubscheme Z hZ :=
  asIso i.toImage ≪≫
    { hom := Scheme.IdealSheafData.inclusion hker.ge
      inv := Scheme.IdealSheafData.inclusion hker.le
      hom_inv_id := by
        rw [Scheme.IdealSheafData.inclusion_comp, Scheme.IdealSheafData.inclusion_id]
      inv_hom_id := by
        rw [Scheme.IdealSheafData.inclusion_comp, Scheme.IdealSheafData.inclusion_id] }

@[reassoc (attr := simp)]
theorem isoReducedSubschemeOfKer_hom_ι {T X : Scheme.{u}} (i : T ⟶ X) [IsClosedImmersion i]
    (Z : Set X) (hZ : IsClosed Z) (hker : i.ker = Scheme.IdealSheafData.vanishingIdeal ⟨Z, hZ⟩) :
    (isoReducedSubschemeOfKer i Z hZ hker).hom ≫ reducedSubschemeι Z hZ = i := by
  simp [isoReducedSubschemeOfKer, Scheme.IdealSheafData.inclusion_subschemeι]

/-- The isomorphism `T ≅ Z_red` for a closed immersion `i : T ⟶ X` of a reduced scheme with
image `Z`. -/
def isoReducedSubscheme {T X : Scheme.{u}} [IsReduced T] (i : T ⟶ X) [IsClosedImmersion i]
    (Z : Set X) (hZ : IsClosed Z) (hrange : Set.range i = Z) : T ≅ reducedSubscheme Z hZ :=
  isoReducedSubschemeOfKer i Z hZ (ker_eq_vanishingIdeal_of_isClosedImmersion i Z hZ hrange)

@[reassoc (attr := simp)]
theorem isoReducedSubscheme_hom_ι {T X : Scheme.{u}} [IsReduced T] (i : T ⟶ X)
    [IsClosedImmersion i] (Z : Set X) (hZ : IsClosed Z) (hrange : Set.range i = Z) :
    (isoReducedSubscheme i Z hZ hrange).hom ≫ reducedSubschemeι Z hZ = i :=
  isoReducedSubschemeOfKer_hom_ι _ _ _ _

/-- Reduced induced subschemes correspond under isomorphisms: for `e : X ≅ Y`, the reduced
induced subscheme on `Z ⊆ X` is isomorphic to the one on `e(Z)`, over `e`. -/
def isoReducedSubschemeOfIso {X Y : Scheme.{u}} (e : X ≅ Y) (Z : Set X) (hZ : IsClosed Z)
    (Z' : Set Y) (hZ' : IsClosed Z') (himage : e.hom '' Z = Z') :
    reducedSubscheme Z hZ ≅ reducedSubscheme Z' hZ' :=
  isoReducedSubschemeOfKer (reducedSubschemeι Z hZ ≫ e.hom) Z' hZ' (by
    rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι,
      Scheme.IdealSheafData.map_vanishingIdeal]
    congr 1
    ext x
    change x ∈ closure (e.hom '' Z) ↔ x ∈ Z'
    rw [himage, hZ'.closure_eq])

@[reassoc (attr := simp)]
theorem isoReducedSubschemeOfIso_hom_ι {X Y : Scheme.{u}} (e : X ≅ Y) (Z : Set X)
    (hZ : IsClosed Z) (Z' : Set Y) (hZ' : IsClosed Z') (himage : e.hom '' Z = Z') :
    (isoReducedSubschemeOfIso e Z hZ Z' hZ' himage).hom ≫ reducedSubschemeι Z' hZ' =
      reducedSubschemeι Z hZ ≫ e.hom :=
  isoReducedSubschemeOfKer_hom_ι _ _ _ _

/-- **Numerical stability excludes exceptional components** (`PLAN-T5.md` §1.3, G0): an
exceptional component is the image of a closed immersion of `ℙ¹_K`, so its reduced induced
subscheme is `ℙ¹_K`, of arithmetic genus `0`, and it has at most two special points (lane T44A3,
`BlowDown.NoClosedExc.not_numericallyStableFibre_of_isExceptionalComponent`). -/
theorem not_isExceptionalComponent_of_numericallyStableFibre (β : C' ⟶ C) (g : C ⟶ S)
    (D' : C'.IdealSheafData) {K : Type u} [Field K] (a : Spec (.of K) ⟶ S)
    (h : NumericallyStableFibre β g D' a) (Z : Set (pullback (C := Scheme.{u}) (β ≫ g) a)) :
    ¬ IsExceptionalComponent β g D' a Z := fun hE ↦
  BlowDown.NoClosedExc.not_numericallyStableFibre_of_isExceptionalComponent β g D' a hE h

/-- **Numerically stable η-modifications have no exceptional components.** -/
theorem IsNumericallyStable.not_isExceptionalComponent {β : C' ⟶ C} {g : C ⟶ S}
    {D' : C'.IdealSheafData} (h : IsNumericallyStable β g D') (K : Type u) [Field K]
    [IsAlgClosed K] (a : Spec (.of K) ⟶ S) (Z : Set (pullback (C := Scheme.{u}) (β ≫ g) a)) :
    ¬ IsExceptionalComponent β g D' a Z :=
  not_isExceptionalComponent_of_numericallyStableFibre β g D' a (h K a) Z

end Numerical

section Producers

/-- **A curve over a valuation ring in the situation of Temkin's §4.5** (`PLAN-T5.md` §1.3; our
case of Temkin's `C`, T:3233–3236): `C` is integral, flat, of finite presentation and projective
over `W`, smooth at the points over the generic point, with marks `D` flat over `W` whose generic
pair is semi-stable. -/
structure IsValuationCurve {K : Type u} [Field K] {W : ValuationSubring K} {C : Scheme.{u}}
    (φ : C ⟶ Spec (.of W)) (D : C.IdealSheafData) : Prop where
  isIntegral : IsIntegral C
  flat : Flat φ
  locallyOfFinitePresentation : LocallyOfFinitePresentation φ
  isProjectiveOver : IsProjectiveOver φ
  isSmoothAt_generic : ∀ x : C, φ x = genericPoint (Spec (.of W)) → IsSmoothAt φ x
  marksFlat : Flat (D.subschemeι ≫ φ)
  genericPair : IsSemistablePair (φ.fiberToSpecResidueField (genericPoint (Spec (.of W))))
    (DeJong.fiberMarks φ D (genericPoint (Spec (.of W))))

/-- **Existence over a valuation ring** (Temkin Prop. 4.5.1 `sepclosprop`, T:3233–3266, with
Thm 1.1 over `W`; `PLAN-T5.md` §1.3, lane T45B). Over a valuation ring `W` of finite height and
equal characteristic whose fraction field is algebraically closed, every curve in the situation
`IsValuationCurve` has a stable η-modification which is numerically stable and projective over
`W`. -/
def ValuationStableExistence : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (W : ValuationSubring K) [Finite (PrimeSpectrum W)],
    (∃ p : ℕ, ExpChar K p ∧ ExpChar (IsLocalRing.ResidueField W) p) →
    ∀ (C : Scheme.{u}) (φ : C ⟶ Spec (.of W)) (D : C.IdealSheafData), IsValuationCurve φ D →
      ∃ (C' : Scheme.{u}) (β : C' ⟶ C) (D' : C'.IdealSheafData),
        IsStableModification β φ D D' ∧ IsNumericallyStable β φ D' ∧ IsProjectiveOver (β ≫ φ)

/-- **Uniqueness over a valuation ring** (Temkin Thm 1.2 over `W`, T:3233–3266;
`PLAN-T5.md` §1.3, lane T45B). In the situation of `ValuationStableExistence`, two stable,
numerically stable η-modifications projective over `W` are isomorphic over `C`. -/
def ValuationStableUniqueness : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (W : ValuationSubring K) [Finite (PrimeSpectrum W)],
    (∃ p : ℕ, ExpChar K p ∧ ExpChar (IsLocalRing.ResidueField W) p) →
    ∀ (C : Scheme.{u}) (φ : C ⟶ Spec (.of W)) (D : C.IdealSheafData), IsValuationCurve φ D →
    ∀ (C₁ C₂ : Scheme.{u}) (β₁ : C₁ ⟶ C) (β₂ : C₂ ⟶ C) (D₁ : C₁.IdealSheafData)
      (D₂ : C₂.IdealSheafData),
      IsStableModification β₁ φ D D₁ → IsNumericallyStable β₁ φ D₁ → IsProjectiveOver (β₁ ≫ φ) →
      IsStableModification β₂ φ D D₂ → IsNumericallyStable β₂ φ D₂ → IsProjectiveOver (β₂ ≫ φ) →
      ∃ e : C₁ ≅ C₂, e.hom ≫ β₂ = β₁

/-- **The blow-down to the stable modification** (Temkin Prop. 4.4.6 `blowdownprop`, T:3188–3229,
iterated with Lemma 4.4.4 `emptylem`, T:3158–3176; `PLAN-T5.md` §1.3, lane T44B). In the situation
of `ValuationStableExistence`, a semi-stable η-modification `f : C' ⟶ C` with the transported
marks, projective over `W`, factors through a stable and numerically stable η-modification
`β` projective over `W`. -/
def BlowDownStable : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (W : ValuationSubring K) [Finite (PrimeSpectrum W)],
    (∃ p : ℕ, ExpChar K p ∧ ExpChar (IsLocalRing.ResidueField W) p) →
    ∀ (C : Scheme.{u}) (φ : C ⟶ Spec (.of W)) (D : C.IdealSheafData), IsValuationCurve φ D →
    ∀ (C' : Scheme.{u}) (f : C' ⟶ C), IsEtaModification f φ →
      IsSemistablePair (f ≫ φ) (genericMarksClosure f φ D (genericPoint (Spec (.of W)))) →
      IsProjectiveOver (f ≫ φ) →
      ∃ (C'' : Scheme.{u}) (β : C'' ⟶ C) (D'' : C''.IdealSheafData) (h : C' ⟶ C''),
        IsStableModification β φ D D'' ∧ IsNumericallyStable β φ D'' ∧
          IsProjectiveOver (β ≫ φ) ∧ h ≫ β = f

/-- **Spreading of numerical stability** (Temkin Lemma 5.1 (ii) `openloclem`, T:3282–3311, in the
form used in the proof of Thm 1.5, T:3384–3394; `PLAN-T5.md` §1.3, node G4). Let `U` be a variety
over `k`, `q : C ⟶ U` projective relative to `k`, `β : X ⟶ C` projective relative to `k`, and
`(X, D')` a semi-stable pair over `U`. If the geometric fibre over one geometric point `a` over
`z ∈ U` is numerically stable, so are the geometric fibres over all points of an open
neighbourhood of `z`.

Compared with `PLAN-T5.md` §1.3 this is the general form: `U` need not be normal (the ω route
of node G4 first normalizes `U`; numerical stability is insensitive to the finite surjective
normalization), and no condition on `C`, the marks of `C` or the generic fibre is imposed (they
are not used by the argument); numerical stability is assumed at one geometric point over `z`
only (numerical stability of a geometric fibre is invariant under extension of the
algebraically closed field). Temkin's Lemma 5.1 (ii) itself asserts constructibility; openness
follows from it together with the stability of numerical stability under generization. -/
def StableOpenNbhd (k : Type u) [Field k] : Prop :=
  ∀ (U : Scheme.{u}) (pU : U ⟶ Spec (.of k)) (_ : IsVariety pU)
    (C : Scheme.{u}) (q : C ⟶ U), IsRelativelyProjective pU q →
    ∀ (X : Scheme.{u}) (β : X ⟶ C), IsRelativelyProjective (q ≫ pU) β →
    ∀ (D' : X.IdealSheafData), IsSemistablePair (β ≫ q) D' →
    ∀ (z : U) (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ U), (∀ x, a x = z) →
      NumericallyStableFibre β q D' a →
      ∃ O : U.Opens, z ∈ O ∧ ∀ z' ∈ O, IsNumericallyStableAt β q D' z'

end Producers

section Projective

/-- **A locally projective stable modification after an alteration** (`PLAN-T5.md` §1.2,
obligations E1–E4 of PLAN-OM3 §6). For `pS : S ⟶ Spec k` and a multipointed `S`-curve
`(g : C ⟶ S, D)`: an alteration `ψ : S' ⟶ S` from an integral normal scheme projective over `k`
(E1) and a stable η-modification `β : C' ⟶ C ×_S S'` of `(C ×_S S', D ×_S S')` (E2), locally
relatively projective over `k` (E3, lane OM3A's `Projectivity.LocallyRelativelyProjective`: a
finite open cover of `C ×_S S'` over whose members `β` is projective relative to `k`) and
numerically stable (E4), whose marks are finite over `S'` and which is an isomorphism over a
nonempty open of `S'`. -/
def HasLocallyProjectiveStableModification (k : Type u) [Field k] {S C : Scheme.{u}}
    (pS : S ⟶ Spec (.of k)) (g : C ⟶ S) (D : C.IdealSheafData) : Prop :=
  ∃ (S' : Scheme.{u}) (_ : IsIntegral S') (ψ : S' ⟶ S) (C' : Scheme.{u})
    (D' : C'.IdealSheafData) (β : C' ⟶ pullback (C := Scheme.{u}) g ψ),
    IsAlteration ψ ∧ IsNormalScheme S' ∧ IsProjectiveOver (ψ ≫ pS) ∧
    IsStableModification β (pullback.snd g ψ) (D.comap (pullback.fst g ψ)) D' ∧
    Projectivity.LocallyRelativelyProjective (pullback.snd g ψ ≫ ψ ≫ pS) β ∧
    IsNumericallyStable β (pullback.snd g ψ) D' ∧
    IsFinite (D'.subschemeι ≫ β ≫ pullback.snd g ψ) ∧
    ∃ U : S'.Opens, Nonempty U ∧ IsIso (β ∣_ ((pullback.snd g ψ) ⁻¹ᵁ U))

/-- **Projectivity of the stable modification** (Temkin Thm 1.1 for the families of Thm 1.5,
T:3379–3399 with §6; PLAN-OM3 §4, `thm:sm-tsm-proj`, lane OM3D). In the situation of
`DeJong.TemkinStableModification k` (`S` a normal projective variety over `k`, `(C, D)` a
multipointed `S`-curve projective over `k` with smooth, semi-stable, geometrically integral
generic fibre), let `ψ : S' ⟶ S` be an alteration with `S'` integral, normal and projective over
`k`, and `β` a stable, numerically stable η-modification of `C ×_S S'` which is locally
relatively projective over `k`. Then `β` is projective relative to `k`.

This is the statement of lane OM3D's `Projectivity.isRelativelyProjective_of_isStableModification`
(PLAN-OM3 §4) with the extra hypotheses `IsVariety pS`, `IsNormalScheme S`, the semi-stability of
the generic pair and numerical stability (E4), which are available at the point of use; it is a
hypothesis of the final assembly, not asserted here. -/
def StableModificationProjectivity (k : Type u) [Field k] [IsAlgClosed k] : Prop :=
  ∀ (S : Scheme.{u}) (pS : S ⟶ Spec (.of k)) (_ : IsVariety pS), IsNormalScheme S →
    IsProjectiveOver pS →
    ∀ (C : Scheme.{u}) (g : C ⟶ S) (D : C.IdealSheafData),
      IsProjectiveOver (g ≫ pS) → IsMultipointedCurve g D →
      Smooth (g.fiberToSpecResidueField (genericPoint S)) →
      IsSemistablePair (g.fiberToSpecResidueField (genericPoint S))
        (DeJong.fiberMarks g D (genericPoint S)) →
      GeometricallyIntegral (g.fiberToSpecResidueField (genericPoint S)) →
    ∀ (S' : Scheme.{u}) [IsIntegral S'], IsNormalScheme S' →
    ∀ (ψ : S' ⟶ S) [IsAlteration ψ], IsProjectiveOver (ψ ≫ pS) →
    ∀ (C' : Scheme.{u}) (β : C' ⟶ pullback (C := Scheme.{u}) g ψ) (D' : C'.IdealSheafData),
      IsStableModification β (pullback.snd g ψ) (D.comap (pullback.fst g ψ)) D' →
      IsNumericallyStable β (pullback.snd g ψ) D' →
      Projectivity.LocallyRelativelyProjective (pullback.snd g ψ ≫ ψ ≫ pS) β →
      IsRelativelyProjective (pullback.snd g ψ ≫ ψ ≫ pS) β

end Projective

end DeJongAlterations.StableModification.Global
