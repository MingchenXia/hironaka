/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.ClosureComponent
import DeJongAlterations.StableModification.BlowDown.ExcSpecializeGenus
import DeJongAlterations.StableModification.BlowDown.ClosedLocus
import DeJongAlterations.StableModification.ValCurves.ModificationsFinite
import DeJongAlterations.StableModification.Curves.Basic
import DeJongAlterations.StableModification.BlowDown.StabilityCriterion

/-!
# Exceptional components specialize to exceptional trees

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), proof of
Lemma 4.4.4 (`emptylem`, T:3162–3168): if a fibre `C′_t` of a semi-stable modification has an
exceptional component `Z`, the closed fibre has one. Temkin's intermediate claim (every
component of `C′_{s₀}` in the closure of `Z` is exceptional) is false (ERRATA T57,
`rem:sm-bd-literature`(1)); the corrected statement is that the trace of the closure of `Z` on the
closed fibre is an **exceptional `ℙ¹`-tree**, which contains an exceptional component
(`CurvesField.IncidenceGraph.IsExceptionalTree.exists_isExceptional`, Temkin App. B). Blueprint:
`lem:sm-bd-exc-specialize`, chapter `sm-blow-down-exceptional.tex`.

Here `C′ = X` is projective and nodal over a valuation ring `V` with finitely many primes and
all `Frac(V/𝔭)` separably closed, `β : X → C` with `g : C → Spec V` proper, `X_t = X ×_V κ(t)`
the residue-field fibres (`ClosureComponent.residuePt`), and the input component is numerical:
contracted by `β_t`, with `χ(𝒪_{Z_red}) = 1` and at most two special points (`specialPoints`).

## Main definitions and results

* `isAlgebraicAt_of_isClosed`, `not_isAlgebraicAt_of_mem_genericPoints`: closed points of `X_t`
  are algebraic over `κ(t)`, generic points of a fibre of pure dimension one are not.
* `exists_mem_genericPoints_preimage_closure`: **the closure of a non-algebraic point meets the
  closed fibre in a curve** (it contains a generic point of `X_{s₀}`).
* `eq_of_mem_closure_of_isAlgebraicAt`: **the closure of an algebraic point meets the closed
  fibre in one point** (Temkin, T:3166–3168; it replaces the normality of `C` used in the
  blueprint's proof).
* `specialPoints`, `closedBoundaryPoints`, `closedMarkPoints`; `ClosureComponentLocal`: the
  étale-local part of `lem:sm-bd-closure-component` ((2) reducedness of the closed fibre of the
  closure, (3) the injections of boundary points and marks), **not formalized**, a named
  hypothesis.
* `IsCombExceptional`: a combinatorially exceptional component of a fibre (contracted, genus `0`
  normalization, no double point of its own, at most two closed special points).
* `markedGraph`: lane CRV4's incidence graph `CurvesField.Genus.nodalGraph` with marks.
* `exists_isCombExceptional_closedFibre` (**`lem:sm-bd-exc-specialize`**): a numerically
  exceptional component of `X_t` produces a combinatorially exceptional component of `X_{s₀}`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

namespace DeJongAlterations.StableModification.BlowDown.ExcSpecialize

universe u

open Cohomology CurvesField CurvesField.Genus ClosureComponent ValCurves
open Curves (pullbackCompMap)
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false



section ResidueFibre

variable {V : Type u} [CommRing V] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of V))
  (t : PrimeSpectrum V)

/-- In the residue-field fibre, the closure of a point is the preimage of the closure of its
image. -/
theorem closure_singleton_eq_preimage (ζ : pullback (C := Scheme.{u}) p (residuePt t)) :
    closure {ζ} = pullback.fst p (residuePt t) ⁻¹' closure {pullback.fst p (residuePt t) ζ} := by
  rw [(isEmbedding_fst_residuePt p t).isInducing.closure_eq_preimage_closure_image,
    Set.image_singleton]

/-- Algebraicity at a point is preserved by precomposition with a morphism inducing an injection
of residue fields at that point, in the downward direction. -/
theorem isAlgebraicAt_of_comp {Y Z : Scheme.{u}} {i : Y ⟶ X} {h : X ⟶ Z} {y : Y}
    (hih : IsAlgebraicAt (i ≫ h) y) : IsAlgebraicAt h (i y) := by
  have e : ((i ≫ h).residueFieldMap y).hom =
      (i.residueFieldMap y).hom.comp (h.residueFieldMap (i y)).hom := by
    change ((i ≫ h).residueFieldMap y).hom = (h.residueFieldMap (i y) ≫ i.residueFieldMap y).hom
    rw [Scheme.residueFieldMap_comp]
  have hint : ((i.residueFieldMap y).hom.comp (h.residueFieldMap (i y)).hom).IsIntegral := by
    rw [← e]
    exact hih
  exact RingHom.IsIntegral.tower_bot _ _ (RingHom.injective _) hint

variable [LocallyOfFiniteType p]

/-- **Closed points of a fibre are algebraic** (Hilbert's Nullstellensatz, Mathlib's
`isFinite_iff_locallyOfFiniteType_of_jacobsonSpace`): a closed point of the residue-field fibre
`X_t` lies over a point of `X` whose residue field is algebraic over `κ(t)`. -/
theorem isAlgebraicAt_of_isClosed (x : pullback (C := Scheme.{u}) p (residuePt t))
    (hx : IsClosed ({x} : Set _)) :
    IsAlgebraicAt p (pullback.fst p (residuePt t) x) := by
  have : IsClosedImmersion ((pullback p (residuePt t)).fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have hfin : IsFinite ((pullback p (residuePt t)).fromSpecResidueField x ≫
      pullback.snd p (residuePt t)) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField] at hfin
  have : IsClosedImmersion ((Spec (CommRingCat.of t.asIdeal.ResidueField)).fromSpecResidueField
      (pullback.snd p (residuePt t) x)) :=
    isClosed_singleton_iff_isClosedImmersion.mp (isClosed_discrete _)
  have : IsFinite (Spec.map ((pullback.snd p (residuePt t)).residueFieldMap x)) := IsFinite.of_comp _
    ((Spec (CommRingCat.of t.asIdeal.ResidueField)).fromSpecResidueField
      (pullback.snd p (residuePt t) x))
  have hq : IsAlgebraicAt (pullback.snd p (residuePt t)) x :=
    IsIntegralHom.SpecMap_iff.mp inferInstance
  have h2 : IsAlgebraicAt (pullback.snd p (residuePt t) ≫ residuePt t) x :=
    hq.comp (isAlgebraicAt_of_surjectiveOnStalks (residuePt t) (pullback.snd p (residuePt t) x))
  rw [← pullback.condition] at h2
  exact isAlgebraicAt_of_comp h2

end ResidueFibre


section Algebraic

variable {V : Type u} [CommRing V] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of V))

/-- Points of the residue-field fibre `X_t` lie over `t`. -/
theorem apply_fst_residuePt {t : PrimeSpectrum V} (w : pullback (C := Scheme.{u}) p (residuePt t)) :
    p (pullback.fst p (residuePt t) w) = t := by
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, residuePt_apply]

/-- Algebraicity at a point is inherited by a closed immersion (whose residue field maps are
isomorphisms). -/
theorem isAlgebraicAt_comp_of_isClosedImmersion {Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i]
    (y : Y) (h : IsAlgebraicAt p (i y)) : IsAlgebraicAt (i ≫ p) y := by
  have e : ((i ≫ p).residueFieldMap y).hom =
      (i.residueFieldMap y).hom.comp (p.residueFieldMap (i y)).hom := by
    change ((i ≫ p).residueFieldMap y).hom = (p.residueFieldMap (i y) ≫ i.residueFieldMap y).hom
    rw [Scheme.residueFieldMap_comp]
  unfold IsAlgebraicAt
  rw [e]
  have hi : (i.residueFieldMap y).hom.IsIntegral :=
    RingHom.isIntegral_of_surjective _ (ConcreteCategory.bijective_of_isIso _).2
  exact RingHom.IsIntegral.trans _ _ h hi

/-- **A closed point of `X_t` is the image of a point of `X` closed in `p⁻¹(t)`**, and
conversely: for `ζ ∈ X_t`, if `{p_t(ζ)}` is closed in the set-theoretic fibre, `{ζ}` is closed in
`X_t`. -/
theorem isClosed_singleton_of_isClosed_preimage {t : PrimeSpectrum V}
    (ζ : pullback (C := Scheme.{u}) p (residuePt t))
    (h : IsClosed ({⟨pullback.fst p (residuePt t) ζ, apply_fst_residuePt p ζ⟩} :
      Set (p ⁻¹' {t}))) : IsClosed ({ζ} : Set (pullback (C := Scheme.{u}) p (residuePt t))) := by
  obtain ⟨F, hF, hFe⟩ := isClosed_induced_iff.mp h
  have : ({ζ} : Set (pullback (C := Scheme.{u}) p (residuePt t))) =
      pullback.fst p (residuePt t) ⁻¹' F := by
    ext w
    constructor
    · intro hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      have : (⟨pullback.fst p (residuePt t) w, apply_fst_residuePt p w⟩ : p ⁻¹' {t}) ∈
          Subtype.val ⁻¹' F := by
        rw [hFe]
        rfl
      exact this
    · intro hw
      have hw' : (⟨pullback.fst p (residuePt t) w, apply_fst_residuePt p w⟩ : p ⁻¹' {t}) ∈
          Subtype.val ⁻¹' F := hw
      rw [hFe, Set.mem_singleton_iff] at hw'
      exact (isEmbedding_fst_residuePt p t).injective (congrArg Subtype.val hw')
  rw [this]
  exact hF.preimage (pullback.fst p (residuePt t)).continuous

/-- **Generic points of a fibre of pure dimension one are not algebraic over the base**: an
algebraic point is closed in its fibre, and a closed point is not generic when all components
have dimension one. -/
theorem not_isAlgebraicAt_of_mem_genericPoints [IsSeparated p] {t : PrimeSpectrum V}
    (hpure : ∀ W ∈ irreducibleComponents (pullback (C := Scheme.{u}) p (residuePt t)),
      topologicalKrullDim W = 1)
    {ζ : pullback (C := Scheme.{u}) p (residuePt t)} (hζ : ζ ∈ genericPoints _) :
    ¬ IsAlgebraicAt p (pullback.fst p (residuePt t) ζ) := by
  intro h
  refine BlowDown.not_mem_genericPoints_of_isClosed hpure ?_ hζ
  exact isClosed_singleton_of_isClosed_preimage p ζ
    (ValCurves.isClosed_singleton_preimage_of_isAlgebraicAt p (apply_fst_residuePt p ζ) h)

variable [IsLocalRing V]

/-- **The closure of a non-algebraic point meets the closed fibre in a curve** (blueprint
`lem:sm-bd-closure-component`(2), the dimension part): if `z ∈ X` has residue field transcendental
over `κ(p z)` and `p` is proper, the closure of `z` contains a generic point of the closed fibre
`X_{s₀}` (of dimension at most one). Otherwise every point of the closure over `s₀` would be
closed in `X_{s₀}`, hence algebraic (Nullstellensatz), so the closure of `z` would be finite over
the local scheme `Spec V` (`ValCurves.exists_isFinite_morphismRestrict_of_isAlgebraicAt`), and
`z` itself algebraic. -/
theorem exists_mem_genericPoints_preimage_closure [IsProper p]
    (hdim₀ : topologicalKrullDim
      (pullback (C := Scheme.{u}) p (residuePt (IsLocalRing.closedPoint V))) ≤ 1)
    {z : X} (hz : ¬ IsAlgebraicAt p z) :
    ∃ w ∈ genericPoints (pullback (C := Scheme.{u}) p (residuePt (IsLocalRing.closedPoint V))),
      pullback.fst p (residuePt (IsLocalRing.closedPoint V)) w ∈ closure {z} := by
  by_contra hno
  push Not at hno
  set s₀ : PrimeSpectrum V := IsLocalRing.closedPoint V
  have : CompactSpace X := compactSpace_of_quasiCompact p
  have : CompactSpace (pullback (C := Scheme.{u}) p (residuePt s₀)) :=
    compactSpace_of_quasiCompact (pullback.snd p (residuePt s₀))
  have halg : ∀ y : closureScheme z, (closureι z ≫ p) y = s₀ →
      IsAlgebraicAt (closureι z ≫ p) y := by
    intro y hy
    have hmem : closureι z y ∈ Set.range (pullback.fst p (residuePt s₀)) := by
      rw [range_fst_residuePt]
      exact hy
    obtain ⟨w, hw⟩ := hmem
    have hwz : pullback.fst p (residuePt s₀) w ∈ closure {z} := by
      rw [hw, ← range_closureι]
      exact ⟨y, rfl⟩
    have hwg : w ∉ genericPoints _ := fun hg => hno w hg hwz
    have hwc := CurvesField.Genus.isClosed_singleton_of_not_mem_genericPoints hdim₀ hwg
    have := isAlgebraicAt_of_isClosed p s₀ w hwc
    rw [hw] at this
    exact isAlgebraicAt_comp_of_isClosedImmersion p (closureι z) y this
  obtain ⟨U, hU, -, hUalg⟩ :=
    ValCurves.exists_isFinite_morphismRestrict_of_isAlgebraicAt (closureι z ≫ p) s₀ halg
  have hUtop : U = ⊤ := BlowDown.eq_top_of_closedPoint_mem U hU
  have h := hUalg (closurePt z) (by rw [hUtop]; trivial)
  have h' := isAlgebraicAt_of_comp h
  rw [closureι_closurePt] at h'
  exact hz h'

end Algebraic

section Contraction

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]

/-- **The closure of an algebraic point meets the closed fibre in one point** (Temkin, proof of
Lemma 4.4.4, T:3166–3168; blueprint `lem:sm-bd-exc-specialize`): for `g : C → Spec V` proper,
all `Frac(V/𝔭)` separably closed and `x ∈ C` with residue field algebraic over `κ(g x)`, any two
points of the closure of `x` over the closed point coincide. The closure contains a closed point
`x₀`; every specialization of `x` specializes to `x₀`
(`BlowDown.specializes_of_specializes_of_isAlgebraicAt`) and is algebraic over `κ(s₀)`
(`ValuationRing.stableUnderSpecialization_fiberTrdeg_eq_zero`), hence closed in the closed fibre. -/
theorem eq_of_mem_closure_of_isAlgebraicAt
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    {C : Scheme.{u}} (g : C ⟶ Spec (CommRingCat.of V)) [IsProper g] {x : C}
    (hx : IsAlgebraicAt g x) {w₁ w₂ : C} (h₁ : w₁ ∈ closure {x}) (h₂ : w₂ ∈ closure {x})
    (hw₁ : g w₁ = IsLocalRing.closedPoint V) (hw₂ : g w₂ = IsLocalRing.closedPoint V) :
    w₁ = w₂ := by
  have : CompactSpace C := compactSpace_of_quasiCompact g
  obtain ⟨x₀, hx₀, hx₀c⟩ := IsClosed.exists_closed_singleton (S := closure {x}) isClosed_closure
    ⟨x, subset_closure rfl⟩
  have hxx₀ : x ⤳ x₀ := specializes_iff_mem_closure.mpr hx₀
  have hgx₀ : g x₀ = IsLocalRing.closedPoint V := by
    have hc : IsClosed ({g x₀} : Set (Spec (CommRingCat.of V))) := by
      rw [← Set.image_singleton]
      exact g.isClosedMap _ hx₀c
    have hmax := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp hc
    exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hmax)
  have key : ∀ w, w ∈ closure {x} → g w = IsLocalRing.closedPoint V → w = x₀ := by
    intro w hw hgw
    have hxw : x ⤳ w := specializes_iff_mem_closure.mpr hw
    have hwx₀ : w ⤳ x₀ := specializes_of_specializes_of_isAlgebraicAt hsep g hxx₀ hx₀c hx hxw
    have hwalg : IsAlgebraicAt g w := by
      rw [ValCurves.isAlgebraicAt_iff_fiberTrdeg_eq_zero] at hx ⊢
      exact ValuationRing.stableUnderSpecialization_fiberTrdeg_eq_zero g hxw hx
    have hcl := ValCurves.isClosed_singleton_preimage_of_isAlgebraicAt g hgw hwalg
    have hsp : (⟨w, hgw⟩ : g ⁻¹' {IsLocalRing.closedPoint V}) ⤳ ⟨x₀, hgx₀⟩ :=
      IsInducing.subtypeVal.specializes_iff.mp hwx₀
    have := hsp.mem_closed hcl rfl
    exact (congrArg Subtype.val (Set.mem_singleton_iff.mp this)).symm
  rw [key w₁ h₁ hw₁, key w₂ h₂ hw₂]

end Contraction


section GenericPointsEmbedding

variable {T Y : Type*} [TopologicalSpace T] [TopologicalSpace Y] [QuasiSober T] [T0Space T]
  [QuasiSober Y] [T0Space Y]

/-- **Generic points of a union of components.** For an embedding `j : T → Y` whose image is a
union of irreducible components of `Y` (every point of the image lies in the closure of a generic
point of `Y` in the image), the generic points of `T` are the points mapping to generic points of
`Y`. -/
theorem mem_genericPoints_iff_of_isEmbedding {j : T → Y} (hj : IsEmbedding j)
    (hR : ∀ x ∈ Set.range j, ∃ v ∈ genericPoints Y, v ∈ Set.range j ∧ x ∈ closure {v}) (η : T) :
    η ∈ genericPoints T ↔ j η ∈ genericPoints Y := by
  rw [CurvesField.Genus.mem_genericPoints_iff, CurvesField.Genus.mem_genericPoints_iff]
  constructor
  · intro h ξ hξ
    obtain ⟨v, hv, ⟨η', rfl⟩, hηv⟩ := hR (j η) ⟨η, rfl⟩
    have h1 : j η' ⤳ j η := specializes_iff_mem_closure.mpr hηv
    have h2 : η' ⤳ η := hj.isInducing.specializes_iff.mp h1
    have h3 : η' = η := h η' h2
    subst h3
    exact ((CurvesField.Genus.mem_genericPoints_iff _).mp hv) ξ hξ
  · intro h ξ hξ
    exact hj.injective (h (j ξ) (hξ.map hj.continuous))

end GenericPointsEmbedding

section Statements

variable {S X : Scheme.{u}}

/-- The *special points* of the fibre `X_a` of `q : X → S` with marks `D'` over a field point
`a : Spec K → S`: the points lying on `D'` and the points at which `X_a → Spec K` is not smooth
(Temkin T:1687). For `q = β ≫ g` this is the set `Global.specialPoints β g D' a` of
`PLAN-T5.md` §1.3 (lane T5G, not yet integrated), and it is the set bounded by the field
`encard_special_le_two` of `Curves.IsExceptionalComponent`. -/
def specialPoints (q : X ⟶ S) (D' : X.IdealSheafData) {K : Type u} [Field K]
    (a : Spec (.of K) ⟶ S) : Set (pullback (C := Scheme.{u}) q a) :=
  pullback.fst q a ⁻¹' (D'.support : Set X) ∪ {y | ¬ DeJong.IsSmoothAt (pullback.snd q a) y}

variable {V : Type u} [CommRing V] [IsLocalRing V]

/-- Every point of `Spec V` specializes to the closed point. -/
theorem specializes_closedPoint (x : PrimeSpectrum V) : x ⤳ IsLocalRing.closedPoint V :=
  (PrimeSpectrum.le_iff_specializes _ _).mp (IsLocalRing.le_maximalIdeal x.isPrime.ne_top)

/-- The *boundary points* in the closed fibre `X_{s₀}` of the trace `Y = X_{s₀} ∩ closure {z}` of
the closure of `z ∈ X`: the ordinary double points of `X_{s₀}` on `Y` lying on a component of
`X_{s₀}` not contained in `Y` (Temkin's `∂_{C'_{s₀}}(Y_{s₀})`, T:4426). -/
def closedBoundaryPoints (q : X ⟶ Spec (.of V)) (z : X) :
    Set (pullback (C := Scheme.{u}) q (residuePt (IsLocalRing.closedPoint V))) :=
  {y | pullback.fst q _ y ∈ closure {z} ∧ IsClosed {y} ∧
    Geometry.IsGeometricOrdinaryDoublePoint (pullback.snd q _) y ∧
    ∃ w ∈ genericPoints (pullback (C := Scheme.{u}) q (residuePt (IsLocalRing.closedPoint V))),
      pullback.fst q _ w ∉ closure {z} ∧ y ∈ closure {w}}

/-- The *marks* on the trace `X_{s₀} ∩ closure {z}`: its points lying on `D'`. -/
def closedMarkPoints (q : X ⟶ Spec (.of V)) (D' : X.IdealSheafData) (z : X) :
    Set (pullback (C := Scheme.{u}) q (residuePt (IsLocalRing.closedPoint V))) :=
  {y | pullback.fst q _ y ∈ closure {z} ∧ pullback.fst q _ y ∈ (D'.support : Set X)}

end Statements

/-- **The étale-local part of the closure-component lemma** (blueprint
`lem:sm-bd-closure-component`(2)–(3); Temkin, proof of Lemma 4.4.4, T:3164–3166). *Not formalized*:
its proof needs the étale node charts of lane SS3 (`thm:sm-etale-node-chart`) at the points of
the closed fibre and the henselianity of `V ⧸ 𝔭`. It is a hypothesis of the results below, in this
precise form. For a semi-stable pair `(q : X → Spec V, D')`, proper and projective over a
valuation ring `V` with finitely many primes and all `Frac(V/𝔭)` separably closed, a point `t` of
`Spec V` and a generic point `ζ` of the fibre `X_t` with image `z ∈ X`:
1. the closed fibre `Ȳ_{s₀}` (over `V ⧸ 𝔭_t`, `fibreAt`) of the reduced closure `Ȳ` of `z` is
   reduced;
2. the boundary points of `Ȳ_{s₀}` in `X_{s₀}` (`closedBoundaryPoints`) and the marks on it
   (`closedMarkPoints`) are together at most as many as the special points (`specialPoints`) of
   the component `closure {ζ}` of `X_t`: generization defines injections
   `∂(Ȳ_{s₀}) ↪ ∂(Ȳ_t)` (onto double points) and `D' ∩ Ȳ_{s₀} ↪ D' ∩ Ȳ_t` (onto smooth points). -/
def ClosureComponentLocal : Prop :=
  ∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V] [Finite (PrimeSpectrum V)],
    (∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal))) →
    ∀ (X : Scheme.{u}) [CompactSpace X] (q : X ⟶ Spec (.of V)) (D' : X.IdealSheafData)
      [IsProper q], IsProjectiveOver q → DeJong.IsSemistablePair q D' →
      ∀ (t : PrimeSpectrum V) (ζ : pullback (C := Scheme.{u}) q (residuePt t)),
        ζ ∈ genericPoints (pullback (C := Scheme.{u}) q (residuePt t)) →
        IsReduced (fibreAt q (pullback.fst q (residuePt t) ζ)
          (specializes_closedPoint (q (pullback.fst q (residuePt t) ζ)))) ∧
        (closedBoundaryPoints q (pullback.fst q (residuePt t) ζ)).encard +
            (closedMarkPoints q D' (pullback.fst q (residuePt t) ζ)).encard ≤
          (closure {ζ} ∩ specialPoints q D' (residuePt t)).encard

section CombExceptional

variable {S X C : Scheme.{u}}

/-- A **combinatorially exceptional component** of the fibre `X_a` of `β ≫ g : X → C → S` with
marks `D'` over a field point `a` (Temkin's exceptional components, App. B T:4459–4462, in terms of
the incidence data of `CurvesField.Genus.nodalGraph`): a generic point `v` of `X_a` whose
component is contracted by `β_a`, whose normalization has genus `0`
(`CurvesField.Genus.componentGenus`), which carries no ordinary double point of `X_a` with both
branches on it, and which carries at most two closed special points. Over an algebraically closed
field and for `X_a` nodal its reduced component is a smooth rational curve, i.e. `ℙ¹` (not
formalized); see `NoClosedExc` for the comparison with the numerical form. -/
structure IsCombExceptional (β : X ⟶ C) (g : C ⟶ S) (D' : X.IdealSheafData) {K : Type u}
    [Field K] (a : Spec (.of K) ⟶ S) [CompactSpace (pullback (C := Scheme.{u}) (β ≫ g) a)]
    [IsAffineHom (pullback.diagonal (terminal.from (pullback (C := Scheme.{u}) (β ≫ g) a)))]
    (v : pullback (C := Scheme.{u}) (β ≫ g) a) : Prop where
  mem_genericPoints : v ∈ genericPoints (pullback (C := Scheme.{u}) (β ≫ g) a)
  contracted : (pullbackCompMap β g a '' closure {v}).Subsingleton
  componentGenus_eq_zero : componentGenus (structureCoeff (pullback.snd (β ≫ g) a)) v = 0
  exists_ne_of_isGeometricOrdinaryDoublePoint : ∀ y ∈ closure {v}, IsClosed ({y} : Set _) →
    Geometry.IsGeometricOrdinaryDoublePoint (pullback.snd (β ≫ g) a) y →
    ∃ w ∈ genericPoints (pullback (C := Scheme.{u}) (β ≫ g) a), w ≠ v ∧ y ∈ closure {w}
  encard_closed_special_le_two :
    (closure {v} ∩ specialPoints (β ≫ g) D' a ∩ {y | IsClosed ({y} : Set _)}).encard ≤ 2

end CombExceptional

section MarkedGraph

variable {X : Scheme.{u}} [IsAffineHom (pullback.diagonal (terminal.from X))]
  [Finite (genericPoints X)] [CompactSpace X] [IsReduced X] {k : Type u} [Field k]
  (q : X ⟶ Spec (.of k)) [LocallyOfFiniteType q] (hdim : topologicalKrullDim X ≤ 1)

open scoped Classical in
/-- The incidence graph `nodalGraph q hdim Z` of `X` along `Z` with the marked points `M`, each
attached to a component in `G` through it (if any). -/
noncomputable def markedGraph (Z : Set X) (G M : Finset X) :
    IncidenceGraph X (nodesIn q Z) M where
  ends := (nodalGraph q hdim Z).ends
  genus := (nodalGraph q hdim Z).genus
  mark d := if h : ∃ v ∈ G, d.1 ∈ closure {v} then h.choose else d.1
  eligible := (nodalGraph q hdim Z).eligible

open scoped Classical in
/-- A mark lying on a component of `G` is attached to such a component. -/
theorem markedGraph_mark_mem {Z : Set X} {G M : Finset X} (d : M)
    (h : ∃ v ∈ G, d.1 ∈ closure {v}) :
    (markedGraph q hdim Z G M).mark d ∈ G ∧ d.1 ∈ closure {(markedGraph q hdim Z G M).mark d} := by
  have e : (markedGraph q hdim Z G M).mark d = h.choose := dif_pos h
  rw [e]
  exact h.choose_spec

end MarkedGraph

section GenericFibreChi

variable {V : Type u} [CommRing V] [Finite (PrimeSpectrum V)] {X : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of V)) (z : X) [CompactSpace X] [IsSeparated p]

/-- `ClosureComponent.eulerChar_genericFibre_eq` over a residue point `t = p z` given by an
equation. -/
theorem eulerChar_genericFibre_eq_of_eq {t : PrimeSpectrum V} (htz : p z = t) {P : Scheme.{u}}
    [IsReduced P] [CompactSpace P] [IsAffineHom (pullback.diagonal (terminal.from P))]
    (i : P ⟶ pullback p (residuePt t)) [IsClosedImmersion i]
    (hi : Set.range i = pullback.fst p (residuePt t) ⁻¹' closure {z}) :
    CurvesField.Genus.eulerChar (genericFibre p z)
        (structureCoeff (bcSnd (algebraMap (BaseRing p z) (GenericField p z)) (closureToBase p z))) =
      CurvesField.Genus.eulerChar P (structureCoeff (i ≫ pullback.snd p (residuePt t))) := by
  subst htz
  exact eulerChar_genericFibre_eq p z i hi

end GenericFibreChi


section Main

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [Finite (PrimeSpectrum V)]
  {X C : Scheme.{u}} (β : X ⟶ C) (g : C ⟶ Spec (CommRingCat.of V)) (D' : X.IdealSheafData)

open scoped Classical in
/-- **Exceptional components specialize to exceptional trees** (blueprint
`lem:sm-bd-exc-specialize`; Temkin, proof of Lemma 4.4.4, T:3162–3168, in the corrected form of
ERRATA T57). Let `V` be a valuation ring with finitely many primes and all `Frac(V/𝔭)` separably
closed, `(β ≫ g : X → C → Spec V, D')` a semi-stable pair, proper and projective over `V`, `g`
proper, with algebraically closed residue fields at `t` and at the closed point `s₀`. Let `ζ` be
a generic point of the fibre `X_t` whose component `Z = closure {ζ}` is contracted by `β_t`, has
`χ(𝒪_{Z_red}) = 1` (arithmetic genus `0`) and at most two special points. Then the closed fibre
`X_{s₀}` has a combinatorially exceptional component (`IsCombExceptional`).

The trace `Y = Z̄ ∩ X_{s₀}` of the closure `Z̄` of `Z` is connected (Zariski, lane COH3C over
`V ⧸ 𝔭_t`), a union of components of `X_{s₀}` (`exists_mem_genericPoints_preimage_closure`),
contracted (`eq_of_mem_closure_of_isAlgebraicAt`), with `χ(𝒪_{Ȳ_{s₀}}) = χ(𝒪_{Z_red}) = 1`
(`ClosureComponent.eulerChar_fibreAt_eq`). Since `Ȳ_{s₀}` is reduced (`ClosureComponentLocal`),
its combinatorial genus is at most `p_a = 0` (`combGenus_le_arithmeticGenus`), so `Y` is a
`ℙ¹`-tree of the incidence graph of `X_{s₀}`, exceptional by the count of
`ClosureComponentLocal`, and it contains an exceptional component
(`CurvesField.IncidenceGraph.IsExceptionalTree.exists_isExceptional`). The hypothesis `hloc`
(the étale-local part of `lem:sm-bd-closure-component`) is not formalized; the nonnegativity of
the genera of the normalized components of `X_{s₀}` is `componentGenus_nonneg`. -/
theorem exists_isCombExceptional_closedFibre (hloc : ClosureComponentLocal.{u})
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsProper (β ≫ g)] [IsProper g] (hp : IsProjectiveOver (β ≫ g))
    (hpair : DeJong.IsSemistablePair (β ≫ g) D')
    [IsAlgClosed (IsLocalRing.closedPoint V).asIdeal.ResidueField]
    {t : PrimeSpectrum V} [IsAlgClosed t.asIdeal.ResidueField]
    (ζ : pullback (C := Scheme.{u}) (β ≫ g) (residuePt t))
    (hζ : ζ ∈ genericPoints (pullback (C := Scheme.{u}) (β ≫ g) (residuePt t)))
    (hcontr : (pullbackCompMap β g (residuePt t) '' closure {ζ}).Subsingleton)
    (hχ : eulerChar (closureScheme ζ)
      (structureCoeff (closureι ζ ≫ pullback.snd (β ≫ g) (residuePt t))) = 1)
    (hspec : (closure {ζ} ∩ specialPoints (β ≫ g) D' (residuePt t)).encard ≤ 2) :
    ∃ v, IsCombExceptional β g D' (residuePt (IsLocalRing.closedPoint V)) v := by
  have hnod : DeJong.IsNodalCurve (β ≫ g) := hpair.nodal
  have hts : (β ≫ g) (pullback.fst (β ≫ g) (residuePt t) ζ) ⤳ IsLocalRing.closedPoint V :=
    specializes_closedPoint _
  -- the fibres are curves
  have hpure_t : ∀ W ∈ irreducibleComponents (pullback (C := Scheme.{u}) (β ≫ g) (residuePt t)),
      topologicalKrullDim W = 1 := fun W hW =>
    hnod.pureGeometricFibers t.asIdeal.ResidueField (residuePt t) W hW
  have hpure₀ : ∀ W ∈ irreducibleComponents
      (pullback (C := Scheme.{u}) (β ≫ g) (residuePt (IsLocalRing.closedPoint V))),
      topologicalKrullDim W = 1 := fun W hW =>
    hnod.pureGeometricFibers _ (residuePt (IsLocalRing.closedPoint V)) W hW
  have hdim₀ : topologicalKrullDim
      (pullback (C := Scheme.{u}) (β ≫ g) (residuePt (IsLocalRing.closedPoint V))) ≤ 1 :=
    BlowDown.topologicalKrullDim_le_one_of_forall_irreducibleComponents fun W hW =>
      (hpure₀ W hW).le
  have := CurvesField.Genus.isLocallyNoetherian_of_locallyOfFiniteType
    (pullback.snd (β ≫ g) (residuePt (IsLocalRing.closedPoint V)))
  have : IsNoetherian
      (pullback (C := Scheme.{u}) (β ≫ g) (residuePt (IsLocalRing.closedPoint V))) := {}
  -- the trace `Y` of the closure of `z` on the closed fibre is a connected union of components
  have hz : ¬ IsAlgebraicAt (β ≫ g) (pullback.fst (β ≫ g) (residuePt t) ζ) :=
    not_isAlgebraicAt_of_mem_genericPoints (β ≫ g) hpure_t hζ
  obtain ⟨w₀, hw₀g, hw₀⟩ := exists_mem_genericPoints_preimage_closure (β ≫ g) hdim₀ hz
  have hYc : IsClosed (pullback.fst (β ≫ g) (residuePt (IsLocalRing.closedPoint V)) ⁻¹'
      closure {pullback.fst (β ≫ g) (residuePt t) ζ}) :=
    isClosed_closure.preimage
      (pullback.fst (β ≫ g) (residuePt (IsLocalRing.closedPoint V))).continuous
  have hYconn := isConnected_preimage_closure (β ≫ g) (pullback.fst (β ≫ g) (residuePt t) ζ) hts
    hsep hp
  have hcurve := BlowDown.exists_mem_genericPoints_of_isConnected hdim₀ hYc hYconn
    ⟨w₀, hw₀, hw₀g⟩
  -- the component `Z` is contracted to a point algebraic over `κ(t)`
  have hfst : ∀ (a : PrimeSpectrum V) (w : pullback (C := Scheme.{u}) (β ≫ g) (residuePt a)),
      pullback.fst g (residuePt a) (pullbackCompMap β g (residuePt a) w) =
        β (pullback.fst (β ≫ g) (residuePt a) w) := by
    intro a w
    rw [← Scheme.Hom.comp_apply, Curves.pullbackCompMap_fst, Scheme.Hom.comp_apply]
  obtain ⟨y, hyZ, hyc⟩ := IsClosed.exists_closed_singleton (S := closure {ζ}) isClosed_closure
    ⟨ζ, subset_closure rfl⟩
  have hy1 : IsAlgebraicAt (β ≫ g) (pullback.fst (β ≫ g) (residuePt t) y) :=
    isAlgebraicAt_of_isClosed (β ≫ g) t y hyc
  have hy2 : IsAlgebraicAt g (β (pullback.fst (β ≫ g) (residuePt t) y)) :=
    isAlgebraicAt_of_comp hy1
  have hβz : β (pullback.fst (β ≫ g) (residuePt t) y) =
      β (pullback.fst (β ≫ g) (residuePt t) ζ) := by
    rw [← hfst, ← hfst, hcontr (Set.mem_image_of_mem _ hyZ)
      (Set.mem_image_of_mem _ (subset_closure rfl))]
  rw [hβz] at hy2
  -- so is the trace `Y`
  have hcontr₀ : (pullbackCompMap β g (residuePt (IsLocalRing.closedPoint V)) ''
      (pullback.fst (β ≫ g) (residuePt (IsLocalRing.closedPoint V)) ⁻¹'
        closure {pullback.fst (β ≫ g) (residuePt t) ζ})).Subsingleton := by
    rintro _ ⟨y₁, hy₁, rfl⟩ _ ⟨y₂, hy₂, rfl⟩
    apply (isEmbedding_fst_residuePt g _).injective
    have hmem : ∀ w ∈ (pullback.fst (β ≫ g) (residuePt (IsLocalRing.closedPoint V)) ⁻¹'
        closure {pullback.fst (β ≫ g) (residuePt t) ζ}),
        pullback.fst g _ (pullbackCompMap β g _ w) ∈
          closure {β (pullback.fst (β ≫ g) (residuePt t) ζ)} := by
      intro w hw
      rw [hfst]
      have := image_closure_subset_closure_image β.continuous (Set.mem_image_of_mem β hw)
      rwa [Set.image_singleton] at this
    exact eq_of_mem_closure_of_isAlgebraicAt hsep g hy2 (hmem y₁ hy₁) (hmem y₂ hy₂)
      (apply_fst_residuePt g _) (apply_fst_residuePt g _)
  -- the closed fibre is a reduced projective nodal curve with finitely many double points
  have hred₀ : IsReduced
      (pullback (C := Scheme.{u}) (β ≫ g) (residuePt (IsLocalRing.closedPoint V))) :=
    DeJong.IsNodalCurve.isReduced_pullback (β ≫ g) _ _
  have hnodal₀ : ∀ y : pullback (C := Scheme.{u}) (β ≫ g) (residuePt (IsLocalRing.closedPoint V)),
      IsClosed ({y} : Set _) →
      DeJong.IsSmoothAt (pullback.snd (β ≫ g) (residuePt (IsLocalRing.closedPoint V))) y ∨
        Geometry.IsGeometricOrdinaryDoublePoint
          (pullback.snd (β ≫ g) (residuePt (IsLocalRing.closedPoint V))) y := fun y hy =>
    (hnod.geometricNodes _ (residuePt _) y hy).imp_left
      (DeJong.isSmoothAt_iff_mem_smoothLocus _ _).mpr
  have hp₀ : IsProjectiveOver (pullback.snd (β ≫ g) (residuePt (IsLocalRing.closedPoint V))) :=
    Cohomology.Connected.isProjectiveOver_bcSnd _ hp
  -- the normalized components of `X_{s₀}` have nonnegative genus
  have hg : ∀ v ∈ genericPoints
      (pullback (C := Scheme.{u}) (β ≫ g) (residuePt (IsLocalRing.closedPoint V))),
      0 ≤ componentGenus
        (structureCoeff (pullback.snd (β ≫ g) (residuePt (IsLocalRing.closedPoint V)))) v := by
    intro v hv
    refine componentGenus_nonneg _ hp₀ hdim₀ ?_
    by_contra hno
    push Not at hno
    have hcl : IsClosed ({v} : Set _) := by
      have : closure {v} = ({v} : Set _) :=
        Set.Subset.antisymm (fun y hy => hno y hy) subset_closure
      rw [← this]
      exact isClosed_closure
    exact BlowDown.not_mem_genericPoints_of_isClosed hpure₀ hcl hv
  have : Finite (genericPoints
      (pullback (C := Scheme.{u}) (β ≫ g) (residuePt (IsLocalRing.closedPoint V)))) :=
    (genericPoints.finite NoetherianSpace.finite_irreducibleComponents).to_subtype
  have hnodesfin := finite_nodesIn
    (pullback.snd (β ≫ g) (residuePt (IsLocalRing.closedPoint V))) hdim₀ hp₀
    (pullback.fst (β ≫ g) (residuePt (IsLocalRing.closedPoint V)) ⁻¹'
        closure {pullback.fst (β ≫ g) (residuePt t) ζ})
  let : Fintype (nodesIn (pullback.snd (β ≫ g) (residuePt (IsLocalRing.closedPoint V)))
      (pullback.fst (β ≫ g) (residuePt (IsLocalRing.closedPoint V)) ⁻¹'
        closure {pullback.fst (β ≫ g) (residuePt t) ζ})) := hnodesfin.fintype
  -- the closed fibre `T = Ȳ_{s₀}` of the closure: reduced (`hloc`), `χ = 1`, a union of components
  obtain ⟨hredT, hcount⟩ := hloc V hsep X (β ≫ g) D' hp hpair t ζ hζ
  have htz : (β ≫ g) (pullback.fst (β ≫ g) (residuePt t) ζ) = t := apply_fst_residuePt _ ζ
  have hi : Set.range (closureι ζ) = pullback.fst (β ≫ g) (residuePt t) ⁻¹'
      closure {pullback.fst (β ≫ g) (residuePt t) ζ} := by
    rw [range_closureι, closure_singleton_eq_preimage]
  have hχT : eulerChar (fibreAt (β ≫ g) (pullback.fst (β ≫ g) (residuePt t) ζ) hts)
      (structureCoeff (fibreAtι (β ≫ g) _ hts ≫
        pullback.snd (β ≫ g) (residuePt (IsLocalRing.closedPoint V)))) = 1 := by
    rw [closureFibreι_snd, ← hχ,
      ← eulerChar_genericFibre_eq_of_eq (β ≫ g) _ htz (closureι ζ) hi]
    exact eulerChar_fibreAt_eq (β ≫ g) _ hts hp
  have hdimT : topologicalKrullDim (fibreAt (β ≫ g) (pullback.fst (β ≫ g) (residuePt t) ζ) hts)
      ≤ 1 :=
    (fibreAtι (β ≫ g) _ hts).isClosedEmbedding.isInducing.topologicalKrullDim_le.trans hdim₀
  have hrangeT := range_fibreAtι (β ≫ g) (pullback.fst (β ≫ g) (residuePt t) ζ) hts
  have hR : ∀ x ∈ Set.range (fibreAtι (β ≫ g) _ hts), ∃ v ∈ genericPoints
      (pullback (C := Scheme.{u}) (β ≫ g) (residuePt (IsLocalRing.closedPoint V))),
      v ∈ Set.range (fibreAtι (β ≫ g) _ hts) ∧ x ∈ closure {v} := by
    rw [hrangeT]
    intro x hx
    obtain ⟨v, hvY, hvg, hxv⟩ := hcurve x hx
    exact ⟨v, hvg, hvY, hxv⟩
  have hgenT := mem_genericPoints_iff_of_isEmbedding
    (fibreAtι (β ≫ g) _ hts).isClosedEmbedding.isEmbedding hR
  have : Finite (genericPoints
      (fibreAt (β ≫ g) (pullback.fst (β ≫ g) (residuePt t) ζ) hts)) := by
    have hf : genericPoints (fibreAt (β ≫ g) (pullback.fst (β ≫ g) (residuePt t) ζ) hts) ⊆
        fibreAtι (β ≫ g) _ hts ⁻¹' genericPoints _ := fun η hη => (hgenT η).mp hη
    exact (((Set.toFinite _).preimage
      (fibreAtι (β ≫ g) _ hts).isClosedEmbedding.injective.injOn).subset hf).to_subtype
  have : IsReduced (fibreAt (β ≫ g) (pullback.fst (β ≫ g) (residuePt t) ζ) hts) := hredT
  -- the components of `X_{s₀}` in `Y`
  let G₀ : Finset (pullback (C := Scheme.{u}) (β ≫ g) (residuePt (IsLocalRing.closedPoint V))) :=
    (genericFinset _).filter (· ∈ pullback.fst (β ≫ g) (residuePt (IsLocalRing.closedPoint V)) ⁻¹'
      closure {pullback.fst (β ≫ g) (residuePt t) ζ})
  have hG₀ : (G₀ : Set _) = genericPoints _ ∩
      pullback.fst (β ≫ g) (residuePt (IsLocalRing.closedPoint V)) ⁻¹'
        closure {pullback.fst (β ≫ g) (residuePt t) ζ} := by
    ext v
    simp [G₀, mem_genericFinset]
  have hmemG₀ : ∀ v, v ∈ G₀ ↔ v ∈ genericPoints _ ∧
      v ∈ pullback.fst (β ≫ g) (residuePt (IsLocalRing.closedPoint V)) ⁻¹'
        closure {pullback.fst (β ≫ g) (residuePt t) ζ} := fun v => by
    rw [← Finset.mem_coe, hG₀]
    rfl
  have hY : ∀ η, fibreAtι (β ≫ g) _ hts η ∈
      pullback.fst (β ≫ g) (residuePt (IsLocalRing.closedPoint V)) ⁻¹'
        closure {pullback.fst (β ≫ g) (residuePt t) ζ} := fun η => by
    rw [← hrangeT]
    exact ⟨η, rfl⟩
  have hGG' : ∀ η, η ∈ genericFinset _ ↔ fibreAtι (β ≫ g) _ hts η ∈ G₀ := fun η => by
    rw [mem_genericFinset, hgenT, hmemG₀]
    exact ⟨fun h => ⟨h, hY η⟩, fun h => h.1⟩
  have hGj : ∀ v ∈ G₀, v ∈ Set.range (fibreAtι (β ≫ g) _ hts) := fun v hv => by
    rw [hrangeT]
    exact ((hmemG₀ v).mp hv).2
  have hGgen : ∀ v ∈ G₀, v ∈ genericPoints _ := fun v hv => ((hmemG₀ v).mp hv).1
  have hpT : IsProjectiveOver (fibreAtι (β ≫ g) _ hts ≫
      pullback.snd (β ≫ g) (residuePt (IsLocalRing.closedPoint V))) := by
    rw [closureFibreι_snd]
    exact Cohomology.Connected.isProjectiveOver_bcSnd _ (isProjectiveOver_closureToBase _ _ hp)
  have hZT : ∀ e : nodesIn (pullback.snd (β ≫ g) (residuePt (IsLocalRing.closedPoint V)))
      (pullback.fst (β ≫ g) (residuePt (IsLocalRing.closedPoint V)) ⁻¹'
        closure {pullback.fst (β ≫ g) (residuePt t) ζ}),
      e.1 ∈ Set.range (fibreAtι (β ≫ g) _ hts) := fun e => by
    rw [hrangeT]
    exact e.2.1
  -- `γ(Y) ≤ p_a(Ȳ_{s₀}) = 0`, and `Y` is connected in the incidence graph, so a `ℙ¹`-tree
  have hγ := combGenus_le_arithmeticGenus
    (pullback.snd (β ≫ g) (residuePt (IsLocalRing.closedPoint V))) (fibreAtι (β ≫ g) _ hts)
    hdim₀ hdimT G₀ (genericFinset _) coe_genericFinset hGG' hGj hGgen
    (fun v hv => hg v (hGgen v hv)) hpT hZT
  have hpaT : arithmeticGenus (fibreAt (β ≫ g) (pullback.fst (β ≫ g) (residuePt t) ζ) hts)
      (structureCoeff (fibreAtι (β ≫ g) _ hts ≫
        pullback.snd (β ≫ g) (residuePt (IsLocalRing.closedPoint V)))) = 0 := by
    rw [arithmeticGenus, hχT]
    norm_num
  have hunion : (⋃ v ∈ G₀, closure ({v} : Set _)) =
      pullback.fst (β ≫ g) (residuePt (IsLocalRing.closedPoint V)) ⁻¹'
        closure {pullback.fst (β ≫ g) (residuePt t) ζ} := by
    refine Set.Subset.antisymm (Set.iUnion₂_subset fun v hv =>
      closure_minimal (Set.singleton_subset_iff.mpr ((hmemG₀ v).mp hv).2) hYc) fun y hy => ?_
    obtain ⟨v, hvY, hvg, hyv⟩ := hcurve y hy
    exact Set.mem_biUnion ((hmemG₀ v).mpr ⟨hvg, hvY⟩) hyv
  have hG₀ne : G₀.Nonempty := ⟨w₀, (hmemG₀ w₀).mpr ⟨hw₀g, hw₀⟩⟩
  have hconn := isConnected_nodalGraph
    (pullback.snd (β ≫ g) (residuePt (IsLocalRing.closedPoint V))) hdim₀ hYc hG₀
    (fun y _ hy => hnodal₀ y hy) (Finset.Subset.refl _) hG₀ne
    (by rw [hunion]; exact hYconn.isPreconnected)
  have hγ0 : (nodalGraph (pullback.snd (β ≫ g) (residuePt (IsLocalRing.closedPoint V))) hdim₀
      (pullback.fst (β ≫ g) (residuePt (IsLocalRing.closedPoint V)) ⁻¹'
        closure {pullback.fst (β ≫ g) (residuePt t) ζ})).combGenus G₀ = 0 :=
    le_antisymm (hγ.trans hpaT.le) (IncidenceGraph.combGenus_nonneg hconn)
  have hP1 := IncidenceGraph.isP1Tree_iff_combGenus_eq_zero.mpr ⟨hconn, hγ0⟩
  -- the marks and the count of special points
  have hcnt := hcount.trans hspec
  have hMfin : (closedMarkPoints (β ≫ g) D' (pullback.fst (β ≫ g) (residuePt t) ζ)).Finite :=
    Set.finite_of_encard_le_coe (le_trans le_add_self hcnt)
  let M := hMfin.toFinset
  let Γ := markedGraph (pullback.snd (β ≫ g) (residuePt (IsLocalRing.closedPoint V))) hdim₀
    (pullback.fst (β ≫ g) (residuePt (IsLocalRing.closedPoint V)) ⁻¹'
      closure {pullback.fst (β ≫ g) (residuePt t) ζ}) G₀ M
  have hends : ∀ e, Γ.ends e = (nodalGraph (pullback.snd (β ≫ g)
      (residuePt (IsLocalRing.closedPoint V))) hdim₀ (pullback.fst (β ≫ g)
        (residuePt (IsLocalRing.closedPoint V)) ⁻¹' closure {pullback.fst (β ≫ g) (residuePt t) ζ})).ends e :=
    fun _ => rfl
  have hP1Γ : Γ.IsP1Tree G₀ := hP1
  have hmk : ((Γ.marks G₀).card : ℕ∞) ≤
      (closedMarkPoints (β ≫ g) D' (pullback.fst (β ≫ g) (residuePt t) ζ)).encard := by
    rw [hMfin.encard_eq_coe_toFinset_card]
    exact_mod_cast (Finset.card_le_univ _).trans (Fintype.card_coe M).le
  have hbd : ((Γ.boundary G₀).card : ℕ∞) ≤
      (closedBoundaryPoints (β ≫ g) (pullback.fst (β ≫ g) (residuePt t) ζ)).encard := by
    rw [← Finset.card_image_of_injective _ Subtype.val_injective,
      ← Set.encard_coe_eq_coe_finsetCard]
    refine Set.encard_le_encard fun y hy => ?_
    rw [Finset.coe_image] at hy
    obtain ⟨e, he, rfl⟩ := hy
    obtain ⟨-, v, hv, hvG⟩ := IncidenceGraph.mem_boundary.mp (Finset.mem_coe.mp he)
    obtain ⟨hvg, hev⟩ := (mem_nodalGraph_ends _ hdim₀ e v).mp hv
    refine ⟨e.2.1, e.2.2.1, e.2.2.2.2, v, hvg, fun hvY => hvG ((hmemG₀ v).mpr ⟨hvg, hvY⟩), hev⟩
  have hexc : Γ.IsExceptionalTree G₀ := by
    refine ⟨hP1Γ, fun v hv => ⟨((hmemG₀ v).mp hv).2, ((hmemG₀ v).mp hv).1⟩, ?_⟩
    have h : ((Γ.marks G₀).card : ℕ∞) + (Γ.boundary G₀).card ≤ 2 :=
      calc _ ≤ (closedMarkPoints (β ≫ g) D' (pullback.fst (β ≫ g) (residuePt t) ζ)).encard +
            (closedBoundaryPoints (β ≫ g) (pullback.fst (β ≫ g) (residuePt t) ζ)).encard :=
            add_le_add hmk hbd
        _ = _ := add_comm _ _
        _ ≤ 2 := hcnt
    exact_mod_cast h
  obtain ⟨v, hvG, hvexc⟩ := hexc.exists_isExceptional
  -- the exceptional vertex is a combinatorially exceptional component
  obtain ⟨-, hgen0, hinner, hcount1⟩ := IncidenceGraph.isExceptional_iff.mp hvexc
  have hvg := hGgen v hvG
  have hvY := ((hmemG₀ v).mp hvG).2
  have hclv : closure {v} ⊆ pullback.fst (β ≫ g) (residuePt (IsLocalRing.closedPoint V)) ⁻¹'
      closure {pullback.fst (β ≫ g) (residuePt t) ζ} :=
    closure_minimal (Set.singleton_subset_iff.mpr hvY) hYc
  have hnode : ∀ y ∈ closure {v}, IsClosed ({y} : Set _) →
      Geometry.IsGeometricOrdinaryDoublePoint
        (pullback.snd (β ≫ g) (residuePt (IsLocalRing.closedPoint V))) y →
      ∃ hy : y ∈ nodesIn (pullback.snd (β ≫ g) (residuePt (IsLocalRing.closedPoint V)))
        (pullback.fst (β ≫ g) (residuePt (IsLocalRing.closedPoint V)) ⁻¹'
          closure {pullback.fst (β ≫ g) (residuePt t) ζ}), ∃ w ∈ Γ.ends ⟨y, hy⟩, w ≠ v := by
    intro y hyv hyc hn
    have hyn : y ∈ nodesIn (pullback.snd (β ≫ g) (residuePt (IsLocalRing.closedPoint V)))
        (pullback.fst (β ≫ g) (residuePt (IsLocalRing.closedPoint V)) ⁻¹'
          closure {pullback.fst (β ≫ g) (residuePt t) ζ}) :=
      ⟨hclv hyv, hyc, BlowDown.not_mem_genericPoints_of_isClosed hpure₀ hyc, hn⟩
    refine ⟨hyn, ?_⟩
    by_contra hall
    push Not at hall
    have : (⟨y, hyn⟩ : nodesIn _ _) ∈ Γ.inner {v} :=
      IncidenceGraph.mem_inner.mpr fun w hw => Finset.mem_singleton.mpr (hall w hw)
    rw [hinner] at this
    exact Finset.notMem_empty _ this
  refine ⟨v, hvg, hcontr₀.anti (Set.image_mono hclv), ?_, ?_, ?_⟩
  · have h0 : (componentGenus (structureCoeff
        (pullback.snd (β ≫ g) (residuePt (IsLocalRing.closedPoint V)))) v).toNat = 0 := hgen0
    exact le_antisymm (Int.toNat_eq_zero.mp h0) (hg v hvg)
  · intro y hyv hyc hn
    obtain ⟨hyn, w, hw, hwv⟩ := hnode y hyv hyc hn
    obtain ⟨hwg, hyw⟩ := (mem_nodalGraph_ends _ hdim₀ ⟨y, hyn⟩ w).mp hw
    exact ⟨w, hwg, hwv, hyw⟩
  · let A := (Γ.boundary {v}).image Subtype.val
    let B := (Γ.marks {v}).image Subtype.val
    have hAB : closure {v} ∩ specialPoints (β ≫ g) D' (residuePt (IsLocalRing.closedPoint V)) ∩
        {y | IsClosed ({y} : Set _)} ⊆ ↑A ∪ ↑B := by
      rintro y ⟨⟨hyv, hys⟩, hyc⟩
      by_cases hsm : DeJong.IsSmoothAt
          (pullback.snd (β ≫ g) (residuePt (IsLocalRing.closedPoint V))) y
      · -- a smooth special point is a mark, on the component `v` only
        have hD : pullback.fst (β ≫ g) (residuePt (IsLocalRing.closedPoint V)) y ∈
            (D'.support : Set X) := by
          rcases hys with h | h
          · exact h
          · exact absurd hsm h
        have hyM : y ∈ M := hMfin.mem_toFinset.mpr ⟨hclv hyv, hD⟩
        right
        rw [Finset.mem_coe, Finset.mem_image]
        refine ⟨⟨y, hyM⟩, ?_, rfl⟩
        rw [IncidenceGraph.mem_marks, Finset.mem_singleton]
        obtain ⟨hmG, hmcl⟩ := markedGraph_mark_mem
          (pullback.snd (β ≫ g) (residuePt (IsLocalRing.closedPoint V))) hdim₀ (Z := pullback.fst (β ≫ g)
          (residuePt (IsLocalRing.closedPoint V)) ⁻¹' closure {pullback.fst (β ≫ g) (residuePt t) ζ})
          ⟨y, hyM⟩ ⟨v, hvG, hyv⟩
        by_contra hne
        have hyn := mem_nodesIn_of_mem_closure
          (pullback.snd (β ≫ g) (residuePt (IsLocalRing.closedPoint V))) hdim₀
          (fun y _ hy => hnodal₀ y hy) (hclv hyv) (hGgen _ hmG) hvg hne hmcl hyv
        have h2 := natCard_fiber_eq_two_of_isGeometricOrdinaryDoublePoint
          (pullback.snd (β ≫ g) (residuePt (IsLocalRing.closedPoint V))) hdim₀ y hyc
          hyn.2.2.1 hyn.2.2.2
        have h1 := natCard_fiber_eq_one_of_isSmoothAt
          (pullback.snd (β ≫ g) (residuePt (IsLocalRing.closedPoint V))) hdim₀ y hyc
          hyn.2.2.1 hsm
        omega
      · -- a non-smooth closed point is a double point joining `v` to another component
        have hn := (hnodal₀ y hyc).resolve_left hsm
        obtain ⟨hyn, w, hw, hwv⟩ := hnode y hyv hyc hn
        left
        rw [Finset.mem_coe, Finset.mem_image]
        refine ⟨⟨y, hyn⟩, ?_, rfl⟩
        rw [IncidenceGraph.mem_boundary]
        refine ⟨⟨v, (mem_nodalGraph_ends _ hdim₀ _ v).mpr ⟨hvg, hyv⟩,
          Finset.mem_singleton_self v⟩, w, hw, ?_⟩
        rw [Finset.mem_singleton]
        exact hwv
    refine (Set.encard_le_encard hAB).trans ((Set.encard_union_le _ _).trans ?_)
    rw [Set.encard_coe_eq_coe_finsetCard, Set.encard_coe_eq_coe_finsetCard,
      Finset.card_image_of_injective _ Subtype.val_injective,
      Finset.card_image_of_injective _ Subtype.val_injective]
    have h : (Γ.boundary {v}).card + (Γ.marks {v}).card ≤ 2 := by omega
    exact_mod_cast h

end Main

end DeJongAlterations.StableModification.BlowDown.ExcSpecialize
