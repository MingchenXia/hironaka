/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.NumericalDescent
import DeJongAlterations.StableModification.BlowDown.StableComb
import DeJongAlterations.StableModification.BlowDown.ContractingExists
import DeJongAlterations.StableModification.CurvesField.OrdinaryGluing

/-!
# The blow-down results with the proved hypotheses discharged

This file restates results of the blow-down lanes with the hypotheses that are now theorems
removed:

* `NoClosedExc.NodalComponentGenus` (`ComponentGenus.nodalComponentGenus`),
* `NoClosedExc.NumericalDescent` (`NumericalDescent.numericalDescent`),
* the nonnegativity of component genera (`ExcSpecialize.componentGenus_nonneg`), for fibres of
  nodal curves (`componentGenus_fiber_nonneg`) and for curves of pure dimension one,
* `OrdinaryPointCompletion κ` over an algebraically closed field
  (`CurvesField.OrdinaryGluing.ordinaryPointCompletion_of_isAlgClosed`).

## Main results

* `stability_criterion_fibre`, `stability_criterion_fibre_iff`: lane T44A2's fibrewise form of
  Temkin's stability criterion (Temkin, *Stable modification of relative curves*, J. Algebraic
  Geom. 19 (2010), Lemma 4.4.2) without `hg`, and the equivalence without `hg` and `hcompl`;
* `stabdown_scheme`, `stabdown_scheme_of_isP1Tree`, `stabdown_scheme_normalization`,
  `stabdown_scheme_normalization_of_isP1Tree`, `stabdown_scheme_normalization_iff`: lane CRV4's
  scheme-level forms of Temkin's Corollary B.2 with `hg` replaced by the pure dimension one of
  `C'` (`hpure'`);
* `numericallyStableFibre_residuePt_of_closedPoint`, `numericallyStableFibre_of_closedPoint`,
  `numericallyStable_iff_closedPoint`, `isStableModification_of_numericallyStableFibre_closedPoint`,
  `not_isCombExceptional_of_numericallyStableFibre`,
  `numericallyStableFibre_of_forall_not_isCombExceptional_of_descent`,
  `isStableModification_of_forall_not_isCombExceptional`: Temkin's Lemma 4.4.4 in the forms of
  `BlowDown.NoClosedExc` with only `ExcSpecialize.ClosureComponentLocal` left as a hypothesis;
* `exists_isStableModification_of_isSemistableStage`: lane T44B's Temkin Proposition 4.4.6 with
  only `ClosureComponentLocal` and the contracting morphisms (`ContractingMorphismExists`) left as
  hypotheses.

Blueprint: `sm-blow-down-unconditional.tex`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology Module
  IsLocalRing

namespace DeJongAlterations.StableModification.BlowDown.Unconditional

universe u

open DeJongAlterations.StableModification.Cohomology
open DeJongAlterations.StableModification.CurvesField
open DeJongAlterations.StableModification.CurvesField.IncidenceGraph
open DeJongAlterations.StableModification.CurvesField.Genus
open DeJongAlterations.StableModification.CurvesField.OrdinaryCompletion
open Geometry.ModificationCenter (isomorphismOpen center)
open ClosureComponent (residuePt)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

section Dimension

/-- A point whose closure has dimension one is not a closed point. -/
theorem exists_ne_mem_closure_of_topologicalKrullDim_eq_one {X : Type*} [TopologicalSpace X]
    {v : X} (h : topologicalKrullDim (closure {v} : Set X) = 1) : ∃ y ∈ closure {v}, y ≠ v := by
  by_contra hne
  push Not at hne
  have hsub : closure ({v} : Set X) = {v} :=
    Set.eq_singleton_iff_unique_mem.mpr ⟨subset_closure rfl, hne⟩
  rw [hsub] at h
  have : DiscreteTopology ({v} : Set X) := Subsingleton.discreteTopology
  have h0 := topologicalKrullDim_zero_of_discreteTopology ({v} : Set X)
  rw [h] at h0
  exact absurd h0 (by decide)

/-- In a space whose irreducible components have dimension one, the component of a generic point
is not a point. -/
theorem exists_ne_mem_closure_of_mem_genericPoints {X : Type*} [TopologicalSpace X] {v : X}
    (hv : v ∈ genericPoints X)
    (hpure : ∀ W ∈ irreducibleComponents X, topologicalKrullDim W = 1) :
    ∃ y ∈ closure {v}, y ≠ v :=
  exists_ne_mem_closure_of_topologicalKrullDim_eq_one (hpure _ hv)

end Dimension

section FibreGenus

variable {V : Type u} [CommRing V] {X : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of V))

/-- **The genera of the normalized components of a fibre of a projective nodal curve are
nonnegative** (`ExcSpecialize.componentGenus_nonneg`; the components of the fibres of a nodal
curve have dimension one). -/
theorem componentGenus_fiber_nonneg [DeJong.IsNodalCurve q] [IsProper q] (hp : IsProjectiveOver q)
    (s : Spec (CommRingCat.of V)) [IsAlgClosed ((Spec (CommRingCat.of V)).residueField s)]
    {v : q.fiber s} (hv : v ∈ genericPoints (q.fiber s)) :
    0 ≤ componentGenus (structureCoeff (A := ↑((Spec (CommRingCat.of V)).residueField s))
      (q.fiberToSpecResidueField s)) v := by
  have : IsAlgClosed (IsLocalRing.ResidueField ((Spec (CommRingCat.of V)).presheaf.stalk s)) :=
    ‹IsAlgClosed ((Spec (CommRingCat.of V)).residueField s)›
  have hpure : ∀ W ∈ irreducibleComponents (q.fiber s), topologicalKrullDim W = 1 :=
    fun W hW => DeJong.IsNodalCurve.pureGeometricFibers (g := q)
      (↑((Spec (CommRingCat.of V)).residueField s))
      ((Spec (CommRingCat.of V)).fromSpecResidueField s) W hW
  have hdim : topologicalKrullDim (q.fiber s) ≤ 1 :=
    BlowDown.topologicalKrullDim_le_one_of_forall_irreducibleComponents fun W hW =>
      (hpure W hW).le
  have : CompactSpace (q.fiber s) :=
    BlowDown.compactSpace_of_quasiCompact (q.fiberToSpecResidueField s)
  exact ExcSpecialize.componentGenus_nonneg (q.fiberToSpecResidueField s)
    (isProjectiveOver_fiberToSpecResidueField q s hp) hdim
    (exists_ne_mem_closure_of_mem_genericPoints hv hpure)

end FibreGenus

section Criterion

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] {C C' : Scheme.{u}}
  (p : C ⟶ Spec (CommRingCat.of V)) (f : C' ⟶ C) (s : Spec (CommRingCat.of V))

open scoped Classical in
/-- **Temkin's stability criterion, Lemma 4.4.2, fibrewise form** (lane T44A2's
`BlowDown.stability_criterion_fibre`, blueprint `lem:sm-stability-criterion`) without the
hypothesis `hg`: the genera of the components of the contracted fibres are nonnegative
(`componentGenus_fiber_nonneg`). -/
theorem stability_criterion_fibre [Finite (PrimeSpectrum V)]
    [Infinite (IsLocalRing.ResidueField V)]
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    [IsIntegral C] [IsIntegral C'] [IsModification f] [IsProper p] [LocallyOfFinitePresentation p]
    [Flat p] [DeJong.IsNodalCurve (f ≫ p)] (hp : IsProjectiveOver p)
    (hfp : DeJong.IsRelativelyProjective p f)
    (hnormal : IsNormalScheme C) (hcurve : ValuationRing.fiberTrdeg p (genericPoint C) ≤ 1)
    (hη : Curves.IsEtaModification f p)
    [IsAlgClosed ((Spec (CommRingCat.of V)).residueField s)] [IsReduced (p.fiber s)]
    (hpure : ∀ W ∈ irreducibleComponents (p.fiber s), topologicalKrullDim W = 1)
    (J : Finset (p.fiber s)) (hJ : ∀ x, x ∈ J ↔ p.fiberι s x ∈ center f)
    (G : p.fiber s → Finset ((f ≫ p).fiber s))
    (hG : ∀ x ∈ J, (G x : Set ((f ≫ p).fiber s)) = innerPoints (Curves.fiberMap f p s) x)
    (hdim' : topologicalKrullDim ((f ≫ p).fiber s) ≤ 1)
    [Fintype (nodesIn (k := ↑((Spec (CommRingCat.of V)).residueField s))
      ((f ≫ p).fiberToSpecResidueField s) (Curves.fiberMap f p s ⁻¹' (J : Set (p.fiber s))))]
    (m : p.fiber s → ℕ) :
    (∀ x ∈ J, _root_.IsConnected (Curves.fiberMap f p s ⁻¹' {x}) ∧
      ∀ z ∈ Curves.fiberMap f p s ⁻¹' {x}, ∃ v ∈ G x, z ∈ closure {v}) ∧
    ((∀ x ∈ J, (DeJong.IsSmoothAt (p.fiberToSpecResidueField s) x ∨
        Geometry.IsGeometricOrdinaryDoublePoint (p.fiberToSpecResidueField s) x) ∧
        m x ≤ 1 ∧ (m x = 1 → DeJong.IsSmoothAt (p.fiberToSpecResidueField s) x)) →
      ∀ x ∈ J, (nodalGraph ((f ≫ p).fiberToSpecResidueField s) hdim'
          (Curves.fiberMap f p s ⁻¹' (J : Set (p.fiber s)))).IsP1Tree (G x) ∧
        ((nodalGraph ((f ≫ p).fiberToSpecResidueField s) hdim'
          (Curves.fiberMap f p s ⁻¹' (J : Set (p.fiber s)))).boundary (G x)).card + m x ≤ 2) ∧
    ((∀ x ∈ J, (nodalGraph ((f ≫ p).fiberToSpecResidueField s) hdim'
          (Curves.fiberMap f p s ⁻¹' (J : Set (p.fiber s)))).IsP1Tree (G x) ∧
        ((nodalGraph ((f ≫ p).fiberToSpecResidueField s) hdim'
          (Curves.fiberMap f p s ⁻¹' (J : Set (p.fiber s)))).boundary (G x)).card + m x ≤ 2) →
      ∀ x ∈ J, deltaInvariant (normalizationPointsMap (genericPoints (p.fiber s)))
          (structureCoeff (A := ↑((Spec (CommRingCat.of V)).residueField s))
            (p.fiberToSpecResidueField s)) x + 1 =
          Nat.card ↥(normalizationPointsMap (genericPoints (p.fiber s)) ⁻¹' {x}) ∧
        Nat.card ↥(normalizationPointsMap (genericPoints (p.fiber s)) ⁻¹' {x}) ≤ 2 ∧ m x ≤ 1 ∧
        (m x = 1 →
          Nat.card ↥(normalizationPointsMap (genericPoints (p.fiber s)) ⁻¹' {x}) = 1)) := by
  have hp' := DeJong.IsRelativelyProjective.isProjectiveOver hp hfp
  refine BlowDown.stability_criterion_fibre p f s hsep hp hfp hnormal hcurve hη hpure J hJ G hG
    hdim' (fun x hx v hv => ?_) m
  have hv' : v ∈ (G x : Set ((f ≫ p).fiber s)) := hv
  rw [hG x hx] at hv'
  exact componentGenus_fiber_nonneg (f ≫ p) hp' s hv'.1

open scoped Classical in
/-- **Temkin's stability criterion, Lemma 4.4.2, fibrewise form, as an equivalence** (lane
T44A2's `BlowDown.stability_criterion_fibre_iff`, blueprint `lem:sm-stability-criterion`) without
the hypotheses `hg` (`componentGenus_fiber_nonneg`) and `hcompl`
(`CurvesField.OrdinaryGluing.ordinaryPointCompletion_of_isAlgClosed`). -/
theorem stability_criterion_fibre_iff [Finite (PrimeSpectrum V)]
    [Infinite (IsLocalRing.ResidueField V)]
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    [IsIntegral C] [IsIntegral C'] [IsModification f] [IsProper p] [LocallyOfFinitePresentation p]
    [Flat p] [DeJong.IsNodalCurve (f ≫ p)] (hp : IsProjectiveOver p)
    (hfp : DeJong.IsRelativelyProjective p f)
    (hnormal : IsNormalScheme C) (hcurve : ValuationRing.fiberTrdeg p (genericPoint C) ≤ 1)
    (hη : Curves.IsEtaModification f p)
    [IsAlgClosed ((Spec (CommRingCat.of V)).residueField s)] [IsReduced (p.fiber s)]
    (hpure : ∀ W ∈ irreducibleComponents (p.fiber s), topologicalKrullDim W = 1)
    (J : Finset (p.fiber s)) (hJ : ∀ x, x ∈ J ↔ p.fiberι s x ∈ center f)
    (G : p.fiber s → Finset ((f ≫ p).fiber s))
    (hG : ∀ x ∈ J, (G x : Set ((f ≫ p).fiber s)) = innerPoints (Curves.fiberMap f p s) x)
    (hdim' : topologicalKrullDim ((f ≫ p).fiber s) ≤ 1)
    [Fintype (nodesIn (k := ↑((Spec (CommRingCat.of V)).residueField s))
      ((f ≫ p).fiberToSpecResidueField s) (Curves.fiberMap f p s ⁻¹' (J : Set (p.fiber s))))]
    (m : p.fiber s → ℕ) :
    (∀ x ∈ J, (DeJong.IsSmoothAt (p.fiberToSpecResidueField s) x ∨
        Geometry.IsGeometricOrdinaryDoublePoint (p.fiberToSpecResidueField s) x) ∧
        m x ≤ 1 ∧ (m x = 1 → DeJong.IsSmoothAt (p.fiberToSpecResidueField s) x)) ↔
      ∀ x ∈ J, (nodalGraph ((f ≫ p).fiberToSpecResidueField s) hdim'
          (Curves.fiberMap f p s ⁻¹' (J : Set (p.fiber s)))).IsP1Tree (G x) ∧
        ((nodalGraph ((f ≫ p).fiberToSpecResidueField s) hdim'
          (Curves.fiberMap f p s ⁻¹' (J : Set (p.fiber s)))).boundary (G x)).card + m x ≤ 2 := by
  have hp' := DeJong.IsRelativelyProjective.isProjectiveOver hp hfp
  refine BlowDown.stability_criterion_fibre_iff p f s hsep hp hfp hnormal hcurve hη hpure J hJ G
    hG hdim' (fun x hx v hv => ?_) m
    (OrdinaryGluing.ordinaryPointCompletion_of_isAlgClosed _)
  have hv' : v ∈ (G x : Set ((f ≫ p).fiber s)) := hv
  rw [hG x hx] at hv'
  exact componentGenus_fiber_nonneg (f ≫ p) hp' s hv'.1

end Criterion

section StableDown

variable {C C' : Scheme.{u}} (f : C' ⟶ C) (x : C) (U : C.Opens) (hU : ∀ y, y ∈ U ↔ y ≠ x)
  [IsIso (f ∣_ U)] [IsAffineHom (pullback.diagonal (terminal.from C'))] {k : Type u} [Field k]
  [Finite (genericPoints C')]

omit [Finite (genericPoints C')] in
/-- The genera of the components `G = innerPoints f x` of a curve of pure dimension one,
projective over `k = k̄`, are nonnegative (`ExcSpecialize.componentGenus_nonneg`). -/
theorem componentGenus_innerPoints_nonneg [IsAlgClosed k] [CompactSpace C'] [IsReduced C']
    (p' : C' ⟶ Spec (.of k)) [LocallyOfFiniteType p'] (hdim' : topologicalKrullDim C' ≤ 1)
    (hp' : IsProjectiveOver p') (hpure' : ∀ W ∈ irreducibleComponents C', topologicalKrullDim W = 1)
    (G : Finset C') (hG : (G : Set C') = innerPoints f x) :
    ∀ v ∈ G, 0 ≤ componentGenus (structureCoeff p') v := by
  intro v hv
  have hv' : v ∈ (G : Set C') := hv
  rw [hG] at hv'
  exact ExcSpecialize.componentGenus_nonneg p' hp' hdim'
    (exists_ne_mem_closure_of_mem_genericPoints hv'.1 hpure')

open scoped Classical in
include hU in
/-- **Temkin, Corollary B.2, scheme level** (lane CRV4's `CurvesField.Genus.stabdown_scheme`)
with the hypothesis `hg` replaced by the pure dimension one of `C'`
(`componentGenus_innerPoints_nonneg`). -/
theorem stabdown_scheme [IsAlgClosed k] [CompactSpace C]
    [IsAffineHom (pullback.diagonal (terminal.from C))] [IsReduced C] [CompactSpace C']
    [IsReduced C'] [IsProper f] (p : C ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (p' : C' ⟶ Spec (.of k)) [LocallyOfFiniteType p'] (hfp : f ≫ p = p')
    (hxg : x ∉ genericPoints C) (hx : IsClosed {x}) (hdim : topologicalKrullDim C ≤ 1)
    (hdim' : topologicalKrullDim C' ≤ 1) (hp : IsProjectiveOver p) (hp' : IsProjectiveOver p')
    (hpure' : ∀ W ∈ irreducibleComponents C', topologicalKrullDim W = 1)
    (hpa : arithmeticGenus C' (structureCoeff p') = arithmeticGenus C (structureCoeff p))
    (G : Finset C') (hG : (G : Set C') = innerPoints f x) (hZ : _root_.IsConnected (f ⁻¹' {x}))
    (hcurve : ∀ z ∈ f ⁻¹' {x}, ∃ v ∈ G, z ∈ closure {v})
    (hnodal : ∀ y ∈ f ⁻¹' {x}, IsClosed {y} →
      DeJong.IsSmoothAt p' y ∨ Geometry.IsGeometricOrdinaryDoublePoint p' y)
    [Fintype (nodesIn p' (f ⁻¹' {x}))] (V : C.Opens) (hV : IsAffineOpen V) (hxV : x ∈ V) :
    letI := (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤)).toAlgebra
    letI := ((outerMap f x).app V).hom.toAlgebra
    letI := (((outerMap f x).app V).hom.comp
      (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤))).toAlgebra
    haveI : IsScalarTower k Γ(C, V) Γ(normalizationPoints (outerPoints f x), outerMap f x ⁻¹ᵁ V) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    Nat.card (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid
        Γ(normalizationPoints (outerPoints f x), outerMap f x ⁻¹ᵁ V)
        (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl))) =
        ((nodalGraph p' hdim' (f ⁻¹' {x})).boundary G).card ∧
      (rangeIn k (Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal)
          (Localization (Algebra.algebraMapSubmonoid
            Γ(normalizationPoints (outerPoints f x), outerMap f x ⁻¹ᵁ V)
            (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl)) =
        gluing k (Localization (Algebra.algebraMapSubmonoid
            Γ(normalizationPoints (outerPoints f x), outerMap f x ⁻¹ᵁ V)
            (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl)) ↔
        (nodalGraph p' hdim' (f ⁻¹' {x})).IsP1Tree G) :=
  CurvesField.Genus.stabdown_scheme f x U hU p p' hfp hxg hx hdim hdim' hp hp' hpa G hG hZ hcurve
    hnodal (componentGenus_innerPoints_nonneg f x p' hdim' hp' hpure' G hG) V hV hxV

open scoped Classical in
include hU in
/-- **The variant of Corollary B.2 for a disconnected fibre** (lane CRV4's
`CurvesField.Genus.stabdown_scheme_of_isP1Tree`) with `hg` replaced by the pure dimension one of
`C'`. -/
theorem stabdown_scheme_of_isP1Tree [IsAlgClosed k] [CompactSpace C]
    [IsAffineHom (pullback.diagonal (terminal.from C))] [IsReduced C] [CompactSpace C']
    [IsReduced C'] [IsProper f] (p : C ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (p' : C' ⟶ Spec (.of k)) [LocallyOfFiniteType p'] (hfp : f ≫ p = p')
    (hxg : x ∉ genericPoints C) (hx : IsClosed {x}) (hdim : topologicalKrullDim C ≤ 1)
    (hdim' : topologicalKrullDim C' ≤ 1) (hp : IsProjectiveOver p) (hp' : IsProjectiveOver p')
    (hpure' : ∀ W ∈ irreducibleComponents C', topologicalKrullDim W = 1)
    (hpa : arithmeticGenus C' (structureCoeff p') = arithmeticGenus C (structureCoeff p))
    (G : Finset C') (hG : (G : Set C') = innerPoints f x)
    (hcurve : ∀ z ∈ f ⁻¹' {x}, ∃ v ∈ G, z ∈ closure {v})
    (hnodal : ∀ y ∈ f ⁻¹' {x}, IsClosed {y} →
      DeJong.IsSmoothAt p' y ∨ Geometry.IsGeometricOrdinaryDoublePoint p' y)
    [Fintype (nodesIn p' (f ⁻¹' {x}))] (𝒴 : Finset (Finset C')) (hsub : ∀ Y ∈ 𝒴, Y ⊆ G)
    (hcov : ∀ v ∈ G, ∃ Y ∈ 𝒴, v ∈ Y)
    (hsep : ∀ Y ∈ 𝒴, ∀ Y' ∈ 𝒴, Y ≠ Y' → ∀ v ∈ Y, ∀ v' ∈ Y',
      Disjoint (closure ({v} : Set C')) (closure {v'}))
    (htree : ∀ Y ∈ 𝒴, (nodalGraph p' hdim' (f ⁻¹' {x})).IsP1Tree Y)
    (V : C.Opens) (hV : IsAffineOpen V) (hxV : x ∈ V) :
    letI := (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤)).toAlgebra
    letI := ((outerMap f x).app V).hom.toAlgebra
    letI := (((outerMap f x).app V).hom.comp
      (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤))).toAlgebra
    haveI : IsScalarTower k Γ(C, V) Γ(normalizationPoints (outerPoints f x), outerMap f x ⁻¹ᵁ V) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    𝒴.card ≤ 1 ∧
      Nat.card (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid
        Γ(normalizationPoints (outerPoints f x), outerMap f x ⁻¹ᵁ V)
        (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl))) =
        ((nodalGraph p' hdim' (f ⁻¹' {x})).boundary G).card ∧
      rangeIn k (Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal)
          (Localization (Algebra.algebraMapSubmonoid
            Γ(normalizationPoints (outerPoints f x), outerMap f x ⁻¹ᵁ V)
            (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl)) =
        gluing k (Localization (Algebra.algebraMapSubmonoid
            Γ(normalizationPoints (outerPoints f x), outerMap f x ⁻¹ᵁ V)
            (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl)) :=
  CurvesField.Genus.stabdown_scheme_of_isP1Tree f x U hU p p' hfp hxg hx hdim hdim' hp hp' hpa G
    hG hcurve hnodal (componentGenus_innerPoints_nonneg f x p' hdim' hp' hpure' G hG) 𝒴 hsub hcov
    hsep htree V hV hxV

open scoped Classical in
include hU in
/-- **Temkin, Corollary B.2, scheme level, with the normalization of `C`** (lane CRV4's
`CurvesField.Genus.stabdown_scheme_normalization`) with `hg` replaced by the pure dimension one
of `C'`. -/
theorem stabdown_scheme_normalization [IsAlgClosed k] [CompactSpace C]
    [IsAffineHom (pullback.diagonal (terminal.from C))] [Finite (genericPoints C)] [IsReduced C]
    [CompactSpace C'] [IsReduced C'] [IsProper f] (p : C ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (p' : C' ⟶ Spec (.of k)) [LocallyOfFiniteType p'] (hfp : f ≫ p = p')
    (hxg : x ∉ genericPoints C) (hx : IsClosed {x}) (hdim : topologicalKrullDim C ≤ 1)
    (hdim' : topologicalKrullDim C' ≤ 1) (hp : IsProjectiveOver p) (hp' : IsProjectiveOver p')
    (hpure' : ∀ W ∈ irreducibleComponents C', topologicalKrullDim W = 1)
    (hpa : arithmeticGenus C' (structureCoeff p') = arithmeticGenus C (structureCoeff p))
    (G : Finset C') (hG : (G : Set C') = innerPoints f x) (hZ : _root_.IsConnected (f ⁻¹' {x}))
    (hcurve : ∀ z ∈ f ⁻¹' {x}, ∃ v ∈ G, z ∈ closure {v})
    (hnodal : ∀ y ∈ f ⁻¹' {x}, IsClosed {y} →
      DeJong.IsSmoothAt p' y ∨ Geometry.IsGeometricOrdinaryDoublePoint p' y)
    [Fintype (nodesIn p' (f ⁻¹' {x}))] (V : C.Opens) (hV : IsAffineOpen V) (hxV : x ∈ V) :
    letI := (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤)).toAlgebra
    letI := ((normalizationPointsMap (genericPoints C)).app V).hom.toAlgebra
    letI := (((normalizationPointsMap (genericPoints C)).app V).hom.comp
      (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤))).toAlgebra
    haveI : IsScalarTower k Γ(C, V) Γ(normalizationPoints (genericPoints C),
        normalizationPointsMap (genericPoints C) ⁻¹ᵁ V) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    (deltaInvariant (normalizationPointsMap (genericPoints C)) (structureCoeff p) x : ℤ) =
        contractedDelta (nodalGraph p' hdim' (f ⁻¹' {x})) G ∧
      Nat.card (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid
        Γ(normalizationPoints (genericPoints C), normalizationPointsMap (genericPoints C) ⁻¹ᵁ V)
        (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl))) =
        ((nodalGraph p' hdim' (f ⁻¹' {x})).boundary G).card ∧
      (rangeIn k (Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal)
          (Localization (Algebra.algebraMapSubmonoid
            Γ(normalizationPoints (genericPoints C),
              normalizationPointsMap (genericPoints C) ⁻¹ᵁ V)
            (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl)) =
        gluing k (Localization (Algebra.algebraMapSubmonoid
            Γ(normalizationPoints (genericPoints C),
              normalizationPointsMap (genericPoints C) ⁻¹ᵁ V)
            (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl)) ↔
        (nodalGraph p' hdim' (f ⁻¹' {x})).IsP1Tree G) :=
  CurvesField.Genus.stabdown_scheme_normalization f x U hU p p' hfp hxg hx hdim hdim' hp hp' hpa
    G hG hZ hcurve hnodal (componentGenus_innerPoints_nonneg f x p' hdim' hp' hpure' G hG) V hV
    hxV

open scoped Classical in
include hU in
/-- **The variant of Corollary B.2 for a disconnected fibre, with the normalization of `C`**
(lane CRV4's `CurvesField.Genus.stabdown_scheme_normalization_of_isP1Tree`) with `hg` replaced by
the pure dimension one of `C'`. -/
theorem stabdown_scheme_normalization_of_isP1Tree [IsAlgClosed k] [CompactSpace C]
    [IsAffineHom (pullback.diagonal (terminal.from C))] [Finite (genericPoints C)] [IsReduced C]
    [CompactSpace C'] [IsReduced C'] [IsProper f] (p : C ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (p' : C' ⟶ Spec (.of k)) [LocallyOfFiniteType p'] (hfp : f ≫ p = p')
    (hxg : x ∉ genericPoints C) (hx : IsClosed {x}) (hdim : topologicalKrullDim C ≤ 1)
    (hdim' : topologicalKrullDim C' ≤ 1) (hp : IsProjectiveOver p) (hp' : IsProjectiveOver p')
    (hpure' : ∀ W ∈ irreducibleComponents C', topologicalKrullDim W = 1)
    (hpa : arithmeticGenus C' (structureCoeff p') = arithmeticGenus C (structureCoeff p))
    (G : Finset C') (hG : (G : Set C') = innerPoints f x)
    (hcurve : ∀ z ∈ f ⁻¹' {x}, ∃ v ∈ G, z ∈ closure {v})
    (hnodal : ∀ y ∈ f ⁻¹' {x}, IsClosed {y} →
      DeJong.IsSmoothAt p' y ∨ Geometry.IsGeometricOrdinaryDoublePoint p' y)
    [Fintype (nodesIn p' (f ⁻¹' {x}))] (𝒴 : Finset (Finset C')) (hsub : ∀ Y ∈ 𝒴, Y ⊆ G)
    (hcov : ∀ v ∈ G, ∃ Y ∈ 𝒴, v ∈ Y)
    (hsep : ∀ Y ∈ 𝒴, ∀ Y' ∈ 𝒴, Y ≠ Y' → ∀ v ∈ Y, ∀ v' ∈ Y',
      Disjoint (closure ({v} : Set C')) (closure {v'}))
    (htree : ∀ Y ∈ 𝒴, (nodalGraph p' hdim' (f ⁻¹' {x})).IsP1Tree Y)
    (V : C.Opens) (hV : IsAffineOpen V) (hxV : x ∈ V) :
    letI := (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤)).toAlgebra
    letI := ((normalizationPointsMap (genericPoints C)).app V).hom.toAlgebra
    letI := (((normalizationPointsMap (genericPoints C)).app V).hom.comp
      (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤))).toAlgebra
    haveI : IsScalarTower k Γ(C, V) Γ(normalizationPoints (genericPoints C),
        normalizationPointsMap (genericPoints C) ⁻¹ᵁ V) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    𝒴.card ≤ 1 ∧
      Nat.card (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid
        Γ(normalizationPoints (genericPoints C), normalizationPointsMap (genericPoints C) ⁻¹ᵁ V)
        (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl))) =
        ((nodalGraph p' hdim' (f ⁻¹' {x})).boundary G).card ∧
      rangeIn k (Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal)
          (Localization (Algebra.algebraMapSubmonoid
            Γ(normalizationPoints (genericPoints C),
              normalizationPointsMap (genericPoints C) ⁻¹ᵁ V)
            (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl)) =
        gluing k (Localization (Algebra.algebraMapSubmonoid
            Γ(normalizationPoints (genericPoints C),
              normalizationPointsMap (genericPoints C) ⁻¹ᵁ V)
            (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl)) :=
  CurvesField.Genus.stabdown_scheme_normalization_of_isP1Tree f x U hU p p' hfp hxg hx hdim hdim'
    hp hp' hpa G hG hcurve hnodal (componentGenus_innerPoints_nonneg f x p' hdim' hp' hpure' G hG)
    𝒴 hsub hcov hsep htree V hV hxV

open scoped Classical in
include hU in
/-- **Temkin, Corollary B.2, in Temkin's form** (lane CRV4's
`CurvesField.Genus.stabdown_scheme_normalization_iff`) with `hg` replaced by the pure dimension
one of `C'`: `x` is an ordinary `n`-fold point in gluing form iff `Z` is a `ℙ¹`-tree with
`|∂Z| = n`. -/
theorem stabdown_scheme_normalization_iff [IsAlgClosed k] [CompactSpace C]
    [IsAffineHom (pullback.diagonal (terminal.from C))] [Finite (genericPoints C)] [IsReduced C]
    [CompactSpace C'] [IsReduced C'] [IsProper f] (p : C ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (p' : C' ⟶ Spec (.of k)) [LocallyOfFiniteType p'] (hfp : f ≫ p = p')
    (hxg : x ∉ genericPoints C) (hx : IsClosed {x}) (hdim : topologicalKrullDim C ≤ 1)
    (hdim' : topologicalKrullDim C' ≤ 1) (hp : IsProjectiveOver p) (hp' : IsProjectiveOver p')
    (hpure' : ∀ W ∈ irreducibleComponents C', topologicalKrullDim W = 1)
    (hpa : arithmeticGenus C' (structureCoeff p') = arithmeticGenus C (structureCoeff p))
    (G : Finset C') (hG : (G : Set C') = innerPoints f x) (hZ : _root_.IsConnected (f ⁻¹' {x}))
    (hcurve : ∀ z ∈ f ⁻¹' {x}, ∃ v ∈ G, z ∈ closure {v})
    (hnodal : ∀ y ∈ f ⁻¹' {x}, IsClosed {y} →
      DeJong.IsSmoothAt p' y ∨ Geometry.IsGeometricOrdinaryDoublePoint p' y)
    [Fintype (nodesIn p' (f ⁻¹' {x}))] (V : C.Opens) (hV : IsAffineOpen V) (hxV : x ∈ V)
    (n : ℕ) :
    letI := (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤)).toAlgebra
    letI := ((normalizationPointsMap (genericPoints C)).app V).hom.toAlgebra
    letI := (((normalizationPointsMap (genericPoints C)).app V).hom.comp
      (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤))).toAlgebra
    haveI : IsScalarTower k Γ(C, V) Γ(normalizationPoints (genericPoints C),
        normalizationPointsMap (genericPoints C) ⁻¹ᵁ V) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    (Nat.card (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid
        Γ(normalizationPoints (genericPoints C), normalizationPointsMap (genericPoints C) ⁻¹ᵁ V)
        (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl))) = n ∧
      rangeIn k (Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal)
          (Localization (Algebra.algebraMapSubmonoid
            Γ(normalizationPoints (genericPoints C),
              normalizationPointsMap (genericPoints C) ⁻¹ᵁ V)
            (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl)) =
        gluing k (Localization (Algebra.algebraMapSubmonoid
            Γ(normalizationPoints (genericPoints C),
              normalizationPointsMap (genericPoints C) ⁻¹ᵁ V)
            (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl))) ↔
      ((nodalGraph p' hdim' (f ⁻¹' {x})).IsP1Tree G ∧
        ((nodalGraph p' hdim' (f ⁻¹' {x})).boundary G).card = n) :=
  CurvesField.Genus.stabdown_scheme_normalization_iff f x U hU p p' hfp hxg hx hdim hdim' hp hp'
    hpa G hG hZ hcurve hnodal (componentGenus_innerPoints_nonneg f x p' hdim' hp' hpure' G hG) V hV
    hxV n

end StableDown

section NoClosedExc

open NoClosedExc ExcSpecialize

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [Finite (PrimeSpectrum V)]
  {X C : Scheme.{u}} (β : X ⟶ C) (g : C ⟶ Spec (CommRingCat.of V)) (D' : X.IdealSheafData)

/-- **A numerically stable closed fibre has no combinatorially exceptional component**
(`NoClosedExc.not_isCombExceptional_of_numericallyStableFibre` without `NodalComponentGenus`). -/
theorem not_isCombExceptional_of_numericallyStableFibre
    [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsProper (β ≫ g)] (hp : IsProjectiveOver (β ≫ g))
    (hpair : DeJong.IsSemistablePair (β ≫ g) D')
    [IsAlgClosed (IsLocalRing.closedPoint V).asIdeal.ResidueField]
    (hE₀ : NumericallyStableFibre β g D' (residuePt (IsLocalRing.closedPoint V)))
    (v : pullback (C := Scheme.{u}) (β ≫ g) (residuePt (IsLocalRing.closedPoint V))) :
    ¬ IsCombExceptional β g D' (residuePt (IsLocalRing.closedPoint V)) v :=
  NoClosedExc.not_isCombExceptional_of_numericallyStableFibre β g D'
    ComponentGenus.nodalComponentGenus hp hpair hE₀ v

/-- **Temkin's Lemma 4.4.4, numerical form, over the residue points**
(`NoClosedExc.numericallyStableFibre_residuePt_of_closedPoint` without `NodalComponentGenus`). -/
theorem numericallyStableFibre_residuePt_of_closedPoint (hloc : ClosureComponentLocal.{u})
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsProper (β ≫ g)] [IsProper g] (hp : IsProjectiveOver (β ≫ g))
    (hpair : DeJong.IsSemistablePair (β ≫ g) D')
    [IsAlgClosed (IsLocalRing.closedPoint V).asIdeal.ResidueField]
    (hE₀ : NumericallyStableFibre β g D' (residuePt (IsLocalRing.closedPoint V)))
    (t : PrimeSpectrum V) [IsAlgClosed t.asIdeal.ResidueField] :
    NumericallyStableFibre β g D' (residuePt t) :=
  NoClosedExc.numericallyStableFibre_residuePt_of_closedPoint β g D' hloc
    ComponentGenus.nodalComponentGenus hsep hp hpair hE₀ t

/-- **Temkin's Lemma 4.4.4, numerical form, for all geometric fibres**
(`NoClosedExc.numericallyStableFibre_of_closedPoint` without `NodalComponentGenus` and
`NumericalDescent`). -/
theorem numericallyStableFibre_of_closedPoint (hloc : ClosureComponentLocal.{u})
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    (halg : ∀ t : PrimeSpectrum V, IsAlgClosed t.asIdeal.ResidueField)
    [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsProper (β ≫ g)] [IsProper g] (hp : IsProjectiveOver (β ≫ g))
    (hpair : DeJong.IsSemistablePair (β ≫ g) D')
    (hE₀ : NumericallyStableFibre β g D' (residuePt (IsLocalRing.closedPoint V)))
    (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ Spec (CommRingCat.of V)) :
    NumericallyStableFibre β g D' a :=
  NoClosedExc.numericallyStableFibre_of_closedPoint β g D' hloc
    ComponentGenus.nodalComponentGenus NumericalDescent.numericalDescent hsep halg hp hpair hE₀ K a

/-- **Temkin's Lemma 4.4.4, numerical form, as an equivalence**
(`NoClosedExc.numericallyStable_iff_closedPoint` without `NodalComponentGenus` and
`NumericalDescent`): all geometric fibres are numerically stable iff the closed fibre is. -/
theorem numericallyStable_iff_closedPoint (hloc : ClosureComponentLocal.{u})
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    (halg : ∀ t : PrimeSpectrum V, IsAlgClosed t.asIdeal.ResidueField)
    [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsProper (β ≫ g)] [IsProper g] (hp : IsProjectiveOver (β ≫ g))
    (hpair : DeJong.IsSemistablePair (β ≫ g) D') :
    (∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ Spec (CommRingCat.of V)),
        NumericallyStableFibre β g D' a) ↔
      NumericallyStableFibre β g D' (residuePt (IsLocalRing.closedPoint V)) :=
  NoClosedExc.numericallyStable_iff_closedPoint β g D' hloc ComponentGenus.nodalComponentGenus
    NumericalDescent.numericalDescent hsep halg hp hpair

/-- **Temkin's Lemma 4.4.4 for Temkin's stability**
(`NoClosedExc.isStableModification_of_numericallyStableFibre_closedPoint` without
`NodalComponentGenus` and `NumericalDescent`). -/
theorem isStableModification_of_numericallyStableFibre_closedPoint
    (hloc : ClosureComponentLocal.{u})
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    (halg : ∀ t : PrimeSpectrum V, IsAlgClosed t.asIdeal.ResidueField)
    [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsProper (β ≫ g)] [IsProper g] (hp : IsProjectiveOver (β ≫ g))
    (D : C.IdealSheafData) (hη : Curves.IsEtaModification β g)
    (hmarks : D' = Curves.genericMarksClosure β g D (genericPoint (Spec (CommRingCat.of V))))
    (hpair : DeJong.IsSemistablePair (β ≫ g) D')
    (hE₀ : NumericallyStableFibre β g D' (residuePt (IsLocalRing.closedPoint V))) :
    Curves.IsStableModification β g D D' :=
  NoClosedExc.isStableModification_of_numericallyStableFibre_closedPoint β g D' hloc
    ComponentGenus.nodalComponentGenus NumericalDescent.numericalDescent hsep halg hp D hη hmarks
    hpair hE₀

/-- **Lemma 4.4.4, combinatorial form, for all geometric fibres**
(`NoClosedExc.numericallyStableFibre_of_forall_not_isCombExceptional_of_descent` without
`NumericalDescent`). -/
theorem numericallyStableFibre_of_forall_not_isCombExceptional (hloc : ClosureComponentLocal.{u})
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    (halg : ∀ t : PrimeSpectrum V, IsAlgClosed t.asIdeal.ResidueField)
    [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsProper (β ≫ g)] [IsProper g] (hp : IsProjectiveOver (β ≫ g))
    (hpair : DeJong.IsSemistablePair (β ≫ g) D')
    (hE₀ : ∀ v, ¬ IsCombExceptional β g D' (residuePt (IsLocalRing.closedPoint V)) v)
    (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ Spec (CommRingCat.of V)) :
    NumericallyStableFibre β g D' a :=
  NoClosedExc.numericallyStableFibre_of_forall_not_isCombExceptional_of_descent β g D' hloc
    NumericalDescent.numericalDescent hsep halg hp hpair hE₀ K a

/-- **Temkin's Lemma 4.4.4 for Temkin's stability, combinatorial form**
(`NoClosedExc.isStableModification_of_forall_not_isCombExceptional` without
`NumericalDescent`). -/
theorem isStableModification_of_forall_not_isCombExceptional (hloc : ClosureComponentLocal.{u})
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    (halg : ∀ t : PrimeSpectrum V, IsAlgClosed t.asIdeal.ResidueField)
    [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsProper (β ≫ g)] [IsProper g] (hp : IsProjectiveOver (β ≫ g))
    (D : C.IdealSheafData) (hη : Curves.IsEtaModification β g)
    (hmarks : D' = Curves.genericMarksClosure β g D (genericPoint (Spec (CommRingCat.of V))))
    (hpair : DeJong.IsSemistablePair (β ≫ g) D')
    (hE₀ : ∀ v, ¬ IsCombExceptional β g D' (residuePt (IsLocalRing.closedPoint V)) v) :
    Curves.IsStableModification β g D D' :=
  NoClosedExc.isStableModification_of_forall_not_isCombExceptional β g D' hloc
    NumericalDescent.numericalDescent hsep halg hp D hη hmarks hpair hE₀

end NoClosedExc

section Stable

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [Finite (PrimeSpectrum V)]
  {C : Scheme.{u}} (φ : C ⟶ Spec (CommRingCat.of V)) (D : C.IdealSheafData)
  [IsIntegral C] [IsProper φ] [Flat φ] [HenselianLocalRing V]

/-- **Temkin's Proposition 4.4.6** (lane T44B's
`BlowDown.exists_isStableModification_of_isSemistableStage`, blueprint
`thm:sm-bdg-blowdown-stable`) without `NumericalDescent`: every semi-stable stage dominates a
semi-stable stage which is a stable modification with numerically stable geometric fibres. The
remaining inputs are `ClosureComponentLocal` and Temkin's contracting morphisms
(`ContractingMorphismExists`). -/
theorem exists_isStableModification_of_isSemistableStage
    (hloc : ExcSpecialize.ClosureComponentLocal.{u})
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    (halg : ∀ t : PrimeSpectrum V, IsAlgClosed t.asIdeal.ResidueField)
    (hdimC : ValuationRing.fiberTrdeg φ (genericPoint C) ≤ 1)
    (hcontract : ContractingMorphismExists φ D)
    (Y : Scheme.{u}) (β : Y ⟶ C) (hY : IsSemistableStage φ D β) :
    ∃ (Y'' : Scheme.{u}) (β'' : Y'' ⟶ C) (b : Y ⟶ Y''), b ≫ β'' = β ∧
      IsSemistableStage φ D β'' ∧
      Curves.IsStableModification β'' φ D
        (Curves.genericMarksClosure β'' φ D (genericPoint (Spec (CommRingCat.of V)))) ∧
      ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ Spec (CommRingCat.of V)),
        NoClosedExc.NumericallyStableFibre β'' φ
          (Curves.genericMarksClosure β'' φ D (genericPoint (Spec (CommRingCat.of V)))) a :=
  BlowDown.exists_isStableModification_of_isSemistableStage φ D hloc
    NumericalDescent.numericalDescent hsep halg hdimC hcontract Y β hY

/-- **Temkin's Proposition 4.4.6 for `C` projective over `V`** (lane T44F's
`ContractingExists.exists_isStableModification_of_isSemistableStage`, blueprint
`thm:sm-bdc-blowdown-stable`) without `NumericalDescent` and `NodalComponentGenus`: the
contracting morphisms are those of lane T44F (`ContractingExists.contractingMorphismExists`), and
the only remaining named input is `ClosureComponentLocal`. -/
theorem exists_isStableModification_of_isSemistableStage_of_isProjectiveOver
    (hloc : ExcSpecialize.ClosureComponentLocal.{u}) (hC : IsProjectiveOver φ)
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    (halg : ∀ t : PrimeSpectrum V, IsAlgClosed t.asIdeal.ResidueField)
    (hdimC : ValuationRing.fiberTrdeg φ (genericPoint C) ≤ 1)
    (Y : Scheme.{u}) (β : Y ⟶ C) (hY : IsSemistableStage φ D β) :
    ∃ (Y'' : Scheme.{u}) (β'' : Y'' ⟶ C) (b : Y ⟶ Y''), b ≫ β'' = β ∧
      IsSemistableStage φ D β'' ∧
      Curves.IsStableModification β'' φ D
        (Curves.genericMarksClosure β'' φ D (genericPoint (Spec (CommRingCat.of V)))) ∧
      ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ Spec (CommRingCat.of V)),
        NoClosedExc.NumericallyStableFibre β'' φ
          (Curves.genericMarksClosure β'' φ D (genericPoint (Spec (CommRingCat.of V)))) a :=
  ContractingExists.exists_isStableModification_of_isSemistableStage φ D hloc
    NumericalDescent.numericalDescent ComponentGenus.nodalComponentGenus hC hsep halg hdimC Y β hY

end Stable

end DeJongAlterations.StableModification.BlowDown.Unconditional
