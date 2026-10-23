/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.ExcSpecialize

/-!
# Temkin's Lemma 4.4.4: no exceptional components in the closed fibre

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), Lemma 4.4.4
(`emptylem`, T:3158–3176): a semi-stable modification `f : (C', D') → (C, D)` of a multipointed
curve over a valuation ring is stable iff `E₀ = ∅`, where `E₀` is the set of exceptional
components of the fibres of `C'` lying over the closed point. We prove the direction used in the
blow-down (PLAN-T5 C5; Temkin, Prop. 4.4.6 iterated until `E₀ = ∅`), for `C'` projective over
`V`, in the numerical form of `PLAN-T5.md` §1.3 (lane T5G's `Global.NumericallyStableFibre`,
reproduced here as `NumericallyStableFibre`): exceptional components are recognized by their
arithmetic genus `p_a = 0` and their number of special points, without identifying them with
`ℙ¹`.

## Main results

* `numericallyStableFibre_of_forall_not_isCombExceptional` (combinatorial form): if the closed
  fibre has no combinatorially exceptional component (`ExcSpecialize.IsCombExceptional`), then the
  fibre over every point of `Spec V` with algebraically closed residue field is numerically stable
  (the contrapositive of `ExcSpecialize.exists_isCombExceptional_closedFibre`).
* `not_isCombExceptional_of_numericallyStableFibre`: a numerically stable closed fibre has no
  combinatorially exceptional component, given `NodalComponentGenus` (a component of a nodal curve
  meeting the other components only in double points has `p_a = g`, not formalized). Its inputs
  `isSmoothAt_of_mem_genericPoints` (generic points of a nodal curve over `k = k̄` are smooth)
  and `not_mem_support_of_mem_genericPoints` (étale marks miss the generic points of the fibres)
  are proved.
* `numericallyStableFibre_residuePt_of_closedPoint` (**Lemma 4.4.4**, numerical form, over the
  residue points): numerical stability of the closed fibre propagates to every fibre over a point
  with algebraically closed residue field.
* `numericallyStableFibre_of_closedPoint`, `numericallyStable_iff_closedPoint`: all geometric
  fibres, given the base-change statement `NumericalDescent` (not formalized).
* `isStableModification_of_numericallyStableFibre_closedPoint`: **Lemma 4.4.4** for Temkin's
  (exceptional-`ℙ¹`) stability `Curves.IsStableModification`, using
  `not_numericallyStableFibre_of_isExceptionalComponent` (an exceptional component is
  numerically exceptional, `χ(ℙ¹_K, 𝒪) = 1`).
* `numericallyStableFibre_of_forall_not_isCombExceptional_of_descent`,
  `isStableModification_of_forall_not_isCombExceptional`: the same from the combinatorial
  `E₀ = ∅` (the termination condition of the blow-down in the form of the stability criterion),
  without `NodalComponentGenus`.
* `isAlgClosed_residueField_of_isAlgClosed`: in Temkin's setting (`Frac V` algebraically closed)
  all residue fields of `V` are algebraically closed (the hypothesis `halg`).
* `isRelativelyProjective_of_comp`, `isRelativelyProjective_toNormalization`: `B → Nor_B(Y)` is
  projective relative to `Nor_B(Y) → Spec k` (the projectivity part of
  `lem:sm-bd-normalization-birational`).

The results take as explicit hypotheses the named propositions `ExcSpecialize.ClosureComponentLocal`
(the étale-local part of `lem:sm-bd-closure-component`), `NodalComponentGenus` and
`NumericalDescent`. (The nonnegativity of the genera of the normalized components of the closed
fibre, a hypothesis of lane T44A2's `stability_criterion_fibre`, is proved:
`ExcSpecialize.componentGenus_nonneg`.) Normality of `C` is not used: the
contraction of the closure of a contracted component is the closure of an algebraic point
(`ExcSpecialize.eq_of_mem_closure_of_isAlgebraicAt`), so Temkin's reduction to a normal `C`
(T:3159–3161, ERRATA T13) is not needed in this form.

Blueprint: `lem:sm-stable-iff-no-closed-exc`, chapter `sm-blow-down-exceptional.tex`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

namespace DeJongAlterations.StableModification.BlowDown.NoClosedExc

universe u

open Cohomology CurvesField CurvesField.Genus ClosureComponent ValCurves ExcSpecialize
open Curves (pullbackCompMap IsExceptionalComponent IsStableModification)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

section Numerical

variable {S X C : Scheme.{u}}

/-- **Numerical stability of the fibre** `X_a` of `β ≫ g : X → C → S` with marks `D'` over a
field point `a : Spec K → S` (`PLAN-T5.md` §1.3; this is the body of lane T5G's
`Global.NumericallyStableFibre β g D' a`, not yet integrated, so that the two agree by `Iff.rfl`):
every irreducible component `Z` of `X_a` contracted by `β_a` whose reduced induced subscheme
`Z_red` has arithmetic genus `0` contains at least three special points (`specialPoints`). -/
def NumericallyStableFibre (β : X ⟶ C) (g : C ⟶ S) (D' : X.IdealSheafData) {K : Type u}
    [Field K] (a : Spec (.of K) ⟶ S) : Prop :=
  ∀ (Z : Set (pullback (C := Scheme.{u}) (β ≫ g) a))
    (hZ : Z ∈ irreducibleComponents (pullback (C := Scheme.{u}) (β ≫ g) a)),
    (pullbackCompMap β g a '' Z).Subsingleton →
    ∀ [CompactSpace (Scheme.IdealSheafData.vanishingIdeal
        ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩).subscheme]
      [IsSeparated (terminal.from (Scheme.IdealSheafData.vanishingIdeal
        ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩).subscheme)],
      arithmeticGenus (Scheme.IdealSheafData.vanishingIdeal
          ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩).subscheme
          (structureCoeff ((Scheme.IdealSheafData.vanishingIdeal
            ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩).subschemeι ≫
              pullback.snd (β ≫ g) a)) = 0 →
        3 ≤ (Z ∩ specialPoints (β ≫ g) D' a).encard

/-- **Exceptional components are numerically exceptional** (`PLAN-T5.md` §1.3, G0): an
exceptional component `Z` (`Curves.IsExceptionalComponent`) is the image of a closed immersion of
`ℙ¹_K`, so its reduced induced subscheme is `ℙ¹_K`, of arithmetic genus `1 − χ(ℙ¹_K, 𝒪) = 0`
(`ExcSpecialize.eulerChar_projectiveSpace_one`), and it has at most two special points. -/
theorem not_numericallyStableFibre_of_isExceptionalComponent (β : X ⟶ C) (g : C ⟶ S)
    (D' : X.IdealSheafData) {K : Type u} [Field K] (a : Spec (.of K) ⟶ S)
    {Z : Set (pullback (C := Scheme.{u}) (β ≫ g) a)} (hE : IsExceptionalComponent β g D' a Z) :
    ¬ NumericallyStableFibre β g D' a := by
  intro h
  obtain ⟨i, hi, hiK, hrange⟩ := hE.exists_projectiveLine
  have hZ := hE.mem_irreducibleComponents
  have hZc := isClosed_of_mem_irreducibleComponents Z hZ
  have : IsIntegral (projectiveSpace K 1) :=
    Geometry.ProjectiveCurveFibration.projectiveSpace_isIntegral K 1
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨Z, hZc⟩ : Closeds _)
  have : IsReduced I.subscheme :=
    Geometry.ReducedClosedSubscheme.isReduced_vanishingIdeal_subscheme _
  have hrange' : Set.range i = Set.range I.subschemeι := by
    have hs : (I.support : Set _) = Z := by
      rw [Geometry.ReducedClosedSubscheme.support_vanishingIdeal]
      rfl
    rw [Scheme.IdealSheafData.range_subschemeι, hrange, hs]
  have hker : I.subschemeι.ker = i.ker := ker_eq_of_range_eq _ _ hrange'.symm
  have hiso := IsClosedImmersion.isIso_lift I.subschemeι i hker
  let e := asIso (IsClosedImmersion.lift I.subschemeι i hker.le)
  have he : e.hom ≫ I.subschemeι = i := IsClosedImmersion.lift_fac _ _ _
  have : CompactSpace I.subscheme := e.hom.homeomorph.compactSpace
  have : IsSeparated (terminal.from I.subscheme) := by
    rw [← terminal.comp_from e.inv, ← terminal.comp_from (projectiveSpaceStructure K 1)]
    infer_instance
  have hχ : eulerChar I.subscheme (structureCoeff (I.subschemeι ≫ pullback.snd (β ≫ g) a)) = 1 := by
    rw [← eulerChar_projectiveSpace_one K]
    refine (BlowDown.eulerChar_eq_of_iso _ _ e ?_).symm
    rw [← Category.assoc, he, hiK]
  have hpa : arithmeticGenus I.subscheme
      (structureCoeff (I.subschemeι ≫ pullback.snd (β ≫ g) a)) = 0 := by
    rw [arithmeticGenus, hχ]
    norm_num
  have h3 := h Z hZ hE.contracted hpa
  have h2 := hE.encard_special_le_two
  have : (3 : ℕ∞) ≤ 2 := h3.trans h2
  exact absurd this (by decide)

end Numerical

section Fibres

variable {Y : Scheme.{u}} {k : Type u} [Field k] [IsAlgClosed k] (q : Y ⟶ Spec (.of k))
  [LocallyOfFinitePresentation q] [CompactSpace Y] [IsAffineHom (pullback.diagonal (terminal.from Y))]
  [IsReduced Y] [Finite (genericPoints Y)]

/-- **The generic points of a nodal curve are smooth points.** Let `Y` be a reduced curve,
projective over `k = k̄`, of pure dimension one, whose closed points are smooth points or ordinary
double points. If a generic point `v` were not smooth, the closed non-smooth locus would contain
the component `closure {v}`, all of whose closed points would be double points; these are finitely
many (`CurvesField.Genus.finite_nodesIn`), and by the Jacobson property the closed points are
dense in `closure {v}`, so `v` would be closed. -/
theorem isSmoothAt_of_mem_genericPoints (hdim : topologicalKrullDim Y ≤ 1)
    (hp : IsProjectiveOver q)
    (hpure : ∀ W ∈ irreducibleComponents Y, topologicalKrullDim W = 1)
    (hnodal : ∀ y : Y, IsClosed ({y} : Set Y) →
      DeJong.IsSmoothAt q y ∨ Geometry.IsGeometricOrdinaryDoublePoint q y)
    {v : Y} (hv : v ∈ genericPoints Y) : DeJong.IsSmoothAt q v := by
  by_contra hns
  have hN : IsClosed ((q.smoothLocus : Set Y)ᶜ) := q.smoothLocus.isOpen.isClosed_compl
  have hsub : closure {v} ⊆ (q.smoothLocus : Set Y)ᶜ :=
    closure_minimal (Set.singleton_subset_iff.mpr hns) hN
  have hfin : (closure {v} ∩ closedPoints Y).Finite := by
    refine (finite_nodesIn q hdim hp (closure {v})).subset fun y hy => ?_
    obtain ⟨hyv, hyc⟩ := hy
    exact ⟨hyv, hyc, BlowDown.not_mem_genericPoints_of_isClosed hpure hyc,
      (hnodal y hyc).resolve_left fun h => hsub hyv h⟩
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace q
  have hcl := JacobsonSpace.closure_inter_closedPoints (X := Y) (Z := closure {v}) isClosed_closure
  have hFc : IsClosed (closure {v} ∩ closedPoints Y) := by
    rw [← Set.biUnion_of_singleton (closure {v} ∩ closedPoints Y)]
    exact hfin.isClosed_biUnion fun y hy => hy.2
  rw [hFc.closure_eq] at hcl
  have hvF : v ∈ closure {v} ∩ closedPoints Y := by
    rw [hcl]
    exact subset_closure rfl
  exact BlowDown.not_mem_genericPoints_of_isClosed hpure hvF.2 hv

end Fibres

section Marks

variable {V : Type u} [CommRing V] {X : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of V))
  (D' : X.IdealSheafData)

/-- **Étale marks are algebraic over the base**: a point of the support of `D'` with
`D' → Spec V` étale has residue field algebraic over the base (étale morphisms are locally
quasi-finite). -/
theorem isAlgebraicAt_of_mem_support [Etale (D'.subschemeι ≫ q)] {x : X}
    (hx : x ∈ (D'.support : Set X)) : IsAlgebraicAt q x := by
  rw [← Scheme.IdealSheafData.range_subschemeι] at hx
  obtain ⟨d, rfl⟩ := hx
  have : LocallyQuasiFinite (D'.subschemeι ≫ q) := Curves.locallyQuasiFinite_of_etale _
  exact ExcSpecialize.isAlgebraicAt_of_comp
    (isAlgebraicAt_of_quasiFiniteAt ((D'.subschemeι ≫ q).quasiFiniteAt d))

/-- **Étale marks miss the generic points of the fibres of pure dimension one.** -/
theorem not_mem_support_of_mem_genericPoints [Etale (D'.subschemeι ≫ q)] [IsSeparated q]
    {t : PrimeSpectrum V}
    (hpure : ∀ W ∈ irreducibleComponents (pullback (C := Scheme.{u}) q (residuePt t)),
      topologicalKrullDim W = 1)
    {v : pullback (C := Scheme.{u}) q (residuePt t)} (hv : v ∈ genericPoints _) :
    pullback.fst q (residuePt t) v ∉ (D'.support : Set X) := fun hD =>
  not_isAlgebraicAt_of_mem_genericPoints q hpure hv (isAlgebraicAt_of_mem_support q D' hD)

end Marks

section RelativelyProjective

variable {k : Type u} [CommRing k] {B N Y : Scheme.{u}} (pY : Y ⟶ Spec (.of k))

/-- **Relative projectivity passes to the first factor of a separated factorization**
(blueprint `lem:sm-bd-normalization-birational`, the projectivity part): if `τ ≫ ν` is projective
relative to `pY` and `ν` is separated, then `τ` is projective relative to `ν ≫ pY`. The closed
immersion `B ↪ ℙⁿ_Y` factors through `ℙⁿ_N = N ×_Y ℙⁿ_Y`, whose projection to `ℙⁿ_Y` is
separated. -/
theorem isRelativelyProjective_of_comp (τ : B ⟶ N) (ν : N ⟶ Y) [IsSeparated ν]
    (h : DeJong.IsRelativelyProjective pY (τ ≫ ν)) :
    DeJong.IsRelativelyProjective (ν ≫ pY) τ := by
  obtain ⟨n, i, hi, hcomp⟩ := h
  let j' : B ⟶ pullback ν (pullback.fst pY (projectiveSpaceStructure k n)) :=
    pullback.lift τ i hcomp.symm
  have hj' : j' ≫ pullback.snd _ _ = i := pullback.lift_snd _ _ _
  have : IsSeparated (pullback.snd ν (pullback.fst pY (projectiveSpaceStructure k n))) :=
    MorphismProperty.pullback_snd (P := @IsSeparated) _ _ ‹_›
  have : IsClosedImmersion
      (j' ≫ pullback.snd ν (pullback.fst pY (projectiveSpaceStructure k n))) := by
    rw [hj']
    exact hi
  have : IsClosedImmersion j' := IsClosedImmersion.of_comp j' (pullback.snd _ _)
  refine ⟨n, j' ≫ (pullbackRightPullbackFstIso pY (projectiveSpaceStructure k n) ν).hom,
    inferInstance, ?_⟩
  rw [Category.assoc, pullbackRightPullbackFstIso_hom_fst, pullback.lift_fst]

/-- **`B → Nor_B(Y)` is projective relative to `Nor_B(Y) → Spec k`** (blueprint
`lem:sm-bd-normalization-birational`, the projectivity part) when `π : B → Y` is projective
relative to `pY`: `Nor_B(Y) → Y` is integral, hence separated. -/
theorem isRelativelyProjective_toNormalization (π : B ⟶ Y) [QuasiCompact π] [QuasiSeparated π]
    (h : DeJong.IsRelativelyProjective pY π) :
    DeJong.IsRelativelyProjective (π.fromNormalization ≫ pY) π.toNormalization := by
  apply isRelativelyProjective_of_comp
  rw [Scheme.Hom.toNormalization_fromNormalization]
  exact h

end RelativelyProjective

/-- **The genus of a component of a nodal curve meeting the others only in double points**
(*not formalized*; a hypothesis of the results below, in this precise form). Let `Y` be a reduced
curve, projective over an algebraically closed field `k`, whose closed points are smooth points or
ordinary double points, and `v` a generic point of `Y` such that every ordinary double point of
`Y` on the component `closure {v}` also lies on another component. Then the reduced component
`closure {v}` (`ClosureComponent.closureScheme`) has arithmetic genus `g(v)`
(`CurvesField.Genus.componentGenus`, the genus of the normalization): it is normal, since at a
double point `k[[u, v]]/(uv)` with one branch on `closure {v}` its completed local ring is
`k[[u]]`, and at a smooth point `Y` is integral. -/
def NodalComponentGenus : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (Y : Scheme.{u}) (q : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType q] [CompactSpace Y] [IsAffineHom (pullback.diagonal (terminal.from Y))]
    [IsReduced Y], topologicalKrullDim Y ≤ 1 → IsProjectiveOver q →
    (∀ y : Y, IsClosed ({y} : Set Y) →
      DeJong.IsSmoothAt q y ∨ Geometry.IsGeometricOrdinaryDoublePoint q y) →
    ∀ v ∈ genericPoints Y,
      (∀ y ∈ closure {v}, IsClosed ({y} : Set Y) → Geometry.IsGeometricOrdinaryDoublePoint q y →
        ∃ w ∈ genericPoints Y, w ≠ v ∧ y ∈ closure {w}) →
      arithmeticGenus (closureScheme v) (structureCoeff (closureι v ≫ q)) =
        componentGenus (structureCoeff q) v

/-- **Numerical stability descends from residue fibres to geometric fibres** (*not formalized*;
a hypothesis of `numericallyStableFibre_of_closedPoint`). For `β ≫ g : X → C → Spec V` proper
and a point `t` with algebraically closed residue field, numerical stability of the fibre over
`Spec κ(t)` implies it for every geometric point `a : Spec K → Spec V` over `t`: `X_a` is the base
change of `X_t` along the extension `K/κ(t)` of algebraically closed fields, which preserves
irreducible components, reduced induced structures, arithmetic genera (flat base change of
cohomology), smoothness, the marks and the contracted components, and the special points of a
component (finitely many closed points over the closed points of `X_t`, which are `κ(t)`-rational,
and the generic point). -/
def NumericalDescent : Prop :=
  ∀ (V : Type u) [CommRing V] (X C : Scheme.{u}) (β : X ⟶ C) (g : C ⟶ Spec (.of V))
    (D' : X.IdealSheafData) [IsProper (β ≫ g)] (t : PrimeSpectrum V)
    [IsAlgClosed t.asIdeal.ResidueField], NumericallyStableFibre β g D' (residuePt t) →
    ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ Spec (.of V)),
      (∀ x, a x = t) → NumericallyStableFibre β g D' a

section Residue

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]

/-- **In Temkin's setting all residue fields are algebraically closed**: if the fraction field
`K` of the valuation ring `V` is algebraically closed, so is `κ(t)` for every point `t` of
`Spec V` (`t = 0`: `κ(0) ≅ K`; `t ≠ 0`: `ClosureComponent.isAlgClosed_residueField_of_ne_bot`).
Together with `Cohomology.Connected.isSepClosed_fractionRing_quotient` this supplies the
hypotheses `hsep` and `halg` of the results below. -/
theorem isAlgClosed_residueField_of_isAlgClosed (K : Type u) [Field K] [Algebra V K]
    [IsFractionRing V K] [IsAlgClosed K] (t : PrimeSpectrum V) :
    IsAlgClosed t.asIdeal.ResidueField := by
  have hsep : IsSepClosed (FractionRing (V ⧸ (⊥ : Ideal V))) :=
    Cohomology.Connected.isSepClosed_fractionRing_quotient K ⊥
  by_cases ht : t.asIdeal = ⊥
  · let e1 : t.asIdeal.ResidueField ≃+* FractionRing (V ⧸ t.asIdeal) :=
      (FractionRing.algEquiv (V ⧸ t.asIdeal) t.asIdeal.ResidueField).symm.toRingEquiv
    let e2 : FractionRing (V ⧸ t.asIdeal) ≃+* K :=
      IsFractionRing.ringEquivOfRingEquiv (A := V ⧸ t.asIdeal) (B := V)
        (K := FractionRing (V ⧸ t.asIdeal)) (L := K)
        ((Ideal.quotEquivOfEq ht).trans (RingEquiv.quotientBot V))
    exact IsAlgClosed.of_ringEquiv K t.asIdeal.ResidueField (e2.symm.trans e1.symm)
  · exact isAlgClosed_residueField_of_ne_bot hsep t ht

end Residue

section Main

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [Finite (PrimeSpectrum V)]
  {X C : Scheme.{u}} (β : X ⟶ C) (g : C ⟶ Spec (CommRingCat.of V)) (D' : X.IdealSheafData)

/-- **Lemma 4.4.4, combinatorial form** (Temkin, T:3158–3176; blueprint
`lem:sm-stable-iff-no-closed-exc`): in the situation of
`ExcSpecialize.exists_isCombExceptional_closedFibre`, if the closed fibre `X_{s₀}` has no
combinatorially exceptional component (`E₀ = ∅`), then the fibre over every point `t` of
`Spec V` with algebraically closed residue field is numerically stable. -/
theorem numericallyStableFibre_of_forall_not_isCombExceptional
    (hloc : ClosureComponentLocal.{u})
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsProper (β ≫ g)] [IsProper g] (hp : IsProjectiveOver (β ≫ g))
    (hpair : DeJong.IsSemistablePair (β ≫ g) D')
    [IsAlgClosed (IsLocalRing.closedPoint V).asIdeal.ResidueField]
    (hE₀ : ∀ v, ¬ IsCombExceptional β g D' (residuePt (IsLocalRing.closedPoint V)) v)
    (t : PrimeSpectrum V) [IsAlgClosed t.asIdeal.ResidueField] :
    NumericallyStableFibre β g D' (residuePt t) := by
  intro Z hZ hcontr _ _ hpa
  by_contra h3
  have hspec : (Z ∩ specialPoints (β ≫ g) D' (residuePt t)).encard ≤ 2 := by
    have h := not_le.mp h3
    exact Order.le_of_lt_succ h
  obtain ⟨ζ, hζ⟩ := QuasiSober.sober hZ.prop
    (isClosed_of_mem_irreducibleComponents Z hZ)
  have hZζ : closure {ζ} = Z := hζ.def
  subst hZζ
  have hζg : ζ ∈ genericPoints (pullback (C := Scheme.{u}) (β ≫ g) (residuePt t)) := hZ
  have hχ : eulerChar (closureScheme ζ)
      (structureCoeff (closureι ζ ≫ pullback.snd (β ≫ g) (residuePt t))) = 1 := by
    have h : arithmeticGenus (closureScheme ζ)
        (structureCoeff (closureι ζ ≫ pullback.snd (β ≫ g) (residuePt t))) = 0 := hpa
    rw [arithmeticGenus] at h
    linarith
  obtain ⟨v, hv⟩ := exists_isCombExceptional_closedFibre β g D' hloc hsep hp hpair ζ hζg hcontr
    hχ hspec
  exact hE₀ v hv

/-- **Lemma 4.4.4, combinatorial form, for all geometric fibres**: with all residue fields of `V`
algebraically closed and `NumericalDescent`, if the closed fibre has no combinatorially
exceptional component, every geometric fibre is numerically stable. This form does not use
`NodalComponentGenus`. -/
theorem numericallyStableFibre_of_forall_not_isCombExceptional_of_descent
    (hloc : ClosureComponentLocal.{u}) (hdesc : NumericalDescent.{u})
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    (halg : ∀ t : PrimeSpectrum V, IsAlgClosed t.asIdeal.ResidueField)
    [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsProper (β ≫ g)] [IsProper g] (hp : IsProjectiveOver (β ≫ g))
    (hpair : DeJong.IsSemistablePair (β ≫ g) D')
    (hE₀ : ∀ v, ¬ IsCombExceptional β g D' (residuePt (IsLocalRing.closedPoint V)) v)
    (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ Spec (CommRingCat.of V)) :
    NumericallyStableFibre β g D' a := by
  obtain ⟨x⟩ : Nonempty (Spec (.of K)) := inferInstance
  have := halg (IsLocalRing.closedPoint V)
  have := halg (a x)
  have ht := numericallyStableFibre_of_forall_not_isCombExceptional β g D' hloc hsep hp hpair
    hE₀ (a x)
  exact hdesc V X C β g D' (a x) ht K a fun y => by rw [Subsingleton.elim y x]

/-- **Temkin's Lemma 4.4.4 for Temkin's stability, combinatorial form**: a semi-stable
η-modification `β : (X, D') → (C, D)` over `V`, projective over `V`, whose closed fibre has no
combinatorially exceptional component (`E₀ = ∅` in the form of the stability criterion, the
termination condition of the blow-down), is a stable modification. This form does not use
`NodalComponentGenus`. -/
theorem isStableModification_of_forall_not_isCombExceptional
    (hloc : ClosureComponentLocal.{u}) (hdesc : NumericalDescent.{u})
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    (halg : ∀ t : PrimeSpectrum V, IsAlgClosed t.asIdeal.ResidueField)
    [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsProper (β ≫ g)] [IsProper g] (hp : IsProjectiveOver (β ≫ g))
    (D : C.IdealSheafData) (hη : Curves.IsEtaModification β g)
    (hmarks : D' = Curves.genericMarksClosure β g D (genericPoint (Spec (CommRingCat.of V))))
    (hpair : DeJong.IsSemistablePair (β ≫ g) D')
    (hE₀ : ∀ v, ¬ IsCombExceptional β g D' (residuePt (IsLocalRing.closedPoint V)) v) :
    IsStableModification β g D D' where
  toIsEtaModification := hη
  marks_eq := hmarks
  isSemistablePair := hpair
  not_isExceptionalComponent K _ _ a _Z hE :=
    not_numericallyStableFibre_of_isExceptionalComponent β g D' a hE
      (numericallyStableFibre_of_forall_not_isCombExceptional_of_descent β g D' hloc hdesc hsep
        halg hp hpair hE₀ K a)

/-- **A numerically stable closed fibre has no combinatorially exceptional component**, given
`NodalComponentGenus`: a combinatorially exceptional component `closure {v}` is contracted, has
`p_a = g(v) = 0`, and its special points are closed (its generic point is smooth,
`isSmoothAt_of_mem_genericPoints`, and not a mark, `not_mem_support_of_mem_genericPoints`), at
most two of them. -/
theorem not_isCombExceptional_of_numericallyStableFibre (hbridge : NodalComponentGenus.{u})
    [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsProper (β ≫ g)] (hp : IsProjectiveOver (β ≫ g))
    (hpair : DeJong.IsSemistablePair (β ≫ g) D')
    [IsAlgClosed (IsLocalRing.closedPoint V).asIdeal.ResidueField]
    (hE₀ : NumericallyStableFibre β g D' (residuePt (IsLocalRing.closedPoint V)))
    (v : pullback (C := Scheme.{u}) (β ≫ g) (residuePt (IsLocalRing.closedPoint V))) :
    ¬ IsCombExceptional β g D' (residuePt (IsLocalRing.closedPoint V)) v := by
  intro hv
  have hnod : DeJong.IsNodalCurve (β ≫ g) := hpair.nodal
  have hetale : Etale (D'.subschemeι ≫ (β ≫ g)) := hpair.etale
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
  have : Finite (genericPoints
      (pullback (C := Scheme.{u}) (β ≫ g) (residuePt (IsLocalRing.closedPoint V)))) :=
    (genericPoints.finite NoetherianSpace.finite_irreducibleComponents).to_subtype
  have : IsReduced
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
  have hvg := hv.mem_genericPoints
  have hZ : closure {v} ∈ irreducibleComponents
      (pullback (C := Scheme.{u}) (β ≫ g) (residuePt (IsLocalRing.closedPoint V))) := hvg
  -- `p_a = g(v) = 0`
  have hpa : arithmeticGenus (closureScheme v) (structureCoeff (closureι v ≫
      pullback.snd (β ≫ g) (residuePt (IsLocalRing.closedPoint V)))) = 0 := by
    rw [hbridge _ _ _ hdim₀ hp₀ hnodal₀ v hvg hv.exists_ne_of_isGeometricOrdinaryDoublePoint,
      hv.componentGenus_eq_zero]
  -- the special points of `closure {v}` are closed
  have hvsm := isSmoothAt_of_mem_genericPoints _ hdim₀ hp₀ hpure₀ hnodal₀ hvg
  have hvD := not_mem_support_of_mem_genericPoints (β ≫ g) D' hpure₀ hvg
  have hsub : closure {v} ∩ specialPoints (β ≫ g) D' (residuePt (IsLocalRing.closedPoint V)) ⊆
      closure {v} ∩ specialPoints (β ≫ g) D' (residuePt (IsLocalRing.closedPoint V)) ∩
        {y | IsClosed ({y} : Set _)} := by
    rintro y ⟨hyv, hys⟩
    refine ⟨⟨hyv, hys⟩, ?_⟩
    by_cases hyg : y ∈ genericPoints
        (pullback (C := Scheme.{u}) (β ≫ g) (residuePt (IsLocalRing.closedPoint V)))
    · exfalso
      have hvy : v = y := eq_of_mem_closure_of_mem_genericPoints hyg hyv
      subst hvy
      rcases hys with h | h
      · exact hvD h
      · exact h hvsm
    · exact CurvesField.Genus.isClosed_singleton_of_not_mem_genericPoints hdim₀ hyg
  have h2 := (Set.encard_le_encard hsub).trans hv.encard_closed_special_le_two
  have : CompactSpace (Scheme.IdealSheafData.vanishingIdeal
      ⟨closure {v}, isClosed_of_mem_irreducibleComponents _ hZ⟩).subscheme :=
    compactSpace_closureScheme v
  have : IsSeparated (terminal.from (Scheme.IdealSheafData.vanishingIdeal
      ⟨closure {v}, isClosed_of_mem_irreducibleComponents _ hZ⟩).subscheme) := by
    have e : closureι v ≫ pullback.snd (β ≫ g) (residuePt (IsLocalRing.closedPoint V)) ≫
        terminal.from _ = terminal.from (closureScheme v) := terminal.hom_ext _ _
    have : IsSeparated (terminal.from (closureScheme v)) := by rw [← e]; infer_instance
    exact this
  have h3 := hE₀ (closure {v}) hZ hv.contracted hpa
  have : (3 : ℕ∞) ≤ 2 := h3.trans h2
  exact absurd this (by decide)

/-- **Temkin's Lemma 4.4.4, numerical form** (`emptylem`, T:3158–3176; blueprint
`lem:sm-stable-iff-no-closed-exc`; ERRATA T57). Let `V` be a valuation ring with finitely many
primes and all `Frac(V/𝔭)` separably closed, and `(β ≫ g : X → C → Spec V, D')` a semi-stable
pair, proper and projective over `V`, with `g` proper and algebraically closed residue field at
the closed point `s₀`. If the closed fibre is numerically stable (Temkin's `E₀ = ∅`), so is the
fibre over every point `t` of `Spec V` with algebraically closed residue field. Hypotheses not
formalized: `ClosureComponentLocal` and `NodalComponentGenus`. -/
theorem numericallyStableFibre_residuePt_of_closedPoint (hloc : ClosureComponentLocal.{u})
    (hbridge : NodalComponentGenus.{u})
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsProper (β ≫ g)] [IsProper g] (hp : IsProjectiveOver (β ≫ g))
    (hpair : DeJong.IsSemistablePair (β ≫ g) D')
    [IsAlgClosed (IsLocalRing.closedPoint V).asIdeal.ResidueField]
    (hE₀ : NumericallyStableFibre β g D' (residuePt (IsLocalRing.closedPoint V)))
    (t : PrimeSpectrum V) [IsAlgClosed t.asIdeal.ResidueField] :
    NumericallyStableFibre β g D' (residuePt t) :=
  numericallyStableFibre_of_forall_not_isCombExceptional β g D' hloc hsep hp hpair
    (not_isCombExceptional_of_numericallyStableFibre β g D' hbridge hp hpair hE₀) t

/-- **Temkin's Lemma 4.4.4, numerical form, for all geometric fibres**: with all residue fields
of `V` algebraically closed (e.g. `Frac V` algebraically closed, `isAlgClosed_residueField_of_ne_bot`)
and the base-change statement `NumericalDescent`, numerical stability of the closed fibre implies
numerical stability of every geometric fibre (lane T5G's `Global.IsNumericallyStable`). -/
theorem numericallyStableFibre_of_closedPoint (hloc : ClosureComponentLocal.{u})
    (hbridge : NodalComponentGenus.{u}) (hdesc : NumericalDescent.{u})
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    (halg : ∀ t : PrimeSpectrum V, IsAlgClosed t.asIdeal.ResidueField)
    [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsProper (β ≫ g)] [IsProper g] (hp : IsProjectiveOver (β ≫ g))
    (hpair : DeJong.IsSemistablePair (β ≫ g) D')
    (hE₀ : NumericallyStableFibre β g D' (residuePt (IsLocalRing.closedPoint V)))
    (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ Spec (CommRingCat.of V)) :
    NumericallyStableFibre β g D' a := by
  obtain ⟨x⟩ : Nonempty (Spec (.of K)) := inferInstance
  have := halg (IsLocalRing.closedPoint V)
  have := halg (a x)
  have ht := numericallyStableFibre_residuePt_of_closedPoint β g D' hloc hbridge hsep hp hpair
    hE₀ (a x)
  exact hdesc V X C β g D' (a x) ht K a fun y => by rw [Subsingleton.elim y x]

/-- **Temkin's Lemma 4.4.4, numerical form, as an equivalence**: under the hypotheses of
`numericallyStableFibre_of_closedPoint`, all geometric fibres are numerically stable iff the
closed fibre is (`E₀ = ∅`). -/
theorem numericallyStable_iff_closedPoint (hloc : ClosureComponentLocal.{u})
    (hbridge : NodalComponentGenus.{u}) (hdesc : NumericalDescent.{u})
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    (halg : ∀ t : PrimeSpectrum V, IsAlgClosed t.asIdeal.ResidueField)
    [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsProper (β ≫ g)] [IsProper g] (hp : IsProjectiveOver (β ≫ g))
    (hpair : DeJong.IsSemistablePair (β ≫ g) D') :
    (∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ Spec (CommRingCat.of V)),
        NumericallyStableFibre β g D' a) ↔
      NumericallyStableFibre β g D' (residuePt (IsLocalRing.closedPoint V)) := by
  refine ⟨fun h => ?_, fun h => numericallyStableFibre_of_closedPoint β g D' hloc hbridge hdesc
    hsep halg hp hpair h⟩
  have := halg (IsLocalRing.closedPoint V)
  exact h _ _

/-- **Temkin's Lemma 4.4.4 for Temkin's stability** (`emptylem`, T:3158–3176; blueprint
`lem:sm-stable-iff-no-closed-exc`, the direction used by the blow-down): a semi-stable
η-modification `β : (X, D') → (C, D)` over `V`, projective over `V`, whose closed fibre is
numerically stable (`E₀ = ∅`), is a stable modification (`Curves.IsStableModification`: no
geometric fibre has an exceptional `ℙ¹`). -/
theorem isStableModification_of_numericallyStableFibre_closedPoint
    (hloc : ClosureComponentLocal.{u}) (hbridge : NodalComponentGenus.{u})
    (hdesc : NumericalDescent.{u})
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    (halg : ∀ t : PrimeSpectrum V, IsAlgClosed t.asIdeal.ResidueField)
    [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsProper (β ≫ g)] [IsProper g] (hp : IsProjectiveOver (β ≫ g))
    (D : C.IdealSheafData) (hη : Curves.IsEtaModification β g)
    (hmarks : D' = Curves.genericMarksClosure β g D (genericPoint (Spec (CommRingCat.of V))))
    (hpair : DeJong.IsSemistablePair (β ≫ g) D')
    (hE₀ : NumericallyStableFibre β g D' (residuePt (IsLocalRing.closedPoint V))) :
    IsStableModification β g D D' where
  toIsEtaModification := hη
  marks_eq := hmarks
  isSemistablePair := hpair
  not_isExceptionalComponent K _ _ a _Z hE :=
    not_numericallyStableFibre_of_isExceptionalComponent β g D' a hE
      (numericallyStableFibre_of_closedPoint β g D' hloc hbridge hdesc hsep halg hp hpair hE₀
        K a)

end Main

end DeJongAlterations.StableModification.BlowDown.NoClosedExc
