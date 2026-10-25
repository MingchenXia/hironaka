/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.Stable
import DeJongAlterations.StableModification.BlowDown.NoClosedExc
import DeJongAlterations.StableModification.Curves.SemistableNormalScheme

/-!
# The blow-down produces a stable modification (Temkin, Prop. 4.4.6 with Lemma 4.4.4)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`),
Prop. 4.4.6 (T:3188–3229): iterate exceptional blow-downs until the closed fibre has no
exceptional component, and conclude by Lemma 4.4.4 (T:3158–3176). The iteration
(`BlowDown.exists_dominated_stage_not_hasClosedExceptional`) stops at a stage without an
exceptional component of the closed fibre in the form `BlowDown.IsClosedExceptional`
(on the scheme-theoretic fibre `(β ≫ φ).fiber s₀` over `κ(s₀) = (Spec V).residueField s₀`, used by
the stability criterion of lane T44A2), while Lemma 4.4.4 (lane T44A3,
`NoClosedExc.isStableModification_of_forall_not_isCombExceptional`) is stated with
`ExcSpecialize.IsCombExceptional` on the residue-field fibre `pullback (β ≫ φ) (residuePt s₀)` over
`Ideal.ResidueField`. This file proves the bridge and assembles PLAN-T5's `BlowDownStable`
(blueprint `thm:sm-bdg-blowdown-stable`, `sm-blow-down-global.tex`).

## Main results

* `eulerChar_comp_ringEquiv`, `componentGenus_comp_ringEquiv`: `χ(𝒪)` and the genera of the
  normalized components do not change when the coefficient field is changed along a ring
  isomorphism `k₁ ≃ k₂` (the Čech complexes are the same complexes of abelian groups,
  `cechComplexRingEquivIso`).
* `residueFibreHom`: the isomorphism `pullback q (residuePt t) ≅ q.fiber t` over
  `Spec κ(t) ≅ Spec (Spec V).κ(t)`; `componentGenus_residueFibreHom`: it preserves the genera of the
  components.
* `residueFibre_node`: an ordinary double point of the closed fibre corresponds to a closed
  non-smooth ordinary double point of the residue-field fibre.
* `hasClosedExceptional_of_isCombExceptional` (**the bridge**): a combinatorially exceptional
  component of the residue-field fibre of a semi-stable stage is an exceptional component of its
  closed fibre in the sense of `IsClosedExceptional`;
  `not_isCombExceptional_of_not_hasClosedExceptional` is the form consumed by T44A3's theorems.
* `isSemistableStage_of_isSmoothAt_generic`: a projective semi-stable η-modification with
  smooth generic fibre and integral source is a semi-stable stage (normality is automatic).
* `exists_isStableModification_of_isSemistableStage` (**Temkin's Prop. 4.4.6**, PLAN-T5's
  `BlowDownStable`): every semi-stable stage dominates a semi-stable stage which is a stable
  modification, projective over `V`, with all geometric fibres numerically stable
  (`NoClosedExc.NumericallyStableFibre`), given Temkin's contracting morphisms
  (`ContractingMorphismExists`, not formalized) and T44A3's named hypotheses
  `ClosureComponentLocal`, `NumericalDescent`.
-/

namespace DeJongAlterations.StableModification.BlowDown

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open DeJongAlterations.StableModification.Cohomology
open DeJongAlterations.StableModification.CurvesField
open DeJongAlterations.StableModification.CurvesField.IncidenceGraph
open DeJongAlterations.StableModification.CurvesField.Genus
open ClosureComponent (residuePt residuePt_eq)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

universe u

noncomputable section

section FieldChange

variable {X : Scheme.{u}} {k₁ k₂ : Type u} [Field k₁] [Field k₂] (f : k₁ ≃+* k₂)

/-- **The Čech complex with coefficients changed along a ring isomorphism** `f : k₁ ≃ k₂` is the
restriction of scalars of the Čech complex with `k₂`-coefficients (the identity on cochains). -/
def cechComplexRingEquivIso (F : X.Modules) {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (c : k₂ →+* Γ(X, ⊤)) :
    cechComplex F U (c.comp f.toRingHom) ≅
      ((ModuleCat.restrictScalars f.toRingHom).mapHomologicalComplex _).obj (cechComplex F U c) :=
  HomologicalComplex.Hom.isoOfComponents (fun p => LinearEquiv.toModuleIso
    ({ toFun := fun x => x
       invFun := fun x => x
       map_add' := fun _ _ => rfl
       map_smul' := fun _ _ => rfl
       left_inv := fun _ => rfl
       right_inv := fun _ => rfl } : (cechComplex F U (c.comp f.toRingHom)).X p ≃ₗ[k₁]
        ((ModuleCat.restrictScalars f.toRingHom).obj ((cechComplex F U c).X p)))) (by
      intro i j hij
      obtain rfl : i + 1 = j := hij
      ext x
      simp only [cechComplex, DeJongAlterations.Geometry.ProperSteinProjectiveCech.subsetCechComplex,
        CochainComplex.of_d, Functor.mapHomologicalComplex_obj_d, ModuleCat.hom_comp,
        LinearMap.coe_comp, Function.comp_apply]
      rfl)

/-- The dimensions of Čech cohomology do not change along a ring isomorphism of the
coefficients. -/
theorem finrank_cechCohomology_comp_ringEquiv (F : X.Modules) {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) (c : k₂ →+* Γ(X, ⊤)) (i : ℕ) :
    Module.finrank k₁ ((cechComplex F U (c.comp f.toRingHom)).homology i) =
      Module.finrank k₂ ((cechComplex F U c).homology i) := by
  let E : (cechComplex F U (c.comp f.toRingHom)).homology i ≅
      (ModuleCat.restrictScalars f.toRingHom).obj ((cechComplex F U c).homology i) :=
    (HomologicalComplex.homologyFunctor _ _ i).mapIso (cechComplexRingEquivIso f F U c) ≪≫
      ((cechComplex F U c).sc i).mapHomologyIso (ModuleCat.restrictScalars f.toRingHom)
  have h := rank_eq_of_equiv_equiv (R := k₁) (R' := k₂)
    (M := (cechComplex F U (c.comp f.toRingHom)).homology i)
    (M₁ := (cechComplex F U c).homology i) f E.toLinearEquiv.toAddEquiv f.bijective
    (fun r m => by
      change E.toLinearEquiv (r • m) = _
      rw [map_smul]
      rfl)
  unfold Module.finrank
  rw [h]

/-- **`χ(𝒪_X)` does not change along a ring isomorphism of the coefficient fields.** -/
theorem eulerChar_comp_ringEquiv [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (c : k₂ →+* Γ(X, ⊤)) :
    eulerChar X (c.comp f.toRingHom) = eulerChar X c := by
  unfold eulerChar HomologicalComplex.homologyEulerChar GradedObject.eulerChar
  congr 1
  funext i
  rw [finrank_cechCohomology_comp_ringEquiv]

/-- **The genera of the normalized components do not change along a ring isomorphism of the
coefficient fields.** -/
theorem componentGenus_comp_ringEquiv {C : Scheme.{u}} [CompactSpace C]
    [IsAffineHom (pullback.diagonal (terminal.from C))] (c : k₂ →+* Γ(C, ⊤)) (η : C) :
    componentGenus (c.comp f.toRingHom) η = componentGenus c η := by
  unfold componentGenus arithmeticGenus
  rw [← RingHom.comp_assoc, eulerChar_comp_ringEquiv]

/-- `structureCoeff (p ≫ Spec g) = structureCoeff p ∘ g`. -/
theorem structureCoeff_comp_specMap {A B : Type u} [CommRing A] [CommRing B] {Z : Scheme.{u}}
    (p : Z ⟶ Spec (CommRingCat.of B)) (g : A →+* B) :
    structureCoeff (p ≫ Spec.map (CommRingCat.ofHom g)) = (structureCoeff p).comp g := by
  ext a
  simp only [structureCoeff, Scheme.Hom.comp_appTop, RingHom.comp_apply]
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g)
  have h' := congrArg (fun φ => φ.hom a) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h'
  rw [CommRingCat.hom_comp, RingHom.comp_apply, ← h']
  rfl

end FieldChange

section ResidueFibre

variable {V : Type u} [CommRing V] {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of V))
  (t : PrimeSpectrum V)

/-- **The residue-field fibre is the scheme-theoretic fibre**: the isomorphism
`Y ×_V Spec κ(t) → q.fiber t` over `Spec κ(t) ≅ Spec (Spec V).κ(t)` (lane T44A3's
`ClosureComponent.residuePt_eq`). -/
def residueFibreHom : pullback q (residuePt t) ⟶ q.fiber t :=
  pullback.map q (residuePt t) q ((Spec (CommRingCat.of V)).fromSpecResidueField t) (𝟙 Y)
    (Spec.map (Scheme.Spec.residueFieldIso (CommRingCat.of V) t).hom) (𝟙 _) (by simp)
    (by rw [Category.comp_id, residuePt_eq])

instance isIso_residueFibreHom : IsIso (residueFibreHom q t) := by
  unfold residueFibreHom
  infer_instance

@[reassoc (attr := simp)]
theorem residueFibreHom_fiberι :
    residueFibreHom q t ≫ q.fiberι t = pullback.fst q (residuePt t) := by
  unfold residueFibreHom Scheme.Hom.fiberι
  rw [pullback.lift_fst, Category.comp_id]

@[reassoc]
theorem residueFibreHom_fiberToSpecResidueField :
    residueFibreHom q t ≫ q.fiberToSpecResidueField t = pullback.snd q (residuePt t) ≫
      Spec.map (Scheme.Spec.residueFieldIso (CommRingCat.of V) t).hom := by
  unfold residueFibreHom Scheme.Hom.fiberToSpecResidueField
  rw [pullback.lift_snd]

/-- **`residueFibreHom` preserves the genera of the normalized components** (lane T44A3's
`ExcSpecialize.componentGenus_eq` for the isomorphism, and the change of coefficient field
`componentGenus_comp_ringEquiv`). -/
theorem componentGenus_residueFibreHom [IsSeparated q] [LocallyOfFiniteType q] [QuasiCompact q]
    [CompactSpace (pullback (C := Scheme.{u}) q (residuePt t))]
    [IsAffineHom (pullback.diagonal (terminal.from (pullback (C := Scheme.{u}) q (residuePt t))))]
    (v : pullback (C := Scheme.{u}) q (residuePt t)) :
    componentGenus (structureCoeff (A := ↑((Spec (CommRingCat.of V)).residueField t))
        (q.fiberToSpecResidueField t)) (residueFibreHom q t v) =
      componentGenus (structureCoeff (pullback.snd q (residuePt t))) v := by
  have : CompactSpace (q.fiber t) := compactSpace_of_quasiCompact (q.fiberToSpecResidueField t)
  have h1 := ExcSpecialize.componentGenus_eq (q.fiberToSpecResidueField t) (residueFibreHom q t) v
  rw [← h1, residueFibreHom_fiberToSpecResidueField]
  rw [show Spec.map (Scheme.Spec.residueFieldIso (CommRingCat.of V) t).hom =
    Spec.map (CommRingCat.ofHom (Scheme.Spec.residueFieldIso (CommRingCat.of V) t).hom.hom)
      from rfl, structureCoeff_comp_specMap]
  exact componentGenus_comp_ringEquiv
    (Scheme.Spec.residueFieldIso (CommRingCat.of V) t).commRingCatIsoToRingEquiv _ _

end ResidueFibre

section Bridge

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
  [IsAlgClosed ((Spec (CommRingCat.of V)).residueField (IsLocalRing.closedPoint V))]

local notation "s₀" => IsLocalRing.closedPoint V

/-- The residue field `Ideal.ResidueField` of the closed point is algebraically closed. -/
theorem isAlgClosed_residueField_closedPoint :
    IsAlgClosed (IsLocalRing.closedPoint V).asIdeal.ResidueField :=
  IsAlgClosed.of_ringEquiv _ _
    (Scheme.Spec.residueFieldIso (CommRingCat.of V) _).commRingCatIsoToRingEquiv

/-- **Double points of the closed fibre in the residue-field presentation**: if `y` is a closed
ordinary double point of the closed fibre `q.fiber s₀` of a nodal curve, not generic, then the
corresponding point `y₂` of `pullback q (residuePt s₀)` is closed, not smooth and an ordinary double
point (a double point has two branches, a smooth point one; the smooth locus of a geometric fibre
is the preimage of that of `q`, lane OM1's `Omega.preimage_smoothLocus_eq_of_isNodalCurve`). -/
theorem residueFibre_node {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of V))
    [DeJong.IsNodalCurve q] [IsProper q] (y : q.fiber s₀) (hyc : IsClosed ({y} : Set _))
    (hyg : y ∉ genericPoints (q.fiber s₀))
    (hy : Geometry.IsGeometricOrdinaryDoublePoint (q.fiberToSpecResidueField s₀) y)
    (y₂ : pullback (C := Scheme.{u}) q (residuePt s₀)) (hy₂ : residueFibreHom q s₀ y₂ = y) :
    IsClosed ({y₂} : Set _) ∧ ¬ DeJong.IsSmoothAt (pullback.snd q (residuePt s₀)) y₂ ∧
      Geometry.IsGeometricOrdinaryDoublePoint (pullback.snd q (residuePt s₀)) y₂ := by
  have hκ := isAlgClosed_residueField_closedPoint (V := V)
  have hns₁ : ¬ DeJong.IsSmoothAt (q.fiberToSpecResidueField s₀) y := by
    intro hs
    have h2 := natCard_fiber_eq_two_of_isGeometricOrdinaryDoublePoint
      (q.fiberToSpecResidueField s₀) (topologicalKrullDim_fiber_le_one_of_nodal q s₀) y hyc hyg hy
    have h1 := natCard_fiber_eq_one_of_isSmoothAt (q.fiberToSpecResidueField s₀)
      (topologicalKrullDim_fiber_le_one_of_nodal q s₀) y hyc hyg hs
    omega
  have hfst : pullback.fst q (residuePt s₀) y₂ = q.fiberι s₀ y := by
    rw [← hy₂, ← Scheme.Hom.comp_apply, residueFibreHom_fiberι]
  have hnsq : pullback.fst q (residuePt s₀) y₂ ∉ q.smoothLocus := by
    rw [hfst]
    intro h
    exact hns₁ (DeJong.isSmoothAt_pullback_snd q _ y h)
  have hns₂ : ¬ DeJong.IsSmoothAt (pullback.snd q (residuePt s₀)) y₂ := by
    intro hs
    have hpb := Omega.preimage_smoothLocus_eq_of_isNodalCurve q
      (IsLocalRing.closedPoint V).asIdeal.ResidueField (residuePt s₀)
    have h : y₂ ∈ (pullback.snd q (residuePt s₀)).smoothLocus :=
      (DeJong.isSmoothAt_iff_mem_smoothLocus _ _).1 hs
    rw [← hpb] at h
    exact hnsq h
  let H := Scheme.homeoOfIso (asIso (residueFibreHom q s₀))
  have hc₂ : IsClosed ({y₂} : Set _) := by
    have e : ({y₂} : Set (pullback (C := Scheme.{u}) q (residuePt s₀))) = H ⁻¹' {y} := by
      ext z
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro rfl
        exact hy₂
      · intro hz
        exact H.injective (hz.trans hy₂.symm)
    rw [e]
    exact hyc.preimage H.continuous
  exact ⟨hc₂, hns₂, Omega.isGeometricOrdinaryDoublePoint_of_not_mem_smoothLocus q _ (residuePt s₀)
    y₂ hc₂ hnsq⟩

variable {C : Scheme.{u}} (φ : C ⟶ Spec (CommRingCat.of V)) (D : C.IdealSheafData)

/-- **The bridge to lane T44A3's exceptional components** (blueprint
`lem:sm-bdg-comb-bridge`): if the residue-field fibre `pullback (β ≫ φ) (residuePt s₀)` of a
semi-stable stage `β` has a combinatorially exceptional component `v`
(`ExcSpecialize.IsCombExceptional`, with the transported marks), then the closed fibre
`(β ≫ φ).fiber s₀` has an exceptional component (`IsClosedExceptional`), namely the image of `v`
under `residueFibreHom`. Its genus is that of `v` (`componentGenus_residueFibreHom`); a double point
with both branches on it would be a double point of `v` lying on no other component; its boundary
double points (closed, not smooth) and its marks (smooth, closed since étale marks miss the generic
points) are distinct closed special points of `v`, at most two. -/
theorem hasClosedExceptional_of_isCombExceptional {Y : Scheme.{u}} (β : Y ⟶ C)
    (hY : IsSemistableStage φ D β)
    [CompactSpace (pullback (C := Scheme.{u}) (β ≫ φ) (residuePt s₀))]
    [IsAffineHom (pullback.diagonal
      (terminal.from (pullback (C := Scheme.{u}) (β ≫ φ) (residuePt s₀))))]
    (v : pullback (C := Scheme.{u}) (β ≫ φ) (residuePt s₀))
    (hv : ExcSpecialize.IsCombExceptional β φ
      (Curves.genericMarksClosure β φ D (genericPoint (Spec (CommRingCat.of V))))
      (residuePt s₀) v) :
    HasClosedExceptional φ D β := by
  have hn : DeJong.IsNodalCurve (β ≫ φ) := hY.isSemistablePair.nodal
  have hpr : IsProper (β ≫ φ) := hY.isProjectiveOver.isProper
  have hκ := isAlgClosed_residueField_closedPoint (V := V)
  have hetD := hY.isSemistablePair.etale
  let F := residueFibreHom (β ≫ φ) s₀
  let H := Scheme.homeoOfIso (asIso F)
  have hH : ∀ x, H x = F x := fun _ => rfl
  have hF1 : ∀ x, (β ≫ φ).fiberι s₀ (F x) = pullback.fst (β ≫ φ) (residuePt s₀) x := fun x => by
    rw [← Scheme.Hom.comp_apply, residueFibreHom_fiberι]
  have hFsurj : ∀ y, ∃ x, F x = y := fun y => ⟨H.symm y, H.apply_symm_apply y⟩
  have hcl : ∀ x, closure {F x} = F '' closure {x} := fun x => by
    rw [← hH, ← Set.image_singleton, ← H.image_closure]
    rfl
  have hgen : ∀ x, x ∈ genericPoints (pullback (C := Scheme.{u}) (β ≫ φ) (residuePt s₀)) ↔
      F x ∈ genericPoints ((β ≫ φ).fiber s₀) := fun x => by
    rw [mem_genericPoints_iff, mem_genericPoints_iff]
    constructor
    · intro h ξ hξ
      obtain ⟨ξ', rfl⟩ := hFsurj ξ
      rw [h ξ' ((H.isInducing.specializes_iff).1 hξ)]
    · intro h ξ hξ
      exact H.injective (h _ (hξ.map H.continuous))
  -- dimension and purity of the residue-field fibre
  have hdim₂ : topologicalKrullDim (pullback (C := Scheme.{u}) (β ≫ φ) (residuePt s₀)) ≤ 1 := by
    rw [IsHomeomorph.topologicalKrullDim_eq H H.isHomeomorph]
    exact topologicalKrullDim_fiber_le_one_of_nodal (β ≫ φ) s₀
  have hpure₂ := hn.pureGeometricFibers (IsLocalRing.closedPoint V).asIdeal.ResidueField
    (residuePt s₀)
  -- the genus
  have hgenus : componentGenus (structureCoeff (A := ↑((Spec (CommRingCat.of V)).residueField s₀))
      ((β ≫ φ).fiberToSpecResidueField s₀)) (F v) = 0 :=
    (componentGenus_residueFibreHom (β ≫ φ) s₀ v).trans hv.componentGenus_eq_zero
  -- the contraction
  have hcontr : (β '' closure {(β ≫ φ).fiberι s₀ (F v)}).Subsingleton := by
    rw [closure_fiberι_singleton, hcl, Set.image_image, Set.image_image]
    have e : (fun x => β ((β ≫ φ).fiberι s₀ (F x))) = fun x =>
        pullback.fst φ (residuePt s₀) (Curves.pullbackCompMap β φ (residuePt s₀) x) := by
      funext x
      rw [hF1, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Curves.pullbackCompMap_fst]
    rw [e, ← Set.image_image]
    exact hv.contracted.image _
  -- the double points of the closed fibre on the component
  have hnode : ∀ y : (β ≫ φ).fiber s₀, y ∈ nodesIn ((β ≫ φ).fiberToSpecResidueField s₀)
      (closure {F v}) → ∃ y₂, F y₂ = y ∧ y₂ ∈ closure {v} ∧ IsClosed ({y₂} : Set _) ∧
        ¬ DeJong.IsSmoothAt (pullback.snd (β ≫ φ) (residuePt s₀)) y₂ ∧
        Geometry.IsGeometricOrdinaryDoublePoint (pullback.snd (β ≫ φ) (residuePt s₀)) y₂ := by
    rintro y ⟨hyZ, hyc, hyg, hyo⟩
    obtain ⟨y₂, rfl⟩ := hFsurj y
    obtain ⟨hc₂, hns₂, ho₂⟩ := residueFibre_node (β ≫ φ) _ hyc hyg hyo y₂ rfl
    refine ⟨y₂, rfl, ?_, hc₂, hns₂, ho₂⟩
    rw [hcl] at hyZ
    obtain ⟨z, hz, hzy⟩ := hyZ
    rw [← H.injective hzy]
    exact hz
  refine ⟨hn, hpr, F v, ?_⟩
  unfold IsClosedExceptional
  refine ⟨(hgen v).1 hv.mem_genericPoints, hcontr, hgenus.symm.le, fun {_} => ⟨?_, ?_⟩⟩
  · -- `{F v}` is a `ℙ¹`-tree
    refine ⟨⟨⟨Finset.singleton_nonempty _, fun X hX hXne hXZ => ?_⟩, ?_⟩, ?_⟩
    · exact absurd ((Finset.subset_singleton_iff.1 hX).resolve_left hXne.ne_empty) hXZ
    · rw [Finset.card_singleton, Nat.add_eq_right, Finset.card_eq_zero]
      classical
      refine Finset.eq_empty_of_forall_notMem fun e he => ?_
      rw [mem_inner] at he
      obtain ⟨y₂, hy₂, hy₂v, hc₂, -, ho₂⟩ := hnode e.1 e.2
      obtain ⟨w, hw, hwv, hyw⟩ := hv.exists_ne_of_isGeometricOrdinaryDoublePoint y₂ hy₂v hc₂ ho₂
      have hFw : F w ∈ (nodalGraph ((β ≫ φ).fiberToSpecResidueField s₀)
          (topologicalKrullDim_fiber_le_one_of_nodal (β ≫ φ) s₀) (closure {F v})).ends e := by
        rw [mem_nodalGraph_ends]
        refine ⟨(hgen w).1 hw, ?_⟩
        rw [hcl, ← hy₂]
        exact ⟨y₂, hyw, rfl⟩
      have h := he _ hFw
      rw [Finset.mem_singleton] at h
      exact hwv (H.injective h)
    · intro w hw
      rw [Finset.mem_singleton] at hw
      subst hw
      rw [nodalGraph_genus, hgenus]
      rfl
  · -- at most two boundary double points and marks
    set DY := Curves.genericMarksClosure β φ D (genericPoint (Spec (CommRingCat.of V))) with hDY
    set M := closure {(β ≫ φ).fiberι s₀ (F v)} ∩ (DY.support : Set Y) with hM
    set G := nodalGraph ((β ≫ φ).fiberToSpecResidueField s₀)
      (topologicalKrullDim_fiber_le_one_of_nodal (β ≫ φ) s₀) (closure {F v}) with hG
    have hS₂ := hv.encard_closed_special_le_two
    let g : nodesIn ((β ≫ φ).fiberToSpecResidueField s₀) (closure {F v}) →
        pullback (C := Scheme.{u}) (β ≫ φ) (residuePt s₀) := fun e => H.symm e.1
    have hg_inj : Function.Injective g := fun e₁ e₂ h => Subtype.ext (H.symm.injective h)
    have hgF : ∀ e, F (g e) = e.1 := fun e => H.apply_symm_apply e.1
    set B₂ := g '' ((G.boundary {F v} : Finset _) : Set _) with hB₂def
    set M₂ := pullback.fst (β ≫ φ) (residuePt s₀) ⁻¹' M with hM₂def
    have hB₂ : B₂ ⊆ closure {v} ∩ ExcSpecialize.specialPoints (β ≫ φ) DY (residuePt s₀) ∩
        {y | IsClosed ({y} : Set _)} := by
      rintro _ ⟨e, -, rfl⟩
      obtain ⟨y₂, hy₂, hy₂v, hc₂, hns₂, -⟩ := hnode e.1 e.2
      have : g e = y₂ := H.injective ((hgF e).trans hy₂.symm)
      rw [this]
      exact ⟨⟨hy₂v, Or.inr hns₂⟩, hc₂⟩
    have hM₂ : M₂ ⊆ closure {v} ∩ ExcSpecialize.specialPoints (β ≫ φ) DY (residuePt s₀) ∩
        {y | IsClosed ({y} : Set _)} := by
      rintro y ⟨hyZ, hyD⟩
      have hyv : y ∈ closure {v} := by
        rw [ExcSpecialize.closure_singleton_eq_preimage, Set.mem_preimage, ← hF1]
        exact hyZ
      have hyg : y ∉ genericPoints (pullback (C := Scheme.{u}) (β ≫ φ) (residuePt s₀)) :=
        fun hg => NoClosedExc.not_mem_support_of_mem_genericPoints (β ≫ φ) DY hpure₂ hg hyD
      exact ⟨⟨hyv, Or.inl hyD⟩, isClosed_singleton_of_not_mem_genericPoints hdim₂ hyg⟩
    have hdisj : Disjoint B₂ M₂ := by
      rw [Set.disjoint_left]
      rintro _ ⟨e, -, rfl⟩ hyM
      obtain ⟨y₂, hy₂, -, -, hns₂, -⟩ := hnode e.1 e.2
      have he : g e = y₂ := H.injective ((hgF e).trans hy₂.symm)
      rw [he] at hyM
      exact hns₂ (DeJong.isSmoothAt_pullback_snd (β ≫ φ) _ y₂
        (hY.isSemistablePair.smoothAlong _ hyM.2))
    have hMrange : M ⊆ Set.range (pullback.fst (β ≫ φ) (residuePt s₀)) := by
      rintro m ⟨hmZ, -⟩
      rw [closure_fiberι_singleton] at hmZ
      obtain ⟨z, -, rfl⟩ := hmZ
      obtain ⟨z₂, rfl⟩ := hFsurj z
      exact ⟨z₂, (hF1 z₂).symm⟩
    have hcardB : B₂.encard = ((G.boundary {F v}).card : ℕ∞) := by
      rw [hB₂def, hg_inj.injOn.encard_image, Set.encard_coe_eq_coe_finsetCard]
    have hcardM : M₂.encard = M.encard :=
      Set.encard_preimage_of_injective_subset_range
        (ClosureComponent.isEmbedding_fst_residuePt (β ≫ φ) s₀).injective hMrange
    have htot : ((G.boundary {F v}).card : ℕ∞) + M.encard ≤ 2 := by
      rw [← hcardB, ← hcardM, ← Set.encard_union_eq hdisj]
      exact (Set.encard_le_encard (Set.union_subset hB₂ hM₂)).trans hS₂
    have hMfin : M.Finite := Set.finite_of_encard_le_coe (le_trans le_add_self htot)
    change (G.boundary {F v}).card + M.ncard ≤ 2
    rw [← hMfin.cast_ncard_eq] at htot
    exact_mod_cast htot

/-- **No exceptional component of the closed fibre ⇒ `E₀ = ∅` in T44A3's form**: the
termination condition of the blow-down (`¬ HasClosedExceptional`) gives the hypothesis `hE₀` of
`NoClosedExc.isStableModification_of_forall_not_isCombExceptional` and
`NoClosedExc.numericallyStableFibre_of_forall_not_isCombExceptional_of_descent`. -/
theorem not_isCombExceptional_of_not_hasClosedExceptional {Y : Scheme.{u}} (β : Y ⟶ C)
    (hY : IsSemistableStage φ D β) (hE : ¬ HasClosedExceptional φ D β)
    [CompactSpace (pullback (C := Scheme.{u}) (β ≫ φ) (residuePt s₀))]
    [IsAffineHom (pullback.diagonal
      (terminal.from (pullback (C := Scheme.{u}) (β ≫ φ) (residuePt s₀))))]
    (v : pullback (C := Scheme.{u}) (β ≫ φ) (residuePt s₀)) :
    ¬ ExcSpecialize.IsCombExceptional β φ
      (Curves.genericMarksClosure β φ D (genericPoint (Spec (CommRingCat.of V))))
      (residuePt s₀) v :=
  fun hv => hE (hasClosedExceptional_of_isCombExceptional φ D β hY v hv)

end Bridge

section Constructor

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] {C : Scheme.{u}}
  (φ : C ⟶ Spec (CommRingCat.of V)) (D : C.IdealSheafData)

/-- **A semi-stable modification with smooth generic fibre is a semi-stable stage** (blueprint
`lem:sm-bdg-stage-of-semistable`): the normality of `Y` is not an extra condition, by lane SS's
`Curves.SemistableNormal.isNormalScheme_of_isNodalCurve_spec` (nodal over the integrally closed
`V` and smooth over the generic point). -/
theorem isSemistableStage_of_isSmoothAt_generic {Y : Scheme.{u}} (β : Y ⟶ C) [IsIntegral Y]
    (hη : Curves.IsEtaModification β φ)
    (hpair : DeJong.IsSemistablePair (β ≫ φ)
      (Curves.genericMarksClosure β φ D (genericPoint (Spec (CommRingCat.of V)))))
    (hp : IsProjectiveOver (β ≫ φ))
    (hgen : ∀ y : Y, ((β ≫ φ) y).asIdeal = ⊥ → DeJong.IsSmoothAt (β ≫ φ) y) :
    IsSemistableStage φ D β where
  isIntegral := inferInstance
  isNormalScheme := by
    have := hpair.nodal
    exact Curves.SemistableNormal.isNormalScheme_of_isNodalCurve_spec (β ≫ φ) hgen
  isEtaModification := hη
  isSemistablePair := hpair
  isProjectiveOver := hp

end Constructor

section Stable

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [Finite (PrimeSpectrum V)]
  {C : Scheme.{u}} (φ : C ⟶ Spec (CommRingCat.of V)) (D : C.IdealSheafData)
  [IsIntegral C] [IsProper φ] [Flat φ] [HenselianLocalRing V]

/-- **Temkin's Proposition 4.4.6** (T:3188–3229; PLAN-T5's `BlowDownStable`, blueprint
`thm:sm-bdg-blowdown-stable`): over a valuation ring `V` of finite height with all residue fields
algebraically closed and all `Frac(V/𝔭)` separably closed, every semi-stable stage `β : Y → C` of a
proper flat integral `V`-curve with marks `D` dominates (`b ≫ β'' = β`) a semi-stable stage
`β'' : Y'' → C` (projective over `V`, integral and normal) which is a stable modification of
`(C, D)` (`Curves.IsStableModification`, Temkin's stability: no exceptional `ℙ¹` in a geometric
fibre) all of whose geometric fibres are numerically stable (`NoClosedExc.NumericallyStableFibre`).

Inputs not formalized, taken as hypotheses: Temkin's contracting morphisms
(`ContractingMorphismExists`, T:3203–3226) and lane T44A3's `ClosureComponentLocal` and
`NumericalDescent`. -/
theorem exists_isStableModification_of_isSemistableStage
    (hloc : ExcSpecialize.ClosureComponentLocal.{u}) (hdesc : NoClosedExc.NumericalDescent.{u})
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
          (Curves.genericMarksClosure β'' φ D (genericPoint (Spec (CommRingCat.of V)))) a := by
  have := halg (IsLocalRing.closedPoint V)
  have : IsAlgClosed ((Spec (CommRingCat.of V)).residueField (IsLocalRing.closedPoint V)) :=
    IsAlgClosed.of_ringEquiv _ _
      (Scheme.Spec.residueFieldIso (CommRingCat.of V) _).commRingCatIsoToRingEquiv.symm
  have : IsAlgClosed (IsLocalRing.ResidueField V) :=
    IsAlgClosed.of_ringEquiv _ _ (residueFieldClosedPointEquiv (V := V)).symm
  obtain ⟨Y'', β'', b, hY'', hb, hE⟩ :=
    exists_dominated_stage_not_hasClosedExceptional φ D hsep hdimC hcontract Y β hY
  have hp := hY''.isProjectiveOver
  have : IsProper (β'' ≫ φ) := hp.isProper
  have : CompactSpace Y'' := compactSpace_of_quasiCompact (β'' ≫ φ)
  have : IsAffineHom (pullback.diagonal (terminal.from Y'')) :=
    isAffineHom_diagonal_of_isSeparated (β'' ≫ φ)
  have hE₀ := not_isCombExceptional_of_not_hasClosedExceptional φ D β'' hY'' hE
  refine ⟨Y'', β'', b, hb, hY'', ?_, fun K _ _ a => ?_⟩
  · exact NoClosedExc.isStableModification_of_forall_not_isCombExceptional β'' φ _ hloc hdesc hsep
      halg hp D hY''.isEtaModification rfl hY''.isSemistablePair hE₀
  · exact NoClosedExc.numericallyStableFibre_of_forall_not_isCombExceptional_of_descent β'' φ _
      hloc hdesc hsep halg hp hY''.isSemistablePair hE₀ K a

end Stable

end

end DeJongAlterations.StableModification.BlowDown
