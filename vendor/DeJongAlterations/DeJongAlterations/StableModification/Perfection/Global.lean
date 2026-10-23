/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane PL-GLOBAL)
-/
import DeJongAlterations.StableModification.Perfection.GlobalPoint
import DeJongAlterations.StableModification.Perfection.GlobalFiber
import DeJongAlterations.StableModification.Perfection.GlobalField
import DeJongAlterations.StableModification.DeJong.Fibration
import DeJongAlterations.Geometry.SteinNormalizationFactor
import DeJongAlterations.Geometry.RationalCoordinateMap

/-!
# The global purely inseparable smoothing

Blueprint chapter `sm-dj-perfection-global`, nodes `lem:sm-dj-perfection-global-charts`,
`lem:sm-dj-perfection-global-finiteness`, `prop:sm-dj-perfection-global-construction`,
`thm:sm-dj-perfection-global` and `cor:sm-dj-perfection-global-fibration` (new route, not in de
Jong 1996; it replaces de Jong 4.11 (ii) (c), (d) when generic étaleness is not
required, see `sm-dj-perfection`, Remark `rem:sm-dj-perfection-generic-etale`).

This file proves `DeJong.PurelyInseparableSmoothing k` (`StableModification/DeJong/Fibration.lean`)
for every algebraically closed field `k` (`purelyInseparableSmoothing`; the body of the statement
holds over any field, `exists_purelyInseparableSmoothing`), hence `DeJong.TemkinReadyFibration k`
(`temkinReadyFibration`).

Let `f : X ⟶ Y` be a proper dominant morphism of normal projective `k`-varieties with
geometrically integral generic fibre of dimension one, and `W ⊆ X` closed, not containing the
generic point. Put `K = K(Y)`, `M` an algebraic closure of `K(X)` and `Ω ⊆ M` the perfect closure
of `K`. For a nonempty affine open `U ⊆ X` let `A_U = K[Γ(X, U)] ⊆ M` (`chartAlgebra`), a
finitely generated `K`-domain of dimension at most one (`finiteType_chartAlgebra`,
`dimensionLEOne_chartAlgebra`) whose fraction field lies in `K(X)`, hence is linearly disjoint
from `Ω` (`linearDisjoint_fracField_chartAlgebra`, from the geometric integrality of the generic
fibre).

1. Cover `X` by finitely many charts `U` (`exists_finset_chart_cover`); the set `W_η` of points
   of `W` over the generic point `η` of `Y` is finite (`finite_boundary_genericFiber`).
2. By PL's ring-level results (`Perfection/Stabilization.lean`, `Perfection/Residue.lean`) there
   is `E ⊆ Ω` finite over `K` such that every `B_E(A_U)` is smooth over `E` and, for `x ∈ W_η`,
   the residue fields of `B_E(A_U)` at the maximal ideals over the ideal of `x` are separable
   over `E`.
3. `Y₁` is the normalization of `Y` in `E`, `X₁` the normalization of `X` in `L = K(X)(E)`, and
   `f₁ : X₁ ⟶ Y₁` Codex's Stein normalization factor (`exists_smoothing_of_field`).
4. At a point `x₁ ∈ X₁` over the generic point of `Y₁` the local ring of `X₁` is a localization of
   `B_E(A_U)` (`Perfection/GlobalPoint.lean`), which gives smoothness of the generic fibre and the
   separability of the residue fields (`Perfection/GlobalFiber.lean`).
5. The generic fibre of `f₁` is geometrically integral since its function field `L ≅ E ⊗_K K(X)`
   is (`Perfection/GlobalField.lean`, Codex's `genericFiber_geometricallyIntegral_of_field`).

In characteristic zero `Ω = K`; the proof is uniform (and `purelyInseparableSmoothing_of_charZero`
of `Fibration.lean` gives the statement with no base change).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace IntermediateField
open scoped TensorProduct

namespace DeJongAlterations.StableModification.Perfection

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Geometry Geometry.NormalizationInExtension DeJong

section FunctionField

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f]
  {M : Type u} [Field M] [Algebra X.functionField M] [Algebra Y.functionField M]
  (hM : ∀ c, algebraMap Y.functionField M c =
    algebraMap X.functionField M ((functionFieldMap f).hom c))
include hM

theorem isScalarTower_ambient :
    letI := FiniteBirationalNormal.functionFieldAlgebra f
    IsScalarTower Y.functionField X.functionField M := by
  let := FiniteBirationalNormal.functionFieldAlgebra f
  exact IsScalarTower.of_algebraMap_eq hM

omit hM in
/-- The function field extension `K(X) / K(Y)` is geometrically reduced when the generic fibre is
geometrically integral. -/
theorem isGeometricallyReduced_functionField
    (hgi : GeometricallyIntegral (f.fiberToSpecResidueField (genericPoint Y))) :
    letI := FiniteBirationalNormal.functionFieldAlgebra f
    Algebra.IsGeometricallyReduced Y.functionField X.functionField := by
  let := FiniteBirationalNormal.functionFieldAlgebra f
  exact isGeometricallyReduced_of_forall_isDomain fun K' _ _ =>
    isDomain_functionField_tensorProduct_of_genericFiber f hgi K'

/-- A purely inseparable extension of `K(Y)` inside `M` is linearly disjoint from `K(X)`. -/
theorem linearDisjoint_fieldRange
    (hgi : GeometricallyIntegral (f.fiberToSpecResidueField (genericPoint Y)))
    (E : IntermediateField Y.functionField M) [IsPurelyInseparable Y.functionField E] :
    letI := FiniteBirationalNormal.functionFieldAlgebra f
    haveI := isScalarTower_ambient f hM
    E.LinearDisjoint (IsScalarTower.toAlgHom Y.functionField X.functionField M).fieldRange := by
  let := FiniteBirationalNormal.functionFieldAlgebra f
  have := isScalarTower_ambient f hM
  have := isGeometricallyReduced_functionField f hgi
  have : Algebra.IsGeometricallyReduced Y.functionField
      (IsScalarTower.toAlgHom Y.functionField X.functionField M).fieldRange :=
    Algebra.IsGeometricallyReduced.of_injective (AlgHom.equivFieldRange _).symm.toAlgHom
      (AlgHom.equivFieldRange _).symm.injective
  exact linearDisjoint_of_isGeometricallyReduced Y.functionField E _

/-- The fraction field of `A_U` is linearly disjoint from the perfect closure of `K(Y)`. -/
theorem linearDisjoint_fracField_chartAlgebra
    (hgi : GeometricallyIntegral (f.fiberToSpecResidueField (genericPoint Y)))
    (U : NonemptyAffineOpen X) :
    (perfectClosure Y.functionField M).LinearDisjoint
      (fracField (chartAlgebra Y.functionField M U)) := by
  let := FiniteBirationalNormal.functionFieldAlgebra f
  have := isScalarTower_ambient f hM
  have hld := linearDisjoint_fieldRange f hM hgi (perfectClosure Y.functionField M)
  refine hld.of_le_right ?_
  rw [fracField, adjoin_le_iff]
  intro m hm
  exact chartAlgebra_le_of_subring U
    (IsScalarTower.toAlgHom Y.functionField X.functionField M).fieldRange.toSubfield.toSubring
    (fun c =>
      (IsScalarTower.toAlgHom Y.functionField X.functionField M).fieldRange.algebraMap_mem c)
    (fun a => ⟨_, rfl⟩) hm

/-- The local ring of a point of `X` over the generic point of `Y` contains `K(Y)`. -/
theorem algebraMap_mem_stalkToAmbientBase_range {x : X} (hx : f x = genericPoint Y)
    (c : Y.functionField) :
    algebraMap Y.functionField M c ∈ (stalkToAmbientBase M x).range := by
  obtain ⟨c', rfl⟩ := (algebraMap_stalk_bijective_of_eq_genericPoint hx).2 c
  refine ⟨(f.stalkMap x).hom c', ?_⟩
  have h := congrArg (fun φ => φ.hom c') (functionFieldMap_stalk f x)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  rw [hM]
  simp only [stalkToAmbientBase, RingHom.comp_apply]
  rw [← h]

/-- `A_U` is finitely generated over `K(Y)`: `Γ(X, U)` is finitely generated over the ground
field `k`, which maps to `K(Y)`. -/
theorem finiteType_chartAlgebra {k : Type u} [Field k] (pY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType (f ≫ pY)] (U : NonemptyAffineOpen X) :
    Algebra.FiniteType Y.functionField (chartAlgebra Y.functionField M U) := by
  classical
  let := (NormalizationFinite.affineCoefficientMap (f ≫ pY) ⟨U.1.1, U.1.2⟩).toAlgebra
  have : Algebra.FiniteType k Γ(X, U.1.1) :=
    NormalizationFinite.affineSections_finiteType (f ≫ pY) ⟨U.1.1, U.1.2⟩
  obtain ⟨G, hG⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra k Γ(X, U.1.1)).FG)
  have hk : ∀ c : k, sectionsToField M U (algebraMap k Γ(X, U.1.1) c) ∈
      (algebraMap Y.functionField M).range := by
    intro c
    let := SeparableGenericSmoothness.functionFieldAlgebra pY
    let := SeparableGenericSmoothness.functionFieldAlgebra (f ≫ pY)
    let := FiniteBirationalNormal.functionFieldAlgebra f
    have t1 := RationalCoordinateMap.functionFieldScalarTower (f ≫ pY) ⟨U.1.1, U.1.2⟩
    have t2 := VarietyFunctionFieldDimension.functionFieldScalarTower pY f
    refine ⟨algebraMap k Y.functionField c, ?_⟩
    rw [hM]
    simp only [sectionsToField, RingHom.comp_apply]
    congr 1
    have e1 : algebraMap k X.functionField c =
        algebraMap Γ(X, U.1.1) X.functionField (algebraMap k Γ(X, U.1.1) c) :=
      IsScalarTower.algebraMap_apply k Γ(X, U.1.1) X.functionField c
    have e2 : algebraMap k X.functionField c =
        algebraMap Y.functionField X.functionField (algebraMap k Y.functionField c) :=
      IsScalarTower.algebraMap_apply k Y.functionField X.functionField c
    exact e2.symm.trans e1
  have heq : chartAlgebra Y.functionField M U =
      Algebra.adjoin Y.functionField ((G.image (sectionsToField M U) : Finset M) : Set M) := by
    apply le_antisymm
    · rw [chartAlgebra, Algebra.adjoin_le_iff]
      rintro _ ⟨a, rfl⟩
      have ha : a ∈ Algebra.adjoin k (G : Set Γ(X, U.1.1)) := hG ▸ trivial
      induction ha using Algebra.adjoin_induction with
      | mem a ha =>
        refine Algebra.subset_adjoin ?_
        rw [Finset.coe_image]
        exact ⟨a, ha, rfl⟩
      | algebraMap c =>
        obtain ⟨d, hd⟩ := hk c
        rw [← hd]
        exact Subalgebra.algebraMap_mem _ d
      | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
      | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
    · refine Algebra.adjoin_mono ?_
      intro m hm
      rw [Finset.coe_image] at hm
      obtain ⟨a, -, rfl⟩ := hm
      exact ⟨a, rfl⟩
  have hfg : (chartAlgebra Y.functionField M U).FG := by
    rw [heq]
    exact Subalgebra.fg_adjoin_finset _
  exact (Subalgebra.fg_iff_finiteType _).1 hfg

/-- `A_U` has dimension at most one: its transcendence degree over `K(Y)` is at most that of
`K(X)`, the dimension of the generic fibre. -/
theorem dimensionLEOne_chartAlgebra [Algebra.IsAlgebraic X.functionField M]
    [LocallyOfFiniteType f] (hdim : topologicalKrullDim (f.fiber (genericPoint Y)) ≤ 1)
    (U : NonemptyAffineOpen X)
    [Algebra.FiniteType Y.functionField (chartAlgebra Y.functionField M U)] :
    Ring.DimensionLEOne (chartAlgebra Y.functionField M U) := by
  let := FiniteBirationalNormal.functionFieldAlgebra f
  have := isScalarTower_ambient f hM
  set A := chartAlgebra Y.functionField M U
  have htrKX : Algebra.trdeg Y.functionField X.functionField ≤ 1 :=
    SteinGenericFiber.trdeg_le_one f hdim
  have : FaithfulSMul Y.functionField X.functionField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (algebraMap Y.functionField X.functionField).injective
  have : FaithfulSMul X.functionField M :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap X.functionField M).injective
  have hadd := trdeg_add_eq Y.functionField X.functionField (A := M)
  rw [trdeg_eq_zero (R := X.functionField) (A := M), add_zero] at hadd
  have htrA : Algebra.trdeg Y.functionField A ≤ 1 :=
    (trdeg_le_of_injective A.val Subtype.val_injective).trans (hadd ▸ htrKX)
  obtain ⟨d, hd, htrd⟩ :=
    Algebra.FunctionFieldDimension.exists_dimension_and_trdeg Y.functionField A (FractionRing A)
  have : FaithfulSMul A (FractionRing A) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective A _)
  have : Algebra.IsAlgebraic A (FractionRing A) :=
    IsLocalization.isAlgebraic (FractionRing A) (nonZeroDivisors A)
  have h2 := Algebra.FunctionFieldDimension.trdeg_eq_of_isAlgebraic Y.functionField A
    (FractionRing A)
  have hd1 : (d : Cardinal) ≤ 1 := by rw [← htrd, ← h2]; exact htrA
  have hd1' : d ≤ 1 := by exact_mod_cast hd1
  have : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.mpr (by rw [hd]; exact_mod_cast hd1')
  exact ⟨fun hne hp => Ideal.IsPrime.isMaximal_of_ne_bot hp hne⟩

end FunctionField

section Finiteness

/-- A quasi-compact scheme is covered by the nonempty affine charts of finitely many points. -/
theorem exists_finset_chart_cover (X : Scheme.{u}) [CompactSpace X] :
    ∃ (t : Finset X) (V : X → NonemptyAffineOpen X), (∀ x, x ∈ (V x).1.1) ∧
      ∀ x, ∃ y ∈ t, x ∈ (V y).1.1 := by
  have hex : ∀ x : X, ∃ V : NonemptyAffineOpen X, x ∈ V.1.1 := fun x => by
    obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤)
      (by trivial)
    exact ⟨⟨⟨W, hW⟩, ⟨⟨x, hxW⟩⟩⟩, hxW⟩
  choose V hV using hex
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => ((V x).1.1 : Set X))
    (fun x => (V x).1.1.isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x, hV x⟩)
  refine ⟨t, V, hV, fun x => ?_⟩
  have := ht (Set.mem_univ x)
  simp only [Set.mem_iUnion] at this
  obtain ⟨y, hy, hxy⟩ := this
  exact ⟨y, hy, hxy⟩

/-- The points of a closed subset `W ⊆ X` not containing the generic point and lying over the
generic point of `Y` form a finite set, when the generic fibre is a curve. -/
theorem finite_boundary_genericFiber {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    [IsDominant f] [QuasiCompact f] [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim (f.fiber (genericPoint Y)) ≤ 1) (W : Closeds X)
    (hW : genericPoint X ∉ W) : {x : X | x ∈ W ∧ f x = genericPoint Y}.Finite := by
  have : IsIntegral (f.fiber (genericPoint Y)) := GenericFiberIntegral.genericFiber_isIntegral f
  have : LocallyOfFiniteType (f.fiberToSpecResidueField (genericPoint Y)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : IsLocallyNoetherian (f.fiber (genericPoint Y)) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField (genericPoint Y))
  have : AlgebraicGeometry.IsNoetherian (f.fiber (genericPoint Y)) := {}
  let W' : Closeds (f.fiber (genericPoint Y)) := W.preimage (f.fiberι (genericPoint Y)).continuous
  let D := Scheme.IdealSheafData.vanishingIdeal W'
  have hDsupp : D.support = W' :=
    SetLike.coe_injective (Scheme.IdealSheafData.coe_support_vanishingIdeal _)
  have hD : D.support ≠ ⊤ := by
    rw [hDsupp]
    intro h
    obtain ⟨z₀, hz₀⟩ := exists_fiberι_eq_genericPoint f
    apply hW
    rw [← hz₀]
    change z₀ ∈ (W' : Set _)
    rw [h]
    trivial
  have hfin := CurveBoundary.finite_support hdim D hD
  rw [hDsupp] at hfin
  refine (hfin.image (f.fiberι (genericPoint Y))).subset ?_
  rintro x ⟨hxW, hxη⟩
  have : x ∈ Set.range (f.fiberι (genericPoint Y)) := by
    rw [Scheme.Hom.range_fiberι]
    exact hxη
  obtain ⟨z, rfl⟩ := this
  exact ⟨z, hxW, rfl⟩

end Finiteness

section Construction

variable {k : Type u} [Field k]

/-- **The construction for a given field `E`.** Let `E ⊆ Ω` be finite over `K(Y)` such that the
normalizations `B_E(A_U)` are smooth over `E` on a cover of `X` by charts, and such that at every
point `x` of `W` over the generic point of `Y` the residue fields of `B_E(A_U)` (for a chart
`U ∋ x`) at the maximal ideals over the ideal of `x` are separable over `E`. Then the
normalizations `Y₁` of `Y` in `E` and `X₁` of `X` in `K(X)(E)`, with Codex's Stein normalization
factor `f₁ : X₁ ⟶ Y₁`, satisfy the conclusion of the smoothing statement. -/
theorem exists_smoothing_of_field {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsVariety p]
    (hp : IsProjectiveOver p)
    {Y : Scheme.{u}} (pY : Y ⟶ Spec (.of k)) [IsVariety pY] (hYp : IsProjectiveOver pY)
    (f : X ⟶ Y) [IsDominant f] (hfac : f ≫ pY = p)
    (hgi : GeometricallyIntegral (f.fiberToSpecResidueField (genericPoint Y))) (W : Closeds X)
    {M : Type u} [Field M] [Algebra X.functionField M] [Algebra Y.functionField M]
    (hM : ∀ c, algebraMap Y.functionField M c =
      algebraMap X.functionField M ((functionFieldMap f).hom c))
    (E : IntermediateField Y.functionField M) [FiniteDimensional Y.functionField E]
    (hEΩ : E ≤ perfectClosure Y.functionField M)
    (hsmE : ∀ x : X, ∃ U : NonemptyAffineOpen X, x ∈ U.1.1 ∧
      Algebra.Smooth E (Perfection.normalization (chartAlgebra Y.functionField M U) E))
    (hsepE : ∀ x : X, x ∈ W → f x = genericPoint Y →
      ∃ (U : NonemptyAffineOpen X) (hU : x ∈ U.1.1)
        (hK : ∀ c, algebraMap Y.functionField M c ∈ (stalkToAmbientBase M x).range),
        (chartIdeal Y.functionField U hU hK).IsMaximal ∧
        ∀ P : Ideal (normalizationImage (chartAlgebra Y.functionField M U) E), P.IsMaximal →
          P.comap (toNormalizationImage (chartAlgebra Y.functionField M U) E) =
            chartIdeal Y.functionField U hU hK →
          Algebra.IsSeparable E (normalizationImage (chartAlgebra Y.functionField M U) E ⧸ P)) :
    ∃ (X₁ : Scheme.{u}) (φ : X₁ ⟶ X) (_ : IsVariety (φ ≫ p)) (Y₁ : Scheme.{u}) (ψ : Y₁ ⟶ Y)
      (_ : IsVariety (ψ ≫ pY)) (f₁ : X₁ ⟶ Y₁),
      IsAlteration φ ∧ IsProjectiveOver (φ ≫ p) ∧
      IsAlteration ψ ∧ IsNormalScheme Y₁ ∧ IsProjectiveOver (ψ ≫ pY) ∧
      f₁ ≫ ψ = φ ≫ f ∧ IsDominant f₁ ∧
      Smooth (f₁.fiberToSpecResidueField (genericPoint Y₁)) ∧
      GeometricallyIntegral (f₁.fiberToSpecResidueField (genericPoint Y₁)) ∧
      SeparableResidueFieldsAlong f₁ (genericPoint Y₁) (φ ⁻¹' (W : Set X)) := by
  have : LocallyOfFiniteType f := by
    have : LocallyOfFiniteType (f ≫ pY) := by rw [hfac]; infer_instance
    exact locallyOfFiniteType_of_comp f pY
  let := FiniteBirationalNormal.functionFieldAlgebra f
  have := isScalarTower_ambient f hM
  have hEalg : ∀ e ∈ E, IsIntegral Y.functionField e := forall_isIntegral_of_isAlgebraic E
  have : IsPurelyInseparable Y.functionField E := (le_perfectClosure_iff _ M E).1 hEΩ
  set L : IntermediateField X.functionField M := adjoin X.functionField (E : Set M) with hL
  have : FiniteDimensional X.functionField L := finiteDimensional_adjoin_of_finiteDimensional E
  have : IsPurelyInseparable X.functionField L :=
    isPurelyInseparable_adjoin_of_le_perfectClosure E hEΩ
  have : IsFinite (normalizationStructure X L) := normalizationStructure_isFinite L p
  have : IsFinite (normalizationStructure Y E) := normalizationStructure_isFinite E pY
  have hX₁v : IsVariety (normalizationStructure X L ≫ p) := normalization_isVariety p L
  have hY₁v : IsVariety (normalizationStructure Y E ≫ pY) := normalization_isVariety pY E
  have : AlgebraicGeometry.IsNoetherian (NormalizationInExtension.normalization X L) :=
    ProjectiveCurveFibration.variety_isNoetherian (normalizationStructure X L ≫ p)
  have hX₁n : IsNormalScheme (NormalizationInExtension.normalization X L) :=
    NormalizationInExtension.normalization_isNormalScheme L
  set eX := normalizationFunctionFieldEquiv (X := X) L
  set eY := normalizationFunctionFieldEquiv (X := Y) E
  -- the field embedding `E ⊆ L ≅ K(X₁)`
  let σ : letI := FiniteBirationalNormal.functionFieldAlgebra (normalizationStructure X L ≫ f)
      E →ₐ[Y.functionField] (NormalizationInExtension.normalization X L).functionField :=
    letI := FiniteBirationalNormal.functionFieldAlgebra (normalizationStructure X L ≫ f)
    { eX.symm.toRingHom.comp (toAdjoin (F := X.functionField) E) with
      commutes' := fun c => by
        apply eX.injective
        change eX (eX.symm (toAdjoin E (algebraMap Y.functionField E c))) =
          eX ((functionFieldMap (normalizationStructure X L ≫ f)).hom c)
        rw [RingEquiv.apply_symm_apply, functionFieldMap_comp]
        have h : eX ((functionFieldMap (normalizationStructure X L)).hom
            ((functionFieldMap f).hom c)) =
            algebraMap X.functionField L ((functionFieldMap f).hom c) :=
          congrArg (fun φ : X.functionField →+* L => φ ((functionFieldMap f).hom c))
            (normalizationFunctionFieldEquiv_comp (X := X) L)
        change _ = eX ((functionFieldMap (normalizationStructure X L)).hom
          ((functionFieldMap f).hom c))
        rw [h]
        apply Subtype.ext
        change algebraMap Y.functionField M c = algebraMap X.functionField M _
        exact hM c }
  let g := SteinNormalizationFactor.factor (normalizationStructure X L ≫ f) E σ pY hX₁n
  have hgψ : g ≫ normalizationStructure Y E = normalizationStructure X L ≫ f :=
    SteinNormalizationFactor.factor_structure _ E σ pY hX₁n
  have : IsDominant g := SteinNormalizationFactor.factor_isDominant _ E σ pY hX₁n
  have hgff := SteinNormalizationFactor.factor_functionFieldMap _ E σ pY hX₁n
  have hg : ∀ y, ((eX ((functionFieldMap g).hom y) : L) : M) = (eY y : M) := by
    intro y
    rw [hgff]
    change ((eX (eX.symm (toAdjoin E (eY y))) : L) : M) = _
    rw [RingEquiv.apply_symm_apply]
    rfl
  refine ⟨_, normalizationStructure X L, hX₁v, _, normalizationStructure Y E, hY₁v, g,
    normalizationStructure_isAlteration L p,
    FiniteProjective.isProjectiveOver_comp_of_isFinite p hp _,
    normalizationStructure_isAlteration E pY,
    NormalizationInExtension.normalization_isNormalScheme E,
    FiniteProjective.isProjectiveOver_comp_of_isFinite pY hYp _, hgψ, inferInstance, ?_, ?_, ?_⟩
  · -- smoothness of the generic fibre
    have : LocallyOfFiniteType g := by
      have : LocallyOfFiniteType (g ≫ normalizationStructure Y E) := by
        rw [hgψ]
        infer_instance
      exact locallyOfFiniteType_of_comp g (normalizationStructure Y E)
    have : LocallyOfFiniteType (g.fiberToSpecResidueField (genericPoint _)) :=
      MorphismProperty.pullback_snd _ _ inferInstance
    apply smooth_genericFiber_of_formallySmooth g
    intro x₁ hx₁
    obtain ⟨U, hU, hsm⟩ := hsmE (normalizationStructure X L x₁)
    exact formallySmooth_stalkMap_of_smooth L E eY g hg hL hEalg x₁ hx₁ U hU
  · -- geometric integrality of the generic fibre
    apply SteinGeometricIntegrality.genericFiber_geometricallyIntegral_of_field g
    let : Algebra E L := (toAdjoin (F := X.functionField) E).toAlgebra
    have hld := linearDisjoint_fieldRange f hM hgi E
    have hGI : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap E L))) :=
      geometricallyIntegral_specMap_of_forall_isDomain fun E' _ _ =>
        isDomain_adjoin_tensorProduct E hld
          (fun K' _ _ => isDomain_functionField_tensorProduct_of_genericFiber f hgi K') E'
    have hfm : functionFieldMap g = CommRingCat.ofHom eY.toRingHom ≫
        CommRingCat.ofHom (algebraMap E L) ≫ CommRingCat.ofHom eX.symm.toRingHom := by
      apply CommRingCat.hom_ext
      rw [hgff]
      rfl
    rw [hfm, Spec.map_comp, Spec.map_comp]
    have : IsIso (CommRingCat.ofHom eY.toRingHom) := eY.toCommRingCatIso.isIso_hom
    have : IsIso (CommRingCat.ofHom eX.symm.toRingHom) := eX.symm.toCommRingCatIso.isIso_hom
    rw [MorphismProperty.cancel_right_of_respectsIso @GeometricallyIntegral,
      MorphismProperty.cancel_left_of_respectsIso @GeometricallyIntegral]
    exact hGI
  · -- separable residue fields along `φ⁻¹ W`
    apply separableResidueFieldsAlong_of_isSeparable g
    intro x₁ hx₁ hxW
    have hfx : f (normalizationStructure X L x₁) = genericPoint Y := by
      rw [← Scheme.Hom.comp_apply, ← hgψ, Scheme.Hom.comp_apply, hx₁]
      exact genericPoint_map_of_isDominant (normalizationStructure Y E)
    obtain ⟨U, hU, hK, hmax, hsep⟩ := hsepE _ hxW hfx
    exact isSeparable_residueFieldMap_of_isSeparable L E eY g hg hL hEalg x₁ hx₁ U hU hK hmax hsep

end Construction

/-- **PL, global form** (`thm:sm-dj-perfection-global`), over an arbitrary ground field `k`. Let
`f : X ⟶ Y` be a proper dominant morphism of normal projective `k`-varieties whose generic fibre
is geometrically integral of dimension one, and `W ⊆ X` closed, not containing the generic point.
Then there are alterations `φ : X₁ ⟶ X`, `ψ : Y₁ ⟶ Y` of projective varieties, `Y₁` normal, and a
dominant `f₁ : X₁ ⟶ Y₁` over `f` whose generic fibre is smooth and geometrically integral, with
separable residue fields along `φ⁻¹ W`. Here `Y₁` is the normalization of `Y` in a finite purely
inseparable extension `E` of `K(Y)`, `X₁` the normalization of `X` in `K(X)(E)`, and `f₁` Codex's
Stein normalization factor (`exists_smoothing_of_field`). -/
theorem exists_purelyInseparableSmoothing {k : Type u} [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (.of k)) (hpv : IsVariety p) (hp : IsProjectiveOver p) (_hXn : IsNormalScheme X)
    (Y : Scheme.{u}) (pY : Y ⟶ Spec (.of k)) (hYv : IsVariety pY) (hYp : IsProjectiveOver pY)
    (_hYn : IsNormalScheme Y) (f : X ⟶ Y) (hfac : f ≫ pY = p) (hfdom : IsDominant f)
    (hfprop : IsProper f)
    (hgi : GeometricallyIntegral (f.fiberToSpecResidueField (genericPoint Y)))
    (hdimf : topologicalKrullDim (f.fiber (genericPoint Y)) = 1)
    (W : Closeds X) (hW : genericPoint X ∉ W) :
    ∃ (X₁ : Scheme.{u}) (φ : X₁ ⟶ X) (_ : IsVariety (φ ≫ p)) (Y₁ : Scheme.{u}) (ψ : Y₁ ⟶ Y)
      (_ : IsVariety (ψ ≫ pY)) (f₁ : X₁ ⟶ Y₁),
      IsAlteration φ ∧ IsProjectiveOver (φ ≫ p) ∧
      IsAlteration ψ ∧ IsNormalScheme Y₁ ∧ IsProjectiveOver (ψ ≫ pY) ∧
      f₁ ≫ ψ = φ ≫ f ∧ IsDominant f₁ ∧
      Smooth (f₁.fiberToSpecResidueField (genericPoint Y₁)) ∧
      GeometricallyIntegral (f₁.fiberToSpecResidueField (genericPoint Y₁)) ∧
      SeparableResidueFieldsAlong f₁ (genericPoint Y₁) (φ ⁻¹' (W : Set X)) := by
  have : LocallyOfFiniteType f := by
    have : LocallyOfFiniteType (f ≫ pY) := by rw [hfac]; infer_instance
    exact locallyOfFiniteType_of_comp f pY
  have : AlgebraicGeometry.IsNoetherian X := ProjectiveCurveFibration.variety_isNoetherian p
  let M := AlgebraicClosure X.functionField
  let : Algebra Y.functionField M :=
    ((algebraMap X.functionField M).comp (functionFieldMap f).hom).toAlgebra
  have hM : ∀ c, algebraMap Y.functionField M c =
      algebraMap X.functionField M ((functionFieldMap f).hom c) := fun _ => rfl
  set Ω := perfectClosure Y.functionField M
  have hld := linearDisjoint_fracField_chartAlgebra f hM hgi
  have hpY : LocallyOfFiniteType (f ≫ pY) := by rw [hfac]; infer_instance
  have hft : ∀ U, Algebra.FiniteType Y.functionField (chartAlgebra Y.functionField M U) :=
    finiteType_chartAlgebra f hM pY
  have hdimA : ∀ U, Ring.DimensionLEOne (chartAlgebra Y.functionField M U) := fun U => by
    have := hft U
    exact dimensionLEOne_chartAlgebra f hM hdimf.le U
  obtain ⟨t, V, hV, ht⟩ := exists_finset_chart_cover X
  have hfinW := finite_boundary_genericFiber f hdimf.le W hW
  have hKx : ∀ x : X, f x = genericPoint Y → ∀ c : Y.functionField,
      algebraMap Y.functionField M c ∈ (stalkToAmbientBase M x).range :=
    fun x hx c => algebraMap_mem_stalkToAmbientBase_range f hM hx c
  have hmaxI : ∀ x : X, (hx : x ∈ W ∧ f x = genericPoint Y) →
      (chartIdeal Y.functionField (V x) (hV x) (hKx x hx.2)).IsMaximal := by
    intro x hx
    have := hdimA (V x)
    have hxη : x ≠ genericPoint X := fun h => hW (h ▸ hx.1)
    exact Ring.DimensionLEOne.maximalOfPrime (chartIdeal_ne_bot (V x) (hV x) _ hxη)
      inferInstance
  -- the fields making the charts smooth
  have hsm : ∀ y : X, ∃ E₀ : IntermediateField Y.functionField M, E₀ ≤ Ω ∧
      FiniteDimensional Y.functionField E₀ ∧ ∀ E : IntermediateField Y.functionField M,
        E₀ ≤ E → E ≤ Ω →
          Algebra.Smooth E (Perfection.normalization (chartAlgebra Y.functionField M (V y)) E) := by
    intro y
    have := hft (V y)
    have := hdimA (V y)
    obtain ⟨E₀, h1, h2, h3⟩ := exists_smooth_normalization (chartAlgebra Y.functionField M (V y))
      Ω (hld (V y))
    exact ⟨E₀, h1, h2, fun E hE hEΩ => (h3 E hE hEΩ).1⟩
  choose E₀ hE₀Ω hE₀fin hE₀sm using hsm
  -- the fields making the boundary residue fields separable
  have hsep : ∀ x : hfinW.toFinset, ∃ E₂ : IntermediateField Y.functionField M, E₂ ≤ Ω ∧
      FiniteDimensional Y.functionField E₂ ∧ ∀ E : IntermediateField Y.functionField M,
        E₂ ≤ E → E ≤ Ω →
        ∀ P : Ideal (normalizationImage (chartAlgebra Y.functionField M (V x)) E), P.IsMaximal →
          P.comap (toNormalizationImage (chartAlgebra Y.functionField M (V x)) E) =
            chartIdeal Y.functionField (V x) (hV x)
              (hKx x ((Set.Finite.mem_toFinset _).1 x.2).2) →
          Algebra.IsSeparable E
            (normalizationImage (chartAlgebra Y.functionField M (V x)) E ⧸ P) := by
    intro x
    have hx := (Set.Finite.mem_toFinset _).1 x.2
    have := hft (V x)
    obtain ⟨E₂, h1, h2, h3⟩ := exists_isSeparable_quotient (chartAlgebra Y.functionField M (V x))
      Ω (hld (V x)) {chartIdeal Y.functionField (V x) (hV x) (hKx x hx.2)}
      (fun P hP => by rw [Finset.mem_singleton] at hP; rw [hP]; exact hmaxI x hx)
    exact ⟨E₂, h1, h2, fun E hE hEΩ P hP hPc =>
      h3 E hE hEΩ P hP (by rw [hPc]; exact Finset.mem_singleton_self _)⟩
  choose E₂ hE₂Ω hE₂fin hE₂sep using hsep
  let E : IntermediateField Y.functionField M := (⨆ y ∈ t, E₀ y) ⊔ ⨆ x, E₂ x
  have hEΩ : E ≤ Ω := sup_le (iSup₂_le fun y _ => hE₀Ω y) (iSup_le hE₂Ω)
  have : FiniteDimensional Y.functionField E := by
    have := hE₀fin
    have := hE₂fin
    infer_instance
  refine exists_smoothing_of_field p hp pY hYp f hfac hgi W hM E hEΩ ?_ ?_
  · intro x
    obtain ⟨y, hy, hxy⟩ := ht x
    exact ⟨V y, hxy, hE₀sm y E (le_sup_of_le_left (le_iSup₂_of_le y hy le_rfl)) hEΩ⟩
  · intro x hxW hfx
    have hxmem : x ∈ hfinW.toFinset := (Set.Finite.mem_toFinset _).2 ⟨hxW, hfx⟩
    exact ⟨V x, hV x, hKx x hfx, hmaxI x ⟨hxW, hfx⟩, fun P hP hPc =>
      hE₂sep ⟨x, hxmem⟩ E (le_sup_of_le_right (le_iSup_of_le ⟨x, hxmem⟩ le_rfl)) hEΩ P hP hPc⟩

/-- **The smoothing statement** `DeJong.PurelyInseparableSmoothing k` of `DeJong/Fibration.lean`
(`def:sm-dj-purely-inseparable-smoothing`) holds for every algebraically closed field `k`
(`exists_purelyInseparableSmoothing`; algebraic closedness is not used). -/
theorem purelyInseparableSmoothing (k : Type u) [Field k] [IsAlgClosed k] :
    PurelyInseparableSmoothing k :=
  fun X p hpv hp hXn Y pY hYv hYp hYn f hfac hfdom hfprop hgi hdimf W hW =>
    exists_purelyInseparableSmoothing X p hpv hp hXn Y pY hYv hYp hYn f hfac hfdom hfprop hgi
      hdimf W hW

/-- **FIB** (`TemkinReadyFibration k`) over every algebraically closed field, from
`temkinReadyFibration_of_purelyInseparableSmoothing` of `DeJong/Fibration.lean`. -/
theorem temkinReadyFibration (k : Type u) [Field k] [IsAlgClosed k] : TemkinReadyFibration k :=
  temkinReadyFibration_of_purelyInseparableSmoothing (purelyInseparableSmoothing k)

end DeJongAlterations.StableModification.Perfection

end
