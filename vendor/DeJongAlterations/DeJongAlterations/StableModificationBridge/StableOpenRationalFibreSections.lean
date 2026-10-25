/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.StableModificationBridge.StableMarkedComponentDegree
import DeJongAlterations.StableModificationBridge.StableOpenMarkedSupportCount
import DeJongAlterations.StableModificationBridge.StableOpenOriginalPointFactors
import DeJongAlterations.StableModificationBridge.OriginalCanonicalGoodSection
import DeJongAlterations.Geometry.ClosedFibreCanonicalDegree
import DeJongAlterations.Geometry.ClosedFibreCanonicalProjective
import DeJongAlterations.Geometry.CurveFibrationMarkedOpenSmooth

/-! ONE original marked dualizing bundle supplies actual good sections on every
original closed beta fibre above the given rational stable point. Blueprint:
`sm-bridge-stable-open-rational-fibre-sections.tex`. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace DeJongAlterations.StableModificationBridge.StableOpenRationalFibreSections
open StableModification StableModification.Projectivity Cohomology CurvesField
open StableProjectivityClosedFibres
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

/-- The SAME original Cartier marking and global omega(D') line bundle work at
EVERY original closed point above the given rational stable fibre. All native
component degree, residue no-contraction and actual section inputs are derived. -/
theorem exists_markedLineBundle_fibreSections {K : Type u} [Field K] [IsAlgClosed K]
    {V : Scheme.{u}} (pV : V ⟶ Spec (.of K)) [IsVariety pV] (hV : IsNormalScheme V)
    {C : Scheme.{u}} (q : C ⟶ V) (hq : DeJong.IsRelativelyProjective pV q)
    {X : Scheme.{u}} (β : X ⟶ C) (hβ : DeJong.IsRelativelyProjective (q ≫ pV) β)
    (D' : X.IdealSheafData) (hss : DeJong.IsSemistablePair (β ≫ q) D')
    (hsm : Smooth ((β ≫ q).fiberToSpecResidueField (genericPoint V)))
    (a : Spec (.of K) ⟶ V) (ha : a ≫ pV = 𝟙 _)
    (hnum : Global.NumericallyStableFibre β q D' a) (hno : Global.NoContractedClopen β q a) :
    letI : DeJong.IsNodalCurve (β ≫ q) := hss.nodal
    ∃ E : LocalEquations X,
      (∀ i, ∃ h : IsAffineOpen (E.U i), IsRegular (E.f i) ∧
        D'.ideal ⟨E.U i, h⟩ = Ideal.span {E.f i}) ∧
      (∀ x : X, x ∈ E.canonicalSection.nonvanishingLocus ↔ x ∉ (D'.support : Set X)) ∧
      ∃ L : LineBundleData X,
        Nonempty (L.twist (unitModule X) 1 ≅ E.toLineBundleData.twist (Omega.dualizingSheaf (β ≫ q)) 1) ∧
        ∀ y : C, IsClosed ({y} : Set C) → q y = a (IsLocalRing.closedPoint K) →
          HasFiberSection β L y := by
  let f := β ≫ q
  let : IsProper q := hq.isProper
  let : IsProper β := hβ.isProper
  let : IsProper f := inferInstance
  let : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian pV
  let : DeJong.IsNodalCurve f := hss.nodal
  let : IsSeparated (f ≫ pV) := inferInstance
  let : IsAffineHom (pullback.diagonal (terminal.from X)) :=
    Ample.isAffineHom_diagonal_of_isSeparated (f ≫ pV)
  let : Smooth (f.fiberToSpecResidueField (genericPoint V)) := hsm
  have hgen : ∀ x : X, f x = genericPoint V → DeJong.IsSmoothAt f x := by
    intro x hx
    exact (DeJong.isSmoothAt_iff_mem_smoothLocus f x).mpr
      (Geometry.CurveFibrationMarkedOpen.genericFiber_le_smoothLocus f x hx)
  obtain ⟨E, hEi, hEs, L, ⟨e⟩⟩ := StableMarkedDualizingBundle.exists_markedDualizingBundle
    f hV hgen D' hss
  have hEi' : ∀ i, ∃ h : IsAffineOpen (E.U i),
      D'.ideal ⟨E.U i, h⟩ = Ideal.span {E.f i} := by
    intro i
    obtain ⟨h, _, hi⟩ := hEi i
    exact ⟨h, hi⟩
  have hn := Global.isNumericallyStableAt_of_numericallyStableFibre β q D' a
    (fun x => congrArg a (Subsingleton.elim x (IsLocalRing.closedPoint K))) hnum
  let hloc := locallyRelativelyProjective_of_isRelativelyProjective hβ
  refine ⟨E, hEi, hEs, L, ⟨e⟩, ?_⟩
  intro y hy hya
  let a' := Geometry.ClosedFibreComponent.basePoint q y
  let hpT := isProjectiveOver_fiber_of_locallyRelativelyProjective hloc y
  let : IsProper (β.fiberToSpecResidueField y) := hpT.isProper
  let : CompactSpace (β.fiber y) := Ample.compactSpace_of_quasiCompact (β.fiberToSpecResidueField y)
  let : IsAffineHom (pullback.diagonal (terminal.from (β.fiber y))) :=
    Ample.isAffineHom_diagonal_of_isSeparated (β.fiberToSpecResidueField y)
  let : CompactSpace (pullback (C := Scheme.{u}) f a') :=
    Ample.compactSpace_of_quasiCompact (pullback.snd f a')
  let : IsAffineHom (pullback.diagonal (terminal.from (pullback (C := Scheme.{u}) f a'))) :=
    Ample.isAffineHom_diagonal_of_isSeparated (pullback.snd f a')
  have : IsAlgClosed (IsLocalRing.ResidueField (C.presheaf.stalk y)) :=
    isAlgClosed_residueField_of_isClosed (q ≫ pV) y hy
  have : IsAlgClosed (C.residueField y) :=
    isAlgClosed_residueField_of_isClosed (q ≫ pV) y hy
  have hnum' : Global.NumericallyStableFibre β q D' a' := by
    apply hn (C.residueField y) a'
    intro x
    change q (C.fromSpecResidueField y x) = a (IsLocalRing.closedPoint K)
    rw [Scheme.fromSpecResidueField_apply]
    exact hya
  have hno' : Global.NoContractedClopen β q a' :=
    StableOpenOriginalPointFactors.noContractedClopen_residue_of_rational pV β q a ha hno y hy hya
  have hpos : PositiveCanonicalComponents (β.fiberToSpecResidueField y) hpT
      (L.pullback (β.fiberι y)) := by
    change ∀ η ∈ genericPoints (β.fiber y), ¬ IsClosed ({η} : Set (β.fiber y)) → _
    intro η _ hηnc
    let v := Geometry.ClosedFibreComponent.fibreInTotalCurve β q y η
    have hv : v ∈ genericPoints (pullback (C := Scheme.{u}) f a') :=
      Geometry.ClosedFibreComponent.image_mem_genericPoints β q y
        (Omega.ComponentDegree.topologicalKrullDim_fibre_le_one f a') η hηnc
    have hN := Geometry.ClosedFibreComponent.isProjectiveOver_canonicalNormalization β q y hpT η
    obtain ⟨P, M, hP, hM, hdeg⟩ := StableMarkedComponentDegree.exists_lineBundle_component_degree
      f D' a' v hv hN hV hgen hss E hEi' hEs L e
    have hpositive := StableOpenMarkedSupportCount.marked_component_number_pos β q D' a'
      hnum' hno' v hv (Geometry.ClosedFibreComponent.contracted_closure β q y η) hN P M hP hM
    change 0 < DualityScheme.eulerCharOf
        ((L.pullback (Genus.normalizationPointsMap ({η} : Set (β.fiber y)) ≫ β.fiberι y)).twist
          (unitModule (Genus.normalizationPoints ({η} : Set (β.fiber y)))) 1)
          (structureCoeff (Genus.normalizationPointsMap ({η} : Set (β.fiber y)) ≫
            β.fiberToSpecResidueField y)) -
        Genus.eulerChar (Genus.normalizationPoints ({η} : Set (β.fiber y)))
          (structureCoeff (Genus.normalizationPointsMap ({η} : Set (β.fiber y)) ≫
            β.fiberToSpecResidueField y))
    rw [Geometry.ClosedFibreComponent.canonicalNormalization_degree_eq β q y L η, hdeg]
    exact hpositive
  exact OriginalCanonicalGoodSection.algClosedCurveGoodSection (C.residueField y)
    (β.fiber y) (β.fiberToSpecResidueField y) hpT
    (topologicalKrullDim_fiber_le_one β q y) (L.pullback (β.fiberι y)) hpos

end DeJongAlterations.StableModificationBridge.StableOpenRationalFibreSections
