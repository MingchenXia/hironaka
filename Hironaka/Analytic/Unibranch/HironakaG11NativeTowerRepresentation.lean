import Hironaka.Analytic.Unibranch.HironakaG11BlowupLocality
import Hironaka.Analytic.Unibranch.HironakaG10ChowTowerDomination
import Hironaka.Analytic.Unibranch.OriginalSmoothCentreBlowup
import Hironaka.Analytic.Unibranch.RIsoAModification
import Hironaka.Analytic.Unibranch.HironakaG11PresUnconditional

/-!
# Literal selected native towers representing finite modifications

The whole-ideal universal property transports across an actual base isomorphism.
At each stage its uniqueness identifies the ordinary smooth-centre blowup with
the literal object chosen by `OriginalFiniteIdealBlowup`. The resulting tower is
isomorphic over its base to the given modification; the given object itself is
not asserted to satisfy the literal selected-object inductive relation.

Blueprint FIRST: `hironaka-g11-native-tower-representation.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG11NativeTowerRepresentation

open Hironaka HironakaSingularModuleSheafStalk
  HironakaIntrinsicReducedCentreIdealSheaf HironakaNativePulledIdealSheaf
  SourceReducedComplexSpace SmoothCentreModification HironakaG11BlowupLocality
  HironakaG10ChowTowerDomination HironakaG11SingularCentreModification

noncomputable section

/-- The full universal property for the entire intrinsic ideal is preserved
by an actual base isomorphism, with the ideal of its actual inverse-image set. -/
theorem isIdealBlowup_comp_baseIso {X Y W : SourceReducedComplexSpace}
    {p : Y ⟶ X} (C : Set X.obj.left)
    (hp : IsIdealBlowup p (intrinsicReducedCentreIdealModule X.obj.left C)
      (intrinsicReducedCentreIdealInclusion X.obj.left C)) (e : W ≅ X) :
    IsIdealBlowup (p ≫ e.inv)
      (intrinsicReducedCentreIdealModule W.obj.left (e.hom.hom.left.base ⁻¹' C))
      (intrinsicReducedCentreIdealInclusion W.obj.left (e.hom.hom.left.base ⁻¹' C)) := by
  have : IsIso e.hom.hom.left := by
    change IsIso (isoLeft e).hom
    infer_instance
  have hown : HasRankOneData (nativePulledIdealModule
      ((p ≫ e.inv) ≫ e.hom).hom.left
      (intrinsicReducedCentreIdealModule X.obj.left C)
      (intrinsicReducedCentreIdealInclusion X.obj.left C)) := by
    simpa only [Category.assoc, e.inv_hom_id, Category.comp_id] using hp.1
  refine ⟨(hasRankOneData_comp_openImmersion_iff
    (p ≫ e.inv).hom.left e.hom.hom.left C).mp hown, ?_⟩
  intro A F hF
  have hFX : HasRankOneData (nativePulledIdealModule (F ≫ e.hom).hom.left
      (intrinsicReducedCentreIdealModule X.obj.left C)
      (intrinsicReducedCentreIdealInclusion X.obj.left C)) :=
    (hasRankOneData_comp_openImmersion_iff F.hom.left e.hom.hom.left C).mpr hF
  obtain ⟨L, hL, hLu⟩ := hp.2 A (F ≫ e.hom) hFX
  refine ⟨L, ?_, ?_⟩
  · calc
      L ≫ (p ≫ e.inv) = (L ≫ p) ≫ e.inv := (Category.assoc _ _ _).symm
      _ = (F ≫ e.hom) ≫ e.inv := congrArg (fun k => k ≫ e.inv) hL
      _ = F := by simp only [Category.assoc, e.hom_inv_id, Category.comp_id]
  · intro L' hL'
    apply hLu L'
    have h := congrArg (fun k => k ≫ e.hom) hL'
    simpa only [Category.assoc, e.inv_hom_id, Category.comp_id] using h

private theorem selected_projection_isIdealBlowup (X : SourceReducedComplexSpace)
    (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
    (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf))
    [B.IsFiniteType]
    (hDense : Dense {x : X.obj.left | LinearMap.range
      (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = ⊤}) :
    IsIdealBlowup (OriginalFiniteIdealBlowup.projectionMorphism B b hDense) B b := by
  classical
  refine ⟨OriginalFiniteIdealBlowupUniversal.projection_ideal_exists_locallyFreeData
    B b hDense, ?_⟩
  intro A F hF
  obtain ⟨q, hq, huniq⟩ := hF
  let : q.IsLocallyFreeData := hq
  let : ∀ i, Unique (q.generators i).I := fun i => Classical.choice (huniq i)
  exact OriginalFiniteIdealBlowupUniversal.exists_unique_lift_of_locallyFreeData
    B b hDense A F q

/-- Every original finite smooth-centre modification is represented over its
base by an actual tower of the literally selected native blowup objects. -/
theorem exists_nativeTower_representation {X Y : SourceReducedComplexSpace}
    {p : Y ⟶ X} (hp : IsModification p) :
    ∃ (Z : SourceReducedComplexSpace) (a : Z ≅ Y) (σ : Z ⟶ X),
      IsNativeBlowupTower X Z σ ∧ a.hom ≫ p = σ := by
  classical
  induction hp with
  | id => exact ⟨X, Iso.refl X, 𝟙 X, .refl, Category.id_comp _⟩
  | @cons Y Y' f g hf hg ih =>
    obtain ⟨W, a, τ, hτ, ha⟩ := ih
    obtain ⟨S, i, hi⟩ := hf
    let C : Set Y.obj.left := range i.hom.left.base
    let C' : Set W.obj.left := a.hom.hom.left.base ⁻¹' C
    have hC : Y.IsAnalyticSubset C := hi.2.2.2.1
    have hC' : W.IsAnalyticSubset C' := hC.preimage_iso a
    have hthin : interior C' = ∅ := by
      change interior (isoHomeomorph a ⁻¹' C) = ∅
      rw [← (isoHomeomorph a).preimage_interior, hi.2.2.2.2.1]
      exact preimage_empty
    let B := intrinsicReducedCentreIdealModule W.obj.left C'
    let b := intrinsicReducedCentreIdealInclusion W.obj.left C'
    let : B.IsFiniteType :=
      IntrinsicAnalyticCentreFiniteType.intrinsicReducedCentreIdealModule_isFiniteType W C' hC'
    have hDense : Dense {w : W.obj.left | LinearMap.range
        (stalkInclusionLinearMap W.obj.left.toSheafedSpace.sheaf B b w) = ⊤} := by
      change Dense {w : W.obj.left | LinearMap.range
        (stalkInclusionLinearMap W.obj.left.toSheafedSpace.sheaf
          (intrinsicReducedCentreIdealModule W.obj.left C')
          (intrinsicReducedCentreIdealInclusion W.obj.left C') w) = ⊤}
      rw [OriginalSmoothCentreBlowup.intrinsic_ideal_unitLocus_eq_compl W C' hC']
      exact interior_eq_empty_iff_dense_compl.mp hthin
    let Z := OriginalFiniteIdealBlowup.sourceObject B b hDense
    let q : Z ⟶ W := OriginalFiniteIdealBlowup.projectionMorphism B b hDense
    have hq : IsIdealBlowup q B b := selected_projection_isIdealBlowup W B b hDense
    have hf' : IsIdealBlowup (f ≫ a.inv) B b :=
      isIdealBlowup_comp_baseIso C hi.2.2.2.2.2.1 a
    obtain ⟨β, hβ, _⟩ := RIsoAModification.isIdealBlowup_exists_unique_iso hq hf'
    refine ⟨Z, β, q ≫ τ, .step τ B b hDense hτ, ?_⟩
    have hβ' : β.hom ≫ f = q ≫ a.hom := by
      have h := congrArg (fun k => k ≫ a.hom) hβ
      simpa only [Category.assoc, a.inv_hom_id, Category.comp_id] using h
    calc
      β.hom ≫ (f ≫ g) = (β.hom ≫ f) ≫ g := (Category.assoc _ _ _).symm
      _ = (q ≫ a.hom) ≫ g := congrArg (fun k => k ≫ g) hβ'
      _ = q ≫ τ := by rw [Category.assoc, ha]

/-- In particular, G11's actual singular-centre modification admits a
literal selected native tower representation, with an isomorphism over X. -/
theorem exists_nativeTower_representation_of_singularCentre
    {X Y : SourceReducedComplexSpace} {p : Y ⟶ X}
    (hp : IsSingularCentreModification p) :
    ∃ (Z : SourceReducedComplexSpace) (a : Z ≅ Y) (σ : Z ⟶ X),
      IsNativeBlowupTower X Z σ ∧ a.hom ≫ p = σ :=
  exists_nativeTower_representation hp.toIsModification

private theorem isSmooth_of_iso {X Y : SourceReducedComplexSpace} (a : X ≅ Y)
    (hY : Y.IsSmooth) : X.IsSmooth := by
  intro x
  obtain ⟨d, V, j, hj, hjpoint, y, hy⟩ := hY (isoHomeomorph a x)
  let : LocallyRingedSpace.IsOpenImmersion j := hj
  refine ⟨d, V, j ≫ (isoLeft a).inv, inferInstance, ?_, y, ?_⟩
  · change (j ≫ a.inv.hom.left) ≫ X.obj.hom = _
    rw [Category.assoc, Over.w a.inv.hom]
    exact hjpoint
  · change (isoHomeomorph a).symm (j.base y) = x
    rw [hy]
    exact (isoHomeomorph a).symm_apply_apply x

/-- Unconditional compact resolution supplies a compact smooth ORIGINAL
source for a literal native tower, without any uniform dimension assumption. -/
theorem exists_compact_smooth_nativeTower (X : SourceReducedComplexSpace)
    (hX : CompactSpace X.obj.left) :
    ∃ (Z : SourceReducedComplexSpace) (σ : Z ⟶ X),
      IsNativeBlowupTower X Z σ ∧ Z.IsSmooth ∧ CompactSpace Z.obj.left := by
  obtain ⟨Y, p, hp, _, hY, _, _, _, _, _, _, hcompact⟩ :=
    HironakaG11PresUnconditional.exists_endpoint X hX
  obtain ⟨Z, a, σ, hσ, _⟩ := exists_nativeTower_representation_of_singularCentre hp
  let : CompactSpace Y.obj.left := hcompact hX
  exact ⟨Z, σ, hσ, isSmooth_of_iso a hY, (isoHomeomorph a).symm.compactSpace⟩

end
end Hironaka.Analytic.Unibranch.HironakaG11NativeTowerRepresentation
