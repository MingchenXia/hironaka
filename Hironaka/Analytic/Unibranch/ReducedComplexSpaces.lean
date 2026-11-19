import Hironaka.Resolution.HironakaReducedComplexAnalyticSpaces
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Original reduced complex spaces and intrinsic unibranchness

The book assumes reduced Hausdorff paracompact complex spaces. We retain the
existing locally ringed spaces over the complex point and their genuine
whole-vanishing-ideal quotient models, without imposing global second
countability. Reducedness of the intrinsic stalks is proved from the actual
open-immersion stalk maps. Unibranchness uses the actual fraction ring and
integral closure; chart independence, isomorphism invariance and the normal
stalk implication are proved using manufactured ring isomorphisms.

Original source: Appendix B, `def:unibranch:L21` and its standing geometry.
Blueprint: `source-reduced-complex-space-unibranch.tex`.
-/

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open Hironaka
open Hironaka.HironakaReducedComplexAnalyticSpaces
open Hironaka.HironakaActualAnalyticSubspace

namespace Hironaka.Analytic.Unibranch
noncomputable section

/-- The original Hausdorff/paracompact local analytic-model property on the same
actual category of locally ringed spaces over the complex point. -/
def sourceReducedComplexSpaceProperty : ObjectProperty (Over complexPoint) := fun A =>
  T2Space A.left ∧ ParacompactSpace A.left ∧
    ∀ x : A.left, ∃ (n : ℕ) (U : Opens (ComplexModel n)) (C : Set U),
      IsComplexAnalyticSubset (n := n) C ∧
      ∃ i : (modelOver U C).left ⟶ A.left,
        LocallyRingedSpace.IsOpenImmersion i ∧
        i ≫ A.hom = (modelOver U C).hom ∧ x ∈ range i.base

/-- The full category of the original reduced complex spaces. Reducedness is a
theorem about the actual local quotient sheaves, not an additional field. -/
abbrev SourceReducedComplexSpace := sourceReducedComplexSpaceProperty.FullSubcategory

/-- Every genuine embedded analytic model is an original complex space. Its
metric subspace topology supplies Hausdorffness and paracompactness. -/
def sourceReducedComplexSpaceModel {n : ℕ} (U : Opens (ComplexModel n)) (C : Set U)
    (hC : IsComplexAnalyticSubset (n := n) C) : SourceReducedComplexSpace := by
  refine ⟨modelOver U C, ?_, ?_, ?_⟩
  · change T2Space C
    infer_instance
  · change ParacompactSpace C
    infer_instance
  intro x
  exact ⟨n, U, C, hC, 𝟙 _, inferInstance, Category.id_comp _, x, rfl⟩

/-- Actual model stalk isomorphisms prove reducedness for every original stalk,
without any global countability or smoothness hypothesis. -/
theorem SourceReducedComplexSpace.isReduced_stalk (X : SourceReducedComplexSpace)
    (x : X.obj.left) : IsReduced (X.obj.left.presheaf.stalk x).carrier := by
  obtain ⟨n, U, C, _hC, i, hi, _hpoint, c, hcx⟩ := X.property.2.2 x
  subst x
  let : LocallyRingedSpace.IsOpenImmersion i := hi
  let e := (asIso (i.stalkMap c)).commRingCatIsoToRingEquiv
  let : IsReduced ((modelOver U C).left.presheaf.stalk c).carrier := by
    exact actualSubspaceStalk_isReduced (n := n) C c
  refine ⟨?_⟩
  intro r hr
  apply e.injective
  exact (IsReduced.eq_zero (e r) (hr.map e.toRingHom)).trans (map_zero e).symm

/-- On a reduced local ring, unibranchness means being a domain whose actual
integral closure in its actual fraction ring is local. The conjunction also
defines a predicate on arbitrary commutative rings, and is false on non-domains. -/
def SourceUnibranchReducedRing (R : Type*) [CommRing R] : Prop :=
  IsDomain R ∧ IsLocalRing (integralClosure R (FractionRing R))

private def fractionEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    FractionRing R ≃+* FractionRing S := IsFractionRing.ringEquivOfRingEquiv e

private theorem coefficient_square {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) :
    (algebraMap S (FractionRing S)).comp e.toRingHom =
      (fractionEquiv e).toRingHom.comp (algebraMap R (FractionRing R)) := by
  ext r
  exact (IsFractionRing.ringEquivOfRingEquiv_algebraMap e r).symm

/-- The normalization-ring equivalence is constructed from the original ring
equivalence by transporting monic equations along the commuting coefficient maps. -/
private def closureEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    integralClosure R (FractionRing R) ≃+* integralClosure S (FractionRing S) where
  toFun x := ⟨fractionEquiv e x,
    IsIntegral.map_of_comp_eq e.toRingHom (fractionEquiv e).toRingHom
      (coefficient_square e) x.property⟩
  invFun y := ⟨fractionEquiv e.symm y,
    IsIntegral.map_of_comp_eq e.symm.toRingHom (fractionEquiv e.symm).toRingHom
      (coefficient_square e.symm) y.property⟩
  left_inv x := by
    apply Subtype.ext
    exact (fractionEquiv e).symm_apply_apply x
  right_inv x := by
    apply Subtype.ext
    exact (fractionEquiv e).apply_symm_apply x
  map_add' x y := by
    apply Subtype.ext
    exact map_add (fractionEquiv e) (x : FractionRing R) (y : FractionRing R)
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (fractionEquiv e) (x : FractionRing R) (y : FractionRing R)

/-- Ring isomorphisms preserve and reflect actual reduced-ring unibranchness;
the fraction-field and normalization-ring equivalences are manufactured internally. -/
theorem sourceUnibranchReducedRing_iff_of_ringEquiv {R S : Type*}
    [CommRing R] [CommRing S] (e : R ≃+* S) :
    SourceUnibranchReducedRing R ↔ SourceUnibranchReducedRing S := by
  constructor
  · rintro ⟨hD, hL⟩
    let := hL
    exact ⟨e.toMulEquiv.isDomain_iff.mp hD, (closureEquiv e).isLocalRing⟩
  · rintro ⟨hD, hL⟩
    let := hL
    exact ⟨e.toMulEquiv.isDomain_iff.mpr hD, (closureEquiv e).symm.isLocalRing⟩

/-- Original `def:unibranch:L21`: every actual intrinsic structure-sheaf stalk
is unibranch. These stalks are already local and are proved reduced above. -/
def SourceReducedComplexSpace.IsUnibranch (X : SourceReducedComplexSpace) : Prop :=
  ∀ x : X.obj.left, SourceUnibranchReducedRing (X.obj.left.presheaf.stalk x).carrier

/-- A genuine model open immersion tests exactly the intrinsic stalk at its image. -/
theorem SourceReducedComplexSpace.unibranch_stalk_iff_model (X : SourceReducedComplexSpace)
    {n : ℕ} (U : Opens (ComplexModel n)) (C : Set U)
    (i : (modelOver U C).left ⟶ X.obj.left) [LocallyRingedSpace.IsOpenImmersion i]
    (c : (modelOver U C).left) :
    SourceUnibranchReducedRing (X.obj.left.presheaf.stalk (i.base c)).carrier ↔
      SourceUnibranchReducedRing ((modelOver U C).left.presheaf.stalk c).carrier :=
  sourceUnibranchReducedRing_iff_of_ringEquiv
    (asIso (i.stalkMap c)).commRingCatIsoToRingEquiv

/-- All actual chart/model choices give the same intrinsic all-point condition. -/
theorem SourceReducedComplexSpace.isUnibranch_iff_model_stalks (X : SourceReducedComplexSpace) :
    X.IsUnibranch ↔
      ∀ (n : ℕ) (U : Opens (ComplexModel n)) (C : Set U),
        IsComplexAnalyticSubset (n := n) C →
        ∀ i : (modelOver U C).left ⟶ X.obj.left,
          LocallyRingedSpace.IsOpenImmersion i →
          i ≫ X.obj.hom = (modelOver U C).hom →
          ∀ c : (modelOver U C).left,
            SourceUnibranchReducedRing ((modelOver U C).left.presheaf.stalk c).carrier := by
  constructor
  · intro h n U C _hC i hi _hpoint c
    let : LocallyRingedSpace.IsOpenImmersion i := hi
    exact (X.unibranch_stalk_iff_model U C i c).mp (h (i.base c))
  · intro h x
    obtain ⟨n, U, C, hC, i, hi, hpoint, c, hcx⟩ := X.property.2.2 x
    subst x
    let : LocallyRingedSpace.IsOpenImmersion i := hi
    exact (X.unibranch_stalk_iff_model U C i c).mpr (h n U C hC i hi hpoint c)

/-- It suffices to choose one actual model stalk through each original point. -/
theorem SourceReducedComplexSpace.isUnibranch_iff_exists_model_stalks
    (X : SourceReducedComplexSpace) :
    X.IsUnibranch ↔ ∀ x : X.obj.left,
      ∃ (n : ℕ) (U : Opens (ComplexModel n)) (C : Set U),
        IsComplexAnalyticSubset (n := n) C ∧
        ∃ i : (modelOver U C).left ⟶ X.obj.left,
          LocallyRingedSpace.IsOpenImmersion i ∧
          i ≫ X.obj.hom = (modelOver U C).hom ∧
          ∃ c : (modelOver U C).left, i.base c = x ∧
            SourceUnibranchReducedRing ((modelOver U C).left.presheaf.stalk c).carrier := by
  constructor
  · intro h x
    obtain ⟨n, U, C, hC, i, hi, hpoint, c, hcx⟩ := X.property.2.2 x
    refine ⟨n, U, C, hC, i, hi, hpoint, c, hcx, ?_⟩
    let : LocallyRingedSpace.IsOpenImmersion i := hi
    exact (X.unibranch_stalk_iff_model U C i c).mp (h (i.base c))
  · intro h x
    obtain ⟨n, U, C, _hC, i, hi, _hpoint, c, hcx, hc⟩ := h x
    subst x
    let : LocallyRingedSpace.IsOpenImmersion i := hi
    exact (X.unibranch_stalk_iff_model U C i c).mpr hc

/-- Actual isomorphisms of complex spaces preserve intrinsic unibranchness. -/
theorem SourceReducedComplexSpace.isUnibranch_of_iso {X Y : SourceReducedComplexSpace}
    (e : X ≅ Y) (h : X.IsUnibranch) : Y.IsUnibranch := by
  let E : X.obj.left ≅ Y.obj.left :=
    (Over.forget complexPoint).mapIso (sourceReducedComplexSpaceProperty.ι.mapIso e)
  intro y
  exact (sourceUnibranchReducedRing_iff_of_ringEquiv
    (asIso (E.inv.stalkMap y)).commRingCatIsoToRingEquiv).mp (h (E.inv.base y))

/-- For a normal domain, the actual coefficient map onto its normalization ring
is bijective. This ring equivalence is proved, not supplied as data. -/
private def normalClosureEquiv (R : Type*) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] : R ≃+* integralClosure R (FractionRing R) :=
  RingEquiv.ofBijective (algebraMap R (integralClosure R (FractionRing R))) (by
    constructor
    · intro x y h
      apply IsFractionRing.injective R (FractionRing R)
      exact congrArg Subtype.val h
    · intro y
      obtain ⟨x, hx⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral y.property
      exact ⟨x, Subtype.ext hx⟩)

/-- Actual integrally closed domain stalks imply the original unibranch condition. -/
theorem SourceReducedComplexSpace.isUnibranch_of_normal_stalks (X : SourceReducedComplexSpace)
    (hD : ∀ x : X.obj.left, IsDomain (X.obj.left.presheaf.stalk x).carrier)
    (hN : ∀ x : X.obj.left, IsIntegrallyClosed (X.obj.left.presheaf.stalk x).carrier) :
    X.IsUnibranch := by
  intro x
  let := hD x
  let := hN x
  let := X.obj.left.isLocalRing x
  exact ⟨inferInstance, (normalClosureEquiv (X.obj.left.presheaf.stalk x).carrier).isLocalRing⟩

end
end Hironaka.Analytic.Unibranch
