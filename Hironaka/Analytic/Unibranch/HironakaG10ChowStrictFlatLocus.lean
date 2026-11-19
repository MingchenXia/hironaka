import Hironaka.Analytic.Unibranch.HironakaG10ChowOneStepStrictTransform
import Hironaka.Analytic.Unibranch.HironakaG10ChowFlatOpen

/-!
# Non-flat loci under one admissible blowup step (global flattening, route §4 (4.2))

For the one-step strict transform `(Y', p, q)` of a proper `f : Y ⟶ X` under the native blowup
`σ : X' ⟶ X` of a finite-type ideal with dense unit locus (`HironakaG10ChowOneStepStrictTransform`):
off the exceptional set `E = σ⁻¹(nonunit locus)` the strict transform is flat exactly where `f` is
(`strictP_flat_iff`), so the non-flat image of `p` off `E` is the preimage of the non-flat image of
`f` (`nonflatImage_strictP_inter_compl`).  If the centre is ADMISSIBLE — its nonunit locus lies in
the non-flat image of `f`, as in every round of the flattening algorithm (Rydh, proof of
Thm. 1.1: "U-admissible blow-ups") — then `σ` maps the non-flat image of `p` into that of `f`
(`mapsTo_nonflatImage`): this is the compatibility hypothesis `hmaps` of
`HironakaG10ChowStrictTransformCalculus.FlatteningSequence.exists_flat` for one-step rounds.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10ChowStrictFlatLocus

open Hironaka HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  SourceReducedComplexSpace EmbeddedIdealBlowupNonunitLocus HironakaG10ChowFlatteningReduction
  HironakaG10ChowStrictTransformCalculus HironakaG10ChowOneStepStrictTransform
  HironakaG10ChowFlatOpen HironakaG10ChowFlatBimeromorphicIso

noncomputable section

/-- The image of the non-flat locus of a morphism. -/
def nonflatImage {X Y : SourceReducedComplexSpace} (f : Y ⟶ X) : Set X.obj.left :=
  f.hom.left.base '' {y | ¬ (f.hom.left.stalkMap y).hom.Flat}

theorem mem_nonflatImage_iff {X Y : SourceReducedComplexSpace} (f : Y ⟶ X) (x : X.obj.left) :
    x ∉ nonflatImage f ↔ ∀ y, f.hom.left.base y = x → (f.hom.left.stalkMap y).hom.Flat := by
  constructor
  · intro h y hy
    by_contra hn
    exact h ⟨y, hn, hy⟩
  · rintro h ⟨y, hn, hy⟩
    exact hn (h y hy)

/-- Flatness of a stalk map is unchanged by composing with a stalk isomorphism on the source
side. -/
theorem flat_of_comp_isIso {A B C : CommRingCat} (φ : A ⟶ B) (ψ : B ⟶ C) [IsIso ψ]
    (h : (φ ≫ ψ).hom.Flat) : φ.hom.Flat := by
  have heq : φ = (φ ≫ ψ) ≫ inv ψ := by rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [heq]
  exact RingHom.Flat.comp h (flat_of_isIso (inv ψ))

variable {X Y : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf))
  [B.IsFiniteType]
  (hDense : Dense {x : X.obj.left |
    LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = ⊤})
  (f : Y ⟶ X)

/-- **Off the exceptional set the strict transform is flat exactly where `f` is.** -/
theorem strictP_flat_iff (y : (strictSource B b f).obj.left)
    (hy : y ∈ (strictP B b hDense f).hom.left.base ⁻¹' (stepExcep B b hDense)ᶜ) :
    ((strictP B b hDense f).hom.left.stalkMap y).hom.Flat ↔
      (f.hom.left.stalkMap ((strictQ B b f).hom.left.base y)).hom.Flat := by
  have hq : IsIso ((strictQ B b f).hom.left.stalkMap y) :=
    isIso_stalkMap_of_isOpenImmersionOn (strict_openImmersionOn B b hDense f) y hy
  have hσ : IsIso ((stepProj B b hDense).hom.left.stalkMap ((strictP B b hDense f).hom.left.base y)) :=
    isIso_stalkMap_of_isOpenImmersionOn (stepProj_isOpenImmersionOn B b hDense) _ hy
  have hsq : (strictP B b hDense f).hom.left ≫ (stepProj B b hDense).hom.left =
      (strictQ B b f).hom.left ≫ f.hom.left :=
    congrArg (fun H : strictSource B b f ⟶ X => H.hom.left) (strictP_comp B b hDense f)
  constructor
  · intro hp
    have h1 : (((strictP B b hDense f).hom.left ≫ (stepProj B b hDense).hom.left).stalkMap y).hom.Flat :=
      flat_stalkMap_comp _ _ y (flat_of_isIso _) hp
    have h2 : (((strictQ B b f).hom.left ≫ f.hom.left).stalkMap y).hom.Flat :=
      flat_stalkMap_of_eq hsq.symm y h1
    rw [LocallyRingedSpace.stalkMap_comp] at h2
    exact flat_of_comp_isIso _ _ h2
  · intro hf
    have h1 : (((strictQ B b f).hom.left ≫ f.hom.left).stalkMap y).hom.Flat :=
      flat_stalkMap_comp _ _ y hf (flat_of_isIso _)
    have h2 : (((strictP B b hDense f).hom.left ≫ (stepProj B b hDense).hom.left).stalkMap y).hom.Flat :=
      flat_stalkMap_of_eq hsq y h1
    exact flat_stalkMap_of_comp _ _ y hσ h2

/-- **Off the exceptional set, the non-flat image of the strict transform is the preimage of the
non-flat image of `f`.** -/
theorem nonflatImage_strictP_inter_compl :
    nonflatImage (strictP B b hDense f) ∩ (stepExcep B b hDense)ᶜ =
      (stepProj B b hDense).hom.left.base ⁻¹' nonflatImage f ∩ (stepExcep B b hDense)ᶜ := by
  ext x'
  constructor
  · rintro ⟨⟨y', hy'n, rfl⟩, hx'⟩
    refine ⟨?_, hx'⟩
    refine ⟨(strictQ B b f).hom.left.base y', fun hf => hy'n ?_, ?_⟩
    · exact (strictP_flat_iff B b hDense f y' hx').mpr hf
    · exact (strictP_comp_apply B b hDense f y').symm
  · rintro ⟨⟨y, hyn, hyx⟩, hx'⟩
    refine ⟨?_, hx'⟩
    obtain ⟨y', hy'p, hy'q⟩ := strict_covers B b hDense f y x' hx' hyx
    refine ⟨y', fun hp => hyn ?_, hy'p⟩
    have hy'E : y' ∈ (strictP B b hDense f).hom.left.base ⁻¹' (stepExcep B b hDense)ᶜ := by
      change (strictP B b hDense f).hom.left.base y' ∈ (stepExcep B b hDense)ᶜ
      rw [hy'p]
      exact hx'
    have h := (strictP_flat_iff B b hDense f y' hy'E).mp hp
    rwa [hy'q] at h

/-- **Admissible steps keep the non-flat image inside the old one**: if the nonunit locus of the
centre lies in the non-flat image of `f`, then `σ` maps the non-flat image of the strict transform
into the non-flat image of `f`. -/
theorem mapsTo_nonflatImage (hadm : nonunitLocus B b ⊆ nonflatImage f) :
    MapsTo (stepProj B b hDense).hom.left.base (nonflatImage (strictP B b hDense f))
      (nonflatImage f) := by
  intro x' hx'
  by_contra hσ
  have hx'E : x' ∈ (stepExcep B b hDense)ᶜ := fun hE => hσ (hadm hE)
  have := (Set.ext_iff.mp (nonflatImage_strictP_inter_compl B b hDense f) x').mp ⟨hx', hx'E⟩
  exact hσ this.1

end

end Hironaka.Analytic.Unibranch.HironakaG10ChowStrictFlatLocus
