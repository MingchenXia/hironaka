import Hironaka.Geometry.ProjectiveSecantProjectionLocalBridge

/-!
# Actual original open-chart isomorphisms retain the literal original restricted morphism
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.ProjectiveSecant

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A genuine actual Cartesian open source/target chart with actual chart isomorphism makes the SAME original restricted morphism an isomorphism. -/
theorem isIso_morphismRestrict_of_isPullback_open_chart
    {A B X Y : Scheme.{u}} (g : A ⟶ B) (a : A ⟶ X) (b : B ⟶ Y) (f : X ⟶ Y)
    [IsOpenImmersion a] [IsOpenImmersion b] [IsIso g] (H : IsPullback g a b f) :
    IsIso (f ∣_ b.opensRange) := by
  have hpre : f ⁻¹ᵁ b.opensRange = a.opensRange := by
    simpa only [Scheme.Hom.preimage_top, Scheme.Hom.image_top_eq_opensRange] using
      (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H ⊤).symm
  have hA : Set.range a = Set.range (f ⁻¹ᵁ b.opensRange).ι := by
    rw [Scheme.Opens.range_ι]
    exact congrArg (fun U : X.Opens => (U : Set X)) hpre.symm
  let eA := IsOpenImmersion.isoOfRangeEq a (f ⁻¹ᵁ b.opensRange).ι hA
  have ha : eA.inv ≫ a = (f ⁻¹ᵁ b.opensRange).ι := IsOpenImmersion.isoOfRangeEq_inv_fac _ _ hA
  have he : (f ∣_ b.opensRange) = eA.inv ≫ g ≫ b.isoOpensRange.hom := by
    apply (cancel_mono b.opensRange.ι).mp
    rw [morphismRestrict_ι, Category.assoc, Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
    calc
      _ = (eA.inv ≫ a) ≫ f := congrArg (fun m => m ≫ f) ha.symm
      _ = eA.inv ≫ (a ≫ f) := Category.assoc _ _ _
      _ = eA.inv ≫ (g ≫ b) := congrArg (fun m => eA.inv ≫ m) H.w.symm
  rw [he]
  infer_instance

/-- The literal original away maps form an actual native Cartesian spectrum square, with no localization-square certificate. -/
theorem isPullback_spec_awayMap {R S : CommRingCat.{u}} (β : R ⟶ S) (r : R) :
    IsPullback (Spec.map (CommRingCat.ofHom (Localization.awayMap β.hom r)))
      (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (β.hom r)))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) (Spec.map β) := by
  apply IsOpenImmersion.isPullback
  · rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext x
    simp [Localization.awayMap, IsLocalization.Away.map]
  · rw [Scheme.Hom.opensRange_localizationAway, Scheme.Hom.opensRange_localizationAway]
    rfl

end Hironaka.Geometry.ProjectiveSecant
