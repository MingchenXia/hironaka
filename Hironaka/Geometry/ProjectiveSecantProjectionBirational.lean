import Hironaka.Geometry.ProjectiveSecantProjectionFiniteChart
import Hironaka.Geometry.ProjectiveSecantProjectionOpenIso
import Hironaka.Geometry.ProjectiveSecantProjectionImage
import Hironaka.Geometry.AffineBlowupBirational

/-!
# Genuine birationality of the SAME actual original finite general-position projection
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveIdeal ProjectiveRationalPointCoordinates

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Literal original affine away-map bijectivity makes the SAME original finite map restricted to its actual native target localization chart an isomorphism. -/
theorem isIso_original_morphismRestrict_of_awayMap_bijective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (U : Y.Opens) (hU : IsAffineOpen U) (r : Γ(Y, U))
    (hbij : Function.Bijective (Localization.awayMap (f.app U).hom r)) :
    IsIso (f ∣_ (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U) (Localization.Away r))) ≫
      hU.fromSpec).opensRange) := by
  let hV := hU.preimage f
  have H : IsPullback (Spec.map (f.app U)) hV.fromSpec hU.fromSpec f := by
    apply IsOpenImmersion.isPullback
    · simpa only [← Scheme.Hom.app_eq_appLE] using
        (IsAffineOpen.SpecMap_appLE_fromSpec f hU hV le_rfl).symm
    · rw [IsAffineOpen.opensRange_fromSpec, IsAffineOpen.opensRange_fromSpec]
  let g := Spec.map (CommRingCat.ofHom (Localization.awayMap (f.app U).hom r))
  let : IsIso (CommRingCat.ofHom (Localization.awayMap (f.app U).hom r)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  let : IsIso g := inferInstance
  exact isIso_morphismRestrict_of_isPullback_open_chart g _ _ f
    ((isPullback_spec_awayMap (f.app U) r).paste_vert H)

/-- Original finite dominant geometry and original point local data internally produce an actual open containing the SAME original target point on which the SAME original map is an isomorphism. -/
theorem exists_original_target_open_isIso_of_finite_local_data
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [IsDominant f] [IsReduced Y]
    (x : X) (hfibre : ∀ z : X, f z = f x → z = x)
    (hfu : (f.stalkMap x).hom.FormallyUnramified) [IsIso (f.residueFieldMap x)] :
    ∃ W : Y.Opens, f x ∈ W ∧ IsIso (f ∣_ W) := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show f x ∈ (⊤ : Y.Opens) from trivial)
  obtain ⟨Q, hQ, r, hr, hbij⟩ := exists_original_finite_chart_awayMap_bijective f x U hU hxU hfibre hfu
  let b := Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U) (Localization.Away r))) ≫ hU.fromSpec
  refine ⟨b.opensRange, ?_, isIso_original_morphismRestrict_of_awayMap_bijective f U hU r (hbij r dvd_rfl)⟩
  have hP : Spec.map (f.app U) Q ∈
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U) (Localization.Away r)))).opensRange := by
    rw [Scheme.Hom.opensRange_localizationAway]
    exact hr
  change f x ∈ (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U) (Localization.Away r))) ≫ hU.fromSpec).opensRange
  rw [Scheme.Hom.opensRange_comp]
  refine ⟨Spec.map (f.app U) Q, hP, ?_⟩
  have ht : Spec.map (f.app U) ≫ hU.fromSpec = (hU.preimage f).fromSpec ≫ f := by
    simpa only [← Scheme.Hom.app_eq_appLE] using
      (IsAffineOpen.SpecMap_appLE_fromSpec f hU (hU.preimage f) le_rfl)
  have hh := congrArg (fun m : Spec Γ(X, f ⁻¹ᵁ U) ⟶ Y => m Q) ht
  change hU.fromSpec (Spec.map (f.app U) Q) = f ((hU.preimage f).fromSpec Q) at hh
  exact hh.trans (congrArg (fun z => f z) hQ)

/-- The actual original finite integral map with the internally produced original point local data is natively birational OVER its SAME actual original target. -/
theorem birationalOver_id_of_finite_local_data
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [IsDominant f] [IsIntegral X] [IsIntegral Y]
    (x : X) (hfibre : ∀ z : X, f z = f x → z = x)
    (hfu : (f.stalkMap x).hom.FormallyUnramified) [IsIso (f.residueFieldMap x)] :
    Scheme.BirationalOver f (𝟙 Y) := by
  obtain ⟨W, hxW, hW⟩ := exists_original_target_open_isIso_of_finite_local_data f x hfibre hfu
  let := hW
  exact Hironaka.birationalOver_id_of_isIso_morphismRestrict f W ⟨f x, hxW⟩

/-- Original integral projective geometry, actual original rational smooth source and actual centre in the computed original nonempty tangent-secant open internally produce genuine native birationality of the SAME frozen original finite projection onto its SAME actual native integral scheme image. No fibre, unramifiedness, residue isomorphism, local isomorphism or birational certificate is supplied. -/
theorem originalProjection_toImage_birational
    (k : Type u) [Field k] (n : ℕ) {X : Scheme.{u}}
    (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i] [IsIntegral X]
    (s : Spec (CommRingCat.of k) ⟶ X)
    (hs : (s ≫ i) ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
    (hsmall : topologicalKrullDim X < n)
    (hx : s (⊥ : PrimeSpectrum k) ∈ (i ≫ projectiveSpaceStructure k (n + 1)).smoothLocus)
    (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
    (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
    (hc : pointImage k n p ∈ tangentSecantCenterOpen k n i s hs hx hsmall) :
    let f := projectionFromFixedPointOpen k n (s ≫ i) hs i hsmall p hp hc.2
    Scheme.BirationalOver f.toImage (𝟙 f.image) := by
  let f := projectionFromFixedPointOpen k n (s ≫ i) hs i hsmall p hp hc.2
  have h := originalProjection_toImage_local_data k n i s hs hsmall hx p hp hc
  let : IsFinite f.toImage := h.1
  let : IsDominant f.toImage := h.2.1
  let : IsIntegral f.image := h.2.2.1
  let : IsIso (f.toImage.residueFieldMap (s (⊥ : PrimeSpectrum k))) := h.2.2.2.2.1
  apply birationalOver_id_of_finite_local_data f.toImage (s (⊥ : PrimeSpectrum k))
  · intro z hz
    apply Set.mem_singleton_iff.mp
    rw [← h.2.2.2.2.2]
    exact hz
  · exact h.2.2.2.1

end Hironaka.Geometry.ProjectiveSecant
