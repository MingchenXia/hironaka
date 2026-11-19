import Hironaka.Geometry.ProjectiveSecantProjectionScalarImagePullback
import Hironaka.Geometry.ProjectiveSecantProjectionScalarOpenIso
import Hironaka.Geometry.ProjectiveSecantProjectionBirational

/-!
# Genuine birationality of the SAME canonical scalar projection onto its actual native image
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hironaka.Geometry.ProjectiveSecant

open BlowupProjectiveEmbedding ProjectiveProjectionPoint ProjectiveRationalPointCoordinates

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Original geometry internally supplies a dense actual target isomorphism open for the SAME original native image factor, whose actual source inverse image is also dense. -/
theorem originalProjection_toImage_dense_isIso_open
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
    ∃ U : f.image.Opens, f.toImage (s (⊥ : PrimeSpectrum k)) ∈ U ∧
      Dense (U : Set f.image) ∧ Dense (f.toImage ⁻¹ᵁ U : Set X) ∧ IsIso (f.toImage ∣_ U) := by
  let f := projectionFromFixedPointOpen k n (s ≫ i) hs i hsmall p hp hc.2
  have h := originalProjection_toImage_local_data k n i s hs hsmall hx p hp hc
  let : IsFinite f.toImage := h.1
  let : IsDominant f.toImage := h.2.1
  let : IsIntegral f.image := h.2.2.1
  let : IsIso (f.toImage.residueFieldMap (s (⊥ : PrimeSpectrum k))) := h.2.2.2.2.1
  obtain ⟨U, hxU, hU⟩ := exists_original_target_open_isIso_of_finite_local_data f.toImage
    (s (⊥ : PrimeSpectrum k))
    (fun z hz => Set.mem_singleton_iff.mp (by rw [← h.2.2.2.2.2]; exact hz)) h.2.2.2.1
  exact ⟨U, hxU, U.isOpen.dense ⟨_, hxU⟩,
    (f.toImage ⁻¹ᵁ U).isOpen.dense ⟨s (⊥ : PrimeSpectrum k), hxU⟩, hU⟩

/-- Original integral geometry and a genuine centre in the internally constructed tangent-secant open produce native birationality onto the SAME actual native image of the canonical scalar projection, over ANY actual field extension, with BOTH literal whole coefficient triangles. Neither a scalar image comparison, scalar integrality, local isomorphism nor birationality certificate is supplied. -/
theorem originalProjection_from_tangentSecantOpen_scalar
    (k L : Type u) [Field k] [Field L] (φ : k →+* L) (n : ℕ) {X : Scheme.{u}}
    (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i] [IsIntegral X]
    (s : Spec (CommRingCat.of k) ⟶ X)
    (hs : (s ≫ i) ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
    (hsmall : topologicalKrullDim X < n)
    (hx : s (⊥ : PrimeSpectrum k) ∈ (i ≫ projectiveSpaceStructure k (n + 1)).smoothLocus)
    (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
    (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
    (hc : pointImage k n p ∈ tangentSecantCenterOpen k n i s hs hx hsmall) :
    let f := projectionFromFixedPointOpen k n (s ≫ i) hs i hsmall p hp hc.2
    let pX := i ≫ projectiveSpaceStructure k (n + 1)
    let ht := projectionFromFixedPointOpen_structure k n (s ≫ i) hs i hsmall p hp hc.2
    let fL := originalProjectionScalar k L φ n f pX ht
    IsFinite fL ∧ Scheme.BirationalOver fL.toImage (𝟙 fL.image) ∧
      fL ≫ projectiveSpaceStructure L n = pullback.snd pX (Spec.map (CommRingCat.ofHom φ)) ∧
      fL ≫ projectiveCoefficientMap φ n = pullback.fst pX (Spec.map (CommRingCat.ofHom φ)) ≫ f := by
  let f := projectionFromFixedPointOpen k n (s ≫ i) hs i hsmall p hp hc.2
  let pX := i ≫ projectiveSpaceStructure k (n + 1)
  let ht := projectionFromFixedPointOpen_structure k n (s ≫ i) hs i hsmall p hp hc.2
  let : IsFinite f := projectionFromFixedPointOpen_isFinite k n (s ≫ i) hs i hsmall p hp hc.2
  obtain ⟨U, _, hU, hpre, hIso⟩ := originalProjection_toImage_dense_isIso_open k n i s hs hsmall hx p hp hc
  let := hIso
  let := originalProjectionScalarImage_coefficient_universallyOpen k L φ n f pX ht
  exact ⟨originalProjectionScalar_isFinite k L φ n f pX ht,
    birationalOver_pullback_of_dense_isIso
      (originalProjectionScalar_toImage_isPullback k L φ n f pX ht) U hU hpre,
    originalProjectionScalar_structure k L φ n f pX ht,
    originalProjectionScalar_original k L φ n f pX ht⟩

end Hironaka.Geometry.ProjectiveSecant
