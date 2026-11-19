import Hironaka.Geometry.ProjectiveSecantProjectionScalarSource
import Hironaka.Geometry.ProjectiveSecantProjectionScalarEtale
import Hironaka.Geometry.ProjectiveSecantProjectionEtaleOpen

/-!
# The same original geometric finite generically etale projection on its canonical scalar source
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Hironaka.Geometry.ProjectiveSecant

open BlowupProjectiveEmbedding ProjectiveProjectionPoint ProjectiveRationalPointCoordinates

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Finiteness of the SAME entire original projection survives its literal native scalar pullback and internally produced canonical-source isomorphism. -/
theorem originalProjectionScalar_isFinite
    (k L : Type u) [CommRing k] [CommRing L] (φ : k →+* L) (n : ℕ)
    {X : Scheme.{u}} (f : X ⟶ projectiveSpace k n) [IsFinite f]
    (pX : X ⟶ Spec (CommRingCat.of k)) (ht : f ≫ projectiveSpaceStructure k n = pX) :
    IsFinite (originalProjectionScalar k L φ n f pX ht) := by
  dsimp only [originalProjectionScalar]
  infer_instance

/-- Genuine generic etaleness transports to the SAME original projection on the canonical scalar pullback of its SAME original source. -/
theorem originalProjectionScalar_isGenericallyEtale
    (k L : Type u) [Field k] [Field L] (φ : k →+* L) (n : ℕ)
    {X : Scheme.{u}} (f : X ⟶ projectiveSpace k n) (hf : IsGenericallyEtale f)
    (pX : X ⟶ Spec (CommRingCat.of k)) (ht : f ≫ projectiveSpaceStructure k n = pX) :
    IsGenericallyEtale (originalProjectionScalar k L φ n f pX ht) := by
  let : UniversallyOpen (projectiveCoefficientMap φ n) := projectiveCoefficientMap_universallyOpen k L φ n
  exact (isGenericallyEtale_of_etale (originalProjectionScalarSourceIso k L φ n f pX ht).inv).comp
    (genericallyEtale_pullback_of_universallyOpen f (projectiveCoefficientMap φ n) hf)

/-- Original geometric data alone internally produce the SAME original finite generically etale projection on the canonical scalar pullback of the SAME original source, retaining BOTH literal whole original triangles. -/
theorem originalProjection_from_etaleCenterOpen_scalar
    (k L : Type u) [Field k] [Field L] (φ : k →+* L) (n : ℕ)
    {X : Scheme.{u}} [IsIntegral X]
    (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]
    (s : Spec (CommRingCat.of k) ⟶ X)
    (hs : (s ≫ i) ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
    (hdim : topologicalKrullDim X = n)
    (hx : s (⊥ : PrimeSpectrum k) ∈ (i ≫ projectiveSpaceStructure k (n + 1)).smoothLocus)
    (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
    (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
    (hc : pointImage k n p ∈ projectionEtaleCenterOpen k n i s hs hdim hx) :
    let f := projectionFromPoint k n p hp i hc.2
    let pX := i ≫ projectiveSpaceStructure k (n + 1)
    let ht := projectionFromPoint_structure k n p hp i hc.2
    let fL := originalProjectionScalar k L φ n f pX ht
    IsFinite fL ∧ IsGenericallyEtale fL ∧
      fL ≫ projectiveSpaceStructure L n = pullback.snd pX (Spec.map (CommRingCat.ofHom φ)) ∧
      fL ≫ projectiveCoefficientMap φ n = pullback.fst pX (Spec.map (CommRingCat.ofHom φ)) ≫ f := by
  let : IsFinite (projectionFromPoint k n p hp i hc.2) := projectionFromPoint_isFinite k n p hp i hc.2
  exact ⟨originalProjectionScalar_isFinite k L φ n _ _ _,
    originalProjectionScalar_isGenericallyEtale k L φ n _
      (originalProjection_isGenericallyEtale k n i p hp s hs hdim hx hc.2 hc.1) _ _,
    originalProjectionScalar_structure k L φ n _ _ _, originalProjectionScalar_original k L φ n _ _ _⟩

end Hironaka.Geometry.ProjectiveSecant
