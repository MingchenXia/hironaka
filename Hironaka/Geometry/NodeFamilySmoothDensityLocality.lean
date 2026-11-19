import Hironaka.Geometry.NodeFamilySmoothDensityBaseChange

/-! Genuine open-cover density and actual relative smooth-locus transport. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Hironaka.Geometry.NodeFamilySmoothDensityLocality

open Algebra.NodeBlowupChart NodeFamilyFlat NodeFamilyGeometricPurity
open NodeFamilySmoothDensityBaseChange

universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual density descends through a genuine source open cover. -/
theorem dense_of_openCover {X : Scheme.{u}} (𝒰 : X.OpenCover.{v}) (s : Set X)
    (h : ∀ i, Dense ((𝒰.f i) ⁻¹' s)) : Dense s := by
  apply dense_iff_inter_open.mpr
  intro V hV hne
  obtain ⟨x, hx⟩ := hne
  obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
  obtain ⟨z, hzV, hzs⟩ := (h i).inter_open_nonempty
    ((𝒰.f i) ⁻¹' V) (hV.preimage (𝒰.f i).continuous) ⟨y, hx⟩
  exact ⟨𝒰.f i z, hzV, hzs⟩

/-- An actual isomorphism over the original base transports density of native relative smooth loci. -/
theorem smoothLocus_dense_of_iso {X Y S : Scheme.{u}} (e : X ≅ Y)
    (f : X ⟶ S) (g : Y ⟶ S) [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g]
    (h : e.hom ≫ g = f) (hg : Dense (g.smoothLocus : Set Y)) :
    Dense (f.smoothLocus : Set X) := by
  have he := Scheme.Hom.preimage_smoothLocus_eq e.hom g
  have heq := he.trans (smoothLocus_eq_of_eq _ _ h)
  rw [← heq]
  exact hg.preimage e.hom.isOpenEmbedding.isOpenMap

/-- The actual native relative smooth locus is dense if it is dense on every actual cover composite. -/
theorem smoothLocus_dense_of_openCover {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (𝒰 : X.OpenCover.{v})
    (h : ∀ i, Dense ((𝒰.f i ≫ f).smoothLocus : Set (𝒰.X i))) :
    Dense (f.smoothLocus : Set X) := by
  apply dense_of_openCover 𝒰
  intro i
  change Dense (((𝒰.f i) ⁻¹ᵁ f.smoothLocus) : Set (𝒰.X i))
  rw [Scheme.Hom.preimage_smoothLocus_eq]
  exact h i

/-- A genuine open node chart retains dense smooth locus after the actual family field base change. -/
theorem fieldBaseChange_nodeChart_smoothLocus_dense {A : Type u} [CommRing A]
    (K : Type u) [Field K] [Algebra A K] {X : Scheme.{u}}
    (g : X ⟶ Spec (CommRingCat.of A)) [LocallyOfFinitePresentation g]
    (q : A) (f : Spec (CommRingCat.of (Node A q)) ⟶ X) [IsOpenImmersion f]
    (hf : f ≫ g = nodeMorphism q) :
    Dense (((pullback.fst (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap A K)))) f) ≫
      pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap A K)))).smoothLocus :
      Set (pullback (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap A K)))) f : Scheme.{u})) := by
  let s := Spec.map (CommRingCat.ofHom (algebraMap A K))
  have hpb : IsPullback (pullback.snd (pullback.fst g s) f)
      (pullback.fst (pullback.fst g s) f ≫ pullback.snd g s) (nodeMorphism q) s := by
    rw [← hf]
    exact (IsPullback.of_hasPullback (pullback.fst g s) f).flip.paste_vert
      (IsPullback.of_hasPullback g s)
  apply smoothLocus_dense_of_iso hpb.isoPullback _ (fieldBaseChangeMorphism K q)
    hpb.isoPullback_hom_snd
  exact fieldBaseChangeMorphism_smoothLocus_dense K q

end Hironaka.Geometry.NodeFamilySmoothDensityLocality
