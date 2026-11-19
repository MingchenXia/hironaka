import Hironaka.Geometry.ProjectiveSecantProjectionNativeChart
import Hironaka.Geometry.ProjectiveSecantProjectionChartUnramified
import Hironaka.Geometry.ProjectiveProjectionPointFinite
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# The SAME original finite scheme projection is formally unramified on the SAME original smooth-point stalk
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveIdeal ProjectiveProjection ProjectiveProjectionCenter ProjectiveRationalPointCoordinates ProjectiveProjectionPoint
open Algebra.ProjectiveSecant Algebra.ProjectiveLinearCoordinates Algebra.ProjectiveProjectionFinite

universe u

attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Native prime-localized algebra unramifiedness carries through the literal original Spec stalk isomorphisms. -/
theorem spec_stalkMap_formallyUnramified_of_isUnramifiedAt
    {R S : CommRingCat.{u}} (β : R ⟶ S) (Q : PrimeSpectrum S)
    (h : letI := β.hom.toAlgebra; Algebra.IsUnramifiedAt R Q.asIdeal) :
    ((Spec.map β).stalkMap Q).hom.FormallyUnramified := by
  let : Algebra R S := β.hom.toAlgebra
  let : Algebra.IsUnramifiedAt R Q.asIdeal := h
  let P : PrimeSpectrum R := PrimeSpectrum.comap β.hom Q
  let : Q.asIdeal.LiesOver P.asIdeal := ⟨rfl⟩
  let : Algebra (Localization.AtPrime P.asIdeal) (Localization.AtPrime Q.asIdeal) :=
    Localization.AtPrime.algebraOfLiesOver P.asIdeal Q.asIdeal
  have hl : (Localization.localRingHom P.asIdeal Q.asIdeal β.hom rfl).FormallyUnramified := by
    change Algebra.FormallyUnramified (Localization.AtPrime P.asIdeal) (Localization.AtPrime Q.asIdeal)
    infer_instance
  rw [← Scheme.localRingHom_comp_stalkIso β Q]
  exact (RingHom.FormallyUnramified.respectsIso.cancel_left_isIso (Spec.stalkIso R P).hom
    (CommRingCat.ofHom (Localization.localRingHom P.asIdeal Q.asIdeal β.hom rfl) ≫ (Spec.stalkIso S Q).inv)).mpr
      ((RingHom.FormallyUnramified.respectsIso.cancel_right_isIso
        (CommRingCat.ofHom (Localization.localRingHom P.asIdeal Q.asIdeal β.hom rfl)) (Spec.stalkIso S Q).inv).mpr hl)

/-- A literal actual affine source/target chart triangle carries native original chart-prime unramifiedness to the SAME original scheme stalk map. -/
theorem stalkMap_formallyUnramified_of_chart
    {X Y : Scheme.{u}} (f : X ⟶ Y) {R S : CommRingCat.{u}}
    (a : Spec S ⟶ X) [IsOpenImmersion a] (b : Spec R ⟶ Y) [IsOpenImmersion b]
    (β : R ⟶ S) (htriangle : a ≫ f = Spec.map β ≫ b) (Q : PrimeSpectrum S)
    (h : letI := β.hom.toAlgebra; Algebra.IsUnramifiedAt R Q.asIdeal) :
    (f.stalkMap (a Q)).hom.FormallyUnramified := by
  have hβ := spec_stalkMap_formallyUnramified_of_isUnramifiedAt β Q h
  have hc : ((a ≫ f).stalkMap Q).hom.FormallyUnramified := by
    rw [htriangle, Scheme.Hom.stalkMap_comp]
    exact (RingHom.FormallyUnramified.respectsIso.cancel_left_isIso
      (b.stalkMap ((Spec.map β) Q)) ((Spec.map β).stalkMap Q)).mpr hβ
  have hc' : (f.stalkMap (a Q) ≫ a.stalkMap Q).hom.FormallyUnramified := by
    simpa only [Scheme.Hom.stalkMap_comp] using hc
  exact (RingHom.FormallyUnramified.respectsIso.cancel_right_isIso
    (f.stalkMap (a Q)) (a.stalkMap Q)).mp hc'

variable (k : Type u) [Field k] (n : ℕ)
  {X : Scheme.{u}} (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]
  (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
  (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
  (s : Spec (CommRingCat.of k) ⟶ X)
  (hs : (s ≫ i) ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
  (hdim : topologicalKrullDim X ≤ n)
  (hx : s (⊥ : PrimeSpectrum k) ∈ (i ≫ projectiveSpaceStructure k (n + 1)).smoothLocus)

/-- The original geometric source, actual original rational smooth point and actual outside rational centre in the internally computed tangent open produce genuine formal unramifiedness of the SAME frozen original finite scheme projection on the SAME actual original source stalk. -/
theorem projectionFromPoint_stalkMap_formallyUnramified
    (hout : pointImage k n p ∉ Set.range i)
    (hc : pointImage k n p ∈ originalTangentOpen k n i s hs hdim hx) :
    ((projectionFromPoint k n p hp i hout).stalkMap (s (⊥ : PrimeSpectrum k))).hom.FormallyUnramified := by
  obtain ⟨j, Q, hQ, hAt⟩ := exists_original_projection_source_chart_isUnramifiedAt k n i p hp s hs hdim hx hout hc
  let i' := i ≫ (coordinateAutomorphism k n (pointVector k n p hp) (pointVector_ne_zero k n p hp)).hom
  have hout' : centrePoint k n ∉ Set.range i' := transformedInclusion_centre_outside k n i
    (pointVector k n p hp) (pointVector_ne_zero k n p hp) (pointVector_outside k n p hp i hout)
  have ht : (tangentSourceChart_isAffine k n i' j.succ).fromSpec ≫ projectionFromPoint k n p hp i hout =
      Spec.map (CommRingCat.ofHom (originalProjectionSourceChartMap k n i p hp j)) ≫
        Proj.awayι (ProjectiveGrading k n) (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X k j)
          (by decide : 0 < (1 : ℕ)) :=
    original_closedProjection_sourceChart_triangle k n i' hout' j
  have hh := stalkMap_formallyUnramified_of_chart (projectionFromPoint k n p hp i hout)
    (tangentSourceChart_isAffine k n i' j.succ).fromSpec
    (Proj.awayι (ProjectiveGrading k n) (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X k j)
      (by decide : 0 < (1 : ℕ)))
    (CommRingCat.ofHom (originalProjectionSourceChartMap k n i p hp j)) ht Q hAt
  rw [hQ] at hh
  exact hh

end Hironaka.Geometry.ProjectiveSecant
