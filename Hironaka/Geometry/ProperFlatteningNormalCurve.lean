import Hironaka.Geometry.ProperFlatteningDedekind
import Hironaka.Geometry.NormalCurveModification
import Hironaka.Geometry.NormalizationFinite

/-!
# Dominant integral families over normal curves are natively flat

The base is the original normal locally Noetherian integral scheme of dimension
at most one. Its actual affine coordinate rings are internally shown Dedekind;
flatness is derived for the original morphism in arbitrary relative dimension.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.ProperFlatteningDedekind

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The original nonempty affine coordinates of a normal locally Noetherian
 integral scheme of dimension at most one form a Dedekind domain. -/
theorem affineSections_isDedekindDomain {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] (hnormal : IsNormalScheme Y)
    (hdim : topologicalKrullDim Y ≤ 1) (U : Y.affineOpens) [Nonempty U.1] :
    IsDedekindDomain Γ(Y, U.1) := by
  let : IsDomain Γ(Y, U.1) := IsIntegral.component_integral U.1
  let : IsNoetherianRing Γ(Y, U.1) := IsLocallyNoetherian.component_noetherian U
  let : IsIntegrallyClosed Γ(Y, U.1) :=
    NormalCurveModification.affineSections_isIntegrallyClosed hnormal U.1 U.2
  let : Ring.KrullDimLE 1 Γ(Y, U.1) :=
    NormalizationFinite.affineSections_krullDimLE_one U hdim
  let : Ring.DimensionLEOne Γ(Y, U.1) := ⟨fun _ hP ↦ hP.isMaximal_of_ne_bot ‹_›⟩
  let : IsDedekindRing Γ(Y, U.1) := .mk
  exact .mk

/-- Dominance from an integral scheme to the original normal locally Noetherian
 integral base of dimension at most one forces native flatness everywhere. -/
theorem flat_of_dominant_normal_curve {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] (hnormal : IsNormalScheme Y)
    (hdim : topologicalKrullDim Y ≤ 1) (f : X ⟶ Y) [IsDominant f] : Flat f := by
  apply (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @Flat)
    (fun U : Y.affineOpens ↦ U.1) (iSup_affineOpens_eq_top Y)).mpr
  intro U
  by_cases hne : Nonempty U.1
  · let := hne
    have hpre : Nonempty (f ⁻¹ᵁ U.1) := by
      obtain ⟨x, hx⟩ := f.denseRange.exists_mem_open U.1.isOpen (Set.nonempty_coe_sort.mp hne)
      exact ⟨⟨x, hx⟩⟩
    let := hpre
    let : IsIntegral (f ⁻¹ᵁ U.1).toScheme := isIntegral_of_isOpenImmersion (f ⁻¹ᵁ U.1).ι
    let : IsDominant (f ∣_ U.1) := IsZariskiLocalAtTarget.restrict (P := @IsDominant)
      (inferInstance : IsDominant f) U.1
    let : IsDedekindDomain Γ(Y, U.1) := affineSections_isDedekindDomain hnormal hdim U
    have hflat : Flat ((f ∣_ U.1) ≫ U.2.isoSpec.hom) :=
      flat_of_dominant_to_spec Γ(Y, U.1) _
    exact (MorphismProperty.cancel_right_of_respectsIso @Flat _ U.2.isoSpec.hom).mp hflat
  · let : IsEmpty U.1.toScheme := not_nonempty_iff.mp hne
    let : IsIso (f ∣_ U.1) := isIso_of_isEmpty (f ∣_ U.1)
    infer_instance

end Hironaka.Geometry.ProperFlatteningDedekind
