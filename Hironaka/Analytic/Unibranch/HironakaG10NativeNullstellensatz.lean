import Hironaka.Analytic.Unibranch.HironakaG10ModelNativeNullstellensatz
import Hironaka.Analytic.Unibranch.HironakaG10DisjointFlattenerTransport
import Hironaka.Analytic.Unibranch.Resolution

/-! # Native Nullstellensatz on a reduced complex space -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10NativeNullstellensatz
open Hironaka HironakaG10PNIdealFamily HironakaG10HirIdealGerms
  HironakaIntrinsicReducedCentreOpenPullback HironakaNativePulledIdealSheaf
  HironakaActualAnalyticSubspace
open Hironaka.Analytic.Unibranch.SourceReducedComplexSpace
  Hironaka.Analytic.Unibranch.HironakaG10DisjointFlattenerTransport
  Hironaka.Analytic.Unibranch.HironakaG10ModelNativeNullstellensatz

noncomputable section

/-- The native reduced-centre ideal is contained in the radical of any
  locally finitely generated ideal family whose support lies locally in the
  given set. Both the ideal family and the centre are the original ones. -/
theorem intrinsicCentre_le_radical_of_support_subset {X : SourceReducedComplexSpace}
    (V C : Set X.obj.left) (hV : IsOpen V)
    (J : ∀ x : X.obj.left, Ideal (X.obj.left.presheaf.stalk x))
    (hJ : IsLocallyFinitelyGeneratedOn X.obj.left V J)
    (x : X.obj.left) (hxV : x ∈ V)
    (hC : ∀ᶠ y in 𝓝 x, J y ≠ ⊤ → y ∈ C) :
    intrinsicCentreStalkRange X.obj.left C x ≤ (J x).radical := by
  obtain ⟨e,⟨w,hw⟩,heV,_⟩ := LocalEmbedding.exists_domain x hV hxV
  let j := e.map
  let _ : LocallyRingedSpace.IsOpenImmersion j := e.isOpenImmersion
  change j.base w = x at hw
  rw [← hw] at hC ⊢
  let K := pullFamily j J
  have hK : IsLocallyFinitelyGenerated
      (actualSubspaceLocallyRingedSpace (n := e.dim) e.carrier) K := by
    have hh := isLocallyFinitelyGeneratedOn_pull j V J hJ
    intro y
    have hyV : j.base y ∈ V := heV ⟨y,rfl⟩
    obtain ⟨U,hyU,r,s,hs⟩ := hh y hyV
    exact ⟨U,hyU,r,s,fun z hz => hs z hz (heV ⟨z,rfl⟩)⟩
  have hwC : ∀ᶠ y in 𝓝 w, K y ≠ ⊤ → y ∈ j.base ⁻¹' C := by
    have ht : Tendsto j.base (𝓝 w) (𝓝 (j.base w)) := by
      exact j.base.hom.continuous.continuousAt.tendsto
    filter_upwards [ht.eventually hC] with y hy hyK
    apply hy
    intro htop
    apply hyK
    change Ideal.map (j.stalkMap y).hom (J (j.base y)) = ⊤
    rw [htop, Ideal.map_top]
  have hm := Hironaka.Analytic.Unibranch.HironakaG10ModelNativeNullstellensatz.intrinsicCentre_le_radical_of_support_subset
    e.analytic K hK (j.base ⁻¹' C) w hwC
  have hmap : Ideal.map (j.stalkMap w).hom (intrinsicCentreStalkRange X.obj.left C (j.base w)) =
      intrinsicCentreStalkRange (actualSubspaceLocallyRingedSpace (n := e.dim) e.carrier)
        (j.base ⁻¹' C) w := by
    exact openImmersion_pulled_stalkIdeal_eq j C w
  let _ : IsIso (j.stalkMap w) := LocallyRingedSpace.IsOpenImmersion.stalk_iso j w
  have hbij : Function.Bijective (j.stalkMap w).hom :=
    (asIso (j.stalkMap w)).commRingCatIsoToRingEquiv.bijective
  have hrad : Ideal.map (j.stalkMap w).hom
      (intrinsicCentreStalkRange X.obj.left C (j.base w)) ≤
      (Ideal.map (j.stalkMap w).hom (J (j.base w))).radical := by
    rw [hmap]
    exact hm
  have hcom : Ideal.comap (j.stalkMap w).hom
      (Ideal.map (j.stalkMap w).hom (intrinsicCentreStalkRange X.obj.left C (j.base w))) ≤
      Ideal.comap (j.stalkMap w).hom
        (Ideal.map (j.stalkMap w).hom (J (j.base w))).radical := Ideal.comap_mono hrad
  rw [Ideal.comap_radical, Ideal.comap_map_of_bijective _ hbij,
    Ideal.comap_map_of_bijective _ hbij] at hcom
  exact hcom

end
end Hironaka.Analytic.Unibranch.HironakaG10NativeNullstellensatz
