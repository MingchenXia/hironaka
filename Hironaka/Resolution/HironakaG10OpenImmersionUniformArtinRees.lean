import Hironaka.Resolution.HironakaG10PNIdealFamily
import Hironaka.Resolution.HironakaG10RegularCentreUniformArtinRees

/-!
# Uniform Artin–Rees bounds and open immersions

A bound for the full pulled stalk ideals on a neighbourhood descends unchanged
through the stalk isomorphisms of an open immersion.
-/

set_option autoImplicit false
open Set CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped Topology

namespace Hironaka.HironakaG10OpenImmersionUniformArtinRees

open HironakaG10PNIdealFamily HironakaG10ChowUniformArtinRees
  HironakaG10RegularCentreUniformArtinRees

universe u

variable {X Y : LocallyRingedSpace.{u}} (f : Y ⟶ X)

/-- An open immersion transports a locally uniform bound for the actual
pulled ideals back to the open image, with the same exponent. -/
theorem exists_uniform_artinRees_of_openImmersion
    [hf : LocallyRingedSpace.IsOpenImmersion f]
    (I K : ∀ x : X, Ideal (X.presheaf.stalk x)) (y : Y)
    (h : ∃ α : ℕ, ∃ O : Set Y, IsOpen O ∧ y ∈ O ∧ ∀ z ∈ O,
      IsArtinReesNumber (pullFamily f I z) (pullFamily f K z) α) :
    ∃ α : ℕ, ∃ O : Set X, IsOpen O ∧ f.base y ∈ O ∧ ∀ x ∈ O,
      IsArtinReesNumber (I x) (K x) α := by
  obtain ⟨α,O,hO,hyO,hAR⟩ := h
  refine ⟨α,f.base '' O,hf.base_open.isOpenMap _ hO,⟨y,hyO,rfl⟩,?_⟩
  rintro x ⟨z,hz,rfl⟩
  let e := (asIso (f.stalkMap z)).commRingCatIsoToRingEquiv
  have he := isArtinReesNumber_map_ringEquiv e.symm (hAR z hz)
  change IsArtinReesNumber
    (Ideal.map e.symm.toRingHom (Ideal.map e.toRingHom (I (f.base z))))
    (Ideal.map e.symm.toRingHom (Ideal.map e.toRingHom (K (f.base z)))) α at he
  simpa only [Ideal.map_map, RingEquiv.symm_toRingHom_comp_toRingHom,
    Ideal.map_id] using he

end Hironaka.HironakaG10OpenImmersionUniformArtinRees
