import DeJongAlterations.Geometry.ProjectiveSecantFlatComponents
import Mathlib.Topology.NoetherianSpace

/-!
# Actual dense source opens descend under integral maps
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.IntegralDenseOpenDescent

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem prime_eq_of_le_of_comap_eq {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IsIntegral) {P Q : PrimeSpectrum S}
    (hPQ : P ≤ Q) (hmap : PrimeSpectrum.comap f P = PrimeSpectrum.comap f Q) : P = Q := by
  let := f.toAlgebra
  by_contra hne
  obtain ⟨t, htQ, htP⟩ := SetLike.exists_of_lt (show P.asIdeal < Q.asIdeal from
    lt_of_le_of_ne hPQ (fun h => hne (PrimeSpectrum.ext h)))
  have hlt := Ideal.comap_lt_comap_of_integral_mem_sdiff (R := R) hPQ ⟨htQ, htP⟩ (hf t)
  exact hlt.ne (congrArg PrimeSpectrum.asIdeal hmap)

/-- Two comparable ORIGINAL points of an integral morphism with the same image coincide. -/
theorem eq_of_specializes_of_image_eq {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f]
    {x y : X} (hxy : x ⤳ y) (hf : f x = f y) : x = y := by
  obtain ⟨U, hU, hyU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show f y ∈ (⊤ : Y.Opens) from trivial)
  let hV := hU.preimage f
  have hxU : f x ∈ U := hf ▸ hyU
  have hxV : x ∈ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    exact hxU
  have hyV : y ∈ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    exact hyU
  obtain ⟨P, rfl⟩ := hxV
  obtain ⟨Q, rfl⟩ := hyV
  have ht : hV.fromSpec ≫ f = Spec.map (f.app U) ≫ hU.fromSpec := by
    simpa only [Scheme.Hom.app_eq_appLE] using
      (IsAffineOpen.SpecMap_appLE_fromSpec f hU hV le_rfl).symm
  have hPQ : P.asIdeal ≤ Q.asIdeal := (PrimeSpectrum.le_iff_specializes P Q).mpr
    (hV.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp hxy)
  have hmap : PrimeSpectrum.comap (f.app U).hom P =
      PrimeSpectrum.comap (f.app U).hom Q := by
    apply hU.fromSpec.isOpenEmbedding.injective
    have hP := congrArg (fun g : Spec Γ(X, f ⁻¹ᵁ U) ⟶ Y => g P) ht
    have hQ := congrArg (fun g : Spec Γ(X, f ⁻¹ᵁ U) ⟶ Y => g Q) ht
    exact hP.symm.trans (hf.trans hQ)
  exact congrArg hV.fromSpec (prime_eq_of_le_of_comap_eq
    (f.app U).hom (f.isIntegral_app U hU) hPQ hmap)

/-- The actual source point above a component generic point is itself an actual component generic point. -/
theorem exists_component_genericPoint_of_image_generic {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIntegralHom f] {C : Set Y}
    (hC : C ∈ irreducibleComponents Y) {η : Y} (hη : IsGenericPoint η C)
    (x : X) (hx : f x = η) :
    ∃ D ∈ irreducibleComponents X, IsGenericPoint x D := by
  let D := irreducibleComponent x
  have hD : D ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents x
  let ξ := (genericPoints.ofComponent ⟨D, hD⟩).val
  have hξ : IsGenericPoint ξ D := genericPoints.isGenericPoint_ofComponent ⟨D, hD⟩
  have hspec : ξ ⤳ x := hξ.specializes mem_irreducibleComponent
  have hmap : f ξ = f x := by
    rw [hx]
    apply (ProjectiveSecant.eq_of_specializes_component_generic hC hη)
    simpa only [hx] using f.base.hom.map_specializes hspec
  have heq := eq_of_specializes_of_image_eq f hspec hmap
  exact ⟨D, hD, heq ▸ hξ⟩

/-- A Noetherian dense open contains every actual component generic point. -/
theorem genericPoint_mem_of_dense_open {X : Type u} [TopologicalSpace X]
    [NoetherianSpace X] {D : Set X} (hD : D ∈ irreducibleComponents X)
    {η : X} (hη : IsGenericPoint η D) (U : Opens X) (hU : Dense (U : Set X)) : η ∈ U := by
  obtain ⟨W, hW, hWne, hWD⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent D hD
  obtain ⟨x, hxW, hxU⟩ := hU.inter_open_nonempty W hW hWne
  exact (hη.specializes (hWD hxW)).mem_open U.isOpen hxU

/-- The SAME original complement of the actual closed image of the bad source set. -/
def descendedOpen {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] (U : X.Opens) : Y.Opens :=
  ⟨(f '' (U : Set X)ᶜ)ᶜ, (f.isClosedMap _ U.isOpen.isClosed_compl).isOpen_compl⟩

/-- The entire original inverse image lies in the original good source open. -/
theorem preimage_descendedOpen_le {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f]
    (U : X.Opens) : f ⁻¹ᵁ descendedOpen f U ≤ U := by
  intro x hx
  by_contra hbad
  exact hx ⟨x, hbad, rfl⟩

/-- Actual integral incomparability makes the SAME closed-image complement dense. -/
theorem descendedOpen_dense {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f]
    [NoetherianSpace X] (U : X.Opens) (hU : Dense (U : Set X)) :
    Dense (descendedOpen f U : Set Y) := by
  have hgeneric {C : Set Y} (hC : C ∈ irreducibleComponents Y) {η : Y}
      (hη : IsGenericPoint η C) : η ∈ descendedOpen f U := by
    rintro ⟨x, hx, hfx⟩
    obtain ⟨D, hD, hxD⟩ := exists_component_genericPoint_of_image_generic f hC hη x hfx
    exact hx (genericPoint_mem_of_dense_open hD hxD U hU)
  intro y
  let C := irreducibleComponent y
  have hC : C ∈ irreducibleComponents Y := irreducibleComponent_mem_irreducibleComponents y
  let η := (genericPoints.ofComponent ⟨C, hC⟩).val
  have hη : IsGenericPoint η C := genericPoints.isGenericPoint_ofComponent ⟨C, hC⟩
  exact (closure_mono (Set.singleton_subset_iff.mpr (hgeneric hC hη)))
    ((hη.def.symm ▸ mem_irreducibleComponent) : y ∈ closure {η})

end DeJongAlterations.Geometry.IntegralDenseOpenDescent
