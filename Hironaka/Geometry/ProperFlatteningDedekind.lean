import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Native flatness of dominant integral families over a Dedekind base

The original dominant morphism from an integral scheme is already flat over
an affine Dedekind domain. This includes positive-dimensional proper families,
without a supplied flatness or modification certificate. It is a genuine
special case of the family-flattening step, not the arbitrary-base theorem.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.ProperFlatteningDedekind

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem flat_specMap_of_dominant (R : Type u) [CommRing R] [IsDedekindDomain R]
    {S : CommRingCat.{u}} (φ : CommRingCat.of R ⟶ S) (hS : IsIntegral (Spec S))
    [IsDominant (Spec.map φ)] : Flat (Spec.map φ) := by
  let : IsDomain S := (affine_isIntegral_iff S).mp hS
  have hφ : Function.Injective φ.hom := by
    rw [RingHom.injective_iff_ker_eq_bot]
    apply le_antisymm ?_ bot_le
    have h : RingHom.ker φ.hom ≤ nilradical R :=
      (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ.hom).mp
        (Spec.map φ).denseRange
    simpa only [nilradical_eq_zero, Ideal.zero_eq_bot] using h
  rw [Flat.SpecMap_iff]
  let : Algebra R S := φ.hom.toAlgebra
  let : Module.IsTorsionFree R S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hφ
  change Module.Flat R S
  infer_instance

/-- A dominant morphism from an integral scheme to the spectrum of a Dedekind
 domain is natively flat, with no finite-type or relative-dimension restriction. -/
theorem flat_of_dominant_to_spec (R : Type u) [CommRing R] [IsDedekindDomain R]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of R)) [IsDominant f] : Flat f := by
  let 𝒰 : Scheme.OpenCover X :=
    { I₀ := X
      X x := X.affineCover.X (X.affineCover.idx x)
      f x := X.affineCover.f (X.affineCover.idx x)
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨fun x ↦ ⟨x, X.affineCover.covers x⟩, inferInstance⟩ }
  apply (IsZariskiLocalAtSource.iff_of_openCover 𝒰).mpr
  intro i
  have hne : Nonempty (𝒰.X i) := by
    obtain ⟨x, hx⟩ := X.affineCover.covers i
    exact ⟨x⟩
  let : IsIntegral (𝒰.X i) := isIntegral_of_isOpenImmersion (𝒰.f i)
  let : IsDominant (𝒰.f i) := by
    constructor
    exact (IsOpenImmersion.isOpen_range (𝒰.f i)).dense
      ⟨𝒰.f i (Classical.choice hne), ⟨_, rfl⟩⟩
  let g := 𝒰.f i ≫ f
  let φ := Spec.preimage g
  let : IsDominant (Spec.map φ) := by
    rw [Spec.map_preimage]
    change IsDominant g
    dsimp only [g]
    infer_instance
  change Flat g
  rw [← Spec.map_preimage g]
  exact flat_specMap_of_dominant R φ (by
    change IsIntegral (𝒰.X i)
    infer_instance)

end Hironaka.Geometry.ProperFlatteningDedekind
