import DeJongAlterations.Algebra.FaithfullyFlatCartierEquation
import DeJongAlterations.Geometry.FlatScalarIdealSheafDescent
import DeJongAlterations.Geometry.ProjectiveIdealStalk
import DeJongAlterations.Geometry.SNCSubdivisorAffine
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.Localization

/-! Genuine Cartier equations descend along the actual flat surjective affine scalar projection. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace DeJongAlterations.Geometry.FlatScalarCartierDescent

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{u}}

/-- The intrinsic actual pullback stalk ideal is the entire extension along the ORIGINAL stalk map. -/
theorem stalkIdeal_comap (f : X ⟶ Y) [IsAffineHom f] (D : Y.IdealSheafData) (x : X) :
    (D.comap f).stalkIdeal x = (D.stalkIdeal (f x)).map (f.stalkMap x).hom := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := f x) (U := (⊤ : Y.Opens)) trivial
  let V : X.affineOpens := ⟨f ⁻¹ᵁ U, hU.preimage f⟩
  rw [Scheme.IdealSheafData.stalkIdeal_eq_affine (D.comap f) x V hxU,
    Scheme.IdealSheafData.stalkIdeal_eq_affine D (f x) ⟨U, hU⟩ hxU,
    BlowupProjectiveEmbedding.ideal_comap_affine D f V ⟨U, hU⟩ le_rfl,
    Ideal.map_map, Ideal.map_map]
  have hφ : f.appLE U V.1 le_rfl = f.app U := by
    change f.app U ≫ X.presheaf.map (𝟙 _).op = f.app U
    simp
  rw [hφ, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, f.germ_stalkMap]

private theorem regular_germ {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Flat R S] {t : R} (ht : IsRegular t) :
    IsRegular (algebraMap R S t) := by
  have h := Module.Flat.isSMulRegular_of_isRegular (M := S) ht
  constructor
  · intro a b hab
    apply h
    simpa only [Algebra.smul_def] using hab
  · intro a b hab
    apply h
    simpa only [Algebra.smul_def, mul_comm] using hab

/-- Genuine Cartier affine equations give actual regular generators of their intrinsic stalk ideals. -/
theorem stalk_equations (D : X.IdealSheafData) (hD : IsEffectiveCartierDivisor D) (x : X) :
    ∃ b : X.presheaf.stalk x, IsRegular b ∧ D.stalkIdeal x = Ideal.span {b} := by
  obtain ⟨U, hx, t, ht, hI⟩ := hD x
  let := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  let : IsLocalization.AtPrime (X.presheaf.stalk x) (U.2.primeIdealOf ⟨x, hx⟩).asIdeal :=
    U.2.isLocalization_stalk ⟨x, hx⟩
  let : Module.Flat Γ(X, U.1) (X.presheaf.stalk x) :=
    IsLocalization.flat _ (U.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  refine ⟨algebraMap Γ(X, U.1) (X.presheaf.stalk x) t, regular_germ ht, ?_⟩
  rw [Scheme.IdealSheafData.stalkIdeal_eq_affine D x U hx, hI, Ideal.map_span,
    Set.image_singleton]
  rfl

/-- Actual regular stalk generators INTERNALLY spread to genuine affine Cartier neighborhoods. -/
theorem of_stalk_equations [IsLocallyNoetherian X] (D : X.IdealSheafData)
    (hD : ∀ x : X, ∃ b : X.presheaf.stalk x, IsRegular b ∧
      D.stalkIdeal x = Ideal.span {b}) : IsEffectiveCartierDivisor D := by
  intro x
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := x) (U := (⊤ : X.Opens)) trivial
  let A := Γ(X, U)
  let I := D.ideal ⟨U, hU⟩
  let : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hc : IsEffectiveCartierDivisor (D.comap hU.fromSpec) := by
    rw [BlowupCartier.comap_fromSpec D ⟨U, hU⟩]
    apply SNCSubdivisorAffine.isEffectiveCartierDivisor_of_local_equations
    intro p hp
    let q : PrimeSpectrum A := ⟨p, hp⟩
    let y := hU.fromSpec q
    have hy : y ∈ U := hU.range_fromSpec.le (Set.mem_range_self q)
    let := X.presheaf.algebra_section_stalk ⟨y, hy⟩
    let : IsLocalization.AtPrime (X.presheaf.stalk y) p := hU.isLocalization_stalk' q hy
    let e := IsLocalization.algEquiv p.primeCompl (X.presheaf.stalk y)
      (Localization.AtPrime p)
    obtain ⟨b, hb, hspan⟩ := hD y
    refine ⟨e b, CartierLocality.isRegular_ringEquiv e.toRingEquiv hb, ?_⟩
    rw [Scheme.IdealSheafData.stalkIdeal_eq_affine D y ⟨U, hU⟩ hy] at hspan
    have hh := congrArg (Ideal.map e.toRingHom) hspan
    rw [Ideal.map_map, Ideal.map_span, Set.image_singleton] at hh
    have hφ : e.toRingHom.comp (X.presheaf.germ U y hy).hom =
        algebraMap A (Localization.AtPrime p) := by
      ext a
      exact e.commutes a
    rw [hφ] at hh
    exact hh
  let q := hU.primeIdealOf ⟨x, hxU⟩
  have hh := CartierLocality.exists_affine_neighborhood_of_isOpenImmersion
    hU.fromSpec D hc q
  simpa only [q, hU.fromSpec_primeIdealOf] using hh

/-- The original scalar Cartier equation descends without ANY supplied descended equation. -/
theorem of_flat_surjective_affine [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [Flat f] [Surjective f] [IsAffineHom f] (D : Y.IdealSheafData)
    (hD : IsEffectiveCartierDivisor (D.comap f)) : IsEffectiveCartierDivisor D := by
  apply of_stalk_equations D
  intro y
  obtain ⟨x, rfl⟩ := f.surjective y
  let : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  let : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f x) (f.toLRSHom.prop x)
  obtain ⟨b, hb, hspan⟩ := stalk_equations (D.comap f) hD x
  rw [stalkIdeal_comap] at hspan
  obtain ⟨a, _, ha, hI⟩ :=
    Algebra.FaithfullyFlatCartierEquation.exists_regular_generator (D.stalkIdeal (f x)) b hb hspan
  exact ⟨a, ha, hI⟩

end DeJongAlterations.Geometry.FlatScalarCartierDescent
