import DeJongAlterations.Geometry.BlowupProjectiveEmbeddingForms
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! Actual faithfully flat scalar pullback detects original ideal and intersection identities. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace DeJongAlterations.Geometry.FlatScalarIdealSheafDescent

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f] [IsAffineHom f]

/-- ORIGINAL actual affine sections are faithfully flat, with prime lifting produced internally. -/
theorem faithfullyFlat_app (U : Y.affineOpens) : (f.app U.1).hom.FaithfullyFlat := by
  let V : X.affineOpens := ⟨f ⁻¹ᵁ U.1, U.2.preimage f⟩
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
  refine ⟨?_, ?_⟩
  · simpa only [Scheme.Hom.app_eq_appLE] using f.flat_appLE U.2 V.2 le_rfl
  · intro P
    obtain ⟨x, hx⟩ := f.surjective (U.2.fromSpec P)
    have hxV : x ∈ V.1 := by
      change f x ∈ U.1
      rw [hx]
      exact U.2.range_fromSpec.le (Set.mem_range_self P)
    let Q := V.2.primeIdealOf ⟨x, hxV⟩
    refine ⟨Q, ?_⟩
    have hprime : Q.comap (f.app U.1).hom = U.2.primeIdealOf ⟨f x, hxV⟩ := by
      simpa only [Scheme.Hom.app_eq_appLE] using
        IsAffineOpen.comap_primeIdealOf_appLE U.1 U.2 V.1 V.2 le_rfl hxV
    change Q.comap (f.app U.1).hom = P
    rw [hprime]
    apply U.2.fromSpec.isOpenEmbedding.injective
    rw [U.2.fromSpec_primeIdealOf]
    exact hx

/-- The SAME original ideal sheaf is recovered from its actual scalar pullback. -/
theorem map_comap_eq (I : Y.IdealSheafData) : (I.comap f).map f = I := by
  ext U : 2
  rw [Scheme.IdealSheafData.ideal_map_of_isAffineHom,
    BlowupProjectiveEmbedding.ideal_comap_affine I f _ U le_rfl,
    ← Scheme.Hom.app_eq_appLE]
  let : Algebra Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) := (f.app U.1).hom.toAlgebra
  let : Module.FaithfullyFlat Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) := faithfullyFlat_app f U
  exact Ideal.comap_map_eq_self_of_faithfullyFlat (I.ideal U)

/-- Actual scalar pullback detects EVERY original ideal-sheaf identity; no injectivity is assumed. -/
theorem comap_injective : Function.Injective (fun I : Y.IdealSheafData => I.comap f) := by
  intro I J h
  have hh := congrArg (fun K : X.IdealSheafData => K.map f) h
  simpa only [map_comap_eq] using hh

/-- The ENTIRE original defining ideal follows from the actual closed-immersion scalar square. -/
theorem ker_comap_of_isPullback {Z' Z Y' Y : Scheme.{u}}
    {gZ : Z' ⟶ Z} {a' : Z' ⟶ Y'} {a : Z ⟶ Y} {gY : Y' ⟶ Y}
    (H : IsPullback gZ a' a gY) [IsClosedImmersion a] : a.ker.comap gY = a'.ker := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion a gY,
    ← Scheme.Hom.ker_comp_of_isIso H.flip.isoPullback.hom (pullback.fst gY a),
    IsPullback.isoPullback_hom_fst]

end DeJongAlterations.Geometry.FlatScalarIdealSheafDescent
