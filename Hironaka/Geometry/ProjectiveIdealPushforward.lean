/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
/- Reused from EnvelopeProperty/Berkovich/SchemeIdealExtension.lean; SHA256 c69bef2abc83bc1222a84546d251776b4b20ffd61461dee0ea6ca010ebf8b3ed. -/


/-!
# True ideal extension along genuine closed immersions

Use the existing actual geometric ideal pushforward. Its original ideal
subscheme composite has a genuine pullback square by monomorphism cancellation;
the true pullback-kernel theorem proves entire pullback retraction. No ideal,
stalk, generator, Noetherian or representation certificate is an input.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u
namespace AlgebraicGeometry.Scheme.IdealSheafData
variable {Z Y : Scheme.{u}}

/-- The original ideal subscheme has a true whole scheme pullback square along the genuine embedding. -/
theorem isPullback_subscheme_comp_of_isClosedImmersion
    (I : Z.IdealSheafData) (j : Z ⟶ Y) [IsClosedImmersion j] :
    IsPullback (𝟙 I.subscheme) I.subschemeι (I.subschemeι ≫ j) j := by
  exact IsPullback.of_horiz_isIso_mono ⟨by simp⟩

/-- Actual ideal extension along a genuine closed immersion retracts to the ENTIRE original ideal sheaf. -/
theorem comap_map_of_isClosedImmersion
    (I : Z.IdealSheafData) (j : Z ⟶ Y) [IsClosedImmersion j] :
    (I.map j).comap j = I := by
  have h := (isPullback_subscheme_comp_of_isClosedImmersion I j).flip
  rw [map, ← ker_fst_of_isClosedImmersion (I.subschemeι ≫ j) j,
    ← Scheme.Hom.ker_comp_of_isIso h.isoPullback.hom (pullback.fst j (I.subschemeι ≫ j)),
    h.isoPullback_hom_fst, ker_subschemeι]

/-- The genuine ambient kernel of the original ideal subscheme composite pulls back to the full original ideal. -/
theorem comap_ker_subscheme_comp_of_isClosedImmersion
    (I : Z.IdealSheafData) (j : Z ⟶ Y) [IsClosedImmersion j] :
    (I.subschemeι ≫ j).ker.comap j = I :=
  comap_map_of_isClosedImmersion I j

/-- Every original source ideal has a genuinely constructed entire ambient ideal extension under a real closed immersion. -/
theorem exists_idealSheaf_comap_eq_of_isClosedImmersion
    (I : Z.IdealSheafData) (j : Z ⟶ Y) [IsClosedImmersion j] :
    ∃ J : Y.IdealSheafData, J.comap j = I :=
  ⟨I.map j, comap_map_of_isClosedImmersion I j⟩

end AlgebraicGeometry.Scheme.IdealSheafData
