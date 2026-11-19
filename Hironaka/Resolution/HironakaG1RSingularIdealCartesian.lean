import Hironaka.Resolution.HironakaG1RSingularIdealSheaf

/-!
# The singular ideal sheaf along a cartesian square over a field extension (ALG14 layer F5)

`HironakaG1RSingularIdealSheaf.comap_singularIdeal` is stated for the canonical pullback
`X ×_k L`.  The ALG14 target (`CommutesWithChangeOfFields`, lane G1's note
`work/hironaka-resume-20261111/G1/ALG14-R02-FINITE-GENERATION-DESCENT.md`) is phrased with an
ARBITRARY cartesian square `IsPullback p fL f (Spec.map σ)`.  This module states F5 in that form,
for schemes locally of FINITE TYPE over a perfect field (the hypotheses of the dependency's
`Scheme.singIdeal`, whose support is `(f.smoothLocus)ᶜ` there):

  `(vanishingIdeal (Sing X)).comap p = vanishingIdeal (Sing X_L)`   (`comap_singularIdeal_of_isPullback`).

Only Mathlib and lane G1's modules are imported; no named input.
Blueprint: `hironaka-g1-r-smooth-locus-base-change.tex` (node `g1r:singular-ideal-cartesian`).
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace Hironaka.HironakaG1RSingularIdealCartesian

open AlgebraicGeometry HironakaG1RSmoothLocusPullback HironakaG1RGeometricallyReduced
  HironakaG1RSingularIdealSheaf

universe u

/-- **The singular ideal sheaf along a cartesian square over a field extension.**  Let `k` be a
perfect field, `L / k` a field extension, `f : X → Spec k` and `fL : X_L → Spec L` locally of finite
type, and `p : X_L → X` such that the square `p, fL, f, Spec(k → L)` is cartesian.  Then the
pull-back along `p` of the vanishing ideal sheaf of the singular locus of `X` is the vanishing ideal
sheaf of the singular locus of `X_L`. -/
theorem comap_singularIdeal_of_isPullback {k L : Type u} [Field k] [PerfectField k] [Field L]
    [Algebra k L] {X XL : Scheme.{u}} {f : X ⟶ Spec (.of k)} {fL : XL ⟶ Spec (.of L)}
    {p : XL ⟶ X} [LocallyOfFiniteType f] [LocallyOfFiniteType fL]
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :
    (Scheme.IdealSheafData.vanishingIdeal (singularLocus f)).comap p =
      Scheme.IdealSheafData.vanishingIdeal (singularLocus fL) := by
  set g := Spec.map (CommRingCat.ofHom (algebraMap k L))
  have : Flat g := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  set J := Scheme.IdealSheafData.vanishingIdeal (singularLocus f)
  have hJ : IsReduced J.subscheme := isReduced_subscheme_of_isRadical J fun U ↦ by
    simp only [J, Scheme.IdealSheafData.vanishingIdeal_ideal]
    exact PrimeSpectrum.isRadical_vanishingIdeal _
  have hsq : IsPullback (pullback.snd p J.subschemeι) (pullback.fst p J.subschemeι ≫ fL)
      (J.subschemeι ≫ f) g :=
    (IsPullback.of_hasPullback p J.subschemeι).flip.paste_vert h
  have hW : IsReduced (pullback p J.subschemeι) := by
    have := isReduced_pullback_of_perfectField (J.subschemeι ≫ f) L
    exact isReduced_of_isOpenImmersion hsq.isoPullback.hom
  have hrad : (J.comap p).radical = J.comap p := radical_ker_of_isReduced _
  rw [← hrad, ← Scheme.IdealSheafData.vanishingIdeal_support]
  congr 1
  ext1
  rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]
  change p ⁻¹' (f.smoothLocus : Set X)ᶜ = (fL.smoothLocus : Set XL)ᶜ
  rw [Set.preimage_compl, ← preimage_smoothLocus_of_isPullback h]
  rfl

end Hironaka.HironakaG1RSingularIdealCartesian
