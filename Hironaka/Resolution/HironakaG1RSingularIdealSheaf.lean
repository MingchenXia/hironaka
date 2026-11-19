import Hironaka.Resolution.HironakaG1RSmoothLocusPullback
import Hironaka.Resolution.HironakaG1RGeometricallyReduced
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# The singular ideal sheaf under field extension (ALG14 layer F5, scheme form)

For a scheme `X` locally of finite presentation over a PERFECT field `k` (e.g. of characteristic
zero) and any field extension `L / k`, with `p : X_L = X ×_k L → X`:

  `(vanishingIdeal (Sing X)).comap p = vanishingIdeal (Sing X_L)`        (`comap_singularIdeal`)

where `Sing` is the complement of the smooth locus and `vanishingIdeal` is Mathlib's ideal sheaf of
a closed subset (`Scheme.IdealSheafData.vanishingIdeal`).  This is layer F5 of lane G1's ALG14 note
(`X.singIdeal.comap p = XL.singIdeal`, `work/hironaka-resume-20261111/G1/ALG14-R02-FINITE-GENERATION-DESCENT.md`
§3) in Mathlib's ideal-sheaf language.

Proof: the support of the pulled-back ideal is `p⁻¹ (Sing X) = Sing X_L`
(`HironakaG1RSmoothLocusPullback.preimage_smoothLocus_pullback_field`, input D3), and the
pulled-back ideal is radical because its subscheme `Sing(X)_red ×_k L` is reduced (input D1,
`HironakaG1RGeometricallyReduced.isReduced_pullback_of_perfectField`); a radical ideal sheaf is the
vanishing ideal of its support (`vanishingIdeal_support`).  General helpers:
`isReduced_subscheme_of_isRadical` (the subscheme of a radical ideal sheaf is reduced) and
`radical_ker_of_isReduced` (the kernel of a quasi-compact morphism out of a reduced scheme is
radical).

Only Mathlib and lane G1's base-change modules are imported; no named input.
Blueprint: `hironaka-g1-r-smooth-locus-base-change.tex` (node `g1r:singular-ideal-sheaf`).
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace Hironaka.HironakaG1RSingularIdealSheaf

open AlgebraicGeometry HironakaG1RSmoothLocusPullback HironakaG1RGeometricallyReduced

universe u

/-- **The subscheme of a radical ideal sheaf is reduced.** -/
theorem isReduced_subscheme_of_isRadical {X : Scheme.{u}} (I : X.IdealSheafData)
    (hI : ∀ U : X.affineOpens, (I.ideal U).IsRadical) : IsReduced I.subscheme := by
  refine @IsReduced.of_openCover _ I.subschemeCover.openCover fun (U : X.affineOpens) ↦ ?_
  change IsReduced (Spec (.of (Γ(X, U) ⧸ I.ideal U)))
  have : _root_.IsReduced (Γ(X, U) ⧸ I.ideal U) := (Ideal.isRadical_iff_quotient_reduced _).mp (hI U)
  infer_instance

/-- **The kernel of a quasi-compact morphism out of a reduced scheme is radical.** -/
theorem radical_ker_of_isReduced {W Y : Scheme.{u}} (φ : W ⟶ Y) [QuasiCompact φ] [IsReduced W] :
    φ.ker.radical = φ.ker := by
  ext U : 2
  rw [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
  refine Ideal.IsRadical.radical fun x ⟨n, hn⟩ ↦ ?_
  rw [RingHom.mem_ker] at hn ⊢
  exact IsNilpotent.eq_zero ⟨n, by rwa [map_pow] at hn⟩

variable {k L : Type u} [Field k] [Field L] [Algebra k L] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) [LocallyOfFinitePresentation f]

/-- The singular (non-smooth) locus of `f` as a closed subset. -/
def singularLocus {Y S : Scheme.{u}} (g : Y ⟶ S) [LocallyOfFinitePresentation g] :
    TopologicalSpace.Closeds Y :=
  ⟨(g.smoothLocus : Set Y)ᶜ, g.smoothLocus.isOpen.isClosed_compl⟩

/-- **The singular ideal sheaf under field extension** (`k` perfect, `L / k` any field extension):
the vanishing ideal of the singular locus of `X / k`, pulled back to `X_L = X ×_k L`, is the
vanishing ideal of the singular locus of `X_L / L`. -/
theorem comap_singularIdeal [PerfectField k] :
    (Scheme.IdealSheafData.vanishingIdeal (singularLocus f)).comap
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) =
      Scheme.IdealSheafData.vanishingIdeal
        (singularLocus (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k L))))) := by
  set g := Spec.map (CommRingCat.ofHom (algebraMap k L))
  set J := Scheme.IdealSheafData.vanishingIdeal (singularLocus f)
  -- the subscheme of `J` is reduced, hence so is its base change to `L`
  have hJ : IsReduced J.subscheme := isReduced_subscheme_of_isRadical J fun U ↦ by
    simp only [J, Scheme.IdealSheafData.vanishingIdeal_ideal]
    exact PrimeSpectrum.isRadical_vanishingIdeal _
  have hW : IsReduced (pullback (pullback.fst f g) J.subschemeι) := by
    have := isReduced_pullback_of_perfectField (J.subschemeι ≫ f) L
    exact isReduced_of_isOpenImmersion
      (pullbackSymmetry _ _ ≪≫ pullbackRightPullbackFstIso f g J.subschemeι).hom
  -- the pulled-back ideal is radical
  have hrad : (J.comap (pullback.fst f g)).radical = J.comap (pullback.fst f g) :=
    radical_ker_of_isReduced _
  rw [← hrad, ← Scheme.IdealSheafData.vanishingIdeal_support]
  congr 1
  ext1
  rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]
  change pullback.fst f g ⁻¹' (f.smoothLocus : Set X)ᶜ = ((pullback.snd f g).smoothLocus : Set _)ᶜ
  rw [Set.preimage_compl, ← preimage_smoothLocus_pullback_field f]
  rfl

end Hironaka.HironakaG1RSingularIdealSheaf
