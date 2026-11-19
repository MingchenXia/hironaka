import Hironaka.Resolution.HironakaG1RSingularIdealSheaf

/-!
# Vanishing ideal sheaves under field extension (ALG14 input D1, ideal-sheaf form)

For a perfect field `k`, a field extension `L / k`, ANY `k`-scheme `X` and ANY cartesian square
`IsPullback p fL f (Spec.map (k → L))` (so `X_L = X ×_k L`), and every closed subset `Z ⊆ X`:

  `(vanishingIdeal Z).comap p = vanishingIdeal (p⁻¹ Z)`          (`comap_vanishingIdeal_of_isPullback`),

i.e. the reduced induced subscheme on `Z` base-changes to the reduced induced subscheme on `p⁻¹ Z`
(the "reduced preimage" input D1 of lane G1's ALG14 note, §3, in Mathlib's ideal-sheaf language;
no finiteness hypothesis is needed).  Since pulling back ideal sheaves preserves suprema
(`comap_iSup_vanishingIdeal_of_isPullback`), every ideal sheaf that is a supremum of vanishing
ideals of closed sets — e.g. the dependency's `separationIdeal X = ⨆ d, vanishingIdeal
(complementaryClosed X d)` (layer F1) — pulls back to the supremum of the vanishing ideals of the
preimages; F1 is thereby reduced to the set-level identity
`complementaryClosed X_L d = p⁻¹ (complementaryClosed X d)` (layer F2, component dimensions).

Only Mathlib and lane G1's modules are imported; no named input.
Blueprint: `hironaka-g1-r-smooth-locus-base-change.tex` (node `g1r:vanishing-ideal-base-change`).
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace Hironaka.HironakaG1RVanishingIdealBaseChange

open AlgebraicGeometry HironakaG1RGeometricallyReduced HironakaG1RSingularIdealSheaf

universe u

variable {k L : Type u} [Field k] [PerfectField k] [Field L] [Algebra k L] {X XL : Scheme.{u}}
  {f : X ⟶ Spec (.of k)} {fL : XL ⟶ Spec (.of L)} {p : XL ⟶ X}

/-- **Reduced preimages under field extension** (`k` perfect): the vanishing ideal sheaf of a
closed subset `Z ⊆ X` pulls back along `p : X_L → X` to the vanishing ideal sheaf of `p⁻¹ Z`. -/
theorem comap_vanishingIdeal_of_isPullback
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    (Z : TopologicalSpace.Closeds X) :
    (Scheme.IdealSheafData.vanishingIdeal Z).comap p =
      Scheme.IdealSheafData.vanishingIdeal (Z.preimage p.continuous) := by
  set J := Scheme.IdealSheafData.vanishingIdeal Z
  have hJ : IsReduced J.subscheme := isReduced_subscheme_of_isRadical J fun U ↦ by
    simp only [J, Scheme.IdealSheafData.vanishingIdeal_ideal]
    exact PrimeSpectrum.isRadical_vanishingIdeal _
  have hsq : IsPullback (pullback.snd p J.subschemeι) (pullback.fst p J.subschemeι ≫ fL)
      (J.subschemeι ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap k L))) :=
    (IsPullback.of_hasPullback p J.subschemeι).flip.paste_vert h
  have hW : IsReduced (pullback p J.subschemeι) := by
    have := isReduced_pullback_of_perfectField (J.subschemeι ≫ f) L
    exact isReduced_of_isOpenImmersion hsq.isoPullback.hom
  have hrad : (J.comap p).radical = J.comap p := radical_ker_of_isReduced _
  rw [← hrad, ← Scheme.IdealSheafData.vanishingIdeal_support]
  congr 1
  ext1
  rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
    Scheme.IdealSheafData.coe_support_vanishingIdeal, TopologicalSpace.Closeds.coe_preimage]

/-- **Suprema of vanishing ideals under field extension** (`k` perfect). -/
theorem comap_iSup_vanishingIdeal_of_isPullback
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    {ι : Sort*} (Z : ι → TopologicalSpace.Closeds X) :
    (⨆ i, Scheme.IdealSheafData.vanishingIdeal (Z i)).comap p =
      ⨆ i, Scheme.IdealSheafData.vanishingIdeal ((Z i).preimage p.continuous) := by
  rw [(Scheme.IdealSheafData.map_gc p).l_iSup]
  exact iSup_congr fun i ↦ comap_vanishingIdeal_of_isPullback h (Z i)

end Hironaka.HironakaG1RVanishingIdealBaseChange
