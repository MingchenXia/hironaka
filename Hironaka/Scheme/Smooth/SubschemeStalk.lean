/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.IdealSheaf.Defs
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Hironaka.Scheme.IdealSheaf.StalkIdeal

/-!
# The stalk of a closed subscheme is the quotient of the stalk by the stalk ideal

For an ideal sheaf `Z` on a scheme `X` with closed subscheme `ι : V(Z) ⟶ X` and a point
`z ∈ V(Z)` over `x = ι z`, the stalk map `ι^♯_z : 𝒪_{X,x} → 𝒪_{V(Z),z}` is surjective (a closed
immersion) with kernel the stalk `Z_x = stalkIdeal Z x` of the ideal sheaf, so
`𝒪_{V(Z),z} ≅ 𝒪_{X,x}/Z_x` (`stalkQuotientEquiv`) and the residue fields agree
(`residueFieldStalkEquiv`). This is the identification `𝒪_{Z,x} = 𝒪_{X,x}/I_x`, Kollár's "the
local ring of `Z` at `x`", used without comment throughout the sources.

Proof of the kernel formula (the local form of [Sta, Tags 01HP, 01QN]): on an affine open `U ∋ x`
the stalk `𝒪_{X,x}` is the localization `Γ(X, U)_𝔭` and `𝒪_{V(Z),z}` is the localization of
`Γ(V(Z), ι⁻¹U) = Γ(X, U)/Z(U)` at the corresponding prime `𝔮`; the stalk map is the localization
of the surjection `Γ(X, U) → Γ(X, U)/Z(U)` (Mathlib's `ker_subschemeι_app`,
`subschemeι_app_surjective`, `comap_primeIdealOf_appLE`), and the kernel of a localized map is the
localization of the kernel (`IsLocalization.ker_map`), which is `Z(U)·𝒪_{X,x} = Z_x`
(`stalkIdeal_eq_map_germ`).

Used wherever the local ring of a closed subscheme is computed from that of the ambient scheme
(`Hironaka/Scheme/Smooth/AdaptedCoordinates.lean`, `Hironaka/Snc/`, `Hironaka/Sequence/`,
`Hironaka/Resolution/`).
-/

@[expose] public section

namespace AlgebraicGeometry.Scheme.IdealSheafData

open CategoryTheory IsLocalRing TopologicalSpace

universe u

variable {X : Scheme.{u}} (Z : X.IdealSheafData)

/-- A point of the support of `Z` is the image of a point of the closed subscheme `V(Z)`. -/
theorem exists_subschemeι_eq {x : X} (hx : x ∈ Z.support) : ∃ z : Z.subscheme, Z.subschemeι z = x :=
  (Set.ext_iff.mp Z.range_subschemeι x).mpr hx

/-- The kernel of the stalk map of the closed immersion `V(Z) ⟶ X` at `z` is the stalk of `Z`
at `ι z`. -/
theorem ker_stalkMap_subschemeι (z : Z.subscheme) :
    RingHom.ker (Z.subschemeι.stalkMap z).hom = Z.stalkIdeal (Z.subschemeι z) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (Z.subschemeι z)) isOpen_univ
  replace hU : IsAffineOpen U := hU
  have hV : IsAffineOpen (Z.subschemeι ⁻¹ᵁ U) := hU.preimage Z.subschemeι
  have hzV : z ∈ Z.subschemeι ⁻¹ᵁ U := hxU
  let := X.presheaf.algebra_section_stalk ⟨Z.subschemeι z, hxU⟩
  let := Z.subscheme.presheaf.algebra_section_stalk ⟨z, hzV⟩
  have hlocX := hU.isLocalization_stalk ⟨Z.subschemeι z, hxU⟩
  have hlocZ := hV.isLocalization_stalk ⟨z, hzV⟩
  set p := (hU.primeIdealOf ⟨Z.subschemeι z, hxU⟩).asIdeal with hp
  set q := (hV.primeIdealOf ⟨z, hzV⟩).asIdeal with hq
  set g := (Z.subschemeι.app U).hom with hg
  have hgs : Function.Surjective g := Z.subschemeι_app_surjective ⟨U, hU⟩
  have hker : RingHom.ker g = Z.ideal ⟨U, hU⟩ := Z.ker_subschemeι_app ⟨U, hU⟩
  have hcomap : q.comap g = p := by
    have h := IsAffineOpen.comap_primeIdealOf_appLE U hU (Z.subschemeι ⁻¹ᵁ U) hV le_rfl hzV
    have h' := congrArg PrimeSpectrum.asIdeal h
    rw [PrimeSpectrum.comap_asIdeal] at h'
    rw [hg, Scheme.Hom.app_eq_appLE]
    exact h'
  have hT : Submonoid.map g p.primeCompl = q.primeCompl := by
    have h := Ideal.map_primeCompl_comap_of_surjective g hgs q
    convert h using 3
    exact hcomap.symm
  have hmap : (Z.subschemeι.stalkMap z).hom =
      IsLocalization.map (Z.subscheme.presheaf.stalk z) g
        (hT.symm ▸ p.primeCompl.le_comap_map) := by
    apply IsLocalization.ringHom_ext p.primeCompl
    ext s
    rw [RingHom.comp_apply, RingHom.comp_apply, IsLocalization.map_eq]
    exact Z.subschemeι.germ_stalkMap_apply U z hxU s
  rw [hmap, IsLocalization.ker_map (Q := Z.subscheme.presheaf.stalk z) (g := g) (M := p.primeCompl)
    (T := q.primeCompl) hT, hker,
    stalkIdeal_eq_map_germ Z ⟨U, hU⟩ hxU]
  rfl

/-- `𝒪_{V(Z),z} ≅ 𝒪_{X,ι z} / Z_{ι z}`: the stalk of the closed subscheme is the quotient of the
stalk of `X` by the stalk of the ideal sheaf. -/
noncomputable def stalkQuotientEquiv (z : Z.subscheme) :
    (X.presheaf.stalk (Z.subschemeι z) ⧸ Z.stalkIdeal (Z.subschemeι z)) ≃+*
      Z.subscheme.presheaf.stalk z :=
  (Ideal.quotEquivOfEq (ker_stalkMap_subschemeι Z z).symm).trans
    (RingHom.quotientKerEquivOfSurjective (Z.subschemeι.stalkMap_surjective z))

theorem stalkQuotientEquiv_mk (z : Z.subscheme) (a : X.presheaf.stalk (Z.subschemeι z)) :
    stalkQuotientEquiv Z z (Ideal.Quotient.mk _ a) = Z.subschemeι.stalkMap z a :=
  rfl

/-- The residue fields of `𝒪_{X,ι z}` and `𝒪_{V(Z),z}` agree (the stalk map is a surjective local
homomorphism). -/
noncomputable def residueFieldStalkEquiv (z : Z.subscheme) :
    ResidueField (X.presheaf.stalk (Z.subschemeι z)) ≃+*
      ResidueField (Z.subscheme.presheaf.stalk z) :=
  RingEquiv.ofBijective (ResidueField.map (Z.subschemeι.stalkMap z).hom)
    ⟨(ResidueField.map _).injective, fun b => by
      obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective b
      obtain ⟨r, rfl⟩ := Z.subschemeι.stalkMap_surjective z s
      exact ⟨IsLocalRing.residue _ r, ResidueField.map_residue _ r⟩⟩

theorem residueFieldStalkEquiv_residue (z : Z.subscheme) (r : X.presheaf.stalk (Z.subschemeι z)) :
    residueFieldStalkEquiv Z z (IsLocalRing.residue _ r) =
      IsLocalRing.residue _ (Z.subschemeι.stalkMap z r) :=
  ResidueField.map_residue _ r

/-- A closed point of `X` in the support of `Z` is a closed point of `V(Z)`. -/
theorem isClosed_singleton_of_subschemeι_eq {z : Z.subscheme} {x : X} (hzx : Z.subschemeι z = x)
    (hx : IsClosed ({x} : Set X)) : IsClosed ({z} : Set Z.subscheme) := by
  have : ({z} : Set Z.subscheme) = Z.subschemeι ⁻¹' {x} := by
    ext w
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · rintro rfl; exact hzx
    · intro hw; exact Z.subschemeι.isClosedEmbedding.injective (hw.trans hzx.symm)
  rw [this]
  exact hx.preimage Z.subschemeι.continuous

end AlgebraicGeometry.Scheme.IdealSheafData
