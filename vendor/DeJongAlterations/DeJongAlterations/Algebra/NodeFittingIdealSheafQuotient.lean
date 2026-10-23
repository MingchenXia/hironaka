/-
Adapted from Hironaka/Scheme/Smooth/SubschemeStalk.lean in
EnvelopeProperty/deps/hironaka-ep33, original SHA256
2d7452ad24856cfd6f15690425971108a4fbcc65a5fffa2a15ec1de445acfd0f.
Copyright (c) 2026 Resolution; author Chris Elliott (Resolution).
Original Lean formalization by Claude Fable 5.1; Apache License 2.0.
Modified: retain the actual original whole kernel and quotient triangle only,
Mathlib-only imports and a disjoint namespace. License reproduced in
Algebra/AdicCompletionTransport.lean.
-/
import DeJongAlterations.Algebra.NodeFittingIdealSheafStalks

/-! # Actual native closed-subscheme stalk quotients with their full original map triangle -/

noncomputable section

namespace DeJongAlterations.Algebra.NodeFittingIdealSheaf

open AlgebraicGeometry Scheme.IdealSheafData CategoryTheory IsLocalRing TopologicalSpace

universe u
variable {X : Scheme.{u}} (Z : X.IdealSheafData)

/-- The kernel of the stalk map of the closed immersion `V(Z) ⟶ X` at `z` is the stalk of `Z`
at `ι z`. -/
theorem ker_stalkMap_subschemeι (z : Z.subscheme) :
    RingHom.ker (Z.subschemeι.stalkMap z).hom = stalkIdeal Z (Z.subschemeι z) := by
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
    (X.presheaf.stalk (Z.subschemeι z) ⧸ stalkIdeal Z (Z.subschemeι z)) ≃+*
      Z.subscheme.presheaf.stalk z :=
  (Ideal.quotEquivOfEq (ker_stalkMap_subschemeι Z z).symm).trans
    (RingHom.quotientKerEquivOfSurjective (Z.subschemeι.stalkMap_surjective z))

theorem stalkQuotientEquiv_mk (z : Z.subscheme) (a : X.presheaf.stalk (Z.subschemeι z)) :
    stalkQuotientEquiv Z z (Ideal.Quotient.mk _ a) = Z.subschemeι.stalkMap z a :=
  rfl


end DeJongAlterations.Algebra.NodeFittingIdealSheaf
