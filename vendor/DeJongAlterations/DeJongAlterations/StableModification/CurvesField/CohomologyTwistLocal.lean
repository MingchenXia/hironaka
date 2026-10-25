/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.CurvesField.CohomologyTwist

/-!
# The twist is locally isomorphic to the module: quasi-coherence

The twist `F_u = twist F U V u` of `CohomologyTwist` is isomorphic to `F` on `U` (through the
`U`-component of sections) and on `V` (through the `V`-component). Hence `F_u` is
quasi-coherent when `F` is (`twist_isQuasicoherent`), and its cohomology is computed by any finite
affine cover; in particular, when `U`, `V`, `U ∩ V` are affine, by the two-term complex of
`CohomologyTwist` (`cohomologyTwistOneEquiv`, `cohomologyTwistZeroEquiv`). Blueprint:
`sm-curves-fields-cohomology.tex`, `lem:sm-twist-local`.

## Main results

* `twistRestrictIsoU`, `twistRestrictIsoV`: `F_u|_U ≅ F|_U` and `F_u|_V ≅ F|_V`.
* `twist_isQuasicoherent`: `F_u` is quasi-coherent if `F` is.
* `cohomologyTwistOneEquiv`, `cohomologyTwistZeroEquiv`: `H¹(Y, F_u)` and `H⁰(Y, F_u)` from the
  two-term complex, for an affine cover `(U, V)` with affine intersection.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open DeJongAlterations.StableModification.Cohomology

namespace DeJongAlterations.StableModification.CurvesField

noncomputable section

variable {Y : Scheme.{u}} (F : Y.Modules) (U V : Y.Opens) (u : Γ(Y, U ⊓ V)ˣ)

section LocalU

variable {W : Y.Opens} (hW : W ≤ U)

/-- The `U`-component of a section of the twist over `W ≤ U`. -/
def twistToUW (p : twistSubgroup F U V u W) : Γ(F, W) :=
  F.presheaf.map (homOfLE (le_inf le_rfl hW : W ≤ W ⊓ U)).op p.1.1

/-- The section of the twist over `W ≤ U` with `U`-component `s`. -/
def twistOfUW (s : Γ(F, W)) : twistSubgroup F U V u W :=
  ⟨(F.presheaf.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op s,
    Y.presheaf.map (homOfLE (inf_le_inf_right V hW : W ⊓ V ≤ U ⊓ V)).op (u : Γ(Y, U ⊓ V)) •
      F.presheaf.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op s), by
    change TwistCond F U V u W _ _
    unfold TwistCond
    rw [Scheme.Modules.map_smul, ringMap_ringMap _ _ (twist_le₃ U V W),
      presheaf_map_map F _ _ ((twist_le₂ U V W).trans inf_le_left),
      presheaf_map_map F _ _ ((twist_le₂ U V W).trans inf_le_left)]⟩

lemma twistToUW_ofUW (s : Γ(F, W)) : twistToUW F U V u hW (twistOfUW F U V u hW s) = s :=
  presheaf_map_map_self F _ _ s

lemma twistOfUW_toUW (p : twistSubgroup F U V u W) :
    twistOfUW F U V u hW (twistToUW F U V u hW p) = p := by
  have hp : TwistCond F U V u W p.1.1 p.1.2 := p.2
  apply Subtype.ext
  apply Prod.ext
  · exact presheaf_map_map_self F _ _ _
  · change Y.presheaf.map _ (u : Γ(Y, U ⊓ V)) • F.presheaf.map _ (F.presheaf.map _ p.1.1) = p.1.2
    unfold TwistCond at hp
    have hle : W ⊓ V ≤ W ⊓ (U ⊓ V) := fun x hx => ⟨hx.1, hW hx.1, hx.2⟩
    have e := congrArg (F.presheaf.map (homOfLE hle).op) hp
    have h₃ : W ⊓ V ≤ W ⊓ U := fun x hx => ⟨hx.1, hW hx.1⟩
    rw [presheaf_map_map_self, Scheme.Modules.map_smul, ringMap_ringMap _ _ (inf_le_inf_right V hW),
      presheaf_map_map F _ _ h₃] at e
    rw [presheaf_map_map F _ _ h₃, e]

lemma twistToUW_add (p q : twistSubgroup F U V u W) :
    twistToUW F U V u hW (p + q) = twistToUW F U V u hW p + twistToUW F U V u hW q :=
  map_add _ _ _

lemma twistToUW_smul (r : Γ(Y, W)) (p : twistSubgroup F U V u W) :
    twistToUW F U V u hW (r • p) = r • twistToUW F U V u hW p := by
  change F.presheaf.map _ (resU U W r • p.1.1) = r • F.presheaf.map _ p.1.1
  rw [Scheme.Modules.map_smul, ringMap_ringMap _ _ le_rfl, ringMap_self]

lemma twistToUW_restrict {W' : Y.Opens} (h : W' ≤ W) (p : twistSubgroup F U V u W) :
    twistToUW F U V u (h.trans hW) (twistRestrict F U V u h p) =
      F.presheaf.map (homOfLE h).op (twistToUW F U V u hW p) := by
  change F.presheaf.map _ (F.presheaf.map _ p.1.1) = F.presheaf.map _ (F.presheaf.map _ p.1.1)
  rw [presheaf_map_map F _ _ (le_inf h (h.trans hW)),
    presheaf_map_map F _ _ (le_inf h (h.trans hW))]

end LocalU

section LocalV

variable {W : Y.Opens} (hW : W ≤ V)

/-- The `V`-component of a section of the twist over `W ≤ V`. -/
def twistToVW (p : twistSubgroup F U V u W) : Γ(F, W) :=
  F.presheaf.map (homOfLE (le_inf le_rfl hW : W ≤ W ⊓ V)).op p.1.2

lemma twist_le_WU (hW : W ≤ V) : W ⊓ U ≤ U ⊓ V := fun _ hx => ⟨hx.2, hW hx.1⟩

/-- The section of the twist over `W ≤ V` with `V`-component `s`. -/
def twistOfVW (s : Γ(F, W)) : twistSubgroup F U V u W :=
  ⟨(Y.presheaf.map (homOfLE (twist_le_WU U V hW)).op ((u⁻¹ : Γ(Y, U ⊓ V)ˣ) : Γ(Y, U ⊓ V)) •
      F.presheaf.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op s,
    F.presheaf.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op s), by
    change TwistCond F U V u W _ _
    unfold TwistCond
    rw [Scheme.Modules.map_smul, ringMap_ringMap, smul_smul, ← map_mul, Units.mul_inv, map_one,
      one_smul, presheaf_map_map F _ _ ((twist_le₁ U V W).trans inf_le_left),
      presheaf_map_map F _ _ ((twist_le₁ U V W).trans inf_le_left)]
    exact twist_le₃ U V W⟩

lemma twistToVW_ofVW (s : Γ(F, W)) : twistToVW F U V u hW (twistOfVW F U V u hW s) = s :=
  presheaf_map_map_self F _ _ s

lemma twistOfVW_toVW (p : twistSubgroup F U V u W) :
    twistOfVW F U V u hW (twistToVW F U V u hW p) = p := by
  have hp : TwistCond F U V u W p.1.1 p.1.2 := p.2
  apply Subtype.ext
  apply Prod.ext
  · change Y.presheaf.map _ _ • F.presheaf.map _ (F.presheaf.map _ p.1.2) = p.1.1
    unfold TwistCond at hp
    have hle : W ⊓ U ≤ W ⊓ (U ⊓ V) := fun x hx => ⟨hx.1, hx.2, hW hx.1⟩
    have e := congrArg (F.presheaf.map (homOfLE hle).op) hp
    have h₃ : W ⊓ U ≤ W ⊓ V := fun x hx => ⟨hx.1, hW hx.1⟩
    rw [presheaf_map_map F _ _ h₃, Scheme.Modules.map_smul,
      ringMap_ringMap _ _ (twist_le_WU U V hW), presheaf_map_map_self] at e
    rw [presheaf_map_map F _ _ h₃, e, smul_smul, ← map_mul, Units.inv_mul, map_one, one_smul]
  · exact presheaf_map_map_self F _ _ _

lemma twistToVW_add (p q : twistSubgroup F U V u W) :
    twistToVW F U V u hW (p + q) = twistToVW F U V u hW p + twistToVW F U V u hW q :=
  map_add _ _ _

lemma twistToVW_smul (r : Γ(Y, W)) (p : twistSubgroup F U V u W) :
    twistToVW F U V u hW (r • p) = r • twistToVW F U V u hW p := by
  change F.presheaf.map _ (resV V W r • p.1.2) = r • F.presheaf.map _ p.1.2
  rw [Scheme.Modules.map_smul, ringMap_ringMap _ _ le_rfl, ringMap_self]

lemma twistToVW_restrict {W' : Y.Opens} (h : W' ≤ W) (p : twistSubgroup F U V u W) :
    twistToVW F U V u (h.trans hW) (twistRestrict F U V u h p) =
      F.presheaf.map (homOfLE h).op (twistToVW F U V u hW p) := by
  change F.presheaf.map _ (F.presheaf.map _ p.1.2) = F.presheaf.map _ (F.presheaf.map _ p.1.2)
  rw [presheaf_map_map F _ _ (le_inf h (h.trans hW)),
    presheaf_map_map F _ _ (le_inf h (h.trans hW))]

end LocalV

section RestrictIso

/-- **`F_u|_U ≅ F|_U`** through the `U`-component. -/
def twistRestrictIsoU : (twist F U V u).restrict U.ι ≅ F.restrict U.ι :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun W' => ModuleCat.isoMk (AddEquiv.toAddCommGrpIso
      { toFun := fun p => twistToUW F U V u (U.ι_image_le W'.unop) p
        invFun := fun s => twistOfUW F U V u (U.ι_image_le W'.unop) s
        left_inv := twistOfUW_toUW F U V u (U.ι_image_le W'.unop)
        right_inv := twistToUW_ofUW F U V u (U.ι_image_le W'.unop)
        map_add' := twistToUW_add F U V u (U.ι_image_le W'.unop) }) (fun r => by
        ext p
        exact (twistToUW_smul F U V u (U.ι_image_le W'.unop) ((U.ι.appIso W'.unop).inv r) p).symm))
      (fun W₁ W₂ i => by
        ext p
        exact twistToUW_restrict F U V u (U.ι_image_le W₁.unop)
          (U.ι.image_mono (leOfHom i.unop)) p))

/-- **`F_u|_V ≅ F|_V`** through the `V`-component. -/
def twistRestrictIsoV : (twist F U V u).restrict V.ι ≅ F.restrict V.ι :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun W' => ModuleCat.isoMk (AddEquiv.toAddCommGrpIso
      { toFun := fun p => twistToVW F U V u (V.ι_image_le W'.unop) p
        invFun := fun s => twistOfVW F U V u (V.ι_image_le W'.unop) s
        left_inv := twistOfVW_toVW F U V u (V.ι_image_le W'.unop)
        right_inv := twistToVW_ofVW F U V u (V.ι_image_le W'.unop)
        map_add' := twistToVW_add F U V u (V.ι_image_le W'.unop) }) (fun r => by
        ext p
        exact (twistToVW_smul F U V u (V.ι_image_le W'.unop) ((V.ι.appIso W'.unop).inv r) p).symm))
      (fun W₁ W₂ i => by
        ext p
        exact twistToVW_restrict F U V u (V.ι_image_le W₁.unop)
          (V.ι.image_mono (leOfHom i.unop)) p))

end RestrictIso

section Quasicoherent

/-- `F_u` and `F` agree over `U` (as sheaves on the site over `U`). -/
def twistOverIsoU : (twist F U V u).over U ≅ F.over U :=
  (Scheme.Modules.overEquiv U).fullyFaithfulFunctor.preimageIso
    ((Scheme.Modules.overFunctorEquiv U).app _ ≪≫ twistRestrictIsoU F U V u ≪≫
      ((Scheme.Modules.overFunctorEquiv U).app F).symm)

/-- `F_u` and `F` agree over `V` (as sheaves on the site over `V`). -/
def twistOverIsoV : (twist F U V u).over V ≅ F.over V :=
  (Scheme.Modules.overEquiv V).fullyFaithfulFunctor.preimageIso
    ((Scheme.Modules.overFunctorEquiv V).app _ ≪≫ twistRestrictIsoV F U V u ≪≫
      ((Scheme.Modules.overFunctorEquiv V).app F).symm)

/-- **The twist of a quasi-coherent module is quasi-coherent** (blueprint `lem:sm-twist-local`). -/
theorem twist_isQuasicoherent [F.IsQuasicoherent] (h : U ⊔ V = ⊤) :
    (twist F U V u).IsQuasicoherent := by
  have hU : ((twist F U V u).over U).IsQuasicoherent := by
    obtain ⟨⟨q⟩⟩ := SheafOfModules.isQuasicoherent_over F U
    exact (SheafOfModules.QuasicoherentData.ofIsIso (twistOverIsoU F U V u).inv q).isQuasicoherent
  have hV : ((twist F U V u).over V).IsQuasicoherent := by
    obtain ⟨⟨q⟩⟩ := SheafOfModules.isQuasicoherent_over F V
    exact (SheafOfModules.QuasicoherentData.ofIsIso (twistOverIsoV F U V u).inv q).isQuasicoherent
  have hcov : (Opens.grothendieckTopology Y).CoversTop (pairCover U V) := by
    rw [Opens.coversTop_iff, IsOpenCover, iSup_pairCover, h]
  have : ∀ i, ((twist F U V u).over (pairCover U V i)).IsQuasicoherent := by
    intro i
    rcases eq_i₀_or_eq_i₁ i with rfl | rfl
    · exact hU
    · exact hV
  exact SheafOfModules.IsQuasicoherent.of_coversTop (twist F U V u) (pairCover U V) hcov

end Quasicoherent

section Cohomology

variable [CompactSpace Y] [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from Y))]
  [F.IsQuasicoherent] {R : Type u} [CommRing R] (c : R →+* Γ(Y, ⊤)) (h : U ⊔ V = ⊤)
  (h₀ : IsAffineOpen U) (h₁ : IsAffineOpen V) (h₀₁ : IsAffineOpen (U ⊓ V))

/-- `H¹(Y, F_u)` is the cokernel of the twisted two-term complex (cover-free cohomology). -/
def cohomologyTwistOneEquiv :
    cohomology (twist F U V u) c 1 ≃ₗ[R]
      H1 (resUV F U V c) (resVU F U V c) (smulLin F c (u : Γ(Y, U ⊓ V))) :=
  have := twist_isQuasicoherent F U V u h
  (cohomologyPairOneEquiv (twist F U V u) c h h₀ h₁ h₀₁).trans
    ((cechPairOneEquiv U V (twist F U V u) c).symm.trans (cechTwistOneEquiv F U V u c))

/-- `H⁰(Y, F_u)` is the kernel of the twisted two-term complex (cover-free cohomology). -/
def cohomologyTwistZeroEquiv :
    cohomology (twist F U V u) c 0 ≃ₗ[R]
      H0 (resUV F U V c) (resVU F U V c) (smulLin F c (u : Γ(Y, U ⊓ V))) :=
  have := twist_isQuasicoherent F U V u h
  (cohomologyPairZeroEquiv (twist F U V u) c h h₀ h₁ h₀₁).trans
    ((cechPairZeroEquiv U V (twist F U V u) c).symm.trans (cechTwistZeroEquiv F U V u c))

include h h₀ h₁ h₀₁ in
/-- `H^p(Y, F_u) = 0` for `p ≥ 2`. -/
theorem isZero_cohomology_twist (p : ℕ) (hp : 2 ≤ p) :
    Limits.IsZero (cohomology (twist F U V u) c p) :=
  have := twist_isQuasicoherent F U V u h
  isZero_cohomology_pair (twist F U V u) c h h₀ h₁ h₀₁ p hp

/-- `H¹(Y, F)` is the cokernel of the untwisted two-term complex. -/
def cohomologyOneEquivH1 :
    cohomology F c 1 ≃ₗ[R] H1 (resUV F U V c) (resVU F U V c) (smulLin F c 1) :=
  (cohomologyPairOneEquiv F c h h₀ h₁ h₀₁).trans
    ((cechPairOneEquiv U V F c).symm.trans (cechOneEquivH1 F U V c))

/-- `H⁰(Y, F)` is the kernel of the untwisted two-term complex. -/
def cohomologyZeroEquivH0 :
    cohomology F c 0 ≃ₗ[R] H0 (resUV F U V c) (resVU F U V c) (smulLin F c 1) :=
  (cohomologyPairZeroEquiv F c h h₀ h₁ h₀₁).trans
    ((cechPairZeroEquiv U V F c).symm.trans (cechZeroEquivH0 F U V c))

end Cohomology

end

end DeJongAlterations.StableModification.CurvesField
