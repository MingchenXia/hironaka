/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
import Hironaka.Geometry.ProperSteinProjectiveCechInfinitesimal
import Hironaka.Geometry.BlowupProjectiveEmbeddingForms
import Mathlib.Algebra.Exact.Basic

/-!
# Whole original affine infinitesimal quotients and literal restrictions/transitions

Only closed native spectrum-kernel helpers are adapted from
`EnvelopeProperty/deps/hironaka-ep33/Hironaka/Scheme/BlowUp/InverseImage.lean`,
SHA256 4d7e0eb6480cec39995d3edad7fec14518894ecc101702d0298c50bbcc98bd87.
Actual affine quotient/restriction/transition proofs are adapted from
`EnvelopeProperty/EnvelopeProperty/Global/FibreInfinitesimalSections.lean`,
SHA256 293829a148d47d7bb09fc49db1d58ce6eafe90dcc8d30a6cd7d5de720eabcec2.
No other-project import or geometric quotient/exactness output certificate is used.
-/
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
namespace Hironaka.Geometry.ProperSteinProjectiveCech.Infinitesimal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {A B : CommRingCat.{u}}

/-- Actual spectrum pullback on ENTIRE original global sections, with both coordinate isomorphisms. -/
theorem spectrumAppTop (φ : A ⟶ B) :
    (Spec.map φ).appTop = (Scheme.ΓSpecIso A).hom ≫ φ ≫ (Scheme.ΓSpecIso B).inv := by
  rw [← Category.comp_id (Spec.map φ).appTop, ← (Scheme.ΓSpecIso B).hom_inv_id, ← Category.assoc,
    Scheme.ΓSpecIso_naturality, Category.assoc]

/-- The original spectrum pullback retains the WHOLE original ring kernel. -/
theorem spectrumAppTopKernel (φ : A ⟶ B) :
    RingHom.ker (Spec.map φ).appTop.hom = (RingHom.ker φ.hom).map (Scheme.ΓSpecIso A).inv.hom := by
  have hinj : Function.Injective (Scheme.ΓSpecIso B).inv.hom :=
    (Scheme.ΓSpecIso B).symm.commRingCatIsoToRingEquiv.injective
  rw [spectrumAppTop, CommRingCat.hom_comp, CommRingCat.hom_comp, ← RingHom.comap_ker,
    RingHom.ker_comp_of_injective _ hinj]
  ext x
  rw [Ideal.mem_comap, Ideal.mem_map_iff_of_surjective (Scheme.ΓSpecIso A).inv.hom
    (fun y => ⟨(Scheme.ΓSpecIso A).hom.hom y,
      (Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv.symm_apply_apply y⟩)]
  constructor
  · intro hx
    exact ⟨(Scheme.ΓSpecIso A).hom x, hx,
      (Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv.symm_apply_apply x⟩
  · rintro ⟨y, hy, rfl⟩
    have h : (Scheme.ΓSpecIso A).hom.hom ((Scheme.ΓSpecIso A).inv.hom y) = y :=
      (Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv.apply_symm_apply y
    rw [h]
    exact hy

variable {R : Type u} [CommRing R] (I : Ideal R)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The LITERAL original coefficient closed immersion has exactly its WHOLE original ideal power. -/
theorem coefficientScheme_ker (n : ℕ) :
    (coefficientScheme I n).ker = SpecIdealSheaf.specIdealSheaf R (I^n) := by
  rw [Scheme.ker_of_isAffine, spectrumAppTopKernel, CommRingCat.hom_ofHom, Ideal.mk_ker]
  rfl

/-- The ORIGINAL coefficient homomorphism on EVERY original open. -/
def sectionCoefficient (U : X.Opens) : R →+* Γ(X, U) :=
  (f.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom

/-- The SAME original coefficient ideal's genuine geometric extension. -/
abbrev extendedIdeal : X.IdealSheafData := (SpecIdealSheaf.specIdealSheaf R I).comap f

/-- The ENTIRE original power of the SAME genuine extended ideal. -/
abbrev extendedPower (n : ℕ) : X.IdealSheafData := (extendedIdeal I f)^n

/-- EVERY original affine ideal is the actual original coefficient ideal image. -/
theorem extendedIdeal_ideal (U : X.affineOpens) :
    (extendedIdeal I f).ideal U = I.map (sectionCoefficient f U.1) := by
  rw [extendedIdeal, BlowupProjectiveEmbedding.ideal_comap_affine _ f U
    ⟨⊤, isAffineOpen_top _⟩ le_top, SpecIdealSheaf.specIdealSheaf_ideal_top, Ideal.map_map]
  rfl

/-- EVERY original affine ideal power is its SAME whole original coefficient image power. -/
theorem extendedPower_ideal (n : ℕ) (U : X.affineOpens) :
    (extendedPower I f n).ideal U = (I.map (sectionCoefficient f U.1))^n := by
  change ((extendedIdeal I f).ideal U)^n = _
  rw [extendedIdeal_ideal]

/-- The WHOLE original projection kernel is the SAME genuine original geometric ideal power. -/
theorem projection_ker (n : ℕ) : (projection I f n).ker = extendedPower I f n := by
  let : IsClosedImmersion (coefficientScheme I n) :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (Ideal.Quotient.mk (I^n)))
      Ideal.Quotient.mk_surjective
  rw [projection, Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, coefficientScheme_ker]
  apply Scheme.IdealSheafData.ext
  funext U
  change (extendedIdeal (I^n) f).ideal U = _
  rw [extendedIdeal_ideal, extendedPower_ideal, Ideal.map_pow]

/-- EVERY original affine projection section map has its full actual ideal-power kernel. -/
theorem affine_projection_ker (n : ℕ) (U : X.affineOpens) :
    RingHom.ker ((projection I f n).app U).hom = (I.map (sectionCoefficient f U.1))^n := by
  rw [← Scheme.Hom.ker_apply, projection_ker, extendedPower_ideal]

/-- The genuine original projection section map is surjective on EVERY affine open. -/
theorem affine_projection_surjective (n : ℕ) (U : X.affineOpens) :
    Function.Surjective ((projection I f n).app U) :=
  (projection I f n).app_surjective U.1 U.2

/-- The WHOLE original infinitesimal affine section ring is its actual original quotient. -/
def affineQuotientEquiv (n : ℕ) (U : X.affineOpens) :
    Γ(X, U) ⧸ (I.map (sectionCoefficient f U.1))^n ≃+*
      Γ(model I f n, projection I f n ⁻¹ᵁ U.1) :=
  (Ideal.quotEquivOfEq (affine_projection_ker I f n U).symm).trans
    (RingHom.quotientKerEquivOfSurjective (affine_projection_surjective I f n U))

/-- EVERY original quotient representative is its genuine original projection section. -/
theorem affineQuotientEquiv_mk (n : ℕ) (U : X.affineOpens) (s : Γ(X, U)) :
    affineQuotientEquiv I f n U (Ideal.Quotient.mk ((I.map (sectionCoefficient f U.1))^n) s) =
      (projection I f n).app U s := by
  simp only [affineQuotientEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

/-- Genuine projection vanishing is exactly membership in the SAME entire original ideal power. -/
theorem affine_projection_eq_zero_iff (n : ℕ) (U : X.affineOpens) (s : Γ(X, U)) :
    (projection I f n).app U s = 0 ↔ s ∈ (I.map (sectionCoefficient f U.1))^n := by
  change s ∈ RingHom.ker ((projection I f n).app U).hom ↔ _
  rw [affine_projection_ker]

/-- The actual ORIGINAL ideal-power inclusion retains EVERY ambient original section. -/
def affinePowerInclusion (n : ℕ) (U : X.affineOpens) :
    ↥((I.map (sectionCoefficient f U.1))^n) →ₗ[Γ(X, U)] Γ(X, U) :=
  ((I.map (sectionCoefficient f U.1))^n).subtype

/-- The literal original ideal-power inclusion is injective. -/
theorem affinePowerInclusion_injective (n : ℕ) (U : X.affineOpens) :
    Function.Injective (affinePowerInclusion I f n U) := Subtype.val_injective

/-- The SAME actual whole original affine ideal-power/projection pair is exact. -/
theorem affineSection_exact (n : ℕ) (U : X.affineOpens) :
    Function.Exact (affinePowerInclusion I f n U) ((projection I f n).app U) := by
  intro s
  rw [affine_projection_eq_zero_iff]
  exact ⟨fun hs => ⟨⟨s, hs⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.2⟩

/-- Literal original affine restriction on the ENTIRE actual ideal-power quotients. -/
def affineRestriction (n : ℕ) {U V : X.affineOpens} (h : U ≤ V) :
    Γ(X, V) ⧸ (I.map (sectionCoefficient f V.1))^n →+*
      Γ(X, U) ⧸ (I.map (sectionCoefficient f U.1))^n :=
  Ideal.quotientMap _ (X.presheaf.map (homOfLE h).op).hom (by
    rw [← extendedPower_ideal I f n U,
      ← extendedPower_ideal I f n V]
    exact (extendedPower I f n).ideal_le_comap_ideal h)

/-- EVERY quotient representative restricts by the entire original function restriction. -/
theorem affineRestriction_mk (n : ℕ) {U V : X.affineOpens} (h : U ≤ V) (s : Γ(X, V)) :
    affineRestriction I f n h (Ideal.Quotient.mk ((I.map (sectionCoefficient f V.1))^n) s) =
      Ideal.Quotient.mk ((I.map (sectionCoefficient f U.1))^n)
        (X.presheaf.map (homOfLE h).op s) := rfl

/-- EVERY actual original inverse-image affine restriction is exactly the
whole quotient restriction under the SAME genuine affine section equivalences. -/
theorem affineQuotientEquiv_restriction (n : ℕ) {U V : X.affineOpens} (h : U ≤ V)
    (s : Γ(X, V) ⧸ (I.map (sectionCoefficient f V.1))^n) :
    (model I f n).presheaf.map
        (((TopologicalSpace.Opens.map (projection I f n).base).map (homOfLE h)).op)
        (affineQuotientEquiv I f n V s) =
      affineQuotientEquiv I f n U (affineRestriction I f n h s) := by
  induction s using Quotient.inductionOn' with
  | _ s =>
    change (model I f n).presheaf.map _
      (affineQuotientEquiv I f n V (Ideal.Quotient.mk _ s)) =
        affineQuotientEquiv I f n U (affineRestriction I f n h (Ideal.Quotient.mk _ s))
    rw [affineQuotientEquiv_mk, affineRestriction_mk, affineQuotientEquiv_mk]
    exact (congrArg (fun q : Γ(X, V) ⟶ Γ(model I f n, projection I f n ⁻¹ᵁ U.1) => q.hom s)
      ((projection I f n).naturality (homOfLE h).op)).symm

/-- The actual original transition has exactly the SAME original inverse-image open. -/
theorem transition_preimage {n m : ℕ} (h : n ≤ m) (U : X.Opens) :
    transition I f h ⁻¹ᵁ (projection I f m ⁻¹ᵁ U) = projection I f n ⁻¹ᵁ U := by
  rw [← Scheme.Hom.comp_preimage, transition_projection]

/-- The genuine original whole section transition on the SAME inverse-image affine open. -/
def affineTransition {n m : ℕ} (h : n ≤ m) (U : X.affineOpens) :
    Γ(model I f m, projection I f m ⁻¹ᵁ U.1) →+*
      Γ(model I f n, projection I f n ⁻¹ᵁ U.1) :=
  ((transition I f h).appLE (projection I f m ⁻¹ᵁ U.1)
    (projection I f n ⁻¹ᵁ U.1) (transition_preimage I f h U.1).symm.le).hom

/-- The actual whole section transition preserves EVERY original projection section. -/
theorem affineTransition_projection {n m : ℕ} (h : n ≤ m) (U : X.affineOpens) :
    (affineTransition I f h U).comp ((projection I f m).app U).hom =
      ((projection I f n).app U).hom := by
  have hcomp := Scheme.Hom.comp_appLE (transition I f h) (projection I f m)
    U.1 (projection I f n ⁻¹ᵁ U.1) (transition_preimage I f h U.1).symm.le
  simp only [transition_projection, ← Scheme.Hom.app_eq_appLE] at hcomp
  exact congrArg CommRingCat.Hom.hom hcomp.symm

/-- EVERY whole original infinitesimal section transition is the actual
ideal-power quotient factor under the SAME original affine quotient equivalences. -/
theorem affineQuotientEquiv_transition {n m : ℕ} (h : n ≤ m) (U : X.affineOpens)
    (s : Γ(X, U) ⧸ (I.map (sectionCoefficient f U.1))^m) :
    affineTransition I f h U (affineQuotientEquiv I f m U s) =
      affineQuotientEquiv I f n U
        (Ideal.Quotient.factorPow (I.map (sectionCoefficient f U.1)) h s) := by
  induction s using Quotient.inductionOn' with
  | _ s =>
    change affineTransition I f h U
      (affineQuotientEquiv I f m U (Ideal.Quotient.mk _ s)) =
        affineQuotientEquiv I f n U (Ideal.Quotient.mk _ s)
    rw [affineQuotientEquiv_mk, affineQuotientEquiv_mk]
    exact RingHom.congr_fun (affineTransition_projection I f h U) s

end Hironaka.Geometry.ProperSteinProjectiveCech.Infinitesimal
