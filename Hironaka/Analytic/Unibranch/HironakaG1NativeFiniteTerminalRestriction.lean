import Hironaka.Analytic.Unibranch.HironakaG1NativeModificationIsoTransport
import Hironaka.Analytic.Unibranch.HironakaG10GenBlowupBridge
import Hironaka.Resolution.HironakaG1OriginalTerminalOpenRestriction

/-! # Real finite modification on the SAME prescribed terminal inverse open

The actual compact-window canonical tower is internally constructed, restricted
to the prescribed open, and transferred by genuine full native isomorphisms.
No finite-history/endpoint comparison packet or initial singular factory is
an input. Blueprint first. Arbitrary native component assembly is separate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Function TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG1NativeFiniteTerminalRestriction

open Hironaka Hironaka
  Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MaxLocusLocal
  HironakaOriginalTerminalAtlas HironakaOriginalTerminalManifold
  HironakaG1OriginalTerminalOpenRestriction SourceReducedComplexSpace
  OriginalNativeModification SmoothCentreModification HironakaG1NativeModificationIsoTransport
open Hironaka.ResolutionInvariantSpec (IsInvDomain)

attribute [local instance] originalTerminalChartedSpace originalTerminalGluedSpace_isComplexManifold

noncomputable section

variable {n : ℕ} {X : CMfd.{0} n}

private def restrictionFunction (M : MarkedIdeal n X) (hM : IsInvDomain n M) (U : Opens X)
    (z : terminalPreimageOpen M hM U) : U :=
  ⟨originalTerminalGluedProjection M hM z.val, z.property⟩

private theorem restrictionFunction_hol (M : MarkedIdeal n X) (hM : IsInvDomain n M) (U : Opens X) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (restrictionFunction M hM U) :=
  BlowupRestrictOpen.contMDiff_opens_mk
    ((originalTerminalGluedProjection_contMDiff M hM).comp contMDiff_subtype_val) (fun z => z.property)

/-- The SAME actual native projection on its LITERAL original inverse open. -/
def restrictedProjection (M : MarkedIdeal n X) (hM : IsInvDomain n M) (U : Opens X) :
    wholeModel (n := n) (terminalPreimageOpen M hM U) ⟶ wholeModel (n := n) U :=
  nativeMorphism (restrictionFunction_hol M hM U)

/-- Its actual point formula retains both original subtype memberships. -/
theorem restrictedProjection_point (M : MarkedIdeal n X) (hM : IsInvDomain n M) (U : Opens X)
    (z : (wholeModel (n := n) (terminalPreimageOpen M hM U)).obj.left) :
    ((restrictedProjection M hM U).hom.left.base z).val = restrictionFunction M hM U z.val := rfl

/-- FULL native projection square, including the actual original sheaf/scalar maps. -/
theorem restrictedProjection_square (M : MarkedIdeal n X) (hM : IsInvDomain n M) (U : Opens X) :
    restrictedProjection M hM U ≫
        nativeMorphism (n := n) (m := n) (M := U) (N := X) contMDiff_subtype_val =
      nativeMorphism (n := n) (m := n) (M := terminalPreimageOpen M hM U)
          (N := originalTerminalManifold M hM) contMDiff_subtype_val ≫
        nativeMorphism (originalTerminalGluedProjection_contMDiff M hM) := by
  apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
  intro z
  apply Subtype.ext
  rfl

private def restrictFiniteComparison (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (U V : Opens X) (hUV : U ≤ V) {D : CMfd.{0} n}
    (T : BlowupTower (CMfd.of (n := n) V) D)
    (e : D ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (terminalPreimageOpen M hM V))
    (he : ∀ z, originalTerminalGluedProjection M hM (e z).val = (T.proj z).val) :
    CMfd.of (n := n) (openPreimage T (nestedOpens V U))
      ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
        CMfd.of (n := n) (terminalPreimageOpen M hM U) := by
  let O := openPreimage T (nestedOpens V U)
  let W := terminalPreimageOpen M hM U
  let toV : W → terminalPreimageOpen M hM V := fun w => ⟨w.val, hUV w.property⟩
  have htoV : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ toV :=
    BlowupRestrictOpen.contMDiff_opens_mk (n := n) (m := n)
      (V := terminalPreimageOpen M hM V) (f := (Subtype.val : W → originalTerminalManifold M hM))
      contMDiff_subtype_val
      (fun w => hUV w.property)
  have hf (z : O) : (e z.val).val ∈ W := by
    change originalTerminalGluedProjection M hM (e z.val).val ∈ U
    rw [he]
    exact z.property
  have hi (w : W) : e.symm (toV w) ∈ O := by
    change (T.proj (e.symm (toV w))).val ∈ U
    have h := he (e.symm (toV w))
    rw [e.apply_symm_apply] at h
    exact h ▸ w.property
  exact
    { toFun := fun z => ⟨(e z.val).val, hf z⟩
      invFun := fun w => ⟨e.symm (toV w), hi w⟩
      left_inv := by
        intro z
        apply Subtype.ext
        have hv : toV ⟨(e z.val).val, hf z⟩ = e z.val := Subtype.ext rfl
        exact (congrArg e.symm hv).trans (e.symm_apply_apply z.val)
      right_inv := by
        intro w
        apply Subtype.ext
        change (e (e.symm (toV w))).val = w.val
        exact congrArg (fun z : terminalPreimageOpen M hM V => z.val) (e.apply_symm_apply (toV w))
      contMDiff_toFun := BlowupRestrictOpen.contMDiff_opens_mk
        (contMDiff_subtype_val.comp (e.contMDiff.comp contMDiff_subtype_val)) hf
      contMDiff_invFun := BlowupRestrictOpen.contMDiff_opens_mk (e.symm.contMDiff.comp htoV) hi }

private theorem restrictFiniteComparison_proj (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (U V : Opens X) (hUV : U ≤ V) {D : CMfd.{0} n}
    (T : BlowupTower (CMfd.of (n := n) V) D)
    (e : D ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (terminalPreimageOpen M hM V))
    (he : ∀ z, originalTerminalGluedProjection M hM (e z).val = (T.proj z).val)
    (z : openPreimage T (nestedOpens V U)) :
    originalTerminalGluedProjection M hM (restrictFiniteComparison M hM U V hUV T e he z).val =
      (T.proj z.val).val := he z.val

private def nativeIso {A B : CMfd.{0} n}
    (e : A ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ B) :
    wholeModel (n := n) A ≅ wholeModel (n := n) B where
  hom := nativeMorphism e.contMDiff
  inv := nativeMorphism e.symm.contMDiff
  hom_inv_id := by
    apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
    intro z
    apply Subtype.ext
    exact e.symm_apply_apply z.val
  inv_hom_id := by
    apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
    intro z
    apply Subtype.ext
    exact e.apply_symm_apply z.val

/-- Prescribed relatively compact U derives a REAL finite modification of the SAME actual q_U. -/
theorem restrictedProjection_isModification (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (U : Opens X) (hU : IsCompact (closure (U : Set X))) :
    IsModification (restrictedProjection M hM U) := by
  obtain ⟨V, hKV, D, T, _, _, e, he⟩ := exists_compact_window_finite_realization M hM hU
  have hUV : U ≤ V := fun x hx => hKV (subset_closure hx)
  let S := restrict (nestedOpens V U) T
  let eU := restrictFiniteComparison M hM U V hUV T e he
  let E := nativeIso eU.symm
  let F := nativeIso (nestedOpensDiffeo (n := n) hUV)
  have hmod := isModification_conjugate
    (HironakaG10GenBlowupBridge.isModification_nativeMorphism_proj S) E F
  have hfull : E.hom ≫ nativeMorphism S.contMDiff_proj ≫ F.hom = restrictedProjection M hM U := by
    apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
    intro z
    apply Subtype.ext
    apply Subtype.ext
    change ((S.proj (eU.symm z.val)).val).val = originalTerminalGluedProjection M hM z.val.val
    rw [proj_restrict]
    have hp := restrictFiniteComparison_proj M hM U V hUV T e he (eU.symm z.val)
    rw [eU.apply_symm_apply] at hp
    exact hp.symm
  rwa [hfull] at hmod

end
end Hironaka.Analytic.Unibranch.HironakaG1NativeFiniteTerminalRestriction
