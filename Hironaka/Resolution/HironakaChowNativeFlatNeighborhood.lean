import Hironaka.Resolution.HironakaChowNativeFiniteTypeSpreading
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Dimension.Free

/-! ONE flat stalk of a finite same-base native FP module INTERNALLY produces
an actual native free neighbourhood and both whole inverse identities.
This is not relative flatness openness for a positive-dimensional family.
Blueprint first: hironaka-g10-native-flat-neighborhood.tex. -/
set_option autoImplicit false
noncomputable section

open CategoryTheory Opposite TopologicalSpace Set

namespace Hironaka.HironakaChowNativeFlatNeighborhood

open HironakaSingularModuleSheafStalk HironakaSingularLocallyFreeStalk
  HironakaChowNativeFiniteFreeStalk HironakaChowNativeFinitePresentationSpreading
  HironakaChowNativeFiniteTypeSpreading

universe u
variable {X : TopCat.{u}} (R : X.Sheaf CommRingCat.{u})
  {M : SheafOfModules.{u} (forgetRing R)}

private theorem restrictOverHom_id (U V : Opens X) (hVU : V ≤ U)
    (N : SheafOfModules.{u} (forgetRing R)) :
    restrictOverHom R U V hVU (𝟙 (N.over U)) = 𝟙 (N.over V) := by
  ext W m
  rfl

/-- Native FP and ONE ordinary flat original stalk derive both actual whole
inverse maps on an internally chosen original open; no local inverse is input. -/
theorem exists_free_neighborhood_of_flat_stalk [M.IsFinitePresentation]
    (x : X) [IsLocalRing ↑(TopCat.Presheaf.stalk R.obj x)]
    (hflat : Module.Flat ↑(TopCat.Presheaf.stalk R.obj x)
      ↑(TopCat.Presheaf.stalk M.val.presheaf x)) :
    ∃ (r : ℕ) (U : Opens X), x ∈ U ∧
      Nonempty (M.over U ≅
        (SheafOfModules.free (R := forgetRing R) (ULift.{u} (Fin r))).over U) := by
  classical
  let A := ↑(TopCat.Presheaf.stalk R.obj x)
  let P := ↑(TopCat.Presheaf.stalk M.val.presheaf x)
  let : Module.Finite A P := moduleFinite_stalk_of_isFiniteType (M := M) R x
  let : Module.Flat A P := hflat
  let : Module.Free A P := Module.free_of_flat_of_isLocalRing
  let r := Module.finrank A P
  let I := ULift.{u} (Fin r)
  let Q := SheafOfModules.free (R := forgetRing R) I
  let φ : P ≃ₗ[A] ↑(TopCat.Presheaf.stalk Q.val.presheaf x) :=
    ((Module.finBasis A P).reindex (Equiv.ulift.symm : Fin r ≃ I)).equivFun.trans
      (finiteFreeStalkLinearEquiv R I x).symm
  obtain ⟨U,hxU,F,hF⟩ :=
    exists_local_lift_of_isFinitePresentation (M := M) (N := Q) R x φ.toLinearMap
  obtain ⟨V,hVU,hxV,H,hH⟩ :=
    exists_free_local_lift (N := M) R x U hxU φ.symm.toLinearMap
  let FV := restrictOverHom R U V hVU F
  have hM : stalkLinearMapOfOver R V (FV ≫ H) x hxV =
      stalkLinearMapOfOver R V (𝟙 (M.over V)) x hxV := by
    rw [stalkLinearMapOfOver_comp,stalkLinearMapOfOver_id,hH]
    change φ.symm.toLinearMap.comp (stalkLinearMapOfOver R V FV x hxV) = _
    rw [stalkLinearMapOfOver_restrictOverHom,hF]
    ext m
    exact φ.symm_apply_apply m
  have hQ : stalkLinearMapOfOver R V (H ≫ FV) x hxV =
      stalkLinearMapOfOver R V (𝟙 (Q.over V)) x hxV := by
    rw [stalkLinearMapOfOver_comp,stalkLinearMapOfOver_id,hH]
    change (stalkLinearMapOfOver R V FV x hxV).comp φ.symm.toLinearMap = _
    rw [stalkLinearMapOfOver_restrictOverHom,hF]
    ext m
    exact φ.apply_symm_apply m
  obtain ⟨Vm,hVmV,hxVm,hm⟩ := exists_restriction_eq_of_isFiniteType R V
    (FV ≫ H) (𝟙 (M.over V)) x hxV hM
  obtain ⟨Vq,hVqV,hxVq,hq⟩ := exists_restrictOverHom_eq_of_free_stalk_eq R V
    (H ≫ FV) (𝟙 (Q.over V)) x hxV hQ
  let W := Vm ⊓ Vq
  have hWm : W ≤ Vm := inf_le_left
  have hWq : W ≤ Vq := inf_le_right
  have hWV : W ≤ V := hWm.trans hVmV
  let FW := restrictOverHom R V W hWV FV
  let HW := restrictOverHom R V W hWV H
  have hFW : FW ≫ HW = 𝟙 (M.over W) := by
    have hh := congrArg (restrictOverHom R Vm W hWm) hm
    simpa only [restrictOverHom_comp,restrictOverHom_trans,restrictOverHom_id] using hh
  have hHW : HW ≫ FW = 𝟙 (Q.over W) := by
    have hh := congrArg (restrictOverHom R Vq W hWq) hq
    have hraw : HW ≫ FW = restrictOverHom R V W hWV (𝟙 (Q.over V)) := by
      simpa only [restrictOverHom_comp,restrictOverHom_trans] using hh
    exact hraw.trans (restrictOverHom_id R V W hWV Q)
  exact ⟨r,W,⟨hxVm,hxVq⟩,⟨{hom := FW, inv := HW, hom_inv_id := hFW, inv_hom_id := hHW}⟩⟩

/-- Every original stalk on the internally produced SAME-base open is flat. -/
theorem exists_flat_neighborhood [M.IsFinitePresentation]
    (x : X) [IsLocalRing ↑(TopCat.Presheaf.stalk R.obj x)]
    (hflat : Module.Flat ↑(TopCat.Presheaf.stalk R.obj x)
      ↑(TopCat.Presheaf.stalk M.val.presheaf x)) :
    ∃ U : Opens X, x ∈ U ∧ ∀ (y : X), y ∈ U →
      Module.Flat ↑(TopCat.Presheaf.stalk R.obj y)
        ↑(TopCat.Presheaf.stalk M.val.presheaf y) := by
  obtain ⟨r,U,hxU,⟨e⟩⟩ := exists_free_neighborhood_of_flat_stalk R x hflat
  refine ⟨U,hxU,?_⟩
  intro y hyU
  exact Module.Flat.of_linearEquiv ((stalkLinearEquivOfOverIso R U e y hyU).trans
    (finiteFreeStalkLinearEquiv R (ULift.{u} (Fin r)) y))

/-- Actual flatness over the SAME original local stalk rings has an open locus
for a native finite-presentation module; no relative-family claim is made. -/
theorem isOpen_flat_locus [M.IsFinitePresentation]
    [∀ x : X, IsLocalRing ↑(TopCat.Presheaf.stalk R.obj x)] :
    IsOpen {x : X | Module.Flat ↑(TopCat.Presheaf.stalk R.obj x)
      ↑(TopCat.Presheaf.stalk M.val.presheaf x)} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨U,hxU,hU⟩ := exists_flat_neighborhood R x hx
  exact Filter.mem_of_superset (U.isOpen.mem_nhds hxU) hU

end Hironaka.HironakaChowNativeFlatNeighborhood
