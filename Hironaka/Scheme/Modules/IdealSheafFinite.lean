/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Modules.IdealSheaf
public import Hironaka.Scheme.Modules.AffineLocal
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# An ideal sheaf on a locally Noetherian scheme is of finite presentation

The sheaf of modules `I.toModules` of an ideal sheaf `I` restricts, over a basic open `D(r)` of an
affine open `U`, to the localization `I(U)_r = I(D(r))`
(Mathlib's `IdealSheafData.map_ideal_basicOpen`):
`Scheme.IdealSheafData.isLocalizedModule_toModules_resₗ`. Its restriction to `Spec Γ(X, U)` is
therefore the sheaf associated to `I(U)` (Mathlib's `isIso_fromTildeΓ_iff_isLocalizing`), and when
`X` is locally Noetherian `I(U)` is finitely presented, so `I.toModules` is of finite presentation,
hence quasi-coherent and of finite type (`Scheme.IdealSheafData.isFinitePresentation_toModules`).
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (I : X.IdealSheafData)

theorem coe_toModulesSectionsEquiv_smul (U : X.affineOpens) (c : Γ(X, U))
    (s : Γ(I.toModules, U)) :
    ((I.toModulesSectionsEquiv U (c • s) : I.ideal U) : Γ(X, U)) =
      c * (I.toModulesSectionsEquiv U s : Γ(X, U)) := by
  rw [LinearEquiv.map_smul]
  rfl

set_option linter.style.haveILetI false in
/-- Over a basic open `D(r)` of an affine open `U`, the sections of `I.toModules` are the
localization of those over `U`: `I(D(r)) = I(U)_r`. -/
theorem isLocalizedModule_toModules_resₗ (U : X.affineOpens) (r : Γ(X, U)) :
    letI := Module.compHom Γ(I.toModules, X.basicOpen r)
      (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
    IsLocalizedModule (Submonoid.powers r) (I.toModules.resₗ (X.basicOpen_le r)) := by
  letI := Module.compHom Γ(I.toModules, X.basicOpen r)
    (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
  have := U.2.isLocalization_basicOpen r
  set ρ := X.presheaf.map (homOfLE (X.basicOpen_le r)).op
  set eU := I.toModulesSectionsEquiv U
  set eD := I.toModulesSectionsEquiv (X.affineBasicOpen r)
  -- The values in `Γ(X, D(r))` of the sections over `D(r)`.
  let v : Γ(I.toModules, X.basicOpen r) → Γ(X, X.basicOpen r) := fun w => (eD w).1
  have hv : Function.Injective v := fun w w' h => eD.injective (Subtype.ext h)
  have hres (s : Γ(I.toModules, U)) :
      v (I.toModules.resₗ (X.basicOpen_le r) s) = ρ (eU s : Γ(X, U)) :=
    I.coe_toModulesSectionsEquiv_restrictionMap (U := X.affineBasicOpen r) (V := U)
      (X.basicOpen_le r) s
  have hsmul' (c : Γ(X, X.basicOpen r)) (y : Γ(I.toModules, X.basicOpen r)) :
      v (c • y) = c * v y :=
    I.coe_toModulesSectionsEquiv_smul (X.affineBasicOpen r) c y
  have hsmul (c : Γ(X, U)) (y : Γ(I.toModules, X.basicOpen r)) : v (c • y) = ρ c * v y :=
    hsmul' (ρ c) y
  have hunit (n : ℕ) : IsUnit (ρ (r ^ n)) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit (S := Γ(X, X.basicOpen r)) r).pow n
  refine ⟨fun x => ?_, fun y => ?_, fun {a b} h => ?_⟩
  · obtain ⟨_, n, rfl⟩ := x
    rw [Module.End.isUnit_iff]
    obtain ⟨u, hu⟩ := hunit n
    refine ⟨fun y z hyz => hv ?_, fun y => ⟨(u⁻¹ : (Γ(X, X.basicOpen r))ˣ) • y, hv ?_⟩⟩
    · have := congrArg v hyz
      simp only [Module.algebraMap_end_apply] at this
      rw [hsmul, hsmul, ← hu] at this
      exact u.isUnit.mul_left_cancel this
    · change v ((r ^ n) • ((u⁻¹ : (Γ(X, X.basicOpen r))ˣ) • y)) = v y
      rw [hsmul, ← hu, Units.smul_def, hsmul', ← mul_assoc, Units.mul_inv, one_mul]
  · have hmap : ∀ w : Γ(X, X.basicOpen r), w ∈ I.ideal (X.affineBasicOpen r) →
        w ∈ (I.ideal U).map ρ.hom := fun w hw => by rwa [← I.map_ideal_basicOpen] at hw
    have hy := hmap (v y) (eD y).2
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, ha⟩ := (IsLocalization.mem_map_algebraMap_iff
      (Submonoid.powers r) Γ(X, X.basicOpen r)).mp hy
    refine ⟨(eU.symm a, ⟨r ^ n, n, rfl⟩), hv ?_⟩
    change v ((r ^ n) • y) = _
    rw [hsmul, hres, LinearEquiv.apply_symm_apply, mul_comm]
    exact ha
  · have h' := congrArg v h
    simp only [hres] at h'
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers r)
      Γ(X, X.basicOpen r)).mp h'
    refine ⟨c, eU.injective (Subtype.ext ?_)⟩
    rw [Submonoid.smul_def, Submonoid.smul_def, LinearEquiv.map_smul, LinearEquiv.map_smul]
    exact hc

/-- Over an affine open `U`, the restriction of `I.toModules` to `Spec Γ(X, U)` is the sheaf
associated to its global sections: the restrictions to the basic opens are localizations
(`isLocalizedModule_toModules_resₗ`). -/
theorem isIso_fromTildeΓ_toModules {U : X.Opens} (hU : IsAffineOpen U) :
    IsIso (I.toModules.restrict hU.fromSpec).fromTildeΓ :=
  (isIso_fromTildeΓ_iff_isLocalizing _).mpr fun r =>
    (I.toModules.isLocalizedModule_restrict_fromSpec_iff hU r).mpr
      (I.isLocalizedModule_toModules_resₗ ⟨U, hU⟩ r)

/-- **An ideal sheaf on a locally Noetherian scheme is of finite presentation** as a sheaf of
modules: over each affine open `U` its restriction to `Spec Γ(X, U)` is the sheaf associated to
`I(U)`, a finitely presented module over the Noetherian ring `Γ(X, U)`. -/
theorem isFinitePresentation_toModules [IsLocallyNoetherian X] :
    SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) I.toModules := by
  refine I.toModules.isFinitePresentation_of_forall_affine fun U hU => ?_
  let U' : X.affineOpens := ⟨U, hU⟩
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U'
  have : Module.FinitePresentation Γ(X, U) (I.ideal U') :=
    Module.finitePresentation_of_finite _ _
  have : Module.FinitePresentation Γ(X, U) Γ(I.toModules, U) :=
    Module.FinitePresentation.of_equiv (I.toModulesSectionsEquiv U').symm
  have := I.isIso_fromTildeΓ_toModules hU
  exact I.toModules.exists_isFinite_presentation_restrict hU

end AlgebraicGeometry.Scheme.IdealSheafData
