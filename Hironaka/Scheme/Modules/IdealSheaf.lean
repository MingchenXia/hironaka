/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.CategoryTheory.Sites.Subsheaf
import Mathlib.RingTheory.Localization.Ideal

/-!
# An ideal sheaf as a sheaf of modules

Mathlib's ideal sheaves (`X.IdealSheafData`) are given by their ideals `I(U) ⊆ Γ(X, U)` over the
affine opens `U`; Mathlib's sheaves of modules are `X.Modules`. The ideal sheaf `I` as a sheaf of
`𝒪_X`-modules is the subsheaf `I.toModules` of `𝒪_X` whose sections over an open `W` are the
functions whose restriction to every affine open `U ⊆ W` lies in `I(U)`; over an affine open `U`
these are exactly the elements of `I(U)` (`Scheme.IdealSheafData.isLocallyMem_iff`). The sheaf
condition is the locality of membership in `I(U)`: a function on an affine open `U` whose
restrictions to the members of an open cover of `U` lie in the ideals of those members lies in
`I(U)` (`Scheme.IdealSheafData.mem_ideal_of_locally_mem`), since `I` of a basic open `D(g)` of `U`
is the localization of `I(U)` at `g`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- **Membership in `I(U)` is local**: a function on an affine open `U` lies in `I(U)` if every
point of `U` has an open neighbourhood `V` such that the restriction of the function to every affine
open inside `V ∩ U` lies in the ideal of that open. -/
theorem mem_ideal_of_locally_mem (U : X.affineOpens) (s : Γ(X, U))
    (h : ∀ x ∈ (U : X.Opens), ∃ V : X.Opens, x ∈ V ∧ ∀ (U' : X.affineOpens)
      (hU' : (U' : X.Opens) ≤ U), (U' : X.Opens) ≤ V →
        X.presheaf.map (homOfLE hU').op s ∈ I.ideal U') :
    s ∈ I.ideal U := by
  let S : Set Γ(X, U) := {g | X.presheaf.map (homOfLE (X.basicOpen_le g)).op s ∈
    I.ideal (X.affineBasicOpen g)}
  have hspan : Ideal.span S = ⊤ := by
    refine (U.2.iSup_basicOpen_eq_self_iff).mp (le_antisymm (iSup_le fun g => X.basicOpen_le _)
      fun x hxU => ?_)
    obtain ⟨V, hxV, hV⟩ := h x hxU
    obtain ⟨g, hgV, hxg⟩ := U.2.exists_basicOpen_le ⟨x, hxV⟩ hxU
    exact Opens.mem_iSup.mpr ⟨⟨g, hV (X.affineBasicOpen g) (X.basicOpen_le g) hgV⟩, hxg⟩
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ S hspan s fun g => ?_
  have := U.2.isLocalization_basicOpen (g : Γ(X, U))
  have hg := g.2
  change X.presheaf.map (homOfLE (X.basicOpen_le _)).op s ∈ I.ideal (X.affineBasicOpen _) at hg
  rw [← I.map_ideal_basicOpen] at hg
  obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, ham⟩ := (IsLocalization.mem_map_algebraMap_iff
    (Submonoid.powers (g : Γ(X, U))) Γ(X, X.basicOpen (g : Γ(X, U)))).mp hg
  have ham' : algebraMap Γ(X, U) Γ(X, X.basicOpen (g : Γ(X, U))) (s * (g : Γ(X, U)) ^ n) =
      algebraMap Γ(X, U) Γ(X, X.basicOpen (g : Γ(X, U))) a := by
    rw [map_mul]
    exact ham
  obtain ⟨⟨_, k, rfl⟩, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers (g : Γ(X, U)))
    Γ(X, X.basicOpen (g : Γ(X, U)))).mp ham'
  refine ⟨n + k, ?_⟩
  change (g : Γ(X, U)) ^ (n + k) * s ∈ I.ideal U
  rw [pow_add, mul_comm ((g : Γ(X, U)) ^ n), mul_assoc, mul_comm _ s, hc]
  exact Ideal.mul_mem_left _ _ a.2

/-- The condition defining the sections of the ideal sheaf `I` over an open `W`: the restriction to
every affine open `U ⊆ W` lies in `I(U)`. -/
def IsLocallyMem (W : X.Opens) (s : Γ(X, W)) : Prop :=
  ∀ (U : X.affineOpens) (hU : (U : X.Opens) ≤ W), X.presheaf.map (homOfLE hU).op s ∈ I.ideal U

theorem isLocallyMem_map {W W' : X.Opens} (h : W' ≤ W) {s : Γ(X, W)} (hs : I.IsLocallyMem W s) :
    I.IsLocallyMem W' (X.presheaf.map (homOfLE h).op s) := fun U hU => by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  exact hs U (hU.trans h)

/-- The submodules of sections of the ideal sheaf `I` inside `𝒪_X`: over an open `W`, the
functions whose restriction to every affine open `U ⊆ W` lies in `I(U)`. -/
noncomputable def toSubmodule : (SheafOfModules.unit X.ringCatSheaf).val.Submodule where
  obj W :=
    { carrier := {s | I.IsLocallyMem W.unop (s : Γ(X, W.unop))}
      add_mem' := fun {a b} ha hb U hU =>
        (congrArg (· ∈ I.ideal U) (map_add (X.presheaf.map (homOfLE hU).op).hom
          (a : Γ(X, W.unop)) (b : Γ(X, W.unop)))).mpr (add_mem (ha U hU) (hb U hU))
      zero_mem' := fun U hU =>
        (congrArg (· ∈ I.ideal U) (map_zero (X.presheaf.map (homOfLE hU).op).hom)).mpr
          (zero_mem _)
      smul_mem' := fun c s hs U hU =>
        (congrArg (· ∈ I.ideal U) (map_mul (X.presheaf.map (homOfLE hU).op).hom
          (c : Γ(X, W.unop)) (s : Γ(X, W.unop)))).mpr (Ideal.mul_mem_left _ _ (hs U hU)) }
  map f _ hs := I.isLocallyMem_map f.unop.le hs

/-- The sheaf condition of `toSubmodule`, from the locality of membership in `I(U)`
(`mem_ideal_of_locally_mem`). -/
theorem isSheaf_toSubmodule :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) I.toSubmodule.toPresheafOfModules.presheaf := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget (s := CategoryTheory.forget AddCommGrpCat),
    isSheaf_iff_isSheaf_of_type]
  have hF : Presieve.IsSheaf (Opens.grothendieckTopology X)
      (X.presheaf ⋙ CategoryTheory.forget CommRingCat) := by
    rw [← isSheaf_iff_isSheaf_of_type, ← Presheaf.isSheaf_iff_isSheaf_forget]
    exact X.IsSheaf
  let G : Subfunctor (X.presheaf ⋙ CategoryTheory.forget CommRingCat) :=
    { obj W := {s | I.IsLocallyMem W.unop s}
      map {W W'} f s hs := I.isLocallyMem_map f.unop.le hs }
  have hG : Presieve.IsSheaf (Opens.grothendieckTopology X) G.toFunctor := by
    refine (G.isSheaf_iff hF).mpr fun W s hs U hU => ?_
    refine I.mem_ideal_of_locally_mem U _ fun x hxU => ?_
    obtain ⟨V, f, hf, hxV⟩ := hs x (hU hxU)
    refine ⟨V, hxV, fun U' hU' hU'V => ?_⟩
    have := hf U' hU'V
    change X.presheaf.map (homOfLE hU'V).op (X.presheaf.map (homOfLE f.le).op s) ∈ I.ideal U'
      at this
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp] at this
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    exact this
  refine Presieve.isSheaf_iso (Opens.grothendieckTopology X) ?_ hG
  exact NatIso.ofComponents (fun W =>
    { hom := TypeCat.ofHom fun x => ⟨x.1, x.2⟩
      inv := TypeCat.ofHom fun x => ⟨x.1, x.2⟩ }) (fun _ => rfl)

/-- **The ideal sheaf `I` as a sheaf of `𝒪_X`-modules**: the subsheaf of `𝒪_X` of the functions
whose restriction to every affine open `U` lies in `I(U)`. -/
noncomputable def toModules : X.Modules where
  val := I.toSubmodule.toPresheafOfModules
  isSheaf := I.isSheaf_toSubmodule

/-- Over an affine open `U`, the sections of `I.toModules` are the elements of `I(U)`. -/
theorem isLocallyMem_iff (U : X.affineOpens) (s : Γ(X, U)) :
    I.IsLocallyMem U s ↔ s ∈ I.ideal U := by
  refine ⟨fun hs => ?_, fun hs U' hU' => ?_⟩
  · have := hs U le_rfl
    rwa [show homOfLE (le_refl (U : X.Opens)) = 𝟙 _ from rfl, op_id,
      CategoryTheory.Functor.map_id] at this
  · exact I.ideal_le_comap_ideal hU' hs

/-- Over an affine open `U`, the sections of `I.toModules` are the elements of `I(U)`, as modules
over `Γ(X, U)`. -/
noncomputable def toModulesSectionsEquiv (U : X.affineOpens) :
    Γ(I.toModules, U) ≃ₗ[Γ(X, U)] I.ideal U where
  toFun s := ⟨(s : I.toSubmodule.obj (op (U : X.Opens))).1,
    (I.isLocallyMem_iff U _).mp (s : I.toSubmodule.obj (op (U : X.Opens))).2⟩
  invFun a := (⟨a.1, (I.isLocallyMem_iff U a.1).mpr a.2⟩ : I.toSubmodule.obj (op (U : X.Opens)))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coe_toModulesSectionsEquiv (U : X.affineOpens) (s : Γ(I.toModules, U)) :
    ((I.toModulesSectionsEquiv U s : I.ideal U) : Γ(X, U)) =
      (s : I.toSubmodule.obj (op (U : X.Opens))).1 :=
  rfl

/-- The restriction maps of `I.toModules` are the restrictions of functions. -/
theorem coe_toModulesSectionsEquiv_restrictionMap {U V : X.affineOpens} (h : U ≤ V)
    (s : Γ(I.toModules, V)) :
    ((I.toModulesSectionsEquiv U (I.toModules.presheaf.map (homOfLE h).op s) : I.ideal U) :
        Γ(X, U)) =
      X.presheaf.map (homOfLE h).op (I.toModulesSectionsEquiv V s : Γ(X, V)) :=
  rfl

end AlgebraicGeometry.Scheme.IdealSheafData
