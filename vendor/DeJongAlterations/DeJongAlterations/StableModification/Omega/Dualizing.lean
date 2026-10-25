import DeJongAlterations.StableModification.Omega.Affine

/-!
# The relative dualizing sheaf `ω_{X/S} = j_* (Ω¹_{X/S}|_U)` and invertible modules

Let `f : X ⟶ S` be locally of finite presentation, `U = f.smoothLocus` and `j : U → X` the
inclusion. Following PLAN-SM-GEOM §3 Q1 (the elementary replacement of Grothendieck duality in
M. Temkin, *Stable modification of relative curves*, §1.2, T:1691–1712: "one can define
`ω_{C/S}` in a lengthier but much more elementary way"), this file defines

* `dualizingSheaf f = j_* (Ω¹_{X/S}|_U)` (blueprint `def:sm-omega`), with the canonical map
  `toDualizingSheaf f : Ω¹_{X/S} ⟶ ω_{X/S}`;
* `dualizingSheafRestrictIso f : ω_{X/S}|_U ≅ Ω¹_{X/S}|_U`;
* `dualizingSheafSectionsEquiv f W : Γ(ω_{X/S}, W) ≃ Γ(Ω¹_{X/S}, W ⊓ U)`;
* `IsInvertibleModule M`: `M` is locally (on affine opens `Spec Γ(X, W) → X`) isomorphic to
  `𝒪`; `IsInvertibleModule.restrict`.

For a nodal curve with smooth generic fibre over a normal base, `ω_{X/S}` is the relative
dualizing sheaf of Temkin (Deligne–Mumford): this is the content of `lem:sm-omega-invertible`,
proved here for the smooth part (`Omega/Smooth.lean`) and the node model `uv = h`
(`Omega/Node.lean`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace DeJongAlterations.StableModification.Omega

variable {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]

/-- The relative dualizing sheaf `ω_{X/S} = j_* (Ω¹_{X/S}|_U)`, `j : U = f.smoothLocus → X`
(blueprint `def:sm-omega`). -/
def dualizingSheaf : X.Modules :=
  (Scheme.Modules.pushforward f.smoothLocus.ι).obj
    ((relativeDifferentials f).restrict f.smoothLocus.ι)

/-- The canonical map `Ω¹_{X/S} ⟶ ω_{X/S}` (restriction of differentials to the smooth locus). -/
def toDualizingSheaf : relativeDifferentials f ⟶ dualizingSheaf f :=
  (Scheme.Modules.restrictAdjunction f.smoothLocus.ι).unit.app _

/-- On the smooth locus, `ω_{X/S}` is `Ω¹_{X/S}`. -/
def dualizingSheafRestrictIso :
    (dualizingSheaf f).restrict f.smoothLocus.ι ≅
      (relativeDifferentials f).restrict f.smoothLocus.ι :=
  (Scheme.Modules.restrictFunctorAdjCounitIso f.smoothLocus.ι).app _

theorem image_preimage_smoothLocus (W : X.Opens) :
    f.smoothLocus.ι ''ᵁ (f.smoothLocus.ι ⁻¹ᵁ W) = W ⊓ f.smoothLocus := by
  ext x
  simp only [Scheme.Hom.coe_image, Scheme.Hom.coe_preimage, Set.mem_image,
    Set.mem_preimage, SetLike.mem_coe, TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y.2⟩
  · rintro ⟨hW, hU⟩
    exact ⟨⟨x, hU⟩, hW, rfl⟩

/-- Restricting to an equal open and back is the identity. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.map_map_of_le {Y : Scheme.{u}} (M : Y.Modules)
    {U U' : Y.Opens} (h₁ : U' ≤ U) (h₂ : U ≤ U') (s : Γ(M, U)) :
    M.presheaf.map (homOfLE h₂).op (M.presheaf.map (homOfLE h₁).op s) = s := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    Subsingleton.elim (homOfLE h₂ ≫ homOfLE h₁) (𝟙 _), op_id,
    CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]

/-- The sections of `ω_{X/S}` over `W` are the sections of `Ω¹_{X/S}` over `W ⊓ U`. -/
def dualizingSheafSectionsEquiv (W : X.Opens) :
    Γ(dualizingSheaf f, W) ≃+ Γ(relativeDifferentials f, W ⊓ f.smoothLocus) :=
  let e := image_preimage_smoothLocus f W
  { toFun := fun s => (relativeDifferentials f).presheaf.map (homOfLE e.ge).op s
    invFun := fun s => (relativeDifferentials f).presheaf.map (homOfLE e.le).op s
    left_inv := fun s => (relativeDifferentials f).map_map_of_le e.ge e.le s
    right_inv := fun s => (relativeDifferentials f).map_map_of_le e.le e.ge s
    map_add' := fun s t => map_add _ s t }

section Invertible

variable {Y : Scheme.{u}}

/-- An `𝒪_Y`-module is *invertible* if every point has an affine open neighbourhood `W` such that
the restriction of the module to `Spec Γ(Y, W)` is isomorphic to the structure sheaf. -/
def IsInvertibleModule (M : Y.Modules) : Prop :=
  ∀ y : Y, ∃ (W : Y.Opens) (hW : IsAffineOpen W), y ∈ W ∧
    Nonempty (M.restrict hW.fromSpec ≅ SheafOfModules.unit _)

end Invertible

end DeJongAlterations.StableModification.Omega
