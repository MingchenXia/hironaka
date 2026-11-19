import Hironaka.Resolution.HironakaSingularModuleSheafStalk

/-!
# Standard native rank-one local-free data on the SAME original module stalks

Actual isomorphisms on an original over site are sent to original stalks by
restricting representatives to the given open. No stalk dictionary is an input.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Hironaka.HironakaSingularLocallyFreeStalk

open HironakaSingularModuleSheafStalk

universe u

variable {X : TopCat.{u}} (R : X.Sheaf CommRingCat.{u})
  {M N P : SheafOfModules.{u} (forgetRing R)}

private def overStalkCocone (U : Opens X) (f : M.over U ⟶ N.over U)
    (x : X) (hxU : x ∈ U) :
    Cocone ((OpenNhds.inclusion x).op ⋙ M.val.presheaf) where
  pt := TopCat.Presheaf.stalk N.val.presheaf x
  ι.app V :=
    M.val.presheaf.map (homOfLE (inf_le_left : V.unop.1 ⊓ U ≤ V.unop.1)).op ≫
      ((PresheafOfModules.toPresheaf _).map f.val).app
        (op (Over.mk (homOfLE (inf_le_right : V.unop.1 ⊓ U ≤ U)))) ≫
      TopCat.Presheaf.germ N.val.presheaf (V.unop.1 ⊓ U) x ⟨V.unop.2, hxU⟩
  ι.naturality V W i := by
    ext m
    let j : W.unop.1 ⊓ U ⟶ V.unop.1 ⊓ U :=
      homOfLE (inf_le_inf i.unop.le le_rfl)
    let jOver : Over.mk (homOfLE (inf_le_right : W.unop.1 ⊓ U ≤ U)) ⟶
        Over.mk (homOfLE (inf_le_right : V.unop.1 ⊓ U ≤ U)) := Over.homMk j
    have hn := PresheafOfModules.naturality_apply f.val jOver.op
      (M.val.map (homOfLE (inf_le_left : V.unop.1 ⊓ U ≤ V.unop.1)).op m)
    change f.val.app (op (Over.mk (homOfLE (inf_le_right : W.unop.1 ⊓ U ≤ U))))
        (M.val.map j.op
          (M.val.map (homOfLE (inf_le_left : V.unop.1 ⊓ U ≤ V.unop.1)).op m)) =
      N.val.map j.op
        (f.val.app (op (Over.mk (homOfLE (inf_le_right : V.unop.1 ⊓ U ≤ U))))
          (M.val.map (homOfLE inf_le_left).op m)) at hn
    change TopCat.Presheaf.germ N.val.presheaf (W.unop.1 ⊓ U) x ⟨W.unop.2, hxU⟩
        (f.val.app (op (Over.mk (homOfLE (inf_le_right : W.unop.1 ⊓ U ≤ U))))
          (M.val.map (homOfLE inf_le_left).op
            (M.val.map ((OpenNhds.inclusion x).map i.unop).op m))) =
      TopCat.Presheaf.germ N.val.presheaf (V.unop.1 ⊓ U) x ⟨V.unop.2, hxU⟩
        (f.val.app (op (Over.mk (homOfLE (inf_le_right : V.unop.1 ⊓ U ≤ U))))
          (M.val.map (homOfLE inf_le_left).op m))
    erw [← TopCat.Presheaf.germ_res_apply N.val.presheaf j x ⟨W.unop.2, hxU⟩]
    congr 1
    erw [← hn]
    congr 1
    erw [← M.val.map_comp_apply, ← M.val.map_comp_apply]
    congr 1

/-- The actual additive colimit map induced by an original morphism on the over site. -/
private def overStalkAddHom (U : Opens X) (f : M.over U ⟶ N.over U)
    (x : X) (hxU : x ∈ U) :
    ↑(TopCat.Presheaf.stalk M.val.presheaf x) →+
      ↑(TopCat.Presheaf.stalk N.val.presheaf x) :=
  (colimit.desc _ (overStalkCocone R U f x hxU)).hom

private theorem overStalkAddHom_germ (U : Opens X) (f : M.over U ⟶ N.over U)
    (x : X) (hxU : x ∈ U) (V : Opens X) (hxV : x ∈ V)
    (m : M.val.obj (op V)) :
    overStalkAddHom R U f x hxU (TopCat.Presheaf.germ M.val.presheaf V x hxV m) =
      TopCat.Presheaf.germ N.val.presheaf (V ⊓ U) x ⟨hxV, hxU⟩
        (f.val.app (op (Over.mk (homOfLE inf_le_right)))
          (M.val.map (homOfLE inf_le_left).op m)) := by
  exact ConcreteCategory.congr_hom
    (colimit.ι_desc (overStalkCocone R U f x hxU) (op ⟨V, hxV⟩)) m

private theorem overStalkAddHom_germ_of_le (U : Opens X) (f : M.over U ⟶ N.over U)
    (x : X) (hxU : x ∈ U) (V : Opens X) (hxV : x ∈ V) (hVU : V ≤ U)
    (m : M.val.obj (op V)) :
    overStalkAddHom R U f x hxU (TopCat.Presheaf.germ M.val.presheaf V x hxV m) =
      TopCat.Presheaf.germ N.val.presheaf V x hxV
        (f.val.app (op (Over.mk (homOfLE hVU))) m) := by
  rw [overStalkAddHom_germ]
  let j : Over.mk (homOfLE (inf_le_right : V ⊓ U ≤ U)) ⟶
      Over.mk (homOfLE hVU) := Over.homMk (homOfLE inf_le_left)
  have hn := PresheafOfModules.naturality_apply f.val j.op m
  change f.val.app (op (Over.mk (homOfLE (inf_le_right : V ⊓ U ≤ U))))
      (M.val.map (homOfLE inf_le_left).op m) =
    N.val.map (homOfLE inf_le_left).op
      (f.val.app (op (Over.mk (homOfLE hVU))) m) at hn
  rw [hn]
  exact TopCat.Presheaf.germ_res_apply N.val.presheaf (homOfLE inf_le_left) x ⟨hxV, hxU⟩ _

/-- A genuine local module morphism acts linearly on the SAME original global stalks. -/
def stalkLinearMapOfOver (U : Opens X) (f : M.over U ⟶ N.over U)
    (x : X) (hxU : x ∈ U) :
    ↑(TopCat.Presheaf.stalk M.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk R.obj x)]
      ↑(TopCat.Presheaf.stalk N.val.presheaf x) :=
  { overStalkAddHom R U f x hxU with
    map_smul' := by
      intro r m
      change overStalkAddHom R U f x hxU (r • m) =
        r • overStalkAddHom R U f x hxU m
      obtain ⟨V, hVU, hxV, m, rfl⟩ :=
        TopCat.Presheaf.exists_le_germ_eq M.val.presheaf m hxU
      obtain ⟨W, hWV, hxW, r, rfl⟩ :=
        TopCat.Presheaf.exists_le_germ_eq R.obj r hxV
      rw [← TopCat.Presheaf.germ_res_apply M.val.presheaf (homOfLE hWV) x hxW m]
      erw [← M.val.germ_smul (R := R.obj),
        overStalkAddHom_germ_of_le R U f x hxU W hxW (hWV.trans hVU),
        overStalkAddHom_germ_of_le R U f x hxU W hxW (hWV.trans hVU),
        ← N.val.germ_smul (R := R.obj)]
      congr 1
      exact (f.val.app (op (Over.mk (homOfLE (hWV.trans hVU))))).hom.map_smul r _ }

@[simp]
theorem stalkLinearMapOfOver_germ_of_le (U : Opens X) (f : M.over U ⟶ N.over U)
    (x : X) (hxU : x ∈ U) (V : Opens X) (hxV : x ∈ V) (hVU : V ≤ U)
    (m : M.val.obj (op V)) :
    stalkLinearMapOfOver R U f x hxU (TopCat.Presheaf.germ M.val.presheaf V x hxV m) =
      TopCat.Presheaf.germ N.val.presheaf V x hxV
        (f.val.app (op (Over.mk (homOfLE hVU))) m) :=
  overStalkAddHom_germ_of_le R U f x hxU V hxV hVU m

@[simp]
theorem stalkLinearMapOfOver_id (U : Opens X) (x : X) (hxU : x ∈ U) :
    stalkLinearMapOfOver R U (𝟙 (M.over U)) x hxU = LinearMap.id := by
  ext m
  obtain ⟨V, hVU, hxV, m, rfl⟩ :=
    TopCat.Presheaf.exists_le_germ_eq M.val.presheaf m hxU
  erw [stalkLinearMapOfOver_germ_of_le R U _ x hxU V hxV hVU]
  rfl

@[simp]
theorem stalkLinearMapOfOver_comp (U : Opens X)
    (f : M.over U ⟶ N.over U) (g : N.over U ⟶ P.over U) (x : X) (hxU : x ∈ U) :
    stalkLinearMapOfOver R U (f ≫ g) x hxU =
      (stalkLinearMapOfOver R U g x hxU).comp (stalkLinearMapOfOver R U f x hxU) := by
  ext m
  obtain ⟨V, hVU, hxV, m, rfl⟩ :=
    TopCat.Presheaf.exists_le_germ_eq M.val.presheaf m hxU
  simp only [LinearMap.comp_apply]
  erw [stalkLinearMapOfOver_germ_of_le R U _ x hxU V hxV hVU,
    stalkLinearMapOfOver_germ_of_le R U _ x hxU V hxV hVU,
    stalkLinearMapOfOver_germ_of_le R U _ x hxU V hxV hVU]
  rfl

/-- A genuine over-site isomorphism induces an equivalence of original global stalks. -/
def stalkLinearEquivOfOverIso (U : Opens X) (e : M.over U ≅ N.over U)
    (x : X) (hxU : x ∈ U) :
    ↑(TopCat.Presheaf.stalk M.val.presheaf x) ≃ₗ[↑(TopCat.Presheaf.stalk R.obj x)]
      ↑(TopCat.Presheaf.stalk N.val.presheaf x) :=
  LinearEquiv.ofLinearMap
    (stalkLinearMapOfOver R U e.hom x hxU) (stalkLinearMapOfOver R U e.inv x hxU)
    (by rw [← stalkLinearMapOfOver_comp, e.inv_hom_id, stalkLinearMapOfOver_id])
    (by rw [← stalkLinearMapOfOver_comp, e.hom_inv_id, stalkLinearMapOfOver_id])

private def overUnitIso (U : Opens X) :
    (SheafOfModules.unit (forgetRing R)).over U ≅
      SheafOfModules.unit ((forgetRing R).over U) := Iso.refl _

/-- The unit-to-module equivalence of SAME original stalks from an actual local isomorphism. -/
def stalkLinearEquivOfOverUnitIso (U : Opens X)
    (e : SheafOfModules.unit ((forgetRing R).over U) ≅ M.over U)
    (x : X) (hxU : x ∈ U) :
    ↑(TopCat.Presheaf.stalk R.obj x) ≃ₗ[↑(TopCat.Presheaf.stalk R.obj x)]
      ↑(TopCat.Presheaf.stalk M.val.presheaf x) :=
  (unitStalkLinearEquiv R x).symm.trans
    (stalkLinearEquivOfOverIso R U (overUnitIso R U ≪≫ e) x hxU)

/-- Standard native local-free data with exactly one original generator at every cover member
produces invertibility on the SAME original module stalk at every original point. -/
theorem stalkInvertible_of_locallyFreeData
    (q : M.LocalGeneratorsData) [q.IsLocallyFreeData]
    [∀ i, Unique (q.generators i).I] (x : X) :
    Module.Invertible ↑(TopCat.Presheaf.stalk R.obj x)
      ↑(TopCat.Presheaf.stalk M.val.presheaf x) := by
  obtain ⟨V, f, hV, hxV⟩ :=
    (Opens.mem_grothendieckTopology X).mp (q.coversTop ⊤) x (by trivial)
  obtain ⟨i, ⟨g⟩⟩ := (Sieve.mem_ofObjects_iff q.X f).mp hV
  have hxU : x ∈ q.X i := g.le hxV
  let e : SheafOfModules.unit ((forgetRing R).over (q.X i)) ≅ M.over (q.X i) :=
    (coproductUniqueIso (fun _ : (q.generators i).I ↦
      SheafOfModules.unit ((forgetRing R).over (q.X i)))).symm ≪≫
      asIso (q.generators i).π
  exact Module.Invertible.congr (stalkLinearEquivOfOverUnitIso R (q.X i) e x hxU)

end Hironaka.HironakaSingularLocallyFreeStalk
