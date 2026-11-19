import Hironaka.Resolution.HironakaSingularModuleSheafStalk

/-! One original neighbourhood realizes a finite family of original module
stalk elements, and a finite family of original section-germ equalities.
Blueprint: `hironaka-g10-native-section-spreading.tex`. -/

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite TopologicalSpace

namespace Hironaka.HironakaChowNativeSectionSpreading

universe u
variable {X : TopCat.{u}} {R : X.Presheaf CommRingCat.{u}}
  (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
  {I : Type*} [Finite I] (x : X) (U : Opens X) (hxU : x ∈ U)

include hxU in
/-- The same original finite module-stalk family is represented on ONE original open. -/
theorem exists_common_germ_representatives
    (a : I → ↑(TopCat.Presheaf.stalk M.presheaf x)) :
    ∃ (V : Opens X) (_hVU : V ≤ U) (hxV : x ∈ V) (s : I → M.obj (op V)),
      ∀ i, TopCat.Presheaf.germ M.presheaf V x hxV (s i) = a i := by
  classical
  choose V hVU hxV s hs using
    fun i => TopCat.Presheaf.exists_le_germ_eq M.presheaf (a i) hxU
  let W : Opens X := U ⊓ ⨅ i, V i
  have hWU : W ≤ U := inf_le_left
  have hWV (i : I) : W ≤ V i := inf_le_right.trans (iInf_le V i)
  have hxW : x ∈ W := by
    change x ∈ (U : Set X) ∩ ((⨅ i, V i : Opens X) : Set X)
    rw [Opens.coe_iInf]
    exact ⟨hxU, Set.mem_iInter.mpr hxV⟩
  refine ⟨W,hWU,hxW,fun i => M.map (homOfLE (hWV i)).op (s i),?_⟩
  intro i
  exact (TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE (hWV i)) x hxW (s i)).trans (hs i)

/-- Finitely many ORIGINAL section-germ equalities hold on ONE actual original open. -/
theorem exists_common_restriction_eq_of_germ_eq
    (s t : I → M.obj (op U))
    (h : ∀ i, TopCat.Presheaf.germ M.presheaf U x hxU (s i) =
      TopCat.Presheaf.germ M.presheaf U x hxU (t i)) :
    ∃ (V : Opens X) (hVU : V ≤ U) (_hxV : x ∈ V),
      ∀ i, M.map (homOfLE hVU).op (s i) = M.map (homOfLE hVU).op (t i) := by
  classical
  choose V hxV iU jU heq using
    fun i => TopCat.Presheaf.germ_eq M.presheaf x hxU hxU (s i) (t i) (h i)
  let W : Opens X := U ⊓ ⨅ i, V i
  have hWU : W ≤ U := inf_le_left
  have hWV (i : I) : W ≤ V i := inf_le_right.trans (iInf_le V i)
  have hxW : x ∈ W := by
    change x ∈ (U : Set X) ∩ ((⨅ i, V i : Opens X) : Set X)
    rw [Opens.coe_iInf]
    exact ⟨hxU, Set.mem_iInter.mpr hxV⟩
  refine ⟨W,hWU,hxW,?_⟩
  intro i
  have hi := congrArg (fun m => M.map (homOfLE (hWV i)).op m) (heq i)
  change M.map (homOfLE (hWV i)).op (M.map (iU i).op (s i)) =
    M.map (homOfLE (hWV i)).op (M.map (jU i).op (t i)) at hi
  rw [← M.map_comp_apply, ← M.map_comp_apply] at hi
  exact (M.congr_map_apply (Subsingleton.elim _ _) (s i)).trans
    (hi.trans (M.congr_map_apply (Subsingleton.elim _ _) (t i)))

end Hironaka.HironakaChowNativeSectionSpreading
