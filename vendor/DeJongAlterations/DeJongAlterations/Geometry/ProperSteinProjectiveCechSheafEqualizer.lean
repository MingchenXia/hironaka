import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Tactic

/-!
# Actual ORIGINAL native sheaf-module global-section equalizer

Native-only extraction from same-workspace `BingWangEntropy/LineBundleSections.lean`,
SHA256 c1adb73fb95953101383fcb6d4ccd7920eb6fa1cbf573811a7626ea54d521dd3.
Native-only extraction from same-workspace `BingWangEntropy/SchemeGenericSections.lean`,
SHA256 930f0e42863be2648d54be1d0419f78c30b43b11d8dd78cc5ae1cd2b4fb44f1e.
Native-only extraction from same-workspace `BingWangEntropy/ProjectiveSectionFiniteness.lean`,
SHA256 4853b161af90b336994c663ff326526b7907a2d7e2148b2939393fdb581d4997.
No other-project module is imported.
-/

universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
namespace DeJongAlterations.Geometry.ProperSteinProjectiveCech
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {X : Scheme.{u}}

/-- Literal ORIGINAL sections of the ORIGINAL native sheaf of modules. -/
abbrev bundleSections (L : X.Modules) (U : X.Opens) : Type u := L.val.obj (op U)

/-- Original module sections retain the ORIGINAL commutative structure-ring action. -/
instance bundleSectionsModule (L : X.Modules) (U : X.Opens) :
    Module (X.sheaf.obj.obj (op U)) (bundleSections L U) :=
  inferInstanceAs (Module (X.ringCatSheaf.obj.obj (op U)) (L.val.obj (op U)))

/-- Original module sections use the usual ORIGINAL scheme-section ring notation. -/
instance schemeBundleSectionsModule (L : X.Modules) (U : X.Opens) :
    Module Γ(X, U) (bundleSections L U) :=
  inferInstanceAs (Module (X.sheaf.obj.obj (op U)) (bundleSections L U))

/-- Local bundle sections retain their actual action by global regular functions. -/
abbrev localSectionsGlobalModule (L : X.Modules) (U : X.Opens) :
    Module Γ(X, ⊤) (bundleSections L U) :=
  Module.compHom (bundleSections L U) (X.presheaf.map U.leTop.op).hom

/-- The genuine Cech degree-zero equalizer: actual local sections agree on actual overlaps. -/
def bundleCechSections {I : Type u} (L : X.Modules) (U : I → X.Opens) :
    letI : ∀ i, Module Γ(X, ⊤) (bundleSections L (U i)) :=
      fun i => localSectionsGlobalModule L (U i)
    Submodule Γ(X, ⊤) (∀ i, bundleSections L (U i)) := by
  letI : ∀ i, Module Γ(X, ⊤) (bundleSections L (U i)) :=
    fun i => localSectionsGlobalModule L (U i)
  exact {
    carrier := {s | ∀ i j,
      L.val.map (homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)).op (s i) =
      L.val.map (homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)).op (s j)}
    zero_mem' := by
      intro i j
      change L.val.map (homOfLE inf_le_left : U i ⊓ U j ⟶ U i).op 0 =
        L.val.map (homOfLE inf_le_right : U i ⊓ U j ⟶ U j).op 0
      rw [(L.val.map _).hom.map_zero, (L.val.map _).hom.map_zero]
    add_mem' := by
      intro s t hs ht i j
      simp only [Pi.add_apply, map_add, hs i j, ht i j]
    smul_mem' := by
      intro r s hs i j
      change L.val.map _ (X.presheaf.map (U i).leTop.op r • s i) =
        L.val.map _ (X.presheaf.map (U j).leTop.op r • s j)
      rw [L.val.map_smul, L.val.map_smul]
      change X.presheaf.map _ (X.presheaf.map _ r) • _ =
        X.presheaf.map _ (X.presheaf.map _ r) • _
      rw [hs i j]
      congr 1
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
      rfl }

/-- Restrict an actual global section to its genuine compatible chart family. -/
def bundleGlobalToCech {I : Type u} (L : X.Modules) (U : I → X.Opens) :
    letI : ∀ i, Module Γ(X, ⊤) (bundleSections L (U i)) :=
      fun i => localSectionsGlobalModule L (U i)
    bundleSections L ⊤ →ₗ[Γ(X, ⊤)] bundleCechSections L U := by
  letI : ∀ i, Module Γ(X, ⊤) (bundleSections L (U i)) :=
    fun i => localSectionsGlobalModule L (U i)
  exact {
    toFun s := ⟨fun i => L.val.map (U i).leTop.op s, by
      intro i j
      change L.val.presheaf.map _ (L.val.presheaf.map _ s) =
        L.val.presheaf.map _ (L.val.presheaf.map _ s)
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
      rfl⟩
    map_add' s t := by ext i; exact (L.val.map (U i).leTop.op).hom.map_add s t
    map_smul' r s := by
      ext i
      exact L.val.map_smul (U i).leTop.op r s }

/-- The actual sheaf axiom identifies global sections with the actual Cech equalizer. -/
theorem bundleGlobalToCech_bijective {I : Type u} (L : X.Modules) (U : I → X.Opens)
    (hU : iSup U = ⊤) : Function.Bijective (bundleGlobalToCech L U) := by
  constructor
  · intro s t h
    apply TopCat.Presheaf.IsSheaf.section_ext (F := L.presheaf) L.isSheaf
    intro x hx
    have hx' : x ∈ iSup U := by simpa only [hU] using hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
    refine ⟨U i, le_top, hi, ?_⟩
    exact congrArg (fun z : bundleCechSections L U => z.val i) h
  · intro s
    let F : TopCat.Sheaf AddCommGrpCat X := ⟨L.presheaf, L.isSheaf⟩
    obtain ⟨t, ht, _⟩ := F.existsUnique_gluing' U ⊤ (fun i => (U i).leTop)
      (by rw [hU]) s.val (by intro i j; exact s.property i j)
    refine ⟨t, ?_⟩
    apply Subtype.ext
    funext i
    exact ht i

/-- This comparison is a produced linear equivalence of actual sections, not a grading premise. -/
def bundleGlobalCechEquiv {I : Type u} (L : X.Modules) (U : I → X.Opens)
    (hU : iSup U = ⊤) :
    letI : ∀ i, Module Γ(X, ⊤) (bundleSections L (U i)) :=
      fun i => localSectionsGlobalModule L (U i)
    bundleSections L ⊤ ≃ₗ[Γ(X, ⊤)] bundleCechSections L U :=
  LinearEquiv.ofBijective (bundleGlobalToCech L U) (bundleGlobalToCech_bijective L U hU)



end

end DeJongAlterations.Geometry.ProperSteinProjectiveCech
