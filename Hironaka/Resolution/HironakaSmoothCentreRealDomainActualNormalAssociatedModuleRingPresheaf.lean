/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothCentreRealDomainActualNormalAssociatedRingSheaf

/-! The actual section ring, with its independently defined ambient action,
is the genuine whole coproduct of the original layer module presheaves. -/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped DirectSum Topology Manifold ContDiff
open CategoryTheory CategoryTheory.Limits Opposite

namespace Hironaka.HironakaSmoothCentreRealDomainActualNormalAssociatedModuleRingPresheaf
noncomputable section

open Hironaka.HolomorphicIdealSheaves
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaSmoothCentreRealDomainActualNormalLayerScalars
  HironakaSmoothCentreRealDomainActualNormalAssociatedSheaf
  HironakaSmoothCentreRealDomainActualNormalAssociatedRingPresheaf

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The literal original section ring, with its actual ambient action and restrictions. -/
def actualNormalAssociatedRingModulePresheaf (A : GermIdeal n M) (C : Set M) :
    ActualModulePresheaf n M := by
  let G := actualNormalAssociatedRingPresheaf A C ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
  letI (U : (Opens M)ᵒᵖ) :
      Module (((actualComplexStructureSheaf (n := n) M).presheaf ⋙
        forget₂ CommRingCat RingCat).obj U) (G.obj U) := by
    change Module (actualComplexSection (n := n) (unop U))
      (actualNormalAssociatedRingSection A C (unop U))
    infer_instance
  apply PresheafOfModules.ofPresheaf G
  intro U V i r s
  change actualComplexSection (n := n) (unop U) at r
  change actualNormalAssociatedRingSection A C (unop U) at s
  change actualNormalAssociatedRingRestrict A C (unop V) (unop U) _ (r • s) = _
  rw [Algebra.smul_def, map_mul, actualNormalAssociatedRingRestrict_algebraMap]
  have hi : (homOfLE (leOfHom i.unop)).op = i := Subsingleton.elim _ _
  rw [hi]
  exact (Algebra.smul_def
    ((actualComplexStructureSheaf (n := n) M).presheaf.map i r)
    (actualNormalAssociatedRingRestrict A C (unop V) (unop U) (leOfHom i.unop) s)).symm

/-- Forgetting the independent ambient action retains the SAME original additive ring presheaf. -/
theorem actualNormalAssociatedRingModulePresheaf_presheaf (A : GermIdeal n M) (C : Set M) :
    (actualNormalAssociatedRingModulePresheaf A C).presheaf =
      actualNormalAssociatedRingPresheaf A C ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat := rfl

/-- Every original homogeneous section inclusion is a genuine ambient module presheaf morphism. -/
def actualNormalAssociatedRingModuleDegreeMap (A : GermIdeal n M) (C : Set M) (q : ℕ) :
    actualNormalLayerModulePresheaf A C q ⟶ actualNormalAssociatedRingModulePresheaf A C where
  app U := ModuleCat.ofHom (X := (actualNormalLayerModulePresheaf A C q).obj U)
    (Y := (actualNormalAssociatedRingModulePresheaf A C).obj U)
    (DirectSum.lof (actualComplexSection (n := n) (unop U)) ℕ
      (fun k => HironakaSmoothCentreRealDomainActualNormalLayerStalk.actualNormalLayerSection A C k (unop U)) q)
  naturality := by
    intro U V i
    ext s
    exact (actualNormalAssociatedRingRestrict_of A C (unop V) (unop U)
      (leOfHom i.unop) q s).symm

/-- The actual ring-module presheaf has all actual degree-module inclusions as a cofan. -/
def actualNormalAssociatedRingModuleCofan (A : GermIdeal n M) (C : Set M) :
    Cofan (fun q : ℕ => actualNormalLayerModulePresheaf A C q) :=
  Cofan.mk (actualNormalAssociatedRingModulePresheaf A C)
    (actualNormalAssociatedRingModuleDegreeMap A C)

/-- True section finite support proves the full module-presheaf coproduct universal property. -/
def actualNormalAssociatedRingModuleCofanIsColimit (A : GermIdeal n M) (C : Set M) :
    IsColimit (actualNormalAssociatedRingModuleCofan A C) where
  desc s :=
    { app := fun U => ModuleCat.ofHom
        (X := (actualNormalAssociatedRingModulePresheaf A C).obj U) (Y := s.pt.obj U)
        (DirectSum.toModule (actualComplexSection (n := n) (unop U)) ℕ (s.pt.obj U)
          (fun q => ((s.ι.app ⟨q⟩).app U).hom))
      naturality := by
        intro U V i
        apply ModuleCat.hom_ext
        apply DirectSum.linearMap_ext
        intro q
        ext x
        change DirectSum.toModule (actualComplexSection (n := n) (unop V)) ℕ (s.pt.obj V)
            (fun k => ((s.ι.app ⟨k⟩).app V).hom)
            (actualNormalAssociatedRingRestrict A C (unop V) (unop U) _
              (DirectSum.of (fun k => HironakaSmoothCentreRealDomainActualNormalLayerStalk.actualNormalLayerSection A C k (unop U)) q x)) =
          s.pt.map i
            (DirectSum.toModule (actualComplexSection (n := n) (unop U)) ℕ (s.pt.obj U)
              (fun k => ((s.ι.app ⟨k⟩).app U).hom)
              (DirectSum.of (fun k => HironakaSmoothCentreRealDomainActualNormalLayerStalk.actualNormalLayerSection A C k (unop U)) q x))
        rw [actualNormalAssociatedRingRestrict_of]
        erw [DirectSum.toModule_lof, DirectSum.toModule_lof]
        exact PresheafOfModules.naturality_apply (s.ι.app ⟨q⟩) i x }
  fac s j := by
    rcases j with ⟨q⟩
    ext U x
    exact DirectSum.toModule_lof (R := actualComplexSection (n := n) (unop U))
      (ι := ℕ) (M := fun k => HironakaSmoothCentreRealDomainActualNormalLayerStalk.actualNormalLayerSection A C k (unop U))
      (N := s.pt.obj U) (φ := fun k => ((s.ι.app ⟨k⟩).app U).hom) q x
  uniq s m hm := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply DirectSum.linearMap_ext
    intro q
    ext x
    change (m.app U).hom (DirectSum.lof (actualComplexSection (n := n) (unop U)) ℕ
      (fun k => HironakaSmoothCentreRealDomainActualNormalLayerStalk.actualNormalLayerSection A C k (unop U)) q x) =
      DirectSum.toModule (actualComplexSection (n := n) (unop U)) ℕ (s.pt.obj U)
        (fun k => ((s.ι.app ⟨k⟩).app U).hom)
        (DirectSum.lof (actualComplexSection (n := n) (unop U)) ℕ
          (fun k => HironakaSmoothCentreRealDomainActualNormalLayerStalk.actualNormalLayerSection A C k (unop U)) q x)
    erw [DirectSum.toModule_lof]
    exact congrArg (fun f => (f.app U).hom x) (hm ⟨q⟩)

/-- The canonical WHOLE module-presheaf isomorphism, without a coherence assumption. -/
def actualNormalAssociatedModuleRingPresheafIso (A : GermIdeal n M) (C : Set M) :
    actualNormalAssociatedModulePresheaf A C ≅ actualNormalAssociatedRingModulePresheaf A C :=
  colimit.isoColimitCocone
    ⟨actualNormalAssociatedRingModuleCofan A C, actualNormalAssociatedRingModuleCofanIsColimit A C⟩

/-- The whole presheaf comparison retains each literal original degree inclusion. -/
theorem actualNormalAssociatedModuleRingPresheafIso_degree (A : GermIdeal n M) (C : Set M)
    (q : ℕ) :
    Sigma.ι (fun k : ℕ => actualNormalLayerModulePresheaf A C k) q ≫
      (actualNormalAssociatedModuleRingPresheafIso A C).hom =
        actualNormalAssociatedRingModuleDegreeMap A C q :=
  colimit.isoColimitCocone_ι_hom
    ⟨actualNormalAssociatedRingModuleCofan A C, actualNormalAssociatedRingModuleCofanIsColimit A C⟩
    (⟨q⟩ : Discrete ℕ)

end
end Hironaka.HironakaSmoothCentreRealDomainActualNormalAssociatedModuleRingPresheaf
