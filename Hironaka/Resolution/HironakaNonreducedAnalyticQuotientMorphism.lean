import Hironaka.Resolution.HironakaNonreducedAnalyticQuotientModel
import Hironaka.Resolution.HironakaSingularSubspaceBlowupCartier

/-! Actual morphisms between the original nonreduced native quotient LRS.
Only the original holomorphic map and whole pulled-ideal inclusion are input.
BP FIRST: hironaka-nonreduced-analytic-quotient-morphism.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaNonreducedAnalyticQuotientMorphism
noncomputable section
open Hironaka.HolomorphicIdealSheaves
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaSmoothCentreRealDomainActualIdealPresheaf
  HironakaSmoothCentreRealDomainActualCentrePowerStalk
  HironakaSmoothCentreRealDomainActualRemainderQuotientStalk
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaSingularSubspaceBlowupCartier HironakaNonreducedAnalyticQuotientModel
  RelativePrincipalizationSpan InvertibleIdealQuotient

variable {n m : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]

/-- Surjectivity follows from the WHOLE original quotient formula, not from a supplied certificate. -/
theorem quotientInclusion_surjective_stalk (A : GermIdeal n M) (hA : A.IsCoherent)
    (x : A.zeroLocus) : Function.Surjective ((quotientInclusion A hA).stalkMap x) := by
  intro z
  obtain ⟨r,hr⟩ := Ideal.Quotient.mk_surjective (quotientStalkWholeEquiv A hA x z)
  refine ⟨r,(quotientStalkWholeEquiv A hA x).injective ?_⟩
  rw [quotientInclusion_stalk,hr]

/-- BOTH point maps and sheaf maps cancel through the genuine closed quotient inclusion. -/
instance quotientInclusion_mono (A : GermIdeal n M) (hA : A.IsCoherent) :
    Mono (quotientInclusion A hA) := by
  apply LocallyRingedSpace.forgetToSheafedSpace.mono_of_mono_map
  apply SheafedSpace.mono_of_base_injective_of_stalk_epi
  · exact (quotientInclusion_isClosedEmbedding A hA).injective
  · intro x
    exact ConcreteCategory.epi_of_surjective _ (quotientInclusion_surjective_stalk A hA x)

private theorem wholeIdeal_mono {A C : GermIdeal n M} (hAC : GermIdeal.Le A C) (x : M) :
    actualWholeSheafStalkIdeal A x ≤ actualWholeSheafStalkIdeal C x := by
  apply Ideal.span_le.mpr
  rintro _ ⟨g,hg,hmem,rfl⟩
  exact Ideal.subset_span ⟨g,hg,hAC x g hmem,rfl⟩

private theorem map_support {f : M → N}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (A : GermIdeal n M) (B : GermIdeal m N) (hB : B.IsCoherent)
    (hAB : GermIdeal.Le (GermIdeal.pullback (m := n) f B) A) :
    ∀ x ∈ A.zeroLocus, f x ∈ B.zeroLocus := by
  intro x hx g hg
  have hhol : HolomorphicAt n (g ∘ f) x :=
    (GermIdeal.IsCoherent.holomorphicAt_mem hB hg).comp_contMDiff
      (Eventually.of_forall fun _ => hf.contMDiffAt)
  exact hx (g ∘ f) (hAB x (g ∘ f)
    (GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨g,hg,rfl⟩ hhol)))

/-- The original point map, with support preservation derived from the entire ideal condition. -/
@[implicit_reducible]
def quotientTopMap {f : M → N}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (A : GermIdeal n M) (B : GermIdeal m N) (hB : B.IsCoherent)
    (hAB : GermIdeal.Le (GermIdeal.pullback (m := n) f B) A) :
    TopCat.of A.zeroLocus ⟶ TopCat.of B.zeroLocus :=
  actualSubspaceMapTop hf (map_support hf A B hB hAB)

private theorem sectionIdeal_pullback {f : M → N}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (A : GermIdeal n M) (B : GermIdeal m N) (hB : B.IsCoherent)
    (hAB : GermIdeal.Le (GermIdeal.pullback (m := n) f B) A)
    (U : Opens N) (s : actualComplexSection (n := m) U)
    (hs : s ∈ actualSectionIdeal B U) :
    (ChartedSpace.locallyRingedSpaceMap f hf).toHom.c.app (op U) s ∈
      actualSectionIdeal A ((Opens.map (actualAmbientMap hf)).obj U) := by
  intro x hx
  have hi : (ChartedSpace.locallyRingedSpaceMap f hf).stalkMap x
      ((actualComplexStructureSheaf (n := m) N).presheaf.germ U (f x) hx s) ∈
        actualWholeSheafStalkIdeal (GermIdeal.pullback (m := n) f B) x := by
    rw [←map_actualWholeSheafStalkIdeal_native_pullback hf B hB x]
    exact Ideal.mem_map_of_mem _ (hs (f x) hx)
  have h := wholeIdeal_mono hAB x hi
  have hF := PresheafedSpace.stalkMap_germ_apply
    (ChartedSpace.locallyRingedSpaceMap f hf).toHom U x hx s
  exact hF ▸ h

/-- Genuine pullback of every raw whole quotient-section ring. -/
def rawQuotientSectionMap {f : M → N}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (A : GermIdeal n M) (B : GermIdeal m N) (hB : B.IsCoherent)
    (hAB : GermIdeal.Le (GermIdeal.pullback (m := n) f B) A) (U : Opens N) :
    ((quotientPresheaf B).obj (op U)).carrier →+*
      ((quotientPresheaf A).obj (op ((Opens.map (actualAmbientMap hf)).obj U))).carrier :=
  Ideal.Quotient.lift (actualRemainderSectionIdeal B univ 1 U)
    ((Ideal.Quotient.mk (actualRemainderSectionIdeal A univ 1
      ((Opens.map (actualAmbientMap hf)).obj U))).comp
      ((ChartedSpace.locallyRingedSpaceMap f hf).toHom.c.app (op U)).hom)
    (by
      intro s hs
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [remainderSectionIdeal_eq] at hs ⊢
      exact sectionIdeal_pullback hf A B hB hAB U s hs)

private def rawQuotientPresheafMap {f : M → N}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (A : GermIdeal n M) (B : GermIdeal m N) (hB : B.IsCoherent)
    (hAB : GermIdeal.Le (GermIdeal.pullback (m := n) f B) A) :
    quotientPresheaf B ⟶ (TopCat.Presheaf.pushforward CommRingCat (actualAmbientMap hf)).obj
      (quotientPresheaf A) where
  app U := CommRingCat.ofHom (rawQuotientSectionMap hf A B hB hAB (unop U))
  naturality U V i := by
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext s
    exact congrArg (Ideal.Quotient.mk (actualRemainderSectionIdeal A univ 1
      ((Opens.map (actualAmbientMap hf)).obj (unop V))))
      (ConcreteCategory.congr_hom ((ChartedSpace.locallyRingedSpaceMap f hf).toHom.c.naturality i) s)

private def quotientToModel (A : GermIdeal n M) :
    quotientPresheaf A ⟶
      (TopCat.Presheaf.pushforward CommRingCat (actualSubspaceTopInclusion A.zeroLocus)).obj
        (quotientModelSheaf A).presheaf :=
  (TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat
    (actualSubspaceTopInclusion A.zeroLocus)).unit.app (quotientPresheaf A) ≫
    (TopCat.Presheaf.pushforward CommRingCat (actualSubspaceTopInclusion A.zeroLocus)).map
      (quotientModelUnit A)

private def modelPresheafMap {f : M → N}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (A : GermIdeal n M) (B : GermIdeal m N) (hB : B.IsCoherent)
    (hAB : GermIdeal.Le (GermIdeal.pullback (m := n) f B) A) :
    quotientModelPresheaf B ⟶
      (TopCat.Presheaf.pushforward CommRingCat (quotientTopMap hf A B hB hAB)).obj
        (quotientModelSheaf A).presheaf :=
  ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat
    (actualSubspaceTopInclusion B.zeroLocus)).homEquiv (quotientPresheaf B)
      ((TopCat.Presheaf.pushforward CommRingCat (quotientTopMap hf A B hB hAB)).obj
        (quotientModelSheaf A).presheaf)).symm
    (rawQuotientPresheafMap hf A B hB hAB ≫
      (TopCat.Presheaf.pushforward CommRingCat (actualAmbientMap hf)).map (quotientToModel A))

private def modelSheafMap {f : M → N}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (A : GermIdeal n M) (B : GermIdeal m N) (hB : B.IsCoherent)
    (hAB : GermIdeal.Le (GermIdeal.pullback (m := n) f B) A) :
    (quotientModelSheaf B).presheaf ⟶
      (TopCat.Presheaf.pushforward CommRingCat (quotientTopMap hf A B hB hAB)).obj
        (quotientModelSheaf A).presheaf :=
  sheafifyLift (Opens.grothendieckTopology (TopCat.of B.zeroLocus))
    (modelPresheafMap hf A B hB hAB)
    ((TopCat.Sheaf.pushforward CommRingCat (quotientTopMap hf A B hB hAB)).obj
      (quotientModelSheaf A)).property

private theorem modelSheafMap_unit {f : M → N}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (A : GermIdeal n M) (B : GermIdeal m N) (hB : B.IsCoherent)
    (hAB : GermIdeal.Le (GermIdeal.pullback (m := n) f B) A) :
    quotientModelUnit B ≫ modelSheafMap hf A B hB hAB = modelPresheafMap hf A B hB hAB :=
  toSheafify_sheafifyLift _ _ _

private theorem quotientToModel_map {f : M → N}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (A : GermIdeal n M) (B : GermIdeal m N) (hB : B.IsCoherent)
    (hAB : GermIdeal.Le (GermIdeal.pullback (m := n) f B) A) :
    quotientToModel B ≫
      (TopCat.Presheaf.pushforward CommRingCat (actualSubspaceTopInclusion B.zeroLocus)).map
        (modelSheafMap hf A B hB hAB) =
      rawQuotientPresheafMap hf A B hB hAB ≫
        (TopCat.Presheaf.pushforward CommRingCat (actualAmbientMap hf)).map (quotientToModel A) := by
  change (_ ≫ (TopCat.Presheaf.pushforward CommRingCat (actualSubspaceTopInclusion B.zeroLocus)).map
      (quotientModelUnit B)) ≫ _ = _
  rw [Category.assoc,←Functor.map_comp,modelSheafMap_unit]
  have h := ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat
    (actualSubspaceTopInclusion B.zeroLocus)).homEquiv (quotientPresheaf B)
      ((TopCat.Presheaf.pushforward CommRingCat (quotientTopMap hf A B hB hAB)).obj
        (quotientModelSheaf A).presheaf)).apply_symm_apply
    (rawQuotientPresheafMap hf A B hB hAB ≫
      (TopCat.Presheaf.pushforward CommRingCat (actualAmbientMap hf)).map (quotientToModel A))
  rw [Adjunction.homEquiv_unit] at h
  exact h

private theorem rawQuotientPresheafMap_ambient {f : M → N}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (A : GermIdeal n M) (B : GermIdeal m N) (hB : B.IsCoherent)
    (hAB : GermIdeal.Le (GermIdeal.pullback (m := n) f B) A) :
    quotientAmbientPresheafMap B ≫ rawQuotientPresheafMap hf A B hB hAB =
      (ChartedSpace.locallyRingedSpaceMap f hf).toHom.c ≫
        (TopCat.Presheaf.pushforward CommRingCat (actualAmbientMap hf)).map
          (quotientAmbientPresheafMap A) := by
  ext U s
  rfl

@[implicit_reducible]
private def ringedMap {f : M → N}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (A : GermIdeal n M) (hA : A.IsCoherent) (B : GermIdeal m N) (hB : B.IsCoherent)
    (hAB : GermIdeal.Le (GermIdeal.pullback (m := n) f B) A) :
    (quotientLocallyRingedSpace A hA).toPresheafedSpace ⟶
      (quotientLocallyRingedSpace B hB).toPresheafedSpace where
  base := quotientTopMap hf A B hB hAB
  c := modelSheafMap hf A B hB hAB

private theorem ringedMap_inclusion {f : M → N}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (A : GermIdeal n M) (hA : A.IsCoherent) (B : GermIdeal m N) (hB : B.IsCoherent)
    (hAB : GermIdeal.Le (GermIdeal.pullback (m := n) f B) A) :
    (quotientInclusion A hA).toHom ≫ (ChartedSpace.locallyRingedSpaceMap f hf).toHom =
      ringedMap hf A hA B hB hAB ≫ (quotientInclusion B hB).toHom := by
  refine PresheafedSpace.hext _ _ rfl ?_
  apply heq_of_eq
  change (ChartedSpace.locallyRingedSpaceMap f hf).toHom.c ≫
      (TopCat.Presheaf.pushforward CommRingCat (actualAmbientMap hf)).map
        (quotientAmbientPresheafMap A ≫ quotientToModel A) =
    (quotientAmbientPresheafMap B ≫ quotientToModel B) ≫
      (TopCat.Presheaf.pushforward CommRingCat (actualSubspaceTopInclusion B.zeroLocus)).map
        (modelSheafMap hf A B hB hAB)
  rw [Functor.map_comp,←Category.assoc,←rawQuotientPresheafMap_ambient hf A B hB hAB,
    Category.assoc,←quotientToModel_map hf A B hB hAB,←Category.assoc]

private theorem inclusion_base_apply (A : GermIdeal n M) (hA : A.IsCoherent) (x : A.zeroLocus) :
    (quotientInclusion A hA).toHom.base x = x.val := rfl

private theorem ringedMap_base_apply {f : M → N}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (A : GermIdeal n M) (hA : A.IsCoherent) (B : GermIdeal m N) (hB : B.IsCoherent)
    (hAB : GermIdeal.Le (GermIdeal.pullback (m := n) f B) A) (x : A.zeroLocus) :
    (ringedMap hf A hA B hB hAB).base x = quotientTopMap hf A B hB hAB x := rfl

omit [IsComplexManifold n M] [IsComplexManifold m N] in
private theorem ambient_base_apply {f : M → N}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f) (x : M) :
    (ChartedSpace.locallyRingedSpaceMap f hf).toHom.base x = f x := rfl

set_option backward.isDefEq.respectTransparency.types false in
private theorem ringedMap_stalk_square {f : M → N}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (A : GermIdeal n M) (hA : A.IsCoherent) (B : GermIdeal m N) (hB : B.IsCoherent)
    (hAB : GermIdeal.Le (GermIdeal.pullback (m := n) f B) A) (x : A.zeroLocus) :
    (quotientInclusion B hB).toHom.stalkMap (quotientTopMap hf A B hB hAB x) ≫
      (ringedMap hf A hA B hB hAB).stalkMap x =
    (ChartedSpace.locallyRingedSpaceMap f hf).toHom.stalkMap x.val ≫
      (quotientInclusion A hA).toHom.stalkMap x := by
  have h := PresheafedSpace.stalkMap.congr_hom
    ((quotientInclusion A hA).toHom ≫ (ChartedSpace.locallyRingedSpaceMap f hf).toHom)
    (ringedMap hf A hA B hB hAB ≫ (quotientInclusion B hB).toHom)
    (ringedMap_inclusion hf A hA B hB hAB) x
  simpa only [PresheafedSpace.stalkMap.comp,PresheafedSpace.comp_base,TopCat.comp_app,
    inclusion_base_apply,ringedMap_base_apply,ambient_base_apply,
    eqToHom_refl,Category.id_comp] using h.symm

private theorem ringedMap_stalk_isLocalHom {f : M → N}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (A : GermIdeal n M) (hA : A.IsCoherent) (B : GermIdeal m N) (hB : B.IsCoherent)
    (hAB : GermIdeal.Le (GermIdeal.pullback (m := n) f B) A) (x : A.zeroLocus) :
    IsLocalHom ((ringedMap hf A hA B hB hAB).stalkMap x).hom := by
  refine ⟨?_⟩
  intro z hz
  obtain ⟨r,rfl⟩ := quotientInclusion_surjective_stalk B hB (quotientTopMap hf A B hB hAB x) z
  have h := ConcreteCategory.congr_hom (ringedMap_stalk_square hf A hA B hB hAB x) r
  simp only [ConcreteCategory.comp_apply] at h
  let k := ((quotientInclusion A hA).stalkMap x).hom.comp
    ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap x.val).hom
  let : IsLocalHom k := by
    dsimp only [k]
    infer_instance
  have hk : IsUnit (k r) := h ▸ hz
  have hr := isUnit_of_map_unit k r hk
  exact ((quotientInclusion B hB).stalkMap (quotientTopMap hf A B hB hAB x)).hom.isUnit_map hr

/-- The actual original map and WHOLE pulled-ideal inclusion construct the entire native quotient morphism. -/
@[implicit_reducible]
def quotientMap {f : M → N}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (A : GermIdeal n M) (hA : A.IsCoherent) (B : GermIdeal m N) (hB : B.IsCoherent)
    (hAB : GermIdeal.Le (GermIdeal.pullback (m := n) f B) A) :
    quotientLocallyRingedSpace A hA ⟶ quotientLocallyRingedSpace B hB where
  toHom := ringedMap hf A hA B hB hAB
  prop := ringedMap_stalk_isLocalHom hf A hA B hB hAB

/-- FULL ambient square of native LRS morphisms, including their entire structure-sheaf maps. -/
theorem quotientMap_inclusion {f : M → N}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (A : GermIdeal n M) (hA : A.IsCoherent) (B : GermIdeal m N) (hB : B.IsCoherent)
    (hAB : GermIdeal.Le (GermIdeal.pullback (m := n) f B) A) :
    quotientInclusion A hA ≫ ChartedSpace.locallyRingedSpaceMap f hf =
      quotientMap hf A hA B hB hAB ≫ quotientInclusion B hB := by
  apply LocallyRingedSpace.Hom.ext'
  exact ringedMap_inclusion hf A hA B hB hAB

/-- EVERY original quotient-section numerator maps to its literal original holomorphic pullback. -/
theorem quotientMap_section_mk {f : M → N}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (A : GermIdeal n M) (hA : A.IsCoherent) (B : GermIdeal m N) (hB : B.IsCoherent)
    (hAB : GermIdeal.Le (GermIdeal.pullback (m := n) f B) A)
    (U : Opens N) (s : actualComplexSection (n := m) U) :
    (quotientMap hf A hA B hB hAB).toHom.c.app
      (op ((Opens.map (actualSubspaceTopInclusion B.zeroLocus)).obj U))
        (quotientSectionMap B U (Ideal.Quotient.mk (actualSectionIdeal B U) s)) =
      quotientSectionMap A ((Opens.map (actualAmbientMap hf)).obj U)
        (Ideal.Quotient.mk (actualSectionIdeal A ((Opens.map (actualAmbientMap hf)).obj U))
          ((ChartedSpace.locallyRingedSpaceMap f hf).toHom.c.app (op U) s)) := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun k => k.app (op U)) (quotientToModel_map hf A B hB hAB))
    (Ideal.Quotient.mk (actualRemainderSectionIdeal B univ 1 U) s)
  exact h

/-- EVERY whole quotient-stalk numerator has the genuine original ambient pullback formula. -/
theorem quotientMap_stalk_mk {f : M → N}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (A : GermIdeal n M) (hA : A.IsCoherent) (B : GermIdeal m N) (hB : B.IsCoherent)
    (hAB : GermIdeal.Le (GermIdeal.pullback (m := n) f B) A) (x : A.zeroLocus)
    (r : actualComplexStructureStalk (n := m) (f x.val)) :
    quotientStalkWholeEquiv A hA x ((quotientMap hf A hA B hB hAB).stalkMap x
      ((quotientStalkWholeEquiv B hB (quotientTopMap hf A B hB hAB x)).symm
        (Ideal.Quotient.mk (actualWholeSheafStalkIdeal B (f x.val)) r))) =
      Ideal.Quotient.mk (actualWholeSheafStalkIdeal A x.val)
        ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap x.val r) := by
  have hn : (quotientStalkWholeEquiv B hB (quotientTopMap hf A B hB hAB x)).symm
      (Ideal.Quotient.mk (actualWholeSheafStalkIdeal B (f x.val)) r) =
        (quotientInclusion B hB).stalkMap (quotientTopMap hf A B hB hAB x) r := by
    apply (quotientStalkWholeEquiv B hB (quotientTopMap hf A B hB hAB x)).injective
    rw [RingEquiv.apply_symm_apply,quotientInclusion_stalk]
    rfl
  rw [hn]
  have h := ConcreteCategory.congr_hom (ringedMap_stalk_square hf A hA B hB hAB x) r
  simp only [ConcreteCategory.comp_apply] at h
  exact (congrArg (quotientStalkWholeEquiv A hA x) h).trans
    (quotientInclusion_stalk A hA x ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap x.val r))

/-- Full scalar action over the ACTUAL ambient stalk, via the independently constructed structural maps. -/
theorem quotientMap_stalk_smul {f : M → N}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (A : GermIdeal n M) (hA : A.IsCoherent) (B : GermIdeal m N) (hB : B.IsCoherent)
    (hAB : GermIdeal.Le (GermIdeal.pullback (m := n) f B) A) (x : A.zeroLocus)
    (r : actualComplexStructureStalk (n := m) (f x.val))
    (z : ((quotientLocallyRingedSpace B hB).presheaf.stalk (quotientTopMap hf A B hB hAB x)).carrier) :
    letI : Algebra (actualComplexStructureStalk (n := m) (f x.val))
      ((quotientLocallyRingedSpace B hB).presheaf.stalk (quotientTopMap hf A B hB hAB x)).carrier :=
        ((quotientInclusion B hB).stalkMap (quotientTopMap hf A B hB hAB x)).hom.toAlgebra
    letI : Algebra (actualComplexStructureStalk (n := m) (f x.val))
      ((quotientLocallyRingedSpace A hA).presheaf.stalk x).carrier :=
        (((quotientInclusion A hA).stalkMap x).hom.comp
          ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap x.val).hom).toAlgebra
    (quotientMap hf A hA B hB hAB).stalkMap x (r • z) =
      r • (quotientMap hf A hA B hB hAB).stalkMap x z := by
  change (quotientMap hf A hA B hB hAB).stalkMap x
      ((quotientInclusion B hB).stalkMap (quotientTopMap hf A B hB hAB x) r*z) =
    (quotientInclusion A hA).stalkMap x
      ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap x.val r) *
        (quotientMap hf A hA B hB hAB).stalkMap x z
  rw [map_mul]
  have h := ConcreteCategory.congr_hom (ringedMap_stalk_square hf A hA B hB hAB x) r
  simp only [ConcreteCategory.comp_apply] at h
  exact congrArg (fun q => q * (quotientMap hf A hA B hB hAB).stalkMap x z) h

/-- Uniqueness among ALL native LRS morphisms satisfying the full original ambient square. -/
theorem quotientMap_unique {f : M → N}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (A : GermIdeal n M) (hA : A.IsCoherent) (B : GermIdeal m N) (hB : B.IsCoherent)
    (hAB : GermIdeal.Le (GermIdeal.pullback (m := n) f B) A)
    (g : quotientLocallyRingedSpace A hA ⟶ quotientLocallyRingedSpace B hB)
    (hg : g ≫ quotientInclusion B hB = quotientInclusion A hA ≫ ChartedSpace.locallyRingedSpaceMap f hf) :
    g = quotientMap hf A hA B hB hAB :=
  (cancel_mono (quotientInclusion B hB)).mp (hg.trans (quotientMap_inclusion hf A hA B hB hAB))

end
end Hironaka.HironakaNonreducedAnalyticQuotientMorphism
