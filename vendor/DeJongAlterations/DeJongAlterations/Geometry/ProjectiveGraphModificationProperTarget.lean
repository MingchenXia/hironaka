import DeJongAlterations.Geometry.ProjectiveGraphModification

/-!
# Actual graph modifications for proper targets

The actual schematic closure of the graph of a proper-target-valued map on
an open subscheme. Its proper projection and internally constructed native
partial isomorphism give a genuine modification. This is one indeterminacy
elimination producer toward source 4.6, not a quasi-projectivity or Chow theorem.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

namespace DeJongAlterations.Geometry.ProjectiveGraphModification.ProperTarget

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S C X : Scheme.{u}}
    (p : X ⟶ S) (q : C ⟶ S) (U : X.Opens)
    (f : U.toScheme ⟶ C) (hf : f ≫ q = U.ι ≫ p)

/-- The actual graph of the given map on the actual open subscheme. -/
def graph : U.toScheme ⟶ pullback p q :=
  pullback.lift U.ι f hf.symm

@[reassoc (attr := simp)]
theorem graph_fst : graph p q U f hf ≫ pullback.fst _ _ = U.ι := by
  simp [graph]

@[reassoc (attr := simp)]
theorem graph_snd : graph p q U f hf ≫ pullback.snd _ _ = f := by
  simp [graph]

instance graph_isImmersion : IsImmersion (graph p q U f hf) := by
  have : IsImmersion (graph p q U f hf ≫ pullback.fst _ _) := by
    rw [graph_fst]
    infer_instance
  exact IsImmersion.of_comp _ (pullback.fst _ _)

instance graph_isQuasiCompact [IsProper q] [QuasiCompact U.ι] : QuasiCompact (graph p q U f hf) := by
  have : QuasiCompact (graph p q U f hf ≫ pullback.fst _ _) := by
    rw [graph_fst]
    infer_instance
  exact QuasiCompact.of_comp _ (pullback.fst _ _)

/-- The actual kernel closed subscheme of the graph in the native product. -/
def modification : Scheme.{u} := (graph p q U f hf).image

/-- The native factorization of the original open into its graph closure. -/
def inclusion : U.toScheme ⟶ modification p q U f hf := (graph p q U f hf).toImage

/-- The actual kernel closed immersion of the graph closure into the product. -/
def embedding : modification p q U f hf ⟶ pullback p q :=
  (graph p q U f hf).imageι

/-- The actual modification projection to the original scheme. -/
def projection : modification p q U f hf ⟶ X :=
  embedding p q U f hf ≫ pullback.fst _ _

/-- The actual everywhere-defined extension of the original proper-target-valued map. -/
def projectiveMap : modification p q U f hf ⟶ C :=
  embedding p q U f hf ≫ pullback.snd _ _

instance embedding_isClosedImmersion : IsClosedImmersion (embedding p q U f hf) := by
  unfold embedding
  infer_instance

instance projection_isProper [IsProper q] : IsProper (projection p q U f hf) := by
  unfold projection
  infer_instance

instance inclusion_isOpenImmersion [IsProper q] [QuasiCompact U.ι] :
    IsOpenImmersion (inclusion p q U f hf) := by
  unfold inclusion
  infer_instance

instance inclusion_isDominant [IsProper q] [QuasiCompact U.ι] :
    IsDominant (inclusion p q U f hf) := by
  unfold inclusion
  infer_instance

@[reassoc (attr := simp)]
theorem inclusion_embedding :
    inclusion p q U f hf ≫ embedding p q U f hf = graph p q U f hf :=
  (graph p q U f hf).toImage_imageι

@[reassoc (attr := simp)]
theorem inclusion_projection : inclusion p q U f hf ≫ projection p q U f hf = U.ι := by
  rw [projection, inclusion_embedding_assoc, graph_fst]

@[reassoc (attr := simp)]
theorem inclusion_projectiveMap : inclusion p q U f hf ≫ projectiveMap p q U f hf = f := by
  rw [projectiveMap, inclusion_embedding_assoc, graph_snd]

/-- The original coefficient structure is preserved by the actual extension. -/
@[reassoc]
theorem structure_triangle :
    projectiveMap p q U f hf ≫ q =
      projection p q U f hf ≫ p := by
  unfold projectiveMap projection
  rw [Category.assoc, Category.assoc, pullback.condition]

instance modification_isIntegral [IsProper q] [QuasiCompact U.ι] [IsIntegral X] [Nonempty U] :
    IsIntegral (modification p q U f hf) :=
  ProjectiveCompactification.image_isIntegral (graph p q U f hf)

/-- The actual common open, not a supplied birationality certificate. -/
def partialIso [IsProper q] [QuasiCompact U.ι] [IsIntegral X] [Nonempty U] :
    (modification p q U f hf).PartialIso X where
  source := (inclusion p q U f hf).opensRange
  dense_source := (inclusion p q U f hf).denseRange
  target := U
  dense_target := U.isOpen.dense (by
    obtain ⟨x⟩ := (inferInstance : Nonempty U)
    exact ⟨U.ι x, x.2⟩)
  iso := (inclusion p q U f hf).isoOpensRange.symm

/-- The native partial isomorphism is literally compatible with the original base. -/
theorem partialIso_isOver [IsProper q] [QuasiCompact U.ι] [IsIntegral X] [Nonempty U] :
    (partialIso p q U f hf).IsOver (projection p q U f hf) (𝟙 X) := by
  change (inclusion p q U f hf).isoOpensRange.inv ≫ U.ι ≫ 𝟙 X =
    (inclusion p q U f hf).opensRange.ι ≫ projection p q U f hf
  rw [Category.comp_id, ← inclusion_projection p q U f hf, ← Category.assoc,
    Scheme.Hom.isoOpensRange_inv_comp]

/-- Native birationality is produced from the two actual dense open immersions. -/
theorem projection_birationalOver [IsProper q] [QuasiCompact U.ι] [IsIntegral X] [Nonempty U] :
    Scheme.BirationalOver (projection p q U f hf) (𝟙 X) :=
  ⟨partialIso p q U f hf, partialIso_isOver p q U f hf⟩

instance projection_isModification [IsProper q] [QuasiCompact U.ι] [IsIntegral X] [Nonempty U] :
    IsModification (projection p q U f hf) where
  sourceIntegral := inferInstance
  targetIntegral := inferInstance
  birational := projection_birationalOver p q U f hf

/-- The full inverse image of the original open has no extra points or scheme structure. -/
theorem projection_restrict_isIso [IsProper q] [QuasiCompact U.ι] [IsIntegral X] [Nonempty U] :
    IsIso (projection p q U f hf ∣_ U) :=
  ModificationCenter.isIso_restrict_partialIso_target (projection p q U f hf)
    (partialIso p q U f hf) (partialIso_isOver p q U f hf)

include hf

/-- Actual graph modification for any proper target, including native finite products of projective closures. -/
theorem exists_graph_modification [IsProper q] [QuasiCompact U.ι] [IsIntegral X] [Nonempty U] :
    ∃ (Y : Scheme.{u}) (π : Y ⟶ X) (F : Y ⟶ C) (j : U.toScheme ⟶ Y),
      IsModification π ∧ IsOpenImmersion j ∧ IsDominant j ∧
        j ≫ π = U.ι ∧ j ≫ F = f ∧ F ≫ q = π ≫ p ∧ IsIso (π ∣_ U) :=
  ⟨modification p q U f hf, projection p q U f hf, projectiveMap p q U f hf,
    inclusion p q U f hf, inferInstance, inferInstance, inferInstance,
    inclusion_projection p q U f hf, inclusion_projectiveMap p q U f hf,
    structure_triangle p q U f hf, projection_restrict_isIso p q U f hf⟩

end DeJongAlterations.Geometry.ProjectiveGraphModification.ProperTarget
