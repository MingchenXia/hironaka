import DeJongAlterations.Composition
import Mathlib.AlgebraicGeometry.Birational.Birational

/-!
# Modifications

The proper birational morphism condition of de Jong 2.17, with native dense-open
partial isomorphisms. Noetherianity is not needed for the calculus proved here.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations

universe u

variable {S T X Y Z : Scheme.{u}}

/-- A partial isomorphism over S is also over any base receiving a map from S. -/
theorem birationalOver_postcomp {sX : X ⟶ S} {sY : Y ⟶ S}
    (h : Scheme.BirationalOver sX sY) (g : S ⟶ T) :
    Scheme.BirationalOver (sX ≫ g) (sY ≫ g) := by
  obtain ⟨e, he⟩ := h
  refine ⟨e, ?_⟩
  simpa only [Scheme.PartialIso.IsOver, Category.assoc] using
    congrArg (fun m => m ≫ g) he

/-- Actual birational morphisms compose through native partial isomorphisms. -/
theorem birationalOver_id_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Scheme.BirationalOver f (𝟙 Y))
    (hg : Scheme.BirationalOver g (𝟙 Z)) :
    Scheme.BirationalOver (f ≫ g) (𝟙 Z) := by
  have h : Scheme.BirationalOver (f ≫ g) g := by
    simpa only [Category.id_comp] using birationalOver_postcomp hf g
  exact h.trans hg

/-- A modification in the sense of de Jong 2.17; the morphism condition also
makes sense without the source's Noetherian-base convention. -/
class IsModification (f : X ⟶ Y) : Prop extends IsProper f where
  sourceIntegral : IsIntegral X
  targetIntegral : IsIntegral Y
  birational : Scheme.BirationalOver f (𝟙 Y)

/-- The actual dense target open of a birational morphism lies in its image. -/
theorem isDominant_of_birationalOver_id (f : X ⟶ Y)
    (hf : Scheme.BirationalOver f (𝟙 Y)) : IsDominant f := by
  obtain ⟨e, he⟩ := hf
  have heq : e.iso.hom ≫ e.target.ι = e.source.ι ≫ f := by
    simpa only [Scheme.PartialIso.IsOver, Category.comp_id] using he
  refine ⟨e.dense_target.mono ?_⟩
  intro y hy
  obtain ⟨x, hx⟩ := e.iso.hom.surjective ⟨y, hy⟩
  refine ⟨e.source.ι x, ?_⟩
  have h := congrArg (fun m : e.source.toScheme ⟶ Y => m x) heq
  simpa only [Scheme.Hom.comp_apply, hx, Scheme.Opens.ι_apply] using h.symm

/-- A native birational morphism is etale on its actual dense source isomorphism open. -/
theorem isGenericallyEtale_of_birationalOver_id (f : X ⟶ Y)
    (hf : Scheme.BirationalOver f (𝟙 Y)) : IsGenericallyEtale f := by
  obtain ⟨e, he⟩ := hf
  have heq : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι := by
    exact (show e.iso.hom ≫ e.target.ι = e.source.ι ≫ f by
      simpa only [Scheme.PartialIso.IsOver, Category.comp_id] using he).symm
  refine ⟨e.source, e.dense_source, ?_⟩
  rw [heq]
  infer_instance

/-- Birationality gives quasi-finiteness at the actual generic point. -/
theorem quasiFiniteAt_genericPoint_of_birationalOver_id (f : X ⟶ Y)
    [IsIntegral X] (hf : Scheme.BirationalOver f (𝟙 Y)) :
    f.QuasiFiniteAt (genericPoint X) := by
  obtain ⟨e, he⟩ := hf
  let : Nonempty e.source := Set.nonempty_coe_sort.mpr e.dense_source.nonempty
  have heq : e.iso.hom ≫ e.target.ι = e.source.ι ≫ f := by
    simpa only [Scheme.PartialIso.IsOver, Category.comp_id] using he
  have : IsOpenImmersion (e.source.ι ≫ f) := by
    rw [← heq]
    infer_instance
  have hq := (e.source.ι ≫ f).quasiFiniteAt (genericPoint e.source.toScheme)
  have hq' := (Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion
    (f := e.source.ι) (g := f)).mp hq
  have hη : e.source.ι (genericPoint e.source.toScheme) = genericPoint X :=
    genericPoint_eq_of_isOpenImmersion e.source.ι
  rw [hη] at hq'
  exact hq'

instance isModification_id (X : Scheme.{u}) [IsIntegral X] :
    IsModification (𝟙 X) where
  sourceIntegral := inferInstance
  targetIntegral := inferInstance
  birational := Scheme.BirationalOver.refl _

instance IsModification.isDominant (f : X ⟶ Y) [hf : IsModification f] :
    IsDominant f := isDominant_of_birationalOver_id f hf.birational

/-- Modifications preserve the generically etale refinement without a field hypothesis. -/
theorem IsModification.isGenericallyEtale (f : X ⟶ Y) [hf : IsModification f] :
    IsGenericallyEtale f := isGenericallyEtale_of_birationalOver_id f hf.birational

/-- Modifications compose, as asserted in de Jong 2.17. -/
theorem IsModification.comp (f : X ⟶ Y) (g : Y ⟶ Z)
    [hf : IsModification f] [hg : IsModification g] : IsModification (f ≫ g) where
  sourceIntegral := hf.sourceIntegral
  targetIntegral := hg.targetIntegral
  birational := birationalOver_id_comp f g hf.birational hg.birational

/-- A modification is genuinely finite over a nonempty target open and thus an alteration. -/
instance IsModification.toIsAlteration (f : X ⟶ Y) [hf : IsModification f] :
    IsAlteration f := by
  let := hf.sourceIntegral
  exact {
    sourceIntegral := hf.sourceIntegral
    targetIntegral := hf.targetIntegral
    genericallyFinite := isGenericallyFinite_of_quasiFiniteAt_genericPoint f
      (quasiFiniteAt_genericPoint_of_birationalOver_id f hf.birational) }

end DeJongAlterations
