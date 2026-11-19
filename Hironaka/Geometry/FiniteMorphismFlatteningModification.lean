import Hironaka.Geometry.FiniteMorphismFlatteningModificationOpen
import Hironaka.Geometry.FiniteMorphismFlatteningCenter

/-!
# The literal finite flattening transform modifies the original integral source

The original coefficient injectivity and actual nonzero blowup ideal internally
produce the dense common open. Properness, integrality and the native partial
isomorphism are proved for the same closed generic-fibre image, not a substitute.
This completes this birational comparison in the finite case of source 2.18--2.19.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hironaka.Geometry.FiniteMorphismFlattening

open Algebra.ModuleFlatteningMinors

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R A : Type u) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Algebra R A]

/-- The literal strict-transform projection is birational over the original affine source.
Its native partial isomorphism is constructed on an actual nonzero coefficient open. -/
theorem globalTransformToOriginal_birationalOver
    (hinj : Function.Injective (algebraMap R A)) (I : Ideal R) (hI : I ≠ ⊥) :
    Scheme.BirationalOver (globalTransformToOriginal R A I) (𝟙 (Spec (.of A))) := by
  let : IsIntegral (globalTransform R A I) := globalTransform_isIntegral R A I hinj hI
  obtain ⟨g, hg, hg0⟩ : ∃ g ∈ I, g ≠ 0 := by
    by_contra! hzero
    apply hI
    apply le_antisymm ?_ bot_le
    intro a ha
    change a = 0
    exact hzero a ha
  let U : (Spec (.of A)).Opens := PrimeSpectrum.basicOpen (algebraMap R A g)
  let : IsIso (globalTransformToOriginal R A I ∣_ U) :=
    globalTransformToOriginal_restrict_isIso R A hinj I g hg hg0
  have hU : (U : Set (Spec (.of A))).Nonempty := by
    refine ⟨(⊥ : PrimeSpectrum A), ?_⟩
    change algebraMap R A g ≠ 0
    exact fun h => hg0 (hinj (by simpa using h))
  have hη : genericPoint (Spec (.of A)) ∈ U :=
    ((genericPoint_spec (Spec (.of A))).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  have hrange : genericPoint (Spec (.of A)) ∈ Set.range (globalTransformToOriginal R A I) := by
    obtain ⟨x, hx⟩ := (globalTransformToOriginal R A I ∣_ U).surjective ⟨_, hη⟩
    refine ⟨x.val, ?_⟩
    have h := congrArg Subtype.val hx
    simpa only [morphismRestrict_base_coe] using h
  let : IsDominant (globalTransformToOriginal R A I) := by
    refine ⟨?_⟩
    rw [denseRange_iff_closure_range]
    apply Set.Subset.antisymm (Set.subset_univ _)
    rw [← (genericPoint_spec (Spec (.of A))).def]
    exact closure_mono (Set.singleton_subset_iff.mpr hrange)
  exact birationalOver_id_of_isIso_morphismRestrict _ U hU

/-- The SAME actual generic-fibre closure is a native modification of the original source.
Only coefficient injectivity, domains, and a nonzero finitely generated center are required;
the original algebra need not be finite. -/
theorem globalTransformToOriginal_isModification
    (hinj : Function.Injective (algebraMap R A)) (I : Ideal R) (hI : I ≠ ⊥) (hfg : I.FG) :
    IsModification (globalTransformToOriginal R A I) := by
  let : IsProper (globalTransformToOriginal R A I) := globalTransformToOriginal_isProper R A I hfg
  exact {
    sourceIntegral := globalTransform_isIntegral R A I hinj hI
    targetIntegral := inferInstance
    birational := globalTransformToOriginal_birationalOver R A hinj I hI }

/-- Finite-case flattening with the prescribed original flat open and BOTH actual modification
maps: the base blowup and the same native finite flat transform's map to the original source. -/
theorem exists_finite_flat_modification_preserving_open [IsNoetherianRing R] [Module.Finite R A]
    (hinj : Function.Injective (algebraMap R A))
    (U : (Spec (.of R)).Opens) (hflat : Flat (originalMap R A ∣_ U)) :
    ∃ (n r : ℕ) (m : Fin n → A) (V : Matrix (Fin r) (Fin n) R),
      Submodule.span R (Set.range m) = ⊤ ∧ (minorIdeal V).FG ∧ minorIdeal V ≠ ⊥ ∧
      IsProjectiveOver (affineBlowupStructure (minorIdeal V)) ∧
      IsModification (affineBlowupStructure (minorIdeal V)) ∧
      IsFinite (globalTransformMap R A (minorIdeal V)) ∧
      Flat (globalTransformMap R A (minorIdeal V)) ∧
      IsIso (affineBlowupStructure (minorIdeal V) ∣_ U) ∧
      ModificationCenter.center (affineBlowupStructure (minorIdeal V)) ≤ U.compl ∧
      IsModification (globalTransformToOriginal R A (minorIdeal V)) := by
  obtain ⟨n, r, m, V, hm, hfg, hI, hp, hb, hf, hflat', hi, hc⟩ :=
    FiniteMorphismFlatteningCenter.exists_finite_flat_transform_preserving_open R A U hflat
  exact ⟨n, r, m, V, hm, hfg, hI, hp, hb, hf, hflat', hi, hc,
    globalTransformToOriginal_isModification R A hinj (minorIdeal V) hI hfg⟩

end Hironaka.Geometry.FiniteMorphismFlattening
