import Hironaka.Geometry.FiniteMorphismFlatteningModificationGeneric
import Hironaka.Geometry.ModificationCenterBaseChange

/-!
# The same schematic transform over the original isomorphism open

The generic-fibre image has zero kernel on every integral open whose generic
point lies over the original generic point. Applied over a nonzero blowup
coefficient, this proves an isomorphism for the literal transform projection.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hironaka.Geometry.FiniteMorphismFlattening

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual generic-fibre image is the entire integral open when that open's
actual generic point lies over the original generic point. -/
theorem genericImageInclusion_restrict_isIso {W Y : Scheme.{u}} [IrreducibleSpace Y]
    (f : W ⟶ Y) (V : W.Opens) [IsIntegral V]
    [QuasiCompact (f.fiberι (genericPoint Y))]
    (hη : f (V.ι (genericPoint V.toScheme)) = genericPoint Y) :
    IsIso ((f.fiberι (genericPoint Y)).imageι ∣_ V) := by
  let j := f.fiberι (genericPoint Y)
  let j' := j ∣_ V
  let z : f.fiber (genericPoint Y) := (f.fiberHomeo (genericPoint Y)).symm
    ⟨V.ι (genericPoint V.toScheme), hη⟩
  have hz : j z = V.ι (genericPoint V.toScheme) := f.fiberι_fiberHomeo_symm _ _
  have hzV : z ∈ j ⁻¹ᵁ V := by
    change j z ∈ V
    rw [hz]
    exact (genericPoint V.toScheme).property
  have hrange : genericPoint V.toScheme ∈ Set.range j' := by
    refine ⟨⟨z, hzV⟩, ?_⟩
    apply Subtype.ext
    rw [morphismRestrict_base_coe]
    exact hz.trans (Scheme.Opens.ι_apply _ _)
  let : IsDominant j' := by
    refine ⟨?_⟩
    rw [denseRange_iff_closure_range]
    apply Set.Subset.antisymm (Set.subset_univ _)
    rw [← (genericPoint_spec V.toScheme).def]
    exact closure_mono (Set.singleton_subset_iff.mpr hrange)
  let : IsSchemeTheoreticallyDominant j' := .of_isDominant j'
  let : IsIso j'.imageι := (Scheme.isIso_subschemeι_iff_eq_bot _).mpr
    (Scheme.Hom.ker_eq_bot j')
  let H := imageOpenMap_isPullback j j' (j ⁻¹ᵁ V).ι V.ι
    (isPullback_morphismRestrict j V)
  let H' := isPullback_morphismRestrict j.imageι V
  have he : (H'.isoIsPullback _ _ H).hom ≫ j'.imageι = j.imageι ∣_ V :=
    H'.isoIsPullback_hom_fst _ _ H
  rw [← he]
  infer_instance

variable (R A : Type u) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Algebra R A]

omit [IsDomain R] [IsDomain A] in
/-- The original injective coefficient map is dominant on the actual spectra. -/
theorem originalMap_isDominant (hinj : Function.Injective (algebraMap R A)) :
    IsDominant (originalMap R A) := by
  refine ⟨?_⟩
  change DenseRange (PrimeSpectrum.comap (algebraMap R A))
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
  intro a ha
  have ha0 : a = 0 := hinj (by simpa using ha)
  rw [ha0]
  exact Ideal.zero_mem _

/-- The literal strict-transform projection is an actual isomorphism on the original
principal open defined by any nonzero element of the blowup ideal. -/
theorem globalTransformToOriginal_restrict_isIso
    (hinj : Function.Injective (algebraMap R A)) (I : Ideal R)
    (g : R) (hg : g ∈ I) (hg0 : g ≠ 0) :
    IsIso (globalTransformToOriginal R A I ∣_
      PrimeSpectrum.basicOpen (algebraMap R A g)) := by
  let q : baseChanged R A I ⟶ Spec (.of A) := pullback.snd _ _
  let U : (Spec (.of A)).Opens := PrimeSpectrum.basicOpen (algebraMap R A g)
  let V : (baseChanged R A I).Opens := q ⁻¹ᵁ U
  let : IsIso (affineBlowupStructure I ∣_ PrimeSpectrum.basicOpen g) :=
    affineBlowupStructure_restrict_isIso I g hg hg0
  let : IsIso (q ∣_ U) := by
    have H := ModificationCenter.isIso_restrict_of_isPullback
      (IsPullback.of_hasPullback (affineBlowupStructure I) (originalMap R A))
      (PrimeSpectrum.basicOpen g)
    have he : originalMap R A ⁻¹ᵁ PrimeSpectrum.basicOpen g = U := by
      ext x
      rfl
    rw [he] at H
    exact H
  have hU : (U : Set (Spec (.of A))).Nonempty := by
    refine ⟨(⊥ : PrimeSpectrum A), ?_⟩
    change algebraMap R A g ≠ 0
    exact fun h => hg0 (hinj (by simpa using h))
  let : Nonempty U := Set.nonempty_coe_sort.mpr hU
  let : IsIntegral V.toScheme := IsIntegral.of_isIso (inv (q ∣_ U))
  let : IsDominant (originalMap R A) := originalMap_isDominant R A hinj
  have hη : baseChangedToBase R A I (V.ι (genericPoint V.toScheme)) =
      genericPoint (Spec (.of R)) := by
    have hq : q (V.ι (genericPoint V.toScheme)) = genericPoint (Spec (.of A)) := by
      calc
        _ = U.ι ((q ∣_ U) (genericPoint V.toScheme)) := by
          exact congrArg (fun k => k (genericPoint V.toScheme))
            (morphismRestrict_ι q U).symm
        _ = genericPoint (Spec (.of A)) := by
          rw [genericPoint_map_of_isDominant, genericPoint_eq_of_isOpenImmersion]
    have hbase : baseChangedToBase R A I = q ≫ originalMap R A :=
      pullback.condition
    rw [hbase, Scheme.Hom.comp_apply, hq, genericPoint_map_of_isDominant]
  let : IsIso (globalTransformInclusion R A I ∣_ V) :=
    genericImageInclusion_restrict_isIso (baseChangedToBase R A I) V hη
  change IsIso ((globalTransformInclusion R A I ≫ q) ∣_ U)
  rw [morphismRestrict_comp]
  infer_instance

end Hironaka.Geometry.FiniteMorphismFlattening
