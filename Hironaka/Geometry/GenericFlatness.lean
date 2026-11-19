import Hironaka.Geometry.AffineGenericFlatness
import Hironaka.Geometry.IntegralOpen
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Generic flatness on schemes

Actual open restrictions and source-cover gluing for the generic-flatness
input of de Jong 1996, 2.7(a).
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u v

namespace Hironaka.Geometry.GenericFlatness

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{u}}

/-- Flatness over a target open persists under shrinking that open. -/
theorem flat_morphismRestrict_of_le (f : X ⟶ Y) {U V : Y.Opens}
    (h : U ≤ V) (hf : Flat (f ∣_ V)) : Flat (f ∣_ U) := by
  have outer : IsPullback (f ∣_ U)
      (X.homOfLE (f.preimage_mono h) ≫ (f ⁻¹ᵁ V).ι)
      (Y.homOfLE h ≫ V.ι) f := by
    simpa only [Scheme.homOfLE_ι] using isPullback_morphismRestrict f U
  exact IsZariskiLocalAtTarget.of_isPullback
    (outer.of_bot (morphismRestrict_homOfLE f U V h)
      (isPullback_morphismRestrict f V)).flip hf

/-- Flat restrictions of all members of a source cover glue to the original restriction. -/
theorem flat_morphismRestrict_of_openCover (f : X ⟶ Y)
    (𝒰 : X.OpenCover.{v}) (U : Y.Opens)
    (hf : ∀ i, Flat ((𝒰.f i ≫ f) ∣_ U)) : Flat (f ∣_ U) := by
  apply IsZariskiLocalAtSource.of_openCover (𝒰.restrict (f ⁻¹ᵁ U))
  intro i
  change Flat (𝒰.f i ∣_ f ⁻¹ᵁ U ≫ f ∣_ U)
  rw [← morphismRestrict_comp]
  exact hf i

/-- A finite source cover admits a common nonempty flat target open over an irreducible base. -/
theorem exists_nonempty_flat_of_finite_openCover (f : X ⟶ Y) [IrreducibleSpace Y]
    (𝒰 : X.OpenCover.{v}) [Finite 𝒰.I₀]
    (hf : ∀ i, ∃ U : Y.Opens, Nonempty U ∧ Flat ((𝒰.f i ≫ f) ∣_ U)) :
    ∃ U : Y.Opens, Nonempty U ∧ Flat (f ∣_ U) := by
  classical
  choose U hU hflat using hf
  let V : Y.Opens := ⨅ i, U i
  have hη : genericPoint Y ∈ V := by
    change genericPoint Y ∈ ((⨅ i, U i : Y.Opens) : Set Y)
    rw [Opens.coe_iInf, Set.mem_iInter]
    intro i
    exact ((genericPoint_spec Y).mem_open_set_iff (U i).isOpen).mpr
      (by simpa using hU i)
  refine ⟨V, ⟨⟨genericPoint Y, hη⟩⟩, ?_⟩
  apply flat_morphismRestrict_of_openCover f 𝒰 V
  intro i
  exact flat_morphismRestrict_of_le (𝒰.f i ≫ f) (iInf_le U i) (hflat i)

/-- Generic flatness over an affine integral base, with quasi-compact source. -/
theorem exists_nonempty_flat_of_isAffine_target (f : X ⟶ Y)
    [IsAffine Y] [IsIntegral Y] [CompactSpace X] [LocallyOfFiniteType f] :
    ∃ U : Y.Opens, Nonempty U ∧ Flat (f ∣_ U) := by
  let 𝒰 := X.affineCover.finiteSubcover
  have (i : 𝒰.I₀) : IsAffine (𝒰.X i) := by
    dsimp [𝒰, Scheme.OpenCover.finiteSubcover]
    infer_instance
  apply exists_nonempty_flat_of_finite_openCover f 𝒰
  intro i
  exact AffineGenericFlatness.exists_nonempty_flat_morphismRestrict (𝒰.f i ≫ f)

/-- A finite-type morphism over any integral scheme is flat over a nonempty target open. -/
theorem exists_nonempty_flat_of_isIntegral (f : X ⟶ Y)
    [IsIntegral Y] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ U : Y.Opens, Nonempty U ∧ Flat (f ∣_ U) := by
  obtain ⟨V, hV, hη, _⟩ := exists_isAffineOpen_mem_and_subset
    (x := genericPoint Y) (U := (⊤ : Y.Opens)) (by trivial)
  let : Nonempty V := ⟨⟨genericPoint Y, hη⟩⟩
  let : IsAffine V.toScheme := hV
  let : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  let : CompactSpace (f ⁻¹ᵁ V).toScheme :=
    QuasiCompact.compactSpace_of_compactSpace (f ∣_ V)
  obtain ⟨W, hW, hflat⟩ := exists_nonempty_flat_of_isAffine_target (f ∣_ V)
  refine ⟨V.ι ''ᵁ W, hW.map (V.ι.isoImage W).hom, ?_⟩
  exact (MorphismProperty.arrow_mk_iso_iff @Flat (morphismRestrictRestrict f V W)).mp hflat

/-- Flatness over an irreducible base holds over a dense open once a nonempty flat open exists. -/
theorem exists_dense_flat_of_isIntegral (f : X ⟶ Y)
    [IsIntegral Y] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ U : Y.Opens, Dense (U : Set Y) ∧ Flat (f ∣_ U) := by
  obtain ⟨U, hU, hflat⟩ := exists_nonempty_flat_of_isIntegral f
  exact ⟨U, U.isOpen.dense (by simpa using hU), hflat⟩

/-- Flatness over target opens glues over their union. -/
theorem flat_morphismRestrict_iSup (f : X ⟶ Y) {ι : Type v} (U : ι → Y.Opens)
    (hf : ∀ i, Flat (f ∣_ U i)) : Flat (f ∣_ ⨆ i, U i) := by
  let V : Y.Opens := ⨆ i, U i
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (fun i => V.ι ⁻¹ᵁ U i)
  · rw [← Scheme.Hom.preimage_iSup]
    exact V.ι_preimage_self
  · intro i
    have himage : V.ι ''ᵁ (V.ι ⁻¹ᵁ U i) = U i := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact inf_eq_right.mpr (le_iSup U i)
    have hflat : Flat (f ∣_ V.ι ''ᵁ (V.ι ⁻¹ᵁ U i)) := by
      rw [himage]
      exact hf i
    exact (MorphismProperty.arrow_mk_iso_iff @Flat
      (morphismRestrictRestrict f V (V.ι ⁻¹ᵁ U i))).mpr hflat

/-- De Jong 2.7(a): a finite-type morphism to a reduced Noetherian base is generically flat.
Only topological Noetherianity is required in addition to reducedness. -/
theorem exists_dense_flat_of_isReduced (f : X ⟶ Y)
    [NoetherianSpace Y] [IsReduced Y] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ U : Y.Opens, Dense (U : Set Y) ∧ Flat (f ∣_ U) := by
  let I := {W : Y.Opens // Flat (f ∣_ W)}
  let U : Y.Opens := ⨆ W : I, W.val
  refine ⟨U, ?_, flat_morphismRestrict_iSup f _ (fun W : I => W.property)⟩
  rw [dense_iff_inter_open]
  intro V hVo hVn
  obtain ⟨W, hWV, hWn, hWi⟩ :=
    IntegralOpen.exists_nonempty_integral_open_le Y ⟨V, hVo⟩ hVn.to_subtype
  let : IsIntegral W.toScheme := hWi
  obtain ⟨T, hT, hflat⟩ := exists_nonempty_flat_of_isIntegral (f ∣_ W)
  let Z : Y.Opens := W.ι ''ᵁ T
  have hZflat : Flat (f ∣_ Z) :=
    (MorphismProperty.arrow_mk_iso_iff @Flat (morphismRestrictRestrict f W T)).mp hflat
  let z : I := ⟨Z, hZflat⟩
  have hZU : Z ≤ U := le_iSup (fun W : I => W.val) z
  obtain ⟨t⟩ := hT
  exact ⟨W.ι t.val, hWV t.val.property, hZU ⟨t.val, t.property, rfl⟩⟩

end Hironaka.Geometry.GenericFlatness
