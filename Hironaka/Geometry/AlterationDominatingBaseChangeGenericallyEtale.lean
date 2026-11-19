import Hironaka.Geometry.AlterationDominatingBaseChangeProjective
import Hironaka.Geometry.AlterationDominatingBaseChangeEtale
import Hironaka.Geometry.AlterationDominatingBaseChangeComponentEtale

/-!
# Actual generic etaleness of dominating alteration base changes

The actual etale source open of the base alteration pulls back to an
actual reduced Noetherian etale scheme. The genuine component restricted
there has an actual dense etale open. Its actual source-open image gives
generic etaleness of the original component alteration.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Hironaka.Geometry.RelativeChow

noncomputable section

namespace Hironaka.Geometry.AlterationDominatingBaseChange

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y S T : Scheme.{u}}

/-- The actual dominating component of a generically etale alteration
base change is generically etale over a Noetherian integral source.
The etale source open and the component's generic open are both produced. -/
theorem first_isGenericallyEtale
    (f : X ⟶ S) (g : Y ⟶ S) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    [hg : IsAlteration g] (hgEt : IsGenericallyEtale g)
    (j : T ⟶ pullback f g) [IsIntegral T] [IsClosedImmersion j]
    (hj : Set.range j ∈ irreducibleComponents (pullback f g : Scheme.{u}))
    [IsDominant (j ≫ pullback.snd f g)] :
    IsGenericallyEtale (j ≫ pullback.fst f g) := by
  let := hg.sourceIntegral
  let : IsLocallyNoetherian (pullback f g) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f g)
  let : CompactSpace (pullback f g : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst f g)
  let : AlgebraicGeometry.IsNoetherian (pullback f g) := ⟨⟩
  obtain ⟨U, hU, hEt⟩ := hgEt
  let := hEt
  let O := pullback.snd f g ⁻¹ᵁ U
  have H : IsPullback (O.ι ≫ pullback.fst f g) (pullback.snd f g ∣_ U)
      f (U.ι ≫ g) :=
    (isPullback_morphismRestrict (pullback.snd f g) U).flip.paste_horiz
      (IsPullback.of_hasPullback f g)
  let : Etale (O.ι ≫ pullback.fst f g) :=
    MorphismProperty.of_isPullback H.flip inferInstance
  let : IsReduced O.toScheme := isReduced_of_etale (O.ι ≫ pullback.fst f g)
  let : CompactSpace O.toScheme := QuasiCompact.compactSpace_of_compactSpace O.ι
  let : AlgebraicGeometry.IsNoetherian O.toScheme := ⟨⟩
  have hηY : genericPoint Y ∈ U :=
    ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr (by simpa using hU.nonempty)
  have hη : j (genericPoint T) ∈ O := by
    change (j ≫ pullback.snd f g) (genericPoint T) ∈ U
    rw [genericPoint_map_of_isDominant (j ≫ pullback.snd f g)]
    exact hηY
  let : Nonempty (j ⁻¹ᵁ O) := ⟨⟨genericPoint T, hη⟩⟩
  have hc : O.ι ⁻¹' Set.range j ∈ irreducibleComponents O.toScheme :=
    preimage_mem_irreducibleComponents hj O.ι.isOpenEmbedding
      ⟨j (genericPoint T), ⟨genericPoint T, rfl⟩, ⟨⟨j (genericPoint T), hη⟩, rfl⟩⟩
  have hrange : Set.range (j ∣_ O) = O.ι ⁻¹' Set.range j := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, (morphismRestrict_base_coe j O x).symm⟩
    · rintro ⟨x, hx⟩
      refine ⟨⟨x, ?_⟩, ?_⟩
      · change j x ∈ O
        rw [hx]
        exact y.property
      · apply Subtype.ext
        simpa only [morphismRestrict_base_coe, Scheme.Opens.ι_apply] using hx
  have hjEt : IsGenericallyEtale (j ∣_ O) := by
    apply genericallyEtale_component
    rw [hrange]
    exact hc
  have he : IsGenericallyEtale ((j ∣_ O) ≫ (O.ι ≫ pullback.fst f g)) :=
    hjEt.comp (isGenericallyEtale_of_etale (O.ι ≫ pullback.fst f g))
  have he' : IsGenericallyEtale ((j ⁻¹ᵁ O).ι ≫ (j ≫ pullback.fst f g)) := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc] at he
    exact he
  let : IsDominant (j ⁻¹ᵁ O).ι := ⟨by
    change Dense (Set.range (j ⁻¹ᵁ O).ι)
    simpa only [Scheme.Opens.range_ι] using
      (j ⁻¹ᵁ O).isOpen.dense ⟨genericPoint T, hη⟩⟩
  exact genericallyEtale_of_source_open (j ⁻¹ᵁ O).ι (j ≫ pullback.fst f g) he'

/-- An actual dominating generically etale alteration component is
constructed internally over every Noetherian integral original source. -/
theorem exists_genericallyEtale_alteration_component
    (f : X ⟶ S) (g : Y ⟶ S) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    [IsDominant f] [IsAlteration g] (hgEt : IsGenericallyEtale g) :
    ∃ (T : Scheme.{u}) (j : T ⟶ pullback f g),
      IsIntegral T ∧ IsClosedImmersion j ∧
      Set.range j ∈ irreducibleComponents (pullback f g : Scheme.{u}) ∧
      IsAlteration (j ≫ pullback.fst f g) ∧ IsDominant (j ≫ pullback.snd f g) ∧
      IsGenericallyEtale (j ≫ pullback.fst f g) := by
  obtain ⟨T, j, hT, hj, hc, hq, hb⟩ := exists_alteration_component f g
  let := hT
  let := hj
  let := hb
  exact ⟨T, j, hT, hj, hc, hq, hb, first_isGenericallyEtale f g hgEt j hc⟩

/-- The actual component is simultaneously a projective and generically
etale alteration when the actual base alteration has these properties. -/
theorem exists_projective_genericallyEtale_alteration_component
    (f : X ⟶ S) (g : Y ⟶ S) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    [IsDominant f] [IsAlteration g] (hgEt : IsGenericallyEtale g)
    {d : ℕ} (e : Y ⟶ relativeSpace S d) [IsClosedImmersion e]
    (he : e ≫ relativeStructure S d = g) :
    ∃ (T : Scheme.{u}) (j : T ⟶ pullback f g) (a : T ⟶ relativeSpace X d),
      IsIntegral T ∧ IsClosedImmersion j ∧
      Set.range j ∈ irreducibleComponents (pullback f g : Scheme.{u}) ∧
      IsAlteration (j ≫ pullback.fst f g) ∧ IsDominant (j ≫ pullback.snd f g) ∧
      IsGenericallyEtale (j ≫ pullback.fst f g) ∧
      IsClosedImmersion a ∧ a ≫ relativeStructure X d = j ≫ pullback.fst f g := by
  obtain ⟨T, j, hT, hj, hc, hq, hb, hEt⟩ := exists_genericallyEtale_alteration_component f g hgEt
  let := hj
  exact ⟨T, j, j ≫ baseChangeEmbedding f g e he,
    hT, hj, hc, hq, hb, hEt, inferInstance, by simp⟩

end Hironaka.Geometry.AlterationDominatingBaseChange
