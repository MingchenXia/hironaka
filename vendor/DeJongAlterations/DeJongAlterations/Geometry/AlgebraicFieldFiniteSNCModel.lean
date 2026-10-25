import DeJongAlterations.Geometry.AlgebraicFieldFiniteBoundaryIdeals
import DeJongAlterations.Geometry.AlgebraicScalarPureCodimension
import DeJongAlterations.Geometry.FlatScalarCartierDescent
import DeJongAlterations.Geometry.SplitBoundaryDescent

/-! The actual finite split boundary and original closed scalar squares give native SNC descent. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace DeJongAlterations.Geometry.AlgebraicFieldFiniteSNCModel

open StableModification.Limits AlgebraicFieldFiniteModel

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

variable (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]

private theorem scalar_cover {Y : Scheme.{u}} {p : Y ⟶ Spec (.of L)} {i : Index k L}
    (m : Model (diagram k L) (scalarCone k L) p i) :
    Surjective m.g ∧ Flat m.g ∧ IsIntegralHom m.g ∧ IsAffineHom m.g := by
  let E := levelField k L i
  let : Algebra.IsAlgebraic E L := Algebra.IsAlgebraic.tower_top (K := k) (A := L) E
  let c : Spec (.of L) ⟶ Spec (.of E) := Spec.map (CommRingCat.ofHom E.val.toRingHom)
  let : Surjective c := ⟨fun y => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ y⟩⟩
  let : Flat c := inferInstance
  let : IsAffineHom c := inferInstance
  let : IsIntegralHom c := IsIntegralHom.SpecMap_iff.mpr
    (show E.val.toRingHom.IsIntegral from fun z => Algebra.IsIntegral.isIntegral z)
  have H : IsPullback m.g p m.fY c := by simpa only [scalarCone_π] using m.isPullback
  exact ⟨MorphismProperty.of_isPullback H.flip inferInstance,
    MorphismProperty.of_isPullback H.flip inferInstance,
    MorphismProperty.of_isPullback H.flip inferInstance,
    MorphismProperty.of_isPullback H.flip inferInstance⟩

private theorem codimension_of_comap {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [Flat f] [IsIntegralHom f] [Surjective f] (D : Y.IdealSheafData) {r : ℕ}
    (hD : HasPureCodimension (D.comap f).support r) : HasPureCodimension D.support r := by
  let g := SNCLocality.comapSubschemeMap f D
  have H : IsPullback g (D.comap f).subschemeι D.subschemeι f := by
    apply IsPullback.flip
    apply isPullback_of_isClosedImmersion
    · exact (SNCLocality.comapSubschemeMap_ι f D).symm
    · simp only [Scheme.IdealSheafData.ker_subschemeι]
  exact AlgebraicScalarPureCodimension.hasPureCodimension_of_isPullback f D (D.comap f) g H hD

/-- ORIGINAL actual SNC geometry INTERNALLY produces a genuine SNC boundary on the SAME
further smooth finite-field model, retaining its WHOLE original ideal-sheaf pullback. -/
theorem exists_snc_model [PerfectField L] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of L))
    [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
    (D : Y.IdealSheafData) (hD : IsStrictNormalCrossings D)
    {i : Index k L} (m : Model (diagram k L) (scalarCone k L) p i) (hm : m.IsFP)
    [Smooth m.fY] :
    ∃ (j : Index k L) (h : j ⟶ i) (D₀ : (m.baseChange h).Y.IdealSheafData),
      IsStrictNormalCrossings D₀ ∧ D₀.comap (m.baseChange h).g = D := by
  classical
  obtain ⟨j, h, I, D₀, e, _, hred, hwhole, _, hinfo, _⟩ :=
    SplitBoundaryDescent.exists_snc_descended_components k L p D hD m hm
  let M := m.baseChange h
  obtain ⟨hSurj, hFlat, hIntegral, hAffine⟩ := scalar_cover k L M
  let := hSurj
  let := hFlat
  let := hIntegral
  let := hAffine
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  let : IsLocallyNoetherian ((diagram k L).obj j) := by
    change IsLocallyNoetherian (Spec (.of (levelField k L j)))
    infer_instance
  let : LocallyOfFinitePresentation M.fY := (hm.baseChange h).1
  let : IsLocallyNoetherian M.Y := LocallyOfFiniteType.isLocallyNoetherian M.fY
  let : Smooth M.fY := by
    change Smooth (pullback.snd m.fY ((diagram k L).map h))
    infer_instance
  have hreg := RegularSmooth.isRegularScheme_of_smooth (K := levelField k L j) M.fY
  have hc : IsEffectiveCartierDivisor D₀ :=
    FlatScalarCartierDescent.of_flat_surjective_affine M.g D₀ (by rw [hwhole]; exact hD.cartier)
  refine ⟨j, h, D₀, ⟨hc, hred, (fun x _ => hreg x), ?_, ?_⟩, hwhole⟩
  · intro J hJ
    let K := J.map e.symm.toEmbedding
    have hK : K.Nonempty := hJ.map
    have hmap : K.map e.toEmbedding = J := by
      ext C
      simp [K]
    have heq := (hinfo ⟨K, hK⟩).1
    rw [hmap] at heq
    rw [heq]
    exact (hinfo ⟨K, hK⟩).2.2
  · intro J hJ
    let K := J.map e.symm.toEmbedding
    have hK : K.Nonempty := hJ.map
    have hmap : K.map e.toEmbedding = J := by
      ext C
      simp [K]
    have heq := (hinfo ⟨K, hK⟩).1
    rw [hmap] at heq
    rw [heq]
    apply codimension_of_comap M.g (I ⟨K, hK⟩)
    rw [(hinfo ⟨K, hK⟩).2.1]
    have hcard : K.card = J.card := Finset.card_map _
    rw [← hcard]
    exact hD.intersectionsCodimension K hK

end DeJongAlterations.Geometry.AlgebraicFieldFiniteSNCModel
