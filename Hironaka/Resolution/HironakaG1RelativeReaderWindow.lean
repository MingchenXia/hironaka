import Hironaka.Resolution.HironakaG1RelativeBoundaryProjections
import Hironaka.Resolution.HironakaG1SNCReaderNormalization
import Hironaka.Resolution.HironakaSmoothSubmersionMonomialChartPullback

/-! A common open with the two original SNC reader maps and their ordered slots. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG1RelativeReaderWindow

open BlowupTowers HironakaG1RelativeBoundaryProjections
  HironakaG1SNCReaderNormalization HironakaSmoothSubmersionMonomialChartPullback
  BlowupFlatCoordinates HironakaActualAnalyticSubspace
  HironakaActualIntrinsicLabelledBoundaryIdeals NormalCrossings CategoryTheory

noncomputable section

private def euclideanBlock (m : ℕ) : Block m ≃L[ℂ] ComplexModel m :=
  ({ toFun := WithLp.toLp 2
     invFun := WithLp.ofLp
     left_inv := WithLp.ofLp_toLp 2
     right_inv := WithLp.toLp_ofLp 2
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Block m ≃ₗ[ℂ] ComplexModel m).toContinuousLinearEquiv

private def joinBlock {r a : ℕ} (x : Block r × Block a) : ComplexModel (r+a) :=
  joinCoordinates r a (euclideanBlock r x.1) (euclideanBlock a x.2)

private theorem joinBlock_active {r a : ℕ} (x : Block r × Block a) (i : Fin r) :
    joinBlock x (i.castAdd a) = x.1 i := by
  change _ = (euclideanBlock r x.1) i
  rw [← fibreProjection_apply, joinBlock, fibreProjection_join]

private theorem joinBlock_zero {r a : ℕ} : joinBlock (0 : Block r × Block a) = 0 := by
  simp [joinBlock, joinCoordinates]

private theorem contDiff_joinBlock (r a : ℕ) :
    ContDiff ℂ ∞ (joinBlock : Block r × Block a → ComplexModel (r+a)) := by
  apply (splitCoordinates r a).symm.contDiff.comp
  exact ((euclideanBlock r).contDiff.comp contDiff_fst).prodMk
    ((euclideanBlock a).contDiff.comp contDiff_snd)

private theorem contDiff_left (r a b : ℕ) :
    ContDiff ℂ ∞ (leftProjection r a b) := by
  unfold leftProjection
  fun_prop

private theorem contDiff_right (r a b : ℕ) :
    ContDiff ℂ ∞ (rightProjection r a b) := by
  unfold rightProjection
  fun_prop

private theorem rightProjection_zero_anchor {r a b : ℕ} (u : Block r) :
    rightProjection r a b ((0,u),(0,0)) = 0 := by
  change ((fun i => u i * (0 : Block r) i), (0 : Block b)) = (0, 0)
  simp only [Pi.zero_apply, mul_zero]
  rfl

variable {n₁ n₂ : ℕ} {M₁ : CMfd.{0} n₁} {M₂ : CMfd.{0} n₂}
  {p₁ : M₁} {p₂ : M₂} {E₁ : List (Set M₁)} {E₂ : List (Set M₂)}
  {τ : Fin E₁.length ≃ Fin E₂.length}
  (R : RelativeReaders p₁ p₂ E₁ E₂ τ)

private abbrev A := Ambient R.r R.a R.b

/-- Pull the two actual SNC coordinate opens back to the common nonzero-ratio locus. -/
def readerUnitWindow : Opens (A R) :=
  ⟨unitLocus R.r R.a R.b ∩
      (joinBlock ∘ leftProjection R.r R.a R.b) ⁻¹' R.sourceCoordinateOpen ∩
      (joinBlock ∘ rightProjection R.r R.a R.b) ⁻¹' R.targetCoordinateOpen,
    ((isOpen_unitLocus R.r R.a R.b).inter
      (R.sourceCoordinateOpen.isOpen.preimage
        ((contDiff_joinBlock R.r R.a).comp (contDiff_left R.r R.a R.b)).continuous)).inter
      (R.targetCoordinateOpen.isOpen.preimage
        ((contDiff_joinBlock R.r R.b).comp (contDiff_right R.r R.a R.b)).continuous)⟩

private def firstOpen (x : readerUnitWindow R) : R.sourceCoordinateOpen :=
  ⟨joinBlock (leftProjection R.r R.a R.b x.val), x.property.1.2⟩

private def secondOpen (x : readerUnitWindow R) : R.targetCoordinateOpen :=
  ⟨joinBlock (rightProjection R.r R.a R.b x.val), x.property.2⟩

/-- The first map on the common open uses the actual inverse normalized reader. -/
def firstReaderMap (x : readerUnitWindow R) : M₁ :=
  (R.sourceDiffeomorph.symm (firstOpen R x)).val

/-- The second map uses the actual inverse reader and the separate ratio block. -/
def secondReaderMap (x : readerUnitWindow R) : M₂ :=
  (R.targetDiffeomorph.symm (secondOpen R x)).val

/-- At zero active and complementary coordinates, arbitrary nonzero ratios give an
actual point of the common open. -/
theorem ratio_anchor_mem_readerUnitWindow (u : Block R.r) (hu : ∀ i, u i ≠ 0) :
    (((0,u),(0,0)) : A R) ∈ readerUnitWindow R := by
  refine ⟨⟨hu, ?_⟩, ?_⟩
  · change joinBlock (0 : Block R.r × Block R.a) ∈ R.sourceCoordinateOpen
    rw [joinBlock_zero]
    exact R.source_zero_mem
  · change joinBlock (rightProjection R.r R.a R.b ((0,u),(0,0))) ∈ R.targetCoordinateOpen
    rw [rightProjection_zero_anchor, joinBlock_zero]
    exact R.target_zero_mem

/-- Both actual ambient anchors are recovered on the common ratio window. -/
theorem reader_maps_at_ratio_anchor (u : Block R.r) (hu : ∀ i, u i ≠ 0) :
    let x : readerUnitWindow R := ⟨((0,u),(0,0)), ratio_anchor_mem_readerUnitWindow R u hu⟩
    firstReaderMap R x = p₁ ∧ secondReaderMap R x = p₂ := by
  intro x
  have hFirst : firstOpen R x = R.sourceDiffeomorph ⟨p₁,mem_flatDomain_self R.Φ₁⟩ := by
    apply Subtype.ext
    change joinBlock (0 : Block R.r × Block R.a) = _
    rw [joinBlock_zero]
    exact (readerDiffeomorph_center R.Φ₁ R.hsrc₁ R.σ₁ R.zero₁).symm
  have hSecond : secondOpen R x = R.targetDiffeomorph ⟨p₂,mem_flatDomain_self R.Φ₂⟩ := by
    apply Subtype.ext
    change joinBlock (rightProjection R.r R.a R.b ((0,u),(0,0))) = _
    rw [rightProjection_zero_anchor, joinBlock_zero]
    exact (readerDiffeomorph_center R.Φ₂ R.hsrc₂ R.σ₂ R.zero₂).symm
  rw [firstReaderMap, secondReaderMap, hFirst, hSecond, R.sourceDiffeomorph.symm_apply_apply,
    R.targetDiffeomorph.symm_apply_apply]
  exact ⟨rfl, rfl⟩

/-- Corresponding original boundary slots pull back to literally the same set. -/
theorem reader_maps_slot_preimage_eq (i : Fin E₁.length) :
    firstReaderMap R ⁻¹' E₁.get i = secondReaderMap R ⁻¹' E₂.get (τ i) := by
  ext x
  change firstReaderMap R x ∈ E₁.get i ↔ secondReaderMap R x ∈ E₂.get (τ i)
  rw [firstReaderMap, secondReaderMap, R.source_slot_member, R.target_slot_member,
    R.sourceDiffeomorph.apply_symm_apply, R.targetDiffeomorph.apply_symm_apply]
  change
    (∃ j, R.slot i = some j ∧ joinBlock (leftProjection R.r R.a R.b x.val) (j.castAdd R.a) = 0) ↔
    (∃ j, R.slot i = some j ∧ joinBlock (rightProjection R.r R.a R.b x.val) (j.castAdd R.b) = 0)
  simp only [joinBlock_active, rightProjection_coordinate_eq_zero_iff _ _ _ _ x.property.1.1]
  rfl

/-- Position-preserving labels give equality of the whole ordered lists,
including the slots that are empty on the common open. -/
theorem reader_maps_ordered_boundary_eq (hτ : ∀ i, (τ i).val = i.val) :
    E₁.map (firstReaderMap R ⁻¹' ·) = E₂.map (secondReaderMap R ⁻¹' ·) := by
  apply List.ext_get
  · simpa only [List.length_map, Fintype.card_fin] using Fintype.card_congr τ
  intro j hj₁ hj₂
  simp only [List.get_eq_getElem, List.getElem_map]
  let i : Fin E₁.length := ⟨j, List.length_map _ ▸ hj₁⟩
  have hi : (τ i).val = j := hτ i
  simpa only [List.get_eq_getElem, hi] using reader_maps_slot_preimage_eq R i

/-- The two maps on the common open are holomorphic in the original ambient
structures. -/
theorem reader_maps_contMDiff :
    ContMDiff 𝓘(ℂ, A R) 𝓘(ℂ, ComplexModel n₁) ∞ (firstReaderMap R) ∧
    ContMDiff 𝓘(ℂ, A R) 𝓘(ℂ, ComplexModel n₂) ∞ (secondReaderMap R) := by
  have hFirst : ContMDiff 𝓘(ℂ, A R) 𝓘(ℂ, ComplexModel (R.r+R.a)) ∞ (firstOpen R) := by
    apply (ContMDiff.subtypeVal_comp_iff R.sourceCoordinateOpen _).mp
    exact ((contDiff_joinBlock R.r R.a).comp (contDiff_left R.r R.a R.b)).contMDiff.comp
      contMDiff_subtype_val
  have hSecond : ContMDiff 𝓘(ℂ, A R) 𝓘(ℂ, ComplexModel (R.r+R.b)) ∞ (secondOpen R) := by
    apply (ContMDiff.subtypeVal_comp_iff R.targetCoordinateOpen _).mp
    exact ((contDiff_joinBlock R.r R.b).comp (contDiff_right R.r R.a R.b)).contMDiff.comp
      contMDiff_subtype_val
  exact ⟨contMDiff_subtype_val.comp (R.sourceDiffeomorph.symm.contMDiff.comp hFirst),
    contMDiff_subtype_val.comp (R.targetDiffeomorph.symm.contMDiff.comp hSecond)⟩

/-- An actual intrinsic labelled isomorphism yields the common ratio open
and exact equality of the whole pulled ordered boundary lists. -/
theorem exists_readerUnitWindow_of_intrinsic_iso
    (C₁ : Set M₁) (C₂ : Set M₂)
    (e : actualSubspaceLocallyRingedSpace (n := n₁) C₁ ≅
      actualSubspaceLocallyRingedSpace (n := n₂) C₂) (c : C₁)
    (hE₁ : IsSNCDivisor n₁ E₁) (hE₂ : IsSNCDivisor n₂ E₂)
    (hτ : ∀ i, (τ i).val = i.val)
    (hTrace : ∀ i, Ideal.map (e.hom.stalkMap c).hom
      (actualLabelledBoundaryTraceIdeal C₂ E₂ (τ i) (e.hom.base c)) =
        actualLabelledBoundaryTraceIdeal C₁ E₁ i c) :
    ∃ (R₀ : RelativeReaders c.val (e.hom.base c).val E₁ E₂ τ)
      (x : readerUnitWindow R₀),
      firstReaderMap R₀ x = c.val ∧ secondReaderMap R₀ x = (e.hom.base c).val ∧
      E₁.map (firstReaderMap R₀ ⁻¹' ·) = E₂.map (secondReaderMap R₀ ⁻¹' ·) := by
  obtain ⟨R₀⟩ := exists_relative_readers C₁ C₂ e c hE₁ hE₂ τ hTrace
  have hOne : ∀ i : Fin R₀.r, (1 : Block R₀.r) i ≠ 0 := fun _ => one_ne_zero
  let x : readerUnitWindow R₀ := ⟨((0,1),(0,0)), ratio_anchor_mem_readerUnitWindow R₀ 1 hOne⟩
  obtain ⟨hFirst, hSecond⟩ := reader_maps_at_ratio_anchor R₀ 1 hOne
  exact ⟨R₀, x, hFirst, hSecond, reader_maps_ordered_boundary_eq R₀ hτ⟩

private theorem joinBlock_reader_coordinates {r a : ℕ} (v : ComplexModel (r+a)) :
    joinBlock ((euclideanBlock r).symm (fibreProjection r a v),
      (euclideanBlock a).symm (blockProjection r a v)) = v := by
  unfold joinBlock
  rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply,
    joinCoordinates_projections]

/-- A pair of actual reader points with compatible active ratios lifts to
the common open, with the exact given nonzero ratio coordinates. -/
theorem exists_reader_lift_of_coordinate_ratio
    (x : readerSource R.Φ₁) (y : readerSource R.Φ₂)
    (u : Block R.r) (hu : ∀ i, u i ≠ 0)
    (hRatio : ∀ i : Fin R.r, (R.targetDiffeomorph y).val (i.castAdd R.b) =
      u i * (R.sourceDiffeomorph x).val (i.castAdd R.a)) :
    ∃ z : readerUnitWindow R, firstReaderMap R z = x.val ∧
      secondReaderMap R z = y.val ∧ z.val.1.2 = u := by
  let a := (R.sourceDiffeomorph x).val
  let b := (R.targetDiffeomorph y).val
  let z₀ : A R := (((euclideanBlock R.r).symm (fibreProjection R.r R.a a), u),
    ((euclideanBlock R.a).symm (blockProjection R.r R.a a),
      (euclideanBlock R.b).symm (blockProjection R.r R.b b)))
  have hLeft : joinBlock (leftProjection R.r R.a R.b z₀) = a :=
    joinBlock_reader_coordinates a
  have hActive (i : Fin R.r) : (rightProjection R.r R.a R.b z₀).1 i =
      ((euclideanBlock R.r).symm (fibreProjection R.r R.b b)) i := by
    change u i * fibreProjection R.r R.a a i = fibreProjection R.r R.b b i
    rw [fibreProjection_apply, fibreProjection_apply]
    exact (hRatio i).symm
  have hRight : joinBlock (rightProjection R.r R.a R.b z₀) = b := by
    have hProj : rightProjection R.r R.a R.b z₀ =
        ((euclideanBlock R.r).symm (fibreProjection R.r R.b b),
          (euclideanBlock R.b).symm (blockProjection R.r R.b b)) :=
      Prod.ext (funext hActive) rfl
    rw [hProj]
    exact joinBlock_reader_coordinates b
  have hz₀ : z₀ ∈ readerUnitWindow R := by
    refine ⟨⟨hu, ?_⟩, ?_⟩
    · change joinBlock (leftProjection R.r R.a R.b z₀) ∈ R.sourceCoordinateOpen
      rw [hLeft]
      exact (R.sourceDiffeomorph x).property
    · change joinBlock (rightProjection R.r R.a R.b z₀) ∈ R.targetCoordinateOpen
      rw [hRight]
      exact (R.targetDiffeomorph y).property
  let z : readerUnitWindow R := ⟨z₀, hz₀⟩
  have hX : firstOpen R z = R.sourceDiffeomorph x := Subtype.ext hLeft
  have hY : secondOpen R z = R.targetDiffeomorph y := Subtype.ext hRight
  refine ⟨z, ?_, ?_, rfl⟩
  · rw [firstReaderMap, hX, R.sourceDiffeomorph.symm_apply_apply]
  · rw [secondReaderMap, hY, R.targetDiffeomorph.symm_apply_apply]

#print axioms ratio_anchor_mem_readerUnitWindow
#print axioms reader_maps_at_ratio_anchor
#print axioms reader_maps_slot_preimage_eq
#print axioms reader_maps_ordered_boundary_eq
#print axioms reader_maps_contMDiff
#print axioms exists_readerUnitWindow_of_intrinsic_iso
#print axioms exists_reader_lift_of_coordinate_ratio

end
end Hironaka.HironakaG1RelativeReaderWindow
