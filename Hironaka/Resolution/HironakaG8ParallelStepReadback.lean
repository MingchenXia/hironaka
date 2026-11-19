import Hironaka.Resolution.HironakaG8ParallelAdmissibleCentres
import Hironaka.Blowup.BlowupUniqueness
import Hironaka.Blowup.BlowupTowerIsomorphism

/-! Literal marked readback of a parallel step over a saturated isolating window. -/
set_option autoImplicit false
open Set TopologicalSpace Function
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8ParallelStepReadback
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen

variable {n : ℕ} {X Y Z A : CMfd.{0} n}

/-- The literal union restriction has one strict physical comparison with
the chosen local centre blowup over the identical earlier restricted
prefix. The original ordered marked record is transported exactly. -/
theorem parallel_step_readback_on_saturated_open
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (P : BlowupTower X Y)
    {ι : Type*} (C : ι → Set Y) {π : Z → Y} (hπ : IsBlowupAlong n (⋃ i, C i) π)
    (hTest : IsGeoTestTower M (.step P (⋃ i, C i) π hπ))
    (U : Opens X) (D : Set (openPreimage P U)) (ρ : A → openPreimage P U)
    (hρ : IsBlowupAlong n D ρ)
    (hTrace : (Subtype.val : openPreimage P U → Y) ⁻¹' (⋃ i, C i) = D) :
    let Q := BlowupTower.step P (⋃ i, C i) π hπ
    let S := BlowupTower.step (restrict U P) D ρ hρ
    let MU := MarkedIdeal.pullback (Subtype.val : U → X) M
    ∃ e : CMfd.of (n := n) (openPreimage Q U)
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A,
      IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) (restrict U Q) S e ∧
      IsGeoTestTower MU S ∧
      MarkedIdeal.pullback (Subtype.val : openPreimage Q U → Z) (geoTransformAlong M Q) =
        MarkedIdeal.pullback e (geoTransformAlong MU S) := by
  dsimp only
  let Q := BlowupTower.step P (⋃ i, C i) π hπ
  let V := openPreimage P U
  let f : openPreimage Q U → V := fun z => ⟨π z.val,z.property⟩
  have hf : IsBlowupAlong n D f := by
    rw [← hTrace]
    exact BlowupRestrictOpen.isBlowupAlong_restrict hπ V
      (V.isOpen.preimage hπ.contMDiff.continuous)
  obtain ⟨e,g,he,hg,hComm,_,hge,heg⟩ := BlowupUniqueness.exists_biholomorphism_over hf hρ
  let β : CMfd.of (n := n) (openPreimage Q U)
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A :=
    ⟨⟨e,g,congrFun hge,congrFun heg⟩,he,hg⟩
  let S := BlowupTower.step (restrict U P) D ρ hρ
  let MU := MarkedIdeal.pullback (Subtype.val : U → X) M
  have hIso : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) (restrict U Q) S β := by
    apply IsTowerIso.step (IsTowerIso.refl_self (restrict U P)) _ _ β
    · exact fun z => congrFun hComm z
    · exact hTrace.symm
  have hMU := IsWellFormed.pullback_val hM U
  have hLocal := isGeoTestTower_restrict U hM.isClosedSubmanifold_N hM.isCoherent Q hTest
  have hId : MarkedIdeal.pullback (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) MU = MU :=
    ContactCanonicalAlong.pullback_id MU hMU.isCoherent
  have hTests := IsTowerIso.isGeoTestTower_iff (𝔪 := MU) _ hMU.isClosedSubmanifold_N hMU.isCoherent hIso
  rw [hId] at hTests
  have hS := hTests.mp hLocal
  have hExact := IsTowerIso.geoTransformAlong_eq (𝔪 := MU) _ hMU.isClosedSubmanifold_N hMU.isCoherent hIso hS
  rw [hId,geoTransformAlong_restrict U hM.isClosedSubmanifold_N hM.isCoherent Q hTest] at hExact
  exact ⟨β,hIso,hS,hExact⟩

/-- At an isolating current-stage open, the union trace equals the
selected member's trace. This also allows the selected member to miss the open. -/
theorem parallel_trace_eq_selected {ι : Type*} (C : ι → Set Y)
    (V : Opens Y) (j : ι) (hV : ∀ i, i ≠ j → Disjoint (C i) (V : Set Y)) :
    (Subtype.val : V → Y) ⁻¹' (⋃ i, C i) = (Subtype.val : V → Y) ⁻¹' C j := by
  ext x
  constructor
  · intro hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    by_cases h : i = j
    · change x.val ∈ C j
      simpa only [h] using hi
    · exact (disjoint_left.mp (hV i h) hi x.property).elim
  · exact fun hx => mem_iUnion.mpr ⟨j,hx⟩

/-- If no family member meets the open, the exact trace is empty and
the readback can use a real empty identity blowup. -/
theorem parallel_trace_eq_empty {ι : Type*} (C : ι → Set Y)
    (V : Opens Y) (hV : ∀ i, Disjoint (C i) (V : Set Y)) :
    (Subtype.val : V → Y) ⁻¹' (⋃ i, C i) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨i,hi⟩ := mem_iUnion.mp hx
  exact disjoint_left.mp (hV i) hi x.property

end Hironaka.HironakaG8ParallelStepReadback
