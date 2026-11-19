import Hironaka.Resolution.HironakaG8FiniteParallelTest

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8FiniteParallelLocalReadback

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealRestrictOpen
  HironakaG8FiniteParallelGeometry HironakaG8EmptyAwareTestTransport HironakaG8RankedTestCompression
  HironakaG8OccupiedSlotComparison HironakaG8CofinalOccupiedAncestry
  HironakaStageCenters G3UniverseEmptyAwareCore

variable {n : ℕ} {X Y Z : CMfd.{0} n}
local notation "𝓘c" => 𝓘(ℂ, ComplexModel n)

private theorem blockCentre_as_occupied (T : BlowupTower X Y) :
    blockCentre T = ⋃ C ∈ occupiedFootprints T, C := by
  ext x
  simp only [blockCentre,mem_iUnion,occupiedFootprints,List.mem_map,mem_occupiedSlots]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨slotFootprint T i,⟨i,(slotFootprint_nonempty_iff T i).mp ⟨x,hi⟩,rfl⟩,hi⟩
  · rintro ⟨C,⟨i,_,rfl⟩,hi⟩
    exact ⟨i,hi⟩

private theorem short_compare_step {C : Set X} {π : Z → X} (hπ : IsBlowupAlong n C π) :
    ∀ {Y : CMfd.{0} n} (Q : BlowupTower X Y), Q.length ≤ 1 → blockCentre Q = C →
       (e : Y ≃ₘ⟮𝓘c,𝓘c⟯ Z) → (∀ z, π (e z) = Q.proj z) →
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘c X ∞) Q (.step .refl C π hπ) e
  | _, .refl, _, hC, e, hProj => by
      have hc : C = ∅ := hC.symm.trans (by simp [blockCentre,slotFootprint])
      clear hC
      subst C
      have hInv (z : Z) : (e.symm z : X) = π z := by
        simpa only [e.apply_symm_apply,BlowupTower.proj_refl,id_eq] using (hProj (e.symm z)).symm
      have he : e.symm.symm = e := by ext z; rfl
      simpa only [Diffeomorph.refl_trans,he] using
        (EmptyAwareTowerIso.rightEmpty
          (EmptyAwareTowerIso.refl (Φ := Diffeomorph.refl 𝓘c X ∞)) hπ e.symm hInv)
  | _, .step .refl D q hq, _, hC, e, hProj => by
      have hd : blockCentre (.step .refl D q hq) = D := by
        ext x
        simp only [blockCentre,mem_iUnion]
        constructor
        · rintro ⟨i,hi⟩
          by_cases h : i = 0
          · simpa [slotFootprint,h] using hi
          · simp [slotFootprint,h] at hi
        · intro hx
          exact ⟨0,by simpa [slotFootprint] using hx⟩
      subst C
      exact EmptyAwareTowerIso.step
        (EmptyAwareTowerIso.refl (Φ := Diffeomorph.refl 𝓘c X ∞)) hq hπ e hProj
          (by simpa only [Diffeomorph.coe_refl,preimage_id] using hd)
  | _, .step (.step P C π hπ) D q hq, hLen, _, _, _ => by simp at hLen

/-- The grouped step and literal restricted sequence agree through empty
steps when at most one original projected footprint remains visible. The
comparison has identity underlying points on the original terminal object. -/
theorem local_grouped_step_comparison
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (T : BlowupTower X Y)
    (h : IsBlowupAlong n (blockCentre T) T.proj)
    (U : Opens X)
    (hSingle : ∀ i j, Occupied (restrict U T) i → Occupied (restrict U T) j → i = j) :
    let G := BlowupTower.step .refl (blockCentre T) T.proj h
    ∃ e : CMfd.of (n := n) (openPreimage T U) ≃ₘ⟮𝓘c,𝓘c⟯
          CMfd.of (n := n) (openPreimage G U),
      (∀ y, (e y).val = y.val) ∧
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘c (CMfd.of (n := n) U) ∞)
        (restrict U T) (restrict U G) e := by
  dsimp only
  let G := BlowupTower.step .refl (blockCentre T) T.proj h
  let MU := MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → X) M
  have hMU : MU.IsWellFormed := IsWellFormed.pullback_val hM U
  obtain ⟨Z,Q,f,hOcc,_,hCmp,_⟩ := test_empty_free_compression MU hMU (restrict U T)
  have hLen : Q.length ≤ 1 := by
    by_contra! hLen
    let i : {j // Occupied Q j} := ⟨0,occupied_of_empty_free Q hOcc ⟨0,by omega⟩⟩
    let j : {j // Occupied Q j} := ⟨1,occupied_of_empty_free Q hOcc ⟨1,by omega⟩⟩
    let χ := occupiedComparison hCmp
    have hSame : χ i = χ j := Subtype.ext (hSingle _ _ (χ i).property (χ j).property)
    exact (by decide : (0 : ℕ) ≠ 1) (congrArg Subtype.val (χ.injective hSame))
  have he : occupiedFootprints Q = occupiedFootprints (restrict U T) := by
    simpa only [Diffeomorph.coe_refl,preimage_id,List.map_id'] using occupiedFootprints_emptyAware hCmp
  have hCentre : blockCentre Q = (Subtype.val : U → X) ⁻¹' blockCentre T := by
    rw [blockCentre_as_occupied Q,he,← blockCentre_as_occupied]
    simp only [blockCentre,slotFootprint_restrict,preimage_iUnion]
  let e : CMfd.of (n := n) (openPreimage T U) ≃ₘ⟮𝓘c,𝓘c⟯
      CMfd.of (n := n) (openPreimage G U) := Diffeomorph.refl _ _ _
  have hProj (z : Z) : (restrict U G).proj (e (f z)) = Q.proj z := by
    have hF : (restrict U T).proj (f z) = Q.proj z := emptyAware_proj_comm hCmp z
    apply Subtype.ext
    rw [proj_restrict,← hF,proj_restrict]
    rfl
  have hShort : EmptyAwareTowerIso (Diffeomorph.refl 𝓘c (CMfd.of (n := n) U) ∞)
      Q (restrict U G) (f.trans e) := by
    exact short_compare_step _ Q hLen hCentre _ hProj
  refine ⟨e,fun _ => rfl,?_⟩
  have hc := G3UniverseEmptyAwareCore.trans (G3UniverseEmptyAwareCore.symm hCmp) hShort
  have hEnd : f.symm.trans (f.trans e) = e := by
    apply Diffeomorph.ext
    intro y
    change e (f (f.symm y)) = e y
    rw [f.apply_symm_apply]
  simpa only [hEnd,Diffeomorph.symm_refl,Diffeomorph.refl_trans] using hc

end Hironaka.HironakaG8FiniteParallelLocalReadback
