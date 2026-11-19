import Hironaka.Resolution.HironakaG8FootprintAlignedRestriction
import Hironaka.Resolution.HironakaG8OrderedFootprintTraces
import Hironaka.Resolution.HironakaG8RankedTestCompression
import Hironaka.Resolution.HironakaG8PenultimateCoverDescent
import Hironaka.Resolution.HironakaG8AlignedEmptyStrictComparison
import Hironaka.Resolution.HironakaG3EmptyAwareOpenRestriction
import Hironaka.Resolution.HironakaG8EmptyAwareTestTransport

/-! Local empty-aware comparison descends through chosen physical compressions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8EmptyAwareCoverDescent

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  HironakaG3EmptyAwareHistory HironakaG3EmptyAwareOpenRestriction
  HironakaG8PenultimateCoverDescent HironakaG8AlignedEmptyStrictComparison
  HironakaG8CofinalOccupiedAncestry HironakaSharpActualCurveComparisonRestriction

variable {n : ℕ} {X Y Z A B : CMfd.{0} n}
local notation "𝓘c" => 𝓘(ℂ, ComplexModel n)
local notation "𝟙" => Diffeomorph.refl 𝓘c X ∞

def LocalEmptyComparison (S : BlowupTower X Y) (T : BlowupTower X Z)
    (e : Y ≃ₘ⟮𝓘c,𝓘c⟯ Z) (U : Opens X) : Prop :=
  ∃ eU : CMfd.of (n := n) (openPreimage S U) ≃ₘ⟮𝓘c,𝓘c⟯
      CMfd.of (n := n) (openPreimage T U),
    (∀ z, (eU z).val = e z.val) ∧
    EmptyAwareTowerIso (Diffeomorph.refl 𝓘c (CMfd.of (n := n) U) ∞)
      (restrict U S) (restrict U T) eU

private theorem restrict_comparison
    {S : BlowupTower X Y} {T : BlowupTower X Z}
    {e : Y ≃ₘ⟮𝓘c,𝓘c⟯ Z} (h : EmptyAwareTowerIso 𝟙 S T e) (U : Opens X) :
    LocalEmptyComparison S T e U := by
  have hU : preimageOpen (𝟙 : X ≃ₘ⟮𝓘c,𝓘c⟯ X) U = U := rfl
  let Data (V : Opens X) : Prop :=
    ∃ eU : CMfd.of (n := n) (openPreimage S V) ≃ₘ⟮𝓘c,𝓘c⟯
        CMfd.of (n := n) (openPreimage T U),
      (∀ z, (eU z).val = e z.val) ∧
      ∃ f : CMfd.of (n := n) V ≃ₘ⟮𝓘c,𝓘c⟯ CMfd.of (n := n) U,
        (∀ z, (f z).val = z.val) ∧ EmptyAwareTowerIso f (restrict V S) (restrict U T) eU
  have hData : Data (preimageOpen (𝟙 : X ≃ₘ⟮𝓘c,𝓘c⟯ X) U) :=
    ⟨_,fun _ => rfl,_,fun _ => rfl,emptyAware_open_restriction h U⟩
  obtain ⟨a,ha,f,hf,hIso⟩ := hU ▸ hData
  have hF : f = Diffeomorph.refl 𝓘c (CMfd.of (n := n) U) ∞ :=
    Diffeomorph.ext fun z => Subtype.ext (hf z)
  exact ⟨a,ha,hF ▸ hIso⟩

/-- Given exact physical compressions and aligned local raw slots on those
compressions, local empty-aware comparisons descend with the prescribed endpoint. -/
theorem emptyAware_of_local_of_compressed_alignment
    {I : Type*} (U : I → Opens X) (hU : ∀ x : X, ∃ i, x ∈ U i)
    (S : BlowupTower X Y) (T : BlowupTower X Z) (e : Y ≃ₘ⟮𝓘c,𝓘c⟯ Z)
    (he : ∀ z, T.proj (e z) = S.proj z)
    (Q : BlowupTower X A) (R : BlowupTower X B)
    (a : A ≃ₘ⟮𝓘c,𝓘c⟯ Y) (b : B ≃ₘ⟮𝓘c,𝓘c⟯ Z)
    (ha : EmptyAwareTowerIso 𝟙 Q S a) (hb : EmptyAwareTowerIso 𝟙 R T b)
    (hLen : Q.length = R.length)
    (hOcc : ∀ i k, Occupied (restrict (U i) Q) k ↔ Occupied (restrict (U i) R) k)
    (hLocal : ∀ i, LocalEmptyComparison S T e (U i)) :
    EmptyAwareTowerIso 𝟙 S T e := by
  let g := a.trans (e.trans b.symm)
  have hg (z : A) : R.proj (g z) = Q.proj z := by
    have h := (emptyAware_proj_comm hb (b.symm (e (a z)))).symm
    change R.proj (g z) = T.proj (b (b.symm (e (a z)))) at h
    rw [b.apply_symm_apply,he,emptyAware_proj_comm ha] at h
    exact h
  have hStrict (i : I) : LocalStrictComparison 𝟙 Q R g (U i) := by
    obtain ⟨aU,haU,haIso⟩ := restrict_comparison ha (U i)
    obtain ⟨bU,hbU,hbIso⟩ := restrict_comparison hb (U i)
    obtain ⟨eU,heU,heIso⟩ := hLocal i
    let gU := aU.trans (eU.trans bU.symm)
    have hComp := G3UniverseEmptyAwareCore.trans haIso
      (G3UniverseEmptyAwareCore.trans heIso (G3UniverseEmptyAwareCore.symm hbIso))
    have hStrictIso := isTowerIso_of_emptyAware_aligned hComp
      (by simpa only [length_restrict] using hLen) (hOcc i)
    have hG (z : openPreimage Q (U i)) : (gU z).val = g z.val := by
      apply b.injective
      have h := (hbU (bU.symm (eU (aU z)))).symm
      change b (gU z).val = (bU (bU.symm (eU (aU z)))).val at h
      rw [bU.apply_symm_apply,heU,haU] at h
      simpa [g] using h
    exact ⟨gU,hG,hStrictIso⟩
  have hGR := isTowerIso_of_local_strict_comparisons U hU g hLen hg hStrict
  have hComp := G3UniverseEmptyAwareCore.trans (G3UniverseEmptyAwareCore.symm ha)
    (G3UniverseEmptyAwareCore.trans (emptyAware_of_isTowerIso hGR) hb)
  have hEnd : a.symm.trans (g.trans b) = e := by
    ext x
    change b (b.symm (e (a (a.symm x)))) = e x
    simp
  rwa [hEnd] at hComp


open HironakaG8OccupiedSlotComparison HironakaG8OrderedFootprintTraces
  HironakaG8RankedTestCompression HironakaStageCenters HironakaG8EmptyAwareTestTransport
  HironakaG8NestedVisibleWordLift HironakaG8FootprintAlignedRestriction

private theorem raw_footprints_eq_occupied_of_emptyFree
    (T : BlowupTower X Y) (h : StageCentres (fun _ C => C.Nonempty) T) :
    occupiedFootprints T = footprints ⟨Y,T⟩ := by
  apply occupiedFootprints_eq_map_of_exact_slots T (List.range T.length) (slotFootprint T)
  · intro j k hk
    have hj := (List.getElem?_eq_some_iff.mp hk).1
    rw [List.length_range] at hj
    rw [List.getElem?_range hj] at hk
    cases hk
    rfl
  · intro j
    rw [List.length_range,slotFootprint_nonempty_iff]
    exact ⟨occupied_lt_length T,fun hj => occupied_of_empty_free T h ⟨j,hj⟩⟩

/-- On a single original base, exact ordered occupied footprints and
actual local empty-aware comparisons with a fixed endpoint imply the
global empty-aware comparison with that very endpoint. -/
theorem emptyAware_of_local_of_occupiedFootprints_eq
    {I : Type*} (U : I → Opens X) (hU : ∀ x : X, ∃ i, x ∈ U i)
    (S : BlowupTower X Y) (T : BlowupTower X Z) (e : Y ≃ₘ⟮𝓘c,𝓘c⟯ Z)
    (he : ∀ z, T.proj (e z) = S.proj z)
    (M : MarkedIdeals.MarkedIdeal n X) (hM : M.IsWellFormed)
    (hFoot : occupiedFootprints S = occupiedFootprints T)
    (hLocal : ∀ i, LocalEmptyComparison S T e (U i)) :
    EmptyAwareTowerIso 𝟙 S T e := by
  obtain ⟨A,Q,a,hQ,_,ha,_⟩ := test_empty_free_compression M hM S
  obtain ⟨B,R,b,hR,_,hb,_⟩ := test_empty_free_compression M hM T
  have haFoot : occupiedFootprints Q = occupiedFootprints S := by
    simpa only [Diffeomorph.coe_refl,preimage_id,List.map_id'] using occupiedFootprints_emptyAware ha
  have hbFoot : occupiedFootprints R = occupiedFootprints T := by
    simpa only [Diffeomorph.coe_refl,preimage_id,List.map_id'] using occupiedFootprints_emptyAware hb
  have hRaw : footprints ⟨A,Q⟩ = footprints ⟨B,R⟩ := by
    rw [← raw_footprints_eq_occupied_of_emptyFree Q hQ,
      ← raw_footprints_eq_occupied_of_emptyFree R hR,haFoot,hbFoot,hFoot]
  have hLen : Q.length = R.length := by
    simpa [footprints] using congrArg List.length hRaw
  exact emptyAware_of_local_of_compressed_alignment U hU S T e he Q R a b ha hb hLen
    (fun i => (restricted_slots_aligned_of_footprints_eq Q R hRaw (U i)).2) hLocal

end Hironaka.HironakaG8EmptyAwareCoverDescent
