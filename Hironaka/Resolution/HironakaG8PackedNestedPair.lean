import Hironaka.Resolution.HironakaG8FinitePartitionPacking
import Hironaka.Resolution.HironakaG8SortedNestedPairDescent

/-! Literal comparisons persist after parallel packing of nested charts. -/
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8PackedNestedPair

open BlowupTowers BlowupTowerTransforms MaxLocusLocal BlowupTowerIsomorphism
  MarkedIdeals MarkedIdeals.MarkedIdeal G3UniverseEmptyAwareCore
  HironakaSharpActualCurveComparisonRestriction HironakaG8FixedNestedOpenReadback
  HironakaG8SortedNestedEndpoint HironakaG8SortedNestedPairDescent
  HironakaG8EmptyAwareCoverBaseChange HironakaG8FinitePartitionPacking
  HironakaG8OccupiedSlotComparison

variable {n : ℕ} {X A B : CMfd.{0} n} {U V : Opens X}
local notation "𝓘c" => 𝓘(ℂ,ComplexModel n)
local notation "BU" => CMfd.of (n := n) U
local notation "BV" => CMfd.of (n := n) V

/-- Two parallel packings of an originally compared nested pair compare
on the full smaller chart when their ordered occupied round traces agree. -/
theorem packed_nested_pair_of_occupiedFootprints_eq
    (S G : BlowupTower BU A) (T J : BlowupTower BV B)
    {STrace : List (Set U)} {TTrace : List (Set V)}
    (hS : BlockPacking BU S G STrace) (hT : BlockPacking BV T J TTrace)
    (e : BU ≃ₘ⟮𝓘c,𝓘c⟯ CMfd.of (n := n) (nestedOpens V U))
    (he : ∀ x : U, (e x).val.val = x.val)
    (f : A ≃ₘ⟮𝓘c,𝓘c⟯ CMfd.of (n := n) (openPreimage T (nestedOpens V U)))
    (h : EmptyAwareTowerIso e S (restrict (nestedOpens V U) T) f)
    (M : MarkedIdeal n BU) (hM : M.IsWellFormed)
    (hFoot : occupiedFootprints G =
      (occupiedFootprints (restrict (nestedOpens V U) J)).map (e ⁻¹' ·)) :
    ∃ g : A ≃ₘ⟮𝓘c,𝓘c⟯ CMfd.of (n := n) (openPreimage J (nestedOpens V U)),
      (∀ y, (g y).val = (f y).val) ∧
      EmptyAwareTowerIso e G (restrict (nestedOpens V U) J) g := by
  let a := Diffeomorph.refl 𝓘c A ∞
  let b := Diffeomorph.refl 𝓘c B ∞
  have hb : J.proj ∘ b = T.proj := hT.proj_eq
  let g := sortedEndpoint T J a b hb f
  let K := restrict (nestedOpens V U) J
  have hVal (y : A) : (g y).val = (f y).val := rfl
  have hProj (y : A) : K.proj (g y) = e (G.proj y) := by
    apply Subtype.ext
    rw [proj_restrict,hVal,hT.proj_eq,hS.proj_eq]
    have hh := congrArg Subtype.val (emptyAware_proj_comm h y)
    simpa only [proj_restrict] using hh
  let C := {O : Opens (nestedOpens V U) // LocalEmptyComparisonOver e G K g O}
  refine ⟨g,hVal,emptyAware_over_of_local_of_occupiedFootprints_eq
    (fun W : C => W.val) ?_ e G K g hProj M hM hFoot (fun W => W.property)⟩
  intro y
  obtain ⟨x,rfl⟩ := e.surjective y
  obtain ⟨P,hxP,_,hSLocal⟩ := hS.local_cover_stable x ⊤ (by trivial)
  let PX : Opens X := ⟨(Subtype.val : U → X) '' (P : Set U),
    U.isOpen.isOpenMap_subtype_val _ P.isOpen⟩
  have hxPV : (e x).val ∈ nestedOpens V PX := ⟨x,hxP,(he x).symm⟩
  obtain ⟨Q,hxQ,hQ,hTLocal⟩ := hT.local_cover_stable (e x).val (nestedOpens V PX) hxPV
  let O : Opens X := ⟨(Subtype.val : V → X) '' (Q : Set V),
    V.isOpen.isOpenMap_subtype_val _ Q.isOpen⟩
  have hOU : O ≤ U := by
    rintro _ ⟨z,hz,rfl⟩
    obtain ⟨w,_,heq⟩ := hQ hz
    exact heq ▸ w.property
  have hOP : nestedOpens U O ≤ P := by
    intro z hz
    obtain ⟨y,hy,hEq⟩ := hz
    obtain ⟨w,hw,hW⟩ := hQ hy
    exact (Subtype.ext (hW.trans hEq) : w = z) ▸ hw
  have hOQ : nestedOpens V O ≤ Q := by
    intro z hz
    obtain ⟨y,hy,hEq⟩ := hz
    exact (Subtype.ext hEq : y = z) ▸ hy
  obtain ⟨aO,haO,hA⟩ := hSLocal _ hOP
  obtain ⟨bO,hbO,hB⟩ := hTLocal _ hOQ
  obtain ⟨p,hp,q,hq,hLocal⟩ := sorted_nested_common_subopen S T G J hOU
    e he f h a b aO bO haO hbO hA hB
  let H := nestedOpens (nestedOpens V U) (nestedOpens V O)
  have hNested : nestedOpens V O ≤ nestedOpens V U := fun _ hz => hOU hz
  have hFlat := isTowerIso_restrict_nestedOpens hNested J
  have hCmp := G3UniverseEmptyAwareCore.trans hLocal
    (G3UniverseEmptyAwareCore.symm (emptyAware_of_isTowerIso hFlat))
  have hEq : preimageOpen e H = nestedOpens U O := by
    ext z
    change (e z).val.val ∈ O ↔ z.val ∈ O
    rw [he]
  have hRead : LocalEmptyComparisonOver e G K g H := by
    apply canonical_local_comparison e g G K _ H hEq _ _ _ _ hCmp
    · intro z
      apply Subtype.ext
      apply Subtype.ext
      exact (hp z).trans (he z.val).symm
    · intro z
      apply Subtype.ext
      exact hq z
  exact ⟨⟨H,hRead⟩,(by exact ⟨(e x).val,hxQ,rfl⟩)⟩

end Hironaka.HironakaG8PackedNestedPair
