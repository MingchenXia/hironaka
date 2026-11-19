import Hironaka.Resolution.HironakaActualAnchoredStrictCarriers
import Hironaka.Resolution.HironakaActualCurrentStrictCarrierLocality
import Hironaka.Resolution.HironakaActualPointLocalInitialValues

/-! Actual ORIGINAL source tangent validity and complete kept contact records
along different anchored histories. Original strict carriers and the whole
ordered boundary are retained. This does not yet prove alternate target
tangent lower domains/canonical tails or chronological numerical equality. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualAnchoredContactRecords
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism RelativePrincipalizationSpan HomogenizedIdealAlong
  HomogenizedGlueingTower StepOneValue StepOneLowerDomain ContactStageKept
  HironakaActualGeneratedCurrentHistories HironakaActualAnchoredCurrentHistories
  HironakaActualAnchoredStrictCarriers HironakaActualRawRecordPullbacks
variable {n : ℕ} {X X' Y Y' : CMfd.{u} n}

theorem original_chosen_tangent_from_good_record
    (A : MarkedIdeal n X) (B : MarkedIdeal n X')
    (hhol : ∀x g,A.ideal.mem x g → HolomorphicAt n g x)
    (hcl : ∀x g,IsInSpanAt (n := n) (A.ideal.mem x) x g → A.ideal.mem x g)
    (hB : B.IsWellFormed) (hmax : IsMaximalOrderAlong B.N B.ideal B.d)
    (hd : 1≤A.d) (V : Opens X) (V' : Opens X')
    (φ : CMfd.of (n := n) V ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V')
    (hrec : MarkedIdeal.pullback (Subtype.val : V → X) A=
      MarkedIdeal.pullback φ (MarkedIdeal.pullback (Subtype.val : V' → X') B))
    (x : V) (hx : x.val∈A.cosupp) :
    x.val∈(tangentChoice A x.val).1 ∧
      TangentDirectionAlong.IsTangentDirectionAlong A.N A.ideal A.d
        (tangentChoice A x.val).1 (tangentChoice A x.val).2 :=
  StepOneLowerDomain.tangentChoice_spec A
    (HironakaActualPointLocalInitialValues.exists_tangent_from_good_record
      A B hhol hcl hB hmax hd V V' φ hrec x hx)

theorem anchored_original_contact_records
    (A : MarkedIdeal n X) (B : MarkedIdeal n X')
    (_hhol : ∀x g,A.ideal.mem x g → HolomorphicAt n g x) (hB : B.IsWellFormed)
    {V₀ : Opens X} {V₀' : Opens X'}
    {φ : CMfd.of (n := n) V₀ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V₀'}
    (hInitial : MarkedIdeal.pullback (Subtype.val : V₀ → X) A=
      MarkedIdeal.pullback φ (MarkedIdeal.pullback (Subtype.val : V₀' → X') B))
    {S : BlowupTower X Y} {T : BlowupTower X' Y'}
    {U : Opens Y} {U' : Opens Y'} {η} (H : Anchored V₀ V₀' φ S T U U' η)
    (Hbar : Generated (barMarked A) (barMarked B) S T U U' η) (f : X → ℂ) :
    let g:=transportedInitialFunction V₀ V₀' φ f
    contactMarkedKept A f S U=MarkedIdeal.pullback η (contactMarkedKept B g T U') := by
  have hbarA : ∀x g,(barMarked A).ideal.mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
  have hbarB := StepOneLowerDomain.isWellFormed_barMarked B hB
  have hsrc := holomorphic_geoTransformAlong (barMarked A) hbarA S
  have htgt := holomorphic_geoTransformAlong (barMarked B)
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hbarB.isCoherent hg) T
  have hrec := Hbar.whole_records hbarA hbarB
  have hCarrier := HironakaActualAnchoredStrictCarriers.Anchored.original_source_contact_carrier_traces
    H A B hInitial f
  exact HironakaActualCurrentStrictCarrierLocality.contact_record_from_whole_record
    (geoTransformAlong (barMarked A) S) (geoTransformAlong (barMarked B) T) hsrc htgt
    (strictAlong S (A.N∩{x | f x=0}))
    (strictAlong T (B.N∩{x | transportedInitialFunction V₀ V₀' φ f x=0}))
    U U' η hrec hCarrier

end
end Hironaka.HironakaActualAnchoredContactRecords
