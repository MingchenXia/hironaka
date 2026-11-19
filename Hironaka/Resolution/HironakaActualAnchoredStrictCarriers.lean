import Hironaka.Resolution.HironakaActualAnchoredCurrentHistories

/-! Arbitrary ORIGINAL strict carriers, including the actual globally chosen
tangent's arbitrary extension, propagate along anchored different histories.
The target function is internally produced from the actual initial map.
No global analyticity or desired post-carrier identity is supplied. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualAnchoredStrictCarriers
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism HironakaActualGeneratedCurrentHistories
  HironakaActualAnchoredCurrentHistories CoefficientIdealRestriction HomogenizedGlueingTower
variable {n : ℕ} {X X' Y Y' : CMfd.{u} n}

private theorem next_strict_trace {Z Z' : CMfd.{u} n}
    {C : Set Y} {C' : Set Y'} {π : Z → Y} {π' : Z' → Y'}
    (hπ : IsBlowupAlong n C π) (hπ' : IsBlowupAlong n C' π')
    (U : Opens Y) (U' : Opens Y')
    (η : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U')
    (hC : η ⁻¹' ((Subtype.val : U' → Y') ⁻¹' C')=(Subtype.val : U → Y) ⁻¹' C)
    (N : Set Y) (N' : Set Y')
    (hN : (Subtype.val : U → Y) ⁻¹' N=η ⁻¹' ((Subtype.val : U' → Y') ⁻¹' N')) :
    (Subtype.val : BlowupBiholomorphismLift.preOpen hπ U → Z) ⁻¹'
      BlowupStrictSubmanifold.geoStrictTransform π C N=
    (nextComparison hπ hπ' U U' η hC) ⁻¹'
      ((Subtype.val : BlowupBiholomorphismLift.preOpen hπ' U' → Z') ⁻¹'
        BlowupStrictSubmanifold.geoStrictTransform π' C' N') := by
  let V:=BlowupBiholomorphismLift.preOpen hπ U
  let V':=BlowupBiholomorphismLift.preOpen hπ' U'
  let χ:=nextComparison hπ hπ' U U' η hC
  change (Subtype.val : V → Z) ⁻¹' closure (π ⁻¹' (N\C))=
    χ ⁻¹' ((Subtype.val : V' → Z') ⁻¹' closure (π' ⁻¹' (N'\C')))
  have hs : (Subtype.val : V → Z) ⁻¹' closure (π ⁻¹' (N\C))=
      closure ((Subtype.val : V → Z) ⁻¹' (π ⁻¹' (N\C))) :=
    V.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage continuous_subtype_val _
  have ht : (Subtype.val : V' → Z') ⁻¹' closure (π' ⁻¹' (N'\C'))=
      closure ((Subtype.val : V' → Z') ⁻¹' (π' ⁻¹' (N'\C'))) :=
    V'.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage continuous_subtype_val _
  have hχ : χ ⁻¹' closure ((Subtype.val : V' → Z') ⁻¹' (π' ⁻¹' (N'\C')))=
      closure (χ ⁻¹' ((Subtype.val : V' → Z') ⁻¹' (π' ⁻¹' (N'\C')))) :=
    χ.toHomeomorph.preimage_closure _
  rw [hs,ht,hχ]
  apply congrArg closure
  ext z
  simp only [mem_preimage,Set.mem_sdiff]
  rw [nextComparison_square hπ hπ' U U' η hC z]
  let p : U:=⟨π z.val,z.property⟩
  have hn : π z.val∈N ↔ (η p).val∈N' :=
    Iff.of_eq (congrArg (fun L : Set U => p∈L) hN)
  have hc : π z.val∈C ↔ (η p).val∈C' :=
    (Iff.of_eq (congrArg (fun L : Set U => p∈L) hC)).symm
  exact and_congr hn (not_congr hc)

theorem Anchored.strict_carrier_traces {V₀ : Opens X} {V₀' : Opens X'} {φ}
    {S : BlowupTower X Y} {T : BlowupTower X' Y'}
    {U : Opens Y} {U' : Opens Y'} {η} (H : Anchored V₀ V₀' φ S T U U' η)
    (K : Set X) (K' : Set X')
    (hInitial : (Subtype.val : V₀ → X) ⁻¹' K=φ ⁻¹' ((Subtype.val : V₀' → X') ⁻¹' K')) :
    (Subtype.val : U → Y) ⁻¹' strictAlong S K=
      η ⁻¹' ((Subtype.val : U' → Y') ⁻¹' strictAlong T K') := by
  induction H with
  | initial => exact hInitial
  | @shrink Y Y' S T U U' η H V V' hV hV' htr ih =>
    ext z
    exact Iff.of_eq (congrArg (fun L : Set U => (⟨z.val,hV z.property⟩ : U)∈L) ih)
  | @step Y Y' Z Z' S T U U' η H C C' π π' hπ hπ' hC ih =>
    exact next_strict_trace hπ hπ' U U' η hC (strictAlong S K) (strictAlong T K') ih

def transportedInitialFunction (V₀ : Opens X) (V₀' : Opens X')
    (φ : CMfd.of (n := n) V₀ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V₀')
    (f : X → ℂ) : X' → ℂ := by
  classical
  exact fun x => if hx : x∈V₀' then f (φ.symm ⟨x,hx⟩).val else 0

theorem transportedInitialFunction_apply (V₀ : Opens X) (V₀' : Opens X')
    (φ : CMfd.of (n := n) V₀ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V₀')
    (f : X → ℂ) (x : V₀) : transportedInitialFunction V₀ V₀' φ f (φ x).val=f x.val := by
  unfold transportedInitialFunction
  rw [dif_pos (φ x).property]
  exact congrArg (fun y : V₀ => f y.val) (φ.symm_apply_apply x)

theorem Anchored.original_source_contact_carrier_traces {V₀ : Opens X} {V₀' : Opens X'} {φ}
    {S : BlowupTower X Y} {T : BlowupTower X' Y'}
    {U : Opens Y} {U' : Opens Y'} {η} (H : Anchored V₀ V₀' φ S T U U' η)
    (A : MarkedIdeal n X) (B : MarkedIdeal n X')
    (hInitial : MarkedIdeal.pullback (Subtype.val : V₀ → X) A=
      MarkedIdeal.pullback φ (MarkedIdeal.pullback (Subtype.val : V₀' → X') B)) (f : X → ℂ) :
    let g:=transportedInitialFunction V₀ V₀' φ f
    (Subtype.val : U → Y) ⁻¹' strictAlong S (A.N∩{x | f x=0})=
      η ⁻¹' ((Subtype.val : U' → Y') ⁻¹' strictAlong T (B.N∩{x | g x=0})) := by
  have hN:=congrArg MarkedIdeal.N hInitial
  dsimp only
  apply Anchored.strict_carrier_traces H (A.N∩{x | f x=0})
    (B.N∩{x | transportedInitialFunction V₀ V₀' φ f x=0})
  ext x
  have hnx : x.val∈A.N ↔ (φ x).val∈B.N :=
    Iff.of_eq (congrArg (fun L : Set V₀ => x∈L) hN)
  simp only [mem_preimage,mem_inter_iff,mem_ofPred_eq]
  rw [transportedInitialFunction_apply]
  exact and_congr hnx Iff.rfl

end
end Hironaka.HironakaActualAnchoredStrictCarriers
