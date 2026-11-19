import Hironaka.Resolution.HironakaActualNoncanonicalAnalyticTransformLocality
import Hironaka.Resolution.HironakaActualNonregularCoefficientNaturality

/-! Current-window locality of actual strict carriers, including a chosen
contact function that need not be holomorphic outside its original good open.
No global analyticity, admissibility or canonicality is required for the carrier. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualCurrentStrictCarrierLocality
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
open MarkedIdealBiholomorphism MarkedIdealRestrictOpen GermIdealPullbackCalculus
open DerivativeIdealAlongEtale HironakaSharpActualCurrentOpenLowerReferences
open HomogenizedGlueingTower HironakaActualNonregularCoefficientNaturality
open HomogenizedIdealAlong CoefficientIdealRestriction
noncomputable section
variable {n : ℕ} {X Y Z Z' : CMfd.{u} n}

/-- The SAME original strict carrier has equal literal traces on the current
comparison, for an arbitrary initial set. Chosen-contact extensions are covered
without falsely asserting global analyticity of their zero sets. -/
theorem current_strict_carrier_trace
 (T : BlowupTower X Y) (K : Set X)
 {C C' : Set Y} {π : Z → Y} {π' : Z' → Y}
 (hπ : IsBlowupAlong n C π) (hπ' : IsBlowupAlong n C' π') (V : Opens Y)
 (hC : (Subtype.val : V → Y) ⁻¹' C=(Subtype.val : V → Y) ⁻¹' C')
 (η : stepWindow hπ V ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ stepWindow hπ' V)
 (hsq : ∀ z : stepWindow hπ V,π' (η z).val=π z.val) :
 (Subtype.val : stepWindow hπ V → Z) ⁻¹' strictAlong (.step T C π hπ) K =
   η ⁻¹' ((Subtype.val : stepWindow hπ' V → Z') ⁻¹' strictAlong (.step T C' π' hπ') K) := by
 let U := stepWindow hπ V
 let U' := stepWindow hπ' V
 change (Subtype.val : U → Z) ⁻¹' closure (π ⁻¹' (strictAlong T K \ C)) =
   η ⁻¹' ((Subtype.val : U' → Z') ⁻¹' closure (π' ⁻¹' (strictAlong T K \ C')))
 have hclS : (Subtype.val : U → Z) ⁻¹' closure (π ⁻¹' (strictAlong T K \ C)) =
     closure ((Subtype.val : U → Z) ⁻¹' (π ⁻¹' (strictAlong T K \ C))) :=
   U.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage continuous_subtype_val _
 have hclT : (Subtype.val : U' → Z') ⁻¹' closure (π' ⁻¹' (strictAlong T K \ C')) =
     closure ((Subtype.val : U' → Z') ⁻¹' (π' ⁻¹' (strictAlong T K \ C'))) :=
   U'.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage continuous_subtype_val _
 have hηcl : η ⁻¹' closure ((Subtype.val : U' → Z') ⁻¹' (π' ⁻¹' (strictAlong T K \ C'))) =
     closure (η ⁻¹' ((Subtype.val : U' → Z') ⁻¹' (π' ⁻¹' (strictAlong T K \ C')))) :=
   η.toHomeomorph.preimage_closure _
 rw [hclS,hclT,hηcl]
 apply congrArg closure
 ext z
 simp only [mem_preimage,Set.mem_sdiff]
 rw [hsq z]
 have hcent : π z.val∈C ↔ π z.val∈C' :=
   Iff.of_eq (congrArg (fun S : Set V => (⟨π z.val,z.property⟩ : V)∈S) hC)
 exact and_congr Iff.rfl (not_congr hcent)

/-- Raw coefficient-ideal algebra transports the whole coefficient marked
record along a supplied whole-record comparison, without source regularity. -/
theorem coefficient_record_from_whole_record
 (A : MarkedIdeal n Z) (B : MarkedIdeal n Z')
 (hA : ∀ x g,A.ideal.mem x g → HolomorphicAt n g x)
 (hB : ∀ x g,B.ideal.mem x g → HolomorphicAt n g x)
 (U : Opens Z) (U' : Opens Z')
 (η : U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ U')
 (hrec : MarkedIdeal.pullback (Subtype.val : U → Z) A=
   MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') B)) :
 MarkedIdeal.pullback (Subtype.val : U → Z) (coeffMarkedAlong A)=
   MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') (coeffMarkedAlong B)) := by
 have hAS := pullback_coeffMarkedAlong contMDiff_subtype_val
   (fun z => ⟨openInv U z,isLocalInverseAt_val U z⟩) A hA
 have hBT := pullback_coeffMarkedAlong contMDiff_subtype_val
   (fun z => ⟨openInv U' z,isLocalInverseAt_val U' z⟩) B hB
 have hη := pullback_coeffMarkedAlong η.contMDiff
   (fun z => ⟨η.symm,⟨Eventually.of_forall (fun p => (η.contMDiff p).mdifferentiableAt (by simp)),
     Eventually.of_forall (fun p => (η.symm.contMDiff p).mdifferentiableAt (by simp)),
     Eventually.of_forall η.symm_apply_apply,Eventually.of_forall η.apply_symm_apply⟩⟩)
   (MarkedIdeal.pullback (Subtype.val : U' → Z') B) (fun _ _ hg => hg.1)
 rw [hAS,hrec,←hη,←hBT]

/-- The full coefficient/contact record transports when its actual carrier
trace does. In particular the previous theorem supplies the carrier premise
for the same original chosen tangent contact at a fresh inner reference. -/
theorem contact_record_from_whole_record
 (A : MarkedIdeal n Z) (B : MarkedIdeal n Z')
 (hA : ∀ x g,A.ideal.mem x g → HolomorphicAt n g x)
 (hB : ∀ x g,B.ideal.mem x g → HolomorphicAt n g x)
 (K : Set Z) (K' : Set Z') (U : Opens Z) (U' : Opens Z')
 (η : U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ U')
 (hrec : MarkedIdeal.pullback (Subtype.val : U → Z) A=
   MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') B))
 (hK : (Subtype.val : U → Z) ⁻¹' K=η ⁻¹' ((Subtype.val : U' → Z') ⁻¹' K')) :
 MarkedIdeal.pullback (Subtype.val : U → Z) (withN (coeffMarkedAlong A) K)=
   MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z')
     (withN (coeffMarkedAlong B) K')) := by
 have hc := coefficient_record_from_whole_record A B hA hB U U' η hrec
 have hE := congrArg MarkedIdeal.E hc
 have hI := congrArg MarkedIdeal.ideal hc
 have hD := congrArg MarkedIdeal.d hc
 exact MarkedIdealOperationsTransform.MarkedIdeal.ext_of hK hE hI hD
end
end Hironaka.HironakaActualCurrentStrictCarrierLocality
