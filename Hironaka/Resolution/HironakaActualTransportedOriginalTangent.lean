import Hironaka.Resolution.HironakaActualAnchoredContactRecords
import Hironaka.Resolution.HironakaActualOpenTangentDescent

/-! The SAME original source tangent, transported through the actual initial
comparison and extended by zero, is a genuine tangent on an actual target
open neighborhood. No global holomorphic extension or target tangent
certificate is supplied. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualTransportedOriginalTangent
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  RelativePrincipalizationSpan TangentDirectionAlong DerivativeIdealAlongEtale HomogenizedIdealAlong
  HironakaActualAnchoredStrictCarriers HironakaActualRawRecordPullbacks
variable {n : ℕ} {X X' : CMfd.{u} n}

theorem transported_original_tangent
    (A : MarkedIdeal n X) (B : MarkedIdeal n X')
    (hhol : ∀x g,A.ideal.mem x g → HolomorphicAt n g x) (hB : B.IsWellFormed)
    (V : Opens X) (V' : Opens X')
    (φ : CMfd.of (n := n) V ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V')
    (hrec : MarkedIdeal.pullback (Subtype.val : V → X) A=
      MarkedIdeal.pullback φ (MarkedIdeal.pullback (Subtype.val : V' → X') B))
    (O : Set X) (f : X → ℂ) (hf : IsTangentDirectionAlong A.N A.ideal A.d O f) :
    IsTangentDirectionAlong B.N B.ideal B.d
      ((Subtype.val : V' → X') '' ((φ.symm) ⁻¹' ((Subtype.val : V → X) ⁻¹' O)))
      (transportedInitialFunction V V' φ f) := by
  let AU:=MarkedIdeal.pullback (Subtype.val : V → X) A
  let BV:=MarkedIdeal.pullback (Subtype.val : V' → X') B
  have hBVcoh : BV.ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hB.isCoherent
  have hBVhol : ∀x g,BV.ideal.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hBVcoh hg
  have hinv : MarkedIdeal.pullback φ.symm AU=BV := by
    rw [show AU=MarkedIdeal.pullback φ BV from hrec]
    rw [marked_pullback_comp_hhol hBVhol φ.contMDiff φ.symm.contMDiff φ.apply_symm_apply]
    exact ContactCanonicalAlong.pullback_id BV hBVcoh
  have hfirst := ContactEquivalenceAlong.isTangentDirectionAlong_pullback
    (fun p : V => ⟨openInv V p,isLocalInverseAt_val V p⟩) hhol hf
  have hAUhol : ∀x g,AU.ideal.mem x g → HolomorphicAt n g x := by
    rw [show AU=MarkedIdeal.pullback φ BV from hrec]
    exact fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem
      (GermIdealPullbackCalculus.isCoherent_pullback φ.contMDiff hBVcoh) hg
  have hsecond := ContactEquivalenceAlong.isTangentDirectionAlong_pullback
    (fun p : V' => ⟨φ,isLocalInverseAt_of_inverse
      (fun _ => φ.symm.contMDiff.mdifferentiableAt (by simp))
      (fun _ => φ.contMDiff.mdifferentiableAt (by simp))
      φ.symm_apply_apply φ.apply_symm_apply p⟩) hAUhol hfirst
  have hN:=congrArg MarkedIdeal.N hinv
  have hI:=congrArg MarkedIdeal.ideal hinv
  have hd:=congrArg MarkedIdeal.d hinv
  change AU.d=BV.d at hd
  change IsTangentDirectionAlong ((MarkedIdeal.pullback φ.symm AU).N)
    ((MarkedIdeal.pullback φ.symm AU).ideal) AU.d
    ((φ.symm) ⁻¹' ((Subtype.val : V → X) ⁻¹' O))
    ((f ∘ (Subtype.val : V → X)) ∘ φ.symm) at hsecond
  rw [hN,hI,hd] at hsecond
  have hfun : (f ∘ (Subtype.val : V → X)) ∘ φ.symm=
      transportedInitialFunction V V' φ f ∘ (Subtype.val : V' → X') := by
    funext p
    simp only [Function.comp_apply,transportedInitialFunction,dif_pos p.property]
  rw [hfun] at hsecond
  exact HironakaActualOpenTangentDescent.isTangentDirectionAlong_of_open_pullback
    B.N hB.isClosedSubmanifold_N B.ideal hB.isCoherent B.d V'
    ((φ.symm) ⁻¹' ((Subtype.val : V → X) ⁻¹' O)) _ hsecond

theorem transported_original_chosen_tangent_from_good_record
    (A : MarkedIdeal n X) (B : MarkedIdeal n X')
    (hhol : ∀x g,A.ideal.mem x g → HolomorphicAt n g x)
    (hcl : ∀x g,IsInSpanAt (n := n) (A.ideal.mem x) x g → A.ideal.mem x g)
    (hB : B.IsWellFormed) (hmax : IsMaximalOrderAlong B.N B.ideal B.d)
    (hd : 1≤A.d) (V : Opens X) (V' : Opens X')
    (φ : CMfd.of (n := n) V ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V')
    (hrec : MarkedIdeal.pullback (Subtype.val : V → X) A=
      MarkedIdeal.pullback φ (MarkedIdeal.pullback (Subtype.val : V' → X') B))
    (x : V) (hx : x.val∈A.cosupp) :
    let f:=(StepOneValue.tangentChoice A x.val).2
    let O:=(StepOneValue.tangentChoice A x.val).1
    let O':= (Subtype.val : V' → X') '' ((φ.symm) ⁻¹' ((Subtype.val : V → X) ⁻¹' (O : Set X)))
    (φ x).val∈O' ∧ IsTangentDirectionAlong B.N B.ideal B.d O'
      (transportedInitialFunction V V' φ f) := by
  obtain ⟨hxO,hf⟩:=HironakaActualAnchoredContactRecords.original_chosen_tangent_from_good_record
    A B hhol hcl hB hmax hd V V' φ hrec x hx
  dsimp only
  refine ⟨⟨φ x,?_,rfl⟩,transported_original_tangent A B hhol hB V V' φ hrec _ _ hf⟩
  change (φ.symm (φ x)).val∈(StepOneValue.tangentChoice A x.val).1
  simpa only [φ.symm_apply_apply] using hxO

end
end Hironaka.HironakaActualTransportedOriginalTangent
