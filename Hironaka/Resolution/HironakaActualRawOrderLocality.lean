import Hironaka.Resolution.HironakaActualRawRecordPullbacks

/-! Raw germ-span locality of actual nonmonomial orders. This is used on
noncanonical source histories whose regularity is available only locally. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualRawOrderLocality
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
open MarkedIdealBiholomorphism RelativePrincipalizationSpan GermIdealPullbackCalculus
open DerivativeIdealAlongEtale InvertibleIdealQuotient RestrictedIdealExtension RestrictedIdealQuotient
open NonmonomialOrderLocal NonmonomialOrderTail CompanionRebase CompanionReductionAlong MonomialPartAlong
open GermIdealOrder GermIdealTotalTransform IdealWeightPowers
open HironakaActualRawRecordPullbacks
noncomputable section
variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem colon_span_closed {I L : GermIdeal n X} {N : Set X}
 (hL : ∀x g,L.mem x g → HolomorphicAt n g x) {x : X} {f : X → ℂ}
 (hf : IsInSpanAt (n := n) ((colonAlong n N I L).mem x) x f) :
 (colonAlong n N I L).mem x f := by
 obtain ⟨hfhol,K,s,a,hs,ha,hsum⟩ := hf
 refine ⟨hfhol,fun g hg => ?_⟩
 refine restrictOn_of_isInSpanAt (𝔞 := I) ⟨(hL _ _ hg).mul hfhol,K,
   fun i w => g w*s i w,a,fun i => (hs i).2 g hg,ha,?_⟩
 filter_upwards [hsum] with w hw
 show g w*f w = ∑i,a i w*(g w*s i w)
 rw [hw,Finset.mul_sum]
 exact Finset.sum_congr rfl fun i _ => by ring

/-- Actual raw transforms remain closed under holomorphic germ spans.
At a nonempty prefix this follows from the defining colon, without source
coherence or admissibility. -/
theorem span_closed_geoTransformAlong (A : MarkedIdeal n X)
 (hA : ∀x g,IsInSpanAt (n := n) (A.ideal.mem x) x g → A.ideal.mem x g) :
 ∀{Y : CMfd.{u} n} (T : BlowupTower X Y) x g,
   IsInSpanAt (n := n) ((geoTransformAlong A T).ideal.mem x) x g →
     (geoTransformAlong A T).ideal.mem x g
 | _,.refl,x,g,hg => hA x g hg
 | _,.step T C π hπ,x,g,hg => by
   have hDen := isCoherent_idealPow
     (isCoherent_pullback hπ.contMDiff
       (BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ))
     (geoTransformAlong A T).d
   exact colon_span_closed
     (fun _ _ h => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hDen h) hg

/-- Every nonmonomial order threshold of a raw germ-span-closed record
commutes with an actual local biholomorphism. -/
theorem ordGe_pullback_of_local {f : Y → X}
 (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f)
 (hloc : ∀y : Y,∃g : X → Y,IsLocalInverseAt n f g y)
 (J : MarkedIdeal n X)
 (hhol : ∀x g,J.ideal.mem x g → HolomorphicAt n g x)
 (hcl : ∀x g,IsInSpanAt (n := n) (J.ideal.mem x) x g → J.ideal.mem x g)
 (q : ℕ) : ordGe (MarkedIdeal.pullback f J) q = f ⁻¹' ordGe J q := by
 have hp := HironakaActualRawCompanionNaturality.pullback_companionOf hf hloc J hhol hcl J.d
 have hi := congrArg MarkedIdeal.ideal hp
 have hNN : GermIdeal.pullback (m := n) f (nmPart J) = nmPart (MarkedIdeal.pullback f J) := by
   simpa only [MarkedIdeal.pullback,companionOf,companionAlong,lt_self_iff_false,if_false] using hi
 change cosupport n (f ⁻¹' J.N) (nmPart (MarkedIdeal.pullback f J)) q = _
 rw [←hNN]
 exact MonomialPartEtale.cosupport_pullback_of_local hloc
   (fun (x : X) (g : X → ℂ) (hg : (nmPart J).mem x g) => hg.1) J.N q

theorem nmOrd_pullback_of_local {f : Y → X}
 (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f)
 (hloc : ∀y : Y,∃g : X → Y,IsLocalInverseAt n f g y)
 (J : MarkedIdeal n X)
 (hhol : ∀x g,J.ideal.mem x g → HolomorphicAt n g x)
 (hcl : ∀x g,IsInSpanAt (n := n) (J.ideal.mem x) x g → J.ideal.mem x g)
 (y : Y) : nmOrd (MarkedIdeal.pullback f J) y = nmOrd J (f y) :=
 nmOrd_congr fun q => Iff.of_eq (congrArg (fun S : Set Y => y∈S)
   (ordGe_pullback_of_local hf hloc J hhol hcl q))

/-- Entire current-record comparison derives the raw source order and
cosupport comparison; neither assertion is an incoming certificate. -/
theorem order_and_cosupp_from_records (A : MarkedIdeal n X) (B : MarkedIdeal n Y)
 (hA : ∀x g,A.ideal.mem x g → HolomorphicAt n g x)
 (hAc : ∀x g,IsInSpanAt (n := n) (A.ideal.mem x) x g → A.ideal.mem x g)
 (hB : ∀x g,B.ideal.mem x g → HolomorphicAt n g x)
 (hBc : ∀x g,IsInSpanAt (n := n) (B.ideal.mem x) x g → B.ideal.mem x g)
 (U : Opens X) (U' : Opens Y)
 (η : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U')
 (hrec : MarkedIdeal.pullback (Subtype.val : U → X) A =
   MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Y) B))
 (z : U) :
   nmOrd A z.val=nmOrd B (η z).val ∧ (z.val∈A.cosupp ↔ (η z).val∈B.cosupp) := by
 let BU : MarkedIdeal n (CMfd.of (n := n) U') := MarkedIdeal.pullback (Subtype.val : U' → Y) B
 have hBU : ∀x g,BU.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
 have hBUc : ∀x g,IsInSpanAt (n := n) (BU.ideal.mem x) x g → BU.ideal.mem x g := by
   intro x g hg
   dsimp only [BU,MarkedIdeal.pullback,GermIdeal.pullback] at hg ⊢
   exact IsInSpanAt.trans (fun _ hs => hs) hg
 have hS := nmOrd_pullback_of_local (X := X) (Y := CMfd.of (n := n) U)
   contMDiff_subtype_val (fun p => ⟨openInv U p,isLocalInverseAt_val U p⟩) A hA hAc z
 have hM := congrArg (fun Q : MarkedIdeal n (CMfd.of (n := n) U) => nmOrd Q z) hrec
 have hT₁ := nmOrd_pullback_of_local (X := CMfd.of (n := n) U') (Y := CMfd.of (n := n) U)
   η.contMDiff (fun p => ⟨η.symm,isLocalInverseAt_diffeo η p⟩) BU hBU hBUc z
 have hT₂ := nmOrd_pullback_of_local (X := Y) (Y := CMfd.of (n := n) U')
   contMDiff_subtype_val (fun p => ⟨openInv U' p,isLocalInverseAt_val U' p⟩) B hB hBc (η z)
 refine ⟨hS.symm.trans (hM.trans (hT₁.trans hT₂)),?_⟩
 have hc := congrArg MarkedIdeal.cosupp hrec
 rw [MarkedIdealRestrictOpen.cosupp_pullback_val A hA U,
   MarkedIdealBiholomorphism.MarkedIdeal.cosupp_pullback η.contMDiff η.symm.contMDiff
     η.apply_symm_apply η.symm_apply_apply BU hBU,
   MarkedIdealRestrictOpen.cosupp_pullback_val B hB U'] at hc
 exact Iff.of_eq (congrArg (fun S : Set U => z∈S) hc)

end
end Hironaka.HironakaActualRawOrderLocality
