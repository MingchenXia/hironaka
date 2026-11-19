import Hironaka.Resolution.HironakaActualRawCompanionNaturality
import Hironaka.Resolution.HironakaActualFreshRecursiveValues
import Hironaka.Invariant.StepOneTangentChange
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualPointLocalInitialValues
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
open RelativePrincipalizationSpan GermIdealPullbackCalculus InvertibleIdealQuotient
open GermIdealOrder DerivativeIdealAlongEtale StepOneValue StepOneValueMasked
open CompanionRebase CompanionReductionAlong MonomialPartAlong NonmonomialOrderLocal NonmonomialOrderTail
open MarkedIdealRestrictOpen
open ResolutionInvariantSpec (IsInvDomain)
noncomputable section
variable {n : ℕ} {X Y : CMfd.{u} n}

section RawMembership
variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
private theorem mem_congr_span_closed {I : GermIdeal n M}
 (hhol : ∀ x g,I.mem x g → HolomorphicAt n g x)
 (hcl : ∀ x g,IsInSpanAt (n := n) (I.mem x) x g → I.mem x g)
 {x : M} {f g : M → ℂ} (hf : I.mem x f) (heq : f =ᶠ[𝓝 x] g) : I.mem x g :=
 hcl _ _ (DerivativeIdeal.isInSpanAt_congr (isInSpanAt_self hf (hhol _ _ hf)) heq)

omit [IsComplexManifold n M] in
private theorem raw_mem_pullback_val_iff {I : GermIdeal n M}
 (hhol : ∀ x g,I.mem x g → HolomorphicAt n g x)
 (hcl : ∀ x g,IsInSpanAt (n := n) (I.mem x) x g → I.mem x g)
 (U : Opens M) {x : U} {f : U → ℂ} :
 (GermIdeal.pullback (m := n) (Subtype.val : U → M) I).mem x f ↔ I.mem x.val (extendOpens U f) := by
 have hh : (GermIdeal.pullback (m := n) (Subtype.val : U → M) I).mem x f ↔
   IsInSpanAt (n := n) (I.mem x.val) x.val (extendOpens U f) := isInSpanAt_comp_val_iff U
 exact hh.trans ⟨hcl _ _,fun h => isInSpanAt_self h (hhol _ _ h)⟩

end RawMembership
private def InitialLocality (hn : 0<n) (q : ℕ) : Prop :=
 ∀ {X : CMfd.{u} n} (J : MarkedIdeal n X),
   (∀ x g,J.ideal.mem x g → HolomorphicAt n g x) →
   (∀ x g,IsInSpanAt (n := n) (J.ideal.mem x) x g → J.ideal.mem x g) →
   ∀ (U : Opens X),IsInvDomain (M := CMfd.of (n := n) U) q (MarkedIdeal.pullback (n := n) (Subtype.val : U → X) J) →
   ∀ x : U,x.val∈J.cosupp →
     (CanonicalCentres.invFamily hn q).inv J .refl x.val=
       (CanonicalCentres.invFamily hn q).inv (X := CMfd.of (n := n) U) (Y := CMfd.of (n := n) U)
         (MarkedIdeal.pullback (n := n) (Subtype.val : U → X) J) .refl x

private theorem initial_zero (hn : 0<n) : InitialLocality.{u} hn 0 := by
 intro X J hhol hcl U hdom x hx
 rfl

private theorem lowerMarkedM_hhol (J : MarkedIdeal n X) (s : ℕ) (T : BlowupTower X Y) (x : Y) :
 ∀ y g,(StepOneValueMasked.lowerMarkedM J s T x).ideal.mem y g → HolomorphicAt n g y := by
 cases s <;> intro y g hg <;> exact hg.1

private theorem lowerMarkedM_span_closed (J : MarkedIdeal n X) (s : ℕ) (T : BlowupTower X Y) (x : Y) :
 ∀ y g,IsInSpanAt (n := n) ((StepOneValueMasked.lowerMarkedM J s T x).ideal.mem y) y g →
   (StepOneValueMasked.lowerMarkedM J s T x).ideal.mem y g := by
 cases s <;> intro y g hg
 all_goals
   dsimp only [StepOneValueMasked.lowerMarkedM,StepOneValueMasked.lowerMarkedB,StepOneValue.lowerMarked,
     MarkedIdeal.pullback,GermIdeal.pullback] at hg ⊢
   exact IsInSpanAt.trans (fun _ hs => hs) hg

private theorem raw_ordGe_pullback_val
 (J : MarkedIdeal n X)
 (hhol : ∀ x g,J.ideal.mem x g → HolomorphicAt n g x)
 (hcl : ∀ x g,IsInSpanAt (n := n) (J.ideal.mem x) x g → J.ideal.mem x g)
 (U : Opens X) (q : ℕ) :
 ordGe (M := CMfd.of (n := n) U) (MarkedIdeal.pullback (n := n) (Subtype.val : U → X) J) q=
   (Subtype.val : U → X) ⁻¹' ordGe J q := by
 have hp := HironakaActualRawCompanionNaturality.pullback_companionOf (X := X) (Y := CMfd.of (n := n) U)
   contMDiff_subtype_val (fun y => ⟨openInv U y,isLocalInverseAt_val U y⟩) J hhol hcl J.d
 have hi := congrArg MarkedIdeal.ideal hp
 have hNN : GermIdeal.pullback (m := n) (Subtype.val : U → X) (nmPart J)=
     nmPart (M := CMfd.of (n := n) U) (MarkedIdeal.pullback (n := n) (Subtype.val : U → X) J) := by
   simpa only [MarkedIdeal.pullback,companionOf,companionAlong,lt_self_iff_false,if_false] using hi
 change cosupport n ((Subtype.val : U → X) ⁻¹' J.N)
   (nmPart (M := CMfd.of (n := n) U) (MarkedIdeal.pullback (n := n) (Subtype.val : U → X) J)) q=_
 rw [←hNN]
 have hh : ∀ x g,(nmPart J).mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
 exact MonomialPartEtale.cosupport_pullback_of_local
   (fun y => ⟨openInv U y,isLocalInverseAt_val U y⟩) hh J.N q

private theorem raw_nmOrd_pullback_val
 (J : MarkedIdeal n X)
 (hhol : ∀ x g,J.ideal.mem x g → HolomorphicAt n g x)
 (hcl : ∀ x g,IsInSpanAt (n := n) (J.ideal.mem x) x g → J.ideal.mem x g)
 (U : Opens X) (x : U) :
 nmOrd (M := CMfd.of (n := n) U) (MarkedIdeal.pullback (n := n) (Subtype.val : U → X) J) x=nmOrd J x.val :=
 nmOrd_congr (fun q => Iff.of_eq (congrArg (fun S : Set U => x∈S) (raw_ordGe_pullback_val J hhol hcl U q)))
section Compose
variable {P Q R : Type u} [TopologicalSpace P] [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P]
 [TopologicalSpace Q] [ChartedSpace (ComplexModel n) Q] [IsComplexManifold n Q]
 [TopologicalSpace R] [ChartedSpace (ComplexModel n) R] [IsComplexManifold n R]
private theorem pullback_comp_hhol {f : P → R} {g : Q → P}
 (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
 (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
 {𝔞 : GermIdeal n R} (hhol : ∀ x v, 𝔞.mem x v → HolomorphicAt n v x) :
 GermIdeal.pullback (m := n) (f ∘ g) 𝔞 =
   GermIdeal.pullback (m := n) g (GermIdeal.pullback (m := n) f 𝔞) := by
  refine GermIdeal.ext (funext fun z => funext fun v => propext ⟨fun hv => ?_, fun hv => ?_⟩)
  · have hfat : ∀ᶠ y in 𝓝 (g z),
        ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f y :=
      Eventually.of_forall fun y => hf.contMDiffAt
    refine GermIdeal.mem_pullback_iff.mpr
      (IsInSpanAt.mono ?_ (GermIdeal.mem_pullback_iff.mp hv))
    rintro u ⟨c, hc, rfl⟩
    have hchol : HolomorphicAt n c (f (g z)) :=
      hhol _ _ hc
    have hcfhol : HolomorphicAt n (c ∘ f) (g z) := hchol.comp_contMDiff hfat
    have hcf : (GermIdeal.pullback (m := n) f 𝔞).mem (g z) (c ∘ f) :=
      GermIdeal.mem_pullback_iff.mpr (isInSpanAt_of_eq_mul ⟨c, hc, rfl⟩ hcfhol
        (holomorphicAt_const 1) (Eventually.of_forall fun _ => (one_mul _).symm))
    exact ⟨c ∘ f, hcf, rfl⟩
  · refine GermIdeal.mem_pullback_iff.mpr
      (IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hv))
    rintro u ⟨c, hc, rfl⟩
    refine IsInSpanAt.mono ?_
      (isInSpanAt_comp hg (GermIdeal.mem_pullback_iff.mp hc))
    rintro u' ⟨σ, ⟨d, hd, rfl⟩, rfl⟩
    exact ⟨d, hd, rfl⟩

private theorem marked_pullback_comp_hhol {J : MarkedIdeal n R}
 (hhol : ∀ x v, J.ideal.mem x v → HolomorphicAt n v x) {a : P → R} {b : Q → P} {d : Q → R}
 (ha : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ a)
 (hb : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ b) (h : ∀ q,a (b q)=d q) :
 MarkedIdeal.pullback b (MarkedIdeal.pullback a J) = MarkedIdeal.pullback d J := by
 have hfun : a ∘ b = d := funext h
 refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ ?_ ?_ rfl
 · show b ⁻¹' (a ⁻¹' J.N)=d ⁻¹' J.N
   rw [←preimage_comp,hfun]
 · show (J.E.map (a ⁻¹' ·)).map (b ⁻¹' ·)=J.E.map (d ⁻¹' ·)
   rw [List.map_map]
   refine List.map_congr_left fun S _ => ?_
   show b ⁻¹' (a ⁻¹' S)=d ⁻¹' S
   rw [←preimage_comp,hfun]
 · show GermIdeal.pullback (m := n) b (GermIdeal.pullback (m := n) a J.ideal)=GermIdeal.pullback (m := n) d J.ideal
   rw [←pullback_comp_hhol ha hb hhol,hfun]
end Compose

open CoefficientIdealRestriction HomogenizedIdealAlong HomogenizedGlueingTower ContactEquivalenceAlong
open MarkedIdealOperationsAlong.MarkedIdeal

private def swapNested (O U : Opens X) :
 MaxLocusLocal.nestedOpens O U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ MaxLocusLocal.nestedOpens U O :=
 (MaxLocusLocal.nestedDiffeo O (MaxLocusLocal.nestedOpens O U) (O ⊓ U)
   (fun q => ⟨fun h => ⟨q.property,h⟩,fun h => h.2⟩) (fun _ h => h.1)).trans
 (MaxLocusLocal.nestedDiffeo U (MaxLocusLocal.nestedOpens U O) (O ⊓ U)
   (fun q => ⟨fun h => ⟨h,q.property⟩,fun h => h.1⟩) (fun _ h => h.2)).symm

private theorem original_chosen_contact_lower_good_domain
 (q : ℕ) (J : MarkedIdeal n X)
 (hhol : ∀ x g,J.ideal.mem x g → HolomorphicAt n g x)
 (U : Opens X)
 (hgood : IsInvDomain (M := CMfd.of (n := n) U) (q+1) (MarkedIdeal.pullback (n := n) (Subtype.val : U → X) J))
 (x : X)
 (hu : TangentDirectionAlong.IsTangentDirectionAlong J.N J.ideal J.d
   (tangentChoice J x).1 (tangentChoice J x).2) :
 IsInvDomain (M := CMfd.of (n := n) (MaxLocusLocal.nestedOpens (maskB J (.refl : BlowupTower X X) x) U)) q
   (MarkedIdeal.pullback (n := n) (Subtype.val : MaxLocusLocal.nestedOpens (maskB J (.refl : BlowupTower X X) x) U → maskB J (.refl : BlowupTower X X) x)
     (StepOneValueMasked.lowerMarkedB J (.refl : BlowupTower X X) x)) := by
 let JU : MarkedIdeal n (CMfd.of (n := n) U) := MarkedIdeal.pullback (n := n) (Subtype.val : U → X) J
 let O : Opens X := maskB J (.refl : BlowupTower X X) x
 let W := MaxLocusLocal.nestedOpens U O
 let G := MaxLocusLocal.nestedOpens O U
 let u : X → ℂ := (tangentChoice J x).2
 let uU : U → ℂ := u∘Subtype.val
 let Uu : Opens U := ⟨(Subtype.val : U → X) ⁻¹' (tangentChoice J x).1,hu.isOpen.preimage continuous_subtype_val⟩
 have huU : TangentDirectionAlong.IsTangentDirectionAlong JU.N JU.ideal JU.d Uu uU :=
   ContactEquivalenceAlong.isTangentDirectionAlong_pullback
     (fun y => ⟨openInv U y,isLocalInverseAt_val U y⟩) hhol hu
 have hhBar : ∀ y g,(barMarked J).ideal.mem y g → HolomorphicAt n g y := fun _ _ hg => hg.1
 have hbar : MarkedIdeal.pullback (n := n) (Subtype.val : U → X) (barMarked J)=barMarked JU :=
   HironakaActualNonregularCoefficientNaturality.pullback_coeff_homMarkedAlong contMDiff_subtype_val
     (fun y => ⟨openInv U y,isLocalInverseAt_val U y⟩) J hhol
 have hCoeff : MarkedIdeal.pullback (n := n) (Subtype.val : U → X) (coeffMarkedAlong (barMarked J))=
     coeffMarkedAlong (barMarked JU) := by
   rw [HironakaActualNonregularCoefficientNaturality.pullback_coeffMarkedAlong contMDiff_subtype_val
     (fun y => ⟨openInv U y,isLocalInverseAt_val U y⟩) (barMarked J) hhBar,hbar]
 have hZdict : CodimOneSupportAlong.codimOnePartAlong (barMarked JU).N (barMarked JU).ideal (barMarked JU).d=
     (Subtype.val : U → X) ⁻¹' CodimOneSupportAlong.codimOnePartAlong (barMarked J).N (barMarked J).ideal (barMarked J).d := by
   have hc := CodimOnePartCanonical.codimOnePartAlong_pullback_val U (N := (barMarked J).N) hhBar (barMarked J).d
   change CodimOneSupportAlong.codimOnePartAlong (MarkedIdeal.pullback (n := n) (Subtype.val : U → X) (barMarked J)).N
     (MarkedIdeal.pullback (n := n) (Subtype.val : U → X) (barMarked J)).ideal
     (MarkedIdeal.pullback (n := n) (Subtype.val : U → X) (barMarked J)).d=_ at hc
   rw [hbar] at hc
   exact hc
 let K : MarkedIdeal n X := withN (coeffMarkedAlong (barMarked J)) (J.N∩{y |u y=0})
 let KU : MarkedIdeal n (CMfd.of (n := n) U) :=
   withN (coeffMarkedAlong (barMarked JU)) (JU.N∩{y |uU y=0})
 have hK : MarkedIdeal.pullback (n := n) (Subtype.val : U → X) K=KU := by
   refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl ?_ ?_ ?_
   · simpa only [K,KU,withN,MarkedIdeal.pullback] using congrArg MarkedIdeal.E hCoeff
   · simpa only [K,KU,withN,MarkedIdeal.pullback] using congrArg MarkedIdeal.ideal hCoeff
   · simpa only [K,KU,withN,MarkedIdeal.pullback] using congrArg MarkedIdeal.d hCoeff
 have hStage := ContactStageInvDomain.isInvDomain_stage_coeffHomAlong_of_le
   (X := CMfd.of (n := n) U) (k := q+1) JU hgood.isWellFormed hgood.one_le_d hgood.dimLE Uu huU
   (Y := CMfd.of (n := n) U) .refl trivial W (fun y hy => (interior_subset hy).1)
   (by
     intro y hy _ hyZ
     have hyO : y.val∈O := hy
     have hnZ := (interior_subset hyO).2.2
     apply hnZ
     change y∈CodimOneSupportAlong.codimOnePartAlong (barMarked JU).N (barMarked JU).ideal (barMarked JU).d at hyZ
     rw [hZdict] at hyZ
     exact hyZ)
   (by
     intro H hH y hy _
     change H∈JU.E.take JU.E.length at hH
     rw [List.take_length] at hH
     change H∈J.E.map ((Subtype.val : U → X) ⁻¹' ·) at hH
     obtain ⟨K,hK,rfl⟩ := List.mem_map.mp hH
     have hyO : y.val∈O := hy
     apply (interior_subset hyO).2.1 K
     change K∈J.E.take J.E.length
     simpa only [List.take_length] using hK)
 change IsInvDomain (M := CMfd.of (n := n) W) ((q+1)-1)
   (MarkedIdeal.pullback (n := n) (Subtype.val : W → U) KU) at hStage
 have hWdom : IsInvDomain (M := CMfd.of (n := n) W) q (MarkedIdeal.pullback (n := n) (Subtype.val : W → U) KU) := by
   simpa only [Nat.add_sub_cancel] using hStage
 let σ := swapNested O U
 have hhK : ∀ y g,K.ideal.mem y g → HolomorphicAt n g y := fun _ _ hg => hg.1
 have hSwap : MarkedIdeal.pullback (n := n) (Subtype.val : G → O) (StepOneValueMasked.lowerMarkedB J (.refl : BlowupTower X X) x)=
     MarkedIdeal.pullback σ (MarkedIdeal.pullback (n := n) (Subtype.val : W → U) KU) := by
   change MarkedIdeal.pullback (n := n) (Subtype.val : G → O) (MarkedIdeal.pullback (n := n) (Subtype.val : O → X) K)=_
   rw [←hK]
   have hKW : MarkedIdeal.pullback (n := n) (Subtype.val : W → U) (MarkedIdeal.pullback (n := n) (Subtype.val : U → X) K)=
       MarkedIdeal.pullback (n := n) (fun w : W => w.val.val) K :=
     marked_pullback_comp_hhol hhK contMDiff_subtype_val contMDiff_subtype_val (fun _ => rfl)
   rw [hKW]
   exact (marked_pullback_comp_hhol hhK contMDiff_subtype_val contMDiff_subtype_val (fun _ => rfl)).trans
     (marked_pullback_comp_hhol hhK (contMDiff_subtype_val.comp contMDiff_subtype_val) σ.contMDiff (fun _ => rfl)).symm
 rw [hSwap]
 exact InvDomainTowerAlong.isInvDomain_pullback σ hWdom
private theorem original_chosen_contact_lower_good_cosupp
 (q : ℕ) (J : MarkedIdeal n X)
 (hhol : ∀ x g,J.ideal.mem x g → HolomorphicAt n g x)
 (U : Opens X)
 (hgood : IsInvDomain (M := CMfd.of (n := n) U) (q+1) (MarkedIdeal.pullback (n := n) (Subtype.val : U → X) J))
 (x : X) (hxU : x∈U) (hxO : x∈maskB J (.refl : BlowupTower X X) x) (hx : x∈J.cosupp)
 (hu : TangentDirectionAlong.IsTangentDirectionAlong J.N J.ideal J.d
   (tangentChoice J x).1 (tangentChoice J x).2) :
 (⟨⟨x,hxO⟩,hxU⟩ : MaxLocusLocal.nestedOpens (maskB J (.refl : BlowupTower X X) x) U) ∈
   (MarkedIdeal.pullback (n := n) (Subtype.val : MaxLocusLocal.nestedOpens (maskB J (.refl : BlowupTower X X) x) U → maskB J (.refl : BlowupTower X X) x)
     (StepOneValueMasked.lowerMarkedB J (.refl : BlowupTower X X) x)).cosupp := by
 let JU : MarkedIdeal n (CMfd.of (n := n) U) := MarkedIdeal.pullback (n := n) (Subtype.val : U → X) J
 let O : Opens X := maskB J (.refl : BlowupTower X X) x
 let W := MaxLocusLocal.nestedOpens U O
 let G := MaxLocusLocal.nestedOpens O U
 let u : X → ℂ := (tangentChoice J x).2
 let uU : U → ℂ := u∘Subtype.val
 let Uu : Opens U := ⟨(Subtype.val : U → X) ⁻¹' (tangentChoice J x).1,hu.isOpen.preimage continuous_subtype_val⟩
 have huU : TangentDirectionAlong.IsTangentDirectionAlong JU.N JU.ideal JU.d Uu uU :=
   ContactEquivalenceAlong.isTangentDirectionAlong_pullback
     (fun y => ⟨openInv U y,isLocalInverseAt_val U y⟩) hhol hu
 have hhBar : ∀ y g,(barMarked J).ideal.mem y g → HolomorphicAt n g y := fun _ _ hg => hg.1
 have hbar : MarkedIdeal.pullback (n := n) (Subtype.val : U → X) (barMarked J)=barMarked JU :=
   HironakaActualNonregularCoefficientNaturality.pullback_coeff_homMarkedAlong contMDiff_subtype_val
     (fun y => ⟨openInv U y,isLocalInverseAt_val U y⟩) J hhol
 have hCoeff : MarkedIdeal.pullback (n := n) (Subtype.val : U → X) (coeffMarkedAlong (barMarked J))=
     coeffMarkedAlong (barMarked JU) := by
   rw [HironakaActualNonregularCoefficientNaturality.pullback_coeffMarkedAlong contMDiff_subtype_val
     (fun y => ⟨openInv U y,isLocalInverseAt_val U y⟩) (barMarked J) hhBar,hbar]
 have hZdict : CodimOneSupportAlong.codimOnePartAlong (barMarked JU).N (barMarked JU).ideal (barMarked JU).d=
     (Subtype.val : U → X) ⁻¹' CodimOneSupportAlong.codimOnePartAlong (barMarked J).N (barMarked J).ideal (barMarked J).d := by
   have hc := CodimOnePartCanonical.codimOnePartAlong_pullback_val U (N := (barMarked J).N) hhBar (barMarked J).d
   change CodimOneSupportAlong.codimOnePartAlong (MarkedIdeal.pullback (n := n) (Subtype.val : U → X) (barMarked J)).N
     (MarkedIdeal.pullback (n := n) (Subtype.val : U → X) (barMarked J)).ideal
     (MarkedIdeal.pullback (n := n) (Subtype.val : U → X) (barMarked J)).d=_ at hc
   rw [hbar] at hc
   exact hc
 let K : MarkedIdeal n X := withN (coeffMarkedAlong (barMarked J)) (J.N∩{y |u y=0})
 let KU : MarkedIdeal n (CMfd.of (n := n) U) :=
   withN (coeffMarkedAlong (barMarked JU)) (JU.N∩{y |uU y=0})
 have hK : MarkedIdeal.pullback (n := n) (Subtype.val : U → X) K=KU := by
   refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl ?_ ?_ ?_
   · simpa only [K,KU,withN,MarkedIdeal.pullback] using congrArg MarkedIdeal.E hCoeff
   · simpa only [K,KU,withN,MarkedIdeal.pullback] using congrArg MarkedIdeal.ideal hCoeff
   · simpa only [K,KU,withN,MarkedIdeal.pullback] using congrArg MarkedIdeal.d hCoeff
 have hStage := ContactStageInvDomain.isInvDomain_stage_coeffHomAlong_of_le
   (X := CMfd.of (n := n) U) (k := q+1) JU hgood.isWellFormed hgood.one_le_d hgood.dimLE Uu huU
   (Y := CMfd.of (n := n) U) .refl trivial W (fun y hy => (interior_subset hy).1)
   (by
     intro y hy _ hyZ
     have hyO : y.val∈O := hy
     have hnZ := (interior_subset hyO).2.2
     apply hnZ
     change y∈CodimOneSupportAlong.codimOnePartAlong (barMarked JU).N (barMarked JU).ideal (barMarked JU).d at hyZ
     rw [hZdict] at hyZ
     exact hyZ)
   (by
     intro H hH y hy _
     change H∈JU.E.take JU.E.length at hH
     rw [List.take_length] at hH
     change H∈J.E.map ((Subtype.val : U → X) ⁻¹' ·) at hH
     obtain ⟨K,hK,rfl⟩ := List.mem_map.mp hH
     have hyO : y.val∈O := hy
     apply (interior_subset hyO).2.1 K
     change K∈J.E.take J.E.length
     simpa only [List.take_length] using hK)
 change IsInvDomain (M := CMfd.of (n := n) W) ((q+1)-1)
   (MarkedIdeal.pullback (n := n) (Subtype.val : W → U) KU) at hStage
 have hWdom : IsInvDomain (M := CMfd.of (n := n) W) q (MarkedIdeal.pullback (n := n) (Subtype.val : W → U) KU) := by
   simpa only [Nat.add_sub_cancel] using hStage
 let σ := swapNested O U
 have hhK : ∀ y g,K.ideal.mem y g → HolomorphicAt n g y := fun _ _ hg => hg.1
 have hSwap : MarkedIdeal.pullback (n := n) (Subtype.val : G → O) (StepOneValueMasked.lowerMarkedB J (.refl : BlowupTower X X) x)=
     MarkedIdeal.pullback σ (MarkedIdeal.pullback (n := n) (Subtype.val : W → U) KU) := by
   change MarkedIdeal.pullback (n := n) (Subtype.val : G → O) (MarkedIdeal.pullback (n := n) (Subtype.val : O → X) K)=_
   rw [←hK]
   have hKW : MarkedIdeal.pullback (n := n) (Subtype.val : W → U) (MarkedIdeal.pullback (n := n) (Subtype.val : U → X) K)=
       MarkedIdeal.pullback (n := n) (fun w : W => w.val.val) K :=
     marked_pullback_comp_hhol hhK contMDiff_subtype_val contMDiff_subtype_val (fun _ => rfl)
   rw [hKW]
   exact (marked_pullback_comp_hhol hhK contMDiff_subtype_val contMDiff_subtype_val (fun _ => rfl)).trans
     (marked_pullback_comp_hhol hhK (contMDiff_subtype_val.comp contMDiff_subtype_val) σ.contMDiff (fun _ => rfl)).symm
 rw [hSwap]
 let y : U := ⟨x,hxU⟩
 have hy : y∈JU.cosupp := by
   rw [cosupp_pullback_val J hhol U]
   exact hx
 have hyUu : y∈Uu := (interior_subset hxO).1
 have hyzero : uU y=0 := huU.cosupport_inter_subset
   (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hgood.isWellFormed.isCoherent hg) hgood.one_le_d ⟨hy,hyUu⟩
 have hybar : y∈(barMarked JU).cosupp := by
   rw [StepOneLowerDomain.cosupp_barMarked JU hgood.isWellFormed hgood.one_le_d]
   exact hy
 have hyKU : y∈KU.cosupp := by
   rw [show KU=withN (coeffMarkedAlong (barMarked JU)) (JU.N∩{y |uU y=0}) from rfl,
     CoefficientIdealAlongRestriction.cosupp_coeffMarkedAlong_withN
       (StepOneLowerDomain.isWellFormed_barMarked JU hgood.isWellFormed).isClosedSubmanifold_N.2
       (fun _ _ hg => hg.1) (ContactIndependenceAlong.one_le_coeffMarkedAlong_d _)
       (fun _ h => h.1)]
   exact ⟨hybar,⟨hy.1,hyzero⟩⟩
 have hc := MarkedIdeal.cosupp_pullback σ.contMDiff σ.symm.contMDiff
   σ.apply_symm_apply σ.symm_apply_apply
   (MarkedIdeal.pullback (n := n) (Subtype.val : W → U) KU) (fun _ _ hg => hg.1)
 rw [hc,cosupp_pullback_val KU (fun _ _ hg => hg.1) W]
 exact hyKU

private theorem original_chosen_contact_lower_value_on_good_open
 (hn : 0<n) (q : ℕ) (ih : InitialLocality.{u} hn q)
 (J : MarkedIdeal n X)
 (hhol : ∀ x g,J.ideal.mem x g → HolomorphicAt n g x)
 (U : Opens X)
 (hgood : IsInvDomain (M := CMfd.of (n := n) U) (q+1) (MarkedIdeal.pullback (n := n) (Subtype.val : U → X) J))
 (x : X) (hxU : x∈U) (hxO : x∈maskB J (.refl : BlowupTower X X) x) (hx : x∈J.cosupp)
 (hu : TangentDirectionAlong.IsTangentDirectionAlong J.N J.ideal J.d
   (tangentChoice J x).1 (tangentChoice J x).2) :
 (CanonicalCentres.invFamily hn q).inv (X := CMfd.of (n := n) (maskB J (.refl : BlowupTower X X) x)) (Y := CMfd.of (n := n) (maskB J (.refl : BlowupTower X X) x)) (StepOneValueMasked.lowerMarkedB J (.refl : BlowupTower X X) x) .refl ⟨x,hxO⟩ =
 (CanonicalCentres.invFamily hn q).inv (X := CMfd.of (n := n) (MaxLocusLocal.nestedOpens (maskB J (.refl : BlowupTower X X) x) U)) (Y := CMfd.of (n := n) (MaxLocusLocal.nestedOpens (maskB J (.refl : BlowupTower X X) x) U))
   (MarkedIdeal.pullback (n := n) (Subtype.val : MaxLocusLocal.nestedOpens (maskB J (.refl : BlowupTower X X) x) U → maskB J (.refl : BlowupTower X X) x)
     (StepOneValueMasked.lowerMarkedB J (.refl : BlowupTower X X) x)) .refl ⟨⟨x,hxO⟩,hxU⟩ := by
 let O := maskB J (.refl : BlowupTower X X) x
 let G := MaxLocusLocal.nestedOpens O U
 let L := StepOneValueMasked.lowerMarkedB J (.refl : BlowupTower X X) x
 have hLd : IsInvDomain (M := CMfd.of (n := n) G) q (MarkedIdeal.pullback (n := n) (Subtype.val : G → O) L) :=
   original_chosen_contact_lower_good_domain q J hhol U hgood x hu
 have hLc : (⟨⟨x,hxO⟩,hxU⟩ : G) ∈ (MarkedIdeal.pullback (n := n) (Subtype.val : G → O) L).cosupp :=
   original_chosen_contact_lower_good_cosupp q J hhol U hgood x hxU hxO hx hu
 have hhL : ∀ y g,L.ideal.mem y g → HolomorphicAt n g y := lowerMarkedM_hhol J 0 .refl x
 have hcL : ∀ y g,IsInSpanAt (n := n) (L.ideal.mem y) y g → L.ideal.mem y g := lowerMarkedM_span_closed J 0 .refl x
 have hxL : (⟨x,hxO⟩ : O) ∈ L.cosupp := by
   rw [cosupp_pullback_val L hhL G] at hLc
   exact hLc
 exact ih (X := CMfd.of (n := n) O) L hhL hcL G hLd ⟨⟨x,hxO⟩,hxU⟩ hxL
section RecordComparison
variable {Z Z' : CMfd.{u} n}
open HironakaActualFreshRecursiveValues StepOneLowerDomain AnalyticSubsetOpens
open CodimOnePartCanonical HironakaSharpActualCurrentOpenLowerReferences BoundaryCount CodimOneSupportAlong MemberInterLocusAlong
open DerivativeIdealAlong GiraudAlong BlowupFlatCoordinates DerivativeIdealAlongCoherent
open HironakaActualNonregularCompanionNaturality
private theorem tangent_from_record
 (A : MarkedIdeal n Z) (B : MarkedIdeal n Z')
 (hhol : ∀ x g,A.ideal.mem x g → HolomorphicAt n g x)
 (hcl : ∀ x g,IsInSpanAt (n := n) (A.ideal.mem x) x g → A.ideal.mem x g)
 (hB : B.IsWellFormed)
 (hmax : HomogenizedIdealAlong.IsMaximalOrderAlong B.N B.ideal B.d)
 (hd : 1 ≤ A.d) (U : Opens Z) (U' : Opens Z')
 (η : U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ U')
 (hrec : MarkedIdeal.pullback (Subtype.val : U → Z) A =
   MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') B))
 (z : U) (hz : z.val ∈ A.cosupp) :
 ∃ (O : Set Z) (v : Z → ℂ), z.val ∈ O ∧
   TangentDirectionAlong.IsTangentDirectionAlong A.N A.ideal A.d O v := by
 have hhA : ∀ x g, A.ideal.mem x g → HolomorphicAt n g x :=
   hhol
 have hhB : ∀ x g, B.ideal.mem x g → HolomorphicAt n g x :=
   fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hB.isCoherent hg
 have hcA := cosupp_pullback_val A hhA U
 have hcB := cosupp_pullback_val B hhB U'
 have hcη := MarkedIdeal.cosupp_pullback η.contMDiff η.symm.contMDiff
   η.apply_symm_apply η.symm_apply_apply (MarkedIdeal.pullback (Subtype.val : U' → Z') B)
   (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
     (GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hB.isCoherent) hg)
 have hzW : z ∈ (MarkedIdeal.pullback (Subtype.val : U → Z) A).cosupp := by rw [hcA];exact hz
 rw [hrec,hcη,hcB] at hzW
 obtain ⟨k,hNk⟩ := hB.isClosedSubmanifold_N.2 (η z).val hzW.1
 have hNr : RegularAtDim (n := n) A.N z.val k := by
   apply (AnalyticSubsetOpens.regularAtDim_preimage_val_iff (U := U)).mp
   have heq := congrArg MarkedIdeal.N hrec
   change (Subtype.val : U → Z) ⁻¹' A.N = η ⁻¹' ((Subtype.val : U' → Z') ⁻¹' B.N) at heq
   rw [heq]
   apply (regularAtDim_preimage_iff η).mpr
   exact AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hNk
 have hnot : ¬ OrderGE n A.N A.ideal z.val (A.d+1) := by
   intro ho
   let A1 : MarkedIdeal n Z := {A with d := A.d+1}
   let B1 : MarkedIdeal n Z' := {B with d := B.d+1}
   have hdEq : A.d = B.d := congrArg MarkedIdeal.d hrec
   have hr1 : MarkedIdeal.pullback (Subtype.val : U → Z) A1 =
       MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') B1) := by
     apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
     · simpa only [A1,B1,MarkedIdeal.pullback] using congrArg MarkedIdeal.N hrec
     · simpa only [A1,B1,MarkedIdeal.pullback] using congrArg MarkedIdeal.E hrec
     · simpa only [A1,B1,MarkedIdeal.pullback] using congrArg MarkedIdeal.ideal hrec
     · exact congrArg (·+1) hdEq
   have hm : z ∈ (MarkedIdeal.pullback (Subtype.val : U → Z) A1).cosupp := by
     rw [cosupp_pullback_val A1 hhA U]
     exact ⟨hz.1,ho⟩
   rw [hr1,MarkedIdeal.cosupp_pullback η.contMDiff η.symm.contMDiff
     η.apply_symm_apply η.symm_apply_apply _
     (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
       (GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hB.isCoherent) hg),
     cosupp_pullback_val B1 hhB U'] at hm
   exact hmax (η z).val hm
 have hAw : (MarkedIdeal.pullback (Subtype.val : U → Z) A).ideal.IsCoherent := by
   rw [hrec]
   exact isCoherent_pullback η.contMDiff (isCoherent_pullback contMDiff_subtype_val hB.isCoherent)
 have hLocal := exists_local_generators_of_open_pullback hhol hcl U hAw z
 exact HironakaActualLocalTangentGenerators.exists_tangent_of_local_generators hhol hNr hd hz hnot
   (exists_iterated_generators_of_local_generators hLocal hNr (A.d-1))

private theorem bar_record
 (A : MarkedIdeal n Z) (B : MarkedIdeal n Z')
 (hhol : ∀ x g,A.ideal.mem x g → HolomorphicAt n g x)
 (hB : B.IsWellFormed)
 (U : Opens Z) (U' : Opens Z')
 (η : U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ U')
 (hrec : MarkedIdeal.pullback (Subtype.val : U → Z) A =
   MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') B)) :
 MarkedIdeal.pullback (Subtype.val : U → Z) (barMarked A) =
   MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') (barMarked B)) := by
 have hhA : ∀ x g, A.ideal.mem x g → HolomorphicAt n g x :=
   hhol
 have hhB : ∀ x g, B.ideal.mem x g → HolomorphicAt n g x :=
   fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hB.isCoherent hg
 have hBW : (MarkedIdeal.pullback (Subtype.val : U' → Z') B).ideal.IsCoherent :=
   GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hB.isCoherent
 calc
  MarkedIdeal.pullback (Subtype.val : U → Z) (barMarked A) =
    HomogenizedIdealAlong.coeffMarkedAlong (HomogenizedIdealAlong.homMarkedAlong (MarkedIdeal.pullback (Subtype.val : U → Z) A)) :=
    HironakaActualNonregularCoefficientNaturality.pullback_coeff_homMarkedAlong contMDiff_subtype_val
      (fun y => ⟨DerivativeIdealAlongEtale.openInv U y,DerivativeIdealAlongEtale.isLocalInverseAt_val U y⟩) A hhA
  _ = HomogenizedIdealAlong.coeffMarkedAlong (HomogenizedIdealAlong.homMarkedAlong (MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') B))) :=
    congrArg (fun Q : MarkedIdeal n U => HomogenizedIdealAlong.coeffMarkedAlong (HomogenizedIdealAlong.homMarkedAlong Q)) hrec
  _ = MarkedIdeal.pullback η (HomogenizedIdealAlong.coeffMarkedAlong (HomogenizedIdealAlong.homMarkedAlong (MarkedIdeal.pullback (Subtype.val : U' → Z') B))) :=
    (HironakaActualNonregularCoefficientNaturality.pullback_coeff_homMarkedAlong η.contMDiff
      (fun y => ⟨η.symm,⟨Eventually.of_forall (fun p => (η.contMDiff p).mdifferentiableAt (by simp)),
        Eventually.of_forall (fun p => (η.symm.contMDiff p).mdifferentiableAt (by simp)),
        Eventually.of_forall η.symm_apply_apply, Eventually.of_forall η.apply_symm_apply⟩⟩) _
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hBW hg)).symm
  _ = MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') (barMarked B)) := by
    have hv : MarkedIdeal.pullback (Subtype.val : U' → Z') (barMarked B) =
        HomogenizedIdealAlong.coeffMarkedAlong (HomogenizedIdealAlong.homMarkedAlong (MarkedIdeal.pullback (Subtype.val : U' → Z') B)) :=
      HironakaActualNonregularCoefficientNaturality.pullback_coeff_homMarkedAlong contMDiff_subtype_val
        (fun y => ⟨DerivativeIdealAlongEtale.openInv U' y,DerivativeIdealAlongEtale.isLocalInverseAt_val U' y⟩) B hhB
    rw [hv]

private theorem self_mask_from_record
 (A : MarkedIdeal n Z) (B : MarkedIdeal n Z')
 (hhol : ∀ x g,A.ideal.mem x g → HolomorphicAt n g x)
 (hcl : ∀ x g,IsInSpanAt (n := n) (A.ideal.mem x) x g → A.ideal.mem x g)
 (hB : B.IsWellFormed)
 (hmax : HomogenizedIdealAlong.IsMaximalOrderAlong B.N B.ideal B.d)
 (hd : 1 ≤ A.d) (U : Opens Z) (U' : Opens Z')
 (η : U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ U')
 (hrec : MarkedIdeal.pullback (Subtype.val : U → Z) A =
   MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') B))
 (z : U) (hz : z.val ∈ A.cosupp) (hl : level A .refl z.val = 0)
 (hsp : ¬ IsSpecial A .refl z.val) : z.val ∈ maskB A .refl z.val := by
 classical
 have ht := tangent_from_record A B hhol hcl hB hmax hd U U' η hrec z hz
 obtain ⟨hxchoice,hchoice⟩ := tangentChoice_spec A ht
 have hbar := bar_record A B hhol hB U U' η hrec
 have hBarB := isWellFormed_barMarked B hB
 have hdEq : A.d = B.d := congrArg MarkedIdeal.d hrec
 have hdB : 1 ≤ B.d := by omega
 have hBarMax := isMaximalOrderAlong_barMarked B hB hdB hmax
 have hBarD : 1 ≤ (barMarked B).d := ContactIndependenceAlong.one_le_coeffMarkedAlong_d _
 have hZclosed := isClosed_codimOnePartAlong hBarB.isCoherent hBarB.isClosedSubmanifold_N hBarD hBarMax
 have hhBarA : ∀ x g, (barMarked A).ideal.mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
 have hcodA := codimOnePartAlong_pullback_val U (N := (barMarked A).N)
   hhBarA (barMarked A).d
 have hcodB := codimOnePartAlong_pullback_val U' (N := (barMarked B).N)
   (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hBarB.isCoherent hg)
   (barMarked B).d
 have hBW : (MarkedIdeal.pullback (Subtype.val : U' → Z') (barMarked B)).ideal.IsCoherent :=
   GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hBarB.isCoherent
 have hcodη := codimOnePartAlong_pullback η
   (N := (MarkedIdeal.pullback (Subtype.val : U' → Z') (barMarked B)).N)
   (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hBW hg)
   (barMarked B).d
 let ZA := codimOnePartAlong (barMarked A).N (barMarked A).ideal (barMarked A).d
 let ZB := codimOnePartAlong (barMarked B).N (barMarked B).ideal (barMarked B).d
 have hcod : (Subtype.val : U → Z) ⁻¹' ZA = η ⁻¹' ((Subtype.val : U' → Z') ⁻¹' ZB) := by
   calc
    (Subtype.val : U → Z) ⁻¹' ZA = codimOnePartAlong
      (MarkedIdeal.pullback (Subtype.val : U → Z) (barMarked A)).N
      (MarkedIdeal.pullback (Subtype.val : U → Z) (barMarked A)).ideal
      (MarkedIdeal.pullback (Subtype.val : U → Z) (barMarked A)).d := hcodA.symm
    _ = codimOnePartAlong (MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') (barMarked B))).N
      (MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') (barMarked B))).ideal
      (MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') (barMarked B))).d :=
      congrArg (fun Q : MarkedIdeal n U => codimOnePartAlong Q.N Q.ideal Q.d) hbar
    _ = η ⁻¹' codimOnePartAlong
      (MarkedIdeal.pullback (Subtype.val : U' → Z') (barMarked B)).N
      (MarkedIdeal.pullback (Subtype.val : U' → Z') (barMarked B)).ideal
      (MarkedIdeal.pullback (Subtype.val : U' → Z') (barMarked B)).d := hcodη
    _ = η ⁻¹' ((Subtype.val : U' → Z') ⁻¹' ZB) := congrArg (η ⁻¹' ·) hcodB
 have hzZA : z.val ∉ ZA := fun h => hsp (Or.inl ⟨hl,h⟩)
 have hcZA : IsClosed ((Subtype.val : U → Z) ⁻¹' ZA) := by
   rw [hcod]
   exact (hZclosed.preimage continuous_subtype_val).preimage η.continuous
 have hevZ : ∀ᶠ w : U in 𝓝 z, w.val ∉ ZA := hcZA.isOpen_compl.mem_nhds hzZA
 have he := congrArg MarkedIdeal.E hrec
 change A.E.map ((Subtype.val : U → Z) ⁻¹' ·) =
   (B.E.map ((Subtype.val : U' → Z') ⁻¹' ·)).map (η ⁻¹' ·) at he
 have hBAE : (barMarked A).E = A.E := rfl
 have hcount : boundaryCount A.E z.val = boundaryCount B.E (η z).val := by
   rw [←boundaryCount_map_preimage (Subtype.val : U → Z) _ z,he,
     boundaryCount_map_preimage η,boundaryCount_map_preimage (Subtype.val : U' → Z')]
 have hzero : boundaryCount B.E (η z).val = 0 := by
   rw [←hcount]
   simpa only [level,origMembers,geoTransformAlong,hBAE,List.take_length] using hl
 have hnone : ∀ H∈B.E, (η z).val ∉ H := by
   intro H hH hp
   obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hH
   have hpos : 0 < boundaryCount B.E (η z).val := Finset.card_pos.mpr
     ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩⟩
   omega
 have hopen : IsOpen {w : U' | ∀ H∈B.E,w.val ∉ H} := by
   have ho := (List.finite_toSet B.E).isOpen_biInter fun H hH => (hB.isSNCDivisor.1 H hH).isOpen_compl
   convert ho.preimage (continuous_subtype_val : Continuous (Subtype.val : U' → Z')) using 1
   ext w
   simp
 have hevB : ∀ᶠ w : U in 𝓝 z, ∀ H∈B.E,(η w).val ∉ H :=
   η.continuous.continuousAt.eventually (hopen.mem_nhds hnone)
 have hevE : ∀ᶠ w : U in 𝓝 z, ∀ H∈A.E,w.val ∉ H := by
   filter_upwards [hevB] with w hw
   have ht : ∀ H∈(B.E.map ((Subtype.val : U' → Z') ⁻¹' ·)).map (η ⁻¹' ·),w ∉ H := by
     simpa only [List.forall_mem_map,mem_preimage] using hw
   rw [←he] at ht
   simpa only [List.forall_mem_map,mem_preimage] using ht
 have hev : ∀ᶠ w : Z in 𝓝 z.val, (∀ H∈A.E,w∉H) ∧ w∉ZA :=
   (eventually_nhds_val_iff U).mpr (hevE.and hevZ)
 have hf : z.val ∈ interior {w : Z | w∈(tangentChoice A z.val).1 ∧ (∀ H∈A.E,w∉H) ∧ w∉ZA} := by
   apply mem_interior_iff_mem_nhds.mpr
   filter_upwards [hchoice.isOpen.mem_nhds hxchoice,hev] with w hw hc
   exact ⟨hw,hc⟩
 change z.val ∈ interior _
 simpa only [origMembers,geoTransformAlong,BlowupTower.proj,hBAE,List.take_length,id_eq] using hf



private theorem initial_level_special
 (A0 : MarkedIdeal n Z) (B0 : MarkedIdeal n Z')
 (hhol : ∀ x g,A0.ideal.mem x g → HolomorphicAt n g x) (hBF : B0.IsWellFormed)
 (U : Opens Z) (U' : Opens Z')
 (η : U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ U')
 (hr : MarkedIdeal.pullback (Subtype.val : U → Z) A0=
   MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') B0)) :
 ∀ z : U,level A0 .refl z.val=level B0 .refl (η z).val ∧
   (IsSpecial A0 .refl z.val ↔ IsSpecial B0 .refl (η z).val) := by
 let A := barMarked A0
 let B := barMarked B0
 have hrec := bar_record A0 B0 hhol hBF U U' η hr
 have hhA : ∀ x g,A.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
 have hB : B.ideal.IsCoherent := (isWellFormed_barMarked B0 hBF).isCoherent
 have hBW : (MarkedIdeal.pullback (Subtype.val : U' → Z') B).ideal.IsCoherent :=
   isCoherent_pullback contMDiff_subtype_val hB
 have hO : A0.E.map ((Subtype.val : U → Z) ⁻¹' ·)=
     (B0.E.map ((Subtype.val : U' → Z') ⁻¹' ·)).map (η ⁻¹' ·) := congrArg MarkedIdeal.E hrec
 have origA : origMembers A0 (.refl : BlowupTower Z Z)=A0.E := by
   change A0.E.take A0.E.length=A0.E
   exact List.take_length
 have origB : origMembers B0 (.refl : BlowupTower Z' Z')=B0.E := by
   change B0.E.take B0.E.length=B0.E
   exact List.take_length
 have hlevel (z : U) : level A0 .refl z.val=level B0 .refl (η z).val := by
   simp only [level,origA,origB]
   rw [←boundaryCount_map_preimage (Subtype.val : U → Z) _ z,hO,
     boundaryCount_map_preimage η,boundaryCount_map_preimage (Subtype.val : U' → Z')]
 have hcodA := codimOnePartAlong_pullback_val U (N := A.N)
   (fun _ _ hg => hhA _ _ hg) A.d
 have hcodB := codimOnePartAlong_pullback_val U' (N := B.N)
   (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hB hg) B.d
 have hcodη := codimOnePartAlong_pullback η
   (N := (MarkedIdeal.pullback (Subtype.val : U' → Z') B).N)
   (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hBW hg) B.d
 have hcod : (Subtype.val : U → Z) ⁻¹' codimOnePartAlong A.N A.ideal A.d =
     η ⁻¹' ((Subtype.val : U' → Z') ⁻¹' codimOnePartAlong B.N B.ideal B.d) := by
   calc
     (Subtype.val : U → Z) ⁻¹' codimOnePartAlong A.N A.ideal A.d =
         codimOnePartAlong (MarkedIdeal.pullback (Subtype.val : U → Z) A).N
           (MarkedIdeal.pullback (Subtype.val : U → Z) A).ideal
           (MarkedIdeal.pullback (Subtype.val : U → Z) A).d := hcodA.symm
     _ = codimOnePartAlong (MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') B)).N
         (MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') B)).ideal
         (MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') B)).d :=
       congrArg (fun Q : MarkedIdeal n U => codimOnePartAlong Q.N Q.ideal Q.d) hrec
     _ = η ⁻¹' codimOnePartAlong (MarkedIdeal.pullback (Subtype.val : U' → Z') B).N
         (MarkedIdeal.pullback (Subtype.val : U' → Z') B).ideal B.d := hcodη
     _ = η ⁻¹' ((Subtype.val : U' → Z') ⁻¹' codimOnePartAlong B.N B.ideal B.d) :=
       congrArg (η ⁻¹' ·) hcodB
 have hcosA := cosupp_pullback_val A
   (fun _ _ hg => hhA _ _ hg) U
 have hcosB := cosupp_pullback_val B
   (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hB hg) U'
 have hcosη := MarkedIdeal.cosupp_pullback η.contMDiff η.symm.contMDiff
   η.apply_symm_apply η.symm_apply_apply (MarkedIdeal.pullback (Subtype.val : U' → Z') B)
   (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hBW hg)
 have hmemA := memberInterLocus_preimage (Subtype.val : U → Z)
   (fun z => U.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq z) A.N
   A0.E A.cosupp
 have hmemB := memberInterLocus_preimage (Subtype.val : U' → Z')
   (fun z => U'.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq z) B.N
   B0.E B.cosupp
 have hmemη := memberInterLocus_preimage (η : U → U')
   (fun z => η.toHomeomorph.map_nhds_eq z) (MarkedIdeal.pullback (Subtype.val : U' → Z') B).N
   (B0.E.map ((Subtype.val : U' → Z') ⁻¹' ·))
   (MarkedIdeal.pullback (Subtype.val : U' → Z') B).cosupp
 have hmem : (Subtype.val : U → Z) ⁻¹' memberInterLocus A.N
       A0.E A.cosupp =
     η ⁻¹' ((Subtype.val : U' → Z') ⁻¹' memberInterLocus B.N
       B0.E B.cosupp) := by
   calc
     (Subtype.val : U → Z) ⁻¹' memberInterLocus A.N
         A0.E A.cosupp =
       memberInterLocus (MarkedIdeal.pullback (Subtype.val : U → Z) A).N
         (A0.E.map ((Subtype.val : U → Z) ⁻¹' ·))
         (MarkedIdeal.pullback (Subtype.val : U → Z) A).cosupp := by
           rw [hcosA]; exact hmemA.symm
     _ = memberInterLocus (MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') B)).N
         ((B0.E.map ((Subtype.val : U' → Z') ⁻¹' ·)).map (η ⁻¹' ·))
         (MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') B)).cosupp := by
           rw [hrec, hO]
     _ = η ⁻¹' memberInterLocus (MarkedIdeal.pullback (Subtype.val : U' → Z') B).N
         (B0.E.map ((Subtype.val : U' → Z') ⁻¹' ·))
         (MarkedIdeal.pullback (Subtype.val : U' → Z') B).cosupp := by
           rw [hcosη]; exact hmemη
     _ = η ⁻¹' ((Subtype.val : U' → Z') ⁻¹' memberInterLocus B.N
         B0.E B.cosupp) := by
           congr 1
           rw [hcosB]; exact hmemB
 intro z
 refine ⟨hlevel z,?_⟩
 simp only [IsSpecial,origA,origB,geoTransformAlong]
 rw [hlevel z]
 exact or_congr (and_congr_right fun _ => Iff.of_eq (congrArg (fun S : Set U => z ∈ S) hcod))
   (and_congr_right fun _ => Iff.of_eq (congrArg (fun S : Set U => z ∈ S) hmem))


private theorem self_maskA_from_record
 (hn : 0<n) (A : MarkedIdeal n Z) (B : MarkedIdeal n Z')
 (hhol : ∀ x g,A.ideal.mem x g → HolomorphicAt n g x) (hB : B.IsWellFormed) (hdB : 1≤B.d)
 (U : Opens Z) (U' : Opens Z')
 (η : U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ U')
 (hrec : MarkedIdeal.pullback (Subtype.val : U → Z) A=
   MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') B))
 (z : U) (hl : 1≤level A .refl z.val) (hsp : ¬IsSpecial A .refl z.val) :
 z.val∈maskA A .refl z.val := by
 classical
 have facts := initial_level_special A B hhol hB U U' η hrec
 have hpos : 1≤level B .refl (η z).val := by rw [←(facts z).1];exact hl
 have hnsp : ¬IsSpecial B .refl (η z).val := fun h => hsp ((facts z).2.mpr h)
 have hmask := StepOneLowerDomain.mem_maskA B hB hdB hn (.refl : BlowupTower Z' Z') trivial hpos hnsp
 have origA : origMembers A (.refl : BlowupTower Z Z)=A.E := by
   change A.E.take A.E.length=A.E
   exact List.take_length
 have origB : origMembers B (.refl : BlowupTower Z' Z')=B.E := by
   change B.E.take B.E.length=B.E
   exact List.take_length
 change (η z).val∈interior {w | (∀ H∈origMembers B (.refl : BlowupTower Z' Z'),w∈H → (η z).val∈H) ∧
   ¬(level B .refl w=level B .refl (η z).val ∧ IsSpecial B .refl w)} at hmask
 rw [origB] at hmask
 have ht := mem_interior_iff_mem_nhds.mp hmask
 have htU : ∀ᶠ w : U' in 𝓝 (η z),(∀ H∈B.E,w.val∈H → (η z).val∈H) ∧
     ¬(level B .refl w.val=level B .refl (η z).val ∧ IsSpecial B .refl w.val) :=
   (eventually_nhds_val_iff U').mp ht
 have hsU : ∀ᶠ w : U in 𝓝 z,(∀ H∈A.E,w.val∈H → z.val∈H) ∧
     ¬(level A .refl w.val=level A .refl z.val ∧ IsSpecial A .refl w.val) := by
   filter_upwards [η.continuous.continuousAt.eventually htU] with w hw
   have he := congrArg MarkedIdeal.E hrec
   change A.E.map ((Subtype.val : U → Z) ⁻¹' ·)=
     (B.E.map ((Subtype.val : U' → Z') ⁻¹' ·)).map (η ⁻¹' ·) at he
   have hlist : (∀ H∈A.E,w.val∈H → z.val∈H) ↔ (∀ H∈B.E,(η w).val∈H → (η z).val∈H) := by
     have hp := congrArg (fun L : List (Set U) => ∀ H∈L,w∈H → z∈H) he
     simpa only [List.forall_mem_map,mem_preimage] using Iff.of_eq hp
   refine ⟨hlist.mpr hw.1,fun hm => hw.2 ⟨?_,(facts w).2.mp hm.2⟩⟩
   exact (facts w).1.symm.trans (hm.1.trans (facts z).1)
 have hs : ∀ᶠ w : Z in 𝓝 z.val,(∀ H∈A.E,w∈H → z.val∈H) ∧
     ¬(level A .refl w=level A .refl z.val ∧ IsSpecial A .refl w) :=
   (eventually_nhds_val_iff U).mpr hsU
 change z.val∈interior {w | (∀ H∈origMembers A (.refl : BlowupTower Z Z),w∈H → z.val∈H) ∧
   ¬(level A .refl w=level A .refl z.val ∧ IsSpecial A .refl w)}
 rw [origA]
 exact mem_interior_iff_mem_nhds.mpr hs


end RecordComparison

private def toUniv (A : CMfd.{u} n) :
 A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (⊤ : Opens A) where
 toFun a := ⟨a,trivial⟩
 invFun a := a.val
 left_inv _ := rfl
 right_inv _ := rfl
 contMDiff_toFun := BlowupRestrictOpen.contMDiff_opens_mk (V := ⊤) (f := id) contMDiff_id (fun _ => trivial)
 contMDiff_invFun := contMDiff_subtype_val

private theorem good_open_record_dictionary (J : MarkedIdeal n X) (U : Opens X)
 (hc : (MarkedIdeal.pullback (n := n) (Subtype.val : U → X) J).ideal.IsCoherent) :
 let JU : MarkedIdeal n (CMfd.of (n := n) U) := MarkedIdeal.pullback (n := n) (Subtype.val : U → X) J
 JU=MarkedIdeal.pullback (toUniv (CMfd.of (n := n) U))
   (MarkedIdeal.pullback (n := n) (Subtype.val : (⊤ : Opens U) → U) JU) := by
 dsimp only
 have hh : ∀ y g,(MarkedIdeal.pullback (n := n) (Subtype.val : U → X) J).ideal.mem y g → HolomorphicAt n g y := fun _ _ hg => hg.1
 have he := marked_pullback_comp_hhol hh contMDiff_subtype_val (toUniv (CMfd.of (n := n) U)).contMDiff (d := id) (fun _ => rfl)
 rw [he]
 refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl ?_ ?_ rfl
 · simp only [MarkedIdeal.pullback,id_eq,preimage_id_eq]
   exact (List.map_id _).symm
 · exact (BlowupControlledTransform.pullback_id hc).symm

private theorem good_contact_anchor_to_actual_choice
 (hn : 0<n) (q : ℕ) (J : MarkedIdeal n X) (hJ : IsInvDomain (q+1) J)
 (hmax : HomogenizedIdealAlong.IsMaximalOrderAlong J.N J.ideal J.d)
 (x : X) (hx : x∈J.cosupp) (hl : level J .refl x=0) (hsp : ¬IsSpecial J .refl x)
 (Uu : Opens X) (u : X→ℂ)
 (hu : TangentDirectionAlong.IsTangentDirectionAlong J.N J.ideal J.d Uu u)
 (W : Opens X) (hxW : x∈W) (hWU : W≤Uu)
 (hWE : ∀ H∈J.E,∀ y∈W,y∉H)
 (hDW : IsInvDomain (M := CMfd.of (n := n) W) q
   (MarkedIdeal.pullback (n := n) (Subtype.val : W→X)
     (withN (coeffMarkedAlong (barMarked J)) (J.N∩{y |u y=0})))) :
 ∃ hm : x∈maskB J (.refl : BlowupTower X X) x,
   (CanonicalCentres.invFamily hn q).inv (X := CMfd.of (n := n) W)
     (MarkedIdeal.pullback (n := n) (Subtype.val : W→X)
       (withN (coeffMarkedAlong (barMarked J)) (J.N∩{y |u y=0}))) .refl ⟨x,hxW⟩ =
   (CanonicalCentres.invFamily hn q).inv
     (X := CMfd.of (n := n) (maskB J (.refl : BlowupTower X X) x))
     (StepOneValueMasked.lowerMarkedB J (.refl : BlowupTower X X) x) .refl ⟨x,hm⟩ := by
 classical
 have hxbar : x∈(barMarked J).cosupp := by
   rw [StepOneLowerDomain.cosupp_barMarked J hJ.isWellFormed hJ.one_le_d]
   exact hx
 have hD := Seq.StepOneCanonicalTail.lowerDataL_refl J (k := q+1) (CanonicalCentres.invFamily hn q)
   hJ.isWellFormed hJ.one_le_d hn hmax hJ.dimLE (.refl : BlowupTower X X) trivial hxbar
   (show stepRegime J 0 .refl x from ⟨hl,hsp⟩)
 obtain ⟨hm,hDB,hCB,hXB⟩ := hD
 change x∈maskB J (.refl : BlowupTower X X) x at hm
 have hv := StepOneCompare.tangentChoice_spec_of_mem J (interior_subset hm).1
 obtain ⟨A,hxA,hA⟩ := Seq.StepOneTangentChange.inv_restrictedCoeffHom_eq_of_opens
   (CanonicalCentres.invFamily hn q) J hJ.isWellFormed.isCoherent hJ.isWellFormed.isClosedSubmanifold_N
   hJ.one_le_d hx hu (hWU hxW) hv (interior_subset hm).1
 refine ⟨hm,?_⟩
 have h := hA (.refl : BlowupTower X X) (.refl : BlowupTower X X) trivial
   W (maskB J (.refl : BlowupTower X X) x) hWU
   (fun y hy => (interior_subset hy).1)
   (by
     intro H hH y hy
     change H∈J.E.take J.E.length at hH
     rw [List.take_length] at hH
     exact hWE H hH y hy)
   (by
     intro H hH y hy
     apply (interior_subset hy).2.1 H
     exact hH)
   hDW trivial hDB hCB ⟨x,hxW⟩ ⟨x,hm⟩ rfl hxA hxbar
 exact h

private theorem zero_level_step_value_on_good_open
 (hn : 0<n) (q : ℕ) (ih : InitialLocality.{u} hn q)
 (J : MarkedIdeal n X)
 (hhol : ∀ x g,J.ideal.mem x g → HolomorphicAt n g x)
 (hcl : ∀ x g,IsInSpanAt (n := n) (J.ideal.mem x) x g → J.ideal.mem x g)
 (U : Opens X)
 (hgood : IsInvDomain (M := CMfd.of (n := n) U) (q+1) (MarkedIdeal.pullback (n := n) (Subtype.val : U → X) J))
 (hmax : HomogenizedIdealAlong.IsMaximalOrderAlong
   ((MarkedIdeal.pullback (n := n) (Subtype.val : U → X) J).N)
   ((MarkedIdeal.pullback (n := n) (Subtype.val : U → X) J).ideal)
   ((MarkedIdeal.pullback (n := n) (Subtype.val : U → X) J).d))
 (x : X) (hxU : x∈U) (hx : x∈J.cosupp)
 (hl : level J .refl x=0) (hsp : ¬IsSpecial J .refl x) :
 Seq.StepOneValueMasked.stepOneInvM (CanonicalCentres.invFamily hn q) J .refl x =
 Seq.StepOneValueMasked.stepOneInvM (CanonicalCentres.invFamily hn q)
   (X := CMfd.of (n := n) U) (Y := CMfd.of (n := n) U)
   (MarkedIdeal.pullback (n := n) (Subtype.val : U → X) J) .refl ⟨x,hxU⟩ := by
 classical
 let JU : MarkedIdeal n (CMfd.of (n := n) U) := MarkedIdeal.pullback (n := n) (Subtype.val : U → X) J
 let y : U := ⟨x,hxU⟩
 have hrec := good_open_record_dictionary J U hgood.isWellFormed.isCoherent
 have ht := tangent_from_record J JU hhol hcl hgood.isWellFormed hmax hgood.one_le_d
   U ⊤ (toUniv (CMfd.of (n := n) U)) hrec y hx
 obtain ⟨hxChoice,hu⟩ := StepOneLowerDomain.tangentChoice_spec J ht
 have hxO := self_mask_from_record J JU hhol hcl hgood.isWellFormed hmax hgood.one_le_d
   U ⊤ (toUniv (CMfd.of (n := n) U)) hrec y hx hl hsp
 have facts := initial_level_special J JU hhol hgood.isWellFormed
   U ⊤ (toUniv (CMfd.of (n := n) U)) hrec
 have hlU : level JU .refl y=0 := (facts y).1.symm.trans hl
 have hspU : ¬IsSpecial JU .refl y := fun h => hsp ((facts y).2.mpr h)

 let O : Opens X := maskB J (.refl : BlowupTower X X) x
 let W := MaxLocusLocal.nestedOpens U O
 let G := MaxLocusLocal.nestedOpens O U
 let u : X → ℂ := (tangentChoice J x).2
 let uU : U → ℂ := u∘Subtype.val
 let Uu : Opens U := ⟨(Subtype.val : U → X) ⁻¹' (tangentChoice J x).1,hu.isOpen.preimage continuous_subtype_val⟩
 have huU : TangentDirectionAlong.IsTangentDirectionAlong JU.N JU.ideal JU.d Uu uU :=
   ContactEquivalenceAlong.isTangentDirectionAlong_pullback
     (fun y => ⟨openInv U y,isLocalInverseAt_val U y⟩) hhol hu
 have hhBar : ∀ y g,(barMarked J).ideal.mem y g → HolomorphicAt n g y := fun _ _ hg => hg.1
 have hbar : MarkedIdeal.pullback (n := n) (Subtype.val : U → X) (barMarked J)=barMarked JU :=
   HironakaActualNonregularCoefficientNaturality.pullback_coeff_homMarkedAlong contMDiff_subtype_val
     (fun y => ⟨openInv U y,isLocalInverseAt_val U y⟩) J hhol
 have hCoeff : MarkedIdeal.pullback (n := n) (Subtype.val : U → X) (coeffMarkedAlong (barMarked J))=
     coeffMarkedAlong (barMarked JU) := by
   rw [HironakaActualNonregularCoefficientNaturality.pullback_coeffMarkedAlong contMDiff_subtype_val
     (fun y => ⟨openInv U y,isLocalInverseAt_val U y⟩) (barMarked J) hhBar,hbar]
 have hZdict : CodimOneSupportAlong.codimOnePartAlong (barMarked JU).N (barMarked JU).ideal (barMarked JU).d=
     (Subtype.val : U → X) ⁻¹' CodimOneSupportAlong.codimOnePartAlong (barMarked J).N (barMarked J).ideal (barMarked J).d := by
   have hc := CodimOnePartCanonical.codimOnePartAlong_pullback_val U (N := (barMarked J).N) hhBar (barMarked J).d
   change CodimOneSupportAlong.codimOnePartAlong (MarkedIdeal.pullback (n := n) (Subtype.val : U → X) (barMarked J)).N
     (MarkedIdeal.pullback (n := n) (Subtype.val : U → X) (barMarked J)).ideal
     (MarkedIdeal.pullback (n := n) (Subtype.val : U → X) (barMarked J)).d=_ at hc
   rw [hbar] at hc
   exact hc
 let K : MarkedIdeal n X := withN (coeffMarkedAlong (barMarked J)) (J.N∩{y |u y=0})
 let KU : MarkedIdeal n (CMfd.of (n := n) U) :=
   withN (coeffMarkedAlong (barMarked JU)) (JU.N∩{y |uU y=0})
 have hK : MarkedIdeal.pullback (n := n) (Subtype.val : U → X) K=KU := by
   refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl ?_ ?_ ?_
   · simpa only [K,KU,withN,MarkedIdeal.pullback] using congrArg MarkedIdeal.E hCoeff
   · simpa only [K,KU,withN,MarkedIdeal.pullback] using congrArg MarkedIdeal.ideal hCoeff
   · simpa only [K,KU,withN,MarkedIdeal.pullback] using congrArg MarkedIdeal.d hCoeff
 have hStage := ContactStageInvDomain.isInvDomain_stage_coeffHomAlong_of_le
   (X := CMfd.of (n := n) U) (k := q+1) JU hgood.isWellFormed hgood.one_le_d hgood.dimLE Uu huU
   (Y := CMfd.of (n := n) U) .refl trivial W (fun y hy => (interior_subset hy).1)
   (by
     intro y hy _ hyZ
     have hyO : y.val∈O := hy
     have hnZ := (interior_subset hyO).2.2
     apply hnZ
     change y∈CodimOneSupportAlong.codimOnePartAlong (barMarked JU).N (barMarked JU).ideal (barMarked JU).d at hyZ
     rw [hZdict] at hyZ
     exact hyZ)
   (by
     intro H hH y hy _
     change H∈JU.E.take JU.E.length at hH
     rw [List.take_length] at hH
     change H∈J.E.map ((Subtype.val : U → X) ⁻¹' ·) at hH
     obtain ⟨K,hK,rfl⟩ := List.mem_map.mp hH
     have hyO : y.val∈O := hy
     apply (interior_subset hyO).2.1 K
     change K∈J.E.take J.E.length
     simpa only [List.take_length] using hK)
 change IsInvDomain (M := CMfd.of (n := n) W) ((q+1)-1)
   (MarkedIdeal.pullback (n := n) (Subtype.val : W → U) KU) at hStage
 have hWdom : IsInvDomain (M := CMfd.of (n := n) W) q (MarkedIdeal.pullback (n := n) (Subtype.val : W → U) KU) := by
   simpa only [Nat.add_sub_cancel] using hStage
 let σ := swapNested O U
 have hhK : ∀ y g,K.ideal.mem y g → HolomorphicAt n g y := fun _ _ hg => hg.1
 have hSwap : MarkedIdeal.pullback (n := n) (Subtype.val : G → O) (StepOneValueMasked.lowerMarkedB J (.refl : BlowupTower X X) x)=
     MarkedIdeal.pullback σ (MarkedIdeal.pullback (n := n) (Subtype.val : W → U) KU) := by
   change MarkedIdeal.pullback (n := n) (Subtype.val : G → O) (MarkedIdeal.pullback (n := n) (Subtype.val : O → X) K)=_
   rw [←hK]
   have hKW : MarkedIdeal.pullback (n := n) (Subtype.val : W → U) (MarkedIdeal.pullback (n := n) (Subtype.val : U → X) K)=
       MarkedIdeal.pullback (n := n) (fun w : W => w.val.val) K :=
     marked_pullback_comp_hhol hhK contMDiff_subtype_val contMDiff_subtype_val (fun _ => rfl)
   rw [hKW]
   exact (marked_pullback_comp_hhol hhK contMDiff_subtype_val contMDiff_subtype_val (fun _ => rfl)).trans
     (marked_pullback_comp_hhol hhK (contMDiff_subtype_val.comp contMDiff_subtype_val) σ.contMDiff (fun _ => rfl)).symm

 have hsource := original_chosen_contact_lower_value_on_good_open hn q ih J hhol U hgood x hxU hxO hx hu
 have hLc := original_chosen_contact_lower_good_cosupp q J hhol U hgood x hxU hxO hx hu
 have hσcos := MarkedIdeal.cosupp_pullback σ.contMDiff σ.symm.contMDiff
   σ.apply_symm_apply σ.symm_apply_apply
   (MarkedIdeal.pullback (n := n) (Subtype.val : W → U) KU) (fun _ _ hg => hg.1)
 rw [hSwap,hσcos] at hLc
 have hIso := (CanonicalCentres.invFamily hn q).isInvValue.towerIso (X := CMfd.of (n := n) W) (X' := CMfd.of (n := n) G) σ
   (MarkedIdeal.pullback (n := n) (Subtype.val : W → U) KU) hWdom
   .refl .refl σ (.refl) trivial (⟨⟨x,hxO⟩,hxU⟩ : G) hLc
 rw [←hSwap] at hIso
 have hyJU : y∈JU.cosupp := by
   rw [cosupp_pullback_val J hhol U]
   exact hx
 obtain ⟨hmU,hAnchor⟩ := good_contact_anchor_to_actual_choice hn q JU hgood hmax y hyJU hlU hspU
   Uu uU huU W hxO (fun z hz => (interior_subset hz).1)
   (by
     intro H hH z hz
     change H∈J.E.map ((Subtype.val : U→X) ⁻¹' ·) at hH
     obtain ⟨K,hK,rfl⟩ := List.mem_map.mp hH
     apply (interior_subset hz).2.1 K
     change K∈J.E.take J.E.length
     simpa only [List.take_length] using hK)
   hWdom
 have hValues := hsource.trans (hIso.trans hAnchor)
 unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
 rw [if_neg hsp,if_neg hspU,hl,hlU]
 change toLex (0,if h : x∈maskB J (.refl : BlowupTower X X) x then
   ((CanonicalCentres.invFamily hn q).inv (X := CMfd.of (n := n) O) (Y := CMfd.of (n := n) O) (StepOneValueMasked.lowerMarkedB J .refl x) .refl ⟨x,h⟩ : WithTop (CanonicalCentres.ValTy q)) else ⊤)=
   toLex (0,if h : y∈maskB JU (.refl : BlowupTower (CMfd.of (n := n) U) (CMfd.of (n := n) U)) y then
   ((CanonicalCentres.invFamily hn q).inv (X := CMfd.of (n := n) (maskB JU (.refl : BlowupTower (CMfd.of (n := n) U) (CMfd.of (n := n) U)) y)) (Y := CMfd.of (n := n) (maskB JU (.refl : BlowupTower (CMfd.of (n := n) U) (CMfd.of (n := n) U)) y)) (StepOneValueMasked.lowerMarkedB JU .refl y) .refl ⟨y,h⟩ : WithTop (CanonicalCentres.ValTy q)) else ⊤)
 rw [dif_pos hxO,dif_pos hmU,hValues]

open InvDomainRebase InvDomainMemberRestriction MemberInterLocusAlong
private theorem raw_self_memberRestrict_pullback
    (𝔪 : MarkedIdeal n X) (hhol : ∀ x g,𝔪.ideal.mem x g → HolomorphicAt n g x)
    (U : Opens X) (p : U) :
    MarkedIdeal.pullback (Subtype.val : U → X) (memberRestrict 𝔪 (membersThrough 𝔪.E 𝔪.E p)) =
      memberRestrict (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪)
        (membersThrough (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪).E
          (𝔪.E.map ((Subtype.val : U → X) ⁻¹' ·)) p) := by
  have hcoeff := HironakaActualNonregularCoefficientNaturality.pullback_coeffMarkedAlong contMDiff_subtype_val
    (fun y => ⟨openInv U y,isLocalInverseAt_val U y⟩) 𝔪 hhol
  have hmem : ∀ H ∈ 𝔪.E, (p : X) ∈ H →
      (Subtype.val : U → X) ⁻¹' H ∈ 𝔪.E.map ((Subtype.val : U → X) ⁻¹' ·) → H ∈ 𝔪.E :=
    fun H hH _ _ => hH
  have hI := congrArg MarkedIdeal.ideal hcoeff
  have hD := congrArg MarkedIdeal.d hcoeff
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ ?_ hI hD
  · show (Subtype.val : U → X) ⁻¹' (memberRestrict 𝔪 (membersThrough 𝔪.E 𝔪.E p)).N = _
    rw [memberRestrict_membersThrough_N, memberRestrict_membersThrough_N]
    ext q
    simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq]
    refine and_congr_right fun _ => ⟨fun hw H' hH' hH'₀ hpH' => ?_, fun hw H hH hH₀ hpH => ?_⟩
    · obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hH'
      exact hw H hH (hmem H hH hpH' hH'₀) hpH'
    · exact hw _ (List.mem_map_of_mem hH) (List.mem_map_of_mem hH₀) hpH
  · show (memberRestrict 𝔪 (membersThrough 𝔪.E 𝔪.E p)).E.map ((Subtype.val : U → X) ⁻¹' ·) = _
    rw [memberRestrict_membersThrough_E, memberRestrict_membersThrough_E]
    exact (filter_map_members (f := ((Subtype.val : U → X) ⁻¹' ·)) (y := (p : X)) (y' := p)
      (fun H _ => Iff.rfl) hmem).symm

private theorem raw_maskA_good_open_trace
 (J : MarkedIdeal n X)
 (hhol : ∀ x g,J.ideal.mem x g → HolomorphicAt n g x)
 (U : Opens X)
 (hWF : (MarkedIdeal.pullback (n := n) (Subtype.val : U→X) J).IsWellFormed)
 (x : U) :
 (Subtype.val : U→X) ⁻¹' (maskA J (.refl : BlowupTower X X) x.val : Set X)=
   (maskA (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (n := n) (Subtype.val : U→X) J) .refl x : Set U) := by
 let JU : MarkedIdeal n (CMfd.of (n := n) U) := MarkedIdeal.pullback (n := n) (Subtype.val : U→X) J
 have hrec := good_open_record_dictionary J U hWF.isCoherent
 have facts := initial_level_special J JU hhol hWF U ⊤ (toUniv (CMfd.of (n := n) U)) hrec
 have origA : origMembers J (.refl : BlowupTower X X)=J.E := by
   change J.E.take J.E.length=J.E
   exact List.take_length
 have origB : origMembers JU (.refl : BlowupTower (CMfd.of (n := n) U) (CMfd.of (n := n) U))=JU.E := by
   change JU.E.take JU.E.length=JU.E
   exact List.take_length
 change (Subtype.val : U→X) ⁻¹' interior {z | (∀ H∈origMembers J (.refl : BlowupTower X X),z∈H→x.val∈H) ∧
   ¬(level J .refl z=level J .refl x.val ∧ IsSpecial J .refl z)}=
   interior {z | (∀ H∈origMembers JU (.refl : BlowupTower (CMfd.of (n := n) U) (CMfd.of (n := n) U)),z∈H→x∈H) ∧
   ¬(level JU .refl z=level JU .refl x ∧ IsSpecial JU .refl z)}
 rw [origA,origB]
 have ht : IsOpenMap (Subtype.val : U→X) := U.isOpen.isOpenMap_subtype_val
 rw [ht.preimage_interior_eq_interior_preimage continuous_subtype_val]
 apply congrArg interior
 ext z
 change ((∀ H∈J.E,z.val∈H→x.val∈H) ∧ ¬(level J .refl z.val=level J .refl x.val ∧ IsSpecial J .refl z.val)) ↔ _
 rw [(facts z).1,(facts x).1,(facts z).2]
 simp only [JU,MarkedIdeal.pullback,List.forall_mem_map,mem_preimage]
 rfl

private theorem positive_level_step_value_on_good_open
 (hn : 0<n) (q : ℕ) (ih : InitialLocality.{u} hn q)
 (J : MarkedIdeal n X)
 (hhol : ∀ x g,J.ideal.mem x g → HolomorphicAt n g x)
 (U : Opens X)
 (hgood : IsInvDomain (M := CMfd.of (n := n) U) (q+1) (MarkedIdeal.pullback (n := n) (Subtype.val : U → X) J))
 (hmax : HomogenizedIdealAlong.IsMaximalOrderAlong
   ((MarkedIdeal.pullback (n := n) (Subtype.val : U → X) J).N)
   ((MarkedIdeal.pullback (n := n) (Subtype.val : U → X) J).ideal)
   ((MarkedIdeal.pullback (n := n) (Subtype.val : U → X) J).d))
 (x : U) (hx : x.val∈J.cosupp) (s : ℕ)
 (hl : level J .refl x.val=s+1) (hsp : ¬IsSpecial J .refl x.val) :
 Seq.StepOneValueMasked.stepOneInvM (CanonicalCentres.invFamily hn q) J .refl x.val =
 Seq.StepOneValueMasked.stepOneInvM (CanonicalCentres.invFamily hn q)
   (X := CMfd.of (n := n) U) (Y := CMfd.of (n := n) U)
   (MarkedIdeal.pullback (n := n) (Subtype.val : U → X) J) .refl x := by
 classical
 let JU : MarkedIdeal n (CMfd.of (n := n) U) := MarkedIdeal.pullback (n := n) (Subtype.val : U→X) J
 have hrec := good_open_record_dictionary J U hgood.isWellFormed.isCoherent
 have facts := initial_level_special J JU hhol hgood.isWellFormed U ⊤ (toUniv (CMfd.of (n := n) U)) hrec
 have hlU : level JU .refl x=s+1 := (facts x).1.symm.trans hl
 have hspU : ¬IsSpecial JU .refl x := fun h => hsp ((facts x).2.mpr h)
 have hxO := self_maskA_from_record hn J JU hhol hgood.isWellFormed hgood.one_le_d U ⊤
   (toUniv (CMfd.of (n := n) U)) hrec x (by omega) hsp
 have hxJU : x∈JU.cosupp := by rw [cosupp_pullback_val J hhol U];exact hx
 have hxbar : x∈(barMarked JU).cosupp := by
   rw [StepOneLowerDomain.cosupp_barMarked JU hgood.isWellFormed hgood.one_le_d];exact hxJU
 obtain ⟨hmU,hDU,hCU,hXU⟩ := Seq.StepOneCanonicalTail.lowerDataL_refl JU (k := q+1)
   (CanonicalCentres.invFamily hn q) hgood.isWellFormed hgood.one_le_d hn hmax hgood.dimLE
   (.refl : BlowupTower (CMfd.of (n := n) U) (CMfd.of (n := n) U)) trivial hxbar
   (show stepRegime JU (s+1) .refl x from ⟨hlU,hspU⟩)
 let O := maskA J (.refl : BlowupTower X X) x.val
 let O' := maskA JU (.refl : BlowupTower (CMfd.of (n := n) U) (CMfd.of (n := n) U)) x
 let G := MaxLocusLocal.nestedOpens O U
 let W := MaxLocusLocal.nestedOpens U O
 have hW : W=O' := by
   apply TopologicalSpace.Opens.ext
   exact raw_maskA_good_open_trace J hhol U hgood.isWellFormed x
 let σ := (swapNested O U).trans (BlowupTowerIsoTail.opensCongr (n := n) hW)
 let A := memberRestrict (barMarked J) (membersThrough (barMarked J).E (barMarked J).E x.val)
 let B := memberRestrict (barMarked JU) (membersThrough (barMarked JU).E (barMarked JU).E x)
 let L : MarkedIdeal n (CMfd.of (n := n) O) := StepOneValueMasked.lowerMarkedM J (s+1) (.refl : BlowupTower X X) x.val
 let L' : MarkedIdeal n (CMfd.of (n := n) O') := StepOneValueMasked.lowerMarkedM JU (s+1) (.refl : BlowupTower (CMfd.of (n := n) U) (CMfd.of (n := n) U)) x
 have hhA : ∀ y g,A.ideal.mem y g → HolomorphicAt n g y := fun _ _ hg => hg.1
 have hbar : MarkedIdeal.pullback (n := n) (Subtype.val : U→X) (barMarked J)=barMarked JU :=
   HironakaActualNonregularCoefficientNaturality.pullback_coeff_homMarkedAlong contMDiff_subtype_val
     (fun z => ⟨openInv U z,isLocalInverseAt_val U z⟩) J hhol
 have hAB : MarkedIdeal.pullback (n := n) (Subtype.val : U→X) A=B := by
   have h := raw_self_memberRestrict_pullback (barMarked J) (fun _ _ hg => hg.1) U x
   change MarkedIdeal.pullback (n := n) (Subtype.val : U→X) A=memberRestrict
     (MarkedIdeal.pullback (n := n) (Subtype.val : U→X) (barMarked J))
     (membersThrough (MarkedIdeal.pullback (n := n) (Subtype.val : U→X) (barMarked J)).E
       (MarkedIdeal.pullback (n := n) (Subtype.val : U→X) (barMarked J)).E x) at h
   rw [hbar] at h
   exact h
 have hmU' : x∈O' := hmU
 have hSwap : MarkedIdeal.pullback (n := n) (Subtype.val : G→O) L=MarkedIdeal.pullback σ L' := by
   simp only [L,L',StepOneValueMasked.lowerMarkedM,StepOneValue.lowerMarked,origMembers,geoTransformAlong]
   simp only [show (barMarked J).E=J.E from rfl,show (barMarked JU).E=JU.E from rfl,List.take_length]
   change MarkedIdeal.pullback (n := n) (Subtype.val : G→O) (MarkedIdeal.pullback (n := n) (Subtype.val : O→X) A)=
     MarkedIdeal.pullback σ (MarkedIdeal.pullback (n := n) (Subtype.val : O'→U) B)
   rw [←hAB]
   have hB' : MarkedIdeal.pullback (n := n) (Subtype.val : O'→U) (MarkedIdeal.pullback (n := n) (Subtype.val : U→X) A)=
       MarkedIdeal.pullback (n := n) (fun z : O' => z.val.val) A :=
     marked_pullback_comp_hhol hhA contMDiff_subtype_val contMDiff_subtype_val (fun _ => rfl)
   rw [hB']
   exact (marked_pullback_comp_hhol hhA contMDiff_subtype_val contMDiff_subtype_val (fun _ => rfl)).trans
     (marked_pullback_comp_hhol hhA (contMDiff_subtype_val.comp contMDiff_subtype_val) σ.contMDiff (fun _ => rfl)).symm
 have hLG : IsInvDomain (M := CMfd.of (n := n) G) q (MarkedIdeal.pullback (n := n) (Subtype.val : G→O) L) := by
   rw [hSwap]
   exact InvDomainTowerAlong.isInvDomain_pullback σ hDU
 have hhL := lowerMarkedM_hhol J (s+1) (.refl : BlowupTower X X) x.val
 have hcL := lowerMarkedM_span_closed J (s+1) (.refl : BlowupTower X X) x.val
 have hxL : (⟨x.val,hxO⟩ : O)∈L.cosupp := by
   have hcos := MarkedIdeal.cosupp_pullback σ.contMDiff σ.symm.contMDiff σ.apply_symm_apply σ.symm_apply_apply L' (fun _ _ hg => hg.1)
   have ht : (⟨⟨x.val,hxO⟩,x.property⟩ : G)∈(MarkedIdeal.pullback (n := n) (Subtype.val : G→O) L).cosupp := by
     rw [hSwap,hcos]
     exact hXU
   rw [cosupp_pullback_val L hhL G] at ht
   exact ht
 have hIL := ih (X := CMfd.of (n := n) O) L hhL hcL G hLG (⟨⟨x.val,hxO⟩,x.property⟩ : G) hxL
 have hIso := (CanonicalCentres.invFamily hn q).isInvValue.towerIso
   (X := CMfd.of (n := n) O') (X' := CMfd.of (n := n) G) σ L' hDU
   .refl .refl σ (.refl) hCU (⟨⟨x.val,hxO⟩,x.property⟩ : G) hXU
 rw [←hSwap] at hIso
 have hValues := hIL.trans hIso
 unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
 rw [if_neg hsp,if_neg hspU,hl,hlU]
 change toLex (s+1,if h : x.val∈O then
   ((CanonicalCentres.invFamily hn q).inv (X := CMfd.of (n := n) O) L .refl ⟨x.val,h⟩ : WithTop (CanonicalCentres.ValTy q)) else ⊤)=
   toLex (s+1,if h : x∈O' then
   ((CanonicalCentres.invFamily hn q).inv (X := CMfd.of (n := n) O') L' .refl ⟨x,h⟩ : WithTop (CanonicalCentres.ValTy q)) else ⊤)
 rw [dif_pos hxO,dif_pos hmU',hValues]
 have hpt : σ (⟨⟨x.val,hxO⟩,x.property⟩ : G)=(⟨x,hmU'⟩ : O') := by
   apply Subtype.ext
   apply Subtype.ext
   rfl
 rw [hpt]
private theorem maximal_step_value_on_good_open
 (hn : 0<n) (q : ℕ) (ih : InitialLocality.{u} hn q)
 (J : MarkedIdeal n X)
 (hhol : ∀ x g,J.ideal.mem x g → HolomorphicAt n g x)
 (hcl : ∀ x g,IsInSpanAt (n := n) (J.ideal.mem x) x g → J.ideal.mem x g)
 (U : Opens X)
 (hgood : IsInvDomain (M := CMfd.of (n := n) U) (q+1) (MarkedIdeal.pullback (n := n) (Subtype.val : U → X) J))
 (hmax : HomogenizedIdealAlong.IsMaximalOrderAlong
   ((MarkedIdeal.pullback (n := n) (Subtype.val : U → X) J).N)
   ((MarkedIdeal.pullback (n := n) (Subtype.val : U → X) J).ideal)
   ((MarkedIdeal.pullback (n := n) (Subtype.val : U → X) J).d))
 (x : X) (hxU : x∈U) (hx : x∈J.cosupp)
 :
 Seq.StepOneValueMasked.stepOneInvM (CanonicalCentres.invFamily hn q) J .refl x =
 Seq.StepOneValueMasked.stepOneInvM (CanonicalCentres.invFamily hn q)
   (X := CMfd.of (n := n) U) (Y := CMfd.of (n := n) U)
   (MarkedIdeal.pullback (n := n) (Subtype.val : U → X) J) .refl ⟨x,hxU⟩ := by
 classical
 by_cases hsp : IsSpecial J .refl x
 · let JU : MarkedIdeal n (CMfd.of (n := n) U) := MarkedIdeal.pullback (n := n) (Subtype.val : U→X) J
   have hrec := good_open_record_dictionary J U hgood.isWellFormed.isCoherent
   have facts := initial_level_special J JU hhol hgood.isWellFormed U ⊤ (toUniv (CMfd.of (n := n) U)) hrec
   have hspU : IsSpecial (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (n := n) (Subtype.val : U→X) J) .refl ⟨x,hxU⟩ := (facts ⟨x,hxU⟩).2.mp hsp
   have hlev : level J (.refl : BlowupTower X X) x=level (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (n := n) (Subtype.val : U→X) J) .refl ⟨x,hxU⟩ := (facts ⟨x,hxU⟩).1
   unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
   rw [if_pos hsp,if_pos hspU,hlev]
 · cases hl : level J .refl x with
   | zero => exact zero_level_step_value_on_good_open hn q ih J hhol hcl U hgood hmax x hxU hx hl hsp
   | succ s => exact positive_level_step_value_on_good_open hn q ih J hhol U hgood hmax ⟨x,hxU⟩ hx s hl hsp
private theorem companion_span_closed
 (A : MarkedIdeal n X) (o : ℕ) {x : X} {g : X → ℂ}
 (hg : IsInSpanAt (n := n) ((companionOf n A o).ideal.mem x) x g) :
 (companionOf n A o).ideal.mem x g := by
 classical
 unfold companionOf companionAlong at hg ⊢
 split_ifs at hg ⊢
 · simp only [MarkedIdealOperationsTransform.MarkedIdeal.add,RestrictedIdealExtension.sumIdeal] at hg ⊢
   exact IsInSpanAt.trans (fun _ hs => hs) hg
 · obtain ⟨hfhol,K,s,a,hs,ha,hsum⟩ := hg
   refine ⟨hfhol,fun v hv => ?_⟩
   refine RestrictedIdealExtension.restrictOn_of_isInSpanAt (𝔞 := A.ideal)
     ⟨hv.1.mul hfhol,K,fun i w => v w*s i w,a,fun i => (hs i).2 v hv,ha,?_⟩
   filter_upwards [hsum] with w hw
   show v w*g w=∑ i,a i w*(v w*s i w)
   rw [hw,Finset.mul_sum]
   exact Finset.sum_congr rfl fun i _ => by ring

private theorem companion_hhol
 (A : MarkedIdeal n X) (o : ℕ) {x : X} {g : X → ℂ}
 (hg : (companionOf n A o).ideal.mem x g) : HolomorphicAt n g x := by
 unfold companionOf companionAlong at hg
 split_ifs at hg <;> exact hg.1


private theorem raw_ordMask_good_open_trace
 (J : MarkedIdeal n X)
 (hhol : ∀ x g,J.ideal.mem x g → HolomorphicAt n g x)
 (hcl : ∀ x g,IsInSpanAt (n := n) (J.ideal.mem x) x g → J.ideal.mem x g)
 (U : Opens X) (o : ℕ) :
 (Subtype.val : U→X) ⁻¹' (ordMask J o : Set X)=
   (ordMask (M := CMfd.of (n := n) U) (MarkedIdeal.pullback (n := n) (Subtype.val : U→X) J) o : Set U) := by
 change (Subtype.val : U→X) ⁻¹' (closure (ordGe J (o+1)))ᶜ=(closure (ordGe (M := CMfd.of (n := n) U) (MarkedIdeal.pullback (n := n) (Subtype.val : U→X) J) (o+1)))ᶜ
 rw [raw_ordGe_pullback_val J hhol hcl U (o+1),preimage_compl]
 have ht : IsOpenMap (Subtype.val : U→X) := U.isOpen.isOpenMap_subtype_val
 rw [ht.preimage_closure_eq_closure_preimage continuous_subtype_val]

open GeneralValue GeneralCompare GeneralCanonicalTail
private theorem actual_initial_companion_lower_value_on_good_open
 (hn : 0<n) (q : ℕ) (ih : InitialLocality.{u} hn q)
 (J : MarkedIdeal n X)
 (hhol : ∀ x g,J.ideal.mem x g → HolomorphicAt n g x)
 (hcl : ∀ x g,IsInSpanAt (n := n) (J.ideal.mem x) x g → J.ideal.mem x g)
 (U : Opens X)
 (hgood : IsInvDomain (M := CMfd.of (n := n) U) (q+1) (MarkedIdeal.pullback (n := n) (Subtype.val : U → X) J))
 (x : U) (hx : x.val∈J.cosupp) (o : ℕ) (ho : 1≤o) (hxo : nmOrd J x.val=o) :
 genLowerValue (fun {A} K {B} T z => Seq.StepOneValueMasked.stepOneInvM (X := A) (CanonicalCentres.invFamily hn q) K (Y := B) T z)
   J o .refl .refl x.val =
 genLowerValue (fun {A} K {B} T z => Seq.StepOneValueMasked.stepOneInvM (X := A) (CanonicalCentres.invFamily hn q) K (Y := B) T z)
   (X := CMfd.of (n := n) U) (Y₀ := CMfd.of (n := n) U) (Y := CMfd.of (n := n) U)
   (MarkedIdeal.pullback (n := n) (Subtype.val : U→X) J) o .refl .refl x := by
 classical
 let JU : MarkedIdeal n (CMfd.of (n := n) U) := MarkedIdeal.pullback (n := n) (Subtype.val : U→X) J
 have hxJU : x∈JU.cosupp := by rw [cosupp_pullback_val J hhol U];exact hx
 have hxoU : nmOrd JU x=o := (raw_nmOrd_pullback_val J hhol hcl U x).trans hxo
 obtain ⟨hmU,hDU,hMaxU,hCU,hXU⟩ := GeneralCanonicalTail.genLowerData_refl
   (M := fun {A} K {B} T z => Seq.StepOneValueMasked.stepOneInvM (X := A) (CanonicalCentres.invFamily hn q) K (Y := B) T z)
   hn hgood (.refl : BlowupTower (CMfd.of (n := n) U) (CMfd.of (n := n) U)) trivial hxJU hxoU ho
 let O := ordMask J o
 let O' := ordMask JU o
 let G := MaxLocusLocal.nestedOpens O U
 let W := MaxLocusLocal.nestedOpens U O
 have hW : W=O' := by
   apply TopologicalSpace.Opens.ext
   exact raw_ordMask_good_open_trace J hhol hcl U o
 have hmU' : x∈O' := hmU
 have hmA : x.val∈O := by
   have h := congrArg (fun S : Set U => x∈S) (raw_ordMask_good_open_trace J hhol hcl U o)
   exact (Iff.of_eq h).mpr hmU'
 let σ := (swapNested O U).trans (BlowupTowerIsoTail.opensCongr (n := n) hW)
 have hpt : σ (⟨⟨x.val,hmA⟩,x.property⟩ : G)=(⟨x,hmU'⟩ : O') := by
   apply Subtype.ext
   apply Subtype.ext
   rfl
 let A := companionOf n J o
 let B := companionOf n JU o
 let L : MarkedIdeal n (CMfd.of (n := n) O) := compAt J o (.refl : BlowupTower X X)
 let L' : MarkedIdeal n (CMfd.of (n := n) O') := compAt JU o (.refl : BlowupTower (CMfd.of (n := n) U) (CMfd.of (n := n) U))
 have hhA : ∀ y g,A.ideal.mem y g → HolomorphicAt n g y := fun _ _ hg => companion_hhol J o hg
 have hAB : MarkedIdeal.pullback (n := n) (Subtype.val : U→X) A=B :=
   HironakaActualRawCompanionNaturality.pullback_companionOf (X := X) (Y := CMfd.of (n := n) U) (f := (Subtype.val : U→X)) contMDiff_subtype_val
     (fun z => ⟨openInv U z,isLocalInverseAt_val U z⟩) J hhol hcl o
 have hLO : MarkedIdeal.pullback (n := n) (Subtype.val : O→X) A=L :=
   HironakaActualRawCompanionNaturality.pullback_companionOf (X := X) (Y := CMfd.of (n := n) O) (f := (Subtype.val : O→X)) contMDiff_subtype_val
     (fun z => ⟨openInv O z,isLocalInverseAt_val O z⟩) J hhol hcl o
 have hLU : MarkedIdeal.pullback (n := n) (Subtype.val : O'→U) B=L' :=
   HironakaActualRawCompanionNaturality.pullback_companionOf (X := CMfd.of (n := n) U) (Y := CMfd.of (n := n) O') (f := (Subtype.val : O'→U)) contMDiff_subtype_val
     (fun z => ⟨openInv O' z,isLocalInverseAt_val O' z⟩) JU (fun _ _ hg => hg.1)
     (by
       intro y g hg
       dsimp only [JU,MarkedIdeal.pullback,GermIdeal.pullback] at hg ⊢
       exact IsInSpanAt.trans (fun _ hs => hs) hg) o
 have hSwap : MarkedIdeal.pullback (n := n) (Subtype.val : G→O) L=MarkedIdeal.pullback σ L' := by
   rw [←hLO,←hLU,←hAB]
   have hB' : MarkedIdeal.pullback (n := n) (Subtype.val : O'→U) (MarkedIdeal.pullback (n := n) (Subtype.val : U→X) A)=
       MarkedIdeal.pullback (n := n) (fun z : O' => z.val.val) A :=
     marked_pullback_comp_hhol hhA contMDiff_subtype_val contMDiff_subtype_val (fun _ => rfl)
   rw [hB']
   exact (marked_pullback_comp_hhol hhA contMDiff_subtype_val contMDiff_subtype_val (fun _ => rfl)).trans
     (marked_pullback_comp_hhol hhA (contMDiff_subtype_val.comp contMDiff_subtype_val) σ.contMDiff (fun _ => rfl)).symm
 have hLG : IsInvDomain (M := CMfd.of (n := n) G) (q+1) (MarkedIdeal.pullback (n := n) (Subtype.val : G→O) L) := by
   rw [hSwap]
   exact InvDomainTowerAlong.isInvDomain_pullback σ hDU
 have hMaxG : HomogenizedIdealAlong.IsMaximalOrderAlong
   (MarkedIdeal.pullback (n := n) (Subtype.val : G→O) L).N
   (MarkedIdeal.pullback (n := n) (Subtype.val : G→O) L).ideal
   (MarkedIdeal.pullback (n := n) (Subtype.val : G→O) L).d := by
   rw [hSwap]
   exact (StepOneTowerIso.hypotheses_pullback (X := CMfd.of (n := n) O') (X' := CMfd.of (n := n) G) σ L' hDU.isWellFormed hDU.one_le_d hMaxU hDU.dimLE).2.2.1
 have hhL : ∀ y g,L.ideal.mem y g → HolomorphicAt n g y := fun _ _ hg => companion_hhol _ o hg
 have hcL : ∀ y g,IsInSpanAt (n := n) (L.ideal.mem y) y g → L.ideal.mem y g := fun _ _ hg => companion_span_closed _ o hg
 have hxL : (⟨x.val,hmA⟩ : O)∈L.cosupp := by
   have hcos := MarkedIdeal.cosupp_pullback σ.contMDiff σ.symm.contMDiff σ.apply_symm_apply σ.symm_apply_apply L' (fun _ _ hg => companion_hhol _ o hg)
   have ht : (⟨⟨x.val,hmA⟩,x.property⟩ : G)∈(MarkedIdeal.pullback (n := n) (Subtype.val : G→O) L).cosupp := by
     rw [hSwap,hcos]
     change σ (⟨⟨x.val,hmA⟩,x.property⟩ : G)∈L'.cosupp
     rw [hpt]
     exact hXU
   rw [cosupp_pullback_val L hhL G] at ht
   exact ht
 have hIL := maximal_step_value_on_good_open hn q ih L hhL hcL G hLG hMaxG ⟨x.val,hmA⟩ x.property hxL
 have hIso := (StepOneSeq.isMaxOrderValue_stepOneInvM (k := q+1) (CanonicalCentres.invFamily hn q) hn).towerIso
   (X := CMfd.of (n := n) O') (X' := CMfd.of (n := n) G) σ L' hDU hMaxU
   .refl .refl σ (.refl) hCU (⟨⟨x.val,hmA⟩,x.property⟩ : G) (by rw [hpt];exact hXU)
 rw [←hSwap,hpt] at hIso
 have hValues := hIL.trans hIso
 unfold genLowerValue
 change (if h : x.val∈O then
   (Seq.StepOneValueMasked.stepOneInvM (CanonicalCentres.invFamily hn q) L .refl ⟨x.val,h⟩ : WithTop (ℕ ×ₗ WithTop (CanonicalCentres.ValTy q))) else ⊤)=
   (if h : x∈O' then
   (Seq.StepOneValueMasked.stepOneInvM (CanonicalCentres.invFamily hn q) L' .refl ⟨x,h⟩ : WithTop (ℕ ×ₗ WithTop (CanonicalCentres.ValTy q))) else ⊤)
 rw [dif_pos hmA,dif_pos hmU',hValues]

private theorem initial_succ (hn : 0<n) (q : ℕ) (ih : InitialLocality.{u} hn q) :
 InitialLocality.{u} hn (q+1) := by
 intro X J hhol hcl U hgood x hx
 let JU : MarkedIdeal n (CMfd.of (n := n) U) := MarkedIdeal.pullback (n := n) (Subtype.val : U→X) J
 let M := fun {A : CMfd.{u} n} (K : MarkedIdeal n A) {B : CMfd.{u} n} (T : BlowupTower A B) (z : B) =>
   Seq.StepOneValueMasked.stepOneInvM (X := A) (CanonicalCentres.invFamily hn q) K (Y := B) T z
 have hord : nmOrd JU x=nmOrd J x.val := raw_nmOrd_pullback_val J hhol hcl U x
 have hsecond : genSecond M J (.refl : BlowupTower X X) x.val=
   genSecond M JU (.refl : BlowupTower (CMfd.of (n := n) U) (CMfd.of (n := n) U)) x := by
   classical
   unfold genSecond
   change (if nmOrd J x.val=0 then
     toLex (Sum.inl (MonomialCaseAlong.gammaAlong n J.N J.ideal J.E J.d x.val)) else
     toLex (Sum.inr (genLowerValue M J (nmOrd J x.val) .refl .refl x.val)))=
     (if nmOrd JU x=0 then
     toLex (Sum.inl (MonomialCaseAlong.gammaAlong n JU.N JU.ideal JU.E JU.d x)) else
     toLex (Sum.inr (genLowerValue M JU (nmOrd JU x) .refl .refl x)))
   by_cases hz : nmOrd J x.val=0
   · have hzU : nmOrd JU x=0 := hord.trans hz
     rw [if_pos hz,if_pos hzU]
     have hg := MonomialInvariantFunctorialAlong.gammaAlong_pullback_val J hhol U x J.d
     exact congrArg (fun v => toLex (Sum.inl v)) hg.symm
   · have hzU : nmOrd JU x≠0 := fun h => hz (hord.symm.trans h)
     rw [if_neg hz,if_neg hzU,hord]
     have hLow := actual_initial_companion_lower_value_on_good_open hn q ih J hhol hcl U hgood x hx
       (nmOrd J x.val) (by omega) rfl
     exact congrArg (fun v => toLex (Sum.inr v)) hLow
 change genInv M J (.refl : BlowupTower X X) x.val=genInv M JU (.refl : BlowupTower (CMfd.of (n := n) U) (CMfd.of (n := n) U)) x
 unfold genInv
 change toLex (nmOrd J x.val,genSecond M J .refl x.val)=toLex (nmOrd JU x,genSecond M JU .refl x)
 rw [hord,hsecond]

private theorem initial_all (hn : 0<n) (q : ℕ) : InitialLocality.{u} hn q := by
 induction q with
 | zero => exact initial_zero hn
 | succ q ih => exact initial_succ hn q ih

/-- A raw marked record has the literal initial invariant value of any actual good open
containing its cosupport point. The regularity and finite-generation hypotheses are local to
that good record; the original record needs only its raw holomorphic germ-span closure. -/
theorem initial_family_value_on_good_open
 (hn : 0<n) (q : ℕ) (J : MarkedIdeal n X)
 (hhol : ∀ x g,J.ideal.mem x g → HolomorphicAt n g x)
 (hcl : ∀ x g,IsInSpanAt (n := n) (J.ideal.mem x) x g → J.ideal.mem x g)
 (U : Opens X)
 (hgood : IsInvDomain (M := CMfd.of (n := n) U) q (MarkedIdeal.pullback (n := n) (Subtype.val : U→X) J))
 (x : U) (hx : x.val∈J.cosupp) :
 (CanonicalCentres.invFamily hn q).inv J .refl x.val=
 (CanonicalCentres.invFamily hn q).inv (X := CMfd.of (n := n) U) (Y := CMfd.of (n := n) U)
   (MarkedIdeal.pullback (n := n) (Subtype.val : U→X) J) .refl x := by
 exact initial_all hn q J hhol hcl U hgood x hx

end
end Hironaka.HironakaActualPointLocalInitialValues


namespace Hironaka.HironakaActualPointLocalInitialValues
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
open MarkedIdealBiholomorphism MarkedIdealRestrictOpen
open RelativePrincipalizationSpan GermIdealPullbackCalculus
open ResolutionInvariantSpec (IsInvDomain)
noncomputable section
variable {n : ℕ} {X : CMfd.{u} n}

theorem initial_step_one_value_on_good_open
 (hn : 0<n) (q : ℕ) (J : MarkedIdeal n X)
 (hhol : ∀ x g,J.ideal.mem x g → HolomorphicAt n g x)
 (hcl : ∀ x g,IsInSpanAt (n := n) (J.ideal.mem x) x g → J.ideal.mem x g)
 (U : Opens X)
 (hgood : IsInvDomain (M := CMfd.of (n := n) U) (q+1)
   (MarkedIdeal.pullback (n := n) (Subtype.val : U → X) J))
 (hmax : HomogenizedIdealAlong.IsMaximalOrderAlong
   (MarkedIdeal.pullback (n := n) (Subtype.val : U → X) J).N
   (MarkedIdeal.pullback (n := n) (Subtype.val : U → X) J).ideal
   (MarkedIdeal.pullback (n := n) (Subtype.val : U → X) J).d)
 (x : X) (hxU : x∈U) (hx : x∈J.cosupp) :
 Seq.StepOneValueMasked.stepOneInvM (CanonicalCentres.invFamily hn q) J .refl x =
 Seq.StepOneValueMasked.stepOneInvM (CanonicalCentres.invFamily hn q)
   (X := CMfd.of (n := n) U) (Y := CMfd.of (n := n) U)
   (MarkedIdeal.pullback (n := n) (Subtype.val : U → X) J) .refl ⟨x,hxU⟩ := by
 exact maximal_step_value_on_good_open hn q (initial_all hn q)
   J hhol hcl U hgood hmax x hxU hx

end
end Hironaka.HironakaActualPointLocalInitialValues

namespace Hironaka.HironakaActualPointLocalInitialValues
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism RelativePrincipalizationSpan BlowupTowers
open scoped Topology Manifold ContDiff
noncomputable section
variable {n : ℕ} {Z Z' : CMfd.{u} n}

/-- Public export of the existing raw local tangent producer. Its original
proof is unchanged; this interface does not assert a new tangent theorem. -/
theorem exists_tangent_from_good_record
    (A : MarkedIdeal n Z) (B : MarkedIdeal n Z')
    (hhol : ∀x g,A.ideal.mem x g → HolomorphicAt n g x)
    (hcl : ∀x g,IsInSpanAt (n := n) (A.ideal.mem x) x g → A.ideal.mem x g)
    (hB : B.IsWellFormed)
    (hmax : HomogenizedIdealAlong.IsMaximalOrderAlong B.N B.ideal B.d)
    (hd : 1≤A.d) (U : Opens Z) (U' : Opens Z')
    (η : U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ U')
    (hrec : MarkedIdeal.pullback (Subtype.val : U → Z) A=
      MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') B))
    (z : U) (hz : z.val∈A.cosupp) :
    ∃(O : Set Z)(v : Z → ℂ),z.val∈O ∧
      TangentDirectionAlong.IsTangentDirectionAlong A.N A.ideal A.d O v :=
  tangent_from_record A B hhol hcl hB hmax hd U U' η hrec z hz

end
end Hironaka.HironakaActualPointLocalInitialValues
