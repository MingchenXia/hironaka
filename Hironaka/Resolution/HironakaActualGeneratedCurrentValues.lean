import Hironaka.Resolution.HironakaActualGeneratedMemberHistories
import Hironaka.Resolution.HironakaActualGeneratedBarHistories
import Hironaka.Resolution.HironakaActualAlternateContactReferenceSeq
import Hironaka.Resolution.HironakaActualAnchoredOriginalHeads
import Hironaka.Resolution.HironakaActualOriginalZeroMaskWindow
import Hironaka.Resolution.HironakaActualAnchoredRestrictedReferenceHistories

/-! All recursion depths of the ACTUAL current invariant across DIFFERENT
actual generated histories. The proof is a closed mutual induction. Only
the good target is canonical; source global regularity, admissibility and
canonicality are absent. Original heads, masks, tails and every ordered
boundary prefix remain literal. The sharp driver and termination are
separate obligations. -/
set_option autoImplicit false
open Set
open scoped Manifold ContDiff
universe u
namespace Hironaka.HironakaActualGeneratedCurrentValues
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
open RelativePrincipalizationSpan HironakaActualGeneratedCurrentHistories StepOneValue CompanionReductionAlong HomogenizedIdealAlong
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ}

/-- The lower-q IH consumed by both positive-member and zero-contact
reference producers. Source testness/canonicality are absent. -/
private def FamilyCurrent (hn : 0<n) (q : ℕ) : Prop :=
 ∀{X X' Y Y' : CMfd.{u} n} (A : MarkedIdeal n X) (B : MarkedIdeal n X'),
 (∀x g,A.ideal.mem x g → HolomorphicAt n g x) →
 (∀x g,IsInSpanAt (n := n) (A.ideal.mem x) x g → A.ideal.mem x g) →
 IsInvDomain q B →
 ∀(S : BlowupTower X Y) (T : BlowupTower X' Y') (U : TopologicalSpace.Opens Y) (U' : TopologicalSpace.Opens Y')
 (η : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U'),
 Generated A B S T U U' η →
 IsCanonical B ((CanonicalCentres.invFamily hn q).inv B) T →
 ∀z : U,z.val∈(geoTransformAlong A S).cosupp →
 (CanonicalCentres.invFamily hn q).inv A S z.val=
 (CanonicalCentres.invFamily hn q).inv B T (η z).val

/-- The StepOne induction goal at q consumes FamilyCurrent q, and then
proves FamilyCurrent (q+1). It retains the ORIGINAL StepOne inputs. -/
private def StepOneCurrent (hn : 0<n) (q : ℕ) : Prop :=
 ∀{X X' Y Y' : CMfd.{u} n} (A : MarkedIdeal n X) (B : MarkedIdeal n X'),
 (∀x g,A.ideal.mem x g → HolomorphicAt n g x) →
 (∀x g,IsInSpanAt (n := n) (A.ideal.mem x) x g → A.ideal.mem x g) →
 IsInvDomain (q+1) B → IsMaximalOrderAlong B.N B.ideal B.d →
 ∀(S : BlowupTower X Y) (T : BlowupTower X' Y') (U : TopologicalSpace.Opens Y) (U' : TopologicalSpace.Opens Y')
 (η : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U'),
 Generated A B S T U U' η →
 IsCanonical B (Seq.StepOneValueMasked.stepOneInvM (CanonicalCentres.invFamily hn q) B) T →
 ∀z : U,z.val∈(geoTransformAlong A S).cosupp →
 Seq.StepOneValueMasked.stepOneInvM (CanonicalCentres.invFamily hn q) A S z.val=
 Seq.StepOneValueMasked.stepOneInvM (CanonicalCentres.invFamily hn q) B T (η z).val


open Filter TopologicalSpace
open HironakaActualGeneratedCurrentClocks HironakaActualRawRecordPullbacks HironakaActualRawOrderLocality
open HironakaActualGeneratedOriginalHeads HironakaActualGeneratedOriginalOrderMasks HironakaActualGeneratedMaskedHistories
open BlowupTowerSplit GeneralValue GeneralCanonicalTail NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderTail
open StepOneRegime
open CompanionRebase CompanionReductionAlong MonomialPartAlong InvertibleIdealQuotient
open GermIdealPullbackCalculus MarkedIdealBiholomorphism MarkedIdealRestrictOpen
noncomputable section

private theorem familyCurrent_zero (hn : 0<n) : FamilyCurrent.{u} hn 0 := by
  intro X X' Y Y' A B hA hAc hB S T U U' η H hc z hz
  rfl

private theorem gamma_from_record {Y Y' : CMfd.{u} n}
 (A : MarkedIdeal n Y) (B : MarkedIdeal n Y')
 (hA : ∀x g,A.ideal.mem x g → HolomorphicAt n g x)
 (hB : ∀x g,B.ideal.mem x g → HolomorphicAt n g x)
 (U : Opens Y) (U' : Opens Y')
 (η : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U')
 (hrec : MarkedIdeal.pullback (Subtype.val : U → Y) A=
   MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Y') B)) (z : U) :
 MonomialCaseAlong.gammaAlong n A.N A.ideal A.E A.d z.val=
   MonomialCaseAlong.gammaAlong n B.N B.ideal B.E B.d (η z).val := by
 let BU : MarkedIdeal n (CMfd.of (n := n) U') := MarkedIdeal.pullback (Subtype.val : U' → Y') B
 have hBU : ∀x g,BU.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
 have hd : A.d=B.d := congrArg MarkedIdeal.d hrec
 have hs := MonomialInvariantFunctorialAlong.gammaAlong_pullback_val A hA U z A.d
 have hm := congrArg (fun Q : MarkedIdeal n (CMfd.of (n := n) U) =>
   MonomialCaseAlong.gammaAlong n Q.N Q.ideal Q.E A.d z) hrec
 have ht₁ := MonomialInvariantFunctorialAlong.gammaAlong_pullback_diffeomorph η BU hBU z A.d
 have ht₂ := MonomialInvariantFunctorialAlong.gammaAlong_pullback_val B hB U' (η z) A.d
 exact hs.symm.trans (hm.trans (ht₁.trans (ht₂.trans (by rw [hd]))))

private theorem companion_span_closed {Z : CMfd.{u} n}
 (A : MarkedIdeal n Z) (o : ℕ) {x : Z} {g : Z → ℂ}
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
   show v w*g w=∑i,a i w*(v w*s i w)
   rw [hw,Finset.mul_sum]
   exact Finset.sum_congr rfl fun i _ => by ring

private theorem companion_hhol {Z : CMfd.{u} n} (A : MarkedIdeal n Z) (o : ℕ) :
 ∀x g,(companionOf n A o).ideal.mem x g → HolomorphicAt n g x := by
 intro x g hg
 unfold companionOf companionAlong at hg
 split_ifs at hg <;> exact hg.1

private theorem familyCurrent_succ_of_stepOneCurrent (hn : 0<n) (q : ℕ)
 (ih : StepOneCurrent.{u} hn q) : FamilyCurrent.{u} hn (q+1) := by
 classical
 intro X X' Y Y' A B hA hAc hB S T U U' η H hcan z hz
 let R := CanonicalCentres.invFamily hn q
 let M := fun {X : CMfd.{u} n} (J : MarkedIdeal n X) {Y : CMfd.{u} n} (P : BlowupTower X Y) (y : Y) =>
   Seq.StepOneValueMasked.stepOneInvM R J P y
 have hFacts := generated_order_and_cosupp hA hAc hB.isWellFormed H z
 have hzB := hFacts.2.mp hz
 have hOrd := hFacts.1
 change genInv M A S z.val=genInv M B T (η z).val
 change IsCanonical B (genInv M B) T at hcan
 by_cases hzero : nmOrd (geoTransformAlong A S) z.val=0
 · have hzeroB := hOrd.symm.trans hzero
   rw [genInv_of_nmOrd_eq_zero M A S hzero,genInv_of_nmOrd_eq_zero M B T hzeroB]
   apply congrArg (fun v : WithBot MonomialInvariant.Val =>
     toLex ((0 : ℕ),toLex (Sum.inl v : WithBot MonomialInvariant.Val ⊕ WithTop (ℕ ×ₗ WithTop (CanonicalCentres.ValTy q)))))
   exact gamma_from_record (geoTransformAlong A S) (geoTransformAlong B T)
     (holomorphic_geoTransformAlong A hA S)
     (holomorphic_geoTransformAlong B
       (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hB.isWellFormed.isCoherent hg) T)
     U U' η (H.whole_records hA hB.isWellFormed) z
 · let o := nmOrd (geoTransformAlong A S) z.val
   have ho : 1≤o := Nat.one_le_iff_ne_zero.mpr hzero
   have hyo : nmOrd (geoTransformAlong A S) z.val=o := rfl
   have hyoB : nmOrd (geoTransformAlong B T) (η z).val=o := hOrd.symm.trans hyo
   have hRun := generated_regimeRun_ordRegime hA hAc hB.isWellFormed o H z
   let j := regimeRun (OrdRegime A o) S z.val
   have hData := GeneralCanonicalTail.hasGenLowerData_of_isCanonical M
     (StepOneSeq.isMaxOrderValue_stepOneInvM (k := q+1) R hn) hn hB T H.target_test hcan
     (η z).val hzB o hyoB ho
   rw [←hRun] at hData
   obtain ⟨hMaskB,hDom,hMax,hCan,hCos⟩ := hData
   let AH := geoTransformAlong A (head S j)
   let BH := geoTransformAlong B (head T j)
   let W := ordMask AH o
   let W' := ordMask BH o
   let L := compAt A o (head S j)
   let L' := compAt B o (head T j)
   have Hcut := generated_original_head_tails hA hB.isWellFormed H j
   have hAH := holomorphic_geoTransformAlong A hA (head S j)
   have hAHc := span_closed_geoTransformAlong A hAc (head S j)
   have hBHead := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hB.isWellFormed
     (head T j) ((isGeoTestTower_iff_head_tail B T j).mp H.target_test).1
   have hTests := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (R := R) L' hDom hMax hn
     (restrict W' (tail T j)) hCan
   obtain ⟨ν,hν,Hν⟩ := exists_generated_actual_companion_reference_histories
     hAH hAHc hBHead o Hcut hTests.2.1
   have hMasks := generated_original_order_mask_traces hAH hAHc hBHead o Hcut
   have hMaskA : (tail S j).proj z.val∈W :=
     (Set.ext_iff.mp hMasks z).mpr hMaskB
   let zs : MaxLocusLocal.nestedOpens (openPreimage (tail S j) W) U :=
     ⟨⟨z.val,hMaskA⟩,z.property⟩
   let zt : openPreimage (tail T j) W' := ⟨(η z).val,hMaskB⟩
   have hPoint : (ν zs).val=zt := Subtype.ext (hν zs)
   have hL : ∀x g,L.ideal.mem x g → HolomorphicAt n g x := companion_hhol _ o
   have hLc : ∀x g,IsInSpanAt (n := n) (L.ideal.mem x) x g → L.ideal.mem x g :=
     fun _ _ hg => companion_span_closed _ o hg
   have hCosLocal := generated_order_and_cosupp hL hLc hDom.isWellFormed Hν zs
   have hzL : zs.val∈(geoTransformAlong L (restrict W (tail S j))).cosupp := by
     apply hCosLocal.2.mpr
     rw [hPoint]
     exact hCos
   have hValue := ih L L' hL hLc hDom hMax
     (restrict W (tail S j)) (restrict W' (tail T j))
     (MaxLocusLocal.nestedOpens (openPreimage (tail S j) W) U)
     (MaxLocusLocal.nestedOpens (openPreimage (tail T j) W') U') ν Hν hCan zs hzL
   rw [hPoint] at hValue
   rw [genInv_of_nmOrd_ne_zero M A S hyo (ne_of_gt ho),
     genInv_of_nmOrd_ne_zero M B T hyoB (ne_of_gt ho)]
   rw [←hRun]
   apply congrArg (fun v : WithTop (ℕ ×ₗ WithTop (CanonicalCentres.ValTy q)) =>
     toLex (o,toLex (Sum.inr v : WithBot MonomialInvariant.Val ⊕ WithTop (ℕ ×ₗ WithTop (CanonicalCentres.ValTy q)))))
   rw [genLowerValue_eq_of_mem M A hMaskA,genLowerValue_eq_of_mem M B hMaskB]
   exact congrArg (fun v : ℕ ×ₗ WithTop (CanonicalCentres.ValTy q) =>
     (v : WithTop (ℕ ×ₗ WithTop (CanonicalCentres.ValTy q)))) hValue

open HironakaActualGeneratedBarHistories HironakaActualGeneratedStepOneClocks
open HironakaActualGeneratedMemberHistories HironakaActualAnchoredCurrentHistories HironakaActualAnchoredMaskedHistories

private theorem lower_reference_value_congr (hn : 0<n) (q : ℕ)
 {X Y₀ Y : CMfd.{u} n} (J : MarkedIdeal n X) (s : ℕ)
 (T₀ : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Y) (y : Y)
 {a b : Y₀} (hab : a=b)
 (ha : T₁.proj y∈lowerMask J s T₀ a) (hb : T₁.proj y∈lowerMask J s T₀ b) :
 (CanonicalCentres.invFamily hn q).inv
     (StepOneValueMasked.lowerMarkedM J s T₀ a) (restrict (lowerMask J s T₀ a) T₁)
     (⟨y,ha⟩ : openPreimage T₁ (lowerMask J s T₀ a)) =
 (CanonicalCentres.invFamily hn q).inv
     (StepOneValueMasked.lowerMarkedM J s T₀ b) (restrict (lowerMask J s T₀ b) T₁)
     (⟨y,hb⟩ : openPreimage T₁ (lowerMask J s T₀ b)) := by
 cases hab
 rfl

private theorem stepOneCurrent_positive_of_familyCurrent (hn : 0<n) (q : ℕ)
 (ih : FamilyCurrent.{u} hn q)
 {X X' Y Y' : CMfd.{u} n} (A : MarkedIdeal n X) (B : MarkedIdeal n X')
 (hA : ∀x g,A.ideal.mem x g → HolomorphicAt n g x)
 (_hAc : ∀x g,IsInSpanAt (n := n) (A.ideal.mem x) x g → A.ideal.mem x g)
 (hB : IsInvDomain (q+1) B) (hmax : IsMaximalOrderAlong B.N B.ideal B.d)
 (S : BlowupTower X Y) (T : BlowupTower X' Y') (U : Opens Y) (U' : Opens Y')
 (η : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U')
 (H : Generated A B S T U U' η)
 (hcan : IsCanonical B (Seq.StepOneValueMasked.stepOneInvM (CanonicalCentres.invFamily hn q) B) T)
 (z : U) (hz : z.val∈(geoTransformAlong (barMarked A) S).cosupp)
 (s : ℕ) (hs : level A S z.val=s+1) (hsp : ¬IsSpecial A S z.val) :
 Seq.StepOneValueMasked.stepOneInvM (CanonicalCentres.invFamily hn q) A S z.val=
 Seq.StepOneValueMasked.stepOneInvM (CanonicalCentres.invFamily hn q) B T (η z).val := by
 classical
 let R := CanonicalCentres.invFamily hn q
 have hTests := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (R := R) B hB hmax hn T hcan
 have hCanBar := (Seq.StepOneBridge.isCanonical_iff (R := R) B hB hmax hn T).mp hcan
 have hBhol : ∀x g,B.ideal.mem x g → HolomorphicAt n g x :=
   fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hB.isWellFormed.isCoherent hg
 have Hbar := generated_bar_histories hA hBhol H hTests.1
 have hAbar : ∀x g,(barMarked A).ideal.mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
 have hBbar := StepOneLowerDomain.isWellFormed_barMarked B hB.isWellFormed
 have hFacts := generated_step_one_facts A B hB.isWellFormed Hbar
 have hsB : level B T (η z).val=s+1 := (hFacts.2 z).1.symm.trans hs
 have hspB : ¬IsSpecial B T (η z).val := fun h => hsp ((hFacts.2 z).2.1.mpr h)
 have hRecBar := Hbar.whole_records hAbar hBbar
 have hCosBar := congrArg MarkedIdeal.cosupp hRecBar
 have hBT := holomorphic_geoTransformAlong (barMarked B) (fun _ _ hg => hg.1) T
 have hAS := holomorphic_geoTransformAlong (barMarked A) hAbar S
 have hBTU : ∀x g,(MarkedIdeal.pullback (Subtype.val : U' → Y')
     (geoTransformAlong (barMarked B) T)).ideal.mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
 rw [cosupp_pullback_val _ hAS U,MarkedIdealBiholomorphism.MarkedIdeal.cosupp_pullback
   η.contMDiff η.symm.contMDiff η.apply_symm_apply η.symm_apply_apply _ hBTU,
   cosupp_pullback_val _ hBT U'] at hCosBar
 have hzB : (η z).val∈(geoTransformAlong (barMarked B) T).cosupp :=
   (Iff.of_eq (congrArg (fun E : Set U => z∈E) hCosBar)).mp hz
 have hRun := generated_step_one_regime_clocks A B hB.isWellFormed (s+1) Hbar z
 let j := regimeRun (stepRegime A (s+1)) S z.val
 have hData := Seq.StepOneCanonicalTail.hasLowerDataL_of_isCanonical (k := q+1) (R := R) B
   hB.isWellFormed hB.one_le_d hn hmax hB.dimLE T hTests.1 hCanBar (η z).val hzB hspB
 rw [hsB,←hRun] at hData
 have Hcut := generated_original_head_tails hAbar hBbar Hbar j
 obtain ⟨V₀,V₀',φ,hInitial,Hanchor⟩ :=
   HironakaActualAnchoredCurrentHistories.exists_actual_initial_anchor Hcut
 let p : V₀ := ⟨(tail S j).proj z.val,Hanchor.source_mem_initial z⟩
 have hProj : (tail T j).proj (η z).val=(φ p).val := Hanchor.projection_square z
 let D (b : (split T j).1) : Prop :=
   ∃h : (tail T j).proj (η z).val∈lowerMask B (s+1) (head T j) b,
     IsInvDomain q (StepOneValueMasked.lowerMarkedM B (s+1) (head T j) b) ∧
     IsCanonical (StepOneValueMasked.lowerMarkedM B (s+1) (head T j) b)
       (R.inv (StepOneValueMasked.lowerMarkedM B (s+1) (head T j) b))
       (restrict (lowerMask B (s+1) (head T j) b) (tail T j)) ∧
     (⟨(η z).val,h⟩ : openPreimage (tail T j) (lowerMask B (s+1) (head T j) b))∈
       (geoTransformAlong (StepOneValueMasked.lowerMarkedM B (s+1) (head T j) b)
         (restrict (lowerMask B (s+1) (head T j) b) (tail T j))).cosupp
 have hDataD : D ((tail T j).proj (η z).val) := hData
 have hData' : D (φ p).val := hProj ▸ hDataD
 obtain ⟨hMaskB,hDom,hCan,hCos⟩ := hData'
 let W := maskA A (head S j) p.val
 let W' := maskA B (head T j) (φ p).val
 let L := StepOneValueMasked.lowerMarkedM A (s+1) (head S j) p.val
 let L' := StepOneValueMasked.lowerMarkedM B (s+1) (head T j) (φ p).val
 have hBHead := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hBbar
   (head T j) ((isGeoTestTower_iff_head_tail (barMarked B) T j).mp hTests.1).1
 have hLen := generated_original_boundary_length (A := barMarked A) (B := barMarked B) Hbar
 have hLowerTest := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical R.isInvValue
   hDom (restrict W' (tail T j)) hCan
 obtain ⟨ν,hν,Hν⟩ := exists_anchored_original_member_reference_histories A B (head S j) (head T j)
   hLen hBHead hInitial Hanchor p s hLowerTest
 have hMaskInitial := original_member_mask_traces_from_records A B hLen hInitial p
 have hMasks := HironakaActualAnchoredMaskedHistories.Anchored.original_mask_traces Hanchor W W' hMaskInitial
 have hMaskA : (tail S j).proj z.val∈W := (Set.ext_iff.mp hMasks z).mpr hMaskB
 let zs : MaxLocusLocal.nestedOpens (openPreimage (tail S j) W) U := ⟨⟨z.val,hMaskA⟩,z.property⟩
 let zt : openPreimage (tail T j) W' := ⟨(η z).val,hMaskB⟩
 have hPoint : (ν zs).val=zt := Subtype.ext (hν zs)
 have hL : ∀x g,L.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
 have hLc : ∀x g,IsInSpanAt (n := n) (L.ideal.mem x) x g → L.ideal.mem x g := by
   intro x g hg
   dsimp only [L,StepOneValueMasked.lowerMarkedM,StepOneValue.lowerMarked,MarkedIdeal.pullback,
     GermIdeal.pullback] at hg ⊢
   exact IsInSpanAt.trans (fun _ hs => hs) hg
 have hCosLocal := generated_order_and_cosupp hL hLc hDom.isWellFormed Hν zs
 have hzL : zs.val∈(geoTransformAlong L (restrict W (tail S j))).cosupp := by
   apply hCosLocal.2.mpr
   rw [hPoint]
   exact hCos
 have hValue := ih L L' hL hLc hDom (restrict W (tail S j)) (restrict W' (tail T j))
   (MaxLocusLocal.nestedOpens (openPreimage (tail S j) W) U)
   (MaxLocusLocal.nestedOpens (openPreimage (tail T j) W') U') ν Hν hCan zs hzL
 rw [hPoint] at hValue
 change Seq.StepOneValueMasked.stepOneInvL R A (StepOneValueMasked.lowerMarkedM A) S z.val=
   Seq.StepOneValueMasked.stepOneInvL R B (StepOneValueMasked.lowerMarkedM B) T (η z).val
 rw [Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial R A _ S hsp,
   Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial R B _ T hspB,hs,hsB,←hRun]
 apply congrArg (fun v : WithTop (CanonicalCentres.ValTy q) => toLex (s+1,v))
 have hMaskB' : (tail T j).proj (η z).val∈lowerMask B (s+1) (head T j) ((tail T j).proj (η z).val) := by
   simpa only [hProj] using hMaskB
 have hMaskA' : (tail S j).proj z.val∈lowerMask A (s+1) (head S j) ((tail S j).proj z.val) := hMaskA
 rw [Seq.StepOneValueMasked.lowerValueL_eq_of_mem R A _
     (T₀ := head S j) (T₁ := tail S j) (y := z.val) hMaskA',
   Seq.StepOneValueMasked.lowerValueL_eq_of_mem R B _
     (T₀ := head T j) (T₁ := tail T j) (y := (η z).val) hMaskB']
 have hBVal := lower_reference_value_congr hn q B (s+1) (head T j) (tail T j) (η z).val
   hProj hMaskB' hMaskB
 have hScalar : R.inv (StepOneValueMasked.lowerMarkedM A (s+1) (head S j) ((tail S j).proj z.val))
       (restrict (lowerMask A (s+1) (head S j) ((tail S j).proj z.val)) (tail S j))
       (⟨z.val,hMaskA'⟩ : openPreimage (tail S j) (lowerMask A (s+1) (head S j) ((tail S j).proj z.val))) =
     R.inv (StepOneValueMasked.lowerMarkedM B (s+1) (head T j) ((tail T j).proj (η z).val))
       (restrict (lowerMask B (s+1) (head T j) ((tail T j).proj (η z).val)) (tail T j))
       (⟨(η z).val,hMaskB'⟩ : openPreimage (tail T j) (lowerMask B (s+1) (head T j) ((tail T j).proj (η z).val))) :=
   hValue.trans hBVal.symm
 exact congrArg (fun v : CanonicalCentres.ValTy q => (v : WithTop (CanonicalCentres.ValTy q))) hScalar

private theorem stepOneCurrent_special (hn : 0<n) (q : ℕ)
 {X X' Y Y' : CMfd.{u} n} (A : MarkedIdeal n X) (B : MarkedIdeal n X')
 (hA : ∀x g,A.ideal.mem x g → HolomorphicAt n g x)
 (hB : IsInvDomain (q+1) B) (hmax : IsMaximalOrderAlong B.N B.ideal B.d)
 (S : BlowupTower X Y) (T : BlowupTower X' Y') (U : Opens Y) (U' : Opens Y')
 (η : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U')
 (H : Generated A B S T U U' η)
 (hcan : IsCanonical B (Seq.StepOneValueMasked.stepOneInvM (CanonicalCentres.invFamily hn q) B) T)
 (z : U) (hsp : IsSpecial A S z.val) :
 Seq.StepOneValueMasked.stepOneInvM (CanonicalCentres.invFamily hn q) A S z.val=
 Seq.StepOneValueMasked.stepOneInvM (CanonicalCentres.invFamily hn q) B T (η z).val := by
 let R := CanonicalCentres.invFamily hn q
 have hTests := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (R := R) B hB hmax hn T hcan
 have hBhol : ∀x g,B.ideal.mem x g → HolomorphicAt n g x :=
   fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hB.isWellFormed.isCoherent hg
 have Hbar := generated_bar_histories hA hBhol H hTests.1
 have hFacts := (generated_step_one_facts A B hB.isWellFormed Hbar).2 z
 have hspB := hFacts.2.1.mp hsp
 change Seq.StepOneValueMasked.stepOneInvL R A (StepOneValueMasked.lowerMarkedM A) S z.val=
   Seq.StepOneValueMasked.stepOneInvL R B (StepOneValueMasked.lowerMarkedM B) T (η z).val
 rw [Seq.StepOneValueMasked.stepOneInvL_of_isSpecial R A _ S hsp,
   Seq.StepOneValueMasked.stepOneInvL_of_isSpecial R B _ T hspB,hFacts.1]

private theorem source_bar_cosupp_from_original (hn : 0<n) (q : ℕ)
 {X X' Y Y' : CMfd.{u} n} (A : MarkedIdeal n X) (B : MarkedIdeal n X')
 (hA : ∀x g,A.ideal.mem x g → HolomorphicAt n g x)
 (hAc : ∀x g,IsInSpanAt (n := n) (A.ideal.mem x) x g → A.ideal.mem x g)
 (hB : IsInvDomain (q+1) B) (hmax : IsMaximalOrderAlong B.N B.ideal B.d)
 (S : BlowupTower X Y) (T : BlowupTower X' Y') (U : Opens Y) (U' : Opens Y')
 (η : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U')
 (H : Generated A B S T U U' η)
 (hcan : IsCanonical B (Seq.StepOneValueMasked.stepOneInvM (CanonicalCentres.invFamily hn q) B) T)
 (z : U) (hz : z.val∈(geoTransformAlong A S).cosupp) :
 z.val∈(geoTransformAlong (barMarked A) S).cosupp := by
 let R := CanonicalCentres.invFamily hn q
 have hTests := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (R := R) B hB hmax hn T hcan
 have hBhol : ∀x g,B.ideal.mem x g → HolomorphicAt n g x :=
   fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hB.isWellFormed.isCoherent hg
 have Hbar := generated_bar_histories hA hBhol H hTests.1
 have hAbar : ∀x g,(barMarked A).ideal.mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
 have hBbar := StepOneLowerDomain.isWellFormed_barMarked B hB.isWellFormed
 have hRec := Hbar.whole_records hAbar hBbar
 have hC := congrArg MarkedIdeal.cosupp hRec
 have hAS := holomorphic_geoTransformAlong (barMarked A) hAbar S
 have hBT := holomorphic_geoTransformAlong (barMarked B) (fun _ _ hg => hg.1) T
 have hBTU : ∀x g,(MarkedIdeal.pullback (Subtype.val : U' → Y')
     (geoTransformAlong (barMarked B) T)).ideal.mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
 rw [cosupp_pullback_val _ hAS U,MarkedIdealBiholomorphism.MarkedIdeal.cosupp_pullback
   η.contMDiff η.symm.contMDiff η.apply_symm_apply η.symm_apply_apply _ hBTU,
   cosupp_pullback_val _ hBT U'] at hC
 have hzB := (generated_order_and_cosupp hA hAc hB.isWellFormed H z).2.mp hz
 have hzBbar : (η z).val∈(geoTransformAlong (barMarked B) T).cosupp := by
   rw [hTests.2.2]
   exact hzB
 exact (Iff.of_eq (congrArg (fun E : Set U => z∈E) hC)).mpr hzBbar

open HironakaActualAnchoredOriginalHeads HironakaActualAnchoredContactRecords
open HironakaActualAnchoredStrictCarriers HironakaActualTransportedOriginalTangent
open HironakaActualAnchoredRestrictedReferenceHistories HironakaActualOriginalZeroMaskWindow
open ContactStageKept HomogenizedGlueingTower InvDomainTowerAlong StepOneLowerDomain CoefficientIdealRestriction

private theorem stepOneCurrent_zero_of_familyCurrent (hn : 0<n) (q : ℕ)
 (ih : FamilyCurrent.{u} hn q)
 {X X' Y Y' : CMfd.{u} n} (A : MarkedIdeal n X) (B : MarkedIdeal n X')
 (hA : ∀x g,A.ideal.mem x g → HolomorphicAt n g x)
 (hAc : ∀x g,IsInSpanAt (n := n) (A.ideal.mem x) x g → A.ideal.mem x g)
 (hB : IsInvDomain (q+1) B) (hmax : IsMaximalOrderAlong B.N B.ideal B.d)
 (S : BlowupTower X Y) (T : BlowupTower X' Y') (U : Opens Y) (U' : Opens Y')
 (η : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U')
 (H : Generated A B S T U U' η)
 (hcan : IsCanonical B (Seq.StepOneValueMasked.stepOneInvM (CanonicalCentres.invFamily hn q) B) T)
 (z : U) (hz : z.val∈(geoTransformAlong (barMarked A) S).cosupp)
 (hs : level A S z.val=0) (hsp : ¬IsSpecial A S z.val) :
 Seq.StepOneValueMasked.stepOneInvM (CanonicalCentres.invFamily hn q) A S z.val=
 Seq.StepOneValueMasked.stepOneInvM (CanonicalCentres.invFamily hn q) B T (η z).val := by
 classical
 let R := CanonicalCentres.invFamily hn q
 have hTests := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (R := R) B hB hmax hn T hcan
 have hCanBar := (Seq.StepOneBridge.isCanonical_iff (R := R) B hB hmax hn T).mp hcan
 have hBhol : ∀x g,B.ideal.mem x g → HolomorphicAt n g x :=
   fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hB.isWellFormed.isCoherent hg
 have Hbar := generated_bar_histories hA hBhol H hTests.1
 have hAbar : ∀x g,(barMarked A).ideal.mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
 have hBbar := StepOneLowerDomain.isWellFormed_barMarked B hB.isWellFormed
 have hFacts := generated_step_one_facts A B hB.isWellFormed Hbar
 have hsB : level B T (η z).val=0 := (hFacts.2 z).1.symm.trans hs
 have hspB : ¬IsSpecial B T (η z).val := fun h => hsp ((hFacts.2 z).2.1.mpr h)
 have hRecBar := Hbar.whole_records hAbar hBbar
 have hCosBar := congrArg MarkedIdeal.cosupp hRecBar
 have hBT := holomorphic_geoTransformAlong (barMarked B) (fun _ _ hg => hg.1) T
 have hAS := holomorphic_geoTransformAlong (barMarked A) hAbar S
 have hBTU : ∀x g,(MarkedIdeal.pullback (Subtype.val : U' → Y')
     (geoTransformAlong (barMarked B) T)).ideal.mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
 rw [cosupp_pullback_val _ hAS U,MarkedIdealBiholomorphism.MarkedIdeal.cosupp_pullback
   η.contMDiff η.symm.contMDiff η.apply_symm_apply η.symm_apply_apply _ hBTU,
   cosupp_pullback_val _ hBT U'] at hCosBar
 have hzB : (η z).val∈(geoTransformAlong (barMarked B) T).cosupp :=
   (Iff.of_eq (congrArg (fun E : Set U => z∈E) hCosBar)).mp hz
 have hRun := generated_step_one_regime_clocks A B hB.isWellFormed 0 Hbar z
 let j := regimeRun (stepRegime A 0) S z.val
 let S₀ := head S j
 let T₀ := head T j
 let S₁ := tail S j
 let T₁ := tail T j
 have hData := Seq.StepOneCanonicalTail.hasLowerDataL_of_isCanonical (k := q+1) (R := R) B
   hB.isWellFormed hB.one_le_d hn hmax hB.dimLE T hTests.1 hCanBar (η z).val hzB hspB
 rw [hsB,←hRun] at hData
 obtain ⟨V₀,V₀',φ,hInitial,Hfull⟩ := HironakaActualAnchoredCurrentHistories.exists_actual_initial_anchor H
 obtain ⟨Vh,Vh',χ,Hhead,Htail⟩ := anchored_original_head_tails Hfull j
 let p : Vh := ⟨S₁.proj z.val,Htail.source_mem_initial z⟩
 let x : V₀ := ⟨S₀.proj p.val,Hhead.source_mem_initial p⟩
 have hxval : x.val=S.proj z.val := (congrFun (proj_eq_comp S j) z.val).symm
 have hxp : x=⟨S.proj z.val,Hfull.source_mem_initial z⟩ := Subtype.ext hxval
 have hzBraw : (η z).val∈(geoTransformAlong B T).cosupp := by
   rw [←hTests.2.2]
   exact hzB
 have hxBraw := proj_mem_cosupp_of_mem_cosupp hB.isWellFormed.isClosedSubmanifold_N
   hB.isWellFormed.isCoherent T hTests.2.1 hzBraw
 have hxB : (φ x).val∈B.cosupp := by
   rw [hxp,←Hfull.projection_square z]
   exact hxBraw
 have hBc : ∀x g,IsInSpanAt (n := n) (B.ideal.mem x) x g → B.ideal.mem x g :=
   fun _ _ hg => GermIdealTotalTransform.mem_of_isInSpanAt_mem hB.isWellFormed.isCoherent hg
 have hxA := (HironakaActualRawOrderLocality.order_and_cosupp_from_records A B hA hAc hBhol hBc
   V₀ V₀' φ hInitial x).2.mpr hxB
 have hdAB : A.d=B.d := congrArg MarkedIdeal.d hInitial
 have hdA : 1≤A.d := by rw [hdAB];exact hB.one_le_d
 let f := (tangentChoice A x.val).2
 let O := (tangentChoice A x.val).1
 let Og := (Subtype.val : V₀' → X') '' ((φ.symm) ⁻¹' ((Subtype.val : V₀ → X) ⁻¹' (O : Set X)))
 let g := transportedInitialFunction V₀ V₀' φ f
 have hTangent := transported_original_chosen_tangent_from_good_record A B hA hAc hB.isWellFormed hmax
   hdA V₀ V₀' φ hInitial x hxA
 have hg : TangentDirectionAlong.IsTangentDirectionAlong B.N B.ideal B.d Og g := hTangent.2
 have hHeadProj : T₀.proj (T₁.proj (η z).val)=(φ x).val := by
   rw [Htail.projection_square z]
   exact Hhead.projection_square p
 have hOrigBar := bar_records_from_original_records A B hA hBhol V₀ V₀' φ hInitial
 have hHeadTest := ((isGeoTestTower_iff_head_tail (barMarked B) T j).mp hTests.1).1
 have HbarHead := Hhead.to_generated (barMarked A) (barMarked B) hOrigBar hHeadTest
 let Wg : Opens (split T j).1 :=
   ⟨((maskB B T₀ (T₁.proj (η z).val) : Set (split T j).1) ∩ T₀.proj ⁻¹' Og) ∩ (Vh' : Set (split T j).1),
     ((maskB B T₀ (T₁.proj (η z).val)).isOpen.inter
       (hg.isOpen.preimage T₀.contMDiff_proj.continuous)).inter Vh'.isOpen⟩
 have hMaskTarget := hData.choose
 have hzOg : T₀.proj (T₁.proj (η z).val)∈Og := by rw [hHeadProj];exact hTangent.1
 have hzWg : T₁.proj (η z).val∈Wg :=
   ⟨⟨hMaskTarget,hzOg⟩,Htail.target_mem_initial (η z)⟩
 have hWg : (Wg : Set (split T j).1)⊆T₀.proj ⁻¹' Og := fun _ h => h.1.2
 have hWgE : ∀K∈origMembers B T₀,Disjoint (Wg : Set (split T j).1) K := by
   intro K hK
   exact Set.disjoint_left.mpr fun y hy hyK => (interior_subset hy.1.1).2.1 K hK hyK
 have htAppend : IsGeoTestTower (barMarked B) (T₀.append T₁) := by
   rw [head_append_tail]
   exact hTests.1
 have hzAppend : (η z).val∈(geoTransformAlong (barMarked B) (T₀.append T₁)).cosupp := by
   rw [head_append_tail]
   exact hzB
 obtain ⟨Vg,hzg,hVgWg,hDom,hCan,hCos,hAlt,_hAltGeometry⟩ :=
   Seq.HironakaActualAlternateContactReference.exists_alternate_contact_reference R B hB.isWellFormed
     hB.one_le_d T₀ T₁ htAppend (η z).val hzAppend hData Og g hg Wg hzWg hWg hWgE
 have hMaskVg : Vg≤maskB B T₀ (T₁.proj (η z).val) := fun _ h => (hVgWg h).1.1
 have hDomainVg : (Vg : Set (split T j).1)⊆T₀.proj ⁻¹' Og := fun _ h => (hVgWg h).1.2
 obtain ⟨Vs,_hVsU,hVsMask,hVsTrace⟩ := exists_original_source_zero_mask_window A B hB.isWellFormed
   Hhead HbarHead p.val (T₁.proj (η z).val) Vg hMaskVg hDomainVg
 have hpVg : (χ p).val∈Vg := by rw [←Htail.projection_square z];exact hzg
 have hpVs : p.val∈Vs := (Set.ext_iff.mp hVsTrace p).mp hpVg
 have hpMask : p.val∈maskB A S₀ p.val := hVsMask hpVs
 let KA := withN (HomogenizedIdealAlong.coeffMarkedAlong (geoTransformAlong (barMarked A) S₀))
   (strictAlong S₀ (A.N∩{x | f x=0}))
 let KB := withN (HomogenizedIdealAlong.coeffMarkedAlong (geoTransformAlong (barMarked B) T₀))
   (strictAlong T₀ (B.N∩{x | g x=0}))
 have hContact := anchored_original_contact_records A B hA hB.isWellFormed hInitial Hhead HbarHead f
 have hKA : ∀x v,KA.ideal.mem x v → HolomorphicAt n v x := fun _ _ hv => hv.1
 have hKB : ∀x v,KB.ideal.mem x v → HolomorphicAt n v x := fun _ _ hv => hv.1
 obtain ⟨Us,Ut,hUs,_hUt,hzUs,_hzUt,ν,hν,Hν⟩ := exists_actual_restricted_reference_histories
   KA KB hKA hKB hContact Htail (maskB A S₀ p.val) Vg z hpMask hzg
   (ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical R.isInvValue hDom (restrict Vg T₁) hCan)
 let L := StepOneValueMasked.lowerMarkedM A 0 S₀ p.val
 let L' := contactMarkedKept B g T₀ Vg
 let zs : MaxLocusLocal.nestedOpens (openPreimage S₁ (maskB A S₀ p.val)) Us := ⟨⟨z.val,hpMask⟩,hzUs⟩
 let zt : openPreimage T₁ Vg := ⟨(η z).val,hzg⟩
 have hPoint : (ν zs).val=zt := Subtype.ext (hν zs)
 have hL : ∀x v,L.ideal.mem x v → HolomorphicAt n v x := fun _ _ hv => hv.1
 have hLc : ∀x v,IsInSpanAt (n := n) (L.ideal.mem x) x v → L.ideal.mem x v := by
   intro x v hv
   dsimp only [L,StepOneValueMasked.lowerMarkedM,StepOneValueMasked.lowerMarkedB,MarkedIdeal.pullback,GermIdeal.pullback] at hv ⊢
   exact IsInSpanAt.trans (fun _ hs => hs) hv
 have hCosLocal := generated_order_and_cosupp hL hLc hDom.isWellFormed Hν zs
 have hzL : zs.val∈(geoTransformAlong L (restrict (maskB A S₀ p.val) S₁)).cosupp := by
   apply hCosLocal.2.mpr
   rw [hPoint]
   exact hCos
 have hValue := ih L L' hL hLc hDom (restrict (maskB A S₀ p.val) S₁) (restrict Vg T₁)
   (MaxLocusLocal.nestedOpens (openPreimage S₁ (maskB A S₀ p.val)) Us)
   (MaxLocusLocal.nestedOpens (openPreimage T₁ Vg) Ut) ν Hν hCan zs hzL
 rw [hPoint] at hValue
 change Seq.StepOneValueMasked.stepOneInvL R A (StepOneValueMasked.lowerMarkedM A) S z.val=
   Seq.StepOneValueMasked.stepOneInvL R B (StepOneValueMasked.lowerMarkedM B) T (η z).val
 rw [Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial R A _ S hsp,
   Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial R B _ T hspB,hs,hsB,←hRun]
 apply congrArg (fun v : WithTop (CanonicalCentres.ValTy q) => toLex ((0 : ℕ),v))
 rw [Seq.StepOneValueMasked.lowerValueL_eq_of_mem R A _
   (s := 0) (T₀ := S₀) (T₁ := S₁) (y := z.val) hpMask]
 exact (congrArg (fun v : CanonicalCentres.ValTy q => (v : WithTop (CanonicalCentres.ValTy q))) hValue).trans hAlt.symm

private theorem stepOneCurrent_of_familyCurrent (hn : 0<n) (q : ℕ)
 (ih : FamilyCurrent.{u} hn q) : StepOneCurrent.{u} hn q := by
 intro X X' Y Y' A B hA hAc hB hmax S T U U' η H hcan z hz
 have hzBar := source_bar_cosupp_from_original hn q A B hA hAc hB hmax S T U U' η H hcan z hz
 by_cases hsp : IsSpecial A S z.val
 · exact stepOneCurrent_special hn q A B hA hB hmax S T U U' η H hcan z hsp
 · by_cases hs : level A S z.val=0
   · exact stepOneCurrent_zero_of_familyCurrent hn q ih A B hA hAc hB hmax S T U U' η H hcan z hzBar hs hsp
   · obtain ⟨s,hs'⟩ := Nat.exists_eq_succ_of_ne_zero hs
     exact stepOneCurrent_positive_of_familyCurrent hn q ih A B hA hAc hB hmax S T U U' η H hcan z hzBar s hs' hsp

private theorem familyCurrent_all (hn : 0<n) : ∀q : ℕ,FamilyCurrent.{u} hn q := by
 intro q
 induction q with
 | zero => exact familyCurrent_zero hn
 | succ q ih =>
   exact familyCurrent_succ_of_stepOneCurrent hn q (stepOneCurrent_of_familyCurrent hn q ih)

/-- All actual recursion depths on different generated histories. Source
regularity remains local; only the good target history is canonical. -/
theorem actual_family_current_values
 (hn : 0<n) (q : ℕ)
 {X X' Y Y' : CMfd.{u} n} (A : MarkedIdeal n X) (B : MarkedIdeal n X')
 (hA : ∀x g,A.ideal.mem x g → HolomorphicAt n g x)
 (hAc : ∀x g,IsInSpanAt (n := n) (A.ideal.mem x) x g → A.ideal.mem x g)
 (hB : IsInvDomain q B)
 (S : BlowupTower X Y) (T : BlowupTower X' Y') (U : Opens Y) (U' : Opens Y')
 (η : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U')
 (H : Generated A B S T U U' η)
 (hcan : IsCanonical B ((CanonicalCentres.invFamily hn q).inv B) T)
 (z : U) (hz : z.val∈(geoTransformAlong A S).cosupp) :
 (CanonicalCentres.invFamily hn q).inv A S z.val=(CanonicalCentres.invFamily hn q).inv B T (η z).val :=
 familyCurrent_all hn q A B hA hAc hB S T U U' η H hcan z hz

/-- Complete actual StepOne values at every lower recursion depth. The
incoming history comparison is for the ORIGINAL raw records, not merely
for their bar records; bar geometry is internally produced. -/
theorem actual_step_one_current_values
 (hn : 0<n) (q : ℕ)
 {X X' Y Y' : CMfd.{u} n} (A : MarkedIdeal n X) (B : MarkedIdeal n X')
 (hA : ∀x g,A.ideal.mem x g → HolomorphicAt n g x)
 (hAc : ∀x g,IsInSpanAt (n := n) (A.ideal.mem x) x g → A.ideal.mem x g)
 (hB : IsInvDomain (q+1) B) (hmax : IsMaximalOrderAlong B.N B.ideal B.d)
 (S : BlowupTower X Y) (T : BlowupTower X' Y') (U : Opens Y) (U' : Opens Y')
 (η : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U')
 (H : Generated A B S T U U' η)
 (hcan : IsCanonical B (Seq.StepOneValueMasked.stepOneInvM (CanonicalCentres.invFamily hn q) B) T)
 (z : U) (hz : z.val∈(geoTransformAlong A S).cosupp) :
 Seq.StepOneValueMasked.stepOneInvM (CanonicalCentres.invFamily hn q) A S z.val=
 Seq.StepOneValueMasked.stepOneInvM (CanonicalCentres.invFamily hn q) B T (η z).val :=
 stepOneCurrent_of_familyCurrent hn q (familyCurrent_all hn q)
   A B hA hAc hB hmax S T U U' η H hcan z hz

/-- Numerical transport with EVERY ordered old/born boundary prefix. -/
theorem actual_current_values_and_ordered_boundary_prefixes
 (hn : 0<n) (q : ℕ)
 {X X' Y Y' : CMfd.{u} n} (A : MarkedIdeal n X) (B : MarkedIdeal n X')
 (hA : ∀x g,A.ideal.mem x g → HolomorphicAt n g x)
 (hAc : ∀x g,IsInSpanAt (n := n) (A.ideal.mem x) x g → A.ideal.mem x g)
 (hB : IsInvDomain q B)
 (S : BlowupTower X Y) (T : BlowupTower X' Y') (U : Opens Y) (U' : Opens Y')
 (η : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U')
 (H : Generated A B S T U U' η)
 (hcan : IsCanonical B ((CanonicalCentres.invFamily hn q).inv B) T)
 (z : U) (hz : z.val∈(geoTransformAlong A S).cosupp) :
 (CanonicalCentres.invFamily hn q).inv A S z.val=(CanonicalCentres.invFamily hn q).inv B T (η z).val ∧
 ∀m : ℕ,((geoTransformAlong A S).E.take m).map ((Subtype.val : U → Y) ⁻¹' ·)=
   (((geoTransformAlong B T).E.take m).map ((Subtype.val : U' → Y') ⁻¹' ·)).map (η ⁻¹' ·) :=
 ⟨actual_family_current_values hn q A B hA hAc hB S T U U' η H hcan z hz,
   fun m => generated_boundary_prefixes hA hB.isWellFormed H m⟩

end
end Hironaka.HironakaActualGeneratedCurrentValues
