import Hironaka.Resolution.HironakaActualOriginalLowerLocalTests
import Hironaka.Resolution.HironakaActualProjectionTestRecord
import Hironaka.Resolution.HironakaSmoothSubmersionRelativeDifferentialIdeals
import Hironaka.Resolution.HironakaActualMixedPullbackNormalization

/-! Genuine projection comparison of the ORIGINAL fixed lower heads.
The dimension-parametric private static arguments reproduce the proved
OriginalLowerLocalTests lineage with zero separate engine credit. Only the
original Q/H caller is public; source bounds and projected equivalence are
internally derived. No log-boundary operator or current-ideal reset.
Blueprint FIRST: `hironaka-actual-original-lower-head-projection-tests.tex`. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualOriginalLowerHeadProjectionTests
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan IdealWeightPowers GermIdealOrder GermIdealPullbackCalculus IdealOrderArithmetic
  RestrictedIdealWeight RestrictedIdealExtension RestrictLeCalculus
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong
  MarkedIdealOperationsAlong.MarkedIdeal MarkedIdealEquivalence.MarkedIdeal
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower HomogenizedGlueing MarkedIdealBiholomorphism
  HomogenizedIdealAlong HomogenizedIdealAlongTower DerivativeIdealAlong DerivativeIdealAlongCoherent
  CoefficientIdeal CoefficientIdealRestriction TangentDirectionAlong
  ResolutionInvariantSpec InvDomainTowerAlong MarkedIdealRestrictOpen
  HironakaActualPowerBoundaryExponents HironakaActualOriginalPowerTransform
  HironakaActualTrueMarkCoefficientHistorySandwich
  HironakaActualOriginalHistoricalBarWeightedThreshold
  HironakaActualOriginalCoefficientHistoryAlong HironakaActualOriginalTrueMarkMaskCompanions
  HironakaActualOriginalCommonMaskRawOrder
  StepOneValue StepOneValueMasked StepOneLowerDomain ContactStageKept
  CoefficientIdealAlongRestrictionFull HironakaEmbeddedAnalytic
open HironakaActualOriginalLowerLocalTests HironakaActualProjectionTestRecord
  HironakaAuxiliaryGraphGeometry HironakaActualMixedPullbackNormalization
open scoped ProductComplexManifold
variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem hol {A : CMfd.{u} n} {I : GermIdeal n A} (h : I.IsCoherent) :
    ∀x f,I.mem x f→HolomorphicAt n f x := fun _ _ hf=>GermIdeal.IsCoherent.holomorphicAt_mem h hf

private theorem carrier {A B : MarkedIdeal n X} (hN : A.N=B.N) (T : BlowupTower X Y) :
    (geoTransformAlong A T).N=(geoTransformAlong B T).N := by
  rw [N_geoTransformAlong,N_geoTransformAlong,hN]

private theorem current_cosupp_subset {A B : MarkedIdeal n X} (hN : A.N=B.N)
    (hd : A.d=B.d) (h : RestrictLe A.N A.ideal B.ideal) : B.cosupp⊆A.cosupp := by
  intro x hx
  change x∈cosupport n A.N A.ideal A.d
  apply cosupport_subset_of_restrictLe h A.d
  simpa only [MarkedIdeal.cosupp,hN,hd] using hx

private theorem domination_cosupp {A B : MarkedIdeal n X}
    (hN : IsClosedSubmanifold n A.N) (hcA : A.ideal.IsCoherent) (hcB : B.ideal.IsCoherent)
    (hABN : A.N=B.N) (hABE : A.E=B.E) (hABd : A.d=B.d)
    (hLe : RestrictLe A.N A.ideal B.ideal) (T : BlowupTower X Y) (hT : IsGeoTestTower B T) :
    (geoTransformAlong B T).cosupp⊆(geoTransformAlong A T).cosupp :=
  current_cosupp_subset (carrier hABN T) (by simpa only [d_geoTransformAlong] using hABd)
    (restricted_test_domination hN hcA hcB hABN hABE hABd hLe T hT).2

private theorem power_weak {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    {e : ℕ} (he : 1≤e) : WEquiv M (powerMarked M e) := by
  refine ⟨rfl,fun T=>⟨(original_power_test_iff M hM he T).symm,fun hT=>?_⟩⟩
  exact ((original_power_transform M hM e he T hT).2.cosupp_eq.trans
    (powerMarked_cosupp _ (isInvDomain_geoTransformAlong hM T hT) he)).symm

private theorem recoded_coherent (M : MarkedIdeal n X) (hN : IsClosedSubmanifold n M.N)
    (hI : M.ideal.IsCoherent) (d : ℕ) : (recodedCoefficient M d).ideal.IsCoherent :=
  isCoherent_coeffMarkedAlong (𝔪:={M with d:=d}) hI hN

private theorem zeroth (M : MarkedIdeal n X) {d : ℕ} (hd : 1≤d) :
    (idealPow M.ideal (sumExp (fun j=>d-j) d 0)).Le (recodedCoefficient M d).ideal := by
  intro x f hf
  change IsInSpanAt (n:=n) (fun s=>∃i,i<d ∧
    (idealPow (iterDerivIdealAlong M.N M.ideal i) (sumExp (fun j=>d-j) d i)).mem x s) x f
  exact InvertibleIdealQuotient.isInSpanAt_self ⟨0,hd,hf⟩ (holomorphicAt_of_mem_idealPow hf)

private theorem exponent_bound {d m e p i : ℕ} (hd : 0<d) (hm : d≤m)
    (hi : i<d) (hBal : (d-i)*p=d*e) : e*m≤(m-i)*p := by
  have hep : e≤p:=by
    have hde : d*e≤d*p:=by
      rw [←hBal]
      exact Nat.mul_le_mul_right p (Nat.sub_le d i)
    exact Nat.le_of_mul_le_mul_left hde hd
  calc
    e*m=d*e+(m-d)*e:=by rw [←Nat.add_mul,Nat.add_sub_of_le hm,Nat.mul_comm]
    _=(d-i)*p+(m-d)*e:=by rw [hBal]
    _≤(d-i)*p+(m-d)*p:=Nat.add_le_add_left (Nat.mul_le_mul_left (m-d) hep) _
    _=(m-i)*p:=by rw [←Nat.add_mul];congr 1;omega

private theorem recoded_upper_cosupp (M : MarkedIdeal n X) {d : ℕ} (hd : 1≤d) (hm : d≤M.d)
    (hI : M.ideal.IsCoherent) : M.cosupp⊆(recodedCoefficient M d).cosupp := by
  intro x hx
  change x∈cosupport n M.N M.ideal M.d at hx
  let e:=sumExp (fun j=>d-j) d 0
  change x∈cosupport n M.N
    (finSumIdeal (fun i=>idealPow (iterDerivIdealAlong M.N M.ideal i)
      (sumExp (fun j=>d-j) d i)) d) (e*M.d)
  apply (mem_cosupport_finSumIdeal (fun _ _ _ _ h=>holomorphicAt_of_mem_idealPow h)).mpr
  refine ⟨hx.1,?_⟩
  intro i hi
  have hDer : x∈cosupport n M.N (iterDerivIdealAlong M.N M.ideal i) (M.d-i):=by
    apply cosupport_add_subset_cosupport_iterDerivIdealAlong (hol hI) (M.d-i) i
    simpa only [Nat.sub_add_cancel (lt_of_lt_of_le hi hm).le] using hx
  have hPow:=cosupport_subset_cosupport_idealPow (M.d-i) (sumExp (fun j=>d-j) d i) hDer
  apply cosupport_anti (exponent_bound (show 0<d from hd) hm hi ?_) hPow
  exact (mul_sumExp (fun j=>d-j) hi).trans
    (by simpa only [Nat.sub_zero] using (mul_sumExp (fun j=>d-j) (show 0<d from hd) (i:=0)).symm)

private theorem recoded_history_cosupp {k : ℕ} (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) {d : ℕ} (hd : 1≤d) (hm : d≤M.d)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T) :
    (geoTransformAlong (recodedCoefficient M d) T).cosupp=(geoTransformAlong M T).cosupp := by
  obtain ⟨hBT,hN,_hE,hD,hLow,hHigh,_hLen⟩:=recoded_coefficient_history_sandwich M hM d hd hm T hT
  have hC:=isInvDomain_geoTransformAlong hM T hT
  have he : 1≤sumExp (fun j=>d-j) d 0:=one_le_sumExp (fun j hj=>by omega) 0
  have hPower : (powerMarked (geoTransformAlong M T) (sumExp (fun j=>d-j) d 0)).cosupp=
      (geoTransformAlong M T).cosupp:=powerMarked_cosupp _ hC he
  apply Subset.antisymm
  · intro x hx
    rw [←hPower]
    apply current_cosupp_subset (A:=powerMarked (geoTransformAlong M T) (sumExp (fun j=>d-j) d 0))
      (B:=geoTransformAlong (recodedCoefficient M d) T) hN.symm ?_ hLow hx
    rw [hD]
    change (geoTransformAlong M T).d*_=_
    rw [d_geoTransformAlong,Nat.mul_comm]
  · have hDcur : d≤(geoTransformAlong M T).d:=by simpa only [d_geoTransformAlong] using hm
    have hRec:=recoded_upper_cosupp (geoTransformAlong M T) hd hDcur hC.isWellFormed.isCoherent
    intro x hx
    have hz:=hRec hx
    change x∈cosupport n (geoTransformAlong (recodedCoefficient M d) T).N _ _
    rw [hN,hD]
    apply cosupport_subset_of_restrictLe hHigh _
    change x∈cosupport n (geoTransformAlong M T).N
      (recodedCoefficient (geoTransformAlong M T) d).ideal
      (sumExp (fun j=>d-j) d 0*(geoTransformAlong M T).d) at hz
    simpa only [recodedCoefficient,coeffMarkedAlong,msum,derivMarkedAlong,d_geoTransformAlong] using hz

private theorem recoded_weak {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    {d : ℕ} (hd : 1≤d) (hm : d≤M.d) : WEquiv M (recodedCoefficient M d) := by
  let e:=sumExp (fun j=>d-j) d 0
  have he : 1≤e:=one_le_sumExp (fun j hj=>by omega) 0
  have hLow:=restrictLe_of_le (W:=M.N) (recoded_coherent M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent d) (zeroth M hd)
  refine ⟨rfl,fun T=>⟨⟨fun hT=>(recoded_coefficient_history_sandwich M hM d hd hm T hT).1,?_⟩,
    fun hT=>(recoded_history_cosupp M hM hd hm T hT).symm⟩⟩
  intro hB
  have hP:=(restricted_test_domination (A:=powerMarked M e)
    hM.isWellFormed.isClosedSubmanifold_N (isCoherent_idealPow hM.isWellFormed.isCoherent e)
    (recoded_coherent M hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent d)
    rfl rfl (Nat.mul_comm _ _) hLow T hB).1
  exact (original_power_test_iff M hM he T).mp hP

private theorem weak_between {A B C : MarkedIdeal n X}
    (hN : IsClosedSubmanifold n A.N) (hA : A.ideal.IsCoherent) (hB : B.ideal.IsCoherent)
    (hC : C.ideal.IsCoherent) (hABN : A.N=B.N) (hACN : A.N=C.N)
    (hABE : A.E=B.E) (hACE : A.E=C.E) (hABd : A.d=B.d) (hACd : A.d=C.d)
    (hLow : RestrictLe A.N A.ideal B.ideal) (hHigh : RestrictLe B.N B.ideal C.ideal)
    (hWeak : WEquiv A C) : WEquiv A B := by
  have hBCN:=hABN.symm.trans hACN
  have hBCE:=hABE.symm.trans hACE
  have hBCd:=hABd.symm.trans hACd
  refine ⟨hABE,fun T=>⟨?_,?_⟩⟩
  · exact ⟨fun hT=>(restricted_test_domination (hABN ▸ hN) hB hC hBCN hBCE hBCd
      hHigh T ((hWeak.2 T).1.mp hT)).1,
      fun hT=>(restricted_test_domination hN hA hB hABN hABE hABd hLow T hT).1⟩
  · intro hAT
    have hCT:=(hWeak.2 T).1.mp hAT
    have hBT:=(restricted_test_domination (hABN ▸ hN) hB hC hBCN hBCE hBCd hHigh T hCT).1
    apply Subset.antisymm
    · rw [(hWeak.2 T).2 hAT]
      exact domination_cosupp (hABN ▸ hN) hB hC hBCN hBCE hBCd hHigh T hCT
    · exact domination_cosupp hN hA hB hABN hABE hABd hLow T hBT

private theorem static_recoded_bounds {k : ℕ} (M B : MarkedIdeal n X)
    (hM : IsInvDomain k M) (hB : B.ideal.IsCoherent) {d : ℕ} (hd : 1≤d) (hm : d≤M.d)
    (hN : M.N=B.N) (hE : M.E=B.E)
    (hD : B.d=sumExp (fun j=>d-j) d 0*M.d)
    (hLow : RestrictLe M.N (idealPow M.ideal (sumExp (fun j=>d-j) d 0)) B.ideal)
    (hHigh : RestrictLe M.N B.ideal (recodedCoefficient M d).ideal) : WEquiv M B := by
  let e:=sumExp (fun j=>d-j) d 0
  have he : 1≤e:=one_le_sumExp (fun j hj=>by omega) 0
  have hP:=power_weak M hM he
  have hC:=recoded_weak M hM hd hm
  have hHigh' : RestrictLe B.N B.ideal (recodedCoefficient M d).ideal:=by rw [←hN];exact hHigh
  exact hP.trans (weak_between (A:=powerMarked M e) (B:=B) (C:=recodedCoefficient M d)
    hM.isWellFormed.isClosedSubmanifold_N (isCoherent_idealPow hM.isWellFormed.isCoherent e)
    hB (recoded_coherent M hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent d)
    hN rfl hE rfl (by rw [hD];exact Nat.mul_comm _ _) (Nat.mul_comm _ _)
    hLow hHigh' (hP.symm.trans hC))


private theorem projection_deriv (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent)
    (hN : IsClosedSubmanifold n M.N) (j : ℕ) :
    projectionTest (derivMarkedAlong M j) = derivMarkedAlong (projectionTest M) j := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ rfl
  exact HironakaSmoothSubmersionRelativeDifferentialIdeals.pullback_iterDerivIdealAlong (X := X) (Y := projectionAmbient X)
    (isSubmersion_fst (n := n) (m := 1) (X := X) (Y := ComplexModel 1)) M.ideal hI M.N hN j

private theorem projection_hom (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent)
    (hN : IsClosedSubmanifold n M.N) :
    projectionTest (homMarkedAlong M) = homMarkedAlong (projectionTest M) := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ rfl
  exact congrArg (fun A => A.ideal)
    (HironakaSmoothSubmersionRelativeDifferentialIdeals.pullback_homMarkedAlong (X := X) (Y := projectionAmbient X)
      (isSubmersion_fst (n := n) (m := 1) (X := X) (Y := ComplexModel 1)) M hI hN)

private theorem projection_coefficient (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent)
    (hN : IsClosedSubmanifold n M.N) :
    projectionTest (coeffMarkedAlong M) = coeffMarkedAlong (projectionTest M) := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ rfl
  exact congrArg (fun A => A.ideal)
    (HironakaSmoothSubmersionRelativeDifferentialIdeals.pullback_coeffMarkedAlong (X := X) (Y := projectionAmbient X)
      (isSubmersion_fst (n := n) (m := 1) (X := X) (Y := ComplexModel 1)) M hI hN)

private theorem projection_recoded (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent)
    (hN : IsClosedSubmanifold n M.N) (d : ℕ) :
    projectionTest (recodedCoefficient M d) = recodedCoefficient (projectionTest M) d := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ rfl
  exact congrArg (fun A => A.ideal) (projection_coefficient (X := X) {M with d := d} hI hN)

private theorem projection_power (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent) (e : ℕ) :
    projectionTest (powerMarked M e) = powerMarked (projectionTest M) e := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ rfl
  exact HironakaSmoothSubmersionCoefficientIdeals.pullback_idealPow
    (ProductComplexManifold.contMDiff_fst (n := n) (m := 1) (X := X) (Y := ComplexModel 1)) hI e

private theorem projection_withN (M : MarkedIdeal n X) (S : Set X) :
    projectionTest (withN M S) = withN (projectionTest M) ((Prod.fst : projectionAmbient X → X) ⁻¹' S) := rfl

private theorem projected_static_recoded_bounds {k : ℕ} (M B : MarkedIdeal n X)
    (hM : IsInvDomain k M) (hB : B.ideal.IsCoherent) {d : ℕ} (hd : 1≤d) (hm : d≤M.d)
    (hN : M.N=B.N) (hE : M.E=B.E)
    (hD : B.d=sumExp (fun j=>d-j) d 0*M.d)
    (hLow : RestrictLe M.N (idealPow M.ideal (sumExp (fun j=>d-j) d 0)) B.ideal)
    (hHigh : RestrictLe M.N B.ideal (recodedCoefficient M d).ideal) :
    WEquiv (projectionTest M) (projectionTest B) := by
  have hf := isSubmersion_fst (n := n) (m := 1) (X := X) (Y := ComplexModel 1)
  have hMP := projection_test_isInvDomain M hM
  have hBP := isCoherent_pullback hf.contMDiff hB
  have hLowP := cross_dimension_restrictLe_pullback (m := n+1) (Y := projectionAmbient X)
    (f := (Prod.fst : projectionAmbient X → X)) (V := M.N)
    (W := (Prod.fst : projectionAmbient X → X) ⁻¹' M.N)
    hf.contMDiff (fun _ hz => hz) hB hLow
  rw [HironakaSmoothSubmersionCoefficientIdeals.pullback_idealPow hf.contMDiff hM.isWellFormed.isCoherent] at hLowP
  have hHighP := cross_dimension_restrictLe_pullback (m := n+1) (Y := projectionAmbient X)
    (f := (Prod.fst : projectionAmbient X → X)) (V := M.N)
    (W := (Prod.fst : projectionAmbient X → X) ⁻¹' M.N)
    hf.contMDiff (fun _ hz => hz)
    (recoded_coherent M hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent d) hHigh
  have hRec := congrArg (fun A => A.ideal)
    (projection_recoded M hM.isWellFormed.isCoherent hM.isWellFormed.isClosedSubmanifold_N d)
  change GermIdeal.pullback (m := n+1) Prod.fst (recodedCoefficient M d).ideal =
    (recodedCoefficient (projectionTest M) d).ideal at hRec
  rw [hRec] at hHighP
  apply static_recoded_bounds (projectionTest M) (projectionTest B) hMP hBP hd hm
  · change Prod.fst ⁻¹' M.N = Prod.fst ⁻¹' B.N
    rw [hN]
  · change M.E.map _ ++ [horizontal X] = B.E.map _ ++ [horizontal X]
    rw [hE]
  · exact hD
  · exact hLowP
  · exact hHighP

private theorem projected_static_hom_bounds {k : ℕ} (M B : MarkedIdeal n X)
    (hM : IsInvDomain k M) (hB : B.ideal.IsCoherent)
    (hN : M.N=B.N) (hE : M.E=B.E) (hD : M.d=B.d)
    (hLow : RestrictLe M.N M.ideal B.ideal)
    (hHigh : RestrictLe M.N B.ideal (homMarkedAlong M).ideal) :
    WEquiv (projectionTest M) (projectionTest B) := by
  have hf := isSubmersion_fst (n := n) (m := 1) (X := X) (Y := ComplexModel 1)
  have hMP := projection_test_isInvDomain M hM
  have hBP := isCoherent_pullback hf.contMDiff hB
  have hLowP := cross_dimension_restrictLe_pullback (m := n+1) (Y := projectionAmbient X)
    (f := (Prod.fst : projectionAmbient X → X)) (V := M.N)
    (W := (Prod.fst : projectionAmbient X → X) ⁻¹' M.N)
    hf.contMDiff (fun _ hz => hz) hB hLow
  have hHighP := cross_dimension_restrictLe_pullback (m := n+1) (Y := projectionAmbient X)
    (f := (Prod.fst : projectionAmbient X → X)) (V := M.N)
    (W := (Prod.fst : projectionAmbient X → X) ⁻¹' M.N)
    hf.contMDiff (fun _ hz => hz)
    (isCoherent_homMarkedAlong hM.isWellFormed.isCoherent hM.isWellFormed.isClosedSubmanifold_N) hHigh
  have hHom := congrArg (fun A => A.ideal)
    (projection_hom M hM.isWellFormed.isCoherent hM.isWellFormed.isClosedSubmanifold_N)
  change GermIdeal.pullback (m := n+1) Prod.fst (homMarkedAlong M).ideal =
    (homMarkedAlong (projectionTest M)).ideal at hHom
  rw [hHom] at hHighP
  have hNP : (projectionTest M).N=(projectionTest B).N := by
    change Prod.fst ⁻¹' M.N = Prod.fst ⁻¹' B.N
    rw [hN]
  have hEP : (projectionTest M).E=(projectionTest B).E := by
    change M.E.map _ ++ [horizontal X] = B.E.map _ ++ [horizontal X]
    rw [hE]
  have hHighB : RestrictLe (projectionTest B).N (projectionTest B).ideal
      (homMarkedAlong (projectionTest M)).ideal := by rw [←hNP]; exact hHighP
  exact weak_between hMP.isWellFormed.isClosedSubmanifold_N hMP.isWellFormed.isCoherent hBP
    (isCoherent_homMarkedAlong hMP.isWellFormed.isCoherent hMP.isWellFormed.isClosedSubmanifold_N)
    hNP rfl hEP rfl hD rfl hLowP hHighB
    (homAlong_wEquiv (projectionTest M) hMP.isWellFormed.isClosedSubmanifold_N
      hMP.isWellFormed.isCoherent hMP.one_le_d).symm

private theorem pullback_le {A B : GermIdeal n X} {N : Set X} (hB : B.IsCoherent)
    (h : RestrictLe N A B) (W : Opens X) :
    RestrictLe ((Subtype.val : W→X) ⁻¹' N)
      (GermIdeal.pullback (m:=n) (Subtype.val : W→X) A)
      (GermIdeal.pullback (m:=n) (Subtype.val : W→X) B) :=
  restrictLe_pullback contMDiff_subtype_val (fun _ hz=>hz) hB h

private theorem projected_recoded_local_source_bounds {k : ℕ} (M B : MarkedIdeal n X)
    (hM : IsInvDomain k M) (hB : B.ideal.IsCoherent) {d : ℕ} (hd : 1≤d) (hm : d≤M.d)
    (hN : M.N=B.N) (hE : M.E=B.E)
    (hD : B.d=sumExp (fun j=>d-j) d 0*M.d)
    (hLow : RestrictLe M.N (idealPow M.ideal (sumExp (fun j=>d-j) d 0)) B.ideal)
    (hHigh : RestrictLe M.N B.ideal (recodedCoefficient M d).ideal) (W : Opens X) :
    WEquiv (projectionTest (X := CMfd.of (n := n) W) (MarkedIdeal.pullback (Subtype.val : W→X) M))
      (projectionTest (X := CMfd.of (n := n) W) (MarkedIdeal.pullback (Subtype.val : W→X) B)) := by
  let MW : MarkedIdeal n (CMfd.of (n:=n) W):=MarkedIdeal.pullback (Subtype.val : W→X) M
  let BW : MarkedIdeal n (CMfd.of (n:=n) W):=MarkedIdeal.pullback (Subtype.val : W→X) B
  have hMW:=InvDomainTowerAlong.isInvDomain_pullback_val W hM
  have hBW : BW.ideal.IsCoherent:=isCoherent_pullback contMDiff_subtype_val hB
  have hLowW:=pullback_le hB hLow W
  rw [BlowupExceptionalDivisor.pullback_idealPow contMDiff_subtype_val hM.isWellFormed.isCoherent] at hLowW
  have hHighW:=pullback_le
    (recoded_coherent M hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent d) hHigh W
  have hCoef := pullback_val_coeffMarkedAlong W {M with d:=d}
    hM.isWellFormed.isCoherent hM.isWellFormed.isClosedSubmanifold_N hd
  have hCI := congrArg (fun A=>A.ideal) hCoef
  change GermIdeal.pullback (m:=n) (Subtype.val : W→X) (recodedCoefficient M d).ideal=
    (recodedCoefficient (X:=CMfd.of (n:=n) W) MW d).ideal at hCI
  rw [hCI] at hHighW
  apply projected_static_recoded_bounds (X:=CMfd.of (n:=n) W) MW BW hMW hBW hd hm
  · change (Subtype.val : W→X) ⁻¹' M.N=(Subtype.val : W→X) ⁻¹' B.N
    rw [hN]
  · change M.E.map ((Subtype.val : W→X) ⁻¹' ·)=B.E.map ((Subtype.val : W→X) ⁻¹' ·)
    rw [hE]
  · exact hD
  · exact hLowW
  · exact hHighW

private theorem projected_hom_local_source_bounds {k : ℕ} (M B : MarkedIdeal n X)
    (hM : IsInvDomain k M) (hB : B.ideal.IsCoherent)
    (hN : M.N=B.N) (hE : M.E=B.E) (hD : M.d=B.d)
    (hLow : RestrictLe M.N M.ideal B.ideal)
    (hHigh : RestrictLe M.N B.ideal (homMarkedAlong M).ideal) (W : Opens X) :
    WEquiv (projectionTest (X := CMfd.of (n := n) W) (MarkedIdeal.pullback (Subtype.val : W→X) M))
      (projectionTest (X := CMfd.of (n := n) W) (MarkedIdeal.pullback (Subtype.val : W→X) B)) := by
  let MW : MarkedIdeal n (CMfd.of (n:=n) W):=MarkedIdeal.pullback (Subtype.val : W→X) M
  let BW : MarkedIdeal n (CMfd.of (n:=n) W):=MarkedIdeal.pullback (Subtype.val : W→X) B
  have hMW:=InvDomainTowerAlong.isInvDomain_pullback_val W hM
  have hBW : BW.ideal.IsCoherent:=isCoherent_pullback contMDiff_subtype_val hB
  have hLowW:=pullback_le hB hLow W
  have hHighW:=pullback_le (isCoherent_homMarkedAlong hM.isWellFormed.isCoherent
    hM.isWellFormed.isClosedSubmanifold_N) hHigh W
  change RestrictLe ((Subtype.val : W→X) ⁻¹' M.N) (GermIdeal.pullback (m:=n) (Subtype.val : W→X) B.ideal)
    (GermIdeal.pullback (m:=n) (Subtype.val : W→X) (homogenizedIdealAlong M.N M.ideal M.d)) at hHighW
  rw [pullback_val_homogenizedIdealAlong W hM.isWellFormed.isCoherent
    hM.isWellFormed.isClosedSubmanifold_N hM.one_le_d] at hHighW
  have hN' : MW.N=BW.N:=by change _ ⁻¹' M.N=_ ⁻¹' B.N;rw [hN]
  have hE' : MW.E=BW.E:=by change M.E.map _=B.E.map _;rw [hE]
  exact projected_static_hom_bounds (X:=CMfd.of (n:=n) W) MW BW hMW hBW hN' hE' hD hLowW hHighW

private theorem original_head_recoded_projection_local {k : ℕ} (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) {d : ℕ} (hd : 1≤d) (hm : d≤M.d)
    (H : BlowupTower X Y) (hH : IsGeoTestTower M H) (W : Opens Y) :
    WEquiv (projectionTest (X := CMfd.of (n := n) W) (MarkedIdeal.pullback (Subtype.val : W→Y) (geoTransformAlong M H)))
      (projectionTest (X := CMfd.of (n := n) W) (MarkedIdeal.pullback (Subtype.val : W→Y) (geoTransformAlong (recodedCoefficient M d) H))) := by
  obtain ⟨hBH,hN,hE,hD,hLow,hHigh,_hLen⟩:=recoded_coefficient_history_sandwich M hM d hd hm H hH
  have hBC : (geoTransformAlong (recodedCoefficient M d) H).ideal.IsCoherent:=
    (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong (𝔪:=recodedCoefficient M d) hM.isWellFormed.isClosedSubmanifold_N
      (recoded_coherent M hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent d) H hBH).2
  have hMC:=isInvDomain_geoTransformAlong hM H hH
  apply projected_recoded_local_source_bounds (geoTransformAlong M H) _ hMC hBC hd
    (by simpa only [d_geoTransformAlong] using hm) hN.symm hE.symm
    (by simpa only [d_geoTransformAlong] using hD) hLow hHigh W

private theorem hom_domain {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M) :
    IsInvDomain k (homMarkedAlong M) where
  isWellFormed:=⟨hM.isWellFormed.isClosedSubmanifold_N,
    isCoherent_homMarkedAlong hM.isWellFormed.isCoherent hM.isWellFormed.isClosedSubmanifold_N,
    hM.isWellFormed.isSNCDivisor,hM.isWellFormed.isTransverse⟩
  dimLE:=hM.dimLE
  one_le_d:=hM.one_le_d
  isNonzeroAlongAt:=by
    intro x hx
    obtain ⟨f,hf,hfreq⟩:=hM.isNonzeroAlongAt x hx
    exact ⟨f,le_homogenizedIdealAlong (hol hM.isWellFormed.isCoherent) hM.one_le_d x f hf,hfreq⟩

private theorem original_head_hom_projection_local {k : ℕ} (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) (H : BlowupTower X Y) (hH : IsGeoTestTower M H) (W : Opens Y) :
    WEquiv (projectionTest (X := CMfd.of (n := n) W) (MarkedIdeal.pullback (Subtype.val : W→Y) (geoTransformAlong M H)))
      (projectionTest (X := CMfd.of (n := n) W) (MarkedIdeal.pullback (Subtype.val : W→Y) (geoTransformAlong (homMarkedAlong M) H))) := by
  obtain ⟨hHT,hN,hE,hD,_hLen1,_hLen2,hLow,hHigh⟩:=original_homogenization_history_sandwich M hM H hH
  have hHC:=isInvDomain_geoTransformAlong (hom_domain M hM) H hHT
  have hMC:=isInvDomain_geoTransformAlong hM H hH
  apply projected_hom_local_source_bounds (geoTransformAlong M H) _ hMC hHC.isWellFormed.isCoherent
    hN.symm hE.symm (by simpa only [d_geoTransformAlong] using hD.symm)
    (restrictLe_of_le hHC.isWellFormed.isCoherent hLow) ?_ W
  change RestrictLe (geoTransformAlong M H).N _
    (homogenizedIdealAlong (geoTransformAlong M H).N (geoTransformAlong M H).ideal (geoTransformAlong M H).d)
  rw [d_geoTransformAlong]
  exact hHigh

private theorem recoded_own_eq (M : MarkedIdeal n X) (hm : 1≤M.d) :
    recodedCoefficient M M.d=coeffMarkedAlong M := by
  have hD : sumExp (fun j=>M.d-j) M.d 0*M.d=(coeffMarkedAlong M).d:=by
    change _=(Finset.range M.d).prod (fun j=>M.d-j)
    rw [Nat.mul_comm]
    simpa only [Nat.sub_zero] using mul_sumExp (fun j=>M.d-j) (show 0<M.d from hm) (i:=0)
  exact MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl rfl hD

private theorem original_head_bar_projection_local {k : ℕ} (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) (H : BlowupTower X Y) (hH : IsGeoTestTower M H) (W : Opens Y) :
    WEquiv (projectionTest (X := CMfd.of (n := n) W) (MarkedIdeal.pullback (Subtype.val : W→Y) (geoTransformAlong M H)))
      (projectionTest (X := CMfd.of (n := n) W) (MarkedIdeal.pullback (Subtype.val : W→Y) (geoTransformAlong (barMarked M) H))) := by
  have hHT:=(original_homogenization_history_sandwich M hM H hH).1
  have hHDomain:=hom_domain M hM
  have hC:=original_head_recoded_projection_local (homMarkedAlong M) hHDomain hHDomain.one_le_d le_rfl H hHT W
  rw [recoded_own_eq _ hHDomain.one_le_d] at hC
  exact (original_head_hom_projection_local M hM H hH W).trans hC

/-- The projected original head and its literal transformed bar record have
the same controlled tests on any open, including with retained boundary. -/
theorem original_head_bar_projection_local_public {k : ℕ} (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) (H : BlowupTower X Y) (hH : IsGeoTestTower M H) (W : Opens Y) :
    WEquiv (projectionTest (X := CMfd.of (n := n) W) (MarkedIdeal.pullback (Subtype.val : W→Y) (geoTransformAlong M H)))
      (projectionTest (X := CMfd.of (n := n) W) (MarkedIdeal.pullback (Subtype.val : W→Y) (geoTransformAlong (barMarked M) H))) :=
  original_head_bar_projection_local M hM H hH W

private theorem lower_common (A B : MarkedIdeal n X) (hA : A.IsWellFormed) (hB : B.IsWellFormed)
    (hdA : 1≤A.d) (hdB : 1≤B.d) (S : Set X) (hS : IsClosedSubmanifold n S)
    (hSA : S⊆A.N) (hSB : S⊆B.N) (hWeak : WEquiv A B) :
    WEquiv (withN (coeffMarkedAlong A) S) (withN (coeffMarkedAlong B) S) := by
  refine ⟨hWeak.1,fun R=>⟨?_,?_⟩⟩
  · have hRA:=(coeffAlong_restrict_tower_iff A hA.isClosedSubmanifold_N hA.isCoherent hdA hS hSA R).1
    have hRB:=(coeffAlong_restrict_tower_iff B hB.isClosedSubmanifold_N hB.isCoherent hdB hS hSB R).1
    exact hRA.trans ((and_congr_left fun _=>(hWeak.2 R).1).trans hRB.symm)
  · intro hR
    have hRA:=(coeffAlong_restrict_tower_iff A hA.isClosedSubmanifold_N hA.isCoherent hdA hS hSA R).1.mp hR
    have hRB:=(coeffAlong_restrict_tower_iff B hB.isClosedSubmanifold_N hB.isCoherent hdB hS hSB R).1.mpr
      ⟨(hWeak.2 R).1.mp hRA.1,hRA.2⟩
    rw [(coeffAlong_restrict_tower_iff A hA.isClosedSubmanifold_N hA.isCoherent hdA hS hSA R).2 hR,
      (coeffAlong_restrict_tower_iff B hB.isClosedSubmanifold_N hB.isCoherent hdB hS hSB R).2 hRB,
      (hWeak.2 R).2 hRA.1]

private theorem contact_lower_projection_local {k : ℕ} (J K : MarkedIdeal n X)
    (hJ : IsInvDomain k J) (hK : IsInvDomain k K) (hN : J.N=K.N)
    (H : BlowupTower X Y) (hHJ : IsGeoTestTower J H) (hHK : IsGeoTestTower K H)
    (O : Opens Y) (w : X→ℂ)
    (hS : IsClosedSubmanifold n (contactMarkedKept J w H O).N)
    (hUpper : WEquiv
      (projectionTest (X := CMfd.of (n := n) O) (MarkedIdeal.pullback (Subtype.val : O→Y) (geoTransformAlong (barMarked J) H)))
      (projectionTest (X := CMfd.of (n := n) O) (MarkedIdeal.pullback (Subtype.val : O→Y) (geoTransformAlong (barMarked K) H)))) :
    WEquiv (projectionTest (X := CMfd.of (n := n) O) (contactMarkedKept J w H O))
      (projectionTest (X := CMfd.of (n := n) O) (contactMarkedKept K w H O)) := by
  have hBarJ:=(original_bar_weighted_history J hJ H hHJ).2.1
  have hBarK:=(original_bar_weighted_history K hK H hHK).2.1
  let A:=MarkedIdeal.pullback (Subtype.val : O→Y) (geoTransformAlong (barMarked J) H)
  let B:=MarkedIdeal.pullback (Subtype.val : O→Y) (geoTransformAlong (barMarked K) H)
  let S:=(Subtype.val : O→Y) ⁻¹' strictAlong H (J.N∩{x | w x=0})
  have hA:=InvDomainTowerAlong.isInvDomain_pullback_val O hBarJ
  have hB:=InvDomainTowerAlong.isInvDomain_pullback_val O hBarK
  have hSA : S⊆A.N:=by
    intro x hx
    exact MaximalContactAlongTower.strictAlong_subset_N (barMarked J) (fun _ hz=>hz.1) H hx
  have hSB : S⊆B.N:=by
    intro x hx
    have hxK : x.val∈strictAlong H (K.N∩{x | w x=0}):=by rw [←hN];exact hx
    exact MaximalContactAlongTower.strictAlong_subset_N (barMarked K) (fun _ hz=>hz.1) H hxK
  have hLJ : contactMarkedKept J w H O=withN (coeffMarkedAlong A) S:=
    ContactCanonicalAlong.pullback_val_restrictedCoeff O _ hBarJ.isWellFormed.isCoherent
      hBarJ.isWellFormed.isClosedSubmanifold_N hBarJ.one_le_d _
  have hLK : contactMarkedKept K w H O=withN (coeffMarkedAlong B) S:=by
    change MarkedIdeal.pullback (Subtype.val : O→Y)
      (withN (coeffMarkedAlong (geoTransformAlong (barMarked K) H)) (strictAlong H (K.N∩{x | w x=0})))=_
    rw [ContactCanonicalAlong.pullback_val_restrictedCoeff O _ hBarK.isWellFormed.isCoherent
      hBarK.isWellFormed.isClosedSubmanifold_N hBarK.one_le_d]
    change withN (coeffMarkedAlong B) ((Subtype.val : O→Y) ⁻¹' strictAlong H (K.N∩{x | w x=0}))=
      withN (coeffMarkedAlong B) ((Subtype.val : O→Y) ⁻¹' strictAlong H (J.N∩{x | w x=0}))
    rw [hN]
  rw [hLJ,hLK]
  rw [projection_withN,projection_withN,
    projection_coefficient (X := CMfd.of (n := n) O) A hA.isWellFormed.isCoherent hA.isWellFormed.isClosedSubmanifold_N,
    projection_coefficient (X := CMfd.of (n := n) O) B hB.isWellFormed.isCoherent hB.isWellFormed.isClosedSubmanifold_N]
  have hAP := projection_test_isInvDomain (X := CMfd.of (n := n) O) A hA
  have hBP := projection_test_isInvDomain (X := CMfd.of (n := n) O) B hB
  have hf := isSubmersion_fst (n := n) (m := 1) (X := CMfd.of (n := n) O) (Y := ComplexModel 1)
  have hSP := HironakaSmoothSubmersionRelativeGeometry.isClosedSubmanifold_preimage_submersion hf hS
  exact lower_common (X := projectionAmbient (CMfd.of (n := n) O)) (projectionTest A) (projectionTest B)
    hAP.isWellFormed hBP.isWellFormed hAP.one_le_d hBP.one_le_d _ hSP
    (fun _ hz => hSA hz) (fun _ hz => hSB hz) hUpper

/-- Exact ordinary ORIGINAL inputs internally derive the TRUE projected
comparison before ANY LOCAL R, preserving every original head and clock. -/
theorem original_lower_head_projection_tests {A : CMfd.{0} n}
    (hn : 0<n) (Q : MarkedIdeal n A) {k : ℕ} (hQ : IsInvDomain k Q)
    (hN : Q.N=univ) (hE : Q.E=[]) (hMax : IsMaximalOrderAlong Q.N Q.ideal Q.d)
    (Z : Set A) (hZ : IsComplexAnalyticSubset (n:=n) Z)
    (hSing : Q.cosupp⊆singularSet (n:=n) Z) (a : A) (ha : a∈Q.cosupp) :
    ∃hm : a∈maskB Q (.refl : BlowupTower A A) a,
      let V:=maskB Q (.refl : BlowupTower A A) a
      let L : MarkedIdeal n (CMfd.of (n:=n) V):=lowerMarkedB Q (.refl : BlowupTower A A) a
      let x : V:=⟨a,hm⟩
      let μ:=NonmonomialOrderLocal.nmOrd L x
      let e:=sumExp (fun j=>L.d-j) L.d 0
      let U:=NonmonomialOrderTail.ordMask L μ
      let P : MarkedIdeal n (CMfd.of (n:=n) U):=MarkedIdeal.pullback (Subtype.val : U→V) L
      let B : MarkedIdeal n (CMfd.of (n:=n) U):=MarkedIdeal.pullback (Subtype.val : U→V) (coeffMarkedAlong L)
      let J:=CompanionRebase.companionOf n P μ
      let K:=CompanionRebase.companionOf n B (e*μ)
      ∃_hxU : x∈U,
        IsInvDomain (k-1) J ∧ IsInvDomain (k-1) K ∧ J.E=[] ∧ K.E=[] ∧ J.d=μ ∧ K.d=e*μ ∧
        ∀{Y : CMfd.{0} n}(H : BlowupTower (CMfd.of (n:=n) U) Y),IsGeoTestTower J H→
          IsGeoTestTower K H ∧
          ∀y∈(geoTransformAlong (barMarked K) H).cosupp,
            y∉CodimOneSupportAlong.codimOnePartAlong (geoTransformAlong (barMarked K) H).N
              (geoTransformAlong (barMarked K) H).ideal (geoTransformAlong (barMarked K) H).d→
            y∈maskB K H y ∧
            let O:=maskB K H y
            let LJ:=contactMarkedKept J (tangentChoice K (H.proj y)).2 H O
            let LK:=contactMarkedKept K (tangentChoice K (H.proj y)).2 H O
            IsInvDomain ((k-1)-1) LJ ∧ IsInvDomain ((k-1)-1) LK ∧
            LK=lowerMarkedB K H y ∧ LJ.N=LK.N ∧ LJ.E=LK.E ∧
            LJ.d=(Finset.range ((Finset.range μ).prod (fun j=>μ-j))).prod
              (fun j=>(Finset.range μ).prod (fun j=>μ-j)-j) ∧
            LK.d=(Finset.range ((Finset.range (e*μ)).prod (fun j=>e*μ-j))).prod
              (fun j=>(Finset.range (e*μ)).prod (fun j=>e*μ-j)-j) ∧
            LJ.E.length=H.length ∧ LK.E.length=H.length ∧
            MarkedIdealEquivalence.MarkedIdeal.WEquiv
              (HironakaActualProjectionTestRecord.projectionTest (X := CMfd.of (n := n) O) LJ)
              (HironakaActualProjectionTestRecord.projectionTest (X := CMfd.of (n := n) O) LK) ∧
            ∀{Y' : CMfd.{0} n}(R : BlowupTower (CMfd.of (n:=n) O) Y'),
              (IsGeoTestTower LJ R↔IsGeoTestTower LK R) ∧
              (IsGeoTestTower LJ R→
                (geoTransformAlong LJ R).cosupp=(geoTransformAlong LK R).cosupp ∧
                (geoTransformAlong LJ R).N=(geoTransformAlong LK R).N ∧
                (geoTransformAlong LJ R).E=(geoTransformAlong LK R).E ∧
                (geoTransformAlong LJ R).d=LJ.d ∧ (geoTransformAlong LK R).d=LK.d ∧
                (geoTransformAlong LJ R).E.length=H.length+R.length ∧
                (geoTransformAlong LK R).E.length=H.length+R.length) := by
  obtain ⟨hm,hxU,hJ,hK,hJE,hKE,hJd,hKd,hCommon⟩:=
    HironakaActualOriginalLowerLocalTests.original_lower_local_tests hn Q hQ hN hE hMax Z hZ hSing a ha
  obtain ⟨_hmS,_hxS,_hNaturalS,_hJS,_hKS,_hJdS,_hKdS,hSandwich⟩:=
    original_lower_companion_history_sandwich hn Q hQ hN hE hMax Z hZ hSing a ha
  obtain ⟨_hmL,hL,_hEmpty,_hMark,_hx,hμ,_hOrd,_hCoeff,_hHistory⟩:=
    original_lower_coefficient_history_along hn Q hQ hN hE hMax Z hZ hSing a ha
  let V:=maskB Q (.refl : BlowupTower A A) a
  let L : MarkedIdeal n (CMfd.of (n:=n) V):=lowerMarkedB Q (.refl : BlowupTower A A) a
  let x : V:=⟨a,hm⟩
  let μ:=NonmonomialOrderLocal.nmOrd L x
  let e:=sumExp (fun j=>L.d-j) L.d 0
  let U:=NonmonomialOrderTail.ordMask L μ
  let P : MarkedIdeal n (CMfd.of (n:=n) U):=MarkedIdeal.pullback (Subtype.val : U→V) L
  let B : MarkedIdeal n (CMfd.of (n:=n) U):=MarkedIdeal.pullback (Subtype.val : U→V) (coeffMarkedAlong L)
  let J:=CompanionRebase.companionOf n P μ
  let K:=CompanionRebase.companionOf n B (e*μ)
  change IsInvDomain (k-1) J at hJ
  change IsInvDomain (k-1) K at hK
  change IsInvDomain (k-1) L at hL
  change L.d≤μ at hμ
  change J.d=μ at hJd
  change K.d=e*μ at hKd
  refine ⟨hm,hxU,hJ,hK,hJE,hKE,hJd,hKd,?_⟩
  intro Y H hHJ
  obtain ⟨hHK,hStage⟩:=hCommon H hHJ
  obtain ⟨_hHK,hJN,hJEq,_hJLen,_hKLen,hLow,hHigh⟩:=hSandwich H hHJ
  refine ⟨hHK,?_⟩
  intro y hy hOut
  obtain ⟨hyO,hLJ,hLK,hOwnK,hLN,hLE,hLJd,hLKd,hLJLen,hLKLen,hLocal⟩:=hStage y hy hOut
  let O:=maskB K H y
  let w:=(tangentChoice K (H.proj y)).2
  let LJ:=contactMarkedKept J w H O
  let LK:=contactMarkedKept K w H O
  have hJC:=isInvDomain_geoTransformAlong hJ H hHJ
  have hKC:=isInvDomain_geoTransformAlong hK H hHK
  have hPair : WEquiv
      (projectionTest (X := CMfd.of (n := n) O) (MarkedIdeal.pullback (Subtype.val : O→Y) (geoTransformAlong J H)))
      (projectionTest (X := CMfd.of (n := n) O) (MarkedIdeal.pullback (Subtype.val : O→Y) (geoTransformAlong K H))):=by
    apply projected_recoded_local_source_bounds _ _ hJC hKC.isWellFormed.isCoherent hL.one_le_d
      (by simpa only [d_geoTransformAlong,hJd] using hμ) hJN hJEq
      (by
        change (geoTransformAlong K H).d=e*(geoTransformAlong J H).d
        rw [d_geoTransformAlong,d_geoTransformAlong,hJd,hKd]) hLow hHigh O
  have hUpper:=(original_head_bar_projection_local J hJ H hHJ O).symm.trans
    (hPair.trans (original_head_bar_projection_local K hK H hHK O))
  have hJK : J.N=K.N:=by
    simp only [J,K,CompanionRebase.companionOf,CompanionReductionAlong.companionAlong_N]
    rfl
  have hWeak:=contact_lower_projection_local J K hJ hK hJK H hHJ hHK O w hLJ.isWellFormed.isClosedSubmanifold_N hUpper
  exact ⟨hyO,hLJ,hLK,hOwnK,hLN,hLE,hLJd,hLKd,hLJLen,hLKLen,hWeak,hLocal⟩

end
end Hironaka.HironakaActualOriginalLowerHeadProjectionTests
