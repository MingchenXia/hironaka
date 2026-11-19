import Hironaka.Resolution.HironakaDisjointCanonicalHistoricalAnchor

/-! Fixed original contact histories for marking-one full-carrier records on
arbitrary actual manifolds. This supplies the relative open-product normal
anchor without extending local ideals to the whole coordinate space. The
geometric initial hypotheses are discharged by a separate product constructor.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe v
namespace Hironaka.HironakaActualMarkOneFixedContactHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  MarkedIdealOperationsAlong.MarkedIdeal BlowupTowers BlowupTowerTransforms
  HironakaDisjointCoherentNormalRecoding HironakaDisjointFirstStepHistoricalAnchor
  GermIdealOrder RelativePrincipalizationSpan GermIdealPullbackCalculus
  InvertibleIdealQuotient IdealWeightPowers DivisorExponentAlong
  HomogenizedIdealAlong StepOneValue StepOneRegime StepOneLowerDomain
  RestrictedIdealExtension InvDomainRebase CanonicalCentres ContactStageKept
  GeneralValue NonmonomialOrderTail MonomialPartAlong CompanionReductionAlong
  CoefficientIdeal HomogenizedGlueing DerivativeIdeal TangentDirectionAlong
  GermIdealTotalTransform CodimOneSupportAlong NormalCrossings NonmonomialOrderLocal BlowupTowerSplit
  HironakaSharpOriginalProductTraceOrder
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

abbrev fixedContact {n : ℕ} {X : CMfd.{v} (n+1)} (J : MarkedIdeal (n+1) X) (u : X→ℂ) :
    MarkedIdeal (n+1) (CMfd.of (n:=n+1) (⊤ : Opens X)):=contactMarkedKept J u .refl ⊤

private theorem coefficient_one {a : ℕ} {X : CMfd.{v} a}
    (I : GermIdeal a X) (hI : I.IsCoherent) :
    coeffMarked (⟨univ,[],I,1⟩ : MarkedIdeal a X)=(⟨univ,[],I,1⟩ : MarkedIdeal a X):=by
  have hp : idealPow I 1=I:=by
    rw [idealPow_succ,idealPow_zero,BlowupControlledTransform.unitIdeal_mul hI]
  have he : sumExp (fun i : ℕ=>1-i) 1 0=1:=by simp [sumExp]
  have h0 : (idealPow (iterDerivIdeal I 0) (sumExp (fun i : ℕ=>1-i) 1 0)).IsCoherent:=by
    simpa only [iterDerivIdeal_zero,he,hp] using hI
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · rfl
  · rfl
  · change finSumIdeal (fun i=>idealPow (iterDerivIdeal I i) (sumExp (fun j : ℕ=>1-j) 1 i)) 1=I
    rw [finSumIdeal_one h0,iterDerivIdeal_zero,he,hp]
  · simp [coeffMarked,msum]

private theorem coefficient_record {a : ℕ} {X : CMfd.{v} a} (J : MarkedIdeal a X)
    (hc : J.ideal.IsCoherent) (hN : J.N=univ) (hE : J.E=[]) (hd : J.d=1) : coeffMarkedAlong J=J:=by
  have hRecord : J=(⟨univ,[],J.ideal,1⟩ : MarkedIdeal a X):=
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of hN hE rfl hd
  rw [coeffMarkedAlong_eq_coeffMarked hN (fun _ _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem hc hg)]
  exact (congrArg coeffMarked hRecord).trans ((coefficient_one J.ideal hc).trans hRecord.symm)

private theorem bar_record {a : ℕ} {X : CMfd.{v} a} (J : MarkedIdeal a X)
    (hc : J.ideal.IsCoherent) (hN : J.N=univ) (hE : J.E=[]) (hd : J.d=1) : barMarked J=J:=by
  have hHom : homMarkedAlong J=J:=by
    apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    · rfl
    · rfl
    · change homogenizedIdealAlong J.N J.ideal J.d=J.ideal
      rw [hN,hd,homogenizedIdealAlong_univ
        (fun _ _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem hc hg),HomogenizedIdeal.homogenizedIdeal_one hc]
    · rfl
  change coeffMarkedAlong (homMarkedAlong J)=J
  rw [hHom,coefficient_record J hc hN hE hd]

/-- Whole marking-one contact record on the actual whole-open model. -/
theorem fixed_contact_record {n : ℕ} {X : CMfd.{v} (n+1)} (J : MarkedIdeal (n+1) X)
    (hc : J.ideal.IsCoherent) (hN : J.N=univ) (hE : J.E=[]) (hd : J.d=1) (u : X→ℂ) :
    fixedContact J u=MarkedIdeal.pullback (Subtype.val : (⊤ : Opens X)→X)
      (⟨{x | u x=0},[],J.ideal,1⟩ : MarkedIdeal (n+1) X):=by
  have hCoeff : coeffMarkedAlong (barMarked J)=J:=by
    rw [bar_record J hc hN hE hd,coefficient_record J hc hN hE hd]
  change MarkedIdeal.pullback (Subtype.val : (⊤ : Opens X)→X)
    (CoefficientIdealRestriction.withN (coeffMarkedAlong (barMarked J)) (J.N∩{x | u x=0}))=_
  rw [hCoeff,hN,univ_inter]
  apply congrArg (MarkedIdeal.pullback (Subtype.val : (⊤ : Opens X)→X))
  exact MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl hE rfl hd

/-- The ORIGINAL source domain and genuine tangent produce the original
predecessor contact domain, with no lower-domain premise. -/
theorem fixed_contact_original_domain {n q : ℕ} {X : CMfd.{v} (n+1)}
    (J : MarkedIdeal (n+1) X) (hJ : IsInvDomain (q+1) J)
    (hN : J.N=univ) (hE : J.E=[]) (hd : J.d=1)
    (hZ : codimOnePartAlong J.N J.ideal J.d=∅) (u : X→ℂ)
    (hu : IsTangentDirectionAlong J.N J.ideal J.d univ u) : IsInvDomain q (fixedContact J u):=by
  have hb:=bar_record J hJ.isWellFormed.isCoherent hN hE hd
  have h:=ContactStageInvDomain.isInvDomain_stage_coeffHomAlong_of_le J hJ.isWellFormed hJ.one_le_d hJ.dimLE
    ⊤ hu .refl trivial ⊤ (subset_univ _)
    (by
      intro y _ _
      change y∉codimOnePartAlong (barMarked J).N (barMarked J).ideal (barMarked J).d
      rw [hb,hZ]
      exact notMem_empty _)
    (by
      intro H hH
      change H∈(barMarked J).E.take J.E.length at hH
      rw [hE,List.length_nil,List.take_zero] at hH
      exact False.elim (List.not_mem_nil hH))
  exact h

/- The package contains only original geometric hypotheses, never a later
canonicality, value comparison or history. The public endpoints below expose
these hypotheses separately. -/
private structure OriginalGeometry {n : ℕ} {X : CMfd.{v} (n+1)}
    (J : MarkedIdeal (n+1) X) (u : X→ℂ) (q : ℕ) : Prop where
  domain : IsInvDomain (q+1) J
  carrier : J.N=univ
  boundary : J.E=[]
  marking : J.d=1
  maximal : IsMaximalOrderAlong J.N J.ideal J.d
  codimension : codimOnePartAlong J.N J.ideal J.d=∅
  tangent : IsTangentDirectionAlong J.N J.ideal J.d univ u

section Geometry
variable {n q : ℕ} {X : CMfd.{v} (n+1)} {J : MarkedIdeal (n+1) X}
  {u : X→ℂ} (g : OriginalGeometry J u q)
include g

private theorem initial_record : J=(⟨univ,[],J.ideal,1⟩ : MarkedIdeal (n+1) X):=
  MarkedIdealOperationsTransform.MarkedIdeal.ext_of g.carrier g.boundary rfl g.marking

private theorem initial_orderMask : ordMask J 1=⊤:=by
  have hge : ordGe J 2=∅:=by
    have hrecord:=initial_record g
    have he : ordGe J 2=ordGe (HironakaSharpOriginalProductTraceOrder.ordinaryTraceMarked univ J.ideal) 2:=by
      exact congrArg (fun K : MarkedIdeal (n+1) X=>ordGe K 2) hrecord
    rw [he,HironakaSharpOriginalProductTraceOrder.ordGe_ordinaryTraceMarked_eq_cosupport
      univ J.ideal g.domain.isWellFormed.isCoherent 2]
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hm:=g.maximal x
    rw [g.carrier,g.marking] at hm
    exact hm hx
  apply Opens.ext
  change (closure (ordGe J 2))ᶜ=univ
  rw [hge,closure_empty,compl_empty]

private theorem initial_order_le (x : X) : nmOrd J x≤1:=
  nmOrd_le_of_notMem (notMem_ordGe_of_mem_ordMask (show x∈ordMask J 1 by rw [initial_orderMask g]; trivial))

private theorem original_level (Y : CMfd.{v} (n+1)) (T : BlowupTower X Y) (y : Y) : level J T y=0:=by
  change BoundaryCount.boundaryCount ((geoTransformAlong (barMarked J) T).E.take J.E.length) y=0
  rw [g.boundary,List.length_nil,List.take_zero]
  rfl

private theorem bar_test {Y : CMfd.{v} (n+1)} (T : BlowupTower X Y) (hT : IsGeoTestTower J T) :
    IsGeoTestTower (barMarked J) T:=by
  exact ((HomogenizedIdealAlongTower.coeff_homAlong_wEquiv J
    g.domain.isWellFormed.isClosedSubmanifold_N g.domain.isWellFormed.isCoherent g.domain.one_le_d).2 T).1.mpr hT

private theorem current_codimOne_empty {Y : CMfd.{v} (n+1)}
    (T : BlowupTower X Y) (hT : IsGeoTestTower J T) :
    codimOnePartAlong (geoTransformAlong J T).N
      (geoTransformAlong J T).ideal (geoTransformAlong J T).d=∅:=
  CodimOnePartTowerAlong.codimOnePartAlong_geoTransformAlong_eq_empty J g.domain.isWellFormed
    g.domain.one_le_d g.maximal g.codimension T hT

private theorem current_not_special {Y : CMfd.{v} (n+1)}
    (T : BlowupTower X Y) (hT : IsGeoTestTower J T) (y : Y) : ¬IsSpecial J T y:=by
  have hw:=HomogenizedIdealAlongTower.coeff_homAlong_wEquiv J
    g.domain.isWellFormed.isClosedSubmanifold_N g.domain.isWellFormed.isCoherent g.domain.one_le_d
  have he:=CodimOnePartCanonical.codimOnePartAlong_geoTransformAlong_of_wEquiv
    (𝔪:=barMarked J) hw rfl T (bar_test g T hT)
  rw [current_codimOne_empty g T hT] at he
  rintro (⟨_,hz⟩ | ⟨hpos,_⟩)
  · rw [he] at hz
    exact hz
  · rw [original_level g] at hpos
    omega

private theorem current_order_positive {Y : CMfd.{v} (n+1)}
    (T : BlowupTower X Y) (hT : IsGeoTestTower J T)
    {y : Y} (hy : y∈(geoTransformAlong J T).cosupp) : 1≤nmOrd (geoTransformAlong J T) y:=by
  have hA:=InvDomainTowerAlong.isInvDomain_geoTransformAlong g.domain T hT
  have hN : (geoTransformAlong J T).N=univ:=
    (pullback_eq_mul_geoTransformAlong (𝔪:=J) g.carrier g.domain.isWellFormed.isCoherent T hT).1
  have hmax:=isMaximalOrderAlong_geoTransformAlong g.domain.isWellFormed.isClosedSubmanifold_N
    g.domain.isWellFormed.isCoherent g.maximal T hT
  have hOne:=one_mem_monomial_of_empty_codimOne (geoTransformAlong J T)
    hA.isWellFormed hN ((d_geoTransformAlong J T).trans g.marking) hmax (current_codimOne_empty g T hT) y
  apply (mem_ordGe_iff hA.isWellFormed hA.isNonzeroAlongAt hy.1 1).mp
  refine ⟨hy.1,?_⟩
  intro f hf
  have hprod:=hf.2 (fun _=>1) hOne
  have hs : IsInSpanOnAt (n:=n+1) univ ((geoTransformAlong J T).ideal.mem y) y f:=by
    simpa only [hN,one_mul,mul_one] using hprod.2
  obtain ⟨N,s,a,hs,ha,heq⟩:=hs
  have hmem:=mem_of_isInSpanAt_mem hA.isWellFormed.isCoherent
    ⟨hf.1,N,s,a,hs,ha,heq.mono fun z hz=>hz (mem_univ z)⟩
  simpa only [d_geoTransformAlong,g.marking] using hy.2 f hmem

private theorem contact_domain : IsInvDomain q (fixedContact J u):=
  fixed_contact_original_domain J g.domain g.carrier g.boundary g.marking g.codimension u g.tangent

private theorem contact_cosupport {Y : CMfd.{v} (n+1)}
    (T : BlowupTower X Y) (hT : IsGeoTestTower J T) :
    (geoTransformAlong (fixedContact J u) (restrict ⊤ T)).cosupp=
      (Subtype.val : openPreimage T (⊤ : Opens X)→Y) ⁻¹' (geoTransformAlong J T).cosupp:=by
  have hw:=HomogenizedIdealAlongTower.coeff_homAlong_wEquiv J
    g.domain.isWellFormed.isClosedSubmanifold_N g.domain.isWellFormed.isCoherent g.domain.one_le_d
  have hbar:=bar_test g T hT
  have h:=ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le J
    g.domain.isWellFormed.isClosedSubmanifold_N g.domain.isWellFormed.isCoherent g.domain.one_le_d
    ⊤ g.tangent .refl T (by simpa only [BlowupTower.refl_append] using hbar) ⊤ (subset_univ _)
  exact h.2.trans (congrArg (fun A : Set Y=>(Subtype.val : openPreimage T (⊤ : Opens X)→Y) ⁻¹' A)
    (by simpa only [BlowupTower.refl_append] using ((hw.2 T).2 hbar)))

private theorem upper_test {Y : CMfd.{v} (n+1)} (T : BlowupTower X Y)
    (hCan : IsCanonical J ((invFamily (Nat.succ_pos n) (q+1)).inv J) T) : IsGeoTestTower J T:=
  (invFamily (Nat.succ_pos n) (q+1)).isInvValue.isGeoTestTower_of_isCanonical g.domain T hCan

private theorem step_run_test : ∀{Y : CMfd.{v} (n+1)}(T : BlowupTower X Y),
    IsGeoTestTower J T → ∀y,regimeRun (stepRegime J 0) T y=T.length
  | _,.refl,_,_=>rfl
  | _,.step T C π hπ,hT,y=>by
    have hreg : stepRegime J 0 T (π y):=⟨original_level g _ T (π y),current_not_special g T hT.1 (π y)⟩
    exact (regimeRun_step_of _ T C π hπ hreg).trans
      (congrArg (fun r=>r+1) (step_run_test T hT.1 (π y)))

private theorem current_order_one {Y : CMfd.{v} (n+1)} (T : BlowupTower X Y)
    (hCan : IsCanonical J ((invFamily (Nat.succ_pos n) (q+1)).inv J) T)
    {y : Y} (hy : y∈(geoTransformAlong J T).cosupp) : nmOrd (geoTransformAlong J T) y=1:=by
  have ht:=upper_test g T hCan
  have hf : NonmonomialOrderCanonical.OrdMonotone J ((invFamily (Nat.succ_pos n) (q+1)).inv J):=
    ordMonotone_genInv _ _
  have h:=NonmonomialOrderCanonical.nmOrd_le_nmOrd_proj (Nat.succ_pos n) g.domain hf .refl T
    (by simpa only [BlowupTower.refl_append] using ht)
    (by simpa only [BlowupTower.refl_append] using hCan) y
    (by simpa only [BlowupTower.refl_append] using hy)
  have h' : T.proj y∈J.cosupp ∧ nmOrd (geoTransformAlong J T) y≤nmOrd J (T.proj y):=by
    simpa only [BlowupTower.refl_append,geoTransformAlong_refl] using h
  exact Nat.le_antisymm (h'.2.trans (initial_order_le g _)) (current_order_positive g T ht hy)

private theorem order_run : ∀{Y : CMfd.{v} (n+1)} (T : BlowupTower X Y),
    IsCanonical J ((invFamily (Nat.succ_pos n) (q+1)).inv J) T →
    ∀y∈(geoTransformAlong J T).cosupp,
      regimeRun (NonmonomialOrderRegime.OrdRegime J 1) T y=T.length
  | _,.refl,_,_,_=>rfl
  | _,.step T C π hπ,hCan,y,hy=>by
    have ht:=upper_test g (.step T C π hπ) hCan
    have hf : NonmonomialOrderCanonical.OrdMonotone J ((invFamily (Nat.succ_pos n) (q+1)).inv J):=
      ordMonotone_genInv _ _
    have hp:=(NonmonomialOrderCanonical.nmOrd_step_le_of_canonical (Nat.succ_pos n) g.domain hf
      T C π hπ ht hCan.2 hy).1
    have hreg : NonmonomialOrderRegime.OrdRegime J 1 T (π y):=⟨hp,current_order_one g T hCan.1 hp⟩
    exact (regimeRun_step_of _ T C π hπ hreg).trans
      (congrArg (fun r=>r+1) (order_run T hCan.1 (π y) hp))

end Geometry

private def stepMap (q : ℕ) (v : ValTy q) : ℕ ×ₗ WithTop (ValTy q):=toLex (0,(v : WithTop (ValTy q)))

private theorem stepMap_le (q : ℕ) (v w : ValTy q) : stepMap q v≤stepMap q w ↔ v≤w:=by
  simp [stepMap,Prod.Lex.toLex_le_toLex]

private abbrev contactValue {n : ℕ} (q : ℕ) {X : CMfd.{v} (n+1)}
    (J : MarkedIdeal (n+1) X) (u : X→ℂ) {Y : CMfd.{v} (n+1)} (T : BlowupTower X Y) (y : Y) : ValTy q:=
  (invFamily (Nat.succ_pos n) q).inv (fixedContact J u) (restrict ⊤ T) ⟨y,mem_univ _⟩

private theorem upper_step_maximum_of_values {n : ℕ} (q : ℕ) {X : CMfd.{v} (n+1)}
    (J : MarkedIdeal (n+1) X) (u : X→ℂ) {Y : CMfd.{v} (n+1)} (T : BlowupTower X Y)
    (hStep : ∀y∈(geoTransformAlong J T).cosupp,
      Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q) J T y=stepMap q (contactValue q J u T y))
    (hFull : ∀y∈(geoTransformAlong J T).cosupp,
      (invFamily (Nat.succ_pos n) (q+1)).inv J T y=initialEmbedding q (contactValue q J u T y)) :
    ResolutionDriver.maxLocus ((invFamily (Nat.succ_pos n) (q+1)).inv J T) (geoTransformAlong J T).cosupp=
      ResolutionDriver.maxLocus (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q) J T)
        (geoTransformAlong J T).cosupp:=by
  ext y
  constructor
  · rintro ⟨hy,hmax⟩
    refine ⟨hy,?_⟩
    intro z hz
    have h:=hmax z hz
    rw [hFull z hz,hFull y hy] at h
    rw [hStep z hz,hStep y hy]
    exact (stepMap_le q _ _).mpr ((initialEmbedding q).le_iff_le.mp h)
  · rintro ⟨hy,hmax⟩
    refine ⟨hy,?_⟩
    intro z hz
    have h:=hmax z hz
    rw [hStep z hz,hStep y hy] at h
    rw [hFull z hz,hFull y hy]
    exact (initialEmbedding q).monotone ((stepMap_le q _ _).mp h)

section Histories
variable {n q : ℕ} {X : CMfd.{v} (n+1)} {J : MarkedIdeal (n+1) X}
  {u : X→ℂ} (g : OriginalGeometry J u q)
include g

private theorem original_companion_equiv :
    RestrictEquiv (compAt J 1 .refl) (MarkedIdeal.pullback (Subtype.val : ordMask J 1→X) J):=by
  let O:=ordMask J 1
  change RestrictEquiv
    (companionAlong (X:=CMfd.of (n:=n+1) O) ((Subtype.val : O→X) ⁻¹' J.N) (J.E.map ((Subtype.val : O→X) ⁻¹' ·))
      (nonmonomialPartAlong (n+1) ((Subtype.val : O→X) ⁻¹' J.N)
        (GermIdeal.pullback (m:=n+1) (Subtype.val : O→X) J.ideal) (J.E.map ((Subtype.val : O→X) ⁻¹' ·)))
      (monomialPartAlong (n+1) ((Subtype.val : O→X) ⁻¹' J.N)
        (GermIdeal.pullback (m:=n+1) (Subtype.val : O→X) J.ideal) (J.E.map ((Subtype.val : O→X) ⁻¹' ·))) 1 J.d)
    (⟨(Subtype.val : O→X) ⁻¹' J.N,J.E.map ((Subtype.val : O→X) ⁻¹' ·),
      GermIdeal.pullback (m:=n+1) (Subtype.val : O→X) J.ideal,J.d⟩ : MarkedIdeal (n+1) O)
  rw [g.boundary,g.marking,List.map_nil,companionAlong,if_neg (Nat.lt_irrefl 1),
    nonmonomialPartAlong_nil_eq_restrictOn]
  exact ⟨rfl,rfl,rfl,restrictLe_restrictOn,
    restrictLe_self_restrictOn (isCoherent_pullback contMDiff_subtype_val g.domain.isWellFormed.isCoherent)⟩

private theorem step_value_of_canons {Y : CMfd.{v} (n+1)} (T : BlowupTower X Y)
    (hCan : IsCanonical J ((invFamily (Nat.succ_pos n) (q+1)).inv J) T)
    (hStepCan : IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q) J) T)
    (hKCan : IsCanonical (fixedContact J u) ((invFamily (Nat.succ_pos n) q).inv (fixedContact J u)) (restrict ⊤ T))
    {y : Y} (hy : y∈(geoTransformAlong J T).cosupp) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q) J T y=stepMap q (contactValue q J u T y):=by
  let R:=invFamily (Nat.succ_pos n) q
  have ht:=upper_test g T hCan
  have hbar:=bar_test g T ht
  have hbarcan:=(Seq.StepOneBridge.isCanonical_iff (k:=q+1) R J g.domain g.maximal (Nat.succ_pos n) T).mp hStepCan
  have hnsp : ¬IsSpecial J T y:=current_not_special g T ht y
  have hw:=HomogenizedIdealAlongTower.coeff_homAlong_wEquiv J
    g.domain.isWellFormed.isClosedSubmanifold_N g.domain.isWellFormed.isCoherent g.domain.one_le_d
  have hp : y∈(geoTransformAlong (barMarked J) T).cosupp:=((hw.2 T).2 hbar).symm ▸ hy
  have hD:=Seq.StepOneCanonicalTail.hasLowerDataL_of_isCanonical J (k:=q+1) R
    g.domain.isWellFormed g.domain.one_le_d (Nat.succ_pos n) g.maximal g.domain.dimLE T hbar hbarcan y hp hnsp
  have hRun:=step_run_test g T ht y
  have hLevel:=original_level g _ T y
  change Seq.StepOneValueMasked.LowerDataL R J (StepOneValueMasked.lowerMarkedM J) (level J T y)
    (head T (regimeRun (stepRegime J (level J T y)) T y))
    (tail T (regimeRun (stepRegime J (level J T y)) T y)) y at hD
  rw [hLevel,hRun] at hD
  simp only [head,tail] at hD
  rw [StepOneEmptyPrefix.split_of_length_le T _ le_rfl] at hD
  dsimp only at hD
  have hAnchor:=Seq.ContactLowerValue.lowerValueL_zero_eq R J g.domain.isWellFormed
    g.domain.one_le_d .refl T (by simpa only [BlowupTower.refl_append] using hbar)
    g.tangent ⊤ (subset_univ _)
    (by
      intro H hH
      change H∈(barMarked J).E.take J.E.length at hH
      rw [g.boundary,List.length_nil,List.take_zero] at hH
      exact False.elim (List.not_mem_nil hH))
    (contact_domain g) hKCan (mem_univ _) (by simpa only [BlowupTower.refl_append] using hp) hD
  change Seq.StepOneValueMasked.stepOneInvM R J T y=_
  simp only [Seq.StepOneValueMasked.stepOneInvM,Seq.StepOneValueMasked.stepOneInvL,if_neg hnsp]
  rw [hLevel,hRun]
  simp only [head,tail]
  rw [StepOneEmptyPrefix.split_of_length_le T _ le_rfl]
  exact congrArg (fun v : WithTop (ValTy q)=>toLex (0,v)) hAnchor

private theorem companion_value_of_stepCanon {Y : CMfd.{v} (n+1)} (T : BlowupTower X Y)
    (hCan : IsCanonical J ((invFamily (Nat.succ_pos n) (q+1)).inv J) T)
    (hStepCan : IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q) J) T)
    {y : Y} (hy : y∈(geoTransformAlong J T).cosupp) (hp : T.proj y∈ordMask J 1) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q) (compAt J 1 .refl)
      (restrict (ordMask J 1) T) ⟨y,hp⟩=
        Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q) J T y:=by
  let R:=invFamily (Nat.succ_pos n) q
  let O:=ordMask J 1
  let A : MarkedIdeal (n+1) O:=compAt J 1 .refl
  let P:=MarkedIdeal.pullback (Subtype.val : O→X) J
  let p : openPreimage T O:=⟨y,hp⟩
  have hA : IsInvDomain (q+1) A:=GeneralCompare.isInvDomain_compAt (Nat.succ_pos n) (by rfl) .refl g.domain
  have hAM : IsMaximalOrderAlong A.N A.ideal A.d:=GeneralCompare.isMaximalOrderAlong_compAt (Nat.succ_pos n) 1 .refl g.domain
  have hP : IsInvDomain (q+1) P:=InvDomainTowerAlong.isInvDomain_pullback_val O g.domain
  obtain ⟨_,_,hPM,_⟩:=StepOneRestrictOpen.hypotheses_restrict J O
    g.domain.isWellFormed g.domain.one_le_d g.maximal g.domain.dimLE
  have hEq : RestrictEquiv A P:=original_companion_equiv g
  have hEqPA : RestrictEquiv P A:=⟨hEq.N_eq.symm,hEq.E_eq.symm,hEq.d_eq.symm,hEq.N_eq ▸ hEq.ge,hEq.N_eq ▸ hEq.le⟩
  have hF:=StepOneSeq.isMaxOrderValue_stepOneInvM (k:=q+1) R (Nat.succ_pos n)
  have hCanP:=hF.isCanonical_restrict g.domain g.maximal O T hStepCan
  have hCanA:=hF.isCanonical_of_restrictEquiv hP hPM hA hAM hEqPA (restrict O T) hCanP
  have hcsP:=ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict (𝔪:=J)
    g.domain.isWellFormed.isClosedSubmanifold_N g.domain.isWellFormed.isCoherent O T (upper_test g T hCan)
  have hpP : p∈(geoTransformAlong P (restrict O T)).cosupp:=hcsP.symm ▸ hy
  have hcsA:=MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.cosupp_admissible_geoTransformAlong hEq
    hA.isWellFormed.isClosedSubmanifold_N.1 hA.isWellFormed.isCoherent hP.isWellFormed.isCoherent (restrict O T)
  have hpA : p∈(geoTransformAlong A (restrict O T)).cosupp:=hcsA.1.symm ▸ hpP
  have hRep:=hF.representative A P hA hAM hP hPM hEq (restrict O T) hCanA p hpA
  have hRest:=hF.restrictOpen J g.domain g.maximal O T hStepCan p hy
  exact hRep.trans hRest

private theorem full_value_of_stepCanon {Y : CMfd.{v} (n+1)} (T : BlowupTower X Y)
    (hCan : IsCanonical J ((invFamily (Nat.succ_pos n) (q+1)).inv J) T)
    (hStepCan : IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q) J) T)
    {y : Y} (hy : y∈(geoTransformAlong J T).cosupp)
    (hStep : Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q) J T y=stepMap q (contactValue q J u T y)) :
    (invFamily (Nat.succ_pos n) (q+1)).inv J T y=initialEmbedding q (contactValue q J u T y):=by
  let R:=invFamily (Nat.succ_pos n) q
  let F:=fun {M : CMfd.{v} (n+1)} (K : MarkedIdeal (n+1) M) {Z : CMfd.{v} (n+1)} (S : BlowupTower M Z) (z : Z)=>
    Seq.StepOneValueMasked.stepOneInvM R K S z
  have hOrd:=current_order_one g T hCan hy
  have hRun:=order_run g T hCan y hy
  have hp : T.proj y∈ordMask J 1:=by rw [initial_orderMask g];trivial
  have hLower:=(companion_value_of_stepCanon g T hCan hStepCan hy hp).trans hStep
  rw [invFamily_succ,generalStep_inv]
  change genInv F J T y=_
  rw [genInv_of_nmOrd_ne_zero F J T hOrd (by decide),hRun]
  simp only [head,tail]
  rw [StepOneEmptyPrefix.split_of_length_le T _ le_rfl]
  have hGen:=genLowerValue_eq_of_mem (T₀:=.refl) (T₁:=T) (y:=y) F J hp
  have hCoefficient:=hGen.trans
    (congrArg (fun v : ℕ ×ₗ WithTop (ValTy q)=>(v : WithTop (ℕ ×ₗ WithTop (ValTy q)))) hLower)
  exact congrArg (fun v : WithTop (ℕ ×ₗ WithTop (ValTy q))=>(toLex (1,Sum.inrₗ v) : ValTy (q+1))) hCoefficient

private theorem contact_maximum_of_value {Y : CMfd.{v} (n+1)} (T : BlowupTower X Y)
    (hT : IsGeoTestTower J T)
    (hFull : ∀y∈(geoTransformAlong J T).cosupp,
      (invFamily (Nat.succ_pos n) (q+1)).inv J T y=initialEmbedding q (contactValue q J u T y)) :
    ResolutionDriver.maxLocus ((invFamily (Nat.succ_pos n) q).inv (fixedContact J u) (restrict ⊤ T))
      (geoTransformAlong (fixedContact J u) (restrict ⊤ T)).cosupp=
      (Subtype.val : openPreimage T (⊤ : Opens X)→Y) ⁻¹'
        ResolutionDriver.maxLocus ((invFamily (Nat.succ_pos n) (q+1)).inv J T) (geoTransformAlong J T).cosupp:=by
  have hcs:=contact_cosupport g T hT
  ext p
  constructor
  · rintro ⟨hp,hmax⟩
    have hpJ:=(Set.ext_iff.mp hcs p).mp hp
    refine ⟨hpJ,?_⟩
    intro z hz
    let r : openPreimage T (⊤ : Opens X):=⟨z,mem_univ _⟩
    have hr:=(Set.ext_iff.mp hcs r).mpr hz
    have h:=(initialEmbedding q).monotone (hmax r hr)
    exact (hFull z hz).symm ▸ ((hFull p.val hpJ).symm ▸ h)
  · rintro ⟨hp,hmax⟩
    refine ⟨(Set.ext_iff.mp hcs p).mpr hp,?_⟩
    intro z hz
    have hzJ:=(Set.ext_iff.mp hcs z).mp hz
    have h:=hmax z.val hzJ
    exact (initialEmbedding q).le_iff_le.mp ((hFull z.val hzJ) ▸ ((hFull p.val hp) ▸ h))

private theorem actual_history_data : ∀{Y : CMfd.{v} (n+1)} (T : BlowupTower X Y),
    IsCanonical J ((invFamily (Nat.succ_pos n) (q+1)).inv J) T →
    IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q) J) T ∧
    IsCanonical (fixedContact J u) ((invFamily (Nat.succ_pos n) q).inv (fixedContact J u)) (restrict ⊤ T) ∧
    (∀y∈(geoTransformAlong J T).cosupp,
      Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q) J T y=stepMap q (contactValue q J u T y)) ∧
    (∀y∈(geoTransformAlong J T).cosupp,
      (invFamily (Nat.succ_pos n) (q+1)).inv J T y=initialEmbedding q (contactValue q J u T y))
  | _,.refl,_=>by
    refine ⟨trivial,trivial,?_,?_⟩
    · intro y hy
      exact step_value_of_canons g .refl trivial trivial trivial hy
    · intro y hy
      exact full_value_of_stepCanon g .refl trivial trivial hy
        (step_value_of_canons g .refl trivial trivial trivial hy)
  | _,.step T D π hπ,hCan=>by
    obtain ⟨hStepT,hKT,hStepVal,hFullVal⟩:=actual_history_data T hCan.1
    have ht:=upper_test g (.step T D π hπ) hCan
    have hStepMax:=upper_step_maximum_of_values q J u T hStepVal hFullVal
    have hKMax:=contact_maximum_of_value g T ht.1 hFullVal
    have hStepNext : IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q) J)
        (.step T D π hπ):=⟨hStepT,hCan.2.imp id (fun h=>h.trans hStepMax)⟩
    have hKNext : IsCanonical (fixedContact J u) ((invFamily (Nat.succ_pos n) q).inv (fixedContact J u))
        (restrict ⊤ (.step T D π hπ)):=by
      refine ⟨hKT,?_⟩
      change (Subtype.val : openPreimage T (⊤ : Opens X)→_) ⁻¹' D=∅ ∨
        (Subtype.val : openPreimage T (⊤ : Opens X)→_) ⁻¹' D=
          ResolutionDriver.maxLocus ((invFamily (Nat.succ_pos n) q).inv (fixedContact J u) (restrict ⊤ T))
            (geoTransformAlong (fixedContact J u) (restrict ⊤ T)).cosupp
      rcases hCan.2 with hEmpty | hMax
      · left
        rw [hEmpty,preimage_empty]
      · right
        exact (congrArg (fun A=>(Subtype.val : openPreimage T (⊤ : Opens X)→_) ⁻¹' A) hMax).trans hKMax.symm
    refine ⟨hStepNext,hKNext,?_,?_⟩
    · intro y hy
      exact step_value_of_canons g (.step T D π hπ) hCan hStepNext hKNext hy
    · intro y hy
      exact full_value_of_stepCanon g (.step T D π hπ) hCan hStepNext hy
        (step_value_of_canons g (.step T D π hπ) hCan hStepNext hKNext hy)

end Histories

/-- All original chronological years, including empty years, are retained by
both actual regimes of the prescribed canonical history. -/
theorem original_canonical_chronology {n q : ℕ} {X : CMfd.{v} (n+1)}
    (J : MarkedIdeal (n+1) X) (hJ : IsInvDomain (q+1) J)
    (hN : J.N=univ) (hE : J.E=[]) (hd : J.d=1)
    (hmax : IsMaximalOrderAlong J.N J.ideal J.d)
    (hZ : codimOnePartAlong J.N J.ideal J.d=∅) (u : X→ℂ)
    (hu : IsTangentDirectionAlong J.N J.ideal J.d univ u)
    {Y : CMfd.{v} (n+1)} (T : BlowupTower X Y)
    (hCan : IsCanonical J ((invFamily (Nat.succ_pos n) (q+1)).inv J) T) :
    (∀y : Y,¬IsSpecial J T y ∧ level J T y=0 ∧ regimeRun (stepRegime J 0) T y=T.length) ∧
    (∀y∈(geoTransformAlong J T).cosupp,
      nmOrd (geoTransformAlong J T) y=1 ∧ regimeRun (NonmonomialOrderRegime.OrdRegime J 1) T y=T.length):=by
  let g : OriginalGeometry J u q:=⟨hJ,hN,hE,hd,hmax,hZ,hu⟩
  have ht:=upper_test g T hCan
  exact ⟨fun y=>⟨current_not_special g T ht y,original_level g _ T y,step_run_test g T ht y⟩,
    fun y hy=>⟨current_order_one g T hCan hy,order_run g T hCan y hy⟩⟩

/-- The ORIGINAL source domain and original geometry construct the fixed
contact canonical history, its full invariant and complete next maximum on the
SAME actual clock. No later canonicality or value comparison is supplied. -/
theorem fixed_contact_canonical_history {n q : ℕ} {X : CMfd.{v} (n+1)}
    (J : MarkedIdeal (n+1) X) (hJ : IsInvDomain (q+1) J)
    (hN : J.N=univ) (hE : J.E=[]) (hd : J.d=1)
    (hmax : IsMaximalOrderAlong J.N J.ideal J.d)
    (hZ : codimOnePartAlong J.N J.ideal J.d=∅) (u : X→ℂ)
    (hu : IsTangentDirectionAlong J.N J.ideal J.d univ u)
    {Y : CMfd.{v} (n+1)} (T : BlowupTower X Y)
    (hCan : IsCanonical J ((invFamily (Nat.succ_pos n) (q+1)).inv J) T) :
    IsInvDomain q (fixedContact J u) ∧
    IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q) J) T ∧
    IsCanonical (fixedContact J u) ((invFamily (Nat.succ_pos n) q).inv (fixedContact J u)) (restrict ⊤ T) ∧
    (∀y∈(geoTransformAlong J T).cosupp,
      Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q) J T y=
        toLex (0,((invFamily (Nat.succ_pos n) q).inv (fixedContact J u) (restrict ⊤ T) ⟨y,mem_univ _⟩ : WithTop (ValTy q)))) ∧
    (∀y∈(geoTransformAlong J T).cosupp,
      (invFamily (Nat.succ_pos n) (q+1)).inv J T y=
        initialEmbedding q ((invFamily (Nat.succ_pos n) q).inv (fixedContact J u) (restrict ⊤ T) ⟨y,mem_univ _⟩)) ∧
    (geoTransformAlong (fixedContact J u) (restrict ⊤ T)).cosupp=
      (Subtype.val : openPreimage T (⊤ : Opens X)→Y) ⁻¹' (geoTransformAlong J T).cosupp ∧
    (geoTransformAlong (fixedContact J u) (restrict ⊤ T)).E=
      (geoTransformAlong J T).E.map ((Subtype.val : openPreimage T (⊤ : Opens X)→Y) ⁻¹' ·) ∧
    (geoTransformAlong J T).E.length=T.length ∧
    ResolutionDriver.maxLocus ((invFamily (Nat.succ_pos n) (q+1)).inv J T) (geoTransformAlong J T).cosupp=
      (Subtype.val : openPreimage T (⊤ : Opens X)→Y) ''
        ResolutionDriver.maxLocus ((invFamily (Nat.succ_pos n) q).inv (fixedContact J u) (restrict ⊤ T))
          (geoTransformAlong (fixedContact J u) (restrict ⊤ T)).cosupp:=by
  let g : OriginalGeometry J u q:=⟨hJ,hN,hE,hd,hmax,hZ,hu⟩
  have h:=actual_history_data g T hCan
  have ht:=upper_test g T hCan
  refine ⟨contact_domain g,h.1,h.2.1,h.2.2.1,h.2.2.2,contact_cosupport g T ht,?_,?_,?_⟩
  · have hE0 : (fixedContact J u).E=(MarkedIdeal.pullback (Subtype.val : (⊤ : Opens X)→X) J).E:=by
      rw [fixed_contact_record J hJ.isWellFormed.isCoherent hN hE hd]
      change [].map ((Subtype.val : (⊤ : Opens X)→X) ⁻¹' ·)=J.E.map ((Subtype.val : (⊤ : Opens X)→X) ⁻¹' ·)
      rw [hE]
    have he:=MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq hE0 (restrict ⊤ T)
    have hr:=MarkedIdealRestrictOpen.geoTransformAlong_restrict (𝔪:=J) ⊤
      hJ.isWellFormed.isClosedSubmanifold_N hJ.isWellFormed.isCoherent T ht
    exact he.trans (congrArg (fun A=>A.E) hr)
  · simpa only [hE,List.length_nil,Nat.zero_add] using length_E_geoTransformAlong J T
  · have hm:=contact_maximum_of_value g T ht h.2.2.2
    rw [hm]
    have hr : Set.range (Subtype.val : openPreimage T (⊤ : Opens X)→Y)=univ:=
      Set.range_eq_univ.mpr (fun y=>⟨⟨y,mem_univ _⟩,rfl⟩)
    rw [Set.image_preimage_eq_inter_range,hr,Set.inter_univ]

end
end Hironaka.HironakaActualMarkOneFixedContactHistory
