import TranscendentalNakamaye.Pending.HironakaDisjointFirstStepHistoricalAnchor
import TranscendentalNakamaye.Pending.StepOneEmptyPrefix
import TranscendentalNakamaye.Pending.SNCGlobalPrimeComponents
import TranscendentalNakamaye.Pending.DimensionMonotone
import TranscendentalNakamaye.Pending.CodimOnePartTowerAlong

/-! Every original full ambient canonical prefix is anchored to its ORIGINAL literal
normal contact history. Source-first BP: hironaka-disjoint-canonical-historical-anchor.tex.
No nonempty thin-to-base comparison, history reset, or full G1 closure is claimed. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace TranscendentalNakamaye.Pending.HironakaDisjointCanonicalHistoricalAnchor
noncomputable section
open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  MarkedIdealOperationsAlong.MarkedIdeal BlowupTowers BlowupTowerTransforms
  HironakaDisjointCoherentNormalRecoding HironakaDisjointFirstStepHistoricalAnchor
  HironakaActualZeroCoordinateContactSeed
  HironakaRelativeNormalIdeal HironakaActualCentreJointJets HironakaActualIntrinsicStableAmbientIso
  GermIdealOrder RelativePrincipalizationSpan GermIdealPullbackCalculus
  InvertibleIdealQuotient IdealWeightPowers DivisorExponentAlong
  HomogenizedIdealAlong StepOneValue StepOneRegime StepOneLowerDomain
  HironakaSharpOriginalProductTraceOrder RestrictedIdealExtension InvDomainRebase
  CanonicalCentres ContactStageKept GeneralValue NonmonomialOrderTail MonomialPartAlong
  CompanionReductionAlong CoefficientIdeal HomogenizedGlueing DerivativeIdeal TangentDirectionAlong GermIdealTotalTransform
  CodimOneSupportAlong NormalCrossings NonmonomialOrderLocal BlowupTowerSplit
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

private abbrev model (n : ℕ) : CMfd n := CMfd.of (n := n) (ComplexModel n)
variable {n : ℕ}

private theorem stabilized_maximal_order {I : GermIdeal n (ComplexModel n)} (hI : I.IsCoherent) :
    IsMaximalOrderAlong (stabilizedMarked I).N (stabilizedMarked I).ideal (stabilizedMarked I).d := by
  intro z hz
  have hp : z∈ordMask (M := model (n+1)) (stabilizedMarked I) 1 := by
    rw [stabilized_initial_orderMask hI]
    trivial
  have hnot := notMem_ordGe_of_mem_ordMask hp
  change z∉ordGe (ordinaryTraceMarked (X := model (n+1)) univ (stabilizedIdeal I)) 2 at hnot
  rw [ordGe_ordinaryTraceMarked_eq_cosupport (X := model (n+1)) univ (stabilizedIdeal I) (stabilizedIdeal_isCoherent hI) 2] at hnot
  exact hnot hz

private theorem bar_test {q : ℕ} {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I)) {Y : CMfd (n+1)}
    (T : BlowupTower (model (n+1)) Y) (hT : IsGeoTestTower (stabilizedMarked I) T) :
    IsGeoTestTower (barMarked (stabilizedMarked I)) T := by
  have hd := stabilized_isInvDomain hM
  exact ((HomogenizedIdealAlongTower.coeff_homAlong_wEquiv (X := model (n+1))
    (stabilizedMarked I) hd.isWellFormed.isClosedSubmanifold_N hd.isWellFormed.isCoherent hd.one_le_d).2 T).1.mpr hT

private theorem initial_codimOne_empty {q : ℕ} {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I)) :
    codimOnePartAlong (stabilizedMarked I).N (stabilizedMarked I).ideal (stabilizedMarked I).d=∅ := by
  have hd := stabilized_isInvDomain hM
  have hbar : codimOnePartAlong (barMarked (X := model (n+1)) (stabilizedMarked I)).N
      (barMarked (X := model (n+1)) (stabilizedMarked I)).ideal
      (barMarked (X := model (n+1)) (stabilizedMarked I)).d=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact stabilized_not_special hM z (Or.inl ⟨rfl,hz⟩)
  have hw := HomogenizedIdealAlongTower.coeff_homAlong_wEquiv (X := model (n+1))
    (stabilizedMarked I) hd.isWellFormed.isClosedSubmanifold_N hd.isWellFormed.isCoherent hd.one_le_d
  have he := CodimOnePartCanonical.codimOnePartAlong_geoTransformAlong_of_wEquiv
    (X := model (n+1)) (𝔪 := barMarked (stabilizedMarked I)) hw rfl .refl trivial
  exact he.symm.trans hbar

private theorem current_codimOne_empty {q : ℕ} {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I)) {Y : CMfd (n+1)}
    (T : BlowupTower (model (n+1)) Y) (hT : IsGeoTestTower (stabilizedMarked I) T) :
    codimOnePartAlong (geoTransformAlong (stabilizedMarked I) T).N
      (geoTransformAlong (stabilizedMarked I) T).ideal (geoTransformAlong (stabilizedMarked I) T).d=∅ := by
  have hd := stabilized_isInvDomain hM
  exact CodimOnePartTowerAlong.codimOnePartAlong_geoTransformAlong_eq_empty (stabilizedMarked I)
    hd.isWellFormed hd.one_le_d (stabilized_maximal_order (I := I) hM.isWellFormed.isCoherent)
    (initial_codimOne_empty hM) T hT

private theorem current_not_special {q : ℕ} {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I)) {Y : CMfd (n+1)}
    (T : BlowupTower (model (n+1)) Y) (hT : IsGeoTestTower (stabilizedMarked I) T) (y : Y) :
    ¬ IsSpecial (stabilizedMarked I) T y := by
  have hd := stabilized_isInvDomain hM
  have hw := HomogenizedIdealAlongTower.coeff_homAlong_wEquiv (X := model (n+1))
    (stabilizedMarked I) hd.isWellFormed.isClosedSubmanifold_N hd.isWellFormed.isCoherent hd.one_le_d
  have he := CodimOnePartCanonical.codimOnePartAlong_geoTransformAlong_of_wEquiv
    (X := model (n+1)) (𝔪 := barMarked (stabilizedMarked I)) hw rfl T (bar_test hM T hT)
  rw [current_codimOne_empty hM T hT] at he
  rintro (⟨_,hz⟩ | ⟨hpos,_⟩)
  · rw [he] at hz
    exact hz
  · rw [original_level_zero] at hpos
    omega

private theorem mem_of_spanOn_univ {Y : CMfd (n+1)} {A : GermIdeal (n+1) Y}
    (hA : A.IsCoherent) {y : Y} {g : Y → ℂ} (hg : HolomorphicAt (n+1) g y)
    (hs : IsInSpanOnAt (n := n+1) univ (A.mem y) y g) : A.mem y g := by
  obtain ⟨N,s,a,hs,ha,heq⟩ := hs
  exact mem_of_isInSpanAt_mem hA ⟨hg,N,s,a,hs,ha,heq.mono fun z hz => hz (mem_univ z)⟩

private theorem current_order_positive {q : ℕ} {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I)) {Y : CMfd (n+1)}
    (T : BlowupTower (model (n+1)) Y) (hT : IsGeoTestTower (stabilizedMarked I) T)
    {y : Y} (hy : y∈(geoTransformAlong (stabilizedMarked I) T).cosupp) :
    1≤nmOrd (geoTransformAlong (stabilizedMarked I) T) y := by
  have hd := stabilized_isInvDomain hM
  have hA := InvDomainTowerAlong.isInvDomain_geoTransformAlong hd T hT
  have hN : (geoTransformAlong (stabilizedMarked I) T).N=univ :=
    (pullback_eq_mul_geoTransformAlong (𝔪 := stabilizedMarked I) rfl hd.isWellFormed.isCoherent T hT).1
  have hmax := isMaximalOrderAlong_geoTransformAlong hd.isWellFormed.isClosedSubmanifold_N
    hd.isWellFormed.isCoherent (stabilized_maximal_order (I := I) hM.isWellFormed.isCoherent) T hT
  have hOne := one_mem_monomial_of_empty_codimOne (geoTransformAlong (stabilizedMarked I) T)
    hA.isWellFormed hN (d_geoTransformAlong (stabilizedMarked I) T) hmax (current_codimOne_empty hM T hT) y
  apply (mem_ordGe_iff hA.isWellFormed hA.isNonzeroAlongAt hy.1 1).mp
  refine ⟨hy.1,?_⟩
  intro g hg
  have hprod := hg.2 (fun _ => 1) hOne
  have hs : IsInSpanOnAt (n := n+1) univ
      ((geoTransformAlong (stabilizedMarked I) T).ideal.mem y) y g := by
    simpa only [hN,one_mul,mul_one] using hprod.2
  have hmem := mem_of_spanOn_univ hA.isWellFormed.isCoherent hg.1 hs
  simpa only [d_geoTransformAlong,stabilizedMarked] using hy.2 g hmem

private theorem normal_tangent : IsTangentDirectionAlong
    (univ : Set (ComplexModel (n+1))) (vanishingIdeal (n := n+1) (zeroPlane n)) 1 univ
    (addedCoordinate n) := by
  have he : zeroCarrier (univ : Set (ComplexModel n))=zeroPlane n := by
    ext z
    change (tangentProjection n 1 z∈(univ : Set (ComplexModel n)) ∧
      actualJointNormalProjection n 1 z=0) ↔ actualJointNormalProjection n 1 z=0
    simp only [mem_univ,true_and]
  simpa only [zeroIdeal,he] using zero_coordinate_tangent (univ : Set (ComplexModel n))

private theorem stabilized_tangent {I : GermIdeal n (ComplexModel n)} :
    IsTangentDirectionAlong (univ : Set (ComplexModel (n+1))) (stabilizedIdeal I) 1 univ
      (addedCoordinate n) := by
  have hnormal : (vanishingIdeal (n := n+1) (zeroPlane n)).IsCoherent := by
    apply CartanIrreducible.cartanCoherence
    exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
      (actualJointNormalProjection n 1).contMDiff
      (FibreDimensionLowerBound.isComplexAnalyticSubset_singleton (0 : ComplexModel 1))
  refine ⟨isOpen_univ,?_,normal_tangent.multiplicity_one⟩
  intro x hx
  exact le_sumIdeal_right hnormal x _ (normal_tangent.mem x hx)

private theorem normalContact_domain {q : ℕ} {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I)) : IsInvDomain q (normalContact I) := by
  have hd := stabilized_isInvDomain hM
  have h := ContactStageInvDomain.isInvDomain_stage_coeffHomAlong_of_le (X := model (n+1))
    (k := q+1) (stabilizedMarked I) hd.isWellFormed hd.one_le_d hd.dimLE
    ⊤ (stabilized_tangent (I := I)) .refl trivial ⊤ (subset_univ _)
    (by intro y _ _ hz; exact stabilized_not_special hM y (Or.inl ⟨rfl,hz⟩))
    (by intro H hH; cases hH)
  exact h

private theorem normalContact_cosupport {q : ℕ} {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I)) {Y : CMfd (n+1)}
    (T : BlowupTower (model (n+1)) Y) (hT : IsGeoTestTower (stabilizedMarked I) T) :
    (geoTransformAlong (normalContact I) (restrict ⊤ T)).cosupp=
      (Subtype.val : openPreimage T (⊤ : Opens (ComplexModel (n+1))) → Y) ⁻¹'
        (geoTransformAlong (stabilizedMarked I) T).cosupp := by
  have hd := stabilized_isInvDomain hM
  have hw := HomogenizedIdealAlongTower.coeff_homAlong_wEquiv (X := model (n+1))
    (stabilizedMarked I) hd.isWellFormed.isClosedSubmanifold_N hd.isWellFormed.isCoherent hd.one_le_d
  have hbar := bar_test hM T hT
  have h := ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le (X := model (n+1))
    (stabilizedMarked I) hd.isWellFormed.isClosedSubmanifold_N hd.isWellFormed.isCoherent hd.one_le_d
    ⊤ (stabilized_tangent (I := I)) .refl T (by simpa only [BlowupTower.refl_append] using hbar) ⊤ (subset_univ _)
  exact h.2.trans (congrArg (fun A : Set Y =>
    (Subtype.val : openPreimage T (⊤ : Opens (ComplexModel (n+1))) → Y) ⁻¹' A) (by simpa only [BlowupTower.refl_append] using ((hw.2 T).2 hbar)))

private theorem original_companion_equiv {I : GermIdeal n (ComplexModel n)}
    (hI : I.IsCoherent) :
    RestrictEquiv (compAt (X := model (n+1)) (stabilizedMarked I) 1 .refl)
      (MarkedIdeal.pullback (Subtype.val : ordMask (M := model (n+1)) (stabilizedMarked I) 1 → ComplexModel (n+1))
        (stabilizedMarked I)) := by
  let O := ordMask (M := model (n+1)) (stabilizedMarked I) 1
  change RestrictEquiv
    (companionAlong (X := CMfd.of (n := n+1) O) ((Subtype.val : O → ComplexModel (n+1)) ⁻¹' univ) []
      (nonmonomialPartAlong (n+1) ((Subtype.val : O → ComplexModel (n+1)) ⁻¹' univ)
        (GermIdeal.pullback (m := n+1) (Subtype.val : O → ComplexModel (n+1)) (stabilizedIdeal I)) [])
      (monomialPartAlong (n+1) ((Subtype.val : O → ComplexModel (n+1)) ⁻¹' univ)
        (GermIdeal.pullback (m := n+1) (Subtype.val : O → ComplexModel (n+1)) (stabilizedIdeal I)) []) 1 1)
    (⟨(Subtype.val : O → ComplexModel (n+1)) ⁻¹' univ, [],
      GermIdeal.pullback (m := n+1) (Subtype.val : O → ComplexModel (n+1)) (stabilizedIdeal I), 1⟩ : MarkedIdeal (n+1) O)
  rw [companionAlong,if_neg (Nat.lt_irrefl 1),nonmonomialPartAlong_nil_eq_restrictOn]
  exact ⟨rfl,rfl,rfl,restrictLe_restrictOn,
    restrictLe_self_restrictOn (isCoherent_pullback contMDiff_subtype_val (stabilizedIdeal_isCoherent hI))⟩

private theorem upper_test {q : ℕ} (hn : 0<n) {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I)) {Y : CMfd (n+1)}
    (T : BlowupTower (model (n+1)) Y)
    (hCan : IsCanonical (stabilizedMarked I)
      ((invFamily (Nat.succ_pos n) (q+1)).inv (stabilizedMarked I)) T) :
    IsGeoTestTower (stabilizedMarked I) T :=
  (invFamily (Nat.lt_trans hn (Nat.lt_succ_self n)) (q+1)).isInvValue.isGeoTestTower_of_isCanonical
    (stabilized_isInvDomain hM) T hCan

private theorem step_run_test {q : ℕ} {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I)) :
    ∀ {Y : CMfd (n+1)} (T : BlowupTower (model (n+1)) Y),
      IsGeoTestTower (stabilizedMarked I) T → ∀ y : Y,
      regimeRun (stepRegime (X := model (n+1)) (stabilizedMarked I) 0) T y=T.length
  | _,.refl,_,_ => rfl
  | _,.step T C π hπ,hT,y => by
    have hreg : stepRegime (X := model (n+1)) (stabilizedMarked I) 0 T (π y) :=
      ⟨original_level_zero I T (π y),current_not_special hM T hT.1 (π y)⟩
    exact (regimeRun_step_of (X := model (n+1)) _ T C π hπ hreg).trans
      (congrArg (fun r => r+1) (step_run_test hM T hT.1 (π y)))

section Canonical
variable {q : ℕ} (hn : 0<n) {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I)) {Y : CMfd (n+1)}
    (T : BlowupTower (model (n+1)) Y)
    (hCan : IsCanonical (stabilizedMarked I)
      ((invFamily (Nat.succ_pos n) (q+1)).inv (stabilizedMarked I)) T)
include hn hM hCan

/-- No special branch appears on the original full ambient canonical history. -/
theorem canonical_not_special (y : Y) : ¬ IsSpecial (stabilizedMarked I) T y :=
  current_not_special hM T (upper_test hn hM T hCan) y

/-- Born boundary is retained while the full ambient nonmonomial order stays one. -/
theorem canonical_order_one {y : Y} (hy : y∈(geoTransformAlong (stabilizedMarked I) T).cosupp) :
    nmOrd (geoTransformAlong (stabilizedMarked I) T) y=1 := by
  have hd := stabilized_isInvDomain hM
  have ht := upper_test hn hM T hCan
  have hf : NonmonomialOrderCanonical.OrdMonotone (X := model (n+1)) (stabilizedMarked I)
      ((invFamily (Nat.succ_pos n) (q+1)).inv (X := model (n+1)) (stabilizedMarked I)) :=
    ordMonotone_genInv _ _
  have h := NonmonomialOrderCanonical.nmOrd_le_nmOrd_proj (X := model (n+1))
    (Nat.lt_trans hn (Nat.lt_succ_self n)) hd hf .refl T
    (by simpa only [BlowupTower.refl_append] using ht)
    (by simpa only [BlowupTower.refl_append] using hCan) y
    (by simpa only [BlowupTower.refl_append] using hy)
  have h' : T.proj y∈(stabilizedMarked I).cosupp ∧
      nmOrd (geoTransformAlong (stabilizedMarked I) T) y≤nmOrd (M := model (n+1)) (stabilizedMarked I) (T.proj y) := by
    simpa only [BlowupTower.refl_append,geoTransformAlong_refl] using h
  exact Nat.le_antisymm (h'.2.trans_eq (stabilized_order_one hM h'.1))
    (current_order_positive hM T ht hy)

/-- The actual Step One run includes every real and empty historical year. -/
theorem canonical_step_run (y : Y) :
    regimeRun (stepRegime (X := model (n+1)) (stabilizedMarked I) 0) T y=T.length :=
  step_run_test hM T (upper_test hn hM T hCan) y

/-- The literal original contact has the complete true upper cosupport trace. -/
theorem canonical_contact_cosupport :
    IsInvDomain q (normalContact I) ∧
    (geoTransformAlong (normalContact I) (restrict ⊤ T)).cosupp=
      (Subtype.val : openPreimage T (⊤ : Opens (ComplexModel (n+1))) → Y) ⁻¹'
        (geoTransformAlong (stabilizedMarked I) T).cosupp :=
  ⟨normalContact_domain hM,normalContact_cosupport hM T (upper_test hn hM T hCan)⟩

/-- The whole ordered born boundary is pulled back without deleting any slot. -/
theorem canonical_boundary :
    (geoTransformAlong (normalContact I) (restrict ⊤ T)).E=
      (geoTransformAlong (stabilizedMarked I) T).E.map
        ((Subtype.val : openPreimage T (⊤ : Opens (ComplexModel (n+1))) → Y) ⁻¹' ·) ∧
      (geoTransformAlong (stabilizedMarked I) T).E.length=T.length := by
  have hd := stabilized_isInvDomain hM
  have he := MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
    (𝔪 := normalContact I)
    (𝔫 := MarkedIdeal.pullback (Subtype.val : (⊤ : Opens (ComplexModel (n+1))) → ComplexModel (n+1))
      (stabilizedMarked I)) rfl (restrict ⊤ T)
  have hr := MarkedIdealRestrictOpen.geoTransformAlong_restrict (X := model (n+1))
    (𝔪 := stabilizedMarked I) ⊤ hd.isWellFormed.isClosedSubmanifold_N hd.isWellFormed.isCoherent
    T (upper_test hn hM T hCan)
  refine ⟨he.trans (congrArg (fun A => A.E) hr),?_⟩
  simpa only [stabilizedMarked,List.length_nil,Nat.zero_add] using length_E_geoTransformAlong (stabilizedMarked I) T

end Canonical

/-- The full original order run retains every actual canonical prefix year. -/
theorem canonical_order_run {q : ℕ} (hn : 0<n) {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I)) :
    ∀ {Y : CMfd (n+1)} (T : BlowupTower (model (n+1)) Y),
      IsCanonical (stabilizedMarked I) ((invFamily (Nat.succ_pos n) (q+1)).inv (stabilizedMarked I)) T →
      ∀ y∈(geoTransformAlong (stabilizedMarked I) T).cosupp,
      regimeRun (NonmonomialOrderRegime.OrdRegime (X := model (n+1)) (stabilizedMarked I) 1) T y=T.length
  | _,.refl,_,_,_ => rfl
  | _,.step T C π hπ,hCan,y,hy => by
    have ht := upper_test hn hM (.step T C π hπ) hCan
    have hd := stabilized_isInvDomain hM
    have hf : NonmonomialOrderCanonical.OrdMonotone (X := model (n+1)) (stabilizedMarked I)
        ((invFamily (Nat.succ_pos n) (q+1)).inv (X := model (n+1)) (stabilizedMarked I)) :=
      ordMonotone_genInv _ _
    have hp := (NonmonomialOrderCanonical.nmOrd_step_le_of_canonical (X := model (n+1))
      (Nat.lt_trans hn (Nat.lt_succ_self n)) hd hf T C π hπ ht hCan.2 hy).1
    have hreg : NonmonomialOrderRegime.OrdRegime (X := model (n+1)) (stabilizedMarked I) 1 T (π y) :=
      ⟨hp,canonical_order_one hn hM T hCan.1 hp⟩
    exact (regimeRun_step_of (X := model (n+1)) _ T C π hπ hreg).trans
      (congrArg (fun r => r+1) (canonical_order_run hn hM T hCan.1 (π y) hp))

private def stepMap (q : ℕ) (v : ValTy q) : ℕ ×ₗ WithTop (ValTy q) := toLex (0,(v : WithTop (ValTy q)))

private theorem stepMap_le (q : ℕ) (v w : ValTy q) : stepMap q v≤stepMap q w ↔ v≤w := by
  simp [stepMap,Prod.Lex.toLex_le_toLex]

section Anchors
variable {q : ℕ} (hn : 0<n) {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I)) {Y : CMfd (n+1)}
    (T : BlowupTower (model (n+1)) Y)
    (hCan : IsCanonical (stabilizedMarked I)
      ((invFamily (Nat.succ_pos n) (q+1)).inv (stabilizedMarked I)) T)
    (hStepCan : IsCanonical (X := model (n+1)) (stabilizedMarked I)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q) (stabilizedMarked I)) T)
include hn hM hCan hStepCan

private theorem step_value_of_canons
    (hKCan : IsCanonical (normalContact I) ((invFamily (Nat.succ_pos n) q).inv (normalContact I)) (restrict ⊤ T))
    {y : Y} (hy : y∈(geoTransformAlong (stabilizedMarked I) T).cosupp) :
    Seq.StepOneValueMasked.stepOneInvM (X := model (n+1)) (invFamily (Nat.succ_pos n) q)
      (stabilizedMarked I) T y =
      stepMap q ((invFamily (Nat.succ_pos n) q).inv (normalContact I) (restrict ⊤ T) ⟨y,mem_univ _⟩) := by
  let J := (stabilizedMarked I : MarkedIdeal (n+1) (model (n+1)))
  let R := invFamily (Nat.succ_pos n) q
  have hd := stabilized_isInvDomain hM
  have hmax := stabilized_maximal_order (I := I) hM.isWellFormed.isCoherent
  have ht := upper_test hn hM T hCan
  have hbar := bar_test hM T ht
  have hbarcan := (Seq.StepOneBridge.isCanonical_iff (X := model (n+1)) (k := q+1)
    R J hd hmax (Nat.succ_pos n) T).mp hStepCan
  have hnsp : ¬ IsSpecial (X := model (n+1)) J T y := canonical_not_special hn hM T hCan y
  have hw := HomogenizedIdealAlongTower.coeff_homAlong_wEquiv (X := model (n+1))
    J hd.isWellFormed.isClosedSubmanifold_N hd.isWellFormed.isCoherent hd.one_le_d
  have hp : y∈(geoTransformAlong (barMarked (X := model (n+1)) J) T).cosupp :=
    ((hw.2 T).2 hbar).symm ▸ hy
  have hD := Seq.StepOneCanonicalTail.hasLowerDataL_of_isCanonical (X := model (n+1)) J (k := q+1) R
    hd.isWellFormed hd.one_le_d (Nat.succ_pos n) hmax hd.dimLE T hbar hbarcan y hp hnsp
  have hRun := canonical_step_run hn hM T hCan y
  have hLevel := original_level_zero I T y
  change Seq.StepOneValueMasked.LowerDataL (X := model (n+1)) R J
    (StepOneValueMasked.lowerMarkedM (X := model (n+1)) J) (level (X := model (n+1)) J T y)
    (head T (regimeRun (stepRegime (X := model (n+1)) J (level (X := model (n+1)) J T y)) T y))
    (tail T (regimeRun (stepRegime (X := model (n+1)) J (level (X := model (n+1)) J T y)) T y)) y at hD
  rw [hLevel,hRun] at hD
  simp only [head,tail] at hD
  rw [StepOneEmptyPrefix.split_of_length_le T _ le_rfl] at hD
  dsimp only at hD
  have hAnchor := Seq.ContactLowerValue.lowerValueL_zero_eq (X := model (n+1)) R J hd.isWellFormed
    hd.one_le_d .refl T (by simpa only [BlowupTower.refl_append] using hbar)
    (stabilized_tangent (I := I)) ⊤ (subset_univ _) (by intro H hH; cases hH)
    (normalContact_domain hM) hKCan (mem_univ _) (by simpa only [BlowupTower.refl_append] using hp) hD
  change Seq.StepOneValueMasked.stepOneInvM (X := model (n+1)) R J T y=_
  simp only [Seq.StepOneValueMasked.stepOneInvM,Seq.StepOneValueMasked.stepOneInvL,if_neg hnsp]
  rw [hLevel,hRun]
  simp only [head,tail]
  rw [StepOneEmptyPrefix.split_of_length_le T _ le_rfl]
  exact congrArg (fun v : WithTop (ValTy q) => toLex (0,v)) hAnchor

private theorem companion_value_of_stepCanon {y : Y}
    (hy : y∈(geoTransformAlong (stabilizedMarked I) T).cosupp)
    (hp : T.proj y∈ordMask (M := model (n+1)) (stabilizedMarked I) 1) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q)
      (X := CMfd.of (n := n+1) (ordMask (M := model (n+1)) (stabilizedMarked I) 1))
      (compAt (X := model (n+1)) (stabilizedMarked I) 1 .refl)
      (restrict (ordMask (M := model (n+1)) (stabilizedMarked I) 1) T) ⟨y,hp⟩ =
      Seq.StepOneValueMasked.stepOneInvM (X := model (n+1)) (invFamily (Nat.succ_pos n) q)
        (stabilizedMarked I) T y := by
  have hI : I.IsCoherent := hM.isWellFormed.isCoherent
  let J := (stabilizedMarked I : MarkedIdeal (n+1) (model (n+1)))
  let R := invFamily (Nat.succ_pos n) q
  let O := ordMask (M := model (n+1)) J 1
  let A : MarkedIdeal (n+1) O := compAt (X := model (n+1)) J 1 .refl
  let P := MarkedIdeal.pullback (Subtype.val : O → ComplexModel (n+1)) J
  let p : openPreimage T O := ⟨y,hp⟩
  have hd := stabilized_isInvDomain hM
  have hmax := stabilized_maximal_order hI
  have hA : IsInvDomain (q+1) A := GeneralCompare.isInvDomain_compAt
    (X := model (n+1)) (Nat.succ_pos n) (by rfl) .refl hd
  have hAM : IsMaximalOrderAlong A.N A.ideal A.d :=
    GeneralCompare.isMaximalOrderAlong_compAt (X := model (n+1)) (Nat.succ_pos n) 1 .refl hd
  have hP : IsInvDomain (q+1) P := InvDomainTowerAlong.isInvDomain_pullback_val O hd
  obtain ⟨_,_,hPM,_⟩ := StepOneRestrictOpen.hypotheses_restrict (X := model (n+1)) J O
    hd.isWellFormed hd.one_le_d hmax hd.dimLE
  have hEq : RestrictEquiv A P := original_companion_equiv hI
  have hEqPA : RestrictEquiv P A :=
    ⟨hEq.N_eq.symm,hEq.E_eq.symm,hEq.d_eq.symm,hEq.N_eq ▸ hEq.ge,hEq.N_eq ▸ hEq.le⟩
  have hF := StepOneSeq.isMaxOrderValue_stepOneInvM (k := q+1) R (Nat.lt_trans hn (Nat.lt_succ_self n))
  have hCanP := hF.isCanonical_restrict (X := model (n+1)) hd hmax O T hStepCan
  have hCanA := hF.isCanonical_of_restrictEquiv (X := CMfd.of (n := n+1) O)
    hP hPM hA hAM hEqPA (restrict O T) hCanP
  have hcsP := ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict (X := model (n+1))
    (𝔪 := J) hd.isWellFormed.isClosedSubmanifold_N hd.isWellFormed.isCoherent O T (upper_test hn hM T hCan)
  have hpP : p∈(geoTransformAlong P (restrict O T)).cosupp := hcsP.symm ▸ hy
  have hcsA := MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.cosupp_admissible_geoTransformAlong hEq
    hA.isWellFormed.isClosedSubmanifold_N.1 hA.isWellFormed.isCoherent hP.isWellFormed.isCoherent (restrict O T)
  have hpA : p∈(geoTransformAlong A (restrict O T)).cosupp := hcsA.1.symm ▸ hpP
  have hRep := hF.representative (X := CMfd.of (n := n+1) O) A P hA hAM hP hPM hEq (restrict O T) hCanA p hpA
  have hRest := hF.restrictOpen (X := model (n+1)) J hd hmax O T hStepCan p hy
  exact hRep.trans hRest

private theorem full_value_of_stepCanon {y : Y}
    (hy : y∈(geoTransformAlong (stabilizedMarked I) T).cosupp)
    (hStep : Seq.StepOneValueMasked.stepOneInvM (X := model (n+1)) (invFamily (Nat.succ_pos n) q)
      (stabilizedMarked I) T y=stepMap q ((invFamily (Nat.succ_pos n) q).inv (normalContact I) (restrict ⊤ T) ⟨y,mem_univ _⟩)) :
    (invFamily (Nat.succ_pos n) (q+1)).inv (X := model (n+1)) (stabilizedMarked I) T y=
      initialEmbedding q ((invFamily (Nat.succ_pos n) q).inv (normalContact I) (restrict ⊤ T) ⟨y,mem_univ _⟩) := by
  let J := (stabilizedMarked I : MarkedIdeal (n+1) (model (n+1)))
  let R := invFamily (Nat.succ_pos n) q
  let F := fun {X : CMfd (n+1)} (K : MarkedIdeal (n+1) X) {Z : CMfd (n+1)}
    (S : BlowupTower X Z) (z : Z) => Seq.StepOneValueMasked.stepOneInvM (X := X) R K (Y := Z) S z
  have hOrd := canonical_order_one hn hM T hCan hy
  have hRun := canonical_order_run hn hM T hCan y hy
  have hp : T.proj y∈ordMask (M := model (n+1)) J 1 := by
    rw [stabilized_initial_orderMask (I := I) hM.isWellFormed.isCoherent]
    trivial
  have hLower := (companion_value_of_stepCanon hn hM T hCan hStepCan hy hp).trans hStep
  rw [invFamily_succ,generalStep_inv]
  change genInv (X := model (n+1)) F J T y=_
  rw [genInv_of_nmOrd_ne_zero (X := model (n+1)) F J T hOrd (by decide),hRun]
  simp only [head,tail]
  rw [StepOneEmptyPrefix.split_of_length_le T _ le_rfl]
  have hGen := genLowerValue_eq_of_mem (X := model (n+1)) (T₀ := .refl) (T₁ := T) (y := y) F J hp
  have hCoefficient := hGen.trans
    (congrArg (fun v : ℕ ×ₗ WithTop (ValTy q) => (v : WithTop (ℕ ×ₗ WithTop (ValTy q)))) hLower)
  exact congrArg (fun v : WithTop (ℕ ×ₗ WithTop (ValTy q)) => (toLex (1,Sum.inrₗ v) : ValTy (q+1))) hCoefficient

end Anchors

private abbrev contactValue (q : ℕ) (I : GermIdeal n (ComplexModel n)) {Y : CMfd (n+1)}
    (T : BlowupTower (model (n+1)) Y) (y : Y) : ValTy q :=
  (invFamily (Nat.succ_pos n) q).inv (normalContact I) (restrict ⊤ T) ⟨y,mem_univ _⟩

private theorem upper_step_maximum_of_values (q : ℕ) (I : GermIdeal n (ComplexModel n))
    {Y : CMfd (n+1)} (T : BlowupTower (model (n+1)) Y)
    (hStep : ∀ y∈(geoTransformAlong (stabilizedMarked I) T).cosupp,
      Seq.StepOneValueMasked.stepOneInvM (X := model (n+1)) (invFamily (Nat.succ_pos n) q)
        (stabilizedMarked I) T y=stepMap q (contactValue q I T y))
    (hFull : ∀ y∈(geoTransformAlong (stabilizedMarked I) T).cosupp,
      (invFamily (Nat.succ_pos n) (q+1)).inv (X := model (n+1)) (stabilizedMarked I) T y=
        initialEmbedding q (contactValue q I T y)) :
    ResolutionDriver.maxLocus ((invFamily (Nat.succ_pos n) (q+1)).inv (X := model (n+1)) (stabilizedMarked I) T)
      (geoTransformAlong (stabilizedMarked I) T).cosupp =
    ResolutionDriver.maxLocus (Seq.StepOneValueMasked.stepOneInvM (X := model (n+1))
      (invFamily (Nat.succ_pos n) q) (stabilizedMarked I) T) (geoTransformAlong (stabilizedMarked I) T).cosupp := by
  ext y
  constructor
  · rintro ⟨hy,hmax⟩
    refine ⟨hy,?_⟩
    intro z hz
    have h := hmax z hz
    rw [hFull z hz,hFull y hy] at h
    rw [hStep z hz,hStep y hy]
    exact (stepMap_le q _ _).mpr ((initialEmbedding q).le_iff_le.mp h)
  · rintro ⟨hy,hmax⟩
    refine ⟨hy,?_⟩
    intro z hz
    have h := hmax z hz
    rw [hStep z hz,hStep y hy] at h
    rw [hFull z hz,hFull y hy]
    exact (initialEmbedding q).monotone ((stepMap_le q _ _).mp h)

private theorem contact_maximum_of_value {q : ℕ} {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I)) {Y : CMfd (n+1)} (T : BlowupTower (model (n+1)) Y)
    (hT : IsGeoTestTower (stabilizedMarked I) T)
    (hFull : ∀ y∈(geoTransformAlong (stabilizedMarked I) T).cosupp,
      (invFamily (Nat.succ_pos n) (q+1)).inv (X := model (n+1)) (stabilizedMarked I) T y=
        initialEmbedding q (contactValue q I T y)) :
    ResolutionDriver.maxLocus ((invFamily (Nat.succ_pos n) q).inv (normalContact I) (restrict ⊤ T))
      (geoTransformAlong (normalContact I) (restrict ⊤ T)).cosupp =
    (Subtype.val : openPreimage T (⊤ : Opens (ComplexModel (n+1))) → Y) ⁻¹'
      ResolutionDriver.maxLocus ((invFamily (Nat.succ_pos n) (q+1)).inv (X := model (n+1)) (stabilizedMarked I) T)
        (geoTransformAlong (stabilizedMarked I) T).cosupp := by
  have hcs := normalContact_cosupport hM T hT
  ext p
  constructor
  · rintro ⟨hp,hmax⟩
    have hpJ := (Set.ext_iff.mp hcs p).mp hp
    refine ⟨hpJ,?_⟩
    intro z hz
    let r : openPreimage T (⊤ : Opens (ComplexModel (n+1))) := ⟨z,mem_univ _⟩
    have hr := (Set.ext_iff.mp hcs r).mpr hz
    have h := (initialEmbedding q).monotone (hmax r hr)
    exact (hFull z hz).symm ▸ ((hFull p.val hpJ).symm ▸ h)
  · rintro ⟨hp,hmax⟩
    refine ⟨(Set.ext_iff.mp hcs p).mpr hp,?_⟩
    intro z hz
    have hzJ := (Set.ext_iff.mp hcs z).mp hz
    have h := hmax z.val hzJ
    exact (initialEmbedding q).le_iff_le.mp ((hFull z.val hzJ) ▸ ((hFull p.val hp) ▸ h))

private theorem actual_history_data {q : ℕ} (hn : 0<n) {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I)) :
    ∀ {Y : CMfd (n+1)} (T : BlowupTower (model (n+1)) Y),
      IsCanonical (stabilizedMarked I) ((invFamily (Nat.succ_pos n) (q+1)).inv (stabilizedMarked I)) T →
      IsCanonical (X := model (n+1)) (stabilizedMarked I)
        (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q) (stabilizedMarked I)) T ∧
      IsCanonical (normalContact I) ((invFamily (Nat.succ_pos n) q).inv (normalContact I)) (restrict ⊤ T) ∧
      (∀ y∈(geoTransformAlong (stabilizedMarked I) T).cosupp,
        Seq.StepOneValueMasked.stepOneInvM (X := model (n+1)) (invFamily (Nat.succ_pos n) q)
          (stabilizedMarked I) T y=stepMap q (contactValue q I T y)) ∧
      (∀ y∈(geoTransformAlong (stabilizedMarked I) T).cosupp,
        (invFamily (Nat.succ_pos n) (q+1)).inv (X := model (n+1)) (stabilizedMarked I) T y=
          initialEmbedding q (contactValue q I T y))
  | _,.refl,_ => by
    refine ⟨trivial,trivial,?_,?_⟩
    · intro y hy
      exact step_value_of_canons hn hM .refl trivial trivial trivial hy
    · intro y hy
      exact full_value_of_stepCanon hn hM .refl trivial trivial hy
        (step_value_of_canons hn hM .refl trivial trivial trivial hy)
  | _,.step T D π hπ,hCan => by
    obtain ⟨hStepT,hKT,hStepVal,hFullVal⟩ := actual_history_data hn hM T hCan.1
    have ht := upper_test hn hM (.step T D π hπ) hCan
    have hStepMax := upper_step_maximum_of_values q I T hStepVal hFullVal
    have hKMax := contact_maximum_of_value hM T ht.1 hFullVal
    have hStepNext : IsCanonical (X := model (n+1)) (stabilizedMarked I)
        (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q) (stabilizedMarked I))
        (.step T D π hπ) :=
      ⟨hStepT,hCan.2.imp id (fun h => h.trans hStepMax)⟩
    have hKNext : IsCanonical (normalContact I) ((invFamily (Nat.succ_pos n) q).inv (normalContact I))
        (restrict ⊤ (.step T D π hπ)) := by
      refine ⟨hKT,?_⟩
      change (Subtype.val : openPreimage T (⊤ : Opens (ComplexModel (n+1))) → _) ⁻¹' D=∅ ∨
        (Subtype.val : openPreimage T (⊤ : Opens (ComplexModel (n+1))) → _) ⁻¹' D=
          ResolutionDriver.maxLocus ((invFamily (Nat.succ_pos n) q).inv (normalContact I) (restrict ⊤ T))
            (geoTransformAlong (normalContact I) (restrict ⊤ T)).cosupp
      rcases hCan.2 with hEmpty | hMax
      · left
        rw [hEmpty,preimage_empty]
      · right
        exact (congrArg (fun A =>
          (Subtype.val : openPreimage T (⊤ : Opens (ComplexModel (n+1))) → _) ⁻¹' A) hMax).trans hKMax.symm
    refine ⟨hStepNext,hKNext,?_,?_⟩
    · intro y hy
      exact step_value_of_canons hn hM (.step T D π hπ) hCan hStepNext hKNext hy
    · intro y hy
      exact full_value_of_stepCanon hn hM (.step T D π hπ) hCan hStepNext hy
        (step_value_of_canons hn hM (.step T D π hπ) hCan hStepNext hKNext hy)

section Final
variable {q : ℕ} (hn : 0<n) {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I)) {Y : CMfd (n+1)}
    (T : BlowupTower (model (n+1)) Y)
    (hCan : IsCanonical (stabilizedMarked I)
      ((invFamily (Nat.succ_pos n) (q+1)).inv (stabilizedMarked I)) T)
include hn hM hCan

/-- The original upper canonical tower internally produces BOTH genuine lower
canonical histories and the original Step One anchor, at every finite prefix. -/
theorem canonical_history_data :
    IsInvDomain q (normalContact I) ∧
    IsCanonical (X := model (n+1)) (stabilizedMarked I)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q) (stabilizedMarked I)) T ∧
    IsCanonical (normalContact I) ((invFamily (Nat.succ_pos n) q).inv (normalContact I)) (restrict ⊤ T) ∧
    ∀ y∈(geoTransformAlong (stabilizedMarked I) T).cosupp,
      Seq.StepOneValueMasked.stepOneInvM (X := model (n+1)) (invFamily (Nat.succ_pos n) q)
        (stabilizedMarked I) T y=toLex (0,(((invFamily (Nat.succ_pos n) q).inv (normalContact I)
          (restrict ⊤ T) ⟨y,mem_univ _⟩) : WithTop (ValTy q))) := by
  have h := actual_history_data hn hM T hCan
  exact ⟨normalContact_domain hM,h.1,h.2.1,h.2.2.1⟩

/-- Every actual original full-ambient canonical prefix has the literal
original normal-contact historical value as its finite one-depth tail. -/
theorem canonical_history_value {y : Y} (hy : y∈(geoTransformAlong (stabilizedMarked I) T).cosupp) :
    (invFamily (Nat.succ_pos n) (q+1)).inv (X := model (n+1)) (stabilizedMarked I) T y=
      initialEmbedding q ((invFamily (Nat.succ_pos n) q).inv (normalContact I) (restrict ⊤ T) ⟨y,mem_univ _⟩) :=
  (actual_history_data hn hM T hCan).2.2.2 y hy

/-- The entire next maximum is the original contact history's maximum, even
after born boundary and empty years. -/
theorem canonical_history_maximum_locus :
    ResolutionDriver.maxLocus ((invFamily (Nat.succ_pos n) (q+1)).inv (X := model (n+1)) (stabilizedMarked I) T)
      (geoTransformAlong (stabilizedMarked I) T).cosupp =
      (Subtype.val : openPreimage T (⊤ : Opens (ComplexModel (n+1))) → Y) ''
        ResolutionDriver.maxLocus ((invFamily (Nat.succ_pos n) q).inv (normalContact I) (restrict ⊤ T))
          (geoTransformAlong (normalContact I) (restrict ⊤ T)).cosupp := by
  have hd := contact_maximum_of_value hM T (upper_test hn hM T hCan)
    (actual_history_data hn hM T hCan).2.2.2
  rw [hd]
  have hr : Set.range (Subtype.val : openPreimage T (⊤ : Opens (ComplexModel (n+1))) → Y)=univ :=
    Set.range_eq_univ.mpr (fun y => ⟨⟨y,mem_univ _⟩,rfl⟩)
  rw [Set.image_preimage_eq_inter_range,hr,Set.inter_univ]

end Final

end
end TranscendentalNakamaye.Pending.HironakaDisjointCanonicalHistoricalAnchor
