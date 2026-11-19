import Hironaka.Resolution.HironakaG1ProperNormalLowerCanonical

/-! Actual proper-cylinder INITIAL native exponents and original recoding CAN.
The entire nonmonomial ideal is the carrier saturation, not the original
whole ideal. The kept section carrier remains a separate history problem.
Blueprint FIRST: hironaka-g1-proper-normal-initial-regime.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1ProperNormalInitialRegime
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal
  BlowupTowers BlowupTowerTransforms ResolutionInvariantSpec CanonicalCentres
  GermIdealPullbackCalculus RelativePrincipalizationSpan GermIdealOrder InvertibleIdealQuotient
  IdealWeightPowers DivisorExponentAlong MonomialPartAlong DerivativeIdealAlong
  RestrictedIdealExtension RestrictedIdealQuotient RestrictedIdealWeight
  HomogenizedIdealAlong CoefficientIdealRestriction StepOneValue
  CompanionRebase CompanionReductionAlong NonmonomialOrderLocal NonmonomialOrderTail
  HironakaActualOpenZeroSectionDifferentials HironakaActualWeightedNormalPadding
  HironakaActualRelativeNormalGeometry
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalContact
  HironakaG1ProperCarrierNormalLocalClass HironakaG1CoefficientRecodingCanonical
  HironakaG1OriginalUnequalMarkCanonical HironakaG8HomStable HironakaG11InvBMClass
  ResolutionDriver

/-- The SAME genuine vertical field excludes divisibility along a PROPER
cylinder intersection. No ambient/univ replacement is used. -/
theorem normal_power_divExpAlong_eq_zero {n : ℕ} (U : Opens (ComplexModel n))
    (N : Set U) (hNc : IsClosed N) (J : GermIdeal (n+1) (productOpen U))
    (hJ : J.IsCoherent) (r : ℕ) (_hr : 0<r)
    (hpow : ∀x,J.mem x (fun z=>relativeNormalCoordinate U z^r))
    (H : Set U) (hHc : IsClosed H) (x : productOpen U) :
    divExpAlong (n+1) (projection U ⁻¹' N) J (projection U ⁻¹' H) x=0 := by
  have hhol : ∀y g,J.mem y g → HolomorphicAt (n+1) g y :=
    fun _ _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem hJ hg
  by_cases hx : x∈(projection U ⁻¹' N)∩(projection U ⁻¹' H)
  · have hNot : ¬IsDivNearAlong (n+1) (projection U ⁻¹' N) J (projection U ⁻¹' H) 1 x := by
      intro hDiv
      have hVan : (vanishingIdeal (n := n+1) (projection U ⁻¹' (N∩H))).mem x
          (relativeNormalCoordinate U) := by
        refine ⟨Eventually.of_forall (normalCoordinate_mdifferentiable U),?_⟩
        filter_upwards [hDiv] with z hz hzNH
        have hPow := (vanishesToOrderOn_one_iff (n := n+1) (N := projection U ⁻¹' N) (x := z) hzNH.1
          (Eventually.of_forall fun w=>(normalCoordinate_mdifferentiable U).pow r w)).mp
          ((hz hzNH.1 hzNH.2).2 _ (hpow z))
        exact eq_zero_of_pow_eq_zero hPow
      obtain ⟨e,ξ,hOne,hAll⟩ := exists_normal_tangent_field U x
      have hDeriv := ((hAll (N∩H)).preserves _ hVan).2.self_of_nhds hx
      exact one_ne_zero (hOne.symm.trans hDeriv)
    by_contra hne
    exact hNot ((isDivNearAlong_divExpAlong hhol x).mono (Nat.one_le_iff_ne_zero.mpr hne))
  · have hClosed : IsClosed ((projection U ⁻¹' N)∩(projection U ⁻¹' H)) :=
      (hNc.preimage (projection_contMDiff U).continuous).inter
        (hHc.preimage (projection_contMDiff U).continuous)
    have hNone : ¬∃e,¬IsDivNearAlong (n+1) (projection U ⁻¹' N) J
        (projection U ⁻¹' H) (e+1) x := by
      rintro ⟨e,he⟩
      exact he (isDivNearAlong_of_notMem hClosed hx (e+1))
    simp only [divExpAlong,dif_neg hNone]

private theorem proper_normal_power {n : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (x : productOpen U) :
    (properNormalMarked Q).ideal.mem x (fun z=>relativeNormalCoordinate U z^Q.d) := by
  simpa only [properNormalMarked,iterDerivIdealAlong,Nat.add_zero] using
    normal_power_relative_member U Q.N Q.ideal Q.d 0 x

/-- Every ORIGINAL slot, including nonincident/default/empty/repeated slots,
has zero native INITIAL exponent on BOTH true whole records. -/
theorem proper_and_bar_initial_exponents_zero {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) :
    ∀H∈Q.E,∀x : productOpen U,
      divExpAlong (n+1) (properNormalMarked Q).N (properNormalMarked Q).ideal (projection U ⁻¹' H) x=0 ∧
      divExpAlong (n+1) (barMarked (X := CMfd.of (n := n+1) (productOpen U)) (properNormalMarked Q)).N
        (barMarked (X := CMfd.of (n := n+1) (productOpen U)) (properNormalMarked Q)).ideal
        (projection U ⁻¹' H) x=0 := by
  let P:=properNormalMarked Q
  let B:=barMarked (X := CMfd.of (n := n+1) (productOpen U)) P
  have hP:=properNormalMarked_isInvDomain Q hQ
  have hB:=HironakaCoherentTransformExtension.isInvDomain_barMarked
    (X := CMfd.of (n := n+1) (productOpen U)) P hP
  intro H hH x
  have hHc:=hQ.isWellFormed.isSNCDivisor.1 H hH
  exact ⟨normal_power_divExpAlong_eq_zero U Q.N hQ.isWellFormed.isClosedSubmanifold_N.1
      P.ideal hP.isWellFormed.isCoherent Q.d (lt_of_lt_of_le Nat.zero_lt_one hQ.one_le_d)
      (proper_normal_power Q) H hHc x,
    normal_power_divExpAlong_eq_zero U Q.N hQ.isWellFormed.isClosedSubmanifold_N.1
      B.ideal hB.isWellFormed.isCoherent B.d (lt_of_lt_of_le Nat.zero_lt_one hB.one_le_d)
      (normal_power_mem_bar Q hQ) H hHc x⟩

/-- When all boundary exponents vanish, the whole nonmonomial ideal is
exactly the carrier saturation of the given ideal. -/
theorem nonmonomial_eq_restrictOn_of_boundary_zero {n : ℕ} {X : CMfd.{0} n}
    (M : MarkedIdeal n X) (hZero : ∀ H ∈ M.E, ∀ x, divExpAlong n M.N M.ideal H x = 0) :
    nmPart M = restrictOn n M.N M.ideal := by
  have hOne (x : X) : (monomialPartAlong n M.N M.ideal M.E).mem x (fun _ => 1) := by
    refine ⟨holomorphicAt_const 1, fun i _ _ => ?_⟩
    change IsInSpanOnAt (n := n) M.N
      ((idealPow (vanishingIdeal (n := n) (M.E.get i))
        (divExpAlong n M.N M.ideal (M.E.get i) x)).mem x) x (fun _ => 1)
    rw [hZero _ (List.get_mem _ i), idealPow_zero]
    exact IsInSpanAt.restrict (isInSpanAt_self (holomorphicAt_const 1) (holomorphicAt_const 1))
  ext x g
  constructor
  · intro hg
    simpa only [one_mul] using hg.2 (fun _ => 1) (hOne x)
  · intro hg
    exact ⟨hg.1, fun a ha => restrictOn_mul_left ha.1 hg⟩

/-- The whole initial padded nonmonomial ideal is the actual saturation
of the original ideal on its proper cylinder. -/
theorem proper_nonmonomial_eq_restrictOn {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) :
    nmPart (M := CMfd.of (n := n+1) (productOpen U)) (properNormalMarked Q)=
      restrictOn (n+1) (properNormalMarked Q).N (properNormalMarked Q).ideal := by
  apply nonmonomial_eq_restrictOn_of_boundary_zero
  intro D hD x
  obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hD
  exact (proper_and_bar_initial_exponents_zero Q hQ H hH x).1

/-- Native companion at the TRUE original mark: exactly the required
restricted equivalence, preserving the proper carrier and WHOLE boundary. -/
theorem proper_companion_restrictEquiv {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) :
    RestrictEquiv (companionOf (n+1) (M := CMfd.of (n := n+1) (productOpen U))
      (properNormalMarked Q) Q.d) (properNormalMarked Q) := by
  let P:=properNormalMarked Q
  have hI:=(properNormalMarked_isInvDomain Q hQ).isWellFormed.isCoherent
  change RestrictEquiv (companionAlong P.N P.E (nmPart (M := CMfd.of (n := n+1) (productOpen U)) P)
    (monomialPartAlong (n+1) P.N P.ideal P.E) Q.d Q.d) P
  simp only [companionAlong,lt_self_iff_false,if_false]
  refine ⟨rfl,rfl,rfl,?_,?_⟩
  · rw [proper_nonmonomial_eq_restrictOn Q hQ]
    exact restrictLe_restrictOn
  · rw [proper_nonmonomial_eq_restrictOn Q hQ]
    exact restrictLe_self_restrictOn hI

/-- The actual nonmonomial order loci see precisely the ENTIRE restriction
of the whole ideal to the original proper cylinder. -/
theorem proper_ordGe {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) (q : ℕ) :
    ordGe (M := CMfd.of (n := n+1) (productOpen U)) (properNormalMarked Q) q=
      cosupport (n+1) (properNormalMarked Q).N (properNormalMarked Q).ideal q := by
  change cosupport (n+1) (properNormalMarked Q).N (nmPart (M := CMfd.of (n := n+1) (productOpen U)) (properNormalMarked Q)) q=_
  rw [proper_nonmonomial_eq_restrictOn Q hQ]
  exact Subset.antisymm
    (cosupport_subset_of_restrictLe
      (restrictLe_self_restrictOn (properNormalMarked_isInvDomain Q hQ).isWellFormed.isCoherent) q)
    (cosupport_subset_of_restrictLe restrictLe_restrictOn q)

/-- TRUE initial nonmonomial order, on the actual whole cosupport, with
no comparison to the raw/nonmonomial order of unpadded Q. -/
theorem proper_nmOrd_eq_mark {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) {x : productOpen U}
    (hx : x∈(properNormalMarked Q).cosupp) : nmOrd (M := CMfd.of (n := n+1) (productOpen U)) (properNormalMarked Q) x=Q.d := by
  have hP:=properNormalMarked_isInvDomain Q hQ
  apply Nat.le_antisymm
  · apply nmOrd_le_of_notMem
    rw [proper_ordGe Q hQ]
    exact properNormalMarked_maximalOrder Q hQ.isWellFormed.isCoherent x
  · apply (mem_ordGe_iff hP.isWellFormed hP.isNonzeroAlongAt hx.1 Q.d).mp
    rwa [proper_ordGe Q hQ]

/-- The ACTUAL initial order mask is the WHOLE original product open. -/
theorem proper_ordMask_eq_top {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) :
    ordMask (M := CMfd.of (n := n+1) (productOpen U)) (properNormalMarked Q) Q.d=⊤ := by
  have hEmpty : ordGe (M := CMfd.of (n := n+1) (productOpen U)) (properNormalMarked Q) (Q.d+1)=∅ := by
    rw [proper_ordGe Q hQ]
    exact eq_empty_of_forall_notMem (properNormalMarked_maximalOrder Q hQ.isWellFormed.isCoherent)
  apply Opens.ext
  simp only [ordMask,hEmpty,closure_empty,compl_empty,Opens.coe_top]
  rfl

/-- The normalized INITIAL law is internally derived on BOTH true records;
actual D18 tower induction retains every phase change and chronological slot. -/
theorem invFamily_isCanonical_proper_bar_iff {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n+1)} (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y) :
    IsCanonical (properNormalMarked Q) ((invFamily (Nat.succ_pos n) (k+1)).inv (properNormalMarked Q)) T ↔
      IsCanonical (barMarked (X := CMfd.of (n := n+1) (productOpen U)) (properNormalMarked Q))
        ((invFamily (Nat.succ_pos n) (k+1)).inv
          (barMarked (X := CMfd.of (n := n+1) (productOpen U)) (properNormalMarked Q))) T := by
  let P:=properNormalMarked Q
  let B:=barMarked (X := CMfd.of (n := n+1) (productOpen U)) P
  have hP:=properNormalMarked_isInvDomain Q hQ
  have hB:=HironakaCoherentTransformExtension.isInvDomain_barMarked
    (X := CMfd.of (n := n+1) (productOpen U)) P hP
  apply invFamily_isCanonical_iff_of_local (Nat.succ_pos n) P B hP hB
    (bar_local_any_boundary (X := CMfd.of (n := n+1) (productOpen U)) P hP) (SameCarrierDim.of_N_eq rfl) ?_ T
  intro H hH x _hx _hxH
  obtain ⟨H₀,hH₀,rfl⟩ := List.mem_map.mp hH
  obtain ⟨h0,h1⟩ := proper_and_bar_initial_exponents_zero Q hQ H₀ hH₀ x
  rw [h0,h1,mul_zero,mul_zero]

/-- Actual upper P to FULL cylindrical C(barP) CAN, on the SAME ORIGINAL
tower. The kept section-supported R remains distinct and downstream. -/
theorem invFamily_isCanonical_proper_coefficient_bar_iff {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n+1)} (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y) :
    IsCanonical (properNormalMarked Q) ((invFamily (Nat.succ_pos n) (k+1)).inv (properNormalMarked Q)) T ↔
      IsCanonical (coeffMarkedAlong (barMarked (X := CMfd.of (n := n+1) (productOpen U)) (properNormalMarked Q)))
        ((invFamily (Nat.succ_pos n) (k+1)).inv
          (coeffMarkedAlong (barMarked (X := CMfd.of (n := n+1) (productOpen U)) (properNormalMarked Q)))) T :=
  (invFamily_isCanonical_proper_bar_iff Q hQ T).trans
    (invFamily_isCanonical_bar_coefficient_iff (Nat.succ_pos n) (properNormalMarked Q)
      (properNormalMarked_isInvDomain Q hQ) T)

/-- The ENTIRE genuine maximum centre at the SAME original prefix, with
second-side CAN and normalized INITIAL exponents derived internally. -/
theorem invFamily_maxLocus_proper_bar {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n+1)} (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)
    (hCan : IsCanonical (properNormalMarked Q)
      ((invFamily (Nat.succ_pos n) (k+1)).inv (properNormalMarked Q)) T) :
    maxLocus ((invFamily (Nat.succ_pos n) (k+1)).inv (properNormalMarked Q) T)
        (geoTransformAlong (properNormalMarked Q) T).cosupp=
      maxLocus ((invFamily (Nat.succ_pos n) (k+1)).inv
          (barMarked (X := CMfd.of (n := n+1) (productOpen U)) (properNormalMarked Q)) T)
        (geoTransformAlong (barMarked (X := CMfd.of (n := n+1) (productOpen U)) (properNormalMarked Q)) T).cosupp := by
  let P:=properNormalMarked Q
  let B:=barMarked (X := CMfd.of (n := n+1) (productOpen U)) P
  have hP:=properNormalMarked_isInvDomain Q hQ
  have hB:=HironakaCoherentTransformExtension.isInvDomain_barMarked
    (X := CMfd.of (n := n+1) (productOpen U)) P hP
  have hL:=bar_local_any_boundary (X := CMfd.of (n := n+1) (productOpen U)) P hP
  have hDim : SameCarrierDim (X := CMfd.of (n := n+1) (productOpen U)) P B := SameCarrierDim.of_N_eq rfl
  have hExp : ∀H∈P.E,∀x∈P.cosupp,x∈H →
      B.d * divExpAlong (n+1) P.N P.ideal H x=P.d * divExpAlong (n+1) B.N B.ideal H x := by
    intro H hH x _hx _hxH
    obtain ⟨H₀,hH₀,rfl⟩ := List.mem_map.mp hH
    obtain ⟨h0,h1⟩ := proper_and_bar_initial_exponents_zero Q hQ H₀ hH₀ x
    rw [h0,h1,mul_zero,mul_zero]
  have hCanB:=(invFamily_isCanonical_proper_bar_iff Q hQ T).mp hCan
  have hTest:=(invFamily (Nat.succ_pos n) (k+1)).isInvValue.isGeoTestTower_of_isCanonical hP T hCan
  have hCos:=(hL.wEquiv.2 T).2 hTest
  have hCuts:=canonicalTwoPairCuts_invFamily (Nat.succ_pos n) (k+1) P B P B hP hB hP hB
    hL hDim hExp hL hDim hExp rfl rfl trivial trivial trivial trivial T T hCan hCanB hCan hCanB
  rw [←hCos]
  ext x
  constructor
  · rintro ⟨hx,hMax⟩
    refine ⟨hx,fun y hy=>?_⟩
    exact le_of_not_gt (fun h=>not_lt_of_ge (hMax y hy) ((hCuts x hx y hy).mpr h))
  · rintro ⟨hx,hMax⟩
    refine ⟨hx,fun y hy=>?_⟩
    exact le_of_not_gt (fun h=>not_lt_of_ge (hMax y hy) ((hCuts x hx y hy).mp h))

/-- Actual whole cylindrical further-coefficient maximum, retaining every
chronological original/born boundary slot and all empty cases. -/
theorem invFamily_maxLocus_proper_coefficient_bar {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n+1)} (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)
    (hCan : IsCanonical (properNormalMarked Q)
      ((invFamily (Nat.succ_pos n) (k+1)).inv (properNormalMarked Q)) T) :
    maxLocus ((invFamily (Nat.succ_pos n) (k+1)).inv (properNormalMarked Q) T)
        (geoTransformAlong (properNormalMarked Q) T).cosupp=
      maxLocus ((invFamily (Nat.succ_pos n) (k+1)).inv
          (coeffMarkedAlong (barMarked (X := CMfd.of (n := n+1) (productOpen U)) (properNormalMarked Q))) T)
        (geoTransformAlong (coeffMarkedAlong
          (barMarked (X := CMfd.of (n := n+1) (productOpen U)) (properNormalMarked Q))) T).cosupp :=
  (invFamily_maxLocus_proper_bar Q hQ T hCan).trans
    (invFamily_maxLocus_bar_coefficient (Nat.succ_pos n) (properNormalMarked Q)
      (properNormalMarked_isInvDomain Q hQ) T ((invFamily_isCanonical_proper_bar_iff Q hQ T).mp hCan))

end
end Hironaka.HironakaG1ProperNormalInitialRegime
