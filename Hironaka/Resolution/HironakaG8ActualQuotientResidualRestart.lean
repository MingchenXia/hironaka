import Hironaka.Resolution.HironakaG8NativeCommonDenominatorReduction
import Hironaka.Resolution.HironakaActualWeightedNormalPadding
import Hironaka.Resolution.HironakaSharpActualAccumulatedTraceResidual

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8ActualQuotientResidualRestart
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec ResolutionDriver
  NonmonomialOrderLocal GermIdealOrder RelativePrincipalizationSpan InvertibleIdealQuotient
  HironakaActualCoherentWeightedCoefficientMarked HironakaActualWeightedNormalPadding
  HironakaActualWeightedCoefficientCompression HironakaSharpActualAccumulatedTraceResidual
  HironakaSharpActualChronologicalResidualDictionary HironakaG8CommonTowerNonmonomialOrders
  DivisorExponentAlong MonomialPartAlong RestrictedIdealExtension

private theorem principal_mul_generated_family
    {n : ℕ} {X : CMfd.{0} n} {ι : Type}
    (u : X → ℂ) (f : ι → X → ℂ) (hu : ∀ x, HolomorphicAt n u x)
    (hf : ∀ x i, HolomorphicAt n (f i) x) :
    (finiteFunctionIdeal (n := n) (fun _ : Unit => u)).mul (finiteFunctionIdeal f) =
      finiteFunctionIdeal (fun i => u * f i) := by
  ext x g
  constructor
  · intro hg
    refine IsInSpanAt.trans ?_ (mem_mul_iff.mp hg)
    rintro _ ⟨a,b,ha,hb,rfl⟩
    have ha' : IsInSpanAt (n := n) (fun z => z ∈ range (fun _ : Unit => u)) x a := ha
    have hb' : IsInSpanAt (n := n) (fun z => z ∈ range f) x b := hb
    obtain ⟨N,s,c,hs,hc,hEq⟩ := MarkedIdealOperationsAlong.IsInSpanOnAt.mul (W := univ)
      (IsInSpanAt.restrict ha') (IsInSpanAt.restrict hb')
    refine ⟨ha'.1.mul hb'.1,N,s,c,?_,hc,hEq.mono fun _ h => h trivial⟩
    intro i
    obtain ⟨_,_,⟨_,rfl⟩,⟨j,rfl⟩,h⟩ := hs i
    exact ⟨j,h.symm⟩
  · intro hg
    apply mem_mul_iff.mpr
    refine IsInSpanAt.mono ?_ hg
    rintro _ ⟨i,rfl⟩
    exact ⟨u,f i,isInSpanAt_self ⟨(),rfl⟩ (hu x),isInSpanAt_self ⟨i,rfl⟩ (hf x i),rfl⟩

/-- The exact residual at an actual ending chart follows from the source
generators and their true common-denominator quotient equations. The
boundary factor is stripped using its genuine monomial and nonzero data. -/
theorem actual_quotient_family_nmPart
    {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n} {ι : Type} [Fintype ι]
    (P : MarkedIdeal n X) (hP : IsInvDomain n P) (hN : P.N = univ)
    (T : BlowupTower X Y) (hT : IsGeoTestTower P T)
    (F : ι → X → ℂ) (hF : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (F i))
    (hGen : P.ideal = finiteFunctionIdeal F)
    (q : ι → Y → ℂ) (hq : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (q i))
    (u : Y → ℂ) (hu : MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) u)
    (hQuot : ∀ i y, F i (T.proj y) = u y * q i y) :
    let A := geoTransformAlong P T
    let M := finiteFunctionIdeal (n := n) (fun _ : Unit => u)
    let R := finiteFunctionIdeal (n := n) q
    (∀ y ∈ (univ : Set Y), IsNonzeroAlongAt univ M y) →
    (∀ y ∈ (univ : Set Y), IsNonzeroAlongAt univ R y) →
    IsMonomialAlong n univ M A.E →
    (∀ y ∈ (univ : Set Y), ∀ i : Fin A.E.length, y ∈ A.E.get i →
      ∃ f, R.mem y f ∧ ¬ IsInSpanOnAt (n := n) univ ((vanishingIdeal (n := n) (A.E.get i)).mem y) y f) →
    nmPart A = R := by
  intro A M R hNZM hNZR hMono hNo
  have hAD := InvDomainTowerAlong.isInvDomain_geoTransformAlong hP T hT
  have hAN : A.N = univ := (pullback_eq_mul_geoTransformAlong (𝔪 := P)
    hN hP.isWellFormed.isCoherent T hT).1
  have hAW := hAD.isWellFormed
  have hU : IsClosedSubmanifold n (univ : Set Y) := hAN ▸ hAW.isClosedSubmanifold_N
  have hTr : NormalCrossings.IsTransverse n univ A.E := hAN ▸ hAW.isTransverse
  have hM : M.IsCoherent := isCoherent_finiteFunctionIdeal _ (fun _ => hu)
  have hR : R.IsCoherent := isCoherent_finiteFunctionIdeal _ hq
  have hTotal : GermIdeal.pullback (m := n) T.proj P.ideal = M.mul R := by
    rw [hGen,finiteFunctionIdeal_pullback F hF T.proj T.contMDiff_proj]
    have he : (fun (i : ι) => F i ∘ T.proj) = fun i => u * q i := by
      funext i y
      exact hQuot i y
    rw [he,← principal_mul_generated_family u q
      (fun _ => Filter.Eventually.of_forall fun y => hu y)
      (fun _ i => Filter.Eventually.of_forall fun y => hq i y)]
  have hs := controlled_tower_nonmonomial_eq_initial_total_pullback hn P
    hP.isWellFormed hN hP.isNonzeroAlongAt T hT
  change nmPart A = nonmonomialPartAlong n A.N (GermIdeal.pullback (m := n) T.proj P.ideal) A.E at hs
  rw [hAN,hTotal] at hs
  have hRemove := actual_normalized_monomial_product_nonmonomial_eq hn hU hAW.isSNCDivisor
    hTr hM hR hNZM hNZR hMono
  rw [BlowupTowerTransforms.restrictOn_univ (IdealWeightPowers.isCoherent_mul hM hR)] at hRemove
  have hRNo := nonmonomialPartAlong_eq_restrictOn_of_no_member_factor hU hAW.isSNCDivisor hTr hR hNo
  rw [BlowupTowerTransforms.restrictOn_univ hR] at hRNo
  exact hs.trans (hRemove.trans hRNo)

/-- Original normalized degree weights turn true weighted quotient equations
into a single monomial factor at every common divisor mark. -/
theorem actual_weighted_quotient_family_nmPart
    {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n} {ι : Type} [Fintype ι]
    (P : MarkedIdeal n X) (hp : IsInvDomain n P) (hN : P.N = univ)
    (T : BlowupTower X Y) (hT : IsGeoTestTower P T)
    (w : ι → ℕ) (d : ℕ) (hd : ∀ i, w i ∣ d)
    (F : ι → X → ℂ) (hF : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (F i))
    (hGen : P.ideal = finiteFunctionIdeal (fun i => F i ^ (d/w i)))
    (q : ι → Y → ℂ) (hq : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (q i))
    (u : Y → ℂ) (hu : MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) u)
    (hQuot : ∀ i y, F i (T.proj y) = (u y)^(w i) * q i y) :
    let A := geoTransformAlong P T
    let M := finiteFunctionIdeal (n := n) (fun _ : Unit => u^d)
    let R := finiteFunctionIdeal (n := n) (fun i => q i ^ (d/w i))
    (∀ y ∈ (univ : Set Y), IsNonzeroAlongAt univ M y) →
    (∀ y ∈ (univ : Set Y), IsNonzeroAlongAt univ R y) →
    IsMonomialAlong n univ M A.E →
    (∀ y ∈ (univ : Set Y), ∀ i : Fin A.E.length, y ∈ A.E.get i →
      ∃ f, R.mem y f ∧ ¬ IsInSpanOnAt (n := n) univ ((vanishingIdeal (n := n) (A.E.get i)).mem y) y f) →
    nmPart A = R := by
  intro A M R hM hR hMono hNo
  apply actual_quotient_family_nmPart hn P hp hN T hT (fun i => F i ^ (d/w i)) (fun i => (hF i).pow _)
    hGen (fun i => q i ^ (d/w i)) (fun i => (hq i).pow _) (u^d) (hu.pow _)
    _ hM hR hMono hNo
  intro i y
  simp only [Pi.pow_apply]
  rw [hQuot, mul_pow, ← pow_mul, Nat.mul_div_cancel' (hd i)]


/-- A quotient function which remains nonzero arbitrarily near a touching
member gives an explicit nonfactor witness for every natural power. -/
theorem quotient_power_not_boundary_factor
    {n : ℕ} {X : CMfd.{0} n} (P : MarkedIdeal n X)
    (hp : P.IsWellFormed) (hN : P.N = univ)
    (x : X) (i : Fin P.E.length) (f : X → ℂ)
    (hf : HolomorphicAt n f x) (e : ℕ)
    (hNear : ∃ᶠ z in 𝓝 x, z ∈ P.E.get i ∧ f z ≠ 0) :
    ¬ IsInSpanOnAt (n := n) univ ((vanishingIdeal (n := n) (P.E.get i)).mem x) x (f^e) := by
  intro h
  have hx : x ∈ P.N := hN ▸ mem_univ x
  have h' : IsInSpanOnAt (n := n) P.N ((vanishingIdeal (n := n) (P.E.get i)).mem x) x (f^e) := by
    rw [hN]
    exact h
  have hv := (MemberTraceIdealAlong.isInSpanOnAt_vanishingIdeal_iff_mem_of_isWellFormed hp hx i
    (CompanionReduction.holomorphicAt_pow_of hf e)).mp h'
  apply hNear
  filter_upwards [hv.2] with z hz
  rintro ⟨hzE,hzNE⟩
  have hzN : z ∈ P.N := hN ▸ mem_univ z
  exact (pow_ne_zero e hzNE) (hz ⟨hzN,hzE⟩)

/-- A genuine weighted restart on the terminal chart of an actual low
prefix is canonical for the advancing low record. The source generation
and controlled quotient equations supply the exact shared residual. -/
theorem native_chart_restart_canonical_of_weighted_quotients
    {n : ℕ} {Z X Y : CMfd.{0} (n+1)} {I ι : Type} [Fintype ι]
    {W D : Set X} {E : List (Set X)} {H : ℕ → ℕ}
    (A : HironakaG8NativeRelativeClearing.NativeWindows X I W E H D)
    (S : BlowupTower X Y)
    (hSync : HironakaG8NativeSimultaneousCentre.NativeSimultaneousStages
      (CanonicalCentres.canonicalInvariant (n+1)) A.openSet A.powered S)
    (i : I) (P : MarkedIdeal (n+1) Z) (hp : IsInvDomain (n+1) P) (hPN : P.N = univ)
    (T : BlowupTower Z (CMfd.of (n := n+1) (A.openSet i))) (hT : IsGeoTestTower P T)
    (w : ι → ℕ) (hw : ∀ j, 0 < w j)
    (d : ℕ) (hd : 1 < d) (hPd : P.d ≤ d)
    (hWeights : ∀ j, w j ∣ d) (hDvd : d ∣ weightedCommonMark w)
    (F : ι → Z → ℂ) (hF : ∀ j, MDifferentiable 𝓘(ℂ, ComplexModel (n+1)) 𝓘(ℂ, ℂ) (F j))
    (hGen : P.ideal = finiteFunctionIdeal (fun j => F j ^ (d/w j)))
    (q : ι → A.openSet i → ℂ) (hq : ∀ j, MDifferentiable 𝓘(ℂ, ComplexModel (n+1)) 𝓘(ℂ, ℂ) (q j))
    (u : A.openSet i → ℂ) (hu : MDifferentiable 𝓘(ℂ, ComplexModel (n+1)) 𝓘(ℂ, ℂ) u)
    (hQuot : ∀ j y, F j (T.proj y) = (u y)^(w j) * q j y) :
    let L := geoTransformAlong P T
    let M := finiteFunctionIdeal (n := n+1) (fun _ : Unit => u^d)
    let R : MarkedIdeal (n+1) (CMfd.of (n := n+1) (A.openSet i)) :=
      ⟨univ,L.E,finiteFunctionIdeal (fun j => q j ^ (d/w j)),d⟩
    IsInvDomain (n+1) R →
    (∀ y : A.openSet i, ∃ᶠ z in 𝓝 y, u z ≠ 0) →
    IsMonomialAlong (n+1) univ M L.E →
    (∀ y : A.openSet i, ∀ j : Fin L.E.length, y ∈ L.E.get j →
      ∃ v, ∃ᶠ z in 𝓝 y, z ∈ L.E.get j ∧ q v z ≠ 0) →
    A.record i = ⟨univ,L.E,weightedFunctionIdeal w q,weightedCommonMark w⟩ →
    IsCanonical L ((CanonicalCentres.canonicalInvariant (n+1)).inv L)
      (BlowupTowerTransforms.restrict (A.openSet i) S) := by
  intro L M R hr hDen hMono hNo hRaw
  let B := CMfd.of (n := n+1) (A.openSet i)
  have hL := InvDomainTowerAlong.isInvDomain_geoTransformAlong hp T hT
  have hLN : L.N = univ := (pullback_eq_mul_geoTransformAlong (𝔪 := P)
    hPN hp.isWellFormed.isCoherent T hT).1
  have hLd : L.d ≤ d := (d_geoTransformAlong P T).trans_le hPd
  have hM (y : B) (_ : y ∈ (univ : Set B)) : IsNonzeroAlongAt (n := n+1) univ M y := by
    refine ⟨u^d, isInSpanAt_self (S := fun s => s ∈ range (fun _ : Unit => u^d)) ⟨(),rfl⟩ (Filter.Eventually.of_forall fun z => (hu.pow d) z), ?_⟩
    exact (hDen y).mono fun z hz => ⟨mem_univ z,pow_ne_zero d hz⟩
  have hResid : nmPart L = R.ideal := by
    apply actual_weighted_quotient_family_nmPart (X := Z) (Y := B) (Nat.succ_pos n)
      P hp hPN T hT w d hWeights F hF hGen q hq u hu hQuot hM hr.isNonzeroAlongAt hMono
    intro y _ j hy
    obtain ⟨v,h⟩ := hNo y j hy
    have hv : HolomorphicAt (n+1) (q v) y := Filter.Eventually.of_forall fun z => hq v z
    refine ⟨q v ^ (d/w v),isInSpanAt_self ⟨v,rfl⟩ (CompanionReduction.holomorphicAt_pow_of hv _), ?_⟩
    exact quotient_power_not_boundary_factor L hL.isWellFormed hLN y j (q v) hv _ h
  exact HironakaG8NativeCommonDenominatorReduction.native_common_denominator_chart_low_canonical
    A S hSync i L hL hLN w hw d hd hLd hWeights hDvd q hq hr hRaw hResid

/-- For a single occupied cut the actual exceptional geometry supplies
the monomial denominator package, once the chart equation generates
the genuine exceptional ideal. -/
theorem actual_single_cut_weighted_quotient_nmPart
    {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n} {ι : Type} [Fintype ι]
    (P : MarkedIdeal n X) (hp : IsInvDomain n P) (hN : P.N = univ)
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π) (hC : P.IsAdmissibleCentre C)
    (w : ι → ℕ) (d : ℕ) (hd : ∀ i, w i ∣ d)
    (F : ι → X → ℂ) (hF : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (F i))
    (hGen : P.ideal = finiteFunctionIdeal (fun i => F i ^ (d/w i)))
    (q : ι → Y → ℂ) (hq : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (q i))
    (u : Y → ℂ) (hu : MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) u)
    (huIdeal : finiteFunctionIdeal (n := n) (fun _ : Unit => u) =
      (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal)
    (hQuot : ∀ i y, F i (π y) = (u y)^(w i) * q i y) :
    let A := P.geoTransform C π
    let R := finiteFunctionIdeal (n := n) (fun i => q i ^ (d/w i))
    (∀ y ∈ (univ : Set Y), IsNonzeroAlongAt univ R y) →
    (∀ y : Y, ∀ j : Fin A.E.length, y ∈ A.E.get j →
      ∃ v, ∃ᶠ z in 𝓝 y, z ∈ A.E.get j ∧ q v z ≠ 0) →
    nmPart A = R := by
  intro A R hNZR hfactors
  let T : BlowupTower X Y := .step .refl C π hπ
  have hT : IsGeoTestTower P T := ⟨trivial,hC⟩
  have hAW := (InvDomainTowerAlong.isInvDomain_geoTransformAlong hp T hT).isWellFormed
  have hAN : A.N = univ := geoTransform_N_eq_univ hN hπ
  have huGen (x : Y) (a : Y → ℂ) :
      ((BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal).mem x a ↔
        IsInSpanAt (n := n) (· = u) x a := by
    rw [← huIdeal]
    change IsInSpanAt (n := n) (fun c => c ∈ range (fun _ : Unit => u)) x a ↔ _
    exact ⟨IsInSpanAt.mono (fun _ ⟨_,hc⟩ => hc.symm),
      IsInSpanAt.mono (fun _ hc => ⟨(),hc.symm⟩)⟩
  have hPow : IdealWeightPowers.idealPow (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal d =
      finiteFunctionIdeal (n := n) (fun _ : Unit => u^d) := by
    ext x a
    change _ ↔ IsInSpanAt (n := n) (fun c => c ∈ range (fun _ : Unit => u^d)) x a
    have hU : HolomorphicAt n u x := Filter.Eventually.of_forall fun z => hu z
    rw [HironakaSharpActualProductNewExceptionalFactor.idealPow_principal_mem_iff hU (huGen x)]
    exact ⟨IsInSpanAt.mono (fun _ hc => ⟨(),hc.symm⟩),
      IsInSpanAt.mono (fun _ ⟨_,hc⟩ => hc.symm)⟩
  obtain ⟨_,hNonzero,hMono⟩ := HironakaSharpActualMonomialDivisionResidual.actual_new_exceptional_power_monomial
    hn hp.isWellFormed.isClosedSubmanifold_N hp.isWellFormed.isSNCDivisor hp.isWellFormed.isTransverse
    hπ hC.subset_N hC.2.2 d
  change (∀ y ∈ A.N, IsNonzeroAlongAt A.N
    (IdealWeightPowers.idealPow (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal d) y) at hNonzero
  change IsMonomialAlong n A.N
    (IdealWeightPowers.idealPow (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal d) A.E at hMono
  rw [hAN,hPow] at hNonzero hMono
  apply actual_weighted_quotient_family_nmPart hn P hp hN T hT w d hd F hF hGen q hq u hu
    hQuot hNonzero hNZR hMono
  intro y _ j hy
  obtain ⟨v,hv⟩ := hfactors y j hy
  have hHol : HolomorphicAt n (q v) y := Filter.Eventually.of_forall fun z => hq v z
  exact ⟨q v ^ (d/w v),isInSpanAt_self ⟨v,rfl⟩ (CompanionReduction.holomorphicAt_pow_of hHol _),
    quotient_power_not_boundary_factor A hAW hAN y j (q v) hHol _ hv⟩

end
end Hironaka.HironakaG8ActualQuotientResidualRestart
