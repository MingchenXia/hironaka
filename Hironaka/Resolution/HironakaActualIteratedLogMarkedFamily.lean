import Hironaka.Resolution.HironakaActualProjectionNativeLogIdeal
import Hironaka.Resolution.HironakaSmoothSubmersionCoefficientIdeals
import Hironaka.Resolution.HironakaActualSingularSubmersionPullback
import Hironaka.Resolution.HironakaAnalyticBaseChangeQuotientModel
/-! Literal geometric BM iterated log and LCM marked families on proper carriers.
The existing actual540 operation is reused. Abstract Der_N identification is separate.
BP FIRST: hironaka-actual-iterated-log-marked-family.tex. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualIteratedLogMarkedFamily
noncomputable section
open scoped ProductComplexManifold
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan RestrictedIdealExtension CoefficientIdeal IdealWeightPowers
  DerivativeIdealAlong HomogenizedGlueing BlowupTowers MarkedIdeals HironakaActualIntrinsicLogDerivativeFrame
  HironakaActualIntrinsicLogQuotientDictionary HironakaActualProjectionTestRecord
  HironakaActualProjectionCarrierQuotientDictionary HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaReducedComplexAnalyticSpaces HironakaActualWholeStalkHolomorphicPullback
  HironakaRelativeNormalIdeal HolGerm NormalCrossings GermIdealPullbackCalculus
  HironakaActualAnalyticSubspaceOpenRestriction HironakaActualOpenIntrinsicHS
  HironakaActualProjectionNativeLogIdeal HironakaSmoothSubmersionContactParameterCharts
  HironakaSmoothSubmersionContactParameterCoefficientIdeals HironakaActualExceptionalLogDerivativeIdeal
  HironakaNonreducedQuotientNeighborhoodLifting HironakaActualAnalyticSubspaceResidue
  HironakaActualIntrinsicCarrierDerivationTransport HironakaHolomorphicJetChartInvariance
  HironakaHolomorphicJetRankLoci HironakaHolomorphicJetMonomialSpan HolomorphicGermCoordinateDerivation

def rawIter {n : ℕ} {X : CMfd.{0} n} (N : Set X) (E : List (Set X))
    (A : GermIdeal n X) (r : ℕ) : GermIdeal n X := ((logDerivIdealAlong N E)^[r]) A

def carrierIter {n : ℕ} {X : CMfd.{0} n} (N : Set X) (E : List (Set X))
    (A : GermIdeal n X) (r : ℕ) : GermIdeal n X := restrictOn n N (rawIter N E A r)

def rawLogMarked {n : ℕ} {X : CMfd.{0} n} (M : MarkedIdeal n X) (j : ℕ) : MarkedIdeal n X :=
  { N := M.N, E := M.E, ideal := rawIter M.N M.E M.ideal j, d := M.d-j }

def carrierLogMarked {n : ℕ} {X : CMfd.{0} n} (M : MarkedIdeal n X) (j : ℕ) : MarkedIdeal n X :=
  { N := M.N, E := M.E, ideal := carrierIter M.N M.E M.ideal j, d := M.d-j }

def bmCommonMark {n : ℕ} {X : CMfd.{0} n} (Q : ℕ → MarkedIdeal n X) (m : ℕ) : ℕ :=
  (Finset.range m).lcm (fun i => (Q i).d)

def bmFiniteSum {n : ℕ} {X : CMfd.{0} n} (Q : ℕ → MarkedIdeal n X) (m : ℕ) : MarkedIdeal n X :=
  { N := (Q 0).N, E := (Q 0).E,
    ideal := finSumIdeal (fun i => idealPow (Q i).ideal (bmCommonMark Q m / (Q i).d)) m,
    d := bmCommonMark Q m }

def bmCarrierSum {n : ℕ} {X : CMfd.{0} n} (Q : ℕ → MarkedIdeal n X) (m : ℕ) : MarkedIdeal n X :=
  { N := (Q 0).N, E := (Q 0).E,
    ideal := restrictOn n (Q 0).N (bmFiniteSum Q m).ideal, d := bmCommonMark Q m }

theorem rawIter_coherent {n : ℕ} {X : CMfd.{0} n} {N : Set X} {E : List (Set X)}
    (A : GermIdeal n X) (hA : A.IsCoherent) (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n E) (hTr : IsTransverse n N E) (r : ℕ) :
    (rawIter N E A r).IsCoherent := by
  induction r with
  | zero => exact hA
  | succ r ih =>
    change (((logDerivIdealAlong N E)^[r+1]) A).IsCoherent
    rw [Function.iterate_succ_apply']
    exact isCoherent_logDerivIdealAlong ih hN hE hTr

theorem carrier_completion_eq_self {n : ℕ} {X : CMfd.{0} n} {N : Set X}
    (A : GermIdeal n X) (hA : A.IsCoherent) (_hN : IsClosedSubmanifold n N)
    (hIN : (vanishingIdeal (n:=n) N).Le A) : restrictOn n N A=A := by
  rw [restrictOn_eq_sum_vanishingIdeal hA]
  apply GermIdeal.ext
  funext p g
  apply propext
  constructor
  · intro hg
    change IsInSpanAt (fun s => A.mem p s ∨ (vanishingIdeal (n:=n) N).mem p s) p g at hg
    exact HomogenizedIdeal.mem_of_isInSpanAt hA
      (IsInSpanAt.mono (fun s hs => hs.elim id (hIN p s)) hg)
  · intro hg
    exact le_sumIdeal_left hA p g hg

theorem carrier_completion_idempotent {n : ℕ} {X : CMfd.{0} n} {N : Set X}
    (A : GermIdeal n X) (hA : A.IsCoherent) (hN : IsClosedSubmanifold n N) :
    restrictOn n N (restrictOn n N A)=restrictOn n N A :=
  carrier_completion_eq_self _ (isCoherent_restrictOn_of_isClosedSubmanifold hA hN) hN
    vanishingIdeal_le_restrictOn

theorem carrier_completion_native {n : ℕ} {X : CMfd.{0} n} {N : Set X}
    (A : GermIdeal n X) (hA : A.IsCoherent) (hN : IsClosedSubmanifold n N) (p : X) :
    actualWholeSheafStalkIdeal (restrictOn n N A) p=
      actualWholeSheafStalkIdeal A p ⊔ actualWholeSheafStalkIdeal (vanishingIdeal (n:=n) N) p := by
  rw [restrictOn_eq_sum_vanishingIdeal hA]
  exact HironakaAnalyticBaseChangeQuotientModel.actualWholeSheafStalkIdeal_sum A _ hA
    (VanishingIdealCoherent.isCoherent_vanishingIdeal hN) p

private theorem carrier_le_log {n : ℕ} {X : CMfd.{0} n} (N : Set X)
    (E : List (Set X)) (B : GermIdeal n X) :
    (vanishingIdeal (n:=n) N).Le (logDerivIdealAlong N E B) := by
  intro p g hg
  change IsInSpanAt (fun s => B.mem p s ∨ (vanishingIdeal (n:=n) N).mem p s ∨
    ∃ e ξ f, IsLogTangentField N E e ξ p ∧ B.mem p f ∧ s=fieldDeriv e ξ f) p g
  exact isInSpanAt_of_eq_mul (Or.inr (Or.inl hg)) hg.1
    (holomorphicAt_const 1) (Eventually.of_forall fun _ => (one_mul _).symm)

theorem carrierIter_succ_eq_raw {n : ℕ} {X : CMfd.{0} n} {N : Set X} {E : List (Set X)}
    (A : GermIdeal n X) (hA : A.IsCoherent) (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n E) (hTr : IsTransverse n N E) (r : ℕ) :
    carrierIter N E A (r+1)=rawIter N E A (r+1) := by
  apply carrier_completion_eq_self _ (rawIter_coherent A hA hN hE hTr _) hN
  change (vanishingIdeal (n:=n) N).Le (((logDerivIdealAlong N E)^[r+1]) A)
  rw [Function.iterate_succ_apply']
  exact carrier_le_log N E _

theorem logMarked_metadata {n : ℕ} {X : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (j : ℕ) :
    (rawLogMarked M j).IsWellFormed ∧ (carrierLogMarked M j).IsWellFormed ∧
    (rawLogMarked M j).N=M.N ∧ (carrierLogMarked M j).N=M.N ∧
    (rawLogMarked M j).E=M.E ∧ (carrierLogMarked M j).E=M.E ∧
    (rawLogMarked M j).d=M.d-j ∧ (carrierLogMarked M j).d=M.d-j := by
  have hc := rawIter_coherent M.ideal hM.isCoherent hM.isClosedSubmanifold_N
    hM.isSNCDivisor hM.isTransverse j
  exact ⟨⟨hM.isClosedSubmanifold_N,hc,hM.isSNCDivisor,hM.isTransverse⟩,
    ⟨hM.isClosedSubmanifold_N,isCoherent_restrictOn_of_isClosedSubmanifold hc
      hM.isClosedSubmanifold_N,hM.isSNCDivisor,hM.isTransverse⟩,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem logMarked_zero {n : ℕ} {X : CMfd.{0} n} (M : MarkedIdeal n X) : rawLogMarked M 0=M := by
  cases M
  rfl

theorem logMarked_positive {n : ℕ} {X : CMfd.{0} n}
    (M : MarkedIdeal n X) {j : ℕ} (hj : j<M.d) : 0<(rawLogMarked M j).d := by
  change 0<M.d-j
  omega

theorem bmCommonMark_spec {n : ℕ} {X : CMfd.{0} n} (Q : ℕ → MarkedIdeal n X) (m : ℕ)
    (hPos : ∀ i<m, 0<(Q i).d) :
    0<bmCommonMark Q m ∧ ∀ i<m,
      (Q i).d ∣ bmCommonMark Q m ∧ 0<bmCommonMark Q m/(Q i).d ∧
      (Q i).d*(bmCommonMark Q m/(Q i).d)=bmCommonMark Q m := by
  have hl : 0<bmCommonMark Q m := Nat.pos_of_ne_zero
    (Finset.lcm_ne_zero_iff.mpr fun i hi => Nat.ne_of_gt (hPos i (Finset.mem_range.mp hi)))
  refine ⟨hl,?_⟩
  intro i hi
  have hd : (Q i).d ∣ bmCommonMark Q m := Finset.dvd_lcm (Finset.mem_range.mpr hi)
  refine ⟨hd,?_,Nat.mul_div_cancel' hd⟩
  exact Nat.div_pos (Nat.le_of_dvd hl hd) (hPos i hi)

theorem bmFiniteSum_coherent {n : ℕ} {X : CMfd.{0} n} (Q : ℕ → MarkedIdeal n X) (m : ℕ)
    (hCoh : ∀ i<m, (Q i).ideal.IsCoherent) : (bmFiniteSum Q m).ideal.IsCoherent :=
  isCoherent_finSumIdeal_of_lt fun i hi => isCoherent_idealPow (hCoh i hi) _

theorem bmCarrierSum_wellFormed {n : ℕ} {X : CMfd.{0} n} (Q : ℕ → MarkedIdeal n X) (m : ℕ)
    (hCoh : ∀ i<m, (Q i).ideal.IsCoherent)
    (hN : IsClosedSubmanifold n (Q 0).N) (hE : IsSNCDivisor n (Q 0).E)
    (hTr : IsTransverse n (Q 0).N (Q 0).E) : (bmCarrierSum Q m).IsWellFormed :=
  ⟨hN,isCoherent_restrictOn_of_isClosedSubmanifold (bmFiniteSum_coherent Q m hCoh) hN,hE,hTr⟩

theorem productMsum_metadata {n : ℕ} {X : CMfd.{0} n} (Q : ℕ → MarkedIdeal n X) (m : ℕ)
    (hCoh : ∀ i<m, (Q i).ideal.IsCoherent) (hPos : ∀ i<m, 0<(Q i).d)
    (hN : IsClosedSubmanifold n (Q 0).N) (hE : IsSNCDivisor n (Q 0).E)
    (hTr : IsTransverse n (Q 0).N (Q 0).E)
    (_hSameN : ∀ i<m, (Q i).N=(Q 0).N) (_hSameE : ∀ i<m, (Q i).E=(Q 0).E) :
    (msum Q m).IsWellFormed ∧ (msum Q m).N=(Q 0).N ∧ (msum Q m).E=(Q 0).E ∧
    (msum Q m).d=(Finset.range m).prod (fun i => (Q i).d) ∧
    0<(msum Q m).d ∧
    (msum Q m).ideal=finSumIdeal
      (fun i => idealPow (Q i).ideal (sumExp (fun j => (Q j).d) m i)) m ∧
    (∀ i<m, 0<sumExp (fun j => (Q j).d) m i ∧
      (Q i).d*sumExp (fun j => (Q j).d) m i=(msum Q m).d) ∧
    (m=0 → (msum Q m).d=1 ∧ (msum Q m).N=(Q 0).N ∧ (msum Q m).E=(Q 0).E) := by
  refine ⟨⟨hN,isCoherent_finSumIdeal_of_lt (fun i hi => isCoherent_idealPow (hCoh i hi) _),hE,hTr⟩,
    rfl,rfl,rfl,Finset.prod_pos (fun i hi => hPos i (Finset.mem_range.mp hi)),rfl,?_,?_⟩
  · intro i hi
    exact ⟨one_le_sumExp (fun j hj => hPos j hj) i,mul_sumExp (fun j => (Q j).d) hi⟩
  · rintro rfl
    exact ⟨rfl,rfl,rfl⟩

def liftMarked {n : ℕ} {X : CMfd.{0} n} (M : MarkedIdeal n X) :
    MarkedIdeal (n+1) (projectionAmbient X) :=
  { N := (Prod.fst : projectionAmbient X→X) ⁻¹' M.N,
    E := M.E.map ((Prod.fst : projectionAmbient X→X) ⁻¹' ·) ++ [horizontal X],
    ideal := GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X) M.ideal, d := M.d }

theorem projection_carrier_completion_eq {n : ℕ} {X : CMfd.{0} n} {N : Set X}
    (A : GermIdeal n X) (hA : A.IsCoherent) (hN : IsClosedSubmanifold n N) :
    GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X) (restrictOn n N A)=
      restrictOn (n+1) ((Prod.fst : projectionAmbient X→X) ⁻¹' N)
        (GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X) A) :=
  HironakaSmoothSubmersionRelativeRestriction.pullback_restrictOn_submersion
    (HironakaAuxiliaryGraphGeometry.isSubmersion_fst (n:=n) (m:=1) (X:=X) (Y:=ComplexModel 1)) hN hA

theorem projection_marked_family_eq {n : ℕ} {X : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (j : ℕ) :
    liftMarked (rawLogMarked M j)=rawLogMarked (liftMarked M) j ∧
    liftMarked (carrierLogMarked M j)=carrierLogMarked (liftMarked M) j := by
  have hr : GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X)
      (rawIter M.N M.E M.ideal j)=
      rawIter (liftMarked M).N (liftMarked M).E (liftMarked M).ideal j :=
    projection_native_logIdeal_iterate_eq M.ideal hM.isCoherent hM.isClosedSubmanifold_N
      hM.isSNCDivisor hM.isTransverse j
  constructor
  · exact MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl hr rfl
  · refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of
      (𝔪:=liftMarked (carrierLogMarked M j)) (𝔫:=carrierLogMarked (liftMarked M) j) rfl rfl ?_ rfl
    change GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X)
      (restrictOn n M.N (rawIter M.N M.E M.ideal j))=_
    rw [projection_carrier_completion_eq _
      (rawIter_coherent M.ideal hM.isCoherent hM.isClosedSubmanifold_N hM.isSNCDivisor hM.isTransverse j)
      hM.isClosedSubmanifold_N,hr]
    rfl

theorem projection_bmFiniteSum_eq {n : ℕ} {X : CMfd.{0} n}
    (Q : ℕ → MarkedIdeal n X) (m : ℕ) (hQ : ∀ i<m, (Q i).ideal.IsCoherent)
    (hN : IsClosedSubmanifold n (Q 0).N) :
    liftMarked (bmFiniteSum Q m)=bmFiniteSum (fun i => liftMarked (Q i)) m ∧
    liftMarked (bmCarrierSum Q m)=bmCarrierSum (fun i => liftMarked (Q i)) m := by
  have hh : (liftMarked (bmFiniteSum Q m)).ideal=
      (bmFiniteSum (fun i => liftMarked (Q i)) m).ideal := by
    change GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X)
      (finSumIdeal (fun i => idealPow (Q i).ideal (bmCommonMark Q m / (Q i).d)) m)=_
    rw [HironakaSmoothSubmersionCoefficientIdeals.pullback_finSumIdeal
      ProductComplexManifold.contMDiff_fst _ _ (fun i hi => isCoherent_idealPow (hQ i hi) _)]
    apply finSumIdeal_congr
    intro i hi
    exact HironakaSmoothSubmersionCoefficientIdeals.pullback_idealPow
      ProductComplexManifold.contMDiff_fst (hQ i hi) _
  constructor
  · exact MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl hh rfl
  · refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of
      (𝔪:=liftMarked (bmCarrierSum Q m)) (𝔫:=bmCarrierSum (fun i => liftMarked (Q i)) m) rfl rfl ?_ rfl
    change GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X)
      (restrictOn n (Q 0).N (bmFiniteSum Q m).ideal)=_
    rw [projection_carrier_completion_eq _ (bmFiniteSum_coherent Q m hQ) hN]
    exact congrArg (restrictOn (n+1) ((Prod.fst : projectionAmbient X→X) ⁻¹' (Q 0).N)) hh

theorem projection_productMsum_eq {n : ℕ} {X : CMfd.{0} n}
    (Q : ℕ → MarkedIdeal n X) (m : ℕ) (hQ : ∀ i<m, (Q i).ideal.IsCoherent)
    (hN : IsClosedSubmanifold n (Q 0).N) :
    liftMarked (msum Q m)=msum (fun i => liftMarked (Q i)) m ∧
    GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X)
      (restrictOn n (Q 0).N (msum Q m).ideal)=
    restrictOn (n+1) ((Prod.fst : projectionAmbient X→X) ⁻¹' (Q 0).N)
      (msum (fun i => liftMarked (Q i)) m).ideal := by
  have hc : (msum Q m).ideal.IsCoherent :=
    isCoherent_finSumIdeal_of_lt fun i hi => isCoherent_idealPow (hQ i hi) _
  have hh : (liftMarked (msum Q m)).ideal=(msum (fun i => liftMarked (Q i)) m).ideal := by
    change GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X)
      (finSumIdeal (fun i => idealPow (Q i).ideal (sumExp (fun j => (Q j).d) m i)) m)=_
    rw [HironakaSmoothSubmersionCoefficientIdeals.pullback_finSumIdeal
      ProductComplexManifold.contMDiff_fst _ _ (fun i hi => isCoherent_idealPow (hQ i hi) _)]
    apply finSumIdeal_congr
    intro i hi
    exact HironakaSmoothSubmersionCoefficientIdeals.pullback_idealPow
      ProductComplexManifold.contMDiff_fst (hQ i hi) _
  refine ⟨MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl hh rfl,?_⟩
  rw [projection_carrier_completion_eq _ hc hN]
  exact congrArg (restrictOn (n+1) ((Prod.fst : projectionAmbient X→X) ⁻¹' (Q 0).N)) hh

-- Elementary closed-carrier unit germ, independently proved from public native formulas.
private theorem native_top_off {n : ℕ} {X : CMfd.{0} n} {N : Set X}
    (B : GermIdeal n X) (hN : IsClosed N) (hIN : (vanishingIdeal (n:=n) N).Le B)
    (p : X) (hp : p∉N) : actualWholeSheafStalkIdeal B p=⊤ := by
  have hone : actualOriginalFunctionGerm (n:=n) p (fun _ => (1 : ℂ)) (holomorphicAt_const (n:=n) 1)=1 := by
    apply (actualStalkChartEquiv (n:=n) p).injective
    rw [actualOriginalFunctionGerm_chart,map_one]
    rfl
  have hv : (vanishingIdeal (n:=n) N).mem p (fun _ => (1 : ℂ)) := by
    refine ⟨holomorphicAt_const 1,?_⟩
    filter_upwards [hN.isOpen_compl.mem_nhds hp] with q hq hqN
    exact (hq hqN).elim
  have hmem : (1 : actualComplexStructureStalk (n:=n) p)∈actualWholeSheafStalkIdeal B p := by
    rw [←hone]
    exact Ideal.subset_span ⟨_,holomorphicAt_const 1,hIN p _ hv,rfl⟩
  apply top_unique
  intro r _
  simpa only [mul_one] using (actualWholeSheafStalkIdeal B p).mul_mem_left r hmem

theorem log_completion_eq {n : ℕ} {X : CMfd.{0} n} {N : Set X} {E : List (Set X)}
    (A : GermIdeal n X) (hA : A.IsCoherent) (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n E) (hTr : IsTransverse n N E) :
    logDerivIdealAlong N E (restrictOn n N A)=logDerivIdealAlong N E A := by
  have hRA := isCoherent_restrictOn_of_isClosedSubmanifold hA hN
  have hdRA := isCoherent_logDerivIdealAlong hRA hN hE hTr
  have hdA := isCoherent_logDerivIdealAlong hA hN hE hTr
  have heq (p : X) : actualWholeSheafStalkIdeal (logDerivIdealAlong N E (restrictOn n N A)) p=
      actualWholeSheafStalkIdeal (logDerivIdealAlong N E A) p := by
    by_cases hp : p∈N
    · obtain ⟨F,⟨_G⟩⟩ := exists_actual_projection_carrier_quotient_dictionary A hA hN hE hTr p hp
      obtain ⟨hz,hzero⟩ := parameterMap_zero F.Φ F.k F.output.1
      let v : parameterOpen F.Φ F.k := ⟨0,hz⟩
      have hcharts := F.output.2.2.2.2.2.1
      have h0 := fixed_chart_actual_log_dictionary F.Φ F.k F.hk F.hsrc F.κ hcharts A hA v
      have h1 := fixed_chart_actual_log_dictionary F.Φ F.k F.hk F.hsrc F.κ hcharts
        (restrictOn n N A) hRA v
      let phi := parameterGermPullback F.Φ F.k F.hsrc v
      have hinput : Ideal.map phi (actualWholeSheafStalkIdeal (restrictOn n N A) (parameterMapOn F.Φ F.k v))=
          Ideal.map phi (actualWholeSheafStalkIdeal A (parameterMapOn F.Φ F.k v)) := by
        rw [carrier_completion_native A hA hN,Ideal.map_sup,←h0.2.1]
        have hk : Ideal.map phi (RingHom.ker phi)=⊥ := (Ideal.map_eq_bot_iff_le_ker phi).mpr le_rfl
        rw [hk,sup_bot_eq]
      have hh := h1.2.2.2.1.symm
      rw [hinput] at hh
      have hh' := hh.trans h0.2.2.2.1
      change actualWholeSheafStalkIdeal (logDerivIdealAlong N E (restrictOn n N A)) (parameterMap F.Φ F.k 0)=
        actualWholeSheafStalkIdeal (logDerivIdealAlong N E A) (parameterMap F.Φ F.k 0) at hh'
      rw [hzero] at hh'
      exact hh'
    · rw [native_top_off _ hN.1 (carrier_le_log N E _) p hp,
        native_top_off _ hN.1 (carrier_le_log N E _) p hp]
  apply GermIdeal.ext
  funext p g
  apply propext
  by_cases hg : HolomorphicAt n g p
  · rw [coherent_mem_iff_actual_whole _ hdRA p g hg,
      coherent_mem_iff_actual_whole _ hdA p g hg,heq p]
  · exact iff_of_false (fun h => hg (GermIdeal.IsCoherent.holomorphicAt_mem hdRA h))
      (fun h => hg (GermIdeal.IsCoherent.holomorphicAt_mem hdA h))

private theorem rawIter_completion_succ {n : ℕ} {X : CMfd.{0} n} {N : Set X} {E : List (Set X)}
    (A : GermIdeal n X) (hA : A.IsCoherent) (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n E) (hTr : IsTransverse n N E) (r : ℕ) :
    rawIter N E (restrictOn n N A) (r+1)=rawIter N E A (r+1) := by
  induction r with
  | zero => exact log_completion_eq A hA hN hE hTr
  | succ r ih =>
    change ((logDerivIdealAlong N E)^[r+1+1]) (restrictOn n N A)=((logDerivIdealAlong N E)^[r+1+1]) A
    simpa only [rawIter,Function.iterate_succ_apply'] using congrArg (logDerivIdealAlong N E) ih

theorem carrierIter_add {n : ℕ} {X : CMfd.{0} n} {N : Set X} {E : List (Set X)}
    (A : GermIdeal n X) (hA : A.IsCoherent) (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n E) (hTr : IsTransverse n N E) (r s : ℕ) :
    carrierIter N E (carrierIter N E A s) r=carrierIter N E A (r+s) := by
  have hs := rawIter_coherent A hA hN hE hTr s
  have hcs := isCoherent_restrictOn_of_isClosedSubmanifold hs hN
  cases r with
  | zero =>
    simpa only [carrierIter,rawIter,Function.iterate_zero_apply,Nat.zero_add] using
      carrier_completion_idempotent _ hs hN
  | succ r =>
    rw [carrierIter_succ_eq_raw (carrierIter N E A s) hcs hN hE hTr r]
    rw [show r+1+s=(r+s)+1 by omega,carrierIter_succ_eq_raw _ hA hN hE hTr]
    change rawIter N E (restrictOn n N (rawIter N E A s)) (r+1)=rawIter N E A (r+s+1)
    rw [rawIter_completion_succ _ hs hN hE hTr]
    change ((logDerivIdealAlong N E)^[r+1]) (((logDerivIdealAlong N E)^[s]) A)=
      ((logDerivIdealAlong N E)^[r+s+1]) A
    calc
      _ = ((logDerivIdealAlong N E)^[r+1+s]) A :=
        (Function.iterate_add_apply (logDerivIdealAlong N E) (r+1) s A).symm
      _ = _ := congrArg (fun j => ((logDerivIdealAlong N E)^[j]) A) (by omega)

structure NativeIdealQuotient {d k : ℕ} {M : CMfd.{0} d} (p : M)
    (phi : actualComplexStructureStalk (n:=d) p →+* HolGerm (ComplexModel k))
    (K : Ideal (actualComplexStructureStalk (n:=d) p)) (J : Ideal (HolGerm (ComplexModel k))) where
  surjective : Function.Surjective phi
  image : Ideal.map phi K=J
  comap : Ideal.comap phi J=K
  every_numerator : ∀ r, r∈K ↔ phi r∈J
  e : (actualComplexStructureStalk (n:=d) p ⧸ K) ≃+* (HolGerm (ComplexModel k) ⧸ J)
  e_mk : ∀ r, e (Ideal.Quotient.mk K r)=Ideal.Quotient.mk J (phi r)
  e_action : ∀ r q, e (Ideal.Quotient.mk K r*q)=Ideal.Quotient.mk J (phi r)*e q
  structural_scalar : ∀ s : actualComplexStructureStalk (n:=0) (0 : ComplexModel 0),
    phi ((ambientPointMap d M).stalkMap p s)=algebraMap ℂ (HolGerm (ComplexModel k)) (actualComplexPointStalkEquiv s)
  all_scalars : ∀ (s : actualComplexStructureStalk (n:=0) (0 : ComplexModel 0)) q,
    e (Ideal.Quotient.mk K ((ambientPointMap d M).stalkMap p s)*q)=
      Ideal.Quotient.mk J (algebraMap ℂ (HolGerm (ComplexModel k)) (actualComplexPointStalkEquiv s))*e q

-- Elementary native representative/span proofs, locally recompiled with zero engine credit.
-- Provenance: accepted C04 original_stalk_mul/sum/span_image_mem, lines349--395.
-- No private mother references: proofs use only public chart/germ ring formulas.
section NativeSpanAlgebra
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

private theorem original_stalk_function_congr (p : M) {f g : M→ℂ}
    (hf : HolomorphicAt n f p) (hg : HolomorphicAt n g p) (he : f =ᶠ[𝓝 p] g) :
    actualOriginalFunctionGerm p f hf=actualOriginalFunctionGerm p g hg := by
  apply (actualStalkChartEquiv (n:=n) p).injective
  rw [actualOriginalFunctionGerm_chart,actualOriginalFunctionGerm_chart]
  exact chartTranslatedGerm_congr_original p f g hf hg he

private theorem original_stalk_mul (p : M) (f g : M → ℂ)
    (hf : HolomorphicAt n f p) (hg : HolomorphicAt n g p) :
    actualOriginalFunctionGerm p (fun q => f q * g q) (hf.mul hg) =
      actualOriginalFunctionGerm p f hf * actualOriginalFunctionGerm p g hg := by
  apply (actualStalkChartEquiv (n := n) p).injective
  rw [map_mul,actualOriginalFunctionGerm_chart,actualOriginalFunctionGerm_chart,
    actualOriginalFunctionGerm_chart]
  unfold chartTranslatedGerm translatedGerm
  exact HolGerm.mk_mul _ _ _ _

private theorem original_stalk_sum (p : M) {r : ℕ} (s : Fin r → M → ℂ)
    (hs : ∀ i, HolomorphicAt n (s i) p) :
    actualOriginalFunctionGerm p (fun q => ∑ i, s i q)
      (HolomorphicAt.sum Finset.univ fun i _ => hs i) =
      ∑ i, actualOriginalFunctionGerm p (s i) (hs i) := by
  apply (actualStalkChartEquiv (n := n) p).injective
  rw [map_sum]
  simp only [actualOriginalFunctionGerm_chart]
  unfold chartTranslatedGerm translatedGerm
  exact HolGerm.mk_sum _ _ _

private theorem span_image_mem {R : Type*} [CommRing R] (p : M)
    (φ : actualComplexStructureStalk (n := n) p →+* R) (L : Ideal R)
    (S : (M → ℂ) → Prop) (hS : ∀ g, S g → HolomorphicAt n g p)
    (hG : ∀ g hg, S g → φ (actualOriginalFunctionGerm p g hg) ∈ L)
    {f : M → ℂ} (hspan : IsInSpanAt (n := n) S p f) :
    φ (actualOriginalFunctionGerm p f hspan.1) ∈ L := by
  obtain ⟨hf,r,s,a,hs,ha,he⟩ := hspan
  have hsa (i) := (ha i).mul (hS (s i) (hs i))
  have hsum := HolomorphicAt.sum Finset.univ fun i _ => hsa i
  rw [original_stalk_function_congr p hf hsum he,
    original_stalk_sum p (fun i q => a i q * s i q) hsa,map_sum]
  apply L.sum_mem
  intro i _
  rw [original_stalk_mul _ _ _ (ha i) (hS (s i) (hs i)),map_mul]
  exact L.mul_mem_left _ (hG (s i) (hS (s i) (hs i)) (hs i))

private theorem native_mul (A B : GermIdeal n M) (hA : A.IsCoherent) (hB : B.IsCoherent) (p : M) :
    actualWholeSheafStalkIdeal (A.mul B) p=actualWholeSheafStalkIdeal A p*actualWholeSheafStalkIdeal B p := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨f,hf,hm,rfl⟩
    exact span_image_mem p (RingHom.id _) _
      (fun s => ∃ a b, A.mem p a ∧ B.mem p b ∧ s=a*b)
      (by
        rintro s ⟨a,b,ha,hb,rfl⟩
        exact (GermIdeal.IsCoherent.holomorphicAt_mem hA ha).mul
          (GermIdeal.IsCoherent.holomorphicAt_mem hB hb))
      (by
        rintro s hs ⟨a,b,ha,hb,rfl⟩
        change actualOriginalFunctionGerm p (fun q => a q*b q) hs ∈ _
        rw [original_stalk_mul p a b (GermIdeal.IsCoherent.holomorphicAt_mem hA ha)
          (GermIdeal.IsCoherent.holomorphicAt_mem hB hb)]
        exact Ideal.mul_mem_mul (Ideal.subset_span ⟨a,_,ha,rfl⟩) (Ideal.subset_span ⟨b,_,hb,rfl⟩)) hm
  · change Ideal.span _ * Ideal.span _ ≤ _
    rw [Ideal.span_mul_span]
    apply Ideal.span_le.mpr
    rintro _ ⟨u,⟨a,ha,ham,rfl⟩,v,⟨b,hb,hbm,rfl⟩,rfl⟩
    have hm : (A.mul B).mem p (a*b) := by
      change IsInSpanAt (fun s => ∃ a b, A.mem p a ∧ B.mem p b ∧ s=a*b) p (a*b)
      exact isInSpanAt_of_eq_mul ⟨a,b,ham,hbm,rfl⟩ (ha.mul hb) (holomorphicAt_const 1)
        (Eventually.of_forall fun _ => (one_mul _).symm)
    change actualOriginalFunctionGerm p a ha * actualOriginalFunctionGerm p b hb ∈ _
    rw [←original_stalk_mul p a b ha hb]
    exact Ideal.subset_span ⟨a*b,ha.mul hb,hm,rfl⟩

private theorem native_unit (p : M) : actualWholeSheafStalkIdeal (unitIdeal n M) p=⊤ := by
  have hone : actualOriginalFunctionGerm (n:=n) p (fun _ => (1 : ℂ)) (holomorphicAt_const (n:=n) 1)=1 := by
    apply (actualStalkChartEquiv (n:=n) p).injective
    rw [actualOriginalFunctionGerm_chart,map_one]
    rfl
  have hmem : (1 : actualComplexStructureStalk (n:=n) p)∈actualWholeSheafStalkIdeal (unitIdeal n M) p := by
    rw [←hone]
    exact Ideal.subset_span ⟨_,holomorphicAt_const 1,holomorphicAt_const 1,rfl⟩
  apply top_unique
  intro r _
  simpa only [mul_one] using (actualWholeSheafStalkIdeal (unitIdeal n M) p).mul_mem_left r hmem

private theorem native_pow (A : GermIdeal n M) (hA : A.IsCoherent) (p : M) (q : ℕ) :
    actualWholeSheafStalkIdeal (idealPow A q) p=(actualWholeSheafStalkIdeal A p)^q := by
  induction q with
  | zero => simpa only [idealPow_zero,pow_zero,Ideal.one_eq_top] using native_unit (n:=n) p
  | succ q ih => rw [idealPow_succ,native_mul _ _ (isCoherent_idealPow hA q) hA,ih,pow_succ]

private theorem native_finSum (Q : ℕ → GermIdeal n M) (m : ℕ)
    (hQ : ∀ i<m, (Q i).IsCoherent) (p : M) :
    actualWholeSheafStalkIdeal (finSumIdeal Q m) p=⨆ i : Fin m, actualWholeSheafStalkIdeal (Q i.val) p := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨f,hf,hm,rfl⟩
    exact span_image_mem p (RingHom.id _) _
      (fun s => ∃ i, i<m ∧ (Q i).mem p s)
      (by rintro s ⟨i,hi,hs⟩; exact GermIdeal.IsCoherent.holomorphicAt_mem (hQ i hi) hs)
      (by
        rintro s hs ⟨i,hi,hsi⟩
        exact Ideal.mem_iSup_of_mem ⟨i,hi⟩ (Ideal.subset_span ⟨s,hs,hsi,rfl⟩)) hm
  · apply iSup_le
    intro i
    apply Ideal.span_le.mpr
    rintro _ ⟨f,hf,hm,rfl⟩
    have hsum : (finSumIdeal Q m).mem p f := by
      change IsInSpanAt (fun s => ∃ j, j<m ∧ (Q j).mem p s) p f
      exact isInSpanAt_of_eq_mul ⟨i.val,i.isLt,hm⟩ hf (holomorphicAt_const 1)
        (Eventually.of_forall fun _ => (one_mul _).symm)
    exact Ideal.subset_span ⟨f,hf,hsum,rfl⟩

end NativeSpanAlgebra

private def nativeIdealQuotientOfImage {d k : ℕ} {M : CMfd.{0} d} (p : M)
    (phi : actualComplexStructureStalk (n:=d) p →+* HolGerm (ComplexModel k))
    (K : Ideal (actualComplexStructureStalk (n:=d) p)) (J : Ideal (HolGerm (ComplexModel k)))
    (hs : Function.Surjective phi) (him : Ideal.map phi K=J) (hc : Ideal.comap phi J=K)
    (hscalar : ∀ s : actualComplexStructureStalk (n:=0) (0 : ComplexModel 0),
      phi ((ambientPointMap d M).stalkMap p s)=algebraMap ℂ (HolGerm (ComplexModel k)) (actualComplexPointStalkEquiv s)) :
    NativeIdealQuotient p phi K J := by
  have hk : RingHom.ker ((Ideal.Quotient.mk J).comp phi)=K := by
    ext r
    change Ideal.Quotient.mk J (phi r)=0 ↔ r∈K
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Iff.of_eq (congrArg (fun I => r∈I) hc)
  have hsurj : Function.Surjective ((Ideal.Quotient.mk J).comp phi) := Ideal.Quotient.mk_surjective.comp hs
  let e := (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  have he (r) : e (Ideal.Quotient.mk K r)=Ideal.Quotient.mk J (phi r) := rfl
  refine ⟨hs,him,hc,?_,e,he,?_,hscalar,?_⟩
  · intro r
    rw [←hc]
    rfl
  · intro r q
    rw [map_mul,he]
  · intro r q
    rw [map_mul,he,hscalar]

private theorem source_scalar_formula
    {n : ℕ} {X : CMfd.{0} n} {A : GermIdeal n X} {N : Set X} {E : List (Set X)} {x : X}
    (F : OriginalLogFrame A N E x) (G : ProjectionCarrierQuotientOutput F)
    (v : parameterOpen F.Φ F.k) (s : actualComplexStructureStalk (n:=0) (0 : ComplexModel 0)) :
    parameterGermPullback F.Φ F.k F.hsrc v
      ((ambientPointMap n X).stalkMap (parameterMapOn F.Φ F.k v) s)=
    algebraMap ℂ (HolGerm (ComplexModel F.k)) (actualComplexPointStalkEquiv s) := by
  obtain ⟨c,rfl⟩ := actualComplexPointStalkEquiv.symm.surjective s
  change actualStalkChartEquiv (n:=F.k) v
    ((ChartedSpace.locallyRingedSpaceMap (parameterMapOn F.Φ F.k)
      (parameterMapOn_contMDiff F.Φ F.k F.hsrc)).stalkMap v
      ((ambientPointMap n X).stalkMap (parameterMapOn F.Φ F.k v) (actualComplexPointStalkEquiv.symm c)))=_
  rw [G.source_scalar.all_scalars v,actual_ambient_structural_constant_chart,RingEquiv.apply_symm_apply]
  rfl

private theorem completed_image {n k : ℕ} {X : CMfd.{0} n} {N : Set X}
    (B : GermIdeal n X) (hB : B.IsCoherent) (hN : IsClosedSubmanifold n N) (p : X)
    (phi : actualComplexStructureStalk (n:=n) p →+* HolGerm (ComplexModel k))
    (hk : RingHom.ker phi=actualWholeSheafStalkIdeal (vanishingIdeal (n:=n) N) p) :
    Ideal.map phi (actualWholeSheafStalkIdeal (restrictOn n N B) p)=
      Ideal.map phi (actualWholeSheafStalkIdeal B p) := by
  rw [carrier_completion_native B hB hN,Ideal.map_sup,←hk,
    (Ideal.map_eq_bot_iff_le_ker phi).mpr le_rfl,sup_bot_eq]

private theorem completed_comap {n k : ℕ} {X : CMfd.{0} n} {N : Set X}
    (B : GermIdeal n X) (hB : B.IsCoherent) (hN : IsClosedSubmanifold n N) (p : X)
    (phi : actualComplexStructureStalk (n:=n) p →+* HolGerm (ComplexModel k))
    (hs : Function.Surjective phi)
    (hk : RingHom.ker phi=actualWholeSheafStalkIdeal (vanishingIdeal (n:=n) N) p) :
    Ideal.comap phi (Ideal.map phi (actualWholeSheafStalkIdeal B p))=
      actualWholeSheafStalkIdeal (restrictOn n N B) p := by
  rw [Ideal.comap_map_of_surjective phi hs,←RingHom.ker_eq_comap_bot,hk,carrier_completion_native B hB hN]

theorem native_finite_power_sum_dictionary
    {n : ℕ} {X : CMfd.{0} n} {A : GermIdeal n X} {N : Set X} {E : List (Set X)} {x : X}
    (F : OriginalLogFrame A N E x) (G : ProjectionCarrierQuotientOutput F)
    (Q : ℕ → GermIdeal n X) (m : ℕ) (q : ℕ → ℕ)
    (hQ : ∀ i<m, (Q i).IsCoherent) :
    ∀ v : parameterOpen F.Φ F.k,
      let p := parameterMapOn F.Φ F.k v
      let phi := parameterGermPullback F.Φ F.k F.hsrc v
      let I := restrictOn n N (finSumIdeal (fun i => idealPow (Q i) (q i)) m)
      let J := ⨆ i : Fin m, (Ideal.map phi (actualWholeSheafStalkIdeal (Q i.val) p)) ^ q i.val
      Nonempty (NativeIdealQuotient p phi (actualWholeSheafStalkIdeal I p) J) := by
  intro v
  dsimp only
  let phi := parameterGermPullback F.Φ F.k F.hsrc v
  let p := parameterMapOn F.Φ F.k v
  let B := finSumIdeal (fun i => idealPow (Q i) (q i)) m
  have hc : B.IsCoherent := isCoherent_finSumIdeal_of_lt fun i hi => isCoherent_idealPow (hQ i hi) _
  have hf := fixed_chart_actual_log_dictionary F.Φ F.k F.hk F.hsrc F.κ
    F.output.2.2.2.2.2.1 A F.coherent v
  have hmap : Ideal.map phi (actualWholeSheafStalkIdeal B p)=
      ⨆ i : Fin m, (Ideal.map phi (actualWholeSheafStalkIdeal (Q i.val) p))^q i.val := by
    rw [native_finSum _ m (fun i hi => isCoherent_idealPow (hQ i hi) _) p,Ideal.map_iSup]
    apply iSup_congr
    intro i
    rw [native_pow _ (hQ i.val i.isLt) p,Ideal.map_pow]
  refine ⟨nativeIdealQuotientOfImage p phi _ _ hf.1 ?_ ?_ (source_scalar_formula F G v)⟩
  · rw [completed_image B hc F.smooth p phi hf.2.1]
    exact hmap
  · rw [←hmap]
    exact completed_comap B hc F.smooth p phi hf.1 hf.2.1

theorem same_frame_iterated_dictionary
    {n : ℕ} {X : CMfd.{0} n} {A : GermIdeal n X} {N : Set X} {E : List (Set X)} {x : X}
    (F : OriginalLogFrame A N E x) (G : ProjectionCarrierQuotientOutput F)
    (B : GermIdeal n X) (hB : B.IsCoherent) (r : ℕ) :
    ∀ v : parameterOpen F.Φ F.k,
      let p := parameterMapOn F.Φ F.k v
      let phi := parameterGermPullback F.Φ F.k F.hsrc v
      let a := parameterWeight F.Φ F.k F.κ F.hk v
      let J := ((logIdeal a)^[r]) (Ideal.map phi (actualWholeSheafStalkIdeal B p))
      Ideal.map phi (actualWholeSheafStalkIdeal (rawIter N E B r) p)=J ∧
      Nonempty (NativeIdealQuotient p phi (actualWholeSheafStalkIdeal (carrierIter N E B r) p) J) := by
  intro v
  dsimp only
  let phi := parameterGermPullback F.Φ F.k F.hsrc v
  let p := parameterMapOn F.Φ F.k v
  let a := parameterWeight F.Φ F.k F.κ F.hk v
  have hc (j) := rawIter_coherent B hB F.smooth F.snc F.transverse j
  have hf := fixed_chart_actual_log_dictionary F.Φ F.k F.hk F.hsrc F.κ
    F.output.2.2.2.2.2.1 B hB v
  have hm (j : ℕ) : Ideal.map phi (actualWholeSheafStalkIdeal (rawIter N E B j) p)=
      ((logIdeal a)^[j]) (Ideal.map phi (actualWholeSheafStalkIdeal B p)) := by
    induction j with
    | zero => rfl
    | succ j ih =>
      change Ideal.map phi (actualWholeSheafStalkIdeal (((logDerivIdealAlong N E)^[j+1]) B) p)=_
      rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
      have hj := fixed_chart_actual_log_dictionary F.Φ F.k F.hk F.hsrc F.κ
        F.output.2.2.2.2.2.1 (rawIter N E B j) (hc j) v
      exact hj.2.2.1.trans (congrArg (logIdeal a) ih)
  refine ⟨hm r,⟨nativeIdealQuotientOfImage p phi _ _ hf.1 ?_ ?_ (source_scalar_formula F G v)⟩⟩
  · change Ideal.map phi (actualWholeSheafStalkIdeal (restrictOn n N (rawIter N E B r)) p)=
      ((logIdeal a)^[r]) (Ideal.map phi (actualWholeSheafStalkIdeal B p))
    rw [completed_image _ (hc r) F.smooth p phi hf.2.1]
    exact hm r
  · rw [←hm r]
    exact completed_comap _ (hc r) F.smooth p phi hf.1 hf.2.1

private def oldPhi {n : ℕ} {X : CMfd.{0} n} {A : GermIdeal n X} {N : Set X}
    {E : List (Set X)} {x : X} (F : OriginalLogFrame A N E x) (t : parameterProduct F) :
    actualComplexStructureStalk (n:=n) (parameterMapOn F.Φ F.k t.1) →+* HolGerm (ComplexModel F.k) :=
  parameterGermPullback F.Φ F.k F.hsrc t.1

private def productPhi {n : ℕ} {X : CMfd.{0} n} {A : GermIdeal n X} {N : Set X}
    {E : List (Set X)} {x : X} (F : OriginalLogFrame A N E x)
    (G : ProjectionCarrierQuotientOutput F) (t : parameterProduct F) :
    actualComplexStructureStalk (n:=n+1) (productParameterMap F t) →+* HolGerm (ComplexModel (F.k+1)) :=
  (actualStalkChartEquiv (n:=F.k+1) (M:=parameterProduct F) t).toRingHom.comp
    ((ChartedSpace.locallyRingedSpaceMap (productParameterMap F) G.geometry.sigma_holo).stalkMap t).hom

private def piNative {n : ℕ} {X : CMfd.{0} n} {A : GermIdeal n X} {N : Set X}
    {E : List (Set X)} {x : X} (F : OriginalLogFrame A N E x) (t : parameterProduct F) :
    actualComplexStructureStalk (n:=n) (parameterMapOn F.Φ F.k t.1) →+*
      actualComplexStructureStalk (n:=n+1) (productParameterMap F t) :=
  ((ChartedSpace.locallyRingedSpaceMap (Prod.fst : projectionAmbient X→X)
    (ProductComplexManifold.contMDiff_fst (n:=n) (m:=1))).stalkMap (productParameterMap F t)).hom

private def stalkTransport {d : ℕ} {M : CMfd.{0} d} {p q : M} (h : p=q) :
    actualComplexStructureStalk (n:=d) p ≃+* actualComplexStructureStalk (n:=d) q :=
  h ▸ RingEquiv.refl _

structure FixedSumProjectionOutput
    {n : ℕ} {X : CMfd.{0} n} {A : GermIdeal n X} {N : Set X} {E : List (Set X)} {x : X}
    (F : OriginalLogFrame A N E x) (G : ProjectionCarrierQuotientOutput F)
    (I : GermIdeal n X) (Iplus : GermIdeal (n+1) (projectionAmbient X))
    (J : parameterOpen F.Φ F.k → Ideal (HolGerm (ComplexModel F.k))) where
  old_coherent : I.IsCoherent
  new_coherent : Iplus.IsCoherent
  global_eq : GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X) I=Iplus
  every_point : ∀ p : projectionAmbient X,
    actualWholeSheafStalkIdeal
      (GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X) I) p=
    actualWholeSheafStalkIdeal Iplus p
  every_function : ∀ (p : projectionAmbient X) (g : projectionAmbient X→ℂ),
    (GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X) I).mem p g ↔ Iplus.mem p g
  old_native : ∀ v : parameterOpen F.Φ F.k,
    NativeIdealQuotient (parameterMapOn F.Φ F.k v)
      (parameterGermPullback F.Φ F.k F.hsrc v)
      (actualWholeSheafStalkIdeal I (parameterMapOn F.Φ F.k v)) (J v)
  product_native : ∀ t : parameterProduct F,
    NativeIdealQuotient (productParameterMap F t) (productPhi F G t)
      (actualWholeSheafStalkIdeal Iplus (productParameterMap F t))
      (Ideal.map (HironakaRelativeNormalIdeal.tangentPullback F.k 1).toRingHom (J t.1))
  every_old_choice : ∀ (t : parameterProduct F)
    (eOld : (actualComplexStructureStalk (n:=n) (parameterMapOn F.Φ F.k t.1) ⧸
      actualWholeSheafStalkIdeal I (parameterMapOn F.Φ F.k t.1)) ≃+*
      (HolGerm (ComplexModel F.k) ⧸ J t.1)),
    (∀ r, eOld (Ideal.Quotient.mk _ r)=Ideal.Quotient.mk _ (oldPhi F t r)) →
    let Jplus := Ideal.map (HironakaRelativeNormalIdeal.tangentPullback F.k 1).toRingHom (J t.1)
    ∃ D : NativeQuotientDiagram
      ((Ideal.Quotient.mk (J t.1)).comp (oldPhi F t))
      ((Ideal.Quotient.mk Jplus).comp (productPhi F G t))
      (piNative F t)
      (Ideal.quotientMap Jplus (HironakaRelativeNormalIdeal.tangentPullback F.k 1).toRingHom Ideal.le_comap_map)
      (actualWholeSheafStalkIdeal I (parameterMapOn F.Φ F.k t.1))
      (actualWholeSheafStalkIdeal Iplus (productParameterMap F t)), D.e=eOld
  factory_native : ∀ w : parameterOpen (X:=projectionAmbient X) G.geometry.Ψ (F.k+1),
    let p := parameterMapOn (X:=projectionAmbient X) G.geometry.Ψ (F.k+1) w
    let phiw := parameterGermPullback (X:=projectionAmbient X) G.geometry.Ψ (F.k+1) G.geometry.hsrc w
    let Jprod := Ideal.map (HironakaRelativeNormalIdeal.tangentPullback F.k 1).toRingHom (J (G.geometry.rho w).1)
    let rhoHol := actualHolomorphicGermPullback G.geometry.rho.contMDiff w
    NativeIdealQuotient p phiw (actualWholeSheafStalkIdeal Iplus p) (Ideal.map rhoHol.toRingHom Jprod)
  factory_every_native_germ : ∀ (w : parameterOpen (X:=projectionAmbient X) G.geometry.Ψ (F.k+1))
    (r : actualComplexStructureStalk (n:=n+1) (productParameterMap F (G.geometry.rho w))),
    parameterGermPullback (X:=projectionAmbient X) G.geometry.Ψ (F.k+1) G.geometry.hsrc w
        (stalkTransport (G.geometry.sigma w).symm r)=
      actualHolomorphicGermPullback G.geometry.rho.contMDiff w (productPhi F G (G.geometry.rho w) r)
  factory_quotient_comparison : ∀ w : parameterOpen (X:=projectionAmbient X) G.geometry.Ψ (F.k+1),
    let t := G.geometry.rho w
    let Jprod := Ideal.map (HironakaRelativeNormalIdeal.tangentPullback F.k 1).toRingHom (J t.1)
    let rhoHol := actualHolomorphicGermPullback G.geometry.rho.contMDiff w
    let Jfactory := Ideal.map rhoHol.toRingHom Jprod
    ∃ qmap : (HolGerm (ComplexModel (F.k+1)) ⧸ Jprod) →+*
        (HolGerm (ComplexModel (F.k+1)) ⧸ Jfactory),
      (∀ z, qmap (Ideal.Quotient.mk Jprod z)=Ideal.Quotient.mk Jfactory (rhoHol z)) ∧
      (∀ r : actualComplexStructureStalk (n:=n+1) (productParameterMap F t),
        (factory_native w).e (Ideal.Quotient.mk _ (stalkTransport (G.geometry.sigma w).symm r))=
          qmap ((product_native t).e (Ideal.Quotient.mk _ r))) ∧
      (∀ (z : HolGerm (ComplexModel (F.k+1))) q,
        qmap (Ideal.Quotient.mk Jprod z*q)=Ideal.Quotient.mk Jfactory (rhoHol z)*qmap q)
  old_boundary : ∀ i : Fin E.length, projectedAmbientSlot F i.castSucc=Option.map Fin.castSucc (F.κ i)
  horizontal_slot : projectedParameterSlot F (Fin.last E.length)=some (Fin.last F.k)
  recentered_horizontal : ∀ (v : parameterOpen F.Φ F.k) (c : ComplexModel 1),
    parameterWeight (X:=projectionAmbient X) G.geometry.Ψ (F.k+1)
      (projectedAmbientSlot F) (Nat.succ_le_succ F.hk) (G.geometry.rho.symm (v,c)) (Fin.last F.k)=
      HolGerm.constHom (c 0)+coordinateGerm (Fin.last F.k)
  all_weights : ∀ w : parameterOpen (X:=projectionAmbient X) G.geometry.Ψ (F.k+1),
    parameterWeight (X:=projectionAmbient X) G.geometry.Ψ (F.k+1)
      (projectedAmbientSlot F) (Nat.succ_le_succ F.hk) w=
      HironakaActualProjectionLogDerivativeIdeal.projectionWeight
        (parameterWeight F.Φ F.k F.κ F.hk (G.geometry.rho w).1) ((G.geometry.rho w).2 0)

private theorem rhoHol_id
    {n : ℕ} {X : CMfd.{0} n} {A : GermIdeal n X} {N : Set X} {E : List (Set X)} {x : X}
    (F : OriginalLogFrame A N E x) (G : ProjectionCarrierQuotientOutput F)
    (w : parameterOpen (X:=projectionAmbient X) G.geometry.Ψ (F.k+1)) :
    actualHolomorphicGermPullback G.geometry.rho.contMDiff w=AlgHom.id ℂ (HolGerm (ComplexModel (F.k+1))) := by
  apply AlgHom.ext
  intro h
  obtain ⟨r,rfl⟩ := (actualStalkChartEquiv (n:=F.k+1) (G.geometry.rho w)).surjective h
  rw [←actualNativeStalk_chart_pullback]
  exact G.geometry.rho_all_native_germs w r

private def nativeIQPointTransport {d k : ℕ} {M : CMfd.{0} d} {p q : M} (h : p=q)
    (I : GermIdeal d M)
    (phi : actualComplexStructureStalk (n:=d) p →+* HolGerm (ComplexModel k))
    (psi : actualComplexStructureStalk (n:=d) q →+* HolGerm (ComplexModel k))
    (J : Ideal (HolGerm (ComplexModel k)))
    (hphi : ∀ r, psi (stalkTransport h r)=phi r)
    (Q : NativeIdealQuotient p phi (actualWholeSheafStalkIdeal I p) J) :
    NativeIdealQuotient q psi (actualWholeSheafStalkIdeal I q) J := by
  cases h
  have he : psi=phi := RingHom.ext hphi
  subst psi
  exact Q

private theorem product_scalar_formula
    {n : ℕ} {X : CMfd.{0} n} {A : GermIdeal n X} {N : Set X} {E : List (Set X)} {x : X}
    (F : OriginalLogFrame A N E x) (G : ProjectionCarrierQuotientOutput F)
    (t : parameterProduct F) (s : actualComplexStructureStalk (n:=0) (0 : ComplexModel 0)) :
    productPhi F G t ((ambientPointMap (n+1) (projectionAmbient X)).stalkMap (productParameterMap F t) s)=
      algebraMap ℂ (HolGerm (ComplexModel (F.k+1))) (actualComplexPointStalkEquiv s) := by
  obtain ⟨c,rfl⟩ := actualComplexPointStalkEquiv.symm.surjective s
  change actualStalkChartEquiv (n:=F.k+1) t
    ((ChartedSpace.locallyRingedSpaceMap (productParameterMap F) G.geometry.sigma_holo).stalkMap t
      ((ambientPointMap (n+1) (projectionAmbient X)).stalkMap (productParameterMap F t)
        (actualComplexPointStalkEquiv.symm c)))=_
  rw [G.product_scalar.all_scalars t,actual_ambient_structural_constant_chart,RingEquiv.apply_symm_apply]
  rfl

private theorem kernel_of_comap {R S : Type*} [CommRing R] [CommRing S]
    (phi : R→+*S) (K : Ideal R) (J : Ideal S) (hc : Ideal.comap phi J=K) :
    RingHom.ker ((Ideal.Quotient.mk J).comp phi)=K := by
  ext r
  change Ideal.Quotient.mk J (phi r)=0 ↔ r∈K
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Iff.of_eq (congrArg (fun I => r∈I) hc)

private theorem comap_of_kernel {R S : Type*} [CommRing R] [CommRing S]
    (phi : R→+*S) (K : Ideal R) (J : Ideal S)
    (hk : RingHom.ker ((Ideal.Quotient.mk J).comp phi)=K) : Ideal.comap phi J=K := by
  ext r
  change phi r∈J ↔ r∈K
  rw [←hk]
  change phi r∈J ↔ Ideal.Quotient.mk J (phi r)=0
  exact Ideal.Quotient.eq_zero_iff_mem.symm

private def diagramWithOld {R R' S S' : Type*} [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
    (alpha : R→+*S) (alpha' : R'→+*S') (f : R→+*R') (g : S→+*S') (K : Ideal R) (K' : Ideal R')
    (hs : Function.Surjective alpha) (hs' : Function.Surjective alpha')
    (hk : RingHom.ker alpha=K) (hk' : RingHom.ker alpha'=K')
    (hi : Ideal.map f K=K') (hq : alpha'.comp f=g.comp alpha)
    (eOld : (R⧸K)≃+*S) (hOld : ∀ r,eOld (Ideal.Quotient.mk K r)=alpha r) :
    NativeQuotientDiagram alpha alpha' f g K K' := by
  let e' : (R'⧸K')≃+*S' := (Ideal.quotEquivOfEq hk'.symm).trans (RingHom.quotientKerEquivOfSurjective hs')
  have he' (r) : e' (Ideal.Quotient.mk K' r)=alpha' r := rfl
  let fbar := Ideal.quotientMap K' f (hi ▸ Ideal.le_comap_map)
  have hfbar (r) : fbar (Ideal.Quotient.mk K r)=Ideal.Quotient.mk K' (f r) := rfl
  refine ⟨hs,hs',hk,hk',hi,hq,eOld,e',hOld,he',?_,?_,fbar,hfbar,?_⟩
  · intro r q
    rw [map_mul,hOld]
  · intro r q
    rw [map_mul,he']
  · intro q
    obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [hfbar,he',hOld]
    exact RingHom.congr_fun hq r

private def productNativeOfOld
    {n : ℕ} {X : CMfd.{0} n} {A : GermIdeal n X} {N : Set X} {E : List (Set X)} {x : X}
    (F : OriginalLogFrame A N E x) (G : ProjectionCarrierQuotientOutput F)
    (I : GermIdeal n X) (hI : I.IsCoherent) (hIN : (vanishingIdeal (n:=n) N).Le I)
    (J : parameterOpen F.Φ F.k → Ideal (HolGerm (ComplexModel F.k)))
    (hold : ∀ v, NativeIdealQuotient (parameterMapOn F.Φ F.k v)
      (parameterGermPullback F.Φ F.k F.hsrc v) (actualWholeSheafStalkIdeal I (parameterMapOn F.Φ F.k v)) (J v))
    (t : parameterProduct F) :
    NativeIdealQuotient (productParameterMap F t) (productPhi F G t)
      (actualWholeSheafStalkIdeal (GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X) I) (productParameterMap F t))
      (Ideal.map (HironakaRelativeNormalIdeal.tangentPullback F.k 1).toRingHom (J t.1)) := by
  have hf := G.every_coherent_ideal I hI t
  let D := Classical.choice (hf.2.2 hIN)
  have hm := hf.2.1
  change Ideal.map (productPhi F G t)
    (actualWholeSheafStalkIdeal (GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X) I) (productParameterMap F t))=
    Ideal.map (HironakaRelativeNormalIdeal.tangentPullback F.k 1).toRingHom
      (Ideal.map (parameterGermPullback F.Φ F.k F.hsrc t.1) (actualWholeSheafStalkIdeal I (parameterMapOn F.Φ F.k t.1))) at hm
  rw [(hold t.1).image] at hm
  have hk := D.kernel'
  change RingHom.ker ((Ideal.Quotient.mk
    (Ideal.map (HironakaRelativeNormalIdeal.tangentPullback F.k 1).toRingHom
      (Ideal.map (parameterGermPullback F.Φ F.k F.hsrc t.1) (actualWholeSheafStalkIdeal I (parameterMapOn F.Φ F.k t.1))))).comp
      (productPhi F G t))=_ at hk
  rw [(hold t.1).image] at hk
  exact nativeIdealQuotientOfImage _ _ _ _
    ((actualStalkChartEquiv (n:=F.k+1) t).surjective.comp (G.carrier t).surjective')
    hm (comap_of_kernel _ _ _ hk) (product_scalar_formula F G t)

private def fixedSumProjectionOutput
    {n : ℕ} {X : CMfd.{0} n} {A : GermIdeal n X} {N : Set X} {E : List (Set X)} {x : X}
    (F : OriginalLogFrame A N E x) (G : ProjectionCarrierQuotientOutput F)
    (I : GermIdeal n X) (Iplus : GermIdeal (n+1) (projectionAmbient X))
    (J : parameterOpen F.Φ F.k → Ideal (HolGerm (ComplexModel F.k)))
    (hI : I.IsCoherent) (hIN : (vanishingIdeal (n:=n) N).Le I)
    (hglobal : GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X) I=Iplus)
    (hold : ∀ v, NativeIdealQuotient (parameterMapOn F.Φ F.k v)
      (parameterGermPullback F.Φ F.k F.hsrc v) (actualWholeSheafStalkIdeal I (parameterMapOn F.Φ F.k v)) (J v)) :
    FixedSumProjectionOutput F G I Iplus J := by
  subst Iplus
  let hprod := productNativeOfOld F G I hI hIN J hold
  let hfactory := fun w : parameterOpen (X:=projectionAmbient X) G.geometry.Ψ (F.k+1) => by
    let t := G.geometry.rho w
    let Jprod := Ideal.map (HironakaRelativeNormalIdeal.tangentPullback F.k 1).toRingHom (J t.1)
    let rhoHol := actualHolomorphicGermPullback G.geometry.rho.contMDiff w
    have hm : Ideal.map rhoHol.toRingHom Jprod=Jprod := by
      rw [show rhoHol=AlgHom.id ℂ _ from rhoHol_id F G w]
      exact Ideal.map_idₐ Jprod
    change NativeIdealQuotient (parameterMapOn (X:=projectionAmbient X) G.geometry.Ψ (F.k+1) w)
      (parameterGermPullback (X:=projectionAmbient X) G.geometry.Ψ (F.k+1) G.geometry.hsrc w)
      (actualWholeSheafStalkIdeal
        (GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X) I)
        (parameterMapOn (X:=projectionAmbient X) G.geometry.Ψ (F.k+1) w)) (Ideal.map rhoHol.toRingHom Jprod)
    rw [hm]
    exact nativeIQPointTransport (G.geometry.sigma w).symm _ (productPhi F G t)
      (parameterGermPullback (X:=projectionAmbient X) G.geometry.Ψ (F.k+1) G.geometry.hsrc w) Jprod
      (G.factory_all_germs w) (hprod t)
  refine ⟨hI,isCoherent_pullback ProductComplexManifold.contMDiff_fst hI,rfl,?_,?_,hold,hprod,?_,hfactory,?_,?_,?_,?_,?_,G.geometry.all_weights⟩
  · intro p
    rfl
  · intro p g
    rfl
  · intro t eOld hOld
    let Jplus := Ideal.map (HironakaRelativeNormalIdeal.tangentPullback F.k 1).toRingHom (J t.1)
    have hs : Function.Surjective ((Ideal.Quotient.mk (J t.1)).comp (oldPhi F t)) :=
      Ideal.Quotient.mk_surjective.comp (hold t.1).surjective
    have hs' : Function.Surjective ((Ideal.Quotient.mk Jplus).comp (productPhi F G t)) :=
      Ideal.Quotient.mk_surjective.comp (hprod t).surjective
    have hk := kernel_of_comap _ _ _ (hold t.1).comap
    have hk' := kernel_of_comap _ _ _ (hprod t).comap
    have hi := (G.every_coherent_ideal I hI t).1
    have hsq : ((Ideal.Quotient.mk Jplus).comp (productPhi F G t)).comp (piNative F t)=
        (Ideal.quotientMap Jplus (HironakaRelativeNormalIdeal.tangentPullback F.k 1).toRingHom Ideal.le_comap_map).comp
          ((Ideal.Quotient.mk (J t.1)).comp (oldPhi F t)) := by
      ext r
      change Ideal.Quotient.mk Jplus (productPhi F G t (piNative F t r))=_
      have hh := G.all_germs t r
      change productPhi F G t (piNative F t r)=HironakaRelativeNormalIdeal.tangentPullback F.k 1 (oldPhi F t r) at hh
      rw [hh]
      rfl
    let D := diagramWithOld _ _ (piNative F t)
      (Ideal.quotientMap Jplus (HironakaRelativeNormalIdeal.tangentPullback F.k 1).toRingHom Ideal.le_comap_map)
      _ _ hs hs' hk hk' hi hsq eOld hOld
    exact ⟨D,rfl⟩
  · intro w r
    rw [rhoHol_id]
    exact G.factory_all_germs w r
  · intro w
    let t := G.geometry.rho w
    let Jprod := Ideal.map (HironakaRelativeNormalIdeal.tangentPullback F.k 1).toRingHom (J t.1)
    let rhoHol := actualHolomorphicGermPullback G.geometry.rho.contMDiff w
    let Jfactory := Ideal.map rhoHol.toRingHom Jprod
    let qmap := Ideal.quotientMap Jfactory rhoHol.toRingHom Ideal.le_comap_map
    refine ⟨qmap,?_,?_,?_⟩
    · intro z
      rfl
    · intro r
      rw [(hfactory w).e_mk,(hprod t).e_mk]
      change Ideal.Quotient.mk Jfactory
        (parameterGermPullback (X:=projectionAmbient X) G.geometry.Ψ (F.k+1) G.geometry.hsrc w
          (stalkTransport (G.geometry.sigma w).symm r))=
        Ideal.Quotient.mk Jfactory (rhoHol (productPhi F G t r))
      apply congrArg (Ideal.Quotient.mk Jfactory)
      rw [show rhoHol=AlgHom.id ℂ _ from rhoHol_id F G w]
      exact G.factory_all_germs w r
    · intro z q
      rw [map_mul]
      rfl
  · intro i
    simp [projectedAmbientSlot]
  · simp [projectedParameterSlot]
  · intro v c
    simpa only [G.geometry.rho.apply_symm_apply] using
      G.geometry.horizontal_weight (G.geometry.rho.symm (v,c))

private def iteratedPowerSumNative
    {n : ℕ} {X : CMfd.{0} n} {A : GermIdeal n X} {N : Set X} {E : List (Set X)} {x : X}
    (F : OriginalLogFrame A N E x) (G : ProjectionCarrierQuotientOutput F)
    (B : GermIdeal n X) (hB : B.IsCoherent) (m : ℕ) (q : ℕ→ℕ) (v : parameterOpen F.Φ F.k) :
    let p := parameterMapOn F.Φ F.k v
    let phi := parameterGermPullback F.Φ F.k F.hsrc v
    let J0 := Ideal.map phi (actualWholeSheafStalkIdeal B p)
    let a := parameterWeight F.Φ F.k F.κ F.hk v
    NativeIdealQuotient p phi
      (actualWholeSheafStalkIdeal (restrictOn n N (finSumIdeal (fun i => idealPow (rawIter N E B i) (q i)) m)) p)
      (⨆ i : Fin m, (((logIdeal a)^[i.val]) J0) ^ q i.val) := by
  dsimp only
  have hc (j) := rawIter_coherent B hB F.smooth F.snc F.transverse j
  let Q := Classical.choice (native_finite_power_sum_dictionary F G (rawIter N E B) m q (fun i _ => hc i) v)
  have hj : (⨆ i : Fin m, (Ideal.map (parameterGermPullback F.Φ F.k F.hsrc v)
      (actualWholeSheafStalkIdeal (rawIter N E B i.val) (parameterMapOn F.Φ F.k v)))^q i.val)=
      ⨆ i : Fin m, (((logIdeal (parameterWeight F.Φ F.k F.κ F.hk v))^[i.val])
        (Ideal.map (parameterGermPullback F.Φ F.k F.hsrc v) (actualWholeSheafStalkIdeal B (parameterMapOn F.Φ F.k v))))^q i.val := by
    apply iSup_congr
    intro i
    rw [(same_frame_iterated_dictionary F G B hB i.val v).1]
  rw [←hj]
  exact Q

theorem same_frame_marked_sum_dictionary
    {n : ℕ} {X : CMfd.{0} n} {A : GermIdeal n X} {N : Set X} {E : List (Set X)} {x : X}
    (F : OriginalLogFrame A N E x) (G : ProjectionCarrierQuotientOutput F)
    (B : GermIdeal n X) (hB : B.IsCoherent) (d m : ℕ) (hmd : m≤d) :
    let M : MarkedIdeal n X := { N := N, E := E, ideal := B, d := d }
    let Q := rawLogMarked M
    let Qplus := rawLogMarked (liftMarked M)
    let IB := (bmCarrierSum Q m).ideal
    let IBplus := (bmCarrierSum Qplus m).ideal
    let IP := restrictOn n N (msum Q m).ideal
    let IPplus := restrictOn (n+1) ((Prod.fst : projectionAmbient X→X) ⁻¹' N) (msum Qplus m).ideal
    let J0 := fun v : parameterOpen F.Φ F.k =>
      Ideal.map (parameterGermPullback F.Φ F.k F.hsrc v)
        (actualWholeSheafStalkIdeal B (parameterMapOn F.Φ F.k v))
    let Jr := fun (v : parameterOpen F.Φ F.k) (j : ℕ) =>
      ((logIdeal (parameterWeight F.Φ F.k F.κ F.hk v))^[j]) (J0 v)
    let JB := fun v : parameterOpen F.Φ F.k =>
      ⨆ i : Fin m, (Jr v i.val) ^ (bmCommonMark Q m / (d-i.val))
    let JP := fun v : parameterOpen F.Φ F.k =>
      ⨆ i : Fin m, (Jr v i.val) ^ (sumExp (fun j => d-j) m i.val)
    (∀ j<m, 0<(Q j).d ∧ (Q j).N=N ∧ (Q j).E=E ∧ (Q j).d=d-j) ∧
    (Q 0=M) ∧
    (bmCarrierSum Q m).N=N ∧ (bmCarrierSum Q m).E=E ∧ (bmCarrierSum Q m).d=bmCommonMark Q m ∧
    (msum Q m).N=N ∧ (msum Q m).E=E ∧ (msum Q m).d=(Finset.range m).prod (fun j => d-j) ∧
    (bmCarrierSum Qplus m).N=(Prod.fst : projectionAmbient X→X) ⁻¹' N ∧
    (bmCarrierSum Qplus m).E=E.map ((Prod.fst : projectionAmbient X→X) ⁻¹' ·) ++ [horizontal X] ∧
    (bmCarrierSum Qplus m).d=bmCommonMark Q m ∧
    (msum Qplus m).N=(Prod.fst : projectionAmbient X→X) ⁻¹' N ∧
    (msum Qplus m).E=E.map ((Prod.fst : projectionAmbient X→X) ⁻¹' ·) ++ [horizontal X] ∧
    (msum Qplus m).d=(msum Q m).d ∧
    Nonempty (FixedSumProjectionOutput F G IB IBplus JB) ∧
    Nonempty (FixedSumProjectionOutput F G IP IPplus JP) := by
  dsimp only
  let M : MarkedIdeal n X := { N := N, E := E, ideal := B, d := d }
  let Q := rawLogMarked M
  let Qplus := rawLogMarked (liftMarked M)
  have hM : M.IsWellFormed := ⟨F.smooth,hB,F.snc,F.transverse⟩
  have hc (j) : (Q j).ideal.IsCoherent := rawIter_coherent B hB F.smooth F.snc F.transverse j
  have hFam : (fun i => liftMarked (Q i))=Qplus := by
    funext i
    exact (projection_marked_family_eq M hM i).1
  have hBM := congrArg MarkedIdeal.ideal (projection_bmFiniteSum_eq Q m (fun i _ => hc i) F.smooth).2
  rw [hFam] at hBM
  have hPM := (projection_productMsum_eq Q m (fun i _ => hc i) F.smooth).2
  rw [hFam] at hPM
  have hBMcoh : (bmCarrierSum Q m).ideal.IsCoherent :=
    isCoherent_restrictOn_of_isClosedSubmanifold (bmFiniteSum_coherent Q m (fun i _ => hc i)) F.smooth
  have hPMcoh : (restrictOn n N (msum Q m).ideal).IsCoherent :=
    isCoherent_restrictOn_of_isClosedSubmanifold
      (isCoherent_finSumIdeal_of_lt fun i _ => isCoherent_idealPow (hc i) _) F.smooth
  refine ⟨?_,logMarked_zero M,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_,?_⟩
  · intro j hj
    refine ⟨?_,rfl,rfl,rfl⟩
    change 0<d-j
    omega
  · exact ⟨fixedSumProjectionOutput F G _ _ _ hBMcoh vanishingIdeal_le_restrictOn hBM
      (fun v => iteratedPowerSumNative F G B hB m (fun i => bmCommonMark Q m/(d-i)) v)⟩
  · exact ⟨fixedSumProjectionOutput F G _ _ _ hPMcoh vanishingIdeal_le_restrictOn hPM
      (fun v => iteratedPowerSumNative F G B hB m (fun i => sumExp (fun j => d-j) m i) v)⟩

end
end Hironaka.HironakaActualIteratedLogMarkedFamily
