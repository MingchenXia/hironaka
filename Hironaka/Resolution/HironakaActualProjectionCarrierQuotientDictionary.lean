/- Actual same-frame projection carrier quotients. BP FIRST: complete five-proof
hironaka-actual-projection-carrier-quotient-dictionary.tex.
One accepted824 choice, genuine literal product/shuffle/parameter comparison;
no new-native-log operation equality, global purity or projection-isomorphism claim. -/
import Hironaka.Resolution.HironakaActualIntrinsicLogQuotientDictionary
import Hironaka.Resolution.HironakaActualIntrinsicCarrierDerivationTransport
import Hironaka.Resolution.HironakaSingularSubspaceBlowupCartier
import Hironaka.Resolution.HironakaActualProjectionTestRecord
import Hironaka.Resolution.HironakaSmoothSubmersionAdaptedProductCoordinates
import Hironaka.Resolution.HironakaSmoothSubmersionRelativeRestriction
import Hironaka.Resolution.HironakaActualProjectionIntrinsicHS
import Hironaka.Resolution.HironakaActualProjectionLogDerivativeIdeal
set_option autoImplicit false
open Set Filter Classical TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualProjectionCarrierQuotientDictionary
noncomputable section
open scoped ProductComplexManifold
open DerivativeIdealAlong ProductComplexManifold DerivativeIdealAlongEtale HironakaActualIntrinsicCarrierDerivationTransport HironakaActualAnalyticSubspaceResidue
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm BlowupTowers
  HironakaActualIntrinsicLogQuotientDictionary HironakaActualIntrinsicLogDerivativeFrame
  HironakaActualExceptionalLogDerivativeIdeal HironakaActualProjectionTestRecord
  HironakaSmoothSubmersionContactParameterCharts HironakaContactParameterIntrinsicOrder
  HironakaSmoothSubmersionContactParameterCoefficientIdeals
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaReducedComplexAnalyticSpaces
  HironakaActualWholeStalkHolomorphicPullback HironakaActualAnalyticSubspaceOpenRestriction
  HironakaHolomorphicJetRankLoci HironakaHolomorphicJetChartInvariance
  HironakaActualOpenIntrinsicHS HironakaHolomorphicJetMonomialSpan
  HironakaIntrinsicCarrierBoundaryCharts HironakaSmoothSubmersionAdaptedProductCoordinates
  BlowupFlatCoordinates NormalCrossings GiraudAlong RelativePrincipalizationSpan
  ResolutionInvariantSpec MarkedIdeals MarkedIdeals.MarkedIdeal Hironaka.RegularLocusDense

abbrev OriginalLogOutput {n : ℕ} {X : CMfd.{0} n} (A : GermIdeal n X)
    (N : Set X) (E : List (Set X)) (x : X) (k : ℕ) (hk : k≤n)
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
    (κ : Fin E.length→Option (Fin n)) (τ : Fin E.length→Option (Fin k))
    (hsrc : Φ.source⊆(chartAt (ComplexModel n) x).target) : Prop :=
  Φ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
        (∀ i j, κ i = some j → j.val < k) ∧ Set.InjOn κ {i | x ∈ E.get i} ∧
        (∀ i, Option.map Fin.val (τ i) = Option.map Fin.val (κ i)) ∧
        (∀ v : parameterOpen Φ k, ∀ i, parameterMapOn Φ k v ∈ E.get i ↔
          ∃ j : Fin k, τ i = some j ∧ v.val j = 0) ∧
        (∀ p ∈ flatDomain Φ,
          (p ∈ N ↔ flatMap Φ p ∈ complexCoordinatePlane n k) ∧
          ∀ i, p ∈ E.get i ↔ ∃ j, κ i = some j ∧ flatCoord Φ j p = 0) ∧
        (ChartedSpace.locallyRingedSpaceMap (parameterMapOn Φ k) (parameterMapOn_contMDiff Φ k hsrc) ≫
          ambientPointMap n X = ambientPointMap k (parameterOpen Φ k)) ∧
        (logDerivIdealAlong N E A).IsCoherent ∧
        ∀ v : parameterOpen Φ k,
          let φ := parameterGermPullback Φ k hsrc v
          let a := parameterWeight Φ k κ hk v
          let J := Ideal.map φ (actualWholeSheafStalkIdeal A (parameterMapOn Φ k v))
          let D := actualWholeSheafStalkIdeal (logDerivIdealAlong N E A) (parameterMapOn Φ k v)
          Function.Surjective φ ∧
          RingHom.ker φ = actualWholeSheafStalkIdeal (vanishingIdeal (n := n) N) (parameterMapOn Φ k v) ∧
          Ideal.map φ D = logIdeal a J ∧ Ideal.comap φ (logIdeal a J) = D ∧
          ∃ e : (actualComplexStructureStalk (n := n) (parameterMapOn Φ k v) ⧸ D) ≃+*
              (HolGerm (ComplexModel k) ⧸ logIdeal a J),
            (∀ r : actualComplexStructureStalk (n := n) (parameterMapOn Φ k v),
              e (Ideal.Quotient.mk D r) = Ideal.Quotient.mk (logIdeal a J) (φ r)) ∧
            ∀ (r : actualComplexStructureStalk (n := n) (parameterMapOn Φ k v))
              (q : actualComplexStructureStalk (n := n) (parameterMapOn Φ k v) ⧸ D),
              e (Ideal.Quotient.mk D r * q) = Ideal.Quotient.mk (logIdeal a J) (φ r) * e q

structure OriginalLogFrame {n : ℕ} {X : CMfd.{0} n}
    (A : GermIdeal n X) (N : Set X) (E : List (Set X)) (x : X) where
  coherent : A.IsCoherent
  smooth : IsClosedSubmanifold n N
  snc : IsSNCDivisor n E
  transverse : IsTransverse n N E
  k : ℕ
  hk : k≤n
  Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x)
  κ : Fin E.length→Option (Fin n)
  τ : Fin E.length→Option (Fin k)
  hsrc : Φ.source⊆(chartAt (ComplexModel n) x).target
  output : OriginalLogOutput A N E x k hk Φ κ τ hsrc

-- Exact index permutation and continuous linear map, implemented internally.
def projectionShuffle (n k : ℕ) (hk : k≤n) : Fin (n+1) ≃ Fin (n+1) :=
  finSuccEquivLast.trans (finSuccEquiv' (⟨k,Nat.lt_succ_of_le hk⟩ : Fin (n+1))).symm

def projectionShuffleLinear (n k : ℕ) (hk : k≤n) :
    ComplexModel (n+1) ≃L[ℂ] ComplexModel (n+1) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (projectionShuffle n k hk)).toContinuousLinearEquiv



private theorem shuffle_old (n k : ℕ) (hk : k≤n) (i : Fin n) :
    projectionShuffle n k hk i.castSucc=(⟨k,Nat.lt_succ_of_le hk⟩ : Fin (n+1)).succAbove i := by
  simp [projectionShuffle]

private theorem shuffle_new (n k : ℕ) (hk : k≤n) :
    projectionShuffle n k hk (Fin.last n)=(⟨k,Nat.lt_succ_of_le hk⟩ : Fin (n+1)) := by
  simp [projectionShuffle]

private theorem shuffle_linear (n k : ℕ) (hk : k≤n) (w : ComplexModel (n+1)) (i : Fin (n+1)) :
    projectionShuffleLinear n k hk w (projectionShuffle n k hk i)=w i := by
  simp [projectionShuffleLinear,LinearIsometryEquiv.piLpCongrLeft_apply,Equiv.piCongrLeft']

-- Exact held generic product coordinate readback, copied with zero engine credit
-- from ActualProjectionTestRecord split_old/product_old/product_last.
private theorem split_old {d : ℕ} (w : ComplexModel (d+1)) (i : Fin d) :
    ((ProductComplexManifold.prodModelEquiv d 1).symm w).1 i=w i.castSucc := rfl

private theorem split_last {d : ℕ} (w : ComplexModel (d+1)) :
    ((ProductComplexManifold.prodModelEquiv d 1).symm w).2 0=w (Fin.last d) := by
  rfl

private theorem join_old {d : ℕ} (a : ComplexModel d) (b : ComplexModel 1) (i : Fin d) :
    ProductComplexManifold.prodModelEquiv d 1 (a,b) i.castSucc=a i := by
  have h:=congrArg (fun z : ComplexModel d×ComplexModel 1=>z.1 i)
    ((ProductComplexManifold.prodModelEquiv d 1).symm_apply_apply (a,b))
  rw [split_old] at h
  exact h

private theorem join_last {d : ℕ} (a : ComplexModel d) (b : ComplexModel 1) :
    ProductComplexManifold.prodModelEquiv d 1 (a,b) (Fin.last d)=b 0 := by
  have h:=congrArg (fun z : ComplexModel d×ComplexModel 1=>z.2 0)
    ((ProductComplexManifold.prodModelEquiv d 1).symm_apply_apply (a,b))
  rw [split_last] at h
  exact h

private theorem shuffle_inclusion (n k : ℕ) (hk : k≤n)
    (v : ComplexModel k) (c : ComplexModel 1) :
    projectionShuffleLinear n k hk
      (ProductComplexManifold.prodModelEquiv n 1 (coordinateInclusion n k v,c))=
    coordinateInclusion (n+1) (k+1) (ProductComplexManifold.prodModelEquiv k 1 (v,c)) := by
  let p : Fin (n+1):=⟨k,Nat.lt_succ_of_le hk⟩
  ext i
  refine Fin.succAboveCases p ?_ (fun j=>?_) i
  · calc
      projectionShuffleLinear n k hk _ p =
          ProductComplexManifold.prodModelEquiv n 1 (coordinateInclusion n k v,c) (Fin.last n) := by
        simpa only [shuffle_new] using shuffle_linear n k hk
          (ProductComplexManifold.prodModelEquiv n 1 (coordinateInclusion n k v,c)) (Fin.last n)
      _ = c 0 := join_last _ _
      _ = coordinateInclusion (n+1) (k+1) (ProductComplexManifold.prodModelEquiv k 1 (v,c)) p := by
        rw [coordinateInclusion_apply,dif_pos (show p.val<k+1 by dsimp [p];omega)]
        exact (join_last v c).symm
  · calc
      projectionShuffleLinear n k hk _ (p.succAbove j)=
          ProductComplexManifold.prodModelEquiv n 1 (coordinateInclusion n k v,c) j.castSucc := by
        simpa only [shuffle_old] using shuffle_linear n k hk
          (ProductComplexManifold.prodModelEquiv n 1 (coordinateInclusion n k v,c)) j.castSucc
      _ = coordinateInclusion n k v j := join_old _ _ _
      _ = coordinateInclusion (n+1) (k+1) (ProductComplexManifold.prodModelEquiv k 1 (v,c)) (p.succAbove j) := by
        by_cases hj : j.val<k
        · have hpj : j.castSucc<p := hj
          rw [Fin.succAbove_of_castSucc_lt _ _ hpj]
          simp only [coordinateInclusion_apply,Fin.val_castSucc]
          rw [dif_pos hj,dif_pos (Nat.lt_succ_of_lt hj)]
          exact (join_old v c (⟨j.val,hj⟩ : Fin k)).symm
        · have hpj : p≤j.castSucc := by change k≤j.val;omega
          rw [Fin.succAbove_of_le_castSucc _ _ hpj]
          simp only [coordinateInclusion_apply,Fin.val_succ]
          rw [dif_neg hj,dif_neg (show ¬j.val+1<k+1 by omega)]

private theorem shuffle_old_lt (n k : ℕ) (hk : k≤n) (i : Fin n) (hi : i.val<k) :
    projectionShuffle n k hk i.castSucc=i.castSucc := by
  rw [shuffle_old]
  exact Fin.succAbove_of_castSucc_lt _ _ hi

private theorem shuffle_old_value (n k : ℕ) (hk : k≤n)
    (a : ComplexModel n) (c : ComplexModel 1) (i : Fin n) (hi : i.val<k) :
    projectionShuffleLinear n k hk (prodModelEquiv n 1 (a,c)) i.castSucc=a i := by
  rw [←shuffle_old_lt n k hk i hi,shuffle_linear,join_old]

private theorem shuffle_horizontal_value (n k : ℕ) (hk : k≤n)
    (a : ComplexModel n) (c : ComplexModel 1) :
    projectionShuffleLinear n k hk (prodModelEquiv n 1 (a,c)) ⟨k,Nat.lt_succ_of_le hk⟩=c 0 := by
  rw [←shuffle_new n k hk,shuffle_linear,join_last]

section SameChartGeometry
variable {n : ℕ} {X : CMfd.{0} n}
open ProductComplexManifold

-- Exact held product chart body, copied privately with zero engine credit.
private def productCoordinates (p : projectionAmbient X)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) p.1 p.1)) :
    LocalHolomorphicEquivAt (n := n+1) (chartAt (ComplexModel (n+1)) p p) where
  source := (fun w => ((prodModelEquiv n 1).symm w).1) ⁻¹' Φ.source
  target := (fun w => ((prodModelEquiv n 1).symm w).1) ⁻¹' Φ.target
  isOpen_source := Φ.isOpen_source.preimage ((prodModelEquiv n 1).symm.continuous.fst)
  isOpen_target := Φ.isOpen_target.preimage ((prodModelEquiv n 1).symm.continuous.fst)
  center_mem_source := by
    simpa only [mem_preimage,chartAt_prod,prodChart_apply,ContinuousLinearEquiv.symm_apply_apply]
      using Φ.center_mem_source
  toFun w := prodModelEquiv n 1
    (Φ.toFun ((prodModelEquiv n 1).symm w).1,((prodModelEquiv n 1).symm w).2-p.2)
  invFun w := prodModelEquiv n 1
    (Φ.invFun ((prodModelEquiv n 1).symm w).1,((prodModelEquiv n 1).symm w).2+p.2)
  toFun_holomorphic := by
    have hfst : Differentiable ℂ (fun w : ComplexModel (n+1) => ((prodModelEquiv n 1).symm w).1) :=
      (ContinuousLinearMap.fst ℂ (ComplexModel n) (ComplexModel 1)).differentiable.comp (prodModelEquiv n 1).symm.differentiable
    have hsnd : Differentiable ℂ (fun w : ComplexModel (n+1) => ((prodModelEquiv n 1).symm w).2) :=
      (ContinuousLinearMap.snd ℂ (ComplexModel n) (ComplexModel 1)).differentiable.comp (prodModelEquiv n 1).symm.differentiable
    exact (prodModelEquiv n 1).differentiable.comp_differentiableOn
      ((Φ.toFun_holomorphic.comp hfst.differentiableOn (fun _ hz => hz)).prodMk
        (hsnd.sub_const p.2).differentiableOn)
  invFun_holomorphic := by
    have hfst : Differentiable ℂ (fun w : ComplexModel (n+1) => ((prodModelEquiv n 1).symm w).1) :=
      (ContinuousLinearMap.fst ℂ (ComplexModel n) (ComplexModel 1)).differentiable.comp (prodModelEquiv n 1).symm.differentiable
    have hsnd : Differentiable ℂ (fun w : ComplexModel (n+1) => ((prodModelEquiv n 1).symm w).2) :=
      (ContinuousLinearMap.snd ℂ (ComplexModel n) (ComplexModel 1)).differentiable.comp (prodModelEquiv n 1).symm.differentiable
    exact (prodModelEquiv n 1).differentiable.comp_differentiableOn
      ((Φ.invFun_holomorphic.comp hfst.differentiableOn (fun _ hz => hz)).prodMk
        (hsnd.add_const p.2).differentiableOn)
  mapsTo_toFun := by intro w hw; simpa only [mem_preimage,ContinuousLinearEquiv.symm_apply_apply] using Φ.mapsTo_toFun hw
  mapsTo_invFun := by intro w hw; simpa only [mem_preimage,ContinuousLinearEquiv.symm_apply_apply] using Φ.mapsTo_invFun hw
  left_inv := by
    intro w hw
    simp only [ContinuousLinearEquiv.symm_apply_apply,Φ.left_inv _ hw,sub_add_cancel,Prod.mk.eta]
    exact (prodModelEquiv n 1).apply_symm_apply w
  right_inv := by
    intro w hw
    simp only [ContinuousLinearEquiv.symm_apply_apply,Φ.right_inv _ hw,add_sub_cancel_right,Prod.mk.eta]
    exact (prodModelEquiv n 1).apply_symm_apply w


variable {x : X} (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
  (k : ℕ) (hk : k≤n)

private def shiftedProductChart : LocalHolomorphicEquivAt (n:=n+1)
    (chartAt (ComplexModel (n+1)) ((x,0) : projectionAmbient X) (x,0)) :=
  postcomposeLinear (productCoordinates ((x,0) : projectionAmbient X) Φ)
    (projectionShuffleLinear n k hk)

private theorem shuffle_inverse_inclusion (w : ComplexModel (k+1)) :
    (projectionShuffleLinear n k hk).symm (coordinateInclusion (n+1) (k+1) w)=
      prodModelEquiv n 1
        (coordinateInclusion n k ((prodModelEquiv k 1).symm w).1,
          ((prodModelEquiv k 1).symm w).2) := by
  apply (projectionShuffleLinear n k hk).injective
  rw [ContinuousLinearEquiv.apply_symm_apply,shuffle_inclusion,
    ContinuousLinearEquiv.apply_symm_apply]

private theorem shuffle_plane (a : ComplexModel n) (c : ComplexModel 1) :
    projectionShuffleLinear n k hk (prodModelEquiv n 1 (a,c))∈
      complexCoordinatePlane (n+1) (k+1) ↔ a∈complexCoordinatePlane n k := by
  constructor
  · intro h
    have he := coordinateInclusion_coordinateProjection h
    have hh := congrArg (fun w => ((prodModelEquiv n 1).symm
      ((projectionShuffleLinear n k hk).symm w)).1) he
    rw [shuffle_inverse_inclusion,ContinuousLinearEquiv.symm_apply_apply,
      ContinuousLinearEquiv.symm_apply_apply] at hh
    simp only [ContinuousLinearEquiv.symm_apply_apply] at hh
    rw [←hh]
    exact coordinateInclusion_mem_complexCoordinatePlane _
  · intro h
    have he := coordinateInclusion_coordinateProjection h
    rw [←he,shuffle_inclusion]
    exact coordinateInclusion_mem_complexCoordinatePlane _

private theorem shifted_flatDomain (p : projectionAmbient X) :
    p∈flatDomain (M:=projectionAmbient X) (shiftedProductChart Φ k hk) ↔ p.1∈flatDomain Φ := by
  simp only [flatDomain,shiftedProductChart,postcomposeLinear,productCoordinates,
    chartAt_prod,prodChart_source,prodChart_apply,mem_inter_iff,mem_preimage,
    ContinuousLinearEquiv.symm_apply_apply,Set.mem_prod,chartAt_self_eq,
    OpenPartialHomeomorph.refl_source,Set.mem_univ,and_true]

private theorem shifted_flatMap (p : projectionAmbient X) :
    flatMap (M:=projectionAmbient X) (shiftedProductChart Φ k hk) p=
      projectionShuffleLinear n k hk (prodModelEquiv n 1 (flatMap Φ p.1,p.2)) := by
  simp only [flatMap,shiftedProductChart,postcomposeLinear,productCoordinates,
    chartAt_prod,prodChart_apply,ContinuousLinearEquiv.symm_apply_apply,
    chartAt_self_eq,OpenPartialHomeomorph.refl_apply,id_eq,sub_zero]

private theorem shifted_parameter_mem (w : ComplexModel (k+1)) :
    w∈parameterOpen (X:=projectionAmbient X) (shiftedProductChart Φ k hk) (k+1) ↔
      ((prodModelEquiv k 1).symm w).1∈parameterOpen Φ k := by
  change ((prodModelEquiv n 1).symm
    ((projectionShuffleLinear n k hk).symm (coordinateInclusion (n+1) (k+1) w))).1∈Φ.target ↔ _
  rw [shuffle_inverse_inclusion,ContinuousLinearEquiv.symm_apply_apply]
  rfl

private theorem shifted_source (hsrc : Φ.source⊆(chartAt (ComplexModel n) x).target) :
    (shiftedProductChart Φ k hk).source⊆
      (chartAt (ComplexModel (n+1)) ((x,0) : projectionAmbient X)).target := by
  intro w hw
  change w∈(prodChart (chartAt (ComplexModel n) x) (chartAt (ComplexModel 1) (0 : ComplexModel 1))).target
  rw [prodChart_target]
  exact ⟨hsrc hw,Set.mem_univ _⟩

private theorem shifted_centred (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0) :
    (shiftedProductChart Φ k hk).toFun
      (chartAt (ComplexModel (n+1)) ((x,0) : projectionAmbient X) (x,0))=0 := by
  change projectionShuffleLinear n k hk (prodModelEquiv n 1
    (Φ.toFun ((prodModelEquiv n 1).symm
      (chartAt (ComplexModel (n+1)) ((x,0) : projectionAmbient X) (x,0))).1,
      ((prodModelEquiv n 1).symm
        (chartAt (ComplexModel (n+1)) ((x,0) : projectionAmbient X) (x,0))).2-0))=0
  simp only [chartAt_prod,prodChart_apply,ContinuousLinearEquiv.symm_apply_apply,
    chartAt_self_eq,OpenPartialHomeomorph.refl_apply,id_eq,h0,sub_self]
  change projectionShuffleLinear n k hk (prodModelEquiv n 1 0)=0
  simp only [map_zero]

private def sameParameterRho : parameterOpen (X:=projectionAmbient X) (shiftedProductChart Φ k hk) (k+1)
    ≃ₘ⟮𝓘(ℂ,ComplexModel (k+1)),𝓘(ℂ,ComplexModel (k+1))⟯
      projectionAmbient (CMfd.of (n:=k) (parameterOpen Φ k)) where
  toFun w := (⟨((prodModelEquiv k 1).symm w.val).1,(shifted_parameter_mem Φ k hk w.val).mp w.property⟩,
    ((prodModelEquiv k 1).symm w.val).2)
  invFun t := ⟨prodModelEquiv k 1 (t.1.val,t.2),(shifted_parameter_mem Φ k hk _).mpr
    (by simpa only [ContinuousLinearEquiv.symm_apply_apply] using t.1.property)⟩
  left_inv w := Subtype.ext ((prodModelEquiv k 1).apply_symm_apply w.val)
  right_inv t := by
    dsimp only
    simp only [ContinuousLinearEquiv.symm_apply_apply]
  contMDiff_toFun := by
    apply ProductComplexManifold.contMDiff_prodMk
    · apply (ContMDiff.subtypeVal_comp_iff (parameterOpen Φ k) _).mp
      exact ((ContinuousLinearMap.fst ℂ (ComplexModel k) (ComplexModel 1)).contDiff.contMDiff.comp
        (prodModelEquiv k 1).symm.contDiff.contMDiff).comp contMDiff_subtype_val
    · exact ((ContinuousLinearMap.snd ℂ (ComplexModel k) (ComplexModel 1)).contDiff.contMDiff.comp
        (prodModelEquiv k 1).symm.contDiff.contMDiff).comp contMDiff_subtype_val
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff (parameterOpen (X:=projectionAmbient X) (shiftedProductChart Φ k hk) (k+1)) _).mp
    have hjoin : ContMDiff 𝓘(ℂ,ComplexModel (k+1)) 𝓘(ℂ,ComplexModel (k+1)) ∞
        (prodModelEquiv k 1 : ComplexModel k×ComplexModel 1→ComplexModel (k+1)) := by
      intro z
      have h := (contMDiffOn_chart (I:=𝓘(ℂ,ComplexModel (k+1))) (n:=∞)
        (x:=((0,0) : ComplexModel k×ComplexModel 1))).contMDiffAt (x:=z)
          (by simp [chartAt_prod,prodChart_source,chartAt_self_eq])
      have heq : (chartAt (ComplexModel (k+1)) ((0,0) : ComplexModel k×ComplexModel 1) :
          ComplexModel k×ComplexModel 1 → ComplexModel (k+1)) = prodModelEquiv k 1 := by
        funext y
        simp only [chartAt_prod,prodChart_apply,chartAt_self_eq,
          OpenPartialHomeomorph.refl_apply,id_eq]
      rw [heq] at h
      exact h
    exact hjoin.comp
      (ProductComplexManifold.contMDiff_prodMk
        (contMDiff_subtype_val.comp ProductComplexManifold.contMDiff_fst)
        ProductComplexManifold.contMDiff_snd)

private theorem shifted_parameterMap (w : parameterOpen (X:=projectionAmbient X)
    (shiftedProductChart Φ k hk) (k+1)) :
    parameterMapOn (X:=projectionAmbient X) (shiftedProductChart Φ k hk) (k+1) w =
      (parameterMapOn Φ k (sameParameterRho Φ k hk w).1,
        (sameParameterRho Φ k hk w).2) := by
  change (chartAt (ComplexModel (n+1)) ((x,0) : projectionAmbient X)).symm
    (prodModelEquiv n 1
      (Φ.invFun ((prodModelEquiv n 1).symm
        ((projectionShuffleLinear n k hk).symm (coordinateInclusion (n+1) (k+1) w.val))).1,
        ((prodModelEquiv n 1).symm
          ((projectionShuffleLinear n k hk).symm (coordinateInclusion (n+1) (k+1) w.val))).2+0)) = _
  rw [shuffle_inverse_inclusion]
  simp only [ContinuousLinearEquiv.symm_apply_apply,add_zero,chartAt_prod,
    prodChart_symm_apply,chartAt_self_eq,OpenPartialHomeomorph.refl_symm,
    OpenPartialHomeomorph.refl_apply,id_eq]
  rfl

end SameChartGeometry

section Fixed
variable {n : ℕ} {X : CMfd.{0} n} {A : GermIdeal n X} {N : Set X}
  {E : List (Set X)} {x : X} (F : OriginalLogFrame A N E x)

abbrev parameterProduct := projectionAmbient (CMfd.of (n:=F.k) (parameterOpen F.Φ F.k))
def productParameterMap : parameterProduct F→projectionAmbient X :=
  fun t=>(parameterMapOn F.Φ F.k t.1,t.2)
def productParameterRetraction (t : parameterProduct F) :
    projectionAmbient X→parameterProduct F :=
  fun p=>(actualParameterRetraction F.Φ F.k t.1 p.1,p.2)
def projectedBoundary (_F : OriginalLogFrame A N E x) : List (Set (projectionAmbient X)) :=
  E.map ((Prod.fst : projectionAmbient X→X) ⁻¹' ·) ++ [horizontal X]

def projectedAmbientSlot : Fin (E.length+1)→Option (Fin (n+1)) :=
  Fin.lastCases (some ⟨F.k,Nat.lt_succ_of_le F.hk⟩)
    (fun i=>Option.map Fin.castSucc (F.κ i))
def projectedParameterSlot : Fin (E.length+1)→Option (Fin (F.k+1)) :=
  Fin.lastCases (some (Fin.last F.k)) (fun i=>Option.map Fin.castSucc (F.τ i))

structure ProjectionParameterData where
  Ψ : LocalHolomorphicEquivAt (n:=n+1)
    (chartAt (ComplexModel (n+1)) ((x,0) : projectionAmbient X) (x,0))
  hsrc : Ψ.source⊆(chartAt (ComplexModel (n+1)) ((x,0) : projectionAmbient X)).target
  centred : Ψ.toFun (chartAt (ComplexModel (n+1)) ((x,0) : projectionAmbient X) (x,0))=0
  source : Ψ.source=(fun w=>((ProductComplexManifold.prodModelEquiv n 1).symm w).1) ⁻¹' F.Φ.source
  target : ∀ w,w∈Ψ.target ↔
    ((ProductComplexManifold.prodModelEquiv n 1).symm
      ((projectionShuffleLinear n F.k F.hk).symm w)).1∈F.Φ.target
  forward : ∀ w,Ψ.toFun w=projectionShuffleLinear n F.k F.hk
    (ProductComplexManifold.prodModelEquiv n 1
      (F.Φ.toFun ((ProductComplexManifold.prodModelEquiv n 1).symm w).1,
        ((ProductComplexManifold.prodModelEquiv n 1).symm w).2))
  inverse : ∀ w,Ψ.invFun w=ProductComplexManifold.prodModelEquiv n 1
    (F.Φ.invFun ((ProductComplexManifold.prodModelEquiv n 1).symm
      ((projectionShuffleLinear n F.k F.hk).symm w)).1,
      ((ProductComplexManifold.prodModelEquiv n 1).symm
        ((projectionShuffleLinear n F.k F.hk).symm w)).2)
  shuffle : ∀ (v : ComplexModel F.k) (c : ComplexModel 1),
    projectionShuffleLinear n F.k F.hk
      (ProductComplexManifold.prodModelEquiv n 1 (coordinateInclusion n F.k v,c))=
    coordinateInclusion (n+1) (F.k+1) (ProductComplexManifold.prodModelEquiv F.k 1 (v,c))
  rho : parameterOpen (X:=projectionAmbient X) Ψ (F.k+1) ≃ₘ⟮𝓘(ℂ,ComplexModel (F.k+1)),𝓘(ℂ,ComplexModel (F.k+1))⟯
    parameterProduct F
  rho_value : ∀ w,ProductComplexManifold.prodModelEquiv F.k 1 ((rho w).1.val,(rho w).2)=w.val
  rho_inverse : ∀ t,(rho.symm t).val=ProductComplexManifold.prodModelEquiv F.k 1 (t.1.val,t.2)
  sigma : ∀ w,parameterMapOn (X:=projectionAmbient X) Ψ (F.k+1) w=productParameterMap F (rho w)
  sigma_holo : ContMDiff 𝓘(ℂ,ComplexModel (F.k+1)) 𝓘(ℂ,ComplexModel (n+1)) ∞ (productParameterMap F)
  native_sigma : ChartedSpace.locallyRingedSpaceMap (parameterMapOn (X:=projectionAmbient X) Ψ (F.k+1))
      (parameterMapOn_contMDiff (X:=projectionAmbient X) Ψ (F.k+1) hsrc)=
    ChartedSpace.locallyRingedSpaceMap rho rho.contMDiff ≫
      ChartedSpace.locallyRingedSpaceMap (productParameterMap F) sigma_holo
  native_projection : ChartedSpace.locallyRingedSpaceMap (productParameterMap F) sigma_holo ≫
      ChartedSpace.locallyRingedSpaceMap (Prod.fst : projectionAmbient X→X) ProductComplexManifold.contMDiff_fst=
    ChartedSpace.locallyRingedSpaceMap (Prod.fst : parameterProduct F→parameterOpen F.Φ F.k)
      ProductComplexManifold.contMDiff_fst ≫
      ChartedSpace.locallyRingedSpaceMap (parameterMapOn F.Φ F.k)
        (parameterMapOn_contMDiff F.Φ F.k F.hsrc)
  rho_all_native_germs : ∀ w (r : actualComplexStructureStalk (n:=F.k+1) (rho w)),
    actualStalkChartEquiv (n:=F.k+1) w
      ((ChartedSpace.locallyRingedSpaceMap rho rho.contMDiff).stalkMap w r)=
    actualStalkChartEquiv (n:=F.k+1) (rho w) r
  carrier_chart : ∀ p∈flatDomain Ψ,
    p∈(Prod.fst : projectionAmbient X→X) ⁻¹' N ↔
      flatMap Ψ p∈complexCoordinatePlane (n+1) (F.k+1)
  boundary_chart : ∀ p∈flatDomain Ψ,∀ i : Fin (E.length+1),
    p∈(projectedBoundary F).get (Fin.cast (by simp [projectedBoundary]) i) ↔
      ∃ j,projectedAmbientSlot F i=some j ∧ flatCoord Ψ j p=0
  parameter_boundary : ∀ w : parameterOpen (X:=projectionAmbient X) Ψ (F.k+1),∀ i : Fin (E.length+1),
    parameterMapOn (X:=projectionAmbient X) Ψ (F.k+1) w∈(projectedBoundary F).get (Fin.cast (by simp [projectedBoundary]) i) ↔
      ∃ j,projectedParameterSlot F i=some j ∧ w.val j=0
  horizontal_weight : ∀ w : parameterOpen (X:=projectionAmbient X) Ψ (F.k+1),
    parameterWeight (X:=projectionAmbient X) Ψ (F.k+1) (projectedAmbientSlot F) (Nat.succ_le_succ F.hk) w (Fin.last F.k)=
      HolGerm.constHom ((rho w).2 0)+coordinateGerm (Fin.last F.k)
  all_weights : ∀ w : parameterOpen (X:=projectionAmbient X) Ψ (F.k+1),
    parameterWeight (X:=projectionAmbient X) Ψ (F.k+1) (projectedAmbientSlot F) (Nat.succ_le_succ F.hk) w=
      HironakaActualProjectionLogDerivativeIdeal.projectionWeight
        (parameterWeight F.Φ F.k F.κ F.hk (rho w).1) ((rho w).2 0)
  product_carrier : IsClosedSubmanifold (n+1) ((Prod.fst : projectionAmbient X→X) ⁻¹' N)
  product_snc : IsSNCDivisor (n+1) (projectedBoundary F)
  product_transverse : IsTransverse (n+1) ((Prod.fst : projectionAmbient X→X) ⁻¹' N) (projectedBoundary F)
  image : ∀ t,productParameterMap F t∈(Prod.fst : projectionAmbient X→X) ⁻¹' N
  retraction_holo : ∀ t,∀ᶠ p in 𝓝 (productParameterMap F t),MDifferentiableAt
    𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel (F.k+1)) (productParameterRetraction F t) p
  retraction_point : ∀ t,productParameterRetraction F t (productParameterMap F t)=t
  «section» : ∀ t w,productParameterRetraction F t (productParameterMap F w)=w
  roundtrip : ∀ t,∀ᶠ p in 𝓝 (productParameterMap F t),p∈(Prod.fst : projectionAmbient X→X) ⁻¹' N→
    productParameterMap F (productParameterRetraction F t p)=p

end Fixed

-- Generic algebra packaging only; all maps are fixed independently before the output.
structure NativeQuotientDiagram {R R' S S' : Type*}
    [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
    (alpha : R→+*S) (alpha' : R'→+*S') (f : R→+*R') (g : S→+*S')
    (K : Ideal R) (K' : Ideal R') where
  surjective : Function.Surjective alpha
  surjective' : Function.Surjective alpha'
  kernel : RingHom.ker alpha=K
  kernel' : RingHom.ker alpha'=K'
  ideal_map : Ideal.map f K=K'
  square : alpha'.comp f=g.comp alpha
  e : (R⧸K)≃+*S
  e' : (R'⧸K')≃+*S'
  e_mk : ∀ r,e (Ideal.Quotient.mk K r)=alpha r
  e'_mk : ∀ r,e' (Ideal.Quotient.mk K' r)=alpha' r
  e_action : ∀ r q,e (Ideal.Quotient.mk K r*q)=alpha r*e q
  e'_action : ∀ r q,e' (Ideal.Quotient.mk K' r*q)=alpha' r*e' q
  quotient_map : (R⧸K)→+*(R'⧸K')
  quotient_map_mk : ∀ r,quotient_map (Ideal.Quotient.mk K r)=Ideal.Quotient.mk K' (f r)
  quotient_square : ∀ q,e' (quotient_map q)=g (e q)


structure NativeScalarLaws {a b : ℕ} {M P : Type}
    [TopologicalSpace M] [TopologicalSpace P]
    [ChartedSpace (ComplexModel a) M] [IsComplexManifold a M]
    [ChartedSpace (ComplexModel b) P] [IsComplexManifold b P]
    (f : P→M) (hf : ContMDiff 𝓘(ℂ,ComplexModel b) 𝓘(ℂ,ComplexModel a) ∞ f) : Prop where
  triangle : ChartedSpace.locallyRingedSpaceMap f hf ≫ ambientPointMap a M=ambientPointMap b P
  all_scalars : ∀ p (s : actualComplexStructureStalk (n:=0) (0 : ComplexModel 0)),
    (ChartedSpace.locallyRingedSpaceMap f hf).stalkMap p
      ((ambientPointMap a M).stalkMap (f p) s)=(ambientPointMap b P).stalkMap p s

section FixedOutput
variable {n : ℕ} {X : CMfd.{0} n} {A : GermIdeal n X} {N : Set X}
  {E : List (Set X)} {x : X} (F : OriginalLogFrame A N E x)

private def sourceNative (t : parameterProduct F) := parameterStalkMap F.Φ F.k F.hsrc t.1
private def productNative (G : ProjectionParameterData F) (t : parameterProduct F) :
    actualComplexStructureStalk (n:=n+1) (productParameterMap F t) →+*
      actualComplexStructureStalk (n:=F.k+1) t :=
  ((ChartedSpace.locallyRingedSpaceMap (productParameterMap F) G.sigma_holo).stalkMap t).hom
private def ambientNative (t : parameterProduct F) :
    actualComplexStructureStalk (n:=n) (parameterMapOn F.Φ F.k t.1) →+*
      actualComplexStructureStalk (n:=n+1) (productParameterMap F t) :=
  ((ChartedSpace.locallyRingedSpaceMap (Prod.fst : projectionAmbient X→X)
    (ProductComplexManifold.contMDiff_fst (n:=n) (m:=1))).stalkMap (productParameterMap F t)).hom
private def parameterNative (t : parameterProduct F) :
    actualComplexStructureStalk (n:=F.k) t.1 →+*
      actualComplexStructureStalk (n:=F.k+1) t :=
  ((ChartedSpace.locallyRingedSpaceMap (Prod.fst : parameterProduct F→parameterOpen F.Φ F.k)
    (ProductComplexManifold.contMDiff_fst (n:=F.k) (m:=1))).stalkMap t).hom
private def productGerm (G : ProjectionParameterData F) (t : parameterProduct F) :
    actualComplexStructureStalk (n:=n+1) (M:=projectionAmbient X) (productParameterMap F t) →+*
      HolGerm (ComplexModel (F.k+1)) :=
  (actualStalkChartEquiv (n:=F.k+1) t).toRingHom.comp (productNative F G t)
private def sourceGerm (t : parameterProduct F) :
    actualComplexStructureStalk (n:=n) (M:=X) (parameterMapOn F.Φ F.k t.1) →+*
      HolGerm (ComplexModel F.k) := parameterGermPullback F.Φ F.k F.hsrc t.1
private def coordinateQuotient (J : Ideal (HolGerm (ComplexModel F.k))) :=
  Ideal.quotientMap (Ideal.map (HironakaRelativeNormalIdeal.tangentPullback F.k 1).toRingHom J)
    (HironakaRelativeNormalIdeal.tangentPullback F.k 1).toRingHom Ideal.le_comap_map
private abbrev pulled (_F : OriginalLogFrame A N E x) (B : GermIdeal n X) := GermIdeal.pullback (m:=n+1)
  (Prod.fst : projectionAmbient X→X) B
private abbrev nativeIdeal (B : GermIdeal n X) (t : parameterProduct F) :=
  actualWholeSheafStalkIdeal B (parameterMapOn F.Φ F.k t.1)
private abbrev nativeIdealPlus (B : GermIdeal n X) (t : parameterProduct F) :=
  actualWholeSheafStalkIdeal (pulled F B) (productParameterMap F t)
private def stalkTransport {d : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsComplexManifold d M]
    {p q : M} (h : p=q) :
    actualComplexStructureStalk (n:=d) p≃+*actualComplexStructureStalk (n:=d) q :=
  h ▸ RingEquiv.refl _

abbrev CoherentProjectionQuotient (G : ProjectionParameterData F) (t : parameterProduct F)
    (B : GermIdeal n X) : Type :=
  NativeQuotientDiagram
    ((Ideal.Quotient.mk (Ideal.map (sourceGerm F t) (nativeIdeal F B t))).comp (sourceGerm F t))
    ((Ideal.Quotient.mk (Ideal.map (HironakaRelativeNormalIdeal.tangentPullback F.k 1).toRingHom
      (Ideal.map (sourceGerm F t) (nativeIdeal F B t)))).comp (productGerm F G t))
    (ambientNative F t) (coordinateQuotient F (Ideal.map (sourceGerm F t) (nativeIdeal F B t)))
    (nativeIdeal F B t) (nativeIdealPlus F B t)

private abbrev oldLogTargetIdeal (t : parameterProduct F) : Ideal (HolGerm (ComplexModel F.k)) :=
  logIdeal (parameterWeight F.Φ F.k F.κ F.hk t.1)
    (Ideal.map (sourceGerm F t) (nativeIdeal F A t))

abbrev OriginalLogProjectionQuotient (G : ProjectionParameterData F) (t : parameterProduct F) : Type :=
  let D0:=logDerivIdealAlong N E A
  let L:=oldLogTargetIdeal F t
  NativeQuotientDiagram ((Ideal.Quotient.mk L).comp (sourceGerm F t))
    ((Ideal.Quotient.mk (Ideal.map (HironakaRelativeNormalIdeal.tangentPullback F.k 1).toRingHom L)).comp
      (productGerm F G t))
    (ambientNative F t) (coordinateQuotient F L)
    (nativeIdeal F D0 t) (nativeIdealPlus F D0 t)

private abbrev outputField_carrier (G : ProjectionParameterData F) : Type :=
  ∀ t : parameterProduct F,
    NativeQuotientDiagram (sourceNative F t) (productNative F G t)
      (ambientNative F t) (parameterNative F t)
      (nativeIdeal F (vanishingIdeal (n:=n) N) t)
      (actualWholeSheafStalkIdeal (vanishingIdeal (n:=n+1)
        ((Prod.fst : projectionAmbient X→X) ⁻¹' N)) (productParameterMap F t))

private abbrev outputField_all_germs (G : ProjectionParameterData F) : Prop :=
  ∀ (t : parameterProduct F) (r : actualComplexStructureStalk (n:=n) (parameterMapOn F.Φ F.k t.1)),
    productGerm F G t (ambientNative F t r)=
      HironakaRelativeNormalIdeal.tangentPullback F.k 1 (sourceGerm F t r)

private abbrev outputField_factory_all_germs (G : ProjectionParameterData F) : Prop :=
  ∀ w (r : actualComplexStructureStalk (n:=n+1)
      (productParameterMap F (G.rho w))),
    parameterGermPullback (X:=projectionAmbient X) G.Ψ (F.k+1) G.hsrc w
      (stalkTransport (G.sigma w).symm r)=productGerm F G (G.rho w) r

private abbrev outputField_every_coherent_ideal (G : ProjectionParameterData F) : Prop :=
  ∀ (B : GermIdeal n X),B.IsCoherent→∀ t,
    Ideal.map (ambientNative F t) (nativeIdeal F B t)=nativeIdealPlus F B t ∧
    Ideal.map (productGerm F G t) (nativeIdealPlus F B t)=
      Ideal.map (HironakaRelativeNormalIdeal.tangentPullback F.k 1).toRingHom
        (Ideal.map (sourceGerm F t) (nativeIdeal F B t)) ∧
    ((vanishingIdeal (n:=n) N).Le B→Nonempty (CoherentProjectionQuotient F G t B))

private def originalLogQuotientEquiv (G : ProjectionParameterData F) (t : parameterProduct F)
    (Q : OriginalLogProjectionQuotient F G t) :
    (actualComplexStructureStalk (n:=n) (parameterMapOn F.Φ F.k t.1) ⧸
      nativeIdeal F (logDerivIdealAlong N E A) t) ≃+*
    (HolGerm (ComplexModel F.k) ⧸ logIdeal (parameterWeight F.Φ F.k F.κ F.hk t.1)
      (Ideal.map (sourceGerm F t) (nativeIdeal F A t))) := Q.e

private abbrev outputField_retained_original_log (G : ProjectionParameterData F) : Prop :=
  ∀ (t : parameterProduct F)
    (eOld : (actualComplexStructureStalk (n:=n) (M:=X) (parameterMapOn F.Φ F.k t.1) ⧸
      nativeIdeal F (logDerivIdealAlong N E A) t) ≃+*
      (HolGerm (ComplexModel F.k) ⧸ oldLogTargetIdeal F t)),
    (∀ (r : actualComplexStructureStalk (n:=n) (M:=X) (parameterMapOn F.Φ F.k t.1)),
      eOld (Ideal.Quotient.mk (nativeIdeal F (logDerivIdealAlong N E A) t) r)=
        Ideal.Quotient.mk (oldLogTargetIdeal F t) (sourceGerm F t r)) →
    ∃ Q : OriginalLogProjectionQuotient F G t,originalLogQuotientEquiv F G t Q=eOld

private abbrev outputField_source_scalar (_G : ProjectionParameterData F) : Prop :=
  NativeScalarLaws (parameterMapOn F.Φ F.k) (parameterMapOn_contMDiff F.Φ F.k F.hsrc)

private abbrev outputField_product_scalar (G : ProjectionParameterData F) : Prop :=
  NativeScalarLaws (productParameterMap F) G.sigma_holo

private abbrev outputField_ambient_scalar (_G : ProjectionParameterData F) : Prop :=
  NativeScalarLaws (Prod.fst : projectionAmbient X→X) (ProductComplexManifold.contMDiff_fst (n:=n) (m:=1))

private abbrev outputField_parameter_scalar (_G : ProjectionParameterData F) : Prop :=
  NativeScalarLaws (Prod.fst : parameterProduct F→parameterOpen F.Φ F.k)
    (ProductComplexManifold.contMDiff_fst (n:=F.k) (m:=1))

private abbrev outputField_factory_scalar (G : ProjectionParameterData F) : Prop :=
  NativeScalarLaws (parameterMapOn (X:=projectionAmbient X) G.Ψ (F.k+1))
    (parameterMapOn_contMDiff (X:=projectionAmbient X) G.Ψ (F.k+1) G.hsrc)

private abbrev outputField_rho_scalar (G : ProjectionParameterData F) : Prop :=
  NativeScalarLaws G.rho G.rho.contMDiff

private abbrev outputField_rho_inverse_scalar (G : ProjectionParameterData F) : Prop :=
  NativeScalarLaws G.rho.symm G.rho.symm.contMDiff

private abbrev outputField_projection_records (_G : ProjectionParameterData F) : Prop :=
  ∀ (M : MarkedIdeal n X) (_hN : M.N=N) (hE : M.E=E) (_hA : M.ideal=A),
    (projectionTest M).N=(Prod.fst : projectionAmbient X→X) ⁻¹' N ∧
    (projectionTest M).E=projectedBoundary F ∧
    (projectionTest M).ideal=pulled F A ∧ (projectionTest M).d=M.d ∧
    (projectionTest M).E.length=E.length+1 ∧
    (∀ i : Fin E.length,(projectionTest M).E[i.val]'(by change i.val < (M.E.map ((Prod.fst : projectionAmbient X→X) ⁻¹' ·) ++ [horizontal X]).length; simp only [List.length_append,List.length_map,List.length_singleton,hE]; omega)=
      (Prod.fst : projectionAmbient X→X) ⁻¹' E.get i) ∧
    (projectionTest M).E.getLastD ∅=horizontal X ∧
    ∀ s,IsInvDomain s M→IsInvDomain (s+1) (projectionTest M)

structure ProjectionCarrierQuotientOutput where
  geometry : ProjectionParameterData F
  carrier : outputField_carrier F geometry
  all_germs : outputField_all_germs F geometry
  factory_all_germs : outputField_factory_all_germs F geometry
  every_coherent_ideal : outputField_every_coherent_ideal F geometry
  retained_original_log : outputField_retained_original_log F geometry
  source_scalar : outputField_source_scalar F geometry
  product_scalar : outputField_product_scalar F geometry
  ambient_scalar : outputField_ambient_scalar F geometry
  parameter_scalar : outputField_parameter_scalar F geometry
  factory_scalar : outputField_factory_scalar F geometry
  rho_scalar : outputField_rho_scalar F geometry
  rho_inverse_scalar : outputField_rho_inverse_scalar F geometry
  projection_records : outputField_projection_records F geometry

end FixedOutput

private theorem nativeScalarLaws {a b : ℕ} {M P : Type}
    [TopologicalSpace M] [TopologicalSpace P]
    [ChartedSpace (ComplexModel a) M] [IsComplexManifold a M]
    [ChartedSpace (ComplexModel b) P] [IsComplexManifold b P]
    (f : P→M) (hf : ContMDiff 𝓘(ℂ,ComplexModel b) 𝓘(ℂ,ComplexModel a) ∞ f) :
    NativeScalarLaws f hf := by
  have htriangle : ChartedSpace.locallyRingedSpaceMap f hf ≫ ambientPointMap a M =
      ambientPointMap b P :=
    (ChartedSpace.locallyRingedSpace_comp 𝓘(ℂ,ComplexModel 0) hf
      (contMDiff_const : ContMDiff 𝓘(ℂ,ComplexModel a) 𝓘(ℂ,ComplexModel 0) ∞
        (fun _ : M => (0 : ComplexModel 0)))).symm
  refine ⟨htriangle,?_⟩
  intro p r
  obtain ⟨c,rfl⟩ := actualComplexPointStalkEquiv.symm.surjective r
  apply (actualStalkChartEquiv (n:=b) (M:=P) p).injective
  rw [actualNativeStalk_chart_pullback,
    actual_ambient_structural_constant_chart,actual_ambient_structural_constant_chart]
  exact (actualHolomorphicGermPullback hf p).commutes c

-- Pointwise summed-dimension product adapter; follows the held global product chart proof.
private theorem mdifferentiableAt_product {a b d : ℕ} {M P Z : Type}
    [TopologicalSpace M] [TopologicalSpace P] [TopologicalSpace Z]
    [ChartedSpace (ComplexModel a) M] [IsComplexManifold a M]
    [ChartedSpace (ComplexModel b) P] [IsComplexManifold b P]
    [ChartedSpace (ComplexModel d) Z] [IsComplexManifold d Z]
    {f : Z→M} {g : Z→P} {z : Z}
    (hf : MDifferentiableAt 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel a) f z)
    (hg : MDifferentiableAt 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel b) g z) :
    MDifferentiableAt 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel (a+b)) (fun w=>(f w,g w)) z := by
  rw [mdifferentiableAt_iff] at hf hg ⊢
  refine ⟨hf.1.prodMk hg.1,?_⟩
  have h := (prodModelEquiv a b).differentiableAt.comp_differentiableWithinAt
    ((extChartAt 𝓘(ℂ,ComplexModel d) z) z) (hf.2.prodMk hg.2)
  convert h using 1
  simp [writtenInExtChartAt,extChartAt,OpenPartialHomeomorph.extend,Function.comp_def]

-- Provenance: exact private representative/local-retraction engines from accepted824,
-- HironakaActualIntrinsicLogQuotientDictionary.lean lines27–77,178–232.
-- Recompiled here under new private names; no imported private references or engine credit.
section NativeRetractionEngines
variable {n m : ℕ} {M P : Type} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel m) P] [IsComplexManifold m P]

private theorem exists_original_stalk_function (p : M)
    (r : actualComplexStructureStalk (n := n) p) :
    ∃ (g : M → ℂ) (hg : HolomorphicAt n g p), actualOriginalFunctionGerm p g hg = r := by
  obtain ⟨U,hp,s,rfl⟩ := (actualComplexStructureSheaf (n := n) M).presheaf.exists_germ_eq r
  refine ⟨sectionExtension U s,sectionExtension_holomorphicAt U s p hp,?_⟩
  exact actualOriginalFunctionGerm_eq_section U p hp s _ _ (Eventually.of_forall fun _ => rfl)

private theorem original_stalk_function_congr (p : M) {g h : M → ℂ}
    (hg : HolomorphicAt n g p) (hh : HolomorphicAt n h p) (he : g =ᶠ[𝓝 p] h) :
    actualOriginalFunctionGerm p g hg = actualOriginalFunctionGerm p h hh := by
  apply (actualStalkChartEquiv (n := n) p).injective
  rw [actualOriginalFunctionGerm_chart,actualOriginalFunctionGerm_chart]
  exact chartTranslatedGerm_congr_original p g h hg hh he

private theorem original_stalk_zero (p : M) :
    actualOriginalFunctionGerm p (fun _ => (0 : ℂ)) (holomorphicAt_const (n := n) 0) = 0 := by
  apply (actualStalkChartEquiv (n := n) p).injective
  rw [actualOriginalFunctionGerm_chart,map_zero]
  rfl

private theorem original_stalk_zero_iff (p : M) {g : M → ℂ} (hg : HolomorphicAt n g p) :
    actualOriginalFunctionGerm p g hg = 0 ↔ g =ᶠ[𝓝 p] fun _ => 0 := by
  constructor
  · intro hz
    have h := congrArg (actualStalkChartEquiv (n := n) p)
      (hz.trans (original_stalk_zero p).symm)
    rw [actualOriginalFunctionGerm_chart,actualOriginalFunctionGerm_chart] at h
    apply original_eventuallyEq_of_preferred_chart_eventuallyEq (n := n) p g (fun _ => 0)
    apply (HolGerm.mk_eq_mk_iff
      (hf := translated_holomorphic (chartAt (ComplexModel n) p p)
        (CartanLocalReduction.holAt_comp_chart_symm (mem_chart_source (ComplexModel n) p) hg))
      (hg := translated_holomorphic (chartAt (ComplexModel n) p p)
        (CartanLocalReduction.holAt_comp_chart_symm (mem_chart_source (ComplexModel n) p)
          (holomorphicAt_const (n := n) 0)))).mp
    exact h
  · intro he
    exact (original_stalk_function_congr p hg (holomorphicAt_const 0) he).trans (original_stalk_zero p)

private theorem native_stalk_original_function {σ : P → M}
    (hσ : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ σ) (z : P)
    (g : M → ℂ) (hg : HolomorphicAt n g (σ z)) :
    (ChartedSpace.locallyRingedSpaceMap σ hσ).stalkMap z (actualOriginalFunctionGerm (σ z) g hg) =
      actualOriginalFunctionGerm z (g ∘ σ)
        (hg.comp_contMDiff (Eventually.of_forall fun _ => hσ.contMDiffAt)) := by
  apply (actualStalkChartEquiv (n := m) z).injective
  rw [actualNativeStalk_chart_pullback,actualOriginalFunctionGerm_chart,
    actualHolomorphicGermPullback_original_function,actualOriginalFunctionGerm_chart]

omit [IsComplexManifold n M] [IsComplexManifold m P] in
private theorem holomorphic_comp_local {r : M → P} {p : M}
    (hr : ∀ᶠ q in 𝓝 p, MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) r q)
    {g : P → ℂ} (hg : HolomorphicAt m g (r p)) : HolomorphicAt n (g ∘ r) p := by
  filter_upwards [hr,hr.self_of_nhds.continuousAt.eventually hg] with q hq hgq
  exact hgq.comp q hq

/-- A true local geometric section lifts EVERY original native target stalk numerator. -/
private theorem native_stalk_surjective_of_local_retraction {σ : P → M}
    (hσ : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ σ)
    (r : M → P) (z : P)
    (hr : ∀ᶠ p in 𝓝 (σ z), MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) r p)
    (hrz : r (σ z) = z) (hsect : ∀ᶠ w in 𝓝 z, r (σ w) = w) :
    Function.Surjective ((ChartedSpace.locallyRingedSpaceMap σ hσ).stalkMap z) := by
  intro q
  obtain ⟨g,hg,rfl⟩ := exists_original_stalk_function z q
  have hgr : HolomorphicAt n (g ∘ r) (σ z) :=
    holomorphic_comp_local hr (hrz.symm ▸ hg)
  refine ⟨actualOriginalFunctionGerm (σ z) (g ∘ r) hgr,?_⟩
  rw [native_stalk_original_function]
  apply original_stalk_function_congr
  exact hsect.mono fun w hw => congrArg g hw

/-- Native kernel is the SAME whole vanishing ideal, derived by the actual on-carrier roundtrip. -/
private theorem native_stalk_kernel_of_local_retraction {σ : P → M}
    (hσ : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ σ)
    (r : M → P) (N : Set M) (z : P)
    (hr : ∀ᶠ p in 𝓝 (σ z), MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) r p)
    (hrz : r (σ z) = z) (hσN : ∀ w, σ w ∈ N)
    (hround : ∀ᶠ p in 𝓝 (σ z), p ∈ N → σ (r p) = p) :
    RingHom.ker ((ChartedSpace.locallyRingedSpaceMap σ hσ).stalkMap z).hom =
      actualWholeSheafStalkIdeal (vanishingIdeal (n := n) N) (σ z) := by
  apply le_antisymm
  · intro q hq
    obtain ⟨g,hg,rfl⟩ := exists_original_stalk_function (σ z) q
    have hz : actualOriginalFunctionGerm z (g ∘ σ)
        (hg.comp_contMDiff (Eventually.of_forall fun _ => hσ.contMDiffAt)) = 0 := by
      rw [←native_stalk_original_function hσ z g hg]
      exact hq
    have hzero := (original_stalk_zero_iff z _).mp hz
    have hrt : Tendsto r (𝓝 (σ z)) (𝓝 z) := by
      simpa only [hrz] using hr.self_of_nhds.continuousAt.tendsto
    have hN : (vanishingIdeal (n := n) N).mem (σ z) g := by
      refine ⟨hg,?_⟩
      filter_upwards [hround,hrt.eventually hzero] with p hp hz hpN
      exact (congrArg g (hp hpN)).symm.trans hz
    exact Ideal.subset_span ⟨g,hg,hN,rfl⟩
  · apply Ideal.span_le.mpr
    rintro _ ⟨g,hg,hmem,rfl⟩
    change (ChartedSpace.locallyRingedSpaceMap σ hσ).stalkMap z
      (actualOriginalFunctionGerm (σ z) g hg) = 0
    rw [native_stalk_original_function]
    apply (original_stalk_zero_iff z _).mpr
    filter_upwards [hσ.continuous.continuousAt.eventually hmem.2] with w hw
    exact hw (hσN w)

end NativeRetractionEngines

private def nativeQuotientDiagram {R R' S S' : Type*}
    [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
    (alpha : R→+*S) (alpha' : R'→+*S') (f : R→+*R') (g : S→+*S')
    (K : Ideal R) (K' : Ideal R')
    (hs : Function.Surjective alpha) (hs' : Function.Surjective alpha')
    (hk : RingHom.ker alpha=K) (hk' : RingHom.ker alpha'=K')
    (hi : Ideal.map f K=K') (hq : alpha'.comp f=g.comp alpha) :
    NativeQuotientDiagram alpha alpha' f g K K' := by
  let e : (R⧸K)≃+*S := (Ideal.quotEquivOfEq hk.symm).trans
    (RingHom.quotientKerEquivOfSurjective hs)
  let e' : (R'⧸K')≃+*S' := (Ideal.quotEquivOfEq hk'.symm).trans
    (RingHom.quotientKerEquivOfSurjective hs')
  have he (r : R) : e (Ideal.Quotient.mk K r)=alpha r := rfl
  have he' (r : R') : e' (Ideal.Quotient.mk K' r)=alpha' r := rfl
  let fbar : (R⧸K)→+*(R'⧸K') := Ideal.quotientMap K' f (hi ▸ Ideal.le_comap_map)
  have hfbar (r : R) : fbar (Ideal.Quotient.mk K r)=Ideal.Quotient.mk K' (f r) := rfl
  refine ⟨hs,hs',hk,hk',hi,hq,e,e',he,he',?_,?_,fbar,hfbar,?_⟩
  · intro r q
    rw [map_mul,he]
  · intro r q
    rw [map_mul,he']
  · intro q
    obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [hfbar,he,he']
    exact RingHom.congr_fun hq r

private theorem quotient_comp_kernel {R S : Type*} [CommRing R] [CommRing S]
    (alpha : R→+*S) (hs : Function.Surjective alpha) (J : Ideal R)
    (hk : RingHom.ker alpha≤J) :
    RingHom.ker ((Ideal.Quotient.mk (Ideal.map alpha J)).comp alpha)=J := by
  have he : Ideal.comap alpha (Ideal.map alpha J)=J := by
    rw [Ideal.comap_map_of_surjective alpha hs,←RingHom.ker_eq_comap_bot]
    exact sup_eq_left.mpr hk
  ext r
  change Ideal.Quotient.mk (Ideal.map alpha J) (alpha r)=0 ↔ r∈J
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change r∈Ideal.comap alpha (Ideal.map alpha J) ↔ r∈J
  rw [he]

private theorem quotient_comp_kernel_image {R S : Type*} [CommRing R] [CommRing S]
    (alpha : R→+*S) (hs : Function.Surjective alpha) (J : Ideal R) (L : Ideal S)
    (hmap : Ideal.map alpha J=L) (hk : RingHom.ker alpha≤J) :
    RingHom.ker ((Ideal.Quotient.mk L).comp alpha)=J := by
  have he : Ideal.comap alpha L=J := by
    rw [←hmap,Ideal.comap_map_of_surjective alpha hs,←RingHom.ker_eq_comap_bot]
    exact sup_eq_left.mpr hk
  ext r
  change Ideal.Quotient.mk L (alpha r)=0 ↔ r∈J
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change r∈Ideal.comap alpha L ↔ r∈J
  rw [he]

private theorem nativeQuotientDiagram_retains {R R' S S' : Type*}
    [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
    {alpha : R→+*S} {alpha' : R'→+*S'} {f : R→+*R'} {g : S→+*S'}
    {K : Ideal R} {K' : Ideal R'} (Q : NativeQuotientDiagram alpha alpha' f g K K')
    (eOld : (R⧸K)≃+*S) (heOld : ∀ r,eOld (Ideal.Quotient.mk K r)=alpha r) :
    Q.e=eOld := by
  ext q
  obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective q
  exact (Q.e_mk r).trans (heOld r).symm

-- Provenance: held ActualProjectionTestRecord private full boundary geometry,
-- copied from its exact product-axis and all-label proofs (zero duplicate credit).
section GlobalProductGeometry
variable {n : ℕ} {X : CMfd.{0} n}
private def global_boundary (E : List (Set X)) : List (Set (projectionAmbient X)) :=
  E.map ((Prod.fst : projectionAmbient X → X) ⁻¹' ·) ++ [horizontal X]

private def global_liftAxes (S : Finset (Fin n)) : Finset (Fin (n+1)) :=
  S.map (Fin.castAddEmb 1)

private theorem global_last_not_lift (S : Finset (Fin n)) : Fin.last n ∉ global_liftAxes S := by
  intro h
  obtain ⟨i,_hi,he⟩:=Finset.mem_map.mp h
  have hv:=congrArg Fin.val he
  change i.val=n at hv
  exact (Nat.ne_of_lt i.isLt) hv

private theorem global_split_old (w : ComplexModel (n+1)) (i : Fin n) :
    ((prodModelEquiv n 1).symm w).1 i=w (i.castAdd 1) := by
  rfl

private theorem global_split_normal (w : ComplexModel (n+1)) (i : Fin 1) :
    ((prodModelEquiv n 1).symm w).2 i=w (i.natAdd n) := by
  rfl

private theorem global_product_old (a : ComplexModel n) (b : ComplexModel 1) (i : Fin n) :
    prodModelEquiv n 1 (a,b) (i.castAdd 1)=a i := by
  have h:=congrArg (fun z : ComplexModel n × ComplexModel 1 => z.1 i)
    ((prodModelEquiv n 1).symm_apply_apply (a,b))
  rw [global_split_old] at h
  exact h

private theorem global_product_last (a : ComplexModel n) (b : ComplexModel 1) :
    prodModelEquiv n 1 (a,b) (Fin.last n)=b 0 := by
  have he : Fin.last n=(0 : Fin 1).natAdd n:=Fin.ext (by simp)
  rw [he]
  have h:=congrArg (fun z : ComplexModel n × ComplexModel 1 => z.2 0)
    ((prodModelEquiv n 1).symm_apply_apply (a,b))
  rw [global_split_normal] at h
  exact h

private theorem global_product_mask (a : ComplexModel n) (b : ComplexModel 1) (S : Finset (Fin n)) :
    prodModelEquiv n 1 (a,b)∈coordSubspace (global_liftAxes S) ↔ a∈coordSubspace S := by
  constructor
  · intro h i hi
    exact (global_product_old a b i) ▸ h (i.castAdd 1) (Finset.mem_map.mpr ⟨i,hi,rfl⟩)
  · intro h j hj
    obtain ⟨i,hi,rfl⟩:=Finset.mem_map.mp hj
    change prodModelEquiv n 1 (a,b) (i.castAdd 1)=0
    rw [global_product_old]
    exact h i hi

private theorem global_product_normal (a : ComplexModel n) (b : ComplexModel 1) :
    prodModelEquiv n 1 (a,b)∈coordSubspace {Fin.last n} ↔ b=0 := by
  constructor
  · intro h
    ext i
    obtain rfl : i=0:=Subsingleton.elim _ _
    simpa only [global_product_last,PiLp.zero_apply] using h (Fin.last n) (Finset.mem_singleton_self _)
  · intro hb j hj
    rw [Finset.mem_singleton.mp hj,global_product_last,hb]
    rfl

private theorem global_lift_family {ι : Type*} (A : ι → Set X) (S : ι → Finset (Fin n))
    (p : projectionAmbient X) (h : IsCoordinateFamilyAt n A S p.1) :
    IsCoordinateFamilyAt (n+1)
      (Sum.elim (fun i => (Prod.fst : projectionAmbient X → X) ⁻¹' A i) (fun _ : Unit => horizontal X))
      (Sum.elim (fun i => global_liftAxes (S i)) (fun _ : Unit => {Fin.last n})) p := by
  obtain ⟨Φ,hsrc,h0,hflat⟩:=h
  refine ⟨productCoordinates p Φ,?_,?_,?_⟩
  · intro w hw
    change w∈(prodChart (chartAt (ComplexModel n) p.1) (chartAt (ComplexModel 1) p.2)).target
    rw [prodChart_target]
    exact ⟨hsrc hw,Set.mem_univ _⟩
  · change prodModelEquiv n 1
      (Φ.toFun ((prodModelEquiv n 1).symm (chartAt (ComplexModel (n+1)) p p)).1,
        ((prodModelEquiv n 1).symm (chartAt (ComplexModel (n+1)) p p)).2-p.2)=0
    have hzero : Φ.toFun (chartAt (ComplexModel n) p.1 p.1)=0:=h0
    simp only [chartAt_prod,prodChart_apply,ContinuousLinearEquiv.symm_apply_apply,
      chartAt_self_eq,OpenPartialHomeomorph.refl_apply,id_eq,hzero,sub_self]
    exact (prodModelEquiv n 1).map_zero
  · rintro (i | u) hp q hq hqΦ
    · have hpair : q∈(chartAt (ComplexModel n) p.1).source ×ˢ
          (chartAt (ComplexModel 1) p.2).source:=by
        simpa only [complexChartAt,chartAt_prod,prodChart_source] using hq
      have hbase : q.1∈(chartAt (ComplexModel n) p.1).source:=hpair.1
      have hΦ : chartAt (ComplexModel n) p.1 q.1∈Φ.source:=by
        simpa only [productCoordinates,complexChartAt,chartAt_prod,prodChart_apply,
          ContinuousLinearEquiv.symm_apply_apply,mem_preimage] using hqΦ
      change q.1∈A i ↔ _
      rw [hflat i hp hbase hΦ]
      change _ ↔ prodModelEquiv n 1
        (Φ.toFun ((prodModelEquiv n 1).symm (chartAt (ComplexModel (n+1)) p q)).1,
          ((prodModelEquiv n 1).symm (chartAt (ComplexModel (n+1)) p q)).2-p.2)∈coordSubspace _
      simpa only [complexChartAt,chartAt_prod,prodChart_apply,ContinuousLinearEquiv.symm_apply_apply,Sum.elim_inl]
        using (global_product_mask (Φ.toFun (chartAt (ComplexModel n) p.1 q.1))
          ((chartAt (ComplexModel 1) p.2) q.2-p.2) (S i)).symm
    · change q.2=0 ↔ _
      change p.2=0 at hp
      change _ ↔ prodModelEquiv n 1
        (Φ.toFun ((prodModelEquiv n 1).symm (chartAt (ComplexModel (n+1)) p q)).1,
          ((prodModelEquiv n 1).symm (chartAt (ComplexModel (n+1)) p q)).2-p.2)∈coordSubspace _
      simpa only [complexChartAt,chartAt_prod,prodChart_apply,ContinuousLinearEquiv.symm_apply_apply,
        chartAt_self_eq,OpenPartialHomeomorph.refl_apply,id_eq,Sum.elim_inr,hp,sub_zero]
        using (global_product_normal (Φ.toFun (chartAt (ComplexModel n) p.1 q.1)) q.2).symm

private def global_boundaryIndex (E : List (Set X)) (i : Fin (global_boundary E).length) : Fin E.length ⊕ Unit :=
  if hi : i.val<E.length then Sum.inl ⟨i.val,hi⟩ else Sum.inr ()

private theorem global_boundary_get (E : List (Set X)) (i : Fin (global_boundary E).length) :
    (global_boundary E).get i=(global_boundaryIndex E i).elim
      (fun j => (Prod.fst : projectionAmbient X → X) ⁻¹' E.get j) (fun _ => horizontal X) := by
  by_cases hi : i.val<E.length
  · simp only [global_boundaryIndex,dif_pos hi,Sum.elim_inl]
    change (E.map _ ++ [horizontal X])[i.val]=_
    rw [List.getElem_append_left (by simpa using hi),List.getElem_map]
    rfl
  · have he : i.val=E.length:=by have := i.isLt; simp only [global_boundary,List.length_append,List.length_map,List.length_singleton] at this; omega
    simp only [global_boundaryIndex,dif_neg hi,Sum.elim_inr]
    change (E.map _ ++ [horizontal X])[i.val]=_
    rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt hi)]
    simp [he]

private theorem global_boundary_index_value (E : List (Set X)) (i : Fin (global_boundary E).length) :
    (global_boundaryIndex E i).elim Fin.val (fun _ => E.length)=i.val := by
  unfold global_boundaryIndex
  split
  · rfl
  · have := i.isLt
    simp only [global_boundary,List.length_append,List.length_map,List.length_singleton] at this
    dsimp
    omega

private theorem global_boundary_index_injective (E : List (Set X)) : Function.Injective (global_boundaryIndex E) := by
  intro i j hij
  apply Fin.ext
  rw [←global_boundary_index_value E i,←global_boundary_index_value E j,hij]

private theorem global_boundary_snc (E : List (Set X)) (hE : IsSNCDivisor n E) :
    IsSNCDivisor (n+1) (global_boundary E) := by
  classical
  refine ⟨?_,?_⟩
  · intro H hH
    rcases List.mem_append.mp hH with hH | hH
    · obtain ⟨K,hK,rfl⟩:=List.mem_map.mp hH
      exact (hE.1 K hK).preimage continuous_fst
    · rw [List.mem_singleton.mp hH]
      exact isClosed_singleton.preimage continuous_snd
  · intro p
    obtain ⟨S,hFamily,hCard,hInj⟩:=hE.2 p.1
    let F := Sum.elim (fun j => global_liftAxes (S j)) (fun _ : Unit => {Fin.last n})
    have hLift:=global_lift_family (fun j => E.get j) S p hFamily
    refine ⟨F ∘ global_boundaryIndex E,
      NormalCrossingsInvariance.IsCoordinateFamilyAt.reindex hLift (global_boundaryIndex E) (global_boundary_get E) (fun _ => rfl),?_,?_⟩
    · intro i hi
      rw [global_boundary_get] at hi
      cases hidx : global_boundaryIndex E i with
      | inl j =>
        have hj : p.1∈E.get j:=by simpa only [hidx,Sum.elim_inl,mem_preimage] using hi
        simpa only [Function.comp_apply,F,hidx,Sum.elim_inl,global_liftAxes,Finset.card_map] using hCard j hj
      | inr u => simp only [Function.comp_apply,F,hidx,Sum.elim_inr,Finset.card_singleton]
    · intro i hi j hj heq
      apply global_boundary_index_injective E
      change p∈(global_boundary E).get i at hi
      change p∈(global_boundary E).get j at hj
      rw [global_boundary_get] at hi hj
      cases hiidx : global_boundaryIndex E i with
      | inl a =>
        cases hjidx : global_boundaryIndex E j with
        | inl b =>
          have ha : p.1∈E.get a:=by simpa only [hiidx,Sum.elim_inl,mem_preimage] using hi
          have hb : p.1∈E.get b:=by simpa only [hjidx,Sum.elim_inl,mem_preimage] using hj
          have hh : global_liftAxes (S a)=global_liftAxes (S b):=by simpa only [Function.comp_apply,F,hiidx,hjidx,Sum.elim_inl] using heq
          have hS : S a=S b:=Finset.map_injective (Fin.castAddEmb 1) hh
          exact congrArg Sum.inl (hInj ha hb hS)
        | inr v =>
          have hh : global_liftAxes (S a)={Fin.last n}:=by simpa only [Function.comp_apply,F,hiidx,hjidx,Sum.elim_inl,Sum.elim_inr] using heq
          exact False.elim (global_last_not_lift (S a) (hh.symm ▸ Finset.mem_singleton_self _))
      | inr v =>
        cases hjidx : global_boundaryIndex E j with
        | inl b =>
          have hh : {Fin.last n}=global_liftAxes (S b):=by simpa only [Function.comp_apply,F,hiidx,hjidx,Sum.elim_inl,Sum.elim_inr] using heq
          exact False.elim (global_last_not_lift (S b) (hh ▸ Finset.mem_singleton_self _))
        | inr w => cases v; cases w; rfl

private theorem global_boundary_transverse {N : Set X} {E : List (Set X)} (hT : IsTransverse n N E) :
    IsTransverse (n+1) ((Prod.fst : projectionAmbient X → X) ⁻¹' N) (global_boundary E) := by
  classical
  intro p hp
  obtain ⟨S₀,S,hFamily,hCard⟩:=hT p.1 hp
  let F := Sum.elim (fun j => global_liftAxes (S j)) (fun _ : Unit => {Fin.last n})
  have hLift:=global_lift_family (fun o : Option (Fin E.length) => o.elim N (fun j => E.get j))
    (fun o => o.elim S₀ S) p hFamily
  let ix : Option (Fin (global_boundary E).length) → Option (Fin E.length) ⊕ Unit :=
    fun o => o.elim (Sum.inl none) (fun j => (global_boundaryIndex E j).map some id)
  refine ⟨global_liftAxes S₀,F ∘ global_boundaryIndex E,?_,?_⟩
  · apply NormalCrossingsInvariance.IsCoordinateFamilyAt.reindex hLift ix
    · rintro (_ | i)
      · rfl
      · cases hidx : global_boundaryIndex E i <;> simpa [ix,hidx] using global_boundary_get E i
    · rintro (_ | i)
      · rfl
      · cases hidx : global_boundaryIndex E i <;> simp [ix,F,hidx]
  · intro i hi
    rw [global_boundary_get] at hi
    cases hidx : global_boundaryIndex E i with
    | inl j =>
      have hj : p.1∈E.get j:=by simpa only [hidx,Sum.elim_inl,mem_preimage] using hi
      obtain ⟨hc,hd⟩:=hCard j hj
      refine ⟨?_,?_⟩
      · simpa only [Function.comp_apply,F,hidx,Sum.elim_inl,global_liftAxes,Finset.card_map] using hc
      · simpa only [Function.comp_apply,F,hidx,Sum.elim_inl,global_liftAxes,Finset.disjoint_map] using hd
    | inr u =>
      refine ⟨by simp [F,hidx],?_⟩
      apply Finset.disjoint_left.mpr
      intro j hj hjs
      have hjlast : j=Fin.last n:=by simpa [F,hidx] using hj
      exact global_last_not_lift S₀ (hjlast ▸ hjs)


end GlobalProductGeometry

section ProductGeometry
variable {n : ℕ} {X : CMfd.{0} n} {A : GermIdeal n X} {N : Set X}
  {E : List (Set X)} {x : X} (F : OriginalLogFrame A N E x)

private theorem productParameterMap_holo :
    ContMDiff 𝓘(ℂ,ComplexModel (F.k+1)) 𝓘(ℂ,ComplexModel (n+1)) ∞
      (productParameterMap F) :=
  ProductComplexManifold.contMDiff_prodMk
    ((parameterMapOn_contMDiff F.Φ F.k F.hsrc).comp
      (ProductComplexManifold.contMDiff_fst (n:=F.k) (m:=1)))
    (ProductComplexManifold.contMDiff_snd (n:=F.k) (m:=1))

private theorem product_native_projection :
    ChartedSpace.locallyRingedSpaceMap (productParameterMap F) (productParameterMap_holo F) ≫
      ChartedSpace.locallyRingedSpaceMap (Prod.fst : projectionAmbient X→X)
        (ProductComplexManifold.contMDiff_fst (n:=n) (m:=1)) =
    ChartedSpace.locallyRingedSpaceMap (Prod.fst : parameterProduct F→parameterOpen F.Φ F.k)
        (ProductComplexManifold.contMDiff_fst (n:=F.k) (m:=1)) ≫
      ChartedSpace.locallyRingedSpaceMap (parameterMapOn F.Φ F.k)
        (parameterMapOn_contMDiff F.Φ F.k F.hsrc) := by
  rw [← ChartedSpace.locallyRingedSpace_comp 𝓘(ℂ,ComplexModel n),
    ← ChartedSpace.locallyRingedSpace_comp 𝓘(ℂ,ComplexModel n)]
  rfl

private theorem product_native_sigma :
    ChartedSpace.locallyRingedSpaceMap
      (parameterMapOn (X:=projectionAmbient X) (shiftedProductChart F.Φ F.k F.hk) (F.k+1))
      (parameterMapOn_contMDiff (X:=projectionAmbient X) (shiftedProductChart F.Φ F.k F.hk)
        (F.k+1) (shifted_source F.Φ F.k F.hk F.hsrc)) =
    ChartedSpace.locallyRingedSpaceMap (sameParameterRho F.Φ F.k F.hk)
        (sameParameterRho F.Φ F.k F.hk).contMDiff ≫
      ChartedSpace.locallyRingedSpaceMap (productParameterMap F) (productParameterMap_holo F) := by
  rw [←ChartedSpace.locallyRingedSpace_comp 𝓘(ℂ,ComplexModel (n+1))]
  congr 1
  funext w
  exact shifted_parameterMap F.Φ F.k F.hk w

-- Literal held retraction identity, reproved privately; no imported private engine.
private theorem parameter_retraction_section (v w : parameterOpen F.Φ F.k) :
    actualParameterRetraction F.Φ F.k v (parameterMapOn F.Φ F.k w)=w := by
  change openInv (parameterOpen F.Φ F.k) v
    (coordinateProjection n F.k (flatMap F.Φ (parameterMap F.Φ F.k w.val)))=w
  rw [(parameterMap_roundtrip F.Φ F.k F.hk F.hsrc).1 w.val w.property]
  simp [openInv,w.property]

private theorem product_parameter_image (t : parameterProduct F) :
    productParameterMap F t∈(Prod.fst : projectionAmbient X→X) ⁻¹' N := by
  exact (actual_parameter_retraction_geometry F.Φ F.hk F.hsrc N
    (fun p hp => (F.output.2.2.2.2.2.1 p hp).1) t.1).1 t.1

private theorem product_retraction_section (t w : parameterProduct F) :
    productParameterRetraction F t (productParameterMap F w)=w := by
  apply Prod.ext
  · exact parameter_retraction_section F t.1 w.1
  · rfl

private theorem product_retraction_roundtrip (t : parameterProduct F) :
    ∀ᶠ p in 𝓝 (productParameterMap F t), p∈(Prod.fst : projectionAmbient X→X) ⁻¹' N →
      productParameterMap F (productParameterRetraction F t p)=p := by
  have hround := (actual_parameter_retraction_geometry F.Φ F.hk F.hsrc N
    (fun p hp => (F.output.2.2.2.2.2.1 p hp).1) t.1).2.2.2
  have hf : Tendsto (Prod.fst : projectionAmbient X→X) (𝓝 (productParameterMap F t))
      (𝓝 (parameterMapOn F.Φ F.k t.1)) := continuous_fst.continuousAt.tendsto
  have hh : ∀ᶠ p in 𝓝 (productParameterMap F t), p.1∈N →
      parameterMapOn F.Φ F.k (actualParameterRetraction F.Φ F.k t.1 p.1)=p.1 :=
    hf.eventually hround
  filter_upwards [hh] with p hp hpN
  exact Prod.ext (hp hpN) rfl

private theorem product_retraction_holo (t : parameterProduct F) :
    ∀ᶠ p in 𝓝 (productParameterMap F t),MDifferentiableAt
      𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel (F.k+1)) (productParameterRetraction F t) p := by
  have hr := (actual_parameter_retraction_geometry F.Φ F.hk F.hsrc N
    (fun p hp => (F.output.2.2.2.2.2.1 p hp).1) t.1).2.1
  have hf : Tendsto (Prod.fst : projectionAmbient X→X) (𝓝 (productParameterMap F t))
      (𝓝 (parameterMapOn F.Φ F.k t.1)) := continuous_fst.continuousAt.tendsto
  filter_upwards [hf.eventually hr] with p hp
  exact mdifferentiableAt_product
    (hp.comp p ((ProductComplexManifold.contMDiff_fst (n:=n) (m:=1)).mdifferentiable (by simp) p))
    ((ProductComplexManifold.contMDiff_snd (n:=n) (m:=1)).mdifferentiable (by simp) p)

private theorem product_native_kernel (t : parameterProduct F) :
    Function.Surjective ((ChartedSpace.locallyRingedSpaceMap
      (productParameterMap F) (productParameterMap_holo F)).stalkMap t) ∧
    RingHom.ker ((ChartedSpace.locallyRingedSpaceMap (productParameterMap F)
      (productParameterMap_holo F)).stalkMap t).hom =
      actualWholeSheafStalkIdeal (vanishingIdeal (n:=n+1)
        ((Prod.fst : projectionAmbient X→X) ⁻¹' N)) (productParameterMap F t) := by
  constructor
  · exact native_stalk_surjective_of_local_retraction (productParameterMap_holo F)
      (productParameterRetraction F t) t (product_retraction_holo F t)
      (product_retraction_section F t t)
      (Eventually.of_forall (product_retraction_section F t))
  · exact native_stalk_kernel_of_local_retraction (productParameterMap_holo F)
      (productParameterRetraction F t) ((Prod.fst : projectionAmbient X→X) ⁻¹' N) t
      (product_retraction_holo F t) (product_retraction_section F t t)
      (product_parameter_image F) (product_retraction_roundtrip F t)

private theorem source_native_kernel (t : parameterProduct F) :
    Function.Surjective (parameterStalkMap F.Φ F.k F.hsrc t.1) ∧
      RingHom.ker (parameterStalkMap F.Φ F.k F.hsrc t.1)=
        nativeIdeal F (vanishingIdeal (n:=n) N) t := by
  have hg := actual_parameter_retraction_geometry F.Φ F.hk F.hsrc N
    (fun p hp => (F.output.2.2.2.2.2.1 p hp).1) t.1
  constructor
  · exact native_stalk_surjective_of_local_retraction
      (parameterMapOn_contMDiff F.Φ F.k F.hsrc) (actualParameterRetraction F.Φ F.k t.1)
      t.1 hg.2.1 hg.2.2.1 (Eventually.of_forall (parameter_retraction_section F t.1))
  · exact native_stalk_kernel_of_local_retraction
      (parameterMapOn_contMDiff F.Φ F.k F.hsrc) (actualParameterRetraction F.Φ F.k t.1)
      N t.1 hg.2.1 hg.2.2.1 hg.1 hg.2.2.2

private theorem projection_native_whole_ideal (B : GermIdeal n X) (hB : B.IsCoherent)
    (t : parameterProduct F) :
    Ideal.map (ambientNative F t) (nativeIdeal F B t)=nativeIdealPlus F B t := by
  exact HironakaSingularSubspaceBlowupCartier.map_actualWholeSheafStalkIdeal_native_pullback
    (ProductComplexManifold.contMDiff_fst (n:=n) (m:=1)) B hB (productParameterMap F t)

private theorem projection_native_carrier_ideal (t : parameterProduct F) :
    Ideal.map (ambientNative F t) (nativeIdeal F (vanishingIdeal (n:=n) N) t)=
      actualWholeSheafStalkIdeal (vanishingIdeal (n:=n+1)
        ((Prod.fst : projectionAmbient X→X) ⁻¹' N)) (productParameterMap F t) := by
  have h := projection_native_whole_ideal F (vanishingIdeal (n:=n) N)
    (VanishingIdealCoherent.isCoherent_vanishingIdeal F.smooth) t
  simpa only [nativeIdealPlus,pulled,
    HironakaSmoothSubmersionRelativeRestriction.pullback_vanishingIdeal_submersion
      (HironakaAuxiliaryGraphGeometry.isSubmersion_fst
        (n:=n) (m:=1) (X:=X) (Y:=ComplexModel 1)) F.smooth] using h

private theorem product_native_square (t : parameterProduct F) :
    (((ChartedSpace.locallyRingedSpaceMap (productParameterMap F)
      (productParameterMap_holo F)).stalkMap t).hom).comp (ambientNative F t)=
    (parameterNative F t).comp (parameterStalkMap F.Φ F.k F.hsrc t.1) := by
  ext r
  obtain ⟨g,hg,rfl⟩ := exists_original_stalk_function (parameterMapOn F.Φ F.k t.1) r
  change (ChartedSpace.locallyRingedSpaceMap (productParameterMap F)
      (productParameterMap_holo F)).stalkMap t
      ((ChartedSpace.locallyRingedSpaceMap (Prod.fst : projectionAmbient X→X)
        (ProductComplexManifold.contMDiff_fst (n:=n) (m:=1))).stalkMap
        (productParameterMap F t) (actualOriginalFunctionGerm _ g hg)) =
    (ChartedSpace.locallyRingedSpaceMap (Prod.fst : parameterProduct F→parameterOpen F.Φ F.k)
      (ProductComplexManifold.contMDiff_fst (n:=F.k) (m:=1))).stalkMap t
      ((ChartedSpace.locallyRingedSpaceMap (parameterMapOn F.Φ F.k)
        (parameterMapOn_contMDiff F.Φ F.k F.hsrc)).stalkMap t.1
        (actualOriginalFunctionGerm _ g hg))
  erw [native_stalk_original_function,native_stalk_original_function,
    native_stalk_original_function,native_stalk_original_function]
  apply original_stalk_function_congr
  exact Eventually.of_forall fun _ => rfl

private def productCarrierQuotient (G : ProjectionParameterData F) (t : parameterProduct F) :
    NativeQuotientDiagram (sourceNative F t) (productNative F G t)
      (ambientNative F t) (parameterNative F t)
      (nativeIdeal F (vanishingIdeal (n:=n) N) t)
      (actualWholeSheafStalkIdeal (vanishingIdeal (n:=n+1)
        ((Prod.fst : projectionAmbient X→X) ⁻¹' N)) (productParameterMap F t)) :=
  nativeQuotientDiagram _ _ _ _ _ _ (source_native_kernel F t).1
    (product_native_kernel F t).1 (source_native_kernel F t).2
    (product_native_kernel F t).2 (projection_native_carrier_ideal F t) (product_native_square F t)

private theorem product_carrier_chart (p : projectionAmbient X)
    (hp : p∈flatDomain (M:=projectionAmbient X) (shiftedProductChart F.Φ F.k F.hk)) :
    p∈(Prod.fst : projectionAmbient X→X) ⁻¹' N ↔
      flatMap (M:=projectionAmbient X) (shiftedProductChart F.Φ F.k F.hk) p∈
        complexCoordinatePlane (n+1) (F.k+1) := by
  rw [shifted_flatMap,shuffle_plane]
  exact (F.output.2.2.2.2.2.1 p.1 ((shifted_flatDomain F.Φ F.k F.hk p).mp hp)).1

private theorem product_old_boundary (p : projectionAmbient X)
    (hp : p∈flatDomain (M:=projectionAmbient X) (shiftedProductChart F.Φ F.k F.hk))
    (i : Fin E.length) :
    p.1∈E.get i ↔ ∃ j,projectedAmbientSlot F i.castSucc=some j ∧
      flatCoord (shiftedProductChart F.Φ F.k F.hk) j p=0 := by
  have h := (F.output.2.2.2.2.2.1 p.1 ((shifted_flatDomain F.Φ F.k F.hk p).mp hp)).2 i
  cases hκ : F.κ i with
  | none => simpa [projectedAmbientSlot,hκ] using h
  | some j =>
    have hj := F.output.2.1 i j hκ
    have hv : flatCoord (shiftedProductChart F.Φ F.k F.hk) j.castSucc p=flatCoord F.Φ j p.1 := by
      change flatMap (shiftedProductChart F.Φ F.k F.hk) p j.castSucc=flatMap F.Φ p.1 j
      rw [shifted_flatMap,shuffle_old_value n F.k F.hk _ _ j hj]
    simpa [projectedAmbientSlot,hκ,hv] using h

private theorem oneModel_zero_iff (c : ComplexModel 1) : c=0 ↔ c 0=0 := by
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    ext i
    obtain rfl : i=0 := Subsingleton.elim _ _
    exact h

private theorem product_horizontal_boundary (p : projectionAmbient X) :
    p∈horizontal X ↔ ∃ j,projectedAmbientSlot F (Fin.last E.length)=some j ∧
      flatCoord (shiftedProductChart F.Φ F.k F.hk) j p=0 := by
  have hv : flatCoord (shiftedProductChart F.Φ F.k F.hk) ⟨F.k,Nat.lt_succ_of_le F.hk⟩ p=p.2 0 := by
    change flatMap (shiftedProductChart F.Φ F.k F.hk) p _=p.2 0
    rw [shifted_flatMap,shuffle_horizontal_value]
  simp only [projectedAmbientSlot,Fin.lastCases_last]
  change p.2=0 ↔ ∃ j,some (⟨F.k,Nat.lt_succ_of_le F.hk⟩ : Fin (n+1))=some j ∧
    flatCoord (shiftedProductChart F.Φ F.k F.hk) j p=0
  constructor
  · intro h
    exact ⟨_,rfl,hv.trans (congrArg (fun c : ComplexModel 1 => c 0) h)⟩
  · rintro ⟨j,hj,hz⟩
    have he := Option.some.inj hj
    subst j
    exact (oneModel_zero_iff p.2).mpr (hv.symm.trans hz)

private theorem projectedBoundary_old (i : Fin E.length) :
    (projectedBoundary F).get (Fin.cast (by simp [projectedBoundary]) i.castSucc)=
      (Prod.fst : projectionAmbient X→X) ⁻¹' E.get i := by
  change (E.map ((Prod.fst : projectionAmbient X→X) ⁻¹' ·) ++ [horizontal X])[i.val]=_
  rw [List.getElem_append_left (by simpa only [List.length_map] using i.isLt),List.getElem_map]
  rfl

private theorem projectedBoundary_last :
    (projectedBoundary F).get (Fin.cast (by simp [projectedBoundary]) (Fin.last E.length))=horizontal X := by
  change (E.map ((Prod.fst : projectionAmbient X→X) ⁻¹' ·) ++ [horizontal X])[E.length]=_
  rw [List.getElem_append_right (by simp)]
  simp

private theorem product_boundary_chart (p : projectionAmbient X)
    (hp : p∈flatDomain (M:=projectionAmbient X) (shiftedProductChart F.Φ F.k F.hk))
    (i : Fin (E.length+1)) :
    p∈(projectedBoundary F).get (Fin.cast (by simp [projectedBoundary]) i) ↔
      ∃ j,projectedAmbientSlot F i=some j ∧ flatCoord (shiftedProductChart F.Φ F.k F.hk) j p=0 := by
  refine Fin.lastCases ?_ (fun a => ?_) i
  · rw [projectedBoundary_last]
    exact product_horizontal_boundary F p
  · rw [projectedBoundary_old]
    exact product_old_boundary F p hp a

private theorem product_parameter_old_boundary
    (w : parameterOpen (X:=projectionAmbient X) (shiftedProductChart F.Φ F.k F.hk) (F.k+1))
    (i : Fin E.length) :
    (parameterMapOn (X:=projectionAmbient X) (shiftedProductChart F.Φ F.k F.hk) (F.k+1) w).1∈E.get i ↔
      ∃ j,projectedParameterSlot F i.castSucc=some j ∧ w.val j=0 := by
  rw [shifted_parameterMap]
  have h := F.output.2.2.2.2.1 (sameParameterRho F.Φ F.k F.hk w).1 i
  cases hτ : F.τ i with
  | none => simpa [projectedParameterSlot,hτ] using h
  | some j =>
    have hv : (sameParameterRho F.Φ F.k F.hk w).1.val j=w.val j.castSucc := split_old w.val j
    simpa [projectedParameterSlot,hτ,hv] using h

private theorem product_parameter_horizontal_boundary
    (w : parameterOpen (X:=projectionAmbient X) (shiftedProductChart F.Φ F.k F.hk) (F.k+1)) :
    parameterMapOn (X:=projectionAmbient X) (shiftedProductChart F.Φ F.k F.hk) (F.k+1) w∈horizontal X ↔
      ∃ j,projectedParameterSlot F (Fin.last E.length)=some j ∧ w.val j=0 := by
  rw [shifted_parameterMap]
  simp only [projectedParameterSlot,Fin.lastCases_last]
  change (sameParameterRho F.Φ F.k F.hk w).2=0 ↔
    ∃ j,some (Fin.last F.k)=some j ∧ w.val j=0
  constructor
  · intro h
    exact ⟨_,rfl,(split_last w.val).symm.trans (congrArg (fun c : ComplexModel 1 => c 0) h)⟩
  · rintro ⟨j,hj,hz⟩
    have he := Option.some.inj hj
    subst j
    exact (oneModel_zero_iff _).mpr ((split_last w.val).trans hz)

private theorem product_parameter_boundary
    (w : parameterOpen (X:=projectionAmbient X) (shiftedProductChart F.Φ F.k F.hk) (F.k+1))
    (i : Fin (E.length+1)) :
    parameterMapOn (X:=projectionAmbient X) (shiftedProductChart F.Φ F.k F.hk) (F.k+1) w∈
      (projectedBoundary F).get (Fin.cast (by simp [projectedBoundary]) i) ↔
      ∃ j,projectedParameterSlot F i=some j ∧ w.val j=0 := by
  refine Fin.lastCases ?_ (fun a => ?_) i
  · rw [projectedBoundary_last]
    exact product_parameter_horizontal_boundary F w
  · rw [projectedBoundary_old]
    exact product_parameter_old_boundary F w a

private theorem tangentPullback_coordinate (k : ℕ) (i : Fin k) :
    HironakaRelativeNormalIdeal.tangentPullback k 1 (coordinateGerm i)=coordinateGerm i.castSucc := by
  rfl

private theorem tangentPullback_const (k : ℕ) (c : ℂ) :
    HironakaRelativeNormalIdeal.tangentPullback k 1 (HolGerm.constHom c)=HolGerm.constHom c := by
  rfl

private theorem projectedSlot_old_exists (j : Fin F.k) :
    (∃ i,projectedAmbientSlot F i=some (j.castSucc.castLE (Nat.succ_le_succ F.hk))) ↔
      ∃ i,F.κ i=some (j.castLE F.hk) := by
  constructor
  · rintro ⟨i,hi⟩
    revert hi
    refine Fin.lastCases ?_ (fun a => ?_) i
    · intro h
      simp only [projectedAmbientSlot,Fin.lastCases_last,Option.some.injEq] at h
      have hv := congrArg Fin.val h
      simp only [Fin.val_castLE,Fin.val_castSucc] at hv
      omega
    · intro h
      simp only [projectedAmbientSlot,Fin.lastCases_castSucc] at h
      cases hκ : F.κ a with
      | none => simp [hκ] at h
      | some b =>
        simp only [hκ,Option.map_some,Option.some.injEq] at h
        have hb : b=j.castLE F.hk := Fin.ext (congrArg (fun z : Fin (n+1) => z.val) h)
        exact ⟨a,hκ.trans (congrArg some hb)⟩
  · rintro ⟨i,hi⟩
    refine ⟨i.castSucc,?_⟩
    simp only [projectedAmbientSlot,Fin.lastCases_castSucc,hi,Option.map_some]
    rfl

private theorem product_horizontal_weight
    (w : parameterOpen (X:=projectionAmbient X) (shiftedProductChart F.Φ F.k F.hk) (F.k+1)) :
    parameterWeight (X:=projectionAmbient X) (shiftedProductChart F.Φ F.k F.hk) (F.k+1)
      (projectedAmbientSlot F) (Nat.succ_le_succ F.hk) w (Fin.last F.k)=
      HolGerm.constHom ((sameParameterRho F.Φ F.k F.hk w).2 0)+coordinateGerm (Fin.last F.k) := by
  have hslot : ∃ i,projectedAmbientSlot F i=some ((Fin.last F.k).castLE (Nat.succ_le_succ F.hk)) := by
    refine ⟨Fin.last E.length,?_⟩
    simp only [projectedAmbientSlot,Fin.lastCases_last]
    rfl
  rw [parameterWeight,if_pos hslot]
  exact congrArg (fun z : ℂ => HolGerm.constHom z+coordinateGerm (Fin.last F.k))
    (split_last w.val).symm

private theorem product_old_weight
    (w : parameterOpen (X:=projectionAmbient X) (shiftedProductChart F.Φ F.k F.hk) (F.k+1))
    (j : Fin F.k) :
    parameterWeight (X:=projectionAmbient X) (shiftedProductChart F.Φ F.k F.hk) (F.k+1)
      (projectedAmbientSlot F) (Nat.succ_le_succ F.hk) w j.castSucc=
      HironakaRelativeNormalIdeal.tangentPullback F.k 1
        (parameterWeight F.Φ F.k F.κ F.hk (sameParameterRho F.Φ F.k F.hk w).1 j) := by
  simp only [parameterWeight]
  simp only [projectedSlot_old_exists]
  split_ifs with h
  · rw [map_add,tangentPullback_const,
      tangentPullback_coordinate]
    have hv : (sameParameterRho F.Φ F.k F.hk w).1.val j=w.val j.castSucc := split_old w.val j
    rw [hv]
  · exact (map_one _).symm

private theorem product_all_weights
    (w : parameterOpen (X:=projectionAmbient X) (shiftedProductChart F.Φ F.k F.hk) (F.k+1)) :
    parameterWeight (X:=projectionAmbient X) (shiftedProductChart F.Φ F.k F.hk) (F.k+1)
      (projectedAmbientSlot F) (Nat.succ_le_succ F.hk) w=
      HironakaActualProjectionLogDerivativeIdeal.projectionWeight
        (parameterWeight F.Φ F.k F.κ F.hk (sameParameterRho F.Φ F.k F.hk w).1)
        ((sameParameterRho F.Φ F.k F.hk w).2 0) := by
  funext j
  refine Fin.lastCases ?_ (fun a => ?_) j
  · simpa only [HironakaActualProjectionLogDerivativeIdeal.projectionWeight,Fin.lastCases_last]
      using product_horizontal_weight F w
  · simpa only [HironakaActualProjectionLogDerivativeIdeal.projectionWeight,Fin.lastCases_castSucc]
      using product_old_weight F w a

private theorem rho_chart_value
    (w u : parameterOpen (X:=projectionAmbient X) (shiftedProductChart F.Φ F.k F.hk) (F.k+1)) :
    chartAt (ComplexModel (F.k+1)) (sameParameterRho F.Φ F.k F.hk w)
      (sameParameterRho F.Φ F.k F.hk u)=u.val := by
  change prodModelEquiv F.k 1
    (((prodModelEquiv F.k 1).symm u.val).1,((prodModelEquiv F.k 1).symm u.val).2)=u.val
  exact (prodModelEquiv F.k 1).apply_symm_apply u.val

private theorem rho_translated_eventually
    (w : parameterOpen (X:=projectionAmbient X) (shiftedProductChart F.Φ F.k F.hk) (F.k+1)) :
    actualTranslatedMap (sameParameterRho F.Φ F.k F.hk) w=ᶠ[𝓝 (0 : ComplexModel (F.k+1))] id := by
  have hh := actualTranslatedMap_val_eventually (n:=F.k+1)
    (parameterOpen (X:=projectionAmbient X) (shiftedProductChart F.Φ F.k F.hk) (F.k+1)) w
  filter_upwards [hh] with z hz
  change chartAt (ComplexModel (F.k+1)) (sameParameterRho F.Φ F.k F.hk w)
      (sameParameterRho F.Φ F.k F.hk
        ((chartAt (ComplexModel (F.k+1)) w).symm (z+chartAt (ComplexModel (F.k+1)) w w))) -
    chartAt (ComplexModel (F.k+1)) (sameParameterRho F.Φ F.k F.hk w)
      (sameParameterRho F.Φ F.k F.hk w)=z
  rw [rho_chart_value,rho_chart_value]
  simpa only [actualTranslatedMap,chartAt_self_eq,OpenPartialHomeomorph.refl_apply,id_eq] using hz

private theorem rho_germPullback_id
    (w : parameterOpen (X:=projectionAmbient X) (shiftedProductChart F.Φ F.k F.hk) (F.k+1)) :
    actualHolomorphicGermPullback (sameParameterRho F.Φ F.k F.hk).contMDiff w=
      AlgHom.id ℂ (HolGerm (ComplexModel (F.k+1))) := by
  apply AlgHom.ext
  intro a
  induction a using HolGerm.induction_on with
  | h H hH =>
    change actualHolomorphicGermPullback (sameParameterRho F.Φ F.k F.hk).contMDiff w
      (HolGerm.mk H hH)=HolGerm.mk H hH
    unfold actualHolomorphicGermPullback
    rw [compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact (rho_translated_eventually F w).mono (fun z hz => congrArg H hz)

private theorem rho_all_native_germs
    (w : parameterOpen (X:=projectionAmbient X) (shiftedProductChart F.Φ F.k F.hk) (F.k+1))
    (r : actualComplexStructureStalk (n:=F.k+1) (sameParameterRho F.Φ F.k F.hk w)) :
    actualStalkChartEquiv (n:=F.k+1) w
      ((ChartedSpace.locallyRingedSpaceMap (sameParameterRho F.Φ F.k F.hk)
        (sameParameterRho F.Φ F.k F.hk).contMDiff).stalkMap w r)=
      actualStalkChartEquiv (n:=F.k+1) (sameParameterRho F.Φ F.k F.hk w) r := by
  rw [actualNativeStalk_chart_pullback,rho_germPullback_id]
  rfl

private theorem tangentProjection_split (k : ℕ) (z : ComplexModel (k+1)) :
    HironakaRelativeNormalIdeal.tangentProjection k 1 z=((prodModelEquiv k 1).symm z).1 := by
  rfl

private theorem parameterOpen_chart_value (v u : parameterOpen F.Φ F.k) :
    chartAt (ComplexModel F.k) v u=u.val := rfl

private theorem parameterProjection_translated_eventually (t : parameterProduct F) :
    actualTranslatedMap (n:=F.k) (m:=F.k+1)
      (Prod.fst : parameterProduct F→parameterOpen F.Φ F.k) t =ᶠ[𝓝 (0 : ComplexModel (F.k+1))]
      HironakaRelativeNormalIdeal.tangentProjection F.k 1 := by
  have hold := actualTranslatedMap_val_eventually (n:=F.k) (parameterOpen F.Φ F.k) t.1
  have ht : Tendsto (fun z : ComplexModel (F.k+1) => ((prodModelEquiv F.k 1).symm z).1)
      (𝓝 0) (𝓝 0) := by
    simpa only [map_zero,Prod.fst_zero] using
      ((prodModelEquiv F.k 1).symm.continuous.fst.tendsto (0 : ComplexModel (F.k+1)))
  filter_upwards [ht.eventually hold] with z hz
  rw [tangentProjection_split]
  simpa only [actualTranslatedMap,chartAt_prod,prodChart_apply,prodChart_symm_apply,
    map_add,ContinuousLinearEquiv.symm_apply_apply,Prod.fst_add,chartAt_self_eq,
    OpenPartialHomeomorph.refl_apply,id_eq,parameterOpen_chart_value] using hz

private theorem parameterProjection_germPullback (t : parameterProduct F) :
    actualHolomorphicGermPullback
      (ProductComplexManifold.contMDiff_fst (n:=F.k) (m:=1)) t=
      HironakaRelativeNormalIdeal.tangentPullback F.k 1 := by
  apply AlgHom.ext
  intro a
  induction a using HolGerm.induction_on with
  | h H hH =>
    unfold actualHolomorphicGermPullback HironakaRelativeNormalIdeal.tangentPullback
    rw [compAlgHom_mk,compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact (parameterProjection_translated_eventually F t).mono (fun z hz => congrArg H hz)

private def originalProjectionParameterData : ProjectionParameterData F where
  Ψ := shiftedProductChart F.Φ F.k F.hk
  hsrc := shifted_source F.Φ F.k F.hk F.hsrc
  centred := shifted_centred F.Φ F.k F.hk F.output.1
  source := rfl
  target := fun _ => Iff.rfl
  forward := by
    intro w
    simp only [shiftedProductChart,postcomposeLinear,productCoordinates,sub_zero]
  inverse := by
    intro w
    simp only [shiftedProductChart,postcomposeLinear,productCoordinates,add_zero]
  shuffle := shuffle_inclusion n F.k F.hk
  rho := sameParameterRho F.Φ F.k F.hk
  rho_value := fun w => (prodModelEquiv F.k 1).apply_symm_apply w.val
  rho_inverse := fun _ => rfl
  sigma := shifted_parameterMap F.Φ F.k F.hk
  sigma_holo := productParameterMap_holo F
  native_sigma := product_native_sigma F
  native_projection := product_native_projection F
  rho_all_native_germs := rho_all_native_germs F
  carrier_chart := product_carrier_chart F
  boundary_chart := product_boundary_chart F
  parameter_boundary := product_parameter_boundary F
  horizontal_weight := product_horizontal_weight F
  all_weights := product_all_weights F
  product_carrier := HironakaSmoothSubmersionRelativeGeometry.isClosedSubmanifold_preimage_submersion
    (HironakaAuxiliaryGraphGeometry.isSubmersion_fst (n:=n) (m:=1) (X:=X) (Y:=ComplexModel 1)) F.smooth
  product_snc := global_boundary_snc E F.snc
  product_transverse := global_boundary_transverse F.transverse
  image := product_parameter_image F
  retraction_holo := product_retraction_holo F
  retraction_point := fun t => product_retraction_section F t t
  «section» := product_retraction_section F
  roundtrip := product_retraction_roundtrip F

private theorem source_germ_facts (t : parameterProduct F) :
    Function.Surjective (sourceGerm F t) ∧ RingHom.ker (sourceGerm F t)=
      nativeIdeal F (vanishingIdeal (n:=n) N) t := by
  have h := F.output.2.2.2.2.2.2.2.2 t.1
  exact ⟨h.1,h.2.1⟩

private theorem product_germ_facts (t : parameterProduct F) :
    Function.Surjective (productGerm F (originalProjectionParameterData F) t) ∧
      RingHom.ker (productGerm F (originalProjectionParameterData F) t)=
        actualWholeSheafStalkIdeal (vanishingIdeal (n:=n+1)
          ((Prod.fst : projectionAmbient X→X) ⁻¹' N)) (productParameterMap F t) := by
  constructor
  · exact (actualStalkChartEquiv (n:=F.k+1) (M:=parameterProduct F) t).surjective.comp
      (product_native_kernel F t).1
  · rw [←(product_native_kernel F t).2]
    ext r
    change actualStalkChartEquiv (n:=F.k+1) (M:=parameterProduct F) t
      ((ChartedSpace.locallyRingedSpaceMap (productParameterMap F)
        (productParameterMap_holo F)).stalkMap t r)=0 ↔
      (ChartedSpace.locallyRingedSpaceMap (productParameterMap F)
        (productParameterMap_holo F)).stalkMap t r=0
    constructor
    · intro h
      exact (actualStalkChartEquiv (n:=F.k+1) (M:=parameterProduct F) t).injective
        (h.trans (map_zero _).symm)
    · intro h
      rw [h,map_zero]

-- Held accepted824 lines127–132 monotonicity engine; zero duplicate credit.
private theorem native_whole_mono {a : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel a) M] [IsComplexManifold a M]
    {B C : GermIdeal a M} (hBC : B.Le C) (p : M) :
    actualWholeSheafStalkIdeal B p≤actualWholeSheafStalkIdeal C p := by
  apply Ideal.span_le.mpr
  rintro _ ⟨g,hg,hm,rfl⟩
  exact Ideal.subset_span ⟨g,hg,hBC p g hm,rfl⟩

private theorem product_all_germs (t : parameterProduct F)
    (r : actualComplexStructureStalk (n:=n) (parameterMapOn F.Φ F.k t.1)) :
    productGerm F (originalProjectionParameterData F) t (ambientNative F t r)=
      HironakaRelativeNormalIdeal.tangentPullback F.k 1 (sourceGerm F t r) := by
  have he := congrArg (actualStalkChartEquiv (n:=F.k+1) (M:=parameterProduct F) t)
    (RingHom.congr_fun (product_native_square F t) r)
  calc
    _ = actualStalkChartEquiv (n:=F.k+1) (M:=parameterProduct F) t
        (parameterNative F t (sourceNative F t r)) := he
    _ = _ := by
      change actualStalkChartEquiv (n:=F.k+1) (M:=parameterProduct F) t
        ((ChartedSpace.locallyRingedSpaceMap
          (Prod.fst : parameterProduct F→parameterOpen F.Φ F.k)
          (ProductComplexManifold.contMDiff_fst (n:=F.k) (m:=1))).stalkMap t
          (sourceNative F t r)) = _
      rw [actualNativeStalk_chart_pullback,parameterProjection_germPullback]
      rfl

private theorem product_germ_square (t : parameterProduct F) :
    (productGerm F (originalProjectionParameterData F) t).comp (ambientNative F t)=
      (HironakaRelativeNormalIdeal.tangentPullback F.k 1).toRingHom.comp (sourceGerm F t) :=
  RingHom.ext (product_all_germs F t)

private theorem product_whole_ideal_image (B : GermIdeal n X) (hB : B.IsCoherent)
    (t : parameterProduct F) :
    Ideal.map (productGerm F (originalProjectionParameterData F) t) (nativeIdealPlus F B t)=
      Ideal.map (HironakaRelativeNormalIdeal.tangentPullback F.k 1).toRingHom
        (Ideal.map (sourceGerm F t) (nativeIdeal F B t)) := by
  rw [←projection_native_whole_ideal F B hB t,Ideal.map_map,product_germ_square,Ideal.map_map]

private def coherentProjectionQuotient (B : GermIdeal n X) (hB : B.IsCoherent)
    (hNB : (vanishingIdeal (n:=n) N).Le B) (t : parameterProduct F) :
    CoherentProjectionQuotient F (originalProjectionParameterData F) t B := by
  have hk : RingHom.ker (sourceGerm F t)≤nativeIdeal F B t := by
    rw [(source_germ_facts F t).2]
    exact native_whole_mono hNB _
  have hkplus : RingHom.ker (productGerm F (originalProjectionParameterData F) t)≤nativeIdealPlus F B t := by
    rw [(product_germ_facts F t).2,←projection_native_carrier_ideal F t,
      ←projection_native_whole_ideal F B hB t]
    exact Ideal.map_mono (native_whole_mono hNB _)
  refine nativeQuotientDiagram _ _ _ _ _ _
    (Ideal.Quotient.mk_surjective.comp (source_germ_facts F t).1)
    (Ideal.Quotient.mk_surjective.comp (product_germ_facts F t).1)
    (quotient_comp_kernel _ (source_germ_facts F t).1 _ hk) ?_
    (projection_native_whole_ideal F B hB t) ?_
  · exact quotient_comp_kernel_image _ (product_germ_facts F t).1 _ _
      (product_whole_ideal_image F B hB t) hkplus
  · ext r
    change Ideal.Quotient.mk _ (productGerm F (originalProjectionParameterData F) t (ambientNative F t r))=
      Ideal.Quotient.mk _ (HironakaRelativeNormalIdeal.tangentPullback F.k 1 (sourceGerm F t r))
    exact congrArg (Ideal.Quotient.mk _) (product_all_germs F t r)

-- Held elementary generator inclusion; identical accepted824 reasoning, zero engine credit.
private theorem carrier_le_original_log (_F : OriginalLogFrame A N E x) :
    (vanishingIdeal (n:=n) N).Le (logDerivIdealAlong N E A) := by
  intro p g hg
  change IsInSpanAt (fun s : X→ℂ => A.mem p s ∨ (vanishingIdeal (n:=n) N).mem p s ∨
    ∃ (e : ComplexChart n X) (ξ : Fin n→X→ℂ) (f : X→ℂ),
      IsLogTangentField N E e ξ p ∧ A.mem p f ∧ s=fieldDeriv e ξ f) p g
  exact isInSpanAt_of_eq_mul (Or.inr (Or.inl hg)) hg.1
    (holomorphicAt_const 1) (Eventually.of_forall fun _ => (one_mul _).symm)

private def originalLogProjectionQuotient (t : parameterProduct F) :
    OriginalLogProjectionQuotient F (originalProjectionParameterData F) t := by
  have hD : (logDerivIdealAlong N E A).IsCoherent := F.output.2.2.2.2.2.2.2.1
  have hmap : Ideal.map (sourceGerm F t) (nativeIdeal F (logDerivIdealAlong N E A) t)=
      oldLogTargetIdeal F t := (F.output.2.2.2.2.2.2.2.2 t.1).2.2.1
  have hk : RingHom.ker (sourceGerm F t)≤nativeIdeal F (logDerivIdealAlong N E A) t := by
    rw [(source_germ_facts F t).2]
    exact native_whole_mono (carrier_le_original_log F) _
  have hkplus : RingHom.ker (productGerm F (originalProjectionParameterData F) t)≤
      nativeIdealPlus F (logDerivIdealAlong N E A) t := by
    rw [(product_germ_facts F t).2,←projection_native_carrier_ideal F t,
      ←projection_native_whole_ideal F (logDerivIdealAlong N E A) hD t]
    exact Ideal.map_mono (native_whole_mono (carrier_le_original_log F) _)
  have hmapplus : Ideal.map (productGerm F (originalProjectionParameterData F) t)
      (nativeIdealPlus F (logDerivIdealAlong N E A) t)=
      Ideal.map (HironakaRelativeNormalIdeal.tangentPullback F.k 1).toRingHom (oldLogTargetIdeal F t) := by
    rw [product_whole_ideal_image F (logDerivIdealAlong N E A) hD t,hmap]
  refine nativeQuotientDiagram _ _ _ _ _ _
    (Ideal.Quotient.mk_surjective.comp (source_germ_facts F t).1)
    (Ideal.Quotient.mk_surjective.comp (product_germ_facts F t).1)
    (quotient_comp_kernel_image _ (source_germ_facts F t).1 _ _ hmap hk)
    (quotient_comp_kernel_image _ (product_germ_facts F t).1 _ _ hmapplus hkplus)
    (projection_native_whole_ideal F (logDerivIdealAlong N E A) hD t) ?_
  ext r
  change Ideal.Quotient.mk _ (productGerm F (originalProjectionParameterData F) t (ambientNative F t r))=
    Ideal.Quotient.mk _ (HironakaRelativeNormalIdeal.tangentPullback F.k 1 (sourceGerm F t r))
  exact congrArg (Ideal.Quotient.mk _) (product_all_germs F t r)

private theorem retained_original_log : outputField_retained_original_log F (originalProjectionParameterData F) := by
  intro t eOld heOld
  exact ⟨originalLogProjectionQuotient F t,
    nativeQuotientDiagram_retains (originalLogProjectionQuotient F t) eOld heOld⟩

private theorem stalkTransport_originalFunction {d : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsComplexManifold d M]
    {p q : M} (h : p=q) (g : M→ℂ) (hg : HolomorphicAt d g p) :
    stalkTransport h (actualOriginalFunctionGerm p g hg)=
      actualOriginalFunctionGerm q g (h ▸ hg) := by
  cases h
  rfl

private theorem factory_all_germs : outputField_factory_all_germs F (originalProjectionParameterData F) := by
  intro w r
  obtain ⟨g,hg,rfl⟩ := exists_original_stalk_function
    (productParameterMap F (sameParameterRho F.Φ F.k F.hk w)) r
  change parameterGermPullback (X:=projectionAmbient X) (shiftedProductChart F.Φ F.k F.hk)
    (F.k+1) (shifted_source F.Φ F.k F.hk F.hsrc) w
    (stalkTransport (shifted_parameterMap F.Φ F.k F.hk w).symm
      (actualOriginalFunctionGerm _ g hg)) = _
  erw [stalkTransport_originalFunction]
  change actualStalkChartEquiv (n:=F.k+1) w
      ((ChartedSpace.locallyRingedSpaceMap
        (parameterMapOn (X:=projectionAmbient X) (shiftedProductChart F.Φ F.k F.hk) (F.k+1))
        (parameterMapOn_contMDiff (X:=projectionAmbient X) (shiftedProductChart F.Φ F.k F.hk)
          (F.k+1) (shifted_source F.Φ F.k F.hk F.hsrc))).stalkMap w
        (actualOriginalFunctionGerm _ g _)) =
    actualStalkChartEquiv (n:=F.k+1) (M:=parameterProduct F) (sameParameterRho F.Φ F.k F.hk w)
      ((ChartedSpace.locallyRingedSpaceMap (productParameterMap F)
        (productParameterMap_holo F)).stalkMap (sameParameterRho F.Φ F.k F.hk w)
        (actualOriginalFunctionGerm _ g hg))
  rw [←rho_all_native_germs F w]
  apply congrArg (actualStalkChartEquiv (n:=F.k+1) w)
  erw [native_stalk_original_function,native_stalk_original_function,native_stalk_original_function]
  apply original_stalk_function_congr
  exact Eventually.of_forall fun u => congrArg g (shifted_parameterMap F.Φ F.k F.hk u)

private theorem projection_records : outputField_projection_records F (originalProjectionParameterData F) := by
  intro M hMN hME hMA
  refine ⟨?_,?_,?_,rfl,?_,?_,?_,?_⟩
  · change (Prod.fst : projectionAmbient X→X) ⁻¹' M.N=(Prod.fst : projectionAmbient X→X) ⁻¹' N
    rw [hMN]
  · change M.E.map ((Prod.fst : projectionAmbient X→X) ⁻¹' ·) ++ [horizontal X]=projectedBoundary F
    rw [hME]
    rfl
  · change GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X) M.ideal=pulled F A
    rw [hMA]
  · change (M.E.map ((Prod.fst : projectionAmbient X→X) ⁻¹' ·) ++ [horizontal X]).length=E.length+1
    simp only [List.length_append,List.length_map,List.length_singleton,hME]
  · intro i
    change (M.E.map ((Prod.fst : projectionAmbient X→X) ⁻¹' ·) ++ [horizontal X])[i.val]'(by simp only [List.length_append,List.length_map,List.length_singleton,hME]; omega)=_
    rw [List.getElem_append_left (by simpa only [List.length_map,hME] using i.isLt),List.getElem_map]
    simp only [hME,List.get_eq_getElem]
  · change (M.E.map ((Prod.fst : projectionAmbient X→X) ⁻¹' ·) ++ [horizontal X]).getLastD ∅=horizontal X
    simp
  · intro s hD
    exact projection_test_isInvDomain M hD

private def originalProjectionOutput : ProjectionCarrierQuotientOutput F where
  geometry := originalProjectionParameterData F
  carrier := productCarrierQuotient F (originalProjectionParameterData F)
  all_germs := product_all_germs F
  factory_all_germs := factory_all_germs F
  every_coherent_ideal := by
    intro B hB t
    exact ⟨projection_native_whole_ideal F B hB t,product_whole_ideal_image F B hB t,
      fun hNB => ⟨coherentProjectionQuotient F B hB hNB t⟩⟩
  retained_original_log := retained_original_log F
  source_scalar := nativeScalarLaws _ (parameterMapOn_contMDiff F.Φ F.k F.hsrc)
  product_scalar := nativeScalarLaws _ (productParameterMap_holo F)
  ambient_scalar := nativeScalarLaws _ (ProductComplexManifold.contMDiff_fst (n:=n) (m:=1))
  parameter_scalar := nativeScalarLaws _ (ProductComplexManifold.contMDiff_fst (n:=F.k) (m:=1))
  factory_scalar := nativeScalarLaws _ (parameterMapOn_contMDiff (X:=projectionAmbient X)
    (shiftedProductChart F.Φ F.k F.hk) (F.k+1) (shifted_source F.Φ F.k F.hk F.hsrc))
  rho_scalar := nativeScalarLaws _ (sameParameterRho F.Φ F.k F.hk).contMDiff
  rho_inverse_scalar := nativeScalarLaws _ (sameParameterRho F.Φ F.k F.hk).symm.contMDiff
  projection_records := projection_records F

end ProductGeometry

/-- One original824 choice precedes all product parameters, ideals, numerators and scalars. -/
theorem exists_actual_projection_carrier_quotient_dictionary
    {n : ℕ} {X : CMfd.{0} n} {N : Set X} {E : List (Set X)}
    (A : GermIdeal n X) (hA : A.IsCoherent) (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n E) (hTr : IsTransverse n N E) (x : X) (hx : x∈N) :
    ∃ F : OriginalLogFrame A N E x,Nonempty (ProjectionCarrierQuotientOutput F) := by
  obtain ⟨k,hk,Φ,κ,τ,hsrc,hout⟩ :=
    exists_actual_intrinsic_log_quotient_dictionary A hA hN hE hTr x hx
  let F : OriginalLogFrame A N E x := ⟨hA,hN,hE,hTr,k,hk,Φ,κ,τ,hsrc,hout⟩
  exact ⟨F,⟨originalProjectionOutput F⟩⟩

end
end Hironaka.HironakaActualProjectionCarrierQuotientDictionary
