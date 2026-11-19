import Hironaka.Resolution.HironakaActualHistoricalMovingPrefixSupport

/-! Actual moving contact and nonzero block Jacobians for the SAME
historical selector. Origin monicity is used only to derive the original
determinants; no translated monicity or target rank is assumed. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualHistoricalMovingSelectedContact
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf OkaIdealOperations
 HironakaRelativeNormalMonomialBasis HironakaActualCoefficientPresentationCentrePower
 HironakaActualRelativeNormalJetDivision HironakaActualFormalInitialDiagram
 HironakaActualInheritedAnalyticBlockJacobian HironakaActualCanonicalBlockJacobian
 HironakaActualInheritedNestedContactFlag HironakaActualFixedInheritedSelector
 HironakaActualSelectedContactCarriers HironakaActualWholeHSContactWindow
 HironakaRelativeNormalTaylorCoefficients HolomorphicTaylorTail
 HironakaActualNormalZeroAnalyticSaturation HironakaActualOriginalFormalHSTransfer
 HironakaActualDiagonalTaylor HironakaActualGeometricCurrentNeighborhoodHS
 HironakaHolomorphicJetRankLoci HironakaHolomorphicJetChartInvariance
 HironakaActualHistoricalWholeJetFrames HironakaActualHistoricalPrefixJetFrames
 HironakaActualHistoricalFormalSupportedDivision HironakaActualHistoricalMovingPrefixSupport
 HironakaActualAnalyticFormalNormalPowers HironakaHolomorphicJetMonomialSpan
 HironakaActualAnalyticBlockGraphTranslation
 HironakaActualCauchyCoordinateDivision HironakaActualInheritedSmallTails
 HironakaActualOriginalScaledAnalyticDivision HironakaActualInheritedNeighborhoodStandardJets
 HironakaActualFiniteDegLexWeights HironakaActualWeightedVertexSmallTails
 HironakaActualCauchyMonomialDivision HironakaHolomorphicPointJets

variable {n : ℕ}

/-- The exact scalar picked up by one whole coordinate derivative under a
diagonal change. No invertibility is needed for this identity. -/
theorem actual_coordinate_derivative_diagonal (c : Fin n → ℂ) (i : Fin n)
    (F : HolGerm (ComplexModel n)) :
    actualAnalyticCoordinateDerivative i (actualDiagonalPullback c F)=
      c i • actualDiagonalPullback c (actualAnalyticCoordinateDerivative i F) := by
  apply actualUnshiftedTaylorAlgHom_injective n
  ext α
  rw [actualTaylor_actualAnalyticCoordinateDerivative,MvPowerSeries.coeff_pderiv,
    coeff_actualDiagonalPullback,map_smul,map_smul,coeff_actualDiagonalPullback,
    actualTaylor_actualAnalyticCoordinateDerivative,MvPowerSeries.coeff_pderiv]
  have hWeight : (α+Finsupp.single i 1).prod (fun j d=>c j^d)=
      (α.prod fun j d=>c j^d)*c i := by
    have hSingle : (Finsupp.single i 1).prod (fun j d=>c j^d)=c i := by
      simpa only [pow_one] using (Finsupp.prod_single_index
        (a:=i) (b:=1) (h:=fun j d=>c j^d) (pow_zero (c i)))
    rw [Finsupp.prod_add_index' (fun _=>pow_zero _) (fun _ _ _=>pow_add _ _ _),hSingle]
  rw [hWeight]
  simp only [smul_eq_mul]
  ring

def actualDerivativeWordScale (c : Fin n → ℂ) (L : List (Fin n)) : ℂ :=
  (L.map c).prod

theorem actual_word_derivative_diagonal (c : Fin n → ℂ) (L : List (Fin n))
    (F : HolGerm (ComplexModel n)) :
    actualAnalyticWordDerivative L (actualDiagonalPullback c F)=
      actualDerivativeWordScale c L • actualDiagonalPullback c (actualAnalyticWordDerivative L F) := by
  induction L with
  | nil =>
      have hNil (g : HolGerm (ComplexModel n)) : actualAnalyticWordDerivative [] g=g := by
        induction g using HolGerm.induction_on with
        | h f hf => rfl
      rw [hNil,hNil]
      exact (one_smul ℂ _).symm
  | cons i L ih =>
      rw [actualAnalyticWordDerivative_cons,ih,map_smul,actual_coordinate_derivative_diagonal,
        smul_smul,actualAnalyticWordDerivative_cons]
      simp only [actualDerivativeWordScale,List.map_cons,List.prod_cons]
      rw [mul_comm]

theorem actual_multi_derivative_diagonal (c : Fin n → ℂ) (β : Fin n →₀ ℕ)
    (F : HolGerm (ComplexModel n)) :
    actualAnalyticMultiDerivative β (actualDiagonalPullback c F)=
      actualDerivativeWordScale c (actualCoordinateDerivativeWord β) •
        actualDiagonalPullback c (actualAnalyticMultiDerivative β F) :=
  actual_word_derivative_diagonal c (actualCoordinateDerivativeWord β) F

theorem actualDerivativeWordScale_ne_zero (c : Fin n → ℂ) (hc : ∀i,c i≠0)
    (L : List (Fin n)) : actualDerivativeWordScale c L≠0 := by
  induction L with
  | nil => exact one_ne_zero
  | cons i L ih => exact mul_ne_zero (hc i) ih

/-- Actual origin contact supplies a coefficient matrix whose evaluation is
the literal historical block Jacobian. This records the factorization that
can be spread to nearby points, rather than only its zero set. -/
theorem actual_selected_contact_coefficient_matrix
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (G : V → HolGerm (ComplexModel n)) (k : ℕ)
    (hContact : actualFixedSelectorContactAt S G k) :
    ∃M : Matrix (fixedSelectorBlock V k) (fixedSelectorBlock V k) (HolGerm (ComplexModel n)),
      (∀j,∑i,M j i*coordinateGerm i.val=
        actualFixedSelectorDerivative S G (fixedSelectorBlockEssential k j)) ∧
      Matrix.map M HolGerm.eval=actualFixedSelectorJacobian S G k := by
  let B:=fixedSelectorBlock V k
  let F : B → HolGerm (ComplexModel n):=fun j=>actualFixedSelectorDerivative S G (fixedSelectorBlockEssential k j)
  let x : B → HolGerm (ComplexModel n):=fun j=>coordinateGerm j.val
  have hCoord : actualAnalyticCoordinateBlockIdeal B=Ideal.span (range x) := by
    unfold actualAnalyticCoordinateBlockIdeal
    congr 1
    ext g
    constructor
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨i,hi⟩,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨i.val,i.property,rfl⟩
  have hMem (j : B) : F j∈Ideal.span (range x):=by
    rw [←hCoord]
    exact hContact j
  choose M hM using fun j=>Ideal.mem_span_range_iff_exists_fun.mp (hMem j)
  refine ⟨M,hM,?_⟩
  ext j i
  change HolGerm.eval (M j i)=HolGerm.eval (actualAnalyticCoordinateDerivative i.val (F j))
  rw [←hM j,map_sum,map_sum]
  dsimp only [x]
  simp_rw [coordinate_derivative_eval_mul_coordinate]
  simp only [Subtype.val_inj,Finset.sum_ite_eq',Finset.mem_univ,if_true]

/-- A whole block factorization computes the actual Jacobian, including
empty blocks. -/
theorem coordinate_block_jacobian_of_factorization
    (B : Set (Fin n)) [Fintype B] (H : B → HolGerm (ComplexModel n))
    (M : Matrix B B (HolGerm (ComplexModel n)))
    (hM : ∀j,∑i,M j i*coordinateGerm i.val=H j) :
    Matrix.map M HolGerm.eval=
      fun j i=>HolGerm.eval (actualAnalyticCoordinateDerivative i.val (H j)) := by
  ext j i
  change HolGerm.eval (M j i)=HolGerm.eval (actualAnalyticCoordinateDerivative i.val (H j))
  rw [←hM j,map_sum,map_sum]
  simp_rw [coordinate_derivative_eval_mul_coordinate]
  simp only [Subtype.val_inj,Finset.sum_ite_eq',Finset.mem_univ,if_true]

theorem coordinate_block_contact_of_factorization
    (B : Set (Fin n)) [Fintype B] (H : B → HolGerm (ComplexModel n))
    (M : Matrix B B (HolGerm (ComplexModel n)))
    (hM : ∀j,∑i,M j i*coordinateGerm i.val=H j) :
    ∀j,H j∈actualAnalyticCoordinateBlockIdeal B := by
  intro j
  rw [←hM j]
  exact Ideal.sum_mem _ fun i _=>Ideal.mul_mem_left _ _
    (Ideal.subset_span ⟨i.val,i.property,rfl⟩)

/-- Spread the literal origin coefficient matrix to one genuine open.
At points on the same coordinate plane, translation retains its ENTIRE
factorization and a nonzero evaluated determinant. -/
theorem exists_moving_coordinate_block_factorization
    (B : Set (Fin n)) [Fintype B] (H : B → HolGerm (ComplexModel n))
    (M : Matrix B B (HolGerm (ComplexModel n)))
    (hM : ∀j,∑i,M j i*coordinateGerm i.val=H j)
    (hdet : (Matrix.map M HolGerm.eval).det≠0)
    (f : B → ComplexModel n → ℂ) (hf : ∀j,HolAt (f j) 0)
    (hRep : ∀j,HolGerm.mk (f j) (hf j)=H j) :
    ∃U : Set (ComplexModel n),IsOpen U ∧ (0 : ComplexModel n)∈U ∧
      ∀u∈U,(∀i : B,u i.val=0) →
        ∃hfU : ∀j,HolAt (f j) u,
        ∃Mu : Matrix B B (HolGerm (ComplexModel n)),
          (∀j,∑i,Mu j i*coordinateGerm i.val=translatedGerm u (f j) (hfU j)) ∧
          (Matrix.map Mu HolGerm.eval).det≠0 := by
  choose a ha hmk using fun j i=>HolGerm.exists_eq_mk (M j i)
  have hProd (j i : B) : HolAt (fun z=>a j i z*z i.val) 0:=
    (ha j i).mono fun z hz=>hz.mul
      (EuclideanSpace.proj i.val : ComplexModel n →L[ℂ] ℂ).differentiableAt
  have hSum (j : B) :
      HolGerm.mk (fun z=>∑i,a j i z*z i.val)
        (eventually_differentiableAt_sum _ (hProd j))=HolGerm.mk (f j) (hf j) := by
    rw [HolGerm.mk_sum Finset.univ (fun i z=>a j i z*z i.val) (hProd j),hRep j]
    calc
      ∑i,HolGerm.mk (fun z=>a j i z*z i.val) (hProd j i)=
          ∑i,M j i*coordinateGerm i.val := by
        apply Finset.sum_congr rfl
        intro i _
        rw [HolGerm.mk_mul (a j i) (fun z=>z i.val) (ha j i)
          (Eventually.of_forall fun _=>(EuclideanSpace.proj i.val : ComplexModel n →L[ℂ] ℂ).differentiableAt),
          ←hmk j i]
        rfl
      _=H j:=hM j
  have hEq : ∀ᶠz in 𝓝 (0 : ComplexModel n),∀j,∑i,a j i z*z i.val=f j z:=
    eventually_all.mpr fun j=>HolGerm.mk_eq_mk_iff.mp (hSum j)
  have hAAt : ContinuousAt (fun z=>fun j i : B=>a j i z) (0 : ComplexModel n):=
    continuousAt_pi.mpr fun j=>continuousAt_pi.mpr fun i=>(ha j i).self_of_nhds.continuousAt
  have hDAt : ContinuousAt (fun z=>Matrix.det (fun j i : B=>a j i z)) (0 : ComplexModel n):=
    (continuous_id.matrix_det.continuousAt).comp hAAt
  have h0det : Matrix.det (fun j i : B=>a j i 0)≠0 := by
    have hEval : (fun j i : B=>a j i 0)=Matrix.map M HolGerm.eval := by
      ext j i
      rw [Matrix.map_apply,hmk j i,HolGerm.eval_mk]
    rw [hEval]
    exact hdet
  have hDetNear : ∀ᶠz in 𝓝 (0 : ComplexModel n),Matrix.det (fun j i : B=>a j i z)≠0:=
    hDAt.eventually (isOpen_ne.mem_nhds h0det)
  have hHolA : ∀ᶠz in 𝓝 (0 : ComplexModel n),∀j i,DifferentiableAt ℂ (a j i) z:=
    eventually_all.mpr fun j=>eventually_all.mpr fun i=>ha j i
  have hHolF : ∀ᶠz in 𝓝 (0 : ComplexModel n),∀j,DifferentiableAt ℂ (f j) z:=
    eventually_all.mpr hf
  obtain ⟨U,hUsub,hU,h0U⟩:=mem_nhds_iff.mp (hEq.and (hDetNear.and (hHolA.and hHolF)))
  refine ⟨U,hU,h0U,?_⟩
  intro u hu hPlane
  have hAu (j i : B) : HolAt (a j i) u:=
    (show ∀ᶠz in 𝓝 u,z∈U from hU.mem_nhds hu).mono fun z hz=>(hUsub hz).2.2.1 j i
  have hFu (j : B) : HolAt (f j) u:=
    (show ∀ᶠz in 𝓝 u,z∈U from hU.mem_nhds hu).mono fun z hz=>(hUsub hz).2.2.2 j
  let Mu : Matrix B B (HolGerm (ComplexModel n)):=fun j i=>translatedGerm u (a j i) (hAu j i)
  refine ⟨hFu,Mu,?_,?_⟩
  · intro j
    have hProdU (i : B) : HolAt (fun z=>a j i (z+u)*z i.val) 0:=
      (translated_holomorphic u (hAu j i)).mono fun z hz=>hz.mul
        (EuclideanSpace.proj i.val : ComplexModel n →L[ℂ] ℂ).differentiableAt
    have hExpand : (∑i,Mu j i*coordinateGerm i.val)=
        HolGerm.mk (fun z=>∑i,a j i (z+u)*z i.val) (eventually_differentiableAt_sum _ hProdU) := by
      rw [HolGerm.mk_sum Finset.univ _ hProdU]
      apply Finset.sum_congr rfl
      intro i _
      rw [HolGerm.mk_mul (fun z=>a j i (z+u)) (fun z=>z i.val)
        (translated_holomorphic u (hAu j i))
        (Eventually.of_forall fun _=>(EuclideanSpace.proj i.val : ComplexModel n →L[ℂ] ℂ).differentiableAt)]
      rfl
    rw [hExpand]
    apply HolGerm.mk_eq_mk_iff.mpr
    have ht : Tendsto (fun z : ComplexModel n=>z+u) (𝓝 0) (𝓝 u):=by
      simpa only [id_eq,zero_add] using (continuous_id.add_const u).tendsto (0 : ComplexModel n)
    filter_upwards [ht.eventually (hU.mem_nhds hu)] with z hz
    have he:=(hUsub hz).1 j
    have hCoord (i : B) : (z+u) i.val=z i.val := by
      change z i.val+u i.val=z i.val
      rw [hPlane i,add_zero]
    simpa only [hCoord] using he
  · have hEval : Matrix.map Mu HolGerm.eval=fun j i : B=>a j i u := by
      ext j i
      change HolGerm.eval (translatedGerm u (a j i) (hAu j i))=a j i u
      rw [translatedGerm,HolGerm.eval_mk,zero_add]
    rw [hEval]
    exact (hUsub hu).2.1

/-- A total coordinate-indexed version lets literal block equality transport
both contact and determinants without changing any selector label. -/
def actualSelectedCoordinateDerivative {V : Finset (Fin n →₀ ℕ)}
    (S : ActualFixedInheritedSelector V) (G : V → HolGerm (ComplexModel n))
    (i : Fin n) : HolGerm (ComplexModel n) :=
  if hi : i∈fixedSelectorEssential V then actualFixedSelectorDerivative S G ⟨i,hi⟩ else 0

theorem actualSelectedCoordinateDerivative_on_block
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (G : V → HolGerm (ComplexModel n)) (k : ℕ) (j : fixedSelectorBlock V k) :
    actualSelectedCoordinateDerivative S G j.val=
      actualFixedSelectorDerivative S G (fixedSelectorBlockEssential k j) := by
  have hj : j.val∈fixedSelectorEssential V:=(fixedSelectorBlockEssential k j).property
  rw [actualSelectedCoordinateDerivative,dif_pos hj]
  rfl

def ActualSelectedContactByBlock {V : Finset (Fin n →₀ ℕ)}
    (S : ActualFixedInheritedSelector V) (G : V → HolGerm (ComplexModel n))
    (B : Set (Fin n)) : Prop :=
  (∀j : B,actualSelectedCoordinateDerivative S G j.val∈actualAnalyticCoordinateBlockIdeal B) ∧
    Matrix.det (fun j i : B=>HolGerm.eval (actualAnalyticCoordinateDerivative i.val
      (actualSelectedCoordinateDerivative S G j.val)))≠0

theorem actualSelectedContactByBlock_iff
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (G : V → HolGerm (ComplexModel n)) (k : ℕ) :
    ActualSelectedContactByBlock S G (fixedSelectorBlock V k) ↔
      actualFixedSelectorContactAt S G k ∧ (actualFixedSelectorJacobian S G k).det≠0 := by
  unfold ActualSelectedContactByBlock actualFixedSelectorContactAt actualFixedSelectorJacobian
  simp only [actualSelectedCoordinateDerivative_on_block]

theorem actual_contact_fixedSelectorBlock_min (V : Finset (Fin n →₀ ℕ)) (k : ℕ) :
    fixedSelectorBlock V (min k (V.sup normalExponentDegree))=fixedSelectorBlock V k := by
  ext i
  constructor
  · rintro ⟨a,ha,hai⟩
    exact ⟨a,ha.trans (min_le_left _ _),hai⟩
  · rintro ⟨a,ha,hai⟩
    exact ⟨a,le_min ha (Finset.le_sup a.property),hai⟩

section GeometricSource
variable {I : Ideal (HolGerm (ComplexModel n))}
 {G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)}

def actualNativeHistoricalFamily
    {A : GermIdeal n (ComplexModel n)} {R : ℕ → ℕ}
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R)
    (u : ComplexModel n) (hu : u∈PHS.neighborhood) :
    actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I) → HolGerm (ComplexModel n) :=
  fun a=>translatedGerm u (PHS.representatives a) (PHS.holomorphicAt _ hu a)

/-- ONE native neighbourhood preserves ENTIRE selected derivative contact
and every actual block Jacobian at EVERY reference-HS point. The same
origin selector is retained and moving monicity is not required. -/
theorem exists_actual_native_moving_selected_contact
    {A : GermIdeal n (ComplexModel n)} {R : ℕ → ℕ}
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)))
    (hContact : ∀k,actualFixedSelectorContactAt S G.germs k) :
    ∃U : Set (ComplexModel n),IsOpen U ∧ (0 : ComplexModel n)∈U ∧ U⊆PHS.neighborhood ∧
      ∀u∈U,∀hu : u∈PHS.neighborhood,
        (∀ℓ,hilbertSamuelAt A u ℓ=R ℓ) →
          ∀k,actualFixedSelectorContactAt S (actualNativeHistoricalFamily PHS u hu) k ∧
            (actualFixedSelectorJacobian S (actualNativeHistoricalFamily PHS u hu) k).det≠0 := by
  let V:=actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)
  let f : fixedSelectorEssential V → ComplexModel n → ℂ:=fun j=>
    iterDeriv ((actualCoordinateDerivativeWord (fixedSelectorBeta S j)).map
      (fun i=>EuclideanSpace.single i (1 : ℂ))) (PHS.representatives (S.selected j))
  have hf (j : fixedSelectorEssential V) : HolAt (f j) 0:=
    eventually_holomorphic_iterDeriv (PHS.holomorphicAtZero (S.selected j)) _
  have hRep (j : fixedSelectorEssential V) : HolGerm.mk (f j) (hf j)=
      actualFixedSelectorDerivative S G.germs j := by
    rw [actualFixedSelectorDerivative,←PHS.sameGerms (S.selected j),
      actualAnalyticMultiDerivative,actualAnalyticWordDerivative,iteratedDerivativeGerm_mk]
  have hOne (k : ℕ) : ∀ᶠu in 𝓝 (0 : ComplexModel n),∀hu : u∈PHS.neighborhood,
      (∀i∈fixedSelectorBlock V k,u i=0) →
        ActualSelectedContactByBlock S (actualNativeHistoricalFamily PHS u hu) (fixedSelectorBlock V k) := by
    obtain ⟨M,hM,hMatrix⟩:=actual_selected_contact_coefficient_matrix S G.germs k (hContact k)
    have hdet : (Matrix.map M HolGerm.eval).det≠0:=by
      rw [hMatrix]
      exact actualFixedSelectorJacobian_det_ne_zero S G.germs G.monic G.lower k
    obtain ⟨O,hO,h0O,hSpread⟩:=exists_moving_coordinate_block_factorization
      (fixedSelectorBlock V k) _ M hM hdet
      (fun j=>f (fixedSelectorBlockEssential k j)) (fun j=>hf _) (fun j=>hRep _)
    filter_upwards [hO.mem_nhds h0O] with u huO hu hPlane
    obtain ⟨hFu,Mu,hMu,hMuDet⟩:=hSpread u huO (fun i=>hPlane i.val i.property)
    let GN:=actualNativeHistoricalFamily PHS u hu
    have hDerivative (j : fixedSelectorBlock V k) :
        actualFixedSelectorDerivative S GN (fixedSelectorBlockEssential k j)=
          translatedGerm u (f (fixedSelectorBlockEssential k j)) (hFu j) :=
      actualAnalyticMultiDerivative_translatedGerm _ u _ (PHS.holomorphicAt _ hu _) (hFu j)
    have hFactor (j : fixedSelectorBlock V k) :
        ∑i,Mu j i*coordinateGerm i.val=actualFixedSelectorDerivative S GN (fixedSelectorBlockEssential k j):=by
      rw [hDerivative]
      exact hMu j
    apply (actualSelectedContactByBlock_iff S GN k).mpr
    refine ⟨coordinate_block_contact_of_factorization _ _ Mu hFactor,?_⟩
    have hJac:=coordinate_block_jacobian_of_factorization _ _ Mu hFactor
    change Matrix.map Mu HolGerm.eval=actualFixedSelectorJacobian S GN k at hJac
    rw [←hJac]
    exact hMuDet
  let K:=V.sup normalExponentDegree
  have hAll : ∀ᶠu in 𝓝 (0 : ComplexModel n),∀r : Fin (K+1),∀hu : u∈PHS.neighborhood,
      (∀i∈fixedSelectorBlock V r.val,u i=0) →
        ActualSelectedContactByBlock S (actualNativeHistoricalFamily PHS u hu) (fixedSelectorBlock V r.val):=
    eventually_all.mpr fun r=>hOne r.val
  obtain ⟨O,hOsub,hO,h0O⟩:=mem_nhds_iff.mp hAll
  obtain ⟨U,hU,h0U,hUP,hUO,hPlane⟩:=
    exists_actual_whole_hs_coordinate_contact_window PHS S hContact f hf hRep O hO h0O
  refine ⟨U,hU,h0U,hUP,?_⟩
  intro u hu huP hHS k
  have hLow:=(hOsub (hUO hu)) (⟨min k K,by omega⟩ : Fin (K+1)) huP
    ((hPlane u hu hHS).2 (min k K))
  have hBlock : fixedSelectorBlock V (min k K)=fixedSelectorBlock V k:=
    actual_contact_fixedSelectorBlock_min V k
  have hFinal:=Eq.mp (congrArg (ActualSelectedContactByBlock S (actualNativeHistoricalFamily PHS u huP)) hBlock) hLow
  exact (actualSelectedContactByBlock_iff S _ k).mp hFinal

/-- Diagonal pullback fixes the evaluation point even when a diagonal entry
vanishes. -/
theorem actualDiagonalPullback_eval (c : Fin n → ℂ) (F : HolGerm (ComplexModel n)) :
    HolGerm.eval (actualDiagonalPullback c F)=HolGerm.eval F := by
  rw [←HironakaActualCauchyCoefficientLimits.actualTaylor_coeff_zero,
    coeff_actualDiagonalPullback,Finsupp.prod_zero_index,one_mul,
    HironakaActualCauchyCoefficientLimits.actualTaylor_coeff_zero]

theorem actualHolGerm_eval_smul (r : ℂ) (F : HolGerm (ComplexModel n)) :
    HolGerm.eval (r • F)=r*HolGerm.eval F := by
  change HolGerm.eval (HolGerm.constHom r*F)=r*HolGerm.eval F
  rw [map_mul,HolGerm.eval_constHom]

theorem actualDiagonalPullback_mem_coordinate_block (c : Fin n → ℂ)
    (B : Set (Fin n)) (F : HolGerm (ComplexModel n))
    (hF : F∈actualAnalyticCoordinateBlockIdeal B) :
    actualDiagonalPullback c F∈actualAnalyticCoordinateBlockIdeal B := by
  have hLe : Ideal.map (actualDiagonalPullback c).toRingHom
      (actualAnalyticCoordinateBlockIdeal B)≤actualAnalyticCoordinateBlockIdeal B := by
    apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    change actualDiagonalPullback c (coordinateGerm i)∈actualAnalyticCoordinateBlockIdeal B
    rw [actualDiagonalPullback_coordinate]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i,hi,rfl⟩)
  exact hLe (Ideal.mem_map_of_mem (actualDiagonalPullback c).toRingHom hF)

def actualSelectedDiagonalRowFactor {V : Finset (Fin n →₀ ℕ)}
    (S : ActualFixedInheritedSelector V) (c : Fin n → ℂ) (r : V → ℂ)
    (j : fixedSelectorEssential V) : ℂ :=
  r (S.selected j)*actualDerivativeWordScale c (actualCoordinateDerivativeWord (fixedSelectorBeta S j))

theorem actual_selected_derivative_diagonal_rows
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (c : Fin n → ℂ) (r : V → ℂ) (GN : V → HolGerm (ComplexModel n))
    (j : fixedSelectorEssential V) :
    actualFixedSelectorDerivative S (fun a=>r a • actualDiagonalPullback c (GN a)) j=
      actualSelectedDiagonalRowFactor S c r j • actualDiagonalPullback c (actualFixedSelectorDerivative S GN j) := by
  unfold actualFixedSelectorDerivative actualSelectedDiagonalRowFactor
  rw [map_smul,actual_multi_derivative_diagonal,smul_smul]

/-- Literal row units and diagonal coordinates preserve whole historical
contact and multiply each Jacobian by explicit nonzero row/column factors. -/
theorem actual_selected_contact_diagonal_rows
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (c : Fin n → ℂ) (hc : ∀i,c i≠0) (r : V → ℂ) (hr : ∀a,r a≠0)
    (GN : V → HolGerm (ComplexModel n)) (k : ℕ)
    (hContact : actualFixedSelectorContactAt S GN k)
    (hdet : (actualFixedSelectorJacobian S GN k).det≠0) :
    actualFixedSelectorContactAt S (fun a=>r a • actualDiagonalPullback c (GN a)) k ∧
      (actualFixedSelectorJacobian S (fun a=>r a • actualDiagonalPullback c (GN a)) k).det≠0 := by
  have hRow (j : fixedSelectorEssential V) : actualSelectedDiagonalRowFactor S c r j≠0:=
    mul_ne_zero (hr _) (actualDerivativeWordScale_ne_zero c hc _)
  refine ⟨?_,?_⟩
  · intro j
    rw [actual_selected_derivative_diagonal_rows]
    exact Submodule.smul_mem _ _ (actualDiagonalPullback_mem_coordinate_block c _ _ (hContact j))
  let B:=fixedSelectorBlock V k
  let row : B → ℂ:=fun j=>actualSelectedDiagonalRowFactor S c r (fixedSelectorBlockEssential k j)
  let col : B → ℂ:=fun i=>c i.val
  let J : Matrix B B ℂ:=actualFixedSelectorJacobian S GN k
  have hJac : actualFixedSelectorJacobian S (fun a=>r a • actualDiagonalPullback c (GN a)) k=
      Matrix.of (fun j i : B=>row j*(col i*J j i)) := by
    ext j i
    change HolGerm.eval (actualAnalyticCoordinateDerivative i.val
      (actualFixedSelectorDerivative S (fun a=>r a • actualDiagonalPullback c (GN a))
        (fixedSelectorBlockEssential k j)))=row j*(col i*J j i)
    rw [actual_selected_derivative_diagonal_rows,map_smul,actual_coordinate_derivative_diagonal,
      actualHolGerm_eval_smul,actualHolGerm_eval_smul,actualDiagonalPullback_eval]
    rfl
  have hInner : Matrix.det (Matrix.of (fun j i : B=>col i*J j i))=
      (∏i,col i)*J.det:=Matrix.det_mul_row col J
  have hOuter : Matrix.det (Matrix.of (fun j i : B=>row j*(col i*J j i)))=
      (∏j,row j)*Matrix.det (Matrix.of (fun j i : B=>col i*J j i)):=
    Matrix.det_mul_column row (Matrix.of (fun j i : B=>col i*J j i))
  rw [hJac,hOuter,hInner]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun j _=>hRow _))
    (mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _=>hc _)) hdet)

theorem actual_scaled_moving_selected_contact
    {A : GermIdeal n (ComplexModel n)} {R : ℕ → ℕ}
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)))
    (P : ActualInheritedWeightedTailData G) {s : ℂ} (hs0 : s≠0) (hs : s∈Metric.ball 0 P.radius)
    (p : CoordinateSpace n)
    (hdom : MapsTo (fun z=>p+z) (Metric.ball 0 (P.radius/2)) (Metric.ball 0 P.radius))
    (hu : scaledOriginalPoint P s p∈PHS.neighborhood)
    (hCov : ∀j : Fin (actualVertexCount n I),
      let a:=actualVertexEnumeration n I j
      let W:=degLexWeight n P.germs.degreeBound
      actualInheritedTranslatedGerm P hs p hdom j=
        HolGerm.constHom ((s^weightedDegree W a.val)⁻¹)*actualDiagonalPullback (fun i=>s^W i)
          (translatedGerm (scaledOriginalPoint P s p) (PHS.representatives a) (PHS.holomorphicAt _ hu a)))
    (hNative : ∀k,actualFixedSelectorContactAt S (actualNativeHistoricalFamily PHS (scaledOriginalPoint P s p) hu) k ∧
      (actualFixedSelectorJacobian S (actualNativeHistoricalFamily PHS (scaledOriginalPoint P s p) hu) k).det≠0) :
    ∀k,actualFixedSelectorContactAt S
        (fun a=>actualInheritedTranslatedGerm P hs p hdom ((actualVertexEnumeration n I).symm a)) k ∧
      (actualFixedSelectorJacobian S
        (fun a=>actualInheritedTranslatedGerm P hs p hdom ((actualVertexEnumeration n I).symm a)) k).det≠0 := by
  let W:=degLexWeight n P.germs.degreeBound
  have hFamily : (fun a=>actualInheritedTranslatedGerm P hs p hdom ((actualVertexEnumeration n I).symm a))=
      fun a=>(s^weightedDegree W a.val)⁻¹ • actualDiagonalPullback (fun i=>s^W i)
        (actualNativeHistoricalFamily PHS (scaledOriginalPoint P s p) hu a) := by
    funext a
    have h:=hCov ((actualVertexEnumeration n I).symm a)
    simp only [(actualVertexEnumeration n I).apply_symm_apply] at h
    exact h
  let Contact : (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I) →
      HolGerm (ComplexModel n)) → Prop:=fun Γ=>
    ∀k,actualFixedSelectorContactAt S Γ k ∧ (actualFixedSelectorJacobian S Γ k).det≠0
  apply Eq.mpr (congrArg Contact hFamily)
  intro k
  exact actual_selected_contact_diagonal_rows S (fun i=>s^W i) (fun _=>pow_ne_zero _ hs0)
    (fun a=>(s^weightedDegree W a.val)⁻¹) (fun _=>inv_ne_zero (pow_ne_zero _ hs0)) _ k
    (hNative k).1 (hNative k).2

/-- One actual moving presentation carries all five historical laws on one
fixed scale and a genuine common open, with the SAME origin selector. -/
def ActualHistoricalContactPresentationNeighborhood
    {A : GermIdeal n (ComplexModel n)} {R : ℕ → ℕ}
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I))) : Prop :=
    ∃(P : ActualInheritedWeightedTailData G)(s : ℂ)(hs0 : s≠0)
      (hs : s∈Metric.ball 0 P.radius)(δ : ℝ),0<δ ∧
    IsOpen (historicalNativeJetWindow P s hs0 δ) ∧
    (0 : ComplexModel n)∈historicalNativeJetWindow P s hs0 δ ∧
    historicalNativeJetWindow P s hs0 δ⊆PHS.neighborhood ∧
    ∀p∈Metric.ball (0 : CoordinateSpace n) δ,
      ∃hdom : MapsTo (fun z=>p+z) (Metric.ball 0 (P.radius/2)) (Metric.ball 0 P.radius),
      ∃hu : scaledOriginalPoint P s p∈PHS.neighborhood,
        (∀j : Fin (actualVertexCount n I),
          let a:=actualVertexEnumeration n I j
          let W:=degLexWeight n P.germs.degreeBound
          actualInheritedTranslatedGerm P hs p hdom j=
            HolGerm.constHom ((s^weightedDegree W a.val)⁻¹)*
              actualDiagonalPullback (fun i=>s^W i)
                (translatedGerm (scaledOriginalPoint P s p) (PHS.representatives a)
                  (PHS.holomorphicAt _ hu a))) ∧
        actualHistoricalScaledFormalIdeal A (scaledOriginalPoint P s p)
            (fun i=>s^(degLexWeight n P.germs.degreeBound i))=
          Ideal.span (range fun j=>actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom
            (historicalDegreePrefixLabel (actualVertexWords n I) P.germs.degreeBound j))) ∧
        HistoricalWholePrefixSupport
          (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I))
          (fun a=>actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom
            ((actualVertexEnumeration n I).symm a))) ∧
        ((∀ℓ,hilbertSamuelAt A (scaledOriginalPoint P s p) ℓ=R ℓ) →
          ActualHistoricalNativeExactOrderAt PHS (scaledOriginalPoint P s p) hu ∧
          (∀j : Fin (actualVertexCount n I),
            actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom j)∈
              genuineFormalVariables n^normalExponentDegree (wordExponent (actualVertexWords n I j)) ∧
            actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom j)∉
              genuineFormalVariables n^(normalExponentDegree (wordExponent (actualVertexWords n I j))+1)) ∧
          (∀m,HistoricalDegreePrefixFrames (actualVertexWords n I)
            (fun j=>actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom j)) m) ∧
          HistoricalWholeSupportedDivision
            (historicalDegreePrefixWords (actualVertexWords n I) P.germs.degreeBound)
            (fun j=>actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom
              (historicalDegreePrefixLabel (actualVertexWords n I) P.germs.degreeBound j))))
 ∧
        ((∀ℓ,hilbertSamuelAt A (scaledOriginalPoint P s p) ℓ=R ℓ) →
          ∀k,actualFixedSelectorContactAt S
            (fun a=>actualInheritedTranslatedGerm P hs p hdom ((actualVertexEnumeration n I).symm a)) k ∧
            (actualFixedSelectorJacobian S
              (fun a=>actualInheritedTranslatedGerm P hs p hdom ((actualVertexEnumeration n I).symm a)) k).det≠0)


/-- Restrict the EXACT prior (1)--(3),(5) presentation. The fixed scale,
functions, old labels, prefix partitions and entire actual strict ideal are
retained; (4) is derived on this SAME window from genuine origin contact. -/
theorem exists_actual_geometric_historical_contact_presentation_neighbourhood
    {A : GermIdeal n (ComplexModel n)} {R : ℕ → ℕ}
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)))
    (hSupported : ActualHistoricalSupportedPresentationNeighborhood PHS)
    (hContact : ∀k,actualFixedSelectorContactAt S G.germs k) :
    ActualHistoricalContactPresentationNeighborhood PHS S := by
  obtain ⟨O,hO,h0O,_hOsub,hNative⟩:=exists_actual_native_moving_selected_contact PHS S hContact
  obtain ⟨P,s,hs0,hs,δ,hδ,_hWindow,_hWindow0,hWindowSub,hPoints⟩:=hSupported
  let e:=EuclideanSpace.equiv (𝕜:=ℂ) (ι:=Fin n)
  have hc : Continuous (scaledOriginalPoint P s):=
    (actualDiagonalMap (fun i=>s^(degLexWeight n P.germs.degreeBound i))).continuous.comp e.symm.continuous
  have hc0 : scaledOriginalPoint P s (0 : CoordinateSpace n)=0:=by
    change actualDiagonalMap _ (e.symm 0)=0
    rw [map_zero,map_zero]
  have ht : Tendsto (scaledOriginalPoint P s) (𝓝 0) (𝓝 0):=by simpa only [hc0] using hc.tendsto 0
  obtain ⟨η,hη,hηsub⟩:=Metric.mem_nhds_iff.mp (ht.eventually (hO.mem_nhds h0O))
  refine ⟨P,s,hs0,hs,min δ η,lt_min hδ hη,
    historicalNativeJetWindow_isOpen P s hs0 _,historicalNativeJetWindow_zero P s hs0 (lt_min hδ hη),?_,?_⟩
  · intro u hu
    apply hWindowSub
    change (scaledOriginalPointHomeomorph P s hs0).symm u∈Metric.ball 0 δ
    change (scaledOriginalPointHomeomorph P s hs0).symm u∈Metric.ball 0 (min δ η) at hu
    exact Metric.ball_subset_ball (min_le_left δ η) hu
  intro p hp
  have hpδ : p∈Metric.ball (0 : CoordinateSpace n) δ:=mem_ball_zero_iff.mpr
    (lt_of_lt_of_le (mem_ball_zero_iff.mp hp) (min_le_left δ η))
  have hpη : p∈Metric.ball (0 : CoordinateSpace n) η:=mem_ball_zero_iff.mpr
    (lt_of_lt_of_le (mem_ball_zero_iff.mp hp) (min_le_right δ η))
  obtain ⟨hdom,hu,hCov,hIdeal,hPrefix,hPhase⟩:=hPoints p hpδ
  refine ⟨hdom,hu,hCov,hIdeal,hPrefix,hPhase,?_⟩
  intro hHS
  exact actual_scaled_moving_selected_contact PHS S P hs0 hs p hdom hu hCov
    (hNative _ (hηsub hpη) hu hHS)

end GeometricSource

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
 HironakaActualHistoricalPrescribedIteration HironakaActualPrescribedHSRecursion
 HironakaActualPrescribedCentreRebasing HironakaActualPrescribedWeightedSuccessor
 HironakaActualCurrentMarkedFunctionSquares HironakaActualWholeHSContactWindow
 HironakaSmoothCentreCoherentDomain HironakaActualInheritedNestedContactFlag
 HironakaActualFixedInheritedSelector HironakaActualInheritedCurrentSourceRelabel
 HironakaActualNormalMarkedDirection HironakaActualGeometricAdaptedCurrentSelector
 HironakaActualAnalyticAdaptedCurrentSelector HironakaActualOriginalAdaptedMarkedTransport
 HironakaActualRelativeNormalJetDivision HironakaActualAnalyticBlowupTaylor
 HironakaActualCoherentWeightedCoefficientMarked HironakaActualWeightedCoefficientCompression
 HironakaActualFiniteCoefficientIdeals HironakaRelativeNormalDeformationInitialRelations
 HironakaActualFixedFlatteningHSComparison
 HironakaRelativeNormalCoherentTranslatedJets HironakaActualNormalAllDirectionAnalyticSaturation
 MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism GermIdealOrder InvertibleIdealQuotient

/-- ORIGINAL actual geometry retains the SAME stage and prior produced
presentation data, and derives all moving contact/Jacobian laws from the
SAME historical selector and genuine origin contact. -/
theorem exists_actual_geometric_stage_with_historical_selected_contact
    {d t : ℕ} {Z : Type} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel (d+(t+2))) Z] [IsComplexManifold (d+(t+2)) Z]
    (I : Ideal (HolGerm (ComplexModel (d+(t+2)))))
    (G : ActualAnalyticInheritedFamily (d+(t+2)) 0 (analyticZeroTaylorIdeal (d+(t+2)) I))
    (hmem : ∀a,G.germs a∈I)
    (hw : ∀a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+(t+2)) I),
      0<normalExponentDegree a.val)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+(t+2)) I)))
    (hred : ∀k,ActualInheritedPrefixReducedAt G k)
    (hContact : ∀k,actualFixedSelectorContactAt S G.germs k)
    (U : TopologicalSpace.Opens (ComplexModel (d+(t+2)))) (h0U : (0 : ComplexModel (d+(t+2)))∈U)
    (c : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+(t+2)) I) →
      ComplexModel (d+(t+2)) → ℂ)
    (hc : ∀a,MDifferentiableOn 𝓘(ℂ,ComplexModel (d+(t+2))) 𝓘(ℂ,ℂ) (c a) U)
    (hrep : ∀a,HolGerm.mk (c a)
      ((holomorphicAt_of_mdifferentiableOn U.isOpen (hc a) h0U).mono fun _ hz=>hz.differentiableAt)=G.germs a)
    (hCos : ∀a,(U : Set (ComplexModel (d+(t+2))))∩complexCoordinatePlane (d+(t+2)) d⊆
      cosupport (d+(t+2)) univ (actualPrincipalCoefficientIdeal (d+(t+2)) (c a)) (normalExponentDegree a.val))
    (E : List (Set U)) (π : Z → U)
    (hπ : IsBlowupAlong (d+(t+2)) ((Subtype.val : U → ComplexModel (d+(t+2))) ⁻¹'
      complexCoordinatePlane (d+(t+2)) d) π)
    (y : Z) (hy : (π y : ComplexModel (d+(t+2)))=0)
    (W : Set U) (hWa : IsComplexAnalyticSubset (n:=d+(t+2)) W)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+(t+2))) (π y) (π y)))
    (hΦsrc : Φ.source⊆(chartAt (ComplexModel (d+(t+2))) (π y)).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel (d+(t+2))) (π y) (π y))=0)
    (hΦid : Φ.toFun=id) (hΦdom : Φ.source=(U : Set (ComplexModel (d+(t+2)))))
    (hOrigin : I=originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
      (actualFlattenedOriginalSheaf (vanishingIdeal (n:=d+(t+2)) W) (π y) Φ) 0))
    (hHS : ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=d+(t+2)) (strictTransform (d+(t+2)) π W)) y ℓ=
      hilbertSamuelAt (vanishingIdeal (n:=d+(t+2)) W) (π y) ℓ) :
    let w:=fun a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+(t+2)) I)=>
      normalExponentDegree a.val
    let M : MarkedIdeal (d+(t+2)) U:=⟨univ,E,weightedFunctionIdeal w (fun a (z : U)=>c a z),weightedCommonMark w⟩
    let Q:=M.geoTransform ((Subtype.val : U → ComplexModel (d+(t+2))) ⁻¹' complexCoordinatePlane (d+(t+2)) d) π
    let q : Fin (d+(t+2)):=⟨d,by omega⟩
    y∈Q.cosupp ∧
    ∃(e : Fin (d+(t+2)))(b : Fin (d+(t+2)) → ℂ)
      (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+(t+2))) y y))
      (_hΘ0 : Θ.toFun (chartAt (ComplexModel (d+(t+2))) y y)=0)
      (he : q≤e),
      Θ.source⊆(chartAt (ComplexModel (d+(t+2))) y).target ∧
      (∀z : Z,z∈(chartAt (ComplexModel (d+(t+2))) y).source →
        chartAt (ComplexModel (d+(t+2))) y z∈Θ.source →
        (π z : ComplexModel (d+(t+2)))=actualAnalyticBlowupMap (actualTangentCentreVariables d (t+2)) e b
          (Θ.toFun (chartAt (ComplexModel (d+(t+2))) y z))) ∧
      ∃hp : ∀a,G.germs a∈actualAnalyticCoordinateIdeal (Set.Ici q)^normalExponentDegree a.val,
      ∃f : Fin (d+(t+2)),∃_hqf : q≤f,actualNormalMarkedDirection (Set.Ici q) e b f≠0 ∧
      ∃C : HolGerm (ComplexModel (d+(t+2)))≃ₐ[ℂ]HolGerm (ComplexModel (d+(t+2))),
      ∃u : HolGerm (ComplexModel (d+(t+2))),IsUnit u ∧
      ∃D : ActualAdaptedCurrentSelectorData I G q e f b S,
      ∃P : ActualMarkedFunctionSquare w
        (sameAnalyticNormalNormalizedVertex (d+(t+2)) I G q e he b hp) D.targetFamily.germs
        (actualAdaptedOriginalLabelEquiv D) C u,
        (P.oldDomain : Set (ComplexModel (d+(t+2))))⊆Θ.target ∧
        MarkedIdeal.pullback
          (fun z : P.currentDomain=>actualFlatteningInverseMap y Θ (P.chart.toFun z)) Q=
          actualCurrentNativeWeightedRecord P (fun a=>normalExponentDegree a.val)
            ((fun z : P.oldDomain=>actualFlatteningInverseMap y Θ z) ⁻¹' Q.N)
            (Q.E.map ((fun z : P.oldDomain=>actualFlatteningInverseMap y Θ z) ⁻¹' ·)) ∧
        let K:=originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
          (actualFlattenedOriginalSheaf (vanishingIdeal (n:=d+(t+2))
            (strictTransform (d+(t+2)) π W)) y Θ) 0)
        let J:=(HironakaActualGeometricAdaptedCurrentSelector.actualAdaptedHistoricalCurrentSource D).ideal
        let A₀:=vanishingIdeal (n:=d+(t+2))
          (actualFixedFlatteningSet y Θ (strictTransform (d+(t+2)) π W))
        let A:=GermIdeal.pullback (m:=d+(t+2)) P.chart.toFun A₀
        J=Ideal.map C.toRingEquiv.toRingHom K ∧ J=originalCoherentOriginIdeal A ∧
        ∃PHS : ActualGeometricInheritedNeighborhoodHS A J D.targetFamily (hilbertSamuelValue I),
          PHS.representatives=P.currentFunctions ∧ PHS.neighborhood⊆P.currentDomain ∧
          MapsTo P.chart.toFun PHS.neighborhood Θ.target ∧
          (∀k,∀z∈PHS.neighborhood,
            (∀i∈fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex
              (analyticZeroTaylorIdeal (d+(t+2)) I)) k,P.chart.toFun z i=0) ↔
            ∀j∈fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex
              (analyticZeroTaylorIdeal (d+(t+2)) (sameAnalyticZeroNormalizedIdeal (d+(t+2)) _
                D.sourceFamily q D.sourcePower))) k,z j=0) ∧
          (∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=d+(t+2)) (strictTransform (d+(t+2)) π W)) y ℓ=
            hilbertSamuelAt (vanishingIdeal (n:=d+(t+2)) W) (π y) ℓ) ∧
          ActualSelectedContactWindowLaws S
            (sameAnalyticNormalNormalizedVertex (d+(t+2)) I G q e he b hp)
            (actualAdaptedHistoricalCurrentSource D).selector D.targetFamily.germs
            A (hilbertSamuelValue I) P.chart.toFun PHS.neighborhood ∧
          ActualPrescribedStageRebaseLaws Q y Θ P (strictTransform (d+(t+2)) π W)
            D.targetSpan (actualAdaptedHistoricalCurrentSource D).selector (hilbertSamuelValue I) PHS ∧
          ActualPrescribedWeightedRebaseLaws Q y Θ P (strictTransform (d+(t+2)) π W)
            D.targetSpan (actualAdaptedHistoricalCurrentSource D).selector (hilbertSamuelValue I) PHS ∧
          ActualPrescribedHSRebaseLaws Q y Θ P (strictTransform (d+(t+2)) π W)
            D.targetSpan (actualAdaptedHistoricalCurrentSource D).selector (hilbertSamuelValue I) PHS ∧
          ActualPrescribedRepeatedHSRebaseLaws Q y Θ P (strictTransform (d+(t+2)) π W)
            D.targetSpan (actualAdaptedHistoricalCurrentSource D).selector (hilbertSamuelValue I) PHS ∧ ActualHistoricalWholeJetNeighborhood PHS ∧ ActualHistoricalDegreePrefixJetNeighborhood PHS ∧ ActualHistoricalFormalPresentationNeighborhood PHS ∧ ActualHistoricalSupportedPresentationNeighborhood PHS ∧ ActualHistoricalContactPresentationNeighborhood PHS (actualAdaptedHistoricalCurrentSource D).selector := by
  dsimp only
  obtain ⟨hcut,e,b,Θ,hΘ0,he,hΘsrc,hSquare,hp,f,hqf,hvf,Cg,u,hu,D,P,hOldTarget,hRecord,
    hStrict,hOriginCurrent,PHS,hRepresentatives,hPHS,hMap,hFlags,hIntrinsic,hContactLaws,
    hRebaseLaws,hWeightedLaws,hHSTransition,hRepeated,hWholeJets,hDegreeJets,hFormalJets,hSupported⟩:=
    exists_actual_geometric_stage_with_historical_prefix_support I G hmem hw S hred hContact
      U h0U c hc hrep hCos E π hπ y hy W hWa Φ hΦsrc hΦ0 hΦid hΦdom hOrigin hHS
  refine ⟨hcut,e,b,Θ,hΘ0,he,hΘsrc,hSquare,hp,f,hqf,hvf,Cg,u,hu,D,P,hOldTarget,hRecord,
    hStrict,hOriginCurrent,PHS,hRepresentatives,hPHS,hMap,hFlags,hIntrinsic,hContactLaws,
    hRebaseLaws,hWeightedLaws,hHSTransition,hRepeated,hWholeJets,hDegreeJets,hFormalJets,hSupported,?_⟩
  exact exists_actual_geometric_historical_contact_presentation_neighbourhood PHS
    (actualAdaptedHistoricalCurrentSource D).selector hSupported D.targetContact

end
end Hironaka.HironakaActualHistoricalMovingSelectedContact
