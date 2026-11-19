import Hironaka.Resolution.HironakaActualWeightedHSNormalRecodingInput

/-! Genuine subcritical ambient derivatives of homogenization and the whole
ORIGINAL coefficient-homogenized trace, before any canonical history claim.
Blueprint: hironaka-actual-weighted-normal-homogenized-derivatives-20261102.tex. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualWeightedNormalHomogenizedDerivatives
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan InvertibleIdealQuotient GermIdealPullbackCalculus
  GermIdealOrder IdealWeightPowers IdealOrderArithmetic DerivativeIdeal BlowupDerivativeIdeal
  DerivativeIdealAlong HomogenizedGlueing HomogenizedEquivalence HomogenizedIdealAlong CoefficientIdeal
  MarkedIdeals HironakaSmoothSubmersionCoefficientIdeals RestrictedIdealExtension
  HironakaActualCoherentWeightedCoefficientMarked HironakaActualWeightedCoefficientCompression
  HironakaActualWeightedNormalAmbientDerivatives HironakaActualWeightedNormalContact
  HironakaActualWeightedHSNormalInput HironakaActualWeightedHSNormalRecodingInput
  HironakaActualWeightedNormalPadding HironakaActualOpenZeroSectionDifferentials
  HironakaActualRelativeNormalGeometry HironakaActualZeroCoordinateContactSeed
  HironakaActualOriginalInitialHSPhase HironakaActualHistoricalHSMarkedDomain
  HironakaActualGeometricCurrentNeighborhoodHS
  HironakaActualRelativeNormalJetDivision HironakaActualNormalZeroAnalyticSaturation
  HironakaActualFormalInitialDiagram HironakaRelativeNormalMonomialBasis
  HironakaActualCoefficientPresentationCentrePower

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

omit [IsComplexManifold n X] in
private theorem hol {I : GermIdeal n X} (hI : I.IsCoherent) :
    ∀x f,I.mem x f → HolomorphicAt n f x :=
  fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hI hf

private theorem mul_span_right {L : GermIdeal n X} (hL : L.IsCoherent)
    {x : X} {S : (X→ℂ)→Prop} {p q : X→ℂ} (hq : HolomorphicAt n q x)
    (hp : IsInSpanAt (n:=n) S x p)
    (hGen : ∀a,S a → L.mem x (fun z=>a z*q z)) : L.mem x (fun z=>p z*q z) := by
  obtain ⟨hph,K,s,c,hs,hc,hSum⟩:=hp
  apply HomogenizedIdeal.mem_of_isInSpanAt hL
  refine ⟨hph.mul hq,K,(fun i z=>s i z*q z),c,(fun i=>hGen _ (hs i)),hc,?_⟩
  filter_upwards [hSum] with z hz
  rw [hz,Finset.sum_mul]
  exact Finset.sum_congr rfl (fun i _ => by ring)

private theorem chartDeriv_mul_eventually {x : X} {e : ComplexChart n X} {v : ComplexModel n}
    {a b : X→ℂ} (hx : x∈e.val.source) (ha : HolomorphicAt n a x) (hb : HolomorphicAt n b x) :
    chartDeriv e v (fun z=>a z*b z)=ᶠ[𝓝 x]
      (fun z=>chartDeriv e v a z*b z+a z*chartDeriv e v b z) := by
  have h:=chartDeriv_eventuallyEq_sum_mul (e:=e) (v:=v) (f:=fun z=>a z*b z)
    (N:=1) (a:=fun _=>a) (s:=fun _=>b) hx (fun _=>ha) (fun _=>hb)
    (Eventually.of_forall fun _ => by simp)
  simpa using h

/-- The differentiated first factor is recovered after adding the ACTUAL
lower Leibniz term. No false equality for arbitrary product derivatives. -/
theorem derivative_product_recovery {A B : GermIdeal n X}
    (hA : A.IsCoherent) (hB : B.IsCoherent) :
    ((derivIdeal A).mul B).Le (sumIdeal (derivIdeal (A.mul B)) (A.mul (derivIdeal B))) := by
  let L:=sumIdeal (derivIdeal (A.mul B)) (A.mul (derivIdeal B))
  have hAB:=isCoherent_mul hA hB
  have hDAB:=isCoherent_derivIdeal hAB
  have hADB:=isCoherent_mul hA (isCoherent_derivIdeal hB)
  have hL : L.IsCoherent:=isCoherent_sumIdeal hDAB hADB
  intro x g hg
  apply HomogenizedIdeal.mem_of_isInSpanAt hL
  refine IsInSpanAt.trans ?_ (IdealOrderArithmetic.mem_mul_iff.mp hg)
  rintro _ ⟨p,q,hp,hq,rfl⟩
  have hqhol:=hol hB x q hq
  apply isInSpanAt_self ?_ ((holomorphicAt_of_mem_derivIdeal hp).mul hqhol)
  apply mul_span_right hL hqhol hp
  rintro a (ha | ⟨e,v,a,hxe,ha,rfl⟩)
  · have hab : (A.mul B).mem x (fun z=>a z*q z):=
      IdealOrderArithmetic.mul_mem_mul ha hq ((hol hA x a ha).mul hqhol)
    exact le_sumIdeal_left hDAB x _ (le_derivIdeal (hol hAB) x _ hab)
  · have hAhol:=hol hA x a ha
    have hab : (A.mul B).mem x (fun z=>a z*q z):=
      IdealOrderArithmetic.mul_mem_mul ha hq (hAhol.mul hqhol)
    have hd : L.mem x (chartDeriv e v (fun z=>a z*q z)):=
      le_sumIdeal_left hDAB x _ (chartDeriv_mem_derivIdeal (hol hAB) hxe hab)
    have hr : L.mem x (fun z=>a z*chartDeriv e v q z):=
      le_sumIdeal_right hADB x _ (IdealOrderArithmetic.mul_mem_mul ha
        (chartDeriv_mem_derivIdeal (hol hB) hxe hq)
        (hAhol.mul (holomorphicAt_chartDeriv hxe hqhol)))
    have hSpan:=IsInSpanAt.add (isInSpanAt_self hd (hol hL x _ hd))
      (IsInSpanAt.mul_left (holomorphicAt_const (-1 : ℂ))
        (isInSpanAt_self hr (hol hL x _ hr)))
    apply HomogenizedIdeal.mem_of_isInSpanAt hL
    apply IdealWeightPowers.isInSpanAt_congr hSpan
    filter_upwards [chartDeriv_mul_eventually hxe hAhol hqhol] with z hz
    change chartDeriv e v a z*q z=
      chartDeriv e v (fun y=>a y*q y) z+(-1)*(a z*chartDeriv e v q z)
    rw [hz]
    ring

private theorem deriv_finSumIdeal (A : ℕ→GermIdeal n X) (hA : ∀i,(A i).IsCoherent) :
    ∀m,0<m → derivIdeal (finSumIdeal A m)=finSumIdeal (fun i=>derivIdeal (A i)) m
  | 0,hm => False.elim (Nat.not_lt_zero _ hm)
  | 1,_ => by rw [finSumIdeal_one (hA 0),finSumIdeal_one (isCoherent_derivIdeal (hA 0))]
  | m+2,_ => by
    rw [finSumIdeal_succ (fun i _=>hA i),
      show derivIdeal (sumIdeal (finSumIdeal A (m+1)) (A (m+1)))=
          sumIdeal (derivIdeal (finSumIdeal A (m+1))) (derivIdeal (A (m+1))) from
        iterDerivIdeal_sum (isCoherent_finSumIdeal hA (m+1)) (hA (m+1)) 1,
      deriv_finSumIdeal A hA (m+1) (by omega),
      ←finSumIdeal_succ (fun i _=>isCoherent_derivIdeal (hA i))]

/-- The actual truncated source sum for the j-th subcritical derivative. -/
def homogenizedDerivativeSlice (I : GermIdeal n X) (d j : ℕ) : GermIdeal n X :=
  finSumIdeal (fun i=>(iterDerivIdeal I (j+i)).mul (idealPow (iterDerivIdeal I (d-1)) i)) (d-j)

private theorem slice_coherent {I : GermIdeal n X} (hI : I.IsCoherent) (d j : ℕ) :
    (homogenizedDerivativeSlice I d j).IsCoherent:=
  isCoherent_finSumIdeal_of_lt (fun i _ => isCoherent_mul (isCoherent_iterDerivIdeal hI (j+i))
    (isCoherent_idealPow (isCoherent_iterDerivIdeal hI (d-1)) i))

private theorem mul_mono {A A' B B' : GermIdeal n X} (hA : A.Le A') (hB : B.Le B') :
    (A.mul B).Le (A'.mul B') := by
  intro x g hg
  exact IdealOrderArithmetic.mem_mul_iff.mpr ((IdealOrderArithmetic.mem_mul_iff.mp hg).mono
    (fun _ ⟨a,b,ha,hb,he⟩ => ⟨a,b,hA x a ha,hB x b hb,he⟩))

private theorem sum_le {A B L : GermIdeal n X} (hL : L.IsCoherent)
    (hA : A.Le L) (hB : B.Le L) : (sumIdeal A B).Le L := by
  intro x g hg
  exact HomogenizedIdeal.mem_of_isInSpanAt hL
    ((mem_sumIdeal_iff.mp hg).mono (fun f hf => hf.elim (hA x f) (hB x f)))

omit [IsComplexManifold n X] in
private theorem fin_term_le (A : ℕ→GermIdeal n X) (hA : ∀i,(A i).IsCoherent)
    {i m : ℕ} (hi : i<m) : (A i).Le (finSumIdeal A m) := by
  intro x g hg
  change IsInSpanAt (n:=n) (fun f=>∃i,i<m ∧ (A i).mem x f) x g
  exact isInSpanAt_self ⟨i,hi,hg⟩ (hol (hA i) x g hg)

/-- One true derivative of the actual truncated source sum. Both end terms
are absorbed explicitly; no maximal-order hypothesis is used. -/
theorem deriv_homogenized_slice {I : GermIdeal n X} (hI : I.IsCoherent)
    {d j : ℕ} (hj : j+1<d) :
    derivIdeal (homogenizedDerivativeSlice I d j)=homogenizedDerivativeSlice I d (j+1) := by
  let A:=iterDerivIdeal I
  let T:=iterDerivIdeal I (d-1)
  let K:=homogenizedDerivativeSlice I d j
  let L:=homogenizedDerivativeSlice I d (j+1)
  have hA (i : ℕ) : (A i).IsCoherent:=isCoherent_iterDerivIdeal hI i
  have hT : T.IsCoherent:=isCoherent_iterDerivIdeal hI (d-1)
  have hK : K.IsCoherent:=slice_coherent hI d j
  have hL : L.IsCoherent:=slice_coherent hI d (j+1)
  have hSource (i : ℕ) (hi : i<d-j) : ((A (j+i)).mul (idealPow T i)).Le K:=
    fin_term_le _ (fun i=>isCoherent_mul (hA (j+i)) (isCoherent_idealPow hT i)) hi
  have hTarget (i : ℕ) (hi : i<d-(j+1)) : ((A (j+1+i)).mul (idealPow T i)).Le L:=
    fin_term_le _ (fun i=>isCoherent_mul (hA (j+1+i)) (isCoherent_idealPow hT i)) hi
  have hUpper : (derivIdeal K).Le L := by
    change (derivIdeal (finSumIdeal (fun i=>(A (j+i)).mul (idealPow T i)) (d-j))).Le L
    rw [deriv_finSumIdeal _ (fun i=>isCoherent_mul (hA (j+i)) (isCoherent_idealPow hT i))
      (d-j) (by omega)]
    apply finSumIdeal_le hL
    intro i hi
    have hFirst : ((derivIdeal (A (j+i))).mul (idealPow T i)).Le L := by
      by_cases hNext : i+1<d-j
      · have hEq : derivIdeal (A (j+i))=A (j+1+i) := by
          change derivIdeal (iterDerivIdeal I (j+i))=iterDerivIdeal I (j+1+i)
          rw [←iterDerivIdeal_succ]
          congr 1
          omega
        rw [hEq]
        exact hTarget i (by omega)
      · have hLast : i+1=d-j:=by omega
        have hPower : (idealPow T i).Le L := by
          have hTerm:=hTarget (i-1) (by omega)
          have hEq : (A (j+1+(i-1))).mul (idealPow T (i-1))=idealPow T i := by
            change (iterDerivIdeal I (j+1+(i-1))).mul (idealPow T (i-1))=idealPow T i
            rw [show j+1+(i-1)=d-1 by omega]
            change T.mul (idealPow T (i-1))=idealPow T i
            rw [RestrictLeCalculus.mul_comm',←idealPow_succ,show (i-1)+1=i by omega]
          rw [hEq] at hTerm
          exact hTerm
        intro x g hg
        exact hPower x g (mul_le_right (fun {_ _} h=>holomorphicAt_of_mem_derivIdeal h)
          (isCoherent_idealPow hT i) x g hg)
    have hSecond : ((A (j+i)).mul (derivIdeal (idealPow T i))).Le L := by
      by_cases hi0 : i=0
      · subst i
        have hBase:=hTarget 0 (by omega)
        rw [Nat.add_zero,idealPow_zero,RestrictLeCalculus.mul_unitIdeal (hA (j+1))] at hBase
        intro x g hg
        have hIn : (A j).mem x g:=mul_le_left (hA j)
          (fun {_ _} h=>holomorphicAt_of_mem_derivIdeal h) x g hg
        exact hBase x g (le_derivIdeal (hol (hA j)) x g hIn)
      · have hPower : (derivIdeal (idealPow T i)).Le (idealPow T (i-1)) := by
          apply derivIdeal_le_idealPow (hol hT)
          rw [show (i-1)+1=i by omega]
          exact fun _ _ h=>h
        have hTerm:=hTarget (i-1) (by omega)
        rw [show j+1+(i-1)=j+i by omega] at hTerm
        exact fun x g hg=>hTerm x g (mul_mono (fun _ _ h=>h) hPower x g hg)
    have hLeibniz:=derivIdeal_mul_le (hol (hA (j+i))) (hol (isCoherent_idealPow hT i))
    exact fun x g hg=>sum_le hL hFirst hSecond x g (hLeibniz x g hg)
  have hEach : ∀i,i<d-(j+1) → ((A (j+1+i)).mul (idealPow T i)).Le (derivIdeal K) := by
    intro i
    induction i with
    | zero =>
      intro _hi
      rw [Nat.add_zero,idealPow_zero,RestrictLeCalculus.mul_unitIdeal (hA (j+1))]
      have hBase:=hSource 0 (by omega)
      rw [Nat.add_zero,idealPow_zero,RestrictLeCalculus.mul_unitIdeal (hA j)] at hBase
      exact derivIdeal_mono hBase
    | succ i ih =>
      intro hi
      have hPrev:=ih (by omega)
      have hSrc:=hSource (i+1) (by omega)
      have hPower : (derivIdeal (idealPow T (i+1))).Le (idealPow T i):=
        derivIdeal_le_idealPow (hol hT) (fun _ _ h=>h)
      have hLower : ((A (j+(i+1))).mul (derivIdeal (idealPow T (i+1)))).Le (derivIdeal K) := by
        rw [show j+(i+1)=j+1+i by omega]
        exact fun x g hg=>hPrev x g (mul_mono (fun _ _ h=>h) hPower x g hg)
      have hRecovery:=derivative_product_recovery (hA (j+(i+1))) (isCoherent_idealPow hT (i+1))
      have hSum:=sum_le (isCoherent_derivIdeal hK) (derivIdeal_mono hSrc) hLower
      have hEq : A (j+1+(i+1))=derivIdeal (A (j+(i+1))) := by
        change iterDerivIdeal I (j+1+(i+1))=derivIdeal (iterDerivIdeal I (j+(i+1)))
        rw [←iterDerivIdeal_succ]
        congr 1
        omega
      rw [hEq]
      exact fun x g hg=>hSum x g (hRecovery x g hg)
  have hLower : L.Le (derivIdeal K):=finSumIdeal_le (isCoherent_derivIdeal hK) hEach
  exact GermIdeal.ext (funext fun x=>funext fun g=>propext ⟨hUpper x g,hLower x g⟩)

/-- Every genuine subcritical derivative of homogenization is the actual
truncated original derivative/tangent sum, without a maximal-order premise. -/
theorem iterDerivIdeal_homogenized_eq_slice {I : GermIdeal n X} (hI : I.IsCoherent)
    (d : ℕ) : ∀j,j<d → iterDerivIdeal (HomogenizedIdeal.homogenizedIdeal I d) j=
      homogenizedDerivativeSlice I d j
  | 0,_ => by
    rw [iterDerivIdeal_zero,homogenizedIdeal_eq_homSum]
    unfold homSum homogenizedDerivativeSlice
    simp only [Nat.zero_add,Nat.sub_zero]
  | j+1,hj => by
    rw [iterDerivIdeal_succ,iterDerivIdeal_homogenized_eq_slice hI d j (by omega),
      deriv_homogenized_slice hI hj]

private theorem padding_coherent {U : Opens (ComplexModel n)} {I : GermIdeal n U}
    (hI : I.IsCoherent) (d : ℕ) : (normalPaddingIdeal I d).IsCoherent:=
  isCoherent_sumIdeal (isCoherent_pullback (projection_contMDiff U) hI)
    (isCoherent_finiteFunctionIdeal _ (fun _=>(normalCoordinate_mdifferentiable U).pow d))

/-- ENTIRE AMBIENT derivatives of the actual homogenized padding have the
SAME source trace at every genuine subcritical original order. -/
theorem normal_padding_homogenized_derivative_trace {U : Opens (ComplexModel n)}
    {I : GermIdeal n U} (hI : I.IsCoherent) {d j : ℕ} (hj : j<d) :
    GermIdeal.pullback (m:=n) (zeroSection U)
      (iterDerivIdeal (HomogenizedIdeal.homogenizedIdeal (normalPaddingIdeal I d) d) j)=
      iterDerivIdeal (HomogenizedIdeal.homogenizedIdeal I d) j := by
  have hJ:=padding_coherent hI d
  rw [iterDerivIdeal_homogenized_eq_slice hJ d j hj,
    iterDerivIdeal_homogenized_eq_slice hI d j hj]
  unfold homogenizedDerivativeSlice
  rw [HironakaSmoothSubmersionCoefficientIdeals.pullback_finSumIdeal (zeroSection_contMDiff U)
    _ (d-j) (fun i _=>isCoherent_mul (isCoherent_iterDerivIdeal hJ (j+i))
      (isCoherent_idealPow (isCoherent_iterDerivIdeal hJ (d-1)) i))]
  apply finSumIdeal_congr
  intro i hi
  rw [HironakaSmoothSubmersionCoefficientIdeals.pullback_mul (zeroSection_contMDiff U)
      (isCoherent_iterDerivIdeal hJ (j+i)) (isCoherent_idealPow (isCoherent_iterDerivIdeal hJ (d-1)) i),
    HironakaSmoothSubmersionCoefficientIdeals.pullback_idealPow (zeroSection_contMDiff U)
      (isCoherent_iterDerivIdeal hJ (d-1)),
    entire_ambient_derivative_trace hI (show j+i<d by omega),
    entire_ambient_derivative_trace hI (show d-1<d by omega)]

/-- The ENTIRE ORIGINAL C(H(J)) ideal has exactly the ORIGINAL C(H(I))
trace. This is a proved composite, rather than two uncomposed first traces. -/
theorem normal_padding_coefficient_homogenized_trace {U : Opens (ComplexModel n)}
    {I : GermIdeal n U} (hI : I.IsCoherent) (d : ℕ) :
    GermIdeal.pullback (m:=n) (zeroSection U)
      (finSumIdeal (fun i=>idealPow
        (iterDerivIdeal (HomogenizedIdeal.homogenizedIdeal (normalPaddingIdeal I d) d) i)
        (sumExp (fun j=>d-j) d i)) d)=
      finSumIdeal (fun i=>idealPow (iterDerivIdeal (HomogenizedIdeal.homogenizedIdeal I d) i)
        (sumExp (fun j=>d-j) d i)) d := by
  have hHJ:=isCoherent_homogenizedIdeal (padding_coherent hI d) d
  rw [HironakaSmoothSubmersionCoefficientIdeals.pullback_finSumIdeal (zeroSection_contMDiff U)
    _ d (fun i _=>isCoherent_idealPow (isCoherent_iterDerivIdeal hHJ i) _)]
  apply finSumIdeal_congr
  intro i hi
  rw [HironakaSmoothSubmersionCoefficientIdeals.pullback_idealPow (zeroSection_contMDiff U)
    (isCoherent_iterDerivIdeal hHJ i),normal_padding_homogenized_derivative_trace hI hi]

variable {A : GermIdeal n (ComplexModel n)} {I : Ideal (HolGerm (ComplexModel n))}
  {G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)} {R : ℕ→ℕ}

private theorem presentation_functions_mdifferentiable
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R) (i) :
    MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ)
      (fun z : presentationOpen PHS=>PHS.representatives i z.val) := by
  intro z
  have h:=holomorphicAt_of_mdifferentiableOn PHS.isOpen_neighborhood
    (mdifferentiableOn_iff_differentiableOn.mpr (PHS.holomorphicOn i)) z.property
  exact (h.comp_contMDiff (Eventually.of_forall fun _=>
    (contMDiff_subtype_val (U:=presentationOpen PHS)).contMDiffAt)).mdifferentiableAt

/-- The literal INITIAL phase normal padding restricts to the ENTIRE
ORIGINAL bar record of SAME Q, including full E and coefficient product mark. -/
theorem phase_normal_bar_marked_record
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R)
    (hw : ∀i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I),
      0<normalExponentDegree i.val)
    {M : Type u} (η : presentationOpen PHS→M) (E : List (Set M)) :
    markedPullback (m:=n) (zeroSection (presentationOpen PHS))
      (coeffMarkedAlong (homMarkedAlong (phaseNormalMarked PHS η E)))=
      coeffMarkedAlong (homMarkedAlong (initialWeightedRecord PHS η E)) := by
  let Q:=initialWeightedRecord PHS η E
  have hQ : Q.ideal.IsCoherent:=
    isCoherent_weightedFunctionIdeal _ _ (presentation_functions_mdifferentiable PHS)
  have hJ : (phaseNormalMarked PHS η E).ideal.IsCoherent:=padding_coherent hQ Q.d
  have hHQ:=isCoherent_homogenizedIdeal hQ Q.d
  have hHJ:=isCoherent_homogenizedIdeal hJ Q.d
  rw [homMarkedAlong_eq_homMarked rfl (hol hJ),homMarkedAlong_eq_homMarked rfl (hol hQ),
    coeffMarkedAlong_eq_coeffMarked rfl (hol hHJ),coeffMarkedAlong_eq_coeffMarked rfl (hol hHQ)]
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl ?_
    (normal_padding_coefficient_homogenized_trace hQ Q.d) rfl
  change (markedPullback (m:=n) (zeroSection (presentationOpen PHS))
    (phaseNormalMarked PHS η E)).E=(initialWeightedRecord PHS η E).E
  exact congrArg (fun K : MarkedIdeal n (presentationOpen PHS)=>K.E)
    (phase_normal_zero_section_record PHS hw η E)

end
end Hironaka.HironakaActualWeightedNormalHomogenizedDerivatives
