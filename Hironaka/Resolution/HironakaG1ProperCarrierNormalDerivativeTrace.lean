import Hironaka.Resolution.HironakaActualWeightedNormalAmbientDerivatives
import Hironaka.Resolution.HironakaSmoothSubmersionRelativeDifferentialIdeals
import Hironaka.Resolution.HironakaActualOpenZeroSectionDifferentials

/-! Entire first-recoding traces of actual normal padding over a proper carrier.
Blueprint FIRST: hironaka-g1-proper-carrier-normal-derivative-trace.tex.
The cylinder and section carriers remain distinct. No CAN/value/bar claim. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1ProperCarrierNormalDerivativeTrace
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan BlowupTowers InvertibleIdealQuotient GermIdealPullbackCalculus
  RestrictedIdealExtension IdealOrderArithmetic IdealWeightPowers CoefficientIdeal DerivativeIdeal
  DerivativeIdealAlong DerivativeIdealAlongCoherent HomogenizedIdeal HomogenizedEquivalence HomogenizedGlueing HomogenizedIdealAlong MarkedIdeals
  HironakaActualCoherentWeightedCoefficientMarked HironakaActualWeightedNormalPadding
  HironakaActualWeightedNormalAmbientDerivatives HironakaActualRelativeNormalGeometry
  HironakaActualIntrinsicStableAmbientIso HironakaRelativeNormalIdeal
  HironakaActualOpenZeroSectionDifferentials HironakaActualSectionBoundaryGeometry
  HironakaSmoothSubmersionRelativeGeometry HironakaSmoothSubmersionRelativeDifferentialIdeals
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionRelativeRestriction
  HironakaSmoothSubmersionOrderedChoiceImageTrace

private theorem hol {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    {I : GermIdeal n X} (hI : I.IsCoherent) :
    ∀x f,I.mem x f→HolomorphicAt n f x :=
  fun _ _ hf=>GermIdeal.IsCoherent.holomorphicAt_mem hI hf

section Calculus
variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

private theorem sum_le {A B L : GermIdeal n X} (hL : L.IsCoherent)
    (hA : A.Le L) (hB : B.Le L) : (sumIdeal A B).Le L := by
  intro x g hg
  exact HomogenizedIdeal.mem_of_isInSpanAt hL
    ((mem_sumIdeal_iff.mp hg).mono (fun f hf=>hf.elim (hA x f) (hB x f)))

-- The relative sum rule is held privately in ActualTrueMarkCommonContact.
-- This local plumbing reproduces that generic rule, not a new analytic engine.
private theorem field_mem {N : Set X} {A : GermIdeal n X} (hA : A.IsCoherent)
    {x : X} {e : ComplexChart n X} {ξ : Fin n→X→ℂ} (hξ : IsTangentField N e ξ x)
    {f : X→ℂ} (hf : A.mem x f) : (derivIdealAlong N A).mem x (fieldDeriv e ξ f) :=
  isInSpanAt_self (Or.inr (Or.inr ⟨e,ξ,f,hξ,hf,rfl⟩))
    (holomorphicAt_fieldDeriv hξ.mem_source hξ.holomorphicAt (hol hA x f hf))

private theorem deriv_sum {N : Set X} {A B : GermIdeal n X}
    (hA : A.IsCoherent) (hB : B.IsCoherent) (hN : IsClosedSubmanifold n N) :
    derivIdealAlong N (sumIdeal A B)=sumIdeal (derivIdealAlong N A) (derivIdealAlong N B) := by
  have hDA:=isCoherent_derivIdealAlong hA hN
  have hDB:=isCoherent_derivIdealAlong hB hN
  apply GermIdeal.ext
  funext x g
  apply propext
  constructor
  · intro hg
    refine mem_sumIdeal_iff.mpr (IsInSpanAt.trans ?_ hg)
    have hgen : ∀s,A.mem x s∨B.mem x s→
        IsInSpanAt (n:=n) (fun t=>(derivIdealAlong N A).mem x t∨(derivIdealAlong N B).mem x t) x s := by
      rintro s (hs|hs)
      · exact isInSpanAt_self (Or.inl (le_derivIdealAlong (hol hA) x s hs)) (hol hA x s hs)
      · exact isInSpanAt_self (Or.inr (le_derivIdealAlong (hol hB) x s hs)) (hol hB x s hs)
    rintro s (hs|hs|⟨e,ξ,f,hξ,hf,rfl⟩)
    · exact IsInSpanAt.trans hgen (mem_sumIdeal_iff.mp hs)
    · exact isInSpanAt_self (Or.inl (vanishingIdeal_le_derivIdealAlong x s hs)) hs.1
    · obtain ⟨_,K,r,c,hr,hc,hsum⟩:=mem_sumIdeal_iff.mp hf
      have hrhol : ∀k,HolomorphicAt n (r k) x:=fun k=>(hr k).elim (hol hA x _) (hol hB x _)
      have hprod:=fieldDeriv_eventuallyEq_sum_mul (ξ:=ξ) hξ.mem_source hc hrhol hsum
      refine isInSpanAt_congr ?_ hprod.symm
      refine IsInSpanAt.sum Finset.univ fun k _=>IsInSpanAt.add ?_ ?_
      · exact IsInSpanAt.mul_left (holomorphicAt_fieldDeriv hξ.mem_source hξ.holomorphicAt (hc k))
          (hgen _ (hr k))
      · have hdf : (derivIdealAlong N A).mem x (fieldDeriv e ξ (r k))∨
            (derivIdealAlong N B).mem x (fieldDeriv e ξ (r k)) :=
          (hr k).elim (fun h=>Or.inl (field_mem hA hξ h)) (fun h=>Or.inr (field_mem hB hξ h))
        exact isInSpanAt_mul_of_mem hdf (hc k)
          (holomorphicAt_fieldDeriv hξ.mem_source hξ.holomorphicAt (hrhol k))
  · intro hg
    apply HomogenizedIdeal.mem_of_isInSpanAt (isCoherent_derivIdealAlong (isCoherent_sumIdeal hA hB) hN)
    refine IsInSpanAt.trans ?_ (mem_sumIdeal_iff.mp hg)
    rintro s (hs|hs)
    · exact isInSpanAt_self (derivIdealAlong_mono (le_sumIdeal_left hA) x s hs) (hol hDA x s hs)
    · exact isInSpanAt_self (derivIdealAlong_mono (le_sumIdeal_right hB) x s hs) (hol hDB x s hs)

private theorem iter_mono {N : Set X} {A B : GermIdeal n X} (h : A.Le B) :
    ∀r,(iterDerivIdealAlong N A r).Le (iterDerivIdealAlong N B r)
  | 0=>h
  | r+1=>derivIdealAlong_mono (iter_mono h r)

private theorem iter_sum {N : Set X} {A B : GermIdeal n X}
    (hA : A.IsCoherent) (hB : B.IsCoherent) (hN : IsClosedSubmanifold n N) :
    ∀r,iterDerivIdealAlong N (sumIdeal A B) r=
      sumIdeal (iterDerivIdealAlong N A r) (iterDerivIdealAlong N B r)
  | 0=>rfl
  | r+1=>by
    rw [iterDerivIdealAlong,iter_sum hA hB hN r,
      deriv_sum (isCoherent_iterDerivIdealAlong hA hN r) (isCoherent_iterDerivIdealAlong hB hN r) hN]
    rfl


private theorem deriv_le_ambient_plus_vanishing {N : Set X} {A : GermIdeal n X}
    (hA : A.IsCoherent) (hN : IsClosedSubmanifold n N) :
    (derivIdealAlong N A).Le (sumIdeal (derivIdeal A) (vanishingIdeal (n:=n) N)) := by
  have hD:=isCoherent_derivIdeal hA
  have hV:=VanishingIdealCoherent.isCoherent_vanishingIdeal hN
  have hL:=isCoherent_sumIdeal hD hV
  intro x g hg
  apply mem_sumIdeal_iff.mpr
  refine IsInSpanAt.trans ?_ hg
  rintro s (hs|hs|⟨e,ξ,f,hξ,hf,rfl⟩)
  · exact isInSpanAt_self (Or.inl (le_derivIdeal (hol hA) x s hs)) (hol hA x s hs)
  · exact isInSpanAt_self (Or.inr hs) hs.1
  · have hfield : (derivIdeal A).mem x (fieldDeriv e ξ f) := by
      apply HomogenizedIdeal.mem_of_isInSpanAt hD
      unfold fieldDeriv
      exact IsInSpanAt.sum Finset.univ fun i _=>
        IsInSpanAt.mul_left (hξ.holomorphicAt i)
          (isInSpanAt_self (chartDeriv_mem_derivIdeal (hol hA) hξ.mem_source hf)
            (holomorphicAt_chartDeriv hξ.mem_source (hol hA x f hf)))
    exact isInSpanAt_self (Or.inl hfield)
      (holomorphicAt_fieldDeriv hξ.mem_source hξ.holomorphicAt (hol hA x f hf))

private theorem iter_le_ambient_plus_vanishing {N : Set X} {A : GermIdeal n X}
    (hA : A.IsCoherent) (hN : IsClosedSubmanifold n N) :
    ∀j,(iterDerivIdealAlong N A j).Le
      (sumIdeal (iterDerivIdeal A j) (vanishingIdeal (n:=n) N))
  | 0=>le_sumIdeal_left hA
  | j+1=>by
    have hV:=VanishingIdealCoherent.isCoherent_vanishingIdeal hN
    have hD:=isCoherent_iterDerivIdeal hA j
    have hD':=isCoherent_iterDerivIdeal hA (j+1)
    have hL:=isCoherent_sumIdeal hD' hV
    have hstep:=derivIdealAlong_mono (N:=N) (iter_le_ambient_plus_vanishing hA hN j)
    rw [deriv_sum hD hV hN,derivIdealAlong_vanishingIdeal] at hstep
    have hbound : (sumIdeal (derivIdealAlong N (iterDerivIdeal A j))
        (vanishingIdeal (n:=n) N)).Le
        (sumIdeal (iterDerivIdeal A (j+1)) (vanishingIdeal (n:=n) N)) :=
      sum_le hL (deriv_le_ambient_plus_vanishing hD hN) (le_sumIdeal_right hV)
    exact fun x g hg=>hbound x g (hstep x g hg)
end Calculus

variable {n : ℕ}

private theorem projection_section (U : Opens (ComplexModel n)) :
    (projection U)∘(zeroSection U)=id := by
  funext x
  apply Subtype.ext
  exact tangentProjection_tangentInclusion n 1 x.val

private theorem padding_coherent {U : Opens (ComplexModel n)}
    {I : GermIdeal n U} (hI : I.IsCoherent) (d : ℕ) :
    (normalPaddingIdeal I d).IsCoherent :=
  isCoherent_sumIdeal (isCoherent_pullback (projection_contMDiff U) hI)
    (isCoherent_finiteFunctionIdeal _ (fun _=>(normalCoordinate_mdifferentiable U).pow d))

private def normalPower (U : Opens (ComplexModel n)) (d : ℕ) :
    GermIdeal (n+1) (productOpen U) :=
  finiteFunctionIdeal (fun _ : Unit=>fun z=>relativeNormalCoordinate U z^d)

private theorem normalPower_coherent (U : Opens (ComplexModel n)) (d : ℕ) :
    (normalPower U d).IsCoherent :=
  isCoherent_finiteFunctionIdeal _ (fun _=>(normalCoordinate_mdifferentiable U).pow d)

private theorem section_carrier_vanishing_le (U : Opens (ComplexModel n)) (N : Set U) :
    (GermIdeal.pullback (m:=n) (zeroSection U)
      (vanishingIdeal (n:=n+1) (projection U ⁻¹' N))).Le (vanishingIdeal (n:=n) N) := by
  intro x g hg
  obtain ⟨hh,K,s,c,hs,_hc,he⟩:=GermIdeal.mem_pullback_iff.mp hg
  have hs0 : ∀i,∀ᶠ y in 𝓝 x,y∈N→s i y=0 := by
    intro i
    obtain ⟨v,hv,hsv⟩:=hs i
    filter_upwards [(zeroSection_contMDiff U).continuous.continuousAt.eventually hv.2] with y hy hyN
    rw [hsv,Function.comp_apply]
    apply hy
    change projection U (zeroSection U y)∈N
    have he := congrFun (projection_section U) y
    change projection U (zeroSection U y)=y at he
    rwa [he]
  refine ⟨hh,?_⟩
  filter_upwards [he,eventually_all.mpr hs0] with y hy hy0 hyN
  rw [hy]
  exact Finset.sum_eq_zero fun i _=>by rw [hy0 i hyN,mul_zero]

private theorem normal_relative_trace_le {U : Opens (ComplexModel n)} {N : Set U}
    (hN : IsClosedSubmanifold n N) {I : GermIdeal n U} (hI : I.IsCoherent)
    {d j : ℕ} (hj : j<d) :
    (GermIdeal.pullback (m:=n) (zeroSection U)
      (iterDerivIdealAlong (projection U ⁻¹' N) (normalPower U d) j)).Le
      (iterDerivIdealAlong N I j) := by
  cases j with
  | zero=>exact normal_derivative_trace_le U hI hj
  | succ j=>
    have hC:=isClosedSubmanifold_preimage_submersion (projection_isSubmersion (U:=U)) hN
    have hDI:=isCoherent_iterDerivIdealAlong hI hN (j+1)
    have hK:=normalPower_coherent U d
    have hD:=isCoherent_iterDerivIdeal hK (j+1)
    have hV:=VanishingIdealCoherent.isCoherent_vanishingIdeal hC
    have hb : (GermIdeal.pullback (m:=n) (zeroSection U)
        (iterDerivIdealAlong (projection U ⁻¹' N) (normalPower U d) (j+1))).Le
        (GermIdeal.pullback (m:=n) (zeroSection U)
          (sumIdeal (iterDerivIdeal (normalPower U d) (j+1))
            (vanishingIdeal (n:=n+1) (projection U ⁻¹' N)))) := by
      intro x g hg
      exact GermIdeal.mem_pullback_iff.mpr ((GermIdeal.mem_pullback_iff.mp hg).mono
        (fun s hs=>by
          obtain ⟨a,ha,rfl⟩:=hs
          exact ⟨a,iter_le_ambient_plus_vanishing hK hC (j+1) _ _ ha,rfl⟩))
    rw [pullback_sumIdeal_dimensions (zeroSection_contMDiff U) hD hV] at hb
    have ht : (sumIdeal
        (GermIdeal.pullback (m:=n) (zeroSection U) (iterDerivIdeal (normalPower U d) (j+1)))
        (GermIdeal.pullback (m:=n) (zeroSection U) (vanishingIdeal (n:=n+1) (projection U ⁻¹' N)))).Le
        (iterDerivIdealAlong N I (j+1)) :=
      sum_le hDI (normal_derivative_trace_le U hDI hj)
        (fun x g hg=>vanishingIdeal_le_derivIdealAlong x g (section_carrier_vanishing_le U N x g hg))
    exact fun x g hg=>ht x g (hb x g hg)

/-- Entire subcritical relative derivative trace on the actual proper cylinder. -/
theorem entire_relative_derivative_trace {U : Opens (ComplexModel n)} {N : Set U}
    (hN : IsClosedSubmanifold n N) {I : GermIdeal n U} (hI : I.IsCoherent)
    {d j : ℕ} (hj : j<d) :
    GermIdeal.pullback (m:=n) (zeroSection U)
      (iterDerivIdealAlong (projection U ⁻¹' N) (normalPaddingIdeal I d) j)=
      iterDerivIdealAlong N I j := by
  have hC:=isClosedSubmanifold_preimage_submersion (projection_isSubmersion (U:=U)) hN
  have hPI:=isCoherent_pullback (projection_contMDiff U) hI
  have hK:=normalPower_coherent U d
  have hDI:=isCoherent_iterDerivIdealAlong hI hN j
  have hDK:=isCoherent_iterDerivIdealAlong hK hC j
  have hproj:=HironakaSmoothSubmersionRelativeDifferentialIdeals.pullback_iterDerivIdealAlong
    (n:=n) (X:=CMfd.of (n:=n) U) (m:=n+1)
    (Y:=CMfd.of (n:=n+1) (productOpen U)) (f:=projection U)
    (projection_isSubmersion (U:=U)) I hI N hN j
  change GermIdeal.pullback (m:=n) (zeroSection U)
    (iterDerivIdealAlong (projection U ⁻¹' N)
      (sumIdeal (GermIdeal.pullback (m:=n+1) (projection U) I) (normalPower U d)) j)=_
  rw [iter_sum hPI hK hC j,←hproj,
    pullback_sumIdeal_dimensions (zeroSection_contMDiff U)
      (isCoherent_pullback (projection_contMDiff U) hDI) hDK,
    ←coherent_pullback_comp (projection_contMDiff U) (zeroSection_contMDiff U)
      (iterDerivIdealAlong N I j) hDI,projection_section,BlowupControlledTransform.pullback_id hDI]
  apply GermIdeal.ext
  funext x g
  apply propext
  constructor
  · exact sum_le hDI (fun _ _ h=>h) (normal_relative_trace_le hN hI hj) x g
  · exact le_sumIdeal_left hDI x g

/-- Actual normal padding of the GIVEN original record; carrier is the cylinder. -/
def properNormalMarked {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U) :
    MarkedIdeal (n+1) (productOpen U) :=
  ⟨projection U ⁻¹' Q.N,Q.E.map (projection U ⁻¹' ·),normalPaddingIdeal Q.ideal Q.d,Q.d⟩

private theorem relative_homogenized_trace {U : Opens (ComplexModel n)} {N : Set U}
    (hN : IsClosedSubmanifold n N) {I : GermIdeal n U} (hI : I.IsCoherent)
    {d : ℕ} (hd : 0<d) :
    GermIdeal.pullback (m:=n) (zeroSection U)
      (homogenizedIdealAlong (projection U ⁻¹' N) (normalPaddingIdeal I d) d)=
      homogenizedIdealAlong N I d := by
  have hC:=isClosedSubmanifold_preimage_submersion (projection_isSubmersion (U:=U)) hN
  have hJ:=padding_coherent hI d
  unfold homogenizedIdealAlong tangentIdealAlong homSum
  rw [pullback_finSumIdeal (zeroSection_contMDiff U) _ d
    (fun i _=>isCoherent_mul (isCoherent_iterDerivIdealAlong hJ hC i)
      (isCoherent_idealPow (isCoherent_iterDerivIdealAlong hJ hC (d-1)) i))]
  apply finSumIdeal_congr
  intro i hi
  rw [HironakaSmoothSubmersionCoefficientIdeals.pullback_mul (zeroSection_contMDiff U)
      (isCoherent_iterDerivIdealAlong hJ hC i)
      (isCoherent_idealPow (isCoherent_iterDerivIdealAlong hJ hC (d-1)) i),
    HironakaSmoothSubmersionCoefficientIdeals.pullback_idealPow (zeroSection_contMDiff U)
      (isCoherent_iterDerivIdealAlong hJ hC (d-1)),
    entire_relative_derivative_trace hN hI hi,
    entire_relative_derivative_trace hN hI (show d-1<d by omega)]

private theorem relative_coefficient_trace {U : Opens (ComplexModel n)} {N : Set U}
    (hN : IsClosedSubmanifold n N) {I : GermIdeal n U} (hI : I.IsCoherent) (d : ℕ) :
    GermIdeal.pullback (m:=n) (zeroSection U)
      (finSumIdeal (fun i=>idealPow
        (iterDerivIdealAlong (projection U ⁻¹' N) (normalPaddingIdeal I d) i)
        (sumExp (fun j=>d-j) d i)) d)=
      finSumIdeal (fun i=>idealPow (iterDerivIdealAlong N I i) (sumExp (fun j=>d-j) d i)) d := by
  have hC:=isClosedSubmanifold_preimage_submersion (projection_isSubmersion (U:=U)) hN
  have hJ:=padding_coherent hI d
  rw [pullback_finSumIdeal (zeroSection_contMDiff U) _ d
    (fun i _=>isCoherent_idealPow (isCoherent_iterDerivIdealAlong hJ hC i) _)]
  apply finSumIdeal_congr
  intro i hi
  rw [HironakaSmoothSubmersionCoefficientIdeals.pullback_idealPow (zeroSection_contMDiff U)
    (isCoherent_iterDerivIdealAlong hJ hC i),entire_relative_derivative_trace hN hI hi]

private theorem section_cylinder_carrier (U : Opens (ComplexModel n)) (N : Set U) :
    zeroSection U ⁻¹' (projection U ⁻¹' N)=N := by
  rw [←Set.preimage_comp,projection_section]
  rfl

private theorem section_cylinder_boundary (U : Opens (ComplexModel n)) (E : List (Set U)) :
    (E.map (projection U ⁻¹' ·)).map (zeroSection U ⁻¹' ·)=E := by
  rw [List.map_map]
  change E.map (fun H=>(projection U∘zeroSection U) ⁻¹' H)=E
  rw [projection_section]
  change E.map id=E
  exact List.map_id E

/-- All four actual first homogenized fields, with the given proper carrier/full E. -/
theorem markedPullback_homMarkedAlong {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U)
    (hN : IsClosedSubmanifold n Q.N) (hI : Q.ideal.IsCoherent) (hd : 0<Q.d) :
    markedPullback (m:=n) (zeroSection U) (homMarkedAlong (properNormalMarked Q))=
      homMarkedAlong Q := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ ?_
    (relative_homogenized_trace hN hI hd) rfl
  · exact section_cylinder_carrier U Q.N
  · exact section_cylinder_boundary U Q.E

/-- All four actual first coefficient fields, including the literal empty d=0 sum. -/
theorem markedPullback_coeffMarkedAlong {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U)
    (hN : IsClosedSubmanifold n Q.N) (hI : Q.ideal.IsCoherent) :
    markedPullback (m:=n) (zeroSection U) (coeffMarkedAlong (properNormalMarked Q))=
      coeffMarkedAlong Q := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ ?_
    (relative_coefficient_trace hN hI Q.d) rfl
  · exact section_cylinder_carrier U Q.N
  · exact section_cylinder_boundary U Q.E

end
end Hironaka.HironakaG1ProperCarrierNormalDerivativeTrace
