import Hironaka.Resolution.HironakaActualHomogenizedTangentStability
import Hironaka.Resolution.HironakaActualWeightedNormalBarDerivatives
import Hironaka.Invariant.CanonicalCentres

/-! The actual whole tangent ideal across factorial coefficient recoding.
Blueprint FIRST: hironaka-actual-coefficient-homogenized-tangent.tex. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualCoefficientHomogenizedTangent
noncomputable section
open Hironaka.HolomorphicIdealSheaves RelativePrincipalizationSpan
  InvertibleIdealQuotient GermIdealPullbackCalculus GermIdealOrder IdealWeightPowers
  IdealOrderArithmetic DerivativeIdeal HomogenizedGlueing HomogenizedEquivalence
  CoefficientIdeal RestrictedIdealExtension GermIdealTotalTransform MaximalContact
  MarkedIdealOperationsTransform HironakaActualWeightedNormalAmbientDerivatives
  HironakaActualHomogenizedTangentStability HironakaActualWeightedNormalBarDerivatives
  HironakaActualAdaptedContactDerivation HironakaSmoothSubmersionGermIdealColon
  HomogenizedIdealAlong DerivativeIdealAlong TangentDirectionAlong MarkedIdeals StepOneValue BlowupTowers

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

omit [IsComplexManifold n X] in
private theorem hol {I : GermIdeal n X} (hI : I.IsCoherent) :
    ∀x f,I.mem x f→HolomorphicAt n f x :=
  fun _ _ hf=>GermIdeal.IsCoherent.holomorphicAt_mem hI hf

private theorem sum_le {A B L : GermIdeal n X} (hL : L.IsCoherent)
    (hA : A.Le L) (hB : B.Le L) : (sumIdeal A B).Le L := by
  intro x g hg
  exact HomogenizedIdeal.mem_of_isInSpanAt hL
    ((mem_sumIdeal_iff.mp hg).mono (fun f hf=>hf.elim (hA x f) (hB x f)))

private theorem iter_shift (A : GermIdeal n X) (j : ℕ) :
    iterDerivIdeal (derivIdeal A) j=iterDerivIdeal A (j+1) := by
  change iterDerivIdeal (iterDerivIdeal A 1) j=_
  rw [iterDerivIdeal_iterDerivIdeal,Nat.add_comm]

private theorem iter_order_mono {A : GermIdeal n X} (hA : A.IsCoherent)
    {a b : ℕ} (hab : a≤b) : (iterDerivIdeal A a).Le (iterDerivIdeal A b) := by
  obtain ⟨c,rfl⟩:=Nat.exists_eq_add_of_le hab
  rw [←iterDerivIdeal_iterDerivIdeal A a c]
  exact le_iterDerivIdeal (hol (isCoherent_iterDerivIdeal hA a)) c

private theorem iter_product_le :
    ∀r {A B L : GermIdeal n X}, A.IsCoherent→B.IsCoherent→L.IsCoherent→
      (∀i,i≤r→((iterDerivIdeal A i).mul (iterDerivIdeal B (r-i))).Le L)→
      (iterDerivIdeal (A.mul B) r).Le L
  | 0,A,B,L,hA,hB,hL,hParts=>by
    exact hParts 0 le_rfl
  | r+1,A,B,L,hA,hB,hL,hParts=>by
    have hUpper:=iterDerivIdeal_mono (derivIdeal_mul_le (hol hA) (hol hB)) r
    rw [iter_shift,iterDerivIdeal_sum (isCoherent_mul (isCoherent_derivIdeal hA) hB)
      (isCoherent_mul hA (isCoherent_derivIdeal hB))] at hUpper
    have hFirst : (iterDerivIdeal ((derivIdeal A).mul B) r).Le L := by
      apply iter_product_le r (isCoherent_derivIdeal hA) hB hL
      intro i hi
      have hPart:=hParts (i+1) (by omega)
      simpa only [iter_shift,Nat.add_sub_add_right] using hPart
    have hSecond : (iterDerivIdeal (A.mul (derivIdeal B)) r).Le L := by
      apply iter_product_le r hA (isCoherent_derivIdeal hB) hL
      intro i hi
      rw [iter_shift,show (r-i)+1=(r+1)-i by omega]
      exact hParts i (by omega)
    exact fun x g hg=>sum_le hL hFirst hSecond x g (hUpper x g hg)

/-- True finite Leibniz pigeonhole on the SAME whole native ideal powers.
There is no order, quotient, or derivative-comparison certificate input. -/
theorem iterDeriv_power_pigeonhole {A : GermIdeal n X} (hA : A.IsCoherent)
    (p s r : ℕ) (hr : r<p*s) :
    (iterDerivIdeal (idealPow A p) r).Le (iterDerivIdeal A (s-1)) := by
  induction p generalizing r with
  | zero=>omega
  | succ p ih=>
    rw [idealPow_succ]
    apply iter_product_le r (isCoherent_idealPow hA p) hA (isCoherent_iterDerivIdeal hA (s-1))
    intro i hi
    by_cases hSmall : r-i<s
    · have hRight:=iter_order_mono hA (show r-i≤s-1 by omega)
      have hMul:=mul_le_mul' (𝔞:=iterDerivIdeal (idealPow A p) i) (fun _ _ h=>h) hRight
      exact fun x g hg=>mul_le_right (fun {_ _} h=>hol (isCoherent_iterDerivIdeal
        (isCoherent_idealPow hA p) i) _ _ h) (isCoherent_iterDerivIdeal hA (s-1)) x g (hMul x g hg)
    · have hIndex : i<p*s := by
        rw [Nat.succ_mul] at hr
        omega
      have hLeft:=ih i hIndex
      have hMul:=mul_le_mul' (𝔟:=iterDerivIdeal A (r-i)) hLeft (fun _ _ h=>h)
      exact fun x g hg=>mul_le_left (isCoherent_iterDerivIdeal hA (s-1))
        (fun {_ _} h=>hol (isCoherent_iterDerivIdeal hA (r-i)) _ _ h) x g (hMul x g hg)

private theorem iter_fin_sum_le (A : ℕ→GermIdeal n X) (hA : ∀i,(A i).IsCoherent)
    {L : GermIdeal n X} (hL : L.IsCoherent) (r : ℕ) :
    ∀m,0<m→(∀i,i<m→(iterDerivIdeal (A i) r).Le L)→
      (iterDerivIdeal (finSumIdeal A m) r).Le L
  | 0,hm,_=>False.elim (Nat.not_lt_zero _ hm)
  | 1,_,hParts=>by
    rw [finSumIdeal_one (hA 0)]
    exact hParts 0 (by omega)
  | m+2,_,hParts=>by
    rw [finSumIdeal_succ (fun i _=>hA i),
      iterDerivIdeal_sum (isCoherent_finSumIdeal hA (m+1)) (hA (m+1)) r]
    exact sum_le hL (iter_fin_sum_le A hA hL r (m+1) (by omega)
      (fun i hi=>hParts i (by omega))) (hParts (m+1) (by omega))

private theorem bar_coherent {I : GermIdeal n X} (hI : I.IsCoherent) (d : ℕ) :
    (barIdeal I d).IsCoherent := isCoherent_finSumIdeal
      (fun i=>isCoherent_idealPow (isCoherent_iterDerivIdeal
        (isCoherent_homogenizedIdeal hI d) i) _) d

/-- The ENTIRE actual tangent ideal survives coefficient recoding at its
literal factorial mark. Maximal order supplies contact internally. -/
theorem coefficient_homogenized_tangent_ideal {I : GermIdeal n X} (hI : I.IsCoherent)
    {d : ℕ} (hd : 1≤d) (hMax : IsMaximalOrder I d) :
    iterDerivIdeal (barIdeal I d) ((Finset.range d).prod (fun j=>d-j)-1)=
      iterDerivIdeal I (d-1) := by
  let H:=HomogenizedIdeal.homogenizedIdeal I d
  let T:=iterDerivIdeal I (d-1)
  let D:=(Finset.range d).prod (fun j=>d-j)
  let B:=barIdeal I d
  have hH : H.IsCoherent:=isCoherent_homogenizedIdeal hI d
  have hT : T.IsCoherent:=isCoherent_iterDerivIdeal hI (d-1)
  have hB : B.IsCoherent:=bar_coherent hI d
  have hBD : (iterDerivIdeal B (D-1)).IsCoherent:=isCoherent_iterDerivIdeal hB (D-1)
  have hD : 0<D := by
    apply Finset.prod_pos
    intro i hi
    exact Nat.sub_pos_of_lt (Finset.mem_range.mp hi)
  have hTangent : iterDerivIdeal H (d-1)=T:=homogenized_tangent_ideal hI (by omega)
  have hExp : sumExp (fun j=>d-j) d (d-1)=D := by
    have he:=mul_sumExp (fun j=>d-j) (show d-1<d by omega)
    simpa only [show d-(d-1)=1 by omega,one_mul] using he
  have hLast : (idealPow T D).Le B := by
    intro x f hf
    change IsInSpanAt (n:=n) (fun g=>∃i,i<d ∧
      (idealPow (iterDerivIdeal H i) (sumExp (fun j=>d-j) d i)).mem x g) x f
    have hTerm : (idealPow (iterDerivIdeal H (d-1))
        (sumExp (fun j=>d-j) d (d-1))).mem x f := by
      simpa only [hTangent,hExp] using hf
    exact isInSpanAt_self ⟨d-1,by omega,hTerm⟩ (hol (isCoherent_idealPow hT D) x f hf)
  have hUpper : (iterDerivIdeal B (D-1)).Le T := by
    apply iter_fin_sum_le (fun i=>idealPow (iterDerivIdeal H i)
      (sumExp (fun j=>d-j) d i))
      (fun i=>isCoherent_idealPow (isCoherent_iterDerivIdeal hH i) _) hT (D-1) d (by omega)
    intro i hi
    have hProduct:=mul_sumExp (fun j=>d-j) hi
    have hLess : D-1<sumExp (fun j=>d-j) d i*(d-i) := by
      rw [Nat.mul_comm,hProduct]
      exact Nat.sub_lt hD (by omega)
    have hBound:=iterDeriv_power_pigeonhole (isCoherent_iterDerivIdeal hH i)
      (sumExp (fun j=>d-j) d i) (d-i) (D-1) hLess
    rw [iterDerivIdeal_iterDerivIdeal,show i+(d-i-1)=d-1 by omega,hTangent] at hBound
    exact hBound
  have hLower : T.Le (iterDerivIdeal B (D-1)) := by
    intro x f hf
    have hfh : HolomorphicAt n f x:=hol hT x f hf
    by_cases hx : x∈cosupport n univ I d
    · obtain ⟨U,u,hxU,hu⟩:=exists_isTangentDirection hI (hol hI) hd hMax hx
      let Φ:=HironakaHolomorphicJetRankLoci.translationEquiv (chartAt (ComplexModel n) x x)
      have h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0:=sub_self _
      obtain ⟨huh,hRec⟩:=actual_contact_adapted_power_recovery I hI d hd U u hu x hxU hx Φ h0
      have huT : T.mem x u:=hu.mem x hxU
      have hPower : B.mem x (fun y=>u y^D):=
        hLast x _ (HomogenizedIdeal.pow_mem_idealPow huT huh D)
      have hProduct : B.mem x (fun y=>u y^(D-1)*f y) := by
        have hMul:=IdealOrderArithmetic.mul_mem_mul
          (HomogenizedIdeal.pow_mem_idealPow huT huh (D-1)) hf
          ((CompanionReduction.holomorphicAt_pow_of huh (D-1)).mul hfh)
        have hIndex : (D-1)+1=D:=by omega
        have hPow : (idealPow T D).mem x (fun y=>u y^(D-1)*f y) := by
          rw [←hIndex,idealPow_succ]
          exact hMul
        exact hLast x _ hPow
      have hProductHol:=hol hB x _ hProduct
      have hGermProduct : (adaptedGerm x Φ h0 u huh)^(D-1)*adaptedGerm x Φ h0 f hfh∈
          adaptedIdeal B x Φ h0 := by
        have huFlat:=(holomorphic_adapted_iff x Φ h0 u).mpr huh
        have hfFlat:=(holomorphic_adapted_iff x Φ h0 f).mpr hfh
        have hEq : adaptedGerm x Φ h0 (fun y=>u y^(D-1)*f y) hProductHol=
            (adaptedGerm x Φ h0 u huh)^(D-1)*adaptedGerm x Φ h0 f hfh := by
          have hm:=HolGerm.mk_mul
            (fun z=>u ((chartAt (ComplexModel n) x).symm (Φ.invFun z))^(D-1))
            (fun z=>f ((chartAt (ComplexModel n) x).symm (Φ.invFun z)))
            (eventually_differentiableAt_pow huFlat (D-1)) hfFlat
          rw [HolGerm.mk_pow] at hm
          exact hm
        rw [←hEq]
        exact Ideal.subset_span ⟨_,hProductHol,hProduct,rfl⟩
      have hRecovered:=hRec B T hB hT
        (coefficient_homogenized_tangent_stability hI (by omega)) huT D hPower (D-1)
        (adaptedGerm x Φ h0 f hfh) hGermProduct
      exact (mem_adaptedIdeal_iff _ hBD x Φ h0 f hfh).mp hRecovered
    · have hxT : x∉T.zeroLocus := by
        rw [←OrderTaylor.cosupport_succ_eq_zeroLocus_iterDerivIdeal (hol hI) (d-1),
          show (d-1)+1=d by omega]
        exact hx
      obtain ⟨g,hg,hgx⟩:=CompanionReduction.exists_mem_ne_zero_of_notMem_zeroLocus hxT
      have hUnitT:=CompanionReduction.one_mem_of_apply_ne_zero hT hg hgx
      have hUnitB : B.mem x (fun _=>1) := by
        simpa only [one_pow] using hLast x _
          (HomogenizedIdeal.pow_mem_idealPow hUnitT (holomorphicAt_const 1) D)
      have hUnitD:=le_iterDerivIdeal (hol hB) (D-1) x _ hUnitB
      apply HomogenizedIdeal.mem_of_isInSpanAt hBD
      exact isInSpanAt_of_eq_mul hUnitD hfh hfh (Eventually.of_forall fun _=>by simp)
  exact GermIdeal.ext (funext fun x=>funext fun f=>propext ⟨hUpper x f,hLower x f⟩)

/-- Across the ACTUAL factorial mark, the native entire along-tangent ideal
and the existing native contact-choice function are literally unchanged. -/
theorem original_bar_tangentChoice {A : CMfd.{0} n} (Q : MarkedIdeal n A)
    (hN : Q.N=univ) (hI : Q.ideal.IsCoherent) (hd : 1≤Q.d)
    (hMax : IsMaximalOrderAlong Q.N Q.ideal Q.d) :
    iterDerivIdealAlong (barMarked Q).N (barMarked Q).ideal ((barMarked Q).d-1)=
        iterDerivIdealAlong Q.N Q.ideal (Q.d-1) ∧
      tangentChoice (barMarked Q)=tangentChoice Q := by
  have hHI : (homMarked Q).ideal.IsCoherent:=isCoherent_homogenizedIdeal hI Q.d
  have hHC : homMarkedAlong Q=homMarked Q:=homMarkedAlong_eq_homMarked hN (hol hI)
  have hBC : barMarked Q=coeffMarked (homMarked Q) := by
    change coeffMarkedAlong (homMarkedAlong Q)=_
    rw [hHC,coeffMarkedAlong_eq_coeffMarked (𝔪:=homMarked Q) hN (hol hHI)]
  have hBI : (barMarked Q).ideal=barIdeal Q.ideal Q.d := by
    rw [hBC]
    rfl
  have hBCoh : (barMarked Q).ideal.IsCoherent := by
    rw [hBI]
    exact bar_coherent hI Q.d
  have hBM : (barMarked Q).d=(Finset.range Q.d).prod (fun j=>Q.d-j):=rfl
  have hBN : (barMarked Q).N=Q.N:=rfl
  have hAmbientMax : IsMaximalOrder Q.ideal Q.d := by
    apply (isMaximalOrderAlong_univ_iff hI).mp
    simpa only [hN] using hMax
  have hTangent : iterDerivIdealAlong (barMarked Q).N (barMarked Q).ideal
      ((barMarked Q).d-1)=iterDerivIdealAlong Q.N Q.ideal (Q.d-1) := by
    rw [hBN,hN,iterDerivIdealAlong_univ (hol hBCoh),iterDerivIdealAlong_univ (hol hI),hBI,hBM]
    exact coefficient_homogenized_tangent_ideal hI hd hAmbientMax
  have hPredicate : IsTangentDirectionAlong (barMarked Q).N (barMarked Q).ideal
      (barMarked Q).d=IsTangentDirectionAlong Q.N Q.ideal Q.d := by
    funext U w
    apply propext
    constructor
    · rintro ⟨ho,hm,hMult⟩
      exact ⟨ho,fun x hx=>hTangent ▸ hm x hx,hMult⟩
    · rintro ⟨ho,hm,hMult⟩
      exact ⟨ho,fun x hx=>hTangent.symm ▸ hm x hx,hMult⟩
  refine ⟨hTangent,?_⟩
  funext x
  let choosePair (P : Set A→(A→ℂ)→Prop) : Set A × (A→ℂ) :=
    if h : ∃U w,x∈U ∧ P U w then (h.choose,h.choose_spec.choose) else (∅,0)
  change choosePair (IsTangentDirectionAlong (barMarked Q).N (barMarked Q).ideal (barMarked Q).d)=
    choosePair (IsTangentDirectionAlong Q.N Q.ideal Q.d)
  rw [hPredicate]

end
end Hironaka.HironakaActualCoefficientHomogenizedTangent
