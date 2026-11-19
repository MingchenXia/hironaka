import Hironaka.Resolution.HironakaActualOriginalTrueMarkMaskCompanions
import Hironaka.Resolution.HironakaActualCoefficientHomogenizedTangent

/-! Genuine proper-carrier tangent inclusion at the two ORIGINAL true marks,
then the actual selected K contact, with SAME window/function, for both sources.
Blueprint FIRST. Saturation by I_N retained; no choice equality or CAN claim. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualTrueMarkCommonContact
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences RelativePrincipalizationSpan
  InvertibleIdealQuotient GermIdealPullbackCalculus GermIdealOrder IdealWeightPowers
  IdealOrderArithmetic DerivativeIdeal DerivativeIdealAlong DerivativeIdealAlongCoherent
  RestrictedIdealExtension HomogenizedIdeal HomogenizedGlueing HomogenizedIdealAlong HomogenizedIdealAlongTower
  TangentDirectionAlong CompanionReductionAlong CompanionRebase CompanionOpen
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  MarkedIdealOperationsTransform ResolutionInvariantSpec BlowupTowers BlowupTowerTransforms StepOneValue StepOneValueMasked
  InvDomainCompanion InvDomainTowerAlong StepOneLowerDomain
  CoefficientIdeal MonomialPartAlong NonmonomialOrderLocal NonmonomialOrderTail
  HironakaEmbeddedAnalytic HironakaActualOriginalTrueMarkMaskCompanions
  HironakaSharpOriginalProductTraceOrder CodimOneSupportAlong
  HironakaActualCoefficientNonmonomialHistoryOrder HironakaActualInitialNonmonomialCoefficientBoundary

variable {n : ℕ} {X : CMfd.{0} n}

private theorem hol {A : GermIdeal n X} (hA : A.IsCoherent) :
    ∀x f,A.mem x f→HolomorphicAt n f x :=
  fun _ _ hf=>GermIdeal.IsCoherent.holomorphicAt_mem hA hf

private theorem sum_le {A B L : GermIdeal n X} (hL : L.IsCoherent)
    (hA : A.Le L) (hB : B.Le L) : (sumIdeal A B).Le L := by
  intro x g hg
  exact HomogenizedIdeal.mem_of_isInSpanAt hL
    ((mem_sumIdeal_iff.mp hg).mono (fun f hf=>hf.elim (hA x f) (hB x f)))

private theorem sat_le {N : Set X} {A L : GermIdeal n X}
    (hA : A.IsCoherent) (hL : L.IsCoherent) (hAL : A.Le L)
    (hNL : (vanishingIdeal (n:=n) N).Le L) : (restrictOn n N A).Le L := by
  rw [restrictOn_eq_sum_vanishingIdeal hA]
  exact sum_le hL hAL hNL

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

private theorem iter_comp (N : Set X) (A : GermIdeal n X) (i : ℕ) :
    ∀j,iterDerivIdealAlong N (iterDerivIdealAlong N A i) j=iterDerivIdealAlong N A (i+j)
  | 0=>rfl
  | j+1=>by rw [iterDerivIdealAlong,iter_comp N A i j,←Nat.add_assoc];rfl

private theorem iter_vanish (N : Set X) :
    ∀r,iterDerivIdealAlong N (vanishingIdeal (n:=n) N) r=vanishingIdeal (n:=n) N
  | 0=>rfl
  | r+1=>by rw [iterDerivIdealAlong,iter_vanish N r,derivIdealAlong_vanishingIdeal]

private theorem vanishing_le_iter {N : Set X} {A : GermIdeal n X} (r : ℕ) (hr : 0<r) :
    (vanishingIdeal (n:=n) N).Le (iterDerivIdealAlong N A r) := by
  obtain ⟨r,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  exact vanishingIdeal_le_derivIdealAlong

private theorem iter_sat {N : Set X} {A : GermIdeal n X}
    (hA : A.IsCoherent) (hN : IsClosedSubmanifold n N) (r : ℕ) :
    iterDerivIdealAlong N (restrictOn n N A) r=restrictOn n N (iterDerivIdealAlong N A r) := by
  rw [restrictOn_eq_sum_vanishingIdeal hA,
    iter_sum hA (VanishingIdealCoherent.isCoherent_vanishingIdeal hN) hN r,iter_vanish]
  rw [restrictOn_eq_sum_vanishingIdeal (isCoherent_iterDerivIdealAlong hA hN r)]

private theorem iter_order_mono {N : Set X} {A : GermIdeal n X}
    (hA : A.IsCoherent) (hN : IsClosedSubmanifold n N) {a b : ℕ} (hab : a≤b) :
    (iterDerivIdealAlong N A a).Le (iterDerivIdealAlong N A b) := by
  obtain ⟨c,rfl⟩:=Nat.exists_eq_add_of_le hab
  rw [←iter_comp N A a c]
  clear hab
  induction c with
  | zero=>exact fun _ _ h=>h
  | succ c ih=>
    intro x g hg
    exact le_derivIdealAlong
      (hol (isCoherent_iterDerivIdealAlong (isCoherent_iterDerivIdealAlong hA hN a) hN c)) x g (ih x g hg)

private theorem deriv_product {N : Set X} {A B : GermIdeal n X}
    (hA : A.IsCoherent) (hB : B.IsCoherent) (hN : IsClosedSubmanifold n N) :
    (derivIdealAlong N (A.mul B)).Le
      (restrictOn n N (sumIdeal ((derivIdealAlong N A).mul B) (A.mul (derivIdealAlong N B)))) := by
  let L:=sumIdeal ((derivIdealAlong N A).mul B) (A.mul (derivIdealAlong N B))
  have hL : L.IsCoherent:=isCoherent_sumIdeal
    (isCoherent_mul (isCoherent_derivIdealAlong hA hN) hB)
    (isCoherent_mul hA (isCoherent_derivIdealAlong hB hN))
  have hSat:=isCoherent_restrictOn_of_isClosedSubmanifold hL hN
  intro x g hg
  apply HomogenizedIdeal.mem_of_isInSpanAt hSat
  refine IsInSpanAt.trans ?_ hg
  rintro s (hs|hs|⟨e,ξ,f,hξ,hf,rfl⟩)
  · have hP : ((derivIdealAlong N A).mul B).mem x s:=IdealOrderArithmetic.mem_mul_iff.mpr
      ((IdealOrderArithmetic.mem_mul_iff.mp hs).mono fun t ⟨a,b,ha,hb,ht⟩=>⟨a,b,le_derivIdealAlong (hol hA) x a ha,hb,ht⟩)
    exact isInSpanAt_self (le_restrictOn hL x s (le_sumIdeal_left
      (isCoherent_mul (isCoherent_derivIdealAlong hA hN) hB) x s hP)) (hol (isCoherent_mul hA hB) x s hs)
  · exact isInSpanAt_self (vanishingIdeal_le_restrictOn x s hs) hs.1
  · have hResult : L.mem x (fieldDeriv e ξ f) := by
      obtain ⟨_,K,r,c,hr,hc,hsum⟩:=IdealOrderArithmetic.mem_mul_iff.mp hf
      choose a b ha hb hab using hr
      have hahol : ∀k,HolomorphicAt n (a k) x:=fun k=>hol hA x _ (ha k)
      have hbhol : ∀k,HolomorphicAt n (b k) x:=fun k=>hol hB x _ (hb k)
      have hrhol : ∀k,HolomorphicAt n (r k) x:=fun k=>by rw [hab k];exact (hahol k).mul (hbhol k)
      have hprod:=fieldDeriv_eventuallyEq_sum_mul (ξ:=ξ) hξ.mem_source hc hrhol hsum
      have hab' : ∀k,fieldDeriv e ξ (r k)=ᶠ[𝓝 x] fun p=>
          fieldDeriv e ξ (a k) p*b k p+a k p*fieldDeriv e ξ (b k) p := by
        intro k
        have h1:=fieldDeriv_eventuallyEq_sum_mul (e:=e) (ξ:=ξ) (f:=r k) (K:=1)
          (a:=fun _=>a k) (s:=fun _=>b k) hξ.mem_source (fun _=>hahol k) (fun _=>hbhol k)
          (by rw [hab k];exact Eventually.of_forall fun p=>by simp)
        simpa using h1
      have hexp : (fun p=>∑k,(fieldDeriv e ξ (c k) p*(a k p*b k p)+
          c k p*(fieldDeriv e ξ (a k) p*b k p)+c k p*(a k p*fieldDeriv e ξ (b k) p)))
          =ᶠ[𝓝 x] fieldDeriv e ξ f := by
        filter_upwards [hprod,eventually_all.mpr hab'] with p hp hp'
        rw [hp]
        refine Finset.sum_congr rfl fun k _=>?_
        rw [hp' k,hab k]
        simp only [Pi.mul_apply]
        ring
      refine mem_sumIdeal_iff.mpr (isInSpanAt_congr ?_ hexp)
      refine IsInSpanAt.sum Finset.univ fun k _=>IsInSpanAt.add (IsInSpanAt.add ?_ ?_) ?_
      · exact isInSpanAt_mul_of_mem (Or.inl (IdealOrderArithmetic.mul_mem_mul
          (le_derivIdealAlong (hol hA) x _ (ha k)) (hb k) ((hahol k).mul (hbhol k))))
          (holomorphicAt_fieldDeriv hξ.mem_source hξ.holomorphicAt (hc k)) ((hahol k).mul (hbhol k))
      · exact isInSpanAt_mul_of_mem (Or.inl (IdealOrderArithmetic.mul_mem_mul (field_mem hA hξ (ha k)) (hb k)
          ((holomorphicAt_fieldDeriv hξ.mem_source hξ.holomorphicAt (hahol k)).mul (hbhol k))))
          (hc k) ((holomorphicAt_fieldDeriv hξ.mem_source hξ.holomorphicAt (hahol k)).mul (hbhol k))
      · exact isInSpanAt_mul_of_mem (Or.inr (IdealOrderArithmetic.mul_mem_mul (ha k) (field_mem hB hξ (hb k))
          ((hahol k).mul (holomorphicAt_fieldDeriv hξ.mem_source hξ.holomorphicAt (hbhol k)))))
          (hc k) ((hahol k).mul (holomorphicAt_fieldDeriv hξ.mem_source hξ.holomorphicAt (hbhol k)))
    exact isInSpanAt_self (le_restrictOn hL x _ hResult)
      (holomorphicAt_fieldDeriv hξ.mem_source hξ.holomorphicAt (hol (isCoherent_mul hA hB) x f hf))

private theorem iter_product_le {N : Set X} (hN : IsClosedSubmanifold n N) :
    ∀r {A B L : GermIdeal n X},A.IsCoherent→B.IsCoherent→L.IsCoherent→
      (vanishingIdeal (n:=n) N).Le L→
      (∀i,i≤r→((iterDerivIdealAlong N A i).mul (iterDerivIdealAlong N B (r-i))).Le L)→
      (iterDerivIdealAlong N (A.mul B) r).Le L
  | 0,A,B,L,_hA,_hB,_hL,_hNL,hParts=>hParts 0 le_rfl
  | r+1,A,B,L,hA,hB,hL,hNL,hParts=>by
    have hDA:=isCoherent_derivIdealAlong hA hN
    have hDB:=isCoherent_derivIdealAlong hB hN
    have hProd:=deriv_product hA hB hN
    have hUpper:=iter_mono (N:=N) hProd r
    have hShift (I : GermIdeal n X) (j : ℕ) : iterDerivIdealAlong N (derivIdealAlong N I) j=
        iterDerivIdealAlong N I (j+1) := by
      change iterDerivIdealAlong N (iterDerivIdealAlong N I 1) j=_
      rw [iter_comp,Nat.add_comm]
    rw [hShift,iter_sat (isCoherent_sumIdeal (isCoherent_mul hDA hB) (isCoherent_mul hA hDB)) hN,
      iter_sum (isCoherent_mul hDA hB) (isCoherent_mul hA hDB) hN] at hUpper
    have hFirst : (iterDerivIdealAlong N ((derivIdealAlong N A).mul B) r).Le L := by
      apply iter_product_le hN r hDA hB hL hNL
      intro i hi
      have hPart:=hParts (i+1) (by omega)
      simpa only [hShift,Nat.add_sub_add_right] using hPart
    have hSecond : (iterDerivIdealAlong N (A.mul (derivIdealAlong N B)) r).Le L := by
      apply iter_product_le hN r hA hDB hL hNL
      intro i hi
      rw [hShift,show (r-i)+1=(r+1)-i by omega]
      exact hParts i (by omega)
    exact fun x g hg=>sat_le (isCoherent_sumIdeal
      (isCoherent_iterDerivIdealAlong (isCoherent_mul hDA hB) hN r)
      (isCoherent_iterDerivIdealAlong (isCoherent_mul hA hDB) hN r)) hL
      (sum_le hL hFirst hSecond) hNL x g (hUpper x g hg)

/-- True finite tangential Leibniz pigeonhole into the SATURATED whole
original derivative ideal. The proper carrier's vanishing ideal is retained. -/
theorem iterDerivAlong_power_pigeonhole {N : Set X} (hN : IsClosedSubmanifold n N)
    {A : GermIdeal n X} (hA : A.IsCoherent) (p s r : ℕ) (hr : r<p*s) :
    (iterDerivIdealAlong N (idealPow A p) r).Le (restrictOn n N (iterDerivIdealAlong N A (s-1))) := by
  have hT:=isCoherent_restrictOn_of_isClosedSubmanifold (isCoherent_iterDerivIdealAlong hA hN (s-1)) hN
  induction p generalizing r with
  | zero=>omega
  | succ p ih=>
    rw [idealPow_succ]
    apply iter_product_le hN r (isCoherent_idealPow hA p) hA hT vanishingIdeal_le_restrictOn
    intro i hi
    by_cases hSmall : r-i<s
    · have hRight:=iter_order_mono hA hN (show r-i≤s-1 by omega)
      have hRightSat : (iterDerivIdealAlong N A (r-i)).Le (restrictOn n N (iterDerivIdealAlong N A (s-1))):=
        fun x g hg=>le_restrictOn (isCoherent_iterDerivIdealAlong hA hN (s-1)) x g (hRight x g hg)
      have hMul:=mul_le_mul' (𝔞:=iterDerivIdealAlong N (idealPow A p) i) (fun _ _ h=>h) hRightSat
      exact fun x g hg=>mul_le_right (fun {_ _} h=>hol
        (isCoherent_iterDerivIdealAlong (isCoherent_idealPow hA p) hN i) _ _ h) hT x g (hMul x g hg)
    · have hIndex : i<p*s:=by rw [Nat.succ_mul] at hr;omega
      have hLeft:=ih i hIndex
      have hMul:=mul_le_mul' (𝔟:=iterDerivIdealAlong N A (r-i)) hLeft (fun _ _ h=>h)
      exact fun x g hg=>mul_le_left hT
        (fun {_ _} h=>hol (isCoherent_iterDerivIdealAlong hA hN (r-i)) _ _ h) x g (hMul x g hg)

private theorem iter_fin_sum_le {N : Set X} (hN : IsClosedSubmanifold n N)
    (A : ℕ→GermIdeal n X) (hA : ∀i,(A i).IsCoherent)
    {L : GermIdeal n X} (hL : L.IsCoherent) (r : ℕ) :
    ∀m,0<m→(∀i,i<m→(iterDerivIdealAlong N (A i) r).Le L)→
      (iterDerivIdealAlong N (finSumIdeal A m) r).Le L
  | 0,hm,_=>False.elim (Nat.not_lt_zero _ hm)
  | 1,_,hParts=>by
    rw [finSumIdeal_one (hA 0)]
    exact hParts 0 (by omega)
  | m+2,_,hParts=>by
    rw [finSumIdeal_succ (fun i _=>hA i),iter_sum (isCoherent_finSumIdeal hA (m+1)) (hA (m+1)) hN r]
    exact sum_le hL (iter_fin_sum_le hN A hA hL r (m+1) (by omega)
      (fun i hi=>hParts i (by omega))) (hParts (m+1) (by omega))

private theorem exponent_inequality {M e p i r : ℕ} (hM : 0<M)
    (hr : M≤r) (hi : i<M) (hBalance : (M-i)*p=M*e) : r*e≤(r-i)*p := by
  have hLe : M*e≤M*p := by
    rw [←hBalance]
    exact Nat.mul_le_mul_right p (Nat.sub_le M i)
  have hep : e≤p := by
    by_contra h
    have hlt : M*p<M*e:=Nat.mul_lt_mul_of_pos_left (Nat.lt_of_not_ge h) hM
    exact Nat.not_lt_of_ge hLe hlt
  calc
    r*e=M*e+(r-M)*e:=by rw [←Nat.add_mul,Nat.add_sub_of_le hr]
    _=(M-i)*p+(r-M)*e:=by rw [hBalance]
    _≤(M-i)*p+(r-M)*p:=Nat.add_le_add_left (Nat.mul_le_mul_left (r-M) hep) _
    _=(r-i)*p:=by rw [←Nat.add_mul];congr 1;omega

private theorem coefficient_mark (Q : MarkedIdeal n X) (hd : 1≤Q.d) :
    (coeffMarkedAlong Q).d=Q.d*sumExp (fun j=>Q.d-j) Q.d 0 := by
  change (Finset.range Q.d).prod (fun j=>(derivMarkedAlong Q j).d)=_
  simpa only [derivMarkedAlong_d,Nat.sub_zero] using
    (mul_sumExp (fun j=>Q.d-j) (show 0<Q.d from hd) (i:=0)).symm

private theorem coefficient_upper (Q : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n Q.N) (hI : Q.ideal.IsCoherent) (hd : 1≤Q.d)
    (μ : ℕ) (hμ : Q.d≤μ) :
    let e:=sumExp (fun j=>Q.d-j) Q.d 0
    (iterDerivIdealAlong Q.N (coeffMarkedAlong Q).ideal (e*μ-1)).Le
      (restrictOn n Q.N (iterDerivIdealAlong Q.N Q.ideal (μ-1))) := by
  let e:=sumExp (fun j=>Q.d-j) Q.d 0
  have he : 1≤e:=one_le_sumExp (fun j hj=>by omega) 0
  have heμ : 0<e*μ:=Nat.mul_pos he (hd.trans hμ)
  have hTarget:=isCoherent_restrictOn_of_isClosedSubmanifold (isCoherent_iterDerivIdealAlong hI hN (μ-1)) hN
  change (iterDerivIdealAlong Q.N (finSumIdeal (fun i=>idealPow (iterDerivIdealAlong Q.N Q.ideal i)
    (sumExp (fun j=>Q.d-j) Q.d i)) Q.d) (e*μ-1)).Le _
  apply iter_fin_sum_le hN _ (fun i=>isCoherent_idealPow (isCoherent_iterDerivIdealAlong hI hN i) _)
    hTarget (e*μ-1) Q.d (show 0<Q.d from hd)
  intro i hi
  let p:=sumExp (fun j=>Q.d-j) Q.d i
  have hBalance : (Q.d-i)*p=Q.d*e := by
    have hZero:=mul_sumExp (fun j=>Q.d-j) (show 0<Q.d from hd) (i:=0)
    have hTerm:=mul_sumExp (fun j=>Q.d-j) hi
    simpa only [Nat.sub_zero] using hTerm.trans hZero.symm
  have hBound:=exponent_inequality (show 0<Q.d from hd) hμ hi hBalance
  have hBound' : e*μ≤p*(μ-i) := by
    calc
      e*μ=μ*e:=Nat.mul_comm _ _
      _≤(μ-i)*p:=hBound
      _=p*(μ-i):=Nat.mul_comm _ _
  have hLess : e*μ-1<p*(μ-i):=lt_of_lt_of_le (Nat.sub_lt heμ (by omega)) hBound'
  have hPow:=iterDerivAlong_power_pigeonhole hN (isCoherent_iterDerivIdealAlong hI hN i)
    p (μ-i) (e*μ-1) hLess
  rw [iter_comp,show i+(μ-i-1)=μ-1 by omega] at hPow
  exact hPow

/-- WHOLE true-mark tangent inclusion of the actual two high-branch
companions. Saturation is derived from the real empty-boundary residual. -/
theorem true_mark_companion_tangent_inclusion (Q : MarkedIdeal n X) {k : ℕ}
    (hQ : IsInvDomain k Q) (hEmpty : Q.E=[]) (μ : ℕ) (hμ : Q.d≤μ) :
    let e:=sumExp (fun j=>Q.d-j) Q.d 0
    let J:=companionOf n Q μ
    let K:=companionOf n (coeffMarkedAlong Q) (e*μ)
    (iterDerivIdealAlong K.N K.ideal (e*μ-1)).Le (iterDerivIdealAlong J.N J.ideal (μ-1)) := by
  let e:=sumExp (fun j=>Q.d-j) Q.d 0
  let J:=companionOf n Q μ
  let K:=companionOf n (coeffMarkedAlong Q) (e*μ)
  have hN:=hQ.isWellFormed.isClosedSubmanifold_N
  have hI:=hQ.isWellFormed.isCoherent
  have hC:=isCoherent_coeffMarkedAlong hI hN
  have hMarkC : (coeffMarkedAlong Q).d≤e*μ := by
    rw [coefficient_mark Q hQ.one_le_d,Nat.mul_comm Q.d e]
    exact Nat.mul_le_mul_left e hμ
  have hJN : J.N=Q.N:=companionAlong_N _ _ _ _ _ _
  have hKN : K.N=Q.N:=companionAlong_N _ _ _ _ _ _
  have hJI : J.ideal=restrictOn n Q.N Q.ideal := by
    simp only [J,companionAlong,if_neg (Nat.not_lt.mpr hμ)]
    rw [hEmpty,nonmonomialPartAlong_nil_eq_restrictOn]
  have hKI : K.ideal=restrictOn n Q.N (coeffMarkedAlong Q).ideal := by
    simp only [K,companionAlong,if_neg (Nat.not_lt.mpr hMarkC)]
    change nonmonomialPartAlong n Q.N (coeffMarkedAlong Q).ideal Q.E=_
    rw [hEmpty,nonmonomialPartAlong_nil_eq_restrictOn]
  change (iterDerivIdealAlong K.N K.ideal (e*μ-1)).Le (iterDerivIdealAlong J.N J.ideal (μ-1))
  rw [hKN,hJN,hKI,hJI,iter_sat hC hN,iter_sat hI hN]
  exact sat_le (isCoherent_iterDerivIdealAlong hC hN (e*μ-1))
    (isCoherent_restrictOn_of_isClosedSubmanifold (isCoherent_iterDerivIdealAlong hI hN (μ-1)) hN)
    (coefficient_upper Q hN hI hQ.one_le_d μ hμ) vanishingIdeal_le_restrictOn

/-- Actual ordinary original lower inputs yield a NONEMPTY normalized
cosupport and the native selected K window/function as a common J/K contact. -/
theorem original_lower_selected_common_contact (hn : 0<n) (Q : MarkedIdeal n X)
    {k : ℕ}(hQ : IsInvDomain k Q) (hN : Q.N=univ) (hE : Q.E=[])
    (hMax : IsMaximalOrderAlong Q.N Q.ideal Q.d)
    (W : Set X)(hW : IsComplexAnalyticSubset (n:=n) W)
    (hSing : Q.cosupp⊆singularSet (n:=n) W)(a : X)(ha : a∈Q.cosupp) :
    ∃hm : a∈maskB Q (.refl : BlowupTower X X) a,
      let V:=maskB Q (.refl : BlowupTower X X) a
      let L : MarkedIdeal n (CMfd.of (n:=n) V):=lowerMarkedB Q (.refl : BlowupTower X X) a
      let x : V:=⟨a,hm⟩
      let μ:=nmOrd L x
      let e:=sumExp (fun j=>L.d-j) L.d 0
      let U:=ordMask L μ
      let P : MarkedIdeal n (CMfd.of (n:=n) U):=MarkedIdeal.pullback (Subtype.val : U→V) L
      let B : MarkedIdeal n (CMfd.of (n:=n) U):=MarkedIdeal.pullback (Subtype.val : U→V) (coeffMarkedAlong L)
      let J:=companionOf n P μ
      let K:=companionOf n B (e*μ)
      ∃hxU : x∈U,
        IsInvDomain (k-1) J ∧ IsInvDomain (k-1) K ∧ J.N=K.N ∧ J.d=μ ∧ K.d=e*μ ∧
        (⟨x,hxU⟩ : U)∈J.cosupp ∧ (⟨x,hxU⟩ : U)∈K.cosupp ∧
        (iterDerivIdealAlong K.N K.ideal (K.d-1)).Le (iterDerivIdealAlong J.N J.ideal (J.d-1)) ∧
        ∀z∈K.cosupp,
          z∈(tangentChoice K z).1 ∧
          IsTangentDirectionAlong K.N K.ideal K.d (tangentChoice K z).1 (tangentChoice K z).2 ∧
          IsTangentDirectionAlong J.N J.ideal J.d (tangentChoice K z).1 (tangentChoice K z).2 ∧
          J.cosupp∩(tangentChoice K z).1⊆{y | (tangentChoice K z).2 y=0} ∧
          K.cosupp∩(tangentChoice K z).1⊆{y | (tangentChoice K z).2 y=0} := by
  obtain ⟨hm,hxU,_hMask,hNatural,hJ,hK,_hJMax,hKMax,hJN,hKN,_hJE,_hKE,hJd,hKd,
    _hJNative,_hKNative,hWeak,_hHistories⟩:=
    original_lower_true_mark_companions hn Q hQ hN hE hMax W hW hSing a ha
  obtain ⟨_hm0,hL,hEmpty,hxL,hμ,_hMask0⟩:=
    original_lower_true_mark_mask hn Q hQ hN hE hMax W hW hSing a ha
  let V:=maskB Q (.refl : BlowupTower X X) a
  let L : MarkedIdeal n (CMfd.of (n:=n) V):=lowerMarkedB Q (.refl : BlowupTower X X) a
  let x : V:=⟨a,hm⟩
  let μ:=nmOrd L x
  let e:=sumExp (fun j=>L.d-j) L.d 0
  let U:=ordMask L μ
  let P : MarkedIdeal n (CMfd.of (n:=n) U):=MarkedIdeal.pullback (Subtype.val : U→V) L
  let B : MarkedIdeal n (CMfd.of (n:=n) U):=MarkedIdeal.pullback (Subtype.val : U→V) (coeffMarkedAlong L)
  let J:=companionOf n P μ
  let K:=companionOf n B (e*μ)
  change IsInvDomain (k-1) L at hL
  change L.E=[] at hEmpty
  change x∈L.cosupp at hxL
  change L.d≤μ at hμ
  change x∈U at hxU
  change B=coeffMarkedAlong P at hNatural
  change IsInvDomain (k-1) J at hJ
  change IsInvDomain (k-1) K at hK
  change J.N=P.N at hJN
  change K.N=P.N at hKN
  change J.d=μ at hJd
  change K.d=e*μ at hKd
  change MarkedIdealEquivalence.MarkedIdeal.WEquiv J K at hWeak
  have hP : IsInvDomain (k-1) P:=isInvDomain_pullback_val U hL
  have hB : IsInvDomain (k-1) B:=by rw [hNatural];exact coefficient_isInvDomain P hP
  have hPE : P.E=[]:=by
    change L.E.map ((Subtype.val : U→V) ⁻¹' ·)=[]
    rw [hEmpty,List.map_nil]
  have hNK : J.N=K.N:=hJN.trans hKN.symm
  have hIncl : (iterDerivIdealAlong K.N K.ideal (K.d-1)).Le
      (iterDerivIdealAlong J.N J.ideal (J.d-1)) := by
    rw [hKd,hJd]
    change (iterDerivIdealAlong (companionOf n B (e*μ)).N (companionOf n B (e*μ)).ideal (e*μ-1)).Le _
    rw [hNatural]
    exact true_mark_companion_tangent_inclusion P hP hPE μ hμ
  let z₀ : U:=⟨x,hxU⟩
  have hzP : z₀∈P.cosupp:=by
    change z₀∈(MarkedIdeal.pullback (Subtype.val : U→V) L).cosupp
    rw [cosupp_pullback_val L (hol hL.isWellFormed.isCoherent) U]
    exact hxL
  have hRawP : nmOrd P z₀=μ:=nmOrd_pullback_val hn hL.isWellFormed hL.isNonzeroAlongAt U z₀
  have hRawB:=original_coefficient_nonmonomial_order P hP hPE
    (.refl : BlowupTower (CMfd.of (n:=n) U) (CMfd.of (n:=n) U)) trivial z₀ hzP
  change nmOrd (coeffMarkedAlong P) z₀=e*nmOrd P z₀ at hRawB
  rw [←hNatural,hRawP] at hRawB
  have hMarkB : B.d≤e*μ:=by
    change (coeffMarkedAlong L).d≤e*μ
    rw [coefficient_mark L hL.one_le_d,Nat.mul_comm L.d e]
    exact Nat.mul_le_mul_left e hμ
  have hKCut : K.cosupp=ordGe B (e*μ):=by
    simp only [K,companionAlong,if_neg (Nat.not_lt.mpr hMarkB)]
    rfl
  have hzK : z₀∈K.cosupp:=by
    rw [hKCut]
    exact (mem_ordGe_iff hB.isWellFormed hB.isNonzeroAlongAt hzP.1 (e*μ)).mpr (by rw [hRawB])
  have hzJ : z₀∈J.cosupp:=hWeak.cosupp_eq.symm ▸ hzK
  refine ⟨hm,hxU,hJ,hK,hNK,hJd,hKd,hzJ,hzK,hIncl,?_⟩
  intro z hz
  obtain ⟨hzV,huK⟩:=tangentChoice_spec K
    (exists_isTangentDirectionAlong_of_isMaximalOrderAlong hK.isWellFormed.isCoherent
      hK.isWellFormed.isClosedSubmanifold_N hK.one_le_d hKMax hz)
  have huJ : IsTangentDirectionAlong J.N J.ideal J.d (tangentChoice K z).1 (tangentChoice K z).2 := {
    isOpen:=huK.isOpen
    mem:=fun y hy=>hIncl y _ (huK.mem y hy)
    multiplicity_one:=by rw [hNK];exact huK.multiplicity_one }
  exact ⟨hzV,huK,huJ,huJ.cosupport_inter_subset (hol hJ.isWellFormed.isCoherent) hJ.one_le_d,
    huK.cosupport_inter_subset (hol hK.isWellFormed.isCoherent) hK.one_le_d⟩

end
end Hironaka.HironakaActualTrueMarkCommonContact
