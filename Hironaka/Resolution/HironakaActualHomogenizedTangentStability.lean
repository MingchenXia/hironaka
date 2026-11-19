import Hironaka.Resolution.HironakaActualWeightedNormalHomogenizedDerivatives

/-! Actual tangent stability and idempotence at the SAME original mark.
Blueprint: hironaka-actual-homogenized-tangent-stability-20261102.tex. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualHomogenizedTangentStability
noncomputable section
open Hironaka.HolomorphicIdealSheaves RelativePrincipalizationSpan
  InvertibleIdealQuotient GermIdealPullbackCalculus GermIdealOrder IdealWeightPowers
  IdealOrderArithmetic DerivativeIdeal HomogenizedGlueing HomogenizedEquivalence
  CoefficientIdeal RestrictedIdealExtension GermIdealTotalTransform
  HironakaActualWeightedNormalHomogenizedDerivatives

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

omit [IsComplexManifold n X] in
private theorem hol {I : GermIdeal n X} (hI : I.IsCoherent) :
    ∀x f,I.mem x f → HolomorphicAt n f x:=
  fun _ _ hf=>GermIdeal.IsCoherent.holomorphicAt_mem hI hf

private theorem mul_mono {A A' B B' : GermIdeal n X} (hA : A.Le A') (hB : B.Le B') :
    (A.mul B).Le (A'.mul B'):=by
  intro x g hg
  exact IdealOrderArithmetic.mem_mul_iff.mpr ((IdealOrderArithmetic.mem_mul_iff.mp hg).mono
    (fun _ ⟨a,b,ha,hb,he⟩=>⟨a,b,hA x a ha,hB x b hb,he⟩))

private theorem sum_le {A B L : GermIdeal n X} (hL : L.IsCoherent)
    (hA : A.Le L) (hB : B.Le L) : (sumIdeal A B).Le L:=by
  intro x g hg
  exact HomogenizedIdeal.mem_of_isInSpanAt hL
    ((mem_sumIdeal_iff.mp hg).mono (fun f hf=>hf.elim (hA x f) (hB x f)))

private theorem mul_span_right {L : GermIdeal n X} (hL : L.IsCoherent)
    {x : X} {S : (X→ℂ)→Prop} {p q : X→ℂ} (hq : HolomorphicAt n q x)
    (hp : IsInSpanAt (n:=n) S x p)
    (hGen : ∀a,S a → L.mem x (fun z=>a z*q z)) : L.mem x (fun z=>p z*q z):=by
  obtain ⟨hph,K,s,c,hs,hc,hSum⟩:=hp
  apply HomogenizedIdeal.mem_of_isInSpanAt hL
  refine ⟨hph.mul hq,K,(fun i z=>s i z*q z),c,(fun i=>hGen _ (hs i)),hc,?_⟩
  filter_upwards [hSum] with z hz
  rw [hz,Finset.sum_mul]
  exact Finset.sum_congr rfl (fun i _=>by ring)

private theorem mul_sum_le {A B T L : GermIdeal n X}
    (hA : A.IsCoherent) (hB : B.IsCoherent) (hT : T.IsCoherent) (hL : L.IsCoherent)
    (hAT : (A.mul T).Le L) (hBT : (B.mul T).Le L) : ((sumIdeal A B).mul T).Le L:=by
  intro x g hg
  apply HomogenizedIdeal.mem_of_isInSpanAt hL
  refine IsInSpanAt.trans ?_ (IdealOrderArithmetic.mem_mul_iff.mp hg)
  rintro _ ⟨p,q,hp,hq,rfl⟩
  change IsInSpanAt (n:=n) (fun f=>A.mem x f ∨ B.mem x f) x p at hp
  have hqhol:=hol hT x q hq
  apply isInSpanAt_self ?_ (hp.holomorphicAt.mul hqhol)
  apply mul_span_right hL hqhol hp
  rintro a (ha | ha)
  · exact hAT x _ (IdealOrderArithmetic.mul_mem_mul ha hq ((hol hA x a ha).mul hqhol))
  · exact hBT x _ (IdealOrderArithmetic.mul_mem_mul ha hq ((hol hB x a ha).mul hqhol))

private theorem mul_finSum_le (A : ℕ→GermIdeal n X) (hA : ∀i,(A i).IsCoherent)
    {T L : GermIdeal n X} (hT : T.IsCoherent) (hL : L.IsCoherent) (m : ℕ)
    (hAT : ∀i,i<m → ((A i).mul T).Le L) : ((finSumIdeal A m).mul T).Le L:=by
  intro x g hg
  apply HomogenizedIdeal.mem_of_isInSpanAt hL
  refine IsInSpanAt.trans ?_ (IdealOrderArithmetic.mem_mul_iff.mp hg)
  rintro _ ⟨p,q,hp,hq,rfl⟩
  change IsInSpanAt (n:=n) (fun f=>∃i,i<m ∧ (A i).mem x f) x p at hp
  have hqhol:=hol hT x q hq
  apply isInSpanAt_self ?_ (hp.holomorphicAt.mul hqhol)
  apply mul_span_right hL hqhol hp
  rintro a ⟨i,hi,ha⟩
  exact hAT i hi x _ (IdealOrderArithmetic.mul_mem_mul ha hq ((hol (hA i) x a ha).mul hqhol))

omit [IsComplexManifold n X] in
private theorem fin_term_le (A : ℕ→GermIdeal n X) (hA : ∀i,(A i).IsCoherent)
    {i m : ℕ} (hi : i<m) : (A i).Le (finSumIdeal A m):=by
  intro x g hg
  change IsInSpanAt (n:=n) (fun f=>∃i,i<m ∧ (A i).mem x f) x g
  exact isInSpanAt_self ⟨i,hi,hg⟩ (hol (hA i) x g hg)

/-- Stability under the SAME actual tangent ideal passes to one derivative. -/
theorem derivative_tangent_stability {A T : GermIdeal n X}
    (hA : A.IsCoherent) (hT : T.IsCoherent) (hStable : ((derivIdeal A).mul T).Le A) :
    ((derivIdeal (derivIdeal A)).mul T).Le (derivIdeal A):=by
  have hRecovery:=derivative_product_recovery (isCoherent_derivIdeal hA) hT
  have hFirst:=derivIdeal_mono hStable
  have hSecond : ((derivIdeal A).mul (derivIdeal T)).Le (derivIdeal A):=
    mul_le_left (isCoherent_derivIdeal hA) (fun {_ _} h=>holomorphicAt_of_mem_derivIdeal h)
  exact fun x g hg=>sum_le (isCoherent_derivIdeal hA) hFirst hSecond x g (hRecovery x g hg)

/-- Every actual derivative retains stability with the SAME original tangent. -/
theorem iterDeriv_tangent_stability {A T : GermIdeal n X}
    (hA : A.IsCoherent) (hT : T.IsCoherent) (hStable : ((derivIdeal A).mul T).Le A) :
    ∀i,((iterDerivIdeal A (i+1)).mul T).Le (iterDerivIdeal A i)
  | 0=>hStable
  | i+1=>derivative_tangent_stability (isCoherent_iterDerivIdeal hA i) hT
      (iterDeriv_tangent_stability hA hT hStable i)

/-- All actual powers, including the unit power, retain tangent stability. -/
theorem power_tangent_stability {A T : GermIdeal n X}
    (hA : A.IsCoherent) (hT : T.IsCoherent) (hStable : ((derivIdeal A).mul T).Le A) :
    ∀e,((derivIdeal (idealPow A e)).mul T).Le (idealPow A e)
  | 0=>by
    intro x g hg
    exact (IdealOrderArithmetic.mem_mul_iff.mp hg).holomorphicAt
  | e+1=>by
    have hP:=isCoherent_idealPow hA e
    have hDP:=isCoherent_derivIdeal hP
    have hDA:=isCoherent_derivIdeal hA
    have hFirst : (((derivIdeal (idealPow A e)).mul A).mul T).Le (idealPow A (e+1)):=by
      rw [GermIdealTotalTransform.mul_assoc hDP hA hT,RestrictLeCalculus.mul_comm' A T,
        ←GermIdealTotalTransform.mul_assoc hDP hT hA,idealPow_succ]
      exact mul_mono (power_tangent_stability hA hT hStable e) (fun _ _ h=>h)
    have hSecond : (((idealPow A e).mul (derivIdeal A)).mul T).Le (idealPow A (e+1)):=by
      rw [GermIdealTotalTransform.mul_assoc hP hDA hT,idealPow_succ]
      exact mul_mono (fun _ _ h=>h) hStable
    have hLeibniz:=derivIdeal_mul_le (hol hP) (hol hA)
    have hUpper:=mul_mono (B:=T) (B':=T) hLeibniz (fun _ _ h=>h)
    have hSum:=mul_sum_le (isCoherent_mul hDP hA) (isCoherent_mul hP hDA) hT
      (isCoherent_idealPow hA (e+1)) hFirst hSecond
    exact fun x g hg=>hSum x g (hUpper x g hg)

private theorem deriv_finSumIdeal (A : ℕ→GermIdeal n X) (hA : ∀i,(A i).IsCoherent) :
    ∀m,0<m → derivIdeal (finSumIdeal A m)=finSumIdeal (fun i=>derivIdeal (A i)) m
  | 0,hm=>False.elim (Nat.not_lt_zero _ hm)
  | 1,_=>by rw [finSumIdeal_one (hA 0),finSumIdeal_one (isCoherent_derivIdeal (hA 0))]
  | m+2,_=>by
    rw [finSumIdeal_succ (fun i _=>hA i),
      show derivIdeal (sumIdeal (finSumIdeal A (m+1)) (A (m+1)))=
          sumIdeal (derivIdeal (finSumIdeal A (m+1))) (derivIdeal (A (m+1))) from
        HironakaActualWeightedNormalAmbientDerivatives.iterDerivIdeal_sum
          (isCoherent_finSumIdeal hA (m+1)) (hA (m+1)) 1,
      deriv_finSumIdeal A hA (m+1) (by omega),
      ←finSumIdeal_succ (fun i _=>isCoherent_derivIdeal (hA i))]

/-- A true positive finite coherent sum retains the SAME tangent stability. -/
theorem finiteSum_tangent_stability (A : ℕ→GermIdeal n X) (hA : ∀i,(A i).IsCoherent)
    {T : GermIdeal n X} (hT : T.IsCoherent) {m : ℕ} (hm : 0<m)
    (hStable : ∀i,i<m → ((derivIdeal (A i)).mul T).Le (A i)) :
    ((derivIdeal (finSumIdeal A m)).mul T).Le (finSumIdeal A m):=by
  rw [deriv_finSumIdeal A hA m hm]
  apply mul_finSum_le _ (fun i=>isCoherent_derivIdeal (hA i)) hT (isCoherent_finSumIdeal hA m) m
  intro i hi
  exact fun x g hg=>fin_term_le A hA hi x g (hStable i hi x g hg)

private theorem power_anti {T : GermIdeal n X} (hT : T.IsCoherent) {a b : ℕ} (hab : a≤b) :
    (idealPow T b).Le (idealPow T a):=by
  obtain ⟨k,hk⟩:=Nat.exists_eq_add_of_le hab
  rw [hk,RestrictLeCalculus.idealPow_add hT a k]
  exact mul_le_left (isCoherent_idealPow hT a)
    (fun {_ _} h=>GermIdeal.IsCoherent.holomorphicAt_mem (isCoherent_idealPow hT k) h)

/-- ALL actual derivatives of the original homogenization are absorbed by
the SAME tangent power. The high-index case is genuine ideal-power absorption. -/
theorem homogenized_derivative_absorption {I : GermIdeal n X} (hI : I.IsCoherent)
    {d : ℕ} (hd : 0<d) (j : ℕ) :
    ((iterDerivIdeal (HomogenizedIdeal.homogenizedIdeal I d) j).mul
      (idealPow (iterDerivIdeal I (d-1)) j)).Le (HomogenizedIdeal.homogenizedIdeal I d):=by
  let H:=HomogenizedIdeal.homogenizedIdeal I d
  let T:=iterDerivIdeal I (d-1)
  have hH : H.IsCoherent:=isCoherent_homogenizedIdeal hI d
  have hT : T.IsCoherent:=isCoherent_iterDerivIdeal hI (d-1)
  have hSource (i : ℕ) (hi : i<d) : ((iterDerivIdeal I i).mul (idealPow T i)).Le H:=
    fin_term_le _ (fun i=>isCoherent_mul (isCoherent_iterDerivIdeal hI i)
      (isCoherent_idealPow hT i)) hi
  by_cases hj : j<d
  · rw [iterDerivIdeal_homogenized_eq_slice hI d j hj]
    change ((finSumIdeal (fun i=>(iterDerivIdeal I (j+i)).mul (idealPow T i)) (d-j)).mul
      (idealPow T j)).Le H
    apply mul_finSum_le _ (fun i=>isCoherent_mul (isCoherent_iterDerivIdeal hI (j+i))
      (isCoherent_idealPow hT i)) (isCoherent_idealPow hT j) hH (d-j)
    intro i hi
    rw [GermIdealTotalTransform.mul_assoc (isCoherent_iterDerivIdeal hI (j+i))
      (isCoherent_idealPow hT i) (isCoherent_idealPow hT j),
      ←RestrictLeCalculus.idealPow_add hT i j,show i+j=j+i from Nat.add_comm i j]
    exact hSource (j+i) (by omega)
  · have hLast : (idealPow T d).Le H:=by
      have hTerm:=hSource (d-1) (by omega)
      have hEq : (iterDerivIdeal I (d-1)).mul (idealPow T (d-1))=idealPow T d:=by
        change T.mul (idealPow T (d-1))=idealPow T d
        rw [RestrictLeCalculus.mul_comm',←idealPow_succ,show (d-1)+1=d by omega]
      rw [hEq] at hTerm
      exact hTerm
    have hPower:=power_anti hT (show d≤j by omega)
    intro x g hg
    have hIn : (idealPow T j).mem x g:=mul_le_right
      (fun {_ _} h=>GermIdeal.IsCoherent.holomorphicAt_mem (isCoherent_iterDerivIdeal hH j) h)
      (isCoherent_idealPow hT j) x g hg
    exact hLast x g (hPower x g hIn)

/-- The ENTIRE original tangent ideal is unchanged by homogenization. -/
theorem homogenized_tangent_ideal {I : GermIdeal n X} (hI : I.IsCoherent)
    {d : ℕ} (hd : 0<d) :
    iterDerivIdeal (HomogenizedIdeal.homogenizedIdeal I d) (d-1)=iterDerivIdeal I (d-1):=by
  rw [iterDerivIdeal_homogenized_eq_slice hI d (d-1) (by omega)]
  unfold homogenizedDerivativeSlice
  rw [show d-(d-1)=1 by omega,
    finSumIdeal_one (isCoherent_mul (isCoherent_iterDerivIdeal hI ((d-1)+0))
      (isCoherent_idealPow (isCoherent_iterDerivIdeal hI (d-1)) 0)),
    Nat.add_zero,idealPow_zero,RestrictLeCalculus.mul_unitIdeal (isCoherent_iterDerivIdeal hI (d-1))]

/-- Homogenization at the SAME positive mark is an ENTIRE ideal idempotent. -/
theorem homogenized_idempotent {I : GermIdeal n X} (hI : I.IsCoherent)
    {d : ℕ} (hd : 0<d) :
    HomogenizedIdeal.homogenizedIdeal (HomogenizedIdeal.homogenizedIdeal I d) d=
      HomogenizedIdeal.homogenizedIdeal I d:=by
  let H:=HomogenizedIdeal.homogenizedIdeal I d
  have hH : H.IsCoherent:=isCoherent_homogenizedIdeal hI d
  have hLower : H.Le (HomogenizedIdeal.homogenizedIdeal H d):=
    HomogenizedIdeal.le_homogenizedIdeal (hol hH) hd
  have hUpper : (HomogenizedIdeal.homogenizedIdeal H d).Le H:=by
    change (finSumIdeal (fun i=>(iterDerivIdeal H i).mul
      (idealPow (iterDerivIdeal H (d-1)) i)) d).Le H
    apply finSumIdeal_le hH
    intro i _hi
    rw [homogenized_tangent_ideal hI hd]
    exact homogenized_derivative_absorption hI hd i
  exact GermIdeal.ext (funext fun x=>funext fun g=>propext ⟨hUpper x g,hLower x g⟩)

/-- The ORIGINAL entire coefficient-homogenized ideal is stable under the
SAME original tangent, with all literal compression exponents retained. -/
theorem coefficient_homogenized_tangent_stability {I : GermIdeal n X} (hI : I.IsCoherent)
    {d : ℕ} (hd : 0<d) :
    let B:=finSumIdeal (fun i=>idealPow
      (iterDerivIdeal (HomogenizedIdeal.homogenizedIdeal I d) i)
      (sumExp (fun j=>d-j) d i)) d
    ((derivIdeal B).mul (iterDerivIdeal I (d-1))).Le B:=by
  let H:=HomogenizedIdeal.homogenizedIdeal I d
  let T:=iterDerivIdeal I (d-1)
  have hH : H.IsCoherent:=isCoherent_homogenizedIdeal hI d
  have hT : T.IsCoherent:=isCoherent_iterDerivIdeal hI (d-1)
  have hStable : ((derivIdeal H).mul T).Le H:=by
    have h:=homogenized_derivative_absorption hI hd 1
    change ((derivIdeal H).mul (idealPow T 1)).Le H at h
    rw [idealPow_succ,idealPow_zero,BlowupControlledTransform.unitIdeal_mul hT] at h
    exact h
  apply finiteSum_tangent_stability _ (fun i=>isCoherent_idealPow (isCoherent_iterDerivIdeal hH i) _)
    hT hd
  intro i _hi
  exact power_tangent_stability (isCoherent_iterDerivIdeal hH i) hT
    (iterDeriv_tangent_stability hH hT hStable i) _

end
end Hironaka.HironakaActualHomogenizedTangentStability
