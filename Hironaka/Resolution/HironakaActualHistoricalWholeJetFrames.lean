import Hironaka.Resolution.HironakaActualHistoricalPrescribedIteration
import Hironaka.Resolution.HironakaActualInheritedNeighborhoodStandardJets
import Hironaka.Resolution.HironakaActualCauchyFilteredNeumannDivision

/-! Whole actual historical jet columns on the genuine HS stratum.
The current translated members need not have the original monic heads. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualHistoricalWholeJetFrames
noncomputable section
open HolGerm HironakaHolomorphicPointJets
 HironakaActualCoefficientPresentationCentrePower HironakaRelativeNormalMonomialBasis
 HironakaActualCauchyCoordinateDivision HironakaActualCauchyMonomialDivision
 HironakaActualCauchyTaylorSupport HironakaActualCauchyDiagramPartition
 HironakaActualCauchyEnumeratedPartition HironakaActualCauchyNeumannDivision
 HironakaActualCauchyFilteredNeumannDivision HironakaActualFormalInitialDiagram
 HironakaActualNormalZeroAnalyticSaturation HironakaActualOriginalFormalHSTransfer

variable {n k : ℕ}

/-- The accepted Cauchy partition's earlier-cone exclusion, in index form. -/
theorem avoidsCones_take_iff (w : Fin k → CoordinateWord n) (j : Fin k) (α : Fin n →₀ ℕ) :
    AvoidsCones ((List.ofFn w).take j.val) α ↔
      ∀i : Fin k,i<j → ¬wordExponent (w i)≤α := by
  constructor
  · intro h i hi
    apply h (w i)
    apply List.mem_take_iff_getElem.mpr
    refine ⟨i.val,?_,?_⟩
    · simp only [List.length_ofFn]
      exact Nat.lt_min.mpr ⟨hi,i.isLt⟩
    · simp
  · intro h a ha
    obtain ⟨i,hi,he⟩:=List.mem_take_iff_getElem.mp ha
    have hik : i<k := by
      simp only [List.length_ofFn] at hi
      omega
    let fi : Fin k:=⟨i,hik⟩
    have hew : w fi=a := by simpa only [List.getElem_ofFn] using he
    rw [←hew]
    apply h fi
    change i<j.val
    omega

/-- The exact first-eligible OLD head, rather than a new current division owner. -/
def historicalOwner (w : Fin k → CoordinateWord n) (α : Fin n →₀ ℕ) : Option (Fin k) := by
  classical
  let E:=Finset.univ.filter (fun j=>wordExponent (w j)≤α)
  exact if h : E.Nonempty then some (E.min' h) else none

/-- The same literal supported partition used by actual Neumann quotients. -/
theorem historicalOwner_eq_some_iff (w : Fin k → CoordinateWord n) (α : Fin n →₀ ℕ) (j : Fin k) :
    historicalOwner w α=some j ↔
      wordExponent (w j)≤α ∧ AvoidsCones ((List.ofFn w).take j.val) α := by
  classical
  let E:=Finset.univ.filter (fun i=>wordExponent (w i)≤α)
  by_cases hE : E.Nonempty
  · have hmem : wordExponent (w (E.min' hE))≤α := (Finset.mem_filter.mp (Finset.min'_mem E hE)).2
    have hmin (i : Fin k) (hi : wordExponent (w i)≤α) : E.min' hE ≤ i :=
      Finset.min'_le E i (Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩)
    have hSome : historicalOwner w α=some (E.min' hE) := by
      unfold historicalOwner
      exact dif_pos hE
    rw [hSome]
    constructor
    · intro h
      have he:=Option.some.inj h
      rw [←he]
      refine ⟨hmem,(avoidsCones_take_iff w _ α).mpr ?_⟩
      intro i hi hwi
      exact (not_le_of_gt hi) (hmin i hwi)
    · rintro ⟨hj,hprev⟩
      have hmj:=hmin j hj
      have hjm : j≤E.min' hE := by
        by_contra h
        exact (avoidsCones_take_iff w j α).mp hprev (E.min' hE) (lt_of_not_ge h) hmem
      exact congrArg some (le_antisymm hmj hjm)
  · have hNone : historicalOwner w α=none := by
      unfold historicalOwner
      exact dif_neg hE
    rw [hNone]
    constructor
    · intro h
      cases h
    · rintro ⟨hj,_⟩
      exact (hE ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ j,hj⟩⟩).elim

/-- Exactly the old complement, including all zero-head and empty-family cases. -/
theorem historicalOwner_eq_none_iff (w : Fin k → CoordinateWord n) (α : Fin n →₀ ℕ) :
    historicalOwner w α=none ↔ AvoidsCones (List.ofFn w) α := by
  classical
  let E:=Finset.univ.filter (fun i=>wordExponent (w i)≤α)
  by_cases hE : E.Nonempty
  · have hSome : historicalOwner w α=some (E.min' hE) := by
      unfold historicalOwner
      exact dif_pos hE
    rw [hSome]
    constructor
    · intro h
      cases h
    · intro h
      exact (h (w (E.min' hE)) (List.mem_ofFn.mpr ⟨E.min' hE,rfl⟩)
        (Finset.mem_filter.mp (Finset.min'_mem E hE)).2).elim
  · have hNone : historicalOwner w α=none := by
      unfold historicalOwner
      exact dif_neg hE
    rw [hNone]
    constructor
    · intro _ a ha hle
      obtain ⟨i,rfl⟩:=List.mem_ofFn.mp ha
      exact hE ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hle⟩⟩
    · intro _
      rfl

/-- The WHOLE historical column indexed by one OLD monomial. -/
def historicalWholeColumn (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ) (α : Fin n →₀ ℕ) : MvPowerSeries (Fin n) ℂ :=
  match historicalOwner w α with
  | none=>MvPowerSeries.monomial α 1
  | some j=>MvPowerSeries.monomial (α-wordExponent (w j)) 1*g j

/-- The entire bounded coefficient vector, not a quotient by the current ideal. -/
def historicalWholeJetMap (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ) (q : ℕ) :
    (normalExponentIndex n q → ℂ) →ₗ[ℂ] (normalExponentIndex n q → ℂ) := by
  classical
  letI:=normalExponentFintype n q
  exact {
    toFun:=fun c α=>∑β,c β*MvPowerSeries.coeff α.val (historicalWholeColumn w g β.val)
    map_add':=by
      intro c d
      funext α
      simp only [Pi.add_apply,add_mul,Finset.sum_add_distrib]
    map_smul':=by
      intro r c
      funext α
      simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply,mul_assoc,Finset.mul_sum] }


/-- Unperturbed supported quotient extraction on the whole formal series. -/
def historicalMonomialQuotient (w : Fin k → CoordinateWord n) (j : Fin k) :
    MvPowerSeries (Fin n) ℂ →ₗ[ℂ] MvPowerSeries (Fin n) ℂ := by
  classical
  exact {
    toFun:=fun F β=>if historicalOwner w (β+wordExponent (w j))=some j then
      MvPowerSeries.coeff (β+wordExponent (w j)) F else 0
    map_add':=by
      intro F G
      ext β
      change (if historicalOwner w (β+wordExponent (w j))=some j then
        MvPowerSeries.coeff (β+wordExponent (w j)) (F+G) else 0)=
        (if historicalOwner w (β+wordExponent (w j))=some j then
          MvPowerSeries.coeff (β+wordExponent (w j)) F else 0)+
        (if historicalOwner w (β+wordExponent (w j))=some j then
          MvPowerSeries.coeff (β+wordExponent (w j)) G else 0)
      rw [map_add]
      split_ifs <;> simp
    map_smul':=by
      intro c F
      ext β
      change (if historicalOwner w (β+wordExponent (w j))=some j then
        c*MvPowerSeries.coeff (β+wordExponent (w j)) F else 0)=
        c*(if historicalOwner w (β+wordExponent (w j))=some j then
          MvPowerSeries.coeff (β+wordExponent (w j)) F else 0)
      split_ifs <;> simp }

/-- The exact old-complement coefficient extraction. -/
def historicalMonomialRemainder (w : Fin k → CoordinateWord n) :
    MvPowerSeries (Fin n) ℂ →ₗ[ℂ] MvPowerSeries (Fin n) ℂ := by
  classical
  exact {
    toFun:=fun F β=>if historicalOwner w β=none then MvPowerSeries.coeff β F else 0
    map_add':=by
      intro F G
      ext β
      change (if historicalOwner w β=none then MvPowerSeries.coeff β (F+G) else 0)=
        (if historicalOwner w β=none then MvPowerSeries.coeff β F else 0)+
        (if historicalOwner w β=none then MvPowerSeries.coeff β G else 0)
      rw [map_add]
      split_ifs <;> simp
    map_smul':=by
      intro c F
      ext β
      change (if historicalOwner w β=none then c*MvPowerSeries.coeff β F else 0)=
        c*(if historicalOwner w β=none then MvPowerSeries.coeff β F else 0)
      split_ifs <;> simp }

private theorem coeff_owned_product (w : Fin k → CoordinateWord n)
    (Q : Fin k → MvPowerSeries (Fin n) ℂ)
    (hQ : ∀j β,historicalOwner w (β+wordExponent (w j))≠some j → MvPowerSeries.coeff β (Q j)=0)
    (j : Fin k) (α : Fin n →₀ ℕ) :
    MvPowerSeries.coeff α (MvPowerSeries.monomial (wordExponent (w j)) 1*Q j)=
      if historicalOwner w α=some j then MvPowerSeries.coeff (α-wordExponent (w j)) (Q j) else 0 := by
  classical
  rw [MvPowerSeries.coeff_monomial_mul]
  by_cases hH : wordExponent (w j)≤α
  · simp only [if_pos hH,one_mul]
    by_cases ho : historicalOwner w α=some j
    · rw [if_pos ho]
    · rw [if_neg ho]
      apply hQ
      simpa only [tsub_add_cancel_of_le hH] using ho
  · have ho : historicalOwner w α≠some j:=fun h=>hH ((historicalOwner_eq_some_iff w α j).mp h).1
    simp only [if_neg hH,if_neg ho]

/-- Supported quotients and old-complement remainder have the exact
original monomial coordinates; no translated head assumption appears. -/
theorem historical_supported_coordinates (w : Fin k → CoordinateWord n)
    (Q : Fin k → MvPowerSeries (Fin n) ℂ) (R : MvPowerSeries (Fin n) ℂ)
    (hQ : ∀j β,historicalOwner w (β+wordExponent (w j))≠some j → MvPowerSeries.coeff β (Q j)=0)
    (hR : ∀β,historicalOwner w β≠none → MvPowerSeries.coeff β R=0)
    (α : Fin n →₀ ℕ) :
    MvPowerSeries.coeff α ((∑j,MvPowerSeries.monomial (wordExponent (w j)) 1*Q j)+R)=
      match historicalOwner w α with
      | none=>MvPowerSeries.coeff α R
      | some j=>MvPowerSeries.coeff (α-wordExponent (w j)) (Q j) := by
  classical
  rw [map_add,map_sum]
  simp only [coeff_owned_product w Q hQ]
  cases ho : historicalOwner w α with
  | none=>simp only [reduceCtorEq,if_false,Finset.sum_const_zero,zero_add]
  | some j=>
      have hr:=hR α (by rw [ho]; exact Option.some_ne_none j)
      simp only [Option.some.injEq,hr,add_zero]
      simp

/-- Exact recovery of every old supported quotient. -/
theorem historical_supported_quotient_recovery (w : Fin k → CoordinateWord n)
    (Q : Fin k → MvPowerSeries (Fin n) ℂ) (R : MvPowerSeries (Fin n) ℂ)
    (hQ : ∀j β,historicalOwner w (β+wordExponent (w j))≠some j → MvPowerSeries.coeff β (Q j)=0)
    (hR : ∀β,historicalOwner w β≠none → MvPowerSeries.coeff β R=0)
    (j : Fin k) :
    historicalMonomialQuotient w j ((∑i,MvPowerSeries.monomial (wordExponent (w i)) 1*Q i)+R)=Q j := by
  classical
  ext β
  change (if historicalOwner w (β+wordExponent (w j))=some j then
    MvPowerSeries.coeff (β+wordExponent (w j)) ((∑i,MvPowerSeries.monomial (wordExponent (w i)) 1*Q i)+R)
    else 0)=MvPowerSeries.coeff β (Q j)
  by_cases ho : historicalOwner w (β+wordExponent (w j))=some j
  · rw [if_pos ho,historical_supported_coordinates w Q R hQ hR,ho]
    simp only [add_tsub_cancel_right]
  · rw [if_neg ho,hQ j β ho]

/-- Exact recovery of the same old-complement remainder. -/
theorem historical_supported_remainder_recovery (w : Fin k → CoordinateWord n)
    (Q : Fin k → MvPowerSeries (Fin n) ℂ) (R : MvPowerSeries (Fin n) ℂ)
    (hQ : ∀j β,historicalOwner w (β+wordExponent (w j))≠some j → MvPowerSeries.coeff β (Q j)=0)
    (hR : ∀β,historicalOwner w β≠none → MvPowerSeries.coeff β R=0) :
    historicalMonomialRemainder w ((∑i,MvPowerSeries.monomial (wordExponent (w i)) 1*Q i)+R)=R := by
  classical
  ext β
  change (if historicalOwner w β=none then
    MvPowerSeries.coeff β ((∑i,MvPowerSeries.monomial (wordExponent (w i)) 1*Q i)+R)
    else 0)=MvPowerSeries.coeff β R
  by_cases ho : historicalOwner w β=none
  · rw [if_pos ho,historical_supported_coordinates w Q R hQ hR,ho]
  · rw [if_neg ho,hR β ho]

/-- Replace only the original monomial heads by the SAME actual current
members, retaining the old supported partition on every coefficient. -/
def historicalReassemble (w : Fin k → CoordinateWord n) (g : Fin k → MvPowerSeries (Fin n) ℂ) :
    MvPowerSeries (Fin n) ℂ →ₗ[ℂ] MvPowerSeries (Fin n) ℂ := by
  classical
  exact {
    toFun:=fun F=>(∑j,(historicalMonomialQuotient w j F)*g j)+historicalMonomialRemainder w F
    map_add':=by
      intro F G
      simp only [map_add,add_mul,Finset.sum_add_distrib]
      abel
    map_smul':=by
      intro c F
      simp only [map_smul,RingHom.id_apply,smul_mul_assoc,Finset.smul_sum,smul_add] }

/-- Actual supported division yields a preimage under the same whole
historical column operator; these division data are later constructed. -/
theorem historicalReassemble_of_supported_division (w : Fin k → CoordinateWord n)
    (g Q : Fin k → MvPowerSeries (Fin n) ℂ) (R : MvPowerSeries (Fin n) ℂ)
    (hQ : ∀j β,historicalOwner w (β+wordExponent (w j))≠some j → MvPowerSeries.coeff β (Q j)=0)
    (hR : ∀β,historicalOwner w β≠none → MvPowerSeries.coeff β R=0) :
    historicalReassemble w g ((∑j,MvPowerSeries.monomial (wordExponent (w j)) 1*Q j)+R)=
      (∑j,Q j*g j)+R := by
  change (∑j,historicalMonomialQuotient w j _*g j)+historicalMonomialRemainder w _=_
  simp only [historical_supported_quotient_recovery w Q R hQ hR,
    historical_supported_remainder_recovery w Q R hQ hR]


/-- Genuine coefficient degree, with no finite-degree truncation assumption. -/
private theorem historical_degree_add (a b : Fin n →₀ ℕ) :
    normalExponentDegree (a+b)=normalExponentDegree a+normalExponentDegree b := by
  simp only [normalExponentDegree,Finsupp.add_apply,Finset.sum_add_distrib]

/-- The unperturbed quotient has exactly the shifted marked filtration. -/
theorem historicalMonomialQuotient_mem_power (w : Fin k → CoordinateWord n) (j : Fin k)
    {F : MvPowerSeries (Fin n) ℂ} {q : ℕ} (hF : F∈genuineFormalVariables n^q) :
    historicalMonomialQuotient w j F∈genuineFormalVariables n^(q-normalExponentDegree (wordExponent (w j))) := by
  classical
  apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n _ _).mpr
  intro β hβ
  change (if historicalOwner w (β+wordExponent (w j))=some j then
    MvPowerSeries.coeff (β+wordExponent (w j)) F else 0)=0
  split_ifs
  · apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n q F).mp hF
    rw [historical_degree_add]
    omega
  · rfl

/-- Old-complement extraction retains every actual order. -/
theorem historicalMonomialRemainder_mem_power (w : Fin k → CoordinateWord n)
    {F : MvPowerSeries (Fin n) ℂ} {q : ℕ} (hF : F∈genuineFormalVariables n^q) :
    historicalMonomialRemainder w F∈genuineFormalVariables n^q := by
  classical
  apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n q _).mpr
  intro β hβ
  change (if historicalOwner w β=none then MvPowerSeries.coeff β F else 0)=0
  split_ifs
  · exact (mem_genuineFormalVariables_pow_iff_coefficients_zero n q F).mp hF β hβ
  · rfl

/-- SAME current marked orders make the historical operator descend to
EVERY whole jet quotient, including q≤the individual mark. -/
theorem historicalReassemble_mem_power (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hmarked : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    {F : MvPowerSeries (Fin n) ℂ} {q : ℕ} (hF : F∈genuineFormalVariables n^q) :
    historicalReassemble w g F∈genuineFormalVariables n^q := by
  change (∑j,historicalMonomialQuotient w j F*g j)+historicalMonomialRemainder w F∈_
  apply Ideal.add_mem
  · apply Ideal.sum_mem
    intro j _
    have hm:=Ideal.mul_mem_mul (historicalMonomialQuotient_mem_power w j hF) (hmarked j)
    rw [←pow_add] at hm
    exact (Ideal.pow_le_pow_right (by omega)) hm
  · exact historicalMonomialRemainder_mem_power w hF


/-- Whole coefficient jets, before any quotient by the geometric ideal. -/
def boundedCoefficients (q : ℕ) :
    MvPowerSeries (Fin n) ℂ →ₗ[ℂ] (normalExponentIndex n q → ℂ) :=
  LinearMap.pi fun α=>MvPowerSeries.coeff α.val

/-- The literal finite coefficient vector has its genuine polynomial lift. -/
def boundedSeries (q : ℕ) :
    (normalExponentIndex n q → ℂ) →ₗ[ℂ] MvPowerSeries (Fin n) ℂ := by
  classical
  exact {
    toFun:=fun c α=>if hα : normalExponentDegree α<q then c ⟨α,hα⟩ else 0
    map_add':=by
      intro c d
      ext α
      change (if hα : normalExponentDegree α<q then (c+d) ⟨α,hα⟩ else 0)=
        (if hα : normalExponentDegree α<q then c ⟨α,hα⟩ else 0)+
        (if hα : normalExponentDegree α<q then d ⟨α,hα⟩ else 0)
      split_ifs <;> simp
    map_smul':=by
      intro r c
      ext α
      change (if hα : normalExponentDegree α<q then (r*c ⟨α,hα⟩) else 0)=
        r*(if hα : normalExponentDegree α<q then c ⟨α,hα⟩ else 0)
      split_ifs <;> simp }

theorem boundedCoefficients_boundedSeries (q : ℕ) (c : normalExponentIndex n q → ℂ) :
    boundedCoefficients q (boundedSeries q c)=c := by
  classical
  funext α
  change (if hα : normalExponentDegree α.val<q then c ⟨α.val,hα⟩ else 0)=c α
  exact dif_pos α.property

/-- All orders, including zero, of the literal coefficient truncation. -/
theorem sub_boundedSeries_mem_power (q : ℕ) (F : MvPowerSeries (Fin n) ℂ) :
    F-boundedSeries q (boundedCoefficients q F)∈genuineFormalVariables n^q := by
  classical
  apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n q _).mpr
  intro α hα
  change MvPowerSeries.coeff α F-
    (if h : normalExponentDegree α<q then MvPowerSeries.coeff α F else 0)=0
  rw [dif_pos hα,sub_self]

theorem boundedCoefficients_eq_iff (q : ℕ) (F G : MvPowerSeries (Fin n) ℂ) :
    boundedCoefficients q F=boundedCoefficients q G ↔ F-G∈genuineFormalVariables n^q := by
  rw [mem_genuineFormalVariables_pow_iff_coefficients_zero]
  constructor
  · intro h α hα
    have he:=congrFun h (⟨α,hα⟩ : normalExponentIndex n q)
    exact sub_eq_zero.mpr he
  · intro h
    funext α
    exact sub_eq_zero.mp (h α.val α.property)

/-- The SAME historical operator on the WHOLE actual bounded coefficient jet. -/
def historicalWholeJetOperator (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ) (q : ℕ) :
    (normalExponentIndex n q → ℂ) →ₗ[ℂ] (normalExponentIndex n q → ℂ) :=
  (boundedCoefficients q).comp ((historicalReassemble w g).comp (boundedSeries q))

/-- Genuine supported division of arbitrary polynomial numerators; this
algebraic condition is subsequently PRODUCED by actual Neumann division. -/
def HistoricalPolynomialDivision (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ) : Prop :=
  ∀(q : ℕ)(v : normalExponentIndex n q → ℂ),
    ∃(Q : Fin k → MvPowerSeries (Fin n) ℂ)(R : MvPowerSeries (Fin n) ℂ),
      boundedSeries q v=(∑j,Q j*g j)+R ∧
      (∀j β,historicalOwner w (β+wordExponent (w j))≠some j → MvPowerSeries.coeff β (Q j)=0) ∧
      (∀β,historicalOwner w β≠none → MvPowerSeries.coeff β R=0)

/-- Supported analytic division and actual marked orders produce spanning
of the WHOLE ambient jet. No rank or current-diagram premise is supplied. -/
theorem historicalWholeJetOperator_surjective (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hmarked : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hDivision : HistoricalPolynomialDivision w g) (q : ℕ) :
    Function.Surjective (historicalWholeJetOperator w g q) := by
  classical
  intro v
  obtain ⟨Q,R,hEq,hQ,hR⟩:=hDivision q v
  let F:=(∑j,MvPowerSeries.monomial (wordExponent (w j)) 1*Q j)+R
  have hRF : historicalReassemble w g F=boundedSeries q v :=
    (historicalReassemble_of_supported_division w g Q R hQ hR).trans hEq.symm
  let c:=boundedCoefficients q F
  have hm:=historicalReassemble_mem_power w g hmarked (sub_boundedSeries_mem_power q F)
  rw [map_sub] at hm
  have he:=(boundedCoefficients_eq_iff q _ _).mpr hm
  rw [hRF,boundedCoefficients_boundedSeries] at he
  exact ⟨c,he.symm⟩

/-- SAME monomial index on domain and codomain gives genuine bijectivity,
with no caller-supplied dimension or determinant certificate. -/
theorem historicalWholeJetOperator_bijective (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hmarked : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hDivision : HistoricalPolynomialDivision w g) (q : ℕ) :
    Function.Bijective (historicalWholeJetOperator w g q) := by
  classical
  let :=normalExponentFintype n q
  have hs:=historicalWholeJetOperator_surjective w g hmarked hDivision q
  exact ⟨(LinearMap.injective_iff_surjective).mpr hs,hs⟩


/-- The coefficient lift is the literal bounded polynomial, not an
unspecified representative of its jet class. -/
theorem boundedSeries_eq_sum (q : ℕ) (v : normalExponentIndex n q → ℂ) :
    boundedSeries q v=by
      classical
      let :=normalExponentFintype n q
      exact ∑α,MvPowerSeries.monomial α.val (v α) := by
  classical
  let :=normalExponentFintype n q
  ext α
  change (if hα : normalExponentDegree α<q then v ⟨α,hα⟩ else 0)=_
  rw [map_sum]
  by_cases hα : normalExponentDegree α<q
  · rw [dif_pos hα]
    let a : normalExponentIndex n q:=⟨α,hα⟩
    symm
    rw [Finset.sum_eq_single a]
    · exact MvPowerSeries.coeff_monomial_same α (v a)
    · intro β _ hβ
      have hne : β.val≠α:=fun h=>hβ (Subtype.ext h)
      rw [MvPowerSeries.coeff_monomial,if_neg (Ne.symm hne)]
    · intro ha
      exact (ha (Finset.mem_univ a)).elim
  · rw [dif_neg hα]
    symm
    apply Finset.sum_eq_zero
    intro β _
    have hne : β.val≠α:=fun h=>hα (h ▸ β.property)
    rw [MvPowerSeries.coeff_monomial,if_neg (Ne.symm hne)]

private theorem modelTaylor_sum {ι : Type} [Fintype ι] {r : ℝ} (hr : 0<r)
    (f : ι → CoordinateSpace n → ℂ) (hf : ∀i,DifferentiableOn ℂ (f i) (Metric.ball 0 r)) :
    actualUnshiftedTaylorAlgHom n
      (modelGerm hr (DifferentiableOn.fun_sum fun i (_hi : i∈Finset.univ)=>hf i))=
      ∑i,actualUnshiftedTaylorAlgHom n (modelGerm hr (hf i)) := by
  change actualUnshiftedTaylorAlgHom n (HolGerm.mk (fun z : ComplexModel n=>∑i,modelFunction (f i) z) _)=_
  rw [HolGerm.mk_sum Finset.univ _ (fun i=>modelFunction_holAt hr (hf i)),map_sum]
  rfl

private theorem modelTaylor_mul {r : ℝ} (hr : 0<r)
    {f g : CoordinateSpace n → ℂ} (hf : DifferentiableOn ℂ f (Metric.ball 0 r))
    (hg : DifferentiableOn ℂ g (Metric.ball 0 r)) :
    actualUnshiftedTaylorAlgHom n (modelGerm hr (hf.mul hg))=
      actualUnshiftedTaylorAlgHom n (modelGerm hr hf)*actualUnshiftedTaylorAlgHom n (modelGerm hr hg) := by
  change actualUnshiftedTaylorAlgHom n
    (HolGerm.mk (fun z : ComplexModel n=>modelFunction f z*modelFunction g z) _)=_
  rw [HolGerm.mk_mul _ _ (modelFunction_holAt hr hf) (modelFunction_holAt hr hg),map_mul]
  rfl

private theorem modelTaylor_add {r : ℝ} (hr : 0<r)
    {f g : CoordinateSpace n → ℂ} (hf : DifferentiableOn ℂ f (Metric.ball 0 r))
    (hg : DifferentiableOn ℂ g (Metric.ball 0 r)) :
    actualUnshiftedTaylorAlgHom n (modelGerm hr (hf.add hg))=
      actualUnshiftedTaylorAlgHom n (modelGerm hr hf)+actualUnshiftedTaylorAlgHom n (modelGerm hr hg) := by
  change actualUnshiftedTaylorAlgHom n
    (HolGerm.mk (fun z : ComplexModel n=>modelFunction f z+modelFunction g z) _)=_
  rw [HolGerm.mk_add _ _ (modelFunction_holAt hr hf) (modelFunction_holAt hr hg),map_add]
  rfl

private theorem modelTaylor_scaled_word {r : ℝ} (hr : 0<r) (c : ℂ) (w : CoordinateWord n) :
    actualUnshiftedTaylorAlgHom n (modelGerm hr ((wordMonomial_differentiable w).differentiableOn.const_mul c))=
      MvPowerSeries.monomial (wordExponent w) c := by
  have hG : modelGerm hr ((wordMonomial_differentiable w).differentiableOn.const_mul c)=
      HolGerm.constHom c*modelGerm hr (wordMonomial_differentiable w).differentiableOn := by
    change HolGerm.mk (fun z : ComplexModel n=>c*modelFunction (wordMonomial w) z) _=_
    have hc : ∀ᶠz : ComplexModel n in 𝓝 0,DifferentiableAt ℂ (fun _ : ComplexModel n=>c) z:=
      Eventually.of_forall fun _=>differentiableAt_const c
    have hm:=HolGerm.mk_mul (fun _ : ComplexModel n=>c) (modelFunction (wordMonomial w)) hc
      (modelFunction_holAt hr (wordMonomial_differentiable w).differentiableOn)
    simpa only [modelGerm,HolGerm.mk_const] using hm
  have hc : actualUnshiftedTaylorAlgHom n (HolGerm.constHom c)=MvPowerSeries.C c := by
    change (actualUnshiftedTaylorAlgHom n) (algebraMap ℂ (HolGerm (ComplexModel n)) c)=algebraMap ℂ _ c
    exact AlgHom.commutes _ c
  rw [hG,map_mul,hc,actualTaylor_wordMonomial]
  ext α
  rw [MvPowerSeries.coeff_C_mul]
  simp only [MvPowerSeries.coeff_monomial]
  split_ifs <;> simp

private theorem modelTaylor_eqOn {r : ℝ} (hr : 0<r)
    {f g : CoordinateSpace n → ℂ} (hf : DifferentiableOn ℂ f (Metric.ball 0 r))
    (hg : DifferentiableOn ℂ g (Metric.ball 0 r))
    (he : EqOn f g (Metric.ball 0 r)) :
    actualUnshiftedTaylorAlgHom n (modelGerm hr hf)=actualUnshiftedTaylorAlgHom n (modelGerm hr hg) := by
  apply congrArg (actualUnshiftedTaylorAlgHom n)
  apply HolGerm.mk_eq_mk_iff.mpr
  let e:=EuclideanSpace.equiv (𝕜:=ℂ) (ι:=Fin n)
  have ht : Tendsto e (𝓝 (0 : ComplexModel n)) (𝓝 (0 : CoordinateSpace n)) := by
    simpa only [map_zero] using e.continuous.tendsto (0 : ComplexModel n)
  filter_upwards [ht.eventually (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))] with z hz
  exact he hz

/-- Concrete Neumann division PRODUCES the entire supported polynomial
history used by the algebraic whole-jet theorem. -/
theorem historicalPolynomialDivision_of_neumann {r : ℝ} (hr : 0<r)
    (w : Fin k → CoordinateWord n) (D : ConcreteNeumannData r w)
    (H : Fin k → CoordinateSpace n → ℂ)
    (hH : ∀j,DifferentiableOn ℂ (H j) (Metric.ball 0 r))
    (hHb : ∀j,∀z∈Metric.ball (0 : CoordinateSpace n) r,‖H j z‖≤D.epsilon) :
    HistoricalPolynomialDivision w (fun j=>actualUnshiftedTaylorAlgHom n
      (modelGerm hr ((wordMonomial_differentiable (w j)).differentiableOn.add (hH j)))) := by
  classical
  intro q v
  let :=normalExponentFintype n q
  let f : CoordinateSpace n → ℂ:=fun z=>∑α,v α*wordMonomial (wordOfExponent α.val) z
  have hterm (α : normalExponentIndex n q) : DifferentiableOn ℂ
      (fun z=>v α*wordMonomial (wordOfExponent α.val) z) (Metric.ball 0 r) :=
    (wordMonomial_differentiable (wordOfExponent α.val)).differentiableOn.const_mul (v α)
  have hfd : DifferentiableOn ℂ f (Metric.ball 0 r):=DifferentiableOn.fun_sum fun α _=>hterm α
  let M:=∑α,‖v α‖*r^wordDegree (wordOfExponent α.val)
  have hM : 0≤M:=Finset.sum_nonneg fun α _=>mul_nonneg (norm_nonneg _) (pow_nonneg hr.le _)
  have hfb : ∀z∈Metric.ball (0 : CoordinateSpace n) r,‖f z‖≤M := by
    intro z hz
    calc
      ‖f z‖≤∑α,‖v α*wordMonomial (wordOfExponent α.val) z‖:=norm_sum_le _ _
      _≤M:=Finset.sum_le_sum fun α _=>by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (wordMonomial_norm_le _ hr hz) (norm_nonneg _)
  have hd:=neumannSums_differentiableOn hr D hH hHb hM hfd hfb
  have hs:=neumannSums_whole_support hr D hH hHb hM hfd hfb
  let Q:=fun j=>actualUnshiftedTaylorAlgHom n (modelGerm hr (hd.1 j))
  let R:=actualUnshiftedTaylorAlgHom n (modelGerm hr hd.2)
  refine ⟨Q,R,?_,?_,?_⟩
  · have hfTaylor : actualUnshiftedTaylorAlgHom n (modelGerm hr hfd)=boundedSeries q v := by
      rw [modelTaylor_sum hr (fun α z=>v α*wordMonomial (wordOfExponent α.val) z) hterm]
      simp only [modelTaylor_scaled_word,wordExponent_wordOfExponent]
      exact (boundedSeries_eq_sum q v).symm
    rw [←hfTaylor]
    let G:=fun j z=>wordMonomial (w j) z+H j z
    have hg (j) : DifferentiableOn ℂ (G j) (Metric.ball 0 r):=
      (wordMonomial_differentiable (w j)).differentiableOn.add (hH j)
    have hsum : DifferentiableOn ℂ (fun z=>∑j,neumannQuotientSum r w H f j z*G j z) (Metric.ball 0 r):=
      DifferentiableOn.fun_sum fun j _=>(hd.1 j).mul (hg j)
    have hEq:=modelTaylor_eqOn hr hfd (hsum.add hd.2)
      (fun z hz=>neumannSums_division hr D hH hHb hM hfd hfb hz)
    rw [modelTaylor_add hr hsum hd.2,
      modelTaylor_sum hr _ (fun j=>(hd.1 j).mul (hg j))] at hEq
    have hProducts (j : Fin k) : actualUnshiftedTaylorAlgHom n
        (modelGerm hr ((hd.1 j).mul (hg j)))=Q j*actualUnshiftedTaylorAlgHom n (modelGerm hr (hg j)) :=
      modelTaylor_mul hr (hd.1 j) (hg j)
    exact hEq.trans (congrArg (fun A=>A+R) (Finset.sum_congr rfl (fun j _=>hProducts j)))
  · intro j β ho
    apply hs.1 j β
    intro hprev
    apply ho
    apply (historicalOwner_eq_some_iff w _ j).mpr
    exact ⟨le_add_self,hprev⟩
  · intro β ho
    apply hs.2 β
    intro hav
    exact ho ((historicalOwner_eq_none_iff w β).mpr hav)

/-- Actual holomorphic small tails plus the SAME genuine individual marks
produce every whole historical jet basis, with no supplied division/rank law. -/
theorem historicalWholeJetOperator_bijective_of_neumann {r : ℝ} (hr : 0<r)
    (w : Fin k → CoordinateWord n) (D : ConcreteNeumannData r w)
    (H : Fin k → CoordinateSpace n → ℂ)
    (hH : ∀j,DifferentiableOn ℂ (H j) (Metric.ball 0 r))
    (hHb : ∀j,∀z∈Metric.ball (0 : CoordinateSpace n) r,‖H j z‖≤D.epsilon)
    (hmarked : ∀j,actualUnshiftedTaylorAlgHom n
      (modelGerm hr ((wordMonomial_differentiable (w j)).differentiableOn.add (hH j)))∈
      genuineFormalVariables n^normalExponentDegree (wordExponent (w j))) (q : ℕ) :
    Function.Bijective (historicalWholeJetOperator w (fun j=>actualUnshiftedTaylorAlgHom n
      (modelGerm hr ((wordMonomial_differentiable (w j)).differentiableOn.add (hH j)))) q) :=
  historicalWholeJetOperator_bijective w _ hmarked (historicalPolynomialDivision_of_neumann hr w D H hH hHb) q


/-- Old monomial coordinates use exactly their accepted first owner. -/
theorem historicalMonomialQuotient_monomial (w : Fin k → CoordinateWord n) (j : Fin k)
    (α : Fin n →₀ ℕ) (c : ℂ) :
    historicalMonomialQuotient w j (MvPowerSeries.monomial α c)=
      if historicalOwner w α=some j then MvPowerSeries.monomial (α-wordExponent (w j)) c else 0 := by
  classical
  by_cases ho : historicalOwner w α=some j
  · rw [if_pos ho]
    have hHead:wordExponent (w j)≤α:=(historicalOwner_eq_some_iff w α j).mp ho |>.1
    ext β
    change (if historicalOwner w (β+wordExponent (w j))=some j then
      MvPowerSeries.coeff (β+wordExponent (w j)) (MvPowerSeries.monomial α c) else 0)=
      MvPowerSeries.coeff β (MvPowerSeries.monomial (α-wordExponent (w j)) c)
    rw [MvPowerSeries.coeff_monomial,MvPowerSeries.coeff_monomial]
    have heq : β+wordExponent (w j)=α ↔ β=α-wordExponent (w j) := by
      constructor
      · intro h
        rw [←h,add_tsub_cancel_right]
      · intro h
        rw [h,tsub_add_cancel_of_le hHead]
    by_cases he : β+wordExponent (w j)=α
    · have hb:=heq.mp he
      rw [he,if_pos ho,if_pos rfl,if_pos hb]
    · have hb : β≠α-wordExponent (w j):=fun h=>he (heq.mpr h)
      rw [if_neg hb,if_neg he]
      split_ifs <;> rfl
  · rw [if_neg ho]
    ext β
    change (if historicalOwner w (β+wordExponent (w j))=some j then
      MvPowerSeries.coeff (β+wordExponent (w j)) (MvPowerSeries.monomial α c) else 0)=0
    rw [MvPowerSeries.coeff_monomial]
    by_cases he : β+wordExponent (w j)=α
    · rw [he,if_neg ho]
    · rw [if_neg he]
      split_ifs <;> rfl

theorem historicalMonomialRemainder_monomial (w : Fin k → CoordinateWord n)
    (α : Fin n →₀ ℕ) (c : ℂ) :
    historicalMonomialRemainder w (MvPowerSeries.monomial α c)=
      if historicalOwner w α=none then MvPowerSeries.monomial α c else 0 := by
  classical
  by_cases ho : historicalOwner w α=none
  · rw [if_pos ho]
    ext β
    change (if historicalOwner w β=none then MvPowerSeries.coeff β (MvPowerSeries.monomial α c) else 0)=
      MvPowerSeries.coeff β (MvPowerSeries.monomial α c)
    rw [MvPowerSeries.coeff_monomial]
    by_cases he : β=α
    · rw [he,if_pos ho]
    · rw [if_neg he]
      split_ifs <;> rfl
  · rw [if_neg ho]
    ext β
    change (if historicalOwner w β=none then MvPowerSeries.coeff β (MvPowerSeries.monomial α c) else 0)=0
    rw [MvPowerSeries.coeff_monomial]
    by_cases he : β=α
    · rw [he,if_neg ho]
    · rw [if_neg he]
      split_ifs <;> rfl

/-- The historical operator's basis vectors are the literal columns. -/
theorem historicalReassemble_monomial (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ) (α : Fin n →₀ ℕ) :
    historicalReassemble w g (MvPowerSeries.monomial α 1)=historicalWholeColumn w g α := by
  classical
  change (∑j,historicalMonomialQuotient w j (MvPowerSeries.monomial α 1)*g j)+
    historicalMonomialRemainder w (MvPowerSeries.monomial α 1)=_
  simp only [historicalMonomialQuotient_monomial,historicalMonomialRemainder_monomial]
  cases ho : historicalOwner w α with
  | none=>simp only [ho,reduceCtorEq,if_false,zero_mul,Finset.sum_const_zero,if_true,
      zero_add,historicalWholeColumn]
  | some j=>simp [ho,historicalWholeColumn,ite_mul]

private theorem monomial_scalar (α : Fin n →₀ ℕ) (c : ℂ) :
    (MvPowerSeries.monomial α c : MvPowerSeries (Fin n) ℂ)=c • MvPowerSeries.monomial α 1 := by
  ext β
  rw [map_smul]
  simp only [MvPowerSeries.coeff_monomial,smul_eq_mul]
  split_ifs <;> simp

/-- The entire constructed jet operator is precisely the displayed
historical-column matrix, with its original coefficient indexing. -/
theorem historicalWholeJetMap_eq_operator (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ) (q : ℕ) :
    historicalWholeJetMap w g q=historicalWholeJetOperator w g q := by
  classical
  let :=normalExponentFintype n q
  apply LinearMap.ext
  intro c
  funext α
  change (∑β,c β*MvPowerSeries.coeff α.val (historicalWholeColumn w g β.val))=
    MvPowerSeries.coeff α.val (historicalReassemble w g (boundedSeries q c))
  rw [boundedSeries_eq_sum,map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro β _
  rw [monomial_scalar β.val (c β),map_smul,historicalReassemble_monomial,map_smul]
  rfl

/-- The literal SAME historical columns, with original individual marks,
form the whole ambient jet basis at every order. -/
theorem historicalWholeJetMap_bijective_of_neumann {r : ℝ} (hr : 0<r)
    (w : Fin k → CoordinateWord n) (D : ConcreteNeumannData r w)
    (H : Fin k → CoordinateSpace n → ℂ)
    (hH : ∀j,DifferentiableOn ℂ (H j) (Metric.ball 0 r))
    (hHb : ∀j,∀z∈Metric.ball (0 : CoordinateSpace n) r,‖H j z‖≤D.epsilon)
    (hmarked : ∀j,actualUnshiftedTaylorAlgHom n
      (modelGerm hr ((wordMonomial_differentiable (w j)).differentiableOn.add (hH j)))∈
      genuineFormalVariables n^normalExponentDegree (wordExponent (w j))) (q : ℕ) :
    Function.Bijective (historicalWholeJetMap w (fun j=>actualUnshiftedTaylorAlgHom n
      (modelGerm hr ((wordMonomial_differentiable (w j)).differentiableOn.add (hH j)))) q) := by
  rw [historicalWholeJetMap_eq_operator]
  exact historicalWholeJetOperator_bijective_of_neumann hr w D H hH hHb hmarked q


open HironakaActualInheritedSmallTails HironakaActualOriginalScaledAnalyticDivision
 HironakaActualInheritedSourceCauchyRemainder HironakaActualInheritedUniformTranslatedTails
 HironakaActualInheritedTranslatedAnalyticDivision HironakaActualInheritedNeighborhoodStandardJets
 HironakaActualDiagonalTaylor HironakaActualWeightedScaling HironakaActualFiniteDegLexWeights
 HironakaActualWeightedVertexSmallTails HironakaActualTranslatedCauchyOwnerSupport
 HironakaActualGeometricCurrentNeighborhoodHS HironakaHolomorphicJetRankLoci
 HironakaHolomorphicJetChartInvariance OkaRelationSheaf HironakaActualRelativeNormalJetDivision

/-- Genuine diagonal composition preserves all original point powers. -/
theorem diagonal_pullback_mem_maximal_power (c : Fin n → ℂ)
    {F : HolGerm (ComplexModel n)} {q : ℕ}
    (hF : F∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^q) :
    actualDiagonalPullback c F∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^q := by
  apply (mem_analytic_ideal_iff_actualUnshifted_extension n _ _).mpr
  rw [map_actualUnshifted_maximal_pow]
  apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n q _).mpr
  have hf:=Ideal.mem_map_of_mem (actualUnshiftedTaylorAlgHom n).toRingHom hF
  rw [map_actualUnshifted_maximal_pow] at hf
  intro α hα
  have hz : MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom n F)=0:=
    (mem_genuineFormalVariables_pow_iff_coefficients_zero n q _).mp hf α hα
  rw [coeff_actualDiagonalPullback,hz,mul_zero]

private theorem weighted_source_point (W : Fin n → ℕ) (s : ℂ) (z : ComplexModel n) :
    actualWeightedScalingMap W
      (jointPoint n (EuclideanSpace.equiv (𝕜:=ℂ) (ι:=Fin n) z,s))=
      actualDiagonalMap (fun i=>s^W i) z := by
  ext i
  let p : CoordinateSpace n × ℂ:=(EuclideanSpace.equiv (𝕜:=ℂ) (ι:=Fin n) z,s)
  have hp : jointPoint n p (parameterIndex n)=s := by
    change (Fin.addCases (motive:=fun _ : Fin (n+1)=>CoordinateSpace n × ℂ →L[ℂ] ℂ)
      (fun j : Fin n=>(ContinuousLinearMap.proj j).comp (ContinuousLinearMap.fst ℂ (CoordinateSpace n) ℂ))
      (fun _ : Fin 1=>ContinuousLinearMap.snd ℂ (CoordinateSpace n) ℂ) ((0 : Fin 1).natAdd n)) p=s
    rw [Fin.addCases_right]
    rfl
  have hb : jointPoint n p (i.castAdd 1)=z i := by
    change (Fin.addCases (motive:=fun _ : Fin (n+1)=>CoordinateSpace n × ℂ →L[ℂ] ℂ)
      (fun j : Fin n=>(ContinuousLinearMap.proj j).comp (ContinuousLinearMap.fst ℂ (CoordinateSpace n) ℂ))
      (fun _ : Fin 1=>ContinuousLinearMap.snd ℂ (CoordinateSpace n) ℂ) (i.castAdd 1)) p=z i
    rw [Fin.addCases_left]
    rfl
  change jointPoint n p (parameterIndex n)^W i*jointPoint n p (i.castAdd 1)=s^W i*z i
  rw [hp,hb]

section GeometricSource
variable {I : Ideal (HolGerm (ComplexModel n))}
 {G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)}

/-- The actual original point corresponding to one produced translated
Neumann coordinate; the coordinate map is fixed before every jet order. -/
def scaledOriginalPoint (P : ActualInheritedWeightedTailData G) (s : ℂ) (p : CoordinateSpace n) : ComplexModel n :=
  actualDiagonalMap (fun i=>s^(degLexWeight n P.germs.degreeBound i))
    ((EuclideanSpace.equiv (𝕜:=ℂ) (ι:=Fin n)).symm p)

/-- The produced nonzero scale is an actual global coordinate
homeomorphism, so the parameter ball covers a true original-stage open. -/
def scaledOriginalPointHomeomorph (P : ActualInheritedWeightedTailData G) (s : ℂ) (hs0 : s≠0) :
    CoordinateSpace n ≃ₜ ComplexModel n where
  toFun:=scaledOriginalPoint P s
  invFun:=fun z=>(EuclideanSpace.equiv (𝕜:=ℂ) (ι:=Fin n))
    (actualDiagonalMap (fun i=>(s^(degLexWeight n P.germs.degreeBound i))⁻¹) z)
  left_inv:=by
    intro p
    apply (EuclideanSpace.equiv (𝕜:=ℂ) (ι:=Fin n)).symm.injective
    change actualDiagonalMap (fun i=>(s^(degLexWeight n P.germs.degreeBound i))⁻¹)
      (actualDiagonalMap (fun i=>s^(degLexWeight n P.germs.degreeBound i))
        ((EuclideanSpace.equiv (𝕜:=ℂ) (ι:=Fin n)).symm p))=_
    ext i
    rw [actualDiagonalMap_apply,actualDiagonalMap_apply,←mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ hs0),one_mul]
  right_inv:=by
    intro z
    change actualDiagonalMap _ ((EuclideanSpace.equiv (𝕜:=ℂ) (ι:=Fin n)).symm
      ((EuclideanSpace.equiv (𝕜:=ℂ) (ι:=Fin n)) (actualDiagonalMap _ z)))=z
    rw [ContinuousLinearEquiv.symm_apply_apply]
    ext i
    rw [actualDiagonalMap_apply,actualDiagonalMap_apply,←mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ hs0),one_mul]
  continuous_toFun:=(actualDiagonalMap _).continuous.comp
    (EuclideanSpace.equiv (𝕜:=ℂ) (ι:=Fin n)).symm.continuous
  continuous_invFun:=(EuclideanSpace.equiv (𝕜:=ℂ) (ι:=Fin n)).continuous.comp (actualDiagonalMap _).continuous

def historicalNativeJetWindow (P : ActualInheritedWeightedTailData G) (s : ℂ) (hs0 : s≠0) (δ : ℝ) :
    Set (ComplexModel n) :=
  (scaledOriginalPointHomeomorph P s hs0).symm ⁻¹' Metric.ball 0 δ

theorem historicalNativeJetWindow_isOpen (P : ActualInheritedWeightedTailData G) (s : ℂ)
    (hs0 : s≠0) (δ : ℝ) : IsOpen (historicalNativeJetWindow P s hs0 δ) :=
  Metric.isOpen_ball.preimage (scaledOriginalPointHomeomorph P s hs0).symm.continuous

theorem historicalNativeJetWindow_zero (P : ActualInheritedWeightedTailData G) (s : ℂ)
    (hs0 : s≠0) {δ : ℝ} (hδ : 0<δ) : (0 : ComplexModel n)∈historicalNativeJetWindow P s hs0 δ := by
  change (EuclideanSpace.equiv (𝕜:=ℂ) (ι:=Fin n)) (actualDiagonalMap _ 0)∈Metric.ball 0 δ
  rw [map_zero,map_zero]
  exact Metric.mem_ball_self hδ

/-- EVERY actual point of the produced true open is covered by the same
parameter ball, with a literal point equality. -/
theorem historicalNativeJetWindow_coverage (P : ActualInheritedWeightedTailData G) (s : ℂ)
    (hs0 : s≠0) (δ : ℝ) (u : ComplexModel n) (hu : u∈historicalNativeJetWindow P s hs0 δ) :
    ∃p∈Metric.ball (0 : CoordinateSpace n) δ,scaledOriginalPoint P s p=u :=
  ⟨(scaledOriginalPointHomeomorph P s hs0).symm u,hu,
    (scaledOriginalPointHomeomorph P s hs0).apply_symm_apply u⟩

private theorem sourceScaledFamily_value (P : ActualInheritedWeightedTailData G) (s : ℂ)
    (j : Fin (actualVertexCount n I)) (p : CoordinateSpace n) :
    actualInheritedSourceScaledFamily P s j p=
      (s^weightedDegree (degLexWeight n P.germs.degreeBound) (actualVertexEnumeration n I j).val)⁻¹*
        P.representative (actualVertexEnumeration n I j) (scaledOriginalPoint P s p) := by
  let W:=degLexWeight n P.germs.degreeBound
  let e:=EuclideanSpace.equiv (𝕜:=ℂ) (ι:=Fin n)
  have hPoint : actualWeightedScalingMap W (jointPoint n (p,s))=scaledOriginalPoint P s p := by
    have h:=weighted_source_point W s (e.symm p)
    change actualWeightedScalingMap W (jointPoint n (e (e.symm p),s))=
      actualDiagonalMap (fun i=>s^W i) (e.symm p) at h
    rw [e.apply_symm_apply] at h
    exact h
  let a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I):=actualVertexEnumeration n I j
  change P.representative a (actualWeightedScalingMap W (jointPoint n (p,s)))/s^weightedDegree W a.val=
    (s^weightedDegree W a.val)⁻¹*P.representative a (scaledOriginalPoint P s p)
  calc
    _=P.representative a (scaledOriginalPoint P s p)/s^weightedDegree W a.val:=
      congrArg (fun x=>P.representative a x/s^weightedDegree W a.val) hPoint
    _=_:=by rw [div_eq_mul_inv,mul_comm]

/-- The literal current functions and genuine coordinate/unit maps identify
the ENTIRE translated historical members at every inspected actual point. -/
theorem scaled_translated_historical_germ
    {A : Hironaka.HolomorphicIdealSheaves.GermIdeal n (ComplexModel n)} {R : ℕ → ℕ}
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R)
    (P : ActualInheritedWeightedTailData G) {s : ℂ} (hs : s∈Metric.ball 0 P.radius)
    (p : CoordinateSpace n)
    (hdom : MapsTo (fun z=>p+z) (Metric.ball 0 (P.radius/2)) (Metric.ball 0 P.radius))
    (O : Set (ComplexModel n)) (hO : IsOpen O)
    (hEq : ∀x∈O,∀a,P.representative a x=PHS.representatives a x)
    (huO : scaledOriginalPoint P s p∈O)
    (huP : scaledOriginalPoint P s p∈PHS.neighborhood) :
    ∀j : Fin (actualVertexCount n I),
      let a:=actualVertexEnumeration n I j
      let W:=degLexWeight n P.germs.degreeBound
      actualInheritedTranslatedGerm P hs p hdom j=
        HolGerm.constHom ((s^weightedDegree W a.val)⁻¹)*
          actualDiagonalPullback (fun i=>s^W i)
            (translatedGerm (scaledOriginalPoint P s p) (PHS.representatives a)
              (PHS.holomorphicAt _ huP a)) := by
  intro j
  dsimp only
  let a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I):=actualVertexEnumeration n I j
  let W:=degLexWeight n P.germs.degreeBound
  let c : Fin n → ℂ:=fun i=>s^W i
  let e:=EuclideanSpace.equiv (𝕜:=ℂ) (ι:=Fin n)
  let u:=scaledOriginalPoint P s p
  let T : ComplexModel n → ComplexModel n:=fun z=>actualDiagonalMap c (e.symm (p+e z))
  have hT : Continuous T:=(actualDiagonalMap c).continuous.comp
    (e.symm.continuous.comp (continuous_const.add e.continuous))
  have hT0 : T 0=u := by
    simp only [T,map_zero,add_zero,u,scaledOriginalPoint,c,W]
    rfl
  have ht : Tendsto T (𝓝 0) (𝓝 u) := by
    simpa only [hT0] using hT.tendsto 0
  have hnear:=ht.eventually (hO.mem_nhds huO)
  have hRaw:=actual_coordinate_translation_differentiableOn
    (actualInheritedSourceScaledFamily_differentiableOn P hs j) p hdom
  change HolGerm.mk (modelFunction (fun z=>actualInheritedSourceScaledFamily P s j (p+z)))
    (modelFunction_holAt (half_pos P.radius_pos) hRaw)=_
  unfold actualDiagonalPullback
  rw [translatedGerm,compAlgHom_mk,←HolGerm.mk_const,←HolGerm.mk_mul]
  apply HolGerm.mk_eq_mk_iff.mpr
  filter_upwards [hnear] with z hz
  change actualInheritedSourceScaledFamily P s j (p+e z)=
    (s^weightedDegree W (actualVertexEnumeration n I j).val)⁻¹*
      PHS.representatives (actualVertexEnumeration n I j) (actualDiagonalMap c z+u)
  rw [sourceScaledFamily_value]
  change (s^weightedDegree W a.val)⁻¹*P.representative a (T z)=
    (s^weightedDegree W a.val)⁻¹*PHS.representatives a (actualDiagonalMap c z+u)
  rw [hEq (T z) hz a]
  congr 1
  apply congrArg (PHS.representatives a)
  change actualDiagonalMap c (e.symm (p+e z))=actualDiagonalMap c z+actualDiagonalMap c (e.symm p)
  rw [map_add,e.symm_apply_apply,map_add,add_comm]

/-- The formal Neumann family is the actual SAME translated family, not a
new family chosen from its diagram. -/
theorem translated_neumann_family_taylor
    (P : ActualInheritedWeightedTailData G) {s : ℂ} (hs : s∈Metric.ball 0 P.radius)
    (p : CoordinateSpace n)
    (hdom : MapsTo (fun z=>p+z) (Metric.ball 0 (P.radius/2)) (Metric.ball 0 P.radius))
    (hH : ∀j,DifferentiableOn ℂ (actualInheritedTranslatedTail P s p j) (Metric.ball 0 (P.radius/2))) :
    ∀j,actualUnshiftedTaylorAlgHom n (modelGerm (half_pos P.radius_pos)
      ((wordMonomial_differentiable (actualVertexWords n I j)).differentiableOn.add (hH j)))=
      actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom j) := by
  intro j
  apply congrArg (actualUnshiftedTaylorAlgHom n)
  have hRaw:=actual_coordinate_translation_differentiableOn
    (actualInheritedSourceScaledFamily_differentiableOn P hs j) p hdom
  change modelGerm (half_pos P.radius_pos)
    ((wordMonomial_differentiable (actualVertexWords n I j)).differentiableOn.add (hH j))=
    modelGerm (half_pos P.radius_pos) hRaw
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun z=>by
    change wordMonomial (actualVertexWords n I j)
      ((EuclideanSpace.equiv (𝕜:=ℂ) (ι:=Fin n)) z)+
      (actualInheritedSourceScaledFamily P s j
        (p+(EuclideanSpace.equiv (𝕜:=ℂ) (ι:=Fin n)) z)-
        wordMonomial (actualVertexWords n I j) ((EuclideanSpace.equiv (𝕜:=ℂ) (ι:=Fin n)) z))=
      actualInheritedSourceScaledFamily P s j (p+(EuclideanSpace.equiv (𝕜:=ℂ) (ι:=Fin n)) z)
    ring


/-- Transparent OUTPUT of the actual stage: one fixed source neighbourhood
before all inspected geometric HS points and all whole jet orders. -/
def ActualHistoricalWholeJetNeighborhood
    {A : Hironaka.HolomorphicIdealSheaves.GermIdeal n (ComplexModel n)} {R : ℕ → ℕ}
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R) : Prop :=
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
        ((∀ℓ,HironakaHolomorphicJetChartInvariance.hilbertSamuelAt A (scaledOriginalPoint P s p) ℓ=R ℓ) →
          ∀q,Function.Bijective (historicalWholeJetMap (actualVertexWords n I)
            (fun j=>actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom j)) q))

/-- Actual geometric HS on the SAME historical stage derives every
translated mark, and genuine Neumann division constructs all whole jet
frames jointly. No target mark/frame/diagram or new basis is supplied. -/
theorem exists_actual_geometric_historical_whole_jet_neighbourhood
    {A : Hironaka.HolomorphicIdealSheaves.GermIdeal n (ComplexModel n)} {R : ℕ → ℕ}
    (hspan : Ideal.span (range G.germs)=I)
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R) :
    ActualHistoricalWholeJetNeighborhood PHS := by
  classical
  obtain ⟨P,s,hs0,hs,_D0,D1,δ,hδ,_hSource,hnear⟩:=
    exists_actual_inherited_uniform_translated_neumann_division I G hspan
  have hEq (a) : P.representative a=ᶠ[𝓝 (0 : ComplexModel n)] PHS.representatives a:=
    HolGerm.mk_eq_mk_iff.mp ((P.representative_eq a).trans (PHS.sameGerms a).symm)
  have hPmem : ∀ᶠx in 𝓝 (0 : ComplexModel n),x∈PHS.neighborhood:=
    PHS.isOpen_neighborhood.mem_nhds PHS.zero_mem
  have hAll : ∀ᶠx in 𝓝 (0 : ComplexModel n),x∈PHS.neighborhood ∧
      ∀a,P.representative a x=PHS.representatives a x:=
    hPmem.and (eventually_all.mpr hEq)
  obtain ⟨O,hOsub,hO,h0O⟩:=mem_nhds_iff.mp hAll
  let e:=EuclideanSpace.equiv (𝕜:=ℂ) (ι:=Fin n)
  have hc : Continuous (scaledOriginalPoint P s):=
    (actualDiagonalMap (fun i=>s^(degLexWeight n P.germs.degreeBound i))).continuous.comp e.symm.continuous
  have hc0 : scaledOriginalPoint P s (0 : CoordinateSpace n)=0:=by
    change actualDiagonalMap _ (e.symm 0)=0
    rw [map_zero,map_zero]
  have ht : Tendsto (scaledOriginalPoint P s) (𝓝 0) (𝓝 0) := by
    simpa only [hc0] using hc.tendsto 0
  have hpre:=ht.eventually (hO.mem_nhds h0O)
  obtain ⟨η,hη,hηsub⟩:=Metric.mem_nhds_iff.mp hpre
  refine ⟨P,s,hs0,hs,min δ η,lt_min hδ hη,
    historicalNativeJetWindow_isOpen P s hs0 _,historicalNativeJetWindow_zero P s hs0 (lt_min hδ hη),?_,?_⟩
  · intro u hu
    obtain ⟨p,hp,hpu⟩:=historicalNativeJetWindow_coverage P s hs0 (min δ η) u hu
    have hpη : p∈Metric.ball (0 : CoordinateSpace n) η:=mem_ball_zero_iff.mpr
      (lt_of_lt_of_le (mem_ball_zero_iff.mp hp) (min_le_right δ η))
    have hup:=(hOsub (hηsub hpη)).1
    exact hpu ▸ hup
  intro p hp
  have hpδ : p∈Metric.ball (0 : CoordinateSpace n) δ:=mem_ball_zero_iff.mpr
    (lt_of_lt_of_le (mem_ball_zero_iff.mp hp) (min_le_left δ η))
  have hpη : p∈Metric.ball (0 : CoordinateSpace n) η:=mem_ball_zero_iff.mpr
    (lt_of_lt_of_le (mem_ball_zero_iff.mp hp) (min_le_right δ η))
  have huO : scaledOriginalPoint P s p∈O:=hηsub hpη
  have hu : scaledOriginalPoint P s p∈PHS.neighborhood:=(hOsub huO).1
  obtain ⟨hdom,hHd,hHb,_hPolynomial⟩:=hnear p hpδ
  have hCov:=scaled_translated_historical_germ PHS P hs p hdom O hO
    (fun x hx=>(hOsub hx).2) huO hu
  refine ⟨hdom,hu,hCov,?_⟩
  intro hHS
  have hMarked : ∀j : Fin (actualVertexCount n I),
      actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom j)∈
      genuineFormalVariables n^normalExponentDegree (wordExponent (actualVertexWords n I j)) := by
    intro j
    let a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I):=actualVertexEnumeration n I j
    have hOld:=(PHS.wholeHS _ hu).mpr hHS a
    have hDiag:=diagonal_pullback_mem_maximal_power
      (fun i=>s^(degLexWeight n P.germs.degreeBound i)) hOld
    have hScaled:=Ideal.mul_mem_left
      (IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^normalExponentDegree a.val)
      (HolGerm.constHom ((s^weightedDegree (degLexWeight n P.germs.degreeBound) a.val)⁻¹)) hDiag
    have hCurrent : actualInheritedTranslatedGerm P hs p hdom j∈
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^normalExponentDegree a.val :=
      Eq.mpr (congrArg (fun F : HolGerm (ComplexModel n)=>F∈
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^normalExponentDegree a.val) (hCov j)) hScaled
    have hTaylor:=Ideal.mem_map_of_mem (actualUnshiftedTaylorAlgHom n).toRingHom hCurrent
    rw [map_actualUnshifted_maximal_pow] at hTaylor
    have hTaylor' : actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom j)∈
        genuineFormalVariables n^normalExponentDegree (actualVertexEnumeration n I j).val:=hTaylor
    simpa only [actualVertexWords,wordExponent_wordOfExponent] using hTaylor'
  have hIdentity:=translated_neumann_family_taylor P hs p hdom hHd
  have hMarkedNeumann : ∀j,actualUnshiftedTaylorAlgHom n (modelGerm (half_pos P.radius_pos)
      ((wordMonomial_differentiable (actualVertexWords n I j)).differentiableOn.add (hHd j)))∈
      genuineFormalVariables n^normalExponentDegree (wordExponent (actualVertexWords n I j)) := by
    intro j
    rw [hIdentity j]
    exact hMarked j
  intro q
  have hFrame:=historicalWholeJetMap_bijective_of_neumann (half_pos P.radius_pos)
    (actualVertexWords n I) D1 (actualInheritedTranslatedTail P s p) hHd hHb hMarkedNeumann q
  have hFamily : (fun j=>actualUnshiftedTaylorAlgHom n (modelGerm (half_pos P.radius_pos)
      ((wordMonomial_differentiable (actualVertexWords n I j)).differentiableOn.add (hHd j))))=
      (fun j=>actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom j)):=funext hIdentity
  rw [hFamily] at hFrame
  exact hFrame

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

/-- ORIGINAL source geometry produces the SAME actual stage, complete
historical/global continuation and every moving whole-jet frame with the
original entire HS reference. No moving mark, division or frame is supplied. -/
theorem exists_actual_geometric_stage_with_moving_whole_jets
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
            D.targetSpan (actualAdaptedHistoricalCurrentSource D).selector (hilbertSamuelValue I) PHS ∧ ActualHistoricalWholeJetNeighborhood PHS := by
  dsimp only
  obtain ⟨hcut,e,b,Θ,hΘ0,he,hΘsrc,hSquare,hp,f,hqf,hvf,Cg,u,hu,D,P,hOldTarget,hRecord,
    hStrict,hOriginCurrent,PHS,hRepresentatives,hPHS,hMap,hFlags,hIntrinsic,hContactLaws,
    hRebaseLaws,hWeightedLaws,hHSTransition,hRepeated⟩:=
    exists_actual_geometric_stage_prescribed_historical_iteration I G hmem hw S hred hContact
      U h0U c hc hrep hCos E π hπ y hy W hWa Φ hΦsrc hΦ0 hΦid hΦdom hOrigin hHS
  refine ⟨hcut,e,b,Θ,hΘ0,he,hΘsrc,hSquare,hp,f,hqf,hvf,Cg,u,hu,D,P,hOldTarget,hRecord,
    hStrict,hOriginCurrent,PHS,hRepresentatives,hPHS,hMap,hFlags,hIntrinsic,hContactLaws,
    hRebaseLaws,hWeightedLaws,hHSTransition,hRepeated,?_⟩
  exact exists_actual_geometric_historical_whole_jet_neighbourhood D.targetSpan PHS

end
end Hironaka.HironakaActualHistoricalWholeJetFrames
