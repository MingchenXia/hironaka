import Hironaka.Resolution.HironakaActualZeroNormalizedCurrentSelector

/-! Finite repeated zero-chart source construction from the source states
PRODUCED at preceding stages. A step supplies only its pivot, genuine source
centre powers and actual normalized-member marked orders. The next ideal,
current family, whole prefixes and selector contacts are constructed internally.
This restricted zero-chart continuation is not arbitrary canonical-centre G8. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualRepeatedZeroCurrentSources
noncomputable section
open HolGerm HironakaHolomorphicJetChartInvariance HironakaHolomorphicPointJets
 HironakaActualAnalyticBlowupTaylor
 HironakaRelativeNormalMonomialBasis HironakaActualFormalInitialDiagram
 HironakaActualRelativeNormalJetDivision HironakaActualInheritedNestedContactFlag
 HironakaActualFixedInheritedSelector HironakaActualCoefficientPresentationCentrePower
 HironakaActualNormalZeroAnalyticSaturation HironakaActualInheritedSourcePermutationFamily
 HironakaActualZeroNormalizedCurrentSelector
variable {n : ℕ}

/-- All current SOURCE properties, indexed by the whole current Taylor ideal. -/
structure ActualZeroCurrentSource (n : ℕ) where
  ideal : Ideal (HolGerm (ComplexModel n))
  family : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n ideal)
  member : ∀a,family.germs a∈ideal
  wholePrefix : ∀k,ActualInheritedPrefixReducedAt family k
  selector : ActualFixedInheritedSelector
    (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n ideal))
  contact : ∀k,actualFixedSelectorContactAt selector family.germs k

/-- A literal zero-chart cut of the current SOURCE. No next source family,
diagram, prefix condition, selector or HS equality can be supplied here. -/
structure ActualZeroSourceCut (S : ActualZeroCurrentSource n) where
  pivot : Fin n
  sourcePower : ∀a,S.family.germs a∈
    actualAnalyticCoordinateIdeal (Set.Ici pivot)^normalExponentDegree a.val
  retainedOrder : ∀a,sameAnalyticZeroNormalizedVertex n S.ideal S.family pivot sourcePower a∈
    IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^normalExponentDegree a.val

/-- Exact transition evidence, constructed by the preceding analytic producer. -/
structure ActualZeroCurrentTransition (S : ActualZeroCurrentSource n) (c : ActualZeroSourceCut S) where
  target : ActualZeroCurrentSource n
  ideal_eq : target.ideal=sameAnalyticZeroNormalizedIdeal n S.ideal S.family c.pivot c.sourcePower
  vertex_eq : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n S.ideal)=
    actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n target.ideal)
  same_member : ∀a,target.family.germs (sourceVertexSetCast vertex_eq a)=
    sameAnalyticZeroNormalizedVertex n S.ideal S.family c.pivot c.sourcePower a
  same_selector : target.selector=sourceFixedSelectorCast vertex_eq S.selector
  diagram_eq : actualInitialDiagram MonomialOrder.degLex (analyticZeroTaylorIdeal n target.ideal)=
    actualInitialDiagram MonomialOrder.degLex (analyticZeroTaylorIdeal n S.ideal)
  profile_eq : ∀ℓ,hilbertSamuelValue target.ideal ℓ=hilbertSamuelValue S.ideal ℓ
  jacobian_eq : ∀k,(actualFixedSelectorJacobian target.selector target.family.germs k).submatrix
    (sourceBlockCast vertex_eq k) (sourceBlockCast vertex_eq k)=
      actualFixedSelectorJacobian S.selector S.family.germs k

theorem nonempty_actual_zero_current_transition
    (S : ActualZeroCurrentSource n) (c : ActualZeroSourceCut S) :
    Nonempty (ActualZeroCurrentTransition S c) := by
  obtain ⟨hD,hV,G',hLiteral,_hSpan,hMember,hPrefix,hHS,hContact,hJac⟩:=
    exists_same_zero_normalized_current_family_and_selector S.ideal S.family S.member
      c.pivot c.sourcePower c.retainedOrder S.selector S.wholePrefix S.contact
  let T : ActualZeroCurrentSource n:=
    { ideal:=sameAnalyticZeroNormalizedIdeal n S.ideal S.family c.pivot c.sourcePower
      family:=G'
      member:=hMember
      wholePrefix:=hPrefix
      selector:=sourceFixedSelectorCast hV S.selector
      contact:=hContact }
  exact ⟨{ target:=T
           ideal_eq:=rfl
           vertex_eq:=hV
           same_member:=hLiteral
           same_selector:=rfl
           diagram_eq:=hD
           profile_eq:=hHS
           jacobian_eq:=hJac }⟩

/-- One fixed internally constructed transition; no target state is chosen by
the caller. Every field remains the exact output of the actual cut producer. -/
def actualZeroCurrentTransition
    (S : ActualZeroCurrentSource n) (c : ActualZeroSourceCut S) : ActualZeroCurrentTransition S c :=
  Classical.choice (nonempty_actual_zero_current_transition S c)

def actualZeroNextSource (S : ActualZeroCurrentSource n) (c : ActualZeroSourceCut S) :
    ActualZeroCurrentSource n := (actualZeroCurrentTransition S c).target

/-- Every later source is the internally produced target of the preceding cut.
There is no constructor accepting a caller-provided next source certificate. -/
inductive ActualZeroCurrentHistory (S0 : ActualZeroCurrentSource n) : ActualZeroCurrentSource n → Type
  | initial : ActualZeroCurrentHistory S0 S0
  | step {S : ActualZeroCurrentSource n} (h : ActualZeroCurrentHistory S0 S)
      (c : ActualZeroSourceCut S) : ActualZeroCurrentHistory S0 (actualZeroNextSource S c)

/-- All genuine whole HS values agree with the INITIAL source after every
finite sequence of the internally constructed zero-chart transitions. -/
theorem actual_zero_current_history_all_hs
    {S0 S : ActualZeroCurrentSource n} (h : ActualZeroCurrentHistory S0 S) :
    ∀ℓ,hilbertSamuelValue S.ideal ℓ=hilbertSamuelValue S0.ideal ℓ := by
  induction h with
  | initial => exact fun _=>rfl
  | @step S h c ih =>
    exact fun ℓ=>((actualZeroCurrentTransition S c).profile_eq ℓ).trans (ih ℓ)

/-- The whole current diagram, and hence the literal vertex label set, are
internally retained at every stage of the restricted continuation. -/
theorem actual_zero_current_history_whole_diagram
    {S0 S : ActualZeroCurrentSource n} (h : ActualZeroCurrentHistory S0 S) :
    actualInitialDiagram MonomialOrder.degLex (analyticZeroTaylorIdeal n S.ideal)=
      actualInitialDiagram MonomialOrder.degLex (analyticZeroTaylorIdeal n S0.ideal) := by
  induction h with
  | initial => rfl
  | @step S h c ih => exact (actualZeroCurrentTransition S c).diagram_eq.trans ih

end
end Hironaka.HironakaActualRepeatedZeroCurrentSources
