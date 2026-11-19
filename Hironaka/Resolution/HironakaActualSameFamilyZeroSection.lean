import Hironaka.Resolution.HironakaActualZeroSectionCanonicalFamily
import Hironaka.Resolution.HironakaActualNormalZeroAnalyticSaturation

/-! Genuine zero-section augmentation of the SAME given inherited family.
Blueprint: hironaka-actual-same-family-zero-section-20261102.tex. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualSameFamilyZeroSection
noncomputable section
open HolGerm HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaActualZeroSectionStabilization HironakaActualZeroSectionFormalBasis
  HironakaActualZeroSectionCanonicalFamily HironakaActualFormalInitialDiagram
  HironakaActualCoefficientPresentationCentrePower HironakaActualRelativeTaylorCoefficients
  HironakaActualTaylorCoordinateNaturality HironakaActualRelativeNormalJetDivision
  HironakaActualNormalZeroAnalyticSaturation HironakaActualAnalyticCanonicalVertices
  HironakaActualWeightedVertexSmallTails

variable {n t : ℕ} (I : Ideal (HolGerm (ComplexModel n)))
  (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I))

private def liftedGerm
    (a : ZeroSectionVertexIndex (t:=t) (analyticZeroTaylorIdeal n I)) :
    HolGerm (ComplexModel (n+t)) :=
  match a with
  | .inl b => tangentPullback n t (G.germs b)
  | .inr j => normalCoordinate n t j.val

private theorem lifted_monic
    (a : ZeroSectionVertexIndex (t:=t) (analyticZeroTaylorIdeal n I)) :
    MvPowerSeries.coeff (originalZeroSectionVertexEquiv (t:=t) I a).val
      (actualUnshiftedTaylorAlgHom (n+t) (liftedGerm I G a))=1 := by
  cases a with
  | inl a =>
    change MvPowerSeries.coeff (actualJoinedExponent a.val (0 : Fin t→₀ℕ))
      (actualUnshiftedTaylorAlgHom (n+t) (tangentPullback n t (G.germs a)))=1
    have ht:=DFunLike.congr_fun (actualUnshiftedTaylor_tangentPullback n t) (G.germs a)
    change actualUnshiftedTaylorAlgHom (n+t) (tangentPullback n t (G.germs a))=
      MvPowerSeries.rename (Fin.castAdd t) (actualUnshiftedTaylorAlgHom n (G.germs a)) at ht
    rw [ht,
      coefficient_tangent_rename_joined,if_pos rfl]
    exact G.monic a
  | inr j =>
    change MvPowerSeries.coeff (Finsupp.single (j.val.natAdd n) 1)
      (actualUnshiftedTaylorAlgHom (n+t) (normalCoordinate n t j.val))=1
    rw [originalTaylor_normalCoordinate]
    simp

private theorem lifted_lower
    (a : ZeroSectionVertexIndex (t:=t) (analyticZeroTaylorIdeal n I))
    (b : Fin (n+t)→₀ℕ)
    (hb : MonomialOrder.degLex.toSyn b <
      MonomialOrder.degLex.toSyn (originalZeroSectionVertexEquiv (t:=t) I a).val) :
    MvPowerSeries.coeff b (actualUnshiftedTaylorAlgHom (n+t) (liftedGerm I G a))=0 := by
  cases a with
  | inl a =>
    change MonomialOrder.degLex.toSyn b <
      MonomialOrder.degLex.toSyn (actualJoinedExponent a.val (0 : Fin t→₀ℕ)) at hb
    change MvPowerSeries.coeff b
      (actualUnshiftedTaylorAlgHom (n+t) (tangentPullback n t (G.germs a)))=0
    have ht:=DFunLike.congr_fun (actualUnshiftedTaylor_tangentPullback n t) (G.germs a)
    change actualUnshiftedTaylorAlgHom (n+t) (tangentPullback n t (G.germs a))=
      MvPowerSeries.rename (Fin.castAdd t) (actualUnshiftedTaylorAlgHom n (G.germs a)) at ht
    rw [ht,
      ←actualJoinedExponent_split b,coefficient_tangent_rename_joined]
    by_cases hN : actualNormalExponent b=0
    · rw [if_pos hN]
      have hlt : MonomialOrder.degLex.toSyn
          (actualJoinedExponent (actualTangentExponent b) (0 : Fin t→₀ℕ)) <
          MonomialOrder.degLex.toSyn (actualJoinedExponent a.val (0 : Fin t→₀ℕ)) := by
        simpa only [hN] using (show MonomialOrder.degLex.toSyn
          (actualJoinedExponent (actualTangentExponent b) (actualNormalExponent b)) <
          MonomialOrder.degLex.toSyn (actualJoinedExponent a.val (0 : Fin t→₀ℕ)) by
            rwa [actualJoinedExponent_split])
      exact G.lower a _ ((degLex_joined_zero_lt_iff _ _).mp hlt)
    · rw [if_neg hN]
  | inr j =>
    change MonomialOrder.degLex.toSyn b <
      MonomialOrder.degLex.toSyn (Finsupp.single (j.val.natAdd n) 1) at hb
    change MvPowerSeries.coeff b
      (actualUnshiftedTaylorAlgHom (n+t) (normalCoordinate n t j.val))=0
    rw [originalTaylor_normalCoordinate,MvPowerSeries.X_def]
    have hne : b≠Finsupp.single (j.val.natAdd n) 1 := by
      intro he
      rw [he] at hb
      exact lt_irrefl _ hb
    simp [MvPowerSeries.coeff_monomial,hne]

/-- The SAME given inherited family, augmented by actual normal coordinates
on the genuine whole zero-section ideal and its internally proved labels. -/
def augmentedFamily : ActualAnalyticInheritedFamily (n+t) 0
    (analyticZeroTaylorIdeal (n+t) (actualZeroSectionIdeal n t I)) where
  germs a := liftedGerm (n:=n) (t:=t) I G ((originalZeroSectionVertexEquiv (t:=t) I).symm a)
  monic a := by
    have h:=lifted_monic (n:=n) (t:=t) I G ((originalZeroSectionVertexEquiv (t:=t) I).symm a)
    have he:=(originalZeroSectionVertexEquiv (t:=t) I).apply_symm_apply a
    rw [he] at h
    exact h
  lower a b hb := by
    apply lifted_lower (n:=n) (t:=t) I G ((originalZeroSectionVertexEquiv (t:=t) I).symm a) b
    have he:=(originalZeroSectionVertexEquiv (t:=t) I).apply_symm_apply a
    rw [he]
    exact hb

/-- Every old member is literally the pullback of the GIVEN germ. -/
theorem augmentedFamily_lift (a : ActualVertexIndex n I) :
    (augmentedFamily (t:=t) I G).germs (originalZeroSectionVertexEquiv (t:=t) I (.inl a))=
      tangentPullback n t (G.germs a) := by
  change liftedGerm (n:=n) (t:=t) I G
    ((originalZeroSectionVertexEquiv (t:=t) I).symm
      (originalZeroSectionVertexEquiv (t:=t) I (.inl a)))=_
  exact congrArg (liftedGerm (n:=n) (t:=t) I G)
    ((originalZeroSectionVertexEquiv (t:=t) I).symm_apply_apply (.inl a))

/-- Every existing normal label retains exactly its actual normal coordinate. -/
theorem augmentedFamily_normal
    (hI : Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I≠⊤) (j : Fin t) :
    (augmentedFamily (t:=t) I G).germs (originalZeroSectionVertexEquiv (t:=t) I (.inr ⟨j,hI⟩))=
      normalCoordinate n t j := by
  change liftedGerm (n:=n) (t:=t) I G
    ((originalZeroSectionVertexEquiv (t:=t) I).symm
      (originalZeroSectionVertexEquiv (t:=t) I (.inr ⟨j,hI⟩)))=_
  exact congrArg (liftedGerm (n:=n) (t:=t) I G)
    ((originalZeroSectionVertexEquiv (t:=t) I).symm_apply_apply (.inr ⟨j,hI⟩))

/-- Source generation of the SAME given family produces the entire actual
zero-section ideal; no target family or target span is supplied. -/
theorem augmentedFamily_span (hI : I≠⊤) (hspan : Ideal.span (range G.germs)=I) :
    Ideal.span (range (augmentedFamily (t:=t) I G).germs)=actualZeroSectionIdeal n t I := by
  have hK:=actualTaylor_ideal_ne_top I hI
  have hr : range (augmentedFamily (t:=t) I G).germs=
      range (fun a=>tangentPullback n t (G.germs a)) ∪ range (normalCoordinate n t) := by
    ext g
    constructor
    · rintro ⟨a,rfl⟩
      cases he : (originalZeroSectionVertexEquiv (t:=t) I).symm a with
      | inl b =>
        left
        refine ⟨b,?_⟩
        change _=liftedGerm (n:=n) (t:=t) I G
          ((originalZeroSectionVertexEquiv (t:=t) I).symm a)
        rw [he]
        rfl
      | inr j =>
        right
        refine ⟨j.val,?_⟩
        change _=liftedGerm (n:=n) (t:=t) I G
          ((originalZeroSectionVertexEquiv (t:=t) I).symm a)
        rw [he]
        rfl
    · rintro (⟨a,rfl⟩ | ⟨j,rfl⟩)
      · exact ⟨originalZeroSectionVertexEquiv (t:=t) I (.inl a),augmentedFamily_lift I G a⟩
      · exact ⟨originalZeroSectionVertexEquiv (t:=t) I (.inr ⟨j,hK⟩),augmentedFamily_normal I G hK j⟩
  rw [hr,Ideal.span_union]
  have hbase : Ideal.span (range (fun a=>tangentPullback n t (G.germs a)))=
      Ideal.map (tangentPullback n t).toRingHom I := by
    calc
      _=Ideal.map (tangentPullback n t).toRingHom (Ideal.span (range G.germs)) := by
        rw [Ideal.map_span,←Set.range_comp]
        rfl
      _=_ := congrArg (Ideal.map (tangentPullback n t).toRingHom) hspan
  exact congrArg (fun K=>K⊔normalIdeal n t) hbase

end
end Hironaka.HironakaActualSameFamilyZeroSection
