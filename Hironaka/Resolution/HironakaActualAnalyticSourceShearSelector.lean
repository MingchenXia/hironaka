import Hironaka.Resolution.HironakaActualAnalyticSourceShearTaylor
import Hironaka.Resolution.HironakaActualInheritedWholePrefixNormalization
import Hironaka.Resolution.HironakaActualNormalAllDirectionGeometricConverse

/-! Actual source shears preserve the SAME fixed historical selector whenever
its source block variables are fixed and are nonpivot normal directions.
Whole Taylor identities prove actual analytic derivative transport; source
contacts and Jacobians are transported, never assumed at the target. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualAnalyticSourceShearSelector
noncomputable section
open HolGerm HironakaHolomorphicJetMonomialSpan
 HironakaActualCoefficientPresentationCentrePower HironakaActualAnalyticBlowupTaylor
 HironakaActualAnalyticDirectionRemovalQuotient HironakaActualAnalyticSourceShearTaylor
 HironakaActualInheritedWholePrefixNormalization HironakaActualFormalBlowupAllDirections
 HironakaActualInheritedAnalyticBlockJacobian HironakaActualOriginalTaylorDerivatives
 HironakaActualAnalyticFormalNormalPowers HironakaActualFixedInheritedSelector
 HironakaActualAnalyticBlockGraphTranslation HironakaActualFormalCoordinatePowerDivision
 HironakaActualCauchyCoefficientLimits HironakaActualNormalAllDirectionGeometricConverse
 HironakaActualRelativeNormalJetDivision HironakaActualFormalInitialDiagram
 HironakaActualInheritedNestedContactFlag HironakaRelativeNormalMonomialBasis
 HironakaActualNormalMarkedDirection HironakaActualRelativeStandardnessNormalPointBridge
 HironakaActualNormalZeroAnalyticSaturation HironakaActualCanonicalBlockJacobian
 HironakaActualRelativeStandardnessBlockSupport
variable {n : ℕ}

theorem actualAnalyticMultiDerivative_source_shear
    (A : Set (Fin n)) (e : Fin n) (he : e∈A) (w : Fin n → ℂ)
    (β : Fin n →₀ ℕ) (hβ : (↑β.support : Set (Fin n))⊆A\{e})
    (g : HolGerm (ComplexModel n)) :
    actualAnalyticMultiDerivative β (actualAnalyticDirectionShearGermEquiv A e w g)=
      actualAnalyticDirectionShearGermEquiv A e w (actualAnalyticMultiDerivative β g) := by
  apply actualUnshiftedTaylorAlgHom_injective n
  rw [actualTaylor_actualAnalyticMultiDerivative,actualTaylor_analytic_source_shear A e he,
    actualTaylor_analytic_source_shear A e he,actualTaylor_actualAnalyticMultiDerivative,
    actualFormalMultiDerivative_centerShear A e he w β hβ]

theorem actualAnalyticCoordinateDerivative_source_shear
    (A : Set (Fin n)) (e : Fin n) (he : e∈A) (w : Fin n → ℂ)
    (i : Fin n) (hi : i∈A\{e}) (g : HolGerm (ComplexModel n)) :
    actualAnalyticCoordinateDerivative i (actualAnalyticDirectionShearGermEquiv A e w g)=
      actualAnalyticDirectionShearGermEquiv A e w (actualAnalyticCoordinateDerivative i g) := by
  apply actualUnshiftedTaylorAlgHom_injective n
  rw [actualTaylor_actualAnalyticCoordinateDerivative,actualTaylor_analytic_source_shear A e he,
    actualTaylor_analytic_source_shear A e he,actualTaylor_actualAnalyticCoordinateDerivative,
    pderiv_actualFormalCenterShear A e he w i hi.1 hi.2]

private theorem eval_source_shear
    (A : Set (Fin n)) (e : Fin n) (w : Fin n → ℂ) (g : HolGerm (ComplexModel n)) :
    HolGerm.eval (actualAnalyticDirectionShearGermEquiv A e w g)=HolGerm.eval g := by
  obtain ⟨F,hF,rfl⟩:=HolGerm.exists_eq_mk g
  change F (actualAnalyticDirectionShear A e w 0)=F 0
  rw [actualAnalyticDirectionShear_zero]

private theorem block_ideal_source_shear_le
    (A B : Set (Fin n)) (e : Fin n) (he : e∈A) (w : Fin n → ℂ)
    (hw : ∀i∈B,w i=0) :
    Ideal.map (actualAnalyticDirectionShearGermEquiv A e w).toRingEquiv.toRingHom
      (actualAnalyticCoordinateBlockIdeal B)≤actualAnalyticCoordinateBlockIdeal B := by
  have hFix (i : Fin n) (hi : i∈B) :
      actualAnalyticDirectionShearGermEquiv A e w (coordinateGerm i)=coordinateGerm i := by
    apply actualUnshiftedTaylorAlgHom_injective n
    rw [actualTaylor_analytic_source_shear A e he,actualUnshiftedTaylor_coordinate,
      actualFormalCenterShear_X]
    simp only [actualFormalCenterShearCoordinates,hw i hi,map_zero,zero_mul,ite_self,add_zero]
  apply Ideal.map_le_iff_le_comap.mpr
  apply Ideal.span_le.mpr
  rintro g ⟨i,hi,rfl⟩
  change actualAnalyticDirectionShearGermEquiv A e w (coordinateGerm i)∈actualAnalyticCoordinateBlockIdeal B
  rw [hFix i hi]
  exact Ideal.subset_span ⟨i,hi,rfl⟩

/-- The SAME raw historical selector and selected numerators survive the
actual source shear with every block contact and actual block Jacobian. -/
theorem actual_fixed_selector_source_shear
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (G : V → HolGerm (ComplexModel n)) (A : Set (Fin n))
    (e : Fin n) (he : e∈A) (w : Fin n → ℂ)
    (hEss : fixedSelectorEssential V⊆A\{e})
    (hw : ∀i∈fixedSelectorEssential V,w i=0)
    (hContact : ∀k,actualFixedSelectorContactAt S G k) :
    let GS:=fun a=>actualAnalyticDirectionShearGermEquiv A e w (G a)
    (∀k,actualFixedSelectorContactAt S GS k) ∧
      ∀k,actualFixedSelectorJacobian S GS k=actualFixedSelectorJacobian S G k := by
  let GS:=fun a=>actualAnalyticDirectionShearGermEquiv A e w (G a)
  have hBlock (k : ℕ) (i : Fin n) (hi : i∈fixedSelectorBlock V k) :
      i∈fixedSelectorEssential V := (fixedSelectorBlockEssential k ⟨i,hi⟩).property
  have hDeriv (k : ℕ) (j : fixedSelectorBlock V k) :
      actualFixedSelectorDerivative S GS (fixedSelectorBlockEssential k j)=
        actualAnalyticDirectionShearGermEquiv A e w
          (actualFixedSelectorDerivative S G (fixedSelectorBlockEssential k j)) := by
    apply actualAnalyticMultiDerivative_source_shear A e he w
    intro i hi
    apply hEss
    apply hBlock k i
    by_contra h
    exact (Finsupp.mem_support_iff.mp hi) (fixedSelector_beta_support S k j i h)
  constructor
  · intro k j
    rw [hDeriv k j]
    exact block_ideal_source_shear_le A (fixedSelectorBlock V k) e he w
      (fun i hi=>hw i (hBlock k i hi))
      (Ideal.mem_map_of_mem _ (hContact k j))
  · intro k
    ext j i
    change HolGerm.eval (actualAnalyticCoordinateDerivative i.val
      (actualFixedSelectorDerivative S GS (fixedSelectorBlockEssential k j)))=_
    rw [hDeriv k j,actualAnalyticCoordinateDerivative_source_shear A e he w i.val
      (hEss (hBlock k i.val i.property))]
    exact eval_source_shear A e w _

/-- Actual retained orders in the ORIGINAL arbitrary chart internally force
the source-shear conditions for EVERY nonzero normal direction pivot. The
SAME historical selector therefore transports through the source adaptation.
No adapted contact or Jacobian is supplied. -/
theorem actual_marked_orders_source_shear_selector
    (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I))
    (hmem : ∀a,G.germs a∈I) (q e : Fin n) (hqe : q≤e) (b : Fin n → ℂ)
    (hp : ∀a,G.germs a∈actualAnalyticCoordinateIdeal (Set.Ici q)^normalExponentDegree a.val)
    (hOrder : ∀a,HironakaActualNormalAllDirectionAnalyticSaturation.sameAnalyticNormalNormalizedVertex
      n I G q e hqe b hp a∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^normalExponentDegree a.val)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)))
    (hred : ∀k,ActualInheritedPrefixReducedAt G k)
    (hContact : ∀k,actualFixedSelectorContactAt S G.germs k)
    (f : Fin n) (hqf : q≤f) (hvf : actualNormalMarkedDirection (Set.Ici q) e b f≠0) :
    let w:=fun i=>actualNormalMarkedDirection (Set.Ici q) e b i /
      actualNormalMarkedDirection (Set.Ici q) e b f
    let GS:=fun a=>actualAnalyticDirectionShearGermEquiv (Set.Ici q) f w (G.germs a)
    (∀k,actualFixedSelectorContactAt S GS k) ∧
      ∀k,actualFixedSelectorJacobian S GS k=actualFixedSelectorJacobian S G.germs k := by
  obtain ⟨_hpf,hAll⟩:=actual_normal_marked_orders_preserve_same_historical_selector n I G hmem
    q e hqe b hp hOrder S hred hContact
  have hLegal (i : Fin n)
      (hi : i∈fixedSelectorEssential (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I))) :
      i∈Set.Ici q\{e} ∧ b i=0 := by
    obtain ⟨a,ha⟩:=hi
    have hBlock : i∈actualDegreePrefixVariables MonomialOrder.degLex (analyticZeroTaylorIdeal n I)
        (normalExponentDegree a.val):=⟨a,le_rfl,ha⟩
    exact ⟨(hAll (normalExponentDegree a.val)).1.1 hBlock,
      (hAll (normalExponentDegree a.val)).1.2 i hBlock⟩
  have hvi (i : Fin n)
      (hi : i∈fixedSelectorEssential (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I))) :
      actualNormalMarkedDirection (Set.Ici q) e b i=0 := by
    have h:=hLegal i hi
    have hie : i≠e:=h.1.2
    simp only [actualNormalMarkedDirection,if_neg hie,actualNormalPointDirection,
      if_pos h.1.1,h.2]
  have hfnot : f∉fixedSelectorEssential (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)) :=
    fun hf=>hvf (hvi f hf)
  apply actual_fixed_selector_source_shear S G.germs (Set.Ici q) f hqf
    (fun i=>actualNormalMarkedDirection (Set.Ici q) e b i /
      actualNormalMarkedDirection (Set.Ici q) e b f)
  · intro i hi
    exact ⟨(hLegal i hi).1.1,fun hif=>hfnot (hif ▸ hi)⟩
  · intro i hi
    rw [hvi i hi,zero_div]
  · exact hContact

end
end Hironaka.HironakaActualAnalyticSourceShearSelector
