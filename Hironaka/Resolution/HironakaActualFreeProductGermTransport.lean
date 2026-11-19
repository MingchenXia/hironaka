import Hironaka.Resolution.HironakaActualZeroSectionCentreGeometry
import Hironaka.Resolution.HironakaActualAnalyticBlockGraphTranslation

/-! Whole inverse-product pullback on the SAME analytic germs. The existing
product extension supplies the actual functions and actual open domains.
Essential sections, derivatives and coordinate ideals are preserved for
arbitrary nonlinear free charts. No finite-jet substitute is used.
Blueprint: hironaka-actual-inherited-free-product-flattening-extension.tex.
Initial source draft only; no kernel acceptance is asserted. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology

namespace Hironaka.HironakaActualFreeProductGermTransport
noncomputable section
open HolGerm HironakaRelativeNormalIdeal HironakaHolomorphicJetChartInvariance
  HironakaActualZeroSectionCentreGeometry HironakaActualAnalyticBlockGraphTranslation
  HironakaActualInheritedAnalyticBlockJacobian HironakaHolomorphicJetMonomialSpan
  HironakaActualCoefficientPresentationCentrePower OkaRelationSheaf
  HironakaRelativeNormalTaylorCoefficients

private def productAtZero (m e : ℕ)
    (χ : LocalHolomorphicEquivAt (n := m) (0 : ComplexModel m)) :
    LocalHolomorphicEquivAt (n := m+e) (0 : ComplexModel (m+e)) where
  source := (actual_zeroSection_localEquiv m e 0 χ).source
  target := (actual_zeroSection_localEquiv m e 0 χ).target
  isOpen_source := (actual_zeroSection_localEquiv m e 0 χ).isOpen_source
  isOpen_target := (actual_zeroSection_localEquiv m e 0 χ).isOpen_target
  center_mem_source := by
    change tangentProjection m e 0 ∈ χ.source
    simpa only [map_zero] using χ.center_mem_source
  toFun := (actual_zeroSection_localEquiv m e 0 χ).toFun
  invFun := (actual_zeroSection_localEquiv m e 0 χ).invFun
  toFun_holomorphic := (actual_zeroSection_localEquiv m e 0 χ).toFun_holomorphic
  invFun_holomorphic := (actual_zeroSection_localEquiv m e 0 χ).invFun_holomorphic
  mapsTo_toFun := (actual_zeroSection_localEquiv m e 0 χ).mapsTo_toFun
  mapsTo_invFun := (actual_zeroSection_localEquiv m e 0 χ).mapsTo_invFun
  left_inv := (actual_zeroSection_localEquiv m e 0 χ).left_inv
  right_inv := (actual_zeroSection_localEquiv m e 0 χ).right_inv

private theorem product_zero (m e : ℕ)
    (χ : LocalHolomorphicEquivAt (n := m) (0 : ComplexModel m))
    (hχ0 : χ.toFun 0 = 0) : (productAtZero m e χ).toFun 0 = 0 := by
  change tangentInclusion m e (χ.toFun (tangentProjection m e 0)) +
    (0 - tangentInclusion m e (tangentProjection m e 0)) = 0
  simp only [map_zero, hχ0, sub_self, add_zero]

private theorem inverse_product_formula (m e : ℕ)
    (χ : LocalHolomorphicEquivAt (n := m) (0 : ComplexModel m))
    (z : ComplexModel (m+e)) :
    (productAtZero m e χ).invFun z =
      tangentInclusion m e (χ.invFun (tangentProjection m e z)) +
        (z - tangentInclusion m e (tangentProjection m e z)) := rfl

/-- The germ automorphism is inverse-map pullback, so its numerator is
literally F composed with the SAME product inverse. -/
def actualFreeProductGermEquiv (m e : ℕ)
    (χ : LocalHolomorphicEquivAt (n := m) (0 : ComplexModel m))
    (hχ0 : χ.toFun 0 = 0) :
    HolGerm (ComplexModel (m+e)) ≃ₐ[ℂ] HolGerm (ComplexModel (m+e)) :=
  (localGermAlgEquiv (productAtZero m e χ) (product_zero m e χ hχ0)).symm

private theorem inverse_product_mk (m e : ℕ)
    (χ : LocalHolomorphicEquivAt (n := m) (0 : ComplexModel m))
    (hχ0 : χ.toFun 0 = 0) (f : ComplexModel (m+e) → ℂ) (hf : HolAt f 0) :
    actualFreeProductGermEquiv m e χ hχ0 (HolGerm.mk f hf) =
      HolGerm.mk (f ∘ (productAtZero m e χ).invFun)
        (holomorphic_comp (productAtZero m e χ).invFun
          (local_invFun_holomorphic (productAtZero m e χ) (product_zero m e χ hχ0))
          (local_invFun_zero (productAtZero m e χ) (product_zero m e χ hχ0)) hf) := rfl

private theorem inverse_product_coordinate (m e : ℕ)
    (χ : LocalHolomorphicEquivAt (n := m) (0 : ComplexModel m))
    (z : ComplexModel (m+e)) (i : Fin (m+e)) (hi : m ≤ i.val) :
    (productAtZero m e χ).invFun z i = z i := by
  let j : Fin e := ⟨i.val-m, by omega⟩
  have hij : i = j.natAdd m := Fin.ext (by dsimp [j]; omega)
  rw [hij, inverse_product_formula]
  simp only [PiLp.add_apply, PiLp.sub_apply, tangentInclusion_normal,
    zero_add, sub_zero]

private theorem projection_essential_section (m e : ℕ) (z : ComplexModel (m+e)) :
    tangentProjection m e
      (actualBlockCoordinateProjection {i : Fin (m+e) | m ≤ i.val} z) = 0 := by
  ext i
  rw [tangentProjection_apply, actualBlockCoordinateProjection_apply]
  simp only [mem_ofPred_eq, Fin.val_castAdd, not_le.mpr i.isLt, if_false, PiLp.zero_apply]

private theorem inverse_product_section (m e : ℕ)
    (χ : LocalHolomorphicEquivAt (n := m) (0 : ComplexModel m))
    (hχ0 : χ.toFun 0 = 0) (z : ComplexModel (m+e)) :
    (productAtZero m e χ).invFun
        (actualBlockCoordinateProjection {i : Fin (m+e) | m ≤ i.val} z) =
      actualBlockCoordinateProjection {i : Fin (m+e) | m ≤ i.val} z := by
  rw [inverse_product_formula, projection_essential_section,
    local_invFun_zero χ hχ0, map_zero, sub_zero, zero_add]

/-- The SAME inverse product fixes every essential coordinate and restricts
to the identity on the WHOLE essential section for EVERY analytic germ. -/
theorem actualFreeProductGermEquiv_section_coordinates (m e : ℕ)
    (χ : LocalHolomorphicEquivAt (n := m) (0 : ComplexModel m))
    (hχ0 : χ.toFun 0 = 0) :
    (∀ i : Fin (m+e), m ≤ i.val →
      actualFreeProductGermEquiv m e χ hχ0 (coordinateGerm i) = coordinateGerm i) ∧
    (∀ F : HolGerm (ComplexModel (m+e)),
      actualBlockProjectionGermHom {i : Fin (m+e) | m ≤ i.val}
          (actualFreeProductGermEquiv m e χ hχ0 F) =
        actualBlockProjectionGermHom {i : Fin (m+e) | m ≤ i.val} F) := by
  constructor
  · intro i hi
    unfold coordinateGerm
    rw [inverse_product_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => inverse_product_coordinate m e χ z i hi
  · intro F
    induction F using HolGerm.induction_on with
    | h f hf =>
      rw [inverse_product_mk]
      unfold actualBlockProjectionGermHom
      rw [compAlgHom_mk, compAlgHom_mk]
      apply HolGerm.mk_eq_mk_iff.mpr
      exact Eventually.of_forall fun z => congrArg f (inverse_product_section m e χ hχ0 z)

private theorem projection_essential_vector (m e : ℕ) (i : Fin (m+e))
    (hi : m ≤ i.val) :
    tangentProjection m e (EuclideanSpace.single i (1 : ℂ)) = 0 := by
  ext j
  have hne : j.castAdd e ≠ i := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castAdd] at this
    omega
  simp only [tangentProjection_apply, PiLp.single_apply,
    if_neg hne, PiLp.zero_apply]

private theorem inverse_product_add_essential (m e : ℕ)
    (χ : LocalHolomorphicEquivAt (n := m) (0 : ComplexModel m))
    (i : Fin (m+e)) (hi : m ≤ i.val) (z : ComplexModel (m+e)) (t : ℂ) :
    (productAtZero m e χ).invFun (z + t • EuclideanSpace.single i 1) =
      (productAtZero m e χ).invFun z + t • EuclideanSpace.single i 1 := by
  rw [inverse_product_formula, inverse_product_formula,
    map_add, map_smul, projection_essential_vector m e i hi, smul_zero, add_zero]
  abel

private theorem inverse_product_word_derivative (m e : ℕ)
    (χ : LocalHolomorphicEquivAt (n := m) (0 : ComplexModel m))
    (hχ0 : χ.toFun 0 = 0) (L : List (Fin (m+e)))
    (hL : ∀ i ∈ L, m ≤ i.val) (F : HolGerm (ComplexModel (m+e))) :
    actualAnalyticWordDerivative L (actualFreeProductGermEquiv m e χ hχ0 F) =
      actualFreeProductGermEquiv m e χ hχ0 (actualAnalyticWordDerivative L F) := by
  induction F using HolGerm.induction_on with
  | h f hf =>
    change iteratedDerivativeGerm (L.map (fun i => EuclideanSpace.single i 1))
      (actualFreeProductGermEquiv m e χ hχ0 (HolGerm.mk f hf)) =
      actualFreeProductGermEquiv m e χ hχ0
        (iteratedDerivativeGerm (L.map (fun i => EuclideanSpace.single i 1)) (HolGerm.mk f hf))
    rw [inverse_product_mk, iteratedDerivativeGerm_mk,
      iteratedDerivativeGerm_mk, inverse_product_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    obtain ⟨V, hVf, hVo, h0V⟩ := eventually_nhds_iff.mp hf
    let P := productAtZero m e χ
    let Ψ := P.invFun
    let U := P.target ∩ Ψ ⁻¹' V
    have hU : IsOpen U :=
      P.invFun_holomorphic.continuousOn.isOpen_inter_preimage P.isOpen_target hVo
    have h0target : (0 : ComplexModel (m+e)) ∈ P.target := by
      have ht := P.mapsTo_toFun P.center_mem_source
      simpa only [P, product_zero m e χ hχ0] using ht
    have h0U : (0 : ComplexModel (m+e)) ∈ U := by
      refine ⟨h0target, ?_⟩
      change P.invFun 0 ∈ V
      rwa [local_invFun_zero P (product_zero m e χ hχ0)]
    have hΨ : DifferentiableOn ℂ Ψ U := P.invFun_holomorphic.mono inter_subset_left
    have hUV : MapsTo Ψ U V := fun _ hz => hz.2
    have hfV : DifferentiableOn ℂ f V := fun z hz => (hVf z hz).differentiableWithinAt
    filter_upwards [hU.mem_nhds h0U] with z hz
    exact NormalDerivativeMonomial.iterDeriv_comp_translate hU hVo hΨ hUV hfV L
      (fun i hi z t => inverse_product_add_essential m e χ i (hL i hi) z t) z hz

/-- All genuine analytic multi-derivatives supported in the essential block
commute with WHOLE inverse product pullback. -/
theorem actualFreeProductGermEquiv_multiDerivative (m e : ℕ)
    (χ : LocalHolomorphicEquivAt (n := m) (0 : ComplexModel m))
    (hχ0 : χ.toFun 0 = 0) (β : Fin (m+e) →₀ ℕ)
    (hβ : ∀ i : Fin (m+e), ¬ m ≤ i.val → β i = 0)
    (F : HolGerm (ComplexModel (m+e))) :
    actualAnalyticMultiDerivative β (actualFreeProductGermEquiv m e χ hχ0 F) =
      actualFreeProductGermEquiv m e χ hχ0 (actualAnalyticMultiDerivative β F) := by
  apply inverse_product_word_derivative m e χ hχ0 (actualCoordinateDerivativeWord β)
  intro i hi
  by_contra hiB
  have him : i ∈ β.toMultiset := by simpa [actualCoordinateDerivativeWord] using hi
  have hne := Finsupp.mem_support_iff.mp ((Finsupp.mem_toMultiset β i).mp him)
  exact hne (hβ i hiB)

/-- Every whole coordinate ideal generated inside the essential block is
preserved by the SAME genuine inverse-map germ equivalence. -/
theorem actualFreeProductGermEquiv_map_coordinateIdeal (m e : ℕ)
    (χ : LocalHolomorphicEquivAt (n := m) (0 : ComplexModel m))
    (hχ0 : χ.toFun 0 = 0) (T : Set (Fin (m+e)))
    (hT : ∀ i ∈ T, m ≤ i.val) :
    Ideal.map (actualFreeProductGermEquiv m e χ hχ0).toRingEquiv.toRingHom
      (actualAnalyticCoordinateBlockIdeal T) = actualAnalyticCoordinateBlockIdeal T := by
  have hcoord := (actualFreeProductGermEquiv_section_coordinates m e χ hχ0).1
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro f ⟨i, hi, rfl⟩
    change actualFreeProductGermEquiv m e χ hχ0 (coordinateGerm i) ∈
      actualAnalyticCoordinateBlockIdeal T
    rw [hcoord i (hT i hi)]
    exact Ideal.subset_span ⟨i, hi, rfl⟩
  · apply Ideal.span_le.mpr
    rintro f ⟨i, hi, rfl⟩
    have h := Ideal.mem_map_of_mem (actualFreeProductGermEquiv m e χ hχ0).toRingEquiv.toRingHom
      (show coordinateGerm i ∈ actualAnalyticCoordinateBlockIdeal T from
        Ideal.subset_span ⟨i, hi, rfl⟩)
    change actualFreeProductGermEquiv m e χ hχ0 (coordinateGerm i) ∈ _ at h
    rwa [hcoord i (hT i hi)] at h

end
end Hironaka.HironakaActualFreeProductGermTransport
