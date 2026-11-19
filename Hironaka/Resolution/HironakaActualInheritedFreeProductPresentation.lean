import Hironaka.Resolution.HironakaActualFreeProductGermTransport
import Hironaka.Resolution.HironakaActualInheritedSourcePermutationFamily
import Hironaka.Resolution.HironakaActualUnshiftedInitialHSTransfer
import Hironaka.Resolution.HironakaActualRelativeStandardnessPointLeadingDiagram
import Hironaka.Resolution.HironakaSmoothCentreRealDomainActualAmbientHS

/-! SAME pure-essential heads and whole inherited presentations through an
actual inverse product pullback. Whole target diagrams are produced from
retained member heads and genuine ORIGIN quotient HS, never assumed.
Historical selectors are cast only along the internally proved literal
vertex-set equality. No nearby diagram or phase assertion is made.
Blueprint: the fourth node of the free-product-flattening extension. -/
set_option autoImplicit false
open Set Classical
open scoped Topology

namespace Hironaka.HironakaActualInheritedFreeProductPresentation
noncomputable section
open HolGerm HironakaRelativeNormalMonomialBasis HironakaHolomorphicPointJets
  HironakaActualCoefficientPresentationCentrePower HironakaActualOriginalFormalTaylor
  HironakaActualOriginalFormalHSTransfer HironakaActualUnshiftedInitialHSTransfer
  HironakaActualCauchyCoefficientLimits HironakaActualFormalInitialDiagram
  HironakaActualReducedBasisDivision HironakaActualRelativeNormalJetDivision
  HironakaActualInheritedAnalyticBlockJacobian HironakaActualCanonicalBlockJacobian
  HironakaActualInheritedNestedContactFlag HironakaActualAnalyticBlockGraphTranslation
  HironakaActualAnalyticFormalNormalPowers
  HironakaActualFixedInheritedSelector HironakaActualInheritedSourcePermutationFamily
  HironakaActualInheritedCurrentSourceRelabel HironakaActualFreeProductGermTransport
  HironakaActualRelativeStandardnessPointLeadingDiagram
  HironakaSmoothCentreRealDomainActualAmbientHS

private theorem unshifted_property (n : ℕ)
    (P : (r : ℕ) → (HolGerm (ComplexModel r) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) → Prop)
    (h : P (0+n) (originalTaylorAlgHom n)) : P n (actualUnshiftedTaylorAlgHom n) := by
  have hc {r : ℕ} (hr : r=n)
      (f : HolGerm (ComplexModel r) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) (hf : P r f) :
      P n (cast (congrArg (fun j => HolGerm (ComplexModel j) →ₐ[ℂ]
        MvPowerSeries (Fin n) ℂ) hr) f) := by
    subst r
    exact hf
  exact hc (Nat.zero_add n) (originalTaylorAlgHom n) h

private theorem unshifted_maximal_power_iff (n q : ℕ) (F : HolGerm (ComplexModel n)) :
    F ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q ↔
      ∀ a : Fin n →₀ ℕ, normalExponentDegree a < q →
        MvPowerSeries.coeff a (actualUnshiftedTaylorAlgHom n F) = 0 := by
  let P (r : ℕ) (f : HolGerm (ComplexModel r) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) : Prop :=
    ∀ g : HolGerm (ComplexModel r),
      g ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel r)) ^ q ↔
        ∀ a : Fin n →₀ ℕ, normalExponentDegree a < q → MvPowerSeries.coeff a (f g) = 0
  exact unshifted_property n P (mem_original_maximal_pow_iff_formal_coefficients_zero n q) F

private theorem taylor_block_projection {n : ℕ} (B : Set (Fin n))
    (F : HolGerm (ComplexModel n)) :
    actualUnshiftedTaylorAlgHom n (actualBlockProjectionGermHom B F) =
      actualFormalBlockCoordinateProjection B (actualUnshiftedTaylorAlgHom n F) :=
  DFunLike.congr_fun (actualTaylor_blockProjection B) F

private theorem pure_coefficient (m e : ℕ)
    (χ : LocalHolomorphicEquivAt (n := m) (0 : ComplexModel m)) (hχ0 : χ.toFun 0 = 0)
    (F : HolGerm (ComplexModel (m+e))) (a : Fin (m+e) →₀ ℕ)
    (ha : ∀ i : Fin (m+e), ¬ m ≤ i.val → a i = 0) :
    MvPowerSeries.coeff a (actualUnshiftedTaylorAlgHom (m+e)
      (actualFreeProductGermEquiv m e χ hχ0 F)) =
      MvPowerSeries.coeff a (actualUnshiftedTaylorAlgHom (m+e) F) := by
  have hs := (actualFreeProductGermEquiv_section_coordinates m e χ hχ0).2 F
  have ht := congrArg (actualUnshiftedTaylorAlgHom (m+e)) hs
  rw [taylor_block_projection, taylor_block_projection] at ht
  have hc := congrArg (MvPowerSeries.coeff a) ht
  rw [coeff_actualFormalBlockCoordinateProjection,
    coeff_actualFormalBlockCoordinateProjection] at hc
  simpa only [mem_ofPred_eq, if_pos ha] using hc

private theorem product_eval (m e : ℕ)
    (χ : LocalHolomorphicEquivAt (n := m) (0 : ComplexModel m)) (hχ0 : χ.toFun 0 = 0)
    (F : HolGerm (ComplexModel (m+e))) :
    HolGerm.eval (actualFreeProductGermEquiv m e χ hχ0 F) = HolGerm.eval F := by
  rw [← actualTaylor_coeff_zero, ← actualTaylor_coeff_zero]
  exact pure_coefficient m e χ hχ0 F 0 (fun _ _ => rfl)

private theorem maximal_power_map {n : ℕ}
    (E : HolGerm (ComplexModel n) ≃ₐ[ℂ] HolGerm (ComplexModel n)) (q : ℕ)
    (F : HolGerm (ComplexModel n))
    (hF : F ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q) :
    E F ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q := by
  have hm := Ideal.mem_map_of_mem E.toRingEquiv.toRingHom hF
  have hmap : Ideal.map E.toRingEquiv.toRingHom
      (IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q) =
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q := by
    rw [Ideal.map_pow]
    exact congrArg (fun J : Ideal (HolGerm (ComplexModel n)) => J ^ q)
      (IsLocalRing.map_ringEquiv_maximalIdeal E.toRingEquiv)
  change E F ∈ _ at hm
  rwa [hmap] at hm

/-- A SAME pure-essential monic head is retained by the true inverse product
map. The source ordinary power and every target coefficient condition are
produced internally; no target order, head or diagram premise is supplied. -/
theorem actualFreeProduct_same_member_monic (m e : ℕ)
    (χ : LocalHolomorphicEquivAt (n := m) (0 : ComplexModel m)) (hχ0 : χ.toFun 0 = 0)
    (F : HolGerm (ComplexModel (m+e))) (a : Fin (m+e) →₀ ℕ)
    (ha : ∀ i : Fin (m+e), ¬ m ≤ i.val → a i = 0)
    (hc : MvPowerSeries.coeff a (actualUnshiftedTaylorAlgHom (m+e) F) = 1)
    (hlower : ∀ β, MonomialOrder.degLex.toSyn β < MonomialOrder.degLex.toSyn a →
      MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom (m+e) F) = 0) :
    MvPowerSeries.coeff a (actualUnshiftedTaylorAlgHom (m+e)
      (actualFreeProductGermEquiv m e χ hχ0 F)) = 1 ∧
      ∀ β, MonomialOrder.degLex.toSyn β < MonomialOrder.degLex.toSyn a →
        MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom (m+e)
          (actualFreeProductGermEquiv m e χ hχ0 F)) = 0 := by
  have hp : F ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (m+e))) ^ normalExponentDegree a := by
    apply (unshifted_maximal_power_iff (m+e) (normalExponentDegree a) F).mpr
    intro β hβ
    apply hlower β
    apply MonomialOrder.degLex_lt_iff.mpr
    apply Finsupp.DegLex.lt_iff.mpr
    left
    simpa only [ofDegLex_toDegLex, normalExponentDegree, ← Finsupp.degree_eq_sum] using hβ
  have hEp := maximal_power_map (actualFreeProductGermEquiv m e χ hχ0)
    (normalExponentDegree a) F hp
  refine ⟨(pure_coefficient m e χ hχ0 F a ha).trans hc, ?_⟩
  intro β hβ
  rcases Finsupp.DegLex.lt_iff.mp (MonomialOrder.degLex_lt_iff.mp hβ) with hd | ⟨_hd, hlex⟩
  · apply (unshifted_maximal_power_iff (m+e) (normalExponentDegree a) _).mp hEp β
    simpa only [ofDegLex_toDegLex, normalExponentDegree, ← Finsupp.degree_eq_sum] using hd
  · obtain ⟨j, hbefore, hj⟩ := Finsupp.Lex.lt_iff.mp hlex
    simp only [ofDegLex_toDegLex, ofLex_toLex] at hbefore hj
    have hjB : m ≤ j.val := by
      by_contra hjB
      rw [ha j hjB] at hj
      omega
    have hβB (i : Fin (m+e)) (hi : ¬ m ≤ i.val) : β i = 0 := by
      have hij : i < j := Fin.lt_def.mpr (by omega)
      exact (hbefore i hij).trans (ha i hi)
    rw [pure_coefficient m e χ hχ0 F β hβB]
    exact hlower β hβ

private theorem product_cone (m e : ℕ)
    (χ : LocalHolomorphicEquivAt (n := m) (0 : ComplexModel m)) (hχ0 : χ.toFun 0 = 0)
    (b : Fin (m+e) →₀ ℕ) (hb : ∀ i : Fin (m+e), ¬ m ≤ i.val → b i = 0)
    (F : HolGerm (ComplexModel (m+e)))
    (hz : ∀ α, b ≤ α → MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom (m+e) F) = 0) :
    ∀ α, b ≤ α → MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom (m+e)
      (actualFreeProductGermEquiv m e χ hχ0 F)) = 0 := by
  apply (actualAnalyticMultiDerivative_eq_zero_iff_cone b _).mp
  rw [actualFreeProductGermEquiv_multiDerivative m e χ hχ0 b hb,
    (actualAnalyticMultiDerivative_eq_zero_iff_cone b F).mpr hz, map_zero]

private theorem analytic_single {n : ℕ} (i : Fin n) (F : HolGerm (ComplexModel n)) :
    actualAnalyticMultiDerivative (Finsupp.single i 1) F = actualAnalyticCoordinateDerivative i F := by
  apply actualUnshiftedTaylorAlgHom_injective n
  rw [actualTaylor_actualAnalyticMultiDerivative, actualTaylor_actualAnalyticCoordinateDerivative]
  simpa only [zero_add, actualFormalMultiDerivative_zero] using
    actualFormalMultiDerivative_add_single 0 i (actualUnshiftedTaylorAlgHom n F)

private theorem product_partial (m e : ℕ)
    (χ : LocalHolomorphicEquivAt (n := m) (0 : ComplexModel m)) (hχ0 : χ.toFun 0 = 0)
    (i : Fin (m+e)) (hi : m ≤ i.val) (F : HolGerm (ComplexModel (m+e))) :
    actualAnalyticCoordinateDerivative i (actualFreeProductGermEquiv m e χ hχ0 F) =
      actualFreeProductGermEquiv m e χ hχ0 (actualAnalyticCoordinateDerivative i F) := by
  have hb (j : Fin (m+e)) (hj : ¬ m ≤ j.val) : (Finsupp.single i 1 : Fin (m+e) →₀ ℕ) j = 0 := by
    have hji : j ≠ i := by intro h; subst j; exact hj hi
    exact Finsupp.single_eq_of_ne hji
  have h := actualFreeProductGermEquiv_multiDerivative m e χ hχ0 (Finsupp.single i 1) hb F
  rwa [analytic_single, analytic_single] at h

private theorem selector_beta_pure {n m : ℕ} {V : Finset (Fin n →₀ ℕ)}
    (hpure : ∀ a : V, ∀ i : Fin n, ¬ m ≤ i.val → a.val i = 0)
    (S : ActualFixedInheritedSelector V) (j : fixedSelectorEssential V)
    (i : Fin n) (hi : ¬ m ≤ i.val) : fixedSelectorBeta S j i = 0 := by
  simp only [fixedSelectorBeta, Finsupp.tsub_apply, hpure (S.selected j) i hi, zero_tsub]

private theorem selector_block_pure {n m : ℕ} {V : Finset (Fin n →₀ ℕ)}
    (hpure : ∀ a : V, ∀ i : Fin n, ¬ m ≤ i.val → a.val i = 0)
    (k : ℕ) (i : Fin n) (hi : i ∈ fixedSelectorBlock V k) : m ≤ i.val := by
  obtain ⟨a, _ha, hai⟩ := hi
  by_contra h
  exact hai (hpure a i h)

private theorem selector_derivative_product (m e : ℕ)
    (χ : LocalHolomorphicEquivAt (n := m) (0 : ComplexModel m)) (hχ0 : χ.toFun 0 = 0)
    {V : Finset (Fin (m+e) →₀ ℕ)}
    (hpure : ∀ a : V, ∀ i : Fin (m+e), ¬ m ≤ i.val → a.val i = 0)
    (S : ActualFixedInheritedSelector V) (G : V → HolGerm (ComplexModel (m+e)))
    (j : fixedSelectorEssential V) :
    actualFixedSelectorDerivative S (fun a => actualFreeProductGermEquiv m e χ hχ0 (G a)) j =
      actualFreeProductGermEquiv m e χ hχ0 (actualFixedSelectorDerivative S G j) :=
  actualFreeProductGermEquiv_multiDerivative m e χ hχ0 (fixedSelectorBeta S j)
    (selector_beta_pure hpure S j) (G (S.selected j))

private theorem selector_contact_product (m e : ℕ)
    (χ : LocalHolomorphicEquivAt (n := m) (0 : ComplexModel m)) (hχ0 : χ.toFun 0 = 0)
    {V : Finset (Fin (m+e) →₀ ℕ)}
    (hpure : ∀ a : V, ∀ i : Fin (m+e), ¬ m ≤ i.val → a.val i = 0)
    (S : ActualFixedInheritedSelector V) (G : V → HolGerm (ComplexModel (m+e)))
    (k : ℕ) (hcontact : actualFixedSelectorContactAt S G k) :
    actualFixedSelectorContactAt S (fun a => actualFreeProductGermEquiv m e χ hχ0 (G a)) k := by
  intro j
  rw [selector_derivative_product m e χ hχ0 hpure S G]
  have hm := Ideal.mem_map_of_mem (actualFreeProductGermEquiv m e χ hχ0).toRingEquiv.toRingHom
    (hcontact j)
  rw [actualFreeProductGermEquiv_map_coordinateIdeal m e χ hχ0
    (fixedSelectorBlock V k) (selector_block_pure hpure k)] at hm
  exact hm

private theorem selector_jacobian_product (m e : ℕ)
    (χ : LocalHolomorphicEquivAt (n := m) (0 : ComplexModel m)) (hχ0 : χ.toFun 0 = 0)
    {V : Finset (Fin (m+e) →₀ ℕ)}
    (hpure : ∀ a : V, ∀ i : Fin (m+e), ¬ m ≤ i.val → a.val i = 0)
    (S : ActualFixedInheritedSelector V) (G : V → HolGerm (ComplexModel (m+e))) (k : ℕ) :
    actualFixedSelectorJacobian S (fun a => actualFreeProductGermEquiv m e χ hχ0 (G a)) k =
      actualFixedSelectorJacobian S G k := by
  ext j i
  change HolGerm.eval (actualAnalyticCoordinateDerivative i.val
    (actualFixedSelectorDerivative S (fun a => actualFreeProductGermEquiv m e χ hχ0 (G a))
      (fixedSelectorBlockEssential k j))) = _
  rw [selector_derivative_product m e χ hχ0 hpure S G,
    product_partial m e χ hχ0 i.val (selector_block_pure hpure k i.val i.property),
    product_eval]
  rfl

private theorem vertex_cast_val {n : ℕ} {V W : Finset (Fin n →₀ ℕ)}
    (h : V = W) (a : V) : (sourceVertexSetCast h a).val = a.val := by
  cases h
  rfl

private theorem cast_range {n : ℕ} {V W : Finset (Fin n →₀ ℕ)}
    (h : V = W) (G : V → HolGerm (ComplexModel n)) :
    Set.range (sourceRawFamilyCast h G) = Set.range G := by
  cases h
  rfl

/-- Genuine SOURCE membership, SAME pure-essential heads and the actual origin
local-ring equivalence produce the WHOLE target diagram and a CURRENT family.
Every historical selector is transported along the internally proved literal
vertex equality; all old whole prefixes, contacts and actual Jacobians survive. -/
theorem actualFreeProduct_same_family_initialDiagram {m e : ℕ}
    (χ : LocalHolomorphicEquivAt (n := m) (0 : ComplexModel m)) (hχ0 : χ.toFun 0 = 0)
    (K : Ideal (MvPowerSeries (Fin (m+e)) ℂ))
    (G : ActualAnalyticInheritedFamily (m+e) 0 K)
    (hmem : ∀ a, actualUnshiftedTaylorAlgHom (m+e) (G.germs a) ∈ K)
    (hpure : ∀ a : actualInitialVertices MonomialOrder.degLex K,
      ∀ i : Fin (m+e), ¬ m ≤ i.val → a.val i = 0) :
    let E := actualFreeProductGermEquiv m e χ hχ0
    let I := Ideal.span (Set.range G.germs)
    let K' := actualInheritedCurrentSourceIdeal (Ideal.map E.toRingEquiv.toRingHom I)
    actualInitialDiagram MonomialOrder.degLex K' = actualInitialDiagram MonomialOrder.degLex K ∧
      ∃ hV : actualInitialVertices MonomialOrder.degLex K =
          actualInitialVertices MonomialOrder.degLex K',
      ∃ G' : ActualAnalyticInheritedFamily (m+e) 0 K',
        (∀ a, G'.germs (sourceVertexSetCast hV a) = E (G.germs a)) ∧
        Ideal.span (Set.range G'.germs) = Ideal.map E.toRingEquiv.toRingHom I ∧
        (∀ a, actualUnshiftedTaylorAlgHom (m+e) (G'.germs a) ∈ K') ∧
        (∀ k, ActualInheritedPrefixReducedAt G k → ActualInheritedPrefixReducedAt G' k) ∧
        ∀ S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex K),
          (∀ k, actualFixedSelectorContactAt S G.germs k →
            actualFixedSelectorContactAt (sourceFixedSelectorCast hV S) G'.germs k) ∧
          ∀ k, (actualFixedSelectorJacobian (sourceFixedSelectorCast hV S) G'.germs k).submatrix
            (sourceBlockCast hV k) (sourceBlockCast hV k) = actualFixedSelectorJacobian S G.germs k := by
  let E := actualFreeProductGermEquiv m e χ hχ0
  let I := Ideal.span (Set.range G.germs)
  let J := Ideal.map E.toRingEquiv.toRingHom I
  let K' := actualInheritedCurrentSourceIdeal J
  have hsource : actualInheritedCurrentSourceIdeal I = K := by
    have hgen := family_formal_ideal_eq_span_vertex_series MonomialOrder.degLex K
      (actualSourceFormalFamily G hmem)
    rw [actualInheritedCurrentSourceIdeal, Ideal.map_span, ← Set.range_comp]
    exact hgen.symm
  have hheads (a : actualInitialVertices MonomialOrder.degLex K) :=
    actualFreeProduct_same_member_monic m e χ hχ0 (G.germs a) a.val (hpure a)
      (G.monic a) (G.lower a)
  have htarget (a : actualInitialVertices MonomialOrder.degLex K) :
      actualUnshiftedTaylorAlgHom (m+e) (E (G.germs a)) ∈ K' := by
    apply Ideal.mem_map_of_mem (actualUnshiftedTaylorAlgHom (m+e)).toRingHom
    exact Ideal.mem_map_of_mem E.toRingEquiv.toRingHom
      (Ideal.subset_span ⟨a, rfl⟩)
  have hinc : actualInitialDiagram MonomialOrder.degLex K ⊆ actualInitialDiagram MonomialOrder.degLex K' := by
    intro α hα
    obtain ⟨a, ha, hle⟩ := (mem_actualInitialDiagram_iff_vertex_le MonomialOrder.degLex K α).mp hα
    let v : actualInitialVertices MonomialOrder.degLex K := ⟨a, ha⟩
    let F := actualUnshiftedTaylorAlgHom (m+e) (E (G.germs v))
    have hne : F ≠ 0 := by
      intro hz
      have hc := (hheads v).1
      change MvPowerSeries.coeff v.val F = 1 at hc
      rw [hz, map_zero] at hc
      exact zero_ne_one hc
    have hhead : actualInitialExponent MonomialOrder.degLex F hne = a :=
      actualInitialExponent_eq_of_coefficients MonomialOrder.degLex F hne a
        (by rw [(hheads v).1]; exact one_ne_zero) (hheads v).2
    exact actualInitialDiagram_upper MonomialOrder.degLex K' a α
      ⟨F, htarget v, hne, hhead⟩ hle
  have hHS (ℓ : ℕ) : genuineFormalHilbertSamuelValue (m+e) K' ℓ =
      genuineFormalHilbertSamuelValue (m+e) K ℓ := by
    calc
      genuineFormalHilbertSamuelValue (m+e) K' ℓ = hilbertSamuelValue J ℓ :=
        (hilbertSamuelValue_eq_actual_unshifted_formal_extension (m+e) J ℓ).symm
      _ = hilbertSamuelValue I ℓ := actualAmbientHS_eq_of_genuineAlgEquiv E I ℓ
      _ = genuineFormalHilbertSamuelValue (m+e) (actualInheritedCurrentSourceIdeal I) ℓ :=
        hilbertSamuelValue_eq_actual_unshifted_formal_extension (m+e) I ℓ
      _ = genuineFormalHilbertSamuelValue (m+e) K ℓ := by rw [hsource]
  have hD : actualInitialDiagram MonomialOrder.degLex K' = actualInitialDiagram MonomialOrder.degLex K :=
    actualInitialDiagram_eq_of_subset_of_hs_eq K K' hinc hHS
  let hV := actualInitialVertices_eq_of_diagram_eq hD.symm
  let H : actualInitialVertices MonomialOrder.degLex K → HolGerm (ComplexModel (m+e)) :=
    fun a => E (G.germs a)
  let G' : ActualAnalyticInheritedFamily (m+e) 0 K' :=
    { germs := sourceRawFamilyCast hV H
      monic := by
        intro a
        obtain ⟨a, rfl⟩ := (sourceVertexSetCast hV).surjective a
        rw [sourceRawFamilyCast_apply]
        simpa only [vertex_cast_val, H, E, Nat.add_zero] using (hheads a).1
      lower := by
        intro a β hβ
        obtain ⟨a, rfl⟩ := (sourceVertexSetCast hV).surjective a
        rw [sourceRawFamilyCast_apply]
        apply (hheads a).2 β
        simpa only [vertex_cast_val] using hβ }
  have hliteral (a : actualInitialVertices MonomialOrder.degLex K) :
      G'.germs (sourceVertexSetCast hV a) = E (G.germs a) :=
    sourceRawFamilyCast_apply hV H a
  have hspan : Ideal.span (Set.range G'.germs) = J := by
    change Ideal.span (Set.range (sourceRawFamilyCast hV H)) =
      Ideal.map E.toRingEquiv.toRingHom (Ideal.span (Set.range G.germs))
    rw [cast_range, Ideal.map_span, ← Set.range_comp]
    rfl
  refine ⟨hD, hV, G', hliteral, hspan, ?_, ?_, ?_⟩
  · intro a
    obtain ⟨a, rfl⟩ := (sourceVertexSetCast hV).surjective a
    rw [hliteral]
    exact htarget a
  · intro k hred a ha b hb α hbα
    obtain ⟨a, rfl⟩ := (sourceVertexSetCast hV).surjective a
    obtain ⟨b, rfl⟩ := (sourceVertexSetCast hV).surjective b
    have ha0 : k < normalExponentDegree a.val := by simpa only [vertex_cast_val] using ha
    have hb0 : normalExponentDegree b.val ≤ k := by simpa only [vertex_cast_val] using hb
    have hbα0 : b.val ≤ α := by simpa only [vertex_cast_val] using hbα
    rw [hliteral]
    exact product_cone m e χ hχ0 b.val (hpure b) (G.germs a)
      (hred a ha0 b hb0) α hbα0
  · intro S
    constructor
    · intro k hcontact
      change actualFixedSelectorContactAt (sourceFixedSelectorCast hV S)
        (sourceRawFamilyCast hV H) k
      apply (sourceFixedSelectorCast_contact hV S H k).mpr
      exact selector_contact_product m e χ hχ0 hpure S G.germs k hcontact
    · intro k
      change (actualFixedSelectorJacobian (sourceFixedSelectorCast hV S)
        (sourceRawFamilyCast hV H) k).submatrix (sourceBlockCast hV k) (sourceBlockCast hV k) = _
      rw [sourceFixedSelectorCast_jacobian]
      exact selector_jacobian_product m e χ hχ0 hpure S G.germs k

end
end Hironaka.HironakaActualInheritedFreeProductPresentation
