import Hironaka.Resolution.HironakaActualInheritedSourceOwnerPermutation
import Hironaka.Resolution.HironakaActualInheritedCurrentSourceRelabel

/-! Genuine CURRENT labels and SAME raw analytic family after a source
permutation whose member heads have been proved. No fresh selector is chosen. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualInheritedSourcePermutationFamily
noncomputable section
attribute [local instance] Classical.propDecidable
open HolGerm HironakaRelativeNormalMonomialBasis HironakaActualFormalInitialDiagram
  HironakaActualInheritedSourceOwnerPermutation HironakaActualFixedInheritedSelector
  HironakaActualFixedInheritedSelectorPermutation HironakaActualInheritedAnalyticBlockJacobian
  HironakaActualInheritedNestedContactFlag HironakaActualReducedBasisDivision
  HironakaActualInheritedCurrentSourceRelabel HironakaActualRelativeNormalJetDivision
  HironakaActualCoefficientPresentationCentrePower
variable {n : ℕ} {K : Ideal (MvPowerSeries (Fin n) ℂ)}

def actualSourceFormalFamily (G : ActualAnalyticInheritedFamily n 0 K)
    (hmem : ∀ a, actualUnshiftedTaylorAlgHom n (G.germs a) ∈ K) :
    ActualMonicVertexFamily MonomialOrder.degLex K where
  series a := actualUnshiftedTaylorAlgHom n (G.germs a)
  mem := hmem
  monic := G.monic
  lower := G.lower

private theorem minimal_permuted_iff (p : Fin n ≃ Fin n)
    (D : Set (Fin n →₀ ℕ)) (α : Fin n →₀ ℕ) :
    Minimal (· ∈ Finsupp.domCongr p '' D) (Finsupp.domCongr p α) ↔ Minimal (· ∈ D) α := by
  constructor
  · intro h
    have hα : α ∈ D := by
      obtain ⟨β, hβ, he⟩ := h.prop
      exact (Finsupp.domCongr p).injective he ▸ hβ
    refine ⟨hα, ?_⟩
    intro β hβ hβα
    exact (sourceExponentPermutation_le_iff p α β).mp
      (h.2 ⟨β, hβ, rfl⟩ ((sourceExponentPermutation_le_iff p β α).mpr hβα))
  · intro h
    refine ⟨⟨α, h.prop, rfl⟩, ?_⟩
    rintro γ ⟨β, hβ, rfl⟩ hβα
    exact (sourceExponentPermutation_le_iff p α β).mpr
      (h.2 hβ ((sourceExponentPermutation_le_iff p β α).mp hβα))

/-- Exact finite-set identity from WHOLE diagram minimality, not a cardinality certificate. -/
theorem actualSourcePermutationVertices_eq
    (G : ActualAnalyticInheritedFamily n 0 K)
    (hmem : ∀ a, actualUnshiftedTaylorAlgHom n (G.germs a) ∈ K) (p : Fin n ≃ Fin n)
    (hlower : ∀ a γ, MonomialOrder.degLex.toSyn γ <
        MonomialOrder.degLex.toSyn (Finsupp.domCongr p a.val) →
      MvPowerSeries.coeff γ (MvPowerSeries.rename p (actualUnshiftedTaylorAlgHom n (G.germs a))) = 0) :
    actualInitialVertices MonomialOrder.degLex (Ideal.map (MvPowerSeries.rename p).toRingHom K) =
      fixedPermutedVertices p (actualInitialVertices MonomialOrder.degLex K) := by
  have hD := actual_initial_diagram_rename_of_same_family_heads K (actualSourceFormalFamily G hmem) p hlower
  ext γ
  obtain ⟨α, rfl⟩ := (Finsupp.domCongr p).surjective γ
  have hminimal : (Finsupp.domCongr p α) ∈ actualInitialVertices MonomialOrder.degLex
      (Ideal.map (MvPowerSeries.rename p).toRingHom K) ↔
        α ∈ actualInitialVertices MonomialOrder.degLex K := by
    simp only [actualInitialVertices, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    rw [hD, minimal_permuted_iff]
  rw [hminimal]
  constructor
  · intro hα
    exact Finset.mem_map.mpr ⟨α, hα, rfl⟩
  · intro hα
    obtain ⟨β, hβ, he⟩ := Finset.mem_map.mp hα
    exact (Finsupp.domCongr p).injective he ▸ hβ

def sourceVertexSetCast {V W : Finset (Fin n →₀ ℕ)} (h : V = W) : V ≃ W :=
  Equiv.setCongr (congrArg (fun T : Finset (Fin n →₀ ℕ) => (↑T : Set (Fin n →₀ ℕ))) h)

def sourceFixedSelectorCast {V W : Finset (Fin n →₀ ℕ)} (h : V = W)
    (S : ActualFixedInheritedSelector V) : ActualFixedInheritedSelector W := h ▸ S

def sourceRawFamilyCast {V W : Finset (Fin n →₀ ℕ)} (h : V = W)
    (G : V → HolGerm (ComplexModel n)) : W → HolGerm (ComplexModel n) := h ▸ G

theorem sourceRawFamilyCast_apply {V W : Finset (Fin n →₀ ℕ)} (h : V = W)
    (G : V → HolGerm (ComplexModel n)) (a : V) :
    sourceRawFamilyCast h G (sourceVertexSetCast h a) = G a := by
  cases h
  rfl

def sourceEssentialCast {V W : Finset (Fin n →₀ ℕ)} (h : V = W) :
    fixedSelectorEssential V ≃ fixedSelectorEssential W :=
  Equiv.setCongr (congrArg fixedSelectorEssential h)

theorem sourceFixedSelectorCast_selected_val {V W : Finset (Fin n →₀ ℕ)} (h : V = W)
    (S : ActualFixedInheritedSelector V) (j : fixedSelectorEssential V) :
    ((sourceFixedSelectorCast h S).selected (sourceEssentialCast h j)).val = (S.selected j).val := by
  cases h
  rfl

def sourceBlockCast {V W : Finset (Fin n →₀ ℕ)} (h : V = W) (k : ℕ) :
    fixedSelectorBlock V k ≃ fixedSelectorBlock W k :=
  Equiv.setCongr (congrArg (fun T => fixedSelectorBlock T k) h)

theorem sourceFixedSelectorCast_contact {V W : Finset (Fin n →₀ ℕ)} (h : V = W)
    (S : ActualFixedInheritedSelector V) (G : V → HolGerm (ComplexModel n)) (k : ℕ) :
    actualFixedSelectorContactAt (sourceFixedSelectorCast h S) (sourceRawFamilyCast h G) k ↔
      actualFixedSelectorContactAt S G k := by
  cases h
  rfl

theorem sourceFixedSelectorCast_jacobian {V W : Finset (Fin n →₀ ℕ)} (h : V = W)
    (S : ActualFixedInheritedSelector V) (G : V → HolGerm (ComplexModel n)) (k : ℕ) :
    (actualFixedSelectorJacobian (sourceFixedSelectorCast h S) (sourceRawFamilyCast h G) k).submatrix
      (sourceBlockCast h k) (sourceBlockCast h k) = actualFixedSelectorJacobian S G k := by
  cases h
  rfl

/-- The literal exponent permutation lands in the actual CURRENT vertex set. -/
def actualSourcePermutationVertexEquiv
    (G : ActualAnalyticInheritedFamily n 0 K)
    (hmem : ∀ a, actualUnshiftedTaylorAlgHom n (G.germs a) ∈ K) (p : Fin n ≃ Fin n)
    (hlower : ∀ a γ, MonomialOrder.degLex.toSyn γ <
        MonomialOrder.degLex.toSyn (Finsupp.domCongr p a.val) →
      MvPowerSeries.coeff γ (MvPowerSeries.rename p (actualUnshiftedTaylorAlgHom n (G.germs a))) = 0) :
    actualInitialVertices MonomialOrder.degLex K ≃
      actualInitialVertices MonomialOrder.degLex (Ideal.map (MvPowerSeries.rename p).toRingHom K) :=
  (fixedVertexPermutation p _).trans
    (sourceVertexSetCast (actualSourcePermutationVertices_eq G hmem p hlower).symm)

theorem actualSourcePermutationVertexEquiv_val
    (G : ActualAnalyticInheritedFamily n 0 K)
    (hmem : ∀ a, actualUnshiftedTaylorAlgHom n (G.germs a) ∈ K) (p : Fin n ≃ Fin n)
    (hlower : ∀ a γ, MonomialOrder.degLex.toSyn γ <
        MonomialOrder.degLex.toSyn (Finsupp.domCongr p a.val) →
      MvPowerSeries.coeff γ (MvPowerSeries.rename p (actualUnshiftedTaylorAlgHom n (G.germs a))) = 0)
    (a : actualInitialVertices MonomialOrder.degLex K) :
    (actualSourcePermutationVertexEquiv G hmem p hlower a).val = Finsupp.domCongr p a.val := rfl

/-- SAME analytic numerators, cast only along an exact proved actual vertex-set equality. -/
def actualSourcePermutedInheritedFamily
    (G : ActualAnalyticInheritedFamily n 0 K)
    (hmem : ∀ a, actualUnshiftedTaylorAlgHom n (G.germs a) ∈ K) (p : Fin n ≃ Fin n)
    (hlower : ∀ a γ, MonomialOrder.degLex.toSyn γ <
        MonomialOrder.degLex.toSyn (Finsupp.domCongr p a.val) →
      MvPowerSeries.coeff γ (MvPowerSeries.rename p (actualUnshiftedTaylorAlgHom n (G.germs a))) = 0) :
    ActualAnalyticInheritedFamily n 0 (Ideal.map (MvPowerSeries.rename p).toRingHom K) where
  germs := sourceRawFamilyCast (actualSourcePermutationVertices_eq G hmem p hlower).symm
    (actualPermutedSelectorFamily p G.germs)
  monic a := by
    obtain ⟨a, rfl⟩ := (actualSourcePermutationVertexEquiv G hmem p hlower).surjective a
    change MvPowerSeries.coeff (Finsupp.domCongr p a.val)
      (actualUnshiftedTaylorAlgHom n (sourceRawFamilyCast
        (actualSourcePermutationVertices_eq G hmem p hlower).symm (actualPermutedSelectorFamily p G.germs)
        (sourceVertexSetCast (actualSourcePermutationVertices_eq G hmem p hlower).symm
          (fixedVertexPermutation p _ a)))) = 1
    rw [sourceRawFamilyCast_apply]
    simp only [actualPermutedSelectorFamily, Equiv.symm_apply_apply]
    rw [actualTaylor_actualPermutationGermEquiv, sourceExponentPermutation_coeff]
    exact G.monic a
  lower a γ hγ := by
    obtain ⟨a, rfl⟩ := (actualSourcePermutationVertexEquiv G hmem p hlower).surjective a
    change MvPowerSeries.coeff γ
      (actualUnshiftedTaylorAlgHom n (sourceRawFamilyCast
        (actualSourcePermutationVertices_eq G hmem p hlower).symm (actualPermutedSelectorFamily p G.germs)
        (sourceVertexSetCast (actualSourcePermutationVertices_eq G hmem p hlower).symm
          (fixedVertexPermutation p _ a)))) = 0
    rw [sourceRawFamilyCast_apply]
    simp only [actualPermutedSelectorFamily, Equiv.symm_apply_apply]
    rw [actualTaylor_actualPermutationGermEquiv]
    exact hlower a γ hγ

set_option maxHeartbeats 800000 in
/-- The exact old actual numerator, with no canonical replacement. -/
theorem actualSourcePermutedInheritedFamily_germ
    (G : ActualAnalyticInheritedFamily n 0 K)
    (hmem : ∀ a, actualUnshiftedTaylorAlgHom n (G.germs a) ∈ K) (p : Fin n ≃ Fin n)
    (hlower : ∀ a γ, MonomialOrder.degLex.toSyn γ <
        MonomialOrder.degLex.toSyn (Finsupp.domCongr p a.val) →
      MvPowerSeries.coeff γ (MvPowerSeries.rename p (actualUnshiftedTaylorAlgHom n (G.germs a))) = 0)
    (a : actualInitialVertices MonomialOrder.degLex K) :
    (actualSourcePermutedInheritedFamily G hmem p hlower).germs
        (actualSourcePermutationVertexEquiv G hmem p hlower a) =
      actualPermutationGermEquiv p (G.germs a) := by
  change sourceRawFamilyCast (actualSourcePermutationVertices_eq G hmem p hlower).symm
    (actualPermutedSelectorFamily p G.germs)
    (sourceVertexSetCast (actualSourcePermutationVertices_eq G hmem p hlower).symm
      (fixedVertexPermutation p _ a)) = _
  rw [sourceRawFamilyCast_apply]
  change actualPermutationGermEquiv p (G.germs ((fixedVertexPermutation p _).symm (fixedVertexPermutation p _ a))) = _
  rw [Equiv.symm_apply_apply]

theorem actualSourcePermutedInheritedFamily_mem
    (G : ActualAnalyticInheritedFamily n 0 K)
    (hmem : ∀ a, actualUnshiftedTaylorAlgHom n (G.germs a) ∈ K) (p : Fin n ≃ Fin n)
    (hlower : ∀ a γ, MonomialOrder.degLex.toSyn γ <
        MonomialOrder.degLex.toSyn (Finsupp.domCongr p a.val) →
      MvPowerSeries.coeff γ (MvPowerSeries.rename p (actualUnshiftedTaylorAlgHom n (G.germs a))) = 0) :
    ∀ a, actualUnshiftedTaylorAlgHom n ((actualSourcePermutedInheritedFamily G hmem p hlower).germs a) ∈
      Ideal.map (MvPowerSeries.rename p).toRingHom K := by
  intro a
  obtain ⟨a, rfl⟩ := (actualSourcePermutationVertexEquiv G hmem p hlower).surjective a
  rw [actualSourcePermutedInheritedFamily_germ, actualTaylor_actualPermutationGermEquiv]
  exact Ideal.mem_map_of_mem _ (hmem a)

/-- The entire actual analytic span is the map of the SAME old analytic span. -/
theorem actualSourcePermutedInheritedFamily_span
    (G : ActualAnalyticInheritedFamily n 0 K)
    (hmem : ∀ a, actualUnshiftedTaylorAlgHom n (G.germs a) ∈ K) (p : Fin n ≃ Fin n)
    (hlower : ∀ a γ, MonomialOrder.degLex.toSyn γ <
        MonomialOrder.degLex.toSyn (Finsupp.domCongr p a.val) →
      MvPowerSeries.coeff γ (MvPowerSeries.rename p (actualUnshiftedTaylorAlgHom n (G.germs a))) = 0) :
    Ideal.span (Set.range (actualSourcePermutedInheritedFamily G hmem p hlower).germs) =
      Ideal.map (actualPermutationGermEquiv p).toRingEquiv.toRingHom (Ideal.span (Set.range G.germs)) := by
  rw [Ideal.map_span]
  congr 1
  ext F
  constructor
  · rintro ⟨a,rfl⟩
    obtain ⟨a,rfl⟩ := (actualSourcePermutationVertexEquiv G hmem p hlower).surjective a
    exact ⟨G.germs a,⟨a,rfl⟩,(actualSourcePermutedInheritedFamily_germ G hmem p hlower a).symm⟩
  · rintro ⟨F,⟨a,rfl⟩,rfl⟩
    exact ⟨actualSourcePermutationVertexEquiv G hmem p hlower a,
      actualSourcePermutedInheritedFamily_germ G hmem p hlower a⟩

/-- This really is the whole Taylor extension of the generated new analytic ideal. -/
theorem actualSourcePermutedInheritedFamily_current_ideal
    (G : ActualAnalyticInheritedFamily n 0 K)
    (hmem : ∀ a, actualUnshiftedTaylorAlgHom n (G.germs a) ∈ K) (p : Fin n ≃ Fin n)
    (hlower : ∀ a γ, MonomialOrder.degLex.toSyn γ <
        MonomialOrder.degLex.toSyn (Finsupp.domCongr p a.val) →
      MvPowerSeries.coeff γ (MvPowerSeries.rename p (actualUnshiftedTaylorAlgHom n (G.germs a))) = 0) :
    actualInheritedCurrentSourceIdeal (Ideal.span (Set.range
      (actualSourcePermutedInheritedFamily G hmem p hlower).germs)) =
        Ideal.map (MvPowerSeries.rename p).toRingHom K := by
  let G' := actualSourcePermutedInheritedFamily G hmem p hlower
  have hgen := family_formal_ideal_eq_span_vertex_series MonomialOrder.degLex
    (Ideal.map (MvPowerSeries.rename p).toRingHom K)
    (actualSourceFormalFamily G' (actualSourcePermutedInheritedFamily_mem G hmem p hlower))
  rw [actualInheritedCurrentSourceIdeal, Ideal.map_span, ← Set.range_comp]
  exact hgen.symm

/-- WHOLE lower-prefix coefficients transport at every exponent. -/
theorem actualSourcePermutedInheritedFamily_prefix_reduced
    (G : ActualAnalyticInheritedFamily n 0 K)
    (hmem : ∀ a, actualUnshiftedTaylorAlgHom n (G.germs a) ∈ K) (p : Fin n ≃ Fin n)
    (hlower : ∀ a γ, MonomialOrder.degLex.toSyn γ <
        MonomialOrder.degLex.toSyn (Finsupp.domCongr p a.val) →
      MvPowerSeries.coeff γ (MvPowerSeries.rename p (actualUnshiftedTaylorAlgHom n (G.germs a))) = 0)
    (k : ℕ) (hred : ActualInheritedPrefixReducedAt G k) :
    ActualInheritedPrefixReducedAt (actualSourcePermutedInheritedFamily G hmem p hlower) k := by
  intro a ha b hb α hbα
  obtain ⟨a, rfl⟩ := (actualSourcePermutationVertexEquiv G hmem p hlower).surjective a
  obtain ⟨b, rfl⟩ := (actualSourcePermutationVertexEquiv G hmem p hlower).surjective b
  obtain ⟨β, rfl⟩ := (Finsupp.domCongr p).surjective α
  rw [actualSourcePermutedInheritedFamily_germ, actualTaylor_actualPermutationGermEquiv,
    sourceExponentPermutation_coeff]
  have ha' : k < normalExponentDegree a.val := by
    simpa only [actualSourcePermutationVertexEquiv_val, sourceExponentPermutation_degree] using ha
  have hb' : normalExponentDegree b.val ≤ k := by
    simpa only [actualSourcePermutationVertexEquiv_val, sourceExponentPermutation_degree] using hb
  have hle : b.val ≤ β := (sourceExponentPermutation_le_iff p b.val β).mp hbα
  exact hred a ha' b hb' β hle

/-- Historical selector, transported as data along the ACTUAL new vertex-set equality. -/
def actualSourcePermutedFixedSelector
    (G : ActualAnalyticInheritedFamily n 0 K)
    (hmem : ∀ a, actualUnshiftedTaylorAlgHom n (G.germs a) ∈ K) (p : Fin n ≃ Fin n)
    (hlower : ∀ a γ, MonomialOrder.degLex.toSyn γ <
        MonomialOrder.degLex.toSyn (Finsupp.domCongr p a.val) →
      MvPowerSeries.coeff γ (MvPowerSeries.rename p (actualUnshiftedTaylorAlgHom n (G.germs a))) = 0)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex K)) :
    ActualFixedInheritedSelector
      (actualInitialVertices MonomialOrder.degLex (Ideal.map (MvPowerSeries.rename p).toRingHom K)) :=
  sourceFixedSelectorCast (actualSourcePermutationVertices_eq G hmem p hlower).symm
    (actualFixedSelectorPermutation p S)

set_option maxHeartbeats 800000 in
/-- Raw transported provenance lands at the actual current essential labels. -/
theorem actualSourcePermutedFixedSelector_selected_val
    (G : ActualAnalyticInheritedFamily n 0 K)
    (hmem : ∀ a, actualUnshiftedTaylorAlgHom n (G.germs a) ∈ K) (p : Fin n ≃ Fin n)
    (hlower : ∀ a γ, MonomialOrder.degLex.toSyn γ <
        MonomialOrder.degLex.toSyn (Finsupp.domCongr p a.val) →
      MvPowerSeries.coeff γ (MvPowerSeries.rename p (actualUnshiftedTaylorAlgHom n (G.germs a))) = 0)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex K))
    (j : fixedSelectorEssential (actualInitialVertices MonomialOrder.degLex K)) :
    ((actualSourcePermutedFixedSelector G hmem p hlower S).selected
      (sourceEssentialCast (actualSourcePermutationVertices_eq G hmem p hlower).symm
        (fixedEssentialPermutation p _ j))).val = Finsupp.domCongr p (S.selected j).val := by
  rw [actualSourcePermutedFixedSelector,sourceFixedSelectorCast_selected_val]
  change (fixedVertexPermutation p _ (S.selected
    ((fixedEssentialPermutation p _).symm (fixedEssentialPermutation p _ j)))).val = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem actualSourcePermutedFixedSelector_contact
    (G : ActualAnalyticInheritedFamily n 0 K)
    (hmem : ∀ a, actualUnshiftedTaylorAlgHom n (G.germs a) ∈ K) (p : Fin n ≃ Fin n)
    (hlower : ∀ a γ, MonomialOrder.degLex.toSyn γ <
        MonomialOrder.degLex.toSyn (Finsupp.domCongr p a.val) →
      MvPowerSeries.coeff γ (MvPowerSeries.rename p (actualUnshiftedTaylorAlgHom n (G.germs a))) = 0)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex K))
    (k : ℕ) (hadapt : actualFixedSelectorContactAt S G.germs k) :
    actualFixedSelectorContactAt (actualSourcePermutedFixedSelector G hmem p hlower S)
      (actualSourcePermutedInheritedFamily G hmem p hlower).germs k := by
  apply (sourceFixedSelectorCast_contact (actualSourcePermutationVertices_eq G hmem p hlower).symm
    (actualFixedSelectorPermutation p S) (actualPermutedSelectorFamily p G.germs) k).mpr
  exact actualFixedSelectorContact_permutation p S G.germs k hadapt

set_option maxHeartbeats 800000 in
/-- The SAME actual matrix entries, with both indices transported literally. -/
theorem actualSourcePermutedFixedSelector_jacobian
    (G : ActualAnalyticInheritedFamily n 0 K)
    (hmem : ∀ a, actualUnshiftedTaylorAlgHom n (G.germs a) ∈ K) (p : Fin n ≃ Fin n)
    (hlower : ∀ a γ, MonomialOrder.degLex.toSyn γ <
        MonomialOrder.degLex.toSyn (Finsupp.domCongr p a.val) →
      MvPowerSeries.coeff γ (MvPowerSeries.rename p (actualUnshiftedTaylorAlgHom n (G.germs a))) = 0)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex K)) (k : ℕ) :
    (actualFixedSelectorJacobian (actualSourcePermutedFixedSelector G hmem p hlower S)
      (actualSourcePermutedInheritedFamily G hmem p hlower).germs k).submatrix
        ((fixedBlockPermutation p _ k).trans
          (sourceBlockCast (actualSourcePermutationVertices_eq G hmem p hlower).symm k))
        ((fixedBlockPermutation p _ k).trans
          (sourceBlockCast (actualSourcePermutationVertices_eq G hmem p hlower).symm k)) =
      actualFixedSelectorJacobian S G.germs k := by
  change ((actualFixedSelectorJacobian
      (sourceFixedSelectorCast (actualSourcePermutationVertices_eq G hmem p hlower).symm
        (actualFixedSelectorPermutation p S))
      (sourceRawFamilyCast (actualSourcePermutationVertices_eq G hmem p hlower).symm
        (actualPermutedSelectorFamily p G.germs)) k).submatrix
        (sourceBlockCast (actualSourcePermutationVertices_eq G hmem p hlower).symm k)
        (sourceBlockCast (actualSourcePermutationVertices_eq G hmem p hlower).symm k)).submatrix
          (fixedBlockPermutation p _ k) (fixedBlockPermutation p _ k) = _
  rw [sourceFixedSelectorCast_jacobian]
  exact actualFixedSelectorJacobian_permutation p S G.germs k

/-- Simultaneous ACTUAL block reindexing preserves the true Jacobian determinant. -/
theorem actualSourcePermutedFixedSelector_jacobian_det
    (G : ActualAnalyticInheritedFamily n 0 K)
    (hmem : ∀ a, actualUnshiftedTaylorAlgHom n (G.germs a) ∈ K) (p : Fin n ≃ Fin n)
    (hlower : ∀ a γ, MonomialOrder.degLex.toSyn γ <
        MonomialOrder.degLex.toSyn (Finsupp.domCongr p a.val) →
      MvPowerSeries.coeff γ (MvPowerSeries.rename p (actualUnshiftedTaylorAlgHom n (G.germs a))) = 0)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex K)) (k : ℕ) :
    (actualFixedSelectorJacobian (actualSourcePermutedFixedSelector G hmem p hlower S)
      (actualSourcePermutedInheritedFamily G hmem p hlower).germs k).det =
        (actualFixedSelectorJacobian S G.germs k).det := by
  let hV := (actualSourcePermutationVertices_eq G hmem p hlower).symm
  have hcast := sourceFixedSelectorCast_jacobian hV (actualFixedSelectorPermutation p S)
    (actualPermutedSelectorFamily p G.germs) k
  have hd := congrArg Matrix.det hcast
  rw [Matrix.det_submatrix_equiv_self] at hd
  exact hd.trans (actualFixedSelectorJacobian_permutation_det p S G.germs k)

end
end Hironaka.HironakaActualInheritedSourcePermutationFamily
