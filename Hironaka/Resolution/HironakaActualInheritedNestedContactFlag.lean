import Hironaka.Resolution.HironakaActualInheritedNextBlockGraph
import Hironaka.Resolution.HironakaActualAnalyticFormalNormalPowers
import Hironaka.Resolution.HironakaActualInheritedWholeSelectedAdjustment

/-! Actual finite construction of the initial inherited nested contact flag.
The true IFT graph and actual whole selected analytic division are composed
internally. The final original-only endpoint preserves SAME finite labels
and the whole original diagram, and supplies all nested derivative/contact
and whole prefix-support conditions simultaneously. Graph-only lower helpers
remain separate from the complete whole-division construction. -/

set_option autoImplicit false
open Set Filter Classical
open scoped Topology

namespace Hironaka.HironakaActualInheritedNestedContactFlag

noncomputable section

open HolGerm HironakaActualCoefficientPresentationCentrePower
  HironakaActualInheritedAnalyticBlockJacobian HironakaActualAnalyticBlockGraphTranslation
  HironakaActualInheritedNextBlockGraph HironakaActualRelativeNormalJetDivision
  HironakaActualCanonicalBlockJacobian HironakaActualFormalInitialDiagram
  HironakaActualRelativeStandardnessBlockSupport
  HironakaHolomorphicJetChartInvariance HironakaRelativeNormalMonomialBasis
  HironakaActualAnalyticCanonicalVertices HironakaActualReducedFormalStandardBasis
  HironakaActualAnalyticFormalNormalPowers
  HironakaActualInheritedWholeSelectedAdjustment HironakaActualSelectedVertexHomogeneousBasis

variable {n : ℕ} {K : Ideal (MvPowerSeries (Fin n) ℂ)}

theorem actualGraphTransformedMember_initial (G : ActualAnalyticInheritedFamily n 0 K)
    {B C : Set (Fin n)} (D : ActualBlockGraphData B C) (hpriority : ActualBlockGraphLinearPriority D)
    (a : actualInitialVertices MonomialOrder.degLex K) :
    ∃ hnew : actualUnshiftedTaylorAlgHom n (actualBlockGraphGermEquiv D (G.germs a)) ≠ 0,
      actualInitialExponent MonomialOrder.degLex
        (actualUnshiftedTaylorAlgHom n (actualBlockGraphGermEquiv D (G.germs a))) hnew = a.val ∧
      MvPowerSeries.coeff a.val
        (actualUnshiftedTaylorAlgHom n (actualBlockGraphGermEquiv D (G.germs a))) = 1 := by
  have hc := G.monic a
  change MvPowerSeries.coeff a.val (actualUnshiftedTaylorAlgHom n (G.germs a)) = 1 at hc
  have hF : actualUnshiftedTaylorAlgHom n (G.germs a) ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hc
    exact zero_ne_one hc
  have hmin : actualInitialExponent MonomialOrder.degLex
      (actualUnshiftedTaylorAlgHom n (G.germs a)) hF = a.val := by
    apply actualInitialExponent_eq_of_coefficients
    · rw [hc]
      exact one_ne_zero
    · intro β hβ
      have h := G.lower a β hβ
      change MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom n (G.germs a)) = 0 at h
      exact h
  obtain ⟨hS, hhead, hcoeff⟩ :=
    (actualAnalyticBlockGraphTranslation_initial_and_derivatives D hpriority).1
      (actualUnshiftedTaylorAlgHom n (G.germs a)) hF
  have hT : actualUnshiftedTaylorAlgHom n (actualBlockGraphGermEquiv D (G.germs a)) =
      actualBlockGraphFormalEquiv D (actualUnshiftedTaylorAlgHom n (G.germs a)) :=
    congrArg (fun f : HolGerm (ComplexModel n) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ => f (G.germs a))
      (actualTaylor_blockGraph D)
  have hnew : actualUnshiftedTaylorAlgHom n (actualBlockGraphGermEquiv D (G.germs a)) ≠ 0 := by
    rwa [hT]
  refine ⟨hnew, ?_, ?_⟩
  · simpa only [hT] using hhead.trans hmin
  · rw [hT]
    simpa only [hmin, hc] using hcoeff

/-- The SAME analytic members and labels after the genuine graph pullback.
There is no new canonical reduction and no invented target ideal. -/
def actualGraphTransformedFamily (G : ActualAnalyticInheritedFamily n 0 K)
    {B C : Set (Fin n)} (D : ActualBlockGraphData B C) (hpriority : ActualBlockGraphLinearPriority D) :
    ActualAnalyticInheritedFamily n 0 K where
  germs := fun a => actualBlockGraphGermEquiv D (G.germs a)
  monic := fun a => (actualGraphTransformedMember_initial G D hpriority a).choose_spec.2
  lower := by
    intro a β hβ
    obtain ⟨hne, hmin, _hc⟩ := actualGraphTransformedMember_initial G D hpriority a
    apply coeff_eq_zero_of_lt_actualInitialExponent MonomialOrder.degLex _ hne β
    rwa [hmin]

theorem actualGraphTransformedFamily_span (G : ActualAnalyticInheritedFamily n 0 K)
    {B C : Set (Fin n)} (D : ActualBlockGraphData B C) (hpriority : ActualBlockGraphLinearPriority D) :
    Ideal.span (range (actualGraphTransformedFamily G D hpriority).germs) =
      Ideal.map (actualBlockGraphGermEquiv D).toRingEquiv.toRingHom (Ideal.span (range G.germs)) := by
  rw [Ideal.map_span, ← Set.range_comp]
  rfl

/-- The true graph equivalence preserves the ENTIRE diagram of every whole
formal ideal. No claim that arbitrary inherited labels exhaust it is used. -/
theorem actualInitialDiagram_map_blockGraph
    {B C : Set (Fin n)} (D : ActualBlockGraphData B C)
    (hpriority : ActualBlockGraphLinearPriority D)
    (J : Ideal (MvPowerSeries (Fin n) ℂ)) :
    actualInitialDiagram MonomialOrder.degLex
        (Ideal.map (actualBlockGraphFormalEquiv D).toRingEquiv.toRingHom J) =
      actualInitialDiagram MonomialOrder.degLex J := by
  ext α
  constructor
  · rintro ⟨G, hG, hGn, hGα⟩
    obtain ⟨F, hF, rfl⟩ := (Ideal.mem_map_iff_of_surjective
      (actualBlockGraphFormalEquiv D).toRingEquiv.toRingHom
      (actualBlockGraphFormalEquiv D).surjective).mp hG
    have hFn : F ≠ 0 := by
      intro hz
      subst F
      exact hGn (map_zero _)
    obtain ⟨_hSF, hhead, _hc⟩ :=
      (actualAnalyticBlockGraphTranslation_initial_and_derivatives D hpriority).1 F hFn
    exact ⟨F, hF, hFn, hhead.symm.trans hGα⟩
  · rintro ⟨F, hF, hFn, hFα⟩
    obtain ⟨hSF, hhead, _hc⟩ :=
      (actualAnalyticBlockGraphTranslation_initial_and_derivatives D hpriority).1 F hFn
    exact ⟨actualBlockGraphFormalEquiv D F, Ideal.mem_map_of_mem _ hF,
      hSF, hhead.trans hFα⟩

theorem actualInitialDiagram_map_blockGraph_analytic
    {B C : Set (Fin n)} (D : ActualBlockGraphData B C)
    (hpriority : ActualBlockGraphLinearPriority D)
    (J : Ideal (HolGerm (ComplexModel n))) :
    actualInitialDiagram MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom
          (Ideal.map (actualBlockGraphGermEquiv D).toRingEquiv.toRingHom J)) =
      actualInitialDiagram MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom J) := by
  have hmap : Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom
      (Ideal.map (actualBlockGraphGermEquiv D).toRingEquiv.toRingHom J) =
      Ideal.map (actualBlockGraphFormalEquiv D).toRingEquiv.toRingHom
        (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom J) := by
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
    apply RingHom.ext
    intro F
    exact congrArg (fun f : HolGerm (ComplexModel n) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ => f F)
      (actualTaylor_blockGraph D)
  rw [hmap, actualInitialDiagram_map_blockGraph D hpriority]

/-- Whole cone avoidance is exactly vanishing of a true higher derivative in
characteristic zero; no truncation or finite-q surrogate occurs here. -/
theorem actualFormalMultiDerivative_eq_zero_iff_cone
    (β : Fin n →₀ ℕ) (F : MvPowerSeries (Fin n) ℂ) :
    actualFormalMultiDerivative β F = 0 ↔
      ∀ α : Fin n →₀ ℕ, β ≤ α → MvPowerSeries.coeff α F = 0 := by
  constructor
  · intro hzero α hβα
    have hcoeff := congrArg (MvPowerSeries.coeff (α-β)) hzero
    rw [coeff_actualFormalMultiDerivative, tsub_add_cancel_of_le hβα, map_zero] at hcoeff
    exact (mul_eq_zero.mp hcoeff).resolve_right
      (div_ne_zero (actualExponentFactorial_ne_zero α)
        (actualExponentFactorial_ne_zero (α-β)))
  · intro hzero
    apply MvPowerSeries.ext
    intro γ
    rw [coeff_actualFormalMultiDerivative, map_zero]
    have hβ : β ≤ γ+β := by
      intro i
      simp only [Finsupp.add_apply]
      omega
    rw [hzero (γ+β) hβ, zero_mul]

theorem actualAnalyticMultiDerivative_eq_zero_iff_cone
    (β : Fin n →₀ ℕ) (F : HolGerm (ComplexModel n)) :
    actualAnalyticMultiDerivative β F = 0 ↔
      ∀ α : Fin n →₀ ℕ, β ≤ α →
        MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom n F) = 0 := by
  rw [← actualFormalMultiDerivative_eq_zero_iff_cone]
  constructor
  · intro hzero
    rw [← actualTaylor_actualAnalyticMultiDerivative, hzero, map_zero]
  · intro hzero
    apply actualUnshiftedTaylorAlgHom_injective n
    rw [actualTaylor_actualAnalyticMultiDerivative, hzero, map_zero]

/-- This is the WHOLE degree-prefix support condition (5). It is deliberately
stronger than a finite normal-jet condition for one chosen q. -/
def ActualInheritedPrefixReducedAt (G : ActualAnalyticInheritedFamily n 0 K) (k : ℕ) : Prop :=
  ∀ a : actualInitialVertices MonomialOrder.degLex K,
    k < normalExponentDegree a.val →
      ∀ b : actualInitialVertices MonomialOrder.degLex K,
        normalExponentDegree b.val ≤ k →
          ∀ α : Fin n →₀ ℕ, b.val ≤ α →
            MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom n (G.germs a)) = 0

/-- The empty degree block starts with the whole support property for every
genuine inherited family. If a degree-zero vertex exists it is the sole
minimal vertex, so there is no higher member to consider. -/
theorem actualInheritedPrefixReducedAt_zero (G : ActualAnalyticInheritedFamily n 0 K) :
    ActualInheritedPrefixReducedAt G 0 := by
  intro a ha b hb α _hbα
  have hbzero : b.val = 0 := by
    ext i
    have hi : b.val i ≤ normalExponentDegree b.val :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hz : b.val i = 0 := by omega
    exact hz
  have hmin : Minimal (· ∈ actualInitialDiagram MonomialOrder.degLex K) a.val := by
    simpa [actualInitialVertices] using a.property
  have hbmin : Minimal (· ∈ actualInitialDiagram MonomialOrder.degLex K) b.val := by
    simpa [actualInitialVertices] using b.property
  have hazero : a.val = 0 := by
    apply le_antisymm
    · simpa only [hbzero] using hmin.2 hbmin.prop (by simp [hbzero])
    · exact zero_le
  have hdegree : normalExponentDegree a.val = 0 := by simp [hazero, normalExponentDegree]
  omega

/-- Coupling for a true selected-prefix adjustment: old higher members that
are now selected stay fixed; the remaining members avoid the larger whole
diagram. The actual division producer will supply the two exact inputs. -/
theorem actualInheritedPrefixReducedAt_of_fixed_and_larger
    (G H : ActualAnalyticInheritedFamily n 0 K) (r k : ℕ) (hrk : r ≤ k)
    (hfixed : ∀ a, normalExponentDegree a.val ≤ k → H.germs a = G.germs a)
    (hnew : ActualInheritedPrefixReducedAt H k)
    (hold : ActualInheritedPrefixReducedAt G r) : ActualInheritedPrefixReducedAt H r := by
  intro a ha b hb α hbα
  by_cases hak : normalExponentDegree a.val ≤ k
  · rw [hfixed a hak]
    exact hold a ha b hb α hbα
  · exact hnew a (Nat.lt_of_not_ge hak) b (hb.trans hrk) α hbα

/-- The SAME graph pullback preserves every older whole prefix condition.
Only the real support of the old vertices in the new derivative block is
used; the family need not be canonical. -/
theorem actualGraphTransformedFamily_prefix_reduced
    (G : ActualAnalyticInheritedFamily n 0 K) (r k : ℕ) (hrk : r ≤ k)
    {C : Set (Fin n)}
    (D : ActualBlockGraphData (actualDegreePrefixVariables MonomialOrder.degLex K k) C)
    (hpriority : ActualBlockGraphLinearPriority D)
    (hred : ActualInheritedPrefixReducedAt G r) :
    ActualInheritedPrefixReducedAt (actualGraphTransformedFamily G D hpriority) r := by
  intro a ha b hb
  apply (actualAnalyticMultiDerivative_eq_zero_iff_cone b.val _).mp
  have hsupport : ∀ i ∉ actualDegreePrefixVariables MonomialOrder.degLex K k, b.val i = 0 := by
    intro i hi
    by_contra hbi
    exact hi ⟨b, hb.trans hrk, hbi⟩
  change actualAnalyticMultiDerivative b.val (actualBlockGraphGermEquiv D (G.germs a)) = 0
  rw [actualBlockGraphGermEquiv_multi_derivative D b.val hsupport,
    (actualAnalyticMultiDerivative_eq_zero_iff_cone b.val _).mpr (hred a ha b hb), map_zero]

/-- The literal canonical original family internally starts with every WHOLE
prefix support condition, independently of a future graph or adjustment. -/
theorem actualInheritedPrefixReducedAt_of_canonical
    (G : ActualAnalyticInheritedFamily n 0 K)
    (hcanonical : ∀ a, actualUnshiftedTaylorAlgHom n (G.germs a) =
      actualReducedVertexSeries MonomialOrder.degLex K a) (k : ℕ) :
    ActualInheritedPrefixReducedAt G k := by
  intro a ha b hb α hbα
  rw [hcanonical a]
  have hminimal : Minimal (· ∈ actualInitialDiagram MonomialOrder.degLex K) a.val := by
    simpa [actualInitialVertices] using a.property
  have hbmem : b.val ∈ actualInitialDiagram MonomialOrder.degLex K := by
    have hbmin : Minimal (· ∈ actualInitialDiagram MonomialOrder.degLex K) b.val := by
      simpa [actualInitialVertices] using b.property
    exact hbmin.prop
  have hαmem := actualInitialDiagram_upper MonomialOrder.degLex K b.val α hbmem hbα
  rw [actualReducedVertexSeries_coefficient_diagram MonomialOrder.degLex K a α hαmem]
  apply if_neg
  intro hαa
  have hba : b.val ≤ a.val := hαa ▸ hbα
  have hab : a.val ≤ b.val := hminimal.2 hbmem hba
  have he : a.val = b.val := le_antisymm hab hba
  have hd := congrArg normalExponentDegree he
  omega

/-- The true nested block condition concerns derivatives of the CURRENT family. -/
def ActualInheritedContactAt (G : ActualAnalyticInheritedFamily n 0 K) (k : ℕ) : Prop :=
  ∀ j : actualDegreePrefixVariables MonomialOrder.degLex K k,
    actualInheritedEssentialDerivative G
      (actualCanonicalBlockEssentialVariable MonomialOrder.degLex K k j) ∈
        actualAnalyticCoordinateBlockIdeal (actualDegreePrefixVariables MonomialOrder.degLex K k)

/-- Fixing the actual selected prefix fixes all its chosen analytic derivative
germs. This applies to the internally constructed whole division adjustment,
without making any new family canonical. -/
theorem actualInheritedContactAt_of_fixed_prefix
    (G H : ActualAnalyticInheritedFamily n 0 K) (r k : ℕ) (hrk : r ≤ k)
    (hfixed : ∀ a, normalExponentDegree a.val ≤ k → H.germs a = G.germs a)
    (hcontact : ActualInheritedContactAt G r) : ActualInheritedContactAt H r := by
  intro j
  change actualAnalyticMultiDerivative _
    (H.germs (actualCanonicalDerivativeVertex MonomialOrder.degLex K
      (actualCanonicalBlockEssentialVariable MonomialOrder.degLex K r j))) ∈ _
  rw [hfixed _ ((actualCanonicalDerivativeVertex_degree_le MonomialOrder.degLex K r j).trans hrk)]
  exact hcontact j

theorem actualGraphTransformedFamily_selected_derivative
    (G : ActualAnalyticInheritedFamily n 0 K)
    {B C : Set (Fin n)} (D : ActualBlockGraphData B C) (hpriority : ActualBlockGraphLinearPriority D)
    (j : actualCanonicalEssentialVariables MonomialOrder.degLex K)
    (hsupport : ∀ i ∉ B, actualCanonicalDerivativeExponent MonomialOrder.degLex K j i = 0) :
    actualInheritedEssentialDerivative (actualGraphTransformedFamily G D hpriority) j =
      actualBlockGraphGermEquiv D (actualInheritedEssentialDerivative G j) := by
  exact actualBlockGraphGermEquiv_multi_derivative D _ hsupport _

private theorem prefix_block_mono {r k : ℕ} (hrk : r ≤ k) :
    actualDegreePrefixVariables MonomialOrder.degLex K r ⊆
      actualDegreePrefixVariables MonomialOrder.degLex K k := by
  intro i hi
  obtain ⟨a, ha, hai⟩ := hi
  exact ⟨a, ha.trans hrk, hai⟩

private theorem coordinate_ideal_mono {A B : Set (Fin n)} (hAB : A ⊆ B) :
    actualAnalyticCoordinateBlockIdeal A ≤ actualAnalyticCoordinateBlockIdeal B :=
  Ideal.span_mono (Set.image_mono hAB)

/-- True older contact memberships survive the next graph because that graph
is independent of ALL new-block coordinates and fixes the whole old ideal. -/
theorem actualGraphTransformedFamily_contact_earlier
    (G : ActualAnalyticInheritedFamily n 0 K) (kprev k r : ℕ)
    (hcut : kprev ≤ k) (hr : r ≤ kprev)
    (D : ActualBlockGraphData (actualDegreePrefixVariables MonomialOrder.degLex K k)
      (actualNextBlockCoordinates (K := K) kprev k))
    (hpriority : ActualBlockGraphLinearPriority D) (hcontact : ActualInheritedContactAt G r) :
    ActualInheritedContactAt (actualGraphTransformedFamily G D hpriority) r := by
  intro j
  have hsupport : ∀ i ∉ actualDegreePrefixVariables MonomialOrder.degLex K k,
      actualCanonicalDerivativeExponent MonomialOrder.degLex K
        (actualCanonicalBlockEssentialVariable MonomialOrder.degLex K r j) i = 0 := by
    intro i hi
    apply actualCanonicalDerivativeExponent_support MonomialOrder.degLex K r j i
    exact fun hir => hi (prefix_block_mono (hr.trans hcut) hir)
  rw [actualGraphTransformedFamily_selected_derivative G D hpriority _ hsupport]
  have hm := Ideal.mem_map_of_mem (actualBlockGraphGermEquiv D).toRingEquiv.toRingHom (hcontact j)
  have hfix : Ideal.map (actualBlockGraphGermEquiv D).toRingEquiv.toRingHom
      (actualAnalyticCoordinateBlockIdeal (actualDegreePrefixVariables MonomialOrder.degLex K r)) =
      actualAnalyticCoordinateBlockIdeal (actualDegreePrefixVariables MonomialOrder.degLex K r) := by
    apply map_actualAnalyticCoordinateBlockIdeal_graph
    intro i hi hCi
    exact hCi.2 (prefix_block_mono hr hi)
  rwa [hfix] at hm

/-- Every current old-block membership and every newly solved equation combine
to the true enlarged contact block for the SAME graph-transformed family. -/
theorem actualGraphTransformedFamily_contact_next
    (G : ActualAnalyticInheritedFamily n 0 K) (kprev k : ℕ) (hcut : kprev ≤ k)
    (D : ActualBlockGraphData (actualDegreePrefixVariables MonomialOrder.degLex K k)
      (actualNextBlockCoordinates (K := K) kprev k))
    (hpriority : ActualBlockGraphLinearPriority D)
    (hprevious : ActualInheritedContactAt G kprev)
    (hnew : ∀ j : actualNextBlockCoordinates (K := K) kprev k,
      actualBlockGraphGermEquiv D (actualNextBlockDerivativeGerm G kprev k j) ∈
        actualAnalyticCoordinateBlockIdeal (actualDegreePrefixVariables MonomialOrder.degLex K k)) :
    ActualInheritedContactAt (actualGraphTransformedFamily G D hpriority) k := by
  intro j
  have hsupport := actualCanonicalDerivativeExponent_support MonomialOrder.degLex K k j
  rw [actualGraphTransformedFamily_selected_derivative G D hpriority _ hsupport]
  by_cases hjold : j.val ∈ actualDegreePrefixVariables MonomialOrder.degLex K kprev
  · have hold := actualGraphTransformedFamily_contact_earlier G kprev k kprev hcut le_rfl D hpriority
      hprevious ⟨j.val, hjold⟩
    have he : actualCanonicalBlockEssentialVariable MonomialOrder.degLex K kprev ⟨j.val, hjold⟩ =
        actualCanonicalBlockEssentialVariable MonomialOrder.degLex K k j := Subtype.ext rfl
    rw [he, actualGraphTransformedFamily_selected_derivative G D hpriority _ hsupport] at hold
    exact coordinate_ideal_mono (prefix_block_mono hcut) hold
  · exact hnew ⟨j.val, j.property, hjold⟩

set_option linter.unusedVariables false in
/-- Honest composition of two genuine original local holomorphic equivalences.
The pullback order is the corresponding opposite order on analytic germs. -/
def actualContactLocalEquivComp
    (Φ Ψ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n))
    (hΦ0 : Φ.toFun 0 = 0) (hΨ0 : Ψ.toFun 0 = 0) :
    LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n) where
  source := Ψ.source ∩ Ψ.toFun ⁻¹' Φ.source
  target := Φ.target ∩ Φ.invFun ⁻¹' Ψ.target
  isOpen_source := Ψ.toFun_holomorphic.continuousOn.isOpen_inter_preimage
    Ψ.isOpen_source Φ.isOpen_source
  isOpen_target := Φ.invFun_holomorphic.continuousOn.isOpen_inter_preimage
    Φ.isOpen_target Ψ.isOpen_target
  center_mem_source := ⟨Ψ.center_mem_source, by
    change Ψ.toFun 0 ∈ Φ.source
    simpa only [hΨ0] using Φ.center_mem_source⟩
  toFun := Φ.toFun ∘ Ψ.toFun
  invFun := Ψ.invFun ∘ Φ.invFun
  toFun_holomorphic := Φ.toFun_holomorphic.comp
    (Ψ.toFun_holomorphic.mono inter_subset_left) (fun _ hz => hz.2)
  invFun_holomorphic := Ψ.invFun_holomorphic.comp
    (Φ.invFun_holomorphic.mono inter_subset_left) (fun _ hz => hz.2)
  mapsTo_toFun z hz := by
    refine ⟨Φ.mapsTo_toFun hz.2, ?_⟩
    change Φ.invFun (Φ.toFun (Ψ.toFun z)) ∈ Ψ.target
    rw [Φ.left_inv _ hz.2]
    exact Ψ.mapsTo_toFun hz.1
  mapsTo_invFun w hw := by
    refine ⟨Ψ.mapsTo_invFun hw.2, ?_⟩
    change Ψ.toFun (Ψ.invFun (Φ.invFun w)) ∈ Φ.source
    rw [Ψ.right_inv _ hw.2]
    exact Φ.mapsTo_invFun hw.1
  left_inv z hz := by
    change Ψ.invFun (Φ.invFun (Φ.toFun (Ψ.toFun z))) = z
    rw [Φ.left_inv _ hz.2, Ψ.left_inv _ hz.1]
  right_inv w hw := by
    change Φ.toFun (Ψ.toFun (Ψ.invFun (Φ.invFun w))) = w
    rw [Ψ.right_inv _ hw.2, Φ.right_inv _ hw.1]

theorem actualContactLocalEquivComp_zero
    (Φ Ψ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n))
    (hΦ0 : Φ.toFun 0 = 0) (hΨ0 : Ψ.toFun 0 = 0) :
    (actualContactLocalEquivComp Φ Ψ hΦ0 hΨ0).toFun 0 = 0 := by
  change Φ.toFun (Ψ.toFun 0) = 0
  rw [hΨ0, hΦ0]

theorem actualContactLocalEquivComp_germ
    (Φ Ψ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n))
    (hΦ0 : Φ.toFun 0 = 0) (hΨ0 : Ψ.toFun 0 = 0) (F : HolGerm (ComplexModel n)) :
    localGermAlgEquiv (actualContactLocalEquivComp Φ Ψ hΦ0 hΨ0)
        (actualContactLocalEquivComp_zero Φ Ψ hΦ0 hΨ0) F =
      localGermAlgEquiv Ψ hΨ0 (localGermAlgEquiv Φ hΦ0 F) := by
  induction F using HolGerm.induction_on with
  | h f hf =>
    rw [localGermAlgEquiv_mk, localGermAlgEquiv_mk, localGermAlgEquiv_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall (fun _ => rfl)

def actualContactLocalEquivRefl (n : ℕ) : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n) where
  source := Set.univ
  target := Set.univ
  isOpen_source := isOpen_univ
  isOpen_target := isOpen_univ
  center_mem_source := mem_univ _
  toFun := id
  invFun := id
  toFun_holomorphic := differentiableOn_id
  invFun_holomorphic := differentiableOn_id
  mapsTo_toFun := fun _ _ => mem_univ _
  mapsTo_invFun := fun _ _ => mem_univ _
  left_inv := fun _ _ => rfl
  right_inv := fun _ _ => rfl

theorem actualContactLocalEquivRefl_germ (F : HolGerm (ComplexModel n)) :
    localGermAlgEquiv (actualContactLocalEquivRefl n) rfl F = F := by
  induction F using HolGerm.induction_on with
  | h f hf =>
    unfold actualContactLocalEquivRefl
    rw [localGermAlgEquiv_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall (fun _ => rfl)

/-- A constructed finite-stage state. Its actual local chart and whole ideal
span are retained; no contact state is an input to the original-only producer. -/
structure ActualInheritedGraphContactStage (G0 : ActualAnalyticInheritedFamily n 0 K) (k : ℕ) where
  chart : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n)
  zero : chart.toFun 0 = 0
  family : ActualAnalyticInheritedFamily n 0 K
  span_eq : Ideal.span (range family.germs) =
    Ideal.map (localGermAlgEquiv chart zero).toRingEquiv.toRingHom (Ideal.span (range G0.germs))
  diagram_eq : actualInitialDiagram MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom (Ideal.span (range family.germs))) =
    actualInitialDiagram MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom (Ideal.span (range G0.germs)))
  contact : ∀ r : ℕ, r ≤ k → ActualInheritedContactAt family r

private theorem actualInheritedContactAt_zero (G : ActualAnalyticInheritedFamily n 0 K) :
    ActualInheritedContactAt G 0 := by
  intro j
  obtain ⟨a, ha, haj⟩ := j.property
  have hle : a.val j.val ≤ normalExponentDegree a.val := by
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j.val)
  have hz : a.val j.val = 0 := by omega
  exact (haj hz).elim

def actualInheritedGraphContactStage_zero (G0 : ActualAnalyticInheritedFamily n 0 K) :
    ActualInheritedGraphContactStage G0 0 where
  chart := actualContactLocalEquivRefl n
  zero := rfl
  family := G0
  span_eq := by
    have he : (localGermAlgEquiv (actualContactLocalEquivRefl n)
        (show (actualContactLocalEquivRefl n).toFun 0 = 0 from rfl)).toRingEquiv.toRingHom =
        RingHom.id (HolGerm (ComplexModel n)) := by
      apply RingHom.ext
      intro F
      exact actualContactLocalEquivRefl_germ F
    rw [he]
    exact (Ideal.map_id (I := Ideal.span (range G0.germs))).symm
  diagram_eq := rfl
  contact := by
    intro r hr
    have hzero : r = 0 := by omega
    subst r
    exact actualInheritedContactAt_zero G0

set_option linter.unusedVariables false in
/-- A true next graph extends all old contact blocks. There is no certificate
for the new graph or its Jacobian among this theorem's inputs. -/
theorem exists_actual_inherited_graph_contact_stage_succ
    (G0 : ActualAnalyticInheritedFamily n 0 K) (k : ℕ)
    (S : ActualInheritedGraphContactStage G0 k) :
    ∃ Snext : ActualInheritedGraphContactStage G0 (k+1), True := by
  obtain ⟨D, hpriority, hnew⟩ := exists_actual_inherited_next_block_graph S.family k (k+1) (Nat.le_succ k)
  let Ψ := actualBlockGraphLocalEquiv D
  have hΨ0 := actualBlockGraphLocalEquiv_zero D
  let Φ := actualContactLocalEquivComp S.chart Ψ S.zero hΨ0
  have hΦ0 := actualContactLocalEquivComp_zero S.chart Ψ S.zero hΨ0
  let Gnext := actualGraphTransformedFamily S.family D hpriority
  have hspan : Ideal.span (range Gnext.germs) =
      Ideal.map (localGermAlgEquiv Φ hΦ0).toRingEquiv.toRingHom (Ideal.span (range G0.germs)) := by
    rw [actualGraphTransformedFamily_span, S.span_eq, Ideal.map_map]
    congr 1
    apply RingHom.ext
    intro F
    exact (actualContactLocalEquivComp_germ S.chart Ψ S.zero hΨ0 F).symm
  have hdiagram : actualInitialDiagram MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom (Ideal.span (range Gnext.germs))) =
      actualInitialDiagram MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom (Ideal.span (range G0.germs))) := by
    rw [actualGraphTransformedFamily_span,
      actualInitialDiagram_map_blockGraph_analytic D hpriority, S.diagram_eq]
  refine ⟨⟨Φ, hΦ0, Gnext, hspan, hdiagram, ?_⟩, trivial⟩
  intro r hr
  by_cases hrk : r ≤ k
  · exact actualGraphTransformedFamily_contact_earlier S.family k (k+1) r (Nat.le_succ k) hrk
      D hpriority (S.contact r hrk)
  · have he : r = k+1 := by omega
    subst r
    exact actualGraphTransformedFamily_contact_next S.family k (k+1) (Nat.le_succ k)
      D hpriority (S.contact k le_rfl) hnew

/-- Genuine finite induction from the empty contact block, with no input flag. -/
def actualInheritedGraphContactStage (G0 : ActualAnalyticInheritedFamily n 0 K) :
    (k : ℕ) → ActualInheritedGraphContactStage G0 k
  | 0 => actualInheritedGraphContactStage_zero G0
  | k+1 => Classical.choose (exists_actual_inherited_graph_contact_stage_succ G0 k
      (actualInheritedGraphContactStage G0 k))

/-- The finite maximum is computed from the actual original vertex labels;
it is zero for the empty vertex set. -/
def actualInheritedContactLastDegree (K : Ideal (MvPowerSeries (Fin n) ℂ)) : ℕ :=
  (actualInitialVertices MonomialOrder.degLex K).sup normalExponentDegree

theorem actualInheritedContactLastDegree_bound
    (a : actualInitialVertices MonomialOrder.degLex K) :
    normalExponentDegree a.val ≤ actualInheritedContactLastDegree K :=
  Finset.le_sup a.property

/-- Beyond the internally computed last degree the actual coordinate block is
constant. This follows from the actual finite vertices, not a supplied flag. -/
theorem actualDegreePrefixVariables_eq_last {k : ℕ}
    (hk : actualInheritedContactLastDegree K ≤ k) :
    actualDegreePrefixVariables MonomialOrder.degLex K k =
      actualDegreePrefixVariables MonomialOrder.degLex K (actualInheritedContactLastDegree K) := by
  apply Set.Subset.antisymm
  · intro i hi
    obtain ⟨a, _ha, hai⟩ := hi
    exact ⟨a, actualInheritedContactLastDegree_bound a, hai⟩
  · exact prefix_block_mono hk

/-- One genuinely constructed finite chain supplies all nested derivative
memberships. No finite support condition for the final family is claimed. -/
theorem actualInheritedGraphContactStage_all
    (G0 : ActualAnalyticInheritedFamily n 0 K) (k : ℕ) :
    ActualInheritedContactAt
      (actualInheritedGraphContactStage G0 (actualInheritedContactLastDegree K)).family k := by
  let M := actualInheritedContactLastDegree K
  let S := actualInheritedGraphContactStage G0 M
  by_cases hk : k ≤ M
  · exact S.contact k hk
  · have hMk : M ≤ k := Nat.le_of_lt (Nat.lt_of_not_ge hk)
    intro j
    have hjM : j.val ∈ actualDegreePrefixVariables MonomialOrder.degLex K M := by
      rw [← actualDegreePrefixVariables_eq_last (K := K) hMk]
      exact j.property
    have hmem := S.contact M le_rfl ⟨j.val, hjM⟩
    have he : actualCanonicalBlockEssentialVariable MonomialOrder.degLex K M ⟨j.val, hjM⟩ =
        actualCanonicalBlockEssentialVariable MonomialOrder.degLex K k j := Subtype.ext rfl
    rw [he] at hmem
    exact coordinate_ideal_mono (prefix_block_mono hMk) hmem

/-- Unconditional graph part of the initial nested contact flag for a concrete
analytic inherited monic family. The actual input ideal is transported by a
genuine local chart and all SAME finite labels retain their heads. -/
theorem exists_actual_inherited_nested_contact_graph
    (G0 : ActualAnalyticInheritedFamily n 0 K) :
    ∃ (Φ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n))
      (hΦ0 : Φ.toFun 0 = 0) (G : ActualAnalyticInheritedFamily n 0 K),
      Ideal.span (range G.germs) =
        Ideal.map (localGermAlgEquiv Φ hΦ0).toRingEquiv.toRingHom (Ideal.span (range G0.germs)) ∧
      actualInitialDiagram MonomialOrder.degLex
          (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom (Ideal.span (range G.germs))) =
        actualInitialDiagram MonomialOrder.degLex
          (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom (Ideal.span (range G0.germs))) ∧
      (∀ k : ℕ, ActualInheritedContactAt G k) ∧
      ∀ k : ℕ, (actualInheritedBlockJacobian G k).det ≠ 0 := by
  let S := actualInheritedGraphContactStage G0 (actualInheritedContactLastDegree K)
  exact ⟨S.chart, S.zero, S.family, S.span_eq, S.diagram_eq,
    actualInheritedGraphContactStage_all G0,
    actualInheritedBlockJacobian_det_ne_zero S.family⟩

/-- Original-I-only nested derivative/contact memberships. The initial SAME
canonical analytic family is produced internally; the final family is an
inherited monic family, without a new canonical reduction or support claim. -/
theorem exists_original_initial_nested_contact_graph (n : ℕ)
    (I : Ideal (HolGerm (ComplexModel n))) :
    let K := Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I
    ∃ (Φ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n))
      (hΦ0 : Φ.toFun 0 = 0) (G : ActualAnalyticInheritedFamily n 0 K),
      Ideal.span (range G.germs) =
        Ideal.map (localGermAlgEquiv Φ hΦ0).toRingEquiv.toRingHom I ∧
      actualInitialDiagram MonomialOrder.degLex
          (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom (Ideal.span (range G.germs))) =
        actualInitialDiagram MonomialOrder.degLex K ∧
      (∀ k : ℕ, ActualInheritedContactAt G k) ∧
      ∀ k : ℕ, (actualInheritedBlockJacobian G k).det ≠ 0 := by
  let K := Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I
  obtain ⟨B, hB, hspan⟩ := exists_actualAnalyticCanonicalVertexFamily n I
  let G0 : ActualAnalyticInheritedFamily n 0 K := {
    germs := B
    monic := fun a => (hB a).2.2.choose_spec.2
    lower := by
      intro a β hβ
      change MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom n (B a)) = 0
      rw [(hB a).2.1]
      exact actualReducedVertexSeries_coefficient_lower MonomialOrder.degLex K a β hβ }
  have hspan0 : Ideal.span (range G0.germs) = I := hspan
  obtain ⟨Φ, hΦ0, G, hnewspan, hdiagram, hcontact, hJac⟩ :=
    exists_actual_inherited_nested_contact_graph G0
  exact ⟨Φ, hΦ0, G, by simpa only [hspan0] using hnewspan,
    by simpa only [hspan0] using hdiagram, hcontact, hJac⟩

/-- Whole selected analytic division is performed on the SAME current
degree-prefix members. Its construction is the actual Cauchy division, not
the previously accepted finite normal-q matrix adjustment. -/
def actualInheritedWholePrefixFamily (G : ActualAnalyticInheritedFamily n 0 K) (k : ℕ) :
    ActualAnalyticInheritedFamily n 0 K :=
  actualInheritedWholeSelectedFamily G (actualDegreeBlockVertices K k)

theorem actualInheritedWholePrefixFamily_data
    (G : ActualAnalyticInheritedFamily n 0 K) (k : ℕ) :
    (∀ a, normalExponentDegree a.val ≤ k →
      (actualInheritedWholePrefixFamily G k).germs a = G.germs a) ∧
    Ideal.span (range (actualInheritedWholePrefixFamily G k).germs) = Ideal.span (range G.germs) ∧
    ActualInheritedPrefixReducedAt (actualInheritedWholePrefixFamily G k) k := by
  obtain ⟨hfixed, hspan, hzero⟩ :=
    actual_inherited_whole_selected_adjustment G (actualDegreeBlockVertices K k)
  refine ⟨hfixed, hspan, ?_⟩
  intro a ha b hb α hbα
  exact hzero a (by
    change ¬ normalExponentDegree a.val ≤ k
    omega) α ⟨b, hb, hbα⟩

/-- An internally constructed whole-support stage; the graph part carries the
true accumulated chart, generated ideal, entire diagram and all contacts. -/
structure ActualInheritedWholeContactStage (G0 : ActualAnalyticInheritedFamily n 0 K) (k : ℕ) where
  graph : ActualInheritedGraphContactStage G0 k
  reduced : ∀ r : ℕ, r ≤ k → ActualInheritedPrefixReducedAt graph.family r

def actualInheritedWholeContactStage_zero (G0 : ActualAnalyticInheritedFamily n 0 K) :
    ActualInheritedWholeContactStage G0 0 where
  graph := actualInheritedGraphContactStage_zero G0
  reduced := by
    intro r hr
    have hzero : r = 0 := by omega
    subst r
    exact actualInheritedPrefixReducedAt_zero G0

set_option linter.unusedVariables false in
/-- The actual next IFT graph and actual whole selected analytic division
jointly construct the new state. Only a previously constructed state is an
internal input; the original-only theorem starts from the proved empty state. -/
theorem actual_inherited_whole_contact_block_extension
    (G0 : ActualAnalyticInheritedFamily n 0 K) (k : ℕ)
    (S : ActualInheritedWholeContactStage G0 k) :
    ∃ Snext : ActualInheritedWholeContactStage G0 (k+1), True := by
  obtain ⟨D, hpriority, hnew⟩ :=
    exists_actual_inherited_next_block_graph S.graph.family k (k+1) (Nat.le_succ k)
  let Ψ := actualBlockGraphLocalEquiv D
  have hΨ0 := actualBlockGraphLocalEquiv_zero D
  let Φ := actualContactLocalEquivComp S.graph.chart Ψ S.graph.zero hΨ0
  have hΦ0 := actualContactLocalEquivComp_zero S.graph.chart Ψ S.graph.zero hΨ0
  let H := actualGraphTransformedFamily S.graph.family D hpriority
  let Gnext := actualInheritedWholePrefixFamily H (k+1)
  obtain ⟨hfixed, hadjustspan, hnewred⟩ := actualInheritedWholePrefixFamily_data H (k+1)
  have hgraphcontact : ∀ r : ℕ, r ≤ k+1 → ActualInheritedContactAt H r := by
    intro r hr
    by_cases hrk : r ≤ k
    · exact actualGraphTransformedFamily_contact_earlier S.graph.family k (k+1) r
        (Nat.le_succ k) hrk D hpriority (S.graph.contact r hrk)
    · have he : r = k+1 := by omega
      subst r
      exact actualGraphTransformedFamily_contact_next S.graph.family k (k+1)
        (Nat.le_succ k) D hpriority (S.graph.contact k le_rfl) hnew
  have hcontact : ∀ r : ℕ, r ≤ k+1 → ActualInheritedContactAt Gnext r := by
    intro r hr
    exact actualInheritedContactAt_of_fixed_prefix H Gnext r (k+1) hr hfixed (hgraphcontact r hr)
  have hred : ∀ r : ℕ, r ≤ k+1 → ActualInheritedPrefixReducedAt Gnext r := by
    intro r hr
    by_cases hrk : r ≤ k
    · have hgraphred : ActualInheritedPrefixReducedAt H r :=
        actualGraphTransformedFamily_prefix_reduced S.graph.family r (k+1)
          (hrk.trans (Nat.le_succ k)) D hpriority (S.reduced r hrk)
      exact actualInheritedPrefixReducedAt_of_fixed_and_larger H Gnext r (k+1) hr
        hfixed hnewred hgraphred
    · have he : r = k+1 := by omega
      subst r
      exact hnewred
  have hspan : Ideal.span (range Gnext.germs) =
      Ideal.map (localGermAlgEquiv Φ hΦ0).toRingEquiv.toRingHom (Ideal.span (range G0.germs)) := by
    rw [hadjustspan, actualGraphTransformedFamily_span, S.graph.span_eq, Ideal.map_map]
    congr 1
    apply RingHom.ext
    intro F
    exact (actualContactLocalEquivComp_germ S.graph.chart Ψ S.graph.zero hΨ0 F).symm
  have hdiagram : actualInitialDiagram MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom (Ideal.span (range Gnext.germs))) =
      actualInitialDiagram MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom (Ideal.span (range G0.germs))) := by
    rw [hadjustspan, actualGraphTransformedFamily_span,
      actualInitialDiagram_map_blockGraph_analytic D hpriority, S.graph.diagram_eq]
  exact ⟨⟨⟨Φ, hΦ0, Gnext, hspan, hdiagram, hcontact⟩, hred⟩, trivial⟩

/-- Actual finite recursion combines the genuine IFT and whole analytic
division producers. It is not a family of supplied flag certificates. -/
def actualInheritedWholeContactStage (G0 : ActualAnalyticInheritedFamily n 0 K) :
    (k : ℕ) → ActualInheritedWholeContactStage G0 k
  | 0 => actualInheritedWholeContactStage_zero G0
  | k+1 => Classical.choose (actual_inherited_whole_contact_block_extension G0 k
      (actualInheritedWholeContactStage G0 k))

/-- A finite internal construction supplies ALL nested contact and ALL whole
prefix coefficient conditions simultaneously for the final inherited family. -/
theorem exists_actual_inherited_whole_nested_contact_flag
    (G0 : ActualAnalyticInheritedFamily n 0 K) :
    ∃ (Φ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n))
      (hΦ0 : Φ.toFun 0 = 0) (G : ActualAnalyticInheritedFamily n 0 K),
      Ideal.span (range G.germs) =
        Ideal.map (localGermAlgEquiv Φ hΦ0).toRingEquiv.toRingHom (Ideal.span (range G0.germs)) ∧
      actualInitialDiagram MonomialOrder.degLex
          (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom (Ideal.span (range G.germs))) =
        actualInitialDiagram MonomialOrder.degLex
          (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom (Ideal.span (range G0.germs))) ∧
      (∀ k : ℕ, ActualInheritedContactAt G k) ∧
      (∀ k : ℕ, ActualInheritedPrefixReducedAt G k) ∧
      ∀ k : ℕ, (actualInheritedBlockJacobian G k).det ≠ 0 := by
  let M := actualInheritedContactLastDegree K
  let S := actualInheritedWholeContactStage G0 M
  refine ⟨S.graph.chart, S.graph.zero, S.graph.family, S.graph.span_eq, S.graph.diagram_eq,
    ?_, ?_, actualInheritedBlockJacobian_det_ne_zero S.graph.family⟩
  · intro k
    by_cases hk : k ≤ M
    · exact S.graph.contact k hk
    · have hMk : M ≤ k := Nat.le_of_lt (Nat.lt_of_not_ge hk)
      intro j
      have hjM : j.val ∈ actualDegreePrefixVariables MonomialOrder.degLex K M := by
        rw [← actualDegreePrefixVariables_eq_last (K := K) hMk]
        exact j.property
      have hmem := S.graph.contact M le_rfl ⟨j.val, hjM⟩
      have he : actualCanonicalBlockEssentialVariable MonomialOrder.degLex K M ⟨j.val, hjM⟩ =
          actualCanonicalBlockEssentialVariable MonomialOrder.degLex K k j := Subtype.ext rfl
      rw [he] at hmem
      exact coordinate_ideal_mono (prefix_block_mono hMk) hmem
  · intro k
    by_cases hk : k ≤ M
    · exact S.reduced k hk
    · intro a ha _b _hb _α _hbα
      have hbound := actualInheritedContactLastDegree_bound a
      omega

/-- The original ideal itself supplies the initial whole canonical analytic
family and hence the complete initial whole nested contact flag. No flag,
normal flatness, desired support or Jacobian certificate is supplied. -/
theorem exists_original_initial_whole_nested_contact_flag (n : ℕ)
    (I : Ideal (HolGerm (ComplexModel n))) :
    let K := Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I
    ∃ (Φ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n))
      (hΦ0 : Φ.toFun 0 = 0) (G : ActualAnalyticInheritedFamily n 0 K),
      Ideal.span (range G.germs) =
        Ideal.map (localGermAlgEquiv Φ hΦ0).toRingEquiv.toRingHom I ∧
      actualInitialDiagram MonomialOrder.degLex
          (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom (Ideal.span (range G.germs))) =
        actualInitialDiagram MonomialOrder.degLex K ∧
      (∀ k : ℕ, ActualInheritedContactAt G k) ∧
      (∀ k : ℕ, ActualInheritedPrefixReducedAt G k) ∧
      ∀ k : ℕ, (actualInheritedBlockJacobian G k).det ≠ 0 := by
  let K := Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I
  obtain ⟨B, hB, hspan⟩ := exists_actualAnalyticCanonicalVertexFamily n I
  let G0 : ActualAnalyticInheritedFamily n 0 K := {
    germs := B
    monic := fun a => (hB a).2.2.choose_spec.2
    lower := by
      intro a β hβ
      change MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom n (B a)) = 0
      rw [(hB a).2.1]
      exact actualReducedVertexSeries_coefficient_lower MonomialOrder.degLex K a β hβ }
  have hspan0 : Ideal.span (range G0.germs) = I := hspan
  obtain ⟨Φ, hΦ0, G, hnewspan, hdiagram, hcontact, hred, hJac⟩ :=
    exists_actual_inherited_whole_nested_contact_flag G0
  exact ⟨Φ, hΦ0, G, by simpa only [hspan0] using hnewspan,
    by simpa only [hspan0] using hdiagram, hcontact, hred, hJac⟩

end

end Hironaka.HironakaActualInheritedNestedContactFlag
