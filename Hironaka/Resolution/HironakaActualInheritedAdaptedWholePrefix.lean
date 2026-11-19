import Hironaka.Resolution.HironakaActualInheritedWholePrefixNormalization
import Hironaka.Resolution.HironakaActualNormalAllDirectionConverse

/-! The SAME full inherited whole-prefix support after the internally produced
normal adaptation. Marked orders choose the pivot and produce actual CURRENT
labels and the whole strict diagram; those are not caller certificates.
This source-only consumer does not assert the entire historical HS phase. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualInheritedAdaptedWholePrefix
noncomputable section
open HironakaRelativeNormalMonomialBasis HironakaActualFormalInitialDiagram
  HironakaActualOriginalFormalHSTransfer HironakaActualFormalBlowupAllDirections
  HironakaActualReducedBasisDivision HironakaActualFormalCoordinatePowerDivision
  HironakaActualFormalBlowupMemberGeneration HironakaActualFormalStrictGenerators
  HironakaActualRelativeStandardnessInheritedDivision HironakaActualNormalZeroOwnerSupport
  HironakaActualNormalZeroOwnerConverse HironakaActualNormalZeroFormalSaturation
  HironakaActualNormalMarkedDirection HironakaActualNormalAllDirectionConverse
  HironakaActualRelativeStandardnessNormalPivotPriority HironakaActualInheritedSourceOwnerPermutation
  HironakaActualInheritedWholePrefixNormalization

set_option linter.unusedVariables false in
/-- Genuine source marked orders and source whole prefix support produce the
SAME adapted CURRENT family and its ENTIRE normalized whole prefix support.
No target diagram, normalized support or HS equality is an input. -/
theorem exists_same_normal_adapted_family_with_whole_prefix {n : ℕ}
    (K : Ideal (MvPowerSeries (Fin (n+1)) ℂ))
    (B : ActualMonicVertexFamily MonomialOrder.degLex K)
    (q e : Fin (n+1)) (hqe : q ≤ e) (b : Fin (n+1) → ℂ)
    (hpower : ∀ a, B.series a ∈
      actualFormalCoordinateIdeal (n+1) (Set.Ici q) ^ normalExponentDegree a.val)
    (horder : ∀ a, actualNormalizedFormalMember (Set.Ici q) e hqe b
      (normalExponentDegree a.val) (B.series a) (hpower a) ∈
        genuineFormalVariables (n+1) ^ normalExponentDegree a.val)
    (hprefix : ∀ a c : actualInitialVertices MonomialOrder.degLex K,
      normalExponentDegree c.val < normalExponentDegree a.val →
        ∀ α : Fin (n+1) →₀ ℕ, c.val ≤ α → MvPowerSeries.coeff α (B.series a) = 0) :
    ∃ f : Fin (n+1), ∃ hqf : q ≤ f,
      actualNormalMarkedDirection (Set.Ici q) e b f ≠ 0 ∧
      ∃ E : actualInitialVertices MonomialOrder.degLex K ≃
        actualInitialVertices MonomialOrder.degLex (actualNormalAdaptedSourceIdeal K q e f b),
      ∃ BP : ActualMonicVertexFamily MonomialOrder.degLex
        (actualNormalAdaptedSourceIdeal K q e f b),
      ∃ hp : ∀ a, BP.series a ∈
        actualFormalCoordinateIdeal (n+1) (Set.Ici q) ^ normalExponentDegree a.val,
      (∀ a, (E a).val = Finsupp.domCongr (normalPivotEquiv q f) a.val) ∧
      (∀ a, BP.series (E a) = normalPivotRename q f
        (actualFormalCenterShear (Set.Ici q) f
          (fun i => actualNormalMarkedDirection (Set.Ici q) e b i /
            actualNormalMarkedDirection (Set.Ici q) e b f) (B.series a))) ∧
      actualInitialDiagram MonomialOrder.degLex
        (actualFormalStrictTransform (actualNormalAdaptedSourceIdeal K q e f b)
          (Set.Ici q) q (Set.mem_Ici.mpr (le_refl q)) (fun _ => 0)) =
        actualInitialDiagram MonomialOrder.degLex (actualNormalAdaptedSourceIdeal K q e f b) ∧
      (∀ a c : actualInitialVertices MonomialOrder.degLex
          (actualNormalAdaptedSourceIdeal K q e f b),
        normalExponentDegree c.val < normalExponentDegree a.val →
          ∀ α : Fin (n+1) →₀ ℕ, c.val ≤ α →
            MvPowerSeries.coeff α
              (sameMonicZeroNormalizedVertex (actualNormalAdaptedSourceIdeal K q e f b)
                BP q hp a) = 0) := by
  obtain ⟨f, hqf, hvf, E, BP, hp, hlabel, hliteral, horders, _hhs, _hstrict⟩ :=
    exists_same_formal_normal_adapted_family_of_marked_orders K B q e hqe b hpower horder
  let KP := actualNormalAdaptedSourceIdeal K q e f b
  let p := normalPivotEquiv q f
  let w (i : Fin (n+1)) := actualNormalMarkedDirection (Set.Ici q) e b i /
    actualNormalMarkedDirection (Set.Ici q) e b f
  have hpure (a : actualInitialVertices MonomialOrder.degLex KP)
      (i : Fin (n+1)) (hi : i ≤ q) : a.val i = 0 :=
    pure_tail_of_monic_normal_mark_and_normalized_order q a.val (BP.series a)
      (BP.monic a) (hp a) (horders a) i hi
  have hval (a : actualInitialVertices MonomialOrder.degLex K) (i : Fin (n+1)) :
      (E a).val (p i) = a.val i := by
    rw [hlabel]
    simp only [p, sourceExponentPermutation_apply, Equiv.symm_apply_apply]
  have hdegree (a : actualInitialVertices MonomialOrder.degLex K) :
      normalExponentDegree (E a).val = normalExponentDegree a.val := by
    rw [hlabel]
    exact sourceExponentPermutation_degree p a.val
  have hsourceLegal (a : actualInitialVertices MonomialOrder.degLex K) :
      (↑a.val.support : Set (Fin (n+1))) ⊆ Set.Ici q \ {f} := by
    intro i hi
    have hine : a.val i ≠ 0 := Finsupp.mem_support_iff.mp hi
    refine ⟨?_, ?_⟩
    · by_contra hiq
      have hlt : i < q := lt_of_not_ge hiq
      have hpi : p i = i := normalPivotEquiv_tangent q f hqf i hlt
      exact hine ((hval a i).symm.trans (hpure (E a) (p i)
        (by rw [hpi]; exact le_of_lt hlt)))
    · simp only [Set.mem_singleton_iff]
      intro hif
      subst i
      exact hine ((hval a f).symm.trans (hpure (E a) (p f)
        (by rw [show p f = q from normalPivotEquiv_pivot q f hqf])))
  have htargetLegal (a : actualInitialVertices MonomialOrder.degLex KP) :
      (↑a.val.support : Set (Fin (n+1))) ⊆ Set.Ici q \ {q} := by
    intro i hi
    have hine : a.val i ≠ 0 := Finsupp.mem_support_iff.mp hi
    have hqi : q < i := lt_of_not_ge (fun hiq => hine (hpure a i hiq))
    exact ⟨le_of_lt hqi, by simpa only [Set.mem_singleton_iff] using ne_of_gt hqi⟩
  have hD : actualInitialDiagram MonomialOrder.degLex
      (actualFormalStrictTransform KP (Set.Ici q) q (Set.mem_Ici.mpr (le_refl q)) (fun _ => 0)) =
        actualInitialDiagram MonomialOrder.degLex KP :=
    (actual_normal_zero_strict_diagram_and_hs_of_inherited_marked_orders KP KP
      (⟨BP.series, BP.monic, BP.lower⟩ : InheritedMonicFamily MonomialOrder.degLex KP)
      rfl BP.mem q hp horders).2.1
  refine ⟨f, hqf, hvf, E, BP, hp, hlabel, hliteral, hD, ?_⟩
  intro a c hca α hcα
  obtain ⟨a, rfl⟩ := E.surjective a
  obtain ⟨c, rfl⟩ := E.surjective c
  have hcaSource : normalExponentDegree c.val < normalExponentDegree a.val := by
    simpa only [hdegree] using hca
  have hcone : ∀ γ : Fin (n+1) →₀ ℕ, (E c).val ≤ γ →
      MvPowerSeries.coeff γ (BP.series (E a)) = 0 := by
    rw [hliteral a, hlabel c]
    exact shear_rename_cone_zero (Set.Ici q) f hqf w p c.val
      (hsourceLegal c) (B.series a) (hprefix a c hcaSource)
  exact actualNormalizedFormalMember_cone_zero (Set.Ici q) q (Set.mem_Ici.mpr (le_refl q)) (fun _ => 0)
    (E c).val (htargetLegal (E c)) (normalExponentDegree (E a).val)
    (le_of_lt hca) (BP.series (E a)) (hp (E a)) hcone α hcα

end
end Hironaka.HironakaActualInheritedAdaptedWholePrefix
