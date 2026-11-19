import Hironaka.Resolution.HironakaChowAnalyticBaseChangeUniformTails
import Hironaka.Resolution.HironakaChowOriginalFibreSupportedDivision
import Hironaka.Resolution.HironakaChowFibreSupportedUniqueness
import Hironaka.Resolution.HironakaChowFibreDivisionRemainder

/-! Actual SAME-family analytic-base-change division and remainder naturality.
Target uniform data and native inverse are PRODUCED internally; no target
packet or remainder-naturality certificate is input. BP FIRST:
hironaka-g10-analytic-base-change-division.tex. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology
namespace Hironaka.HironakaChowAnalyticBaseChangeDivision
noncomputable section
open HolGerm HironakaRelativeNormalIdeal HironakaChowNormalSupportProjection
  HironakaActualCoefficientPresentationCentrePower HironakaActualWeightedVertexSmallTails
  HironakaChowFibreLiftUniformTails HironakaChowOriginalFibreSupportedDivision
  HironakaChowFibreSupportedUniqueness HironakaChowFibreSupportModules
  HironakaChowFibreDivisionRemainder HironakaChowAnalyticBaseChangeUniformTails
  HironakaActualAnalyticBaseChangeCoefficients HironakaActualJointBaseFibre
  HironakaActualCauchyMonomialDivision HironakaActualCauchyDiagramPartition

variable (d t : ℕ)
local instance : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) := tangentAlgebra d t

/-- Generic EXISTING analytic division/zero-uniqueness constructs the SAME native inverse. -/
theorem exists_linear_division_for_produced_data (I : Ideal (HolGerm (ComplexModel (d+t))))
    (P : FibreLiftUniformTailData d t I) :
    ∃ e : fibreDivisionModule d t I ≃ₗ[HolGerm (ComplexModel d)] HolGerm (ComplexModel (d+t)),
      ∀ z, e z = supportedReassembly d t I P z := by
  let f := supportedReassembly d t I P
  have hs : Function.Surjective f := by
    intro g
    obtain ⟨q,r,hEq,hq,hr⟩ := exists_supported_division_for_original_data d t I P g
    refine ⟨((fun j => ⟨q j,(mem_fibreQuotientModule_iff d t I j (q j)).mpr (hq j)⟩),
      ⟨r,(mem_fibreRemainderModule_iff d t I r).mpr hr⟩),hEq.symm⟩
  have hi : Function.Injective f := by
    apply (LinearMap.ker_eq_bot).mp
    apply le_antisymm _ bot_le
    intro z hz
    have hZero := supported_zero_for_original_data d t I P
      (fun j => (z.1 j : HolGerm (ComplexModel (d+t)))) (z.2 : HolGerm (ComplexModel (d+t))) hz
      (fun j => (mem_fibreQuotientModule_iff d t I j _).mp (z.1 j).property)
      ((mem_fibreRemainderModule_iff d t I _).mp z.2.property)
    change z = 0
    apply Prod.ext
    · funext j
      apply Subtype.ext
      exact hZero.1 j
    · apply Subtype.ext
      exact hZero.2
  exact ⟨LinearEquiv.ofBijective f ⟨hi,hs⟩,fun _ => rfl⟩

/- Native original mask readback. No new support predicate/module is introduced. -/
private theorem joined_le (b t : ℕ) (α β : Fin t →₀ ℕ) :
    actualJoinedExponent (0 : Fin b →₀ ℕ) α ≤ actualJoinedExponent (0 : Fin b →₀ ℕ) β ↔ α ≤ β := by
  constructor
  · intro h i
    simpa [actualJoinedExponent] using h (i.natAdd b)
  · intro h i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [actualJoinedExponent]
    · simpa [actualJoinedExponent] using h j

private theorem joined_le_add (b t : ℕ) (α β γ : Fin t →₀ ℕ) :
    actualJoinedExponent (0 : Fin b →₀ ℕ) α ≤
      actualJoinedExponent (0 : Fin b →₀ ℕ) β + actualJoinedExponent (0 : Fin b →₀ ℕ) γ ↔ α ≤ β+γ := by
  constructor
  · intro h i
    simpa [actualJoinedExponent] using h (i.natAdd b)
  · intro h i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [actualJoinedExponent]
    · simpa [actualJoinedExponent] using h j

private theorem quotient_masks_dimensions (d e t k : ℕ) (a : Fin k → Fin t →₀ ℕ) (j : Fin k) :
    assignedQuotientNormalMask (fun i => wordOfExponent (actualJoinedExponent (0 : Fin d →₀ ℕ) (a i))) j =
      assignedQuotientNormalMask (fun i => wordOfExponent (actualJoinedExponent (0 : Fin e →₀ ℕ) (a i))) j := by
  ext γ
  simp only [assignedQuotientNormalMask,Set.mem_ofPred_eq,AvoidsCones]
  rw [List.ofFn_comp' a (fun α => wordOfExponent (actualJoinedExponent (0 : Fin d →₀ ℕ) α)),
    ← List.map_take,List.forall_mem_map,
    List.ofFn_comp' a (fun α => wordOfExponent (actualJoinedExponent (0 : Fin e →₀ ℕ) α)),
    ← List.map_take,List.forall_mem_map]
  simp only [wordExponent_wordOfExponent,joined_le_add]

private theorem remainder_masks_dimensions (d e t k : ℕ) (a : Fin k → Fin t →₀ ℕ) :
    assignedRemainderNormalMask (fun i => wordOfExponent (actualJoinedExponent (0 : Fin d →₀ ℕ) (a i))) =
      assignedRemainderNormalMask (fun i => wordOfExponent (actualJoinedExponent (0 : Fin e →₀ ℕ) (a i))) := by
  ext γ
  simp only [assignedRemainderNormalMask,Set.mem_ofPred_eq,AvoidsCones]
  rw [List.ofFn_comp' a (fun α => wordOfExponent (actualJoinedExponent (0 : Fin d →₀ ℕ) α)),
    List.forall_mem_map,
    List.ofFn_comp' a (fun α => wordOfExponent (actualJoinedExponent (0 : Fin e →₀ ℕ) α)),
    List.forall_mem_map]
  simp only [wordExponent_wordOfExponent,joined_le]

private def normalEnumeration (t : ℕ) (J : Ideal (HolGerm (ComplexModel t))) :
    Fin (Fintype.card (ActualVertexIndex t J)) → Fin t →₀ ℕ :=
  fun j => ((Fintype.equivFin (ActualVertexIndex t J)).symm j).val

private def indexEquiv {t : ℕ} {J K : Ideal (HolGerm (ComplexModel t))} (h : K = J) :
    Fin (Fintype.card (ActualVertexIndex t K)) ≃ Fin (Fintype.card (ActualVertexIndex t J)) :=
  finCongr (congrArg (fun Q : Ideal (HolGerm (ComplexModel t)) => Fintype.card (ActualVertexIndex t Q)) h)

private theorem vertex_enum_transport {t : ℕ} {J K : Ideal (HolGerm (ComplexModel t))}
    (h : K = J) (j : Fin (Fintype.card (ActualVertexIndex t K))) :
    fibreVertexEquiv h ((Fintype.equivFin (ActualVertexIndex t K)).symm j) =
      (Fintype.equivFin (ActualVertexIndex t J)).symm (indexEquiv h j) := by
  subst K
  rfl

private theorem quotient_masks_transport (d e t : ℕ) {J K : Ideal (HolGerm (ComplexModel t))}
    (h : K = J) (j : Fin (Fintype.card (ActualVertexIndex t K))) :
    assignedQuotientNormalMask (fun i => wordOfExponent
      (actualJoinedExponent (0 : Fin e →₀ ℕ) (normalEnumeration t K i))) j =
      assignedQuotientNormalMask (fun i => wordOfExponent
        (actualJoinedExponent (0 : Fin d →₀ ℕ) (normalEnumeration t J i))) (indexEquiv h j) := by
  subst K
  exact quotient_masks_dimensions e d t _ (normalEnumeration t J) j

private theorem remainder_masks_transport (d e t : ℕ) {J K : Ideal (HolGerm (ComplexModel t))}
    (h : K = J) :
    assignedRemainderNormalMask (fun i => wordOfExponent
      (actualJoinedExponent (0 : Fin e →₀ ℕ) (normalEnumeration t K i))) =
      assignedRemainderNormalMask (fun i => wordOfExponent
        (actualJoinedExponent (0 : Fin d →₀ ℕ) (normalEnumeration t J i))) := by
  subst K
  exact remainder_masks_dimensions e d t _ (normalEnumeration t J)

private def pulledTuple (d e t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t))))
    (φ : ComplexModel e → ComplexModel d)
    (hφ : ∀ᶠ v in nhds (0 : ComplexModel e), DifferentiableAt ℂ φ v) (hφ0 : φ 0 = 0)
    (z : fibreDivisionModule d t I) :
    fibreDivisionModule e t (Ideal.map (jointBasePullback d e t φ hφ hφ0).toRingHom I) := by
  let IB := Ideal.map (jointBasePullback d e t φ hφ hφ0).toRingHom I
  let hJ := base_changed_fibre_ideal_eq d e t I φ hφ hφ0
  let k := indexEquiv hJ
  refine (fun j => ⟨jointBasePullback d e t φ hφ hφ0 (z.1 (k j) : HolGerm (ComplexModel (d+t))),?_⟩,
    ⟨jointBasePullback d e t φ hφ hφ0 (z.2 : HolGerm (ComplexModel (d+t))),?_⟩)
  · change jointBasePullback d e t φ hφ hφ0 (z.1 (k j) : HolGerm (ComplexModel (d+t))) ∈
      normalSupportSubmodule e t (assignedQuotientNormalMask (fibreHeadWords e t IB) j)
    have hm := quotient_masks_transport d e t hJ j
    change assignedQuotientNormalMask (fibreHeadWords e t IB) j =
      assignedQuotientNormalMask (fibreHeadWords d t I) (k j) at hm
    rw [hm]
    exact jointBasePullback_mem_normalSupportSubmodule d e t φ hφ hφ0 _ _ (z.1 (k j)).property
  · change jointBasePullback d e t φ hφ hφ0 (z.2 : HolGerm (ComplexModel (d+t))) ∈
      normalSupportSubmodule e t (assignedRemainderNormalMask (fibreHeadWords e t IB))
    have hm := remainder_masks_transport d e t hJ
    change assignedRemainderNormalMask (fibreHeadWords e t IB) =
      assignedRemainderNormalMask (fibreHeadWords d t I) at hm
    rw [hm]
    exact jointBasePullback_mem_normalSupportSubmodule d e t φ hφ hφ0 _ _ z.2.property

private theorem reassembly_base_change (d e t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (P : FibreLiftUniformTailData d t I)
    (φ : ComplexModel e → ComplexModel d)
    (hφ : ∀ᶠ v in nhds (0 : ComplexModel e), DifferentiableAt ℂ φ v) (hφ0 : φ 0 = 0)
    (PB : FibreLiftUniformTailData e t (Ideal.map (jointBasePullback d e t φ hφ hφ0).toRingHom I))
    (hLift : ∀ a, PB.lift a = jointBasePullback d e t φ hφ hφ0
      (P.lift (fibreVertexEquiv (base_changed_fibre_ideal_eq d e t I φ hφ hφ0) a)))
    (z : fibreDivisionModule d t I) :
    supportedReassembly e t _ PB (pulledTuple d e t I φ hφ hφ0 z) =
      jointBasePullback d e t φ hφ hφ0 (supportedReassembly d t I P z) := by
  let hJ := base_changed_fibre_ideal_eq d e t I φ hφ hφ0
  let k := indexEquiv hJ
  have hF (j) : PB.lift (fibreEnumeration e t _ j) = jointBasePullback d e t φ hφ hφ0
      (P.lift (fibreEnumeration d t I (k j))) := by
    rw [hLift]
    congr 2
    exact vertex_enum_transport hJ j
  change (∑ j, jointBasePullback d e t φ hφ hφ0 (z.1 (k j) : HolGerm (ComplexModel (d+t))) *
      PB.lift (fibreEnumeration e t _ j)) +
        jointBasePullback d e t φ hφ hφ0 (z.2 : HolGerm (ComplexModel (d+t))) =
    jointBasePullback d e t φ hφ hφ0
      ((∑ j, (z.1 j : HolGerm (ComplexModel (d+t))) * P.lift (fibreEnumeration d t I j)) +
        (z.2 : HolGerm (ComplexModel (d+t))))
  rw [map_add,map_sum]
  simp_rw [map_mul,hF]
  congr 1
  exact k.sum_comp (fun j => jointBasePullback d e t φ hφ hφ0 (z.1 j : HolGerm (ComplexModel (d+t))) *
    jointBasePullback d e t φ hφ hφ0 (P.lift (fibreEnumeration d t I j)))

/-- SAME original analytic family internally produces actual target division and R-naturality. -/
theorem exists_same_base_changed_linear_division (d e t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (P : FibreLiftUniformTailData d t I)
    (eA : fibreDivisionModule d t I ≃ₗ[HolGerm (ComplexModel d)] HolGerm (ComplexModel (d+t)))
    (hEA : ∀ z, eA z = supportedReassembly d t I P z)
    (φ : ComplexModel e → ComplexModel d)
    (hφ : ∀ᶠ v in nhds (0 : ComplexModel e), DifferentiableAt ℂ φ v) (hφ0 : φ 0 = 0) :
    let IB := Ideal.map (jointBasePullback d e t φ hφ hφ0).toRingHom I
    let hJ := base_changed_fibre_ideal_eq d e t I φ hφ hφ0
    ∃ (PB : FibreLiftUniformTailData e t IB)
      (eB : fibreDivisionModule e t IB ≃ₗ[HolGerm (ComplexModel e)] HolGerm (ComplexModel (e+t))),
      PB.fibre = transportFibreData hJ P.fibre ∧ PB.baseWeight = P.baseWeight ∧ PB.bound = P.bound ∧
      (∀ a, PB.lift a = jointBasePullback d e t φ hφ hφ0 (P.lift (fibreVertexEquiv hJ a))) ∧
      (∀ z, eB z = supportedReassembly e t IB PB z) ∧
      ∀ g : HolGerm (ComplexModel (d+t)),
        (divisionRemainder e t IB eB (jointBasePullback d e t φ hφ hφ0 g) : HolGerm (ComplexModel (e+t))) =
          jointBasePullback d e t φ hφ hφ0 (divisionRemainder d t I eA g : HolGerm (ComplexModel (d+t))) := by
  let IB := Ideal.map (jointBasePullback d e t φ hφ hφ0).toRingHom I
  obtain ⟨PB,hFib,hL,hBound,hLift⟩ := exists_same_base_changed_uniform_tails d e t I P φ hφ hφ0
  obtain ⟨eB,hEB⟩ := exists_linear_division_for_produced_data e t IB PB
  refine ⟨PB,eB,hFib,hL,hBound,hLift,hEB,?_⟩
  intro g
  have hsq := reassembly_base_change d e t I P φ hφ hφ0 PB hLift (eA.symm g)
  have hTarget : eB (pulledTuple d e t I φ hφ hφ0 (eA.symm g)) = jointBasePullback d e t φ hφ hφ0 g := by
    rw [hEB,hsq,← hEA (eA.symm g),eA.apply_symm_apply]
  have hInv : eB.symm (jointBasePullback d e t φ hφ hφ0 g) = pulledTuple d e t I φ hφ hφ0 (eA.symm g) := by
    rw [← hTarget,eB.symm_apply_apply]
  exact congrArg (fun z : fibreDivisionModule e t IB => (z.2 : HolGerm (ComplexModel (e+t)))) hInv

end
end Hironaka.HironakaChowAnalyticBaseChangeDivision
