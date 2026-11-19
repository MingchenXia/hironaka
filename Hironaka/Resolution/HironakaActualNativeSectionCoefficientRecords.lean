import Hironaka.Resolution.HironakaActualNativeSectionDifferentialIdeals
import Hironaka.Resolution.HironakaActualNativeSectionIncidentBoundary

/-! Whole original coefficient/homogenized/bar and selected-member records
on the SAME actual native model. All ordered positions are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualNativeSectionCoefficientRecords
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal SubmanifoldChartedSpace
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionDifferentialIdeals
  HironakaActualNativeSectionIncidentBoundary HironakaActualNonregularCoefficientNaturality
  IdealWeightPowers InvertibleIdealQuotient RelativePrincipalizationSpan GermIdealOrder
  DerivativeIdealAlong HomogenizedIdealAlong HomogenizedEquivalence HomogenizedGlueing CoefficientIdeal GiraudAlong
  InvDomainMemberRestriction InvDomainRebase
  NormalCrossings
variable {n k : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] {W : Set X}

theorem pullback_native_homogenizedIdealAlong (hk : k≤n)
    (hW : ∀x∈W,RegularAtDim (n:=n) W x k) :
    letI := chartedSpace hk hW
    letI := isComplexManifold_chartedSpace hk hW
    ∀(N : Set X)(_hNW : N⊆W)(I : GermIdeal n X)
      (_hI : ∀x g,I.mem x g → HolomorphicAt n g x)(d : ℕ),
      GermIdeal.pullback (m:=k) (Subtype.val : W→X) (homogenizedIdealAlong N I d)=
        homogenizedIdealAlong ((Subtype.val : W→X) ⁻¹' N)
          (GermIdeal.pullback (m:=k) (Subtype.val : W→X) I) d := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro N hNW I hI d
  unfold homogenizedIdealAlong
  rw [pullback_homSum (contMDiff_val hk hW) (fun i=>iterDerivIdealAlong N I i)
    (tangentIdealAlong N I d) d
    (fun i _ {_ _} hg=>holomorphicAt_of_mem_iterDerivIdealAlong hI i _ _ hg)
    (fun {_ _} hg=>holomorphicAt_of_mem_iterDerivIdealAlong (N:=N) hI (d-1) _ _ hg)]
  exact homSum_congr (fun i _=>pullback_native_iterDerivIdealAlong hk hW N hNW I hI i)
    (pullback_native_iterDerivIdealAlong hk hW N hNW I hI (d-1))

section Records
variable {Y : CMfd.{0} n} {V : Set Y} (hk : k≤n)
    (hV : ∀y∈V,RegularAtDim (n:=n) V y k)

theorem nativePullback_coeffMarkedAlong (M : MarkedIdeal n Y) (hMN : M.N⊆V)
    (hI : ∀x g,M.ideal.mem x g → HolomorphicAt n g x) :
    nativePullback hk V hV (coeffMarkedAlong M)=coeffMarkedAlong (nativePullback hk V hV M) := by
  let := chartedSpace hk hV
  have := isComplexManifold_chartedSpace hk hV
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ rfl
  change GermIdeal.pullback (m:=k) (Subtype.val : V→Y)
      (finSumIdeal (fun i=>idealPow (iterDerivIdealAlong M.N M.ideal i)
        (sumExp (fun j=>M.d-j) M.d i)) M.d)=
    finSumIdeal (fun i=>idealPow (iterDerivIdealAlong ((Subtype.val : V→Y) ⁻¹' M.N)
      (GermIdeal.pullback (m:=k) (Subtype.val : V→Y) M.ideal) i)
        (sumExp (fun j=>M.d-j) M.d i)) M.d
  rw [pullback_finSumIdeal (contMDiff_val hk hV) _ _
    (fun _ _ {_ _} hg=>holomorphicAt_of_mem_idealPow hg)]
  refine finSumIdeal_congr fun i _=>?_
  rw [pullback_idealPow (contMDiff_val hk hV)
    (fun {_ _} hg=>holomorphicAt_of_mem_iterDerivIdealAlong hI i _ _ hg),
    pullback_native_iterDerivIdealAlong hk hV M.N hMN M.ideal hI i]

theorem nativePullback_homMarkedAlong (M : MarkedIdeal n Y) (hMN : M.N⊆V)
    (hI : ∀x g,M.ideal.mem x g → HolomorphicAt n g x) :
    nativePullback hk V hV (homMarkedAlong M)=homMarkedAlong (nativePullback hk V hV M) :=
  MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl
    (pullback_native_homogenizedIdealAlong hk hV M.N hMN M.ideal hI M.d) rfl

theorem nativePullback_barMarked (M : MarkedIdeal n Y) (hMN : M.N⊆V)
    (hI : ∀x g,M.ideal.mem x g → HolomorphicAt n g x) :
    nativePullback hk V hV (StepOneValue.barMarked M)=StepOneValue.barMarked (nativePullback hk V hV M) := by
  change nativePullback hk V hV (coeffMarkedAlong (homMarkedAlong M))=_
  rw [nativePullback_coeffMarkedAlong hk hV (homMarkedAlong M) hMN (fun _ _ hg=>hg.1),
    nativePullback_homMarkedAlong hk hV M hMN hI]

theorem nativePullback_memberRestrict_membersThrough
    (hn : 0<n) (M : MarkedIdeal n Y) (hMN : M.N⊆V)
    (hI : ∀x g,M.ideal.mem x g → HolomorphicAt n g x)
    (hE : IsSNCDivisor n M.E) (hT : IsTransverse n V M.E)
    (E₀ : List (Set Y)) (hE₀ : ∀H∈E₀,H∈M.E) (p : nativeManifold hk V hV) :
    nativePullback hk V hV (memberRestrict M (membersThrough M.E E₀ p.val))=
      memberRestrict (nativePullback hk V hV M)
        (membersThrough (nativePullback hk V hV M).E
          (E₀.map ((Subtype.val : V→Y) ⁻¹' ·)) p) := by
  classical
  let := chartedSpace hk hV
  have := isComplexManifold_chartedSpace hk hV
  have hCoeff:=nativePullback_coeffMarkedAlong hk hV M hMN hI
  have hIdeal:=congrArg (fun K : MarkedIdeal k (nativeManifold hk V hV)=>K.ideal) hCoeff
  have hMark:=congrArg (fun K : MarkedIdeal k (nativeManifold hk V hV)=>K.d) hCoeff
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · change (Subtype.val : V→Y) ⁻¹' (memberRestrict M (membersThrough M.E E₀ p.val)).N=_
    rw [memberRestrict_membersThrough_N,memberRestrict_membersThrough_N]
    ext q
    change (q.val∈M.N ∧ ∀H∈M.E,H∈E₀ → p.val∈H → q.val∈H) ↔
      (q.val∈M.N ∧ ∀K∈M.E.map ((Subtype.val : V→Y) ⁻¹' ·),
        K∈E₀.map ((Subtype.val : V→Y) ⁻¹' ·) → p∈K → q∈K)
    refine and_congr_right fun _=>⟨?_,?_⟩
    · intro hw K hK hK₀ hpK
      obtain ⟨H,hH,rfl⟩:=List.mem_map.mp hK
      exact hw H hH ((incident_member_selection hn hE hT p E₀ hE₀ H hH hpK).mp hK₀) hpK
    · intro hw H hH hH₀ hpH
      exact hw _ (List.mem_map_of_mem hH) (List.mem_map_of_mem hH₀) hpH
  · change (memberRestrict M (membersThrough M.E E₀ p.val)).E.map ((Subtype.val : V→Y) ⁻¹' ·)=_
    rw [memberRestrict_membersThrough_E,memberRestrict_membersThrough_E]
    exact (filter_map_members (f:=((Subtype.val : V→Y) ⁻¹' ·)) (y:=p.val) (y':=p)
      (fun _ _=>Iff.rfl) (fun H hH hpH h=>
        (incident_member_selection hn hE hT p E₀ hE₀ H hH hpH).mp h)).symm
  · exact hIdeal
  · exact hMark

end Records
end
end Hironaka.HironakaActualNativeSectionCoefficientRecords
