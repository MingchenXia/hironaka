import Hironaka.Resolution.HironakaActualNonregularCoefficientNaturality
import Hironaka.Invariant.MemberRestrictTowerIso

/-! The source record need not be globally regular
or have an SNC divisor: SNC of its literal trace on the good CURRENT open
is enough to transport the ordered member restriction. This preserves all
retained original and born boundary labels in their existing list order. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualPointLocalMemberRestriction
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
open RelativePrincipalizationSpan GermIdealPullbackCalculus InvDomainMemberRestriction InvDomainRebase
open HomogenizedIdealAlong NormalCrossings
open BlowupTowers DerivativeIdealAlongEtale
noncomputable section
variable {n : ℕ}

section OneSpace
variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

omit [IsComplexManifold n M] in
/-- The trace itself being SNC prevents a born member through the point from
being confused with an old member after restriction, even when the untraced
source divisor is not globally SNC. -/
theorem mem_of_preimage_val_mem_map_of_snc_trace
  {E E₀ : List (Set M)} (hE₀ : ∀ H∈E₀,H∈E) (U : Opens M)
  (hEU : IsSNCDivisor n (E.map ((Subtype.val : U → M) ⁻¹' ·)))
  (p : U) {H : Set M} (hH : H∈E) (hpH : (p : M)∈H)
  (h : (Subtype.val : U → M) ⁻¹' H∈E₀.map ((Subtype.val : U → M) ⁻¹' ·)) : H∈E₀ := by
  obtain ⟨H₀,hH₀,hpre⟩ := List.mem_map.mp h
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp (hE₀ H₀ hH₀)
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp hH
  let i' : Fin (E.map ((Subtype.val : U → M) ⁻¹' ·)).length :=
    ⟨i.val,by simpa only [List.length_map] using i.isLt⟩
  let j' : Fin (E.map ((Subtype.val : U → M) ⁻¹' ·)).length :=
    ⟨j.val,by simpa only [List.length_map] using j.isLt⟩
  have hgeti : (E.map ((Subtype.val : U → M) ⁻¹' ·)).get i' =
      (Subtype.val : U → M) ⁻¹' E.get i := by simp [i',List.get_eq_getElem]
  have hgetj : (E.map ((Subtype.val : U → M) ⁻¹' ·)).get j' =
      (Subtype.val : U → M) ⁻¹' E.get j := by simp [j',List.get_eq_getElem]
  have heq : (E.map ((Subtype.val : U → M) ⁻¹' ·)).get i' =
      (E.map ((Subtype.val : U → M) ⁻¹' ·)).get j' := by
    rw [hgeti,hgetj,hi,hj]
    exact hpre
  have hpj : p∈(E.map ((Subtype.val : U → M) ⁻¹' ·)).get j' := by
    rw [hgetj,hj]
    exact hpH
  have hpi : p∈(E.map ((Subtype.val : U → M) ⁻¹' ·)).get i' := by rw [heq];exact hpj
  have hij' : i'=j' := InvDomainRebase.eq_of_eventually_mem_iff hEU hpi hpj
    (Eventually.of_forall fun w => by rw [heq])
  have hij : i=j := by
    apply Fin.ext
    exact congrArg (fun a : Fin (E.map ((Subtype.val : U → M) ⁻¹' ·)).length => a.val) hij'
  have hH0 : H₀=H := hi.symm.trans ((congrArg E.get hij).trans hj)
  exact hH0 ▸ hH₀

/-- Raw holomorphic coefficient algebra plus SNC on the literal good open
gives the entire member-restricted record there; no global source well-formedness
or global source test-history premise is used. -/
theorem pullback_val_memberRestrict_membersThrough_of_snc_trace
  (A : MarkedIdeal n M)
  (hhol : ∀ x g,A.ideal.mem x g → HolomorphicAt n g x)
  {E₀ : List (Set M)} (hE₀ : ∀ H∈E₀,H∈A.E) (U : Opens M)
  (hEU : IsSNCDivisor n (A.E.map ((Subtype.val : U → M) ⁻¹' ·))) (p : U) :
  MarkedIdeal.pullback (Subtype.val : U → M)
      (memberRestrict A (membersThrough A.E E₀ p)) =
    memberRestrict (MarkedIdeal.pullback (Subtype.val : U → M) A)
      (membersThrough (MarkedIdeal.pullback (Subtype.val : U → M) A).E
        (E₀.map ((Subtype.val : U → M) ⁻¹' ·)) p) := by
  have hcoeff := HironakaActualNonregularCoefficientNaturality.pullback_coeffMarkedAlong
    contMDiff_subtype_val (fun y => ⟨openInv U y,isLocalInverseAt_val U y⟩) A hhol
  have hmem : ∀ H∈A.E,(p : M)∈H →
      (Subtype.val : U → M) ⁻¹' H∈E₀.map ((Subtype.val : U → M) ⁻¹' ·) → H∈E₀ :=
    fun H hH hpH h => mem_of_preimage_val_mem_map_of_snc_trace hE₀ U hEU p hH hpH h
  have hI := congrArg MarkedIdeal.ideal hcoeff
  have hD := congrArg MarkedIdeal.d hcoeff
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ ?_ hI hD
  · show (Subtype.val : U → M) ⁻¹' (memberRestrict A (membersThrough A.E E₀ p)).N = _
    rw [memberRestrict_membersThrough_N,memberRestrict_membersThrough_N]
    ext q
    simp only [mem_preimage,mem_inter_iff,mem_ofPred_eq]
    refine and_congr_right fun _ => ⟨fun hw H' hH' hH'₀ hpH' => ?_,fun hw H hH hH₀ hpH => ?_⟩
    · obtain ⟨H,hH,rfl⟩ := List.mem_map.mp hH'
      exact hw H hH (hmem H hH hpH' hH'₀) hpH'
    · exact hw _ (List.mem_map_of_mem hH) (List.mem_map_of_mem hH₀) hpH
  · show (memberRestrict A (membersThrough A.E E₀ p)).E.map ((Subtype.val : U → M) ⁻¹' ·) = _
    rw [memberRestrict_membersThrough_E,memberRestrict_membersThrough_E]
    exact (filter_map_members (f := ((Subtype.val : U → M) ⁻¹' ·))
      (y := (p : M)) (y' := p) (fun H _ => Iff.rfl) hmem).symm
end OneSpace

section Record
variable {Z Z' : CMfd.{u} n}

/-- The actual two post-records determine the entire positive-level lower
member record on the CURRENT opens. The source's ordered divisor is allowed
to be bad elsewhere. The original sublists are transported as lists. -/
theorem current_member_records_from_whole_record
  (A : MarkedIdeal n Z) (B : MarkedIdeal n Z')
  (hhol : ∀ x g,A.ideal.mem x g → HolomorphicAt n g x)
  (hB : B.IsWellFormed) (hdB : 1≤B.d)
  (E₀ : List (Set Z)) (F₀ : List (Set Z'))
  (hE₀ : ∀ H∈E₀,H∈A.E) (hF₀ : ∀ H∈F₀,H∈B.E)
  (U : Opens Z) (U' : Opens Z')
  (η : U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ U')
  (hrec : MarkedIdeal.pullback (Subtype.val : U → Z) A =
    MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') B))
  (hOld : E₀.map ((Subtype.val : U → Z) ⁻¹' ·) =
    (F₀.map ((Subtype.val : U' → Z') ⁻¹' ·)).map (η ⁻¹' ·)) (z : U) :
  MarkedIdeal.pullback (Subtype.val : U → Z)
      (memberRestrict A (membersThrough A.E E₀ z.val)) =
    MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z')
      (memberRestrict B (membersThrough B.E F₀ (η z).val))) := by
  let AU : MarkedIdeal n (CMfd.of (n := n) U) :=
    MarkedIdeal.pullback (Subtype.val : U → Z) A
  let BU : MarkedIdeal n (CMfd.of (n := n) U') :=
    MarkedIdeal.pullback (Subtype.val : U' → Z') B
  have hBU : BU.IsWellFormed := IsWellFormed.pullback_val hB U'
  have hAU : AU.IsWellFormed := by
    change (MarkedIdeal.pullback (Subtype.val : U → Z) A).IsWellFormed
    rw [hrec]
    exact MarkedIdealTowerTransport.IsWellFormed.pullback (Φ := η) hBU
  have hLocalSNC : IsSNCDivisor n (A.E.map ((Subtype.val : U → Z) ⁻¹' ·)) := hAU.isSNCDivisor
  have hS := pullback_val_memberRestrict_membersThrough_of_snc_trace A hhol hE₀ U hLocalSNC z
  have hT := InvDomainRebase.pullback_val_memberRestrict_membersThrough hB hdB hF₀ U' (η z)
  have hη := MemberRestrictTowerIso.pullback_diffeo_memberRestrict_membersThrough η
    hBU hdB (F₀.map ((Subtype.val : U' → Z') ⁻¹' ·)) z
  calc
    MarkedIdeal.pullback (Subtype.val : U → Z)
        (memberRestrict A (membersThrough A.E E₀ z.val)) =
      memberRestrict AU (membersThrough AU.E (E₀.map ((Subtype.val : U → Z) ⁻¹' ·)) z) := hS
    _ = memberRestrict (MarkedIdeal.pullback η BU)
        (membersThrough (MarkedIdeal.pullback η BU).E
          ((F₀.map ((Subtype.val : U' → Z') ⁻¹' ·)).map (η ⁻¹' ·)) z) := by
      have hrec' : AU=MarkedIdeal.pullback η BU := hrec
      simpa only [hOld] using congrArg
        (fun Q : MarkedIdeal n (CMfd.of (n := n) U) =>
          memberRestrict Q (membersThrough Q.E (E₀.map ((Subtype.val : U → Z) ⁻¹' ·)) z)) hrec'
    _ = MarkedIdeal.pullback η
        (memberRestrict BU (membersThrough BU.E
          (F₀.map ((Subtype.val : U' → Z') ⁻¹' ·)) (η z))) := hη.symm
    _ = MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z')
        (memberRestrict B (membersThrough B.E F₀ (η z).val))) :=
      congrArg (MarkedIdeal.pullback η) hT.symm
end Record
end
end Hironaka.HironakaActualPointLocalMemberRestriction
