import Hironaka.Resolution.HironakaG8TestBirthTangency
import Hironaka.Resolution.HironakaG8ExceptionalDivOpen
import Hironaka.Resolution.HironakaG8TangentOpen
/-! # Birth tangency from geometry on a source open -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8LocalizedBirthTangency
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold BlowupSpaceTangent
  BlowupRestrictOpen HomogenizedGlueingTower MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen NormalCrossings NormalCrossingsInvariance
  DivisorExponentAlong HironakaG11InvBMLower HironakaG8ExceptionalDivOpen HironakaG8TangentOpen

/-- Actual exceptional divisibility forces tangency at a birth even when the
contact carrier is known smooth and contains the centre only on an open
source neighbourhood. -/
theorem tangent_le_of_div_on_source_open
    {n : ℕ} {X Y Z : CMfd.{0} n} {C P : Set X} {π : Y → X}
    (hπ : IsBlowupAlong n C π) (U : Opens X)
    (hP : IsClosedSubmanifold n ((Subtype.val : U → X) ⁻¹' P))
    (hCP : ((Subtype.val : U → X) ⁻¹' C) ⊆ ((Subtype.val : U → X) ⁻¹' P))
    {E : List (Set X)} (hE : IsSNCDivisor n E) (hcross : HasNormalCrossings n C E)
    (i : Fin E.length) (M : MarkedIdeal n Y)
    (hMN : M.N = geoStrictTransform π C P) (hD : π ⁻¹' C ∈ M.E)
    (T : BlowupTower Y Z)
    (hM : (MarkedIdeal.pullback (Subtype.val : (⟨π ⁻¹' (U : Set X), U.isOpen.preimage hπ.contMDiff.continuous⟩ : Opens Y) → Y) M).IsWellFormed)
    (hT : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : (⟨π ⁻¹' (U : Set X), U.isOpen.preimage hπ.contMDiff.continuous⟩ : Opens Y) → Y) M)
      (restrict (⟨π ⁻¹' (U : Set X), U.isOpen.preimage hπ.contMDiff.continuous⟩ : Opens Y) T))
    {S : List (Set Z)} (hS : ∀ K ∈ S, IsClosedSubmanifold n K)
    (hmem : strictAlong T (geoStrictTransform π C (E.get i)) ∈ S) (e : ℕ) {z : Z}
    (hzU : π (T.proj z) ∈ U) (hzP : z ∈ strictAlong T M.N)
    (hzD : z ∈ strictAlong T (π ⁻¹' C)) (hpC : π (T.proj z) ∈ C)
    (hpH : π (T.proj z) ∈ E.get i)
    (hdiv : IsDivNearAlong n (strictAlong T M.N) (exceptionalTermBM (n := n) S e)
      (strictAlong T (π ⁻¹' C)) 1 z) :
    tangentSpace n P (π (T.proj z)) ≤ tangentSpace n (E.get i) (π (T.proj z)) := by
  let V : Opens Y := ⟨π ⁻¹' (U : Set X), U.isOpen.preimage hπ.contMDiff.continuous⟩
  let ρ : V → U := fun p => ⟨π p.val,p.2⟩
  let C' : Set U := (Subtype.val : U → X) ⁻¹' C
  let P' : Set U := (Subtype.val : U → X) ⁻¹' P
  let E' : List (Set U) := E.map ((Subtype.val : U → X) ⁻¹' ·)
  let i' : Fin E'.length := ⟨i.val, by simp [E']⟩
  let W := openPreimage T V
  let z' : W := ⟨z,hzU⟩
  let M' := MarkedIdeal.pullback (Subtype.val : V → Y) M
  let T' := restrict V T
  have hρ : IsBlowupAlong n C' ρ := isBlowupAlong_restrict hπ U V.isOpen
  let : Fact (IsClosedSubmanifold n C') := ⟨hρ.1⟩
  have hE' : IsSNCDivisor n E' := isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hE
  have hcross' : HasNormalCrossings n C' E' := hasNormalCrossings_preimage (pullsBackCoordinates_val U) hcross
  have hi' : E'.get i' = (Subtype.val : U → X) ⁻¹' (E.get i) := by
    simp [E', i']
  have hMN' : M'.N = geoStrictTransform ρ C' P' := by
    change (Subtype.val : V → Y) ⁻¹' M.N = _
    rw [hMN, geoStrictTransform_restrict U V.isOpen P]
  have hD' : ρ ⁻¹' C' ∈ M'.E := by
    change (Subtype.val : V → Y) ⁻¹' (π ⁻¹' C) ∈ M.E.map (fun H => (Subtype.val : V → Y) ⁻¹' H)
    exact List.mem_map.mpr ⟨π ⁻¹' C,hD,rfl⟩
  have hS' : ∀ K ∈ S.map ((Subtype.val : W → Z) ⁻¹' ·), IsClosed K := by
    intro K hK
    obtain ⟨K₀,hK₀,rfl⟩ := List.mem_map.mp hK
    exact (hS K₀ hK₀).1.preimage continuous_subtype_val
  have hSne : S ≠ [] := by
    intro hh
    simp [hh] at hmem
  have hdiv' := (isDivNearAlong_exceptionalTermBM_pullback_val_iff W hS hSne
    (strictAlong T M.N) (strictAlong T (π ⁻¹' C)) e 1 z').mpr hdiv
  have hstrictP := strictAlong_restrict V T M.N
  have hstrictD := strictAlong_restrict V T (π ⁻¹' C)
  have hstrictH := strictAlong_restrict V T (geoStrictTransform π C (E.get i))
  have hHS : geoStrictTransform ρ C' (E'.get i') =
      (Subtype.val : V → Y) ⁻¹' geoStrictTransform π C (E.get i) := by
    rw [hi']
    exact geoStrictTransform_restrict U V.isOpen _
  have hmem' : strictAlong T' (geoStrictTransform ρ C' (E'.get i')) ∈
      S.map ((Subtype.val : W → Z) ⁻¹' ·) := by
    rw [hHS, hstrictH]
    exact List.mem_map.mpr ⟨_, hmem, rfl⟩
  have hzP' : z' ∈ strictAlong T' M'.N := by
    change z' ∈ strictAlong T' ((Subtype.val : V → Y) ⁻¹' M.N)
    rw [hstrictP]
    exact hzP
  have hzD' : z' ∈ strictAlong T' (ρ ⁻¹' C') := by
    change z' ∈ strictAlong T' ((Subtype.val : V → Y) ⁻¹' (π ⁻¹' C))
    rw [hstrictD]
    exact hzD
  have hdiv'' : IsDivNearAlong n (strictAlong T' M'.N)
      (exceptionalTermBM (n := n) (S.map ((Subtype.val : W → Z) ⁻¹' ·)) e)
      (strictAlong T' (ρ ⁻¹' C')) 1 z' := by
    change IsDivNearAlong n (strictAlong T' ((Subtype.val : V → Y) ⁻¹' M.N)) _
      (strictAlong T' ((Subtype.val : V → Y) ⁻¹' (π ⁻¹' C))) 1 z'
    rw [hstrictP, hstrictD]
    exact hdiv'
  have hproj : ((T'.proj z' : V) : Y) = T.proj z := proj_restrict V T z'
  have hpC' : ρ (T'.proj z') ∈ C' := by
    change π ((T'.proj z' : V) : Y) ∈ C
    rw [hproj]
    exact hpC
  have hpH' : ρ (T'.proj z') ∈ E'.get i' := by
    rw [hi']
    change π ((T'.proj z' : V) : Y) ∈ E.get i
    rw [hproj]
    exact hpH
  have htan := HironakaG8TestBirthTangency.tangent_le_of_div_of_normalCrossings
    (X := CMfd.of (n := n) U) (Y := CMfd.of (n := n) V) (Z := CMfd.of (n := n) W)
    (C := C') (π := ρ) (P := P') hρ hρ.2.1 hP hCP hE' hcross' i' M' hM hMN' hD'
    T' hT hS' hmem' e hzP' hzD' hpC' hpH' hdiv''
  have hregular : ∃ k, RegularAtDim (n := n) P (π (T.proj z)) k := by
    obtain ⟨k,hk⟩ := hP.2 ⟨π (T.proj z), hzU⟩ (hCP hpC)
    exact ⟨k, AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp hk⟩
  obtain ⟨k,hk⟩ := hregular
  apply (tangent_le_preimage_val_iff U ⟨π (T.proj z),hzU⟩ hk hpH).mp
  have hpoint : ρ (T'.proj z') = (⟨π (T.proj z), hzU⟩ : U) := by
    apply Subtype.ext
    change π ((T'.proj z' : V) : Y) = π (T.proj z)
    rw [hproj]
  rw [hpoint, hi'] at htan
  exact htan

end
end Hironaka.HironakaG8LocalizedBirthTangency
