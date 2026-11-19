import Hironaka.Resolution.HironakaG8ResidualBirthTangency
import Hironaka.Resolution.HironakaG8TestTraceIdentity

/-! # Birth tangency along a literal test suffix -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8TestBirthTangency
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupStrictSubmanifold BlowupSpaceTangent HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  NormalCrossings DivisorExponentAlong HironakaG11InvBMLower

theorem tangent_le_of_div_of_containing_germ
    {n : ℕ} {X Y Z : CMfd.{0} n} {C : Set X} [Fact (IsClosedSubmanifold n C)]
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCint : interior C = ∅)
    {P H : Set X} (hP : IsClosedSubmanifold n P) (hCP : C ⊆ P)
    (M : MarkedIdeal n Y) (hM : M.IsWellFormed)
    (hMN : M.N = geoStrictTransform π C P) (hD : π ⁻¹' C ∈ M.E)
    (T : BlowupTower Y Z)
    (hT : IsGeoTestTower M T)
    {S : List (Set Z)} (hS : ∀ K ∈ S, IsClosed K)
    (hmem : strictAlong T (geoStrictTransform π C H) ∈ S) (e : ℕ) {z : Z}
    (hzP : z ∈ strictAlong T M.N)
    (hzD : z ∈ strictAlong T (π ⁻¹' C)) (hpC : π (T.proj z) ∈ C)
    (hCH : ∀ᶠ x in 𝓝 (π (T.proj z)), x ∈ C → x ∈ H)
    (hdiv : IsDivNearAlong n (strictAlong T M.N) (exceptionalTermBM (n := n) S e)
      (strictAlong T (π ⁻¹' C)) 1 z) :
    tangentSpace n P (π (T.proj z)) ≤ tangentSpace n H (π (T.proj z)) := by
  by_contra hnt
  obtain ⟨W,V,_,_,hpV,hDense⟩ :=
    HironakaG11ContainingAbstractLocalHistory.exists_local_trace_dense_of_containing_germ
      hπ hCint hP hCP hpC hCH hnt
  have hDense' : ((Subtype.val : V → Y) ⁻¹' (M.N ∩ (π ⁻¹' C))) ⊆
      closure (((Subtype.val : V → Y) ⁻¹' (M.N ∩ (π ⁻¹' C))) \
        ((Subtype.val : V → Y) ⁻¹' geoStrictTransform π C H)) := by
    rw [hMN]
    exact hDense
  exact HironakaG8TestTraceIdentity.not_div_of_trace_density M hM V (π ⁻¹' C)
    (geoStrictTransform π C H) hD isClosed_closure hDense' T hT hS hmem e hpV hzP hzD hdiv

/-- At a normal-crossings birth, exceptional-term divisibility forces the
old boundary member to contain the centre as a germ. -/
theorem containing_germ_of_div
    {n : ℕ} {X Y Z : CMfd.{0} n} {C : Set X} [Fact (IsClosedSubmanifold n C)]
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCint : interior C = ∅)
    {P : Set X} (hP : IsClosedSubmanifold n P) (hCP : C ⊆ P)
    {E : List (Set X)} (hE : IsSNCDivisor n E) (hcross : HasNormalCrossings n C E)
    (i : Fin E.length) (M : MarkedIdeal n Y) (hM : M.IsWellFormed)
    (hMN : M.N = geoStrictTransform π C P) (hD : π ⁻¹' C ∈ M.E)
    (T : BlowupTower Y Z)
    (hT : IsGeoTestTower M T)
    {S : List (Set Z)} (hS : ∀ K ∈ S, IsClosed K)
    (hmem : strictAlong T (geoStrictTransform π C (E.get i)) ∈ S) (e : ℕ) {z : Z}
    (hzP : z ∈ strictAlong T M.N)
    (hzD : z ∈ strictAlong T (π ⁻¹' C)) (hpC : π (T.proj z) ∈ C)
    (hpH : π (T.proj z) ∈ E.get i)
    (hdiv : IsDivNearAlong n (strictAlong T M.N) (exceptionalTermBM (n := n) S e)
      (strictAlong T (π ⁻¹' C)) 1 z) :
    ∀ᶠ x in 𝓝 (π (T.proj z)), x ∈ C → x ∈ E.get i := by
  by_contra hnot
  obtain ⟨W,V,_,_,hpV,hDense⟩ :=
    HironakaG11NoncontainingAbstractLocalHistory.exists_local_trace_dense_of_noncontaining_germ
      hπ hCint hP hCP hE hcross i hpC hpH hnot
  have hDense' : ((Subtype.val : V → Y) ⁻¹' (M.N ∩ (π ⁻¹' C))) ⊆
      closure (((Subtype.val : V → Y) ⁻¹' (M.N ∩ (π ⁻¹' C))) \
        ((Subtype.val : V → Y) ⁻¹' geoStrictTransform π C (E.get i))) := by
    rw [hMN]
    exact hDense
  exact HironakaG8TestTraceIdentity.not_div_of_trace_density M hM V (π ⁻¹' C)
    (geoStrictTransform π C (E.get i)) hD isClosed_closure hDense' T hT hS hmem e hpV hzP hzD hdiv


/-- Exceptional-term divisibility after the actual local test suffix forces
the birth-centre contact carrier to be tangent to the old boundary. -/
theorem tangent_le_of_div_of_normalCrossings
    {n : ℕ} {X Y Z : CMfd.{0} n} {C : Set X} [Fact (IsClosedSubmanifold n C)]
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCint : interior C = ∅)
    {P : Set X} (hP : IsClosedSubmanifold n P) (hCP : C ⊆ P)
    {E : List (Set X)} (hE : IsSNCDivisor n E) (hcross : HasNormalCrossings n C E)
    (i : Fin E.length) (M : MarkedIdeal n Y) (hM : M.IsWellFormed)
    (hMN : M.N = geoStrictTransform π C P) (hD : π ⁻¹' C ∈ M.E)
    (T : BlowupTower Y Z)
    (hT : IsGeoTestTower M T)
    {S : List (Set Z)} (hS : ∀ K ∈ S, IsClosed K)
    (hmem : strictAlong T (geoStrictTransform π C (E.get i)) ∈ S) (e : ℕ) {z : Z}
    (hzP : z ∈ strictAlong T M.N)
    (hzD : z ∈ strictAlong T (π ⁻¹' C)) (hpC : π (T.proj z) ∈ C)
    (hpH : π (T.proj z) ∈ E.get i)
    (hdiv : IsDivNearAlong n (strictAlong T M.N) (exceptionalTermBM (n := n) S e)
      (strictAlong T (π ⁻¹' C)) 1 z) :
    tangentSpace n P (π (T.proj z)) ≤ tangentSpace n (E.get i) (π (T.proj z)) := by
  have hCH := containing_germ_of_div hπ hCint hP hCP hE hcross i M hM hMN hD T hT
    hS hmem e hzP hzD hpC hpH hdiv
  exact tangent_le_of_div_of_containing_germ hπ hCint hP hCP M hM hMN hD T hT
    hS hmem e hzP hzD hpC hCH hdiv

end
end Hironaka.HironakaG8TestBirthTangency
