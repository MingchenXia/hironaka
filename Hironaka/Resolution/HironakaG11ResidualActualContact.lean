import Hironaka.Resolution.HironakaG11ResidualBirthFullTrace
import Hironaka.Resolution.HironakaG11PairedContactBirthGeometry
import Hironaka.Resolution.HironakaG11InvBMMask
import Hironaka.Invariant.StepOneBridge

set_option autoImplicit false

/-!
# The actual paired contact configuration at a residual boundary birth

The lower-ideal anchor and evaluated point are distinct. The actual mask
conditions place the evaluated point over both chosen tangent opens, while
the residual divisibility alternative identifies the old member at the
same birth. The common test birth itself supplies both contact-carrier
centre containments and ambient hypersurface data.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG11ResidualActualContact
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealRestrictOpen MarkedIdealBiholomorphism
  HomogenizedGlueingTower HomogenizedIdealAlong TangentDirectionAlong
  HironakaG11InvBMLower HironakaG11InvBMMask StepOneValue StepOneLowerDomain
  ResolutionInvariantSpec HironakaG8LocalHistory HironakaG8LocalContact DivisorExponentAlong
  HironakaG11ResidualBirthFullTrace HironakaG11PairedContactBirthGeometry

noncomputable section

/-- At a residual point, an actual selected old member and born boundary
produce the paired contact configuration at their common literal birth. -/
theorem residual_birth_has_paired_contact
    {n : ℕ} {X : CMfd.{0} n} {A B : MarkedIdeal n X} {k k' : ℕ}
    (hA : IsInvDomain k A) (hB : IsInvDomain k' B)
    (hmA : IsMaximalOrderAlong A.N A.ideal A.d) (hmB : IsMaximalOrderAlong B.N B.ideal B.d)
    (h : LocWPEquiv A B)
    {Y : CMfd.{0} n} (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked A) T)
    (a z : Y) (ha : a ∈ (geoTransformAlong (barMarked A) T).cosupp)
    (s : ℕ) (O : Opens Y) (hOA : O ≤ maskBM A (s + 1) T a)
    (hOB : O ≤ maskBM B (s + 1) T a) (hzO : z ∈ O)
    {H K : Set Y} (hH : H ∈ (lowerIdealBM A (s + 1) T a).E)
    (hK : K ∈ throughMembers A T a) (hS : ∀ H ∈ throughMembers A T a, IsClosed H)
    (hzA : z ∈ (lowerIdealBM A (s + 1) T a).N)
    (hzB : z ∈ (lowerIdealBM B (s + 1) T a).N) (hzH : z ∈ H)
    (hdiv : IsDivNearAlong n (lowerIdealBM A (s + 1) T a).N
      (exceptionalTermBM (n := n) (throughMembers A T a) (coeffEmptyBM A).d) H 1 z ∨
      IsDivNearAlong n (lowerIdealBM B (s + 1) T a).N
      (exceptionalTermBM (n := n) (throughMembers A T a) (coeffEmptyBM A).d) H 1 z) :
    ∃ (Y₀ Y₁ : CMfd.{0} n) (P : BlowupTower X Y₀) (C : Set Y₀)
      (π : Y₁ → Y₀) (hπ : IsBlowupAlong n C π) (Q : BlowupTower Y₁ Y) (K₀ : Set X)
      (U : Opens X) (p : openPreimage P U),
      T = (BlowupTower.step P C π hπ).append Q ∧ H = strictAlong Q (π ⁻¹' C) ∧
      K₀ ∈ A.E ∧ K = strictAlong Q (geoStrictTransform π C (strictAlong P K₀)) ∧
      p.val = π (Q.proj z) ∧ p.val ∈ C ∧
      IsGeoTestTower (barMarked A) P ∧
      (geoTransformAlong (barMarked A) P).IsAdmissibleCentre C ∧
      IsGeoTestTower (geoTransformAlong (barMarked A) (.step P C π hπ)) Q ∧
      Q.proj z ∈ geoStrictTransform π C (strictAlong P (A.N ∩ {x | (tangentChoice A (T.proj a)).2 x = 0})) ∧
      Q.proj z ∈ geoStrictTransform π C (strictAlong P (B.N ∩ {x | (tangentChoice B (T.proj a)).2 x = 0})) ∧
      Q.proj z ∈ geoStrictTransform π C (strictAlong P K₀) ∧
      IsTangentDirectionAlong A.N A.ideal A.d U (tangentChoice A (T.proj a)).2 ∧
      IsTangentDirectionAlong B.N B.ideal B.d U (tangentChoice B (T.proj a)).2 ∧
      let V := openPreimage P U
      let LA := MarkedIdeal.pullback (Subtype.val : V → Y₀)
        (contactCoeffBM A (tangentChoice A (T.proj a)).2 P)
      let LB := MarkedIdeal.pullback (Subtype.val : V → Y₀)
        (contactCoeffBM B (tangentChoice B (T.proj a)).2 P)
      let RA := MarkedIdeal.pullback (Subtype.val : V → Y₀) (geoTransformAlong A P)
      let RB := MarkedIdeal.pullback (Subtype.val : V → Y₀) (geoTransformAlong B P)
      RA.IsWellFormed ∧ LA.N ⊆ RA.N ∧ IsClosedSubmanifold n LA.N ∧
        (Subtype.val : V → Y₀) ⁻¹' C ⊆ LA.N ∧
        (∃ m, RegularAtDim (n := n) RA.N p (m + 1) ∧ RegularAtDim (n := n) LA.N p m) ∧
      RB.IsWellFormed ∧ LB.N ⊆ RB.N ∧ IsClosedSubmanifold n LB.N ∧
        (Subtype.val : V → Y₀) ⁻¹' C ⊆ LB.N ∧
        ∃ m, RegularAtDim (n := n) RB.N p (m + 1) ∧ RegularAtDim (n := n) LB.N p m := by
  have hWA := StepOneBridge.barMarked_wEquiv A hA
  have hWB := StepOneBridge.barMarked_wEquiv B hB
  have hTA : IsGeoTestTower A T := (hWA.2 T).1.mp hT
  have hTB : IsGeoTestTower B T := (h.wEquiv.2 T).1.mp hTA
  have hTJB : IsGeoTestTower (barMarked B) T := (hWB.2 T).1.mpr hTB
  have haA : a ∈ (geoTransformAlong A T).cosupp := (hWA.2 T).2 hT ▸ ha
  have haB : a ∈ (geoTransformAlong (barMarked B) T).cosupp := by
    rw [(hWB.2 T).2 hTJB, ← (h.wEquiv.2 T).2 hTA]
    exact haA
  obtain ⟨-, hu⟩ := tangentChoice_spec A
    (exists_tangent_of_mem_cosupp A hA.isWellFormed hA.one_le_d hmA T hT ha)
  obtain ⟨-, hv⟩ := tangentChoice_spec B
    (exists_tangent_of_mem_cosupp B hB.isWellFormed hB.one_le_d hmB T hTJB haB)
  let U : Opens X := ⟨(tangentChoice A (T.proj a)).1 ∩ (tangentChoice B (T.proj a)).1,
    hu.isOpen.inter hv.isOpen⟩
  have huU := IsTangentDirectionAlong.mono_open hu U.isOpen (fun _ hx => hx.1)
  have hvU := IsTangentDirectionAlong.mono_open hv U.isOpen (fun _ hx => hx.2)
  have hzUA : T.proj z ∈ (tangentChoice A (T.proj a)).1 := by
    have hx : z ∈ T.proj ⁻¹' (tangentChoice A (T.proj a)).1 :=
      interior_subset (show z ∈ interior (T.proj ⁻¹' (tangentChoice A (T.proj a)).1) from (hOA hzO).2)
    exact hx
  have hzUB : T.proj z ∈ (tangentChoice B (T.proj a)).1 := by
    have hx : z ∈ T.proj ⁻¹' (tangentChoice B (T.proj a)).1 :=
      interior_subset (show z ∈ interior (T.proj ⁻¹' (tangentChoice B (T.proj a)).1) from (hOB hzO).2)
    exact hx
  obtain ⟨Y₀,Y₁,P,C,π,hπ,Q,K₀,hEq,hH',hK₀,hK',hPc,hCc,hQc,hP,hC,hQ,hzA',hzB',hzC,hzK⟩ :=
    lower_residual_birth_with_full_tests A B hA.isWellFormed hA.one_le_d (s+1) (s+1) T hT a z hH hK hS hzA hzB hzH hdiv
  have hpU : P.proj (π (Q.proj z)) ∈ U := by
    change P.proj (π (Q.proj z)) ∈ (tangentChoice A (T.proj a)).1 ∩ (tangentChoice B (T.proj a)).1
    have hproj : P.proj (π (Q.proj z)) = T.proj z := by
      rw [hEq, BlowupTower.proj_append, BlowupTower.proj_step]
      rfl
    rw [hproj]
    exact ⟨hzUA, hzUB⟩
  let p : openPreimage P U := ⟨π (Q.proj z), hpU⟩
  have hStep : IsGeoTestTower (barMarked A) (.step P C π hπ) :=
    (isGeoTestTower_step_iff _ P C π hπ).mpr ⟨hP,hC⟩
  refine ⟨Y₀,Y₁,P,C,π,hπ,Q,K₀,U,p,hEq,hH',hK₀,hK',rfl,hzC,hP,hC,hQ,hzA',hzB',hzK,huU,hvU, ?_⟩
  exact paired_contact_birth_geometry hA hB h U huU hvU P C π hπ hStep p hzC

end
end Hironaka.HironakaG11ResidualActualContact
