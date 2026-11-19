import Hironaka.Resolution.HironakaG8P1ArcCarrierPlane
import Hironaka.Resolution.HironakaG8LocalContactStage

set_option autoImplicit false

/-!
# The actual previous ambient carrier of a coefficient stage

The ordinary maximal-contact input constructs a coefficient carrier of
codimension one in the literal previous native carrier. This relationship
is retained along the actual restricted test tower. The previous native
record supplies its full original-and-born boundary transversality.

The base closedness and regularity proof extracts the existing private
`HironakaG8ClassStepHistory.contact_facts` (and its earlier residual copy).
The additional positivity of the ambient local dimension is derived from
the actual tangent direction's nonzero tangent derivative. The final
producer uses the public actual contact test tower and carrier equality,
not an assumed future ambient or dimension-preservation certificate.

This is the source geometry needed to discharge the ambient-carrier hO'
configuration in a subsequent History consumer. It does not assert hO,
Case T, residual case (r1), or any original Hironaka goal.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8ContactStageAmbient

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen MarkedIdealOperationsAlong.MarkedIdeal
  BlowupFlatCoordinates NormalCrossings ContactEquivalenceAlong TangentDirectionAlong
  GiraudAlong HomogenizedGlueingTower CoefficientIdealRestriction
  HironakaG11InvBMLower HironakaG11InvBMStage
  HironakaG8P1ArcCarrierPlane

noncomputable section

/-- A genuine nonzero tangent derivative at a zero of a tangent direction
rules out a zero-dimensional regular carrier. This retains information
which the old base contact regularity output erased. -/
private theorem positive_regular_dimension_of_tangent_zero
    {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] {N : Set M} {I : GermIdeal n M} {d : ℕ}
    (hI : ∀ x f, I.mem x f → HolomorphicAt n f x)
    {U : Set M} {f : M → ℂ} (hf : IsTangentDirectionAlong N I d U f)
    {x : M} (hxU : x ∈ U) (hxN : x ∈ N) (hfx : f x = 0)
    {k : ℕ} (hN : RegularAtDim (n := n) N x k) : 0 < k := by
  obtain ⟨e, ξ, hξ, hne⟩ := hf.multiplicity_one x hxU hfx
  have hhol : HolomorphicAt n f x :=
    holomorphicAt_of_mem_iterDerivIdealAlong hI (d - 1) x f (hf.mem x hxU)
  obtain ⟨_hkn, _hx, Φ, hsrc, _hzero, hflat⟩ := hN
  dsimp only [complexChartAt] at Φ hsrc hflat
  obtain ⟨j, hj, _hnePartial⟩ := exists_flatPartial_ne_zero hsrc hflat
    (mem_flatDomain_self Φ) hxN hhol hξ hne
  omega

variable {n : ℕ} {X : CMfd.{u} n}

/-- Faithful extraction of the existing base contact facts, retaining the
actual previous carrier and rewriting the dimensions as m and m+1 only
after the tangent derivative has proved the ambient dimension positive. -/
private theorem contact_base_facts
    (A : MarkedIdeal n X) (hA : A.IsWellFormed) (U : Opens X) {u : X → ℂ}
    (hu : IsTangentDirectionAlong A.N A.ideal A.d U u) :
    let P := MarkedIdeal.pullback (Subtype.val : U → X)
      (withN (coeffEmptyBM A) (A.N ∩ {x | u x = 0}))
    let R := MarkedIdeal.pullback (Subtype.val : U → X) A
    P.IsWellFormed ∧ P.N ⊆ R.N ∧
      ∀ x ∈ P.N, ∃ m, RegularAtDim (n := n) R.N x (m + 1) ∧
        RegularAtDim (n := n) P.N x m := by
  let P := MarkedIdeal.pullback (Subtype.val : U → X)
    (withN (coeffEmptyBM A) (A.N ∩ {x | u x = 0}))
  let R := MarkedIdeal.pullback (Subtype.val : U → X) A
  let M := MarkedIdeal.pullback (Subtype.val : U → X) (emptyBoundary A)
  have hN := hA.isClosedSubmanifold_N
  have hI := hA.isCoherent
  have hhol := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hI
  have hval : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (Subtype.val : U → X) := contMDiff_subtype_val
  have hNU : IsClosedSubmanifold n M.N :=
    BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN U
  have hcU : M.ideal.IsCoherent := GermIdealPullbackCalculus.isCoherent_pullback hval hI
  have huU : IsTangentDirectionAlong M.N M.ideal M.d univ (u ∘ Subtype.val) :=
    isTangentDirectionAlong_pullback_val U hhol hu
  have hContact := isClosedSubmanifold_contact_along (X := CMfd.of (n := n) U)
    (𝔪 := M) hNU hcU huU
  rw [preimage_val_contact_eq U] at hContact
  have hcP : P.ideal.IsCoherent := GermIdealPullbackCalculus.isCoherent_pullback hval
    (isWellFormed_coeffEmptyBM hA).isCoherent
  have hP : P.IsWellFormed :=
    ⟨hContact, hcP, isSNCDivisor_nil, isTransverse_nil_of_isClosedSubmanifold hContact⟩
  change P.IsWellFormed ∧ P.N ⊆ R.N ∧ _
  refine ⟨hP, fun _ hx => hx.1, ?_⟩
  intro x hx
  have hxContact : x ∈ M.N ∩ {x : U | (u ∘ Subtype.val) x = 0} ∩ univ := by
    rw [preimage_val_contact_eq U]
    exact hx
  have hholU := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcU
  obtain ⟨k, hk, hkContact⟩ := IsTangentDirectionAlong.regularAtDim_contact hholU hNU huU hxContact
  have hkpos : 0 < k := positive_regular_dimension_of_tangent_zero hholU huU
    (mem_univ x) hxContact.1.1 hxContact.1.2 hk
  rw [preimage_val_contact_eq U] at hkContact
  change RegularAtDim (n := n) R.N x k at hk
  refine ⟨k - 1, ?_, hkContact⟩
  simpa only [Nat.sub_add_cancel hkpos] using hk

/-- Ordinary maximal-contact input produces the literal previous native
ambient carrier for the actual coefficient stage. Its full boundary stays
transverse to that ambient carrier, and the actual coefficient carrier is
a closed regular hypersurface of it at every stage point over U.

All carrier/tower witnesses are constructed from the actual native record,
contact function and test tower. No ambient-carrier conclusion or preserved
dimension is supplied by the caller. -/
theorem contact_stage_ambient_hypersurface
    (A : MarkedIdeal n X) (hA : A.IsWellFormed) (hd : 1 ≤ A.d)
    (U : Opens X) {u : X → ℂ}
    (hu : IsTangentDirectionAlong A.N A.ideal A.d U u)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower A T)
    (p : openPreimage T U) (hp : p.val ∈ (contactCoeffBM A u T).N) :
    let V := openPreimage T U
    let C := MarkedIdeal.pullback (Subtype.val : V → Y) (contactCoeffBM A u T)
    let R := MarkedIdeal.pullback (Subtype.val : V → Y) (geoTransformAlong A T)
    R.IsWellFormed ∧ C.N ⊆ R.N ∧ IsClosedSubmanifold n C.N ∧
      ∃ m, RegularAtDim (n := n) R.N p (m + 1) ∧ RegularAtDim (n := n) C.N p m := by
  let V := openPreimage T U
  let C := MarkedIdeal.pullback (Subtype.val : V → Y) (contactCoeffBM A u T)
  let R := MarkedIdeal.pullback (Subtype.val : V → Y) (geoTransformAlong A T)
  let P := MarkedIdeal.pullback (Subtype.val : U → X)
    (withN (coeffEmptyBM A) (A.N ∩ {x | u x = 0}))
  let R0 := MarkedIdeal.pullback (Subtype.val : U → X) A
  let S := restrict U T
  obtain ⟨hP, _hPR0, hBaseDim⟩ := contact_base_facts A hA U hu
  obtain ⟨hPS, hRE⟩ := restrictEquiv_stage_contactCoeffBM hA hd U hu T hT
  have hR0 : R0.IsWellFormed := IsWellFormed.pullback_val hA U
  have hRS : IsGeoTestTower R0 S := isGeoTestTower_restrict U
    hA.isClosedSubmanifold_N hA.isCoherent T hT
  have hR : R.IsWellFormed := IsWellFormed.pullback_val
    (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hA T hT) V
  have hCR : C.N ⊆ R.N := by
    intro q hq
    change q.val ∈ strictAlong T (A.N ∩ {x | u x = 0}) at hq
    change q.val ∈ (geoTransformAlong A T).N
    rw [N_geoTransformAlong]
    exact MemberInterTowerAlong.strictAlong_mono T inter_subset_left hq
  have hPStage := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hP S hPS
  have hClosedC : IsClosedSubmanifold n C.N := by
    rw [← hRE.N_eq]
    exact hPStage.isClosedSubmanifold_N
  have hAmbientEq : geoTransformAlong R0 S = R := geoTransformAlong_restrict U
    hA.isClosedSubmanifold_N hA.isCoherent T hT
  have hpC : p ∈ C.N := hp
  have hpP : p ∈ (geoTransformAlong P S).N := by
    rw [hRE.N_eq]
    exact hpC
  have hpR : p ∈ (geoTransformAlong R0 S).N := by
    rw [hAmbientEq]
    exact hCR hpC
  have hBasePoint : S.proj p ∈ P.N := by
    apply MemberInterTowerAlong.strictAlong_subset_preimage S hP.isClosedSubmanifold_N.1
    simpa only [N_geoTransformAlong] using hpP
  obtain ⟨m, hmR, hmP⟩ := hBaseDim (S.proj p) hBasePoint
  have hAmbientDim := regularAtDim_geoTransformAlong_carrier R0 hR0 S hRS hpR hmR
  have hContactDim := regularAtDim_geoTransformAlong_carrier P hP S hPS hpP hmP
  rw [hAmbientEq] at hAmbientDim
  rw [hRE.N_eq] at hContactDim
  change R.IsWellFormed ∧ C.N ⊆ R.N ∧ IsClosedSubmanifold n C.N ∧ _
  exact ⟨hR, hCR, hClosedC, m, hAmbientDim, hContactDim⟩

end

end Hironaka.HironakaG8ContactStageAmbient
