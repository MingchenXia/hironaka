import Hironaka.Resolution.HironakaActualNativeBornWeightedExponents
import Hironaka.Resolution.HironakaG11PresLineStable
import Hironaka.Resolution.HironakaG1OriginalUnequalMarkCanonical
import Hironaka.Resolution.HironakaSharpOriginalDistinctTraceUSC
import Hironaka.Resolution.HironakaStepOneZeroContactRemainderGlueing

/-!
# Boundary-aware comparison of native Hilbert–Samuel windows

At a native cut point the reduced-stalk dictionary detects divisibility
by every smooth divisor that does not lie in the singular carrier as a
germ. Actual overlaps with the same full boundary and this noncontainment
condition therefore have the same support and the same canonical history
in the common ambient space.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8NativeBoundaryComparison

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  MarkedIdealTowerTransport
  NormalCrossings ResolutionInvariantSpec CanonicalCentres HironakaG11PresLineState
  HironakaG11PresLineStable HironakaG8LocalHistory HironakaG11InvBMClass
  DivisorExponent DivisorExponentAlong IdealWeightPowers GermIdealOrder HironakaStageCenters
  HironakaEmbeddedAnalytic

variable {n : ℕ} {X : CMfd.{0} n}

/-- A boundary member whose germ is not contained in the underlying set has
exponent zero at an actual native cut point. -/
theorem native_divExpAlong_eq_zero_of_boundary_noncontainment
    {Q : MarkedIdeal n X} {W : Set X} {H : ℕ → ℕ} (hState : NativeHSState Q W H)
    {x : X} (hx : x ∈ Q.cosupp) {D : Set X} (hD : IsClosedSubmanifold n D) (hxD : x ∈ D)
    (hNot : ¬ ∀ᶠ y in 𝓝 x, y ∈ D → y ∈ W) :
    divExpAlong n Q.N Q.ideal D x = 0 := by
  obtain ⟨_, hW, hN, hQI, V, S, k, a, w, _, hPos, _, _, _, _, hAt⟩ := hState
  obtain ⟨_, _, _, _, hTests, _⟩ :=
    HironakaActualNativeBornWeightedExponents.actual_native_point_reduced_stalk_dictionary
      S a w hPos W hW Q hQI x (hAt x hx)
  have hIW := CartanIrreducible.cartanCoherence W hW
  have hID := VanishingIdealCoherent.isCoherent_vanishingIdeal hD
  obtain ⟨d, hd⟩ := hD.2 x hxD
  rw [hN, divExpAlong_univ]
  by_contra hne
  have hQHol : ∀ y f, Q.ideal.mem y f → HolomorphicAt n f y := fun _ _ hf =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hQI hf
  have hDiv := (isDivNear_divExp hQHol x (H := D)).mono (Nat.one_le_iff_ne_zero.mpr hne)
  have hQStalk := (isDivNear_iff hQI hd).mp hDiv
  rw [FactorizationFromResolution.idealPow_one_of_isCoherent hID] at hQStalk
  have hWStalk := (hTests D hID).mp hQStalk
  apply hNot
  filter_upwards [HironakaSharpOriginalDistinctTraceUSC.eventually_coherent_germ_le hIW hID hWStalk]
    with y hy hyD
  apply VanishingIdealZeroLocus.zeroLocus_vanishingIdeal_subset (n := n) hW.isClosed
  intro f hf
  exact (hy f hf).2.self_of_nhds hyD

/-- Installing the actual SNC boundary on an ambient native record keeps its
invariant domain, native state, and exact cosupport. -/
theorem native_state_with_snc_boundary {k : ℕ} (Q : MarkedIdeal n X)
    {W : Set X} {H : ℕ → ℕ} (hQ : IsInvDomain k Q) (hState : NativeHSState Q W H)
    (E : List (Set X)) (hE : IsSNCDivisor n E) :
    let R : MarkedIdeal n X := { Q with E := E }
    IsInvDomain k R ∧ NativeHSState R W H ∧ R.cosupp = Q.cosupp := by
  have hTrans : IsTransverse n Q.N E := by
    rw [hState.2.2.1]
    exact SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE
  exact ⟨⟨⟨hQ.isWellFormed.isClosedSubmanifold_N, hQ.isWellFormed.isCoherent, hE, hTrans⟩,
    hQ.dimLE, hQ.one_le_d, hQ.isNonzeroAlongAt⟩, hState, rfl⟩

private theorem native_comparison_of_common_boundary {k : ℕ} (hn : 0 < n)
    (A B : MarkedIdeal n X) (hA : IsInvDomain k A) (hB : IsInvDomain k B)
    {W : Set X} {H : ℕ → ℕ} (hSA : NativeHSState A W H) (hSB : NativeHSState B W H)
    (hBoundary : A.E = B.E)
    (hNot : ∀ D ∈ A.E, ∀ x ∈ A.cosupp, x ∈ D → ¬ ∀ᶠ y in 𝓝 x, y ∈ D → y ∈ W) :
    LocWPEquiv A B ∧ A.cosupp = B.cosupp ∧
    (∀ D ∈ A.E, ∀ x ∈ A.cosupp, x ∈ D →
      divExpAlong n A.N A.ideal D x = 0 ∧ divExpAlong n B.N B.ideal D x = 0) ∧
    ∀ {Z : CMfd.{0} n} (T : BlowupTower X Z),
      IsCanonical A ((invFamily hn k).inv A) T ↔ IsCanonical B ((invFamily hn k).inv B) T := by
  have hEq := locWPEquiv_native hSA hSB hBoundary.symm
  have hCos := hSA.cosupp_eq.trans hSB.cosupp_eq.symm
  have hZero : ∀ D ∈ A.E, ∀ x ∈ A.cosupp, x ∈ D →
      divExpAlong n A.N A.ideal D x = 0 ∧ divExpAlong n B.N B.ideal D x = 0 := by
    intro D hDA x hx hxD
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hDA
    have hD := MonomialPart.isClosedSubmanifold_get hn hA.isWellFormed.isSNCDivisor i
    exact ⟨native_divExpAlong_eq_zero_of_boundary_noncontainment hSA hx hD hxD
      (hNot _ hDA x hx hxD), native_divExpAlong_eq_zero_of_boundary_noncontainment hSB
      (hCos ▸ hx) hD hxD (hNot _ hDA x hx hxD)⟩
  refine ⟨hEq, hCos, hZero, fun T => ?_⟩
  have hDims := SameCarrierDim.of_N_eq (hSA.2.2.1.trans hSB.2.2.1.symm)
  have hExp : ∀ D ∈ A.E, ∀ x ∈ A.cosupp, x ∈ D →
      B.d * divExpAlong n A.N A.ideal D x = A.d * divExpAlong n B.N B.ideal D x := by
    intro D hD x hx hxD
    obtain ⟨h₁, h₂⟩ := hZero D hD x hx hxD
    rw [h₁, h₂, mul_zero, mul_zero]
  exact HironakaG1OriginalUnequalMarkCanonical.invFamily_isCanonical_iff_of_local
    hn A B hA hB hEq hDims hExp T

/-- The actual pulled native records on one ambient overlap have identical
cosupports and canonical histories when their common boundary members have
noncontaining germs at the cut. The original marks may differ. -/
theorem native_boundary_comparison {k : ℕ} (hn : 0 < n) {Y O : CMfd.{0} n}
    (p : O ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    (q : O ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y)
    (P : MarkedIdeal n X) (Q : MarkedIdeal n Y)
    (hP : IsInvDomain k P) (hQ : IsInvDomain k Q)
    {W : Set X} {V : Set Y} {H : ℕ → ℕ}
    (hSP : NativeHSState P W H) (hSQ : NativeHSState Q V H)
    (hCarrier : p ⁻¹' W = q ⁻¹' V)
    (hBoundary : (MarkedIdeal.pullback p P).E = (MarkedIdeal.pullback q Q).E)
    (hNot : ∀ D ∈ (MarkedIdeal.pullback p P).E, ∀ x ∈ (MarkedIdeal.pullback p P).cosupp,
      x ∈ D → ¬ ∀ᶠ y in 𝓝 x, y ∈ D → y ∈ p ⁻¹' W) :
    let A := MarkedIdeal.pullback p P
    let B := MarkedIdeal.pullback q Q
    LocWPEquiv A B ∧
    A.cosupp = p ⁻¹' P.cosupp ∧ B.cosupp = q ⁻¹' Q.cosupp ∧
    A.cosupp = B.cosupp ∧
    (∀ D ∈ A.E, ∀ x ∈ A.cosupp, x ∈ D →
      divExpAlong n A.N A.ideal D x = 0 ∧ divExpAlong n B.N B.ideal D x = 0) ∧
    ∀ {Z : CMfd.{0} n} (T : BlowupTower O Z),
      IsCanonical A ((invFamily hn k).inv A) T ↔ IsCanonical B ((invFamily hn k).inv B) T := by
  let A := MarkedIdeal.pullback p P
  let B := MarkedIdeal.pullback q Q
  have hA : IsInvDomain k A := InvDomainTowerAlong.isInvDomain_pullback p hP
  have hB : IsInvDomain k B := InvDomainTowerAlong.isInvDomain_pullback q hQ
  have hSA : NativeHSState A (p ⁻¹' W) H := hSP.pullback p
  have hSB : NativeHSState B (p ⁻¹' W) H := by
    rw [hCarrier]
    exact hSQ.pullback q
  obtain ⟨hEq, hCos, hZero, hCanonical⟩ :=
    native_comparison_of_common_boundary hn A B hA hB hSA hSB hBoundary hNot
  exact ⟨hEq, cosupp_pullback_eq hP.isWellFormed.isCoherent,
    cosupp_pullback_eq hQ.isWellFormed.isCoherent, hCos, hZero, hCanonical⟩

private theorem reduced_nonzero_at_native_cut {k : ℕ} {Q : MarkedIdeal n X}
    {W : Set X} {H : ℕ → ℕ} (hQ : IsInvDomain k Q) (hState : NativeHSState Q W H)
    {x : X} (hx : x ∈ Q.cosupp) :
    IsNonzeroAlongAt univ (vanishingIdeal (n := n) W) x := by
  obtain ⟨_, hW, hN, hQI, V, S, k', a, w, _, hPos, _, _, _, _, hAt⟩ := hState
  obtain ⟨_, _, _, _, _, hLe⟩ :=
    HironakaActualNativeBornWeightedExponents.actual_native_point_reduced_stalk_dictionary
      S a w hPos W hW Q hQI x (hAt x hx)
  have hNZ := hQ.isNonzeroAlongAt x (Q.cosupp_subset_N hx)
  rw [hN] at hNZ
  obtain ⟨g, hg, hFreq⟩ := hNZ
  exact ⟨g, hLe g hg, hFreq⟩

/-- For two native records on an actual open of the current ambient, the
boundary born in an original singular-centred test history supplies the
noncontainment needed for canonical comparison. The initial boundary of
that original history is empty. -/
theorem native_comparison_on_born_boundary {k : ℕ} (hn : 0 < n) {Y : CMfd.{0} n}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W) (T : BlowupTower X Y)
    (hTest : IsGeoTestTower (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T)
    (hStage : StageCentres (fun R C => C ⊆ singularSet (n := n) (strictTransform n R.proj W)) T)
    (U : Opens Y) (P Q : MarkedIdeal n (CMfd.of (n := n) U))
    (hP : IsInvDomain k P) (hQ : IsInvDomain k Q) (H : ℕ → ℕ)
    (hSP : NativeHSState P ((Subtype.val : U → Y) ⁻¹' strictTransform n T.proj W) H)
    (hSQ : NativeHSState Q ((Subtype.val : U → Y) ⁻¹' strictTransform n T.proj W) H)
    (hEP : P.E = (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T).E.map
      ((Subtype.val : U → Y) ⁻¹' ·)) (hEQ : Q.E = P.E) :
    LocWPEquiv P Q ∧ P.cosupp = Q.cosupp ∧
    (∀ D ∈ P.E, ∀ x ∈ P.cosupp, x ∈ D →
      divExpAlong n P.N P.ideal D x = 0 ∧ divExpAlong n Q.N Q.ideal D x = 0) ∧
    ∀ {Z : CMfd.{0} n} (R : BlowupTower (CMfd.of (n := n) U) Z),
      IsCanonical P ((invFamily hn k).inv P) R ↔ IsCanonical Q ((invFamily hn k).inv Q) R := by
  let M : MarkedIdeal n X := ⟨univ, [], vanishingIdeal (n := n) W, 1⟩
  let A := strictTransform n T.proj W
  let F := (geoTransformAlong M T).E
  have hM : M.IsWellFormed :=
    ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ, CartanIrreducible.cartanCoherence W hW,
      isSNCDivisor_nil, SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor isSNCDivisor_nil⟩
  have hF : IsSNCDivisor n F :=
    (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM T hTest).isSNCDivisor
  have hA := HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hW T
  have hIA := CartanIrreducible.cartanCoherence A hA
  apply native_comparison_of_common_boundary hn P Q hP hQ hSP hSQ hEQ.symm
  intro D hD x hx hxD hContains
  obtain ⟨B, hB, rfl⟩ := List.mem_map.mp (hEP ▸ hD)
  have hxB : x.val ∈ B := hxD
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hB
  have hBsm := hi ▸ MonomialPart.isClosedSubmanifold_get hn hF i
  have hBInv := hi ▸ HironakaNormalCrossingsFiniteMarkedCompletion.isInvertible_vanishingIdeal_snc_member hF i
  have hNZ : IsNonzeroAlongAt univ (vanishingIdeal (n := n) A) x.val := by
    apply (HironakaStepOneZeroContactRemainderGlueing.isNonzeroAlongAt_pullback_val_iff
      (N := univ) hIA U x).mp
    rw [SmoothCentreHomogeneity.pullback_val_vanishingIdeal, preimage_univ]
    exact reduced_nonzero_at_native_cut hP hSP hx
  have hBorn : B ∈ (geoTransformAlong M T).E.drop M.E.length := by
    simpa only [show M.E = [] from rfl, List.length_nil, List.drop_zero] using hB
  have hZero := HironakaActualSingularBornCriticalBoundary.born_boundary_vanishing_exponent_zero
    M W hW T hStage B hBorn hBsm hBInv x.val hNZ
  have hContainsY : ∀ᶠ y in 𝓝 x.val, y ∈ B → y ∈ A := by
    rw [← U.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq x]
    exact Filter.eventually_map.mpr hContains
  have hIHol : ∀ (y : Y) f, (vanishingIdeal (n := n) A).mem y f → HolomorphicAt n f y :=
    fun _ _ hf => hf.1
  have hDiv : IsDivNear n (vanishingIdeal (n := n) A) B 1 x.val := by
    filter_upwards [hContainsY] with y hy hyB
    rw [cosupport_one hIHol, univ_inter]
    exact VanishingIdealZeroLocus.subset_zeroLocus_vanishingIdeal A (hy hyB)
  have hNot := not_isDivNear_divExp_succ hIHol hxB (isNonzeroAlongAt_univ_iff.mp hNZ)
  rw [divExpAlong_univ] at hZero
  rw [hZero] at hNot
  exact hNot hDiv

end
end Hironaka.HironakaG8NativeBoundaryComparison
