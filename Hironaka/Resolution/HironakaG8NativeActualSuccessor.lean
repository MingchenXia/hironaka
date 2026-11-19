import Hironaka.Resolution.HironakaG8NativePrefixReplay
import Hironaka.Resolution.HironakaG8NativeNumericalOverlap
import Hironaka.Resolution.HironakaG8NativeGlobalSuccessor
import Hironaka.Resolution.HironakaG8SurfaceLimitEndpoint
import Hironaka.Resolution.HironakaActualWholeAmbientHSSuperlevel
import Hironaka.Resolution.HironakaOriginalSelectedContactCosupport

/-! Replay the same native phase records on the literal restrictions
of their common full-boundary ambient prefix. -/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8NativeActualSuccessor

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec HironakaG11InvBMClass HironakaG8LocalHistory
  HironakaEmbeddedAnalytic HironakaHolomorphicJetChartInvariance NormalCrossings
  HironakaG11PresLineState HironakaG11PresTowerState HomogenizedGlueingTower HironakaStageCenters
  HironakaActualVanishingIntrinsicHSTransport HironakaActualPowerBoundaryExponents
  HironakaG8NativeNumericalOverlap HironakaG8NativeGlobalSuccessor HironakaG8NativePrefixReplay
  HironakaG8SurfaceLimitEndpoint HironakaActualWholeAmbientHSSuperlevel
  HironakaOriginalSelectedContactCosupport StepOneLowerDomain

/-- Once the original ambient prefix is canonical on all literal powered
native restrictions, either the profile has dropped over the original
compact stratum or a nonempty global singular step extends every restriction. -/
theorem native_phase_successor_along_actual_prefix {n : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} {ι Λ : Type} [LinearOrder Λ]
    (R : BMInvariant n (fun {A} P Q => LocWPEquiv (X := A) P Q) n Λ)
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    (E : List (Set X)) (hE : IsSNCDivisor n E)
    (H : ℕ → ℕ) (D : Set X) (hD : IsCompact D)
    (hExact : D = {x | ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) W) x ℓ = H ℓ})
    (U : ι → Opens X) (hCover : ∀ x ∈ D, ∃ i, x ∈ U i)
    (P : ∀ i, MarkedIdeal n (CMfd.of (n := n) (U i))) (hP : ∀ i, IsInvDomain n (P i))
    (hState : ∀ i, NativeHSState (P i) ((Subtype.val : U i → X) ⁻¹' W) H)
    (hPE : ∀ i, (P i).E = E.map ((Subtype.val : U i → X) ⁻¹' ·))
    (e : ι → ℕ) (he : ∀ i, 1 ≤ e i) (d : ℕ) (hd : ∀ i, (powerMarked (P i) (e i)).d = d)
    (hNot : ∀ B ∈ E, ∀ x ∈ D, x ∈ B → ¬ ∀ᶠ z in 𝓝 x, z ∈ B → z ∈ W)
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T)
    (hStage : StageCentres (fun S C => C ⊆ singularSet (n := n) (strictTransform n S.proj W)) T)
    (hCan : ∀ i, IsCanonical (powerMarked (P i) (e i))
      (R.toResolutionInvariant.inv (powerMarked (P i) (e i))) (restrict (U i) T)) :
    let M : MarkedIdeal n X := ⟨univ, E, vanishingIdeal (n := n) W, 1⟩
    let A := strictTransform n T.proj W
    (∀ z ∈ T.proj ⁻¹' D, toLex (hilbertSamuelAt (vanishingIdeal (n := n) A) z) < toLex H) ∨
    ∃ (C : Set Y) (Z : CMfd.{0} n) (π : Z → Y) (hπ : IsBlowupAlong n C π),
      C.Nonempty ∧ C ⊆ T.proj ⁻¹' D ∧ C ⊆ singularSet (n := n) A ∧
      IsGeoTestTower M (.step T C π hπ) ∧
      StageCentres (fun S B => B ⊆ singularSet (n := n) (strictTransform n S.proj W)) (.step T C π hπ) ∧
      (∀ i, IsCanonical (powerMarked (P i) (e i))
        (R.toResolutionInvariant.inv (powerMarked (P i) (e i))) (restrict (U i) (.step T C π hπ))) ∧
      ∀ z ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n π A)) z ℓ ≤
        hilbertSamuelAt (vanishingIdeal (n := n) A) (π z) ℓ := by
  let M : MarkedIdeal n X := ⟨univ, E, vanishingIdeal (n := n) W, 1⟩
  let A := strictTransform n T.proj W
  let V (i : ι) : Opens Y := openPreimage T (U i)
  let S (i : ι) := restrict (U i) T
  let Q (i : ι) := powerMarked (P i) (e i)
  let Q' (i : ι) := geoTransformAlong (Q i) (S i)
  let R₀ := R.toResolutionInvariant
  have hM : M.IsWellFormed := ⟨isClosedSubmanifold_univ,
    CartanIrreducible.cartanCoherence W hW, hE, SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
  have hA : IsComplexAnalyticSubset (n := n) A :=
    HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hW T
  have hStrict : strictAlong T W = A := intrinsic_strictAlong_eq W hW T hStage
  have hQ (i : ι) : IsInvDomain n (Q i) := powerMarked_isInvDomain (P i) (hP i) (he i)
  have hQT (i : ι) : IsGeoTestTower (Q i) (S i) :=
    R₀.isInvValue.isGeoTestTower_of_isCanonical (hQ i) (S i) (hCan i)
  have hLocal (i : ι) : (Q' i).E = (geoTransformAlong M T).E.map ((Subtype.val : V i → Y) ⁻¹' ·) ∧
      HSTowerState (Q' i) ((Subtype.val : V i → Y) ⁻¹' A) H := by
    rw [← hStrict]
    exact powered_native_state_after_actual_restriction M hM T hT W H (U i) (P i)
      (hP i) (hState i) (hPE i) (e i) (he i) (hQT i)
  have hBase (i : ι) : (Q i).cosupp = (Subtype.val : U i → X) ⁻¹' D := by
    rw [show (Q i).cosupp = (P i).cosupp from powerMarked_cosupp (P i) (hP i) (he i),
      (hState i).cosupp_eq, hExact]
    ext x
    simp only [mem_ofPred_eq, mem_preimage, hilbertSamuelAt_vanishing_actual_open_any]
  have hProj (i : ι) (y : V i) (hy : y ∈ (Q' i).cosupp) : T.proj y.val ∈ D := by
    have h := proj_mem_cosupp_of_mem_cosupp (hQ i).isWellFormed.isClosedSubmanifold_N
      (hQ i).isWellFormed.isCoherent (S i) (hQT i) hy
    rw [hBase i] at h
    change ((restrict (U i) T).proj y).val ∈ D at h
    simpa only [proj_restrict] using h
  have hStateAt (i : ι) := (hLocal i).2 (.refl : BlowupTower (CMfd.of (n := n) (V i)) _) trivial
  have hUpper (i : ι) (y : V i) (ℓ : ℕ) : hilbertSamuelAt (vanishingIdeal (n := n) A) y.val ℓ ≤ H ℓ :=
    (hilbertSamuelAt_vanishing_actual_open_any (n := n) (V i) A y ℓ).symm.le.trans ((hStateAt i).2.2.1 y ℓ)
  have hCut (i : ι) (y : V i) : y ∈ (Q' i).cosupp ↔
      ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) A) y.val ℓ = H ℓ := by
    simpa only [geoTransformAlong_refl, strictAlong_refl, hilbertSamuelAt_vanishing_actual_open_any] using (hStateAt i).2.2.2.1 y
  have hSing (i : ι) (y : V i) (hy : y ∈ (Q' i).cosupp) : y.val ∈ singularSet (n := n) A := by
    have h := (hStateAt i).2.2.2.2 hy
    change y ∈ singularSet (n := n) ((Subtype.val : V i → Y) ⁻¹' A) at h
    rw [HironakaResolutionSpaceLocal.singularSet_preimage_val] at h
    exact h
  let F := T.proj ⁻¹' D ∩ actualWholeAmbientHSSuperlevel (vanishingIdeal (n := n) A) H
  have hF : IsCompact F :=
    ((HironakaLocalPrincipalization.isProperMap_proj T).isCompact_preimage hD).inter_right
      (isComplexAnalyticSubset_actualWholeAmbientHSSuperlevel _
        (CartanIrreducible.cartanCoherence A hA) H).isClosed
  have hFoot (i : ι) (y : V i) (hy : y ∈ (Q' i).cosupp) : y.val ∈ F :=
    ⟨hProj i y hy, fun ℓ => ((hCut i y).mp hy ℓ).ge⟩
  have hCoverF : ∀ y ∈ F, ∃ (i : ι) (hy : y ∈ V i), (⟨y, hy⟩ : V i) ∈ (Q' i).cosupp := by
    intro y hy
    obtain ⟨i, hi⟩ := hCover (T.proj y) hy.1
    exact ⟨i, hi, (hCut i ⟨y, hi⟩).mpr fun ℓ => le_antisymm (hUpper i ⟨y, hi⟩ ℓ) (hy.2 ℓ)⟩
  by_cases hNe : F.Nonempty
  · have hOverlap (i j : ι) (y : Y) (hi : y ∈ V i) (hj : y ∈ V j)
        (hy : (⟨y, hi⟩ : V i) ∈ (Q' i).cosupp) :
        (⟨y, hj⟩ : V j) ∈ (Q' j).cosupp ∧ R₀.inv (Q i) (S i) ⟨y, hi⟩ = R₀.inv (Q j) (S j) ⟨y, hj⟩ := by
      refine native_window_values_agree_along hn R (U i) (U j) (P i) (P j) (hP i) (hP j)
        W H (hState i) (hState j) E (hPE i) (hPE j) (e i) (e j) (he i) (he j)
        ((hd i).trans (hd j).symm) ?_ T (hCan i) (hCan j) hi hj hy
      intro B hB x hx hxB
      apply hNot B hB x.val ?_ hxB
      have hxQ : x ∈ (Q i).cosupp := (powerMarked_cosupp (P i) (hP i) (he i)).symm ▸ hx
      rw [hBase i] at hxQ
      exact hxQ
    obtain ⟨m, hBound, hAttain⟩ := exists_actual_native_compact_maximum_along R₀ V F hF hNe
      Q S hQ hCan hCoverF hFoot hOverlap
    obtain ⟨C, Z, π, hπ, hCne, hCF, hCS, _, hNext, hTrace, _, hLe⟩ :=
      exists_actual_native_global_maximum_blowup_along R₀ hA (geoTransformAlong M T).E V F hF.isClosed
        (fun y hy => by obtain ⟨i, hi, _⟩ := hCoverF y hy; exact ⟨i, hi⟩)
        Q S hQ hCan (fun i => (hLocal i).1) H (fun i y hy => ⟨hSing i y hy, (hCut i y).mp hy⟩)
        hFoot hOverlap m hBound hAttain
    have hCos : W ⊆ M.cosupp := by
      exact (HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hW.isClosed E).ge
    have hStay : A ⊆ (geoTransformAlong M T).cosupp := by
      rw [← hStrict]
      exact strictAlong_subset_cosupp_of_subset M hM.isClosedSubmanifold_N hM.isCoherent hCos T hT
    have hAdm : (geoTransformAlong M T).IsAdmissibleCentre C := by
      refine ⟨hNext.2.1, hCS.trans ((singularSet_subset A).trans hStay), hNext.2.2.2⟩
    refine Or.inr ⟨C, Z, π, hπ, hCne, hCF.trans inter_subset_left, hCS, ⟨hT, hAdm⟩,
      ⟨hStage, hCS⟩, ?_, hLe⟩
    intro i
    refine ⟨hCan i, ?_⟩
    rw [hTrace i]
    by_cases hHit : ({x | x ∈ (Q' i).cosupp ∧ R₀.inv (Q i) (S i) x = m} : Set (V i)).Nonempty
    · obtain ⟨x, hx, hxm⟩ := hHit
      right
      ext y
      constructor
      · rintro ⟨hy, hym⟩
        exact ⟨hy, fun z hz => (hBound i z hz).trans_eq hym.symm⟩
      · rintro ⟨hy, hyMax⟩
        exact ⟨hy, le_antisymm (hBound i y hy) (hxm.symm.trans_le (hyMax x hx))⟩
    · exact Or.inl (not_nonempty_iff_eq_empty.mp hHit)
  · refine Or.inl (fun z hz => ?_)
    obtain ⟨i, hi⟩ := hCover (T.proj z) hz
    have hLe : ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) A) z ℓ ≤ H ℓ :=
      hUpper i ⟨z, hi⟩
    apply lt_of_le_of_ne (Pi.toLex_monotone hLe)
    intro hEq
    exact hNe ⟨z, hz, fun ℓ => (congrFun (congrArg ofLex hEq) ℓ).ge⟩

end
end Hironaka.HironakaG8NativeActualSuccessor
