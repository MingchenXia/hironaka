import Hironaka.Resolution.HironakaG8NativeActualSuccessor
import Hironaka.Resolution.HironakaG8FiniteWindowCount
import Hironaka.Blowup.BlowupExistenceCodimOne
import Hironaka.Resolution.HironakaG8CompactNativeFirstStep

/-! A compact phase on one fixed ambient manifold terminates through
literal canonical window histories and a compact footprint count. -/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8CompactNativePhase

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec ResolutionInvariantSeq HironakaG11InvBMClass HironakaG8LocalHistory
  HironakaEmbeddedAnalytic HironakaHolomorphicJetChartInvariance NormalCrossings
  HironakaG11PresLineState HironakaG11PresTowerState HironakaStageCenters
  HironakaActualPowerBoundaryExponents StrictTransformComposition BlowupExistenceCodimOne
  HironakaG8NativeActualSuccessor HironakaG8FiniteWindowCount HironakaLocallyFiniteResolutionSequence
  HironakaUniformHistoricalSuccessorOriginalRegular HironakaG8IntrinsicSingularBlockSchedule
  HironakaG8CompactNativeFirstStep HironakaActualWholeAmbientHSSuperlevel
  HironakaActualHistoricalOriginalSingularReference CanonicalCentres HironakaG1OriginalInvariantClassFunctorial

/-- A finite family of genuine native windows over the highest singular
profile gives one finite original-test phase on the actual ambient manifold.
At the endpoint every current singular point has strictly smaller profile. -/
theorem exists_finite_compact_native_phase_of_windows {n : ℕ} (hn : 0 < n)
    {X : CMfd.{0} n} {ι Λ : Type} [Finite ι] [LinearOrder Λ]
    (R : BMInvariant.{0,0} n (fun {A} P Q => LocWPEquiv (X := A) P Q) n Λ)
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    (E : List (Set X)) (hE : IsSNCDivisor n E)
    (H : ℕ → ℕ) (hHighest : ∀ x ∈ singularSet (n := n) W,
      toLex (hilbertSamuelAt (vanishingIdeal (n := n) W) x) ≤ toLex H)
    (D : Set X) (hD : IsCompact D)
    (hExact : D = {x | ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) W) x ℓ = H ℓ})
    (U : ι → Opens X) (hCover : ∀ x ∈ D, ∃ i, x ∈ U i)
    (P : ∀ i, MarkedIdeal n (CMfd.of (n := n) (U i))) (hP : ∀ i, IsInvDomain n (P i))
    (hState : ∀ i, NativeHSState (P i) ((Subtype.val : U i → X) ⁻¹' W) H)
    (hPE : ∀ i, (P i).E = E.map ((Subtype.val : U i → X) ⁻¹' ·))
    (e : ι → ℕ) (he : ∀ i, 1 ≤ e i) (d : ℕ) (hd : ∀ i, (powerMarked (P i) (e i)).d = d)
    (hNot : ∀ B ∈ E, ∀ x ∈ D, x ∈ B → ¬ ∀ᶠ z in 𝓝 x, z ∈ B → z ∈ W) :
    ∃ (Y : CMfd.{0} n) (T : BlowupTower X Y),
      IsGeoTestTower (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T ∧
      StageCentres (fun S C => C ⊆ singularSet (n := n) (strictTransform n S.proj W)) T ∧
      (∀ i, IsCanonical (powerMarked (P i) (e i))
        (R.toResolutionInvariant.inv (powerMarked (P i) (e i))) (restrict (U i) T)) ∧
      (∀ z ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n T.proj W)) z ℓ ≤
        hilbertSamuelAt (vanishingIdeal (n := n) W) (T.proj z) ℓ) ∧
      ∀ z ∈ singularSet (n := n) (strictTransform n T.proj W),
        toLex (hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n T.proj W)) z) < toLex H := by
  let M : MarkedIdeal n X := ⟨univ, E, vanishingIdeal (n := n) W, 1⟩
  let R₀ := R.toResolutionInvariant
  let Q (i : ι) := powerMarked (P i) (e i)
  let Good := {t : Σ Y : CMfd.{0} n, BlowupTower X Y //
    IsGeoTestTower M t.2 ∧
    StageCentres (fun S C => C ⊆ singularSet (n := n) (strictTransform n S.proj W)) t.2 ∧
    (∀ i, IsCanonical (Q i) (R₀.inv (Q i)) (restrict (U i) t.2)) ∧
    ∀ z ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n t.2.proj W)) z ℓ ≤
      hilbertSamuelAt (vanishingIdeal (n := n) W) (t.2.proj z) ℓ}
  let Done (p : Good) : Prop := ∀ z ∈ p.1.2.proj ⁻¹' D,
    toLex (hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n p.1.2.proj W)) z) < toLex H
  let hInit : Good := ⟨⟨X, .refl⟩, trivial, trivial, fun _ => trivial, by
    intro z ℓ
    simpa only [BlowupTower.proj_refl, strictTransform_id hW.isClosed, id_eq] using (le_rfl : hilbertSamuelAt (vanishingIdeal (n := n) W) z ℓ ≤ _)⟩
  have hExtend (p : Good) : ∃ (q : Good) (C : Set p.1.1) (π : q.1.1 → p.1.1)
      (hπ : IsBlowupAlong n C π), q.1.2 = .step p.1.2 C π hπ ∧
      C ⊆ p.1.2.proj ⁻¹' D ∧ (C = ∅ → Done p) := by
    obtain hDone | ⟨C, Z, π, hπ, hCne, hCF, _hSing, hTest, hStage, hCan, hLe⟩ :=
      native_phase_successor_along_actual_prefix hn R hW E hE H D hD hExact U hCover P hP hState
        hPE e he d hd hNot p.1.2 p.2.1 p.2.2.1 p.2.2.2.1
    · let hπ : IsBlowupAlong n (∅ : Set p.1.1) (id : p.1.1 → p.1.1) := isBlowupAlong_id_empty
      have hTest : IsGeoTestTower M (.step p.1.2 ∅ id hπ) :=
        ⟨p.2.1, (geoTransformAlong M p.1.2).isAdmissibleCentre_empty⟩
      have hStage : StageCentres (fun S C => C ⊆ singularSet (n := n) (strictTransform n S.proj W))
          (.step p.1.2 ∅ id hπ) := ⟨p.2.2.1, empty_subset _⟩
      have hCan (i : ι) : IsCanonical (Q i) (R₀.inv (Q i)) (restrict (U i) (.step p.1.2 ∅ id hπ)) :=
        ⟨p.2.2.2.1 i, Or.inl rfl⟩
      let q : Good := ⟨⟨p.1.1, .step p.1.2 ∅ id hπ⟩, hTest, hStage, hCan, p.2.2.2.2⟩
      exact ⟨q, ∅, id, hπ, rfl, empty_subset _, fun _ => hDone⟩
    · have hGlobal : ∀ z ℓ,
          hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n (BlowupTower.step p.1.2 C π hπ).proj W)) z ℓ ≤
            hilbertSamuelAt (vanishingIdeal (n := n) W) ((BlowupTower.step p.1.2 C π hπ).proj z) ℓ := by
        intro z ℓ
        rw [BlowupTower.proj_step, strictTransform_comp p.1.2.contMDiff_proj hπ.contMDiff W]
        exact (hLe z ℓ).trans (p.2.2.2.2 (π z) ℓ)
      let q : Good := ⟨⟨Z, .step p.1.2 C π hπ⟩, hTest, hStage, hCan, hGlobal⟩
      exact ⟨q, C, π, hπ, rfl, hCF, fun h => False.elim (hCne.ne_empty h)⟩
  choose next centre π hπ hStep hSubset hStop using hExtend
  let s := GrowingSeq.ofIterate (fun p : Good => p.1) next hInit rfl
    (fun p => ⟨centre p, π p, hπ p, hStep p⟩)
  let last (t : Σ Y : CMfd.{0} n, BlowupTower X Y) : Σ Y : CMfd.{0} n, Set Y :=
    match t with
    | ⟨_, .refl⟩ => ⟨X, ∅⟩
    | ⟨_, .step _ C _ _⟩ => ⟨_, C⟩
  have hCentre (j : ℕ) : stepCentre s j = centre (next^[j] hInit) := by
    obtain ⟨f, hf, heq⟩ := exists_step_map s j
    have hSelected : last (s.stage (j + 1)) = ⟨(s.stage j).1, stepCentre s j⟩ := by
      change last ⟨(s.stage (j + 1)).1, (s.stage (j + 1)).2⟩ = _
      rw [heq]
    let p := next^[j] hInit
    have hChosen : last (next p).1 = ⟨p.1.1, centre p⟩ := by
      change last ⟨(next p).1.1, (next p).1.2⟩ = _
      rw [hStep p]
    have hj : s.stage (j + 1) = (next p).1 := by
      change (next^[j + 1] hInit).1 = (next p).1
      rw [Function.iterate_succ_apply']
    have h := hSelected.symm.trans ((congrArg last hj).trans hChosen)
    exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have hUnions : D ⊆ ⋃ i, (U i : Set X) := fun x hx =>
    let ⟨i, hi⟩ := hCover x hx
    mem_iUnion.mpr ⟨i, hi⟩
  have hDomain (i : ι) : IsInvDomain n (Q i) := powerMarked_isInvDomain (P i) (hP i) (he i)
  have hCan (i : ι) (j : ℕ) : IsCanonical (Q i) (R₀.inv (Q i)) (restrict (U i) (s.stage j).2) :=
    (next^[j] hInit).2.2.2.1 i
  have hHit (j : ℕ) (hNonempty : ∀ a ≤ j, (stepCentre s a).Nonempty) :
      (centreImage s j ∩ D).Nonempty := by
    obtain ⟨x, hx⟩ := hNonempty j le_rfl
    exact ⟨(s.stage j).2.proj x, ⟨x, hx, rfl⟩, hSubset (next^[j] hInit) (hCentre j ▸ hx)⟩
  obtain ⟨j, hj⟩ := exists_empty_stepCentre_of_finite_compact_cover R₀ s U Q hDomain hD hUnions
    (fun i j _ => hCan i j) hHit
  let p := next^[j] hInit
  have hDone : Done p := hStop p ((hCentre j).symm.trans hj)
  have hGeometry := actual_singular_history_original_regular_protection W hW p.1.2
    (intrinsic_stage_native_history W p.1.2 p.2.2.1)
  refine ⟨p.1.1, p.1.2, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2, fun z hz => ?_⟩
  have hOriginal := hGeometry.2.2.2.2.2.1 hz
  have hLe := Pi.toLex_monotone (p.2.2.2.2 z)
  have ht := hHighest (p.1.2.proj z) hOriginal
  by_cases hEq : toLex (hilbertSamuelAt (vanishingIdeal (n := n) W) (p.1.2.proj z)) = toLex H
  · apply hDone z
    rw [mem_preimage, hExact]
    exact fun ℓ => congrFun (congrArg ofLex hEq) ℓ
  · exact hLe.trans_lt (lt_of_le_of_ne ht hEq)

/-- A compact singular locus supplies its own finite actual native phase
on the full boundary of the original ambient manifold. -/
theorem exists_finite_compact_native_phase_of_compact_singular {n : ℕ} (hn : 0 < n)
    {X : CMfd.{0} n} {Λ : Type} [LinearOrder Λ]
    (R : BMInvariant.{0,0} n (fun {A} P Q => LocWPEquiv (X := A) P Q) n Λ)
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact (singularSet (n := n) W))
    (hns : ¬ IsClosedSubmanifold n W)
    (E : List (Set X)) (hE : IsSNCDivisor n E)
    (hNot : ∀ B ∈ E, ∀ x ∈ singularSet (n := n) W, x ∈ B → ¬ ∀ᶠ z in 𝓝 x, z ∈ B → z ∈ W) :
    ∃ a ∈ singularSet (n := n) W,
      (∀ x ∈ singularSet (n := n) W, toLex (hilbertSamuelAt (vanishingIdeal (n := n) W) x) ≤
        toLex (hilbertSamuelAt (vanishingIdeal (n := n) W) a)) ∧
      ∃ (Y : CMfd.{0} n) (T : BlowupTower X Y),
        IsGeoTestTower (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T ∧
        StageCentres (fun S C => C ⊆ singularSet (n := n) (strictTransform n S.proj W)) T ∧
        (∀ z ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n T.proj W)) z ℓ ≤
          hilbertSamuelAt (vanishingIdeal (n := n) W) (T.proj z) ℓ) ∧
        ∀ z ∈ singularSet (n := n) (strictTransform n T.proj W),
          toLex (hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n T.proj W)) z) <
            toLex (hilbertSamuelAt (vanishingIdeal (n := n) W) a) := by
  obtain ⟨a, ι, U, P, e, d, _, _, _, _, _, ha, hHighest, hI, hRecords, hCover, _⟩ :=
    exists_compact_native_first_step_of_compact_singular hn R hW hK hns E hE hNot
  let : Finite ι := hI
  let H := hilbertSamuelAt (vanishingIdeal (n := n) W) a
  let D : Set X := {x | ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) W) x ℓ = H ℓ}
  have hDS : D ⊆ singularSet (n := n) W :=
    actual_original_singular_profile_locus_subset_current_singular W hW a ha W hW
  have hD : IsCompact D := by
    have hExact : D = singularSet (n := n) W ∩
        actualWholeAmbientHSSuperlevel (vanishingIdeal (n := n) W) H := by
      ext x
      constructor
      · intro hx
        exact ⟨hDS hx, fun ℓ => (hx ℓ).ge⟩
      · rintro ⟨hx, hge⟩
        exact fun ℓ => congrFun (congrArg ofLex
          (le_antisymm (hHighest x hx) (Pi.toLex_monotone hge))) ℓ
    rw [hExact]
    exact hK.of_isClosed_subset
      ((isClosed_singularSet hW.isClosed).inter
        (isComplexAnalyticSubset_actualWholeAmbientHSSuperlevel _
          (CartanIrreducible.cartanCoherence W hW) H).isClosed)
      inter_subset_left
  obtain ⟨Y, T, hTest, hStage, _, hLe, hDrop⟩ :=
    exists_finite_compact_native_phase_of_windows hn R hW E hE H hHighest D hD rfl U hCover
      P (fun i => (hRecords i).1) (fun i => (hRecords i).2.1)
      (fun i => (hRecords i).2.2.1) e (fun i => (hRecords i).2.2.2.1) d
      (fun i => (hRecords i).2.2.2.2) (fun B hB x hx => hNot B hB x (hDS hx))
  exact ⟨a, ha, hHighest, Y, T, hTest, hStage, hLe, hDrop⟩

/-- The finite strict-drop phase for a compact analytic carrier. -/
theorem exists_finite_compact_native_phase {n : ℕ} (hn : 0 < n)
    {X : CMfd.{0} n} {Λ : Type} [LinearOrder Λ]
    (R : BMInvariant.{0,0} n (fun {A} P Q => LocWPEquiv (X := A) P Q) n Λ)
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W)
    (hns : ¬ IsClosedSubmanifold n W)
    (E : List (Set X)) (hE : IsSNCDivisor n E)
    (hNot : ∀ B ∈ E, ∀ x ∈ singularSet (n := n) W, x ∈ B → ¬ ∀ᶠ z in 𝓝 x, z ∈ B → z ∈ W) :
    ∃ a ∈ singularSet (n := n) W,
      (∀ x ∈ singularSet (n := n) W, toLex (hilbertSamuelAt (vanishingIdeal (n := n) W) x) ≤
        toLex (hilbertSamuelAt (vanishingIdeal (n := n) W) a)) ∧
      ∃ (Y : CMfd.{0} n) (T : BlowupTower X Y),
        IsGeoTestTower (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T ∧
        StageCentres (fun S C => C ⊆ singularSet (n := n) (strictTransform n S.proj W)) T ∧
        (∀ z ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n T.proj W)) z ℓ ≤
          hilbertSamuelAt (vanishingIdeal (n := n) W) (T.proj z) ℓ) ∧
        ∀ z ∈ singularSet (n := n) (strictTransform n T.proj W),
          toLex (hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n T.proj W)) z) <
            toLex (hilbertSamuelAt (vanishingIdeal (n := n) W) a) := by
  exact exists_finite_compact_native_phase_of_compact_singular hn R hW
    (hK.of_isClosed_subset (isClosed_singularSet hW.isClosed) (singularSet_subset _)) hns E hE hNot

/-- The original canonical invariant yields a finite strict-drop phase for
any compact singular analytic set with empty initial boundary. -/
theorem exists_finite_compact_native_phase_empty_boundary {n : ℕ} (hn : 0 < n)
    {X : CMfd.{0} n} {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    (hK : IsCompact W) (hns : ¬ IsClosedSubmanifold n W) :
    ∃ a ∈ singularSet (n := n) W,
      (∀ x ∈ singularSet (n := n) W, toLex (hilbertSamuelAt (vanishingIdeal (n := n) W) x) ≤
        toLex (hilbertSamuelAt (vanishingIdeal (n := n) W) a)) ∧
      ∃ (Y : CMfd.{0} n) (T : BlowupTower X Y),
        IsGeoTestTower (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T ∧
        StageCentres (fun S C => C ⊆ singularSet (n := n) (strictTransform n S.proj W)) T ∧
        (∀ z ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n T.proj W)) z ℓ ≤
          hilbertSamuelAt (vanishingIdeal (n := n) W) (T.proj z) ℓ) ∧
        ∀ z ∈ singularSet (n := n) (strictTransform n T.proj W),
          toLex (hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n T.proj W)) z) <
            toLex (hilbertSamuelAt (vanishingIdeal (n := n) W) a) := by
  let R : BMInvariant.{0,0} n (fun {A} P Q => LocWPEquiv (X := A) P Q) n (ValTy n) :=
    ⟨canonicalInvariant n, classFunctorialFor_canonicalInvariant n⟩
  exact exists_finite_compact_native_phase hn R hW hK hns [] isSNCDivisor_nil
    (fun _ hB => False.elim (List.not_mem_nil hB))

end
end Hironaka.HironakaG8CompactNativePhase
