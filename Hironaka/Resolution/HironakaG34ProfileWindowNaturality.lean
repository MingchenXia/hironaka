import Hironaka.Resolution.HironakaG34ProfileBlockEquivariance

/-!
# Naturality of the profile windows; equivariance of the profile-block concatenation (seventh brick of EQ_d)

Lane G34 (run 0080, round 9).  Blueprint: `hironaka-g34-resume-profile-window-naturality.tex`.  Route note:
`work/hironaka-resume-20261111/G34/GENERAL-D-ROUTE.md` §1 (row "carrier": orders and the distinct count are local and natural).

Along a prefix `T` with `T|_V ≅ T|_{V'}` over a biholomorphism `φ` preserving `W` and the members of `E` (last-stage map
`χ`), the chronological rows at the last stage are the residual parts of the CURRENT data, which `χ` preserves; so their
ordinary orders along the current carrier and their distinct proper count are `χ`-invariant, and so is the profile window
(an interior of a condition on these numbers).  Hence appending a profile block of
`HironakaG34ProfileBlockEquivariance.exists_actual_global_original_profile_blocks_equivariant` to an equivariant prefix
keeps it equivariant.

## Main results

* `mem_interior_iff_of_homeomorph`: a homeomorphism of opens preserving a set preserves its interior;
* **`order_count_isTowerIso`**: the row orders and the distinct count at the last stage are `χ`-invariant;
* **`mem_profileWindow_iff_of_isTowerIso`**: the profile window is `χ`-invariant;
* **`isEquivariant_append_profile_block`**: `T` equivariant for `(W, E)` and `Q` equivariant for the current data and
  the profile window `⇒` `T Q` equivariant for `(W, E)`.

New file; no existing statement changed; no named input.  Sorry-free.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaG34ProfileWindowNaturality
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong MarkedIdealBiholomorphism
  NormalCrossings NormalCrossingsComparison NormalCrossingsInvariance
  RelativePrincipalizationSpan RestrictedIdealExtension InvertibleIdealQuotient
  HironakaActualRetainedBoundaryJointStep HironakaActualRetainedBornResidualSeed
  HironakaActualRetainedBornResidualHistory HironakaActualRetainedBornResidualOpen
  HironakaActualRetainedBoundaryMaskBlock HironakaActualRetainedBoundaryProfileExit
  HironakaActualDefectProfileWindows HironakaG4PreparedCentreCoordinates
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualFiniteMemberProduct
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpActualEmptyChronologicalDefect
  HironakaSharpActualEquimultipleResidualHistory HironakaG4RecordedTowerResidualCompatibility
  HironakaSharpOriginalProductTraceOrder HironakaG4CompactWholeMonomialMaskPhase
  HironakaSharpOriginalMultiBoundaryBadLocus MonomialPartAlong MonomialPartEtale
  GermIdealOrder DivisorExponentAlong MemberInterLocusAlong IdealWeightPowers
  BlowupTowerIsomorphism BlowupTowerSplitIso MarkedIdealRestrictOpen
  DerivativeIdealAlongEtale HironakaG34MaskFoldEquivariance
  HironakaG34ProfileBlockEquivariance

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- **A homeomorphism of opens preserving a set preserves its interior.** -/
theorem mem_interior_iff_of_homeomorph {M : Type*} [TopologicalSpace M] {O O' : Opens M} (h : O ≃ₜ O')
    {S : Set M} (hS : ∀ p : O, ((h p : O') : M) ∈ S ↔ (p : M) ∈ S) (p : O) :
    ((h p : O') : M) ∈ interior S ↔ (p : M) ∈ interior S := by
  have hmap : ∀ {P : Opens M} (x : P), map (Subtype.val : P → M) (𝓝 x) = 𝓝 (x : M) :=
    fun {P} _ => P.isOpen.isOpenMap_subtype_val.map_nhds_eq continuous_subtype_val.continuousAt
  rw [mem_interior_iff_mem_nhds, mem_interior_iff_mem_nhds, ← hmap, ← hmap, Filter.mem_map, Filter.mem_map,
    ← h.map_nhds_eq, Filter.mem_map]
  have hpre : h ⁻¹' ((Subtype.val : O' → M) ⁻¹' S) = (Subtype.val : O → M) ⁻¹' S := Set.ext hS
  rw [hpre]

private theorem open_iso_local_inverse (U : Opens X)
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ U) (z : Y) :
    ∃ ψ : X → Y,IsLocalInverseAt n ((Subtype.val : U → X) ∘ e) ψ z := by
  let ψ := e.symm ∘ openInv U (e z)
  have hInv := isLocalInverseAt_val (n := n) U (e z)
  refine ⟨ψ,⟨?_,?_,?_,?_⟩⟩
  · exact Eventually.of_forall fun w =>
      ((contMDiff_subtype_val.comp e.contMDiff) w).mdifferentiableAt (by simp)
  · filter_upwards [hInv.mdiff_inv] with x hx
    exact ((e.symm.contMDiff _).mdifferentiableAt (by simp)).comp x hx
  · filter_upwards [e.contMDiff.continuous.continuousAt.eventually hInv.left_inv] with w hw
    change e.symm (openInv U (e z) ((e w).val))=w
    rw [hw,e.symm_apply_apply]
  · filter_upwards [hInv.right_inv] with x hx
    change (e (e.symm (openInv U (e z) x))).val=x
    rw [e.apply_symm_apply]
    exact hx

theorem ordinary_order_pullback_open_iso (hn : 0 < n) {N : Set X} {I : GermIdeal n X}
    (hN : IsClosedSubmanifold n N) (hI : I.IsCoherent)
    (hnz : ∀ x ∈ N,IsNonzeroAlongAt N I x) (U : Opens X)
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ U) (z : Y) :
    ordinaryTraceOrder (((Subtype.val : U → X) ∘ e) ⁻¹' N)
      (GermIdeal.pullback (m := n) ((Subtype.val : U → X) ∘ e) I) z=
      ordinaryTraceOrder N I (e z).val := by
  exact NonmonomialOrderLocal.nmOrd_pullback_of_local hn
    (fun y => open_iso_local_inverse U e y) (ordinaryTraceMarked_isWellFormed hN hI) hnz z

private theorem count_pullback_open_iso {m : ℕ} (F : Fin m → GermIdeal n X)
    (hc : ∀ i,(F i).IsCoherent) (U : Opens X)
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ U) (z : Y) :
    actualDistinctProperCount (fun i => GermIdeal.pullback (m := n) ((Subtype.val : U → X) ∘ e) (F i)) z=
      actualDistinctProperCount F (e z).val := by
  let FV := fun i => GermIdeal.pullback (m := n) (Subtype.val : U → X) (F i)
  have hFam : (fun i => GermIdeal.pullback (m := n) ((Subtype.val : U → X) ∘ e) (F i))=
      (fun i => GermIdeal.pullback (m := n) e (FV i)) := by
    funext i
    exact GermIdealTotalTransform.pullback_comp contMDiff_subtype_val e.contMDiff (hc i)
  rw [hFam]
  exact (actual_distinct_proper_count_biholo (X := CMfd.of (n := n) U) e FV
    (fun i => GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val (hc i)) z).trans
      (HironakaSharpActualDistinctCountOpenNaturality.actual_distinct_proper_count_open F hc U (e z))

section Window

variable {V V' : Opens X}
  (φ : CMfd.of (n := n) V ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) V')

/-- **The row orders and the distinct count at the last stage of an equivariant prefix are invariant**: if `φ` preserves
`W` and the members of `E`, and `χ` is the last-stage map of `T|_V ≅ T|_{V'}` over `φ`, then at every point `p` over `V`
the ordinary order of each chronological row along the current carrier and the distinct proper count of the rows are the
same at `p` and at `χ p`. -/
theorem order_count_isTowerIso (hn : 0 < n) {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hφN : ∀ p : V, ((φ p : V') : X) ∈ W ↔ (p : X) ∈ W)
    (hφH : ∀ H ∈ E, ∀ p : V, ((φ p : V') : X) ∈ H ↔ (p : X) ∈ H)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    {χ : CMfd.of (n := n) (openPreimage T V) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T V')} (hχ : IsTowerIso φ (restrict V T) (restrict V' T) χ)
    (p : openPreimage T V) :
    (∀ i : Fin E.length, ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal ((χ p : openPreimage T V') : Y) =
      ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal (p : Y)) ∧
    actualDistinctProperCount (fun i : Fin E.length =>
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal) ((χ p : openPreimage T V') : Y) =
      actualDistinctProperCount (fun i : Fin E.length =>
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal) (p : Y) := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let O := E.map (strictAlong T)
  let F := fun i : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
  have hRec := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hφH' : ∀ H ∈ E ++ [], ∀ p : V, ((φ p : V') : X) ∈ H ↔ (p : X) ∈ H := by
    rw [List.append_nil]
    exact hφH
  have hFull' : IsGeoTestTower (geometricTemplate (univ : Set X) (E ++ [])) T := by
    rw [List.append_nil]
    exact hFull
  obtain ⟨hcN, hcH⟩ := HironakaG34MaskStepEquivariance.current_data_preserved φ hW hφN hφH' T hT hFull' hχ
  let f₁ : CMfd.of (n := n) (openPreimage T V) → Y := fun q => ((χ q : openPreimage T V') : Y)
  let f₂ : CMfd.of (n := n) (openPreimage T V) → Y := Subtype.val
  have hf₁ : HironakaBaseChange.IsOpenHoloEmbedding n f₁ := ⟨openPreimage T V', χ, fun _ => rfl⟩
  have hf₂ : HironakaBaseChange.IsOpenHoloEmbedding n f₂ :=
    HironakaBaseChange.isOpenHoloEmbedding_val (n := n) (openPreimage T V)
  have hNN : f₁ ⁻¹' A.N = f₂ ⁻¹' A.N := Set.ext fun q => hcN q
  have hHH : ∀ H ∈ O ++ A.E, f₁ ⁻¹' H = f₂ ⁻¹' H := fun H hH => Set.ext fun q => hcH H hH q
  have hEE : A.E.map (f₁ ⁻¹' ·) = A.E.map (f₂ ⁻¹' ·) :=
    List.map_congr_left fun H hH => hHH H (List.mem_append_right _ hH)
  have hRow : ∀ i : Fin E.length, F i =
      oldResidualPart A.N O A.E ⟨i.val, by simpa only [O, List.length_map] using i.isLt⟩ := fun i =>
    (congrArg (fun M : MarkedIdeal n Y => M.ideal)
      (retained_seed_eq_original_chronological hn hW hE hdense T hT hFull i)).symm
  have hParts (i : Fin E.length) := actual_old_parts_geometry hn hRec.1 hRec.2.1 hRec.2.2.1 hRec.2.2.2.1
    (⟨i.val, by simpa only [O, List.length_map] using i.isLt⟩ : Fin O.length)
  have hcoh : ∀ i, (F i).IsCoherent := fun i => by rw [hRow i]; exact (hParts i).2.2.1
  have hnz : ∀ i, ∀ y ∈ A.N, IsNonzeroAlongAt A.N (F i) y := fun i => by rw [hRow i]; exact (hParts i).2.2.2.1
  have hPull : ∀ i, GermIdeal.pullback (m := n) f₁ (F i) = GermIdeal.pullback (m := n) f₂ (F i) := by
    intro i
    let j : Fin O.length := ⟨i.val, by simpa only [O, List.length_map] using i.isLt⟩
    have h1 := HironakaG34JointMaskEquivariance.pullback_residual hf₁ hn hRec.1 hRec.2.1 hRec.2.2.1 hRec.2.2.2.1 j
    have h2 := HironakaG34JointMaskEquivariance.pullback_residual hf₂ hn hRec.1 hRec.2.1 hRec.2.2.1 hRec.2.2.2.1 j
    have hOj : f₁ ⁻¹' O.get j = f₂ ⁻¹' O.get j := hHH (O.get j) (List.mem_append_left _ (List.get_mem O j))
    rw [hRow i]
    refine h1.trans (Eq.trans ?_ h2.symm)
    rw [hNN, hOj, hEE]
  refine ⟨fun i => ?_, ?_⟩
  · have o1 := ordinary_order_pullback_open_iso hn hRec.1 (hcoh i) (hnz i) (openPreimage T V') χ p
    have o2 := ordinary_order_pullback_open_iso hn hRec.1 (hcoh i) (hnz i) (openPreimage T V)
      (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) (openPreimage T V)) ∞) p
    exact o1.symm.trans ((congrArg₂ (fun (N : Set (openPreimage T V)) (I : GermIdeal n (CMfd.of (n := n)
      (openPreimage T V))) => ordinaryTraceOrder N I p) hNN (hPull i)).trans o2)
  · have c1 := count_pullback_open_iso F hcoh (openPreimage T V') χ p
    have c2 := count_pullback_open_iso F hcoh (openPreimage T V)
      (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) (openPreimage T V)) ∞) p
    have hFam : (fun i => GermIdeal.pullback (m := n) f₁ (F i)) = (fun i => GermIdeal.pullback (m := n) f₂ (F i)) :=
      funext hPull
    exact c1.symm.trans ((congrArg (fun G : Fin E.length → GermIdeal n (CMfd.of (n := n) (openPreimage T V)) =>
      actualDistinctProperCount G p) hFam).trans c2)

/-- **The profile window is invariant under the lift of a data-preserving biholomorphism along the prefix.** -/
theorem mem_profileWindow_iff_of_isTowerIso (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hφN : ∀ p : V, ((φ p : V') : X) ∈ W ↔ (p : X) ∈ W)
    (hφH : ∀ H ∈ E, ∀ p : V, ((φ p : V') : X) ∈ H ↔ (p : X) ∈ H)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    {χ : CMfd.of (n := n) (openPreimage T V) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T V')} (hχ : IsTowerIso φ (restrict V T) (restrict V' T) χ)
    (q : ℕ) (r : Fin E.length → ℕ) (p : openPreimage T V) :
    ((χ p : openPreimage T V') : Y) ∈ profileWindow W E T q r ↔ (p : Y) ∈ profileWindow W E T q r := by
  let S : Set Y := {x | (∀ i : Fin E.length,
    ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x ≤ r i) ∧
      actualDistinctProperCount (fun i : Fin E.length =>
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal) x < q}
  have hS : ∀ p : openPreimage T V, ((χ p : openPreimage T V') : Y) ∈ S ↔ (p : Y) ∈ S := by
    intro p
    obtain ⟨ho, hc⟩ := order_count_isTowerIso φ hn hW hE hdense hφN hφH T hT hFull hχ p
    change ((∀ i : Fin E.length, _ ≤ r i) ∧ _ < q) ↔ ((∀ i : Fin E.length, _ ≤ r i) ∧ _ < q)
    rw [hc]
    exact and_congr_left' (forall_congr' fun i => by rw [ho i])
  exact mem_interior_iff_of_homeomorph χ.toHomeomorph hS p

/-- **Appending a profile block to an equivariant prefix keeps it equivariant**: `T` equivariant for `(W, E)` (both
geometric tests) and `Q` equivariant for the current data along `T` together with the profile window (as the blocks of
`HironakaG34ProfileBlockEquivariance.exists_actual_global_original_profile_blocks_equivariant` are) give `T Q` equivariant
for `(W, E)`. -/
theorem isEquivariant_append_profile_block (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T) (hEqT : IsEquivariant W E T)
    (q : ℕ) (r : Fin E.length → ℕ) (Q : BlowupTower Y Z)
    (hEqQ : IsEquivariant (geoTransformAlong (geometricTemplate W []) T).N
      ((profileWindow W E T q r : Set Y) :: (E.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate W []) T).E))
      Q) :
    IsEquivariant W E (T.append Q) :=
  isEquivariant_append_of_window hW T hT hFull hEqT _
    (fun _ _ φ hφN hφH _ hχ p => mem_profileWindow_iff_of_isTowerIso φ hn hW hE hdense hφN hφH T hT hFull hχ q r p)
    Q hEqQ

end Window

end
end Hironaka.HironakaG34ProfileWindowNaturality
