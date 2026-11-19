import Hironaka.Resolution.HironakaG1ActualCommonGraphNativeComparison
import Hironaka.Resolution.HironakaG1NativeBoundaryTrace
import Hironaka.Resolution.HironakaOriginalBoundaryEmptyFilterComparison

/-! Original canonicality and maxima on successful native common-graph overlaps. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1NativeGraphOverlapRead

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism ResolutionInvariantSpec
  CanonicalCentres ResolutionDriver DivisorExponentAlong MarkedIdealRestrictOpen
  BlowupTowerIsomorphism HironakaG8LocalTransport RelativePrincipalizationSpan
  Hironaka.HolomorphicIdealSheaves
  HironakaG11PresLineState HironakaG11InvBMClass HironakaG8LocalHistory
  HironakaG1NativeBoundaryTrace HironakaG1OriginalUnequalMarkCanonical
  HironakaG8GuardedCanonicality HironakaOriginalBoundaryEmptyFilterComparison

private theorem nativeHSState_nonemptyBoundary {n : ℕ} {X : CMfd.{0} n}
    {P : MarkedIdeal n X} {D : Set X} {h : ℕ → ℕ} (hP : NativeHSState P D h) :
    NativeHSState (nonemptyBoundary P) D h := by
  exact hP

/-- On a common graph refinement, the independent ordered boundaries may
have different empty slots. The lists of surviving slots must agree, and
only the surviving incident traces need satisfy the native cut criterion.
The original records and marks appear in the conclusion. -/
theorem native_graph_overlap_canonical_and_max {n : ℕ} (hn : 0 < n)
    {X : CMfd.{0} n} {P Q : MarkedIdeal n X} {D : Set X} {h : ℕ → ℕ}
    (hP : NativeHSState P D h) (hQ : NativeHSState Q D h)
    (hPD : IsInvDomain n P) (hQD : IsInvDomain n Q)
    (U : Opens X) :
    let A := CMfd.of (n := n) U
    let L := MarkedIdeal.pullback (M' := A) (Subtype.val : U → X) P
    let R := MarkedIdeal.pullback (M' := A) (Subtype.val : U → X) Q
    let F := nonemptyBoundary L
    let G := nonemptyBoundary R
    G.E = F.E →
    (∀ (i : Fin F.E.length) (x : A), x ∈ F.cosupp → x ∈ F.E.get i →
      (∀ᶠ y in 𝓝 x, y ∈ F.E.get i → y ∈ (Subtype.val : U → X) ⁻¹' D) →
      ∀ᶠ y in 𝓝 x, y ∈ F.E.get i → y ∈ F.cosupp) →
    ∀ {Y : CMfd.{0} n} (T : BlowupTower A Y),
      (IsCanonical L ((canonicalInvariant n).inv L) T ↔
        IsCanonical R ((canonicalInvariant n).inv R) T) ∧
      (IsCanonical L ((canonicalInvariant n).inv L) T →
        (geoTransformAlong L T).cosupp = (geoTransformAlong R T).cosupp ∧
        maxLocus ((canonicalInvariant n).inv L T) (geoTransformAlong L T).cosupp =
          maxLocus ((canonicalInvariant n).inv R T) (geoTransformAlong R T).cosupp) := by
  intro A L R F G hE hTrace Y T
  have hLD : IsInvDomain n L := InvDomainTowerAlong.isInvDomain_pullback_val U hPD
  have hRD : IsInvDomain n R := InvDomainTowerAlong.isInvDomain_pullback_val U hQD
  have hFD := isInvDomain_nonemptyBoundary L hLD
  have hGD := isInvDomain_nonemptyBoundary R hRD
  have hFS := nativeHSState_nonemptyBoundary (hP.restrict U)
  have hGS := nativeHSState_nonemptyBoundary (hQ.restrict U)
  have hClass : LocWPEquiv (X := A) F G := HironakaG11PresLineStable.locWPEquiv_native hFS hGS hE
  have hN : SameCarrierDim F G := SameCarrierDim.of_N_eq (hFS.2.2.1.trans hGS.2.2.1.symm)
  have hExp := normalized_native_boundary_exponents_of_trace hn hFS hGS hFD hGD hE hTrace
  have hCan := canonicalInvariant_isCanonical_iff_of_local F G hFD hGD hClass hN hExp T
  have hL := isCanonical_nonemptyBoundary_iff L T
  have hR := isCanonical_nonemptyBoundary_iff R T
  refine ⟨hL.symm.trans (hCan.trans hR), fun hLC => ?_⟩
  have hFC := hL.mpr hLC
  have hGC := hCan.mp hFC
  have hFT := (canonicalInvariant n).isInvValue.isGeoTestTower_of_isCanonical hFD T hFC
  have hCos := (hClass.wEquiv.2 T).2 hFT
  have hMax := maxLocus_eq_of_guarded_pairCuts (fun {_} _ => True) (canonicalInvariant n).inv
    (canonicalTwoPairCuts_canonicalInvariant n) F G hFD hGD trivial trivial hClass hN hExp T hFT hFC hGC
  rw [cosupp_nonemptyBoundary_along L T, cosupp_nonemptyBoundary_along R T] at hCos hMax
  rw [maxLocus_nonemptyBoundary L T, maxLocus_nonemptyBoundary R T] at hMax
  exact ⟨hCos, hMax⟩

/-- A trace condition on the good locus descends to any refinement, even
when restricting deletes some of that chart's ordered boundary slots. -/
theorem native_graph_trace_on_refinement {n : ℕ} {X : CMfd.{0} n}
    (P : MarkedIdeal n X) (hP : P.ideal.IsCoherent) (D : Set X) (U : Opens X)
    (hGood : ∀ F ∈ P.E, ∀ x ∈ P.cosupp, x ∈ U → x ∈ F →
      (∀ᶠ y in 𝓝 x, y ∈ F → y ∈ D) →
      ∀ᶠ y in 𝓝 x, y ∈ F → y ∈ P.cosupp) :
    let F := nonemptyBoundary (MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → X) P)
    ∀ (i : Fin F.E.length) (x : U), x ∈ F.cosupp → x ∈ F.E.get i →
      (∀ᶠ y in 𝓝 x, y ∈ F.E.get i → y ∈ (Subtype.val : U → X) ⁻¹' D) →
      ∀ᶠ y in 𝓝 x, y ∈ F.E.get i → y ∈ F.cosupp := by
  intro F i x hx hxF hContained
  have hMem := List.get_mem F.E i
  change F.E.get i ∈ ((P.E.map ((Subtype.val : U → X) ⁻¹' ·)).filter _) at hMem
  obtain ⟨G, hG, hSlot⟩ := List.mem_map.mp (List.mem_of_mem_filter hMem)
  have hCos : F.cosupp = (Subtype.val : U → X) ⁻¹' P.cosupp :=
    cosupp_pullback_val P (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hP hg) U
  have hMap := U.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq x
  rw [← hSlot] at hxF hContained ⊢
  have hC : ∀ᶠ y in 𝓝 x.val, y ∈ G → y ∈ D := by
    rw [← hMap]
    exact hContained
  have hxP : x.val ∈ P.cosupp := by rw [hCos] at hx; exact hx
  have h := hGood G hG x.val hxP x.property hxF hC
  rw [← hMap] at h
  rw [hCos]
  exact h

private theorem canonical_chart_pullback_iff {n : ℕ} {X Y A B : CMfd.{0} n}
    (P : MarkedIdeal n X) (hP : IsInvDomain n P)
    (e : A ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    (χ : B ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y)
    (T : BlowupTower X Y) (S : BlowupTower A B) (hi : IsTowerIso e S T χ) :
    let P' := MarkedIdeal.pullback e P
    IsCanonical P ((canonicalInvariant n).inv P) T ↔
      IsCanonical P' ((canonicalInvariant n).inv P') S := by
  intro P'
  let R := canonicalInvariant n
  have hD : IsInvDomain n P' := InvDomainTowerAlong.isInvDomain_pullback e hP
  refine ⟨Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso R hP e hi, fun h => ?_⟩
  have hBack : MarkedIdeal.pullback e.symm P' = P :=
    pullback_symm_pullback e hP.isWellFormed.isCoherent
  have hc := Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso R hD e.symm hi.symm h
  rwa [hBack] at hc

set_option maxHeartbeats 1100000 in
/-- Descend the actual common-graph calculation to two independent chart
refinements of the same history. The source records retain their independent
ordered boundary lists. Maximum loci match via the actual endpoint map. -/
theorem native_graph_overlap_descend_to_charts {n : ℕ} (hn : 0 < n)
    {X : CMfd.{0} n} {P Q : MarkedIdeal n X} {D : Set X} {h : ℕ → ℕ}
    (hP : NativeHSState P D h) (hQ : NativeHSState Q D h)
    (hPD : IsInvDomain n P) (hQD : IsInvDomain n Q)
    (U : Opens X)
    (hE : (nonemptyBoundary (MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → X) Q)).E =
      (nonemptyBoundary (MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → X) P)).E)
    (hGood : ∀ F ∈ P.E, ∀ x ∈ P.cosupp, x ∈ U → x ∈ F →
      (∀ᶠ y in 𝓝 x, y ∈ F → y ∈ D) →
      ∀ᶠ y in 𝓝 x, y ∈ F → y ∈ P.cosupp)
    {Y A₁ A₂ Y₁ Y₂ : CMfd.{0} n} (T : BlowupTower (CMfd.of (n := n) U) Y)
    (T₁ : BlowupTower A₁ Y₁) (T₂ : BlowupTower A₂ Y₂)
    (e₁ : A₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ U)
    (e₂ : A₂ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ U)
    (χ₁ : Y₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y)
    (χ₂ : Y₂ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y)
    (hi₁ : IsTowerIso e₁ T₁ T χ₁) (hi₂ : IsTowerIso e₂ T₂ T χ₂) :
    let P₁ := MarkedIdeal.pullback e₁ (MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → X) P)
    let Q₂ := MarkedIdeal.pullback e₂ (MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → X) Q)
    let f : Y₁ → Y₂ := χ₂.symm ∘ χ₁
    (IsCanonical P₁ ((canonicalInvariant n).inv P₁) T₁ ↔
      IsCanonical Q₂ ((canonicalInvariant n).inv Q₂) T₂) ∧
    (IsCanonical P₁ ((canonicalInvariant n).inv P₁) T₁ →
      (geoTransformAlong P₁ T₁).cosupp = f ⁻¹' (geoTransformAlong Q₂ T₂).cosupp ∧
      maxLocus ((canonicalInvariant n).inv P₁ T₁) (geoTransformAlong P₁ T₁).cosupp =
        f ⁻¹' maxLocus ((canonicalInvariant n).inv Q₂ T₂) (geoTransformAlong Q₂ T₂).cosupp) := by
  intro P₁ Q₂ f
  let L := MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → X) P
  let R := MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → X) Q
  have hLD := InvDomainTowerAlong.isInvDomain_pullback_val U hPD
  have hRD := InvDomainTowerAlong.isInvDomain_pullback_val U hQD
  have h₁ := canonical_chart_pullback_iff L hLD e₁ χ₁ T T₁ hi₁
  have h₂ := canonical_chart_pullback_iff R hRD e₂ χ₂ T T₂ hi₂
  have hO := native_graph_overlap_canonical_and_max hn hP hQ hPD hQD U hE
    (native_graph_trace_on_refinement P hPD.isWellFormed.isCoherent D U hGood) T
  refine ⟨h₁.symm.trans (hO.1.trans h₂), fun h => ?_⟩
  have hLC := h₁.mpr h
  have hRC := hO.1.mp hLC
  obtain ⟨hCos, hMax⟩ := hO.2 hLC
  let I := canonicalInvariant n
  have hLT := I.isInvValue.isGeoTestTower_of_isCanonical hLD T hLC
  have hRT := I.isInvValue.isGeoTestTower_of_isCanonical hRD T hRC
  have hC₁ := IsTowerIso.cosupp_geoTransformAlong e₁ hLD.isWellFormed.isClosedSubmanifold_N
    hLD.isWellFormed.isCoherent hi₁ hLT
  have hC₂ := IsTowerIso.cosupp_geoTransformAlong e₂ hRD.isWellFormed.isClosedSubmanifold_N
    hRD.isWellFormed.isCoherent hi₂ hRT
  have hM₁ := Seq.MaxLocusLocal.maxLocus_isTowerIso I hLD e₁ hi₁ hLC
  have hM₂ := Seq.MaxLocusLocal.maxLocus_isTowerIso I hRD e₂ hi₂ hRC
  constructor
  · rw [hC₁, hC₂, hCos]
    ext z
    simp [f]
  · rw [hM₁, hM₂, hMax]
    ext z
    simp [f, I]

private theorem eventually_members_missing_anchor {X : Type*} [TopologicalSpace X]
    (E : List (Set X)) (x : X) (hE : ∀ F ∈ E, IsClosed F) :
    ∀ᶠ y in 𝓝 x, ∀ F ∈ E, x ∉ F → y ∉ F := by
  induction E with
  | nil => simp
  | cons F E ih =>
    have hTail := ih (fun G hG => hE G (List.mem_cons_of_mem _ hG))
    have hHead : ∀ᶠ y in 𝓝 x, x ∉ F → y ∉ F := by
      by_cases hx : x ∈ F
      · exact Eventually.of_forall fun _ h => (h hx).elim
      · have hc : ∀ᶠ y in 𝓝 x, y ∉ F := (hE F List.mem_cons_self).isOpen_compl.mem_nhds hx
        exact hc.mono fun _ hy _ => hy
    filter_upwards [hHead, hTail] with y hyF hyE G hG hx
    rcases List.mem_cons.mp hG with rfl | hG
    · exact hyF hx
    · exact hyE G hG hx

private theorem restrict_ordered_germ_matches {X : Type*} [TopologicalSpace X]
    {E E' : List (Set X)} {x : X}
    (h : List.Forall₂ (fun F G : Set X => ∀ᶠ y in 𝓝 x, y ∈ F ↔ y ∈ G) E E') :
    ∀ᶠ y in 𝓝 x, List.Forall₂ (fun F G : Set X => y ∈ F ↔ y ∈ G) E E' := by
  induction h with
  | nil => exact Eventually.of_forall fun _ => .nil
  | cons hFG _ ih => exact (hFG.and ih).mono fun _ h => .cons h.1 h.2

private theorem map_preimage_eq_of_pointwise_matches {X : Type*}
    {E E' : List (Set X)} {U : Set X}
    (h : ∀ y ∈ U, List.Forall₂ (fun F G : Set X => y ∈ F ↔ y ∈ G) E E')
    (hSome : ∃ y, y ∈ U) :
    E.map ((Subtype.val : U → X) ⁻¹' ·) = E'.map ((Subtype.val : U → X) ⁻¹' ·) := by
  obtain ⟨y0, hy0⟩ := hSome
  have aux {A B : List (Set X)}
      (h₀ : List.Forall₂ (fun F G : Set X => y0 ∈ F ↔ y0 ∈ G) A B) :
      (∀ y ∈ U, List.Forall₂ (fun F G : Set X => y ∈ F ↔ y ∈ G) A B) →
      A.map ((Subtype.val : U → X) ⁻¹' ·) = B.map ((Subtype.val : U → X) ⁻¹' ·) := by
    induction h₀ with
    | nil => intro _; rfl
    | @cons F A G B _ _ ih =>
      intro h'
      simp only [List.map_cons, List.cons.injEq]
      refine ⟨Set.ext (fun z => ?_), ih ?_⟩
      · have hZ := h' z.val z.property
        cases hZ with
        | cons hFG _ => exact hFG
      · intro y hy
        have hZ := h' y hy
        cases hZ with
        | cons _ hTail => exact hTail
  exact aux (h y0 hy0) h

/-- Matching the ordered germs of the incident slots suffices to find an
actual common refinement with identical nonempty ordered boundaries. All
other slots become empty on the chosen neighborhood. -/
theorem exists_refinement_of_ordered_incident_germs {n : ℕ} {X : CMfd.{0} n}
    (P Q : MarkedIdeal n X) (hP : P.IsWellFormed) (hQ : Q.IsWellFormed)
    (V : Opens X) (x : X) (hx : x ∈ V)
    (hMatch : List.Forall₂ (fun F G : Set X => ∀ᶠ y in 𝓝 x, y ∈ F ↔ y ∈ G)
      (P.E.filter (fun F => decide (x ∈ F))) (Q.E.filter (fun F => decide (x ∈ F)))) :
    ∃ U : Opens X, x ∈ U ∧ U ≤ V ∧
      (nonemptyBoundary (MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → X) P)).E =
      (nonemptyBoundary (MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → X) Q)).E := by
  have hV : ∀ᶠ y in 𝓝 x, y ∈ V := V.isOpen.mem_nhds hx
  have hL := eventually_members_missing_anchor P.E x hP.isSNCDivisor.1
  have hR := eventually_members_missing_anchor Q.E x hQ.isSNCDivisor.1
  obtain ⟨W, hW, hWo, hxW⟩ := mem_nhds_iff.mp
    (hV.and (hL.and (hR.and (restrict_ordered_germ_matches hMatch))))
  let U : Opens X := ⟨W, hWo⟩
  have hFilter (E : List (Set X)) (hAvoid : ∀ y ∈ U, ∀ F ∈ E, x ∉ F → y ∉ F) :
      (E.map ((Subtype.val : U → X) ⁻¹' ·)).filter (fun F => decide F.Nonempty) =
      (E.filter (fun F => decide (x ∈ F))).map ((Subtype.val : U → X) ⁻¹' ·) := by
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro F hF
    apply decide_eq_decide.mpr
    exact ⟨fun ⟨z, hz⟩ => by
      by_contra h
      exact hAvoid z.val z.property F hF h hz,
      fun hxF => ⟨⟨x, hxW⟩, hxF⟩⟩
  refine ⟨U, hxW, fun y hy => (hW hy).1, ?_⟩
  change (P.E.map ((Subtype.val : U → X) ⁻¹' ·)).filter _ =
    (Q.E.map ((Subtype.val : U → X) ⁻¹' ·)).filter _
  rw [hFilter P.E (fun _ hy => (hW hy).2.1), hFilter Q.E (fun _ hy => (hW hy).2.2.1)]
  exact map_preimage_eq_of_pointwise_matches (fun _ hy => (hW hy).2.2.2) ⟨x, hxW⟩

/-- Two genuine graph records with the same ordered incident germs admit a
common neighborhood carrying the same original canonical histories and
maximum loci. The trace premise is tested before shrinking, on the
prescribed good locus. -/
theorem exists_native_graph_refinement_canonical_and_max {n : ℕ} (hn : 0 < n)
    {X : CMfd.{0} n} {P Q : MarkedIdeal n X} {D : Set X} {h : ℕ → ℕ}
    (hP : NativeHSState P D h) (hQ : NativeHSState Q D h)
    (hPD : IsInvDomain n P) (hQD : IsInvDomain n Q)
    (V : Opens X) (x : X) (hx : x ∈ V)
    (hMatch : List.Forall₂ (fun F G : Set X => ∀ᶠ y in 𝓝 x, y ∈ F ↔ y ∈ G)
      (P.E.filter (fun F => decide (x ∈ F))) (Q.E.filter (fun F => decide (x ∈ F))))
    (hGood : ∀ F ∈ P.E, ∀ x ∈ P.cosupp, x ∈ V → x ∈ F →
      (∀ᶠ y in 𝓝 x, y ∈ F → y ∈ D) →
      ∀ᶠ y in 𝓝 x, y ∈ F → y ∈ P.cosupp) :
    ∃ U : Opens X, x ∈ U ∧ U ≤ V ∧
      let A := CMfd.of (n := n) U
      let L := MarkedIdeal.pullback (M' := A) (Subtype.val : U → X) P
      let R := MarkedIdeal.pullback (M' := A) (Subtype.val : U → X) Q
      ∀ {Y : CMfd.{0} n} (T : BlowupTower A Y),
        (IsCanonical L ((canonicalInvariant n).inv L) T ↔
          IsCanonical R ((canonicalInvariant n).inv R) T) ∧
        (IsCanonical L ((canonicalInvariant n).inv L) T →
          (geoTransformAlong L T).cosupp = (geoTransformAlong R T).cosupp ∧
          maxLocus ((canonicalInvariant n).inv L T) (geoTransformAlong L T).cosupp =
            maxLocus ((canonicalInvariant n).inv R T) (geoTransformAlong R T).cosupp) := by
  obtain ⟨U, hxU, hUV, hE⟩ := exists_refinement_of_ordered_incident_germs
    P Q hPD.isWellFormed hQD.isWellFormed V x hx hMatch
  refine ⟨U, hxU, hUV, native_graph_overlap_canonical_and_max hn hP hQ hPD hQD U hE.symm ?_⟩
  exact native_graph_trace_on_refinement P hPD.isWellFormed.isCoherent D U
    (fun F hF y hy hyU => hGood F hF y hy (hUV hyU))

end Hironaka.HironakaG1NativeGraphOverlapRead
