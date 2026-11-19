import Hironaka.Resolution.HironakaG1NormalSimultaneousFields
import Hironaka.Blowup.SimultaneousNormalCrossings

/-! Differential transversality for later selected normal contact. -/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1LaterContactFieldExistence

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers NormalCrossings BlowupFlatCoordinates DerivativeIdeal DerivativeIdealAlong
  DerivativeIdealAlongCoherent HironakaG8FlatFieldCalculus HironakaG1NormalSimultaneousFields

private theorem flatCoord_mem_vanishingIdeal_of_coordinate {n : ℕ} {X : CMfd.{0} n}
    {x : X} {A : Set X} {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)}
    (T : Finset (Fin n))
    (hA : ∀ y ∈ flatDomain Φ, y ∈ A ↔
      Φ.toFun (chartAt (ComplexModel n) x y) ∈ coordSubspace T)
    {j : Fin n} (hj : j ∈ T) :
    (vanishingIdeal (n := n) A).mem x (flatCoord Φ j) := by
  have hxΦ := mem_flatDomain_self Φ
  refine ⟨holomorphicAt_flatCoord Φ j hxΦ, ?_⟩
  filter_upwards [isOpen_flatDomain Φ |>.mem_nhds hxΦ] with y hy hyA
  exact (hA y hy).mp hyA j hj

/-- If the strict contact hypersurface supplies a tangent direction for each
selected boundary coordinate independently, then a free coordinate of the
selected carrier detects the contact function. -/
theorem exists_free_flatPartial_of_boundary_differential {n : ℕ} {X : CMfd.{0} n}
    {x : X} {N D : Set X} {u : X → ℂ}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hSrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (T R : Finset (Fin n))
    (hN : ∀ y ∈ flatDomain Φ, y ∈ N ↔
      Φ.toFun (chartAt (ComplexModel n) x y) ∈ coordSubspace T)
    (hxN : x ∈ N) (hxD : x ∈ D) (hDN : D ⊆ N)
    (hu : (vanishingIdeal (n := n) D).mem x u)
    {e : ComplexChart n X} {ξ : Fin n → X → ℂ}
    (hξ : IsTangentField N e ξ x) (hDetect : fieldDeriv e ξ u x ≠ 0)
    (hRows : ∀ j ∈ R, ∃ (e' : ComplexChart n X) (η : Fin n → X → ℂ),
      IsTangentField D e' η x ∧ fieldDeriv e' η (flatCoord Φ j) x ≠ 0 ∧
      ∀ i ∈ R, i ≠ j → fieldDeriv e' η (flatCoord Φ i) x = 0) :
    ∃ j, j ∉ T ∪ R ∧ flatPartial Φ j u x ≠ 0 := by
  classical
  have hxΦ := mem_flatDomain_self Φ
  by_contra! hFree
  have hTzero {e' : ComplexChart n X} {η : Fin n → X → ℂ} (hη : IsTangentField D e' η x)
      (i : Fin n) (hi : i ∈ T) : fieldDeriv e' η (flatCoord Φ i) x = 0 := by
    have hiN := flatCoord_mem_vanishingIdeal_of_coordinate T hN hi
    have hiD : (vanishingIdeal (n := n) D).mem x (flatCoord Φ i) :=
      ⟨hiN.1, hiN.2.mono fun _ h hyD => h (hDN hyD)⟩
    exact (hη.preserves _ hiD).2.self_of_nhds hxD
  have hRzero (j : Fin n) (hj : j ∈ R) : flatPartial Φ j u x = 0 := by
    obtain ⟨e', η, hη, hηj, hηrest⟩ := hRows j hj
    have hsum := (fieldDeriv_eventuallyEq_sum_flatPartial hSrc e' η hη.mem_source hxΦ hu.1).self_of_nhds
    have hz := (hη.preserves _ hu).2.self_of_nhds hxD
    rw [hsum] at hz
    change (∑ i, fieldDeriv e' η (flatCoord Φ i) x * flatPartial Φ i u x) = 0 at hz
    rw [Finset.sum_eq_single j] at hz
    · exact (mul_eq_zero.mp hz).resolve_left hηj
    · intro i _ hij
      by_cases hiT : i ∈ T
      · rw [hTzero hη i hiT, zero_mul]
      by_cases hiR : i ∈ R
      · rw [hηrest i hiR hij, zero_mul]
      · rw [hFree i (by simp [hiT, hiR]), mul_zero]
    · simp
  apply hDetect
  rw [(fieldDeriv_eventuallyEq_sum_flatPartial hSrc e ξ hξ.mem_source hxΦ hu.1).self_of_nhds]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hiT : i ∈ T
  · rw [(hξ.preserves _ (flatCoord_mem_vanishingIdeal_of_coordinate T hN hiT)).2.self_of_nhds hxN,
      zero_mul]
  by_cases hiR : i ∈ R
  · rw [hRzero i hiR, mul_zero]
  · rw [hFree i (by simp [hiT, hiR]), mul_zero]

private noncomputable def coordinateField {n : ℕ} {X : CMfd.{0} n} {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)) (j : Fin n) :
    Fin n → X → ℂ :=
  combField Φ (fun i _ => if i = j then 1 else 0)

private theorem coordinateField_deriv {n : ℕ} {X : CMfd.{0} n} {x : X}
    {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)}
    (j : Fin n) {f : X → ℂ} :
    fieldDeriv (complexChartAt (n := n) x) (coordinateField Φ j) f x =
      flatPartial Φ j f x := by
  classical
  rw [coordinateField, fieldDeriv_combField]
  simp

private theorem coordinateField_tangent {n : ℕ} {X : CMfd.{0} n}
    {x : X} {A : Set X} {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)}
    (hSrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (T : Finset (Fin n))
    (hA : ∀ y ∈ flatDomain Φ, y ∈ A ↔
      Φ.toFun (chartAt (ComplexModel n) x y) ∈ coordSubspace T)
    {j : Fin n} (hj : j ∉ T) :
    IsTangentField A (complexChartAt (n := n) x) (coordinateField Φ j) x := by
  classical
  have hxΦ := mem_flatDomain_self Φ
  let a : Fin n → X → ℂ := fun i _ => if i = j then 1 else 0
  have ha : ∀ i, HolomorphicAt n (a i) x := fun i =>
    holomorphicAt_const (if i = j then 1 else 0)
  refine isTangentField_of_coordinate (e := complexChartAt (n := n) x) hSrc T
    (fun hy hy' => hA _ ⟨hy, hy'⟩) hxΦ hxΦ.1 (holomorphicAt_combField (Φ := Φ) hxΦ ha) ?_
  intro i hi
  refine ⟨holomorphicAt_fieldDeriv hxΦ.1 (holomorphicAt_combField hxΦ ha)
    (holomorphicAt_flatCoord Φ i hxΦ), ?_⟩
  filter_upwards [(isOpen_flatDomain Φ).mem_nhds hxΦ] with y hy _
  rw [coordinateField, fieldDeriv_combField_flatCoord hSrc _ i hy]
  simp [show i ≠ j from fun h => hj (h ▸ hi)]

/-- A change of adapted chart carries the normal differential of a given
boundary hypersurface to a nonzero scalar multiple of its new coordinate
differential. Both straightening equations refer to the very same member. -/
theorem flatPartial_boundary_coordinate_of_two_charts {n : ℕ} {X : CMfd.{0} n}
    {x : X} {A : Set X}
    (Φ Ψ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (hΨsrc : Ψ.source ⊆ (chartAt (ComplexModel n) x).target)
    (jx jz : Fin n) (hxA : x ∈ A)
    (hΦA : ∀ y ∈ flatDomain Φ, y ∈ A ↔
      Φ.toFun (chartAt (ComplexModel n) x y) ∈ coordSubspace {jx})
    (hΨA : ∀ y ∈ flatDomain Ψ, y ∈ A ↔
      Ψ.toFun (chartAt (ComplexModel n) x y) ∈ coordSubspace {jz}) :
    (∀ i, i ≠ jz → flatPartial Ψ i (flatCoord Φ jx) x = 0) ∧
      flatPartial Ψ jz (flatCoord Φ jx) x ≠ 0 := by
  classical
  have hxΦ := mem_flatDomain_self Φ
  have hxΨ := mem_flatDomain_self Ψ
  have hvan := flatCoord_mem_vanishingIdeal_of_coordinate {jx} hΦA (Finset.mem_singleton_self _)
  have hZero (i : Fin n) (hi : i ≠ jz) : flatPartial Ψ i (flatCoord Φ jx) x = 0 := by
    rw [← coordinateField_deriv]
    have htan := coordinateField_tangent hΨsrc {jz} hΨA (Finset.notMem_singleton.mpr hi)
    exact (htan.preserves _ hvan).2.self_of_nhds hxA
  refine ⟨hZero, ?_⟩
  intro h
  let e := complexChartAt (n := n) x
  let ξ := coordinateField Φ jx
  have hOne : fieldDeriv e ξ (flatCoord Φ jx) x = 1 := by
    simp [e, ξ, coordinateField, fieldDeriv_combField_flatCoord hΦsrc _ jx hxΦ]
  have hSum := (fieldDeriv_eventuallyEq_sum_flatPartial hΨsrc e ξ hxΨ.1 hxΨ hvan.1).self_of_nhds
  have hAll (i : Fin n) : flatPartial Ψ i (flatCoord Φ jx) x = 0 := by
    by_cases hi : i = jz
    · simpa [hi] using h
    · exact hZero i hi
  simp [hAll, hOne] at hSum

/-- Two separately adapted charts suffice for normalized contact on the actual
intersection of the carrier with the selected members. The second chart only
uses the genuine differential transversality of the strict section to those
same members. -/
theorem exists_normalized_tangent_field_of_two_boundary_charts
    {n : ℕ} {X : CMfd.{0} n} {x : X} {N D : Set X} {u : X → ℂ}
    (E : List (Set X)) (I : Finset (Fin E.length))
    (Φ Ψ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (hΨsrc : Ψ.source ⊆ (chartAt (ComplexModel n) x).target)
    (T U : Finset (Fin n)) (s t : Fin E.length → Fin n)
    (hN : ∀ y ∈ flatDomain Φ, y ∈ N ↔
      Φ.toFun (chartAt (ComplexModel n) x y) ∈ coordSubspace T)
    (hD : ∀ y ∈ flatDomain Ψ, y ∈ D ↔
      Ψ.toFun (chartAt (ComplexModel n) x y) ∈ coordSubspace U)
    (hΦE : ∀ i ∈ I, ∀ y ∈ flatDomain Φ, y ∈ E.get i ↔
      Φ.toFun (chartAt (ComplexModel n) x y) ∈ coordSubspace {s i})
    (hΨE : ∀ i ∈ I, ∀ y ∈ flatDomain Ψ, y ∈ E.get i ↔
      Ψ.toFun (chartAt (ComplexModel n) x y) ∈ coordSubspace {t i})
    (hI : ∀ i ∈ I, x ∈ E.get i) (ht : ∀ i ∈ I, t i ∉ U) (hInj : Set.InjOn t ↑I)
    (hxD : x ∈ D) (hDN : D ⊆ N) (hu : (vanishingIdeal (n := n) D).mem x u)
    {e : ComplexChart n X} {ξ : Fin n → X → ℂ}
    (hξ : IsTangentField N e ξ x) (hDetect : fieldDeriv e ξ u x ≠ 0) :
    ∀ᶠ y in 𝓝 x, ∃ (e' : ComplexChart n X) (η : Fin n → X → ℂ),
      IsTangentField (N ∩ BoundaryCount.memberInter E I) e' η y ∧
      fieldDeriv e' η u =ᶠ[𝓝 y] fun _ => 1 := by
  classical
  let R := I.image s
  have hRows (j : Fin n) (hj : j ∈ R) :
      ∃ (e' : ComplexChart n X) (η : Fin n → X → ℂ),
        IsTangentField D e' η x ∧ fieldDeriv e' η (flatCoord Φ j) x ≠ 0 ∧
        ∀ l ∈ R, l ≠ j → fieldDeriv e' η (flatCoord Φ l) x = 0 := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    refine ⟨complexChartAt x, coordinateField Ψ (t i),
      coordinateField_tangent hΨsrc U hD (ht i hi), ?_, ?_⟩
    · rw [coordinateField_deriv]
      exact (flatPartial_boundary_coordinate_of_two_charts Φ Ψ hΦsrc hΨsrc
        (s i) (t i) (hI i hi) (hΦE i hi) (hΨE i hi)).2
    · intro l hl hli
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hl
      rw [coordinateField_deriv]
      apply (flatPartial_boundary_coordinate_of_two_charts Φ Ψ hΦsrc hΨsrc
        (s b) (t b) (hI b hb) (hΦE b hb) (hΨE b hb)).1
      intro heq
      exact hli (congrArg s (hInj hi hb heq).symm)
  obtain ⟨r, hr, hDeriv⟩ := exists_free_flatPartial_of_boundary_differential Φ hΦsrc T R
    hN (hDN hxD) hxD hDN hu hξ hDetect hRows
  have hxΦ := mem_flatDomain_self Φ
  have hNonzero := (holomorphicAt_flatPartial r hxΦ hu.1).continuousAt.eventually
    (isOpen_ne.mem_nhds hDeriv)
  filter_upwards [(isOpen_flatDomain Φ).mem_nhds hxΦ, hu.1.eventually_nhds, hNonzero]
    with p hp hpU hpNonzero
  refine exists_normalized_tangent_field_of_flatPartial Φ hΦsrc hp
    (T ∪ R) ?_ r hr hpU hpNonzero
  intro y hy hy'
  have hyΦ : y ∈ flatDomain Φ := ⟨hy, hy'⟩
  change (y ∈ N ∧ ∀ i ∈ I, y ∈ E.get i) ↔ _
  rw [hN y hyΦ]
  constructor
  · rintro ⟨hTy, hRy⟩ l hl
    rcases Finset.mem_union.mp hl with hl | hl
    · exact hTy l hl
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hl
      exact (hΦE i hi y hyΦ).mp (hRy i hi) _ (Finset.mem_singleton_self _)
  · intro h
    refine ⟨fun l hl => h l (Finset.mem_union_left _ hl), fun i hi => (hΦE i hi y hyΦ).mpr ?_⟩
    intro l hl
    rw [Finset.mem_singleton.mp hl]
    exact h _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩))

/-- Transversality of both carriers to the same SNC boundary suffices.
The selected indices may comprise any subset of the members through the
point. The contact function is required to vanish along the strict section
as a holomorphic germ and to have a nonzero carrier derivative. -/
theorem exists_normalized_tangent_field_of_transverse_boundary
    {n : ℕ} (hn : 0 < n) {X : CMfd.{0} n} {x : X} {N D : Set X} {u : X → ℂ}
    (E : List (Set X)) (I : Finset (Fin E.length))
    (hE : IsSNCDivisor n E) (hTN : IsTransverse n N E) (hTD : IsTransverse n D E)
    (hI : ∀ i ∈ I, x ∈ E.get i) (hxD : x ∈ D) (hDN : D ⊆ N)
    (hu : (vanishingIdeal (n := n) D).mem x u)
    {e : ComplexChart n X} {ξ : Fin n → X → ℂ}
    (hξ : IsTangentField N e ξ x) (hDetect : fieldDeriv e ξ u x ≠ 0) :
    ∀ᶠ y in 𝓝 x, ∃ (e' : ComplexChart n X) (η : Fin n → X → ℂ),
      IsTangentField (N ∩ BoundaryCount.memberInter E I) e' η y ∧
      fieldDeriv e' η u =ᶠ[𝓝 y] fun _ => 1 := by
  classical
  obtain ⟨TN, SN, ⟨Φ, hΦsrc, _, hΦ⟩, hSN⟩ := hTN x (hDN hxD)
  obtain ⟨TD, SD, ⟨Ψ, hΨsrc, _, hΨ⟩, hSD⟩ := hTD x hxD
  let pick (A : Finset (Fin n)) : Fin n := if h : A.Nonempty then A.min' h else ⟨0, hn⟩
  have hPick (A : Finset (Fin n)) (hA : A.card = 1) : A = {pick A} := by
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hA
    simp [pick]
  let s := pick ∘ SN
  let t := pick ∘ SD
  have hΦE (i) (hi : i ∈ I) (y) (hy : y ∈ flatDomain Φ) :
      y ∈ E.get i ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ coordSubspace {s i} := by
    have h := hΦ (some i) (hI i hi) hy.1 hy.2
    exact (hPick _ (hSN i (hI i hi)).1) ▸ h
  have hΨE (i) (hi : i ∈ I) (y) (hy : y ∈ flatDomain Ψ) :
      y ∈ E.get i ↔ Ψ.toFun (chartAt (ComplexModel n) x y) ∈ coordSubspace {t i} := by
    have h := hΨ (some i) (hI i hi) hy.1 hy.2
    exact (hPick _ (hSD i (hI i hi)).1) ▸ h
  have ht (i) (hi : i ∈ I) : t i ∉ TD := by
    have h := (hSD i (hI i hi)).2
    rw [hPick _ (hSD i (hI i hi)).1] at h
    exact Finset.disjoint_singleton_left.mp h
  have hInj : Set.InjOn t ↑I := by
    intro i hi j hj hij
    apply SimultaneousNormalCrossings.eq_of_eventually_mem_iff hE (hI i hi) (hI j hj)
    filter_upwards [(isOpen_flatDomain Ψ).mem_nhds (mem_flatDomain_self Ψ)] with y hy
    rw [hΨE i hi y hy, hΨE j hj y hy, hij]
  exact exists_normalized_tangent_field_of_two_boundary_charts E I Φ Ψ hΦsrc hΨsrc
    TN TD s t (fun _ hy => hΦ none (hDN hxD) hy.1 hy.2)
    (fun _ hy => hΨ none hxD hy.1 hy.2) hΦE hΨE hI ht hInj hxD hDN hu hξ hDetect

open BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec
  StepOneValue TangentDirectionAlong InvDomainMemberRestriction HironakaG8HomStable
  HironakaG1ProperCarrierNormalContact HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1ProperCarrierNormalLocalClass HironakaG1RecursiveMemberValueTransport
  HironakaG1LaterSelectedNormalTangent HironakaActualSectionBoundaryGeometry
  HironakaActualOpenZeroSectionDifferentials HironakaActualRelativeNormalGeometry
  RelativePrincipalizationSpan
open HomogenizedGlueingTower (strictAlong N_geoTransformAlong)

/-- An actual tested upper stage has normalized contact near each point of its
strict section, tangent to the literal intersection with the old members
selected at that point. Both transverse carriers come from tested records. -/
theorem exists_later_positive_selected_normal_contact {n k : ℕ}
    {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (H : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hH : IsGeoTestTower (properNormalMarked Q) H) {x : Y}
    (hx : x ∈ strictAlong H ((properNormalMarked Q).N ∩ {z | relativeNormalCoordinate U z = 0})) :
    let P := properNormalMarked Q
    let D := strictAlong H (P.N ∩ {z | relativeNormalCoordinate U z = 0})
    ∃ (V : Opens Y) (u : Y → ℂ), x ∈ V ∧
      IsTangentDirectionAlong (positiveMemberOn P H x V).N
        (positiveMemberOn P H x V).ideal (positiveMemberOn P H x V).d univ
        (u ∘ (Subtype.val : V → Y)) ∧
      (positiveMemberOn P H x V).N ∩ {z : V | u z.val = 0} =
        (positiveMemberOn P H x V).N ∩ (Subtype.val : V → Y) ⁻¹' D := by
  intro P D
  let B := geoTransformAlong (barMarked P) H
  let X := CMfd.of (n := n + 1) (productOpen U)
  let S := geoTransformAlong (sectionMarked Q) H
  let I := membersThrough B.E (origMembers P H) x
  have hP := properNormalMarked_isInvDomain Q hQ
  have hBar := HironakaCoherentTransformExtension.isInvDomain_barMarked (X := X) P hP
  have hBT := ((bar_local_any_boundary (X := X) P hP).wEquiv.2 H).1.mp hH
  have hB := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hBar.isWellFormed H hBT
  have hS0 : IsInvDomain k (sectionMarked Q) := section_projected_domain k Q.N Q.E Q.ideal Q.d hQ
  have hST := ((properNormalMarked_locWPEquiv_section Q hQ).wEquiv.2 H).1.mp hH
  have hS := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hS0.isWellFormed H hST
  have hSE : S.E = B.E :=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
      (𝔪 := sectionMarked Q) (𝔫 := barMarked P) rfl H
  have hSD : S.N = D := by
    rw [N_geoTransformAlong]
    exact congrArg (strictAlong H) (normal_contact_carrier Q).symm
  have hDN : D ⊆ B.N := by
    change D ⊆ (geoTransformAlong (barMarked P) H).N
    rw [N_geoTransformAlong]
    exact MemberInterTowerAlong.strictAlong_mono H (fun _ hy => hy.1)
  obtain ⟨V, u, hxV, hu, hZero⟩ := later_normal_bar_contact Q hQ H hH (hDN hx)
  have hxU : u x = 0 := ((Set.ext_iff.mp hZero x).mpr ⟨hx, hxV⟩).1.2
  obtain ⟨e, ξ, hξ, hDetect⟩ := hu.multiplicity_one x hxV hxU
  have hUvan : (vanishingIdeal (n := n + 1) D).mem x u := by
    refine ⟨GiraudAlong.holomorphicAt_of_mem_iterDerivIdealAlong
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hB.isCoherent hg)
      (B.d - 1) x u (hu.mem x hxV), ?_⟩
    filter_upwards [V.isOpen.mem_nhds hxV] with y hy hyD
    exact ((Set.ext_iff.mp hZero y).mpr ⟨hyD, hy⟩).1.2
  have hTransD : IsTransverse (n + 1) D B.E := hSD ▸ hSE ▸ hS.isTransverse
  have hFields := exists_normalized_tangent_field_of_transverse_boundary (Nat.succ_pos n)
    B.E I hB.isSNCDivisor hB.isTransverse hTransD (fun i hi => (mem_membersThrough.mp hi).2)
    hx hDN hUvan hξ hDetect
  obtain ⟨W, hW, hWo, hxW⟩ := mem_nhds_iff.mp (hFields.and (V.isOpen.mem_nhds hxV))
  let O : Opens Y := ⟨W, hWo⟩
  refine ⟨O, u, hxW, later_positive_member_normal_contact_on_chart Q hQ H hH x O u ?_ ?_ ?_⟩
  · exact ⟨O.isOpen, fun y hy => hu.mem y (hW hy).2,
      fun y hy => hu.multiplicity_one y (hW hy).2⟩
  · ext y
    constructor
    · rintro ⟨hy, hyO⟩
      exact ⟨(Set.ext_iff.mp hZero y).mp ⟨hy, (hW hyO).2⟩ |>.1, hyO⟩
    · rintro ⟨hy, hyO⟩
      exact ⟨(Set.ext_iff.mp hZero y).mpr ⟨hy, (hW hyO).2⟩ |>.1, hyO⟩
  · exact fun y hy => (hW hy).1

end Hironaka.HironakaG1LaterContactFieldExistence
