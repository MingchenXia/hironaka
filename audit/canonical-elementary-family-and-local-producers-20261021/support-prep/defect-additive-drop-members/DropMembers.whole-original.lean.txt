import TranscendentalNakamaye.Pending.NormalCrossingsComparison
import TranscendentalNakamaye.Pending.CoefficientIdealRestriction
import TranscendentalNakamaye.Pending.TransformOffCentre

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Dropping members of `E` along multiple test blow-ups

Blueprint `hir:drop-members`, `hir:drop-containing-members` (`blueprint/src/hironaka.tex`, Hironaka phase H4, Step 1a
of Proposition `hir:maximal-order-step`).  Sources: Włodarczyk 2005, Step 1a (passing from `E` to `E_S`, the members not
containing `S`) and Step 1b (the members of the original `E` are dropped once they miss the cosupport); Bierstone--Milman
2008, §6.

Only the divisor of a transform depends on `E`; admissibility compares through TN3's normal-crossings comparison
(`NormalCrossingsComparison`).

* `geoTransformAlong_withE`: along any tower, `(M, N, E', 𝔞, d)` and `(M, N, E, 𝔞, d)` have transforms with the same
  submanifold, ideal and mark (hence cosupport).
* **Deleting the members that contain every centre** (`isGeoTestTower_withE_iff_of_centresIn`): if every member of `E`
  missing from `E'` contains `S`, then along towers with centres in the strict transforms of `S` the test towers of the
  two marked ideals coincide (`E` simple normal crossings, the marked ideal well formed), and the dropped members keep
  containing the strict transforms of `S`.
* **Deleting members away from the cosupport** (`isGeoTestTower_withE_iff_of_disjoint`): if every member of `E` missing
  from `E'` is disjoint from the cosupport, the test towers coincide; `hasNormalCrossings_of_forall_disjoint` is the
  normal-crossings half (members missing the centre do not matter).

Import discipline (Hironaka phase): this module does not import, even transitively,
`Pending.RelativePrincipalization` or `Pending.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter
open scoped Topology Manifold

universe u

namespace TranscendentalNakamaye.Pending.DropMembers

open FirstPass FirstPass.BlowupSequences NormalCrossings BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupStrictSubmanifold NormalCrossingsComparison CoefficientIdealRestriction HomogenizedGlueingTower

noncomputable section

/-! ### Normal crossings and members missing the centre -/

section NC

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]

/-- **Members missing the centre do not matter for normal crossings**: if `C` has only normal crossings with `E'`, every
member of `E'` is a member of `E` and every member of `E` missing from `E'` is disjoint from `C`, then `C` has only
normal crossings with `E`. -/
theorem hasNormalCrossings_of_forall_disjoint {C : Set X} {E E' : List (Set X)}
    (h : HasNormalCrossings n C E') (hdis : ∀ H ∈ E, H ∉ E' → Disjoint C H) :
    HasNormalCrossings n C E := by
  classical
  intro x hx
  obtain ⟨S₀, S, ⟨Φ, hΦt, hΦ0, hΦA⟩, hS⟩ := h x hx
  -- a member of `E` through `x` is a member of `E'`
  have hmem : ∀ i : Fin E.length, x ∈ E.get i → E.get i ∈ E' := fun i hxi => by
    by_contra hnot
    exact Set.disjoint_left.mp (hdis _ (List.get_mem _ _) hnot) hx hxi
  set idx : Fin E.length → Option (Fin E'.length) := fun i =>
    if h : E.get i ∈ E' then some (List.mem_iff_get.mp h).choose else none
  have hidx : ∀ i (hxi : x ∈ E.get i), ∃ j, idx i = some j ∧ E'.get j = E.get i := fun i hxi => by
    have h := hmem i hxi
    exact ⟨_, dif_pos h, (List.mem_iff_get.mp h).choose_spec⟩
  refine ⟨S₀, fun i => (idx i).elim ∅ S, ⟨Φ, hΦt, hΦ0, ?_⟩, fun i hi => ?_⟩
  · rintro (_ | i) hi y hy hyΦ
    · exact hΦA none hi hy hyΦ
    · obtain ⟨j, hj, hjE⟩ := hidx i hi
      have h1 := hΦA (some j) (by simp only [Option.elim]; rw [hjE]; exact hi) hy hyΦ
      simp only [Option.elim] at h1 ⊢
      rw [hjE] at h1
      rw [hj]
      exact h1
  · obtain ⟨j, hj, hjE⟩ := hidx i hi
    simp only [hj, Option.elim]
    exact hS j (by rw [hjE]; exact hi)

end NC

/-! ### The transforms of `(M, N, E', 𝔞, d)` -/

section Tower

variable {n : ℕ} {X : CMfd.{u} n}

/-- **Only the divisor depends on `E`**: along every tower the transforms of `(M, N, E', 𝔞, d)` and of `𝔪` have the same
submanifold, ideal and mark. -/
theorem geoTransformAlong_withE (𝔪 : MarkedIdeal n X) (E' : List (Set X)) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) →
      (geoTransformAlong ({ 𝔪 with E := E' } : MarkedIdeal n X) T).N = (geoTransformAlong 𝔪 T).N ∧
      (geoTransformAlong ({ 𝔪 with E := E' } : MarkedIdeal n X) T).ideal = (geoTransformAlong 𝔪 T).ideal ∧
      (geoTransformAlong ({ 𝔪 with E := E' } : MarkedIdeal n X) T).d = (geoTransformAlong 𝔪 T).d
  | _, .refl => ⟨rfl, rfl, rfl⟩
  | _, .step T C π hπ => by
    obtain ⟨hN, hI, hd⟩ := geoTransformAlong_withE 𝔪 E' T
    simp only [geoTransformAlong_step, geoTransform]
    exact ⟨by rw [hN], by rw [hN, hI, hd], hd⟩

/-- Along every tower the two transforms have the same cosupport. -/
theorem cosupp_geoTransformAlong_withE (𝔪 : MarkedIdeal n X) (E' : List (Set X)) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) :
    (geoTransformAlong ({ 𝔪 with E := E' } : MarkedIdeal n X) T).cosupp = (geoTransformAlong 𝔪 T).cosupp := by
  obtain ⟨hN, hI, hd⟩ := geoTransformAlong_withE 𝔪 E' T
  simp only [cosupp, hN, hI, hd]

/-- Admissibility for the transform of `(M, N, E', 𝔞, d)` is admissibility for the transform of `𝔪` with its divisor
replaced. -/
theorem isAdmissibleCentre_geoTransformAlong_withE_iff (𝔪 : MarkedIdeal n X) (E' : List (Set X)) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (C : Set Y) :
    (geoTransformAlong ({ 𝔪 with E := E' } : MarkedIdeal n X) T).IsAdmissibleCentre C ↔
      ({ geoTransformAlong 𝔪 T with E := (geoTransformAlong ({ 𝔪 with E := E' } : MarkedIdeal n X) T).E } :
        MarkedIdeal n Y).IsAdmissibleCentre C := by
  have hc := cosupp_geoTransformAlong_withE 𝔪 E' T
  unfold IsAdmissibleCentre
  rw [hc]
  rfl

/-- **Deleting the members that contain every centre**, general form: as `isGeoTestTower_withE_iff_of_centresIn`, with
well-formedness replaced by its only use, the simple normal crossings of the transformed divisor along the multiple test
blow-ups of `𝔪`. -/
theorem isGeoTestTower_withE_iff_of_centresIn_of_snc (𝔪 : MarkedIdeal n X)
    (hSNC : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower 𝔪 T →
      IsSNCDivisor n (geoTransformAlong 𝔪 T).E) {E' : List (Set X)}
    {S : Set X} (hsub : ∀ H ∈ E', H ∈ 𝔪.E) (hA : ∀ H ∈ 𝔪.E, H ∉ E' → S ⊆ H) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → CentresIn S T →
      (IsGeoTestTower ({ 𝔪 with E := E' } : MarkedIdeal n X) T ↔ IsGeoTestTower 𝔪 T) ∧
      (∀ H ∈ (geoTransformAlong ({ 𝔪 with E := E' } : MarkedIdeal n X) T).E, H ∈ (geoTransformAlong 𝔪 T).E) ∧
      (∀ H ∈ (geoTransformAlong 𝔪 T).E,
        H ∉ (geoTransformAlong ({ 𝔪 with E := E' } : MarkedIdeal n X) T).E → strictAlong T S ⊆ H)
  | _, .refl, _ => ⟨Iff.rfl, hsub, hA⟩
  | _, .step T C π hπ, hT => by
    obtain ⟨hTS, hCS⟩ := (centresIn_step_iff S T C π hπ).mp hT
    obtain ⟨hiff, hsubT, hAT⟩ := isGeoTestTower_withE_iff_of_centresIn_of_snc 𝔪 hSNC hsub hA T hTS
    refine ⟨?_, forall_mem_transformE π C hsubT, ?_⟩
    · have hadm : IsGeoTestTower 𝔪 T →
          ((geoTransformAlong ({ 𝔪 with E := E' } : MarkedIdeal n X) T).IsAdmissibleCentre C ↔
            (geoTransformAlong 𝔪 T).IsAdmissibleCentre C) := fun h𝔪T => by
        rw [isAdmissibleCentre_geoTransformAlong_withE_iff]
        exact isAdmissibleCentre_withE_iff _ (hSNC T h𝔪T) hsubT fun H hH hH' => hCS.trans (hAT H hH hH')
      simp only [isGeoTestTower_step_iff]
      constructor
      · rintro ⟨h1, h2⟩
        have h𝔪T := hiff.mp h1
        exact ⟨h𝔪T, (hadm h𝔪T).mp h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨hiff.mpr h1, (hadm h1).mpr h2⟩
    · rw [strictAlong_step]
      exact forall_notMem_transformE π C hAT

/-- **Deleting the members that contain every centre** (`hir:drop-containing-members`): let `𝔪` be well formed, `E'` a
list of members of `𝔪.E`, and `S` a set contained in every member of `𝔪.E` missing from `E'`. Along every tower with
centres in the strict transforms of `S`, the test towers of `(M, N, E', 𝔞, d)` and of `𝔪` coincide, every member of the
transformed `E'` is a member of the transformed `E`, and the members of the transformed `E` missing from the transformed
`E'` contain the strict transform of `S`. -/
theorem isGeoTestTower_withE_iff_of_centresIn (𝔪 : MarkedIdeal n X) (h𝔪 : 𝔪.IsWellFormed) {E' : List (Set X)}
    {S : Set X} (hsub : ∀ H ∈ E', H ∈ 𝔪.E) (hA : ∀ H ∈ 𝔪.E, H ∉ E' → S ⊆ H) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → CentresIn S T →
      (IsGeoTestTower ({ 𝔪 with E := E' } : MarkedIdeal n X) T ↔ IsGeoTestTower 𝔪 T) ∧
      (∀ H ∈ (geoTransformAlong ({ 𝔪 with E := E' } : MarkedIdeal n X) T).E, H ∈ (geoTransformAlong 𝔪 T).E) ∧
      (∀ H ∈ (geoTransformAlong 𝔪 T).E,
        H ∉ (geoTransformAlong ({ 𝔪 with E := E' } : MarkedIdeal n X) T).E → strictAlong T S ⊆ H) :=
  isGeoTestTower_withE_iff_of_centresIn_of_snc 𝔪
    (fun T hT => (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong h𝔪 T hT).isSNCDivisor) hsub hA

/-- **Deleting members away from the cosupport** (`hir:drop-members`): let `𝔪` have a closed submanifold `N` and a
coherent ideal, and let every member of `𝔪.E` missing from `E'` (a list of members of `𝔪.E`) be closed and disjoint
from `cosupp 𝔪`. Then `(M, N, E', 𝔞, d)` and `𝔪` have the same multiple test blow-ups. -/
theorem isGeoTestTower_withE_iff_of_disjoint (𝔪 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) {E' : List (Set X)} (hsub : ∀ H ∈ E', H ∈ 𝔪.E)
    (hdis : ∀ H ∈ 𝔪.E, H ∉ E' → IsClosed H ∧ Disjoint 𝔪.cosupp H) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) →
      (IsGeoTestTower ({ 𝔪 with E := E' } : MarkedIdeal n X) T ↔ IsGeoTestTower 𝔪 T) ∧
      (∀ H ∈ (geoTransformAlong ({ 𝔪 with E := E' } : MarkedIdeal n X) T).E, H ∈ (geoTransformAlong 𝔪 T).E) ∧
      (∀ H ∈ (geoTransformAlong 𝔪 T).E,
        H ∉ (geoTransformAlong ({ 𝔪 with E := E' } : MarkedIdeal n X) T).E →
          ∃ H₀ ∈ 𝔪.E, H₀ ∉ E' ∧ H ⊆ T.proj ⁻¹' H₀)
  | _, .refl => ⟨Iff.rfl, hsub, fun H hH hH' => ⟨H, hH, hH', fun _ hx => hx⟩⟩
  | _, .step T C π hπ => by
    obtain ⟨hiff, hsubT, hAT⟩ := isGeoTestTower_withE_iff_of_disjoint 𝔪 hN h𝔞 hsub hdis T
    refine ⟨?_, forall_mem_transformE π C hsubT, ?_⟩
    · -- the members missing from `E'_T` miss every centre inside the cosupport
      have hmiss : IsGeoTestTower 𝔪 T → ∀ C' ⊆ (geoTransformAlong 𝔪 T).cosupp,
          ∀ H ∈ (geoTransformAlong 𝔪 T).E,
            H ∉ (geoTransformAlong ({ 𝔪 with E := E' } : MarkedIdeal n X) T).E → Disjoint C' H := by
        intro h𝔪T C' hC' H hH hH'
        obtain ⟨H₀, hH₀, hH₀', hHsub⟩ := hAT H hH hH'
        refine Set.disjoint_left.mpr fun z hzC hzH => ?_
        have hzc := TransformOffCentre.cosupp_geoTransformAlong_subset 𝔪 hN h𝔞 T h𝔪T (hC' hzC)
        exact Set.disjoint_left.mp (hdis H₀ hH₀ hH₀').2 hzc (hHsub hzH)
      have hadm : IsGeoTestTower 𝔪 T →
          ((geoTransformAlong ({ 𝔪 with E := E' } : MarkedIdeal n X) T).IsAdmissibleCentre C ↔
            (geoTransformAlong 𝔪 T).IsAdmissibleCentre C) := fun h𝔪T => by
        rw [isAdmissibleCentre_geoTransformAlong_withE_iff]
        constructor
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h1, h2, hasNormalCrossings_of_forall_disjoint h3 (hmiss h𝔪T C h2)⟩
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h1, h2, hasNormalCrossings_of_forall_mem h3 hsubT⟩
      simp only [isGeoTestTower_step_iff]
      constructor
      · rintro ⟨h1, h2⟩
        have h𝔪T := hiff.mp h1
        exact ⟨h𝔪T, (hadm h𝔪T).mp h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨hiff.mpr h1, (hadm h1).mpr h2⟩
    · intro H hH hH'
      simp only [geoTransformAlong_step, geoTransform_E] at hH hH'
      rcases List.mem_append.mp hH with hH | hH
      · obtain ⟨K, hK, rfl⟩ := List.mem_map.mp hH
        have hK' : K ∉ (geoTransformAlong ({ 𝔪 with E := E' } : MarkedIdeal n X) T).E := fun h =>
          hH' (List.mem_append_left _ (List.mem_map_of_mem h))
        obtain ⟨H₀, hH₀, hH₀', hKsub⟩ := hAT K hK hK'
        refine ⟨H₀, hH₀, hH₀', ?_⟩
        rw [BlowupTower.proj_step]
        have hcl : IsClosed (π ⁻¹' (T.proj ⁻¹' H₀)) :=
          ((hdis H₀ hH₀ hH₀').1.preimage T.contMDiff_proj.continuous).preimage hπ.contMDiff.continuous
        exact closure_minimal (fun z hz => hKsub hz.1) hcl
      · exact absurd (List.mem_append_right _ hH) hH'

/-- Along a multiple test blow-up of `𝔪`, the transforms of the members deleted in `hir:drop-members` stay disjoint from
the cosupports. -/
theorem disjoint_cosupp_of_disjoint (𝔪 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) {E' : List (Set X)} (hsub : ∀ H ∈ E', H ∈ 𝔪.E)
    (hdis : ∀ H ∈ 𝔪.E, H ∉ E' → IsClosed H ∧ Disjoint 𝔪.cosupp H) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower 𝔪 T) (H : Set Y) (hH : H ∈ (geoTransformAlong 𝔪 T).E)
    (hH' : H ∉ (geoTransformAlong ({ 𝔪 with E := E' } : MarkedIdeal n X) T).E) :
    Disjoint (geoTransformAlong 𝔪 T).cosupp H := by
  obtain ⟨H₀, hH₀, hH₀', hHsub⟩ := (isGeoTestTower_withE_iff_of_disjoint 𝔪 hN h𝔞 hsub hdis T).2.2 H hH hH'
  refine Set.disjoint_left.mpr fun z hz hzH => ?_
  exact Set.disjoint_left.mp (hdis H₀ hH₀ hH₀').2
    (TransformOffCentre.cosupp_geoTransformAlong_subset 𝔪 hN h𝔞 T hT hz) (hHsub hzH)

end Tower

end

end TranscendentalNakamaye.Pending.DropMembers
