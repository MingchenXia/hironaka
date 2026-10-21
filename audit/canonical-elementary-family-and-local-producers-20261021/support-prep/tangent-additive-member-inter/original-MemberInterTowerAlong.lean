import TranscendentalNakamaye.Pending.ExceptionalPushforwardAlong
import TranscendentalNakamaye.Pending.BoundaryCount
import TranscendentalNakamaye.Pending.HomogenizedGlueingTower
import TranscendentalNakamaye.Pending.MarkedIdealOpenBiholomorphism
import TranscendentalNakamaye.Pending.NormalCrossingsComparison
import TranscendentalNakamaye.Pending.CoefficientIdealRestriction

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Strict transforms of intersections of members along multiple test blow-ups

Hironaka phase H2 (TN3), the blowup side of Step 1a inside a submanifold `N` (`hir:maximal-order-step`,
TN-CLASSICAL's H4 design; claim I-0977 C-0091).  Blueprint `bcalc:member-intersection-strict`,
`bcalc:member-intersection-tower` (chapter `blowup-calculus.tex`).  Sources: Włodarczyk 2009
(`wlodarczyk09-analytic-resolution`) Step 1a (printed p. 55, the intersections `H^s_α` of `s` divisors
and the count `s(x)` with the strict transforms of `E` identified with `E`); Bierstone--Milman 2008
(`bierstone-milman08-functoriality`) §2 (the transformed divisor `E'`).

Let `π` be the blowup along `C ⊆ N`, `E` a simple normal crossings divisor transverse to the closed
set `N`, `C` with only normal crossings with `E`, and `S` a set of indices of members.

* `geoStrictTransform_inter_memberInter_eq`: `(N ∩ H_S)' = N' ∩ ⋂_{i ∈ S} H_i'` -- the several-member
  form of `ExceptionalPushforwardAlong.geoStrictTransform_inter_eq` (in adapted coordinates all of them
  are coordinate subspaces of one monomial chart, `bcalc:snc-chart`).

Along a tower `T` (`strictAlong`, TN23's iterated strict transform):

* `take_E_geoTransformAlong`, `get_E_geoTransformAlong`: the first `#E` members of the transformed
  divisor `E_T` are the strict transforms `strictAlong T H_i` of the original members (the exceptional
  divisors are appended after them);
* `strictAlong_mono`, `isClosed_strictAlong`, `strictAlong_subset_preimage`,
  `disjoint_strictAlong`: strict transforms along a tower are monotone, closed, lie over the set, and
  so stay disjoint;
* `strictAlong_inter_memberInter`: for a well-formed `(M, N, E, 𝔞, d)` and a multiple test blow-up
  `T`, `(N ∩ H_S)_T = N_T ∩ ⋂_{i ∈ S} (H_i)_T` -- a point of `N_T` lying on the strict transforms of
  the members `H_i`, `i ∈ S`, lies on the strict transform of the intersection `N ∩ H_S`;
  `mem_strictAlong_inter_memberInter_iff` reads it with the members `E_T.get i` of the transform, and
  `mem_strictAlong_inter_memberInter_self` takes for `S` the original members through the point.  In
  Step 1a a point of the cosupport with `s(x) = s` thus lies on the strict transform of the
  intersection it lies on at the start of Step 1, where the restricted invariant is evaluated.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Pending.RelativePrincipalization` or `Pending.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace TranscendentalNakamaye.Pending.MemberInterTowerAlong

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
open TranscendentalNakamaye.Pending.BlowupFlatCoordinates
  TranscendentalNakamaye.Pending.BlowupMonomialCharts
  TranscendentalNakamaye.Pending.BlowupLocalSurjectivity
  TranscendentalNakamaye.Pending.BlowupStrictSubmanifold
  TranscendentalNakamaye.Pending.BlowupSNCTransform TranscendentalNakamaye.Pending.NormalCrossings
  TranscendentalNakamaye.Pending.SimultaneousNormalCrossings
  TranscendentalNakamaye.Pending.BoundaryCount TranscendentalNakamaye.Pending.BlowupTowers
  TranscendentalNakamaye.Pending.MarkedIdeals TranscendentalNakamaye.Pending.MarkedIdeals.MarkedIdeal
  TranscendentalNakamaye.Pending.HomogenizedGlueingTower

noncomputable section

variable {n : ℕ}

/-! ### One blowup: `(N ∩ H_S)' = N' ∩ ⋂_{i ∈ S} H_i'` -/

section OneBlowup

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

/-- **`(N ∩ H_S)' = N' ∩ ⋂_{i ∈ S} H_i'`**: for members `H_i`, `i ∈ S`, of a simple normal crossings
divisor `E` transverse to a closed set `N ⊇ C`, the centre `C` having only normal crossings with `E`,
the strict transform of `N ∩ H_S` is the intersection of the strict transforms of `N` and of the
`H_i`.  (Off `π⁻¹ C` the blowup is biholomorphic; over `C`, in adapted coordinates and a monomial
chart, all of them are coordinate subspaces, `bcalc:snc-chart`.) -/
theorem geoStrictTransform_inter_memberInter_eq (hπ : IsBlowupAlong n C π) {N : Set X}
    (hNc : IsClosed N) (hCN : C ⊆ N) {E : List (Set X)} (hE : IsSNCDivisor n E)
    (hT : IsTransverse n N E) (hnc : HasNormalCrossings n C E) (S : Finset (Fin E.length)) :
    geoStrictTransform π C (N ∩ memberInter E S) =
      geoStrictTransform π C N ∩ {z | ∀ i ∈ S, z ∈ geoStrictTransform π C (E.get i)} := by
  classical
  have hπc : Continuous π := hπ.contMDiff.continuous
  refine Subset.antisymm (subset_inter
    (closure_mono (preimage_mono (sdiff_subset_sdiff_left inter_subset_left)))
    fun z hz i hi => closure_mono (preimage_mono (sdiff_subset_sdiff_left fun y hy => hy.2 i hi)) hz) ?_
  rintro z ⟨hzN, hzH⟩
  have hzN' : π z ∈ N := geoStrictTransform_subset_preimage hπc hNc hzN
  have hzH' : ∀ i ∈ S, π z ∈ E.get i := fun i hi =>
    geoStrictTransform_subset_preimage hπc (hE.1 _ (List.get_mem _ _)) (hzH i hi)
  by_cases hzC : π z ∈ C
  · have hn : 0 < n := pos_of_isBlowupAlong hπ hzC
    obtain ⟨kC, kN, Φ, s, hΦt, -, -, hflat⟩ := isAdaptedAt_of_hasNormalCrossings hn hCN hE hT hnc hzC
    have hx' : π z ∈ flatDomain Φ := ⟨mem_chart_source _ (π z), Φ.center_mem_source⟩
    have hflatC : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
        chartAt (ComplexModel n) (π z) y ∈ Φ.source →
          (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ complexCoordinatePlane n kC) :=
      fun hy hyΦ => (hflat hy hyΦ).1
    set TN : Finset (Fin n) := Finset.univ.filter fun t : Fin n => kN ≤ t.1 with hTN
    have hflatN : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
        chartAt (ComplexModel n) (π z) y ∈ Φ.source →
          (y ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ coordSubspace TN) :=
      fun hy hyΦ => by
        rw [hTN, coordSubspace_eq_complexCoordinatePlane]; exact (hflat hy hyΦ).2.1
    have hflatH : ∀ i ∈ S, ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
        chartAt (ComplexModel n) (π z) y ∈ Φ.source →
          (y ∈ E.get i ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ coordSubspace {s i}) :=
      fun i hi y hy hyΦ => by
        rw [mem_coordSubspace_singleton]; exact (hflat hy hyΦ).2.2 i (hzH' i hi)
    set TS : Finset (Fin n) := S.biUnion (fun i => ({s i} : Finset (Fin n))) ∪ TN with hTS
    have hflatA : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
        chartAt (ComplexModel n) (π z) y ∈ Φ.source →
          (y ∈ N ∩ memberInter E S ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ coordSubspace TS) :=
      fun {y} hy hyΦ => by
        rw [hTS, ExceptionalPushforwardAlong.coordSubspace_union]
        simp only [mem_inter_iff]
        rw [mem_coordSubspace_biUnion]
        constructor
        · rintro ⟨hyN, hyS⟩
          exact ⟨fun i hi => (hflatH i hi hy hyΦ).mp (hyS i hi), (hflatN hy hyΦ).mp hyN⟩
        · rintro ⟨h1, h2⟩
          exact ⟨(hflatN hy hyΦ).mpr h2, fun i hi => (hflatH i hi hy hyΦ).mpr (h1 i hi)⟩
    obtain ⟨j, hj, O, hO, hzO, W, hWs, hWeq, hℓ, -⟩ :=
      exists_monomialLocalInverse hπ hΦt hflatC hx'
    obtain ⟨hjN, hWN⟩ :=
      (mem_geoStrictTransform_iff_of_chart hπ hΦt hflatC hflatN hj hO hWs hWeq hℓ hzO).mp hzN
    have hH : ∀ i ∈ S, j ∉ ({s i} : Finset (Fin n)) ∧ W z ∈ coordSubspace {s i} := fun i hi =>
      (mem_geoStrictTransform_iff_of_chart hπ hΦt hflatC (hflatH i hi) hj hO hWs hWeq hℓ hzO).mp
        (hzH i hi)
    refine (mem_geoStrictTransform_iff_of_chart hπ hΦt hflatC hflatA hj hO hWs hWeq hℓ
      hzO).mpr ⟨?_, ?_⟩
    · rw [hTS, Finset.mem_union, Finset.mem_biUnion]
      rintro (⟨i, hi, hji⟩ | h)
      exacts [(hH i hi).1 hji, hjN h]
    · rw [hTS, ExceptionalPushforwardAlong.coordSubspace_union, mem_inter_iff,
        mem_coordSubspace_biUnion]
      exact ⟨fun i hi => (hH i hi).2, hWN⟩
  · exact subset_closure ⟨⟨hzN', fun i hi => hzH' i hi⟩, hzC⟩

end OneBlowup

/-! ### Strict transforms along a tower -/

section Strict

variable {X : CMfd.{u} n}

/-- **Strict transforms along a tower are monotone.** -/
theorem strictAlong_mono : {Y : CMfd.{u} n} → (T : BlowupTower X Y) → {A B : Set X} → A ⊆ B →
    strictAlong T A ⊆ strictAlong T B
  | _, .refl, _, _, h => h
  | _, .step T _ _ _, _, _, h =>
      closure_mono (preimage_mono (sdiff_subset_sdiff_left (strictAlong_mono T h)))

/-- **Strict transforms of closed sets along a tower are closed** (along a nonempty tower they are
closures). -/
theorem isClosed_strictAlong : {Y : CMfd.{u} n} → (T : BlowupTower X Y) → {A : Set X} →
    IsClosed A → IsClosed (strictAlong T A)
  | _, .refl, _, hA => hA
  | _, .step _ _ _ _, _, _ => isClosed_closure

/-- **The strict transform of a closed set lies over it.** -/
theorem strictAlong_subset_preimage : {Y : CMfd.{u} n} → (T : BlowupTower X Y) → {A : Set X} →
    IsClosed A → strictAlong T A ⊆ T.proj ⁻¹' A
  | _, .refl, _, _ => fun _ h => h
  | _, .step T _ _ hπ, _, hA => fun _ hz =>
      strictAlong_subset_preimage T hA
        (geoStrictTransform_subset_preimage hπ.contMDiff.continuous (isClosed_strictAlong T hA) hz)

/-- **Strict transforms of disjoint closed sets stay disjoint.** -/
theorem disjoint_strictAlong {Y : CMfd.{u} n} (T : BlowupTower X Y) {A B : Set X} (hA : IsClosed A)
    (hB : IsClosed B) (hAB : Disjoint A B) : Disjoint (strictAlong T A) (strictAlong T B) :=
  Disjoint.mono (strictAlong_subset_preimage T hA) (strictAlong_subset_preimage T hB)
    (hAB.preimage T.proj)

end Strict

/-! ### The original members along a tower -/

section Members

variable {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X)

/-- **The first `#E` members of `E_T` are the strict transforms of the members of `E`**: the
exceptional divisors are appended after them. -/
theorem take_E_geoTransformAlong : {Y : CMfd.{u} n} → (T : BlowupTower X Y) →
    (geoTransformAlong 𝔪 T).E.take 𝔪.E.length = 𝔪.E.map (strictAlong T)
  | _, .refl => by
    simp only [geoTransformAlong_refl, List.take_length]
    exact (List.map_id' _).symm
  | _, .step T C π hπ => by
    have hlen :
        𝔪.E.length ≤ ((geoTransformAlong 𝔪 T).E.map (geoStrictTransform π C)).length := by
      rw [List.length_map, length_E_geoTransformAlong]; omega
    rw [geoTransformAlong_step, geoTransform_E, List.take_append_of_le_length hlen, ← List.map_take,
      take_E_geoTransformAlong T, List.map_map]
    rfl

theorem length_E_le_length_E_geoTransformAlong {Y : CMfd.{u} n} (T : BlowupTower X Y) :
    𝔪.E.length ≤ (geoTransformAlong 𝔪 T).E.length := by
  rw [length_E_geoTransformAlong]; omega

/-- **The `i`-th member of `E_T` is the strict transform of the `i`-th member of `E`**
(`i < #E`). -/
theorem get_E_geoTransformAlong {Y : CMfd.{u} n} (T : BlowupTower X Y) (i : Fin 𝔪.E.length) :
    (geoTransformAlong 𝔪 T).E.get (Fin.castLE (length_E_le_length_E_geoTransformAlong 𝔪 T) i) =
      strictAlong T (𝔪.E.get i) := by
  have h := List.getElem_of_eq (take_E_geoTransformAlong 𝔪 T)
    (i := i.1) (by rw [List.length_take]; exact lt_min i.2 (by
      have := length_E_le_length_E_geoTransformAlong 𝔪 T; omega))
  simp only [List.getElem_take, List.getElem_map] at h
  simpa using h

end Members

/-! ### `(N ∩ H_S)_T = N_T ∩ ⋂_{i ∈ S} (H_i)_T` along a multiple test blow-up -/

section Tower

variable {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X)

/-- The intersection of strict transforms as an intersection of members of `E_T`. -/
theorem setOf_forall_strictAlong_eq_memberInter {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (S : Finset (Fin 𝔪.E.length)) :
    {z | ∀ i ∈ S, z ∈ strictAlong T (𝔪.E.get i)} =
      memberInter (geoTransformAlong 𝔪 T).E
        (S.map (Fin.castLEEmb (length_E_le_length_E_geoTransformAlong 𝔪 T))) := by
  ext z
  simp only [memberInter, mem_ofPred_eq, Finset.mem_map, Fin.castLEEmb_apply, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, get_E_geoTransformAlong]

/-- **`(N ∩ H_S)_T = N_T ∩ ⋂_{i ∈ S} (H_i)_T`** along a multiple test blow-up `T` of a well-formed
marked ideal `(M, N, E, 𝔞, d)`: the strict transform of the intersection of `N` with the members
`H_i`, `i ∈ S`, is the intersection of `N_T` with their strict transforms. -/
theorem strictAlong_inter_memberInter (h𝔪 : 𝔪.IsWellFormed) (S : Finset (Fin 𝔪.E.length)) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower 𝔪 T →
      strictAlong T (𝔪.N ∩ memberInter 𝔪.E S) =
        (geoTransformAlong 𝔪 T).N ∩ {z | ∀ i ∈ S, z ∈ strictAlong T (𝔪.E.get i)}
  | _, .refl, _ => rfl
  | _, .step T C π hπ, hT => by
    have ih := strictAlong_inter_memberInter h𝔪 S T hT.1
    have hW := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong h𝔪 T hT.1
    have hC : (geoTransformAlong 𝔪 T).IsAdmissibleCentre C := hT.2
    rw [strictAlong_step, ih, setOf_forall_strictAlong_eq_memberInter 𝔪 T S,
      geoStrictTransform_inter_memberInter_eq hπ hW.isClosedSubmanifold_N.1 hC.subset_N
        hW.isSNCDivisor hW.isTransverse hC.2.2]
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, Finset.mem_map, Fin.castLEEmb_apply,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, get_E_geoTransformAlong,
      N_geoTransformAlong_step, strictAlong_step]

/-- `strictAlong_inter_memberInter` with the members `E_T.get i` of the transformed divisor. -/
theorem mem_strictAlong_inter_memberInter_iff (h𝔪 : 𝔪.IsWellFormed) (S : Finset (Fin 𝔪.E.length))
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) (z : Y) :
    z ∈ strictAlong T (𝔪.N ∩ memberInter 𝔪.E S) ↔ z ∈ (geoTransformAlong 𝔪 T).N ∧
      ∀ i ∈ S, z ∈ (geoTransformAlong 𝔪 T).E.get
        (Fin.castLE (length_E_le_length_E_geoTransformAlong 𝔪 T) i) := by
  rw [strictAlong_inter_memberInter 𝔪 h𝔪 S T hT]
  simp only [mem_inter_iff, mem_ofPred_eq, get_E_geoTransformAlong]

open Classical in
/-- **A point of `N_T` lies on the strict transform of the intersection of `N` with the original
members whose strict transforms pass through it** (Step 1a: the intersection `N ∩ H_S` a point with
`s(x) = s` lies on). -/
theorem mem_strictAlong_inter_memberInter_self (h𝔪 : 𝔪.IsWellFormed) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) {z : Y} (hz : z ∈ (geoTransformAlong 𝔪 T).N) :
    z ∈ strictAlong T
      (𝔪.N ∩ memberInter 𝔪.E (Finset.univ.filter fun i => z ∈ strictAlong T (𝔪.E.get i))) := by
  rw [strictAlong_inter_memberInter 𝔪 h𝔪 _ T hT]
  exact ⟨hz, fun i hi => (Finset.mem_filter.mp hi).2⟩

end Tower

/-! ### Localising the centres over an open set -/

section Localise

variable {X : CMfd.{u} n}

open TopologicalSpace TranscendentalNakamaye.Pending.BlowupTowerTransforms
  TranscendentalNakamaye.Pending.CoefficientIdealRestriction

/-- **The strict transform of a union along a tower is the union of the strict transforms.** -/
theorem strictAlong_union : {Y : CMfd.{u} n} → (T : BlowupTower X Y) → (A B : Set X) →
    strictAlong T (A ∪ B) = strictAlong T A ∪ strictAlong T B
  | _, .refl, _, _ => rfl
  | _, .step T C π _, A, B => by
    rw [strictAlong_step, strictAlong_step, strictAlong_step, strictAlong_union T A B]
    unfold geoStrictTransform
    rw [union_sdiff_distrib, preimage_union, closure_union]

/-- **Localising the centres, several intersections at once** (Step 1a, "moving apart"): if the
centres of `T` lie in the strict transforms of `A ∪ B`, with `B` closed and disjoint from the open
set `U`, then the centres of the restriction of `T` to `U` lie in the strict transforms of `A ∩ U`. -/
theorem centresIn_restrict_of_centresIn_union (U : Opens X) {A B : Set X} (hB : IsClosed B)
    (hUB : Disjoint (U : Set X) B) : {Y : CMfd.{u} n} → (T : BlowupTower X Y) →
      CentresIn (A ∪ B) T → CentresIn ((↑) ⁻¹' A : Set U) (restrict U T)
  | _, .refl, _ => trivial
  | _, .step T C _ _, hT => by
    refine ⟨centresIn_restrict_of_centresIn_union U hB hUB T hT.1, fun p hp => ?_⟩
    rw [strictAlong_restrict U T A]
    have hpC : p.1 ∈ strictAlong T A ∪ strictAlong T B := by
      rw [← strictAlong_union]; exact hT.2 hp
    rcases hpC with h | h
    · exact h
    · exact absurd (strictAlong_subset_preimage T hB h) (Set.disjoint_left.mp hUB p.2)

/-- **Localising the centres, for every multiple test blow-up** (Step 1b, a hypersurface of maximal
contact on `U`): if every admissible centre `C` of every multiple test blow-up `T` of `𝔪` satisfies
`C ∩ T⁻¹ U ⊆ A_T`, then the centres of the restriction to `U` of every multiple test blow-up of `𝔪`
lie in the strict transforms of `A ∩ U`. -/
theorem centresIn_restrict_of_forall (𝔪 : MarkedIdeal n X) (U : Opens X) {A : Set X}
    (h : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y), IsGeoTestTower 𝔪 T →
      (geoTransformAlong 𝔪 T).IsAdmissibleCentre C → C ∩ T.proj ⁻¹' (U : Set X) ⊆ strictAlong T A) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower 𝔪 T →
      CentresIn ((↑) ⁻¹' A : Set U) (restrict U T)
  | _, .refl, _ => trivial
  | _, .step T C _ _, hT => by
    refine ⟨centresIn_restrict_of_forall 𝔪 U h T hT.1, fun p hp => ?_⟩
    rw [strictAlong_restrict U T A]
    exact h T C hT.1 hT.2 ⟨hp, p.2⟩

end Localise

/-! ### Transversality to the strict transform of a submanifold containing the centres -/

section Transverse

variable {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X)

open TranscendentalNakamaye.Pending.CoefficientIdealRestriction

/-- The members of `E_T` after the original ones, after one more blowup. -/
theorem drop_E_geoTransformAlong_step {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y)
    (π : Z → Y) (hπ : IsBlowupAlong n C π) :
    (geoTransformAlong 𝔪 (.step T C π hπ)).E.drop 𝔪.E.length =
      ((geoTransformAlong 𝔪 T).E.drop 𝔪.E.length).map (geoStrictTransform π C) ++ [π ⁻¹' C] := by
  have hlen : 𝔪.E.length ≤ ((geoTransformAlong 𝔪 T).E.map (geoStrictTransform π C)).length := by
    rw [List.length_map, length_E_geoTransformAlong]; omega
  rw [geoTransformAlong_step, geoTransform_E, List.drop_append_of_le_length hlen, List.map_drop]

/-- **The exceptional members are transverse to the strict transform of a submanifold containing
the centres** (Włodarczyk 2009, p. 55, remark (5): the new divisors are born from centres in the
hypersurface of maximal contact, and are transversal to it).  Let `𝔪` be well formed, `W` a closed
submanifold and `T` a multiple test blow-up of `𝔪` whose centres lie in the strict transforms of `W`.
Then `W_T` is a closed submanifold, and the members of `E_T` after the original ones (the
exceptional divisors of `T`) form a simple normal crossings divisor transverse to `W_T`. -/
theorem isTransverse_drop_E_geoTransformAlong (h𝔪 : 𝔪.IsWellFormed) {W : Set X}
    (hW : IsClosedSubmanifold n W) : {Y : CMfd.{u} n} → (T : BlowupTower X Y) →
      IsGeoTestTower 𝔪 T → CentresIn W T →
      IsClosedSubmanifold n (strictAlong T W) ∧
        IsSNCDivisor n ((geoTransformAlong 𝔪 T).E.drop 𝔪.E.length) ∧
        IsTransverse n (strictAlong T W) ((geoTransformAlong 𝔪 T).E.drop 𝔪.E.length)
  | _, .refl, _, _ => by
    simp only [geoTransformAlong_refl, List.drop_length, strictAlong_refl]
    exact ⟨hW, isSNCDivisor_nil, isTransverse_nil_of_isClosedSubmanifold hW⟩
  | _, .step T C π hπ, hT, hTW => by
    obtain ⟨hWT, hsnc, htr⟩ := isTransverse_drop_E_geoTransformAlong h𝔪 hW T hT.1 hTW.1
    have hC : (geoTransformAlong 𝔪 T).IsAdmissibleCentre C := hT.2
    have hCW : C ⊆ strictAlong T W := hTW.2
    have hnc : HasNormalCrossings n C ((geoTransformAlong 𝔪 T).E.drop 𝔪.E.length) :=
      NormalCrossingsComparison.hasNormalCrossings_of_forall_mem hC.2.2
        fun _ hH => List.mem_of_mem_drop hH
    rw [drop_E_geoTransformAlong_step, strictAlong_step]
    exact ⟨BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hWT hCW,
      isSNCDivisor_geoTransformE_of_hasNormalCrossings hπ hsnc hnc,
      isTransverse_geoTransformE_of_hasNormalCrossings hπ hWT.1 hCW hsnc htr hnc⟩

/-- **All of `E_T` is transverse to `W_T`** when `E` is transverse to `W` at the start and the
centres lie in the strict transforms of `W`. -/
theorem isTransverse_E_geoTransformAlong (h𝔪 : 𝔪.IsWellFormed) {W : Set X}
    (hW : IsClosedSubmanifold n W) (hWE : IsTransverse n W 𝔪.E) : {Y : CMfd.{u} n} →
      (T : BlowupTower X Y) → IsGeoTestTower 𝔪 T → CentresIn W T →
      IsClosedSubmanifold n (strictAlong T W) ∧ IsTransverse n (strictAlong T W) (geoTransformAlong 𝔪 T).E
  | _, .refl, _, _ => ⟨hW, hWE⟩
  | _, .step T C π hπ, hT, hTW => by
    obtain ⟨hWT, htr⟩ := isTransverse_E_geoTransformAlong h𝔪 hW hWE T hT.1 hTW.1
    have hwf := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong h𝔪 T hT.1
    have hC : (geoTransformAlong 𝔪 T).IsAdmissibleCentre C := hT.2
    have hCW : C ⊆ strictAlong T W := hTW.2
    rw [geoTransformAlong_step, geoTransform_E, strictAlong_step]
    exact ⟨BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hWT hCW,
      isTransverse_geoTransformE_of_hasNormalCrossings hπ hWT.1 hCW hwf.isSNCDivisor htr hC.2.2⟩

/-- **The marked ideal on `W_T` with the exceptional members is well formed**: under the hypotheses
of `isTransverse_drop_E_geoTransformAlong`, `(Y, W_T, E_T without the original members, 𝔟, μ)` is well
formed for every coherent `𝔟` (Step 1b's marked ideal on the strict transform of the hypersurface of
maximal contact, the old members having been dropped in Step 1a). -/
theorem isWellFormed_strictAlong_drop (h𝔪 : 𝔪.IsWellFormed) {W : Set X}
    (hW : IsClosedSubmanifold n W) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T)
    (hTW : CentresIn W T) {𝔟 : GermIdeal n Y} (h𝔟 : 𝔟.IsCoherent) (μ : ℕ) :
    ({ N := strictAlong T W, E := (geoTransformAlong 𝔪 T).E.drop 𝔪.E.length, ideal := 𝔟, d := μ } :
      MarkedIdeal n Y).IsWellFormed :=
  let h := isTransverse_drop_E_geoTransformAlong 𝔪 h𝔪 hW T hT hTW
  ⟨h.1, h𝔟, h.2.1, h.2.2⟩

end Transverse

end

end TranscendentalNakamaye.Pending.MemberInterTowerAlong
