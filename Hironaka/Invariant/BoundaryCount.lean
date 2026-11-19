import Hironaka.Invariant.MemberPullback
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Intersections of members of a normal crossings divisor and the boundary count

Source: Wlodarczyk 2005 (`wlodarczyk05-hironaka`), proof of Proposition `pr:resol`, Step 1a
("reduction to the nonboundary case": `s(x)` is the number of divisors in `E` through `x`, the
intersections `H^s_α` of `s` members, and "if `s ≥ 2` then by blowing up `C = H^s_α` we separate
divisors contributing to `H^s_α`, thus creating new points all with `s(x) < s`"); Bierstone--Milman
2008, §5.  Blueprint `bcalc:member-intersection`, `bcalc:boundary-count`,
`bcalc:boundary-count-drop` (chapter `blowup-calculus.tex`); H4 list item 4 (I-0977 C-0045).

Let `E` be a simple normal crossings divisor on `X` and `S` a set of indices of members.

* `memberInter E S = ⋂_{i ∈ S} E.get i`: `hasNormalCrossings_memberInter` (it has normal crossings
  with `E`), `isClosedSubmanifold_memberInter` (it is a closed submanifold, `0 < n`), and
  `isAdmissibleCentre_memberInter` (inside the cosupport of a marked ideal with boundary `E`, it is
  an admissible centre).
* `boundaryCount E x = #{i | x ∈ E.get i}`: `eventually_boundaryCount_le` (upper semicontinuous),
  `boundaryCount_map` (re-indexing along `E.map f`), `boundaryCount_map_geoStrictTransform_le`
  (along a blowup the strict transforms of the members through `z` come from members through `π z`).
* `boundaryCount_map_geoStrictTransform_lt` (**the blowup of a maximal intersection separates the
  members**): if the centre is `C = memberInter E S` and no member outside `S` meets `C`, then every
  point `z` over `C` lies on fewer than `#S` strict transforms of members (a blowup centre is never
  the whole manifold, so `S ≠ ∅` is automatic).  Proof: in adapted coordinates
  and a monomial chart `j` around `z`, all members of `S` through `z` would give `W_{s i}(z) = 0`,
  `s i ≠ j`; then the points `σ_j(W z + ε e_j)` lie on every member of `S`, hence in `C`, although
  their `j`-th coordinate is `ε ≠ 0`.
* The local form: `card_filter_mem_geoStrictTransform_lt` (if `C ⊇ H_S` near `π z`, then `z` is not
  on all the `H_i'`, `i ∈ S`) and `boundaryCount_map_geoStrictTransform_lt_boundaryCount` (if near
  `x = π z` the centre contains the intersection of the members through `x`, then `s'(z) < s(x)`; no
  global maximality).  The same curve, now taken close to `π z`.
* Along a tower: `boundaryCount_take_E_transformAlong_le` and
  `boundaryCount_take_E_geoTransformAlong_le` (the first `#E` members of the transformed divisor,
  the strict transforms of the original members, pass through at most `s(T.proj z)` of them at `z`),
  with `isClosed_of_mem_take_E_transformAlong`, `isClosed_of_mem_take_E_geoTransformAlong`.

Everything here is sorry-free, and outside the import closure of the two Hironaka statements.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.BoundaryCount

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupFlatCoordinates BlowupMonomialCharts BlowupLocalSurjectivity BlowupStrictSubmanifold
  BlowupSNCTransform NormalCrossings SimultaneousNormalCrossings MarkedIdeals

noncomputable section

variable {n : ℕ}

section Members

variable {X : Type*} [TopologicalSpace X]

/-- The intersection of the members of `E` with indices in `S`. -/
def memberInter (E : List (Set X)) (S : Finset (Fin E.length)) : Set X :=
  {x | ∀ i ∈ S, x ∈ E.get i}

open Classical in
/-- **The boundary count** `s(x)`: the number of members of `E` through `x`. -/
def boundaryCount (E : List (Set X)) (x : X) : ℕ :=
  (Finset.univ.filter fun i : Fin E.length => x ∈ E.get i).card

/-- An intersection of closed members is closed. -/
theorem isClosed_memberInter {E : List (Set X)} (hE : ∀ H ∈ E, IsClosed H)
    (S : Finset (Fin E.length)) : IsClosed (memberInter E S) := by
  have : memberInter E S = ⋂ i ∈ S, E.get i := by
    ext x
    simp [memberInter]
  rw [this]
  exact isClosed_biInter fun i _ => hE _ (List.get_mem _ _)

/-- `x` lies on the coordinate subspace of a union iff on each. -/
theorem mem_coordSubspace_biUnion {ι : Type*} (S : Finset ι) (T : ι → Finset (Fin n))
    (w : ComplexModel n) : w ∈ coordSubspace (S.biUnion T) ↔ ∀ i ∈ S, w ∈ coordSubspace (T i) := by
  simp only [coordSubspace, mem_ofPred_eq, Finset.mem_biUnion]
  constructor
  · intro h i hi t ht
    exact h t ⟨i, hi, ht⟩
  · rintro h t ⟨i, hi, ht⟩
    exact h i hi t ht

open Classical in
/-- **Upper semicontinuity of the boundary count**: near `x`, only members through `x` pass. -/
theorem eventually_boundaryCount_le {E : List (Set X)} (hE : ∀ H ∈ E, IsClosed H) (x : X) :
    ∀ᶠ y in 𝓝 x, boundaryCount E y ≤ boundaryCount E x := by
  have h : ∀ᶠ y in 𝓝 x, ∀ i : Fin E.length, x ∉ E.get i → y ∉ E.get i :=
    eventually_all.mpr fun i => by
      by_cases hi : x ∈ E.get i
      · exact Eventually.of_forall fun _ h => absurd hi h
      · filter_upwards [(hE _ (List.get_mem _ _)).isOpen_compl.mem_nhds hi] with y hy _
        exact hy
  filter_upwards [h] with y hy
  refine Finset.card_le_card fun i hi => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  by_contra hx
  exact hy i hx hi

open Classical in
/-- **Re-indexing along a map of the members.** -/
theorem boundaryCount_map {Y : Type*} (f : Set X → Set Y) (E : List (Set X)) (z : Y) :
    boundaryCount (E.map f) z =
      (Finset.univ.filter fun i : Fin E.length => z ∈ f (E.get i)).card := by
  unfold boundaryCount
  refine Finset.card_equiv (finCongr (List.length_map f)) fun i => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, finCongr_apply, List.get_eq_getElem,
    List.getElem_map, Fin.val_cast]

end Members

section Manifold

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

omit [IsComplexManifold n X] in
/-- Truncating the dimension at `n` does not change the coordinate plane. -/
theorem complexCoordinatePlane_min (k : ℕ) :
    complexCoordinatePlane n (min k n) = complexCoordinatePlane n k := by
  ext w
  simp only [complexCoordinatePlane, mem_ofPred_eq]
  refine forall_congr' fun i => ?_
  have hi := i.2
  have : min k n ≤ i.1 ↔ k ≤ i.1 := by omega
  rw [this]

/-- **An intersection of members has normal crossings with `E`.** -/
theorem hasNormalCrossings_memberInter {E : List (Set X)} (hE : IsSNCDivisor n E)
    (S : Finset (Fin E.length)) : HasNormalCrossings n (memberInter E S) E := by
  intro x hx
  obtain ⟨T, ⟨Φ, hΦt, hΦ0, hΦA⟩, hcard, -⟩ := hE.2 x
  refine ⟨S.biUnion T, T, ⟨Φ, hΦt, hΦ0, ?_⟩, hcard⟩
  rintro (_ | i) hxi y hy hyΦ
  · change (∀ i ∈ S, y ∈ E.get i) ↔
      Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (S.biUnion T)
    rw [mem_coordSubspace_biUnion]
    exact forall₂_congr fun i hi => hΦA i (hx i hi) hy hyΦ
  · exact hΦA i hxi hy hyΦ

/-- **An intersection of members is a closed submanifold** (`0 < n`). -/
theorem isClosedSubmanifold_memberInter (hn : 0 < n) {E : List (Set X)} (hE : IsSNCDivisor n E)
    (S : Finset (Fin E.length)) : IsClosedSubmanifold n (memberInter E S) := by
  refine ⟨isClosed_memberInter hE.1 S, fun x hx => ?_⟩
  obtain ⟨kC, kN, Φ, s, -, -, -, hflat⟩ := isAdaptedAt_of_hasNormalCrossings hn (subset_univ _) hE
    (isTransverse_univ_of_isSNCDivisor hE) (hasNormalCrossings_memberInter hE S) hx
  refine ⟨min kC n, RegularPatchNeighborhood.regularAtDim_of_flattening (min_le_right _ _) Φ
    (fun {y} hy hyΦ => ?_) hx (mem_chart_source _ x) Φ.center_mem_source⟩
  have h := (hflat hy hyΦ).1
  rw [← complexCoordinatePlane_min] at h
  exact h

/-- **An intersection of members inside the cosupport is an admissible centre.** -/
theorem isAdmissibleCentre_memberInter (hn : 0 < n) (𝔪 : MarkedIdeal n X)
    (hE : IsSNCDivisor n 𝔪.E) (S : Finset (Fin 𝔪.E.length)) (hsub : memberInter 𝔪.E S ⊆ 𝔪.cosupp) :
    𝔪.IsAdmissibleCentre (memberInter 𝔪.E S) :=
  ⟨isClosedSubmanifold_memberInter hn hE S, hsub, hasNormalCrossings_memberInter hE S⟩

section Blowup

variable {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

open Classical in
/-- **The boundary count does not increase**: the strict transforms of the members through `z` come
from members through `π z`. -/
theorem boundaryCount_map_geoStrictTransform_le (hπc : Continuous π) {E : List (Set X)}
    (hE : ∀ H ∈ E, IsClosed H) (z : Y) :
    boundaryCount (E.map (geoStrictTransform π C)) z ≤ boundaryCount E (π z) := by
  rw [boundaryCount_map]
  refine Finset.card_le_card fun i hi => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact geoStrictTransform_subset_preimage hπc (hE _ (List.get_mem _ _)) hi

open Classical in
/-- **Blowing up a maximal intersection of members separates them** (Wlodarczyk, Step 1aa): if
`C = ⋂_{i ∈ S} E.get i` and no member outside `S` meets `C`, every point over `C` lies on fewer than
`#S` strict transforms of members. -/
theorem boundaryCount_map_geoStrictTransform_lt (hπ : IsBlowupAlong n C π) {E : List (Set X)}
    (hE : IsSNCDivisor n E) (S : Finset (Fin E.length)) (hC : C = memberInter E S)
    (hS : ∀ x ∈ C, ∀ i, x ∈ E.get i → i ∈ S) {z : Y} (hz : π z ∈ C) :
    boundaryCount (E.map (geoStrictTransform π C)) z < S.card := by
  rw [boundaryCount_map]
  have hsub : (Finset.univ.filter fun i : Fin E.length =>
      z ∈ geoStrictTransform π C (E.get i)) ⊆ S := fun i hi => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hS _ hz i
      (geoStrictTransform_subset_preimage hπ.contMDiff.continuous (hE.1 _ (List.get_mem _ _)) hi)
  refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => ?_⟩)
  have hall : ∀ i ∈ S, z ∈ geoStrictTransform π C (E.get i) := fun i hi => by
    have : i ∈ Finset.univ.filter fun i : Fin E.length =>
        z ∈ geoStrictTransform π C (E.get i) := heq ▸ hi
    simpa using this
  have hzS : π z ∈ memberInter E S := by rw [← hC]; exact hz
  have hn : 0 < n := pos_of_isBlowupAlong hπ hz
  have hnc : HasNormalCrossings n C E := by rw [hC]; exact hasNormalCrossings_memberInter hE S
  obtain ⟨kC, kN, Φ, s, hΦt, -, -, hflat⟩ := isAdaptedAt_of_hasNormalCrossings hn (subset_univ C) hE
    (isTransverse_univ_of_isSNCDivisor hE) hnc hz
  have hz' : π z ∈ flatDomain Φ := ⟨mem_chart_source _ (π z), Φ.center_mem_source⟩
  have hflatC : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ complexCoordinatePlane n kC) :=
    fun hy hyΦ => (hflat hy hyΦ).1
  obtain ⟨j, hj, O, hO, hzO, W, hWs, hWeq, hℓ, -⟩ :=
    exists_monomialLocalInverse hπ hΦt hflatC hz'
  -- every member of `S` passes through `z`: its coordinate is not `j` and vanishes at `W z`
  have hHi : ∀ i ∈ S, s i ≠ j ∧ W z (s i) = 0 := fun i hi => by
    have hflatH : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
        chartAt (ComplexModel n) (π z) y ∈ Φ.source →
          (y ∈ E.get i ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ coordSubspace {s i}) :=
      fun hy hyΦ => by
        rw [mem_coordSubspace_singleton]
        exact (hflat hy hyΦ).2.2 i (hzS i hi)
    have h := (mem_geoStrictTransform_iff_of_chart hπ hΦt hflatC hflatH hj hO hWs hWeq hℓ hzO).mp
      (hall i hi)
    exact ⟨fun hsj => h.1 (by simp [hsj]), mem_coordSubspace_singleton.mp h.2⟩
  have hWj : W z j = 0 := by
    have h := (hflatC (hWeq z hzO).1.1 (hWeq z hzO).1.2).mp hz
    rw [← (hWeq z hzO).2, monomial_mem_plane_iff hj] at h
    exact h
  -- the points `σ_j(W z + ε e_j)` lie on every member of `S` but not in `C`
  have hpt : monomial kC j (W z) ∈ Φ.target := by
    rw [(hWeq z hzO).2]
    exact Φ.mapsTo_toFun (hWeq z hzO).1.2
  have hcont : Continuous fun ε : ℂ => monomial kC j (W z + ε • EuclideanSpace.single j (1 : ℂ)) :=
    (contDiff_monomial kC j).continuous.comp (by fun_prop)
  have htend : Tendsto (fun ε : ℂ => monomial kC j (W z + ε • EuclideanSpace.single j (1 : ℂ)))
      (𝓝 0) (𝓝 (monomial kC j (W z))) := by
    simpa using hcont.tendsto 0
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (htend (Φ.isOpen_target.mem_nhds hpt))
  have hε : dist ((r / 2 : ℝ) : ℂ) 0 < r := by
    rw [dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  have hwt := hball hε
  have hsrc := Φ.mapsTo_invFun hwt
  have htgt := hΦt hsrc
  have hys := (chartAt (ComplexModel n) (π z)).map_target htgt
  have hey := (chartAt (ComplexModel n) (π z)).right_inv htgt
  have hyΦ : chartAt (ComplexModel n) (π z) ((chartAt (ComplexModel n) (π z)).symm
      (Φ.invFun (monomial kC j (W z + ((r / 2 : ℝ) : ℂ) • EuclideanSpace.single j (1 : ℂ)))))
        ∈ Φ.source := by
    rw [hey]; exact hsrc
  have hΦy : Φ.toFun (chartAt (ComplexModel n) (π z) ((chartAt (ComplexModel n) (π z)).symm
      (Φ.invFun (monomial kC j (W z + ((r / 2 : ℝ) : ℂ) • EuclideanSpace.single j (1 : ℂ)))))) =
      monomial kC j (W z + ((r / 2 : ℝ) : ℂ) • EuclideanSpace.single j (1 : ℂ)) := by
    rw [hey]; exact Φ.right_inv _ hwt
  have hyC : (chartAt (ComplexModel n) (π z)).symm
      (Φ.invFun (monomial kC j (W z + ((r / 2 : ℝ) : ℂ) • EuclideanSpace.single j (1 : ℂ))))
        ∈ C := by
    rw [hC]
    intro i hi
    refine ((hflat hys hyΦ).2.2 i (hzS i hi)).mpr ?_
    rw [hΦy]
    obtain ⟨hsj, hW0⟩ := hHi i hi
    simp [monomial_apply, hsj, hW0]
  have h := (hflatC hys hyΦ).mp hyC
  rw [hΦy, monomial_mem_plane_iff hj] at h
  simp [hWj] at h
  linarith

open Classical in
/-- **No point over the centre lies on all the strict transforms** of the members of `S`, if near
`π z` the centre contains their intersection (`C ⊇ H_S`, for instance `C = H_S`): same curve
`σ_j(W z + ε e_j)` as in `boundaryCount_map_geoStrictTransform_lt`, now taken close to `π z`. -/
theorem card_filter_mem_geoStrictTransform_lt (hπ : IsBlowupAlong n C π) {E : List (Set X)}
    (hE : IsSNCDivisor n E) (hnc : HasNormalCrossings n C E) (S : Finset (Fin E.length))
    {z : Y} (hz : π z ∈ C) (hC : ∀ᶠ y in 𝓝 (π z), y ∈ memberInter E S → y ∈ C) :
    (S.filter fun i => z ∈ geoStrictTransform π C (E.get i)).card < S.card := by
  refine Finset.card_lt_card (Finset.filter_ssubset.mpr ?_)
  by_contra hall
  simp only [not_exists, not_and, not_not] at hall
  have hzS : ∀ i ∈ S, π z ∈ E.get i := fun i hi =>
    geoStrictTransform_subset_preimage hπ.contMDiff.continuous (hE.1 _ (List.get_mem _ _))
      (hall i hi)
  have hn : 0 < n := pos_of_isBlowupAlong hπ hz
  obtain ⟨kC, kN, Φ, s, hΦt, -, -, hflat⟩ := isAdaptedAt_of_hasNormalCrossings hn (subset_univ C) hE
    (isTransverse_univ_of_isSNCDivisor hE) hnc hz
  have hz' : π z ∈ flatDomain Φ := ⟨mem_chart_source _ (π z), Φ.center_mem_source⟩
  have hflatC : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ complexCoordinatePlane n kC) :=
    fun hy hyΦ => (hflat hy hyΦ).1
  obtain ⟨j, hj, O, hO, hzO, W, hWs, hWeq, hℓ, -⟩ :=
    exists_monomialLocalInverse hπ hΦt hflatC hz'
  have hHi : ∀ i ∈ S, s i ≠ j ∧ W z (s i) = 0 := fun i hi => by
    have hflatH : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
        chartAt (ComplexModel n) (π z) y ∈ Φ.source →
          (y ∈ E.get i ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ coordSubspace {s i}) :=
      fun hy hyΦ => by
        rw [mem_coordSubspace_singleton]
        exact (hflat hy hyΦ).2.2 i (hzS i hi)
    have h := (mem_geoStrictTransform_iff_of_chart hπ hΦt hflatC hflatH hj hO hWs hWeq hℓ hzO).mp
      (hall i hi)
    exact ⟨fun hsj => h.1 (by simp [hsj]), mem_coordSubspace_singleton.mp h.2⟩
  have hWj : W z j = 0 := by
    have h := (hflatC (hWeq z hzO).1.1 (hWeq z hzO).1.2).mp hz
    rw [← (hWeq z hzO).2, monomial_mem_plane_iff hj] at h
    exact h
  have hpt : monomial kC j (W z) ∈ Φ.target := by
    rw [(hWeq z hzO).2]
    exact Φ.mapsTo_toFun (hWeq z hzO).1.2
  have hcont : Continuous fun ε : ℂ => monomial kC j (W z + ε • EuclideanSpace.single j (1 : ℂ)) :=
    (contDiff_monomial kC j).continuous.comp (by fun_prop)
  have htend : Tendsto (fun ε : ℂ => monomial kC j (W z + ε • EuclideanSpace.single j (1 : ℂ)))
      (𝓝 0) (𝓝 (monomial kC j (W z))) := by
    simpa using hcont.tendsto 0
  -- the curve `ε ↦ Φ⁻¹(σ_j(W z + ε e_j))`, read back in `X`, tends to `π z`
  have hγ : Tendsto (fun ε : ℂ => (chartAt (ComplexModel n) (π z)).symm
      (Φ.invFun (monomial kC j (W z + ε • EuclideanSpace.single j (1 : ℂ))))) (𝓝 0)
        (𝓝 (π z)) := by
    have h1 : Φ.invFun (monomial kC j (W z)) = chartAt (ComplexModel n) (π z) (π z) := by
      rw [(hWeq z hzO).2]
      exact Φ.left_inv _ (hWeq z hzO).1.2
    have h2 : ContinuousAt Φ.invFun (monomial kC j (W z)) :=
      Φ.invFun_holomorphic.continuousOn.continuousAt (Φ.isOpen_target.mem_nhds hpt)
    have h3 : ContinuousAt (chartAt (ComplexModel n) (π z)).symm
        (Φ.invFun (monomial kC j (W z))) := by
      rw [h1]
      exact (chartAt (ComplexModel n) (π z)).continuousAt_symm (mem_chart_target _ _)
    have h4 : Tendsto (fun ε : ℂ => (chartAt (ComplexModel n) (π z)).symm
        (Φ.invFun (monomial kC j (W z + ε • EuclideanSpace.single j (1 : ℂ))))) (𝓝 0)
          (𝓝 ((chartAt (ComplexModel n) (π z)).symm (Φ.invFun (monomial kC j (W z))))) :=
      (h3.comp h2).tendsto.comp htend
    rwa [h1, (chartAt (ComplexModel n) (π z)).left_inv (mem_chart_source _ _)] at h4
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp
    ((htend.eventually (Φ.isOpen_target.mem_nhds hpt)).and (hγ.eventually hC))
  have hε : dist ((r / 2 : ℝ) : ℂ) 0 < r := by
    rw [dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  obtain ⟨hwt, hyC'⟩ := hball hε
  have hsrc := Φ.mapsTo_invFun hwt
  have htgt := hΦt hsrc
  have hys := (chartAt (ComplexModel n) (π z)).map_target htgt
  have hey := (chartAt (ComplexModel n) (π z)).right_inv htgt
  have hyΦ : chartAt (ComplexModel n) (π z) ((chartAt (ComplexModel n) (π z)).symm
      (Φ.invFun (monomial kC j (W z + ((r / 2 : ℝ) : ℂ) • EuclideanSpace.single j (1 : ℂ)))))
        ∈ Φ.source := by
    rw [hey]; exact hsrc
  have hΦy : Φ.toFun (chartAt (ComplexModel n) (π z) ((chartAt (ComplexModel n) (π z)).symm
      (Φ.invFun (monomial kC j (W z + ((r / 2 : ℝ) : ℂ) • EuclideanSpace.single j (1 : ℂ)))))) =
      monomial kC j (W z + ((r / 2 : ℝ) : ℂ) • EuclideanSpace.single j (1 : ℂ)) := by
    rw [hey]; exact Φ.right_inv _ hwt
  have hyC : (chartAt (ComplexModel n) (π z)).symm
      (Φ.invFun (monomial kC j (W z + ((r / 2 : ℝ) : ℂ) • EuclideanSpace.single j (1 : ℂ))))
        ∈ C := by
    refine hyC' fun i hi => ?_
    refine ((hflat hys hyΦ).2.2 i (hzS i hi)).mpr ?_
    rw [hΦy]
    obtain ⟨hsj, hW0⟩ := hHi i hi
    simp [monomial_apply, hsj, hW0]
  have h := (hflatC hys hyΦ).mp hyC
  rw [hΦy, monomial_mem_plane_iff hj] at h
  simp [hWj] at h
  linarith

open Classical in
/-- **Blowing up the intersection of the members through a point lowers the count over it**: if
near `x = π z` the centre contains the intersection of all members through `x` (Step 1aa: near each
of its points the centre `H^s_α` is that intersection), then `z` lies on fewer strict transforms of
members than `x` lies on members. No global maximality is needed. -/
theorem boundaryCount_map_geoStrictTransform_lt_boundaryCount (hπ : IsBlowupAlong n C π)
    {E : List (Set X)} (hE : IsSNCDivisor n E) (hnc : HasNormalCrossings n C E) {z : Y}
    (hz : π z ∈ C)
    (hC : ∀ᶠ y in 𝓝 (π z), (∀ i : Fin E.length, π z ∈ E.get i → y ∈ E.get i) → y ∈ C) :
    boundaryCount (E.map (geoStrictTransform π C)) z < boundaryCount E (π z) := by
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin E.length),
      S = Finset.univ.filter fun i : Fin E.length => π z ∈ E.get i := ⟨_, rfl⟩
  have hcount : boundaryCount E (π z) = S.card := by rw [hS]; rfl
  have hsub : (Finset.univ.filter fun i : Fin E.length => z ∈ geoStrictTransform π C (E.get i)) =
      S.filter fun i => z ∈ geoStrictTransform π C (E.get i) := by
    ext i
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => ⟨geoStrictTransform_subset_preimage hπ.contMDiff.continuous
      (hE.1 _ (List.get_mem _ _)) h, h⟩, fun h => h.2⟩
  rw [boundaryCount_map, hsub, hcount]
  refine card_filter_mem_geoStrictTransform_lt hπ hE hnc S hz ?_
  filter_upwards [hC] with y hy hyS
  exact hy fun i hi => hyS i (by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hi⟩)

end Blowup

end Manifold

section Tower

open BlowupTowers

variable {X Y : CMfd.{u} n}

/-- The first `#E` members along a tower are closed: the original members, or strict transforms. -/
theorem isClosed_of_mem_take_E_transformAlong (𝔪 : MarkedIdeal n X)
    (hE : ∀ H ∈ 𝔪.E, IsClosed H) (T : BlowupTower X Y) :
    ∀ H ∈ (𝔪.transformAlong T).E.take 𝔪.E.length, IsClosed H := by
  cases T with
  | refl => simpa using hE
  | step T C π hπ =>
    intro H hH
    have hlen : 𝔪.E.length ≤ ((𝔪.transformAlong T).E.map (geoStrictTransform π C)).length := by
      rw [List.length_map, MarkedIdeal.length_E_transformAlong]; omega
    rw [MarkedIdeal.transformAlong_step, MarkedIdeal.transform_E,
      List.take_append_of_le_length hlen] at hH
    obtain ⟨H₀, -, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take hH)
    exact isClosed_closure

open Classical in
/-- **The boundary count does not increase along a tower**: a point of the last space lies on at
most as many strict transforms of the original members (the first `#E` members of the transformed
divisor; the exceptional divisors are not counted) as its image in `X` lies on members. -/
theorem boundaryCount_take_E_transformAlong_le (𝔪 : MarkedIdeal n X)
    (hE : ∀ H ∈ 𝔪.E, IsClosed H) (T : BlowupTower X Y) (z : Y) :
    boundaryCount ((𝔪.transformAlong T).E.take 𝔪.E.length) z ≤ boundaryCount 𝔪.E (T.proj z) := by
  induction T with
  | refl => simp
  | step T C π hπ ih =>
    have hlen : 𝔪.E.length ≤ ((𝔪.transformAlong T).E.map (geoStrictTransform π C)).length := by
      rw [List.length_map, MarkedIdeal.length_E_transformAlong]; omega
    rw [MarkedIdeal.transformAlong_step, MarkedIdeal.transform_E,
      List.take_append_of_le_length hlen, ← List.map_take, BlowupTower.proj_step,
      Function.comp_apply]
    exact (boundaryCount_map_geoStrictTransform_le hπ.contMDiff.continuous
      (isClosed_of_mem_take_E_transformAlong 𝔪 hE T) z).trans (ih (π z))

/-- `isClosed_of_mem_take_E_transformAlong` for `geoTransformAlong`. -/
theorem isClosed_of_mem_take_E_geoTransformAlong (𝔪 : MarkedIdeal n X)
    (hE : ∀ H ∈ 𝔪.E, IsClosed H) (T : BlowupTower X Y) :
    ∀ H ∈ (𝔪.geoTransformAlong T).E.take 𝔪.E.length, IsClosed H := by
  cases T with
  | refl => simpa using hE
  | step T C π hπ =>
    intro H hH
    have hlen :
        𝔪.E.length ≤ ((𝔪.geoTransformAlong T).E.map (geoStrictTransform π C)).length := by
      rw [List.length_map, MarkedIdeal.length_E_geoTransformAlong]; omega
    rw [MarkedIdeal.geoTransformAlong_step, MarkedIdeal.geoTransform_E,
      List.take_append_of_le_length hlen] at hH
    obtain ⟨H₀, -, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take hH)
    exact isClosed_closure

open Classical in
/-- `boundaryCount_take_E_transformAlong_le` for `geoTransformAlong`. -/
theorem boundaryCount_take_E_geoTransformAlong_le (𝔪 : MarkedIdeal n X)
    (hE : ∀ H ∈ 𝔪.E, IsClosed H) (T : BlowupTower X Y) (z : Y) :
    boundaryCount ((𝔪.geoTransformAlong T).E.take 𝔪.E.length) z ≤
      boundaryCount 𝔪.E (T.proj z) := by
  induction T with
  | refl => simp
  | step T C π hπ ih =>
    have hlen :
        𝔪.E.length ≤ ((𝔪.geoTransformAlong T).E.map (geoStrictTransform π C)).length := by
      rw [List.length_map, MarkedIdeal.length_E_geoTransformAlong]; omega
    rw [MarkedIdeal.geoTransformAlong_step, MarkedIdeal.geoTransform_E,
      List.take_append_of_le_length hlen, ← List.map_take, BlowupTower.proj_step,
      Function.comp_apply]
    exact (boundaryCount_map_geoStrictTransform_le hπ.contMDiff.continuous
      (isClosed_of_mem_take_E_geoTransformAlong 𝔪 hE T) z).trans (ih (π z))

end Tower

end

end Hironaka.BoundaryCount
