import Hironaka.Invariant.CodimOnePartTowerAlong
import Hironaka.Invariant.BoundaryCountAlong
import Hironaka.MarkedIdeal.CoefficientIdealAlongRestriction
import Hironaka.Blowup.NormalCrossingsComparison

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Step 1aa inside a submanifold: the value set of `(s, ∞)`

Hironaka phase H2 (TN3), for TN-CLASSICAL's Step 1a inside `N` (`hir:maximal-order-step`; claim
I-0977 C-0104).  Blueprint `bcalc:member-locus-def`, `bcalc:member-locus-canonical`,
`bcalc:member-locus-level`, `bcalc:member-restriction-nonzero`, `bcalc:member-locus-centre` (chapter
`blowup-calculus.tex`; the last appended in round r3, claim I-0977 C-0106).  Sources: Włodarczyk 2005
(`wlodarczyk05-hironaka`), Step 1a of Proposition `pr:resol`; Włodarczyk 2009
(`wlodarczyk09-analytic-resolution`) Step 1aa (printed p. 55).

In Step 1a of the algorithm for a marked ideal `(M, N, E, 𝔞, d)` of maximal order along `N`, the points
of an intersection `N ∩ H_S` of members contained in the cosupport get the value `(s, ∞)`.  Włodarczyk
intersects irreducible components; the invariant must be local (`hir:centre-function` (5)), so here a
point `x` belongs to the **member locus** `memberInterLocus N E S` of a set `S` (the cosupport) if
`x ∈ S` and, near `x`, every point of `N` on all the members of `E` through `x` lies in `S`: the
intersection `N ∩ H_{S(x)}` of `N` with the members through `x` is contained in `S` near `x`.  At a stage
`T` of the algorithm it is taken with `N_T`, the strict transforms `E_T.take #E` of the original members
and the cosupport of the transform.

## Main results

* `mem_memberInterLocus_iff` (membership through the members, not their indices),
  `mem_memberInterLocus_map_congr` (locality: only the germs at `x` of `N`, `S` and the members matter),
  `mem_memberInterLocus_preimage_iff` (preimages under a map `f` with `map f (𝓝 z) = 𝓝 (f z)`), and
  `map_nhds_eq_of_notMem` (a blowup is such a map off its centre);
* `mem_memberInterLocus_geoTransform_iff`: off the centre of a blowup the member locus corresponds;
  along towers: `mem_memberInterLocus_geoTransformAlong_step_iff` (properties (3) "equal otherwise" and
  (4)), `memberInterLocus_geoTransformAlong_transport` (6), `memberInterLocus_geoTransformAlong_restrict`
  (5), `memberInterLocus_geoTransformAlong_of_restrictEquiv`, `memberInterLocus_geoTransformAlong_of_wEquiv`
  (7);
* the level-`s₀` part `C = L ∩ {s = s₀}` (the centre of Step 1aa): `eventually_mem_memberInterLocus_level` (near
  each of its points it contains `N ∩ H_{S(x)}`); `memberInterLocus_level_geoTransform_eq_empty` (after the
  blowup along `C`, admissible, the level-`s₀` part is empty: the count drops over `C`);
  `memberInterLocus_level_geoTransformAlong_subset` (along every multiple test blow-up the level-`s₀` part lies
  over the closure of the original one), `memberInterLocus_level_geoTransformAlong_eq_empty`,
  `memberInterLocus_level_geoTransformAlong_append_eq_empty` (so after Step 1aa it stays empty);
  tools `boundaryCount_eq_of_forall_iff`, `forall_iff_of_forall_imp_of_boundaryCount_le`, `strictAlong_append`,
  `strictAlong_inter_forall_mem`;
* `isAdmissibleCentre_memberInterLocus_level`: at the maximal level (`s ≤ s₀` on the cosupport, `d ≥ 1`, `0 < n`)
  the level-`s₀` part is an admissible centre -- closed by the filling lemma on `N ∩ H_{S(x)}`, near each of its
  points equal to `N ∩ H_{S(x)}` (`eventually_mem_level_iff`); tool `setOf_forall_mem_eq_memberInter_of_mem`;
* `isNonzeroAlongAt_of_notMem_memberInterLocus`, `isNonzeroAlongAt_coeffMarkedAlong_of_notMem_memberInterLocus`:
  off the member locus, the restriction of the coefficient ideal along `N` to `N ∩ H_{S(y)}` is nonzero
  near `y` (the hypothesis of `hir:centre-function` for the restricted marked ideals of Step 1ab).

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.MemberInterLocusAlong

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.HomogenizedGlueingTower Hironaka.MarkedIdealRestrictOpen
  Hironaka.MarkedIdealBiholomorphism Hironaka.MarkedIdealTowerTransport
  Hironaka.CodimOnePartCanonical Hironaka.GermIdealOrder
  Hironaka.HomogenizedIdealAlong Hironaka.BoundaryCount
  Hironaka.DivisorExponentAlong Hironaka.CoefficientIdealRestriction
  Hironaka.MarkedIdealEquivalence Hironaka.GiraudAlong
  Hironaka.BlowupStrictSubmanifold Hironaka.MemberInterTowerAlong
  Hironaka.CodimOnePartTowerAlong

noncomputable section

variable {n : ℕ}

/-! ### The member locus -/

section General

variable {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y]

/-- **The member locus** of `S` along `N` and `E` (Step 1aa's value set `(s, ∞)` for `S` the cosupport):
the points `x ∈ S` near which every point of `N` lying on all the members of `E` through `x` lies in `S`,
i.e. `N ∩ H_{S(x)} ⊆ S` near `x`. -/
def memberInterLocus (N : Set X) (E : List (Set X)) (S : Set X) : Set X :=
  {x | x ∈ S ∧ ∀ᶠ y in 𝓝 x, y ∈ N → (∀ i : Fin E.length, x ∈ E.get i → y ∈ E.get i) → y ∈ S}

/-- Quantifying over the indices of a list is quantifying over its members. -/
theorem forall_get_iff {E : List (Set X)} {P : Set X → Prop} :
    (∀ i : Fin E.length, P (E.get i)) ↔ ∀ H ∈ E, P H :=
  ⟨fun h H hH => by obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hH; exact h i,
    fun h i => h _ (List.get_mem _ _)⟩

/-- **Membership through the members**: `x ∈ memberInterLocus N E S` iff `x ∈ S` and near `x` every
point of `N` lying on every member of `E` through `x` lies in `S`. -/
theorem mem_memberInterLocus_iff {N : Set X} {E : List (Set X)} {S : Set X} {x : X} :
    x ∈ memberInterLocus N E S ↔
      x ∈ S ∧ ∀ᶠ y in 𝓝 x, y ∈ N → (∀ H ∈ E, x ∈ H → y ∈ H) → y ∈ S := by
  refine and_congr Iff.rfl (eventually_congr (Eventually.of_forall fun y => ?_))
  exact imp_congr_right fun _ => imp_congr_left (forall_get_iff (P := fun H => x ∈ H → y ∈ H))

theorem memberInterLocus_subset (N : Set X) (E : List (Set X)) (S : Set X) :
    memberInterLocus N E S ⊆ S := fun _ h => h.1

open Classical in
/-- The intersection of the members through `y` in index form. -/
theorem setOf_forall_mem_eq_memberInter (E : List (Set X)) (y : X) :
    {z | ∀ H ∈ E, y ∈ H → z ∈ H} = memberInter E (Finset.univ.filter fun i => y ∈ E.get i) := by
  ext z
  show (∀ H ∈ E, y ∈ H → z ∈ H) ↔ ∀ i ∈ Finset.univ.filter (fun i => y ∈ E.get i), z ∈ E.get i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact (forall_get_iff (P := fun H => y ∈ H → z ∈ H)).symm

/-- **The member locus is local**: if near `x` the sets `N'`, `S'` agree with `N`, `S`, and for every
member `H` of `E` the set `g H` agrees with `g' H`, then `x` is in the member locus of `S'` along `N'` and
`E.map g` iff it is in that of `S` along `N` and `E.map g'` (`E` a list in any type). -/
theorem mem_memberInterLocus_map_congr {α : Type*} {N N' S S' : Set X} {E : List α} {g g' : α → Set X}
    {x : X} (hN : ∀ᶠ y in 𝓝 x, y ∈ N' ↔ y ∈ N) (hS : ∀ᶠ y in 𝓝 x, y ∈ S' ↔ y ∈ S)
    (hE : ∀ H ∈ E, ∀ᶠ y in 𝓝 x, y ∈ g H ↔ y ∈ g' H) :
    x ∈ memberInterLocus N' (E.map g) S' ↔ x ∈ memberInterLocus N (E.map g') S := by
  rw [mem_memberInterLocus_iff, mem_memberInterLocus_iff]
  have hE' : ∀ᶠ y in 𝓝 x, ∀ H ∈ E, (y ∈ g H ↔ y ∈ g' H) :=
    (eventually_all_finite (List.finite_toSet E)).mpr hE
  have hx : ∀ H ∈ E, (x ∈ g H ↔ x ∈ g' H) := fun H hH => (hE H hH).self_of_nhds
  refine and_congr hS.self_of_nhds (eventually_congr ?_)
  filter_upwards [hN, hS, hE'] with y hyN hyS hyE
  simp only [List.forall_mem_map]
  rw [hyN, hyS]
  constructor
  · intro h hyN' hall
    exact h hyN' fun H hH hxH => (hyE H hH).mpr (hall H hH ((hx H hH).mp hxH))
  · intro h hyN' hall
    exact h hyN' fun H hH hxH => (hyE H hH).mp (hall H hH ((hx H hH).mpr hxH))

/-- The locality of `mem_memberInterLocus_map_congr` with `g' = id`. -/
theorem mem_memberInterLocus_map_congr_id {N N' S S' : Set X} {E : List (Set X)} {g : Set X → Set X}
    {x : X} (hN : ∀ᶠ y in 𝓝 x, y ∈ N' ↔ y ∈ N) (hS : ∀ᶠ y in 𝓝 x, y ∈ S' ↔ y ∈ S)
    (hE : ∀ H ∈ E, ∀ᶠ y in 𝓝 x, y ∈ g H ↔ y ∈ H) :
    x ∈ memberInterLocus N' (E.map g) S' ↔ x ∈ memberInterLocus N E S := by
  have h := mem_memberInterLocus_map_congr (g' := id) hN hS hE
  rwa [List.map_id] at h

/-- **Preimages**: for a map `f` with `map f (𝓝 z) = 𝓝 (f z)` (a homeomorphism, an open embedding, a
blowup off its centre), `z` is in the member locus of `f⁻¹ S` along `f⁻¹ N` and the preimages of the
members iff `f z` is in that of `S`. -/
theorem mem_memberInterLocus_preimage_iff (f : Y → X) {z : Y} (hf : Filter.map f (𝓝 z) = 𝓝 (f z))
    (N : Set X) (E : List (Set X)) (S : Set X) :
    z ∈ memberInterLocus (f ⁻¹' N) (E.map (f ⁻¹' ·)) (f ⁻¹' S) ↔ f z ∈ memberInterLocus N E S := by
  rw [mem_memberInterLocus_iff, mem_memberInterLocus_iff]
  refine and_congr Iff.rfl ?_
  simp only [List.forall_mem_map, mem_preimage]
  rw [← hf, eventually_map]

/-- The set form of `mem_memberInterLocus_preimage_iff`. -/
theorem memberInterLocus_preimage (f : Y → X) (hf : ∀ z, Filter.map f (𝓝 z) = 𝓝 (f z))
    (N : Set X) (E : List (Set X)) (S : Set X) :
    memberInterLocus (f ⁻¹' N) (E.map (f ⁻¹' ·)) (f ⁻¹' S) = f ⁻¹' memberInterLocus N E S :=
  Set.ext fun z => mem_memberInterLocus_preimage_iff f (hf z) N E S

/-- **Members not through `x` do not matter.** -/
theorem mem_memberInterLocus_append_iff {N S : Set X} {E E' : List (Set X)} {x : X}
    (hE' : ∀ H ∈ E', x ∉ H) :
    x ∈ memberInterLocus N (E ++ E') S ↔ x ∈ memberInterLocus N E S := by
  rw [mem_memberInterLocus_iff, mem_memberInterLocus_iff]
  refine and_congr Iff.rfl (eventually_congr (Eventually.of_forall fun y => ?_))
  refine imp_congr_right fun _ => imp_congr_left ?_
  simp only [List.mem_append]
  exact ⟨fun h H hH => h H (Or.inl hH), fun h H hH hx => hH.elim (fun hH => h H hH hx)
    fun hH => absurd hx (hE' H hH)⟩

open Classical in
/-- **Equal counts** for points on the same members. -/
theorem boundaryCount_eq_of_forall_iff {E : List (Set X)} {y z : X} (h : ∀ H ∈ E, y ∈ H ↔ z ∈ H) :
    boundaryCount E y = boundaryCount E z := by
  unfold boundaryCount
  exact congrArg Finset.card (Finset.filter_congr fun i _ => h _ (List.get_mem _ _))

open Classical in
/-- **A point on all the members through `z` with no larger count lies on the same members.** -/
theorem forall_iff_of_forall_imp_of_boundaryCount_le {E : List (Set X)} {y z : X}
    (himp : ∀ H ∈ E, z ∈ H → y ∈ H) (hle : boundaryCount E y ≤ boundaryCount E z) :
    ∀ H ∈ E, y ∈ H ↔ z ∈ H := by
  unfold boundaryCount at hle
  have hsub : (Finset.univ.filter fun i : Fin E.length => z ∈ E.get i) ⊆
      (Finset.univ.filter fun i : Fin E.length => y ∈ E.get i) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact himp _ (List.get_mem _ _) hi
  have heq := Finset.eq_of_subset_of_card_le hsub hle
  intro H hH
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hH
  have h := Finset.ext_iff.mp heq i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
  exact h.symm

end General

/-! ### Off the centre of a blowup -/

section OffCentre

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {C : Set X} {π : Y → X}

/-- **A blowup is a local homeomorphism off its centre**: `map π (𝓝 z) = 𝓝 (π z)` for `π z ∉ C` (the
holomorphic section of `π` over `X \ C`, `BlowupIsomorphismOff.exists_section_compl`). -/
theorem map_nhds_eq_of_notMem (hπ : IsBlowupAlong n C π) {z : Y} (hz : π z ∉ C) :
    Filter.map π (𝓝 z) = 𝓝 (π z) := by
  obtain ⟨s, hs, hsπ, hsec⟩ := BlowupIsomorphismOff.exists_section_compl hπ
  refine le_antisymm hπ.contMDiff.continuous.continuousAt fun t ht => ?_
  have hsp := hsec z hz
  have h1 : s ⁻¹' (π ⁻¹' t) ∈ 𝓝 (⟨π z, hz⟩ : (⟨Cᶜ, hπ.1.1.isOpen_compl⟩ : Opens X)) :=
    hs.continuous.continuousAt.preimage_mem_nhds (by rw [hsp]; exact ht)
  have h2 : (Subtype.val : (⟨Cᶜ, hπ.1.1.isOpen_compl⟩ : Opens X) → X) '' (s ⁻¹' (π ⁻¹' t)) ∈
      𝓝 (π z) := by
    have h3 := image_mem_map (m := (Subtype.val : (⟨Cᶜ, hπ.1.1.isOpen_compl⟩ : Opens X) → X)) h1
    rw [Topology.IsOpenEmbedding.map_nhds_eq (Opens.isOpen _).isOpenEmbedding_subtypeVal] at h3
    exact h3
  refine mem_of_superset h2 ?_
  rintro _ ⟨q, hq, rfl⟩
  have hq' : π (s q) = q := congrFun hsπ q
  rw [← hq']
  exact hq

/-- **Off the centre the member locus does not change**: for the blowup `π` along `C`, a list `E₀` of
closed sets (the members counted) and `π z ∉ C`, `z` is in the member locus of the cosupport of the
transform along `N'` and the strict transforms of `E₀` iff `π z` is in that of `𝔪` (`N` closed, ideal of
holomorphic germs). -/
theorem mem_memberInterLocus_geoTransform_iff (𝔪 : MarkedIdeal n X) (hN : IsClosed 𝔪.N)
    (h𝔞 : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x) (hπ : IsBlowupAlong n C π)
    {E₀ : List (Set X)} (hE₀ : ∀ H ∈ E₀, IsClosed H) {z : Y} (hz : π z ∉ C) :
    z ∈ memberInterLocus (𝔪.geoTransform C π).N (E₀.map (geoStrictTransform π C))
        (𝔪.geoTransform C π).cosupp ↔
      π z ∈ memberInterLocus 𝔪.N E₀ 𝔪.cosupp := by
  rw [← mem_memberInterLocus_preimage_iff π (map_nhds_eq_of_notMem hπ hz) 𝔪.N E₀ 𝔪.cosupp]
  refine mem_memberInterLocus_map_congr ?_ ?_ ?_
  · exact TransformOffCentre.eventually_mem_geoStrictTransform_iff hN hπ.1.1 hπ.contMDiff.continuous hz
  · filter_upwards [(hπ.1.1.isOpen_compl.preimage hπ.contMDiff.continuous).mem_nhds hz] with y hy
    exact TransformOffCentre.mem_cosupp_geoTransform_iff 𝔪 hN h𝔞 hπ hy
  · intro H hH
    exact TransformOffCentre.eventually_mem_geoStrictTransform_iff (hE₀ H hH) hπ.1.1
      hπ.contMDiff.continuous hz

/-- **A blowup along `∅` pulls the member locus back** (property (4), empty steps). -/
theorem memberInterLocus_geoTransform_empty (𝔪 : MarkedIdeal n X) (hN : IsClosed 𝔪.N)
    (h𝔞 : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x) (hπ : IsBlowupAlong n ∅ π)
    {E₀ : List (Set X)} (hE₀ : ∀ H ∈ E₀, IsClosed H) :
    memberInterLocus (𝔪.geoTransform ∅ π).N (E₀.map (geoStrictTransform π ∅)) (𝔪.geoTransform ∅ π).cosupp =
      π ⁻¹' memberInterLocus 𝔪.N E₀ 𝔪.cosupp :=
  Set.ext fun _ => mem_memberInterLocus_geoTransform_iff 𝔪 hN h𝔞 hπ hE₀ (Set.notMem_empty _)

end OffCentre

/-! ### Along towers -/

section Tower

variable {X X' : CMfd.{u} n} {𝔪 : MarkedIdeal n X}

/-- **Off the centre of the last blowup of a tower the member locus does not change** (properties (3)
"equal otherwise" and (4)): along a multiple test blow-up `T` followed by the blowup `π` along `C`, with
the strict transforms of the original members, for `π z ∉ C`. -/
theorem mem_memberInterLocus_geoTransformAlong_step_iff (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) (hE : ∀ H ∈ 𝔪.E, IsClosed H) {Y Z : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower 𝔪 T) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π) {z : Z}
    (hz : π z ∉ C) :
    z ∈ memberInterLocus (geoTransformAlong 𝔪 (.step T C π hπ)).N
        ((geoTransformAlong 𝔪 (.step T C π hπ)).E.take 𝔪.E.length)
        (geoTransformAlong 𝔪 (.step T C π hπ)).cosupp ↔
      π z ∈ memberInterLocus (geoTransformAlong 𝔪 T).N ((geoTransformAlong 𝔪 T).E.take 𝔪.E.length)
        (geoTransformAlong 𝔪 T).cosupp := by
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T hT
  have hlen : 𝔪.E.length ≤ ((geoTransformAlong 𝔪 T).E.map (geoStrictTransform π C)).length := by
    rw [List.length_map, MarkedIdeal.length_E_geoTransformAlong]; omega
  rw [MarkedIdeal.geoTransformAlong_step, MarkedIdeal.geoTransform_E, List.take_append_of_le_length hlen,
    ← List.map_take]
  exact mem_memberInterLocus_geoTransform_iff (geoTransformAlong 𝔪 T) hNT.1
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcT hg) hπ
    (isClosed_of_mem_take_E_geoTransformAlong 𝔪 hE T) hz

/-- **The member locus along transported towers** (property (6)): along the transport of a tower `T`
by a biholomorphism `Φ : X' ≅ X`, the member locus of the transform of `Φ^*𝔪` is the preimage under the
last-stage biholomorphism of that of the transform of `𝔪`. -/
theorem memberInterLocus_geoTransformAlong_transport
    (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) (h𝔞 : 𝔪.ideal.IsCoherent) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) →
      memberInterLocus (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) (transport Φ T).tower).N
          ((geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) (transport Φ T).tower).E.take 𝔪.E.length)
          (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) (transport Φ T).tower).cosupp =
        (transport Φ T).back ⁻¹' memberInterLocus (geoTransformAlong 𝔪 T).N
          ((geoTransformAlong 𝔪 T).E.take 𝔪.E.length) (geoTransformAlong 𝔪 T).cosupp
  | _, .refl => by
      ext p
      change p ∈ memberInterLocus (Φ ⁻¹' 𝔪.N) ((𝔪.E.map (Φ ⁻¹' ·)).take 𝔪.E.length)
          (cosupport n (Φ ⁻¹' 𝔪.N) (GermIdeal.pullback (m := n) Φ 𝔪.ideal) 𝔪.d) ↔
        Φ p ∈ memberInterLocus 𝔪.N (𝔪.E.take 𝔪.E.length) (cosupport n 𝔪.N 𝔪.ideal 𝔪.d)
      rw [List.take_of_length_le (by rw [List.length_map]), List.take_of_length_le le_rfl,
        cosupport_pullback Φ
          (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg) 𝔪.d]
      exact mem_memberInterLocus_preimage_iff Φ (Φ.toHomeomorph.map_nhds_eq p) _ _ _
  | _, .step T C π hπ => by
      rw [geoTransformAlong_transport_step Φ h𝔞 T C π hπ]
      rfl

/-- **The member locus along restricted towers** (property (5)): along the restriction to an open `U`
of a multiple test blow-up `T`, the member locus of the transform of `𝔪|_U` is the trace on the open
preimage of `U` of that of the transform of `𝔪`. -/
theorem memberInterLocus_geoTransformAlong_restrict (U : Opens X) (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) :
    memberInterLocus (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (restrict U T)).N
        ((geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (restrict U T)).E.take
          𝔪.E.length)
        (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (restrict U T)).cosupp =
      ((↑) : openPreimage T U → Y) ⁻¹' memberInterLocus (geoTransformAlong 𝔪 T).N
        ((geoTransformAlong 𝔪 T).E.take 𝔪.E.length) (geoTransformAlong 𝔪 T).cosupp := by
  obtain ⟨-, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T hT
  rw [geoTransformAlong_restrict U hN h𝔞 T hT]
  have hc := cosupp_pullback_val (geoTransformAlong 𝔪 T)
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcT hg)
    (openPreimage T U)
  ext p
  change p ∈ memberInterLocus ((Subtype.val : openPreimage T U → Y) ⁻¹' (geoTransformAlong 𝔪 T).N)
      (((geoTransformAlong 𝔪 T).E.map ((Subtype.val : openPreimage T U → Y) ⁻¹' ·)).take 𝔪.E.length)
      (MarkedIdeal.pullback (Subtype.val : openPreimage T U → Y) (geoTransformAlong 𝔪 T)).cosupp ↔ _
  rw [hc, ← List.map_take]
  exact mem_memberInterLocus_preimage_iff Subtype.val
    ((openPreimage T U).isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq p) _ _ _

/-- **Restricted-equivalent marked ideals have the same member locus at every stage** (property (7);
closed `N`, coherent ideals). -/
theorem memberInterLocus_geoTransformAlong_of_restrictEquiv {𝔫 : MarkedIdeal n X}
    (h : MarkedIdealOperationsAlong.MarkedIdeal.RestrictEquiv 𝔪 𝔫) (hN : IsClosed 𝔪.N)
    (h𝔪 : 𝔪.ideal.IsCoherent) (h𝔫 : 𝔫.ideal.IsCoherent) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) →
      memberInterLocus (geoTransformAlong 𝔪 T).N ((geoTransformAlong 𝔪 T).E.take 𝔪.E.length)
          (geoTransformAlong 𝔪 T).cosupp =
        memberInterLocus (geoTransformAlong 𝔫 T).N ((geoTransformAlong 𝔫 T).E.take 𝔪.E.length)
          (geoTransformAlong 𝔫 T).cosupp
  | _, .refl => by
      change memberInterLocus 𝔪.N (𝔪.E.take 𝔪.E.length) 𝔪.cosupp =
        memberInterLocus 𝔫.N (𝔫.E.take 𝔪.E.length) 𝔫.cosupp
      rw [h.N_eq, h.E_eq, h.cosupp_eq]
  | _, .step T C π hπ => by
      rw [MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.geoTransformAlong_step_eq h hN h𝔪 h𝔫 T C π hπ]

/-- **Equivalent marked ideals with the same `N` have the same member locus along every multiple test
blow-up** (property (7) for the replacement of `𝔪` by `𝓒(𝓗(𝔪))`). -/
theorem memberInterLocus_geoTransformAlong_of_wEquiv {𝔫 : MarkedIdeal n X}
    (h : MarkedIdealEquivalence.MarkedIdeal.WEquiv 𝔪 𝔫) (hN : 𝔪.N = 𝔫.N) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) :
    memberInterLocus (geoTransformAlong 𝔪 T).N ((geoTransformAlong 𝔪 T).E.take 𝔪.E.length)
        (geoTransformAlong 𝔪 T).cosupp =
      memberInterLocus (geoTransformAlong 𝔫 T).N ((geoTransformAlong 𝔫 T).E.take 𝔪.E.length)
        (geoTransformAlong 𝔫 T).cosupp := by
  rw [N_geoTransformAlong, N_geoTransformAlong, hN, (h.2 T).2 hT,
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq h.1 T]

end Tower

/-! ### Level sets of the member locus: the 1aa centre and its persistence -/

section LevelStep

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {π : Y → X}

/-- **The level set of the member locus contains `N ∩ H_{S(x)}` near each of its points**: if
`x ∈ memberInterLocus N E S` with `s(x) = s₀` (members closed), then near `x` every point of `N` on all
the members through `x` is again in the member locus, with count `s₀`. -/
theorem eventually_mem_memberInterLocus_level {N S : Set X} {E : List (Set X)}
    (hE : ∀ H ∈ E, IsClosed H) {x : X} (hx : x ∈ memberInterLocus N E S) :
    ∀ᶠ y in 𝓝 x, y ∈ N → (∀ i : Fin E.length, x ∈ E.get i → y ∈ E.get i) →
      y ∈ memberInterLocus N E S ∧ boundaryCount E y = boundaryCount E x := by
  have hloc := (mem_memberInterLocus_iff.mp hx).2
  have havoid : ∀ᶠ y in 𝓝 x, ∀ H ∈ E, x ∉ H → y ∉ H :=
    (eventually_all_finite (List.finite_toSet E)).mpr fun H hH => by
      by_cases hxH : x ∈ H
      · exact Eventually.of_forall fun _ h => absurd hxH h
      · filter_upwards [(hE H hH).isOpen_compl.mem_nhds hxH] with y hy _
        exact hy
  filter_upwards [hloc.eventually_nhds, havoid] with y hy1 hy2 hyN hyE
  have hyE' : ∀ H ∈ E, x ∈ H → y ∈ H := (forall_get_iff (P := fun H => x ∈ H → y ∈ H)).mp hyE
  have hiff : ∀ H ∈ E, (y ∈ H ↔ x ∈ H) := fun H hH =>
    ⟨fun h => by_contra fun h' => hy2 H hH h' h, hyE' H hH⟩
  refine ⟨mem_memberInterLocus_iff.mpr ⟨hy1.self_of_nhds hyN hyE', ?_⟩,
    boundaryCount_eq_of_forall_iff hiff⟩
  filter_upwards [hy1] with w hw hwN hwE
  exact hw hwN fun H hH hxH => hwE H hH ((hiff H hH).mpr hxH)

/-- **Blowing up the level-`s₀` part of the member locus empties it** (Step 1aa inside `N`).  Let `𝔪` be
well formed, `E₀` a sublist of its divisor (the members counted), `C` the set of points of the member locus
of the cosupport along `N` and `E₀` at which `s = s₀`, assumed an admissible centre, and `π` the blowup
along `C`.  Then no point of the transform has `s' = s₀` and lies in the member locus of the transformed
cosupport along `N'` and the strict transforms of `E₀`: over `C` the count drops
(`BoundaryCountAlong.boundaryCount_map_geoStrictTransform_lt_boundaryCount_along`, as `C ⊇ N ∩ H_{S(x)}` near
`x`), and off `C` the member locus and the count correspond. -/
theorem memberInterLocus_level_geoTransform_eq_empty (𝔪 : MarkedIdeal n X) (h𝔪 : 𝔪.IsWellFormed)
    {E₀ : List (Set X)} (hE₀ : E₀.Sublist 𝔪.E) (s₀ : ℕ)
    (hπ : IsBlowupAlong n (memberInterLocus 𝔪.N E₀ 𝔪.cosupp ∩ {x | boundaryCount E₀ x = s₀}) π)
    (hC : 𝔪.IsAdmissibleCentre (memberInterLocus 𝔪.N E₀ 𝔪.cosupp ∩ {x | boundaryCount E₀ x = s₀})) :
    memberInterLocus (𝔪.geoTransform (memberInterLocus 𝔪.N E₀ 𝔪.cosupp ∩ {x | boundaryCount E₀ x = s₀}) π).N
        (E₀.map (geoStrictTransform π (memberInterLocus 𝔪.N E₀ 𝔪.cosupp ∩ {x | boundaryCount E₀ x = s₀})))
        (𝔪.geoTransform (memberInterLocus 𝔪.N E₀ 𝔪.cosupp ∩ {x | boundaryCount E₀ x = s₀}) π).cosupp ∩
      {z | boundaryCount (E₀.map (geoStrictTransform π
        (memberInterLocus 𝔪.N E₀ 𝔪.cosupp ∩ {x | boundaryCount E₀ x = s₀}))) z = s₀} = ∅ := by
  set C := memberInterLocus 𝔪.N E₀ 𝔪.cosupp ∩ {x | boundaryCount E₀ x = s₀} with hCdef
  have hE₀c : ∀ H ∈ E₀, IsClosed H := fun H hH => h𝔪.isSNCDivisor.1 H (hE₀.subset hH)
  have hhol : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔪.isCoherent hg
  refine eq_empty_iff_forall_notMem.mpr fun z ⟨hzL, hzs⟩ => ?_
  have hzs' : boundaryCount (E₀.map (geoStrictTransform π C)) z = s₀ := hzs
  by_cases hzC : π z ∈ C
  · have hzN : z ∈ geoStrictTransform π C 𝔪.N := (𝔪.geoTransform C π).cosupp_subset_N hzL.1
    obtain ⟨hxL, hxs⟩ := hzC
    have hxs' : boundaryCount E₀ (π z) = s₀ := hxs
    have hCloc : ∀ᶠ y in 𝓝 (π z), y ∈ 𝔪.N →
        (∀ i : Fin E₀.length, π z ∈ E₀.get i → y ∈ E₀.get i) → y ∈ C := by
      filter_upwards [eventually_mem_memberInterLocus_level hE₀c hxL] with y hy hyN hyE
      obtain ⟨hyL, hyc⟩ := hy hyN hyE
      exact ⟨hyL, show boundaryCount E₀ y = s₀ by rw [hyc, hxs']⟩
    have hlt := BoundaryCountAlong.boundaryCount_map_geoStrictTransform_lt_boundaryCount_along hπ
      hC.subset_N (NormalCrossingsComparison.isSNCDivisor_of_sublist h𝔪.isSNCDivisor hE₀)
      (NormalCrossingsComparison.isTransverse_of_forall_mem h𝔪.isTransverse fun _ hH => hE₀.subset hH)
      (NormalCrossingsComparison.hasNormalCrossings_of_forall_mem hC.2.2 fun _ hH => hE₀.subset hH)
      ⟨hxL, hxs⟩ hzN hCloc
    omega
  · have h1 := (mem_memberInterLocus_geoTransform_iff 𝔪 h𝔪.isClosedSubmanifold_N.1 hhol hπ hE₀c hzC).mp hzL
    have h2 := CodimOnePartCanonical.boundaryCount_map_geoStrictTransform_of_notMem hπ.1.1
      hπ.contMDiff.continuous hE₀c hzC
    exact hzC ⟨h1, show boundaryCount E₀ (π z) = s₀ by rw [← h2]; exact hzs'⟩

end LevelStep

section LevelTower

variable {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X)

/-- **Strict transforms along concatenated towers compose.** -/
theorem strictAlong_append {Y : CMfd.{u} n} (T : BlowupTower X Y) (A : Set X) :
    {Z : CMfd.{u} n} → (S : BlowupTower Y Z) → strictAlong (T.append S) A = strictAlong S (strictAlong T A)
  | _, .refl => rfl
  | _, .step S C π hπ => by
      rw [BlowupTower.append_step, strictAlong_step, strictAlong_step, strictAlong_append T A S]

/-- **Strict transforms of intersections of members** (index-free form of
`MemberInterTowerAlong.strictAlong_inter_memberInter`): for `𝔪` well formed, a list `E₀` of members of
`𝔪.E`, a property `P` of members and a multiple test blow-up `T`, the strict transform of the intersection
of `N` with the members of `E₀` satisfying `P` is the intersection of `N_T` with their strict transforms. -/
theorem strictAlong_inter_forall_mem (h𝔪 : 𝔪.IsWellFormed) {E₀ : List (Set X)}
    (hE₀ : ∀ H ∈ E₀, H ∈ 𝔪.E) (P : Set X → Prop) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower 𝔪 T) :
    strictAlong T (𝔪.N ∩ {w | ∀ H ∈ E₀, P H → w ∈ H}) =
      (geoTransformAlong 𝔪 T).N ∩ {w | ∀ H ∈ E₀, P H → w ∈ strictAlong T H} := by
  classical
  set S : Finset (Fin 𝔪.E.length) := Finset.univ.filter fun i => 𝔪.E.get i ∈ E₀ ∧ P (𝔪.E.get i)
    with hS
  have key : ∀ {W : Type u} (f : Set X → Set W) (w : W),
      (∀ H ∈ E₀, P H → w ∈ f H) ↔ ∀ i ∈ S, w ∈ f (𝔪.E.get i) := by
    intro W f w
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro h i ⟨hi, hP⟩
      exact h _ hi hP
    · intro h H hH hP
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp (hE₀ H hH)
      exact h i ⟨hH, hP⟩
  have e1 : 𝔪.N ∩ {w | ∀ H ∈ E₀, P H → w ∈ H} = 𝔪.N ∩ memberInter 𝔪.E S := by
    ext w
    exact and_congr Iff.rfl (key (fun H => H) w)
  rw [e1, strictAlong_inter_memberInter 𝔪 h𝔪 S T hT]
  ext w
  exact and_congr Iff.rfl (key (strictAlong T) w).symm

/-- **Along a multiple test blow-up the level-`s₀` part of the member locus lies over the closure of the
original one.**  For `𝔪` well formed, a list `E₀` of members of `𝔪.E` (the members counted) and a multiple
test blow-up `T`, every point of `N_T` in the member locus of the cosupport along `N_T` and the strict
transforms of `E₀`, with `s_T = s₀`, lies over the closure of the set of points of the original member locus
with `s = s₀`.  (Near such a point `z` the member locus contains `N_T ∩ H_{S(z),T}`, the strict transform
of `N ∩ H_{S(z)}` (`strictAlong_inter_forall_mem`), which is the closure of the preimage of its strict
transform before the last blowup off the centre; at the points `y` of that preimage near `z`, `y` lies on
the same members as `z` (the count is upper semicontinuous), so `y` is in the level-`s₀` member locus, and
off the centre it corresponds.) -/
theorem memberInterLocus_level_geoTransformAlong_subset (h𝔪 : 𝔪.IsWellFormed) {E₀ : List (Set X)}
    (hE₀ : ∀ H ∈ E₀, H ∈ 𝔪.E) (s₀ : ℕ) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower 𝔪 T →
      memberInterLocus (geoTransformAlong 𝔪 T).N (E₀.map (strictAlong T)) (geoTransformAlong 𝔪 T).cosupp ∩
          {z | boundaryCount (E₀.map (strictAlong T)) z = s₀} ⊆
        T.proj ⁻¹' closure (memberInterLocus 𝔪.N E₀ 𝔪.cosupp ∩ {x | boundaryCount E₀ x = s₀})
  | _, .refl, _ => by
      intro x hx
      have hm : E₀.map (strictAlong (BlowupTower.refl : BlowupTower X X)) = E₀ := List.map_id' E₀
      rw [hm] at hx
      exact subset_closure hx
  | _, .step T C π hπ, hT => by
      intro z ⟨hzL, hzs⟩
      obtain ⟨hT0, -⟩ := (isGeoTestTower_step_iff 𝔪 T C π hπ).mp hT
      set T' : BlowupTower X _ := .step T C π hπ with hT'
      have hN := h𝔪.isClosedSubmanifold_N
      have h𝔞 := h𝔪.isCoherent
      obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T hT0
      have hE₀c : ∀ H ∈ E₀, IsClosed H := fun H hH => h𝔪.isSNCDivisor.1 H (hE₀ H hH)
      have hETc : ∀ H ∈ E₀.map (strictAlong T), IsClosed H := by
        rw [List.forall_mem_map]
        exact fun H hH => isClosed_strictAlong T (hE₀c H hH)
      have hET'c : ∀ H ∈ E₀.map (strictAlong T'), IsClosed H := by
        rw [List.forall_mem_map]
        exact fun H hH => isClosed_strictAlong T' (hE₀c H hH)
      have hmap : E₀.map (strictAlong T') = (E₀.map (strictAlong T)).map (geoStrictTransform π C) := by
        rw [List.map_map]
        rfl
      have hcl : IsClosed (T'.proj ⁻¹'
          closure (memberInterLocus 𝔪.N E₀ 𝔪.cosupp ∩ {x | boundaryCount E₀ x = s₀})) :=
        isClosed_closure.preimage T'.contMDiff_proj.continuous
      rw [← hcl.closure_eq, mem_closure_iff_nhds]
      intro t ht
      set P : Set X → Prop := fun H => z ∈ strictAlong T' H with hP
      have hA := strictAlong_inter_forall_mem 𝔪 h𝔪 hE₀ P T' hT
      have hzN : z ∈ (geoTransformAlong 𝔪 T').N := (geoTransformAlong 𝔪 T').cosupp_subset_N hzL.1
      have hzA : z ∈ strictAlong T' (𝔪.N ∩ {w | ∀ H ∈ E₀, P H → w ∈ H}) := by
        rw [hA]
        exact ⟨hzN, fun H _ hPH => hPH⟩
      have hzA' : z ∈ closure (π ⁻¹' (strictAlong T (𝔪.N ∩ {w | ∀ H ∈ E₀, P H → w ∈ H}) \ C)) := hzA
      have hloc := (mem_memberInterLocus_iff.mp hzL).2
      have hle := eventually_boundaryCount_le hET'c z
      obtain ⟨y, ⟨⟨hyt, hyloc⟩, hyle⟩, hyA, hyC⟩ :=
        mem_closure_iff_nhds.mp hzA' _ (inter_mem (inter_mem ht hloc.eventually_nhds) hle)
      have hyA' : y ∈ strictAlong T' (𝔪.N ∩ {w | ∀ H ∈ E₀, P H → w ∈ H}) := subset_closure ⟨hyA, hyC⟩
      rw [hA] at hyA'
      obtain ⟨hyN, hyE⟩ := hyA'
      have himp : ∀ H ∈ E₀.map (strictAlong T'), z ∈ H → y ∈ H := by
        rw [List.forall_mem_map]
        exact fun H hH hzH => hyE H hH hzH
      have hiff := forall_iff_of_forall_imp_of_boundaryCount_le himp hyle
      have hyL : y ∈ memberInterLocus (geoTransformAlong 𝔪 T').N (E₀.map (strictAlong T'))
          (geoTransformAlong 𝔪 T').cosupp := by
        refine mem_memberInterLocus_iff.mpr ⟨hyloc.self_of_nhds hyN himp, ?_⟩
        filter_upwards [hyloc] with w hw hwN hwE
        exact hw hwN fun H hH hzH => hwE H hH ((hiff H hH).mpr hzH)
      have hys : boundaryCount (E₀.map (strictAlong T')) y = s₀ := by
        rw [boundaryCount_eq_of_forall_iff hiff]
        exact hzs
      rw [hmap] at hyL hys
      have hπyL := (mem_memberInterLocus_geoTransform_iff (geoTransformAlong 𝔪 T) hNT.1
        (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcT hg) hπ hETc
        hyC).mp hyL
      have hπys : boundaryCount (E₀.map (strictAlong T)) (π y) = s₀ := by
        rw [← CodimOnePartCanonical.boundaryCount_map_geoStrictTransform_of_notMem hπ.1.1
          hπ.contMDiff.continuous hETc hyC]
        exact hys
      exact ⟨y, hyt, memberInterLocus_level_geoTransformAlong_subset h𝔪 hE₀ s₀ T hT0 ⟨hπyL, hπys⟩⟩

/-- **Once empty, the level-`s₀` part of the member locus stays empty along every multiple test
blow-up.** -/
theorem memberInterLocus_level_geoTransformAlong_eq_empty (h𝔪 : 𝔪.IsWellFormed) {E₀ : List (Set X)}
    (hE₀ : ∀ H ∈ E₀, H ∈ 𝔪.E) (s₀ : ℕ)
    (hempty : memberInterLocus 𝔪.N E₀ 𝔪.cosupp ∩ {x | boundaryCount E₀ x = s₀} = ∅)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) :
    memberInterLocus (geoTransformAlong 𝔪 T).N (E₀.map (strictAlong T)) (geoTransformAlong 𝔪 T).cosupp ∩
      {z | boundaryCount (E₀.map (strictAlong T)) z = s₀} = ∅ := by
  have h := memberInterLocus_level_geoTransformAlong_subset 𝔪 h𝔪 hE₀ s₀ T hT
  rw [hempty, closure_empty, preimage_empty] at h
  exact subset_empty_iff.mp h

/-- **After Step 1aa the level-`s₀` part of the member locus is empty and stays empty**: for `𝔪` well
formed, a sublist `E₀` of `𝔪.E` (the members counted), `π` the blowup along the level-`s₀` part `C` of the
member locus and `S` a tower over its source such that `π` followed by `S` is a multiple test blow-up of
`𝔪`, the level-`s₀` part of the member locus of the transform along this tower (strict transforms of
`E₀`) is empty. -/
theorem memberInterLocus_level_geoTransformAlong_append_eq_empty (h𝔪 : 𝔪.IsWellFormed)
    {E₀ : List (Set X)} (hE₀ : E₀.Sublist 𝔪.E) (s₀ : ℕ) {Y₁ : CMfd.{u} n} (π : Y₁ → X)
    (hπ : IsBlowupAlong n (memberInterLocus 𝔪.N E₀ 𝔪.cosupp ∩ {x | boundaryCount E₀ x = s₀}) π)
    {Y : CMfd.{u} n} (S : BlowupTower Y₁ Y)
    (hS : IsGeoTestTower 𝔪 ((BlowupTower.step .refl
      (memberInterLocus 𝔪.N E₀ 𝔪.cosupp ∩ {x | boundaryCount E₀ x = s₀}) π hπ).append S)) :
    memberInterLocus
        (geoTransformAlong 𝔪 ((BlowupTower.step .refl
          (memberInterLocus 𝔪.N E₀ 𝔪.cosupp ∩ {x | boundaryCount E₀ x = s₀}) π hπ).append S)).N
        (E₀.map (strictAlong ((BlowupTower.step .refl
          (memberInterLocus 𝔪.N E₀ 𝔪.cosupp ∩ {x | boundaryCount E₀ x = s₀}) π hπ).append S)))
        (geoTransformAlong 𝔪 ((BlowupTower.step .refl
          (memberInterLocus 𝔪.N E₀ 𝔪.cosupp ∩ {x | boundaryCount E₀ x = s₀}) π hπ).append S)).cosupp ∩
      {z | boundaryCount (E₀.map (strictAlong ((BlowupTower.step .refl
          (memberInterLocus 𝔪.N E₀ 𝔪.cosupp ∩ {x | boundaryCount E₀ x = s₀}) π hπ).append S))) z = s₀} =
      ∅ := by
  set C := memberInterLocus 𝔪.N E₀ 𝔪.cosupp ∩ {x | boundaryCount E₀ x = s₀} with hCdef
  set T₁ : BlowupTower X Y₁ := .step .refl C π hπ with hT₁
  obtain ⟨hT₁t, hSt⟩ := (isGeoTestTower_append_iff 𝔪 T₁ S).mp hS
  have hC : 𝔪.IsAdmissibleCentre C := hT₁t.2
  have hW₁ : (geoTransformAlong 𝔪 T₁).IsWellFormed :=
    MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong h𝔪 T₁ hT₁t
  have hE₁ : ∀ H ∈ E₀.map (strictAlong T₁), H ∈ (geoTransformAlong 𝔪 T₁).E := by
    rw [List.forall_mem_map]
    intro H hH
    show geoStrictTransform π C H ∈ 𝔪.E.map (geoStrictTransform π C) ++ [π ⁻¹' C]
    exact List.mem_append_left _ (List.mem_map_of_mem (hE₀.subset hH))
  have hempty₁ := memberInterLocus_level_geoTransform_eq_empty 𝔪 h𝔪 hE₀ s₀ hπ hC
  have hempty₁' : memberInterLocus (geoTransformAlong 𝔪 T₁).N (E₀.map (strictAlong T₁))
      (geoTransformAlong 𝔪 T₁).cosupp ∩ {x | boundaryCount (E₀.map (strictAlong T₁)) x = s₀} = ∅ :=
    hempty₁
  have h := memberInterLocus_level_geoTransformAlong_eq_empty (geoTransformAlong 𝔪 T₁) hW₁ hE₁ s₀
    hempty₁' S hSt
  have hmap : E₀.map (strictAlong (T₁.append S)) = (E₀.map (strictAlong T₁)).map (strictAlong S) := by
    rw [List.map_map]
    exact List.map_congr_left fun H _ => strictAlong_append T₁ H S
  rw [hmap, geoTransformAlong_append]
  exact h

end LevelTower

/-! ### Off the member locus the restriction to `N ∩ H_{S(y)}` is nonzero -/

section Nonzero

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **Off the member locus the restriction to the intersection of the members through `y` is
nonzero.**  Let `y ∈ N`, `A = N ∩ {z | z lies on every member of E through y}`, `𝔟` coherent, and assume
that near `y` the cosupport of `(𝔟|_A, ν)` lies in `S`.  If `y` is not in the member locus of `S`, some germ
of `𝔟` at `y` does not vanish identically on `A` near `y`: otherwise every point of `A` near `y` lies in
the cosupport of `(𝔟|_A, ν)`, hence in `S`. -/
theorem isNonzeroAlongAt_of_notMem_memberInterLocus {N S : Set M} {E : List (Set M)}
    {𝔟 : GermIdeal n M} {ν : ℕ} (h𝔟 : 𝔟.IsCoherent) {y : M} (hyN : y ∈ N)
    (hcos : ∀ᶠ z in 𝓝 y, z ∈ cosupport n (N ∩ {z | ∀ H ∈ E, y ∈ H → z ∈ H}) 𝔟 ν → z ∈ S)
    (hy : y ∉ memberInterLocus N E S) :
    IsNonzeroAlongAt (N ∩ {z | ∀ H ∈ E, y ∈ H → z ∈ H}) 𝔟 y := by
  by_contra h
  apply hy
  rw [mem_memberInterLocus_iff]
  have key : ∀ᶠ z in 𝓝 y, z ∈ N → (∀ H ∈ E, y ∈ H → z ∈ H) → z ∈ S := by
    filter_upwards [hcos, eventually_forall_eq_zero_of_not_isNonzeroAlongAt h𝔟 h] with z hz1 hz2 hzN hzE
    exact hz1 ⟨⟨hzN, hzE⟩, fun g hg => ⟨fun _ => 0, zero_mem_idealPow _ z ν, hz2 g hg⟩⟩
  exact ⟨key.self_of_nhds hyN fun _ _ h => h, key⟩

/-- **Step 1ab's restricted marked ideals are nonzero along their submanifolds off the member locus.**
For `𝔪 = (M, N, E, 𝔞, d)` with `N` a closed submanifold, `𝔞` coherent, `d ≥ 1`, a list `E₀` of sets (the
members counted) and `y ∈ N` not in the member locus of the cosupport along `N` and `E₀`, the coefficient
ideal along `N` restricted to `A = N ∩ H_{S(y)}` (TN23's `withN (coeffMarkedAlong 𝔪) A`, with any `E`) is
nonzero along `A` near `y`.  (Its cosupport is `cosupp 𝔪 ∩ A`,
`CoefficientIdealAlongRestriction.cosupp_coeffMarkedAlong_withN`.) -/
theorem isNonzeroAlongAt_coeffMarkedAlong_of_notMem_memberInterLocus (𝔪 : MarkedIdeal n M)
    (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d) (E₀ : List (Set M))
    {y : M} (hyN : y ∈ 𝔪.N) (hy : y ∉ memberInterLocus 𝔪.N E₀ 𝔪.cosupp) :
    IsNonzeroAlongAt (withN (coeffMarkedAlong 𝔪) (𝔪.N ∩ {z | ∀ H ∈ E₀, y ∈ H → z ∈ H})).N
      (withN (coeffMarkedAlong 𝔪) (𝔪.N ∩ {z | ∀ H ∈ E₀, y ∈ H → z ∈ H})).ideal y := by
  have hc := CoefficientIdealAlongRestriction.cosupp_coeffMarkedAlong_withN hN.2
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg) hd
    (S := 𝔪.N ∩ {z | ∀ H ∈ E₀, y ∈ H → z ∈ H}) (fun _ hz => hz.1)
  refine isNonzeroAlongAt_of_notMem_memberInterLocus (ν := (coeffMarkedAlong 𝔪).d)
    (isCoherent_coeffMarkedAlong h𝔞 hN) hyN (Eventually.of_forall fun z hz => ?_) hy
  have hz' : z ∈ (withN (coeffMarkedAlong 𝔪) (𝔪.N ∩ {z | ∀ H ∈ E₀, y ∈ H → z ∈ H})).cosupp := hz
  rw [hc] at hz'
  exact hz'.1

end Nonzero

/-! ### The Step 1aa centre at the maximal level is admissible -/

section Centre

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

open Classical in
/-- **Intersections of members of a sublist, in index form of the whole divisor**: for a list `E₀` of
members of `E` and a property `P` of members, `⋂_{H ∈ E₀, P H} H = memberInter E S` with `S` the indices of
the members of `E` that are in `E₀` and satisfy `P`. -/
theorem setOf_forall_mem_eq_memberInter_of_mem {E E₀ : List (Set M)} (hE₀ : ∀ H ∈ E₀, H ∈ E)
    (P : Set M → Prop) :
    {w | ∀ H ∈ E₀, P H → w ∈ H} =
      memberInter E (Finset.univ.filter fun i => E.get i ∈ E₀ ∧ P (E.get i)) := by
  ext w
  show (∀ H ∈ E₀, P H → w ∈ H) ↔
    ∀ i ∈ Finset.univ.filter (fun i => E.get i ∈ E₀ ∧ P (E.get i)), w ∈ E.get i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro h i ⟨hi, hP⟩
    exact h _ hi hP
  · intro h H hH hP
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp (hE₀ H hH)
    exact h i ⟨hH, hP⟩

/-- **Near each of its points the level set of the member locus is `N ∩ H_{S(x)}`** (members closed,
`S ⊆ N`). -/
theorem eventually_mem_level_iff {N S : Set M} {E₀ : List (Set M)} (hE₀c : ∀ H ∈ E₀, IsClosed H)
    (hSN : S ⊆ N) {s₀ : ℕ} {x : M} (hx : x ∈ memberInterLocus N E₀ S ∩ {x | boundaryCount E₀ x = s₀}) :
    ∀ᶠ y in 𝓝 x, y ∈ memberInterLocus N E₀ S ∩ {x | boundaryCount E₀ x = s₀} ↔
      y ∈ N ∩ {w | ∀ H ∈ E₀, x ∈ H → w ∈ H} := by
  have hxs : boundaryCount E₀ x = s₀ := hx.2
  have havoid : ∀ᶠ y in 𝓝 x, ∀ H ∈ E₀, x ∉ H → y ∉ H :=
    (eventually_all_finite (List.finite_toSet E₀)).mpr fun H hH => by
      by_cases hxH : x ∈ H
      · exact Eventually.of_forall fun _ h => absurd hxH h
      · filter_upwards [(hE₀c H hH).isOpen_compl.mem_nhds hxH] with y hy _
        exact hy
  filter_upwards [eventually_mem_memberInterLocus_level hE₀c hx.1, havoid] with y hy1 hy2
  constructor
  · rintro ⟨hyL, hys⟩
    have hys' : boundaryCount E₀ y = s₀ := hys
    have himp : ∀ H ∈ E₀, y ∈ H → x ∈ H := fun H hH hyH => by_contra fun h => hy2 H hH h hyH
    have hle : boundaryCount E₀ x ≤ boundaryCount E₀ y := by rw [hxs, hys']
    have hiff := forall_iff_of_forall_imp_of_boundaryCount_le himp hle
    exact ⟨hSN hyL.1, fun H hH hxH => (hiff H hH).mp hxH⟩
  · rintro ⟨hyN, hyE⟩
    obtain ⟨hyL, hyc⟩ := hy1 hyN ((forall_get_iff (P := fun H => x ∈ H → y ∈ H)).mpr hyE)
    exact ⟨hyL, show boundaryCount E₀ y = s₀ by rw [hyc, hxs]⟩

/-- **The Step 1aa centre at the maximal level is admissible.**  Let `𝔪` be well formed, `d ≥ 1`, `0 < n`,
`E₀` a sublist of `𝔪.E` (the members counted), and `s₀` an upper bound of the count `s` on the cosupport.
Then the level-`s₀` part `C` of the member locus of the cosupport along `N` and `E₀` is an admissible centre
of `𝔪`: near each of its points it is `N ∩ H_{S(x)}`, a closed submanifold with normal crossings with `E`
(`MemberInterAlong`); and it is closed: at a limit point `x`, `s(x) = s₀` (upper semicontinuity and the
bound), the points of `C` near `x` lie on exactly the members through `x`, so the analytic set
`cosupp ∩ N ∩ H_{S(x)}` contains open pieces of the submanifold `N ∩ H_{S(x)}` accumulating at `x`, and by the
filling lemma (`CodimOneSupport.eventually_mem_of_locDimGE`) it contains `N ∩ H_{S(x)}` near `x`. -/
theorem isAdmissibleCentre_memberInterLocus_level (𝔪 : MarkedIdeal n M) (h𝔪 : 𝔪.IsWellFormed)
    (hd : 1 ≤ 𝔪.d) (hn : 0 < n) {E₀ : List (Set M)} (hE₀ : E₀.Sublist 𝔪.E) (s₀ : ℕ)
    (hmax : ∀ x ∈ 𝔪.cosupp, boundaryCount E₀ x ≤ s₀) :
    𝔪.IsAdmissibleCentre (memberInterLocus 𝔪.N E₀ 𝔪.cosupp ∩ {x | boundaryCount E₀ x = s₀}) := by
  set C := memberInterLocus 𝔪.N E₀ 𝔪.cosupp ∩ {x | boundaryCount E₀ x = s₀} with hCdef
  have hN := h𝔪.isClosedSubmanifold_N
  have h𝔞 := h𝔪.isCoherent
  have hE₀c : ∀ H ∈ E₀, IsClosed H := fun H hH => h𝔪.isSNCDivisor.1 H (hE₀.subset hH)
  have hE₀snc := NormalCrossingsComparison.isSNCDivisor_of_sublist h𝔪.isSNCDivisor hE₀
  have hE₀tr := NormalCrossingsComparison.isTransverse_of_forall_mem h𝔪.isTransverse
    fun _ hH => hE₀.subset hH
  have hSN : 𝔪.cosupp ⊆ 𝔪.N := 𝔪.cosupp_subset_N
  have hHsub : ∀ x : M, IsClosedSubmanifold n (𝔪.N ∩ {w | ∀ H ∈ E₀, x ∈ H → w ∈ H}) := fun x => by
    rw [setOf_forall_mem_eq_memberInter E₀ x]
    exact MemberInterAlong.isClosedSubmanifold_inter_memberInter hn hN.1 hE₀snc hE₀tr _
  have hloc : ∀ x ∈ C, ∀ᶠ y in 𝓝 x, y ∈ C ↔ y ∈ 𝔪.N ∩ {w | ∀ H ∈ E₀, x ∈ H → w ∈ H} :=
    fun x hx => eventually_mem_level_iff hE₀c hSN hx
  have hcos : IsClosed 𝔪.cosupp := GiraudAlong.isClosed_cosupport_along h𝔞 hN 𝔪.d
  have hCc : IsClosed C := by
    refine isClosed_of_closure_subset fun x hx => ?_
    have hxS : x ∈ 𝔪.cosupp := hcos.closure_subset (closure_mono (fun y hy => hy.1.1) hx)
    have havoid : ∀ᶠ y in 𝓝 x, ∀ H ∈ E₀, x ∉ H → y ∉ H :=
      (eventually_all_finite (List.finite_toSet E₀)).mpr fun H hH => by
        by_cases hxH : x ∈ H
        · exact Eventually.of_forall fun _ h => absurd hxH h
        · filter_upwards [(hE₀c H hH).isOpen_compl.mem_nhds hxH] with y hy _
          exact hy
    have hle := eventually_boundaryCount_le hE₀c x
    obtain ⟨y₀, hy₀le, hy₀C⟩ := mem_closure_iff_nhds.mp hx _ hle
    have hxs : boundaryCount E₀ x = s₀ := by
      have h0 : boundaryCount E₀ y₀ = s₀ := hy₀C.2
      exact le_antisymm (hmax x hxS) (h0 ▸ hy₀le)
    set H := 𝔪.N ∩ {w | ∀ H' ∈ E₀, x ∈ H' → w ∈ H'} with hHdef
    have hxH : x ∈ H := ⟨hSN hxS, fun _ _ h => h⟩
    obtain ⟨k, hk⟩ := (hHsub x).2 x hxH
    have hA : IsComplexAnalyticSubset (n := n) (𝔪.cosupp ∩ H) :=
      (CodimOneSupportAlong.isComplexAnalyticSubset_cosupport_along h𝔞 hN hd).inter
        (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold (hHsub x))
    have hsame : ∀ᶠ y in 𝓝 x, y ∈ C → ∀ H' ∈ E₀, (x ∈ H' ↔ y ∈ H') := by
      filter_upwards [havoid] with y hyav hyC
      have himp : ∀ H' ∈ E₀, y ∈ H' → x ∈ H' := fun H' hH' hy => by_contra fun h => hyav H' hH' h hy
      have hle' : boundaryCount E₀ x ≤ boundaryCount E₀ y := by
        rw [hxs, show boundaryCount E₀ y = s₀ from hyC.2]
      exact forall_iff_of_forall_imp_of_boundaryCount_le himp hle'
    have hHreg := RegularPatchNeighborhood.eventually_regularAtDim hk
    have hdim : AnalyticDimensionBasics.LocDimGE (n := n) (𝔪.cosupp ∩ H) x k := by
      intro U hU
      obtain ⟨y, ⟨⟨hyU, hysame⟩, hyreg⟩, hyC⟩ :=
        mem_closure_iff_nhds.mp hx _ (inter_mem (inter_mem hU hsame) hHreg)
      have hyiff := hysame hyC
      have hyH : y ∈ H := ⟨hSN hyC.1.1, fun H' hH' hxH' => (hyiff H' hH').mp hxH'⟩
      have hHy : 𝔪.N ∩ {w | ∀ H' ∈ E₀, y ∈ H' → w ∈ H'} = H := by
        ext w
        exact and_congr Iff.rfl ⟨fun h H' hH' hxH' => h H' hH' ((hyiff H' hH').mp hxH'),
          fun h H' hH' hyH' => h H' hH' ((hyiff H' hH').mpr hyH')⟩
      refine ⟨y, hyU, k, le_rfl, CodimOneSupport.regularAtDim_of_eventually_mem_iff ?_ (hyreg hyH)⟩
      filter_upwards [hloc y hyC] with w hw
      rw [hHy] at hw
      exact ⟨fun hwH => ⟨(hw.mpr hwH).1.1, hwH⟩, fun h => h.2⟩
    have hfill := CodimOneSupport.eventually_mem_of_locDimGE hA hk
      (Eventually.of_forall fun _ h => h.2) hdim
    refine ⟨mem_memberInterLocus_iff.mpr ⟨hxS, ?_⟩, hxs⟩
    filter_upwards [hfill] with w hw hwN hwE
    exact (hw ⟨hwN, hwE⟩).1
  refine ⟨⟨hCc, fun x hx => ?_⟩, fun x hx => hx.1.1, ?_⟩
  · obtain ⟨k, hk⟩ := (hHsub x).2 x ⟨hSN hx.1.1, fun _ _ h => h⟩
    exact ⟨k, CodimOneSupport.regularAtDim_of_eventually_mem_iff ((hloc x hx).mono fun _ h => h.symm) hk⟩
  · refine CodimOneAdmissibleAlong.hasNormalCrossings_of_forall_eventually fun x hx => ?_
    refine ⟨𝔪.N ∩ {w | ∀ H ∈ E₀, x ∈ H → w ∈ H}, ⟨hSN hx.1.1, fun _ _ h => h⟩, hloc x hx, ?_⟩
    rw [setOf_forall_mem_eq_memberInter_of_mem (fun H hH => hE₀.subset hH) (fun H => x ∈ H)]
    exact MemberInterAlong.hasNormalCrossings_inter_memberInter h𝔪.isTransverse _

end Centre

end

end Hironaka.MemberInterLocusAlong
