import DeJongAlterations.StableModification.Blowups.SeparationLift

/-!
# Separation of the boundary (Temkin, Lemma 4.3.2, for sections)

M. Temkin, *Stable modification of relative curves*, Lemma 4.3.2 (`divlem`, T:3019–3046): for a
strictly semi-stable curve `C` over a valuation ring `A` with separably closed fraction field and
marks given by sections `σ₁, …, σₙ`, a composite of blow-ups makes the strict transforms of the
sections pairwise disjoint and contained in the smooth locus. Blueprint
`sm-boundary-separation.tex`, `lem:sm-boundary-separation`.

We iterate the transported chart blow-ups of `exists_nodeBlowup_transport` and
`exists_smoothBlowup_transport`, inducting on the pair `(N, P)` (lexicographically), where `N` is
the number of sections whose closed point has no smooth chart and `P` the number of pairs of
sections meeting at the closed fibre:

* **node step** (`exists_node_step`, T:3036–3046): at the origin `x` of a node chart
  `A[u,v]/(uv - a)` through which sections `(cₖ, dₖ)` pass, blow up `(u, π)` with `π = c_m` of
  minimal valuation; the lift of `σ_m` acquires a smooth chart, so `N` drops;
* **smooth step** (`exists_smooth_step`, replacing T:3027–3033): at a smooth chart point `x`
  through which sections `T = cₖ` pass, blow up `(π, T - c_i)` with `π = c_i - c_j` of minimal
  valuation among the differences; all lifts lie in the smooth `π`-chart and `σ_i, σ_j` are
  separated, so `N` stays `0` and `P` drops.

## Main results

* `exists_separation` (**Lemma 4.3.2 for sections**): a modification `β : C' ⟶ C`, with `C'`
  integral, separated and strictly semi-stable without marks, and lifts `σ'ₖ` of the sections
  with pairwise disjoint images in the smooth locus of `C' ⟶ Spec A`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing Polynomial

noncomputable section

namespace DeJongAlterations.StableModification.Blowups

universe u

open Curves Algebra.NodeBlowupChart

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Measure

open Classical

variable {A : Type u} [CommRing A] [IsLocalRing A] {C : Scheme.{u}} {n : ℕ}

/-- The number of sections whose closed point has no smooth chart. -/
def numNoChart (g : C ⟶ Spec (.of A)) (σ : Fin n → (Spec (.of A) ⟶ C)) : ℕ :=
  (Finset.univ.filter fun k ↦ ¬ HasSmoothChart g (σ k (closedPoint A))).card

/-- The number of pairs `k < l` of sections meeting at the closed fibre. -/
def numMeeting (σ : Fin n → (Spec (.of A) ⟶ C)) : ℕ :=
  (Finset.univ.filter fun kl : Fin n × Fin n ↦
    kl.1 < kl.2 ∧ σ kl.1 (closedPoint A) = σ kl.2 (closedPoint A)).card

/-- The induction measure `N (n² + 1) + P`, which decreases with `(N, P)` lexicographically. -/
def separationMeasure (g : C ⟶ Spec (.of A)) (σ : Fin n → (Spec (.of A) ⟶ C)) : ℕ :=
  numNoChart g σ * (n * n + 1) + numMeeting σ

theorem numMeeting_le (σ : Fin n → (Spec (.of A) ⟶ C)) : numMeeting σ ≤ n * n := by
  refine (Finset.card_filter_le _ _).trans ?_
  simp

end Measure

section Helpers

variable {A : Type u} [CommRing A] {C : Scheme.{u}}

/-- A smooth chart at `y` gives one at every generization of `y`. -/
theorem HasSmoothChart.of_specializes {g : C ⟶ Spec (.of A)} {y y' : C} (h : HasSmoothChart g y)
    (hy : y' ⤳ y) : HasSmoothChart g y' := by
  obtain ⟨Y, ι, _, e, _, hyι, he⟩ := h
  exact ⟨Y, ι, inferInstance, e, inferInstance,
    hy.mem_open ι.isOpenEmbedding.isOpen_range hyι, he⟩

variable [IsLocalRing A]

theorem factorThruOpen_homOfLE (σ : Spec (.of A) ⟶ C) {U₀ U : C.Opens} (hU₀ : U₀ ≤ U)
    (h₀ : σ (closedPoint A) ∈ U₀) (h : σ (closedPoint A) ∈ U) :
    factorThruOpen σ U₀ h₀ ≫ C.homOfLE hU₀ = factorThruOpen σ U h := by
  rw [← cancel_mono U.ι, Category.assoc, Scheme.homOfLE_ι, factorThruOpen_ι, factorThruOpen_ι]

theorem factorThruOpen_closedPoint (σ : Spec (.of A) ⟶ C) (U : C.Opens)
    (h : σ (closedPoint A) ∈ U) :
    factorThruOpen σ U h (closedPoint A) = ⟨σ (closedPoint A), h⟩ := by
  apply U.ι.isOpenEmbedding.injective
  rw [← Scheme.Hom.comp_apply, factorThruOpen_ι]
  rfl

/-- In a valuation ring, among finitely many elements one divides all others. -/
theorem exists_dvd_all {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R] {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (c : ι → R) : ∃ m ∈ s, ∀ k ∈ s, c m ∣ c k := by
  classical
  induction s using Finset.induction_on with
  | empty => exact absurd hs Finset.not_nonempty_empty
  | insert i s hi ih =>
    rcases s.eq_empty_or_nonempty with rfl | hne
    · exact ⟨i, by simp, by simp⟩
    obtain ⟨m, hm, hmk⟩ := ih hne
    rcases ValuationRing.dvd_total (c i) (c m) with h | h
    · refine ⟨i, Finset.mem_insert_self _ _, fun k hk ↦ ?_⟩
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact dvd_rfl
      · exact h.trans (hmk k hk)
    · refine ⟨m, Finset.mem_insert_of_mem hm, fun k hk ↦ ?_⟩
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact h
      · exact hmk k hk

end Helpers

/-- The invariants of the separation induction: `C` is integral, separated and strictly
semi-stable without marks over `A`, and the `σₖ` are pairwise distinct sections. -/
structure SeparationGood {A : Type u} [CommRing A] {C : Scheme.{u}} (g : C ⟶ Spec (.of A))
    {n : ℕ} (σ : Fin n → (Spec (.of A) ⟶ C)) : Prop where
  separated : IsSeparated g
  integral : IsIntegral C
  semistable : IsStrictlySemistable g ⊤
  isSection : ∀ k, σ k ≫ g = 𝟙 _
  injective : Function.Injective σ

section Lifts

variable {A : Type u} [CommRing A] [IsLocalRing A] {C C' M M' : Scheme.{u}} {n : ℕ}

open Classical in
/-- **Lifting all sections through a transport.** Given the output of `exists_transport` and, for
the sections through `x`, lifts `τₖ` of `φ₀ ∘ σₖ` to `M'`, there are lifts `σ'ₖ` of all sections
to `C'`: through the chart `j` for sections through `x`, through `W` otherwise. Smooth charts at
the closed points of the latter persist. -/
theorem exists_lifts (g : C ⟶ Spec (.of A)) {U₀ W : C.Opens} (φ₀ : U₀.toScheme ⟶ M)
    (β₀ : M' ⟶ M) (β : C' ⟶ C) (j : pullback β₀ φ₀ ⟶ C') [IsOpenImmersion j]
    (kW : W.toScheme ⟶ C') [IsOpenImmersion kW]
    (hj : j ≫ β = pullback.snd β₀ φ₀ ≫ U₀.ι) (hkW : kW ≫ β = W.ι) (x : C) (hxU₀ : x ∈ U₀)
    (huniq : ∀ y ∉ W, g y = closedPoint A → y = x)
    (σ : Fin n → (Spec (.of A) ⟶ C)) (hσ : ∀ k, σ k ≫ g = 𝟙 _)
    (τ : Fin n → (Spec (.of A) ⟶ M'))
    (hτ : ∀ k (hk : σ k (closedPoint A) = x),
      τ k ≫ β₀ = factorThruOpen (σ k) U₀ (by rw [hk]; exact hxU₀) ≫ φ₀) :
    ∃ σ' : Fin n → (Spec (.of A) ⟶ C'), (∀ k, σ' k ≫ β = σ k) ∧
      (∀ k, σ k (closedPoint A) = x → ∃ p : (pullback β₀ φ₀ : Scheme.{u}),
        σ' k (closedPoint A) = j p ∧ pullback.fst β₀ φ₀ p = τ k (closedPoint A)) ∧
      (∀ k, σ k (closedPoint A) ≠ x → HasSmoothChart g (σ k (closedPoint A)) →
        HasSmoothChart (β ≫ g) (σ' k (closedPoint A))) := by
  have hW : ∀ k, σ k (closedPoint A) ≠ x → σ k (closedPoint A) ∈ W := fun k hk ↦
    closedPoint_mem_of_ne g W x huniq (σ k) (hσ k) hk
  let σ' : Fin n → (Spec (.of A) ⟶ C') := fun k ↦
    if hk : σ k (closedPoint A) = x then
      liftThroughChart φ₀ β₀ j (σ k) (by rw [hk]; exact hxU₀) (τ k) (hτ k hk)
    else factorThruOpen (σ k) W (hW k hk) ≫ kW
  refine ⟨σ', fun k ↦ ?_, fun k hk ↦ ?_, fun k hk hch ↦ ?_⟩
  · by_cases hk' : σ k (closedPoint A) = x
    · simp only [σ', dif_pos hk']
      exact liftThroughChart_comp φ₀ β₀ β j hj _ _ _ _
    · simp only [σ', dif_neg hk', Category.assoc, hkW, factorThruOpen_ι]
  · refine ⟨pullback.lift (τ k) (factorThruOpen (σ k) U₀ (by rw [hk]; exact hxU₀)) (hτ k hk)
      (closedPoint A), ?_, ?_⟩
    · simp only [σ', dif_pos hk, liftThroughChart, Scheme.Hom.comp_apply]
    · rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
  · have hmem := hW k hk
    have hres := HasSmoothChart.restrict W ⟨_, hmem⟩ hch
    have h2 := HasSmoothChart.of_isOpenImmersion kW (g' := β ≫ g)
      (by rw [← Category.assoc, hkW]) hres
    convert h2 using 1
    simp only [σ', dif_neg hk, Scheme.Hom.comp_apply, factorThruOpen_closedPoint]

open Classical in
/-- Under lifts, meeting pairs can only disappear. -/
theorem numMeeting_le_of_lift {σ : Fin n → (Spec (.of A) ⟶ C)}
    {σ' : Fin n → (Spec (.of A) ⟶ C')} (β : C' ⟶ C) (h : ∀ k, σ' k ≫ β = σ k) :
    numMeeting σ' ≤ numMeeting σ := by
  apply Finset.card_le_card
  intro kl hkl
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hkl ⊢
  refine ⟨hkl.1, ?_⟩
  rw [← h kl.1, ← h kl.2, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hkl.2]

omit [IsLocalRing A] in
/-- Lifts of distinct sections are distinct sections. -/
theorem separationGood_of_lift {g : C ⟶ Spec (.of A)} {σ : Fin n → (Spec (.of A) ⟶ C)}
    (hgood : SeparationGood g σ) {σ' : Fin n → (Spec (.of A) ⟶ C')} (β : C' ⟶ C)
    [IsModification β] (hss : IsStrictlySemistable (β ≫ g) ⊤) (h : ∀ k, σ' k ≫ β = σ k) :
    SeparationGood (β ≫ g) σ' where
  separated := by
    have := hgood.separated
    infer_instance
  integral := IsModification.sourceIntegral (f := β)
  semistable := hss
  isSection k := by rw [← Category.assoc, h, hgood.isSection]
  injective k l hkl := hgood.injective (by rw [← h k, ← h l, hkl])

end Lifts

section NodeHelpers

variable {A : Type u} [CommRing A]

theorem nodePoint_congr (a : A) {c c' d d' : A} (hc : c = c') (hd : d = d') (h : c * d = a)
    (h' : c' * d' = a) : nodePoint a c d h = nodePoint a c' d' h' := by
  subst hc hd
  rfl

/-- The node model lies over the closed point at `p` iff `p` contracts to the maximal ideal. -/
theorem algebraMap_mem_iff_of_nodeModel_eq [IsLocalRing A] {a : A} (p : Spec (.of (Node A a)))
    (hp : nodeModel a p = closedPoint A) (r : A) :
    algebraMap A (Node A a) r ∈ p.asIdeal ↔ r ∈ maximalIdeal A := by
  have h2 : maximalIdeal A = ((nodeModel a) p).asIdeal := by rw [hp]; rfl
  rw [h2]
  exact Iff.rfl

end NodeHelpers

section Steps

variable {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A] [IsIntegrallyClosed A]
  [HenselianLocalRing A] [IsSepClosed (ResidueField A)] {C : Scheme.{u}} {n : ℕ}

open Classical in
/-- **The node step** (Temkin, Lemma 4.3.2, T:3036–3046). If the closed point `x = σ_{k₀}(s)`
has no smooth chart, a transported node blow-up `Bl_{(u, π)}`, `π = c_m` of minimal valuation
among the `u`-coordinates of the sections through `x`, gives lifts with fewer closed points
without smooth chart and no new meetings. -/
theorem exists_node_step {g : C ⟶ Spec (.of A)} {σ : Fin n → (Spec (.of A) ⟶ C)}
    (hgood : SeparationGood g σ) (k₀ : Fin n)
    (hk₀ : ¬ HasSmoothChart g (σ k₀ (closedPoint A))) :
    ∃ (C₁ : Scheme.{u}) (β : C₁ ⟶ C) (σ₁ : Fin n → (Spec (.of A) ⟶ C₁)),
      IsModification β ∧ SeparationGood (β ≫ g) σ₁ ∧ (∀ k, σ₁ k ≫ β = σ k) ∧
      numNoChart (β ≫ g) σ₁ < numNoChart g σ ∧ numMeeting σ₁ ≤ numMeeting σ := by
  have := hgood.separated
  have hCint := hgood.integral
  set x := σ k₀ (closedPoint A) with hxdef
  have hx : g x = closedPoint A := by
    rw [hxdef, ← Scheme.Hom.comp_apply, hgood.isSection]; rfl
  obtain ⟨U, hxU, hcase⟩ := exists_chart hgood.semistable x hx
  rcases hcase with ⟨e, he, hφ⟩ | ⟨a, φ, hφe, hφ⟩
  · have := he
    exact absurd (hasSmoothChart_of_etale g U e hφ x hxU) hk₀
  have : Etale φ := hφe
  -- `φ x` is the origin of the node chart
  have hxu : ∀ i : Fin 2, φ ⟨x, hxU⟩ ∉ Geometry.NodeFamilySmooth.coordinateOpen a i := by
    intro i hi
    exact hk₀ (hasSmoothChart_of_node g U.ι a φ hφ ⟨x, hxU⟩ i hi)
  have hu0 : coordinate a 0 ∈ (φ ⟨x, hxU⟩).asIdeal := by
    by_contra h
    exact hxu 0 h
  have hu1 : coordinate a 1 ∈ (φ ⟨x, hxU⟩).asIdeal := by
    by_contra h
    exact hxu 1 h
  have : Nonempty U.toScheme := ⟨⟨x, hxU⟩⟩
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  have ha : a ≠ 0 := node_param_ne_zero a φ ⟨x, hxU⟩ hu0 hu1
  have hφx : nodeModel a (φ ⟨x, hxU⟩) = closedPoint A := by
    rw [← Scheme.Hom.comp_apply, hφ, Scheme.Hom.comp_apply]
    exact hx
  -- the sections through `x` and their coordinates
  let I := Finset.univ.filter fun k ↦ σ k (closedPoint A) = x
  have hk₀I : k₀ ∈ I := by simp [I, hxdef]
  have hIx : ∀ k ∈ I, σ k (closedPoint A) = x := fun k hk ↦ (Finset.mem_filter.mp hk).2
  have hU : ∀ k ∈ I, σ k (closedPoint A) ∈ U := fun k hk ↦ by rw [hIx k hk]; exact hxU
  have hcoord : ∀ k (hk : k ∈ I), ∃ (c d : A) (h : c * d = a),
      factorThruOpen (σ k) U (hU k hk) ≫ φ =
        Spec.map (CommRingCat.ofHom (nodePoint a c d h).toRingHom) := fun k hk ↦
    exists_eq_specMap_nodePoint a _ (by
      rw [Category.assoc, hφ, ← Category.assoc, factorThruOpen_ι, hgood.isSection])
  choose! c d hcd hfac using hcoord
  have hpt : ∀ k (hk : k ∈ I), Spec.map (CommRingCat.ofHom (nodePoint a (c k) (d k)
      (hcd k hk)).toRingHom) (closedPoint A) = φ ⟨x, hxU⟩ := by
    intro k hk
    rw [← hfac k hk, Scheme.Hom.comp_apply, factorThruOpen_closedPoint]
    congr 1
    exact Subtype.ext (hIx k hk)
  have hcm : ∀ k ∈ I, c k ∈ maximalIdeal A := by
    intro k hk
    have h := hu0
    rw [← hpt k hk, specMap_nodePoint_closedPoint_asIdeal, Ideal.mem_comap] at h
    simpa using h
  -- the section through `x` with `c_m` of minimal valuation
  obtain ⟨m₀, hm₀, hdvd⟩ := exists_dvd_all I ⟨k₀, hk₀I⟩ c
  have hcd₀ : c m₀ * d m₀ = a := hcd m₀ hm₀
  have hπ : c m₀ ≠ 0 := left_ne_zero_of_mul (hcd₀ ▸ ha)
  have hb : d m₀ ≠ 0 := right_ne_zero_of_mul (hcd₀ ▸ ha)
  choose! e he using hdvd
  have hde : ∀ k ∈ I, d k * e k = d m₀ := by
    intro k hk
    apply mul_left_cancel₀ hπ
    have h1 := hcd k hk
    rw [he k hk] at h1
    rw [hcd₀, ← h1]
    ring
  have he₀ : e m₀ = 1 := by
    apply mul_left_cancel₀ hπ
    rw [mul_one, ← he m₀ hm₀]
  subst hcd₀
  have : Fact (c m₀ ≠ 0) := ⟨hπ⟩
  have : Fact (d m₀ ≠ 0) := ⟨hb⟩
  -- the centre passes through `φ x`
  have hxi : φ ⟨x, hxU⟩ ∈ Set.range (nodeLocus (c m₀) (d m₀)) := by
    rw [range_nodeLocus]
    simp only [nodeLocusComplement, Set.mem_compl_iff, Opens.coe_sup, Set.mem_union,
      SetLike.mem_coe, not_or]
    exact ⟨⟨fun h ↦ h hu0, fun h ↦ h hu1⟩,
      fun h ↦ h ((algebraMap_mem_iff_of_nodeModel_eq _ hφx _).mpr (hcm m₀ hm₀))⟩
  obtain ⟨U₀, hU₀, W, C₁, β, j, kW, hxU₀, -, -, huniq, hj, hkW, hjβ, hkβ, -, -, -, hss, hmod⟩ :=
    exists_nodeBlowup_transport (c m₀) (d m₀) g hgood.semistable U φ hφ x hxU hx hxi
  have : IsModification β := hmod hCint
  -- the lifts of the sections through `x`
  let τ : Fin n → (Spec (.of A) ⟶ affineBlowup (centerIdeal (c m₀) (d m₀))) := fun k ↦
    if hk : k ∈ I then nodeLift (c m₀) (d m₀) (d k) (e k) (hde k hk)
    else nodeLift (c m₀) (d m₀) (d m₀) 1 (mul_one _)
  have hτ : ∀ k (hk : σ k (closedPoint A) = x), τ k ≫ affineBlowupStructure
      (centerIdeal (c m₀) (d m₀)) = factorThruOpen (σ k) U₀ (by rw [hk]; exact hxU₀) ≫
        (C.homOfLE hU₀ ≫ φ) := by
    intro k hk
    have hkI : k ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
    simp only [τ, dif_pos hkI]
    rw [nodeLift_comp, ← Category.assoc, factorThruOpen_homOfLE (σ k) hU₀ _ (hU k hkI),
      hfac k hkI]
    congr 3
    exact nodePoint_congr _ (he k hkI).symm rfl _ _
  obtain ⟨σ₁, hσ₁β, hσ₁chart, hσ₁rest⟩ := exists_lifts g (C.homOfLE hU₀ ≫ φ)
    (affineBlowupStructure (centerIdeal (c m₀) (d m₀))) β j kW hjβ hkβ x hxU₀ huniq σ
    hgood.isSection τ hτ
  refine ⟨C₁, β, σ₁, inferInstance, separationGood_of_lift hgood β hss hσ₁β, hσ₁β, ?_,
    numMeeting_le_of_lift β hσ₁β⟩
  -- `N` drops
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_of_subset (fun k hk ↦ ?_) |>.mpr ⟨m₀, ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    intro hch
    by_cases hkx : σ k (closedPoint A) = x
    · exact hk₀ (hkx ▸ hch)
    · exact hk (hσ₁rest k hkx hch)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hIx m₀ hm₀]
    exact hk₀
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
    obtain ⟨p, hp, hpfst⟩ := hσ₁chart m₀ (hIx m₀ hm₀)
    rw [hp]
    have hτm : τ m₀ = nodeLift (c m₀) (d m₀) (d m₀) (e m₀) (hde m₀ hm₀) := by
      simp only [τ, dif_pos hm₀]
    rw [hτm, nodeLift, Scheme.Hom.comp_apply] at hpfst
    refine hasSmoothChart_of_nodeChart_lift (β ≫ g) j
      (pullback.fst (affineBlowupStructure (centerIdeal (c m₀) (d m₀))) (C.homOfLE hU₀ ≫ φ))
      (affineBlowupStructure (centerIdeal (c m₀) (d m₀)) ≫ nodeModel (c m₀ * d m₀)) ?_ (d m₀)
      (tChartInclusion (c m₀) (d m₀)) ?_ p _ hpfst.symm 1 ?_
    · rw [← Category.assoc, pullback.condition, Category.assoc, Category.assoc, hφ,
        ← Category.assoc (C.homOfLE hU₀), Scheme.homOfLE_ι, ← Category.assoc, ← hjβ,
        Category.assoc]
    · exact tChartInclusion_nodeBlowupMorphism (c m₀) (d m₀)
    · exact specMap_nodePoint_closedPoint_mem_coordinateOpen _ _ _ _ (by rw [he₀]; exact isUnit_one)

open Classical in
/-- **The smooth step** (replacing Temkin's separation by `Bl_{D_{i₁} ×_C D_{i₂}}` and
Prop 4.3.1, T:3027–3033). If all closed points of the sections have smooth charts and two
sections meet at `x`, a transported smooth blow-up `Bl_{(π, T - c_i)}`, `π = c_i - c_j` of minimal
valuation among the differences of the coordinates of the sections through `x`, gives lifts whose
closed points all have smooth charts and with fewer meeting pairs. -/
theorem exists_smooth_step {g : C ⟶ Spec (.of A)} {σ : Fin n → (Spec (.of A) ⟶ C)}
    (hgood : SeparationGood g σ) (hN : ∀ k, HasSmoothChart g (σ k (closedPoint A)))
    (i₀ j₀ : Fin n) (hij₀ : i₀ ≠ j₀) (hmeet : σ i₀ (closedPoint A) = σ j₀ (closedPoint A)) :
    ∃ (C₁ : Scheme.{u}) (β : C₁ ⟶ C) (σ₁ : Fin n → (Spec (.of A) ⟶ C₁)),
      IsModification β ∧ SeparationGood (β ≫ g) σ₁ ∧ (∀ k, σ₁ k ≫ β = σ k) ∧
      (∀ k, HasSmoothChart (β ≫ g) (σ₁ k (closedPoint A))) ∧
      numMeeting σ₁ < numMeeting σ := by
  have := hgood.separated
  have hCint := hgood.integral
  set x := σ i₀ (closedPoint A) with hxdef
  have hx : g x = closedPoint A := by
    rw [hxdef, ← Scheme.Hom.comp_apply, hgood.isSection]; rfl
  obtain ⟨Y, ι, _, e₀, _, ⟨y₀, hy₀⟩, he₀⟩ := hN i₀
  let U : C.Opens := ι.opensRange
  let φ : U.toScheme ⟶ Spec (.of A[X]) := ι.isoOpensRange.inv ≫ e₀
  have hφ : φ ≫ smoothModel A = U.ι ≫ g := by
    simp only [φ, Category.assoc, he₀]
    rw [← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]
  have hxU : x ∈ U := ⟨y₀, hy₀⟩
  have : Etale φ := by dsimp only [φ]; infer_instance
  have : IsSeparated (φ ≫ smoothModel A) := by rw [hφ]; infer_instance
  have : IsSeparated φ := IsSeparated.of_comp φ (smoothModel A)
  -- the sections through `x` and their coordinates
  let I := Finset.univ.filter fun k ↦ σ k (closedPoint A) = x
  have hIx : ∀ k ∈ I, σ k (closedPoint A) = x := fun k hk ↦ (Finset.mem_filter.mp hk).2
  have hi₀I : i₀ ∈ I := by simp [I, hxdef]
  have hj₀I : j₀ ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmeet.symm⟩
  have hU : ∀ k ∈ I, σ k (closedPoint A) ∈ U := fun k hk ↦ by rw [hIx k hk]; exact hxU
  have hcoord : ∀ k (hk : k ∈ I), ∃ c : A, factorThruOpen (σ k) U (hU k hk) ≫ φ =
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom c)) := fun k hk ↦
    exists_eq_specMap_evalRingHom _ (by
      rw [Category.assoc, hφ, ← Category.assoc, factorThruOpen_ι, hgood.isSection])
  choose! c hfac using hcoord
  have hpt : ∀ k (hk : k ∈ I), Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (c k)))
      (closedPoint A) = φ ⟨x, hxU⟩ := by
    intro k hk
    rw [← hfac k hk, Scheme.Hom.comp_apply, factorThruOpen_closedPoint]
    congr 1
    exact Subtype.ext (hIx k hk)
  -- distinct sections through `x` have distinct coordinates
  have hinjc : ∀ k ∈ I, ∀ l ∈ I, c k = c l → k = l := by
    intro k hk l hl hkl
    apply hgood.injective
    have heq := eq_of_comp_eq_of_apply_eq (U.ι ≫ g) φ (factorThruOpen (σ k) U (hU k hk))
      (factorThruOpen (σ l) U (hU l hl))
      (by rw [← Category.assoc, factorThruOpen_ι, hgood.isSection])
      (by rw [← Category.assoc, factorThruOpen_ι, hgood.isSection]) (closedPoint A)
      (by rw [factorThruOpen_closedPoint, factorThruOpen_closedPoint]
          exact Subtype.ext ((hIx k hk).trans (hIx l hl).symm))
      (by rw [hfac k hk, hfac l hl, hkl])
    rw [← factorThruOpen_ι (σ k) U (hU k hk), ← factorThruOpen_ι (σ l) U (hU l hl), heq]
  -- the coordinates are congruent modulo the maximal ideal
  have hcong : ∀ k ∈ I, ∀ l ∈ I, c k - c l ∈ maximalIdeal A := by
    intro k hk l hl
    have h1 := congrArg PrimeSpectrum.asIdeal ((hpt k hk).trans (hpt l hl).symm)
    rw [specMap_evalRingHom_closedPoint_asIdeal, specMap_evalRingHom_closedPoint_asIdeal] at h1
    have hmem : (X - Polynomial.C (c l) : A[X]) ∈
        (maximalIdeal A).comap (Polynomial.evalRingHom (c l)) := by
      simp
    rw [← h1, Ideal.mem_comap] at hmem
    simpa using hmem
  -- the pair of largest distance
  let pairs := (I ×ˢ I).filter fun kl : Fin n × Fin n ↦ kl.1 ≠ kl.2
  have hpairs : (i₀, j₀) ∈ pairs := by simp [pairs, hi₀I, hj₀I, hij₀]
  obtain ⟨⟨i, j⟩, hijp, hdvd⟩ := exists_dvd_all pairs ⟨_, hpairs⟩ fun kl ↦ c kl.1 - c kl.2
  simp only [pairs, Finset.mem_filter, Finset.mem_product] at hijp
  obtain ⟨⟨hi, hj⟩, hne⟩ := hijp
  have hπ : c i - c j ≠ 0 := sub_ne_zero.mpr fun h ↦ hne (hinjc i hi j hj h)
  have : Fact (c i - c j ≠ 0) := ⟨hπ⟩
  have hlift : ∀ k ∈ I, ∃ e : A, c k = c i + (c i - c j) * e := by
    intro k hk
    by_cases hki : k = i
    · exact ⟨0, by rw [hki]; ring⟩
    · obtain ⟨e, he⟩ := hdvd (k, i) (by simp [pairs, hk, hi, hki])
      exact ⟨e, by rw [← he]; ring⟩
  choose! e he using hlift
  have hei : e i = 0 := by
    have h := he i hi
    have : (c i - c j) * e i = (c i - c j) * 0 := by linear_combination -h
    exact mul_left_cancel₀ hπ this
  have hej : e j = -1 := by
    have h := he j hj
    have : (c i - c j) * e j = (c i - c j) * (-1) := by linear_combination -h
    exact mul_left_cancel₀ hπ this
  -- the centre passes through `φ x`
  have hxi : φ ⟨x, hxU⟩ ∈ Set.range (smoothLocus (c i - c j) (c i)) := by
    rw [range_smoothLocus, ← hpt i hi]
    intro h
    apply h
    change _ ∈ PrimeSpectrum.zeroLocus _
    rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, smoothCenter, Ideal.span_le,
      Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨?_, ?_⟩
    · change Polynomial.C (c i - c j) ∈ (Spec.map (CommRingCat.ofHom
        (Polynomial.evalRingHom (c i))) (closedPoint A)).asIdeal
      rw [specMap_evalRingHom_closedPoint_asIdeal, Ideal.mem_comap]
      simpa using hcong i hi j hj
    · change X - Polynomial.C (c i) ∈ (Spec.map (CommRingCat.ofHom
        (Polynomial.evalRingHom (c i))) (closedPoint A)).asIdeal
      rw [specMap_evalRingHom_closedPoint_asIdeal, Ideal.mem_comap]
      simp
  obtain ⟨U₀, hU₀, W, C₁, β, j', kW, hxU₀, -, -, huniq, hj', hkW, hjβ, hkβ, -, -, -, hss, hmod⟩ :=
    exists_smoothBlowup_transport (c i - c j) (c i) g hgood.semistable U φ hφ x hxU hx hxi
  have : IsModification β := hmod hCint
  -- the lifts of the sections through `x`
  let τ : Fin n → (Spec (.of A) ⟶ affineBlowup (smoothCenter (c i - c j) (c i))) := fun k ↦
    smoothLift (c i - c j) (c i) (e k)
  have hτ : ∀ k (hk : σ k (closedPoint A) = x), τ k ≫ affineBlowupStructure
      (smoothCenter (c i - c j) (c i)) = factorThruOpen (σ k) U₀ (by rw [hk]; exact hxU₀) ≫
        (C.homOfLE hU₀ ≫ φ) := by
    intro k hk
    have hkI : k ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
    rw [smoothLift_comp, ← Category.assoc, factorThruOpen_homOfLE (σ k) hU₀ _ (hU k hkI),
      hfac k hkI, ← he k hkI]
  obtain ⟨σ₁, hσ₁β, hσ₁chart, hσ₁rest⟩ := exists_lifts g (C.homOfLE hU₀ ≫ φ)
    (affineBlowupStructure (smoothCenter (c i - c j) (c i))) β j' kW hjβ hkβ x hxU₀ huniq σ
    hgood.isSection τ hτ
  have hf : pullback.fst (affineBlowupStructure (smoothCenter (c i - c j) (c i)))
      (C.homOfLE hU₀ ≫ φ) ≫ affineBlowupStructure (smoothCenter (c i - c j) (c i)) ≫
        smoothModel A = j' ≫ β ≫ g := by
    have h1 := pullback.condition (f := affineBlowupStructure (smoothCenter (c i - c j) (c i)))
      (g := C.homOfLE hU₀ ≫ φ)
    calc _ = (pullback.fst _ _ ≫ affineBlowupStructure (smoothCenter (c i - c j) (c i))) ≫
          smoothModel A := (Category.assoc _ _ _).symm
      _ = pullback.snd _ _ ≫ C.homOfLE hU₀ ≫ (φ ≫ smoothModel A) := by
          rw [h1]; simp only [Category.assoc]
      _ = pullback.snd _ _ ≫ (C.homOfLE hU₀ ≫ U.ι) ≫ g := by
          rw [hφ]; simp only [Category.assoc]
      _ = (j' ≫ β) ≫ g := by rw [Scheme.homOfLE_ι, hjβ, Category.assoc]
      _ = j' ≫ β ≫ g := Category.assoc _ _ _
  refine ⟨C₁, β, σ₁, inferInstance, separationGood_of_lift hgood β hss hσ₁β, hσ₁β,
    fun k ↦ ?_, ?_⟩
  · by_cases hkx : σ k (closedPoint A) = x
    · obtain ⟨p, hp, hpfst⟩ := hσ₁chart k hkx
      rw [hp]
      refine hasSmoothChart_of_smoothChart_lift (β ≫ g) j' _ _ hf
        (smoothParamChartInclusion (c i - c j) (c i))
        (smoothParamChartInclusion_smoothBlowupMorphism _ _) p ?_
      rw [hpfst]
      exact ⟨_, rfl⟩
    · exact hσ₁rest k hkx (hN k)
  -- `P` drops: the pair `{i, j}` is separated
  have hsep : σ₁ i (closedPoint A) ≠ σ₁ j (closedPoint A) := by
    obtain ⟨p, hp, hpfst⟩ := hσ₁chart i (hIx i hi)
    obtain ⟨q, hq, hqfst⟩ := hσ₁chart j (hIx j hj)
    intro heq
    rw [hp, hq] at heq
    have hpq := j'.isOpenEmbedding.injective heq
    have := smoothLift_closedPoint_ne (c i - c j) (c i) (e := e i) (e' := e j)
      (by rw [hei, hej]; simp)
    apply this
    rw [← hpfst, ← hqfst, hpq]
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_of_subset (fun kl hkl ↦ ?_) |>.mpr ?_
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hkl ⊢
    refine ⟨hkl.1, ?_⟩
    rw [← hσ₁β kl.1, ← hσ₁β kl.2, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hkl.2]
  · rcases lt_or_gt_of_ne hne with hlt | hlt
    · refine ⟨(i, j), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hlt, (hIx i hi).trans (hIx j hj).symm⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and]
        exact fun _ ↦ hsep
    · refine ⟨(j, i), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hlt, (hIx j hj).trans (hIx i hi).symm⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and]
        exact fun _ h ↦ hsep h.symm

end Steps

section Main

variable {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A] [IsIntegrallyClosed A]
  [HenselianLocalRing A] [IsSepClosed (ResidueField A)] {n : ℕ}

theorem measure_lt_of_node {N N₁ P P₁ M : ℕ} (hN : N₁ < N) (hP₁ : P₁ ≤ M) :
    N₁ * (M + 1) + P₁ < N * (M + 1) + P := by
  have h1 : (N₁ + 1) * (M + 1) ≤ N * (M + 1) := Nat.mul_le_mul_right _ hN
  rw [Nat.succ_mul] at h1
  omega

open Classical in
/-- **The separation induction.** -/
theorem exists_separation_of_good {C : Scheme.{u}} {g : C ⟶ Spec (.of A)}
    {σ : Fin n → (Spec (.of A) ⟶ C)} (hgood : SeparationGood g σ) :
    ∃ (C' : Scheme.{u}) (β : C' ⟶ C) (σ' : Fin n → (Spec (.of A) ⟶ C')),
      IsModification β ∧ SeparationGood (β ≫ g) σ' ∧ (∀ k, σ' k ≫ β = σ k) ∧
      (∀ k, HasSmoothChart (β ≫ g) (σ' k (closedPoint A))) ∧
      (∀ k l, k ≠ l → σ' k (closedPoint A) ≠ σ' l (closedPoint A)) := by
  suffices H : ∀ m (C : Scheme.{u}) (g : C ⟶ Spec (.of A)) (σ : Fin n → (Spec (.of A) ⟶ C)),
      SeparationGood g σ → separationMeasure g σ = m →
      ∃ (C' : Scheme.{u}) (β : C' ⟶ C) (σ' : Fin n → (Spec (.of A) ⟶ C')),
        IsModification β ∧ SeparationGood (β ≫ g) σ' ∧ (∀ k, σ' k ≫ β = σ k) ∧
        (∀ k, HasSmoothChart (β ≫ g) (σ' k (closedPoint A))) ∧
        (∀ k l, k ≠ l → σ' k (closedPoint A) ≠ σ' l (closedPoint A)) from
    H _ C g σ hgood rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro C g σ hgood hm
  have := hgood.integral
  -- recursion on a step
  have recurse : ∀ (C₁ : Scheme.{u}) (β : C₁ ⟶ C) (σ₁ : Fin n → (Spec (.of A) ⟶ C₁)),
      IsModification β → SeparationGood (β ≫ g) σ₁ → (∀ k, σ₁ k ≫ β = σ k) →
      separationMeasure (β ≫ g) σ₁ < m →
      ∃ (C' : Scheme.{u}) (β' : C' ⟶ C) (σ' : Fin n → (Spec (.of A) ⟶ C')),
        IsModification β' ∧ SeparationGood (β' ≫ g) σ' ∧ (∀ k, σ' k ≫ β' = σ k) ∧
        (∀ k, HasSmoothChart (β' ≫ g) (σ' k (closedPoint A))) ∧
        (∀ k l, k ≠ l → σ' k (closedPoint A) ≠ σ' l (closedPoint A)) := by
    intro C₁ β σ₁ hβ hgood₁ hσ₁ hlt
    obtain ⟨C', β', σ', hβ', hgood', hσ', hch', hdisj'⟩ := ih _ hlt C₁ (β ≫ g) σ₁ hgood₁ rfl
    refine ⟨C', β' ≫ β, σ', IsModification.comp β' β, ?_, fun k ↦ ?_, ?_, hdisj'⟩
    · rw [Category.assoc]; exact hgood'
    · rw [← Category.assoc, hσ', hσ₁]
    · rw [Category.assoc]; exact hch'
  by_cases hN : ∃ k₀, ¬ HasSmoothChart g (σ k₀ (closedPoint A))
  · obtain ⟨k₀, hk₀⟩ := hN
    obtain ⟨C₁, β, σ₁, hβ, hgood₁, hσ₁, hlt, hle⟩ := exists_node_step hgood k₀ hk₀
    refine recurse C₁ β σ₁ hβ hgood₁ hσ₁ ?_
    rw [← hm]
    exact measure_lt_of_node hlt (numMeeting_le σ₁)
  push Not at hN
  by_cases hP : ∃ i j, i ≠ j ∧ σ i (closedPoint A) = σ j (closedPoint A)
  · obtain ⟨i, j, hij, hmeet⟩ := hP
    obtain ⟨C₁, β, σ₁, hβ, hgood₁, hσ₁, hch₁, hlt⟩ := exists_smooth_step hgood hN i j hij hmeet
    refine recurse C₁ β σ₁ hβ hgood₁ hσ₁ ?_
    have h0 : numNoChart g σ = 0 := by
      rw [numNoChart, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun k _ h ↦ h (hN k)
    have h1 : numNoChart (β ≫ g) σ₁ = 0 := by
      rw [numNoChart, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun k _ h ↦ h (hch₁ k)
    rw [← hm, separationMeasure, separationMeasure, h0, h1]
    omega
  push Not at hP
  exact ⟨C, 𝟙 C, σ, inferInstance, by rwa [Category.id_comp], fun k ↦ Category.comp_id _,
    fun k ↦ by rw [Category.id_comp]; exact hN k, hP⟩

/-- **Separation of the boundary** (M. Temkin, *Stable modification of relative curves*,
Lemma 4.3.2, T:3019–3046, for marks which are sections; `lem:sm-boundary-separation`). Let `A`
be a valuation ring which is henselian with separably closed residue field (for instance a
valuation ring with separably closed fraction field), `g : C ⟶ Spec A` separated with `C`
integral and `(C, ∅)` strictly semi-stable, and `σ₁, …, σₙ` pairwise distinct sections. There
is a modification `β : C' ⟶ C`, a composite of transported chart blow-ups, with `C' ⟶ Spec A`
separated and `(C', ∅)` strictly semi-stable, and sections `σ'ₖ` of `C'` lifting the `σₖ`, with
pairwise disjoint images contained in the smooth locus of `C' ⟶ Spec A`. -/
theorem exists_separation {C : Scheme.{u}} (g : C ⟶ Spec (.of A)) [IsSeparated g]
    [IsIntegral C] (hC : IsStrictlySemistable g ⊤) (σ : Fin n → (Spec (.of A) ⟶ C))
    (hσ : ∀ k, σ k ≫ g = 𝟙 _) (hinj : Function.Injective σ) :
    ∃ (C' : Scheme.{u}) (β : C' ⟶ C) (σ' : Fin n → (Spec (.of A) ⟶ C')),
      IsModification β ∧ IsSeparated (β ≫ g) ∧ IsStrictlySemistable (β ≫ g) ⊤ ∧
      (∀ k, σ' k ≫ β = σ k) ∧
      (∀ k l, k ≠ l → Disjoint (Set.range (σ' k)) (Set.range (σ' l))) ∧
      ∀ k (t : Spec (.of A)), DeJong.IsSmoothAt (β ≫ g) (σ' k t) := by
  obtain ⟨C', β, σ', hβ, hgood', hσ', hch', hdisj'⟩ :=
    exists_separation_of_good (g := g) ⟨inferInstance, inferInstance, hC, hσ, hinj⟩
  have := hgood'.separated
  refine ⟨C', β, σ', hβ, hgood'.separated, hgood'.semistable, hσ', fun k l hkl ↦ ?_,
    fun k t ↦ ?_⟩
  · exact disjoint_range_of_apply_closedPoint_ne (β ≫ g) (σ' k) (σ' l) (hgood'.isSection k)
      (hgood'.isSection l) (hdisj' k l hkl)
  · exact ((hch' k).of_specializes ((specializes_closedPoint t).map (σ' k).continuous)).isSmoothAt

end Main

end DeJongAlterations.StableModification.Blowups
