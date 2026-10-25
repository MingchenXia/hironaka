/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane T45D)
-/
import DeJongAlterations.StableModification.Gluing.SeparationProjectiveTransport

/-!
# Separation of marks with projectivity tracked

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), Lemma 4.3.2
(`divlem`, T:3019–3046), for marks which are sections, **with the projectivity of the
modification** (`PLAN-T5.md` §2.2 step 4, node A4, the marks part). Lane BND proved the lemma
(`Blowups.exists_separation_marks`) by an induction on the pair `(N, P)` (lexicographically), `N`
the number of sections whose closed point has no smooth chart and `P` the number of pairs of
sections meeting at the closed fibre, with two kinds of steps. This file reruns the induction with
the invariant "the modification **preserves projectivity**"
(`CofinalProjective.PreservesProjective`: it is projective over every ring over which its target is projective and of finite presentation),
exactly as lane T45C did for Proposition 4.3.1:

* **node step** (`exists_node_step_projective`): at the origin `x` of a node chart `uv = a` through
  which sections `(cₖ, dₖ)` pass, BND blows up `(u, π)`, `π = c_m` of minimal valuation; its centre
  `V(u, π)` is a curve and its trivial extension is not known to be projective. Instead let `π` be,
  among **all** the coordinates `cₖ, dₖ`, one of minimal valuation; after exchanging `u` and `v` it
  is some `c_m`. Then `π` divides every `cₖ` and `dₖ`, so `a = π²b`, and we blow up `(u, v, π)`
  (lane T45C's `Gluing.LocusBlowup`), whose centre is the modification locus. Every section
  through `x` lifts to the `π`-chart `(u/π)(v/π) = b` at `(cₖ/π, dₖ/π)` (`piLift`), and the lift
  of `σ_m` is `(1, d_m/π)`, a point of the smooth open `u/π ≠ 0`: `N` drops;
* **smooth step** (`exists_smooth_step_projective`): BND's blow-up `Bl_{(π, T - c_i)}` of a smooth
  chart, whose centre is the modification locus; `P` drops.

Each step is an extended chart blow-up with centre the modification locus, transported along an
affine neighbourhood (`exists_locusBlowup_transport_projective`,
`exists_smoothBlowup_transport_projective`), hence the blow-up of an ideal sheaf of finite type,
which preserves projectivity by SERRE-I.

## Main results

* `exists_separation_of_good_projective`: the induction;
* `exists_separation_marks_projective` (**Lemma 4.3.2 for sections, with projectivity**): BND's
  `Blowups.exists_separation_marks` together with `PreservesProjective β`.

Blueprint: `sm-gluing-separation-projective.tex`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing Polynomial

universe u

namespace DeJongAlterations.StableModification.Gluing.SeparationProjective

open Curves Blowups Algebra.NodeBlowupChart
open CofinalProjective (PreservesProjective)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Steps

variable {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A] [IsIntegrallyClosed A]
  [HenselianLocalRing A] [IsSepClosed (ResidueField A)] {C : Scheme.{u}} {n : ℕ}

attribute [local instance] LocusBlowup.fact_mul_ne_zero

omit [ValuationRing A] in
open Classical in
/-- **The projective node step, with a coordinate dividing all others** (the projective
replacement of BND's `Blowups.exists_node_step`; Temkin, Lemma 4.3.2, T:3036–3046). Let the closed
point `x = σ_{k₀}(s)` have no smooth chart, `φ : U → Spec A[u,v]/(uv - a)` a node chart at `x`, the
sections through `x` given by `(cₖ, dₖ)`, and `c_{m₀}` dividing every `cₖ` and `dₖ`. Then
`a = c_{m₀}² b`, and the transported blow-up of `(u, v, c_{m₀})` gives lifts with fewer closed
points without smooth chart and no new meetings; it is a modification which preserves projectivity. -/
theorem exists_node_step_projective_aux {g : C ⟶ Spec (.of A)} {σ : Fin n → (Spec (.of A) ⟶ C)}
    (hgood : SeparationGood g σ) (k₀ : Fin n)
    (hk₀ : ¬ HasSmoothChart g (σ k₀ (closedPoint A))) (U : C.Opens)
    (hxU : σ k₀ (closedPoint A) ∈ U) (a : A) (φ : U.toScheme ⟶ Spec (.of (Node A a))) [Etale φ]
    (hφ : φ ≫ nodeModel a = U.ι ≫ g) (c d : Fin n → A)
    (hcd : ∀ k, σ k (closedPoint A) = σ k₀ (closedPoint A) → c k * d k = a)
    (hfac : ∀ k (hk : σ k (closedPoint A) = σ k₀ (closedPoint A)),
      factorThruOpen (σ k) U (by rw [hk]; exact hxU) ≫ φ =
        Spec.map (CommRingCat.ofHom (nodePoint a (c k) (d k) (hcd k hk)).toRingHom))
    (m₀ : Fin n) (hm₀ : σ m₀ (closedPoint A) = σ k₀ (closedPoint A))
    (hdvd : ∀ k, σ k (closedPoint A) = σ k₀ (closedPoint A) → c m₀ ∣ c k ∧ c m₀ ∣ d k) :
    ∃ (C₁ : Scheme.{u}) (β : C₁ ⟶ C) (σ₁ : Fin n → (Spec (.of A) ⟶ C₁)),
      IsModification β ∧ PreservesProjective β ∧ SeparationGood (β ≫ g) σ₁ ∧
      (∀ k, σ₁ k ≫ β = σ k) ∧ numNoChart (β ≫ g) σ₁ < numNoChart g σ ∧
      numMeeting σ₁ ≤ numMeeting σ := by
  have := hgood.separated
  have hCint := hgood.integral
  set x := σ k₀ (closedPoint A) with hxdef
  have hx : g x = closedPoint A := by
    rw [hxdef, ← Scheme.Hom.comp_apply, hgood.isSection]; rfl
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
  have hpt : ∀ k (hk : σ k (closedPoint A) = x), Spec.map (CommRingCat.ofHom
      (nodePoint a (c k) (d k) (hcd k hk)).toRingHom) (closedPoint A) = φ ⟨x, hxU⟩ := by
    intro k hk
    rw [← hfac k hk, Scheme.Hom.comp_apply, factorThruOpen_closedPoint]
    congr 1
    exact Subtype.ext hk
  have hcm : c m₀ ∈ maximalIdeal A := by
    have h := hu0
    rw [← hpt m₀ hm₀, specMap_nodePoint_closedPoint_asIdeal, Ideal.mem_comap] at h
    simpa using h
  -- `a = π²b` with `π = c m₀`
  obtain ⟨b, hb⟩ := (hdvd m₀ hm₀).2
  have hab : a = c m₀ * (c m₀ * b) := by rw [← hcd m₀ hm₀, hb]
  subst hab
  have hπ : c m₀ ≠ 0 := left_ne_zero_of_mul ha
  have hb0 : b ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul ha)
  have : Fact (c m₀ ≠ 0) := ⟨hπ⟩
  have : Fact (b ≠ 0) := ⟨hb0⟩
  -- the centre `V(u, v, π)` passes through `φ x`
  have hxi : φ ⟨x, hxU⟩ ∈ Set.range (nodeLocus (c m₀) (c m₀ * b)) := by
    rw [range_nodeLocus]
    simp only [nodeLocusComplement, Set.mem_compl_iff, Opens.coe_sup, Set.mem_union,
      SetLike.mem_coe, not_or]
    exact ⟨⟨fun h ↦ h hu0, fun h ↦ h hu1⟩,
      fun h ↦ h ((algebraMap_mem_iff_of_nodeModel_eq _ hφx _).mpr hcm)⟩
  obtain ⟨U₀, hU₀, W, C₁, β, j, kW, hxU₀, -, -, huniq, hj, hkW, hjβ, hkβ, -, -, -, hss, hmod,
      hproj⟩ :=
    exists_locusBlowup_transport_projective (c m₀) b g hgood.semistable U φ hφ x hxU hx hxi
  have : IsModification β := hmod hCint
  -- the lifts of the sections through `x` to the `π`-chart
  have hlift : ∀ k, σ k (closedPoint A) = x →
      ∃ c' d' : A, c k = c m₀ * c' ∧ d k = c m₀ * d' ∧ c' * d' = b := by
    intro k hk
    obtain ⟨⟨c', hc'⟩, ⟨d', hd'⟩⟩ := hdvd k hk
    refine ⟨c', d', hc', hd', ?_⟩
    apply mul_left_cancel₀ (mul_ne_zero hπ hπ)
    have h := hcd k hk
    rw [hc', hd'] at h
    linear_combination h
  choose! c' d' hc' hd' hc'd' using hlift
  let τ : Fin n → (Spec (.of A) ⟶ affineBlowup (LocusBlowup.locusIdeal (c m₀) b)) := fun k ↦
    if hk : σ k (closedPoint A) = x then piLift (c m₀) b (c' k) (d' k) (hc'd' k hk)
    else piLift (c m₀) b 1 b (one_mul b)
  have hτ : ∀ k (hk : σ k (closedPoint A) = x), τ k ≫ affineBlowupStructure
      (LocusBlowup.locusIdeal (c m₀) b) = factorThruOpen (σ k) U₀ (by rw [hk]; exact hxU₀) ≫
        (C.homOfLE hU₀ ≫ φ) := by
    intro k hk
    simp only [τ, dif_pos hk]
    rw [piLift_comp, ← Category.assoc, factorThruOpen_homOfLE (σ k) hU₀ _ (by rw [hk]; exact hxU),
      hfac k hk]
    congr 3
    exact nodePoint_congr _ (hc' k hk).symm (hd' k hk).symm _ _
  obtain ⟨σ₁, hσ₁β, hσ₁chart, hσ₁rest⟩ := exists_lifts g (C.homOfLE hU₀ ≫ φ)
    (affineBlowupStructure (LocusBlowup.locusIdeal (c m₀) b)) β j kW hjβ hkβ x hxU₀ huniq σ
    hgood.isSection τ hτ
  refine ⟨C₁, β, σ₁, inferInstance, hproj hCint, separationGood_of_lift hgood β hss hσ₁β, hσ₁β,
    ?_, numMeeting_le_of_lift β hσ₁β⟩
  -- `N` drops
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_of_subset (fun k hk ↦ ?_) |>.mpr ⟨m₀, ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    intro hch
    by_cases hkx : σ k (closedPoint A) = x
    · exact hk₀ (hkx ▸ hch)
    · exact hk (hσ₁rest k hkx hch)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hm₀]
    exact hk₀
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
    obtain ⟨p, hp, hpfst⟩ := hσ₁chart m₀ hm₀
    rw [hp]
    have hc'₀ : c' m₀ = 1 := by
      apply mul_left_cancel₀ hπ
      rw [mul_one, ← hc' m₀ hm₀]
    have hτm : τ m₀ = piLift (c m₀) b (c' m₀) (d' m₀) (hc'd' m₀ hm₀) := by
      simp only [τ, dif_pos hm₀]
    rw [hτm, piLift, Scheme.Hom.comp_apply] at hpfst
    refine hasSmoothChart_of_nodeChart_lift (β ≫ g) j
      (pullback.fst (affineBlowupStructure (LocusBlowup.locusIdeal (c m₀) b))
        (C.homOfLE hU₀ ≫ φ))
      (affineBlowupStructure (LocusBlowup.locusIdeal (c m₀) b) ≫ nodeModel (c m₀ * (c m₀ * b)))
      ?_ b (LocusBlowup.piChartInclusion (c m₀) b) ?_ p _ hpfst.symm 0 ?_
    · rw [← Category.assoc, pullback.condition, Category.assoc, Category.assoc, hφ,
        ← Category.assoc (C.homOfLE hU₀), Scheme.homOfLE_ι, ← Category.assoc, ← hjβ,
        Category.assoc]
    · exact LocusBlowup.piChartInclusion_morphism (c m₀) b
    · exact specMap_nodePoint_closedPoint_mem_coordinateOpen₀ _ _ _ _
        (by rw [hc'₀]; exact isUnit_one)

open Classical in
/-- **The projective node step** (Temkin, Lemma 4.3.2, T:3036–3046, with the blow-up of
`(u, v, π)` of `Gluing.LocusBlowup`; the projective form of BND's `Blowups.exists_node_step`). If
the closed point `x = σ_{k₀}(s)` has no smooth chart, a node chart at `x` and, among the
coordinates `cₖ, dₖ` of the sections through `x`, one `π` of minimal valuation (after exchanging
`u` and `v`, `π = c_m`) give a transported blow-up of `(u, v, π)` with lifts with fewer closed
points without smooth chart and no new meetings; it is a modification preserving projectivity. -/
theorem exists_node_step_projective {g : C ⟶ Spec (.of A)} {σ : Fin n → (Spec (.of A) ⟶ C)}
    (hgood : SeparationGood g σ) (k₀ : Fin n)
    (hk₀ : ¬ HasSmoothChart g (σ k₀ (closedPoint A))) :
    ∃ (C₁ : Scheme.{u}) (β : C₁ ⟶ C) (σ₁ : Fin n → (Spec (.of A) ⟶ C₁)),
      IsModification β ∧ PreservesProjective β ∧ SeparationGood (β ≫ g) σ₁ ∧
      (∀ k, σ₁ k ≫ β = σ k) ∧ numNoChart (β ≫ g) σ₁ < numNoChart g σ ∧
      numMeeting σ₁ ≤ numMeeting σ := by
  have := hgood.separated
  set x := σ k₀ (closedPoint A) with hxdef
  have hx : g x = closedPoint A := by
    rw [hxdef, ← Scheme.Hom.comp_apply, hgood.isSection]; rfl
  obtain ⟨U, hxU, hcase⟩ := exists_chart hgood.semistable x hx
  rcases hcase with ⟨e, he, hφ⟩ | ⟨a, φ, hφe, hφ⟩
  · have := he
    exact absurd (hasSmoothChart_of_etale g U e hφ x hxU) hk₀
  have : Etale φ := hφe
  -- the coordinates of the sections through `x`
  have hcoord : ∀ k, ∃ (c d : A) (h : σ k (closedPoint A) = x → c * d = a),
      ∀ hk : σ k (closedPoint A) = x, factorThruOpen (σ k) U (by rw [hk]; exact hxU) ≫ φ =
        Spec.map (CommRingCat.ofHom (nodePoint a c d (h hk)).toRingHom) := by
    intro k
    by_cases hk : σ k (closedPoint A) = x
    · obtain ⟨c, d, h, hf⟩ := exists_eq_specMap_nodePoint a
        (factorThruOpen (σ k) U (by rw [hk]; exact hxU) ≫ φ) (by
          rw [Category.assoc, hφ, ← Category.assoc, factorThruOpen_ι, hgood.isSection])
      exact ⟨c, d, fun _ ↦ h, fun _ ↦ hf⟩
    · exact ⟨0, 0, fun h ↦ absurd h hk, fun h ↦ absurd h hk⟩
  choose c d hcd hfac using hcoord
  -- the coordinates of minimal valuation
  let I := Finset.univ.filter fun k ↦ σ k (closedPoint A) = x
  have hk₀I : k₀ ∈ I := by simp [I, hxdef]
  have hIx : ∀ k ∈ I, σ k (closedPoint A) = x := fun k hk ↦ (Finset.mem_filter.mp hk).2
  have hxI : ∀ k, σ k (closedPoint A) = x → k ∈ I := fun k hk ↦
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
  obtain ⟨m₁, hm₁, hdvd₁⟩ := exists_dvd_all I ⟨k₀, hk₀I⟩ c
  obtain ⟨m₂, hm₂, hdvd₂⟩ := exists_dvd_all I ⟨k₀, hk₀I⟩ d
  rcases ValuationRing.dvd_total (c m₁) (d m₂) with h12 | h21
  · exact exists_node_step_projective_aux hgood k₀ hk₀ U hxU a φ hφ c d hcd hfac m₁ (hIx m₁ hm₁)
      fun k hk ↦ ⟨hdvd₁ k (hxI k hk), h12.trans (hdvd₂ k (hxI k hk))⟩
  -- exchange `u` and `v`
  let sw : CommRingCat.of (Node A a) ⟶ CommRingCat.of (Node A a) :=
    (nodeSwap a).toRingEquiv.toCommRingCatIso.hom
  have : IsIso (Spec.map sw) := inferInstance
  let φ' := φ ≫ Spec.map sw
  have : Etale φ' := inferInstance
  have hsw : Spec.map sw ≫ nodeModel a = nodeModel a := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext r : 2
    exact (nodeSwap a).commutes r
  have hφ' : φ' ≫ nodeModel a = U.ι ≫ g := by
    rw [Category.assoc, hsw, hφ]
  have hcd' : ∀ k, σ k (closedPoint A) = x → d k * c k = a := fun k hk ↦ by
    rw [mul_comm]
    exact hcd k hk
  have hfac' : ∀ k (hk : σ k (closedPoint A) = x),
      factorThruOpen (σ k) U (by rw [hk]; exact hxU) ≫ φ' =
        Spec.map (CommRingCat.ofHom (nodePoint a (d k) (c k) (hcd' k hk)).toRingHom) := by
    intro k hk
    rw [← Category.assoc, hfac k hk, ← Spec.map_comp]
    congr 1
    refine CommRingCat.hom_ext ?_
    have : (nodePoint a (c k) (d k) (hcd k hk)).comp (nodeSwap a).toAlgHom =
        nodePoint a (d k) (c k) (hcd' k hk) := by
      apply node_algHom_ext
      · change nodePoint a (c k) (d k) (hcd k hk) (nodeSwap a (coordinate a 0)) = _
        rw [nodeSwap_coordinate0]
        simp
      · change nodePoint a (c k) (d k) (hcd k hk) (nodeSwap a (coordinate a 1)) = _
        rw [nodeSwap_coordinate1]
        simp
    exact congrArg AlgHom.toRingHom this
  exact exists_node_step_projective_aux hgood k₀ hk₀ U hxU a φ' hφ' d c hcd' hfac' m₂
    (hIx m₂ hm₂) fun k hk ↦ ⟨hdvd₂ k (hxI k hk), h21.trans (hdvd₁ k (hxI k hk))⟩

open Classical in
/-- **The projective smooth step** (BND's `Blowups.exists_smooth_step` with the transport of
`exists_smoothBlowup_transport_projective`). If all closed points of the sections have smooth
charts and two sections meet at `x`, a transported smooth blow-up `Bl_{(π, T - c_i)}`,
`π = c_i - c_j` of minimal valuation among the differences of the coordinates of the sections
through `x`, gives lifts whose closed points all have smooth charts and with fewer meeting pairs;
it is a modification preserving projectivity. -/
theorem exists_smooth_step_projective {g : C ⟶ Spec (.of A)} {σ : Fin n → (Spec (.of A) ⟶ C)}
    (hgood : SeparationGood g σ) (hN : ∀ k, HasSmoothChart g (σ k (closedPoint A)))
    (i₀ j₀ : Fin n) (hij₀ : i₀ ≠ j₀) (hmeet : σ i₀ (closedPoint A) = σ j₀ (closedPoint A)) :
    ∃ (C₁ : Scheme.{u}) (β : C₁ ⟶ C) (σ₁ : Fin n → (Spec (.of A) ⟶ C₁)),
      IsModification β ∧ PreservesProjective β ∧ SeparationGood (β ≫ g) σ₁ ∧
      (∀ k, σ₁ k ≫ β = σ k) ∧ (∀ k, HasSmoothChart (β ≫ g) (σ₁ k (closedPoint A))) ∧
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
  obtain ⟨U₀, hU₀, W, C₁, β, j', kW, hxU₀, -, -, huniq, hj', hkW, hjβ, hkβ, -, -, -, hss, hmod,
      hproj⟩ :=
    exists_smoothBlowup_transport_projective (c i - c j) (c i) g hgood.semistable U φ hφ x hxU hx
      hxi
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
  refine ⟨C₁, β, σ₁, inferInstance, hproj hCint, separationGood_of_lift hgood β hss hσ₁β, hσ₁β,
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

/-- A morphism between strictly semi-stable curves over `A` is locally of finite
presentation. -/
theorem locallyOfFinitePresentation_of_isStrictlySemistable {A : Type u} [CommRing A]
    {C C₁ : Scheme.{u}}
    {g : C ⟶ Spec (.of A)} (hC : IsStrictlySemistable g ⊤) (β : C₁ ⟶ C)
    (hC₁ : IsStrictlySemistable (β ≫ g) ⊤) : LocallyOfFinitePresentation β := by
  have : DeJong.IsNodalCurve g := hC.isNodalCurve
  have : DeJong.IsNodalCurve (β ≫ g) := hC₁.isNodalCurve
  exact locallyOfFinitePresentation_of_comp_of_locallyOfFiniteType β g

section Main

variable {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A] [IsIntegrallyClosed A]
  [HenselianLocalRing A] [IsSepClosed (ResidueField A)] {n : ℕ}

open Classical in
/-- **The separation induction with projectivity** (BND's `Blowups.exists_separation_of_good`,
with the invariant `PreservesProjective`). -/
theorem exists_separation_of_good_projective {C : Scheme.{u}} {g : C ⟶ Spec (.of A)}
    {σ : Fin n → (Spec (.of A) ⟶ C)} (hgood : SeparationGood g σ) :
    ∃ (C' : Scheme.{u}) (β : C' ⟶ C) (σ' : Fin n → (Spec (.of A) ⟶ C')),
      IsModification β ∧ PreservesProjective β ∧ SeparationGood (β ≫ g) σ' ∧
      (∀ k, σ' k ≫ β = σ k) ∧ (∀ k, HasSmoothChart (β ≫ g) (σ' k (closedPoint A))) ∧
      (∀ k l, k ≠ l → σ' k (closedPoint A) ≠ σ' l (closedPoint A)) := by
  suffices H : ∀ m (C : Scheme.{u}) (g : C ⟶ Spec (.of A)) (σ : Fin n → (Spec (.of A) ⟶ C)),
      SeparationGood g σ → separationMeasure g σ = m →
      ∃ (C' : Scheme.{u}) (β : C' ⟶ C) (σ' : Fin n → (Spec (.of A) ⟶ C')),
        IsModification β ∧ PreservesProjective β ∧ SeparationGood (β ≫ g) σ' ∧
        (∀ k, σ' k ≫ β = σ k) ∧ (∀ k, HasSmoothChart (β ≫ g) (σ' k (closedPoint A))) ∧
        (∀ k l, k ≠ l → σ' k (closedPoint A) ≠ σ' l (closedPoint A)) from
    H _ C g σ hgood rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro C g σ hgood hm
  have := hgood.integral
  -- recursion on a step
  have recurse : ∀ (C₁ : Scheme.{u}) (β : C₁ ⟶ C) (σ₁ : Fin n → (Spec (.of A) ⟶ C₁)),
      IsModification β → PreservesProjective β → SeparationGood (β ≫ g) σ₁ →
      (∀ k, σ₁ k ≫ β = σ k) → separationMeasure (β ≫ g) σ₁ < m →
      ∃ (C' : Scheme.{u}) (β' : C' ⟶ C) (σ' : Fin n → (Spec (.of A) ⟶ C')),
        IsModification β' ∧ PreservesProjective β' ∧ SeparationGood (β' ≫ g) σ' ∧
        (∀ k, σ' k ≫ β' = σ k) ∧ (∀ k, HasSmoothChart (β' ≫ g) (σ' k (closedPoint A))) ∧
        (∀ k l, k ≠ l → σ' k (closedPoint A) ≠ σ' l (closedPoint A)) := by
    intro C₁ β σ₁ hβ hβp hgood₁ hσ₁ hlt
    obtain ⟨C', β', σ', hβ', hβ'p, hgood', hσ', hch', hdisj'⟩ :=
      ih _ hlt C₁ (β ≫ g) σ₁ hgood₁ rfl
    have : LocallyOfFinitePresentation β :=
      locallyOfFinitePresentation_of_isStrictlySemistable hgood.semistable β hgood₁.semistable
    refine ⟨C', β' ≫ β, σ', IsModification.comp β' β,
      PreservesProjective.comp hβ'p hβp, ?_, fun k ↦ ?_, ?_,
      hdisj'⟩
    · rw [Category.assoc]; exact hgood'
    · rw [← Category.assoc, hσ', hσ₁]
    · rw [Category.assoc]; exact hch'
  by_cases hN : ∃ k₀, ¬ HasSmoothChart g (σ k₀ (closedPoint A))
  · obtain ⟨k₀, hk₀⟩ := hN
    obtain ⟨C₁, β, σ₁, hβ, hβp, hgood₁, hσ₁, hlt, hle⟩ := exists_node_step_projective hgood k₀ hk₀
    refine recurse C₁ β σ₁ hβ hβp hgood₁ hσ₁ ?_
    rw [← hm]
    exact measure_lt_of_node hlt (numMeeting_le σ₁)
  push Not at hN
  by_cases hP : ∃ i j, i ≠ j ∧ σ i (closedPoint A) = σ j (closedPoint A)
  · obtain ⟨i, j, hij, hmeet⟩ := hP
    obtain ⟨C₁, β, σ₁, hβ, hβp, hgood₁, hσ₁, hch₁, hlt⟩ :=
      exists_smooth_step_projective hgood hN i j hij hmeet
    refine recurse C₁ β σ₁ hβ hβp hgood₁ hσ₁ ?_
    have h0 : numNoChart g σ = 0 := by
      rw [numNoChart, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun k _ h ↦ h (hN k)
    have h1 : numNoChart (β ≫ g) σ₁ = 0 := by
      rw [numNoChart, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun k _ h ↦ h (hch₁ k)
    rw [← hm, separationMeasure, separationMeasure, h0, h1]
    omega
  push Not at hP
  exact ⟨C, 𝟙 C, σ, inferInstance, preservesProjective_id C, by rwa [Category.id_comp],
    fun k ↦ Category.comp_id _, fun k ↦ by rw [Category.id_comp]; exact hN k, hP⟩

/-- **Separation of the boundary with projectivity** (M. Temkin, *Stable modification of
relative curves*, Lemma 4.3.2, T:3019–3046, for marks which are sections, with the projectivity of
the modification; `thm:sm-sep-proj-main`). Let `A` be a valuation ring which is henselian with
separably closed residue field (for instance a valuation ring of a separably closed field),
`g : C ⟶ Spec A` separated with `C` integral and `(C, ∅)` strictly semi-stable, and
`σ₁, …, σₙ` pairwise distinct sections. There is a modification `β : C' ⟶ C`, a composite of
transported chart blow-ups with centres the modification loci, such that

* `β` **preserves projectivity**: `C' ⟶ Spec E` is projective whenever `C ⟶ Spec E` is projective
  and locally of finite presentation;
* `C' ⟶ Spec A` is separated and the lifts `σ'ₖ` of the sections have pairwise disjoint images;
* `(C', ⋂ₖ ker σ'ₖ)` is strictly semi-stable, hence a semi-stable pair.

This is BND's `Blowups.exists_separation_marks` with the first conclusion added. -/
theorem exists_separation_marks_projective {C : Scheme.{u}} (g : C ⟶ Spec (.of A))
    [IsSeparated g] [IsIntegral C] (hC : IsStrictlySemistable g ⊤)
    (σ : Fin n → (Spec (.of A) ⟶ C)) (hσ : ∀ k, σ k ≫ g = 𝟙 _) (hinj : Function.Injective σ) :
    ∃ (C' : Scheme.{u}) (β : C' ⟶ C) (σ' : Fin n → (Spec (.of A) ⟶ C')),
      IsModification β ∧ PreservesProjective β ∧ IsSeparated (β ≫ g) ∧
      (∀ k, σ' k ≫ β = σ k) ∧
      (∀ k l, k ≠ l → Disjoint (Set.range (σ' k)) (Set.range (σ' l))) ∧
      ((⨅ k, (σ' k).ker).support : Set C') = ⋃ k, Set.range (σ' k) ∧
      IsStrictlySemistable (β ≫ g) (⨅ k, (σ' k).ker) ∧
      DeJong.IsSemistablePair (β ≫ g) (⨅ k, (σ' k).ker) := by
  obtain ⟨C', β, σ', hβ, hβp, hgood', hσ', hch', hdisj'⟩ :=
    exists_separation_of_good_projective (g := g) ⟨inferInstance, inferInstance, hC, hσ, hinj⟩
  have := hgood'.separated
  have hdisj : ∀ k l, k ≠ l → Disjoint (Set.range (σ' k)) (Set.range (σ' l)) := fun k l hkl ↦
    disjoint_range_of_apply_closedPoint_ne (β ≫ g) (σ' k) (σ' l) (hgood'.isSection k)
      (hgood'.isSection l) (hdisj' k l hkl)
  have hss := isStrictlySemistable_marks (β ≫ g) hgood'.semistable σ' hgood'.isSection hdisj hch'
  exact ⟨C', β, σ', hβ, hβp, hgood'.separated, hσ', hdisj, support_iInf_ker σ' hgood'.isSection,
    hss, hss.isSemistablePair⟩

end Main

end DeJongAlterations.StableModification.Gluing.SeparationProjective
