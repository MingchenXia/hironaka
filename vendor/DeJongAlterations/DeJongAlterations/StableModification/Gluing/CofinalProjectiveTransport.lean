/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane T45C)
-/
import DeJongAlterations.StableModification.Gluing.BlowupProjective
import DeJongAlterations.StableModification.Gluing.BlowupProjectiveNode
import DeJongAlterations.StableModification.LocalUniformization.GlobalTransport

/-!
# Projective global transport of chart blow-ups

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), proof of
Proposition 4.3.1 (T:2970–2983): a chart blow-up `Bl_I M → M` of a standard model `M = Spec A`,
spread along an étale chart `φ : U → M` of a strictly semi-stable curve `X → Spec O` near a closed
point `x` and extended trivially, is a strictly semi-stable modification of `X`. This file reproves
lane T43A's `LocalUniformization.exists_smoothBlowup_globalTransport` and
`exists_nodeBlowup_globalTransport` (and BND's `Blowups.exists_transport`, which they use) with
two changes, so that the result is **projective over `X`** (`PLAN-T5.md` node A4):

* the neighbourhood `V₀` of `x` over which the chart blow-up is pulled back is chosen **affine**
  (`exists_isAffineOpen_finite_subset`, prime avoidance), and the blow-up is extended by the
  identity in one step from `V₀` to `X`;
* the centre `V(I)` of the chart blow-up must be the modification locus itself (true for the
  smooth stage `Bl_{(π, T - a)}`; for the node stage we use `Bl_{(u, v, π)}` of
  `Gluing.LocusBlowup`, as `Bl_{(u, π)}` has a centre of dimension one).

Then the extension is a native blow-up of an ideal sheaf of finite type
(`BlowupProjective.isProjectiveOver_extensionHom`), projective over `X` by SERRE-I.

## Main results

* `exists_isAffineOpen_finite_subset`: a finite subset of an open `U₀` of an affine open lies in
  an affine open contained in `U₀`;
* `exists_blowup_globalTransport_projective`: the transport for a general chart blow-up with
  centre equal to the locus;
* `exists_smoothBlowup_globalTransport_projective`, `exists_locusBlowup_globalTransport_projective`:
  the two stages.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing Polynomial

universe u

namespace DeJongAlterations.StableModification.Gluing.CofinalProjective

open DeJongAlterations Curves Blowups LocalUniformization Algebra.NodeBlowupChart

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Avoidance

/-- **Prime avoidance for affine opens**: a finite set `Z` of points of an open `U₀` contained in
an affine open `U₁` lies in an affine open `V ⊆ U₀` (a basic open of `U₁`). -/
theorem exists_isAffineOpen_finite_subset {Y : Scheme.{u}} {U₁ U₀ : Y.Opens} (hU₁ : IsAffineOpen U₁)
    (h : U₀ ≤ U₁) {Z : Set Y} (hZ : Z.Finite) (hZU : Z ⊆ U₀) :
    ∃ V : Y.Opens, IsAffineOpen V ∧ V ≤ U₀ ∧ Z ⊆ V := by
  classical
  by_cases hZe : Z = ∅
  · exact ⟨⊥, isAffineOpen_bot _, bot_le, by simp [hZe]⟩
  obtain ⟨z₀, -⟩ := Set.nonempty_iff_ne_empty.mpr hZe
  -- the functions on `U₁` whose basic open lies in `U₀`
  let 𝔞 : Ideal Γ(Y, U₁) :=
    { carrier := {f | Y.basicOpen f ≤ U₀}
      zero_mem' := by
        change Y.basicOpen (0 : Γ(Y, U₁)) ≤ U₀
        rw [Scheme.basicOpen_zero]
        exact bot_le
      add_mem' := fun {f g} hf hg ↦ (Y.basicOpen_add_le f g).trans (sup_le hf hg)
      smul_mem' := fun r f hf ↦ by
        change Y.basicOpen (r * f) ≤ U₀
        rw [Scheme.basicOpen_mul]
        exact inf_le_right.trans hf }
  -- the prime of a point of `U₁`
  let 𝔭 : Y → Ideal Γ(Y, U₁) := fun z ↦
    { carrier := {f | z ∉ Y.basicOpen f}
      zero_mem' := by
        change z ∉ Y.basicOpen (0 : Γ(Y, U₁))
        rw [Scheme.basicOpen_zero]
        exact fun h ↦ h
      add_mem' := fun {f g} hf hg h ↦ by
        rcases Y.basicOpen_add_le f g h with h | h
        · exact hf h
        · exact hg h
      smul_mem' := fun r f hf h ↦ by
        change z ∈ Y.basicOpen (r * f) at h
        rw [Scheme.basicOpen_mul] at h
        exact hf h.2 }
  have h𝔭 : ∀ z ∈ Z, (𝔭 z).IsPrime := by
    intro z hz
    refine ⟨fun htop ↦ ?_, fun {f g} hfg ↦ ?_⟩
    · have h1 : (1 : Γ(Y, U₁)) ∈ 𝔭 z := htop ▸ Submodule.mem_top
      apply h1
      rw [Scheme.basicOpen_one]
      exact h (hZU hz)
    · by_contra hc
      rw [not_or] at hc
      apply hfg
      rw [Scheme.basicOpen_mul]
      exact ⟨not_not.mp hc.1, not_not.mp hc.2⟩
  have hnot : ∀ z ∈ Z, ¬ 𝔞 ≤ 𝔭 z := by
    intro z hz hle
    obtain ⟨f, hfU, hzf⟩ := hU₁.exists_basicOpen_le (V := U₀) ⟨z, hZU hz⟩ (h (hZU hz))
    exact hle hfU hzf
  have hav : ¬ ((𝔞 : Set Γ(Y, U₁)) ⊆ ⋃ z ∈ (↑hZ.toFinset : Set Y), (𝔭 z : Set Γ(Y, U₁))) := by
    intro hsub
    have hp : ∀ i ∈ hZ.toFinset, i ≠ z₀ → i ≠ z₀ → (𝔭 i).IsPrime :=
      fun i hi _ _ ↦ h𝔭 i ((Set.Finite.mem_toFinset hZ).mp hi)
    obtain ⟨z, hz, hle⟩ := (Ideal.subset_union_prime _ _ hp).mp hsub
    exact hnot z ((Set.Finite.mem_toFinset hZ).mp hz) hle
  rw [Set.not_subset] at hav
  obtain ⟨f, hf, hfz⟩ := hav
  refine ⟨Y.basicOpen f, hU₁.basicOpen f, hf, fun z hz ↦ ?_⟩
  by_contra hzf
  exact hfz (Set.mem_iUnion₂.mpr ⟨z, (Set.Finite.mem_toFinset hZ).mpr hz, hzf⟩)

end Avoidance

section Transport

/-- The image of the points of an open `W ≤ U` mapping into `S` under `φ`. -/
theorem image_preimage_homOfLE {Y M : Scheme.{u}} {U W : Y.Opens} (hWU : W ≤ U)
    (φ : U.toScheme ⟶ M) (S : Set M) :
    W.ι '' ((Y.homOfLE hWU ≫ φ) ⁻¹' S) = (W : Set Y) ∩ U.ι '' (φ ⁻¹' S) := by
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w.2, Y.homOfLE hWU w, hw, ?_⟩
    rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
  · rintro ⟨hyW, u, hu, rfl⟩
    refine ⟨⟨U.ι u, hyW⟩, ?_, rfl⟩
    have h : Y.homOfLE hWU ⟨U.ι u, hyW⟩ = u := Subtype.ext (Scheme.homOfLE_apply _ _)
    change φ (Y.homOfLE hWU ⟨U.ι u, hyW⟩) ∈ S
    rw [h]
    exact hu

variable {K : Type u} [Field K] [IsSepClosed K] (O B : ValuationSubring K) (hOB : O ≤ B)
  [Finite (PrimeSpectrum O)]

/-- **Projective global transport of a chart blow-up** (Temkin, proof of Proposition 4.3.1,
T:2970–2983, with projectivity). Let `X → Spec O` be integral, separated and strictly semi-stable,
`x` a closed point of `X` over `𝔭 = 𝔪_B ∩ O`, `φ : U → M = Spec A` an étale chart of `X_B` at `x`
to a model over `B`, and `I ⊆ A` finitely generated with `Bl_I M` strictly semi-stable over `B`,
covered by spectra of integrally closed domains, and `φ(x) ∈ V(I)`, where `V(I)` is finite over a
closed subscheme `Spec A/I` of `Spec B` cut out by some `π ≠ 0`. Then there is a strictly
semi-stable modification `β : X₂ → X` such that every point of `X₂` over `x` lies in an open
`J(P)`, `P` étale over `Bl_I M` via `p₁` and over `U` via `p₂`, and **`X₂` is projective (and of
finite presentation) over every ring over which `X` is**. -/
theorem exists_blowup_globalTransport_projective {X : Scheme.{u}} [IsIntegral X]
    (g : X ⟶ Spec (.of O)) [IsSeparated g] (hX : IsStrictlySemistable g ⊤)
    {AM : Type u} [CommRing AM] [IsDomain AM] [Algebra B AM] (IM : Ideal AM) (hIM : IM.FG)
    (qM : Spec (.of AM) ⟶ Spec (.of B)) (hqM : qM = Spec.map (CommRingCat.ofHom (algebraMap B AM)))
    (hĀ : Function.Surjective (algebraMap B (AM ⧸ IM)))
    {π : B} (hπ : π ≠ 0) (hπĀ : algebraMap B (AM ⧸ IM) π = 0)
    (hM' : IsStrictlySemistable (affineBlowupStructure IM ≫ qM) ⊤)
    (hβ₀ : IsModification (affineBlowupStructure IM))
    (hcovM : ∀ m : affineBlowup IM, ∃ (C : Type u) (_ : CommRing C) (_ : IsDomain C)
      (_ : IsIntegrallyClosed C) (j : Spec (.of C) ⟶ affineBlowup IM) (_ : IsOpenImmersion j),
      m ∈ Set.range j)
    (U : (baseOpen O B hOB g).toScheme.Opens) (φ : U.toScheme ⟶ Spec (.of AM)) [Etale φ]
    (hφ : φ ≫ qM = U.ι ≫ baseRestrict O B hOB g)
    {x : X} (hxU' : x ∈ baseOpen O B hOB g)
    (hxU : (⟨x, hxU'⟩ : (baseOpen O B hOB g).toScheme) ∈ U) (hxcl : IsClosed ({x} : Set X))
    (hx : baseRestrict O B hOB g ⟨x, hxU'⟩ = closedPoint B)
    (hxi : φ ⟨⟨x, hxU'⟩, hxU⟩ ∈ Set.range (BlowupProjective.quotientMap IM)) :
    ∃ (X₂ : Scheme.{u}) (β : X₂ ⟶ X) (P : Scheme.{u}) (J : P ⟶ X₂)
      (p₁ : P ⟶ affineBlowup IM) (p₂ : P ⟶ U.toScheme),
      IsModification β ∧ IsStrictlySemistable (β ≫ g) ⊤ ∧ IsOpenImmersion J ∧ Etale p₁ ∧
      p₁ ≫ affineBlowupStructure IM = p₂ ≫ φ ∧
      J ≫ β = p₂ ≫ U.ι ≫ (baseOpen O B hOB g).ι ∧ (∀ y : X₂, β y = x → y ∈ Set.range J) ∧
      ∀ {E : Type u} [CommRing E] (p : X ⟶ Spec (.of E)), IsProjectiveOver p →
        LocallyOfFinitePresentation p → IsProjectiveOver (β ≫ p) := by
  have : IsClosedImmersion (BlowupProjective.quotientMap IM) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hi : (BlowupProjective.quotientMap IM) ≫ qM =
      Spec.map (CommRingCat.ofHom (algebraMap B (AM ⧸ IM))) := by
    rw [hqM]
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    rfl
  have hC' := isStrictlySemistable_baseRestrict O B hOB g hX
  obtain ⟨U₁, hU₁, hxU₁, hsub⟩ := exists_affine_le U hxU
  have : IsAffine U₁.toScheme := hU₁
  let φ₁ := (baseOpen O B hOB g).toScheme.homOfLE hsub ≫ φ
  have hφ₁ : φ₁ ≫ qM = U₁.ι ≫ (baseRestrict O B hOB g) := by
    rw [Category.assoc, hφ, ← Category.assoc, Scheme.homOfLE_ι]
  have hxi₁ : φ₁ ⟨⟨x, hxU'⟩, hxU₁⟩ ∈ Set.range (BlowupProjective.quotientMap IM) := by
    have hh : (baseOpen O B hOB g).toScheme.homOfLE hsub ⟨⟨x, hxU'⟩, hxU₁⟩ = ⟨⟨x, hxU'⟩, hxU⟩ :=
      Subtype.ext (Scheme.homOfLE_apply _ _)
    rw [Scheme.Hom.comp_apply, hh]
    exact hxi
  obtain ⟨U₀, hU₀, hxU₀, hZcl, huniq⟩ :=
    exists_open_isClosed_locus (baseRestrict O B hOB g) U₁ qM φ₁ hφ₁ hĀ
      (BlowupProjective.quotientMap IM) hi ⟨x, hxU'⟩ hxU₁ hx hxi₁
  set Z : Set (baseOpen O B hOB g).toScheme := (U₀ : Set (baseOpen O B hOB g).toScheme) ∩
    U₁.ι '' (φ₁ ⁻¹' Set.range (BlowupProjective.quotientMap IM)) with hZdef
  -- finiteness of the locus
  have : Finite (PrimeSpectrum B) := finite_primeSpectrum O B hOB
  have hfinĀ : Finite (Spec (.of (AM ⧸ IM))) :=
    Finite.of_injective _ (PrimeSpectrum.comap_injective_of_surjective _ hĀ)
  have : QuasiCompact φ₁ :=
    HasAffineProperty.iff_of_isAffine.mpr (inferInstance : CompactSpace U₁.toScheme)
  have hZfin : Z.Finite :=
    (((Set.finite_range _).preimage' fun _ _ ↦ φ₁.finite_preimage_singleton _).image _).subset
      Set.inter_subset_right
  -- an affine neighbourhood of the locus
  obtain ⟨V₀', hV₀', hV₀'U₀, hZV₀'⟩ :=
    exists_isAffineOpen_finite_subset hU₁ hU₀ hZfin Set.inter_subset_left
  have hxZ : (⟨x, hxU'⟩ : (baseOpen O B hOB g).toScheme) ∈ Z := ⟨hxU₀, ⟨⟨x, hxU'⟩, hxU₁⟩, hxi₁, rfl⟩
  have hV₀'U : V₀' ≤ U := hV₀'U₀.trans (hU₀.trans hsub)
  have hZeq : V₀'.ι '' (((baseOpen O B hOB g).toScheme.homOfLE hV₀'U ≫ φ) ⁻¹'
      Set.range (BlowupProjective.quotientMap IM)) = Z := by
    have h2 := image_preimage_homOfLE hsub φ (Set.range (BlowupProjective.quotientMap IM))
    rw [image_preimage_homOfLE]
    ext y
    constructor
    · rintro ⟨hyV, hy⟩
      refine ⟨hV₀'U₀ hyV, ?_⟩
      change y ∈ U₁.ι '' ((((baseOpen O B hOB g).toScheme.homOfLE hsub ≫ φ)) ⁻¹' _)
      rw [h2]
      exact ⟨hU₀ (hV₀'U₀ hyV), hy⟩
    · rintro ⟨hyU₀, hy⟩
      refine ⟨hZV₀' ⟨hyU₀, hy⟩, ?_⟩
      change y ∈ U₁.ι '' ((((baseOpen O B hOB g).toScheme.homOfLE hsub ≫ φ)) ⁻¹' _) at hy
      rw [h2] at hy
      exact hy.2
  -- the affine open `V₀` of `X` and the chart on it
  let V₀ : X.Opens := (baseOpen O B hOB g).ι ''ᵁ V₀'
  have hV₀ : IsAffineOpen V₀ := hV₀'.image_of_isOpenImmersion _
  let e : V₀'.toScheme ≅ V₀.toScheme :=
    IsOpenImmersion.isoOfRangeEq (V₀'.ι ≫ (baseOpen O B hOB g).ι) V₀.ι (by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
      Scheme.Opens.range_ι]
    rfl)
  have he : e.hom ≫ V₀.ι = V₀'.ι ≫ (baseOpen O B hOB g).ι :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have he' : V₀.ι =
      e.inv ≫ (baseOpen O B hOB g).toScheme.homOfLE hV₀'U ≫ U.ι ≫ (baseOpen O B hOB g).ι := by
    rw [← Category.assoc ((baseOpen O B hOB g).toScheme.homOfLE hV₀'U), Scheme.homOfLE_ι,
      Iso.eq_inv_comp, he]
  let φV : V₀.toScheme ⟶ Spec (.of AM) := e.inv ≫ (baseOpen O B hOB g).toScheme.homOfLE hV₀'U ≫ φ
  have : Flat φV := inferInstance
  have hφV : φV ≫ qM ≫ specInclusion O B hOB = V₀.ι ≫ g := by
    simp only [φV, Category.assoc]
    rw [reassoc_of% hφ, baseRestrict_comp, he']
    simp only [Category.assoc]
  -- the locus in `X`
  set T : Set X := (baseOpen O B hOB g).ι '' Z with hTdef
  have hTeq : V₀.ι '' (φV ⁻¹' Set.range (BlowupProjective.quotientMap IM)) = T := by
    rw [hTdef, ← hZeq, ← Set.image_comp]
    change (V₀.ι : V₀.toScheme → X) ''
      ((e.inv ≫ (baseOpen O B hOB g).toScheme.homOfLE hV₀'U ≫ φ) ⁻¹' _) = _
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp,
      ← Set.image_eq_preimage_of_inverse (f := e.hom) (g := e.inv) (fun a ↦ by simp)
        (fun a ↦ by simp), ← Set.image_comp]
    congr 1
    ext a
    change (e.hom ≫ V₀.ι) a = (V₀'.ι ≫ (baseOpen O B hOB g).ι) a
    rw [he]
  have hTfin : T.Finite := hZfin.image _
  have hTsub : ∀ z ∈ T, (g z).asIdeal ≤ O.idealOfLE B hOB := by
    rintro _ ⟨z, -, rfl⟩
    exact (mem_baseOpen_iff O B hOB g).mp z.2
  have hTcl : ∀ y ∈ closure T, (g y).asIdeal ≤ O.idealOfLE B hOB → y ∈ T := by
    intro y hy hle
    have hyU : y ∈ (baseOpen O B hOB g) := (mem_baseOpen_iff O B hOB g).mpr hle
    refine ⟨⟨y, hyU⟩, ?_, rfl⟩
    rw [← hZcl.closure_eq,
      (baseOpen O B hOB g).ι.isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image]
    exact hy
  have huniq' : ∀ y ∈ T, g y = specInclusion O B hOB (closedPoint B) → y = x := by
    rintro _ ⟨z, hz, rfl⟩ hgz
    have := huniq z hz ((baseRestrict_apply_eq_closedPoint_iff O B hOB g z).mpr hgz)
    rw [this]
    rfl
  have hTclosed : IsClosed T :=
    isClosed_of_finite_of_unique g (specInclusion O B hOB (closedPoint B)) hTfin hTsub hTcl
      hxcl huniq'
  have hxT : x ∈ T := ⟨⟨x, hxU'⟩, hxZ, rfl⟩
  let W₁ : X.Opens := ⟨Tᶜ, hTclosed.isOpen_compl⟩
  have hTV₀ : T ⊆ V₀ := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, hZV₀' hz, rfl⟩
  have hcov : V₀ ⊔ W₁ = ⊤ := by
    refine eq_top_iff.mpr fun y _ ↦ ?_
    by_cases hy : y ∈ T
    · exact Or.inl (hTV₀ hy)
    · exact Or.inr hy
  have hzero :
      PrimeSpectrum.zeroLocus (IM : Set AM) = Set.range (BlowupProjective.quotientMap IM) :=
    (BlowupProjective.range_quotientMap IM).symm
  have hW : V₀.ι ⁻¹ᵁ W₁ ≤ φV ⁻¹ᵁ affineBlowupCenterComplement IM := by
    intro v hv hvZ
    apply hv
    rw [← hTeq]
    refine ⟨v, ?_, rfl⟩
    rw [← hzero]
    exact hvZ
  have : IsIso ((affineBlowupStructure IM) ∣_ affineBlowupCenterComplement IM) :=
    affineBlowupStructure_centerComplement_isIso IM
  have : IsIso (pullback.snd (affineBlowupStructure IM) φV ∣_ (V₀.ι ⁻¹ᵁ W₁)) :=
    isIso_pullback_snd_restrict_of_le (affineBlowupStructure IM) φV _ hW
  have hT' : IsClosed (V₀.ι '' (φV ⁻¹' PrimeSpectrum.zeroLocus (IM : Set AM))) := by
    rw [hzero, hTeq]
    exact hTclosed
  -- a point off the locus
  have : DeJong.IsNodalCurve (baseRestrict O B hOB g) := hC'.isNodalCurve
  have : Nonempty (baseOpen O B hOB g).toScheme := ⟨⟨x, hxU'⟩⟩
  obtain ⟨y₀, hy₀⟩ := exists_not_mem_of_flat (baseRestrict O B hOB g) hπ
  have hW₁ne : (W₁ : Set X).Nonempty := by
    refine ⟨(baseOpen O B hOB g).ι y₀, ?_⟩
    rintro ⟨z, ⟨-, u₁, ⟨a, ha⟩, hu₁⟩, hz⟩
    have hzy : z = y₀ := (baseOpen O B hOB g).ι.isOpenEmbedding.injective hz
    subst hzy
    apply hy₀
    have h1 : (baseRestrict O B hOB g) (U₁.ι u₁) = qM (φ₁ u₁) := by
      rw [← Scheme.Hom.comp_apply, ← hφ₁, Scheme.Hom.comp_apply]
    rw [← hu₁, h1, ← ha, ← Scheme.Hom.comp_apply, hi]
    change π ∈ Ideal.comap (algebraMap B (AM ⧸ IM)) a.asIdeal
    rw [Ideal.mem_comap, hπĀ]
    exact a.asIdeal.zero_mem
  -- the extension
  have : IsReduced (pullback (affineBlowupStructure IM) φV) :=
    isReduced_of_etale_of_cover (pullback.fst (affineBlowupStructure IM) φV) hcovM
  have : IsModification (affineBlowupStructure IM) := hβ₀
  have hM'' : IsStrictlySemistable ((affineBlowupStructure IM) ≫ qM ≫ specInclusion O B hOB) ⊤ := by
    simpa only [Category.assoc] using
      Blowups.IsStrictlySemistable.comp_isOpenImmersion hM' (specInclusion O B hOB)
  refine ⟨extension W₁ (pullback.snd (affineBlowupStructure IM) φV),
    extensionHom W₁ (pullback.snd (affineBlowupStructure IM) φV),
    pullback (affineBlowupStructure IM) φV, extensionι₁ W₁ _,
    pullback.fst (affineBlowupStructure IM) φV,
    pullback.snd (affineBlowupStructure IM) φV ≫ e.inv ≫
      (baseOpen O B hOB g).toScheme.homOfLE hV₀'U,
    isModification_transport φV (affineBlowupStructure IM) W₁ hcov ⟨x, hTV₀ hxT⟩ hW₁ne,
    isStrictlySemistable_transport_top φV (affineBlowupStructure IM) W₁ g
      (qM ≫ specInclusion O B hOB) hφV hM'' hX,
    inferInstance, inferInstance, ?_, ?_, ?_, fun p hp hlfp ↦ ?_⟩
  · rw [pullback.condition]
    rfl
  · rw [extensionι₁_extensionHom, he']
    simp only [Category.assoc]
  · intro y hy
    rcases extension_jointly_surjective W₁ (pullback.snd (affineBlowupStructure IM) φV) y with
      h | ⟨w, rfl⟩
    · exact h
    · exfalso
      rw [extensionHom_ι₂_apply] at hy
      have : W₁.ι w ∈ (W₁ : Set X) := w.2
      rw [hy] at this
      exact this hxT
  · have := hlfp
    exact BlowupProjective.isProjectiveOver_extensionHom IM hV₀ φV W₁ hIM hcov hW hT' p hp

/-- **Projective global transport of the smooth chart blow-up** `Bl_{(π, T - a)}` (Temkin,
Prop 4.3.1, stage 2, T:2992–3016): `LocalUniformization.exists_smoothBlowup_globalTransport` with
the projectivity of the modification over every ring over which `X` is projective. -/
theorem exists_smoothBlowup_globalTransport_projective {X : Scheme.{u}} [IsIntegral X]
    (g : X ⟶ Spec (.of O)) [IsSeparated g] (hX : IsStrictlySemistable g ⊤) (π a : B)
    [Fact (π ≠ 0)] (U : (baseOpen O B hOB g).toScheme.Opens) (φ : U.toScheme ⟶ Spec (.of B[X]))
    [Etale φ] (hφ : φ ≫ smoothModel B = U.ι ≫ baseRestrict O B hOB g)
    {x : X} (hxU' : x ∈ baseOpen O B hOB g)
    (hxU : (⟨x, hxU'⟩ : (baseOpen O B hOB g).toScheme) ∈ U) (hxcl : IsClosed ({x} : Set X))
    (hx : baseRestrict O B hOB g ⟨x, hxU'⟩ = closedPoint B)
    (hxi : φ ⟨⟨x, hxU'⟩, hxU⟩ ∈ Set.range (smoothLocus π a)) :
    ∃ (X₂ : Scheme.{u}) (β : X₂ ⟶ X) (P : Scheme.{u}) (J : P ⟶ X₂)
      (p₁ : P ⟶ affineBlowup (smoothCenter π a)) (p₂ : P ⟶ U.toScheme),
      IsModification β ∧ IsStrictlySemistable (β ≫ g) ⊤ ∧ IsOpenImmersion J ∧ Etale p₁ ∧
      p₁ ≫ affineBlowupStructure (smoothCenter π a) = p₂ ≫ φ ∧
      J ≫ β = p₂ ≫ U.ι ≫ (baseOpen O B hOB g).ι ∧ (∀ y : X₂, β y = x → y ∈ Set.range J) ∧
      ∀ {E : Type u} [CommRing E] (p : X ⟶ Spec (.of E)), IsProjectiveOver p →
        LocallyOfFinitePresentation p → IsProjectiveOver (β ≫ p) := by
  have hπĀ : algebraMap B (B[X] ⧸ smoothCenter π a) π = 0 := by
    rw [IsScalarTower.algebraMap_apply B B[X], Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem, Polynomial.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply]
    exact C_mem_smoothCenter π a
  exact exists_blowup_globalTransport_projective O B hOB g hX (smoothCenter π a)
    (smoothCenter_fg π a) (smoothModel B) rfl (algebraMap_smoothLocus_surjective π a)
    (Fact.out : π ≠ 0) hπĀ (smoothBlowup_isStrictlySemistable π a)
    (smoothBlowup_isModification π a) (smoothBlowup_cover π a) U φ hφ hxU' hxU hxcl hx hxi

/-- **Projective global transport of the node-locus blow-up** `Bl_{(u, v, π)}` of
`B[u,v]/(uv - π²b)` (`Gluing.LocusBlowup`; the projective replacement of Temkin's stage 1). -/
theorem exists_locusBlowup_globalTransport_projective {X : Scheme.{u}} [IsIntegral X]
    (g : X ⟶ Spec (.of O)) [IsSeparated g] (hX : IsStrictlySemistable g ⊤) (π b : B)
    [Fact (π ≠ 0)] [Fact (b ≠ 0)] (U : (baseOpen O B hOB g).toScheme.Opens)
    (φ : U.toScheme ⟶ Spec (.of (Node B (π * (π * b))))) [Etale φ]
    (hφ : φ ≫ nodeModel (π * (π * b)) = U.ι ≫ baseRestrict O B hOB g)
    {x : X} (hxU' : x ∈ baseOpen O B hOB g)
    (hxU : (⟨x, hxU'⟩ : (baseOpen O B hOB g).toScheme) ∈ U) (hxcl : IsClosed ({x} : Set X))
    (hx : baseRestrict O B hOB g ⟨x, hxU'⟩ = closedPoint B)
    (hxi : φ ⟨⟨x, hxU'⟩, hxU⟩ ∈ Set.range (nodeLocus π (π * b))) :
    ∃ (X₂ : Scheme.{u}) (β : X₂ ⟶ X) (P : Scheme.{u}) (J : P ⟶ X₂)
      (p₁ : P ⟶ affineBlowup (LocusBlowup.locusIdeal π b)) (p₂ : P ⟶ U.toScheme),
      IsModification β ∧ IsStrictlySemistable (β ≫ g) ⊤ ∧ IsOpenImmersion J ∧ Etale p₁ ∧
      p₁ ≫ affineBlowupStructure (LocusBlowup.locusIdeal π b) = p₂ ≫ φ ∧
      J ≫ β = p₂ ≫ U.ι ≫ (baseOpen O B hOB g).ι ∧ (∀ y : X₂, β y = x → y ∈ Set.range J) ∧
      ∀ {E : Type u} [CommRing E] (p : X ⟶ Spec (.of E)), IsProjectiveOver p →
        LocallyOfFinitePresentation p → IsProjectiveOver (β ≫ p) := by
  have : Fact (π * b ≠ 0) := LocusBlowup.fact_mul_ne_zero π b
  refine exists_blowup_globalTransport_projective O B hOB g hX (LocusBlowup.locusIdeal π b)
    (LocusBlowup.locusIdeal_fg π b) (nodeModel (π * (π * b))) rfl
    (algebraMap_nodeLocus_surjective π (π * b)) (Fact.out : π ≠ 0) ?_
    (LocusBlowup.locusBlowup_isStrictlySemistable π b) (LocusBlowup.locusBlowup_isModification π b)
    (LocusBlowup.locusBlowup_cover π b) U φ hφ hxU' hxU hxcl hx hxi
  rw [IsScalarTower.algebraMap_apply B (Node B (π * (π * b))), Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem]
  exact LocusBlowup.algebraMap_mem_locusIdeal π b

end Transport

end DeJongAlterations.StableModification.Gluing.CofinalProjective
