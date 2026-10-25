/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane T45B)
-/
import DeJongAlterations.StableModification.Gluing.MarksLift

/-!
# Local semi-stable models with separated marks

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), proof of
Proposition 4.5.1 (`sepclosprop`, T:3246–3252: "applying to them first Proposition cofinprop and
then Lemma divlem we can construct a semi-stable modification of `(C'_i, D'_i)`"), in the form of
`PLAN-T5.md` §2.2 steps 6–8 with marks (node V2, the pair version of lane T45A's nodes A6–A8).

Let `N` be an integral proper curve over a valuation ring `R`, with marks given by sections
`σN k : Spec R → N`. The **mark-bad set** `markBad` consists of the points of the sections at
which `N → Spec R` is not smooth or two sections meet; it is closed, and the **good locus**
`goodOpen` (nodal and not mark-bad) is the locus where `(N, ⋃ₖ σN k)` is a semi-stable pair.
Around a closed point `x` of an open `O ⊆ N` carrying a strictly semi-stable model `τ : B → O`,
the open `O_x = O ∩ throughOpen x` meets only the sections through `x` (which lie in it
entirely, `range_subset_throughOpen`); over `O_x` the sections lift to `τ⁻¹(O_x)`, and the
separation of marks with projectivity tracked (`ProjectiveSeparation`, **not proved here**: lane
BND's `Blowups.exists_separation_marks` with the projectivity of the output, `PLAN-T5.md` node A4)
gives a local model `τ_x : B_x → O_x` which is projective over `O_x`, nodal, whose lifted sections
are pairwise disjoint and pass through smooth points, and whose isomorphism locus lies in the good
locus (`exists_local_marked_model`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace DeJongAlterations.StableModification.Gluing.StableVal

open DeJong (IsNodalCurve IsSmoothAt IsSemistablePair)
open Geometry.ModificationCenter (isomorphismOpen center)
open _root_.DeJongAlterations.StableModification.ValuationRing (fiberTrdeg)
open Curves (IsStrictlySemistable)

set_option backward.isDefEq.respectTransparency false

section Hypothesis

variable {K : Type u} [Field K] (R : ValuationSubring K)

/-- **Projective separation of marks** (`PLAN-T5.md` §2.2 step 4, node A4, the marks part;
Temkin, Lemma 4.3.3 `divlem`, T:3019–3044, with the projectivity of the output tracked; **not
proved here**, lane T45C's `Gluing/SeparationProjective*`). For an integral strictly semi-stable
curve `g : B → Spec R`, separated over `R`, and finitely many pairwise distinct sections `σ k`,
there is a modification `β : B' → B`, projective relative to `g`, such that the lifted sections
are pairwise disjoint and `(B', ⋃ₖ σ' k)` is a semi-stable pair. Without the projectivity of `β`
this is lane BND's `Blowups.exists_separation_marks` (whose output is moreover strictly
semi-stable). -/
def ProjectiveSeparation : Prop :=
  ∀ (B : Scheme.{u}) (g : B ⟶ Spec (.of R)) [IsSeparated g] [IsIntegral B],
    IsStrictlySemistable g ⊤ → ∀ (n : ℕ) (σ : Fin n → (Spec (.of R) ⟶ B)),
      (∀ k, σ k ≫ g = 𝟙 _) → Function.Injective σ →
      ∃ (B' : Scheme.{u}) (β : B' ⟶ B) (σ' : Fin n → (Spec (.of R) ⟶ B')),
        IsModification β ∧ DeJong.IsRelativelyProjective g β ∧ (∀ k, σ' k ≫ β = σ k) ∧
        (∀ k l, k ≠ l → Disjoint (Set.range (σ' k)) (Set.range (σ' l))) ∧
        IsSemistablePair (β ≫ g) (⨅ k, (σ' k).ker)

end Hypothesis

section Smooth

/-- **Smoothness transfers along a morphism which is an isomorphism near the point.** -/
theorem isSmoothAt_of_isIso_restrict {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (U : Y.Opens) [IsIso (f ∣_ U)] {x : X} (hx : f x ∈ U) (h : IsSmoothAt (f ≫ g) x) :
    IsSmoothAt g (f x) := by
  let x' : (f ⁻¹ᵁ U).toScheme := ⟨x, hx⟩
  have h1 : IsSmoothAt ((f ⁻¹ᵁ U).ι ≫ f ≫ g) x' :=
    Curves.isSmoothAt_comp (Curves.isSmoothAt_of_smooth _ x') h
  rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc] at h1
  have h2 : IsSmoothAt (inv (f ∣_ U) ≫ (f ∣_ U) ≫ U.ι ≫ g) ((f ∣_ U) x') := by
    refine Curves.isSmoothAt_comp (Curves.isSmoothAt_of_smooth _ _) ?_
    rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]
    exact h1
  rw [IsIso.inv_hom_id_assoc] at h2
  have h3 := Curves.isSmoothAt_of_isOpenImmersion_comp U.ι h2
  have h4 : U.ι ((f ∣_ U) x') = f x := by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
    rfl
  rwa [h4] at h3

end Smooth

section Local

variable {K : Type u} [Field K] {R : ValuationSubring K}
  {N : Scheme.{u}} (pN : N ⟶ Spec (.of R)) [IsSeparated pN]
  {n : ℕ} (σN : Fin n → (Spec (.of R) ⟶ N)) (hσN : ∀ k, σN k ≫ pN = 𝟙 _)

local notation "s₀" => IsLocalRing.closedPoint R

/-- The **mark-bad set**: points of a section at which `pN` is not smooth or which lie on two
sections. -/
def markBad : Set N :=
  ⋃ k, Set.range (σN k) ∩ ({y | ¬ IsSmoothAt pN y} ∪ ⋃ l ∈ {l | l ≠ k}, Set.range (σN l))

include hσN in
theorem isClosed_markBad [LocallyOfFinitePresentation pN] : IsClosed (markBad pN σN) := by
  refine isClosed_iUnion_of_finite fun k ↦ (isClosed_range σN hσN k).inter
    (IsClosed.union ?_ (isClosed_iUnion_ne σN hσN k))
  have : {y | ¬ IsSmoothAt pN y} = (pN.smoothLocus : Set N)ᶜ := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, SetLike.mem_coe,
      DeJong.isSmoothAt_iff_mem_smoothLocus]
  rw [this]
  exact pN.smoothLocus.isOpen.isClosed_compl

/-- The **good locus** of `(N, ⋃ₖ σN k)`: nodal and not mark-bad. -/
def goodOpen [LocallyOfFinitePresentation pN] : N.Opens :=
  Curves.SemistableOpen.nodalLocus pN ⊓
    ⟨(markBad pN σN)ᶜ, (isClosed_markBad pN σN hσN).isOpen_compl⟩

theorem mem_goodOpen_iff [LocallyOfFinitePresentation pN] (y : N) :
    y ∈ goodOpen pN σN hσN ↔ y ∈ Curves.SemistableOpen.nodalLocus pN ∧ y ∉ markBad pN σN :=
  Iff.rfl

omit [IsSeparated pN] in
theorem not_mem_markBad_iff (y : N) :
    y ∉ markBad pN σN ↔ ∀ k t, σN k t = y →
      IsSmoothAt pN y ∧ ∀ l, l ≠ k → y ∉ Set.range (σN l) := by
  constructor
  · intro h k t ht
    refine ⟨by_contra fun hs ↦ h (Set.mem_iUnion.mpr ⟨k, ⟨t, ht⟩, Or.inl hs⟩), fun l hl hy ↦
      h (Set.mem_iUnion.mpr ⟨k, ⟨t, ht⟩, Or.inr (Set.mem_biUnion hl hy)⟩)⟩
  · intro h hy
    obtain ⟨k, ⟨t, ht⟩, hy'⟩ := Set.mem_iUnion.mp hy
    obtain ⟨h1, h2⟩ := h k t ht
    rcases hy' with hs | hl
    · exact hs h1
    · obtain ⟨l, hl, hyl⟩ := Set.mem_iUnion₂.mp hl
      exact h2 l hl hyl

/-- The open of the points which are not on a section avoiding `x` at the closed point. -/
def throughOpen (x : N) : N.Opens :=
  ⟨(⋃ k ∈ {k | σN k s₀ ≠ x}, Set.range (σN k))ᶜ,
    (Set.Finite.isClosed_biUnion (Set.toFinite _) fun k _ ↦
      isClosed_range σN hσN k).isOpen_compl⟩

theorem mem_throughOpen_iff (x y : N) :
    y ∈ throughOpen pN σN hσN x ↔ ∀ k, y ∈ Set.range (σN k) → σN k s₀ = x := by
  change y ∈ (⋃ k ∈ {k | σN k s₀ ≠ x}, Set.range (σN k))ᶜ ↔ _
  simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop, not_exists,
    not_and]
  constructor
  · intro h k hk
    by_contra hne
    exact h k hne hk
  · intro h k hne hk
    exact hne (h k hk)

omit [IsSeparated pN] in
/-- Closed points of a proper `R`-scheme lie over the closed point. -/
theorem apply_eq_closedPoint_of_isClosed [IsProper pN] {x : N} (hx : IsClosed ({x} : Set N)) :
    pN x = s₀ := by
  have h : IsClosed ({pN x} : Set (Spec (.of R))) := by
    have := pN.isClosedMap _ hx
    rwa [Set.image_singleton] at this
  have hmax := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp h
  exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hmax)

include hσN in
theorem mem_throughOpen_self [IsProper pN] {x : N} (hx : IsClosed ({x} : Set N)) :
    x ∈ throughOpen pN σN hσN x := by
  rw [mem_throughOpen_iff]
  rintro k ⟨t, rfl⟩
  have ht : t = s₀ := by
    have := apply_eq_closedPoint_of_isClosed pN hx
    rw [← Scheme.Hom.comp_apply, hσN k] at this
    exact this
  rw [ht]

include hσN in
/-- A section through `x` at the closed point lies entirely in `throughOpen x`. -/
theorem range_subset_throughOpen {x : N} {k : Fin n} (hk : σN k s₀ = x) :
    Set.range (σN k) ⊆ throughOpen pN σN hσN x := by
  rintro _ ⟨t, rfl⟩
  rw [SetLike.mem_coe, mem_throughOpen_iff]
  rintro l ⟨t', ht'⟩
  have htt : t' = t := by
    have := congrArg pN ht'
    rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hσN, hσN] at this
  subst htt
  rw [← hk]
  exact (Blowups.apply_closedPoint_eq_of_apply_eq pN (σN k) (σN l) (hσN k) (hσN l) t'
    ht'.symm).symm

end Local

section Opens

variable {N : Scheme.{u}}

/-- The stalks of an open subscheme of a normal scheme are integrally closed. -/
theorem isIntegrallyClosed_stalk_opens (hN : IsNormalScheme N) (O : N.Opens) (y : O) :
    IsIntegrallyClosed (O.toScheme.presheaf.stalk y) := by
  have := (hN (O.ι y)).2
  exact IsIntegrallyClosed.of_equiv (asIso (O.ι.stalkMap y)).commRingCatIsoToRingEquiv

/-- Two opens with the same image are isomorphic: `V = O ∩ Ox` viewed in `O`, and `Ox ≤ O`. -/
theorem range_ι_preimage_ι {O Ox : N.Opens} (h : Ox ≤ O) :
    Set.range ((O.ι ⁻¹ᵁ Ox).ι ≫ O.ι) = Set.range Ox.ι := by
  rw [Scheme.Opens.range_ι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Scheme.Opens.range_ι]
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hz
    exact ⟨⟨z, h hz⟩, hz, rfl⟩

end Opens

section LocalModel

variable {K : Type u} [Field K] {R : ValuationSubring K} [Finite (PrimeSpectrum R)]
  {N : Scheme.{u}} [IsIntegral N] (hN : IsNormalScheme N) (pN : N ⟶ Spec (.of R)) [IsProper pN]
  [Flat pN] [LocallyOfFinitePresentation pN] (hdim : fiberTrdeg pN (genericPoint N) ≤ 1)
  {n : ℕ} (σN : Fin n → (Spec (.of R) ⟶ N)) (hσN : ∀ k, σN k ≫ pN = 𝟙 _)
  (hinj : Function.Injective fun k ↦ σN k (genericPoint (Spec (.of R))))

local notation "s₀" => IsLocalRing.closedPoint R

include hN hdim hinj in
/-- **A local semi-stable model with separated marks** (Temkin, proof of Proposition 4.5.1,
T:3246–3252, with Lemma 4.3.3; `PLAN-T5.md` §2.2 steps 6–8 with marks). Let `τ : B → O` be a
strictly semi-stable model of an open `O ⊆ N`, projective over `O`, and `x ∈ O` a closed point.
Over `O_x = O ∩ throughOpen x` there is a modification `τ_x : B_x → O_x`, projective over `O_x`,
nodal over `R`, whose isomorphism locus lies in the good locus, together with lifts of the
sections through `x` which are pairwise disjoint and pass through smooth points of `B_x`.
Input not proved here: `ProjectiveSeparation R`. -/
theorem exists_local_marked_model (hsepM : ProjectiveSeparation R) (O : N.Opens)
    {B : Scheme.{u}} (τ : B ⟶ O) [IsModification τ] (hss : IsStrictlySemistable (τ ≫ O.ι ≫ pN) ⊤)
    (hτp : DeJong.IsRelativelyProjective (O.ι ≫ pN) τ) {x : N} (hxO : x ∈ O)
    (hx : IsClosed ({x} : Set N)) :
    ∃ (Bx : Scheme.{u}) (τx : Bx ⟶ (O ⊓ throughOpen pN σN hσN x : N.Opens)),
      IsModification τx ∧
      DeJong.IsRelativelyProjective ((O ⊓ throughOpen pN σN hσN x).ι ≫ pN) τx ∧
      IsNodalCurve (τx ≫ (O ⊓ throughOpen pN σN hσN x).ι ≫ pN) ∧
      (O ⊓ throughOpen pN σN hσN x).ι ''ᵁ isomorphismOpen τx ≤ goodOpen pN σN hσN ∧
      ∃ σx : (k : Fin n) → σN k s₀ = x → (Spec (.of R) ⟶ Bx),
        (∀ k hk, σx k hk ≫ τx ≫ (O ⊓ throughOpen pN σN hσN x).ι = σN k) ∧
        (∀ k hk t, IsSmoothAt (τx ≫ (O ⊓ throughOpen pN σN hσN x).ι ≫ pN) (σx k hk t)) ∧
        (∀ k hk l hl, k ≠ l → Disjoint (Set.range (σx k hk)) (Set.range (σx l hl))) := by
  classical
  set Ox := O ⊓ throughOpen pN σN hσN x with hOx
  have hxOx : x ∈ Ox := ⟨hxO, mem_throughOpen_self pN σN hσN hx⟩
  have : Nonempty Ox := ⟨⟨x, hxOx⟩⟩
  have : IsIntegral Ox.toScheme := isIntegral_of_isOpenImmersion Ox.ι
  -- the restriction of `τ` over `Ox`
  let V : O.toScheme.Opens := O.ι ⁻¹ᵁ Ox
  let eV : V.toScheme ≅ Ox.toScheme :=
    IsOpenImmersion.isoOfRangeEq ((O.ι ⁻¹ᵁ Ox).ι ≫ O.ι) Ox.ι (range_ι_preimage_ι inf_le_left)
  have heV : eV.hom ≫ Ox.ι = V.ι ≫ O.ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have : Nonempty V := ⟨⟨⟨x, hxO⟩, hxOx⟩⟩
  have hτV := Geometry.CurveCompactification.isModification_morphismRestrict τ V
  have := isModification_of_isIso eV.hom
  let τ₀ : (τ ⁻¹ᵁ V).toScheme ⟶ Ox := (τ ∣_ V) ≫ eV.hom
  have hτ₀ : IsModification τ₀ := IsModification.comp _ _
  have : IsIntegral (τ ⁻¹ᵁ V).toScheme := hτ₀.sourceIntegral
  have hτ₀ι : τ₀ ≫ Ox.ι = (τ ⁻¹ᵁ V).ι ≫ τ ≫ O.ι := by
    simp only [τ₀, Category.assoc, heV]
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
  set g₀ := τ₀ ≫ Ox.ι ≫ pN with hg₀def
  have hg₀ : g₀ = (τ ⁻¹ᵁ V).ι ≫ τ ≫ O.ι ≫ pN := by
    rw [hg₀def, ← Category.assoc, hτ₀ι, Category.assoc, Category.assoc]
  have hss₀ : IsStrictlySemistable g₀ ⊤ := by
    have h := hss.etale_comp (τ ⁻¹ᵁ V).ι
    rw [Scheme.IdealSheafData.comap_top] at h
    rw [hg₀]
    exact h
  have : IsSeparated g₀ := by rw [hg₀]; infer_instance
  -- the sections through `x`
  let Kx := {k : Fin n // σN k s₀ = x}
  let e : Fin (Fintype.card Kx) ≃ Kx := (Fintype.equivFin Kx).symm
  have hsub : ∀ k : Kx, Set.range (σN k.1) ⊆ Set.range Ox.ι := fun k ↦ by
    rw [Scheme.Opens.range_ι]
    intro y hy
    exact ⟨Blowups.range_subset_of_closedPoint_mem (σN k.1) O (by rw [k.2]; exact hxO) hy,
      range_subset_throughOpen pN σN hσN k.2 hy⟩
  let sOx : Kx → (Spec (.of R) ⟶ Ox) := fun k ↦ IsOpenImmersion.lift Ox.ι (σN k.1) (hsub k)
  have hsOx : ∀ k, sOx k ≫ Ox.ι = σN k.1 := fun k ↦ IsOpenImmersion.lift_fac _ _ _
  have hnormOx : ∀ y : Ox, (Ox.ι ≫ pN) y = genericPoint (Spec (.of R)) →
      IsIntegrallyClosed (Ox.toScheme.presheaf.stalk y) := fun y _ ↦
    isIntegrallyClosed_stalk_opens hN Ox y
  have hdimOx : fiberTrdeg (Ox.ι ≫ pN) (genericPoint Ox.toScheme) ≤ 1 := by
    rw [fiberTrdeg_genericPoint_opens]
    exact hdim
  have hlift : ∀ k : Kx, ∃ s : Spec (.of R) ⟶ (τ ⁻¹ᵁ V).toScheme, s ≫ τ₀ = sOx k := fun k ↦
    exists_lift_section (Ox.ι ≫ pN) hnormOx hdimOx τ₀ (sOx k)
      (by rw [← Category.assoc, hsOx, hσN])
  choose σB hσB using hlift
  have hσBN : ∀ k, σB k ≫ τ₀ ≫ Ox.ι = σN k.1 := fun k ↦ by
    rw [← Category.assoc, hσB, hsOx]
  have hσBsec : ∀ i, σB (e i) ≫ g₀ = 𝟙 _ := fun i ↦ by
    rw [hg₀def, ← Category.assoc τ₀, ← Category.assoc, hσBN, hσN]
  have hσBinj : Function.Injective fun i ↦ σB (e i) := by
    intro i j hij
    have h1 : σN (e i).1 = σN (e j).1 := by
      rw [← hσBN, ← hσBN]
      exact congrArg (· ≫ τ₀ ≫ Ox.ι) hij
    have h2 := hinj (congrArg (fun f : Spec (.of R) ⟶ N ↦ f (genericPoint (Spec (.of R)))) h1)
    exact e.injective (Subtype.ext h2)
  -- the separation of the marks
  obtain ⟨Bx, βx, σ', hβx, hβxp, hσ', hdisj, hpair⟩ :=
    hsepM (τ ⁻¹ᵁ V).toScheme g₀ hss₀ _ (fun i ↦ σB (e i)) hσBsec hσBinj
  have hτx : IsModification (βx ≫ τ₀) := IsModification.comp _ _
  have hnod : IsNodalCurve ((βx ≫ τ₀) ≫ Ox.ι ≫ pN) := by
    have := hpair.nodal
    rwa [Category.assoc]
  have hσ'sec : ∀ i, σ' i ≫ βx ≫ g₀ = 𝟙 _ := fun i ↦ by
    rw [← Category.assoc, hσ', hσBsec]
  have hσ'N : ∀ i, σ' i ≫ (βx ≫ τ₀) ≫ Ox.ι = σN (e i).1 := fun i ↦ by
    rw [Category.assoc, ← Category.assoc (σ' i), hσ', hσBN]
  have hsm : ∀ i t, IsSmoothAt ((βx ≫ τ₀) ≫ Ox.ι ≫ pN) (σ' i t) := by
    intro i t
    have hmem : σ' i t ∈ ((⨅ k, (σ' k).ker).support : Set Bx) := by
      rw [support_iInf_ker' σ' hσ'sec]
      exact Set.mem_iUnion.mpr ⟨i, t, rfl⟩
    have h := hpair.smoothAlong _ hmem
    rwa [Category.assoc]
  refine ⟨Bx, βx ≫ τ₀, hτx, ?_, hnod, ?_, fun k hk ↦ σ' (e.symm ⟨k, hk⟩), fun k hk ↦ ?_,
    fun k hk t ↦ hsm _ t, fun k hk l hl hkl ↦ hdisj _ _ fun h ↦ hkl ?_⟩
  · -- projectivity
    have h1 := Projectivity.isRelativelyProjective_restrict hτp V
    have h2 : V.ι ≫ O.ι ≫ pN = eV.hom ≫ Ox.ι ≫ pN := by
      rw [← Category.assoc eV.hom, heV, Category.assoc]
    rw [h2] at h1
    have h3 : DeJong.IsRelativelyProjective (Ox.ι ≫ pN) τ₀ :=
      isRelativelyProjective_comp_iso (Ox.ι ≫ pN) eV h1
    exact IsRelativelyProjective.comp h3 hβxp
  · -- the isomorphism locus is good
    rintro _ ⟨y', hy', rfl⟩
    rw [mem_goodOpen_iff]
    refine ⟨image_isomorphismOpen_le_nodalLocus pN Ox (βx ≫ τ₀) hnod ⟨y', hy', rfl⟩, ?_⟩
    rw [not_mem_markBad_iff]
    have hiso : IsIso ((βx ≫ τ₀) ∣_ isomorphismOpen (βx ≫ τ₀)) :=
      (Geometry.ModificationCenter.le_isomorphismOpen_iff _ _).mp le_rfl
    -- points of `Bx` over `y'` coincide
    have huniq : ∀ w₁ w₂ : Bx, (βx ≫ τ₀) w₁ = y' → (βx ≫ τ₀) w₂ = y' → w₁ = w₂ := by
      intro w₁ w₂ h₁ h₂
      have hm₁ : w₁ ∈ (βx ≫ τ₀) ⁻¹ᵁ isomorphismOpen (βx ≫ τ₀) := by
        rw [Scheme.Hom.mem_preimage, h₁]
        exact hy'
      have hm₂ : w₂ ∈ (βx ≫ τ₀) ⁻¹ᵁ isomorphismOpen (βx ≫ τ₀) := by
        rw [Scheme.Hom.mem_preimage, h₂]
        exact hy'
      have hinj' := ((βx ≫ τ₀) ∣_ isomorphismOpen (βx ≫ τ₀)).isOpenEmbedding.injective
      have : ((βx ≫ τ₀) ∣_ isomorphismOpen (βx ≫ τ₀)) ⟨w₁, hm₁⟩ =
          ((βx ≫ τ₀) ∣_ isomorphismOpen (βx ≫ τ₀)) ⟨w₂, hm₂⟩ := by
        apply Subtype.ext
        change ((βx ≫ τ₀) ∣_ _ ≫ (isomorphismOpen (βx ≫ τ₀)).ι) ⟨w₁, hm₁⟩ =
          ((βx ≫ τ₀) ∣_ _ ≫ (isomorphismOpen (βx ≫ τ₀)).ι) ⟨w₂, hm₂⟩
        rw [morphismRestrict_ι, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
        exact h₁.trans h₂.symm
      exact congrArg Subtype.val (hinj' this)
    have hpt : ∀ i t, σN (e i).1 t = Ox.ι y' → (βx ≫ τ₀) (σ' i t) = y' := by
      intro i t ht
      apply Ox.ι.isOpenEmbedding.injective
      rw [← ht, ← hσ'N i]
      rfl
    intro k t hkt
    have hk : σN k s₀ = x := (mem_throughOpen_iff pN σN hσN x _).mp y'.2.2 k ⟨t, hkt⟩
    have hkt' : σN (e (e.symm ⟨k, hk⟩)).1 t = Ox.ι y' := by
      rw [Equiv.apply_symm_apply]
      exact hkt
    have hw := hpt _ t hkt'
    refine ⟨?_, fun l hl hyl ↦ ?_⟩
    · have h := isSmoothAt_of_isIso_restrict (βx ≫ τ₀) (Ox.ι ≫ pN) _
        (by rw [hw]; exact hy') (hsm (e.symm ⟨k, hk⟩) t)
      rw [hw] at h
      exact Curves.isSmoothAt_of_isOpenImmersion_comp Ox.ι h
    · obtain ⟨t', ht'⟩ := hyl
      have htt : t' = t := by
        have h1 := congrArg pN (ht'.trans hkt.symm)
        rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hσN, hσN] at h1
      subst htt
      have hl' : σN l s₀ = x := (mem_throughOpen_iff pN σN hσN x _).mp y'.2.2 l ⟨t', ht'⟩
      have hlt' : σN (e (e.symm ⟨l, hl'⟩)).1 t' = Ox.ι y' := by
        rw [Equiv.apply_symm_apply]
        exact ht'
      have hw' := hpt _ t' hlt'
      have heq := huniq _ _ hw hw'
      have hne : e.symm ⟨k, hk⟩ ≠ e.symm ⟨l, hl'⟩ := fun h ↦ hl (by
        have := congrArg Subtype.val (e.symm.injective h)
        exact this.symm)
      exact Set.disjoint_left.mp (hdisj _ _ hne) ⟨t', rfl⟩ ⟨t', heq.symm⟩
  · -- the lifts
    have h := hσ'N (e.symm ⟨k, hk⟩)
    rw [Equiv.apply_symm_apply] at h
    exact h
  · have := congrArg Subtype.val (e.symm.injective h)
    exact this

end LocalModel

end DeJongAlterations.StableModification.Gluing.StableVal
