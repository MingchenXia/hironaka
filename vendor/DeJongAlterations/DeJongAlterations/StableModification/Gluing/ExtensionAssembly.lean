/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane T45A)
-/
import DeJongAlterations.StableModification.Gluing.Extension
import DeJongAlterations.StableModification.Gluing.BadLocus
import DeJongAlterations.StableModification.Gluing.LocalModels
import DeJongAlterations.StableModification.Curves.SemistableOpen
import DeJongAlterations.StableModification.DeJong.NodalBaseChange
import DeJongAlterations.StableModification.Projectivity.Reduction
import DeJongAlterations.StableModification.BlowDown.NoClosedExc

/-!
# The semi-stable model of the normalized refinement (PLAN-T5 nodes A6–A8 assembled)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), proof of
Proposition 4.5.1 (`sepclosprop`, T:3243–3266), in the form of `PLAN-T5.md` §2.2 steps 5–8: the
normalization `N` of the projective refinement `C'` is covered by opens `Oᵢ = ν⁻¹(Wᵢ)` carrying the
strictly semi-stable models `τᵢ : Bᵢ → Oᵢ`; outside the finite bad locus `N` is already nodal, and
around each closed bad point a local model `τᵢ⁻¹(Uₓ) → Uₓ` is inserted by the identity.

## Main results

* `isModification_of_isIso`, `isModification_of_comp`, `IsoOver.isModification`: modifications
  and isomorphisms; cancellation `f ≫ g, g ⇒ f`.
* `preimage_isomorphismOpen_le`, `preimage_inv_isomorphismOpen_le`: isomorphism loci of
  restrictions.
* `exists_modification_of_localModifications`: **the generic assembly** (nodes A6–A8) — for a
  normal integral `N` proper over `V` (finite height, separably closed residue fields) covered by
  finitely many local modifications `τᵢ : Bᵢ → Oᵢ` and an open `G` containing their isomorphism
  loci, a modification `β : X → N`, an isomorphism over an open `O' ⊆ G`, which over the other
  opens `Uₖ` of a cover is an open of some `Bᵢ`.
* `isNodalCurve_comp_of_cover`, `image_isomorphismOpen_le_nodalLocus`: nodality from such a cover;
  isomorphism loci of nodal local models lie in the nodal locus
  (`Curves.SemistableOpen.nodalLocus`).
* `exists_nodal_modification_normalization`: **nodes A5–A8 assembled** — for an integral proper
  relative curve `C'` of finite presentation over `V`, covered by opens `Wᵢ` dominated by normal,
  flat, nodal modifications `qᵢ : Bᵢ → Wᵢ` projective relative to `Wᵢ → Spec V`, the normalization
  `N = Nor(C')` is finite over `C'` and there is a modification `X → N` with `X → C'` a
  modification and `X` nodal over `V`, locally an open of some `Bᵢ` or of the nodal locus of `N`.

The input `qᵢ` (projective strictly semi-stable models of the pieces of the refinement) is the
output of PLAN-T5 node A4, which is not proved in this lane; marks (the pair version of the
semi-stable locus) are not treated here: `exists_modification_of_localModifications` applies to any
good locus `G`, in particular to a semi-stable-pair locus once its openness is available.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology

universe u

namespace DeJongAlterations.StableModification.Gluing

open Geometry.ModificationCenter ValCurves
open _root_.DeJongAlterations.StableModification.ValuationRing (fiberTrdeg)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Restrict

variable {X Y Z : Scheme.{u}}

/-- An isomorphism between integral schemes is a modification. -/
theorem isModification_of_isIso (e : X ⟶ Y) [IsIso e] [IsIntegral Y] : IsModification e := by
  have : Nonempty X := ⟨(inv e) (Nonempty.some inferInstance)⟩
  exact
    { sourceIntegral := isIntegral_of_isOpenImmersion e
      targetIntegral := inferInstance
      birational := Scheme.Hom.birationalOver e (𝟙 Y) e (Category.comp_id e) }

/-- The isomorphism locus of a restriction contains the restriction of the isomorphism locus. -/
theorem preimage_isomorphismOpen_le (f : X ⟶ Y) (V : Y.Opens) :
    V.ι ⁻¹ᵁ isomorphismOpen f ≤ isomorphismOpen (f ∣_ V) := by
  have himage : V.ι ''ᵁ (V.ι ⁻¹ᵁ isomorphismOpen f) ≤ isomorphismOpen f := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    exact inf_le_right
  have : IsIso (f ∣_ V.ι ''ᵁ (V.ι ⁻¹ᵁ isomorphismOpen f)) := isIso_restrict_of_le f himage
  have H : IsIso ((f ∣_ V) ∣_ V.ι ⁻¹ᵁ isomorphismOpen f) :=
    ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictRestrict f V (V.ι ⁻¹ᵁ isomorphismOpen f))).mpr this
  exact le_isomorphismOpen_of_isIso _ _

/-- Composing with an isomorphism transports the isomorphism locus. -/
theorem preimage_inv_isomorphismOpen_le (f : X ⟶ Y) (e : Y ≅ Z) :
    e.inv ⁻¹ᵁ isomorphismOpen f ≤ isomorphismOpen (f ≫ e.hom) := by
  have h : e.hom ⁻¹ᵁ (e.inv ⁻¹ᵁ isomorphismOpen f) = isomorphismOpen f := by
    rw [← Scheme.Hom.comp_preimage, e.hom_inv_id, Scheme.Hom.id_preimage]
  have : IsIso (f ∣_ (e.hom ⁻¹ᵁ (e.inv ⁻¹ᵁ isomorphismOpen f))) := by
    rw [h]
    infer_instance
  have : IsIso ((f ≫ e.hom) ∣_ (e.inv ⁻¹ᵁ isomorphismOpen f)) := by
    rw [morphismRestrict_comp]
    infer_instance
  exact le_isomorphismOpen_of_isIso _ _

/-- **Cancellation of modifications**: if `f ≫ g` and `g` are modifications, then `f` is a
modification (over a dense open of `Z` both are isomorphisms). -/
theorem isModification_of_comp (f : X ⟶ Y) (g : Y ⟶ Z) [IsModification (f ≫ g)]
    [IsModification g] : IsModification f := by
  have hfg : IsModification (f ≫ g) := inferInstance
  have hg : IsModification g := inferInstance
  have := hfg.sourceIntegral
  have := hg.sourceIntegral
  have := hg.targetIntegral
  have hpf : IsProper f := IsProper.of_comp f g
  let U := isomorphismOpen (f ≫ g) ⊓ isomorphismOpen g
  have hUd : Dense (U : Set Z) := (dense_isomorphismOpen (f ≫ g)).inter_of_isOpen_left
    (dense_isomorphismOpen g) (isomorphismOpen (f ≫ g)).isOpen
  have : IsIso ((f ≫ g) ∣_ U) := isIso_restrict_of_le _ inf_le_left
  have : IsIso (g ∣_ U) := isIso_restrict_of_le _ inf_le_right
  have : IsIso (f ∣_ (g ⁻¹ᵁ U)) := by
    have h := morphismRestrict_comp f g U
    have : IsIso (f ∣_ g ⁻¹ᵁ U ≫ g ∣_ U) := by rw [← h]; infer_instance
    exact IsIso.of_isIso_comp_right _ (g ∣_ U)
  obtain ⟨z, hz⟩ := hUd.nonempty
  let y := inv (g ∣_ U) ⟨z, hz⟩
  let x := inv (f ∣_ (g ⁻¹ᵁ U)) y
  have hV : ((g ⁻¹ᵁ U : Y.Opens) : Set Y).Nonempty := ⟨y.1, y.2⟩
  have hW : ((f ⁻¹ᵁ (g ⁻¹ᵁ U) : X.Opens) : Set X).Nonempty := ⟨x.1, x.2⟩
  refine
    { toIsProper := hpf
      sourceIntegral := inferInstance
      targetIntegral := inferInstance
      birational := ⟨⟨f ⁻¹ᵁ (g ⁻¹ᵁ U), (f ⁻¹ᵁ (g ⁻¹ᵁ U)).isOpen.dense hW, g ⁻¹ᵁ U,
        (g ⁻¹ᵁ U).isOpen.dense hV, asIso (f ∣_ (g ⁻¹ᵁ U))⟩, ?_⟩ }
  change (f ∣_ (g ⁻¹ᵁ U)) ≫ (g ⁻¹ᵁ U).ι ≫ 𝟙 Y = (f ⁻¹ᵁ (g ⁻¹ᵁ U)).ι ≫ f
  rw [Category.comp_id, morphismRestrict_ι]

/-- Modifications are stable under isomorphisms of the source over the target. -/
theorem IsoOver.isModification {f₁ : X ⟶ Z} {f₂ : Y ⟶ Z} (h : IsoOver f₁ f₂)
    [IsModification f₂] : IsModification f₁ := by
  obtain ⟨i, rfl⟩ := h
  have hf : IsModification f₂ := inferInstance
  have := hf.sourceIntegral
  have := isModification_of_isIso i.hom
  exact IsModification.comp _ _

/-- Relative projectivity is transported along an isomorphism of the target over the base. -/
theorem isRelativelyProjective_comp_iso {k : Type u} [CommRing k] {T T' : Scheme.{u}}
    (pT' : T' ⟶ Spec (.of k)) (e : T ≅ T') {f : X ⟶ T}
    (h : DeJong.IsRelativelyProjective (e.hom ≫ pT') f) :
    DeJong.IsRelativelyProjective pT' (f ≫ e.hom) := by
  obtain ⟨n, i, hi, hf⟩ := h
  have := hi
  refine ⟨n, i ≫ pullback.map (e.hom ≫ pT') (projectiveSpaceStructure k n) pT'
    (projectiveSpaceStructure k n) e.hom (𝟙 _) (𝟙 _) (by simp) (by simp), inferInstance, ?_⟩
  rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hf]

end Restrict

section Assembly

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [Finite (PrimeSpectrum V)]
  (hsep : ∀ p : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ p.asIdeal)))
  {N : Scheme.{u}} [IsIntegral N] (hN : IsNormalScheme N) (pN : N ⟶ Spec (.of V)) [IsProper pN]
  (hdim : fiberTrdeg pN (genericPoint N) ≤ 1)
  {ι : Type*} [Finite ι] (O : ι → N.Opens) (hO : ⨆ i, O i = ⊤) {B : ι → Scheme.{u}}
  (τ : ∀ i, B i ⟶ O i) [∀ i, IsModification (τ i)] (G : N.Opens)
  (hG : ∀ i, (O i).ι ''ᵁ isomorphismOpen (τ i) ≤ G)

include hsep hN hdim hO hG in
/-- **Inserting the local semi-stable models by the identity** (`PLAN-T5.md` §2.2 steps 6–8,
nodes A6–A8; Temkin, proof of Proposition 4.5.1, T:3243–3266). Let `N` be normal, integral and
proper over a valuation ring `V` of finite height with separably closed residue fields, a relative
curve, covered by finitely many opens `Oᵢ` carrying modifications `τᵢ : Bᵢ → Oᵢ`, and let `G ⊆ N`
be an open containing the loci where the `τᵢ` are isomorphisms. Then there is a modification
`β : X → N` and an open `O' ⊆ G` over which `β` is an isomorphism such that `N` is covered by `O'`
and finitely many opens `Uₖ ⊆ Oⱼ₍ₖ₎` over which `X` is the open `τ⁻¹(Uₖ)` of `Bⱼ₍ₖ₎`. -/
theorem exists_modification_of_localModifications :
    ∃ (X : Scheme.{u}) (β : X ⟶ N), IsModification β ∧
      ∃ O' : N.Opens, O' ≤ G ∧ O' ≤ isomorphismOpen β ∧
      ∃ (κ : Type u) (_ : Finite κ) (U : κ → N.Opens) (j : κ → ι), O' ⊔ (⨆ k, U k) = ⊤ ∧
        ∀ k, U k ≤ O (j k) ∧ IsoOver ((β ⁻¹ᵁ U k).ι ≫ β)
          ((τ (j k) ⁻¹ᵁ ((O (j k)).ι ⁻¹ᵁ U k)).ι ≫ τ (j k) ≫ (O (j k)).ι) ∧
          (DeJong.IsRelativelyProjective ((O (j k)).ι ≫ pN) (τ (j k)) →
            DeJong.IsRelativelyProjective ((U k).ι ≫ pN) (β ∣_ U k)) := by
  classical
  -- the local modification loci and the bad locus
  let Z : ι → Set N := fun i ↦ localCenter (O i) (τ i)
  have hZc : ∀ i, IsClosed (((↑) : O i → N) ⁻¹' Z i) := fun i ↦
    isClosed_preimage_localCenter (O i) (τ i)
  have hZf : ∀ i, (Z i).Finite := fun i ↦ finite_localCenter pN (τ i) hN hdim
  have hZa : ∀ i, ∀ t ∈ Z i, IsAlgebraicAt pN t := fun i _ ht ↦
    isAlgebraicAt_of_mem_localCenter pN (τ i) hN hdim ht
  have hBad : IsClosed ((G : Set N)ᶜ) := G.isOpen.isClosed_compl
  have hBadf : ((G : Set N)ᶜ).Finite := finite_compl pN O τ G hN hdim hO hG
  have hBadZ : ∀ i, (G : Set N)ᶜ ∩ O i ⊆ Z i := fun i _ ⟨hz, hzO⟩ ↦
    compl_inter_subset_localCenter O τ G hG i hz hzO
  obtain ⟨κ, hκ, j, U, T, hTc, hTU, hUO, hdisj, hcov, hUZ, hTZ, hTne⟩ :=
    exists_localModels hsep pN O Z ((G : Set N)ᶜ) hO hZc hZf hZa hBad hBadf hBadZ
  have : Fintype κ := Fintype.ofFinite κ
  -- the complements of the `Tₖ`
  let W : κ → N.Opens := fun k ↦ ⟨(T k)ᶜ, (hTc k).isOpen_compl⟩
  have hUW : ∀ k, U k ⊔ W k = ⊤ := fun k ↦ eq_top_iff.mpr fun z _ ↦ by
    by_cases hz : z ∈ T k
    · exact TopologicalSpace.Opens.mem_sup.mpr (Or.inl (hTU k hz))
    · exact TopologicalSpace.Opens.mem_sup.mpr (Or.inr hz)
  have hgen : ∀ k, genericPoint N ∈ W k := fun k h ↦
    genericPoint_not_mem_localCenter (O (j k)) (τ (j k)) (hTZ k h)
  have hUWl : ∀ k l, k ≠ l → U k ≤ W l := fun k l hkl z hz hzT ↦
    Set.disjoint_left.mp (hdisj k l hkl) hz hzT
  -- the local models `fₖ : τ⁻¹(Uₖ) → Uₖ`
  let Vk : ∀ k, (O (j k)).toScheme.Opens := fun k ↦ (O (j k)).ι ⁻¹ᵁ U k
  have hrange : ∀ k, Set.range ((Vk k).ι ≫ (O (j k)).ι) = Set.range (U k).ι := by
    intro k
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι]
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hz
      exact ⟨⟨z, hUO k hz⟩, hz, rfl⟩
  let e : ∀ k, (Vk k).toScheme ≅ (U k).toScheme := fun k ↦
    IsOpenImmersion.isoOfRangeEq ((Vk k).ι ≫ (O (j k)).ι) (U k).ι (hrange k)
  have he : ∀ k, (e k).inv ≫ (Vk k).ι ≫ (O (j k)).ι = (U k).ι := fun k ↦
    IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _
  have he' : ∀ k, (e k).hom ≫ (U k).ι = (Vk k).ι ≫ (O (j k)).ι := fun k ↦
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  let f : ∀ k, (τ (j k) ⁻¹ᵁ Vk k).toScheme ⟶ (U k).toScheme := fun k ↦
    (τ (j k) ∣_ Vk k) ≫ (e k).hom
  have hf : ∀ k, IsModification (f k) := by
    intro k
    have hmod : IsModification (τ (j k)) := inferInstance
    have := hmod.targetIntegral
    obtain ⟨t, ht⟩ := hTne k
    have : Nonempty (Vk k) := ⟨⟨⟨t, hUO k (hTU k ht)⟩, hTU k ht⟩⟩
    have := Geometry.CurveCompactification.isModification_morphismRestrict (τ (j k)) (Vk k)
    have : Nonempty (U k).toScheme := ⟨⟨t, hTU k ht⟩⟩
    have : IsIntegral (U k).toScheme := isIntegral_of_isOpenImmersion (e k).inv
    have := isModification_of_isIso (e k).hom
    exact IsModification.comp _ _
  have hfiso : ∀ k, (U k).ι ⁻¹ᵁ W k ≤ isomorphismOpen (f k) := by
    intro k u hu
    refine preimage_inv_isomorphismOpen_le _ (e k) (preimage_isomorphismOpen_le _ (Vk k) ?_)
    change (Vk k).ι ((e k).inv u) ∈ isomorphismOpen (τ (j k))
    by_contra hc
    have hZ : (O (j k)).ι ((Vk k).ι ((e k).inv u)) ∈ Z (j k) := ⟨_, hc, rfl⟩
    have hpt : (O (j k)).ι ((Vk k).ι ((e k).inv u)) = (U k).ι u := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, he]
    rw [hpt] at hZ
    exact hu (hUZ k ⟨u.2, hZ⟩)
  -- the extension
  obtain ⟨X, β, hβ, hiso, hloc⟩ := exists_extension_finset U W f hUW hgen hUWl hfiso Finset.univ
  let O' : N.Opens := ⟨(⋃ k, T k)ᶜ, (isClosed_iUnion_of_finite hTc).isOpen_compl⟩
  have hO'W : ∀ k, O' ≤ W k := fun k z hz hzT ↦ hz (Set.mem_iUnion.mpr ⟨k, hzT⟩)
  refine ⟨X, β, hβ, O', fun z hz ↦ ?_, hiso O' fun k _ ↦ hO'W k, κ, hκ, U, j, ?_,
    fun k ↦ ⟨hUO k, ?_, fun hτ ↦ ?_⟩⟩
  · by_contra hzG
    exact hz (hcov hzG)
  · refine eq_top_iff.mpr fun z _ ↦ ?_
    by_cases hz : z ∈ ⋃ k, T k
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hz
      exact TopologicalSpace.Opens.mem_sup.mpr
        (Or.inr (TopologicalSpace.Opens.mem_iSup.mpr ⟨k, hTU k hk⟩))
    · exact TopologicalSpace.Opens.mem_sup.mpr (Or.inl hz)
  · have h := (hloc k (Finset.mem_univ k)).comp (U k).ι
    rw [morphismRestrict_ι] at h
    have hfk : f k ≫ (U k).ι = (τ (j k) ⁻¹ᵁ Vk k).ι ≫ τ (j k) ≫ (O (j k)).ι := by
      change ((τ (j k) ∣_ Vk k) ≫ (e k).hom) ≫ (U k).ι = _
      rw [Category.assoc, he', ← Category.assoc, morphismRestrict_ι, Category.assoc]
    rw [hfk] at h
    exact h
  · obtain ⟨i, hi⟩ := hloc k (Finset.mem_univ k)
    have h1 := Projectivity.isRelativelyProjective_restrict hτ (Vk k)
    have h2 : (Vk k).ι ≫ (O (j k)).ι ≫ pN = (e k).hom ≫ (U k).ι ≫ pN := by
      rw [← Category.assoc (e k).hom, he', Category.assoc]
    rw [h2] at h1
    rw [← hi]
    exact Projectivity.isRelativelyProjective_iso_hom_comp
      (isRelativelyProjective_comp_iso ((U k).ι ≫ pN) (e k) h1) i

end Assembly

section Nodal

open DeJong (IsNodalCurve)

/-- **Nodality from a cover by local models**: if `N` is covered by an open `O'` over which
`β : X → N` is an isomorphism and `O'` is nodal over `S`, and by opens `Uₖ` over which `X` is
isomorphic to nodal `S`-curves, then `X` is nodal over `S`. -/
theorem isNodalCurve_comp_of_cover {X N S : Scheme.{u}} (β : X ⟶ N) (pN : N ⟶ S) (O' : N.Opens)
    (hO' : O' ≤ isomorphismOpen β) (hO'n : IsNodalCurve (O'.ι ≫ pN)) {κ : Type*}
    (U : κ → N.Opens) (hcov : O' ⊔ (⨆ k, U k) = ⊤) {Y : κ → Scheme.{u}} (g : ∀ k, Y k ⟶ N)
    (hg : ∀ k, IsoOver ((β ⁻¹ᵁ U k).ι ≫ β) (g k)) (hgn : ∀ k, IsNodalCurve (g k ≫ pN)) :
    IsNodalCurve (β ≫ pN) := by
  refine Curves.IsNodalCurve.of_openCover _ fun x ↦ ?_
  have hx : β x ∈ O' ⊔ ⨆ k, U k := by rw [hcov]; trivial
  rcases TopologicalSpace.Opens.mem_sup.mp hx with hx | hx
  · refine ⟨β ⁻¹ᵁ O', hx, ?_⟩
    have : IsIso (β ∣_ O') := (le_isomorphismOpen_iff β O').mp hO'
    have h : (β ⁻¹ᵁ O').ι ≫ β ≫ pN = (asIso (β ∣_ O')).hom ≫ O'.ι ≫ pN := by
      rw [asIso_hom, morphismRestrict_ι_assoc]
    rw [h]
    exact DeJong.IsNodalCurve.of_iso _ _
  · obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    refine ⟨β ⁻¹ᵁ U k, hk, ?_⟩
    obtain ⟨i, hi⟩ := hg k
    have := hgn k
    have h : (β ⁻¹ᵁ U k).ι ≫ β ≫ pN = i.hom ≫ g k ≫ pN := by
      rw [← Category.assoc, ← hi, Category.assoc]
    rw [h]
    exact DeJong.IsNodalCurve.of_iso _ _

/-- **The isomorphism locus of a nodal local model is nodal**: for `τ : B → O`, `O ⊆ N` open, with
`B` nodal over `S`, the open of `N` where `τ` is an isomorphism lies in the nodal locus. -/
theorem image_isomorphismOpen_le_nodalLocus {N S B : Scheme.{u}} (pN : N ⟶ S) (O : N.Opens)
    (τ : B ⟶ O) (hB : IsNodalCurve (τ ≫ O.ι ≫ pN)) :
    O.ι ''ᵁ isomorphismOpen τ ≤ Curves.SemistableOpen.nodalLocus pN := by
  apply Curves.SemistableOpen.le_nodalLocus
  have h1 : IsNodalCurve ((τ ⁻¹ᵁ isomorphismOpen τ).ι ≫ τ ≫ O.ι ≫ pN) :=
    Curves.IsNodalCurve.etale_comp _ _
  have h2 : (isomorphismOpen τ).ι ≫ O.ι ≫ pN =
      (asIso (inv (τ ∣_ isomorphismOpen τ))).hom ≫ (τ ⁻¹ᵁ isomorphismOpen τ).ι ≫ τ ≫ O.ι ≫ pN := by
    rw [asIso_hom, ← morphismRestrict_ι_assoc, IsIso.inv_hom_id_assoc]
  have h3 : IsNodalCurve ((isomorphismOpen τ).ι ≫ O.ι ≫ pN) := by
    rw [h2]
    exact DeJong.IsNodalCurve.of_iso _ _
  have h4 : (O.ι ''ᵁ isomorphismOpen τ).ι ≫ pN =
      (O.ι.isoImage (isomorphismOpen τ)).symm.hom ≫ (isomorphismOpen τ).ι ≫ O.ι ≫ pN := by
    rw [Iso.symm_hom, ← Category.assoc (isomorphismOpen τ).ι,
      ← Scheme.Hom.isoImage_hom_ι O.ι (isomorphismOpen τ), Category.assoc, Iso.inv_hom_id_assoc]
  rw [h4]
  exact DeJong.IsNodalCurve.of_iso _ _

end Nodal

section Global

open DeJong (IsNodalCurve)

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [Finite (PrimeSpectrum V)]
  (hsep : ∀ p : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ p.asIdeal)))
  {C' : Scheme.{u}} [IsIntegral C'] (pC' : C' ⟶ Spec (.of V)) [IsProper pC']
  [LocallyOfFinitePresentation pC'] (hdim : fiberTrdeg pC' (genericPoint C') ≤ 1)
  {ι : Type*} [Finite ι] {W : ι → C'.Opens} (hW : ⨆ i, W i = ⊤) {B : ι → Scheme.{u}}
  (q : ∀ i, B i ⟶ W i) [∀ i, IsModification (q i)] (hB : ∀ i, IsNormalScheme (B i))
  (hflat : ∀ i, Flat (q i ≫ (W i).ι ≫ pC'))
  (hq : ∀ i, DeJong.IsRelativelyProjective ((W i).ι ≫ pC') (q i))
  (hnod : ∀ i, IsNodalCurve (q i ≫ (W i).ι ≫ pC'))

include hsep hdim hW hB hflat hq hnod in
/-- **The semi-stable model from local projective semi-stable models** (`PLAN-T5.md` §2.2
steps 5–8, nodes A5–A8; Temkin, proof of Proposition 4.5.1, T:3243–3266). Let `C'` be an integral
relative curve, proper and of finite presentation over a valuation ring `V` of finite height with
separably closed residue fields, covered by finitely many opens `Wᵢ` dominated by modifications
`qᵢ : Bᵢ → Wᵢ` which are projective relative to `Wᵢ → Spec V`, with `Bᵢ` normal, flat and nodal
over `V` (the output of PLAN-T5 node A4 for the projective refinement). Then the normalization
`N = Nor(C')` is finite over `C'`, and there is a modification `β : X → N` such that `X → C'` is a
modification, `X` is a nodal curve over `V`, and `X` is covered by an open isomorphic to an open
of the nodal locus of `N` and by opens isomorphic over `C'` to opens of the `Bᵢ`. -/
theorem exists_nodal_modification_normalization :
    IsFinite (genericPt C').fromNormalization ∧
      ∃ (X : Scheme.{u}) (β : X ⟶ (genericPt C').normalization), IsModification β ∧
        IsModification (β ≫ (genericPt C').fromNormalization) ∧
        IsNodalCurve (β ≫ (genericPt C').fromNormalization ≫ pC') ∧
        Projectivity.LocallyRelativelyProjective ((genericPt C').fromNormalization ≫ pC') β ∧
        ∃ O' : (genericPt C').normalization.Opens, O' ≤ isomorphismOpen β ∧
          O' ≤ Curves.SemistableOpen.nodalLocus ((genericPt C').fromNormalization ≫ pC') ∧
          ∃ (κ : Type u) (_ : Finite κ) (U : κ → (genericPt C').normalization.Opens)
            (j : κ → ι), O' ⊔ (⨆ k, U k) = ⊤ ∧ ∀ k, ∃ Vk : (B (j k)).Opens,
              IsoOver ((β ⁻¹ᵁ U k).ι ≫ β ≫ (genericPt C').fromNormalization)
                (Vk.ι ≫ q (j k) ≫ (W (j k)).ι) := by
  have hfin : IsFinite (genericPt C').fromNormalization :=
    isFinite_fromNormalization_genericPt q pC' hW hB hflat hq
  refine ⟨hfin, ?_⟩
  set ν := (genericPt C').fromNormalization
  have hν : IsModification ν := isModification_fromNormalization_genericPt
  have hN : IsNormalScheme (genericPt C').normalization := isNormalScheme_normalization_genericPt
  have hdimN : fiberTrdeg (ν ≫ pC') (genericPoint (genericPt C').normalization) ≤ 1 := by
    rw [ValCurves.fiberTrdeg_comp_genericPoint pC' ν]
    exact hdim
  -- the local models over the pieces `ν⁻¹ Wᵢ`
  choose ji hji using fun i ↦ isoOver_restrict_normalization_genericPt q i (hB i)
  let τ : ∀ i, B i ⟶ (ν ⁻¹ᵁ W i).toScheme := fun i ↦ (q i).toNormalization ≫ (ji i).inv
  have hτ : ∀ i, τ i ≫ (ν ∣_ W i) = q i := fun i ↦ by
    change ((q i).toNormalization ≫ (ji i).inv) ≫ ν ∣_ W i = q i
    rw [← hji i, Category.assoc, Iso.inv_hom_id_assoc, Scheme.Hom.toNormalization_fromNormalization]
  have hτm : ∀ i, IsModification (τ i) := by
    intro i
    have hmod : IsModification (q i) := inferInstance
    have := hmod.targetIntegral
    have : Nonempty (W i) := (inferInstance : Nonempty (W i).toScheme)
    have := Geometry.CurveCompactification.isModification_morphismRestrict ν (W i)
    have : IsModification (τ i ≫ ν ∣_ W i) := by rw [hτ i]; infer_instance
    exact isModification_of_comp (τ i) (ν ∣_ W i)
  have hτO : ∀ i, τ i ≫ (ν ⁻¹ᵁ W i).ι ≫ ν = q i ≫ (W i).ι := fun i ↦ by
    rw [← morphismRestrict_ι, ← Category.assoc, hτ i]
  have hτn : ∀ i, IsNodalCurve (τ i ≫ (ν ⁻¹ᵁ W i).ι ≫ ν ≫ pC') := fun i ↦ by
    have h := hτO i
    rw [← Category.assoc ((ν ⁻¹ᵁ W i).ι), ← Category.assoc (τ i), h, Category.assoc]
    exact hnod i
  -- extension by the identity
  obtain ⟨X, β, hβ, O', hO'G, hO'iso, κ, hκ, U, j, hcov, hloc⟩ :=
    exists_modification_of_localModifications hsep hN (ν ≫ pC') hdimN (fun i ↦ ν ⁻¹ᵁ W i)
      (iSup_preimage_eq_top ν hW) τ (Curves.SemistableOpen.nodalLocus (ν ≫ pC'))
      fun i ↦ image_isomorphismOpen_le_nodalLocus _ _ (τ i) (hτn i)
  have hτp : ∀ i, DeJong.IsRelativelyProjective ((ν ⁻¹ᵁ W i).ι ≫ ν ≫ pC') (τ i) := by
    intro i
    have h1 := BlowDown.NoClosedExc.isRelativelyProjective_toNormalization ((W i).ι ≫ pC') (q i)
      (hq i)
    have h2 : (q i).fromNormalization ≫ (W i).ι ≫ pC' =
        (ji i).symm.hom ≫ (ν ⁻¹ᵁ W i).ι ≫ ν ≫ pC' := by
      rw [Iso.symm_hom, ← morphismRestrict_ι_assoc, ← hji i, Category.assoc,
        Iso.inv_hom_id_assoc]
    rw [h2] at h1
    exact isRelativelyProjective_comp_iso _ (ji i).symm h1
  refine ⟨X, β, hβ, IsModification.comp β ν, ?_, ?_, O', hO'iso, hO'G, κ, hκ, U, j, hcov,
    fun k ↦ ⟨τ (j k) ⁻¹ᵁ ((ν ⁻¹ᵁ W (j k)).ι ⁻¹ᵁ U k), ?_⟩⟩
  · refine isNodalCurve_comp_of_cover β (ν ≫ pC') O' hO'iso
      (Curves.SemistableOpen.isNodalCurve_of_le_nodalLocus _ hO'G) U hcov _
      (fun k ↦ (hloc k).2.1) fun k ↦ ?_
    have := hτn (j k)
    simp only [Category.assoc]
    exact Curves.IsNodalCurve.etale_comp _ _
  · refine ⟨Option κ, inferInstance, fun o ↦ o.elim O' U, ?_, fun o ↦ ?_⟩
    · refine eq_top_iff.mpr fun z _ ↦ ?_
      have hz : z ∈ O' ⊔ ⨆ k, U k := by rw [hcov]; trivial
      rcases TopologicalSpace.Opens.mem_sup.mp hz with hz | hz
      · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨none, hz⟩
      · obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
        exact TopologicalSpace.Opens.mem_iSup.mpr ⟨some k, hk⟩
    · rcases o with _ | k
      · have : IsIso (β ∣_ O') := (le_isomorphismOpen_iff β O').mp hO'iso
        change DeJong.IsRelativelyProjective (O'.ι ≫ ν ≫ pC') (β ∣_ O')
        exact DeJong.isRelativelyProjective_of_isClosedImmersion _ _
      · exact (hloc k).2.2 (hτp (j k))
  · have h := (hloc k).2.1.comp ν
    simp only [Category.assoc] at h
    rw [hτO] at h
    exact h

end Global

end DeJongAlterations.StableModification.Gluing
