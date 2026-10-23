/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane T45B)
-/
import DeJongAlterations.StableModification.Gluing.MarksLocal
import DeJongAlterations.StableModification.Gluing.NodalUnconditional

/-!
# A nodal modification with separated marks over a valuation ring

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), proof of
Proposition 4.5.1 (`sepclosprop`, T:3243–3266), in the form of `PLAN-T5.md` §2.2 steps 1–8 **with
marks** (node V2; the pair version of lane T45A's `Gluing.exists_nodal_modification`). Let `K` be
algebraically closed, `R ⊆ K` a valuation ring of finite height and equal characteristic, and
`φ : C → Spec R` a proper flat integral relative curve, normal along its generic fibre, with
finitely many sections `σ k` with pairwise distinct generic points. Then there are the normalized
projective refinement `b : N → C` (lane T45A) and a modification `β : X → N` such that `X` is a
nodal curve over `R`, locally projective over `N`, and the lifts `σX k` of the sections to `X` are
pairwise disjoint and pass through smooth points of `X → Spec R`
(the assembly `exists_marked_nodal_modification` is **not** in this file, see below).

The construction: the sections lift to `N` (`exists_lift_section`); the good locus `G` of
`(N, ⋃ₖ σN k)` (`goodOpen`) is covered by the identity, and each closed point `x ∉ G` by a local
model with separated marks (`exists_local_marked_model`, built from lane T45A/T45C's projective
strictly semi-stable models of the pieces of the refinement and the hypothesis
`ProjectiveSeparation R`); the local models are inserted by the identity
(`Gluing.exists_modification_of_localModifications`). The marks of `X` are analysed pointwise:
over the part where `β` is an isomorphism onto an open of `G` they are those of `N`
(`smooth_and_disjoint_of_mem_isomorphismOpen`), over a local model they correspond to the
separated lifted sections (`IsoOver.apply_section_eq`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace DeJongAlterations.StableModification.Gluing.StableVal

open DeJong (IsNodalCurve IsSmoothAt IsSemistablePair)
open Geometry.ModificationCenter (isomorphismOpen center)
open _root_.DeJongAlterations.StableModification.ValuationRing (fiberTrdeg)
open Curves (IsStrictlySemistable)
open ValCurves (genericPt)

set_option backward.isDefEq.respectTransparency false

section Closure

variable {R : Type u} [CommRing R] [IsDomain R] {X : Scheme.{u}} (q : X ⟶ Spec (.of R))
  [IsSeparated q]

/-- **The image of a section is the closure of its generic point.** -/
theorem range_eq_closure_genericPoint (σ : Spec (.of R) ⟶ X) (hσ : σ ≫ q = 𝟙 _) :
    Set.range σ = closure {σ (genericPoint (Spec (.of R)))} := by
  refine Set.Subset.antisymm ?_ (closure_minimal (by
    rintro _ rfl
    exact ⟨_, rfl⟩) (Blowups.isClosed_range_section σ hσ))
  rintro _ ⟨t, rfl⟩
  have h : genericPoint (Spec (.of R)) ⤳ t :=
    (genericPoint_spec (Spec (.of R))).specializes (Set.mem_univ t)
  exact (h.map σ.continuous).mem_closure

end Closure

section Transfer

variable {R : Type u} [CommRing R] [IsDomain R]
  {N X B : Scheme.{u}} (pN : N ⟶ Spec (.of R)) (β : X ⟶ N) (O U : N.Opens) (τ : B ⟶ O)
  [IsSeparated (τ ≫ O.ι ≫ pN)]
  (i : (β ⁻¹ᵁ U).toScheme ≅ (τ ⁻¹ᵁ (O.ι ⁻¹ᵁ U)).toScheme)
  (hi : i.hom ≫ (τ ⁻¹ᵁ (O.ι ⁻¹ᵁ U)).ι ≫ τ ≫ O.ι = (β ⁻¹ᵁ U).ι ≫ β)
  (η : Spec (.of R)) (hgen : ∀ w₁ w₂ : B, τ w₁ = τ w₂ → pN (O.ι (τ w₁)) = η → w₁ = w₂)
  (σN : Spec (.of R) ⟶ N) (hσN : σN ≫ pN = 𝟙 _) (σX : Spec (.of R) ⟶ X) (hσX : σX ≫ β = σN)
  (sB : Spec (.of R) ⟶ B) (hsB : sB ≫ τ ≫ O.ι = σN)

include hi hgen hσN hσX hsB in
/-- **Sections correspond under a local isomorphism over `N`**: if `X` and `B` are isomorphic
over `U ⊆ N` (`i`), `B → O` is injective over the generic point, and `σX`, `sB` are lifts of the
same section `σN`, then `i` maps `σX t` to `sB t` whenever `σN t ∈ U`. -/
theorem IsoOver.apply_section_eq (t : Spec (.of R)) (hηt : η ⤳ t) (ht : σN t ∈ U) :
    (τ ⁻¹ᵁ (O.ι ⁻¹ᵁ U)).ι (i.hom ⟨σX t, by
      rw [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, hσX]; exact ht⟩) = sB t := by
  have hηU : σN η ∈ U := (hηt.map σN.continuous).mem_open U.isOpen ht
  have hmem : ∀ s, σN s ∈ U → σX s ∈ β ⁻¹ᵁ U := fun s hs ↦ by
    rw [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, hσX]
    exact hs
  set j := (τ ⁻¹ᵁ (O.ι ⁻¹ᵁ U)).ι
  have hj : ∀ z : β ⁻¹ᵁ U, O.ι (τ (j (i.hom z))) = β z.1 := fun z ↦ by
    have := congrArg (fun f ↦ f z) hi
    simp only [Scheme.Hom.comp_apply] at this
    exact this
  -- the generic points correspond
  have hwη : j (i.hom ⟨σX η, hmem η hηU⟩) = sB η := by
    apply hgen
    · apply O.ι.isOpenEmbedding.injective
      rw [hj]
      show β (σX η) = O.ι (τ (sB η))
      rw [← Scheme.Hom.comp_apply σX β, hσX, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
        hsB]
    · rw [hj]
      show pN (β (σX η)) = η
      rw [← Scheme.Hom.comp_apply σX β, hσX, ← Scheme.Hom.comp_apply, hσN]
      rfl
  -- specialization
  have hsp : (⟨σX η, hmem η hηU⟩ : β ⁻¹ᵁ U) ⤳ ⟨σX t, hmem t ht⟩ :=
    Topology.IsInducing.subtypeVal.specializes_iff.mp (hηt.map σX.continuous)
  have hsp' := (hsp.map i.hom.continuous).map j.continuous
  rw [hwη] at hsp'
  have hsec : sB ≫ τ ≫ O.ι ≫ pN = 𝟙 _ := by
    have e : sB ≫ τ ≫ O.ι ≫ pN = (sB ≫ τ ≫ O.ι) ≫ pN := by simp only [Category.assoc]
    rw [e, hsB, hσN]
  have hmemR : j (i.hom ⟨σX t, hmem t ht⟩) ∈ Set.range sB :=
    closure_minimal (Set.singleton_subset_iff.mpr (Set.mem_range_self η))
      (Blowups.isClosed_range_section sB hsec) hsp'.mem_closure
  obtain ⟨t', ht'⟩ := hmemR
  have htt : t' = t := by
    have h1 : (sB ≫ τ ≫ O.ι ≫ pN) t' = (σX ≫ β ≫ pN) t := by
      simp only [Scheme.Hom.comp_apply]
      rw [ht', hj]
    rw [hsec, ← Category.assoc, hσX, hσN] at h1
    exact h1
  rw [← ht', htt]

omit [IsDomain R] [IsSeparated (τ ≫ O.ι ≫ pN)] in
include hi in
/-- **Smoothness transfers along a local isomorphism over `N`.** -/
theorem IsoOver.isSmoothAt_of_isSmoothAt (z : β ⁻¹ᵁ U)
    (h : IsSmoothAt (τ ≫ O.ι ≫ pN) ((τ ⁻¹ᵁ (O.ι ⁻¹ᵁ U)).ι (i.hom z))) :
    IsSmoothAt (β ≫ pN) z.1 := by
  have h1 : IsSmoothAt ((τ ⁻¹ᵁ (O.ι ⁻¹ᵁ U)).ι ≫ τ ≫ O.ι ≫ pN) (i.hom z) :=
    Curves.isSmoothAt_comp (Curves.isSmoothAt_of_smooth _ _) h
  have h2 : IsSmoothAt (i.hom ≫ (τ ⁻¹ᵁ (O.ι ⁻¹ᵁ U)).ι ≫ τ ≫ O.ι ≫ pN) z :=
    Curves.isSmoothAt_comp (Curves.isSmoothAt_of_smooth _ _) h1
  have e : i.hom ≫ (τ ⁻¹ᵁ (O.ι ⁻¹ᵁ U)).ι ≫ τ ≫ O.ι ≫ pN = (β ⁻¹ᵁ U).ι ≫ β ≫ pN := by
    simp only [← Category.assoc] at hi ⊢
    rw [hi]
  rw [e] at h2
  exact Curves.isSmoothAt_of_isOpenImmersion_comp _ h2

end Transfer

section IsoLocus

variable {X N S : Scheme.{u}} (β : X ⟶ N) (pN : N ⟶ S)

/-- A morphism which is an isomorphism over `V` is smooth at the points over `V`. -/
theorem isSmoothAt_of_mem_isomorphismOpen {V : N.Opens} [IsIso (β ∣_ V)] {z : X} (hz : β z ∈ V)
    (h : IsSmoothAt pN (β z)) : IsSmoothAt (β ≫ pN) z := by
  let z' : (β ⁻¹ᵁ V).toScheme := ⟨z, hz⟩
  have h1 : IsSmoothAt ((β ∣_ V) ≫ V.ι ≫ pN) z' := by
    refine Curves.isSmoothAt_comp (Curves.isSmoothAt_of_smooth _ _) ?_
    refine Curves.isSmoothAt_comp (Curves.isSmoothAt_of_smooth _ _) ?_
    have : V.ι ((β ∣_ V) z') = β z := by
      rw [← Scheme.Hom.comp_apply, morphismRestrict_ι]
      rfl
    rw [this]
    exact h
  rw [← Category.assoc, morphismRestrict_ι, Category.assoc] at h1
  exact Curves.isSmoothAt_of_isOpenImmersion_comp _ h1

/-- A morphism which is an isomorphism over `U` is injective over `U`. -/
theorem eq_of_isIso_restrict {Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) [IsIso (f ∣_ U)]
    {w₁ w₂ : X} (h : f w₁ = f w₂) (hU : f w₁ ∈ U) : w₁ = w₂ := by
  have hm₁ : w₁ ∈ f ⁻¹ᵁ U := hU
  have hm₂ : w₂ ∈ f ⁻¹ᵁ U := by rw [Scheme.Hom.mem_preimage, ← h]; exact hU
  have : (f ∣_ U) ⟨w₁, hm₁⟩ = (f ∣_ U) ⟨w₂, hm₂⟩ := by
    apply Subtype.ext
    change ((f ∣_ U) ≫ U.ι) ⟨w₁, hm₁⟩ = ((f ∣_ U) ≫ U.ι) ⟨w₂, hm₂⟩
    rw [morphismRestrict_ι, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact h
  exact congrArg Subtype.val ((f ∣_ U).isOpenEmbedding.injective this)

/-- If `(β⁻¹ U → U) ≅ j` over `N` with `j` an open immersion with image `U`, then `β` is an
isomorphism over `U`. -/
theorem isIso_restrict_of_isoOver {U : N.Opens} {T : Scheme.{u}} (j : T ⟶ N) [IsOpenImmersion j]
    (hj : Set.range j = U) (h : IsoOver ((β ⁻¹ᵁ U).ι ≫ β) j) : IsIso (β ∣_ U) := by
  obtain ⟨i, hi⟩ := h
  let e : T ≅ U.toScheme := IsOpenImmersion.isoOfRangeEq j U.ι (by rw [hj, Scheme.Opens.range_ι])
  have he : e.hom ≫ U.ι = j := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have : β ∣_ U = i.hom ≫ e.hom := by
    rw [← cancel_mono U.ι, morphismRestrict_ι, Category.assoc, he, hi]
  rw [this]
  infer_instance

end IsoLocus

section Pieces

variable {K : Type u} [Field K] {R : ValuationSubring K} {N X : Scheme.{u}}
  (pN : N ⟶ Spec (.of R))
  (β : X ⟶ N) {n : ℕ} (σN : Fin n → (Spec (.of R) ⟶ N)) (σX : Fin n → (Spec (.of R) ⟶ X))
  (hσX : ∀ k, σX k ≫ β = σN k)

include hσX in
/-- **The marks over an isomorphism piece in the good locus**: if `β` is an isomorphism over an
open `V` avoiding the mark-bad set, the lifted sections are smooth and disjoint over `V`. -/
theorem marks_of_iso_piece (V : N.Opens) (hV : ∀ y ∈ V, y ∉ markBad pN σN) [IsIso (β ∣_ V)]
    (k : Fin n) (t : Spec (.of R)) (hyV : σN k t ∈ V) :
    IsSmoothAt (β ≫ pN) (σX k t) ∧ ∀ l, l ≠ k → σX l t ≠ σX k t := by
  have hβσ : ∀ l, β (σX l t) = σN l t := fun l ↦ by rw [← Scheme.Hom.comp_apply, hσX]
  have hy := (not_mem_markBad_iff pN σN (σN k t)).mp (hV _ hyV) k t rfl
  refine ⟨isSmoothAt_of_mem_isomorphismOpen β pN (V := V) (by rw [hβσ]; exact hyV)
    (by rw [hβσ]; exact hy.1), fun l hl he ↦ hy.2 l hl ⟨t, ?_⟩⟩
  rw [← hβσ, he, hβσ]

end Pieces

section Insertion

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [Finite (PrimeSpectrum V)]
  (hsep : ∀ p : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ p.asIdeal)))
  {N : Scheme.{u}} [IsIntegral N] (hN : IsNormalScheme N) (pN : N ⟶ Spec (.of V)) [IsProper pN]
  (hdim : fiberTrdeg pN (genericPoint N) ≤ 1)
  {ι : Type u} [Finite ι] (O : ι → N.Opens) {B : ι → Scheme.{u}} (τ : ∀ i, B i ⟶ O i)
  [∀ i, IsModification (τ i)] (G : N.Opens) [Nonempty G]

include hsep hN hdim in
/-- **Inserting local models around the complement of a good open** (lane T45A's
`Gluing.exists_modification_of_localModifications` with the identity on the good open `G`
among the local models). If `G` and the opens `Oᵢ` cover `N`, the isomorphism loci of the
`τᵢ` lie in `G`, `G` and the `τᵢ` are nodal and the `τᵢ` projective over the `Oᵢ`, there is a
modification `β : X → N` with `X` nodal and locally projective over `N`, an isomorphism over
opens of `G` covering `N` together with opens `Uₖ ⊆ O_{j k}` over which `X` is an open of
`B_{j k}`. -/
theorem exists_modification_of_localModifications_id
    (hcov : G ⊔ ⨆ i, O i = ⊤) (hG : ∀ i, (O i).ι ''ᵁ isomorphismOpen (τ i) ≤ G)
    (hGn : IsNodalCurve (G.ι ≫ pN)) (hτn : ∀ i, IsNodalCurve (τ i ≫ (O i).ι ≫ pN))
    (hτp : ∀ i, DeJong.IsRelativelyProjective ((O i).ι ≫ pN) (τ i)) :
    ∃ (X : Scheme.{u}) (β : X ⟶ N), IsModification β ∧ IsNodalCurve (β ≫ pN) ∧
      Projectivity.LocallyRelativelyProjective pN β ∧
      ∃ (κ : Type u) (_ : Finite κ) (U : κ → N.Opens) (j : κ → Option ι), ⨆ k, U k = ⊤ ∧
        ∀ k, (j k = none → U k ≤ G ∧ IsIso (β ∣_ U k)) ∧
          (∀ i, j k = some i → U k ≤ O i ∧
            IsoOver ((β ⁻¹ᵁ U k).ι ≫ β) ((τ i ⁻¹ᵁ ((O i).ι ⁻¹ᵁ U k)).ι ≫ τ i ≫ (O i).ι)) := by
  classical
  have : IsIntegral G.toScheme := isIntegral_of_isOpenImmersion G.ι
  let Oo : Option ι → N.Opens := fun o ↦ o.elim G O
  let Bo : Option ι → Scheme.{u} := fun o ↦ match o with
    | none => G.toScheme
    | some i => B i
  let τo : ∀ o, Bo o ⟶ (Oo o).toScheme := fun o ↦ match o with
    | none => 𝟙 G.toScheme
    | some i => τ i
  have hτom : ∀ o, IsModification (τo o) := fun o ↦ match o with
    | none => isModification_of_isIso (𝟙 G.toScheme)
    | some i => (inferInstance : IsModification (τ i))
  have hO : ⨆ o, Oo o = ⊤ := by
    refine eq_top_iff.mpr fun y _ ↦ ?_
    have hy : y ∈ G ⊔ ⨆ i, O i := by rw [hcov]; trivial
    rcases TopologicalSpace.Opens.mem_sup.mp hy with hy | hy
    · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨none, hy⟩
    · obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨some i, hi⟩
  have hGo : ∀ o, (Oo o).ι ''ᵁ isomorphismOpen (τo o) ≤ G := fun o ↦ match o with
    | none => by
        rintro _ ⟨y', -, rfl⟩
        exact y'.2
    | some i => hG i
  obtain ⟨X, β, hβ, O', hO'G, hO'iso, κ, hκ, U, j, hcovU, hlocU⟩ :=
    exists_modification_of_localModifications hsep hN pN hdim Oo hO τo G hGo
  have hτon : ∀ o, IsNodalCurve (τo o ≫ (Oo o).ι ≫ pN) := fun o ↦ match o with
    | none => by
        change IsNodalCurve (𝟙 G.toScheme ≫ G.ι ≫ pN)
        rw [Category.id_comp]
        exact hGn
    | some i => hτn i
  have hτop : ∀ o, DeJong.IsRelativelyProjective ((Oo o).ι ≫ pN) (τo o) := fun o ↦ match o with
    | none => DeJong.isRelativelyProjective_of_isClosedImmersion _ _
    | some i => hτp i
  have hnone : ∀ k, j k = none → U k ≤ G ∧ IsIso (β ∣_ U k) := by
    intro k hk
    obtain ⟨hUO, hiso, -⟩ := hlocU k
    revert hUO hiso
    rw [hk]
    intro hUO hiso
    have hUG : U k ≤ G := hUO
    refine ⟨hUG, isIso_restrict_of_isoOver β _ ?_ hiso⟩
    change Set.range ((𝟙 G.toScheme ⁻¹ᵁ (G.ι ⁻¹ᵁ U k)).ι ≫ 𝟙 G.toScheme ≫ G.ι) = U k
    rw [Category.id_comp, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι]
    ext y
    constructor
    · rintro ⟨y', hy', rfl⟩
      exact hy'
    · intro hy
      exact ⟨⟨y, hUG hy⟩, hy, rfl⟩
  refine ⟨X, β, hβ, ?_, ?_, Option κ, inferInstance, fun o ↦ o.elim O' U,
    fun o ↦ o.elim none j, ?_, fun o ↦ ?_⟩
  · refine isNodalCurve_comp_of_cover β pN O' hO'iso
      (Curves.SemistableOpen.isNodalCurve_of_le_nodalLocus _
        (hO'G.trans (Curves.SemistableOpen.le_nodalLocus pN hGn))) U hcovU _
      (fun m ↦ (hlocU m).2.1) fun m ↦ ?_
    have := hτon (j m)
    simp only [Category.assoc]
    exact Curves.IsNodalCurve.etale_comp _ _
  · refine ⟨Option κ, inferInstance, fun o ↦ o.elim O' U, ?_, fun o ↦ ?_⟩
    · refine eq_top_iff.mpr fun z _ ↦ ?_
      have hz : z ∈ O' ⊔ ⨆ m, U m := by rw [hcovU]; trivial
      rcases TopologicalSpace.Opens.mem_sup.mp hz with hz | hz
      · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨none, hz⟩
      · obtain ⟨m, hm⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
        exact TopologicalSpace.Opens.mem_iSup.mpr ⟨some m, hm⟩
    · rcases o with _ | m
      · have : IsIso (β ∣_ O') :=
          (Geometry.ModificationCenter.le_isomorphismOpen_iff β O').mp hO'iso
        change DeJong.IsRelativelyProjective (O'.ι ≫ pN) (β ∣_ O')
        exact DeJong.isRelativelyProjective_of_isClosedImmersion _ _
      · exact (hlocU m).2.2 (hτop (j m))
  · refine eq_top_iff.mpr fun z _ ↦ ?_
    have hz : z ∈ O' ⊔ ⨆ m, U m := by rw [hcovU]; trivial
    rcases TopologicalSpace.Opens.mem_sup.mp hz with hz | hz
    · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨none, hz⟩
    · obtain ⟨m, hm⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨some m, hm⟩
  · rcases o with _ | m
    · refine ⟨fun _ ↦ ⟨hO'G, (Geometry.ModificationCenter.le_isomorphismOpen_iff β O').mp
        hO'iso⟩, fun i hi ↦ ?_⟩
      exact absurd hi (by simp)
    · refine ⟨hnone m, fun i hi ↦ ?_⟩
      obtain ⟨hUO, hiso, -⟩ := hlocU m
      revert hUO hiso
      change j m = some i at hi
      rw [hi]
      exact fun hUO hiso ↦ ⟨hUO, hiso⟩

end Insertion

end DeJongAlterations.StableModification.Gluing.StableVal
