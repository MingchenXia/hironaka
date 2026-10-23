/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane T45F)
-/
import DeJongAlterations.StableModification.Gluing.UniquenessValSetup
import DeJongAlterations.StableModification.Global.SetupMarks
import DeJongAlterations.StableModification.Blowups.SeparationSections

/-!
# Uniqueness over a valuation ring: the marks as sections

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), proof of
Lemma 4.3.3 (T:3025–3027) and §4.4–4.5: over a valuation ring `V` with algebraically closed
fraction field the generic marks `D_η` of `(C, D)` are finitely many `K`-points, whose closures are
sections `cₖ : Spec V → C`; the transported marks of an η-modification `β : X → C`
(`Curves.genericMarksClosure`) are the closures of the lifts `τₖ` of the `cₖ`.

`AreGenericMarkSections q D' τ` records that the sections `τₖ` of `q : X → Spec V` have pairwise
distinct generic points and that these are exactly the points of `D'` over the generic point.
Then:

* `AreGenericMarkSections.apply_mem_support`, `.exists_eq_of_mem_support`: if `D'` is étale over
  `V`, the support of `D'` is the union of the images of the sections (`D'` is the closure of its
  generic fibre, lane T5G's `Global.eq_vanishingIdeal_of_etale`);
* `AreGenericMarkSections.eq_of_apply_eq`: **étale marks give disjoint sections** (two sections of
  the étale `D' → Spec V` meeting at a point coincide, BND's `Blowups.eq_of_comp_eq_of_apply_eq`);
* `AreGenericMarkSections.isSmoothAt`: semi-stable marks pass through smooth points;
* `AreGenericMarkSections.of_isEtaModification`: the lifts of the sections of `(C, D)` to an
  η-modification are generic mark sections for the transported marks;
* `exists_areGenericMarkSections`: the sections of a curve in the situation of
  `Global.IsValuationCurve` (lane T45B's `exists_sections_of_etale_genericMarks`).

Blueprint: `sm-gluing-uniqueness.tex`, `lem:sm-gu-marks`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace DeJongAlterations.StableModification.Gluing.UniquenessVal

open DeJong (IsNodalCurve IsSmoothAt IsSemistablePair)

set_option backward.isDefEq.respectTransparency false

section Sections

variable {V : Type u} [CommRing V] [IsDomain V]

/-- **Generic mark sections**: the sections `τₖ` of `q` have pairwise distinct generic points,
which are exactly the points of `D'` over the generic point of `Spec V`. -/
structure AreGenericMarkSections {X : Scheme.{u}} (q : X ⟶ Spec (.of V)) (D' : X.IdealSheafData)
    {n : ℕ} (τ : Fin n → (Spec (.of V) ⟶ X)) : Prop where
  section_eq : ∀ k, τ k ≫ q = 𝟙 _
  injective : Function.Injective fun k ↦ τ k (genericPoint (Spec (.of V)))
  generic : ∀ x : X, q x = genericPoint (Spec (.of V)) →
    (x ∈ (D'.support : Set X) ↔ ∃ k, τ k (genericPoint (Spec (.of V))) = x)

variable {X : Scheme.{u}} {q : X ⟶ Spec (.of V)} {D' : X.IdealSheafData} {n : ℕ}
  {τ : Fin n → (Spec (.of V) ⟶ X)}

theorem AreGenericMarkSections.apply_genericPoint (h : AreGenericMarkSections q D' τ) (k : Fin n) :
    q (τ k (genericPoint (Spec (.of V)))) = genericPoint (Spec (.of V)) := by
  rw [← Scheme.Hom.comp_apply, h.section_eq k]
  rfl

/-- The sections lie on the marks. -/
theorem AreGenericMarkSections.apply_mem_support [IsSeparated q]
    (h : AreGenericMarkSections q D' τ) (k : Fin n) (s : Spec (.of V)) :
    τ k s ∈ (D'.support : Set X) := by
  have hr := Gluing.StableVal.range_eq_closure_genericPoint q (τ k) (h.section_eq k)
  have hsub : Set.range (τ k) ⊆ (D'.support : Set X) := by
    rw [hr]
    exact closure_minimal (Set.singleton_subset_iff.mpr
      ((h.generic _ (h.apply_genericPoint k)).mpr ⟨k, rfl⟩)) D'.support.isClosed
  exact hsub ⟨s, rfl⟩

/-- **The marks are the union of the images of the sections** when they are étale over `V`. -/
theorem AreGenericMarkSections.exists_eq_of_mem_support [IsSeparated q]
    [Etale (D'.subschemeι ≫ q)] (h : AreGenericMarkSections q D' τ) {x : X}
    (hx : x ∈ (D'.support : Set X)) : ∃ k s, τ k s = x := by
  have hD := Global.eq_vanishingIdeal_of_etale q D'
  have hset : (D'.support : Set X) ∩ q ⁻¹' {genericPoint (Spec (.of V))} =
      ⋃ k, ({τ k (genericPoint (Spec (.of V)))} : Set X) := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion]
    constructor
    · rintro ⟨hyD, hyη⟩
      obtain ⟨k, hk⟩ := (h.generic y hyη).mp hyD
      exact ⟨k, hk.symm⟩
    · rintro ⟨k, rfl⟩
      exact ⟨(h.generic _ (h.apply_genericPoint k)).mpr ⟨k, rfl⟩, h.apply_genericPoint k⟩
  have hsupp : (D'.support : Set X) =
      closure ((D'.support : Set X) ∩ q ⁻¹' {genericPoint (Spec (.of V))}) := by
    conv_lhs => rw [hD]
    rfl
  rw [hsupp, hset, closure_iUnion_of_finite] at hx
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
  rw [← Gluing.StableVal.range_eq_closure_genericPoint q (τ k) (h.section_eq k)] at hk
  obtain ⟨s, rfl⟩ := hk
  exact ⟨k, s, rfl⟩

/-- A section of `q` factors through étale marks containing its image. -/
theorem AreGenericMarkSections.exists_lift [IsSeparated q] (h : AreGenericMarkSections q D' τ)
    (k : Fin n) : ∃ ρ : Spec (.of V) ⟶ D'.subscheme, ρ ≫ D'.subschemeι = τ k := by
  have : QuasiCompact (τ k) := by
    have : QuasiCompact (τ k ≫ q) := by rw [h.section_eq k]; infer_instance
    exact QuasiCompact.of_comp (τ k) q
  have hker : D'.subschemeι.ker ≤ (τ k).ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, Global.ker_eq_vanishingIdeal_closure_range]
    have hle : (⟨closure (Set.range (τ k)), isClosed_closure⟩ : Closeds X) ≤ D'.support :=
      closure_minimal (fun _ ⟨s, hs⟩ ↦ hs ▸ h.apply_mem_support k s) D'.support.isClosed
    refine le_trans ?_ (Scheme.IdealSheafData.vanishingIdeal_antimono hle)
    rw [Scheme.IdealSheafData.vanishingIdeal_support]
    exact Scheme.IdealSheafData.le_radical _
  exact ⟨IsClosedImmersion.lift _ _ hker, IsClosedImmersion.lift_fac _ _ _⟩

/-- **Étale marks give disjoint sections**: two of the sections meeting at a point coincide
(sections of the étale separated `D' → Spec V` over the connected `Spec V`), hence have the same
generic point. -/
theorem AreGenericMarkSections.eq_of_apply_eq [IsSeparated q] [Etale (D'.subschemeι ≫ q)]
    (h : AreGenericMarkSections q D' τ) {k l : Fin n} {s : Spec (.of V)} (hkl : τ k s = τ l s) :
    k = l := by
  obtain ⟨ρk, hρk⟩ := h.exists_lift k
  obtain ⟨ρl, hρl⟩ := h.exists_lift l
  have hk : ρk ≫ D'.subschemeι ≫ q = 𝟙 _ := by rw [← Category.assoc, hρk, h.section_eq k]
  have hl : ρl ≫ D'.subschemeι ≫ q = 𝟙 _ := by rw [← Category.assoc, hρl, h.section_eq l]
  have hs : ρk s = ρl s := by
    apply D'.subschemeι.isClosedEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hρk, ← Scheme.Hom.comp_apply, hρl, hkl]
  have heq : ρk = ρl := Blowups.eq_of_comp_eq_of_apply_eq (D'.subschemeι ≫ q)
    (D'.subschemeι ≫ q) ρk ρl hk hl s hs (by rw [hk, hl])
  apply h.injective
  change τ k _ = τ l _
  rw [← hρk, ← hρl, heq]

/-- **Semi-stable marks pass through smooth points.** -/
theorem AreGenericMarkSections.isSmoothAt [IsSeparated q] (h : AreGenericMarkSections q D' τ)
    (hpair : IsSemistablePair q D') (k : Fin n) (s : Spec (.of V)) : IsSmoothAt q (τ k s) :=
  hpair.smoothAlong _ (h.apply_mem_support k s)

end Sections

section Transport

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [Finite (PrimeSpectrum V)]
  {C X : Scheme.{u}} {φ : C ⟶ Spec (.of V)} {D : C.IdealSheafData} {n : ℕ}
  {c : Fin n → (Spec (.of V) ⟶ C)}

/-- **Lifts of generic mark sections to an η-modification** are generic mark sections of the
transported marks `genericMarksClosure β φ D η` (Temkin, Remark 4.1, T:2810): `β` is a bijection
on the generic fibres (`eq_of_isEtaModification`), and a point of `X` over the generic point lies
on the transported marks iff its image lies on `D` (`Global.mem_genericMarksClosure_iff`). -/
theorem AreGenericMarkSections.of_isEtaModification (hc : AreGenericMarkSections φ D c)
    (β : X ⟶ C) (hβ : Curves.IsEtaModification β φ) (τ : Fin n → (Spec (.of V) ⟶ X))
    (hτ : ∀ k, τ k ≫ β = c k) :
    AreGenericMarkSections (β ≫ φ)
      (Curves.genericMarksClosure β φ D (genericPoint (Spec (.of V)))) τ where
  section_eq k := by rw [← Category.assoc, hτ k, hc.section_eq k]
  injective k l hkl := by
    apply hc.injective
    change c k _ = c l _
    rw [← hτ k, ← hτ l, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact congrArg β hkl
  generic x hx := by
    rw [Global.mem_genericMarksClosure_iff β φ D _ x hx, hc.generic (β x) hx]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have hk' : (τ k ≫ β) (genericPoint (Spec (.of V))) = β x := by rw [hτ k]; exact hk
      have hτη : (β ≫ φ) (τ k (genericPoint (Spec (.of V)))) = genericPoint (Spec (.of V)) := by
        rw [← Scheme.Hom.comp_apply, ← Category.assoc, hτ k, hc.section_eq k]
        rfl
      exact eq_of_isEtaModification φ β hβ hτη hk'
    · rintro ⟨k, rfl⟩
      exact ⟨k, by rw [← Scheme.Hom.comp_apply, hτ k]⟩

end Transport

section Generic

variable {K : Type u} [Field K] [IsAlgClosed K] {W : ValuationSubring K}

/-- **The marks of a curve in the situation of `Global.IsValuationCurve` are sections** (lane
T45B's `Gluing.StableVal.exists_sections_of_etale_genericMarks`; Temkin, proof of Lemma 4.3.3,
T:3025–3027): the generic marks are étale over the algebraically closed `κ(η) = K`. -/
theorem exists_areGenericMarkSections {C : Scheme.{u}} {φ : C ⟶ Spec (.of W)}
    {D : C.IdealSheafData} (hC : Global.IsValuationCurve φ D) :
    ∃ (n : ℕ) (c : Fin n → (Spec (.of W) ⟶ C)), AreGenericMarkSections φ D c := by
  have := hC.isProjectiveOver.isProper
  have := isAlgClosed_residueField W (Gluing.StableVal.pt₀ (V := W))
  have he := hC.genericPair.etale
  rw [Gluing.StableVal.genericPoint_eq_pt₀] at he
  obtain ⟨n, c, hc, hinj, hgen⟩ := Gluing.StableVal.exists_sections_of_etale_genericMarks φ D he
  refine ⟨n, c, hc, ?_, ?_⟩
  · rw [Gluing.StableVal.genericPoint_eq_pt₀]
    exact hinj
  · rw [Gluing.StableVal.genericPoint_eq_pt₀]
    exact hgen

end Generic

end DeJongAlterations.StableModification.Gluing.UniquenessVal
