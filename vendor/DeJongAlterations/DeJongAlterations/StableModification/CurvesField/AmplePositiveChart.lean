/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane OM3E)
-/
import DeJongAlterations.StableModification.CurvesField.AmpleFiber

/-!
# Line-bundle data with generators on the two members of a cover

Lane OM3E (blueprint `sm-curves-fields-ample-positive.tex`) derives the hypothesis of lane OM3B's
ampleness criterion (`CurvesField.serreAmple_of_section`: a section of `𝓛^n` which does not vanish
at the non-closed points and vanishes at a specialization of each of them) from positivity of the
degree of `𝓛` on the components of a curve. This is the fibre input of the projectivity theorem of
M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), Theorem 1.1
(`references/temkin10-stable-modification/source/semi-stable.tex`, lines 1713--1749, "the
classical computation", lines 1735--1741).

Degrees are computed on the two-term Čech complex of a cover `X = U ∪ V`. This file generalizes
OM3B's `CurvesField.Ample.LineBundleData.twoChartIso` (a global section on `U`, a generator on
`V`) to **two local generators**: if `τ` generates `𝓛^N` on `U` and `σ` generates `𝓛^N` on `V`,
with transition function `g = τ / σ ∈ Γ(U ∩ V, 𝒪)ˣ`, then `F ⊗ 𝓛^{N k}` is the twist
`CurvesField.twist F U V (g^k)` of `F` along `(U, V)` (lane COH4): a section `t` corresponds to the
pair `(t / τ^k, t / σ^k)`.

## Main definitions and results

* `transFun hσ τ`, `transUnit hτ hσ`: the transition function `g = τ / σ`, a unit on `U ∩ V`,
  with `τ|_{U ∩ V} = g · σ|_{U ∩ V}` (`restrict_eq_transFun_smul`).
* `twoTrivIso : F ⊗ 𝓛^{N k} ≅ twist F U V (g^k)`.
* `globalSectionsEquiv`: global sections of `𝓛^{N k}` are the pairs `(a, b) ∈ Γ(U) × Γ(V)` with
  `b| = g^k a|` on `U ∩ V`.
* `cohomologyIsoOfIso`: cohomology is invariant under isomorphisms of modules.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open DeJongAlterations.StableModification.Cohomology
open DeJongAlterations.StableModification.Projectivity

namespace DeJongAlterations.StableModification.CurvesField.Positive

noncomputable section

open Ample Ample.LineBundleData Projectivity.LineBundleData

variable {X : Scheme.{u}}

/-- **Cohomology is invariant under isomorphisms of modules.** -/
def cohomologyIsoOfIso [CompactSpace X]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))] {M N : X.Modules}
    (e : M ≅ N) {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) (p : ℕ) :
    cohomology M c p ≅ cohomology N c p :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) p).mapIso
    ((cechComplexFunctor (FiniteAffineCover.choose X).U c).mapIso e)

variable {L : Projectivity.LineBundleData X}

section TwoTriv

variable {N : ℤ} {U V : X.Opens} {τ : L.Sections N U} {σ : L.Sections N V}

lemma nonvanishingLocus_restrict_of_eq {W W' : X.Opens} {s : L.Sections N W}
    (hs : s.nonvanishingLocus = W) (h : W' ≤ W) : (s.restrict h).nonvanishingLocus = W' := by
  rw [Sections.nonvanishingLocus_restrict, hs]
  exact inf_eq_left.mpr h

variable (τ) (hσ : σ.nonvanishingLocus = V)

/-- The **transition function** `τ / σ ∈ Γ(U ∩ V, 𝒪)`. -/
def transFun : Γ(X, U ⊓ V) :=
  (mulSecEquiv (unitModule X)
    (nonvanishingLocus_restrict_of_eq hσ (inf_le_right : U ⊓ V ≤ V))).symm
    (τ.restrict (inf_le_left : U ⊓ V ≤ U))

lemma restrict_eq_transFun_smul :
    τ.restrict (inf_le_left : U ⊓ V ≤ U) =
      transFun τ hσ • σ.restrict (inf_le_right : U ⊓ V ≤ V) := by
  rw [← mulSec_unit]
  exact (mulSec_mulSecEquiv_symm (unitModule X) _ _).symm

variable {τ}

lemma basicOpen_transFun (hτ : τ.nonvanishingLocus = U) : X.basicOpen (transFun τ hσ) = U ⊓ V := by
  have h := congrArg Sections.nonvanishingLocus (restrict_eq_transFun_smul τ hσ)
  rw [nonvanishingLocus_restrict_of_eq hτ, Sections.nonvanishingLocus_smul,
    nonvanishingLocus_restrict_of_eq hσ] at h
  exact le_antisymm (X.basicOpen_le _) (h.le.trans inf_le_left)

lemma isUnit_transFun (hτ : τ.nonvanishingLocus = U) : IsUnit (transFun τ hσ) :=
  isUnit_of_basicOpen_eq (basicOpen_transFun hσ hτ)

/-- The transition function as a unit of `Γ(U ∩ V, 𝒪)`. -/
def transUnit (hτ : τ.nonvanishingLocus = U) : Γ(X, U ⊓ V)ˣ := (isUnit_transFun hσ hτ).unit

lemma coe_transUnit (hτ : τ.nonvanishingLocus = U) : (transUnit hσ hτ : Γ(X, U ⊓ V)) = transFun τ hσ :=
  IsUnit.unit_spec _

lemma coe_transUnit_zpow (hτ : τ.nonvanishingLocus = U) (k : ℕ) :
    ((transUnit hσ hτ ^ (k : ℤ) : Γ(X, U ⊓ V)ˣ) : Γ(X, U ⊓ V)) = transFun τ hσ ^ k := by
  rw [zpow_natCast, Units.val_pow_eq_pow_val, coe_transUnit]

/-- `τ^k` on `W ∩ U`. -/
abbrev secU' (τ : L.Sections N U) (k : ℕ) (W : X.Opens) : L.Sections (N * k) (W ⊓ U) :=
  (τ.npow k).restrict (inf_le_right : W ⊓ U ≤ U)

lemma nonvanishingLocus_secU' (hτ : τ.nonvanishingLocus = U) (k : ℕ) (W : X.Opens) :
    (secU' τ k W).nonvanishingLocus = W ⊓ U := by
  rw [Sections.nonvanishingLocus_restrict, Sections.nonvanishingLocus_npow_of_eq τ hτ k]
  exact inf_eq_left.mpr inf_le_right

/-- On `W' ⊆ U ∩ V`, `τ^k = g^k σ^k`. -/
lemma npow_restrict_eq' (k : ℕ) {W' : X.Opens} (h : W' ≤ U ⊓ V) :
    (τ.npow k).restrict (h.trans inf_le_left) =
      X.presheaf.map (homOfLE h).op (transFun τ hσ ^ k) •
        (σ.npow k).restrict (h.trans inf_le_right) := by
  rw [← Sections.restrict_restrict (inf_le_left : U ⊓ V ≤ U) h, Sections.npow_restrict,
    restrict_eq_transFun_smul τ hσ, Sections.smul_npow, Sections.restrict_smul,
    ← Sections.npow_restrict, Sections.restrict_restrict]

variable (hτ : τ.nonvanishingLocus = U) (F : X.Modules)

/-- The pair of local coefficients `(t / τ^k, t / σ^k)` of a section `t` of `F ⊗ 𝓛^{Nk}`. -/
def toPair' (k : ℕ) (W : X.Opens) (t : L.twistSubgroup F (N * k) W) :
    Γ(F, W ⊓ U) × Γ(F, W ⊓ V) :=
  ((mulSecEquiv F (nonvanishingLocus_secU' hτ k W)).symm
      (L.twistRestrict F _ (inf_le_left : W ⊓ U ≤ W) t),
    (mulSecEquiv F (nonvanishingLocus_secV hσ k W)).symm
      (L.twistRestrict F _ (inf_le_left : W ⊓ V ≤ W) t))

variable (k : ℕ)

lemma mulSec_toPair'_fst (W : X.Opens) (t : L.twistSubgroup F (N * k) W) :
    mulSec F (secU' τ k W) (toPair' hσ hτ F k W t).1 = L.twistRestrict F _ inf_le_left t :=
  mulSec_mulSecEquiv_symm F _ _

lemma mulSec_toPair'_snd (W : X.Opens) (t : L.twistSubgroup F (N * k) W) :
    mulSec F (secV σ k W) (toPair' hσ hτ F k W t).2 = L.twistRestrict F _ inf_le_left t :=
  mulSec_mulSecEquiv_symm F _ _

lemma toPair'_fst_eq_iff (W : X.Opens) (t : L.twistSubgroup F (N * k) W) (a : Γ(F, W ⊓ U)) :
    (toPair' hσ hτ F k W t).1 = a ↔
      mulSec F (secU' τ k W) a = L.twistRestrict F _ inf_le_left t :=
  (LinearEquiv.symm_apply_eq _).trans eq_comm

lemma toPair'_snd_eq_iff (W : X.Opens) (t : L.twistSubgroup F (N * k) W) (b : Γ(F, W ⊓ V)) :
    (toPair' hσ hτ F k W t).2 = b ↔
      mulSec F (secV σ k W) b = L.twistRestrict F _ inf_le_left t :=
  (LinearEquiv.symm_apply_eq _).trans eq_comm

/-- **The local coefficients satisfy the gluing condition of the twist by `g^k`**: on
`W ∩ U ∩ V`, `t / σ^k = g^k · (t / τ^k)`. -/
lemma toPair'_twistCond (W : X.Opens) (t : L.twistSubgroup F (N * k) W) :
    TwistCond F U V (transUnit hσ hτ ^ (k : ℤ)) W (toPair' hσ hτ F k W t).1
      (toPair' hσ hτ F k W t).2 := by
  unfold TwistCond
  have h₃ : W ⊓ (U ⊓ V) ≤ V := (twist_le₃ U V W).trans inf_le_right
  set σ₃ : L.Sections (N * k) (W ⊓ (U ⊓ V)) := (σ.npow k).restrict h₃
  have hD : σ₃.nonvanishingLocus = W ⊓ (U ⊓ V) := by
    rw [Sections.nonvanishingLocus_restrict, Sections.nonvanishingLocus_npow_of_eq σ hσ k]
    exact inf_eq_left.mpr h₃
  apply (mulSec_bijective F hD).1
  have e₂ : σ₃ = (secV σ k W).restrict (twist_le₂ U V W) := by
    rw [Sections.restrict_restrict]
  have e₁ : X.presheaf.map (homOfLE (twist_le₃ U V W)).op
      ((transUnit hσ hτ ^ (k : ℤ) : Γ(X, U ⊓ V)ˣ) : Γ(X, U ⊓ V)) • σ₃ =
      (secU' τ k W).restrict (twist_le₁ U V W) := by
    rw [coe_transUnit_zpow, Sections.restrict_restrict]
    exact (npow_restrict_eq' hσ k (twist_le₃ U V W)).symm
  rw [← mulSec_smul_sec, e₁, e₂, ← mulSec_restrict, ← mulSec_restrict,
    mulSec_toPair'_fst, mulSec_toPair'_snd, twistRestrict_twistRestrict,
    twistRestrict_twistRestrict]

lemma toPair'_restrict {W W' : X.Opens} (h : W' ≤ W) (t : L.twistSubgroup F (N * k) W) :
    toPair' hσ hτ F k W' (L.twistRestrict F _ h t) =
      (F.presheaf.map (homOfLE (inf_le_inf_right U h)).op (toPair' hσ hτ F k W t).1,
        F.presheaf.map (homOfLE (inf_le_inf_right V h)).op (toPair' hσ hτ F k W t).2) := by
  apply Prod.ext
  · rw [toPair'_fst_eq_iff]
    have e : secU' τ k W' = (secU' τ k W).restrict (inf_le_inf_right U h) := by
      rw [Sections.restrict_restrict]
    rw [e, ← mulSec_restrict, mulSec_toPair'_fst, twistRestrict_twistRestrict,
      twistRestrict_twistRestrict]
  · rw [toPair'_snd_eq_iff]
    have e : secV σ k W' = (secV σ k W).restrict (inf_le_inf_right V h) := by
      rw [Sections.restrict_restrict]
    rw [e, ← mulSec_restrict, mulSec_toPair'_snd, twistRestrict_twistRestrict,
      twistRestrict_twistRestrict]

lemma toPair'_add (W : X.Opens) (t t' : L.twistSubgroup F (N * k) W) :
    toPair' hσ hτ F k W (t + t') = toPair' hσ hτ F k W t + toPair' hσ hτ F k W t' := by
  simp only [toPair', map_add, Prod.mk_add_mk]

lemma toPair'_smul (W : X.Opens) (r : Γ(X, W)) (t : L.twistSubgroup F (N * k) W) :
    toPair' hσ hτ F k W (r • t) =
      (resU U W r • (toPair' hσ hτ F k W t).1, resV V W r • (toPair' hσ hτ F k W t).2) := by
  apply Prod.ext
  · rw [toPair'_fst_eq_iff, mulSec_smul, mulSec_toPair'_fst,
      Projectivity.LineBundleData.twistRestrict_smul]
  · rw [toPair'_snd_eq_iff, mulSec_smul, mulSec_toPair'_snd,
      Projectivity.LineBundleData.twistRestrict_smul]

lemma toPair'_injective (hUV : U ⊔ V = ⊤) (W : X.Opens) :
    Function.Injective (toPair' hσ hτ F k W) := by
  intro t t' h
  have h₁ : L.twistRestrict F _ (inf_le_left : W ⊓ U ≤ W) t =
      L.twistRestrict F _ (inf_le_left : W ⊓ U ≤ W) t' := by
    rw [← mulSec_toPair'_fst hσ hτ F k W t, ← mulSec_toPair'_fst hσ hτ F k W t',
      congrArg Prod.fst h]
  have h₂ : L.twistRestrict F _ (inf_le_left : W ⊓ V ≤ W) t =
      L.twistRestrict F _ (inf_le_left : W ⊓ V ≤ W) t' := by
    rw [← mulSec_toPair'_snd hσ hτ F k W t, ← mulSec_toPair'_snd hσ hτ F k W t',
      congrArg Prod.snd h]
  exact (twistSheafAb (L.twist F (N * k))).eq_of_locally_eq₂
    (homOfLE (inf_le_left : W ⊓ U ≤ W)) (homOfLE (inf_le_left : W ⊓ V ≤ W))
    (le_sup_inf hUV W) t t' h₁ h₂

lemma toPair'_surjective (hUV : U ⊔ V = ⊤) (W : X.Opens) (p : Γ(F, W ⊓ U) × Γ(F, W ⊓ V))
    (hp : TwistCond F U V (transUnit hσ hτ ^ (k : ℤ)) W p.1 p.2) :
    ∃ t, toPair' hσ hτ F k W t = p := by
  have h₄ : W ⊓ U ⊓ (W ⊓ V) ≤ W ⊓ (U ⊓ V) := fun x hx => ⟨hx.1.1, hx.1.2, hx.2.2⟩
  have h₅ : W ⊓ U ⊓ (W ⊓ V) ≤ U ⊓ V := h₄.trans (twist_le₃ U V W)
  have hxy : L.twistRestrict F _ (inf_le_left : W ⊓ U ⊓ (W ⊓ V) ≤ W ⊓ U)
      (mulSec F (secU' τ k W) p.1) =
      L.twistRestrict F _ (inf_le_right : W ⊓ U ⊓ (W ⊓ V) ≤ W ⊓ V)
      (mulSec F (secV σ k W) p.2) := by
    rw [mulSec_restrict, mulSec_restrict, Sections.restrict_restrict, Sections.restrict_restrict,
      npow_restrict_eq' hσ k h₅, mulSec_smul_sec]
    congr 1
    have e := congrArg (F.presheaf.map (homOfLE h₄).op) hp
    rw [presheaf_map_map, Scheme.Modules.map_smul, presheaf_map_map, coe_transUnit_zpow,
      ringMap_ringMap _ _ h₅] at e
    exact e.symm
  obtain ⟨t, ht₁, ht₂⟩ := exists_glue₂ (twistSheafAb (L.twist F (N * k)))
    (inf_le_left : W ⊓ U ≤ W) (inf_le_left : W ⊓ V ≤ W) (le_sup_inf hUV W)
    (mulSec F (secU' τ k W) p.1) (mulSec F (secV σ k W) p.2) hxy
  exact ⟨t, Prod.ext ((toPair'_fst_eq_iff hσ hτ F k W t p.1).mpr ht₁.symm)
    ((toPair'_snd_eq_iff hσ hτ F k W t p.2).mpr ht₂.symm)⟩

/-- **The comparison** `F ⊗ 𝓛^{Nk} ⟶ twist F U V (g^k)`, `t ↦ (t / τ^k, t / σ^k)`. -/
def twoTrivHom : L.twist F (N * k) ⟶ twist F U V (transUnit hσ hτ ^ (k : ℤ)) where
  val := PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom
        { toFun := fun t => (⟨toPair' hσ hτ F k W.unop t, toPair'_twistCond hσ hτ F k W.unop t⟩ :
            twistSubgroup F U V (transUnit hσ hτ ^ (k : ℤ)) W.unop)
          map_zero' := Subtype.ext (by
            have h := toPair'_add hσ hτ F k W.unop 0 0
            rw [add_zero] at h
            exact (add_eq_left.mp h.symm))
          map_add' := fun t t' => Subtype.ext (toPair'_add hσ hτ F k W.unop t t') }
      naturality := fun {W W'} i => by
        ext t
        apply Subtype.ext
        exact toPair'_restrict hσ hτ F k (leOfHom i.unop) t }
    (fun W r t => Subtype.ext (toPair'_smul hσ hτ F k W.unop r t))

lemma twoTrivHom_app (W : X.Opens) (t : L.twistSubgroup F (N * k) W) :
    (show twistSubgroup F U V (transUnit hσ hτ ^ (k : ℤ)) W from
      (twoTrivHom hσ hτ F k).app W t).1 = toPair' hσ hτ F k W t :=
  rfl

theorem isIso_twoTrivHom (hUV : U ⊔ V = ⊤) : IsIso (twoTrivHom hσ hτ F k) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro W
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun t t' h => toPair'_injective hσ hτ F k hUV W (congrArg Subtype.val h),
    fun p => ?_⟩
  obtain ⟨t, ht⟩ := toPair'_surjective hσ hτ F k hUV W p.1 p.2
  exact ⟨t, Subtype.ext ht⟩

/-- **`F ⊗ 𝓛^{Nk} ≅ twist F U V (g^k)`** for line-bundle data generated by `τ` on `U` and by `σ`
on `V`, with transition function `g = τ / σ`. -/
def twoTrivIso (hUV : U ⊔ V = ⊤) :
    L.twist F (N * k) ≅ twist F U V (transUnit hσ hτ ^ (k : ℤ)) :=
  haveI := isIso_twoTrivHom hσ hτ F k hUV
  asIso (twoTrivHom hσ hτ F k)

end TwoTriv

end

end DeJongAlterations.StableModification.CurvesField.Positive
