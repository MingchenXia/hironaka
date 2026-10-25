/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane OM3B)
-/
import DeJongAlterations.StableModification.Projectivity.LineBundleOpsIso
import DeJongAlterations.StableModification.Projectivity.LineBundleOpsHyperplane
import DeJongAlterations.StableModification.CurvesField.RiemannRoch


/-!
# Line-bundle data trivialized on two charts

Lane OM3B (PLAN-OM3 node group M3, blueprint `sm-curves-fields-ample.tex`) proves that a line
bundle on a projective curve over a field which has a section vanishing in finitely many points,
at least one on every one-dimensional irreducible component, is ample in Serre's sense (OM3A's
`Projectivity.LineBundleData.SerreAmple`, hence `Projectivity.FiberAmple`). This is the fibre
input of the projectivity theorem of M. Temkin, *Stable modification of relative curves*,
J. Algebraic Geom. 19 (2010), Theorem 1.1 (`references/temkin10-stable-modification/source/
semi-stable.tex`, lines 1713--1749: "relative ampleness can be checked separately on each fiber").

Cohomology of curves over a field is computed (lane COH4, `CurvesField.RiemannRoch`) with the
two-term Čech complex of a cover `X = U ∪ V` and the twists `F(mD) = divisorTwist F U V hf m` of a
module along that cover by the powers of a function `f ∈ Γ(V, 𝒪)` which is a unit on `U ∩ V`.
This file identifies the twists `F ⊗ 𝓛^{N k}` of OM3A's line-bundle data with these divisor twists,
when `𝓛^N` is trivialized on `U` by a global section `s` (`U ⊆ D(s)`) and on `V` by a nowhere
vanishing section `σ`: the transition function is the ratio `f = s / σ ∈ Γ(V, 𝒪)`.

## Main definitions and results

* `exists_glue₂`: gluing of sections of a sheaf of abelian groups over two opens.
* `LineBundleData.mulSec F σ : Γ(W, F) → Γ(W, F ⊗ 𝓛^m)`, `a ↦ σ · a` (coefficientwise), linear,
  compatible with restriction; bijective when `σ` vanishes nowhere on `W` (`mulSec_bijective`,
  `mulSecEquiv`): over an open on which `𝓛^m` has a generator, `F ⊗ 𝓛^m` is `F`.
* `LineBundleData.ratio s hσ = s / σ ∈ Γ(V, 𝒪)`, with `s|_V = (s/σ) σ`
  (`restrict_eq_ratio_smul`) and `D(s/σ) = V ∩ D(s)` (`basicOpen_ratio`); it is a unit on
  `U ∩ V` (`isUnit_ratio`).
* `LineBundleData.toPair`: a section `t` of `F ⊗ 𝓛^{N k}` over `W` gives the pair of local
  coefficients `(t / s^k, t / σ^k) ∈ Γ(W ∩ U, F) × Γ(W ∩ V, F)`, which satisfies the gluing
  condition of the divisor twist (`toPair_twistCond`).
* `LineBundleData.twoChartIso : F ⊗ 𝓛^{N k} ≅ F(kD)` (blueprint `lem:sm-ample-two-chart`).
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open DeJongAlterations.StableModification.Cohomology
open DeJongAlterations.StableModification.Projectivity

namespace DeJongAlterations.StableModification.CurvesField.Ample

noncomputable section

variable {X : Scheme.{u}}

/-! ### Binary gluing -/

/-- Sections of a sheaf of abelian groups over two opens which agree on the overlap glue. -/
lemma exists_glue₂ (G : TopCat.Sheaf Ab.{u} X) {U₁ U₂ V : X.Opens} (h₁ : U₁ ≤ V) (h₂ : U₂ ≤ V)
    (hcov : V ≤ U₁ ⊔ U₂) (x : ToType (G.1.obj (op U₁))) (y : ToType (G.1.obj (op U₂)))
    (hxy : G.1.map (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).op x =
      G.1.map (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).op y) :
    ∃ s : ToType (G.1.obj (op V)), G.1.map (homOfLE h₁).op s = x ∧
      G.1.map (homOfLE h₂).op s = y := by
  let W : ULift.{u} Bool → X.Opens := fun t => cond t.down U₁ U₂
  let sf : ∀ t : ULift.{u} Bool, ToType (G.1.obj (op (W t))) := fun t =>
    match t with
    | ⟨true⟩ => x
    | ⟨false⟩ => y
  have hyx : G.1.map (homOfLE (inf_le_left : U₂ ⊓ U₁ ≤ U₂)).op y =
      G.1.map (homOfLE (inf_le_right : U₂ ⊓ U₁ ≤ U₁)).op x := by
    have e := congrArg (G.1.map (homOfLE (le_of_eq (inf_comm U₂ U₁))).op) hxy
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← G.1.map_comp,
      ← G.1.map_comp] at e
    exact e.symm
  have hcompat : TopCat.Presheaf.IsCompatible G.1 W sf := by
    rintro ⟨_ | _⟩ ⟨_ | _⟩
    · rfl
    · exact hyx
    · exact hxy
    · rfl
  have hc : V ≤ iSup W := by
    refine hcov.trans (sup_le ?_ ?_)
    · exact le_iSup W ⟨true⟩
    · exact le_iSup W ⟨false⟩
  obtain ⟨s, hs, -⟩ := G.existsUnique_gluing' W V (fun t => match t with
    | ⟨true⟩ => homOfLE h₁
    | ⟨false⟩ => homOfLE h₂) hc sf hcompat
  exact ⟨s, hs ⟨true⟩, hs ⟨false⟩⟩

namespace LineBundleData

open Projectivity.LineBundleData

variable {L : Projectivity.LineBundleData X}

/-! ### Restrictions -/

lemma twistRestrict_twistRestrict (F : X.Modules) (m : ℤ) {W₁ W₂ W₃ : X.Opens} (h₁ : W₂ ≤ W₁)
    (h₂ : W₃ ≤ W₂) (t : L.twistSubgroup F m W₁) :
    L.twistRestrict F m h₂ (L.twistRestrict F m h₁ t) = L.twistRestrict F m (h₂.trans h₁) t := by
  apply Subtype.ext
  funext i
  exact presheaf_map_map F _ _ _ _

lemma Sections.restrict_restrict {m : ℤ} {W₁ W₂ W₃ : X.Opens} (h₁ : W₂ ≤ W₁) (h₂ : W₃ ≤ W₂)
    (s : L.Sections m W₁) : (s.restrict h₁).restrict h₂ = s.restrict (h₂.trans h₁) :=
  twistRestrict_twistRestrict (unitModule X) m h₁ h₂ s

lemma Sections.npow_restrict {m : ℤ} {W W' : X.Opens} (h : W' ≤ W) (s : L.Sections m W)
    (k : ℕ) : (s.npow k).restrict h = (s.restrict h).npow k := by
  ext i
  simp only [Sections.coeff_restrict, Sections.coeff_npow, map_pow]

lemma Sections.smul_npow {m : ℤ} {W : X.Opens} (r : Γ(X, W)) (s : L.Sections m W) (k : ℕ) :
    (r • s).npow k = r ^ k • s.npow k := by
  ext i
  simp only [Sections.coeff_npow, Sections.coeff_smul, mul_pow, map_pow]

lemma Sections.restrict_smul {m : ℤ} {W W' : X.Opens} (h : W' ≤ W) (r : Γ(X, W))
    (s : L.Sections m W) :
    (r • s).restrict h = X.presheaf.map (homOfLE h).op r • s.restrict h := by
  ext i
  simp only [Sections.coeff_restrict, Sections.coeff_smul, map_mul]
  congr 1
  exact (res_res _ _ (inf_le_left.trans h) r).trans (res_res h inf_le_left _ r).symm

/-- A section with non-vanishing locus `W` has all powers with non-vanishing locus `W`. -/
lemma Sections.nonvanishingLocus_npow_of_eq {m : ℤ} {W : X.Opens} (s : L.Sections m W)
    (hs : s.nonvanishingLocus = W) (k : ℕ) : (s.npow k).nonvanishingLocus = W := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · apply le_antisymm (Sections.nonvanishingLocus_le _)
    intro x hx
    obtain ⟨i, hi⟩ := L.exists_mem_U x
    rw [Sections.mem_nonvanishingLocus_iff _ hi, Sections.coeff_npow, pow_zero,
      Scheme.basicOpen_one]
    exact ⟨hx, hi⟩
  · rw [Sections.nonvanishingLocus_npow _ hk, hs]

/-- The powers of a section are non-vanishing wherever the section is, `U ≤ D(s)`. -/
lemma Sections.le_nonvanishingLocus_npow {m : ℤ} {W U : X.Opens} (s : L.Sections m W)
    (hU : U ≤ s.nonvanishingLocus) (k : ℕ) : U ≤ (s.npow k).nonvanishingLocus := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · intro x hx
    have hxW : x ∈ W := s.nonvanishingLocus_le (hU hx)
    obtain ⟨i, hi⟩ := L.exists_mem_U x
    rw [Sections.mem_nonvanishingLocus_iff _ hi, Sections.coeff_npow, pow_zero,
      Scheme.basicOpen_one]
    exact ⟨hxW, hi⟩
  · rwa [Sections.nonvanishingLocus_npow _ hk]

/-! ### Multiplication by a section -/

section MulSec

variable (F : X.Modules) {m : ℤ} {W : X.Opens} (σ : L.Sections m W)

/-- **Multiplication by a section** `σ` of `𝓛^m` over `W`: `Γ(W, F) → Γ(W, F ⊗ 𝓛^m)`,
`a ↦ σ · a` (coefficientwise `σ_i · a|`). -/
def mulSec (a : Γ(F, W)) : L.twistSubgroup F m W :=
  ⟨fun i => σ.coeff i • F.presheaf.map (homOfLE (inf_le_left : W ⊓ L.U i ≤ W)).op a, by
    intro i j
    simp only
    rw [Scheme.Modules.map_smul, Scheme.Modules.map_smul, σ.coeff_compat, smul_smul,
      presheaf_map_map F _ _ ((L.le_left W i j).trans inf_le_left),
      presheaf_map_map F _ _ ((L.le_right W i j).trans inf_le_left)]⟩

@[simp]
lemma mulSec_apply (a : Γ(F, W)) (i : L.ι) :
    (mulSec F σ a).1 i = σ.coeff i • F.presheaf.map (homOfLE (inf_le_left : W ⊓ L.U i ≤ W)).op a :=
  rfl

lemma mulSec_add (a b : Γ(F, W)) : mulSec F σ (a + b) = mulSec F σ a + mulSec F σ b := by
  apply Subtype.ext
  funext i
  change σ.coeff i • F.presheaf.map (homOfLE (inf_le_left : W ⊓ L.U i ≤ W)).op (a + b) =
    σ.coeff i • F.presheaf.map (homOfLE (inf_le_left : W ⊓ L.U i ≤ W)).op a +
    σ.coeff i • F.presheaf.map (homOfLE (inf_le_left : W ⊓ L.U i ≤ W)).op b
  rw [map_add, smul_add]

lemma mulSec_smul (r : Γ(X, W)) (a : Γ(F, W)) : mulSec F σ (r • a) = r • mulSec F σ a := by
  apply Subtype.ext
  funext i
  change σ.coeff i • F.presheaf.map (homOfLE (inf_le_left : W ⊓ L.U i ≤ W)).op (r • a) =
    res (inf_le_left : W ⊓ L.U i ≤ W) r •
      (σ.coeff i • F.presheaf.map (homOfLE (inf_le_left : W ⊓ L.U i ≤ W)).op a)
  rw [Scheme.Modules.map_smul, smul_comm]

/-- Multiplication by `σ` as a `Γ(X, W)`-linear map. -/
def mulSecLinear : Γ(F, W) →ₗ[Γ(X, W)] L.twistSubgroup F m W where
  toFun := mulSec F σ
  map_add' := mulSec_add F σ
  map_smul' := mulSec_smul F σ

lemma mulSec_smul_sec (r : Γ(X, W)) (a : Γ(F, W)) : mulSec F (r • σ) a = mulSec F σ (r • a) := by
  apply Subtype.ext
  funext i
  change (res (inf_le_left : W ⊓ L.U i ≤ W) r * σ.coeff i) •
      F.presheaf.map (homOfLE (inf_le_left : W ⊓ L.U i ≤ W)).op a =
    σ.coeff i • F.presheaf.map (homOfLE (inf_le_left : W ⊓ L.U i ≤ W)).op (r • a)
  rw [Scheme.Modules.map_smul, smul_smul, mul_comm]

lemma mulSec_restrict {W' : X.Opens} (h : W' ≤ W) (a : Γ(F, W)) :
    L.twistRestrict F m h (mulSec F σ a) =
      mulSec F (σ.restrict h) (F.presheaf.map (homOfLE h).op a) := by
  apply Subtype.ext
  funext i
  change F.presheaf.map _ (σ.coeff i • F.presheaf.map _ a) =
    X.presheaf.map _ (σ.coeff i) • F.presheaf.map _ (F.presheaf.map _ a)
  rw [Scheme.Modules.map_smul, presheaf_map_map F _ _ (inf_le_left.trans h),
    presheaf_map_map F _ _ (inf_le_left.trans h)]

variable {σ}

/-- **Multiplication by a nowhere vanishing section is bijective.** -/
theorem mulSec_bijective (hσ : σ.nonvanishingLocus = W) : Function.Bijective (mulSec F σ) := by
  have hu := Sections.isUnit_coeff_of_nonvanishingLocus_eq σ hσ
  choose v hv using hu
  constructor
  · intro a a' h
    apply L.eq_of_forall_chart F
    intro i
    have hi := congrFun (congrArg Subtype.val h) i
    change σ.coeff i • F.presheaf.map _ a = σ.coeff i • F.presheaf.map _ a' at hi
    rw [← hv i] at hi
    have := congrArg (fun z => (((v i)⁻¹ : Γ(X, W ⊓ L.U i)ˣ) : Γ(X, W ⊓ L.U i)) • z) hi
    simpa only [smul_smul, Units.inv_mul, one_smul] using this
  · intro t
    obtain ⟨a, ha⟩ := L.exists_glue_cover F W
      (fun i => (((v i)⁻¹ : Γ(X, W ⊓ L.U i)ˣ) : Γ(X, W ⊓ L.U i)) • t.1 i) (by
        intro i j
        have ht := t.2 i j
        have hsc := σ.coeff_compat i j
        rw [← hv i, ← hv j] at hsc
        rw [Scheme.Modules.map_smul, Scheme.Modules.map_smul, ht, smul_smul]
        congr 1
        set a := X.presheaf.map (homOfLE (L.le_left W i j)).op (v i : Γ(X, W ⊓ L.U i))
        set b := X.presheaf.map (homOfLE (L.le_right W i j)).op (v j : Γ(X, W ⊓ L.U j))
        have ha : X.presheaf.map (homOfLE (L.le_left W i j)).op
            (((v i)⁻¹ : Γ(X, W ⊓ L.U i)ˣ) : Γ(X, W ⊓ L.U i)) * a = 1 := by
          rw [← map_mul, Units.inv_mul, map_one]
        have hb : X.presheaf.map (homOfLE (L.le_right W i j)).op
            (((v j)⁻¹ : Γ(X, W ⊓ L.U j)ˣ) : Γ(X, W ⊓ L.U j)) * b = 1 := by
          rw [← map_mul, Units.inv_mul, map_one]
        have hsc' : a = L.transPow m W i j * b := hsc
        calc X.presheaf.map (homOfLE (L.le_left W i j)).op
              (((v i)⁻¹ : Γ(X, W ⊓ L.U i)ˣ) : Γ(X, W ⊓ L.U i)) * L.transPow m W i j
            = X.presheaf.map (homOfLE (L.le_left W i j)).op
                (((v i)⁻¹ : Γ(X, W ⊓ L.U i)ˣ) : Γ(X, W ⊓ L.U i)) * L.transPow m W i j *
                (X.presheaf.map (homOfLE (L.le_right W i j)).op
                  (((v j)⁻¹ : Γ(X, W ⊓ L.U j)ˣ) : Γ(X, W ⊓ L.U j)) * b) := by rw [hb, mul_one]
          _ = X.presheaf.map (homOfLE (L.le_right W i j)).op
                (((v j)⁻¹ : Γ(X, W ⊓ L.U j)ˣ) : Γ(X, W ⊓ L.U j)) *
                (X.presheaf.map (homOfLE (L.le_left W i j)).op
                  (((v i)⁻¹ : Γ(X, W ⊓ L.U i)ˣ) : Γ(X, W ⊓ L.U i)) *
                  (L.transPow m W i j * b)) := by ring
          _ = X.presheaf.map (homOfLE (L.le_right W i j)).op
                (((v j)⁻¹ : Γ(X, W ⊓ L.U j)ˣ) : Γ(X, W ⊓ L.U j)) := by
              rw [← hsc', ha, mul_one])
    refine ⟨a, Subtype.ext (funext fun i => ?_)⟩
    change σ.coeff i • F.presheaf.map _ a = t.1 i
    rw [ha i, ← hv i, smul_smul, Units.mul_inv, one_smul]

/-- Multiplication by a nowhere vanishing section, as a linear equivalence. -/
def mulSecEquiv (hσ : σ.nonvanishingLocus = W) : Γ(F, W) ≃ₗ[Γ(X, W)] L.twistSubgroup F m W :=
  LinearEquiv.ofBijective (mulSecLinear F σ) (mulSec_bijective F hσ)

@[simp]
lemma mulSecEquiv_apply (hσ : σ.nonvanishingLocus = W) (a : Γ(F, W)) :
    mulSecEquiv F hσ a = mulSec F σ a :=
  rfl

lemma mulSec_mulSecEquiv_symm (hσ : σ.nonvanishingLocus = W) (t : L.twistSubgroup F m W) :
    mulSec F σ ((mulSecEquiv F hσ).symm t) = t :=
  (mulSecEquiv F hσ).apply_symm_apply t



end MulSec

/-! ### Multiplication by a section and functions -/

section Unit

variable {m : ℤ} {W : X.Opens}

lemma mulSec_unit (σ : L.Sections m W) (a : Γ(X, W)) :
    (mulSec (unitModule X) σ a : L.Sections m W) = a • σ := by
  ext i
  change σ.coeff i * X.presheaf.map (homOfLE (inf_le_left : W ⊓ L.U i ≤ W)).op a =
    res (inf_le_left : W ⊓ L.U i ≤ W) a * σ.coeff i
  exact mul_comm _ _

lemma Sections.nonvanishingLocus_smul (r : Γ(X, W)) (σ : L.Sections m W) :
    (r • σ).nonvanishingLocus = X.basicOpen r ⊓ σ.nonvanishingLocus := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    rw [Sections.coeff_smul, X.basicOpen_mul, Scheme.basicOpen_res]
    exact inf_le_inf (inf_le_right) (σ.basicOpen_coeff_le i)
  · rintro x ⟨hr, hx⟩
    obtain ⟨i, hi⟩ := L.exists_mem_U x
    rw [Sections.mem_nonvanishingLocus_iff _ hi, Sections.coeff_smul, X.basicOpen_mul,
      Scheme.basicOpen_res]
    exact ⟨⟨⟨X.basicOpen_le r hr, hi⟩, hr⟩, (σ.mem_nonvanishingLocus_iff hi).mp hx⟩

end Unit

/-! ### Two charts -/

section TwoChart

variable {N : ℤ} {U V : X.Opens} (s : L.Sections N ⊤) {σ : L.Sections N V}
  (hσ : σ.nonvanishingLocus = V)

/-- The **ratio** `s / σ ∈ Γ(V, 𝒪)` of a global section `s` of `𝓛^N` by a nowhere vanishing
section `σ` of `𝓛^N` over `V`. -/
def ratio : Γ(X, V) := (mulSecEquiv (unitModule X) hσ).symm (s.restrict (le_top : V ≤ ⊤))

lemma restrict_eq_ratio_smul : s.restrict (le_top : V ≤ ⊤) = ratio s hσ • σ := by
  rw [← mulSec_unit]
  exact (mulSec_mulSecEquiv_symm (unitModule X) hσ _).symm

lemma basicOpen_ratio : X.basicOpen (ratio s hσ) = V ⊓ s.nonvanishingLocus := by
  have h := congrArg Sections.nonvanishingLocus (restrict_eq_ratio_smul s hσ)
  rw [Sections.nonvanishingLocus_restrict, Sections.nonvanishingLocus_smul, hσ] at h
  rw [h]
  exact (inf_eq_left.mpr ((X.basicOpen_le _))).symm

lemma isUnit_ratio (hU : U ≤ s.nonvanishingLocus) :
    IsUnit (X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op (ratio s hσ)) := by
  apply isUnit_of_basicOpen_eq
  rw [Scheme.basicOpen_res, basicOpen_ratio]
  apply le_antisymm inf_le_left
  exact le_inf le_rfl (le_inf inf_le_right (inf_le_left.trans hU))

/-- `s^k` on `W ∩ U`, a nowhere vanishing section of `𝓛^{Nk}`. -/
abbrev secU (U : X.Opens) (k : ℕ) (W : X.Opens) : L.Sections (N * k) (W ⊓ U) :=
  (s.npow k).restrict (le_top : W ⊓ U ≤ ⊤)

/-- `σ^k` on `W ∩ V`, a nowhere vanishing section of `𝓛^{Nk}`. -/
abbrev secV (σ : L.Sections N V) (k : ℕ) (W : X.Opens) : L.Sections (N * k) (W ⊓ V) :=
  (σ.npow k).restrict (inf_le_right : W ⊓ V ≤ V)

lemma nonvanishingLocus_secU (hU : U ≤ s.nonvanishingLocus) (k : ℕ) (W : X.Opens) :
    (secU s U k W).nonvanishingLocus = W ⊓ U := by
  rw [Sections.nonvanishingLocus_restrict]
  exact inf_eq_left.mpr (inf_le_right.trans (Sections.le_nonvanishingLocus_npow s hU k))

lemma nonvanishingLocus_secV (hσ : σ.nonvanishingLocus = V) (k : ℕ) (W : X.Opens) :
    (secV σ k W).nonvanishingLocus = W ⊓ V := by
  rw [Sections.nonvanishingLocus_restrict, Sections.nonvanishingLocus_npow_of_eq σ hσ k]
  exact inf_eq_left.mpr inf_le_right

variable (F : X.Modules)

/-- The pair of local coefficients `(t / s^k, t / σ^k)` of a section `t` of `F ⊗ 𝓛^{Nk}`. -/
def toPair (hσ : σ.nonvanishingLocus = V) (hU : U ≤ s.nonvanishingLocus) (k : ℕ) (W : X.Opens)
    (t : L.twistSubgroup F (N * k) W) : Γ(F, W ⊓ U) × Γ(F, W ⊓ V) :=
  ((mulSecEquiv F (nonvanishingLocus_secU s hU k W)).symm
      (L.twistRestrict F _ (inf_le_left : W ⊓ U ≤ W) t),
    (mulSecEquiv F (nonvanishingLocus_secV hσ k W)).symm
      (L.twistRestrict F _ (inf_le_left : W ⊓ V ≤ W) t))

variable (hU : U ≤ s.nonvanishingLocus) (k : ℕ)

lemma mulSec_toPair_fst (W : X.Opens) (t : L.twistSubgroup F (N * k) W) :
    mulSec F (secU s U k W) (toPair s F hσ hU k W t).1 = L.twistRestrict F _ inf_le_left t :=
  mulSec_mulSecEquiv_symm F _ _

lemma mulSec_toPair_snd (W : X.Opens) (t : L.twistSubgroup F (N * k) W) :
    mulSec F (secV σ k W) (toPair s F hσ hU k W t).2 = L.twistRestrict F _ inf_le_left t :=
  mulSec_mulSecEquiv_symm F _ _

lemma toPair_fst_eq_iff (W : X.Opens) (t : L.twistSubgroup F (N * k) W) (a : Γ(F, W ⊓ U)) :
    (toPair s F hσ hU k W t).1 = a ↔
      mulSec F (secU s U k W) a = L.twistRestrict F _ inf_le_left t :=
  (LinearEquiv.symm_apply_eq _).trans eq_comm

lemma toPair_snd_eq_iff (W : X.Opens) (t : L.twistSubgroup F (N * k) W) (b : Γ(F, W ⊓ V)) :
    (toPair s F hσ hU k W t).2 = b ↔
      mulSec F (secV σ k W) b = L.twistRestrict F _ inf_le_left t :=
  (LinearEquiv.symm_apply_eq _).trans eq_comm

omit hU in
/-- On `W' ⊆ V`, `s^k = (s/σ)^k σ^k`. -/
lemma npow_restrict_eq {W' : X.Opens} (h : W' ≤ V) :
    (s.npow k).restrict (le_top : W' ≤ ⊤) =
      X.presheaf.map (homOfLE h).op (ratio s hσ ^ k) • (σ.npow k).restrict h := by
  rw [← Sections.restrict_restrict (le_top : V ≤ ⊤) h, Sections.npow_restrict,
    restrict_eq_ratio_smul s hσ, Sections.smul_npow, Sections.restrict_smul]


lemma coe_unit_zpow (hU : U ≤ s.nonvanishingLocus) :
    ((((isUnit_ratio s hσ hU).unit ^ (k : ℤ) : Γ(X, U ⊓ V)ˣ)) : Γ(X, U ⊓ V)) =
      X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op (ratio s hσ ^ k) := by
  rw [zpow_natCast, Units.val_pow_eq_pow_val, IsUnit.unit_spec, map_pow]

/-- **The local coefficients satisfy the gluing condition of the divisor twist**: on
`W ∩ U ∩ V`, `t / σ^k = (s / σ)^k · (t / s^k)`. -/
lemma toPair_twistCond (W : X.Opens) (t : L.twistSubgroup F (N * k) W) :
    TwistCond F U V ((isUnit_ratio s hσ hU).unit ^ (k : ℤ)) W (toPair s F hσ hU k W t).1
      (toPair s F hσ hU k W t).2 := by
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
      ((((isUnit_ratio s hσ hU).unit ^ (k : ℤ) : Γ(X, U ⊓ V)ˣ)) : Γ(X, U ⊓ V)) • σ₃ =
      (secU s U k W).restrict (twist_le₁ U V W) := by
    rw [coe_unit_zpow (hU := hU), ringMap_ringMap _ _ h₃, Sections.restrict_restrict]
    exact (npow_restrict_eq s hσ k h₃).symm
  rw [← mulSec_smul_sec, e₁, e₂, ← mulSec_restrict, ← mulSec_restrict,
    mulSec_toPair_fst, mulSec_toPair_snd, twistRestrict_twistRestrict,
    twistRestrict_twistRestrict]

lemma toPair_restrict {W W' : X.Opens} (h : W' ≤ W) (t : L.twistSubgroup F (N * k) W) :
    toPair s F hσ hU k W' (L.twistRestrict F _ h t) =
      (F.presheaf.map (homOfLE (inf_le_inf_right U h)).op (toPair s F hσ hU k W t).1,
        F.presheaf.map (homOfLE (inf_le_inf_right V h)).op (toPair s F hσ hU k W t).2) := by
  apply Prod.ext
  · rw [toPair_fst_eq_iff]
    have e : secU s U k W' = (secU s U k W).restrict (inf_le_inf_right U h) := by
      rw [Sections.restrict_restrict]
    rw [e, ← mulSec_restrict, mulSec_toPair_fst, twistRestrict_twistRestrict,
      twistRestrict_twistRestrict]
  · rw [toPair_snd_eq_iff]
    have e : secV σ k W' = (secV σ k W).restrict (inf_le_inf_right V h) := by
      rw [Sections.restrict_restrict]
    rw [e, ← mulSec_restrict, mulSec_toPair_snd, twistRestrict_twistRestrict,
      twistRestrict_twistRestrict]

lemma toPair_add (W : X.Opens) (t t' : L.twistSubgroup F (N * k) W) :
    toPair s F hσ hU k W (t + t') = toPair s F hσ hU k W t + toPair s F hσ hU k W t' := by
  simp only [toPair, map_add, Prod.mk_add_mk]

lemma toPair_smul (W : X.Opens) (r : Γ(X, W)) (t : L.twistSubgroup F (N * k) W) :
    toPair s F hσ hU k W (r • t) =
      (resU U W r • (toPair s F hσ hU k W t).1, resV V W r • (toPair s F hσ hU k W t).2) := by
  apply Prod.ext
  · rw [toPair_fst_eq_iff, mulSec_smul, mulSec_toPair_fst,
      Projectivity.LineBundleData.twistRestrict_smul]
  · rw [toPair_snd_eq_iff, mulSec_smul, mulSec_toPair_snd,
      Projectivity.LineBundleData.twistRestrict_smul]

/-- The twist as a sheaf of abelian groups. -/
abbrev twistSheafAb (M : X.Modules) : TopCat.Sheaf Ab.{u} X := ⟨M.presheaf, M.isSheaf⟩

lemma le_sup_inf (hUV : U ⊔ V = ⊤) (W : X.Opens) : W ≤ W ⊓ U ⊔ W ⊓ V := by
  rw [← inf_sup_left, hUV, inf_top_eq]

lemma toPair_injective (hUV : U ⊔ V = ⊤) (W : X.Opens) :
    Function.Injective (toPair s F hσ hU k W) := by
  intro t t' h
  have h₁ : L.twistRestrict F _ (inf_le_left : W ⊓ U ≤ W) t =
      L.twistRestrict F _ (inf_le_left : W ⊓ U ≤ W) t' := by
    rw [← mulSec_toPair_fst s hσ F hU k W t, ← mulSec_toPair_fst s hσ F hU k W t',
      congrArg Prod.fst h]
  have h₂ : L.twistRestrict F _ (inf_le_left : W ⊓ V ≤ W) t =
      L.twistRestrict F _ (inf_le_left : W ⊓ V ≤ W) t' := by
    rw [← mulSec_toPair_snd s hσ F hU k W t, ← mulSec_toPair_snd s hσ F hU k W t',
      congrArg Prod.snd h]
  exact (twistSheafAb (L.twist F (N * k))).eq_of_locally_eq₂
    (homOfLE (inf_le_left : W ⊓ U ≤ W)) (homOfLE (inf_le_left : W ⊓ V ≤ W))
    (le_sup_inf hUV W) t t' h₁ h₂

lemma toPair_surjective (hUV : U ⊔ V = ⊤) (W : X.Opens) (p : Γ(F, W ⊓ U) × Γ(F, W ⊓ V))
    (hp : TwistCond F U V ((isUnit_ratio s hσ hU).unit ^ (k : ℤ)) W p.1 p.2) :
    ∃ t, toPair s F hσ hU k W t = p := by
  have h₄ : W ⊓ U ⊓ (W ⊓ V) ≤ W ⊓ (U ⊓ V) := fun x hx => ⟨hx.1.1, hx.1.2, hx.2.2⟩
  have h₅ : W ⊓ U ⊓ (W ⊓ V) ≤ V := h₄.trans ((twist_le₃ U V W).trans inf_le_right)
  set σ₄ : L.Sections (N * k) (W ⊓ U ⊓ (W ⊓ V)) := (σ.npow k).restrict h₅
  have hxy : L.twistRestrict F _ (inf_le_left : W ⊓ U ⊓ (W ⊓ V) ≤ W ⊓ U)
      (mulSec F (secU s U k W) p.1) =
      L.twistRestrict F _ (inf_le_right : W ⊓ U ⊓ (W ⊓ V) ≤ W ⊓ V)
      (mulSec F (secV σ k W) p.2) := by
    rw [mulSec_restrict, mulSec_restrict, Sections.restrict_restrict, Sections.restrict_restrict,
      npow_restrict_eq s hσ k h₅, mulSec_smul_sec]
    congr 1
    have e := congrArg (F.presheaf.map (homOfLE h₄).op) hp
    rw [presheaf_map_map, Scheme.Modules.map_smul, presheaf_map_map, coe_unit_zpow (hU := hU),
      ringMap_ringMap _ _ (h₄.trans (twist_le₃ U V W)), ringMap_ringMap _ _ h₅] at e
    exact e.symm
  obtain ⟨t, ht₁, ht₂⟩ := exists_glue₂ (twistSheafAb (L.twist F (N * k)))
    (inf_le_left : W ⊓ U ≤ W) (inf_le_left : W ⊓ V ≤ W) (le_sup_inf hUV W)
    (mulSec F (secU s U k W) p.1) (mulSec F (secV σ k W) p.2) hxy
  exact ⟨t, Prod.ext ((toPair_fst_eq_iff s hσ F hU k W t p.1).mpr ht₁.symm)
    ((toPair_snd_eq_iff s hσ F hU k W t p.2).mpr ht₂.symm)⟩

/-- **The two-chart comparison** `F ⊗ 𝓛^{Nk} ⟶ F(kD)`, `t ↦ (t / s^k, t / σ^k)`, where `F(kD)`
is the divisor twist of `F` along `(U, V)` by `(s/σ)^k`. -/
def twoChartHom : L.twist F (N * k) ⟶ divisorTwist F U V (isUnit_ratio s hσ hU) k where
  val := PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom
        { toFun := fun t => (⟨toPair s F hσ hU k W.unop t, toPair_twistCond s hσ F hU k W.unop t⟩ :
            twistSubgroup F U V ((isUnit_ratio s hσ hU).unit ^ (k : ℤ)) W.unop)
          map_zero' := Subtype.ext (by
            have h := toPair_add s hσ F hU k W.unop 0 0
            rw [add_zero] at h
            exact (add_eq_left.mp h.symm))
          map_add' := fun t t' => Subtype.ext (toPair_add s hσ F hU k W.unop t t') }
      naturality := fun {W W'} i => by
        ext t
        apply Subtype.ext
        exact toPair_restrict s hσ F hU k (leOfHom i.unop) t }
    (fun W r t => Subtype.ext (toPair_smul s hσ F hU k W.unop r t))

lemma twoChartHom_app (W : X.Opens) (t : L.twistSubgroup F (N * k) W) :
    (show twistSubgroup F U V ((isUnit_ratio s hσ hU).unit ^ (k : ℤ)) W from
      (twoChartHom s hσ F hU k).app W t).1 = toPair s F hσ hU k W t :=
  rfl

theorem isIso_twoChartHom (hUV : U ⊔ V = ⊤) : IsIso (twoChartHom s hσ F hU k) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro W
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun t t' h => toPair_injective s hσ F hU k hUV W (congrArg Subtype.val h), fun p => ?_⟩
  obtain ⟨t, ht⟩ := toPair_surjective s hσ F hU k hUV W p.1 p.2
  exact ⟨t, Subtype.ext ht⟩

/-- **`F ⊗ 𝓛^{Nk} ≅ F(kD)`** for line-bundle data trivialized by `s` on `U` and by `σ` on `V`,
with `D` cut out by `s/σ` on `V`. -/
def twoChartIso (hUV : U ⊔ V = ⊤) :
    L.twist F (N * k) ≅ divisorTwist F U V (isUnit_ratio s hσ hU) k :=
  haveI := isIso_twoChartHom s hσ F hU k hUV
  asIso (twoChartHom s hσ F hU k)

end TwoChart

end LineBundleData

end

end DeJongAlterations.StableModification.CurvesField.Ample
