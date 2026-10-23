/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.StableModificationBridge.StableMarkedCartier
import DeJongAlterations.StableModification.Projectivity.LineBundleOps
import Mathlib.RingTheory.Flat.TorsionFree

/-! The original Cartier ideal constructs its actual line bundle and canonical
section, with every original affine ideal retained. Blueprint:
`stable-marked-cartier-line-bundle.tex`. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.StableModificationBridge.StableMarkedCartierLineBundle

open StableModification StableModification.Projectivity

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

private theorem regular_res {X : Scheme.{u}} {U V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V ≤ U)
    {t : Γ(X, U)} (ht : IsRegular t) : IsRegular (res h t) := by
  let : Algebra Γ(X, U) Γ(X, V) := (res h).toAlgebra
  have : Module.Flat Γ(X, U) Γ(X, V) := by
    change (res h).Flat
    simpa only [res, Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp] using
      Scheme.Hom.flat_appLE (𝟙 X) hU hV h
  have hl : IsLeftRegular (res h t) := by
    change Function.Injective (fun x : Γ(X, V) => res h t * x)
    simpa only [IsSMulRegular, Algebra.smul_def, RingHom.algebraMap_toAlgebra] using
      (Module.Flat.isSMulRegular_of_isRegular (M := Γ(X, V)) ht)
  exact ⟨hl, hl.right_of_commute fun _ => Commute.all _ _⟩

private theorem exists_unit_ratio {R : Type*} [CommRing R] {a b : R}
    (hb : IsRegular b) (h : Ideal.span {a} = Ideal.span {b}) :
    ∃ v : Rˣ, a = (v : R) * b := by
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp (h ▸ Ideal.mem_span_singleton_self a)
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp (h.symm ▸ Ideal.mem_span_singleton_self b)
  have hsr : s * r = 1 := hb.right (by
    change (s * r) * b = 1 * b
    rw [mul_assoc, hr, hs, one_mul])
  exact ⟨⟨r, s, by simpa only [mul_comm] using hsr, hsr⟩, hr.symm⟩

/-- The whole ORIGINAL effective Cartier ideal supplies its actual cocycle, original
regular affine equations, and canonical section with EXACT original support. -/
theorem exists_localEquations {X : Scheme.{u}}
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (D : X.IdealSheafData) (hD : IsEffectiveCartierDivisor D) :
    ∃ E : LocalEquations X,
      (∀ i, ∃ h : IsAffineOpen (E.U i), IsRegular (E.f i) ∧
        D.ideal ⟨E.U i, h⟩ = Ideal.span {E.f i}) ∧
      ∀ x : X, x ∈ E.canonicalSection.nonvanishingLocus ↔ x ∉ (D.support : Set X) := by
  classical
  choose U hx t hreg hideal using hD
  have hcover : ⨆ x, (U x).1 = ⊤ := by
    apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  have hunit : ∀ i j : X, ∃ v : Γ(X, (U i).1 ⊓ (U j).1)ˣ,
      res (inf_le_left : (U i).1 ⊓ (U j).1 ≤ (U i).1) (t i) =
        (v : Γ(X, (U i).1 ⊓ (U j).1)) *
          res (inf_le_right : (U i).1 ⊓ (U j).1 ≤ (U j).1) (t j) := by
    intro i j
    let V : X.affineOpens := ⟨(U i).1 ⊓ (U j).1, (U i).2.inf (U j).2⟩
    have hVi : V ≤ U i := by change (U i).1 ⊓ (U j).1 ≤ (U i).1; exact inf_le_left
    have hVj : V ≤ U j := by change (U i).1 ⊓ (U j).1 ≤ (U j).1; exact inf_le_right
    have hi : D.ideal V = Ideal.span {res (inf_le_left : V.1 ≤ (U i).1) (t i)} := by
      rw [← D.map_ideal hVi, hideal,
        Ideal.map_span, Set.image_singleton]
      rfl
    have hj : D.ideal V = Ideal.span {res (inf_le_right : V.1 ≤ (U j).1) (t j)} := by
      rw [← D.map_ideal hVj, hideal,
        Ideal.map_span, Set.image_singleton]
      rfl
    exact exists_unit_ratio (regular_res (U j).2 V.2 inf_le_right (hreg j))
      (hi.symm.trans hj)
  have hnzd : ∀ i j k : X,
      res (inf_le_right : (U i).1 ⊓ (U j).1 ⊓ (U k).1 ≤ (U k).1) (t k) ∈
        nonZeroDivisors Γ(X, (U i).1 ⊓ (U j).1 ⊓ (U k).1) := by
    intro i j k
    exact (regular_res (U k).2 (((U i).2.inf (U j).2).inf (U k).2)
      inf_le_right (hreg k)).mem_nonZeroDivisors
  let E := LocalEquations.ofNonZeroDivisors (fun x => (U x).1) hcover t hunit hnzd
  refine ⟨E, (fun i => ⟨(U i).2, hreg i, hideal i⟩), ?_⟩
  intro x
  have hmem : x ∈ E.canonicalSection.nonvanishingLocus ↔ x ∈ X.basicOpen (t x) := by
    have he := E.nonvanishingLocus_canonicalSection_inf x
    constructor
    · intro h
      have : x ∈ E.canonicalSection.nonvanishingLocus ⊓ E.U x := ⟨h, hx x⟩
      rwa [he] at this
    · intro h
      have : x ∈ E.canonicalSection.nonvanishingLocus ⊓ E.U x := by rw [he]; exact h
      exact this.1
  have hsupp : x ∈ (D.support : Set X) ↔ x ∉ X.basicOpen (t x) := by
    change x ∈ D.support ↔ _
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := U x) (hx x), hideal,
      X.zeroLocus_span, X.zeroLocus_singleton]
    rfl
  exact hmem.trans (by rw [hsupp, not_not])

/-- The ACTUAL original semistable marking supplies its own regular equations and
canonical line-bundle section internally; no replacement Cartier divisor is supplied. -/
theorem exists_localEquations_of_isSemistablePair {X S : Scheme.{u}} (f : X ⟶ S)
    [DeJong.IsNodalCurve f] [IsIntegral S] [IsLocallyNoetherian S]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (hS : IsNormalScheme S)
    (hgen : ∀ x : X, f x = genericPoint S → DeJong.IsSmoothAt f x)
    (D : X.IdealSheafData) (hD : DeJong.IsSemistablePair f D) :
    ∃ E : LocalEquations X,
      (∀ i, ∃ h : IsAffineOpen (E.U i), IsRegular (E.f i) ∧
        D.ideal ⟨E.U i, h⟩ = Ideal.span {E.f i}) ∧
      ∀ x : X, x ∈ E.canonicalSection.nonvanishingLocus ↔ x ∉ (D.support : Set X) :=
  exists_localEquations D
    (StableMarkedCartier.isEffectiveCartierDivisor_of_isSemistablePair f hS hgen D hD)

end DeJongAlterations.StableModificationBridge.StableMarkedCartierLineBundle
