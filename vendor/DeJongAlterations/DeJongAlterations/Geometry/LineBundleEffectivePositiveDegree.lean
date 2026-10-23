/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.Geometry.LineBundleCurveRiemannRoch
import DeJongAlterations.StableModification.CurvesField.AmplePositiveNormalization

/-! # A genuine original nontrivial effective section has positive Euler degree -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

namespace DeJongAlterations.Geometry.CurveLineBundle

universe u

open StableModification StableModification.Projectivity StableModification.Cohomology
open CurvesField CurvesField.Positive CurvesField.Ample
open CurvesField.Ample.LineBundleData Projectivity.LineBundleData

set_option backward.isDefEq.respectTransparency false

/-- A nonunit original coefficient gives a genuinely nonzero multiplication quotient. -/
theorem nontrivial_quotient_fMul_of_not_isUnit {K : Type u} [Field K]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (V : X.Opens) (b : Γ(X, V))
    (hb : ¬ IsUnit b) : Nontrivial
      (sectionsModuleCat (unitModule X) (structureCoeff p) V le_top ⧸
        LinearMap.range (fMul (unitModule X) V (structureCoeff p) b)) := by
  let M := sectionsModuleCat (unitModule X) (structureCoeff p) V le_top
  let Q := M ⧸ LinearMap.range (fMul (unitModule X) V (structureCoeff p) b)
  let one : M := (1 : Γ(X, V))
  have hne : (Submodule.Quotient.mk one : Q) ≠ 0 := by
    intro h
    obtain ⟨r, hr⟩ := (Submodule.Quotient.mk_eq_zero _).mp h
    apply hb
    exact isUnit_iff_dvd_one.mpr ⟨(show Γ(X, V) from r), hr.symm⟩
  exact ⟨⟨_, _, hne⟩⟩

/-- An actual original global section, nonzero generically and with an actual zero,
has strictly positive original Euler degree; no local cokernel certificate is input. -/
theorem degree_pos_of_effective_section {K : Type u} [Field K] [Infinite K]
    {X : Scheme.{u}} [IsIntegral X] {p : X ⟶ Spec (.of K)}
    (hp : IsProjectiveOver p) (hdim : topologicalKrullDim X ≤ 1)
    [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    (L : LineBundleData X) (s : L.Sections 1 ⊤)
    (hs : genericPoint X ∈ s.nonvanishingLocus) (hz : ∃ z : X, z ∉ s.nonvanishingLocus) :
    0 < Positive.degree L (structureCoeff p) := by
  classical
  let : IsProper p := hp.isProper
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : IsNoetherian X := {}
  let U := s.nonvanishingLocus
  have hgen : ∀ x : X, ¬ IsClosed ({x} : Set X) → x ∈ U := by
    intro x hx
    rw [eq_genericPoint_of_not_isClosed hdim hx]
    exact hs
  have hzero : ∀ x : X, ¬ IsClosed ({x} : Set X) → ∃ z, x ⤳ z ∧ z ∉ U := by
    intro x hx
    obtain ⟨z, hz⟩ := hz
    refine ⟨z, ?_, hz⟩
    rw [eq_genericPoint_of_not_isClosed hdim hx]
    exact (genericPoint_spec X).specializes (Set.mem_univ z)
  have hU : IsAffineOpen U := isAffineOpen_nonvanishingLocus_of_section hp hdim s hgen hzero
  let Z : Set X := (U : Set X)ᶜ
  have hZcl : ∀ z ∈ Z, IsClosed ({z} : Set X) := by
    intro z hz
    by_contra hc
    exact hz (hgen z hc)
  have hZ : Z.Finite := finite_of_forall_isClosed_singleton U.isOpen.isClosed_compl hZcl
  obtain ⟨W, hW, hZW⟩ := exists_isAffineOpen_mem_of_isProjectiveOver hp hZ.toFinset
  obtain ⟨σ₁, hσ₁⟩ := exists_section_nonvanishing L 1 hW hZ
    (fun z hz => hZW z (hZ.mem_toFinset.mpr hz)) hZcl
  let V := σ₁.nonvanishingLocus
  have hV : IsAffineOpen V := isAffineOpen_nonvanishingLocus_of_isAffineOpen hW σ₁
  have hZV : Z ⊆ V := hσ₁
  have hVW : V ≤ W := Sections.nonvanishingLocus_le σ₁
  let σ := σ₁.restrict hVW
  have hσ : σ.nonvanishingLocus = V := by
    rw [Sections.nonvanishingLocus_restrict]
    exact inf_idem V
  let τ := s.restrict (le_top : U ≤ ⊤)
  have hτ : τ.nonvanishingLocus = U := by
    rw [Sections.nonvanishingLocus_restrict]
    exact inf_idem U
  have hsup : U ⊔ V = ⊤ := by
    apply top_unique
    intro x _
    by_cases hx : x ∈ U
    · exact Opens.mem_sup.mpr (Or.inl hx)
    · exact Opens.mem_sup.mpr (Or.inr (hZV hx))
  let b := ratio s hσ
  have hbOpen : X.basicOpen b = U ⊓ V := by
    rw [basicOpen_ratio]
    exact inf_comm V U
  let P : Presentation L := ⟨U, V, hU, hV, hsup, b, hbOpen, τ, hτ, σ, hσ⟩
  have hbtrans : P.resV b = (P.g : Γ(X, U ⊓ V)) := by
    change _ = (transUnit hσ hτ : Γ(X, U ⊓ V))
    rw [coe_transUnit]
    symm
    apply transFun_eq_of_eq_smul
    have h := congrArg (fun t : L.Sections 1 V => t.restrict (inf_le_right : U ⊓ V ≤ V))
      (restrict_eq_ratio_smul s hσ)
    simpa only [τ, Presentation.resV, Sections.restrict_restrict, Sections.restrict_smul] using h
  have hηV : genericPoint X ∈ V := by
    obtain ⟨z, hz⟩ := hz
    exact ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr ⟨z, trivial, hZV hz⟩
  have hUV : ((U ⊓ V : X.Opens) : Set X).Nonempty := ⟨genericPoint X, hs, hηV⟩
  have : Nonempty V := ⟨⟨genericPoint X, hηV⟩⟩
  have hb0 : b ≠ 0 := ne_zero_of_isUnit_res inf_le_right hUV P.isUnit_resV_f
  have hbnu : ¬ IsUnit b := by
    intro hu
    obtain ⟨z, hz⟩ := hz
    have hzb : z ∈ X.basicOpen b := by
      rw [X.basicOpen_of_isUnit hu]
      exact hZV hz
    exact hz (hbOpen ▸ hzb).1
  let c := structureCoeff p
  have : FiniteDimensional K (cohomology (unitModule X) c 0) :=
    finite_cohomology_of_isProjectiveOver hp (unitModule X) (fun W _ => Module.Finite.self _) 0
  have : FiniteDimensional K (cohomology (unitModule X) c 1) :=
    finite_cohomology_of_isProjectiveOver hp (unitModule X) (fun W _ => Module.Finite.self _) 1
  have := finiteDimensional_quotient_fMul (p := p) hdim hV hb0
  have := nontrivial_quotient_fMul_of_not_isUnit p V b hbnu
  have hpos : 0 < Module.finrank K
      (sectionsModuleCat (unitModule X) c V le_top ⧸
        LinearMap.range (fMul (unitModule X) V c b)) := Module.finrank_pos
  have he := P.eulerCharOf_twist c (j := 0) (a := b)
    (by simpa only [pow_zero, mul_one] using hbtrans)
    (injective_fMul_of_ne_zero hb0) (injective_fMul_of_ne_zero hb0) 1
  simp only [Nat.cast_zero, Nat.cast_one, zero_mul, sub_zero, one_mul] at he
  change DualityScheme.eulerCharOf (L.twist (unitModule X) 1) c =
    DualityScheme.eulerCharOf (unitModule X) c +
      (Module.finrank K (sectionsModuleCat (unitModule X) c V le_top ⧸
        LinearMap.range (fMul (unitModule X) V c b)) : ℤ) at he
  change 0 < DualityScheme.eulerCharOf (L.twist (unitModule X) 1) c -
    DualityScheme.eulerCharOf (unitModule X) c
  omega

end DeJongAlterations.Geometry.CurveLineBundle
