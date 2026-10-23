/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.StableModificationBridge.StableMarkedNativeCokernel
import DeJongAlterations.StableModificationBridge.StableMarkedSimpleQuotient
import DeJongAlterations.Algebra.NodeFittingIdealSheafAffinePullback

/-! Actual one-dimensional local marking cokernels from SAME original whole ideal,
actual native etale pullback, and literal finite support. Blueprint:
`stable-marked-local-cokernel.tex`. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace DeJongAlterations.StableModificationBridge.StableMarkedLocalCokernel
open StableModification StableModification.Projectivity Cohomology Omega.RosenlichtComponent
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

/-- The actual original pulled marking map has a one-dimensional native cokernel
locally at EACH actual mark. All original coefficient actions and whole ideals are retained. -/
theorem exists_local_cokernel {X Y : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]
    (q : Y ⟶ Spec (.of K)) (E : LocalEquations X) (D : X.IdealSheafData)
    (hE : ∀ i, ∃ h : IsAffineOpen (E.U i),
      D.ideal ⟨E.U i, h⟩ = Ideal.span {E.f i})
    (M : X.Modules) (hM : Omega.IsInvertibleModule M) (ν : Y ⟶ X)
    [Etale ((D.comap ν).subschemeι ≫ q)]
    (T : Finset Y) (hT : ∀ y, y ∈ T ↔ ν y ∈ (D.support : Set X))
    (hTc : ∀ y ∈ T, IsClosed ({y} : Set Y)) :
    ∀ y ∈ T, ∃ V : Y.Opens, IsAffineOpen V ∧ y ∈ V ∧
      (∀ z ∈ T, z ∈ V → z = y) ∧
      FiniteDimensional K (sectionsCoker (structureCoeff q)
        (StableMarkedNativePullback.pullbackMarkedTwistMap E M ν) V) ∧
      Module.finrank K (sectionsCoker (structureCoeff q)
        (StableMarkedNativePullback.pullbackMarkedTwistMap E M ν) V) = 1 := by
  classical
  let : M.IsQuasicoherent := isQuasicoherent_of_isInvertibleModule M hM
  intro y hy
  let O : Y.Opens := ⟨((T.erase y : Finset Y) : Set Y)ᶜ,
    (isClosed_finset (T.erase y) (fun z hz => hTc z (Finset.mem_of_mem_erase hz))).isOpen_compl⟩
  have hyO : y ∈ O := by simp [O]
  obtain ⟨U, σ, hxU, hσ⟩ := exists_isFreeGenerator hM (ν y)
  obtain ⟨i, hi⟩ := E.toLineBundleData.exists_mem_U (ν y)
  obtain ⟨hEi, hEiD⟩ := hE i
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset
    (x := ν y) (U := U ⊓ E.U i) ⟨hxU, hi⟩
  let hWi : W ≤ E.U i := hWU.trans inf_le_right
  let σW := M.presheaf.map (homOfLE (hWU.trans inf_le_left)).op σ
  have hσW : IsFreeGenerator M σW := hσ.restrict (hWU.trans inf_le_left)
  have hσW' : Function.Bijective (fun r : Γ(X, W) => r • σW) := by
    simpa using hσW W le_rfl
  obtain ⟨V, hV, hyV, hVO⟩ := exists_isAffineOpen_mem_and_subset
    (x := y) (U := O ⊓ ν ⁻¹ᵁ W) ⟨hyO, hxW⟩
  let hVW : V ≤ ν ⁻¹ᵁ W := hVO.trans inf_le_right
  have hVsingle : ∀ z ∈ T, z ∈ V → z = y := by
    intro z hz hzV
    by_contra hzy
    exact (hVO hzV).1 (Finset.mem_erase.mpr ⟨hzy, hz⟩)
  let I := D.comap ν
  have hyI : y ∈ I.support := by
    rw [Scheme.IdealSheafData.support_comap]
    exact (hT y).mp hy
  have hisol : ∀ z : Y, z ∈ I.support → z ∈ V → z = y := by
    intro z hz hzV
    apply hVsingle z ((hT z).mpr ?_) hzV
    change z ∈ (D.comap ν).support at hz
    rwa [Scheme.IdealSheafData.support_comap] at hz
  have hDW : D.ideal ⟨W, hW⟩ = Ideal.span {res hWi (E.f i)} := by
    rw [← D.map_ideal (show (⟨W, hW⟩ : X.affineOpens) ≤ ⟨E.U i, hEi⟩ from hWi),
      hEiD, Ideal.map_span, Set.image_singleton]
    rfl
  have hIV : I.ideal ⟨V, hV⟩ =
      Ideal.span {ν.appLE W V hVW (res hWi (E.f i))} := by
    rw [Algebra.NodeFittingIdealSheaf.ideal_comap_of_le D ν ⟨W, hW⟩ ⟨V, hV⟩ hVW,
      hDW, Ideal.map_span, Set.image_singleton]
  let : Algebra K Γ(Y, V) :=
    (sectionsRingHom (structureCoeff q) (le_top : V ≤ ⊤)).toAlgebra
  have hQ := StableMarkedSimpleQuotient.quotient_finiteDimensional_finrank_one q I hV
    y hyV hyI hisol
  rw [hIV] at hQ
  let e := StableMarkedNativeCokernel.pullbackMarkedCokerEquivQuotient (structureCoeff q)
    E M ν hW hWi hV hVW σW hσW'
  let : FiniteDimensional K (Γ(Y, V) ⧸ Ideal.span {ν.appLE W V hVW (res hWi (E.f i))}) := hQ.1
  exact ⟨V, hV, hyV, hVsingle, Module.Finite.equiv e.symm,
    by rw [e.finrank_eq, hQ.2]⟩

end DeJongAlterations.StableModificationBridge.StableMarkedLocalCokernel
