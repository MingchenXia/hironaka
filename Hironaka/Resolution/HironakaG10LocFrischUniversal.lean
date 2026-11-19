import Hironaka.Resolution.HironakaG10LocFrischLocus

/-! # Frisch's locus is the largest parameter set along which the kernel extends (reduced universality)

Frisch 1968, Lemme 2 (ii) and the mechanism of Lemme 3 (ii), for the REDUCED locus: if along a
parameter set `R ∋ s₀` the kernel of `B(K, f(s₀))` extends continuously — a family `G(r)` of
matrices, continuous at `s₀`, with `G(s₀) = g₀` (generating `ker B(K,f(s₀))`, `(g₀, f(s₀))` direct
exact) and `f(r) G(r) = 0` for `r ∈ R` — then `R` lies in Frisch's locus `T` near `s₀`
(**`eventually_mem_frischLocus`**). With `HironakaG10LocFrischLocus.kerFamily_spec` (the kernel
extends holomorphically along `T` itself) this characterizes `T` near `s₀` as the largest such set,
and `relFibreFlatAt_frischLocus` gives flatness over it.

* `P_g_rinv`: `P g R(g) = P` for the right inverse `R(g) = R₀ P A(g)⁻¹ P` where `A(g)` is invertible.
Not formalized: that flatness of `coker f` over `R` near `{s₀} × K` produces such a family (Douady §8
Prop. 5 + Scholie with Theorem A over `R × K`), nor the non-reduced statement.
BP: hironaka-g10-loc-frisch-universal.tex. -/
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace Hironaka.HironakaG10LocFrischUniversal
noncomputable section
open HironakaG10FlatPolydiscAlgebra HironakaG10FlatResolutionStart HironakaG10LocDirectPersistence
  HironakaG10LocProductExact HironakaG10LocFrischLocus

section Abstract
variable {E₂ E₁ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] [NormedAddCommGroup E₁]
  [NormedSpace ℂ E₁]

/-- **`P g R(g) = P`** wherever `A(g)` is invertible. -/
theorem P_g_rinv {g₀ : E₂ →L[ℂ] E₁} {R₀ : E₁ →L[ℂ] E₂} (hR₀ : ∀ e, g₀ (R₀ (g₀ e)) = g₀ e)
    {g : E₂ →L[ℂ] E₁} (hA : (opA (g₀.comp R₀) R₀ g).IsInvertible) (x : E₁) :
    g₀ (R₀ (g (rinv (g₀.comp R₀) R₀ g x))) = g₀ (R₀ x) := by
  set P : E₁ →L[ℂ] E₁ := g₀.comp R₀ with hPdef
  have hPP : ∀ x, P (P x) = P x := fun x => projP_idem hR₀ x
  set A := opA P R₀ g with hAdef
  have hAP : ∀ x, A (P x) = P (A x) := by
    intro x
    simp only [hAdef, opA_apply, map_add, map_sub, hPP, sub_self, add_zero]
  have hAiP : ∀ y, A.inverse (P y) = P (A.inverse y) := by
    intro y
    apply hA.injective
    rw [hA.self_apply_inverse, hAP, hA.self_apply_inverse]
  show P (g (rinv P R₀ g x)) = P x
  set z := A.inverse (P x) with hz
  have hzP : P z = z := by rw [hz, ← hAiP, hPP]
  have hAz : A z = P x := hA.self_apply_inverse _
  have hRx : rinv P R₀ g x = R₀ (P z) := by
    show R₀ (P (A.inverse (P x))) = R₀ (P z)
    rw [← hz]
  rw [hRx, ← hAz, hAdef, opA_apply, hzP, sub_self, add_zero]

end Abstract

section Matrix
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]

/-- **Reduced universality of Frisch's locus**: along any parameter set `Rs` on which the kernel
of `f(s₀)` extends continuously (`G(r)`, `G(s₀) = g₀`, `f(r) G(r) = 0` on `Rs`), the parameters near
`s₀` lie in Frisch's locus `T`. -/
theorem eventually_mem_frischLocus {Y : Type*} [TopologicalSpace Y] {a b c : ℕ} (Rs : Set Y)
    {Fm : Y → Fin a → Fin b → R} {G : Y → Fin b → Fin c → R} {s₀ : Y} {V : Set Y}
    (hV : V ∈ 𝓝 s₀) (hFc : ContinuousAt Fm s₀) (hGc : ContinuousAt G s₀)
    (h₀ : DirectExact (G s₀) (Fm s₀)) {R₀ : (Fin b → R) →L[ℂ] (Fin c → R)}
    (hR₀ : ∀ e, matrixOperator (G s₀) (R₀ (matrixOperator (G s₀) e)) = matrixOperator (G s₀) e)
    {S₀ : (Fin a → R) →L[ℂ] (Fin b → R)}
    (hS₀ : ∀ x, matrixOperator (Fm s₀) (S₀ (matrixOperator (Fm s₀) x)) = matrixOperator (Fm s₀) x)
    (hcomp : ∀ᶠ r in 𝓝 s₀, r ∈ Rs → ∀ i k, ∑ j, Fm r i j * G r j k = 0) :
    ∀ᶠ r in 𝓝 s₀, r ∈ Rs → r ∈ frischLocus ((matrixOperator (G s₀)).comp R₀)
      ((matrixOperator (Fm s₀)).comp S₀) S₀ (fun s => matrixOperator (Fm s)) V := by
  set P := (matrixOperator (G s₀)).comp R₀ with hP
  have hc₀ : ∀ e, matrixOperator (Fm s₀) (matrixOperator (G s₀) e) = 0 :=
    matrixOperator_comp_apply (G s₀) (Fm s₀) h₀.comp
  have hex : ∀ x, matrixOperator (Fm s₀) x = 0 → ∃ e, matrixOperator (G s₀) e = x := h₀.exact
  have hfc : ContinuousAt (fun s => matrixOperator (Fm s)) s₀ :=
    (matrixOperatorCLM (R := R) (p := Fin b) (q := Fin a)).continuous.continuousAt.comp hFc
  have hgc : ContinuousAt (fun s => matrixOperator (G s)) s₀ :=
    (matrixOperatorCLM (R := R) (p := Fin c) (q := Fin b)).continuous.continuousAt.comp hGc
  have hCc : ContinuousAt (fun s => opC P ((matrixOperator (Fm s₀)).comp S₀) S₀
      (matrixOperator (Fm s))) s₀ :=
    (hfc.clm_comp continuousAt_const).add continuousAt_const
  have hAc : ContinuousAt (fun s => opA P R₀ (matrixOperator (G s))) s₀ :=
    (continuousAt_const.clm_comp (hgc.clm_comp continuousAt_const)).add continuousAt_const
  have hCinv : ∀ᶠ s in 𝓝 s₀, (opC P ((matrixOperator (Fm s₀)).comp S₀) S₀
      (matrixOperator (Fm s))).IsInvertible :=
    hCc (show {L : (Fin a → R) →L[ℂ] (Fin a → R) | L.IsInvertible} ∈
      𝓝 (opC P ((matrixOperator (Fm s₀)).comp S₀) S₀ (matrixOperator (Fm s₀))) by
        rw [opC_self hc₀]; exact isInvertible_mem_nhds_id)
  have hAinv : ∀ᶠ s in 𝓝 s₀, (opA P R₀ (matrixOperator (G s))).IsInvertible :=
    hAc (show {L : (Fin b → R) →L[ℂ] (Fin b → R) | L.IsInvertible} ∈
      𝓝 (opA P R₀ (matrixOperator (G s₀))) by
        rw [hP, opA_self hR₀]; exact isInvertible_mem_nhds_id)
  filter_upwards [hV, hCinv, hAinv, hcomp] with r hrV hrC hrA hrc hrR
  refine ⟨hrV, hrC, (schurOp_eq_zero_iff hR₀ hS₀ hex hrC).2 fun x =>
    ⟨matrixOperator (G r) (rinv P R₀ (matrixOperator (G r)) x),
      matrixOperator_comp_apply (G r) (Fm r) (hrc hrR) _, P_g_rinv hR₀ hrA x⟩⟩

end Matrix

end
end Hironaka.HironakaG10LocFrischUniversal
