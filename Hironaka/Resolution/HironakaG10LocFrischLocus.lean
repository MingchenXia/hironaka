import Hironaka.Resolution.HironakaG10LocFrischFlat

/-! # Frisch's local flattening locus `T` (reduced part) and Lemme 3 (i) on it

Frisch 1968, §2, Lemmes 2–3: for a presentation `f` and a polydisc `K` privileged for the fibre at
`s₀`, the parameters `t` near `s₀` for which `B(K, f(t))` keeps a kernel complementary to a fixed
complement `N₁` of `ker B(K, f(s₀))` form the zero set `T` of a Banach-analytic "Schur" map, and
`𝓕(T)` is `T`-flat on `T × K̊`.

Abstract operator form (`E₁`, `E₀` normed spaces; `g₀ : E₂ → E₁`, `f₀ : E₁ → E₀` exact at `E₁` with
generalized inverses `R₀`, `S₀`; `P = g₀ R₀`, `Q = f₀ S₀`, `C(f) = f (1 − P) S₀ + (1 − Q)` = `opC`):
* `schurOp f = (1 − Q) C(f)⁻¹ f` and `kerSec f = 1 − (1 − P) S₀ C(f)⁻¹ f`;
* `f_kerSec`: if `C(f)` is invertible and `schurOp f = 0`, then `f ∘ kerSec f = 0`;
* `kerSec_of_mem_ker` (`kerSec f x = x` on `ker f`), `schurOp_self` (`schurOp f₀ = 0`);
* **`schurOp_eq_zero_iff`**: for `C(f)` invertible, `schurOp f = 0` iff `ker f` projects onto
  `ker f₀ = im P` (every `x` has `y ∈ ker f` with `P y = P x`) — Frisch's `T` is the set where the
  kernel keeps its size (the pointwise content of Lemme 2 (ii)).
* `frischLocus P Q S₀ f V`: the parameters `s ∈ V` with `C(f(s))` invertible and `schurOp (f s) = 0`.

On `B(K)`: **`relFibreFlatAt_frischLocus`** (Frisch Lemme 3 (i) on Frisch's `T`, sheaf level): for a
presentation `f` holomorphic on `V × U` and `(g₀, f(s₀)|_K)` direct exact over `B(K)`, for `s ∈ T` near
`s₀` the sheaf `coker f` is flat over `T` at every point of `{s} × K̊`; the kernel family is
`kerSec (f(s)|_K) g₀` (`kerFamily`), holomorphic in `s`.
Inputs: `hTh1` (Douady §7 Th. 1) and `hA` (Theorem A), explicit hypotheses.
BP: hironaka-g10-loc-frisch-locus.tex. -/
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace Hironaka.HironakaG10LocFrischLocus
noncomputable section
open OkaRelationSheaf HironakaG10FlatPolydiscAlgebra HironakaG10FlatResolutionStart
  HironakaG10FlatPrivilegedNbhd HironakaG10LocDirectPersistence HironakaG10LocSheafExact
  HironakaG10LocFibreOpen HironakaG10LocRelative HironakaG10LocJointHol HironakaG10LocProductExact
  HironakaG10LocFrischFlat

section Abstract
variable {E₂ E₁ E₀ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] [NormedAddCommGroup E₁]
  [NormedSpace ℂ E₁] [NormedAddCommGroup E₀] [NormedSpace ℂ E₀]

/-- Frisch's Schur operator `(1 − Q) C(f)⁻¹ f`. -/
def schurOp (P : E₁ →L[ℂ] E₁) (Q : E₀ →L[ℂ] E₀) (S₀ : E₀ →L[ℂ] E₁) (f : E₁ →L[ℂ] E₀) :
    E₁ →L[ℂ] E₀ :=
  (ContinuousLinearMap.id ℂ E₀ - Q).comp ((opC P Q S₀ f).inverse.comp f)

/-- The kernel section `1 − (1 − P) S₀ C(f)⁻¹ f`. -/
def kerSec (P : E₁ →L[ℂ] E₁) (Q : E₀ →L[ℂ] E₀) (S₀ : E₀ →L[ℂ] E₁) (f : E₁ →L[ℂ] E₀) :
    E₁ →L[ℂ] E₁ :=
  ContinuousLinearMap.id ℂ E₁ -
    (ContinuousLinearMap.id ℂ E₁ - P).comp (S₀.comp ((opC P Q S₀ f).inverse.comp f))

variable {g₀ : E₂ →L[ℂ] E₁} {f₀ : E₁ →L[ℂ] E₀} {R₀ : E₁ →L[ℂ] E₂} {S₀ : E₀ →L[ℂ] E₁}

/-- `f (1 − P) w = C(f) (f₀ w)` (uses exactness at `s₀`). -/
theorem f_one_sub_P (hR₀ : ∀ e, g₀ (R₀ (g₀ e)) = g₀ e) (hS₀ : ∀ x, f₀ (S₀ (f₀ x)) = f₀ x)
    (hex : ∀ x, f₀ x = 0 → ∃ e, g₀ e = x) (f : E₁ →L[ℂ] E₀) (w : E₁) :
    f (w - g₀ (R₀ w)) = opC (g₀.comp R₀) (f₀.comp S₀) S₀ f (f₀ w) := by
  have h1 := one_sub_P_S₀_f₀ hR₀ hS₀ hex w
  have h2 : opC (g₀.comp R₀) (f₀.comp S₀) S₀ f (f₀ w) =
      f (S₀ (f₀ w) - g₀ (R₀ (S₀ (f₀ w)))) + (f₀ w - f₀ (S₀ (f₀ w))) := rfl
  rw [h2, hS₀, sub_self, add_zero, h1]

/-- **On Frisch's `T` the kernel section maps into `ker f`.** -/
theorem f_kerSec (hR₀ : ∀ e, g₀ (R₀ (g₀ e)) = g₀ e) (hS₀ : ∀ x, f₀ (S₀ (f₀ x)) = f₀ x)
    (hex : ∀ x, f₀ x = 0 → ∃ e, g₀ e = x) {f : E₁ →L[ℂ] E₀}
    (hC : (opC (g₀.comp R₀) (f₀.comp S₀) S₀ f).IsInvertible)
    (hT : schurOp (g₀.comp R₀) (f₀.comp S₀) S₀ f = 0) (x : E₁) :
    f (kerSec (g₀.comp R₀) (f₀.comp S₀) S₀ f x) = 0 := by
  set C := opC (g₀.comp R₀) (f₀.comp S₀) S₀ f with hCdef
  set y := C.inverse (f x) with hy
  have hQy : f₀ (S₀ y) = y := by
    have h := congrArg (fun L : E₁ →L[ℂ] E₀ => L x) hT
    simp only [schurOp, ContinuousLinearMap.comp_apply, sub_apply,
      ContinuousLinearMap.id_apply, zero_apply] at h
    rw [← hCdef, ← hy] at h
    exact (sub_eq_zero.mp h).symm
  have hk : kerSec (g₀.comp R₀) (f₀.comp S₀) S₀ f x = x - (S₀ y - g₀ (R₀ (S₀ y))) := rfl
  rw [hk, map_sub, f_one_sub_P hR₀ hS₀ hex f (S₀ y), ← hCdef, hQy, hy, hC.self_apply_inverse,
    sub_self]

omit [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] in
/-- The kernel section fixes `ker f`. -/
theorem kerSec_of_mem_ker (P : E₁ →L[ℂ] E₁) (Q : E₀ →L[ℂ] E₀) (S₀ : E₀ →L[ℂ] E₁)
    {f : E₁ →L[ℂ] E₀} {x : E₁} (hx : f x = 0) : kerSec P Q S₀ f x = x := by
  have h : kerSec P Q S₀ f x = x - (S₀ ((opC P Q S₀ f).inverse (f x)) -
      P (S₀ ((opC P Q S₀ f).inverse (f x)))) := rfl
  rw [h, hx, map_zero, map_zero, map_zero, sub_zero, sub_zero]

/-- At `f₀` the Schur operator vanishes. -/
theorem schurOp_self (hS₀ : ∀ x, f₀ (S₀ (f₀ x)) = f₀ x) (hc₀ : ∀ e, f₀ (g₀ e) = 0) :
    schurOp (g₀.comp R₀) (f₀.comp S₀) S₀ f₀ = 0 := by
  ext x
  simp only [schurOp, opC_self (R₀ := R₀) hc₀, ContinuousLinearMap.inverse_id,
    ContinuousLinearMap.comp_apply, sub_apply, ContinuousLinearMap.id_apply,
    zero_apply]
  rw [hS₀, sub_self]

/-- **Frisch's `T` is where the kernel keeps its size** (pointwise Lemme 2 (ii)): for `C(f)`
invertible, `schurOp f = 0` iff `ker f` projects onto `im P = ker f₀`. -/
theorem schurOp_eq_zero_iff (hR₀ : ∀ e, g₀ (R₀ (g₀ e)) = g₀ e)
    (hS₀ : ∀ x, f₀ (S₀ (f₀ x)) = f₀ x) (hex : ∀ x, f₀ x = 0 → ∃ e, g₀ e = x) {f : E₁ →L[ℂ] E₀}
    (hC : (opC (g₀.comp R₀) (f₀.comp S₀) S₀ f).IsInvertible) :
    schurOp (g₀.comp R₀) (f₀.comp S₀) S₀ f = 0 ↔
      ∀ x, ∃ y, f y = 0 ∧ g₀ (R₀ y) = g₀ (R₀ x) := by
  set C := opC (g₀.comp R₀) (f₀.comp S₀) S₀ f with hCdef
  constructor
  · intro hT x
    refine ⟨kerSec (g₀.comp R₀) (f₀.comp S₀) S₀ f x, f_kerSec hR₀ hS₀ hex hC hT x, ?_⟩
    have hk : kerSec (g₀.comp R₀) (f₀.comp S₀) S₀ f x =
        x - (S₀ (C.inverse (f x)) - g₀ (R₀ (S₀ (C.inverse (f x))))) := rfl
    rw [hk, map_sub, map_sub, map_sub, map_sub, projP_idem hR₀, sub_self, sub_zero]
  · intro hk
    ext x
    simp only [schurOp, ContinuousLinearMap.comp_apply, sub_apply,
      ContinuousLinearMap.id_apply, zero_apply]
    rw [← hCdef]
    obtain ⟨y, hy, hPy⟩ := hk x
    -- `f x = C (f₀ (x − y))`
    have hfx : f x = C (f₀ (x - y)) := by
      rw [← f_one_sub_P hR₀ hS₀ hex f (x - y), map_sub R₀ x y, map_sub g₀ (R₀ x) (R₀ y), hPy,
        sub_self, sub_zero, map_sub f x y, hy, sub_zero]
    rw [hfx, hC.inverse_apply_self, hS₀, sub_self]

/-- **Frisch's local flattening locus** (reduced part): the parameters `s ∈ V` at which `C(f(s))`
is invertible and the Schur operator of `f(s)` vanishes. -/
def frischLocus {S : Type*} (P : E₁ →L[ℂ] E₁) (Q : E₀ →L[ℂ] E₀) (S₀ : E₀ →L[ℂ] E₁)
    (f : S → E₁ →L[ℂ] E₀) (V : Set S) : Set S :=
  {s | s ∈ V ∧ (opC P Q S₀ (f s)).IsInvertible ∧ schurOp P Q S₀ (f s) = 0}

end Abstract

/-! ## The kernel family over a normed algebra -/

section KernelFamily
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]

/-- The kernel family `σ(s) = kerSec (f(s)) g₀` (columns), for matrices over a normed algebra. -/
def kerFamily {Y : Type*} {a b c : ℕ} (Fm : Y → Fin a → Fin b → R) (g₀ : Fin b → Fin c → R)
    (R₀ : (Fin b → R) →L[ℂ] (Fin c → R)) (S₀ : (Fin a → R) →L[ℂ] (Fin b → R)) (s₀ s : Y) :
    Fin b → Fin c → R :=
  fun j k => kerSec ((matrixOperator g₀).comp R₀) ((matrixOperator (Fm s₀)).comp S₀) S₀
    (matrixOperator (Fm s)) (fun j' => g₀ j' k) j

/-- **The kernel family** (Frisch Lemme 2 (i)–3 (i), Banach part): matrices `f(s)` holomorphic
near `s₀`, `(g₀, f(s₀))` direct exact with generalized inverses `R₀`, `S₀`. Then `s₀` lies in
Frisch's locus `T`, the kernel family `σ` is holomorphic near `s₀`, `f(s) σ(s) = 0` for `s ∈ T`, and
`σ(s₀) = g₀`. -/
theorem kerFamily_spec {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] {a b c : ℕ}
    {Fm : Y → Fin a → Fin b → R} {s₀ : Y} {V : Set Y} (hs₀V : s₀ ∈ V)
    (hF : ∀ᶠ s in 𝓝 s₀, DifferentiableAt ℂ Fm s) {g₀ : Fin b → Fin c → R}
    (h₀ : DirectExact g₀ (Fm s₀)) {R₀ : (Fin b → R) →L[ℂ] (Fin c → R)}
    (hR₀ : ∀ e, matrixOperator g₀ (R₀ (matrixOperator g₀ e)) = matrixOperator g₀ e)
    {S₀ : (Fin a → R) →L[ℂ] (Fin b → R)}
    (hS₀ : ∀ x, matrixOperator (Fm s₀) (S₀ (matrixOperator (Fm s₀) x)) = matrixOperator (Fm s₀) x) :
    s₀ ∈ frischLocus ((matrixOperator g₀).comp R₀) ((matrixOperator (Fm s₀)).comp S₀) S₀
        (fun s => matrixOperator (Fm s)) V ∧
      (∀ᶠ s in 𝓝 s₀, DifferentiableAt ℂ (kerFamily Fm g₀ R₀ S₀ s₀) s) ∧
      (∀ s ∈ frischLocus ((matrixOperator g₀).comp R₀) ((matrixOperator (Fm s₀)).comp S₀) S₀
        (fun s => matrixOperator (Fm s)) V, ∀ i k,
          ∑ j, Fm s i j * kerFamily Fm g₀ R₀ S₀ s₀ s j k = 0) ∧
      kerFamily Fm g₀ R₀ S₀ s₀ s₀ = g₀ := by
  set P := (matrixOperator g₀).comp R₀ with hP
  have hc₀ : ∀ e, matrixOperator (Fm s₀) (matrixOperator g₀ e) = 0 :=
    matrixOperator_comp_apply g₀ (Fm s₀) h₀.comp
  have hex : ∀ x, matrixOperator (Fm s₀) x = 0 → ∃ e, matrixOperator g₀ e = x := h₀.exact
  have hC₀ : opC P ((matrixOperator (Fm s₀)).comp S₀) S₀ (matrixOperator (Fm s₀)) =
      ContinuousLinearMap.id ℂ _ := opC_self hc₀
  have hFo : ∀ s, DifferentiableAt ℂ Fm s →
      DifferentiableAt ℂ (fun t => matrixOperator (Fm t)) s := fun s hs =>
    differentiableAt_matrixOperator fun i j => differentiableAt_pi.1 (differentiableAt_pi.1 hs i) j
  refine ⟨⟨hs₀V, ?_, schurOp_self hS₀ hc₀⟩, ?_, ?_, ?_⟩
  · rw [hC₀]
    exact ⟨ContinuousLinearEquiv.refl ℂ _, rfl⟩
  · have hCc : ContinuousAt (fun s => opC P ((matrixOperator (Fm s₀)).comp S₀) S₀
        (matrixOperator (Fm s))) s₀ :=
      ((hFo s₀ hF.self_of_nhds).continuousAt.clm_comp continuousAt_const).add continuousAt_const
    have hCinv : ∀ᶠ s in 𝓝 s₀, (opC P ((matrixOperator (Fm s₀)).comp S₀) S₀
        (matrixOperator (Fm s))).IsInvertible :=
      hCc (show {L : (Fin a → R) →L[ℂ] (Fin a → R) | L.IsInvertible} ∈
        𝓝 (opC P ((matrixOperator (Fm s₀)).comp S₀) S₀ (matrixOperator (Fm s₀))) by
          rw [hC₀]; exact isInvertible_mem_nhds_id)
    filter_upwards [hCinv, hF] with s hsC hsF
    have hCd : DifferentiableAt ℂ (fun t => opC P ((matrixOperator (Fm s₀)).comp S₀) S₀
        (matrixOperator (Fm t))) s :=
      ((hFo s hsF).clm_comp (differentiableAt_const _)).add (differentiableAt_const _)
    have hI : DifferentiableAt ℂ (ContinuousLinearMap.inverse ∘ fun t =>
        opC P ((matrixOperator (Fm s₀)).comp S₀) S₀ (matrixOperator (Fm t))) s :=
      DifferentiableAt.comp (g := ContinuousLinearMap.inverse) s
        ((hsC.contDiffAt_map_inverse (n := 1)).differentiableAt one_ne_zero) hCd
    have hk : DifferentiableAt ℂ (fun t => kerSec P ((matrixOperator (Fm s₀)).comp S₀) S₀
        (matrixOperator (Fm t))) s :=
      (differentiableAt_const _).sub ((differentiableAt_const _).clm_comp
        ((differentiableAt_const _).clm_comp (hI.clm_comp (hFo s hsF))))
    exact differentiableAt_pi.2 fun j => differentiableAt_pi.2 fun k =>
      differentiableAt_pi.1 (hk.clm_apply (differentiableAt_const (fun j' => g₀ j' k))) j
  · intro s hsT i k
    have h := congrFun (f_kerSec hR₀ hS₀ hex hsT.2.1 hsT.2.2 (fun j' => g₀ j' k)) i
    rw [matrixOperator_apply] at h
    exact h
  · funext j k
    have hk0 : matrixOperator (Fm s₀) (fun j' => g₀ j' k) = 0 := by
      have h := hc₀ (Pi.single k 1)
      rw [← h]
      congr 1
      funext j'
      rw [matrixOperator_apply]
      simp [Pi.single_apply]
    exact congrFun (kerSec_of_mem_ker P ((matrixOperator (Fm s₀)).comp S₀) S₀ hk0) j

end KernelFamily

/-! ## Frisch's Lemme 3 (i) on Frisch's `T` -/

variable {S X : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [NormedAddCommGroup X]
  [NormedSpace ℂ X]

/-- **Frisch 1968 Lemme 3 (i) on Frisch's locus `T`** (sheaf level, reduced `T`): `f` holomorphic on
`V × U`, `K ∈ 𝒦` compact in `U`, `(g₀, f(s₀)|_K)` direct exact over `B(K)` with generalized inverses
`R₀`, `S₀`; `T` = Frisch's locus of the `B(K)`-operators `f(s)|_K`. Then `s₀ ∈ T`, and for `s ∈ T`
near `s₀`, `coker f` is flat over `T` at every point of `{s} × K̊`. -/
theorem relFibreFlatAt_frischLocus [FiniteDimensional ℂ S] [FiniteDimensional ℂ X]
    {𝒦 : Set (Set X)} (hTh1 : PrivilegedNbhdsProperty X 𝒦) (hA : RelationsTheoremA X 𝒦)
    {K U : Set X} (hK : K ∈ 𝒦) [CompactSpace K] (hU : IsOpen U) (hKU : K ⊆ U) {V : Set S}
    (hV : IsOpen V) {s₀ : S} (hs₀V : s₀ ∈ V) {a b c : ℕ} (f : Fin a → Fin b → S × X → ℂ)
    (hf : ∀ i j, DifferentiableOn ℂ (f i j) (V ×ˢ U)) (g₀ : Fin b → Fin c → holSubalgebra K)
    (h₀ : DirectExact g₀ (fun i j => fibRestrict K hKU (f i j) (hf i j) s₀))
    (R₀ : (Fin b → holSubalgebra K) →L[ℂ] (Fin c → holSubalgebra K))
    (hR₀ : ∀ e, matrixOperator g₀ (R₀ (matrixOperator g₀ e)) = matrixOperator g₀ e)
    (S₀ : (Fin a → holSubalgebra K) →L[ℂ] (Fin b → holSubalgebra K))
    (hS₀ : ∀ x, matrixOperator (fun i j => fibRestrict K hKU (f i j) (hf i j) s₀)
      (S₀ (matrixOperator (fun i j => fibRestrict K hKU (f i j) (hf i j) s₀) x)) =
        matrixOperator (fun i j => fibRestrict K hKU (f i j) (hf i j) s₀) x) :
    s₀ ∈ frischLocus ((matrixOperator g₀).comp R₀)
        ((matrixOperator (fun i j => fibRestrict K hKU (f i j) (hf i j) s₀)).comp S₀) S₀
        (fun s => matrixOperator (fun i j => fibRestrict K hKU (f i j) (hf i j) s)) V ∧
      ∀ᶠ s in 𝓝 s₀, s ∈ frischLocus ((matrixOperator g₀).comp R₀)
        ((matrixOperator (fun i j => fibRestrict K hKU (f i j) (hf i j) s₀)).comp S₀) S₀
        (fun s => matrixOperator (fun i j => fibRestrict K hKU (f i j) (hf i j) s)) V →
          ∀ y ∈ interior K, RelFibreFlatAt (frischLocus ((matrixOperator g₀).comp R₀)
            ((matrixOperator (fun i j => fibRestrict K hKU (f i j) (hf i j) s₀)).comp S₀) S₀
            (fun s => matrixOperator (fun i j => fibRestrict K hKU (f i j) (hf i j) s)) V)
            f (s, y) := by
  have hFd : ∀ᶠ s in 𝓝 s₀, DifferentiableAt ℂ
      (fun s i j => fibRestrict K hKU (f i j) (hf i j) s) s := by
    filter_upwards [hV.mem_nhds hs₀V] with s hs
    exact differentiableAt_pi.2 fun i => differentiableAt_pi.2 fun j =>
      differentiableAt_fibRestrict K hU hKU hV (f i j) (hf i j) hs
  obtain ⟨hs₀T, hσd, hσT, hσ₀⟩ := kerFamily_spec hs₀V hFd h₀ hR₀ hS₀
  refine ⟨hs₀T, ?_⟩
  have h₀' : DirectExact (kerFamily (fun s i j => fibRestrict K hKU (f i j) (hf i j) s) g₀ R₀ S₀
      s₀ s₀) (fun i j => fibRestrict K hKU (f i j) (hf i j) s₀) := by
    rw [hσ₀]
    exact h₀
  exact relFibreFlatAt_of_kernelFamily hTh1 hA _ hK hU hKU hV hs₀V hs₀T f hf _ hσd
    (Filter.Eventually.of_forall fun s hsT => hσT s hsT) h₀'

end
end Hironaka.HironakaG10LocFrischLocus
