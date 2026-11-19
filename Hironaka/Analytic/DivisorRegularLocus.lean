import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Hironaka.Analytic.HausdorffAreaFormula
import Hironaka.Manifold.HolomorphicContDiff

set_option autoImplicit false

/-!
# The regular points of the divisor of a holomorphic function

Let `V` be a complex inner product space and `g : V → ℂ`.  A point `x` is a *regular point of the
divisor of `g`* if near `x`

  `g = hᵐ v`,  `h(x) = 0`, `dh ≠ 0`, `v` without zeros, `m ≥ 1`

(`RegularPresentation`).  Near such a point the zero set of `g` is the complex hypersurface
`{h = 0}`, counted with multiplicity `m`.  This is the input of the integration current of the
divisor (Lelong--Poincaré, step LP2 of `ana:divisor-lelong-poincare`).

* `RegularPresentation.analyticOrderAt_line`: along a complex line through `x` in a direction `u`
  with `dh(x) u ≠ 0`, the order of vanishing of `g` at `x` is `m`; along a tangent line it is at
  least `2m` (`RegularPresentation.le_analyticOrderAt_line`).
* Hence any two presentations at `x` have the same multiplicity and proportional differentials
  (`RegularPresentation.m_eq`, `RegularPresentation.exists_fderiv_eq_smul`), and the following are
  intrinsic: `regularLocus g`, `divisorMult g x`, and the *transverse form*
  `transverseForm g x v w = Im (conj (ℓ v) ℓ w) / ‖ℓ‖²`, `ℓ = dh(x)` (`lineForm`), the real
  `(1,1)`-form of the complex line orthogonal to the tangent hyperplane
  (`RegularPresentation.transverseForm_eq`; `τ(v, i v) = |ℓ v|² / ‖ℓ‖² ≥ 0`).
* `Splitting u E`: an orthogonal splitting `V = ℂ u ⊕ ι(E)`; one exists for every unit vector of a
  finite-dimensional space (`exists_splitting`).
* `RegularPresentation.exists_graph_slices`: near a point with `dh(x) u ≠ 0` the zero set is the
  holomorphic graph `{k(w) u + ι w}` over an open `W ⊆ E`, every line parallel to `u` meets it
  only on the graph, and there `g` vanishes to order `m` along the line.
* `RegularPresentation.normDet_mul_transverseForm`: on such a graph, the volume factor of the
  graph map times `τ(u, i u)` is `1` (`normDet_graphDeriv`: `‖Dg‖_det = 1 + ‖dk‖²`;
  `lineForm_mul_graph`: `τ(u, i u) = 1 / (1 + ‖dk‖²)`).
* `exists_isOpen_regularLocus`, `exists_isOpen_transverseLocus`: both loci are the zero set
  intersected with an open set.
-/

open Set Filter Function
open scoped Topology ComplexConjugate InnerProductSpace ContDiff

noncomputable section

namespace Hironaka.DivisorRegularLocus

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- A regular presentation of the divisor of `g` at `x`: on an open set `U ∋ x`,
`g = h ^ m * v` with `h`, `v` holomorphic, `h x = 0`, `dh` nowhere zero and `v` without zeros on
`U`, and `m ≥ 1`. -/
structure RegularPresentation (g : V → ℂ) (x : V) where
  /-- the domain of the presentation -/
  U : Set V
  isOpen : IsOpen U
  mem : x ∈ U
  /-- the multiplicity -/
  m : ℕ
  m_pos : 0 < m
  /-- a local defining function of the hypersurface -/
  h : V → ℂ
  /-- the unit factor -/
  v : V → ℂ
  h_diff : DifferentiableOn ℂ h U
  v_diff : DifferentiableOn ℂ v U
  h_zero : h x = 0
  dh_ne : ∀ y ∈ U, fderiv ℂ h y ≠ 0
  v_ne : ∀ y ∈ U, v y ≠ 0
  eq : ∀ y ∈ U, g y = h y ^ m * v y

namespace RegularPresentation

variable {g : V → ℂ} {x : V}

theorem g_eq_zero_iff (P : RegularPresentation g x) {y : V} (hy : y ∈ P.U) :
    g y = 0 ↔ P.h y = 0 := by
  rw [P.eq y hy, mul_eq_zero, pow_eq_zero_iff P.m_pos.ne', or_iff_left (P.v_ne y hy)]

theorem g_x (P : RegularPresentation g x) : g x = 0 :=
  (P.g_eq_zero_iff P.mem).mpr P.h_zero

/-- A presentation at `x` is a presentation at every zero of `g` in its domain. -/
def restrict (P : RegularPresentation g x) {y : V} (hy : y ∈ P.U) (hgy : g y = 0) :
    RegularPresentation g y where
  U := P.U
  isOpen := P.isOpen
  mem := hy
  m := P.m
  m_pos := P.m_pos
  h := P.h
  v := P.v
  h_diff := P.h_diff
  v_diff := P.v_diff
  h_zero := (P.g_eq_zero_iff hy).mp hgy
  dh_ne := P.dh_ne
  v_ne := P.v_ne
  eq := P.eq

@[simp] theorem restrict_m (P : RegularPresentation g x) {y : V} (hy : y ∈ P.U)
    (hgy : g y = 0) : (P.restrict hy hgy).m = P.m := rfl

@[simp] theorem restrict_h (P : RegularPresentation g x) {y : V} (hy : y ∈ P.U)
    (hgy : g y = 0) : (P.restrict hy hgy).h = P.h := rfl

/-! ### Orders along complex lines -/

theorem hasFDerivAt_h (P : RegularPresentation g x) {y : V} (hy : y ∈ P.U) :
    HasFDerivAt P.h (fderiv ℂ P.h y) y :=
  ((P.h_diff y hy).differentiableAt (P.isOpen.mem_nhds hy)).hasFDerivAt

theorem line_mem_nhds (P : RegularPresentation g x) (a u : V) {s₀ : ℂ} (hs₀ : a + s₀ • u = x) :
    {s : ℂ | a + s • u ∈ P.U} ∈ 𝓝 s₀ := by
  have hc : Continuous fun s : ℂ => a + s • u := by fun_prop
  exact hc.continuousAt.preimage_mem_nhds (by rw [hs₀]; exact P.isOpen.mem_nhds P.mem)

theorem analyticAt_line_h (P : RegularPresentation g x) (a u : V) {s₀ : ℂ}
    (hs₀ : a + s₀ • u = x) : AnalyticAt ℂ (fun s : ℂ => P.h (a + s • u)) s₀ := by
  refine DifferentiableOn.analyticAt (s := {s : ℂ | a + s • u ∈ P.U}) ?_ (P.line_mem_nhds a u hs₀)
  intro s hs
  exact ((P.h_diff _ hs).differentiableAt (P.isOpen.mem_nhds hs)).comp_differentiableWithinAt
    (𝕜 := ℂ) s (by fun_prop)

theorem analyticAt_line_v (P : RegularPresentation g x) (a u : V) {s₀ : ℂ}
    (hs₀ : a + s₀ • u = x) : AnalyticAt ℂ (fun s : ℂ => P.v (a + s • u)) s₀ := by
  refine DifferentiableOn.analyticAt (s := {s : ℂ | a + s • u ∈ P.U}) ?_ (P.line_mem_nhds a u hs₀)
  intro s hs
  exact ((P.v_diff _ hs).differentiableAt (P.isOpen.mem_nhds hs)).comp_differentiableWithinAt
    (𝕜 := ℂ) s (by fun_prop)

theorem deriv_line_h (P : RegularPresentation g x) (a u : V) {s₀ : ℂ} (hs₀ : a + s₀ • u = x) :
    deriv (fun s : ℂ => P.h (a + s • u)) s₀ = fderiv ℂ P.h x u := by
  have hl : HasDerivAt (fun s : ℂ => a + s • u) u s₀ := by
    simpa using ((hasDerivAt_id s₀).smul_const u).const_add a
  have := (P.hasFDerivAt_h P.mem).comp_hasDerivAt_of_eq s₀ hl hs₀.symm
  exact this.deriv

theorem line_eventuallyEq (P : RegularPresentation g x) (a u : V) {s₀ : ℂ}
    (hs₀ : a + s₀ • u = x) :
    (fun s : ℂ => g (a + s • u)) =ᶠ[𝓝 s₀]
      (fun s : ℂ => P.h (a + s • u)) ^ P.m * fun s : ℂ => P.v (a + s • u) := by
  filter_upwards [P.line_mem_nhds a u hs₀] with s hs
  simp [P.eq _ hs]

theorem analyticOrderAt_line_v (P : RegularPresentation g x) (a u : V) {s₀ : ℂ}
    (hs₀ : a + s₀ • u = x) : analyticOrderAt (fun s : ℂ => P.v (a + s • u)) s₀ = 0 :=
  (P.analyticAt_line_v a u hs₀).analyticOrderAt_eq_zero.mpr
    (by simpa [hs₀] using P.v_ne x P.mem)

/-- **Transverse lines.**  If `dh(x) u ≠ 0` and the line `s ↦ a + s u` passes through `x` at
`s₀`, the order of `g` along it at `s₀` is `m`. -/
theorem analyticOrderAt_line (P : RegularPresentation g x) (a : V) {u : V} {s₀ : ℂ}
    (hs₀ : a + s₀ • u = x) (hu : fderiv ℂ P.h x u ≠ 0) :
    analyticOrderAt (fun s : ℂ => g (a + s • u)) s₀ = P.m := by
  rw [analyticOrderAt_congr (P.line_eventuallyEq a u hs₀),
    analyticOrderAt_mul ((P.analyticAt_line_h a u hs₀).pow _) (P.analyticAt_line_v a u hs₀),
    analyticOrderAt_pow (P.analyticAt_line_h a u hs₀), P.analyticOrderAt_line_v a u hs₀,
    (P.analyticAt_line_h a u hs₀).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
      (by simpa [hs₀] using P.h_zero) (by rwa [P.deriv_line_h a u hs₀])]
  simp

/-- **Tangent lines.**  If `dh(x) u = 0`, the order of `g` along a line through `x` in the
direction `u` is at least `2m`. -/
theorem le_analyticOrderAt_line (P : RegularPresentation g x) (a : V) {u : V} {s₀ : ℂ}
    (hs₀ : a + s₀ • u = x) (hu : fderiv ℂ P.h x u = 0) :
    ((2 * P.m : ℕ) : ℕ∞) ≤ analyticOrderAt (fun s : ℂ => g (a + s • u)) s₀ := by
  rw [analyticOrderAt_congr (P.line_eventuallyEq a u hs₀),
    analyticOrderAt_mul ((P.analyticAt_line_h a u hs₀).pow _) (P.analyticAt_line_v a u hs₀),
    analyticOrderAt_pow (P.analyticAt_line_h a u hs₀), P.analyticOrderAt_line_v a u hs₀,
    add_zero]
  have h2 : (2 : ℕ∞) ≤ analyticOrderAt (fun s : ℂ => P.h (a + s • u)) s₀ := by
    have := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (n := 2)
      (P.analyticAt_line_h a u hs₀)).mpr
    refine this fun i hi => ?_
    interval_cases i
    · simpa [hs₀] using P.h_zero
    · simpa [P.deriv_line_h a u hs₀] using hu
  calc ((2 * P.m : ℕ) : ℕ∞) = P.m • (2 : ℕ∞) := by push_cast; ring
    _ ≤ P.m • analyticOrderAt (fun s : ℂ => P.h (a + s • u)) s₀ := by
      simp only [nsmul_eq_mul]
      exact mul_le_mul_right h2 _

/-! ### Independence of the presentation -/

/-- Two nonzero functionals have a common non-root. -/
theorem exists_apply_ne_zero_both {ℓ ℓ' : V →L[ℂ] ℂ} (hℓ : ℓ ≠ 0) (hℓ' : ℓ' ≠ 0) :
    ∃ u : V, ℓ u ≠ 0 ∧ ℓ' u ≠ 0 := by
  obtain ⟨a, ha⟩ : ∃ a, ℓ a ≠ 0 := by
    by_contra h
    push Not at h
    exact hℓ (ContinuousLinearMap.ext h)
  obtain ⟨b, hb⟩ : ∃ b, ℓ' b ≠ 0 := by
    by_contra h
    push Not at h
    exact hℓ' (ContinuousLinearMap.ext h)
  by_cases ha' : ℓ' a ≠ 0
  · exact ⟨a, ha, ha'⟩
  by_cases hb' : ℓ b ≠ 0
  · exact ⟨b, hb', hb⟩
  push Not at ha' hb'
  refine ⟨a + b, ?_, ?_⟩ <;> simp [ha', hb', ha, hb]

theorem m_eq (P P' : RegularPresentation g x) : P.m = P'.m := by
  obtain ⟨u, hu, hu'⟩ := exists_apply_ne_zero_both (P.dh_ne x P.mem) (P'.dh_ne x P'.mem)
  have h1 := P.analyticOrderAt_line x (s₀ := 0) (by simp) hu
  have h2 := P'.analyticOrderAt_line x (s₀ := 0) (by simp) hu'
  rw [h1] at h2
  exact_mod_cast h2

theorem ker_le (P P' : RegularPresentation g x) {u : V} (hu : fderiv ℂ P'.h x u = 0) :
    fderiv ℂ P.h x u = 0 := by
  by_contra hne
  have h1 := P.analyticOrderAt_line x (s₀ := 0) (by simp) hne
  have h2 := P'.le_analyticOrderAt_line x (s₀ := 0) (by simp) hu
  rw [h1, ← P.m_eq P'] at h2
  have := P.m_pos
  have : 2 * P.m ≤ P.m := by exact_mod_cast h2
  omega

/-- The differentials of two presentations at the same point are proportional. -/
theorem exists_fderiv_eq_smul (P P' : RegularPresentation g x) :
    ∃ c : ℂ, c ≠ 0 ∧ fderiv ℂ P'.h x = c • fderiv ℂ P.h x := by
  set ℓ := fderiv ℂ P.h x
  set ℓ' := fderiv ℂ P'.h x
  obtain ⟨a, ha⟩ : ∃ a, ℓ a ≠ 0 := by
    by_contra h
    push Not at h
    exact P.dh_ne x P.mem (ContinuousLinearMap.ext h)
  refine ⟨ℓ' a / ℓ a, ?_, ?_⟩
  · intro h0
    rw [div_eq_zero_iff, or_iff_left ha] at h0
    -- then `ℓ' = 0` on the kernel of `ℓ` and at `a`, hence everywhere
    apply P'.dh_ne x P'.mem
    ext1 v
    have hk : ℓ (v - (ℓ v / ℓ a) • a) = 0 := by
      simp [map_sub, map_smul, div_mul_cancel₀ _ ha]
    have hk' : ℓ' (v - (ℓ v / ℓ a) • a) = 0 := P'.ker_le P hk
    simpa [map_sub, map_smul, h0] using hk'
  · ext1 v
    have hk : ℓ (v - (ℓ v / ℓ a) • a) = 0 := by
      simp [map_sub, map_smul, div_mul_cancel₀ _ ha]
    have hk' : ℓ' (v - (ℓ v / ℓ a) • a) = 0 := P'.ker_le P hk
    simp only [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at hk'
    simp only [smul_apply, smul_eq_mul]
    rw [hk']
    field_simp

end RegularPresentation

/-! ### Intrinsic multiplicity and transverse form -/

/-- The regular locus of the divisor of `g`. -/
def regularLocus (g : V → ℂ) : Set V := {x | Nonempty (RegularPresentation g x)}

open Classical in
/-- The multiplicity of the divisor of `g` at a regular point (`0` elsewhere). -/
def divisorMult (g : V → ℂ) (x : V) : ℕ :=
  if h : Nonempty (RegularPresentation g x) then h.some.m else 0

open Classical in
/-- The differential at `x` of the defining function of a chosen presentation (`0` off the
regular locus); it is intrinsic up to a nonzero factor. -/
def normalFun (g : V → ℂ) (x : V) : V →L[ℂ] ℂ :=
  if h : Nonempty (RegularPresentation g x) then fderiv ℂ h.some.h x else 0

/-- The real `(1,1)`-form `Im (conj (ℓ v) ℓ w) / ‖ℓ‖²` of a complex functional `ℓ`: the
transverse form of the hyperplane `ker ℓ`.  It does not change when `ℓ` is multiplied by a
nonzero scalar. -/
def lineForm (ℓ : V →L[ℂ] ℂ) (v w : V) : ℝ := (conj (ℓ v) * ℓ w).im / ‖ℓ‖ ^ 2

/-- The transverse `(1,1)`-form of the divisor of `g` at `x`. -/
def transverseForm (g : V → ℂ) (x : V) (v w : V) : ℝ := lineForm (normalFun g x) v w

theorem lineForm_smul (ℓ : V →L[ℂ] ℂ) {c : ℂ} (hc : c ≠ 0) (v w : V) :
    lineForm (c • ℓ) v w = lineForm ℓ v w := by
  simp only [lineForm, smul_apply, smul_eq_mul, map_mul, norm_smul, mul_pow]
  have key : conj c * conj (ℓ v) * (c * ℓ w) =
      ((Complex.normSq c : ℝ) : ℂ) * (conj (ℓ v) * ℓ w) := by
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  have hc2 : Complex.normSq c ≠ 0 := Complex.normSq_pos.mpr hc |>.ne'
  rw [key, Complex.im_ofReal_mul, ← Complex.normSq_eq_norm_sq, mul_div_mul_left _ _ hc2]

theorem lineForm_apply_I (ℓ : V →L[ℂ] ℂ) (v : V) :
    lineForm ℓ v (Complex.I • v) = ‖ℓ v‖ ^ 2 / ‖ℓ‖ ^ 2 := by
  simp only [lineForm, map_smul, smul_eq_mul]
  have key : conj (ℓ v) * (Complex.I * ℓ v) = ((Complex.normSq (ℓ v) : ℝ) : ℂ) * Complex.I := by
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  rw [key, Complex.im_ofReal_mul, Complex.I_im, mul_one, Complex.normSq_eq_norm_sq]

theorem lineForm_apply_I_nonneg (ℓ : V →L[ℂ] ℂ) (v : V) :
    0 ≤ lineForm ℓ v (Complex.I • v) := by
  rw [lineForm_apply_I]
  positivity

theorem lineForm_swap (ℓ : V →L[ℂ] ℂ) (v w : V) : lineForm ℓ w v = -lineForm ℓ v w := by
  simp only [lineForm]
  have key : conj (ℓ w) * ℓ v = conj (conj (ℓ v) * ℓ w) := by
    rw [map_mul, Complex.conj_conj, mul_comm]
  rw [key, Complex.conj_im, neg_div]

theorem lineForm_I_I (ℓ : V →L[ℂ] ℂ) (v w : V) :
    lineForm ℓ (Complex.I • v) (Complex.I • w) = lineForm ℓ v w := by
  simp only [lineForm, map_smul, smul_eq_mul, map_mul, Complex.conj_I]
  congr 2
  have : -Complex.I * conj (ℓ v) * (Complex.I * ℓ w) =
      (-(Complex.I * Complex.I)) * (conj (ℓ v) * ℓ w) := by ring
  rw [this, Complex.I_mul_I, neg_neg, one_mul]

namespace RegularPresentation

variable {g : V → ℂ} {x : V}

theorem mem_regularLocus (P : RegularPresentation g x) : x ∈ regularLocus g := ⟨P⟩

theorem divisorMult_eq (P : RegularPresentation g x) : divisorMult g x = P.m := by
  have hn : Nonempty (RegularPresentation g x) := ⟨P⟩
  rw [divisorMult, dif_pos hn]
  exact hn.some.m_eq P

theorem transverseForm_eq (P : RegularPresentation g x) (v w : V) :
    transverseForm g x v w = lineForm (fderiv ℂ P.h x) v w := by
  have hn : Nonempty (RegularPresentation g x) := ⟨P⟩
  rw [transverseForm, normalFun, dif_pos hn]
  obtain ⟨c, hc, hcℓ⟩ := hn.some.exists_fderiv_eq_smul P
  rw [hcℓ, lineForm_smul _ hc]

/-- The multiplicity is locally constant along the zero set. -/
theorem divisorMult_of_mem (P : RegularPresentation g x) {y : V} (hy : y ∈ P.U)
    (hgy : g y = 0) : divisorMult g y = P.m :=
  (P.restrict hy hgy).divisorMult_eq

theorem transverseForm_of_mem (P : RegularPresentation g x) {y : V} (hy : y ∈ P.U)
    (hgy : g y = 0) (v w : V) : transverseForm g y v w = lineForm (fderiv ℂ P.h y) v w :=
  (P.restrict hy hgy).transverseForm_eq v w

theorem mem_regularLocus_of_mem (P : RegularPresentation g x) {y : V} (hy : y ∈ P.U)
    (hgy : g y = 0) : y ∈ regularLocus g :=
  (P.restrict hy hgy).mem_regularLocus

end RegularPresentation

theorem eq_zero_of_mem_regularLocus {g : V → ℂ} {x : V} (hx : x ∈ regularLocus g) : g x = 0 :=
  hx.some.g_x

theorem transverseForm_apply_I_nonneg (g : V → ℂ) (x v : V) :
    0 ≤ transverseForm g x v (Complex.I • v) :=
  lineForm_apply_I_nonneg _ v

/-! ### Orthogonal splittings `V = ℂ u ⊕ E` -/

section Graph

/-- An orthogonal splitting `V = ℂ u ⊕ ι(E)` along a unit vector `u`. -/
structure Splitting (u : V) (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] where
  /-- the isometric embedding of the complement -/
  ι : E →ₗᵢ[ℂ] V
  /-- the projection onto the complement -/
  π : V →L[ℂ] E
  π_ι : ∀ w, π (ι w) = w
  π_u : π u = 0
  decomp : ∀ y, y = ⟪u, y⟫_ℂ • u + ι (π y)
  inner_ι : ∀ w, ⟪u, ι w⟫_ℂ = 0

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

namespace Splitting

variable {u : V} (S : Splitting u E)

theorem π_smul_add (s : ℂ) (w : E) : S.π (s • u + S.ι w) = w := by
  rw [map_add, map_smul, S.π_u, smul_zero, zero_add, S.π_ι]

theorem inner_smul_add (hu : ‖u‖ = 1) (s : ℂ) (w : E) : ⟪u, s • u + S.ι w⟫_ℂ = s := by
  rw [inner_add_right, inner_smul_right, S.inner_ι, add_zero, inner_self_eq_norm_sq_to_K, hu]
  simp

/-- The linear isomorphism `y ↦ (ℓ y, π y)` for a functional with `ℓ u ≠ 0`. -/
def equiv (ℓ : V →L[ℂ] ℂ) (hℓ : ℓ u ≠ 0) : V ≃L[ℂ] ℂ × E :=
  ContinuousLinearEquiv.equivOfInverse (ℓ.prod S.π)
    (((ℓ u)⁻¹ • (ContinuousLinearMap.fst ℂ ℂ E -
        ℓ.comp ((S.ι.toContinuousLinearMap).comp (ContinuousLinearMap.snd ℂ ℂ E)))).smulRight u +
      (S.ι.toContinuousLinearMap).comp (ContinuousLinearMap.snd ℂ ℂ E))
    (by
      intro y
      simp only [add_apply, ContinuousLinearMap.smulRight_apply, smul_apply, sub_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_comp, Function.comp_apply,
        ContinuousLinearMap.coe_snd', ContinuousLinearMap.prod_apply, smul_eq_mul,
        LinearIsometry.coe_toContinuousLinearMap]
      conv_rhs => rw [S.decomp y]
      congr 2
      have : ℓ y = ⟪u, y⟫_ℂ * ℓ u + ℓ (S.ι (S.π y)) := by
        conv_lhs => rw [S.decomp y]
        rw [map_add, map_smul, smul_eq_mul]
      rw [this]
      field_simp
      ring)
    (by
      rintro ⟨c, w⟩
      simp only [add_apply, ContinuousLinearMap.smulRight_apply, smul_apply, sub_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_comp, Function.comp_apply,
        ContinuousLinearMap.coe_snd', ContinuousLinearMap.prod_apply, smul_eq_mul, map_add,
        map_smul, LinearIsometry.coe_toContinuousLinearMap, S.π_ι, S.π_u]
      ext
      · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        field_simp
        ring
      · simp)

@[simp] theorem equiv_apply (ℓ : V →L[ℂ] ℂ) (hℓ : ℓ u ≠ 0) (y : V) :
    S.equiv ℓ hℓ y = (ℓ y, S.π y) := rfl

theorem coe_equiv (ℓ : V →L[ℂ] ℂ) (hℓ : ℓ u ≠ 0) :
    (S.equiv ℓ hℓ : V →L[ℂ] ℂ × E) = ℓ.prod S.π := rfl

end Splitting

/-- Every unit vector of a finite-dimensional space has an orthogonal splitting, with complement
a standard Euclidean space. -/
theorem exists_splitting [FiniteDimensional ℂ V] {u : V} (hu : ‖u‖ = 1) :
    ∃ m : ℕ, m + 1 = Module.finrank ℂ V ∧
      Nonempty (Splitting u (EuclideanSpace ℂ (Fin m))) := by
  let K : Submodule ℂ V := (ℂ ∙ u)ᗮ
  let b := stdOrthonormalBasis ℂ K
  have hfin : Module.finrank ℂ K + 1 = Module.finrank ℂ V := by
    have h := (ℂ ∙ u).finrank_add_finrank_orthogonal
    have hu0 : u ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hu; exact zero_ne_one hu
    rw [finrank_span_singleton hu0] at h
    change 1 + Module.finrank ℂ K = _ at h
    omega
  refine ⟨Module.finrank ℂ K, hfin, ⟨{
    ι := K.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
    π := (b.repr.toContinuousLinearEquiv : K →L[ℂ] EuclideanSpace ℂ (Fin _)).comp
      K.orthogonalProjectionOnto
    π_ι := ?_
    π_u := ?_
    decomp := ?_
    inner_ι := ?_ }⟩⟩
  · intro w
    simp [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  · have : K.orthogonalProjectionOnto u = 0 :=
      Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
        (Submodule.le_orthogonal_orthogonal _ (Submodule.mem_span_singleton_self u))
    simp [this]
  · intro y
    have h := (ℂ ∙ u).starProjection_add_starProjection_orthogonal y
    rw [Submodule.starProjection_unit_singleton ℂ hu] at h
    simp only [LinearIsometry.coe_comp, Submodule.coe_subtypeₗᵢ, LinearIsometryEquiv.coe_toLinearIsometry,
      Function.comp_apply, ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.symm_apply_apply]
    exact h.symm
  · intro w
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b.repr.symm w).2

end Graph

section GraphLocal

variable [FiniteDimensional ℂ V] {g : V → ℂ} {x : V}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

namespace RegularPresentation

theorem contDiffOn_h (P : RegularPresentation g x) : ContDiffOn ℂ ∞ P.h P.U :=
  Hironaka.contDiffOn_of_differentiableOn_complex P.h_diff P.isOpen

theorem continuousOn_fderiv_h (P : RegularPresentation g x) :
    ContinuousOn (fderiv ℂ P.h) P.U :=
  P.contDiffOn_h.continuousOn_fderiv_of_isOpen P.isOpen (by simp)

theorem hasStrictFDerivAt_h (P : RegularPresentation g x) {y : V} (hy : y ∈ P.U) :
    HasStrictFDerivAt P.h (fderiv ℂ P.h y) y :=
  (P.contDiffOn_h.contDiffAt (P.isOpen.mem_nhds hy)).hasStrictFDerivAt (by simp)

theorem isOpen_transverse (P : RegularPresentation g x) (u : V) :
    IsOpen {y | y ∈ P.U ∧ fderiv ℂ P.h y u ≠ 0} := by
  have hc : ContinuousOn (fun y => fderiv ℂ P.h y u) P.U :=
    P.continuousOn_fderiv_h.clm_apply continuousOn_const
  have := hc.isOpen_inter_preimage P.isOpen (isOpen_ne : IsOpen {z : ℂ | z ≠ 0})
  simpa [Set.inter_def] using this

/-- **The hypersurface is locally a graph over the complement of `u`** at a point where
`dh(x) u ≠ 0`: near `x`, `{h = 0}` is `{k(w) u + ι w : w ∈ W}` with `k` holomorphic. -/
theorem exists_graph (P : RegularPresentation g x) {u : V} (S : Splitting u E) (hxu : fderiv ℂ P.h x u ≠ 0) :
    ∃ (N : Set V) (W : Set E) (k : E → ℂ),
      IsOpen N ∧ x ∈ N ∧ N ⊆ P.U ∧ (∀ y ∈ N, fderiv ℂ P.h y u ≠ 0) ∧
      IsOpen W ∧ S.π x ∈ W ∧ DifferentiableOn ℂ k W ∧
      (∀ w ∈ W, k w • u + S.ι w ∈ N ∧ P.h (k w • u + S.ι w) = 0) ∧
      (∀ y ∈ N, P.h y = 0 → S.π y ∈ W ∧ k (S.π y) = ⟪u, y⟫_ℂ) := by
  have : CompleteSpace V := FiniteDimensional.complete ℂ V
  set N₀ : Set V := {y | y ∈ P.U ∧ fderiv ℂ P.h y u ≠ 0} with hN₀def
  have hN₀ : IsOpen N₀ := P.isOpen_transverse u
  have hxN₀ : x ∈ N₀ := ⟨P.mem, hxu⟩
  set Φ : V → ℂ × E := fun y => (P.h y, S.π y) with hΦdef
  have hΦ : ∀ y (hy : y ∈ N₀), HasStrictFDerivAt Φ
      ((S.equiv (fderiv ℂ P.h y) hy.2 : V →L[ℂ] ℂ × E)) y := by
    intro y hy
    rw [S.coe_equiv]
    exact (P.hasStrictFDerivAt_h hy.1).prodMk S.π.hasStrictFDerivAt
  have hΦc : ∀ y ∈ N₀, ContDiffAt ℂ 1 Φ y := fun y hy =>
    ((P.contDiffOn_h.contDiffAt (P.isOpen.mem_nhds hy.1)).of_le (by simp)).prodMk
      S.π.contDiff.contDiffAt
  set F := (hΦ x hxN₀).toOpenPartialHomeomorph Φ with hFdef
  have hFΦ : (F : V → ℂ × E) = Φ := (hΦ x hxN₀).toOpenPartialHomeomorph_coe
  have hxF : x ∈ F.source := (hΦ x hxN₀).mem_toOpenPartialHomeomorph_source
  set N : Set V := F.source ∩ N₀ with hNdef
  have hNo : IsOpen N := F.open_source.inter hN₀
  set W : Set E := (fun w : E => ((0 : ℂ), w)) ⁻¹' (F.target ∩ F.symm ⁻¹' N) with hWdef
  have hFy : ∀ y, F y = (P.h y, S.π y) := fun y => by rw [hFΦ]
  refine ⟨N, W, fun w => ⟪u, F.symm (0, w)⟫_ℂ, hNo, ⟨hxF, hxN₀⟩, fun y hy => hy.2.1,
    fun y hy => hy.2.2, ?_, ?_, ?_, ?_, ?_⟩
  · exact (F.isOpen_inter_preimage_symm hNo).preimage (by fun_prop)
  · have hΦx : F x = (0, S.π x) := by rw [hFy, P.h_zero]
    refine ⟨?_, ?_⟩
    · show ((0 : ℂ), S.π x) ∈ F.target
      rw [← hΦx]; exact F.map_source hxF
    · show F.symm (0, S.π x) ∈ N
      rw [← hΦx, F.left_inv hxF]
      exact ⟨hxF, hxN₀⟩
  · intro w hw
    have hyN : F.symm (0, w) ∈ N := hw.2
    have hsymm : ContDiffAt ℂ 1 F.symm (0, w) := by
      refine F.contDiffAt_symm (f₀' := S.equiv (fderiv ℂ P.h (F.symm (0, w))) hyN.2.2)
        hw.1 ?_ ?_
      · rw [hFΦ]; exact (hΦ _ hyN.2).hasFDerivAt
      · rw [hFΦ]; exact hΦc _ hyN.2
    have hd : DifferentiableAt ℂ (fun w : E => ⟪u, F.symm (0, w)⟫_ℂ) w := by
      have h1 : DifferentiableAt ℂ (fun w : E => F.symm (0, w)) w :=
        (hsymm.differentiableAt one_ne_zero).comp w (by fun_prop)
      exact (innerSL ℂ u).differentiableAt.comp w h1
    exact hd.differentiableWithinAt
  · intro w hw
    have hyN : F.symm (0, w) ∈ N := hw.2
    have hFy' : F (F.symm (0, w)) = (0, w) := F.right_inv hw.1
    rw [hFy] at hFy'
    have hh : P.h (F.symm (0, w)) = 0 := congrArg Prod.fst hFy'
    have hpr : S.π (F.symm (0, w)) = w := congrArg Prod.snd hFy'
    have hdec := S.decomp (F.symm (0, w))
    rw [hpr] at hdec
    rw [← hdec]
    exact ⟨hyN, hh⟩
  · intro y hy hhy
    have hFy' : F y = (0, S.π y) := by rw [hFy, hhy]
    have htarget : ((0 : ℂ), S.π y) ∈ F.target := by rw [← hFy']; exact F.map_source hy.1
    have hsy : F.symm (0, S.π y) = y := by rw [← hFy', F.left_inv hy.1]
    refine ⟨⟨htarget, ?_⟩, ?_⟩
    · show F.symm (0, S.π y) ∈ N
      rw [hsy]; exact hy
    · show ⟪u, F.symm (0, S.π y)⟫_ℂ = ⟪u, y⟫_ℂ
      rw [hsy]

/-- **Graph pieces with their slices.**  Near a point of a regular presentation transverse to
`u`, the zero set of `g` is a holomorphic graph over the complement of `u`; on every line parallel
to `u` through the neighbourhood the only zero is on the graph, where `g` vanishes to order `m`
along the line; and every zero in the neighbourhood is regular with the same multiplicity. -/
theorem exists_graph_slices (P : RegularPresentation g x) {u : V} (hu : ‖u‖ = 1)
    (S : Splitting u E) (hxu : fderiv ℂ P.h x u ≠ 0) :
    ∃ (N : Set V) (W : Set E) (k : E → ℂ),
      IsOpen N ∧ x ∈ N ∧ N ⊆ P.U ∧ (∀ y ∈ N, fderiv ℂ P.h y u ≠ 0) ∧
      IsOpen W ∧ S.π x ∈ W ∧ DifferentiableOn ℂ k W ∧
      (∀ w ∈ W, k w • u + S.ι w ∈ N ∧ P.h (k w • u + S.ι w) = 0) ∧
      (∀ (w : E) (s : ℂ), s • u + S.ι w ∈ N →
        (g (s • u + S.ι w) = 0 ↔ w ∈ W ∧ s = k w)) ∧
      (∀ w ∈ W, analyticOrderAt (fun s : ℂ => g (S.ι w + s • u)) (k w) = P.m) := by
  obtain ⟨N, W, k, hNo, hxN, hNU, hNtr, hWo, hxW, hk, hgraph, hzero⟩ := P.exists_graph S hxu
  refine ⟨N, W, k, hNo, hxN, hNU, hNtr, hWo, hxW, hk, hgraph, ?_, ?_⟩
  · intro w s hy
    rw [P.g_eq_zero_iff (hNU hy)]
    constructor
    · intro hh
      obtain ⟨hW, hk'⟩ := hzero _ hy hh
      rw [S.π_smul_add] at hW hk'
      rw [S.inner_smul_add hu] at hk'
      exact ⟨hW, hk'.symm⟩
    · rintro ⟨hw, rfl⟩
      exact (hgraph w hw).2
  · intro w hw
    obtain ⟨hyN, hh⟩ := hgraph w hw
    have hgy : g (k w • u + S.ι w) = 0 := (P.g_eq_zero_iff (hNU hyN)).mpr hh
    have := (P.restrict (hNU hyN) hgy).analyticOrderAt_line (S.ι w) (s₀ := k w) (u := u)
      (by rw [add_comm]) (by simpa using hNtr _ hyN)
    simpa using this

end RegularPresentation

end GraphLocal

/-! ### The Jacobian of a graph over the complement of `u` -/

section Jacobian

/-- `det (1 + A B) = det (1 + B A)` for linear maps between finite free modules. -/
theorem det_one_add_comp_comm {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] [AddCommGroup N] [Module R N] [Module.Free R N]
    [Module.Finite R N] (A : N →ₗ[R] M) (B : M →ₗ[R] N) :
    LinearMap.det (1 + A ∘ₗ B) = LinearMap.det (1 + B ∘ₗ A) := by
  classical
  let bM := Module.Free.chooseBasis R M
  let bN := Module.Free.chooseBasis R N
  rw [← LinearMap.det_toMatrix bM, ← LinearMap.det_toMatrix bN, map_add, map_add,
    LinearMap.toMatrix_one, LinearMap.toMatrix_one, LinearMap.toMatrix_comp bM bN bM,
    LinearMap.toMatrix_comp bN bM bN, Matrix.det_one_add_mul_comm]

/-- On a complex Euclidean space the real inner product is the real part of the complex one. -/
theorem real_inner_euclidean {k : ℕ} (x y : EuclideanSpace ℂ (Fin k)) :
    ⟪x, y⟫_ℝ = (⟪x, y⟫_ℂ).re := by
  simp only [PiLp.inner_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.inner, RCLike.inner_apply]

variable {n m : ℕ} {u : EuclideanSpace ℂ (Fin n)}

/-- The differential `e ↦ κ(e) u + ι e` of the graph map `w ↦ k(w) u + ι w`. -/
def graphDeriv (S : Splitting u (EuclideanSpace ℂ (Fin m)))
    (κ : EuclideanSpace ℂ (Fin m) →L[ℂ] ℂ) :
    EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  κ.smulRight u + S.ι.toContinuousLinearMap

@[simp] theorem graphDeriv_apply (S : Splitting u (EuclideanSpace ℂ (Fin m)))
    (κ : EuclideanSpace ℂ (Fin m) →L[ℂ] ℂ) (e : EuclideanSpace ℂ (Fin m)) :
    graphDeriv S κ e = κ e • u + S.ι e := rfl

theorem inner_graphDeriv (hu : ‖u‖ = 1) (S : Splitting u (EuclideanSpace ℂ (Fin m)))
    (κ : EuclideanSpace ℂ (Fin m) →L[ℂ] ℂ) (e e' : EuclideanSpace ℂ (Fin m)) :
    ⟪graphDeriv S κ e, graphDeriv S κ e'⟫_ℂ =
      ⟪e + κ e • (InnerProductSpace.toDual ℂ (EuclideanSpace ℂ (Fin m))).symm κ, e'⟫_ℂ := by
  have huu : ⟪u, u⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hu]; simp
  have he' : ⟪u, S.ι e'⟫_ℂ = 0 := S.inner_ι e'
  have he : ⟪S.ι e, u⟫_ℂ = 0 := by rw [← inner_conj_symm, S.inner_ι e, map_zero]
  simp only [graphDeriv_apply, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, huu, he, he', LinearIsometry.inner_map_map,
    InnerProductSpace.toDual_symm_apply]
  ring

/-- **The volume factor of a graph differential**: `‖Dg‖_det = 1 + ‖κ‖²`. -/
theorem normDet_graphDeriv (hu : ‖u‖ = 1) (S : Splitting u (EuclideanSpace ℂ (Fin m)))
    (κ : EuclideanSpace ℂ (Fin m) →L[ℂ] ℂ) :
    (((graphDeriv S κ).restrictScalars ℝ : EuclideanSpace ℂ (Fin m) →L[ℝ]
        EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin m) →ₗ[ℝ]
        EuclideanSpace ℂ (Fin n)).normDet = 1 + ‖κ‖ ^ 2 := by
  set b : EuclideanSpace ℂ (Fin m) := (InnerProductSpace.toDual ℂ _).symm κ with hb
  have hκb : ∀ e, κ e = ⟪b, e⟫_ℂ := fun e => by
    rw [hb, InnerProductSpace.toDual_symm_apply]
  have hnb : ‖b‖ = ‖κ‖ := by rw [hb, LinearIsometryEquiv.norm_map]
  set L : EuclideanSpace ℂ (Fin m) →L[ℝ] EuclideanSpace ℂ (Fin n) :=
    (graphDeriv S κ).restrictScalars ℝ with hL
  set B : EuclideanSpace ℂ (Fin m) →ₗ[ℝ] ℂ :=
    ((κ : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] ℂ).restrictScalars ℝ) with hB
  set A : ℂ →ₗ[ℝ] EuclideanSpace ℂ (Fin m) :=
    (LinearMap.toSpanSingleton ℂ (EuclideanSpace ℂ (Fin m)) b).restrictScalars ℝ with hA
  have hgram : (((ContinuousLinearMap.adjoint L).comp L : EuclideanSpace ℂ (Fin m) →L[ℝ]
      EuclideanSpace ℂ (Fin m)) : EuclideanSpace ℂ (Fin m) →ₗ[ℝ] EuclideanSpace ℂ (Fin m)) =
      (1 + A ∘ₗ B : EuclideanSpace ℂ (Fin m) →ₗ[ℝ] EuclideanSpace ℂ (Fin m)) := by
    apply LinearMap.ext
    intro e
    apply ext_inner_right ℝ
    intro e'
    rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.adjoint_inner_left, real_inner_euclidean, real_inner_euclidean]
    simp only [hL, ContinuousLinearMap.coe_restrictScalars', inner_graphDeriv hu,
      LinearMap.add_apply, Module.End.one_apply, LinearMap.coe_comp, Function.comp_apply, hA, hB,
      LinearMap.coe_restrictScalars, LinearMap.toSpanSingleton_apply, ContinuousLinearMap.coe_coe]
    rfl
  have hBA : B ∘ₗ A = (‖b‖ ^ 2 : ℝ) • (LinearMap.id : ℂ →ₗ[ℝ] ℂ) := by
    apply LinearMap.ext
    intro z
    simp only [LinearMap.coe_comp, Function.comp_apply, hA, hB, LinearMap.coe_restrictScalars,
      LinearMap.toSpanSingleton_apply, ContinuousLinearMap.coe_coe, map_smul, smul_eq_mul,
      hκb b, inner_self_eq_norm_sq_to_K, LinearMap.smul_apply, LinearMap.id_apply]
    rw [Complex.real_smul, mul_comm]
    norm_cast
  have hdet : LinearMap.det (1 + A ∘ₗ B : EuclideanSpace ℂ (Fin m) →ₗ[ℝ]
      EuclideanSpace ℂ (Fin m)) = (1 + ‖b‖ ^ 2) ^ 2 := by
    rw [det_one_add_comp_comm, hBA]
    have : (1 : ℂ →ₗ[ℝ] ℂ) + (‖b‖ ^ 2 : ℝ) • (LinearMap.id : ℂ →ₗ[ℝ] ℂ) =
        (1 + ‖b‖ ^ 2 : ℝ) • (LinearMap.id : ℂ →ₗ[ℝ] ℂ) := by
      rw [add_smul, one_smul]; rfl
    rw [this, LinearMap.det_smul, LinearMap.det_id, mul_one, Complex.finrank_real_complex]
  have hsq := ContinuousLinearMap.normDet_sq (𝕜 := ℝ) L
  simp only [RCLike.ofReal_real_eq_id, id] at hsq
  rw [ContinuousLinearMap.det, hgram, hdet] at hsq
  have hnn : 0 ≤ ((L : EuclideanSpace ℂ (Fin m) →ₗ[ℝ] EuclideanSpace ℂ (Fin n))).normDet :=
    LinearMap.normDet_nonneg _
  rw [← hnb]
  nlinarith [sq_nonneg (((L : EuclideanSpace ℂ (Fin m) →ₗ[ℝ] EuclideanSpace ℂ (Fin n))).normDet
      - (1 + ‖b‖ ^ 2)), sq_nonneg ‖b‖]

/-- **The transverse form of a graph.**  If `ℓ` vanishes on the graph differential
`e ↦ κ(e) u + ι e` and `ℓ u ≠ 0`, then `‖ℓ‖² = |ℓ u|² (1 + ‖κ‖²)`, so the transverse form of
`ker ℓ` on `(u, i u)` is `1 / (1 + ‖κ‖²)`. -/
theorem lineForm_mul_graph {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [CompleteSpace V] {u : V} (hu : ‖u‖ = 1) (S : Splitting u E)
    (κ : E →L[ℂ] ℂ) (ℓ : V →L[ℂ] ℂ) (hℓu : ℓ u ≠ 0)
    (hker : ∀ e, ℓ (κ e • u + S.ι e) = 0) :
    lineForm ℓ u (Complex.I • u) * (1 + ‖κ‖ ^ 2) = 1 := by
  set a : V := (InnerProductSpace.toDual ℂ V).symm ℓ with ha
  have hℓa : ∀ y, ℓ y = ⟪a, y⟫_ℂ := fun y => by rw [ha, InnerProductSpace.toDual_symm_apply]
  have hna : ‖a‖ = ‖ℓ‖ := by rw [ha, LinearIsometryEquiv.norm_map]
  set b : E := (InnerProductSpace.toDual ℂ E).symm κ with hb
  have hκb : ∀ e, κ e = ⟪b, e⟫_ℂ := fun e => by rw [hb, InnerProductSpace.toDual_symm_apply]
  have hnb : ‖b‖ = ‖κ‖ := by rw [hb, LinearIsometryEquiv.norm_map]
  have hua : ⟪u, a⟫_ℂ = conj (ℓ u) := by rw [hℓa, inner_conj_symm]
  -- the component of `a` in the complement
  have hπa : S.π a = (-conj (ℓ u)) • b := by
    apply ext_inner_right ℂ
    intro e
    have h1 : ⟪S.π a, e⟫_ℂ = ⟪S.ι (S.π a), S.ι e⟫_ℂ := (S.ι.inner_map_map _ _).symm
    have h2 : S.ι (S.π a) = a - ⟪u, a⟫_ℂ • u := eq_sub_of_add_eq' (S.decomp a).symm
    have hk := hker e
    rw [map_add, map_smul, smul_eq_mul] at hk
    rw [h1, h2, inner_sub_left, inner_smul_left, S.inner_ι, mul_zero, sub_zero, ← hℓa,
      inner_smul_left, ← hκb, map_neg, Complex.conj_conj]
    linear_combination hk
  have hpyth : ‖a‖ ^ 2 = ‖ℓ u‖ ^ 2 + ‖ℓ u‖ ^ 2 * ‖κ‖ ^ 2 := by
    have horth : ⟪⟪u, a⟫_ℂ • u, S.ι (S.π a)⟫_ℂ = 0 := by
      rw [inner_smul_left, S.inner_ι, mul_zero]
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
    rw [← S.decomp a] at h
    rw [sq, h, LinearIsometry.norm_map, hπa, norm_smul, norm_smul, hua, hu, norm_neg,
      Complex.norm_conj, hnb]
    ring
  rw [lineForm_apply_I, ← hna, hpyth]
  have hℓu' : ‖ℓ u‖ ^ 2 ≠ 0 := by positivity
  field_simp

/-- **Area factor times transverse density is one on a graph piece.**  For a regular
presentation, a splitting along `u` and a holomorphic graph `w ↦ k(w) u + ι w` of the zero set on
an open `W`, transverse to `u`, the Jacobian of the graph map times the transverse density
`τ(u, i u)` is `1` at every point of `W`. -/
theorem RegularPresentation.normDet_mul_transverseForm {n m : ℕ}
    {g : EuclideanSpace ℂ (Fin n) → ℂ} {x : EuclideanSpace ℂ (Fin n)}
    (P : RegularPresentation g x) {u : EuclideanSpace ℂ (Fin n)} (hu : ‖u‖ = 1)
    (S : Splitting u (EuclideanSpace ℂ (Fin m))) {W : Set (EuclideanSpace ℂ (Fin m))}
    {k : EuclideanSpace ℂ (Fin m) → ℂ} (hWo : IsOpen W) (hk : DifferentiableOn ℂ k W)
    (hG : ∀ w ∈ W, k w • u + S.ι w ∈ P.U ∧ P.h (k w • u + S.ι w) = 0)
    (htr : ∀ w ∈ W, fderiv ℂ P.h (k w • u + S.ι w) u ≠ 0) {w : EuclideanSpace ℂ (Fin m)}
    (hw : w ∈ W) :
    ((fderiv ℝ (fun w => k w • u + S.ι w) w : EuclideanSpace ℂ (Fin m) →L[ℝ]
        EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin m) →ₗ[ℝ]
        EuclideanSpace ℂ (Fin n)).normDet *
      transverseForm g (k w • u + S.ι w) u (Complex.I • u) = 1 := by
  set G : EuclideanSpace ℂ (Fin m) → EuclideanSpace ℂ (Fin n) := fun w => k w • u + S.ι w
    with hGdef
  set κ := fderiv ℂ k w with hκ
  have hkd : HasFDerivAt k κ w := (hk.differentiableAt (hWo.mem_nhds hw)).hasFDerivAt
  have hGd : HasFDerivAt G (graphDeriv S κ) w := by
    have h1 := hkd.smul_const u
    have h2 := S.ι.toContinuousLinearMap.hasFDerivAt (x := w)
    exact h1.add h2
  have hGr : fderiv ℝ G w = (graphDeriv S κ).restrictScalars ℝ :=
    (hGd.restrictScalars ℝ).fderiv
  set ℓ := fderiv ℂ P.h (G w) with hℓ
  have hGU := (hG w hw).1
  have hhd : HasFDerivAt P.h ℓ (G w) :=
    ((P.h_diff _ hGU).differentiableAt (P.isOpen.mem_nhds hGU)).hasFDerivAt
  have hcomp : HasFDerivAt (P.h ∘ G) (ℓ.comp (graphDeriv S κ)) w := hhd.comp w hGd
  have hzero : HasFDerivAt (P.h ∘ G) (0 : EuclideanSpace ℂ (Fin m) →L[ℂ] ℂ) w := by
    have hev : (P.h ∘ G) =ᶠ[𝓝 w] fun _ => (0 : ℂ) := by
      filter_upwards [hWo.mem_nhds hw] with y hy
      exact (hG y hy).2
    exact (hasFDerivAt_const (0 : ℂ) w).congr_of_eventuallyEq hev
  have hker : ℓ.comp (graphDeriv S κ) = 0 := hcomp.unique hzero
  have hker' : ∀ e, ℓ (κ e • u + S.ι e) = 0 := fun e => by
    have := congrArg (fun L => L e) hker
    simpa using this
  have hgw : g (G w) = 0 := (P.g_eq_zero_iff hGU).mpr (hG w hw).2
  rw [hGr, normDet_graphDeriv hu, P.transverseForm_of_mem hGU hgw]
  have := lineForm_mul_graph hu S κ ℓ (htr w hw) hker'
  linarith

end Jacobian

/-! ### The regular and transverse loci are relatively open in the zero set -/

section Loci

variable {g : V → ℂ}

theorem lineForm_apply_I_ne_zero_iff {ℓ : V →L[ℂ] ℂ} (hℓ : ℓ ≠ 0) (u : V) :
    lineForm ℓ u (Complex.I • u) ≠ 0 ↔ ℓ u ≠ 0 := by
  rw [lineForm_apply_I]
  have : ‖ℓ‖ ≠ 0 := norm_ne_zero_iff.mpr hℓ
  constructor
  · intro h h0
    apply h
    simp [h0]
  · intro h
    exact div_ne_zero (pow_ne_zero 2 (norm_ne_zero_iff.mpr h)) (pow_ne_zero 2 this)

/-- The points of the regular locus where the divisor is transverse to the direction `u`. -/
def transverseLocus (g : V → ℂ) (u : V) : Set V :=
  {x | x ∈ regularLocus g ∧ transverseForm g x u (Complex.I • u) ≠ 0}

theorem RegularPresentation.mem_transverseLocus_iff {x : V} (P : RegularPresentation g x)
    {y : V} (hy : y ∈ P.U) (hgy : g y = 0) (u : V) :
    y ∈ transverseLocus g u ↔ fderiv ℂ P.h y u ≠ 0 := by
  have hreg := P.mem_regularLocus_of_mem hy hgy
  simp only [transverseLocus, Set.mem_ofPred_eq, hreg, true_and,
    P.transverseForm_of_mem hy hgy]
  exact lineForm_apply_I_ne_zero_iff (P.dh_ne y hy) u

theorem exists_isOpen_regularLocus (g : V → ℂ) :
    ∃ O : Set V, IsOpen O ∧ regularLocus g = {x | g x = 0} ∩ O := by
  let P : ∀ x, x ∈ regularLocus g → RegularPresentation g x := fun x hx => Classical.choice hx
  refine ⟨⋃ x, ⋃ hx : x ∈ regularLocus g, (P x hx).U,
    isOpen_iUnion fun x => isOpen_iUnion fun hx => (P x hx).isOpen, ?_⟩
  ext y
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · intro hy
    exact ⟨eq_zero_of_mem_regularLocus hy, y, hy, (P y hy).mem⟩
  · rintro ⟨hgy, x, hx, hyU⟩
    exact (P x hx).mem_regularLocus_of_mem hyU hgy

theorem exists_isOpen_transverseLocus [FiniteDimensional ℂ V] (g : V → ℂ) (u : V) :
    ∃ O : Set V, IsOpen O ∧ transverseLocus g u = {x | g x = 0} ∩ O := by
  classical
  let P : ∀ x, x ∈ transverseLocus g u → RegularPresentation g x := fun x hx =>
    Classical.choice hx.1
  refine ⟨⋃ x, ⋃ hx : x ∈ transverseLocus g u, {y | y ∈ (P x hx).U ∧
    fderiv ℂ (P x hx).h y u ≠ 0}, ?_, ?_⟩
  · exact isOpen_iUnion fun x => isOpen_iUnion fun hx => (P x hx).isOpen_transverse u
  · ext y
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro hy
      refine ⟨eq_zero_of_mem_regularLocus hy.1, y, hy, (P y hy).mem, ?_⟩
      exact ((P y hy).mem_transverseLocus_iff (P y hy).mem
        (eq_zero_of_mem_regularLocus hy.1) u).mp hy
    · rintro ⟨hgy, x, hx, hyU, hdy⟩
      exact ((P x hx).mem_transverseLocus_iff hyU hgy u).mpr hdy

theorem transverseLocus_subset_regularLocus (g : V → ℂ) (u : V) :
    transverseLocus g u ⊆ regularLocus g := fun _ hx => hx.1

end Loci

end Hironaka.DivisorRegularLocus
