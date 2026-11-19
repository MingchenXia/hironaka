import Hironaka.Resolution.HironakaG10FlatResolutionStart

/-! # Direct exactness of a family of 3-term complexes persists (Douady 1966, §2 Prop. 3; §8)

Douady 1966, §8 (Scholie, Prop. 2 (b): "on a une suite exacte directe au point `s`, donc une suite
exacte directe de fibrés triviaux sur un voisinage `V` de `s`") and §2 n° 3 Prop. 3, for a complex of
three terms. Let `g(s) : E₂ → E₁`, `f(s) : E₁ → E₀` be families of bounded operators between complex
Banach spaces with `f(s) g(s) = 0`. If at `s₀` the start is exact (`ker f(s₀) = im g(s₀)`) and both
maps are direct (bounded generalized inverses `R₀`, `S₀`), then the same holds near `s₀`.

Put `P = g₀ R₀` (a projection onto `im g₀ = ker f₀`), `Q = f₀ S₀` (onto `im f₀`) and
`A(g) = P g R₀ P + (1 − P)` (`opA`), `B(f) = (1 − P) S₀ f + P` (`opB`),
`C(f) = f (1 − P) S₀ + (1 − Q)` (`opC`); all three are the identity at `s₀` (`opA_self`, `opB_self`,
`opC_self`), hence invertible near `s₀`. Wherever they are invertible and `f g = 0`
(`directExact3_of_isInvertible`):
* `ker f ∩ ker P = 0` (`B` is injective);
* `A` commutes with `P`, and `R = R₀ P A⁻¹ P` satisfies `P g R = P`; hence `g R = 1` on `ker f`
  (EXACTNESS) and `g R g = g` (generalized inverse of `g`);
* `f (1 − P) = C Q f₀`, so `f = C f₀ (1 − g R)` and `S = (1 − P) S₀ C⁻¹` satisfies `f S f = f`.

* `eventually_directExact3` — the persistence statement for continuous families;
* matrix form over a complete normed algebra: **`directExact_eventually`** (a family of matrix starts
  continuous at `s₀` with `f g = 0` near `s₀`, `DirectExact` at `s₀` ⇒ `DirectExact` near `s₀`);
* `directExact_of_factor`: a start `(g, f)` with `f g = 0` is direct exact when some direct exact
  `(d₁, f)` factors as `d₁ = g X` (independence of the second matrix of a start).
BP: hironaka-g10-loc-direct-persistence.tex. -/
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace Hironaka.HironakaG10LocDirectPersistence
noncomputable section
open HironakaG10FlatPolydiscAlgebra HironakaG10FlatResolutionStart HironakaG10FlatGeneralizedInverse

/-! ## The comparison operators -/

section Abstract
variable {E₂ E₁ E₀ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] [NormedAddCommGroup E₁]
  [NormedSpace ℂ E₁] [NormedAddCommGroup E₀] [NormedSpace ℂ E₀]

/-- `A(g) = P g R₀ P + (1 − P)`. -/
def opA (P : E₁ →L[ℂ] E₁) (R₀ : E₁ →L[ℂ] E₂) (g : E₂ →L[ℂ] E₁) : E₁ →L[ℂ] E₁ :=
  P.comp (g.comp (R₀.comp P)) + (ContinuousLinearMap.id ℂ E₁ - P)

/-- `B(f) = (1 − P) S₀ f + P`. -/
def opB (P : E₁ →L[ℂ] E₁) (S₀ : E₀ →L[ℂ] E₁) (f : E₁ →L[ℂ] E₀) : E₁ →L[ℂ] E₁ :=
  (ContinuousLinearMap.id ℂ E₁ - P).comp (S₀.comp f) + P

/-- `C(f) = f (1 − P) S₀ + (1 − Q)`. -/
def opC (P : E₁ →L[ℂ] E₁) (Q : E₀ →L[ℂ] E₀) (S₀ : E₀ →L[ℂ] E₁) (f : E₁ →L[ℂ] E₀) :
    E₀ →L[ℂ] E₀ :=
  f.comp ((ContinuousLinearMap.id ℂ E₁ - P).comp S₀) + (ContinuousLinearMap.id ℂ E₀ - Q)

theorem opA_apply (P : E₁ →L[ℂ] E₁) (R₀ : E₁ →L[ℂ] E₂) (g : E₂ →L[ℂ] E₁) (x : E₁) :
    opA P R₀ g x = P (g (R₀ (P x))) + (x - P x) := rfl

theorem opB_apply (P : E₁ →L[ℂ] E₁) (S₀ : E₀ →L[ℂ] E₁) (f : E₁ →L[ℂ] E₀) (x : E₁) :
    opB P S₀ f x = (S₀ (f x) - P (S₀ (f x))) + P x := rfl

theorem opC_apply (P : E₁ →L[ℂ] E₁) (Q : E₀ →L[ℂ] E₀) (S₀ : E₀ →L[ℂ] E₁) (f : E₁ →L[ℂ] E₀)
    (y : E₀) : opC P Q S₀ f y = f (S₀ y - P (S₀ y)) + (y - Q y) := rfl

variable {g₀ : E₂ →L[ℂ] E₁} {f₀ : E₁ →L[ℂ] E₀} {R₀ : E₁ →L[ℂ] E₂} {S₀ : E₀ →L[ℂ] E₁}

/-- `P = g₀ R₀` is idempotent. -/
theorem projP_idem (hR₀ : ∀ e, g₀ (R₀ (g₀ e)) = g₀ e) (x : E₁) :
    g₀ (R₀ (g₀ (R₀ x))) = g₀ (R₀ x) := hR₀ (R₀ x)

/-- `Q = f₀ S₀` fixes `im f₀`. -/
theorem projQ_f (hS₀ : ∀ x, f₀ (S₀ (f₀ x)) = f₀ x) (x : E₁) :
    (f₀.comp S₀) (f₀ x) = f₀ x := hS₀ x

/-- `(1 − P) S₀ f₀ = 1 − P` (uses exactness at `s₀`). -/
theorem one_sub_P_S₀_f₀ (hR₀ : ∀ e, g₀ (R₀ (g₀ e)) = g₀ e) (hS₀ : ∀ x, f₀ (S₀ (f₀ x)) = f₀ x)
    (hex : ∀ x, f₀ x = 0 → ∃ e, g₀ e = x) (x : E₁) :
    S₀ (f₀ x) - g₀ (R₀ (S₀ (f₀ x))) = x - g₀ (R₀ x) := by
  have hk : f₀ (S₀ (f₀ x) - x) = 0 := by rw [map_sub, hS₀, sub_self]
  obtain ⟨e, he⟩ := hex _ hk
  have h2 : g₀ (R₀ (S₀ (f₀ x))) - g₀ (R₀ x) = S₀ (f₀ x) - x := by
    rw [← map_sub, ← map_sub, ← he, hR₀]
  rw [← sub_eq_zero, show S₀ (f₀ x) - g₀ (R₀ (S₀ (f₀ x))) - (x - g₀ (R₀ x)) =
    (S₀ (f₀ x) - x) - (g₀ (R₀ (S₀ (f₀ x))) - g₀ (R₀ x)) by abel, h2, sub_self]

/-- `A(g₀) = 1`. -/
theorem opA_self (hR₀ : ∀ e, g₀ (R₀ (g₀ e)) = g₀ e) :
    opA (g₀.comp R₀) R₀ g₀ = ContinuousLinearMap.id ℂ E₁ := by
  ext x
  rw [opA_apply]
  show g₀ (R₀ (g₀ (R₀ (g₀ (R₀ x))))) + (x - g₀ (R₀ x)) = x
  rw [projP_idem hR₀, projP_idem hR₀, add_sub_cancel]

/-- `B(f₀) = 1`. -/
theorem opB_self (hR₀ : ∀ e, g₀ (R₀ (g₀ e)) = g₀ e) (hS₀ : ∀ x, f₀ (S₀ (f₀ x)) = f₀ x)
    (hex : ∀ x, f₀ x = 0 → ∃ e, g₀ e = x) :
    opB (g₀.comp R₀) S₀ f₀ = ContinuousLinearMap.id ℂ E₁ := by
  ext x
  rw [opB_apply]
  show (S₀ (f₀ x) - g₀ (R₀ (S₀ (f₀ x)))) + g₀ (R₀ x) = x
  rw [one_sub_P_S₀_f₀ hR₀ hS₀ hex, sub_add_cancel]

/-- `C(f₀) = 1`. -/
theorem opC_self (hc₀ : ∀ e, f₀ (g₀ e) = 0) :
    opC (g₀.comp R₀) (f₀.comp S₀) S₀ f₀ = ContinuousLinearMap.id ℂ E₀ := by
  ext y
  rw [opC_apply]
  show f₀ (S₀ y - g₀ (R₀ (S₀ y))) + (y - f₀ (S₀ y)) = y
  rw [map_sub, hc₀, sub_zero, add_sub_cancel]

/-! ## Exactness and directness where the comparison operators are invertible -/

/-- **Exactness and generalized inverses at every parameter where `A`, `B`, `C` are invertible.** -/
theorem directExact3_of_isInvertible (hR₀ : ∀ e, g₀ (R₀ (g₀ e)) = g₀ e)
    (hS₀ : ∀ x, f₀ (S₀ (f₀ x)) = f₀ x) (hex : ∀ x, f₀ x = 0 → ∃ e, g₀ e = x)
    {g : E₂ →L[ℂ] E₁} {f : E₁ →L[ℂ] E₀} (hc : ∀ e, f (g e) = 0)
    (hA : (opA (g₀.comp R₀) R₀ g).IsInvertible) (hB : (opB (g₀.comp R₀) S₀ f).IsInvertible)
    (hC : (opC (g₀.comp R₀) (f₀.comp S₀) S₀ f).IsInvertible) :
    (∀ x, f x = 0 → ∃ e, g e = x) ∧ (∃ R : E₁ →L[ℂ] E₂, ∀ e, g (R (g e)) = g e) ∧
      ∃ S : E₀ →L[ℂ] E₁, ∀ x, f (S (f x)) = f x := by
  set P : E₁ →L[ℂ] E₁ := g₀.comp R₀ with hPdef
  have hP : ∀ x, P x = g₀ (R₀ x) := fun _ => rfl
  have hPP : ∀ x, P (P x) = P x := fun x => projP_idem hR₀ x
  -- (i) `ker f ∩ ker P = 0`
  have hinj : ∀ x, f x = 0 → P x = 0 → x = 0 := by
    intro x hfx hPx
    apply hB.injective
    rw [opB_apply, hfx, map_zero, map_zero, sub_zero, hPx, add_zero, map_zero]
  -- (ii) `A` commutes with `P`
  set A := opA P R₀ g with hAdef
  have hAP : ∀ x, A (P x) = P (A x) := by
    intro x
    simp only [hAdef, opA_apply, map_add, map_sub, hPP, sub_self, add_zero]
  have hAiP : ∀ y, A.inverse (P y) = P (A.inverse y) := by
    intro y
    apply hA.injective
    rw [hA.self_apply_inverse, hAP, hA.self_apply_inverse]
  set R : E₁ →L[ℂ] E₂ := R₀.comp (P.comp (A.inverse.comp P)) with hRdef
  have hPgR : ∀ x, P (g (R x)) = P x := by
    intro x
    set z := A.inverse (P x) with hz
    have hzP : P z = z := by rw [hz, ← hAiP, hPP]
    have hAz : A z = P x := hA.self_apply_inverse _
    have hRx : R x = R₀ (P z) := by
      show R₀ (P (A.inverse (P x))) = R₀ (P z)
      rw [← hz]
    rw [hRx, ← hAz, hAdef, opA_apply, hzP, sub_self, add_zero]
  -- exactness, and `g R = 1` on `ker f`
  have hgR : ∀ x, f x = 0 → g (R x) = x := by
    intro x hx
    have h1 : f (g (R x) - x) = 0 := by rw [map_sub, hc, hx, sub_self]
    have h2 : P (g (R x) - x) = 0 := by rw [map_sub, hPgR, sub_self]
    exact sub_eq_zero.mp (hinj _ h1 h2)
  refine ⟨fun x hx => ⟨R x, hgR x hx⟩, ⟨R, fun e => hgR _ (hc e)⟩, ?_⟩
  -- the generalized inverse of `f`
  set C := opC P (f₀.comp S₀) S₀ f with hCdef
  -- `f (1 − P) w = C (f₀ w)`
  have hfC : ∀ w, f (w - P w) = C (f₀ w) := by
    intro w
    have h1 := one_sub_P_S₀_f₀ hR₀ hS₀ hex w
    have h2 : C (f₀ w) = f (S₀ (f₀ w) - g₀ (R₀ (S₀ (f₀ w)))) + (f₀ w - f₀ (S₀ (f₀ w))) := rfl
    rw [h2, hS₀, sub_self, add_zero, h1]
    rfl
  -- `f = C f₀ (1 − g R)`
  have hfx : ∀ x, f x = C (f₀ (x - g (R x))) := by
    intro x
    rw [← hfC, map_sub P x (g (R x)), hPgR, sub_self, sub_zero, map_sub, hc, sub_zero]
  refine ⟨((ContinuousLinearMap.id ℂ E₁ - P).comp S₀).comp C.inverse, fun x => ?_⟩
  show f (S₀ (C.inverse (f x)) - P (S₀ (C.inverse (f x)))) = f x
  rw [hfC, hfx x, hC.inverse_apply_self, hS₀]

/-! ## Persistence for continuous families -/

/-- The invertible operators form a neighbourhood of the identity. -/
theorem isInvertible_mem_nhds_id {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] :
    {T : E →L[ℂ] E | T.IsInvertible} ∈ 𝓝 (ContinuousLinearMap.id ℂ E) := by
  have h : range ((↑) : (E ≃L[ℂ] E) → E →L[ℂ] E) ∈ 𝓝 (ContinuousLinearMap.id ℂ E) := by
    rw [← ContinuousLinearEquiv.coe_refl]
    exact ContinuousLinearEquiv.nhds _
  filter_upwards [h] with T ⟨e, he⟩
  exact ⟨e, he⟩

/-- **Persistence of direct exactness of a 3-term family** (Douady §2 Prop. 3, §8 Prop. 2 (b)):
families `g(s)`, `f(s)` continuous at `s₀`, exact at `s₀` with generalized inverses `R₀`, `S₀`; then
near `s₀`, wherever `f(s) g(s) = 0`, the start is exact and both maps have generalized inverses. -/
theorem eventually_directExact3 [CompleteSpace E₁] [CompleteSpace E₀] {X : Type*}
    [TopologicalSpace X] {g : X → E₂ →L[ℂ] E₁} {f : X → E₁ →L[ℂ] E₀} {s₀ : X}
    (hg : ContinuousAt g s₀) (hf : ContinuousAt f s₀) {R₀ : E₁ →L[ℂ] E₂} {S₀ : E₀ →L[ℂ] E₁}
    (hR₀ : ∀ e, g s₀ (R₀ (g s₀ e)) = g s₀ e) (hS₀ : ∀ x, f s₀ (S₀ (f s₀ x)) = f s₀ x)
    (hex : ∀ x, f s₀ x = 0 → ∃ e, g s₀ e = x) (hc₀ : ∀ e, f s₀ (g s₀ e) = 0) :
    ∀ᶠ s in 𝓝 s₀, (∀ e, f s (g s e) = 0) →
      (∀ x, f s x = 0 → ∃ e, g s e = x) ∧ (∃ R : E₁ →L[ℂ] E₂, ∀ e, g s (R (g s e)) = g s e) ∧
        ∃ S : E₀ →L[ℂ] E₁, ∀ x, f s (S (f s x)) = f s x := by
  have hAc : ContinuousAt (fun s => opA ((g s₀).comp R₀) R₀ (g s)) s₀ :=
    (continuousAt_const.clm_comp (hg.clm_comp continuousAt_const)).add continuousAt_const
  have hBc : ContinuousAt (fun s => opB ((g s₀).comp R₀) S₀ (f s)) s₀ :=
    (continuousAt_const.clm_comp (continuousAt_const.clm_comp hf)).add continuousAt_const
  have hCc : ContinuousAt (fun s => opC ((g s₀).comp R₀) ((f s₀).comp S₀) S₀ (f s)) s₀ :=
    (hf.clm_comp continuousAt_const).add continuousAt_const
  have hA := hAc (show {T : E₁ →L[ℂ] E₁ | T.IsInvertible} ∈ 𝓝 (opA ((g s₀).comp R₀) R₀ (g s₀)) by
    rw [opA_self hR₀]; exact isInvertible_mem_nhds_id)
  have hB := hBc (show {T : E₁ →L[ℂ] E₁ | T.IsInvertible} ∈ 𝓝 (opB ((g s₀).comp R₀) S₀ (f s₀)) by
    rw [opB_self hR₀ hS₀ hex]; exact isInvertible_mem_nhds_id)
  have hC := hCc (show {T : E₀ →L[ℂ] E₀ | T.IsInvertible} ∈
      𝓝 (opC ((g s₀).comp R₀) ((f s₀).comp S₀) S₀ (f s₀)) by
    rw [opC_self hc₀]; exact isInvertible_mem_nhds_id)
  filter_upwards [hA, hB, hC] with s hsA hsB hsC hcs
  exact directExact3_of_isInvertible hR₀ hS₀ hex hcs hsA hsB hsC

end Abstract

/-! ## Matrix starts over a normed algebra -/

section Matrix
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R]
  {ι₂ ι₁ ι₀ : Type*} [Fintype ι₂] [Fintype ι₁] [Fintype ι₀]

/-- **Direct exactness of a family of matrix starts persists** (Douady §8, Scholie and Prop. 2 (b),
Banach core): matrices `g(s)`, `f(s)` over a complete normed algebra, continuous at `s₀`, with
`f(s) g(s) = 0` near `s₀` and `DirectExact (g s₀) (f s₀)`, are direct exact near `s₀`. -/
theorem directExact_eventually [CompleteSpace R] {X : Type*} [TopologicalSpace X]
    {g : X → ι₁ → ι₂ → R} {f : X → ι₀ → ι₁ → R} {s₀ : X} (hg : ContinuousAt g s₀)
    (hf : ContinuousAt f s₀) (hcomp : ∀ᶠ s in 𝓝 s₀, ∀ i k, ∑ j, f s i j * g s j k = 0)
    (h₀ : DirectExact (g s₀) (f s₀)) : ∀ᶠ s in 𝓝 s₀, DirectExact (g s) (f s) := by
  have hgo : ContinuousAt (fun s => matrixOperator (g s)) s₀ :=
    (matrixOperatorCLM (R := R) (p := ι₂) (q := ι₁)).continuous.continuousAt.comp hg
  have hfo : ContinuousAt (fun s => matrixOperator (f s)) s₀ :=
    (matrixOperatorCLM (R := R) (p := ι₁) (q := ι₀)).continuous.continuousAt.comp hf
  obtain ⟨S₀, hS₀⟩ := h₀.exists_generalizedInverse_f
  obtain ⟨R₀, hR₀⟩ := h₀.exists_generalizedInverse_g
  have hc₀ := matrixOperator_comp_apply (g s₀) (f s₀) h₀.comp
  filter_upwards [eventually_directExact3 hgo hfo hR₀ hS₀ h₀.exact hc₀, hcomp] with s hs hcs
  obtain ⟨hex, ⟨R', hR'⟩, ⟨S, hS⟩⟩ := hs (matrixOperator_comp_apply (g s) (f s) hcs)
  exact ⟨hcs, hex, closedComplemented_ker_of_generalizedInverse _ S hS,
    closedComplemented_range_of_generalizedInverse _ S hS,
    closedComplemented_ker_of_generalizedInverse _ R' hR'⟩

omit [Fintype ι₀] [Fintype ι₁] in
/-- `matrixOperator (g X) = matrixOperator g ∘ matrixOperator X`. -/
theorem matrixOperator_mul_apply {κ : Type*} [Fintype κ] (g : ι₁ → ι₂ → R) (X : ι₂ → κ → R)
    (d : ι₁ → κ → R) (hX : ∀ j k, d j k = ∑ l, g j l * X l k) (t : κ → R) :
    matrixOperator d t = matrixOperator g (matrixOperator X t) := by
  funext j
  simp only [matrixOperator_apply, hX, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

omit [Fintype ι₀] in
/-- **Independence of the second matrix of a direct exact start**: if `(d₁, f)` is direct exact and
`d₁ = g X` with `f g = 0`, then `(g, f)` is direct exact. -/
theorem directExact_of_factor [CompleteSpace R] {κ : Type*} [Fintype κ] {d₁ : ι₁ → κ → R}
    {f : ι₀ → ι₁ → R} {g : ι₁ → ι₂ → R} (h : DirectExact d₁ f) (X : ι₂ → κ → R)
    (hX : ∀ j k, d₁ j k = ∑ l, g j l * X l k) (hfg : ∀ i k, ∑ j, f i j * g j k = 0) :
    DirectExact g f := by
  obtain ⟨S, hS⟩ := h.exists_rightInverse
  refine ⟨hfg, fun x hx => ?_, h.kerf, h.imf, ?_⟩
  · obtain ⟨t, ht⟩ := h.exact x hx
    exact ⟨matrixOperator X t, by rw [← matrixOperator_mul_apply g X d₁ hX, ht]⟩
  · refine closedComplemented_ker_of_generalizedInverse _ ((matrixOperator X).comp S) fun e => ?_
    show matrixOperator g (matrixOperator X (S (matrixOperator g e))) = matrixOperator g e
    rw [← matrixOperator_mul_apply g X d₁ hX]
    exact hS _ (matrixOperator_comp_apply g f hfg e)

end Matrix

end
end Hironaka.HironakaG10LocDirectPersistence
