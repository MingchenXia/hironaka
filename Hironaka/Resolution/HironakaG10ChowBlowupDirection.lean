import Hironaka.Blowup.BlowupLocalSurjectivity
import Hironaka.Blowup.BlowupStrictSubmanifold

/-!
# Points of a blowup are determined by their base point and their normal direction

Route step N2 of the global half of flattening
(`work/hironaka-resume-20261111/G10C/GLOBAL-FLATTENING-ROUTE.md` §3.2 item 4): pair-injectivity of
the one-step strict transform.

Let `π : Z → M` be a blowup along `C` (`IsBlowupAlong`, a universal property) and let `C` be flattened
near `y₀` by `Φ ∘ e` onto `ℂᵏ × 0`.  Near a point `z` over the flattening domain the flattening
coordinates pulled back to `Z` factor as `(Φ ∘ e ∘ π)ᵢ = αᵢ h` (`i ≥ k`)
(`BlowupLocalSurjectivity.exists_coeff_ne_zero`).

* `monomialLift_directionCoord`: for ANY pivot `j ≥ k` with `αⱼ(z) ≠ 0` (not only a maximal one),
  `z` is the image under the lift `ℓⱼ` of the `j`-th monomial chart of the point with coordinates
  `αᵢ(z)/αⱼ(z)` (`i ≥ k`, `i ≠ j`) and `(Φ ∘ e ∘ π)ᵢ(z)` otherwise.
* `eq_of_proportional_coeff`: two points over the same base point whose coefficient vectors are
  proportional coincide (the exceptional fibre embeds into the projectivized normal space).
* `limit_proportional`: proportionality of two vector-valued functions on a dense set passes to the
  limit, given an inverse relation that keeps the limit of the second one nonzero.
* `eq_of_pair_value_core`: the value-level core of pair-injectivity.  Two points `a, c` of the
  geometric strict transform `S' = closure (π'⁻¹ (W' ∖ C'))` of a carrier `W'` in a second blowup
  `π' : Z' → M'` over the same point `w₀`, sent by a map `Q : S' → Z` (continuous at `a, c`, with
  `π ∘ Q = φ ∘ π'`) to the same point, coincide, provided the flattening coordinates of `C'` at `w₀`
  and the pulled-back flattening coordinates of `C` generate the same ideal along `W'`
  (explicit matrices `A'`, `A` of functions continuous at `w₀`).  This is the situation of the strict
  transform `Bl_{f*B} Y → Bl_B X ×_X Y` of the global flattening algorithm, chart by chart.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG10ChowBlowupDirection

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupFlatCoordinates BlowupMonomialCharts BlowupLocalSurjectivity BlowupStrictSubmanifold

noncomputable section

/-! ### The monomial-chart coordinates of a point, for an arbitrary pivot -/

section Direction

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

instance (O : TopologicalSpace.Opens Z) : IsComplexManifold n O where

variable {C : Set M} {π : Z → M} {y₀ : M}

/-- The coordinates in the `j`-th monomial chart determined by a coefficient vector `α` at `z`. -/
def directionCoord (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y₀ y₀))
    (k : ℕ) (j : Fin n) (α : Fin n → Z → ℂ) (π : Z → M) (z : Z) : ComplexModel n :=
  WithLp.toLp 2 fun i => if k ≤ i.1 ∧ i ≠ j then α i z * (α j z)⁻¹ else flatCoord Φ i (π z)

variable {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y₀ y₀)} {k : ℕ}

/-- **Local inverse of a monomial lift, for any pivot with a nonzero coefficient.**  A variant of
`BlowupLocalSurjectivity.exists_monomialLocalInverse` in which the coefficient vector and the pivot
are given. -/
theorem monomialLift_directionCoord (hπ : IsBlowupAlong n C π)
    {z : Z} (hz : π z ∈ flatDomain Φ) (α : Fin n → Z → ℂ) (hα : ∀ i, HolomorphicAt n (α i) z)
    (h : Z → ℂ)
    (hαev : ∀ᶠ z' in 𝓝 z, ∀ i : Fin n, k ≤ i.1 → flatCoord Φ i (π z') = α i z' * h z')
    {j : Fin n} (hj : k ≤ j.1) (hαj : α j z ≠ 0) :
    ∃ hw : directionCoord Φ k j α π z ∈ monomialDomain Φ k j,
      ∀ ℓ : LiftedOpen.{u} (monomialDomain Φ k j) → Z,
        ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ℓ →
          π ∘ ℓ = monomialChart Φ k j →
            ℓ (LiftedOpen.mk _ (directionCoord Φ k j α π z) hw) = z := by
  classical
  have hπs : ∀ z', ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π z' :=
    fun z' => hπ.contMDiff z'
  set wc : Fin n → Z → ℂ := fun i z' =>
    if k ≤ i.1 ∧ i ≠ j then α i z' * (α j z')⁻¹ else flatCoord Φ i (π z') with hwc_def
  set wmap : Z → ComplexModel n := fun z' => WithLp.toLp 2 fun i => wc i z' with hwmap_def
  have hwmap_eq : ∀ z', wmap z' = directionCoord Φ k j α π z' := fun _ => rfl
  have hwc : ∀ i, ∀ z', α j z' ≠ 0 → π z' ∈ flatDomain Φ → HolomorphicAt n (α i) z' →
      HolomorphicAt n (α j) z' → HolomorphicAt n (wc i) z' := by
    intro i z' h0 hz' hi hj'
    simp only [hwc_def]
    split_ifs
    · exact hi.mul (HolomorphicAt.inv hj' h0)
    · exact (holomorphicAt_flatCoord Φ i hz').comp_contMDiff (Eventually.of_forall hπs)
  set P : Z → Prop := fun z' => α j z' ≠ 0 ∧ π z' ∈ flatDomain Φ ∧
    (∀ i : Fin n, k ≤ i.1 → flatCoord Φ i (π z') = α i z' * h z') ∧
    ∀ i, HolomorphicAt n (wc i) z' with hP_def
  have hP : ∀ᶠ z' in 𝓝 z, P z' := by
    have h1 := (hα j).continuousAt.eventually (isOpen_ne.mem_nhds hαj)
    have h2 := hπ.contMDiff.continuous.continuousAt.eventually
      ((isOpen_flatDomain Φ).mem_nhds hz)
    have h3 : ∀ᶠ z' in 𝓝 z, ∀ i, HolomorphicAt n (α i) z' :=
      eventually_all.2 fun i => (hα i).eventually
    filter_upwards [h1, h2, hαev, h3] with z' h1' h2' h3' h4'
    exact ⟨h1', h2', h3', fun i => hwc i z' h1' h2' (h4' i) (h4' j)⟩
  have hkey : ∀ z', P z' →
      monomial k j (wmap z') = Φ.toFun (chartAt (ComplexModel n) y₀ (π z')) := by
    intro z' hz'
    ext i
    simp only [monomial_apply, hwmap_def, hwc_def]
    by_cases hij : k ≤ i.1 ∧ i ≠ j
    · rw [if_pos hij, if_pos hij, if_neg (by simp), hz'.2.2.1 j hj,
        show (Φ.toFun (chartAt (ComplexModel n) y₀ (π z'))) i = flatCoord Φ i (π z') from rfl,
        hz'.2.2.1 i hij.1]
      field_simp [hz'.1]
    · rw [if_neg hij, if_neg hij]
      rfl
  set O : TopologicalSpace.Opens Z := ⟨interior {z' | P z'}, isOpen_interior⟩
  have hzO : z ∈ O := mem_interior_iff_mem_nhds.mpr hP
  have hPO : ∀ x : O, P x.1 := fun x =>
    (interior_subset (s := {z' | P z'}) (x.2 : x.1 ∈ interior {z' | P z'}) : x.1 ∈ {z' | P z'})
  have hwmapmem : ∀ x : O, wmap x.1 ∈ monomialDomain Φ k j := fun x => by
    show monomial k j (wmap x.1) ∈ Φ.target
    rw [hkey _ (hPO x)]
    exact Φ.mapsTo_toFun (hPO x).2.1.2
  set wmap' : O → LiftedOpen.{u} (monomialDomain Φ k j) := fun x =>
    LiftedOpen.mk _ (wmap x.1) (hwmapmem x)
  have hwmapsmooth : ∀ z', P z' →
      ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ wmap z' := by
    intro z' hz'
    have hpi : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, Fin n → ℂ) ∞ (fun z'' i => wc i z'') z' :=
      contMDiffAt_pi_space.2 fun i =>
        contMDiffAt_of_eventually_mdifferentiableAt ((hz'.2.2.2 i).mono fun _ h' => h')
    exact (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm.toContinuousLinearMap
      |>.contMDiff.contMDiffAt.comp z' hpi
  have hwmap'smooth : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ wmap' := fun x =>
    LiftedOpen.contMDiffAt_of_toModel _
      (contMDiffAt_subtype_iff.mpr (hwmapsmooth x.1 (hPO x)) :
        ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (fun x : O => wmap x.1) x)
  have huniq := hπ.2.2.2.2 n O (π ∘ Subtype.val) (hπ.contMDiff.comp contMDiff_subtype_val)
    (IsInvertible.pullback_comp_val O hπ.2.2.2.1)
  refine ⟨hwmapmem ⟨z, hzO⟩, fun ℓ hℓs hℓπ => ?_⟩
  have hlift : π ∘ (ℓ ∘ wmap') = π ∘ Subtype.val := by
    funext x
    have := congrFun hℓπ (wmap' x)
    simp only [Function.comp_apply] at this ⊢
    rw [this]
    show (chartAt (ComplexModel n) y₀).symm (Φ.invFun (monomial k j (wmap x.1))) = π x.1
    rw [hkey _ (hPO x)]
    exact flatInverse_flat Φ (hPO x).2.1
  have heq := huniq.unique ⟨hℓs.comp hwmap'smooth, hlift⟩ ⟨contMDiff_subtype_val, rfl⟩
  exact congrFun heq ⟨z, hzO⟩

/-- **The exceptional fibre embeds into the projectivized normal space.**  Two points over the same
base point whose coefficient vectors (with respect to the same flattening coordinates) are
proportional coincide. -/
theorem eq_of_proportional_coeff (hπ : IsBlowupAlong n C π)
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) y₀).target)
    (hflat : ∀ {y : M}, y ∈ (chartAt (ComplexModel n) y₀).source →
      chartAt (ComplexModel n) y₀ y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) y₀ y) ∈ complexCoordinatePlane n k))
    {z₁ z₂ : Z} (hz : π z₁ = π z₂) (hz₁ : π z₁ ∈ flatDomain Φ)
    (α₁ α₂ : Fin n → Z → ℂ) (hα₁ : ∀ i, HolomorphicAt n (α₁ i) z₁)
    (hα₂ : ∀ i, HolomorphicAt n (α₂ i) z₂) (h₁ h₂ : Z → ℂ)
    (hev₁ : ∀ᶠ z' in 𝓝 z₁, ∀ i : Fin n, k ≤ i.1 → flatCoord Φ i (π z') = α₁ i z' * h₁ z')
    (hev₂ : ∀ᶠ z' in 𝓝 z₂, ∀ i : Fin n, k ≤ i.1 → flatCoord Φ i (π z') = α₂ i z' * h₂ z')
    (c : ℂ) (hprop : ∀ i : Fin n, k ≤ i.1 → α₁ i z₁ = c * α₂ i z₂)
    {j : Fin n} (hj : k ≤ j.1) (hj₁ : α₁ j z₁ ≠ 0) : z₁ = z₂ := by
  have hc : c ≠ 0 := by
    rintro rfl
    exact hj₁ (by rw [hprop j hj, zero_mul])
  have hj₂ : α₂ j z₂ ≠ 0 := by
    intro h0
    exact hj₁ (by rw [hprop j hj, h0, mul_zero])
  have hz₂ : π z₂ ∈ flatDomain Φ := hz ▸ hz₁
  obtain ⟨ℓ, ⟨hℓs, hℓπ⟩, -⟩ := existsUnique_monomialLift hπ hΦsrc hflat hj
  obtain ⟨hw₁, H₁⟩ := monomialLift_directionCoord hπ hz₁ α₁ hα₁ h₁ hev₁ hj hj₁
  obtain ⟨hw₂, H₂⟩ := monomialLift_directionCoord hπ hz₂ α₂ hα₂ h₂ hev₂ hj hj₂
  have hv : directionCoord Φ k j α₁ π z₁ = directionCoord Φ k j α₂ π z₂ := by
    ext i
    simp only [directionCoord]
    by_cases hij : k ≤ i.1 ∧ i ≠ j
    · simp only [if_pos hij]
      rw [hprop i hij.1, hprop j hj]
      field_simp
    · simp only [if_neg hij]
      rw [hz]
  rw [← H₁ ℓ hℓs hℓπ, ← H₂ ℓ hℓs hℓπ]
  congr 1
  exact Subtype.ext (congrArg ULift.up hv)

end Direction

/-! ### Proportionality passes to limits -/

section Limit

/-- Two functions continuous at `b` that agree on a set accumulating at `b` agree at `b`. -/
theorem eq_at_of_eventually_on {S : Type*} [TopologicalSpace S] {D : Set S} {b : S}
    (hb : b ∈ closure D) {f g : S → ℂ} (hf : ContinuousAt f b) (hg : ContinuousAt g b)
    (hfg : ∀ᶠ z in 𝓝 b, z ∈ D → f z = g z) : f b = g b := by
  have hfr : ∃ᶠ z in 𝓝 b, z ∈ D := mem_closure_iff_frequently.mp hb
  exact tendsto_nhds_unique_of_frequently_eq hf hg (hfr.mp (hfg.mono fun z h hz => h hz))

/-- **Proportionality on a dense set passes to the limit.**  If `u(z) ∥ v(z)` on `D` near `b`,
`a(z) = A(z) v(z)` on `D` near `b` (so `v(b) ≠ 0` as soon as `a(b) ≠ 0`), and `u(b) ≠ 0`, then
`u(b) = c v(b)` with `c ≠ 0`.  The index predicates `P`, `R` select the normal coordinates. -/
theorem limit_proportional {S : Type*} [TopologicalSpace S] {ι ι' : Type*} [Fintype ι']
    {D : Set S} {b : S} (hb : b ∈ closure D) (P : ι' → Prop) (R : ι → Prop)
    (u v : ι' → S → ℂ) (a : ι → S → ℂ) (A : ι → ι' → S → ℂ)
    (hu : ∀ t, ContinuousAt (u t) b) (hv : ∀ t, ContinuousAt (v t) b)
    (ha : ∀ s, ContinuousAt (a s) b) (hA : ∀ s t, ContinuousAt (A s t) b)
    (hA0 : ∀ s t, ¬ P t → A s t b = 0)
    (hpar : ∀ᶠ z in 𝓝 b, z ∈ D → ∃ c : ℂ, ∀ t, P t → u t z = c * v t z)
    (hinv : ∀ᶠ z in 𝓝 b, z ∈ D → ∀ s, R s → a s z = ∑ t, A s t z * v t z)
    (hu0 : ∃ t, P t ∧ u t b ≠ 0) (ha0 : ∃ s, R s ∧ a s b ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ t, P t → u t b = c * v t b := by
  classical
  -- the minors vanish at `b`
  have hminor : ∀ t r, P t → P r → u t b * v r b = u r b * v t b := by
    intro t r ht hr
    refine eq_at_of_eventually_on hb ((hu t).mul (hv r)) ((hu r).mul (hv t)) ?_
    filter_upwards [hpar] with z hz hzD
    obtain ⟨c, hc⟩ := hz hzD
    simp only [Pi.mul_apply]
    rw [hc t ht, hc r hr]
    ring
  -- the inverse relation at `b`
  have hinvb : ∀ s, R s → a s b = ∑ t, A s t b * v t b := by
    intro s hs
    have hsum : ContinuousAt (fun z => ∑ t, A s t z * v t z) b :=
      tendsto_finsetSum Finset.univ fun t _ => (hA s t).mul (hv t)
    exact eq_at_of_eventually_on hb (ha s) hsum (hinv.mono fun z hz hzD => hz hzD s hs)
  -- `v(b) ≠ 0` on a normal coordinate
  obtain ⟨s, hs, has⟩ := ha0
  obtain ⟨r, -, hr⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hinvb s hs ▸ has)
  have hAr : A s r b ≠ 0 := left_ne_zero_of_mul hr
  have hvr : v r b ≠ 0 := right_ne_zero_of_mul hr
  have hPr : P r := by
    by_contra hPr
    exact hAr (hA0 s r hPr)
  refine ⟨u r b / v r b, ?_, fun t ht => ?_⟩
  · intro hc0
    obtain ⟨t, ht, hut⟩ := hu0
    have hur : u r b = 0 := by
      rcases div_eq_zero_iff.mp hc0 with h | h
      · exact h
      · exact absurd h hvr
    have := hminor t r ht hPr
    rw [hur, zero_mul] at this
    exact hut ((mul_eq_zero.mp this).resolve_right hvr)
  · have := hminor t r ht hPr
    field_simp
    linear_combination this

end Limit

/-! ### The value-level core of pair-injectivity -/

section Core

variable {n n' : ℕ}
  {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n') M']
  [IsComplexManifold n' M']
  {Z' : Type u} [TopologicalSpace Z'] [ChartedSpace (ComplexModel n') Z']
  [IsComplexManifold n' Z']
  {C : Set M} {π : Z → M} {C' W' : Set M'} {π' : Z' → M'}

omit [TopologicalSpace M'] in
/-- Every point of a geometric strict transform is a limit of points off the centre. -/
theorem mem_closure_offCentre (b : geoStrictTransform π' C' W') :
    b ∈ closure {z : geoStrictTransform π' C' W' | π' z.val ∉ C'} := by
  rw [closure_subtype]
  refine closure_mono ?_ b.property
  intro z hz
  exact ⟨⟨z, subset_closure hz⟩, hz.2, rfl⟩

omit [IsComplexManifold n M] [IsComplexManifold n Z] in
/-- **Limit proportionality at one point.**  At a point `b` of the strict transform over `w₀`, the
coefficient vector of `b` (with respect to the flattening coordinates of `C'` at `w₀`) is a nonzero
multiple of `A'(w₀) α(Q b)`, where `α` is the coefficient vector of `Q b` on the other side. -/
theorem proportional_at (hπ' : IsBlowupAlong n' C' π') (hW' : IsClosed W')
    {y₀ : M} {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y₀ y₀)} {k : ℕ}
    {w₀ : M'} {Φ' : LocalHolomorphicEquivAt (n := n') (chartAt (ComplexModel n') w₀ w₀)}
    {k' : ℕ} (hΦ'src : Φ'.source ⊆ (chartAt (ComplexModel n') w₀).target)
    (hflat' : ∀ {y : M'}, y ∈ (chartAt (ComplexModel n') w₀).source →
      chartAt (ComplexModel n') w₀ y ∈ Φ'.source →
        (y ∈ C' ↔ Φ'.toFun (chartAt (ComplexModel n') w₀ y) ∈ complexCoordinatePlane n' k'))
    (Q : geoStrictTransform π' C' W' → Z) (φ : M' → M)
    (A' : Fin n' → Fin n → M' → ℂ) (A : Fin n → Fin n' → M' → ℂ)
    (hA'0 : ∀ t s, s.1 < k → A' t s = 0) (hA0 : ∀ s t, t.1 < k' → A s t = 0)
    (hA'c : ∀ t s, ContinuousAt (A' t s) w₀) (hAc : ∀ s t, ContinuousAt (A s t) w₀)
    (hrel' : ∀ᶠ w in 𝓝 w₀, w ∈ W' → ∀ t : Fin n', k' ≤ t.1 →
      flatCoord Φ' t w = ∑ s, A' t s w * flatCoord Φ s (φ w))
    (hrel : ∀ᶠ w in 𝓝 w₀, w ∈ W' → ∀ s : Fin n, k ≤ s.1 →
      flatCoord Φ s (φ w) = ∑ t, A s t w * flatCoord Φ' t w)
    (b : geoStrictTransform π' C' W') (hb : π' b.val = w₀) (hQb : ContinuousAt Q b)
    (hφb : ∀ᶠ z in 𝓝 b, π (Q z) = φ (π' z.val))
    (α : Fin n → Z → ℂ) (hα : ∀ s, HolomorphicAt n (α s) (Q b)) (h : Z → ℂ)
    (hev : ∀ᶠ x in 𝓝 (Q b), ∀ s : Fin n, k ≤ s.1 → flatCoord Φ s (π x) = α s x * h x)
    (hs₀ : ∃ s : Fin n, k ≤ s.1 ∧ α s (Q b) ≠ 0) :
    ∃ (α' : Fin n' → Z' → ℂ) (_ : ∀ t, HolomorphicAt n' (α' t) b.val) (h' : Z' → ℂ)
      (_ : ∀ᶠ z' in 𝓝 b.val, ∀ t : Fin n', k' ≤ t.1 → flatCoord Φ' t (π' z') = α' t z' * h' z')
      (_ : ∃ t : Fin n', k' ≤ t.1 ∧ α' t b.val ≠ 0) (c : ℂ), c ≠ 0 ∧
      ∀ t : Fin n', k' ≤ t.1 → α' t b.val = c * ∑ s, A' t s w₀ * α s (Q b) := by
  classical
  have hbflat : π' b.val ∈ flatDomain Φ' := hb ▸ mem_flatDomain_self Φ'
  obtain ⟨α', hα', h', hev', t₀, ht₀, hαt₀⟩ := exists_coeff_ne_zero hπ' hΦ'src hflat' hbflat
  refine ⟨α', hα', h', hev', ⟨t₀, ht₀, hαt₀⟩, ?_⟩
  -- the maps into the two bases, as functions on the strict transform
  have hval : Tendsto (Subtype.val : geoStrictTransform π' C' W' → Z') (𝓝 b) (𝓝 b.val) :=
    continuous_subtype_val.continuousAt
  have hπval : Tendsto (fun z : geoStrictTransform π' C' W' => π' z.val) (𝓝 b) (𝓝 w₀) := by
    have := (hπ'.contMDiff.continuous.continuousAt (x := b.val)).tendsto.comp hval
    rwa [hb] at this
  have hW'mem : ∀ z : geoStrictTransform π' C' W', π' z.val ∈ W' := fun z =>
    geoStrictTransform_subset_preimage hπ'.contMDiff.continuous hW' z.property
  set v : Fin n' → geoStrictTransform π' C' W' → ℂ :=
    fun t z => ∑ s, A' t s (π' z.val) * α s (Q z) with hv_def
  -- continuity at `b`
  have hcA' : ∀ t s, ContinuousAt (fun z : geoStrictTransform π' C' W' => A' t s (π' z.val)) b :=
    fun t s => by
      show Tendsto _ (𝓝 b) (𝓝 (A' t s (π' b.val)))
      rw [hb]
      exact (hA'c t s).tendsto.comp hπval
  have hcA : ∀ s t, ContinuousAt (fun z : geoStrictTransform π' C' W' => A s t (π' z.val)) b :=
    fun s t => by
      show Tendsto _ (𝓝 b) (𝓝 (A s t (π' b.val)))
      rw [hb]
      exact (hAc s t).tendsto.comp hπval
  have hcα : ∀ s, ContinuousAt (fun z => α s (Q z)) b := fun s =>
    (hα s).continuousAt.comp hQb
  have hcv : ∀ t, ContinuousAt (v t) b := fun t =>
    tendsto_finsetSum Finset.univ fun s _ => (hcA' t s).mul (hcα s)
  have hcu : ∀ t, ContinuousAt (fun z : geoStrictTransform π' C' W' => α' t z.val) b :=
    fun t => (hα' t).continuousAt.comp hval
  -- the eventual identities near `b`
  have E1 := hval.eventually hev'
  have E2 := hQb.eventually hev
  have E3 := hπval.eventually hrel'
  have E4 := hπval.eventually hrel
  have E6 : ∀ᶠ z in 𝓝 b, π' (Subtype.val z) ∈ flatDomain Φ' :=
    hπval.eventually ((isOpen_flatDomain Φ').mem_nhds (mem_flatDomain_self Φ'))
  -- the key identity `α' h' = (A' α∘Q) h∘Q`
  have hkey : ∀ᶠ z in 𝓝 b, ∀ t : Fin n', k' ≤ t.1 → α' t z.val * h' z.val = v t z * h (Q z) := by
    filter_upwards [E1, E2, E3, hφb] with z e1 e2 e3 e5 t ht
    rw [← e1 t ht, e3 (hW'mem z) t ht, hv_def]
    simp only
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases hs : k ≤ s.1
    · rw [← e5, e2 s hs, mul_assoc]
    · rw [hA'0 t s (by omega)]
      simp
  -- off the centre both generators are nonzero
  have hnz : ∀ᶠ z in 𝓝 b, π' z.val ∉ C' → h' z.val ≠ 0 ∧ h (Q z) ≠ 0 := by
    filter_upwards [E1, E2, E3, hφb, E6] with z e1 e2 e3 e5 e6 hzC
    have hplane : ¬ Φ'.toFun (chartAt (ComplexModel n') w₀ (π' z.val)) ∈
        complexCoordinatePlane n' k' := fun hp => hzC ((hflat' e6.1 e6.2).mpr hp)
    simp only [complexCoordinatePlane, mem_ofPred_eq, not_forall] at hplane
    obtain ⟨t, ht, htne⟩ := hplane
    have htne' : flatCoord Φ' t (π' z.val) ≠ 0 := htne
    refine ⟨fun h0 => htne' (by rw [e1 t ht, h0, mul_zero]), fun h0 => htne' ?_⟩
    rw [e3 (hW'mem z) t ht]
    refine Finset.sum_eq_zero fun s _ => ?_
    by_cases hs : k ≤ s.1
    · rw [← e5, e2 s hs, h0, mul_zero, mul_zero]
    · rw [hA'0 t s (by omega)]
      simp
  have hpar : ∀ᶠ z in 𝓝 b, z ∈ {z : geoStrictTransform π' C' W' | π' z.val ∉ C'} →
      ∃ c : ℂ, ∀ t : Fin n', k' ≤ t.1 → α' t z.val = c * v t z := by
    filter_upwards [hkey, hnz] with z hk hn hzD
    obtain ⟨h1, h2⟩ := hn hzD
    refine ⟨h (Q z) / h' z.val, fun t ht => ?_⟩
    have := hk t ht
    field_simp
    linear_combination this
  have hinv : ∀ᶠ z in 𝓝 b, z ∈ {z : geoStrictTransform π' C' W' | π' z.val ∉ C'} →
      ∀ s : Fin n, k ≤ s.1 → α s (Q z) = ∑ t, A s t (π' z.val) * v t z := by
    filter_upwards [hkey, hnz, E1, E2, E4, hφb] with z hk hn e1 e2 e4 e5 hzD s hs
    obtain ⟨-, h2⟩ := hn hzD
    have hmul : α s (Q z) * h (Q z) = (∑ t, A s t (π' z.val) * v t z) * h (Q z) := by
      rw [← e2 s hs, e5, e4 (hW'mem z) s hs, Finset.sum_mul]
      refine Finset.sum_congr rfl fun t _ => ?_
      by_cases ht : k' ≤ t.1
      · rw [e1 t ht, hk t ht, mul_assoc]
      · rw [hA0 s t (by omega)]
        simp
    exact mul_right_cancel₀ h2 hmul
  -- apply the limit lemma
  obtain ⟨c, hc, hcb⟩ := limit_proportional (mem_closure_offCentre b)
    (fun t : Fin n' => k' ≤ t.1) (fun s : Fin n => k ≤ s.1)
    (fun t z => α' t z.val) v (fun s z => α s (Q z)) (fun s t z => A s t (π' z.val))
    hcu hcv hcα hcA (fun s t ht => by
      show A s t (π' b.val) = 0
      rw [hA0 s t (by omega)]
      rfl) hpar hinv ⟨t₀, ht₀, hαt₀⟩ hs₀
  refine ⟨c, hc, fun t ht => ?_⟩
  rw [hcb t ht, hv_def]
  simp only [hb]

/-- **The value-level core of pair-injectivity.**  Two points `a, c` of the geometric strict
transform `S' = closure (π'⁻¹ (W' ∖ C'))` over the same point `w₀`, with the same image under a map
`Q : S' → Z` that is continuous at both and satisfies `π ∘ Q = φ ∘ π'` near both, coincide, provided
the flattening coordinates of `C'` at `w₀` and the flattening coordinates of `C` at `φ w₀`, pulled
back by `φ`, generate the same ideal along `W'` near `w₀` (explicit matrices `A'`, `A` continuous at
`w₀`, supported on the normal coordinates). -/
theorem eq_of_pair_value_core (hπ : IsBlowupAlong n C π) (hπ' : IsBlowupAlong n' C' π')
    (hW' : IsClosed W')
    {y₀ : M} {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y₀ y₀)} {k : ℕ}
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) y₀).target)
    (hflat : ∀ {y : M}, y ∈ (chartAt (ComplexModel n) y₀).source →
      chartAt (ComplexModel n) y₀ y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) y₀ y) ∈ complexCoordinatePlane n k))
    {w₀ : M'} {Φ' : LocalHolomorphicEquivAt (n := n') (chartAt (ComplexModel n') w₀ w₀)}
    {k' : ℕ} (hΦ'src : Φ'.source ⊆ (chartAt (ComplexModel n') w₀).target)
    (hflat' : ∀ {y : M'}, y ∈ (chartAt (ComplexModel n') w₀).source →
      chartAt (ComplexModel n') w₀ y ∈ Φ'.source →
        (y ∈ C' ↔ Φ'.toFun (chartAt (ComplexModel n') w₀ y) ∈ complexCoordinatePlane n' k'))
    (Q : geoStrictTransform π' C' W' → Z) (φ : M' → M)
    (A' : Fin n' → Fin n → M' → ℂ) (A : Fin n → Fin n' → M' → ℂ)
    (hA'0 : ∀ t s, s.1 < k → A' t s = 0) (hA0 : ∀ s t, t.1 < k' → A s t = 0)
    (hA'c : ∀ t s, ContinuousAt (A' t s) w₀) (hAc : ∀ s t, ContinuousAt (A s t) w₀)
    (hrel' : ∀ᶠ w in 𝓝 w₀, w ∈ W' → ∀ t : Fin n', k' ≤ t.1 →
      flatCoord Φ' t w = ∑ s, A' t s w * flatCoord Φ s (φ w))
    (hrel : ∀ᶠ w in 𝓝 w₀, w ∈ W' → ∀ s : Fin n, k ≤ s.1 →
      flatCoord Φ s (φ w) = ∑ t, A s t w * flatCoord Φ' t w)
    (a c : geoStrictTransform π' C' W') (ha : π' a.val = w₀) (hc : π' c.val = w₀)
    (hQ : Q a = Q c) (hQflat : π (Q a) ∈ flatDomain Φ)
    (hQa : ContinuousAt Q a) (hQc : ContinuousAt Q c)
    (hφa : ∀ᶠ z in 𝓝 a, π (Q z) = φ (π' z.val)) (hφc : ∀ᶠ z in 𝓝 c, π (Q z) = φ (π' z.val)) :
    a = c := by
  obtain ⟨α, hα, h, hev, s₀, hs₀, hαs₀⟩ := exists_coeff_ne_zero hπ hΦsrc hflat hQflat
  obtain ⟨α₁, hα₁, h₁, hev₁, ⟨t₀, ht₀, hαt₀⟩, c₁, hc₁, hprop₁⟩ :=
    proportional_at hπ' hW' hΦ'src hflat' Q φ A' A hA'0 hA0 hA'c hAc hrel' hrel a ha hQa hφa
      α hα h hev ⟨s₀, hs₀, hαs₀⟩
  have hαc : ∀ s, HolomorphicAt n (α s) (Q c) := hQ ▸ hα
  have hevc : ∀ᶠ x in 𝓝 (Q c), ∀ s : Fin n, k ≤ s.1 → flatCoord Φ s (π x) = α s x * h x :=
    hQ ▸ hev
  obtain ⟨α₂, hα₂, h₂, hev₂, -, c₂, hc₂, hprop₂⟩ :=
    proportional_at hπ' hW' hΦ'src hflat' Q φ A' A hA'0 hA0 hA'c hAc hrel' hrel c hc hQc hφc
      α hαc h hevc ⟨s₀, hs₀, hQ ▸ hαs₀⟩
  have hπac : π' a.val = π' c.val := ha.trans hc.symm
  have hprop : ∀ t : Fin n', k' ≤ t.1 → α₁ t a.val = (c₁ / c₂) * α₂ t c.val := by
    intro t ht
    rw [hprop₁ t ht, hprop₂ t ht, ← hQ]
    field_simp
  exact Subtype.ext (eq_of_proportional_coeff hπ' hΦ'src hflat' hπac
    (ha ▸ mem_flatDomain_self Φ') α₁ α₂ hα₁ hα₂ h₁ h₂ hev₁ hev₂ _ hprop ht₀ hαt₀)

end Core

end

end Hironaka.HironakaG10ChowBlowupDirection
