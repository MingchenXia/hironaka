/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane OM3C)
-/
import DeJongAlterations.StableModification.Projectivity.RelativeTwist
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Serre's extension lemma for line-bundle data (`lem:sm-ltg-serre`)

Blueprint `sm-projectivity-relative.tex`, `lem:sm-qcqs-localization` and `lem:sm-ltg-serre`
(PLAN-OM3 §3 step 3; Hartshorne II.5.14). Let `Z` be a quasi-compact scheme with affine diagonal
(e.g. separated), `𝓐`, `𝓝` line bundles on `Z` (OM3A's line-bundle data), `f` a global section
of `𝓝` and `t` a section of `𝓐` over the non-vanishing locus `D(f)`. Then for some `r` the section
`t ⊗ f^r` of `𝓐 ⊗ 𝓝^r` over `D(f)` extends to a global section `T`
(`exists_extension_tensor`); in particular `D(T) ∩ D(f) = D(t)`
(`exists_extension_of_nonvanishingLocus`).

## Proof

Cover `Z` by finitely many affine opens `V_k`, each inside a chart of `𝓐` and of `𝓝`. On `V_k`
the section `f` is a function `g_k` with `D(f) ∩ V_k = D(g_k)`, so (localization on the affine
`V_k`) `g_k^n t` is the restriction of a section `σ_k` of `𝓐 ⊗ 𝓝^n` over `V_k`. On the affine
`V_k ∩ V_l` the difference `σ_k - σ_l` vanishes on `D(f)`, hence is killed by a power `g_k^e`
(localization again), so the sections `σ_k f^e` glue to `T`.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits

namespace DeJongAlterations.StableModification.Projectivity

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {Z : Scheme.{u}}

namespace LineBundleData

/-! ### Coefficients on an open inside a chart -/

section LocCoeff

variable {B : LineBundleData Z} {m : ℤ}

/-- The coefficient of a section of `𝓑^m` over an open `W` inside the chart `U p`, a function on
`W`. -/
def Sections.locCoeff {W : Z.Opens} {p : B.ι} (hW : W ≤ B.U p) (σ : B.Sections m W) : Γ(Z, W) :=
  Z.presheaf.map (homOfLE (le_inf le_rfl hW : W ≤ W ⊓ B.U p)).op (σ.coeff p)

lemma Sections.locCoeff_eq_toLocal {W : Z.Opens} {p : B.ι} (hW : W ≤ B.U p)
    (σ : B.Sections m W) : σ.locCoeff hW = toLocal (unitModule Z) m hW σ.toTwist :=
  rfl

lemma Sections.locCoeff_injective {W : Z.Opens} {p : B.ι} (hW : W ≤ B.U p) :
    Function.Injective (Sections.locCoeff (m := m) hW) := by
  intro σ τ h
  have := congrArg (ofLocal (unitModule Z) m hW) h
  rw [Sections.locCoeff_eq_toLocal, Sections.locCoeff_eq_toLocal, ofLocal_toLocal,
    ofLocal_toLocal] at this
  exact this

lemma Sections.locCoeff_sub {W : Z.Opens} {p : B.ι} (hW : W ≤ B.U p) (σ τ : B.Sections m W) :
    (σ - τ).locCoeff hW = σ.locCoeff hW - τ.locCoeff hW :=
  map_sub _ _ _

lemma Sections.locCoeff_zero {W : Z.Opens} {p : B.ι} (hW : W ≤ B.U p) :
    (0 : B.Sections m W).locCoeff hW = 0 :=
  map_zero _

lemma Sections.locCoeff_restrict {W W' : Z.Opens} {p : B.ι} (hW : W ≤ B.U p) (h : W' ≤ W)
    (σ : B.Sections m W) :
    (σ.restrict h).locCoeff (h.trans hW) = Z.presheaf.map (homOfLE h).op (σ.locCoeff hW) := by
  simp only [Sections.locCoeff, Sections.coeff_restrict, ringMap_map_trans]

lemma Sections.basicOpen_locCoeff {W : Z.Opens} {p : B.ι} (hW : W ≤ B.U p)
    (σ : B.Sections m W) : Z.basicOpen (σ.locCoeff hW) = σ.nonvanishingLocus := by
  rw [Sections.locCoeff, Scheme.basicOpen_res, ← σ.nonvanishingLocus_inf p]
  apply le_antisymm
  · exact inf_le_right.trans inf_le_left
  · exact le_inf σ.nonvanishingLocus_le (le_inf le_rfl (σ.nonvanishingLocus_le.trans hW))

lemma Sections.locCoeff_ofLocal {W : Z.Opens} {p : B.ι} (hW : W ≤ B.U p) (c : Γ(Z, W)) :
    (Sections.ofTwist (ofLocal (unitModule Z) m hW c) : B.Sections m W).locCoeff hW = c :=
  toLocal_ofLocal (unitModule Z) m hW c

end LocCoeff

/-! ### The extension lemma -/

section Extension

variable {A N : LineBundleData Z}

lemma Sections.locCoeff_mulPow {n e : ℤ} {W : Z.Opens} {p : A.ι × N.ι}
    (hW : W ≤ (A.mul (N.pow n)).U p) (σ : (A.mul (N.pow n)).Sections 1 W) (g : N.Sections e W) :
    (σ.mulPow g).locCoeff (B := A.mul (N.pow (n + e))) hW =
      σ.locCoeff hW * g.locCoeff (B := N) (hW.trans inf_le_right) := by
  simp only [Sections.locCoeff, Sections.coeff_mulPow, map_mul, ringMap_map_trans]

lemma Sections.locCoeff_tensorN {e : ℤ} {W : Z.Opens} {p : A.ι × N.ι}
    (hW : W ≤ (A.mul (N.pow e)).U p) (t : A.Sections 1 W) (g : N.Sections e W) :
    (t.tensorN g).locCoeff hW = t.locCoeff (B := A) (hW.trans inf_le_left) *
      g.locCoeff (B := N) (hW.trans inf_le_right) := by
  simp only [Sections.locCoeff, Sections.coeff_tensorN, map_mul, ringMap_map_trans]

lemma Sections.locCoeff_npow {m : ℤ} {W : Z.Opens} {i : N.ι} (hW : W ≤ N.U i)
    (g : N.Sections m W) (k : ℕ) : (g.npow k).locCoeff hW = g.locCoeff hW ^ k := by
  simp only [Sections.locCoeff, Sections.coeff_npow, map_pow]

lemma Sections.locCoeff_castPow {n n' : ℤ} (h : n = n') {W : Z.Opens} {p : A.ι × N.ι}
    (hW : W ≤ (A.mul (N.pow n)).U p) (σ : (A.mul (N.pow n)).Sections 1 W) :
    (σ.castPow h).locCoeff (B := A.mul (N.pow n')) hW = σ.locCoeff hW := by
  subst h
  rfl

lemma Sections.restrict_restrict' {B : LineBundleData Z} {m : ℤ} {W₁ W₂ W₃ : Z.Opens}
    (h₁ : W₂ ≤ W₁) (h₂ : W₃ ≤ W₂) (σ : B.Sections m W₁) :
    (σ.restrict h₁).restrict h₂ = σ.restrict (h₂.trans h₁) := by
  ext i
  simp only [Sections.coeff_restrict, ringMap_map_trans]

lemma Sections.restrict_sub' {B : LineBundleData Z} {m : ℤ} {W W' : Z.Opens} (h : W' ≤ W)
    (σ τ : B.Sections m W) : (σ - τ).restrict h = σ.restrict h - τ.restrict h := by
  ext i
  change Z.presheaf.map _ (σ.coeff i - τ.coeff i) = Z.presheaf.map _ (σ.coeff i) -
    Z.presheaf.map _ (τ.coeff i)
  exact map_sub _ _ _

lemma Sections.restrict_cast {B : LineBundleData Z} {m m' : ℤ} (h : m = m') {W W' : Z.Opens}
    (hW : W' ≤ W) (σ : B.Sections m W) : (σ.cast h).restrict hW = (σ.restrict hW).cast h := by
  subst h
  rfl

lemma Sections.locCoeff_cast {B : LineBundleData Z} {m m' : ℤ} (h : m = m') {W : Z.Opens}
    {p : B.ι} (hW : W ≤ B.U p) (σ : B.Sections m W) : (σ.cast h).locCoeff hW = σ.locCoeff hW := by
  subst h
  rfl

lemma Sections.locCoeff_restrict_tensorN_npow {D' W : Z.Opens} (t : A.Sections 1 D')
    (f' : N.Sections 1 D') (k : ℕ) (hW : W ≤ D') {p : A.ι × N.ι}
    (hWp : W ≤ (A.mul (N.pow (k : ℤ))).U p) :
    ((t.tensorN ((f'.npow k).cast (one_mul _))).restrict hW).locCoeff hWp =
      (t.restrict hW).locCoeff (B := A) (hWp.trans inf_le_left) *
        ((f'.restrict hW).locCoeff (B := N) (hWp.trans inf_le_right)) ^ k := by
  simp only [Sections.locCoeff, Sections.coeff_restrict, Sections.coeff_tensorN,
    Sections.coeff_cast, Sections.coeff_npow, map_mul, map_pow, ringMap_map_trans]

variable [CompactSpace Z]

/-- A finite cover of `Z` by affine opens inside charts of two line-bundle data. -/
lemma exists_finite_affine_chart_cover (A N : LineBundleData Z) :
    ∃ (κ : Type u) (_ : Fintype κ) (V : κ → Z.Opens) (i : κ → A.ι) (j : κ → N.ι),
      (∀ x, IsAffineOpen (V x)) ∧ (∀ x, V x ≤ A.U (i x) ⊓ N.U (j x)) ∧
        ∀ z : Z, ∃ x, z ∈ V x := by
  have hcov : ∀ x : Z, ∃ V : Z.Opens, IsAffineOpen V ∧ x ∈ V ∧ ∃ i j, V ≤ A.U i ⊓ N.U j := by
    intro x
    obtain ⟨i, hi⟩ := A.exists_mem_U x
    obtain ⟨j, hj⟩ := N.exists_mem_U x
    obtain ⟨V, hV, hxV, hVij⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ A.U i ⊓ N.U j from ⟨hi, hj⟩)
    exact ⟨V, hV, hxV, i, j, hVij⟩
  choose V hV hxV i j hVij using hcov
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set Z))
    (fun x => (V x).isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x, hxV x⟩)
  refine ⟨s, inferInstance, fun x => V x.1, fun x => i x.1, fun x => j x.1, fun x => hV x.1,
    fun x => hVij x.1, fun z => ?_⟩
  have := hs (Set.mem_univ z)
  simp only [Set.mem_iUnion] at this
  obtain ⟨x, hx, hz⟩ := this
  exact ⟨⟨x, hx⟩, hz⟩

variable [IsAffineHom (pullback.diagonal (terminal.from Z))]

/-- **Serre's extension lemma** (blueprint `lem:sm-ltg-serre`, Hartshorne II.5.14): on a
quasi-compact scheme with affine diagonal, for a global section `f` of `𝓝` and a section `t` of
`𝓐` over `D(f)`, some `t ⊗ f^r` extends to a global section of `𝓐 ⊗ 𝓝^r`. -/
theorem exists_extension_tensor (f : N.Sections 1 ⊤) (t : A.Sections 1 f.nonvanishingLocus) :
    ∃ (r : ℕ) (T : (A.mul (N.pow (r : ℤ))).Sections 1 ⊤),
      T.restrict le_top = t.tensorN (((f.restrict le_top).npow r).cast (one_mul _)) := by
  obtain ⟨κ, _, V, i, j, hV, hVij, hcov⟩ := exists_finite_affine_chart_cover A N
  have hVi : ∀ x, V x ≤ A.U (i x) := fun x => (hVij x).trans inf_le_left
  have hVj : ∀ x, V x ≤ N.U (j x) := fun x => (hVij x).trans inf_le_right
  -- `f` on `V x` is the function `g x`
  obtain ⟨g, hgdef⟩ : ∃ g : ∀ x, Γ(Z, V x),
      ∀ x, g x = (f.restrict (le_top : V x ≤ ⊤)).locCoeff (B := N) (p := j x) (hVj x) := ⟨_, fun _ => rfl⟩
  have hg : ∀ x, Z.basicOpen (g x) = V x ⊓ f.nonvanishingLocus := fun x => by
    rw [hgdef, Sections.basicOpen_locCoeff, Sections.nonvanishingLocus_restrict]
  have hBV : ∀ x, Z.basicOpen (g x) ≤ V x := fun x => Z.basicOpen_le _
  have hBD : ∀ x, Z.basicOpen (g x) ≤ f.nonvanishingLocus := fun x =>
    (hg x).le.trans inf_le_right
  have hfloc : ∀ x {W : Z.Opens} (hW : W ≤ V x),
      (f.restrict (le_top : W ≤ ⊤)).locCoeff (B := N) (p := j x) (hW.trans (hVj x)) =
        Z.presheaf.map (homOfLE hW).op (g x) := by
    intro x W hW
    rw [hgdef, ← Sections.locCoeff_restrict (B := N) (p := j x) (hVj x) hW (f.restrict (le_top : V x ≤ ⊤)),
      Sections.restrict_restrict' (le_top : V x ≤ ⊤) hW f]
  -- the coefficient of `t ⊗ f^k` on opens inside `V x ∩ D(f)`
  have hτloc : ∀ (k : ℕ) x {W : Z.Opens} (hW : W ≤ f.nonvanishingLocus) (hWV : W ≤ V x),
      ((t.tensorN (((f.restrict (le_top : f.nonvanishingLocus ≤ ⊤)).npow k).cast
          (one_mul _))).restrict hW).locCoeff
          (B := A.mul (N.pow (k : ℤ))) (p := (i x, j x)) (hWV.trans (hVij x)) =
        (t.restrict hW).locCoeff (B := A) (p := i x) (hWV.trans (hVi x)) *
          Z.presheaf.map (homOfLE hWV).op (g x) ^ k := by
    intro k x W hW hWV
    rw [Sections.locCoeff_restrict_tensorN_npow t (f.restrict le_top) k hW (hWV.trans (hVij x)),
      Sections.restrict_restrict' (le_top : f.nonvanishingLocus ≤ ⊤) hW f, hfloc x hWV]
  -- the coefficient of `t` on `D(g x)`
  obtain ⟨a, hadef⟩ : ∃ a : ∀ x, Γ(Z, Z.basicOpen (g x)),
      ∀ x, a x = (t.restrict (hBD x)).locCoeff (B := A) (p := i x) ((hBV x).trans (hVi x)) :=
    ⟨_, fun _ => rfl⟩
  -- numerators
  have step1 : ∀ x, ∃ (n : ℕ) (c : Γ(Z, V x)), Z.presheaf.map (homOfLE (hBV x)).op c =
      Z.presheaf.map (homOfLE (hBV x)).op (g x) ^ n * a x := by
    intro x
    let := (hV x).isLocalization_basicOpen (g x)
    obtain ⟨⟨c, ⟨_, n, rfl⟩⟩, hc⟩ := IsLocalization.surj (Submonoid.powers (g x)) (a x)
    refine ⟨n, c, ?_⟩
    have hc' : a x * Z.presheaf.map (homOfLE (hBV x)).op (g x ^ n) =
        Z.presheaf.map (homOfLE (hBV x)).op c := hc
    rw [← hc', map_pow, mul_comm]
  choose nx c hc using step1
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, ∀ x, nx x ≤ n₀ :=
    ⟨Finset.univ.sup nx, fun x => Finset.le_sup (Finset.mem_univ x)⟩
  obtain ⟨c', hc'⟩ : ∃ c' : ∀ x, Γ(Z, V x), ∀ x, Z.presheaf.map (homOfLE (hBV x)).op (c' x) =
      Z.presheaf.map (homOfLE (hBV x)).op (g x) ^ n₀ * a x := by
    refine ⟨fun x => g x ^ (n₀ - nx x) * c x, fun x => ?_⟩
    have hle : nx x ≤ n₀ := hn₀ x
    simp only [map_mul, map_pow, hc x, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  -- the local sections `σ x` of `𝓐 ⊗ 𝓝^{n₀}`
  obtain ⟨σ, hσ⟩ : ∃ σ : ∀ x, (A.mul (N.pow (n₀ : ℤ))).Sections 1 (V x),
      ∀ x, (σ x).locCoeff (p := (i x, j x)) (hVij x) = c' x :=
    ⟨fun x => Sections.ofTwist (ofLocal (unitModule Z) 1 (L := A.mul (N.pow (n₀ : ℤ)))
      (i := (i x, j x)) (hVij x) (c' x)), fun x => Sections.locCoeff_ofLocal (B := A.mul (N.pow (n₀ : ℤ))) (p := (i x, j x)) (hVij x) (c' x)⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : (A.mul (N.pow (n₀ : ℤ))).Sections 1 f.nonvanishingLocus,
      τ = t.tensorN (((f.restrict (le_top : f.nonvanishingLocus ≤ ⊤)).npow n₀).cast (one_mul _)) :=
    ⟨_, rfl⟩
  have step2 : ∀ x, (σ x).restrict (hBV x) = τ.restrict (hBD x) := by
    intro x
    apply Sections.locCoeff_injective (B := A.mul (N.pow (n₀ : ℤ))) (p := (i x, j x))
      ((hBV x).trans (hVij x))
    rw [Sections.locCoeff_restrict (B := A.mul (N.pow (n₀ : ℤ))) (p := (i x, j x)) (hVij x) (hBV x) (σ x), hσ x, hc' x, hτ,
      hτloc n₀ x (hBD x) (hBV x), ← hadef, mul_comm]
  have step2' : ∀ x {W : Z.Opens} (hW : W ≤ Z.basicOpen (g x)),
      (σ x).restrict (hW.trans (hBV x)) = τ.restrict (hW.trans (hBD x)) := by
    intro x W hW
    rw [← Sections.restrict_restrict' (hBV x) hW (σ x), step2 x,
      Sections.restrict_restrict' (hBD x) hW τ]
  -- the overlaps
  have step3 : ∀ x y, ∃ e : ℕ,
      Z.presheaf.map (homOfLE (inf_le_left : V x ⊓ V y ≤ V x)).op (g x) ^ e *
        ((σ x).restrict inf_le_left - (σ y).restrict inf_le_right).locCoeff
          (B := A.mul (N.pow (n₀ : ℤ))) (p := (i x, j x)) (inf_le_left.trans (hVij x)) = 0 := by
    intro x y
    set h := Z.presheaf.map (homOfLE (inf_le_left : V x ⊓ V y ≤ V x)).op (g x) with hh
    have hxy : IsAffineOpen (V x ⊓ V y) := (hV x).inf (hV y)
    let := hxy.isLocalization_basicOpen h
    have hBh : Z.basicOpen h = V x ⊓ V y ⊓ f.nonvanishingLocus := by
      rw [hh, Scheme.basicOpen_res, hg x]
      apply le_antisymm
      · exact le_inf inf_le_left (inf_le_right.trans inf_le_right)
      · exact le_inf inf_le_left (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
    have hBx : Z.basicOpen h ≤ Z.basicOpen (g x) := by
      rw [hBh, hg x]
      exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have hBy : Z.basicOpen h ≤ Z.basicOpen (g y) := by
      rw [hBh, hg y]
      exact le_inf (inf_le_left.trans inf_le_right) inf_le_right
    obtain ⟨δ, hδdef⟩ : ∃ δ : (A.mul (N.pow (n₀ : ℤ))).Sections 1 (V x ⊓ V y),
        δ = (σ x).restrict (inf_le_left : V x ⊓ V y ≤ V x) -
          (σ y).restrict (inf_le_right : V x ⊓ V y ≤ V y) := ⟨_, rfl⟩
    have hδ : δ.restrict (Z.basicOpen_le h) = 0 := by
      rw [hδdef, Sections.restrict_sub' (Z.basicOpen_le h) ((σ x).restrict inf_le_left)
          ((σ y).restrict inf_le_right),
        Sections.restrict_restrict' inf_le_left (Z.basicOpen_le h) (σ x),
        Sections.restrict_restrict' inf_le_right (Z.basicOpen_le h) (σ y),
        step2' x hBx, step2' y hBy, sub_self]
    have hd : Z.presheaf.map (homOfLE (Z.basicOpen_le h)).op
        (δ.locCoeff (B := A.mul (N.pow (n₀ : ℤ))) (p := (i x, j x))
          (inf_le_left.trans (hVij x))) = 0 := by
      rw [← Sections.locCoeff_restrict (B := A.mul (N.pow (n₀ : ℤ))) (p := (i x, j x)) (inf_le_left.trans (hVij x)) (Z.basicOpen_le h) δ, hδ,
        Sections.locCoeff_zero]
    obtain ⟨⟨_, e, rfl⟩, he⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers h)
      (S := Γ(Z, Z.basicOpen h))
      (show algebraMap Γ(Z, V x ⊓ V y) Γ(Z, Z.basicOpen h)
        (δ.locCoeff (B := A.mul (N.pow (n₀ : ℤ))) (p := (i x, j x))
          (inf_le_left.trans (hVij x))) = algebraMap _ _ 0 from hd.trans (map_zero _).symm)
    refine ⟨e, ?_⟩
    rw [← hδdef]
    simpa using he
  choose e he using step3
  obtain ⟨e₀, hee⟩ : ∃ e₀ : ℕ, ∀ x y, e x y ≤ e₀ :=
    ⟨Finset.univ.sup fun x => Finset.univ.sup fun y => e x y, fun x y =>
      (Finset.le_sup (f := fun y => e x y) (Finset.mem_univ y)).trans
        (Finset.le_sup (f := fun x => Finset.univ.sup fun y => e x y) (Finset.mem_univ x))⟩
  obtain ⟨σ', hσ'⟩ : ∃ σ' : ∀ x, (A.mul (N.pow ((n₀ : ℤ) + 1 * (e₀ : ℤ)))).Sections 1 (V x),
      ∀ x, σ' x = (σ x).mulPow ((f.restrict (le_top : V x ≤ ⊤)).npow e₀) := ⟨_, fun _ => rfl⟩
  have hres' : ∀ x {W : Z.Opens} (hW : W ≤ V x), (σ' x).restrict hW =
      ((σ x).restrict hW).mulPow ((f.restrict (le_top : W ≤ ⊤)).npow e₀) := by
    intro x W hW
    rw [hσ' x, Sections.restrict_mulPow hW (σ x), Sections.restrict_npow hW _ e₀,
      Sections.restrict_restrict' (le_top : V x ≤ ⊤) hW f]
  have hcompat : ∀ x y, (σ' x).restrict (inf_le_left : V x ⊓ V y ≤ V x) =
      (σ' y).restrict (inf_le_right : V x ⊓ V y ≤ V y) := by
    intro x y
    rw [← sub_eq_zero]
    apply Sections.locCoeff_injective (B := A.mul (N.pow ((n₀ : ℤ) + 1 * (e₀ : ℤ))))
      (p := (i x, j x)) (inf_le_left.trans (hVij x))
    rw [Sections.locCoeff_zero, hres' x inf_le_left, hres' y inf_le_right,
      ← Sections.sub_mulPow, Sections.locCoeff_mulPow (n := (n₀ : ℤ)) (e := 1 * (e₀ : ℤ)) (p := (i x, j x)) (inf_le_left.trans (hVij x)) _ _,
      Sections.locCoeff_npow (N := N) (m := 1) (i := j x) ((inf_le_left.trans (hVij x)).trans inf_le_right) _ e₀,
      hfloc x inf_le_left, ← Nat.sub_add_cancel (hee x y), pow_add, mul_comm, mul_assoc, he x y,
      mul_zero]
  -- gluing
  let F := (A.mul (N.pow ((n₀ : ℤ) + 1 * (e₀ : ℤ)))).twist (unitModule Z) 1
  let G : TopCat.Sheaf Ab Z := ⟨F.presheaf, F.isSheaf⟩
  have hcov' : (⊤ : Z.Opens) ≤ ⨆ x, V x := fun z _ => by
    obtain ⟨x, hz⟩ := hcov z
    exact Opens.mem_iSup.mpr ⟨x, hz⟩
  obtain ⟨T, hT, -⟩ := G.existsUnique_gluing' V ⊤ (fun x => homOfLE le_top) hcov'
    (fun x => (σ' x : ToType (G.1.obj (op (V x))))) (fun x y => hcompat x y)
  obtain ⟨T', hT'⟩ : ∃ T' : (A.mul (N.pow ((n₀ : ℤ) + 1 * (e₀ : ℤ)))).Sections 1 ⊤,
      ∀ x, T'.restrict (le_top : V x ≤ ⊤) = σ' x := ⟨Sections.ofTwist T, hT⟩
  have hr : (n₀ : ℤ) + 1 * (e₀ : ℤ) = ((n₀ + e₀ : ℕ) : ℤ) := by push_cast; ring
  refine ⟨n₀ + e₀,
    T'.castPow hr, ?_⟩
  -- compare on the cover of `D(f)` by the `D(g x)`
  let F' := (A.mul (N.pow ((n₀ + e₀ : ℕ) : ℤ))).twist (unitModule Z) 1
  let G' : TopCat.Sheaf Ab Z := ⟨F'.presheaf, F'.isSheaf⟩
  have hcovD : f.nonvanishingLocus ≤ ⨆ x, Z.basicOpen (g x) := fun z hz => by
    obtain ⟨x, hzx⟩ := hcov z
    refine Opens.mem_iSup.mpr ⟨x, ?_⟩
    rw [hg x]
    exact ⟨hzx, hz⟩
  refine G'.eq_of_locally_eq' (fun x => Z.basicOpen (g x)) f.nonvanishingLocus
    (fun x => homOfLE (hBD x)) hcovD _ _ (fun x => ?_)
  change ((T'.castPow
      hr).restrict le_top).restrict (hBD x) =
    (t.tensorN (((f.restrict (le_top : f.nonvanishingLocus ≤ ⊤)).npow (n₀ + e₀)).cast
      (one_mul _))).restrict (hBD x)
  apply Sections.locCoeff_injective (B := A.mul (N.pow ((n₀ + e₀ : ℕ) : ℤ))) (p := (i x, j x))
    ((hBV x).trans (hVij x))
  rw [hτloc (n₀ + e₀) x (hBD x) (hBV x),
    Sections.restrict_restrict' le_top (hBD x) (T'.castPow hr),
    Sections.restrict_castPow hr ((hBD x).trans le_top) T',
    Sections.locCoeff_castPow (n := (n₀ : ℤ) + 1 * (e₀ : ℤ)) (p := (i x, j x)) hr ((hBV x).trans (hVij x)) _,
    ← Sections.restrict_restrict' (le_top : V x ≤ ⊤) (hBV x) T', hT' x,
    Sections.locCoeff_restrict (B := A.mul (N.pow ((n₀ : ℤ) + 1 * (e₀ : ℤ)))) (p := (i x, j x)) (hVij x) (hBV x) (σ' x), hσ' x,
    Sections.locCoeff_mulPow (n := (n₀ : ℤ)) (e := 1 * (e₀ : ℤ)) (p := (i x, j x)) (hVij x) (σ x) _, Sections.locCoeff_npow (N := N) (m := 1) (i := j x) (hVj x) _ e₀, ← hgdef,
    hσ x, map_mul, map_pow, hc' x, ← hadef, pow_add]
  ring

/-- **Serre's extension lemma**, non-vanishing form: for a global section `f` of `𝓝` and a
section `t` of `𝓐` over `D(f)` there are `r` and a global section `T` of `𝓐 ⊗ 𝓝^r` with
`D(T) ∩ D(f) = D(t)`. -/
theorem exists_extension_of_nonvanishingLocus (f : N.Sections 1 ⊤)
    (t : A.Sections 1 f.nonvanishingLocus) :
    ∃ (r : ℕ) (T : (A.mul (N.pow (r : ℤ))).Sections 1 ⊤),
      T.nonvanishingLocus ⊓ f.nonvanishingLocus = t.nonvanishingLocus := by
  obtain ⟨r, T, hT⟩ := exists_extension_tensor f t
  refine ⟨r, T, ?_⟩
  have h := congrArg Sections.nonvanishingLocus hT
  rw [Sections.nonvanishingLocus_restrict, Sections.nonvanishingLocus_tensorN,
    Sections.nonvanishingLocus_cast] at h
  rw [inf_comm, h]
  refine inf_eq_left.mpr (fun x hx => ?_)
  refine Sections.nonvanishingLocus_le_npow _ r ?_
  rw [Sections.nonvanishingLocus_restrict]
  exact ⟨t.nonvanishingLocus_le hx, t.nonvanishingLocus_le hx⟩

/-- **Small non-vanishing loci** (a consequence of `lem:sm-ltg-serre`): if a global section `e` of
`𝓝` has affine non-vanishing locus containing `z`, then every open neighbourhood `O` of `z`
contains the non-vanishing locus of a global section of some `𝓝^d` which does not vanish at `z`. -/
theorem exists_section_mem_le {N : LineBundleData Z} (e : N.Sections 1 ⊤)
    (he : IsAffineOpen e.nonvanishingLocus) {z : Z} (hz : z ∈ e.nonvanishingLocus) {O : Z.Opens}
    (hzO : z ∈ O) :
    ∃ (d : ℕ) (F : N.Sections (d : ℤ) ⊤), 0 < d ∧ z ∈ F.nonvanishingLocus ∧
      F.nonvanishingLocus ≤ O := by
  obtain ⟨b, hbO, hzb⟩ := he.exists_basicOpen_le (V := O) ⟨z, hzO⟩ hz
  let t : N.Sections 1 e.nonvanishingLocus := b • e.restrict le_top
  have ht : t.nonvanishingLocus = Z.basicOpen b := by
    rw [Sections.nonvanishingLocus_smul_eq, Sections.nonvanishingLocus_restrict]
    exact inf_eq_left.mpr (le_inf (Z.basicOpen_le b) (Z.basicOpen_le b))
  obtain ⟨r, T, hT⟩ := exists_extension_of_nonvanishingLocus (A := N) e t
  have hr : (1 + (r : ℤ)) + 1 = ((r + 2 : ℕ) : ℤ) := by push_cast; ring
  refine ⟨r + 2, (T.diag.mul e).cast hr, by omega, ?_, ?_⟩
  · rw [Sections.nonvanishingLocus_cast, Sections.nonvanishingLocus_mul,
      Sections.nonvanishingLocus_diag, hT, ht]
    exact hzb
  · rw [Sections.nonvanishingLocus_cast, Sections.nonvanishingLocus_mul,
      Sections.nonvanishingLocus_diag, hT, ht]
    exact hbO

end Extension

end LineBundleData

end

end DeJongAlterations.StableModification.Projectivity
