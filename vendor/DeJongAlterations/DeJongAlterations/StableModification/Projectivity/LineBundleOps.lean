/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane OM3A)
-/
import DeJongAlterations.StableModification.Projectivity.LineBundleTwist

/-!
# Operations on line-bundle data

Blueprint `sm-projectivity-core.tex`, `lem:sm-lbd-ops` and `lem:sm-lbd-cartier` (PLAN-OM3 M1).
For line-bundle data `L`, `L'` on `X` (`LineBundle.lean`):

* invariance under isomorphisms of modules: `IsGloballyGenerated.of_iso`,
  `isZero_cechCohomology_iff_of_iso`;
* powers `L.pow n` (`twistSubgroup_pow`: `(𝓛^n)^m = 𝓛^{n m}` on sections) and tensor products
  `L.mul L'` with the product of sections `Sections.tensor`;
* `twistZeroIso : F ⊗ 𝓛^0 ≅ F`, and `twistIsoOfNonvanishing`: a nowhere vanishing section of
  `𝓛^m` gives `F ⊗ 𝓛^n ≅ F ⊗ 𝓛^{m+n}` (so `F ⊗ 𝓛^{m k} ≅ F` when `𝓛^m` is trivial);
* `LocalEquations` (`lem:sm-lbd-cartier`): an effective Cartier divisor given by local equations
  `f i` with `f i = u i j · f j`, its line bundle `𝒪(D)` and canonical section `s_D`
  (`LocalEquations.canonicalSection`, non-vanishing exactly off `D`), and the construction from
  local equations which are non-zero-divisors (`LocalEquations.ofNonZeroDivisors`).
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits

namespace DeJongAlterations.StableModification.Projectivity

noncomputable section

variable {X : Scheme.{u}}

lemma ringMap_map' {V₁ V₂ V₃ : X.Opens} (h₁ : V₂ ≤ V₁) (h₂ : V₃ ≤ V₂) (h₃ : V₃ ≤ V₁)
    (r : Γ(X, V₁)) :
    X.presheaf.map (homOfLE h₂).op (X.presheaf.map (homOfLE h₁).op r) =
      X.presheaf.map (homOfLE h₃).op r :=
  res_res h₁ h₂ h₃ r

/-- Two restrictions compose (with the composite inclusion, so that rewriting creates no side
goals). -/
lemma ringMap_map_trans {V₁ V₂ V₃ : X.Opens} (h₁ : V₂ ≤ V₁) (h₂ : V₃ ≤ V₂) (r : Γ(X, V₁)) :
    X.presheaf.map (homOfLE h₂).op (X.presheaf.map (homOfLE h₁).op r) =
      X.presheaf.map (homOfLE (h₂.trans h₁)).op r :=
  res_res h₁ h₂ _ r

lemma res_res_trans {V₁ V₂ V₃ : X.Opens} (h₁ : V₂ ≤ V₁) (h₂ : V₃ ≤ V₂) (r : Γ(X, V₁)) :
    res h₂ (res h₁ r) = res (h₂.trans h₁) r :=
  res_res h₁ h₂ _ r

lemma ringMap_self' {V : X.Opens} (h : V ≤ V) (r : Γ(X, V)) :
    X.presheaf.map (homOfLE h).op r = r :=
  res_self h r

/-- A function whose basic open is its whole domain is a unit. -/
lemma isUnit_of_basicOpen_eq {U : X.Opens} {f : Γ(X, U)} (h : X.basicOpen f = U) : IsUnit f :=
  RingedSpace.isUnit_of_isUnit_germ X.toRingedSpace U f fun x hx =>
    (X.mem_basicOpen f x hx).mp (h.symm ▸ hx)

/-! ### Invariance under isomorphisms -/

/-- Global generation is invariant under isomorphisms of modules. -/
lemma IsGloballyGenerated.of_iso {M N : X.Modules} (e : M ≅ N) (h : IsGloballyGenerated M) :
    IsGloballyGenerated N := by
  intro W s x hx
  obtain ⟨V, hVW, hxV, hV⟩ := h W (e.inv.app W s) x hx
  refine ⟨V, hVW, hxV, ?_⟩
  let φ : Γ(M, V) →ₗ[Γ(X, V)] Γ(N, V) :=
    { toFun := e.hom.app V
      map_add' := map_add _
      map_smul' := fun r t => Scheme.Modules.Hom.app_smul e.hom r t }
  have nat : ∀ {V₁ V₂ : X.Opens} (i : V₂ ⟶ V₁) (t : Γ(M, V₁)),
      e.hom.app V₂ (M.presheaf.map i.op t) = N.presheaf.map i.op (e.hom.app V₁ t) :=
    fun i t => ConcreteCategory.congr_hom (e.hom.mapPresheaf.naturality i.op) t
  have h1 := Submodule.mem_map_of_mem (f := φ) hV
  rw [Submodule.map_span] at h1
  have h2 : φ (M.presheaf.map (homOfLE hVW).op (e.inv.app W s)) =
      N.presheaf.map (homOfLE hVW).op s := by
    change e.hom.app V _ = _
    rw [nat]
    congr 1
    change (e.inv.app W ≫ e.hom.app W) s = s
    rw [← Scheme.Modules.Hom.comp_app, e.inv_hom_id]
    rfl
  rw [h2] at h1
  refine Submodule.span_mono ?_ h1
  rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
  exact ⟨e.hom.app ⊤ t, (nat _ t).symm⟩

/-- Global generation is invariant under isomorphisms of modules. -/
lemma isGloballyGenerated_iff_of_iso {M N : X.Modules} (e : M ≅ N) :
    IsGloballyGenerated M ↔ IsGloballyGenerated N :=
  ⟨IsGloballyGenerated.of_iso e, IsGloballyGenerated.of_iso e.symm⟩

/-- Vanishing of Čech cohomology is invariant under isomorphisms of modules. -/
lemma isZero_cechCohomology_iff_of_iso {M N : X.Modules} (e : M ≅ N) {ι : Type u}
    [LinearOrder ι] (U : ι → X.Opens) {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) (p : ℕ) :
    IsZero (Cohomology.cechCohomology M U c p) ↔ IsZero (Cohomology.cechCohomology N U c p) := by
  let e' := (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) p).mapIso
    ((Cohomology.cechComplexFunctor U c).mapIso e)
  exact ⟨fun h => h.of_iso e'.symm, fun h => h.of_iso e'⟩

namespace LineBundleData

variable (L : LineBundleData X) (F : X.Modules)

lemma coe_res_zpow {i j : L.ι} {V : X.Opens} (h : V ≤ L.U i ⊓ L.U j) (n : ℤ) :
    res h ((L.u i j ^ n : Γ(X, L.U i ⊓ L.U j)ˣ) : Γ(X, L.U i ⊓ L.U j)) =
      ((L.trans h ^ n : Γ(X, V)ˣ) : Γ(X, V)) := by
  rw [trans, ← map_zpow]
  rfl

/-! ### Powers -/

/-- The `n`-th power `𝓛^{⊗ n}` (`n ∈ ℤ`): the same cover with transition units `(u i j)^n`. -/
abbrev pow (n : ℤ) : LineBundleData X where
  ι := L.ι
  U := L.U
  iSup_eq_top := L.iSup_eq_top
  u i j := L.u i j ^ n
  cocycle i j k := by
    rw [L.coe_res_zpow, L.coe_res_zpow, L.coe_res_zpow, ← Units.val_mul, ← mul_zpow,
      L.trans_mul_trans]

lemma pow_trans (n : ℤ) {i j : L.ι} {V : X.Opens} (h : V ≤ L.U i ⊓ L.U j) :
    (L.pow n).trans (i := i) (j := j) h = L.trans h ^ n :=
  Units.ext (L.coe_res_zpow h n)

lemma transPow_pow (n m : ℤ) (W : X.Opens) (i j : L.ι) :
    (L.pow n).transPow m W i j = L.transPow (n * m) W i j := by
  unfold transPow
  rw [pow_trans, ← zpow_mul]

/-- Sections of `(𝓛^n)^m ⊗ F` are sections of `𝓛^{n m} ⊗ F`. -/
lemma twistSubgroup_pow (n m : ℤ) (W : X.Opens) :
    (L.pow n).twistSubgroup F m W = L.twistSubgroup F (n * m) W := by
  ext t
  change (L.pow n).IsCompatible F m W t ↔ L.IsCompatible F (n * m) W t
  unfold IsCompatible
  simp only [transPow_pow]

/-! ### Tensor products -/

section Mul

variable (L' : LineBundleData X)

lemma mul_le₁ (p q : L.ι × L'.ι) {V : X.Opens}
    (h : V ≤ (L.U p.1 ⊓ L'.U p.2) ⊓ (L.U q.1 ⊓ L'.U q.2)) : V ≤ L.U p.1 ⊓ L.U q.1 :=
  fun _ hx => ⟨(h hx).1.1, (h hx).2.1⟩

lemma mul_le₂ (p q : L.ι × L'.ι) {V : X.Opens}
    (h : V ≤ (L.U p.1 ⊓ L'.U p.2) ⊓ (L.U q.1 ⊓ L'.U q.2)) : V ≤ L'.U p.2 ⊓ L'.U q.2 :=
  fun _ hx => ⟨(h hx).1.2, (h hx).2.2⟩

/-- The tensor product `𝓛 ⊗ 𝓛'`: the cover `U i ∩ U' i'` with transition units
`u i j · u' i' j'`. -/
abbrev mul : LineBundleData X where
  ι := L.ι × L'.ι
  U p := L.U p.1 ⊓ L'.U p.2
  iSup_eq_top := by
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨i, hi⟩ := L.exists_mem_U x
    obtain ⟨i', hi'⟩ := L'.exists_mem_U x
    exact Opens.mem_iSup.mpr ⟨(i, i'), hi, hi'⟩
  u p q := L.trans (L.mul_le₁ L' p q le_rfl) * L'.trans (L.mul_le₂ L' p q le_rfl)
  cocycle p q r := by
    simp only [Units.val_mul, map_mul, L.res_trans, L'.res_trans]
    rw [mul_mul_mul_comm, ← Units.val_mul, ← Units.val_mul, L.trans_mul_trans,
      L'.trans_mul_trans]

lemma mul_trans {p q : L.ι × L'.ι} {V : X.Opens}
    (h : V ≤ (L.U p.1 ⊓ L'.U p.2) ⊓ (L.U q.1 ⊓ L'.U q.2)) :
    (L.mul L').trans (i := p) (j := q) h =
      L.trans (L.mul_le₁ L' p q h) * L'.trans (L.mul_le₂ L' p q h) := by
  apply Units.ext
  change res h ((L.trans (L.mul_le₁ L' p q le_rfl) * L'.trans (L.mul_le₂ L' p q le_rfl) :
    Γ(X, (L.U p.1 ⊓ L'.U p.2) ⊓ (L.U q.1 ⊓ L'.U q.2))ˣ) : Γ(X, _)) = _
  rw [Units.val_mul, map_mul, L.res_trans, L'.res_trans, Units.val_mul]

variable {L L'} {m : ℤ}

/-- The **product of sections** `s ⊗ s'` of `𝓛^m` and `𝓛'^m`, a section of `(𝓛 ⊗ 𝓛')^m`. -/
def Sections.tensor {W : X.Opens} (s : L.Sections m W) (s' : L'.Sections m W) :
    (L.mul L').Sections m W :=
  Sections.mk (L := L.mul L')
    (fun p => X.presheaf.map (homOfLE (inf_le_inf_left W inf_le_left :
        W ⊓ (L.U p.1 ⊓ L'.U p.2) ≤ W ⊓ L.U p.1)).op (s.coeff p.1) *
      X.presheaf.map (homOfLE (inf_le_inf_left W inf_le_right :
        W ⊓ (L.U p.1 ⊓ L'.U p.2) ≤ W ⊓ L'.U p.2)).op (s'.coeff p.2)) (by
    intro p q
    have hV₁ : W ⊓ ((L.U p.1 ⊓ L'.U p.2) ⊓ (L.U q.1 ⊓ L'.U q.2)) ≤ W ⊓ (L.U p.1 ⊓ L.U q.1) :=
      fun _ hx => ⟨hx.1, hx.2.1.1, hx.2.2.1⟩
    have hV₂ : W ⊓ ((L.U p.1 ⊓ L'.U p.2) ⊓ (L.U q.1 ⊓ L'.U q.2)) ≤
        W ⊓ (L'.U p.2 ⊓ L'.U q.2) :=
      fun _ hx => ⟨hx.1, hx.2.1.2, hx.2.2.2⟩
    have e₁ := congrArg (X.presheaf.map (homOfLE hV₁).op) (s.coeff_compat p.1 q.1)
    have e₂ := congrArg (X.presheaf.map (homOfLE hV₂).op) (s'.coeff_compat p.2 q.2)
    rw [ringMap_map_trans, map_mul, ringMap_map_trans, L.map_res_trans_zpow] at e₁
    rw [ringMap_map_trans, map_mul, ringMap_map_trans, L'.map_res_trans_zpow] at e₂
    rw [map_mul, ringMap_map_trans, ringMap_map_trans]
    refine (congrArg₂ (· * ·) e₁ e₂).trans ?_
    rw [map_mul, ringMap_map_trans, ringMap_map_trans]
    simp only [transPow, mul_trans, mul_zpow, Units.val_mul]
    ring)

@[simp]
lemma Sections.coeff_tensor {W : X.Opens} (s : L.Sections m W) (s' : L'.Sections m W)
    (p : L.ι × L'.ι) :
    (s.tensor s').coeff p = X.presheaf.map (homOfLE (inf_le_inf_left W inf_le_left :
        W ⊓ (L.U p.1 ⊓ L'.U p.2) ≤ W ⊓ L.U p.1)).op (s.coeff p.1) *
      X.presheaf.map (homOfLE (inf_le_inf_left W inf_le_right :
        W ⊓ (L.U p.1 ⊓ L'.U p.2) ≤ W ⊓ L'.U p.2)).op (s'.coeff p.2) :=
  rfl

lemma Sections.nonvanishingLocus_tensor {W : X.Opens} (s : L.Sections m W)
    (s' : L'.Sections m W) :
    (s.tensor s').nonvanishingLocus = s.nonvanishingLocus ⊓ s'.nonvanishingLocus := by
  apply le_antisymm
  · refine iSup_le fun p => ?_
    rw [Sections.coeff_tensor, X.basicOpen_mul, Scheme.basicOpen_res, Scheme.basicOpen_res]
    exact inf_le_inf (inf_le_right.trans (s.basicOpen_coeff_le p.1))
      (inf_le_right.trans (s'.basicOpen_coeff_le p.2))
  · rintro x ⟨hs, hs'⟩
    obtain ⟨i, hi⟩ := L.exists_mem_U x
    obtain ⟨i', hi'⟩ := L'.exists_mem_U x
    have h₁ := (s.mem_nonvanishingLocus_iff hi).mp hs
    have h₂ := (s'.mem_nonvanishingLocus_iff hi').mp hs'
    have hxW : x ∈ W := (X.basicOpen_le _ h₁).1
    rw [Sections.mem_nonvanishingLocus_iff (L := L.mul L') _ (i := (i, i')) ⟨hi, hi'⟩,
      Sections.coeff_tensor, X.basicOpen_mul, Scheme.basicOpen_res, Scheme.basicOpen_res]
    exact ⟨⟨⟨hxW, hi, hi'⟩, h₁⟩, ⟨hxW, hi, hi'⟩, h₂⟩

end Mul

/-! ### Twisting by `𝓛^0` -/

section Zero

lemma transPow_zero (W : X.Opens) (i j : L.ι) : L.transPow 0 W i j = 1 := by
  simp [transPow]

/-- The restrictions of a section of `F` form a section of `F ⊗ 𝓛^0`. -/
def toTwistZero (W : X.Opens) (s : Γ(F, W)) : L.twistSubgroup F 0 W :=
  ⟨fun i => F.presheaf.map (homOfLE (inf_le_left : W ⊓ L.U i ≤ W)).op s, by
    intro i j
    simp only
    rw [transPow_zero, one_smul, Cohomology.presheaf_map_map F _ _ inf_le_left,
      Cohomology.presheaf_map_map F _ _ inf_le_left]⟩

lemma toTwistZero_injective (W : X.Opens) : Function.Injective (L.toTwistZero F W) := by
  intro s s' h
  let G : TopCat.Sheaf Ab X := ⟨F.presheaf, F.isSheaf⟩
  refine G.eq_of_locally_eq' (fun i => W ⊓ L.U i) W
    (fun i => homOfLE inf_le_left) ?_ s s' (fun i => congrFun (congrArg Subtype.val h) i)
  intro x hx
  obtain ⟨i, hi⟩ := L.exists_mem_U x
  exact Opens.mem_iSup.mpr ⟨i, hx, hi⟩

lemma toTwistZero_surjective (W : X.Opens) : Function.Surjective (L.toTwistZero F W) := by
  intro t
  let G : TopCat.Sheaf Ab X := ⟨F.presheaf, F.isSheaf⟩
  have hcompat : TopCat.Presheaf.IsCompatible G.1 (fun i => W ⊓ L.U i) t.1 := by
    intro i j
    have ht := t.2 i j
    rw [transPow_zero, one_smul] at ht
    have hle : (W ⊓ L.U i) ⊓ (W ⊓ L.U j) ≤ W ⊓ (L.U i ⊓ L.U j) :=
      fun _ hx => ⟨hx.1.1, hx.1.2, hx.2.2⟩
    have e := congrArg (F.presheaf.map (homOfLE hle).op) ht
    rw [Cohomology.presheaf_map_map F _ _ inf_le_left,
      Cohomology.presheaf_map_map F _ _ inf_le_right] at e
    exact e
  have hcov : W ≤ ⨆ i, W ⊓ L.U i := by
    intro x hx
    obtain ⟨i, hi⟩ := L.exists_mem_U x
    exact Opens.mem_iSup.mpr ⟨i, hx, hi⟩
  obtain ⟨s, hs, -⟩ := G.existsUnique_gluing' (fun i => W ⊓ L.U i) W
    (fun i => homOfLE inf_le_left) hcov t.1 hcompat
  exact ⟨s, Subtype.ext (funext hs)⟩

/-- The morphism `F ⟶ F ⊗ 𝓛^0` (restriction to the charts). -/
def toTwistZeroHom : F ⟶ L.twist F 0 where
  val := PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom
        { toFun := L.toTwistZero F W.unop
          map_zero' := Subtype.ext (funext fun _ => map_zero _)
          map_add' := fun _ _ => Subtype.ext (funext fun _ => map_add _ _ _) }
      naturality := fun {W W'} i => by
        ext s
        apply Subtype.ext
        funext j
        change F.presheaf.map (homOfLE (inf_le_left : W'.unop ⊓ L.U j ≤ W'.unop)).op
            (F.presheaf.map (homOfLE (leOfHom i.unop)).op s) =
          F.presheaf.map (homOfLE (inf_le_inf_right (L.U j) (leOfHom i.unop))).op
            (F.presheaf.map (homOfLE (inf_le_left : W.unop ⊓ L.U j ≤ W.unop)).op s)
        exact (Cohomology.presheaf_map_map F _ _ (inf_le_left.trans (leOfHom i.unop)) _).trans
          (Cohomology.presheaf_map_map F _ _ (inf_le_left.trans (leOfHom i.unop)) _).symm }
    (fun W r s => by
      apply Subtype.ext
      funext j
      exact Scheme.Modules.map_smul F (homOfLE (inf_le_left : W.unop ⊓ L.U j ≤ W.unop)) r s)

lemma toTwistZeroHom_app (W : X.Opens) (s : Γ(F, W)) :
    (L.toTwistZeroHom F).app W s = L.toTwistZero F W s :=
  rfl

instance : IsIso (L.toTwistZeroHom F) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro W
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨L.toTwistZero_injective F W, L.toTwistZero_surjective F W⟩

/-- **`F ⊗ 𝓛^0 ≅ F`.** -/
def twistZeroIso : L.twist F 0 ≅ F :=
  (asIso (L.toTwistZeroHom F)).symm

end Zero

/-! ### Nowhere vanishing sections -/

section Nonvanishing

variable {L} {m : ℤ}

/-- `𝓛^m` has a **nowhere vanishing global section** (i.e. `𝓛^m ≅ 𝒪_X`). -/
def HasNonvanishingSection (L : LineBundleData X) (m : ℤ) : Prop :=
  ∃ s : L.Sections m ⊤, s.nonvanishingLocus = ⊤

lemma Sections.isUnit_coeff_of_nonvanishingLocus_eq {W : X.Opens} (s : L.Sections m W)
    (hs : s.nonvanishingLocus = W) (i : L.ι) : IsUnit (s.coeff i) := by
  apply isUnit_of_basicOpen_eq
  rw [← s.nonvanishingLocus_inf, hs]

/-- Multiplication by a section `s` of `𝓛^m` over `⊤`, `F ⊗ 𝓛^n ⟶ F ⊗ 𝓛^{m+n}`. -/
def smulTwistHom (s : L.Sections m ⊤) (n : ℤ) : L.twist F n ⟶ L.twist F (m + n) where
  val := PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom
        { toFun := fun t => (s.restrict le_top).smulTwist F t
          map_zero' := Subtype.ext (funext fun _ => smul_zero _)
          map_add' := fun _ _ => Subtype.ext (funext fun _ => smul_add _ _ _) }
      naturality := fun {W W'} i => by
        ext t
        apply Subtype.ext
        funext j
        change (s.restrict (le_top : W'.unop ≤ ⊤)).coeff j •
            F.presheaf.map (homOfLE (inf_le_inf_right (L.U j) (leOfHom i.unop))).op
              ((t : L.twistSubgroup F n W.unop).1 j) =
          F.presheaf.map (homOfLE (inf_le_inf_right (L.U j) (leOfHom i.unop))).op
            ((s.restrict (le_top : W.unop ≤ ⊤)).coeff j •
              (t : L.twistSubgroup F n W.unop).1 j)
        rw [Scheme.Modules.map_smul]
        congr 1
        exact (ringMap_map_trans _ _ _).symm }
    (fun W r t => by
      apply Subtype.ext
      funext j
      exact smul_comm _ _ _)

lemma smulTwistHom_app_apply (s : L.Sections m ⊤) (n : ℤ) (W : X.Opens)
    (t : L.twistSubgroup F n W) (j : L.ι) :
    ((smulTwistHom F s n).app W t : L.twistSubgroup F (m + n) W).1 j =
      (s.restrict (le_top : W ≤ ⊤)).coeff j • t.1 j :=
  rfl

lemma smulTwistHom_bijective (s : L.Sections m ⊤) (hs : s.nonvanishingLocus = ⊤) (n : ℤ)
    (W : X.Opens) : Function.Bijective ((smulTwistHom F s n).app W) := by
  have hs' : (s.restrict (le_top : W ≤ ⊤)).nonvanishingLocus = W := by
    rw [Sections.nonvanishingLocus_restrict, hs, inf_top_eq]
  have hu := Sections.isUnit_coeff_of_nonvanishingLocus_eq _ hs'
  constructor
  · intro t t' h
    apply Subtype.ext
    funext j
    have hj := congrFun (congrArg Subtype.val h) j
    change (s.restrict le_top).coeff j • t.1 j = (s.restrict le_top).coeff j • t'.1 j at hj
    obtain ⟨v, hv⟩ := hu j
    rw [← hv] at hj
    have := congrArg (fun z => ((v⁻¹ : Γ(X, W ⊓ L.U j)ˣ) : Γ(X, W ⊓ L.U j)) • z) hj
    simpa only [smul_smul, Units.inv_mul, one_smul] using this
  · intro t₀
    let t' : L.twistSubgroup F (m + n) W := t₀
    choose v hv using hu
    refine ⟨⟨fun j => (((v j)⁻¹ : Γ(X, W ⊓ L.U j)ˣ) : Γ(X, W ⊓ L.U j)) • t'.1 j, ?_⟩, ?_⟩
    · intro i j
      have ht := t'.2 i j
      have hsc := (s.restrict (le_top : W ≤ ⊤)).coeff_compat i j
      simp only at ht ⊢
      rw [← hv i, ← hv j] at hsc
      rw [Scheme.Modules.map_smul, Scheme.Modules.map_smul, ht]
      -- unit bookkeeping on `W ∩ U i ∩ U j`
      set a := X.presheaf.map (homOfLE (L.le_left W i j)).op (v i : Γ(X, W ⊓ L.U i))
      set b := X.presheaf.map (homOfLE (L.le_right W i j)).op (v j : Γ(X, W ⊓ L.U j))
      have ha : X.presheaf.map (homOfLE (L.le_left W i j)).op
          (((v i)⁻¹ : Γ(X, W ⊓ L.U i)ˣ) : Γ(X, W ⊓ L.U i)) * a = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      have hb : X.presheaf.map (homOfLE (L.le_right W i j)).op
          (((v j)⁻¹ : Γ(X, W ⊓ L.U j)ˣ) : Γ(X, W ⊓ L.U j)) * b = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      rw [smul_smul, smul_smul]
      congr 1
      have hT : L.transPow (m + n) W i j = L.transPow m W i j * L.transPow n W i j := by
        simp only [transPow, zpow_add, Units.val_mul]
      rw [hT]
      -- from `a = T_m * b`
      have hsc' : a = L.transPow m W i j * b := hsc
      calc X.presheaf.map (homOfLE (L.le_left W i j)).op
            (((v i)⁻¹ : Γ(X, W ⊓ L.U i)ˣ) : Γ(X, W ⊓ L.U i)) *
            (L.transPow m W i j * L.transPow n W i j)
          = X.presheaf.map (homOfLE (L.le_left W i j)).op
              (((v i)⁻¹ : Γ(X, W ⊓ L.U i)ˣ) : Γ(X, W ⊓ L.U i)) *
              (L.transPow m W i j * L.transPow n W i j) *
              (X.presheaf.map (homOfLE (L.le_right W i j)).op
                (((v j)⁻¹ : Γ(X, W ⊓ L.U j)ˣ) : Γ(X, W ⊓ L.U j)) * b) := by rw [hb, mul_one]
        _ = L.transPow n W i j * X.presheaf.map (homOfLE (L.le_right W i j)).op
              (((v j)⁻¹ : Γ(X, W ⊓ L.U j)ˣ) : Γ(X, W ⊓ L.U j)) *
              (X.presheaf.map (homOfLE (L.le_left W i j)).op
                (((v i)⁻¹ : Γ(X, W ⊓ L.U i)ˣ) : Γ(X, W ⊓ L.U i)) *
                (L.transPow m W i j * b)) := by ring
        _ = L.transPow n W i j * X.presheaf.map (homOfLE (L.le_right W i j)).op
              (((v j)⁻¹ : Γ(X, W ⊓ L.U j)ˣ) : Γ(X, W ⊓ L.U j)) := by
            rw [← hsc', ha, mul_one]
    · apply Subtype.ext
      funext j
      change (s.restrict le_top).coeff j •
        ((((v j)⁻¹ : Γ(X, W ⊓ L.U j)ˣ) : Γ(X, W ⊓ L.U j)) • t'.1 j) = t'.1 j
      rw [← hv j, smul_smul, Units.mul_inv, one_smul]

lemma isIso_smulTwistHom (s : L.Sections m ⊤) (hs : s.nonvanishingLocus = ⊤) (n : ℤ) :
    IsIso (smulTwistHom F s n) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro W
  rw [ConcreteCategory.isIso_iff_bijective]
  exact smulTwistHom_bijective F s hs n W

/-- **A nowhere vanishing section of `𝓛^m` gives `F ⊗ 𝓛^n ≅ F ⊗ 𝓛^{m+n}`.** -/
def twistIsoOfNonvanishing (s : L.Sections m ⊤) (hs : s.nonvanishingLocus = ⊤) (n : ℤ) :
    L.twist F n ≅ L.twist F (m + n) :=
  haveI := isIso_smulTwistHom F s hs n
  asIso (smulTwistHom F s n)

/-- Twists by equal exponents are isomorphic. -/
def twistCongr {n n' : ℤ} (h : n = n') : L.twist F n ≅ L.twist F n' :=
  eqToIso (by rw [h])

/-- If `𝓛^m` has a nowhere vanishing section, then `F ⊗ 𝓛^{m k} ≅ F` for every `k : ℕ`. -/
def twistIsoOfNonvanishingMul (s : L.Sections m ⊤) (hs : s.nonvanishingLocus = ⊤) :
    ∀ k : ℕ, L.twist F (m * k) ≅ F
  | 0 => L.twistCongr F (by simp) ≪≫ L.twistZeroIso F
  | k + 1 => L.twistCongr F (by push_cast; ring) ≪≫ (twistIsoOfNonvanishing F s hs (m * k)).symm ≪≫
      twistIsoOfNonvanishingMul s hs k

end Nonvanishing

end LineBundleData

/-! ### Effective Cartier divisors from local equations -/

/-- **Local equations of an effective Cartier divisor** (blueprint `lem:sm-lbd-cartier`): line
bundle data together with functions `f i ∈ Γ(U i, 𝒪_X)` with `f i = u i j · f j` on
`U i ∩ U j`. The line bundle is `𝒪(D)` (generated on `U i` by `1 / f i`), and the functions form
its canonical section `s_D` (`canonicalSection`). -/
structure LocalEquations (X : Scheme.{u}) extends LineBundleData X where
  /-- The local equations. -/
  f : ∀ i, Γ(X, U i)
  f_eq : ∀ i j, res (inf_le_left : U i ⊓ U j ≤ U i) (f i) =
    (u i j : Γ(X, U i ⊓ U j)) * res (inf_le_right : U i ⊓ U j ≤ U j) (f j)

namespace LocalEquations

variable (D : LocalEquations X)

/-- The **canonical section** `s_D` of `𝒪(D)`: its coefficients are the local equations. -/
def canonicalSection : D.toLineBundleData.Sections 1 ⊤ :=
  LineBundleData.Sections.mk (fun i => res (inf_le_right : ⊤ ⊓ D.U i ≤ D.U i) (D.f i)) (by
    intro i j
    have hle : ⊤ ⊓ (D.U i ⊓ D.U j) ≤ D.U i ⊓ D.U j := inf_le_right
    have e := congrArg (res hle) (D.f_eq i j)
    rw [res_res_trans, map_mul, res_res_trans] at e
    change res _ (res _ (D.f i)) = _ * res _ (res _ (D.f j))
    rw [res_res_trans, res_res_trans]
    refine e.trans ?_
    congr 1
    simp only [LineBundleData.transPow, zpow_one]
    rfl)

lemma coeff_canonicalSection (i : D.ι) :
    D.canonicalSection.coeff i = res (inf_le_right : ⊤ ⊓ D.U i ≤ D.U i) (D.f i) :=
  rfl

/-- The canonical section does not vanish exactly off `D`: on `U i` its non-vanishing locus is
`D(f i)`. -/
lemma nonvanishingLocus_canonicalSection_inf (i : D.ι) :
    D.canonicalSection.nonvanishingLocus ⊓ D.U i = X.basicOpen (D.f i) := by
  rw [LineBundleData.Sections.nonvanishingLocus_inf, coeff_canonicalSection]
  change X.basicOpen (X.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ D.U i ≤ D.U i)).op (D.f i)) = _
  rw [Scheme.basicOpen_res]
  exact inf_eq_right.mpr (le_inf le_top (X.basicOpen_le _))

/-- **Local equations from non-zero-divisors**: if the `f i` restrict to non-zero-divisors on the
triple overlaps and their ratios on double overlaps are units, the ratios form a cocycle. -/
def ofNonZeroDivisors {ι : Type u} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) (f : ∀ i, Γ(X, U i))
    (hunit : ∀ i j, ∃ v : Γ(X, U i ⊓ U j)ˣ,
      res (inf_le_left : U i ⊓ U j ≤ U i) (f i) =
        (v : Γ(X, U i ⊓ U j)) * res (inf_le_right : U i ⊓ U j ≤ U j) (f j))
    (hnzd : ∀ i j k, res (inf_le_right : U i ⊓ U j ⊓ U k ≤ U k) (f k) ∈
      nonZeroDivisors Γ(X, U i ⊓ U j ⊓ U k)) : LocalEquations X where
  ι := ι
  U := U
  iSup_eq_top := hU
  u i j := (hunit i j).choose
  cocycle i j k := by
    have hT₁ : U i ⊓ U j ⊓ U k ≤ U i ⊓ U j := inf_le_left
    have hT₂ : U i ⊓ U j ⊓ U k ≤ U j ⊓ U k := le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have hT₃ : U i ⊓ U j ⊓ U k ≤ U i ⊓ U k := le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have hTi : U i ⊓ U j ⊓ U k ≤ U i := inf_le_left.trans inf_le_left
    have hTj : U i ⊓ U j ⊓ U k ≤ U j := inf_le_left.trans inf_le_right
    have hTk : U i ⊓ U j ⊓ U k ≤ U k := inf_le_right
    have e₁ : res hTi (f i) = res hT₁ ((hunit i j).choose : Γ(X, U i ⊓ U j)) * res hTj (f j) := by
      have := congrArg (res hT₁) (hunit i j).choose_spec
      rwa [res_res_trans, map_mul, res_res_trans] at this
    have e₂ : res hTj (f j) = res hT₂ ((hunit j k).choose : Γ(X, U j ⊓ U k)) * res hTk (f k) := by
      have := congrArg (res hT₂) (hunit j k).choose_spec
      rwa [res_res_trans, map_mul, res_res_trans] at this
    have e₃ : res hTi (f i) = res hT₃ ((hunit i k).choose : Γ(X, U i ⊓ U k)) * res hTk (f k) := by
      have := congrArg (res hT₃) (hunit i k).choose_spec
      rwa [res_res_trans, map_mul, res_res_trans] at this
    have key : (res hT₁ ((hunit i j).choose : Γ(X, U i ⊓ U j)) *
        res hT₂ ((hunit j k).choose : Γ(X, U j ⊓ U k)) -
        res hT₃ ((hunit i k).choose : Γ(X, U i ⊓ U k))) * res hTk (f k) = 0 := by
      rw [sub_mul, mul_assoc, ← e₂, ← e₁, ← e₃, sub_self]
    exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp (hnzd i j k)).2 _ key)
  f := f
  f_eq i j := (hunit i j).choose_spec

end LocalEquations

end

end DeJongAlterations.StableModification.Projectivity
