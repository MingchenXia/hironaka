import DeJongAlterations.StableModification.Omega.Smooth
import DeJongAlterations.StableModification.Omega.NodeAlgebra
import DeJongAlterations.Algebra.NodeFamilyLocalization

/-!
# `Ω¹_{X/S}` near a node: the generator `du/u = -dv/v`

The node model computation of `lem:sm-omega-invertible` (M. Temkin, *Stable modification of
relative curves*, §1.2, T:1691–1712; PLAN-SM-GEOM chapter M): on the node model
`Spec R[u,v]/(uv - h) → Spec R` with `h` a non-zero-divisor, the differentials `du/u` on
`D(u)` and `-dv/v` on `D(v)` glue to a section `σ` of `Ω¹` over `D(u) ∪ D(v)`, and for every
basic open `D(g)` the map `Γ(D(g), 𝒪) → Γ(D(g) ∩ (D(u) ∪ D(v)), Ω¹)`, `c ↦ c σ`, is bijective.

* `Scheme.Modules.exists_glue₂`: gluing two sections of an `𝒪_X`-module.
* `TwoChartData`, `TwoChartData.exists_bijective`: the abstract computation on an affine open
  `W₀` with elements `u₀, v₀` such that `u₀v₀` comes from the base,
  `Γ(X, W₀) = Γ(D(u₀)) ∩ Γ(D(v₀))`, and `Ω¹` is free on `du₀` over `D(u₀)` and `D(u₀v₀)` and
  on `dv₀` over `D(v₀)`.
* `NodeChart`: an affine open `W ≤ f⁻¹ V` with `Γ(X, W) ≅ Γ(S, V)[u,v]/(uv - h)`, `h` a
  non-zero-divisor; `NodeChart.twoChartData`: every basic open `D(g) ⊆ W` satisfies the
  hypotheses (`nodeEqualizerData_node`, `nodeKaehler_bijective`), hence
  `NodeChart.exists_generator`; `NodeChart.basicOpen_coord_le_smoothLocus`: the coordinate
  charts `D(xᵢ)` lie in the smooth locus.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace DeJongAlterations.StableModification.Omega

variable {X S : Scheme.{u}}

/-- Two sections agreeing on the overlap glue to a section over the union. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.exists_glue₂ (N : X.Modules) {U₁ U₂ : X.Opens}
    (s₁ : Γ(N, U₁)) (s₂ : Γ(N, U₂))
    (h : N.presheaf.map (homOfLE inf_le_left : U₁ ⊓ U₂ ⟶ U₁).op s₁ =
      N.presheaf.map (homOfLE inf_le_right : U₁ ⊓ U₂ ⟶ U₂).op s₂) :
    ∃ s : Γ(N, U₁ ⊔ U₂), N.presheaf.map (homOfLE le_sup_left).op s = s₁ ∧
      N.presheaf.map (homOfLE le_sup_right).op s = s₂ := by
  let F : TopCat.Sheaf Ab X := ⟨N.presheaf, N.isSheaf⟩
  let U : Bool → X.Opens := fun b => cond b U₁ U₂
  let sf : ∀ b, Γ(N, U b) := fun b => Bool.rec (motive := fun b => Γ(N, U b)) s₂ s₁ b
  have hcomp : TopCat.Presheaf.IsCompatible F.1 U sf := by
    intro i j
    cases i <;> cases j
    · change N.presheaf.map _ s₂ = N.presheaf.map _ s₂
      rw [Subsingleton.elim (Opens.infLELeft (U false) (U false))
        (Opens.infLERight (U false) (U false))]
    · change N.presheaf.map _ s₂ = N.presheaf.map _ s₁
      have e : U₂ ⊓ U₁ ≤ U₁ ⊓ U₂ := le_of_eq (inf_comm U₂ U₁)
      have := congrArg (N.presheaf.map (homOfLE e).op) h
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
        ← Functor.map_comp] at this
      exact this.symm
    · change N.presheaf.map _ s₁ = N.presheaf.map _ s₂
      exact h
    · change N.presheaf.map _ s₁ = N.presheaf.map _ s₁
      rw [Subsingleton.elim (Opens.infLELeft (U true) (U true))
        (Opens.infLERight (U true) (U true))]
  have hcover : U₁ ⊔ U₂ ≤ iSup U := by
    rw [iSup_bool_eq]
    exact le_rfl
  obtain ⟨s, hs, -⟩ := F.existsUnique_gluing' U (U₁ ⊔ U₂)
    (fun b => homOfLE (by cases b <;> simp [U])) hcover sf hcomp
  exact ⟨s, hs true, hs false⟩

section TwoChart

variable (f : X ⟶ S)

/-- Restriction of sections of `𝒪_X` from an open to a smaller one. -/
abbrev res {U U' : X.Opens} (h : U' ≤ U) : Γ(X, U) →+* Γ(X, U') :=
  (X.presheaf.map (homOfLE h).op).hom

theorem res_res {U U' U'' : X.Opens} (h₁ : U' ≤ U) (h₂ : U'' ≤ U') (x : Γ(X, U)) :
    res h₂ (res h₁ x) = res (h₂.trans h₁) x := by
  change (X.presheaf.map _ ≫ X.presheaf.map _) x = _
  rw [← Functor.map_comp]
  rfl

theorem Ω_map_res_smul {N : X.Modules} {U U' : X.Opens} (h : U' ≤ U) (c : Γ(X, U))
    (m : Γ(N, U)) :
    N.presheaf.map (homOfLE h).op (c • m) = res h c • N.presheaf.map (homOfLE h).op m :=
  Scheme.Modules.map_smul N (homOfLE h) c m

theorem map_map_eq {N : X.Modules} {U U' U'' : X.Opens} (h₁ : U' ≤ U) (h₂ : U'' ≤ U')
    (m : Γ(N, U)) :
    N.presheaf.map (homOfLE h₂).op (N.presheaf.map (homOfLE h₁).op m) =
      N.presheaf.map (homOfLE (h₂.trans h₁)).op m := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

theorem sec_res {N : X.Modules} (d : RelDerivation f N) {U U' : X.Opens} (h : U' ≤ U)
    (x : Γ(X, U)) :
    d.sec U' (res h x) = N.presheaf.map (homOfLE h).op (d.sec U x) :=
  d.sec_map (homOfLE h) x

/-- The hypotheses of the two-chart computation on an affine open `W₀` with elements
`u₀, v₀` (the local form of a node: `Γ(X, W₀) = Γ(D(u₀)) ∩ Γ(D(v₀))`, `u₀ v₀` comes from the
base, `Ω¹` is free on `du₀` over `D(u₀)` and `D(u₀v₀)` and on `dv₀` over `D(v₀)`). -/
structure TwoChartData (V : S.Opens) (W₀ : X.Opens) (u₀ v₀ : Γ(X, W₀)) : Prop where
  isAffineOpen : IsAffineOpen W₀
  le : W₀ ≤ f ⁻¹ᵁ V
  base : ∃ r : Γ(S, V), u₀ * v₀ = f.appLE V W₀ le r
  equalizer : NodeEqualizerData u₀ v₀
  kaehler_u : Function.Bijective (fun c : Γ(X, X.basicOpen u₀) =>
    c • (universalDerivation f).sec _ (res (X.basicOpen_le u₀) u₀))
  kaehler_v : Function.Bijective (fun c : Γ(X, X.basicOpen v₀) =>
    c • (universalDerivation f).sec _ (res (X.basicOpen_le v₀) v₀))
  kaehler_uv : Function.Bijective (fun c : Γ(X, X.basicOpen (u₀ * v₀)) =>
    c • (universalDerivation f).sec _ (res (X.basicOpen_le (u₀ * v₀)) u₀))

namespace TwoChartData

variable {f} {V : S.Opens} {W₀ : X.Opens} {u₀ v₀ : Γ(X, W₀)} (H : TwoChartData f V W₀ u₀ v₀)
include H

/-- **The two-chart computation.** There is a section `σ` of `Ω¹_{X/S}` over `D(u₀) ∪ D(v₀)`
with `u₀ σ = du₀` on `D(u₀)` and `v₀ σ = -dv₀` on `D(v₀)` (so `σ = du₀/u₀ = -dv₀/v₀`), and
`c ↦ c σ` is a bijection from `Γ(X, W₀)` onto the sections of `Ω¹_{X/S}` over
`D(u₀) ∪ D(v₀)`. -/
theorem exists_bijective :
    ∃ σ : Γ(relativeDifferentials f, X.basicOpen u₀ ⊔ X.basicOpen v₀),
      res (X.basicOpen_le u₀) u₀ • (relativeDifferentials f).presheaf.map
          (homOfLE le_sup_left).op σ =
        (universalDerivation f).sec _ (res (X.basicOpen_le u₀) u₀) ∧
      res (X.basicOpen_le v₀) v₀ • (relativeDifferentials f).presheaf.map
          (homOfLE le_sup_right).op σ =
        -(universalDerivation f).sec _ (res (X.basicOpen_le v₀) v₀) ∧
      Function.Bijective (fun c : Γ(X, W₀) =>
        res (sup_le (X.basicOpen_le u₀) (X.basicOpen_le v₀)) c • σ) := by
  set Du := X.basicOpen u₀
  set Dv := X.basicOpen v₀
  set hu := X.basicOpen_le u₀
  set hv := X.basicOpen_le v₀
  set uU := res hu u₀
  set vV := res hv v₀
  have huU : IsUnit uU := X.toRingedSpace.isUnit_res_basicOpen u₀
  have hvV : IsUnit vV := X.toRingedSpace.isUnit_res_basicOpen v₀
  obtain ⟨r, hr⟩ := H.base
  -- the relation `u dv + v du = 0` on any open `U ≤ W₀`
  have hrel : ∀ {U : X.Opens} (hU : U ≤ W₀),
      res hU u₀ • (universalDerivation f).sec U (res hU v₀) +
        res hU v₀ • (universalDerivation f).sec U (res hU u₀) = 0 := by
    intro U hU
    rw [← RelDerivation.sec_mul, ← map_mul, hr, ← CommRingCat.comp_apply,
      Scheme.Hom.appLE_map]
    exact (universalDerivation f).sec_appLE _ r
  -- the two local generators agree on the overlap
  set σu : Γ(relativeDifferentials f, Du) := huU.unit⁻¹.val • (universalDerivation f).sec Du uU
  set σv : Γ(relativeDifferentials f, Dv) := -(hvV.unit⁻¹.val • (universalDerivation f).sec Dv vV)
  have hglue : (relativeDifferentials f).presheaf.map (homOfLE inf_le_left : Du ⊓ Dv ⟶ Du).op σu =
      (relativeDifferentials f).presheaf.map (homOfLE inf_le_right : Du ⊓ Dv ⟶ Dv).op σv := by
    have hI : Du ⊓ Dv ≤ W₀ := inf_le_left.trans hu
    set a := res (inf_le_left : Du ⊓ Dv ≤ Du) huU.unit⁻¹.val
    set b := res (inf_le_right : Du ⊓ Dv ≤ Dv) hvV.unit⁻¹.val
    have ha : a * res hI u₀ = 1 := by
      rw [← res_res hu inf_le_left, ← map_mul, IsUnit.val_inv_mul, map_one]
    have hb : b * res hI v₀ = 1 := by
      rw [← res_res hv inf_le_right, ← map_mul, IsUnit.val_inv_mul, map_one]
    simp only [σu, σv, map_neg, Ω_map_res_smul, uU, vV, ← sec_res f, res_res]
    have := hrel hI
    rw [eq_neg_iff_add_eq_zero]
    calc a • (universalDerivation f).sec _ (res hI u₀) +
          b • (universalDerivation f).sec _ (res hI v₀)
        = (a * b) • (res hI u₀ • (universalDerivation f).sec _ (res hI v₀) +
            res hI v₀ • (universalDerivation f).sec _ (res hI u₀)) := by
          rw [smul_add, smul_smul, smul_smul]
          rw [show a * b * res hI u₀ = b by rw [mul_right_comm, ha, one_mul],
            show a * b * res hI v₀ = a by rw [mul_assoc, hb, mul_one]]
          abel
      _ = 0 := by rw [this, smul_zero]
  obtain ⟨σ, hσu, hσv⟩ := (relativeDifferentials f).exists_glue₂ σu σv hglue
  refine ⟨σ, ?_, ?_, ?_⟩
  · rw [hσu, smul_smul, IsUnit.mul_val_inv, one_smul]
  · rw [hσv, smul_neg, smul_smul, IsUnit.mul_val_inv, one_smul]
  have hUW : Du ⊔ Dv ≤ W₀ := sup_le hu hv
  have hW₀ := H.isAffineOpen
  -- restricting `c • σ` to the two charts
  have hresU : ∀ c : Γ(X, W₀), (relativeDifferentials f).presheaf.map
      (homOfLE le_sup_left : Du ⟶ Du ⊔ Dv).op (res hUW c • σ) = res hu c • σu := by
    intro c
    rw [Ω_map_res_smul, hσu, res_res]
  have hresV : ∀ c : Γ(X, W₀), (relativeDifferentials f).presheaf.map
      (homOfLE le_sup_right : Dv ⟶ Du ⊔ Dv).op (res hUW c • σ) = res hv c • σv := by
    intro c
    rw [Ω_map_res_smul, hσv, res_res]
  have hinj_u : Function.Injective (res hu) := by
    let := (X.presheaf.map (homOfLE hu).op).hom.toAlgebra
    have := hW₀.isLocalization_basicOpen u₀
    exact IsLocalization.injective (M := Submonoid.powers u₀) Γ(X, Du)
      (Submonoid.powers_le.mpr H.equalizer.u_mem)
  let F : TopCat.Sheaf Ab X := ⟨(relativeDifferentials f).presheaf,
    (relativeDifferentials f).isSheaf⟩
  constructor
  · intro c c' hcc'
    have h1 := congrArg ((relativeDifferentials f).presheaf.map
      (homOfLE le_sup_left : Du ⟶ Du ⊔ Dv).op) hcc'
    simp only [hresU, σu, smul_smul] at h1
    have h2 := H.kaehler_u.1 h1
    apply hinj_u
    have := congrArg (· * uU) h2
    simp only [mul_assoc, IsUnit.val_inv_mul, mul_one] at this
    exact this
  · intro τ
    obtain ⟨a, ha⟩ := H.kaehler_u.2 ((relativeDifferentials f).presheaf.map
      (homOfLE le_sup_left : Du ⟶ Du ⊔ Dv).op τ)
    obtain ⟨b, hb⟩ := H.kaehler_v.2 ((relativeDifferentials f).presheaf.map
      (homOfLE le_sup_right : Dv ⟶ Du ⊔ Dv).op τ)
    simp only at ha hb
    set Duv := X.basicOpen (u₀ * v₀)
    have hDuv : Duv = Du ⊓ Dv := X.basicOpen_mul u₀ v₀
    have huv_u : Duv ≤ Du := hDuv.le.trans inf_le_left
    have huv_v : Duv ≤ Dv := hDuv.le.trans inf_le_right
    have huv : Duv ≤ W₀ := X.basicOpen_le _
    -- compare on `D(u₀v₀)`
    have hτ : (res huv_u a) • (universalDerivation f).sec _ (res huv u₀) =
        (res huv_v b) • (universalDerivation f).sec _ (res huv v₀) := by
      have e1 := congrArg ((relativeDifferentials f).presheaf.map (homOfLE huv_u).op) ha
      have e2 := congrArg ((relativeDifferentials f).presheaf.map (homOfLE huv_v).op) hb
      rw [map_map_eq, Ω_map_res_smul, ← sec_res f, res_res] at e1 e2
      rw [e1, e2]
    have hrel' := hrel huv
    have hkey : (res huv_u a * res huv u₀) • (universalDerivation f).sec _ (res huv u₀) =
        (-(res huv_v b * res huv v₀)) • (universalDerivation f).sec _ (res huv u₀) := by
      rw [mul_comm, ← smul_smul, hτ, smul_smul, mul_comm, ← smul_smul,
        eq_neg_of_add_eq_zero_left hrel', smul_neg, smul_smul, neg_smul, mul_comm]
    have hab := H.kaehler_uv.1 hkey
    -- the equalizer gives `c`
    let := (X.presheaf.map (homOfLE hu).op).hom.toAlgebra
    let := (X.presheaf.map (homOfLE hv).op).hom.toAlgebra
    let := (X.presheaf.map (homOfLE huv).op).hom.toAlgebra
    have := hW₀.isLocalization_basicOpen u₀
    have := hW₀.isLocalization_basicOpen v₀
    have := hW₀.isLocalization_basicOpen (u₀ * v₀)
    obtain ⟨c, hcu, hcv⟩ := H.equalizer.exists_eq (Au := Γ(X, Du)) (Av := Γ(X, Dv))
      (Auv := Γ(X, Duv)) (res huv_u) (res huv_v)
      (RingHom.ext fun x => res_res hu huv_u x) (RingHom.ext fun x => res_res hv huv_v x)
      (a * uU) (-(b * vV)) (by
        rw [map_mul, map_neg, map_mul, res_res, res_res]
        exact hab)
    refine ⟨c, ?_⟩
    simp only
    apply F.eq_of_locally_eq₂ (homOfLE le_sup_left) (homOfLE le_sup_right) le_rfl
    · change (relativeDifferentials f).presheaf.map _ (res hUW c • σ) =
        (relativeDifferentials f).presheaf.map _ τ
      rw [hresU, ← ha]
      change res hu c • σu = _
      rw [show res hu c = a * uU from hcu, mul_smul, smul_smul uU, IsUnit.mul_val_inv,
        one_smul]
    · change (relativeDifferentials f).presheaf.map _ (res hUW c • σ) =
        (relativeDifferentials f).presheaf.map _ τ
      rw [hresV, ← hb]
      change res hv c • σv = _
      rw [show res hv c = -(b * vV) from hcv, smul_neg, neg_smul, neg_neg, mul_smul,
        smul_smul vV, IsUnit.mul_val_inv, one_smul]

end TwoChartData

end TwoChart

section NodeChart

open DeJongAlterations.Algebra.NodeBlowupChart

/-- Ring isomorphisms transport the equalizer data. -/
theorem NodeEqualizerData.map_ringEquiv {A B : Type*} [CommRing A] [CommRing B] {u v : A}
    (H : NodeEqualizerData u v) (e : A ≃+* B) : NodeEqualizerData (e u) (e v) := by
  have hnzd : ∀ w ∈ nonZeroDivisors A, e w ∈ nonZeroDivisors B := by
    intro w hw
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    have : e.symm x * w = 0 := by
      apply e.injective
      rw [map_mul, e.apply_symm_apply, hx, map_zero]
    have := (mem_nonZeroDivisors_iff_right.mp hw) _ this
    simpa using congrArg e this
  refine ⟨hnzd u H.u_mem, hnzd v H.v_mem, fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hx
  have : v * e.symm x ∈ Ideal.span {u} := Ideal.mem_span_singleton'.mpr ⟨e.symm y, by
    apply e.injective
    simp [hy]⟩
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp (H.sat _ this)
  exact Ideal.mem_span_singleton'.mpr ⟨e z, by rw [← map_mul, hz, e.apply_symm_apply]⟩

variable (f : X ⟶ S)

/-- A *node chart* of `f : X ⟶ S`: affine opens `W ⊆ X`, `V ⊆ S` with `W ≤ f⁻¹ V` and an
isomorphism `Γ(S, V)[u,v]/(uv - h) ≅ Γ(X, W)` over `Γ(S, V)`, `h` a non-zero-divisor (the
Zariski-local form of the node model `Spec R[u,v]/(uv - h) → Spec R`). -/
structure NodeChart (V : S.Opens) (W : X.Opens) where
  isAffineOpen_W : IsAffineOpen W
  isAffineOpen_V : IsAffineOpen V
  le : W ≤ f ⁻¹ᵁ V
  /-- The equation of the node. -/
  h : Γ(S, V)
  h_mem : h ∈ nonZeroDivisors Γ(S, V)
  /-- The presentation of `Γ(X, W)`. -/
  equiv : Node Γ(S, V) h ≃+* Γ(X, W)
  equiv_algebraMap : ∀ r, equiv (algebraMap Γ(S, V) (Node Γ(S, V) h) r) = f.appLE V W le r

namespace NodeChart

variable {f} {V : S.Opens} {W : X.Opens} (C : NodeChart f V W)

/-- The coordinates `u = x₀`, `v = x₁` of the chart. -/
def coord (i : Fin 2) : Γ(X, W) := C.equiv (coordinate C.h i)

theorem coord_mul : C.coord 0 * C.coord 1 = f.appLE V W C.le C.h := by
  rw [coord, coord, ← map_mul, ← C.equiv_algebraMap]
  congr 1
  exact DeJongAlterations.Algebra.NodeDomain.nodeCoordinateProduct C.h

theorem nodeEqualizerData : NodeEqualizerData (C.coord 0) (C.coord 1) :=
  (nodeEqualizerData_node C.h_mem).map_ringEquiv C.equiv

/-- **Kähler differentials on a node chart.** On an affine open `W' ≤ W` whose ring of
sections is a localization of `Γ(X, W)` in which the coordinate `xᵢ` is a unit, `Ω¹_{X/S}` is
free on `dxᵢ`. -/
theorem kaehler_bijective {W' : X.Opens} (hW' : IsAffineOpen W') (hle : W' ≤ W)
    (M : Submonoid Γ(X, W))
    (hM : letI := (res hle).toAlgebra; IsLocalization M Γ(X, W')) (i : Fin 2)
    (hi : IsUnit (res hle (C.coord i))) :
    Function.Bijective (fun c : Γ(X, W') =>
      c • (universalDerivation f).sec W' (res hle (C.coord i))) := by
  let φ := f.appLE V W' (hle.trans C.le)
  let := φ.hom.toAlgebra
  let := ((res hle).comp C.equiv.toRingHom).toAlgebra
  have htower : IsScalarTower Γ(S, V) (Node Γ(S, V) C.h) Γ(X, W') :=
    IsScalarTower.of_algebraMap_eq (R := Γ(S, V)) (S := Node Γ(S, V) C.h) (A := Γ(X, W'))
      (fun r => by
        change φ r = res hle (C.equiv (algebraMap _ _ r))
        rw [C.equiv_algebraMap, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map])
  let := (res hle).toAlgebra
  have hloc : IsLocalization (M.map C.equiv.symm.toMonoidHom) Γ(X, W') := by
    have := IsLocalization.isLocalization_of_base_ringEquiv M Γ(X, W') C.equiv.symm
    convert this
    all_goals rfl
  have hbij := nodeKaehler_bijective (R := Γ(S, V)) (S := Γ(X, W')) C.h
    (M.map C.equiv.symm.toMonoidHom) i hi
  have heq := sectionsLinearMap_bijective f hW' C.isAffineOpen_V (hle.trans C.le)
  have hpt : ∀ c : Γ(X, W'), c • (universalDerivation f).sec W' (res hle (C.coord i)) =
      sectionsLinearMap f (hle.trans C.le) (c • KaehlerDifferential.D Γ(S, V) Γ(X, W')
        (algebraMap (Node Γ(S, V) C.h) Γ(X, W') (coordinate C.h i))) := by
    intro c
    refine Eq.trans ?_ ((sectionsLinearMap f (hle.trans C.le)).hom.map_smul c _).symm
    congr 1
    exact (sectionsLinearMap_d f (hle.trans C.le) (res hle (C.coord i))).symm
  have hcomp : (fun c : Γ(X, W') => c • (universalDerivation f).sec W' (res hle (C.coord i))) =
      (sectionsLinearMap f (hle.trans C.le)) ∘ (fun c : Γ(X, W') =>
        c • KaehlerDifferential.D Γ(S, V) Γ(X, W')
          (algebraMap (Node Γ(S, V) C.h) Γ(X, W') (coordinate C.h i))) :=
    funext hpt
  rw [hcomp]
  exact heq.comp hbij

omit C in
/-- Sections over `D_{D(g)}(a|)` are the localization of `Γ(X, W)` at `g a`. -/
theorem isLocalization_basicOpen_res (hW : IsAffineOpen W) (g a : Γ(X, W)) :
    letI := (res ((X.basicOpen_le (res (X.basicOpen_le g) a)).trans (X.basicOpen_le g))).toAlgebra
    IsLocalization (Submonoid.powers (g * a))
      Γ(X, X.basicOpen (res (X.basicOpen_le g) a)) := by
  let hg := X.basicOpen_le g
  let ha := X.basicOpen_le (res hg a)
  let : Algebra Γ(X, W) Γ(X, X.basicOpen g) := (res hg).toAlgebra
  let : Algebra Γ(X, X.basicOpen g) Γ(X, X.basicOpen (res hg a)) := (res ha).toAlgebra
  let : Algebra Γ(X, W) Γ(X, X.basicOpen (res hg a)) := (res (ha.trans hg)).toAlgebra
  have : IsScalarTower Γ(X, W) Γ(X, X.basicOpen g) Γ(X, X.basicOpen (res hg a)) :=
    IsScalarTower.of_algebraMap_eq (fun x => (res_res hg ha x).symm)
  have := hW.isLocalization_basicOpen g
  have := (hW.basicOpen g).isLocalization_basicOpen (res hg a)
  exact IsLocalization.Away.mul' Γ(X, X.basicOpen g) Γ(X, X.basicOpen (res hg a)) g a

/-- **Every basic open of a node chart satisfies the two-chart hypotheses.** -/
theorem twoChartData (g : Γ(X, W)) :
    TwoChartData f V (X.basicOpen g) (res (X.basicOpen_le g) (C.coord 0))
      (res (X.basicOpen_le g) (C.coord 1)) := by
  have hW := C.isAffineOpen_W
  set hg := X.basicOpen_le g
  have hbo : ∀ i : Fin 2, X.basicOpen (res hg (C.coord i)) ≤ X.basicOpen (C.coord i) := by
    intro i
    exact (Scheme.basicOpen_res X (C.coord i) (homOfLE hg).op).le.trans inf_le_right
  have hkaehler : ∀ i : Fin 2, Function.Bijective (fun c : Γ(X, X.basicOpen (res hg (C.coord i))) =>
      c • (universalDerivation f).sec _
        (res (X.basicOpen_le (res hg (C.coord i))) (res hg (C.coord i)))) := by
    intro i
    have hle := (X.basicOpen_le (res hg (C.coord i))).trans hg
    have := C.kaehler_bijective ((hW.basicOpen g).basicOpen (res hg (C.coord i))) hle
      (Submonoid.powers (g * C.coord i)) (isLocalization_basicOpen_res hW g (C.coord i)) i
      (isUnit_map_of_le_basicOpen _ (hbo i) hle)
    simpa only [res_res] using this
  refine ⟨hW.basicOpen g, hg.trans C.le, ⟨C.h, ?_⟩, ?_, hkaehler 0, hkaehler 1, ?_⟩
  · rw [← map_mul, coord_mul, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  · let := (res hg).toAlgebra
    have := hW.isLocalization_basicOpen g
    exact C.nodeEqualizerData.isLocalization (Submonoid.powers g)
  · have e : res hg (C.coord 0) * res hg (C.coord 1) = res hg (C.coord 0 * C.coord 1) :=
      (map_mul _ _ _).symm
    rw [e]
    have hle := (X.basicOpen_le (res hg (C.coord 0 * C.coord 1))).trans hg
    have hu : X.basicOpen (res hg (C.coord 0 * C.coord 1)) ≤ X.basicOpen (C.coord 0) :=
      (Scheme.basicOpen_res X _ (homOfLE hg).op).le.trans
        (inf_le_right.trans (X.basicOpen_mul (C.coord 0) (C.coord 1)).le |>.trans inf_le_left)
    have := C.kaehler_bijective ((hW.basicOpen g).basicOpen (res hg (C.coord 0 * C.coord 1)))
      hle (Submonoid.powers (g * (C.coord 0 * C.coord 1)))
      (isLocalization_basicOpen_res hW g _) 0 (isUnit_map_of_le_basicOpen _ hu hle)
    simpa only [res_res] using this

/-- **The coordinate charts are smooth.** `D(xᵢ) ⊆ W` lies in the smooth locus of `f`
(`D(xᵢ)` is the spectrum of a Laurent polynomial ring over `Γ(S, V)`). -/
theorem basicOpen_coord_le_smoothLocus [LocallyOfFinitePresentation f] (i : Fin 2) :
    X.basicOpen (C.coord i) ≤ f.smoothLocus := by
  intro x hx
  have hW := C.isAffineOpen_W
  set W' := X.basicOpen (C.coord i)
  have hW' : IsAffineOpen W' := hW.basicOpen _
  have hW'V : W' ≤ f ⁻¹ᵁ V := (X.basicOpen_le _).trans C.le
  have hle : W' ≤ W := X.basicOpen_le _
  let := (f.appLE V W' hW'V).hom.toAlgebra
  -- `Γ(X, W')` is the localization of the node algebra at `xᵢ`
  let := ((res hle).comp C.equiv.toRingHom).toAlgebra
  have htower : IsScalarTower Γ(S, V) (Node Γ(S, V) C.h) Γ(X, W') :=
    IsScalarTower.of_algebraMap_eq (R := Γ(S, V)) (S := Node Γ(S, V) C.h) (A := Γ(X, W'))
      (fun r => by
        change f.appLE V W' hW'V r = res hle (C.equiv (algebraMap _ _ r))
        rw [C.equiv_algebraMap, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map])
  let := (res hle).toAlgebra
  have hloc0 := hW.isLocalization_basicOpen (C.coord i)
  have hloc : IsLocalization (Submonoid.powers (coordinate C.h i)) Γ(X, W') := by
    have := IsLocalization.isLocalization_of_base_ringEquiv (Submonoid.powers (C.coord i))
      Γ(X, W') C.equiv.symm
    convert this
    · rw [Submonoid.map_powers]
      simp [coord]
    all_goals rfl
  let e : Localization.Away (coordinate C.h i) ≃ₐ[Node Γ(S, V) C.h] Γ(X, W') :=
    IsLocalization.algEquiv (Submonoid.powers (coordinate C.h i)) _ _
  have hsm : Algebra.Smooth Γ(S, V) (Localization.Away (coordinate C.h i)) :=
    DeJongAlterations.Algebra.NodeFamilyLocalization.coordinateOpen_smooth_of_index C.h i
  have : Algebra.Smooth Γ(S, V) Γ(X, W') :=
    Algebra.Smooth.of_equiv (e.restrictScalars Γ(S, V))
  rw [Scheme.Hom.mem_smoothLocus]
  exact (formallySmooth_stalkMap_iff V C.isAffineOpen_V W' hW' hW'V hx).mpr
    (by rw [Algebra.smoothLocus_eq_univ]; trivial)

/-- The coordinate `xᵢ` restricted to the basic open `D(g)`. -/
abbrev coordAt (g : Γ(X, W)) (i : Fin 2) : Γ(X, X.basicOpen g) := res (X.basicOpen_le g) (C.coord i)

/-- **The node model computation** (blueprint `prop:sm-omega-node`). On a node chart, for every
`g ∈ Γ(X, W)`, with `u = x₀|_{D(g)}` and `v = x₁|_{D(g)}`, there is a section `σ` of `Ω¹_{X/S}`
over `D(u) ∪ D(v) = D(g) ∩ (D(x₀) ∪ D(x₁))` with `u σ = du` and `v σ = -dv` (`σ = du/u = -dv/v`),
and `c ↦ c σ` is a bijection `Γ(X, D(g)) ≅ Γ(D(u) ∪ D(v), Ω¹_{X/S})`. -/
theorem exists_generator (g : Γ(X, W)) :
    ∃ σ : Γ(relativeDifferentials f, X.basicOpen (C.coordAt g 0) ⊔ X.basicOpen (C.coordAt g 1)),
      res (X.basicOpen_le (C.coordAt g 0)) (C.coordAt g 0) •
          (relativeDifferentials f).presheaf.map (homOfLE le_sup_left).op σ =
        (universalDerivation f).sec _ (res (X.basicOpen_le (C.coordAt g 0)) (C.coordAt g 0)) ∧
      res (X.basicOpen_le (C.coordAt g 1)) (C.coordAt g 1) •
          (relativeDifferentials f).presheaf.map (homOfLE le_sup_right).op σ =
        -(universalDerivation f).sec _ (res (X.basicOpen_le (C.coordAt g 1)) (C.coordAt g 1)) ∧
      Function.Bijective (fun c : Γ(X, X.basicOpen g) =>
        res (sup_le (X.basicOpen_le (C.coordAt g 0)) (X.basicOpen_le (C.coordAt g 1))) c • σ) :=
  (C.twoChartData g).exists_bijective

end NodeChart

end NodeChart

end DeJongAlterations.StableModification.Omega
