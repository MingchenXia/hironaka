import DeJongAlterations.StableModification.Omega.EtaleDescent
import DeJongAlterations.StableModification.Curves.SemistableOpenNode
import DeJongAlterations.Algebra.NodeFamilyBaseChange
import Mathlib.RingTheory.MvPolynomial.Localization

/-!
# Étale node charts on spectra

Construction of the étale node charts used in step 4 of `lem:sm-omega-invertible` (blueprint
`sm-omega-invertible.tex`, `lem:sm-omega-etale-chart-spec`; M. Temkin, *Stable modification of
relative curves*, §1.2, T:1700–1712; the étale-local form of a node is Stacks, Tag 0CBY, produced
by lane SS3 as `Curves.SemistableNormal.exists_away_etale_nodeChart`).

* `EtaleNodeChart.restrictBasicOpen`: an étale node chart restricts to basic opens.
* `EtaleNodeChart.ofSpec`: algebraic data `φ : Γ(X, W) → T`, `ν : O[u,v]/(uv - c) → T` étale and
  compatible over `Γ(S, V)` give an étale node chart of `Spec T → X → S` on `Spec T`
  (`appLE_SpecMap_comp_fromSpec` computes the sections map of `Spec T → W ⊆ X`).
* `algebraMap_ne_zero_of_isDomain`: if the local ring of `O[u,v]/(uv - c)` at a prime `P ∋ u, v`
  is a domain, then `c ≠ 0` in the local ring of `O` at `P ∩ O` (the maps `nodeLineMap`,
  `u ↦ X, v ↦ 0`).
* `exists_notMem_mem_nonZeroDivisors_away`: over a Noetherian ring, a non-zero-divisor of a local
  ring is a non-zero-divisor on a basic open.
* `nodeLocalizationMap`, `isLocalization_nodeLocalizationMap`, `chartAwayMap`,
  `etale_chartAwayMap`: localizing `O` at `s` (`O_s[u,v]/(uv - c)` is the localization of
  `O[u,v]/(uv - c)` at `s`), the chart ring becomes `T_s`, étale over `O_s[u,v]/(uv - c)`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open DeJongAlterations.Algebra.NodeBlowupChart

universe u

namespace DeJongAlterations.StableModification.Omega


theorem appLE_SpecMap_comp_fromSpec {X : Scheme.{u}} {T : CommRingCat.{u}} {V : X.Opens}
    (hV : IsAffineOpen V) (g : Γ(X, V) ⟶ T) (e) :
    (Spec.map g ≫ hV.fromSpec).appLE V ⊤ e = g ≫ (Scheme.ΓSpecIso T).inv := by
  rw [Scheme.Hom.comp_appLE, hV.fromSpec_app_self, Category.assoc]
  erw [Scheme.Hom.map_appLE]
  rw [Scheme.ΓSpecIso_inv_naturality]
  rfl

theorem appLE_eq_of_eq_SpecMap_comp_fromSpec {X : Scheme.{u}} {T : CommRingCat.{u}} {V : X.Opens}
    (hV : IsAffineOpen V) (g : Γ(X, V) ⟶ T) {h : Spec T ⟶ X} (hh : h = Spec.map g ≫ hV.fromSpec)
    (e) : h.appLE V ⊤ e = g ≫ (Scheme.ΓSpecIso T).inv := by
  subst hh
  exact appLE_SpecMap_comp_fromSpec hV g e

variable {X S : Scheme.{u}}

namespace EtaleNodeChart

variable {f : X ⟶ S} {V : S.Opens} {W : X.Opens}

/-- The restriction of an étale node chart to a basic open. -/
def restrictBasicOpen (C : EtaleNodeChart f V W) (h : Γ(X, W)) :
    EtaleNodeChart f V (X.basicOpen h) where
  isAffineOpen_W := C.isAffineOpen_W.basicOpen h
  isAffineOpen_V := C.isAffineOpen_V
  le := (X.basicOpen_le h).trans C.le
  O := C.O
  c := C.c
  c_mem := C.c_mem
  toNode := (res (X.basicOpen_le h)).comp C.toNode
  etale_toNode := by
    have hloc := C.isAffineOpen_W.isLocalization_basicOpen h
    let := (res (X.basicOpen_le h)).toAlgebra
    have : Algebra.Etale Γ(X, W) Γ(X, X.basicOpen h) := Algebra.Etale.of_isLocalizationAway h
    exact RingHom.Etale.stableUnderComposition _ _ C.etale_toNode this
  compat r := by
    rw [RingHom.comp_apply, C.compat, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

end EtaleNodeChart

/-- **An étale node chart on `Spec T`** from algebraic data: an étale-type map
`O[u,v]/(uv - c) → T` compatible with `φ : Γ(X, W) → T`, where `ψ = Spec φ ≫ (W ⊆ X)`. -/
def EtaleNodeChart.ofSpec (f : X ⟶ S) {V : S.Opens} (hV : IsAffineOpen V) {W : X.Opens}
    (hW : IsAffineOpen W) (hWV : W ≤ f ⁻¹ᵁ V) {T : Type u} [CommRing T] (φ : Γ(X, W) →+* T)
    {ψ : Spec (CommRingCat.of T) ⟶ X} (hψ : ψ = Spec.map (CommRingCat.ofHom φ) ≫ hW.fromSpec)
    (O : Type u) [CommRing O] [Algebra Γ(S, V) O] [Algebra.Etale Γ(S, V) O]
    (c : O) (hc : c ∈ nonZeroDivisors O) (ν : Node O c →+* T) (hν : ν.Etale)
    (hcompat : ∀ r, ν (algebraMap O (Node O c) (algebraMap Γ(S, V) O r)) =
      φ (f.appLE V W hWV r)) :
    EtaleNodeChart (ψ ≫ f) V ⊤ where
  isAffineOpen_W := isAffineOpen_top _
  isAffineOpen_V := hV
  le := by
    intro y _
    subst hψ
    change f ((Spec.map (CommRingCat.ofHom φ) ≫ hW.fromSpec) y) ∈ V
    apply hWV
    rw [Scheme.Hom.comp_apply]
    have := Set.mem_range_self (f := hW.fromSpec) ((Spec.map (CommRingCat.ofHom φ)) y)
    rwa [hW.range_fromSpec] at this
  O := O
  c := c
  c_mem := hc
  toNode := (Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom.comp ν
  etale_toNode := RingHom.Etale.stableUnderComposition _ _ hν
    (RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of T)).inv))
  compat r := by
    rw [RingHom.comp_apply, hcompat]
    have h1 : ψ ≫ f = Spec.map (f.appLE V W hWV ≫ CommRingCat.ofHom φ) ≫ hV.fromSpec := by
      rw [hψ, Spec.map_comp, Category.assoc, Category.assoc,
        IsAffineOpen.SpecMap_appLE_fromSpec f hV hW hWV]
    rw [appLE_eq_of_eq_SpecMap_comp_fromSpec hV _ h1]
    rfl



section NodeLine

variable {O : Type u} [CommRing O] (c : O) {L : Type*} [CommRing L] (g : O →+* L)

/-- The map `O[u,v]/(uv - c) → L[X]` sending the `i`-th coordinate to `X` and the other one to
`0`, for `g : O → L` killing `c`. -/
def nodeLineMap (hc : g c = 0) (i : Fin 2) : Node O c →+* Polynomial L :=
  Ideal.Quotient.lift (DeJongAlterations.Algebra.NodeChart.uChartIdeal O c)
    (MvPolynomial.eval₂Hom (Polynomial.C.comp g) (fun j => if j = i then Polynomial.X else 0))
    (by
      intro p hp
      rw [DeJongAlterations.Algebra.NodeChart.uChartIdeal, Ideal.mem_span_singleton] at hp
      obtain ⟨q, rfl⟩ := hp
      rw [map_mul]
      apply mul_eq_zero_of_left
      fin_cases i <;> simp [hc])

theorem nodeLineMap_coordinate (hc : g c = 0) (i j : Fin 2) :
    nodeLineMap c g hc i (coordinate c j) = if j = i then Polynomial.X else 0 := by
  simp [nodeLineMap, coordinate]

theorem nodeLineMap_algebraMap (hc : g c = 0) (i : Fin 2) (o : O) :
    nodeLineMap c g hc i (algebraMap O (Node O c) o) = Polynomial.C (g o) := by
  rw [← Ideal.Quotient.mk_algebraMap, nodeLineMap, Ideal.Quotient.lift_mk,
    MvPolynomial.algebraMap_eq, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
  rfl

theorem eval_zero_nodeLineMap_mk (hc : g c = 0) (i : Fin 2) (p : MvPolynomial (Fin 2) O) :
    Polynomial.eval 0 (nodeLineMap c g hc i (Ideal.Quotient.mk _ p)) =
      g (MvPolynomial.constantCoeff p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [nodeLineMap]
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, Polynomial.eval_mul, hp, MvPolynomial.constantCoeff_X, mul_zero]
    simp [nodeLineMap]
    fin_cases i <;> fin_cases j <;> simp

theorem mk_sub_algebraMap_constantCoeff_mem (p : MvPolynomial (Fin 2) O) :
    Ideal.Quotient.mk (DeJongAlterations.Algebra.NodeChart.uChartIdeal O c) p -
      algebraMap O (Node O c) (MvPolynomial.constantCoeff p) ∈
        Ideal.span {coordinate c 0, coordinate c 1} := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq,
      MvPolynomial.constantCoeff_C, sub_self]
    exact Ideal.zero_mem _
  | add p q hp hq =>
    rw [map_add, map_add, map_add, add_sub_add_comm]
    exact Ideal.add_mem _ hp hq
  | mul_X p j hp =>
    rw [map_mul MvPolynomial.constantCoeff, MvPolynomial.constantCoeff_X, mul_zero, map_zero,
      sub_zero, map_mul]
    apply Ideal.mul_mem_left
    apply Ideal.subset_span
    fin_cases j
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ rfl

end NodeLine

section NodeDomain

variable {O : Type u} [CommRing O] (c : O)

/-- **The node parameter is non-zero near a normal point of the node.** If the local ring of
`O[u,v]/(uv - c)` at a prime `P ∋ u, v` is a domain, then `c ≠ 0` in the local ring of `O` at
`P ∩ O`. -/
theorem algebraMap_ne_zero_of_isDomain (P : Ideal (Node O c)) [P.IsPrime]
    (hu : coordinate c 0 ∈ P) (hv : coordinate c 1 ∈ P)
    [IsDomain (Localization.AtPrime P)] :
    algebraMap O (Localization.AtPrime (P.comap (algebraMap O (Node O c)))) c ≠ 0 := by
  set 𝔮 := P.comap (algebraMap O (Node O c))
  set L := Localization.AtPrime 𝔮
  intro h0
  obtain ⟨⟨s, hs⟩, hsc⟩ := (IsLocalization.map_eq_zero_iff 𝔮.primeCompl L c).mp h0
  have hs' : algebraMap O (Node O c) s ∈ P.primeCompl := hs
  have huv : algebraMap (Node O c) (Localization.AtPrime P) (coordinate c 0) *
      algebraMap (Node O c) (Localization.AtPrime P) (coordinate c 1) = 0 := by
    rw [← map_mul, coordinate, coordinate,
      DeJongAlterations.Algebra.NodeDomain.nodeCoordinateProduct]
    refine (IsLocalization.map_eq_zero_iff P.primeCompl _ _).mpr ⟨⟨_, hs'⟩, ?_⟩
    change algebraMap O (Node O c) s * algebraMap O _ c = 0
    rw [← map_mul, hsc, map_zero]
  -- the value at the origin of an element outside `P` is a unit of `L`
  have hη : ∀ t : Node O c, t ∉ P → ∀ i, Polynomial.eval 0
      (nodeLineMap c (algebraMap O L) h0 i t) ≠ 0 := by
    intro t ht i
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective t
    rw [eval_zero_nodeLineMap_mk]
    have hmem := mk_sub_algebraMap_constantCoeff_mem c p
    have hspan : Ideal.span {coordinate c 0, coordinate c 1} ≤ P := by
      rw [Ideal.span_le]
      rintro x (rfl | rfl)
      · exact hu
      · exact hv
    have hcP : algebraMap O (Node O c) (MvPolynomial.constantCoeff p) ∉ P := by
      intro hcP
      apply ht
      have := P.add_mem (hspan hmem) hcP
      rwa [sub_add_cancel] at this
    have hunit : IsUnit (algebraMap O L (MvPolynomial.constantCoeff p)) :=
      IsLocalization.map_units L (⟨_, hcP⟩ : 𝔮.primeCompl)
    exact hunit.ne_zero
  rcases mul_eq_zero.mp huv with h | h
  · obtain ⟨⟨t, ht⟩, htu⟩ := (IsLocalization.map_eq_zero_iff P.primeCompl _ _).mp h
    have h1 := congrArg (nodeLineMap c (algebraMap O L) h0 0) htu
    rw [map_mul, map_zero, nodeLineMap_coordinate] at h1
    simp only [if_true] at h1
    have h2 : nodeLineMap c (algebraMap O L) h0 0 t = 0 :=
      (mul_right_mem_nonZeroDivisors_eq_zero_iff Polynomial.X_mem_nonzeroDivisors).mp h1
    exact hη t ht 0 (by rw [h2, Polynomial.eval_zero])
  · obtain ⟨⟨t, ht⟩, htv⟩ := (IsLocalization.map_eq_zero_iff P.primeCompl _ _).mp h
    have h1 := congrArg (nodeLineMap c (algebraMap O L) h0 1) htv
    rw [map_mul, map_zero, nodeLineMap_coordinate] at h1
    simp only [if_true] at h1
    have h2 : nodeLineMap c (algebraMap O L) h0 1 t = 0 :=
      (mul_right_mem_nonZeroDivisors_eq_zero_iff Polynomial.X_mem_nonzeroDivisors).mp h1
    exact hη t ht 1 (by rw [h2, Polynomial.eval_zero])

end NodeDomain

section Annihilator

/-- **Spreading out a non-zero-divisor.** Over a Noetherian ring, an element which is a
non-zero-divisor in the local ring at `𝔮` is a non-zero-divisor on some basic open `D(s) ∋ 𝔮`. -/
theorem exists_notMem_mem_nonZeroDivisors_away {O : Type u} [CommRing O] [IsNoetherianRing O]
    (c : O) (𝔮 : Ideal O) [𝔮.IsPrime]
    (hc : algebraMap O (Localization.AtPrime 𝔮) c ∈ nonZeroDivisors (Localization.AtPrime 𝔮)) :
    ∃ s ∉ 𝔮, algebraMap O (Localization.Away s) c ∈ nonZeroDivisors (Localization.Away s) := by
  let I : Ideal O := (Ideal.span {c}).annihilator
  have hI : ∀ x ∈ I, ∃ s ∉ 𝔮, s * x = 0 := by
    intro x hx
    have hxc : x * c = 0 := (Submodule.mem_annihilator_span_singleton c x).mp hx
    have h1 : algebraMap O (Localization.AtPrime 𝔮) x = 0 := by
      apply (mul_right_mem_nonZeroDivisors_eq_zero_iff hc).mp
      rw [← map_mul, hxc, map_zero]
    obtain ⟨⟨s, hs⟩, hsx⟩ := (IsLocalization.map_eq_zero_iff 𝔮.primeCompl _ x).mp h1
    exact ⟨s, hs, hsx⟩
  obtain ⟨s, hs, hsI⟩ := Curves.SemistableOpen.exists_notMem_forall_mul_eq_zero I
    (IsNoetherian.noetherian I) 𝔮 hI
  refine ⟨s, hs, mem_nonZeroDivisors_iff_right.mpr fun y hy => ?_⟩
  obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers s) y
  rw [← IsLocalization.mk'_one (M := Submonoid.powers s) (Localization.Away s) c,
    ← IsLocalization.mk'_mul, mul_one, IsLocalization.mk'_eq_zero_iff] at hy
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := hy
  have hmem : s ^ m * a ∈ I := by
    apply (Submodule.mem_annihilator_span_singleton c _).mpr
    change s ^ m * a * c = 0
    rw [mul_assoc]
    exact hm
  have h2 := hsI _ hmem
  rw [IsLocalization.mk'_eq_zero_iff]
  refine ⟨⟨s ^ (m + 1), m + 1, rfl⟩, ?_⟩
  change s ^ (m + 1) * a = 0
  rw [pow_succ', mul_assoc]
  exact h2

end Annihilator

section NodeLocalization

variable {O : Type u} [CommRing O] (c : O) (s : O)

/-- The map `O[u,v]/(uv - c) → O_s[u,v]/(uv - c)`. -/
def nodeLocalizationMap : Node O c →+* Node (Localization.Away s) (algebraMap O _ c) :=
  Ideal.quotientMap _ (MvPolynomial.map (algebraMap O (Localization.Away s))) (by
    rw [← Ideal.map_le_iff_le_comap, DeJongAlterations.Algebra.NodeFamilyBaseChange.nodeIdeal_map])

theorem nodeLocalizationMap_mk (p : MvPolynomial (Fin 2) O) :
    nodeLocalizationMap c s (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap O (Localization.Away s)) p) :=
  Ideal.quotientMap_mk

theorem nodeLocalizationMap_coordinate (i : Fin 2) :
    nodeLocalizationMap c s (coordinate c i) = coordinate (algebraMap O _ c) i := by
  rw [coordinate, nodeLocalizationMap_mk, MvPolynomial.map_X]
  rfl

theorem nodeLocalizationMap_algebraMap (o : O) :
    nodeLocalizationMap c s (algebraMap O (Node O c) o) =
      algebraMap (Localization.Away s) _ (algebraMap O (Localization.Away s) o) := by
  rw [← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq, nodeLocalizationMap_mk,
    MvPolynomial.map_C, ← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]

attribute [local instance] MvPolynomial.algebraMvPolynomial in
/-- `O_s[u,v]/(uv - c)` is the localization of `O[u,v]/(uv - c)` at `s`. -/
theorem isLocalization_nodeLocalizationMap :
    letI := (nodeLocalizationMap c s).toAlgebra
    IsLocalization.Away (algebraMap O (Node O c) s)
      (Node (Localization.Away s) (algebraMap O _ c)) := by
  let := (nodeLocalizationMap c s).toAlgebra
  have h := IsLocalization.of_surjective ((Submonoid.powers s).map
      (MvPolynomial.C (σ := Fin 2) (R := O)))
    (MvPolynomial (Fin 2) (Localization.Away s))
    (Ideal.Quotient.mk (DeJongAlterations.Algebra.NodeChart.uChartIdeal O c))
    Ideal.Quotient.mk_surjective
    (Ideal.Quotient.mk (DeJongAlterations.Algebra.NodeChart.uChartIdeal (Localization.Away s)
      (algebraMap O _ c))) Ideal.Quotient.mk_surjective
    (by
      ext p
      · simp only [RingHom.comp_apply]
        exact (nodeLocalizationMap_mk c s _).symm
      · simp only [RingHom.comp_apply]
        exact (nodeLocalizationMap_mk c s _).symm)
    (by
      rw [Ideal.mk_ker, Ideal.mk_ker,
        ← DeJongAlterations.Algebra.NodeFamilyBaseChange.nodeIdeal_map]
      rfl)
  rw [Submonoid.map_powers, Submonoid.map_powers] at h
  have e : algebraMap O (Node O c) s =
      Ideal.Quotient.mk (DeJongAlterations.Algebra.NodeChart.uChartIdeal O c)
        (MvPolynomial.C s) := by
    rw [← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq]
  rw [IsLocalization.Away, e]
  exact h

end NodeLocalization

section ChartLocalization

variable {O : Type u} [CommRing O] (c : O) (s : O) (T : Type u) [CommRing T]
  [Algebra (Node O c) T]

/-- The localization of the chart ring at `s ∈ O`. -/
abbrev chartAway := Localization.Away (algebraMap (Node O c) T (algebraMap O (Node O c) s))

/-- The map `O_s[u,v]/(uv - c) → T_s` induced by `O[u,v]/(uv - c) → T`. -/
def chartAwayMap : Node (Localization.Away s) (algebraMap O _ c) →+* chartAway c s T :=
  letI := (nodeLocalizationMap c s).toAlgebra
  haveI := isLocalization_nodeLocalizationMap c s
  IsLocalization.Away.lift (algebraMap O (Node O c) s)
    (g := algebraMap (Node O c) (chartAway c s T))
    (by
      rw [IsScalarTower.algebraMap_apply (Node O c) T (chartAway c s T)]
      exact IsLocalization.Away.algebraMap_isUnit _)

theorem chartAwayMap_nodeLocalizationMap (x : Node O c) :
    chartAwayMap c s T (nodeLocalizationMap c s x) = algebraMap (Node O c) (chartAway c s T) x := by
  let := (nodeLocalizationMap c s).toAlgebra
  have := isLocalization_nodeLocalizationMap c s
  exact IsLocalization.Away.lift_eq (algebraMap O (Node O c) s) _ x

theorem chartAwayMap_coordinate (i : Fin 2) :
    chartAwayMap c s T (coordinate (algebraMap O _ c) i) =
      algebraMap T (chartAway c s T) (algebraMap (Node O c) T (coordinate c i)) := by
  rw [← nodeLocalizationMap_coordinate, chartAwayMap_nodeLocalizationMap,
    IsScalarTower.algebraMap_apply (Node O c) T (chartAway c s T)]

theorem chartAwayMap_algebraMap (o : O) :
    chartAwayMap c s T (algebraMap (Localization.Away s) _ (algebraMap O (Localization.Away s) o)) =
      algebraMap T (chartAway c s T) (algebraMap (Node O c) T (algebraMap O (Node O c) o)) := by
  rw [← nodeLocalizationMap_algebraMap, chartAwayMap_nodeLocalizationMap,
    IsScalarTower.algebraMap_apply (Node O c) T (chartAway c s T)]

/-- **Étaleness survives localizing the node parameter ring.** -/
theorem etale_chartAwayMap [Algebra.Etale (Node O c) T] : (chartAwayMap c s T).Etale := by
  let := (nodeLocalizationMap c s).toAlgebra
  have := isLocalization_nodeLocalizationMap c s
  let := (chartAwayMap c s T).toAlgebra
  have : IsScalarTower (Node O c) (Node (Localization.Away s) (algebraMap O _ c))
      (chartAway c s T) :=
    IsScalarTower.of_algebraMap_eq (fun x => (chartAwayMap_nodeLocalizationMap c s T x).symm)
  have : Algebra.Etale (Node O c) (Node (Localization.Away s) (algebraMap O _ c)) :=
    Algebra.Etale.of_isLocalizationAway (algebraMap O (Node O c) s)
  have : Algebra.Etale (Node (Localization.Away s) (algebraMap O _ c)) (chartAway c s T) :=
    Algebra.Etale.of_restrictScalars (Node O c) _ _
  exact RingHom.etale_algebraMap.mpr this

end ChartLocalization

end DeJongAlterations.StableModification.Omega
