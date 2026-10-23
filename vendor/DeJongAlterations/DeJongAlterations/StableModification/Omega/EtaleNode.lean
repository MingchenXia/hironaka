import DeJongAlterations.StableModification.Omega.InvertibleNode
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Étale charts of the node and `ω_{X/S}`

An *étale node chart* of `f : X ⟶ S` (`EtaleNodeChart`) is an affine open `W ≤ f⁻¹ V`
(`V ⊆ S` affine) with an étale `Γ(S, V)`-algebra `O`, a non-zero-divisor `c ∈ O` and an étale
ring map `O[u,v]/(uv - c) → Γ(X, W)` over `Γ(S, V)`. This is the étale-local form of a node
(Stacks, Tag 0CBY; lane SS3's `Curves.SemistableNormal.exists_away_etale_nodeChart` produces it on
an étale neighbourhood, ERRATA DJA-O9: Zariski node charts need not exist). The node chart
computation of `Omega/InvertibleNode.lean` extends to étale node charts
(`EtaleNodeChart.twoChartAffine`), so `ω_{X/S}` is invertible on every étale node chart
(`EtaleNodeChart.isInvertibleAt_dualizingSheaf`). Blueprint `sm-omega-invertible.tex`,
`lem:sm-omega-etale-node-chart`; M. Temkin, *Stable modification of relative curves*, §1.2,
T:1691–1712.

## Algebra

For `T` formally étale over `N = O[u,v]/(uv - c)` and `O` formally unramified over `R`:

* `NodeEqualizerData.of_flat`: the equalizer conditions on `u, v` ascend along flat maps;
* `extendDerivationEtale`, `span_D_algebraMap_eq_top`: derivations extend along formally étale
  maps, and `Ω_{T/R}` is spanned by the differentials of `N`;
* `etaleNodeKaehler_bijective`: if `xᵢ` is a unit in `T`, `Ω_{T/R}` is free on `dxᵢ`;
* `formallySmooth_of_isUnit_coordinate`: if moreover `O` is formally étale over `R` and `xᵢ` is
  a unit, `T` is formally smooth over `R`;
* `not_mem_smoothLocus_of_etale_node`: primes containing both coordinates are not smooth.
-/

noncomputable section

open TensorProduct

universe u

namespace DeJongAlterations.StableModification.Omega

open DeJongAlterations.Algebra.NodeBlowupChart

section Flat

/-- **The equalizer conditions ascend along flat maps.** -/
theorem NodeEqualizerData.of_flat {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] {u v : A} (H : NodeEqualizerData u v) :
    NodeEqualizerData (algebraMap A B u) (algebraMap A B v) := by
  have hreg : ∀ w ∈ nonZeroDivisors A, algebraMap A B w ∈ nonZeroDivisors B := by
    intro w hw
    have h1 : IsSMulRegular A w := fun x y hxy => by
      dsimp only at hxy
      have : (x - y) * w = 0 := by
        rw [sub_mul]
        rw [smul_eq_mul, smul_eq_mul] at hxy
        rw [mul_comm x, mul_comm y, hxy, sub_self]
      exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff_right.mp hw) _ this)
    have h2 := h1.of_flat (S := B)
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    apply h2
    dsimp only
    rw [smul_eq_mul, smul_eq_mul, mul_zero, mul_comm]
    exact hx
  refine ⟨hreg u H.u_mem, hreg v H.v_mem, fun x hx => ?_⟩
  set I : Ideal A := Ideal.span {u}
  have hI : I.map (algebraMap A B) = Ideal.span {algebraMap A B u} := by
    rw [Ideal.map_span, Set.image_singleton]
  have hregq : IsSMulRegular (A ⧸ I) v := by
    intro a b hab
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    dsimp only at hab
    rw [Ideal.Quotient.eq]
    apply H.sat
    rw [mul_sub]
    rw [Algebra.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul,
      Ideal.Quotient.eq] at hab
    exact hab
  have hregT : IsSMulRegular (B ⊗[A] (A ⧸ I)) v := hregq.lTensor B
  let e := Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I
  have hx' : Ideal.Quotient.mk (I.map (algebraMap A B)) x = 0 := by
    apply e.injective
    rw [map_zero]
    apply hregT
    dsimp only
    rw [smul_zero]
    change v • (x ⊗ₜ[A] (1 : A ⧸ I)) = 0
    rw [TensorProduct.smul_tmul', Algebra.smul_def, mul_comm]
    change e (Ideal.Quotient.mk _ (x * algebraMap A B v)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (by rw [hI, mul_comm]; exact hx), map_zero]
  rw [Ideal.Quotient.eq_zero_iff_mem, hI] at hx'
  exact hx'

end Flat


open DeJongAlterations.Algebra.NodeBlowupChart

section ExtendDerivation

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  [Algebra S T] [IsScalarTower R S T] [Algebra.FormallyEtale S T]
  {M : Type*} [AddCommGroup M] [Module T M] [Module S M] [IsScalarTower S T M] [Module R M]
  [IsScalarTower R T M] [IsScalarTower R S M]

/-- A derivation `S → M` extends along a formally étale `S → T` to a derivation `T → M`. -/
noncomputable def extendDerivationEtale (D : Derivation R S M) : Derivation R T M :=
  ((D.liftKaehlerDifferential.liftBaseChange T).comp
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T).symm.toLinearMap).compDer
      (KaehlerDifferential.D R T)

theorem extendDerivationEtale_algebraMap (D : Derivation R S M) (s : S) :
    extendDerivationEtale D (algebraMap S T s) = D s := by
  change (D.liftKaehlerDifferential.liftBaseChange T)
    ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T).symm
      (KaehlerDifferential.D R T (algebraMap S T s))) = D s
  rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    LinearMap.liftBaseChange_tmul, one_smul, Derivation.liftKaehlerDifferential_comp_D]

omit [Module T M] [Module S M] [IsScalarTower S T M] [Module R M] [IsScalarTower R T M]
  [IsScalarTower R S M] in
/-- Along a formally étale map, `Ω_{T/R}` is spanned by the differentials of elements of `S`. -/
theorem span_D_algebraMap_eq_top :
    Submodule.span T (Set.range fun s : S => KaehlerDifferential.D R T (algebraMap S T s)) = ⊤ := by
  set N := Submodule.span T (Set.range fun s : S => KaehlerDifferential.D R T (algebraMap S T s))
  rw [eq_top_iff]
  rintro z -
  obtain ⟨w, rfl⟩ := (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T).surjective z
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact N.zero_mem
  | add a b ha hb => rw [map_add]; exact N.add_mem ha hb
  | tmul t ω =>
    rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
      KaehlerDifferential.mapBaseChange_tmul]
    refine N.smul_mem t ?_
    have hω : ω ∈ Submodule.span S (Set.range (KaehlerDifferential.D R S)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction hω using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      rw [KaehlerDifferential.map_D]
      exact Submodule.subset_span ⟨s, rfl⟩
    | zero => rw [map_zero]; exact N.zero_mem
    | add a b _ _ ha hb => rw [map_add]; exact N.add_mem ha hb
    | smul s a _ ha =>
      rw [map_smul, ← algebraMap_smul T s]
      exact N.smul_mem _ ha

end ExtendDerivation


open DeJongAlterations.Algebra.NodeBlowupChart

section EtaleNodeKaehler

variable {R O : Type u} [CommRing R] [CommRing O] [Algebra R O] (c : O)
  {T : Type*} [CommRing T] [Algebra (Node O c) T] [Algebra R T] [IsScalarTower R (Node O c) T]

/-- Differentials of functions from an unramified base vanish. -/
theorem D_algebraMap_base_eq_zero [Algebra.FormallyUnramified R O] (o : O) :
    KaehlerDifferential.D R T (algebraMap (Node O c) T (algebraMap O (Node O c) o)) = 0 := by
  rw [← KaehlerDifferential.map_D R R (Node O c) T, ← KaehlerDifferential.map_D R R O (Node O c),
    Subsingleton.elim (KaehlerDifferential.D R O o) 0, map_zero, map_zero]

/-- In `Ω_{T/R}`, `u dv + v du = 0`. -/
theorem etale_coordinate_relation [Algebra.FormallyUnramified R O] :
    algebraMap (Node O c) T (coordinate c 0) •
        KaehlerDifferential.D R T (algebraMap (Node O c) T (coordinate c 1)) +
      algebraMap (Node O c) T (coordinate c 1) •
        KaehlerDifferential.D R T (algebraMap (Node O c) T (coordinate c 0)) = 0 := by
  have hprod : coordinate c 0 * coordinate c 1 = algebraMap O (Node O c) c :=
    DeJongAlterations.Algebra.NodeDomain.nodeCoordinateProduct c
  rw [← Derivation.leibniz, ← map_mul, hprod, D_algebraMap_base_eq_zero]

/-- On an algebra `T` formally étale over the node algebra in which `xᵢ` is a unit, `Ω_{T/R}` is
spanned by `dxᵢ`. -/
theorem etaleNodeKaehler_span [Algebra.FormallyUnramified R O]
    [Algebra.FormallyEtale (Node O c) T] (i : Fin 2)
    (hu : IsUnit (algebraMap (Node O c) T (coordinate c i))) :
    Submodule.span T {KaehlerDifferential.D R T (algebraMap (Node O c) T (coordinate c i))} =
      ⊤ := by
  set N := Submodule.span T
    {KaehlerDifferential.D R T (algebraMap (Node O c) T (coordinate c i))}
  have hj : ∀ j : Fin 2,
      KaehlerDifferential.D R T (algebraMap (Node O c) T (coordinate c j)) ∈ N := by
    have hrel := etale_coordinate_relation (R := R) (T := T) c
    intro j
    by_cases hji : j = i
    · subst hji
      exact Submodule.subset_span rfl
    · have hD : algebraMap (Node O c) T (coordinate c i) •
          KaehlerDifferential.D R T (algebraMap (Node O c) T (coordinate c j)) ∈ N := by
        fin_cases i <;> fin_cases j
        · exact absurd rfl hji
        · simp only [Fin.zero_eta, Fin.mk_one] at hrel ⊢
          rw [eq_neg_of_add_eq_zero_left hrel]
          exact N.neg_mem (N.smul_mem _ (Submodule.subset_span rfl))
        · simp only [Fin.zero_eta, Fin.mk_one] at hrel ⊢
          rw [eq_neg_of_add_eq_zero_right hrel]
          exact N.neg_mem (N.smul_mem _ (Submodule.subset_span rfl))
        · exact absurd rfl hji
      have := N.smul_mem hu.unit⁻¹.val hD
      rwa [smul_smul, IsUnit.val_inv_mul, one_smul] at this
  rw [eq_top_iff, ← span_D_algebraMap_eq_top (R := R) (S := Node O c) (T := T), Submodule.span_le]
  rintro _ ⟨b, rfl⟩
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  dsimp only
  induction p using MvPolynomial.induction_on with
  | C r =>
    change KaehlerDifferential.D R T (algebraMap (Node O c) T (algebraMap O (Node O c) r)) ∈ N
    rw [D_algebraMap_base_eq_zero]
    exact N.zero_mem
  | add p q hp hq =>
    rw [map_add, map_add, map_add]
    exact N.add_mem hp hq
  | mul_X p j hp =>
    rw [map_mul, map_mul, Derivation.leibniz]
    exact N.add_mem (N.smul_mem _ (hj j)) (N.smul_mem _ hp)

/-- The `R`-derivation `∂/∂xᵢ : Node O c → T` (`O`-linear, `∂xᵢ = 1`). -/
noncomputable def etaleNodeDerivation (i : Fin 2)
    (hu : IsUnit (algebraMap (Node O c) T (coordinate c i))) :
    Derivation R (Node O c) T :=
  letI : Algebra O T := ((algebraMap (Node O c) T).comp (algebraMap O (Node O c))).toAlgebra
  haveI : IsScalarTower O (Node O c) T :=
    IsScalarTower.of_algebraMap_eq (R := O) (S := Node O c) (A := T) (fun _ => rfl)
  haveI : IsScalarTower R O T := IsScalarTower.of_algebraMap_eq (fun r => by
    change algebraMap R T r = algebraMap (Node O c) T (algebraMap O (Node O c) (algebraMap R O r))
    rw [← IsScalarTower.algebraMap_apply R O (Node O c),
      ← IsScalarTower.algebraMap_apply R (Node O c) T])
  (nodeDerivation c i hu).restrictScalars R

theorem etaleNodeDerivation_coordinate (i : Fin 2)
    (hu : IsUnit (algebraMap (Node O c) T (coordinate c i))) :
    etaleNodeDerivation (R := R) c i hu (coordinate c i) = 1 := by
  let : Algebra O T := ((algebraMap (Node O c) T).comp (algebraMap O (Node O c))).toAlgebra
  have : IsScalarTower O (Node O c) T :=
    IsScalarTower.of_algebraMap_eq (R := O) (S := Node O c) (A := T) (fun _ => rfl)
  exact nodeDerivation_coordinate c i hu

/-- **Kähler differentials of an étale chart of the node.** If `T` is formally étale over
`O[u,v]/(uv - c)`, `O` is formally unramified over `R` and the coordinate `xᵢ` is a unit in `T`,
then `Ω_{T/R}` is free on `dxᵢ`. -/
theorem etaleNodeKaehler_bijective [Algebra.FormallyUnramified R O]
    [Algebra.FormallyEtale (Node O c) T] (i : Fin 2)
    (hu : IsUnit (algebraMap (Node O c) T (coordinate c i))) :
    Function.Bijective (fun t : T =>
      t • KaehlerDifferential.D R T (algebraMap (Node O c) T (coordinate c i))) :=
  bijective_smul_D_of_span _ (etaleNodeKaehler_span c i hu)
    (extendDerivationEtale (etaleNodeDerivation c i hu))
    (by rw [extendDerivationEtale_algebraMap, etaleNodeDerivation_coordinate])

end EtaleNodeKaehler


open DeJongAlterations.Algebra.NodeBlowupChart

section EtaleNodeSmooth

variable {R O : Type u} [CommRing R] [CommRing O] [Algebra R O] (c : O)
  {T : Type u} [CommRing T] [Algebra (Node O c) T] [Algebra R T] [IsScalarTower R (Node O c) T]

/-- **The coordinate charts of an étale chart of the node are smooth.** If `T` is formally étale
over `O[u,v]/(uv - c)`, `O` is formally étale over `R` and `xᵢ` is a unit in `T`, then `T` is
formally smooth over `R`. -/
theorem formallySmooth_of_isUnit_coordinate [Algebra.FormallyEtale R O]
    [Algebra.FormallyEtale (Node O c) T] (i : Fin 2)
    (hu : IsUnit (algebraMap (Node O c) T (coordinate c i))) :
    Algebra.FormallySmooth R T := by
  let N := Node O c
  let Ni := Localization.Away (coordinate c i)
  have hsm : Algebra.Smooth O Ni :=
    DeJongAlterations.Algebra.NodeFamilyLocalization.coordinateOpen_smooth_of_index c i
  let : Algebra Ni T := (IsLocalization.Away.lift (coordinate c i) hu).toAlgebra
  have : IsScalarTower N Ni T := IsScalarTower.of_algebraMap_eq (fun n => by
    change algebraMap N T n = IsLocalization.Away.lift (coordinate c i) hu (algebraMap N Ni n)
    rw [IsLocalization.Away.lift_eq])
  have : Algebra.FormallyUnramified N Ni := Algebra.FormallyUnramified.of_isLocalization
    (Submonoid.powers (coordinate c i))
  have : Algebra.FormallyEtale Ni T := Algebra.FormallyEtale.of_restrictScalars (R := N)
  let : Algebra O T := ((algebraMap N T).comp (algebraMap O N)).toAlgebra
  have : IsScalarTower O N T :=
    IsScalarTower.of_algebraMap_eq (R := O) (S := N) (A := T) (fun _ => rfl)
  have : IsScalarTower O Ni T := IsScalarTower.of_algebraMap_eq (fun o => by
    change algebraMap N T (algebraMap O N o) = algebraMap Ni T (algebraMap O Ni o)
    rw [IsScalarTower.algebraMap_apply O N Ni, ← IsScalarTower.algebraMap_apply N Ni T])
  have : IsScalarTower R O T := IsScalarTower.of_algebraMap_eq (fun r => by
    change algebraMap R T r = algebraMap N T (algebraMap O N (algebraMap R O r))
    rw [← IsScalarTower.algebraMap_apply R O N, ← IsScalarTower.algebraMap_apply R N T])
  have : Algebra.FormallySmooth O T := Algebra.FormallySmooth.comp O Ni T
  exact Algebra.FormallySmooth.comp R O T

/-- **The node point of an étale chart is not smooth.** Let `A` be finitely presented over `R`
and étale over `O[u,v]/(uv - c)`, `c` a non-zero-divisor, `O` formally unramified over `R`. Then
no prime `q` of `A` containing the coordinates lies in the smooth locus of `A` over `R`. -/
theorem not_mem_smoothLocus_of_etale_node [Algebra.FormallyUnramified R O]
    [Algebra.Etale (Node O c) T] [Algebra.FinitePresentation R T] (hc : c ∈ nonZeroDivisors O)
    (q : PrimeSpectrum T) (h0 : algebraMap (Node O c) T (coordinate c 0) ∈ q.asIdeal)
    (h1 : algebraMap (Node O c) T (coordinate c 1) ∈ q.asIdeal) :
    q ∉ Algebra.smoothLocus R T := by
  let N := Node O c
  have hED := (nodeEqualizerData_node hc).of_flat (B := T)
  let : Algebra O T := ((algebraMap N T).comp (algebraMap O N)).toAlgebra
  have : IsScalarTower O N T :=
    IsScalarTower.of_algebraMap_eq (R := O) (S := N) (A := T) (fun _ => rfl)
  -- generic freeness
  have hgen : ∀ p : PrimeSpectrum T, algebraMap N T (coordinate c 0) ∉ p.asIdeal →
      Function.Bijective (fun t : Localization.AtPrime p.asIdeal =>
        t • KaehlerDifferential.D R (Localization.AtPrime p.asIdeal)
          (algebraMap T (Localization.AtPrime p.asIdeal) (algebraMap N T (coordinate c 0)))) := by
    intro p hp
    let L := Localization.AtPrime p.asIdeal
    have : Algebra.FormallyEtale T L := Algebra.FormallyEtale.of_isLocalization p.asIdeal.primeCompl
    have : Algebra.FormallyEtale N L := Algebra.FormallyEtale.comp N T L
    have hu : IsUnit (algebraMap N L (coordinate c 0)) := by
      rw [IsScalarTower.algebraMap_apply N T L]
      exact IsLocalization.map_units (M := p.asIdeal.primeCompl) L ⟨_, hp⟩
    have := etaleNodeKaehler_bijective (R := R) (T := L) c 0 hu
    simpa only [← IsScalarTower.algebraMap_apply] using this
  -- the two derivations into `κ(q)`
  let κ := q.asIdeal.ResidueField
  have : IsScalarTower O N κ := IsScalarTower.of_algebraMap_eq (R := O) (S := N) (A := κ)
    (fun o => by
      rw [IsScalarTower.algebraMap_apply O T κ, IsScalarTower.algebraMap_apply N T κ,
        ← IsScalarTower.algebraMap_apply O N T])
  have : IsScalarTower R O T := IsScalarTower.of_algebraMap_eq (fun r => by
    change algebraMap R T r = algebraMap N T (algebraMap O N (algebraMap R O r))
    rw [← IsScalarTower.algebraMap_apply R O N, ← IsScalarTower.algebraMap_apply R N T])
  have : IsScalarTower R O κ := IsScalarTower.of_algebraMap_eq (R := R) (S := O) (A := κ)
    (fun r => by
      rw [IsScalarTower.algebraMap_apply R T κ, IsScalarTower.algebraMap_apply O T κ,
        ← IsScalarTower.algebraMap_apply R O T])
  have hc0 : ∀ i, algebraMap N κ (coordinate c i) = 0 := by
    intro i
    rw [IsScalarTower.algebraMap_apply N T κ, Ideal.algebraMap_residueField_eq_zero]
    fin_cases i
    · exact h0
    · exact h1
  have hval : ∀ j : Fin 2, algebraMap N κ (coordinate c 0) * (Pi.single j 1 : Fin 2 → κ) 1 +
      algebraMap N κ (coordinate c 1) * (Pi.single j 1 : Fin 2 → κ) 0 = 0 := by
    intro j
    rw [hc0, hc0, zero_mul, zero_mul, add_zero]
  let D : Fin 2 → Derivation R T κ := fun j =>
    extendDerivationEtale ((nodeDerivationOfValues c (Pi.single j 1) (hval j)).1.restrictScalars R)
  have hD : ∀ j i, D j (algebraMap N T (coordinate c i)) = (Pi.single j 1 : Fin 2 → κ) i := by
    intro j i
    exact (extendDerivationEtale_algebraMap _ _).trans
      ((nodeDerivationOfValues c (Pi.single j 1) (hval j)).2 i)
  exact not_mem_smoothLocus_of_derivations q (algebraMap N T (coordinate c 0))
    (algebraMap N T (coordinate c 1)) hED.u_mem hgen (D 0) (D 1)
    (by rw [hD]; exact Pi.single_eq_same _ _)
    (by rw [hD]; exact Pi.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide) _)
    (by rw [hD]; exact Pi.single_eq_same _ _)

end EtaleNodeSmooth


open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open DeJongAlterations.Algebra.NodeBlowupChart

variable {X S : Scheme.{u}}

variable (f : X ⟶ S) in
/-- An *étale node chart* of `f`: affine opens `W ≤ f⁻¹ V`, an étale `Γ(S, V)`-algebra `O`, a
non-zero-divisor `c ∈ O`, and an étale ring map `O[u,v]/(uv - c) → Γ(X, W)` over `Γ(S, V)`. -/
structure EtaleNodeChart (V : S.Opens) (W : X.Opens) where
  isAffineOpen_W : IsAffineOpen W
  isAffineOpen_V : IsAffineOpen V
  le : W ≤ f ⁻¹ᵁ V
  /-- The étale base of the node. -/
  O : Type u
  [commRing : CommRing O]
  [algebra : Algebra Γ(S, V) O]
  [etale : Algebra.Etale Γ(S, V) O]
  /-- The equation of the node. -/
  c : O
  c_mem : c ∈ nonZeroDivisors O
  /-- The étale map from the node model. -/
  toNode : Node O c →+* Γ(X, W)
  etale_toNode : toNode.Etale
  compat : ∀ r : Γ(S, V),
    toNode (algebraMap O (Node O c) (algebraMap Γ(S, V) O r)) = f.appLE V W le r

namespace EtaleNodeChart

attribute [instance] commRing algebra etale

variable {f : X ⟶ S} {V : S.Opens} {W : X.Opens} (C : EtaleNodeChart f V W)

/-- The coordinates `u = x₀`, `v = x₁` of the chart. -/
def coord (i : Fin 2) : Γ(X, W) := C.toNode (coordinate C.c i)

/-- The algebra structures of an étale node chart on the sections over an open `W' ≤ W`. -/
abbrev nodeAlgebra {W' : X.Opens} (hle : W' ≤ W) : Algebra (Node C.O C.c) Γ(X, W') :=
  ((res hle).comp C.toNode).toAlgebra

theorem isScalarTower {W' : X.Opens} (hle : W' ≤ W) :
    letI := C.nodeAlgebra hle
    letI := (f.appLE V W' (hle.trans C.le)).hom.toAlgebra
    IsScalarTower Γ(S, V) (Node C.O C.c) Γ(X, W') := by
  let := C.nodeAlgebra hle
  let := (f.appLE V W' (hle.trans C.le)).hom.toAlgebra
  exact IsScalarTower.of_algebraMap_eq (R := Γ(S, V)) (S := Node C.O C.c) (A := Γ(X, W'))
    (fun r => by
    change f.appLE V W' (hle.trans C.le) r = res hle (C.toNode (algebraMap _ _ r))
    rw [IsScalarTower.algebraMap_apply Γ(S, V) C.O (Node C.O C.c), C.compat,
      ← CommRingCat.comp_apply, Scheme.Hom.appLE_map])

theorem formallyEtale_of_isLocalization {W' : X.Opens} (hle : W' ≤ W) (M : Submonoid Γ(X, W))
    (hM : letI := (res hle).toAlgebra; IsLocalization M Γ(X, W')) :
    letI := C.nodeAlgebra hle
    Algebra.FormallyEtale (Node C.O C.c) Γ(X, W') := by
  let := C.toNode.toAlgebra
  have : Algebra.Etale (Node C.O C.c) Γ(X, W) := C.etale_toNode
  let := (res hle).toAlgebra
  let := C.nodeAlgebra hle
  have : IsScalarTower (Node C.O C.c) Γ(X, W) Γ(X, W') :=
    IsScalarTower.of_algebraMap_eq (R := Node C.O C.c) (S := Γ(X, W)) (A := Γ(X, W'))
      (fun _ => rfl)
  have : Algebra.FormallyEtale Γ(X, W) Γ(X, W') := Algebra.FormallyEtale.of_isLocalization M
  exact Algebra.FormallyEtale.comp (Node C.O C.c) Γ(X, W) Γ(X, W')


theorem isScalarTower_self :
    letI := C.toNode.toAlgebra
    letI := (f.appLE V W C.le).hom.toAlgebra
    IsScalarTower Γ(S, V) (Node C.O C.c) Γ(X, W) := by
  let := C.toNode.toAlgebra
  let := (f.appLE V W C.le).hom.toAlgebra
  exact IsScalarTower.of_algebraMap_eq (R := Γ(S, V)) (S := Node C.O C.c) (A := Γ(X, W))
    (fun r => by
      change f.appLE V W C.le r = C.toNode (algebraMap _ _ r)
      rw [IsScalarTower.algebraMap_apply Γ(S, V) C.O (Node C.O C.c), C.compat])

theorem coord_mul : C.coord 0 * C.coord 1 = C.toNode (algebraMap C.O (Node C.O C.c) C.c) := by
  rw [coord, coord, ← map_mul]
  congr 1
  exact DeJongAlterations.Algebra.NodeDomain.nodeCoordinateProduct C.c

theorem nodeEqualizerData : NodeEqualizerData (C.coord 0) (C.coord 1) := by
  let := C.toNode.toAlgebra
  have : Algebra.Etale (Node C.O C.c) Γ(X, W) := C.etale_toNode
  exact (nodeEqualizerData_node C.c_mem).of_flat (B := Γ(X, W))

/-- `d(uv) = 0`: `uv = c` comes from the étale `Γ(S, V)`-algebra `O`. -/
theorem rel (U : X.Opens) (hU : U ≤ W) :
    (universalDerivation f).sec U (res hU (C.coord 0 * C.coord 1)) = 0 := by
  rw [sec_res]
  have h0 : (universalDerivation f).sec W (C.coord 0 * C.coord 1) = 0 := by
    let := C.toNode.toAlgebra
    let := (f.appLE V W C.le).hom.toAlgebra
    have := C.isScalarTower_self
    rw [RelDerivation.sec_apply, ← sectionsLinearMap_d f C.le, C.coord_mul]
    change sectionsLinearMap f C.le (KaehlerDifferential.D Γ(S, V) Γ(X, W)
      (algebraMap (Node C.O C.c) Γ(X, W) (algebraMap C.O (Node C.O C.c) C.c))) = 0
    rw [D_algebraMap_base_eq_zero]
    exact map_zero (sectionsLinearMap f C.le).hom
  rw [h0, map_zero]

/-- **Kähler differentials on an étale node chart.** On an affine open `W' ≤ W` whose ring of
sections is a localization of `Γ(X, W)` in which the coordinate `xᵢ` is a unit, `Ω¹_{X/S}` is
free on `dxᵢ`. -/
theorem kaehler_bijective {W' : X.Opens} (hW' : IsAffineOpen W') (hle : W' ≤ W)
    (M : Submonoid Γ(X, W))
    (hM : letI := (res hle).toAlgebra; IsLocalization M Γ(X, W')) (i : Fin 2)
    (hi : IsUnit (res hle (C.coord i))) :
    Function.Bijective (fun c : Γ(X, W') =>
      c • (universalDerivation f).sec W' (res hle (C.coord i))) := by
  let := C.nodeAlgebra hle
  let := (f.appLE V W' (hle.trans C.le)).hom.toAlgebra
  have := C.isScalarTower hle
  have := C.formallyEtale_of_isLocalization hle M hM
  have hbij := etaleNodeKaehler_bijective (R := Γ(S, V)) (T := Γ(X, W')) C.c i hi
  have heq := sectionsLinearMap_bijective f hW' C.isAffineOpen_V (hle.trans C.le)
  have hpt : ∀ c : Γ(X, W'), c • (universalDerivation f).sec W' (res hle (C.coord i)) =
      sectionsLinearMap f (hle.trans C.le) (c • KaehlerDifferential.D Γ(S, V) Γ(X, W')
        (algebraMap (Node C.O C.c) Γ(X, W') (coordinate C.c i))) := by
    intro c
    refine Eq.trans ?_ ((sectionsLinearMap f (hle.trans C.le)).hom.map_smul c _).symm
    congr 1
    exact (sectionsLinearMap_d f (hle.trans C.le) (res hle (C.coord i))).symm
  have hcomp : (fun c : Γ(X, W') => c • (universalDerivation f).sec W' (res hle (C.coord i))) =
      (sectionsLinearMap f (hle.trans C.le)) ∘ (fun c : Γ(X, W') =>
        c • KaehlerDifferential.D Γ(S, V) Γ(X, W')
          (algebraMap (Node C.O C.c) Γ(X, W') (coordinate C.c i))) :=
    funext hpt
  rw [hcomp]
  exact heq.comp hbij

variable [LocallyOfFinitePresentation f]

/-- **The coordinate charts of an étale node chart are smooth.** -/
theorem basicOpen_coord_le_smoothLocus (i : Fin 2) :
    X.basicOpen (C.coord i) ≤ f.smoothLocus := by
  intro y hy
  have hW := C.isAffineOpen_W
  set W' := X.basicOpen (C.coord i)
  have hW' : IsAffineOpen W' := hW.basicOpen _
  have hle : W' ≤ W := X.basicOpen_le _
  let := C.nodeAlgebra hle
  let := (f.appLE V W' (hle.trans C.le)).hom.toAlgebra
  have := C.isScalarTower hle
  let := (res hle).toAlgebra
  have hloc := hW.isLocalization_basicOpen (C.coord i)
  have := C.formallyEtale_of_isLocalization hle (Submonoid.powers (C.coord i)) hloc
  have hu : IsUnit (algebraMap (Node C.O C.c) Γ(X, W') (coordinate C.c i)) :=
    X.toRingedSpace.isUnit_res_basicOpen (C.coord i)
  have hsm := formallySmooth_of_isUnit_coordinate (R := Γ(S, V)) (T := Γ(X, W')) C.c i hu
  rw [Scheme.Hom.mem_smoothLocus,
    formallySmooth_stalkMap_iff V C.isAffineOpen_V W' hW' (hle.trans C.le) hy]
  change Algebra.FormallySmooth Γ(S, V) (Localization.AtPrime _)
  exact Algebra.FormallySmooth.comp Γ(S, V) Γ(X, W') _

/-- **The points of `V(x₀, x₁)` are not smooth.** -/
theorem not_mem_smoothLocus {x : X} (hx : x ∈ W)
    (h0 : x ∉ X.basicOpen (C.coord 0)) (h1 : x ∉ X.basicOpen (C.coord 1)) :
    x ∉ f.smoothLocus := by
  have hW := C.isAffineOpen_W
  let := C.toNode.toAlgebra
  have : Algebra.Etale (Node C.O C.c) Γ(X, W) := C.etale_toNode
  let := (f.appLE V W C.le).hom.toAlgebra
  have := C.isScalarTower_self
  have : Algebra.FinitePresentation Γ(S, V) Γ(X, W) :=
    f.finitePresentation_appLE C.isAffineOpen_V hW C.le
  have h0' : C.coord 0 ∈ (hW.primeIdealOf ⟨x, hx⟩).asIdeal := by
    by_contra h
    exact h0 ((mem_basicOpen_iff_notMem hW hx _).mpr h)
  have h1' : C.coord 1 ∈ (hW.primeIdealOf ⟨x, hx⟩).asIdeal := by
    by_contra h
    exact h1 ((mem_basicOpen_iff_notMem hW hx _).mpr h)
  rw [Scheme.Hom.mem_smoothLocus, formallySmooth_stalkMap_iff V C.isAffineOpen_V W hW C.le hx]
  exact not_mem_smoothLocus_of_etale_node (R := Γ(S, V)) (T := Γ(X, W)) C.c C.c_mem _ h0' h1'

/-- **The smooth locus of an étale node chart.** `W ∩ smoothLocus(f) = D(x₀) ∪ D(x₁)`. -/
theorem inf_smoothLocus :
    W ⊓ f.smoothLocus = X.basicOpen (C.coord 0) ⊔ X.basicOpen (C.coord 1) := by
  apply le_antisymm
  · rintro x ⟨hxW, hxU⟩
    by_contra hx
    simp only [TopologicalSpace.Opens.mem_sup, not_or] at hx
    exact C.not_mem_smoothLocus hxW hx.1 hx.2 hxU
  · exact sup_le (le_inf (X.basicOpen_le _) (C.basicOpen_coord_le_smoothLocus 0))
      (le_inf (X.basicOpen_le _) (C.basicOpen_coord_le_smoothLocus 1))

/-- An étale node chart is a two-chart affine with the coordinates `u = x₀`, `v = x₁`. -/
theorem twoChartAffine : TwoChartAffine f W (C.coord 0) (C.coord 1) where
  isAffineOpen := C.isAffineOpen_W
  rel := C.rel
  equalizer := C.nodeEqualizerData
  kaehler := by
    rintro W' hW' hle M hM t (rfl | rfl) ht
    · exact C.kaehler_bijective hW' hle M hM 0 ht
    · exact C.kaehler_bijective hW' hle M hM 1 ht
  smoothLocus := C.inf_smoothLocus

include C in
/-- **`ω_{X/S}` is invertible on an étale node chart.** -/
theorem isInvertibleAt_dualizingSheaf {x : X} (hx : x ∈ W) :
    IsInvertibleAt (dualizingSheaf f) x :=
  C.twoChartAffine.isInvertibleAt_dualizingSheaf hx

end EtaleNodeChart

end DeJongAlterations.StableModification.Omega
