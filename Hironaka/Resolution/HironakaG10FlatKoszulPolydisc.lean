import Hironaka.Resolution.HironakaG10FlatKoszulSplit
import Hironaka.Resolution.HironakaG10FlatPolydiscRemainderMap

/-! # The Koszul step on polydiscs `K' × D̄(0,ρ)`

Douady 1966, §7 Prop. 5 Cor., concrete Banach form for the coordinate `w`: the division by the
Weierstrass polynomial `W = w` (`b = 1`, `weierstrassHyp_coord`) on `B(K' × D̄(0,ρ))`
(`HironakaG10FlatPolydiscRemainderMap`) is a division by `w` with remainders in `B(K')`
(`coordDiv`, a `HironakaG10FlatKoszulSplit.RingDiv`); `pull`-linearity of remainder and quotient for any
Weierstrass polynomial (`remMap_pull_mul`, `quotMap_pull_mul`). Hence, by
`HironakaG10FlatKoszulSplit.splitBy_koszul (coordDiv hK' hρ)`: if a chain `e` over `B(K')` is split in
degrees `1..m` (`r (m+1) = 0`, i.e. `K'` privileged for a finite resolution,
`privilegedOn_iff_exists_splitBy`), the Koszul chain of `w` on its pull-back is split over
`B(K' × D̄(0,ρ))` in degrees `1..m+1`, for EVERY `ρ > 0`. (Restating that conclusion with the concrete
`Fin n → B(K)` families re-synthesizes their normed instances along another path and times out in
`isDefEq`: apply `splitBy_koszul` to `coordDiv` without restating the type.)
BP: hironaka-g10-flat-koszul-polydisc.tex. -/
set_option autoImplicit false
open Set Filter Metric
open scoped Topology
namespace Hironaka.HironakaG10FlatKoszulPolydisc
noncomputable section
open HironakaG10FlatPolydiscAlgebra HironakaG10FlatDiscWeierstrassDivision HironakaG10FlatPolydiscQuotient
  HironakaG10FlatPolydiscRemainderMap HironakaG10FlatKoszulSplit HironakaG10FlatSplitComplex

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]

/-- The coefficients of the Weierstrass polynomial `W = w` (`b = 1`). -/
def coordCoeff : ℕ → P → ℂ := fun i _ => if i = 1 then 1 else 0

omit [NormedAddCommGroup P] [NormedSpace ℂ P] in
theorem polyEval_coordCoeff (z : P) (α : ℂ) : polyEval 1 coordCoeff z α = α := by
  simp [polyEval, coordCoeff]

/-- `W = w` satisfies the Weierstrass hypotheses on `K' × D̄(0,ρ)`. -/
theorem weierstrassHyp_coord {K' : Set P} (hK' : K' ⊆ closure (interior K')) {ρ : ℝ} (hρ : 0 < ρ) :
    WeierstrassHyp K' ρ 1 coordCoeff univ where
  regular := hK'
  pos := hρ
  isOpen := isOpen_univ
  sub := subset_univ _
  holo k := differentiableOn_const _
  monic z _ := if_pos rfl
  roots z _ α hα := by
    rw [polyEval_coordCoeff] at hα
    rw [hα]
    exact mem_ball_self hρ

variable [FiniteDimensional ℂ P] {K' : Set P} {ρ : ℝ} {b : ℕ} {A : ℕ → P → ℂ} {U : Set P}
  [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)] [CompactSpace K']

omit [FiniteDimensional ℂ P] in
/-- Multiplying a division by a pulled-back function. -/
theorem pull_mul_divisionMap (H : WeierstrassHyp K' ρ b A U) (a : holSubalgebra K')
    (q : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) (r : Fin b → holSubalgebra K') :
    pull K' ρ a * divisionMap H (q, r) = divisionMap H (pull K' ρ a * q, fun i => a * r i) := by
  rw [divisionMap_apply, divisionMap_apply, polySum_extFin, polySum_extFin, mul_add,
    Finset.mul_sum]
  dsimp only
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun i _ => by rw [map_mul]; ring

/-- The remainder map is `B(K')`-linear. -/
theorem remMap_pull_mul (H : WeierstrassHyp K' ρ b A U) (a : holSubalgebra K')
    (f : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) :
    remMap H (pull K' ρ a * f) = fun i => a * remMap H f i := by
  conv_lhs => rw [← divisionMap_quot_rem H f, pull_mul_divisionMap, remMap_divisionMap]

/-- The quotient map is `B(K')`-linear. -/
theorem quotMap_pull_mul (H : WeierstrassHyp K' ρ b A U) (a : holSubalgebra K')
    (f : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) :
    quotMap H (pull K' ρ a * f) = pull K' ρ a * quotMap H f := by
  conv_lhs => rw [← divisionMap_quot_rem H f, pull_mul_divisionMap, quotMap_divisionMap]

omit [FiniteDimensional ℂ P] in
/-- For `b = 1` the polynomial part is the pull-back of the constant coefficient. -/
theorem divisionMap_one (H : WeierstrassHyp K' ρ 1 A U)
    (x : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ) × (Fin 1 → holSubalgebra K')) :
    divisionMap H x = Welem H * x.1 + pull K' ρ (x.2 0) := by
  rw [divisionMap_apply, polySum_extFin, Fin.sum_univ_one, Fin.val_zero, wPow_zero, mul_one]

/-- **The division by `w` on `B(K' × D̄(0,ρ))`** with remainders in `B(K')`: its element `w` is
`Welem` of `W = w`, the restriction of `(z, w) ↦ polyEval 1 coordCoeff z w = w`
(`polyEval_coordCoeff`, `evalHom_Welem`). -/
def coordDiv (hK' : K' ⊆ closure (interior K')) (hρ : 0 < ρ) :
    RingDiv (holSubalgebra K') (holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) where
  ι := pullCLM K' ρ
  ι_mul a c := map_mul (pull K' ρ) a c
  w := Welem (weierstrassHyp_coord hK' hρ)
  rem := (ContinuousLinearMap.proj 0).comp (remMap (weierstrassHyp_coord hK' hρ))
  quot := quotMap (weierstrassHyp_coord hK' hρ)
  decomp x := by
    conv_lhs => rw [← divisionMap_quot_rem (weierstrassHyp_coord hK' hρ) x]
    rw [divisionMap_one]
    rfl
  rem_w x := by
    show remMap _ _ 0 = 0
    rw [remMap_Welem_mul]
    rfl
  quot_w x := quotMap_Welem_mul _ x
  rem_ι_mul a x := by
    show remMap _ (pull K' ρ a * x) 0 = a * remMap _ x 0
    rw [remMap_pull_mul]
  quot_ι_mul a x := quotMap_pull_mul _ a x

end
end Hironaka.HironakaG10FlatKoszulPolydisc
