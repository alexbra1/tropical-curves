import TropicalCurves.Polarization
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Pi
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Tactic.Ring

/-!
# The unit-length graph Jacobian in chain coordinates

Let every edge of a finite oriented graph have length one. Real edge chains
then have the usual Euclidean length pairing. The chain-coordinate model of
its Jacobian is

`ℝ^E / (im(δ : ℝ^V → ℝ^E) + H₁(G,ℤ))`.

Here `δφ(e) = φ(target e) - φ(source e)`, and integral cycles are the kernel
of the signed incoming boundary. The subgroup in this quotient is constructed
explicitly; equality in the quotient is proved equivalent to an actual real
gradient plus an actual integral cycle. No tropical cell decomposition or
vertex-integrality assertion is included in its definition.

Loops and parallel edges are permitted, and connectivity is not required for
these algebraic constructions. This module is specifically for unit lengths:
general positive lengths require the corresponding weighted gradient space.
-/

noncomputable section

namespace TropicalCurves
namespace UnitJacobian

open FiniteStability

variable {V E : Type*} [Fintype E] [DecidableEq V]

/-- The signed incidence coefficient: incoming edges count positively and
outgoing edges negatively. A loop contributes zero. -/
def incidence (G : EndpointGraph V E) (v : V) (e : E) : ℤ :=
  (if G.target e = v then 1 else 0) - (if G.source e = v then 1 else 0)

/-- The real gradient for the unit-edge-length inner product. -/
def gradient (G : EndpointGraph V E) : (V → ℝ) →ₗ[ℝ] (E → ℝ) where
  toFun φ e := φ (G.target e) - φ (G.source e)
  map_add' φ ψ := by ext e; simp only [Pi.add_apply]; ring
  map_smul' r φ := by ext e; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

omit [Fintype E] [DecidableEq V] in
@[simp] theorem gradient_apply (G : EndpointGraph V E) (φ : V → ℝ) (e : E) :
    gradient G φ e = φ (G.target e) - φ (G.source e) := rfl

/-- The integral boundary operator, with the same incoming-slope convention. -/
def integerBoundary (G : EndpointGraph V E) : (E → ℤ) →+ (V → ℤ) where
  toFun c v := ∑ e, incidence G v e * c e
  map_zero' := by ext v; simp
  map_add' c d := by ext v; simp [mul_add, Finset.sum_add_distrib]

@[simp] theorem integerBoundary_apply (G : EndpointGraph V E) (c : E → ℤ) (v : V) :
    integerBoundary G c v = ∑ e, incidence G v e * c e := rfl

/-- The real boundary operator. -/
def realBoundary (G : EndpointGraph V E) : (E → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun c v := ∑ e, (incidence G v e : ℝ) * c e
  map_add' c d := by ext v; simp [mul_add, Finset.sum_add_distrib]
  map_smul' r c := by
    ext v
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro e he
    ring

@[simp] theorem realBoundary_apply (G : EndpointGraph V E) (c : E → ℝ) (v : V) :
    realBoundary G c v = ∑ e, (incidence G v e : ℝ) * c e := rfl

/-- Include integral edge chains into real edge chains coefficient by coefficient. -/
def castChain : (E → ℤ) →+ (E → ℝ) where
  toFun c e := (c e : ℝ)
  map_zero' := by ext e; simp
  map_add' c d := by ext e; simp

omit [Fintype E] in
@[simp] theorem castChain_apply (c : E → ℤ) (e : E) :
    castChain c e = (c e : ℝ) := rfl

/-- Integral cycles are exactly integral chains with zero boundary. -/
def integerCycles (G : EndpointGraph V E) : AddSubgroup (E → ℤ) :=
  (integerBoundary G).ker

@[simp] theorem mem_integerCycles (G : EndpointGraph V E) (c : E → ℤ) :
    c ∈ integerCycles G ↔ integerBoundary G c = 0 := Iff.rfl

/-- Real gradients, viewed as an additive subgroup of the real chain space. -/
def gradientSubgroup (G : EndpointGraph V E) : AddSubgroup (E → ℝ) :=
  (gradient G).toAddMonoidHom.range

/-- The integral cycle lattice in real chain coordinates. -/
def integralCycleSubgroup (G : EndpointGraph V E) : AddSubgroup (E → ℝ) :=
  (integerCycles G).map castChain

/-- The sum of the gradient space and the integral cycle lattice. -/
def periodSubgroup (G : EndpointGraph V E) : AddSubgroup (E → ℝ) :=
  gradientSubgroup G ⊔ integralCycleSubgroup G

/-- Membership in the denominator subgroup is precisely the explicit
gradient-plus-integral-cycle relation. -/
theorem mem_periodSubgroup_iff (G : EndpointGraph V E) (x : E → ℝ) :
    x ∈ periodSubgroup G ↔
      ∃ (φ : V → ℝ) (c : E → ℤ), integerBoundary G c = 0 ∧
        x = gradient G φ + castChain c := by
  rw [periodSubgroup, AddSubgroup.mem_sup]
  constructor
  · rintro ⟨g, ⟨φ, rfl⟩, z, ⟨c, hc, rfl⟩, hx⟩
    exact ⟨φ, c, hc, hx.symm⟩
  · rintro ⟨φ, c, hc, hx⟩
    exact ⟨gradient G φ, ⟨φ, rfl⟩, castChain c, ⟨c, hc, rfl⟩, hx.symm⟩

/-- The real covering space in chain coordinates, before dividing by the
integral cycle lattice. This definition supplies its additive quotient structure. -/
abbrev Cover (G : EndpointGraph V E) := (E → ℝ) ⧸ gradientSubgroup G

/-- The additive quotient map to the covering space. -/
def coverClass (G : EndpointGraph V E) : (E → ℝ) →+ Cover G :=
  QuotientAddGroup.mk' (gradientSubgroup G)

omit [Fintype E] [DecidableEq V] in
/-- Two real chains represent the same covering point exactly when their
difference is a real gradient. -/
theorem cover_eq_iff (G : EndpointGraph V E) (x y : E → ℝ) :
    coverClass G x = coverClass G y ↔
      ∃ φ : V → ℝ, x - y = gradient G φ := by
  change (QuotientAddGroup.mk x : Cover G) = QuotientAddGroup.mk y ↔ _
  rw [QuotientAddGroup.eq_iff_sub_mem]
  constructor
  · rintro ⟨φ, hφ⟩
    exact ⟨φ, hφ.symm⟩
  · rintro ⟨φ, hφ⟩
    exact ⟨φ, hφ.symm⟩

omit [Fintype E] [DecidableEq V] in
@[simp] theorem coverClass_gradient (G : EndpointGraph V E) (φ : V → ℝ) :
    coverClass G (gradient G φ) = 0 := by
  have h := (cover_eq_iff G (gradient G φ) 0).mpr ⟨φ, by simp⟩
  simpa using h

/-- The unit-length Jacobian in real-chain coordinates. -/
abbrev Jacobian (G : EndpointGraph V E) := (E → ℝ) ⧸ periodSubgroup G

/-- The additive quotient map from real edge chains to their Jacobian class. -/
def classMap (G : EndpointGraph V E) : (E → ℝ) →+ Jacobian G :=
  QuotientAddGroup.mk' (periodSubgroup G)

/-- The natural projection from the real covering space to the Jacobian. -/
def coverProjection (G : EndpointGraph V E) : Cover G →+ Jacobian G :=
  QuotientAddGroup.map (gradientSubgroup G) (periodSubgroup G)
    (AddMonoidHom.id (E → ℝ)) (by
      intro x hx
      exact AddSubgroup.mem_sup_left hx)

@[simp] theorem coverProjection_coverClass (G : EndpointGraph V E) (x : E → ℝ) :
    coverProjection G (coverClass G x) = classMap G x := rfl

/-- Equality of Jacobian classes has exactly the expected concrete witnesses. -/
theorem class_eq_iff (G : EndpointGraph V E) (x y : E → ℝ) :
    classMap G x = classMap G y ↔
      ∃ (φ : V → ℝ) (c : E → ℤ), integerBoundary G c = 0 ∧
        x - y = gradient G φ + castChain c := by
  change (QuotientAddGroup.mk x : Jacobian G) = QuotientAddGroup.mk y ↔ _
  rw [QuotientAddGroup.eq_iff_sub_mem, mem_periodSubgroup_iff]

/-- Equality downstairs is equivalent to equality of covering points after
translation by a genuine integral cycle. -/
theorem class_eq_iff_cover_shift (G : EndpointGraph V E) (x y : E → ℝ) :
    classMap G x = classMap G y ↔
      ∃ c : E → ℤ, integerBoundary G c = 0 ∧
        coverClass G x = coverClass G (y + castChain c) := by
  rw [class_eq_iff]
  constructor
  · rintro ⟨φ, c, hc, hxy⟩
    refine ⟨c, hc, (cover_eq_iff G _ _).mpr ⟨φ, ?_⟩⟩
    rw [sub_add_eq_sub_sub, hxy]
    simp
  · rintro ⟨c, hc, hcover⟩
    obtain ⟨φ, hφ⟩ := (cover_eq_iff G _ _).mp hcover
    rw [sub_add_eq_sub_sub] at hφ
    exact ⟨φ, c, hc, sub_eq_iff_eq_add.mp hφ⟩

/-- The zero-class criterion is the same explicit relation without a second chain. -/
theorem class_eq_zero_iff (G : EndpointGraph V E) (x : E → ℝ) :
    classMap G x = 0 ↔
      ∃ (φ : V → ℝ) (c : E → ℤ), integerBoundary G c = 0 ∧
        x = gradient G φ + castChain c := by
  simpa using class_eq_iff G x 0

@[simp] theorem classMap_gradient (G : EndpointGraph V E) (φ : V → ℝ) :
    classMap G (gradient G φ) = 0 := by
  apply (class_eq_zero_iff G _).mpr
  exact ⟨φ, 0, by simp, by simp⟩

theorem classMap_integerCycle (G : EndpointGraph V E) (c : E → ℤ)
    (hc : integerBoundary G c = 0) : classMap G (castChain c) = 0 := by
  apply (class_eq_zero_iff G _).mpr
  exact ⟨0, c, hc, by simp⟩

theorem classMap_add_gradient (G : EndpointGraph V E) (x : E → ℝ) (φ : V → ℝ) :
    classMap G (x + gradient G φ) = classMap G x := by simp

theorem classMap_add_integerCycle (G : EndpointGraph V E) (x : E → ℝ)
    (c : E → ℤ) (hc : integerBoundary G c = 0) :
    classMap G (x + castChain c) = classMap G x := by
  simp [classMap_integerCycle G c hc]

/-- Casting integral coefficients commutes with the signed boundary operator. -/
theorem realBoundary_castChain (G : EndpointGraph V E) (c : E → ℤ) :
    realBoundary G (castChain c) = fun v => (integerBoundary G c v : ℝ) := by
  ext v
  simp [realBoundary_apply, integerBoundary_apply]

section SingleEdges

variable [DecidableEq E]

/-- A unit chain on one edge has its signed endpoints as its boundary. -/
theorem integerBoundary_single (G : EndpointGraph V E) (e : E) (n : ℤ) :
    integerBoundary G (Pi.single e n) =
      Pi.single (G.target e) n - Pi.single (G.source e) n := by
  ext v
  simp [integerBoundary_apply, Pi.single_apply, incidence, sub_mul, mul_ite, eq_comm]

omit [Fintype E] in
/-- Casting a single-edge integral chain gives the corresponding real chain. -/
@[simp] theorem castChain_single (e : E) (n : ℤ) :
    castChain (Pi.single e n) = Pi.single e (n : ℝ) := by
  ext f
  simp [Pi.single_apply]

end SingleEdges

section FiniteVertices

variable [Fintype V]

omit [Fintype E] in
/-- Every oriented edge has one incoming and one outgoing incidence. -/
theorem sum_incidence (G : EndpointGraph V E) (e : E) :
    ∑ v, incidence G v e = 0 := by
  simp [incidence, Finset.sum_sub_distrib]

/-- Boundaries have total degree zero, without any connectivity hypothesis. -/
theorem integerBoundary_sum (G : EndpointGraph V E) (c : E → ℤ) :
    ∑ v, integerBoundary G c v = 0 := by
  simp only [integerBoundary_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e he
  rw [← Finset.sum_mul, sum_incidence, zero_mul]

omit [Fintype E] in
/-- The incidence matrix pairs a potential with its endpoint difference. -/
theorem incidence_pairing (G : EndpointGraph V E) (φ : V → ℝ) (e : E) :
    (∑ v, (incidence G v e : ℝ) * φ v) = gradient G φ e := by
  simp [incidence, sub_mul, Finset.sum_sub_distrib]

/-- Real boundary and unit-length gradient are adjoint for the ordinary
finite-coordinate pairings. -/
theorem boundary_gradient_pairing (G : EndpointGraph V E) (x : E → ℝ) (φ : V → ℝ) :
    (∑ v, realBoundary G x v * φ v) = ∑ e, x e * gradient G φ e := by
  simp only [realBoundary_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [← incidence_pairing G φ e, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  ring

/-- Gradients annihilate every harmonic one-form under edge integration. -/
theorem gradient_pairing_cycle_zero (G : EndpointGraph V E) (φ : V → ℝ)
    (h : E → ℝ) (hh : realBoundary G h = 0) :
    (∑ e, gradient G φ e * h e) = 0 := by
  have hz : (∑ e, h e * gradient G φ e) = 0 := by
    rw [← boundary_gradient_pairing, hh]
    simp
  simpa only [mul_comm] using hz

end FiniteVertices

end UnitJacobian
end TropicalCurves
