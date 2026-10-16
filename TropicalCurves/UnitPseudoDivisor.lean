import TropicalCurves.Polarization
import Mathlib.Data.Fintype.Sum

/-!
# Quasistable pseudo-divisor types on arbitrary finite graphs

A pseudo-divisor consists of a set of exceptional edges and integral
coefficients at the original vertices. Each selected edge is subdivided by
one new vertex, carrying coefficient `-1`; the polarization is extended by
zero. Quasistability is exactly the finite-graph beta inequality already
formalized in `Polarization`, applied to this explicit subdivision.

These definitions are combinatorial and do not impose edge lengths. They
supply the labels used for the cells of the unit-length Jacobian model.
-/

namespace TropicalCurves
namespace UnitPseudoDivisor

open FiniteStability

variable {V E : Type*}

/-- Original vertices and one new exceptional vertex per selected edge. -/
abbrev SubdividedVertex (V : Type*) (S : Finset E) := V ⊕ {e : E // e ∈ S}

/-- Every original edge remains as its first segment; each selected edge
acquires one additional second segment. -/
abbrev SubdividedEdge (S : Finset E) := E ⊕ {e : E // e ∈ S}

variable [decE : DecidableEq E]

/-- Subdivide exactly the edges selected by `S`, preserving their orientation.
Loops and parallel edges require no special cases. -/
def subdivide (G : EndpointGraph V E) (S : Finset E) :
    EndpointGraph (SubdividedVertex V S) (SubdividedEdge S) where
  source
    | .inl e => .inl (G.source e)
    | .inr e => .inr e
  target
    | .inl e => if h : e ∈ S then .inr ⟨e, h⟩ else .inl (G.target e)
    | .inr e => .inl (G.target e.val)

/-- The polarization has coefficient zero at every exceptional vertex. -/
def extendPolarization (S : Finset E) (μ : V → ℝ) : SubdividedVertex V S → ℝ
  | .inl v => μ v
  | .inr _ => 0

/-- A pseudo-divisor has coefficient `-1` at every exceptional vertex. -/
def extendDivisor (S : Finset E) (F : V → ℤ) : SubdividedVertex V S → ℤ
  | .inl v => F v
  | .inr _ => -1

@[simp] theorem subdivide_source_original (G : EndpointGraph V E) (S : Finset E) (e : E) :
    (subdivide G S).source (.inl e) = .inl (G.source e) := rfl

@[simp] theorem subdivide_target_selected (G : EndpointGraph V E) (S : Finset E)
    (e : E) (he : e ∈ S) :
    (subdivide G S).target (.inl e) = .inr ⟨e, he⟩ := by
  simp [subdivide, he]

@[simp] theorem subdivide_target_unselected (G : EndpointGraph V E) (S : Finset E)
    (e : E) (he : e ∉ S) :
    (subdivide G S).target (.inl e) = .inl (G.target e) := by
  simp [subdivide, he]

@[simp] theorem subdivide_source_extra (G : EndpointGraph V E) (S : Finset E)
    (e : {e : E // e ∈ S}) : (subdivide G S).source (.inr e) = .inr e := rfl

@[simp] theorem subdivide_target_extra (G : EndpointGraph V E) (S : Finset E)
    (e : {e : E // e ∈ S}) : (subdivide G S).target (.inr e) = .inl (G.target e.val) := rfl

omit decE

@[simp] theorem extendPolarization_original (S : Finset E) (μ : V → ℝ) (v : V) :
    extendPolarization S μ (.inl v) = μ v := rfl

@[simp] theorem extendPolarization_exceptional (S : Finset E) (μ : V → ℝ)
    (e : {e : E // e ∈ S}) : extendPolarization S μ (.inr e) = 0 := rfl

@[simp] theorem extendDivisor_original (S : Finset E) (F : V → ℤ) (v : V) :
    extendDivisor S F (.inl v) = F v := rfl

@[simp] theorem extendDivisor_exceptional (S : Finset E) (F : V → ℤ)
    (e : {e : E // e ∈ S}) : extendDivisor S F (.inr e) = -1 := rfl

variable [Fintype V]

/-- Extending by zero preserves the polarization degree. -/
@[simp] theorem extendPolarization_degree (S : Finset E) (μ : V → ℝ) :
    polarizationDegree (extendPolarization S μ) = polarizationDegree μ := by
  simp [polarizationDegree, Fintype.sum_sum_type, extendPolarization]

/-- Each exceptional coefficient subtracts one from the integer degree. -/
theorem extendDivisor_sum (S : Finset E) (F : V → ℤ) :
    (∑ w, extendDivisor S F w) = (∑ v, F v) - (S.card : ℤ) := by
  simp [Fintype.sum_sum_type, extendDivisor, sub_eq_add_neg]

/-- The same degree identity after passage to real coefficients. -/
theorem extendDivisor_sum_real (S : Finset E) (F : V → ℤ) :
    (∑ w, (extendDivisor S F w : ℝ)) =
      (∑ v, (F v : ℝ)) - (S.card : ℝ) := by
  exact_mod_cast extendDivisor_sum S F

/-- Degree compatibility on the subdivision is the usual pseudo-divisor
degree condition `sum F - card S = degree μ`. -/
theorem extend_degreeCompatible_iff (S : Finset E) (μ : V → ℝ) (F : V → ℤ) :
    DegreeCompatible (extendPolarization S μ) (extendDivisor S F) ↔
      (∑ v, (F v : ℝ)) - (S.card : ℝ) = polarizationDegree μ := by
  unfold DegreeCompatible
  rw [extendPolarization_degree, extendDivisor_sum_real]

/-- The combinatorial label of a pseudo-divisor cell. -/
structure PseudoDivisorType (V E : Type*) where
  exceptional : Finset E
  coefficients : V → ℤ

/-- Total degree, including coefficient `-1` at every exceptional vertex. -/
def PseudoDivisorType.degree (T : PseudoDivisorType V E) : ℤ :=
  (∑ v, T.coefficients v) - (T.exceptional.card : ℤ)

include decE

variable [Fintype E] [DecidableEq V]

/-- A valid cell label uses standard rooted quasistability on the explicit
subdivision, with original root `root`. No additional combinatorial
connectivity or integrality assumptions are built into this predicate. -/
def IsQuasistableType (G : EndpointGraph V E) (μ : V → ℝ) (root : V)
    (T : PseudoDivisorType V E) : Prop :=
  IsQuasistable (subdivide G T.exceptional)
    (extendPolarization T.exceptional μ) (.inl root)
    (extendDivisor T.exceptional T.coefficients)

/-- The type of actual quasistable pseudo-divisor labels. -/
abbrev QuasistableType (G : EndpointGraph V E) (μ : V → ℝ) (root : V) :=
  {T : PseudoDivisorType V E // IsQuasistableType G μ root T}

/-- Every quasistable pseudo-divisor type has the degree of its polarization. -/
theorem IsQuasistableType.degree_eq {G : EndpointGraph V E} {μ : V → ℝ} {root : V}
    {T : PseudoDivisorType V E} (hT : IsQuasistableType G μ root T) :
    (T.degree : ℝ) = polarizationDegree μ := by
  have hdegree := (extend_degreeCompatible_iff T.exceptional μ T.coefficients).mp hT.1.1
  simpa [PseudoDivisorType.degree] using hdegree

/-- If the polarization has integer degree `d`, each valid cell label has
that exact integer degree. -/
theorem IsQuasistableType.degree_eq_int {G : EndpointGraph V E} {μ : V → ℝ} {root : V}
    {T : PseudoDivisorType V E} {d : ℤ} (hT : IsQuasistableType G μ root T)
    (hμ : polarizationDegree μ = (d : ℝ)) : T.degree = d := by
  have h := hT.degree_eq.trans hμ
  exact_mod_cast h

/-- The coefficients at original vertices therefore have degree
`d + card exceptional`, as in the usual pseudo-divisor convention. -/
theorem IsQuasistableType.original_degree {G : EndpointGraph V E} {μ : V → ℝ} {root : V}
    {T : PseudoDivisorType V E} {d : ℤ} (hT : IsQuasistableType G μ root T)
    (hμ : polarizationDegree μ = (d : ℝ)) :
    (∑ v, T.coefficients v) = d + (T.exceptional.card : ℤ) := by
  have h := hT.degree_eq_int hμ
  unfold PseudoDivisorType.degree at h
  omega

end UnitPseudoDivisor
end TropicalCurves
