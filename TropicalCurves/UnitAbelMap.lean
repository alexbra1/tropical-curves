import TropicalCurves.UnitRoutes
import TropicalCurves.UnitPseudoDivisor
import TropicalCurves.MetricGraph
import Mathlib.Tactic.Abel

/-!
# Divisor integration and Abel maps on unit-length graph models

This module connects the canonical graph point set, its finitely supported
integral divisors, and the chain-coordinate Jacobian. Integral routes from a
fixed root supply point integrals. The endpoint relation is proved by an
integral cycle, so integration is compatible with the closed edge maps.

For every vertex-supported divisor and every finite list of moving edges
(including repeated edges and loops), the resulting divisor Abel map has the
explicit affine chain representative `castChain cornerChain - edgeChain`.
The same construction applies to the exceptional-edge parameters of a
pseudo-divisor type.
-/

noncomputable section

namespace TropicalCurves
namespace UnitAbelMap

open FiniteStability UnitJacobian UnitRoutes

variable {V E : Type*}

/-- Give every edge of an endpoint graph length one. -/
def unitGraph (G : EndpointGraph V E) : RealLengthGraph V E where
  source := G.source
  target := G.target
  length _ := 1
  length_pos _ := by norm_num

@[simp] theorem unitGraph_source (G : EndpointGraph V E) (e : E) :
    (unitGraph G).source e = G.source e := rfl

@[simp] theorem unitGraph_target (G : EndpointGraph V E) (e : E) :
    (unitGraph G).target e = G.target e := rfl

@[simp] theorem unitGraph_length (G : EndpointGraph V E) (e : E) :
    (unitGraph G).length e = 1 := rfl

variable [Fintype E] [DecidableEq V] [DecidableEq E]
variable (G : EndpointGraph V E) {q : V} (R : VertexRoutes G q)

/-- Integrate from the chosen root to a canonical graph point, modulo real
gradients and integral cycles. -/
def pointIntegral : (unitGraph G).Point → Jacobian G
  | Sum.inl v => classMap G (castChain (R.chain v))
  | Sum.inr ⟨e, t⟩ =>
      classMap G (castChain (R.chain (G.source e)) + (t : ℝ) • (Pi.single e (1 : ℝ) : E → ℝ))

@[simp] theorem pointIntegral_vertex (v : V) :
    pointIntegral G R ((unitGraph G).vertex v) =
      classMap G (castChain (R.chain v)) := rfl

@[simp] theorem pointIntegral_interior (e : E) (t : Set.Ioo (0 : ℝ) 1) :
    pointIntegral G R ((unitGraph G).interior e t) =
      classMap G (castChain (R.chain (G.source e)) + (t : ℝ) • (Pi.single e (1 : ℝ) : E → ℝ)) := rfl

/-- Point integration is independent of the routes chosen from the same root.
Only an integral cycle changes when a route is replaced. -/
theorem pointIntegral_route_independent (S : VertexRoutes G q)
    (p : (unitGraph G).Point) : pointIntegral G R p = pointIntegral G S p := by
  rcases p with v | ⟨e, t⟩
  · exact R.route_class_independent S v
  · change classMap G (castChain (R.chain (G.source e)) +
        (t : ℝ) • (Pi.single e (1 : ℝ) : E → ℝ)) =
      classMap G (castChain (S.chain (G.source e)) +
        (t : ℝ) • (Pi.single e (1 : ℝ) : E → ℝ))
    rw [map_add, map_add, R.route_class_independent S (G.source e)]

/-- Point integration on a closed edge includes both endpoint vertices.
The terminal endpoint uses the integral-cycle identity for the chosen routes. -/
@[simp] theorem pointIntegral_closedEdgeMap (e : E) (t : Set.Icc (0 : ℝ) 1) :
    pointIntegral G R ((unitGraph G).closedEdgeMap e t) =
      classMap G (castChain (R.chain (G.source e)) + (t : ℝ) • (Pi.single e (1 : ℝ) : E → ℝ)) := by
  unfold RealLengthGraph.closedEdgeMap
  split_ifs with hzero hone
  · change classMap G (castChain (R.chain (G.source e))) = _
    simp [hzero]
  · have ht : (t : ℝ) = 1 := hone
    change classMap G (castChain (R.chain (G.target e))) = _
    rw [ht, one_smul]
    exact (R.endpoint_class e).symm
  · rfl

/-- Additive integration of finitely supported integral divisors. -/
def divisorClass : (unitGraph G).Divisor →+ Jacobian G :=
  Finsupp.liftAddHom fun p =>
    { toFun := fun n : ℤ => n • pointIntegral G R p
      map_zero' := zero_zsmul _
      map_add' := fun m n => add_zsmul _ m n }

@[simp] theorem divisorClass_single (p : (unitGraph G).Point) (n : ℤ) :
    divisorClass G R (Finsupp.single p n) = n • pointIntegral G R p := by
  simp [divisorClass]

/-- The entire divisor-class homomorphism is independent of route choices. -/
theorem divisorClass_eq_of_routes (S : VertexRoutes G q) :
    divisorClass G R = divisorClass G S := by
  apply Finsupp.addHom_ext
  intro p n
  simp only [divisorClass_single, pointIntegral_route_independent G R S p]

/-- Divisor integration is independent of the chosen integral routes. -/
theorem divisorClass_route_independent (S : VertexRoutes G q)
    (D : (unitGraph G).Divisor) : divisorClass G R D = divisorClass G S D :=
  DFunLike.congr_fun (divisorClass_eq_of_routes G R S) D

/-- Integration of the actual divisor-level Abel construction. -/
theorem divisorClass_abelDivisor {I : Type*} [Fintype I]
    (D : (unitGraph G).Divisor) (p : I → (unitGraph G).Point) :
    divisorClass G R ((unitGraph G).abelDivisor D p) =
      divisorClass G R D - ∑ i, pointIntegral G R (p i) := by
  simp [RealLengthGraph.abelDivisor, RealLengthGraph.movingDivisor, map_sum]

section VertexDivisors

variable [Fintype V]

/-- Extend integral coefficients on the finite vertex set by zero to the
canonical graph point set. -/
def fixedVertexDivisor (F : V → ℤ) : (unitGraph G).Divisor :=
  ∑ v, Finsupp.single ((unitGraph G).vertex v) (F v)

omit [Fintype E] [DecidableEq E] in
@[simp] theorem fixedVertexDivisor_vertex (F : V → ℤ) (v : V) :
    fixedVertexDivisor G F ((unitGraph G).vertex v) = F v := by
  classical
  simp [fixedVertexDivisor, Finsupp.single_apply]

omit [Fintype E] [DecidableEq V] [DecidableEq E] in
@[simp] theorem fixedVertexDivisor_interior (F : V → ℤ) (e : E)
    (t : Set.Ioo (0 : ℝ) 1) :
    fixedVertexDivisor G F ((unitGraph G).interior e t) = 0 := by
  classical
  simp [fixedVertexDivisor]

omit [Fintype E] [DecidableEq V] [DecidableEq E] in
/-- The extension has exactly the sum of its original coefficients as degree. -/
@[simp] theorem degree_fixedVertexDivisor (F : V → ℤ) :
    (unitGraph G).degree (fixedVertexDivisor G F) = ∑ v, F v := by
  change (unitGraph G).degreeHom (∑ v, Finsupp.single ((unitGraph G).vertex v) (F v)) = _
  rw [map_sum]
  simp [RealLengthGraph.degreeHom]

omit [Fintype E] [DecidableEq V] [DecidableEq E] in
/-- Every extended graph divisor is supported on the original vertices. -/
theorem fixedVertexDivisor_vertexSupported (F : V → ℤ) :
    (unitGraph G).VertexSupported (fixedVertexDivisor G F) := by
  intro e t
  exact fixedVertexDivisor_interior G F e t

omit [Fintype E] [DecidableEq E] in
/-- Every vertex-supported divisor is the extension of its vertex coefficients. -/
theorem fixedVertexDivisor_of_vertexSupported {D : (unitGraph G).Divisor}
    (hD : (unitGraph G).VertexSupported D) :
    fixedVertexDivisor G (fun v => D ((unitGraph G).vertex v)) = D := by
  ext p
  rcases (unitGraph G).point_cases p with ⟨v, rfl⟩ | ⟨e, t, rfl⟩
  · exact fixedVertexDivisor_vertex G _ v
  · rw [fixedVertexDivisor_interior, hD e t]

omit [Fintype E] [DecidableEq E] in
/-- The vertex-coefficient presentation exhausts vertex-supported divisors. -/
theorem vertexSupported_iff_exists_fixedVertexDivisor (D : (unitGraph G).Divisor) :
    (unitGraph G).VertexSupported D ↔ ∃ F : V → ℤ, fixedVertexDivisor G F = D := by
  constructor
  · intro hD
    exact ⟨fun v => D ((unitGraph G).vertex v), fixedVertexDivisor_of_vertexSupported G hD⟩
  · rintro ⟨F, rfl⟩
    exact fixedVertexDivisor_vertexSupported G F

/-- Integrating a fixed vertex divisor is the sum of its integral routes. -/
theorem divisorClass_fixedVertexDivisor (F : V → ℤ) :
    divisorClass G R (fixedVertexDivisor G F) =
      classMap G (castChain (∑ v, F v • R.chain v)) := by
  simp only [fixedVertexDivisor, map_sum, divisorClass_single, pointIntegral_vertex, map_zsmul]

end VertexDivisors

/-- The real edge chain obtained from a list of moving edge coordinates.
The edge list is arbitrary: repetitions and loops are permitted. -/
def edgeChain {I : Type*} [Fintype I] (edges : I → E) (x : I → ℝ) : E → ℝ :=
  ∑ i, x i • (Pi.single (edges i) (1 : ℝ) : E → ℝ)

/-- The integral affine offset of the Abel map on a product of closed edges. -/
def cornerChain [Fintype V] {I : Type*} [Fintype I]
    (F : V → ℤ) (edges : I → E) : E → ℤ :=
  (∑ v, F v • R.chain v) - ∑ i, R.chain (G.source (edges i))

/-- The divisor Abel map on a closed edge product has its explicit affine
representative in the chain-coordinate Jacobian. -/
theorem divisorClass_edgeAbelDivisor [Fintype V] {I : Type*} [Fintype I]
    (F : V → ℤ) (edges : I → E) (x : (unitGraph G).EdgeProduct edges) :
    divisorClass G R ((unitGraph G).edgeAbelDivisor (fixedVertexDivisor G F) edges x) =
      classMap G (castChain (cornerChain G R F edges) -
        edgeChain edges (fun i => (x i : ℝ))) := by
  simp only [RealLengthGraph.edgeAbelDivisor, divisorClass_abelDivisor,
    divisorClass_fixedVertexDivisor, pointIntegral_closedEdgeMap,
    cornerChain, edgeChain, map_sub, map_sum, map_add]
  rw [Finset.sum_add_distrib]
  abel

/-- The same affine formula for an arbitrary vertex-supported source divisor. -/
theorem divisorClass_edgeAbelDivisor_of_vertexSupported [Fintype V]
    {I : Type*} [Fintype I] (D : (unitGraph G).Divisor)
    (hD : (unitGraph G).VertexSupported D)
    (edges : I → E) (x : (unitGraph G).EdgeProduct edges) :
    divisorClass G R ((unitGraph G).edgeAbelDivisor D edges x) =
      classMap G (castChain
        (cornerChain G R (fun v => D ((unitGraph G).vertex v)) edges) -
        edgeChain edges (fun i => (x i : ℝ))) := by
  simpa only [fixedVertexDivisor_of_vertexSupported G hD] using
    divisorClass_edgeAbelDivisor G R (fun v => D ((unitGraph G).vertex v)) edges x

/-- The actual moving divisor attached to a pseudo-divisor label: coefficients
at original vertices, minus one chip on each exceptional edge. -/
def pseudoDivisor [Fintype V] (T : UnitPseudoDivisor.PseudoDivisorType V E)
    (x : (unitGraph G).EdgeProduct (fun e : {e : E // e ∈ T.exceptional} => e.val)) :
    (unitGraph G).Divisor :=
  (unitGraph G).edgeAbelDivisor (fixedVertexDivisor G T.coefficients)
    (fun e : {e : E // e ∈ T.exceptional} => e.val) x

omit [Fintype E] [DecidableEq V] [DecidableEq E] in
/-- The actual moving divisor has precisely the degree of its pseudo-divisor label,
including parameter values at edge endpoints. -/
@[simp] theorem degree_pseudoDivisor [Fintype V]
    (T : UnitPseudoDivisor.PseudoDivisorType V E)
    (x : (unitGraph G).EdgeProduct (fun e : {e : E // e ∈ T.exceptional} => e.val)) :
    (unitGraph G).degree (pseudoDivisor G T x) = T.degree := by
  simp [pseudoDivisor, UnitPseudoDivisor.PseudoDivisorType.degree]

/-- A quasistable type gives actual divisors whose degree is the polarization degree. -/
theorem degree_pseudoDivisor_of_quasistable [Fintype V]
    {μ : V → ℝ} {root : V} {T : UnitPseudoDivisor.PseudoDivisorType V E}
    (hT : UnitPseudoDivisor.IsQuasistableType G μ root T)
    (x : (unitGraph G).EdgeProduct (fun e : {e : E // e ∈ T.exceptional} => e.val)) :
    ((unitGraph G).degree (pseudoDivisor G T x) : ℝ) = polarizationDegree μ := by
  rw [degree_pseudoDivisor]
  exact hT.degree_eq

/-- Integer-degree version of the preceding degree compatibility theorem. -/
theorem degree_pseudoDivisor_of_quasistable_int [Fintype V]
    {μ : V → ℝ} {root : V} {T : UnitPseudoDivisor.PseudoDivisorType V E} {d : ℤ}
    (hT : UnitPseudoDivisor.IsQuasistableType G μ root T)
    (hμ : polarizationDegree μ = (d : ℝ))
    (x : (unitGraph G).EdgeProduct (fun e : {e : E // e ∈ T.exceptional} => e.val)) :
    (unitGraph G).degree (pseudoDivisor G T x) = d := by
  rw [degree_pseudoDivisor]
  exact hT.degree_eq_int hμ

/-- Pseudo-divisor cells use the same proved divisor-to-chain coordinate map. -/
theorem divisorClass_pseudoDivisor [Fintype V]
    (T : UnitPseudoDivisor.PseudoDivisorType V E)
    (x : (unitGraph G).EdgeProduct (fun e : {e : E // e ∈ T.exceptional} => e.val)) :
    divisorClass G R (pseudoDivisor G T x) =
      classMap G (castChain (cornerChain G R T.coefficients
        (fun e : {e : E // e ∈ T.exceptional} => e.val)) -
          edgeChain (fun e : {e : E // e ∈ T.exceptional} => e.val)
            (fun e => (x e : ℝ))) :=
  divisorClass_edgeAbelDivisor G R T.coefficients _ x

end UnitAbelMap
end TropicalCurves
