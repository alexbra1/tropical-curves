import TropicalCurves.UnitJacobian
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Tactic.Abel

/-!
# Integral routes on a connected unit-length graph

Connectivity is expressed using the ordinary undirected skeleton of the
endpoint graph. Parallel edges and loops remain in the chain spaces; only
the auxiliary connectivity graph forgets their multiplicity and loops.

Every walk gives an integral edge chain with the prescribed endpoint boundary.
These routes define vertex Abel--Jacobi classes independently of path choices,
and their endpoint compatibility lets edge-integral formulas descend to the
actual point set of the metric graph.
-/

noncomputable section

namespace TropicalCurves
namespace UnitRoutes

open FiniteStability UnitJacobian

variable {V E : Type*}

/-- The underlying undirected simple graph, used only to state connectivity.
Its edges are the distinct-endpoint edges of the original endpoint graph. -/
def skeleton (G : EndpointGraph V E) : SimpleGraph V where
  Adj v w := v ≠ w ∧ ∃ e,
    (G.source e = v ∧ G.target e = w) ∨ (G.source e = w ∧ G.target e = v)
  symm := by
    intro v w h
    obtain ⟨hvw, e, he⟩ := h
    exact ⟨hvw.symm, e, he.elim Or.inr Or.inl⟩
  loopless := by
    intro v h
    exact h.1 rfl

variable [Fintype E] [DecidableEq V] [DecidableEq E]

/-- An adjacent step has an integral chain with its signed endpoint boundary. -/
theorem exists_chain_of_adj (G : EndpointGraph V E) {v w : V}
    (h : (skeleton G).Adj v w) :
    ∃ c : E → ℤ, integerBoundary G c = Pi.single w 1 - Pi.single v 1 := by
  obtain ⟨_, e, he⟩ := h
  rcases he with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · exact ⟨Pi.single e 1, by rw [integerBoundary_single, hs, ht]⟩
  · refine ⟨-Pi.single e 1, ?_⟩
    rw [map_neg, integerBoundary_single, hs, ht, neg_sub]

/-- Summing the signed edge chains along any walk gives its endpoint boundary. -/
theorem exists_chain_of_walk (G : EndpointGraph V E) {v w : V}
    (p : (skeleton G).Walk v w) :
    ∃ c : E → ℤ, integerBoundary G c = Pi.single w 1 - Pi.single v 1 := by
  induction p with
  | nil => exact ⟨0, by simp⟩
  | cons h p ih =>
    obtain ⟨a, ha⟩ := exists_chain_of_adj G h
    obtain ⟨b, hb⟩ := ih
    refine ⟨a + b, ?_⟩
    rw [map_add, ha, hb]
    abel

/-- Ordinary graph connectedness supplies all the required integral routes. -/
theorem exists_chain_of_connected (G : EndpointGraph V E)
    (hG : (skeleton G).Connected) (q v : V) :
    ∃ c : E → ℤ, integerBoundary G c = Pi.single v 1 - Pi.single q 1 := by
  obtain ⟨p⟩ := hG q v
  exact exists_chain_of_walk G p

/-- A choice of integral routes from a fixed vertex to every graph vertex. -/
structure VertexRoutes (G : EndpointGraph V E) (q : V) where
  chain : V → E → ℤ
  boundary_chain : ∀ v,
    integerBoundary G (chain v) = Pi.single v 1 - Pi.single q 1

/-- Choose routes from graph connectedness. No extra algebraic connectivity
assumption is imposed on the boundary map. -/
def routes_of_connected (G : EndpointGraph V E) (q : V)
    (hG : (skeleton G).Connected) : VertexRoutes G q where
  chain v := Classical.choose (exists_chain_of_connected G hG q v)
  boundary_chain v := Classical.choose_spec (exists_chain_of_connected G hG q v)

namespace VertexRoutes

variable {G : EndpointGraph V E} {q : V}

omit [DecidableEq E] in
/-- Two integral routes to the same endpoint differ by an integral cycle. -/
theorem route_difference_cycle (R S : VertexRoutes G q) (v : V) :
    integerBoundary G (R.chain v - S.chain v) = 0 := by
  rw [map_sub, R.boundary_chain, S.boundary_chain, sub_self]

omit [DecidableEq E] in
/-- Vertex Abel--Jacobi classes do not depend on the selected routes. -/
theorem route_class_independent (R S : VertexRoutes G q) (v : V) :
    classMap G (castChain (R.chain v)) = classMap G (castChain (S.chain v)) := by
  apply sub_eq_zero.mp
  have hz := classMap_integerCycle G (R.chain v - S.chain v)
    (route_difference_cycle R S v)
  simpa only [map_sub] using hz

/-- Traversing one complete unit edge has the same Jacobian class as the
chosen route to its target. This proves the edge formulas match at endpoints. -/
theorem endpoint_class (R : VertexRoutes G q) (e : E) :
    classMap G (castChain (R.chain (G.source e)) + Pi.single e (1 : ℝ)) =
      classMap G (castChain (R.chain (G.target e))) := by
  have hc : integerBoundary G
      (R.chain (G.source e) + Pi.single e 1 - R.chain (G.target e)) = 0 := by
    rw [map_sub, map_add, R.boundary_chain, integerBoundary_single,
      R.boundary_chain]
    abel
  apply sub_eq_zero.mp
  have hz := classMap_integerCycle G
    (R.chain (G.source e) + Pi.single e 1 - R.chain (G.target e)) hc
  simpa only [map_sub, map_add, castChain_single, Int.cast_one] using hz

end VertexRoutes

end UnitRoutes
end TropicalCurves
