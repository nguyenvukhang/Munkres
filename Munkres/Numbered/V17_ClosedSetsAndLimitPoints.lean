import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Topology.Bases
import Munkres.Mathlib.Disjoint
import Munkres.Mathlib.Subtype
import Munkres.Subtype.Topology
import Munkres.Closure.Subtype

open Topology Filter TopologicalSpace

universe u

variable {α : Type u} [TopologicalSpace α]

section S₂
--* Theorem 17.2
-- Let Y be a subspace of X. Then a set A is closed in Y ↔ it equals the
-- intersection of a closed set of X with Y.
variable {Y : Set α}

example {A : Set Y} : IsClosed A ↔ ∃ G, IsClosed G ∧ Subtype.val '' A = Y ∩ G
  := by --
  rw [isClosed_induced_iff]
  simp only [Subtype.preimage_val_eq_iff] -- ∎

example {A : Set α} : IsClosedIn A Y ↔ ∃ G, IsClosed G ∧ A = G ∩ Y
  := by --
  exact IsClosedIn.iff -- ∎
end S₂

section S₃
--* Theorem 17.3
-- Let Y be a subspace of X. If A is closed in Y and Y is closed in X, then A
-- is closed in X .
variable {Y : Set α}

example {A : Set Y} : IsClosed A → IsClosed Y → IsClosed (Subtype.val '' A)
  := by --
  exact IsClosed.trans -- ∎

example {A : Set α} : IsClosedIn A Y → IsClosed Y → IsClosed A
  := by --
  exact IsClosedIn.trans -- ∎
end S₃

section S₄
--* Theorem 17.4
-- Let Y be a subspace of X, A ⊆ Y, let Ā denote the closure of A in X. Then
-- the closure of A in Y equals Ā ∩ Y.
variable {Y : Set α}

--* Theorem 17.4: If A ⊆ Y ⊆ X, the closure of A in Y = (closure A in X) ∩ Y.
example {A : Set Y} : closure A = closure (A : Set α) ∩ Y
  := by --
  exact closure_subtype₂ A -- ∎

--* Theorem 17.4: If A ⊆ Y ⊆ X, the closure of A in Y = (closure A in X) ∩ Y.
example {A : Set α} {hAY : A ⊆ Y} : closure (A.as Y) = closure A ∩ Y
  := by --
  exact closure_subtype₃ hAY -- ∎

end S₄
