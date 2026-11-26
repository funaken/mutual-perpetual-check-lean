import MPC.Chess.CheckingRaySeparation

namespace MPC.Chess.Tests

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

private def near : RayDirection → Pos
  | .north => (3, 4) | .northEast => (4, 4) | .east => (4, 3) | .southEast => (4, 2)
  | .south => (3, 2) | .southWest => (2, 2) | .west => (2, 3) | .northWest => (2, 4)
private def middle : RayDirection → Pos
  | .north => (3, 5) | .northEast => (5, 5) | .east => (5, 3) | .southEast => (5, 1)
  | .south => (3, 1) | .southWest => (1, 1) | .west => (1, 3) | .northWest => (1, 5)
private def far : RayDirection → Pos
  | .north => (3, 6) | .northEast => (6, 6) | .east => (6, 3) | .southEast => (6, 0)
  | .south => (3, 0) | .southWest => (0, 0) | .west => (0, 3) | .northWest => (0, 6)

-- All eight orientations, with each of the two possible blocking squares.
example (d : RayDirection) : Between (near d) (far d) (middle d) := by
  have h := kingLine_blocker_between (K := (3, 3)) (L := far d) (B := middle d) (A := near d)
    (by cases d <;> decide) (by cases d <;> decide) (by cases d <;> decide)
    (by cases d <;> decide) (by cases d <;> decide) (by cases d <;> decide)
  exact h.resolve_left (by cases d <;> decide)

example (d : RayDirection) : Between (near d) (near d.opposite) (3, 3) := by
  have h := kingLine_blocker_between (K := (3, 3)) (L := near d.opposite) (B := middle d) (A := near d)
    (by cases d <;> decide) (by cases d <;> decide) (by cases d <;> decide)
    (by cases d <;> decide) (by cases d <;> decide) (by cases d <;> decide)
  exact h.resolve_right (by cases d <;> decide)

-- The other king's endpoint/inside cases cannot be silently accepted.
example : ¬ Between (1, 0) (2, 0) (0, 0) ∧ ¬ Between (1, 0) (2, 0) (2, 0) ∧
    Between (7, 7) (0, 0) (4, 4) ∧ ¬ Pos.collinear (0, 0) (7, 7) (4, 3) := by decide

example (d : RayDirection) : rayOffset (Pos.toPlane (3, 3)) (far d).toPlane d = 0 := by
  apply (OnRay.collinear_iff_rayOffset_eq_zero (q := middle d) (by cases d <;> decide)).mp
  cases d <;> decide

private def lineKings (c : Color) : Color → Pos := fun o => if o = c then (0, 0) else (6, 0)
private def overlapBoard (c : Color) : Board := fun q =>
  if q = (0, 0) then some ⟨c, .king⟩
  else if q = (6, 0) then some ⟨c.opponent, .king⟩
  else if q = (2, 0) then some ⟨c.opponent, .rook⟩
  else if q = (4, 0) then some ⟨c, .rook⟩ else none
private def overlapTrace (c : Color) : MoveTrace := .empty ⟨overlapBoard c, c, {}, none⟩

-- Length zero satisfies the move predicates and periodicity, and has correctly
-- placed kings, yet admits checking rays overlapping along the kings' line.
example (c : Color) :
    (overlapTrace c).FollowsLegalMoves ∧ (overlapTrace c).KingsWellPlaced (fun _ => lineKings c) ∧
    (overlapTrace c).EveryMoveChecksOpponent (fun _ => lineKings c) ∧
    (overlapTrace c).BoardTurnPeriodic ∧ (overlapTrace c).len = 0 ∧
    (overlapTrace c).CheckingRay (0, 0) c .east ∧
    (overlapTrace c).CheckingRay (6, 0) c.opponent .west := by
  refine ⟨(fun i => Fin.elim0 i), ?_, (fun i => Fin.elim0 i), ⟨rfl, rfl⟩, rfl, ?_⟩
  · unfold MoveTrace.KingsWellPlaced MPC.Chess.KingsWellPlaced
    cases c <;> decide
  · cases c <;> decide

-- The full closed interval is common, including both kings and non-lattice
-- points. This is not a positive-length mutual-check example.
example (c : Color) (t : ℚ) (ht : 0 ≤ t) (ht' : t ≤ 6) :
    (overlapTrace c).CheckingCrossing (lineKings c) (t, 0) := by
  intro owner
  by_cases he : owner = c
  · subst owner
    refine ⟨.east, ?_, ?_⟩
    · cases c <;> decide
    · simp [lineKings, Pos.toPlane, Pos.toInt, OnRationalRay, rayParameter, rayPoint,
        RayDirection.vector, ht]
  · have he' : owner = c.opponent := by cases owner <;> cases c <;> simp_all [Color.opponent]
    subst owner
    refine ⟨.west, ?_, ?_⟩
    · cases c <;> decide
    · simp only [lineKings, Color.opponent_ne, ite_false]
      norm_num [Pos.toPlane, Pos.toInt, OnRationalRay, rayParameter, rayPoint,
        RayDirection.vector, Fin.coe_ofNat_eq_mod]
      exact ht'

private def prefixKings (c : Color) : Color → Pos := fun o => if o = c then (0, 0) else (4, 0)
private def prefixBoard (c : Color) : Board := fun q =>
  if q = (0, 0) then some ⟨c, .king⟩
  else if q = (4, 0) then some ⟨c.opponent, .king⟩
  else if q = (2, 0) then some ⟨c.opponent, .queen⟩
  else if q = (2, 2) then some ⟨c, .knight⟩
  else if q = (0, 4) then some ⟨c, .bishop⟩ else none
private def prefixMove : ℕ → Move
  | 0 => .boardMove (2, 2) (1, 0) none
  | _ => .boardMove (2, 0) (2, 2) none
private def prefixState (c : Color) : ℕ → Position
  | 0 => ⟨prefixBoard c, c, {}, none⟩
  | n + 1 => applyMove (prefixState c n) (prefixMove n)
private def prefixTrace (c : Color) : MoveTrace where
  len := 2
  states := fun k => prefixState c k.val
  moves := fun i => prefixMove i.val

-- Recurrence is essential: this legal two-move mutual-check prefix starts
-- with a king-line checker and lands a non-glaring knight on that line.
example (c : Color) :
    (prefixTrace c).FollowsLegalMoves ∧ (prefixTrace c).KingsWellPlaced (fun _ => prefixKings c) ∧
    (prefixTrace c).EveryMoveChecksOpponent (fun _ => prefixKings c) ∧
    ¬ (prefixTrace c).BoardTurnPeriodic ∧
    ¬ (prefixTrace c).GlaresAtEnemyKing (fun _ => prefixKings c) 0 (2, 2) ∧
    Pos.collinear (prefixKings c c) (prefixKings c c.opponent) (1, 0) ∧
    attacks (prefixBoard c) ⟨c.opponent, .queen⟩ (2, 0) (prefixKings c c) := by
  constructor
  · intro i
    refine ⟨prefixKings c, ?_, rfl⟩
    have h : ∀ i : Fin 2, LegalMove (prefixState c i.val) (prefixMove i.val) (prefixKings c) := by
      cases c <;> decide
    exact h i
  refine ⟨?_, ?_, ?_, ?_⟩
  · change ∀ i : Fin 3, KingsWellPlaced (prefixState c i.val).board (prefixKings c)
    cases c <;> decide
  · unfold MoveTrace.EveryMoveChecksOpponent
    cases c <;> decide
  · intro h
    have he := congrFun h.1 (2, 0)
    cases c <;> contradiction
  · cases c <;> decide

private def cycleBoard (c : Color) : Board := fun q =>
  if q = (0, 0) then some ⟨c, .king⟩
  else if q = (6, 0) then some ⟨c.opponent, .king⟩
  else if q = (2, 0) then some ⟨c.opponent, .rook⟩
  else if q = (2, 2) then some ⟨c, .knight⟩ else none
private def cycleMove : ℕ → Move
  | 0 => .boardMove (2, 2) (1, 0) none
  | 1 => .boardMove (2, 0) (2, 1) none
  | 2 => .boardMove (1, 0) (2, 2) none
  | _ => .boardMove (2, 1) (2, 0) none
private def cycleState (c : Color) : ℕ → Position
  | 0 => ⟨cycleBoard c, c, {}, none⟩
  | n + 1 => applyMove (cycleState c n) (cycleMove n)
private def cycleTrace (c : Color) : MoveTrace where
  len := 4
  states := fun k => cycleState c k.val
  moves := fun i => cycleMove i.val

-- Legal positive-length recurrence alone does not exclude king-line checks:
-- the initial/final rook checks, but the intervening moves are not all checks.
example (c : Color) :
    (cycleTrace c).FollowsLegalMoves ∧ (cycleTrace c).KingsWellPlaced (fun _ => lineKings c) ∧
    (cycleTrace c).BoardTurnPeriodic ∧
    ¬ (cycleTrace c).EveryMoveChecksOpponent (fun _ => lineKings c) ∧
    (cycleTrace c).CheckingRay (0, 0) c .east ∧ Pos.collinear (0, 0) (6, 0) (2, 0) := by
  constructor
  · intro i
    refine ⟨lineKings c, ?_, rfl⟩
    have h : ∀ i : Fin 4, LegalMove (cycleState c i.val) (cycleMove i.val) (lineKings c) := by
      cases c <;> decide
    exact h i
  refine ⟨?_, ?_, ?_, ?_⟩
  · change ∀ i : Fin 5, KingsWellPlaced (cycleState c i.val).board (lineKings c)
    cases c <;> decide
  · constructor
    · funext q
      have h : ∀ q, (cycleState c 4).board q = cycleBoard c q := by cases c <;> decide
      exact h q
    · cases c <;> rfl
  · intro h
    have h0 := h (0 : Fin 4)
    have hn : ¬ inCheck (cycleState c 1).board c.opponent (lineKings c c.opponent) := by cases c <;> decide
    exact hn h0
  · cases c <;> decide

end MPC.Chess.Tests
