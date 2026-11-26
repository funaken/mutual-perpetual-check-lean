import MPC.Invariants.DiscHInvariant
/-!
# MPC.Trace.MutualCheck

The hypotheses and case-analysis skeleton of the main theorem.
`MutualPerpetualCheck` includes the empty-drop condition. The final theorem uses
`PeriodicMutualCheck`, deriving that condition from hand availability and periodicity.

`DiscoveredCheckByEachSide` expresses Proposition 4.1, proved using the angle
potential. `PieceCountsAtMostTwo` expresses the board counts needed by the piece
cases; it is derived from initial board/hand counts and drops from the hand.

A discovered check moves a non-glaring piece by a board move (Lemma 2.5).
The king cannot be that piece (Proposition 2.2). `false_of_no_openableMove`
closes the argument once the other piece types have been excluded.
-/

namespace MPC
namespace MoveTrace

/-- A periodic mutual-check trace: the premises of the main theorem on traces. -/
structure MutualPerpetualCheck (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos) :
    Prop where
  transitions : tr.FollowsTransitions
  sourcesOwned : tr.BoardMoveSourcesOwned
  kingsWellPlaced : tr.KingsWellPlaced kp
  ownKingSafe : tr.EveryMoveLeavesOwnKingSafe kp
  initialOpponentSafe : tr.InitialOpponentKingSafe kp
  checks : tr.EveryMoveChecksOpponent kp
  movementRules : tr.BoardMovesFollowCanMoveToOriented
  periodic : tr.IsPeriodic
  dropsEmpty : tr.DropDestinationsEmpty
  nonempty : 0 < tr.len

/-- Proposition 4.1: each side makes a discovered check, a move with an unblocked
    checker, at some move of the trace. It follows from `MutualPerpetualCheck`. -/
def DiscoveredCheckByEachSide (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos) :
    Prop :=
  ∀ o : Player, ∃ i : Fin tr.len, (tr.before i).turn = o ∧
    hasUnblockedCheckerOriented (tr.before i).board (tr.after i).board (tr.moves i)
      (tr.before i).turn.opponent (kp i.succ (tr.before i).turn.opponent)

open Classical in
/-- The squares of state `k` holding a bishop or a horse. -/
noncomputable def bishopHorseSquares (tr : MoveTrace) (k : Fin (tr.len + 1)) : Finset Pos :=
  Finset.univ.filter fun q => ∃ p : Piece, (tr.states k).board.grid q = some p ∧
    (p.pieceType = .bishop ∨ p.pieceType = .horse)

open Classical in
/-- The squares of state `k` holding a rook or a dragon. -/
noncomputable def rookDragonSquares (tr : MoveTrace) (k : Fin (tr.len + 1)) : Finset Pos :=
  Finset.univ.filter fun q => ∃ p : Piece, (tr.states k).board.grid q = some p ∧
    (p.pieceType = .rook ∨ p.pieceType = .dragon)

/-- The piece counts of shogi as a premise: in every state at most two squares hold
    a bishop or horse, and at most two hold a rook or dragon. -/
def PieceCountsAtMostTwo (tr : MoveTrace) : Prop :=
  ∀ k : Fin (tr.len + 1),
    (tr.bishopHorseSquares k).card ≤ 2 ∧ (tr.rookDragonSquares k).card ≤ 2

/-- Side `o` makes a discovered check by moving its non-glaring piece of type `pt`
    on the board. -/
def OpenableMoveBy (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos) (o : Player)
    (pt : PieceType) : Prop :=
  ∃ (i : Fin tr.len) (src dst : Pos) (promote : Bool),
    (tr.before i).turn = o ∧ tr.moves i = .boardMove src dst promote ∧
    (tr.before i).board.grid src = some ⟨o, pt⟩ ∧
    ¬ tr.GlaresAtEnemyKing kp i.castSucc src ∧
    hasUnblockedCheckerOriented (tr.before i).board (tr.after i).board (tr.moves i)
      o.opponent (kp i.succ o.opponent)

/-- A move with an unblocked checker moves a non-glaring piece of the mover on the
    board: drops never have one, and a glaring source rules one out (Lemma 2.5). -/
theorem openableMove_of_unblockedChecker (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (i : Fin tr.len)
    (hu : hasUnblockedCheckerOriented (tr.before i).board (tr.after i).board (tr.moves i)
      (tr.before i).turn.opponent (kp i.succ (tr.before i).turn.opponent)) :
    ∃ pt : PieceType, tr.OpenableMoveBy kp (tr.before i).turn pt := by
  have key : ∀ mv : Move, tr.moves i = mv →
      ∃ pt : PieceType, tr.OpenableMoveBy kp (tr.before i).turn pt := by
    intro mv hm
    cases mv with
    | boardMove src dst promote =>
      obtain ⟨piece, hp, ho⟩ := hs i src dst promote hm
      refine ⟨piece.pieceType, i, src, dst, promote, rfl, hm, ?_, ?_, hu⟩
      · rw [hp, ← ho]
      · exact fun hg => tr.not_unblockedChecker_of_source_glares kp ht hs hk hsafe h0 i src dst
          promote hm hg hu
    | dropMove pt dst =>
      rw [hm] at hu
      exact hu.elim
  exact key _ rfl

/-- Under Proposition 4.1, each side makes a discovered check by moving some
    non-glaring piece on the board. -/
theorem exists_openableMove (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (hm : tr.MutualPerpetualCheck kp) (h41 : tr.DiscoveredCheckByEachSide kp) (o : Player) :
    ∃ pt : PieceType, tr.OpenableMoveBy kp o pt := by
  obtain ⟨i, hturn, hu⟩ := h41 o
  have h := tr.openableMove_of_unblockedChecker kp hm.transitions hm.sourcesOwned
    hm.kingsWellPlaced hm.ownKingSafe hm.initialOpponentSafe i hu
  rw [hturn] at h
  exact h

/-- Proposition 2.2 for the main argument: in a periodic mutual-check trace the
    piece moved by a discovered check is never a king. -/
theorem not_openableMove_king (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (hm : tr.MutualPerpetualCheck kp) (o : Player) : ¬ tr.OpenableMoveBy kp o .king := by
  rintro ⟨i, src, dst, promote, hturn, hmv, hsrc, _, _⟩
  apply tr.not_kingMoveAt_of_periodic kp hm.transitions hm.sourcesOwned hm.kingsWellPlaced
    hm.ownKingSafe hm.initialOpponentSafe hm.checks hm.movementRules hm.periodic i
  refine ⟨dst, promote, ?_⟩
  have hk : src = kp i.castSucc o := (hm.kingsWellPlaced i.castSucc o src).mp hsrc
  rw [hmv, hk, hturn]

/-- The skeleton of the main theorem: if, in a periodic mutual-check trace with
    Proposition 4.1, no piece type other than the king can be moved by the first
    player's discovered check, there is no such trace. The piece-specific lemmas
    exclude each piece type. -/
theorem false_of_no_openableMove (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (hm : tr.MutualPerpetualCheck kp) (h41 : tr.DiscoveredCheckByEachSide kp)
    (hexcl : ∀ pt : PieceType, pt ≠ .king → ¬ tr.OpenableMoveBy kp .sente pt) : False := by
  obtain ⟨pt, hpt⟩ := tr.exists_openableMove kp hm h41 .sente
  by_cases hking : pt = .king
  · subst hking
    exact tr.not_openableMove_king kp hm .sente hpt
  · exact hexcl pt hking hpt

end MoveTrace
end MPC
