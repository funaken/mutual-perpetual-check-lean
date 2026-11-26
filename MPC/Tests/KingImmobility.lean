import MPC.Basic.Lemmas
import MPC.Geometry.KingImmobility
import Mathlib.Tactic.IntervalCases
import Lean
/-!
# MPC.Tests.KingImmobility

Proposition 2.2 for both first movers.

- A two-move trace: a king steps off its own rook's file (a discovered check),
  then the opponent drops a gold that blocks the rook and checks the king. It
  satisfies every premise except periodicity. The kings stop being aligned and
  stay that way; the drop moves no king. Because a king moves, periodicity
  cannot be dropped from the immobility theorems.
- A periodic four-move trace in which the two kings step away and back on an
  otherwise empty board. It satisfies every premise except mutual check, and
  its kings become aligned after being unaligned while a king moves. So the
  mutual-check premise cannot be dropped either.

Whether the movement condition is needed for the periodic theorems is not
exhibited here;  shows it is needed for the per-move step. Board
updates make no complete-legality claim.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "King immobility verification must not import GameSeq"

namespace MPC
namespace KingImmobilityTests

/-! ## A non-periodic mutual-check trace with a king move -/

private def col (p : Player) (j : Fin 9) : Pos := (0, if p = .sente then j else 4 - j)
-- The mover's king blocks its own rook on the file of the enemy king.
private def initial (p : Player) : BoardState :=
  { board :=
    { grid := fun q =>
        if q = col p 0 then some ⟨p, .rook⟩
        else if q = col p 2 then some ⟨p, .king⟩
        else if q = col p 4 then some ⟨p.opponent, .king⟩ else none
      hand := fun _ => ∅ }
    turn := p }
private def kingMove (p : Player) (dst : Pos) : Move := .boardMove (col p 2) dst false
private def positions (p : Player) : Player → Pos := fun o => if o = p then col p 2 else col p 4
private def step : Pos := (1, 2)
-- The opponent's reply: a gold on the vacated square.
private def drop (p : Player) : Move := .dropMove .gold (col p 2)
private def s1 (p : Player) : BoardState := applyMove (initial p) (kingMove p step)
private def s2 (p : Player) : BoardState := applyMove (s1 p) (drop p)

private def trA (p : Player) : MoveTrace where
  len := 2
  states := fun k => match k.val with
    | 0 => initial p
    | 1 => s1 p
    | _ => s2 p
  moves := fun i => match i.val with
    | 0 => kingMove p step
    | _ => drop p

private theorem col_clear (b : Board) (p : Player) :
    pathClear b (col p 0) (col p 4) ↔
      b.grid (col p 1) = none ∧ b.grid (col p 2) = none ∧ b.grid (col p 3) = none := by
  have hc := pathClear_iff_of_exact_steps b (col p 0) (col p 4)
    (0, if p = .sente then 1 else -1) 4 (by cases p <;> decide) (by decide)
    (by cases p <;> decide) (by cases p <;> decide) (by cases p <;> decide)
  constructor
  · intro h
    have h1 := hc.mp h 1 (by decide) (by decide) (by cases p <;> unfold onBoard <;> decide)
    have h2 := hc.mp h 2 (by decide) (by decide) (by cases p <;> unfold onBoard <;> decide)
    have h3 := hc.mp h 3 (by decide) (by decide) (by cases p <;> unfold onBoard <;> decide)
    cases p <;> exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    apply hc.mpr
    intro j hj hjn hob
    interval_cases j <;> cases p <;> assumption

private theorem col_attack (b : Board) (p : Player) :
    attacksOriented b p .rook (col p 0) (col p 4) ↔ pathClear b (col p 0) (col p 4) := by
  constructor
  · rintro (hs | ⟨_, _, _, _, _, _, _, hc⟩)
    · simp [PieceType.stepDirs] at hs
    · exact hc
  · intro hc
    refine Or.inr ⟨(0, if p = .sente then 1 else -1), ?_, ?_, 4, by decide, ?_, ?_, hc⟩ <;>
      cases p <;> decide

private theorem s1_grid (p : Player) (q : Pos) :
    (s1 p).board.grid q =
      if q = step then some ⟨p, .king⟩
      else if q = col p 2 then none else (initial p).board.grid q := by
  unfold s1 kingMove
  have hd : step ≠ col p 2 := by cases p <;> decide
  by_cases hq : q = step
  · subst q
    rw [ite_eq_left rfl, applyMove_boardMove_grid_dst]
    cases p <;> rfl
  · by_cases hs : q = col p 2
    · subst q
      rw [ite_eq_right hq, ite_eq_left rfl]
      exact applyMove_boardMove_grid_src (initial p) (col p 2) step false (Ne.symm hd)
    · rw [ite_eq_right hq, ite_eq_right hs]
      exact applyMove_boardMove_grid_other (initial p) (col p 2) step false q hs hq

private theorem s2_grid (p : Player) (q : Pos) :
    (s2 p).board.grid q =
      if q = col p 2 then some ⟨p.opponent, .gold⟩ else (s1 p).board.grid q := by
  unfold s2 drop
  by_cases hq : q = col p 2
  · subst q
    rw [ite_eq_left rfl, applyMove_dropMove_grid_dst]
    rfl
  · rw [ite_eq_right hq]
    exact applyMove_dropMove_grid_other (s1 p) .gold (col p 2) q hq

private theorem placedA (p : Player) : KingsWellPlaced (initial p).board (positions p) := by
  intro o q
  cases p <;> cases o <;> by_cases h1 : q = (0, 0) <;> by_cases h2 : q = (0, 2) <;>
    by_cases h3 : q = (0, 4) <;> simp_all [initial, positions, col, Player.opponent]

-- Initially the rook is blocked by the mover's own king, which is too far to check.
private theorem start_safe (p : Player) :
    ¬ inCheckOriented (initial p).board p.opponent (col p 4) := by
  rintro ⟨pos, piece, hp, ho, ha⟩
  dsimp only [initial] at hp
  split_ifs at hp
  · cases hp; subst pos
    have h := ((col_clear _ p).mp ((col_attack _ p).mp ha)).2.1
    cases p <;> simp [initial, col] at h
  · cases hp; subst pos
    rcases ha with hs | ⟨_, hsd, _⟩
    · revert hs
      cases p <;> decide
    · simp [PieceType.slideDirs] at hsd
  · cases hp; cases p <;> cases ho

-- After the king steps off the file, the enemy king is too far to attack it.
private theorem s1_safe (p : Player) : ¬ inCheckOriented (s1 p).board p step := by
  rintro ⟨pos, piece, hp, ho, ha⟩
  rw [s1_grid] at hp
  dsimp only [initial] at hp
  split_ifs at hp <;> cases hp
  all_goals first
    | (cases p <;> cases ho; done)
    | (rename_i h; subst h
       rcases ha with hs | ⟨_, hsd, _⟩
       · revert hs
         cases p <;> decide
       · simp [PieceType.slideDirs] at hsd)

-- The rook's file is now clear, so the step is a discovered check.
private theorem s1_check (p : Player) : inCheckOriented (s1 p).board p.opponent (col p 4) := by
  refine ⟨col p 0, ⟨p, .rook⟩, ?_, by cases p <;> rfl, ?_⟩
  · rw [s1_grid, ite_eq_right (by cases p <;> decide), ite_eq_right (by cases p <;> decide)]
    cases p <;> rfl
  · refine (col_attack _ p).mpr ((col_clear _ p).mpr ⟨?_, ?_, ?_⟩)
    · rw [s1_grid, ite_eq_right (by cases p <;> decide), ite_eq_right (by cases p <;> decide)]
      cases p <;> rfl
    · rw [s1_grid, ite_eq_right (by cases p <;> decide), ite_eq_left rfl]
    · rw [s1_grid, ite_eq_right (by cases p <;> decide), ite_eq_right (by cases p <;> decide)]
      cases p <;> rfl

-- The gold blocks the rook, and the stepped king is too far to attack.
private theorem s2_safe (p : Player) : ¬ inCheckOriented (s2 p).board p.opponent (col p 4) := by
  rintro ⟨pos, piece, hp, ho, ha⟩
  rw [s2_grid] at hp
  split_ifs at hp with h0
  · cases hp; cases p <;> cases ho
  · rw [s1_grid] at hp
    dsimp only [initial] at hp
    split_ifs at hp <;> cases hp
    all_goals first
      | (cases p <;> cases ho; done)
      | (rename_i h; subst h
         have hb := ((col_clear _ p).mp ((col_attack _ p).mp ha)).2.1
         rw [s2_grid, ite_eq_left rfl] at hb
         cases hb)
      | (rename_i h; subst h
         rcases ha with hs | ⟨_, hsd, _⟩
         · revert hs
           cases p <;> decide
         · simp [PieceType.slideDirs] at hsd)

-- The gold checks the stepped king from the side.
private theorem s2_check (p : Player) : inCheckOriented (s2 p).board p step := by
  refine ⟨col p 2, ⟨p.opponent, .gold⟩, ?_, rfl, Or.inl (by cases p <;> decide)⟩
  rw [s2_grid, ite_eq_left rfl]

private def premisesA (p : Player) : Prop :=
  let tr := trA p
  let kp := tr.kingPositionsFrom (positions p)
  tr.FollowsTransitions ∧ tr.BoardMoveSourcesOwned ∧ tr.KingsWellPlaced kp ∧
    tr.EveryMoveLeavesOwnKingSafe kp ∧ tr.InitialOpponentKingSafe kp ∧
    tr.EveryMoveChecksOpponent kp ∧ tr.BoardMovesFollowCanMoveToOriented

-- Every premise of the immobility theorems except periodicity.
private theorem premisesA_hold (p : Player) : premisesA p := by
  dsimp only [premisesA]
  let tr := trA p
  have ht : tr.FollowsTransitions := by
    intro i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  refine ⟨ht, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i src dst pr hm
    match i with
    | ⟨0, _⟩ =>
      change Move.boardMove (col p 2) step false = .boardMove src dst pr at hm
      cases hm
      exact ⟨⟨p, .king⟩, by cases p <;> rfl, rfl⟩
    | ⟨1, _⟩ =>
      change Move.dropMove .gold (col p 2) = .boardMove src dst pr at hm
      cases hm
  · apply MoveTrace.kingsWellPlaced_kingPositionsFrom tr (positions p) ht
    · intro i
      match i with
      | ⟨0, _⟩ =>
        show ∀ owner, (initial p).board.grid step ≠ some ⟨owner, .king⟩
        intro o
        have h : (initial p).board.grid step = none := by cases p <;> rfl
        rw [h]
        exact nofun
      | ⟨1, _⟩ =>
        show ∀ owner, (s1 p).board.grid (col p 2) ≠ some ⟨owner, .king⟩
        intro o
        rw [s1_grid, ite_eq_right (by cases p <;> decide), ite_eq_left rfl]
        exact nofun
    · intro i pt dst hm
      match i with
      | ⟨0, _⟩ =>
        change Move.boardMove (col p 2) step false = .dropMove pt dst at hm
        cases hm
      | ⟨1, _⟩ =>
        change Move.dropMove .gold (col p 2) = .dropMove pt dst at hm
        cases hm
        exact (by decide)
    · exact placedA p
  · intro i
    match i with
    | ⟨0, _⟩ =>
      have h := s1_safe p
      cases p
      · exact h
      · exact h
    | ⟨1, _⟩ =>
      have h := s2_safe p
      cases p
      · exact h
      · exact h
  · cases p
    exacts [start_safe .sente, start_safe .gote]
  · intro i
    match i with
    | ⟨0, _⟩ =>
      have h := s1_check p
      cases p
      · exact h
      · exact h
    | ⟨1, _⟩ =>
      have h := s2_check p
      cases p
      · exact h
      · exact h
  · intro i src dst pr piece hm hp
    match i with
    | ⟨0, _⟩ =>
      change Move.boardMove (col p 2) step false = .boardMove src dst pr at hm
      cases hm
      change (initial p).board.grid (col p 2) = some piece at hp
      have hp' : (initial p).board.grid (col p 2) = some ⟨p, .king⟩ := by cases p <;> rfl
      rw [hp'] at hp
      cases hp
      exact Or.inl (by cases p <;> decide)
    | ⟨1, _⟩ =>
      change Move.dropMove .gold (col p 2) = .boardMove src dst pr at hm
      cases hm

private theorem kingMoveAt_zero (p : Player) :
    (trA p).KingMoveAt ((trA p).kingPositionsFrom (positions p)) (0 : Fin 2) :=
  ⟨step, false, by cases p <;> rfl⟩

private theorem not_periodic (p : Player) : ¬ (trA p).IsPeriodic := by
  intro h
  have hg := congrArg (fun s : BoardState => s.board.grid step) h
  change (s2 p).board.grid step = (initial p).board.grid step at hg
  rw [s2_grid, ite_eq_right (by cases p <;> decide), s1_grid, ite_eq_left rfl] at hg
  have hi : (initial p).board.grid step = none := by cases p <;> rfl
  rw [hi] at hg
  cases hg

-- Both first movers. The king move needs aligned kings before it and ends the
-- alignment; the drop moves no king and lands on no king's square, and the
-- alignment stays lost. Since a king moves, the trace cannot be periodic.
example (p : Player) :
    let tr := trA p
    let kp := tr.kingPositionsFrom (positions p)
    tr.KingMoveAt kp (0 : Fin 2) ∧ ¬ tr.KingMoveAt kp (1 : Fin 2) ∧
    kp (2 : Fin 3) = kp (1 : Fin 3) ∧ (∀ o, kp (1 : Fin 3) o ≠ col p 2) ∧
    KingsAligned (kp (0 : Fin 3)) ∧ ¬ KingsAligned (kp (1 : Fin 3)) ∧
    ¬ KingsAligned (kp (2 : Fin 3)) ∧ ¬ tr.IsPeriodic := by
  dsimp only
  obtain ⟨ht, hs, hk, hsafe, h0, hc, _⟩ := premisesA_hold p
  let tr := trA p
  have hnk : ¬ tr.KingMoveAt (tr.kingPositionsFrom (positions p)) (1 : Fin 2) := by
    rintro ⟨d, pr, hm⟩
    change Move.dropMove .gold (col p 2) = _ at hm
    cases hm
  have hal0 : KingsAligned (tr.kingPositionsFrom (positions p) (0 : Fin 3)) := by
    cases p <;> simp only [KingsAligned, Pos.isAligned] <;> decide
  have hal1 : ¬ KingsAligned (tr.kingPositionsFrom (positions p) (1 : Fin 3)) := by
    cases p <;> simp only [KingsAligned, Pos.isAligned] <;> decide
  refine ⟨kingMoveAt_zero p, hnk,
    tr.kingPos_succ_of_not_kingMove _ ht hs hk (1 : Fin 2) hnk,
    fun o => tr.dropMove_dst_ne_kingPos _ ht hs hk hsafe h0 hc (1 : Fin 2) .gold (col p 2) rfl o,
    hal0, hal1, fun h => hal1 ?_, not_periodic p⟩
  exact tr.kingsAligned_of_le _ ht hs hk hsafe h0 hc (j := (1 : Fin 3)) (k := (2 : Fin 3))
    (by change (1 : Fin 3) ≤ 2; decide) h

-- Both first movers. Every premise except periodicity holds and a king moves, so
-- periodicity cannot be dropped from `not_kingMoveAt_of_periodic`.
example (p : Player) :
    let tr := trA p
    let kp := tr.kingPositionsFrom (positions p)
    tr.FollowsTransitions ∧ tr.BoardMoveSourcesOwned ∧ tr.KingsWellPlaced kp ∧
    tr.EveryMoveLeavesOwnKingSafe kp ∧ tr.InitialOpponentKingSafe kp ∧
    tr.EveryMoveChecksOpponent kp ∧ tr.BoardMovesFollowCanMoveToOriented ∧
    tr.KingMoveAt kp (0 : Fin 2) ∧ ¬ tr.IsPeriodic := by
  obtain ⟨ht, hs, hk, hsafe, h0, hc, hr⟩ := premisesA_hold p
  exact ⟨ht, hs, hk, hsafe, h0, hc, hr, kingMoveAt_zero p, not_periodic p⟩

/-! ## A periodic king shuffle without checks -/

-- Only the two kings: the first mover's at `a`, the opponent's at `b`.
private def kb (p : Player) (a b : Pos) (t : Player) : BoardState :=
  { board :=
    { grid := fun q =>
        if q = a then some ⟨p, .king⟩ else if q = b then some ⟨p.opponent, .king⟩ else none
      hand := fun _ => ∅ }
    turn := t }
private def kpos (p : Player) (a b : Pos) : Player → Pos := fun o => if o = p then a else b

private theorem kb_moveA (p : Player) (a a' b : Pos) (t : Player) (ha : a' ≠ a) (hab : a ≠ b)
    (hb : a' ≠ b) : applyMove (kb p a b t) (.boardMove a a' false) = kb p a' b t.opponent := by
  simp only [applyMove, kb, Board.setGrid, ha, hb, ↓reduceIte,
    Bool.false_eq_true, BoardState.mk.injEq, Board.mk.injEq, and_true]
  funext q
  by_cases h1 : q = a' <;> by_cases h2 : q = a <;> by_cases h3 : q = b <;> simp_all

private theorem kb_moveB (p : Player) (a b b' : Pos) (t : Player) (hb : b' ≠ b) (hab : a ≠ b)
    (ha : b' ≠ a) : applyMove (kb p a b t) (.boardMove b b' false) = kb p a b' t.opponent := by
  simp only [applyMove, kb, Board.setGrid, ha, hb, Ne.symm hab, ↓reduceIte,
    Bool.false_eq_true, BoardState.mk.injEq, Board.mk.injEq, and_true]
  funext q
  by_cases h1 : q = b' <;> by_cases h2 : q = a <;> by_cases h3 : q = b <;> simp_all

private theorem kb_placed (p : Player) (a b : Pos) (t : Player) (hab : a ≠ b) :
    KingsWellPlaced (kb p a b t).board (kpos p a b) := by
  intro o q
  cases p <;> cases o <;> by_cases h1 : q = a <;> by_cases h2 : q = b <;>
    simp_all [kb, kpos, Player.opponent]

-- With no adjacent kings, neither king is in check.
private theorem kb_safe (p : Player) (a b : Pos) (t : Player)
    (hfar : ∀ o : Player, Pos.dirTo a b ∉ PieceType.king.stepDirs.map (Dir.forPlayer · o) ∧
      Pos.dirTo b a ∉ PieceType.king.stepDirs.map (Dir.forPlayer · o))
    (o : Player) : ¬ inCheckOriented (kb p a b t).board o (kpos p a b o) := by
  rintro ⟨pos, piece, hp, ho, ha⟩
  simp only [kb] at hp
  split_ifs at hp with h1 h2 <;> cases hp
  · subst h1
    rcases ha with hs | ⟨_, hsd, _⟩
    · cases p <;> cases o <;> simp [Player.opponent] at ho
      · exact (hfar _).1 hs
      · exact (hfar _).1 hs
    · simp [PieceType.slideDirs] at hsd
  · subst h2
    rcases ha with hs | ⟨_, hsd, _⟩
    · cases p <;> cases o <;> simp [Player.opponent] at ho
      · exact (hfar _).2 hs
      · exact (hfar _).2 hs
    · simp [PieceType.slideDirs] at hsd

private def a0 : Pos := (0, 0)
private def a1 : Pos := (1, 0)
private def b0 : Pos := (8, 7)
private def b1 : Pos := (8, 8)

private def shuffle (p : Player) : MoveTrace where
  len := 4
  states := fun k => match k.val with
    | 0 => kb p a0 b0 p
    | 1 => kb p a1 b0 p.opponent
    | 2 => kb p a1 b1 p
    | 3 => kb p a0 b1 p.opponent
    | _ => kb p a0 b0 p
  moves := fun i => match i.val with
    | 0 => .boardMove a0 a1 false
    | 1 => .boardMove b0 b1 false
    | 2 => .boardMove a1 a0 false
    | _ => .boardMove b1 b0 false

private def kpS (p : Player) : Fin ((shuffle p).len + 1) → Player → Pos := fun k =>
  match k.val with
  | 0 => kpos p a0 b0
  | 1 => kpos p a1 b0
  | 2 => kpos p a1 b1
  | 3 => kpos p a0 b1
  | _ => kpos p a0 b0

private theorem far (a b : Pos)
    (h : Pos.dirTo a b ∉ PieceType.king.stepDirs ∧ Pos.dirTo b a ∉ PieceType.king.stepDirs ∧
      Pos.dirTo a b ∉ PieceType.king.stepDirs.map (Dir.forPlayer · .gote) ∧
      Pos.dirTo b a ∉ PieceType.king.stepDirs.map (Dir.forPlayer · .gote)) (o : Player) :
    Pos.dirTo a b ∉ PieceType.king.stepDirs.map (Dir.forPlayer · o) ∧
      Pos.dirTo b a ∉ PieceType.king.stepDirs.map (Dir.forPlayer · o) := by
  cases o
  · simp only [Dir.forPlayer, List.map_id']
    exact ⟨h.1, h.2.1⟩
  · exact h.2.2

-- Both first movers. Placement, safety, movement, and periodicity hold, but no
-- move checks. The kings start unaligned and become aligned while a king moves,
-- so the mutual-check premise cannot be dropped.
example (p : Player) :
    let tr := shuffle p
    let kp := kpS p
    tr.FollowsTransitions ∧ tr.BoardMoveSourcesOwned ∧ tr.KingsWellPlaced kp ∧
    tr.EveryMoveLeavesOwnKingSafe kp ∧ tr.InitialOpponentKingSafe kp ∧
    tr.BoardMovesFollowCanMoveToOriented ∧ tr.IsPeriodic ∧ ¬ tr.EveryMoveChecksOpponent kp ∧
    kp (Fin.last 4) = kp 0 ∧ tr.KingMoveAt kp (0 : Fin 4) ∧
    ¬ KingsAligned (kp (0 : Fin 5)) ∧ KingsAligned (kp (1 : Fin 5)) := by
  dsimp only
  have f00 := far a0 b0 (by decide)
  have f10 := far a1 b0 (by decide)
  have f11 := far a1 b1 (by decide)
  have f01 := far a0 b1 (by decide)
  have ht : (shuffle p).FollowsTransitions := by
    intro i
    match i with
    | ⟨0, _⟩ => exact (kb_moveA p a0 a1 b0 p (by decide) (by decide) (by decide)).symm
    | ⟨1, _⟩ =>
      show kb p a1 b1 p = applyMove (kb p a1 b0 p.opponent) (.boardMove b0 b1 false)
      rw [kb_moveB p a1 b0 b1 _ (by decide) (by decide) (by decide), Player.opponent_opponent]
    | ⟨2, _⟩ => exact (kb_moveA p a1 a0 b1 p (by decide) (by decide) (by decide)).symm
    | ⟨3, _⟩ =>
      show kb p a0 b0 p = applyMove (kb p a0 b1 p.opponent) (.boardMove b1 b0 false)
      rw [kb_moveB p a0 b1 b0 _ (by decide) (by decide) (by decide), Player.opponent_opponent]
  have hp : (shuffle p).IsPeriodic := rfl
  have hk : (shuffle p).KingsWellPlaced (kpS p) := by
    intro k
    match k with
    | ⟨0, _⟩ => exact kb_placed p a0 b0 p (by decide)
    | ⟨1, _⟩ => exact kb_placed p a1 b0 p.opponent (by decide)
    | ⟨2, _⟩ => exact kb_placed p a1 b1 p (by decide)
    | ⟨3, _⟩ => exact kb_placed p a0 b1 p.opponent (by decide)
    | ⟨4, _⟩ => exact kb_placed p a0 b0 p (by decide)
  refine ⟨ht, ?_, hk, ?_, kb_safe p a0 b0 p f00 p.opponent, ?_, hp, ?_, hp.kingPos_last hk,
    ⟨a1, false, by cases p <;> rfl⟩, by cases p <;> simp only [KingsAligned, Pos.isAligned] <;>
      decide, by cases p <;> simp only [KingsAligned, Pos.isAligned] <;> decide⟩
  · intro i src dst pr hm
    match i with
    | ⟨0, _⟩ =>
      change Move.boardMove a0 a1 false = .boardMove src dst pr at hm
      cases hm
      exact ⟨⟨p, .king⟩, by show (kb p a0 b0 p).board.grid a0 = _; simp [kb], rfl⟩
    | ⟨1, _⟩ =>
      change Move.boardMove b0 b1 false = .boardMove src dst pr at hm
      cases hm
      exact ⟨⟨p.opponent, .king⟩,
        by show (kb p a1 b0 p.opponent).board.grid b0 = _; simp [kb, a1, b0], rfl⟩
    | ⟨2, _⟩ =>
      change Move.boardMove a1 a0 false = .boardMove src dst pr at hm
      cases hm
      exact ⟨⟨p, .king⟩, by show (kb p a1 b1 p).board.grid a1 = _; simp [kb], rfl⟩
    | ⟨3, _⟩ =>
      change Move.boardMove b1 b0 false = .boardMove src dst pr at hm
      cases hm
      exact ⟨⟨p.opponent, .king⟩,
        by show (kb p a0 b1 p.opponent).board.grid b1 = _; simp [kb, a0, b1], rfl⟩
  · intro i
    match i with
    | ⟨0, _⟩ => exact kb_safe p a1 b0 p.opponent f10 p
    | ⟨1, _⟩ => exact kb_safe p a1 b1 p f11 p.opponent
    | ⟨2, _⟩ => exact kb_safe p a0 b1 p.opponent f01 p
    | ⟨3, _⟩ => exact kb_safe p a0 b0 p f00 p.opponent
  · intro i src dst pr piece hm hpc
    match i with
    | ⟨0, _⟩ =>
      change Move.boardMove a0 a1 false = .boardMove src dst pr at hm
      cases hm
      change (kb p a0 b0 p).board.grid a0 = some piece at hpc
      simp only [kb] at hpc
      cases hpc
      exact Or.inl (by cases p <;> decide)
    | ⟨1, _⟩ =>
      change Move.boardMove b0 b1 false = .boardMove src dst pr at hm
      cases hm
      change (kb p a1 b0 p.opponent).board.grid b0 = some piece at hpc
      simp only [kb, ite_eq_right (show b0 ≠ a1 by decide)] at hpc
      cases hpc
      exact Or.inl (by cases p <;> decide)
    | ⟨2, _⟩ =>
      change Move.boardMove a1 a0 false = .boardMove src dst pr at hm
      cases hm
      change (kb p a1 b1 p).board.grid a1 = some piece at hpc
      simp only [kb] at hpc
      cases hpc
      exact Or.inl (by cases p <;> decide)
    | ⟨3, _⟩ =>
      change Move.boardMove b1 b0 false = .boardMove src dst pr at hm
      cases hm
      change (kb p a0 b1 p.opponent).board.grid b1 = some piece at hpc
      simp only [kb, ite_eq_right (show b1 ≠ a0 by decide)] at hpc
      cases hpc
      exact Or.inl (by cases p <;> decide)
  · intro hc
    exact kb_safe p a1 b0 p.opponent f10 p.opponent (hc (0 : Fin 4))

end KingImmobilityTests
end MPC
