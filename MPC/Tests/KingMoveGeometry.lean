import MPC.Geometry.KingMoveGeometry
import Mathlib.Tactic.IntervalCases
import Lean
/-!
# MPC.Tests.KingMoveGeometry

The per-move steps of Proposition 2.2 for both owners: a king stepping off its
own rook's file is a discovered check, the kings were aligned before and are not
afterwards. A king that jumps along the enemy king's rank satisfies every other
premise and stays aligned, so the movement condition is needed. Two coordinate
examples show the finite-geometry premises are needed. Board updates here make
no complete-legality claim.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "King move geometry verification must not import GameSeq"

namespace MPC
namespace KingMoveGeometryTests

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
-- A one-step move off the file (the same square for both owners), and a jump onto
-- the enemy king's rank.
private def step : Pos := (1, 2)
private def jump (p : Player) : Pos := (5, if p = .sente then 4 else 0)

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

private theorem after_grid (p : Player) (dst q : Pos) (hd : dst ≠ col p 2) :
    (applyMove (initial p) (kingMove p dst)).board.grid q =
      if q = dst then some ⟨p, .king⟩
      else if q = col p 2 then none else (initial p).board.grid q := by
  unfold kingMove
  by_cases hq : q = dst
  · subst q
    rw [ite_eq_left rfl, applyMove_boardMove_grid_dst]
    cases p <;> rfl
  · by_cases hs : q = col p 2
    · subst q
      rw [ite_eq_right hq, ite_eq_left rfl]
      exact applyMove_boardMove_grid_src (initial p) (col p 2) dst false (Ne.symm hd)
    · rw [ite_eq_right hq, ite_eq_right hs]
      exact applyMove_boardMove_grid_other (initial p) (col p 2) dst false q hs hq

private theorem placed (p : Player) : KingsWellPlaced (initial p).board (positions p) := by
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

-- After the king leaves the file, the enemy king is too far to attack it.
private theorem after_safe (p : Player) (dst : Pos) (hd2 : dst ≠ col p 2)
    (hfar : Pos.dirTo (col p 4) dst ∉ PieceType.king.stepDirs.map (Dir.forPlayer · p.opponent)) :
    ¬ inCheckOriented (applyMove (initial p) (kingMove p dst)).board p dst := by
  rintro ⟨pos, piece, hp, ho, ha⟩
  rw [after_grid p dst pos hd2] at hp
  dsimp only [initial] at hp
  split_ifs at hp <;> cases hp
  all_goals first
    | (cases p <;> cases ho; done)
    | (rename_i h; subst h
       rcases ha with hs | ⟨_, hsd, _⟩
       · exact hfar hs
       · simp [PieceType.slideDirs] at hsd)

private theorem rook_check (p : Player) (dst : Pos) (hd1 : dst ≠ col p 1) (hd2 : dst ≠ col p 2)
    (hd3 : dst ≠ col p 3) (hd0 : col p 0 ≠ dst) :
    inCheckOriented (applyMove (initial p) (kingMove p dst)).board p.opponent (col p 4) := by
  refine ⟨col p 0, ⟨p, .rook⟩, ?_, by cases p <;> rfl, ?_⟩
  · rw [after_grid p dst _ hd2, ite_eq_right hd0, ite_eq_right (by cases p <;> decide)]
    cases p <;> rfl
  · refine (col_attack _ p).mpr ((col_clear _ p).mpr ⟨?_, ?_, ?_⟩)
    · rw [after_grid p dst _ hd2, ite_eq_right (Ne.symm hd1), ite_eq_right (by cases p <;> decide)]
      cases p <;> rfl
    · rw [after_grid p dst _ hd2, ite_eq_right (Ne.symm hd2), ite_eq_left rfl]
    · rw [after_grid p dst _ hd2, ite_eq_right (Ne.symm hd3), ite_eq_right (by cases p <;> decide)]
      cases p <;> rfl

private def premisesOf (p : Player) (dst : Pos) : Prop :=
  let tr := MoveTrace.single (initial p) (kingMove p dst)
  let kp := tr.kingPositionsFrom (positions p)
  tr.FollowsTransitions ∧ tr.BoardMoveSourcesOwned ∧ tr.KingsWellPlaced kp ∧
    tr.EveryMoveLeavesOwnKingSafe kp ∧ tr.InitialOpponentKingSafe kp ∧
    tr.EveryMoveChecksOpponent kp

-- All transition and safety premises and every move checking, for any destination off the
-- file and away from the enemy king.
private theorem premises (p : Player) (dst : Pos) (hd0 : col p 0 ≠ dst) (hd1 : dst ≠ col p 1)
    (hd2 : dst ≠ col p 2) (hd3 : dst ≠ col p 3) (hd4 : dst ≠ col p 4)
    (hfar : Pos.dirTo (col p 4) dst ∉ PieceType.king.stepDirs.map (Dir.forPlayer · p.opponent)) :
    premisesOf p dst := by
  dsimp only [premisesOf]
  let tr := MoveTrace.single (initial p) (kingMove p dst)
  have ht := MoveTrace.single_followsTransitions (initial p) (kingMove p dst)
  have hempty : (initial p).board.grid dst = none := by
    dsimp only [initial]
    rw [ite_eq_right (Ne.symm hd0), ite_eq_right hd2, ite_eq_right hd4]
  refine ⟨ht, ?_, ?_, ?_, ?_, ?_⟩
  · intro i src dst' pr hm; have hi := Fin.eq_zero i; subst i
    change Move.boardMove (col p 2) dst false = .boardMove src dst' pr at hm
    cases hm
    exact ⟨⟨p, .king⟩, by cases p <;> rfl, rfl⟩
  · apply MoveTrace.kingsWellPlaced_kingPositionsFrom tr (positions p) ht
    · intro i o; have hi := Fin.eq_zero i; subst i
      change (initial p).board.grid dst ≠ some ⟨o, .king⟩
      rw [hempty]
      exact nofun
    · intro i pt dst' hm; change Move.boardMove _ _ _ = .dropMove pt dst' at hm; cases hm
    · exact placed p
  · intro i; have hi := Fin.eq_zero i; subst i
    have h := after_safe p dst hd2 hfar
    cases p
    · exact h
    · exact h
  · cases p
    exacts [start_safe .sente, start_safe .gote]
  · intro i; have hi := Fin.eq_zero i; subst i
    have h := rook_check p dst hd1 hd2 hd3 hd0
    cases p
    · exact h
    · exact h

/-! ## A king step off the file -/

-- Both owners. The kings are never adjacent, the king moves to its destination,
-- the move is a discovered check, the kings shared
-- the file before, and they share no line afterwards.
example (p : Player) :
    let tr := MoveTrace.single (initial p) (kingMove p step)
    let kp := tr.kingPositionsFrom (positions p)
    (∀ k o, ¬ attacksOriented (tr.states k).board o .king (kp k o) (kp k o.opponent)) ∧
    kp 1 p = step ∧
    hasUnblockedCheckerOriented (tr.before (0 : Fin 1)).board (tr.after (0 : Fin 1)).board
      (tr.moves (0 : Fin 1)) p.opponent (kp 1 p.opponent) ∧
    Pos.isAligned (kp 0 p) (kp 0 p.opponent) ∧ ¬ Pos.isAligned (kp 1 p) (kp 1 p.opponent) := by
  dsimp only
  obtain ⟨ht, hs, hk, hsafe, h0, hc⟩ :=
    premises p step (by cases p <;> decide) (by cases p <;> decide) (by cases p <;> decide)
      (by cases p <;> decide) (by cases p <;> decide) (by cases p <;> decide)
  let tr := MoveTrace.single (initial p) (kingMove p step)
  have hr : tr.BoardMovesFollowCanMoveToOriented := by
    intro i src dst pr piece hm hp; have hi := Fin.eq_zero i; subst i
    change Move.boardMove (col p 2) step false = .boardMove src dst pr at hm
    cases hm
    change (initial p).board.grid (col p 2) = some piece at hp
    have hp' : (initial p).board.grid (col p 2) = some ⟨p, .king⟩ := by cases p <;> rfl
    rw [hp'] at hp
    cases hp
    exact Or.inl (by cases p <;> decide)
  have hm : tr.moves (0 : Fin 1) =
      .boardMove (tr.kingPositionsFrom (positions p) (0 : Fin 1).castSucc
        (tr.before (0 : Fin 1)).turn) step false := by
    cases p <;> rfl
  refine ⟨tr.kings_not_adjacent _ hk hsafe h0, ?_,
    tr.kingMove_unblockedChecker _ ht hs hk hsafe h0 hc (0 : Fin 1) step false hm,
    tr.kingMove_aligned_before _ ht hs hk hsafe h0 hc (0 : Fin 1) step false hm,
    tr.kingMove_not_aligned_after _ ht hs hk hsafe h0 hc hr (0 : Fin 1) step false hm⟩
  refine (tr.kingPos_succ_of_boardMove _ ht hk (0 : Fin 1) (col p 2) step false rfl p).trans ?_
  cases p <;> rfl

/-! ## The movement condition is needed -/

-- Both owners. A king that jumps onto the enemy king's rank satisfies every other
-- premise and moves, yet the kings remain aligned; so the trace cannot follow the
-- owner-oriented movement condition.
example (p : Player) :
    let tr := MoveTrace.single (initial p) (kingMove p (jump p))
    let kp := tr.kingPositionsFrom (positions p)
    Pos.isAligned (kp 0 p) (kp 0 p.opponent) ∧ Pos.isAligned (kp 1 p) (kp 1 p.opponent) ∧
    ¬ tr.BoardMovesFollowCanMoveToOriented := by
  dsimp only
  obtain ⟨ht, hs, hk, hsafe, h0, hc⟩ :=
    premises p (jump p) (by cases p <;> decide) (by cases p <;> decide) (by cases p <;> decide)
      (by cases p <;> decide) (by cases p <;> decide) (by cases p <;> decide)
  let tr := MoveTrace.single (initial p) (kingMove p (jump p))
  have hm : tr.moves (0 : Fin 1) =
      .boardMove (tr.kingPositionsFrom (positions p) (0 : Fin 1).castSucc
        (tr.before (0 : Fin 1)).turn) (jump p) false := by
    cases p <;> rfl
  have hal : Pos.isAligned (tr.kingPositionsFrom (positions p) 1 p)
      (tr.kingPositionsFrom (positions p) 1 p.opponent) := by
    cases p <;> simp only [Pos.isAligned] <;> decide
  exact ⟨tr.kingMove_aligned_before _ ht hs hk hsafe h0 hc (0 : Fin 1) (jump p) false hm, hal,
    fun hr => tr.kingMove_not_aligned_after _ ht hs hk hsafe h0 hc hr (0 : Fin 1) (jump p) false hm hal⟩

/-! ## The finite-geometry premises are needed -/

-- Without `e ≠ -d`: stepping back along the line keeps the alignment.
example :
    let src : Pos := (2, 2)
    let dst : Pos := (2, 1)
    let target : Pos := (2, 4)
    target.toInt = (src.toInt.1 + ↑(2 : ℕ) * 0, src.toInt.2 + ↑(2 : ℕ) * 1) ∧
    Pos.dirTo src dst ∈ PieceType.king.stepDirs ∧ Pos.dirTo src dst ≠ (0, 1) ∧
    Pos.dirTo dst target ∉ PieceType.king.stepDirs ∧ Pos.isAligned dst target := by
  simp only [Pos.isAligned]
  decide

-- Without `m ≥ 2`: from one diagonal step before the target, a sideways step
-- lands on the target's rank two squares away.
example :
    let src : Pos := (2, 2)
    let dst : Pos := (1, 3)
    let target : Pos := (3, 3)
    target.toInt = (src.toInt.1 + ↑(1 : ℕ) * 1, src.toInt.2 + ↑(1 : ℕ) * 1) ∧
    Pos.dirTo src dst ∈ PieceType.king.stepDirs ∧ Pos.dirTo src dst ≠ (1, 1) ∧
    Pos.dirTo src dst ≠ (-1, -1) ∧
    Pos.dirTo dst target ∉ PieceType.king.stepDirs ∧ Pos.isAligned dst target := by
  simp only [Pos.isAligned]
  decide

end KingMoveGeometryTests
end MPC
