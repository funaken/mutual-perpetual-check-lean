import MPC.Basic.Lemmas
import MPC.Geometry.OpenableGeometry
import MPC.Geometry.AngleKey
/-!
# MPC.Invariants.CheckerAngle

The checking square of each state, and how a move relates the angle keys of the
checkers and the destination.

In a periodic mutual-check trace every state has exactly one checking square:
every move checks (`EveryMoveChecksOpponent`), state `0` equals the last state, and
there is no double check (`checker_unique_of_periodic`). `checkerSquare` names it.
Before move `i` it holds a piece of the side not to move, attacking the mover's king.

- `destination_eq_or_onRay_checker`: the move answers the check. Its destination is
  the checker's square, or a square strictly between the checker and the mover's
  king on the checker's half-line (Corollary 3.4's second half, in half-line form).
- `angleKey_destination_eq_checker`: so, seen from the mover's own king, the
  destination makes the same angle as the checker. In the paper, the enemy's direct
  check `Q` lies on the line along which `P` glared at the enemy king, so `Q` makes
  the angle `P` made.
- `destination_eq_or_angleKey_lt_checker`: seen from the other king, against the
  mover's king, the destination makes a strictly smaller angle unless it captures
  the checker (Remark 4.4: `iang m = 0` for a capture, `iang m < 0` for an
  interposition). This needs the checker off the kings' line
  (`lineSide_kings_checkerSquare_ne_zero`, from Proposition 3.6).
- `checkerSquare_succ_cases`: after a move, the checker is on the destination (a
  direct check), or it is the unblocked checker of a board move, on the source's
  half-line from the checked king, so it makes the source's angle (Remark 4.5: for
  a discovered check, `α` is the angle of `D`).

-/

namespace MPC

/-- All points of one half-line from `K` have the same key. -/
theorem angleKey_eq_of_onRay {K L A B : Pos} {e : Dir} {a b : ℤ} (hA : OnRay K e a A)
    (hB : OnRay K e b B) : angleKey K L A = angleKey K L B := by
  obtain ⟨_, ha, hA⟩ := hA
  obtain ⟨_, hb, hB⟩ := hB
  have a1 : A.toInt.1 = K.toInt.1 + a * e.1 := congrArg Prod.fst hA
  have a2 : A.toInt.2 = K.toInt.2 + a * e.2 := congrArg Prod.snd hA
  have b1 : B.toInt.1 = K.toInt.1 + b * e.1 := congrArg Prod.fst hB
  have b2 : B.toInt.2 = K.toInt.2 + b * e.2 := congrArg Prod.snd hB
  unfold angleKey
  -- `b (A - K) = a (B - K)`: both are `a b e`.
  rw [← vecKey_of_mul b hb (A.toInt.1 - K.toInt.1, A.toInt.2 - K.toInt.2)
      (b * (A.toInt.1 - K.toInt.1), b * (A.toInt.2 - K.toInt.2)) _ rfl rfl]
  exact vecKey_of_mul a ha _ _ _ (by simp only; rw [a1, b1]; ring)
    (by simp only; rw [a2, b2]; ring)

/-- A point nearer to `T` on a half-line from `T` has a smaller key against `T`,
    unless the half-line lies on the line through `K` and `T`. -/
theorem angleKey_lt_of_onRay {K T Q C : Pos} {e : Dir} {n c : ℤ} (hQ : OnRay T e n Q)
    (hC : OnRay T e c C) (hcn : c < n) (hside : lineSide K T Q ≠ 0) :
    angleKey K T C < angleKey K T Q := by
  obtain ⟨_, _, hQ⟩ := hQ
  obtain ⟨_, hc, hC⟩ := hC
  refine angleKey_lt_of_between K T Q C (-e.1, -e.2) (n - c) n (by omega) (by omega) ?_ ?_ hside
  · rw [hC, hQ]
    ext <;> simp only <;> ring
  · rw [hQ]
    ext <;> simp only <;> ring

namespace MoveTrace

open Classical in
/-- The checking square of state `k`: a square whose piece attacks its enemy king,
    or the first player's king square when there is none. In a periodic
    mutual-check trace it is the unique checking square
    (`isCheckerAt_checkerSquare`, `checkerSquare_eq_of_isCheckerAt`). -/
noncomputable def checkerSquare (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (k : Fin (tr.len + 1)) : Pos :=
  if h : ∃ q, tr.IsCheckerAt kp k q then Classical.choose h else kp k .sente

/-- In a periodic mutual-check trace both kings stay on their initial squares. -/
theorem kingPos_eq_of_mutualPerpetualCheck (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hm : tr.MutualPerpetualCheck kp)
    (k : Fin (tr.len + 1)) : kp k = kp 0 :=
  tr.kingPos_eq_of_periodic kp hm.transitions hm.sourcesOwned hm.kingsWellPlaced
    hm.ownKingSafe hm.initialOpponentSafe hm.checks hm.movementRules hm.periodic k

/-- Every state has a checking square: after each move by `EveryMoveChecksOpponent`,
    and at state `0` because it equals the last state. -/
theorem exists_checker_of_mutualPerpetualCheck (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hm : tr.MutualPerpetualCheck kp)
    (k : Fin (tr.len + 1)) : ∃ q, tr.IsCheckerAt kp k q := by
  have succ_case : ∀ i : Fin tr.len, ∃ q, tr.IsCheckerAt kp i.succ q := by
    intro i
    obtain ⟨pos, piece, hp, ho, hatk⟩ := hm.checks i
    refine ⟨pos, piece, hp, ?_⟩
    have hopp : piece.owner.opponent = (tr.before i).turn.opponent := by
      rw [ho, Player.opponent_opponent]
    rw [hopp]
    exact hatk
  rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨j, rfl⟩
  · have hlen := hm.nonempty
    obtain ⟨i, hi⟩ : ∃ i : Fin tr.len, i.succ = Fin.last tr.len :=
      ⟨⟨tr.len - 1, by omega⟩, Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; omega)⟩
    obtain ⟨q, piece, hp, hatk⟩ := succ_case i
    rw [hi] at hp hatk
    refine ⟨q, piece, ?_, ?_⟩
    · rw [← hm.periodic]
      exact hp
    · rw [← hm.periodic, ← hm.periodic.kingPos_last hm.kingsWellPlaced]
      exact hatk
  · exact succ_case j

/-- The checking square of every state holds a checker. -/
theorem isCheckerAt_checkerSquare (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (hm : tr.MutualPerpetualCheck kp) (k : Fin (tr.len + 1)) :
    tr.IsCheckerAt kp k (tr.checkerSquare kp k) := by
  have h := tr.exists_checker_of_mutualPerpetualCheck kp hm k
  unfold checkerSquare
  rw [dite_eq_left h]
  exact Classical.choose_spec h

/-- Every checking square of a state is its `checkerSquare` (no double check). -/
theorem checkerSquare_eq_of_isCheckerAt (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hm : tr.MutualPerpetualCheck kp)
    {k : Fin (tr.len + 1)} {q : Pos} (hq : tr.IsCheckerAt kp k q) :
    tr.checkerSquare kp k = q :=
  tr.checker_unique_of_periodic kp hm.transitions hm.sourcesOwned hm.kingsWellPlaced
    hm.ownKingSafe hm.initialOpponentSafe hm.checks hm.movementRules hm.periodic hm.nonempty k
    _ _ (tr.isCheckerAt_checkerSquare kp hm k) hq

/-- Before a move, the checking square holds a piece of the side not to move,
    attacking the mover's king. -/
theorem checkerSquare_before (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (hm : tr.MutualPerpetualCheck kp) (i : Fin tr.len) :
    ∃ X : Piece, (tr.before i).board.grid (tr.checkerSquare kp i.castSucc) = some X ∧
      X.owner = (tr.before i).turn.opponent ∧
      attacksOriented (tr.before i).board X.owner X.pieceType (tr.checkerSquare kp i.castSucc)
        (kp i.castSucc (tr.before i).turn) := by
  obtain ⟨X, hX, hatk⟩ := tr.isCheckerAt_checkerSquare kp hm i.castSucc
  have ho : X.owner = (tr.before i).turn.opponent := by
    rcases Player.eq_or_eq_opponent X.owner (tr.before i).turn with ho | ho
    · exfalso
      apply tr.before_opponent_not_inCheck kp hm.transitions hm.ownKingSafe
        hm.initialOpponentSafe i
      refine ⟨_, X, hX, by rw [ho, Player.opponent_opponent], ?_⟩
      rw [ho] at hatk ⊢
      exact hatk
    · exact ho
  refine ⟨X, hX, ho, ?_⟩
  have hopp : X.owner.opponent = (tr.before i).turn := by rw [ho, Player.opponent_opponent]
  rw [hopp] at hatk
  exact hatk

/-- Corollary 3.4's second half in half-line form: a move lands on the checking
    square, or strictly between it and the mover's king on its half-line from that
    king. -/
theorem destination_eq_or_onRay_checker (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hm : tr.MutualPerpetualCheck kp)
    (i : Fin tr.len) :
    (tr.moves i).destination = tr.checkerSquare kp i.castSucc ∨
      ∃ (e : Dir) (n c : ℤ),
        OnRay (kp i.castSucc (tr.before i).turn) e n (tr.checkerSquare kp i.castSucc) ∧
        OnRay (kp i.castSucc (tr.before i).turn) e c (tr.moves i).destination ∧ c < n := by
  obtain ⟨X, hX, ho, hatk⟩ := tr.checkerSquare_before kp hm i
  have hkm : kp i.succ (tr.before i).turn = kp i.castSucc (tr.before i).turn := by
    rw [tr.kingPos_eq_of_mutualPerpetualCheck kp hm i.succ,
      tr.kingPos_eq_of_mutualPerpetualCheck kp hm i.castSucc]
  rcases tr.destination_on_checker_line kp hm.transitions hm.sourcesOwned hm.ownKingSafe i hkm
      _ X hX ho hatk with h | ⟨hmem, hns⟩
  · exact Or.inl h
  · right
    obtain ⟨e, n, hray, _, hiff⟩ := ray_of_attack_not_step _ _ _ _ _ hatk hns
    obtain ⟨c, hc1, hcn, hq⟩ := (hiff _).mp hmem
    exact ⟨e, n, c, hray, ⟨hray.1, by omega, hq⟩, hcn⟩

/-- Seen from the mover's own king, a move's destination makes the same angle as the
    checking square it answers. -/
theorem angleKey_destination_eq_checker (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hm : tr.MutualPerpetualCheck kp)
    (i : Fin tr.len) (L : Pos) :
    angleKey (kp i.castSucc (tr.before i).turn) L (tr.moves i).destination =
      angleKey (kp i.castSucc (tr.before i).turn) L (tr.checkerSquare kp i.castSucc) := by
  rcases tr.destination_eq_or_onRay_checker kp hm i with h | ⟨e, n, c, hQ, hC, _⟩
  · rw [h]
  · exact angleKey_eq_of_onRay hC hQ

/-- Remark 4.4: seen from another king `K`, against the mover's king, a move's
    destination makes a strictly smaller angle than the checking square, unless it
    captures the checker. The checker must be off the line through `K` and the
    mover's king. -/
theorem destination_eq_or_angleKey_lt_checker (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hm : tr.MutualPerpetualCheck kp)
    (i : Fin tr.len) (K : Pos)
    (hside : lineSide K (kp i.castSucc (tr.before i).turn) (tr.checkerSquare kp i.castSucc) ≠ 0) :
    (tr.moves i).destination = tr.checkerSquare kp i.castSucc ∨
      angleKey K (kp i.castSucc (tr.before i).turn) (tr.moves i).destination <
        angleKey K (kp i.castSucc (tr.before i).turn) (tr.checkerSquare kp i.castSucc) := by
  rcases tr.destination_eq_or_onRay_checker kp hm i with h | ⟨e, n, c, hQ, hC, hcn⟩
  · exact Or.inl h
  · exact Or.inr (angleKey_lt_of_onRay hQ hC hcn hside)

/-- Proposition 3.6 for the checking square: it is off the line through both
    kings. -/
theorem lineSide_kings_checkerSquare_ne_zero (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hm : tr.MutualPerpetualCheck kp)
    (k : Fin (tr.len + 1)) (p : Player) :
    lineSide (kp 0 p) (kp 0 p.opponent) (tr.checkerSquare kp k) ≠ 0 := by
  intro h0
  apply tr.checker_off_kingLine_of_periodic kp hm.transitions hm.sourcesOwned hm.kingsWellPlaced
    hm.ownKingSafe hm.initialOpponentSafe hm.checks hm.movementRules hm.periodic hm.dropsEmpty
    hm.nonempty k (tr.checkerSquare kp k)
  obtain ⟨X, hX, hatk⟩ := tr.isCheckerAt_checkerSquare kp hm k
  refine ⟨X, hX, hatk, ?_⟩
  have hcol := (lineSide_eq_zero_iff_collinear _ _ _).mp h0
  cases p
  · exact hcol
  · exact (Geometry.collinear_swap _ _ _).mp hcol

/-- After a move the checking square is the destination (a direct check), or the
    unblocked checker of a board move. That checker stands on the source's half-line
    from the checked king, so it makes the source's angle (Remark 4.5). -/
theorem checkerSquare_succ_cases (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (hm : tr.MutualPerpetualCheck kp) (i : Fin tr.len) :
    tr.checkerSquare kp i.succ = (tr.moves i).destination ∨
      ∃ (src dst : Pos) (promote : Bool), tr.moves i = .boardMove src dst promote ∧
        hasUnblockedCheckerOriented (tr.before i).board (tr.after i).board (tr.moves i)
          (tr.before i).turn.opponent (kp i.succ (tr.before i).turn.opponent) ∧
        ∀ L : Pos, angleKey (kp i.succ (tr.before i).turn.opponent) L (tr.checkerSquare kp i.succ) =
          angleKey (kp i.succ (tr.before i).turn.opponent) L src := by
  rcases (tr.everyMoveChecksOpponent_iff_destination_or_unblocked_of_safe kp hm.transitions
      hm.sourcesOwned hm.kingsWellPlaced hm.ownKingSafe hm.initialOpponentSafe).mp hm.checks i
    with hd | hu
  · left
    obtain ⟨piece, hp, ho, hatk⟩ := hd
    apply tr.checkerSquare_eq_of_isCheckerAt kp hm
    refine ⟨piece, hp, ?_⟩
    have hopp : piece.owner.opponent = (tr.before i).turn.opponent := by
      rw [ho, Player.opponent_opponent]
    rw [hopp]
    exact hatk
  · right
    have key : ∀ mv : Move, tr.moves i = mv →
        ∃ (src dst : Pos) (promote : Bool), tr.moves i = .boardMove src dst promote ∧
          hasUnblockedCheckerOriented (tr.before i).board (tr.after i).board (tr.moves i)
            (tr.before i).turn.opponent (kp i.succ (tr.before i).turn.opponent) ∧
          ∀ L : Pos, angleKey (kp i.succ (tr.before i).turn.opponent) L
              (tr.checkerSquare kp i.succ) =
            angleKey (kp i.succ (tr.before i).turn.opponent) L src := by
      intro mv hmv
      cases mv with
      | dropMove pt dst =>
        rw [hmv] at hu
        exact hu.elim
      | boardMove src dst promote =>
        have hu' := hu
        rw [hmv] at hu'
        obtain ⟨pos, piece, _, _, hpb, hpa, hpo, hatk, hsrc, _⟩ := hu'
        have hown : piece.owner = (tr.before i).turn := by rw [hpo, Player.opponent_opponent]
        have hns : Pos.dirTo pos (kp i.succ (tr.before i).turn.opponent) ∉
            piece.pieceType.stepDirs.map (Dir.forPlayer · piece.owner) := by
          have h := tr.not_stepAttack_of_before kp hm.transitions hm.ownKingSafe
            hm.initialOpponentSafe i pos piece hpb hown
          rw [tr.kingPos_eq_of_mutualPerpetualCheck kp hm i.castSucc] at h
          rw [tr.kingPos_eq_of_mutualPerpetualCheck kp hm i.succ]
          exact h
        obtain ⟨e, n, hray, _, hiff⟩ := ray_of_attack_not_step _ _ _ _ _ hatk hns
        obtain ⟨c, hc1, _, hq⟩ := (hiff _).mp hsrc
        have hchk : tr.checkerSquare kp i.succ = pos := by
          apply tr.checkerSquare_eq_of_isCheckerAt kp hm
          refine ⟨piece, hpa, ?_⟩
          have hopp : piece.owner.opponent = (tr.before i).turn.opponent := by rw [hown]
          rw [hopp]
          exact hatk
        refine ⟨src, dst, promote, hmv, hu, fun L => ?_⟩
        rw [hchk]
        exact angleKey_eq_of_onRay hray ⟨hray.1, by omega, hq⟩
    exact key _ rfl

end MoveTrace
end MPC
