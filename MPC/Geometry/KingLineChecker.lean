import MPC.Basic.Lemmas
import MPC.Geometry.KingLineOpenable
/-!
# MPC.Geometry.KingLineChecker

The paper's Proposition 3.6 on periodic traces: no checking piece stands on the
line through both kings.

Suppose a piece `P` on `A` checks the king `K` of the side to move, and `A` lies
on the line through `K` and `P`'s own king `L`. The reply must lift the check, so
it lands on `A` or strictly between `A` and `K` (Corollary 3.4). That square is on
the kings' line, so by Proposition 3.5 the reply is not an openable piece's move.
Its destination glares, so it checks `L` directly. From strictly between `A` and
`K` that check would cross `K` (if `L` lies beyond `K`) or `A`, where `P` still
stands (if `L` lies beyond `A`). So the reply captures `P` on `A` and checks `L`
from `A`, along the same line. The situation repeats with the sides exchanged.
Every move from then on captures, so the number of occupied squares falls at
every move, which a periodic trace cannot allow.

The capture argument needs drops to land on empty squares, a shogi rule that
MoveTrace does not impose by itself: otherwise two sides can keep re-dropping
onto `A`. That rule is the premise `DropDestinationsEmpty`; the verification
shows a periodic counterexample without it. -/

namespace MPC

private theorem pos_eq_of_toInt {a b : Pos} (h : a.toInt = b.toInt) : a = b := by
  have h1 : (a.1.val : ℤ) = b.1.val := congrArg Prod.fst h
  have h2 : (a.2.val : ℤ) = b.2.val := congrArg Prod.snd h
  exact Prod.ext (Fin.ext (by exact_mod_cast h1)) (Fin.ext (by exact_mod_cast h2))

private theorem slide_mem_king (pt : PieceType) (o : Player) (d : Dir)
    (h : d ∈ pt.slideDirs.map (Dir.forPlayer · o)) : d ∈ PieceType.king.stepDirs := by
  have key : ∀ x ∈ pt.slideDirs.map (Dir.forPlayer · o), x ∈ PieceType.king.stepDirs := by
    cases o <;> cases pt <;> decide
  exact key d h

/-- Three points at parameters `a`, `b`, `c` on a line through `B` with direction
    `d` are collinear. -/
theorem collinear_of_line_params (B P₁ P₂ P₃ : Pos) (d : Dir) (a b c : ℤ)
    (h₁ : P₁.toInt = (B.toInt.1 + a * d.1, B.toInt.2 + a * d.2))
    (h₂ : P₂.toInt = (B.toInt.1 + b * d.1, B.toInt.2 + b * d.2))
    (h₃ : P₃.toInt = (B.toInt.1 + c * d.1, B.toInt.2 + c * d.2)) :
    Geometry.collinear P₁.toInt P₂.toInt P₃.toInt := by
  unfold Geometry.collinear
  rw [h₁, h₂, h₃]
  ring

private theorem collinear_kings_of_sg (kp0 : Player → Pos) (p : Player) (A : Pos)
    (h : Geometry.collinear (kp0 .sente).toInt (kp0 .gote).toInt A.toInt) :
    Geometry.collinear (kp0 p).toInt (kp0 p.opponent).toInt A.toInt := by
  cases p
  · exact h
  · exact (Geometry.collinear_swap _ _ _).mp h

private theorem collinear_sg_of_kings (kp0 : Player → Pos) (p : Player) (A : Pos)
    (h : Geometry.collinear (kp0 p).toInt (kp0 p.opponent).toInt A.toInt) :
    Geometry.collinear (kp0 .sente).toInt (kp0 .gote).toInt A.toInt := by
  cases p
  · exact h
  · exact (Geometry.collinear_swap _ _ _).mp h

namespace MoveTrace

/-- Drops land on empty squares. This shogi rule is not part of MoveTrace. -/
def DropDestinationsEmpty (tr : MoveTrace) : Prop :=
  ∀ (i : Fin tr.len) (pt : PieceType) (dst : Pos),
    tr.moves i = .dropMove pt dst → (tr.before i).board.grid dst = none

/-- The piece on `A` attacks its enemy king, and `A` lies on the line through both
    kings. -/
def CheckerOnKingLine (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (k : Fin (tr.len + 1)) (A : Pos) : Prop :=
  ∃ P : Piece, (tr.states k).board.grid A = some P ∧
    attacksOriented (tr.states k).board P.owner P.pieceType A (kp k P.owner.opponent) ∧
    Geometry.collinear (kp 0 .sente).toInt (kp 0 .gote).toInt A.toInt

open Classical in
/-- The occupied squares of state `k`. -/
noncomputable def occupiedSquares (tr : MoveTrace) (k : Fin (tr.len + 1)) : Finset Pos :=
  Finset.univ.filter fun q => (tr.states k).board.grid q ≠ none

theorem mem_occupiedSquares (tr : MoveTrace) (k : Fin (tr.len + 1)) (q : Pos) :
    q ∈ tr.occupiedSquares k ↔ (tr.states k).board.grid q ≠ none := by
  simp [occupiedSquares]

/-- A board move onto an occupied square empties its source and so lowers the
    number of occupied squares. -/
theorem occupiedSquares_card_succ_lt_of_capture (tr : MoveTrace) (ht : tr.FollowsTransitions)
    (hs : tr.BoardMoveSourcesOwned) (i : Fin tr.len) (src dst : Pos) (promote : Bool)
    (hm : tr.moves i = .boardMove src dst promote) (hsd : src ≠ dst)
    (hcap : (tr.before i).board.grid dst ≠ none) :
    (tr.occupiedSquares i.succ).card < (tr.occupiedSquares i.castSucc).card := by
  have hsrc : src ∈ tr.occupiedSquares i.castSucc := by
    refine (tr.mem_occupiedSquares _ _).mpr ?_
    obtain ⟨piece, hp, _⟩ := hs i src dst promote hm
    change (tr.before i).board.grid src ≠ none
    rw [hp]
    exact Option.some_ne_none _
  refine lt_of_le_of_lt (Finset.card_le_card ?_) (Finset.card_erase_lt_of_mem hsrc)
  intro q hq
  have hocc := (tr.mem_occupiedSquares _ _).mp hq
  have hqs : q ≠ src := by
    rintro rfl
    exact hocc (tr.boardMove_grid_src ht i q dst promote hm hsd)
  refine Finset.mem_erase.mpr ⟨hqs, (tr.mem_occupiedSquares _ _).mpr ?_⟩
  by_cases hqd : q = dst
  · rw [hqd]
    exact hcap
  · have h := tr.boardMove_grid_other ht i src dst promote q hm hqs hqd
    change (tr.before i).board.grid q ≠ none
    rw [← h]
    exact hocc

/-- One step of Proposition 3.6: in a periodic trace satisfying 's
    premises and `DropDestinationsEmpty`, if a checker stands on the kings' line
    at `A` before move `i`, the move captures on `A` by a board move, and the
    capturing piece is again a checker on the kings' line at `A`. -/
theorem checkerOnKingLine_succ_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (hde : tr.DropDestinationsEmpty) (i : Fin tr.len) (A : Pos)
    (h : tr.CheckerOnKingLine kp i.castSucc A) :
    (∃ (src : Pos) (promote : Bool), tr.moves i = .boardMove src A promote) ∧
      (tr.before i).board.grid A ≠ none ∧ tr.CheckerOnKingLine kp i.succ A := by
  obtain ⟨P, hP, hatkP, hcol⟩ := h
  have hkp := tr.kingPos_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp
  have hd := tr.boardMoveEndpointsDistinct_of_oriented hs hr
  have hgd := tr.glaringDestinationsCheck_of_periodic kp ht hs hk hsafe h0 hc hr hp
  -- The checker belongs to the side not to move.
  have hPo : P.owner = (tr.before i).turn.opponent := by
    rcases Player.eq_or_eq_opponent P.owner (tr.before i).turn with ho | ho
    · exfalso
      apply tr.before_opponent_not_inCheck kp ht hsafe h0 i
      refine ⟨A, P, hP, by rw [ho, Player.opponent_opponent], ?_⟩
      rw [show P.owner.opponent = (tr.before i).turn.opponent by rw [ho]] at hatkP
      exact hatkP
    · exact ho
  have hKt : kp i.castSucc P.owner.opponent = kp 0 (tr.before i).turn := by
    rw [hPo, Player.opponent_opponent, hkp]
  rw [hKt] at hatkP
  have hPA : (tr.before i).board.grid A = some P := hP
  have hocc : (tr.before i).board.grid A ≠ none := by
    rw [hPA]
    exact Option.some_ne_none _
  -- Corollary 3.4: the reply lands on `A` or on `P`'s line to the king.
  have hcor := tr.destination_on_checker_line kp ht hs hsafe i
    (by rw [hkp i.succ, hkp i.castSucc]) A P hPA hPo (by rw [hkp i.castSucc]; exact hatkP)
  rw [hkp i.castSucc] at hcor
  obtain ⟨D, hD⟩ : ∃ D, (tr.moves i).destination = D := ⟨_, rfl⟩
  rw [hD] at hcor
  -- A destination on the kings' line glares, so the reply checks directly.
  have hglares : Geometry.collinear (kp 0 .sente).toInt (kp 0 .gote).toInt D.toInt →
      tr.GlaresAtEnemyKing kp i.succ (tr.moves i).destination := by
    intro hcolD
    by_contra hng
    exact tr.openable_destination_off_kingLine_of_periodic kp ht hs hk hsafe h0 hc hr hp i hng
      (by rw [hD]; exact hcolD)
  -- Squares other than the destination and the source keep their contents.
  have hkeep : ∀ q : Pos, q ≠ D → (tr.before i).board.grid q ≠ none →
      (∀ piece : Piece, (tr.before i).board.grid q = some piece →
        piece.owner ≠ (tr.before i).turn) →
      (tr.states i.succ).board.grid q = (tr.before i).board.grid q := by
    intro q hqD _ hown
    have key : ∀ mv : Move, tr.moves i = mv →
        (tr.states i.succ).board.grid q = (tr.before i).board.grid q := by
      intro mv hm
      have hqd : q ≠ mv.destination := by rw [← hm, hD]; exact hqD
      cases mv with
      | boardMove src dst promote =>
        have hqs : q ≠ src := by
          rintro rfl
          obtain ⟨piece, hp', ho⟩ := hs i q dst promote hm
          exact hown piece hp' ho
        exact tr.boardMove_grid_other ht i src dst promote q hm hqs hqd
      | dropMove pt dst =>
        exact tr.dropMove_grid_other ht i pt dst q hm hqd
    exact key _ rfl
  rcases hcor with hDA | ⟨hmem, hns⟩
  · -- The reply captures on `A`.
    subst hDA
    obtain ⟨R, hR, hRo, hatkR⟩ := hgd i (hglares hcol)
    rw [hD] at hR hatkR
    have hboard : ∃ (src : Pos) (promote : Bool), tr.moves i = .boardMove src D promote := by
      have key : ∀ mv : Move, tr.moves i = mv →
          ∃ (src : Pos) (promote : Bool), tr.moves i = .boardMove src D promote := by
        intro mv hm
        have hdst : mv.destination = D := by rw [← hm]; exact hD
        cases mv with
        | boardMove src dst promote =>
          change dst = D at hdst
          exact ⟨src, promote, by rw [hm, hdst]⟩
        | dropMove pt dst =>
          have h' := hde i pt dst hm
          change dst = D at hdst
          rw [hdst] at h'
          exact absurd h' hocc
      exact key _ rfl
    refine ⟨hboard, hocc, R, hR, ?_, hcol⟩
    have hRt : kp i.succ R.owner.opponent = kp i.succ (tr.before i).turn.opponent := by
      rw [hRo, Player.opponent_opponent]
    rw [hRt]
    exact hatkR
  · -- A reply strictly between `A` and `K` would check across `K` or `A`.
    exfalso
    rcases hatkP with hst | ⟨sd, hsd, hnorm, n, hn, hx, hy, hpc⟩
    · exact hns hst
    have hsdK := slide_mem_king _ _ sd hsd
    have hu := (PieceType.mem_king_stepDirs_iff sd).mp hsdK
    have hd0 : sd ≠ (0, 0) := fun h => hu.2.2.2.2 ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    obtain ⟨K, hKdef⟩ : ∃ K, K = kp 0 (tr.before i).turn := ⟨_, rfl⟩
    obtain ⟨L, hLdef⟩ : ∃ L, L = kp 0 (tr.before i).turn.opponent := ⟨_, rfl⟩
    rw [← hKdef] at hx hy hnorm hpc hmem
    have hKx : K.toInt.1 = A.toInt.1 + ↑n * sd.1 := by
      dsimp [Pos.dirTo, Pos.toInt] at hx ⊢
      omega
    have hKy : K.toInt.2 = A.toInt.2 + ↑n * sd.2 := by
      dsimp [Pos.dirTo, Pos.toInt] at hy ⊢
      omega
    have hiff := mem_slidePath_iff_of_exact_steps A K sd n hd0 hn hnorm hKx hKy
    obtain ⟨x, hx1, hxn, hDeq⟩ := (hiff D.toInt).mp hmem
    -- `L` lies on the line through `A` and `K`.
    have hcolKL : Geometry.collinear K.toInt L.toInt A.toInt := by
      rw [hKdef, hLdef]
      exact collinear_kings_of_sg (kp 0) _ A hcol
    obtain ⟨t, hLt⟩ := exists_line_param_of_collinear K L A sd (-(n : ℤ)) hsdK (by omega) (by
      ext
      · show A.toInt.1 = K.toInt.1 + -↑n * sd.1
        rw [hKx]; ring
      · show A.toInt.2 = K.toInt.2 + -↑n * sd.2
        rw [hKy]; ring) hcolKL
    have hLu : L.toInt = (A.toInt.1 + (↑n + t) * sd.1, A.toInt.2 + (↑n + t) * sd.2) := by
      rw [hLt]
      ext
      · show K.toInt.1 + t * sd.1 = A.toInt.1 + (↑n + t) * sd.1
        rw [hKx]; ring
      · show K.toInt.2 + t * sd.2 = A.toInt.2 + (↑n + t) * sd.2
        rw [hKy]; ring
    have hKn : K.toInt = (A.toInt.1 + ↑n * sd.1, A.toInt.2 + ↑n * sd.2) := Prod.ext hKx hKy
    have hA0 : A.toInt = (A.toInt.1 + 0 * sd.1, A.toInt.2 + 0 * sd.2) := by simp
    -- Remark 3.2 for `P`: its own king `L` is not on its path to `K`.
    have hLking : (tr.states i.castSucc).board.grid L =
        some ⟨(tr.before i).turn.opponent, .king⟩ := by
      rw [hLdef, ← hkp i.castSucc]
      exact (hk i.castSucc).king_present _
    have hLnot : L.toInt ∉ slidePath A K := by
      intro hLmem
      have h' := hpc L.toInt hLmem (Pos.onBoard_toInt L) (Pos.onBoard_toInt L)
      rw [Pos.toPos_toInt, hLking] at h'
      cases h'
    have ht0 : t ≠ 0 := by
      intro h'
      rw [h', zero_mul, zero_mul, add_zero, add_zero] at hLt
      have hLK : L = K := pos_eq_of_toInt hLt
      rw [hLdef, hKdef] at hLK
      exact Player.opponent_ne_self _ ((hk 0).positions_injective hLK)
    have hu0 : (n : ℤ) + t ≠ 0 := by
      intro h'
      rw [h', zero_mul, zero_mul, add_zero, add_zero] at hLu
      have hLA : L = A := pos_eq_of_toInt hLu
      rw [hLA, hP] at hLking
      cases hLking
      simp [PieceType.slideDirs] at hsd
    have hside : (n : ℤ) < n + t ∨ (n : ℤ) + t < 0 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨hlt, hge⟩ := hcon
      apply hLnot
      refine (hiff L.toInt).mpr ⟨(↑n + t).toNat, by omega, by omega, ?_⟩
      rw [hLu, Int.toNat_of_nonneg (by omega)]
    -- `D` is on the kings' line, so the reply checks `L` directly from `D`.
    have hcolD : Geometry.collinear (kp 0 .sente).toInt (kp 0 .gote).toInt D.toInt := by
      apply collinear_sg_of_kings (kp 0) (tr.before i).turn D
      rw [← hKdef, ← hLdef]
      exact collinear_of_line_params A K L D sd n (↑n + t) x hKn hLu hDeq
    obtain ⟨R, hR, _, hatkR⟩ := hgd i (hglares hcolD)
    rw [hD, hkp i.succ, ← hLdef] at hatkR
    -- `D` is not `A`.
    have hDA : D ≠ A := by
      intro h'
      rw [h'] at hDeq
      have e1 : (x : ℤ) * sd.1 = 0 := by
        have := congrArg Prod.fst hDeq
        simp only at this
        linarith
      have e2 : (x : ℤ) * sd.2 = 0 := by
        have := congrArg Prod.snd hDeq
        simp only at this
        linarith
      have hx0 : (x : ℤ) ≠ 0 := by omega
      exact hu.2.2.2.2 ⟨(mul_eq_zero.mp e1).resolve_left hx0, (mul_eq_zero.mp e2).resolve_left hx0⟩
    -- An occupied square strictly between `D` and `L`.
    obtain ⟨Z, z, hZ, hZocc, hzb⟩ : ∃ (Z : Pos) (z : ℤ),
        Z.toInt = (A.toInt.1 + z * sd.1, A.toInt.2 + z * sd.2) ∧
        (tr.states i.succ).board.grid Z ≠ none ∧
        (((x : ℤ) < z ∧ z < n + t) ∨ ((n : ℤ) + t < z ∧ z < x)) := by
      rcases hside with h' | h'
      · refine ⟨K, n, hKn, ?_, Or.inl ⟨by omega, h'⟩⟩
        rw [hKdef, ← hkp i.succ, (hk i.succ).king_present]
        exact Option.some_ne_none _
      · refine ⟨A, 0, hA0, ?_, Or.inr ⟨h', by omega⟩⟩
        rw [hkeep A (Ne.symm hDA) hocc (fun piece hp' => by
          rw [hPA] at hp'
          cases hp'
          rw [hPo]
          exact Player.opponent_ne_self _)]
        exact hocc
    have hZmem : Z.toInt ∈ slidePath D L :=
      mem_slidePath_of_between A D L Z sd x (↑n + t) z hsdK hDeq hLu hZ hzb
    rcases hatkR with hstR | ⟨sd', hsd', hnorm', m', hm', hx', hy', hpc'⟩
    · -- No step reaches two or more squares along the line.
      have e1 : (Pos.dirTo D L).1 = (↑n + t - ↑x) * sd.1 := by
        change L.toInt.1 - D.toInt.1 = _
        rw [hLu, hDeq]
        ring
      have e2 : (Pos.dirTo D L).2 = (↑n + t - ↑x) * sd.2 := by
        change L.toInt.2 - D.toInt.2 = _
        rw [hLu, hDeq]
        ring
      have hshape := stepDir_unit_or_knight _ _ _ hstR
      rw [e1, e2] at hshape
      rcases (show sd.1 = -1 ∨ sd.1 = 0 ∨ sd.1 = 1 by omega) with h1 | h1 | h1 <;>
        rcases (show sd.2 = -1 ∨ sd.2 = 0 ∨ sd.2 = 1 by omega) with h2 | h2 | h2 <;>
        rw [h1, h2] at hshape <;> omega
    · have h' := hpc' Z.toInt hZmem (Pos.onBoard_toInt Z) (Pos.onBoard_toInt Z)
      rw [Pos.toPos_toInt] at h'
      exact hZocc h'

/-- Once a checker stands on the kings' line at `A`, every later move captures on
    `A` and leaves a checker there. -/
private theorem checkerOnKingLine_forward (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (hde : tr.DropDestinationsEmpty) (A : Pos) (k : Fin (tr.len + 1))
    (h : tr.CheckerOnKingLine kp k A) :
    ∀ m : Fin (tr.len + 1), k ≤ m → tr.CheckerOnKingLine kp m A := by
  intro m
  induction m using Fin.induction with
  | zero =>
    intro hkm
    rw [Fin.le_zero_iff.mp hkm] at h
    exact h
  | succ i ih =>
    intro hkm
    by_cases he : k = i.succ
    · rw [← he]
      exact h
    · exact (tr.checkerOnKingLine_succ_of_periodic kp ht hs hk hsafe h0 hc hr hp hde i A
        (ih (Fin.le_castSucc_iff.mpr (lt_of_le_of_ne hkm he)))).2.2

/-- Proposition 3.6: in a periodic trace of at least one move satisfying 's
    premises and `DropDestinationsEmpty`, no checking piece stands on the line
    through both kings. Otherwise every move would capture, and the number of
    occupied squares could not return to its start. -/
theorem checker_off_kingLine_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (hde : tr.DropDestinationsEmpty) (hlen : 0 < tr.len)
    (k : Fin (tr.len + 1)) (A : Pos) : ¬ tr.CheckerOnKingLine kp k A := by
  intro h
  have hd := tr.boardMoveEndpointsDistinct_of_oriented hs hr
  have hperiod : tr.states (Fin.last tr.len) = tr.states 0 := hp
  -- The checker persists to the end of the period, hence from its start, hence always.
  obtain ⟨P, hP, hatk, hcol⟩ := tr.checkerOnKingLine_forward kp ht hs hk hsafe h0 hc hr hp hde A
    k h (Fin.last tr.len) (Fin.le_last k)
  have hstart : tr.CheckerOnKingLine kp 0 A := by
    refine ⟨P, by rw [← hperiod]; exact hP, ?_, hcol⟩
    rw [← hperiod, ← hp.kingPos_last hk]
    exact hatk
  have hall : ∀ m : Fin (tr.len + 1), tr.CheckerOnKingLine kp m A := fun m =>
    tr.checkerOnKingLine_forward kp ht hs hk hsafe h0 hc hr hp hde A 0 hstart m (Fin.zero_le m)
  -- Every move is a capture, so the occupied squares strictly decrease.
  have hcap : ∀ i : Fin tr.len,
      (tr.occupiedSquares i.succ).card < (tr.occupiedSquares i.castSucc).card := by
    intro i
    obtain ⟨⟨src, promote, hm⟩, hocc, _⟩ :=
      tr.checkerOnKingLine_succ_of_periodic kp ht hs hk hsafe h0 hc hr hp hde i A (hall _)
    exact tr.occupiedSquares_card_succ_lt_of_capture ht hs i src A promote hm
      (hd i src A promote hm) hocc
  have hcount : ∀ m : Fin (tr.len + 1),
      (tr.occupiedSquares m).card + m.val ≤ (tr.occupiedSquares 0).card := by
    intro m
    induction m using Fin.induction with
    | zero => simp
    | succ i ih =>
      have := hcap i
      simp only [Fin.val_succ, Fin.val_castSucc] at ih ⊢
      omega
  have hl := hcount (Fin.last tr.len)
  have heq : tr.occupiedSquares (Fin.last tr.len) = tr.occupiedSquares 0 := by
    ext q
    rw [tr.mem_occupiedSquares, tr.mem_occupiedSquares, hperiod]
  rw [heq, Fin.val_last] at hl
  omega

end MoveTrace
end MPC
