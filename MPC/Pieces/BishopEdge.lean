import MPC.Basic.Lemmas
import MPC.Pieces.BishopBasics
/-!
# MPC.Pieces.BishopEdge

Each side's bishop or horse moves along a single edge, and the candidate squares
for the mover's king. Throughout, the trace is a periodic
mutual-check trace with Proposition 4.1 and the piece counts, `o` is a side, `K`
its enemy king, `L` its own king, and coordinates are relative to `K`.

**Corollary 3.4 at a bishop move** (`bishopCheckerConstraint_of_checker`). Before
the move `o` is in check by an enemy piece `X`, which glares and so is not a bishop
or horse. The move lands on `X` or on `X`'s line to `L`. So `L` lies a
step from the destination, a forward knight's jump from it, or along a rank or file
from it with the enemy king not in between (`BishopCheckerConstraint`).

**One edge** (`bishop_moves_facing_of_periodic`). By  the move goes between
points at distance `t` on the rank and file through `K`. Proposition 3.5 keeps
both ends off the line through both kings, so `L` is on neither the rank nor the
file. Then the destination always faces `L`: it lies on the half-line toward `L`'s
side (`bishop_destination_facing`). With the indicator of the facing points as the
weight, no move lowers the potential, and 's lemma makes every move start on
a facing point too. So every move of `o`'s bishop goes between the two facing
points, and each such move has a reverse (`bishop_reverse_of_periodic`).

**The king's candidates** (`bishop_king_candidates`, `KingCandidate`). With both
moves the constraint leaves `L = (σt, ρt)` for the facing signs `σ`, `ρ`, or a few
squares when `t = 1` or `t = 2`. These are the paper's Table 1 candidates, together
with those whose bishop squares lie in front of `K` for `o`, which  excludes
(`bishop_configuration_of_periodic`). -/

namespace MPC

/-- Corollary 3.4's constraint on the mover's king `l` at a bishop move to `D`, when
    the checker's owner has forward sign `-τ` and is not a bishop or horse: a step,
    a forward knight's jump, or a rank or file line from `D` that does not pass the
    enemy king. -/
def BishopCheckerConstraint (τ : ℤ) (D l : ℤ × ℤ) : Prop :=
  ((l.1 - D.1, l.2 - D.2) : Dir) ∈ PieceType.king.stepDirs ∨
    ((l.1 = D.1 + 1 ∨ l.1 = D.1 - 1) ∧ l.2 = D.2 - 2 * τ) ∨
    (∃ sd : Dir, (sd = (1, 0) ∨ sd = (-1, 0) ∨ sd = (0, 1) ∨ sd = (0, -1)) ∧ ∃ c : ℤ, 1 ≤ c ∧
      l = (D.1 + c * sd.1, D.2 + c * sd.2) ∧
      ∀ c' : ℤ, 1 ≤ c' → c' < c → (D.1 + c' * sd.1, D.2 + c' * sd.2) ≠ (0, 0))

/-- The same constraint with the blocking condition used only at distance `t`. -/
def BishopCheckerConstraintAt (τ t : ℤ) (D l : ℤ × ℤ) : Prop :=
  ((l.1 - D.1, l.2 - D.2) : Dir) ∈ PieceType.king.stepDirs ∨
    ((l.1 = D.1 + 1 ∨ l.1 = D.1 - 1) ∧ l.2 = D.2 - 2 * τ) ∨
    (∃ sd : Dir, (sd = (1, 0) ∨ sd = (-1, 0) ∨ sd = (0, 1) ∨ sd = (0, -1)) ∧ ∃ c : ℤ, 1 ≤ c ∧
      l = (D.1 + c * sd.1, D.2 + c * sd.2) ∧
      (t < c → (D.1 + t * sd.1, D.2 + t * sd.2) ≠ (0, 0)))

theorem BishopCheckerConstraint.at {τ : ℤ} {D l : ℤ × ℤ} (h : BishopCheckerConstraint τ D l)
    (t : ℤ) (ht : 1 ≤ t) : BishopCheckerConstraintAt τ t D l := by
  rcases h with h | h | ⟨sd, hsd, c, hc, hl, hblk⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨sd, hsd, c, hc, hl, fun h => hblk t ht h⟩)

/-- Corollary 3.4 on the board for a checker that is not a bishop or horse, when the
    enemy king's square `K` is occupied before the move. -/
theorem bishopCheckerConstraint_of_checker (b : Board) (X : Piece) (C L D K : Pos)
    (hatk : attacksOriented b X.owner X.pieceType C L)
    (hD : D = C ∨ (D.toInt ∈ slidePath C L ∧
      Pos.dirTo C L ∉ X.pieceType.stepDirs.map (Dir.forPlayer · X.owner)))
    (hK : b.grid K ≠ none) (hX : ¬ (X.pieceType = .bishop ∨ X.pieceType = .horse)) :
    BishopCheckerConstraint (-forwardSign X.owner) (relTo K D) (relTo K L) := by
  rcases checker_cases b X C L D hatk hD with ⟨rfl, hst⟩ | ⟨d, n, c, hC, hc1, hcn, hDe, hsl,
      hempty⟩
  · have hl : (((relTo K L).1 - (relTo K D).1, (relTo K L).2 - (relTo K D).2) : Dir) =
        Pos.dirTo D L := by
      simp only [relTo, Pos.dirTo, Pos.toInt]
      ext <;> dsimp only <;> ring
    rcases stepDir_unit_or_forward_knight _ _ _ hst with hu | ⟨h1, h2⟩
    · left
      rw [hl]
      exact hu
    · right
      left
      have e1 := congrArg Prod.fst hl
      have e2 := congrArg Prod.snd hl
      dsimp only at e1 e2
      constructor
      · omega
      · omega
  · right
    right
    have hu := (PieceType.mem_king_stepDirs_iff d).mp hC.1
    have horth : d.1 = 0 ∨ d.2 = 0 := by
      by_contra h
      push Not at h
      exact hX (bishopHorse_of_slideDir _ _ _ hsl (by dsimp only; omega) (by dsimp only; omega))
    refine ⟨(-d.1, -d.2), orth_unit_cases (neg_mem_king_stepDirs hC.1) (by dsimp only; omega),
      c, hc1, ?_, ?_⟩
    · simp only [relTo, hDe]
      ext <;> dsimp only <;> ring
    · intro c' h1 h2 h
      apply hK
      apply hempty (c - c') (by omega) (by omega) K
      have e1 := congrArg Prod.fst h
      have e2 := congrArg Prod.snd h
      simp only [relTo, hDe] at e1 e2
      ext <;> dsimp only <;> linarith

/-- The line through both kings in relative coordinates: `q` is on it exactly when it
    is collinear with `K` and `L` in the cross-product sense. -/
theorem collinear_kings_iff (kp0 : Player → Pos) (o : Player) (q : Pos) :
    Geometry.collinear (kp0 .sente).toInt (kp0 .gote).toInt q.toInt ↔
      (relTo (kp0 o.opponent) (kp0 o)).1 * (relTo (kp0 o.opponent) q).2 =
        (relTo (kp0 o.opponent) (kp0 o)).2 * (relTo (kp0 o.opponent) q).1 := by
  unfold Geometry.collinear
  cases o <;> simp only [relTo, Player.opponent] <;> constructor <;> intro h <;> linarith

/-- The points facing the king `l`: on the rank through `K` on `l`'s side, or on the
    file through `K` on `l`'s side. -/
def Facing (l w : ℤ × ℤ) : Prop :=
  (w.2 = 0 ∧ ((0 < w.1 ∧ 0 < l.1) ∨ (w.1 < 0 ∧ l.1 < 0))) ∨
    (w.1 = 0 ∧ ((0 < w.2 ∧ 0 < l.2) ∨ (w.2 < 0 ∧ l.2 < 0)))

instance (l w : ℤ × ℤ) : Decidable (Facing l w) := by
  unfold Facing
  infer_instance

/-- Off both the rank and the file of `K`, a king far from `K` admits a bishop move to
    a point at distance `t` on that rank or file only if the point faces the king. -/
theorem bishop_destination_facing (τ t : ℤ) (hτ : τ = 1 ∨ τ = -1) (ht : 1 ≤ t)
    (w l : ℤ × ℤ) (hw : (w.2 = 0 ∧ (w.1 = t ∨ w.1 = -t)) ∨ (w.1 = 0 ∧ (w.2 = t ∨ w.2 = -t)))
    (hl1 : l.1 ≠ 0) (hl2 : l.2 ≠ 0) (hfar : ¬ (-1 ≤ l.1 ∧ l.1 ≤ 1 ∧ -1 ≤ l.2 ∧ l.2 ≤ 1))
    (h : BishopCheckerConstraintAt τ t w l) : Facing l w := by
  obtain ⟨w1, w2⟩ := w
  obtain ⟨l1, l2⟩ := l
  unfold Facing
  unfold BishopCheckerConstraintAt at h
  dsimp only at hw hl1 hl2 hfar h ⊢
  rcases hτ with rfl | rfl <;>
    rcases h with hu | hk | ⟨sd, hsd, c, hc, hl, hblk⟩ <;>
    (try rw [PieceType.mem_king_stepDirs_iff] at hu) <;>
    (try rcases hsd with rfl | rfl | rfl | rfl) <;>
    (try simp only [Prod.mk.injEq, ne_eq, mul_one, mul_zero, mul_neg, add_zero]
      at hl hblk) <;>
    (try dsimp only at hu) <;>
    omega

/-- The king's candidates for an edge between `(σt, 0)` and `(0, ρt)`: `(σt, ρt)`, and
    when `t = 1` or `t = 2` a few squares more. The ones with `ρ = τ`, where the edge's
    file point lies in front of `K` for the mover, are excluded later. -/
def KingCandidate (τ σ ρ t : ℤ) (l : ℤ × ℤ) : Prop :=
  l = (σ * t, ρ * t) ∨ (t = 1 ∧ (l = (σ, 2 * ρ) ∨ l = (2 * σ, ρ) ∨ (ρ = -τ ∧ l = (σ, 3 * ρ)))) ∨
    (t = 2 ∧ ρ = -τ ∧ (l = (σ, 2 * ρ) ∨ l = (3 * σ, 2 * ρ)))

set_option maxHeartbeats 4000000 in
/-- The king's position: if Corollary 3.4's constraint holds at both moves of the edge
    between `(σt, 0)` and `(0, ρt)`, which face the king, then the king is a candidate. -/
theorem bishop_king_candidates (τ σ ρ t : ℤ) (hτ : τ = 1 ∨ τ = -1) (hσ : σ = 1 ∨ σ = -1)
    (hρ : ρ = 1 ∨ ρ = -1) (ht : 1 ≤ t) (l : ℤ × ℤ)
    (hl1 : 0 < σ * l.1) (hl2 : 0 < ρ * l.2)
    (hfar : ¬ (-1 ≤ l.1 ∧ l.1 ≤ 1 ∧ -1 ≤ l.2 ∧ l.2 ≤ 1))
    (hA : BishopCheckerConstraintAt τ t (0, ρ * t) l)
    (hB : BishopCheckerConstraintAt τ t (σ * t, 0) l) : KingCandidate τ σ ρ t l := by
  obtain ⟨l1, l2⟩ := l
  unfold KingCandidate
  unfold BishopCheckerConstraintAt at hA hB
  dsimp only at hl1 hl2 hfar hA hB ⊢
  simp only [Prod.mk.injEq]
  rcases hτ with rfl | rfl <;> rcases hσ with rfl | rfl <;> rcases hρ with rfl | rfl <;>
    rcases hA with hu | hk | ⟨sd, hsd, c, hc, hl, hblk⟩ <;>
    rcases hB with hu' | hk' | ⟨sd', hsd', c', hc', hl', hblk'⟩ <;>
    (try rw [PieceType.mem_king_stepDirs_iff] at hu) <;>
    (try rw [PieceType.mem_king_stepDirs_iff] at hu') <;>
    (try dsimp only at hu) <;>
    (try dsimp only at hu') <;>
    (try rcases hsd with rfl | rfl | rfl | rfl) <;>
    (try rcases hsd' with rfl | rfl | rfl | rfl) <;>
    (try simp only [Prod.mk.injEq, ne_eq, mul_one, mul_zero, mul_neg, add_zero,
      one_mul, neg_mul, zero_add] at hl hblk) <;>
    (try simp only [Prod.mk.injEq, ne_eq, mul_one, mul_zero, mul_neg, add_zero,
      one_mul, neg_mul, zero_add] at hl' hblk') <;>
    omega

/-- Two moves along edges with a common end, both of whose other ends face the king,
    have the same other end. -/
theorem facing_edge_unique (t t' : ℤ) (v w u l : ℤ × ℤ) (h1 : BishopEdge t v w)
    (h2 : BishopEdge t' w u) (hv : Facing l v) (hu : Facing l u) : u = v := by
  obtain ⟨v1, v2⟩ := v
  obtain ⟨u1, u2⟩ := u
  unfold BishopEdge at h1 h2
  unfold Facing at hv hu
  dsimp only at h1 h2 hv hu
  simp only [Prod.mk.injEq]
  omega

/-- Proposition 3.5 for both ends of an edge puts the king off the rank and the file
    of `K`. -/
theorem king_off_axes_of_edge (t : ℤ) (v w l : ℤ × ℤ) (h : BishopEdge t v w)
    (hv : l.1 * v.2 ≠ l.2 * v.1) (hw : l.1 * w.2 ≠ l.2 * w.1) : l.1 ≠ 0 ∧ l.2 ≠ 0 := by
  obtain ⟨v1, v2⟩ := v
  obtain ⟨w1, w2⟩ := w
  unfold BishopEdge at h
  dsimp only at h hv hw
  rcases h with ⟨_, ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩⟩
  · subst h1
    subst h3
    constructor
    · intro hl
      apply hw
      rw [hl]
      ring
    · intro hl
      apply hv
      rw [hl]
      ring
  · subst h1
    subst h3
    constructor
    · intro hl
      apply hv
      rw [hl]
      ring
    · intro hl
      apply hw
      rw [hl]
      ring

/-- The two ends of an edge whose ends face the king, named by the facing signs. -/
theorem facing_edge_signs (t : ℤ) (v w l : ℤ × ℤ) (h : BishopEdge t v w) (hv : Facing l v)
    (hw : Facing l w) :
    ∃ σ ρ : ℤ, (σ = 1 ∨ σ = -1) ∧ (ρ = 1 ∨ ρ = -1) ∧ 0 < σ * l.1 ∧ 0 < ρ * l.2 ∧
      ((v = (σ * t, 0) ∧ w = (0, ρ * t)) ∨ (v = (0, ρ * t) ∧ w = (σ * t, 0))) := by
  obtain ⟨v1, v2⟩ := v
  obtain ⟨w1, w2⟩ := w
  obtain ⟨l1, l2⟩ := l
  unfold BishopEdge at h
  unfold Facing at hv hw
  dsimp only at h hv hw ⊢
  simp only [Prod.mk.injEq]
  rcases lt_trichotomy l1 0 with h1 | h1 | h1 <;> rcases lt_trichotomy l2 0 with h2 | h2 | h2
  all_goals first
    | exact ⟨-1, -1, Or.inr rfl, Or.inr rfl, by omega, by omega, by omega⟩
    | exact ⟨-1, 1, Or.inr rfl, Or.inl rfl, by omega, by omega, by omega⟩
    | exact ⟨1, -1, Or.inl rfl, Or.inr rfl, by omega, by omega, by omega⟩
    | exact ⟨1, 1, Or.inl rfl, Or.inl rfl, by omega, by omega, by omega⟩

/-- An edge whose ends face the king meets the facing edge at distance `t` in both ends
    or in neither. -/
theorem facing_edge_mem_iff (t t' σ ρ : ℤ) (v w l : ℤ × ℤ) (hσ : σ = 1 ∨ σ = -1)
    (hρ : ρ = 1 ∨ ρ = -1) (hl1 : 0 < σ * l.1) (hl2 : 0 < ρ * l.2) (h : BishopEdge t' v w)
    (hv : Facing l v) (hw : Facing l w) :
    (v = (σ * t, 0) ∨ v = (0, ρ * t)) ↔ (w = (σ * t, 0) ∨ w = (0, ρ * t)) := by
  obtain ⟨v1, v2⟩ := v
  obtain ⟨w1, w2⟩ := w
  obtain ⟨l1, l2⟩ := l
  unfold BishopEdge at h
  unfold Facing at hv hw
  dsimp only at h hv hw hl1 hl2
  simp only [Prod.mk.injEq]
  rcases hσ with rfl | rfl <;> rcases hρ with rfl | rfl <;> omega

namespace MoveTrace

/-- Under the premises of the main theorem, the data of a non-glaring move of a bishop
    or horse of `o` relative to `K`: the edge, Proposition 3.5 for both ends, and
    Corollary 3.4's constraint on `o`'s king. -/
theorem bishop_move_data_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hm : tr.MutualPerpetualCheck kp)
    (h41 : tr.DiscoveredCheckByEachSide kp) (hcount : tr.PieceCountsAtMostTwo)
    (i : Fin tr.len) (src dst : Pos) (promote : Bool) (p : Piece)
    (hmv : tr.moves i = .boardMove src dst promote)
    (hpc : (tr.before i).board.grid src = some p)
    (hng : ¬ tr.GlaresAtEnemyKing kp i.castSucc src) :
    ∃ t : ℤ, BishopEdge t (relTo (kp 0 p.owner.opponent) src) (relTo (kp 0 p.owner.opponent) dst) ∧
      (relTo (kp 0 p.owner.opponent) (kp 0 p.owner)).1 * (relTo (kp 0 p.owner.opponent) src).2 ≠
        (relTo (kp 0 p.owner.opponent) (kp 0 p.owner)).2 * (relTo (kp 0 p.owner.opponent) src).1 ∧
      (relTo (kp 0 p.owner.opponent) (kp 0 p.owner)).1 * (relTo (kp 0 p.owner.opponent) dst).2 ≠
        (relTo (kp 0 p.owner.opponent) (kp 0 p.owner)).2 * (relTo (kp 0 p.owner.opponent) dst).1 ∧
      BishopCheckerConstraint (forwardSign p.owner) (relTo (kp 0 p.owner.opponent) dst)
        (relTo (kp 0 p.owner.opponent) (kp 0 p.owner)) := by
  have hm' := hm
  obtain ⟨ht, hs, hk, hsafe, h0, hc, hr, hp, _, _⟩ := hm
  have hkp := tr.kingPos_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp
  have hown : p.owner = (tr.before i).turn := by
    obtain ⟨piece, hpiece, ho⟩ := hs i src dst promote hmv
    rw [hpc] at hpiece
    cases hpiece
    exact ho
  obtain ⟨t, hedge⟩ :=
    tr.bishopEdge_of_nonGlaring_move_of_periodic kp hm' h41 hcount i src dst promote p hmv hpc hng
  -- Proposition 3.5 for the destination, and for the source through its arrival.
  have hngd : ¬ tr.GlaresAtEnemyKing kp i.succ (tr.moves i).destination := by
    rw [hmv]
    exact fun hg => hng (tr.glares_source_of_glares_destination_of_periodic kp ht hs hk hsafe h0
      hc hr hp i src dst promote hmv hg)
  have hoffd := tr.openable_destination_off_kingLine_of_periodic kp ht hs hk hsafe h0 hc hr hp i
    hngd
  rw [hmv] at hoffd
  obtain ⟨i', src', pr, hmi', hpi', hngi'⟩ :=
    tr.arrival_of_nonGlaring_move_of_periodic kp ht hs hk hsafe h0 hc hr hp i src dst promote p
      hmv hpc hng
  have hngs : ¬ tr.GlaresAtEnemyKing kp i'.succ (tr.moves i').destination := by
    rw [hmi']
    exact fun hg => hngi' (tr.glares_source_of_glares_destination_of_periodic kp ht hs hk hsafe
      h0 hc hr hp i' src' src pr hmi' hg)
  have hoffs := tr.openable_destination_off_kingLine_of_periodic kp ht hs hk hsafe h0 hc hr hp i'
    hngs
  rw [hmi'] at hoffs
  rw [collinear_kings_iff (kp 0) p.owner] at hoffd hoffs
  -- Corollary 3.4: the checker is not a bishop or horse, because it glares.
  obtain ⟨C, X, hX, hXo, hatk, hD⟩ := tr.checker_before_of_periodic kp ht hs hk hsafe h0 hc hr hp i
  rw [hmv, ← hown] at hD
  rw [← hown] at hatk hXo
  have hXg : tr.GlaresAtEnemyKing kp i.castSucc C :=
    tr.glaresAtEnemyKing_of_attacks kp i.castSucc C X hX
      (by
        rw [hkp i.castSucc, show kp 0 X.owner.opponent = kp 0 p.owner by
          rw [hXo, Player.opponent_opponent]]
        exact hatk)
  have hXbh : ¬ (X.pieceType = .bishop ∨ X.pieceType = .horse) := fun hb =>
    tr.not_glares_bishopHorse_of_periodic kp hm' h41 hcount i.castSucc C X hX hb hXg
  have hKocc : (tr.before i).board.grid (kp 0 p.owner.opponent) ≠ none := by
    change (tr.states i.castSucc).board.grid _ ≠ none
    rw [← hkp i.castSucc, (hk i.castSucc).king_present]
    exact Option.some_ne_none _
  have hcon := bishopCheckerConstraint_of_checker _ X C _ dst _ hatk hD hKocc hXbh
  rw [hXo, forwardSign_opponent, neg_neg] at hcon
  exact ⟨t, hedge, hoffs, hoffd, hcon⟩

/-- Under the same premises, every non-glaring move of a bishop or horse of `o` goes
    between two points facing `o`'s king: the facing indicator is a potential that no
    move lowers. -/
theorem bishop_moves_facing_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hm : tr.MutualPerpetualCheck kp)
    (h41 : tr.DiscoveredCheckByEachSide kp) (hcount : tr.PieceCountsAtMostTwo) (o : Player)
    (i : Fin tr.len) (src dst : Pos) (promote : Bool) (p : Piece)
    (hmv : tr.moves i = .boardMove src dst promote)
    (hpc : (tr.before i).board.grid src = some p) (hpo : p.owner = o)
    (hng : ¬ tr.GlaresAtEnemyKing kp i.castSucc src) :
    ∃ t : ℤ, BishopEdge t (relTo (kp 0 o.opponent) src) (relTo (kp 0 o.opponent) dst) ∧
      Facing (relTo (kp 0 o.opponent) (kp 0 o)) (relTo (kp 0 o.opponent) src) ∧
      Facing (relTo (kp 0 o.opponent) (kp 0 o)) (relTo (kp 0 o.opponent) dst) := by
  have hm' := hm
  obtain ⟨ht, hs, hk, hsafe, h0, hc, hr, hp, _, _⟩ := hm
  obtain ⟨K, hKdef⟩ : ∃ K, K = kp 0 o.opponent := ⟨_, rfl⟩
  obtain ⟨L, hLdef⟩ : ∃ L, L = kp 0 o := ⟨_, rfl⟩
  rw [← hKdef, ← hLdef]
  have hfar : ¬ (-1 ≤ (relTo K L).1 ∧ (relTo K L).1 ≤ 1 ∧ -1 ≤ (relTo K L).2 ∧
      (relTo K L).2 ≤ 1) := by
    rintro ⟨h1, h2, h3, h4⟩
    have hLK : L ≠ K := by
      intro h
      have hL := (hk 0).king_present o
      have hK := (hk 0).king_present o.opponent
      rw [← hKdef, ← h, hLdef, hL] at hK
      cases o <;> cases hK
    have hne : ¬ ((relTo K L).1 = 0 ∧ (relTo K L).2 = 0) := by
      rintro ⟨e1, e2⟩
      apply hLK
      apply relTo_inj
      rw [show relTo K K = (0, 0) by simp [relTo]]
      exact Prod.ext e1 e2
    have hstep : Pos.dirTo L K ∈ PieceType.king.stepDirs := by
      rw [PieceType.mem_king_stepDirs_iff]
      have e1 : (Pos.dirTo L K).1 = -(relTo K L).1 := by
        simp only [Pos.dirTo, relTo, Pos.toInt]
        ring
      have e2 : (Pos.dirTo L K).2 = -(relTo K L).2 := by
        simp only [Pos.dirTo, relTo, Pos.toInt]
        ring
      rw [e1, e2]
      omega
    have hmap : ∀ d ∈ PieceType.king.stepDirs,
        d ∈ PieceType.king.stepDirs.map (Dir.forPlayer · o) := by
      cases o <;> decide
    apply tr.kings_not_adjacent kp hk hsafe h0 0 o
    rw [← hLdef, ← hKdef]
    exact Or.inl (hmap _ hstep)
  -- Every move ends on a facing point.
  have hτ : forwardSign o = 1 ∨ forwardSign o = -1 := forwardSign_cases o
  have hdata : ∀ (j : Fin tr.len) (s d : Pos) (pr : Bool) (x : Piece),
      tr.moves j = .boardMove s d pr → (tr.before j).board.grid s = some x → x.owner = o →
      ¬ tr.GlaresAtEnemyKing kp j.castSucc s →
      ∃ t : ℤ, BishopEdge t (relTo K s) (relTo K d) ∧ Facing (relTo K L) (relTo K d) := by
    intro j s d pr x hmj hxj hxo hngj
    obtain ⟨t, hedge, hoffs, hoffd, hcon⟩ :=
      tr.bishop_move_data_of_periodic kp hm' h41 hcount j s d pr x hmj hxj hngj
    rw [hxo, ← hKdef] at hedge
    rw [hxo, ← hKdef, ← hLdef] at hoffs hoffd hcon
    obtain ⟨hl1, hl2⟩ := king_off_axes_of_edge t _ _ _ hedge hoffs hoffd
    refine ⟨t, hedge, bishop_destination_facing _ t hτ hedge.1 _ _ ?_ hl1 hl2 hfar
      (hcon.at t hedge.1)⟩
    obtain ⟨_, h | h⟩ := hedge
    · exact Or.inr ⟨h.2.2.1, h.2.2.2⟩
    · exact Or.inl ⟨h.2.2.1, h.2.2.2⟩
  -- The facing indicator as a potential.
  let P : Piece → Prop := fun x => x.owner = o
  let f : Pos → ℕ := fun q => if Facing (relTo K L) (relTo K q) then 1 else 0
  have hf : ∀ j s d, tr.NonGlaringMoveOf kp P j s d → f s ≤ f d := by
    rintro j s d ⟨pr, x, hmj, hxj, hngj, hxo⟩
    obtain ⟨_, _, hfd⟩ := hdata j s d pr x hmj hxj hxo hngj
    simp only [f, ite_eq_left hfd]
    split_ifs <;> omega
  have heq := tr.potential_move_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp P f hf i src dst
    ⟨promote, p, hmv, hpc, hng, hpo⟩
  obtain ⟨t, hedge, hfd⟩ := hdata i src dst promote p hmv hpc hpo hng
  refine ⟨t, hedge, ?_, hfd⟩
  by_contra hfs
  simp only [f, ite_eq_left hfd, ite_eq_right hfs] at heq
  omega

/-- Under the same premises, every non-glaring move of a bishop or horse of `o` has a
    reverse move of the same piece. -/
theorem bishop_reverse_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hm : tr.MutualPerpetualCheck kp)
    (h41 : tr.DiscoveredCheckByEachSide kp) (hcount : tr.PieceCountsAtMostTwo) (o : Player)
    (i : Fin tr.len) (src dst : Pos) (promote : Bool) (p : Piece)
    (hmv : tr.moves i = .boardMove src dst promote)
    (hpc : (tr.before i).board.grid src = some p) (hpo : p.owner = o)
    (hng : ¬ tr.GlaresAtEnemyKing kp i.castSucc src) :
    ∃ (j : Fin tr.len) (pr : Bool), tr.moves j = .boardMove dst src pr ∧
      (tr.before j).board.grid dst = some p ∧ ¬ tr.GlaresAtEnemyKing kp j.castSucc dst := by
  have hm' := hm
  obtain ⟨ht, hs, hk, hsafe, h0, hc, hr, hp, _, _⟩ := hm
  obtain ⟨t, hedge, hfs, _⟩ :=
    tr.bishop_moves_facing_of_periodic kp hm' h41 hcount o i src dst promote p hmv hpc hpo hng
  obtain ⟨j, d', pr, hmj, hpj, hngj⟩ :=
    tr.departure_of_nonGlaring_move_of_periodic kp ht hs hk hsafe h0 hc hr hp i src dst promote p
      hmv hpc hng
  obtain ⟨t', hedge', _, hfd'⟩ :=
    tr.bishop_moves_facing_of_periodic kp hm' h41 hcount o j dst d' pr p hmj hpj hpo hngj
  have hd' : d' = src := relTo_inj (facing_edge_unique t t' _ _ _ _ hedge hedge' hfs hfd')
  subst hd'
  exact ⟨j, pr, hmj, hpj, hngj⟩

/-- Under the premises of the main theorem, the kings are not adjacent, in relative
    coordinates. -/
theorem relTo_king_far_of_periodic (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (hm : tr.MutualPerpetualCheck kp) (o : Player) :
    ¬ (-1 ≤ (relTo (kp 0 o.opponent) (kp 0 o)).1 ∧ (relTo (kp 0 o.opponent) (kp 0 o)).1 ≤ 1 ∧
      -1 ≤ (relTo (kp 0 o.opponent) (kp 0 o)).2 ∧ (relTo (kp 0 o.opponent) (kp 0 o)).2 ≤ 1) := by
  obtain ⟨_, _, hk, hsafe, h0, _, _, _, _, _⟩ := hm
  obtain ⟨K, hKdef⟩ : ∃ K, K = kp 0 o.opponent := ⟨_, rfl⟩
  obtain ⟨L, hLdef⟩ : ∃ L, L = kp 0 o := ⟨_, rfl⟩
  rw [← hKdef, ← hLdef]
  rintro ⟨h1, h2, h3, h4⟩
  have hLK : L ≠ K := by
    intro h
    have hL := (hk 0).king_present o
    have hK := (hk 0).king_present o.opponent
    rw [← hKdef, ← h, hLdef, hL] at hK
    cases o <;> cases hK
  have hne : ¬ ((relTo K L).1 = 0 ∧ (relTo K L).2 = 0) := by
    rintro ⟨e1, e2⟩
    apply hLK
    apply relTo_inj
    rw [show relTo K K = (0, 0) by simp [relTo]]
    exact Prod.ext e1 e2
  have hstep : Pos.dirTo L K ∈ PieceType.king.stepDirs := by
    rw [PieceType.mem_king_stepDirs_iff]
    have e1 : (Pos.dirTo L K).1 = -(relTo K L).1 := by
      simp only [Pos.dirTo, relTo, Pos.toInt]
      ring
    have e2 : (Pos.dirTo L K).2 = -(relTo K L).2 := by
      simp only [Pos.dirTo, relTo, Pos.toInt]
      ring
    rw [e1, e2]
    omega
  have hmap : ∀ d ∈ PieceType.king.stepDirs,
      d ∈ PieceType.king.stepDirs.map (Dir.forPlayer · o) := by
    cases o <;> decide
  apply tr.kings_not_adjacent kp hk hsafe h0 0 o
  rw [← hLdef, ← hKdef]
  exact Or.inl (hmap _ hstep)

/-- Under the premises of the main theorem, a side has at most one bishop-or-horse
    square in each state. -/
theorem bishopHorse_square_unique_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hm : tr.MutualPerpetualCheck kp)
    (h41 : tr.DiscoveredCheckByEachSide kp) (hcount : tr.PieceCountsAtMostTwo)
    (k : Fin (tr.len + 1)) (q q' : Pos) (P P' : Piece) (hq : (tr.states k).board.grid q = some P)
    (hq' : (tr.states k).board.grid q' = some P') (hPo : P'.owner = P.owner)
    (hPt : P.pieceType = .bishop ∨ P.pieceType = .horse)
    (hPt' : P'.pieceType = .bishop ∨ P'.pieceType = .horse) : q = q' := by
  by_contra hne
  obtain ⟨r, R, hr, hRo, hRt, _⟩ :=
    tr.exists_openable_bishopHorse_of_periodic kp hm h41 hcount k P.owner.opponent
  have hqr : q ≠ r := by
    rintro rfl
    rw [hq] at hr
    cases hr
    generalize P.owner = x at hRo
    cases x <;> cases hRo
  have hq'r : q' ≠ r := by
    rintro rfl
    rw [hq'] at hr
    cases hr
    rw [hPo] at hRo
    generalize P.owner = x at hRo
    cases x <;> cases hRo
  exact tr.false_of_three_bishopHorse hcount k q q' r hne hqr hq'r
    (tr.mem_bishopHorseSquares_of _ _ P hq hPt) (tr.mem_bishopHorseSquares_of _ _ P' hq' hPt')
    (tr.mem_bishopHorseSquares_of _ _ R hr hRt)

/-- The configuration of a side's bishop or horse: it always stands on one of two
    squares `a = (σt, 0)` and `b = (0, ρt)` facing the side's king, it moves both ways
    between them, and the king is a candidate for this edge. -/
theorem bishop_configuration_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hm : tr.MutualPerpetualCheck kp)
    (h41 : tr.DiscoveredCheckByEachSide kp) (hcount : tr.PieceCountsAtMostTwo) (o : Player) :
    ∃ (t σ ρ : ℤ) (a b : Pos), 1 ≤ t ∧ (σ = 1 ∨ σ = -1) ∧ (ρ = 1 ∨ ρ = -1) ∧
      relTo (kp 0 o.opponent) a = (σ * t, 0) ∧ relTo (kp 0 o.opponent) b = (0, ρ * t) ∧
      0 < σ * (relTo (kp 0 o.opponent) (kp 0 o)).1 ∧
      0 < ρ * (relTo (kp 0 o.opponent) (kp 0 o)).2 ∧
      KingCandidate (forwardSign o) σ ρ t (relTo (kp 0 o.opponent) (kp 0 o)) ∧
      (∃ (i : Fin tr.len) (pr : Bool) (P : Piece), tr.moves i = .boardMove a b pr ∧
        (tr.before i).board.grid a = some P ∧ P.owner = o ∧
        ¬ tr.GlaresAtEnemyKing kp i.castSucc a) ∧
      (∃ (i : Fin tr.len) (pr : Bool) (P : Piece), tr.moves i = .boardMove b a pr ∧
        (tr.before i).board.grid b = some P ∧ P.owner = o ∧
        ¬ tr.GlaresAtEnemyKing kp i.castSucc b) ∧
      (∀ (k : Fin (tr.len + 1)) (q : Pos) (P : Piece), (tr.states k).board.grid q = some P →
        P.owner = o → (P.pieceType = .bishop ∨ P.pieceType = .horse) → q = a ∨ q = b) := by
  have hm' := hm
  obtain ⟨ht, hs, hk, hsafe, h0, hc, hr, hp, _, _⟩ := hm
  obtain ⟨K, hKdef⟩ : ∃ K, K = kp 0 o.opponent := ⟨_, rfl⟩
  obtain ⟨L, hLdef⟩ : ∃ L, L = kp 0 o := ⟨_, rfl⟩
  rw [← hKdef, ← hLdef]
  have hfar := tr.relTo_king_far_of_periodic kp hm' o
  rw [← hKdef, ← hLdef] at hfar
  have hτ := forwardSign_cases o
  -- A move of `o`'s bishop or horse, from Proposition 4.1.
  obtain ⟨pt, hopen⟩ := tr.exists_openableMove kp hm' h41 o
  have hpt := tr.bishopHorse_of_openableMove kp hm' h41 hcount o pt hopen
  obtain ⟨i, src, dst, promote, _, hmv, hsrc, hng, _⟩ := hopen
  obtain ⟨t, hedge, hfs, hfd⟩ :=
    tr.bishop_moves_facing_of_periodic kp hm' h41 hcount o i src dst promote ⟨o, pt⟩ hmv hsrc rfl
      hng
  rw [← hKdef] at hedge
  rw [← hKdef, ← hLdef] at hfs hfd
  obtain ⟨σ, ρ, hσ, hρ, hl1, hl2, hsd⟩ := facing_edge_signs t _ _ _ hedge hfs hfd
  obtain ⟨j, pr, hmj, hpj, hngj⟩ :=
    tr.bishop_reverse_of_periodic kp hm' h41 hcount o i src dst promote ⟨o, pt⟩ hmv hsrc rfl hng
  -- Name the squares and the two moves.
  obtain ⟨a, b, hra, hrb, hab, hba⟩ : ∃ a b : Pos, relTo K a = (σ * t, 0) ∧
      relTo K b = (0, ρ * t) ∧
      (∃ (i : Fin tr.len) (pr : Bool) (P : Piece), tr.moves i = .boardMove a b pr ∧
        (tr.before i).board.grid a = some P ∧ P.owner = o ∧
        ¬ tr.GlaresAtEnemyKing kp i.castSucc a) ∧
      (∃ (i : Fin tr.len) (pr : Bool) (P : Piece), tr.moves i = .boardMove b a pr ∧
        (tr.before i).board.grid b = some P ∧ P.owner = o ∧
        ¬ tr.GlaresAtEnemyKing kp i.castSucc b) := by
    rcases hsd with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨src, dst, h1, h2, ⟨i, promote, _, hmv, hsrc, rfl, hng⟩,
        ⟨j, pr, _, hmj, hpj, rfl, hngj⟩⟩
    · exact ⟨dst, src, h2, h1, ⟨j, pr, _, hmj, hpj, rfl, hngj⟩,
        ⟨i, promote, _, hmv, hsrc, rfl, hng⟩⟩
  have ht1 : 1 ≤ t := hedge.1
  -- The king is a candidate: Corollary 3.4 at both moves.
  have hcand : KingCandidate (forwardSign o) σ ρ t (relTo K L) := by
    obtain ⟨i1, pr1, P1, hm1, hP1, hP1o, hng1⟩ := hab
    obtain ⟨i2, pr2, P2, hm2, hP2, hP2o, hng2⟩ := hba
    obtain ⟨_, _, _, _, hconA⟩ :=
      tr.bishop_move_data_of_periodic kp hm' h41 hcount i1 a b pr1 P1 hm1 hP1 hng1
    obtain ⟨_, _, _, _, hconB⟩ :=
      tr.bishop_move_data_of_periodic kp hm' h41 hcount i2 b a pr2 P2 hm2 hP2 hng2
    rw [hP1o, ← hKdef, ← hLdef, hrb] at hconA
    rw [hP2o, ← hKdef, ← hLdef, hra] at hconB
    exact bishop_king_candidates _ σ ρ t hτ hσ hρ ht1 _ hl1 hl2 hfar (hconA.at t ht1)
      (hconB.at t ht1)
  refine ⟨t, σ, ρ, a, b, ht1, hσ, hρ, hra, hrb, hl1, hl2, hcand, hab, hba, ?_⟩
  -- `o`'s bishop or horse stays on `a` or `b`: the count there never changes.
  let P : Piece → Prop := fun x => x.owner = o ∧ (x.pieceType = .bishop ∨ x.pieceType = .horse)
  let f : Pos → ℕ := fun q => if q = a ∨ q = b then 1 else 0
  have hmemab : ∀ q : Pos, (q = a ∨ q = b) ↔ (relTo K q = (σ * t, 0) ∨ relTo K q = (0, ρ * t)) := by
    intro q
    constructor
    · rintro (rfl | rfl)
      · exact Or.inl hra
      · exact Or.inr hrb
    · rintro (h | h)
      · exact Or.inl (relTo_inj (h.trans hra.symm))
      · exact Or.inr (relTo_inj (h.trans hrb.symm))
  have hkeep : ∀ j s d, tr.NonGlaringMoveOf kp P j s d → f s = f d := by
    rintro j s d ⟨pr, x, hmj, hxj, hngj, hxo, _⟩
    obtain ⟨t', hedge', hfs', hfd'⟩ :=
      tr.bishop_moves_facing_of_periodic kp hm' h41 hcount o j s d pr x hmj hxj hxo hngj
    rw [← hKdef] at hedge'
    rw [← hKdef, ← hLdef] at hfs' hfd'
    have hiff := facing_edge_mem_iff t t' σ ρ _ _ _ hσ hρ hl1 hl2 hedge' hfs' hfd'
    rw [← hmemab, ← hmemab] at hiff
    simp only [f]
    by_cases hsab : s = a ∨ s = b
    · rw [ite_eq_left hsab, ite_eq_left (hiff.mp hsab)]
    · rw [ite_eq_right hsab, ite_eq_right (fun h => hsab (hiff.mpr h))]
  have hstep : ∀ jj : Fin tr.len,
      tr.potential kp P f jj.succ = tr.potential kp P f jj.castSucc := by
    intro jj
    by_cases hj : ∃ s d, tr.NonGlaringMoveOf kp P jj s d
    · obtain ⟨s, d, hjm⟩ := hj
      have h := tr.potential_succ_add_of_move kp ht hs hk hsafe h0 hc hr hp P f jj s d hjm
      have := hkeep jj s d hjm
      omega
    · push Not at hj
      exact tr.potential_succ_of_not_move kp ht hs hk hsafe h0 hc hr hp P f jj hj
  have hconst : ∀ k, tr.potential kp P f k = tr.potential kp P f 0 := by
    intro k
    induction k using Fin.induction with
    | zero => rfl
    | succ jj ih => rw [hstep jj, ih]
  -- Before the first move the bishop or horse is on `a`.
  obtain ⟨i1, pr1, P1, hm1, hP1, hP1o, hng1⟩ := hab
  have hP1t := tr.bishopHorse_of_nonGlaring_move kp hm' h41 hcount i1 a b pr1 P1 hm1 hP1 hng1
  have hpos : 1 ≤ tr.potential kp P f i1.castSucc := by
    have hmem : a ∈ tr.nonGlaringSquaresOf kp P i1.castSucc :=
      (tr.mem_nonGlaringSquaresOf kp P _ _).mpr ⟨⟨P1, hP1, hP1o, hP1t⟩, hng1⟩
    unfold potential
    rw [← Finset.add_sum_erase _ f hmem]
    have : f a = 1 := by simp [f]
    omega
  intro k q Q hQ hQo hQt
  have hposk : (tr.nonGlaringSquaresOf kp P k).sum f ≠ 0 := by
    have := hconst k
    have := hconst i1.castSucc
    unfold potential at *
    omega
  obtain ⟨q', hq'mem, hq'f⟩ := Finset.exists_ne_zero_of_sum_ne_zero hposk
  obtain ⟨⟨Q', hQ', hQ'o, hQ't⟩, _⟩ := (tr.mem_nonGlaringSquaresOf kp P _ _).mp hq'mem
  have hq'ab : q' = a ∨ q' = b := by
    by_contra h
    simp only [ite_eq_right h] at hq'f
    exact hq'f rfl
  have hqq' := tr.bishopHorse_square_unique_of_periodic kp hm' h41 hcount k q q' Q Q' hQ hQ'
    (hQ'o.trans hQo.symm) hQt hQ't
  rw [hqq']
  exact hq'ab

end MoveTrace
end MPC
