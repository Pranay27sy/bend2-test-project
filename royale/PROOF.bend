# The proofs of LAWS.bend: `bend PROOF.bend` is the whole verification.
#
# dead_stay_dead: apply returns a 0-health fighter untouched, so each
# step of run is the identity. hp_capped: hits and storm only subtract,
# heals go through cap, and nothing else touches health. fire_spends_ammo
# and zone_never_grows are case analysis and Nat.sub never growing.

import Base
import ./royale.bend as R
import ./LAWS.bend as Laws

# Order
# -----

def le_refl(n: Nat) -> R.LE(n, n):
  match n:
    case 0n:
      Unit{}
    case 1n+p:
      le_refl(p)

def le_succ(a: Nat, b: Nat, e: R.LE(a, b)) -> R.LE(a, 1n+b):
  match a b:
    case 0n _:
      Unit{}
    case 1n+a1 0n:
      Empty.absurd(R.LE(1n+a1, 1n), e)
    case 1n+a1 1n+b1:
      le_succ(a1, b1, e)

def le_trans(a: Nat, b: Nat, c: Nat, e1: R.LE(a, b), e2: R.LE(b, c)) -> R.LE(a, c):
  match a b c:
    case 0n _ _:
      Unit{}
    case 1n+a1 0n _:
      Empty.absurd(R.LE(1n+a1, c), e1)
    case 1n+a1 1n+b1 0n:
      Empty.absurd(R.LE(1n+a1, 0n), e2)
    case 1n+a1 1n+b1 1n+c1:
      le_trans(a1, b1, c1, e1, e2)

# subtracting never makes a number bigger
def sub_le(a: Nat, b: Nat) -> R.LE(Nat.sub(a, b), a):
  match a b:
    case 0n _:
      Unit{}
    case 1n+p 0n:
      le_refl(p)
    case 1n++p 1n++q:
      le_succ(Nat.sub(p, q), p, sub_le(p, q))

# Fighters
# --------

def Laws.dead_stay_dead(acts, ammo, kills):
  match acts:
    case Nil{}:
      {==}
    case act <> rest:
      Laws.dead_stay_dead(rest, ammo, kills)

def cap_go_le(+n: Nat, c: Or(R.LE(n, R.max_hp()), R.LE(R.max_hp(), n)))
  -> R.LE(R.cap.go(n, c), R.max_hp()):
  match c:
    case Inl{e}:
      e
    case Inr{e}:
      le_refl(R.max_hp())

def live_capped(+h: Nat, +a: Nat, +k: Nat, act: R.Act, ok: R.LE(h, R.max_hp()))
  -> R.LE(R.hp(R.live(h, a, k, act)), R.max_hp()):
  match act:
    case R.Hit{+d}:
      le_trans(Nat.sub(h, d), h, R.max_hp(), sub_le(h, d), ok)
    case R.Storm{+d}:
      le_trans(Nat.sub(h, d), h, R.max_hp(), sub_le(h, d), ok)
    case R.Heal{+n}:
      cap_go_le(Nat.add(h, n), R.le_case(Nat.add(h, n), R.max_hp()))
    case R.Loot{n}:
      ok
    case R.Fire{}:
      ok
    case R.Kill{}:
      ok

def apply_capped(+f: R.Fighter, act: R.Act, ok: R.LE(R.hp(f), R.max_hp()))
  -> R.LE(R.hp(R.apply(f, act)), R.max_hp()):
  match f:
    case R.Fighter{h, +a, +k}:
      match h:
        case 0n:
          Unit{}
        case 1n++p:
          live_capped(1n+p, a, k, act, ok)

def Laws.hp_capped(acts, f, ok):
  match acts:
    case Nil{}:
      ok
    case +act <> rest:
      Laws.hp_capped(rest, R.apply(f, act), apply_capped(f, act, ok))

def Laws.fire_spends_ammo(f):
  match f:
    case R.Fighter{h, a, k}:
      match h:
        case 0n:
          {==}
        case 1n+p:
          match a:
            case 0n:
              {==}
            case 1n+q:
              {==}

# The storm
# ---------

def Laws.zone_never_grows(t):
  sub_le(R.radius(t), R.rate(t))
