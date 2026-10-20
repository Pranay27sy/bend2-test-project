# royale: the rules of Last Circle, a top-down battle royale. Every
# fighter's health, ammo and kills live here, and every shot, hit, heal,
# pickup and second in the storm is an Act that this file applies. The
# safe circle's radius at every second is decided here too. The browser
# (web/) only moves fighters around and draws them; it asks this file
# what each act does.
#
# LAWS.bend states that the dead stay dead, health never passes the cap,
# a shot spends exactly the bullet it fires, and the storm never grows
# back. PROOF.bend proves all four.
#
#   bend royale.bend           # a scripted duel
#   bend web/index.html -o dist  # bundle the browser game

import Base

# Evidence
# --------
# LE(a, b) is the type of proofs of a <= b: Unit when it holds, Empty
# when it fails. le_case hands back the verdict with its evidence.

def LE(a: Nat, b: Nat) -> Data:
  match a b:
    case 0n b0:
      Unit
    case 1n+a1 0n:
      Empty
    case 1n+a1 1n+b1:
      LE(a1, b1)

def le_case(a: Nat, b: Nat) -> Or(LE(a, b), LE(b, a)):
  match a b:
    case 0n b0:
      Inl{Unit{}}
    case 1n+a1 0n:
      Inr{Unit{}}
    case 1n+a1 1n+b1:
      le_case(a1, b1)

def pick(-A: Type, c: Bool, a: A, b: A) -> A:
  match c:
    case True{}:
      a
    case False{}:
      b

# Tuning
# ------

def max_hp() -> Nat:
  100n

def start_ammo() -> Nat:
  12n

def bullet_dmg() -> Nat:
  17n

def medkit_heal() -> Nat:
  40n

def ammo_box() -> Nat:
  15n

# Fighters
# --------

type Fighter is Data:
  Fighter{hp: Nat, ammo: Nat, kills: Nat}

type Act is Data:
  Hit{dmg: Nat}    # a bullet struck
  Storm{dmg: Nat}  # a second spent outside the safe circle
  Heal{amt: Nat}   # a medkit
  Loot{n: Nat}     # an ammo box
  Fire{}           # pulled the trigger
  Kill{}           # finished someone off

def spawn() -> Fighter:
  Fighter{max_hp(), start_ammo(), 0n}

def hp(f: Fighter) -> Nat:
  Fighter{h, a, k} = f
  h

def ammo(f: Fighter) -> Nat:
  Fighter{h, a, k} = f
  a

def kills(f: Fighter) -> Nat:
  Fighter{h, a, k} = f
  k

def alive(f: Fighter) -> Bool:
  Fighter{h, a, k} = f
  match h:
    case 0n:
      False{}
    case 1n+p:
      True{}

# health after a heal: never above max_hp
def cap.go(+n: Nat, c: Or(LE(n, max_hp()), LE(max_hp(), n))) -> Nat:
  match c:
    case Inl{e}:
      n
    case Inr{e}:
      max_hp()

def cap(+n: Nat) -> Nat:
  cap.go(n, le_case(n, max_hp()))

# one less, stopping at 0n
def dec(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

# what an act does to a fighter with h > 0 health
def live(+h: Nat, +a: Nat, +k: Nat, act: Act) -> Fighter:
  match act:
    case Hit{d}:
      Fighter{Nat.sub(h, d), a, k}
    case Storm{d}:
      Fighter{Nat.sub(h, d), a, k}
    case Heal{n}:
      Fighter{cap(Nat.add(h, n)), a, k}
    case Loot{n}:
      Fighter{h, Nat.add(a, n), k}
    case Fire{}:
      Fighter{h, dec(a), k}
    case Kill{}:
      Fighter{h, a, 1n+k}

# a fighter at 0 health ignores every act
def apply(f: Fighter, act: Act) -> Fighter:
  match f:
    case Fighter{h, +a, +k}:
      match h:
        case 0n:
          Fighter{0n, a, k}
        case 1n++p:
          live(1n+p, a, k, act)

# the bullets a Fire act sends: 1n when alive and loaded, else 0n
def fired(f: Fighter) -> Nat:
  match f:
    case Fighter{h, a, k}:
      match h:
        case 0n:
          0n
        case 1n+p:
          match a:
            case 0n:
              0n
            case 1n+q:
              1n

# applies every act in order
def run(acts: List<&2, Act>, f: Fighter) -> Fighter:
  match acts:
    case Nil{}:
      f
    case act <> rest:
      run(rest, apply(f, act))

# The storm
# ---------
# The safe circle starts wide enough to cover the whole map, then closes
# in phases: a wait, a shrink, a wait, a faster shrink... The browser
# asks radius(t) for second t and blends between seconds.

def start_radius() -> Nat:
  1700n

# how far the circle closes during second s
def rate(+s: Nat) -> Nat:
  pick(Nat, Nat.is_lt(s, 25n), 0n,
    pick(Nat, Nat.is_lt(s, 55n), 18n,
      pick(Nat, Nat.is_lt(s, 75n), 0n,
        pick(Nat, Nat.is_lt(s, 105n), 14n,
          pick(Nat, Nat.is_lt(s, 120n), 0n,
            pick(Nat, Nat.is_lt(s, 150n), 10n,
              pick(Nat, Nat.is_lt(s, 165n), 0n,
                pick(Nat, Nat.is_lt(s, 190n), 8n, 4n))))))))

def radius(t: Nat) -> Nat:
  match t:
    case 0n:
      start_radius()
    case 1n++s:
      Nat.sub(radius(s), rate(s))

# the damage a second in the storm deals, growing each phase
def storm_dmg(+t: Nat) -> Nat:
  pick(Nat, Nat.is_lt(t, 75n), 2n,
    pick(Nat, Nat.is_lt(t, 150n), 5n, 10n))

# seconds until the circle next starts closing (0n while it closes)
def next_shrink(+t: Nat) -> Nat:
  pick(Nat, Nat.is_lt(t, 25n), Nat.sub(25n, t),
    pick(Nat, Nat.is_lt(t, 55n), 0n,
      pick(Nat, Nat.is_lt(t, 75n), Nat.sub(75n, t),
        pick(Nat, Nat.is_lt(t, 105n), 0n,
          pick(Nat, Nat.is_lt(t, 120n), Nat.sub(120n, t),
            pick(Nat, Nat.is_lt(t, 150n), 0n,
              pick(Nat, Nat.is_lt(t, 165n), Nat.sub(165n, t), 0n)))))))

# Demo
# ----

def show(f: Fighter) -> String:
  Fighter{h, a, k} = f
  "hp " ++ Nat.show(h) ++ ", ammo " ++ Nat.show(a) ++ ", kills " ++ Nat.show(k)

def main() -> IO(Unit):
  +duel = {[Fire{}, Hit{40n}, Heal{medkit_heal()}, Heal{medkit_heal()}, Loot{ammo_box()},
    Storm{storm_dmg(80n)}, Hit{100n}, Heal{medkit_heal()}, Fire{}] : List<&2, Act>}
  do IO<Unit>:
    IO.print("spawn: " ++ show(spawn()))
    IO.print("after: " ++ show(run(duel, spawn())) ++ "  (the heal after dying did nothing)")
    IO.print("circle: " ++ Nat.show(radius(0n)) ++ " -> " ++ Nat.show(radius(60n)) ++ " -> " ++ Nat.show(radius(200n)))
