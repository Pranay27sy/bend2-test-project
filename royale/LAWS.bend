# The laws of Last Circle. The human states them; PROOF.bend must prove
# them. `bend PROOF.bend` fails while any of them is open or false.

import Base
import ./royale.bend as R

# LAW: the dead stay dead. A fighter at 0 health, whatever its ammo and
# kills, comes out of any sequence of acts exactly as it went in: no
# revives, no healing, no looting, no shooting, no kills.
law dead_stay_dead:
  for  acts : List<&2, R.Act>
  for +ammo : Nat
  for +kills: Nat
  {R.run(acts, R.Fighter{0n, ammo, kills}) == R.Fighter{0n, ammo, kills} : R.Fighter}

# LAW: health never passes the cap. A fighter that starts at or below
# max_hp is still at or below it after any sequence of acts.
law hp_capped:
  for  acts: List<&2, R.Act>
  for +f   : R.Fighter
  for  ok  : R.LE(R.hp(f), R.max_hp())
  R.LE(R.hp(R.run(acts, f)), R.max_hp())

# LAW: a shot spends exactly the bullet it fires: the bullets a Fire act
# sends plus the ammo left after it are the ammo before. No free shots,
# and no ammo lost without a shot.
law fire_spends_ammo:
  for +f: R.Fighter
  {Nat.add(R.fired(f), R.ammo(R.apply(f, R.Fire{}))) == R.ammo(f) : Nat}

# LAW: the storm never grows back: at every second, the safe circle is
# no wider than the second before.
law zone_never_grows:
  for +t: Nat
  R.LE(R.radius(1n+t), R.radius(t))
