# Last Circle

A top-down battle royale in the browser: you and 15 bots drop onto one field,
loot ammo and medkits, fight, and stay inside a safe circle that keeps
closing. The last one standing wins.

The combat rules are written in Bend 2 and come with **machine-checked
proofs** that they can't be broken.

| File            | What it is                                                         |
|-----------------|--------------------------------------------------------------------|
| `royale.bend`   | the rules: fighters, acts (hit, storm, heal, loot, fire, kill), the circle |
| `LAWS.bend`     | the rules the game must never break                                |
| `PROOF.bend`    | the proofs that every law holds                                    |
| `web/`          | the browser game; it imports `royale.bend` directly                |

## Run it

```bash
cd royale
bend PROOF.bend               # ALL PROOFS CHECK
bend royale.bend              # a scripted duel, and the circle over time
bend web/index.html -o dist   # bundle the browser game into dist/
```

Serve `dist/` with any static server (for example `npx http-server dist`).
Controls: WASD to move, mouse to aim, click or hold to shoot. On a phone, drag
with your left thumb to move and with your right thumb to aim and shoot.

## Who decides what

Bend owns the rules. Every change to a fighter's health, ammo or kills goes
through `R.apply(fighter, act)`; a gun only fires when `R.fired` says so; the
circle's radius at second `t` is `R.radius(t)`; storm damage, medkit and ammo
amounts, bullet damage and max health all live in `royale.bend`.

The browser owns movement, collisions, bullet flight, bot behaviour and
drawing. Those aren't covered by the laws.

## The laws

```python
law dead_stay_dead:     # a fighter at 0 health comes out of any sequence
  for  acts : List<&2, R.Act>   # of acts unchanged: no revives, no
  for +ammo : Nat               # healing, looting, shooting or kills
  for +kills: Nat
  {R.run(acts, R.Fighter{0n, ammo, kills}) == R.Fighter{0n, ammo, kills} : R.Fighter}

law hp_capped:          # health never goes above max_hp (100)
  for  acts: List<&2, R.Act>
  for +f   : R.Fighter
  for  ok  : R.LE(R.hp(f), R.max_hp())
  R.LE(R.hp(R.run(acts, f)), R.max_hp())

law fire_spends_ammo:   # bullets fired + ammo left == ammo before
  for +f: R.Fighter
  {Nat.add(R.fired(f), R.ammo(R.apply(f, R.Fire{}))) == R.ammo(f) : Nat}

law zone_never_grows:   # the circle at second t+1 is never wider than at t
  for +t: Nat
  R.LE(R.radius(1n+t), R.radius(t))
```

Each of these edits still compiles and runs, but `bend PROOF.bend` rejects
it with SOME PROOFS FAIL:

- let dead fighters act (`live(0n, a, k, act)` in `apply`): medkits revive;
- heal without `cap`: health climbs past 100;
- fire without `dec(a)`: infinite ammo;
- `Nat.add` instead of `Nat.sub` in `radius`: the storm grows back.
