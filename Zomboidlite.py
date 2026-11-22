"""ZOMBOID LITE - uboga wersja survivalu z zombie (widok z gory, tkinter).

Uruchom:  python zomboid_lite.py
(tkinter jest w standardowym Pythonie - nic nie trzeba instalowac)

Cel: przetrwac jak najdluzej. Szukaj jedzenia i wody w domach, unikaj halasu,
nie daj sie ugryzc. Gdy zginiesz - zaczynasz od nowa w nowym swiecie.

Sterowanie:
  W/A/S/D - ruch     Shift - bieg (glosno!)     Ctrl albo C - skradanie (cicho)
  Mysz - celowanie   Lewy klik / Spacja - uderzenie
  E - przeszukaj / otworz-zamknij drzwi     1-9, 0 - uzyj przedmiotu / wez bron
  Esc lub P - pauza
"""

import math
import random
import time
import tkinter as tk
from collections import deque

# ------------------------------------------------------------------ ustawienia
TILE = 32
VIEW_W, VIEW_H = 800, 560
PANEL_W = 220
W, H = VIEW_W + PANEL_W, VIEW_H
N = 64                  # swiat N x N kafelkow
B = 16                  # rozmiar bloku (droga + dzialka)
TIME_SCALE = 2.0        # minut gry na sekunde rzeczywista
INV_SLOTS = 10

WALK, RUN, SNEAK = 3.0, 4.8, 1.6      # kafelki / s
PLAYER_R = 0.28

GRASS, ROAD, WOOD, TILEF, WALL, WINDOW, DOOR, TREE, FENCE, CONT, FURN = range(11)
BLOCK = {WALL, WINDOW, TREE, FENCE, CONT, FURN}

FONT = "Courier"

# ------------------------------------------------------------------ przedmioty
ITEMS = {
    "Puszka fasoli": dict(type="food", hunger=25, thirst=0),
    "Konserwa": dict(type="food", hunger=22, thirst=0),
    "Chleb": dict(type="food", hunger=18, thirst=0),
    "Czekolada": dict(type="food", hunger=12, thirst=0),
    "Jabłko": dict(type="food", hunger=8, thirst=4),
    "Woda butelkowana": dict(type="drink", hunger=0, thirst=45),
    "Sok": dict(type="drink", hunger=3, thirst=28),
    "Cola": dict(type="drink", hunger=4, thirst=22),
    "Bandaż": dict(type="bandage"),
    "Tabletki": dict(type="pills", heal=15),
    "Nóż kuchenny": dict(type="weapon", dmg=2, dur=40, reach=1.1, cd=0.40, noise=4, knock=0.3),
    "Patelnia": dict(type="weapon", dmg=2, dur=80, reach=1.1, cd=0.60, noise=6, knock=0.4),
    "Kij bejsbolowy": dict(type="weapon", dmg=3, dur=60, reach=1.5, cd=0.75, noise=8, knock=0.9),
    "Siekiera": dict(type="weapon", dmg=5, dur=50, reach=1.3, cd=0.95, noise=9, knock=0.5),
}
FISTS = dict(dmg=1, reach=1.0, cd=0.50, noise=3, knock=0.25)

LOOT = {
    "fridge": [("Chleb", 3), ("Jabłko", 3), ("Cola", 3), ("Woda butelkowana", 3), ("Sok", 3),
               ("Czekolada", 2), ("Puszka fasoli", 2)],
    "cabinet": [("Bandaż", 4), ("Tabletki", 3), ("Woda butelkowana", 3), ("Konserwa", 2),
                ("Nóż kuchenny", 1)],
    "shelf": [("Konserwa", 4), ("Puszka fasoli", 4), ("Czekolada", 2), ("Cola", 2),
              ("Woda butelkowana", 2), ("Bandaż", 1)],
    "wardrobe": [("Patelnia", 2), ("Kij bejsbolowy", 2), ("Bandaż", 3), ("Siekiera", 1)],
    "crate": [("Nóż kuchenny", 2), ("Kij bejsbolowy", 2), ("Siekiera", 1), ("Konserwa", 2),
              ("Woda butelkowana", 2), ("Tabletki", 1)],
}
CONT_COUNTS = {"fridge": [1, 2, 2, 3], "cabinet": [0, 1, 2, 2], "shelf": [1, 2, 2, 3],
               "wardrobe": [0, 0, 1, 1], "crate": [0, 1, 1, 2]}
CONT_NAMES = {"fridge": "lodówkę", "cabinet": "szafkę", "shelf": "regał",
              "wardrobe": "szafę", "crate": "skrzynię"}
CONT_TIME = {"fridge": 1.2, "cabinet": 1.4, "shelf": 1.2, "wardrobe": 1.8, "crate": 1.6}
CONT_COLORS = {"fridge": (225, 228, 232), "cabinet": (140, 96, 60), "shelf": (120, 120, 128),
               "wardrobe": (96, 62, 40), "crate": (170, 138, 84)}

ZOMBIE_COUNTS = {"low": 30, "mid": 50, "high": 80}
ZOMBIE_SPEEDS = {"slow": 1.0, "normal": 1.35, "fast": 2.0}


def clamp(v, a, b):
    return max(a, min(b, v))


def wrap(a):
    return (a + math.pi) % (2 * math.pi) - math.pi


def new_item(name):
    return {"n": name, "d": ITEMS[name].get("dur")}


def roll_loot(kind, rng):
    n = rng.choice(CONT_COUNTS[kind])
    names, weights = zip(*LOOT[kind])
    return [rng.choices(names, weights)[0] for _ in range(n)]


# ------------------------------------------------------------------ swiat
class World:
    def __init__(self, rng):
        self.rng = rng
        self.t = [[GRASS] * N for _ in range(N)]
        self.under = {}                 # co jest pod meblem / drzwiami
        self.doors = {}                 # (x, y) -> otwarte?
        self.conts = {}                 # (x, y) -> {"kind", "items", "looted"}
        self.furn = {}                  # (x, y) -> "bed" / "table"
        self.houses = []
        for y in range(N):
            for x in range(N):
                if x % B < 2 or y % B < 2:
                    self.t[y][x] = ROAD
        for i in range(N):
            for x, y in ((i, 0), (i, N - 1), (0, i), (N - 1, i)):
                self.t[y][x] = FENCE
        for by in range(4):
            for bx in range(4):
                lo_x, lo_y, avail = bx * B + 2, by * B + 2, B - 3
                if (bx, by) == (2, 2):
                    w, h, kind = 12, 9, "store"
                else:
                    w, h, kind = rng.randint(7, 11), rng.randint(6, 9), "house"
                x0 = lo_x + rng.randint(0, avail - w)
                y0 = lo_y + rng.randint(0, avail - h)
                house = self.build(x0, y0, w, h, kind)
                house["block"] = (bx, by)
                self.houses.append(house)
                for _ in range(rng.randint(4, 9)):
                    x = lo_x + rng.randint(0, avail - 1)
                    y = lo_y + rng.randint(0, avail - 1)
                    if self.t[y][x] == GRASS and not (x0 - 2 <= x <= x0 + w + 1 and y0 - 2 <= y <= y0 + h + 1):
                        self.t[y][x] = TREE
        start_house = next(h for h in self.houses if h["block"] == (1, 1))
        self.start_house = start_house
        # startowy dom ma jedzenie, picie i bandaz
        conts = [self.conts[p] for p in start_house["conts"]]
        for c, kind, items in zip(conts, ("fridge", "cabinet"),
                                  (["Chleb", "Cola", "Jabłko"], ["Bandaż", "Woda butelkowana", "Nóż kuchenny"])):
            c["kind"], c["items"] = kind, items
        cx, cy = start_house["center"]
        self.start = (cx + 0.5, cy + 0.5)

    def passable_tile(self, x, y):
        return 0 <= x < N and 0 <= y < N and self.t[y][x] not in BLOCK

    def reach_ok(self, origin, cells):
        seen = {origin}
        dq = deque([origin])
        while dq:
            x, y = dq.popleft()
            for dx, dy in ((1, 0), (-1, 0), (0, 1), (0, -1)):
                n = (x + dx, y + dy)
                if n not in seen and self.passable_tile(*n):
                    seen.add(n)
                    dq.append(n)
        return all(c in seen or self.t[c[1]][c[0]] in BLOCK for c in cells)

    def build(self, x0, y0, w, h, kind):
        t, rng = self.t, self.rng
        x1, y1 = x0 + w - 1, y0 + h - 1
        floor = TILEF if kind == "store" else WOOD
        for y in range(y0, y1 + 1):
            for x in range(x0, x1 + 1):
                t[y][x] = WALL if (x in (x0, x1) or y in (y0, y1)) else floor

        cands = []
        for x in range(x0 + 1, x1):
            cands.append(((x, y1), (x, y1 + 1)))
            cands.append(((x, y0), (x, y0 - 1)))
        for y in range(y0 + 1, y1):
            cands.append(((x0, y), (x0 - 1, y)))
            cands.append(((x1, y), (x1 + 1, y)))
        cands = [c for c in cands if t[c[1][1]][c[1][0]] in (GRASS, ROAD)]
        door, outside = rng.choice(cands)
        t[door[1]][door[0]] = DOOR
        self.doors[door] = False
        self.under[door] = floor

        perim = [(x, y0) for x in range(x0 + 1, x1)] + [(x, y1) for x in range(x0 + 1, x1)] + \
                [(x0, y) for y in range(y0 + 1, y1)] + [(x1, y) for y in range(y0 + 1, y1)]
        for x, y in perim:
            if t[y][x] == WALL and abs(x - door[0]) + abs(y - door[1]) > 1 and rng.random() < 0.28:
                t[y][x] = WINDOW

        if kind == "house" and w >= 9:
            px = x0 + w // 2
            if door[1] in (y0, y1) and door[0] == px:
                px += 1
            for y in range(y0 + 1, y1):
                t[y][px] = WALL
            dy = rng.randint(y0 + 2, y1 - 2)
            t[dy][px] = DOOR
            self.doors[(px, dy)] = False
            self.under[(px, dy)] = floor

        interior = [(x, y) for y in range(y0 + 1, y1) for x in range(x0 + 1, x1) if t[y][x] == floor]
        door_cells = [p for p in self.doors if x0 <= p[0] <= x1 and y0 <= p[1] <= y1]

        def ok_spot(p, taken):
            x, y = p
            if t[y][x] != floor:
                return False
            if not any(t[y + dy][x + dx] in (WALL, WINDOW) for dx, dy in ((1, 0), (-1, 0), (0, 1), (0, -1))):
                return False
            if any(abs(x - d[0]) + abs(y - d[1]) <= 2 for d in door_cells):
                return False
            return not any(abs(x - q[0]) <= 1 and abs(y - q[1]) <= 1 for q in taken)

        spots = [p for p in interior]
        rng.shuffle(spots)
        want_c = 11 if kind == "store" else rng.randint(3, 5)
        want_f = 1 if kind == "store" else rng.randint(1, 3)
        taken, conts = [], []
        placed_c = placed_f = 0
        for p in spots:
            if placed_c >= want_c and placed_f >= want_f:
                break
            if not ok_spot(p, taken):
                continue
            is_cont = placed_c < want_c
            prev = t[p[1]][p[0]]
            t[p[1]][p[0]] = CONT if is_cont else FURN
            if not self.reach_ok(outside, interior):
                t[p[1]][p[0]] = prev
                continue
            self.under[p] = floor
            taken.append(p)
            if is_cont:
                if kind == "store":
                    ck = "fridge" if placed_c < 2 else ("crate" if placed_c == 2 else "shelf")
                elif placed_c == 0:
                    ck = "fridge"
                elif placed_c == 1:
                    ck = "cabinet"
                else:
                    ck = rng.choice(["wardrobe", "shelf", "crate", "cabinet", "fridge"])
                self.conts[p] = {"kind": ck, "items": roll_loot(ck, rng), "looted": False}
                if kind == "store" and ck == "shelf":
                    self.conts[p]["items"] += roll_loot("shelf", rng)
                conts.append(p)
                placed_c += 1
            else:
                self.furn[p] = rng.choice(["bed", "table"])
                placed_f += 1
        free = [p for p in interior if t[p[1]][p[0]] == floor]
        cx, cy = (x0 + x1) // 2, (y0 + y1) // 2
        free.sort(key=lambda p: abs(p[0] - cx) + abs(p[1] - cy))
        return {"rect": (x0, y0, x1, y1), "kind": kind, "interior": interior, "door": door,
                "outside": outside, "conts": conts, "center": free[0] if free else (cx, cy)}


# ------------------------------------------------------------------ logika
class Zombie:
    def __init__(self, x, y, rng):
        self.x, self.y = x, y
        self.hp = 6.0
        self.face = rng.uniform(0, 2 * math.pi)
        self.state = "wander"
        self.last = (x, y)
        self.lost = 0.0
        self.cd = rng.uniform(0.2, 1.0)
        self.stagger = 0.0
        self.flash = 0.0
        self.wt = rng.uniform(0, 3)
        self.wdir = None


class Game:
    def __init__(self, zcount=50, zspeed=1.35, seed=None):
        self.rng = random.Random(seed)
        self.world = World(self.rng)
        self.x, self.y = self.world.start
        self.hp = 100.0
        self.hunger = 100.0
        self.thirst = 100.0
        self.bleeding = False
        self.infection = None
        self.inv = [new_item("Woda butelkowana")]
        self.equipped = None
        self.face = 0.0
        self.attack_cd = 0.0
        self.swing = 0.0
        self.sneak = False
        self.running = False
        self.moving = False
        self.action = None
        self.minutes = 8 * 60.0
        self.kills = 0
        self.msgs = []
        self.status = "playing"
        self.cause = ""
        self.event_noise = 0.0
        self.noise_r = 0.0
        self.hurt_flash = 0.0
        self.zspeed = zspeed
        self.zombies = []
        self.corpses = []
        self.flow = None
        self.flow_tile = None
        self.flow_age = 99.0
        self.last_hour = int(self.minutes // 60)
        self.warned = {"hunger": False, "thirst": False}
        self.spawn_initial(zcount)
        self.say("Przetrwaj. Znajdź jedzenie i wodę.  [E] - przeszukaj")

    # ---------- czas ----------
    @property
    def day(self):
        return int(self.minutes // 1440) + 1

    @property
    def hour(self):
        return (self.minutes % 1440) / 60.0

    def daylight(self):
        h = self.hour
        if 8 <= h < 18:
            return 1.0
        if 6 <= h < 8:
            return (h - 6) / 2
        if 18 <= h < 20:
            return 1 - (h - 18) / 2
        return 0.0

    # ---------- komunikaty ----------
    def say(self, text, ttl=4.0):
        self.msgs.append([text, ttl])
        self.msgs = self.msgs[-5:]

    # ---------- swiat ----------
    def spawn_initial(self, count):
        w = self.world
        outdoor = [(x, y) for y in range(N) for x in range(N) if w.t[y][x] in (GRASS, ROAD)]
        indoor = [p for h in w.houses for p in h["interior"] if w.t[p[1]][p[0]] in (WOOD, TILEF)]
        for _ in range(count):
            for _try in range(50):
                pool = indoor if (self.rng.random() < 0.4 and indoor) else outdoor
                x, y = self.rng.choice(pool)
                lim = 7 if pool is indoor else 14
                if math.hypot(x + 0.5 - self.x, y + 0.5 - self.y) > lim:
                    self.zombies.append(Zombie(x + 0.5, y + 0.5, self.rng))
                    break

    def free_p(self, x, y, r=PLAYER_R):
        t = self.world.t
        for cx in (x - r, x + r):
            for cy in (y - r, y + r):
                ix, iy = int(cx), int(cy)
                if not (0 <= ix < N and 0 <= iy < N):
                    return False
                tile = t[iy][ix]
                if tile == DOOR:
                    if not self.world.doors[(ix, iy)]:
                        self.world.doors[(ix, iy)] = True
                        self.event_noise = max(self.event_noise, 4)
                        return False
                elif tile in BLOCK:
                    return False
        return True

    def free_z(self, x, y, r=0.28):
        t = self.world.t
        for cx in (x - r, x + r):
            for cy in (y - r, y + r):
                ix, iy = int(cx), int(cy)
                if not (0 <= ix < N and 0 <= iy < N):
                    return False
                tile = t[iy][ix]
                if tile == DOOR:
                    self.world.doors[(ix, iy)] = True
                elif tile in BLOCK:
                    return False
        return True

    def los(self, x0, y0, x1, y1):
        t, doors = self.world.t, self.world.doors
        dx, dy = x1 - x0, y1 - y0
        steps = int(math.hypot(dx, dy) / 0.25) + 1
        for i in range(1, steps):
            f = i / steps
            ix, iy = int(x0 + dx * f), int(y0 + dy * f)
            tile = t[iy][ix]
            if tile == WALL or (tile == DOOR and not doors[(ix, iy)]):
                return False
        return True

    # ---------- gracz ----------
    def hurt(self, dmg, cause):
        self.hp -= dmg
        self.cause = cause
        self.hurt_flash = 0.3
        self.action = None

    def weapon(self):
        if self.equipped is not None:
            return ITEMS[self.equipped["n"]]
        return FISTS

    def attack(self):
        if self.attack_cd > 0:
            return
        self.action = None
        w = self.weapon()
        self.attack_cd = w["cd"]
        self.swing = 0.15
        self.event_noise = max(self.event_noise, w["noise"])
        hit = False
        for z in self.zombies[:]:
            dx, dy = z.x - self.x, z.y - self.y
            d = math.hypot(dx, dy)
            if d <= w["reach"] + 0.3 and abs(wrap(math.atan2(dy, dx) - self.face)) < 1.05 \
                    and self.los(self.x, self.y, z.x, z.y):
                hit = True
                z.hp -= w["dmg"]
                z.flash = 0.12
                z.stagger = 0.45
                z.state, z.last, z.lost = "chase", (self.x, self.y), 0.0
                k = w["knock"]
                nx, ny = z.x + dx / (d or 1) * k, z.y + dy / (d or 1) * k
                if self.free_z(nx, ny):
                    z.x, z.y = nx, ny
                if z.hp <= 0:
                    self.zombies.remove(z)
                    self.corpses.append((z.x, z.y))
                    self.kills += 1
        if hit and self.equipped is not None and self.equipped["d"] is not None:
            self.equipped["d"] -= 1
            if self.equipped["d"] <= 0:
                self.inv.remove(self.equipped)
                self.say(f"{self.equipped['n']} się zepsuł!")
                self.equipped = None

    def nearest_container(self):
        best, bd = None, 1.5
        for (cx, cy), c in self.world.conts.items():
            if c["looted"]:
                continue
            d = math.hypot(cx + 0.5 - self.x, cy + 0.5 - self.y)
            if d < bd:
                best, bd = (cx, cy), d
        return best, bd

    def nearest_door(self):
        best, bd = None, 1.3
        for (dx, dy) in self.world.doors:
            d = math.hypot(dx + 0.5 - self.x, dy + 0.5 - self.y)
            if d < bd:
                best, bd = (dx, dy), d
        return best, bd

    def prompt(self):
        if self.action or self.status != "playing":
            return None
        c, cd = self.nearest_container()
        d, dd = self.nearest_door()
        if c and (not d or cd <= dd):
            return f"[E] Przeszukaj {CONT_NAMES[self.world.conts[c]['kind']]}"
        if d:
            return "[E] Zamknij drzwi" if self.world.doors[d] else "[E] Otwórz drzwi"
        return None

    def interact(self):
        if self.action:
            return
        c, cd = self.nearest_container()
        d, dd = self.nearest_door()
        if c and (not d or cd <= dd):
            self.action = {"pos": c, "t": 0.0, "dur": CONT_TIME[self.world.conts[c]["kind"]]}
        elif d:
            if self.world.doors[d]:
                tx, ty = d
                occupied = (int(self.x) == tx and int(self.y) == ty) or \
                    any(int(z.x) == tx and int(z.y) == ty for z in self.zombies)
                if occupied:
                    self.say("Coś blokuje drzwi.")
                    return
            self.world.doors[d] = not self.world.doors[d]
            self.event_noise = max(self.event_noise, 4)

    def finish_search(self):
        pos = self.action["pos"]
        self.action = None
        c = self.world.conts[pos]
        if not c["items"]:
            c["looted"] = True
            self.say("Pusto.")
            return
        got = []
        while c["items"] and len(self.inv) < INV_SLOTS:
            name = c["items"].pop(0)
            self.inv.append(new_item(name))
            got.append(name)
        if got:
            self.say("Znaleziono: " + ", ".join(got))
        if c["items"]:
            self.say("Plecak pełny!")
        else:
            c["looted"] = True

    def use_item(self, idx):
        if self.status != "playing" or idx >= len(self.inv):
            return
        it = self.inv[idx]
        d = ITEMS[it["n"]]
        kind = d["type"]
        if kind in ("food", "drink"):
            if self.hunger >= 100 and d["hunger"] and not d["thirst"]:
                self.say("Nie jesteś głodny.")
                return
            self.hunger = min(100, self.hunger + d["hunger"])
            self.thirst = min(100, self.thirst + d["thirst"])
            self.inv.pop(idx)
            self.say(("Zjadłeś: " if kind == "food" else "Wypiłeś: ") + it["n"])
        elif kind == "bandage":
            if self.bleeding:
                self.bleeding = False
                self.inv.pop(idx)
                self.say("Zatamowałeś krwawienie.")
            else:
                self.say("Nie krwawisz.")
        elif kind == "pills":
            self.hp = min(100, self.hp + d["heal"])
            self.inv.pop(idx)
            self.say("Czujesz się trochę lepiej.")
        elif kind == "weapon":
            if self.equipped is it:
                self.equipped = None
                self.say("Chowasz broń.")
            else:
                self.equipped = it
                self.say(f"Bierzesz: {it['n']}")

    # ---------- zombie ----------
    def build_flow(self):
        sx, sy = int(self.x), int(self.y)
        dist = [[-1] * N for _ in range(N)]
        dist[sy][sx] = 0
        dq = deque([(sx, sy)])
        t = self.world.t
        while dq:
            x, y = dq.popleft()
            d = dist[y][x]
            if d >= 90:
                continue
            for dx, dy in ((1, 0), (-1, 0), (0, 1), (0, -1)):
                nx, ny = x + dx, y + dy
                if 0 <= nx < N and 0 <= ny < N and dist[ny][nx] < 0 and t[ny][nx] not in BLOCK:
                    dist[ny][nx] = d + 1
                    dq.append((nx, ny))
        self.flow = dist
        self.flow_tile = (sx, sy)
        self.flow_age = 0.0

    def flow_target(self, z):
        ix, iy = int(z.x), int(z.y)
        d0 = self.flow[iy][ix]
        if d0 < 0:
            return None
        if d0 == 0:
            return self.x, self.y
        t = self.world.t
        best, bd = None, d0
        for dx, dy in ((1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (1, -1), (-1, 1), (-1, -1)):
            nx, ny = ix + dx, iy + dy
            if not (0 <= nx < N and 0 <= ny < N) or self.flow[ny][nx] < 0 or self.flow[ny][nx] >= bd:
                continue
            if dx and dy and (t[iy][nx] in BLOCK or t[ny][ix] in BLOCK):
                continue
            best, bd = (nx, ny), self.flow[ny][nx]
        if best is None:
            return None
        return best[0] + 0.5, best[1] + 0.5

    def zmove(self, z, tx, ty, speed, dt):
        dx, dy = tx - z.x, ty - z.y
        d = math.hypot(dx, dy)
        if d < 1e-6:
            return False
        step = min(speed * dt, d)
        nx, ny = z.x + dx / d * step, z.y + dy / d * step
        moved = False
        if self.free_z(nx, z.y):
            z.x = nx
            moved = True
        if self.free_z(z.x, ny):
            z.y = ny
            moved = True
        return moved

    def update_zombies(self, dt, noise_r):
        sight = 4.0 + 8.0 * self.daylight()
        if self.sneak:
            sight *= 0.5
        chasing = False
        info = []
        for z in self.zombies:
            z.cd = max(0.0, z.cd - dt)
            z.stagger = max(0.0, z.stagger - dt)
            z.flash = max(0.0, z.flash - dt)
            dx, dy = self.x - z.x, self.y - z.y
            d = math.hypot(dx, dy) or 1e-6
            sees = hears = False
            if d < sight + 1:
                if d < 1.6 or (d < sight and abs(wrap(math.atan2(dy, dx) - z.face)) < 1.3):
                    sees = self.los(z.x, z.y, self.x, self.y)
            if d < noise_r:
                hears = self.los(z.x, z.y, self.x, self.y) or d < noise_r * 0.6
            if sees or hears:
                z.state, z.last, z.lost = "chase", (self.x, self.y), 0.0
            elif z.state == "chase":
                z.lost += dt
                if z.lost > 6.0:
                    z.state, z.wt = "wander", 0.0
            if z.state == "chase":
                chasing = True
            info.append((z, d, sees))

        if chasing and (self.flow is None or self.flow_tile != (int(self.x), int(self.y))
                        or self.flow_age > 1.0) and self.flow_age > 0.2:
            self.build_flow()

        for z, d, sees in info:
            if z.stagger > 0:
                continue
            if z.state == "chase":
                z.face = math.atan2(self.y - z.y, self.x - z.x) if sees else z.face
                if d > 0.7:
                    target = None
                    if sees and d < 7:
                        target = (self.x, self.y)
                    elif self.flow is not None:
                        target = self.flow_target(z)
                    if target is None:
                        target = z.last
                    z.face = math.atan2(target[1] - z.y, target[0] - z.x)
                    self.zmove(z, target[0], target[1], self.zspeed, dt)
                if d < 0.9 and z.cd <= 0:
                    z.cd = 1.1
                    if self.rng.random() < 0.55:
                        self.zombie_hit()
            else:
                z.wt -= dt
                if z.wt <= 0:
                    z.wt = self.rng.uniform(1.5, 4.5)
                    z.wdir = self.rng.choice([None, self.rng.uniform(0, 2 * math.pi)])
                if z.wdir is not None:
                    z.face = z.wdir
                    if not self.zmove(z, z.x + math.cos(z.wdir), z.y + math.sin(z.wdir),
                                      self.zspeed * 0.4, dt):
                        z.wt = 0.0

        zs = self.zombies
        for i in range(len(zs)):
            a = zs[i]
            for j in range(i + 1, len(zs)):
                b = zs[j]
                dx, dy = b.x - a.x, b.y - a.y
                if abs(dx) < 0.5 and abs(dy) < 0.5:
                    d = math.hypot(dx, dy) or 0.01
                    push = (0.5 - d) / 2
                    if push > 0:
                        ux, uy = dx / d * push, dy / d * push
                        if self.free_z(a.x - ux, a.y - uy):
                            a.x, a.y = a.x - ux, a.y - uy
                        if self.free_z(b.x + ux, b.y + uy):
                            b.x, b.y = b.x + ux, b.y + uy

    def zombie_hit(self):
        self.hurt(self.rng.uniform(7, 12), "Zagryziony przez zombie")
        if not self.bleeding and self.rng.random() < 0.30:
            self.bleeding = True
            self.say("Krwawisz! Potrzebujesz bandaża.")
        if self.infection is None and self.rng.random() < 0.08:
            self.infection = 720.0
            self.say("UGRYZIONY! Jesteś zarażony...", 8.0)

    def maybe_spawn_night_zombie(self):
        if self.daylight() > 0.3 or len(self.zombies) >= 120 or self.rng.random() > 0.35:
            return
        w = self.world
        for _ in range(40):
            x, y = self.rng.randrange(N), self.rng.randrange(N)
            d = math.hypot(x + 0.5 - self.x, y + 0.5 - self.y)
            if w.t[y][x] in (GRASS, ROAD) and 18 <= d <= 28:
                self.zombies.append(Zombie(x + 0.5, y + 0.5, self.rng))
                return

    # ---------- glowna aktualizacja ----------
    def update(self, dt, keys=(), aim=None, attack_held=False):
        if self.status != "playing":
            return
        dm = dt * TIME_SCALE
        self.minutes += dm
        self.hurt_flash = max(0.0, self.hurt_flash - dt)
        self.attack_cd = max(0.0, self.attack_cd - dt)
        self.swing = max(0.0, self.swing - dt)
        self.flow_age += dt
        for m in self.msgs:
            m[1] -= dt
        self.msgs = [m for m in self.msgs if m[1] > 0]

        mx = ("d" in keys) - ("a" in keys)
        my = ("s" in keys) - ("w" in keys)
        self.sneak = any(k in keys for k in ("Control_L", "Control_R", "c"))
        self.running = (("Shift_L" in keys) or ("Shift_R" in keys)) and not self.sneak
        self.moving = bool(mx or my)
        if aim is not None:
            self.face = aim
        if self.moving:
            if aim is None:
                self.face = math.atan2(my, mx)
            self.action = None
            n = math.hypot(mx, my)
            speed = SNEAK if self.sneak else (RUN if self.running else WALK)
            nx, ny = self.x + mx / n * speed * dt, self.y + my / n * speed * dt
            if self.free_p(nx, self.y):
                self.x = nx
            if self.free_p(self.x, ny):
                self.y = ny

        if attack_held:
            self.attack()
        if self.action:
            self.action["t"] += dt
            self.event_noise = max(self.event_noise, 2.0)
            if self.action["t"] >= self.action["dur"]:
                self.finish_search()

        if self.moving:
            base = 1.5 if self.sneak else (9.0 if self.running else 5.0)
        else:
            base = 0.8 if self.sneak else 1.5
        self.noise_r = max(base, self.event_noise)
        self.update_zombies(dt, self.noise_r)
        self.event_noise_shown = self.event_noise
        self.event_noise = 0.0

        # przetrwanie
        self.hunger = max(0.0, self.hunger - 0.03 * dm)
        self.thirst = max(0.0, self.thirst - 0.055 * dm)
        if self.hunger <= 0 or self.thirst <= 0:
            self.hp -= 0.25 * dm
            self.cause = "Głód i pragnienie"
        elif self.hunger > 30 and self.thirst > 30 and not self.bleeding and self.infection is None:
            self.hp = min(100.0, self.hp + 0.04 * dm)
        if self.bleeding:
            self.hp -= 0.35 * dm
            self.cause = "Wykrwawienie"
        if self.infection is not None:
            self.infection -= dm
            if self.infection <= 0:
                self.hp = 0
                self.cause = "Infekcja"
        for key, val in (("hunger", self.hunger), ("thirst", self.thirst)):
            if val < 25 and not self.warned[key]:
                self.warned[key] = True
                self.say("Jesteś głodny." if key == "hunger" else "Chce ci się pić.")
            elif val > 40:
                self.warned[key] = False

        h = int(self.minutes // 60)
        if h != self.last_hour:
            self.last_hour = h
            self.maybe_spawn_night_zombie()
            if h % 24 == 6:
                self.say(f"Świt. Dzień {self.day}.", 5.0)

        if self.hp <= 0:
            self.hp = 0
            self.status = "dead"
            self.action = None


# ------------------------------------------------------------------ rysowanie
def hexc(rgb, f=1.0):
    return "#%02x%02x%02x" % tuple(max(0, min(255, int(c * f))) for c in rgb)


GRASS_VARIANTS = [(66, 108, 58), (72, 116, 62), (62, 102, 54)]
BASE_COLORS = {ROAD: (72, 72, 78), WOOD: (146, 106, 68), TILEF: (168, 168, 172),
               WALL: (96, 82, 72), WINDOW: (130, 170, 200), FENCE: (112, 92, 62)}

MENU_STATES = ("title", "options", "paused", "dead")


class App:
    def __init__(self, root):
        self.root = root
        root.title("ZOMBOID LITE")
        root.resizable(False, False)
        self.canvas = tk.Canvas(root, width=W, height=H, bg="#14161c", highlightthickness=0)
        self.canvas.pack()

        self.settings = {"zombies": "mid", "speed": "normal"}
        self.game = Game(ZOMBIE_COUNTS["mid"], ZOMBIE_SPEEDS["normal"], seed=1)
        self.mode = "title"
        self.menu_index = 0
        self.keys = set()
        self.pending = {}
        self.mouse = (VIEW_W / 2, VIEW_H / 2)
        self.mouse_moved = False
        self.mouse_down = False
        self.last = time.perf_counter()
        self.pan = 0.0
        self.cam = (0, 0)

        root.bind("<KeyPress>", self.on_key_down)
        root.bind("<KeyRelease>", self.on_key_up)
        root.bind("<FocusOut>", lambda e: self.keys.clear())
        self.canvas.bind("<Motion>", self.on_motion)
        self.canvas.bind("<B1-Motion>", self.on_motion)
        self.canvas.bind("<Button-1>", self.on_mouse_down)
        self.canvas.bind("<ButtonRelease-1>", lambda e: setattr(self, "mouse_down", False))
        self.loop()

    # ---------- menu ----------
    def tr_opt(self, key, value):
        names = {"low": "Mało", "mid": "Średnio", "high": "Dużo",
                 "slow": "Wolne", "normal": "Normalne", "fast": "Szybkie"}
        return names[value]

    def items(self):
        s = self.settings
        if self.mode == "title":
            return [("Graj", self.start), ("Opcje", lambda: self.goto("options")),
                    ("Jak grać", lambda: self.goto("help")), ("Wyjście", self.root.destroy)]
        if self.mode == "options":
            return [(f"Zombie:  <  {self.tr_opt('z', s['zombies'])}  >", lambda: self.cycle("zombies")),
                    (f"Prędkość zombie:  <  {self.tr_opt('s', s['speed'])}  >", lambda: self.cycle("speed")),
                    ("Wróć", lambda: self.goto("title"))]
        if self.mode == "paused":
            return [("Wznów", self.resume), ("Menu główne", lambda: self.goto("title"))]
        if self.mode == "dead":
            return [("Jeszcze raz", self.start), ("Menu główne", lambda: self.goto("title"))]
        return []

    def cycle(self, key):
        opts = {"zombies": ["low", "mid", "high"], "speed": ["slow", "normal", "fast"]}[key]
        self.settings[key] = opts[(opts.index(self.settings[key]) + 1) % len(opts)]

    def goto(self, mode):
        self.mode = mode
        self.menu_index = 0

    def resume(self):
        self.mode = "playing"
        self.last = time.perf_counter()

    def start(self):
        s = self.settings
        self.game = Game(ZOMBIE_COUNTS[s["zombies"]], ZOMBIE_SPEEDS[s["speed"]])
        self.mode = "playing"
        self.keys.clear()
        self.last = time.perf_counter()

    @property
    def menu_top(self):
        return 250 if self.mode in ("title", "options") else 300

    def item_at(self, x, y):
        for i in range(len(self.items())):
            top = self.menu_top + i * 58
            if W / 2 - 190 <= x <= W / 2 + 190 and top <= y <= top + 46:
                return i
        return None

    # ---------- wejscie ----------
    def on_key_down(self, event):
        key = event.keysym
        if len(key) == 1:
            key = key.lower()
        if key in self.pending:
            self.root.after_cancel(self.pending.pop(key))
        if key in self.keys:
            return
        self.keys.add(key)
        self.handle_action(key)

    def on_key_up(self, event):
        key = event.keysym
        if len(key) == 1:
            key = key.lower()
        self.pending[key] = self.root.after(12, lambda k=key: self.release(k))

    def release(self, key):
        self.keys.discard(key)
        self.pending.pop(key, None)

    def on_motion(self, event):
        self.mouse = (event.x, event.y)
        self.mouse_moved = True
        if self.mode in MENU_STATES:
            i = self.item_at(event.x, event.y)
            if i is not None:
                self.menu_index = i

    def on_mouse_down(self, event):
        if self.mode == "help":
            self.goto("title")
        elif self.mode in MENU_STATES:
            i = self.item_at(event.x, event.y)
            if i is not None:
                self.menu_index = i
                self.items()[i][1]()
        elif self.mode == "playing":
            self.mouse_down = True

    def handle_action(self, key):
        m = self.mode
        if m == "playing":
            if key in ("Escape", "p"):
                self.mode = "paused"
                self.menu_index = 0
            elif key == "e":
                self.game.interact()
            elif key.isdigit():
                self.game.use_item(9 if key == "0" else int(key) - 1)
            return
        if m == "help":
            self.goto("title")
            return
        items = self.items()
        if key in ("Up", "w"):
            self.menu_index = (self.menu_index - 1) % len(items)
        elif key in ("Down", "s"):
            self.menu_index = (self.menu_index + 1) % len(items)
        elif key in ("Return", "KP_Enter", "space"):
            items[self.menu_index][1]()
        elif key in ("Left", "Right") and m == "options" and self.menu_index < 2:
            self.cycle(("zombies", "speed")[self.menu_index])
        elif key == "Escape":
            if m == "paused":
                self.resume()
            elif m in ("options", "dead"):
                self.goto("title")
        elif key == "r" and m == "dead":
            self.start()

    # ---------- petla ----------
    def loop(self):
        now = time.perf_counter()
        dt = min(0.05, now - self.last)
        self.last = now
        g = self.game
        if self.mode == "playing":
            aim = None
            if self.mouse_moved:
                sx, sy = self.player_screen()
                aim = math.atan2(self.mouse[1] - sy, self.mouse[0] - sx)
            g.update(dt, self.keys, aim, self.mouse_down or "space" in self.keys)
            if g.status == "dead":
                self.mode = "dead"
                self.menu_index = 0
        elif self.mode in ("title", "options", "help"):
            self.pan += dt * 40
        self.draw()
        self.root.after(15, self.loop)

    def camera(self):
        g = self.game
        if self.mode in ("title", "options", "help"):
            cx = 300 + (self.pan % 1400)
            cy = 640
        else:
            cx, cy = g.x * TILE, g.y * TILE
        camx = clamp(cx - VIEW_W / 2, 0, N * TILE - VIEW_W)
        camy = clamp(cy - VIEW_H / 2, 0, N * TILE - VIEW_H)
        return camx, camy

    def player_screen(self):
        camx, camy = self.camera()
        return self.game.x * TILE - camx, self.game.y * TILE - camy

    # ---------- rysowanie swiata ----------
    def ground_rgb(self, tx, ty):
        w = self.game.world
        t = w.t[ty][tx]
        if t in (GRASS, TREE):
            return GRASS_VARIANTS[((tx // 4) * 7 + (ty // 4) * 3) % 3]
        if t in (DOOR, CONT, FURN):
            t = w.under.get((tx, ty), WOOD)
        return BASE_COLORS[t]

    def draw_ground(self, camx, camy, bright):
        c = self.canvas
        tx0, tx1 = int(camx // TILE), min(N - 1, int((camx + VIEW_W) // TILE))
        ty0, ty1 = int(camy // TILE), min(N - 1, int((camy + VIEW_H) // TILE))
        for ty in range(ty0, ty1 + 1):
            run, start = None, tx0
            for tx in range(tx0, tx1 + 2):
                col = self.ground_rgb(tx, ty) if tx <= tx1 else None
                if col != run:
                    if run is not None:
                        c.create_rectangle(start * TILE - camx, ty * TILE - camy, tx * TILE - camx,
                                           (ty + 1) * TILE - camy, fill=hexc(run, bright), outline="")
                    run, start = col, tx

    def draw_world(self, camx, camy, bright, show_prompt=True):
        c, g = self.canvas, self.game
        w = g.world
        self.draw_ground(camx, camy, bright)
        tx0, tx1 = int(camx // TILE), min(N - 1, int((camx + VIEW_W) // TILE))
        ty0, ty1 = int(camy // TILE), min(N - 1, int((camy + VIEW_H) // TILE))

        for ty in range(ty0, ty1 + 1):
            for tx in range(tx0, tx1 + 1):
                t = w.t[ty][tx]
                if t not in (TREE, DOOR, CONT, FURN):
                    continue
                x0, y0 = tx * TILE - camx, ty * TILE - camy
                if t == TREE:
                    c.create_oval(x0 - 3, y0 - 3, x0 + TILE + 3, y0 + TILE + 3,
                                  fill=hexc((34, 84, 44), bright), outline=hexc((20, 56, 30), bright))
                    c.create_oval(x0 + 6, y0 + 5, x0 + TILE - 8, y0 + TILE - 9,
                                  fill=hexc((46, 104, 56), bright), outline="")
                elif t == DOOR:
                    if w.doors[(tx, ty)]:
                        c.create_rectangle(x0, y0, x0 + 4, y0 + TILE, fill=hexc((110, 72, 40), bright),
                                           outline="")
                    else:
                        c.create_rectangle(x0 + 1, y0 + 1, x0 + TILE - 1, y0 + TILE - 1,
                                           fill=hexc((110, 72, 40), bright), outline=hexc((60, 38, 20), bright))
                        c.create_oval(x0 + TILE - 10, y0 + TILE // 2 - 2, x0 + TILE - 6, y0 + TILE // 2 + 2,
                                      fill=hexc((220, 190, 90), bright), outline="")
                elif t == CONT:
                    cont = w.conts[(tx, ty)]
                    col = (80, 80, 84) if cont["looted"] else CONT_COLORS[cont["kind"]]
                    c.create_rectangle(x0 + 3, y0 + 3, x0 + TILE - 3, y0 + TILE - 3, fill=hexc(col, bright),
                                       outline=hexc((30, 24, 20), bright), width=2)
                    if cont["kind"] in ("shelf", "cabinet"):
                        c.create_line(x0 + 5, y0 + TILE // 2, x0 + TILE - 5, y0 + TILE // 2,
                                      fill=hexc((40, 34, 30), bright))
                else:
                    kind = w.furn[(tx, ty)]
                    col = (110, 120, 170) if kind == "bed" else (120, 84, 50)
                    c.create_rectangle(x0 + 2, y0 + 2, x0 + TILE - 2, y0 + TILE - 2, fill=hexc(col, bright),
                                       outline=hexc((30, 24, 20), bright), width=2)

        for x, y in g.corpses:
            sx, sy = x * TILE - camx, y * TILE - camy
            if -20 < sx < VIEW_W + 20 and -20 < sy < VIEW_H + 20:
                c.create_oval(sx - 13, sy - 9, sx + 13, sy + 9, fill=hexc((92, 14, 14), bright), outline="")
                c.create_oval(sx - 9, sy - 6, sx + 9, sy + 6, fill=hexc((70, 84, 62), bright), outline="")

        for z in g.zombies:
            sx, sy = z.x * TILE - camx, z.y * TILE - camy
            if not (-20 < sx < VIEW_W + 20 and -20 < sy < VIEW_H + 20):
                continue
            body = (240, 230, 230) if z.flash > 0 else (118, 138, 100)
            r = 10
            ax, ay = math.cos(z.face), math.sin(z.face)
            px, py = -ay, ax
            for side in (-1, 1):
                c.create_line(sx + px * side * 7, sy + py * side * 7,
                              sx + px * side * 7 + ax * 14, sy + py * side * 7 + ay * 14,
                              fill=hexc((92, 112, 80), bright), width=4)
            c.create_oval(sx - r, sy - r, sx + r, sy + r, fill=hexc(body, bright),
                          outline=hexc((50, 62, 44), bright), width=2)
            if z.hp < 6:
                c.create_rectangle(sx - 10, sy - 18, sx + 10, sy - 15, fill="#400000", outline="")
                c.create_rectangle(sx - 10, sy - 18, sx - 10 + 20 * z.hp / 6, sy - 15, fill="#d02020",
                                   outline="")

        # gracz
        sx, sy = g.x * TILE - camx, g.y * TILE - camy
        if self.mode != "title":
            ax, ay = math.cos(g.face), math.sin(g.face)
            if g.equipped is not None:
                wl = 22 if g.equipped["n"] in ("Kij bejsbolowy", "Siekiera") else 16
                c.create_line(sx, sy, sx + ax * wl, sy + ay * wl, fill="#cfcfcf", width=4)
            r = 9 if g.sneak else 10
            c.create_oval(sx - r, sy - r, sx + r, sy + r, fill="#4a8fd0" if not g.sneak else "#3a6f9e",
                          outline="#1c3a5a", width=2)
            c.create_oval(sx + ax * 5 - 3, sy + ay * 5 - 3, sx + ax * 5 + 3, sy + ay * 5 + 3,
                          fill="#f0d0a8", outline="")
            if g.swing > 0:
                reach = g.weapon()["reach"] * TILE
                deg = -math.degrees(g.face)
                c.create_arc(sx - reach, sy - reach, sx + reach, sy + reach, start=deg - 45, extent=90,
                             style="arc", outline="#ffffff", width=3)
            if g.noise_r >= 5 or getattr(g, "event_noise_shown", 0) >= 3:
                rr = max(g.noise_r, getattr(g, "event_noise_shown", 0)) * TILE
                c.create_oval(sx - rr, sy - rr, sx + rr, sy + rr, outline="#7a7a2a", dash=(3, 6))
            if g.action:
                frac = g.action["t"] / g.action["dur"]
                c.create_rectangle(sx - 18, sy - 26, sx + 18, sy - 20, fill="#202020", outline="#aaaaaa")
                c.create_rectangle(sx - 18, sy - 26, sx - 18 + 36 * frac, sy - 20, fill="#6dd06d", outline="")

    def draw_night(self, bright):
        g = self.game
        radius = (5 + 25 * g.daylight()) * TILE
        if radius > 520 or self.mode not in ("playing", "paused", "dead"):
            return
        sx, sy = self.player_screen()
        pts = [0, 0, VIEW_W, 0, VIEW_W, VIEW_H, 0, VIEW_H, 0, 0]
        n = 36
        pts += [sx + radius, sy]
        for k in range(1, n + 1):
            a = -2 * math.pi * k / n
            pts += [sx + math.cos(a) * radius, sy + math.sin(a) * radius]
        pts += [0, 0]
        self.canvas.create_polygon(*pts, fill="#05060a", outline="")

    # ---------- panel i HUD ----------
    def bar(self, x, y, w, frac, color, label, value):
        c = self.canvas
        c.create_text(x, y, text=label, fill="#9a9aa8", font=(FONT, 9, "bold"), anchor="w")
        c.create_text(x + w, y, text=value, fill="#e8eaf0", font=(FONT, 9, "bold"), anchor="e")
        c.create_rectangle(x, y + 8, x + w, y + 18, fill="#2a2d36", outline="#555866")
        c.create_rectangle(x, y + 8, x + w * clamp(frac, 0, 1), y + 18, fill=color, outline="")

    def draw_panel(self):
        c, g = self.canvas, self.game
        x0 = VIEW_W
        c.create_rectangle(x0, 0, W, H, fill="#14161c", outline="#3a3d48", width=2)
        mins = int(g.minutes % 1440)
        c.create_text(x0 + 12, 18, text=f"Dzień {g.day}   {mins // 60:02d}:{mins % 60:02d}", fill="#ffe27a",
                      font=(FONT, 13, "bold"), anchor="w")
        hp_col = "#5cc070" if g.hp > 60 else ("#e0b030" if g.hp > 30 else "#d03030")
        self.bar(x0 + 12, 44, PANEL_W - 24, g.hp / 100, hp_col, "ZDROWIE", f"{int(g.hp)}")
        self.bar(x0 + 12, 80, PANEL_W - 24, g.hunger / 100, "#c08a40", "GŁÓD", f"{int(g.hunger)}")
        self.bar(x0 + 12, 116, PANEL_W - 24, g.thirst / 100, "#4a90d0", "PRAGNIENIE", f"{int(g.thirst)}")

        y = 156
        status = []
        if g.bleeding:
            status.append(("KRWAWISZ", "#ff4a4a"))
        if g.infection is not None:
            status.append((f"ZARAŻONY ({int(g.infection // 60) + 1} h)", "#b8d040"))
        if g.sneak:
            status.append(("skradanie", "#8ab0d0"))
        elif g.running and g.moving:
            status.append(("bieg (głośno)", "#d0a050"))
        for text, col in status:
            c.create_text(x0 + 12, y, text=text, fill=col, font=(FONT, 10, "bold"), anchor="w")
            y += 16

        y = max(y + 8, 214)
        c.create_text(x0 + 12, y, text="PLECAK", fill="#9a9aa8", font=(FONT, 10, "bold"), anchor="w")
        y += 18
        for i in range(INV_SLOTS):
            key = (i + 1) % 10
            if i < len(g.inv):
                it = g.inv[i]
                eq = g.equipped is it
                label = it["n"] + (f" ({it['d']})" if it["d"] is not None else "")
                col = "#ffe27a" if eq else "#e8eaf0"
                c.create_text(x0 + 12, y, text=f"{key}. {'*' if eq else ' '}{label}", fill=col,
                              font=(FONT, 10), anchor="w")
            else:
                c.create_text(x0 + 12, y, text=f"{key}. -", fill="#4a4d58", font=(FONT, 10), anchor="w")
            y += 17
        w = g.weapon()
        wname = g.equipped["n"] if g.equipped is not None else "Pięści"
        c.create_text(x0 + 12, H - 52, text=f"Broń: {wname}", fill="#d8d8d8", font=(FONT, 10), anchor="w")
        c.create_text(x0 + 12, H - 34, text=f"Zabite zombie: {g.kills}", fill="#d8d8d8",
                      font=(FONT, 10), anchor="w")
        c.create_text(x0 + 12, H - 16, text="E - szukaj   Esc - pauza", fill="#6a6d78",
                      font=(FONT, 9), anchor="w")

    def draw_messages(self):
        c, g = self.canvas, self.game
        y = VIEW_H - 14
        prompt = g.prompt()
        if prompt:
            c.create_text(VIEW_W / 2, VIEW_H - 62, text=prompt, fill="#ffffff", font=(FONT, 13, "bold"))
        for text, ttl in reversed(g.msgs):
            c.create_text(14, y, text=text, fill="#f0e8c8" if ttl > 1 else "#8a8468",
                          font=(FONT, 11, "bold"), anchor="sw")
            y -= 18

    # ---------- menu ----------
    def draw_buttons(self):
        c = self.canvas
        for i, (label, _) in enumerate(self.items()):
            top = self.menu_top + i * 58
            sel = i == self.menu_index
            c.create_rectangle(W / 2 - 190, top, W / 2 + 190, top + 46,
                               fill="#8a1c1c" if sel else "#1f232c", outline="#c03030", width=2)
            c.create_text(W / 2, top + 23, text=label, fill="#ffffff" if sel else "#d8d8d8",
                          font=(FONT, 15, "bold"))

    def draw_panel_box(self, title, sub, color):
        c = self.canvas
        c.create_rectangle(W / 2 - 260, 90, W / 2 + 260, 440, fill="#0a0a0e", outline=color, width=3)
        c.create_text(W / 2, 150, text=title, fill=color, font=(FONT, 34, "bold"))
        for i, line in enumerate(sub):
            c.create_text(W / 2, 205 + i * 26, text=line, fill="#d8d8d8", font=(FONT, 13))

    def draw(self):
        c, g = self.canvas, self.game
        c.delete("all")
        camx, camy = self.camera()
        ingame = self.mode in ("playing", "paused", "dead")
        bright = 0.35 + 0.65 * g.daylight() if ingame else 0.55
        self.draw_world(camx, camy, bright)
        if ingame:
            self.draw_night(bright)
            if g.hurt_flash > 0:
                wdt = max(2, int(16 * g.hurt_flash / 0.3))
                c.create_rectangle(wdt / 2, wdt / 2, VIEW_W - wdt / 2, VIEW_H - wdt / 2, outline="#c01010",
                                   width=wdt)
            self.draw_messages()
            self.draw_panel()

        m = self.mode
        if m == "title":
            c.create_rectangle(0, 40, W, 210, fill="#0a0a0e", outline="#8a1c1c", width=3)
            c.create_text(W / 2 + 3, 113, text="ZOMBOID LITE", fill="#3a0808", font=(FONT, 60, "bold"))
            c.create_text(W / 2, 110, text="ZOMBOID LITE", fill="#d03030", font=(FONT, 60, "bold"))
            c.create_text(W / 2, 178, text="uboga wersja survivalu - przetrwaj tak długo, jak się da",
                          fill="#a8a0a0", font=(FONT, 12))
            self.draw_buttons()
        elif m == "options":
            c.create_rectangle(0, 40, W, 210, fill="#0a0a0e", outline="#8a1c1c", width=3)
            c.create_text(W / 2, 110, text="OPCJE", fill="#d03030", font=(FONT, 50, "bold"))
            c.create_text(W / 2, 178, text="strzałki lewo/prawo albo klik - zmiana wartości",
                          fill="#a8a0a0", font=(FONT, 12))
            self.draw_buttons()
        elif m == "help":
            c.create_rectangle(120, 40, W - 120, 520, fill="#0a0a0e", outline="#8a1c1c", width=3)
            c.create_text(W / 2, 90, text="JAK GRAĆ", fill="#d03030", font=(FONT, 34, "bold"))
            lines = ["W/A/S/D - ruch,  mysz - celowanie,  lewy klik / spacja - uderzenie",
                     "Shift - bieg (bardzo głośno),  Ctrl lub C - skradanie (cicho)",
                     "E - przeszukaj lodówkę, szafkę, regał...  /  otwórz i zamknij drzwi",
                     "1-9, 0 - zjedz, wypij, użyj bandaża albo weź broń do ręki",
                     "",
                     "Zombie widzą cię i SŁYSZĄ. Hałas przyciąga je z daleka.",
                     "Zamknięte drzwi chronią przed wzrokiem, ale nie na długo.",
                     "Rany krwawią - bandaż. Ugryzienie = infekcja = śmierć.",
                     "Nocą widzisz tylko najbliższe otoczenie.",
                     "Jedzenie i picie znajdziesz w domach i w sklepie na środku miasta."]
            for i, line in enumerate(lines):
                c.create_text(W / 2, 150 + i * 30, text=line, fill="#d8d8d8", font=(FONT, 12))
            c.create_text(W / 2, 495, text="naciśnij dowolny klawisz albo kliknij", fill="#8a8a98",
                          font=(FONT, 11))
        elif m == "paused":
            self.draw_panel_box("PAUZA", [], "#e8eaf0")
            self.draw_buttons()
        elif m == "dead":
            hrs = int(g.minutes // 60) - 8
            self.draw_panel_box("TAK ZGINĄŁEŚ", [
                g.cause or "Zombie cię dopadły",
                f"Przetrwałeś: {max(0, hrs // 24)} dni i {max(0, hrs) % 24} godz.",
                f"Zabite zombie: {g.kills}"], "#d03030")
            self.draw_buttons()


def main():
    root = tk.Tk()
    App(root)
    root.mainloop()


if __name__ == "__main__":
    main()
