import requests
import numpy
import time
import itertools as itr
import bisect
import json
import traceback
import os.path


MAX_ID      = 31_797_108
BATCH       = 50
MIN_SAMPLE  = 200
RATELIMIT   = 1000

brackets = list(itr.takewhile(lambda x: x < MAX_ID, map(lambda x: 10**x, itr.count(2))))
brackets.append(MAX_ID)

MAXITER = 100 * MIN_SAMPLE * len(brackets)
PRELOAD = 10000

class Bracket:
    def __init__(self, higher):
        self.yes = 0
        self.no  = 0
        self.tot = 0

        self.higher = higher
        self._bound = self.higher ** 0.5

    def inc_yes(self):
        self.yes += 1
        self.tot += 1

    def inc_no(self):
        self.no  += 1
        self.tot += 1

    def done(self):
        return self.tot > MIN_SAMPLE or self.tot > self._bound

    def _json(self):
        return {"yes": self.yes, "no": self.no, "tot": self.tot}

samples = [Bracket(x) for x in brackets]

def _json():
    return (brackets, [y._json() for y in samples])


try:
  with open("credentials.json") as f:
      credentials = json.load(f)

      CLIENT_ID = int(credentials["client_id"])
      SECRET    = credentials["secret"]
except:
    print("Found no credentials, will fail if resampling is necessary")
    print()
    print()

token = [None]


def get_token():
    endpoint = "https://osu.ppy.sh/oauth/token"

    headers = {
        "Accept": "application/json",
        "Content-Type": "application/json",
    }

    body = {
        "client_id": CLIENT_ID,
        "client_secret": SECRET,
        "grant_type": "client_credentials",
        "scope": "public"
    }

    return requests.post(endpoint, headers=headers, json=body).json()

def get_users(uids):
    endpoint = f"https://osu.ppy.sh/api/v2/users/"

    params = {
        "key": "id",
        "ids[]": uids
    }

    if not token[0]:
        token[0] = get_token()["access_token"]

    headers = {
        "Authorization": f"Bearer {token[0]}",
        "Content-Type": "application/json",
        "Accept": "application/json",
    }

    return requests.get(endpoint, params=params, headers=headers).json()

def ranking(cursor=None):
    endpoint = "https://osu.ppy.sh/api/v2/rankings/osu/performance"

    params = {
        "filter": "all",
    }

    if cursor:
        for k, v in cursor.items():
            params[f"cursor[{k}]"] = v

    if not token[0]:
        token[0] = get_token()["access_token"]

    headers = {
        "Authorization": f"Bearer {token[0]}",
        "Content-Type": "application/json",
        "Accept": "application/json",
    }

    return requests.get(endpoint, params=params, headers=headers).json()

def draw_ranking(cursor=None):
    ranks = ranking(cursor=cursor)

    overview = {}

    try:
        for user_info in ranks["ranking"]:
            supporter = user_info.get("user", {}).get("is_supporter", False)
            rank      = user_info["global_rank"]

            i = bisect.bisect(brackets, rank)
            if supporter:
                samples[i].inc_yes()
            else:
                samples[i].inc_no()

            overview[i] = overview.get(i, 0) + 1

        return ranks["cursor"], overview
    except:
        if ranks.get("error", None) == 'Too Many Attempts.':
            print("ratelimited")
            time.sleep(60)
        else:
            print("failed to request ranking", cursor)
            traceback.print_exc()
            print(ranks)

        return 0, overview

def get_none(a, k, d=None):
    if a is None:
        return d
    x = a.get(k, None)
    if x is None:
        return d
    return x

def draw():
    uids = list(numpy.random.randint(0, MAX_ID, size=BATCH))

    user_infos = get_users(uids)
    overview = {}
    try:    
        num = 0

        for user_info in user_infos["users"]:
            if not user_info:
                print("banned")
                continue

            try:
                supporter = user_info.get("is_supporter", False)

                stats = get_none(user_info, "statistics_rulesets")
                osu   = get_none(stats, "osu")
                rank  = get_none(osu, "global_rank", d=MAX_ID - 1)

                if rank < PRELOAD:
                    continue

                i = bisect.bisect(brackets, rank)
                if supporter:
                    samples[i].inc_yes()
                else:
                    samples[i].inc_no()

                overview[i] = overview.get(i, 0) + 1
                
                num += 1
            except:
                traceback.print_exc()
                print("failed to sample")
                print(user_info)

        print(num, "/", BATCH)

        return num, overview
    except:
        if user_infos.get("error", None) == 'Too Many Attempts.':
            print("ratelimited")
            time.sleep(60)
        else:
            print("failed to request", uids[:3], "...")
            traceback.print_exc()
            print(user_infos)

        return 0, overview

def dict_add(a, b):
    for k, v in b.items():
        a[k] = a.get(k, 0) + v


SAMPLES = "samples.json"
if not os.path.exists("samples.json"):
  try:
      cursor = {"page": 1}

      i = 0
      i_ = 0
      overview = {}

      while cursor:
          if i - i_ > 1000:
              print(overview)
              overview = {}
              i_ = i

          cursor, o_ = draw_ranking(cursor=cursor)
          i += 50
          dict_add(overview, o_)
          time.sleep(RATELIMIT / 60 / 50) # wrong, but we're not getting ratelimited ¯\_(ツ)_/¯

      i = 0
      i_ = 0
      overview = {}

      while i < MAXITER:
          if i - i_ > 1000:
              print("iter", i, "of", MAXITER)
              print(overview)
              overview = {}
              i_ = i

          done = True
          for s in samples:
              done &= s.done()

          if done:
              break

          di, o_ = draw()
          dict_add(overview, o_)
          i += di
          time.sleep(RATELIMIT / 60 / 50) # still wrong, and we're getting ratelimited ¯\_(ツ)_/¯
  except:
      traceback.print_exc()
  finally:
      with open("samples.json", mode="w") as f:
          json.dump(_json(), f)
      ...

with open("samples.json", mode="r") as f:
    a = json.load(f)[1]

prev = 0
supporters = 0
for bracket, sample1 in zip(brackets, a):
    yes = sample1["yes"]
    tot = sample1["tot"]

    r = yes / tot
    total = bracket - prev

    extrapolated = int(total * r)
    supporters += extrapolated

    print(f"sampled {yes:<6}/  {tot:<9} from {prev:<9} until {bracket:<9}, extrapolating to {extrapolated:<6} ({r*100:.2f}%)")

    prev = bracket

money_low  = 2.166 * supporters
money_high = 4 * supporters

print("total extrapolated supporters", supporters)
print(f"monthly acquired moneys lies between {money_low:.0f} and {money_high:.0f}")
print(f"yearly acquired moneys lies between {12 * money_low:.0f} and {12 * money_high:.0f}")

NUMBR = 41.2 / 26
MINS_YEAR = 365 * 24 * 60

NUMBR_Y = NUMBR / MINS_YEAR

EXPEND_PER_Y = 1 / NUMBR * MINS_YEAR

print()
print(f"peppy loses {int(EXPEND_PER_Y)} moneys per year")

print()
print(f"this number of supporters yields between {12 * NUMBR * money_low:.0f} and {12 * NUMBR * money_high:.0f} minutes per year")
print(f"or between {12 * NUMBR_Y * money_low:.2f} and {12 * NUMBR_Y * money_high:.2f} years per year")
