#!/usr/bin/env python3
"""Gerador de EPG (XMLTV) e otimizador de logótipos para TiviMate.

- Lê a lista M3U, identifica os canais (prioridade aos canais portugueses).
- Junta várias fontes XMLTV abertas e escolhe, por canal, a que tem mais
  programação nos próximos 7 dias -> epg.xml
- Procura logótipos HD transparentes (tv-logo/tv-logos e iptv-org) e
  coloca-os no epg.xml e nas tags tvg-logo da lista.
- Reescreve tvg-id / tvg-logo na lista para corresponderem ao epg.xml.

Só usa a biblioteca padrão do Python (3.9+).
"""
import argparse
import csv
import datetime as dt
import gzip
import io
import json
import os
import re
import sys
import unicodedata
import urllib.request
import xml.etree.ElementTree as ET

# --------------------------------------------------------------------------
# Configuração
# --------------------------------------------------------------------------

DAYS = 7
PAST_HOURS = 6  # mantém um pouco de passado para o "catch-up" do TiviMate

# (nome, url, tipo) – tipo "meo" = IDs são códigos MEO (ver MEO_CODES)
EPG_SOURCES = [
    ("open-epg-meo", "https://www.open-epg.com/files/portugal2.xml", "meo"),
    ("open-epg-nos", "https://www.open-epg.com/files/portugal1.xml", "names"),
    ("open-epg-3", "https://www.open-epg.com/files/portugal3.xml", "names"),
    ("epgshare01", "https://epgshare01.online/epgshare01/epg_ripper_PT1.xml.gz", "names"),
]

# Grupos da lista a tratar (regex sobre group-title). Os grupos 24/7 e VOD
# não têm programação real, por isso ficam de fora.
SCOPE_GROUPS = r"^Portugal( HEVC)?$"
# Canais de outros grupos cujo nome termina em " PT" também são tratados.
SCOPE_NAME_SUFFIX = r"\sPT\s*$"

TV_LOGOS_API = "https://api.github.com/repos/tv-logo/tv-logos/contents/countries/portugal"
TV_LOGOS_RAW = "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/portugal/"
IPTV_ORG_CHANNELS = "https://iptv-org.github.io/api/channels.json"
IPTV_ORG_LOGOS = "https://iptv-org.github.io/api/logos.json"

# Códigos usados pela fonte MEO -> nome do canal
MEO_CODES = {
    "RTP1": "RTP 1", "RTP2": "RTP 2", "RTPN": "RTP Notícias", "RTPA": "RTP África",
    "RTPACR": "RTP Açores", "RTPMA": "RTP Madeira", "RTPM": "RTP Memória",
    "SIC": "SIC", "SICN": "SIC Notícias", "SICR": "SIC Radical", "SICM": "SIC Mulher",
    "SICC": "SIC Caras", "SICK": "SIC K", "SICNOV": "SIC Novelas",
    "TVI": "TVI", "TVIR": "TVI Reality", "VMAISTVI": "V+TVI", "CNNPT": "CNN Portugal",
    "CMTV": "CMTV", "PORTO": "Porto Canal", "ARTV": "ARTV", "C11": "Canal 11",
    "ABOLA": "A Bola TV", "SCPHD": "Sporting TV", "SMAISHD": "S+",
    "SPT1HD": "SPORT TV1", "SPT2HD": "SPORT TV2", "SPT3HD": "SPORT TV3",
    "SPT4HD": "SPORT TV4", "SPT5HD": "SPORT TV5", "SPT6HD": "SPORT TV6",
    "SPT7HD": "SPORT TV7", "SPTVHD": "SPORT TV+",
    "DAZN1": "DAZN 1", "DAZN2": "DAZN 2", "DAZN3": "DAZN 3", "DAZN4": "DAZN 4", "DAZN5": "DAZN 5",
    "EURHD": "Eurosport 1", "EURS2HD": "Eurosport 2",
    "TVCTOPH": "TVCine TOP", "TVCEDIH": "TVCine EDITION", "TVCEMOH": "TVCine EMOTION",
    "TVCACTH": "TVCine ACTION",
    "AXNHD": "AXN", "AXNMHD": "AXN Movies", "AXWHD": "AXN White",
    "AMCHD": "AMC", "AMCBRE": "AMC Break", "AMCCRI": "AMC Crime",
    "STARCHA": "Star Channel", "STARCOM": "Star Comedy", "STARCRI": "Star Crime",
    "STARLIF": "Star Life", "STARMOV": "Star Movies",
    "HOLHD": "Canal Hollywood", "CINEHD": "Cinemundo", "SYFHD": "Syfy",
    "HISTHD": "Canal História", "ODISSHD": "Odisseia", "NGHD": "National Geographic",
    "WILDHD": "National Geographic WILD", "DISCVHD": "Discovery",
    "ID": "ID Investigation Discovery", "TLC": "TLC", "HGTV": "HGTV",
    "24KTHD": "24Kitchen", "CASACOZ": "Casa e Cozinha", "TRAHD": "Travel Channel",
    "TRAXP": "TravelXP", "CAÇAPHD": "Caça e Pesca", "CAÇAVHD": "Caça Vision",
    "DISNY": "Disney Channel", "DISNYJ": "Disney Junior", "PANDA": "Canal Panda",
    "PANDAK": "Panda Kids", "CART": "Cartoon Network", "CNITO": "Cartoonito",
    "NICKELO": "Nickelodeon", "NICKJR": "Nick Jr.", "BABYT": "Baby TV",
    "LOLLY": "Lolly Kids", "GAMET": "GameToon", "KANUCA": "Kanuca TV",
    "C180": "Canal 180", "QHD": "Canal Q", "GALERIA": "Canal Galeria",
    "AZORES": "Azores TV", "KURIAKO": "Kuriakos TV", "CNOVA": "Canção Nova",
    "LVTVHD": "Localvisão TV", "CONTALA": "Conta Lá", "ALMALUS": "Alma Lusa",
    "BOMSOM": "BOMSOM TV", "NEWSNOW": "NewsNow", "TCV": "TCV Internacional",
    "GLOB": "Globo", "REC HD": "Record", "MEZZO": "Mezzo", "MEZHD": "Mezzo Live",
    "ICOHD": "Stingray iConcerts", "FTVHD": "FTV", "DOGTVHD": "DOGTV",
    "ONETORO": "OneToro TV", "WSPORT": "W-Sport", "DIZI": "Dizi", "VINTV": "VinTV",
    "UNIFE": "Unifé TV", "AFRO": "Afro Music Channel", "EURN": "Euronews",
    "MCMTHD": "MCM Top", "MCM P": "MCM Pop", "TVE24HD": "TVE 24h",
    "NHKHD": "NHK World TV", "CNBC": "CNBC", "CNN": "CNN", "BBC W": "BBC World News",
    "FR24F": "France 24 (F)", "FR24I": "France 24 (I)", "TPA": "TPA Internacional",
}

# Nome normalizado na lista -> nome normalizado nas fontes EPG / logótipos
ALIASES = {
    "e": "eentertainment", "vmais": "vmaistvi", "hollywood": "canalhollywood",
    "historia": "canalhistoria", "discoverychannel": "discovery",
    "natgeowild": "nationalgeographicwild", "nationalgeo": "nationalgeographic",
    "idinvestigation": "idinvestigationdiscovery",
    "investigationdiscovery": "idinvestigationdiscovery",
    "sickids": "sick", "star": "starchannel", "mtv": "mtvportugal",
    "tvglobo": "globo", "tvrecord": "record", "fashiontv": "ftv",
    "homegardentv": "hgtv", "iconcerts": "stingrayiconcerts",
    "afromusic": "afromusicchannel", "motorvisiontv": "motorvision",
    "onetoro": "onetorotv", "nhkworldjapan": "nhkworldtv", "cnbceurope": "cnbc",
    "tcvinternational": "tcvinternacional", "now": "newsnow", "dizichannel": "dizi",
    "artvparlamento": "artv", "btv": "btv1", "canalsmais": "smais",
    "cnn": "cnnportugal", "tpa": "tpainternacional",
}

STRIP_TOKENS = {"fhd", "hd", "uhd", "sd", "hevc", "h265", "4k", "vip", "pt",
                "backup", "mobile", "upscale", "baixa", "internet"}

UA = {"User-Agent": "Mozilla/5.0 (epg-generator; +https://github.com/iptv-org)"}


# --------------------------------------------------------------------------
# Utilitários
# --------------------------------------------------------------------------

def log(msg):
    print(msg, flush=True)


def fetch(url, headers=None, timeout=120):
    h = dict(UA)
    h.update(headers or {})
    for attempt in range(3):
        try:
            with urllib.request.urlopen(urllib.request.Request(url, headers=h), timeout=timeout) as r:
                data = r.read()
            if data[:2] == b"\x1f\x8b":
                data = gzip.decompress(data)
            return data
        except Exception as e:  # noqa: BLE001
            log(f"  ! {url} (tentativa {attempt + 1}): {e}")
    return None


def ascii_fold(s):
    return unicodedata.normalize("NFKD", s).encode("ascii", "ignore").decode()


def norm(name, aliases=True):
    """Chave de comparação: sem acentos, qualidade, sufixos e pontuação.

    Os ALIASES só se aplicam aos nomes da lista/logótipos; os nomes das fontes
    EPG ficam como estão, para "CNN" não ser confundido com "CNN Portugal".
    """
    s = ascii_fold(name).lower()
    s = re.sub(r"\.pt$", "", s)
    s = re.sub(r"\(.*?\)|\[.*?\]", " ", s)
    s = s.replace("4:3", " ").replace("+", " mais ").replace("&", " ")
    toks = [t for t in re.findall(r"[a-z0-9]+", s) if t not in STRIP_TOKENS]
    key = "".join(toks)
    return ALIASES.get(key, key) if aliases else key


def pretty(name):
    name = re.sub(r"\.pt$", "", name).strip()
    return re.sub(r"\s+(HD|FHD)$", "", name, flags=re.I)


def make_id(name):
    s = re.sub(r"[^A-Za-z0-9+!]+", ".", ascii_fold(pretty(name))).strip(".")
    return f"{s}.pt"


def parse_time(s):
    try:
        return dt.datetime.strptime(s.strip()[:20], "%Y%m%d%H%M%S %z")
    except ValueError:
        return dt.datetime.strptime(s.strip()[:14], "%Y%m%d%H%M%S").replace(tzinfo=dt.timezone.utc)


# --------------------------------------------------------------------------
# M3U
# --------------------------------------------------------------------------

ATTR_RE = r'{}="([^"]*)"'


def get_attr(line, attr):
    m = re.search(ATTR_RE.format(re.escape(attr)), line)
    return m.group(1) if m else ""


def set_attr(line, attr, value):
    pat = re.compile(ATTR_RE.format(re.escape(attr)))
    new = f'{attr}="{value}"'
    if pat.search(line):
        return pat.sub(lambda _: new, line, count=1)
    return re.sub(r"^(#EXT(?:INF:-?\d+|M3U))", lambda m: f"{m.group(1)} {new}", line, count=1)


def read_m3u(path):
    with open(path, encoding="utf-8", errors="replace", newline="") as f:
        raw = f.read()
    # divide só em "\n" para manter os finais de linha (\r\n ou \n) tal como estão
    return raw.split("\n")


def scoped_channels(lines):
    """Devolve [(índice da linha EXTINF, nome, grupo)] dos canais a tratar."""
    group_re, suffix_re = re.compile(SCOPE_GROUPS), re.compile(SCOPE_NAME_SUFFIX)
    out = []
    for i, line in enumerate(lines):
        if not line.startswith("#EXTINF"):
            continue
        url = next((l for l in lines[i + 1:i + 4] if l.strip() and not l.startswith("#")), "")
        if "/movie/" in url or "/series/" in url:
            continue
        name = line.rsplit(",", 1)[-1].strip()
        group = get_attr(line, "group-title")
        if name.startswith(("#", "=")):
            continue
        if group_re.search(group) or ("24-7" not in group and "VOD" not in group and suffix_re.search(name)):
            out.append((i, name, group))
    return out


# --------------------------------------------------------------------------
# EPG
# --------------------------------------------------------------------------

def load_epg_sources(wanted_keys, start, end):
    """Devolve {key: [(fonte, nome_bonito, [programmes])]} para as chaves pedidas."""
    found = {}
    for src, url, kind in EPG_SOURCES:
        log(f"- EPG {src}: {url}")
        data = fetch(url)
        if not data:
            continue
        try:
            root = ET.parse(io.BytesIO(data)).getroot()
        except ET.ParseError as e:
            log(f"  ! XML inválido: {e}")
            continue
        chan_key = {}
        for ch in root.iter("channel"):
            cid = ch.get("id", "")
            if kind == "meo":
                label = MEO_CODES.get(re.sub(r"\.pt$", "", cid))
                if not label:
                    continue
            else:
                label = ch.findtext("display-name") or cid
            key = norm(label, aliases=False)
            if key in wanted_keys:
                chan_key[cid] = (key, label)
        progs = {}
        for p in root.iter("programme"):
            cid = p.get("channel")
            if cid not in chan_key:
                continue
            try:
                if parse_time(p.get("stop")) < start or parse_time(p.get("start")) > end:
                    continue
            except (TypeError, ValueError):
                continue
            progs.setdefault(cid, []).append(p)
        n = 0
        for cid, (key, label) in chan_key.items():
            if progs.get(cid):
                found.setdefault(key, []).append((src, label, progs[cid]))
                n += 1
        log(f"  {n} canais com programação")
    return found


def best_source(cands, now):
    """Escolhe a fonte com mais programação futura (e, em empate, a primeira)."""
    def score(c):
        progs = c[2]
        last = max(parse_time(p.get("stop")) for p in progs)
        future = sum(1 for p in progs if parse_time(p.get("stop")) > now)
        return (last, future)
    return max(cands, key=score)


# --------------------------------------------------------------------------
# Logótipos
# --------------------------------------------------------------------------

def load_logos():
    """Devolve {key: url}. Prioridade: tv-logo/tv-logos > iptv-org (PNG, maior)."""
    logos = {}

    headers = {"Accept": "application/vnd.github+json"}
    if os.environ.get("GITHUB_TOKEN"):
        headers["Authorization"] = f"Bearer {os.environ['GITHUB_TOKEN']}"
    data = fetch(TV_LOGOS_API, headers)
    tvlogos = {}
    if data:
        for item in json.loads(data):
            fname = item.get("name", "")
            if not fname.endswith(".png") or "-icon" in fname:
                continue
            stem = re.sub(r"-pt$", "", fname[:-4])
            key = norm(stem.replace("-", " "))
            is_hd = bool(re.search(r"(^|-)hd(-|$)", stem))
            # a versão sem "HD" no logótipo é a mais limpa; usa a HD só se for a única
            if key not in tvlogos or (tvlogos[key][1] and not is_hd):
                tvlogos[key] = (TV_LOGOS_RAW + fname, is_hd)
    log(f"- tv-logo/tv-logos: {len(tvlogos)} logótipos PT")

    iptv = {}
    chans, lgs = fetch(IPTV_ORG_CHANNELS), fetch(IPTV_ORG_LOGOS)
    if chans and lgs:
        best = {}
        for l in json.loads(lgs):
            if l.get("format") != "PNG" or l.get("feed"):
                continue
            cur = best.get(l["channel"])
            if not cur or (l.get("width") or 0) > (cur.get("width") or 0):
                best[l["channel"]] = l
        # canais PT primeiro, para ganharem a outros países com o mesmo nome
        for c in sorted(json.loads(chans), key=lambda c: c.get("country") != "PT"):
            if c["id"] not in best or c.get("closed"):
                continue
            for n in [c["name"], *c.get("alt_names", [])]:
                iptv.setdefault(norm(n), best[c["id"]]["url"])
    log(f"- iptv-org: {len(iptv)} nomes com logótipo PNG")

    logos.update(iptv)
    logos.update({k: v[0] for k, v in tvlogos.items()})
    return logos


# --------------------------------------------------------------------------
# Main
# --------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--m3u", default="lista.m3u")
    ap.add_argument("--epg", default="epg.xml")
    ap.add_argument("--report", default="canais.csv")
    ap.add_argument("--epg-url", default=os.environ.get("EPG_URL", ""),
                    help="URL pública do epg.xml, colocada em url-tvg no cabeçalho da lista")
    args = ap.parse_args()

    now = dt.datetime.now(dt.timezone.utc)
    start, end = now - dt.timedelta(hours=PAST_HOURS), now + dt.timedelta(days=DAYS)

    lines = read_m3u(args.m3u)
    channels = scoped_channels(lines)
    log(f"{len(channels)} canais a tratar em {args.m3u}")
    keys = {norm(name) for _, name, _ in channels}

    epg = load_epg_sources(keys, start, end)
    if not epg:
        sys.exit("Nenhuma fonte EPG respondeu – epg.xml não foi alterado.")
    logos = load_logos()

    # Escolhe a fonte de cada canal e gera o XMLTV
    tv = ET.Element("tv", {"generator-info-name": "generate_epg.py",
                           "source-info-name": ", ".join(s for s, _, _ in EPG_SOURCES)})
    # o ID vem do nome MEO quando existe, para não mudar de dia para dia
    meo_names = {norm(n, aliases=False): n for n in MEO_CODES.values()}
    chosen = {}
    for key in sorted(epg):
        src, _, progs = best_source(epg[key], now)
        label = meo_names.get(key, epg[key][0][1])
        cid = make_id(label)
        chosen[key] = (cid, src, progs)
        ch = ET.SubElement(tv, "channel", id=cid)
        ET.SubElement(ch, "display-name", lang="pt").text = pretty(label)
        if key in logos:
            ET.SubElement(ch, "icon", src=logos[key])
    for key in sorted(epg):
        cid, _, progs = chosen[key]
        for p in sorted(progs, key=lambda p: p.get("start")):
            p.set("channel", cid)
            for icon in p.findall("icon"):  # ícones de programa partidos da fonte NOS
                if not icon.get("src", "").startswith("http") or icon.get("src", "").endswith(".pt"):
                    p.remove(icon)
            tv.append(p)
    ET.indent(tv, space="  ")
    with open(args.epg, "wb") as f:
        f.write(b'<?xml version="1.0" encoding="UTF-8"?>\n')
        f.write(ET.tostring(tv, encoding="utf-8"))
    log(f"{args.epg}: {len(chosen)} canais, {sum(1 for _ in tv.iter('programme'))} programas")

    # Atualiza a lista
    rows, with_epg, with_logo = [], 0, 0
    for i, name, group in channels:
        key = norm(name)
        line = lines[i]
        tvg_id, src, _ = chosen.get(key, ("", "", None))
        if tvg_id:
            line = set_attr(line, "tvg-id", tvg_id)
            with_epg += 1
        if key in logos:
            line = set_attr(line, "tvg-logo", logos[key])
            with_logo += 1
        lines[i] = line
        rows.append([group, name, get_attr(line, "tvg-id"), src or "-", "sim" if key in logos else "não"])
    if args.epg_url and lines and lines[0].startswith("#EXTM3U"):
        lines[0] = set_attr(set_attr(lines[0], "url-tvg", args.epg_url), "x-tvg-url", args.epg_url)
    with open(args.m3u, "w", encoding="utf-8", newline="") as f:
        f.write("\n".join(lines))
    log(f"{args.m3u}: {with_epg}/{len(channels)} com EPG, {with_logo}/{len(channels)} com logótipo HD")

    if args.report:
        with open(args.report, "w", encoding="utf-8", newline="") as f:
            w = csv.writer(f)
            w.writerow(["grupo", "canal", "tvg-id", "fonte_epg", "logo_hd"])
            w.writerows(sorted(rows))
        log(f"{args.report}: relatório por canal")


if __name__ == "__main__":
    main()
