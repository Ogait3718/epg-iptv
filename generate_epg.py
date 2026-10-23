#!/usr/bin/env python3
"""Gerador de EPG (XMLTV) e otimizador de logótipos para TiviMate.

- Lê a lista M3U e identifica os canais de cada país configurado em COUNTRIES
  (Portugal, Bélgica, Brasil, França, Alemanha e Reino Unido).
- Junta várias fontes XMLTV abertas desse país e escolhe, por canal, a que
  tem mais programação nos próximos 7 dias -> epg.xml
- Procura logótipos HD transparentes (tv-logo/tv-logos e iptv-org) e
  coloca-os no epg.xml e nas tags tvg-logo da lista.
- Reescreve tvg-id / tvg-logo na lista para corresponderem ao epg.xml.
- Acrescenta ao epg.xml os nomes exatos do fornecedor como <display-name>,
  para o TiviMate (Xtream Codes) associar a programação pelo nome.

Só usa a biblioteca padrão do Python (3.9+).
"""
import argparse
import copy
import csv
import datetime as dt
import gzip
import html
import io
import json
import os
import re
import sys
import unicodedata
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET

# --------------------------------------------------------------------------
# Configuração
# --------------------------------------------------------------------------

DAYS = 7
PAST_HOURS = 6  # mantém um pouco de passado para o "catch-up" do TiviMate

OPEN_EPG = "https://www.open-epg.com/files/{}.xml"
EPGSHARE = "https://epgshare01.online/epgshare01/epg_ripper_{}.xml.gz"

# Por país:
#   groups  – regex sobre group-title (os grupos 24/7 e VOD ficam de fora)
#   suffix  – canais de outros grupos cujo nome termina neste código também entram
#   epg     – fontes XMLTV (nome, url, tipo); tipo "meo" = IDs são códigos MEO
#   logos   – pasta em tv-logo/tv-logos/countries; iptv – código de país no iptv-org
COUNTRIES = {
    "PT": {
        "groups": r"^Portugal( HEVC)?$", "suffix": "PT", "lang": "pt",
        "logos": "portugal", "iptv": "PT",
        "epg": [
            ("open-epg-meo", OPEN_EPG.format("portugal2"), "meo"),
            ("open-epg-nos", OPEN_EPG.format("portugal1"), "names"),
            ("open-epg-3", OPEN_EPG.format("portugal3"), "names"),
            ("epgshare01", EPGSHARE.format("PT1"), "names"),
        ],
    },
    "BE": {
        "groups": r"^Belgium$", "suffix": "BE", "lang": "fr",
        "logos": "belgium", "iptv": "BE",
        "epg": [
            ("open-epg-be2", OPEN_EPG.format("belgium2"), "names"),
            ("open-epg-be1", OPEN_EPG.format("belgium1"), "names"),
            ("epgshare01-be", EPGSHARE.format("BE2"), "names"),
        ],
    },
    "BR": {
        "groups": r"^Brazil$", "suffix": "BR", "lang": "pt",
        "logos": "brazil", "iptv": "BR",
        "epg": [
            ("open-epg-br1", OPEN_EPG.format("brazil1"), "names"),
            ("open-epg-br3", OPEN_EPG.format("brazil3"), "names"),
            ("open-epg-br2", OPEN_EPG.format("brazil2"), "names"),
            ("epgshare01-br1", EPGSHARE.format("BR1"), "names"),
            ("epgshare01-br2", EPGSHARE.format("BR2"), "names"),
        ],
    },
    "FR": {
        "groups": r"^France( HEVC)?$", "suffix": "FR", "lang": "fr",
        "logos": "france", "iptv": "FR",
        "epg": [
            ("open-epg-fr1", OPEN_EPG.format("france1"), "names"),
            ("open-epg-fr2", OPEN_EPG.format("france2"), "names"),
            ("open-epg-fr3", OPEN_EPG.format("france3"), "names"),
            ("epgshare01-fr", EPGSHARE.format("FR1"), "names"),
        ],
    },
    "DE": {
        "groups": r"^Germany( HEVC| VIP)?$", "suffix": "DE", "lang": "de",
        "logos": "germany", "iptv": "DE",
        "epg": [
            ("open-epg-de3", OPEN_EPG.format("germany3"), "names"),
            ("open-epg-de1", OPEN_EPG.format("germany1"), "names"),
            ("epgshare01-de", EPGSHARE.format("DE1"), "names"),
        ],
    },
    "UK": {
        "groups": r"^(United Kingdom( VIP)?|Script UK)$", "suffix": "UK", "lang": "en",
        "logos": "united-kingdom", "iptv": "UK",
        "epg": [
            ("open-epg-uk3", OPEN_EPG.format("unitedkingdom3"), "names"),
            ("open-epg-uk1", OPEN_EPG.format("unitedkingdom1"), "names"),
            ("open-epg-uk2", OPEN_EPG.format("unitedkingdom2"), "names"),
            ("epgshare01-uk", EPGSHARE.format("UK1"), "names"),
        ],
    },
}
SKIP_GROUPS = r"24-7|VOD|XXX|Adult"
SKIP_NAMES = r"24/7"

# Grupos genéricos de desporto/eventos ("VIP Sports", "Events", "PPV VIP Sports"...).
# Aqui o país só se sabe pelo nome; o canal só entra se tiver exatamente um
# marcador de um dos nossos países (ex.: "S Sports Football FHD UK VIP SPORTS",
# "UK | ...", "Eleven Sports 3 (Belgium FR)"). Sem marcador ou de outro país
# (US, ES, IT, AT...) é descartado.
SPORT_GROUPS = r"(?i)vip\s*sports?|\bevents?\b"
SPORT_COUNTRY_WORDS = {
    "PT": r"portugal", "BE": r"belgi(um|que|e)", "BR": r"bra[sz]il",
    "FR": r"france", "DE": r"germany|deutschland", "UK": r"united kingdom|england|scotland",
}
SPORT_CODES = {"PT": "PT", "BE": "BE", "BR": "BR", "FR": "FR", "DE": "DE", "UK": "UK", "GB": "UK"}
# Marcas aceites mesmo sem código. "Sky Sports" (plural) é só do Reino Unido;
# "TNT Sports" também existe no Brasil, mas nestes grupos sem código é o do UK.
SPORT_BRANDS = {"UK": r"^(Sky|TNT) Sports\b"}

TV_LOGOS_API = "https://api.github.com/repos/tv-logo/tv-logos/contents/countries/{}"
TV_LOGOS_RAW = "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/{}/"
IPTV_ORG_CHANNELS = "https://iptv-org.github.io/api/channels.json"
IPTV_ORG_LOGOS = "https://iptv-org.github.io/api/logos.json"

# Prioridade dos logótipos (o primeiro que existir ganha):
#   1. OFFICIAL_LOGOS – ficheiros oficiais das próprias emissoras
#   2. iptv-org com URL num domínio oficial de emissora (apanha rebrandings
#      novos sem mexer no script, ex.: RTP 2026)
#   3. tv-logo/tv-logos (PNG transparente 512 px)
#   4. restantes logótipos PNG do iptv-org (o maior)
OFFICIAL_LOGO_HOSTS = (
    r"(^|\.)(rtp\.pt|iol\.pt|sic\.pt|impresa\.pt|bbci?\.co\.uk|itv\.com|channel[45]\.com|sky\.com"
    r"|rtbf\.be|vrt\.be|dpgmedia\.(be|net)|globo\.com|glbimg\.com|sbt\.com\.br|r7\.com"
    r"|tf1\.fr|francetv\.fr|france\.tv|cnews\.fr|canalplus\.com|m6\.fr|arte\.tv"
    r"|ard\.de|daserste\.de|zdf\.de|rtl\.de|prosiebensat1\.(de|com)|br\.de|wdr\.de|ndr\.de|mdr\.de|swr\.de)$"
)
RTP_CDN = "https://cdn-images.rtp.pt/common/img/channels/logos/color/horizontal/{}_2026.png"
IOL_CDN = "https://cdn.iol.pt/img/logostvi/branco/{}.png"  # versão branca, para fundo escuro
OFFICIAL_LOGOS = {
    "PT": {
        "RTP 1": RTP_CDN.format("rtp1"), "RTP 2": RTP_CDN.format("rtp2"),
        "RTP Notícias": RTP_CDN.format("rtpnoticias"), "RTP 3": RTP_CDN.format("rtpnoticias"),
        "RTP Memória": RTP_CDN.format("rtpmemoria"), "RTP África": RTP_CDN.format("rtpafrica"),
        "RTP Açores": RTP_CDN.format("rtpacores"), "RTP Madeira": RTP_CDN.format("rtpmadeira"),
        "TVI Reality": IOL_CDN.format("tvireality"), "TVI Ficção": IOL_CDN.format("tvificcao"),
        "TVI Internacional": IOL_CDN.format("tviinternacional"), "TVI África": IOL_CDN.format("tviafrica"),
        "V+TVI": IOL_CDN.format("vmaistvi"),
    },
}

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
ALIASES_PT = {
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

# Outros países: nome na lista -> nome na fonte EPG (normalizados no arranque).
# Só canais que são de certeza o mesmo; variantes regionais ou "+1" sem
# equivalente na fonte ficam de fora para não mostrar programação errada.
NAME_ALIASES = {
    "BE": {
        "Animal Planet": "Animal Pl HD", "Crime + Investigation": "Crime & Investigation Network",
        "DAZN Pro Leagues 1": "DAZN Pro League 1", "Discovery Science": "Disc Science",
        "Eurosport 2": "Eurosp2 HD N", "QU4TRE": "Quatre HD", "RTBF Tipik": "RTBF Tipik TV HD",
        "RTL Luxembourg": "RTL Lëtzebuerg", "TVL": "TV Lux HD", "VTM 1": "VTM HD",
        "Nat Geo": "National Geographic HD", "E! Entertainment": "E! HD N",
    },
    "BR": {
        "Band Sport": "BandSports HD", "CNN Internacional": "CNN INTERNATIONAL",
        "ESPN Brazil": "ESPN Brasil", "GLOBO BAHIA": "Globo TV Bahia",
        "GLOBO RBS PORTO ALEGRE": "RBS TV Porto Alegre HD", "GLOBO TV TRIBUNA SANTOS": "Globo TV Tribuna",
        "GLOBO TV VERDES MARES FORTALEZA": "TV Verdes Mares HD", "TV Globo": "Globo HD",
        "MegaPix TV": "Megapix HD", "Premier 2": "Premiere 2", "Premier 3": "PREMIERE 3 HD",
        "Premier 4": "Premiere 4", "Premier 5": "Premiere HD 5", "Premier 7": "Premiere 7 HD",
        "Record RS": "Record TV RS", "Record Ba": "Record TV Bahia", "Record MG": "Record TV Minas HD",
        "Record RJ": "Record TV Rio HD", "Record SP": "Record TV HD", "SBT SP": "SBT HD",
        "SBT Cidade Verde": "TV Cidade Verde HD", "SBT TV CIDADE VERDE PIAUI": "TV Cidade Verde HD",
        "SBT TV Jornal": "TV Jornal HD", "SporTV 1": "SporTV HD",
        "TC Action": "Telecine Action HD", "TC Cult": "Telecine Cult HD",
        "TC Fun": "Telecine Fun HD", "TC Pipoca": "Telecine Pipoca HD",
        "Globo MINAS": "Globo Belo Horizonte HD", "MTV": "MTV Brasil",
        "NatGeo": "National Geographic", "ID Discovery": "ID HD",
        "Discovery H&H": "Discovery Home & Health HD", "DISCOVERY TLC": "TLC HD",
        "Warner TV": "Warner Channel HD",
    },
    "FR": {
        "C-STAR HITS": "CSTAR Hits France", "Cine Club": "Ciné+ Club",
        "Discovery": "Discovery Channel", "DISCOVERY INVES": "Discovery Investigation",
        "Investigation Discovery": "Discovery Investigation", "F1 SERIES & FILMS": "TF1 Séries Films",
        "Franced 2": "France 2", "Franced 3": "France 3",
        "La Chaîne Normande TV": "La Chaîne normande", "L'Equipe 21": "L'Equipe",
        "L'EQUIPE TV": "L'Equipe", "LCP": "LCP-AN-PS", "LUCKY JACK TV": "Lucky Jack",
        "NATIONAL GEO CHANNEL": "National Geographic", "Nickelodeon 4 Teen": "Nickelodéon Teen",
        "NICK JUNIOR": "Nickelodeon Junior", "OLYMPIA": "Olympia TV",
        "Planète+ Crime+Investigation": "Planète+ Crime Investigation",
        "PLANETE+ CI": "Planète+ Crime Investigation",
        "RMC SPORT 1 ACCESS": "RMC Sport Access 1", "RMC SPORTS 1": "RMC Sport 1",
        "RMC SPORTS 2": "RMC Sport 2", "SCIENCES&VIE": "Science & Vie TV",
        "Tele Melody": "Melody", "Tele Novelas": "Novelas TV", "Trace CARRIBEAN": "Trace Caribbean",
        "TV5 Monde Europe": "TV5MONDE", "TV8 Mont+Blanc": "8 Mont-Blanc", "USHUAIA": "Ushuaïa TV",
        "Numéro 23": "RMC Story", "Golf Channel": "Golf+", "Ciné Polar": "Polar+",
        "DAZN 1": "DAZN",
    },
    "DE": {
        "Auto Motor Sport TV": "auto motor und sport", "CRIME INVESTIGATION": "Crime+Investigation",
        "Crime Investigation+": "Crime+Investigation", "DAZN | Eurosport 1": "Eurosport 1",
        "DAZN | Eurosport 2": "Eurosport 2", "DAZN | SPORTDIGITAL FUSSBALL": "SPORTDIGITAL FUSSBALL",
        "Sportdigital": "Sportdigital1+", "DAZN | Red Bull TV": "Red Bull TV",
        "Fix und Foxi": "Fix & Foxi", "Heimatikanal": "Heimatkanal", "KINO WELT": "KinoweltTV",
        "MDR Sachsen": "MDR-Fernsehen Sachsen", "PRO7 MAXX": "ProSieben MAXX", "Puls 8": "PULS acht",
        "RTL II": "RTLZWEI", "RTL 2": "RTLZWEI", "RTL Nitro": "NITRO", "RTL TELEVISION": "RTL",
        "Servus TV": "Servus TV Österreich", "SERVUSTV": "Servus TV Österreich",
        "Sky Cinema Premieren": "Sky Cinema Premiere", "Sky PREMIEREN": "Sky Cinema Premiere",
        "Sky Dokumentaries": "Sky Documentaries", "TOGGO plus von Super RTL": "TOGGO plus",
        "Warner Comedy": "Warner TV Comedy", "Warner Film": "Warner TV Film",
        "Warner Serie": "Warner TV Serie", "Warner TV Series": "Warner TV Serie",
        "WDR Aachen": "WDR Fernsehen Aachen", "WDR Duisburg": "WDR Fernsehen Duisburg",
        "WDR Wuppertal": "WDR Fernsehen Wuppertal", "Wedo Movies": "wedotv Movies",
        "Mainfranken Würzburg TV": "TV Mainfranken", "SWR": "SWR/SR",
        "AXN": "AXN Black", "History": "The HISTORY Channel", "Nickelodeon": "nick",
        "Sky 1": "Sky One", "GEO": "GEO Television", "Silverline Movie Channel": "Silverline",
        "ORF eins": "ORF 1", "SR": "SR Fernsehen",
        **{f"BUNDESLIGA {n}": f"Sky Sport Bundesliga {n}" for n in range(1, 11)},
    },
    "UK": {
        "Alibi": "UAndalibi HD", "Dave": "UAndDave", "Dave ja vu": "UAndDave Ja Vu",
        "Drama": "UAndDrama", "Eden": "UAndEden", "Eden +1": "U and Eden+1",
        "GOLD +1": "U and GOLD+1", "YESTERDAY": "UAndYesterday", "Yesterday +1": "U and YESTERDAY+1",
        "Animal Planet +1": "Animal Plnt+1", "BBC One": "BBC One London HD",
        "BBC One Channel Islands": "BBC One CI HD", "BBC One East Midlands": "BBC One E Mid HD",
        "BBC One East E": "BBC One EastHD", "BBC One North East": "BBC One NE and C HD",
        "BBC One North West": "BBC One N West HD", "BBC One Northern Ireland": "BBC One NI HD",
        "BBC One Nothern Ireland": "BBC One NI HD", "BBC One Scotland": "BBC One ScotHD",
        "BBC One South": "BBC One Sth HD", "BBC One South East": "BBC One S East HD",
        "BBC One South West": "BBC One S West HD", "BBC One Wales": "BBC One Wal HD",
        "BBC One West Midlands": "BBC One WM HD", "BBC One Yorkshire": "BBC One Yorks HD",
        "BBC Two Wales": "BBC Two Wal HD", "Comedy Central Extra": "ComedyXtra",
        "Comedy Central +1": "ComedyCent+1", "Comedy Cent": "Comedy Central HD",
        "Crime+Investigation": "Crime+Inv HD", "Crime & Investigation": "Crime+Inv HD",
        "Crime+Investigation +1": "Crime+Inv+1", "Discovery Channel": "Discovery HD",
        "Discovery History": "Disc.History", "Discovery History +1": "Disc.History+1",
        "Discovery Science": "Disc.Science", "Discovery Science +1": "Disc.Sci+1",
        "Discovery Turbo": "Disc.Turbo", "Food Network +1": "Food Netwrk+1",
        "History": "Sky History HD", "ITV": "ITV1 HD", "ITV +1": "ITV1 +1",
        "ITVX ITV Quiz": "ITV Quiz", "Premier Sports": "Premier Sports 1 HD",
        "Premier Sports 2 HD UK": "Premier Sports 2 HD", "Racing": "Racing TV HD",
        "Racing UK": "Racing TV HD", "Rishtey": "ColorsRishtey",
        "Sky Box Office": "Sky Sports Box Office HD",
        "Sky Cinema Action & Adventure": "Sky Cinema Action HD",
        "Sky Cinema Crime & Thriller": "Sky Cinema Thriller HD",
        "S Cinema Crime & Thriller": "Sky Cinema Thriller HD",
        "Sky Cinema Drama & Romance": "Sky Cinema Drama HD",
        "Sky Cinema ScFi/Horror": "Sky ScFi/HorHD", "Sky Cinema SciFi/Hor": "Sky ScFi/HorHD",
        "Sky Sports Action": "SkySp Action", "Sky Sports News HQ": "Sky Sports News HD",
        "TravelXP Europe": "Travelxp", "Virgin One": "Virgin Media One HD",
        "Virgin Two": "Virgin Media Two HD", "Virgin Three": "Virgin Media Three",
        "Virgin Media 4": "Virgin Media Four HD",
        "National Geographic": "Nat Geo HD", "Investigation Discovery": "ID",
        "NICK": "Nickelodeon HD", "MTV 1": "MTV HD", "Racing UK HD": "Racing TV HD",
    },
}
ALIASES = {"PT": ALIASES_PT}

# Nos grupos do Reino Unido e Alemanha o fornecedor abrevia "Sky" para "S"
# (ex.: "S Sports F1", "S Cinema Premieren").
SKY_PREFIX = {"UK", "DE"}

STRIP_TOKENS = {"fhd", "hd", "uhd", "sd", "hevc", "h265", "4k", "vip", "pt",
                "backup", "mobile", "upscale", "baixa", "internet", "script"}
COUNTRY_TAIL = r"(\s|\.)(pt|be|br|fr|de|uk|gb)(\s+vip)?\s*$"

UA = {"User-Agent": "Mozilla/5.0 (epg-generator; +https://github.com/iptv-org)"}


# --------------------------------------------------------------------------
# Utilitários
# --------------------------------------------------------------------------

def log(msg):
    print(msg, flush=True)


def fetch(url, headers=None, timeout=180):
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
    s = re.sub(r"[¹²³]", "", s)  # "TV Rá Tim Bum HD ³" (marcas de qualidade da fonte BR)
    return unicodedata.normalize("NFKD", s).encode("ascii", "ignore").decode()


def strip_source_noise(name):
    """Tira o sufixo de país (".pt", " UK") e o prefixo de cidade ("São Paulo/SP  ")."""
    name = re.sub(r"^[^/]{2,40}/[A-Z]{2}\s+", "", html.unescape(name).strip())
    name = re.sub(r"\s*\|\s*Event\s*$", "", name, flags=re.I)  # "Canal+ Live 1 FR | Event"
    name = re.sub(r"\s+VIP\s+SPORTS?\s*$", "", name, flags=re.I)  # grupos "VIP Sports"
    name = re.sub(r"^(PT|BE|BR|FR|DE|UK|GB)\s*[|:]\s*", "", name)  # "UK | Sky Sports"
    return re.sub(COUNTRY_TAIL, "", name, flags=re.I).strip()


def norm(name, cc="PT", aliases=True):
    """Chave de comparação: sem acentos, qualidade, sufixos e pontuação.

    Os ALIASES só se aplicam aos nomes da lista/logótipos; os nomes das fontes
    EPG ficam como estão, para "CNN" não ser confundido com "CNN Portugal".
    """
    # parênteses antes do sufixo de país: "AMAZON PRIME 8 HD FR (ONLY EVENTS)"
    s = re.sub(r"\(.*?\)|\[.*?\]", " ", name)
    s = ascii_fold(strip_source_noise(s)).lower()
    s = re.sub(r"\bsd\+", " ", s)  # "beIN SPORTS 1 SD+" é qualidade, não "+1"
    s = s.replace("4:3", " ").replace("+", " mais ").replace("&", " ")
    toks = [t for t in re.findall(r"[a-z0-9]+", s) if t not in STRIP_TOKENS]
    if cc in SKY_PREFIX and toks[:1] == ["s"]:
        toks[0] = "sky"
    key = "".join(toks)
    table = ALIASES.get(cc, {})
    return table.get(key, key) if aliases else key


for _cc, _pairs in NAME_ALIASES.items():
    ALIASES[_cc] = {norm(k, _cc, aliases=False): norm(v, _cc, aliases=False) for k, v in _pairs.items()}


def pretty(name):
    return re.sub(r"\s+(HD|FHD)$", "", strip_source_noise(name), flags=re.I)


def make_id(name, cc):
    s = re.sub(r"[^A-Za-z0-9+!]+", ".", ascii_fold(pretty(name))).strip(".")
    return f"{s}.{cc.lower()}"


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


def sport_country(name):
    """País de um canal dos grupos de desporto/eventos, ou None se não for claro."""
    # o país por extenso entre parênteses ganha ao código de língua: "(Belgium FR)"
    for paren in re.findall(r"\(([^)]*)\)", name):
        found = {cc for cc, rx in SPORT_COUNTRY_WORDS.items() if re.search(rx, paren, re.I)}
        if len(found) == 1:
            return found.pop()
    codes = {SPORT_CODES[t] for t in re.findall(r"\b([A-Z]{2})\b", name) if t in SPORT_CODES}
    if len(codes) == 1:
        return codes.pop()
    if not codes and not re.search(r"\b[A-Z]{2}\b", name.replace("VIP", "")):
        found = [cc for cc, rx in SPORT_BRANDS.items() if re.search(rx, name)]
        if len(found) == 1:
            return found[0]
    return None


def country_of(group, name):
    for cc, cfg in COUNTRIES.items():
        if re.search(cfg["groups"], group):
            return cc
    if re.search(SPORT_GROUPS, group):
        return sport_country(name)
    if re.search(SKIP_GROUPS, group):
        return None
    for cc, cfg in COUNTRIES.items():
        if re.search(rf"\s{cfg['suffix']}\s*$", name):
            return cc
    return None


def scoped_channels(lines):
    """Devolve [(índice da linha EXTINF, nome, grupo, país)] dos canais a tratar."""
    out = []
    for i, line in enumerate(lines):
        if not line.startswith("#EXTINF"):
            continue
        url = next((l for l in lines[i + 1:i + 4] if l.strip() and not l.startswith("#")), "")
        if "/movie/" in url or "/series/" in url:
            continue
        name = line.rsplit(",", 1)[-1].strip()
        group = get_attr(line, "group-title")
        if name.startswith(("#", "=")) or re.search(SKIP_NAMES, name):
            continue
        cc = country_of(group, name)
        if cc:
            out.append((i, name, group, cc))
    return out


# --------------------------------------------------------------------------
# EPG
# --------------------------------------------------------------------------

def load_epg_sources(cc, wanted_keys, start, end):
    """Devolve {key: [(fonte, nome_bonito, [programmes])]} para as chaves pedidas."""
    found = {}
    for src, url, kind in COUNTRIES[cc]["epg"]:
        log(f"- EPG {cc} {src}: {url}")
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
            key = norm(label, cc, aliases=False)
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


def shift_programme(p, hours):
    """Cópia do programa com início/fim deslocados (para canais "+1")."""
    q = copy.deepcopy(p)
    for attr in ("start", "stop"):
        t = parse_time(q.get(attr)) + dt.timedelta(hours=hours)
        q.set(attr, t.strftime("%Y%m%d%H%M%S %z"))
    return q


def best_source(cands, now):
    """Escolhe a fonte com mais programas futuros; em empate, a que vai mais longe.

    Conta programas e não só a hora final: algumas fontes têm um único bloco
    "fictício" de vários dias (ex.: beIN SPORTS 1 na france3), que ganharia a
    uma fonte com a grelha completa.
    """
    def score(c):
        progs = c[2]
        last = max(parse_time(p.get("stop")) for p in progs)
        future = sum(1 for p in progs if parse_time(p.get("stop")) > now)
        return (future, last)
    return max(cands, key=score)


# --------------------------------------------------------------------------
# Logótipos
# --------------------------------------------------------------------------

def load_tv_logos(cc):
    folder = COUNTRIES[cc]["logos"]
    headers = {"Accept": "application/vnd.github+json"}
    if os.environ.get("GITHUB_TOKEN"):
        headers["Authorization"] = f"Bearer {os.environ['GITHUB_TOKEN']}"
    data = fetch(TV_LOGOS_API.format(folder), headers)
    tvlogos = {}
    if data:
        suffix = "gb|uk" if cc == "UK" else cc.lower()
        for item in json.loads(data):
            fname = item.get("name", "")
            if not fname.endswith(".png") or "-icon" in fname:
                continue
            stem = re.sub(rf"-({suffix})$", "", fname[:-4])
            is_hd = bool(re.search(r"(^|-)hd(-|$)", stem))
            # com e sem aliases: "BBC One" tem alias para a região de Londres,
            # mas o logótipo "bbcone" também serve de marca para as outras regiões
            for key in {norm(stem.replace("-", " "), cc), norm(stem.replace("-", " "), cc, aliases=False)}:
                # a versão sem "HD" no logótipo é a mais limpa; usa a HD só se for a única
                if key not in tvlogos or (tvlogos[key][1] and not is_hd):
                    tvlogos[key] = (TV_LOGOS_RAW.format(folder) + fname, is_hd)
    log(f"- tv-logo/tv-logos {cc}: {len(tvlogos)} logótipos")
    return {k: v[0] for k, v in tvlogos.items()}


def load_logos():
    """Devolve {país: {key: url}}. Prioridade: tv-logo/tv-logos > iptv-org (PNG, maior)."""
    chans, lgs = fetch(IPTV_ORG_CHANNELS), fetch(IPTV_ORG_LOGOS)
    best, official = {}, {}
    if chans and lgs:
        for l in json.loads(lgs):
            if l.get("format") != "PNG" or l.get("feed"):
                continue
            # no domínio oficial a largura do iptv-org nem sempre está certa
            # (rtpnoticias_2026.png diz 185 px e tem 2340), por isso não conta
            if re.search(OFFICIAL_LOGO_HOSTS, urllib.parse.urlparse(l["url"]).hostname or ""):
                official.setdefault(l["channel"], l)
            cur = best.get(l["channel"])
            if not cur or (l.get("width") or 0) > (cur.get("width") or 0):
                best[l["channel"]] = l
        chans = [c for c in json.loads(chans) if c["id"] in best and not c.get("closed")]
    else:
        chans = []

    logos, local = {}, {}
    for cc, cfg in COUNTRIES.items():
        iptv, own, own_official = {}, {}, {}
        # canais do próprio país primeiro, para ganharem a outros com o mesmo nome
        for c in sorted(chans, key=lambda c: c.get("country") != cfg["iptv"]):
            for n in [c["name"], *c.get("alt_names", [])]:
                for key in {norm(n, cc), norm(n, cc, aliases=False)}:
                    iptv.setdefault(key, best[c["id"]]["url"])
                    if c.get("country") == cfg["iptv"]:
                        own.setdefault(key, best[c["id"]]["url"])
                        if c["id"] in official:
                            own_official.setdefault(key, official[c["id"]]["url"])
        curated = {}
        for n, url in OFFICIAL_LOGOS.get(cc, {}).items():
            for key in {norm(n, cc), norm(n, cc, aliases=False)}:
                curated[key] = url
        tvlogos = load_tv_logos(cc)
        logos[cc] = {**iptv, **tvlogos, **own_official, **curated}
        local[cc] = {**own, **tvlogos, **own_official, **curated}
        log(f"  {cc}: {len(curated)} logótipos oficiais, {len(own_official)} do iptv-org em domínio oficial")
    log(f"- iptv-org: {len(best)} canais com logótipo PNG")
    return logos, local


def find_logo(key, table, local):
    """Logótipo exato; senão o do canal base ("+1") ou da marca do mesmo país.

    Ex.: "BBC One South" -> BBC One, "Globo SP" -> Globo, "E4 +1" -> E4.
    A marca só é procurada nos logótipos do próprio país e nunca corta a meio
    de um número ("DAZN 10" não fica com o logótipo do "DAZN 1").
    """
    if key in table:
        return table[key]
    base = re.sub(r"mais(1|24)$", "", key)
    if base != key and base in table:
        return table[base]
    # canais de notícias são outra marca ("Fox News" não é a "Fox")
    prefixes = [k for k in local if len(k) >= 3 and base.startswith(k)
                and not base[len(k):][:1].isdigit() and not base[len(k):].startswith("news")]
    return local[max(prefixes, key=len)] if prefixes else None


def print_missing(rows):
    """Resumo por país dos canais sem EPG e/ou sem logótipo (variantes agrupadas)."""
    groups = {}
    for cc, _, name, _, src, logo in rows:
        g = groups.setdefault((cc, norm(name, cc)), {"names": [], "epg": src != "-", "logo": logo == "sim"})
        g["names"].append(name)
    log("\nCanais sem EPG e/ou sem logótipo HD (variantes FHD/HD/HEVC agrupadas):")
    for cc in COUNTRIES:
        items = [(min(g["names"], key=len), len(g["names"]), g["epg"], g["logo"])
                 for (c, _), g in groups.items() if c == cc and not (g["epg"] and g["logo"])]
        if not items:
            continue
        no_epg = sorted(i for i in items if not i[2])
        no_logo = sorted(i for i in items if i[2] and not i[3])
        log(f"\n[{cc}] {len(no_epg)} sem EPG, {len(no_logo)} só sem logótipo")
        for name, n, _, logo in no_epg:
            log(f"  - {name}{f' (+{n - 1})' if n > 1 else ''}{'' if logo else '  [sem logótipo]'}")
        for name, n, _, _ in no_logo:
            log(f"  · {name}{f' (+{n - 1})' if n > 1 else ''}  [tem EPG, sem logótipo]")


def print_check(pattern, rows, programmes, logo_of, now):
    """Relatório de um conjunto de canais: fonte escolhida, grelha e logótipo."""
    progs_of = {cid: progs for cid, progs in programmes}
    groups = {}
    for cc, group, name, tvg_id, src, _ in rows:
        if re.search(pattern, name, re.I):
            key = (cc, norm(name, cc))
            groups.setdefault(key, {"tvg_id": tvg_id, "src": src, "names": []})["names"].append(f"{name}  [{group}]")
    log(f"\nVerificação dos canais '{pattern}': {len(groups)} canais, "
        f"{sum(len(g['names']) for g in groups.values())} entradas na lista")
    for (cc, key), g in sorted(groups.items()):
        progs = progs_of.get(g["tvg_id"], [])
        future = [p for p in progs if parse_time(p.get("stop")) > now]
        if future:
            last = max(parse_time(p.get("stop")) for p in future)
            epg = f"{g['src']}: {len(future)} programas até {last:%d/%m %H:%M} UTC"
        else:
            epg = "SEM EPG"
        logo = logo_of.get((cc, key), "SEM LOGÓTIPO")
        ok = "OK " if future and (cc, key) in logo_of else "!! "
        log(f"\n{ok}[{cc}] {g['tvg_id'] or '(sem tvg-id)'}")
        log(f"    EPG:  {epg}")
        log(f"    Logo: {logo}")
        for n in g["names"]:
            log(f"    - {n}")


# --------------------------------------------------------------------------
# Main
# --------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--m3u", default="lista.m3u")
    ap.add_argument("--epg", default="epg.xml")
    ap.add_argument("--report", default="canais.csv")
    ap.add_argument("--countries", default=",".join(COUNTRIES),
                    help="países a tratar, separados por vírgula (ex.: PT,UK)")
    ap.add_argument("--check", default="",
                    help="mostra o estado (fonte, programas, logótipo) dos canais cujo nome "
                         "corresponda a esta regex, ex.: --check 'beIN SPORTS.*FR'")
    ap.add_argument("--epg-url", default=os.environ.get("EPG_URL", ""),
                    help="URL pública do epg.xml, colocada em url-tvg no cabeçalho da lista")
    args = ap.parse_args()
    wanted = [c.strip().upper() for c in args.countries.split(",") if c.strip().upper() in COUNTRIES]

    now = dt.datetime.now(dt.timezone.utc)
    start, end = now - dt.timedelta(hours=PAST_HOURS), now + dt.timedelta(days=DAYS)

    lines = read_m3u(args.m3u)
    channels = [c for c in scoped_channels(lines) if c[3] in wanted]
    log(f"{len(channels)} canais a tratar em {args.m3u}")

    # Nomes exatos do fornecedor (título, tvg-name e tvg-id originais) por canal.
    # Com Xtream Codes o TiviMate mostra estes nomes e associa o EPG por eles.
    provider_names = {}
    for i, name, _, cc in channels:
        names = provider_names.setdefault((cc, norm(name, cc)), [])
        for n in (name, get_attr(lines[i], "tvg-name"), get_attr(lines[i], "tvg-id")):
            n = n.strip()
            if n and n not in names:
                names.append(n)

    logos, local_logos = load_logos()
    logo_of = {}
    for cc, key in provider_names:
        url = find_logo(key, logos[cc], local_logos[cc])
        if url:
            logo_of[(cc, key)] = url
    tv = ET.Element("tv", {"generator-info-name": "generate_epg.py",
                           "source-info-name": "open-epg.com, epgshare01.online"})
    # o ID vem do nome MEO quando existe, para não mudar de dia para dia
    meo_names = {norm(n, "PT", aliases=False): n for n in MEO_CODES.values()}
    chosen, programmes = {}, []
    for cc in wanted:
        keys = {k for c, k in provider_names if c == cc}
        # canais "+1"/"+24" sem guia próprio: usa o canal base com a hora deslocada
        shifted = {}
        for key in keys:
            m = re.fullmatch(r"(.+?)mais(1|24)", key)
            if m:
                base = ALIASES.get(cc, {}).get(m.group(1), m.group(1))
                shifted[key] = (base, int(m.group(2)))
        epg = load_epg_sources(cc, keys | {b for b, _ in shifted.values()}, start, end)
        for key, (base, hours) in shifted.items():
            if key in epg or base not in epg:
                continue
            src, label, progs = best_source(epg[base], now)
            epg[key] = [(f"{src} +{hours}h", f"{pretty(label)} +{hours}",
                         [shift_programme(p, hours) for p in progs])]
        for key in sorted(k for k in epg if k in keys):
            src, _, progs = best_source(epg[key], now)
            label = meo_names.get(key) if cc == "PT" else None
            label = label or epg[key][0][1]
            cid = make_id(label, cc)
            chosen[(cc, key)] = (cid, src)
            ch = ET.SubElement(tv, "channel", id=cid)
            display = [pretty(label)]
            display += [n for n in provider_names.get((cc, key), []) if n != display[0]]
            for n in display:
                ET.SubElement(ch, "display-name", lang=COUNTRIES[cc]["lang"]).text = n
            if (cc, key) in logo_of:
                ET.SubElement(ch, "icon", src=logo_of[(cc, key)])
            programmes.append((cid, progs))
    if not chosen:
        sys.exit("Nenhuma fonte EPG respondeu – epg.xml não foi alterado.")

    for cid, progs in programmes:
        for p in sorted(progs, key=lambda p: p.get("start")):
            p.set("channel", cid)
            for icon in p.findall("icon"):  # ícones de programa partidos (ex.: fonte NOS)
                src = icon.get("src", "")
                if not src.startswith("http") or re.search(r"\.[a-z]{2}$", src):
                    p.remove(icon)
            tv.append(p)
    ET.indent(tv, space="  ")
    with open(args.epg, "wb") as f:
        f.write(b'<?xml version="1.0" encoding="UTF-8"?>\n')
        f.write(ET.tostring(tv, encoding="utf-8"))
    log(f"{args.epg}: {len(chosen)} canais, {sum(len(p) for _, p in programmes)} programas")

    # Atualiza a lista
    rows, stats = [], {}
    for i, name, group, cc in channels:
        key = norm(name, cc)
        line = lines[i]
        tvg_id, src = chosen.get((cc, key), ("", ""))
        logo = logo_of.get((cc, key))
        if tvg_id:
            line = set_attr(line, "tvg-id", tvg_id)
        if logo:
            line = set_attr(line, "tvg-logo", logo)
        lines[i] = line
        s = stats.setdefault(cc, [0, 0, 0])
        s[0] += 1
        s[1] += bool(tvg_id)
        s[2] += bool(logo)
        rows.append([cc, group, name, get_attr(line, "tvg-id"), src or "-", "sim" if logo else "não"])
    if args.epg_url and lines and lines[0].startswith("#EXTM3U"):
        lines[0] = set_attr(set_attr(lines[0], "url-tvg", args.epg_url), "x-tvg-url", args.epg_url)
    with open(args.m3u, "w", encoding="utf-8", newline="") as f:
        f.write("\n".join(lines))
    for cc, (total, with_epg, with_logo) in stats.items():
        log(f"{args.m3u} {cc}: {with_epg}/{total} com EPG, {with_logo}/{total} com logótipo HD")
    print_missing(rows)
    if args.check:
        print_check(args.check, rows, programmes, logo_of, now)

    if args.report:
        with open(args.report, "w", encoding="utf-8", newline="") as f:
            w = csv.writer(f)
            w.writerow(["pais", "grupo", "canal", "tvg-id", "fonte_epg", "logo_hd"])
            w.writerows(sorted(rows))
        log(f"{args.report}: relatório por canal")


if __name__ == "__main__":
    main()
