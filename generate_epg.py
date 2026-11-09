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
#   logos_extra – outras pastas do tv-logos, para canais que a do país não tem
COUNTRIES = {
    "PT": {
        "groups": r"^Portugal( HEVC)?$", "suffix": "PT", "lang": "pt",
        "logos": "portugal", "iptv": "PT",
        "logos_extra": ["spain", "international"],
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
        "logos_extra": ["france", "netherlands", "international"],
        "epg": [
            ("open-epg-be2", OPEN_EPG.format("belgium2"), "names"),
            ("open-epg-be1", OPEN_EPG.format("belgium1"), "names"),
            ("epgshare01-be", EPGSHARE.format("BE2"), "names"),
        ],
    },
    "BR": {
        "groups": r"^Brazil$", "suffix": "BR", "lang": "pt",
        "logos": "brazil", "iptv": "BR",
        "logos_extra": ["world-latin-america", "united-states"],
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
        "logos_extra": ["international"],
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
        "logos_extra": ["germany/sky-sport", "austria", "international"],
        "epg": [
            ("open-epg-de3", OPEN_EPG.format("germany3"), "names"),
            ("open-epg-de1", OPEN_EPG.format("germany1"), "names"),
            ("epgshare01-de", EPGSHARE.format("DE1"), "names"),
        ],
    },
    "UK": {
        "groups": r"^(United Kingdom( VIP)?|Script UK)$", "suffix": "UK", "lang": "en",
        "logos": "united-kingdom", "iptv": "UK",
        "logos_extra": ["international"],
        "epg": [
            ("open-epg-uk3", OPEN_EPG.format("unitedkingdom3"), "names"),
            ("open-epg-uk1", OPEN_EPG.format("unitedkingdom1"), "names"),
            ("open-epg-uk2", OPEN_EPG.format("unitedkingdom2"), "names"),
            ("epgshare01-uk", EPGSHARE.format("UK1"), "names"),
        ],
    },
    "US": {
        "groups": r"^United States( VIP)?$", "suffix": "US", "lang": "en",
        "logos": "united-states", "iptv": "US",
        "logos_extra": ["united-states/us-local", "international"],
        "epg": [
            ("open-epg-us1", OPEN_EPG.format("unitedstates1"), "names"),
            ("open-epg-us2", OPEN_EPG.format("unitedstates2"), "names"),
            ("open-epg-us3", OPEN_EPG.format("unitedstates3"), "names"),
            ("open-epg-us4", OPEN_EPG.format("unitedstates4"), "names"),
            ("open-epg-us5", OPEN_EPG.format("unitedstates5"), "names"),
            ("open-epg-us6", OPEN_EPG.format("unitedstates6"), "names"),
            ("epgshare01-us2", EPGSHARE.format("US2"), "names"),
            ("epgshare01-us-sports", EPGSHARE.format("US_SPORTS1"), "names"),
            ("epgshare01-fanduel", EPGSHARE.format("FANDUEL1"), "names"),
            # estações locais (por indicativo); ~550 MB, lido em fluxo
            ("epgshare01-us-locals", EPGSHARE.format("US_LOCALS1"), "stream"),
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
    "US": r"united states|\busa\b",
}
SPORT_CODES = {"PT": "PT", "BE": "BE", "BR": "BR", "FR": "FR", "DE": "DE", "UK": "UK", "GB": "UK",
               "US": "US"}
# Marcas aceites mesmo sem código. "Sky Sports" (plural) é só do Reino Unido;
# "TNT Sports" também existe no Brasil, mas nestes grupos sem código é o do UK.
# "S Sports" é a Sky Sports abreviada ("S Sports F1 1 VIP SPORTS").
# Ligas e serviços só dos EUA ("MLS NEXT Flex", "ESPNplus 3", "NBA League Pass 1",
# "Peacock | Event 1"...); nomes com código de outro país ("ESPN 1 FHD AU") não entram.
SPORT_BRANDS = {
    "UK": r"^(Sky|S|TNT) Sports\b",
    "US": r"^(NFL|NBA|NHL|MLB|MILB|MLS|AHL|BTN)\b|^ESPN|^Fox (Sports|Soccer)\b"
          r"|^NBC Sports\b|^Peacock\b|^Paramount\+",
}

# lista de todos os ficheiros do repositório num só pedido (a API tem limite de 60/h sem token)
TV_LOGOS_API = "https://api.github.com/repos/tv-logo/tv-logos/git/trees/main?recursive=1"
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
# um ficheiro de uma pasta qualquer do tv-logo/tv-logos ("pasta/nome", sem .png)
TV_LOGO = "https://raw.githubusercontent.com/tv-logo/tv-logos/main/countries/{}.png"
# logótipos feitos por nós (pasta logos/), quando o tv-logo/tv-logos não tem o canal
REPO_LOGOS = "https://raw.githubusercontent.com/Ogait3718/epg-iptv/main/logos/{}.png"
# cópias dos logótipos do imgur (pasta logos/imgur/, mesmo nome de ficheiro): o imgur
# bloqueia (429) quem pede muitas imagens seguidas, e o TiviMate pede-as todas de uma
# vez ao atualizar o EPG, por isso os logótipos desapareciam
IMGUR_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "logos", "imgur")
IMGUR_MIRROR = "https://raw.githubusercontent.com/Ogait3718/epg-iptv/main/logos/imgur/{}"
# EUA: cópias dos logótipos encontrados noutros servidores (Wikimedia, Plex, Pluto...),
# para os logótipos dos EUA virem todos do repositório; nome = servidor + caminho
US_EXT_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "logos", "us", "ext")
US_EXT_MIRROR = "https://raw.githubusercontent.com/Ogait3718/epg-iptv/main/logos/us/ext/{}"
# logótipos atuais na Wikimedia Commons (confirmados na infobox da Wikipédia)
COMMONS = "https://upload.wikimedia.org/wikipedia/commons/thumb/{0}/960px-{1}.png"
CNBC_2025 = COMMONS.format("b/bc/CNBC_2025.svg", "CNBC_2025.svg")
ID_2020 = COMMONS.format("3/35/InvestigationDiscoveryLogo2020.svg", "InvestigationDiscoveryLogo2020.svg")
EURONEWS_2025 = COMMONS.format("3/3c/Euronews_Logo_2025.svg", "Euronews_Logo_2025.svg")
TRACE_URBAN_2022 = "https://upload.wikimedia.org/wikipedia/commons/9/9a/Traceurban2022.png"
# Ciné+ Premier passou a chamar-se OCS em julho de 2024
OCS_2024 = COMMONS.format("3/37/OCS_2024.svg", "OCS_2024.svg")
# Além dos oficiais, aqui ficam correções: logótipos desatualizados ou errados e
# versões para fundo escuro (o TiviMate tem fundo preto). TV_LOGO = ficheiro do
# tv-logos de outra pasta; REPO_LOGOS = feito por nós a partir do logótipo oficial
# atual, só com o preto passado a branco (ou o negativo, nos logótipos a preto e
# branco), como as próprias marcas fazem em fundo escuro. Logótipos com cores
# escuras da marca (ex.: azul-escuro) ficam como estão.
OFFICIAL_LOGOS = {
    "PT": {
        "RTP 1": RTP_CDN.format("rtp1"), "RTP 2": RTP_CDN.format("rtp2"),
        "RTP Notícias": RTP_CDN.format("rtpnoticias"), "RTP 3": RTP_CDN.format("rtpnoticias"),
        "RTP Memória": RTP_CDN.format("rtpmemoria"), "RTP África": RTP_CDN.format("rtpafrica"),
        "RTP Açores": RTP_CDN.format("rtpacores"), "RTP Madeira": RTP_CDN.format("rtpmadeira"),
        "TVI Reality": IOL_CDN.format("tvireality"), "TVI Ficção": IOL_CDN.format("tvificcao"),
        "TVI Internacional": IOL_CDN.format("tviinternacional"), "TVI África": IOL_CDN.format("tviafrica"),
        "V+TVI": IOL_CDN.format("vmaistvi"),
        # mesmo desenho dos SPORT TV 1-6 do tv-logo/tv-logos (512x96, letras brancas)
        "SPORT TV7": REPO_LOGOS.format("sport-tv-7-pt"),
        "VH1": TV_LOGO.format("united-kingdom/vh1-uk"),
        # o "tpa-es" do tv-logos/spain é a TPA das Astúrias
        "TPA Internacional": "https://i.imgur.com/M7aB0LN.png",
        "CNBC Europe": CNBC_2025, "ID Investigation Discovery": ID_2020,
        "Euronews": EURONEWS_2025, "Trace Urban": TRACE_URBAN_2022,
        "Discovery Channel": REPO_LOGOS.format("discovery-channel-eu"),
        "Nat Geo Wild": TV_LOGO.format("netherlands/national-geographic-wild-nl"),
        "Travel Channel": COMMONS.format("8/8a/2018_Travel_Channel_logo.svg", "2018_Travel_Channel_logo.svg"),
        "DAZN 5": TV_LOGO.format("belgium/dazn-5-be"),
        "Motorvision TV": TV_LOGO.format("germany/motorvision-tv-de"),
        "ARTV": REPO_LOGOS.format("artv-pt"), "W-Sport": REPO_LOGOS.format("w-sport-pt"),
        "BOMSOM TV": REPO_LOGOS.format("bomsom-tv-pt"),
        # "BackUP- Sport 1": cópia da SPORT TV 1, mesmo logótipo
        "Sport 1": TV_LOGO.format("portugal/sport-tv-1-pt"),
        # "CNN PT" e "S News PT" são a CNN dos EUA e a Sky News do Reino Unido (ver ALIASES_PT)
        "CNN US": TV_LOGO.format("united-states/cnn-us"),
        "Sky News": TV_LOGO.format("united-kingdom/sky-news-uk"),
        "Fox News": TV_LOGO.format("united-states/fox-news-us"),
        "Ginx": TV_LOGO.format("international/ginx-e-sports-tv-int"),
        # o iptv-org dava a HGTV do Vietname (Hậu Giang TV)
        "HGTV": TV_LOGO.format("united-kingdom/hgtv-uk"),
        "TVE 24h": TV_LOGO.format("spain/24h-es"),  # o canal da RTVE chama-se agora "24h"
        # todos os "LiveCam <praia>" (a marca chega pelo prefixo, em find_logo)
        "LiveCam": REPO_LOGOS.format("meo-beachcam-pt"),
        "OneToro TV": REPO_LOGOS.format("onetoro-tv-pt"),
        "RTP Arena": REPO_LOGOS.format("rtp-arena-pt"),
        "Santuario Fatima": REPO_LOGOS.format("santuario-fatima-pt"),
        "TV Maná": "https://i.imgur.com/6jNqpTP.png",
        "AD Almada TV": "https://i.imgur.com/AlKQZcZ.jpeg",
        # o tv-logos e o iptv-org não o têm; é o logótipo que vinha na lista do fornecedor
        "Dizi": "https://i.imgur.com/2Hyii2W.png",
        "Campo Pequeno": REPO_LOGOS.format("campo-pequeno-tv-pt"),
    },
    "BE": {
        "Discovery Channel": REPO_LOGOS.format("discovery-channel-eu"),
        "Nat Geo Wild": TV_LOGO.format("netherlands/national-geographic-wild-nl"),
        "AB3": REPO_LOGOS.format("ab3-be"), "AB3 Family": REPO_LOGOS.format("ab3-be"),
        # a pasta belgium tem os Ciné+ com o desenho de 2011
        "Ciné+ Classic": TV_LOGO.format("france/cine-plus-classic-fr"),
        "Ciné+ Frisson": TV_LOGO.format("france/cine-plus-frisson-fr"), "Ciné+ Premier": OCS_2024,
        "Euronews": EURONEWS_2025, "Trace Urban": TRACE_URBAN_2022,
        "Love Nature": COMMONS.format("0/0d/Love_Nature_logo_%282025%29.svg", "Love_Nature_logo_%282025%29.svg"),
    },
    "BR": {
        "E!": TV_LOGO.format("united-states/e-entertainment-us"),
        "A&E": TV_LOGO.format("brazil/a-and-e-br"),
        "Curta!": REPO_LOGOS.format("curta-br"),
        # canal de futebol da Globo; o iptv-org dava o Sky Cinema alemão (e links partidos)
        **{f"Premiere {n}": TV_LOGO.format("brazil/premiere-br") for n in range(1, 8)},
        "Premier 1": TV_LOGO.format("brazil/premiere-br"),
        "ID": ID_2020,
    },
    "FR": {
        "Discovery Channel": REPO_LOGOS.format("discovery-channel-eu"),
        "Discovery Investigation": ID_2020,
        "National Geographic": TV_LOGO.format("united-kingdom/national-geographic-uk"),
        "Nat Geo Wild": TV_LOGO.format("netherlands/national-geographic-wild-nl"),
        "E!": TV_LOGO.format("united-kingdom/e-entertainment-uk"),
        "Luxe TV": TV_LOGO.format("luxembourg/luxe-tv-lu"),
        "Viceland": REPO_LOGOS.format("vice-tv"),  # a marca é agora Vice TV
        "Gong": REPO_LOGOS.format("gong-fr"),
        "VH1": TV_LOGO.format("united-kingdom/vh1-uk"),
        "Euronews": EURONEWS_2025,
        # mudaram de nome: Chérie 25 -> RMC Life, CStar Hits France -> Europe 2 Pop TV,
        # Ciné+ Premier -> OCS, Ciné+ Famiz -> Ciné+ Family, Ciné+ Club -> Ciné+ Festival
        "Chérie 25": TV_LOGO.format("france/rmc-life-fr"),
        "CSTAR Hits France": REPO_LOGOS.format("europe-2-pop-tv-fr"),
        "Ciné+ Premier": OCS_2024,
        "Ciné+ Famiz": TV_LOGO.format("france/cine-plus-family-fr"),
        "Ciné+ Club": TV_LOGO.format("france/cine-plus-festival-fr"),
        "ES1": REPO_LOGOS.format("mgg-tv-fr"),  # ES1 -> MGG TV (2022)
        "DJAZZ TV": REPO_LOGOS.format("stingray-djazz-fr"),
        "FRANCE 3 NOA": REPO_LOGOS.format("france-3-nouvelle-aquitaine-fr"),
        "M6 Boutique & Co": REPO_LOGOS.format("m6-boutique-fr"),
        "Motus TV": REPO_LOGOS.format("motus-fr"),
        "TAHITI NUI": REPO_LOGOS.format("tntv-fr"),  # Tahiti Nui Télévision (TNTV)
        "TV5 Monde Info": IMGUR_MIRROR.format("AJx5Fy2.png"),
        "TV5 Monde Infor": IMGUR_MIRROR.format("AJx5Fy2.png"),
    },
    "DE": {
        "NatGeo": TV_LOGO.format("germany/national-geographic-de"),
        **{f"DAZN {n}": TV_LOGO.format(f"belgium/dazn-{n}-be") for n in range(3, 7)},
        "QVC 2": TV_LOGO.format("germany/qvc-zwei-de"),
        "QVC Beauty & Style": TV_LOGO.format("germany/qvc-style-de"),
        "Eurosport 2 Xtra": REPO_LOGOS.format("eurosport-2-xtra-de"),
        "Sky PREMIEREN +24": TV_LOGO.format("germany/sky-cinema-premieren-plus24-de"),
        # o "rtl-plus-de" do tv-logos não é o logótipo atual (RTL+ 2021)
        "RTL+": REPO_LOGOS.format("rtl-plus-de"),
        "Euronews": EURONEWS_2025,
        # cópias em logos/ (tv-logo/tv-logos, Wikimedia Commons); a lista não tinha
        # logótipo ou tinha um antigo (A+E com o do Crime + Investigation, anterior a 2014)
        "A+E": REPO_LOGOS.format("a-and-e-de"),
        **{f"Dyn Sport {n}": REPO_LOGOS.format("dyn-de") for n in range(1, 26)},
        "Franken Plus": REPO_LOGOS.format("franken-plus-de"),
        "Schau TV": REPO_LOGOS.format("schau-tv-at"),  # texto preto passado a branco
        "Sky Sport 4K Ultra": REPO_LOGOS.format("sky-sport-uhd-de"),  # é o Sky Sport UHD
        # canal novo (set. 2026) ainda sem logótipo público: feito no estilo dos
        # outros Sky Sport DE (como o Sky Sport F1), com o escudo oficial da NFL
        "Sky Sport NFL": REPO_LOGOS.format("sky-sport-nfl-de"),
    },
    "UK": {
        "E!": TV_LOGO.format("united-kingdom/e-entertainment-uk"),
        "Nat Geo Wild": TV_LOGO.format("netherlands/national-geographic-wild-nl"),
        "CNBC": CNBC_2025,
        "BBC Lifestyle": REPO_LOGOS.format("bbc-lifestyle"),
        "Luxe TV": TV_LOGO.format("luxembourg/luxe-tv-lu"),
        "TCM": TV_LOGO.format("united-kingdom/tcm-movies-uk"),  # no UK o canal é TCM Movies
        "TRT World": TV_LOGO.format("turkey/trt-world-tr"),
        # "TNT Sports 4K UHD" (a chave fica "tntsports"): o canal 4K do UK é o
        # TNT Sports Ultimate; antes caía no logótipo da TNT Sports latino-americana
        "TNT Sports": TV_LOGO.format("united-kingdom/tnt-sports-ultimate-uk"),
        "Nasa TV": TV_LOGO.format("united-states/nasa-tv-us"),
        # canal "Script" sem equivalente real; o iptv-org dava um canal de Hong Kong
        "Classic Movies": "",
        # cópias em logos/ (tv-logo/tv-logos, Wikipédia); o iptv-org e a lista não
        # tinham logótipo que funcionasse
        "Celtic TV": REPO_LOGOS.format("celtic-tv-uk"),  # emblema do Celtic FC
        "Club MTV": REPO_LOGOS.format("club-mtv-uk"),
        "Food Network +1": REPO_LOGOS.format("food-network-plus-1-uk"),
        "Fox News": REPO_LOGOS.format("fox-news-uk"),
        "Sky Cinema ScFi/Horror": REPO_LOGOS.format("sky-cinema-sci-fi-horror-uk"),
        "Premier 1": REPO_LOGOS.format("premier-sports-1-uk"),  # canais "Script"
        "Premier 2": REPO_LOGOS.format("premier-sports-2-uk"),
        "TOWIE TV": REPO_LOGOS.format("towie-tv-uk"),  # The Only Way Is Essex
        # sem isto caíam no logótipo antigo da Sky Sports (imgur, anterior a 2020)
        "Sky Sports+ 1": REPO_LOGOS.format("sky-sports-plus-uk"),
        "Sky Sports+ 24": REPO_LOGOS.format("sky-sports-plus-uk"),
        **{f"Sky Sports F1 {n}": REPO_LOGOS.format("sky-sports-f1-uk") for n in range(1, 6)},
    },
    "US": {
        # canais de equipa da NBA ("US NBA Atlanta Hawks (A)"): emblema da equipa
        # (cópias em logos/us/ do tv-logo/tv-logos)
        **{f"NBA {t.replace('-', ' ').title()}": REPO_LOGOS.format(f"us/nba-{t}") for t in (
            "atlanta-hawks", "boston-celtics", "brooklyn-nets", "charlotte-hornets",
            "chicago-bulls", "cleveland-cavaliers", "dallas-mavericks", "denver-nuggets",
            "detroit-pistons", "golden-state-warriors", "houston-rockets", "indiana-pacers",
            "los-angeles-lakers", "memphis-grizzlies", "miami-heat", "milwaukee-bucks",
            "minnesota-timberwolves", "new-orleans-pelicans", "new-york-knicks",
            "oklahoma-city-thunder", "orlando-magic", "philadelphia-76ers", "phoenix-suns",
            "portland-trail-blazers", "sacramento-kings", "san-antonio-spurs",
            "toronto-raptors", "utah-jazz", "washington-wizards")},
        "NBA Los Angeles Clippers": REPO_LOGOS.format("us/nba-la-clippers"),
        "beIN Sport 1": REPO_LOGOS.format("us/bein-sports-1"),
        **{f"DAZN {n}": REPO_LOGOS.format("us/dazn") for n in range(1, 31)},  # "US-DAZN 3"
        # o iptv-org dava o logótipo de outro canal (This TV, HBO Canada/Hits, SNY...)
        # ou a versão a preto, invisível no fundo do TiviMate
        "Cinemax More": REPO_LOGOS.format("us/cinemax"), "CineMax MoreMax": REPO_LOGOS.format("us/cinemax"),
        "MoreMax": REPO_LOGOS.format("us/cinemax"), "HBO East": REPO_LOGOS.format("us/hbo"),
        "HBO 2": REPO_LOGOS.format("us/hbo"), "HBO 2 West": REPO_LOGOS.format("us/hbo"),
        "RetroPlex": REPO_LOGOS.format("us/retroplex"), "IndiePlex": REPO_LOGOS.format("us/indieplex"),
        "A&E": REPO_LOGOS.format("us/a-and-e"), "A&E TV": REPO_LOGOS.format("us/a-and-e"),
        "ION TV": REPO_LOGOS.format("us/ion-television"), "CBS": REPO_LOGOS.format("us/cbs"),
        # sem logótipo certo disponível (o iptv-org dava o de outro canal)
        "Bleav Football": "", "FilmRise Classic": "", "CTV DRAMA": "", "CTV sci-fi": "",
        "Fight Sport": "", "Sportsnet East": "",
        **{f"Fox Sports {r}": REPO_LOGOS.format("us/fanduel-sports-network")
           for r in ("Ohio", "Ohio Plus", "Time Ohio", "San Antonio", "Arizona")},
        **{f"beIN Sport {n}": REPO_LOGOS.format(f"us/bein-sports-{n}") for n in range(2, 9)},
    },
}
# EUA: canais de eventos de uma liga/serviço ("NFL-49ers", "MLB 7", "MLS 2023 Leagues
# Cup Pumas", "Peacock Event 5", "US-DAZN 10"): sem logótipo próprio, ficam com o da
# marca. Só para canais dos EUA que não encontraram nenhum (cópias em logos/us/).
# marcas que mudaram de nome: o logótipo atual ganha a todos os outros
# (Fox Sports regionais -> Bally Sports -> FanDuel Sports Network em 2024)
US_PREFIX_LOGOS = {"fanduelsports": REPO_LOGOS.format("us/fanduel-sports-network")}
US_BRAND_LOGOS = {
    "nfl": REPO_LOGOS.format("us/nfl"), "mlb": REPO_LOGOS.format("us/mlb"),
    "mls": REPO_LOGOS.format("us/mls"), "paramountmais": REPO_LOGOS.format("us/paramount-plus"),
    "peacock": REPO_LOGOS.format("us/peacock"), "dazn": REPO_LOGOS.format("us/dazn"),
    "stadium": REPO_LOGOS.format("us/stadium"), "btn": REPO_LOGOS.format("us/btn"),
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
    "cnn": "cnnus", "snews": "skynews", "tpa": "tpainternacional",
    "sporttv": "sporttv1",  # "SportTV UHD 4K": o fornecedor dá-lhe o tvg-id da SPORT TV 1
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
        # canais da plataforma da LFP; no tv-logos são "Ligue 1+" e "Ligue 1+ 2" a "10"
        "Ligue 1+ Pass 1": "Ligue 1+", **{f"Ligue 1+ Pass {n}": f"Ligue 1+ {n}" for n in range(2, 11)},
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
    # EUA: nomes antigos ou abreviados na lista -> nome nas fontes; estações locais
    # pelo indicativo (ver us_callsign). Só entram os confirmados com programação.
    "US": {
        "5 StarMax": "5 StarMAX HD East", "CineMax 5 StarMax": "5 StarMAX HD East",
        "ABC": "ABC National Feed", "ABC 7 ( New York )": "WABC", "ABC News": "ABC News Live",
        "Adult Swim": "AdultSwim com Cartoon Network", "A&E": "AETV",
        "American Heroes": "American Heroes Channel HD",
        "AWE": "A Wealth of Entertainment", "AWE TV": "A Wealth of Entertainment",
        "beINSports": "beIN Sports USA HD", "bein Sport US": "beIN Sports USA HD",
        "Bloomberg TV": "Bloomberg HD", "Buzzr": "BUZZR Stream",
        "Cable News Network": "Cable News Network HDTV",
        "CBS": "CBS National Schedule", "CBSN": "CBS News National Stream",
        "CBS Sports Golazo": "CBS Sports Golazo Network",
        "Cinemax Action East": "Cinemax Action HDTV", "CineMax ActionMax East": "ActionMax Eastern",
        "Cinemax West": "Cinemax (Pacific)", "Cinemax More": "MoreMax Eastern",
        "CineMax MoreMax": "MoreMax Eastern", "MoreMax": "MoreMax Eastern",
        "Comet tv": "Comet", "COWBOY CHANNEL": "The Cowboy Channel", "C-Span 1": "CSPAN",
        "CW11": "WPIX", "Discovery": "Discovery Channel HD",
        "Discovery Family": "Discovery Family Channel HD", "Discovery Velocity": "MOTORTREND HD",
        "E! Entertainment": "E! Entertainment USA East",
        "EPIX": "MGM+ HD", "EPIX 2": "MGM+ Hits HD", "EPIX DRIVE IN": "MGM+ Drive-In",
        "EPIX HITS": "MGM+ Marquee", "ESPN 1": "ESPN HD", "Fight": "Fight Network",
        "FXX East": "FXX USA Eastern", "GAC Family": "GAC Family East",
        "Galavision": "Galavision HDTV", "Hallmark": "Hallmark Channel HD",
        "HALLMARK DRAMA": "Hallmark Family", "Hallmark Movies & Mysteries": "Hallmark Mystery HD",
        "HBO 2 West": "HBO2 (Pacific)", "ION TV": "ION (West Network)", "Law & Crime Network": "Law and Crime",
        "Lifetime Movies": "Lifetime Movies East", "ME TV": "Me TV Network",
        "MLB": "MLB Network HD", "MSG": "MSG National",
        "Nat Geographic": "National Geographic HD", "Nat Geo Wild": "National Geographic Wild HD",
        "NBA": "NBA TV HD", "NBC Golf": "Golf Channel HD", "NBC Golf Channel": "Golf Channel HD",
        "NBC New York": "WNBC", "NBC San Diego": "KNSD", "FOX San Diego": "KSWB",
        "CBS San Diego": "KFMB",
        # estações Fox próprias (O&O): nome comercial -> indicativo
        "Fox 10 Phoenix": "KSAZ", "Fox 11 LosAngeles": "KTTV", "Fox 13 Seattle": "KCPQ",
        "Fox 13 Tampa Bay": "WTVT", "Fox 26 Houston": "KRIV", "Fox 29 Philadelphia": "WTXF",
        "Fox 2 Detroit": "WJBK", "Fox 2 San Francisco": "KTVU", "Fox 32 Chicago": "WFLD",
        "Fox 35 Orlando": "WOFL", "Fox 4 Dallas | Fort Worth": "KDFW", "Fox 5 Atlanta": "WAGA",
        "Fox 5 New York": "WNYW", "Fox 5 Washington DC": "WTTG", "Fox 6 Milwaukee": "WITI",
        "Fox 7 Austin": "KTBC", "Fox 9 Minneapolis-St. Paul": "KMSP", "FOX 43": "WPMT",
        "WGN-TV 9  Chicago": "WGN", "WGN America": "NewsNation",
        "PBS 13 (WNETDT) NewYork": "WNET", "Valley PBS": "KVPT",
        "TN VA | TRI CITIES | CBS WJHL": "WJHL", "MO | ST. LOUIS ABC KDNL": "KDNL",
        # Fox Sports regionais -> Bally Sports (2021) -> FanDuel Sports Network (2024)
        "Fox Sports Cincinnati": "FanDuel Sports Network Ohio - Cincinnati",
        "Fox Sports Detroit": "FanDuel Sports Network Detroit HD",
        "Fox Sports Florida": "FanDuel Sports Network Florida",
        "Fox Sports MIDWEST": "FanDuel Sports Network Midwest St. Louis",
        "FanDuel Sports Network Midwest": "FanDuel Sports Network Midwest St. Louis",
        "Fox Sports New Orleans": "FanDuel Sports New Orleans",
        "Fox Sports North": "FanDuel Sports Network North",
        "Fox Sports Oklahoma": "FanDuel Sports Network Oklahoma",
        "Fox Sports Prime Ticket": "FanDuel Sports Network SoCal",
        "Fox Sports South": "FanDuel Sports Network South",
        "Fox Sports TENNESSEE": "FanDuel Sports - Tennessee East",
        "FanDuel Sports Network CAROLINAS": "FanDuel Sports Network South- Carolinas",
        "Fox Sports Carolina": "FanDuel Sports Network South- Carolinas",
        # canais de jogo com o nome da rede: grelha da rede
        "NCAAF | 00 ABC": "ABC National Feed", "NCAAF | 01 ACC NETWORK": "ACC Network",
        "NCAAF | 02 AT&T SPORTSNET PITTSBURGH": "SportsNet Pittsburgh HD",
        "NCAAF | 03 BIG TEN NETWORK": "Big Ten Network HD", "NCAAF | 04 CBS": "CBS National Schedule",
        "NCAAF | 05 CBS SPORTS NETWORK": "CBS Sports Network HD", "NCAAF | 06 ESPN": "ESPN HD",
        "NCAAF | 07 ESPN 2": "ESPN2", "NCAAF | 08 ESPN U": "ESPNU HD", "NCAAF | 13 FOX": "FOX",
        "NCAAF | 14 FS1": "Fox Sports 1", "NCAAF | 15 MSG": "MSG National",
        "NCAAF | 16 SEC NETWORK": "SEC Network HD", "NFL | 00 ESPN MNF": "ESPN HD",
        "NFL | 00 NFL NETWORK TNF": "NFL Network HD", "NFL | 00 NFL REDZONE": "NFL RedZone HD",
        "NFL Network 1": "NFL Network HD",
        "NECN": "NECN New England Cable News", "NESN Plus": "NESN+ New England Sports Network Plus",
        "News 12 The Bronx": "News 12 Bronx", "One America News": "One America News Network HD",
        "Outside TV": "Outside Television HD", "Smithsonian Channel": "Smithsonian Channel USA",
        "SNY": "SNY SportsNet New York HD", "Start TV": "Start TV Network",
        "Starz Black": "Starz in Black HD", "Starz Cinema East": "Starz Cinema Eastern",
        "Starz East": "Starz Eastern", "Starz Encore East": "Starz Encore Eastern",
        "Starz Encore West": "Starz Encore (Pacific)", "Starz Encore Western": "Starz Encore Westerns",
        "Starz Family": "Starz Encore Family SD", "Starz Kids & Family": "STARZ Kids And Family HD",
        "Starz West": "Starz (Pacific)", "SUNDANCE": "SundanceTV HD",
        "VH1 Classic": "MTV Classic", "Viceland": "Vice", "H2": "Vice",
        "VSiN": "VSIN Vegas Sports and Information Network", "WEATHER NATION": "Weather Nation TV HD",
        "Spike TV": "Paramount Network", "DIY Network": "Magnolia Network",
        "Discovery Science": "Science Channel",
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


# Estações locais dos EUA: o indicativo (KTLA, WPWR...) é o que identifica o canal.
# Na lista: "CA | LOS ANGELES | CW KTLA 5", "ABC 13 Las Vegas NV (KTNV)", "CBS WPEC
# West Palm Beach"; nas fontes: "KTLA-DT" (US_LOCALS1), "(KMTP) San Francisco, CA".
US_NETWORKS = r"ABC|CBS|NBC|FOX|CW|PBS|MyTV|MyNetworkTV|ION|Telemundo|Univision|UniMas"


CALL = r"(?!WEST\b|KIDS\b|WILD\b|WORLD\b)[KW][A-Z]{2,3}"


def us_callsign(name):
    m = (re.fullmatch(rf"({CALL})-(DT|TV|CD|LD)", name)
         or re.search(rf"\(({CALL})(?:-(?:TV|DT))?\)", name)
         or re.match(rf"^(?:{US_NETWORKS})\s+({CALL})\b", name))
    if m:
        return m.group(1)
    if re.match(r"^[A-Z]{2}\s*\|[^|]+\|", name):  # "ESTADO | CIDADE | ..."
        calls = re.findall(rf"\b({CALL})\b", name.split("|", 2)[2])
        if calls:
            return calls[-1]
    return None


def norm(name, cc="PT", aliases=True):
    """Chave de comparação: sem acentos, qualidade, sufixos e pontuação.

    Os ALIASES só se aplicam aos nomes da lista/logótipos; os nomes das fontes
    EPG ficam como estão, para "CNN" não ser confundido com "CNN Portugal".
    """
    if cc == "US":
        # "US| ABC 15 Phoenix", "00 | UNIMAS (EAST)"
        name = re.sub(r"^(US|\d{2})\s*\|\s*", "", html.unescape(name).strip())
        call = us_callsign(name)
        if call:
            return call.lower()
        # "TX | DALLAS | GALAVISION": afiliada sem indicativo -> grelha da rede
        local = re.match(r"^[A-Z]{2}\s*\|[^|]+\|(.*)$", name)
        if local and local.group(1).strip(" |"):
            name = local.group(1)
    # parênteses antes do sufixo de país: "AMAZON PRIME 8 HD FR (ONLY EVENTS)"
    s = re.sub(r"\(.*?\)|\[.*?\]", " ", name)
    s = ascii_fold(strip_source_noise(s)).lower()
    s = re.sub(r"\bsd\+", " ", s)  # "beIN SPORTS 1 SD+" é qualidade, não "+1"
    s = s.replace("4:3", " ").replace("+", " mais ").replace("&", " ")
    toks = [t for t in re.findall(r"[a-z0-9]+", s) if t not in STRIP_TOKENS]
    if cc in SKY_PREFIX and toks[:1] == ["s"]:
        toks[0] = "sky"
    # EUA: o código vem no fim ("A&E HD US", "Fox 5 ... HD VIP US") ou no início
    # ("US NFL-49ers"); só aqui, para não mexer nas chaves dos outros países
    # (o PT usa "CNN US" das fontes)
    if cc == "US":
        if len(toks) > 1 and toks[-1] == "us":
            toks.pop()
        if len(toks) > 1 and toks[0] == "us":
            toks.pop(0)
    key = "".join(toks)
    table = ALIASES.get(cc, {})
    return table.get(key, key) if aliases else key


for _cc, _pairs in NAME_ALIASES.items():
    ALIASES[_cc] = {norm(k, _cc, aliases=False): norm(v, _cc, aliases=False) for k, v in _pairs.items()}


def pretty(name):
    return re.sub(r"\s+(HD|FHD)$", "", strip_source_noise(name), flags=re.I)


def make_id(name, cc):
    name = pretty(name)
    if cc == "US":  # "A&E HD US" -> "A.E.us", não "A.E.HD.US.us"
        name = pretty(re.sub(r"^US\s+|(\s+VIP)?\s+US$", "", name))
    s = re.sub(r"[^A-Za-z0-9+!]+", ".", ascii_fold(name)).strip(".")
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
    # "HD"/"SD" são qualidade, não país ("TNT Sports 1 HD VIP Sports")
    if not codes and not re.search(r"\b(?!HD\b|SD\b)[A-Z]{2}\b", name.replace("VIP", "")):
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

def load_epg_stream(src, data, cc, wanted_keys, start, end):
    """Como load_epg_sources para uma fonte, mas sem ter o XML todo em memória
    (US_LOCALS1 tem ~550 MB). Devolve {key: (fonte, nome, [programmes])}."""
    chan_key, progs = {}, {}
    try:
        for _, el in ET.iterparse(io.BytesIO(data), events=("end",)):
            if el.tag == "channel":
                cid = el.get("id", "")
                label = el.findtext("display-name") or cid
                key = norm(label, cc, aliases=False)
                if key in wanted_keys:
                    chan_key[cid] = (key, label)
                el.clear()
            elif el.tag == "programme":
                cid = el.get("channel")
                keep = False
                if cid in chan_key:
                    try:
                        keep = not (parse_time(el.get("stop")) < start or parse_time(el.get("start")) > end)
                    except (TypeError, ValueError):
                        keep = False
                if keep:
                    progs.setdefault(cid, []).append(copy.deepcopy(el))
                el.clear()
    except ET.ParseError as e:
        log(f"  ! XML inválido: {e}")
    out = {}
    for cid, (key, label) in chan_key.items():
        if progs.get(cid) and key not in out:
            out[key] = (src, label, progs[cid])
    return out


def load_epg_sources(cc, wanted_keys, start, end):
    """Devolve {key: [(fonte, nome_bonito, [programmes])]} para as chaves pedidas."""
    found = {}
    for src, url, kind in COUNTRIES[cc]["epg"]:
        log(f"- EPG {cc} {src}: {url}")
        data = fetch(url)
        if not data:
            continue
        if kind == "stream":
            found_src = load_epg_stream(src, data, cc, wanted_keys, start, end)
            del data
            for key, item in found_src.items():
                found.setdefault(key, []).append(item)
            log(f"  {len(found_src)} canais com programação")
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

_tv_logos_files = None

def tv_logos_files():
    """{pasta: [ficheiros]} de todo o tv-logo/tv-logos/countries, pedido uma vez só."""
    global _tv_logos_files
    if _tv_logos_files is None:
        headers = {"Accept": "application/vnd.github+json"}
        if os.environ.get("GITHUB_TOKEN"):
            headers["Authorization"] = f"Bearer {os.environ['GITHUB_TOKEN']}"
        data = fetch(TV_LOGOS_API, headers)
        _tv_logos_files = {}
        for item in json.loads(data)["tree"] if data else []:
            folder, _, fname = item["path"].removeprefix("countries/").rpartition("/")
            if item["path"].startswith("countries/") and item["type"] == "blob":
                _tv_logos_files.setdefault(folder, []).append(fname)
    return _tv_logos_files


def load_tv_logos(cc, folder):
    tvlogos = {}
    files = tv_logos_files().get(folder)
    if files:
        # nas pastas de outros países o sufixo é o código desse país ("-es", "-us", "-lam")
        own = folder == COUNTRIES[cc]["logos"]
        suffix = ("gb|uk" if cc == "UK" else cc.lower()) if own else "[a-z]+"
        for fname in files:
            if not fname.endswith(".png") or "-icon" in fname:
                continue
            stem = re.sub(rf"-({suffix})$", "", fname[:-4])
            is_hd = bool(re.search(r"(^|-)hd(-|$)", stem))
            # o tv-logos escreve "+" como "plus" ("canal-plus-fr"), a lista usa "+"
            # ("CANAL+" -> "canalmais", "premieren-plus24" -> "+24", "ligue-1plus" ->
            # "Ligue 1+"); as duas formas entram, porque "plus" também é nome próprio
            # ("toggo-plus" = "TOGGO plus")
            stems = {stem, re.sub(r"(^|-|\d)plus(?=-|\d|$)", r"\1+", stem)}
            # com e sem aliases: "BBC One" tem alias para a região de Londres,
            # mas o logótipo "bbcone" também serve de marca para as outras regiões
            keys = {norm(s.replace("-", " "), cc, aliases=a) for s in stems for a in (True, False)}
            if folder.endswith("/us-local"):
                m = re.search(r"-([kw][a-z]{2,3})(-hz)?$", stem)
                if m:
                    keys.add(m.group(1))
                # a versão horizontal ("-hz") só se for a única
                is_hd = is_hd or bool(m and m.group(2))
            for key in keys:
                # a versão sem "HD" no logótipo é a mais limpa; usa a HD só se for a única
                if key not in tvlogos or (tvlogos[key][1] and not is_hd):
                    tvlogos[key] = (TV_LOGOS_RAW.format(folder) + fname, is_hd)
    log(f"- tv-logo/tv-logos {cc} ({folder}): {len(tvlogos)} logótipos")
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
        tvlogos = load_tv_logos(cc, cfg["logos"])
        # pastas de países vizinhos: só para canais que a do próprio país não tem
        # (ex.: France 2 na Bélgica), antes dos logótipos genéricos do iptv-org
        extra = {}
        for folder in cfg.get("logos_extra", ()):
            for key, url in load_tv_logos(cc, folder).items():
                extra.setdefault(key, url)
        logos[cc] = {**iptv, **extra, **tvlogos, **own_official, **curated}
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


def ext_logo_name(url):
    u = urllib.parse.urlparse(url)
    return re.sub(r"[^A-Za-z0-9._-]+", "_", f"{u.hostname}{urllib.parse.unquote(u.path)}").strip("_")[-120:]


def mirror_logo_us(url):
    """EUA: troca um logótipo de fora do GitHub pela cópia em logos/us/ext/, se existir."""
    if urllib.parse.urlparse(url).hostname in ("raw.githubusercontent.com", None):
        return url
    fname = ext_logo_name(url)
    if os.path.isfile(os.path.join(US_EXT_DIR, fname)):
        return US_EXT_MIRROR.format(urllib.parse.quote(fname))
    return url


def mirror_logo(url):
    """Troca um link do imgur pela cópia em logos/imgur/, quando existe."""
    fname = re.sub(r"^https?://i\.imgur\.com/", "", url)
    if fname != url and os.path.isfile(os.path.join(IMGUR_DIR, fname)):
        return IMGUR_MIRROR.format(fname)
    return url


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
    provider_logo = {(cc, norm(name, cc)) for i, name, _, cc in channels if get_attr(lines[i], "tvg-logo")}
    logo_of = {}
    # EUA: as estações locais (chave = indicativo) só procuram no tv-logos dos EUA e nos
    # nossos; nos nomes do iptv-org "KCTV" (CBS Kansas City) apanhava a King County TV
    us_only = {k: v for k, v in logos.get("US", {}).items()
               if "/united-states/" in v or "/Ogait3718/" in v}
    for cc, key in provider_names:
        prefix = next((p for p in US_PREFIX_LOGOS if key.startswith(p)), None) if cc == "US" else None
        if prefix:
            url = US_PREFIX_LOGOS[prefix]
        elif cc == "US" and re.fullmatch(r"[kw][a-z]{2,3}", key):
            url = find_logo(key, us_only, us_only)
        else:
            url = find_logo(key, logos[cc], local_logos[cc])
        if url is None and cc == "US":
            # com alias a chave passa a ser a da fonte EPG ("Fox Sports New Orleans" ->
            # "FanDuel Sports New Orleans"); o logótipo pode estar no nome original
            for n in provider_names[(cc, key)]:
                k = norm(n, cc, aliases=False)
                call = re.fullmatch(r"[kw][a-z]{2,3}", k)
                url = find_logo(k, us_only if call else logos[cc], us_only if call else local_logos[cc])
                if url is not None:
                    break
            # o da marca só se o fornecedor não der nenhum ("NFL Live 01" já traz o seu)
            brand = next((b for b in US_BRAND_LOGOS if key.startswith(b)), None)
            if url is None and brand and (cc, key) not in provider_logo:
                url = US_BRAND_LOGOS[brand]
        if url:
            logo_of[(cc, key)] = mirror_logo(url)
            if cc == "US":
                url = mirror_logo_us(logo_of[(cc, key)])
                # nos EUA só logótipos do GitHub/repositório; sem cópia fica o do fornecedor
                if urllib.parse.urlparse(url).hostname == "raw.githubusercontent.com":
                    logo_of[(cc, key)] = url
                else:
                    del logo_of[(cc, key)]
                    log(f"  ! {cc} {key}: logótipo sem cópia no repositório, ignorado: {url}")
    # logótipos novos do imgur ainda sem cópia: descarregar para logos/imgur/
    no_copy = sorted({u for u in logo_of.values() if "i.imgur.com" in u})
    if no_copy:
        log(f"- {len(no_copy)} logótipos do imgur sem cópia em logos/imgur/: {' '.join(no_copy)}")
    no_copy_us = sorted({u for (c, _), u in logo_of.items() if c == "US" and "i.imgur.com" not in u
                         and urllib.parse.urlparse(u).hostname != "raw.githubusercontent.com"})
    if no_copy_us:
        log(f"- {len(no_copy_us)} logótipos dos EUA sem cópia em logos/us/ext/: {' '.join(no_copy_us)}")
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
            display = [pretty(label)]
            display += [n for n in provider_names.get((cc, key), []) if n != display[0]]
            # nomes diferentes do mesmo canal ("Sky PREMIEREN +24" e "S Cinema
            # Premieren +24"): uma só entrada com todos os nomes, sem repetir a grelha
            ch = tv.find(f"channel[@id='{cid}']")
            if ch is not None:
                have = {d.text for d in ch.findall("display-name")}
                for n in display:
                    if n not in have:
                        ET.SubElement(ch, "display-name", lang=COUNTRIES[cc]["lang"]).text = n
                continue
            ch = ET.SubElement(tv, "channel", id=cid)
            for n in display:
                ET.SubElement(ch, "display-name", lang=COUNTRIES[cc]["lang"]).text = n
            if (cc, key) in logo_of:
                ET.SubElement(ch, "icon", src=logo_of[(cc, key)])
            programmes.append((cid, progs))
    if not chosen:
        sys.exit("Nenhuma fonte EPG respondeu – epg.xml não foi alterado.")

    # Canais sem programação em nenhuma fonte mas com logótipo (ex.: Ligue 1+ Pass
    # 1-10): entram só com os nomes e o logótipo, para o TiviMate mostrar o logótipo
    ids = {cid for cid, _ in chosen.values()}
    logo_only = {}
    for (cc, key), names in sorted(provider_names.items()):
        if (cc, key) in chosen or (cc, key) not in logo_of:
            continue
        label = pretty(min((n for n in names if " " in n), key=len, default=names[0]))
        cid = make_id(label, cc)
        if cid in ids:
            # o tvg-id do fornecedor às vezes é o de outro canal ("FRANCE 3 NOA FHD FR"
            # vem com "Novelas TV FR"): usa o nome do próprio canal e deixa de fora os
            # nomes que são de outros canais, para o TiviMate não os confundir
            names = [n for n in names if make_id(pretty(n), cc) not in ids]
            if not names:
                continue
            label = pretty(names[0])
            cid = make_id(label, cc)
            if cid in ids:
                continue
        ids.add(cid)
        logo_only[(cc, key)] = cid
        ch = ET.SubElement(tv, "channel", id=cid)
        for n in [label] + [n for n in names if n != label]:
            ET.SubElement(ch, "display-name", lang=COUNTRIES[cc]["lang"]).text = n
        ET.SubElement(ch, "icon", src=logo_of[(cc, key)])

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
    log(f"{args.epg}: {len(chosen)} canais, {sum(len(p) for _, p in programmes)} programas, "
        f"{len(logo_only)} canais só com logótipo")

    # Atualiza a lista
    rows, stats = [], {}
    for i, name, group, cc in channels:
        key = norm(name, cc)
        line = lines[i]
        tvg_id, src = chosen.get((cc, key), ("", ""))
        logo = logo_of.get((cc, key))
        if tvg_id or (cc, key) in logo_only:
            line = set_attr(line, "tvg-id", tvg_id or logo_only[(cc, key)])
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
