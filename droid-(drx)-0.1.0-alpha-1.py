import hashlib
import hmac
import json
import time
import ecdsa
import binascii
import os
import threading
import socket
import sys
import subprocess
import queue
import itertools
import select
from colorama import Fore, Style, init
import struct
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.kdf.argon2 import Argon2id
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
# OPRAVA A-6: ověřování podpisů přes OpenSSL. Knihovna cryptography už v
# závislostech byla (Argon2id a AES-GCM), SECP256K1 i Prehashed(SHA3-256)
# podporuje, takže formát podpisu ani adresy se nemění.
from cryptography.hazmat.primitives.asymmetric import ec, utils as asym_utils
from cryptography.exceptions import InvalidSignature
import getpass
import sqlite3
import bisect
import heapq
import multiprocessing
from collections import defaultdict, deque
# OPRAVA G-11: readline se nikde nevolá a statická analýza ho hlásí jako
# nepoužitý import - je ale importovaný PRO VEDLEJŠÍ EFEKT: pouhý import
# napojí readline na vstup input(), a tím převezme obsluhu editace řádku.
#
# NEODSTRAŇOVAT. Bez něj si input() neudržuje přehled o skutečné pozici
# kurzoru a mazání znaku terminál nepřekreslí správně - v příkazové řádce
# zůstávají "vypálené" znaky, které už nejde smazat. Projevuje se to hlavně
# u výpisů s ANSI sekvencemi (colorama) a u diakritiky, kde jeden znak není
# jeden bajt. Jako bonus fungují šipky a historie.
import readline  # noqa: F401 - importován pro vedlejší efekt (obsluha editace v input())
import signal
import ipaddress
from decimal import Decimal
import platform
import copy
from types import SimpleNamespace

init(autoreset=True)

PROJECT_NAME = "Droid"
TICKER = "DRX"
DECIMALS = 8
MAX_SUPPLY = 100_000_000 * (10 ** DECIMALS)
BLOCK_REWARD = 50 * (10 ** DECIMALS)
HALVING_INTERVAL_BLOCKS = 1_000_000
BLOCK_TIME_SECONDS = 60
COINBASE_MATURITY = 1000
MAX_REORG_DEPTH = 1000
# REFAKTOR (bez změny konsenzu): dřív `int(0.00000001 * (10 ** DECIMALS))`.
# Hodnota je při DECIMALS = 8 shodná - `1e-08 * 10**8` se v double zaokrouhlí
# přesně na 1.0, takže `int()` dalo 1. Důvod přepisu je trojí:
#
# 1) Byla to jediná konstanta, kde peníze procházely floatem. MAX_SUPPLY
#    i BLOCK_REWARD násobí celými čísly, tedy přesně, a zbytek kódu počítá
#    v nedělitelných jednotkách jako int.
# 2) Při DECIMALS < 8 by `int()` výsledek TIŠE zkrátil na 0 (0.00000001 * 10**6
#    = 0.01 -> 0). Z konsenzu by bez jediné chybové zprávy zmizela dolní mez
#    poplatku i částky a povolily by se transakce s nulovým poplatkem.
# 3) 1 vyjadřuje záměr přesněji: obě konstanty znamenají "jedna nejmenší
#    nedělitelná jednotka", a to je 1 vždy, nezávisle na DECIMALS.
#
# 1 = 0.00000001 DRX při DECIMALS = 8.
TX_FEE_MIN = 1
# ZMĚNA 1: horní limit transakčního poplatku (dřívější konstanta TX_FEE_MAX,
# 0,01 DRX) je odstraněn ÚPLNĚ a nenahrazuje ho žádná jiná konstanta ani jiný
# maximální limit. Po OPRAVĚ #6b (níže) už platil jen jako mempoolová politika
# v add_transaction() a při zadávání poplatku ve volbě 2 menu - nově neplatí
# ani tam. Jediné pravidlo pro poplatek v konsenzu (add_block, validate_fork,
# is_valid_chain) i v mempoolu je fee >= TX_FEE_MIN. Shora je poplatek omezený
# jen zůstatkem odesílatele, protože amount + fee musí být kryté.
#
# Konsenzus se touto změnou NEMĚNÍ (horní mez v něm po #6b už nebyla). Mění se
# jen to, co uzel přijme do mempoolu, přepošle a vytěží. Uzel se starším kódem
# transakci s poplatkem nad 0,01 DRX do svého mempoolu nepřijme ani nepřepošle,
# blok, který ji obsahuje, ale přijme.
#
# OPRAVA #6b (varianta A) - původní zdůvodnění odstranění horní meze z konsenzu
# (add_block, validate_fork, is_valid_chain):
#
# Důvod: jako konsenzuální pravidlo dělal strop 0,01 DRX z bloku s vyšším
# poplatkem NEPLATNÝ blok. Do bloku se vejde ~1 633 transakcí, takže absolutní
# strop poplatků byl 16,33 DRX/blok - a subsidy pod tuhle hodnotu klesá už
# u halvingu 2, tedy zhruba za 3,8 roku. Od té chvíle by strop, ne emise,
# určoval celý bezpečnostní rozpočet sítě. Druhý dopad: při zahlcení nemohla
# cena za místo v bloku vystoupat nad strop, takže aukce o blockspace v mine()
# (řazení podle -fee) degenerovala na pořadí příchodu podle timestampu - a to
# je zneužitelné, útočník si čas v povoleném okně posune a předběhne frontu.
#
# Konsenzus nově vynucuje jen dolní mez (fee >= TX_FEE_MIN). Horní mez není
# potřeba: poplatek je stejně shora omezený zůstatkem odesílatele, protože
# validace vyžaduje pokrytí amount + fee, takže inflace ani přetečení nehrozí.
#
# Tohle je hard fork. Uzel s tímhle kódem přijme blok, který by starý uzel
# odmítl. Musí být nasazeno před spuštěním sítě, ne po něm.
# REFAKTOR (bez změny konsenzu): dřív `int(0.00000001 * (10 ** DECIMALS))`,
# ze stejných důvodů jako u TX_FEE_MIN výš. 1 = jedna nejmenší nedělitelná
# jednotka, tedy 0.00000001 DRX při DECIMALS = 8.
MIN_TX_AMOUNT = 1
DIFFICULTY_ADJUSTMENT_INTERVAL = 144
# OPRAVA #15: TARGET_BLOCK_TIME odstraněn - nikde se nepoužíval (LWMA-3 si
# okno počítá z BLOCK_TIME_SECONDS a N přímo v calculate_expected_target).
# ZMĚNA 6 (HARD FORK): počáteční obtížnost zvýšena z 20 na 22 bitů.
#
# INITIAL_DIFFICULTY_BITS NENÍ jen "startovní" hodnota. Je to zároveň PODLAHA
# obtížnosti pro celou životnost sítě, protože FIXED_TARGET vystupuje ve čtyřech
# různých rolích:
#
#   1) target prvních DIFFICULTY_ADJUSTMENT_INTERVAL + 1 bloků - do té výšky
#      vrací calculate_expected_target() natvrdo FIXED_TARGET, takže LWMA-3
#      ještě vůbec nepočítá (prvních 145 bloků, při cílovém čase ~2,4 h),
#   2) strop targetu v LWMA-3: new_target = max(1, min(new_target, FIXED_TARGET)).
#      Tohle je ta podstatná role - ať hashrate spadne jakkoli hluboko,
#      obtížnost se nikdy nedostane pod tuhle mez,
#   3) povinná vlastnost genesis bloku (_is_valid_chain_inner vyžaduje
#      current_block.target == FIXED_TARGET),
#   4) síťové minimum v brankách, které blok platí ještě před plnou validací:
#      _pow_branka_bloku() (a přes ni cesty 'response_blocks', 'new_block'
#      i _store_fork_batch_inner()), add_orphan_block() a handler 'new_block'
#      shodně odmítají target volnější než FIXED_TARGET.
#
# Důvod změny je měřený, ne odhadnutý. Na Poco X7 Pro (Dimensity 8400 Ultra)
# dává uzel v Termuxu ~400 kH/s, takže:
#
#   20 bitů = 2^20 = 1 048 576 hashů na blok  -> ~2,6 s
#   22 bitů = 2^22 = 4 194 304 hashů na blok  -> ~10,5 s
#
# Při BLOCK_TIME_SECONDS = 60 je 2,6 s o více než řád vedle. Prvních 145 bloků
# by se vytěžilo prakticky okamžitě a LWMA-3 by nad nimi startovala z hodnoty,
# která s realitou sítě nemá nic společného. Druhá polovina problému je role (2):
# při výpadku nebo nepravidelné těžbě LWMA-3 target zvyšuje, dokud nenarazí na
# strop - a strop na 20 bitech znamená, že i jediný mobil pak chrlí bloky po
# pár vteřinách.
#
# POZOR, 22 BITŮ CÍL NEŘEŠÍ, JEN ZMENŠUJE ODSTUP: 10,5 s je pořád ~6x pod
# BLOCK_TIME_SECONDS. Na 60 s při 400 kH/s by bylo potřeba 2,4e7 hashů, tedy
# log2(400000 * 60) = 24,5 bitu. Hodnota je zvolená jako kompromis - podlaha
# nemá odpovídat výkonu jednoho konkrétního telefonu, protože pak by se na
# slabším zařízení nedal vytěžit ani první blok. O skutečný cílový čas se po
# 145. bloku stará LWMA-3; tohle je jen mez, pod kterou nesmí klesnout.
#
# JE TO ZMĚNA KONSENZU (HARD FORK), a to OBOUSMĚRNÁ:
#   - uzel s tímhle kódem odmítne každý blok vytěžený na 20bitovém targetu
#     (neprojde ani PoW brankou, ani kontrolou expected_target),
#   - starý uzel odmítne genesis blok s novým targetem a tím celý řetězec.
# Patří tedy do kódu PŘED spuštěním sítě, ne po něm - stejně jako OPRAVA A-4,
# OPRAVA #6b / ZMĚNA 1, OPRAVA #14, OPRAVA N-3 a OPRAVA AUDIT-10.
#
# Genesis blok byl kvůli tomu znovu vytěžen, viz GENESIS_NONCE níž.
INITIAL_DIFFICULTY_BITS = 22
FIXED_TARGET = (1 << 256) >> INITIAL_DIFFICULTY_BITS

BLOCKCHAIN_DB = 'blockchain.db'
WALLETS_FILE = 'wallets.json.enc'
MEMPOOL_DB = 'mempool.db'
PEERS_FILE = 'peers.json'
ADDRESS_BOOK_FILE = 'address_book.json.enc'
BLACKLIST_FILE = 'blacklist.json'
P2P_HOST = '0.0.0.0'

GENESIS_ADDRESS = "DRXf4fc20af1250719b255554a2382feb510b8022c7eeb0376f84b8cc03a1fce1b6a3fd1e3f"
GENESIS_ADDRESS_EXPECTED_HASH = "8f46fa50b96e72c0156c846b6ac7b48445b17217d70be4c639b0f9f9582b71b2"
GENESIS_TIMESTAMP = 1785614400
# Samotný state_root genesis bloku se dopočítá automaticky v create_genesis_block().
# Při JAKÉKOLI změně obsahu genesis bloku (adresa, částka, čas, data, target,
# version, chain_id) je nutné obě hodnoty níže znovu vytěžit a přepsat.
# ZMĚNA 6 (hard fork): zvýšení INITIAL_DIFFICULTY_BITS z 20 na 22 změnilo
# FIXED_TARGET, a protože target je POLE HLAVIČKY (Block.compute_hash() ho balí
# do 32 bajtů mezi nonce a previous_hash), změnil se i hash genesis bloku.
# Genesis byl proto znovu vytěžen na nový target:
#   tx_id genesis  d28c60c67232023b9eb14e91517a6ef2ba57bf42984cf809b382c89652c5f254 (beze změny)
#   merkle root    1454f46084c0419623620b5b6b3cf07b327d054420f79abc93cb0fa9edf48199 (beze změny)
#   state_root     c6253efc7a5da68207e84ab2d5d238e33c23e9945cf411c0c622cb0adfca380a (beze změny)
#   nonce 1110404 -> hash 000000175a92851df760840381db6b0dbb63d68242f6d6b9d1366e18c776b006
#
# Změnil se tedy VÝHRADNĚ nonce a hash. tx_id ani merkle root na targetu
# nezávisí (ten do get_signing_data() ani do listu Merkle stromu nevstupuje)
# a state_root stojí na SMT účtů, immature odměně a total_supply, ne na hlavičce.
#
# Nonce je NEJNIŽŠÍ, který nový target splňuje - hledalo se postupně od nuly,
# stejnou konvencí jako u předchozích hodnot.
#
# OPRAVA A-4 (hard fork): předtím zavedení příznakového bajtu
# v encode_optional_field() změnilo podepisovaná data, a tím tx_id genesis
# transakce i merkle root bloku; tehdy platily nonce 977525 a hash
# 000005313da262cac258328eb23d83cf86a3b16764cc4b00a5f9eaefb5404ff8 (a před nimi
# nonce 3622, hash 0000092d03... pro staré kódování). Obojí by s tímhle kódem
# neprošlo - hodnoty jsou tu jen jako záznam, proč se genesis těžil opakovaně.
#
# verify_genesis_block() i CHECKPOINTS[0] projdou (checkpoint se z téhle
# konstanty odvozuje, takže se nemusí přepisovat zvlášť).
GENESIS_NONCE = 1110404
GENESIS_BLOCK_EXPECTED_HASH = "000000175a92851df760840381db6b0dbb63d68242f6d6b9d1366e18c776b006"
GENESIS_AMOUNT = 50 * (10 ** DECIMALS)

MAX_BLOCK_SIZE_BYTES = 1 * 1024 * 1024
MAX_MEMPOOL_SIZE_BYTES = 10 * 1024 * 1024
MAX_PENDING_TX_PER_ADDRESS = 100

# OPRAVA D-01: orphan pool byl omezený POČTEM položek (100) a neměl expiraci.
# Počet položek je špatná jednotka: blok smí mít až MAX_BLOCK_SIZE_BYTES, takže
# 100 položek je ve skutečnosti až 100 MiB serializovaných dat - a naparsovaný
# blok v paměti zabírá násobek toho. Strop je proto nově v bajtech a je odvozený
# od MAX_BLOCK_SIZE_BYTES, ne zvolený nazdařbůh: 16 plných bloků je dost na
# překlenutí běžného přeuspořádání, ale je to rozpočet, který uzel na telefonu
# unese. Expirace řeší druhou půlku problému - orphan má smysl jen do chvíle,
# než dorazí jeho rodič.
MAX_ORPHAN_POOL_BYTES = 16 * MAX_BLOCK_SIZE_BYTES
ORPHAN_EXPIRATION = 600

# OPRAVA D-03: část mempoolu je rezervovaná pro transakce s NADMEDIÁNOVOU
# sazbou (poplatek/bajt). Samotné vytěsňování (viz _evict_for) už sice zajistí,
# že plný mempool není absolutní bariéra, ale rezerva navíc znamená, že
# levný spam nedokáže obsadit ani celý zbytek: nad hranicí
# MAX_MEMPOOL_SIZE_BYTES - MEMPOOL_PREMIUM_RESERVE_BYTES se podprůměrně
# platící transakce nedostane vůbec a nemusí se kvůli ní nic vytěsňovat.
MEMPOOL_PREMIUM_RESERVE_BYTES = MAX_MEMPOOL_SIZE_BYTES // 10

# OPRAVA A-3: sync_buffer.db neměl žádné omezení velikosti - orphan
# pool má MAX_ORPHAN_POOL_BYTES + expiraci, mempool MAX_MEMPOOL_SIZE_BYTES,
# peer_listen_ports MAX_PEER_LISTEN_PORTS + TTL, locator MAX_LOCATOR_HASHES,
# jen buffer forku neměl nic.
# (OPRAVA G-05/G-06: tady stálo, že sync_buffer.db byl "jediná neomezená
# struktura v kódu". To NEPLATILO - neomezené byly i p2p_log a blacklist,
# obojí vzdáleně vyvolatelné. Formulace je opravená, protože takové tvrzení
# bere čtenář příštího auditu jako hotovou informaci a nekontroluje ho.
# Dnes má strop p2p_log (MAX_P2P_LOG_ENTRIES) i blacklist
# (MAX_BLACKLIST_ENTRIES + periodické prořezávání).)
# _store_fork_batch_inner() zapisoval dávku za
# dávkou bez počítadla, zatímco replace_chain() na druhém konci tvrdě odmítne
# cokoli delšího než MAX_REORG_DEPTH + 1. Uzel tedy uměl zapsat 2 500 bloků,
# z toho 1 499 s předem jistým výsledkem "odmítnuto", a pak celý buffer zahodit
# - při plných blocích ~2,5 GB zápisu na flash telefonu za jeden útok. Cena pro
# útočníka je přitom jen PoW, žádné platné transakce ani state root: do bufferu
# se blok dostane po třech kontrolách (rozsah targetu, meets_difficulty,
# návaznost uvnitř dávky).
#
# Strop je dvojí, protože ani jeden sám nestačí: hloubkový drží buffer v mezích,
# které replace_chain() vůbec může přijmout, bajtový chrání flash i v případě,
# že hloubku neumíme spočítat (fork_start_index není znám) nebo jsou bloky plné.
MAX_SYNC_BUFFER_BYTES = (MAX_REORG_DEPTH + 1) * 64 * 1024

# OPRAVA Z-2 (audit 15. 10. 2026, nález 2): strop výše je rozpočet na FLASH, ne
# na RAM. process_sync_buffer() z bufferu staví objekty a ty stojí násobek:
# naměřeno 62,3 MiB na disku -> 195 MiB RSS, tedy 3,1x (z toho 1,8x objekty,
# zbytek byla dvojí reprezentace, kterou ta oprava odstranila).
#
# Je to tedy HRANICE PAMĚTI, ne jen zápisu, a kdo bude MAX_SYNC_BUFFER_BYTES
# někdy zvedat, musí počítat s tímhle násobkem - na telefonu rozhoduje on, ne
# velikost souboru. Konstanta je jen dokumentační, nikde se nepočítá: skutečnou
# mez drží MAX_SYNC_BUFFER_BYTES a po opravě i to, že se v paměti nedrží dvě
# reprezentace téhož bufferu naráz.
SYNC_BUFFER_RAM_FACTOR = 1.8

# OPRAVA AUDIT-2026-1 (audit 8. 10. 2026, nález 1): strop výše je odvozený od
# 64 kB na blok, zatímco blok smí mít MAX_BLOCK_SIZE_BYTES, tedy 1 MiB. Nad
# PLNÝMI bloky se do bufferu vejde jen ~62 bloků (naměřeno 1 049 157 B na řádek),
# přestože hloubkový strop je MAX_REORG_DEPTH = 1000. Fork hlubší než těch ~62
# bloků tedy JDE stáhnout jen po částech - a část sama o sobě naši větev
# nepřebije.
#
# Strop se ZÁMĚRNĚ nezvyšuje: (MAX_REORG_DEPTH + 1) * MAX_BLOCK_SIZE_BYTES je
# ~1 GB zápisu na flash telefonu, což je cílová platforma. Místo toho se
# nedokončitelný reorg pojmenuje: viz _prefix_muze_vyhrat() a _prefix_neprebiji().
#
# Backoff brání tomu, aby se uzel o tentýž nedosažitelný fork pokoušel každých
# 10 s (perioda sync_chain_periodically). Bez něj se měřilo ~63 MiB staženo
# a zapsáno na flash každých 10 s, tedy ~528 GiB za den, donekonečna a bez banu.
FORK_UNWINNABLE_BACKOFF_SECONDS = 600

# OPRAVA T-1 (Nález 1, 2/2): účetnictví bufferu měřilo JEN sloupec
# `transactions`. Pole hlavičky (previous_hash, merkle_root, state_root) přitom
# procházejí tvarovou brankou pouze přes isinstance(..., str), takže blok
# s prázdným seznamem transakcí a balastem ve state_root se do bufferu zapsal
# s účtovanou velikostí 12 B. Naměřený poměr skutečnost/účetnictví byl
# 251 221x - bajtový strop se tedy neuplatnil vůbec a zbyl jen hloubkový
# (1001 řádků), tedy řádově 10 GB zápisu na flash proti zamýšleným 63 MB.
#
# Jediný zdroj pravdy o velikosti řádku je proto tahle dvojice: SQL verze pro
# změřený obsah tabulky a Python verze pro odhad dávky PŘED zápisem. Obě musí
# dávat totéž, jinak by se strop dal obejít v mezeře mezi nimi - proto jsou
# vedle sebe a obě vycházejí z téhož seznamu sloupců.
#
# Měří se BAJTY, ne znaky: LENGTH() nad TEXTem vrací počet znaků, takže by
# jediný čtyřbajtový znak ve state_root účtoval za 1 a dal útočníkovi 4x páku
# na skutečný zápis. CAST(... AS BLOB) vrátí délku v bajtech kódování UTF-8.
# COALESCE je nutné u každého sloupce zvlášť: LENGTH(NULL) je NULL a NULL
# v součtu udělá z CELÉHO řádku nulu, tedy přesně opačnou chybu, než jakou
# tenhle strop opravuje.
SYNC_BUFFER_COLUMNS = ('block_index', 'timestamp', 'transactions', 'previous_hash',
                       'target_hex', 'nonce', 'block_hash', 'merkle_root',
                       'version', 'chain_id', 'state_root')
SYNC_BUFFER_BYTES_SQL = (
    "SELECT COALESCE(SUM("
    + " + ".join(f"LENGTH(CAST(COALESCE({sloupec}, '') AS BLOB))" for sloupec in SYNC_BUFFER_COLUMNS)
    + "), 0) FROM sync_blocks"
)

def subsidy_po_halvingu(halvings):
    """OPRAVA AUDIT-2026-18: BLOCK_REWARD // (2 ** halvings) v konstantním čase.

    `2 ** halvings` je neomezené: block.index smí být až 2**63-1 (viz
    Block.from_dict), takže halvings dosáhne ~9,2e12 a výsledkem je celé číslo
    o 9,2e12 bitech, tedy >1 TB paměti. Naměřeno v update_state_with_block():
    index 2**62 -> MemoryError po 11,4 s, index 10**15 -> 5,3 s a 125 MB.

    Dosažitelné ze sítě to NENÍ - add_block(), _validate_fork_inner() i
    _is_valid_chain_inner() vynucují návaznost indexů (block.index ==
    previous.index + 1) JEŠTĚ PŘED tímhle výpočtem, takže halvings je shora
    omezené skutečnou výškou řetězce. update_state_with_block() je ale veřejná
    metoda a jediná, která si tu mez nehlídá sama - a spoléhat se na disciplínu
    volajících je přesně to, co OPRAVA #4 a D-15 zakazují.

    Výsledek je BIT ZA BITEM shodný s původním výrazem, takže konsenzus se
    nemění: pro halvings >= BLOCK_REWARD.bit_length() je celočíselné dělení
    nulové tak jako tak (komentář u OPRAVY AUDIT-10 to říká pro halving 33).
    """
    if halvings >= BLOCK_REWARD.bit_length():
        return 0
    return BLOCK_REWARD >> halvings


def sync_row_bytes(hodnoty):
    # Python protějšek SYNC_BUFFER_BYTES_SQL nad týmž řádkem PŘED zápisem.
    # SQLite čísla při CASTu nejdřív vyrenderuje do textu, takže str(v) je
    # tady ekvivalent - a NULL (None) nepřispívá ničím.
    celkem = 0
    for v in hodnoty:
        if v is None:
            continue
        celkem += len(v.encode('utf-8')) if isinstance(v, str) else len(str(v).encode('utf-8'))
    return celkem

# OPRAVA D-04: add_block() měl jediný pokus o zámek s timeout=5 a při vypršení
# platný blok zahodil. Blok má přednost před transakcemi, takže se o zámek
# pokouší opakovaně; celkový rozpočet je 3 × 5 s.
ADD_BLOCK_LOCK_TIMEOUT = 5
ADD_BLOCK_LOCK_RETRIES = 3
# OPRAVA #15 (revidováno): CONFIRMATIONS_THRESHOLD byl původně odstraněn jako
# mrtvý kód, protože se jeho JMÉNO nikde nepoužívalo. To ale byla nedostatečná
# kontrola: obarvování počtu potvrzení ve format_confirmations() existovalo,
# jen mělo hodnotu opsanou natvrdo jako "1000".
#
# Práh říká, že blok je DEFINITIVNÍ, tedy chráněný proti reorgu.
#
# V uzlu existují DVA systémy počítání potvrzení a každý odpovídá jinému
# pravidlu konsenzu:
#
#   1) Hloubka bloku - blok potvrzuje sám sebe, nový blok má 1 potvrzení.
#      get_confirmations() = max_block_index - block_index + 1
#      Porovnává se s MAX_REORG_DEPTH, protože reorg_depth ve validate_fork()
#      počítá TÝMŽ vzorcem: max_block_index - fork_index + 1. Blok tedy leží
#      v přepisovatelném rozsahu právě když N <= MAX_REORG_DEPTH, a první
#      nedosažitelná hloubka je MAX_REORG_DEPTH + 1.
#      Používají volby 10, 11, 12 a 13.
#
#   2) Počet bloků NAD blokem - vrchol řetězce má 0.
#      Porovnává se s COINBASE_MATURITY, protože zrání se řídí pravidlem
#      target_index = block.index - COINBASE_MATURITY (update_state_with_block).
#      Používá volba 14 a znamená, že odměna je utratitelná.
#
# Jednička se proto jednou přičítá a jednou ne. Není to nedůslednost: každá
# strana počítá tak, jak počítá pravidlo, které zobrazuje.
#
# Obojí ve výsledku říká "reorg to už nesmaže", ale jsou to dvě NEZÁVISLÉ cesty
# ke stejnému závěru. Že vycházejí na stejný blok, drží výhradně na tom, že
# COINBASE_MATURITY == MAX_REORG_DEPTH. Kdyby se rozešly:
#   - vyšší MAX_REORG_DEPTH -> coinbase je utratitelná DŘÍV, než je definitivní,
#     takže ji reorg umí smazat i po odemčení,
#   - nižší MAX_REORG_DEPTH -> odměna leží zamčená déle, než je nutné.
# Test v test_opravy.py na rozejití upozorní. Je to varování, ne zábrana -
# konstanty se rozejít můžou, ale musí to být rozhodnutí, ne přehlédnutí.
CONFIRMATIONS_THRESHOLD = MAX_REORG_DEPTH + 1
NTP_SERVERS = ['pool.ntp.org', 'time.nist.gov', 'time.google.com']
# OPRAVA #18: parametry pro medián a tvrdý strop NTP offsetu.
# MAX_NTP_OFFSET_SECONDS je záměrně menší než akceptační okno bloku (+600 s),
# aby posunutý čas nedokázal vystrčit bloky uzlu mimo to okno.
MIN_NTP_SOURCES = 2
NTP_AGREEMENT_SECONDS = 60
MAX_NTP_OFFSET_SECONDS = 300
LAST_BLOCKS_TO_KEEP = 1200
MAX_PEERS = 20

# OPRAVA D-08: tabulka peerů se nikdy neuvolňovala. Handshake je zdarma a bez
# identity, takže 20 zpráv z 20 IP adres ji zaplnilo a od té chvíle se do ní
# nedostal ŽÁDNÝ poctivý uzel - klasický eclipse. Jediné cesty ven byly detekce
# připojení k sobě samému, změna naslouchacího portu a ruční smazání
# uživatelem; žádná eviction při nedostupnosti, žádná diverzita podsítí,
# žádné skóre. Nefunkční peer v tabulce zůstal napořád.
#
# MAX_PEERS_PER_SUBNET: jedna /16 (u IPv6 /32) nesmí obsadit všechna místa.
#   Získat 20 adres v jedné podsíti je pro útočníka levné, získat je ve 20
#   různých podsítích řádově dražší.
# PROTECTED_PEER_SLOTS: místa vyhrazená pro peery zadané ručně (peers.json,
#   volba v menu). Uzel tak jde vždycky zachránit i z plné tabulky.
# PEER_STALE_SECONDS: po jak dlouhé nečinnosti je peer kandidátem na vytlačení.
MAX_PEERS_PER_SUBNET = 3
PROTECTED_PEER_SLOTS = 4
# OPRAVA G-10: strop tabulky peerů pro RUČNÍ zadání. Ruční peer záměrně obchází
# _can_admit_locked() (je to záchranná cesta z eclipse útoku, kterou nesmí
# zablokovat plná tabulka), ale úplná absence horní meze znamenala, že self.peers
# i protected_peers mohly růst bez omezení. PROTECTED_PEER_SLOTS je tedy nově
# skutečná kvantifikovaná rezerva: ručně smí tabulka přerůst právě o tolik.
MAX_MANUAL_PEERS_TOTAL = MAX_PEERS + PROTECTED_PEER_SLOTS
PEER_STALE_SECONDS = 1800

# peer_listen_ports je branka důvěry z OPRAVY #10 - handle_message propouští
# cokoli od IP, která v něm figuruje. Původně nebyl omezený MAX_PEERS ani se
# nikdy nečistil, takže každá IP, která kdy poslala handshake, zůstala
# důvěryhodná NAVŽDY a slovník rostl bez omezení (pomalý únik paměti).
MAX_PEER_LISTEN_PORTS = 4 * MAX_PEERS
PEER_LISTEN_PORT_TTL = 3600

# OPRAVA U-20 (audit 7. 10. 2026, nález 2): evidence je nově klíčovaná dvojicí
# (IP, node_id), aby se za jednu IP vešlo víc uzlů (dva uzly na jednom VPS, dvě
# instance za jedním NATem s různými porty). Tím ale vzniká nová cesta k
# zahlcení, kterou dřívější klíčování podle samotné IP nemělo: jedna IP mohla
# obsadit právě jeden slot, zatímco teď si jich útočník může opakovaným
# handshakem s vymyšlenými node_id vyrobit libovolně mnoho a vytlačit z branky
# důvěry poctivé uzly. Strop na JEDNU IP to zavírá; hodnota odpovídá duchu
# MAX_PEERS_PER_SUBNET (3), jen s jedním místem navíc pro přechodný stav
# "uzel právě změnil naslouchací port".
MAX_LISTEN_PORTS_PER_IP = 4

# OPRAVA #1: původní limit byl 10 požadavků za 1 sekundu na IP, přičemž každá
# P2P zpráva je samostatné TCP spojení (_send_to_single_peer se připojí, pošle,
# zavře). Běžné stahování řetězce po dávkách proto vyčerpalo rozpočet během
# ~100 bloků a dva POCTIVÉ uzly se na LAN, localhostu nebo rychlé mobilní síti
# navzájem TRVALE zablokovaly - blacklist byl bez expirace a ukládal se na disk.
#
# Nově token bucket: RATE_LIMIT_BUCKET_CAPACITY je povolený burst,
# RATE_LIMIT_REFILL_PER_SECOND ustálený strop spojení za sekundu. Při RTT 20 ms
# a sériové komunikaci dělá sync ~18 spojení/s. Trvalý ban je nahrazen dočasným
# (BAN_DURATION_SECONDS) a uděluje se až po dlouhodobém překračování, ne po
# prvním překročení burstu.
#
# OPRAVA W-2 (audit 9. 10. 2026, nález N-2): hodnoty zvýšeny z 200 / 30 / 600.
# Rozpočet se počítá po ZPRÁVÁCH (ETAPA 2), a s přeposíláním transakcí a bloků
# (viz P2PNode._preposli_sousedum) jich od jednoho poctivého peera přibývá
# tolik, kolik jich síť vyrobí - při plném využití bloku
# MAX_BLOCK_SIZE_BYTES / TYPICKA_VELIKOST_TX_BYTES za BLOCK_TIME_SECONDS, tedy
# ~27 zpráv/s. Spolu se syncem (~18-20/s) to je nad původních 30/s, takže by si
# dva poctivé, plně vytížené uzly navzájem vyčerpaly rozpočet a po
# RATE_LIMIT_ABUSE_THRESHOLD si udělily ban - doslova failure mode OPRAVY #1,
# jen o patro výš. Nová hodnota je součet obou složek s rezervou.
#
# DoS ochranu to neruší: objem z jedné IP dál drží INBOUND_BYTES_PER_SECOND
# (2 MiB/s), souběžná spojení MAX_INBOUND_PER_IP a drahé dotazy vlastní, řádově
# přísnější rozpočet (EXPENSIVE_*). 90 zpráv/s po ~630 B je ~56 kB/s, tedy
# hluboko pod bajtovým stropem.
RATE_LIMIT_BUCKET_CAPACITY = 400
RATE_LIMIT_REFILL_PER_SECOND = 90.0
RATE_LIMIT_ABUSE_THRESHOLD = 20.0 * RATE_LIMIT_REFILL_PER_SECOND

# Samostatný, řádově přísnější rozpočet pro drahé dotazy (čtou z DB a generují
# velké odpovědi). Dřív spadaly do stejného limitu jako levné zprávy.
EXPENSIVE_BUCKET_CAPACITY = 40
EXPENSIVE_REFILL_PER_SECOND = 4.0

BAN_DURATION_SECONDS = 3600
BAN_DURATION_PROTOCOL = 24 * 3600

# OPRAVA G-05: strop P2P logu. Fronta neměla maxsize a vyprazdňovala se JEDINĚ
# ručně z menu (volba 19) - jiný odtok neexistoval. Uzel běžící bez dozoru,
# tedy v normálním provozním stavu, paměť nikdy neuvolnil. Přitom skoro každá
# přijatá zpráva zapíše aspoň řádek, a to VČETNĚ odmítnutých (neznámý typ,
# chybějící 'data', vyčerpaný rate limit, neprošlá branka důvěry). Útočník
# tedy nepotřebuje platná data, PoW, minci ani zůstatek: měřením vyšlo 109 B
# na odmítnutou zprávu, což při trvalém stropu rate limiteru (30 zpráv/s)
# dělá 3,2 kB/s = 271 MB za den z JEDINÉ IP. Na telefonu OOM kill.
# 1000 řádků je víc, než kdo v menu přečte, a shora omezuje log na ~110 kB.
MAX_P2P_LOG_ENTRIES = 1000

# OPRAVA N1 (audit 10. 10. 2026, nález N1): strop POČTEM řádků nestačí.
#
# Do řádku se interpolují řetězce od protistrany - msg_type, software_version
# a hlavně text výjimky z Block.from_dict / Transaction.from_dict, který nese
# syrovou hodnotu pole ("Target není kanonický hex řetězec: {raw_target!r}",
# "dodané tx_id '{supplied_tx_id}'"). Žádný z nich neměl délkovou mez: komentář
# výše počítá se 109 B na řádek, naměřeno 200 099 B, tedy 1836x víc. Při
# MAX_MESSAGE_SIZE (10 MiB) na zprávu je ustálená spotřeba 1000 x 10 MiB =
# 9,8 GB, a log se vyprazdňuje JEDINĚ ručně z menu (volba 19) - uzel běžící bez
# dozoru, tedy v normálním provozním stavu, paměť nikdy neuvolní. Na telefonu
# OOM kill. Cena pro útočníka je nula: stačí jeden handshake a pak zprávy
# s dlouhým 'type', které se stejně odmítnou (odmítnutá zpráva taky loguje).
#
# Je to táž chyba, kterou OPRAVA D-01 pojmenovala u orphan poolu ("Počet
# položek je špatná jednotka") a OPRAVA A-3 u sync bufferu; k logu se
# nepropsala. Strop je proto nově dvojí a rozhoduje ten bajtový:
#
#   MAX_P2P_LOG_LINE_CHARS - tvrdý ořez JEDNOHO řádku, aby žádná jediná hláška
#     nemohla rozpočet vyčerpat sama (a aby ořez nemusel řešit volající),
#   MAX_P2P_LOG_BYTES - strop celého logu, měřený v BAJTECH kódování UTF-8.
#     Ne ve znacích: jeden čtyřbajtový znak by účtoval za 1 a dal útočníkovi
#     4x páku na skutečnou paměť - táž úvaha jako u SYNC_BUFFER_BYTES_SQL.
#
# 256 kB je víc, než kdo v menu přečte, a na telefonu je to zanedbatelné.
# Oba stropy platí současně s MAX_P2P_LOG_ENTRIES; vytěsňuje se nejstarší.
MAX_P2P_LOG_LINE_CHARS = 512
MAX_P2P_LOG_BYTES = 256 * 1024

# Délka hodnoty od protistrany vložené do jedné hlášky. Ořez celého řádku je
# tvrdá pojistka, tenhle ořez je kvůli ČITELNOSTI: bez něj by z hlášky zbyl
# jen útočníkův balast a ořízlo by se to podstatné (IP odesílatele, důvod),
# protože hodnota bývá uprostřed věty, ne na konci.
MAX_LOG_VALUE_CHARS = 120

# Žádný legitimní typ zprávy delší není - nejdelší je 'response_full_chain'
# (20 znaků). Delší msg_type se odmítá hned, tedy dřív, než se vůbec dostane
# do logu nebo do tvarové branky _data_shape_ok().
MAX_MSG_TYPE_LEN = 32

# OPRAVA W-2 (audit 9. 10. 2026, nález N-2): strop evidence už přeposlaných
# bloků a transakcí. Je to jediná nová struktura, kterou přeposílání zavádí,
# takže musí mít mez hned od začátku - všechny ostatní evidence v uzlu ji mají
# (MAX_P2P_LOG_ENTRIES, MAX_BLACKLIST_ENTRIES, MAX_PEER_LISTEN_PORTS) a každá
# z nich ji dostala až po nálezu, že bez ní roste donekonečna.
#
# Klíč je dvojice (druh, hash/tx_id), tedy ~75 B na položku; 4096 položek je
# ~300 kB. Rozměr je odvozený od toho, co se přes uzel protočí: plný mempool
# má ~16 700 transakcí a blok ~1 660, takže 4096 pokrývá několik minut provozu,
# což je řádově víc, než kolik trvá, než se táž položka může vrátit po smyčce.
MAX_RELAY_SEEN_ENTRIES = 4096

# OPRAVA G-06: strop a perioda úklidu blacklistu. Slovník se nikdy neprocházel
# kvůli úklidu - expirovaný záznam zmizel jedině tehdy, když se náhodou znovu
# ozvala TÁŽ IP (is_blacklisted). IP, která se už nikdy neozve, zůstala
# v paměti i v souboru napořád. Útočník s jediným /64 prefixem má 2^64 adres a
# každou umí zabanovat jedním protokolovým přestupkem (třeba handshake s cizím
# chain_id), tedy prakticky zdarma. Strop je proto tvrdý: při překročení
# vypadnou bany s nejbližší expirací (trvalé bany od uživatele nikdy).
# 2048 položek je pro telefon s MAX_PEERS = 20 bohatě dost; proti útočníkovi
# s celým /64 prefixem neubrání ŽÁDNÁ velikost, takže strop reálnou ochranu
# neoslabuje - blacklist je proti opakovaným provinilcům z pár adres.
MAX_BLACKLIST_ENTRIES = 2048
# Rezerva nad stropem. Bez ní by se při zaplněném blacklistu musel při KAŽDÉM
# banu protřídit celý slovník (O(N log N) na jeden ban - naměřeno 0,78 s na
# 6500 banů, tedy nový CPU žrout na téže cestě, kterou má oprava zlevnit).
# S rezervou se ořez provede jednou za BLACKLIST_CAP_SLACK banů a amortizovaná
# cena je O(1). Překročení stropu je tím pádem přechodné a shora omezené.
BLACKLIST_CAP_SLACK = 256
BLACKLIST_PRUNE_INTERVAL = 300.0

# OPRAVA K-2 (audit 21. 10. 2026, nález 2): strop a perioda úklidu pro kbelíky
# rychlostních limitů. Byly to JEDINÉ struktury klíčované IP adresou v téhle
# třídě bez tvrdého stropu - blacklist, peer_listen_ports, mempool_offer_cursor
# i fork_slot_cooldown ho mají, a každá ho dostala až po nálezu, že bez něj
# roste donekonečna (viz MAX_BLACKLIST_ENTRIES a MAX_RELAY_SEEN_ENTRIES).
#
# Původní ochrana byla jen "nad 1000 položkami prořež podle stáří". To má dvě
# vady: (a) při čerstvém provozu nevyřadí nic a slovník roste dál, (b) je O(n)
# a spouštěla se při KAŽDÉM volání nad prahem, takže celkový náklad byl
# kvadratický. Naměřeno na is_connection_rate_limited(): 95 µs na kontrolu při
# 3 000 IP, 1 061 µs při 15 000 IP, 184 B na položku. A tahle konkrétní cesta
# se volá na KAŽDÉ přijaté TCP spojení - před handshakem, před _inbound_admit()
# a bez jakékoli jiné branky, takže útočníkovi stačí jediný /64 prefix a nemusí
# poslat ani bajt dat.
#
# 4096 položek je ~750 kB na kbelík. Rozměr je odvozený od MAX_PEERS = 20 a
# MAX_INBOUND_CONNECTIONS = 64: poctivý uzel se do nízkých stovek vejde
# s velkou rezervou, takže ořez ho nikdy nepotká.
MAX_RATE_BUCKETS = 4096
# Rezerva nad stropem, úplně stejná konstrukce a stejný důvod jako
# BLACKLIST_CAP_SLACK: ořez se provede jednou za RATE_BUCKET_CAP_SLACK nových
# IP a amortizovaná cena je O(1) místo O(n) na každé volání.
RATE_BUCKET_CAP_SLACK = 512
# Perioda, se kterou se kbelíky prořezávají podle stáří (vrací paměť po
# odražené vlně). Jede ve stejném rytmu jako úklid blacklistu, jen hustěji -
# okna kbelíků jsou 60 až 300 s, ne hodiny.
RATE_BUCKET_PRUNE_INTERVAL = 60.0
# Okna stáří jednotlivých kbelíků. Odpovídají tomu, za jak dlouho se kbelík
# stejně dorovná na plnou kapacitu, takže vyhozená položka a položka ponechaná
# jsou od té chvíle k nerozeznání.
RATE_BUCKET_MAX_AGE = 60.0
RATE_BUCKET_MAX_AGE_LONG = 300.0
# Zápis na disk se dávkuje: ban_peer() volal save_blacklist() s KOMPLETNÍM
# slovníkem po každém jednotlivém banu, takže N banů znamenalo O(N^2)
# zapsaných bajtů (měřeno: 1500 banů = 59 kB souboru a 2,0 s čistého I/O).
# Na flash paměti telefonu je to navíc zbytečné opotřebení. Nově se změna jen
# označí a na disk ji odnese úklidové vlákno, nejvýš jednou za tento interval.
# 120 s: při plném blacklistu má soubor ~84 kB, takže i za trvalého útoku se
# na flash zapisuje nejvýš ~0,7 kB/s. Bany se nikdy neztratí - vypínací cesta
# i ruční zásahy z menu volají flush_blacklist(force=True).
BLACKLIST_FLUSH_INTERVAL = 120.0

# OPRAVA AUDIT-2026-8 (audit 21. 10. 2026, nález N3): táž dávka pro peers.json.
# Handler handshake volal save_peers() - tedy write + flush + fsync + os.replace -
# při KAŽDÉ zprávě, která tabulkou pohnula. A pohnout jí umí kdokoli: handshake
# je jediný typ vyňatý z branky důvěry a nespadá mezi drahé dotazy, takže na něj
# platí jen RATE_LIMIT_REFILL_PER_SECOND (90 zpráv/s na IP). Stačilo střídat
# deklarovaný listen_port a uzel pokaždé spadl do větve "tentýž uzel změnil
# port", přepsal self.peers a zapsal celý soubor znovu - přestože tabulka
# vypadala po každé dvojici zpráv stejně.
#
# Naměřeno: 0,99 zápisu na zprávu z jediné IP = 90 fsync/s a 0,38 GB/den;
# při plné tabulce 20 flapujících peerů 1 680 zápisů/s a 138 GB/den. Cena pro
# útočníka: zpráva o ~120 bajtech, bez PoW a bez zůstatku.
#
# 30 s místo 120 s jako u blacklistu: peers.json je o dva řády menší (~1 kB
# proti ~84 kB), takže i nejhorší případ vyjde na ~0,03 kB/s, a tabulka peerů
# je po nečekaném pádu cennější - je to jediná cesta zpátky do sítě.
# O změnu se nepřijde: vypínací cesta volá flush_peers(force=True).
PEERS_FLUSH_INTERVAL = 30.0

MAX_MESSAGE_SIZE = 10 * 1024 * 1024

# OPRAVA N-2: strop souběžných PŘÍCHOZÍCH spojení a lhůta na doručení celé zprávy.
# start_server() dřív spouštěl vlákno na každé spojení bez jakéhokoli stropu a
# timeout CONNECTION_IDLE_TIMEOUT platil na JEDNO recv(), takže 1 bajt za méně než
# 120 s držel spojení věčně. Z jediné IP přibývalo 60 + 5 spojení/s bez konce;
# po vyčerpání deskriptorů selhalo i otevření SQLite a smyčka accept() se točila
# na 100 % CPU (ověřeno testem t_bug2_slowloris.py).
MAX_INBOUND_CONNECTIONS = 64
# OPRAVA N-10: rozpočet odchozích pokusů vyvolaných zprávou 'new_peer'.
NEW_PEER_CONNECT_CAPACITY = 5
NEW_PEER_CONNECT_REFILL_PER_SECOND = 1.0 / 30
MAX_INBOUND_PER_IP = 4

# OPRAVA Z-1 (audit 15. 10. 2026, nález 1): příchozí sloty se daly obsadit
# natrvalo a nebylo z nich co vytěsnit.
#
# Accept smyčka znala jen dva stropy: MAX_INBOUND_CONNECTIONS (64) a
# MAX_INBOUND_PER_IP (4). Při překročení spojení prostě zavřela. Tři důsledky,
# a žádný z nich nestál útočníka víc než pár paketů:
#
#  1) Žádný strop na PREFIX. 4 sloty na IP x 16 adres = všech 64 slotů, a 16
#     adres je uvnitř jediného /64 zdarma. MAX_PEERS_PER_SUBNET existuje, ale
#     platí jen pro tabulku peerů v _can_admit_locked(), ne pro příchozí stranu.
#  2) Žádná REZERVA pro uzly, které už známe. Zavřená příchozí strana tedy
#     nebyla jen pro nové neznámé uzly - nedovolal se ani peer ze self.peers,
#     takže uzel přišel o push bloků i transakcí a zbyl mu jen pull jednou za
#     10 s (sync_chain_periodically).
#  3) Žádné VYTĚSŇOVÁNÍ. Tabulka peerů tohle řeší od OPRAVY D-08
#     (try_admit_peer vytlačí nejhoršího), příchozí sloty ne - plný stav byl
#     absolutní bariéra, přesně jak to D-08 popisuje u eclipse.
#
# Držení slotu navíc NENÍ omezené na CONNECTION_IDLE_TIMEOUT: ta lhůta platí na
# JEDNU zprávu. Handler handshaku vrací None, takže se čítač
# MAX_UNAUTHENTICATED_MESSAGES nuluje a jeden platný handshake za <120 s drží
# slot libovolně dlouho.
#
# MAX_INBOUND_PER_SUBNET: kolik spojení smí mít jeden prefix. Klíč počítá
#   subnet_key() (IPv4 /16, IPv6 /32), tedy TÁŽ funkce, jakou používá diverzita
#   tabulky peerů - dvě místa, která dělí síť na prefixy, se nesmějí rozejít.
#   Pro IPv6 je /32 ZÁMĚRNĚ hrubší než /64 z nálezu: útočník s celým /48 spadne
#   do jediného klíče. Při 8 na prefix potřebuje 6 různých /32, což je řádově
#   jiná cena než 6 různých /64.
# INBOUND_RESERVED_FOR_KNOWN: sloty, na které neznámý uzel nedosáhne vůbec.
#   Neznámí tedy obsadí nejvýš 64 - 16 = 48 slotů a 16 zůstává peerům ze
#   self.peers a protected_peers. Je to táž myšlenka jako PROTECTED_PEER_SLOTS
#   u tabulky peerů, jen o patro níž.
MAX_INBOUND_PER_SUBNET = 8
INBOUND_RESERVED_FOR_KNOWN = 16

# OPRAVA N2 (audit 10. 10. 2026, nález N2): strop SOUBĚŽNÝCH ODCHOZÍCH pokusů.
#
# MAX_INBOUND_CONNECTIONS výše omezuje jen PŘÍCHOZÍ stranu; odchozí vlákna
# neomezovalo nic. Přitom jedna příchozí zpráva uměla vyrobit právě jedno
# odchozí vlákno i socket: blok, který add_block() odmítne, ale jehož rodiče
# máme v DB, spustí send_to_peer({'type': 'request_chain_info'}), a to je nové
# vlákno a v něm až dva pokusy o connect() po 5 s (v get_connection() a znovu
# v _send_to_single_peer()). Útočná zpráva je REPLAY libovolného veřejného
# bloku - 870 B, žádné PoW navíc - a 'new_block' nebyla mezi drahými dotazy,
# takže platil jen RATE_LIMIT_REFILL_PER_SECOND (90 zpráv/s na IP). Naměřeno
# 1,00 vlákna a 1,00 socketu na zprávu, uvolní se až po ~10 s, tedy ~900
# souběžně z JEDNÉ IP a ~14 400 z šestnácti. Plný timeout si útočník zajistí
# tím, že v handshaku deklaruje naslouchací port na adrese, která SYN zahazuje
# místo odmítání.
#
# Semafor je tvrdá mez na počet vláken, která smí být v odchozím pokusu
# současně. Přetečení se jen ZAHODÍ a zaloguje: rozesílání i přeposílání
# (OPRAVA W-2) jsou best-effort a cokoli vynechaného doteče nejbližším kolem
# periodické synchronizace. 32 je nad tím, co potřebuje poctivý uzel - i plný
# broadcast je MAX_PEERS = 20 vláken.
MAX_OUTBOUND_SEND_THREADS = 32

# Jak často smí JEDNA IP vyvolat odchozí 'request_chain_info' tím, že nám pošle
# blok, který neumíme navázat. K ničemu jinému ta zpráva neslouží - zjistí se
# jí, jestli má protistrana delší řetězec - a jedna odpověď za tuhle dobu
# stačí: periodický sync se stejně ptá všech peerů každých 10 s. Dřív se
# posílala na KAŽDÝ odmítnutý blok, což byla ta pravá páka nálezu N2.
CHAIN_INFO_REQUEST_COOLDOWN = 30.0

# OPRAVA AUDIT-2026-3 (audit 8. 10. 2026, nález 3): příchozí strana neměla
# ŽÁDNÝ bajtový rozpočet. is_rate_limited() odebere jeden token za ZPRÁVU bez
# ohledu na velikost, takže zpráva o 1 B a zpráva o 10 MiB stály útočníka
# stejně. Naměřeno: 4 spojení z jedné IP (MAX_INBOUND_PER_IP) daly +41,7 MB RSS
# za 4 tokeny z kapacity 200; extrapolace na 64 spojení je ~667 MB RAM, tedy
# OOM kill na telefonu. Rozpočet existoval jen pro ODCHOZÍ drahé odpovědi
# (EXPENSIVE_BYTES_*), pro příchozí data žádný.
#
# Dvě nezávislé zábrany, protože ani jedna sama nestačí:
#
#  1) MAX_INBOUND_BUFFER_BYTES - strop SOUBĚŽNĚ rezervované přijímací paměti
#     přes všechna spojení dohromady. Rychlostní limit sám špičku paměti
#     neomezí: čtyři souběžná recv() po 10 MiB drží 40 MiB bez ohledu na to,
#     jak pomalu kapou. Rezervace se bere z OHLÁŠENÉ délky (msglen) ještě PŘED
#     alokací bufferu a drží se po celou dobu zpracování zprávy, protože
#     naparsovaný JSON je násobně větší než drát (měřeno 7 MiB -> 35 MiB).
#     24 MiB pustí tři souběžné plné dávky bloků (MAX_BATCH_BYTES = 8 MiB),
#     což je víc, než poctivý uzel potřebuje.
#
#  2) INBOUND_BYTES_* - per-IP kbelík, stejná konstrukce jako
#     EXPENSIVE_BYTES_*, jen opačným směrem. Omezuje dlouhodobý OBJEM z jedné
#     adresy, tedy opotřebení i CPU na parsování. 2 MiB/s je hluboko nad tím,
#     co potřebuje poctivý peer: moderní cesta (request_id) vrací odpovědi po
#     NAŠEM odchozím socketu, takže se jí tenhle rozpočet netýká vůbec; sem
#     spadají jen nevyžádané zprávy a odpovědi starších uzlů, které odpovídají
#     novým spojením.
MAX_INBOUND_BUFFER_BYTES = 24 * 1024 * 1024
INBOUND_BYTES_CAPACITY = 24 * 1024 * 1024
INBOUND_BYTES_PER_SECOND = 2 * 1024 * 1024

# Tělo zprávy musí dorazit rychlostí aspoň MIN_RECV_RATE (plus pevná rezerva).
# 50 kB/s je hluboko pod reálnou mobilní linkou, 10 MiB zpráva má ~240 s.
MIN_RECV_RATE_BYTES_PER_S = 50 * 1024
MESSAGE_RECV_GRACE_SECONDS = 30

# OPRAVA #6c: dávka byla 10 bloků a komunikace je striktně sériová
# (request -> čekání -> response -> request), takže při RTT 143 ms a víc se
# reorg do hloubky 1000 nestihl do deadlinu. Větší dávka snižuje počet cyklů
# i počet TCP spojení, které vidí rate limiter z opravy #1.
SYNC_BATCH_SIZE = 100

# OPRAVA #21: SYNC_BATCH_SIZE omezuje jen POČET bloků, ne jejich objem.
# MAX_BLOCK_SIZE_BYTES se měří na kompaktním JSONu, takže 100 plných bloků je
# ~100 MiB v jedné zprávě - desetinásobek MAX_MESSAGE_SIZE. Příjemce takovou
# zprávu odmítne a odesílatele ZABANUJE, přestože poctivě odpověděl na jeho
# vlastní dotaz. Je to přesně ta třída chyby jako #1.
# Dávka je proto shora omezená i bajtově, s rezervou pod MAX_MESSAGE_SIZE.
MAX_BATCH_BYTES = 8 * 1024 * 1024

# --- ETAPA 1: request/response protokol ---
# Dotaz nese request_id a odpověď se posílá po TÉMŽE socketu. Bez toho nešlo
# spárovat odpověď s dotazem, a tedy ani mít víc dotazů v letu.
# Zpráva bez request_id se obslouží po staru (odpověď novým spojením), takže
# se PROTOCOL_VERSION zvyšovat nemusí - a uzly se navzájem nezabanují.
REQUEST_TIMEOUT = 20.0
CONNECTION_IDLE_TIMEOUT = 120
MAX_UNAUTHENTICATED_MESSAGES = 5

# --- ETAPA 2: rate limiting po zprávách ---
# is_rate_limited() se dřív volal jednou při accept(), tedy jednou za SPOJENÍ.
# S perzistentním spojením by to znamenalo jeden token na libovolně mnoho
# zpráv a DoS ochrana by tiše zmizela. Účtuje se proto po zprávách
# (RATE_LIMIT_*), a spojení má vlastní, mnohem menší rozpočet (CONN_*) -
# perzistentních spojení je potřeba málo.
CONN_BUCKET_CAPACITY = 60
CONN_REFILL_PER_SECOND = 5.0

# Drahé dotazy se nově účtují i BAJTOVĚ. Počet požadavků je špatná jednotka:
# request_blocks nad prázdnými bloky stojí zlomek toho, co nad plnými, a
# strop 1 req/s zastropoval propustnost na 100 bloků/s bez ohledu na hloubku
# pipeliningu. Bajtový kbelík škáluje se skutečnou prací, takže malé bloky
# poletí rychle a plné se přirozeně přiškrtí.
EXPENSIVE_BYTES_CAPACITY = 16 * 1024 * 1024
EXPENSIVE_BYTES_PER_SECOND = 2 * 1024 * 1024

# OPRAVA #6c: deadline se dřív měřil od ZAČÁTKU stahování forku a už se nikdy
# neobnovil, takže neměřil nečinnost, ale celkovou dobu - a nad hraničním RTT
# se hluboký reorg nedotáhl nikdy. Nově je to watchdog na nečinnost: obnovuje
# se při každém úspěšném zápisu do bufferu.
FORK_SYNC_IDLE_TIMEOUT = 60

# OPRAVA N3 (audit 10. 10. 2026, nález N3): jak dlouho se IP, které vypršel
# watchdog nad rozpracovaným forkem, nesmí znovu ucházet o fork slot.
#
# ETAPA 3 váže stahování forku na JEDEN uzel (fork_peer_ip), aby šel vadný
# buffer přiřknout konkrétní protistraně. Slot se ale přiděloval podle POŘADÍ
# PŘÍCHODU a nabízená práce se neporovnávala s ničím: kdo poslal první
# PoW-platný blok, držel slot celých FORK_SYNC_IDLE_TIMEOUT a dávky všech
# ostatních se zahazovaly ("Dávka od ... ignorována: fork se stahuje z ...").
# Útočníkovi na to stačil JEDEN blok vytěžený na FIXED_TARGET (po ZMĚNĚ 6
# ~2^22 hashů, v době nálezu ~2^20), znovupoužitelný donekonečna - stačí ho
# přehrávat s has_more: true. Naměřeno:
# uzel s vrcholem #12 ignoroval těžší větev po #30 v šesti kolech za sebou,
# bez jediného banu. Prakticky to znamená, že uzel nikdy neprovede hluboký
# reorg a zůstane na lehčí větvi.
#
# Hlavní oprava je, že se slot nově přiděluje PODLE PRÁCE (viz
# _nabidka_prebiji_fork) a čerstvý neprázdný buffer nejde zahodit cizím
# nárokem. Cooldown je druhá linie: bez něj by útočník po každém vypršení
# watchdogu slot zabral znovu dřív, než se poctivý peer stihne ozvat - zabrání
# ho stojí jedinou zprávu a smí jich poslat 90 za sekundu.
#
# Platí JEN pro založení nového forku, ne pro pokračování rozpracovaného
# (_resume_fork_sync), takže poctivý peer, kterému jednou vypadla linka,
# o dodávání rozpracovaného bufferu nepřijde. Běžná synchronizace bloků
# (request_chain_info, request_blocks) se tím neomezuje vůbec.
FORK_SLOT_COOLDOWN_SECONDS = 120
# Strop evidence cooldownů. Klíčem je IP, a tu si útočník vybírá sám, takže
# struktura nesmí růst bez meze - táž úvaha jako u MAX_PEER_LISTEN_PORTS
# a MAX_MEMPOOL_OFFER_CURSORS. Při překročení padají nejdřív expirující.
MAX_FORK_SLOT_COOLDOWNS = 4 * MAX_PEERS

# OPRAVA #9: request_blocks iteroval locator_hashes bez limitu délky a na každý
# prvek pouštěl SQL dotaz - útočník mohl poslat statisíce hashů v jedné 10MB
# zprávě. Locator se navíc staví exponenciálně, ne jako 1200 po sobě jdoucích
# hashů, což je jediné, k čemu je dobrý.
MAX_LOCATOR_HASHES = 32

# OPRAVA W-3 (audit 9. 10. 2026, nález N-3): náhrada za TX_RATE_LIMIT = 100
# za TX_RATE_WINDOW = 60 s.
#
# Starý limit měl dvě vady najednou. Zaprvé byl zvolený nazdařbůh a vyšel 17x
# POD kapacitou řetězce: běžná transakce má ~630 B, do bloku se jich vejde
# ~1 660 a blok je za 60 s, tedy ~27,7 tx/s - zatímco limit pouštěl 1,67 tx/s.
# Zadruhé, a hlavně, se jeho překročení trestalo BANEM (ban_peer na hodinu),
# ne zahozením zprávy. Ban je přitom oboustranný (is_blacklisted() se testuje
# i v connect_to_peer() a _send_to_single_peer()), takže by si poctivé uzly po
# zavedení přeposílání (OPRAVA W-2, nález N-2) začaly navzájem udělovat bany
# už při ~6 % využití bloku a síť by se rozpadla na ostrovy. To je přesně
# scénář, který pro SPOJENÍ řešila OPRAVA #1.
#
# Nově tedy totéž, co dělá OPRAVA #1: token bucket, překročení burstu zprávu
# jen ZAHODÍ, a ban přijde až po dlouhodobém překračování (TX_RATE_ABUSE_*),
# stejnou konstrukcí jako RATE_LIMIT_ABUSE_THRESHOLD.
#
# Strop je ODVOZENÝ od kapacity řetězce, ne zvolený: burst je jeden blok
# transakcí (tolik jich může peer přeposlat najednou po vytěžení bloku),
# ustálená hodnota je dvojnásobek skutečné kapacity řetězce. Poctivý peer se
# k ní nepřiblíží; kdo ji trvale překračuje, posílá transakce rychleji, než je
# síť schopná vytěžit.
TYPICKA_VELIKOST_TX_BYTES = 640
TX_PER_BLOCK_CAPACITY = MAX_BLOCK_SIZE_BYTES // TYPICKA_VELIKOST_TX_BYTES
TX_RATE_BUCKET_CAPACITY = TX_PER_BLOCK_CAPACITY
TX_RATE_REFILL_PER_SECOND = 2.0 * TX_PER_BLOCK_CAPACITY / BLOCK_TIME_SECONDS
TX_RATE_ABUSE_THRESHOLD = 20.0 * TX_RATE_REFILL_PER_SECOND

# OPRAVA F-02: velikost jedné transakce nebyla nijak omezená. Pole 'signature'
# nevstupuje do get_signing_data(), tedy ani do tx_id, takže jeho délku nic
# nekontrolovalo a jediným stropem byl MAX_MESSAGE_SIZE (10 MiB). Jedna taková
# transakce vytěsnila 93,5 % mempoolu ještě PŘED ověřením podpisu.
#
# Dvě nezávislé zábrany:
#   1) MAX_TX_SIZE_BYTES - tvrdý strop na jednu transakci. Odvozený od velikosti
#      bloku: transakce, která se nikdy nevejde do bloku, nemá v mempoolu co
#      dělat. Osmina bloku je s rezervou nad reálnou transakcí (~400 B).
#   2) SIGNATURE_HEX_LEN / PUBLIC_KEY_HEX_LEN - přesná délka obou hex polí.
#      SECP256k1: 64 bajtů podpisu i nekomprimovaného veřejného klíče bez
#      prefixu = 128 hex znaků. Cokoli jiného je odpad, ne podpis.
MAX_TX_SIZE_BYTES = MAX_BLOCK_SIZE_BYTES // 8
SIGNATURE_HEX_LEN = 128
PUBLIC_KEY_HEX_LEN = 128

# OPRAVA F-04: 'response_mempool' byla jediná odpověď bez branky. Zatímco
# 'response_full_chain' hlídá awaiting_full_chain a 'response_blocks' příznak
# syncing_fork, tuhle mohl poslat nevyžádaně kdokoli po handshaku. Nebyla ani
# v seznamu drahých dotazů, ani se nepočítala do rozpočtu transakcí (ten hlídá
# jen zprávy typu 'transaction'; dnes TX_RATE_*, dřív TX_RATE_LIMIT = 100 za
# 60 s). Do jedné 10MiB zprávy se vejde ~16 700 transakcí, tedy 166násobek
# tehdejšího limitu.
#
# MEMPOOL_RESPONSE_WINDOW: jak dlouho po odeslání request_mempool jsme ochotni
# odpověď přijmout. Musí být delší než REQUEST_TIMEOUT, protože starší uzly
# odpovídají novým spojením (asynchronně), ne po témže socketu.
MEMPOOL_RESPONSE_WINDOW = 60

# OPRAVA Y-5 (audit 14. 10. 2026, nález 5): totéž okno pro 'response_full_chain'.
#
# Branka té zprávy byl dosud prostý bool bez expirace: uzel, který poslal
# request_full_chain a nedočkal se odpovědi, zůstal otevřený NAVŽDY - jediná
# cesta zpět vedla přes skutečnou odpověď. Libovolně pozdější nevyžádaná
# 'response_full_chain' od kteréhokoli známého uzlu pak brankou prošla.
#
# Je to nekonzistence mezi dvěma brankami, které dělají totéž: sesterská
# MEMPOOL_RESPONSE_WINDOW výše okno má a consume_mempool_expectation() je navíc
# jednorázová. Důvod pro stejnou hodnotu je i stejný - musí být delší než
# REQUEST_TIMEOUT, protože starší uzly odpovídají novým spojením, ne po témže
# socketu.
#
# Závažnost je nízká, protože replace_chain(0, ...) navrhovaný řetězec stejně
# celý ověří; jde tedy o vynucenou práci, ne o přijetí neplatných dat.
FULL_CHAIN_RESPONSE_WINDOW = 60

# Kolik transakcí smí jedna zpráva 'response_mempool' obsahovat - a kolik jich
# tedy uzel sám odešle jako odpověď na 'request_mempool'. Sync mempoolu je
# best-effort: zbytek doteče běžným rozesíláním 'transaction' (OPRAVA W-2)
# a dalšími koly periodické synchronizace, která díky rotaci okna (OPRAVA W-5)
# postupně projdou CELÝ mempool, ne pořád tutéž nejdražší pětistovku.
#
# OPRAVA W-5 (audit 9. 10. 2026, nález N-2b): hodnota 500 zůstává, protože je
# to zároveň strop, který příjemce vynucuje BANEM - viz komentář u handleru
# 'request_mempool'. Skutečným omezením objemu je MAX_BATCH_BYTES.
MAX_MEMPOOL_RESPONSE_TX = 500

# OPRAVA W-5 (nález N-2b): kurzor rotace okna, jeden na peera. Drží se jen
# dvojice (klíč poslední odeslané položky, čas), tedy desítky bajtů na peera.
# TTL i strop jsou tu ze stejného důvodu jako u PEER_LISTEN_PORT_TTL
# a MAX_PEER_LISTEN_PORTS: struktura klíčovaná IP adresou nesmí růst bez meze,
# protože adresu si útočník vybírá sám. Strop odpovídá MAX_PEER_LISTEN_PORTS.
MEMPOOL_OFFER_CURSOR_TTL = 3600
MAX_MEMPOOL_OFFER_CURSORS = 4 * MAX_PEERS
SOFTWARE_VERSION = "0.1.0-alpha.1"

# OPRAVA N6 (audit 10. 10. 2026, nález N6): 'node_id' z handshaku se dosud
# netypovalo ani neomezovalo délkou, přestože se z něj skládá KLÍČ do slovníku
# ((ip, node_id) v peer_listen_ports po OPRAVĚ U-20). dict a list tam vyhodily
# TypeError: unhashable type, který spolkl až catch-all v handle_message() -
# selhání bezpečným směrem, ale přesně ta třída nálezu, kterou OPRAVA S-7
# odstranila u 'request_id' kontrolou isinstance. Délku neomezovalo nic:
# naměřeno uložené node_id o 200 000 znacích. Stropy branky důvěry (4 na IP,
# 80 celkem) drží, takže rozsah byl omezený, ale 80 klíčů o velikosti zprávy
# není to, s čím návrh počítá.
#
# 64 znaků je s rezervou nad tím, co uzel sám posílá: node_id je
# binascii.hexlify(os.urandom(8)), tedy 16 znaků.
MAX_NODE_ID_LEN = 64

PROTOCOL_VERSION = 1
CHAIN_ID = 1
BLOCK_VERSION = 1
MEMPOOL_TX_EXPIRATION = 86400

CHECKPOINTS = {
    0: GENESIS_BLOCK_EXPECTED_HASH,
}

# OPRAVA A-6 (assumevalid): load_data() volá is_valid_chain() BEZPODMÍNEČNĚ při
# každém spuštění a ověřuje každý podpis od genesis bloku. CHECKPOINTS přitom
# existovaly, ale používaly se jen k porovnání hashe - ne k přeskočení validace
# pod checkpointem. Přitom právě to je jejich smysl: hashový řetězec obsah pod
# checkpointem zavazuje, takže ověřovat podpisy znovu nic nepřidává. Hash bloku,
# merkle root, state root, target, časy i stav se přehrávají dál - přeskakuje se
# JEN kryptografie, tedy 97 % nákladu.
#
# Předpoklad, na kterém to stojí: hodnoty v CHECKPOINTS jsou součástí binárky
# a uzel jim věří stejně jako GENESIS_BLOCK_EXPECTED_HASH. Přidávat je proto smí
# jen ten, kdo vydává kód - a je to dobrá praxe i bez ohledu na rychlost.
#
# ASSUMEVALID = False vypne optimalizaci a vynutí ověření každého podpisu od
# genesis (pro audit, forenzní analýzu nebo nedůvěru k vydané binárce).
ASSUMEVALID = True
NEJVYSSI_CHECKPOINT = max(CHECKPOINTS) if CHECKPOINTS else -1

time_offset = 0

def get_ntp_time(server):
    TIME1970 = 2208988800
    client = None
    try:
        addr_info = socket.getaddrinfo(server, 123, socket.AF_UNSPEC, socket.SOCK_DGRAM)
        family, socktype, proto, _, sockaddr = addr_info[0]
        client = socket.socket(family, socktype, proto)
        client.settimeout(5)
        data = b'\x1b' + 47 * b'\0'
        client.sendto(data, sockaddr)
        data, _ = client.recvfrom(1024)
        # OPRAVA U-21 (audit 7. 10. 2026, pozorování 4.5): struct.unpack('!12I')
        # vyžaduje PŘESNĚ 48 bajtů, takže odpověď s připojeným autentizačním
        # kódem (key identifier + message digest, RFC 5905 §7.5) propadla celá:
        # unpack vyhodil struct.error, obecný except ho spolkl a vrátil None.
        # Hlavička NTP je prvních 48 bajtů bez ohledu na to, co za nimi
        # následuje, takže se zbytek jen odřízne. KRATŠÍ odpověď zůstává vadná
        # a vrací None - ta useknutá hlavička je skutečně nepoužitelná.
        #
        # Selhání bylo v bezpečném směru (míň zdrojů -> read-only), takže šlo
        # o liveness, ne o bezpečnost. Při MIN_NTP_SOURCES = 2 ale stačili dva
        # takhle nakonfigurované servery k tomu, aby uzel přestal těžit, a
        # z logu by nikdo nepoznal proč.
        if data and len(data) >= 48:
            t = struct.unpack('!12I', data[:48])
            ntp_seconds = t[10]
            if ntp_seconds < TIME1970:
                ntp_seconds += 2**32
            secs = ntp_seconds - TIME1970
            frac = t[11] / 2**32
            return secs + frac
    except Exception:
        return None
    finally:
        if client:
            client.close()
    return None

def sync_time_with_ntp():
    # OPRAVA #18: NTP je neautentizované. Původní kód vzal offset od PRVNÍHO
    # serveru, který odpověděl, bez jakéhokoli stropu - útočník na cestě (nebo
    # jediný podvržený server) tak mohl posunout time_offset a vystrčit bloky
    # uzlu mimo akceptační okno, případně ho donutit odmítat vlastní bloky.
    #
    # Nově: dotážeme se všech serverů, vezmeme medián nabídnutých offsetů,
    # zahodíme vzorky, které se od mediánu liší o víc než NTP_AGREEMENT_SECONDS,
    # a výsledek uplatníme jen tehdy, když se shodly aspoň MIN_NTP_SOURCES
    # nezávislé servery A výsledný offset se vejde do MAX_NTP_OFFSET_SECONDS.
    # Jinak offset NEPOUŽIJEME a uzel jede v read-only režimu, tedy netěží a
    # neodesílá transakce. Medián ze tří zdrojů znamená, že útočník musí
    # ovládnout většinu z nich, ne jen ten nejrychlejší.
    global time_offset
    global read_only

    samples = []
    for server in NTP_SERVERS:
        try:
            local_before = time.time()
            ntp_time = get_ntp_time(server)
            local_after = time.time()
            if ntp_time is not None:
                # Round-trip kompenzujeme středem intervalu měření.
                local_mid = (local_before + local_after) / 2
                samples.append((server, ntp_time - local_mid))
                print(f"{Fore.GREEN}NTP server {server} odpověděl (offset {ntp_time - local_mid:+.3f} s).{Style.RESET_ALL}")
        except Exception as e:
            print(f"{Fore.RED}NTP server {server} je nedostupný: {e}{Style.RESET_ALL}")

    if not samples:
        print(f"{Fore.RED}Žádný NTP server není dostupný. Startuji v read-only režimu.{Style.RESET_ALL}")
        read_only = True
        return

    offsets = sorted(o for _, o in samples)
    median = offsets[len(offsets) // 2] if len(offsets) % 2 == 1 else (offsets[len(offsets) // 2 - 1] + offsets[len(offsets) // 2]) / 2

    agreeing = [(s, o) for s, o in samples if abs(o - median) <= NTP_AGREEMENT_SECONDS]
    for server, o in samples:
        if abs(o - median) > NTP_AGREEMENT_SECONDS:
            print(f"{Fore.YELLOW}NTP server {server} zahozen jako odlehlý (offset {o:+.3f} s vs. medián {median:+.3f} s).{Style.RESET_ALL}")

    if len(agreeing) < MIN_NTP_SOURCES:
        print(f"{Fore.RED}Shodly se jen {len(agreeing)} NTP zdroje (vyžadovány {MIN_NTP_SOURCES}). Offset se NEPOUŽIJE, jedu v read-only režimu.{Style.RESET_ALL}")
        read_only = True
        return

    agreeing_offsets = sorted(o for _, o in agreeing)
    final_offset = (agreeing_offsets[len(agreeing_offsets) // 2] if len(agreeing_offsets) % 2 == 1
                    else (agreeing_offsets[len(agreeing_offsets) // 2 - 1] + agreeing_offsets[len(agreeing_offsets) // 2]) / 2)

    if abs(final_offset) > MAX_NTP_OFFSET_SECONDS:
        print(f"{Fore.RED}Nevěrohodná odchylka času: {final_offset:+.1f} s překračuje tvrdý strop {MAX_NTP_OFFSET_SECONDS} s.{Style.RESET_ALL}")
        print(f"{Fore.RED}Offset se NEPOUŽIJE. Zkontrolujte hodiny zařízení. Uzel jede v read-only režimu (netěží).{Style.RESET_ALL}")
        read_only = True
        return

    time_offset = final_offset
    print(f"{Fore.GREEN}Čas synchronizován z {len(agreeing)} shodujících se zdrojů. Offset: {time_offset:+.6f} s.{Style.RESET_ALL}")

def get_time():
    return int(time.time() + time_offset)

def zkrat(hodnota, limit=MAX_LOG_VALUE_CHARS):
    """OPRAVA N1 (nález N1): hodnota od protistrany do jedné hlášky logu.

    Vrací text nejvýš `limit` znaků; delší se ořízne a doplní se, kolik znaků
    hodnota měla doopravdy - z logu tak musí být poznat, že se ořezávalo, jinak
    by příští audit četl zkrácenou hodnotu jako skutečnou.

    Ořez CELÉHO řádku v _p2p_log_append_locked() je tvrdá pojistka a platí vždy;
    tenhle ořez je kvůli čitelnosti. Hodnota bývá uprostřed věty, takže bez něj
    by řádkový ořez usekl to podstatné (IP odesílatele, důvod odmítnutí)
    a nechal v logu útočníkův balast.

    Pracuje nad čímkoli, ne jen nad str: do hlášek se interpolují i texty
    výjimek a hodnoty polí libovolného typu (viz OPRAVA D-15).
    """
    try:
        s = hodnota if isinstance(hodnota, str) else str(hodnota)
    except Exception:
        # __str__ od protistrany nikdy nevoláme nad cizím objektem, ale kontrakt
        # "tahle funkce nevyhodí" musí platit bezvýhradně - loguje se i
        # z chybových cest, kde je výjimka to poslední, co kdo potřebuje.
        return '<nezobrazitelná hodnota>'
    if len(s) <= limit:
        return s
    return f"{s[:limit]}...[zkráceno, celkem {len(s)} znaků]"


def p2p_log(message):
    # OPRAVA AUDIT-1: konsenzuální metody (add_block, replace_chain,
    # resolve_orphans, recycle_orphan_transactions, cleanup_mempool) volaly
    # p2p_node.add_log() přímo. Bez inicializovaného globálu z toho letí
    # NameError, a tím padá deklarovaný kontrakt "add_block vrací True/False" -
    # volající s výjimkou nepočítají. V ostrém provozu to dosud zachraňoval
    # vedlejší efekt _is_valid_chain_inner(), která si globál dosadí jako
    # DummyNode dřív, než se přidá první blok. To je záchrana náhodou:
    # jakákoli změna pořadí v main() ji ruší.
    #
    # Tahle funkce dělá totéž, co vzorec "if 'p2p_node' in globals() and
    # p2p_node is not None", jen na jednom místě. Když uzel neexistuje, zpráva
    # se zahodí - stejně jako u toho vzorce - a volající dostane návratovou
    # hodnotu, ne výjimku.
    node = globals().get('p2p_node')
    if node is not None and hasattr(node, 'add_log'):
        node.add_log(message)

def is_valid_private_key(key_hex):
    if not isinstance(key_hex, str):
        return False
    if len(key_hex) != 64:
        return False
    try:
        ecdsa.SigningKey.from_string(binascii.unhexlify(key_hex), curve=ecdsa.SECP256k1)
        return True
    # OPRAVA N-6: unhexlify() nad ne-ASCII řetězcem hází ValueError, který NENÍ
    # binascii.Error (je to naopak jeho předek) - funkce tak místo False vyhodila.
    except (ValueError, ecdsa.BadSignatureError, ecdsa.MalformedPointError):
        return False

# OPRAVA A-6: čistě pythonovská knihovna `ecdsa` stála 97 % času startovní
# validace řetězce. Naměřeno na 300 blocích s 6 221 transakcemi:
# is_valid_chain() 13,25 s, z toho 7,45 s v Transaction.verify_signature
# (3,31 s jen v ellipticcurve._double, 748 720 volání). S ověřováním podpisů
# 6,63 s, bez nich 0,17 s. Extrapolace na rok provozu (525 600 bloků po 60 s):
# 6,5 h při 20 tx/blok a 520 h při plných blocích - a to na x86; cílem je ARM
# v Termuxu. Uzel by po roce provozu nenaběhl.
#
# Ověřování proto běží přes OpenSSL: 2,18 -> 0,41 ms na podpis, tedy 5,4x.
# Formát zůstává bit za bitem stejný:
#   - veřejný klíč  64 bajtů X||Y (nekomprimovaný, bez prefixu 0x04)
#   - podpis        64 bajtů r||s, low-S
#   - hash          SHA3-256 přes get_signing_data(), předaný jako Prehashed
# Ověřeno křížově: podpis vyrobený knihovnou `ecdsa` projde přes OpenSSL
# a pozměněná zpráva neprojde.
#
# PODEPISOVÁNÍ zůstává na `ecdsa` a `sign_deterministic` (RFC 6979) záměrně.
# cryptography deterministické ECDSA neumí a volí k náhodně; podpis by tak
# přestal být reprodukovatelný ze samotného klíče a zprávy. Na výkonu to
# nesejde - podepisuje se jednou za transakci, ověřuje se při každém startu
# uzlu za celý řetězec. Chceme-li se `ecdsa` zbavit úplně, je to jediné místo,
# které je potřeba přepsat, a cenou je právě ztráta determinismu.
SECP256K1_ORDER = ecdsa.SECP256k1.order

def verify_ecdsa_signature(public_key_hex, signature_hex, message):
    # Vrací True/False, nikdy nevyhazuje - viz kontrakt Transaction.verify_signature().
    try:
        pub = binascii.unhexlify(public_key_hex)
        sig = binascii.unhexlify(signature_hex)
    except (binascii.Error, TypeError, ValueError):
        return False
    if len(pub) != 64 or len(sig) != 64:
        return False

    r = int.from_bytes(sig[:32], 'big')
    s = int.from_bytes(sig[32:], 'big')
    if r <= 0 or r >= SECP256K1_ORDER or s <= 0 or s >= SECP256K1_ORDER:
        return False
    # Malleabilita: vyšší polovina se odmítá stejně jako dřív. Podpis je
    # součástí listu merkle stromu, takže dvě platné varianty téhož podpisu
    # by daly dva různé merkle rooty pro tentýž obsah bloku.
    if s > SECP256K1_ORDER // 2:
        return False

    try:
        vk = ec.EllipticCurvePublicKey.from_encoded_point(ec.SECP256K1(), b'\x04' + pub)
        vk.verify(asym_utils.encode_dss_signature(r, s),
                  hashlib.sha3_256(message).digest(),
                  ec.ECDSA(asym_utils.Prehashed(hashes.SHA3_256())))
        return True
    except (InvalidSignature, ValueError, TypeError):
        return False

class Wallet:
    def __init__(self, private_key=None):
        if private_key:
            if not is_valid_private_key(private_key):
                raise ValueError("Neplatný privátní klíč")
            self.private_key = ecdsa.SigningKey.from_string(binascii.unhexlify(private_key), curve=ecdsa.SECP256k1, hashfunc=hashlib.sha3_256)
        else:
            self.private_key = self.generate_private_key()
        self.public_key = self.private_key.get_verifying_key()
        self.address = self.generate_address()

    def generate_private_key(self):
        return ecdsa.SigningKey.generate(curve=ecdsa.SECP256k1, hashfunc=hashlib.sha3_256)

    def generate_address(self):
        return self.public_key_to_address(self.public_key.to_string())

    @staticmethod
    def public_key_to_address(public_key_bytes):
        address_hash = hashlib.sha3_256(public_key_bytes).hexdigest()
        base_address = f"{TICKER}{address_hash}"
        checksum = hashlib.sha3_256(base_address.encode()).hexdigest()[:8]
        return base_address + checksum

    def sign_transaction(self, transaction):
        message = transaction.get_signing_data()
        sig = self.private_key.sign_deterministic(message, hashfunc=hashlib.sha3_256)
        r, s = ecdsa.util.sigdecode_string(sig, ecdsa.SECP256k1.order)
        if s > (ecdsa.SECP256k1.order // 2):
            s = ecdsa.SECP256k1.order - s
            sig = ecdsa.util.sigencode_string(r, s, ecdsa.SECP256k1.order)
            
        return binascii.hexlify(sig).decode()


# OPRAVA A-4: volitelná pole se kódovala jen délkovým prefixem, a None se
# kódovalo jako DÉLKA 0 - tedy bit za bitem stejně jako prázdný řetězec.
# Podepisovaná data pro data=None a data="" byla shodná, a tím pádem i tx_id;
# podpis vytvořený nad jednou variantou platil i pro druhou. Totéž platilo pro
# public_key, to_address, pole signature v listu merkle stromu a pro
# state_root i previous_hash v hlavičce bloku.
#
# Dnes to není zneužitelné - všechny tři validátory blok s coinbase.data = ""
# odmítnou, from_dict() vynucuje u hex polí přesnou délku a is_valid_address()
# prázdnou adresu nepustí. Jenže to je obrana o vrstvu výš, ne vlastnost
# základu: podpis nebyl závazkem k jednoznačné n-tici hodnot. Přesně proti
# spoléhání na druhou linii míří OPRAVA #4 i D-15.
#
# Nově jeden bajt navíc rozlišuje přítomnost od prázdnoty:
#   None -> 0x00
#   ""   -> 0x01 + délka 0
#   "x"  -> 0x01 + délka 1 + "x"
#
# POZOR: mění to tx_id, merkle root i hash genesis bloku. Je to hard fork -
# nasadit před spuštěním sítě, ne po něm. GENESIS_NONCE
# a GENESIS_BLOCK_EXPECTED_HASH jsou kvůli tomu přepočítané.
def encode_optional_field(s):
    if s is None:
        return b'\x00'
    enc = str(s).encode('utf-8')
    return b'\x01' + struct.pack('!I', len(enc)) + enc

class Transaction:
    def __init__(self, from_address, to_address, amount, fee=0, nonce=0, public_key=None, signature=None, timestamp=None, tx_id=None, data=None, chain_id=CHAIN_ID):
        self.from_address = from_address
        self.to_address = to_address
        self.amount = amount
        self.fee = fee
        self.nonce = nonce
        # OPRAVA F-13: `or` bere nulu jako nepravdu, takže legitimní
        # timestamp = 0 - který from_dict() výslovně povoluje
        # (_check_uint(..., minimum=0)) - se tiše přepsal aktuálním časem.
        # Táž zpráva zpracovaná dvěma uzly s různými hodinami tak dala dvě
        # různá tx_id. Dnes to maskuje kontrola tx_id a podpisu, ale je to
        # nedeterminismus v konsenzuální struktuře.
        self.timestamp = timestamp if timestamp is not None else get_time()
        self.public_key = public_key
        self.signature = signature
        self.data = data
        self.chain_id = chain_id
        self.tx_id = tx_id or self.compute_hash()
        # OPRAVA #11: lokální metadata mempoolu - absolutní čas, kdy má transakce
        # z mempoolu vypadnout. NENÍ součástí to_dict(), get_signing_data() ani
        # tx_id, takže se nepromítá do konsenzu, hashe ani velikosti bloku.
        # Existuje proto, že reorg vracel do mempoolu transakce podepsané dřív
        # než před MEMPOOL_TX_EXPIRATION, a ty se odmítaly jako expirované -
        # uživatel o ně nenávratně přišel, přestože už jednou v bloku byly.
        self.mempool_deadline = self.timestamp + MEMPOOL_TX_EXPIRATION

    def get_signing_data(self):
        b = b''
        b += struct.pack('!I', int(self.chain_id))
        b += struct.pack('!Q', int(self.amount))
        b += struct.pack('!Q', int(self.fee))
        b += struct.pack('!Q', int(self.nonce))
        b += struct.pack('!Q', int(self.timestamp))
        
        # OPRAVA A-4: viz encode_optional_field() - None a "" už nejsou totéž.
        for s in [self.from_address, self.to_address, self.public_key, self.data]:
            b += encode_optional_field(s)
        return b

    def compute_hash(self):
        return hashlib.sha3_256(self.get_signing_data()).hexdigest()

    def to_dict(self):
        return {
            'chain_id': self.chain_id,
            'from_address': self.from_address,
            'to_address': self.to_address,
            'amount': self.amount,
            'fee': self.fee,
            'timestamp': self.timestamp,
            'nonce': self.nonce,
            'public_key': self.public_key,
            'signature': self.signature,
            'tx_id': self.tx_id,
            'data': self.data,
        }

    @staticmethod
    def from_dict(data):
        try:
            amount = data.get('amount')
            fee = data.get('fee')
            nonce = data.get('nonce', 0)

            # OPRAVA #4: kontrakt téhle funkce je "při špatných datech vyhoď
            # ValueError". Původně se kontrolovalo jen isinstance(amount, int)
            # a amount > 0, tedy BEZ horní meze - jenže get_signing_data() balí
            # amount/fee/nonce/timestamp přes struct.pack('!Q') a chain_id přes
            # '!I'. Hodnota mimo rozsah proto propadla až do struct.error, která
            # NENÍ podtřídou ValueError, takže ji except níž nechytil a unikla
            # volajícím (nejcitlivěji load_mempool, který spoléhá na ValueError).
            # Rozsahy proto ověřujeme explicitně JEŠTĚ PŘED voláním konstruktoru,
            # protože Transaction.__init__ počítá tx_id, a tedy struct.pack volá.
            #
            # isinstance(True, int) je v Pythonu True, takže bool musíme vyloučit
            # zvlášť - jinak by 'amount': true prošlo jako částka 1.
            def _check_uint(value, bits, label, minimum=0):
                if isinstance(value, bool) or not isinstance(value, int):
                    raise ValueError(f"{label} musí být celé číslo.")
                if not (minimum <= value <= (1 << bits) - 1):
                    raise ValueError(
                        f"{label} je mimo povolený rozsah ({minimum} až {(1 << bits) - 1}): {value}."
                    )

            # OPRAVA AUDIT-10: minimum=1 platilo bezvýhradně, tedy i pro coinbase.
            # Tím si deserializace protiřečila s konsenzem: add_block() (ř. 3753),
            # _validate_fork_inner() (ř. 4534) i _is_valid_chain_inner() (ř. 5009)
            # vyžadují PŘESNOU rovnost `coinbase.amount == expected_reward + total_fees`.
            # Od halvingu 33 (blok 33 000 000) je BLOCK_REWARD // (2 ** halvings)
            # nula, takže u prázdného bloku vychází požadovaná částka 0 - a taková
            # coinbase se nedala naparsovat. Nulu přitom NEZPŮSOBÍ ořez na
            # MAX_SUPPLY - total_supply: celková emise podle halvingu skončí na
            # 9 999 999 989 000 000 nanitů, tedy o 11 000 000 POD MAX_SUPPLY, který
            # se tak nikdy neuplatní. Je to čisté celočíselné dělení.
            #
            # Následek byl rozštěpení sítě: těžař sestavil prázdný blok, vlastní
            # uzel ho přijal a zapsal do blockchain.db, ale každý jiný uzel ho po
            # drátě odmítl s ValueError - a handlery `new_block` (ř. 8739) i
            # `response_blocks` (ř. 8506) na ValueError volají ban_peer(...,
            # BAN_DURATION_PROTOCOL). Poctivý těžař si tedy za blok, který sám
            # považuje za platný, postupně zabanoval celou vlastní síť.
            #
            # Nula se proto povoluje VÝHRADNĚ coinbase transakci. Nic se tím
            # neuvolňuje: pravidlo `amount > 0` (a `amount >= MIN_TX_AMOUNT`) pro
            # běžné transakce dál vynucuje konsenzus ve všech třech validátorech
            # i mempoolová politika v add_transaction(), která navíc coinbase do
            # mempoolu nepustí vůbec. Útočníkovi tedy nulová coinbase k ničemu
            # není - v bloku projde jen tehdy, když se na nanit rovná nároku.
            #
            # POZOR, JE TO ZMĚNA KONSENZU (HARD FORK): patří do kódu PŘED
            # spuštěním sítě, ne po něm. Stejnou poznámku nesou OPRAVA A-4,
            # OPRAVA #6b / ZMĚNA 1, OPRAVA #14 a OPRAVA N-3.
            #
            # OPRAVA U-2 (audit 2. 10. 2026, nález 2): mez byla 2**64-1, ale
            # amount, fee, nonce i timestamp jdou v save_mempool() rovnou jako
            # parametry do mempool.db, kde je INTEGER 64bitový SE ZNAMÉNKEM.
            # Hodnota nad 2**63-1 by tam vyhodila OverflowError - stejná úvaha
            # jako u OPRAVY A-05 a o pár řádků výš u Block.from_dict (U-2).
            #
            # Konsenzus se nemění. MAX_SUPPLY je 10**16 nanitů, takže částka ani
            # poplatek se k 2**63 nepřiblíží ani o deset řádů a transakce nad
            # touhle mezí dnes stejně padne na kontrole zůstatku; get_signing_data()
            # pole dál balí přes '!Q' (uint64), tohle je jen užší podmnožina.
            je_coinbase = data.get('from_address') == "COINBASE"
            _check_uint(amount, 63, "Částka", minimum=0 if je_coinbase else 1)
            _check_uint(fee, 63, "Poplatek")
            _check_uint(nonce, 63, "Nonce")

            chain_id = data.get('chain_id', CHAIN_ID)
            _check_uint(chain_id, 32, "chain_id")

            # OPRAVA W-6 (audit 9. 10. 2026, nález N-5): 'timestamp' je POVINNÝ.
            #
            # Dřív tu stálo data.get('timestamp') a chybějící klíč znamenal
            # timestamp=None, které konstruktor nahradil get_time(). Tatáž zpráva
            # tedy na dvou uzlech vyrobila DVĚ RŮZNÁ tx_id - nedeterminismus
            # v konsenzuální struktuře, tedy přesně to, co OPRAVA F-13 odstranila
            # u `or` a OPRAVY U-7 / N-5 u polí bloku.
            #
            # Block.from_dict() je u svých polí důsledný (chybějící 'nonce'
            # i 'merkle_root' odmítá výslovně), u transakcí ta přísnost chyběla -
            # a dvě branky, které o témže objektu říkají něco jiného, jsou
            # opakující se zdroj nálezů (N-5 u targetu, U-7 u merkle rootu,
            # U-8 u celočíselného targetu).
            #
            # Dnes to selhávalo bezpečným směrem (nesedící merkle root, případně
            # kontrola dodaného tx_id na konci téhle funkce), takže je to oprava
            # latentní vady. Nic legitimního se tím neomezuje: to_dict() pole
            # vyplňuje vždy a save_mempool() ho ukládá jako NOT NULL hodnotu.
            #
            # Explicitní 'timestamp': null nově padá taky, protože _check_uint()
            # None odmítne - stejně jako u 'nonce' v Block.from_dict().
            if 'timestamp' not in data:
                raise ValueError("Pole 'timestamp' chybí.")
            raw_timestamp = data['timestamp']
            # OPRAVA G-01: kontrola běžela až NAD převedenou hodnotou
            # (`timestamp = int(raw_timestamp)` bylo dřív), takže bool-guard
            # v _check_uint neměl co zachytit a 'timestamp': true prošlo
            # jako čas 1, "1785614460" jako číslo a 1785614460.7 se tiše
            # oříznulo. Kontroluje se proto SYROVÁ hodnota, stejně jako
            # u amount, fee, nonce a chain_id o pár řádků výš.
            # OPRAVA U-2: mez 63 bitů ze stejného důvodu jako u amount/fee/
            # nonce výš - timestamp jde do mempool.db jako parametr SQLite.
            _check_uint(raw_timestamp, 63, "Timestamp")
            timestamp = raw_timestamp

            # OPRAVA F-02: tvar hex polí se vynucuje JEŠTĚ PŘED konstrukcí.
            # 'signature' nevstupuje do get_signing_data(), takže se nepromítne
            # do tx_id a nikdo ho dřív nekontroloval - útočník do něj mohl vložit
            # megabajty a transakce se tou velikostí probojovala vytěsňováním
            # mempoolu dřív, než ji o pár řádků níž zahodilo ověření podpisu.
            # 'public_key' do tx_id vstupuje, ale i tak nemá být libovolně dlouhý.
            def _check_hex_field(value, expected_len, label):
                if value is None:
                    return
                if not isinstance(value, str):
                    raise ValueError(f"{label} musí být hex řetězec nebo None.")
                if len(value) != expected_len:
                    raise ValueError(
                        f"{label} má neplatnou délku ({len(value)}), očekáváno {expected_len} hex znaků."
                    )
                try:
                    binascii.unhexlify(value)
                except (binascii.Error, ValueError):
                    raise ValueError(f"{label} není platný hex řetězec.")
                # OPRAVA A-01: kanonický tvar. Kontrolovala se jen délka a to,
                # že unhexlify projde - velikost písmen ne. Block.from_dict()
                # přitom u 'hash' i 'target' malý hex vynucuje výslovně.
                #
                # 'signature' nevstupuje do get_signing_data(), takže tx_id
                # zůstane stejné, ale VSTUPUJE do listu Merkle stromu: tentýž
                # obsah bloku zapsaný s velkými písmeny v podpisu dá jiný merkle
                # root. Je to táž třída problému, proti které se u
                # verify_ecdsa_signature odmítá vyšší polovina 's' ("dvě platné
                # varianty téhož podpisu by daly dva různé merkle rooty pro
                # tentýž obsah bloku"); varianta s velikostí písmen ošetřená
                # nebyla.
                if value != value.lower():
                    raise ValueError(f"{label} musí být v malých písmenech.")

            raw_signature = data.get('signature')
            raw_public_key = data.get('public_key')
            _check_hex_field(raw_signature, SIGNATURE_HEX_LEN, "Podpis")
            _check_hex_field(raw_public_key, PUBLIC_KEY_HEX_LEN, "Veřejný klíč")

            # OPRAVA D-15: from_address, to_address a data šly do konstruktoru
            # bez jakékoli kontroly typu. get_signing_data() na nich dělá
            # str(s).encode('utf-8'), takže from_address = None, to_address = 12345
            # i data = {'a': 1} prošly a jen se zahashovala jejich textová podoba.
            # Zachytí je sice až is_valid_address() a zákaz `data` v konsenzu, ale
            # spoléhat se na obranu v druhé linii je přesně to, kvůli čemu vznikla
            # OPRAVA #4: co je součástí podpisových dat, má mít tvar ověřený
            # JEŠTĚ PŘED tím, než se z toho počítá tx_id.
            #
            # 'data' zůstává povolené jako řetězec - nese ho genesis coinbase
            # ("BTC: ..."). Pro všechny ostatní transakce ho konsenzus zakazuje
            # (musí být None), to se kontroluje v add_block/validate_fork/is_valid_chain.
            raw_from = data['from_address']
            raw_to = data['to_address']
            if not isinstance(raw_from, str):
                raise ValueError(
                    f"Pole 'from_address' musí být řetězec (je {type(raw_from).__name__})."
                )
            if not isinstance(raw_to, str):
                raise ValueError(
                    f"Pole 'to_address' musí být řetězec (je {type(raw_to).__name__})."
                )
            raw_payload = data.get('data')
            if raw_payload is not None and not isinstance(raw_payload, str):
                raise ValueError(
                    f"Pole 'data' musí být řetězec nebo None (je {type(raw_payload).__name__})."
                )

            tx = Transaction(
                raw_from,
                raw_to,
                amount,
                fee,
                nonce=nonce,
                public_key=raw_public_key,
                signature=raw_signature,
                timestamp=timestamp,
                data=raw_payload,
                chain_id=chain_id
            )
            # OPRAVA F-02: tvrdý strop na velikost jedné transakce. Zbylá volná
            # pole (from_address, to_address, data) žádnou délkovou mez neměla.
            if tx.get_size() > MAX_TX_SIZE_BYTES:
                raise ValueError(
                    f"Transakce je příliš velká ({tx.get_size()} B), maximum je {MAX_TX_SIZE_BYTES} B."
                )
            supplied_tx_id = data.get('tx_id')
            if supplied_tx_id is not None and supplied_tx_id != tx.tx_id:
                raise ValueError(
                    f"Neplatné tx_id: dodané tx_id '{supplied_tx_id}' neodpovídá "
                    f"vypočtenému hashi obsahu transakce '{tx.tx_id}'."
                )
            return tx
        except (KeyError, ValueError, TypeError, AttributeError, struct.error, OverflowError) as e:
            # struct.error a OverflowError doplněny k původnímu tuple jako
            # pojistka - rozsahové kontroly výše by je už neměly připustit,
            # ale kontrakt "ven jde vždy ValueError" musí platit bezvýhradně.
            #
            # OPRAVA G-07: totéž pro AttributeError. Nad ne-dictem padne hned
            # první `data.get('amount')` a dosud výjimka propadla ven - tedy
            # přesně to, co OPRAVA D-15 popsala u Block.from_dict. Volající to
            # sice mají nově ošetřené kontrolou tvaru (_data_shape_ok), tohle
            # je druhá linie: kontrakt musí platit bez ohledu na to, kdo funkci
            # zavolá a co jí podá.
            raise ValueError(f"Chyba při deserializaci transakce: {e}")

    def get_size(self):
        # OPRAVA D-04: get_size() serializuje celou transakci přes json.dumps,
        # a add_transaction() ho volal pro KAŽDOU transakci v mempoolu při
        # každém jednom příjmu (sum(tx.get_size() for tx in ...)). To je
        # kvadratické v počtu transakcí a drželo se to pod self.lock: při plném
        # mempoolu ~151 ms na transakci, zatímco rate limiter dovnitř pouštěl
        # 33 tx/s. Zámek pak nestíhal a add_block() svůj timeout=5 vyčerpal -
        # u vlastního vytěženého bloku to znamenalo zahodit celé kolo PoW.
        #
        # Obsah transakce je po podepsání neměnný, takže velikost stačí spočítat
        # jednou. Cache je LÍNÁ a invaliduje se přes invalidate_size_cache() -
        # jediné místo, kde se transakce po vzniku ještě mění, je doplnění
        # podpisu ve volbě "odeslat transakci".
        cached = getattr(self, '_size_cache', None)
        if cached is None:
            cached = len(json.dumps(self.to_dict(), separators=(',', ':'), sort_keys=True).encode('utf-8'))
            self._size_cache = cached
        return cached

    def invalidate_size_cache(self):
        self._size_cache = None

    def is_valid_timestamp(self, allow_expired=False):
        # allow_expired: transakce recyklovaná z odpojeného bloku. Byla už jednou
        # potvrzená, takže její stáří nesmí být důvodem k zahození - horní mez
        # (čas v budoucnosti) ale platí vždy. Viz OPRAVA #11.
        if self.timestamp > (get_time() + 600):
            return False
        # OPRAVA X-4: spodní mez chyběla. OPRAVA D-12 doplnila pravidlo
        # tx.timestamp >= GENESIS_TIMESTAMP do všech tří validátorů bloku
        # (add_block, validate_fork, is_valid_chain), ale ne sem - a při
        # allow_expired=True tu pak nezůstávala ŽÁDNÁ spodní mez. Mempool tedy
        # přijal transakci s timestamp = 1, kterou konsenzus zaručeně odmítne.
        # mine() kontroluje u vybíraných transakcí zůstatky (D-09) a nonce, ale
        # ne čas, takže by ji těžař vybral a přišel o celé kolo PoW na bloku,
        # který sám odmítne.
        #
        # Ze sítě to dnes dosažitelné není - allow_expired=True používají jen
        # recycle_orphan_transactions() a replace_chain() (odtud transakce
        # pochází z bloku, který už validací prošel) a revalidate_stored_mempool()
        # z lokálního mempool.db. Je to tedy obrana v druhé linii. Doplňuje se
        # proto, že si kód sám klade pravidlo "mempool nesmí přijmout nic, co
        # konsenzus odmítne", a tady ho porušoval.
        #
        # Mez stojí PŘED větví allow_expired: stáří potvrzené transakce není
        # důvod k zahození (OPRAVA #11), ale čas před genesis blokem je nesmysl
        # bez ohledu na to, odkud transakce přišla.
        if self.timestamp < GENESIS_TIMESTAMP:
            return False
        if allow_expired:
            return True
        return self.timestamp >= (get_time() - MEMPOOL_TX_EXPIRATION)

    def verify_signature(self):
        if self.from_address == "COINBASE":
            return True
        if not self.public_key or not self.signature:
            return False
        try:
            # OPRAVA A-6: ověření přes OpenSSL. Kontroly rozsahu r/s i odmítnutí
            # vyšší poloviny s (malleabilita) jsou uvnitř helperu.
            return verify_ecdsa_signature(self.public_key, self.signature, self.get_signing_data())
        except (binascii.Error, ValueError, TypeError, struct.error, OverflowError):
            return False
        except Exception:
            # OPRAVA #3: ecdsa.util.MalformedSignature dědí přímo z Exception
            # (MRO: MalformedSignature -> Exception), takže ji původní tuple
            # nechytal - stačil podpis, který nemá přesně 64 bajtů.
            #
            # verify_signature() je dosažitelná ze sítě (zpráva 'transaction' ->
            # add_transaction) i z disku (load_mempool, is_valid_chain při startu)
            # a žádný z volajících výjimku neočekává: load_mempool chytá per
            # transakci jen ValueError, takže by jediný poškozený podpis přerušil
            # obnovu celého mempoolu, a is_valid_chain() se při startu volá zcela
            # bez try - poškozená DB by shodila uzel s tracebackem.
            #
            # Kontrakt téhle metody je "vrať True/False, nikdy nevyhoď".
            # Catch-all je tu proto záměrný: jakákoli výjimka z kryptografické
            # knihovny nad nedůvěryhodným vstupem znamená neplatný podpis.
            return False

    def verify_sender_identity(self):
        if self.from_address == "COINBASE":
            return True
        if not self.public_key:
            return False
        try:
            public_key_bytes = binascii.unhexlify(self.public_key)
            generated_address = Wallet.public_key_to_address(public_key_bytes)
            if len(self.from_address) != 75:
                return False
            return self.from_address == generated_address
        # OPRAVA N5 (audit 10. 10. 2026, nález N5): kontrakt téhle metody je
        # "vrať True/False, nikdy nevyhoď" - stejně jako u verify_signature()
        # o pár řádků výš. Chytala se ale jen binascii.Error, a ta nestačí:
        #   unhexlify('ž'*64)   -> holý ValueError (binascii.Error je naopak
        #                          jeho PODTŘÍDA, ne nadtřída),
        #   unhexlify({'a': 1}) -> TypeError,
        # a len() nad ne-řetězcovou from_address taky TypeError. Ověřeno:
        # dict, list i int dají TypeError, 'ž'*64 a '\udcff'*64 dají ValueError.
        #
        # Je to doslova ta chyba, kterou OPRAVA N-6 odstranila v sesterské
        # is_valid_private_key() ("unhexlify() nad ne-ASCII řetězcem hází
        # ValueError, který NENÍ binascii.Error") - sem se nepropsala.
        #
        # Ze sítě to dnes dosažitelné není, protože _check_hex_field()
        # v Transaction.from_dict() vynucuje přesně 128 malých hex znaků. Je to
        # tedy obrana v druhé linii - na kterou se ale kód jinde výslovně
        # odmítá spoléhat (OPRAVA #4, D-15), a volající (add_block,
        # validate_fork, is_valid_chain) s výjimkou odsud nepočítá ani jeden.
        except (ValueError, TypeError):
            return False

# OPRAVA #14: doménová separace listů a vnitřních uzlů transakčního Merkle
# stromu. SMT nad účty ji má správně (SMT_LEAF_PREFIX / SMT_NODE_PREFIX), ale
# transakční strom hashoval list i uzel bez jakéhokoli rozlišení. Dnes to
# zneužít nejde (vstupy mají různý formát a nikde se nepoužívají Merkle proofy),
# ale je to standardní obrana proti záměně typu uzlu a nekonzistence oproti SMT.
# Poznámka: tahle změna mění merkle_root, a tím i hash genesis bloku.
MERKLE_LEAF_PREFIX = b'\x00'
MERKLE_NODE_PREFIX = b'\x01'

def compute_merkle_leaf_hash(tx):
    # OPRAVA A-4: dřív se testovala PRAVDIVOST podpisu, takže None i "" daly
    # shodný list. Navíc se tím do listu promítalo i to, že prázdný podpis
    # nebyl odlišitelný od chybějícího.
    b = MERKLE_LEAF_PREFIX + tx.get_signing_data() + encode_optional_field(tx.signature)
    return hashlib.sha3_256(b).hexdigest()

MERKLE_ZERO_HASH = "0" * 64

def compute_merkle_root(transactions):
    if not transactions:
        # Prázdný strom: hash prázdného vstupu se nemůže srazit ani s listem
        # (prefix 0x00), ani s uzlem (prefix 0x01), protože ty mají vždy
        # aspoň jeden bajt prefixu navíc. Doména je tedy oddělená i tady.
        return hashlib.sha3_256(b'').hexdigest()
    tx_hashes = [compute_merkle_leaf_hash(tx) for tx in transactions]
    while len(tx_hashes) > 1:
        if len(tx_hashes) % 2 != 0:
            tx_hashes.append(MERKLE_ZERO_HASH)
        new_hashes = []
        for i in range(0, len(tx_hashes), 2):
            combined = tx_hashes[i] + tx_hashes[i + 1]
            new_hash = hashlib.sha3_256(MERKLE_NODE_PREFIX + combined.encode()).hexdigest()
            new_hashes.append(new_hash)
        tx_hashes = new_hashes
    return tx_hashes[0]

# ---------------------------------------------------------------------------
# STATE ROOT - Sparse Merkle Tree (SMT) nad účty
# ---------------------------------------------------------------------------
# Konsenzuální commitment k celému stavu řetězce. Hlavička bloku nese state_root
# = stav PO aplikaci daného bloku (ethereum sémantika). Protože přechod stavu
# nezávisí na nonce ani na hashi bloku, těžař root spočítá ještě před PoW a
# ostatní uzly ho po aplikaci bloku ověří.
#
# Struktura: sparse Merkle tree hloubky 256, pozice listu je dána
# sha3_256(adresa). Podstrom s jediným listem se "sbalí" na hash toho listu
# (jellyfish varianta) - díky tomu je strom mělký (~log2(n)) a výpočet je
# O(n log n) místo O(n*256). Sbalení je bezpečné, protože list hashuje i svůj
# vlastní klíč, takže ho nelze přesunout jinam ve stromě.
#
# Doménové prefixy oddělují hash listu od hashe vnitřního uzlu (ochrana proti
# záměně typu uzlu).
#
# KANONICKÉ PRAVIDLO: účet je součástí stavu, právě když má nenulový zůstatek
# NEBO záznam v nonce_map. Nulové zůstatky se do rootu nepočítají, takže
# nezáleží na tom, jestli v paměti zbyl klíč s hodnotou 0 - jinak by uzel po
# reorgu došel k jinému rootu než uzel po lineárním sync.

SMT_EMPTY_HASH = b'\x00' * 32
SMT_LEAF_PREFIX = b'\x00'
SMT_NODE_PREFIX = b'\x01'
SMT_MAX_DEPTH = 256
STATE_ROOT_DOMAIN = b'DRX/state/v1'
IMMATURE_ROOT_DOMAIN = b'DRX/immature/v1'
# OPRAVA #15: EMPTY_STATE_ROOT byl definován dvakrát (tady jako None a níž
# jako compute_state_root({}, {}, {}, 0)) a nikdy se nepoužil. Obě definice
# odstraněny.

def encode_account(address, balance, nonce):
    if not isinstance(balance, int) or not isinstance(nonce, int):
        raise ValueError(f"Stav účtu {address} má neceločíselné hodnoty.")
    if balance < 0:
        raise ValueError(f"Záporný zůstatek u adresy {address}.")
    if balance > MAX_SUPPLY:
        raise ValueError(f"Zůstatek adresy {address} překračuje MAX_SUPPLY.")
    if nonce < -1:
        raise ValueError(f"Neplatný nonce {nonce} u adresy {address}.")
    # OPRAVA G-02: chyběla HORNÍ mez. Nonce se balí přes '!q', tedy ZNAMÉNKOVÝ
    # 64bit (znaménko je tu nutné, protože -1 znamená "účet ještě nemá nonce"),
    # takže strop je 2^63-1. Transaction.from_dict přitom povoluje až 2^64-1.
    # Pro nonce >= 2^63 vyhodil struct.pack výjimku struct.error, která NENÍ
    # podtřídou ValueError - proletěla by tedy přes `except ValueError`
    # v add_block(), _validate_fork_inner(), _is_valid_chain_inner() i mine().
    # Prakticky je to nedosažitelné (striktní posloupnost nonce znamená, že
    # k nonce 2^63 by adresa potřebovala 2^63 předchozích transakcí), ale
    # kontrakt "ven jde vždy ValueError" má platit bezvýhradně.
    # Formát packování se ZÁMĚRNĚ nemění - je součástí konsenzu (state root).
    if nonce > 2**63 - 1:
        raise ValueError(f"Nonce {nonce} u adresy {address} překračuje rozsah kódování (2^63-1).")
    addr_bytes = str(address).encode('utf-8')
    # Délka adresy se balí přes '!I'. Adresy jsou jinde omezené na 75 znaků,
    # tahle mez je jen proto, aby funkce nemohla vyhodit struct.error ani při
    # volání odjinud.
    if len(addr_bytes) > 2**32 - 1:
        raise ValueError(f"Adresa je pro kódování příliš dlouhá ({len(addr_bytes)} B).")
    return (struct.pack('!I', len(addr_bytes)) + addr_bytes +
            struct.pack('!Q', balance) +
            struct.pack('!q', nonce))

def smt_key(address):
    return hashlib.sha3_256(str(address).encode('utf-8')).digest()

def smt_leaf_hash(address, balance, nonce):
    return hashlib.sha3_256(
        SMT_LEAF_PREFIX + smt_key(address) + encode_account(address, balance, nonce)
    ).digest()

def _smt_bit(key, depth):
    return (key[depth >> 3] >> (7 - (depth & 7))) & 1

def _smt_subtree_root(items, depth):
    if not items:
        return SMT_EMPTY_HASH
    if len(items) == 1:
        return items[0][1]
    if depth >= SMT_MAX_DEPTH:
        # Nedosažitelné bez kolize sha3-256, ošetřeno jen proti nekonečné rekurzi.
        h = hashlib.sha3_256(SMT_NODE_PREFIX)
        for _, leaf_hash in items:
            h.update(leaf_hash)
        return h.digest()
    left = []
    right = []
    for item in items:
        if _smt_bit(item[0], depth):
            right.append(item)
        else:
            left.append(item)
    return hashlib.sha3_256(
        SMT_NODE_PREFIX + _smt_subtree_root(left, depth + 1) + _smt_subtree_root(right, depth + 1)
    ).digest()

def compute_accounts_root(balance_map, nonce_map):
    addresses = set(nonce_map.keys())
    for address, balance in balance_map.items():
        if balance:
            addresses.add(address)
    items = []
    for address in addresses:
        items.append((
            smt_key(address),
            smt_leaf_hash(address, balance_map.get(address, 0), nonce_map.get(address, -1))
        ))
    items.sort(key=lambda item: item[0])
    return _smt_subtree_root(items, 0)

_IMMATURE_BLOB_CACHE = {}


def _immature_blob(block_index, reward):
    # OPRAVA F-03: kódování jedné položky je deterministické a položky se
    # nemění - jen přibývají na jednom konci a maturují na druhém. Držíme si
    # tedy hotové bajty. Slovník je omezený zhruba dvojnásobkem okna
    # COINBASE_MATURITY, aby nerostl donekonečna.
    ck = (int(block_index), reward['address'], int(reward['amount']))
    blob = _IMMATURE_BLOB_CACHE.get(ck)
    if blob is None:
        addr_bytes = str(reward['address']).encode('utf-8')
        blob = (struct.pack('!Q', int(block_index)) +
                struct.pack('!I', len(addr_bytes)) + addr_bytes +
                struct.pack('!Q', int(reward['amount'])))
        if len(_IMMATURE_BLOB_CACHE) > 4 * COINBASE_MATURITY:
            _IMMATURE_BLOB_CACHE.clear()
        _IMMATURE_BLOB_CACHE[ck] = blob
    return blob


def compute_immature_root(immature_rewards):
    h = hashlib.sha3_256(IMMATURE_ROOT_DOMAIN)
    h.update(b''.join(
        _immature_blob(bi, immature_rewards[bi])
        for bi in sorted(immature_rewards.keys(), key=int)
    ))
    return h.digest()


# OPRAVA F-03: přírůstkový Sparse Merkle Tree nad účty.
#
# compute_accounts_root() staví celý strom od nuly při KAŽDÉM bloku, přestože
# SMT je v kódu přítomná právě proto, aby šla aktualizovat po jednom listu.
# Naměřeno: 0,71 ms při 100 účtech, ale 984 ms při 100 000 - a volá se čtyřikrát
# (mine, add_block, validate_fork, is_valid_chain), pokaždé jednou na blok.
# Ověření řetězce o délce jednoho roku (525 600 bloků) by při 100 000 účtech
# stálo ~145 hodin jen za state rooty, a to na desktopu; cílovou platformou je
# ARM v Termuxu. Reorg do hloubky 1000 znamenal ~17 minut držení self.lock.
#
# Blok změní jen hrstku účtů, takže se mění jen cesty od těchto listů ke kořeni,
# tedy O(log A) uzlů na změněný list. Ostatní podstromy se berou z cache.
#
# KRITICKÉ: kořen musí být BIT ZA BITEM shodný s compute_accounts_root(),
# jinak vznikne consensus split. Referenční implementace proto zůstává
# beze změny a slouží jako orákulum pro test i jako záloha, když cache není
# k dispozici (viz compute_state_root_from).
class AccountsSMT:
    __slots__ = ('leaves', 'sorted_keys', 'nodes', 'key_of', 'value_of')

    def __init__(self):
        self.leaves = {}        # key(bytes32) -> leaf_hash
        self.sorted_keys = []   # setříděné klíče, kanonické pořadí stromu
        self.nodes = {}         # (depth, prefix_int) -> digest; JEN vnitřní uzly
        self.key_of = {}        # address -> key(bytes32), aby se hash nepočítal 2x
        self.value_of = {}      # address -> (balance, nonce), pro detekci "beze změny"

    def clone(self):
        c = AccountsSMT()
        c.leaves = dict(self.leaves)
        c.sorted_keys = list(self.sorted_keys)
        c.nodes = dict(self.nodes)
        c.key_of = dict(self.key_of)
        c.value_of = dict(self.value_of)
        return c

    @staticmethod
    def _prefix(key, depth):
        if depth == 0:
            return 0
        return int.from_bytes(key, 'big') >> (256 - depth)

    @staticmethod
    def _common_prefix_len(a, b):
        # Počet shodných úvodních BITŮ dvou klíčů.
        if a == b:
            return SMT_MAX_DEPTH
        x = int.from_bytes(a, 'big') ^ int.from_bytes(b, 'big')
        return 256 - x.bit_length()

    def _neighbour_depth(self, key):
        # Nejhlubší úroveň, na které může uzel obsahující `key` mít 2+ listy.
        # Hlouběji už je podstrom jednoprvkový, a jednoprvkové uzly se necachují.
        i = bisect.bisect_left(self.sorted_keys, key)
        d = 0
        if i > 0:
            d = max(d, self._common_prefix_len(key, self.sorted_keys[i - 1]))
        j = i + 1 if (i < len(self.sorted_keys) and self.sorted_keys[i] == key) else i
        if j < len(self.sorted_keys):
            d = max(d, self._common_prefix_len(key, self.sorted_keys[j]))
        return d

    def _invalidate(self, key):
        # Zneplatní cestu od kořene k listu. Hloubka se počítá ze SOUSEDŮ, ne
        # paušálně přes všech 256 úrovní - u náhodných klíčů (a klíč je sha3
        # adresy) je to průměrně ~2*log2(A) úrovní.
        d_max = self._neighbour_depth(key)
        nodes = self.nodes
        for d in range(d_max + 1):
            nodes.pop((d, self._prefix(key, d)), None)

    def set_account(self, address, balance, nonce):
        key = self.key_of.get(address)
        if key is None:
            key = smt_key(address)
            self.key_of[address] = key
        if self.value_of.get(address) == (balance, nonce):
            return  # Nic se nezměnilo, strom se nesmí zbytečně přepočítávat.
        leaf = smt_leaf_hash(address, balance, nonce)
        existuje = key in self.leaves
        self._invalidate(key)           # neplatnost podle STARÉHO okolí
        self.leaves[key] = leaf
        self.value_of[address] = (balance, nonce)
        if not existuje:
            bisect.insort(self.sorted_keys, key)
            self._invalidate(key)       # a znovu podle NOVÉHO okolí

    def remove_account(self, address):
        key = self.key_of.get(address)
        if key is None or key not in self.leaves:
            self.value_of.pop(address, None)
            return
        self._invalidate(key)           # podle starého okolí, dokud tam klíč je
        i = bisect.bisect_left(self.sorted_keys, key)
        if i < len(self.sorted_keys) and self.sorted_keys[i] == key:
            del self.sorted_keys[i]
        del self.leaves[key]
        self.value_of.pop(address, None)
        self._invalidate(key)           # a podle nového okolí

    def _split_point(self, lo, hi, depth):
        # První index v [lo, hi), kde má klíč na pozici `depth` bit 1.
        # Klíče jsou setříděné, takže stačí binární půlení.
        keys = self.sorted_keys
        while lo < hi:
            mid = (lo + hi) // 2
            if _smt_bit(keys[mid], depth):
                hi = mid
            else:
                lo = mid + 1
        return lo

    def _subtree(self, lo, hi, depth):
        n = hi - lo
        if n == 0:
            return SMT_EMPTY_HASH
        if n == 1:
            return self.leaves[self.sorted_keys[lo]]
        if depth >= SMT_MAX_DEPTH:
            # Shodné s referenční implementací. Nedosažitelné bez kolize sha3-256.
            h = hashlib.sha3_256(SMT_NODE_PREFIX)
            for i in range(lo, hi):
                h.update(self.leaves[self.sorted_keys[i]])
            return h.digest()
        ck = (depth, self._prefix(self.sorted_keys[lo], depth))
        cached = self.nodes.get(ck)
        if cached is not None:
            return cached
        mid = self._split_point(lo, hi, depth)
        digest = hashlib.sha3_256(
            SMT_NODE_PREFIX
            + self._subtree(lo, mid, depth + 1)
            + self._subtree(mid, hi, depth + 1)
        ).digest()
        self.nodes[ck] = digest
        return digest

    def root(self):
        return self._subtree(0, len(self.sorted_keys), 0)

    def root_with_changes(self, zmeny):
        """OPRAVA N-11: kořen stromu PO změnách, aniž by se strom měnil.

        zmeny: {adresa: (zustatek, nonce)} pro účet, který ve stromu je/bude,
        nebo {adresa: None} pro účet, který ze stromu vypadne. Přepočítají se jen
        cesty ke změněným listům; nezměněné podstromy se berou z cache základu.
        Struktura rekurze je TOTOŽNÁ se _subtree() i s referenční
        _smt_subtree_root(): prázdný podstrom = SMT_EMPTY_HASH, jediný list se
        sbalí na svůj hash, jinak hash(prefix uzlu | levý | pravý).
        """
        nove_listy = {}
        odebrane = set()
        for adresa, hodnota in zmeny.items():
            klic = self.key_of.get(adresa)
            if klic is None:
                klic = smt_key(adresa)
            v_zakladu = klic in self.leaves
            if hodnota is None:
                if v_zakladu:
                    odebrane.add(klic)
                continue
            if v_zakladu and self.value_of.get(adresa) == hodnota:
                continue
            nove_listy[klic] = smt_leaf_hash(adresa, hodnota[0], hodnota[1])
        if not nove_listy and not odebrane:
            return self.root()
        dotcene = sorted(set(nove_listy) | odebrane)
        return self._subtree_se_zmenami(0, len(self.sorted_keys), 0, dotcene, nove_listy, odebrane)

    def _subtree_se_zmenami(self, lo, hi, depth, dotcene, nove_listy, odebrane):
        if not dotcene:
            return self._subtree(lo, hi, depth)
        pridane = sum(1 for k in dotcene if k in nove_listy and k not in self.leaves)
        ubrane = sum(1 for k in dotcene if k in odebrane)
        pocet = (hi - lo) - ubrane + pridane
        if pocet == 0:
            return SMT_EMPTY_HASH
        if pocet == 1 or depth >= SMT_MAX_DEPTH:
            listy = {}
            for i in range(lo, hi):
                k = self.sorted_keys[i]
                if k not in odebrane:
                    listy[k] = nove_listy.get(k, self.leaves[k])
            for k in dotcene:
                if k in nove_listy:
                    listy[k] = nove_listy[k]
            if pocet == 1:
                return next(iter(listy.values()))
            h = hashlib.sha3_256(SMT_NODE_PREFIX)
            for k in sorted(listy):
                h.update(listy[k])
            return h.digest()
        mid = self._split_point(lo, hi, depth)
        vlevo = [k for k in dotcene if not _smt_bit(k, depth)]
        vpravo = [k for k in dotcene if _smt_bit(k, depth)]
        return hashlib.sha3_256(
            SMT_NODE_PREFIX
            + self._subtree_se_zmenami(lo, mid, depth + 1, vlevo, nove_listy, odebrane)
            + self._subtree_se_zmenami(mid, hi, depth + 1, vpravo, nove_listy, odebrane)
        ).digest()

    def sync_from_maps(self, balance_map, nonce_map, touched=None):
        """Srovná strom s mapami. `touched` = jen dotčené adresy (rychlá cesta).

        Bez `touched` projde všechny adresy - to je O(A), používá se jen při
        prvotní stavbě stromu nad hotovým stavem.
        """
        if touched is None:
            chtene = set(nonce_map.keys())
            for address, balance in balance_map.items():
                if balance:
                    chtene.add(address)
            if not self.leaves:
                # Rychlá cesta: strom je prázdný, takže se staví hromadně.
                # Vkládat po jednom přes bisect.insort by bylo kvadratické
                # v počtu účtů (posun pole při každém vložení) - u 100 000
                # účtů 3 s místo 0,3 s. Tady se jen naplní mapy a setřídí jednou.
                for address in chtene:
                    key = self.key_of.get(address)
                    if key is None:
                        key = smt_key(address)
                        self.key_of[address] = key
                    balance = balance_map.get(address, 0)
                    nonce = nonce_map.get(address, -1)
                    self.leaves[key] = smt_leaf_hash(address, balance, nonce)
                    self.value_of[address] = (balance, nonce)
                self.sorted_keys = sorted(self.leaves.keys())
                self.nodes.clear()
                return
            for address in list(self.value_of.keys()):
                if address not in chtene:
                    self.remove_account(address)
            for address in chtene:
                self.set_account(address, balance_map.get(address, 0), nonce_map.get(address, -1))
            return
        for address in touched:
            # Účet je ve stromu, právě když má nenulový zůstatek nebo záznam
            # v nonce_map - přesně jako v compute_accounts_root().
            v_nonce = address in nonce_map
            zustatek = balance_map.get(address, 0)
            if v_nonce or zustatek:
                self.set_account(address, zustatek, nonce_map.get(address, -1))
            else:
                self.remove_account(address)


_CHYBI = object()


class _PrekryvnaMapa:
    """OPRAVA N-11: mapa nad jinou mapou bez jejího kopírování.

    Zápisy a mazání jdou do vrstvy `zmeny`, základ zůstává netknutý. Umí přesně
    to, co s mapami dělá update_state_with_block() a prune_zero_balances()
    (get, [], []=, del, in, pop, copy); vrstva zároveň říká, které adresy se
    změnily - to je vstup pro AccountsSMT.root_with_changes().
    """
    __slots__ = ('zaklad', 'zmeny')

    def __init__(self, zaklad):
        self.zaklad = zaklad
        self.zmeny = {}

    def get(self, klic, default=None):
        if klic in self.zmeny:
            v = self.zmeny[klic]
            return default if v is _CHYBI else v
        return self.zaklad.get(klic, default)

    def __getitem__(self, klic):
        v = self.get(klic, _CHYBI)
        if v is _CHYBI:
            raise KeyError(klic)
        return v

    def __setitem__(self, klic, hodnota):
        self.zmeny[klic] = hodnota

    def __delitem__(self, klic):
        if klic not in self:
            raise KeyError(klic)
        self.zmeny[klic] = _CHYBI

    def __contains__(self, klic):
        return self.get(klic, _CHYBI) is not _CHYBI

    def pop(self, klic, *default):
        v = self.get(klic, _CHYBI)
        if v is _CHYBI:
            if default:
                return default[0]
            raise KeyError(klic)
        self.zmeny[klic] = _CHYBI
        return v

    def copy(self):
        d = dict(self.zaklad)
        for k, v in self.zmeny.items():
            if v is _CHYBI:
                d.pop(k, None)
            else:
                d[k] = v
        return d


def build_accounts_smt(balance_map, nonce_map):
    smt = AccountsSMT()
    smt.sync_from_maps(balance_map, nonce_map)
    return smt


def compute_state_root(balance_map, nonce_map, immature_rewards, total_supply):
    return hashlib.sha3_256(
        STATE_ROOT_DOMAIN +
        compute_accounts_root(balance_map, nonce_map) +
        compute_immature_root(immature_rewards) +
        struct.pack('!Q', int(total_supply))
    ).hexdigest()


def _state_root_bytes(accounts_root, immature_rewards, total_supply):
    return hashlib.sha3_256(
        STATE_ROOT_DOMAIN +
        accounts_root +
        compute_immature_root(immature_rewards) +
        struct.pack('!Q', int(total_supply))
    ).hexdigest()

def _state_smt(state):
    """Vrátí AccountsSMT navěšený na nosič stavu, nebo None.

    Nosičem je buď Blockchain / SimpleNamespace (atribut), nebo dict
    (get_state_at, state_checkpoints). Když strom chybí, volající se vrátí
    k referenčnímu compute_accounts_root() - je to pomalejší, ale vždy správné.
    """
    if isinstance(state, dict):
        return state.get('accounts_smt')
    return getattr(state, 'accounts_smt', None)


def compute_state_root_from(state):
    # Přijímá jak dict (get_state_at, is_valid_chain), tak objekt s atributy
    # (Blockchain, SimpleNamespace shadow).
    #
    # OPRAVA F-03: je-li k nosiči navěšený udržovaný SMT, použije se jeho
    # kořen. Výsledek je bit za bitem shodný s referenční cestou - ověřeno
    # diferenciálním testem proti compute_accounts_root() nad tisíci
    # náhodnými mutacemi. Bez stromu se počítá po starém.
    smt = _state_smt(state)
    if isinstance(state, dict):
        balance_map = state['balance_map']
        nonce_map = state['nonce_map']
        immature = state.get('immature_rewards', {})
        total_supply = state['total_supply']
    else:
        balance_map = state.balance_map
        nonce_map = state.nonce_map
        immature = state.immature_rewards
        total_supply = state.total_supply

    if smt is not None:
        return _state_root_bytes(smt.root(), immature, total_supply)
    return compute_state_root(balance_map, nonce_map, immature, total_supply)

def make_state_shadow(base):
    # Mělká kopie stavu pro spekulativní aplikaci bloku přes
    # update_state_with_block(state_target=...). Hodnoty balance_map i nonce_map
    # jsou inty (immutable) a u immature_rewards se vnitřní dicty nikdy nemutují,
    # jen nahrazují celé záznamy - stejný předpoklad, na kterém stojí i
    # get_state_at().
    #
    # OPRAVA F-03: se stavem se klonuje i SMT, jinak by spekulativní větev
    # (validate_fork, is_valid_chain) přišla o cache a počítala strom od nuly.
    # clone() kopíruje i cache podstromů, takže nezměněné části zůstávají
    # spočítané. Když base strom nemá, postaví se prázdný a naplní se ze stavu.
    zdroj_smt = _state_smt(base)
    if zdroj_smt is not None:
        smt = zdroj_smt.clone()
    else:
        smt = None

    if isinstance(base, dict):
        shadow = SimpleNamespace(
            balance_map=dict(base['balance_map']),
            nonce_map=dict(base['nonce_map']),
            immature_rewards=dict(base.get('immature_rewards', {})),
            total_supply=base['total_supply'],
            cumulative_work=base.get('cumulative_work', 0),
            undo_logs={},
            state_checkpoints={},
            # OPRAVA AUDIT-13: oba volající (genesis při inicializaci a pomalá
            # cesta add_block()) stín po zjištění state rootu zahodí, takže
            # checkpoint stavu by se vyrobil jen proto, aby se zahodil s ním.
            checkpointy_povolene=False
        )
    else:
        shadow = SimpleNamespace(
            balance_map=dict(base.balance_map),
            nonce_map=dict(base.nonce_map),
            immature_rewards=dict(base.immature_rewards),
            total_supply=base.total_supply,
            cumulative_work=getattr(base, 'cumulative_work', 0),
            undo_logs={},
            state_checkpoints={},
            # OPRAVA AUDIT-13: oba volající (genesis při inicializaci a pomalá
            # cesta add_block()) stín po zjištění state rootu zahodí, takže
            # checkpoint stavu by se vyrobil jen proto, aby se zahodil s ním.
            checkpointy_povolene=False
        )

    if smt is None:
        smt = build_accounts_smt(shadow.balance_map, shadow.nonce_map)
    shadow.accounts_smt = smt
    return shadow

def prune_zero_balances(balance_map, addresses):
    # Kanonizace stavu: účet s nulovým zůstatkem v mapě nedržíme. Root ho stejně
    # ignoruje, ale díky tomuhle je i samotná balance_map stejná bez ohledu na
    # to, jestli vznikla lineárním sync nebo reorgem.
    for address in addresses:
        if balance_map.get(address) == 0:
            del balance_map[address]


class Block:
    def __init__(self, index, transactions, previous_hash, target, nonce=0, timestamp=None, version=BLOCK_VERSION, chain_id=CHAIN_ID, state_root=None):
        self.version = version
        self.chain_id = chain_id
        self.index = index
        # OPRAVA F-13: `or` bere nulu jako nepravdu, takže legitimní
        # timestamp = 0 - který from_dict() výslovně povoluje
        # (_check_uint(..., minimum=0)) - se tiše přepsal aktuálním časem.
        # Táž zpráva zpracovaná dvěma uzly s různými hodinami tak dala dvě
        # různá tx_id. Dnes to maskuje kontrola tx_id a podpisu, ale je to
        # nedeterminismus v konsenzuální struktuře.
        self.timestamp = timestamp if timestamp is not None else get_time()
        self.transactions = transactions
        self.merkle_root = compute_merkle_root(transactions)
        self.previous_hash = previous_hash
        self.target = target
        self.nonce = nonce
        self.state_root = state_root
        self.hash = self.compute_hash()

    def compute_hash(self):
        b = b''
        b += struct.pack('!I', int(self.version))
        b += struct.pack('!I', int(self.chain_id))
        b += struct.pack('!Q', int(self.index))
        b += struct.pack('!Q', int(self.timestamp))
        b += struct.pack('!Q', int(self.nonce))
        
        target_bytes = int(self.target).to_bytes(32, byteorder='big', signed=False)
        b += target_bytes
        
        # state_root je součástí hlavičky, takže spadá i pod PoW. Blok bez něj
        # (starý formát) se zahashuje jako 0x00 (chybí) a neprojde kontrolou hashe.
        # OPRAVA A-4: chybějící pole (0x00) je nově odlišené od prázdného ("").
        for s in [self.previous_hash, self.merkle_root, self.state_root]:
            b += encode_optional_field(s)
        return hashlib.sha3_256(b).hexdigest()

    @staticmethod
    def hlavicka_hash_z_dictu(bd, target_val):
        """OPRAVA P-2: hash hlavičky ze SYROVÉHO dictu, bez parsování transakcí.

        compute_hash() bere merkle_root jako POLE hlavičky, ne jako něco, co si
        sám dopočítá z transakcí - hash hlavičky proto nezávisí na `transactions`
        a jde spočítat v konstantním čase. Díky tomu může _store_fork_batch_inner()
        ověřit vazbu hash <-> obsah ještě PŘED zápisem do bufferu, aniž by za to
        zaplatila výpočtem tx_id všech transakcí dávky.

        Serializace se ZÁMĚRNĚ nekopíruje - staví se prázdný Block a volá se jeho
        compute_hash(). Druhá ruční kopie hlavičky už v kódu je (mining_worker) a
        rozejití těch dvou je dokumentovaná past; třetí se nepřidává.

        Vrací hex hash, nebo None, když hlavičku nelze zakódovat (hodnota mimo
        rozsah struct). None se u volajícího chová jako neshoda.
        """
        try:
            b = Block.__new__(Block)
            b.version = bd.get('version', BLOCK_VERSION)
            b.chain_id = bd.get('chain_id', CHAIN_ID)
            b.index = bd['index']
            b.timestamp = bd['timestamp']
            b.nonce = bd.get('nonce', 0)
            b.target = target_val
            b.previous_hash = bd['previous_hash']
            b.merkle_root = bd['merkle_root']
            b.state_root = bd.get('state_root')
            return b.compute_hash()
        except (KeyError, TypeError, ValueError, struct.error, OverflowError):
            return None

    def _dict_bez_transakci(self):
        # OPRAVA X-2: jediný zdroj pravdy o polích bloku. to_dict() i get_size()
        # vycházejí odsud, takže se nemůžou rozejít. Pozn.: přepsání klíče
        # 'transactions' v to_dict() nemění jeho POZICI (dict si v Pythonu 3.7+
        # drží pořadí vložení), takže serializace zůstává bajt za bajtem táž
        # jako před touto opravou.
        return {
            'version': self.version,
            'chain_id': self.chain_id,
            'index': self.index,
            'timestamp': self.timestamp,
            'transactions': [],
            'merkle_root': self.merkle_root,
            'state_root': self.state_root,
            'previous_hash': self.previous_hash,
            'target': hex(self.target)[2:],
            'nonce': self.nonce,
            'hash': self.hash
        }

    def get_size(self):
        # OPRAVA X-2: velikost se počítá PŘÍRŮSTKOVĚ, ne opakovanou serializací
        # celého bloku. Původní verze volala json.dumps() nad to_dict(), což
        # znovu serializovalo všechny transakce - 5,6 ms na bloku s 1 501 tx
        # (x86, na ARM násobek). Volá se jednou na blok ve dvou smyčkách přes
        # CELÝ řetězec (_is_valid_chain_inner a _validate_fork_inner), takže to
        # dělalo ~279 s při startu nad řetězcem 50 000 bloků a 5,6 s na samotné
        # měření velikosti při reorgu do hloubky 1000.
        #
        # PROČ NE CACHE NA OBJEKTU (jak má Transaction od OPRAVY D-04):
        # v obou drahých smyčkách se blok staví čerstvě z řádku DB a get_size()
        # se na něm volá PRÁVĚ JEDNOU - líná cache by tam neušetřila nic. A na
        # jediném místě, kde se volá dvakrát (mine()), by byla přímo nebezpečná:
        # první volání měří blok se záměrně nastaveným nonce = sys.maxsize
        # (nejhorší případ), pak se nonce vrátí na 0 a PoW ho přepíše skutečnou
        # hodnotou. Zapamatovaná velikost by se pak dostala do konsenzuální
        # kontroly v add_block() i do výpisu po vytěžení.
        #
        # ROZKLAD JE EXAKTNÍ, NE ODHAD - a to je tu podmínka, ne luxus:
        # výsledek se porovnává s MAX_BLOCK_SIZE_BYTES, tedy s konsenzuálním
        # pravidlem. Jakákoli odchylka od původní hodnoty by byla hard fork.
        # json.dumps se sort_keys=True a kompaktními separátory je skládací:
        # text vnořeného seznamu je přesně '[' + ','.join(text položky) + ']'
        # a text jedné položky je týž, ať se serializuje samostatně nebo uvnitř.
        # Tedy:
        #   velikost = základ(prázdný seznam) + suma velikostí transakcí
        #              + čárky mezi nimi (počet - 1)
        # Základ už obsahuje '[]', takže se nic nepřičítá ani neodečítá navíc.
        # Je to týž rozklad, jaký používá mine() od OPRAVY D-06.
        #
        # tx.get_size() je díky cache z OPRAVY D-04 konstanta a cache je v obou
        # drahých smyčkách UŽ NAPLNĚNÁ: Block.from_dict() staví transakce přes
        # Transaction.from_dict(), a ta na každé volá get_size() kvůli stropu
        # MAX_TX_SIZE_BYTES (OPRAVA F-02). Suma přes 1 501 transakcí tak stojí
        # 0,59 ms místo 5,6 ms.
        zaklad = len(json.dumps(self._dict_bez_transakci(),
                                separators=(',', ':'), sort_keys=True).encode('utf-8'))
        pocet = len(self.transactions)
        if pocet == 0:
            return zaklad
        return zaklad + sum(tx.get_size() for tx in self.transactions) + (pocet - 1)

    def to_dict(self):
        d = self._dict_bez_transakci()
        d['transactions'] = [tx.to_dict() for tx in self.transactions]
        return d

    @staticmethod
    def from_dict(data):
        # OPRAVA D-07: kontrakt "ven jde vždy ValueError" platil jen pro
        # Transaction.from_dict (OPRAVA #4), pro bloky ne. Původní kód dělal
        # int(data['target'], 16) BEZ horní meze a Block.__init__ hned nato volá
        # compute_hash(), kde je int(self.target).to_bytes(32, 'big', signed=False).
        # Target 'f'*80 tedy dal OverflowError: int too big to convert a target
        # '-1' OverflowError: can't convert negative int to unsigned.
        #
        # OverflowError NENÍ podtřída ValueError, takže ji nechytal ani handler
        # new_block, ani nic mezi tím - propadla až do obecného
        # except Exception v handle_client_connection, kde spadlo celé spojení
        # bez banu a bez rozlišení příčiny. Je to týž vzorec jako D-02: výjimka
        # z nedůvěryhodných dat prochází vrstvou, která s ní nepočítá. Kdyby se
        # from_dict volalo za nastaveným stavovým příznakem, byl by z toho
        # okamžitě další trvale uvíznutý sync.
        #
        # Rozsahy proto ověřujeme explicitně JEŠTĚ PŘED voláním konstruktoru
        # (ten už hashuje), přesně podle vzoru Transaction.from_dict.
        try:
            def _check_uint(value, bits, label, minimum=0):
                # isinstance(True, int) je v Pythonu True, takže bool vylučujeme
                # zvlášť - jinak by 'index': true prošlo jako výška 1.
                if isinstance(value, bool) or not isinstance(value, int):
                    raise ValueError(f"{label} musí být celé číslo.")
                if not (minimum <= value <= (1 << bits) - 1):
                    raise ValueError(
                        f"{label} je mimo povolený rozsah ({minimum} až {(1 << bits) - 1}): {value}."
                    )

            # OPRAVA D-15: kontrakt "ven jde vždy ValueError" neplatil pro pole
            # 'transactions'. Iterovalo se přes data['transactions'] bez kontroly
            # typu a každá položka šla rovnou do Transaction.from_dict(), která
            # na ní volá .get(). Odtud:
            #     transactions = 'retezec' -> iterace po znacích -> 'r'.get()
            #     transactions = [None]    -> None.get()
            #     transactions = [42]      -> (42).get()
            # ve všech případech AttributeError, a ta NENÍ v tuple na konci téhle
            # funkce (ani v tom v replace_chain, ř. 3923), takže propadla ven.
            #
            # Měřitelný důsledek byl nesymetrický postih: blok s vadným targetem
            # dal ValueError -> handler new_block banoval, blok s
            # transactions=[None] dal AttributeError -> spadlo celé spojení
            # v obecném except handle_client_connection, tedy BEZ banu. Odesílatel
            # stejně vadného bloku tak vyklouzl podle toho, které pole zkazil.
            #
            # Tvar se proto ověřuje JEŠTĚ PŘED konstrukcí, stejným vzorem jako
            # u ostatních polí. Kontroluje se jen TVAR, ne platnost.
            raw_txs = data['transactions']
            if not isinstance(raw_txs, list):
                raise ValueError("Pole 'transactions' musí být seznam.")
            for tx_data in raw_txs:
                if not isinstance(tx_data, dict):
                    raise ValueError(
                        f"Položka v 'transactions' není objekt (je {type(tx_data).__name__})."
                    )
            transactions = [Transaction.from_dict(tx_data) for tx_data in raw_txs]

            raw_target = data['target']
            # OPRAVA N-5: int(x, 16) bere i "0x…", podtržítka, mezery a "+", a
            # int(True) je 1 - tentýž blok tak měl několik různých platných JSON
            # zápisů a brána _valid_block_dict() (cesta syncu) i from_dict()
            # (cesta new_block) říkaly o tvaru targetu každá něco jiného.
            # Kanonický tvar je ten, který posílá to_dict(): hex(target)[2:].
            # OPRAVA U-8 (audit 5. 10. 2026, nález 2): celočíselný target se už
            # NETOLERUJE. Dřív tu stálo `elif isinstance(raw_target, int)` bez
            # jakékoli rozsahové kontroly a _valid_block_dict() int propouštěla
            # taky - jenže hodnota putuje do sloupce target_hex v SQLite jako
            # parametr, kde je INTEGER 64bitový SE ZNAMÉNKEM. Tři důsledky:
            #
            #  1) target = 2**63 prošel brankou (na rozdíl od index, timestamp,
            #     nonce, version i chain_id, kde mez A-05 platí) a spadl teprve
            #     na zápisu do bufferu jako OverflowError. Ta NENÍ sqlite3.Error
            #     ani OSError ani MemoryError, takže _store_fork_batch() ji
            #     vyhodnotil jako "neočekávanou chybu" a odesílatel dostal 24 h
            #     ban. Jedna hlavička s minimálním PoW tak zrušila probíhající
            #     fork sync.
            #  2) Deklarovaná zpětná kompatibilita byla past, ne vstřícnost:
            #     Block.to_dict() posílá hex(self.target)[2:], takže int dnes
            #     neposílá ŽÁDNÁ verze - klient, který by se na tu toleranci
            #     spolehl, by si vysloužil ban od každého uzlu v síti. Přesně
            #     ten failure mode, proti kterému míří OPRAVY #1, N-1, P-1
            #     a ETAPA 3.
            #  3) Nad rámec auditu: int V ROZSAHU byl tiché poškození dat.
            #     Sloupec target_hex má TEXT afinitu, takže SQLite int 0x4000…
            #     uloží jako DEKADICKÝ text; process_sync_buffer() ho přečte
            #     zpátky a int(…, 16) ho vyloží jako hexadecimální - jiné číslo.
            #     Blok by pak neodpovídal vlastnímu hashi. Dnes to maskuje
            #     kontrola hlavičky v _store_fork_batch_inner(), tedy obrana
            #     v druhé linii, na kterou se kód jinde odmítá spoléhat (#4).
            #
            # Kanonický tvar je proto jediný: ten, který posílá to_dict().
            # Obě branky tím říkají o targetu TOTÉŽ, což byl cíl OPRAVY N-5.
            # Konsenzus se nemění - žádný existující blok se neodmítne, protože
            # takový blok po drátě ani v DB nevzniká.
            if isinstance(raw_target, bool):
                raise ValueError("Target nesmí být bool.")
            if not isinstance(raw_target, str):
                raise ValueError(
                    f"Target musí být kanonický hex řetězec (je {type(raw_target).__name__})."
                )
            if (not raw_target or len(raw_target) > 64 or raw_target[0] == '0'
                    or any(c not in '0123456789abcdef' for c in raw_target)):
                raise ValueError(f"Target není kanonický hex řetězec: {raw_target!r}")
            target = int(raw_target, 16)
            # Horní mez je dána compute_hash(): target se balí do 32 bajtů.
            # Dolní mez je 1 - target 0 nesplní žádný hash a work by dělil nulou.
            # Kanonický tvar obojí zaručuje už sám (max 64 znaků, první není '0'),
            # kontrola zůstává jako pojistka pro případ změny pravidla výš.
            if not (0 < target < (1 << 256)):
                raise ValueError(f"Target mimo rozsah: {raw_target}")

            # OPRAVA G-01: pořadí bylo obrácené - `ts = int(data['timestamp'])`
            # proběhlo PŘED kontrolou, takže _check_uint dostal už hotový int
            # a jeho bool-guard neměl co zachytit. Ověřeno spuštěním: 'timestamp'
            # true prošel jako čas 1, "1785614460" jako číslo a 1785614460.7 se
            # tiše oříznulo. Přímo zneužitelné to nebylo - hash bloku se počítá
            # až z normalizované hodnoty, takže kontrola hashe o vrstvu níž se
            # tím obejít nedá - ale byl to rozpor s deklarovaným kontraktem a
            # normalizační nekonzistence: tentýž blok měl několik různých
            # platných JSON reprezentací. Kontroluje se proto SYROVÁ hodnota,
            # stejně jako u index, nonce, version a chain_id.
            #
            # index/timestamp/nonce jdou do compute_hash() přes struct.pack('!Q'),
            # version a chain_id přes '!I'. Mimo rozsah = struct.error, která také
            # není podtřída ValueError.
            #
            # OPRAVA U-2 (audit 2. 10. 2026, nález 2): mez byla 2**64-1, zatímco
            # _valid_block_dict() (branka cesty response_blocks) i sloupce
            # v SQLite drží 2**63-1. Úvaha z OPRAVY A-05 se do téhle branky
            # nepromítla: index, timestamp i nonce jdou do SQLite jako
            # parametry, a hodnota nad 2**63-1 tam vyhodí OverflowError.
            #
            # Důsledek byl nesymetrický postih stejný jako u OPRAVY D-15:
            # blok s nonce 2**63+5 prošel cestou new_block CELOU validací
            # konsenzu - target, merkle root, PoW, podpisy všech transakcí,
            # state root - a padl teprve na zápisu do databáze, tedy bez banu.
            # Týž blok přes response_blocks skončil na rychlé brance a odesílatel
            # dostal 24 h ban. Útočník s platným PoW tak uměl opakovaně vynutit
            # plnou validační práci zadarmo.
            #
            # Konsenzus se tím NEMĚNÍ: hodnota nad 2**63-1 je nepřijatelná už
            # dnes (nikdo takový blok neuloží), jen se odmítne dřív a se
            # správnou diagnostikou. Je to táž náprava jako OPRAVA N-5
            # u targetu - obě branky mají o témže objektu říkat totéž.
            _check_uint(data['timestamp'], 63, "Timestamp bloku")
            ts = data['timestamp']  # _check_uint výše zaručil int (a ne bool)
            _check_uint(data['index'], 63, "Index bloku")
            # OPRAVA (dokončení U-7): 'nonce' je POVINNÝ.
            #
            # Dřív tu stálo data.get('nonce', 0), zatímco _valid_block_dict()
            # pole vyžaduje. Je to přesně ten rozpor, který U-7 odstranila
            # u merkle_root: bajt po bajtu identický blok dopadl na dvou
            # síťových cestách opačně. Ověřeno na bloku s platným PoW a
            # nonce == 0 (vytěženo grindováním coinbase timestampu):
            #   'new_block'       -> blok PŘIJAT do řetězce (tip 0 -> 1)
            #   'response_blocks' -> tvarová branka ho zahodila a odesílatel
            #                        dostal 24hodinový ban.
            # Zároveň to byly dvě platné JSON reprezentace téhož bloku, což
            # OPRAVA N-5 odstraňovala u targetu.
            #
            # Sjednoceno na přísnější pravidlo, protože odpovídá tomu, co uzel
            # skutečně posílá - to_dict() nonce uvádí vždy.
            if 'nonce' not in data:
                raise ValueError("Pole 'nonce' chybí.")
            nonce = data['nonce']
            _check_uint(nonce, 63, "Nonce bloku")
            version = data.get('version', BLOCK_VERSION)
            _check_uint(version, 32, "Verze bloku")
            chain_id = data.get('chain_id', CHAIN_ID)
            _check_uint(chain_id, 32, "chain_id bloku")

            # OPRAVA D-15: textová pole hlavičky se dosud nekontrolovala vůbec.
            # compute_hash() na ně dělá str(s).encode('utf-8'), takže
            # previous_hash = None i previous_hash = ['a'] prošly bez výjimky
            # a zahashovaly se jako "None" resp. "['a']". Dnes je zachytí až
            # kontrola hashe o vrstvu níž - to je ale obrana v druhé linii,
            # ne v konstruktoru. Navíc block.hash putuje do meets_difficulty(),
            # kde se dělá int(hash, 16): nehexadecimální hodnota tam vyhodí
            # ValueError na místě, které s ní nepočítá (viz D-02).
            #
            # Pravidlo pro 'hash' je záměrně TOTOŽNÉ s _valid_block_dict(),
            # aby obě branky říkaly o tvaru bloku totéž.
            def _check_str(value, label, allow_none=False):
                if value is None:
                    if allow_none:
                        return
                    raise ValueError(f"{label} nesmí být None.")
                if not isinstance(value, str):
                    raise ValueError(
                        f"{label} musí být řetězec (je {type(value).__name__})."
                    )

            raw_hash = data['hash']
            _check_str(raw_hash, "Hash bloku")
            if len(raw_hash) != 64 or any(c not in '0123456789abcdef' for c in raw_hash):
                raise ValueError("Hash bloku není 64 znaků malého hexa.")

            raw_previous_hash = data['previous_hash']
            # Délka se NEvynucuje: genesis má previous_hash = "0".
            _check_str(raw_previous_hash, "Pole 'previous_hash'")

            # state_root smí chybět (starý formát bloku bez něj). Takový blok se
            # zahashuje jako délka 0 a neprojde kontrolou hashe - to je původní
            # a záměrné chování, jen se k němu nesmí přidat jiný typ než řetězec.
            raw_state_root = data.get('state_root')
            _check_str(raw_state_root, "Pole 'state_root'", allow_none=True)

            # OPRAVA U-7 (audit 5. 10. 2026, nález 3): merkle_root je POVINNÝ.
            #
            # Dřív tu stálo `if 'merkle_root' in data:` s dopočtem z transakcí
            # v else větvi, zatímco _valid_block_dict() pole vyžadovala. Bajt po
            # bajtu identický blok tak dopadl na dvou síťových cestách opačně:
            # přes 'new_block' se PŘIJAL do řetězce, přes 'response_blocks' ho
            # tvarová branka zahodila a odesílatel dostal 24hodinový ban.
            #
            # Je to vzorec pojmenovaný u OPRAV D-15 a U-2 ("odesílatel stejně
            # vadného bloku vyklouzl podle toho, které pole zkazil"), jen
            # v obráceném gardu: blok byl PLATNÝ a trest nejtvrdší, jaký kód zná.
            #
            # Sjednoceno na přísnější pravidlo, protože odpovídá tomu, co uzel
            # skutečně posílá - to_dict() merkle_root uvádí vždy. Volnější
            # varianta (povolit chybějící pole v obou brankách) by zavedla dvě
            # platné JSON reprezentace téhož bloku, což je přesně to, co OPRAVA
            # N-5 odstraňovala u targetu. Hard fork je to jen formálně: žádná
            # verze blok bez merkle_root neposílá a ani v DB takový nevznikne
            # (sloupec se plní z block.merkle_root).
            #
            # Pozn.: explicitní None padalo na _check_str už dřív; mění se jen
            # chování pro CHYBĚJÍCÍ klíč.
            if 'merkle_root' not in data:
                raise ValueError("Pole 'merkle_root' chybí.")
            raw_merkle_root = data['merkle_root']
            _check_str(raw_merkle_root, "Pole 'merkle_root'")

            block = Block(
                index=data['index'],
                transactions=transactions,
                previous_hash=raw_previous_hash,
                target=target,
                nonce=nonce,
                timestamp=ts,
                version=version,
                chain_id=chain_id,
                state_root=raw_state_root
            )
            block.hash = raw_hash
            block.merkle_root = raw_merkle_root
            return block
        except (KeyError, ValueError, TypeError, struct.error, OverflowError) as e:
            # struct.error a OverflowError jsou tu proto, aby kontrakt platil
            # bezvýhradně i kdyby rozsahová kontrola výše někdy zaostala za
            # tím, co compute_hash() skutečně balí.
            raise ValueError(f"Chyba při deserializaci bloku: {e}")

    def is_valid_timestamp(self, median_time_past):
        return self.timestamp > median_time_past and self.timestamp <= (get_time() + 600) and self.timestamp >= GENESIS_TIMESTAMP

class MissingChainDataError(Exception):
    """OPRAVA F-05: chybí blok, který je pro rozhodnutí nezbytný.

    Dřív se v takové situaci vracel FIXED_TARGET, tedy NEJSNAZŠÍ povolená
    obtížnost. Všechny tři validátory na tom trvají jako na tvrdém pravidle
    konsenzu, takže uzel s poškozenou DB začal vyžadovat target 8x volnější:
    přijímal by bloky s osminovou prací a zároveň odmítal každý poctivý blok.

    Fail-open v konsenzuálním kódu je vždy chyba. Při nejistotě se blok
    odmítá, nikdy nepovoluje.
    """
    pass


class Blockchain:
    def __init__(self, create_genesis=True):
        self.lock = threading.RLock()
        self.chain = []
        self.max_block_index = 0
        self.unconfirmed_transactions = []
        self.mining_in_progress = False
        self.balance_map = {}
        self.nonce_map = {}
        self.immature_rewards = {}
        self.total_supply = 0
        self.orphan_pool = {}
        self.orphan_parents = defaultdict(list)
        # OPRAVA D-01: doprovodná evidence k orphan poolu - velikost každého
        # orphanu, čas vložení a průběžný součet bajtů. Součet se udržuje
        # inkrementálně; počítat ho pokaždé znovu přes get_size() by byl týž
        # kvadratický vzorec jako D-04 u mempoolu.
        self.orphan_sizes = {}
        self.orphan_added_at = {}
        self.orphan_pool_bytes = 0
        self.cumulative_work = 0
        self.last_target_log_idx = -1
        self.undo_logs = {}
        self.state_checkpoints = {}
        # OPRAVA F-03: udržovaný SMT nad účty. Musí vzniknout PŘED genesis
        # blokem, aby ho update_state_with_block() rovnou plnil.
        self.accounts_smt = AccountsSMT()
        if create_genesis:
            self.create_genesis_block()

    # OPRAVA D-04: mempool má nově vedle seznamu i UDRŽOVANÉ INDEXY. Důvod je
    # měřený: add_transaction() dělal při každém jednom příjmu pět lineárních
    # průchodů celým mempoolem (součet velikostí, množina nonce odesílatele,
    # test duplicitního tx_id, get_next_nonce a odečet zůstatku) a všechno pod
    # self.lock. Celkově kvadratické: 6,1 ms při 500 tx, 34,4 ms při 5 000,
    # extrapolovaně ~151 ms při plném mempoolu.
    #
    # Indexy jsou ODVOZENÁ data, ne druhý zdroj pravdy - kanonický zůstává
    # seznam. Aby se nemohly rozejít, je unconfirmed_transactions property:
    # jakékoli hromadné přiřazení (cleanup_mempool, add_block, replace_chain,
    # load_mempool) projde setterem a indexy se přestaví. Přírůstkové cesty
    # používají _mempool_add() / _mempool_remove().
    @property
    def unconfirmed_transactions(self):
        return self._unconfirmed_transactions

    @unconfirmed_transactions.setter
    def unconfirmed_transactions(self, transactions):
        self._unconfirmed_transactions = list(transactions)
        self._reindex_mempool()

    def _reindex_mempool(self):
        self.mempool_bytes = 0
        self.mempool_by_txid = {}
        self.mempool_by_sender = defaultdict(list)
        # OPRAVA F-07: setříděné sazby poplatků. Viz _median_fee_rate().
        self._fee_rates_sorted = []
        for tx in self._unconfirmed_transactions:
            self.mempool_bytes += tx.get_size()
            self.mempool_by_txid[tx.tx_id] = tx
            self.mempool_by_sender[tx.from_address].append(tx)
            self._fee_rates_sorted.append(self._fee_rate(tx))
        self._fee_rates_sorted.sort()

    def _mempool_add(self, tx):
        self._unconfirmed_transactions.append(tx)
        self.mempool_bytes += tx.get_size()
        self.mempool_by_txid[tx.tx_id] = tx
        self.mempool_by_sender[tx.from_address].append(tx)
        # OPRAVA F-07: vložení na správné místo místo pozdějšího řazení celku.
        bisect.insort(self._fee_rates_sorted, self._fee_rate(tx))

    def _mempool_remove(self, tx):
        # Odebrání jedné transakce bez přestavby indexů. Seznam samotný je
        # lineární, ale používá se to jen při vytěsňování (D-03) a při
        # zahazování neplatné transakce (D-09), ne v hlavní příjmové cestě.
        removed = self.mempool_by_txid.pop(tx.tx_id, None)
        if removed is None:
            return False
        self._unconfirmed_transactions = [t for t in self._unconfirmed_transactions if t.tx_id != tx.tx_id]
        self.mempool_bytes -= removed.get_size()
        if self.mempool_bytes < 0:
            self.mempool_bytes = 0
        bucket = self.mempool_by_sender.get(removed.from_address)
        if bucket is not None:
            bucket[:] = [t for t in bucket if t.tx_id != tx.tx_id]
            if not bucket:
                del self.mempool_by_sender[removed.from_address]
        # OPRAVA F-07: odebrat JEDEN výskyt téže sazby. Duplicitní hodnoty jsou
        # běžné (většina transakcí má minimální poplatek) a pro medián je
        # jedno, kterou z nich odebereme.
        rate = self._fee_rate(removed)
        i = bisect.bisect_left(self._fee_rates_sorted, rate)
        if i < len(self._fee_rates_sorted) and self._fee_rates_sorted[i] == rate:
            del self._fee_rates_sorted[i]
        return True

    # OPRAVA T-4 (Nález 2): get_mempool_bytes() odstraněna - mrtvý kód. Byl to
    # jednořádkový getter nad self.mempool_bytes a všichni volající čtou ten
    # atribut přímo.

    @staticmethod
    def _fee_rate(tx, size=None):
        # Sazba = poplatek na bajt. Porovnávat holý poplatek by bylo špatně:
        # velká transakce s vyšším absolutním poplatkem může síť stát víc místa
        # než dvě malé dohromady. Těžař v mine() vybírá podle -fee, což je pro
        # výběr do bloku jiná (a legitimní) otázka; tady jde o místo v paměti.
        return tx.fee / max(1, size if size is not None else tx.get_size())

    def _median_fee_rate(self):
        # OPRAVA F-07: dřív tahle metoda SEŘADILA CELÝ MEMPOOL při každém
        # jednom příjmu (add_transaction -> _mempool_cap_for -> sem). To je
        # přesně ten vzorec, který komentář u OPRAVY D-04 popisuje jako
        # odstraněný, jen o patro níž: 3,895 ms na jeden příjem při 17 000
        # transakcích - a celé pod droid_chain.lock, tedy souběžně s
        # add_block(). Kvůli tomu vznikly D-04 i ADD_BLOCK_LOCK_RETRIES.
        #
        # Setříděný seznam sazeb se nově udržuje přírůstkově v _mempool_add()
        # a _mempool_remove(); tady se z něj jen čte prostředek, tedy O(1).
        rates = self._fee_rates_sorted
        if not rates:
            return 0.0
        mid = len(rates) // 2
        if len(rates) % 2:
            return rates[mid]
        return (rates[mid - 1] + rates[mid]) / 2

    def _mempool_cap_for(self, transaction, tx_size):
        # OPRAVA D-03: rezervovaná horní část mempoolu je přístupná jen
        # transakcím nad mediánovou sazbou. Pro ostatní je strop nižší.
        if self._fee_rate(transaction, tx_size) > self._median_fee_rate():
            return MAX_MEMPOOL_SIZE_BYTES
        return MAX_MEMPOOL_SIZE_BYTES - MEMPOOL_PREMIUM_RESERVE_BYTES

    def _evict_for(self, transaction, tx_size, cap):
        # OPRAVA D-03: vytěsňování podle sazby poplatku. Původně add_transaction()
        # při plném mempoolu odmítla cokoli - přijetí bylo čistě "kdo dřív
        # přijde". Útočník za ~0,00034 DRX zaplnil celých 10 MiB minimálními
        # transakcemi a od té chvíle neprošel ani poctivý uživatel s poplatkem
        # milionkrát nad minimem. mine() sice řadí podle poplatku, ale jen mezi
        # tím, co se do mempoolu UŽ DOSTALO, a to je právě to, co útočník řídí.
        #
        # Dvě pravidla, obě podstatná:
        #   1) Vyhazuje se vždy transakce s NEJVYŠŠÍ NONCE dané adresy. Kdyby se
        #      vyhodila z prostředka, vznikne v posloupnosti díra a všechny
        #      navazující transakce se stanou nevytěžitelnými - poškodilo by to
        #      poctivého odesílatele víc než útočníka.
        #   2) Nová transakce musí mít VYŠŠÍ sazbu než každá, kterou vytlačí.
        #      Bez toho by šlo mempool cyklicky přeorávat stejně levnými
        #      transakcemi a vytěsňování by se samo stalo útokem.
        if tx_size > cap:
            return False
        new_rate = self._fee_rate(transaction, tx_size)

        # Za každou adresu se nabízí jen aktuálně nejvyšší nonce; po jejím
        # vyhození nastupuje další v pořadí. Halda drží vždy tyhle "hlavy".
        stacks = {}
        heap = []
        for sender, txs in self.mempool_by_sender.items():
            # Vlastní rozpracovanou posloupnost si transakce vytlačit nesmí -
            # jinak by si mohla zrušit předchůdce, na kterého navazuje noncí.
            if sender == transaction.from_address or not txs:
                continue
            stack = sorted(txs, key=lambda t: t.nonce, reverse=True)
            stacks[sender] = stack
            heapq.heappush(heap, (self._fee_rate(stack[0]), stack[0].tx_id, sender))

        evicted = []
        freed = 0
        while self.mempool_bytes + tx_size - freed > cap and heap:
            rate, _, sender = heapq.heappop(heap)
            if rate >= new_rate:
                # Nejlevnější zbývající kandidát je pořád aspoň tak drahý jako
                # příchozí transakce - není co vytlačit.
                break
            victim = stacks[sender].pop(0)
            evicted.append(victim)
            freed += victim.get_size()
            if stacks[sender]:
                nxt = stacks[sender][0]
                heapq.heappush(heap, (self._fee_rate(nxt), nxt.tx_id, sender))

        if self.mempool_bytes + tx_size - freed > cap:
            return False

        for victim in evicted:
            self._mempool_remove(victim)
            if 'p2p_node' in globals() and p2p_node is not None:
                p2p_node.add_log(f"{Fore.YELLOW}Transakce {victim.tx_id} vytěsněna z mempoolu transakcí s vyšší sazbou poplatku.{Style.RESET_ALL}")
        # OPRAVA U-9 (audit 5. 10. 2026, nález 4): dřív `return bool(evicted)`,
        # tedy "vytěsnilo se něco?". Při volném mempoolu se smyčka neprovede,
        # evicted zůstane prázdný a metoda hlásila False - "nepodařilo se uvolnit
        # místo", přestože místo bylo. Návratová hodnota má odpovídat otázce,
        # kterou klade volající: "vejde se transakce?"
        #
        # Dnes to neškodí, protože add_transaction() volá _evict_for() až za
        # podmínkou `if self.mempool_bytes + tx_size > cap:`. Právě kvůli
        # PŘESUNU tohohle kroku ale vznikla OPRAVA F-02 - a při jakémkoli dalším
        # přerovnání by z rozporu bylo tiché odmítání platných transakcí.
        #
        # _mempool_remove() už mempool_bytes o vytěsněné snížil, takže je to
        # tatáž podmínka jako kontrola `- freed` výš, jen po provedení odběrů.
        return self.mempool_bytes + tx_size <= cap

    def _prune_mempool_sequences(self, senders=None, stale_only=False):
        # ZMĚNA 4: odstranění konfliktních a nevytěžitelných transakcí podle
        # AKTUÁLNÍHO stavu řetězce (nonce_map, balance_map).
        #
        # Problém: add_block() odebíral z mempoolu jen transakce se STEJNÝM
        # tx_id, jaké má blok. Když ale blok obsahuje JINOU transakci téže
        # adresy se stejnou nonce (stejná peněženka použitá na dvou uzlech,
        # znovu odeslaná platba s jiným časem nebo částkou, double-spend),
        # naše verze v mempoolu zůstala až do expirace (24 h) - a škodila:
        #   - mine() začíná u adresy transakcí s nejnižší nonce; ta byla
        #     zastaralá, takže se adresa přeskočila CELÁ a nevytěžily se ani
        #     její platné navazující transakce,
        #   - cleanup_mempool() i add_transaction() odečítaly její částku od
        #     zůstatku, takže platné navazující transakce propadaly jako
        #     "nedostatečný zůstatek" a nové transakce adresy se odmítaly.
        #
        # Pro každou adresu se její transakce projdou v pořadí nonce:
        #   1) nonce <= nonce_map: nonci už spotřeboval řetězec, transakce se
        #      nikdy nevytěží. Odstraní se, ale posloupnost NEPŘERUŠUJE.
        #   2) duplicitní nonce: ponechá se dříve přijatá transakce.
        #   3) díra v posloupnosti nonce: transakce i všechny navazující jsou
        #      nevytěžitelné.
        #   4) kumulovaná částka + poplatek nad zůstatek: transakce i všechny
        #      navazující padají - stejné pravidlo jako dosud v cleanup_mempool()
        #      (OPRAVA D-09) a v add_transaction().
        # Podpis, adresy ani čas se tu znovu neověřují - na stavu řetězce
        # nezávisí, ověřila je add_transaction() při přijetí a expiraci řeší
        # cleanup_mempool().
        #
        # senders:    adresy ke kontrole; None = všechny adresy v mempoolu.
        # stale_only: jen krok 1. Používá add_block() před recyklací transakcí
        #             při mini-reorgu, kdy by díra v posloupnosti mohla být jen
        #             dočasná (recyklace ji může zaplnit).
        #
        # Volající musí držet self.lock. Vrací seznam dvojic (tx, důvod).
        if senders is None:
            senders = list(self.mempool_by_sender.keys())
        odstranit = []
        for sender in senders:
            if sender == "COINBASE":
                continue
            txs = self.mempool_by_sender.get(sender)
            if not txs:
                continue
            potvrzena_dalsi = self.nonce_map.get(sender, -1) + 1
            ocekavana = potvrzena_dalsi
            dostupne = self.balance_map.get(sender, 0)
            preruseno = None
            # sorted() je stabilní, takže při shodné nonce zůstává pořadí
            # přijetí do mempoolu.
            for tx in sorted(txs, key=lambda t: t.nonce):
                if tx.nonce < potvrzena_dalsi:
                    odstranit.append((tx, f"nonce {tx.nonce} už v blockchainu spotřebovala jiná transakce téže adresy"))
                    continue
                if stale_only:
                    continue
                if preruseno is not None:
                    odstranit.append((tx, preruseno))
                    continue
                if tx.nonce < ocekavana:
                    odstranit.append((tx, f"duplicitní nonce {tx.nonce}"))
                    continue
                if tx.nonce > ocekavana:
                    odstranit.append((tx, f"díra v posloupnosti nonce, chybí nonce {ocekavana}"))
                    preruseno = f"navazuje na chybějící transakci s nonce {ocekavana}"
                    continue
                if dostupne < tx.amount + tx.fee:
                    odstranit.append((tx, "nedostatečný zůstatek"))
                    preruseno = f"navazuje na odstraněnou transakci s nonce {tx.nonce}"
                    continue
                dostupne -= (tx.amount + tx.fee)
                ocekavana += 1
        if odstranit:
            # Jedno hromadné odebrání místo _mempool_remove() po jedné: každé
            # jednotlivé volání přestavuje celý seznam, tedy O(n) na transakci.
            ids = {tx.tx_id for tx, _ in odstranit}
            self.unconfirmed_transactions = [t for t in self.unconfirmed_transactions if t.tx_id not in ids]
        return odstranit

    def cleanup_mempool(self):
        with self.lock:
            current_time = get_time()
            valid_transactions = []
            expired_transactions = []
            
            txs_by_addr = defaultdict(list)
            for tx in self.unconfirmed_transactions:
                txs_by_addr[tx.from_address].append(tx)
                
            for addr, txs in txs_by_addr.items():
                txs.sort(key=lambda t: t.nonce)
                expired_nonce_threshold = None
                for tx in txs:
                    # OPRAVA #11: expirace se počítá z mempool_deadline, ne z
                    # tx.timestamp. U běžné transakce je to totéž, u transakce
                    # vrácené reorgem to znamená novou lhůtu od návratu.
                    deadline = getattr(tx, 'mempool_deadline', tx.timestamp + MEMPOOL_TX_EXPIRATION)
                    if current_time > deadline:
                        if expired_nonce_threshold is None:
                            expired_nonce_threshold = tx.nonce
                        expired_transactions.append(tx)
                    else:
                        if expired_nonce_threshold is not None and tx.nonce > expired_nonce_threshold:
                            expired_transactions.append(tx)
                        else:
                            valid_transactions.append(tx)

            valid_tx_ids = {t.tx_id for t in valid_transactions}
            self.unconfirmed_transactions = [t for t in self.unconfirmed_transactions if t.tx_id in valid_tx_ids]

            # OPRAVA D-09: cleanup_mempool() dosud řešil VÝHRADNĚ expiraci, ne
            # platnost. Transakce, která se stala neutratitelnou (zůstatek
            # odesílatele mezitím zmizel), tak zůstala v mempoolu až 24 hodin
            # a při každém pokusu o těžbu shodila výpočet state rootu, tedy
            # celou těžbu. Revalidace proti AKTUÁLNÍMU stavu to řeší u zdroje.
            #
            # Prochází se po adresách a v pořadí nonce: jakmile jedna transakce
            # neprojde, jsou všechny navazující stejně nevytěžitelné (díra
            # v posloupnosti nonce), takže padají s ní.
            #
            # ZMĚNA 4: pravidlo D-09 (zůstatek + navazující) se nově provádí
            # v _prune_mempool_sequences() a je rozšířené o kontrolu nonce:
            # zastaralé transakce (nonce už spotřebovaná řetězcem), duplicitní
            # nonce a díry v posloupnosti. Pro mempool bez takových transakcí je
            # výsledek beze změny. Tady slouží jako pojistka - add_block() tytéž
            # transakce odstraňuje hned po přijetí bloku.
            invalid_transactions = self._prune_mempool_sequences()

            if expired_transactions or invalid_transactions:
                save_mempool(self.unconfirmed_transactions)
                # OPRAVA G-11: `global p2p_node` tu bylo zbytečně - deklarace je nutná jen při PŘIŘAZENÍ, ne při čtení. Odstraněno.
                if 'p2p_node' in globals() and p2p_node is not None:
                    for tx in expired_transactions:
                        p2p_node.add_log(f"{Fore.YELLOW}Upozornění: Transakce {tx.tx_id} byla odstraněna z mempoolu (expirace nebo navazující).{Style.RESET_ALL}")
                    for tx, duvod in invalid_transactions:
                        p2p_log(f"{Fore.YELLOW}Upozornění: Transakce {tx.tx_id} byla odstraněna z mempoolu ({duvod}).{Style.RESET_ALL}")

    def revalidate_stored_mempool(self, kandidati):
        # ZMĚNA 3: validace uloženého mempoolu při startu uzlu.
        #
        # Mempool se při vypnutí už nemaže (ZMĚNA 2), takže mempool.db může po
        # startu obsahovat transakce, které mezitím přestaly platit: jsou už
        # vytěžené (například je vytěžil jiný uzel a blok se stihl zapsat, ale
        # uzel spadl dřív, než uložil mempool), jejich nonce spotřebovala jiná
        # transakce téže adresy, vypršely, odesílatel na ně už nemá zůstatek,
        # nebo je záznam poškozený. Volá se z load_mempool() až PO načtení
        # a validaci blockchainu, tedy nad aktuálním balance_map a nonce_map.
        #
        # kandidati: seznam dvojic (tx, allow_expired) v pořadí, v jakém byly
        # transakce zapsané do mempool.db (ORDER BY rowid). To odpovídá pořadí
        # jejich původního přijetí do mempoolu.
        #
        # Postup:
        #   1) Transakce, jejichž tx_id už je v blockchainu, se vyřadí jedním
        #      dávkovým dotazem (tx_ids_in_chain), ne dotazem na každou zvlášť.
        #   2) Zbytek se rozdělí podle odesílatele a v rámci odesílatele seřadí
        #      podle nonce. Na pořadí záleží: add_transaction() přijme jen
        #      transakci s PŘESNĚ následující nonce, takže při načtení v jiném
        #      pořadí (nonce 7 před 6) by platná navazující transakce propadla.
        #      Mezi odesílateli se transakce prokládají podle původního pořadí
        #      zápisu, aby kapacitní politika mempoolu (rezerva pro nadmediánovou
        #      sazbu, vytěsňování) viděla transakce co nejpodobněji původnímu
        #      příjmu.
        #   3) Transakce s očekávanou nonce projde add_transaction(), tedy PŘESNĚ
        #      týmiž pravidly jako transakce přijatá ze sítě: chain_id, formát
        #      adres, identita odesílatele, podpis, částka, poplatek (jen
        #      fee >= TX_FEE_MIN), timestamp a expirace, nonce a zůstatek
        #      KUMULOVANĚ se všemi už přijatými transakcemi téže adresy.
        #      Vlastní kopie pravidel tu záměrně není - rozešla by se
        #      s add_transaction() při první budoucí úpravě.
        #   4) Chybí-li u adresy platná transakce s očekávanou nonce, vznikne
        #      v posloupnosti díra a všechny navazující transakce téže adresy
        #      jsou nevytěžitelné, takže se odstraní také - stejné pravidlo jako
        #      v cleanup_mempool() a mine(). Transakce, jejíž nonce už spotřeboval
        #      řetězec, posloupnost nepřerušuje: jen se zahodí jako zastaralá
        #      a další transakce téže adresy se posuzují normálně.
        #
        # Vrací (počet ponechaných, počet odstraněných). Zápis výsledku do
        # mempool.db zajišťuje volající (load_mempool). Výpisy jdou přes print(),
        # protože při startu p2p_node (a tedy ani jeho log) ještě neexistuje.
        with self.lock:
            odstranene = 0

            def odstran(tx, duvod):
                nonlocal odstranene
                odstranene += 1
                print(f"{Fore.YELLOW}  Odstraněno z mempoolu: {tx.tx_id} - {duvod}{Style.RESET_ALL}")

            # Pojistka proti duplicitnímu tx_id v uložených datech. V mempool.db
            # je tx_id PRIMARY KEY, takže by k tomu nemělo dojít.
            videne = set()
            unikatni = []
            for poradi, (tx, allow_expired) in enumerate(kandidati):
                if tx.tx_id in videne:
                    odstran(tx, "duplicitní TX ID v uloženém mempoolu")
                    continue
                videne.add(tx.tx_id)
                unikatni.append((poradi, tx, allow_expired))

            # 1) Už vytěžené transakce.
            vytezene = self.tx_ids_in_chain([tx.tx_id for _, tx, _ in unikatni])

            # 2) Rozdělení podle odesílatele; v rámci odesílatele podle nonce,
            #    při shodné nonce podle pořadí zápisu.
            zasobniky = defaultdict(list)
            for poradi, tx, allow_expired in unikatni:
                if tx.tx_id in vytezene:
                    odstran(tx, "už je zahrnutá v blockchainu (vytěžená)")
                    continue
                if tx.from_address == "COINBASE":
                    odstran(tx, "COINBASE transakce do mempoolu nepatří")
                    continue
                zasobniky[tx.from_address].append((tx.nonce, poradi, tx, allow_expired))

            # Halda vybírá mezi odesílateli toho, jehož nejbližší transakce (v
            # pořadí nonce) byla zapsaná nejdřív. Pořadí nonce uvnitř adresy tím
            # zůstává zachované vždy.
            halda = []
            pozice = {}
            for odesilatel, polozky in zasobniky.items():
                polozky.sort(key=lambda p: (p[0], p[1]))
                pozice[odesilatel] = 0
                heapq.heappush(halda, (polozky[0][1], odesilatel))

            prijate = []
            preruseno = {}
            while halda:
                _, odesilatel = heapq.heappop(halda)
                polozky = zasobniky[odesilatel]
                i = pozice[odesilatel]
                pozice[odesilatel] = i + 1
                if i + 1 < len(polozky):
                    heapq.heappush(halda, (polozky[i + 1][1], odesilatel))
                _, _, tx, allow_expired = polozky[i]

                # 4) Po díře v posloupnosti už nic z téže adresy neprojde.
                if odesilatel in preruseno:
                    odstran(tx, preruseno[odesilatel])
                    continue

                # Nonce už spotřebovaná řetězcem: vytěžená byla jiná transakce
                # téže adresy se stejnou nonce (vlastní tx_id by zachytil krok 1).
                potvrzena_dalsi = self.nonce_map.get(odesilatel, -1) + 1
                if tx.nonce < potvrzena_dalsi:
                    odstran(tx, f"nonce {tx.nonce} už v blockchainu spotřebovala jiná transakce téže adresy (zastaralá)")
                    continue

                ocekavana = self.get_next_nonce(odesilatel)
                if tx.nonce < ocekavana:
                    # Tuto nonce už v mempoolu drží dříve přijatá platná
                    # transakce téže adresy.
                    odstran(tx, f"duplicitní nonce {tx.nonce} - tuto nonce už v mempoolu má jiná platná transakce téže adresy")
                    continue
                if tx.nonce > ocekavana:
                    odstran(tx, f"díra v posloupnosti nonce (očekávána {ocekavana}, transakce má {tx.nonce})")
                    preruseno[odesilatel] = f"navazuje na chybějící nebo odstraněnou transakci s nonce {ocekavana} (díra v posloupnosti nonce)"
                    continue

                # 3) Plné ověření týmiž pravidly jako transakce ze sítě.
                puvodni_deadline = tx.mempool_deadline
                if self.add_transaction(tx, allow_expired=allow_expired):
                    if allow_expired:
                        # add_transaction() dá transakci vrácené reorgem novou
                        # lhůtu počítanou od "teď". Obnova po restartu ale není
                        # návrat z reorgu: lhůta běží od původního návratu do
                        # mempoolu a restart ji nesmí prodlužovat. Strop
                        # "teď + MEMPOOL_TX_EXPIRATION" chrání před nesmyslnou
                        # hodnotou z poškozeného souboru.
                        tx.mempool_deadline = min(puvodni_deadline, get_time() + MEMPOOL_TX_EXPIRATION)
                    prijate.append(tx)
                else:
                    # Posloupnost se tu ještě nepřerušuje: může následovat jiný
                    # kandidát se stejnou nonce. Pokud nenásleduje, zachytí díru
                    # kontrola "tx.nonce > ocekavana" u další transakce adresy.
                    odstran(tx, "neprošla ověřením podle aktuálních pravidel (konkrétní důvod je vypsaný o řádek výš)")

            # add_transaction() může při plném mempoolu vytěsnit dříve přijatou
            # transakci s nižší sazbou poplatku - ta pak v mempoolu už není.
            ponechane = 0
            for tx in prijate:
                if tx.tx_id in self.mempool_by_txid:
                    ponechane += 1
                else:
                    odstran(tx, "vytěsněna z plného mempoolu transakcí s vyšší sazbou poplatku")

            return ponechane, odstranene

    def create_genesis_block(self):
        genesis_tx = Transaction(
            from_address="COINBASE",
            to_address=GENESIS_ADDRESS,
            amount=GENESIS_AMOUNT,
            fee=0,
            nonce=0,
            public_key=None,
            signature=None,
            timestamp=GENESIS_TIMESTAMP,
            data="BTC: 000000000000000000009c26a9609e1956765cb1a89fb4cdd2411b75f208dd76"
        )
        genesis_block = Block(0, [genesis_tx], "0", FIXED_TARGET, nonce=GENESIS_NONCE, timestamp=GENESIS_TIMESTAMP, version=BLOCK_VERSION, chain_id=CHAIN_ID)

        # state_root genesis bloku je deterministický, dopočítá se sám: coinbase
        # odměna jde do immature_rewards, takže accounts_root je prázdný strom a
        # total_supply = GENESIS_AMOUNT. Ručně je potřeba doplnit jen GENESIS_NONCE
        # a GENESIS_BLOCK_EXPECTED_HASH (viz poznámka u konstant).
        genesis_shadow = make_state_shadow(
            {'balance_map': {}, 'nonce_map': {}, 'immature_rewards': {}, 'total_supply': 0, 'cumulative_work': 0}
        )
        self.update_state_with_block(genesis_block, state_target=genesis_shadow)
        genesis_block.state_root = compute_state_root_from(genesis_shadow)
        genesis_block.hash = genesis_block.compute_hash()

        self.chain.append(genesis_block)
        self.max_block_index = 0
        self.update_state_with_block(genesis_block)
        print(f"{Fore.GREEN}Genesis blok vytvořen a přidán do řetězce!{Style.RESET_ALL}")

    def state_root_po_bloku(self, block):
        """OPRAVA N-11: state root po aplikaci bloku na AKTUÁLNÍ vrchol.

        Nic se nekopíruje: mapy jsou překryvné (_PrekryvnaMapa), immature
        odměny se zkopírují (~COINBASE_MATURITY položek) a kořen SMT se spočítá
        bez změny stromu přes root_with_changes(). Výsledek je bit za bitem
        shodný s make_state_shadow() + compute_state_root_from() - ověřeno
        diferenciálním testem t_fix11_smt_diff.py a regresí nad řetězci.
        Volat se drženým self.lock. Chyby stavu (záporný zůstatek apod.) jdou
        ven jako ValueError, stejně jako dřív.
        """
        stin = SimpleNamespace(
            balance_map=_PrekryvnaMapa(self.balance_map),
            nonce_map=_PrekryvnaMapa(self.nonce_map),
            immature_rewards=dict(self.immature_rewards),
            total_supply=self.total_supply,
            cumulative_work=self.cumulative_work,
            undo_logs={},
            state_checkpoints={},
            # OPRAVA AUDIT-13: stín se po výpočtu kořene zahodí, takže nemá smysl
            # do něj vyrábět checkpoint stavu - viz update_state_with_block().
            checkpointy_povolene=False,
            accounts_smt=None,
        )
        self.update_state_with_block(block, state_target=stin)
        smt = _state_smt(self)
        if smt is None:
            return compute_state_root(stin.balance_map.copy(), stin.nonce_map.copy(),
                                      stin.immature_rewards, stin.total_supply)
        zmeny = {}
        for adresa in set(stin.balance_map.zmeny) | set(stin.nonce_map.zmeny):
            if adresa in stin.nonce_map or stin.balance_map.get(adresa, 0):
                zmeny[adresa] = (stin.balance_map.get(adresa, 0), stin.nonce_map.get(adresa, -1))
            else:
                zmeny[adresa] = None
        return _state_root_bytes(smt.root_with_changes(zmeny), stin.immature_rewards, stin.total_supply)

    def update_state_with_block(self, block, state_target=None):
        # state_target umožňuje zapisovat stav (balance_map, nonce_map, undo_logs, ...)
        # do jiného nosiče než self (využívá is_valid_chain, aby v jediném průchodu
        # zároveň validovala i stavěla state, aniž by mutovala self dřív, než je
        # celý řetězec ověřen jako platný). Výchozí chování (state_target=None) je
        # beze změny a zapisuje přímo do self, stejně jako doposud.
        target = state_target if state_target is not None else self

        if not hasattr(target, 'undo_logs'):
            target.undo_logs = {}
            
        undo_data = {
            'balance_changes': defaultdict(int),
            'nonce_restores': {},
            'immature_restores': {},
            'immature_removes': [],
            'cumulative_work_change': 0,
            'total_supply_change': 0
        }

        touched_addresses = set()

        target_index = block.index - COINBASE_MATURITY
        if target_index in target.immature_rewards:
            reward_data = target.immature_rewards.pop(target_index)
            mature_address = reward_data['address']
            mature_amount = reward_data['amount']
            target.balance_map[mature_address] = target.balance_map.get(mature_address, 0) + mature_amount
            touched_addresses.add(mature_address)
            
            undo_data['immature_restores'][target_index] = reward_data
            undo_data['balance_changes'][mature_address] -= mature_amount

        for tx in block.transactions:
            if tx.from_address == "COINBASE":
                target.immature_rewards[block.index] = {'address': tx.to_address, 'amount': tx.amount}
                undo_data['immature_removes'].append(block.index)
            else:
                target.balance_map[tx.from_address] = target.balance_map.get(tx.from_address, 0) - tx.amount - tx.fee
                target.balance_map[tx.to_address] = target.balance_map.get(tx.to_address, 0) + tx.amount
                touched_addresses.add(tx.from_address)
                touched_addresses.add(tx.to_address)
                
                undo_data['balance_changes'][tx.from_address] += (tx.amount + tx.fee)
                undo_data['balance_changes'][tx.to_address] -= tx.amount
                
                if tx.from_address not in undo_data['nonce_restores']:
                    undo_data['nonce_restores'][tx.from_address] = target.nonce_map.get(tx.from_address, -1)
                target.nonce_map[tx.from_address] = max(target.nonce_map.get(tx.from_address, -1), tx.nonce)

        # Kanonizace stavu (viz prune_zero_balances). rollback_state() a
        # get_state_at() nulové účty mazaly už dřív, dopředná aplikace bloku ne -
        # dva uzly ve stejném logickém stavu tak měly různou balance_map.
        prune_zero_balances(target.balance_map, touched_addresses)

        # OPRAVA F-03: přírůstková aktualizace SMT. Blok změní jen adresy
        # v touched_addresses (zralá coinbase odměna + odesílatelé a příjemci),
        # takže se přepočítají jen cesty od těchto listů ke kořeni. Zbytek
        # stromu se bere z cache podstromů. Bez tohohle se strom stavěl celý
        # znovu na každý blok: 984 ms při 100 000 účtech, čtyřikrát na blok.
        smt = _state_smt(target)
        if smt is not None and touched_addresses:
            smt.sync_from_maps(target.balance_map, target.nonce_map, touched=touched_addresses)

        work = (1 << 256) // block.target if block.target > 0 else 0
        target.cumulative_work += work
        undo_data['cumulative_work_change'] = work

        halvings = block.index // HALVING_INTERVAL_BLOCKS
        subsidy = GENESIS_AMOUNT if block.index == 0 else subsidy_po_halvingu(halvings)
        subsidy = max(0, min(subsidy, MAX_SUPPLY - target.total_supply))
            
        target.total_supply += subsidy
        undo_data['total_supply_change'] = subsidy

        target.undo_logs[block.index] = undo_data
        while len(target.undo_logs) > LAST_BLOCKS_TO_KEEP:
            oldest = min(target.undo_logs.keys())
            del target.undo_logs[oldest]
            
        # Perodické databázové checkpointy pro zrychlení rebuild_state
        #
        # OPRAVA AUDIT-13: podmínka `checkpointy_povolene`. Checkpoint se dřív
        # vyráběl i nad ZAHAZOVANÝMI stínovými stavy, kde se hned poté zahodil
        # spolu s celým nosičem. U _PrekryvnaMapa (state_root_po_bloku) navíc
        # .copy() materializuje CELOU základní mapu, ne jen vrstvu změn, takže
        # cena rostla s počtem účtů, ne s počtem změn v bloku - naměřeno
        # 2× 60 001 položek na jeden blok při 60 000 účtech. Cesta je přitom
        # horká: state_root_po_bloku() volá mine() i rychlá cesta add_block(),
        # tedy u každého 1000. bloku dvakrát.
        #
        # POZOR: nestačí podmínka `target is self`. _is_valid_chain_inner()
        # staví checkpointy do vlastního nosiče (ř. 4835) ZÁMĚRNĚ - vrací je
        # ven jako 'state_checkpoints' (ř. 5198) a load_data() je přebírá do
        # droid_chain (ř. 6320). Příznak proto nesou jen ty nosiče, které se
        # opravdu zahazují: stín ve state_root_po_bloku() a make_state_shadow().
        # Výchozí hodnota je True, takže self i nosič is_valid_chain() se chovají
        # přesně jako dřív.
        if (block.index > 0 and block.index % 1000 == 0
                and getattr(target, 'checkpointy_povolene', True)):
            if not hasattr(target, 'state_checkpoints'):
                target.state_checkpoints = {}
            target.state_checkpoints[block.index] = {
                'balance_map': target.balance_map.copy(),
                'nonce_map': target.nonce_map.copy(),
                'immature_rewards': copy.deepcopy(target.immature_rewards),
                'total_supply': target.total_supply,
                'cumulative_work': target.cumulative_work
            }
            checkpoint_keys = sorted(target.state_checkpoints.keys())
            while len(checkpoint_keys) > 5:
                del target.state_checkpoints[checkpoint_keys.pop(0)]

    def rollback_state(self, to_index):
        if not hasattr(self, 'undo_logs'):
            self.undo_logs = {}
        current_max = self.max_block_index
        
        if to_index < current_max - LAST_BLOCKS_TO_KEEP:
            self.rebuild_state(up_to_index=to_index)
            return

        for i in range(current_max, to_index, -1):
            if i not in self.undo_logs:
                self.rebuild_state(up_to_index=to_index)
                return
            
            undo_data = self.undo_logs[i]
            
            self.total_supply -= undo_data['total_supply_change']
            self.cumulative_work -= undo_data['cumulative_work_change']
            
            for addr, change in undo_data['balance_changes'].items():
                self.balance_map[addr] = self.balance_map.get(addr, 0) + change
                if self.balance_map[addr] == 0:
                    del self.balance_map[addr]

            for addr, old_nonce in undo_data['nonce_restores'].items():
                if old_nonce == -1:
                    if addr in self.nonce_map:
                        del self.nonce_map[addr]
                else:
                    self.nonce_map[addr] = old_nonce

            for idx, reward_data in undo_data['immature_restores'].items():
                self.immature_rewards[idx] = reward_data

            for idx in undo_data['immature_removes']:
                if idx in self.immature_rewards:
                    del self.immature_rewards[idx]

            # OPRAVA F-03: zpětný chod musí strom udržet stejně jako dopředný,
            # jinak by po reorgu ukazoval stav, který už neplatí. Dotčené
            # adresy jsou přesně ty z undo logu.
            smt = _state_smt(self)
            if smt is not None:
                dotcene = set(undo_data['balance_changes'].keys())
                dotcene.update(undo_data['nonce_restores'].keys())
                if dotcene:
                    smt.sync_from_maps(self.balance_map, self.nonce_map, touched=dotcene)

            del self.undo_logs[i]
            
        self.max_block_index = to_index

    def get_state_at(self, target_index):
        # OPRAVA AUDIT-2: pro target_index NAD vrcholem byl range(max, target, -1)
        # prázdný, smyčka odrolování neproběhla a funkce vrátila aktuální stav
        # vrcholu označený jako stav na jiné výšce. Ověřeno: get_state_at(2**40)
        # nad řetězcem o 32 blocích vrátilo total_supply z vrcholu místo None.
        #
        # Kontrakt "None znamená nevím" je základ, na kterém OPRAVA D-16 staví
        # rozlišení mezi "fork je prokazatelně neplatný" a "nedokážu
        # rozhodnout" - právě to brání tomu, aby každý neplatný fork spouštěl
        # revalidaci celého řetězce.
        if target_index > self.max_block_index:
            return None

        # OPRAVA F-03: k vrácenému stavu se přikládá i KLON udržovaného SMT.
        # Pro aktuální vrchol je klon přesný; pro starší index se do něj
        # promítne totéž odrolování jako do map (viz níž).
        smt_self = _state_smt(self)
        if target_index == self.max_block_index:
            return {
                'balance_map': dict(self.balance_map),
                'nonce_map': dict(self.nonce_map),
                'total_supply': self.total_supply,
                'cumulative_work': self.cumulative_work,
                'immature_rewards': dict(self.immature_rewards),
                'accounts_smt': smt_self.clone() if smt_self is not None else None
            }
            
        if not hasattr(self, 'undo_logs') or target_index < self.max_block_index - LAST_BLOCKS_TO_KEEP:
            return None
        
        state = {
            'balance_map': dict(self.balance_map),
            'nonce_map': dict(self.nonce_map),
            'total_supply': self.total_supply,
            'cumulative_work': self.cumulative_work,
            'immature_rewards': dict(self.immature_rewards),
            'accounts_smt': smt_self.clone() if smt_self is not None else None
        }
        
        for i in range(self.max_block_index, target_index, -1):
            undo_data = self.undo_logs.get(i)
            if not undo_data: return None
            
            state['total_supply'] -= undo_data['total_supply_change']
            state['cumulative_work'] -= undo_data['cumulative_work_change']
            
            for addr, change in undo_data['balance_changes'].items():
                state['balance_map'][addr] = state['balance_map'].get(addr, 0) + change
                if state['balance_map'][addr] == 0:
                    del state['balance_map'][addr]
                    
            for addr, old_nonce in undo_data['nonce_restores'].items():
                if old_nonce == -1:
                    state['nonce_map'].pop(addr, None)
                else:
                    state['nonce_map'][addr] = old_nonce
                    
            for idx, reward_data in undo_data['immature_restores'].items():
                state['immature_rewards'][idx] = reward_data
                
            for idx in undo_data['immature_removes']:
                state['immature_rewards'].pop(idx, None)

            # OPRAVA F-03: strom se odroluje spolu s mapami.
            if state['accounts_smt'] is not None:
                dotcene = set(undo_data['balance_changes'].keys())
                dotcene.update(undo_data['nonce_restores'].keys())
                if dotcene:
                    state['accounts_smt'].sync_from_maps(
                        state['balance_map'], state['nonce_map'], touched=dotcene)
        
        return state

    def rebuild_state(self, up_to_index=None):
        # OPRAVA M-2: spojení je nově pod try/finally a Block.from_dict() nad
        # ŘÁDKY Z VLASTNÍ DB je ošetřená. Dřív tu nebylo ani jedno: poškozený
        # řádek (ValueError) nebo sqlite3.OperationalError ("disk I/O error",
        # "database is locked") nechal spojení viset a proletěl ven přes
        # rollback_state() až z add_block(), který na to nemá žádný try - viz
        # OPRAVA M-2 v mutační sekci add_block(). Cílová platforma je Termux na
        # flash paměti, kde I/O chyba není teorie.
        #
        # Poškozený řádek se ZÁMĚRNĚ nepřeskakuje: přeskočením by vznikl tiše
        # nesprávný stav, což je fail-open v konsenzuálním kódu. Místo toho jde
        # ven MissingChainDataError, tedy týž typ, kterým už kód hlásí "chybí
        # data nutná pro rozhodnutí" (viz OPRAVA F-05), a volající se podle něj
        # umí zařídit.
        conn = None
        try:
            conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
            conn.execute("PRAGMA journal_mode=WAL;")
            c = conn.cursor()

            target_index = up_to_index if up_to_index is not None else float('inf')
            start_index = 0
            closest_checkpoint = 0

            if hasattr(self, 'state_checkpoints') and self.state_checkpoints:
                valid_checkpoints = [k for k in self.state_checkpoints.keys() if k <= target_index]
                if valid_checkpoints:
                    closest_checkpoint = max(valid_checkpoints)

            if closest_checkpoint > 0:
                checkpoint = self.state_checkpoints[closest_checkpoint]
                self.balance_map = checkpoint['balance_map'].copy()
                self.nonce_map = checkpoint['nonce_map'].copy()
                self.immature_rewards = copy.deepcopy(checkpoint['immature_rewards'])
                self.total_supply = checkpoint['total_supply']
                self.cumulative_work = checkpoint['cumulative_work']
                self.undo_logs = {k: v for k, v in self.undo_logs.items() if k <= closest_checkpoint}
                start_index = closest_checkpoint + 1
            else:
                self.balance_map = {}
                self.nonce_map = {}
                self.immature_rewards = {}
                self.cumulative_work = 0
                self.total_supply = 0
                self.undo_logs = {}

            # OPRAVA F-03: mapy se právě celé nahradily, takže se strom staví
            # jednorázově od nuly. Od téhle chvíle ho update_state_with_block()
            # udržuje přírůstkově, blok po bloku.
            self.accounts_smt = build_accounts_smt(self.balance_map, self.nonce_map)

            query = "SELECT block_index, timestamp, transactions, previous_hash, target_hex, nonce, block_hash, merkle_root, version, chain_id, state_root FROM blocks WHERE block_index >= ?"
            params = [start_index]
            if up_to_index is not None:
                query += " AND block_index <= ?"
                params.append(up_to_index)

            c.execute(query + " ORDER BY block_index", tuple(params))

            for row in c:
                try:
                    block_data = {
                        'index': row[0],
                        'timestamp': row[1],
                        'transactions': json.loads(row[2]),
                        'previous_hash': row[3],
                        'target': row[4],
                        'nonce': row[5],
                        'hash': row[6],
                        'merkle_root': row[7],
                        'version': row[8],
                        'chain_id': row[9], 'state_root': row[10]
                    }
                    block = Block.from_dict(block_data)
                except (ValueError, KeyError, TypeError, struct.error,
                        OverflowError, json.JSONDecodeError) as e:
                    raise MissingChainDataError(
                        f"Blok #{row[0]} v blockchain.db je poškozený a nelze z něj "
                        f"přehrát stav ({type(e).__name__}: {e})."
                    ) from e
                self.update_state_with_block(block)
        finally:
            if conn is not None:
                try:
                    conn.close()
                except Exception:
                    pass

        if up_to_index is not None:
            self.max_block_index = up_to_index

    def _resync_memory_from_db(self):
        """OPRAVA M-2: dorovná paměť k databázi a vrátí True/False podle úspěchu.

        Používá se jako ŘÍZENÉ ZOTAVENÍ tam, kde mutace paměti selže ZA commitem.
        Do commitu vede každá chyba na "blok nebyl přijat" a stav uzlu zůstává
        netknutý (OPRAVA A-2); za commitem už je blok v DB nezvratně, takže
        vrátit False nad polovičním přechodem by paměť a DB rozešlo natrvalo -
        táž třída chyby, kterou popisuje OPRAVA A-1, jen o patro níž.

        Databáze je tu autoritativní: stav se přehraje z ní, okno posledních
        bloků se načte znovu. Checkpointy i undo logy se zahazují ZÁMĚRNĚ -
        mohly vzniknout nad větví, kterou právě proběhlý mini-reorg opustil,
        a přehrát stav z takového checkpointu by chybu jen zakonzervovalo.
        Přehrání od genesis je pomalé, ale tohle je havarijní cesta, kde má
        správnost přednost před rychlostí.
        """
        conn = None
        try:
            conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=5.0)
            conn.execute("PRAGMA journal_mode=WAL;")
            c = conn.cursor()
            c.execute("SELECT MAX(block_index) FROM blocks")
            row = c.fetchone()
            tip = row[0] if row and row[0] is not None else None
            if tip is None:
                return False
            c.execute("SELECT block_index, timestamp, transactions, previous_hash, target_hex, nonce, block_hash, merkle_root, version, chain_id, state_root FROM blocks WHERE block_index >= ? ORDER BY block_index",
                      (max(0, tip - LAST_BLOCKS_TO_KEEP + 1),))
            # OPRAVA Z-2 (nález 2): streamovaný kurzor místo fetchall(). Tohle je
            # HAVARIJNÍ cesta - volá se, když mutace paměti selhala za commitem -
            # takže je to poslední místo, kde si uzel smí dovolit držet naráz
            # syrové řádky i objekty z nich (u plných bloků ~1,2 GB navíc).
            nove_okno = [Block.from_dict({
                'index': r[0], 'timestamp': r[1], 'transactions': json.loads(r[2]),
                'previous_hash': r[3], 'target': r[4], 'nonce': r[5], 'hash': r[6],
                'merkle_root': r[7], 'version': r[8], 'chain_id': r[9], 'state_root': r[10]
            }) for r in c]
        except Exception:
            return False
        finally:
            if conn is not None:
                try:
                    conn.close()
                except Exception:
                    pass

        if not nove_okno or nove_okno[-1].index != tip:
            return False

        self.state_checkpoints = {}
        self.undo_logs = {}
        try:
            self.rebuild_state(up_to_index=tip)
        except Exception:
            return False

        self.chain = nove_okno
        self.max_block_index = tip
        return True

    def get_block_from_db(self, index, conn=None):
        # OPRAVA A-5: volitelné sdílené spojení, stejně jako u tx_ids_in_chain
        # po OPRAVĚ D-05. Dřív si každé volání otevíralo vlastní connect()
        # + PRAGMA + dotaz + close(), a protože calculate_expected_target()
        # potřebuje 145 předchůdců a get_median_time_past() 11, dělalo to při
        # reorgu do hloubky 50 celkem 6 141 otevření spojení (99,2 % z nich
        # právě tady) a extrapolovaně ~150 000 při MAX_REORG_DEPTH. Celé pod
        # self.lock, takže uzel po tu dobu nepřijímal bloky ani netěžil.
        vlastni_conn = conn is None
        if vlastni_conn:
            conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
        try:
            # OPRAVA K-4 (audit 21. 10. 2026, nález 4): PRAGMA stála PŘED try:, takže ji
            # conn.close() ve finally nekrylo. sqlite3.connect() je líná a nad
            # poškozeným souborem uspěje; první skutečný dotaz - tedy právě
            # tahle PRAGMA - vyhodí sqlite3.DatabaseError ("file is not a
            # database") a deskriptor zůstal viset až do cyklického GC.
            # Nad ZAMČENOU WAL databází PRAGMA projde, takže běžný souběh
            # problém nedělal; poškozený soubor ano. Nedokončená OPRAVA S-7 -
            # ostatní cesty v souboru už správný vzorec mají (viz
            # get_iterable(), proposed_chain_iterator(), load_mempool()).
            if vlastni_conn:
                conn.execute("PRAGMA journal_mode=WAL;")
            c = conn.cursor()
            c.execute("SELECT block_index, timestamp, transactions, previous_hash, target_hex, nonce, block_hash, merkle_root, version, chain_id, state_root FROM blocks WHERE block_index = ?", (index,))
            row = c.fetchone()
        finally:
            if vlastni_conn:
                try:
                    conn.close()
                except Exception:
                    pass
        if row:
            block_data = {
                'index': row[0],
                'timestamp': row[1],
                'transactions': json.loads(row[2]),
                'previous_hash': row[3],
                'target': row[4],
                'nonce': row[5],
                'hash': row[6],
                'merkle_root': row[7],
                'version': row[8],
                'chain_id': row[9], 'state_root': row[10]
            }
            return Block.from_dict(block_data)
        return None

    def _load_header_window(self, first_index, last_index, chain_dict=None, conn=None):
        # OPRAVA A-5 (klouzavé okno): okna MTP a LWMA-3 se u sousedních výšek
        # překrývají z ~99 %, ale kód je četl blok po bloku a každý blok si
        # otevíral vlastní spojení. Nově jeden dotaz BETWEEN na celý chybějící
        # rozsah.
        #
        # Druhá polovina úspory: oběma funkcím stačí timestamp a target, takže
        # se sloupec `transactions` vůbec nečte. Dřív se každý blok v okně
        # deserializoval celý včetně výpočtu tx_id každé transakce - u plných
        # bloků ~1 600 transakcí na blok, jen aby se z výsledku přečetlo jedno
        # číslo. Hlavičky proto vracíme jako lehký SimpleNamespace; oba
        # konzumenti z nich čtou právě .timestamp a .target.
        #
        # PRAGMA journal_mode=WAL se tu záměrně nenastavuje: režim žurnálu je
        # v souboru databáze trvalý, takže na čtecí cestě je to jen zbytečný
        # zápis navíc v nejteplejší smyčce validace.
        pamet = chain_dict if chain_dict is not None else {b.index: b for b in self.chain}

        okno = {}
        chybejici = []
        for i in range(first_index, last_index + 1):
            b = pamet.get(i)
            if b is not None:
                okno[i] = b
            else:
                chybejici.append(i)

        if not chybejici:
            return okno

        vlastni_conn = conn is None
        if vlastni_conn:
            conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
        try:
            c = conn.cursor()
            c.execute("SELECT block_index, timestamp, target_hex FROM blocks WHERE block_index BETWEEN ? AND ?",
                      (chybejici[0], chybejici[-1]))
            for row in c.fetchall():
                idx = row[0]
                if idx in okno:
                    continue
                try:
                    target = int(row[2], 16) if isinstance(row[2], str) else int(row[2])
                    timestamp = int(row[1])
                except (TypeError, ValueError):
                    # Nečitelný řádek se chová jako chybějící blok: volající
                    # vyhodí MissingChainDataError, tedy odmítnutí, ne fail-open.
                    continue
                if target <= 0 or timestamp < 0:
                    continue
                okno[idx] = SimpleNamespace(index=idx, timestamp=timestamp, target=target)
        finally:
            if vlastni_conn:
                try:
                    conn.close()
                except Exception:
                    pass
        return okno

    def get_block(self, index):
        for b in self.chain:
            if b.index == index:
                return b
        return self.get_block_from_db(index)

    def get_last_block(self):
        if self.chain:
            return self.chain[-1]
        return self.get_block_from_db(self.max_block_index)

    # OPRAVA T-4 (Nález 2): get_previous_block() odstraněna - mrtvý kód.
    # Konsenzuální cesty si předchůdce berou přes get_block_by_index()
    # nebo get_block_from_db(), žádná z nich tudy nešla.

    def get_next_nonce(self, address):
        with self.lock:
            expected_nonce = self.nonce_map.get(address, -1) + 1
            # OPRAVA D-04: dřív další průchod celým mempoolem při každém volání,
            # a add_transaction() ho volá dvakrát. Index dá rovnou jen transakce
            # téhle adresy (max. MAX_PENDING_TX_PER_ADDRESS).
            mempool_nonces = {tx.nonce for tx in self.mempool_by_sender.get(address, [])}
            while expected_nonce in mempool_nonces:
                expected_nonce += 1
            return expected_nonce

    # OPRAVA #15: get_balance() odstraněna - nikdo ji nevolal.
    #
    # OPRAVA T-4 (Nález 2a): původní znění tohohle komentáře tvrdilo, že kód
    # "si vybírá explicitně mezi get_confirmed_balance() a
    # get_pending_balance()". To nebyla pravda - get_pending_balance()
    # nevolalo nic a byla to past. Vracela totiž DELTU včetně PŘÍCHOZÍCH
    # nepotvrzených plateb:
    #
    #     balance_change -= tx.amount + tx.fee   # odchozí
    #     balance_change += tx.amount            # příchozí se připisovalo
    #
    # kdežto volba 1 v menu počítá útratný zůstatek záměrně jinak - jen jako
    # confirmed minus odchozí, a příchozí nepotvrzené ukazuje zvlášť, mimo
    # útratnou částku. Kdo by se tím komentářem řídil a metodu zapojil, začal
    # by uživateli nabízet k útratě prostředky, které ještě nejsou v bloku.
    #
    # Metoda je proto odstraněná taky. Jediný zůstatek, který třída poskytuje,
    # je get_confirmed_balance(); nepotvrzená část se počítá na místě spotřeby,
    # kde je zároveň vidět, jaká sémantika se tam zrovna hodí.

    def get_confirmed_balance(self, wallet_address):
        return self.balance_map.get(wallet_address, 0)

    def get_total_supply(self):
        return self.total_supply

    def get_cumulative_work(self, up_to_index=None):
        if up_to_index is None or up_to_index == self.max_block_index:
            return self.cumulative_work
        total_work = 0
        # OPRAVA L-3: spojení bez try/finally na cestě dosažitelné ze sítě
        # (replace_chain -> get_cumulative_work). Navíc se tu dělalo
        # int(row[0], 16) bez ošetření: nad poškozeným řádkem odsud letěl
        # ValueError do cesty, která s ním nepočítá. Zachytil ho až obecný
        # except v replace_chain(), takže se to projevilo "jen" jako odmítnutí
        # a netěsné spojení - ale fail-closed to bylo náhodou, ne záměrem.
        #
        # Poškozený target se nepřeskakuje: vrátit menší práci, než řetězec
        # skutečně má, by znamenalo přijmout slabší fork. Při nejistotě se
        # hlásí MissingChainDataError, stejně jako u ostatních konsenzuálních
        # dotazů (OPRAVA F-05).
        conn = None
        try:
            conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
            conn.execute("PRAGMA journal_mode=WAL;")
            c = conn.cursor()
            c.execute("SELECT block_index, target_hex FROM blocks WHERE block_index <= ?", (up_to_index,))
            for row in c:
                try:
                    target = int(row[1], 16)
                except (TypeError, ValueError) as e:
                    raise MissingChainDataError(
                        f"Blok #{row[0]} má v blockchain.db nečitelný target "
                        f"({type(e).__name__}); kumulovanou práci nelze spočítat."
                    ) from e
                work = (1 << 256) // target if target > 0 else 0
                total_work += work
        finally:
            if conn is not None:
                try:
                    conn.close()
                except Exception:
                    pass
        return total_work

    def add_transaction(self, transaction, allow_expired=False, chain_tx_ids=None):
        # allow_expired používají jen recyklační cesty po reorgu
        # (recycle_orphan_transactions a replace_chain). Ze sítě se transakce
        # přijímají vždy s allow_expired=False. Viz OPRAVA #11.
        #
        # OPRAVA W-4 (audit 9. 10. 2026, nález N-4): chain_tx_ids je množina
        # tx_id, o kterých volající UŽ VÍ, že jsou v řetězci - výsledek jediného
        # dávkového tx_ids_in_chain(). Když ji dostaneme, nahradí kontrolu
        # duplicity níž a ušetří jedno sqlite3.connect() NA KAŽDOU transakci.
        #
        # Předat ji smí jen volající, který drží self.lock od okamžiku dávkového
        # dotazu (recycle_orphan_transactions a obnova mempoolu v replace_chain),
        # jinak by mohla být zastaralá. Síťová cesta ji nepředává a chová se
        # přesně jako dřív.
        if not self.lock.acquire(timeout=5):
            print(f"{Fore.RED}System is busy (lock timeout). Try again later.{Style.RESET_ALL}")
            return False
        try:
            if transaction.chain_id != CHAIN_ID:
                print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Transakce patří jiné síti (nesprávné chain_id).")
                return False
            if transaction.from_address == "COINBASE":
                print(f"{Fore.RED}Chyba:{Style.RESET_ALL} COINBASE transakci nelze přidat do mempoolu ručně ani přes síť.")
                return False
            if transaction.from_address != "COINBASE" and transaction.data is not None:
                print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Nepovolená zpráva v ne-coinbase transakci.")
                return False
            
            # OPRAVA D-04: všechny průchody celým mempoolem níž nahrazeny
            # indexy. Seznam transakcí jedné adresy je shora omezený hodnotou
            # MAX_PENDING_TX_PER_ADDRESS (100), takže práce na jeden příjem už
            # neroste s velikostí mempoolu.
            sender_txs = self.mempool_by_sender.get(transaction.from_address, [])
            pending_count = len(sender_txs)
            if pending_count >= MAX_PENDING_TX_PER_ADDRESS:
                print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Dosažen limit maximálního počtu nepotvrzených transakcí pro jednu adresu ({MAX_PENDING_TX_PER_ADDRESS}).")
                return False
                
            # OPRAVA F-02: velikost se zjišťuje tady, ale VYTĚSŇOVÁNÍ se přesunulo
            # až za ověření podpisu a zůstatku (viz níž). Dřív běželo na tomhle
            # místě, tedy dřív, než se transakce vůbec ověřila: nepodepsaná
            # transakce o 9,8 MB s vysokým poplatkem vyhodila 93,5 % mempoolu
            # a teprve pak byla sama zamítnuta. Útočník k tomu nepotřeboval
            # klíč ani jedinou minci.
            tx_size = transaction.get_size()
            if tx_size > MAX_TX_SIZE_BYTES:
                print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Transakce je příliš velká ({tx_size} B). Maximum je {MAX_TX_SIZE_BYTES} B.")
                return False

            if not transaction.is_valid_timestamp(allow_expired=allow_expired):
                print(f"{Fore.RED}Chyba ověření transakce:{Style.RESET_ALL} Timestamp transakce je neplatný.")
                return False
            # OPRAVA W-4: s dodanou množinou (dávkový dotaz volajícího) se tady
            # do databáze vůbec nesahá.
            if chain_tx_ids is None:
                uz_v_retezci = self.is_tx_id_in_chain(transaction.tx_id)
            else:
                uz_v_retezci = transaction.tx_id in chain_tx_ids
            if uz_v_retezci:
                print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Duplicitní TX ID: {transaction.tx_id}. Transakce již existuje v blockchainu.")
                return False
            if transaction.tx_id in self.mempool_by_txid:
                print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Duplicitní TX ID v mempoolu: {transaction.tx_id}.")
                return False
            if not isinstance(transaction.amount, int) or not isinstance(transaction.fee, int) or not isinstance(transaction.nonce, int):
                print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Hodnoty amount, fee a nonce musí být celá čísla.")
                return False
            if transaction.from_address != "COINBASE":
                # OPRAVA F-02: vytěsnění se přesunulo až na konec funkce, takže
                # tady už seznam odesílatele nikdo změnit nemohl. Čte se přesto
                # z indexu (ne z proměnné sender_txs výše), aby kontrola zůstala
                # správná i kdyby se pořadí kroků v budoucnu znovu měnilo.
                nonce_set = {tx.nonce for tx in self.mempool_by_sender.get(transaction.from_address, [])}
                if transaction.nonce in nonce_set:
                    print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Duplicitní nonce {transaction.nonce} pro adresu {transaction.from_address} v mempoolu.")
                    return False
            if transaction.amount <= 0:
                print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Částka transakce musí být větší než 0.")
                return False
            if transaction.amount < MIN_TX_AMOUNT:
                print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Částka transakce je příliš malá. Minimální částka je {format(Decimal(MIN_TX_AMOUNT) / Decimal(10 ** DECIMALS), f'.{DECIMALS}f')} {TICKER}.")
                return False
            if not is_valid_address(transaction.from_address) or not is_valid_address(transaction.to_address):
                print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Neplatný formát adresy odesílatele nebo příjemce.")
                return False
            if not transaction.verify_sender_identity():
                print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Veřejný klíč neodpovídá adrese odesílatele.")
                return False
            if transaction.from_address == transaction.to_address:
                print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Nelze posílat peníze na stejnou adresu.")
                return False
            # ZMĚNA 1: horní mez poplatku (TX_FEE_MAX), která tu po OPRAVĚ #6b
            # zůstala jako politika tohoto uzlu, je odstraněna. Platí jen dolní
            # mez, stejně jako v add_block(), validate_fork() a is_valid_chain().
            # Shora poplatek omezuje už jen kontrola zůstatku níž (amount + fee).
            if not (transaction.fee >= TX_FEE_MIN):
                print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Poplatek za transakci je nižší než minimum ({format(Decimal(TX_FEE_MIN) / Decimal(10 ** DECIMALS), f'.{DECIMALS}f')} {TICKER}).")
                return False
            if transaction.nonce != self.get_next_nonce(transaction.from_address):
                print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Neplatná nonce ({transaction.nonce}). Očekávána: {self.get_next_nonce(transaction.from_address)}.")
                return False
            if not transaction.verify_signature():
                print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Neplatný podpis transakce od {transaction.from_address}")
                return False
            current_available_balance = self.get_confirmed_balance(transaction.from_address)
            # OPRAVA D-04: jen transakce téhož odesílatele, ne celý mempool.
            for tx_in_mempool in self.mempool_by_sender.get(transaction.from_address, []):
                current_available_balance -= (tx_in_mempool.amount + tx_in_mempool.fee)
            if current_available_balance < transaction.amount + transaction.fee:
                print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Nedostatečný zůstatek. K dispozici: {format(Decimal(current_available_balance) / Decimal(10 ** DECIMALS), f'.{DECIMALS}f')} {TICKER}")
                return False

            # OPRAVA F-02: kapacita a vytěsňování až TADY, jako úplně poslední
            # krok před zápisem. Od tohoto řádku výš je transakce plně ověřená -
            # podpis sedí, odesílatel na ni má, nonce navazuje. Teprve taková
            # transakce smí sáhnout na cizí obsah mempoolu.
            #
            # OPRAVA D-03 (beze změny významu): plný mempool není absolutní
            # bariéra. Dřív se odmítlo cokoli bez ohledu na poplatek, takže
            # útočník mohl za 0,00034 DRX zaplnit mempool minimálními
            # transakcemi a nikdo - ani uživatel s milionkrát vyšším poplatkem -
            # se už nedostal dovnitř. To je cenzura sítě za cenu, která je
            # ekonomicky nula.
            cap = self._mempool_cap_for(transaction, tx_size)
            if self.mempool_bytes + tx_size > cap:
                if not self._evict_for(transaction, tx_size, cap):
                    print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Mempool je plný a poplatek transakce nestačí na vytěsnění levnějších.")
                    return False

            if allow_expired:
                # Recyklovaná transakce dostává novou lhůtu od okamžiku návratu
                # do mempoolu, jinak by ji nejbližší cleanup_mempool() zase
                # vyhodil a oprava by neměla žádný efekt.
                transaction.mempool_deadline = get_time() + MEMPOOL_TX_EXPIRATION
            self._mempool_add(transaction)
            return True
        finally:
            self.lock.release()

    def is_tx_id_in_chain(self, tx_id, exclude_from_index=None, conn=None):
        # exclude_from_index: ignoruj transakce zapsané v blocích od tohoto indexu
        # výš. Používá add_block() při mini-reorgu - nahrazovaný blok je v DB ještě
        # přítomný, ale už do řetězce nepatří, takže jeho transakce nesmí platit
        # jako duplicita. Bez toho by konkurenční blok obsahující tytéž uživatelské
        # transakce jako současný vrchol byl chybně odmítnut.
        #
        # OPRAVA D-05: conn je nově volitelný parametr. Původně si funkce
        # otevírala VLASTNÍ sqlite3.connect() a volala se uvnitř cyklu přes
        # transakce bloku: 302 spojení na blok s 300 transakcemi, odhadem
        # ~1 683 na plný blok. Každé spojení znamená otevřít soubor a načíst
        # hlavičku a WAL - v Termuxu na flash paměti násobně dražší než na SSD.
        # Volající, který zpracovává celý blok, teď otevře spojení jednou.
        own_conn = conn is None
        if own_conn:
            conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
        try:
            # OPRAVA K-4: PRAGMA dovnitř try, viz
            # get_block_from_db(). Tuhle metodu volá add_block() pro každý
            # blok, takže nad poškozenou DB unikal deskriptor na každý přijatý
            # blok.
            if own_conn:
                conn.execute("PRAGMA journal_mode=WAL;")
            c = conn.cursor()
            if exclude_from_index is None:
                c.execute("SELECT 1 FROM transactions WHERE tx_id = ? LIMIT 1", (tx_id,))
            else:
                c.execute("SELECT 1 FROM transactions WHERE tx_id = ? AND block_index < ? LIMIT 1",
                          (tx_id, exclude_from_index))
            row = c.fetchone()
            return row is not None
        finally:
            if own_conn:
                conn.close()

    def tx_ids_in_chain(self, tx_ids, exclude_from_index=None, conn=None):
        # OPRAVA D-05: jeden dotaz na CELÝ blok místo jednoho dotazu na každou
        # transakci. Vrací množinu tx_id, které už v řetězci jsou.
        # SQLite má strop na počet parametrů (SQLITE_MAX_VARIABLE_NUMBER,
        # historicky 999), takže se dotaz dělí po dávkách.
        tx_ids = list(tx_ids)
        if not tx_ids:
            return set()
        own_conn = conn is None
        if own_conn:
            conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
        try:
            # OPRAVA K-4: PRAGMA dovnitř try, viz
            # get_block_from_db().
            if own_conn:
                conn.execute("PRAGMA journal_mode=WAL;")
            c = conn.cursor()
            found = set()
            CHUNK = 900
            for start in range(0, len(tx_ids), CHUNK):
                chunk = tx_ids[start:start + CHUNK]
                placeholders = ','.join('?' * len(chunk))
                if exclude_from_index is None:
                    c.execute(f"SELECT tx_id FROM transactions WHERE tx_id IN ({placeholders})", chunk)
                else:
                    c.execute(
                        f"SELECT tx_id FROM transactions WHERE tx_id IN ({placeholders}) AND block_index < ?",
                        chunk + [exclude_from_index]
                    )
                found.update(row[0] for row in c.fetchall())
            return found
        finally:
            if own_conn:
                conn.close()

    def get_target(self):
        # OPRAVA F-05: calculate_expected_target() nově při chybějícím bloku
        # vyhodí MissingChainDataError. Tady ji ZÁMĚRNĚ nechytáme: těžit nad
        # poškozenou DB nemá smysl, protože takový blok by stejně žádný jiný
        # uzel nepřijal. Volající v mine() ji odchytí a těžbu odmítne spustit.
        last_block = self.get_last_block()
        new_block_index = last_block.index + 1
        new_target = self.calculate_expected_target(new_block_index)
        
        if not hasattr(self, 'last_target_log_idx'):
            self.last_target_log_idx = -1
        if new_block_index != self.last_target_log_idx:
            # OPRAVA G-11: `global p2p_node` tu bylo zbytečně - deklarace je nutná jen při PŘIŘAZENÍ, ne při čtení. Odstraněno.
            if 'p2p_node' in globals() and p2p_node is not None:
                p2p_node.add_log(
                    f"{Fore.MAGENTA}ÚPRAVA TARGETU (LWMA-3) na bloku #{new_block_index}:{Style.RESET_ALL}\n"
                    f"  Starý target (hex): {hex(last_block.target)[2:]} -> Nový target (hex): {hex(new_target)[2:]}"
                )
            self.last_target_log_idx = new_block_index
        return new_target

    def get_median_time_past(self, new_block_index, chain_dict=None, conn=None):
        # OPRAVA F-05: chybějící blok v okně dřív medián jen tiše posunul dolů,
        # takže se rozvolnilo časové pravidlo (blok musí být novější než MTP).
        # Stejně jako u targetu platí: chybí-li konsenzuální data, nesmí se
        # rozhodovat, ale odmítat.
        MTP_SPAN = 11
        first_index = max(0, new_block_index - MTP_SPAN)
        if first_index >= new_block_index:
            # Jediný legitimní případ: new_block_index == 0, tedy genesis.
            return GENESIS_TIMESTAMP
        # OPRAVA A-5: jeden dotaz na celé okno místo 11 samostatných spojení.
        okno = self._load_header_window(first_index, new_block_index - 1,
                                        chain_dict=chain_dict, conn=conn)
        timestamps = []
        for i in range(first_index, new_block_index):
            b = okno.get(i)
            if b is None:
                raise MissingChainDataError(
                    f"Blok #{i} chybí v okně MTP pro blok #{new_block_index}."
                )
            timestamps.append(b.timestamp)
        timestamps.sort()
        count = len(timestamps)
        mid = count // 2
        if count % 2 == 1:
            return timestamps[mid]
        return (timestamps[mid - 1] + timestamps[mid]) // 2

    # OPRAVA #15: parametr new_timestamp odstraněn. Funkce ho přijímala, ale
    # nikdy nečetla - navádělo to čtenáře k domněnce, že target závisí i na
    # čase nově těženého bloku. LWMA-3 ho počítá výhradně z časů a targetů
    # už existujících bloků [index-N-1, index-1].
    def calculate_expected_target(self, new_block_index, chain_dict=None, conn=None):
        N = DIFFICULTY_ADJUSTMENT_INTERVAL
        
        if new_block_index <= N:
            return FIXED_TARGET
            
        first_index = new_block_index - N - 1
        if first_index < 0:
            return FIXED_TARGET

        # OPRAVA A-5: 145 předchůdců se načte jedním dotazem místo 145 spojení,
        # a bez sloupce `transactions`, takže se neparsuje ani nepočítá tx_id.
        okno = self._load_header_window(first_index, new_block_index - 1,
                                        chain_dict=chain_dict, conn=conn)
        blocks = []
        for i in range(first_index, new_block_index):
            b = okno.get(i)
            if b is None:
                # OPRAVA F-05: dřív se tu vracel FIXED_TARGET, tedy nejsnazší
                # povolená obtížnost. Chybějící blok v okně LWMA-3 je porucha,
                # ne pokyn "pusť cokoli".
                raise MissingChainDataError(
                    f"Blok #{i} chybí v okně LWMA-3 pro blok #{new_block_index}."
                )
            blocks.append(b)
                
        sum_target = 0
        t = 0
        # OPRAVA N-3 (HARD FORK): solvetime se dřív ořezával asymetricky na
        # [-3T, +6T] a záporné hodnoty byly povolené. Blok s časem na hraně
        # pravidla (+600 s) si tak připsal +360 s, zatímco následující poctivý
        # blok ubral jen 180 s - každý takový blok nafoukl měřený čas o ~60 s.
        # Simulace (t_bug3_lwma.py): 10 % hashrate = obtížnost 88 %, emise 113 %
        # plánu; 25 % hashrate = obtížnost 73 %, emise 136 %.
        #
        # Nově metoda "předchozí timestamp": časy se zpracují jako monotónní
        # (nejméně předchozí + 1) a solvetime se po blocích NEOŘEZÁVÁ. Čas
        # "vypůjčený" z budoucnosti se vrací u následujících bloků, které
        # dostanou solvetime 1, takže se manipulace vynuluje. Ořez shora (6T)
        # byl vyzkoušen a zahozen: zahazuje část vypůjčeného času, takže tatáž
        # manipulace obtížnost naopak ZVEDALA (10 % hashrate -> 126 %).
        # Změnu targetu dál omezuje ořez na 4x/0,25x níž a strop FIXED_TARGET.
        # Porovnání variant: t_bug3_variants.py.
        #
        # POZNÁMKA U-5 (audit 2. 10. 2026, nález 3): chybějící ořez solve_time je
        # ZÁMĚRNÁ odchylka od referenční LWMA (zawy), která ho má typicky na 6T.
        # Zůstává vědomě z důvodu popsaného výše a cena je změřená:
        #
        #   N = 144, T = 60 s, všechny targety v okně stejné
        #   poctivý průběh (rovnoměrně po 60 s)  -> 1,0000x základ
        #   veškerý čas natlačený na konec okna  -> 1,9698x základ (obtížnost / 1,97)
        #   maximálně stlačené časy              -> 0,016667x základ (obtížnost x 60)
        #
        # Horní mez je teoretická mez váženého součtu 2N/(N+1) = 1,986, naměřená
        # hodnota je tedy u stropu: útočník, který ovládá pořadí časových razítek
        # v celém okně, srazí obtížnost nejvýš zhruba na polovinu. Víc nejde -
        # časy jsou shora vázané get_time() + 600 a zdola klouzavým mediánem
        # (MTP). Opačný směr je formálně větší (x60), ale ořez 4x ho rozloží
        # nejméně do tří bloků a LWMA se sama vrací.
        #
        # Doplnění ořezu by bylo ZMĚNOU KONSENZU (hard fork) - patří do kódu před
        # spuštěním sítě, ne po něm, stejně jako OPRAVA A-4, #6b / ZMĚNA 1, #14,
        # N-3 a AUDIT-10. Pokud se k němu někdy sáhne, musí se znovu proměřit
        # scénář z OPRAVY N-3, protože ten tuhle variantu právě zamítl.
        predchozi_ts = blocks[0].timestamp
        for i in range(1, N + 1):
            ts = blocks[i].timestamp
            if ts <= predchozi_ts:
                ts = predchozi_ts + 1
            solve_time = ts - predchozi_ts
            predchozi_ts = ts
            t += solve_time * i
            sum_target += blocks[i].target
            
        K = (N * (N + 1)) // 2
        avg_target = sum_target // N
        t = max(1, t)
        
        new_target = (avg_target * t) // (K * BLOCK_TIME_SECONDS)
        
        prev_target = blocks[-1].target
        if new_target > prev_target * 4:
            new_target = prev_target * 4
        elif new_target < prev_target // 4:
            new_target = prev_target // 4
            
        new_target = max(1, min(new_target, FIXED_TARGET))
        
        return new_target

    @staticmethod
    def mining_worker(block_data, start_nonce, step, result_queue, stop_event, update_interval=1.0, worker_id=0):
        index = block_data['index']
        timestamp = block_data['timestamp']
        merkle_root = block_data['merkle_root']
        state_root = block_data['state_root']
        previous_hash = block_data['previous_hash']
        target_hex = block_data['target']
        version = block_data.get('version', BLOCK_VERSION)
        chain_id = block_data.get('chain_id', CHAIN_ID)
        original_target = int(target_hex, 16)
        # OPRAVA #7: worker běží v samostatném procesu a používal holé
        # time.time(), zatímco zbytek uzlu počítá čas jako time.time() + time_offset
        # (get_time()). Při offsetu horším než -60 s se timestamp resetoval hned
        # v první iteraci a blok dostal neopravený lokální čas; nad -600 s uzel
        # odmítl vlastní právě vytěžený blok. Offset se proto předává v block_data
        # (nespoléháme na dědění globálu - to platí jen u fork startu, ne u spawn).
        worker_time_offset = block_data.get('time_offset', 0)
        # OPRAVA U-6: spodní mez času z klouzavého mediánu (MTP + 1). Blok, který
        # ji poruší, odmítnou všechny tři validátory konsenzu včetně našeho
        # vlastního add_block(), takže reset timestampu ji musí respektovat -
        # jinak by si ji mine() spočítala a worker ji vzápětí zahodil.
        min_timestamp = block_data.get('min_timestamp', 0)

        def worker_now():
            return time.time() + worker_time_offset

        target = original_target
        nonce = start_nonce
        hashes_calculated = 0
        last_update_time = worker_now()
        
        while not stop_event.is_set():
            current_time = worker_now()
            if current_time - timestamp > 60:
                # OPRAVA U-6: dřív tu bylo holé int(current_time).
                timestamp = max(min_timestamp, int(current_time))
                nonce = start_nonce
                target = original_target
                if worker_id == 0:
                    formatted_time = time.strftime("%d.%m.%Y %H:%M:%S UTC+00:00", time.gmtime(timestamp))
                    sys.stdout.write(f"\n{Fore.YELLOW}Reset PoW nonce{Style.RESET_ALL}\n")
                    sys.stdout.write(f"{Fore.CYAN}Nový timestamp:{Style.RESET_ALL} {formatted_time}\n")
                    sys.stdout.write(f"{Fore.MAGENTA}Target:{Style.RESET_ALL} {hex(target)[2:]}\n\n")
                    sys.stdout.flush()
            
            b = b''
            b += struct.pack('!I', int(version))
            b += struct.pack('!I', int(chain_id))
            b += struct.pack('!Q', int(index))
            b += struct.pack('!Q', int(timestamp))
            b += struct.pack('!Q', int(nonce))
            
            target_bytes = int(target).to_bytes(32, byteorder='big', signed=False)
            b += target_bytes
            
            # Musí odpovídat Block.compute_hash(), jinak by vytěžený hash
            # neprošel vlastní validací v add_block(). OPRAVA A-4 se proto musí
            # promítnout i sem - tenhle kód je ruční kopie hlavičky a rozejití
            # obou míst by znamenalo, že uzel nedokáže přijmout vlastní blok.
            for s in [previous_hash, merkle_root, state_root]:
                b += encode_optional_field(s)
            
            computed_hash = hashlib.sha3_256(b).hexdigest()
            hashes_calculated += 1
            
            if Blockchain.meets_difficulty(computed_hash, target):
                result_queue.put(('result', worker_id, nonce, timestamp, computed_hash))
                return
            if current_time - last_update_time >= update_interval:
                result_queue.put(('update', worker_id, hashes_calculated, nonce, computed_hash))
                hashes_calculated = 0
                last_update_time = current_time
            nonce += step
            
        if hashes_calculated > 0:
            result_queue.put(('update', worker_id, hashes_calculated, nonce, computed_hash))

    def proof_of_work(self, block, num_cores, min_timestamp=0):
        # OPRAVA U-6: min_timestamp je spodní mez času bloku odvozená z MTP
        # (median_time_past + 1). Výchozí 0 znamená "bez meze" a zachovává
        # původní chování pro případné jiné volající.
        #
        # OPRAVA L-1: obsluha Ctrl+C sahala na proměnné, které v okamžiku
        # přerušení nemusely existovat. stop_event, processes i result_queue
        # vznikají až o ~20 řádků níž, takže KeyboardInterrupt kdekoli nad nimi
        # vedl v handleru na UnboundLocalError - a to NENÍ KeyboardInterrupt,
        # takže ji nezachytil ani `except KeyboardInterrupt` v mine() a propadla
        # až do obecného except v menu. Předinicializace + testy v handleru.
        stop_event = None
        processes = []
        result_queue = None
        original_sigint = None
        sigint_ignorovan = False
        try:
            start_time = get_time()
            computed_hash = ""
            # OPRAVA G-11: total_hashes_calculated se nikdy nečetlo (skutečné
            # počítadlo drží worker procesy) - odstraněno.
            self.mining_in_progress = True
            sys.stdout.write(f"\n{Fore.YELLOW}Začínám těžit blok na zvolený počet CPU jader: {num_cores}{Style.RESET_ALL}\n")
            # OPRAVA G-11: last_block = self.get_last_block() se nikdy
            # nepoužilo - odstraněno i s tím dotazem.
            block_data = {
                'index': block.index,
                'timestamp': block.timestamp,
                'merkle_root': block.merkle_root,
                'state_root': block.state_root,
                'previous_hash': block.previous_hash,
                'target': hex(block.target)[2:],
                'version': block.version,
                'chain_id': block.chain_id,
                # OPRAVA #7: NTP offset předáváme workerům explicitně, aby
                # počítaly stejný čas jako get_time() ve zbytku uzlu.
                'time_offset': time_offset,
                # OPRAVA U-6: spodní mez z MTP. Worker si po 60 s přepisuje
                # timestamp vlastním výpočtem času, takže pravidlo musí znát -
                # jinak by reset vrátil blok pod medián a uzel by si ho sám
                # odmítl. Stejný důvod, proč se mu předává time_offset.
                'min_timestamp': int(min_timestamp),
            }
            result_queue = multiprocessing.Queue()
            stop_event = multiprocessing.Event()
            processes = []
            original_sigint = signal.getsignal(signal.SIGINT)
            signal.signal(signal.SIGINT, signal.SIG_IGN)
            sigint_ignorovan = True
            core_hashes = [0] * num_cores
            core_nonces = [0] * num_cores
            core_last_hashes = [""] * num_cores
            
            # OPRAVA L-1: selhání p.start() (typicky OSError při forku, na
            # telefonu při vyčerpané paměti nebo limitu procesů) dřív nechalo
            # už rozběhnuté workery běžet dál a výjimka odešla ven. Teď se
            # rozdělaná práce uklidí a teprve pak se chyba pustí dál.
            try:
                for i in range(num_cores):
                    p = multiprocessing.Process(target=Blockchain.mining_worker, args=(block_data, i, num_cores, result_queue, stop_event, 1.0, i))
                    processes.append(p)
                    p.start()
            except Exception:
                stop_event.set()
                self._shutdown_workers(processes, result_queue)
                self.mining_in_progress = False
                raise
                
            signal.signal(signal.SIGINT, original_sigint)
            sigint_ignorovan = False
            last_hashrate_time = get_time()
            
            while self.mining_in_progress:
                try:
                    msg = result_queue.get(timeout=1)
                    if msg[0] == 'result':
                        winner_id = msg[1]
                        nonce = msg[2]
                        new_timestamp = msg[3]
                        computed_hash = msg[4]
                        block.nonce = nonce
                        block.timestamp = new_timestamp
                        block.hash = computed_hash
                        stop_event.set()
                        break
                    elif msg[0] == 'update':
                        worker_id = msg[1]
                        core_hashes[worker_id] += msg[2]
                        core_nonces[worker_id] = msg[3]
                        core_last_hashes[worker_id] = msg[4][:10]
                except queue.Empty:
                    pass
                    
                current_time = get_time()
                if current_time - last_hashrate_time >= 5:
                    elapsed_time = current_time - start_time
                    if elapsed_time > 0:
                        total_hashrate = sum(core_hashes) / elapsed_time
                        sys.stdout.write(f"\r{Fore.CYAN}Celkový Hashrate:{Style.RESET_ALL} {total_hashrate/1000:.2f} Kh/s {Fore.CYAN}Čas:{Style.RESET_ALL} {elapsed_time:.1f}s\n")
                        for i in range(num_cores):
                            core_hashrate = core_hashes[i] / elapsed_time if elapsed_time > 0 else 0
                            sys.stdout.write(f"Jádro {i+1}: {core_hashrate/1000:.2f} Kh/s | Nonce: {core_nonces[i]} | Hash: {core_last_hashes[i]}\n")
                            sys.stdout.flush()
                    last_hashrate_time = current_time
                    
            stop_event.set()
            self._shutdown_workers(processes, result_queue)
            self.mining_in_progress = False
            
            if computed_hash:
                elapsed_time = get_time() - start_time
                hashrate = sum(core_hashes) / elapsed_time if elapsed_time > 0 else 0
                winner_hashrate = core_hashes[winner_id] / elapsed_time if elapsed_time > 0 else 0
                sys.stdout.write(f"\r{Fore.GREEN}Blok nalezen! [Jádro {winner_id+1} : {winner_hashrate/1000:.2f} Kh/s]{Style.RESET_ALL} | {Fore.CYAN}Celkový Hashrate:{Style.RESET_ALL} {hashrate/1000:.2f} Kh/s | {Fore.CYAN}Nonce:{Style.RESET_ALL} {block.nonce} | {Fore.CYAN}Hash:{Style.RESET_ALL} {computed_hash[:10]}... | {Fore.CYAN}Čas:{Style.RESET_ALL} {elapsed_time:.2f}s\n")
                sys.stdout.flush()
                return computed_hash
            else:
                sys.stdout.write(f"\r{Fore.YELLOW}Těžba byla zastavena, přijat nový blok od uzlu.{Style.RESET_ALL}\n")
                sys.stdout.flush()
                return None
        except KeyboardInterrupt:
            self.mining_in_progress = False
            # OPRAVA L-1: bez těchto testů tu vznikal UnboundLocalError, viz
            # komentář na začátku metody.
            if stop_event is not None:
                stop_event.set()
            for p in processes:
                try:
                    p.terminate()
                except Exception:
                    pass
            if result_queue is not None:
                self._shutdown_workers(processes, result_queue)
            print(f"\n{Fore.YELLOW}Těžba byla ukončena uživatelem (CTRL+C).{Style.RESET_ALL}")
            return None
        finally:
            # OPRAVA L-1: druhá polovina nálezu. SIGINT se ignoruje jen po dobu
            # startu workerů (aby signál nechytily děti), obnovoval se ale
            # obyčejným řádkem uprostřed try. Když mezitím selhal p.start(),
            # obnovení se přeskočilo a Ctrl+C přestalo fungovat DO KONCE BĚHU
            # UZLU. Obnovení proto patří do finally.
            if sigint_ignorovan and original_sigint is not None:
                try:
                    signal.signal(signal.SIGINT, original_sigint)
                except Exception:
                    # signal.signal() jde volat jen z hlavního vlákna; selhání
                    # tady nesmí přebít výsledek ani probíhající výjimku.
                    pass

    @staticmethod
    def _shutdown_workers(processes, result_queue, timeout=10.0):
        # OPRAVA #13: klasická past multiprocessing.Queue - po stop_event.set()
        # se volal rovnou p.join() bez vyprázdnění fronty. Pokud má worker
        # rozepsaná data ve feeder pipe a rodič z fronty nečte, pipe se zaplní,
        # worker se zablokuje v zápisu a p.join() visí navždy. Rodič proto musí
        # frontu odčerpávat po celou dobu, co na workery čeká, a join() dostane
        # timeout s tvrdým terminate() jako pojistkou.
        deadline = time.time() + timeout
        while time.time() < deadline and any(p.is_alive() for p in processes):
            try:
                result_queue.get(timeout=0.1)
            except queue.Empty:
                pass
            except (OSError, ValueError, EOFError):
                break

        while True:
            try:
                result_queue.get_nowait()
            except queue.Empty:
                break
            except (OSError, ValueError, EOFError):
                break

        for p in processes:
            p.join(timeout=2)
            if p.is_alive():
                p.terminate()
                p.join(timeout=2)
            if p.is_alive():
                try:
                    p.kill()
                    p.join(timeout=2)
                except Exception:
                    pass

        try:
            result_queue.close()
            result_queue.cancel_join_thread()
        except Exception:
            pass

    @staticmethod
    def meets_difficulty(hash_hex, target):
        hash_int = int(hash_hex, 16)
        return hash_int < target

    def add_block(self, block, proof):
        # OPRAVA D-04: dřív jediný pokus s timeout=5 a při vypršení se PLATNÝ
        # BLOK ZAHODIL. U bloku ze sítě se uzel ještě zotavil (handler pošle
        # request_chain_info), ale u vlastního vytěženého bloku byla ztráta
        # konečná - mine() dostalo False a celé kolo PoW přišlo vniveč. Na
        # telefonu, kde je jedno kolo drahé, je to citelné, a útočník to spouštěl
        # zdarma zahlcením mempoolu (D-03 + kvadratický add_transaction).
        #
        # Blok je vždycky důležitější než transakce, takže se o zámek pokoušíme
        # opakovaně a s delším celkovým rozpočtem. Vlastní příčinu (držení zámku
        # po stovky ms) odstraňují indexy z D-04; tohle je pojistka pro případ,
        # že zámek drží něco jiného, například probíhající reorg.
        acquired = False
        for pokus in range(ADD_BLOCK_LOCK_RETRIES):
            if self.lock.acquire(timeout=ADD_BLOCK_LOCK_TIMEOUT):
                acquired = True
                break
            if 'p2p_node' in globals() and p2p_node is not None:
                p2p_node.add_log(f"{Fore.YELLOW}Zámek pro blok #{block.index} zatím obsazen (pokus {pokus + 1}/{ADD_BLOCK_LOCK_RETRIES}), zkouším znovu.{Style.RESET_ALL}")
        if not acquired:
            print(f"{Fore.RED}System is busy (lock timeout). Try again later.{Style.RESET_ALL}")
            return False
        try:
            if block.chain_id != CHAIN_ID:
                p2p_log(f"{Fore.RED}Chyba ověření bloku: Zjištěno cizí chain_id.{Style.RESET_ALL}")
                return False
            if block.version != BLOCK_VERSION:
                p2p_log(f"{Fore.RED}Chyba ověření bloku: Neplatná verze bloku.{Style.RESET_ALL}")
                return False
            block_size = block.get_size()
            if block_size > MAX_BLOCK_SIZE_BYTES:
                p2p_log(f"{Fore.RED}Chyba ověření bloku: Velikost bloku ({block_size} bajtů) překračuje maximální povolenou velikost {MAX_BLOCK_SIZE_BYTES} bajtů.{Style.RESET_ALL}")
                return False
                
            previous_block = self.get_last_block()
            previous_hash = previous_block.hash
            
            is_mini_reorg = False
            block_to_remove = None

            if previous_hash != block.previous_hash:
                if block.index == previous_block.index:
                    prev_prev = self.get_block(block.index - 1)
                    if prev_prev and prev_prev.hash == block.previous_hash:
                        current_work = (1 << 256) // previous_block.target if previous_block.target > 0 else 0
                        new_work = (1 << 256) // block.target if block.target > 0 else 0
                        if new_work > current_work or (new_work == current_work and block.hash < previous_block.hash):
                            is_mini_reorg = True
                            block_to_remove = previous_block
                            previous_block = prev_prev
                            previous_hash = previous_block.hash
                        else:
                            # OPRAVA #16: tyhle větve se dřív vracely tiše, bez
                            # jediného řádku v logu. Při ladění reorgů to znamenalo
                            # "blok zmizel a nikdo neví proč".
                            p2p_log(f"{Fore.YELLOW}Blok #{block.index} zamítnut: konkurent na stejné výšce nemá větší práci ani lepší hash (mini-reorg neproběhne).{Style.RESET_ALL}")
                            return False
                    else:
                        p2p_log(f"{Fore.RED}Blok #{block.index} zamítnut: konkurenční blok na stejné výšce nenavazuje na náš blok #{block.index - 1}.{Style.RESET_ALL}")
                        return False
                else:
                    p2p_log(f"{Fore.RED}Blok #{block.index} zamítnut: previous_hash neodpovídá našemu vrcholu #{previous_block.index} a nejde ani o konkurenta na stejné výšce.{Style.RESET_ALL}")
                    return False
                    
            if block.index != previous_block.index + 1:
                p2p_log(f"{Fore.RED}Blok #{block.index} zamítnut: nenavazuje na vrchol řetězce (očekáván index #{previous_block.index + 1}).{Style.RESET_ALL}")
                return False

            # OPRAVA F-10: checkpointy se vynucovaly jen v is_valid_chain()
            # (4 výskyty), zatímco add_block() a validate_fork() je neznaly
            # vůbec. Blok v rozporu s checkpointem tedy prošel do DB, a teprve
            # is_valid_chain() při dalším startu řetězec odmítla - a protože
            # load_data() na to reaguje sys.exit(1), uzel by už nenaběhl.
            # Všechny tři validátory teď vynucují totéž pravidlo.
            if block.index in CHECKPOINTS and block.hash != CHECKPOINTS[block.index]:
                p2p_log(f"{Fore.RED}Blok #{block.index} zamítnut: neodpovídá checkpointu (očekáváno {CHECKPOINTS[block.index]}).{Style.RESET_ALL}")
                return False

            # Základní stav, proti kterému se blok validuje = stav po bloku
            # block.index - 1. Při mini-reorgu (níže) se odpojuje současný vrchol,
            # takže self.balance_map / nonce_map / immature_rewards ještě obsahují
            # blok, který se má nahradit; get_state_at() ho přes undo log odroluje.
            # OPRAVA N-11: v běžném případě (blok navazuje na vrchol) je
            # základním stavem self - nekopíruje se. get_state_at() dřív vracel
            # dict(balance_map), dict(nonce_map) a klon SMT a make_state_shadow()
            # to níž zkopíroval ZNOVU: 37 ms na blok při 100 000 účtech
            # (t_perf11_state_copy.py). Kopie stavu zůstává jen pro mini-reorg,
            # kde se odroluje současný vrchol.
            rychla_cesta = (not is_mini_reorg and block.index - 1 == self.max_block_index)
            if rychla_cesta:
                base_state = {
                    'balance_map': self.balance_map,
                    'nonce_map': self.nonce_map,
                    'immature_rewards': self.immature_rewards,
                    'total_supply': self.total_supply,
                }
            else:
                base_state = self.get_state_at(block.index - 1)
            if base_state is None:
                p2p_log(f"{Fore.RED}Chyba ověření bloku: Nelze rekonstruovat stav pro blok #{block.index}.{Style.RESET_ALL}")
                return False
            base_balance_map = base_state['balance_map']
            base_nonce_map = base_state['nonce_map']
            base_immature_rewards = base_state['immature_rewards']
            base_total_supply = base_state['total_supply']
                
            # OPRAVA F-05: chybějící blok v okně MTP/LWMA znamená odmítnutí,
            # ne tichý posun mediánu nebo nejsnazší target.
            try:
                median_time_past = self.get_median_time_past(block.index)
            except MissingChainDataError as e:
                p2p_log(f"{Fore.RED}Blok #{block.index} zamítnut: {e} Nelze ověřit časové pravidlo.{Style.RESET_ALL}")
                return False
            if not block.is_valid_timestamp(median_time_past):
                p2p_log(f"{Fore.RED}Chyba ověření bloku:{Style.RESET_ALL} Timestamp bloku je neplatný.")
                return False
                
            # Target se MUSÍ počítat pro výšku validovaného bloku. get_target() si
            # uvnitř bere get_last_block(), takže vrací pravidlo pro tip.index + 1.
            # V přímém pokračování to vyjde, ale při mini-reorgu je
            # block.index == tip.index a platný konkurenční blok byl zamítán s
            # "Nesprávný target bloku" - mini-reorg tak nad výškou N+1 nikdy
            # neproběhl a add_block aplikoval jiné pravidlo než validate_fork
            # a is_valid_chain. calculate_expected_target() čte bloky
            # [index-N-1, index-1], tedy vždy jen společné předky.
            try:
                expected_target = self.calculate_expected_target(block.index)
            except MissingChainDataError as e:
                p2p_log(f"{Fore.RED}Blok #{block.index} zamítnut: {e} Nelze ověřit target.{Style.RESET_ALL}")
                return False
            if block.target != expected_target:
                p2p_log(f"{Fore.RED}Chyba ověření bloku: Nesprávný target bloku.{Style.RESET_ALL}")
                return False
                
            # ZMĚNA 5 (názvosloví): v hláškách se kořen transakčního stromu
            # označuje jako "Transaction root", ne "Merkle root". Uzel počítá
            # kořeny dva - tenhle nad transakcemi a SMT nad účty (state_root) -
            # takže obecné označení neříká, o který z nich jde; při čtení logu
            # po neúspěšné validaci je to zrovna ta informace, kterou člověk
            # potřebuje nejdřív. Shodné s výpisem bloku ve volbách 10 a 11.
            #
            # Mění se VÝHRADNĚ text hlášky. Pole bloku `merkle_root`, funkce
            # compute_merkle_root(), konstanty MERKLE_* ani sloupec merkle_root
            # v blockchain.db se NEMĚNÍ - jsou součástí formátu na drátě i na
            # disku, takže přejmenovat je by byl hard fork a nekompatibilita
            # s uloženými daty.
            #
            # Táž hláška je ve všech třech místech, kde se kořen kontroluje
            # a zároveň se o tom loguje: tady, v _is_valid_chain_inner()
            # a v _merkle_branka_bloku(). _validate_fork_inner() kořen
            # kontroluje taky, ale nelogovala nikdy (vrací jen False) -
            # viz poznámka tamtéž.
            if block.merkle_root != compute_merkle_root(block.transactions):
                p2p_log(f"{Fore.RED}Chyba ověření bloku: Nesprávný Transaction root.{Style.RESET_ALL}")
                return False
            if not self.meets_difficulty(proof, block.target):
                # OPRAVA #16: doplněn chybějící log.
                p2p_log(f"{Fore.RED}Chyba ověření bloku: Hash bloku #{block.index} nesplňuje jeho target (neplatný PoW).{Style.RESET_ALL}")
                return False
            if proof != block.compute_hash():
                p2p_log(f"{Fore.RED}Chyba ověření bloku: Hash bloku neodpovídá jeho obsahu (možný útok bez reálného PoW).{Style.RESET_ALL}")
                return False
            if block.index > 0 and any(tx.data is not None for tx in block.transactions):
                p2p_log(f"{Fore.RED}Chyba ověření bloku: Nepovolená zpráva v bloku mimo genesis.{Style.RESET_ALL}")
                return False
                
            # OPRAVA D-05: jeden dotaz na celý blok místo jednoho na každou
            # transakci (dřív 302 SQLite spojení na blok s 300 transakcemi).
            #
            # OPRAVA B-2: tohle je PRVNÍ otevření databáze v add_block(), a bylo
            # bez ošetření - chyba DB odsud propadla ven z celé metody a kontrakt
            # "add_block vrací True/False" přestal platit. Volající (handler
            # new_block, mine(), resolve_orphans) s výjimkou nepočítají. Stav
            # sice ještě změněný není, ale odpovědět je potřeba korektně.
            try:
                duplicate_ids = self.tx_ids_in_chain(
                    [tx.tx_id for tx in block.transactions], exclude_from_index=block.index
                )
            except Exception as e:
                p2p_log(f"{Fore.RED}Chyba ověření bloku #{block.index}: databázi se nepodařilo dotázat na duplicitní TX ID ({type(e).__name__}: {e}).{Style.RESET_ALL}")
                return False

            for tx in block.transactions:
                if not isinstance(tx.amount, int) or not isinstance(tx.fee, int) or not isinstance(tx.nonce, int):
                    p2p_log(f"{Fore.RED}Chyba ověření bloku: Hodnoty amount, fee a nonce musí být celá čísla.{Style.RESET_ALL}")
                    return False
                if tx.timestamp > block.timestamp + 7200:
                    p2p_log(f"{Fore.RED}Chyba ověření bloku: Transakce {tx.tx_id} má čas příliš v budoucnosti oproti bloku.{Style.RESET_ALL}")
                    return False
                # OPRAVA D-12: blok měl spodní mez času (timestamp >= GENESIS_TIMESTAMP),
                # transakce ne - transakce s timestamp = 1 prošla všemi třemi
                # validátory. Horní mez existovala, spodní chyběla. U genesis
                # transakce se stejně vyžaduje přesná rovnost, takže kolize nehrozí.
                if tx.timestamp < GENESIS_TIMESTAMP:
                    p2p_log(f"{Fore.RED}Chyba ověření bloku: Transakce {tx.tx_id} má čas před genesis blokem.{Style.RESET_ALL}")
                    return False
                if tx.chain_id != CHAIN_ID:
                    p2p_log(f"{Fore.RED}Chyba ověření bloku:{Style.RESET_ALL} Transakce patří k jinému chain_id.")
                    return False
                if not is_valid_address(tx.to_address):
                    p2p_log(f"{Fore.RED}Chyba ověření bloku:{Style.RESET_ALL} Neplatný formát adresy příjemce ({tx.to_address}).")
                    return False
                if tx.tx_id in duplicate_ids:
                    p2p_log(f"{Fore.RED}Chyba ověření bloku:{Style.RESET_ALL} Duplicitní TX ID {tx.tx_id} v bloku.")
                    return False
                    
            nonce_map = {}
            tx_id_set = set()
            for tx in block.transactions:
                if tx.tx_id in tx_id_set:
                    p2p_log(f"{Fore.RED}Chyba ověření bloku:{Style.RESET_ALL} Duplicitní TX ID {tx.tx_id} v bloku.")
                    return False
                tx_id_set.add(tx.tx_id)
                if tx.from_address != "COINBASE":
                    if tx.from_address in nonce_map:
                        if tx.nonce in nonce_map[tx.from_address]:
                            p2p_log(f"{Fore.RED}Chyba ověření bloku:{Style.RESET_ALL} Duplicitní nonce {tx.nonce} pro adresu {tx.from_address} v bloku.")
                            return False
                        nonce_map[tx.from_address].add(tx.nonce)
                    else:
                        nonce_map[tx.from_address] = {tx.nonce}
                        
            for sender, nonces_in_block in nonce_map.items():
                expected_nonce = base_nonce_map.get(sender, -1) + 1
                for tx_nonce in sorted(nonces_in_block):
                    if tx_nonce != expected_nonce:
                        p2p_log(f"{Fore.RED}Chyba ověření bloku: Neplatná posloupnost nonce {tx_nonce} pro adresu {sender} (očekávána přesně {expected_nonce}).{Style.RESET_ALL}")
                        return False
                    expected_nonce += 1
                    
            for tx in block.transactions:
                if not tx.verify_sender_identity() and tx.from_address != "COINBASE":
                    p2p_log(f"{Fore.RED}Chyba ověření bloku:{Style.RESET_ALL} Veřejný klíč neodpovídá adrese odesílatele.")
                    return False
                if not tx.verify_signature() and tx.from_address != "COINBASE":
                    p2p_log(f"{Fore.RED}Chyba ověření bloku:{Style.RESET_ALL} Neplatný podpis transakce.")
                    return False
                if tx.from_address != "COINBASE":
                    if tx.amount <= 0:
                        p2p_log(f"{Fore.RED}Chyba ověření bloku: Částka transakce musí být větší než 0.{Style.RESET_ALL}")
                        return False
                    if tx.amount < MIN_TX_AMOUNT:
                        p2p_log(f"{Fore.RED}Chyba ověření bloku: Částka transakce je příliš malá.{Style.RESET_ALL}")
                        return False
                    # OPRAVA #6b: konsenzus vynucuje jen dolní mez poplatku.
                    # ZMĚNA 1: horní mez (TX_FEE_MAX) už neexistuje vůbec, ani
                    # jako politika mempoolu v add_transaction() - viz komentář
                    # u TX_FEE_MIN.
                    if tx.fee < TX_FEE_MIN:
                        p2p_log(f"{Fore.RED}Chyba ověření bloku: Poplatek transakce je nižší než minimum.{Style.RESET_ALL}")
                        return False
                    # OPRAVA #6d: zákaz transakce sám sobě byl jen v add_transaction(),
                    # tedy v mempoolové politice, a v konsenzu chyběl. Pravidlo tak
                    # drželo náhodou: poctivý uzel takovou transakci nevytěží, protože
                    # mine() bere z mempoolu - ale těžař s upravenou binárkou ji vloží
                    # do bloku přímo a každý uzel v síti ten blok přijal. Musí být ve
                    # všech třech validátorech, jinak vznikne consensus split (uzel by
                    # blok odmítl při přímém příjmu, ale přijal ho jako součást forku).
                    # Coinbase zůstává vyňatá přes nadřazené `if tx.from_address != "COINBASE"`.
                    if tx.from_address == tx.to_address:
                        p2p_log(f"{Fore.RED}Chyba ověření bloku: Transakce na vlastní adresu není povolena.{Style.RESET_ALL}")
                        return False
                        
            coinbase_txs = [tx for tx in block.transactions if tx.from_address == "COINBASE"]
            if len(coinbase_txs) != 1:
                p2p_log(f"{Fore.RED}Chyba ověření bloku: Nesprávný počet coinbase transakcí (očekávána 1).{Style.RESET_ALL}")
                return False
            if block.transactions[0].from_address != "COINBASE":
                p2p_log(f"{Fore.RED}Chyba ověření bloku: Coinbase transakce musí být první v bloku.{Style.RESET_ALL}")
                return False
                
            coinbase_tx = coinbase_txs[0]

            # OPRAVA D-11: poplatek u coinbase se nevalidoval vůbec - blok
            # s coinbase.fee = 12345 přijaly všechny tři validátory. Peníze to
            # netvoří (total_fees coinbase vylučuje a update_state_with_block
            # u coinbase čte jen amount), ale je to NEVALIDOVANÉ POLE
            # v konsenzuální struktuře, které vstupuje do tx_id, a tedy i do
            # merkle rootu a hashe bloku. Fakticky je to volný grindovací prostor
            # navíc a do budoucna past: kdokoli později napíše kód, který
            # u coinbase poplatek čte, dostane nekontrolovanou hodnotu ze sítě.
            # Musí být ve všech třech validátorech, jinak vznikne consensus split.
            if coinbase_tx.fee != 0:
                p2p_log(f"{Fore.RED}Chyba ověření bloku: Coinbase transakce musí mít nulový poplatek (má {coinbase_tx.fee}).{Style.RESET_ALL}")
                return False

            # OPRAVA F-09: táž past jako u poplatku, jen o dvě pole dál.
            # Pravidlo "žádné zprávy v blocích mimo genesis" kontroluje pouze
            # tx.data, jenže coinbase má další dvě volně textová pole, která
            # nikdo nevalidoval: verify_signature() i verify_sender_identity()
            # pro COINBASE vracejí rovnou True.
            #   public_key -> vstupuje do get_signing_data(), tedy do tx_id
            #   signature  -> vstupuje do compute_merkle_leaf_hash()
            # Ověřeno auditem: blok s textovou zprávou v obou polích přijaly
            # všechny tři validátory a zpráva se uložila do blockchain.db.
            # Volného místa v bloku bez jediné transakce bylo 1 023 KB.
            # mine() i create_genesis_block() staví coinbase vždy s None,
            # takže tohle pravidlo nic legitimního neomezuje.
            if coinbase_tx.public_key is not None or coinbase_tx.signature is not None:
                p2p_log(f"{Fore.RED}Chyba ověření bloku: Coinbase transakce musí mít prázdné public_key i signature.{Style.RESET_ALL}")
                return False

            # Nonce coinbase transakce musí být rovna výšce bloku. Je to jediné, co
            # dělá tx_id coinbase transakcí unikátní napříč celým řetězcem (obdoba
            # BIP30) - bez tohoto pravidla na tom stála jen konvence těžaře v mine()
            # a dva bloky téhož těžaře se stejnou odměnou i časem by kolidovaly.
            if coinbase_tx.nonce != block.index:
                p2p_log(f"{Fore.RED}Chyba ověření bloku: Nonce coinbase transakce ({coinbase_tx.nonce}) musí být rovna výšce bloku ({block.index}).{Style.RESET_ALL}")
                return False

            halvings = block.index // HALVING_INTERVAL_BLOCKS
            expected_reward = subsidy_po_halvingu(halvings) if block.index > 0 else GENESIS_AMOUNT
            expected_reward = max(0, min(expected_reward, MAX_SUPPLY - base_total_supply))
                
            total_fees = sum(tx.fee for tx in block.transactions if tx.from_address != "COINBASE")
            if coinbase_tx.amount != expected_reward + total_fees:
                p2p_log(f"{Fore.RED}Chyba ověření bloku: Nesprávná coinbase odměna.{Style.RESET_ALL}")
                return False
                
            target_index = block.index - COINBASE_MATURITY
            simulated_mature_balance = defaultdict(int)
            if target_index in base_immature_rewards:
                simulated_mature_balance[base_immature_rewards[target_index]['address']] += base_immature_rewards[target_index]['amount']

            temp_balance_changes = defaultdict(int)
            for tx in block.transactions:
                if tx.from_address != "COINBASE":
                    current_balance = base_balance_map.get(tx.from_address, 0) + simulated_mature_balance[tx.from_address] + temp_balance_changes[tx.from_address]
                    if current_balance < tx.amount + tx.fee:
                        p2p_log(f"{Fore.RED}Chyba ověření bloku: Nedostatečný zůstatek pro transakci {tx.tx_id} od {tx.from_address}.{Style.RESET_ALL}")
                        return False
                    temp_balance_changes[tx.from_address] -= (tx.amount + tx.fee)
                    temp_balance_changes[tx.to_address] += tx.amount
                else:
                    pass

            # Ověření state rootu: blok se spekulativně aplikuje na kopii
            # základního stavu a výsledný root se porovná s hlavičkou. Teprve po
            # shodě se blok zapisuje do DB a promítá do self.
            try:
                if rychla_cesta:
                    expected_state_root = self.state_root_po_bloku(block)
                else:
                    shadow_state = make_state_shadow(base_state)
                    self.update_state_with_block(block, state_target=shadow_state)
                    expected_state_root = compute_state_root_from(shadow_state)
            # OPRAVA G-02: struct.error doplněn jako pojistka. Rozsahové kontroly v encode_account() by ji už neměly připustit, ale kontrakt "ven jde vždy ValueError" musí platit bezvýhradně.
            except (ValueError, struct.error) as e:
                p2p_log(f"{Fore.RED}Chyba ověření bloku: Neplatný stav po aplikaci bloku #{block.index} ({e}).{Style.RESET_ALL}")
                return False
            if block.state_root != expected_state_root:
                p2p_log(f"{Fore.RED}Chyba ověření bloku: Nesprávný state root bloku #{block.index} (očekáván {expected_state_root}, přijat {block.state_root}).{Style.RESET_ALL}")
                return False

            # OPRAVA A-1: jeden logický přechod stavu byl rozdělený do DVOU
            # samostatných SQLite transakcí a paměť se mutovala JEŠTĚ PŘED nimi.
            # Selhal-li první commit (DELETE při mini-reorgu), paměť spadla na
            # výšku N-1, zatímco v DB zůstal blok N - get_block() sahá při
            # neúspěchu do DB, takže calculate_expected_target() i
            # get_median_time_past() dál četly blok, o kterém paměť tvrdila, že
            # neexistuje. Selhal-li druhý commit (INSERT), uzel tiše zahodil
            # vlastní blok: spadl o výšku níž, přišel o emisi, a protože se
            # recycle_orphan_transactions() na chybové cestě nikdy nezavolá,
            # uživatelské transakce z odpojeného bloku zmizely beze stopy.
            # Volající přitom dostal False, tedy "blok odmítnut, nic se nestalo".
            #
            # Cílová platforma je Termux na Androidu, kde "disk I/O error" a
            # "database or disk is full" nejsou teorie. Nově tedy: JEDNO spojení,
            # JEDNA transakce (DELETE starého + INSERT nového), a mutace paměti
            # až PO úspěšném commitu. Do try spadá i json.dumps() celého bloku,
            # takže ani výjimka při serializaci paměť nerozbije. Je to tatáž
            # zásada, kterou si kód formuluje u OPRAVY D-02 - jen tady nejde
            # o stavový příznak, nýbrž o celý stav řetězce.
            if is_mini_reorg:
                p2p_log(f"{Fore.YELLOW}Detekován lepší konkurenční blok na stejné výšce. Provádím bleskový mini-reorg (Undo).{Style.RESET_ALL}")

            block.hash = proof

            conn = None
            try:
                transactions_json = json.dumps([tx.to_dict() for tx in block.transactions])
                target_hex = hex(block.target)[2:]
                conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
                conn.execute("PRAGMA journal_mode=WAL;")
                c = conn.cursor()

                if is_mini_reorg:
                    c.execute("DELETE FROM blocks WHERE block_index = ?", (block_to_remove.index,))
                    c.execute("DELETE FROM transactions WHERE block_index = ?", (block_to_remove.index,))

                c.execute('''
                    INSERT OR REPLACE INTO blocks (block_index, timestamp, transactions, previous_hash, target_hex, nonce, block_hash, merkle_root, version, chain_id, state_root)
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                ''', (block.index, block.timestamp, transactions_json, block.previous_hash, target_hex, block.nonce, block.hash, block.merkle_root, block.version, block.chain_id, block.state_root))

                for tx in block.transactions:
                    c.execute('INSERT OR REPLACE INTO transactions (tx_id, block_index) VALUES (?, ?)', (tx.tx_id, block.index))

                conn.commit()
            except Exception as e:
                if conn is not None:
                    try:
                        conn.rollback()
                    except Exception:
                        pass
                p2p_log(f"{Fore.RED}Kritická chyba DB: Selhal zápis bloku #{block.index} ({e}). Stav uzlu zůstal nezměněn, blok nebyl přijat.{Style.RESET_ALL}")
                return False
            finally:
                if conn is not None:
                    try:
                        conn.close()
                    except Exception:
                        pass

            # Databáze je v cílovém stavu - teprve teď se mutuje paměť.
            #
            # OPRAVA M-2: tenhle blok neměl ŽÁDNÝ try. rollback_state() volá
            # rebuild_state(), a odtud může jít ven MissingChainDataError
            # (poškozený řádek v blocks) nebo sqlite3.OperationalError. Výjimka
            # odsud proletěla ven z add_block(), čímž se porušil kontrakt
            # "vrací True/False", a paměť zůstala v půli přechodu: chain.pop()
            # už proběhl, stav odrolovaný jen zčásti, nový blok nepřipojený -
            # přestože V DATABÁZI UŽ JE. Zotavením je dorovnat paměť k DB.
            try:
                if is_mini_reorg:
                    self.chain.pop()
                    self.rollback_state(block_to_remove.index - 1)

                self.chain.append(block)
                self.max_block_index = block.index
                if len(self.chain) > LAST_BLOCKS_TO_KEEP:
                    self.chain = self.chain[-LAST_BLOCKS_TO_KEEP:]
                self.update_state_with_block(block)
            except Exception as e:
                p2p_log(
                    f"{Fore.RED}Kritická chyba: blok #{block.index} je zapsaný v DB, "
                    f"ale mutace paměti selhala ({type(e).__name__}: {e}). "
                    f"Dorovnávám paměť podle databáze...{Style.RESET_ALL}")
                if not self._resync_memory_from_db():
                    p2p_log(
                        f"{Fore.RED}Dorovnání paměti podle databáze SELHALO. Stav uzlu "
                        f"není důvěryhodný - restartujte uzel, aby se řetězec načetl "
                        f"znovu od začátku.{Style.RESET_ALL}")
                    return False
                p2p_log(
                    f"{Fore.GREEN}Paměť dorovnána podle databáze (vrchol #{self.max_block_index}). "
                    f"Blok #{block.index} je součástí řetězce.{Style.RESET_ALL}")
            
            confirmed_tx_ids = {tx.tx_id for tx in block.transactions if tx.from_address != "COINBASE"}
            self.unconfirmed_transactions = [
                tx for tx in self.unconfirmed_transactions
                if tx.tx_id not in confirmed_tx_ids
            ]

            # ZMĚNA 4: výše se odstraňují jen transakce se STEJNÝM tx_id jako
            # v bloku. Transakce téže adresy se stejnou nonce, ale jiným tx_id
            # (konflikt) se odstraní tady, hned po přijetí bloku - dřív zůstala
            # v mempoolu až do expirace. Viz _prune_mempool_sequences().
            # Změnit se mohla jen nonce a zůstatek odesílatelů z bloku (příjemci
            # a zralá coinbase odměna zůstatek jen zvyšují), takže u běžného bloku
            # stačí zkontrolovat je.
            odesilatele_bloku = {tx.from_address for tx in block.transactions if tx.from_address != "COINBASE"}

            # Transakce odpojeného bloku, které nový vrchol nepřebírá, musí zpět do
            # mempoolu - jinak by mini-reorgem nenávratně zmizely. Volá se až tady,
            # protože recycle_orphan_transactions() se ptá is_tx_id_in_chain() a
            # add_transaction() validuje proti stavu; obojí už je aktuální.
            if is_mini_reorg and block_to_remove is not None:
                # ZMĚNA 4: před recyklací jen zastaralé transakce - jinak by
                # add_transaction() odečítala jejich částky od zůstatku a mohla
                # platnou recyklovanou transakci odmítnout. Díry a zůstatek až po
                # recyklaci, protože ta může díru v posloupnosti zaplnit.
                odstranene_po_bloku = self._prune_mempool_sequences(odesilatele_bloku, stale_only=True)
                self.recycle_orphan_transactions([block_to_remove])
                # Mini-reorg mění zůstatky a nonce adres z OBOU bloků (i příjemcům
                # z odpojeného bloku peníze ubydou) a je vzácný, takže se
                # kontroluje celý mempool.
                odstranene_po_bloku += self._prune_mempool_sequences()
            else:
                odstranene_po_bloku = self._prune_mempool_sequences(odesilatele_bloku)

            if odstranene_po_bloku and 'p2p_node' in globals() and p2p_node is not None:
                for tx, duvod in odstranene_po_bloku:
                    p2p_node.add_log(f"{Fore.YELLOW}Transakce {tx.tx_id} odstraněna z mempoolu po bloku #{block.index} ({duvod}).{Style.RESET_ALL}")
            
            self.resolve_orphans(block.hash)
            return True
        finally:
            self.lock.release()

    def _drop_orphan(self, orphan_hash):
        # Vyjme orphan z poolu i z indexu rodičů a vrátí jeho velikost v bajtech.
        # Odstranění bylo dřív rozepsané inline jen na jednom místě; teď se dělá
        # ze tří (strop v bajtech, expirace, ruční úklid), takže musí být na jednom.
        block = self.orphan_pool.pop(orphan_hash, None)
        if block is None:
            return 0
        parent = block.previous_hash
        if parent in self.orphan_parents:
            if orphan_hash in self.orphan_parents[parent]:
                self.orphan_parents[parent].remove(orphan_hash)
            if not self.orphan_parents[parent]:
                del self.orphan_parents[parent]
        size = self.orphan_sizes.pop(orphan_hash, 0)
        self.orphan_added_at.pop(orphan_hash, None)
        self.orphan_pool_bytes -= size
        if self.orphan_pool_bytes < 0:
            self.orphan_pool_bytes = 0
        return size

    def expire_orphans(self):
        # OPRAVA D-01: orphan pool neměl expiraci vůbec - blok v něm ležel, dokud
        # ho nevytlačilo 100 dalších. Orphan má smysl jen do chvíle, než dorazí
        # jeho rodič; po ORPHAN_EXPIRATION už je to jen obsazená paměť.
        now = get_time()
        for orphan_hash, added in list(self.orphan_added_at.items()):
            if now - added > ORPHAN_EXPIRATION:
                self._drop_orphan(orphan_hash)

    def add_orphan_block(self, block):
        # OPRAVA D-01: pojistka na druhé straně branky z handleru new_block.
        # Orphan pool je PAMĚŤ, ne cache - patří do něj jen to, co má zaplacené
        # PoW. Handler kontroluje totéž, ale add_orphan_block je veřejná metoda
        # a spoléhat se na disciplínu všech budoucích volajících je přesně ta
        # chyba, kvůli které D-01 vzniklo (add_block velikost kontroloval,
        # tahle cesta ne).
        #
        # OPRAVA AUDIT-2026-13 (audit 25. 10. 2026, nález 3): mutace poolu se
        # serializují pod self.lock. Dřív běžela tahle metoda BEZ zámku,
        # zatímco resolve_orphans()/_drop_orphan() mutují tytéž struktury POD
        # zámkem z add_block() - orphan pool byl jediná struktura uzlu, kterou
        # dvě vlákna měnila neserializovaně. Naměřeno (6 vláken, 10 s):
        # účetnictví orphan_pool_bytes se proti součtu orphan_sizes rozcházelo
        # přechodně až o 2 373 B a klíče orphan_pool/orphan_added_at se lišily;
        # po dobehnutí vláken se stav srovnal, takže trvalou korupci se
        # prokázat nepodařilo, ale invariant platil jen mezi operacemi.
        #
        # Rozhodující je ale druhá věc: bez tohohle zámku NEJDE přidat
        # periodické volání expire_orphans() (druhá polovina nálezu 3).
        # Vytěsňovací smyčka níž iteruje orphan_pool přes min() a expirace
        # z jiného vlákna mu slovník mění pod rukama. Ověřeno: vede to na
        # `RuntimeError: dictionary changed size during iteration` a na
        # `KeyError` v `self.orphan_pool[obet]`, obojí uniká z add_orphan_block
        # ven do handleru.
        #
        # Drahé ověřování (PoW, compute_hash, merkle root, get_size) zůstává
        # PŘED zámkem - jsou to čisté funkce bloku, nečtou žádný společný stav,
        # a sha3 nad blokem o 1 MiB se pod konsenzuálním zámkem držet nesmí.
        if not (0 < block.target <= FIXED_TARGET):
            return
        if not Blockchain.meets_difficulty(block.hash, block.target):
            return
        if block.hash != block.compute_hash():
            return
        # OPRAVA AUDIT-2026-12 (audit 25. 10. 2026, nález 2): merkle root se
        # váže na skutečné transakce. Bez téhle kontroly prošly všechny branky
        # výš i blok, jehož `transactions` s hlavičkou vůbec nesouvisí: hash je
        # polem HLAVIČKY, takže jedna vytěžená hlavička unesla libovolný obsah.
        #
        # Ověřeno se skutečným PoW (nonce 657 711 na tehdejším 20bitovém
        # FIXED_TARGET; po ZMĚNĚ 6 by vyšel jiný nonce): hlavičce se
        # beze změny podstrčilo 2 600 vymyšlených transakcí, hash zůstal bit za
        # bitem shodný a add_orphan_block blok PŘIJAL - zatímco add_block ho
        # při příchodu rodiče zaručeně odmítne. Pool tedy držel blok, o kterém
        # se už v okamžiku přijetí vědělo, že je neplatný, a resolve_orphans()
        # ho pak celý naparsoval (včetně sha3 každého tx_id) pro nic.
        #
        # Bajtové zesílení to nebylo - rozpočet poolu se měří get_size(), tedy
        # kanonickou velikostí zastropovanou na MAX_BLOCK_SIZE_BYTES stejně
        # jako u poctivého bloku - ale byla to poslední cesta, kudy se do
        # paměti uzlu dostal prokazatelně neplatný blok. Cesta sync bufferu
        # tutéž vazbu dostala v OPRAVĚ Y-2 (_merkle_branka_bloku) a add_block
        # ji má taky; tady chyběla.
        if block.merkle_root != compute_merkle_root(block.transactions):
            return
        size = block.get_size()
        if size > MAX_BLOCK_SIZE_BYTES:
            return

        # Od tohohle místa se pracuje se společnými strukturami, takže se bere
        # zámek (OPRAVA AUDIT-2026-13 výš). Orphan je best-effort: když zámek
        # drží třeba probíhající reorg, blok se zahodí místo čekání - handler
        # se o rodiče stejně hned ptá přes request_chain_info a periodický sync
        # ho dotáhne do 10 s. Tím se taky zavírá cesta, kterou by útočník
        # hromadil handlerová vlákna zablokovaná na zámku.
        if not self.lock.acquire(timeout=ADD_BLOCK_LOCK_TIMEOUT):
            p2p_log(f"{Fore.YELLOW}Zámek obsazen, orphan blok #{block.index} zahazuji.{Style.RESET_ALL}")
            return
        try:
            # Duplicitní kontrola je nově POD zámkem - mimo něj by mezi
            # kontrolou a vložením stejně mohl tentýž blok projít dvakrát.
            if block.hash in self.orphan_pool:
                return

            self.expire_orphans()

            # Strop je nově v BAJTECH, ne v položkách. Počet položek je špatná
            # jednotka ze stejného důvodu jako u EXPENSIVE_BYTES_*: 100 prázdných
            # bloků stojí zlomek toho, co 100 plných, a útočník si vybere ty plné.
            # OPRAVA N-8: vytěsňovalo se FIFO bez ohledu na práci, takže 17 orphanů
            # s nejsnazším povoleným targetem (po ZMĚNĚ 6 ~2^22 hashů, v době
            # nálezu ~2^20) vytlačilo i legitimní
            # orphan s plnou síťovou obtížností (test t_bug8_orphans.py). Nově se
            # obětuje orphan s NEJMENŠÍ prací (při shodě nejstarší) a jen tehdy,
            # když nový nese práce víc - levný spam tak nevytlačí dražší bloky.
            prace_noveho = (1 << 256) // block.target
            while self.orphan_pool and self.orphan_pool_bytes + size > MAX_ORPHAN_POOL_BYTES:
                obet = min(self.orphan_pool,
                           key=lambda h: ((1 << 256) // self.orphan_pool[h].target,
                                          self.orphan_added_at.get(h, 0)))
                # OPRAVA S-6 (Nález 3): dřív tu bylo `>=`, tedy při SHODNÉ práci se
                # nevytěsnilo nic. calculate_expected_target() ale vrací pro
                # index <= DIFFICULTY_ADJUSTMENT_INTERVAL natvrdo FIXED_TARGET, takže
                # v prvních 144 blocích sítě (~2,4 h) mají VŠECHNY bloky práci
                # shodnou - pool se dal zaplnit a poctivé orphany se do něj až do
                # expirace (600 s) nedostaly. Totéž nastane kdykoli později, když
                # hashrate spadne na podlahu.
                #
                # Ochrana proti levnému spamu zůstává beze změny: orphan s MENŠÍ
                # prací pořád nevytlačí dražší blok. Při shodné práci se nově
                # obětuje nejstarší, což je pořadí, podle kterého se oběť už dnes
                # vybírá (druhý klíč min() je orphan_added_at) - nový blok je vždy
                # mladší než cokoli v poolu, takže samotné `>` stáří dorovná.
                if (1 << 256) // self.orphan_pool[obet].target > prace_noveho:
                    return
                self._drop_orphan(obet)
            if self.orphan_pool_bytes + size > MAX_ORPHAN_POOL_BYTES:
                return

            self.orphan_pool[block.hash] = block
            self.orphan_sizes[block.hash] = size
            self.orphan_added_at[block.hash] = get_time()
            self.orphan_pool_bytes += size
            self.orphan_parents[block.previous_hash].append(block.hash)
        finally:
            self.lock.release()

    def _orphan_children_items(self, parent_hash):
        # OPRAVA D-18: snímek dvojic (rodič, potomek) pro zásobník
        # resolve_orphans(). Pořadí je OBRÁCENÉ, aby se z LIFO odebíraly ve
        # stejném pořadí, v jakém je procházela původní rekurze.
        #
        # Čte se přes .get(), ne přes indexaci - orphan_parents je defaultdict
        # a indexace by pro neznámý hash vyrobila prázdnou položku, kterou by
        # pak `parent_hash not in self.orphan_parents` neodfiltrovalo.
        deti = self.orphan_parents.get(parent_hash)
        if not deti:
            return []
        return [(parent_hash, ch) for ch in reversed(deti)]

    def resolve_orphans(self, parent_hash):
        # OPRAVA D-18: rekurze nahrazena zásobníkem.
        #
        # Rekurze tu byla VZÁJEMNÁ, ne jen přímá: resolve_orphans() volalo
        # add_block() a add_block() hned po zápisu bloku volá resolve_orphans()
        # zpátky. Na každý článek řetězu navazujících orphanů tedy padly dva
        # rámce Pythonu. Strop poolu 16 MiB při ~400 B na prázdný blok dovolí
        # až ~41 900 orphanů, zatímco limit rekurze je 1 000 - řetěz delší než
        # ~500 orphanů shodil RecursionError uprostřed přidávání bloků.
        #
        # Cenu útoku drží PoW (každý orphan musí splnit FIXED_TARGET), takže
        # je to teoretická mez, ne levný útok. Přepsat to je ale pár řádků.
        #
        # POŘADÍ ZŮSTÁVÁ STEJNÉ jako u rekurze - do hloubky, sourozenci zleva
        # doprava. Není to kosmetika: kdyby se přešlo na frontu (do šířky),
        # přidaly by se konkurenční větve v jiném pořadí a add_block() by dělal
        # mini-reorgy jinak, tedy jiný výsledný řetězec.
        #
        # Stav _orphan_pending_parents je sdílený přes self, ale resolve_orphans()
        # má jediného vnějšího volajícího - add_block() - a ten po celou dobu
        # drží self.lock (RLock), takže se sem dvě vlákna nedostanou.
        predane_zvenci = getattr(self, '_orphan_pending_parents', None)
        if predane_zvenci is not None:
            # Vnořené volání z add_block(). Místo zanoření jen předáme hash
            # vnější smyčce a vrátíme se - hloubka zásobníku Pythonu tím
            # zůstává konstantní bez ohledu na délku řetězu orphanů.
            predane_zvenci.append(parent_hash)
            return

        if parent_hash not in self.orphan_parents:
            return

        self._orphan_pending_parents = []
        try:
            zasobnik = self._orphan_children_items(parent_hash)
            while zasobnik:
                ocekavany_rodic, child_hash = zasobnik.pop()
                if child_hash not in self.orphan_pool:
                    continue
                child_block = self.orphan_pool[child_hash]
                # OPRAVA D-01: odebrání jde přes _drop_orphan(), aby se s blokem
                # uklidila i jeho velikost z orphan_pool_bytes. Původní kód dělal
                # pop() přímo, což by po zavedení bajtového stropu nechalo čítač
                # trvale nafouknutý a pool by se postupně sám uzavřel.
                self._drop_orphan(child_hash)
                if child_block.previous_hash != ocekavany_rodic:
                    continue

                self._orphan_pending_parents.clear()
                pridano = self.add_block(child_block, child_block.hash)
                # Hashe, na které by původní kód rekurzoval: co nám předalo
                # vnořené volání z add_block(), plus blok samotný (to dělal
                # řádek self.resolve_orphans(child_block.hash)).
                predane = list(self._orphan_pending_parents)
                self._orphan_pending_parents.clear()

                if pridano:
                    p2p_log(f"{Fore.GREEN}Orphan blok {child_block.index} přidán do chainu.{Style.RESET_ALL}")
                    if child_block.hash not in predane:
                        predane.append(child_block.hash)
                else:
                    self.recycle_orphan_transactions([child_block])
                    p2p_log(f"{Fore.RED}Orphan blok {child_block.index} nevalidní, zahazuji a recykluji tx.{Style.RESET_ALL}")

                # Potomci jdou NA VRCH zásobníku, aby se prošli dřív než
                # sourozenci právě zpracovaného bloku - tím vzniká totéž
                # pořadí do hloubky, jaké dávala rekurze.
                for h in reversed(predane):
                    zasobnik.extend(self._orphan_children_items(h))
        finally:
            self._orphan_pending_parents = None

    def _duvod_zamitnuti_z_mempoolu(self, tx, chain_tx_ids, kontext_retezce):
        """OPRAVA W-4 (audit 9. 10. 2026, nález N-4): dopočet důvodu BEZ dotazů do DB
        a BEZ lineárních průchodů mempoolem.

        Původní dopočet stál tři věci, a každou pro KAŽDOU zamítnutou transakci:
        vlastní sqlite3.connect() v is_tx_id_in_chain(), průchod celým seznamem
        unconfirmed_transactions přes any(...) a ještě jeden průchod kvůli součtu
        zůstatku. Je to doslova vzorec, který OPRAVA D-05 vymýtila z add_block()
        a OPRAVA D-04 z add_transaction() - sem se tehdy nedostaly.

        chain_tx_ids: výsledek JEDNOHO dávkového tx_ids_in_chain() od volajícího,
        nebo None, když se dávkový dotaz nepovedl (pak se padá zpět na dotaz po
        jedné transakci, tedy na původní chování).
        kontext_retezce: text do hlášky ("v blockchainu" / "v novém řetězci").

        Volající musí držet self.lock, aby se mezi zamítnutím a dopočtem nic
        nezměnilo - obě cesty (recyklace i reorg) ho drží.
        """
        if chain_tx_ids is None:
            v_retezci = self.is_tx_id_in_chain(tx.tx_id)
        else:
            v_retezci = tx.tx_id in chain_tx_ids
        if v_retezci:
            return f"Již existuje {kontext_retezce}"
        # OPRAVA D-04: index místo průchodu celým mempoolem.
        if tx.tx_id in self.mempool_by_txid:
            return "Již existuje v mempoolu"
        ocekavana = self.get_next_nonce(tx.from_address)
        if tx.nonce != ocekavana:
            return (f"Navazující chyba nonce (Máte {tx.nonce}, ale síť čeká na {ocekavana}. "
                    f"Pravděpodobně selhala předchozí transakce.)")
        # Sčítá se jen přes transakce TÉŽE adresy (shora omezené
        # MAX_PENDING_TX_PER_ADDRESS), ne přes celý mempool.
        obsazeno = sum(t.amount + t.fee for t in self.mempool_by_sender.get(tx.from_address, []))
        if self.get_confirmed_balance(tx.from_address) - obsazeno < tx.amount + tx.fee:
            return "Nedostatečný zůstatek (pokus o utracení zrušené coinbase odměny nebo již utracených prostředků)"
        return "Jiná chyba ověření (např. čas, podpis, plný mempool)"

    def recycle_orphan_transactions(self, orphaned_blocks):
        # OPRAVA W-4 (audit 9. 10. 2026, nález N-4): duplicita se zjišťuje JEDNÍM
        # dávkovým dotazem, ne jedním spojením na transakci.
        #
        # Dřív tu bylo `elif not self.is_tx_id_in_chain(tx.tx_id)` uvnitř cyklu
        # přes všechny transakce odpojeného bloku, a každé takové volání si
        # otevíralo vlastní sqlite3.connect() včetně PRAGMA. Naměřeno 3,0 spojení
        # na transakci (tenhle test + kontrola uvnitř add_transaction() + dopočet
        # důvodu zamítnutí), extrapolovaně ~5 000 spojení a ~0,9 s na plný blok -
        # a celé pod self.lock, tedy v soupeření s add_block(), který má rozpočet
        # jen ADD_BLOCK_LOCK_RETRIES x ADD_BLOCK_LOCK_TIMEOUT. Na flash paměti
        # telefonu je otevření souboru a načtení WAL násobně dražší než na x86.
        #
        # tx_ids_in_chain() existuje přesně pro tohle od OPRAVY D-05, jen se tu
        # nepoužíval. Výsledek slouží třikrát: k prvotnímu odfiltrování, jako
        # chain_tx_ids pro add_transaction() (ušetří druhé spojení na transakci)
        # a pro dopočet důvodu (třetí). Řetězec se mezitím změnit nemůže -
        # volající (add_block, resolve_orphans) drží self.lock.
        kandidati = []
        for block in orphaned_blocks:
            for tx in block.transactions:
                if tx.from_address == "COINBASE":
                    p2p_log(f"{Fore.YELLOW}COINBASE transakce {tx.tx_id} z osiřelého bloku #{block.index} zanikla (přirozené chování).{Style.RESET_ALL}")
                else:
                    kandidati.append(tx)

        try:
            v_retezci = self.tx_ids_in_chain([tx.tx_id for tx in kandidati])
        except Exception as e:
            # Selhání dotazu nesmí recyklaci shodit - kontrakt volajících
            # (add_block, resolve_orphans) s výjimkou odsud nepočítá. Bez
            # dávkového výsledku se jen vrátíme k dotazu po jedné transakci,
            # tedy k původnímu (pomalejšímu, ale správnému) chování.
            p2p_log(f"{Fore.YELLOW}Dávkový dotaz na duplicitní TX ID selhal ({type(e).__name__}: {e}), pokračuji po jedné.{Style.RESET_ALL}")
            v_retezci = None

        if v_retezci is None:
            orphaned_transactions = [tx for tx in kandidati if not self.is_tx_id_in_chain(tx.tx_id)]
        else:
            orphaned_transactions = [tx for tx in kandidati if tx.tx_id not in v_retezci]
        orphaned_transactions.sort(key=lambda x: (x.from_address, x.nonce))

        for tx in orphaned_transactions:
            # OPRAVA #11: allow_expired=True - tahle transakce už jednou byla v
            # bloku, takže ji nesmíme zahodit jen proto, že byla podepsána před
            # víc než MEMPOOL_TX_EXPIRATION. Bez toho ji uživatel po reorgu
            # nenávratně ztratil a musel ji podepsat znovu.
            if self.add_transaction(tx, allow_expired=True, chain_tx_ids=v_retezci):
                p2p_log(f"{Fore.GREEN}Osiřelá uživatelská transakce {tx.tx_id} přidána zpět do mempoolu.{Style.RESET_ALL}")
            else:
                reason = self._duvod_zamitnuti_z_mempoolu(tx, v_retezci, "v blockchainu")
                p2p_log(f"{Fore.RED}Osiřelá uživatelská transakce {tx.tx_id} zamítnuta z mempoolu. Důvod: {reason}.{Style.RESET_ALL}")

    def mine(self, miner_address):
        # OPRAVA #18: druhá pojistka vedle read-only gate v menu. Těžba s
        # nevěrohodným časem produkuje bloky, které síť odmítne (nebo které
        # odmítne i vlastní uzel), takže se do ní vůbec nepouštíme.
        if globals().get('read_only', False):
            print(f"{Fore.RED}Těžba zamítnuta: uzel je v read-only režimu (nevěrohodný nebo neověřený čas).{Style.RESET_ALL}")
            return False
        self.cleanup_mempool()
        try:
            # OPRAVA #6: mine() četla sdílený stav bez zámku. Zámek se dřív bral
            # až těsně před add_block(), ale čtení probíhalo dávno předtím:
            # get_total_supply(), iterace self.unconfirmed_transactions, self.nonce_map
            # a hlavně make_state_shadow(self) -> dict(self.balance_map). Všechno
            # souběžně mutovatelné P2P vlákny. dict() nad slovníkem, do kterého jiné
            # vlákno zapisuje, může vyhodit RuntimeError: dictionary changed size
            # during iteration; v lepším případě vznikne roztržený state_root a celé
            # kolo PoW je k ničemu. Celá příprava bloku (výběr transakcí i výpočet
            # state rootu) je proto nově pod zámkem. Zámek je RLock, takže vnořené
            # volání add_block() níž je bezpečné. Zámek KONČÍ před dotazem na počet
            # jader a před samotným PoW - jinak by uzel držel zámek po celou dobu
            # těžby a čekání na uživatelský vstup, a P2P vlákna by uvázla.
            with self.lock:
                new_block_index = self.max_block_index + 1
                halvings = new_block_index // HALVING_INTERVAL_BLOCKS
                current_reward = subsidy_po_halvingu(halvings)
                current_reward = max(0, min(current_reward, MAX_SUPPLY - self.get_total_supply()))
                
                mining_reward = Transaction("COINBASE", miner_address, 0, nonce=new_block_index, public_key=None, signature=None, data=None, chain_id=CHAIN_ID)
            
                total_fees = 0
                tx_by_sender = {}
            
                for tx in self.unconfirmed_transactions:
                    if tx.from_address not in tx_by_sender:
                        tx_by_sender[tx.from_address] = []
                    tx_by_sender[tx.from_address].append(tx)
                
                for sender in tx_by_sender:
                    tx_by_sender[sender].sort(key=lambda tx: tx.nonce)
            
                pq = []
                expected_nonces = {sender: self.nonce_map.get(sender, -1) + 1 for sender in tx_by_sender.keys()}
            
                for sender, txs in tx_by_sender.items():
                    if txs:
                        first_tx = txs[0]
                        if first_tx.nonce == expected_nonces[sender]:
                            heapq.heappush(pq, (-first_tx.fee, first_tx.timestamp, first_tx.tx_id, sender))
            
                selected_txs = []
                last_block_hash = self.get_last_block().hash
                # OPRAVA F-05: nad poškozenou DB se těžba nespustí. Dřív by
                # get_target() vrátil FIXED_TARGET a uzel by vytěžil blok,
                # který zbytek sítě odmítne - promarněná práce a rozštěpený
                # pohled na obtížnost.
                try:
                    target = self.get_target()
                except MissingChainDataError as e:
                    print(f"{Fore.RED}Těžbu nelze spustit:{Style.RESET_ALL} {e}")
                    print(f"{Fore.YELLOW}Databáze bloků je neúplná. Nechte uzel dosynchronizovat ze sítě.{Style.RESET_ALL}")
                    return False

                # OPRAVA U-6 (audit 5. 10. 2026, nález 1): spodní mez času bloku.
                # mine() stavěla Block() BEZ parametru timestamp, takže konstruktor
                # dosadil get_time() - bez ohledu na klouzavý medián. Všechny tři
                # validátory přitom vyžadují block.timestamp > median_time_past
                # (Block.is_valid_timestamp), a protože bloky smějí mít čas až
                # get_time() + 600, může MTP vyjít NAD aktuální čas. Od té chvíle
                # uzel vyráběl bloky, které sám odmítne: celé kolo PoW vniveč,
                # opakovaně, až ~600 s.
                #
                # Útočníka to nepotřebuje. Stačí, aby 6 z 11 posledních bloků
                # vytěžily uzly s hodinami napřed - MAX_NTP_OFFSET_SECONDS povoluje
                # odchylku ±300 s. calculate_expected_target() s natlačováním časů
                # na konec okna už počítá (POZNÁMKA U-5), jen se tam neřešil tenhle
                # vedlejší účinek na ŽIVOST poctivého těžaře.
                #
                # Řešení je totéž, jaké má Bitcoin Core:
                #   nTime = max(GetMedianTimePast() + 1, GetAdjustedTime())
                # Konsenzus se NEMĚNÍ - pravidlo zůstává beze změny, jen se
                # přestanou vyrábět bloky, které ho porušují.
                #
                # Počítá se pod TÍMŽ zámkem jako target a vrchol řetězce: kdyby
                # mezitím přišel cizí blok, posunul by se i MTP. Konzistenci hlídá
                # kontrola last_block_hash níž, která v takovém případě těžbu ruší.
                try:
                    mtp = self.get_median_time_past(new_block_index)
                except MissingChainDataError as e:
                    print(f"{Fore.RED}Těžbu nelze spustit:{Style.RESET_ALL} {e}")
                    print(f"{Fore.YELLOW}Databáze bloků je neúplná. Nechte uzel dosynchronizovat ze sítě.{Style.RESET_ALL}")
                    return False
                min_timestamp = mtp + 1
                block_timestamp = max(min_timestamp, get_time())

                # Horní mez téhož pravidla je get_time() + 600. Když ji spodní mez
                # přeroste, neexistuje ŽÁDNÝ čas, se kterým by byl blok platný -
                # kolo PoW by bylo prokazatelně zbytečné. Stejná úvaha jako
                # u OPRAVY #18 (read-only režim) a F-05 (neúplná DB): těžba se
                # nespouští do situace, o které dopředu víme, jak dopadne.
                if block_timestamp > get_time() + 600:
                    print(f"{Fore.YELLOW}Těžba odložena:{Style.RESET_ALL} medián času posledních 11 bloků (MTP) leží {mtp - get_time()} s v budoucnosti.")
                    print(f"{Fore.YELLOW}Platný blok nelze vytvořit dřív než za ~{block_timestamp - (get_time() + 600)} s. Zkuste to znovu později.{Style.RESET_ALL}")
                    return False

                # OPRAVA D-06: velikost bloku se počítá PŘÍRŮSTKOVĚ. Původně se
                # pro každého kandidáta stavěl celý zkušební blok a volal
                # get_size(), což znovu serializovalo VŠECHNY dosud vybrané
                # transakce - kvadratické v počtu kandidátů: 0,05 s při 100,
                # 3,49 s při 800, odhadem ~15 s pro plný 1 MiB blok. Při cílovém
                # čase bloku 60 s je to čtvrtina intervalu prohospodařená ještě
                # PŘED zahájením PoW, a to na x86; na ARM násobek.
                #
                # Rozklad je exaktní, ne odhad: JSON bloku je hlavička se
                # seznamem transakcí, takže
                #   velikost = základ(prázdný seznam) + suma velikostí transakcí
                #              + čárky mezi nimi (počet transakcí - 1).
                # tx.get_size() je díky cache z D-04 konstanta. Coinbase se
                # přepočítává, protože jeho amount roste s vybranými poplatky
                # a mění tím počet číslic.
                probe_block = Block(
                    index=new_block_index,
                    transactions=[],
                    previous_hash=last_block_hash,
                    target=target,
                    nonce=sys.maxsize,
                    timestamp=block_timestamp,
                    version=BLOCK_VERSION,
                    chain_id=CHAIN_ID,
                    state_root="0" * 64
                )
                probe_block.merkle_root = "0" * 64
                base_size = probe_block.get_size()
                selected_size = 0

                # OPRAVA D-09: mine() vybírala transakce podle nonce a poplatku,
                # ale NEKONTROLOVALA ZŮSTATKY. Spoléhala na to, že
                # update_state_with_block() nad stínovým stavem vyhodí ValueError
                # - jenže tím selhala CELÁ TĚŽBA, ne jen ta jedna transakce.
                # Vadná transakce přitom zůstala v mempoolu, protože
                # cleanup_mempool() řešil výhradně expiraci, ne platnost, takže
                # uzel nevytěžil nic až 24 hodin, než transakce sama vypršela.
                # Kód na to má hotovou logiku - stejnou jako temp_balance_changes
                # v add_block() - jen se nepoužívala.
                shadow_balance = defaultdict(int)
                mature_now = defaultdict(int)
                maturity_index = new_block_index - COINBASE_MATURITY
                if maturity_index in self.immature_rewards:
                    reward = self.immature_rewards[maturity_index]
                    mature_now[reward['address']] += reward['amount']
                unspendable_txs = []

                while pq:
                    _, _, _, sender = heapq.heappop(pq)
                    if sender not in tx_by_sender or not tx_by_sender[sender]:
                        continue
                    tx = tx_by_sender[sender].pop(0)

                    # OPRAVA D-09: neplatného kandidáta přeskočíme a označíme
                    # k odstranění z mempoolu, místo abychom shodili celou těžbu.
                    # Zbytek posloupnosti téže adresy se do fronty nevrací -
                    # bez téhle transakce by v posloupnosti nonce vznikla díra
                    # a navazující transakce jsou stejně nevytěžitelné.
                    available = (self.balance_map.get(tx.from_address, 0)
                                 + mature_now[tx.from_address]
                                 + shadow_balance[tx.from_address])
                    if available < tx.amount + tx.fee:
                        unspendable_txs.append(tx)
                        # OPRAVA B-3: mine() a cleanup_mempool() měly různou
                        # politiku. cleanup_mempool() odstraní neplatnou
                        # transakci I VŠECHNY NAVAZUJÍCÍ (správně - bez ní
                        # vznikne díra v posloupnosti nonce a zbytek je stejně
                        # nevytěžitelný), zatímco mine() odstranila jen tu
                        # jednu. Navazující transakce pak v mempoolu ležely
                        # nevytěžitelné, dokud uživatel nedoplnil chybějící
                        # nonce nebo neuplynulo MEMPOOL_TX_EXPIRATION (24 h),
                        # a každé kolo těžby je znovu bralo do úvahy.
                        # Sjednoceno na chování cleanup_mempool().
                        navazujici = tx_by_sender.get(sender) or []
                        if navazujici:
                            unspendable_txs.extend(navazujici)
                            tx_by_sender[sender] = []
                            print(f"{Fore.YELLOW}S transakcí {tx.tx_id} padá i {len(navazujici)} navazujících transakcí téže adresy (díra v nonce).{Style.RESET_ALL}")
                        print(f"{Fore.YELLOW}Transakce {tx.tx_id} přeskočena při sestavování bloku: nedostatečný zůstatek. Bude odstraněna z mempoolu.{Style.RESET_ALL}")
                        continue

                    test_reward = current_reward + total_fees + tx.fee
                    test_coinbase = Transaction("COINBASE", miner_address, test_reward, nonce=new_block_index, public_key=None, signature=None, timestamp=mining_reward.timestamp, data=None, chain_id=CHAIN_ID)

                    # Počet transakcí v kandidátovi = coinbase + vybrané + tahle,
                    # tedy čárek je o jednu míň.
                    candidate_size = (base_size
                                      + test_coinbase.get_size()
                                      + selected_size
                                      + tx.get_size()
                                      + (len(selected_txs) + 1))
                    if candidate_size > MAX_BLOCK_SIZE_BYTES:
                        continue
                    
                    selected_txs.append(tx)
                    selected_size += tx.get_size()
                    total_fees += tx.fee
                    shadow_balance[tx.from_address] -= (tx.amount + tx.fee)
                    shadow_balance[tx.to_address] += tx.amount
                    expected_nonces[sender] += 1
                
                    if tx_by_sender[sender]:
                        next_tx = tx_by_sender[sender][0]
                        if next_tx.nonce == expected_nonces[sender]:
                            heapq.heappush(pq, (-next_tx.fee, next_tx.timestamp, next_tx.tx_id, sender))

                # OPRAVA D-09: nevytěžitelné transakce z mempoolu ven, jinak by
                # je další kolo těžby zkoušelo znovu a znovu.
                if unspendable_txs:
                    for bad_tx in unspendable_txs:
                        self._mempool_remove(bad_tx)
                    save_mempool(self.unconfirmed_transactions)
                    
                tx_id_set = set()
                nonce_map = {}
                for tx in selected_txs:
                    if tx.tx_id in tx_id_set:
                        print(f"{Fore.RED}Chyba v mineru:{Style.RESET_ALL} Duplicitní TX ID {tx.tx_id} v vybraných transakcích. Těžba nebyla spuštěna.")
                        return False
                    tx_id_set.add(tx.tx_id)
                    if tx.from_address != "COINBASE":
                        if tx.from_address in nonce_map:
                            if tx.nonce in nonce_map[tx.from_address]:
                                print(f"{Fore.RED}Chyba v mineru:{Style.RESET_ALL} Duplicitní nonce {tx.nonce} pro adresu {tx.from_address} v vybraných transakcích. Těžba nebyla spuštěna.")
                                return False
                            nonce_map[tx.from_address].add(tx.nonce)
                        else:
                            nonce_map[tx.from_address] = {tx.nonce}
                        
                final_reward = current_reward + total_fees
                # OPRAVA AUDIT-10 (druhá část - živost sítě): tady dřív stálo
                # `return False`, tedy těžba se vůbec nespustila. Ve spojení
                # s vyčerpanou emisí (subsidy = 0 od bloku 33 000 000) to
                # znamenalo, že při prázdném mempoolu se ŘETĚZEC ZASTAVÍ:
                # poctivý těžař nevytěží nic, dokud nepřijde aspoň jedna
                # transakce s poplatkem. Blok s nulovou coinbase je přitom
                # podle konsenzu naprosto platný (`amount == expected_reward
                # + total_fees`, tedy 0 == 0) a po opravě deserializace výš
                # ho přijmou i ostatní uzly.
                #
                # Těžba proto pokračuje i s nulovou odměnou - jen se to
                # uživateli oznámí, ať ví, proč mu na účet nic nepřibude.
                # Blok se v takovém případě těží čistě kvůli živosti sítě.
                if final_reward == 0:
                    print(f"{Fore.YELLOW}Upozornění:{Style.RESET_ALL} Emise je vyčerpána a mempool je prázdný - blok se vytěží s nulovou odměnou (kvůli živosti sítě).")
                
                new_block_transactions = [Transaction("COINBASE", miner_address, final_reward, nonce=new_block_index, public_key=None, signature=None, timestamp=mining_reward.timestamp, data=None, chain_id=CHAIN_ID)] + selected_txs
            
                # OPRAVA U-6: timestamp se předává explicitně (viz výpočet
                # block_timestamp výš). Bez něj by konstruktor dosadil holý
                # get_time() a blok mohl padnout na vlastní kontrole MTP.
                new_block = Block(
                    index=new_block_index,
                    transactions=new_block_transactions,
                    previous_hash=last_block_hash,
                    target=target,
                    timestamp=block_timestamp,
                    version=BLOCK_VERSION,
                    chain_id=CHAIN_ID
                )

                # State root se počítá až nad finálním seznamem transakcí, ale ještě
                # před PoW - přechod stavu nezávisí na nonce, takže root je v tuhle
                # chvíli už jednoznačně určený a může vstoupit do hashovaného headeru.
                try:
                    # OPRAVA N-11: bez kopie celého stavu, viz state_root_po_bloku().
                    new_block.state_root = self.state_root_po_bloku(new_block)
                # OPRAVA G-02: struct.error doplněn jako pojistka. Rozsahové kontroly v encode_account() by ji už neměly připustit, ale kontrakt "ven jde vždy ValueError" musí platit bezvýhradně.
                except (ValueError, struct.error) as e:
                    print(f"{Fore.RED}Kritická chyba: Nelze spočítat state root pro nový blok ({e}).{Style.RESET_ALL}")
                    return False
                new_block.hash = new_block.compute_hash()
            
                new_block.nonce = sys.maxsize
                if new_block.get_size() > MAX_BLOCK_SIZE_BYTES:
                    print(f"{Fore.RED}Kritická chyba: Výsledný blok přesahuje maximální velikost před těžbou.{Style.RESET_ALL}")
                    return False
                new_block.nonce = 0
            
                if self.get_last_block().hash != last_block_hash:
                    print(f"{Fore.YELLOW}Těžba zrušena: Mezitím přišel nový blok od jiného uzlu.{Style.RESET_ALL}")
                    return False
                
            num_cores = multiprocessing.cpu_count()
            print(f"Detekováno {num_cores} CPU jader.")
            try:
                user_cores = int(input("Vyberte počet dostupných CPU jader: "))
                if 1 <= user_cores <= num_cores:
                    num_cores = user_cores
                else:
                    print(f"{Fore.RED}Neplatný počet. Používám všechna {num_cores} jádra.{Style.RESET_ALL}")
            except ValueError:
                print(f"{Fore.RED}Neplatný vstup. Používám všechna {num_cores} jádra.{Style.RESET_ALL}")
                
            if self.get_last_block().hash != last_block_hash:
                print(f"{Fore.YELLOW}Těžba zrušena: Mezitím přišel nový blok od jiného uzlu.{Style.RESET_ALL}")
                return False
                
            # OPRAVA U-6: spodní mez času jde až k workerům - při resetu PoW
            # po 60 s si ji musí uplatnit taky, jinak by MTP obešel reset.
            proof = self.proof_of_work(new_block, num_cores, min_timestamp=min_timestamp)
            if proof is None:
                return False
                
            with self.lock:
                if self.get_last_block().hash != last_block_hash:
                    print(f"{Fore.YELLOW}Těžba zrušena: Řetězec se mezitím změnil.{Style.RESET_ALL}")
                    return False
                if self.add_block(new_block, proof):
                    print(f"{Fore.GREEN}Blok {new_block.index} byl vytěžen a přidán do řetězce!{Style.RESET_ALL} (Target: {hex(target)[2:]})")
                    print(f"  Datum: {time.strftime('%d.%m.%Y %H:%M:%S UTC+00:00', time.gmtime(new_block.timestamp))}")
                    print(f"  Velikost bloku: {Fore.CYAN}{new_block.get_size() / 1024:.2f} KB{Style.RESET_ALL}")
                    # OPRAVA G-12: dělení floatem nahrazeno Decimalem. int/int dává
                    # v Pythonu float a ten má 53bitovou mantisu, tedy ~15,9 platné
                    # číslice - zůstatek v nanitech jich má až 17. Na 2 000 000
                    # náhodných zůstatků se výpis rozešel s přesnou hodnotou v 11 %
                    # případů, vždy o jeden nanit. Účetní kniha je celočíselná a byla
                    # v pořádku, ale uživatel viděl jinou částku, než doopravdy měl.
                    print(f"  Odměna za blok: {Fore.CYAN}{format(Decimal(current_reward) / Decimal(10 ** DECIMALS), f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                    print(f"  Poplatky z transakcí: {Fore.CYAN}{format(Decimal(total_fees) / Decimal(10 ** DECIMALS), f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                    print(f"  Celková odměna pro těžaře: {Fore.CYAN}{format(Decimal(final_reward) / Decimal(10 ** DECIMALS), f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                    print(f"  Těžařská adresa: {Fore.CYAN}{miner_address}{Style.RESET_ALL}")
                    
                    save_mempool(self.unconfirmed_transactions)
                    # OPRAVA W-2 (nález N-2): jde přes preposli_sousedum(), aby
                    # se vlastní blok zapsal do evidence přeposlaného. Bez addr
                    # se nevynechává nikdo - rozesílá se všem, jako dosud.
                    # Kdyby se nám blok vrátil od souseda, add_block() ho odmítne
                    # a evidence je druhá pojistka proti zbytečnému druhému kolu.
                    p2p_node.preposli_sousedum({'type': 'new_block', 'data': new_block.to_dict()},
                                               ('blok', new_block.hash), None)
                    return new_block.index
            return False
        except KeyboardInterrupt:
            self.mining_in_progress = False
            print(f"\n{Fore.YELLOW}Těžba byla ukončena uživatelem (CTRL+C).{Style.RESET_ALL}")
            return False

    def validate_fork(self, fork_index, new_chain_tail):
        # OPRAVA A-5: obal, který otevře JEDNO spojení na celé ověření forku
        # a předá ho oknům MTP i LWMA-3. Stejný vzorec jako _store_fork_batch()
        # / _store_fork_batch_inner(). Selže-li otevření, pokračuje se s
        # conn=None a každé volání si otevře vlastní - funkčnost tím netrpí,
        # jen se ztratí úspora.
        conn = None
        try:
            conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
        except sqlite3.Error:
            conn = None
        try:
            return self._validate_fork_inner(fork_index, new_chain_tail, conn)
        finally:
            if conn is not None:
                try:
                    conn.close()
                except Exception:
                    pass

    def _validate_fork_inner(self, fork_index, new_chain_tail, okno_conn=None):
        # OPRAVA D-16: návratová hodnota rozlišuje TŘI stavy, ne dva.
        #
        #   True  - fork je platný, jde s ním state_dict a undo logy
        #   False - fork je PROKAZATELNĚ NEPLATNÝ; volající ho má rovnou zahodit
        #   None  - NEVÍM: nepodařilo se sestavit výchozí stav pro fork_index-1,
        #           takže se o platnosti nedalo rozhodnout. Teprve tady má smysl
        #           fallback na is_valid_chain() od genesis.
        #
        # Dřív se vracelo (False, None, {}) v obou nerozhodných i zamítavých
        # případech a replace_chain() je nerozlišoval (podmínka
        # `not is_valid and new_state is None` je při selhání splněná VŽDY).
        # Každý neplatný fork tak spustil revalidaci CELÉHO řetězce od genesis
        # včetně všech podpisů: fork o 2 blocích s vadou až v posledním
        # protlačil is_valid_chain přes 42 bloků. Zesílení roste lineárně
        # s délkou řetězce a útočník ho pořizuje za cenu dvou bloků - na mobilu
        # je to citelné. Fallback je nově vyhrazený jen pro stav "nevím".
        state = self.get_state_at(fork_index - 1)
        if state is None:
            # Stav se nedá odrolovat (undo logy tak hluboko nesahají). O forku
            # to neříká nic - rozhodne až fallback.
            return None, None, {}
            
        balance_map = state['balance_map']
        nonce_map = state['nonce_map']
        total_supply = state['total_supply']
        immature_rewards = state['immature_rewards']
        cumulative_work = state['cumulative_work']
        
        previous_block = self.get_block(fork_index - 1)
        if not previous_block:
            # OPRAVA D-16: chybí blok v NAŠÍ databázi, ne v dodaném forku.
            # Je to tedy taky "nevím", ne důkaz neplatnosti - fork proti němu
            # nikdy nebyl ověřen. Fallback nad kompletním řetězcem tuhle díru
            # najde a odmítne, ale rozhodnutí patří jemu.
            return None, None, {}
            
        chain_window = {}
        new_undo_logs = {}
        # OPRAVA #19: validate_fork() jako jediná cesta k novému stavu nevytvářela
        # state_checkpoints. Po reorgu tak rebuild_state() musel přehrávat řetězec
        # od výrazně staršího checkpointu (nebo od genesis), což je čistě výkonová
        # ztráta, ale na mobilu citelná. Checkpointy stavíme ve stejném rytmu i
        # formátu jako update_state_with_block(), aby byly zaměnitelné.
        new_state_checkpoints = {}
        
        fork_tx_ids = set()
        
        for current_block in new_chain_tail:
            chain_window[current_block.index] = current_block
            
            current_block_size = current_block.get_size()
            if current_block_size > MAX_BLOCK_SIZE_BYTES:
                return False, None, {}
            if current_block.chain_id != CHAIN_ID:
                return False, None, {}
            if current_block.version != BLOCK_VERSION:
                return False, None, {}
            if current_block.hash != current_block.compute_hash():
                return False, None, {}
            if current_block.previous_hash != previous_block.hash:
                return False, None, {}
            if current_block.index != previous_block.index + 1:
                return False, None, {}

            # OPRAVA F-10: checkpointy se vynucovaly JEN v is_valid_chain().
            # Ověřeno: add_block() blok přijal a zapsal do DB, validate_fork()
            # taky, ale is_valid_chain() nad touž DB vrátila False - a protože
            # load_data() na neplatný řetězec reaguje sys.exit(1), uzel by po
            # restartu už nenaběhl. Dnes je položka jediná (index 0), ale je to
            # mina nastražená na okamžik, kdy se přidá druhý checkpoint.
            if current_block.index in CHECKPOINTS and current_block.hash != CHECKPOINTS[current_block.index]:
                return False, None, {}

            # OPRAVA F-05: chybějící blok v okně = odmítnutí, ne fail-open.
            try:
                median_time_past = self.get_median_time_past(current_block.index, chain_dict=chain_window, conn=okno_conn)
                expected_target = self.calculate_expected_target(current_block.index, chain_dict=chain_window, conn=okno_conn)
            except MissingChainDataError:
                return False, None, {}

            if not current_block.is_valid_timestamp(median_time_past):
                return False, None, {}

            if current_block.target != expected_target:
                return False, None, {}
            # ZMĚNA 5 (názvosloví): třetí místo, kde se kontroluje kořen
            # transakčního stromu - ale jediné BEZ hlášky, takže tu není co
            # přejmenovat. _validate_fork_inner() nelogovala nikdy a vrací jen
            # False; je to vědomý stav, ne přehlédnutí (viz výjimka u pravidla
            # "transakce na vlastní adresu", kde se log doplňoval a komentář to
            # výslovně zmiňuje). Poznámka je tu proto, aby při příštím hledání
            # podle řetězce "Merkle root" tohle místo nevypadalo jako
            # zapomenuté. Text pro add_block() a _is_valid_chain_inner() viz
            # obsáhlý komentář v add_block().
            if current_block.merkle_root != compute_merkle_root(current_block.transactions):
                return False, None, {}
            if not self.meets_difficulty(current_block.hash, current_block.target):
                return False, None, {}
            if any(tx.data is not None for tx in current_block.transactions):
                return False, None, {}

            coinbase_txs = [tx for tx in current_block.transactions if tx.from_address == "COINBASE"]
            if len(coinbase_txs) != 1 or current_block.transactions[0].from_address != "COINBASE":
                return False, None, {}

            coinbase_tx = coinbase_txs[0]

            # OPRAVA D-11: stejné pravidlo jako v add_block() a is_valid_chain().
            # Nevalidované pole v konsenzuální struktuře vstupuje do tx_id,
            # merkle rootu i hashe bloku - volný grindovací prostor navíc.
            if coinbase_tx.fee != 0:
                return False, None, {}

            # OPRAVA F-09: coinbase nesmí nést libovolná data v public_key ani
            # v signature. Stejné pravidlo jako v add_block() a is_valid_chain() -
            # kdyby platilo jen někde, vznikl by consensus split.
            if coinbase_tx.public_key is not None or coinbase_tx.signature is not None:
                return False, None, {}

            # Stejné pravidlo jako v add_block(): nonce coinbase = výška bloku.
            if coinbase_tx.nonce != current_block.index:
                return False, None, {}

            halvings = current_block.index // HALVING_INTERVAL_BLOCKS
            expected_reward = subsidy_po_halvingu(halvings)
            expected_reward = max(0, min(expected_reward, MAX_SUPPLY - total_supply))
                
            total_fees = sum(tx.fee for tx in current_block.transactions if tx.from_address != "COINBASE")
            if coinbase_tx.amount != expected_reward + total_fees:
                return False, None, {}
                
            undo_data = {
                'balance_changes': defaultdict(int),
                'nonce_restores': {},
                'immature_restores': {},
                'immature_removes': [],
                'cumulative_work_change': 0,
                'total_supply_change': 0
            }

            total_supply += expected_reward
            undo_data['total_supply_change'] = expected_reward
            
            work = (1 << 256) // current_block.target if current_block.target > 0 else 0
            cumulative_work += work
            undo_data['cumulative_work_change'] = work

            block_nonce_map = {}

            # OPRAVA D-05: dřív se pro KAŽDOU transakci otevíralo nové
            # sqlite3.connect() přímo v cyklu - 306 spojení na blok s 300
            # transakcemi a odhadem ~1 705 440 spojení při reorgu do hloubky
            # 1000 s plnými bloky. Reorg se pak reálně nemusel stihnout pod
            # FORK_SYNC_IDLE_TIMEOUT. Nově jeden dotaz na celý blok.
            # OPRAVA X-3: dotažení D-05. validate_fork() otevře jedno spojení
            # a předává ho do get_median_time_past() i calculate_expected_target();
            # tohle volání jako jediné zůstalo bez něj, takže si tx_ids_in_chain()
            # otevíralo vlastní - jedno sqlite3.connect() na blok, tedy 1000
            # zbytečných spojení při reorgu do hloubky 1000.
            chain_tx_ids = self.tx_ids_in_chain(
                [tx.tx_id for tx in current_block.transactions], exclude_from_index=fork_index,
                conn=okno_conn
            )

            for tx in current_block.transactions:
                if not isinstance(tx.amount, int) or not isinstance(tx.fee, int) or not isinstance(tx.nonce, int):
                    return False, None, {}
                if tx.timestamp > current_block.timestamp + 7200:
                    return False, None, {}
                # OPRAVA D-12: spodní mez času transakce, stejně jako v add_block()
                # a is_valid_chain(). Bez ní projde transakce s timestamp = 1.
                if tx.timestamp < GENESIS_TIMESTAMP:
                    return False, None, {}
                if tx.chain_id != CHAIN_ID:
                    return False, None, {}
                if not is_valid_address(tx.to_address):
                    return False, None, {}
                    
                if tx.tx_id in fork_tx_ids:
                    return False, None, {}
                    
                if tx.tx_id in chain_tx_ids:
                    return False, None, {}
                    
                fork_tx_ids.add(tx.tx_id)
                
                if tx.from_address != "COINBASE":
                    if tx.amount <= 0 or tx.amount < MIN_TX_AMOUNT:
                        return False, None, {}
                    # OPRAVA #6b: jen dolní mez, stejně jako v add_block().
                    if tx.fee < TX_FEE_MIN:
                        return False, None, {}
                    # OPRAVA #6d: totéž pravidlo jako v add_block() - bez něj by
                    # uzel blok odmítl při přímém příjmu, ale přijal ho jako
                    # součást forku, a dva uzly by skončily na jiném řetězci.
                    if tx.from_address == tx.to_address:
                        # validate_fork() dosud nelogovala vůbec, takže se tu na
                        # existenci p2p_node nedá spolehnout tak jako jinde.
                        if 'p2p_node' in globals() and p2p_node is not None:
                            p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Transakce na vlastní adresu není povolena.{Style.RESET_ALL}")
                        return False, None, {}
                    if tx.from_address in block_nonce_map:
                        if tx.nonce in block_nonce_map[tx.from_address]:
                            return False, None, {}
                        block_nonce_map[tx.from_address].add(tx.nonce)
                    else:
                        block_nonce_map[tx.from_address] = {tx.nonce}
                        
                if not tx.verify_sender_identity() and tx.from_address != "COINBASE":
                    return False, None, {}
                if not tx.verify_signature() and tx.from_address != "COINBASE":
                    return False, None, {}

            for sender, nonces_in_block in block_nonce_map.items():
                expected_nonce = nonce_map.get(sender, -1) + 1
                for tx_nonce in sorted(nonces_in_block):
                    if tx_nonce != expected_nonce:
                        return False, None, {}
                    expected_nonce += 1
                if sender not in undo_data['nonce_restores']:
                    undo_data['nonce_restores'][sender] = nonce_map.get(sender, -1)
                nonce_map[sender] = expected_nonce - 1

            touched_addresses = set()

            target_index = current_block.index - COINBASE_MATURITY
            if target_index in immature_rewards:
                reward_data = immature_rewards.pop(target_index)
                balance_map[reward_data['address']] = balance_map.get(reward_data['address'], 0) + reward_data['amount']
                touched_addresses.add(reward_data['address'])
                
                undo_data['immature_restores'][target_index] = reward_data
                undo_data['balance_changes'][reward_data['address']] -= reward_data['amount']

            temp_balance_changes = defaultdict(int)
            for tx in current_block.transactions:
                if tx.from_address != "COINBASE":
                    current_balance = balance_map.get(tx.from_address, 0) + temp_balance_changes[tx.from_address]
                    if current_balance < tx.amount + tx.fee:
                        return False, None, {}
                    temp_balance_changes[tx.from_address] -= (tx.amount + tx.fee)
                    temp_balance_changes[tx.to_address] += tx.amount
                    # OPRAVA G-03: tady byla podmínka
                    #     if tx.from_address not in undo_data['nonce_restores']:
                    #         undo_data['nonce_restores'][tx.from_address] = nonce_map.get(...)
                    # Nemohla být NIKDY pravdivá: každý ne-coinbase odesílatel se
                    # dostane do block_nonce_map ve smyčce nad transakcemi výše
                    # a odtud do nonce_restores ve smyčce přes block_nonce_map,
                    # která běží PŘED tímhle kódem. A kdyby se přece provedla,
                    # uložila by už AKTUALIZOVANOU hodnotu nonce_map[sender] -
                    # tedy chybný undo log. Odstraněno, aby nesvádělo ke
                    # domněnce, že se tu něco ukládá.
                else:
                    immature_rewards[current_block.index] = {'address': tx.to_address, 'amount': tx.amount}
                    undo_data['immature_removes'].append(current_block.index)
            
            for addr, change in temp_balance_changes.items():
                balance_map[addr] = balance_map.get(addr, 0) + change
                undo_data['balance_changes'][addr] -= change
                touched_addresses.add(addr)

            prune_zero_balances(balance_map, touched_addresses)

            # OPRAVA F-03: validate_fork() si mapy mutuje SAMA, ne přes
            # update_state_with_block(), takže strom se musí dosynchronizovat
            # tady. Dotčené adresy jsou přesně touched_addresses; nonce se mění
            # jen odesílatelům, a ti jsou v temp_balance_changes, tedy už uvnitř.
            # Bez tohohle by strom zůstal na stavu z get_state_at() a reorg by
            # spadl na neshodě state rootu.
            fork_smt = _state_smt(state)
            if fork_smt is not None:
                dotcene = set(touched_addresses)
                dotcene.update(undo_data['nonce_restores'].keys())
                if dotcene:
                    fork_smt.sync_from_maps(balance_map, nonce_map, touched=dotcene)

            # Stav po tomto bloku musí odpovídat state rootu v jeho hlavičce.
            try:
                if fork_smt is not None:
                    expected_state_root = _state_root_bytes(
                        fork_smt.root(), immature_rewards, total_supply)
                else:
                    expected_state_root = compute_state_root(
                        balance_map, nonce_map, immature_rewards, total_supply)
            # OPRAVA G-02: struct.error doplněn jako pojistka. Rozsahové kontroly v encode_account() by ji už neměly připustit, ale kontrakt "ven jde vždy ValueError" musí platit bezvýhradně.
            except (ValueError, struct.error):
                return False, None, {}
            if current_block.state_root != expected_state_root:
                return False, None, {}

            new_undo_logs[current_block.index] = undo_data

            # OPRAVA #19: periodický checkpoint stavu PO tomto bloku.
            if current_block.index > 0 and current_block.index % 1000 == 0:
                new_state_checkpoints[current_block.index] = {
                    'balance_map': balance_map.copy(),
                    'nonce_map': nonce_map.copy(),
                    'immature_rewards': copy.deepcopy(immature_rewards),
                    'total_supply': total_supply,
                    'cumulative_work': cumulative_work
                }

            previous_block = current_block

        state_dict = {
            'balance_map': balance_map,
            'nonce_map': nonce_map,
            'total_supply': total_supply,
            'cumulative_work': cumulative_work,
            'immature_rewards': immature_rewards,
            'state_checkpoints': new_state_checkpoints,
            # OPRAVA F-03: strom putuje se stavem. replace_chain() ho převezme
            # spolu s mapami, takže po reorgu nezačíná uzel s prázdnou cache.
            'accounts_smt': _state_smt(state)
        }
        return True, state_dict, new_undo_logs

    def is_valid_chain(self, chain_iterable=None, vrchol_index=None):
        # OPRAVA A-02: vrchol_index = index POSLEDNÍHO bloku ověřovaného řetězce.
        # Slouží jen k rozhodnutí, jestli smí platit ASSUMEVALID (viz
        # _is_valid_chain_inner). Volající, který řetězec předává generátorem,
        # ho zná - generátor sám změřit nejde. Když se nepředá a řetězec jde
        # z generátoru, ASSUMEVALID se NEUPLATNÍ a podpisy se ověří všechny;
        # bezpečná strana je ta pomalejší.
        #
        # OPRAVA A-5: totéž co u validate_fork() - jedno spojení na celé
        # ověření řetězce místo dvou na každý blok.
        conn = None
        try:
            conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
        except sqlite3.Error:
            conn = None
        try:
            return self._is_valid_chain_inner(chain_iterable, conn, vrchol_index)
        except MissingChainDataError as e:
            # OPRAVA R-2: poškozený řádek ve VLASTNÍ databázi je "řetězec neplatný",
            # ne výjimka ven. load_data() na (False, None) reaguje záchranným
            # menu z OPRAVY F-14 (odložit DB a stáhnout znovu ze sítě), což je
            # přesně správná reakce na poškozená data.
            uzel = globals().get('p2p_node')
            hlaska = f"{Fore.RED}Chyba ověření řetězce: {e}{Style.RESET_ALL}"
            if uzel is not None and hasattr(uzel, 'add_log'):
                uzel.add_log(hlaska)
            else:
                print(hlaska)
            return False, None
        except (sqlite3.Error, OSError) as e:
            # OPRAVA S-1 (Nález 4): OPRAVA R-2 výš ošetřila poškozený ŘÁDEK,
            # ale ne poškozený SOUBOR. sqlite3.DatabaseError ("file is not a
            # database", "database disk image is malformed") z get_iterable()
            # proletěla ven, a protože load_data() volá is_valid_chain() bez
            # try a main() volá load_data() bez try, padal celý uzel tracebackem
            # místo záchranného menu z OPRAVY F-14. Na flash paměti telefonu je
            # to po výpadku napájení při zápisu běžný stav, ne teorie.
            #
            # Kontrakt funkce je (bool, state|None) - držíme ho i tady.
            #
            # POZOR: sqlite3.OperationalError ("database is locked", typicky
            # druhá běžící instance uzlu) je podtřída DatabaseError a spadne
            # sem taky. ZDRAVOU databázi tedy nesmí nikdo podle tohohle
            # návratu prohlásit za poškozenou - rozlišení dělá nedestruktivní
            # sonda _db_je_jen_zamcena() v load_data() PŘED záchranným menu.
            uzel = globals().get('p2p_node')
            hlaska = (f"{Fore.RED}Chyba ověření řetězce: databázi nelze číst "
                      f"({type(e).__name__}: {e}).{Style.RESET_ALL}")
            if uzel is not None and hasattr(uzel, 'add_log'):
                uzel.add_log(hlaska)
            else:
                print(hlaska)
            return False, None
        finally:
            if conn is not None:
                try:
                    conn.close()
                except Exception:
                    pass

    def _is_valid_chain_inner(self, chain_iterable=None, okno_conn=None, vrchol_index=None):
        global p2p_node
        if 'p2p_node' not in globals() or p2p_node is None:
            class DummyNode:
                def add_log(self, msg):
                    print(msg)
            p2p_node = DummyNode()

        # OPRAVA F-08: obě struktury dřív rostly bez omezení a nikdy se z nich
        # nic neodebíralo.
        #
        # seen_tx_ids (množina VŠECH tx_id celého řetězce) stála 132 MB
        # na milion transakcí. Zrušena, protože kontrola, kterou dělala, je
        # implikovaná pravidly, která se ověřují o pár řádků níž v témž průchodu:
        #   - tx_id = sha3_256(get_signing_data()), a get_signing_data() kóduje
        #     všechna pole délkově prefixovaně, takže je kódování prosté
        #     (dvě různé transakce nemohou dát tentýž vstup hashe);
        #   - u běžné transakce vstupuje do podpisových dat from_address i nonce,
        #     přičemž nonce jsou vynucené STRIKTNĚ POSLOUPNÉ přes celý řetězec
        #     (viz nonce_last_seen níž) - táž dvojice (odesílatel, nonce) se
        #     tedy v řetězci nemůže objevit dvakrát;
        #   - u coinbase je from_address vždy "COINBASE" a platí pravidlo
        #     coinbase.nonce == index bloku, přičemž návaznost indexů je
        #     kontrolovaná - dvě coinbase tedy nemohou mít stejnou nonce.
        # Duplicitní tx_id napříč řetězcem je proto nedosažitelný stav.
        # Kontrola duplicity UVNITŘ bloku (block_tx_ids) zůstává beze změny;
        # ta je omezená velikostí bloku, tedy konstantní.
        #
        # nonce_maps drželo množinu VŠECH nonce každé adresy a expected_nonce
        # se počítal přes max() - O(k), tedy ~13,5 ms na blok u adresy s
        # milionem transakcí. Protože jsou nonce vynucené striktně posloupné,
        # stačí poslední použitá hodnota: jeden int na adresu.
        nonce_last_seen = {}
        
        # Nosič stavu (balance_map, nonce_map, immature_rewards, total_supply,
        # cumulative_work, undo_logs, state_checkpoints), do kterého zapisuje
        # update_state_with_block(). Díky tomu se validace a stavba stavu
        # (dříve dělaná odděleně přes rebuild_state) provádí v jediném průchodu
        # řetězcem, a přitom se self nezmění, dokud není celý řetězec ověřen
        # jako platný (důležité pro replace_chain, který ověřuje navrhovaný
        # řetězec ještě před jeho přijetím).
        state = SimpleNamespace(
            balance_map={},
            nonce_map={},
            immature_rewards={},
            total_supply=0,
            cumulative_work=0,
            undo_logs={},
            state_checkpoints={},
            # OPRAVA F-03: is_valid_chain() staví stav od genesis bloku, takže
            # začíná s prázdným stromem a dál ho udržuje update_state_with_block().
            # Tohle je ta nejdůležitější cesta: právě tady se stavěl SMT znovu
            # pro KAŽDÝ blok řetězce.
            accounts_smt=AccountsSMT()
        )
        
        chain_window = {}
        previous_block = None
        
        def get_iterable():
            if chain_iterable is not None:
                for b in chain_iterable:
                    yield b
            else:
                # OPRAVA R-2: totéž ošetření, jaké dostal rebuild_state() v M-2.
                # Block.from_dict() má kontrakt "nad špatnými daty vyhoď
                # ValueError" a json.loads() vyhodí JSONDecodeError (podtřída
                # ValueError). Obojí se tu dělalo nad ŘÁDKY Z VLASTNÍ DB bez
                # jakéhokoli ošetření, takže poškozený řádek proletěl ven z
                # is_valid_chain() - a ta se z load_data() volá BEZ try, takže
                # uzel spadl s tracebackem místo záchranného menu (F-14).
                # Kontrakt téhle metody je "vrať (False, None)", ne "vyhoď".
                #
                # Spojení se navíc zavíralo až ZA smyčkou, takže ho předčasný
                # return volajícího (neplatný blok) přeskočil úplně - generátor
                # se zahodil na yieldu a close() se nikdy neprovedl. To je
                # přesně spoléhání na GC, které OPRAVA G-08 zakazuje.
                conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
                try:
                    conn.execute("PRAGMA journal_mode=WAL;")
                    c = conn.cursor()
                    c.execute("SELECT block_index, timestamp, transactions, previous_hash, target_hex, nonce, block_hash, merkle_root, version, chain_id, state_root FROM blocks ORDER BY block_index")
                    for row in c:
                        try:
                            blok = Block.from_dict({
                                'index': row[0],
                                'timestamp': row[1],
                                'transactions': json.loads(row[2]),
                                'previous_hash': row[3],
                                'target': row[4],
                                'nonce': row[5],
                                'hash': row[6],
                                'merkle_root': row[7],
                                'version': row[8],
                                'chain_id': row[9], 'state_root': row[10]
                            })
                        except (ValueError, KeyError, TypeError, struct.error,
                                OverflowError, json.JSONDecodeError) as e:
                            raise MissingChainDataError(
                                f"Blok #{row[0]} v blockchain.db je poškozený "
                                f"({type(e).__name__}: {e})."
                            ) from e
                        yield blok
                finally:
                    try:
                        conn.close()
                    except Exception:
                        pass

        # OPRAVA A-02: ASSUMEVALID smí platit JEN nad řetězcem, který nejvyšší
        # checkpoint skutečně obsahuje.
        #
        # Původní podmínka `index > NEJVYSSI_CHECKPOINT` se ptala pouze na výšku.
        # Ležel-li NEJVYSSI_CHECKPOINT nad vrcholem ověřovaného řetězce, byla
        # nepravdivá pro VŠECHNY bloky - podpisy se tedy přeskočily celému
        # řetězci - a zároveň se nikdy nespustila kontrola checkpointu níž,
        # protože se na tu výšku nedošlo. Ochrana i to, co ji má podmiňovat,
        # vypadly současně: řetězec s prokazatelně neplatným podpisem prošel.
        # Zasažená cesta je replace_chain(0, ...) -> is_valid_chain(), tedy
        # první synchronizace čerstvého uzlu - přesně stav, kdy je řetězec
        # kratší než checkpoint.
        #
        # Vrchol zjistíme PŘED smyčkou. Pro vlastní DB dotazem, pro předaný
        # iterátor z parametru (generátor změřit nejde). Když vrchol neznáme,
        # ověřujeme podpisy všechny - stojí to čas, ne bezpečnost.
        #
        # Návaznost indexů od nuly je vynucená (viz kontrola níž), takže při
        # vrchol >= NEJVYSSI_CHECKPOINT se kontrola checkpointu zaručeně
        # provede. Bloky pod checkpointem se sice ověří dřív, než se checkpoint
        # potvrdí, ale při jeho selhání se odmítne celý řetězec.
        vrchol_retezce = vrchol_index
        if vrchol_retezce is None and chain_iterable is None:
            vrchol_conn = okno_conn
            vlastni_conn = None
            try:
                if vrchol_conn is None:
                    vlastni_conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
                    vrchol_conn = vlastni_conn
                radek = vrchol_conn.execute("SELECT MAX(block_index) FROM blocks").fetchone()
                if radek is not None and radek[0] is not None:
                    vrchol_retezce = int(radek[0])
            except (sqlite3.Error, ValueError, TypeError, OverflowError):
                vrchol_retezce = None
            finally:
                if vlastni_conn is not None:
                    try:
                        vlastni_conn.close()
                    except Exception:
                        pass

        assumevalid_platny = (
            ASSUMEVALID
            and vrchol_retezce is not None
            and vrchol_retezce >= NEJVYSSI_CHECKPOINT
        )
        # Hláška má smysl jen tam, kde by ASSUMEVALID reálně něco přeskočil.
        # Při jediném checkpointu na genesis (dnešní stav) se pod ním neověřuje
        # nic, takže by šlo o čistý šum - třeba nad prázdnou DB při prvním startu.
        if ASSUMEVALID and not assumevalid_platny and NEJVYSSI_CHECKPOINT > 0:
            p2p_node.add_log(
                f"{Fore.YELLOW}Ověření řetězce: nejvyšší checkpoint (#{NEJVYSSI_CHECKPOINT}) "
                f"leží nad vrcholem ověřovaného řetězce, ověřuji všechny podpisy.{Style.RESET_ALL}")

        for current_block in get_iterable():
            # OPRAVA #2: pokud první blok iterovaného řetězce nemá index 0,
            # větev pro genesis se přeskočí a previous_block zůstane None -
            # o pár řádků níž pak `current_block.previous_hash != previous_block.hash`
            # vyhodí AttributeError: 'NoneType' object has no attribute 'hash'.
            # Dosažitelné ze sítě přes handler response_full_chain ->
            # replace_chain(0, ocas_nezačínající_na_0). Zámek se sice díky finally
            # uvolnil (deadlock nehrozil), ale zpracování zprávy skončilo
            # tracebackem místo čistého odmítnutí. Řetězec, který nezačíná
            # genesis blokem, je prostě neplatný - odmítneme ho hned.
            if previous_block is None and current_block.index != 0:
                p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Řetězec nezačíná genesis blokem (první blok má index #{current_block.index}).{Style.RESET_ALL}")
                return False, None

            current_block_size = current_block.get_size()

            # OPRAVA A-6 (assumevalid): blok pod nejvyšším checkpointem má obsah
            # zavázaný hashovým řetězcem, který k tomu checkpointu vede. Ověřovat
            # jeho podpisy znovu je práce navíc bez informační hodnoty - a je to
            # 97 % času startovní validace. Vše ostatní (hash, merkle root,
            # state root, target, časy, přehrání stavu) se dělá dál beze změny.
            # OPRAVA A-02: místo ASSUMEVALID se ptáme na assumevalid_platny,
            # spočítané před smyčkou. Výška bloku sama o sobě nestačí - musí
            # platit i to, že ověřovaný řetězec checkpoint vůbec obsahuje.
            overit_podpisy = (not assumevalid_platny) or current_block.index > NEJVYSSI_CHECKPOINT

            chain_window[current_block.index] = current_block
            if len(chain_window) > LAST_BLOCKS_TO_KEEP:
                oldest = min(chain_window.keys())
                del chain_window[oldest]
                
            if current_block.index in CHECKPOINTS:
                if current_block.hash != CHECKPOINTS[current_block.index]:
                    p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Blok #{current_block.index} neodpovídá checkpointu (očekáváno: {CHECKPOINTS[current_block.index]}).{Style.RESET_ALL}")
                    return False, None

            if current_block.index == 0:
                if current_block_size > MAX_BLOCK_SIZE_BYTES:
                    p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Velikost Genesis bloku překračuje limit.{Style.RESET_ALL}")
                    return False, None
                if current_block.hash != current_block.compute_hash():
                    p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Hash genesis bloku neodpovídá obsahu.{Style.RESET_ALL}")
                    return False, None
                if current_block.index != 0 or current_block.previous_hash != "0" or current_block.target != FIXED_TARGET or current_block.chain_id != CHAIN_ID or current_block.version != BLOCK_VERSION:
                    p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Nesprávné vlastnosti genesis bloku.{Style.RESET_ALL}")
                    return False, None
                if current_block.timestamp != GENESIS_TIMESTAMP:
                    p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Podvržený genesis blok (špatný čas)!{Style.RESET_ALL}")
                    return False, None
                # OPRAVA #12: větev pro index == 0 neobsahovala volání
                # meets_difficulty(), takže PoW genesis bloku se nikdy
                # nekontrolovalo. Fakticky to zachraňoval CHECKPOINTS[0], ale
                # pravidlo, o kterém si člověk myslí, že platí, vynucené nebylo.
                if not self.meets_difficulty(current_block.hash, current_block.target):
                    p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Genesis blok nesplňuje svůj target (chybí platný PoW).{Style.RESET_ALL}")
                    return False, None
                if len(current_block.transactions) != 1 or current_block.transactions[0].from_address != "COINBASE":
                    return False, None
                    
                genesis_tx = current_block.transactions[0]
                if not is_valid_address(genesis_tx.to_address) or genesis_tx.to_address != GENESIS_ADDRESS or genesis_tx.amount != GENESIS_AMOUNT or genesis_tx.timestamp != GENESIS_TIMESTAMP or genesis_tx.nonce != 0:
                    return False, None
                if current_block.merkle_root != compute_merkle_root(current_block.transactions):
                    return False, None
                if genesis_tx.data != "BTC: 000000000000000000009c26a9609e1956765cb1a89fb4cdd2411b75f208dd76":
                    return False, None
                    
                # OPRAVA B-1: totéž pravidlo i pro genesis blok.
                try:
                    self.update_state_with_block(current_block, state_target=state)
                    expected_state_root = compute_state_root_from(state)
                # OPRAVA G-02: struct.error doplněn jako pojistka. Rozsahové kontroly v encode_account() by ji už neměly připustit, ale kontrakt "ven jde vždy ValueError" musí platit bezvýhradně.
                except (ValueError, struct.error) as e:
                    p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Neplatný stav po genesis bloku ({e}).{Style.RESET_ALL}")
                    return False, None
                if current_block.state_root != expected_state_root:
                    p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Nesprávný state root genesis bloku (očekáván {expected_state_root}).{Style.RESET_ALL}")
                    return False, None
                # OPRAVA F-08: seen_tx_ids zrušeno, viz komentář u inicializace.
                previous_block = current_block
                continue

            if current_block_size > MAX_BLOCK_SIZE_BYTES:
                p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Velikost bloku #{current_block.index} ({current_block_size} bajtů) překračuje maximální povolenou velikost {MAX_BLOCK_SIZE_BYTES} bajtů.{Style.RESET_ALL}")
                return False, None
            if current_block.chain_id != CHAIN_ID:
                p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Neplatné chain_id u bloku #{current_block.index}.{Style.RESET_ALL}")
                return False, None
            if current_block.version != BLOCK_VERSION:
                p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Neplatná verze bloku #{current_block.index}.{Style.RESET_ALL}")
                return False, None
            if current_block.hash != current_block.compute_hash():
                return False, None
            if current_block.previous_hash != previous_block.hash:
                return False, None
            if current_block.index != previous_block.index + 1:
                p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Návaznost indexů přerušena u bloku #{current_block.index}.{Style.RESET_ALL}")
                return False, None

            # OPRAVA F-05: chybějící blok v okně = odmítnutí, ne fail-open.
            try:
                median_time_past = self.get_median_time_past(current_block.index, chain_dict=chain_window, conn=okno_conn)
                expected_target = self.calculate_expected_target(current_block.index, chain_dict=chain_window, conn=okno_conn)
            except MissingChainDataError as e:
                p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: {e}{Style.RESET_ALL}")
                return False, None

            if not current_block.is_valid_timestamp(median_time_past):
                p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Timestamp bloku #{current_block.index} v řetězci je neplatný.{Style.RESET_ALL}")
                return False, None
                
            if current_block.target != expected_target:
                p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Nesprávný target bloku #{current_block.index}.{Style.RESET_ALL}")
                return False, None
            # ZMĚNA 5 (názvosloví): "Transaction root" místo "Merkle root",
            # viz obsáhlý komentář u téže kontroly v add_block().
            if current_block.merkle_root != compute_merkle_root(current_block.transactions):
                p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Nesprávný Transaction root v bloku #{current_block.index}.{Style.RESET_ALL}")
                return False, None
            if not self.meets_difficulty(current_block.hash, current_block.target):
                return False, None
            if any(tx.data is not None for tx in current_block.transactions):
                p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Nepovolená zpráva v bloku mimo genesis #{current_block.index}.{Style.RESET_ALL}")
                return False, None

            coinbase_txs = [tx for tx in current_block.transactions if tx.from_address == "COINBASE"]
            if len(coinbase_txs) != 1:
                p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Nesprávný počet coinbase transakcí v bloku #{current_block.index} (očekávána 1).{Style.RESET_ALL}")
                return False, None
            if current_block.transactions[0].from_address != "COINBASE":
                p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Coinbase transakce musí být první v bloku #{current_block.index}.{Style.RESET_ALL}")
                return False, None

            coinbase_tx = coinbase_txs[0]

            # OPRAVA D-11: stejné pravidlo jako v add_block() a validate_fork().
            # Musí být ve všech třech, jinak by uzel blok odmítl při přímém
            # příjmu, ale přijal ho jako součást forku - consensus split.
            if coinbase_tx.fee != 0:
                p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Coinbase transakce v bloku #{current_block.index} musí mít nulový poplatek (má {coinbase_tx.fee}).{Style.RESET_ALL}")
                return False, None

            # OPRAVA F-09: coinbase nesmí nést libovolná data v public_key ani
            # v signature. Třetí ze tří míst - pravidlo musí být všude stejné.
            if coinbase_tx.public_key is not None or coinbase_tx.signature is not None:
                p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Coinbase transakce v bloku #{current_block.index} musí mít prázdné public_key i signature.{Style.RESET_ALL}")
                return False, None

            # Stejné pravidlo jako v add_block() a validate_fork():
            # nonce coinbase = výška bloku.
            if coinbase_tx.nonce != current_block.index:
                p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Nonce coinbase transakce ({coinbase_tx.nonce}) v bloku #{current_block.index} neodpovídá výšce bloku.{Style.RESET_ALL}")
                return False, None

            halvings = current_block.index // HALVING_INTERVAL_BLOCKS
            expected_reward = subsidy_po_halvingu(halvings)
            expected_reward = max(0, min(expected_reward, MAX_SUPPLY - state.total_supply))
                
            total_fees = sum(tx.fee for tx in current_block.transactions if tx.from_address != "COINBASE")
            if coinbase_tx.amount != expected_reward + total_fees:
                p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Nesprávná coinbase odměna v bloku #{current_block.index}.{Style.RESET_ALL}")
                return False, None

            block_tx_ids = set()
            block_nonce_map = {}
            for tx in current_block.transactions:
                if not isinstance(tx.amount, int) or not isinstance(tx.fee, int) or not isinstance(tx.nonce, int):
                    p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Hodnoty amount, fee a nonce musí být celá čísla.{Style.RESET_ALL}")
                    return False, None
                if tx.timestamp > current_block.timestamp + 7200:
                    p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Transakce má čas příliš v budoucnosti.{Style.RESET_ALL}")
                    return False, None
                # OPRAVA D-12: spodní mez času transakce. Blok ji měl
                # (timestamp >= GENESIS_TIMESTAMP), transakce ne - transakce
                # s timestamp = 1 prošla všemi třemi validátory. Genesis
                # transakce má stejně vyžadovanou přesnou rovnost, takže
                # kolize nehrozí.
                if tx.timestamp < GENESIS_TIMESTAMP:
                    p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Transakce {tx.tx_id} má čas před genesis blokem.{Style.RESET_ALL}")
                    return False, None
                if tx.chain_id != CHAIN_ID:
                    p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Transakce má nesprávné chain_id.{Style.RESET_ALL}")
                    return False, None
                if not is_valid_address(tx.to_address):
                    p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Neplatný formát adresy příjemce ({tx.to_address}) v bloku #{current_block.index}.{Style.RESET_ALL}")
                    return False, None
                if tx.tx_id in block_tx_ids:
                    p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Duplicitní TX ID {tx.tx_id} v bloku #{current_block.index}.{Style.RESET_ALL}")
                    return False, None
                    
                block_tx_ids.add(tx.tx_id)
                
                if tx.from_address != "COINBASE":
                    if tx.amount <= 0:
                        p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Částka transakce musí být větší než 0.{Style.RESET_ALL}")
                        return False, None
                    if tx.amount < MIN_TX_AMOUNT:
                        p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Částka transakce je příliš malá.{Style.RESET_ALL}")
                        return False, None
                    # OPRAVA #6b: jen dolní mez, stejně jako v add_block().
                    if tx.fee < TX_FEE_MIN:
                        p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Poplatek transakce je nižší než minimum.{Style.RESET_ALL}")
                        return False, None
                    # OPRAVA #6d: třetí a poslední místo, kde musí pravidlo platit.
                    if tx.from_address == tx.to_address:
                        p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Transakce na vlastní adresu není povolena.{Style.RESET_ALL}")
                        return False, None
                    if tx.from_address in block_nonce_map:
                        if tx.nonce in block_nonce_map[tx.from_address]:
                            p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Duplicitní nonce {tx.nonce} pro adresu {tx.from_address} v bloku #{current_block.index}.{Style.RESET_ALL}")
                            return False, None
                        block_nonce_map[tx.from_address].add(tx.nonce)
                    else:
                        block_nonce_map[tx.from_address] = {tx.nonce}
                        
                if not tx.verify_sender_identity() and tx.from_address != "COINBASE":
                    return False, None
                # OPRAVA A-6: pod nejvyšším checkpointem se podpisy neověřují -
                # obsah těch bloků už zavazuje hashový řetězec vedoucí ke
                # checkpointu, který je součástí binárky. Identita odesílatele
                # (verify_sender_identity, tedy shoda adresy s veřejným klíčem)
                # se kontroluje dál: je to jen hash, ne křivka, a stojí skoro nic.
                if overit_podpisy and not tx.verify_signature() and tx.from_address != "COINBASE":
                    return False, None

            for sender, nonces_in_block in block_nonce_map.items():
                # OPRAVA F-08: dřív max() nad množinou VŠECH dosavadních nonce
                # dané adresy, tedy O(k) při každém dalším bloku. Nonce jsou
                # vynucené striktně posloupné, takže poslední hodnota stačí.
                expected_nonce = nonce_last_seen.get(sender, -1) + 1
                for tx_nonce in sorted(nonces_in_block):
                    if tx_nonce != expected_nonce:
                        p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Neplatná posloupnost nonce {tx_nonce} pro adresu {sender} v bloku #{current_block.index} (očekávána přesně {expected_nonce}).{Style.RESET_ALL}")
                        return False, None
                    expected_nonce += 1
                nonce_last_seen[sender] = expected_nonce - 1

            # Kontrola dostatečnosti zůstatku PŘED aplikací bloku na stav. Čte se
            # ze stavu naakumulovaného přes předchozí bloky (state.balance_map),
            # samotná mutace (maturace immature reward, odečty/připsání částek,
            # nonce_map, total_supply, cumulative_work) proběhne až níže přes
            # update_state_with_block, a to pouze pokud tato kontrola projde.
            target_index = current_block.index - COINBASE_MATURITY
            pending_mature_amount = 0
            if target_index in state.immature_rewards:
                pending_mature_amount = state.immature_rewards[target_index]['amount']
                pending_mature_address = state.immature_rewards[target_index]['address']

            temp_balance_changes = defaultdict(int)
            if target_index in state.immature_rewards:
                temp_balance_changes[pending_mature_address] += pending_mature_amount

            for tx in current_block.transactions:
                if tx.from_address != "COINBASE":
                    current_balance = state.balance_map.get(tx.from_address, 0) + temp_balance_changes[tx.from_address]
                    if current_balance < tx.amount + tx.fee:
                        p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Nedostatečný zůstatek pro transakci {tx.tx_id} od {tx.from_address} v bloku #{current_block.index}.{Style.RESET_ALL}")
                        return False, None
                    temp_balance_changes[tx.from_address] -= (tx.amount + tx.fee)
                    temp_balance_changes[tx.to_address] += tx.amount

            # OPRAVA B-1: tohle volání bylo jako jediné ze tří MIMO try. V
            # add_block() i v mine() je totéž volání uvnitř try/except ValueError,
            # tady ne - a encode_account() ValueError umí vyhodit (záporný
            # zůstatek, zůstatek nad MAX_SUPPLY). Dnes je to nedosažitelné,
            # protože kontrola zůstatků o pár řádků výš to pokrývá, jenže
            # is_valid_chain() se volá z load_data(), a to kolem ní try nemá:
            # uzel by spadl s tracebackem místo záchranného menu z OPRAVY F-14.
            # Kontrakt téhle metody je "vrať (False, None)", ne "vyhoď".
            try:
                self.update_state_with_block(current_block, state_target=state)
                expected_state_root = compute_state_root_from(state)
            # OPRAVA G-02: struct.error doplněn jako pojistka. Rozsahové kontroly v encode_account() by ji už neměly připustit, ale kontrakt "ven jde vždy ValueError" musí platit bezvýhradně.
            except (ValueError, struct.error) as e:
                p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Neplatný stav po bloku #{current_block.index} ({e}).{Style.RESET_ALL}")
                return False, None
            if current_block.state_root != expected_state_root:
                p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Nesprávný state root bloku #{current_block.index} (očekáván {expected_state_root}, v bloku {current_block.state_root}).{Style.RESET_ALL}")
                return False, None

            previous_block = current_block

        # OPRAVA D-10: nad PRÁZDNOU databází se smyčka výše neprovedla ani
        # jednou a funkce došla rovnou sem - řetězec bez genesis bloku byl tedy
        # formálně "platný", a to včetně vráceného stavu
        # {'total_supply': 0, 'cumulative_work': 0}. Volající pak dostal stav,
        # nad kterým get_last_block() vrací None a get_target() spadne na
        # AttributeError. V ostrém startu to o dva kroky dál zachytí
        # verify_genesis_block() (OPRAVA #17), takže praktický dopad byl malý,
        # ale je to porušený kontrakt funkce, na kterou se spoléhá i
        # replace_chain() - a OPRAVA #2 řeší přesně sousední případ (řetězec
        # nezačínající nulou). Prázdný vstup je nově chyba.
        if previous_block is None:
            p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: řetězec je prázdný.{Style.RESET_ALL}")
            return False, None

        state_dict = {
            'balance_map': state.balance_map,
            'nonce_map': state.nonce_map,
            'total_supply': state.total_supply,
            'cumulative_work': state.cumulative_work,
            'immature_rewards': state.immature_rewards,
            # Přidáno navíc oproti původnímu state_dict, aby load_data() při startu
            # uzlu nemusela po validaci volat ještě rebuild_state() pro druhý
            # průchod řetězcem jen kvůli undo_logs/state_checkpoints. Volající kód,
            # který čte jen původní klíče (replace_chain), je tímto nedotčen.
            'undo_logs': state.undo_logs,
            'state_checkpoints': state.state_checkpoints,
            # OPRAVA F-03: strom postavený během validace se předává dál,
            # aby ho load_data() ani replace_chain() nemusely stavět znovu.
            'accounts_smt': _state_smt(state),
            # OPRAVA Y-4 (audit 14. 10. 2026, nález 4): výška a hash vrcholu
            # řetězce, ke kterému vrácený stav PATŘÍ. Bez toho si volající
            # nemá jak ověřit, že jeho představa o výšce odpovídá stavu, který
            # právě přebírá - a load_data() se v jedné chybové cestě rozešla
            # právě takhle (podrobně tam). Návaznost indexů od nuly si tahle
            # metoda vynucuje sama, takže index posledního bloku je skutečná
            # výška vrcholu, ne tvrzení odesílatele.
            'tip_index': previous_block.index,
            'tip_hash': previous_block.hash
        }
        return True, state_dict

    def get_confirmations_by_index(self, block_index):
        # Počet potvrzení bloku na dané výšce, VČETNĚ bloku samotného
        # (vrchol řetězce = 1). Volby 12 a 13 si tenhle vzorec dřív opisovaly
        # inline; musí zůstat totožný s reorg_depth ve validate_fork(), jinak
        # by se práh definitivnosti (CONFIRMATIONS_THRESHOLD) rozešel se
        # skutečností.
        #
        # Tohle je systém potvrzení č. 1 (definitivnost). Pro zrání coinbase se
        # NEPOUŽÍVÁ - to je systém č. 2, počítá bloky nad blokem (vrchol = 0)
        # a odpovídá jinému pravidlu konsenzu. Viz volba 14 a odvození
        # u CONFIRMATIONS_THRESHOLD.
        return self.max_block_index - block_index + 1

    def get_confirmations(self, block_hash):
        # OPRAVA L-3: spojení bez try/finally. Ze sítě dosažitelné není (volá se
        # z menu), ale netěsné spojení je netěsné spojení - a WAL soubor drží
        # otevřený deskriptor i po chybě, což na Termuxu není zadarmo.
        conn = None
        try:
            conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
            conn.execute("PRAGMA journal_mode=WAL;")
            c = conn.cursor()
            c.execute("SELECT block_index FROM blocks WHERE block_hash = ?", (block_hash,))
            row = c.fetchone()
        except sqlite3.Error as e:
            # OPRAVA S-7: try/finally bez except je táž třída jako Nález 2.
            # Dopad je tu nulový (volá se jen z menu a obecný except v menu to
            # zachytí), ale spoléhat na obranu v druhé linii je zbytečné.
            # Vrací se 0 jako u neznámého bloku; aby to nevypadalo jako
            # "blok není potvrzený", řekne se nahlas, že jde o chybu čtení.
            print(f"{Fore.RED}Počet potvrzení nelze zjistit: databázi nelze číst "
                  f"({type(e).__name__}: {e}).{Style.RESET_ALL}")
            return 0
        finally:
            if conn is not None:
                try:
                    conn.close()
                except Exception:
                    pass
        if row:
            block_index = row[0]
            return self.max_block_index - block_index + 1
        return 0

    def replace_chain(self, fork_index, new_blocks_data=None, hotove_bloky=None):
        # OPRAVA Z-2 (audit 15. 10. 2026, nález 2, 2/3): ocas forku smí přijít
        # dvěma způsoby a vždy právě jedním.
        #
        #   new_blocks_data - seznam DICTŮ ze sítě (handler response_full_chain).
        #                     Ten je shora omezený MAX_BATCH_BYTES, takže se do
        #                     objektů převede tady jako dosud.
        #   hotove_bloky    - seznam hotových Block objektů (process_sync_buffer).
        #                     Buffer může mít až MAX_SYNC_BUFFER_BYTES, a držet
        #                     z něj v paměti obě reprezentace naráz byla ta
        #                     měřená špička 195 MiB - viz komentář tamtéž.
        #
        # Tvarová branka níž platí pro obě cesty stejně; pro hotové bloky se jen
        # místo "je to dict" ptá "je to Block". Kontrakt metody se nemění: nad
        # jakýmkoli vstupem vrací True/False a nikdy nevyhazuje.
        #
        # OPRAVA F-11: kontrola tvaru vstupu JEŠTĚ PŘED zabráním zámku. Funkce
        # je dosažitelná ze sítě přes 'response_full_chain' a neměla žádný
        # except - jen finally. Ověřeno auditem: data = 42 -> TypeError,
        # {'a': 1} -> ValueError, ['ahoj'] -> ValueError, [None] -> ValueError,
        # vše ven z funkce. Navíc prázdný seznam u fork_index == tip+1 vedl na
        # IndexError při new_chain_tail[-1] níž.
        # OPRAVA G-11: `global p2p_node` tu bylo zbytečně - deklarace je nutná jen při PŘIŘAZENÍ, ne při čtení. Odstraněno.

        def _reject(duvod):
            if 'p2p_node' in globals() and p2p_node is not None and hasattr(p2p_node, 'add_log'):
                p2p_node.add_log(f"{Fore.RED}replace_chain zamítnut: {duvod}{Style.RESET_ALL}")
            else:
                print(f"{Fore.RED}replace_chain zamítnut:{Style.RESET_ALL} {duvod}")
            return False

        if isinstance(fork_index, bool) or not isinstance(fork_index, int) or fork_index < 0:
            return _reject("fork_index musí být nezáporné celé číslo.")
        # OPRAVA Z-2 (nález 2): právě jeden ze dvou vstupů. Obojí naráz ani nic
        # z toho jsou chyba volajícího, ne stav, který by se měl tiše urovnat.
        if (new_blocks_data is None) == (hotove_bloky is None):
            return _reject("zadej právě jeden z parametrů new_blocks_data / hotove_bloky.")
        vstup = new_blocks_data if hotove_bloky is None else hotove_bloky
        ocekavany_typ = dict if hotove_bloky is None else Block
        if not isinstance(vstup, list):
            return _reject("vstup není seznam bloků.")
        if not vstup:
            # Prázdný ocas nemůže nikdy vyhrát a new_chain_tail[-1] by na něm
            # spadl na IndexError.
            return _reject("prázdný seznam bloků.")
        if len(vstup) > MAX_REORG_DEPTH + 1:
            return _reject(f"seznam bloků delší než MAX_REORG_DEPTH ({MAX_REORG_DEPTH}).")
        if not all(isinstance(b, ocekavany_typ) for b in vstup):
            return _reject("seznam obsahuje položku, která není blok.")

        if not self.lock.acquire(timeout=5):
            print(f"{Fore.RED}System is busy (lock timeout). Try again later.{Style.RESET_ALL}")
            return False
        try:
            # OPRAVA AUDIT-3: chyběla horní mez - kontrolovalo se jen
            # fork_index >= 0. Pro nesmyslně velkou hodnotu vyšla reorg_depth
            # ZÁPORNÁ, prošla tedy limitem MAX_REORG_DEPTH, prefix_work se
            # rovnala celkové práci řetězce a new_cum_work proto vždy převýšila
            # současnou. Výsledek byl nakonec správný (fork se odmítl), ale
            # cestou validate_fork -> is_valid is None -> fallback to stálo
            # přesně jednu PLNOU revalidaci od genesis, lineární v délce
            # řetězce. Naměřeno pro fork_index 10^6 i 2^40.
            #
            # fork_index == max_block_index + 1 je legitimní (čisté prodloužení
            # vrcholu bez reorgu, viz OPRAVA F-11 výš), cokoli nad tím znamená
            # díru mezi vrcholem a začátkem navrhovaného ocasu.
            #
            # Ze sítě to dnes nedosáhnete - handler response_blocks dávku bez
            # známého rodiče zahodí dřív. Je to obrana v druhé linii, na kterou
            # se kód jinde výslovně odmítá spoléhat (viz OPRAVA #4 a D-15).
            if fork_index > self.max_block_index + 1:
                return _reject(f"fork_index {fork_index} je nad vrcholem řetězce (#{self.max_block_index}).")

            reorg_depth = self.max_block_index - fork_index + 1
            if reorg_depth > MAX_REORG_DEPTH:
                if 'p2p_node' in globals() and hasattr(p2p_node, 'add_log'):
                    p2p_node.add_log(f"{Fore.RED}Reorg zamítnut: hloubka {reorg_depth} překračuje limit MAX_REORG_DEPTH ({MAX_REORG_DEPTH}).{Style.RESET_ALL}")
                return False

            # OPRAVA F-11: Block.from_dict() vyhazuje ValueError/KeyError/TypeError
            # nad nedůvěryhodnými daty; ani jedno se tu dřív nechytalo.
            # OPRAVA Z-2 (nález 2): hotové bloky se nepřevádějí podruhé. Jsou to
            # TYTÉŽ objekty, jaké by tahle řádka vyrobila - process_sync_buffer()
            # je staví stejným Block.from_dict() nad stejnými daty, jen o jednu
            # vrstvu dřív a s uvolněním syrového dictu po každém řádku.
            if hotove_bloky is not None:
                new_chain_tail = hotove_bloky
            else:
                try:
                    new_chain_tail = [Block.from_dict(b) for b in new_blocks_data]
                except (ValueError, KeyError, TypeError, struct.error, OverflowError) as e:
                    return _reject(f"blok nelze deserializovat ({type(e).__name__}: {e}).")
            
            current_cum_work = self.get_cumulative_work()
            current_length = self.max_block_index + 1
            
            prefix_work = self.get_cumulative_work(up_to_index=fork_index - 1) if fork_index > 0 else 0
            tail_work = sum(((1 << 256) // b.target if b.target > 0 else 0) for b in new_chain_tail)
            new_cum_work = prefix_work + tail_work
            new_length = fork_index + len(new_chain_tail)
            
            if new_cum_work < current_cum_work:
                return False
            elif new_cum_work == current_cum_work:
                if new_length < current_length:
                    return False
                elif new_length == current_length:
                    if new_chain_tail[-1].hash >= self.get_last_block().hash:
                        return False
            
            if fork_index == 0:
                def proposed_chain_iterator():
                    for b in new_chain_tail: yield b
                # OPRAVA A-02: vrchol navrhovaného řetězce. Návaznost indexů od
                # nuly si is_valid_chain() vynucuje sama, takže index posledního
                # bloku je skutečná výška vrcholu - nejde o tvrzení odesílatele,
                # které by šlo nafouknout bez poslání odpovídajících bloků.
                is_valid, new_state = self.is_valid_chain(
                    chain_iterable=proposed_chain_iterator(),
                    vrchol_index=new_chain_tail[-1].index if new_chain_tail else None)
                # OPRAVA M-1: undo_logy se tu zahazovaly, přestože je
                # is_valid_chain() PRÁVĚ SPOČÍTALA a vrací je ve state_dict
                # (viz OPRAVA, která sloučila dva průchody řetězcem do jednoho).
                # Prázdný slovník znamená, že get_state_at(vrchol-1) vrátí None,
                # validate_fork() pak pro KAŽDÝ další fork vrátí is_valid = None
                # ("nevím") a spustí se plná revalidace od genesis včetně všech
                # podpisů - tedy přesně to, co OPRAVA D-16 odstraňovala, a to
                # v okamžiku hned po plné synchronizaci, kdy je uzel nejzranitelnější.
                # Navíc do příchodu dalšího bloku není možný mini-reorg na vrcholu.
                new_undo_logs = new_state.get('undo_logs', {}) if new_state else {}
            else:
                is_valid, new_state, new_undo_logs = self.validate_fork(fork_index, new_chain_tail)
                # OPRAVA D-16: fallback JEN na "nevím" (is_valid is None).
                # Rozlišení `is None` musí zůstat explicitní - False i None jsou
                # obě nepravdivé, takže `not is_valid` by fallback spustilo zas
                # pro oba případy a oprava by byla zpátky na začátku.
                if is_valid is None:
                    if 'p2p_node' in globals() and p2p_node is not None and hasattr(p2p_node, 'add_log'):
                        p2p_node.add_log(
                            f"{Fore.YELLOW}Výchozí stav pro fork od #{fork_index} nelze sestavit, "
                            f"ověřuji celý řetězec od genesis.{Style.RESET_ALL}")
                    def proposed_chain_iterator():
                        # OPRAVA V-1 (audit 3. 10. 2026, nález 1): spojení leželo
                        # mimo try/finally a conn.close() bylo obyčejným řádkem za
                        # smyčkou. Přeskočily ho DVĚ cesty:
                        #   - výjimka z json.loads() nebo Block.from_dict() nad
                        #     poškozeným řádkem vlastní DB,
                        #   - PŘEDČASNÝ RETURN konzumenta: _is_valid_chain_inner()
                        #     vrací (False, None) u prvního vadného bloku, takže
                        #     generátor zůstal viset na yieldu a za něj se kód už
                        #     nikdy nedostal.
                        #
                        # Je to doslova týž nález, který OPRAVA R-2 vyřešila
                        # v get_iterable() uvnitř _is_valid_chain_inner() - sem se
                        # tehdy nedostala. Cesta je dosažitelná ze sítě
                        # (response_blocks -> process_sync_buffer -> replace_chain)
                        # a spustí se, kdykoli validate_fork() vrátí "nevím".
                        # Naměřeno: 42 deskriptorů po 20 voláních, tedy 2,1 na
                        # volání (soubor + WAL); uvolní je až cyklický GC.
                        conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
                        try:
                            conn.execute("PRAGMA journal_mode=WAL;")
                            c = conn.cursor()
                            c.execute("SELECT block_index, timestamp, transactions, previous_hash, target_hex, nonce, block_hash, merkle_root, version, chain_id, state_root FROM blocks WHERE block_index < ? ORDER BY block_index", (fork_index,))
                            for row in c:
                                yield Block.from_dict({
                                    'index': row[0], 'timestamp': row[1], 'transactions': json.loads(row[2]),
                                    'previous_hash': row[3], 'target': row[4], 'nonce': row[5], 'hash': row[6],
                                    'merkle_root': row[7], 'version': row[8], 'chain_id': row[9], 'state_root': row[10]
                                })
                        finally:
                            try:
                                conn.close()
                            except Exception:
                                pass
                        for b in new_chain_tail: yield b
                    # OPRAVA A-02: viz větev fork_index == 0 výš. Iterátor
                    # vydá bloky z DB pod forkem a pak celý navrhovaný ocas,
                    # takže vrchol je index posledního bloku ocasu.
                    is_valid, new_state = self.is_valid_chain(
                        chain_iterable=proposed_chain_iterator(),
                        vrchol_index=new_chain_tail[-1].index if new_chain_tail else None)
                    # OPRAVA M-1 (druhé místo, fallback při is_valid is None):
                    # týž případ jako výš. Undo logy pod fork_index zůstávají
                    # platné (bloky pod forkem jsou oběma větvím společné),
                    # takže se níž na ř. ~4650 jen doplní zbytek.
                    new_undo_logs = new_state.get('undo_logs', {}) if new_state else {}
            
            if not is_valid:
                # OPRAVA D-16: dřív se zamítalo tiše, takže v logu nešlo odlišit
                # "fork je neplatný" od "sem se výpočet vůbec nedostal".
                return _reject(f"navrhovaný fork od #{fork_index} neprošel ověřením.")

            # OPRAVA A-2 (1/3): zápis nového řetězce do DB neměl žádné ošetření.
            # replace_chain() má jen try/finally, takže OperationalError (disk
            # full, database is locked) i ValueError z Transaction.from_dict()
            # nad poškozeným lokálním záznamem prošly celou funkcí ven - přes
            # process_sync_buffer() až do _store_fork_batch(), kde se z nich
            # stal 24hodinový ban poctivé protistrany za chybu NAŠEHO disku.
            # Nově: transakce se vrátí zpět, vrací se False, a protože se paměť
            # mění až za tímto blokem, je stav uzlu netknutý.
            conn = None
            orphaned_transactions = []
            try:
                conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
                conn.execute("PRAGMA journal_mode=WAL;")
                c = conn.cursor()

                if fork_index <= self.max_block_index:
                    c.execute("SELECT block_index, transactions FROM blocks WHERE block_index >= ? ORDER BY block_index", (fork_index,))
                    new_tx_ids = set(tx.tx_id for block in new_chain_tail for tx in block.transactions)

                    # OPRAVA Z-2 (audit 15. 10. 2026, nález 2, 3/3): opouštěné
                    # bloky se STREAMUJÍ a recyklované transakce mají rozpočet.
                    #
                    # Dřív tu stálo `for row in c.fetchall()`, tedy materializace
                    # VŠECH opouštěných bloků (až MAX_REORG_DEPTH), a z každé
                    # jejich transakce se stavěl objekt do orphaned_transactions
                    # bez jakékoli meze. Naměřeno na 100 plných blocích: +287 MiB
                    # a 3,7 s, tedy 2,9 MiB a 37 ms na blok -> při MAX_REORG_DEPTH
                    # 2,8 GiB a 37 s. To je větší špička než celý sync buffer,
                    # a je dosažitelná ZCELA LEGITIMNĚ: 1001 malých bloků (přesně
                    # to, na co je MAX_SYNC_BUFFER_BYTES dimenzované) přebije
                    # 1000 našich plných, protože práce se počítá z targetu, ne
                    # z velikosti.
                    #
                    # Rozpočet je odvozený, ne zvolený: mempool má strop
                    # MAX_MEMPOOL_SIZE_BYTES, takže víc recyklovaných transakcí
                    # by se do něj stejně nevešlo - add_transaction() by je
                    # odmítla nebo vytěsnila (OPRAVA D-03). Držet jich v paměti
                    # 2,8 GiB kvůli 10MiB mempoolu nedává smysl.
                    #
                    # Které transakce se při vyčerpání rozpočtu zahodí, NENÍ
                    # jedno: zachovává se přirozené pořadí od NEJSTARŠÍHO
                    # opouštěného bloku, takže ponechané transakce tvoří PREFIX
                    # posloupnosti nonce každého odesílatele. Opačné pořadí by
                    # vyrobilo díry a add_transaction() by je odmítla tak jako
                    # tak (viz _prune_mempool_sequences).
                    #
                    # Transakce nad rozpočtem se ani NEPARSUJÍ - coinbase se
                    # pozná ze syrového dictu, takže odpadá i sha3 tx_id a
                    # json.dumps v get_size() na každou z nich.
                    rozpocet_recyklace = MAX_MEMPOOL_SIZE_BYTES
                    recyklovano_bajtu = 0
                    vynechano_tx = 0
                    zaniklo_coinbase = 0
                    for row in c:
                        local_block_index = row[0]
                        local_transactions = json.loads(row[1])
                        for tx_data in local_transactions:
                            if not isinstance(tx_data, dict):
                                continue
                            if tx_data.get('from_address') == "COINBASE":
                                zaniklo_coinbase += 1
                                # Jednotlivě jen u mělkého reorgu. Hluboký by do
                                # logu nasypal až 1000 řádků a vytlačil z něj
                                # všechno ostatní (MAX_P2P_LOG_ENTRIES); souhrn
                                # je níž.
                                if reorg_depth <= 10:
                                    p2p_log(f"{Fore.YELLOW}COINBASE transakce {tx_data.get('tx_id')} z osiřelého bloku #{local_block_index} zanikla (přirozené chování).{Style.RESET_ALL}")
                                continue
                            if recyklovano_bajtu >= rozpocet_recyklace:
                                vynechano_tx += 1
                                continue
                            tx = Transaction.from_dict(tx_data)
                            if tx.tx_id in new_tx_ids:
                                continue
                            velikost = tx.get_size()
                            if recyklovano_bajtu + velikost > rozpocet_recyklace:
                                # Rozpočet je vyčerpaný; další transakce se už
                                # nebudou ani parsovat.
                                recyklovano_bajtu = rozpocet_recyklace
                                vynechano_tx += 1
                                continue
                            recyklovano_bajtu += velikost
                            orphaned_transactions.append(tx)

                    if zaniklo_coinbase and reorg_depth > 10:
                        p2p_log(f"{Fore.YELLOW}REORG: zaniklo {zaniklo_coinbase} coinbase odměn z opouštěných bloků #{fork_index}-#{self.max_block_index} (přirozené chování).{Style.RESET_ALL}")
                    if vynechano_tx:
                        p2p_log(
                            f"{Fore.YELLOW}REORG: {vynechano_tx} transakcí z opouštěných bloků se "
                            f"nerecykluje - rozpočet {rozpocet_recyklace // 1024} kB (velikost mempoolu) "
                            f"je vyčerpaný. Doteče běžným rozesíláním a synchronizací mempoolu."
                            f"{Style.RESET_ALL}")

                    if reorg_depth > 0:
                        p2p_log(
                            f"{Fore.MAGENTA}REORG: hloubka {reorg_depth} bloků "
                            f"(fork od bloku #{fork_index}, "
                            f"opouštím staré bloky do #{self.max_block_index}).{Style.RESET_ALL}"
                        )

                c.execute("DELETE FROM blocks WHERE block_index >= ?", (fork_index,))
                c.execute("DELETE FROM transactions WHERE block_index >= ?", (fork_index,))
                for block in new_chain_tail:
                    transactions_json = json.dumps([tx.to_dict() for tx in block.transactions])
                    target_hex = hex(block.target)[2:]
                    c.execute("INSERT INTO blocks (block_index, timestamp, transactions, previous_hash, target_hex, nonce, block_hash, merkle_root, version, chain_id, state_root) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)",
                              (block.index, block.timestamp, transactions_json, block.previous_hash, target_hex, block.nonce, block.hash, block.merkle_root, block.version, block.chain_id, block.state_root))
                    for tx in block.transactions:
                        c.execute("INSERT INTO transactions (tx_id, block_index) VALUES (?, ?)", (tx.tx_id, block.index))
                conn.commit()
            except Exception as e:
                if conn is not None:
                    try:
                        conn.rollback()
                    except Exception:
                        pass
                return _reject(f"zápis nového řetězce do databáze selhal ({type(e).__name__}: {e}); stav uzlu zůstal nezměněn.")
            finally:
                if conn is not None:
                    try:
                        conn.close()
                    except Exception:
                        pass

            # OPRAVA A-2 (2/3): self.chain se dřív načítala z DB SAMOSTATNÝM
            # spojením AŽ PO přiřazení balance_map, nonce_map, total_supply,
            # cumulative_work i max_block_index. Selhalo-li to čtení, zůstal
            # self.chain na staré větvi, zatímco max_block_index ukazoval na
            # novou. Důsledky: get_last_block() vracel blok #10, ale stav i DB
            # byly na #11; mine() by vytěžil blok #12 navazující na #10 (síť ho
            # odmítne a celé kolo PoW je pryč) a add_block() by čekal na blok
            # #11, který už v DB i ve stavu je - jeho přijetí by stav aplikovalo
            # podruhé.
            #
            # Nový self.chain se proto skládá z dat, která už jsou v paměti:
            # starý prefix pod fork_indexem + new_chain_tail. Žádné I/O, takže
            # se přiřadí spolu se zbytkem stavu a rozejít se nemají jak.
            nova_chain = [b for b in self.chain if b.index < fork_index] + list(new_chain_tail)
            if len(nova_chain) > LAST_BLOCKS_TO_KEEP:
                nova_chain = nova_chain[-LAST_BLOCKS_TO_KEEP:]

            self.balance_map = new_state['balance_map']
            self.nonce_map = new_state['nonce_map']
            self.total_supply = new_state['total_supply']
            self.cumulative_work = new_state['cumulative_work']
            self.immature_rewards = new_state.get('immature_rewards', {})
            # OPRAVA F-03: strom MUSÍ jít se stavem. Kdyby tu zůstal ten starý,
            # ukazoval by na odpojenou větev a state root by po reorgu nesouhlasil.
            # Chybí-li (starší cesta bez stromu), postaví se znovu ze stavu.
            prevzaty_smt = new_state.get('accounts_smt')
            self.accounts_smt = (prevzaty_smt if prevzaty_smt is not None
                                 else build_accounts_smt(self.balance_map, self.nonce_map))
            self.chain = nova_chain
            self.max_block_index = new_length - 1

            if hasattr(self, 'undo_logs'):
                self.undo_logs = {k: v for k, v in self.undo_logs.items() if k < fork_index}
                if new_undo_logs:
                    self.undo_logs.update(new_undo_logs)
                while len(self.undo_logs) > LAST_BLOCKS_TO_KEEP:
                    del self.undo_logs[min(self.undo_logs.keys())]

            if hasattr(self, 'state_checkpoints'):
                # OPRAVA #19: checkpointy z odpojené větve zahodit, ale ty, které
                # validace nové větve právě spočítala, převzít. Dřív se zahodily
                # obojí (a validate_fork žádné ani nevyráběl), takže první
                # rebuild_state() po reorgu startoval od dávno starého bodu.
                self.state_checkpoints = {k: v for k, v in self.state_checkpoints.items() if k < fork_index}
                self.state_checkpoints.update(new_state.get('state_checkpoints', {}))
                checkpoint_keys = sorted(self.state_checkpoints.keys())
                while len(checkpoint_keys) > 5:
                    del self.state_checkpoints[checkpoint_keys.pop(0)]

            # Reorg na kratší (ale těžší) větev může okno v paměti zkrátit pod
            # LAST_BLOCKS_TO_KEEP. Doplnění z DB je čistě optimalizace, takže
            # smí selhat: kratší okno je legitimní stav a get_block() si
            # chybějící bloky dohledá v databázi. Rozhodně ale nesmí shodit
            # reorg, který už je zapsaný a promítnutý do stavu.
            zadouci_delka = min(LAST_BLOCKS_TO_KEEP, new_length)
            if len(self.chain) < zadouci_delka:
                conn = None
                try:
                    conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
                    conn.execute("PRAGMA journal_mode=WAL;")
                    c = conn.cursor()
                    c.execute("SELECT block_index, timestamp, transactions, previous_hash, target_hex, nonce, block_hash, merkle_root, version, chain_id, state_root FROM blocks WHERE block_index >= ? ORDER BY block_index", (max(0, self.max_block_index - LAST_BLOCKS_TO_KEEP + 1),))
                    # OPRAVA Z-2 (nález 2): kurzor se streamuje. fetchall() držel
                    # až LAST_BLOCKS_TO_KEEP syrových řádků (u plných bloků ~1,2 GB)
                    # SOUČASNĚ s objekty, které se z nich stavěly - táž dvojí
                    # reprezentace jako v process_sync_buffer(). Objekty samy
                    # jsou nevyhnutelné, je to obsah self.chain; syrové řádky
                    # vedle nich ne.
                    doplnene = [Block.from_dict({
                        'index': row[0], 'timestamp': row[1], 'transactions': json.loads(row[2]),
                        'previous_hash': row[3], 'target': row[4], 'nonce': row[5], 'hash': row[6],
                        'merkle_root': row[7], 'version': row[8], 'chain_id': row[9], 'state_root': row[10]
                    }) for row in c]
                    if len(doplnene) > len(self.chain) and doplnene and doplnene[-1].index == self.max_block_index:
                        self.chain = doplnene
                except Exception as e:
                    p2p_log(f"{Fore.YELLOW}Okno posledních bloků se nepodařilo doplnit z DB ({type(e).__name__}: {e}); pokračuji s kratším oknem.{Style.RESET_ALL}")
                finally:
                    if conn is not None:
                        try:
                            conn.close()
                        except Exception:
                            pass

            # OPRAVA A-2 (3/3): obnova mempoolu běží až ZA úspěšným reorgem.
            # Řetězec i stav už jsou nahrazené, takže selhání téhle části nesmí
            # znamenat "reorg neproběhl" - vrátit tu False by volajícího poslalo
            # zpátky pro data, která už máme. Chyba se proto zaloguje a reorg
            # se dokončí; nejhorší následek je transakce, která zůstane venku
            # a doteče příštím kolem synchronizace mempoolu.
            try:
                existing_mempool = self.unconfirmed_transactions
                self.unconfirmed_transactions = []

                all_pending = {tx.tx_id: tx for tx in existing_mempool}
                # OPRAVA #11: transakce z odpojených bloků si označíme, aby dostaly
                # allow_expired=True. Transakce, které v mempoolu jen ležely, se
                # posuzují normálně - jejich lhůta běžet nepřestala.
                orphaned_tx_ids = {tx.tx_id for tx in orphaned_transactions}
                for tx in orphaned_transactions:
                    all_pending[tx.tx_id] = tx

                combined_transactions = list(all_pending.values())
                combined_transactions.sort(key=lambda x: (x.from_address, x.nonce))

                # OPRAVA W-4 (audit 9. 10. 2026, nález N-4): jeden dávkový dotaz
                # na celou obnovu místo tří spojení na transakci. U hlubokého
                # reorgu se počty násobí délkou větve, takže tady to bolí ještě
                # víc než ve recycle_orphan_transactions() - a celé to běží pod
                # self.lock. Dotaz se dělá AŽ TEĎ, nad už nahrazeným řetězcem.
                try:
                    v_novem_retezci = self.tx_ids_in_chain([tx.tx_id for tx in combined_transactions])
                except Exception as e:
                    p2p_log(f"{Fore.YELLOW}Dávkový dotaz na duplicitní TX ID po reorgu selhal ({type(e).__name__}: {e}), pokračuji po jedné.{Style.RESET_ALL}")
                    v_novem_retezci = None

                for tx in combined_transactions:
                    if self.add_transaction(tx, allow_expired=(tx.tx_id in orphaned_tx_ids),
                                            chain_tx_ids=v_novem_retezci):
                        p2p_log(f"{Fore.GREEN}Osiřelá/čekající transakce {tx.tx_id} ponechána nebo přidána do mempoolu.{Style.RESET_ALL}")
                    else:
                        reason = self._duvod_zamitnuti_z_mempoolu(tx, v_novem_retezci, "v novém řetězci")
                        p2p_log(f"{Fore.RED}Transakce {tx.tx_id} zamítnuta z mempoolu po reorgu. Důvod: {reason}.{Style.RESET_ALL}")

                save_mempool(self.unconfirmed_transactions)
            except Exception as e:
                p2p_log(f"{Fore.YELLOW}Reorg proběhl, ale obnova mempoolu selhala ({type(e).__name__}: {e}). Řetězec je v pořádku.{Style.RESET_ALL}")
            return True
        except Exception as e:
            # OPRAVA A-2: pojistka pro cokoli, co se výše nechytlo. Bez ní
            # výjimka propadla přes process_sync_buffer() do _store_fork_batch(),
            # kde se z lokální chyby stal ban protistrany.
            return _reject(f"neočekávaná chyba při nahrazení řetězce ({type(e).__name__}: {e}).")
        finally:
            self.lock.release()

    def find_transaction_by_id(self, tx_id):
        for tx in self.unconfirmed_transactions:
            if tx.tx_id == tx_id:
                return tx, "Mempool"
        for block in self.chain:
            for tx in block.transactions:
                if tx.tx_id == tx_id:
                    return tx, f"Blok #{block.index}"
        
        # OPRAVA AUDIT-11: conn.close() leželo jako obyčejný řádek na konci
        # obou větví, takže ho každá výjimka přeskočila - přesně ten vzorec,
        # který OPRAVA L-3 a OPRAVA G-08 označily za chybu a odstranily jinde.
        # Sem se oprava tehdy nedostala. Stačil poškozený řádek ve sloupci
        # `transactions`: json.loads() vyhodil JSONDecodeError a spojení zůstalo
        # viset. Naměřeno 41 otevřených deskriptorů po 20 voláních (dva na
        # volání - samotný soubor plus WAL), zatímco kontrolní get_block_from_db()
        # se stejným vstupem uniká jediný. Po vyčerpání deskriptorů selže
        # i otevření SQLite jinde a uzel skončí v situaci popsané u OPRAVY N-2
        # (smyčka accept() se točila na 100 % CPU).
        #
        # Parsování se navíc přesunulo AŽ ZA close(): z databáze se jen vyzvednou
        # řádky, spojení se zavře a teprve pak se sahá na json.loads()
        # a Transaction.from_dict(). Výjimka z parsování tak nemá co uniknout.
        # Chování při poškozených datech se nemění - výjimka propadne volajícímu
        # (volba 12) stejně jako dřív a zachytí ji obecný handler v main().
        conn = None
        b_idx = None
        block_row = None
        try:
            conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
            conn.execute("PRAGMA journal_mode=WAL;")
            c = conn.cursor()
            c.execute("SELECT block_index FROM transactions WHERE tx_id = ?", (tx_id,))
            row = c.fetchone()
            if row:
                b_idx = row[0]
                c.execute("SELECT transactions FROM blocks WHERE block_index = ?", (b_idx,))
                block_row = c.fetchone()
        finally:
            if conn is not None:
                try:
                    conn.close()
                except Exception:
                    pass

        if block_row:
            transactions = json.loads(block_row[0])
            for tx_data in transactions:
                if tx_data['tx_id'] == tx_id:
                    return Transaction.from_dict(tx_data), f"Blok #{b_idx}"
        return None, None

def format_confirmations(count):
    # OPRAVA #15 (revidováno): práh se čte z CONFIRMATIONS_THRESHOLD místo
    # natvrdo zapsané tisícovky. `count < 1001` je totéž co původní
    # `count <= 1000`, chování se tedy nemění.
    # Zelená = blok je definitivní, tedy chráněný proti reorgu. Používají
    # volby 10, 11, 12 a 13. Zrání coinbase ve volbě 14 má vlastní, jiný systém
    # počítání potvrzení - viz odvození u CONFIRMATIONS_THRESHOLD.
    if count < CONFIRMATIONS_THRESHOLD:
        return f"{Fore.RED}{count}{Style.RESET_ALL}"
    else:
        return f"{Fore.GREEN}{count}{Style.RESET_ALL}"

def load_address_book(password):
    old_file = 'address_book.json'
    if os.path.exists(old_file) and password:
        try:
            with open(old_file, 'r') as f:
                address_book = json.load(f)
            save_address_book(address_book, password)
            os.remove(old_file)
            print(f"{Fore.GREEN}Adresář byl úspěšně migrován a zašifrován.{Style.RESET_ALL}")
            return address_book
        except Exception as e:
            print(f"{Fore.RED}Chyba při migraci starého adresáře: {e}{Style.RESET_ALL}")
            return {}
    if os.path.exists(ADDRESS_BOOK_FILE) and password:
        try:
            with open(ADDRESS_BOOK_FILE, 'rb') as f:
                data = f.read()
            salt = data[:16]
            nonce = data[16:28]
            ciphertext_and_tag = data[28:]
            # OPRAVA AUDIT-9: derivace nově vede přes sdílenou cache
            # derive_wallet_key(). Načtení musí použít sůl ZE SOUBORU, takže
            # tohle je plná derivace - naplní ale cache, takže následná
            # uložení adresáře (i peněženek) už Argon2id nepočítají vůbec.
            _, key = derive_wallet_key(password, salt)
            aesgcm = AESGCM(key)
            decrypted = aesgcm.decrypt(nonce, ciphertext_and_tag, None)
            return json.loads(decrypted.decode())
        except Exception:
            # OPRAVA G-11: 'as e' se nepoužívalo. Text výjimky se tu ZÁMĚRNĚ
            # nevypisuje - u chyby dešifrování by prozrazoval, jestli selhalo
            # heslo, nebo integrita souboru.
            print(f"{Fore.RED}Chyba při dešifrování adresáře (špatné heslo nebo poškozený soubor).{Style.RESET_ALL}")
            # OPRAVA AUDIT-8: dřív se jen vrátil prázdný slovník a první
            # přidání nebo smazání adresy pak zavolalo save_address_book() s {},
            # čímž původní soubor nevratně přepsalo. Ztracená data nejsou
            # kritická (adresář neobsahuje klíče), ale mizela bez druhého
            # dotazu. Nedešifrovatelný soubor se proto odkládá stranou, přesně
            # jak to dělá load_data() s poškozenou blockchain.db - když šlo jen
            # o překlep v hesle, uživatel ho přejmenuje zpátky.
            zaloha = f"{ADDRESS_BOOK_FILE}.invalid.{int(time.time())}"
            try:
                os.replace(ADDRESS_BOOK_FILE, zaloha)
                print(f"{Fore.YELLOW}Původní adresář odložen jako {zaloha}{Style.RESET_ALL}")
                print(f"{Fore.YELLOW}Pokračuji s prázdným adresářem. Pokud šlo jen o špatné heslo, přejmenujte soubor zpět na {ADDRESS_BOOK_FILE}.{Style.RESET_ALL}")
            except OSError as e:
                print(f"{Fore.RED}Adresář se nepodařilo odložit stranou ({e}).{Style.RESET_ALL}")
                print(f"{Fore.RED}Nepřidávejte ani nemažte adresy, dokud soubor nezálohujete - uložení by ho přepsalo.{Style.RESET_ALL}")
            return {}
    return {}

def save_address_book(address_book, password):
    try:
        data_json = json.dumps(address_book, indent=4).encode()
        # OPRAVA AUDIT-9: každé uložení dřív generovalo novou sůl a pouštělo
        # plnou derivaci Argon2id (64 MiB, 3 iterace, 4 lanes) - podle poznámky
        # u OPRAVY #5 to na ARM v Termuxu dělá 1-3 sekundy na jedno přidání
        # adresy a projeví se jako nevysvětlené zaseknutí menu. Peněženky mají
        # pro tentýž účel cache, adresář ne; tímhle se sjednocují.
        #
        # Klíč i sůl bere z derive_wallet_key(), tedy z téhož procesního cache
        # jako peněženky. Sůl se ukládá do hlavičky souboru, takže sdílení
        # s peněženkami nic nerozbíjí a každé uložení dostává vlastní náhodnou
        # nonce - AES-GCM tedy nikdy nešifruje dvakrát stejnou dvojicí.
        salt, key = derive_wallet_key(password)
        nonce = os.urandom(12)
        aesgcm = AESGCM(key)
        ciphertext_and_tag = aesgcm.encrypt(nonce, data_json, None)
        temp_file = ADDRESS_BOOK_FILE + '.tmp'
        with open(temp_file, 'wb') as f:
            f.write(salt + nonce + ciphertext_and_tag)
            f.flush()
            os.fsync(f.fileno())
        os.replace(temp_file, ADDRESS_BOOK_FILE)
    except Exception as e:
        print(f"{Fore.RED}Chyba při ukládání adresáře: {e}{Style.RESET_ALL}")
        if os.path.exists(ADDRESS_BOOK_FILE + '.tmp'):
            os.remove(ADDRESS_BOOK_FILE + '.tmp')

def normalize_ip_str(ip_str):
    # OPRAVA T-3 (Nález 3): kanonický tvar IP adresy. Bylo to dosud jen
    # P2PNode.normalize_ip(), ale potřebuje ho i load_blacklist() - a ta běží
    # dřív, než P2PNode vůbec vznikne. Druhá kopie téhož výpočtu by byla přesně
    # ten rozpor, kvůli kterému ban_peer() a is_blacklisted() nefungovaly
    # dohromady, takže metoda na P2PNode nově volá tuhle funkci.
    try:
        return str(ipaddress.ip_address(ip_str))
    except ValueError:
        return ip_str

def is_self_target_ip(ip_str):
    # OPRAVA T-4 (Nález 4): dřív to byl textový test proti seznamu
    # ['127.0.0.1', 'localhost', '::1', '0.0.0.0'] v connect_to_peer(). Rozepsaný
    # loopback ('0:0:0:0:0:0:0:1') v tom seznamu NENÍ, takže detekcí připojení
    # k sobě samému neprošel a zachytila ho až druhá linie (shoda node_id
    # v handshaku). Spoléhání na obranu v druhé linii si kód jinde výslovně
    # zakazuje (OPRAVA #4, D-15), tak ať to platí i tady.
    #
    # OPRAVA N4 (audit 10. 10. 2026, nález N4): funkce nově hlásí jen adresu,
    # která NEMŮŽE být cílem spojení - tedy nespecifikovanou ('0.0.0.0', '::'
    # i rozepsané tvary). Loopback ani 'localhost' sem už nepatří.
    #
    # Odmítat celý loopback bylo příliš široké: dva uzly na jednom stroji se
    # pak nedaly ručně propojit ani na různých portech. To si protiřečí
    # s OPRAVOU U-20, která tu topologii výslovně podporuje ("dva uzly na
    # jednom VPS, dvě instance za jedním NATem s různými porty") a kvůli které
    # se evidence překlíčovala na dvojici (IP, node_id). Ruční peering je
    # navíc dokumentovaná záchranná cesta z eclipse útoku
    # (PROTECTED_PEER_SLOTS), takže právě v téhle topologii nefungovalo to, co
    # má fungovat vždycky; vedlejším dopadem bylo, že nešlo postavit lokální
    # testovací síť, což je u projektu cíleného na Termux citelné.
    #
    # Skutečnou detekci spojení k sobě samému dělá connect_to_peer() porovnáním
    # DVOJICE (IP, port) a hlavně shoda node_id v handleru handshake, která si
    # i uklidí tabulku peerů. Tahle funkce je jen branka na nesmyslný cíl.
    try:
        ip = ipaddress.ip_address(ip_str)
    except ValueError:
        # 'localhost' a jiná jména nejsou IP adresa; cíl rozhodne až spojení
        # a porovnání (IP, port) ve volajícím.
        return False
    # is_unspecified pokrývá '0.0.0.0' i '::' (a jeho rozepsaný tvar).
    return ip.is_unspecified

def normalize_peer_list(peers):
    # OPRAVA T-4 (Nález 1): kanonizace celé tabulky peerů. T-3 normalizovala
    # blacklist, ale do self.peers a protected_peers se oprava nedostala - ty
    # dál držely syrový řetězec přesně tak, jak ho zadal uživatel (volba 16
    # v menu, peers.json). socket.accept() přitom vrací vždy kanonický tvar,
    # takže se týž hostitel dostal do tabulky DVAKRÁT: jednou rozepsaně
    # z ručního zadání, podruhé zkráceně z handshaku.
    #
    # Dopady byly čtyři: dvě místa v MAX_PEERS i v MAX_PEERS_PER_SUBNET pro
    # jediný uzel (tedy oslabená diverzita podsítí, kterou zavádí D-08 jako
    # obranu proti eclipse útoku), každý broadcast odeslaný témuž uzlu dvakrát,
    # nesmazatelný chráněný duplikát po volbě 17 a nerozpoznaná změna
    # naslouchacího portu v handshaku.
    #
    # Vrací (seznam, počet sloučených). Pořadí se zachovává a vyhrává první
    # výskyt - stejné pravidlo, jakým load_blacklist() slučuje dva zápisy téže
    # adresy. Jednorázová migrace peers.json není potřeba: normalizace při
    # načtení duplicity sloučí sama a nejbližší save_peers() zapíše čistý stav.
    out = []
    videne = set()
    slouceno = 0
    for ip, port in peers:
        klic = (normalize_ip_str(ip), port)
        if klic in videne:
            slouceno += 1
            continue
        videne.add(klic)
        out.append(klic)
    return out, slouceno

def load_blacklist():
    # OPRAVA #1: blacklist je nově slovník {ip: expirace}, kde None znamená
    # trvalý ban (ten uděluje jen uživatel ručně z menu). Starý formát byl
    # prostý seznam IP bez jakékoli expirace - ten načteme a zmigrujeme na
    # dočasné bany, aby se uzly zablokované kvůli chybě #1 samy uvolnily.
    if os.path.exists(BLACKLIST_FILE):
        try:
            with open(BLACKLIST_FILE, 'r') as f:
                raw = json.load(f)
            # OPRAVA T-3 (Nález 3): klíče se normalizují i při NAČÍTÁNÍ. Bez
            # toho by oprava v ban_peer()/is_blacklisted() uzavřela dosah jen
            # novým banům a ty už uložené v syrovém tvaru by se staly
            # nedosažitelnými - tedy přesně ten tichý výpadek, který nález
            # popisuje, jen obráceně. Týká se hlavně ručních trvalých banů,
            # protože ty jsou jediné, které mají soubor přežít.
            if isinstance(raw, list):
                now = time.time()
                print(f"{Fore.YELLOW}Blacklist ve starém formátu převeden na dočasné bany ({len(raw)} IP).{Style.RESET_ALL}")
                return {normalize_ip_str(str(ip)): now + BAN_DURATION_SECONDS for ip in raw}
            if isinstance(raw, dict):
                out = {}
                for ip, expiry in raw.items():
                    klic = normalize_ip_str(str(ip))
                    hodnota = None if expiry is None else float(expiry)
                    # Normalizace může sloučit dva zápisy téže adresy ('::1'
                    # a '0:0:0:0:0:0:0:1'). Platí totéž pravidlo jako
                    # v ban_peer(): trvalý ban vyhrává nad dočasným, jinak
                    # vyhrává ten delší.
                    if klic in out:
                        stary = out[klic]
                        if stary is None or hodnota is None:
                            out[klic] = None
                        else:
                            out[klic] = max(stary, hodnota)
                    else:
                        out[klic] = hodnota
                return out
        except Exception as e:
            print(f"{Fore.RED}Chyba při načítání blacklistu:{Style.RESET_ALL} {e}")
    return {}

def save_blacklist(blacklist):
    # OPRAVA G-06: vrací True/False. Volající (flush_blacklist) podle toho drží
    # nebo shazuje příznak 'dirty' - při neúspěšném zápisu se tedy o změnu
    # nepřijde a zkusí se znovu při dalším flushi.
    temp_file = BLACKLIST_FILE + '.tmp'
    try:
        with open(temp_file, 'w') as f:
            json.dump(dict(blacklist), f, indent=4)
            f.flush()
            os.fsync(f.fileno())
        os.replace(temp_file, BLACKLIST_FILE)
        return True
    except Exception as e:
        print(f"{Fore.RED}Chyba při ukládání blacklistu:{Style.RESET_ALL} {e}")
        if os.path.exists(temp_file):
            os.remove(temp_file)
        return False

def ensure_column(conn, table, column, coltype):
    # Obecná migrace: doplní chybějící sloupec do už existující tabulky.
    # Používá se pro lokální (nekonsenzuální) metadata, viz OPRAVA #11.
    try:
        c = conn.cursor()
        c.execute(f"PRAGMA table_info({table})")
        columns = [row[1] for row in c.fetchall()]
        if columns and column not in columns:
            c.execute(f"ALTER TABLE {table} ADD COLUMN {column} {coltype}")
            conn.commit()
            return True
    except Exception:
        pass
    return False

def ensure_state_root_column(conn, table='blocks'):
    # Migrace DB vytvořené ještě bez sloupce state_root. Staré bloky dostanou
    # NULL, takže je is_valid_chain() při startu odmítne - což je správně, jde
    # o konsenzuální změnu a takový řetězec už neplatí.
    try:
        c = conn.cursor()
        c.execute(f"PRAGMA table_info({table})")
        columns = [row[1] for row in c.fetchall()]
        if columns and 'state_root' not in columns:
            c.execute(f"ALTER TABLE {table} ADD COLUMN state_root TEXT")
            conn.commit()
            return True
    except Exception:
        pass
    return False

def save_data(droid_chain, wallets, password, peers, full=False, save_wallets=False):
    # OPRAVA #5: save_data() se volá z handleru new_block, tedy při KAŽDÉM bloku
    # ze sítě, a přepisovala do SQLite celý droid_chain.chain - až 1 200 bloků
    # i se všemi transakcemi. Přijetí jednoho bloku tak znamenalo O(1200)
    # databázových zápisů. Přitom add_block() i replace_chain() si svoje bloky
    # do DB zapisují samy, takže tenhle přepis byl čistě redundantní.
    #
    # full=True         -> zapiš celý řetězec (start uzlu, vytvoření genesis,
    #                      vypnutí - tam na pár set milisekundách nesejde)
    # full=False        -> dopiš jen bloky, které v DB ještě nejsou (běžně nula)
    # save_wallets=True -> ulož i peněženky (jen když se opravdu změnily;
    #                      jinak by se počítal Argon2id, resp. zbytečně
    #                      přepisoval soubor s klíči)
    # OPRAVA R-5: funkce nově vrací True/False. Dřív každou chybu jen vypsala,
    # takže volající neměl jak poznat, že se neuložilo nic - a menu na to
    # spoléhalo: volby 6 a 7 hlásí "Privátní klíč byl bezpečně uložen do
    # souboru" BEZ ohledu na výsledek. Při selhání zápisu existoval klíč jen
    # v paměti a po restartu zmizel i s prostředky, které na adresu mezitím
    # přišly.
    vse_ok = True
    conn = None
    try:
        with droid_chain.lock:
            conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
            conn.execute("PRAGMA journal_mode=WAL;")
            c = conn.cursor()
            c.execute('''
                CREATE TABLE IF NOT EXISTS blocks (
                    block_index INTEGER PRIMARY KEY,
                    timestamp INTEGER,
                    transactions TEXT,
                    previous_hash TEXT,
                    target_hex TEXT,
                    nonce INTEGER,
                    block_hash TEXT,
                    merkle_root TEXT,
                    version INTEGER,
                    chain_id INTEGER,
                    state_root TEXT
                )
            ''')
            c.execute('''
                CREATE TABLE IF NOT EXISTS transactions (
                    tx_id TEXT PRIMARY KEY,
                    block_index INTEGER,
                    FOREIGN KEY(block_index) REFERENCES blocks(block_index)
                )
            ''')
            c.execute('CREATE INDEX IF NOT EXISTS idx_transactions_tx_id ON transactions(tx_id)')
            # OPRAVA X-1: blocks.block_hash neměl index, přestože se na něj
            # dotazují ČTYŘI místa a dvě z nich jsou dosažitelná ze sítě:
            # handler request_blocks (ve smyčce přes locator hashe) a handler
            # new_block (fallback při nenavázaném bloku). Bez indexu je každý
            # takový dotaz full scan tabulky bloků - a to VŽDY, ne jen v
            # nejhorším případě: SQLite musí dojít na konec i tehdy, když řádek
            # najde hned, protože bez indexu neví, že je unikátní.
            #
            # Důsledek: locator s 32 hashy (~2 kB na drátě) znamenal nad DB o
            # 30 000 blocích ~5 s souvislého čtení z disku v jediném handleru,
            # přičemž is_expensive_rate_limited() účtuje jeden token za ZPRÁVU
            # bez ohledu na délku locatoru. Dávka EXPENSIVE_BUCKET_CAPACITY = 40
            # zpráv tedy vycházela na stovky sekund čtení za ~81 kB provozu.
            # Zesílení roste lineárně s délkou řetězce. Na flash paměti telefonu
            # (cílová platforma) to bolí i bez útočníka: sync_chain_periodically()
            # běží každých 10 s a každý poctivý peer platí jeden full scan.
            #
            # OPRAVA #9 tentýž problém pojmenovala ("útočník poslal statisíce
            # hashů a uzel na každý pustil SQL dotaz"), ale omezila jen POČET
            # dotazů (MAX_LOCATOR_HASHES), ne cenu jednoho.
            #
            # Index mění plán na SEARCH blocks USING COVERING INDEX a řeší
            # všechny čtyři dotazy najednou. Obě místa se schématem se volají
            # i nad UŽ EXISTUJÍCÍ tabulkou, takže si index doplní i stávající
            # databáze při prvním startu - není potřeba žádná migrace.
            c.execute('CREATE INDEX IF NOT EXISTS idx_blocks_hash ON blocks(block_hash)')

            if full:
                blocks_to_write = droid_chain.chain
            else:
                # Jen to, co v DB chybí. add_block()/replace_chain() zapisují
                # samy, takže tohle je běžně prázdné a stojí jeden dotaz.
                c.execute("SELECT MAX(block_index) FROM blocks")
                row = c.fetchone()
                db_max = row[0] if row and row[0] is not None else -1
                blocks_to_write = [b for b in droid_chain.chain if b.index > db_max]

            for block in blocks_to_write:
                transactions_json = json.dumps([tx.to_dict() for tx in block.transactions])
                target_hex = hex(block.target)[2:]
                c.execute('''
                    INSERT OR REPLACE INTO blocks (block_index, timestamp, transactions, previous_hash, target_hex, nonce, block_hash, merkle_root, version, chain_id, state_root)
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                ''', (block.index, block.timestamp, transactions_json, block.previous_hash, target_hex, block.nonce, block.hash, block.merkle_root, block.version, block.chain_id, block.state_root))
                for tx in block.transactions:
                    c.execute('INSERT OR REPLACE INTO transactions (tx_id, block_index) VALUES (?, ?)', (tx.tx_id, block.index))
            conn.commit()
            conn.close()
            conn = None
            save_mempool(droid_chain.unconfirmed_transactions)
            save_peers(peers)
    except Exception as e:
        print(f"{Fore.RED}Chyba při ukládání dat:{Style.RESET_ALL} {e}")
        vse_ok = False
    finally:
        # OPRAVA R-1: spojení se zavírá i na chybové cestě. Bez toho zůstalo
        # po první neúspěšné save_data() viset s rozdělanou transakcí a
        # VŠECHNY další zápisy do blockchain.db (včetně add_block) končily
        # na "database is locked" - uzel běžel dál, ale nepřijal už ani blok.
        if conn is not None:
            try:
                conn.rollback()
            except Exception:
                pass
            try:
                conn.close()
            except Exception:
                pass

    # OPRAVA R-5: peněženky se ukládají NEZÁVISLE na zápisu blockchainu. Dřív byly
    # až za conn.commit(), takže selhání blockchain.db (třeba "database is
    # locked") znamenalo, že se save_wallets_enc() vůbec nezavolala - klíč se
    # neuložil, přestože s ním nebylo nic v nepořádku.
    if save_wallets:
        try:
            save_wallets_enc(wallets, password)
        except Exception as e:
            print(f"{Fore.RED}Chyba při ukládání peněženek:{Style.RESET_ALL} {e}")
            vse_ok = False
    if vse_ok and (full or save_wallets):
        print(f"{Fore.GREEN}Data byla úspěšně uložena.{Style.RESET_ALL}")
    return vse_ok

def save_data_z_p2p(droid_chain, peers):
    # OPRAVA AUDIT-4: čtyři volání v P2P vrstvě (process_sync_buffer a handlery
    # response_blocks, response_full_chain, new_block) předávala modulové
    # globály `wallets` a `password`, které nastavuje až main(). Stejná třída
    # jako AUDIT-1: bez nich vyletí NameError uprostřed obsluhy zprávy ze sítě.
    #
    # Všechna čtyři volání běží se save_wallets=False, takže se `wallets` ani
    # `password` uvnitř save_data() vůbec nepoužijí - jen se vyhodnocují jako
    # argumenty. Wrapper je proto čte přes globals() a peněženky neukládá
    # vůbec; save_wallets tu záměrně není ani jako parametr, aby nešlo omylem
    # přepsat soubor s klíči prázdným slovníkem.
    save_data(droid_chain, globals().get('wallets', {}), globals().get('password'), peers)

# OPRAVA #5: Argon2id (64 MiB, 3 iterace, 4 lanes) se počítal při KAŽDÉM
# volání save_wallets_enc, tedy i při každém bloku přijatém ze sítě - 0,385 s
# a 64 MiB špička na rychlém x86, na ARM v Termuxu odhadem 1-3 s. Klíč se nově
# odvodí jednou a drží se v paměti; sůl zůstává stejná jako v souboru, nonce
# je pokaždé nový, takže AES-GCM zůstává bezpečné (dvojice klíč+nonce se nikdy
# neopakuje).
# OPRAVA F-12: náhodný pepper platný jen po dobu běhu procesu. Slouží k tomu,
# aby se v paměti nedržel otisk hesla, který by šel offline porovnat se
# slovníkem - otisk je bez tohoto tajemství nepoužitelný a s koncem procesu
# zaniká. Použití je čistě na rozlišení "je to totéž heslo jako minule?".
_WALLET_CACHE_PEPPER = os.urandom(32)
_wallet_key_cache = {'salt': None, 'key': None, 'pw_tag': None}

def derive_wallet_key(password, salt=None):
    # OPRAVA F-12: cache byla klíčovaná VÝHRADNĚ solí, takže při zásahu se
    # parametr `password` vůbec nepoužil. Dvě různá hesla proto vracela shodný
    # klíč a soubor "uložený novým heslem" byl dešifrovatelný jen tím původním.
    # Dnes je to latentní (menu změnu hesla nenabízí), ale okamžitě nebezpečné,
    # jakmile taková volba přibude - uživatel by si myslel, že heslo změnil.
    #
    # Cache existuje kvůli ceně Argon2id, takže ji nerušíme; jen se klíčuje
    # dvojicí (sůl, heslo). Heslo se v paměti drží jen jako HMAC otisk se
    # samostatnou náhodnou solí procesu, ne v otevřené podobě.
    global _wallet_key_cache
    pw_tag = hashlib.blake2b(
        password.encode(), key=_WALLET_CACHE_PEPPER, digest_size=32
    ).digest()

    if salt is None:
        if (_wallet_key_cache['key'] is not None
                and _wallet_key_cache['salt'] is not None
                and _wallet_key_cache['pw_tag'] is not None
                and hmac.compare_digest(_wallet_key_cache['pw_tag'], pw_tag)):
            return _wallet_key_cache['salt'], _wallet_key_cache['key']
        # Jiné heslo než v cache -> nová sůl a plná derivace.
        salt = os.urandom(16)
    elif (_wallet_key_cache['salt'] == salt
            and _wallet_key_cache['key'] is not None
            and _wallet_key_cache['pw_tag'] is not None
            and hmac.compare_digest(_wallet_key_cache['pw_tag'], pw_tag)):
        return salt, _wallet_key_cache['key']
    kdf = Argon2id(
        salt=salt,
        length=32,
        iterations=3,
        lanes=4,
        memory_cost=65536
    )
    key = kdf.derive(password.encode())
    _wallet_key_cache = {'salt': salt, 'key': key, 'pw_tag': pw_tag}
    return salt, key

def save_wallets_enc(wallets, password):
    wallet_data = {
        address: binascii.hexlify(wallet.private_key.to_string()).decode()
        for address, wallet in wallets.items()
    }
    data_json = json.dumps(wallet_data).encode()
    salt, key = derive_wallet_key(password)
    nonce = os.urandom(12)
    aesgcm = AESGCM(key)
    ciphertext_and_tag = aesgcm.encrypt(nonce, data_json, None)
    temp_file = WALLETS_FILE + '.tmp'
    try:
        with open(temp_file, 'wb') as f:
            f.write(salt + nonce + ciphertext_and_tag)
            f.flush()
            os.fsync(f.fileno())
        os.replace(temp_file, WALLETS_FILE)
    except Exception as e:
        if os.path.exists(temp_file):
            os.remove(temp_file)
        raise e

# OPRAVA D-04: množina tx_id, o kterých víme, že jsou zapsané v MEMPOOL_DB.
# None znamená "nevíme, načti z DB" - tak se to chová po startu uzlu i po
# jakékoli chybě zápisu, aby se cache nikdy nemohla tiše rozejít se souborem.
_mempool_persisted_ids = None

# OPRAVA N-4: save_mempool() volají P2P vlákna (handlery 'transaction',
# 'response_mempool', new_block -> save_data) i hlavní vlákno, a to bez
# droid_chain.lock. Dvě souběžná volání počítala rozdíl proti téže staré cache
# _mempool_persisted_ids a to, které doběhlo později, ji přepsalo svým snímkem.
# Test t_bug4_mempool_race.py: cache tvrdí "Y je uložená", v mempool.db není
# a žádné další uložení ji už nezapíše - restart transakci ztratí.
_mempool_save_lock = threading.Lock()

def save_mempool(unconfirmed_transactions):
    with _mempool_save_lock:
        _save_mempool_nezamceno(unconfirmed_transactions)

def _save_mempool_nezamceno(unconfirmed_transactions):
    global _mempool_persisted_ids
    conn = None
    try:
        conn = sqlite3.connect(MEMPOOL_DB, timeout=1.0)
        conn.execute("PRAGMA journal_mode=WAL;")
        c = conn.cursor()
        c.execute('''
            CREATE TABLE IF NOT EXISTS transactions (
                tx_id TEXT PRIMARY KEY,
                from_address TEXT,
                to_address TEXT,
                amount INTEGER,
                fee INTEGER,
                nonce INTEGER,
                timestamp INTEGER,
                public_key TEXT,
                signature TEXT,
                data TEXT,
                chain_id INTEGER,
                mempool_deadline INTEGER
            )
        ''')
        # OPRAVA #11: bez uložení deadline by transakce vrácená reorgem zmizela
        # při nejbližším restartu uzlu - load_mempool by ji zase posoudil jako
        # expirovanou. Sloupec je čistě lokální metadata, nikoli konsenzus.
        ensure_column(conn, 'transactions', 'mempool_deadline', 'INTEGER')

        # OPRAVA D-04: dřív 'DELETE FROM transactions' + N INSERT při KAŽDÉ
        # jedné přijaté transakci. Naměřeno 43 ms při 5 000 transakcích,
        # extrapolovaně ~144 ms zápisu do SQLite na každý příjem - a to na x86;
        # na telefonu ve flash paměti řádově víc. Naplnění mempoolu tak stálo
        # ~20 minut čistého I/O, které útočník vyvolal zdarma.
        #
        # Nově se zapisuje jen ROZDÍL. Množina už uložených tx_id se drží
        # v paměti, takže běžný případ (jedna nová transakce) je jeden INSERT.
        # Při první změně po startu se množina načte z DB - držet ji jinde by
        # znamenalo druhý zdroj pravdy, který se může rozejít.
        # OPRAVA N-7: cache je nově {tx_id: mempool_deadline}. Dřív se u řádku,
        # který už v DB byl, lhůta nikdy nepřepsala - prodloužení z recyklace
        # (add_transaction(allow_expired=True)) se tak do souboru nedostalo a
        # po restartu load_mempool() transakci posoudil podle staré lhůty.
        if _mempool_persisted_ids is None:
            c.execute('SELECT tx_id, mempool_deadline FROM transactions')
            _mempool_persisted_ids = {row[0]: row[1] for row in c.fetchall()}

        def _lhuta(tx):
            return getattr(tx, 'mempool_deadline', tx.timestamp + MEMPOOL_TX_EXPIRATION)

        current = {tx.tx_id: tx for tx in unconfirmed_transactions}
        to_insert = [tx for tx_id, tx in current.items() if tx_id not in _mempool_persisted_ids]
        to_delete = [tx_id for tx_id in _mempool_persisted_ids if tx_id not in current]
        to_update = [(_lhuta(tx), tx_id) for tx_id, tx in current.items()
                     if tx_id in _mempool_persisted_ids and _mempool_persisted_ids[tx_id] != _lhuta(tx)]
        if to_update:
            c.executemany('UPDATE transactions SET mempool_deadline = ? WHERE tx_id = ?', to_update)

        for tx in to_insert:
            c.execute('''
                INSERT OR REPLACE INTO transactions (tx_id, from_address, to_address, amount, fee, nonce, timestamp, public_key, signature, data, chain_id, mempool_deadline)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            ''', (tx.tx_id, tx.from_address, tx.to_address, tx.amount, tx.fee, tx.nonce, tx.timestamp, tx.public_key, tx.signature, tx.data, tx.chain_id,
                  getattr(tx, 'mempool_deadline', tx.timestamp + MEMPOOL_TX_EXPIRATION)))
        if to_delete:
            c.executemany('DELETE FROM transactions WHERE tx_id = ?', [(tx_id,) for tx_id in to_delete])

        conn.commit()
        conn.close()
        conn = None
        # Až po úspěšném commitu - kdyby zápis selhal, musí se příště zkusit znovu.
        _mempool_persisted_ids = {tx_id: _lhuta(tx) for tx_id, tx in current.items()}
    except Exception as e:
        # Po chybě nevíme, co v DB skutečně je; vynutíme příště načtení z DB.
        _mempool_persisted_ids = None
        print(f"{Fore.RED}Chyba při ukládání mempoolu:{Style.RESET_ALL} {e}")
    finally:
        # OPRAVA R-1: totéž co v save_data(). Tahle cesta je navíc
        # dosažitelná ze sítě - save_mempool() se volá při KAŽDÉ
        # přijaté transakci, takže uniklé zapisovací spojení tu
        # zamkne mempool.db pro všechny další zápisy.
        if conn is not None:
            try:
                conn.rollback()
            except Exception:
                pass
            try:
                conn.close()
            except Exception:
                pass


def save_peers(peers):
    # OPRAVA AUDIT-2026-8 (audit 21. 10. 2026, nález N3): vrací True/False, stejně jako
    # save_blacklist() po OPRAVĚ G-06. Volající (flush_peers) podle toho drží
    # nebo shazuje příznak 'dirty' - při neúspěšném zápisu se o změnu nepřijde
    # a zkusí se znovu při dalším flushi.
    temp_file = PEERS_FILE + '.tmp'
    try:
        with open(temp_file, 'w') as f:
            json.dump(peers, f, indent=4)
            f.flush()
            os.fsync(f.fileno())
        os.replace(temp_file, PEERS_FILE)
        return True
    except Exception as e:
        print(f"{Fore.RED}Chyba při ukládání peers:{Style.RESET_ALL} {e}")
        if os.path.exists(temp_file):
            os.remove(temp_file)
        return False

def load_data():
    wallets = {}
    droid_chain = None
    peers = []
    password = None
    if os.path.exists(WALLETS_FILE):
        try:
            password = getpass.getpass(f"{Fore.BLUE}Zadejte heslo: {Style.RESET_ALL}")
        except KeyboardInterrupt:
            print("\nUkončeno uživatelem.")
            sys.exit(0)
        try:
            with open(WALLETS_FILE, 'rb') as f:
                data = f.read()
            salt = data[:16]
            nonce = data[16:28]
            ciphertext_and_tag = data[28:]
            # OPRAVA #5: odvození při odemknutí zároveň naplní cache, takže
            # všechny další zápisy peněženek už Argon2id nepočítají.
            salt, key = derive_wallet_key(password, salt)
            aesgcm = AESGCM(key)
            decrypted = aesgcm.decrypt(nonce, ciphertext_and_tag, None)
            wallet_data = json.loads(decrypted.decode())
            try:
                wallets = {
                    address: Wallet(private_key)
                    for address, private_key in wallet_data.items()
                }
                print(f"{Fore.GREEN}Peněženky byly načteny ze souboru.{Style.RESET_ALL}")
            except ValueError:
                print(f"{Fore.RED}Chyba: Soubor peněženek obsahuje neplatná data (poškozený klíč).{Style.RESET_ALL}")
                sys.exit(1)
        except Exception:
            # OPRAVA G-11: 'as e' se nepoužívalo; text výjimky se tu opět
            # záměrně nevypisuje.
            print(f"{Fore.RED}Chyba při dešifrování peněženek: Špatné heslo nebo poškozený soubor.{Style.RESET_ALL}")
            sys.exit(1)
    else:
        print(f"{Fore.YELLOW}Žádný šifrovaný soubor peněženek nenalezen. Vytvářím nový.{Style.RESET_ALL}")
        while True:
            try:
                pwd1 = getpass.getpass(f"{Fore.BLUE}Vytvořte heslo (8-20 znaků): {Style.RESET_ALL}")
                if not 8 <= len(pwd1) <= 20:
                    print(f"{Fore.RED}Délka hesla musí být mezi 8 a 20 znaky.{Style.RESET_ALL}")
                    continue
                pwd2 = getpass.getpass(f"{Fore.BLUE}Potvrďte heslo: {Style.RESET_ALL}")
                if pwd1 == pwd2:
                    password = pwd1
                    break
                else:
                    print(f"{Fore.RED}Hesla se neshodují.{Style.RESET_ALL}")
            except KeyboardInterrupt:
                print("\nUkončeno uživatelem.")
                sys.exit(0)
        wallets = {}
        save_wallets_enc(wallets, password)
        print(f"{Fore.GREEN}Nový šifrovaný soubor peněženek vytvořen. Zálohujte si své privátní klíče odděleně pro případ obnovy.{Style.RESET_ALL}")
    
    if os.path.exists(PEERS_FILE):
        try:
            with open(PEERS_FILE, 'r') as f:
                peers_data = json.load(f)
                # OPRAVA S-7: dřív šlo `[tuple(p) for p in peers_data]` rovnou
                # do P2PNode.__init__, kde `for ip, port in initial_peers`
                # rozbalí každou položku na dvojici. Tříprvková položka (ruční
                # editace, poškozený soubor) tam vyhodila ValueError MIMO
                # jakýkoli try - a protože main() volá load_data() bez try,
                # padal uzel tracebackem kvůli souboru, který ani není
                # konsenzuální. Tvar se proto ověří tady, u zdroje.
                if not isinstance(peers_data, list):
                    raise ValueError("peers.json není seznam.")
                peers = []
                vadnych = 0
                for p in peers_data:
                    if (isinstance(p, (list, tuple)) and len(p) == 2
                            and isinstance(p[0], str)
                            and isinstance(p[1], int) and not isinstance(p[1], bool)
                            and 1 <= p[1] <= 65535):
                        peers.append((p[0], p[1]))
                    else:
                        vadnych += 1
                if vadnych:
                    print(f"{Fore.YELLOW}Z peers.json vyhozeno {vadnych} položek se špatným tvarem "
                          f"(očekává se [\"ip\", port]).{Style.RESET_ALL}")
                # OPRAVA T-4 (Nález 1): adresy se normalizují už tady, u zdroje -
                # stejně jako load_blacklist() normalizuje klíče při NAČÍTÁNÍ.
                # Bez toho by do P2PNode vešel syrový tvar z ruční editace
                # souboru a tabulka peerů by držela tutéž adresu ve dvou
                # podobách. Druhá, nezávislá pojistka je v P2PNode.__init__().
                peers, slouceno = normalize_peer_list(peers)
                if slouceno:
                    print(f"{Fore.YELLOW}Z peers.json sloučeno {slouceno} záznamů, které po "
                          f"normalizaci IP ukazovaly na týž uzel.{Style.RESET_ALL}")
                print(f"{Fore.GREEN}Peers byly načteny ze souboru.{Style.RESET_ALL}")
        except Exception as e:
            print(f"{Fore.RED}Chyba při načítání peers:{Style.RESET_ALL} {e}")
            
    droid_chain = Blockchain(create_genesis=False)
    
    if os.path.exists(BLOCKCHAIN_DB):
        conn = None
        try:
            conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
            conn.execute("PRAGMA journal_mode=WAL;")
            c = conn.cursor()
            c.execute('''
                CREATE TABLE IF NOT EXISTS blocks (
                    block_index INTEGER PRIMARY KEY,
                    timestamp INTEGER,
                    transactions TEXT,
                    previous_hash TEXT,
                    target_hex TEXT,
                    nonce INTEGER,
                    block_hash TEXT,
                    merkle_root TEXT,
                    version INTEGER,
                    chain_id INTEGER,
                    state_root TEXT
                )
             ''')
            c.execute('''
                CREATE TABLE IF NOT EXISTS transactions (
                    tx_id TEXT PRIMARY KEY,
                    block_index INTEGER,
                    FOREIGN KEY(block_index) REFERENCES blocks(block_index)
                )
            ''')
            c.execute('CREATE INDEX IF NOT EXISTS idx_transactions_tx_id ON transactions(tx_id)')
            # OPRAVA X-1: viz obsáhlý komentář u téhož řádku v save_data().
            # Tohle je startovní cesta, takže právě tady si index doplní
            # databáze založené ještě před touto opravou.
            c.execute('CREATE INDEX IF NOT EXISTS idx_blocks_hash ON blocks(block_hash)')

            if ensure_state_root_column(conn):
                print(f"{Fore.YELLOW}Databáze byla rozšířena o sloupec state_root. Bloky uložené ve starém formátu neprojdou validací a řetězec bude potřeba stáhnout znovu.{Style.RESET_ALL}")

            c.execute("SELECT COUNT(*) FROM transactions")
            if c.fetchone()[0] == 0:
                c.execute("SELECT block_index, transactions FROM blocks")
                for row in c.fetchall():
                    b_idx = row[0]
                    txs = json.loads(row[1])
                    for t in txs:
                        c.execute("INSERT OR IGNORE INTO transactions (tx_id, block_index) VALUES (?, ?)", (t['tx_id'], b_idx))
                conn.commit()

            c.execute("SELECT MAX(block_index) FROM blocks")
            droid_chain.max_block_index = c.fetchone()[0] or 0
            c.execute("SELECT block_index, timestamp, transactions, previous_hash, target_hex, nonce, block_hash, merkle_root, version, chain_id, state_root FROM blocks WHERE block_index > ? ORDER BY block_index", (droid_chain.max_block_index - LAST_BLOCKS_TO_KEEP,))
            # OPRAVA Z-2 (nález 2): streamovaný kurzor místo fetchall(). Komentář
            # u OPRAVY Y-4 níž výslovně počítá s "MemoryError při fetchall() nad
            # oknem LAST_BLOCKS_TO_KEEP bloků (až 1,2 GB)" jako s reálnou cestou
            # na cílové platformě; půlka té špičky byly syrové řádky držené
            # zbytečně vedle objektů, které se z nich stavěly.
            droid_chain.chain = [Block.from_dict({
                'index': row[0],
                'timestamp': row[1],
                'transactions': json.loads(row[2]),
                'previous_hash': row[3],
                'target': row[4],
                'nonce': row[5],
                'hash': row[6],
                'merkle_root': row[7],
                'version': row[8],
                'chain_id': row[9], 'state_root': row[10]
            }) for row in c]
            # OPRAVA S-7: `conn.close()` tu byl obyčejný řádek uvnitř try bez
            # finally - vzorec, který si kód jinde sám zakazuje (OPRAVA G-08,
            # L-3). Nad poškozeným řádkem vyhodí json.loads() i Block.from_dict()
            # kousek výš, takže na chybové cestě spojení unikalo. Zavření je
            # nově ve finally.
            print(f"{Fore.GREEN}Blockchain byl načten z databáze.{Style.RESET_ALL}")
        except Exception as e:
            # OPRAVA S-7: čtecí spojení se zavře JEŠTĚ PŘED záchranným zápisem
            # níž - save_data(full=True) přepisuje tytéž tabulky a nemá kolem
            # sebe potřebovat otevřeného čtenáře.
            if conn is not None:
                try:
                    conn.close()
                except Exception:
                    pass
                conn = None
            print(f"{Fore.RED}Chyba při načítání blockchainu:{Style.RESET_ALL} {e}")
            # OPRAVA U-22 (audit 7. 10. 2026, pozorování 4.4): hláška tu dřív
            # zněla "Vytvářím nový blockchain s genesis blokem", což je ZAVÁDĚJÍCÍ.
            # save_data() žádnou tabulku nemaže - bloky zapisuje přes
            # INSERT OR REPLACE - takže obsah blockchain.db zůstane celý i se
            # všemi starými bloky. Nový je jen stav V PAMĚTI. Uživatel, který
            # té hlášce uvěří, se domnívá, že přišel o řetězec, a sáhne po
            # destruktivním řešení, přestože mu data pořád leží na disku.
            # O skutečném osudu databáze rozhodne až is_valid_chain() níž
            # a nabídka z OPRAVY F-14.
            print(f"{Fore.YELLOW}Stav v paměti vracím na genesis blok. "
                  f"Obsah blockchain.db se NEMAŽE - jeho platnost posoudí validace "
                  f"při startu.{Style.RESET_ALL}")
            # OPRAVA G-11: droid_chain.chain už v tuhle chvíli může být částečně
            # naplněná - výjimka mohla nastat až ZA přiřazením výše. Genesis by
            # se pak připojil na KONEC existujícího seznamu a save_data(full=True)
            # by zapsal i staré bloky. Následná is_valid_chain() to sice zachytí,
            # ale spoléhat se na obranu v druhé linii je zbytečné: stav se před
            # tvorbou genesis vynuluje. (max_block_index si create_genesis_block()
            # nastavuje sám.)
            droid_chain.chain = []
            droid_chain.create_genesis_block()
            # OPRAVA U-22 (pozorování 4.4): save_wallets=False. Tahle cesta se
            # týká VÝHRADNĚ blockchain.db; s peněženkami nemá nic společného
            # a jejich obsah se na ní nemění. Zápis je sice atomický (temp +
            # fsync + os.replace) a nikdy nic nerozbil, ale je to zbytečná
            # operace nad nejcennějším souborem uzlu, a to zrovna na chybové
            # cestě - tedy ve chvíli, kdy o stavu stroje víme nejmíň.
            # Navíc s sebou nese přepočet Argon2id, který tu k ničemu není.
            save_data(droid_chain, wallets, password, peers, full=True, save_wallets=False)
        finally:
            if conn is not None:
                try:
                    conn.close()
                except Exception:
                    pass
    else:
        print(f"{Fore.YELLOW}Databáze blockchainu nenalezena. Vytvářím nový blockchain s genesis blokem.{Style.RESET_ALL}")
        droid_chain.create_genesis_block()
        save_data(droid_chain, wallets, password, peers, full=True, save_wallets=True)
        
    print(f"{Fore.YELLOW}Provádím plnou validaci blockchain.db při startu...{Style.RESET_ALL}")
    is_valid, chain_state = droid_chain.is_valid_chain()
    if not is_valid:
        # OPRAVA F-14: dřív tady bylo bezpodmínečné sys.exit(1) - uzel s vadnou
        # databází se už nikdy nespustil a uživateli nezbylo než ručně smazat
        # blockchain.db, tedy bez jakéhokoli vodítka, co dělá. V kombinaci
        # s F-03 a F-08 (OOM na telefonu) nebo s F-10 to znamenalo uzel, který
        # je mimo provoz natrvalo.
        #
        # Odmítnutí vadného řetězce je správně a nemění se: uzel s ním
        # nepokračuje. Nově ale existuje cesta ven - zahodit lokální databázi
        # a stáhnout řetězec znovu ze sítě, což je přesně to, co by uživatel
        # dělal ručně. Rozhodnutí zůstává na něm, protože jde o destruktivní
        # operaci; automaticky se nemaže nic.
        #
        # OPRAVA S-1 (Nález 4): is_valid_chain() nově vrací (False, None) i při
        # sqlite3.Error. Mezi ně patří i OperationalError "database is locked",
        # tedy stav ZDRAVÉ databáze, kterou drží druhá instance uzlu. Kdyby se
        # v takové chvíli nabídlo destruktivní menu, byla by oprava horší než
        # původní pád. Levná nedestruktivní sonda to rozliší PŘED menu:
        # poškozený soubor hlásí sqlite3.DatabaseError ("file is not a
        # database" / "database disk image is malformed"), zamčený jen
        # OperationalError - a ten je podtřída, takže se chytá jako první.
        def _db_je_jen_zamcena():
            try:
                _c = sqlite3.connect(BLOCKCHAIN_DB, timeout=0.5)
                try:
                    _c.execute("SELECT COUNT(*) FROM sqlite_master")
                    return False, None
                finally:
                    _c.close()
            except sqlite3.OperationalError as e:
                return True, e
            except Exception:
                return False, None

        _zamcena, _duvod = _db_je_jen_zamcena()
        if os.path.exists(BLOCKCHAIN_DB) and _zamcena:
            print(f"{Fore.RED}CHYBA: blockchain.db není čitelná ({_duvod}).{Style.RESET_ALL}")
            print(f"{Fore.YELLOW}Nejspíš už běží druhá instance uzlu nad týmž adresářem.{Style.RESET_ALL}")
            print(f"{Fore.YELLOW}Databáze se NEMAŽE a zůstává nedotčená. Ukončete druhou{Style.RESET_ALL}")
            print(f"{Fore.YELLOW}instanci (nebo opravte práva k souboru) a spusťte uzel znovu.{Style.RESET_ALL}")
            sys.exit(1)

        print(f"{Fore.RED}CHYBA: Blockchain v blockchain.db je neplatný nebo byl ručně podvržen!{Style.RESET_ALL}")
        print(f"{Fore.YELLOW}Uzel s tímto řetězcem nemůže pokračovat. Peněženky ani adresář{Style.RESET_ALL}")
        print(f"{Fore.YELLOW}adres se v žádném případě nemažou - jsou v samostatných souborech.{Style.RESET_ALL}")
        print()
        print(f"  {Fore.GREEN}1{Style.RESET_ALL} - Zahodit blockchain.db a stáhnout řetězec znovu ze sítě")
        print(f"  {Fore.GREEN}2{Style.RESET_ALL} - Ukončit a nechat databázi beze změny (pro ruční rozbor)")
        try:
            volba = input(f"{Fore.BLUE}Volba [1/2]: {Style.RESET_ALL}").strip()
        except (KeyboardInterrupt, EOFError):
            volba = '2'

        if volba != '1':
            print(f"{Fore.RED}Program se ukončuje. Databáze zůstala nedotčená.{Style.RESET_ALL}")
            sys.exit(1)

        # Poškozenou DB odkládáme stranou, nemažeme ji. Kdyby šlo o chybu
        # v uzlu a ne o podvrh, je pak co zkoumat.
        zaloha = f"{BLOCKCHAIN_DB}.invalid.{int(time.time())}"
        try:
            for pripona in ('', '-wal', '-shm'):
                zdroj = BLOCKCHAIN_DB + pripona
                if os.path.exists(zdroj):
                    os.replace(zdroj, zaloha + pripona)
            print(f"{Fore.YELLOW}Původní databáze odložena jako {zaloha}{Style.RESET_ALL}")
        except OSError as e:
            print(f"{Fore.RED}Databázi se nepodařilo odložit ({e}). Ukončuji.{Style.RESET_ALL}")
            sys.exit(1)

        # Mempool z vadného řetězce je také k ničemu - nonce i zůstatky
        # odkazují na stav, který neplatí.
        for pripona in ('', '-wal', '-shm'):
            try:
                if os.path.exists(MEMPOOL_DB + pripona):
                    os.remove(MEMPOOL_DB + pripona)
            except OSError:
                pass

        droid_chain = Blockchain(create_genesis=False)
        droid_chain.create_genesis_block()
        save_data(droid_chain, wallets, password, peers, full=True, save_wallets=False)
        print(f"{Fore.GREEN}Blockchain resetován na genesis blok.{Style.RESET_ALL}")
        print(f"{Fore.YELLOW}Řetězec se dotáhne ze sítě při první synchronizaci s peery.{Style.RESET_ALL}")

        is_valid, chain_state = droid_chain.is_valid_chain()
        if not is_valid:
            # Neplatný řetězec o jediném genesis bloku znamená vadný build,
            # ne poškozená data - ze sítě to opravit nejde.
            print(f"{Fore.RED}CHYBA: Ani čerstvý genesis blok neprošel validací.{Style.RESET_ALL}")
            print(f"{Fore.RED}To ukazuje na chybu v samotném programu, ne v datech. Ukončuji.{Style.RESET_ALL}")
            sys.exit(1)

    droid_chain.balance_map = chain_state['balance_map']
    droid_chain.nonce_map = chain_state['nonce_map']
    droid_chain.total_supply = chain_state['total_supply']
    droid_chain.cumulative_work = chain_state['cumulative_work']
    droid_chain.immature_rewards = chain_state.get('immature_rewards', {})
    # OPRAVA F-03: strom postavený při startovní validaci se převezme rovnou.
    # Bez tohohle by uzel běžel s prázdnou cache nad plnými mapami, tedy se
    # špatným state rootem.
    startovni_smt = chain_state.get('accounts_smt')
    droid_chain.accounts_smt = (startovni_smt if startovni_smt is not None
                                else build_accounts_smt(droid_chain.balance_map,
                                                        droid_chain.nonce_map))

    # is_valid_chain() nyní v rámci téhož průchodu řetězcem rovnou staví i
    # undo_logs a state_checkpoints (dříve to vyžadovalo druhý, samostatný
    # průchod přes rebuild_state()/update_state_with_block() po validaci).
    # Tím se sloučily dva průchody řetězcem do jednoho a ušetří se CPU čas
    # potřebný na start uzlu.
    droid_chain.undo_logs = chain_state.get('undo_logs', {})
    droid_chain.state_checkpoints = chain_state.get('state_checkpoints', {})

    # OPRAVA Y-4 (audit 14. 10. 2026, nález 4): s ověřeným stavem se přebírá
    # i VÝŠKA, ke které ten stav patří.
    #
    # is_valid_chain() přečte CELOU databázi a vrátí stav jejího vrcholu;
    # max_block_index a chain se ale braly z načítací větve výš. V jedné cestě
    # se ty dva zdroje rozešly: když čtení DB vyhodí výjimku, except větev
    # zahodí stav v paměti a zavolá create_genesis_block(), tedy srazí
    # max_block_index na 0 - a hned nato se sem převezme balance_map,
    # nonce_map, total_supply, cumulative_work, immature_rewards i SMT
    # odpovídající vrcholu v DB. Uzel pak hlásí "Blockchain validován úspěšně",
    # ale tvrdí výšku 0 nad stavem výšky N: get_state_at(0) vrací stav vrcholu,
    # reálný následující blok se odmítne a vytěžený blok #1 by nesl state root
    # jiné výšky, takže by ho odmítla celá síť. Uživatel nemá jak poznat, že je
    # uzel rozbitý - a to je na tom to nejhorší.
    #
    # Dosažitelnost je úzká, ale reálná: stačí přechodná výjimka v tom jednom
    # bloku try, která se v is_valid_chain() nezopakuje. Nejpravděpodobnější je
    # MemoryError při fetchall() nad oknem LAST_BLOCKS_TO_KEEP bloků (až 1,2 GB),
    # protože is_valid_chain() čte po jednom přes generátor. Cílová platforma
    # je telefon, takže to není čistá teorie.
    #
    # Neshoda se proto nedopočítává ručně, ale předá se _resync_memory_from_db(),
    # která přesně tohle umí a je pro řízené zotavení napsaná (viz OPRAVA M-2).
    # Rebuild stavu je pomalý, ale tohle je havarijní cesta, kde má správnost
    # přednost před rychlostí. V běžném startu se podmínka nikdy nesplní.
    tip_index = chain_state.get('tip_index')
    if tip_index is not None and droid_chain.max_block_index != tip_index:
        print(f"{Fore.RED}Nesoulad stavu uzlu: v paměti je vrchol #{droid_chain.max_block_index}, "
              f"ale ověřený řetězec v databázi končí na #{tip_index}.{Style.RESET_ALL}")
        print(f"{Fore.YELLOW}Dorovnávám paměť podle databáze...{Style.RESET_ALL}")
        if not droid_chain._resync_memory_from_db():
            print(f"{Fore.RED}Dorovnání paměti podle databáze SELHALO. Uzel by běžel se stavem{Style.RESET_ALL}")
            print(f"{Fore.RED}jedné výšky a vrcholem jiné: nepřijal by cizí bloky a vytěžil by{Style.RESET_ALL}")
            print(f"{Fore.RED}blok, který síť odmítne. Ukončuji - spusťte uzel znovu.{Style.RESET_ALL}")
            sys.exit(1)
        print(f"{Fore.GREEN}Paměť dorovnána podle databáze (vrchol #{droid_chain.max_block_index}).{Style.RESET_ALL}")

    print(f"{Fore.GREEN}Blockchain validován úspěšně.{Style.RESET_ALL}")
    droid_chain.unconfirmed_transactions = load_mempool(droid_chain)
    return droid_chain, wallets, peers, password

def load_mempool(droid_chain):
    # ZMĚNA 3: načtení CELÉHO uloženého mempoolu (nejen transakcí tohoto uzlu)
    # a jeho validace proti aktuálnímu blockchainu. Volá se z load_data() až po
    # načtení a validaci řetězce, takže balance_map a nonce_map jsou aktuální.
    #
    # Oproti původní verzi:
    #   - transakce se čtou v pořadí zápisu (ORDER BY rowid) a ověřují se po
    #     odesílatelích v pořadí nonce - dřív šly do add_transaction() v pořadí,
    #     jaké náhodou vrátil SELECT, a platná navazující transakce propadla,
    #     kdykoli se načetla dřív než její předchůdce,
    #   - vytěžené, zastaralé a jinak neplatné transakce (včetně navazujících
    #     po díře v nonce) se odstraní, viz Blockchain.revalidate_stored_mempool,
    #   - výsledek validace se hned propíše zpět do mempool.db.
    if not os.path.exists(MEMPOOL_DB):
        return droid_chain.unconfirmed_transactions
    try:
        conn = sqlite3.connect(MEMPOOL_DB, timeout=1.0)
        try:
            conn.execute("PRAGMA journal_mode=WAL;")
            c = conn.cursor()
            c.execute('''
                CREATE TABLE IF NOT EXISTS transactions (
                    tx_id TEXT PRIMARY KEY,
                    from_address TEXT,
                    to_address TEXT,
                    amount INTEGER,
                    fee INTEGER,
                    nonce INTEGER,
                    timestamp INTEGER,
                    public_key TEXT,
                    signature TEXT,
                    data TEXT,
                    chain_id INTEGER,
                    mempool_deadline INTEGER
                )
            ''')
            ensure_column(conn, 'transactions', 'mempool_deadline', 'INTEGER')
            c.execute("SELECT tx_id, from_address, to_address, amount, fee, nonce, timestamp, public_key, signature, data, chain_id, mempool_deadline FROM transactions ORDER BY rowid")
            rows = c.fetchall()
        finally:
            conn.close()
    except Exception as e:
        print(f"{Fore.RED}Chyba při načítání mempoolu:{Style.RESET_ALL} {e}")
        return droid_chain.unconfirmed_transactions

    if not rows:
        return droid_chain.unconfirmed_transactions

    print(f"{Fore.YELLOW}Ověřuji uložený mempool ({len(rows)} TX) proti aktuálnímu stavu blockchainu...{Style.RESET_ALL}")
    kandidati = []
    necitelne = 0
    for row in rows:
        tx_data = {
            'tx_id': row[0],
            'from_address': row[1],
            'to_address': row[2],
            'amount': row[3],
            'fee': row[4],
            'nonce': row[5],
            'timestamp': row[6],
            'public_key': row[7],
            'signature': row[8],
            'data': row[9],
            'chain_id': row[10]
        }
        try:
            tx = Transaction.from_dict(tx_data)
        except ValueError as e:
            # from_dict() ověřuje i shodu uloženého tx_id s obsahem transakce,
            # takže sem padá i ručně pozměněný záznam.
            necitelne += 1
            print(f"{Fore.YELLOW}  Odstraněno z mempoolu: {row[0]} - poškozený nebo nečitelný záznam ({e}){Style.RESET_ALL}")
            continue
        # OPRAVA #11: uloženou lhůtu obnovíme. Pokud ještě běží a je
        # pozdější, než by odpovídalo stáří transakce, jde o transakci
        # vrácenou reorgem a musí se pustit zpět i jako "expirovaná".
        stored_deadline = row[11]
        allow_expired = False
        if isinstance(stored_deadline, int):
            tx.mempool_deadline = stored_deadline
            if stored_deadline > tx.timestamp + MEMPOOL_TX_EXPIRATION and stored_deadline > get_time():
                allow_expired = True
        kandidati.append((tx, allow_expired))

    try:
        ponechane, odstranene = droid_chain.revalidate_stored_mempool(kandidati)
    except Exception as e:
        # V mempoolu zůstává jen to, co už validací prošlo.
        print(f"{Fore.RED}Chyba při ověřování uloženého mempoolu:{Style.RESET_ALL} {e}")
        return droid_chain.unconfirmed_transactions
    odstranene += necitelne

    # Odstraněné transakce se hned smažou i z mempool.db. save_mempool() zapisuje
    # rozdíl proti souboru, takže ponechané transakce se nepřepisují a smažou
    # se jen řádky, které v paměti nejsou.
    save_mempool(droid_chain.unconfirmed_transactions)
    print(f"{Fore.GREEN}Mempool obnoven a ověřen: ponecháno {ponechane} TX, odstraněno {odstranene} TX.{Style.RESET_ALL}")
    return droid_chain.unconfirmed_transactions

def uloz_mempool_pri_vypnuti(droid_chain):
    # ZMĚNA 2: náhrada za původní mazání mempool.db při vypnutí uzlu (volba 20
    # i CTRL+C). Mazání mělo chránit před načtením zastaralých transakcí po
    # delší nečinnosti, jenže uzel si pak po restartu musel transakce znovu
    # vyžádat od peerů - a ty je neposílají v pořadí nonce, takže navazující
    # transakce téže adresy propadaly. A kdyby to dělal každý uzel, neuchovával
    # by si mempool nikdo a po restartu by nebylo odkud ho získat.
    #
    # Ochranu před zastaralými transakcemi nově zajišťuje validace při startu
    # (Blockchain.revalidate_stored_mempool), takže se mempool uchovává celý.
    #
    # save_data() mempool ukládá také, ale až po zápisu blockchainu - kdyby
    # ten selhal, save_mempool() by se vůbec nezavolal. Proto se tu ukládá
    # ještě jednou samostatně. Je-li mempool.db už aktuální, zapíše se prázdný
    # rozdíl, takže to nic nestojí.
    with droid_chain.lock:
        save_mempool(droid_chain.unconfirmed_transactions)
        pocet = len(droid_chain.unconfirmed_transactions)
        ulozeno = _mempool_persisted_ids is not None
    if ulozeno:
        print(f"{Fore.GREEN}Mempool ({pocet} TX) zůstává uložený v {MEMPOOL_DB} a při dalším spuštění se načte a ověří.{Style.RESET_ALL}")
    else:
        print(f"{Fore.RED}Mempool se nepodařilo uložit do {MEMPOOL_DB} (viz chyba výše).{Style.RESET_ALL}")

class PeerConnection:
    """
    ETAPA 1: perzistentní odchozí spojení na jeden uzel.

    Nese naše požadavky a odpovědi protistrany. Odpověď se páruje s dotazem
    přes request_id. Zprávy bez request_id (např. new_block, který nám peer
    pošle sám od sebe) jdou do handle_message() jako nevyžádané.

    Topologie je záměrně dvousocketová: tenhle socket vlastníme my a nese naše
    dotazy, protistrana má svůj vlastní pro své dotazy. Sdílet jeden socket
    obousměrně by vyžadovalo domluvu, kdo ho po výpadku obnovuje.
    """

    def __init__(self, node, peer, sock):
        self.node = node
        self.peer = peer
        self.sock = sock
        self.send_lock = threading.Lock()
        self.pending_lock = threading.Lock()
        self.pending = {}
        self.alive = True
        self.last_used = time.time()
        self.reader = threading.Thread(target=self._read_loop, daemon=True)
        self.reader.start()

    def _read_loop(self):
        # OPRAVA P-3: rozpočet na NEVYŽÁDANÉ zprávy i na tomhle socketu.
        #
        # Uzel má dvě čtecí cesty, které obě končí v handle_message():
        # handle_client_connection() (spojení navázal peer) a tahle
        # (spojení jsme navázali my). Rate limiting i MAX_UNAUTHENTICATED_MESSAGES
        # byly jen na té první, takže peer, kterého jsme sami dialovali, mohl
        # posílat nevyžádané zprávy bez jakéhokoli stropu a spojení se nikdy
        # nezavřelo, ať jich bylo odmítnuto kolik chtělo. Měřeno: 50 zpráv =
        # 50 volání is_rate_limited() na příchozí cestě, 0 na této.
        #
        # Odpovědi párované přes request_id se NEúčtují - ty jsme si vyžádali
        # sami a vlastní limiter by nám škrtil vlastní sync.
        neprijate_za_sebou = 0
        try:
            while self.alive and self.node.running:
                # NAD RÁMEC AUDITU (týž vzorec jako A-06): celková lhůta i na
                # HLAVIČKU, stejně jako v handle_client_connection(). Bez ní
                # platil timeout jen na jedno recv(), takže 4 bajty hlavičky
                # kapající po jednom držely vlákno až 4x CONNECTION_IDLE_TIMEOUT.
                # Audit to hodnotí jako dostačující (strop je konečný), ale
                # obě čtecí cesty se nemají lišit v tom, co po peerovi chtějí.
                # Na nečinné spojení to nic nemění: lhůta je táž hodnota, jakou
                # už drží settimeout na socketu.
                raw = P2PNode._recv_exactly(self.sock, 4, time.monotonic() + CONNECTION_IDLE_TIMEOUT)
                if not raw:
                    break
                msglen = struct.unpack('!I', raw)[0]
                if msglen > MAX_MESSAGE_SIZE:
                    self.node.add_log(f"{Fore.RED}Odpověď od {self.peer} překračuje MAX_MESSAGE_SIZE. Zavírám spojení.{Style.RESET_ALL}")
                    break
                # OPRAVA A-06: celková lhůta na doručení TĚLA, stejně jako
                # v handle_client_connection(). Bez ní platil timeout jen na
                # JEDNO recv(), takže peer, který kape po bajtu, držel spojení
                # i čtecí vlákno navždy - a protože self.alive zůstávalo True,
                # get_connection() takové spojení dál vracelo jako živé a peer
                # se stal černou dírou, o které uzel nevěděl. Je to doslova
                # stav, který popisuje OPRAVA N-2; do téhle čtecí cesty se
                # tehdy nedostala.
                # OPRAVA AUDIT-2026-3 (audit 8. 10. 2026, nález 3): i tahle čtecí
                # cesta si musí místo pro buffer REZERVOVAT z globálního stropu.
                # Je jich na uzlu nejvýš MAX_PEERS, ale 20 x 10 MiB je pořád
                # 200 MiB, a zabraná paměť je zabraná bez ohledu na to, kterým
                # socketem přišla.
                #
                # Per-IP kbelík (charge_inbound_bytes) se tu ZÁMĚRNĚ neúčtuje:
                # tudy chodí odpovědi na NAŠE vlastní dotazy, jejichž tempo si
                # řídíme sami přes sync_blocks_from_peer(). Účtovat je znamená
                # škrtit vlastní synchronizaci, což je přesně failure mode
                # OPRAVY #1 - dva poctivé uzly, které se navzájem přiškrtí.
                if not self.node.rezervuj_prijmovou_pamet(msglen):
                    self.node.add_log(f"{Fore.YELLOW}Odpověď od {self.peer} ({msglen / 1024:.0f} KB) "
                                      f"zahozena: vyčerpán strop souběžně přijímaných dat. "
                                      f"Zavírám spojení.{Style.RESET_ALL}")
                    break
                try:
                    body = P2PNode._recv_exactly(
                        self.sock, msglen,
                        time.monotonic() + MESSAGE_RECV_GRACE_SECONDS + msglen / MIN_RECV_RATE_BYTES_PER_S)
                finally:
                    # Uvolňuje se hned po recv(), ne až po zpracování jako na
                    # příchozí cestě: tady se zpráva zpracovává pod zámky
                    # blockchainu (replace_chain, add_block) a držet přes to
                    # globální rozpočet by zablokovalo příjem od ostatních peerů.
                    # Strop tedy kryje souběžné BUFFERY, parsovanou strukturu
                    # drží v mezích MAX_PEERS.
                    self.node.uvolni_prijmovou_pamet(msglen)
                # _recv_exactly() nechá na socketu zbytek lhůty; další čtení
                # i odeslání mají mít zase plný timeout.
                self.sock.settimeout(CONNECTION_IDLE_TIMEOUT)
                if body is None:
                    break
                if not P2PNode._json_depth_ok(body):
                    self.node.add_log(f"{Fore.RED}Odpověď od {self.peer} má příliš hluboké vnoření. Zavírám spojení.{Style.RESET_ALL}")
                    break
                # OPRAVA U-1 (audit 2. 10. 2026, nález 1): json.loads() nevyhodí
                # vždy JSONDecodeError. Od Pythonu 3.11 je převod desítkového
                # řetězce na int omezen na sys.get_int_max_str_digits() (4300)
                # číslic, takže JSON s delším celočíselným literálem vyhodí HOLÝ
                # ValueError - a ten tenhle except nechytal. Výjimka z
                # nedůvěryhodných dat tak propadla o vrstvu výš, tedy přesně
                # vzorec, který řeší OPRAVA #4, #3, D-07, N-6, G-07, R-2 a S-1.
                #
                # json.JSONDecodeError JE podtřída ValueError, takže širší tuple
                # pokrývá obě cesty a nic navíc nepropouští.
                try:
                    message = json.loads(body.decode('utf-8'))
                except (ValueError, UnicodeDecodeError):
                    break
                if not isinstance(message, dict):
                    continue

                rid = message.get('request_id')
                waiter = None
                # OPRAVA S-7: rid jde přímo z dat protistrany do dict.pop().
                # Nehashovatelná hodnota ({"request_id": []}) vyhodila
                # TypeError: unhashable type: 'list' a shodila celé spojení.
                # Vlastní request_id vydává next_request_id(), tedy int -
                # cokoli jiného odpovědí na náš dotaz být nemůže a rovnou se
                # zpracuje jako nevyžádaná zpráva. isinstance(True, int) je
                # v Pythonu True, takže bool vylučujeme zvlášť.
                if isinstance(rid, int) and not isinstance(rid, bool):
                    with self.pending_lock:
                        waiter = self.pending.pop(rid, None)
                if waiter is not None:
                    waiter.put(message)
                    neprijate_za_sebou = 0
                else:
                    # Nevyžádaná zpráva na našem odchozím socketu. Peera jsme
                    # dialovali sami, takže bránu z opravy #10 projde.
                    # OPRAVA P-3: proto na ni musí platit týž rozpočet jako na
                    # zprávu z příchozího spojení.
                    if self.node.is_rate_limited(self.peer):
                        self.node.add_log(f"{Fore.YELLOW}Nevyžádaná zpráva od {self.peer} zahozena: vyčerpán limit zpráv. Zavírám spojení.{Style.RESET_ALL}")
                        break
                    # OPRAVA N1 (audit 10. 10. 2026, poznámka k nálezu N1):
                    # bajtový rozpočet se tudy ZÁMĚRNĚ neúčtuje odpovědím na
                    # naše vlastní dotazy (viz komentář u recv výš - škrtili
                    # bychom si vlastní sync). Nevyžádaná zpráva je ale něco
                    # jiného: tempo si řídí protistrana, ne my, takže na ni
                    # musí platit týž bajtový strop jako na příchozí cestě.
                    # Bez toho zbývala jediná mez počet zpráv za sekundu, tedy
                    # právě ta jednotka, kterou nález N1 označil za špatnou.
                    if not self.node.charge_inbound_bytes(self.peer, msglen):
                        self.node.add_log(f"{Fore.YELLOW}Nevyžádaná zpráva od {self.peer} "
                                          f"({msglen / 1024:.0f} KB) zahozena: vyčerpán bajtový "
                                          f"rozpočet příjmu. Zavírám spojení.{Style.RESET_ALL}")
                        break
                    prijato = self.node.handle_message(message, self.peer, reply=self.send)
                    # OPRAVA P-3: `is False` stejně jako v handle_client_connection -
                    # None znamená "zpracováno, nic k hlášení", ne odmítnutí.
                    if prijato is False:
                        neprijate_za_sebou += 1
                        if neprijate_za_sebou >= MAX_UNAUTHENTICATED_MESSAGES:
                            self.node.add_log(f"{Fore.YELLOW}Uzel {self.peer} poslal {neprijate_za_sebou} neakceptovaných zpráv za sebou. Zavírám spojení.{Style.RESET_ALL}")
                            break
                    else:
                        neprijate_za_sebou = 0
        except (OSError, socket.timeout, struct.error):
            pass
        except Exception as e:
            self.node.add_log(f"{Fore.RED}Chyba čtecí smyčky spojení s {self.peer}: {e}{Style.RESET_ALL}")
        finally:
            self.close()

    def send(self, message):
        # OPRAVA AUDIT-2026-2 (nález 2, 2/2): `message` smí být i HOTOVÝ rámec
        # (bytes). _respond() si ho musí postavit tak jako tak, aby změřil
        # skutečnou délku odpovědi pro bajtový rozpočet; dřív ho zahodil a tahle
        # metoda ho vyrobila znovu, tedy 7 MiB serializace navíc na každou 7MiB
        # odpověď. Dict se dál rámuje tady, takže volající, kteří posílají
        # zprávy (request(), _send_to_single_peer()), se nemění.
        if not self.alive:
            return False
        try:
            data = message if isinstance(message, (bytes, bytearray)) else P2PNode._frame(message)
            with self.send_lock:
                self.sock.sendall(data)
            self.last_used = time.time()
            return True
        except (OSError, socket.timeout):
            self.close()
            return False

    def request(self, message, timeout=REQUEST_TIMEOUT):
        """Pošle dotaz a počká na odpověď. Vrací dict, nebo None při selhání."""
        rid = self.node.next_request_id()
        message = dict(message)
        message['request_id'] = rid
        waiter = queue.Queue(maxsize=1)
        with self.pending_lock:
            self.pending[rid] = waiter
        if not self.send(message):
            with self.pending_lock:
                self.pending.pop(rid, None)
            return None
        try:
            return waiter.get(timeout=timeout)
        except queue.Empty:
            # Timeout musí pending uklidit, jinak teče a sync se tiše zasekne.
            with self.pending_lock:
                self.pending.pop(rid, None)
            self.node.add_log(f"{Fore.YELLOW}Dotaz {message.get('type')} na {self.peer} vypršel po {timeout:.0f}s.{Style.RESET_ALL}")
            return None

    def close(self):
        if not self.alive:
            return
        self.alive = False
        try:
            self.sock.close()
        except Exception:
            pass
        # Všechny nevyřízené dotazy musí selhat, ne viset do timeoutu.
        with self.pending_lock:
            waiters = list(self.pending.values())
            self.pending.clear()
        for w in waiters:
            try:
                w.put_nowait(None)
            except Exception:
                pass
        self.node.drop_connection(self.peer, self)


class P2PNode:
    def __init__(self, blockchain, host, port, initial_peers):
        self.node_id = binascii.hexlify(os.urandom(8)).decode()
        self.blockchain = blockchain
        self.host = host
        self.port = port
        # OPRAVA T-4 (Nález 1): jediné místo, které ručí za invariant "self.peers
        # obsahuje výhradně kanonické tvary IP". Dřív byly normalizované jen
        # peer_listen_ports a peer_listen_seen, kdežto peers, protected_peers
        # a peer_last_seen držely to, co přišlo od uživatele - a právě ten
        # rozpor způsoboval dvojí evidenci jednoho hostitele. Normalizuje se
        # tady, ne až u jednotlivých čtení, aby se nemohlo stát, že na nový
        # způsob zápisu někdo zapomene.
        normalized_peers, _ = normalize_peer_list(initial_peers)
        self.peers = normalized_peers
        self.peers_lock = threading.Lock()
        # OPRAVA U-20 (audit 7. 10. 2026, nález 2): klíčem už není samotná IP,
        # ale dvojice (IP, node_id) -> naslouchací port. Slovník IP -> jeden port
        # znamenal, že uzel umí mluvit vždy jen s JEDNÍM uzlem na dané adrese:
        # druhý handshake ze stejné IP první záznam přepsal, resolve_peer_addr()
        # pak směrovala žádosti i odpovědi na nesprávný uzel a uzel trvale uvízl
        # na lehčí větvi - bez chyby, bez banu, bez jediného varovného řádku.
        #
        # node_id protokol nese už dnes (viz handshake níž), používal se ale jen
        # na detekci spojení k sobě samému. Je to přesně ten rozlišovač, který
        # tu chyběl: podle něj se pozná "tentýž uzel změnil port" (přepsat) od
        # "jiný uzel na téže IP" (přidat).
        #
        # Peery z peers.json a z menu známe jen adresou, node_id se dozvíme až
        # z jejich handshaku. Do té doby dostanou provizorní klíč odvozený od
        # portu (_provisional_node_id) - ten je v rámci IP jednoznačný a první
        # skutečný handshake ho nahradí.
        self.peer_listen_ports = {
            (ip, self._provisional_node_id(port)): port for ip, port in normalized_peers
        }
        # OPRAVA D-08: peery zadané ručně (peers.json / volba v menu) se nikdy
        # nevytlačují automaticky. Bez toho by útočník mohl vytlačit i ty uzly,
        # přes které se dá spojení se sítí obnovit.
        self.protected_peers = set(normalized_peers)
        # Skóre = čas poslední ÚSPĚŠNÉ interakce. Peer, se kterým se dlouho
        # nepovedlo nic, je první na vyhození.
        now = get_time()
        self.peer_last_seen = {peer: now for peer in normalized_peers}
        # Čas posledního zápisu do peer_listen_ports, kvůli TTL. Klíč je týž
        # jako u peer_listen_ports, tedy (IP, node_id) - viz OPRAVA U-20.
        self.peer_listen_seen = {
            (ip, self._provisional_node_id(port)): now for ip, port in normalized_peers
        }
        self.server_thread = threading.Thread(target=self.start_server)
        self.running = True
        self.bind_ready = threading.Event()
        self.sync_thread = threading.Thread(target=self.sync_chain_periodically)
        self.sync_thread.daemon = True
        # OPRAVA G-05: místo queue.Queue() bez maxsize je log kruhový buffer.
        # Spotřeba paměti je shora omezená bez ohledu na to, jak dlouho uzel
        # běží a co na něj kdo posílá. Počítadlo zahozených záznamů se ukáže
        # při čtení, aby uživatel poznal, že o něco přišel.
        #
        # OPRAVA N1 (nález N1): deque už NENÍ maxlen=N. Vytěsňování si dělá
        # _p2p_log_append_locked() samo, protože vedle počtu řádků musí držet
        # i BAJTOVÝ strop - a maxlen zahodí nejstarší záznam potichu, takže by
        # se k němu průběžný součet bajtů nedal snížit a tiše by se rozešel se
        # skutečností (táž past jako u OPRAVY S-2, kde se do účetnictví sync
        # bufferu přičítalo něco, co v tabulce nepřibylo).
        self.p2p_log = deque()
        self.p2p_log_lock = threading.Lock()
        self.p2p_log_dropped = 0
        self.p2p_log_bytes = 0
        # Potlačení opakujících se hlášek: zaplavovací útok posílá tutéž
        # zprávu tisíckrát, takže z ní nově vznikne jeden řádek a počítadlo.
        self._p2p_log_last = None
        self._p2p_log_repeat = 0
        # OPRAVA #1: token buckets místo seznamu časových razítek.
        # rate_buckets   = levné zprávy / navazovaná spojení
        # expensive_buckets = drahé dotazy (request_blocks, request_full_chain, ...)
        # rate_overflow  = počítadlo dlouhodobého překračování, teprve to vede na ban
        # ETAPA 1: pool perzistentních odchozích spojení a čítač request_id.
        self.connections = {}
        self.connections_lock = threading.Lock()
        self.request_counter = itertools.count(1)
        self.request_counter_lock = threading.Lock()

        # OPRAVA N2 (audit 10. 10. 2026, nález N2): strop souběžných odchozích
        # pokusů a evidence, kdy jsme které IP naposled poslali vyžádaný
        # 'request_chain_info'. Obojí viz _spawn_send() a _muze_zadat_chain_info().
        self.outbound_semaphore = threading.BoundedSemaphore(MAX_OUTBOUND_SEND_THREADS)
        self.chain_info_asked = {}

        self.rate_lock = threading.Lock()
        self.conn_buckets = {}
        self.expensive_byte_buckets = {}
        self.rate_buckets = {}
        self.expensive_buckets = {}
        self.rate_overflow = {}
        # OPRAVA K-2: značka pro periodický úklid kbelíků,
        # stejný vzorec jako blacklist_last_prune. Taktéž time.time(), ne
        # get_time() - rozpočty nesmí záviset na síťovém offsetu.
        self.rate_buckets_last_prune = time.time()
        self.blacklist_lock = threading.Lock()
        self.blacklist = load_blacklist()
        # OPRAVA G-06: stav pro dávkovaný zápis a periodický úklid.
        # dirty = v paměti je změna, která ještě není na disku.
        self.blacklist_dirty = False
        self.blacklist_last_flush = 0.0
        # Blacklist pracuje důsledně s time.time(), ne s get_time() - expirace
        # banu nesmí záviset na síťovém offsetu, který uzly mezi sebou ladí.
        self.blacklist_last_prune = time.time()
        # OPRAVA AUDIT-2026-8 (nález N3): týž pár příznaků pro tabulku peerů. Hlídá je
        # peers_lock, pod kterým se tabulka stejně mění - vlastní zámek by
        # jen přidal pořadí, které je třeba dodržet.
        self.peers_dirty = False
        self.peers_last_flush = 0.0
        # OPRAVA AUDIT-2026-6 (nález N1): komu už jsme poslali handshake.
        # Drží se jen pro peery z tabulky, takže je shora omezená stejně jako
        # ona (MAX_MANUAL_PEERS_TOTAL); uklízí ji _uklid_evidence_peeru_locked()
        # spolu s peer_last_seen a offline_peers.
        self.handshake_sent = {}
        # OPRAVA AUDIT-2026-15 (audit 27. 10. 2026, nálezy 2 a 5): evidence
        # nedostupných peerů patří sem, ne do líného `if not hasattr(...)`.
        #
        # Líné vytváření bylo samo malým souběhem: dvě odchozí vlákna mohla
        # obě projít testem hasattr a obě přiřadit čerstvou množinu, takže
        # zápis jednoho z nich zmizel a hláška "je offline" se pro téhož peera
        # vypsala dvakrát. Je to táž třída problému jako zbytek nálezu 2, jen
        # o jednu úroveň výš, a u atributu, který existuje po celou dobu života
        # uzlu, není pro líné vytváření žádný důvod.
        #
        # Množina drží peery, o kterých víme, že jsou nedostupní. Smysl je
        # jediný: hlásit PŘECHOD stavu, ne každý neúspěšný pokus. Zapisuje se
        # výhradně přes _oznac_peer_offline() / _oznac_peer_online(), které si
        # berou peers_lock, protože tutéž množinu prochází
        # _uklid_evidence_peeru_locked() pod tímtéž zámkem.
        self.offline_peers = set()
        # OPRAVA W-3 (audit 9. 10. 2026, nález N-3): token bucket místo seznamu
        # časových razítek. Stejná dvojice struktur jako u is_rate_limited():
        # kbelík na burst a počítadlo dlouhodobého překračování, které jediné
        # vede na ban.
        self.tx_buckets = {}
        self.tx_overflow = {}
        # OPRAVA W-2 (audit 9. 10. 2026, nález N-2): evidence už přeposlaných
        # bloků a transakcí. Množina pro test, deque pro pořadí - viz
        # _uz_preposlano().
        self.relay_lock = threading.Lock()
        self.relay_seen = set()
        self.relay_order = deque()
        # OPRAVA Y-5 (audit 14. 10. 2026, nález 5): branka pro
        # 'response_full_chain' má nově stejný tvar jako ta mempoolová - mapa
        # normalizovaná IP -> čas, do kdy jsme od ní odpověď ochotni přijmout.
        # Dřív to byl prostý bool bez expirace, takže se po jediném nezodpovězeném
        # request_full_chain už nikdy nezavřel.
        self.awaiting_full_chain = {}
        self.awaiting_full_chain_lock = threading.Lock()
        self.syncing_fork = False
        # OPRAVA F-04: branka pro 'response_mempool'. Mapa normalizovaná IP ->
        # čas, do kdy jsme od ní ochotni odpověď na náš request_mempool přijmout.
        # Bez ní mohl kdokoli po handshaku poslat nevyžádanou dávku transakcí -
        # jediná zpráva obešla rozpočet transakcí 166násobně.
        self.awaiting_mempool = {}
        self.awaiting_mempool_lock = threading.Lock()
        # OPRAVA W-5 (audit 9. 10. 2026, nález N-2b): kurzor rotace mempoolové
        # odpovědi, normalizovaná IP -> (klíč poslední odeslané transakce, čas).
        self.mempool_offer_lock = threading.Lock()
        self.mempool_offer_cursor = {}
        # OPRAVA U-19 (audit 7. 10. 2026, nález 1): stavový automat stahování
        # forku neměl ŽÁDNÝ zámek. syncing_fork se v handleru response_blocks
        # přečte, a teprve o dvě otevření SQLite a mazání souborů dál se zapíše;
        # dvě vlákna tedy obě viděla False a obě prošla větví, která volá
        # discard_sync_buffer(). To okno je v řádu milisekund, na flash paměti
        # telefonu i delší, a dvě odpovědi naráz nejsou výjimka, ale BĚŽNÝ stav -
        # sync_chain_periodically() spouští vlákno na každého peera zároveň.
        # Naměřeno 37 ze 40 kol, kdy kritickou větví prošla obě vlákna.
        #
        # Zámek drží celý PŘECHOD: test příznaku, případné zahození bufferu,
        # zápis příznaků i init_sync_buffer(). Příznak se uvnitř zámku čte
        # ZNOVU - původní hodnota z doby před jeho získáním je bezcenná.
        #
        # RLock, ne Lock: _abort_fork_sync() si zámek bere taky a volá se jak
        # zevnitř přechodu, tak z _store_fork_batch() mimo něj. S nereentrantním
        # zámkem by první cesta uzel natrvalo zamrazila - přesně failure mode
        # OPRAVY F-01, kde si jedna metoda vzala nereentrantní peers_lock
        # podruhé a stála celá P2P vrstva. Zámek se zásadně nedrží přes čekání
        # na síť; pořadí vůči peers_lock je vždy fork_lock -> peers_lock.
        self.fork_lock = threading.RLock()
        # ETAPA 3: stahování jednoho forku je vázané na JEDEN uzel. Míchání
        # zdrojů znamená, že nelze určit, kdo dodal vadný blok, a hlavně vede
        # na banování poctivých uzlů - viz komentář v _store_fork_batch().
        self.fork_peer_ip = None
        self.fork_start_index = None
        # OPRAVA A-3: účetní počítadlo bajtů zapsaných do sync_buffer.db.
        self.sync_buffer_bytes = 0
        self.fork_sync_start = 0
        self.SYNC_BUFFER_DB = 'sync_buffer.db'
        # OPRAVA AUDIT-2026-1 (nález 1): dvojice (fork_start_index, expirace)
        # posledního forku, o kterém víme, že se do rozpočtu sync bufferu
        # nevejde a jeho stažitelný prefix naši větev nepřebíjí. Drží se JEDNA
        # položka, ne slovník: uzel stahuje nejvýš jeden fork naráz (ETAPA 3),
        # takže víc jich zároveň vzniknout nemůže a struktura nemá jak růst.
        self.fork_neprosaditelny = None
        # OPRAVA N3 (audit 10. 10. 2026, nález N3): čas posledního ÚSPĚŠNÉHO
        # zápisu do sync bufferu a evidence IP, kterým nad rozpracovaným forkem
        # vypršel watchdog. První rozhoduje, jestli je buffer rozpracovaná práce
        # (a tedy chráněný před cizím nárokem), druhá brání tomu, aby si slot
        # šlo držet trvale přehráváním jednoho a téhož bloku.
        #
        # fork_sync_start se na to použít nedá: watchdog ho při vypršení nuluje
        # a _resume_fork_sync() ho posouvá při každém pokusu o obnovu, takže
        # neměří stáří OBSAHU bufferu, ale stáří naší poslední snahy.
        self.fork_last_progress = 0
        self.fork_slot_cooldown = {}
        # OPRAVA AUDIT-2026-3 (nález 3): globální rezervace přijímací paměti
        # a per-IP bajtový kbelík. Oboje se inicializuje TADY, ne až
        # ve start_server() jako inbound_total - handle_client_connection()
        # i PeerConnection._read_loop() se volají z vláken, která mohou běžet
        # dřív, než server dokončí bind.
        self.inbound_buffer_lock = threading.Lock()
        self.inbound_buffer_bytes = 0
        self.inbound_byte_buckets = {}
        # OPRAVA Z-1 (nález 1): evidence příchozích spojení. Dřív vznikala až
        # ve start_server() ZA bindem; stěhuje se sem ze stejného důvodu, jaký
        # popisuje komentář o tři řádky výš - na struktury sahá i obslužné
        # vlákno a spoléhat na pořadí startu je zbytečná past.
        #
        # inbound_conns je kanonický seznam ŽIVÝCH příchozích spojení; čítače
        # jsou z něj odvozená data (stejný vztah jako mempool_by_txid vs.
        # unconfirmed_transactions po OPRAVĚ D-04). Aby se nemohly rozejít,
        # mění je VÝHRADNĚ _inbound_admit() a _inbound_release().
        self.inbound_lock = threading.Lock()
        self.inbound_total = 0
        self.inbound_per_ip = defaultdict(int)
        self.inbound_per_subnet = defaultdict(int)
        self.inbound_conns = {}
        self.inbound_seq = itertools.count(1)

    def _inbound_je_znamy(self, ip):
        """OPRAVA Z-1 (nález 1): je tahle IP uzel, který už známe?

        Známý = figuruje v tabulce peerů nebo mezi ručně zadanými
        (protected_peers). Takovému uzlu patří rezerva INBOUND_RESERVED_FOR_KNOWN
        a nesmí být vytěsněn.

        Porovnává se KANONICKÝ tvar adresy, ne syrový řetězec - jinak by se
        záznam z accept() nespároval se záznamem z peers.json, což je přesně
        chyba, kterou OPRAVA T-4 odstranila v tabulce peerů.

        Volá se MIMO inbound_lock: bere peers_lock a vnořovat dva zámky na cestě
        dosažitelné ze sítě je past, kterou kód jednou zaplatil (OPRAVA F-01).
        """
        if not ip:
            return False
        with self.peers_lock:
            for p in self.peers:
                if self.normalize_ip(p[0]) == ip:
                    return True
            for p in self.protected_peers:
                if self.normalize_ip(p[0]) == ip:
                    return True
        return False

    def _inbound_vyber_obet_locked(self, novy_subnet, novy_znamy):
        """OPRAVA Z-1 (nález 1): koho vytěsnit, aby se nový uzel vešel.

        Volat POUZE s drženým inbound_lock. Vrací záznam oběti, nebo None.

        Pravidla, obě podstatná (táž konstrukce jako _evict_for u mempoolu):

          1) Obětí smí být VÝHRADNĚ spojení od neznámého uzlu. Peer z tabulky
             se vytěsnit nedá nikdy - jinak by rezerva nebyla rezerva.
          2) Neznámý nový uzel smí vytěsnit jen z prefixu, který je PO VÝMĚNĚ
             pořád aspoň tak zastoupený jako ten jeho:
                 pocet[obet] > pocet[novy] + 1
             Tím je vytěsnění monotónní - vždy srovnává koncentraci - a nemůže
             se zacyklit: po výměně má obětní prefix pocet-1 a nový pocet+1,
             takže zpětné vytěsnění by vyžadovalo nerovnost, která právě
             neplatila. Bez toho by se dva neznámí uzly vyhazovali donekonečna
             a vytěsňování by se samo stalo útokem.

        Známý nový uzel pravidlo 2 nepotřebuje: rezerva mu místo drží sama,
        tohle je druhá linie pro případ, že si ji vyčerpají známé uzly navzájem.

        Z kandidátů se bere NEJVÍC ZASTOUPENÝ prefix a v něm NEJDÉLE NEČINNÉ
        spojení - útočník je ze své podstaty ten koncentrovaný, poctivé uzly
        jsou rozptýlené.
        """
        nejlepsi = None
        nejlepsi_klic = None
        for zaznam in self.inbound_conns.values():
            if zaznam.znamy:
                continue
            pocet = self.inbound_per_subnet.get(zaznam.subnet, 0)
            if not novy_znamy and pocet <= self.inbound_per_subnet.get(novy_subnet, 0) + 1:
                continue
            # Vyšší zastoupení prefixu vyhrává, při shodě starší aktivita.
            klic = (pocet, -zaznam.last_active)
            if nejlepsi_klic is None or klic > nejlepsi_klic:
                nejlepsi_klic = klic
                nejlepsi = zaznam
        return nejlepsi

    def _inbound_zrus_locked(self, zaznam):
        # Odebere záznam z evidence a sníží čítače. Volat POUZE s drženým
        # inbound_lock. Idempotentní: druhé volání nad týmž záznamem už nic
        # neodečte, takže se čítače nemůžou dostat pod nulu ani když se potkají
        # vytěsnění a doběh obslužného vlákna.
        if self.inbound_conns.pop(zaznam.cid, None) is None:
            return False
        self.inbound_total -= 1
        if self.inbound_total < 0:
            self.inbound_total = 0
        self.inbound_per_ip[zaznam.ip] -= 1
        if self.inbound_per_ip[zaznam.ip] <= 0:
            del self.inbound_per_ip[zaznam.ip]
        self.inbound_per_subnet[zaznam.subnet] -= 1
        if self.inbound_per_subnet[zaznam.subnet] <= 0:
            del self.inbound_per_subnet[zaznam.subnet]
        return True

    def _inbound_admit(self, sock, addr):
        """OPRAVA Z-1 (nález 1): rozhodne o přijetí příchozího spojení.

        Vrací (zaznam, obet, duvod):
          zaznam != None -> spojení přijato a zapsáno do evidence,
          obet   != None -> volající MUSÍ na jeho socketu zavolat shutdown(),
                            a to AŽ MIMO zámek,
          duvod          -> text do logu, když se nepřijalo.

        Proč shutdown() a ne close(): zavřít socket, na kterém jiné vlákno visí
        v recv(), uvolní deskriptor, a ten může accept() vzápětí přidělit NOVÉMU
        spojení - staré vlákno by pak četlo cizí data. shutdown() deskriptor
        nechá být, jen probudí recv() s koncem proudu; obslužné vlákno doběhne
        normální cestou a socket zavře jeho vlastní `with conn:`.

        Čítače se u oběti snižují HNED, ne až v jejím finally. Slot je tím volný
        okamžitě a po dobu, než oběť doběhne, může být živých vláken o pár víc
        než MAX_INBOUND_CONNECTIONS - přechodně a shora omezeně, protože
        vytěsnění spouští jen accept, a ten je sám omezený
        is_connection_rate_limited(). Opačné pořadí (čekat na doběh) by znamenalo
        přijmout nové spojení, na které ještě není místo.
        """
        ip = self.normalize_ip(addr[0])
        subnet = self.subnet_key(ip)
        # Mimo zámek - viz _inbound_je_znamy().
        znamy = self._inbound_je_znamy(ip)
        obet = None
        with self.inbound_lock:
            # Čte se přes .get(), ne indexací. Oba slovníky jsou defaultdict,
            # takže by indexace při ODMÍTNUTÍ založila klíč s nulou, který už
            # nikdo nikdy nesmaže - a klíč si vybírá útočník. Z jednoho /64
            # prefixu je to neomezený růst za cenu jednoho SYN na adresu, tedy
            # táž třída úniku, jakou řešily OPRAVY #10 (peer_listen_ports),
            # G-06 (blacklist) a AUDIT-2026-4 (offline_peers). Klíč smí vzniknout
            # jedině PŘIJETÍM spojení, a to je shora omezené
            # MAX_INBOUND_CONNECTIONS.
            if self.inbound_per_ip.get(ip, 0) >= MAX_INBOUND_PER_IP:
                return None, None, f"na IP {ip} už běží {MAX_INBOUND_PER_IP} příchozích spojení"
            if not znamy and self.inbound_per_subnet.get(subnet, 0) >= MAX_INBOUND_PER_SUBNET:
                # Prefix si svůj strop vyčerpal. Vytěsňovat tu nemá co - oběť by
                # byla z téhož prefixu, takže by se nic nezměnilo.
                return None, None, (f"prefix {subnet} už má {MAX_INBOUND_PER_SUBNET} "
                                    f"příchozích spojení (strop na prefix)")
            strop = MAX_INBOUND_CONNECTIONS if znamy else (MAX_INBOUND_CONNECTIONS
                                                           - INBOUND_RESERVED_FOR_KNOWN)
            if self.inbound_total >= strop:
                obet = self._inbound_vyber_obet_locked(subnet, znamy)
                if obet is None:
                    return None, None, (f"příchozích spojení je {self.inbound_total}, strop pro "
                                        f"{'známý' if znamy else 'neznámý'} uzel je {strop} "
                                        f"a není koho vytěsnit")
                self._inbound_zrus_locked(obet)
                obet.vytesnen = True

            zaznam = SimpleNamespace(
                cid=next(self.inbound_seq), ip=ip, subnet=subnet, znamy=znamy,
                last_active=time.time(), vytesnen=False, sock=sock)
            self.inbound_conns[zaznam.cid] = zaznam
            self.inbound_total += 1
            self.inbound_per_ip[ip] += 1
            self.inbound_per_subnet[subnet] += 1
        return zaznam, obet, None

    def _inbound_release(self, zaznam):
        # Protějšek _inbound_admit(). Volá se VÝHRADNĚ z finally obslužného
        # vlákna; u vytěsněného spojení už záznam v evidenci není a neodečte se
        # tedy podruhé (viz _inbound_zrus_locked).
        if zaznam is None:
            return
        with self.inbound_lock:
            self._inbound_zrus_locked(zaznam)

    @staticmethod
    def _inbound_touch(zaznam):
        # Značka poslední aktivity, podle které se vybírá nejdéle nečinné
        # spojení. Bez zámku ZÁMĚRNĚ: je to jedno přiřazení floatu (pod GILem
        # atomické) a čtenář ho jen porovnává, takže zastaralá hodnota nanejvýš
        # posune pořadí kandidátů. Brát kvůli tomu inbound_lock na každou
        # přijatou zprávu by byl zámek navíc v nejteplejší cestě uzlu.
        if zaznam is not None:
            zaznam.last_active = time.time()

    def get_locator_hashes(self):
        # OPRAVA #9: dřív se posílalo až LAST_BLOCKS_TO_KEEP (1200) po sobě
        # jdoucích hashů. Protokol z nich stejně použije jen první, který
        # protistrana zná, takže stačí exponenciálně řídnoucí posloupnost:
        # posledních 10 bloků po jednom, pak krok 2, 4, 8, ... To pokryje
        # stejnou hloubku ~32 hashi místo 1200.
        locator = []
        # OPRAVA L-3: conn.close() leželo až na konci try, takže při výjimce
        # uprostřed (poškozený řádek, zamčená DB) spojení zůstalo otevřené.
        conn = None
        try:
            conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
            conn.execute("PRAGMA journal_mode=WAL;")
            c = conn.cursor()
            c.execute("SELECT MAX(block_index) FROM blocks")
            row = c.fetchone()
            tip = row[0] if row and row[0] is not None else None
            if tip is not None:
                indices = []
                idx = tip
                step = 1
                count = 0
                while idx >= 0 and len(indices) < MAX_LOCATOR_HASHES:
                    indices.append(idx)
                    count += 1
                    if count > 10:
                        step *= 2
                    idx -= step
                if 0 not in indices and len(indices) < MAX_LOCATOR_HASHES:
                    indices.append(0)
                placeholders = ','.join('?' for _ in indices)
                c.execute(f"SELECT block_index, block_hash FROM blocks WHERE block_index IN ({placeholders})", tuple(indices))
                found = {r[0]: r[1] for r in c.fetchall()}
                locator = [found[i] for i in indices if i in found]
        except Exception:
            pass
        finally:
            if conn is not None:
                try:
                    conn.close()
                except Exception:
                    pass
        return locator

    def init_sync_buffer(self, reset=True):
        # OPRAVA #6c: DROP TABLE se nově dělá jen když opravdu začínáme nový
        # fork (reset=True). Při navazování na rozpracovaný buffer se tabulka
        # zachová, jinak by každý pokus začínal od nuly a hluboký reorg by se
        # nad hraničním RTT nedotáhl nikdy.
        # OPRAVA L-3: spojení bez try/finally. Volá se ze síťové cesty při
        # každém zahájení i navázání fork syncu; selhání DROP/CREATE (plný disk,
        # zamčená DB) tu nechalo deskriptor viset.
        conn = None
        try:
            conn = sqlite3.connect(self.SYNC_BUFFER_DB, timeout=1.0)
            conn.execute("PRAGMA journal_mode=WAL;")
            c = conn.cursor()
            if reset:
                c.execute("DROP TABLE IF EXISTS sync_blocks")
            c.execute('''
                CREATE TABLE IF NOT EXISTS sync_blocks (
                    block_index INTEGER PRIMARY KEY,
                    timestamp INTEGER,
                    transactions TEXT,
                    previous_hash TEXT,
                    target_hex TEXT,
                    nonce INTEGER,
                    block_hash TEXT,
                    merkle_root TEXT,
                    version INTEGER,
                    chain_id INTEGER,
                    state_root TEXT
                )
            ''')
            conn.commit()
            # OPRAVA A-3: počítadlo bajtů musí sedět i při navazování na
            # rozpracovaný buffer (reset=False), jinak by strop po timeoutu začal
            # počítat od nuly a útočník by ho obešel pouhým přerušením přenosu.
            if reset:
                self.sync_buffer_bytes = 0
            else:
                try:
                    # OPRAVA T-1 (Nález 1, 2/2): měří se celý řádek, ne jen
                    # sloupec transactions - viz SYNC_BUFFER_BYTES_SQL.
                    c.execute(SYNC_BUFFER_BYTES_SQL)
                    self.sync_buffer_bytes = int(c.fetchone()[0] or 0)
                except Exception:
                    self.sync_buffer_bytes = 0
        finally:
            if conn is not None:
                try:
                    conn.close()
                except Exception:
                    pass

    @staticmethod
    def _sync_row_values(bd, tx_json):
        # OPRAVA T-1 (Nález 1, 2/2): jediné místo, kde se skládá řádek bufferu.
        # Používá ho INSERT i účtování bajtů - kdyby si každý sestavoval řádek
        # po svém, strop by se dal obejít v rozdílu mezi nimi (přesně to se
        # stalo: zapisovalo se 11 sloupců, účtoval se jeden).
        # Pořadí MUSÍ odpovídat SYNC_BUFFER_COLUMNS i sloupcům v INSERTu.
        return (bd['index'], bd['timestamp'], tx_json, bd['previous_hash'],
                bd['target'], bd['nonce'], bd['hash'], bd['merkle_root'],
                bd.get('version', BLOCK_VERSION), bd.get('chain_id', CHAIN_ID),
                bd.get('state_root'))

    def sync_buffer_tip(self):
        # OPRAVA #6c: (index, hash) posledního bloku v bufferu, nebo None.
        # Používá se k navázání po timeoutu, aby se přenesený pokrok neztratil.
        try:
            if not os.path.exists(self.SYNC_BUFFER_DB):
                return None
            # OPRAVA L-3: conn.close() bylo uvnitř try, takže selhání dotazu
            # (poškozený buffer) spojení nezavřelo - a tahle metoda se volá
            # z watchdogu každých 10 s.
            conn = None
            try:
                conn = sqlite3.connect(self.SYNC_BUFFER_DB, timeout=1.0)
                c = conn.cursor()
                c.execute("SELECT block_index, block_hash FROM sync_blocks ORDER BY block_index DESC LIMIT 1")
                row = c.fetchone()
            finally:
                if conn is not None:
                    try:
                        conn.close()
                    except Exception:
                        pass
            if row:
                return (row[0], row[1])
        except Exception:
            pass
        return None

    @staticmethod
    def _soucet_prace(cursor):
        """Součet PoW práce přes sloupec target_hex otevřeného kurzoru.

        Vrací (práce, počet bloků), nebo None, když je některý target
        nečitelný. None znamená "nevím" - viz _prefix_muze_vyhrat().

        Vzorec (1 << 256) // target je TÝŽ, jaký používá
        update_state_with_block(), get_cumulative_work() i replace_chain();
        kdyby se rozešel, rozhodovalo by se tu podle jiné veličiny, než jakou
        pak posoudí replace_chain().
        """
        prace = 0
        pocet = 0
        for radek in cursor:
            try:
                target = int(radek[0], 16) if isinstance(radek[0], str) else int(radek[0])
            except (TypeError, ValueError):
                return None
            if target <= 0:
                return None
            prace += (1 << 256) // target
            pocet += 1
        return prace, pocet

    def _prace_bufferu(self):
        # OPRAVA AUDIT-2026-1 (nález 1): práce a počet bloků ležících v sync
        # bufferu. None = nedokážeme spočítat.
        if not os.path.exists(self.SYNC_BUFFER_DB):
            return None
        conn = None
        try:
            conn = sqlite3.connect(self.SYNC_BUFFER_DB, timeout=1.0)
            c = conn.cursor()
            c.execute("SELECT target_hex FROM sync_blocks")
            vysledek = self._soucet_prace(c)
        except (sqlite3.Error, OSError, OverflowError):
            return None
        finally:
            if conn is not None:
                try:
                    conn.close()
                except Exception:
                    pass
        if vysledek is None or vysledek[1] == 0:
            return None
        return vysledek

    def _prace_nasich_bloku_od(self, od_indexu):
        # OPRAVA AUDIT-2026-1 (nález 1): práce a počet NAŠICH bloků od zadaného
        # indexu výš, tedy přesně těch, které by reorg zahodil.
        #
        # Čte se cíleně přes WHERE block_index >= ?, ne přes
        # get_cumulative_work(up_to_index=...), která dělá sken celého řetězce
        # od genesis. Tady je počet řádků shora omezený kontrolou
        # hloubka_reorgu <= MAX_REORG_DEPTH, která proběhla o kus výš, takže je
        # dotaz levný i nad dlouhým řetězcem.
        conn = None
        try:
            conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
            c = conn.cursor()
            c.execute("SELECT target_hex FROM blocks WHERE block_index >= ?", (od_indexu,))
            vysledek = self._soucet_prace(c)
        except (sqlite3.Error, OSError, OverflowError):
            return None
        finally:
            if conn is not None:
                try:
                    conn.close()
                except Exception:
                    pass
        return vysledek

    def _prefix_muze_vyhrat(self, fork_start):
        """OPRAVA AUDIT-2026-1 (nález 1): smí se neúplný prefix z bufferu poslat
        do replace_chain()?

        Buffer má dva stropy (hloubkový a bajtový) a po jejich dosažení se
        dosud BEZPODMÍNEČNĚ volal process_sync_buffer(). Komentář u OPRAVY N-1
        to zdůvodňoval slovy "typicky už těžší než naše větev" - jenže se to
        nijak neověřovalo. replace_chain() přitom porovnává práci prefixu
        s prací NAŠÍ CELÉ větve, takže prefix vyhraje jen tehdy, když přebije
        všechny naše bloky nad bodem forku. U plných bloků se do bufferu vejde
        ~62 bloků, takže pro naši větev delší než ~62 bloků prefix prohraje
        VŽDY - a po odmítnutí discard_sync_buffer() buffer smaže a
        sync_chain_periodically() celé kolo za 10 s zopakuje. Ověřeno
        t10_buffer_strop.py: tip uzlu se nehnul ve třech kolech po sobě.

        Rozhodovací pravidlo je ZÁMĚRNĚ totožné s replace_chain():
          větší práce                        -> může vyhrát
          stejná práce a nejsme kratší       -> může vyhrát (rozhodne hash)
          jinak                              -> prohraje jistě
        Kdyby se rozešlo, zamítali bychom tu fork, který by replace_chain()
        přijal, nebo naopak pouštěli dál práci, o které dopředu víme, jak
        dopadne.

        Při NEJISTOTĚ (neznámý fork_start, nečitelný target) se vrací True:
        rozhodnutí pak udělá replace_chain() nad plnými daty, tedy přesně jako
        před touto opravou. Je to táž úvaha jako u MissingChainDataError - při
        nejistotě se nehádá; jen tady je bezpečná strana ta, která nic nemaže.
        """
        if fork_start is None:
            return True
        buf = self._prace_bufferu()
        nas = self._prace_nasich_bloku_od(fork_start)
        if buf is None or nas is None:
            return True
        buf_prace, buf_pocet = buf
        nas_prace, nas_pocet = nas
        if buf_prace > nas_prace:
            return True
        if buf_prace == nas_prace and buf_pocet >= nas_pocet:
            return True
        return False

    def _prefix_neprebiji(self, fork_start, duvod_stropu):
        # OPRAVA AUDIT-2026-1 (nález 1): společná cesta ven, když je buffer plný
        # a jeho obsah naši větev nepřebíjí.
        #
        # Buffer se ZAHAZUJE, přestože návrh auditu zní "ponechat a pokračovat
        # ve stahování". Ponechat ho nemá smysl právě proto, že je plný: další
        # blok se do něj nevejde, takže pokračovat stejně nelze a na flash by
        # jen ležel nepoužitelný soubor. Rozhodující je backoff - ten zastaví
        # opakované stahování, které byl vlastní obsah nálezu.
        #
        # Žádný ban: jiná, delší větev není důkaz zlého úmyslu a poctivý uzel
        # za náš paměťový rozpočet nemůže. Stejná úvaha jako u OPRAVY N-1.
        self.add_log(
            f"{Fore.YELLOW}Fork od #{fork_start} se do sync bufferu nevejde celý "
            f"({duvod_stropu}) a stažený prefix nepřebíjí naši větev - "
            f"replace_chain() by ho zaručeně odmítl.{Style.RESET_ALL}")
        self.add_log(
            f"{Fore.YELLOW}Reorg této hloubky uzel při MAX_SYNC_BUFFER_BYTES = "
            f"{MAX_SYNC_BUFFER_BYTES // (1024 * 1024)} MiB dokončit nedokáže. Buffer "
            f"zahazuji a dalších {FORK_UNWINNABLE_BACKOFF_SECONDS} s se o tentýž fork "
            f"nepokusím, ať se nestahuje donekonečna.{Style.RESET_ALL}")
        self.fork_neprosaditelny = (fork_start, time.time() + FORK_UNWINNABLE_BACKOFF_SECONDS)
        self._abort_fork_sync(None, "fork přesahuje rozpočet sync bufferu", ban=False)

    def _fork_zbyva_backoff(self, fork_start):
        # OPRAVA AUDIT-2026-1 (nález 1): kolik sekund ještě zbývá backoffu pro
        # tenhle bod forku. 0 = nic nebrání. Vypršelý záznam se rovnou zahodí.
        #
        # Klíčem je fork_start_index, ne IP: nedosažitelný je FORK, ne
        # protistrana. Mělčí fork od téhož uzlu projde dál, stejně jako tentýž
        # fork od kohokoli jiného zůstane nedosažitelný.
        zaznam = getattr(self, 'fork_neprosaditelny', None)
        if not zaznam:
            return 0
        index, expirace = zaznam
        if time.time() >= expirace:
            self.fork_neprosaditelny = None
            return 0
        if index != fork_start:
            return 0
        return int(expirace - time.time())

    def _davka_nese_nove_bloky(self, blocks_data):
        """OPRAVA K-1 (audit 21. 10. 2026, nález 1): obsahuje dávka aspoň jeden blok,
        který v blockchain.db NEMÁME?

        Nárok na fork slot smí vznést jen nabídka konkurenční VĚTVE. Dávka
        složená z bloků, které už v řetězci máme, žádnou alternativu nenabízí -
        replace_chain() ji po dokončení stahování stejně zahodí hláškou
        "Buffer končí blokem, který už je naším vrcholem". Její jediný skutečný
        efekt by tedy bylo zahození CIZÍ rozpracované práce, a to je přesně to,
        čemu OPRAVY H-1 a P-1 zabránily na ostatních cestách.

        Proč to nestačí řešit v _prace_davky(): ta měří práci, a práce
        přehraných bloků je skutečná - vytěžil ji kdysi někdo, klidně my sami.
        Sečtená vyjde stejně vysoko jako u poctivé větve a bránu tedy projde.
        Rozhodující není kolik práce dávka nese, ale jestli nabízí něco, co
        ještě nemáme.

        Při nejistotě (DB nelze číst) se vrací True, tedy chování před touto
        opravou: nedostupnost vlastní databáze nesmí zablokovat reorg. Stejný
        směr fail-safe jako _prefix_muze_vyhrat().

        Dotazuje se na block_hash, který je v blocks UNIQUE indexem, takže jde
        o vyhledání v indexu, ne o průchod tabulkou. Dávky po dělí na bloky po
        900 kvůli SQLITE_MAX_VARIABLE_NUMBER, stejně jako tx_ids_in_chain().
        """
        hashe = {bd.get('hash') for bd in blocks_data if isinstance(bd, dict)}
        hashe.discard(None)
        if not hashe:
            return False
        conn = None
        try:
            conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
            c = conn.cursor()
            zname = set()
            hashe_l = list(hashe)
            CHUNK = 900
            for start in range(0, len(hashe_l), CHUNK):
                chunk = hashe_l[start:start + CHUNK]
                placeholders = ','.join('?' * len(chunk))
                c.execute(f"SELECT block_hash FROM blocks WHERE block_hash IN ({placeholders})", chunk)
                zname.update(row[0] for row in c.fetchall())
            return bool(hashe - zname)
        except (sqlite3.Error, OSError):
            return True
        finally:
            if conn is not None:
                try:
                    conn.close()
                except Exception:
                    pass

    def _prace_davky(self, blocks_data):
        """OPRAVA N3 (audit 10. 10. 2026, nález N3): součet PROKÁZANÉ práce dávky.

        Vrací None, jakmile některý blok neprojde PoW brankou - pak dávka
        neprokazuje nic a nesmí ničím hýbat. To je tu podstatné: práce se
        počítá jako (1 << 256) // target, tedy z hodnoty, kterou si blok
        deklaruje SÁM. Teprve _pow_branka_bloku() z toho dělá tvrzení
        podložené prací: ověří, že target není volnější než síťové minimum,
        že hash odpovídá hlavičce a že ho skutečně splňuje. Bez té branky by
        si útočník "víc práce" prostě napsal - což je přesně chyba, kterou
        OPRAVA #8 odstranila v _store_fork_batch.

        Cena je konstantní na blok (hash hlavičky, žádné parsování transakcí -
        viz Block.hlavicka_hash_z_dictu), takže se to vyplatí počítat i na
        cestě, kterou útočník zahlcuje.

        Vzorec je TÝŽ, jakým počítá práci update_state_with_block(),
        get_cumulative_work() i replace_chain(). Kdyby se rozešel, rozhodovalo
        by se tu podle jiné veličiny, než jakou pak posoudí replace_chain().

        OPRAVA K-1: každý hash se počítá JEN JEDNOU.
        Dávka tentýž blok klidně obsahuje stokrát - PoW brankou projde každá
        kopie (hash hlavičce odpovídá) a součet se tím nafoukne stokrát,
        aniž by vznikla jediná nová větev. replace_chain() přitom posuzuje
        práci VÝSLEDNÉHO řetězce, kde se duplikát uplatní jednou nebo vůbec.
        Bez deduplikace se tedy rozhoduje podle jiné veličiny, než jakou pak
        posoudí replace_chain() - tedy právě to, čemu má poslední odstavec
        výše zabránit. Naměřeno: 360 kopií jednoho bloku (6 unikátních) dalo
        šedesátinásobek skutečné práce.
        """
        prace = 0
        videne = set()
        for bd in blocks_data:
            if self._pow_branka_bloku(bd) is not None:
                return None
            bd_hash = bd.get('hash') if isinstance(bd, dict) else None
            if bd_hash in videne:
                continue
            videne.add(bd_hash)
            try:
                # OPRAVA AUDIT-2026-17: OverflowError, viz _pow_branka_bloku().
                # Tady je to druhá linie (PoW branka výš se vrátí dřív), ale
                # obě místa s týmž výrazem musí mít i týž except tuple.
                if not isinstance(bd['target'], (str, int)) or isinstance(bd['target'], bool):
                    return None
                target = int(bd['target'], 16) if isinstance(bd['target'], str) else int(bd['target'])
            except (TypeError, ValueError, KeyError, OverflowError):
                return None
            if target <= 0:
                return None
            prace += (1 << 256) // target
        return prace

    def _nabidka_prebiji_fork(self, blocks_data):
        """OPRAVA N3 (nález N3): nese nabízená dávka víc práce, než co už v bufferu leží?

        Tohle je jediné kritérium, podle kterého smí cizí nárok sáhnout na
        rozpracovaný fork - ani pořadí příchodu, ani to, kdo byl dřív. Prázdný
        (nebo nečitelný) buffer se počítá jako nulová práce, takže o nic
        nepřijdeme: v prvním případě není co ztratit, ve druhém je obsah stejně
        nepoužitelný.

        Vyžaduje se OSTŘE víc. Shodná práce tedy slot nepřebírá - jinak by dva
        peeři dodávající tutéž větev buffer donekonečna mazali jeden druhému.

        OPRAVA K-1: k práci přistupuje druhá podmínka -
        dávka musí nést aspoň jeden blok, který ještě nemáme. Přehrání naší
        vlastní větve totiž projde jak PoW brankou, tak porovnáním práce,
        a zahodilo by cizí rozpracovaný buffer, aniž by nabídlo alternativu.
        Útok byl opakovatelný bez postihu: 26 našich bloků (21 kB, bez PoW
        navíc) udrželo uzel na vrcholu #30, zatímco dostupná větev končila
        na #44, a to v pěti kolech za sebou.
        """
        nabidka = self._prace_davky(blocks_data)
        if nabidka is None:
            return False
        if not self._davka_nese_nove_bloky(blocks_data):
            return False
        v_bufferu = self._prace_bufferu()
        prace_bufferu = v_bufferu[0] if v_bufferu else 0
        return nabidka > prace_bufferu

    def _buffer_je_cerstvy(self):
        # OPRAVA N3 (nález N3): leží v bufferu práce, na které se ještě pracuje?
        #
        # Měří se od POSLEDNÍHO ZÁPISU do bufferu (fork_last_progress), ne od
        # fork_sync_start: ten watchdog při vypršení vynuluje, takže by každý
        # buffer po timeoutu vypadal jako čerstvý nebo naopak prastarý podle
        # toho, kdo se na něj zrovna ptá. Zastaralý buffer je opuštěná práce
        # a zahodit ho kvůli novému forku je v pořádku.
        if self.sync_buffer_tip() is None:
            return False
        return (time.time() - getattr(self, 'fork_last_progress', 0)) <= FORK_SYNC_IDLE_TIMEOUT

    def _fork_slot_na_cooldownu(self, ip):
        # OPRAVA N3 (nález N3): vypršel téhle IP watchdog nad rozpracovaným
        # forkem tak nedávno, že se o slot zatím nesmí ucházet znovu?
        #
        # Volat POUZE s drženým fork_lock - slovník je součástí stavu fork
        # automatu a čte i mění ho týž přechod, který sahá na syncing_fork.
        # Dnes to platí u všech volajících (_lze_prevzit_fork_slot,
        # _zalozit_novy_fork, _watchdog_fork_syncu).
        # Vypršelý záznam se rovnou zahodí, stejně jako u _fork_zbyva_backoff().
        if not ip:
            return 0
        ip = self.normalize_ip(ip)
        now = time.time()
        zaznam = self.fork_slot_cooldown.get(ip)
        if zaznam is None:
            return 0
        if now >= zaznam:
            del self.fork_slot_cooldown[ip]
            return 0
        return int(zaznam - now)

    def _zapis_fork_slot_cooldown(self, ip):
        # OPRAVA N3 (nález N3): volat POUZE s drženým fork_lock, viz
        # _fork_slot_na_cooldownu(). Volá se, když watchdog odebere slot uzlu,
        # který přestal dodávat. Přesně tohle je útočníkův vzorec - zabrat slot
        # jedním blokem, mlčet, nechat ho vypršet a zabrat znovu.
        #
        # Struktura je klíčovaná IP, takže musí mít mez (viz
        # MAX_FORK_SLOT_COOLDOWNS). Při překročení padají nejdřív expirující,
        # tedy ty, které by stejně brzy zanikly samy.
        if not ip:
            return
        ip = self.normalize_ip(ip)
        now = time.time()
        self.fork_slot_cooldown = {k: v for k, v in self.fork_slot_cooldown.items() if v > now}
        self.fork_slot_cooldown[ip] = now + FORK_SLOT_COOLDOWN_SECONDS
        if len(self.fork_slot_cooldown) > MAX_FORK_SLOT_COOLDOWNS:
            nejblizsi = sorted(self.fork_slot_cooldown.items(), key=lambda p: p[1])
            for k, _ in nejblizsi[:len(self.fork_slot_cooldown) - MAX_FORK_SLOT_COOLDOWNS]:
                del self.fork_slot_cooldown[k]

    def _lze_prevzit_fork_slot(self, addr, blocks_data, ip_port):
        """OPRAVA N3 (nález N3): smí tahle dávka převzít fork slot drženému jiným uzlem?

        Volat POUZE s drženým fork_lock a jen když syncing_fork je True.

        Bez téhle cesty byl slot nedobytný: _store_fork_batch_inner() zahodí
        cokoli od jiné IP, než je fork_peer_ip, a cesta k založení nového forku
        vede jen přes syncing_fork == False. Kdo tedy poslal první PoW-platný
        blok, držel slot celých FORK_SYNC_IDLE_TIMEOUT a poctivá, výrazně těžší
        větev se ignorovala - naměřeno šest kol za sebou, uzel zůstal na #12,
        zatímco dostupná větev končila na #30.

        Pravidlo ETAPY 3 ("fork se stahuje od JEDNOHO uzlu") zůstává v platnosti
        a s ním i atributovatelnost vadného bufferu - mění se jen to, že se
        držitel slotu smí vyměnit za někoho, kdo prokazatelně nabízí víc práce.
        """
        if not addr:
            return False
        ip = self.normalize_ip(addr[0])
        drzitel = self.normalize_ip(self.fork_peer_ip) if self.fork_peer_ip else None
        if drzitel is None or ip == drzitel:
            # Vlastní držitel pokračuje normální cestou (_store_fork_batch).
            return False

        # Odmítnutí se tu ZÁMĚRNĚ neloguje: dávka propadne do
        # _store_fork_batch_inner(), který ji zahodí svou vlastní hláškou
        # ("Dávka od ... ignorována: fork se stahuje z ..."). Dva řádky o téže
        # události by z logu udělaly šum právě při zaplavení.
        if self._fork_slot_na_cooldownu(ip) > 0:
            return False
        if not self._nabidka_prebiji_fork(blocks_data):
            return False

        self.add_log(f"{Fore.CYAN}Fork slot přebírá {ip_port}: nabízí prokazatelně víc práce "
                     f"než to, co do bufferu dodal {self.fork_peer_ip}.{Style.RESET_ALL}")
        return True

    def discard_sync_buffer(self):
        # OPRAVA A-3: s bufferem padá i jeho účetnictví.
        self.sync_buffer_bytes = 0
        # OPRAVA N3 (nález N3): a s ním i značka o posledním pokroku - prázdný
        # buffer nesmí vypadat jako rozpracovaná práce, kterou je co chránit.
        self.fork_last_progress = 0
        for suffix in ('', '-wal', '-shm'):
            try:
                path = self.SYNC_BUFFER_DB + suffix
                if os.path.exists(path):
                    os.remove(path)
            except OSError:
                pass

    def process_sync_buffer(self):
        self.add_log(f"{Fore.YELLOW}Stahování forku do bufferu dokončeno, spouštím replace_chain()...{Style.RESET_ALL}")
        
        # OPRAVA L-3: `conn.close()` leželo jako poslední řádek uvnitř try, takže
        # při výjimce z json.loads() nad poškozeným řádkem bufferu se spojení
        # nezavřelo. Cesta je dosažitelná ze sítě (dávky forku plní buffer),
        # takže útočník mohl deskriptory hromadit. Zavření patří do finally.
        conn = None
        chyba_cteni = None
        bloky = []
        try:
            conn = sqlite3.connect(self.SYNC_BUFFER_DB, timeout=1.0)
            conn.execute("PRAGMA journal_mode=WAL;")
            c = conn.cursor()
            c.execute("SELECT block_index, timestamp, transactions, previous_hash, target_hex, nonce, block_hash, merkle_root, version, chain_id, state_root FROM sync_blocks ORDER BY block_index")

            # OPRAVA Z-2 (audit 15. 10. 2026, nález 2, 1/3): řádek se převede na
            # Block HNED a syrový dict se zahodí, místo aby se celý buffer nejdřív
            # naparsoval do seznamu dictů a teprve replace_chain() z nich udělala
            # objekty.
            #
            # Dřív byly v paměti SOUČASNĚ obě reprezentace: tahle metoda držela
            # blocks_data (dicty) a replace_chain() z nich na ř. ~6370 postavila
            # new_chain_tail (objekty), přičemž blocks_data zůstalo živé jako
            # parametr volajícího. Naměřeno nad plným bufferem (62,3 MiB na disku,
            # 60 plných bloků): +129,6 MiB za dicty a +36,8 MiB za objekty, tedy
            # špička 195 MiB a nafouknutí 3,1x proti JSONu na disku. Na telefonu
            # to je OOM kill - a protože se po restartu stáhne týž fork znovu,
            # uzel hluboký reorg nikdy nedotáhne. Selže přesně tehdy, kdy na tom
            # nejvíc záleží.
            #
            # Objekty samy o sobě jsou nevyhnutelné: po úspěšném reorgu je stejně
            # drží self.chain. Odstraňuje se tedy ta polovina špičky, která je
            # čistě navíc. Cursor se streamuje (for row in c), takže ani SQLite
            # nedrží celý výsledek.
            for row in c:
                bloky.append(Block.from_dict({
                    'index': row[0],
                    'timestamp': row[1],
                    'transactions': json.loads(row[2]),
                    'previous_hash': row[3],
                    'target': row[4],
                    'nonce': row[5],
                    'hash': row[6],
                    'merkle_root': row[7],
                    'version': row[8],
                    'chain_id': row[9], 'state_root': row[10]
                }))
        except Exception as e:
            # POZNÁMKA P-1: úklid se dělá AŽ ZA finally níž, protože
            # discard_sync_buffer() maže soubory bufferu - a mazat je se
            # spojením, které je má ještě otevřené, je zbytečná past.
            chyba_cteni = e
        finally:
            if conn is not None:
                try:
                    conn.close()
                except Exception:
                    pass

        if chyba_cteni is not None:
            # OPRAVA Z-2 (nález 2): sem nově spadne i ValueError z
            # Block.from_dict() nad poškozeným řádkem bufferu. Dřív ho o kus níž
            # zachytila replace_chain() svým _reject() a buffer se zahodil na
            # konci metody; výsledek je tedy týž (zahodit, nikoho nebanovat -
            # poškozený řádek je náš disk, ne vina protistrany), jen se na to
            # přijde dřív a bez zbytečné práce.
            self.add_log(f"{Fore.RED}Chyba při čtení ze sync bufferu: {chyba_cteni}{Style.RESET_ALL}")
            # POZNÁMKA P-1: tahle cesta jako jediná buffer NEZAHAZOVALA -
            # nevynulovala fork_start_index ani sync_buffer_bytes a nevolala
            # discard_sync_buffer(). Nad poškozeným řádkem (reálný spouštěč je
            # vadný disk) se uzel točil v cyklu: dostáhne -> přečte -> spadne ->
            # dostáhne, pořád nad týmž nečitelným bufferem. Každá jiná chybová
            # cesta v téhle metodě buffer zahazuje; tahle to teď dělá taky.
            # OPRAVA U-19 (nález 1): i tenhle úklid je přechod automatu, takže
            # se příznaky mění pod fork_lock.
            with self.fork_lock:
                self.syncing_fork = False
                self.fork_start_index = None
                self.fork_sync_start = 0
                self.fork_peer_ip = None
            try:
                self.discard_sync_buffer()
            except Exception as e2:
                # Kontrakt discard_sync_buffer() je "nevyhazuj", ale kdyby se to
                # změnilo, nesmí to shodit úklid stavu - účetnictví bufferu
                # se vynuluje tak jako tak, jinak by strop MAX_SYNC_BUFFER_BYTES
                # počítal bajty, které už nikdo nedrží.
                self.add_log(f"{Fore.RED}Sync buffer se nepodařilo zahodit: {e2}{Style.RESET_ALL}")
                self.sync_buffer_bytes = 0
            return

        # OPRAVA U-19 (nález 1): přečtení a vynulování příznaků je jeden
        # nedělitelný krok. Mezi `fork_idx = self.fork_start_index` a
        # `self.fork_start_index = None` se dřív vešlo cizí vlákno, které mohlo
        # mezitím založit nový fork - a tenhle řádek mu ho vzápětí vynuloval,
        # takže process_sync_buffer() dalšího kola porovnávala začátek bufferu
        # s None a všechno zahodila.
        with self.fork_lock:
            fork_idx = self.fork_start_index
            fork_peer_ip = self.fork_peer_ip

            self.syncing_fork = False
            self.fork_start_index = None
            self.fork_sync_start = 0
            self.fork_peer_ip = None

        if not bloky:
            return

        # ETAPA 3: souvislost bufferu se ověřuje TADY, nad kompletními daty.
        # Dřív to dělal _store_fork_batch() po dávkách, což banovalo poctivé
        # uzly (viz komentář tamtéž) a s dávkami mimo pořadí by to nešlo vůbec.
        #
        # Rozlišujeme dva druhy selhání:
        #  - DÍRA v indexech = ztracená nebo nedoručená odpověď. Buffer zahodíme,
        #    ale NEBANUJEME - poctivý uzel za výpadek sítě nemůže.
        #  - Souvislé indexy, ale nesedící previous_hash = prokazatelný rozpor
        #    v datech od jednoho konkrétního uzlu. Tam ban zůstává.
        # OPRAVA Z-2 (nález 2): tytéž kontroly, jen nad objekty místo dictů.
        # Pravidla se nemění: díra v indexech je výpadek sítě (bez postihu),
        # nesedící previous_hash při souvislých indexech je rozpor v datech
        # jednoho konkrétního uzlu (ban).
        if bloky[0].index != fork_idx:
            self.add_log(f"{Fore.YELLOW}Buffer nezačíná na očekávaném indexu #{fork_idx} (má #{bloky[0].index}). Zahazuji bez postihu.{Style.RESET_ALL}")
            self.discard_sync_buffer()
            return

        for i in range(1, len(bloky)):
            if bloky[i].index != bloky[i-1].index + 1:
                self.add_log(f"{Fore.YELLOW}Díra v bufferu mezi #{bloky[i-1].index} a #{bloky[i].index} (chybí odpověď). Zahazuji bez postihu.{Style.RESET_ALL}")
                self.discard_sync_buffer()
                return
            if bloky[i].previous_hash != bloky[i-1].hash:
                self.add_log(f"{Fore.RED}Rozpor v bufferu u bloku #{bloky[i].index}: previous_hash neodpovídá předchozímu bloku.{Style.RESET_ALL}")
                if fork_peer_ip:
                    self.ban_peer(fork_peer_ip, "nesouvislý řetězec dodaný při fork syncu", BAN_DURATION_PROTOCOL)
                self.discard_sync_buffer()
                return

        # OPRAVA #22 (druhá pojistka): buffer, jehož vrchol je SHODNÝ s naším
        # vrcholem, není konkurenční fork, ale duplicita - typicky opožděná
        # odpověď na žádost, kterou předběhl broadcast téhož bloku (viz komentář
        # u de-duplikace dávky v handleru response_blocks). replace_chain() by
        # ji odmítl na podmínce "hash není lepší" a do logu by spadlo červené
        # "Odmítnuto", které vypadá jako chyba konsenzu, ačkoli o nic nejde.
        # Tady se zahodí tiše. Kontrola je tu i pro případ, že se dávky poskládají
        # do bufferu jinou cestou, než přes de-duplikaci výš.
        if bloky[-1].hash == self.blockchain.get_last_block().hash:
            self.add_log(f"{Fore.CYAN}Buffer končí blokem, který už je naším vrcholem (#{bloky[-1].index}). Není co přehrávat, zahazuji.{Style.RESET_ALL}")
            self.discard_sync_buffer()
            return

        # OPRAVA G-11: `global wallets, password` tu bylo zbytečně - deklarace je nutná jen při PŘIŘAZENÍ, ne při čtení. Odstraněno.
        # OPRAVA Z-2 (nález 2): bloky jsou už naparsované, takže jdou do
        # replace_chain() jako hotove_bloky - nestaví se z nich podruhé.
        pocet_bloku = len(bloky)
        if self.blockchain.replace_chain(fork_idx, hotove_bloky=bloky):
            # OPRAVA N-1: řídicí smyčka sync_blocks_from_peer() podle toho pozná,
            # že fork neskončil zrušením, ale úspěchem, a může pokračovat.
            self.fork_last_ok = True
            # OPRAVA AUDIT-2026-1 (nález 1): reorg prošel, takže poznámka
            # "tenhle fork se nevejde" je neplatná - vrchol se posunul a stejný
            # bod forku může příště vyjít. Backoff by jinak doběhl naprázdno.
            self.fork_neprosaditelny = None
            save_data_z_p2p(self.blockchain, self.peers_snapshot())
            self.add_log(f"{Fore.GREEN}Úspěšný reorg z bufferu! (zpracováno {pocet_bloku} bloků){Style.RESET_ALL}")
        else:
            self.add_log(f"{Fore.RED}Navrhovaný fork z bufferu není platný nebo nemá větší váhu. Odmítnuto.{Style.RESET_ALL}")
            
        # Fork je dotažený (ať už přijatý, nebo odmítnutý) - buffer už nemá smysl.
        self.discard_sync_buffer()

    @staticmethod
    def normalize_ip(ip_str):
        # OPRAVA T-3 (Nález 3): jediná implementace je modulová
        # normalize_ip_str(); tahle metoda zůstává, protože ji volá přes 15
        # míst v uzlu.
        return normalize_ip_str(ip_str)

    # OPRAVA AUDIT-2026-9 (audit 21. 10. 2026, nález N4): značka ořezu je konstanta, aby
    # ji druhý průchod poznal a aby se obě poloviny nemohly rozejít.
    _OREZ_PREDPONA = "...[řádek zkrácen, celkem "
    _OREZ_PRIPONA = " znaků]"

    @staticmethod
    def _orez_radek(message):
        # OPRAVA N1 (nález N1): tvrdý ořez JEDNOHO řádku. Je to poslední branka
        # před zápisem do paměti, takže se nesmí spoléhat na to, že volající
        # hodnotu od protistrany zkrátil sám (zkrat() výš) - stačí jedno nové
        # místo, kde se na to zapomene, a strop zase neplatí. Přesně proti
        # spoléhání na druhou linii míří OPRAVA #4 i D-15.
        #
        # Ořezaný řádek dostane na konec Style.RESET_ALL: hlášky jsou plné ANSI
        # sekvencí z coloramy a ořez uprostřed sekvence by nechal "vypálenou"
        # barvu na zbytku terminálu (viz poznámka u importu readline).
        if not isinstance(message, str):
            message = zkrat(message, MAX_P2P_LOG_LINE_CHARS)
        if len(message) <= MAX_P2P_LOG_LINE_CHARS:
            return message
        # OPRAVA AUDIT-2026-9 (nález N4): funkce je nově IDEMPOTENTNÍ.
        #
        # add_log() ořeže hlášku a výsledek předá _p2p_log_append_locked(),
        # která ořez volá znovu (a volat ho musí - je to poslední branka před
        # zápisem, viz komentář výš). Jenže ořez si na konec připíše vlastní
        # popisek, takže jeho výstup je DELŠÍ než MAX_P2P_LOG_LINE_CHARS a druhý
        # průchod ho zkrátil podruhé - tentokrát i s popiskem, do kterého zapsal
        # délku UŽ OŘEZANÉHO řetězce.
        #
        # Naměřeno: hodnota o 200 000 znacích skončila v logu jako řádek o 552
        # znacích s popiskem "celkem 555 znaků". To je přesně to, čemu měla
        # OPRAVA N1 zabránit - z logu musí být poznat, že se ořezávalo, "jinak
        # by příští audit četl zkrácenou hodnotu jako skutečnou".
        #
        # Vlastní výstup se pozná podle toho, že značka začíná PŘESNĚ na
        # MAX_P2P_LOG_LINE_CHARS a řádek končí příponou. Takový řetězec je tím
        # shora omezený (MAX + značka), takže ani podvržená hláška, která by
        # značku obsahovala, nemůže strop obejít - musela by se trefit na znak
        # přesně a stejně by byla krátká.
        if (message.endswith(P2PNode._OREZ_PRIPONA + Style.RESET_ALL)
                and message.startswith(P2PNode._OREZ_PREDPONA, MAX_P2P_LOG_LINE_CHARS)):
            return message
        return (message[:MAX_P2P_LOG_LINE_CHARS]
                + P2PNode._OREZ_PREDPONA + str(len(message)) + P2PNode._OREZ_PRIPONA
                + Style.RESET_ALL)

    def _p2p_log_append_locked(self, message):
        # Volat POUZE s drženým self.p2p_log_lock.
        #
        # OPRAVA N1 (nález N1): vedle počtu řádků platí i strop v BAJTECH.
        # Počet řádků byl špatná jednotka ze stejného důvodu jako u orphan
        # poolu (OPRAVA D-01): do řádku se interpolují řetězce od protistrany,
        # takže 1000 řádků nebylo ~110 kB, jak slibuje komentář u konstanty,
        # ale naměřených 190,8 MB - a při MAX_MESSAGE_SIZE na zprávu 9,8 GB.
        #
        # Měří se bajty kódování UTF-8, ne znaky: jediný čtyřbajtový znak by
        # jinak účtoval za 1 a dal útočníkovi 4x páku na skutečnou paměť.
        message = self._orez_radek(message)
        self.p2p_log.append(message)
        self.p2p_log_bytes += len(message.encode('utf-8'))
        while self.p2p_log and (len(self.p2p_log) > MAX_P2P_LOG_ENTRIES
                                or self.p2p_log_bytes > MAX_P2P_LOG_BYTES):
            # Nejstarší ven. Jeden řádek je po ořezu vždy hluboko pod bajtovým
            # stropem, takže smyčka nikdy nevyhodí právě přidaný záznam a vždy
            # skončí - podmínka `self.p2p_log and` je jen pojistka pro případ,
            # že by se konstanty někdy posunuly proti sobě.
            self.p2p_log_bytes -= len(self.p2p_log.popleft().encode('utf-8'))
            self.p2p_log_dropped += 1
        if self.p2p_log_bytes < 0:
            self.p2p_log_bytes = 0

    def _p2p_log_flush_repeat_locked(self):
        # Volat POUZE s drženým self.p2p_log_lock. Zhmotní potlačené opakování
        # do jediného souhrnného řádku.
        if self._p2p_log_repeat > 0:
            self._p2p_log_append_locked(
                f"{Fore.YELLOW}  ... předchozí hláška se opakovala {self._p2p_log_repeat}x.{Style.RESET_ALL}"
            )
            self._p2p_log_repeat = 0

    def add_log(self, message):
        # OPRAVA G-05: zápis do kruhového bufferu místo do neomezené fronty.
        # Zámek je potřeba proto, že add_log volají všechna P2P vlákna, kdežto
        # dřívější Queue si synchronizaci řešila sama.
        # OPRAVA K-3 (audit 21. 10. 2026, nález 3): ořez se provede JEDNOU tady a dál se
        # pracuje už jen s oříznutou podobou.
        #
        # Dosud si _p2p_log_last držel SYROVOU hlášku, zatímco do fronty šel
        # výsledek _orez_radek(). Strop MAX_P2P_LOG_LINE_CHARS tedy platil pro
        # frontu, ale ne pro tenhle jeden atribut: naměřeno 300 108 znaků
        # z jediné zprávy 'new_block' s dlouhou hodnotou v poli 'index',
        # přičemž bajtové účetnictví fronty hlásilo 1 222 B. Spotřeba je shora
        # omezená velikostí zprávy a drží se jen jedna položka, takže o únik
        # nejde - ale je to táž třída nálezu jako OPRAVA N1 ("počet položek je
        # špatná jednotka"), jen o patro vedle, a stejně jako tam je správné
        # místo poslední branka před uložením, ne spoléhání na volajícího.
        #
        # Porovnává se taktéž oříznutá podoba. Dvě různé dlouhé hlášky, které
        # se liší až za stropem, se tím slijí do jedné a druhá se započítá jako
        # opakování. To je správně: do logu by se obě vypsaly stejně, takže
        # vypsat je dvakrát by byl jen šum - a právě proti němu potlačování je.
        message = self._orez_radek(message)
        with self.p2p_log_lock:
            if message == self._p2p_log_last:
                self._p2p_log_repeat += 1
                return
            self._p2p_log_flush_repeat_locked()
            self._p2p_log_last = message
            self._p2p_log_append_locked(message)

    def drain_log(self):
        # OPRAVA G-05: jediná cesta, kudy se log čte. Vrátí seznam řádků a
        # buffer vyprázdní - stejná sémantika jako dřívější smyčka nad
        # Queue.get(), jen navíc hlásí, kolik záznamů padlo pod strop.
        with self.p2p_log_lock:
            self._p2p_log_flush_repeat_locked()
            entries = list(self.p2p_log)
            self.p2p_log.clear()
            # OPRAVA N1 (nález N1): s obsahem padá i jeho účetnictví. Kdyby tu
            # počítadlo zůstalo, strop by se po prvním čtení logu uplatňoval
            # proti bajtům, které už nikdo nedrží.
            self.p2p_log_bytes = 0
            dropped = self.p2p_log_dropped
            self.p2p_log_dropped = 0
            self._p2p_log_last = None
        if dropped:
            entries.append(
                f"{Fore.YELLOW}[{dropped} nejstarších záznamů bylo zahozeno, "
                f"strop logu je {MAX_P2P_LOG_ENTRIES} řádků a "
                f"{MAX_P2P_LOG_BYTES // 1024} kB.]{Style.RESET_ALL}"
            )
        return entries

    def ban_peer(self, ip, reason, duration=BAN_DURATION_SECONDS):
        # OPRAVA #1: jediné místo, kudy se uděluje ban, a je vždy DOČASNÝ.
        # duration=None znamená trvalý ban - ten smí udělit jen uživatel z menu.
        if not ip:
            return
        # OPRAVA T-3 (Nález 3): blacklist byl JEDINÁ struktura klíčovaná IP
        # adresou, která ukládala syrový řetězec - peer_listen_ports,
        # peer_listen_seen i úklid v _prune_listen_ports_locked() chodí přes
        # normalize_ip(). Adresy ze socket.accept() jsou kanonické, takže
        # automatické bany fungovaly, ale adresa od UŽIVATELE ne: volba 16 bere
        # peer_ip syrově ze vstupu, volba 17 pak banuje peer_to_remove[0], tedy
        # ten syrový tvar ('0:0:0:0:0:0:0:1'). Skutečné spojení z téhož
        # hostitele se ohlásí kanonicky ('::1') a s uloženým klíčem se
        # nespárovalo - ruční trvalý ban tiše nefungoval.
        ip = self.normalize_ip(ip)
        expiry = None if duration is None else time.time() + duration
        with self.blacklist_lock:
            existing = self.blacklist.get(ip, 0)
            if ip in self.blacklist and existing is None:
                return  # trvalý ban dočasným nepřepisujeme
            # OPRAVA T-2 (Nález 2): delší ban vyhrává. Zápis byl bezpodmínečný,
            # takže uzel zabanovaný na 24 h za protokolový přestupek
            # (BAN_DURATION_PROTOCOL) si ban zkrátil na hodinu tím, že spáchal
            # LEVNĚJŠÍ prohřešek - stačilo vyčerpat rate limit, což vede na
            # BAN_DURATION_SECONDS. Trvalý ban proti přepsání chráněný byl,
            # dočasné bany proti sobě navzájem ne.
            #
            # Pro nepřítomnou IP je existing == 0, tedy menší než jakákoli
            # expirace - nový ban projde. Vypršelý, ale dosud nesklizený záznam
            # má existing v minulosti, takže ho nový ban přepíše také.
            if existing is not None and expiry is not None and existing > expiry:
                return
            self.blacklist[ip] = expiry
            # OPRAVA G-06 (b): dřív se tu volalo save_blacklist(dict(...)),
            # tedy kompletní přepis souboru po KAŽDÉM banu - N banů znamenalo
            # O(N^2) zapsaných bajtů (měřeno: 1500 banů = 59 kB souboru a 2,0 s
            # čistého I/O) a zbytečné opotřebení flash paměti telefonu. Nově se
            # změna jen označí a na disk ji odnese flush_blacklist().
            self.blacklist_dirty = True
            # OPRAVA G-06 (a): tvrdý strop na počet položek. Bez něj mohl
            # útočník z jediného /64 prefixu (2^64 adres) nechat slovník růst
            # bez omezení - každá adresa se dá zabanovat jedním protokolovým
            # přestupkem, tedy prakticky zdarma.
            self._enforce_blacklist_cap_locked(slack=BLACKLIST_CAP_SLACK)
        if expiry is None:
            # Trvalý ban uděluje výhradně uživatel z menu a čeká, že přežije
            # vypnutí. Ten jediný se zapisuje okamžitě - je jich řádově málo,
            # takže kvadratické chování nehrozí.
            self.flush_blacklist(force=True)
        if expiry is None:
            self.add_log(f"{Fore.RED}Uzel {ip} trvale zablokován. Důvod: {reason}.{Style.RESET_ALL}")
        else:
            self.add_log(f"{Fore.RED}Uzel {ip} dočasně zablokován na {int(duration)} s. Důvod: {reason}.{Style.RESET_ALL}")

    def _enforce_blacklist_cap_locked(self, slack=0):
        # OPRAVA G-06 (a): volat POUZE s drženým self.blacklist_lock.
        # slack > 0 je horká cesta (ban_peer): ořez se spustí až po překročení
        # rezervy a sáhne rovnou pod strop, takže amortizovaně stojí O(1).
        # slack = 0 je úklidová cesta (prune_blacklist), která dorovná přesně.
        if len(self.blacklist) <= MAX_BLACKLIST_ENTRIES + slack:
            return 0
        now = time.time()
        # Nejdřív se zkusí uvolnit místo bez ztráty informace - expirované ven.
        obetovane = [ip for ip, exp in self.blacklist.items()
                     if exp is not None and now >= exp]
        for ip in obetovane:
            del self.blacklist[ip]
        prebytek = len(self.blacklist) - MAX_BLACKLIST_ENTRIES
        if prebytek > 0:
            # Pořád plno. Obětují se DOČASNÉ bany s nejbližší expirací, tedy
            # ty, které by stejně brzy vypršely samy. Trvalý ban uděluje jen
            # uživatel ručně z menu - ten se nezahazuje nikdy, i kdyby jich
            # bylo nad strop; smazat cizí rozhodnutí je horší než mít o pár
            # položek víc.
            docasne = sorted((exp, ip) for ip, exp in self.blacklist.items()
                             if exp is not None)
            for _, ip in docasne[:prebytek]:
                del self.blacklist[ip]
                obetovane.append(ip)
        if obetovane:
            self.blacklist_dirty = True
        return len(obetovane)

    def flush_blacklist(self, force=False):
        # OPRAVA G-06 (b): dávkovaný zápis na disk. Snapshot se pořizuje pod
        # zámkem, samotné I/O běží bez něj. Když zápis selže, příznak 'dirty'
        # se vrátí zpátky, takže se o změnu nepřijde.
        if not self.blacklist_dirty:
            return False
        now = time.time()
        with self.blacklist_lock:
            if not self.blacklist_dirty:
                return False
            if not force and now - self.blacklist_last_flush < BLACKLIST_FLUSH_INTERVAL:
                return False
            snapshot = dict(self.blacklist)
            self.blacklist_dirty = False
            self.blacklist_last_flush = now
        if save_blacklist(snapshot):
            return True
        with self.blacklist_lock:
            self.blacklist_dirty = True
        return False

    def mark_peers_dirty(self):
        """OPRAVA AUDIT-2026-8 (audit 21. 10. 2026, nález N3): označí tabulku peerů za
        změněnou. Na disk ji odnese flush_peers() z periodického kola.

        Nahrazuje přímá volání save_peers() ze síťových cest. Důvod je v
        komentáři u PEERS_FLUSH_INTERVAL: handshake je jediný typ zprávy mimo
        branku důvěry, takže zápis na flash šlo vyvolat 90x za sekundu z jedné
        IP, aniž se tabulka jakkoli změnila.

        Metoda je záměrně bez zámku: nastavit bool je atomické a případný souběh
        s flush_peers() může vést nejvýš k jednomu zápisu navíc, nikdy k jeho
        ztrátě - flush si příznak bere znovu pod zámkem.
        """
        self.peers_dirty = True

    def flush_peers(self, force=False):
        """OPRAVA AUDIT-2026-8 (nález N3): dávkovaný zápis peers.json.

        Přesná obdoba flush_blacklist(): snímek pod zámkem, I/O bez něj, a když
        zápis selže, příznak se vrátí, takže se o změnu nepřijde.
        """
        if not self.peers_dirty:
            return False
        now = time.time()
        with self.peers_lock:
            if not self.peers_dirty:
                return False
            if not force and now - self.peers_last_flush < PEERS_FLUSH_INTERVAL:
                return False
            snapshot = list(self.peers)
            self.peers_dirty = False
            self.peers_last_flush = now
        if save_peers(snapshot):
            return True
        with self.peers_lock:
            self.peers_dirty = True
        return False

    def prune_blacklist(self, force=False):
        # OPRAVA G-06 (a): periodický úklid. Dřív se slovník kvůli úklidu
        # neprocházel VŮBEC - expirovaný záznam zmizel jedině tehdy, když se
        # náhodou znovu ozvala TÁŽ IP (is_blacklisted). IP, která se už nikdy
        # neozve, zůstala v paměti i v souboru napořád. Volá se ze
        # sync_chain_periodically, tedy odtud, kde už běží cleanup_mempool().
        now = time.time()
        if not force and now - self.blacklist_last_prune < BLACKLIST_PRUNE_INTERVAL:
            return 0
        self.blacklist_last_prune = now
        with self.blacklist_lock:
            vyprsele = [ip for ip, exp in self.blacklist.items()
                        if exp is not None and now >= exp]
            for ip in vyprsele:
                del self.blacklist[ip]
            if vyprsele:
                self.blacklist_dirty = True
            self._enforce_blacklist_cap_locked()
        if vyprsele:
            self.add_log(f"{Fore.GREEN}Úklid blacklistu: {len(vyprsele)} vypršelých banů odstraněno.{Style.RESET_ALL}")
        self.flush_blacklist()
        return len(vyprsele)

    def _uklid_kbelik(self, bucket, max_age, now, dvojice=True):
        """OPRAVA K-2: společný úklid kbelíku klíčovaného IP.

        Volat POUZE s drženým self.rate_lock. Mění slovník NA MÍSTĚ, aby se
        nemusel přiřazovat zpět do atributu (původní kód ho nahrazoval novým
        slovníkem, takže každý úklid alokoval celou kopii).

        Konstrukce je táž jako u _enforce_blacklist_cap_locked():

          1. Ořez se vůbec nespustí, dokud se slovník nedostane nad
             MAX_RATE_BUCKETS + RATE_BUCKET_CAP_SLACK. Pak sáhne rovnou pod
             strop, takže na jedno volání vychází amortizovaně O(1). Původní
             varianta procházela celý slovník při každém volání nad 1000.
          2. Nejdřív padají položky starší než okno kbelíku, tedy bez ztráty
             informace.
          3. Když to nestačí, vytěsní se NEJSTARŠÍ položky na tvrdý strop.

        Proč je bod 3 bezpečný: vyhozená položka znamená, že IP začne
        s PLNOU kapacitou. Přesně to ale dostane i každá IP, kterou uzel vidí
        poprvé - limiter je per-IP a útočník si adresu vybírá sám. Útočník,
        který se protočí přes >4096 adres, si tedy nic nekoupí: stejně čerstvý
        rozpočet má zdarma tím, že vezme další adresu. Naopak poctivému uzlu
        vytěsnění jedině pomůže. Totéž platí pro přetečené čítače
        (rate_overflow, tx_overflow) a pro chain_info_asked: u obou znamená
        zapomenutý záznam "cooldown dávno vypršel", což je právě to, co by za
        okamžik řekl i ponechaný záznam.

        `dvojice` rozlišuje tvar hodnoty: (tokeny, cas) u kbelíků, holý
        časový údaj u chain_info_asked.
        """
        if len(bucket) <= MAX_RATE_BUCKETS + RATE_BUCKET_CAP_SLACK:
            return 0
        stamp = (lambda v: v[1]) if dvojice else (lambda v: v)
        stare = [k for k, v in bucket.items() if now - stamp(v) >= max_age]
        for k in stare:
            del bucket[k]
        odstraneno = len(stare)
        prebytek = len(bucket) - MAX_RATE_BUCKETS
        if prebytek > 0:
            podle_veku = sorted(bucket.items(), key=lambda p: stamp(p[1]))
            for k, _ in podle_veku[:prebytek]:
                del bucket[k]
            odstraneno += prebytek
        return odstraneno

    def prune_rate_buckets(self, force=False):
        """OPRAVA K-2: periodický úklid kbelíků podle stáří.

        Tvrdý strop v _uklid_kbelik() drží paměť shora omezenou, ale sám ji po
        odražené vlně nevrátí - položky pod stropem tam zůstanou ležet. Tohle
        je druhá polovina: jeden průchod všemi kbelíky nejvýš jednou za
        RATE_BUCKET_PRUNE_INTERVAL. Jede ve stejném rytmu a ze stejného důvodu
        jako prune_blacklist(), odkud je i vzorec s vlastní periodou uvnitř
        metody - volající ji smí zkoušet každých 10 s, aniž by to něco stálo.
        """
        now = time.time()
        if not force and now - self.rate_buckets_last_prune < RATE_BUCKET_PRUNE_INTERVAL:
            return 0
        self.rate_buckets_last_prune = now
        odstraneno = 0
        with self.rate_lock:
            for bucket, max_age in (
                (self.rate_buckets, RATE_BUCKET_MAX_AGE),
                (self.conn_buckets, RATE_BUCKET_MAX_AGE_LONG),
                (self.tx_buckets, RATE_BUCKET_MAX_AGE_LONG),
                (self.rate_overflow, RATE_BUCKET_MAX_AGE_LONG),
                (self.tx_overflow, RATE_BUCKET_MAX_AGE_LONG),
                (self.expensive_buckets, RATE_BUCKET_MAX_AGE_LONG),
                (self.expensive_byte_buckets, RATE_BUCKET_MAX_AGE_LONG),
                (self.inbound_byte_buckets, RATE_BUCKET_MAX_AGE_LONG),
            ):
                stare = [k for k, v in bucket.items() if now - v[1] >= max_age]
                for k in stare:
                    del bucket[k]
                odstraneno += len(stare)
            stare = [k for k, v in self.chain_info_asked.items()
                     if now - v >= CHAIN_INFO_REQUEST_COOLDOWN]
            for k in stare:
                del self.chain_info_asked[k]
            odstraneno += len(stare)
        return odstraneno

    def _take_token(self, bucket, ip, capacity, refill, now):
        # Token bucket: vrací True, pokud byl token k dispozici a byl odebrán.
        tokens, last = bucket.get(ip, (float(capacity), now))
        tokens = min(float(capacity), tokens + (now - last) * refill)
        if tokens < 1.0:
            bucket[ip] = (tokens, now)
            return False
        bucket[ip] = (tokens - 1.0, now)
        return True

    def is_rate_limited(self, addr):
        # OPRAVA #1: překročení burstu už NEZNAMENÁ ban - spojení se jen zahodí.
        # Ban přijde teprve po dlouhodobém překračování (rate_overflow), a i pak
        # je dočasný. Tím zmizí scénář, kdy se dva poctivé uzly na rychlé síti
        # navzájem natrvalo vyřadí po prvních ~100 blocích.
        # OPRAVA T-4 (Nález 3): klíčovalo se syrovou adresou. Přes accept()
        # to zneužít nešlo (ta vrací vždy kanonický tvar a útočník si textovou
        # podobu své adresy vybrat nemůže), ale PeerConnection._read_loop()
        # sem posílá self.peer, tedy adresu z tabulky - takže týž hostitel měl
        # jiný rozpočet pro odchozí a jiný pro příchozí spojení.
        ip = self.normalize_ip(addr[0])
        now = time.time()
        with self.rate_lock:
            # OPRAVA K-2: tvrdý strop místo prořezávání
            # podle stáří při každém volání. Viz _uklid_kbelik().
            self._uklid_kbelik(self.rate_buckets, RATE_BUCKET_MAX_AGE, now)
            self._uklid_kbelik(self.expensive_buckets, RATE_BUCKET_MAX_AGE_LONG, now)
            self._uklid_kbelik(self.rate_overflow, RATE_BUCKET_MAX_AGE_LONG, now)

            if self._take_token(self.rate_buckets, ip, RATE_LIMIT_BUCKET_CAPACITY, RATE_LIMIT_REFILL_PER_SECOND, now):
                return False

            count, last = self.rate_overflow.get(ip, (0.0, now))
            count = max(0.0, count - (now - last) * RATE_LIMIT_REFILL_PER_SECOND) + 1.0
            self.rate_overflow[ip] = (count, now)
            over_limit = count > RATE_LIMIT_ABUSE_THRESHOLD

        if over_limit:
            self.ban_peer(ip, "dlouhodobé překračování limitu spojení")
        return True

    def is_connection_rate_limited(self, addr):
        # ETAPA 2: rozpočet na navazovaná spojení. Překročení spojení jen zahodí,
        # ban až po dlouhodobém překračování - stejná logika jako u zpráv.
        # OPRAVA T-4 (Nález 3): kanonický klíč, viz is_rate_limited().
        ip = self.normalize_ip(addr[0])
        now = time.time()
        with self.rate_lock:
            # OPRAVA K-2: tahle cesta se volá na KAŽDÉ
            # přijaté TCP spojení, takže je z celé třídy nejexponovanější.
            self._uklid_kbelik(self.conn_buckets, RATE_BUCKET_MAX_AGE_LONG, now)
            if self._take_token(self.conn_buckets, ip, CONN_BUCKET_CAPACITY, CONN_REFILL_PER_SECOND, now):
                return False
        return True

    def is_tx_rate_limited(self, addr):
        # OPRAVA W-3 (audit 9. 10. 2026, nález N-3): rozpočet na zprávy typu
        # 'transaction'. Doslova táž konstrukce jako is_rate_limited(), jen nad
        # vlastní dvojicí struktur a s mezemi odvozenými od kapacity bloku.
        #
        # Podstatná změna oproti původnímu kódu je NÁVRATOVÁ CESTA: překročení
        # burstu znamená "zahoď zprávu", ne "zabanuj peera". Ban se uděluje až
        # za dlouhodobé překračování, a i pak je dočasný (BAN_DURATION_SECONDS).
        # Dřív stačilo 101 zpráv za sekundu a poctivý uzel měl hodinu ban od
        # všech sousedů - viz komentář u TX_RATE_BUCKET_CAPACITY.
        if not addr:
            return False
        # Kanonický klíč ze stejného důvodu jako u ostatních limiterů (T-4):
        # jinak má týž hostitel jiný rozpočet pro příchozí a jiný pro odchozí
        # spojení.
        ip = self.normalize_ip(addr[0])
        now = time.time()
        with self.rate_lock:
            # OPRAVA K-2, viz _uklid_kbelik().
            self._uklid_kbelik(self.tx_buckets, RATE_BUCKET_MAX_AGE_LONG, now)
            self._uklid_kbelik(self.tx_overflow, RATE_BUCKET_MAX_AGE_LONG, now)

            if self._take_token(self.tx_buckets, ip, TX_RATE_BUCKET_CAPACITY,
                                TX_RATE_REFILL_PER_SECOND, now):
                return False

            count, last = self.tx_overflow.get(ip, (0.0, now))
            count = max(0.0, count - (now - last) * TX_RATE_REFILL_PER_SECOND) + 1.0
            self.tx_overflow[ip] = (count, now)
            over_limit = count > TX_RATE_ABUSE_THRESHOLD

        if over_limit:
            self.ban_peer(ip, "dlouhodobé překračování limitu transakcí")
        return True

    def expect_mempool_from(self, peer_addr):
        # OPRAVA F-04: zaznamená, že jsme právě odeslali request_mempool a od
        # této IP tedy odpověď čekáme. Klíčem je IP, ne (IP, port): starší uzly
        # odpovídají NOVÝM spojením, takže zdrojový port odpovědi se nerovná
        # portu, na který jsme se ptali.
        if not peer_addr:
            return
        ip = self.normalize_ip(peer_addr[0])
        with self.awaiting_mempool_lock:
            if len(self.awaiting_mempool) > 1000:
                now = get_time()
                self.awaiting_mempool = {k: v for k, v in self.awaiting_mempool.items() if v > now}
            self.awaiting_mempool[ip] = get_time() + MEMPOOL_RESPONSE_WINDOW

    def _mempool_kurzor_get(self, addr):
        # OPRAVA W-5 (audit 9. 10. 2026, nález N-2b): kde jsme u tohohle peera
        # minule skončili. None = začít od nejdražších.
        #
        # Klíčem je IP, ne dvojice (IP, port): stejně jako u awaiting_mempool
        # chodí odpovědi starších uzlů z jiného zdrojového portu. Nejhorší
        # následek hrubšího klíče je, že si dva uzly na téže adrese sdílejí
        # rotaci, tedy dostanou různé části mempoolu - což syncu nevadí.
        if not addr:
            return None
        ip = self.normalize_ip(addr[0])
        with self.mempool_offer_lock:
            zaznam = self.mempool_offer_cursor.get(ip)
        if zaznam is None:
            return None
        klic, kdy = zaznam
        if time.time() - kdy > MEMPOOL_OFFER_CURSOR_TTL:
            # Peer se dlouho neozval; začneme mu zase od nejdražších, ať
            # nedostane rovnou ten nejlevnější konec.
            return None
        return klic

    def _mempool_kurzor_set(self, addr, klic):
        # OPRAVA W-5: klic=None kurzor ruší (celý mempool se vešel do jedné
        # odpovědi, takže není co rotovat).
        if not addr:
            return
        ip = self.normalize_ip(addr[0])
        now = time.time()
        with self.mempool_offer_lock:
            if len(self.mempool_offer_cursor) > MAX_MEMPOOL_OFFER_CURSORS:
                # Stejná konstrukce jako u ostatních kbelíků klíčovaných IP:
                # při překročení stropu vypadnou záznamy po TTL. Nejde o
                # bezpečnostní stav, takže se nic netřídí - ztracený kurzor
                # znamená jen jedno kolo od nejdražších.
                self.mempool_offer_cursor = {
                    k: v for k, v in self.mempool_offer_cursor.items()
                    if now - v[1] < MEMPOOL_OFFER_CURSOR_TTL}
                # Tvrdý strop pro případ, že jsou všechny záznamy čerstvé.
                # Samotné TTL by stačilo jen díky tomu, že se sem dostane pouze
                # IP, která prošla brankou důvěry (ta má vlastní strop
                # MAX_PEER_LISTEN_PORTS) - a spoléhat se na obranu v druhé linii
                # je přesně to, co zakazuje OPRAVA #4. Zahazují se nejstarší
                # kurzory; ztráta kurzoru znamená jen jedno kolo od nejdražších.
                if len(self.mempool_offer_cursor) > MAX_MEMPOOL_OFFER_CURSORS:
                    nejnovejsi = sorted(self.mempool_offer_cursor.items(),
                                        key=lambda p: p[1][1], reverse=True)
                    self.mempool_offer_cursor = dict(nejnovejsi[:MAX_MEMPOOL_OFFER_CURSORS])
            if klic is None:
                self.mempool_offer_cursor.pop(ip, None)
            else:
                self.mempool_offer_cursor[ip] = (klic, now)

    def consume_mempool_expectation(self, addr):
        # Jednorázová branka: platí pro JEDNU odpověď. Druhá zpráva na týž
        # dotaz už neprojde, takže nejde poslat 100 dávek za sebou.
        if not addr:
            return False
        ip = self.normalize_ip(addr[0])
        now = get_time()
        with self.awaiting_mempool_lock:
            deadline = self.awaiting_mempool.pop(ip, None)
        return deadline is not None and deadline > now

    def expect_full_chain_from(self, peer_addr):
        # OPRAVA Y-5 (audit 14. 10. 2026, nález 5): protějšek
        # expect_mempool_from() pro 'request_full_chain'. Zaznamená, že jsme si
        # o full chain řekli, a DOKDY jsme ochotni odpověď přijmout - dřív tu
        # byl bool, který se bez odpovědi nikdy nezavřel.
        #
        # Klíčem je IP, ne (IP, port), ze stejného důvodu jako u mempoolu:
        # starší uzly odpovídají NOVÝM spojením, takže zdrojový port odpovědi
        # se nerovná portu, na který jsme se ptali.
        if not peer_addr:
            return
        ip = self.normalize_ip(peer_addr[0])
        with self.awaiting_full_chain_lock:
            if len(self.awaiting_full_chain) > 1000:
                now = get_time()
                self.awaiting_full_chain = {k: v for k, v in self.awaiting_full_chain.items() if v > now}
            self.awaiting_full_chain[ip] = get_time() + FULL_CHAIN_RESPONSE_WINDOW

    def consume_full_chain_expectation(self, addr):
        # Jednorázová branka, stejně jako consume_mempool_expectation(): platí
        # pro JEDNU odpověď, takže nejde poslat víc full chainů za sebou.
        if not addr:
            return False
        ip = self.normalize_ip(addr[0])
        now = get_time()
        with self.awaiting_full_chain_lock:
            deadline = self.awaiting_full_chain.pop(ip, None)
        return deadline is not None and deadline > now

    def charge_expensive_bytes(self, addr, nbytes):
        # ETAPA 2: bajtový rozpočet pro drahé odpovědi. Počet požadavků je
        # špatná jednotka - request_blocks nad prázdnými bloky stojí zlomek
        # toho, co nad plnými, a strop 1 req/s zastropoval propustnost na
        # 100 bloků/s bez ohledu na hloubku pipeliningu. Bajtový kbelík škáluje
        # se skutečnou prací. Vrací False, když rozpočet nestačí.
        if not addr:
            return True
        # OPRAVA T-4 (Nález 3): kanonický klíč, viz is_rate_limited().
        ip = self.normalize_ip(addr[0])
        now = time.time()
        with self.rate_lock:
            # OPRAVA K-2, viz _uklid_kbelik().
            self._uklid_kbelik(self.expensive_byte_buckets, RATE_BUCKET_MAX_AGE_LONG, now)
            tokens, last = self.expensive_byte_buckets.get(ip, (float(EXPENSIVE_BYTES_CAPACITY), now))
            tokens = min(float(EXPENSIVE_BYTES_CAPACITY), tokens + (now - last) * EXPENSIVE_BYTES_PER_SECOND)
            if tokens < nbytes:
                self.expensive_byte_buckets[ip] = (tokens, now)
                return False
            self.expensive_byte_buckets[ip] = (tokens - nbytes, now)
            return True

    def uctuj_predem(self, addr, odhad_bajtu, ip_port, popis):
        """OPRAVA AUDIT-2026-2 (audit 8. 10. 2026, nález 2): strhne ODHAD z
        bajtového rozpočtu ještě PŘED tím, než handler sáhne do databáze.

        Vrací počet stržených bajtů (který se pak předá _respond() jako
        `uz_uctovano`), nebo None, když rozpočet nestačí a dotaz se nemá
        obsloužit vůbec.

        Dosud se účtovalo až z hotové odpovědi v _respond(), takže vyčerpaný
        rozpočet odpověď jen zahodil - čtení z DB, parsování i serializace už
        proběhly. Naměřeno: 79 B dotaz vynutil 62 ms obsluhy a 35 MiB špičky
        paměti, 9 z 10 odpovědí se zahodilo až po práci, a trvalé držení stropu
        stálo útočníka 316 B/s. Odhad proto musí stát na LEVNÉM dotazu
        (agregace přes LENGTH), ne na skutečné odpovědi.

        Nepřesnost odhadu nevadí: _respond() dopočítá rozdíl, je-li skutečná
        odpověď větší. Odhad nad skutečnost se do kbelíku nevrací - rozpočet má
        škrtit vykonanou práci, a tu handler odvedl podle odhadu.
        """
        if not addr:
            return 0
        odhad = max(0, int(odhad_bajtu))
        if not self.charge_expensive_bytes(addr, odhad):
            self.add_log(
                f"{Fore.YELLOW}{popis} od {ip_port} zahozen JEŠTĚ PŘED čtením z databáze: "
                f"vyčerpán bajtový rozpočet (odhad {odhad / 1024:.0f} KB).{Style.RESET_ALL}")
            return None
        return odhad

    def is_expensive_rate_limited(self, addr):
        # OPRAVA #1 + #9: samostatný, mnohem přísnější rozpočet pro dotazy, které
        # čtou z databáze a generují velké odpovědi.
        if not addr:
            return False
        # OPRAVA T-4 (Nález 3): kanonický klíč, viz is_rate_limited().
        ip = self.normalize_ip(addr[0])
        now = time.time()
        with self.rate_lock:
            # OPRAVA K-2: expensive_buckets se dosud
            # prořezával JEN v is_rate_limited(). Dnes tudy projde každá
            # zpráva, takže to vycházelo, ale strop struktury nemá záležet na
            # tom, kdo ji náhodou uklízí. Zápis a úklid patří k sobě.
            self._uklid_kbelik(self.expensive_buckets, RATE_BUCKET_MAX_AGE_LONG, now)
            return not self._take_token(self.expensive_buckets, ip, EXPENSIVE_BUCKET_CAPACITY, EXPENSIVE_REFILL_PER_SECOND, now)

    def _muze_zadat_chain_info(self, addr):
        """OPRAVA N2 (audit 10. 10. 2026, nález N2): smíme téhle IP poslat
        'request_chain_info' vyvolaný blokem, který neumíme navázat?

        Dřív se posílal na KAŽDÝ takový blok. Útočná zpráva je přitom pouhý
        replay libovolného veřejného bloku (870 B, žádné PoW navíc), takže
        z jedné IP šlo vyrobit 90 odchozích vláken a socketů za sekundu, každé
        živé až 10 s. Rozpočet platí na IP a je jednorázový v okně: jedna
        odpověď za CHAIN_INFO_REQUEST_COOLDOWN stačí, protože se touhle zprávou
        jen ptáme, jestli má protistrana delší řetězec - a totéž se periodický
        sync ptá všech peerů každých 10 s.

        Vrací True a rovnou si odeslání poznamená, takže test i zápis jsou
        jeden krok (dvě vlákna s týmž blokem nepošlou dva dotazy).
        """
        if not addr:
            return True
        ip = self.normalize_ip(addr[0])
        now = time.time()
        with self.rate_lock:
            # Struktura je klíčovaná IP, a tu si útočník vybírá sám, takže musí
            # mít mez - stejně jako ostatní kbelíky v téhle třídě.
            # OPRAVA K-2: mez byla jen měkká (prořež podle
            # stáří nad 1000), nově tvrdý strop. Hodnota je holý čas, ne
            # dvojice, proto dvojice=False.
            self._uklid_kbelik(self.chain_info_asked, CHAIN_INFO_REQUEST_COOLDOWN,
                               now, dvojice=False)
            posledni = self.chain_info_asked.get(ip, 0.0)
            if now - posledni < CHAIN_INFO_REQUEST_COOLDOWN:
                return False
            self.chain_info_asked[ip] = now
            return True

    def is_blacklisted(self, addr):
        ip = addr[0] if isinstance(addr, (tuple, list)) else addr
        if not ip:
            return False
        # OPRAVA T-3 (Nález 3): táž normalizace jako v ban_peer(). Obě strany
        # musí klíčovat stejně, jinak se zápis a čtení minou.
        ip = self.normalize_ip(ip)
        with self.blacklist_lock:
            if ip not in self.blacklist:
                return False
            expiry = self.blacklist[ip]
            if expiry is None:
                return True
            if time.time() >= expiry:
                # OPRAVA #1: ban vypršel, IP se sama uvolní.
                # OPRAVA G-06 (b): dřív se tady rovnou přepisoval celý soubor.
                # Nově se změna jen označí; na disk ji odnese flush_blacklist()
                # z úklidového vlákna. Tahle cesta je navíc jen pojistka -
                # systematicky expirované bany maže prune_blacklist().
                del self.blacklist[ip]
                self.blacklist_dirty = True
            else:
                return True
        self.add_log(f"{Fore.GREEN}Dočasný ban IP {ip} vypršel, uzel je opět povolen.{Style.RESET_ALL}")
        return False

    @staticmethod
    def subnet_key(ip_str):
        # OPRAVA D-08: klíč pro diverzitu. U IPv4 /16, u IPv6 /32 - hranice,
        # za kterou už adresy typicky nepatří jednomu levnému poolu. Cílem není
        # dokonalá topologická přesnost, ale aby 20 adres z jednoho rozsahu
        # nemohlo obsadit celou tabulku.
        try:
            ip = ipaddress.ip_address(ip_str)
        except ValueError:
            return ip_str
        if ip.version == 4:
            return str(ipaddress.ip_network(f"{ip}/16", strict=False))
        return str(ipaddress.ip_network(f"{ip}/32", strict=False))

    def note_peer_activity(self, peer):
        # Zaznamená úspěšnou interakci s peerem. Volá se odsud, kde se
        # prokazatelně povedla komunikace - to je jediné skóre, kterému se dá
        # věřit, protože si ho útočník nemůže deklarovat sám.
        if not peer:
            return
        # OPRAVA AUDIT-2026-4 (audit 8. 10. 2026, nález 4): zapisuje se JEN pro
        # peera, který v self.peers skutečně je.
        #
        # Dřív to byl bezpodmínečný zápis, takže se do mapy dostala i adresa,
        # která v tabulce není a nikdy nebude - typicky responder_addr z
        # _respond() nebo cíl z _send_to_single_peer(). Takový záznam pak neměl
        # kdo smazat: všechny tři úklidové cesty (try_admit_peer, handshake
        # s detekcí sebe sama, volba 17 v menu) mažou klíče podle self.peers.
        # Naměřeno 30 ze 30 cyklů zapsaných mimo tabulku; ~194 B na záznam,
        # tedy ~64 MB za den při trvalém stropu drahých dotazů z jedné IP -
        # a z jednoho prefixu /64 bez omezení.
        #
        # Skóre má smysl výhradně pro peery v tabulce: čte ho jen
        # _can_admit_locked() při rozhodování, koho vytlačit. Záznam pro
        # kohokoli jiného je mrtvá hmota, ne ztracená informace.
        #
        # Strop tím vzniká implicitně a je tentýž jako u tabulky samotné
        # (MAX_MANUAL_PEERS_TOTAL), takže se nezavádí další konstanta, která by
        # se mohla s MAX_PEERS rozejít.
        klic = tuple(peer)
        with self.peers_lock:
            if klic in self.peers:
                self.peer_last_seen[klic] = get_time()

    def peers_snapshot(self):
        """OPRAVA AUDIT-2026-5 (audit 8. 10. 2026, nález 5): kopie tabulky peerů
        pořízená pod peers_lock.

        Živý self.peers se dosud předával až do json.dump() v save_peers()
        (cestou save_data() z menu i save_data_z_p2p() ze síťových handlerů).
        Seznam na rozdíl od slovníku výjimku nevyhodí, takže se to neprojeví
        pádem - jen může peers.json vyjít nekonzistentní, tedy s přeskočenou
        nebo zdvojenou položkou. Všechna ostatní místa v uzlu si snímek berou
        (`with self.peers_lock: peers_snapshot = list(self.peers)`); tyhle dvě
        cesty byly výjimka.
        """
        with self.peers_lock:
            return list(self.peers)

    def _uklid_evidence_peeru_locked(self):
        # OPRAVA AUDIT-2026-4 (nález 4): jednorázové dorovnání peer_last_seen
        # a offline_peers k self.peers. Volá se se drženým peers_lock.
        #
        # note_peer_activity() i _send_to_single_peer() nově zapisují jen pro
        # peera v tabulce, takže tohle je druhá linie: uklidí záznamy, které
        # vznikly dřív (načtený starý stav) nebo které osiřely tím, že byl peer
        # mezitím vytlačen. Je to táž konstrukce jako _prune_listen_ports_locked(),
        # jen nad mapami, které strop ani TTL neměly vůbec.
        zive = set(self.peers)
        for klic in [k for k in self.peer_last_seen if k not in zive]:
            self.peer_last_seen.pop(klic, None)
        # OPRAVA AUDIT-2026-15 (nálezy 2 a 5): atribut zakládá konstruktor,
        # takže getattr() s náhradní hodnotou už není potřeba.
        for klic in [k for k in self.offline_peers if k not in zive]:
            self.offline_peers.discard(klic)
        # OPRAVA AUDIT-2026-6 (nález N1): evidence odeslaných handshaků patří do
        # stejného úklidu. Vytlačenému peerovi musí značka zmizet - kdyby se
        # vrátil do tabulky, představíme se mu znovu, protože o nás mezitím
        # mohl zapomenout.
        handshaky = getattr(self, 'handshake_sent', None)
        if handshaky:
            for klic in [k for k in handshaky if k not in zive]:
                handshaky.pop(klic, None)

    def _peer_str(self, peer):
        """Jednotný zápis adresy pro log (IPv6 v hranatých závorkách)."""
        return f"[{peer[0]}]:{peer[1]}" if ':' in str(peer[0]) else f"{peer[0]}:{peer[1]}"

    @staticmethod
    def _duvod_spojeni(e):
        """OPRAVA AUDIT-2026-15 (nález 5): krátký, STABILNÍ popis selhání spojení.

        Text se vypisuje jen v přechodové hlášce, ale musí být stabilní:
        socket.timeout má prázdný str(), kdežto OSError nese errno a text
        závislý na jazyku systému. Kdyby se do hlášky dostalo volné str(e),
        rozpad na varianty by znovu zapnul to, co potlačení v add_log() řeší -
        a hlavně by se do logu dostal text z prostředí, kde uzel běží.
        """
        if isinstance(e, socket.timeout):
            return "spojení vypršelo"
        if isinstance(e, ConnectionRefusedError):
            return "spojení odmítnuto"
        if isinstance(e, socket.gaierror):
            return "adresu nelze přeložit"
        if isinstance(e, OSError) and getattr(e, 'errno', None) is not None:
            return f"chyba sítě (errno {e.errno})"
        return type(e).__name__

    def _oznac_peer_offline(self, peer, duvod=None):
        """OPRAVA AUDIT-2026-15 (audit 27. 10. 2026, nálezy 2 a 5): jediná cesta,
        kudy se peer označuje za nedostupného.

        Řeší dvě věci najednou, protože mají tutéž příčinu - evidenci
        dostupnosti si dosud každá cesta vedla sama:

        NÁLEZ 2 (souběh): self.offline_peers se měnila MIMO peers_lock
        (_send_to_single_peer z odchozích vláken), ale
        _uklid_evidence_peeru_locked() ji prochází POD ním. Naměřeno nad
        otevřeným oknem: 151 výjimek, z toho 94x RuntimeError "Set changed size
        during iteration" a 57x "dictionary changed size during iteration".
        V ostrém provozu je okno mikrosekundové (evidence má strop ~24 položek),
        takže dopad byl jedno přeskočené kolo periodické synchronizace - zachytí
        ho `except` z OPRAVY R-3 - ale je to souběh a patří pod zámek.
        Zápis do množiny je proto celý pod peers_lock, včetně testu přechodu.

        NÁLEZ 5 (spam v menu): connect_to_peer() hlásila selhání přes print(),
        takže šla do MENU, ne do P2P logu - a protože se při selhání nenastaví
        handshake_sent, periodický sync ji zkoušel znovu každých 10 s a hlásil
        totéž donekonečna ("Chyba při připojování: timed out"). Potlačování
        opakování v add_log() na to nedosáhne ze dvou důvodů: print() ho obchází
        úplně, a i kdyby ne, hlášky se v logu střídají s "Synchronizuji
        blockchain a mempool..." z téhož kola, takže se nikdy neopakují DVĚ
        STEJNÉ ZA SEBOU, na což je potlačování v add_log() postavené.

        Správná jednotka proto není hláška, ale STAV peera: hlásí se jen
        PŘECHOD dostupný -> nedostupný, tedy jednou při odpojení a jednou při
        opětovném připojení (_oznac_peer_online). Přesně tenhle vzorec už
        _send_to_single_peer() používala, jen si ho vedla lokálně; teď ho má
        celý uzel na jednom místě.

        Vrací True, pokud šlo o přechod (a hláška se tedy zapsala).
        """
        with self.peers_lock:
            # OPRAVA AUDIT-2026-4 (nález 4): do evidence smí JEN peer, který je
            # v tabulce. Pro adresu mimo tabulku je to evidence něčeho, co uzel
            # stejně nesleduje, a množina by neměla strop.
            if peer not in self.peers:
                return False
            if peer in self.offline_peers:
                return False
            self.offline_peers.add(peer)
        # add_log() bere p2p_log_lock, proto se volá až po uvolnění peers_lock:
        # pořadí zámků se tím nikde nekříží.
        popis = f" ({duvod})" if duvod else ""
        self.add_log(f"{Fore.RED}Uzel {self._peer_str(peer)} je offline{popis}{Style.RESET_ALL}")
        return True

    def _oznac_peer_online(self, peer):
        """Druhá polovina OPRAVY AUDIT-2026-15 (nálezy 2 a 5): peer se ozval.

        Hláška jde do logu jen tehdy, když jsme ho předtím vedli jako offline -
        tedy jednou při opětovném připojení, ne při každém úspěšném kole.
        discard() místo remove(): dvě odchozí vlákna mohou dojít k úspěchu
        současně a vzorec `if peer in mnozina: mnozina.remove(peer)` mezi testem
        a odebráním nedržel nic. Vlákno v _spawn_send() navíc žádný except nemá,
        takže by KeyError skončil tracebackem na stderr - tedy právě v tom
        terminálu, který nález 5 odhlučňuje.
        """
        with self.peers_lock:
            if peer not in self.offline_peers:
                return False
            self.offline_peers.discard(peer)
        self.add_log(f"{Fore.GREEN}Uzel {self._peer_str(peer)} je opět online{Style.RESET_ALL}")
        return True

    @staticmethod
    def _provisional_node_id(port):
        # OPRAVA U-20 (nález 2): klíč pro uzel, jehož node_id ještě neznáme -
        # peer z peers.json, z volby v menu nebo uzel, ke kterému jsme se sami
        # připojili dřív, než nám odpověděl handshakem. Odvozuje se od portu,
        # takže je v rámci jedné IP jednoznačný a dva takové uzly se nepřebijí.
        # Dvojtečka v něm zaručuje, že nikdy nekoliduje se skutečným node_id
        # (hex z binascii.hexlify).
        return f"port:{port}"

    def _forget_listen_port_locked(self, ip, port):
        # OPRAVA U-20 (nález 2): odstraní z evidence VŠECHNY záznamy, které pro
        # danou IP ukazují na daný port - tedy skutečný i případný provizorní
        # klíč téhož uzlu. Volá se se drženým peers_lock.
        #
        # Klíčem je nově dvojice, takže "zapomeň na tenhle uzel" už není prostý
        # pop() podle IP: ten by při dvou uzlech na jedné adrese smazal oba,
        # nebo (podle pořadí) ten nesprávný.
        normalized = self.normalize_ip(ip)
        for key in [k for k, v in self.peer_listen_ports.items()
                    if k[0] == normalized and v == port]:
            self.peer_listen_ports.pop(key, None)
            self.peer_listen_seen.pop(key, None)

    def _prune_listen_ports_locked(self):
        # OPRAVA D-08: peer_listen_ports je branka důvěry (OPRAVA #10), takže
        # jeho neomezený růst znamenal, že každá IP, která kdy poslala
        # handshake, zůstala důvěryhodná navždy. Nově má TTL i strop a jeho
        # životnost je navázaná na self.peers: kdo je v peers, nevyprší.
        #
        # OPRAVA U-20 (nález 2): "kdo je v peers" se posuzuje podle DVOJICE
        # (IP, port), ne podle samotné IP. Jinak by záznam uzlu, který v tabulce
        # peerů není, nikdy nevypršel jen proto, že na téže adrese běží jiný uzel,
        # který v ní je.
        now = get_time()
        live = {(self.normalize_ip(ip), port) for ip, port in self.peers}
        for key in list(self.peer_listen_ports.keys()):
            if (key[0], self.peer_listen_ports[key]) in live:
                continue
            if now - self.peer_listen_seen.get(key, 0) > PEER_LISTEN_PORT_TTL:
                self.peer_listen_ports.pop(key, None)
                self.peer_listen_seen.pop(key, None)

        def _evictable():
            return [k for k in self.peer_listen_ports
                    if (k[0], self.peer_listen_ports[k]) not in live]

        # OPRAVA U-20 (nález 2): strop na JEDNU IP. Bez něj by si útočník
        # z jediné adresy vyrobil opakovaným handshakem s vymyšlenými node_id
        # libovolně mnoho záznamů a vytlačil z branky důvěry poctivé uzly -
        # cesta, kterou klíčování podle samotné IP z principu nemělo.
        podle_ip = defaultdict(list)
        for key in self.peer_listen_ports:
            podle_ip[key[0]].append(key)
        for ip, keys in podle_ip.items():
            if len(keys) <= MAX_LISTEN_PORTS_PER_IP:
                continue
            # Vyhazují se nejstarší záznamy, které nemají protějšek v self.peers;
            # zavedený peer se nesmí dát vytlačit cizím handshakem.
            kandidati = sorted(
                [k for k in keys if (k[0], self.peer_listen_ports[k]) not in live],
                key=lambda k: self.peer_listen_seen.get(k, 0))
            while len(keys) > MAX_LISTEN_PORTS_PER_IP and kandidati:
                nejstarsi = kandidati.pop(0)
                self.peer_listen_ports.pop(nejstarsi, None)
                self.peer_listen_seen.pop(nejstarsi, None)
                keys.remove(nejstarsi)

        # Tvrdý globální strop: kdyby TTL nestačilo (nával handshaků), padají
        # nejstarší záznamy mimo self.peers.
        while len(self.peer_listen_ports) > MAX_PEER_LISTEN_PORTS:
            evictable = _evictable()
            if not evictable:
                break
            oldest = min(evictable, key=lambda k: self.peer_listen_seen.get(k, 0))
            self.peer_listen_ports.pop(oldest, None)
            self.peer_listen_seen.pop(oldest, None)

    def touch_listen_port(self, ip, port, node_id=None):
        # OPRAVA U-20 (nález 2): zápis už není prostý přepis "IP -> port", ale
        # zápis pod klíč (IP, node_id). Tentýž uzel, který změnil naslouchací
        # port, má týž klíč, takže se jeho záznam přepíše; JINÝ uzel na téže IP
        # má klíč jiný a přibude vedle. Přesně to je rozdíl, který dřív chyběl.
        with self.peers_lock:
            normalized = self.normalize_ip(ip)
            if node_id:
                # Dozvěděli jsme se skutečnou identitu uzlu, se kterým jsme
                # dosud pracovali jen podle adresy - provizorní záznam téhož
                # portu zahodíme, ať na jeden uzel nezůstanou dva klíče.
                provizorni = (normalized, self._provisional_node_id(port))
                if provizorni in self.peer_listen_ports:
                    self.peer_listen_ports.pop(provizorni, None)
                    self.peer_listen_seen.pop(provizorni, None)
                key = (normalized, node_id)
            else:
                # Bez node_id nemáme čím uzel odlišit. Pokud už na tenhle port
                # nějaký záznam ukazuje (typicky z dřívějšího handshaku), jen mu
                # obnovíme čas - jinak bychom vedle skutečné identity vyrobili
                # druhý, provizorní záznam téhož uzlu.
                key = None
                for k, v in self.peer_listen_ports.items():
                    if k[0] == normalized and v == port:
                        key = k
                        break
                if key is None:
                    key = (normalized, self._provisional_node_id(port))
            self.peer_listen_ports[key] = port
            self.peer_listen_seen[key] = get_time()
            self._prune_listen_ports_locked()

    # OPRAVA T-4 (Nález 2b): is_peer_valid() odstraněna. Byl to nedestruktivní
    # předběžný test "vešel by se?", který si SÁM bral nereentrantní
    # peers_lock. Jediného volajícího (handler 'new_peer') odstranila
    # OPRAVA F-01 právě proto, že tohle zamrazilo celou P2P vrstvu.
    #
    # Zůstala tak metoda bez volajících, jejíž jediná reálná vlastnost byla, že
    # umí nevratně zamrazit uzel, zavolá-li ji někdo z kódu, který zámek drží.
    # Varování v docstringu ten problém neřeší, jen ho popisuje - a varovat
    # před metodou je zbytečné, když ji lze rovnou nemít. Jediná potřebná
    # cesta je _can_admit_locked() níž (volá se s drženým zámkem) a
    # try_admit_peer() pro skutečné přijetí včetně vytlačení.

    def _can_admit_locked(self, peer_addr):
        # Vrací (vejde_se, koho_vytlacit). Volá se se drženým peers_lock.
        if peer_addr in self.peers:
            return True, None

        subnet = self.subnet_key(peer_addr[0])
        same_subnet = [p for p in self.peers if self.subnet_key(p[0]) == subnet]
        if len(same_subnet) >= MAX_PEERS_PER_SUBNET:
            # Diverzita má přednost i před volným místem - jinak by jedna
            # podsíť obsadila tabulku dřív, než se stihne zaplnit poctivými.
            return False, None

        if len(self.peers) < MAX_PEERS:
            return True, None

        # Tabulka je plná. OPRAVA D-08: dřív se tady nový uzel prostě odmítl
        # (return False) a tabulka zůstala zamrzlá napořád. Nově se vytlačí
        # NEJHORŠÍ zavedený peer, pokud je dost starý - "nejhorší" = nejdéle
        # bez úspěšné interakce.
        now = get_time()
        candidates = [p for p in self.peers if p not in self.protected_peers]
        # OPRAVA G-04: tady byla větev
        #     if len(self.peers) - len(candidates) < PROTECTED_PEER_SLOTS:
        #         free_for_network = MAX_PEERS - PROTECTED_PEER_SLOTS   # 16
        #         if len(candidates) <= free_for_network - 1:           # <= 15
        #             return True, None
        # Do tohohle bodu se kód dostane jen při len(self.peers) >= MAX_PEERS,
        # tedy >= 20. Podmínky ale zároveň vyžadují chráněných < 4 a
        # kandidátů <= 15, což dává len(peers) <= 18. Spor - větev byla
        # NEDOSAŽITELNÁ. A kdyby dosažitelná byla, vracela by (True, None),
        # tedy přijetí BEZ vytlačení, a tabulka by přerostla MAX_PEERS.
        # Rezervu pro ruční peery řeší samotná množina protected_peers: chráněné
        # uzly se nikdy neobjeví mezi kandidáty, takže je vytlačit nelze.

        if not candidates:
            return False, None

        worst = min(candidates, key=lambda p: self.peer_last_seen.get(p, 0))
        if now - self.peer_last_seen.get(worst, 0) < PEER_STALE_SECONDS:
            # Všichni jsou čerství - není důvod nikoho vyhazovat. Tabulka
            # plná zdravých peerů je legitimní stav, ne selhání.
            return False, None
        return True, worst

    def try_admit_peer(self, peer_addr):
        # Přijme peera do tabulky, případně za cenu vytlačení nejhoršího.
        # Vrací True, pokud je peer po návratu v tabulce.
        with self.peers_lock:
            if peer_addr in self.peers:
                self.peer_last_seen[peer_addr] = get_time()
                return True
            ok, victim = self._can_admit_locked(peer_addr)
            if not ok:
                return False
            if victim is not None:
                self.peers.remove(victim)
                self.peer_last_seen.pop(victim, None)
                # OPRAVA U-20 (nález 2): maže se záznam VYTLAČENÉHO uzlu, ne
                # všechno, co má jeho IP. Dřív stačila podmínka "na téhle IP už
                # nikdo není" a pop() podle IP; při dvou uzlech na jedné adrese
                # by buď nezmizelo nic, nebo (po přechodu na dvojicový klíč)
                # i záznam toho druhého, který v tabulce zůstává.
                victim_ip = self.normalize_ip(victim[0])
                if (victim_ip, victim[1]) not in self.peers:
                    self._forget_listen_port_locked(victim_ip, victim[1])
                self.add_log(f"{Fore.YELLOW}Peer {victim[0]}:{victim[1]} vytlačen z tabulky (nejdéle bez odezvy), místo uvolněno pro {peer_addr[0]}:{peer_addr[1]}.{Style.RESET_ALL}")
            self.peers.append(peer_addr)
            self.peer_last_seen[peer_addr] = get_time()
            return True

    def start_server(self):
        sockets = []
        for bind_ip in ['0.0.0.0', '::']:
            try:
                addr_info = socket.getaddrinfo(bind_ip, self.port, socket.AF_UNSPEC, socket.SOCK_STREAM, 0, socket.AI_PASSIVE)
                family, socktype, proto, _, sockaddr = addr_info[0]
                s = socket.socket(family, socktype, proto)
                s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
                if family == socket.AF_INET6:
                    try:
                        s.setsockopt(socket.IPPROTO_IPV6, socket.IPV6_V6ONLY, 1)
                    except (AttributeError, OSError):
                        pass
                s.bind(sockaddr)
                s.listen()
                sockets.append(s)
            except OSError as e:
                self.add_log(f"{Fore.YELLOW}Nepodařilo se nabindovat na {bind_ip}:{self.port} - {e}{Style.RESET_ALL}")
        if not sockets:
            print(f"\n{Fore.RED}Chyba: Port {self.port} nelze naslouchat na IPv4 ani IPv6. Vypínám uzel.{Style.RESET_ALL}")
            self.running = False
            self.bind_ready.set()
            return
        self.add_log(f"{Fore.CYAN}Poslouchám na portu {self.port} (IPv4 i IPv6)...{Style.RESET_ALL}")
        self.bind_ready.set()
        # OPRAVA N-2: evidence souběžných příchozích spojení (celkem a po IP).
        # OPRAVA Z-1 (nález 1): evidence se zakládá v __init__, ne tady - viz
        # komentář u inbound_conns. Tady se ZÁMĚRNĚ nenuluje: start_server()
        # běží jednou, ale kdyby se někdy volal podruhé, vynulování by shodilo
        # účetnictví živých spojení.
        while self.running:
            try:
                readable, _, _ = select.select(sockets, [], [], 1.0)
                for s in readable:
                    try:
                        conn, addr = s.accept()
                    except OSError:
                        # OPRAVA N-2: EMFILE/ENFILE nechávají spojení ve frontě,
                        # select() ho hlásí dál jako čitelné a smyčka se točila
                        # na 100 % CPU. Krátká pauza místo busy loopu.
                        time.sleep(0.2)
                        continue
                    if isinstance(addr, tuple) and len(addr) > 2:
                        addr = (addr[0], addr[1])
                    if self.is_blacklisted(addr):
                        conn.close()
                        continue
                    # ETAPA 2: na úrovni accept() zůstává jen mnohem menší
                    # rozpočet na SPOJENÍ - s perzistentními spojeními jich
                    # poctivý uzel potřebuje málo. Zprávy se účtují až v
                    # handle_client_connection().
                    if self.is_connection_rate_limited(addr):
                        conn.close()
                        continue
                    # OPRAVA Z-1 (nález 1): o přijetí rozhoduje _inbound_admit(),
                    # které kromě stropů umí i vytěsnit nejdéle nečinné spojení
                    # z nejvíc zastoupeného prefixu. Plný stav už tedy není
                    # absolutní bariéra - táž změna, jakou pro tabulku peerů
                    # udělala OPRAVA D-08.
                    zaznam, obet, duvod = self._inbound_admit(conn, addr)
                    if obet is not None:
                        # Mimo zámek a shutdown(), ne close() - viz _inbound_admit().
                        self.add_log(f"{Fore.YELLOW}Příchozí spojení z {obet.ip} vytěsněno "
                                     f"(prefix {obet.subnet}, {int(time.time() - obet.last_active)} s "
                                     f"bez aktivity), místo uvolněno pro {addr[0]}.{Style.RESET_ALL}")
                        if obet.sock is not None:
                            try:
                                obet.sock.shutdown(socket.SHUT_RDWR)
                            except OSError:
                                # Protistrana mohla zavřít dřív; doběh obslužného
                                # vlákna to vyřeší samo.
                                pass
                    if zaznam is None:
                        self.add_log(f"{Fore.YELLOW}Příchozí spojení od {addr[0]} odmítnuto: "
                                     f"{duvod}.{Style.RESET_ALL}")
                        conn.close()
                        continue
                    client_thread = threading.Thread(target=self._serve_inbound, args=(conn, addr, zaznam))
                    client_thread.daemon = True
                    try:
                        client_thread.start()
                    except RuntimeError as e:
                        # OPRAVA R-4: evidence se zvyšuje PŘED startem vlákna, ale
                        # odečítá ji až finally v _serve_inbound() - a to při
                        # neúspěšném startu nikdy nedoběhne. Čítače tedy zůstaly
                        # trvale nafouknuté a spojení navíc neuzavřené.
                        # Po MAX_INBOUND_PER_IP selháních přestal uzel přijímat
                        # spojení z té IP, po MAX_INBOUND_CONNECTIONS od kohokoli.
                        # Přesně v okamžiku vyčerpání vláken, tedy tehdy, kdy na
                        # zotavení nejvíc záleží.
                        # OPRAVA Z-1 (nález 1): úklid jde přes _inbound_release(),
                        # aby se s čítači uklidil i záznam v inbound_conns - jinak
                        # by v evidenci zůstalo "živé" spojení bez vlákna a stalo
                        # by se trvalým kandidátem na vytěsnění místo skutečného.
                        self._inbound_release(zaznam)
                        try:
                            conn.close()
                        except Exception:
                            pass
                        self.add_log(f"{Fore.YELLOW}Spojení od {addr} odmítnuto: nepodařilo se spustit obslužné vlákno ({e}).{Style.RESET_ALL}")
                        time.sleep(0.2)
                        continue
            except OSError:
                pass
            except Exception as e:
                self.add_log(f"{Fore.RED}Chyba serveru: {e}{Style.RESET_ALL}")
        for s in sockets:
            try:
                s.close()
            except Exception:
                pass

    @staticmethod
    def _recv_exactly(conn, n, deadline=None):
        # OPRAVA N-2: dřív `buf = b''` a `buf += part` - bytes je neměnný, takže
        # každé přidání kopírovalo celý dosavadní buffer. 10 MiB zprávy po 1 KiB
        # stálo 17,6 s CPU pod GILem (test t_bug2b_recv.py), odesílatele nic.
        # bytearray se prodlužuje amortizovaně v O(1).
        #
        # deadline (time.monotonic()) je CELKOVÁ lhůta na n bajtů. Timeout
        # socketu sám o sobě hlídá jen jedno recv(), takže pomalé odkapávání
        # po bajtu ho nikdy nevyčerpá (slowloris).
        buf = bytearray()
        while len(buf) < n:
            if deadline is not None:
                zbyva = deadline - time.monotonic()
                if zbyva <= 0:
                    raise socket.timeout("lhůta na doručení zprávy vypršela")
                conn.settimeout(zbyva)
            part = conn.recv(min(n - len(buf), 1 << 20))
            if not part:
                return None
            buf += part
        return bytes(buf)

    def rezervuj_prijmovou_pamet(self, nbytes):
        """OPRAVA AUDIT-2026-3 (audit 8. 10. 2026, nález 3): rezervace místa pro
        přijímací buffer jedné zprávy. Vrací True, když se rezervace vešla.

        Strop je GLOBÁLNÍ, přes všechna spojení dohromady, protože právě to je
        veličina, kterou útok z nálezu zvedá: čtyři souběžná recv() po 10 MiB
        drží 40 MiB bez ohledu na to, jak pomalu data kapou. Rychlostní kbelík
        (charge_inbound_bytes) omezuje objem za čas, ale ŠPIČKU paměti neomezí
        vůbec - proto jsou obě zábrany potřeba a ani jedna nenahrazuje druhou.

        Rezervuje se z OHLÁŠENÉ délky (msglen), tedy ještě před alokací
        bytearray v _recv_exactly(). Rezervace se drží po celou dobu zpracování
        zprávy včetně json.loads(), protože naparsovaná struktura je násobně
        větší než drát (7 MiB JSON -> 35 MiB dictů).
        """
        nbytes = max(0, int(nbytes))
        with self.inbound_buffer_lock:
            if self.inbound_buffer_bytes + nbytes > MAX_INBOUND_BUFFER_BYTES:
                return False
            self.inbound_buffer_bytes += nbytes
            return True

    def uvolni_prijmovou_pamet(self, nbytes):
        # Protějšek rezervuj_prijmovou_pamet(). Volá se VÝHRADNĚ z finally,
        # aby rezervace nemohla uniknout - jinak by se uzel po několika
        # přerušených spojeních sám zamkl (táž třída jako OPRAVA R-4
        # u inbound_total).
        nbytes = max(0, int(nbytes))
        with self.inbound_buffer_lock:
            self.inbound_buffer_bytes -= nbytes
            if self.inbound_buffer_bytes < 0:
                self.inbound_buffer_bytes = 0

    def charge_inbound_bytes(self, addr, nbytes):
        """OPRAVA AUDIT-2026-3 (nález 3): per-IP bajtový kbelík na PŘIJÍMANÁ data.

        Zrcadlo charge_expensive_bytes(), jen opačným směrem. Existoval jen
        rozpočet na odchozí drahé odpovědi; příchozí strana účtovala
        is_rate_limited(), tedy JEDEN token za zprávu bez ohledu na velikost -
        zpráva o 1 B a zpráva o 10 MiB stály útočníka stejně. Naměřeno: 4 spojení
        z jedné IP daly +41,7 MB RSS za 4 tokeny z kapacity 200.

        Účtuje se z OHLÁŠENÉ délky, tedy dřív, než se alokuje buffer a dřív, než
        se cokoli přečte ze socketu. Vrací False, když rozpočet nestačí.
        """
        if not addr:
            return True
        ip = self.normalize_ip(addr[0])
        now = time.time()
        with self.rate_lock:
            # OPRAVA K-2, viz _uklid_kbelik().
            self._uklid_kbelik(self.inbound_byte_buckets, RATE_BUCKET_MAX_AGE_LONG, now)
            tokens, last = self.inbound_byte_buckets.get(ip, (float(INBOUND_BYTES_CAPACITY), now))
            tokens = min(float(INBOUND_BYTES_CAPACITY), tokens + (now - last) * INBOUND_BYTES_PER_SECOND)
            if tokens < nbytes:
                self.inbound_byte_buckets[ip] = (tokens, now)
                return False
            self.inbound_byte_buckets[ip] = (tokens - nbytes, now)
            return True

    def _serve_inbound(self, conn, addr, zaznam):
        # OPRAVA N-2: obal, který spojení vždy odečte z evidence - i při výjimce.
        # OPRAVA Z-1 (nález 1): odečítá se přes _inbound_release(), tedy včetně
        # záznamu v inbound_conns a čítače prefixu.
        try:
            self.handle_client_connection(conn, addr, zaznam)
        finally:
            self._inbound_release(zaznam)

    @staticmethod
    def _json_depth_ok(data_buffer, max_depth=20):
        # POZNÁMKA P-2: bajtová smyčka v čistém Pythonu stála nad zprávou
        # o 10 MiB 0,256 s, zatímco json.loads(), který má chránit, 0,026 s -
        # tedy desetkrát víc než to, co hlídá.
        #
        # Předfiltr počítaný v C: hloubka vnoření nemůže být vyšší než POČET
        # otevíracích závorek v celém bufferu. Počítadlo bere i závorky uvnitř
        # řetězců, takže je to horní odhad - když ani ten nepřekročí max_depth,
        # je odpověď jistě True a smyčku netřeba spouštět vůbec. Opačný směr
        # se nezkracuje: vyšší počet závorek NEznamená vyšší hloubku
        # ([][][]... je hloubka 1), proto se dál pokračuje přesným výpočtem.
        #
        # Pomáhá u drtivé většiny provozu (handshake, transakce, request_*,
        # response_chain_info). U plného bloku s tisíci transakcemi předfiltr
        # neprojde a přesná smyčka běží dál - tam je ale cena vázaná na
        # skutečný obsah, ne na levný balast od útočníka.
        if data_buffer.count(b'{') + data_buffer.count(b'[') <= max_depth:
            return True

        # OPRAVA #20: původní kód počítal závorky i uvnitř JSON řetězců, takže
        # adresa nebo data obsahující '[' nebo '{' uměle navyšovaly hloubku
        # (latentní false positive - a falešný nález tady vede rovnou na ban).
        # Sledujeme proto stav "jsme uvnitř řetězce" včetně escapování.
        depth = 0
        in_string = False
        escaped = False
        for byte in data_buffer:
            if in_string:
                if escaped:
                    escaped = False
                elif byte == 92:      # zpětné lomítko
                    escaped = True
                elif byte == 34:      # uvozovka - konec řetězce
                    in_string = False
                continue
            if byte == 34:            # uvozovka - začátek řetězce
                in_string = True
            elif byte == 123 or byte == 91:
                depth += 1
                if depth > max_depth:
                    return False
            elif byte == 125 or byte == 93:
                depth -= 1
        return True

    def handle_client_connection(self, conn, addr, zaznam=None):
        # OPRAVA Z-1 (nález 1): zaznam je položka evidence příchozích spojení.
        # Značí se do ní poslední aktivita, podle které _inbound_vyber_obet_locked()
        # vybírá, koho při plném stavu vytěsnit. None znamená "mimo evidenci"
        # (volání odjinud než z accept smyčky) a chová se jako dosud.
        #
        # OPRAVA #1: spojení obsluhuje víc zpráv za sebou, ne jen jednu.
        #
        # ETAPA 1: navíc umí po TÉMŽE socketu odpovídat. Dotaz s request_id
        # dostane odpověď zpět touto cestou; dotaz bez něj se obslouží po staru
        # (odpověď novým odchozím spojením), takže starší uzly fungují dál.
        #
        # ETAPA 2: rate limiting se přesunul sem, na úroveň ZPRÁV. Dřív se
        # účtoval jednou při accept(), což by s perzistentním spojením znamenalo
        # jeden token na libovolně mnoho zpráv - DoS ochrana by tiše zmizela,
        # aniž by cokoli spadlo nebo se objevilo v logu. Absolutní stropy
        # MAX_MESSAGES_PER_CONNECTION a MAX_BYTES_PER_CONNECTION jsou proto
        # nahrazené rychlostním limitem; jako absolutní meze by dlouhoživotní
        # spojení zabily po 64 zprávách, resp. 10 MiB.
        send_lock = threading.Lock()

        def reply(message):
            # OPRAVA AUDIT-2026-2 (nález 2, 2/2): přijímá i hotový rámec (bytes),
            # aby se odpověď neserializovala dvakrát. Viz PeerConnection.send().
            try:
                data = message if isinstance(message, (bytes, bytearray)) else self._frame(message)
                with send_lock:
                    conn.sendall(data)
                return True
            except (OSError, socket.timeout):
                return False

        # OPRAVA U-20 (audit 7. 10. 2026, nález 2): identita uzlu NA TOMHLE
        # SPOJENÍ. addr nese efemérní zdrojový port, takže se naslouchací adresa
        # odesílatele musí dohledat - a běží-li na jedné IP dva uzly, je node_id
        # z handshaku jediné, čím je od sebe rozeznat. Bez něj odcházely odpovědi
        # i navazující žádosti nesprávnému uzlu a ten náš trvale uvízl na lehčí
        # větvi. Platí jen pro tohle spojení; žádný stav uzlu z toho nevzniká.
        src_node_id = None
        with conn:
            conn.settimeout(CONNECTION_IDLE_TIMEOUT)
            unauthenticated_in_row = 0
            try:
                while self.running:
                    # OPRAVA N-2: celková lhůta na hlavičku i na tělo zprávy.
                    raw_msglen = self._recv_exactly(conn, 4, time.monotonic() + CONNECTION_IDLE_TIMEOUT)
                    if not raw_msglen:
                        # Peer korektně zavřel spojení - běžný konec, ne chyba.
                        # Sem se dostane i spojení, které vytěsnil _inbound_admit()
                        # přes shutdown(): konec proudu, obsluha doběhne normálně
                        # a `with conn:` níž socket zavře.
                        return
                    # OPRAVA Z-1 (nález 1): značka aktivity se posouvá UŽ TEĎ, ne
                    # až po zpracování celé zprávy. Tělo smí podle
                    # MIN_RECV_RATE_BYTES_PER_S kapat stovky sekund, takže by se
                    # poctivé spojení uprostřed velkého přenosu jevilo jako
                    # nečinné a vytěsnilo by se přednostně.
                    self._inbound_touch(zaznam)
                    msglen = struct.unpack('!I', raw_msglen)[0]
                    if msglen > MAX_MESSAGE_SIZE:
                        self.add_log(f"{Fore.RED}Přijatá zpráva příliš velká od {addr}: {msglen} bajtů. Odmítnuto.{Style.RESET_ALL}")
                        self.ban_peer(addr[0], "zpráva překračující MAX_MESSAGE_SIZE")
                        return

                    # ETAPA 2: jeden token za zprávu.
                    if self.is_rate_limited(addr):
                        self.add_log(f"{Fore.YELLOW}Zpráva od {addr} zahozena: vyčerpán limit zpráv.{Style.RESET_ALL}")
                        return

                    # OPRAVA AUDIT-2026-3 (audit 8. 10. 2026, nález 3): rozpočet
                    # i rezervace paměti se účtují z OHLÁŠENÉ délky, tedy ještě
                    # než se ze socketu přečte první bajt těla a než se alokuje
                    # bytearray. Limit výše (is_rate_limited) odebere jeden token
                    # za ZPRÁVU, takže 1bajtová a 10MiB zpráva stály útočníka
                    # stejně - naměřeno 4 spojení z jedné IP = +41,7 MB RSS za
                    # 4 tokeny z kapacity 200, extrapolovaně ~667 MB RAM na 64
                    # spojení, tedy OOM kill na telefonu.
                    if not self.charge_inbound_bytes(addr, msglen):
                        self.add_log(f"{Fore.YELLOW}Zpráva od {addr} ({msglen / 1024:.0f} KB) zahozena: "
                                     f"vyčerpán bajtový rozpočet příjmu. Zavírám spojení.{Style.RESET_ALL}")
                        return
                    if not self.rezervuj_prijmovou_pamet(msglen):
                        self.add_log(f"{Fore.YELLOW}Zpráva od {addr} ({msglen / 1024:.0f} KB) zahozena: "
                                     f"vyčerpán strop souběžně přijímaných dat "
                                     f"({MAX_INBOUND_BUFFER_BYTES // (1024 * 1024)} MiB). "
                                     f"Zavírám spojení.{Style.RESET_ALL}")
                        return

                    # Rezervace se drží po CELOU dobu zpracování zprávy, ne jen
                    # přes recv(): naparsovaný JSON je násobně větší než drát
                    # (měřeno 7 MiB -> 35 MiB dictů), takže uvolnit ji před
                    # json.loads() by měřilo tu menší půlku. finally je nutné -
                    # uniklá rezervace by uzel po několika přerušených spojeních
                    # sama zamkla, což je táž třída chyby jako OPRAVA R-4
                    # u inbound_total.
                    try:
                        data_buffer = self._recv_exactly(
                            conn, msglen,
                            time.monotonic() + MESSAGE_RECV_GRACE_SECONDS + msglen / MIN_RECV_RATE_BYTES_PER_S)
                        if data_buffer is None:
                            self.add_log(f"{Fore.RED}Spojení s {addr} přerušeno při přijímání dat.{Style.RESET_ALL}")
                            return
                        # OPRAVA N-2: _recv_exactly() nechal na socketu zbytek lhůty;
                        # odpověď (reply -> sendall) má mít zase plný timeout.
                        conn.settimeout(CONNECTION_IDLE_TIMEOUT)

                        if not self._json_depth_ok(data_buffer):
                            self.add_log(f"{Fore.RED}Přijatá zpráva má příliš hluboké vnoření. Odmítnuto.{Style.RESET_ALL}")
                            self.ban_peer(addr[0], "příliš hluboce vnořený JSON")
                            return

                        # OPRAVA U-1 (audit 2. 10. 2026, nález 1): totéž co
                        # v PeerConnection._read_loop(). Celočíselný literál delší
                        # než sys.get_int_max_str_digits() (4300) vyhodí z
                        # json.loads() holý ValueError, ne JSONDecodeError. Spojení
                        # se zavřelo tak či tak, ale až přes obecný
                        # `except Exception` na konci téhle metody - a do logu se
                        # psalo "Chyba spojení s ...", což svádí hledat problém
                        # v síti místo ve vadné zprávě. JSONDecodeError je podtřída
                        # ValueError, takže širší tuple pokrývá obojí.
                        try:
                            message = json.loads(data_buffer.decode('utf-8'))
                        except (ValueError, UnicodeDecodeError) as e:
                            self.add_log(f"{Fore.RED}Chyba dekódování JSON od {addr}: {e}{Style.RESET_ALL}")
                            return

                        # OPRAVA U-20 (nález 2): handshake je jediná zpráva, která
                        # identitu odesílatele nese. Zapamatuje se pro zbytek
                        # spojení - další zprávy už jen řeknou "jsem ta IP", což při
                        # dvou uzlech na jedné adrese nestačí. Zapisuje se i tehdy,
                        # když handshake sám neuspěje (cizí chain_id, jiná verze);
                        # takový uzel stejně neprojde brankou z OPRAVY #10, takže
                        # směrování se tím nic nemění.
                        if isinstance(message, dict) and message.get('type') == 'handshake':
                            nid = message.get('node_id')
                            # OPRAVA N6 (audit 10. 10. 2026, nález N6): i délková
                            # mez, nejen typ. Hodnota se stává částí KLÍČE do
                            # peer_listen_ports a drží se po celou dobu spojení -
                            # naměřeno uložené node_id o 200 000 znacích.
                            if isinstance(nid, str) and 0 < len(nid) <= MAX_NODE_ID_LEN:
                                src_node_id = nid

                        accepted = self.handle_message(message, addr, reply=reply, src_node_id=src_node_id)
                    finally:
                        self.uvolni_prijmovou_pamet(msglen)
                        data_buffer = None
                    # OPRAVA Z-1 (nález 1): druhá značka aktivity, po dokončení
                    # zprávy. Zpracování může trvat (replace_chain, add_block pod
                    # zámkem řetězce) a bez tohohle by se spojení, které zrovna
                    # odvedlo tu nejdražší práci, vzápětí jevilo jako nejstarší.
                    self._inbound_touch(zaznam)
                    # ETAPA 2: s perzistentním spojením může neznámý uzel držet
                    # socket otevřený donekonečna a posílat zprávy, které se
                    # všechny zahodí branou z opravy #10 - a stojí nás to vlákno.
                    # Po několika odmítnutích za sebou spojení zavřeme.
                    # OPRAVA B-4: `is False` zůstává záměrně - None tu znamená
                    # "zpráva zpracována, nic k hlášení" (legitimní konec
                    # synchronizace, prázdná dávka, úklid peerů), ne odmítnutí.
                    # Opraveny byly naopak handlery, které None vracely tam, kde
                    # myslely False; ty teď vracejí False výslovně.
                    if accepted is False:
                        unauthenticated_in_row += 1
                        if unauthenticated_in_row >= MAX_UNAUTHENTICATED_MESSAGES:
                            self.add_log(f"{Fore.YELLOW}Uzel {addr} poslal {unauthenticated_in_row} neakceptovaných zpráv za sebou. Zavírám spojení.{Style.RESET_ALL}")
                            return
                    else:
                        unauthenticated_in_row = 0
            except socket.timeout:
                pass
            except Exception as e:
                self.add_log(f"{Fore.RED}Chyba spojení s {addr}: {e}{Style.RESET_ALL}")

    def next_request_id(self):
        with self.request_counter_lock:
            return next(self.request_counter)

    def get_connection(self, peer, connect_timeout=5):
        """ETAPA 1: vrátí živé perzistentní spojení na peera, případně navazuje."""
        if self.is_blacklisted(peer):
            return None
        with self.connections_lock:
            conn = self.connections.get(peer)
            if conn is not None and conn.alive:
                return conn
        try:
            addr_info = socket.getaddrinfo(peer[0], peer[1], socket.AF_UNSPEC, socket.SOCK_STREAM)
            family, socktype, proto, _, sockaddr = addr_info[0]
            sock = socket.socket(family, socktype, proto)
            sock.settimeout(connect_timeout)
            sock.connect(sockaddr)
            sock.settimeout(CONNECTION_IDLE_TIMEOUT)
        except (ConnectionRefusedError, socket.timeout, OSError):
            return None
        conn = PeerConnection(self, peer, sock)
        with self.connections_lock:
            old_conn = self.connections.get(peer)
            self.connections[peer] = conn
        if old_conn is not None and old_conn is not conn:
            old_conn.close()
        return conn

    def drop_connection(self, peer, conn):
        with self.connections_lock:
            if self.connections.get(peer) is conn:
                del self.connections[peer]

    def close_all_connections(self):
        with self.connections_lock:
            conns = list(self.connections.values())
            self.connections.clear()
        for c in conns:
            c.close()

    def send_request(self, peer, message, timeout=REQUEST_TIMEOUT):
        """
        ETAPA 1: pošle dotaz a vrátí odpověď (dict), nebo None.
        Volající MUSÍ počítat s None - spojení mohlo upadnout nebo vypršet.
        """
        conn = self.get_connection(peer)
        if conn is None:
            return None
        return conn.request(message, timeout=timeout)

    def sync_blocks_from_peer(self, peer, max_rounds=2000):
        """
        ETAPA 1: řízené stahování bloků v request/response smyčce, hloubka 1.

        Oproti původnímu řetězu nevyžádaných zpráv má tohle dvě výhody: víme,
        na kterou dávku odpověď patří, a poznáme, že nepřišla vůbec (send_request
        vrátí None) místo abychom čekali na watchdog.
        """
        rounds = 0
        # OPRAVA D-17: jakmile smyčka jednou běží ve fork režimu, musí poznat,
        # že jí byl fork pod rukama zrušen (_abort_fork_sync po vadné dávce
        # nebo watchdog). Bez toho by další kolo poslalo locator od NAŠEHO
        # vrcholu, tedy začalo běžný sync s uzlem, kterého jsme právě zabanovali
        # - a odpověď na něj by založila "nový fork" nad zahozeným bufferem.
        fork_mode_seen = False
        while self.running and rounds < max_rounds:
            rounds += 1
            in_fork = bool(getattr(self, 'syncing_fork', False))
            if fork_mode_seen and not in_fork:
                # OPRAVA N-1: fork mohl skončit i ÚSPĚCHEM (buffer se zpracoval
                # po dosažení stropu). Pak se pokračuje od nového vrcholu jako
                # běžné prodloužení řetězce.
                if getattr(self, 'fork_last_ok', False):
                    self.fork_last_ok = False
                    fork_mode_seen = False
                    in_fork = False
                else:
                    self.add_log(f"{Fore.YELLOW}Řízený sync s {peer} ukončen: fork byl mezitím zrušen.{Style.RESET_ALL}")
                    return False
            fork_mode_seen = fork_mode_seen or in_fork
            tip = self.sync_buffer_tip() if in_fork else None
            if tip:
                req = {'type': 'request_blocks', 'data': {'locator_hashes': [tip[1]]}}
            else:
                req = {'type': 'request_blocks', 'data': {'locator_hashes': self.get_locator_hashes()}}

            resp = self.send_request(peer, req)
            if resp is None or resp.get('type') != 'response_blocks':
                self.add_log(f"{Fore.YELLOW}Řízený sync s {peer} přerušen (bez odpovědi v kole {rounds}).{Style.RESET_ALL}")
                return False
            # OPRAVA N-9: prázdná dávka s has_more=True je protimluv - smyčka by
            # se na ní točila až do stropu max_rounds, aniž by se cokoli stáhlo.
            if not resp.get('data') and resp.get('has_more'):
                self.add_log(f"{Fore.YELLOW}Řízený sync s {peer} přerušen: prázdná dávka s has_more=True.{Style.RESET_ALL}")
                return False

            zruseni_pred = getattr(self, 'fork_abort_count', 0)
            self.handle_message(resp, peer, driven=True)
            if getattr(self, 'fork_abort_count', 0) != zruseni_pred:
                self.add_log(f"{Fore.YELLOW}Řízený sync s {peer} ukončen: dávka z kola {rounds} fork zrušila.{Style.RESET_ALL}")
                return False

            # OPRAVA S-2 (Nález 1): detekce nulového pokroku. Locator dalšího
            # kola se staví ze špičky bufferu; když protistrana pošle tutéž
            # dávku znovu, INSERT OR REPLACE jen přepíše řádky, špička se
            # nehne - a smyčka se ptá pořád na totéž až do max_rounds (2000).
            # Watchdog nečinnosti nezasáhne, protože se obnovuje při každém
            # ÚSPĚŠNÉM zápisu, a ten se povede pokaždé. Samotné přesné
            # účtování bajtů tuhle smyčku nezastaví, proto druhá polovina
            # opravy.
            #
            # tip_po is None = buffer byl mezitím zpracován a zahozen
            # (OPRAVA N-1, úspěšná cesta) - to pokrok je, nekončíme tu.
            if in_fork and tip is not None:
                tip_po = self.sync_buffer_tip()
                if tip_po is not None and tip_po[0] <= tip[0]:
                    self.add_log(f"{Fore.YELLOW}Řízený sync s {peer} ukončen: dávka z kola "
                                 f"{rounds} neposunula buffer (#{tip[0]}).{Style.RESET_ALL}")
                    return False

            if not resp.get('has_more'):
                self.add_log(f"{Fore.GREEN}Řízený sync s {peer} dokončen po {rounds} kolech.{Style.RESET_ALL}")
                return True
        self.add_log(f"{Fore.YELLOW}Řízený sync s {peer} zastaven na stropu {max_rounds} kol.{Style.RESET_ALL}")
        return False

    def _resume_fork_sync(self, kandidati):
        """
        ETAPA 3: obnovení přerušeného stahování forku s JEDNÍM uzlem.

        Uzly zkoušíme po jednom, dokud jeden nedodá pokračování. Broadcast tu
        být nesmí - víc odpovědí na tutéž žádost vedlo na ban poctivého uzlu.

        OPRAVA D-17: tahle metoda byla mrtvý kód. Dvě podmínky si protiřečily:
        pokračovalo se JEN když syncing_fork == False (vstupní podmínka smyčky),
        ale sync_blocks_from_peer() čte špičku bufferu JEN když syncing_fork
        == True. Větev `if tip:` tam tedy byla nedosažitelná a odešel locator
        od NAŠEHO vrcholu. Odpověď pak neprošla testem
        `first_block_index == buffer_tip[0] + 1` v handleru response_blocks,
        spadla do větve "nový fork" a zavolala discard_sync_buffer().

        Následek: rozpracovaný buffer se při každém pokusu zahodil, přenesený
        pokrok byl nulový a hluboký reorg se nad hraničním RTT nedotáhl nikdy -
        přesně ten failure mode, kvůli kterému OPRAVA #6c vznikla. ETAPA 3 ji
        při přepisu vyřadila.

        Příznaky se proto nastavují PŘED voláním smyčky a při neúspěchu zase
        uvolňují, aby uzel neuvázl v syncing_fork bez běžícího stahování.
        """
        # OPRAVA W-1 (audit 9. 10. 2026, nález N-1, doplňkové zjištění): špička
        # bufferu z předchozího pokusu. Posune-li se mezi dvěma pokusy, znamená
        # to, že buffer plní někdo jiný - typicky původní, jen pomalý zdroj,
        # jehož opožděná dávka právě dorazila. V takové chvíli nemá smysl
        # přetahovat fork_peer_ip na dalšího kandidáta: dávky funkčního zdroje
        # by se od té chvíle ignorovaly (ETAPA 3 je váže na jediný uzel), což
        # pravděpodobnost celého nálezu N-1 jen zvyšovalo.
        posledni_tip = None
        # OPRAVA N3 (audit 10. 10. 2026, nález N3): bod forku, kvůli kterému
        # jsme sem šli. Od téhle opravy může jiné vlákno slot mezitím převzít
        # nabídkou s větší prací a založit fork od JINÉHO indexu - obnovovat
        # nad ním ten starý by znamenalo přesně to, čemu tahle oprava brání,
        # jen z druhé strany: přetáhli bychom fork_peer_ip zpátky na kandidáta,
        # který dodává starý fork, a dávky nového zdroje by se ignorovaly.
        puvodni_start = self.fork_start_index
        try:
            for peer in kandidati:
                if not self.running:
                    return
                # Buffer i fork_start_index se čtou ZNOVU pro každý pokus:
                # předchozí kolo mohlo skončit _abort_fork_sync(), který buffer
                # zahodil a fork_start_index vynuloval. Bez fork_start_index by
                # process_sync_buffer() stejně porovnával začátek bufferu s None
                # a všechno zahodil, takže nemá smysl pokračovat.
                tip = self.sync_buffer_tip()
                if not tip or self.fork_start_index is None:
                    return
                if self.fork_start_index != puvodni_start:
                    self.add_log(
                        f"{Fore.GREEN}Mezitím se začal stahovat jiný fork (od "
                        f"#{self.fork_start_index}), obnovu toho od #{puvodni_start} "
                        f"nepřebírám.{Style.RESET_ALL}")
                    return
                if posledni_tip is not None and tip[0] > posledni_tip:
                    self.add_log(
                        f"{Fore.GREEN}Buffer se mezitím posunul na #{tip[0]} - fork dodává "
                        f"někdo jiný, obnovu nepřebírám.{Style.RESET_ALL}")
                    return
                posledni_tip = tip[0]
                self.add_log(f"{Fore.CYAN}Zkouším obnovit fork sync přes {peer} od #{tip[0]}.{Style.RESET_ALL}")
                # OPRAVA U-19 (nález 1): převzetí forku je přechod automatu,
                # takže jde pod fork_lock. Zámek se ale NEDRŽÍ přes
                # sync_blocks_from_peer() - ta čeká na síť a uvnitř se přes
                # handle_message() vrací do týchž příznaků, takže by se vlákno
                # zablokovalo samo na sobě (u reentrantního zámku hůř: držel by
                # ho celou dobu stahování a každý handler response_blocks by
                # čekal). Atomický musí být zápis, ne čekání.
                with self.fork_lock:
                    # syncing_fork musí být nastavené PŘED smyčkou - jinak se locator
                    # nepostaví od špičky bufferu.
                    self.syncing_fork = True
                    # fork_sync_start se posouvá, aby watchdog (FORK_SYNC_IDLE_TIMEOUT)
                    # nesestřelil pokus, který právě začal.
                    self.fork_sync_start = time.time()
                    # Uzel, kterého se ptáme, se stává zdrojem forku. Opožděné dávky od
                    # ostatních pak _store_fork_batch_inner() ignoruje BEZ postihu.
                    self.fork_peer_ip = peer[0]
                if self.sync_blocks_from_peer(peer):
                    return
                # Neúspěch: příznaky uvolníme, ať se uzel nezasekne v syncing_fork
                # s nikým na druhé straně. Buffer a fork_start_index ZŮSTÁVAJÍ -
                # o ně při timeoutu nejde, jde jen o to, že přestalo přicházet.
                with self.fork_lock:
                    self.syncing_fork = False
                    self.fork_peer_ip = None
            self.add_log(f"{Fore.YELLOW}Žádný uzel nedodal pokračování forku. Buffer zůstává pro další pokus.{Style.RESET_ALL}")
        finally:
            # Táž pojistka jako u _store_fork_batch (OPRAVA D-02): žádná cesta,
            # která nastaví stavový příznak, nesmí skončit dřív, než ho uklidí.
            # Tohle vlákno je JEDINÉ, které obnovené stahování řídí - jakmile
            # z metody odejde, dotazy už nikdo neposílá. Kdyby tu syncing_fork
            # zůstalo viset, periodický sync by mlčel celý FORK_SYNC_IDLE_TIMEOUT.
            # Při úspěchu ho uklidil už process_sync_buffer(), tohle je pro
            # zbylé cesty ven (early return i výjimka).
            # OPRAVA U-19 (nález 1): test i zápis pod jedním zámkem - jinak by
            # se mezi ně vešlo založení nového forku jiným vláknem a tahle
            # pojistka by mu příznak sestřelila.
            with self.fork_lock:
                if getattr(self, 'syncing_fork', False):
                    self.syncing_fork = False
                    self.fork_peer_ip = None

    def sync_with_peer(self, peer):
        """ETAPA 1: jedno kolo periodické synchronizace s jedním uzlem."""
        # OPRAVA N-9: sync_chain_periodically() spouštělo každých 10 s nové
        # vlákno pro každého peera bez ohledu na to, jestli předchozí ještě běží.
        # Peer, který tvrdí větší práci a odpovídá pomalu, tak hromadil vlákna
        # lineárně (test t_bug9_sync_threads.py: 6 nových za minutu, každé až
        # 2000 kol). Nově nejvýš jedna synchronizace na peera.
        with self.peers_lock:
            probihajici = self.__dict__.setdefault('sync_in_progress', set())
            if peer in probihajici:
                return
            probihajici.add(peer)
        try:
            self._sync_with_peer_inner(peer)
        finally:
            with self.peers_lock:
                self.sync_in_progress.discard(peer)

    def _sync_with_peer_inner(self, peer):
        # OPRAVA AUDIT-2026-6 (audit 21. 10. 2026, nález N1), druhá polovina:
        # než se peera na cokoli zeptáme, musíme se mu PŘEDSTAVIT.
        #
        # Oprava v connect_to_peer() sama nestačila: tu metodu na peery
        # z peers.json nikdo nevolá. main() je předá rovnou do konstruktoru
        # P2PNode a jediné, co s nimi pak pracuje, je tahle periodická
        # synchronizace - jenže ta rovnou posílala request_chain_info, který
        # protistrana bez předchozího handshaku odmítne brankou důvěry.
        # Uzel se tak každých 10 s ptal a pokaždé dostal ticho (naměřeno:
        # "Dotaz request_chain_info vypršel po 8s" donekonečna, tip zůstal #0).
        #
        # connect_to_peer() je přesně ta představovací rutina: pošle handshake
        # i oba dotazy po JEDNOM socketu (OPRAVA #1) a odpovědi dorazí
        # reaktivně - stejnou cestou, jakou prokazatelně funguje ruční přidání
        # z menu. Proto se tenhle kruh nedokončuje dialogem, ale skončí tady.
        # OPRAVA AUDIT-2026-15 (nález 2): čtení pod zámkem, aby se test nemíjel
        # se souběžným úklidem v _uklid_evidence_peeru_locked().
        with self.peers_lock:
            predstaveni_chybi = peer not in self.handshake_sent
        if predstaveni_chybi:
            self.connect_to_peer(peer)
            return

        resp = self.send_request(peer, {'type': 'request_chain_info'}, timeout=8.0)
        if resp is None:
            # Buď je uzel nedostupný, nebo běží bez téhle změny a odpověděl
            # novým spojením - v tom případě ji zpracovalo handle_message()
            # reaktivně a my tu nemáme co dělat.
            #
            # OPRAVA AUDIT-2026-6: ticho může taky znamenat, že se protistrana
            # mezitím restartovala a na náš handshake si nepamatuje. Značka se
            # proto zahodí a příští kolo se představíme znovu. Tím se spojení
            # po restartu souseda uzdraví samo, bez zásahu uživatele.
            #
            # OPRAVA AUDIT-2026-15 (nález 2): pod peers_lock, viz zápis
            # v connect_to_peer().
            with self.peers_lock:
                self.handshake_sent.pop(peer, None)
            # OPRAVA AUDIT-2026-15 (nález 5): ticho na aplikační dotaz je taky
            # nedostupnost, i když TCP spojení prošlo. Bez tohohle by se uzel,
            # který spojení přijímá a pak mlčí, v logu nikdy neobjevil jako
            # offline - a příští kolo by na něj poslalo connect_to_peer(), jehož
            # hláška se nově hlásí jen při přechodu. Tady je ten přechod.
            self._oznac_peer_offline(peer, "neodpovídá na dotazy")
            return
        # Odpověď přišla, takže peer žije - případný přechod zpět na online.
        self._oznac_peer_online(peer)
        self.handle_message(resp, peer, driven=True)

        # OPRAVA F-04: odpověď se přijme jen tehdy, když jsme si o ni řekli.
        # Zaznamenat se to musí PŘED odesláním, jinak by rychlá odpověď po jiné
        # cestě (starší uzel odpovídá novým spojením) narazila na zavřenou branku.
        self.expect_mempool_from(peer)
        mresp = self.send_request(peer, {'type': 'request_mempool'}, timeout=8.0)
        if mresp is not None:
            self.handle_message(mresp, peer, driven=True)

    @staticmethod
    def _valid_block_dict(bd):
        # OPRAVA D-02: tvarová kontrola dávky, která běží JEŠTĚ PŘED nastavením
        # syncing_fork = True. Původně se surový dict předával rovnou do
        # meets_difficulty(bd['hash'], ...), tedy do int(hash_hex, 16):
        # nehexadecimální hash vyhodil ValueError, chybějící klíč KeyError,
        # a to až POTÉ, co byl příznak nastaven. Výjimka propadla až do obecného
        # except v handle_client_connection, takže _abort_fork_sync() se nikdy
        # nezavolal, příznak zůstal viset a sync_chain_periodically() přestala
        # posílat dotazy. Uzel byl odříznutý až do FORK_SYNC_IDLE_TIMEOUT (60 s)
        # a útočník za to nedostal ani ban - stačilo útok opakovat každých ~10 s.
        #
        # Kontroluje se jen TVAR, ne platnost - ta patří do validate_fork().
        # Cílem je, aby se do cesty za stavovým příznakem nedostalo nic, co by
        # tam mohlo vyhodit neočekávanou výjimku.
        if not isinstance(bd, dict):
            return False
        for k in ('index', 'timestamp', 'transactions', 'previous_hash',
                  'target', 'nonce', 'hash', 'merkle_root'):
            if k not in bd:
                return False
        if not isinstance(bd['hash'], str) or len(bd['hash']) != 64:
            return False
        if any(c not in '0123456789abcdef' for c in bd['hash']):
            return False
        if not isinstance(bd['previous_hash'], str):
            return False
        if not isinstance(bd['transactions'], list):
            return False
        # OPRAVA D-15: kontroloval se jen typ seznamu, ne typ prvků, takže
        # transactions = [None] projde touhle brankou a AttributeError vznikne
        # až uvnitř Block.from_dict(). Branka má zaručit, že za stavovým
        # příznakem nevznikne neočekávaná výjimka - k tomu musí kontrolovat
        # tvar do stejné hloubky, v jaké se s daty dál pracuje.
        if any(not isinstance(t, dict) for t in bd['transactions']):
            return False
        # OPRAVA: tvar POLOŽEK transakcí, ne jen to, že jsou to dicty.
        #
        # Hlavička se hashuje bez transakcí (Block.hlavicka_hash_z_dictu), takže
        # _pow_branka_bloku() váže PoW jen na HLAVIČKU - pole 'transactions'
        # nebylo při zápisu do bufferu vázané ničím. Blok s platným PoW
        # a 'transactions': [{}, {}, ...] proto prošel brankou i PoW, zapsal se
        # do sync_buffer.db a spustil celý process_sync_buffer() + replace_chain(),
        # kde teprve Block.from_dict() selhal - a replace_chain za ValueError
        # NEBANUJE. Táž vadná data přes 'new_block' přitom stála 24hodinový ban.
        # Je to vzorec z OPRAV D-15/U-2/U-7 ("odesílatel stejně vadného bloku
        # vyklouzl podle toho, kterou cestou přišel"), jen v opačném gardu.
        #
        # Kontroluje se jen TVAR a jen do hloubky, v jaké se s daty dál pracuje -
        # záměrně PODMNOŽINA toho, co vynucuje Transaction.from_dict(), aby
        # branka nikdy neodmítla nic, co from_dict() přijme. tx_id, délky hexu,
        # velikost ani podpisy se tu nepočítají; to by stálo přesně tu práci,
        # které se P-2 chtěla vyhnout.
        _I64 = (1 << 63) - 1
        for _t in bd['transactions']:
            if not isinstance(_t.get('from_address'), str) or not isinstance(_t.get('to_address'), str):
                return False
            # OPRAVA W-6 (audit 9. 10. 2026, nález N-5): 'timestamp' je nově
            # povinný i tady, protože ho od téže opravy vyžaduje
            # Transaction.from_dict(). Branka zůstává PODMNOŽINOU from_dict()
            # (neodmítne nic, co from_dict() přijme), jen obě říkají o témže
            # poli totéž - jinak by blok s transakcí bez času prošel brankou,
            # zapsal se do sync bufferu a padl až v replace_chain(), tedy bez
            # postihu, kdežto přes 'new_block' by stál 24hodinový ban. To je
            # nesymetrie pojmenovaná v OPRAVÁCH D-15, U-2 a U-7.
            if 'timestamp' not in _t:
                return False
            for _k in ('amount', 'fee'):
                _v = _t.get(_k)
                if isinstance(_v, bool) or not isinstance(_v, int) or not 0 <= _v <= _I64:
                    return False
            for _k in ('nonce', 'timestamp', 'chain_id'):
                if _k in _t and _t[_k] is not None:
                    _v = _t[_k]
                    if isinstance(_v, bool) or not isinstance(_v, int) or not 0 <= _v <= _I64:
                        return False
            for _k in ('public_key', 'signature', 'data', 'tx_id'):
                if _t.get(_k) is not None and not isinstance(_t[_k], str):
                    return False
        if isinstance(bd['index'], bool) or not isinstance(bd['index'], int):
            return False
        # OPRAVA L-2: branka kontrolovala tvar MĚLČEJI, než se s daty dál
        # pracuje - přesně vzorec, který popisuje OPRAVA D-15. Pole timestamp,
        # nonce, merkle_root a target neprocházela žádnou kontrolou, přestože
        # jdou v _store_fork_batch_inner() rovnou jako parametry do SQLite.
        # Například timestamp jako objekt dá sqlite3.InterfaceError; tu zachytí
        # _store_fork_batch() jako sqlite3.Error a vyhodnotí ji jako CHYBU
        # NAŠEHO DISKU - _abort_fork_sync(ban=False). Uzel tedy zahodí buffer
        # a protistranu nepotrestá, přestože vadná data poslala ona.
        #
        # Kontroluje se pořád jen TVAR, ne platnost: skutečné meze targetu řeší
        # _store_fork_batch_inner() proti FIXED_TARGET a pravidlo pro danou
        # výšku až validate_fork() / is_valid_chain().
        for k in ('timestamp', 'nonce'):
            if isinstance(bd[k], bool) or not isinstance(bd[k], int) or bd[k] < 0:
                return False
            # OPRAVA A-05: horní mez. Python int je neomezený, SQLite INTEGER
            # je 64bitový se znaménkem - hodnota nad 2**63-1 vyhodí při zápisu
            # OverflowError. Branka musí kontrolovat ROZSAH, ne jen typ,
            # protože tahle pole jdou do SQLite jako parametry.
            if bd[k] > (1 << 63) - 1:
                return False
        if not isinstance(bd['merkle_root'], str):
            return False
        # OPRAVA U-8 (audit 5. 10. 2026, nález 2): target MUSÍ být kanonický hex
        # řetězec. Dřív se tu int toleroval "kvůli starším uzlům", ale bez
        # rozsahové kontroly - jako jediné pole branky, zatímco index, timestamp,
        # nonce, version i chain_id mez z OPRAVY A-05 mají. target přitom jde
        # v _sync_row_values() do SQLite jako parametr úplně stejně.
        #
        # Celé odůvodnění (ban za 2**63, zpětná kompatibilita jako past, tichá
        # záměna hex/dec přes TEXT afinitu sloupce) je u téže opravy
        # v Block.from_dict(). Podstatné tady: obě branky teď říkají o targetu
        # TOTÉŽ, což byl cíl OPRAVY N-5.
        if not isinstance(bd['target'], str):
            return False
        # OPRAVA N-5: stejné pravidlo jako Block.from_dict() - malý hex.
        if (not bd['target'] or len(bd['target']) > 64 or bd['target'][0] == '0'
                or any(c not in '0123456789abcdef' for c in bd['target'])):
            return False
        # Nepovinná pole, která jdou do SQLite také (INSERT níž je bere přes
        # .get() s výchozí hodnotou, takže chybět smějí - ale mít vadný typ ne).
        # NAD RÁMEC AUDITU (týž vzorec jako A-05): i version a chain_id jdou
        # v _store_fork_batch_inner() rovnou jako parametry do SQLite, takže
        # potřebují i horní mez. Dnes je pokrývá kontrola hash <-> hlavička
        # (hlavicka_hash_z_dictu() nad hodnotou mimo rozsah struct vrátí None
        # a dávka je odmítnuta i s banem), tedy obrana AŽ ZA touhle brankou.
        # Spoléhat se na druhou linii je přesně to, co OPRAVA #4 zakazuje.
        # OPRAVA: mez je 32 bitů, ne 64 - přesně jako _check_uint(..., 32) v
        # Block.from_dict(). Obě pole jdou v compute_hash() přes struct.pack('!I'),
        # takže hodnota nad 2**32-1 je neplatná tak jako tak; dřív ji ale branka
        # propustila a odmítla ji teprve kontrola hash <-> hlavička. Obě branky
        # mají o témže objektu říkat totéž (viz OPRAVA N-5, U-7, U-8).
        _UINT32_MAX = (1 << 32) - 1
        if 'version' in bd and (isinstance(bd['version'], bool) or not isinstance(bd['version'], int)
                                or not 0 <= bd['version'] <= _UINT32_MAX):
            return False
        if 'chain_id' in bd and (isinstance(bd['chain_id'], bool) or not isinstance(bd['chain_id'], int)
                                 or not 0 <= bd['chain_id'] <= _UINT32_MAX):
            return False
        if bd.get('state_root') is not None and not isinstance(bd.get('state_root'), str):
            return False
        # OPRAVA A-05: totéž co u timestamp/nonce výš. Kontrolovala se jen dolní
        # mez, takže blok s index = 2**70 branku prošel a hodnota ze sítě se
        # dostala až do SELECTu v de-duplikaci handleru response_blocks, kde
        # vyhodila OverflowError. Odesílatel za to navíc nedostal ban (spadlo
        # to do obecného except), takže byl útok opakovatelný donekonečna -
        # přesně nesymetrie popsaná v OPRAVĚ D-15.
        if not 0 <= bd['index'] <= (1 << 63) - 1:
            return False
        # OPRAVA T-1 (Nález 1, 1/2): bajtový strop nad SYROVÝM dictem. Tohle
        # byla JEDINÁ cesta přijímající bloky ze sítě bez kontroly
        # MAX_BLOCK_SIZE_BYTES - add_block(), add_orphan_block(), mine(),
        # _validate_fork_inner(), _is_valid_chain_inner() i handler 'new_block'
        # ji mají, buffer forku ne. To je přímý rozpor s komentářem
        # v _store_fork_batch_inner(): "dvě síťové cesty přijímající bloky se
        # nesmějí lišit v tom, co po nich chtějí."
        #
        # Měří se stejně jako v handleru 'new_block' (tatáž serializace, tatáž
        # mez), protože rozdíl v měření mezi dvěma cestami je přesně ten druh
        # nesouladu, který tenhle nález odhalil.
        #
        # Kontrola je ZÁMĚRNĚ až za všemi typovými testy výš: serializace je
        # tady to nejdražší, co děláme, a za blok se špatným tvarem ji nemá
        # smysl platit. Naopak proti zbytku cesty je levná - parsování bloku
        # počítá tx_id každé transakce.
        try:
            raw_size = len(json.dumps(bd, separators=(',', ':'), sort_keys=True).encode('utf-8'))
        except (TypeError, ValueError):
            # Neserializovatelný dict do SQLite stejně nedojde; tvarová branka
            # ho má odmítnout tady, ne až výjimkou za stavovým příznakem.
            return False
        return raw_size <= MAX_BLOCK_SIZE_BYTES

    def _abort_fork_sync(self, addr, reason, ban=True):
        # Společný úklid při zamítnuté dávce. Buffer se maže, protože dávka byla
        # prokazatelně vadná - navazovat na ni nemá smysl (na rozdíl od timeoutu,
        # kde je buffer v pořádku a jen se přestalo odpovídat, viz OPRAVA #6c).
        #
        # OPRAVA A-2 (3/3): ban=False je pro případ, kdy je na vině NÁŠ disk,
        # ne protistrana. Stahování forku se stejně musí zrušit (buffer je
        # v nejistém stavu), ale 24hodinový ban poctivého uzlu za naši chybu
        # I/O je přesně ten failure mode, který OPRAVA #1 i ETAPA 3 odstraňují.
        # OPRAVA N-1: počítadlo zrušení - řídicí smyčka sync_blocks_from_peer()
        # podle něj pozná, že dávka z TOHOTO kola fork zrušila (i bez banu), a
        # nebude se ptát znovu na totéž až do stropu max_rounds.
        self.fork_abort_count = getattr(self, 'fork_abort_count', 0) + 1
        if ban:
            self.add_log(f"{Fore.RED}DoS ochrana: {reason} Uzel ignoruji.{Style.RESET_ALL}")
        else:
            self.add_log(f"{Fore.YELLOW}Stahování forku zrušeno: {reason}{Style.RESET_ALL}")
        if addr and ban:
            self.ban_peer(addr[0], reason, BAN_DURATION_PROTOCOL)
        # OPRAVA U-19 (nález 1): úklid je přechod stavového automatu jako
        # každý jiný, takže patří pod fork_lock - jinak by zrušení forku mohlo
        # proběhnout uprostřed zakládání nového a smazat mu buffer pod rukama.
        # Volá se jak zevnitř již drženého zámku (handler response_blocks), tak
        # mimo něj (_store_fork_batch); proto je fork_lock reentrantní.
        with self.fork_lock:
            self.syncing_fork = False
            self.fork_start_index = None
            self.fork_sync_start = 0
            self.fork_peer_ip = None
            self.discard_sync_buffer()

    def _store_fork_batch(self, blocks_data, first_block_index, last_block_data, addr, ip_port, has_more, driven=False, src_node_id=None):
        # OPRAVA D-02: obal, který zaručuje, že z téhle cesty NIKDY neodejde
        # výjimka bez úklidu stavu. Obecné pravidlo, které z nálezu plyne:
        # žádná cesta, která nastaví stavový příznak, nesmí skončit výjimkou
        # dřív, než ho zase uklidí. Vlastní tělo je v _store_fork_batch_inner();
        # tady je jen pojistka, aby se na disciplínu uvnitř nemuselo spoléhat.
        #
        # _abort_fork_sync() banuje, což je u neočekávané výjimky z dat
        # protistrany správně: dávku poslal on a její tvar je jeho odpovědnost.
        try:
            return self._store_fork_batch_inner(blocks_data, first_block_index, last_block_data,
                                                addr, ip_port, has_more, driven, src_node_id)
        except (sqlite3.Error, OSError, MemoryError) as e:
            # OPRAVA A-2 (3/3): tohle jsou chyby NAŠEHO stroje - plný disk,
            # zamčená databáze, došlá paměť. Data protistrany s nimi nemají nic
            # společného, takže se fork zruší, ale bez postihu.
            self._abort_fork_sync(
                addr,
                f"lokální chyba při zpracování dávky forku ({type(e).__name__}: {e}). Protistrana není na vině, žádný postih.",
                ban=False)
            return
        except Exception as e:
            self._abort_fork_sync(addr, f"neočekávaná chyba při zpracování dávky forku ({type(e).__name__}: {e}).")
            return

    @staticmethod
    def _pow_branka_bloku(bd):
        """
        Cena za zápis bloku do sync bufferu: platný target, hash odpovídající
        hlavičce a splněný PoW. Vrací None, nebo text důvodu odmítnutí.

        OPRAVA U-19 (audit 7. 10. 2026, nález 1, 2/2): tyhle tři kontroly
        bývaly jen uvnitř smyčky v _store_fork_batch_inner(), tedy AŽ ZA
        destruktivním discard_sync_buffer() v handleru response_blocks. Dávka
        bez jediného vytěženého hashe tak stihla smazat rozpracovaný buffer
        poctivého peera dřív, než ji kdokoli ověřil - naměřeno 30 bloků
        v bufferu před, 0 po, a odesílatel za to zaplatil jen 24hodinovým
        banem, který si z jiné IP koupí znovu.

        Metoda je ZÁMĚRNĚ bez vedlejších efektů: nic neuklízí, nebanuje a na
        žádný příznak nesahá. Právě proto se dá zavolat jako branka PŘED
        přechodem automatu, kde ještě nevíme, čí práci bychom zahodili.

        Nezávislá na stavu uzlu (předky forku tu ještě nemáme), takže je
        statická. Cena je konstantní na blok - hash hlavičky nezávisí na
        transakcích, nic se neparsuje (viz Block.hlavicka_hash_z_dictu).

        OPRAVA Y-1 (audit 14. 10. 2026, nález 1): branku nově volá i handler
        'new_block', tedy nad dictem, který NEPROŠEL tvarovou brankou
        _valid_block_dict() - ta běží jen na cestě 'response_blocks'. Dosud se
        tu na její záruky mlčky spoléhalo: chybějící klíč 'target' nebo 'hash'
        by vyhodil KeyError a spolkl by ho až catch-all v handle_message().
        To je přesně vzorec, který si kód jinde zakazuje (OPRAVA #4, D-15,
        G-07) - kontrakt "vrať None, nebo text důvodu" musí platit nad JAKÝMI
        daty ze sítě, ne jen nad těmi, která prošla jinou brankou.

        Na cestě 'response_blocks' se tím nic nemění: _valid_block_dict()
        přítomnost i tvar všech těchto polí vynucuje, takže žádná z nových
        podmínek tam nemůže být pravdivá.
        """
        # OPRAVA K-3: hodnota 'index' se do hlášky vkládá
        # přes zkrat(). Na cestě 'response_blocks' je tvar vynucený brankou
        # _valid_block_dict(), ale na cestě 'new_block' (zavedené OPRAVOU Y-1)
        # je surový od protistrany - a text téhle hlášky jde dál i do
        # ban_peer(reason), tedy do druhé hlášky logu. Táž úvaha jako u OPRAVY
        # N1: hodnotu od protistrany se do logu nevkládá nezkrácená.
        if not isinstance(bd, dict):
            return "Blok není objekt JSON."
        for klic in ('target', 'hash', 'index', 'timestamp', 'previous_hash', 'merkle_root'):
            if klic not in bd:
                return f"Blok #{zkrat(bd.get('index'))} nemá povinné pole hlavičky '{klic}'."

        # OPRAVA AUDIT-2026-17: OverflowError doplněn do tuple a nečíselné
        # typy se odmítají JEŠTĚ PŘED int().
        #
        # json.loads() přijímá nestandardní literály Infinity / -Infinity / NaN
        # (parse_constant je ve výchozím stavu zapnutý), takže 'target' mohl
        # přijít jako float('inf') - a int(inf) vyhodí OverflowError, která NENÍ
        # podtřídou ValueError. Kontrakt téhle branky ("vrať None, nebo text
        # důvodu") tím přestal platit a výjimku spolkl až catch-all
        # v handle_message(). Důsledkem byla ztráta POSTIHU, tedy přesně druhá
        # polovina nálezu OPRAVY Y-1: blok s targetem 'zz' stál odesílatele
        # BAN_DURATION_PROTOCOL, týž blok s targetem Infinity byl zdarma a
        # opakovatelný donekonečna (naměřeno 200 zpráv, žádný ban).
        #
        # Dosažitelné to bylo VÝHRADNĚ z handleru 'new_block', který brankou
        # _valid_block_dict() neprochází. Na cestě 'response_blocks' ta branka
        # vynucuje isinstance(bd['target'], str), takže se tam nic nemění.
        #
        # Konsenzus se NEMĚNÍ: takový blok odmítnou všechny tři validátory tak
        # jako tak (Block.from_dict vyžaduje kanonický hex řetězec), jen se teď
        # odmítne se správnou diagnostikou a se stejným postihem jako sesterské
        # případy. Táž úvaha jako u OPRAV N-5, U-7 a U-8: dvě branky mají
        # o témže poli říkat totéž.
        if not isinstance(bd['target'], (str, int)) or isinstance(bd['target'], bool):
            return f"Blok #{zkrat(bd.get('index'))} má nečitelný target."
        try:
            target_val = int(bd['target'], 16) if isinstance(bd['target'], str) else int(bd['target'])
        except (TypeError, ValueError, OverflowError):
            return f"Blok #{zkrat(bd.get('index'))} má nečitelný target."

        if target_val <= 0 or target_val > FIXED_TARGET:
            return (f"Blok #{zkrat(bd.get('index'))} deklaruje target mimo povolený rozsah "
                    f"(snazší než síťové minimum).")

        # OPRAVA Y-1: `hlavicka is None` se testuje VÝSLOVNĚ. Dřív tu stálo
        # jen `... != bd['hash']`, jenže hlavicka_hash_z_dictu() vrací None,
        # když hlavičku nelze zakódovat - a pro bd['hash'] = None je
        # `None != None` NEPRAVDA, takže se propadlo do meets_difficulty(None),
        # kde int(None, 16) vyhodí TypeError. Na cestě 'response_blocks' to
        # dosažitelné nebylo (branka vynucuje 64 znaků malého hexa), na nové
        # cestě z 'new_block' ano.
        hlavicka = Block.hlavicka_hash_z_dictu(bd, target_val)
        if hlavicka is None or hlavicka != bd['hash']:
            return f"Blok #{zkrat(bd.get('index'))} má hash, který neodpovídá jeho hlavičce."

        if not Blockchain.meets_difficulty(bd['hash'], target_val):
            return f"Blok #{zkrat(bd.get('index'))} nesplňuje deklarovaný target."

        return None

    @staticmethod
    def _merkle_branka_bloku(bd):
        """OPRAVA Y-2 (audit 14. 10. 2026, nález 2): váže pole 'transactions'
        na vytěženou práci. Vrací None, nebo text důvodu odmítnutí.

        _pow_branka_bloku() výše hashuje ZÁMĚRNĚ jen hlavičku, aby se blok dal
        ocenit bez parsování transakcí (OPRAVA P-2). Druhá strana té mince ale
        nikde ošetřená nebyla: _valid_block_dict() kontroluje TVAR transakcí,
        ale nikdy neporovná merkle_root s jejich OBSAHEM, takže pole
        'transactions' nebylo vázané na nic, co by stálo práci. Odesílatel si
        tedy objem zápisu do sync_buffer.db vybíral sám, nezávisle na PoW:
        vzít blok s reálně vytěženou hlavičkou, nechat hlavičku bajt za bajtem
        a vyměnit jen transakce dalo 1 047 567 B místo 795 B na drátě, tedy
        1 324x víc zápisu na flash za tutéž práci. Strop bufferu se naplnil
        62 takovými bloky místo 82 517 poctivých.
        Blok nakonec padl až v replace_chain() na nesedícím merkle rootu -
        tedy BEZ postihu, protože ta cesta za ValueError nebanuje. Je to
        nesymetrie pojmenovaná v OPRAVÁCH D-15, U-2 a U-7: odesílatel stejně
        vadného bloku vyklouzl podle toho, kterou cestou přišel.

        Komentář u OPRAVY A-3 přitom na cenu útoku výslovně spoléhá ("cena pro
        útočníka je jen PoW") a celý rozpočet MAX_SYNC_BUFFER_BYTES je od té
        úvahy odvozený. Teprve tímhle to platí: merkle_root je pole hlavičky,
        hlavička je pod PoW, takže shoda rootu s obsahem připoutá transakce
        k vytěžené práci.

        CENA: transakce se tu musí naparsovat, a naparsují se podruhé
        v replace_chain(). Je to vědomá výměna. Platí se jen za bloky, které UŽ
        PROKÁZALY práci (PoW branka běží dřív a dávku při prvním selhání
        zruší), kdežto zápis na flash a následné zahození celého bufferu se
        dosud platily i za bloky, které práci neprokázaly žádnou.

        Parsování vede přes Transaction.from_dict() a compute_merkle_root(),
        tedy přes JEDINÝ zdroj pravdy o kódování. Ruční kopie té serializace se
        tu záměrně nepíše - rozejití dvou kopií hlavičky je v tomhle kódu
        dokumentovaná past (viz Block.hlavicka_hash_z_dictu a mining_worker).

        OPRAVA AUDIT-2026-14 (audit 25. 10. 2026, nález 4): doplněn týž
        isinstance guard, jaký má sesterská _pow_branka_bloku() od OPRAVY Y-1.
        Bez něj kontrakt "vrať None, nebo text důvodu" nad ne-dictem neplatil:
        bd.get() vyhodilo AttributeError ('NoneType' object has no attribute
        'get') a spolkl by ho až catch-all v handle_message().

        Dnes to dosažitelné NENÍ - _pow_branka_bloku() běží dřív a nad
        ne-dictem se vrátí, a na cestě 'response_blocks' tvar vynucuje
        _valid_block_dict(). Právě to je ale ten vzorec, který si kód jinde
        výslovně zakazuje (OPRAVA #4, D-15, G-07): branka nesmí spoléhat na to,
        že ji někdo jiný zavolá ve správném pořadí.

        OPRAVA AUDIT-2026-15 (audit 27. 10. 2026, nález 3): dokončení téže
        myšlenky o jedno pole dál. Předchozí oprava dala isinstance guard celé
        funkci a `bd['transactions']` schovala do try, ale `bd['merkle_root']`
        o pár řádků níž zůstal nechráněný - a to je POVINNÉ pole hlavičky,
        které v dictu chybět může. Nad blokem bez něj funkce vyhodila
        KeyError('merkle_root'), tedy přesně to, co její kontrakt zakazuje
        (naměřeno: sesterská _pow_branka_bloku() nad týmž vstupem korektně
        vrátila text "Blok #1 nemá povinné pole hlavičky 'merkle_root'.").

        Dosažitelné to opět NENÍ - jediný volající pouští PoW branku dřív a ta
        chybějící 'merkle_root' zachytí - ale je to táž vada druhé linie, jakou
        řešila AUDIT-2026-14, a platí pro ni tentýž argument: branka se nesmí
        spoléhat na pořadí volání. Řeší se stejnou technikou jako v PoW brance,
        tedy explicitní kontrolou přítomnosti pole, aby se vracel SROZUMITELNÝ
        důvod (text putuje do _abort_fork_sync() jako důvod 24hodinového banu),
        ne jen obecné "nečitelná data".
        """
        if not isinstance(bd, dict):
            return "Blok není objekt JSON."
        # Totéž pojmenování chybějícího pole, jaké dává _pow_branka_bloku().
        if 'merkle_root' not in bd:
            return "Blok nemá povinné pole hlavičky 'merkle_root'."
        try:
            transakce = [Transaction.from_dict(t) for t in bd['transactions']]
        except (ValueError, KeyError, TypeError) as e:
            # Transaction.from_dict() má kontrakt "ven jde vždy ValueError";
            # zbytek tuple je druhá linie, stejně jako u OPRAVY G-07.
            return (f"Blok #{bd.get('index')} obsahuje nečitelnou transakci "
                    f"({zkrat(e)}).")

        # ZMĚNA 5 (názvosloví): "Transaction root" místo "merkle root", viz
        # obsáhlý komentář u téže kontroly v add_block(). Tenhle text nejde jen
        # do logu - putuje i do _abort_fork_sync() jako důvod banu, takže se
        # protistraně v hlášce o 24hodinovém banu říká totéž jméno, jaké uvidí
        # ve vlastním logu i ve výpisu bloku.
        if compute_merkle_root(transakce) != bd['merkle_root']:
            return (f"Blok #{bd.get('index')} má Transaction root, který neodpovídá "
                    f"jeho transakcím.")

        return None

    def _store_fork_batch_inner(self, blocks_data, first_block_index, last_block_data, addr, ip_port, has_more, driven=False, src_node_id=None):
        # Ověření dávky před zápisem do bufferu + samotný zápis.
        # Vytaženo do samostatné metody, aby ji mohla volat i cesta navazující
        # na rozpracovaný buffer po timeoutu (OPRAVA #6c).
        #
        # ETAPA 3: kontrola návaznosti NA HRANICI DÁVEK odsud zmizela a přesunula
        # se do process_sync_buffer(), nad kompletní buffer. Důvod je konkrétní
        # a byl to živý bug: watchdog z opravy #6c rozesílal žádost o pokračování
        # BROADCASTEM všem uzlům. Odpovědělo jich víc, první odpověď posunula
        # špičku bufferu a druhá - od stejně poctivého uzlu, se stejnými bloky -
        # už na posunutou špičku nenavazovala. Výsledkem byl 24hodinový ban
        # poctivého uzlu, tedy zase failure mode chyby #1.
        #
        # Stahování forku je proto nově vázané na jeden uzel a dávky od ostatních
        # se tiše ignorují. Zároveň to dává atributovatelnost: když je buffer na
        # konci nesouvislý, víme, kdo ho dodal.
        # OPRAVA U-19 (nález 1): i tohle je test-and-set, takže patří pod
        # fork_lock. Bez něj mohla dvě vlákna obě vidět fork_peer_ip is None,
        # obě se zapsat a obě pokračovat - a pravidlo ETAPY 3 "fork se stahuje
        # od JEDNOHO uzlu", na kterém stojí atributovatelnost vadného bufferu,
        # by přestalo platit přesně v okamžiku, kdy je nejvíc potřeba.
        peer_ip = addr[0] if addr else None
        with self.fork_lock:
            if self.fork_peer_ip is None:
                self.fork_peer_ip = peer_ip
            zdroj_forku = self.fork_peer_ip
            # OPRAVA W-1 (audit 9. 10. 2026, nález N-1): fork_start_index se čte
            # UŽ TADY, pod tímtéž zámkem - branka návaznosti níž ho potřebuje
            # dřív, než se sáhne na buffer. Dřív se četl až o dvě stě řádků níž
            # (viz OPRAVA U-19, kde se čtení scelilo do jediného přístupu).
            fork_start_snapshot = self.fork_start_index
        if peer_ip != zdroj_forku:
            self.add_log(f"{Fore.YELLOW}Dávka od {ip_port} ignorována: fork se stahuje z {zdroj_forku}. Žádný postih.{Style.RESET_ALL}")
            return

        # OPRAVA W-1 (audit 9. 10. 2026, nález N-1): BRANKA NÁVAZNOSTI, a to
        # JEŠTĚ PŘED jakýmkoli zápisem do bufferu.
        #
        # Dávka se dosud zapisovala bez ověření, že navazuje na špičku bufferu;
        # souvislost se záměrně kontrolovala až v process_sync_buffer() nad
        # hotovým bufferem (ETAPA 3, aby se nebanovaly poctivé uzly za
        # přeuspořádané dávky). Jenže zápis je INSERT OR REPLACE podle
        # block_index, takže nenavazující dávka buffer PŘEPÍŠE - a
        # process_sync_buffer() pak zjistí, že nezačíná na očekávaném indexu,
        # a zahodí ho CELÝ, včetně stovek poctivě stažených bloků.
        #
        # Není to teorie a není k tomu potřeba útočník:
        #   1. watchdog po FORK_SYNC_IDLE_TIMEOUT spustí _resume_fork_sync(),
        #   2. ta zkouší sousedy jednoho po druhém a každému nastaví
        #      fork_peer_ip, takže se jeho dávky přijímají,
        #   3. soused, který náš fork NEZNÁ, nenajde v DB žádný hash z locatoru
        #      a handler request_blocks mu pošle bloky od indexu 0,
        #   4. ty se zapíšou a rozbijí souvislost bufferu.
        # Fork je typicky menšinová větev, takže většina sousedů ho nezná a
        # pravděpodobnost téhle cesty je vysoká. U plných bloků to znamená až
        # ~63 MiB staženo a zapsáno na flash nazmar, opakovaně - tedy přesně
        # ten nulový přenesený pokrok, kvůli kterému vznikla OPRAVA #6c.
        #
        # Branka je ZÁMĚRNĚ nedestruktivní a BEZ POSTIHU: nenavazující dávka
        # není důkaz zlého úmyslu, poctivý soused prostě odpověděl na locator,
        # který nezná. Je to totéž rozlišení, jaké už dělá process_sync_buffer()
        # mezi "díra v dávkách" (bez postihu) a "nesedící previous_hash UVNITŘ
        # dávky" (ban) - a ta druhá kontrola zůstává beze změny níž.
        #
        # Při nejistotě (prázdný buffer A neznámý fork_start_index) se nebrání
        # ničemu: rozhodne až process_sync_buffer() nad kompletními daty, tedy
        # jako dosud. Je to táž úvaha jako u MissingChainDataError, jen tady je
        # bezpečná strana ta, která nic nemaže.
        tip_bufferu = self.sync_buffer_tip()
        if tip_bufferu is None:
            ocekavany_index = fork_start_snapshot
            ocekavany_rodic = None
        else:
            ocekavany_index = tip_bufferu[0] + 1
            ocekavany_rodic = tip_bufferu[1]

        if ocekavany_index is not None:
            try:
                prvni_index_davky = int(blocks_data[0]['index'])
            except (TypeError, ValueError, KeyError):
                # Tvarová branka _valid_block_dict() tohle už nepropustí; je to
                # druhá linie, aby se za ní nemohla objevit neočekávaná výjimka.
                self._abort_fork_sync(addr, "Dávka nemá čitelné indexy.")
                return
            if (prvni_index_davky != ocekavany_index
                    or (ocekavany_rodic is not None
                        and blocks_data[0].get('previous_hash') != ocekavany_rodic)):
                self.add_log(
                    f"{Fore.YELLOW}Dávka od {ip_port} začíná blokem #{prvni_index_davky}, "
                    f"ale buffer čeká #{ocekavany_index}. Nejspíš náš fork nezná. "
                    f"Dávku zahazuji, buffer ponechávám, žádný postih.{Style.RESET_ALL}")
                return

        for i, bd in enumerate(blocks_data):
            # OPRAVA #8: původní kód porovnával hash bloku s targetem, KTERÝ SI
            # BLOK SÁM DEKLAROVAL. Útočníkovi stačilo uvést target o jedničku
            # vyšší než vlastní hash a kontrola prošla zdarma - komentář sliboval
            # DoS ochranu, kterou kód neposkytoval, a sync_buffer.db se dal
            # plnit balastem. Nově se target porovnává i proti skutečnému
            # síťovému stropu: nesmí být volnější než FIXED_TARGET (počáteční,
            # tedy nejsnazší povolená obtížnost). Tím se z kontroly stává reálná
            # cena za zápis do bufferu. Přesné pravidlo pro danou výšku
            # (calculate_expected_target) se ověřuje až ve validate_fork /
            # is_valid_chain, protože tady ještě nemáme předky forku.
            #
            # OPRAVA P-2: hash MUSÍ odpovídat hlavičce, kterou blok deklaruje.
            #
            # Bez téhle kontroly nebyla předchozí kontrola meets_difficulty()
            # cenou za nic: pole 'hash' nebylo k obsahu bloku ničím vázané, takže
            # útočníkovi stačil JEDINÝ hash splňující FIXED_TARGET a mohl ho
            # zopakovat v libovolném počtu bloků (hash = previous_hash = H, indexy
            # po sobě). Obě zbylé kontroly to pustí: previous_hash uvnitř dávky
            # sedí (H == H) a meets_difficulty testuje pořád týž H. Hash si navíc
            # nemusel ani vytěžit - hash kteréhokoli existujícího bloku řetězce je
            # veřejný a svůj target z definice splňuje, takže reálná cena byla
            # NULA. Ověřeno: 200 řádků v sync_buffer.db za 0 hashů, bez postihu;
            # při plných blocích ~60 MiB zápisu na flash za jedno kolo, opakovaně.
            #
            # Komentář u OPRAVY A-3 přitom na tuhle cenu výslovně spoléhá
            # ("cena pro útočníka je jen PoW"). Teprve tímhle řádkem to platí.
            #
            # Je to TÁŽ kontrola, jakou už dělá handler 'new_block'
            # ("rychlá validace PoW") - dvě síťové cesty přijímající bloky se
            # nesmějí lišit v tom, co po nich chtějí.
            #
            # OPRAVA T-1 (Nález 1): druhá polovina téhož pravidla, tedy strop
            # MAX_BLOCK_SIZE_BYTES, tady dlouho CHYBĚLA. Dnes ho tahle cesta má
            # taky, jen o kus dřív - v tvarové brance _valid_block_dict(), kudy
            # vede každé volání _store_fork_batch(). Kdo sem přijde hledat
            # MAX_BLOCK_SIZE_BYTES, najde ho tam.
            #
            # OPRAVA U-19 (nález 1, 2/2): vlastní tři kontroly se přestěhovaly do
            # _pow_branka_bloku(), protože je potřebuje i handler response_blocks
            # JEŠTĚ PŘED discard_sync_buffer(). Jedna implementace, dvě místa
            # volání - ne dvě kopie, které se časem rozejdou.
            duvod = self._pow_branka_bloku(bd)
            if duvod is not None:
                self._abort_fork_sync(addr, duvod)
                return

            # OPRAVA Y-2 (nález 2): druhá půlka ceny za zápis do bufferu -
            # transakce musí odpovídat merkle rootu v hlavičce, a tím i PoW.
            # Běží AŽ ZA PoW brankou záměrně: tahle kontrola transakce parsuje,
            # takže ji platíme jen za blok, který už práci prokázal.
            # Ban je na místě ze stejného důvodu jako o pár řádků níž
            # u nenavazující dávky: hlavička je platná a transakce k ní nesedí,
            # takže je prokazatelně složil odesílatel.
            duvod = self._merkle_branka_bloku(bd)
            if duvod is not None:
                self._abort_fork_sync(addr, duvod)
                return

            # Nesoulad UVNITŘ dávky je prokazatelná vina odesílatele - ban zůstává.
            if i > 0:
                if bd['previous_hash'] != blocks_data[i-1]['hash'] or bd['index'] != blocks_data[i-1]['index'] + 1:
                    self._abort_fork_sync(addr, "Bloky v dávce nenavazují.")
                    return

        # OPRAVA A-3 (hloubkový strop): hloubka se měří od fork_start_index,
        # tedy přesně tím pravidlem, kterým ji potom posoudí replace_chain().
        # Cokoli nad MAX_REORG_DEPTH je zápis na flash, o kterém dopředu víme,
        # že skončí hláškou "Navrhovaný fork z bufferu není platný". Dřív se
        # takových bloků dalo zapsat kolik útočník chtěl.
        # OPRAVA N-1: dřív se tu jako "hloubka" počítala DÉLKA OCASU nové větve
        # (poslední index dávky - fork_start_index + 1) a nad MAX_REORG_DEPTH
        # se sync zrušil S BANEM na 24 h. MAX_REORG_DEPTH ale omezuje, kolik
        # NAŠICH bloků se smí zahodit - ne kolik bloků má delší větev. Uzel se
        # slepým vrcholem (stačil jediný osiřelý blok), který byl pozadu o víc
        # než ~1000 bloků, se proto už nikdy nedosynchronizoval a postupně
        # zabanoval všechny poctivé peery (ověřeno testem t_bug1_fork_sync.py).
        #
        # Nově dvě nezávislé veličiny:
        #   hloubka reorgu = max_block_index - fork_start_index + 1 (naše bloky)
        #                    -> nad limitem zrušit, ale BEZ banu - jiná větev
        #                       není důkaz zlého úmyslu,
        #   délka ocasu    = počet bloků v bufferu -> strop jen kvůli paměti
        #                    a flash; po jeho dosažení se zpracuje, co už v
        #                    bufferu je, a zbytek se dotáhne běžným syncem jako
        #                    prosté pokračování.
        #
        # OPRAVA AUDIT-2026-1 (nález 1): tady dřív stálo, že obsah bufferu je po
        # dosažení stropu "typicky už těžší než naše větev". To je domněnka,
        # která se nikde neověřovala a u plných bloků NEPLATÍ: do bufferu se
        # jich vejde ~62, takže naše větev delší než ~62 bloků prefix vždycky
        # přebije. Formulace je opravená, protože takové tvrzení bere čtenář
        # příštího auditu jako hotovou informaci a nekontroluje ho - stejný
        # důvod, jaký uvádí OPRAVA G-05/G-06 u sync_buffer.db.
        #
        # Zpracovat se smí jen prefix, který replace_chain() může přijmout;
        # rozhoduje o tom _prefix_muze_vyhrat(). duvod_stropu nese, který ze
        # dvou stropů se uplatnil, aby to šlo říct v logu.
        zpracovat_hned = False
        duvod_stropu = None
        # OPRAVA (dokončení U-19): fork_start_index se čte JEDNOU, pod fork_lock,
        # do lokální proměnné.
        #
        # Dřív se četl dvakrát bez zámku - jednou v `is not None`, podruhé
        # v int(). Mezi ty dva přístupy se vejde cizí vlákno, které pod
        # fork_lock zavolá process_sync_buffer() a příznak vynuluje; int(None)
        # pak vyhodí TypeError a ten padne rovnou do _abort_fork_sync() s
        # výchozím ban=True. Ověřeno: peer, který poslal naprosto platnou dávku,
        # dostal 24hodinový ban s nepravdivým důvodem "Dávka nemá čitelné indexy".
        # Dvě souběžná vlákna z jedné IP jsou běžný stav (MAX_INBOUND_PER_IP = 4)
        # a banovat poctivé uzly za vlastní závod je přesně failure mode, proti
        # kterému míří OPRAVY #1, N-1, P-1 i ETAPA 3.
        #
        # OPRAVA W-1 (audit 9. 10. 2026, nález N-1): čtení se přesunulo na začátek
        # metody, do téhož `with self.fork_lock`, kde se řeší fork_peer_ip -
        # potřebuje ho už branka návaznosti. Druhé čtení tady by bylo pod jiným
        # zámkem v jiném čase, tedy přesně ta dvojí hodnota, kterou U-19 scelila.
        if fork_start_snapshot is not None:
            try:
                start = int(fork_start_snapshot)
                prvni = int(blocks_data[0]['index'])
            except (TypeError, ValueError, KeyError):
                self._abort_fork_sync(addr, "Dávka nemá čitelné indexy.")
                return
            hloubka_reorgu = self.blockchain.max_block_index - start + 1
            if hloubka_reorgu > MAX_REORG_DEPTH:
                self._abort_fork_sync(
                    addr,
                    f"Fork od #{start} by vyžadoval reorg hloubky {hloubka_reorgu} > MAX_REORG_DEPTH ({MAX_REORG_DEPTH}). Žádný postih.",
                    ban=False)
                return
            volno = (MAX_REORG_DEPTH + 1) - (prvni - start)
            if volno < len(blocks_data):
                blocks_data = blocks_data[:max(0, volno)]
                zpracovat_hned = True
                duvod_stropu = f"hloubkový strop MAX_REORG_DEPTH = {MAX_REORG_DEPTH}"
                if not blocks_data:
                    # OPRAVA AUDIT-2026-1 (nález 1): do bufferu se už nevejde ani
                    # jeden blok dávky, takže tohle je definitivní podoba prefixu.
                    # Posílat ho do replace_chain() bez ověření znamenalo
                    # zaručené odmítnutí, smazání bufferu a další kolo za 10 s.
                    if self._prefix_muze_vyhrat(start):
                        self.process_sync_buffer()
                    else:
                        self._prefix_neprebiji(start, duvod_stropu)
                    return
                last_block_data = blocks_data[-1]

        # OPRAVA A-3 (bajtový strop): drží i tam, kde hloubku spočítat neumíme
        # (fork_start_index není znám), a chrání flash i při plných blocích.
        # Serializace se dělá jednou a použije se pro účtování i pro zápis.
        # OPRAVA T-1 (Nález 1, 2/2): účtuje se CELÝ řádek, který se zapíše, ne
        # jen tx_json. Dřív se sem započítal jen sloupec transactions, takže
        # blok s prázdným seznamem transakcí a 500 kB ve state_root stál podle
        # účetnictví 12 bajtů a strop se neuplatnil vůbec.
        pripravene = []
        davka_bajtu = 0
        for bd in blocks_data:
            tx_json = json.dumps(bd['transactions'])
            radek_bajtu = sync_row_bytes(self._sync_row_values(bd, tx_json))
            davka_bajtu += radek_bajtu
            pripravene.append((bd, tx_json, radek_bajtu))

        buffer_bajtu = getattr(self, 'sync_buffer_bytes', 0)
        if buffer_bajtu + davka_bajtu > MAX_SYNC_BUFFER_BYTES:
            # OPRAVA N-1: plný bajtový strop NENÍ vina protistrany - 63 plných
            # poctivých bloků ho naplní taky. Místo banu se vezme jen tolik
            # bloků, kolik se vejde, a zpracuje se, co v bufferu je.
            vejde_se = []
            vejde_se_bajtu = 0
            for bd, tx_json, radek_bajtu in pripravene:
                if buffer_bajtu + vejde_se_bajtu + radek_bajtu > MAX_SYNC_BUFFER_BYTES:
                    break
                vejde_se.append((bd, tx_json, radek_bajtu))
                vejde_se_bajtu += radek_bajtu
            if not vejde_se:
                if self.sync_buffer_tip() is not None:
                    # OPRAVA AUDIT-2026-1 (nález 1): viz tatáž dvojice o kus výš
                    # u hloubkového stropu. Tohle je ta cesta, kterou nález
                    # naměřil: ~63 MiB staženo a zahozeno každých 10 s.
                    if self._prefix_muze_vyhrat(fork_start_snapshot):
                        self.process_sync_buffer()
                    else:
                        self._prefix_neprebiji(
                            fork_start_snapshot,
                            f"bajtový strop MAX_SYNC_BUFFER_BYTES = {MAX_SYNC_BUFFER_BYTES // (1024 * 1024)} MiB")
                else:
                    self._abort_fork_sync(addr, "Blok forku se nevejde do MAX_SYNC_BUFFER_BYTES. Žádný postih.", ban=False)
                return
            pripravene = vejde_se
            davka_bajtu = vejde_se_bajtu
            blocks_data = [bd for bd, _, _ in vejde_se]
            last_block_data = blocks_data[-1]
            zpracovat_hned = True
            duvod_stropu = f"bajtový strop MAX_SYNC_BUFFER_BYTES = {MAX_SYNC_BUFFER_BYTES // (1024 * 1024)} MiB"

        # OPRAVA L-3: zápis dávky do bufferu je nejfrekventovanější síťová cesta
        # do SQLite v celém uzlu a spojení tu viselo bez try/finally. Výjimku
        # samotnou řeší obal _store_fork_batch() (OPRAVA A-2/D-02), ale
        # deskriptor po ní zůstával otevřený - a při opakovaných pokusech
        # o fork sync se hromadil.
        conn = None
        skutecne_bajtu = None
        try:
            conn = sqlite3.connect(self.SYNC_BUFFER_DB, timeout=1.0)
            conn.execute("PRAGMA journal_mode=WAL;")
            c = conn.cursor()
            for bd, tx_json, _ in pripravene:
                c.execute('''
                    INSERT OR REPLACE INTO sync_blocks 
                    (block_index, timestamp, transactions, previous_hash, target_hex, nonce, block_hash, merkle_root, version, chain_id, state_root)
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                ''', self._sync_row_values(bd, tx_json))
            # OPRAVA S-2 (Nález 1): zápis je INSERT OR REPLACE podle block_index,
            # takže TÁŽ dávka poslaná znovu v bufferu nic nepřidá - řádky se jen
            # přepíšou. Přičítání davka_bajtu proto účtovalo objem, který v
            # tabulce neexistuje, a po ~8 opakováních plné dávky překročilo
            # MAX_SYNC_BUFFER_BYTES: rozpracovaný hluboký reorg se zahodil,
            # a protože cesta "buffer plný" je záměrně bez banu (OPRAVA N-1),
            # útočník za to nic nezaplatil (posílal jen platné bloky, které
            # už jednou poslal).
            #
            # Skutečný obsah tabulky je jediný zdroj pravdy. Tabulka má strop
            # ~1000 řádků, takže agregace je levná a dělá se jen jednou na dávku.
            #
            # OPRAVA T-1 (Nález 1, 2/2): agregace sčítá VŠECHNY sloupce řádku.
            # Měřit jen `transactions` znamenalo měřit tu jedinou část bloku,
            # kterou útočník nepotřebuje - hlavička má v tvarové brance pouze
            # isinstance(..., str) a PoW se počítá nad hlavičkou včetně balastu,
            # takže se celá cena útoku vešla do neúčtovaného sloupce.
            c.execute(SYNC_BUFFER_BYTES_SQL)
            skutecne_bajtu = int(c.fetchone()[0] or 0)
            conn.commit()
        except Exception:
            # Buď se zapíše celá dávka, nebo nic - poloviční dávka by v bufferu
            # udělala díru, kterou process_sync_buffer() vyhodnotí jako výpadek.
            if conn is not None:
                try:
                    conn.rollback()
                except Exception:
                    pass
            raise
        finally:
            if conn is not None:
                try:
                    conn.close()
                except Exception:
                    pass
        # OPRAVA S-2 (Nález 1): naměřeno z tabulky, ne přičteno. Fallback na
        # původní výpočet je jen pro jistotu - sem se dojde pouze po úspěšném
        # commitu, takže skutecne_bajtu je vždy nastavené.
        self.sync_buffer_bytes = skutecne_bajtu if skutecne_bajtu is not None else (buffer_bajtu + davka_bajtu)

        # OPRAVA #6c: watchdog na NEČINNOST - lhůta se obnovuje při každém
        # úspěšném zápisu do bufferu, ne jen jednou na začátku stahování.
        self.fork_sync_start = time.time()
        # OPRAVA N3 (nález N3): značka stáří OBSAHU bufferu. Na rozdíl od
        # fork_sync_start ji nikdo jiný neposouvá ani nenuluje, takže podle ní
        # jde poznat rozpracovanou práci, kterou je co chránit před cizím
        # nárokem (viz _buffer_je_cerstvy()).
        self.fork_last_progress = time.time()

        self.add_log(f"{Fore.CYAN}Uloženo {len(blocks_data)} bloků do bufferu (od #{first_block_index} do #{last_block_data['index']}).{Style.RESET_ALL}")

        # OPRAVA N-1: buffer dosáhl stropu (délky ocasu nebo bajtů). Zpracuje
        # se hned - zbytek větve se po úspěšném reorgu dotáhne jako prosté
        # pokračování řetězce.
        #
        # OPRAVA AUDIT-2026-1 (nález 1): ...ale jen když ten prefix může vyhrát.
        # Práce se počítá AŽ TADY, tedy nad bufferem VČETNĚ právě zapsané dávky -
        # to je přesně obsah, který by do replace_chain() šel.
        if zpracovat_hned:
            if self._prefix_muze_vyhrat(fork_start_snapshot):
                self.process_sync_buffer()
            else:
                self._prefix_neprebiji(fork_start_snapshot, duvod_stropu or "strop sync bufferu")
            return

        # OPRAVA #21: pokračování se řídí příznakem od protistrany, ne délkou
        # dávky - ta může být kratší i kvůli bajtovému stropu.
        if has_more and driven:
            # ETAPA 1: navazující dotaz vydá řídicí smyčka sync_blocks_from_peer(),
            # ne handler - jinak by šly dva dotazy na tutéž dávku.
            return
        if has_more:
            request = {'type': 'request_blocks', 'data': {'locator_hashes': [last_block_data['hash']]}}
            # OPRAVA U-20 (nález 2): navazující žádost MUSÍ odejít tomu, kdo
            # dávku poslal. Odešla-li jinému uzlu na téže IP, stahování forku
            # se tiše zastavilo - adresát o žádném forku nic nevěděl.
            requester_addr = self.resolve_peer_addr(addr, src_node_id)
            if requester_addr:
                self.send_to_peer(requester_addr, request)
            else:
                self.add_log(f"{Fore.YELLOW}Navazující žádost o bloky zahozena: naslouchací port uzlu {ip_port} není znám.{Style.RESET_ALL}")
        else:
            self.process_sync_buffer()

    def peer_ip_known(self, addr):
        # OPRAVA U-20 (nález 2): branka důvěry z OPRAVY #10 oddělená od
        # SMĚROVÁNÍ. Obojí dřív dělala resolve_peer_addr() jedním lookupem, což
        # šlo jen díky tomu, že na jednu IP připadal právě jeden záznam.
        #
        # Jsou to ale dvě různé otázky. Branka se ptá "známe tuhle adresu?" a je
        # ze své podstaty na úrovni IP - stejně jako bany a rate limity. Směrování
        # se ptá "kam přesně mám odpovědět?" a to při dvou uzlech na jedné IP
        # jednoznačnou odpověď mít nemusí. Spojené dohromady by zpřísnění
        # směrování zavřelo branku i uzlům, které nic neprovedly.
        if not addr:
            return False
        normalized_ip = self.normalize_ip(addr[0])
        with self.peers_lock:
            return any(key[0] == normalized_ip for key in self.peer_listen_ports)

    def resolve_peer_addr(self, addr, node_id=None):
        """
        Naslouchací adresa uzlu, od kterého přišla zpráva, nebo None.

        OPRAVA U-20 (audit 7. 10. 2026, nález 2): dřív to byl lookup
        `peer_listen_ports[ip]` nad slovníkem IP -> jeden port. Druhý uzel na
        téže IP ten záznam přepsal a od té chvíle odcházely VŠECHNY odpovědi
        i žádosti nesprávnému uzlu. Naměřený následek: uzel správně pozná, že
        peer A má těžší řetězec, žádost o bloky ale pošle peerovi B - a uvízne
        na lehčí větvi natrvalo. Žádná výjimka, žádný ban, žádný varovný řádek;
        z pohledu uživatele vypadá uzel zdravě.

        Pořadí rozhodování:
          1. Je adresa sama známým naslouchacím místem? Pak je to ona.
             Tudy chodí celý řízený sync (sync_blocks_from_peer, PeerConnection) -
             tam je `addr` rovnou peer z tabulky, ne efemérní port spojení.
          2. Zná-li volající node_id odesílatele (příchozí spojení, které se
             uvedlo handshakem), rozhodne node_id.
          3. Zbývá-li na té IP jediný uzel, je to on.
          4. Víc uzlů a žádný rozlišovač: vrací se None. Mlčky hádat znamená
             poslat zprávu nesprávnému uzlu, a právě to byl nález 2.
        """
        if not addr:
            return None
        normalized_ip = self.normalize_ip(addr[0])
        with self.peers_lock:
            zaznamy = {key: port for key, port in self.peer_listen_ports.items()
                       if key[0] == normalized_ip}
            if not zaznamy:
                return None
            # 1. Adresa už naslouchacím místem je (řízený sync, perzistentní
            #    spojení). Tohle je zároveň minimální oprava, kterou ověřoval
            #    kontrolní pokus v auditu.
            if len(addr) > 1 and addr[1] in zaznamy.values():
                return (addr[0], addr[1])
            # 2. Odesílatel se uvedl node_id na tomtéž spojení.
            if node_id:
                port = zaznamy.get((normalized_ip, node_id))
                if port is not None:
                    return (addr[0], port)
            # 3. Jediný uzel na téhle IP - není co plést.
            porty = set(zaznamy.values())
            if len(porty) == 1:
                return (addr[0], porty.pop())
        # 4. Víc uzlů na jedné IP bez rozlišovače. Log mimo zámek.
        self.add_log(f"{Fore.YELLOW}Naslouchací port odesílatele z {addr[0]} nelze určit "
                     f"jednoznačně ({len(porty)} uzlů na téže IP, zpráva bez node_id). "
                     f"Žádost neodesílám, ať neskončí u nesprávného uzlu.{Style.RESET_ALL}")
        return None

    def _respond(self, request_msg, response, addr, ip_port, reply, popis, src_node_id=None,
                 uz_uctovano=0):
        """
        ETAPA 1: odpověď se posílá po TOMTÉŽ socketu, na kterém přišel dotaz,
        pokud dotaz nesl request_id. Jinak se padá na starou cestu (nové
        odchozí spojení), takže uzly bez téhle změny fungují dál a
        PROTOCOL_VERSION se zvyšovat nemusí.

        ETAPA 2: velikost odpovědi se účtuje do bajtového rozpočtu peera.

        OPRAVA AUDIT-2026-2 (audit 8. 10. 2026, nález 2): `uz_uctovano` je počet
        bajtů, které si volající z rozpočtu STRHL PŘEDEM, ještě než sáhl do
        databáze. Doúčtuje se jen rozdíl proti skutečné odpovědi.

        Důvod: rozpočet se dosud účtoval až TADY, tedy až po tom, co handler
        dávku přečetl z DB, naparsoval a znovu serializoval. Při vyčerpaném
        rozpočtu se odpověď zahodila, ale veškerá práce už proběhla - naměřeno
        79 B dotaz -> 62 ms obsluhy a 35 MiB špičky paměti, přičemž 9 z 10
        odpovědí se zahodilo AŽ PO té práci. Jediná skutečná brzda zbývala
        is_expensive_rate_limited(), která počítá DOTAZY, ne jejich cenu - a to
        je přesně ta jednotka, kterou komentář u EXPENSIVE_BYTES_* sám označuje
        za špatnou.

        OPRAVA AUDIT-2026-2 (nález 2, 2/2): rámec se serializuje JEDNOU. Dřív
        se postavil tady jen kvůli změření délky, zahodil, a reply() ho vyrobil
        znovu - u 7 MiB odpovědi 7 MiB práce navíc na každý dotaz. reply()
        i PeerConnection.send() proto přijímají i hotové bajty.
        """
        rid = request_msg.get('request_id')
        if reply is not None and rid is not None:
            response = dict(response)
            response['request_id'] = rid

        payload = self._frame(response)
        # Doúčtuje se jen to, co předběžný odhad nepokryl. Záporný rozdíl
        # (odhad byl velkorysejší než skutečnost) se do kbelíku nevrací -
        # rozpočet má škrtit práci, a tu volající odvedl podle svého odhadu.
        doplatek = max(0, len(payload) - int(uz_uctovano or 0))
        if not self.charge_expensive_bytes(addr, doplatek if addr else 0):
            self.add_log(f"{Fore.YELLOW}{popis} od {ip_port} zahozeno: vyčerpán bajtový rozpočet ({len(payload)/1024:.0f} KB).{Style.RESET_ALL}")
            return True

        if reply is not None and rid is not None:
            if reply(payload):
                self.add_log(f"{Fore.YELLOW}{popis} od {ip_port}, odpovídám po stejném spojení (request_id {rid}).{Style.RESET_ALL}")
                return True
            self.add_log(f"{Fore.YELLOW}{popis} od {ip_port}: odpověď po spojení selhala, zkouším nové spojení.{Style.RESET_ALL}")

        # OPRAVA U-20 (nález 2): náhradní cesta otevírá NOVÉ spojení, takže si
        # musí naslouchací adresu dohledat - a tam se dřív odpověď na dotaz
        # uzlu 1 odeslala uzlu 2, běžel-li na téže IP. src_node_id je identita
        # z handshaku na tomtéž spojení, tedy jediný spolehlivý rozlišovač.
        responder_addr = self.resolve_peer_addr(addr, src_node_id)
        if responder_addr:
            self.add_log(f"{Fore.YELLOW}{popis} od {ip_port}, odesílám unicastem...{Style.RESET_ALL}")
            self.send_to_peer(responder_addr, response)
            return True
        self.add_log(f"{Fore.YELLOW}{popis} od {ip_port} zahozeno: naslouchací port není znám.{Style.RESET_ALL}")
        return True

    def _je_duplicitni_transakce(self, tx):
        """OPRAVA AUDIT-2026-16 (audit 28. 10. 2026, nález 1): odliší "tuhle
        transakci UŽ MÁME" od "ta transakce je VADNÁ".

        add_transaction() vrací False pro obojí, ale pro započtení do
        MAX_UNAUTHENTICATED_MESSAGES je to rozdíl mezi poctivým sousedem a
        útočníkem - viz odůvodnění na volajícím místě.

        Volá se VÝHRADNĚ na zamítavé cestě, tedy až když add_transaction()
        vrátila False. Dotaz do DB tím padá na vzácnou cestu: u transakce, která
        se do mempoolu přijala, se nekoná vůbec.

        Při nedostupné databázi se vrací True ("považuj za duplicitu"). Je to
        záměrně shovívavá volba: neumíme-li kvůli VLASTNÍMU problému rozhodnout,
        nesmí to peera stát spojení. Táž úvaha jako u fail-safe v OPRAVĚ S-4.
        """
        if tx.tx_id in self.blockchain.mempool_by_txid:
            return True
        try:
            return self.blockchain.is_tx_id_in_chain(tx.tx_id)
        except (sqlite3.Error, MissingChainDataError, OSError):
            return True

    # OPRAVA F-06: očekávaný tvar pole 'data' podle typu zprávy. Dřív si každá
    # větev sahala na message['data'] po svém a 12 z 12 testovaných tvarů
    # vyhodilo výjimku ven z handleru (KeyError při chybějícím 'data',
    # TypeError u tuple(číslo), AttributeError u .get() nad seznamem...).
    # Výjimku chytal až obecný except v handle_client_connection(), který je
    # MIMO smyčku - první taková zpráva ukončila obsluhu celého spojení, a to
    # bez banu a bez započtení do MAX_UNAUTHENTICATED_MESSAGES.
    #
    # Hodnota None znamená "pole 'data' se v této větvi nepoužívá".
    # Typy, které tu nejsou uvedené (handshake), si tvar řeší samy.
    _DATA_SHAPE = {
        'transaction': dict,
        'response_chain_info': dict,
        'request_blocks': dict,
        'response_blocks': list,
        'response_full_chain': list,
        'new_block': dict,
        'response_mempool': list,
        'new_peer': (list, tuple),
        'request_chain_info': None,
        'request_full_chain': None,
        'request_mempool': None,
    }

    def _data_shape_ok(self, message, msg_type, ip_port):
        """Ověří přítomnost a základní tvar pole 'data'. Vrací True/False."""
        expected = self._DATA_SHAPE.get(msg_type, 'unknown')
        if expected == 'unknown' or expected is None:
            return True
        if 'data' not in message:
            self.add_log(f"{Fore.RED}Zpráva {msg_type} od {ip_port} nemá pole 'data'. Odmítnuto.{Style.RESET_ALL}")
            return False
        if not isinstance(message['data'], expected):
            self.add_log(f"{Fore.RED}Zpráva {msg_type} od {ip_port} má pole 'data' špatného typu. Odmítnuto.{Style.RESET_ALL}")
            return False
        if msg_type == 'response_mempool':
            # OPRAVA G-07: dosud se ověřovalo jen to, že 'data' je SEZNAM, ne
            # typ jeho prvků. Transaction.from_dict volá na prvku .get(), takže
            # data=[42] dalo AttributeError a data=[None] taktéž - a ta v except
            # tuple téhle funkce nebyla. Výjimka propadla až do obecného
            # except v handle_message(): zpráva sice skončila jako False, ale
            # zbytek dávky se nezpracoval a v logu to vypadalo jako neočekávaná
            # chyba, ne jako čisté odmítnutí.
            # Je to přesně ta kontrola, kterou OPRAVA D-15 zavedla v
            # Block.from_dict; tady chyběla. Ověřuje se jen TVAR, ne platnost.
            #
            # Záměrně JEN pro response_mempool: response_blocks a
            # response_full_chain si tvar prvků řeší ve vlastní větvi a za vadný
            # tvar navíc UDĚLUJÍ BAN. Odmítnutí už tady by ten ban obešlo.
            for polozka in message['data']:
                if not isinstance(polozka, dict):
                    self.add_log(
                        f"{Fore.RED}Zpráva {msg_type} od {ip_port} má v 'data' položku, "
                        f"která není objekt (je {type(polozka).__name__}). Odmítnuto.{Style.RESET_ALL}"
                    )
                    return False
        if msg_type == 'response_chain_info':
            # OPRAVA A-03: hodnoty z 'data' šly v handleru rovnou do porovnání
            # '>' a '<'. Pro None, řetězec nebo dict z toho letí TypeError,
            # který skončil až v obecném except handle_message() - tedy přesně
            # to, co kontrakt OPRAVY F-06 zakazuje ("vadná zpráva se nikdy
            # nedostane do větve, která na 'data' sáhne bez kontroly").
            # Obecný except je pojistka, ne cesta.
            #
            # Chybět pole smějí: handler je bere přes .get() s výchozí hodnotou.
            # Kontroluje se jen tvar toho, co přišlo. Horní mez netřeba - ani
            # jedna hodnota nejde do SQLite, jen se porovnává.
            d = message['data']
            for k in ('length', 'cum_work'):
                if k in d and (isinstance(d[k], bool) or not isinstance(d[k], int) or d[k] < 0):
                    self.add_log(f"{Fore.RED}Zpráva response_chain_info od {ip_port} má pole '{k}' špatného typu. Odmítnuto.{Style.RESET_ALL}")
                    return False
            if 'last_hash' in d and not isinstance(d['last_hash'], str):
                self.add_log(f"{Fore.RED}Zpráva response_chain_info od {ip_port} má pole 'last_hash' špatného typu. Odmítnuto.{Style.RESET_ALL}")
                return False
        if msg_type == 'new_peer':
            # tuple(message['data']) níž vyžaduje přesně dvojici (host, port).
            d = message['data']
            if len(d) != 2 or not isinstance(d[0], str) or isinstance(d[1], bool) or not isinstance(d[1], int):
                self.add_log(f"{Fore.RED}Zpráva new_peer od {ip_port} nemá tvar (host, port). Odmítnuto.{Style.RESET_ALL}")
                return False
            if not (0 < d[1] < 65536):
                self.add_log(f"{Fore.RED}Zpráva new_peer od {ip_port} má port mimo rozsah. Odmítnuto.{Style.RESET_ALL}")
                return False
        return True

    def handle_message(self, message, addr=None, reply=None, driven=False, src_node_id=None):
        # OPRAVA F-06: obal kolem vlastního handleru. Kontrakt téhle metody je
        # "nikdy nevyhoď ven" - jedna vadná zpráva nesmí shodit obsluhu spojení.
        # Návratová hodnota False navíc zprávu započítá do
        # MAX_UNAUTHENTICATED_MESSAGES, takže odesílatel vadných zpráv o spojení
        # po pár pokusech přijde sám, řízeně a s otiskem v logu.
        if addr:
            ip_port = f"[{addr[0]}]:{addr[1]}" if ':' in addr[0] else f"{addr[0]}:{addr[1]}"
        else:
            ip_port = "neznámý uzel"

        if not isinstance(message, dict):
            self.add_log(f"{Fore.RED}Zpráva od {ip_port} není objekt JSON. Odmítnuto.{Style.RESET_ALL}")
            return False

        try:
            return self._handle_message_inner(message, addr=addr, reply=reply, driven=driven,
                                              src_node_id=src_node_id)
        except Exception as e:
            # Sem se dostane jen tvar, na který výslovné kontroly nestačily.
            # Nechceme traceback ani ukončení spojení, jen zahodit a jít dál.
            # OPRAVA N1 (nález N1): typ i text výjimky jdou do logu zkrácené -
            # obojí nese hodnoty od protistrany (text výjimky z from_dict()
            # obsahuje syrový obsah pole, viz "Target není kanonický hex
            # řetězec: {raw_target!r}").
            self.add_log(
                f"{Fore.RED}Chyba při zpracování zprávy typu "
                f"{zkrat(message.get('type', 'neznámý'), 32)} od {ip_port}: "
                f"{type(e).__name__}: {zkrat(e)}. Zpráva zahozena.{Style.RESET_ALL}"
            )
            return False

    def _zalozit_novy_fork(self, blocks_data, first_block_index, first_block_data, addr, ip_port, src_node_id=None):
        """
        Založení NOVÉHO stahování forku. Volá se VÝHRADNĚ s drženým fork_lock
        a jen tehdy, když syncing_fork je (pod tímtéž zámkem ověřeně) False.

        Vrací True = příznaky nastaveny, dávka se má zapsat do bufferu,
        None = dávka odmítnuta (volající vrátí False),
        NotImplemented = odešel fallback na full sync, dávka se nezapisuje.

        OPRAVA U-19 (nález 1): vytaženo z handleru response_blocks, aby bylo
        vidět, kam až sahá kritická sekce a kudy se z ní dá odejít. Obsah je
        beze změny až na to, že tahle cesta už nemůže běžet dvakrát naráz.
        """
        # OPRAVA AUDIT-2026-1 (nález 1): o fork, o kterém už víme, že se do
        # rozpočtu bufferu nevejde a jeho prefix naši větev nepřebíjí, se
        # nepokoušíme znovu hned. Bez téhle branky by další kolo periodického
        # syncu (10 s) stáhlo a zahodilo celých ~63 MiB znovu, a tak pořád
        # dokola - což je přesně to chování, které nález naměřil.
        #
        # Branka je PŘED jakýmkoli zápisem i před dotazem do DB: dávka se
        # zahodí, nic se nemaže a nic nenastavuje.
        zbyva = self._fork_zbyva_backoff(first_block_index)
        if zbyva > 0:
            self.add_log(
                f"{Fore.YELLOW}Fork od #{first_block_index} od {ip_port} zatím nezkouším: "
                f"tentýž bod forku se do sync bufferu nevešel a jeho prefix naši větev "
                f"nepřebil. Zbývá {zbyva} s.{Style.RESET_ALL}")
            return None

        # OPRAVA N3 (audit 10. 10. 2026, nález N3): cooldown po vypršeném
        # watchdogu. Bez něj by útočník zabral uvolněný slot dřív, než se
        # poctivý peer stihne ozvat - stojí ho to jednu zprávu a smí jich
        # poslat 90 za sekundu.
        zbyva = self._fork_slot_na_cooldownu(addr[0] if addr else None)
        if zbyva > 0:
            self.add_log(
                f"{Fore.YELLOW}Nárok uzlu {ip_port} na fork slot zamítnut: předchozí pokus "
                f"od téhle IP vypršel bez dokončení, zbývá {zbyva} s cooldownu.{Style.RESET_ALL}")
            return None

        # OPRAVA N3 (nález N3): rozpracovaný buffer se cizím nárokem nezahazuje.
        #
        # Tady se dřív volalo discard_sync_buffer() BEZPODMÍNEČNĚ, o pár řádků
        # níž. Naměřeno: buffer s 15 poctivě staženými a ověřenými bloky zmizel
        # po jediné útočné zprávě o 878 B, a to bez banu. OPRAVA P-1 přitom
        # buffer na sousední cestě (dávka s neznámým rodičem) výslovně chrání
        # a OPRAVA H-1 totéž udělala pro prázdnou dávku - sem se ochrana
        # nepropsala.
        #
        # Pravidlo je stejné jako u převzetí slotu za běhu
        # (_lze_prevzit_fork_slot): zahodit smí jen nabídka s prokazatelně
        # větší prací. Zastaralý buffer (nikdo do něj déle než
        # FORK_SYNC_IDLE_TIMEOUT nezapsal) je opuštěná práce a chrání se dál
        # jen backoffem výš.
        if self._buffer_je_cerstvy() and not self._nabidka_prebiji_fork(blocks_data):
            tip = self.sync_buffer_tip()
            self.add_log(
                f"{Fore.YELLOW}Nárok uzlu {ip_port} na fork od #{first_block_index} zamítnut: "
                f"v bufferu leží rozpracovaný fork (do #{tip[0] if tip else '?'}) s větší nebo "
                f"shodnou prací. Buffer ponechávám, dávku zahazuji, žádný postih.{Style.RESET_ALL}")
            return None

        self.add_log(f"{Fore.YELLOW}Detekován fork (od bloku #{first_block_index}). Zahajuji ukládání do dočasného bufferu...{Style.RESET_ALL}")
        
        # OPRAVA L-3: spojení bez try/finally na cestě přímo
        # dosažitelné ze sítě. Selhání dotazu (OperationalError,
        # DatabaseError) tu nechalo deskriptor viset a výjimka
        # odešla do obecného except v handle_message(), kde se
        # z ní stalo jen "zpráva zahozena" - tedy tichý únik,
        # opakovatelný jednou zprávou na spojení.
        conn = None
        try:
            conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
            conn.execute("PRAGMA journal_mode=WAL;")
            c = conn.cursor()
            c.execute("SELECT block_hash FROM blocks WHERE block_index = ?", (first_block_index - 1,))
            row = c.fetchone()
        finally:
            if conn is not None:
                try:
                    conn.close()
                except Exception:
                    pass
        
        if (not row or row[0] != first_block_data['previous_hash']) and first_block_index != 0:
            if self.blockchain.max_block_index == 0:
                request = {'type': 'request_full_chain'}
                requester_addr = self.resolve_peer_addr(addr, src_node_id)
                if requester_addr:
                    self.add_log(f"{Fore.RED}Nedokážu navázat přijaté bloky. Fallback na full sync...{Style.RESET_ALL}")
                    # OPRAVA Y-5 (nález 5): branka se otevírá PRO KONKRÉTNÍ UZEL
                    # a na omezenou dobu, ne natrvalo a pro kohokoli. Zaznamenat
                    # se to musí PŘED odesláním, jinak by rychlá odpověď narazila
                    # na zavřenou branku - táž úvaha jako u expect_mempool_from()
                    # v sync_with_peer(). Větev bez známého portu tím odpadá: nic
                    # neodešlo, tak se ani nic neotevírá.
                    self.expect_full_chain_from(requester_addr)
                    self.send_to_peer(requester_addr, request)
                else:
                    # OPRAVA #9: bez broadcastu. (Dřív se tu navíc musel ručně
                    # zavírat příznak awaiting_full_chain, aby nezůstal viset.
                    # Po OPRAVĚ Y-5 se branka otevírá až vedle samotného
                    # odeslání, takže na téhle cestě není co uklízet.)
                    self.add_log(f"{Fore.YELLOW}Fallback na full sync zrušen: naslouchací port uzlu {ip_port} není znám.{Style.RESET_ALL}")
                # NotImplemented = fallback vyřízen, dávku do bufferu nezapisujeme.
                return NotImplemented
            else:
                # OPRAVA G-09: tady se dřív tři příznaky uklízely
                # ručně (syncing_fork, fork_start_index,
                # fork_sync_start) a ČTVRTÝ - fork_peer_ip - zůstal
                # viset. Nevolala se ani discard_sync_buffer(), takže
                # rozpracovaný buffer zůstal na disku i s napočítaným
                # sync_buffer_bytes. Úklid proto vede přes
                # _abort_fork_sync(), jediné místo, kde je kompletní.
                #
                # OPRAVA P-1: ...ale BEZ BANU a bez ničení cizí práce.
                #
                # Podmínka výše zní jen "rodiče prvního bloku dávky
                # nemám v blockchain.db". To není důkaz viny - nastane
                # to i zcela legitimně:
                #   - rodič leží v sync bufferu, ne v DB (to je základ
                #     útoku H-1),
                #   - protistrana odpověděla na locator, který jsme
                #     mezitím přerostli,
                #   - protistrana je na skutečně jiné větvi, hlubší,
                #     než kam sahá naše DB.
                # Postih přitom býval nejtvrdší, jaký kód zná: 24 hodin
                # za jedinou dávku. Ban patří k PROKAZATELNÉMU rozporu
                # (nesouvislá dávka, nesedící previous_hash uvnitř
                # dávky) - stejnou úvahu dělá process_sync_buffer(),
                # kde se díra v indexech záměrně nebanuje ("poctivý
                # uzel za výpadek sítě nemůže").
                #
                # Druhá půlka opravy: leží-li v bufferu rozpracovaný
                # fork, NESAHÁME na něj. Po FORK_SYNC_IDLE_TIMEOUT je
                # syncing_fork False a buffer čeká na _resume_fork_sync();
                # nechat libovolný uzel tenhle buffer smazat jednou
                # nenavazující dávkou je táž ztráta práce jako u H-1,
                # jen jinými dveřmi. Dávku tedy zahodíme a dál se
                # nestane nic.
                self.add_log(f"{Fore.YELLOW}Dávka od {ip_port} začíná blokem #{first_block_index}, jehož rodiče nemáme v DB. Fallback na fullsync zamítnut, dávku zahazuji.{Style.RESET_ALL}")
                if self.sync_buffer_tip() is not None:
                    self.add_log(f"{Fore.CYAN}Rozpracovaný fork buffer ponechávám (nepatří téhle dávce).{Style.RESET_ALL}")
                else:
                    self._abort_fork_sync(
                        addr,
                        "dávka nenavazuje na naši DB (neznámý rodič). Nic prokázáno není, žádný postih.",
                        ban=False)
                # None znamená "volající vrátí False", tedy dávku jsme
                # odmítli a má se započítat do MAX_UNAUTHENTICATED_MESSAGES.
                return None

        # Nový fork - buffer po případném starém pokusu zahodíme. Po OPRAVĚ N3
        # se sem dojde jen tehdy, když je buffer prázdný, zastaralý, nebo když
        # tahle dávka nese prokazatelně víc práce než jeho obsah (viz branka
        # výš) - zahodí se tedy vždycky něco, co buď nikdo nedodělává, nebo co
        # právě prohrálo na práci.
        self.discard_sync_buffer()
        self.fork_last_ok = False
        self.syncing_fork = True
        self.fork_start_index = first_block_index
        self.fork_sync_start = time.time()
        # OPRAVA N3: nový buffer je od téhle chvíle rozpracovaná práce
        # a chrání ho _buffer_je_cerstvy(). Samotný zápis dávky posune značku
        # znovu (viz _store_fork_batch_inner).
        self.fork_last_progress = time.time()
        self.fork_peer_ip = addr[0] if addr else None
        self.init_sync_buffer(reset=True)
        return True

    def _handle_message_inner(self, message, addr=None, reply=None, driven=False, src_node_id=None):
        # OPRAVA U-20 (audit 7. 10. 2026, nález 2): src_node_id je node_id,
        # kterým se odesílatel uvedl v handshaku NA TOMTÉŽ SPOJENÍ. Příchozí
        # spojení nese v addr efemérní zdrojový port, takže naslouchací adresu
        # je nutné dohledat - a běží-li na jedné IP dva uzly, je node_id jediné,
        # čím je od sebe rozeznat. Cesty, kde je addr rovnou peer z tabulky
        # (řízený sync, PeerConnection), ho nepotřebují a nechávají None.
        #
        # ETAPA 1: vrací True, pokud byla zpráva přijata ke zpracování, a False,
        # pokud ji brána odmítla. handle_client_connection() na základě toho
        # zavírá spojení uzlů, které jen spamují bez identity.
        try:
            timestamp = get_time()
            formatted_time = time.strftime('%d.%m.%Y %H:%M:%S UTC+00:00', time.gmtime(timestamp))
        except Exception:
            formatted_time = "Neznámý čas"
        if addr:
            ip_port = f"[{addr[0]}]:{addr[1]}" if ':' in addr[0] else f"{addr[0]}:{addr[1]}"
        else:
            ip_port = "neznámý uzel"
            
        msg_type = message.get('type')
        if not msg_type:
            self.add_log(f"{Fore.RED}Přijata zpráva bez udání typu od uzlu {ip_port}. Odmítnuto.{Style.RESET_ALL}")
            return False
        if not isinstance(msg_type, str):
            self.add_log(f"{Fore.RED}Přijata zpráva s nekorektním typem od uzlu {ip_port}. Odmítnuto.{Style.RESET_ALL}")
            return False

        # OPRAVA AUDIT-2026-16 (audit 28. 10. 2026, nález 3): když spojení
        # identitu nenese, zkusí se identita ze SAMOTNÉ ZPRÁVY.
        #
        # src_node_id plní jen handshake na tomtéž spojení. Přeposílání
        # (OPRAVA W-2) ale často odchází JEDNORÁZOVÝM socketem bez handshaku
        # (fallback v _send_to_single_peer, když se nedrží perzistentní
        # spojení), takže u 'new_block' i 'transaction' zůstávalo None -
        # naměřeno addr=('127.0.0.1', 34034), src_node_id=None. Při dvou uzlech
        # na jedné IP pak resolve_peer_addr() vrátí None a volající padá na
        # hrubší klíč nebo žádost vůbec neodešle.
        #
        # Stamp přidává preposli_sousedum() do odcházející zprávy. Pro uzly se
        # starším kódem se nic nemění: pole navíc ignorují (tvarová branka
        # _data_shape_ok() se dívá jen do 'data') a jeho absence vrací chování
        # přesně na stav před touto opravou, takže PROTOCOL_VERSION se nemění.
        #
        # Podvržení cizího node_id nedává nic navíc: resolve_peer_addr() hledá
        # klíč (NAŠE IP odesílatele, node_id), takže se dá jmenovat jedině uzel,
        # který už na TÉŽE IP známe - a tam dnešní kód vynechává celou IP tak
        # jako tak. Jediný možný následek je, že jeden soused přijde o jedno
        # přeposlání a dostane totéž nejbližším kolem syncu.
        if src_node_id is None:
            nid_ze_zpravy = message.get('node_id')
            # Táž kontrola typu i délky jako u handshaku (OPRAVA N6): hodnota
            # se stává částí KLÍČE do peer_listen_ports.
            if isinstance(nid_ze_zpravy, str) and 0 < len(nid_ze_zpravy) <= MAX_NODE_ID_LEN:
                src_node_id = nid_ze_zpravy
        # OPRAVA N1 (audit 10. 10. 2026, nález N1): délková mez na 'type'.
        #
        # Kontrolovalo se jen isinstance(..., str), a msg_type se pak
        # interpoluje do nejméně tří hlášek - včetně té o pár řádků níž, která
        # se zapíše ZPRÁVĚ, KTEROU UZEL ODMÍTL. Útok je tedy jediná zpráva
        # s dlouhým 'type', bez PoW a bez platných dat. Mez je tady, dřív než
        # se typ dostane do logu i do tvarové branky _data_shape_ok().
        #
        # Žádný legitimní typ se tím neomezuje - nejdelší, který uzel posílá,
        # je 'response_full_chain' (20 znaků).
        if len(msg_type) > MAX_MSG_TYPE_LEN:
            self.add_log(
                f"{Fore.RED}Zpráva od {ip_port} má typ delší než {MAX_MSG_TYPE_LEN} znaků "
                f"({len(msg_type)}): {zkrat(msg_type, 32)}. Odmítnuto.{Style.RESET_ALL}")
            return False

        # OPRAVA Y-3 (audit 14. 10. 2026, nález 3): typ a rozsah 'request_id'.
        #
        # _respond() vkládá request_id z příchozí zprávy ZPĚT do odpovědi, ať
        # je to cokoli - echem prošel int, str, list, dict, bool i float a
        # délku neomezovalo nic. request_id o 10 MiB tedy vyrobil odpověď
        # o 10 MiB a zvedl špičku RSS o 31 až 60 MB, přičemž rate limiter
        # odebral jeden token za ZPRÁVU bez ohledu na velikost odpovědi - táž
        # chybná jednotka, kterou pojmenovává komentář u EXPENSIVE_BYTES_*.
        #
        # Vlastní request_id vydává next_request_id(), tedy celé číslo, a
        # párovací strana v PeerConnection._read_loop() přijímá VÝHRADNĚ
        # `isinstance(rid, int) and not isinstance(rid, bool)`. Echo jiného
        # typu je pro protistranu bezcenné - jen nás stojí paměť a pásmo.
        # Podmínka je proto schválně TÁŽ jako tam (OPRAVA S-7); obě strany mají
        # o témže poli říkat totéž, stejně jako to OPRAVY N-5, U-7 a U-8
        # srovnaly u polí bloku.
        #
        # Horní mez je stejná jako u ostatních celočíselných polí ze sítě
        # (A-05, U-2). S ní je odpověď shora omezená konstrukcí, takže mizí
        # i druhá polovina nálezu - serializace odpovědi, kterou rozpočet
        # vzápětí zahodí. Tu OPRAVA AUDIT-2026-2 odstranila u request_blocks,
        # request_full_chain a request_mempool zavedením uctuj_predem();
        # request_chain_info ho nepotřebuje, protože jeho odpověď je i s
        # request_id v řádu stovek bajtů.
        if 'request_id' in message:
            rid = message['request_id']
            if (isinstance(rid, bool) or not isinstance(rid, int)
                    or not (0 <= rid <= (1 << 63) - 1)):
                self.add_log(
                    f"{Fore.RED}Zpráva {zkrat(msg_type, 32)} od {ip_port} má neplatné "
                    f"'request_id' ({type(rid).__name__}). Odmítnuto.{Style.RESET_ALL}")
                return False

        # OPRAVA F-06: tvar pole 'data' se ověřuje centrálně a JEŠTĚ PŘED
        # branami níž, takže se vadná zpráva nikdy nedostane do větve, která na
        # 'data' sáhne bez kontroly. Odmítnutí zde nemění žádný stav uzlu,
        # není tedy co uklízet (týž vzorec jako OPRAVA D-02 u response_blocks).
        if not self._data_shape_ok(message, msg_type, ip_port):
            return False

        # OPRAVA #10: handle_message dřív reagovala na response_blocks,
        # response_chain_info, new_block, transaction i new_peer od LIBOVOLNÉ IP.
        # Jediný chráněný typ byl response_full_chain (přes awaiting_full_chain).
        # Útočník tak mohl jedním paketem nastavit syncing_fork = True a na 30 s
        # zablokovat legitimní synchronizaci - a opakovat to donekonečna.
        #
        # Nově se cokoli kromě handshaku přijímá jen od uzlu, kterého známe:
        # nakonfigurovaný peer, uzel, ke kterému jsme se sami připojili, nebo
        # uzel, který u nás dokončil handshake. Přesně to vyjadřuje
        # resolve_peer_addr() != None, protože všechny tři cesty plní
        # peer_listen_ports. Handshake sám je z pravidla vyňatý, jinak by se
        # nikdo nemohl představit.
        #
        # OPRAVA U-20 (nález 2): ptáme se peer_ip_known(), ne resolve_peer_addr().
        # Jsou to dvě různé otázky (viz komentář u obou metod) a od chvíle, kdy
        # směrování při dvou uzlech na jedné IP poctivě přizná "nevím kam", by
        # sloučená podmínka zavřela branku i uzlům, které nic neprovedly.
        # Rozsah branky se tím nemění: evidence byla dosud klíčovaná IP, takže
        # "je v ní záznam pro tuhle IP" je přesně původní podmínka.
        if msg_type != 'handshake' and not self.peer_ip_known(addr):
            self.add_log(f"{Fore.YELLOW}Zpráva typu {msg_type} od neznámého uzlu {ip_port} odmítnuta (chybí handshake).{Style.RESET_ALL}")
            return False

        # OPRAVA #1 + #9: drahé dotazy mají vlastní, mnohem přísnější rozpočet.
        #
        # OPRAVA N2 (audit 10. 10. 2026, nález N2): mezi ně patří i 'new_block'.
        # Od plné validace ji dělí jen add_block(), přitom platil jediný strop
        # RATE_LIMIT_REFILL_PER_SECOND = 90 zpráv/s na IP, a bajtový rozpočet
        # (2 MiB/s) při 870 B na zprávu nic neomezil.
        #
        # Poctivý provoz se tím neomezuje ani náhodou: kbelík je PER IP, takže
        # každý soused má vlastních EXPENSIVE_BUCKET_CAPACITY = 40 tokenů
        # s obnovou 4/s, zatímco blok vzniká jednou za BLOCK_TIME_SECONDS.
        # I po přeposílání (OPRAVA W-2) od jednoho souseda přijde jeden blok za
        # kolo. Zahozená zpráva navíc neznamená ztracený blok - periodický sync
        # ho dotáhne do 10 s.
        # OPRAVA AUDIT-2026-15 (audit 27. 10. 2026, nález 1): do rozpočtu
        # přibyla 'response_chain_info', ale JEN jako nevyžádaná.
        #
        # Byla to jediná zpráva bez branky očekávání (response_mempool má
        # consume_mempool_expectation(), response_full_chain
        # consume_full_chain_expectation(), response_blocks automat forku) a
        # zároveň jediná, která v tomhle seznamu chyběla - přitom každá vyvolá
        # get_locator_hashes() (čtení z DB) a odchozí spojení, tedy slot
        # v GLOBÁLNÍM semaforu MAX_OUTBOUND_SEND_THREADS.
        #
        # Vyjímka pro driven je nutná, ne kosmetická: driven=True nastavuje
        # VÝHRADNĚ náš vlastní kód (_sync_with_peer_inner / sync_blocks_from_peer)
        # pro odpověď, která přišla na socketu, jejž jsme sami otevřeli na svůj
        # vlastní dotaz. Útočník si ten příznak nastavit nemůže. Kdyby pod limit
        # spadla i vyžádaná odpověď, omezil by se počáteční sync - periodické
        # kolo se ptá každých 10 s, kdežto ostatní zprávy v seznamu jsou
        # příchozí DOTAZY, které nikdy nechodí s driven=True, takže se pro ně
        # nic nemění.
        if msg_type in ('request_blocks', 'request_full_chain', 'request_mempool',
                        'request_chain_info', 'new_block') or (
                            msg_type == 'response_chain_info' and not driven):
            if self.is_expensive_rate_limited(addr):
                self.add_log(f"{Fore.YELLOW}Dotaz {msg_type} od {ip_port} zahozen: vyčerpán limit drahých dotazů.{Style.RESET_ALL}")
                return True

        self.add_log(f"\n{Fore.CYAN}Přijata zpráva typu: {msg_type} od uzlu {ip_port} Čas {formatted_time}{Style.RESET_ALL}")
        
        if msg_type == 'transaction':
            # OPRAVA W-3 (audit 9. 10. 2026, nález N-3): zahodit zprávu, ne
            # zabanovat peera. Celé odůvodnění je u konstant TX_RATE_*.
            # Kanonický klíč a sledování dlouhodobého překračování řeší
            # is_tx_rate_limited(), stejně jako u ostatních limiterů.
            if self.is_tx_rate_limited(addr):
                self.add_log(f"{Fore.YELLOW}Transakce od {ip_port} zahozena: vyčerpán limit transakcí.{Style.RESET_ALL}")
                # OPRAVA B-4: tahle cesta (a dalších devět odmítavých cest
                # v tomhle handleru) vracela bare `return`, tedy None.
                # handle_client_connection() testuje `if accepted is False`,
                # takže None čítač MAX_UNAUTHENTICATED_MESSAGES NEVYNULOVAL -
                # on ho rovnou resetoval větví `else`. Uzel, který posílá jen
                # rate-limitované nebo jinak odmítnuté zprávy, tak spojení nikdy
                # neztratil a držel nám vlákno zdarma. Odmítnutí = False.
                return False

            tx_data = message['data']
            # OPRAVA F-06: from_dict() má kontrakt "při špatných datech vyhoď
            # ValueError" a ten se tady dřív vůbec neodchytával - stačila částka
            # mimo uint64 a výjimka odešla ven z handleru.
            try:
                tx = Transaction.from_dict(tx_data)
            except ValueError as e:
                self.add_log(f"{Fore.RED}Neplatná transakce od {ip_port}: {zkrat(e)}{Style.RESET_ALL}")
                return False
            if self.blockchain.add_transaction(tx):
                self.add_log(f"{Fore.GREEN}Přijata a ověřena nová transakce.{Style.RESET_ALL}")
                save_mempool(self.blockchain.unconfirmed_transactions)
                # OPRAVA W-2 (audit 9. 10. 2026, nález N-2): přeposlat dál.
                # Bez tohohle řádku se transakce dostala jen k přímým sousedům
                # svého původce (<= MAX_PEERS) a dál jedině syncem mempoolu,
                # který ale posílá pořád tutéž nejdražší pětistovku (nález N-2b).
                # Transakce s minimálním poplatkem z okrajového uzlu se tak
                # k těžaři nemusela dostat vůbec a po MEMPOOL_TX_EXPIRATION
                # vypršela, aniž by uživatel měl jak zjistit proč.
                #
                # Posílá se tx.to_dict(), ne přijatý tx_data: to_dict() je
                # kanonický tvar, takže se nešíří případné odchylky vstupu.
                if self.preposli_sousedum({'type': 'transaction', 'data': tx.to_dict()},
                                          ('tx', tx.tx_id), addr, src_node_id=src_node_id):
                    self.add_log(f"{Fore.CYAN}Transakce {tx.tx_id} přeposlána ostatním uzlům.{Style.RESET_ALL}")
            else:
                # OPRAVA AUDIT-2026-16 (audit 28. 10. 2026, nález 1): duplicita
                # se NEZAPOČÍTÁVÁ do MAX_UNAUTHENTICATED_MESSAGES.
                #
                # OPRAVA AUDIT-2026-15 sem správně doplnila `return False` za
                # VADNOU transakci, ale `add_transaction()` vrací False i za
                # transakci, kterou UŽ MÁME - a to je v lavinovém šíření
                # (OPRAVA W-2) úplně běžný stav, ne útok. preposli_sousedum()
                # posílá všem sousedům kromě přímého odesílatele, takže
                # v jakékoli topologii s cyklem dostane uzel tutéž transakci
                # dvakrát ZARUČENĚ: v trojúhelníku A-B-C ji C dostane od A i od
                # B, oba poctiví.
                #
                # Pět takových duplicit za sebou na jednom spojení znamenalo
                # MAX_UNAUTHENTICATED_MESSAGES a zavření spojení poctivému
                # sousedovi (naměřeno: 8 duplicit na živých třech uzlech = 1
                # reálně zavřené TCP spojení). A protože relay i synchronizační
                # dotazy jedou po TOMTÉŽ PeerConnection, zavření vzalo s sebou
                # i rozpracované dotazy - send_request() vrátí None a probíhající
                # kolo sync_blocks_from_peer() skončí "přerušen (bez odpovědi)".
                # Uzel dohánějící řetězec si tak běžný provoz transakcí
                # opakovaně shazoval stahování.
                #
                # Replay téže transakce donekonečna zdarma není: na tenhle typ
                # sedí vlastní rychlostní limit is_tx_rate_limited() z OPRAVY
                # W-3, který zprávu zahodí ještě dřív, než se sem dojde.
                if self._je_duplicitni_transakce(tx):
                    self.add_log(f"{Fore.YELLOW}Transakce {tx.tx_id} už ji máme (duplicita z přeposílání), zahozena.{Style.RESET_ALL}")
                    return True

                self.add_log(f"{Fore.RED}Přijatá transakce je neplatná, odmítnuta.{Style.RESET_ALL}")
                # OPRAVA AUDIT-2026-15 (audit 27. 10. 2026, nález 4): tahle
                # cesta OPRAVĚ B-4 unikla. Je to přitom ta nejdostupnější ze
                # všech odmítavých cest: transakce s rozbitým podpisem projde
                # from_dict() (podpis do tx_id nevstupuje) a padne teprve na
                # add_transaction(), takže se sem dá dojít libovolně dlouho
                # (naměřeno: návrat None, tedy `započte se: False`).
                #
                # Čítač se větví `else` výše dokonce VYNULOVAL, takže peer, který
                # posílá výhradně neplatné transakce, držel vlákno zdarma a
                # MAX_UNAUTHENTICATED_MESSAGES na něj nedosáhl vůbec. Vlastní
                # rychlostní limit (is_tx_rate_limited) škodu omezuje, ale
                # mechanismus nedělal to, co podle komentáře u B-4 dělat má.
                return False

        elif msg_type == 'request_chain_info':
            local_length = self.blockchain.max_block_index + 1
            local_last_hash = self.blockchain.get_last_block().hash
            local_cum_work = self.blockchain.get_cumulative_work()
            response = {'type': 'response_chain_info', 'data': {'length': local_length, 'last_hash': local_last_hash, 'cum_work': local_cum_work}}
            # OPRAVA #9: broadcastový fallback zrušen. Když resolve_peer_addr()
            # vrátí None, jeden paket od neznámé IP vyrobil N odpovědí ven -
            # čistá amplifikace. Po opravě #10 se sem navíc neznámý uzel vůbec
            # nedostane, takže je tahle větev už jen pojistka.
            self._respond(message, response, addr, ip_port, reply, "Požadavek na info o řetězci", src_node_id)
                
        elif msg_type == 'response_chain_info':
            data = message['data']
            remote_length = data.get('length', 0)
            remote_last_hash = data.get('last_hash', "")
            remote_cum_work = data.get('cum_work', 0)
            
            local_length = self.blockchain.max_block_index + 1
            local_last_hash = self.blockchain.get_last_block().hash
            local_cum_work = self.blockchain.get_cumulative_work()
            
            def request_blocks_from_sender():
                requester_addr = self.resolve_peer_addr(addr, src_node_id)
                if not requester_addr:
                    # OPRAVA #9: žádný broadcast. Periodický sync stejně za 10 s
                    # rozešle request_chain_info všem známým peerům.
                    self.add_log(f"{Fore.YELLOW}Naslouchací port uzlu {ip_port} není znám, žádost o bloky zahozena.{Style.RESET_ALL}")
                    return
                if driven:
                    # ETAPA 1: jsme uvnitř vlákna řízeného syncu, takže bloky
                    # stáhneme v request/response smyčce s pevným párováním
                    # odpovědí místo řetězu nevyžádaných zpráv.
                    self.sync_blocks_from_peer(requester_addr)
                else:
                    # OPRAVA AUDIT-2026-15 (nález 1), druhá polovina: tahle
                    # větev je NEVYŽÁDANÁ cesta - zprávu nikdo nežádal, a přesto
                    # z ní vycházelo čtení z DB (get_locator_hashes) a odchozí
                    # spojení držící slot globálního semaforu ~10 s.
                    #
                    # Naměřený dopad před opravou: 60 zpráv po 199 B (11 940 B
                    # celkem, bez PoW a bez zůstatku) z JEDNÉ IP, jejíž
                    # deklarovaný naslouchací port zahazuje SYN, obsadilo
                    # všech 32/32 slotů - a uzel pak nepřeposlal ani vlastní
                    # vytěžený blok, ani transakci ("blok doručen poctivému
                    # peerovi: False"). Sám se dál synchronizoval, protože pull
                    # jde přes get_connection, takže se navenek tvářil zdravě.
                    #
                    # Rozpočet drahých dotazů výše sám nestačí: při 4 dotazech/s
                    # a desetisekundové držbě slotu vychází 40 souběžných slotů,
                    # tedy pořád víc než 32. Druhá branka je proto jednorázová
                    # v okně CHAIN_INFO_REQUEST_COOLDOWN na IP - táž, kterou
                    # OPRAVA N2 zavřela tutéž páku u 'new_block'. Jedna IP tak
                    # drží nejvýš jeden slot a periodický sync se ptá sám.
                    if not self._muze_zadat_chain_info(addr):
                        self.add_log(f"{Fore.YELLOW}Nevyžádaná informace o řetězci od {ip_port}: "
                                     f"bloky jsem si od téhle IP vyžádal za poslední "
                                     f"{int(CHAIN_INFO_REQUEST_COOLDOWN)} s, dotaz neopakuji.{Style.RESET_ALL}")
                        return
                    request = {'type': 'request_blocks', 'data': {'locator_hashes': self.get_locator_hashes()}}
                    self.send_to_peer(requester_addr, request)

            if remote_cum_work > local_cum_work:
                self.add_log(f"{Fore.YELLOW}Detekován řetězec s větší prací. Žádám o bloky přes inkrementální sync...{Style.RESET_ALL}")
                request_blocks_from_sender()
            elif remote_cum_work == local_cum_work:
                if remote_length > local_length:
                    self.add_log(f"{Fore.YELLOW}Stejná práce, ale delší řetězec. Žádám o bloky přes inkrementální sync...{Style.RESET_ALL}")
                    request_blocks_from_sender()
                elif remote_length == local_length:
                    if remote_last_hash < local_last_hash:
                        self.add_log(f"{Fore.YELLOW}Stejná práce i délka, ale lepší hash (tie-breaker). Žádám o bloky přes inkrementální sync...{Style.RESET_ALL}")
                        request_blocks_from_sender()
                    else:
                        self.add_log(f"{Fore.GREEN}Řetězce synchronizovány (stejná práce i délka, náš hash je lepší nebo stejný).{Style.RESET_ALL}")
                else:
                    self.add_log(f"{Fore.GREEN}Náš řetězec má stejnou práci, ale je delší (nebo jsme synchronizováni).{Style.RESET_ALL}")
            else:
                self.add_log(f"{Fore.GREEN}Náš řetězec má větší práci. Ignoruji vzdálený.{Style.RESET_ALL}")
                
        elif msg_type == 'request_blocks':
            locator_hashes = message['data'].get('locator_hashes', [])
            # OPRAVA #9: tvrdý strop na délku locatoru. Bez něj útočník poslal
            # statisíce hashů a uzel na každý pustil SQL dotaz.
            if not isinstance(locator_hashes, list):
                locator_hashes = []
            elif len(locator_hashes) > MAX_LOCATOR_HASHES:
                self.add_log(f"{Fore.YELLOW}Locator od {ip_port} má {len(locator_hashes)} hashů, zkracuji na {MAX_LOCATOR_HASHES}.{Style.RESET_ALL}")
                locator_hashes = locator_hashes[:MAX_LOCATOR_HASHES]
            # OPRAVA G-08: typ PRVKŮ locatoru se dosud nekontroloval vůbec -
            # šly rovnou jako parametr do SQLite. SQL injection to není (dotaz
            # je parametrizovaný), ale locator_hashes=[{'a': 1}] vyhodilo
            # sqlite3.ProgrammingError: Error binding parameter 1: type 'dict'
            # is not supported, a ta přeskočila conn.close() na konci větve.
            # Spojení se pak uzavřelo až při garbage collection - spoléhání na
            # implementační detail CPythonu v cestě dosažitelné ze sítě.
            # Prvek, který nemá tvar hashe, v DB stejně nic najít nemůže,
            # takže se tiše zahodí.
            locator_hashes = [h for h in locator_hashes
                              if isinstance(h, str) and len(h) == 64]
            start_index = message['data'].get('start_index', 0)
            # isinstance(True, int) je True, takže bool vylučujeme zvlášť -
            # stejný důvod jako u _check_uint v Transaction.from_dict.
            # OPRAVA A-04: chyběla HORNÍ mez. Hodnota nad 2**63-1 doletěla až do
            # SELECTu níž a SQLite ji odmítlo OverflowErrorem ("Python int too
            # large to convert to SQLite INTEGER"). Spojení se díky finally
            # z OPRAVY G-08 zavřelo, ale odpověď neodešla a odesílatel nedostal
            # ani ban. Pro srovnání: _check_uint() v Transaction.from_dict()
            # vynucuje obě meze.
            if (isinstance(start_index, bool) or not isinstance(start_index, int)
                    or start_index < 0 or start_index > (1 << 63) - 1):
                start_index = 0
            # OPRAVA S-7: sqlite3.connect() leželo MIMO try, takže "database is
            # locked" proletělo do obecného except v handle_message() - táž
            # třída jako Nález 2, jen bez následku (žadatel si dotaz zopakuje).
            # Síťová cesta ale nemá házet výjimky kvůli stavu našeho disku.
            conn = None
            try:
                conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
                conn.execute("PRAGMA journal_mode=WAL;")
                c = conn.cursor()
            
                if locator_hashes:
                    for h in locator_hashes:
                        c.execute("SELECT block_index FROM blocks WHERE block_hash = ?", (h,))
                        row = c.fetchone()
                        if row:
                            start_index = row[0] + 1
                            break

                # OPRAVA AUDIT-2026-2 (nález 2): bajtový rozpočet se strhne TADY,
                # z levné agregace, ne až z hotové odpovědi. Dotaz čte jediný
                # sloupec a nic neparsuje, takže stojí zlomek toho, co SELECT
                # níž - a při vyčerpaném rozpočtu se ten SELECT vůbec nespustí.
                #
                # LENGTH(CAST(... AS BLOB)) měří BAJTY kódování UTF-8, ne znaky;
                # LENGTH() nad TEXTem by vrátil počet znaků a jeden vícebajtový
                # znak by útočníkovi dal páku na skutečný objem. Je to tatáž
                # úvaha jako u SYNC_BUFFER_BYTES_SQL.
                #
                # +512 B na blok je táž rezerva na hlavičku, s jakou počítá
                # odhad row_bytes níž; strop MAX_BATCH_BYTES je tentýž, kterým
                # se dávka vzápětí ořízne, takže odhad nikdy nepřestřelí
                # skutečnou odpověď o víc než o tu rezervu.
                c.execute(
                    "SELECT COUNT(*), COALESCE(SUM(LENGTH(CAST(transactions AS BLOB))), 0) FROM "
                    "(SELECT transactions FROM blocks WHERE block_index >= ? ORDER BY block_index LIMIT ?)",
                    (start_index, SYNC_BATCH_SIZE))
                odhad_radku = c.fetchone() or (0, 0)
                odhad_bajtu = min(MAX_BATCH_BYTES,
                                  int(odhad_radku[1] or 0) + int(odhad_radku[0] or 0) * 512) + 512
                uctovano = self.uctuj_predem(addr, odhad_bajtu, ip_port, "Požadavek na bloky")
                if uctovano is None:
                    return True

                # OPRAVA #21: +1 řádek navíc, abychom poznali, že další bloky existují,
                # aniž bychom je posílali.
                c.execute("SELECT block_index, timestamp, transactions, previous_hash, target_hex, nonce, block_hash, merkle_root, version, chain_id, state_root FROM blocks WHERE block_index >= ? ORDER BY block_index LIMIT ?", (start_index, SYNC_BATCH_SIZE + 1))
                # OPRAVA: kurzor se STREAMUJE, nematerializuje. fetchall() natáhl do
                # paměti všech SYNC_BATCH_SIZE+1 řádků (101 x MAX_BLOCK_SIZE_BYTES,
                # tedy ~105 MiB) JEŠTĚ PŘED tím, než MAX_BATCH_BYTES odpověď ořízne
                # na 8 MiB - naměřeno 118,6 MiB špičky proti 15,8 MiB při streamování.
                # Sesterský handler request_full_chain nad týmž dotazem streamuje
                # ('for row in c'), takže tohle byl rozpor mezi dvěma cestami, které
                # dělají totéž. Předčasný break nechá kurzor nedočerpaný; spojení
                # zavírá finally, stejně jako u request_full_chain.
                blocks_data = []
                batch_bytes = 0
                has_more = False
                for i, row in enumerate(c):
                    if i >= SYNC_BATCH_SIZE:
                        has_more = True
                        break
                    # Odhad velikosti na drátě: transakce jsou zdaleka největší část,
                    # zbytek hlavičky je pár set bajtů. Přesnost tu není potřeba,
                    # jde o strop s rezervou.
                    row_bytes = len(row[2]) + 512
                    if blocks_data and batch_bytes + row_bytes > MAX_BATCH_BYTES:
                        # Aspoň jeden blok pošleme vždy, jinak by se sync zasekl.
                        has_more = True
                        break
                    batch_bytes += row_bytes
                    blocks_data.append({
                        'index': row[0],
                        'timestamp': row[1],
                        'transactions': json.loads(row[2]),
                        'previous_hash': row[3],
                        'target': row[4],
                        'nonce': row[5],
                        'hash': row[6],
                        'merkle_root': row[7],
                        'version': row[8],
                        'chain_id': row[9], 'state_root': row[10]
                    })
            except sqlite3.Error as e:
                # OPRAVA S-7: dotaz se prostě nezodpoví. Žadatel si ho zopakuje
                # a postih nikdo nedostane - na vině je náš disk, ne protistrana.
                self.add_log(f"{Fore.YELLOW}Požadavek na bloky od {ip_port} nelze obsloužit "
                             f"({type(e).__name__}: {e}).{Style.RESET_ALL}")
                return False
            finally:
                # OPRAVA G-08: spojení se zavře i při výjimce.
                if conn is not None:
                    try:
                        conn.close()
                    except sqlite3.Error:
                        pass
            
            # OPRAVA #21: 'has_more' je nutné, protože s bajtovým stropem už
            # kratší dávka neznamená "konec řetězce". Bez toho by si příjemce
            # myslel, že je hotovo, a předčasně by spustil process_sync_buffer().
            response = {'type': 'response_blocks', 'data': blocks_data, 'has_more': has_more}
            self._respond(message, response, addr, ip_port, reply,
                          f"Požadavek na bloky ({len(blocks_data)} od #{start_index}, {batch_bytes / 1024:.0f} KB, další: {'ano' if has_more else 'ne'})",
                          src_node_id, uz_uctovano=uctovano)
                
        elif msg_type == 'response_blocks':
            blocks_data = message['data']

            # OPRAVA D-02: tvar dávky se ověřuje ÚPLNĚ NA ZAČÁTKU, tedy ještě
            # než se sáhne na syncing_fork, fork_start_index nebo buffer. Dřív
            # se surové dicty dostaly až do _store_fork_batch a tam do
            # int(bd['hash'], 16); ValueError/KeyError pak proletěl kolem
            # _abort_fork_sync() a nechal syncing_fork viset natrvalo.
            # Odmítnutí ZDE nechává stav netknutý, takže není co uklízet.
            if not isinstance(blocks_data, list):
                self.add_log(f"{Fore.RED}Dávka od {ip_port} není seznam bloků, zahazuji.{Style.RESET_ALL}")
                if addr:
                    self.ban_peer(addr[0], "response_blocks se špatným tvarem dat", BAN_DURATION_PROTOCOL)
                return False
            for bd in blocks_data:
                if not self._valid_block_dict(bd):
                    self.add_log(f"{Fore.RED}Dávka od {ip_port} obsahuje blok se špatným tvarem, zahazuji.{Style.RESET_ALL}")
                    if addr:
                        self.ban_peer(addr[0], "blok se špatným tvarem v response_blocks", BAN_DURATION_PROTOCOL)
                    return False

            # OPRAVA #21: příznak od protistrany je autoritativní. Uzel bez téhle
            # opravy ho neposílá, takže padáme zpět na původní test délky dávky.
            batch_has_more = message.get('has_more')
            if not isinstance(batch_has_more, bool):
                batch_has_more = (len(blocks_data) == SYNC_BATCH_SIZE)
            
            if not blocks_data:
                if getattr(self, 'syncing_fork', False):
                    # OPRAVA H-1: tahle větev běžela DŘÍV, než se kdokoli podíval
                    # na fork_peer_ip, takže obcházela pravidlo ETAPY 3 ("fork se
                    # stahuje od jednoho uzlu, dávky od ostatních se ignorují"),
                    # které se vynucuje až v _store_fork_batch_inner().
                    #
                    # Cena útoku byly dvě zprávy: handshake (bez PoW, z libovolné
                    # IP) a 39bajtová {"type":"response_blocks","data":[]}.
                    # Následek: process_sync_buffer() doběhl nad NEÚPLNÝM bufferem,
                    # replace_chain() ho odmítl (ještě nemá převahu) a
                    # discard_sync_buffer() ho smazal - u hlubokého reorgu se tím
                    # zahodí stovky stažených bloků. Horší je druhý krok: navazující
                    # dávka od POCTIVÉHO zdroje, která už byla na drátě, dorazí do
                    # uzlu bez bufferu i bez fork_start_index, takže resuming je
                    # False, kontrola rodiče v blockchain.db selže (rodič ležel jen
                    # v bufferu) a spustí se větev "long-range útok" s banem na 24 h.
                    # Uzel si tak jeden po druhém zabanuje vlastní synchronizační
                    # zdroje - tedy eclipse, přesně failure mode, proti kterému míří
                    # OPRAVA #1, ETAPA 3 i D-17.
                    #
                    # Prázdná dávka je legitimní signál "nic dalšího nemám", ale
                    # jen od toho, kdo fork dodává. Od kohokoli jiného se ignoruje.
                    peer_ip = addr[0] if addr else None
                    if self.fork_peer_ip is not None and peer_ip != self.fork_peer_ip:
                        self.add_log(f"{Fore.YELLOW}Prázdná dávka od {ip_port} ignorována: "
                                     f"fork se stahuje z {self.fork_peer_ip}.{Style.RESET_ALL}")
                        # False, ne None: odmítnutá zpráva se MÁ započítat do
                        # MAX_UNAUTHENTICATED_MESSAGES. Původní holé `return`
                        # vracelo None, takže handle_client_connection() čítač
                        # vynuloval a útok šel opakovat donekonečna po jednom spojení.
                        return False
                    self.process_sync_buffer()
                return
                
            self.add_log(f"{Fore.YELLOW}Přijaty bloky ({len(blocks_data)}), zpracovávám...{Style.RESET_ALL}")

            # OPRAVA #22: dávka se nejdřív očistí o bloky, které UŽ MÁME.
            #
            # Bez toho vzniká FALEŠNÝ FORK v závodu dvou cest, kterými k nám
            # tentýž blok dorazí - push (new_block) a pull (request_blocks):
            #
            #   1. response_chain_info -> "lepší hash (tie-breaker)" -> odchází
            #      request_blocks; odpověď je na cestě a nikdo ji nesleduje,
            #   2. mezitím dorazí new_block s TÝMŽ blokem, add_block() udělá
            #      mini-reorg a ten blok se stane naším vrcholem,
            #   3. teprve teď dorazí response_blocks z kroku 1. Náš vrchol se
            #      mezitím posunul, takže first_block_index (#1) se už nerovná
            #      current_index (#2) a kód spadne do větve pro fork: založí
            #      buffer a zavolá replace_chain() na blok, který JE naším
            #      vrcholem. Ten ho odmítne (stejná práce, stejná délka, hash
            #      není lepší - je shodný) a do logu spadne červené
            #      "Navrhovaný fork z bufferu není platný ... Odmítnuto."
            #
            # Opožděná odpověď na žádost, kterou předběhl broadcast téhož bloku,
            # je normální stav sítě - ne fork a ne vina protistrany. Řešením je
            # udělat sync idempotentní: co už v DB máme se stejným indexem
            # i hashem, to z dávky odřízneme. Nezbude-li nic, byla to jen
            # opožděná duplicita a tiše ji zahodíme.
            if not getattr(self, 'syncing_fork', False):
                known_count = 0
                # OPRAVA A-05: conn se zavíralo obyčejným řádkem UVNITŘ try,
                # takže ho jakákoli výjimka ze smyčky přeskočila - deskriptor
                # (plus WAL) zůstal viset až do cyklického GC. Bylo to jediné
                # místo v tomhle handleru bez try/finally, přesně proti pravidlu
                # z OPRAVY G-08 "nespoléhat na GC". Naměřeno ~135 otevřených
                # deskriptorů místo 4 po 300 zprávách po ~300 bajtech.
                conn = None
                try:
                    conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
                    conn.execute("PRAGMA journal_mode=WAL;")
                    c = conn.cursor()
                    for bd in blocks_data:
                        c.execute("SELECT 1 FROM blocks WHERE block_index = ? AND block_hash = ?",
                                  (bd['index'], bd['hash']))
                        if c.fetchone() is None:
                            break
                        known_count += 1
                except Exception as e:
                    # Selhání dotazu nesmí sync zastavit: neodřízne se nic
                    # a dávka projde původní cestou.
                    self.add_log(f"{Fore.YELLOW}Kontrolu duplicit v dávce od {ip_port} se nepodařilo provést ({e}), pokračuji bez ní.{Style.RESET_ALL}")
                    known_count = 0
                finally:
                    if conn is not None:
                        try:
                            conn.close()
                        except Exception:
                            pass

                if known_count == len(blocks_data):
                    self.add_log(f"{Fore.CYAN}Dávka od {ip_port} neobsahuje nic nového ({known_count} bloků už máme, poslední #{blocks_data[-1]['index']}). Ignoruji.{Style.RESET_ALL}")
                    # Navazující dávku si v řízeném syncu vyžádá smyčka
                    # sync_blocks_from_peer(), tady jen v reaktivní cestě.
                    if batch_has_more and not driven:
                        request = {'type': 'request_blocks', 'data': {'locator_hashes': [blocks_data[-1]['hash']]}}
                        requester_addr = self.resolve_peer_addr(addr, src_node_id)
                        if requester_addr:
                            self.send_to_peer(requester_addr, request)
                        else:
                            self.add_log(f"{Fore.YELLOW}Navazující žádost o bloky zahozena: naslouchací port uzlu {ip_port} není znám.{Style.RESET_ALL}")
                    return
                elif known_count > 0:
                    self.add_log(f"{Fore.CYAN}Prvních {known_count} bloků z dávky od {ip_port} už máme, zpracuji jen zbytek ({len(blocks_data) - known_count}).{Style.RESET_ALL}")
                    blocks_data = blocks_data[known_count:]

            current_index = self.blockchain.max_block_index + 1
            last_hash = self.blockchain.get_last_block().hash
            first_block_data = blocks_data[0]
            first_block_index = first_block_data['index']
            last_block_data = blocks_data[-1]
            
            if first_block_index == current_index and first_block_data['previous_hash'] == last_hash and not getattr(self, 'syncing_fork', False):
                added = False
                for block_data in blocks_data:
                    # OPRAVA AUDIT-2026-16 (audit 28. 10. 2026, nález 2): branka
                    # PoW i na téhle cestě, a to PŘED Block.from_dict().
                    #
                    # Tahle větev ("přímé pokračování") byla jediná ze TŘÍ cest,
                    # kterými blok ze sítě vstupuje, bez branky: forková větev
                    # téhož handleru ji má od OPRAVY U-19 (volá se v
                    # _store_fork_batch_inner i na first_block_data), cesta
                    # 'new_block' od OPRAVY Y-1. Komentář u Y-1 přitom říká
                    # otevřeně, že "dvě síťové cesty přijímající bloky se nesmějí
                    # lišit v tom, co po nich chtějí, ani v tom, KDY to chtějí" -
                    # jenže se to tehdy dopsalo jen do 'new_block'.
                    #
                    # Druhá polovina nálezu je POSTIH. Zamítnutí v add_block()
                    # níž jen logovalo, takže týž podvržený blok, který přes
                    # 'new_block' stojí BAN_DURATION_PROTOCOL, byl přes
                    # 'response_blocks' zdarma a opakovatelný donekonečna.
                    # Naměřeno 7 ze 7 případů (podvržený hash, merkle_root,
                    # state_root, cizí chain_id, target pod síťovým minimem,
                    # target 2**63, chybějící state_root): 'new_block' -> 24h,
                    # 'response_blocks' -> bez banu. Útočník si prostě vybral
                    # druhou cestu.
                    #
                    # Branka je bez vedlejších efektů a konstantně drahá, takže
                    # ji lze volat nad syrovým dictem; poctivý blok s platným PoW
                    # žádnou z jejích podmínek porušit nemůže.
                    duvod_pow = self._pow_branka_bloku(block_data)
                    if duvod_pow is not None:
                        self.add_log(f"{Fore.RED}Blok v dávce od {ip_port} zahozen ještě před parsováním: {duvod_pow}{Style.RESET_ALL}")
                        if addr:
                            self.ban_peer(addr[0], duvod_pow, BAN_DURATION_PROTOCOL)
                        break

                    # OPRAVA D-02/D-07: from_dict pracuje s nedůvěryhodnými daty
                    # a nově garantuje ValueError i pro target mimo rozsah.
                    # Necháme-li ji propadnout, spadne celé spojení v obecném
                    # except handle_client_connection - bez logu a bez postihu.
                    try:
                        block = Block.from_dict(block_data)
                    except ValueError as e:
                        self.add_log(f"{Fore.RED}Nečitelný blok v dávce od {ip_port}: {zkrat(e)}{Style.RESET_ALL}")
                        if addr:
                            self.ban_peer(addr[0], "nečitelný blok v response_blocks", BAN_DURATION_PROTOCOL)
                        break
                    if block.index != current_index or block.previous_hash != last_hash:
                        self.add_log(f"{Fore.RED}Uvnitř přijatých bloků je chyba návaznosti, přerušuji.{Style.RESET_ALL}")
                        break
                    if self.blockchain.add_block(block, block.hash):
                        current_index += 1
                        last_hash = block.hash
                        added = True
                    else:
                        # OPRAVA AUDIT-2026-16 (nález 2): tady se ZÁMĚRNĚ
                        # NEBANUJE, přesně jako na cestě 'new_block'.
                        #
                        # add_block() vrací False i z důvodů, za které peer
                        # nemůže: vypršení ADD_BLOCK_LOCK_TIMEOUT ("System is
                        # busy") a MissingChainDataError nad nečitelnou vlastní
                        # databází. Ban by tedy trestal poctivý uzel za NÁŠ
                        # lokální problém - a to je přesně ten failure mode,
                        # proti kterému míří OPRAVY #1, #21 a N-1.
                        #
                        # Postih nese branka výš, a to stačí: hlavička, kterou
                        # hashuje (Block.hlavicka_hash_z_dictu), zahrnuje
                        # version, chain_id, index, timestamp, nonce, target,
                        # previous_hash, merkle_root I state_root. Jakákoli
                        # podvržená hodnota kteréhokoli z nich tedy hash
                        # hlavičky rozbije a branka ji zachytí s banem - ověřeno
                        # na všech sedmi případech z nálezu. Co brankou projde,
                        # za to odesílatel ZAPLATIL platným PoW, takže to není
                        # zdarma opakovatelné.
                        self.add_log(f"{Fore.RED}Neplatný blok #{block.index}, přerušuji přidávání.{Style.RESET_ALL}")
                        break

                if added:
                    save_data_z_p2p(self.blockchain, self.peers_snapshot())
                    self.add_log(f"{Fore.GREEN}Nové bloky úspěšně přidány (přímé pokračování).{Style.RESET_ALL}")
                    
                if batch_has_more and not driven:
                    request = {'type': 'request_blocks', 'data': {'locator_hashes': [last_block_data['hash']]}}
                    requester_addr = self.resolve_peer_addr(addr, src_node_id)
                    if requester_addr:
                        self.send_to_peer(requester_addr, request)
                    else:
                        # OPRAVA #9: bez broadcastu.
                        self.add_log(f"{Fore.YELLOW}Navazující žádost o bloky zahozena: naslouchací port uzlu {ip_port} není znám.{Style.RESET_ALL}")

            else:
                # OPRAVA U-19 (audit 7. 10. 2026, nález 1, 1/2): celý PŘECHOD
                # stavového automatu je nově pod fork_lock.
                #
                # Dřív se syncing_fork přečetlo tady a příznaky se zapsaly až
                # o desítky řádků níž - mezi tím ležela dvě otevření SQLite
                # a mazání souborů. Dvě vlákna tedy obě viděla False a obě prošla
                # větví volající discard_sync_buffer(); naměřeno 37 ze 40 kol.
                # A dvě odpovědi naráz nejsou výjimečný stav:
                # sync_chain_periodically() spouští vlákno na každého peera
                # zároveň, takže stačili dva poctiví peeři odpovídající současně
                # a práce jednoho z nich šla do koše - při hlubokém reorgu až
                # MAX_REORG_DEPTH bloků a desítky MiB.
                #
                # Příznak se uvnitř zámku čte ZNOVU. Hodnota přečtená před jeho
                # získáním je bezcenná - přesně na ní ten závod stál.
                #
                # Zámek se drží jen přes přechod; _store_fork_batch() níž (zápis
                # dávky, případný reorg) běží už bez něj. Souběžnou dávku od
                # jiného uzlu tam odstíní pravidlo ETAPY 3 podle fork_peer_ip.
                with self.fork_lock:
                    # OPRAVA N3 (audit 10. 10. 2026, nález N3): slot se
                    # nepřiděluje podle POŘADÍ PŘÍCHODU.
                    #
                    # Sem se dřív nedalo dostat, dokud držitel slot nepustil:
                    # cesta k založení forku vede jen přes syncing_fork ==
                    # False a _store_fork_batch_inner() zahodí cokoli od jiné
                    # IP, než je fork_peer_ip. Kdo tedy poslal první PoW-platný
                    # blok, držel slot celých FORK_SYNC_IDLE_TIMEOUT a poctivá
                    # těžší větev se ignorovala - naměřeno šest kol za sebou,
                    # uzel zůstal na #12 proti dostupné větvi po #30. Útočníkovi
                    # na to stačil JEDEN blok na síťovém minimu, přehrávaný
                    # dokola.
                    #
                    # Nárok cizího uzlu se proto posuzuje PODLE PRÁCE. Příznaky
                    # se jen uvolní; buffer se tady ZÁMĚRNĚ nemaže, o tom
                    # rozhodne až _zalozit_novy_fork() - jinak by stačila
                    # nabídka s velkou prací a neznámým rodičem a buffer by
                    # zmizel za nic.
                    if getattr(self, 'syncing_fork', False):
                        if self._lze_prevzit_fork_slot(addr, blocks_data, ip_port):
                            self.syncing_fork = False
                            self.fork_peer_ip = None
                            self.fork_sync_start = 0
                    if not getattr(self, 'syncing_fork', False):
                        # OPRAVA U-19 (nález 1, 2/2): PoW BRANKA PŘED čímkoli
                        # destruktivním.
                        #
                        # Druhá polovina nálezu: PoW se ověřovalo až
                        # v _store_fork_batch_inner(), tedy AŽ ZA
                        # discard_sync_buffer() o kus níž. Dávka bez jediného
                        # vytěženého hashe tak stihla smazat rozpracovaný buffer
                        # (naměřeno 30 bloků před, 0 po) a odesílatel za to
                        # zaplatil jen 24hodinovým banem - z jiné IP si ho koupí
                        # znovu, oběť přijde o celý přenesený pokrok.
                        #
                        # Ověřuje se PRVNÍ blok dávky: ten rozhoduje, jestli se
                        # vůbec sáhne na buffer, a zbytek dávky stejně projde
                        # toutéž brankou v _store_fork_batch_inner(). Cena
                        # útoku je tím znovu PoW, na což komentář u OPRAVY A-3
                        # výslovně spoléhá.
                        #
                        # Odmítnutí je ZÁMĚRNĚ nedestruktivní - žádné
                        # _abort_fork_sync(). To by buffer smazalo, tedy udělalo
                        # přesně to, čemu branka brání. Ban zůstává: hash, který
                        # neodpovídá vlastní hlavičce, je prokazatelná vina
                        # odesílatele, ne výpadek sítě.
                        duvod = self._pow_branka_bloku(first_block_data)
                        if duvod is not None:
                            self.add_log(f"{Fore.RED}Dávka od {ip_port} zahozena před sáhnutím na buffer: "
                                         f"{duvod}{Style.RESET_ALL}")
                            if addr:
                                self.ban_peer(addr[0], duvod, BAN_DURATION_PROTOCOL)
                            # False, ne None: dávku jsme odmítli, ať se započítá
                            # do MAX_UNAUTHENTICATED_MESSAGES.
                            return False

                        # OPRAVA #6c: pokud v bufferu leží rozpracovaný fork a tahle
                        # dávka na něj navazuje, POKRAČUJEME místo abychom začínali
                        # znovu. Bez toho byl každý pokus po timeoutu nulový pokrok
                        # a nad hraničním RTT se hluboký reorg nedotáhl nikdy.
                        buffer_tip = self.sync_buffer_tip()
                        resuming = (
                            buffer_tip is not None
                            and self.fork_start_index is not None
                            and first_block_index == buffer_tip[0] + 1
                            and first_block_data['previous_hash'] == buffer_tip[1]
                        )
                        if resuming:
                            self.add_log(f"{Fore.CYAN}Navazuji na rozpracovaný fork buffer (v bufferu do #{buffer_tip[0]}, přišel #{first_block_index}).{Style.RESET_ALL}")
                            self.syncing_fork = True
                            self.fork_sync_start = time.time()
                            # ETAPA 3: první uzel, který na obnovení odpoví, se stává
                            # zdrojem forku; ostatní odpovědi se ignorují bez postihu.
                            self.fork_peer_ip = addr[0] if addr else None
                            self.init_sync_buffer(reset=False)
                            # fork_start_index zůstává původní - buffer se skládá dál.
                            # OPRAVA U-19: dávka se zapisuje až ZA zámkem, jedním
                            # společným voláním na konci větve.
                        else:
                            vysledek = self._zalozit_novy_fork(
                                blocks_data, first_block_index, first_block_data,
                                addr, ip_port, src_node_id)
                            if vysledek is None:
                                # Dávka odmítnuta (neznámý rodič). Odmítnutí se
                                # má započítat do MAX_UNAUTHENTICATED_MESSAGES.
                                return False
                            if vysledek is NotImplemented:
                                # Odešel fallback na full sync, do bufferu se
                                # nezapisuje nic.
                                return

                return self._store_fork_batch(blocks_data, first_block_index, last_block_data,
                                              addr, ip_port, batch_has_more, driven, src_node_id)

        elif msg_type == 'request_full_chain':
            # OPRAVA L-3: týž vzorec jako u request_blocks, který řešila OPRAVA
            # G-08 - jen se sem tehdy nedostala. json.loads() nad poškozeným
            # řádkem vyhodí uvnitř smyčky a conn.close() na konci se přeskočí.
            conn = None
            chain_data = []
            full_chain_bytes = 0
            uctovano = 0
            try:
                conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
                conn.execute("PRAGMA journal_mode=WAL;")
                c = conn.cursor()
                # OPRAVA AUDIT-2026-2 (nález 2): předběžné účtování, stejně jako
                # u request_blocks o kus výš. Tahle odpověď je ze všech nejdražší,
                # takže tady na pořadí "zaplať, pak pracuj" záleží nejvíc.
                c.execute(
                    "SELECT COUNT(*), COALESCE(SUM(LENGTH(CAST(transactions AS BLOB))), 0) FROM "
                    "(SELECT transactions FROM blocks ORDER BY block_index LIMIT ?)",
                    (SYNC_BATCH_SIZE,))
                odhad_radku = c.fetchone() or (0, 0)
                odhad_bajtu = min(MAX_BATCH_BYTES,
                                  int(odhad_radku[1] or 0) + int(odhad_radku[0] or 0) * 512) + 512
                uctovano = self.uctuj_predem(addr, odhad_bajtu, ip_port, "Požadavek na full-chain")
                if uctovano is None:
                    return True
                # OPRAVA #21: stejný bajtový strop jako u request_blocks - i tady by
                # 100 plných bloků přeteklo MAX_MESSAGE_SIZE a vedlo na ban poctivého uzlu.
                c.execute("SELECT block_index, timestamp, transactions, previous_hash, target_hex, nonce, block_hash, merkle_root, version, chain_id, state_root FROM blocks ORDER BY block_index LIMIT ?", (SYNC_BATCH_SIZE,))
                for row in c:
                    if chain_data and full_chain_bytes + len(row[2]) + 512 > MAX_BATCH_BYTES:
                        break
                    full_chain_bytes += len(row[2]) + 512
                    chain_data.append({
                        'index': row[0],
                        'timestamp': row[1],
                        'transactions': json.loads(row[2]),
                        'previous_hash': row[3],
                        'target': row[4],
                        'nonce': row[5],
                        'hash': row[6],
                        'merkle_root': row[7],
                        'version': row[8],
                        'chain_id': row[9], 'state_root': row[10]
                    })
            finally:
                if conn is not None:
                    try:
                        conn.close()
                    except sqlite3.Error:
                        pass
            response = {'type': 'response_full_chain', 'data': chain_data}
            # OPRAVA #9: broadcast fallback zrušen i tady - tahle odpověď je ze
            # všech nejdražší.
            self._respond(message, response, addr, ip_port, reply,
                          f"Požadavek na full-chain ({len(chain_data)} bloků)",
                          src_node_id, uz_uctovano=uctovano)
                
        elif msg_type == 'response_full_chain':
            # OPRAVA Y-5 (nález 5): branka je nově vázaná na IP, které jsme se
            # ptali, a na okno FULL_CHAIN_RESPONSE_WINDOW; konzumuje se
            # jednorázově. Dřív to byl bool bez expirace, takže po jediné
            # nezodpovězené žádosti zůstal otevřený napořád a prošla jím
            # libovolně pozdější nevyžádaná odpověď od kteréhokoli známého uzlu.
            # Je to týž tvar jako u consume_mempool_expectation() - dvě branky,
            # které dělají totéž, se nemají lišit.
            if not self.consume_full_chain_expectation(addr):
                self.add_log(f"{Fore.YELLOW}Přijat nevyžádaný response_full_chain od uzlu {ip_port}, ignoruji.{Style.RESET_ALL}")
                return False
            new_chain_data = message.get('data', [])
            
            if self.blockchain.replace_chain(0, new_chain_data):
                save_data_z_p2p(self.blockchain, self.peers_snapshot())
                self.add_log(f"{Fore.GREEN}Počáteční dávka blockchainu z reorgu (od indexu 0) byla úspěšně uložena. Zbytek stáhne inkrementální proces.{Style.RESET_ALL}")
            else:
                self.add_log(f"{Fore.YELLOW}Přijatý počáteční řetězec není platný nebo lepší, odmítám ho.{Style.RESET_ALL}")
                
        elif msg_type == 'new_block':
            new_block_data = message['data']

            # OPRAVA D-01: branka MUSÍ být tady, ne až v add_block(). Původně se
            # blok ověřoval jen proti targetu, KTERÝ SI DEKLAROVAL SÁM ODESÍLATEL
            # - přesně ta chyba, kterou OPRAVA #8 odstranila v _store_fork_batch,
            # ale do téhle cesty se nedostala. S target = 2^256-1 prošel libovolný
            # hash při nonce = 0, tedy za nula hashů. add_block() takový blok sice
            # odmítl kvůli velikosti, jenže handler ho hned nato uložil do
            # orphan_poolu, který velikost ani PoW nekontroluje: 100 bloků po
            # 9,46 MiB = 1,09 GiB RAM za ~3 s a zdarma. Na telefonu to znamená
            # OOM kill nebo uváznutí ve swapu.
            #
            # Nejdřív bajtový strop nad SYROVÝMI daty - parsování bloku počítá
            # tx_id každé transakce, takže je řádově dražší než tahle kontrola
            # a nesmíme ho útočníkovi zaplatit předem.
            try:
                raw_size = len(json.dumps(new_block_data, separators=(',', ':'), sort_keys=True).encode('utf-8'))
            except (TypeError, ValueError):
                if addr:
                    self.ban_peer(addr[0], "neserializovatelný blok v new_block", BAN_DURATION_PROTOCOL)
                return False
            if raw_size > MAX_BLOCK_SIZE_BYTES:
                self.add_log(f"{Fore.RED}Blok od {ip_port} překračuje MAX_BLOCK_SIZE ({raw_size} B), zahozeno.{Style.RESET_ALL}")
                if addr:
                    self.ban_peer(addr[0], "blok překračující MAX_BLOCK_SIZE", BAN_DURATION_PROTOCOL)
                return False

            # OPRAVA Y-1 (audit 14. 10. 2026, nález 1): PoW se ověřuje nad
            # SYROVÝM dictem, tedy JEŠTĚ PŘED Block.from_dict().
            #
            # Komentář o kus níž ("Rychlá validace PoW před složitějším
            # zpracováním") popisoval záměr, kterému umístění neodpovídalo:
            # from_dict() naparsuje a zahashuje KAŽDOU transakci bloku, takže
            # se za zprávu bez jediného vytěženého hashe platilo plnou cenou.
            # Naměřeno na bloku 1 MiB s 3 370 transakcemi: 81 ms na zprávu
            # proti 0,0037 ms, které stojí kontrola, jež ji zamítne - poměr
            # 21 787:1. Bajtový rozpočet (INBOUND_BYTES_PER_SECOND) pustí
            # z jedné IP 2 MiB/s, tedy dvě takové zprávy za sekundu = 16 %
            # jádra; při MAX_INBOUND_PER_IP = 4 a MAX_INBOUND_CONNECTIONS = 64
            # je to 16 IP naráz, naměřeno 259 % jádra na x86. Cílová platforma
            # je ARM v Termuxu, kde jsou CPU náklady násobkem.
            #
            # _pow_branka_bloku() je přesně tahle kontrola a je konstantně
            # drahá: hash hlavičky nezávisí na transakcích a nic se neparsuje
            # (Block.hlavicka_hash_z_dictu). Je to TÁŽ branka, jakou používá
            # cesta 'response_blocks' - dvě síťové cesty přijímající bloky se
            # nesmějí lišit v tom, co po nich chtějí, ani v tom, KDY to chtějí.
            #
            # Druhá polovina nálezu je POSTIH. Všechny ostatní zamítavé cesty
            # v tomhle handleru udělují BAN_DURATION_PROTOCOL (neserializovatelný
            # blok, překročení MAX_BLOCK_SIZE, nečitelný blok, target pod
            # síťovým minimem), jen selhání PoW vracelo holé False - tedy
            # jediná z nich, která PROKAZUJE, že si odesílatel blok vymyslel,
            # byla zdarma a opakovatelná donekonečna. Blok s platným PoW
            # žádnou z těchto podmínek porušit nemůže, takže se ban nemá jak
            # trefit do poctivého uzlu.
            duvod_pow = self._pow_branka_bloku(new_block_data)
            if duvod_pow is not None:
                self.add_log(f"{Fore.RED}Blok od {ip_port} zahozen ještě před parsováním: {duvod_pow}{Style.RESET_ALL}")
                if addr:
                    self.ban_peer(addr[0], duvod_pow, BAN_DURATION_PROTOCOL)
                return False

            # OPRAVA D-07: from_dict nově garantuje ValueError i pro target mimo
            # rozsah (dřív unikla OverflowError až do handle_client_connection).
            try:
                new_block = Block.from_dict(new_block_data)
            except ValueError as e:
                self.add_log(f"{Fore.RED}Nečitelný blok od {ip_port}: {zkrat(e)}{Style.RESET_ALL}")
                if addr:
                    self.ban_peer(addr[0], "nečitelný blok v new_block", BAN_DURATION_PROTOCOL)
                return False

            # Target nesmí být volnější než síťové minimum (FIXED_TARGET je
            # počáteční, tedy nejsnazší povolená obtížnost). Teprve tím se
            # z kontroly PoW níž stává reálná cena. Přesné pravidlo pro danou
            # výšku ověří add_block() přes calculate_expected_target().
            #
            # OPRAVA Y-1: obě kontroly níž jsou od téhle opravy obranou v DRUHÉ
            # linii - branka výš je dělá nad syrovým dictem, tohle je totéž nad
            # naparsovaným blokem. Záměrně se nerušily: from_dict() hodnoty
            # normalizuje a kód se jinde výslovně odmítá spoléhat na jedinou
            # kontrolu (OPRAVA #4, D-15). Postih je stejný jako u branky.
            if not (0 < new_block.target <= FIXED_TARGET):
                self.add_log(f"{Fore.RED}Blok od {ip_port} deklaruje target snazší než síťové minimum, zahozeno.{Style.RESET_ALL}")
                if addr:
                    self.ban_peer(addr[0], "blok s targetem snazším než síťové minimum", BAN_DURATION_PROTOCOL)
                return False

            # Rychlá validace PoW před složitějším zpracováním
            quick_hash = new_block.compute_hash()
            if quick_hash != new_block.hash or not Blockchain.meets_difficulty(quick_hash, new_block.target):
                self.add_log(f"{Fore.RED}Přijatý blok neprošel rychlou kontrolou PoW, zahozeno.{Style.RESET_ALL}")
                # OPRAVA Y-1: doplněn chybějící postih - viz branka výš.
                if addr:
                    self.ban_peer(addr[0], "blok s neplatným PoW v new_block", BAN_DURATION_PROTOCOL)
                return False

            if self.blockchain.add_block(new_block, new_block.hash):
                # Zastavíme těžení až po úspěšném ověření a zapsání bloku do DB uvnitř add_block
                if self.blockchain.mining_in_progress:
                    self.blockchain.mining_in_progress = False
                    self.add_log(f"{Fore.YELLOW}Těžba zastavena, přijat platný nový blok.{Style.RESET_ALL}")

                self.add_log(f"{Fore.GREEN}Přijat a přidán nový blok {new_block.index} od jiného uzlu.{Style.RESET_ALL}")
                self.add_log(f"{Fore.YELLOW}Mempool byl bezpečně aktualizován.{Style.RESET_ALL}")
                # OPRAVA W-2 (audit 9. 10. 2026, nález N-2): přeposlat dál,
                # a to HNED - dřív než save_data_z_p2p(), která sahá na disk.
                # U bloku jde o latenci: každých ušetřených pár set milisekund
                # na skok se násobí průměrem sítě a přímo snižuje míru
                # osiřelých bloků. Zápis na disk tu nic nebrzdí, blok už je
                # v DB z add_block().
                #
                # Přeposílá se jen blok, který PRÁVĚ TEĎ prošel add_block(),
                # takže se nešíří nic neověřeného; orphan ani odmítnutý
                # konkurent na stejné výšce se dál neposílá (add_block vrátí
                # False). Tím je zároveň vyřešená smyčka: druhý výskyt téhož
                # bloku už add_block() nepřijme.
                self.preposli_sousedum({'type': 'new_block', 'data': new_block.to_dict()},
                                       ('blok', new_block.hash), addr, src_node_id=src_node_id)
                save_data_z_p2p(self.blockchain, self.peers_snapshot())
            else:
                # OPRAVA L-3: spojení bez try/finally na síťové cestě. json se
                # tu sice neparsuje, ale sqlite3.OperationalError ("database is
                # locked" při souběžném zápisu bloku) je běžný stav - a odsud
                # vedla rovnou k netěsnému spojení.
                conn = None
                db_nedostupna = False
                # OPRAVA AUDIT-2026-15 (audit 27. 10. 2026, nález 4): vedle
                # rodiče se ptáme i na blok SÁM. Viz odůvodnění u `return False`
                # na konci téhle větve - potřebujeme odlišit čistý replay bloku,
                # který už máme, od poctivého konkurenta na stejné výšce.
                # Jde o tentýž dotaz nad týmž indexem a po témž spojení, takže
                # to nestojí ani další otevření DB.
                uz_mame = False
                try:
                    conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
                    conn.execute("PRAGMA journal_mode=WAL;")
                    c = conn.cursor()
                    c.execute("SELECT 1 FROM blocks WHERE block_hash = ?", (new_block.previous_hash,))
                    exists = c.fetchone() is not None
                    c.execute("SELECT 1 FROM blocks WHERE block_hash = ?", (new_block.hash,))
                    uz_mame = c.fetchone() is not None
                except sqlite3.Error as e:
                    # OPRAVA S-4 (Nález 2): OPRAVA L-3 sem doplnila `finally`
                    # kvůli netěsnému spojení, ale `except` ne - a komentář
                    # o dva řádky výš přitom sám uvádí, že "database is locked"
                    # je BĚŽNÝ stav. Výjimka proletěla do obecného `except`
                    # v handle_message(), zpráva se zahodila a blok se neuložil
                    # ani do orphan poolu, ani se nevyžádal chain_info.
                    #
                    # Paradox: k souběhu zápisů dochází právě tehdy, když uzel
                    # dostává bloky nejrychleji - tedy když na jejich udržení
                    # nejvíc záleží.
                    #
                    # Fail-safe je chovat se jako při NEZNÁMÉM rodiči: orphan
                    # pool je čistě paměťový (žádné SQLite), takže blok přežije
                    # i se zamčenou databází, a chain_info doplní, co nevíme.
                    exists = False
                    db_nedostupna = True
                    self.add_log(f"{Fore.YELLOW}Databázi nelze číst ({type(e).__name__}: {e}); "
                                 f"blok {new_block.index} držím v orphan poolu.{Style.RESET_ALL}")
                finally:
                    if conn is not None:
                        try:
                            conn.close()
                        except Exception:
                            pass
                
                if exists:
                    request = {'type': 'request_chain_info'}
                    requester_addr = self.resolve_peer_addr(addr, src_node_id)
                    if not requester_addr:
                        self.add_log(f"{Fore.YELLOW}Přijatý blok není navázaný na náš poslední blok, ale naslouchací port uzlu {ip_port} není znám. Ignoruji.{Style.RESET_ALL}")
                    # OPRAVA N2 (audit 10. 10. 2026, nález N2): tahle jediná
                    # řádka byla celý útok. Blok, který add_block() odmítne,
                    # ale jehož rodiče máme v DB, je pro útočníka zadarmo -
                    # je to replay libovolného veřejného bloku - a každý takový
                    # vyrobil nové odchozí vlákno i socket na ~10 s. Rozpočet
                    # je nově na IP a na okno; zahození NENÍ ztráta, protože se
                    # touhle zprávou jen ptáme na délku cizího řetězce a totéž
                    # se periodický sync ptá všech peerů každých 10 s.
                    elif not self._muze_zadat_chain_info(addr):
                        self.add_log(f"{Fore.YELLOW}Přijatý blok není navázaný na náš poslední blok; "
                                     f"uzlu {ip_port} jsme se na stav řetězce ptali před méně než "
                                     f"{int(CHAIN_INFO_REQUEST_COOLDOWN)} s, dotaz neopakuji.{Style.RESET_ALL}")
                    else:
                        self.add_log(f"{Fore.YELLOW}Přijatý blok není navázaný na náš poslední blok. Zahajuji synchronizaci s {ip_port}...{Style.RESET_ALL}")
                        self.send_to_peer(requester_addr, request)
                else:
                    self.blockchain.add_orphan_block(new_block)
                    self.add_log(f"{Fore.YELLOW}Přijat orphan blok {new_block.index}, uložen do poolu.{Style.RESET_ALL}")
                    # OPRAVA S-4 (Nález 2): o rodiči nevíme nic jen proto, že se
                    # nepodařilo přečíst DB - o chain_info se proto řekne i tady.
                    # Bez toho by blok v poolu jen čekal na expiraci (600 s).
                    #
                    # OPRAVA N2: týž rozpočet jako o pár řádků výš. Je to táž
                    # zpráva se stejnou cenou, jen vyvolaná jinou větví, a
                    # útočník si mezi nimi vybere podle toho, co se mu hodí.
                    if db_nedostupna:
                        requester_addr = self.resolve_peer_addr(addr, src_node_id)
                        if requester_addr and self._muze_zadat_chain_info(addr):
                            self.send_to_peer(requester_addr, {'type': 'request_chain_info'})

                # OPRAVA AUDIT-2026-16 (audit 28. 10. 2026, nález 1): blok,
                # který už máme, se NEZAPOČÍTÁVÁ do MAX_UNAUTHENTICATED_MESSAGES.
                #
                # OPRAVA AUDIT-2026-15 tady zavedla `return False` s odůvodněním,
                # že "blok, který už MÁME v databázi, je čistý replay". To ale
                # platí jen pro útočníka. Pro poctivého souseda je to NORMÁLNÍ
                # důsledek lavinového šíření z OPRAVY W-2: preposli_sousedum()
                # rozesílá blok všem kromě přímého odesílatele, takže
                # v topologii s cyklem dorazí tentýž blok ZARUČENĚ dvakrát -
                # v trojúhelníku A-B-C ho C dostane od A i od B. Druhý z nich
                # jsme si přitom sami vyžádali tím, že jsme se k oběma připojili.
                #
                # Pět takových duplicit za sebou zavřelo spojení poctivému
                # uzlu, a protože relay i synchronizační dotazy jedou po témž
                # PeerConnection, vzalo to s sebou i rozpracovaný sync (viz
                # podrobné odůvodnění u téže opravy na cestě 'transaction').
                #
                # Zdarma opakovatelné to není: 'new_block' patří od OPRAVY N2
                # mezi drahé dotazy, takže na replay sedí EXPENSIVE_BUCKET
                # (40 tokenů, obnova 4/s na IP) a zpráva se zahodí dřív, než se
                # sem dojde.
                #
                # Zbytek téhle větve se nezapočítával už dřív a platí to dál:
                #   - konkurent na stejné výšce, který prohrál tie-break, je
                #     poctivý blok od poctivého těžaře. Jeho previous_hash míří
                #     na rodiče našeho vrcholu, takže spadne do téhož `else`,
                #     ale uzel za něj trestat nesmíme.
                #   - orphan (neznámý rodič) znamená, že jsme POZADU. Trestat
                #     peera, který nám posílá platné nové bloky během dohánění,
                #     by spojení zavřelo přesně v okamžiku, kdy ho potřebujeme.
                if uz_mame:
                    self.add_log(f"{Fore.YELLOW}Blok {new_block.hash} už máme (duplicita z přeposílání), zahozen.{Style.RESET_ALL}")
                    return True

        elif msg_type == 'request_mempool':
            # OPRAVA F-04: odpověď je shora omezená počtem i objemem. Dřív se
            # posílal celý mempool, tedy až ~16 700 transakcí v jedné zprávě.
            # Vybírají se transakce s nejvyšší sazbou poplatku - to je i to,
            # co protistrana nejspíš potřebuje vytěžit.
            #
            # OPRAVA W-5 (audit 9. 10. 2026, nález N-2b): okno se po každé
            # odpovědi POSOUVÁ.
            #
            # Dřív se pořadí počítalo jen podle sazby a posílalo se prvních
            # MAX_MEMPOOL_RESPONSE_TX položek, tedy při každém kole TÁŽ pětistovka.
            # Komentář u té konstanty tvrdil, že "zbytek doteče běžným rozesíláním
            # 'transaction' a dalším kolem periodické synchronizace" - jenže
            # rozesílání neexistovalo (nález N-2, viz OPRAVA W-2) a další kolo
            # poslalo totéž, protože pořadí je deterministické. Transakce na
            # 3000. místě se do okna dostala, až se nad ní vytěžilo 2500
            # dražších; při trvalém zahlcení nikdy. Při plném mempoolu se za
            # první skok nedostalo ~97 % transakcí.
            #
            # Řešení je rotace: pořadí je totální (sazba sestupně, při shodě
            # tx_id), u každého peera si pamatujeme klíč POSLEDNÍ odeslané
            # položky a příště pokračujeme za ním, s přetočením na začátek.
            # Celý mempool se tak pokryje za ceil(N / okno) kol, při plném
            # mempoolu a periodě 10 s zhruba za 6 minut.
            #
            # Kurzor je KLÍČ, ne index: mempool se mezi koly mění a index by
            # ukazoval na něco jiného. Paměťově je to jedna dvojice na peera.
            #
            # MAX_MEMPOOL_RESPONSE_TX = 500 se ZÁMĚRNĚ nezvyšuje, přestože by se
            # do MAX_BATCH_BYTES vešlo ~13 000 transakcí: příjemce počet
            # kontroluje a nad limitem uděluje BAN_DURATION_PROTOCOL. Uzel se
            # starším kódem by tedy za větší odpověď zabanoval poctivý nový
            # uzel - failure mode, proti kterému míří OPRAVY #1, #21 a N-1.
            # Objem dál drží MAX_BATCH_BYTES, počet je jen kompatibilní strop.
            pool = list(self.blockchain.unconfirmed_transactions)
            # Klíče se počítají jednou dopředu: _fee_rate() je sice nad cache
            # z OPRAVY D-04 levný, ale volá se při řazení O(n log n)krát.
            klice = {t.tx_id: (-Blockchain._fee_rate(t), t.tx_id) for t in pool}
            pool.sort(key=lambda t: klice[t.tx_id])

            kurzor = self._mempool_kurzor_get(addr)
            zacatek = 0
            if kurzor is not None:
                # První položka ostře za kurzorem v témže uspořádání. Binární
                # půlení nad už setříděným seznamem, tedy O(log n).
                lo, hi = 0, len(pool)
                while lo < hi:
                    stred = (lo + hi) // 2
                    if klice[pool[stred].tx_id] > kurzor:
                        hi = stred
                    else:
                        lo = stred + 1
                zacatek = lo
            # Přetočení: za koncem se pokračuje od nejdražších, takže ani po
            # vyčerpání okna nevznikne kolo, ve kterém by se neposlalo nic.
            poradi = pool[zacatek:] + pool[:zacatek] if zacatek else pool

            # OPRAVA AUDIT-2026-2 (nález 2): nejdřív se jen SEČTE, co by odpověď
            # obsahovala, a odhad se strhne z rozpočtu; teprve pak se volá
            # tx.to_dict(), tedy to drahé. tx.get_size() je díky cache
            # z OPRAVY D-04 konstanta, takže samotný součet nic nestojí.
            vybrane_tx = []
            objem = 0
            for tx in poradi[:MAX_MEMPOOL_RESPONSE_TX]:
                velikost = tx.get_size()
                if vybrane_tx and objem + velikost > MAX_BATCH_BYTES:
                    break
                vybrane_tx.append(tx)
                objem += velikost

            # Kurzor se posouvá, i když odpověď nakonec neodejde (vyčerpaný
            # rozpočet níž): příště se má pokračovat dál, ne znovu od začátku.
            # Vešel-li se celý mempool, kurzor se ruší a další kolo začne zase
            # u nejdražších - jinak by se při malém mempoolu zbytečně rotovalo.
            if not vybrane_tx or len(vybrane_tx) >= len(pool):
                self._mempool_kurzor_set(addr, None)
            else:
                self._mempool_kurzor_set(addr, klice[vybrane_tx[-1].tx_id])

            uctovano = self.uctuj_predem(addr, objem + 512, ip_port, "Požadavek na mempool")
            if uctovano is None:
                return True
            vybrane = [tx.to_dict() for tx in vybrane_tx]
            response = {'type': 'response_mempool', 'data': vybrane}
            self._respond(message, response, addr, ip_port, reply, "Požadavek na mempool",
                          src_node_id, uz_uctovano=uctovano)
                
        elif msg_type == 'response_mempool':
            # OPRAVA F-04: branka. Bez ní mohl kdokoli po handshaku poslat
            # nevyžádanou dávku transakcí a obejít rozpočet transakcí (TX_RATE_*).
            # Stejný vzorec jako awaiting_full_chain u response_full_chain.
            if not self.consume_mempool_expectation(addr):
                self.add_log(f"{Fore.YELLOW}Přijat nevyžádaný response_mempool od uzlu {ip_port}, ignoruji.{Style.RESET_ALL}")
                return False

            tx_data_list = message['data']
            if len(tx_data_list) > MAX_MEMPOOL_RESPONSE_TX:
                self.add_log(f"{Fore.RED}response_mempool od {ip_port} obsahuje {len(tx_data_list)} transakcí, limit je {MAX_MEMPOOL_RESPONSE_TX}. Zahazuji.{Style.RESET_ALL}")
                if addr:
                    self.ban_peer(addr[0], "response_mempool nad limitem", BAN_DURATION_PROTOCOL)
                return False

            self.add_log(f"{Fore.YELLOW}Přijat mempool s {len(tx_data_list)} transakcemi.{Style.RESET_ALL}")

            # OPRAVA F-04 + F-07: množina tx_id se staví JEDNOU, ne pro každou
            # položku znovu. Původní kód uvnitř cyklu skládal set přes celý
            # mempool, což při 16 700 položkách vycházelo extrapolovaně na
            # ~17 s CPU na jedinou zprávu - a to celé pod droid_chain.lock.
            # Index mempool_by_txid tuhle práci stejně už drží hotovou.
            #
            # OPRAVA AUDIT-2026-11 (audit 25. 10. 2026, nález 1): parsování se
            # vytáhlo před smyčku a transakce se MEZI parsováním a vkládáním
            # SEŘADÍ podle (odesílatel, nonce).
            #
            # Důvod: handler 'request_mempool' výš řadí odpověď podle SAZBY
            # POPLATKU (klice[t.tx_id] = (-fee_rate, tx_id)), ale
            # add_transaction() přijme jen PŘESNĚ následující nonce. Transakce,
            # která dorazila dřív než její předchůdce, tedy propadla - a protože
            # se řadí sestupně podle poplatku, propadala systematicky ta
            # NEJDRAŽŠÍ transakce v posloupnosti.
            #
            # Naměřeno na dvou uzlech se shodným řetězcem, 6 transakcí jednoho
            # odesílatele s nonce 0-5: odesílatel poslal pořadí 2,4,0,3,5,1
            # a příjemce z toho v prvním kole přijal jen nonce 0 a 1. Úplná
            # synchronizace trvala tři kola místo jednoho; při mempoolu nad
            # MAX_MEMPOOL_RESPONSE_TX (kde se kurzor posouvá místo rušení) se
            # vynechaná transakce nabídne až po celém otočení okna, což při
            # plném mempoolu vychází na ~34 kol, tedy ~5,6 minuty na jediný
            # krok posloupnosti.
            #
            # Je to tentýž failure mode, který kód řeší na třech jiných místech
            # týmž klíčem - recycle_orphan_transactions(), replace_chain()
            # a ZMĚNA 3 v revalidate_stored_mempool(), jejíž komentář to říká
            # doslova. Síťová cesta byla jediná, kde řazení chybělo.
            #
            # get_next_nonce() nepotvrzené nonce zohledňuje (přeskakuje ty už
            # ležící v mempoolu), takže po vložení nonce N vrátí N+1 a celá
            # souvislá posloupnost projde v JEDNOM kole.
            prichozi = []
            for tx_data in tx_data_list:
                try:
                    prichozi.append(Transaction.from_dict(tx_data))
                except ValueError as e:
                    self.add_log(f"{Fore.RED}Neplatná transakce v mempoolu od {ip_port}: {zkrat(e)}{Style.RESET_ALL}")
                    continue
            prichozi.sort(key=lambda x: (x.from_address, x.nonce))

            pridano = 0
            for tx in prichozi:
                if tx.tx_id in self.blockchain.mempool_by_txid:
                    continue
                tx_nonce = self.blockchain.get_next_nonce(tx.from_address)
                if tx.nonce == tx_nonce and self.blockchain.add_transaction(tx):
                    pridano += 1
                    self.add_log(f"{Fore.GREEN}Přidána nová transakce z mempoolu od uzlu: {tx.tx_id}{Style.RESET_ALL}")
                else:
                    self.add_log(f"{Fore.RED}Transakce z mempoolu zamítnuta (neplatná nonce nebo jiná chyba): {tx.tx_id}{Style.RESET_ALL}")
            if pridano:
                save_mempool(self.blockchain.unconfirmed_transactions)
            
        elif msg_type == 'new_peer':
            new_peer_addr = tuple(message['data'])
            try:
                ip = ipaddress.ip_address(new_peer_addr[0])
                is_allowed_ip = not (ip.is_loopback or ip.is_private or ip.is_multicast or ip.is_reserved or ip.is_unspecified)
            except ValueError:
                is_allowed_ip = False
                
            if is_allowed_ip:
                # OPRAVA F-01: tady se dřív volala is_peer_valid(), která si
                # peers_lock bere ZNOVU. peers_lock je threading.Lock (r. 4182),
                # tedy nereentrantní, takže handler zamrzl s drženým zámkem -
                # a protože resolve_peer_addr() potřebuje tentýž zámek pro
                # KAŽDOU příchozí zprávu, zamrzla s ním celá P2P vrstva
                # (příjem, handshake, periodický sync i vypnutí). Spouštěč byla
                # jediná zpráva 'new_peer' od kohokoli po handshaku, nevratně
                # bez restartu uzlu.
                # Uvnitř drženého zámku se proto volá přímo _can_admit_locked().
                with self.peers_lock:
                    should_connect = (new_peer_addr not in self.peers
                                      and new_peer_addr != (self.host, self.port)
                                      and self._can_admit_locked(new_peer_addr)[0])
                if should_connect:
                    # OPRAVA N-10: každá zpráva new_peer dřív OKAMŽITĚ spustila
                    # odchozí spojení na IP:port podle odesílatele. Neúspěšné
                    # spojení se do tabulky nezapíše, takže šlo opakovat bez
                    # konce - uzel sloužil jako skener portů / reflektor
                    # handshaků (test t_bug10_new_peer.py: 60 zpráv = 60 pokusů).
                    # Objevování peerů nespěchá: globální rozpočet 5 pokusů
                    # najednou a pak 1 za 30 s.
                    with self.rate_lock:
                        povoleno = self._take_token(
                            self.__dict__.setdefault('new_peer_bucket', {}), '*',
                            NEW_PEER_CONNECT_CAPACITY, NEW_PEER_CONNECT_REFILL_PER_SECOND, time.time())
                    if povoleno:
                        self.connect_to_peer(new_peer_addr)
                    else:
                        self.add_log(f"{Fore.YELLOW}Zpráva 'new_peer' od {ip_port}: vyčerpán rozpočet na nová spojení, {new_peer_addr[0]} se nezkouší.{Style.RESET_ALL}")
                        return False
            else:
                self.add_log(f"{Fore.YELLOW}Zpráva 'new_peer' ignorována: Adresa {new_peer_addr[0]} není povolená veřejná IP.{Style.RESET_ALL}")
                
        elif msg_type == 'handshake':
            remote_protocol_version = message.get('protocol_version')
            remote_software_version = message.get('software_version', 'neznámá')
            remote_chain_id = message.get('chain_id')
            remote_node_id = message.get('node_id')

            # OPRAVA N6 (audit 10. 10. 2026, nález N6): node_id se netypovalo
            # ani neomezovalo délkou, přestože z něj o pár řádků níž vzniká
            # KLÍČ do slovníku ((ip, node_id) po OPRAVĚ U-20). dict a list tam
            # vyhodily TypeError: unhashable type, který spolkl až catch-all
            # v handle_message() - selhání bezpečným směrem, ale přesně ta
            # třída nálezu, kterou OPRAVA S-7 odstranila u 'request_id'
            # kontrolou isinstance. Délku neomezovalo nic: uložil se klíč
            # o 200 000 znacích a stropy branky důvěry (4 na IP, 80 celkem)
            # ho držely jen co do POČTU, ne velikosti.
            #
            # Vadná hodnota se bere jako CHYBĚJÍCÍ, ne jako důvod k odmítnutí
            # handshaku: node_id je nepovinné (uzel bez něj se umí představit
            # taky) a chová se pak přesně jako dřív - dostane provizorní klíč
            # odvozený od portu (_provisional_node_id). Žádný legitimní uzel se
            # tím neomezuje, protože vlastní node_id má 16 znaků.
            if remote_node_id is not None and not (
                    isinstance(remote_node_id, str) and 0 < len(remote_node_id) <= MAX_NODE_ID_LEN):
                self.add_log(
                    f"{Fore.YELLOW}Handshake od {ip_port} má neplatné node_id "
                    f"({type(remote_node_id).__name__}, "
                    f"{len(remote_node_id) if isinstance(remote_node_id, str) else '?'} znaků). "
                    f"Pokračuji, jako by chybělo.{Style.RESET_ALL}")
                remote_node_id = None

            if remote_node_id and remote_node_id == getattr(self, 'node_id', None):
                self.add_log(f"{Fore.YELLOW}Varování: Detekováno připojení k sobě samému (shoda Node ID)! Spojení zahozeno.{Style.RESET_ALL}")
                if addr:
                    normalized_ip = self.normalize_ip(addr[0])
                    remote_listen_port = message.get('listen_port')
                    if remote_listen_port:
                        # OPRAVA T-4 (Nález 1): self.peers je nově vždy kanonická,
                        # takže i klíč pro odstranění musí být kanonický - jinak
                        # by tenhle úklid po detekci spojení k sobě samému
                        # neodstranil nic.
                        peer_to_remove = (normalized_ip, remote_listen_port)
                        with self.peers_lock:
                            if peer_to_remove in self.peers:
                                self.peers.remove(peer_to_remove)
                            # OPRAVA U-20 (nález 2): maže se záznam TOHOTO uzlu
                            # (tedy nás samých, viděných zvenčí), ne všechno, co
                            # má jeho IP. Pop podle samotné IP by na adrese, kde
                            # kromě nás běží i cizí uzel, vyhodil z branky důvěry
                            # i jeho - a ten za naši chybu ve směrování nemůže.
                            self._forget_listen_port_locked(normalized_ip, remote_listen_port)
                            # OPRAVA D-08: se záznamem musí zmizet i doprovodná
                            # evidence, jinak zůstane osiřelé skóre.
                            if remote_node_id:
                                self.peer_listen_ports.pop((normalized_ip, remote_node_id), None)
                                self.peer_listen_seen.pop((normalized_ip, remote_node_id), None)
                            self.peer_last_seen.pop(peer_to_remove, None)
                            self.protected_peers.discard(peer_to_remove)
                        # OPRAVA AUDIT-2026-8 (nález N3): dávkovaný zápis. Snímek se už
                        # nebere tady - flush_peers() si ho pořídí sám v okamžiku
                        # zápisu, takže na disk jde aktuální tabulka, ne ta, jak
                        # vypadala při označení.
                        self.mark_peers_dirty()
                return
                
            if remote_chain_id != CHAIN_ID:
                if addr:
                    self.ban_peer(addr[0], f"handshake: cizí chain_id {remote_chain_id}", BAN_DURATION_PROTOCOL)
                self.add_log(f"{Fore.RED}Handshake selhal od uzlu {ip_port}: nesprávné chain_id {zkrat(remote_chain_id, 32)} (očekáváno {CHAIN_ID}). Uzel blacklistován.{Style.RESET_ALL}")
            elif remote_protocol_version != PROTOCOL_VERSION:
                if addr:
                    self.ban_peer(addr[0], f"handshake: nekompatibilní protocol_version {remote_protocol_version}", BAN_DURATION_PROTOCOL)
                self.add_log(f"{Fore.RED}Handshake selhal od uzlu {ip_port}: nekompatibilní protocol_version {zkrat(remote_protocol_version, 32)} (očekáváno {PROTOCOL_VERSION}). Uzel blacklistován.{Style.RESET_ALL}")
            else:
                self.add_log(f"{Fore.GREEN}Handshake úspěšný od uzlu {ip_port}: software_version={zkrat(remote_software_version, 32)}, protocol_version={zkrat(remote_protocol_version, 32)}, chain_id={zkrat(remote_chain_id, 32)}.{Style.RESET_ALL}")
                remote_listen_port = message.get('listen_port')
                # OPRAVA X-5: isinstance(True, int) je v Pythonu True, takže
                # listen_port: true brankou prošel a do evidence se zapsal
                # port True. Dopad byl minimální ((ip, True) == (ip, 1) i se
                # shodným hashem, takže se žádná evidence nerozešla a po
                # restartu by položku zahodil filtr tvaru v load_data), ale
                # jinde se bool vylučuje důsledně - _check_uint, _valid_block_dict,
                # handler new_peer i request_blocks. Tohle byl jediný výskyt,
                # kde kontrola chyběla.
                if (addr and isinstance(remote_listen_port, int)
                        and not isinstance(remote_listen_port, bool)
                        and 0 < remote_listen_port <= 65535):
                    normalized_ip = self.normalize_ip(addr[0])
                    # OPRAVA U-20 (nález 2): PŘED zápisem si zapamatujeme, na
                    # kterém portu tenhle uzel (podle node_id) naslouchal dosud.
                    # Právě tím se o kus níž odliší "tentýž uzel změnil port"
                    # od "jiný uzel na téže IP" - rozdíl, který dřív nikdo
                    # nedělal a kvůli kterému první uzel z tabulky mizel.
                    # touch_listen_port() ten údaj vzápětí přepíše, takže se
                    # musí přečíst teď.
                    predchozi_port = None
                    if remote_node_id:
                        with self.peers_lock:
                            predchozi_port = self.peer_listen_ports.get((normalized_ip, remote_node_id))
                    # OPRAVA D-08: zápis do branky důvěry jde přes
                    # touch_listen_port(), který drží TTL i strop. Dřív to byl
                    # holý zápis do slovníku, který nikdy nikdo nečistil.
                    self.touch_listen_port(addr[0], remote_listen_port, remote_node_id)
                    # OPRAVA T-4 (Nález 1): do tabulky jde kanonický tvar.
                    # Z accept() sice kanonický už přijde, ale invariant drží
                    # tabulka, ne náhodná vlastnost zdroje dat.
                    new_peer_addr = (normalized_ip, remote_listen_port)
                    
                    try:
                        ip_obj = ipaddress.ip_address(addr[0])
                        is_allowed_ip = not (ip_obj.is_loopback or ip_obj.is_private or ip_obj.is_multicast or ip_obj.is_reserved or ip_obj.is_unspecified)
                    except ValueError:
                        is_allowed_ip = False
                        
                    if is_allowed_ip and new_peer_addr != (self.host, self.port):
                        changed = False
                        with self.peers_lock:
                            # OPRAVA U-20 (audit 7. 10. 2026, nález 2): dřív se
                            # hledalo podle SAMOTNÉ IP a první nalezený záznam se
                            # přepsal. Komentář u OPRAVY T-4 to říkal otevřeně -
                            # "je to tentýž uzel, jen jiný naslouchací port" -
                            # jenže to je pravda jen tehdy, když to opravdu tentýž
                            # uzel je. Při dvou uzlech na jedné adrese (dva uzly na
                            # jednom VPS, dvě instance za jedním NATem) druhý
                            # handshake první uzel z tabulky ODSTRANIL a od té
                            # chvíle o něm uzel nevěděl.
                            #
                            # Identitu nese node_id, ne adresa. Pořadí rozhodování:
                            #   1. přesná shoda adresy  -> jen obnovit skóre,
                            #   2. shoda node_id na jiném portu -> tentýž uzel se
                            #      přestěhoval, záznam nahradit,
                            #   3. bez node_id (uzel, který ho neposílá) -> padá se
                            #      zpět na původní chování podle IP,
                            #   4. jinak je to CIZÍ uzel na téže IP -> přidat vedle.
                            old_peer = None
                            if new_peer_addr in self.peers:
                                old_peer = new_peer_addr
                                # OPRAVA D-08: úspěšný handshake je důkaz, že
                                # peer žije - tím se obnovuje jeho skóre.
                                self.peer_last_seen[old_peer] = get_time()
                            elif remote_node_id and predchozi_port is not None \
                                    and (normalized_ip, predchozi_port) in self.peers:
                                old_peer = (normalized_ip, predchozi_port)
                            elif not remote_node_id:
                                # OPRAVA T-4 (Nález 1): porovnání bylo textové
                                # proti syrovému addr[0]. U peera zapsaného
                                # rozepsaně se shoda nenašla, větev "změnil se
                                # naslouchací port" se neuplatnila a místo
                                # aktualizace vznikl další záznam o témže uzlu.
                                for p in self.peers:
                                    if self.normalize_ip(p[0]) == normalized_ip:
                                        old_peer = p
                                        break

                            if old_peer is not None and old_peer != new_peer_addr:
                                self.peers.remove(old_peer)
                                self.peers.append(new_peer_addr)
                                # Skóre i ochrana se přenášejí na nový záznam -
                                # je to tentýž uzel, jen jiný naslouchací port.
                                self.peer_last_seen.pop(old_peer, None)
                                self.peer_last_seen[new_peer_addr] = get_time()
                                if old_peer in self.protected_peers:
                                    self.protected_peers.discard(old_peer)
                                    self.protected_peers.add(new_peer_addr)
                                # Se starou adresou musí zmizet i její záznam
                                # v evidenci naslouchacích portů, jinak by na uzel
                                # zůstaly ukazovat dva porty a směrování by zase
                                # nebylo jednoznačné.
                                self._forget_listen_port_locked(normalized_ip, old_peer[1])
                                changed = True

                        # OPRAVA AUDIT-2026-7 (audit 21. 10. 2026, nález N2): odliší se
                        # "do tabulky přibyl NOVÝ uzel" od "známý uzel změnil
                        # port". Jen to první se ohlašuje dál (viz níž).
                        novy_peer = False
                        if not old_peer:
                            # OPRAVA D-08: přijetí nově umí vytlačit nejhorší
                            # zavedený peer místo toho, aby nový uzel odmítlo.
                            # Dřív se po zaplnění tabulky do sítě nedostal žádný
                            # poctivý uzel a stav byl trvalý (eclipse).
                            if self.try_admit_peer(new_peer_addr):
                                changed = True
                                novy_peer = True
                            else:
                                self.add_log(f"{Fore.YELLOW}Uzel {ip_port} nepřijat do tabulky peerů (limit podsítě nebo plná tabulka zdravých peerů).{Style.RESET_ALL}")

                        if changed:
                            # OPRAVA AUDIT-2026-8 (nález N3): místo save_peers() na každou
                            # zprávu se změna jen označí; na disk ji odnese
                            # flush_peers() z periodického kola.
                            self.mark_peers_dirty()
                            self.add_log(f"{Fore.GREEN}Uzel {ip_port} (naslouchá na portu {remote_listen_port}) byl aktualizován/přidán do peers.{Style.RESET_ALL}")

                        if novy_peer:
                            self.ohlas_noveho_peera(new_peer_addr)

    def connect_to_peer(self, peer_addr, manual=False):
        # OPRAVA D-08: manual=True označuje peera zadaného UŽIVATELEM (volba
        # v menu, peers.json). Takový uzel se zapíše mezi chráněné - nikdy ho
        # automaticky nevytlačí síťový provoz a nevztahuje se na něj limit
        # podsítě, protože je to výslovné rozhodnutí uživatele. Právě tím se
        # dá uzel zachránit z eclipse.
        #
        # OPRAVA T-4 (Nález 1): normalizace hned na vstupu. Tudy vede jediná
        # cesta, kudy se do self.peers dostane adresa pocházející od UŽIVATELE
        # (volba 16) nebo od cizího uzlu (zpráva 'new_peer'); obě můžou přijít
        # v libovolném textovém tvaru. Dál v metodě se peer_addr používá jako
        # klíč do peers, protected_peers i peer_last_seen, takže se musí
        # kanonizovat dřív než první z nich.
        peer_addr = (self.normalize_ip(peer_addr[0]), peer_addr[1])
        if self.is_blacklisted(peer_addr):
            self.add_log(f"{Fore.YELLOW}Spojení zrušeno: Uzel {peer_addr[0]} je na blacklistu.{Style.RESET_ALL}")
            return False
            
        with self.peers_lock:
            already_peer = peer_addr in self.peers

        # OPRAVA AUDIT-2026-6 (audit 21. 10. 2026, nález N1): handshake odchází i peerovi,
        # kterého UŽ v tabulce máme. Dřív bylo celé tělo metody - včetně jediného
        # místa v souboru, které zprávu 'handshake' odesílá - obalené podmínkou
        # `if not already_peer:`.
        #
        # Jenže main() předává peery z peers.json rovnou do konstruktoru P2PNode,
        # takže v self.peers jsou od první vteřiny a connect_to_peer() se na ně
        # nikdy nezavolá. Handshake proto neodešel a protistrana pak každou naši
        # zprávu odmítla brankou důvěry v handle_message() ("chybí handshake").
        #
        # Důsledek: čerstvá instalace se seed listem se k síti NEPŘIPOJILA VŮBEC.
        # Fungoval jedině uzel přidaný ručně z menu (volba 16, tam je tabulka
        # prázdná) nebo takový, jehož adresu měla protistrana ve vlastním
        # peers.json. Ověřeno dvěma uzly: bootstrap z peers.json skončil na tipu
        # #0, táž dvojice přes volbu 16 stáhla řetězec do vteřiny.
        #
        # Co zůstává za `already_peer`: PŘIJETÍ do tabulky. Peer, který v ní je,
        # se znovu nepřijímá (neplýtvá se slotem ani zápisem na disk) - ale
        # představit se mu musíme, jinak s námi nemluví.
        try:
            addr_info = socket.getaddrinfo(peer_addr[0], peer_addr[1], socket.AF_UNSPEC, socket.SOCK_STREAM)
            family, socktype, proto, _, sockaddr = addr_info[0]
            client_socket = socket.socket(family, socktype, proto)
            client_socket.settimeout(3)
            client_socket.connect(sockaddr)

            local_ip = client_socket.getsockname()[0]
            # OPRAVA T-4 (Nález 4): obě porovnání byla textová. Seznam
            # ['127.0.0.1', 'localhost', '::1', '0.0.0.0'] neobsahoval
            # rozepsaný loopback ('0:0:0:0:0:0:0:1') ani zbytek rozsahu
            # 127.0.0.0/8, takže připojení k sobě samému touhle brankou
            # prošlo. Test přes ipaddress pokrývá všechny tvary najednou;
            # local_ip se normalizuje ze stejného důvodu (peer_addr je po
            # OPRAVĚ T-4 výše už kanonická).
            #
            # OPRAVA N4 (audit 10. 10. 2026, nález N4): porovnává se DVOJICE
            # (IP, port), ne samotná adresa.
            #
            # Uzel na témž stroji má local_ip shodné s cílovou adresou,
            # takže se dva uzly nedaly ručně propojit, i když běžely na
            # různých portech - ověřeno: na portu 45942 běžel JINÝ uzel
            # a connect_to_peer() vrátilo False jak pro jeho LAN adresu,
            # tak pro 127.0.0.1. Přitom OPRAVA U-20 tuhle topologii výslovně
            # podporuje a ruční peering je dokumentovaná záchranná cesta
            # z eclipse útoku (PROTECTED_PEER_SLOTS).
            #
            # "Jsem to já" znamená táž adresa A týž naslouchací port.
            # Spolehlivou detekci kód stejně má jinde - shoda node_id
            # v handleru handshake, která si navíc uklidí tabulku peerů -
            # takže tahle branka má zachytit jen zjevný nesmysl, ne
            # vyloučit celou legitimní topologii.
            if ((self.normalize_ip(local_ip) == peer_addr[0] and peer_addr[1] == self.port)
                    or is_self_target_ip(peer_addr[0])):
                self.add_log(f"{Fore.YELLOW}Spojení zrušeno: Pokus o připojení na vlastní adresu a port ({peer_addr[0]}:{peer_addr[1]}).{Style.RESET_ALL}")
                client_socket.close()
                return False

            # OPRAVA AUDIT-2026-6: zmena_tabulky rozlišuje "tabulka se opravdu změnila"
            # od "jen jsme se znovu představili". Na disk se sahá výhradně
            # v prvním případě (viz OPRAVA AUDIT-2026-8).
            zmena_tabulky = False
            if manual:
                # OPRAVA G-10: při manual=True se _can_admit_locked() nevolal
                # vůbec, takže self.peers i protected_peers mohly růst BEZ
                # JAKÉHOKOLI stropu. Záměr je legitimní (ruční zadání je
                # záchranná cesta z eclipse útoku a nesmí ho zablokovat plná
                # tabulka), ale horní mez chyběla úplně. Nově se rezerva
                # kvantifikuje: ručně smí tabulka přerůst nejvýš o
                # PROTECTED_PEER_SLOTS nad MAX_PEERS.
                #
                # OPRAVA AUDIT-2026-6: větev nově běží i pro peera, který v tabulce už
                # je. Právě tím se dá existující peer POVÝŠIT na chráněného -
                # dosud to nešlo, takže dokumentovaná záchrana z eclipse útoku
                # selhala přesně v situaci, kdy útočník naši adresu do tabulky
                # už protlačil. Strop to neobchází: `peer_addr in self.peers`
                # je v podmínce níž, takže se žádný nový slot nezabírá.
                with self.peers_lock:
                    if peer_addr in self.peers or len(self.peers) < MAX_MANUAL_PEERS_TOTAL:
                        if peer_addr not in self.protected_peers:
                            self.protected_peers.add(peer_addr)
                            zmena_tabulky = True
                        if peer_addr not in self.peers:
                            self.peers.append(peer_addr)
                            zmena_tabulky = True
                        self.peer_last_seen[peer_addr] = get_time()
                        admitted = True
                    else:
                        admitted = False
                if not admitted:
                    self.add_log(
                        f"{Fore.YELLOW}Uzel {peer_addr[0]}:{peer_addr[1]} nelze přidat ručně: "
                        f"tabulka má {MAX_MANUAL_PEERS_TOTAL} peerů, což je strop i pro ruční "
                        f"zadání. Odeberte nejdřív jiný uzel (menu 17).{Style.RESET_ALL}"
                    )
                    client_socket.close()
                    return False
            elif already_peer:
                # Peer v tabulce je - slot se nepřijímá znovu, jen se
                # potvrdí, že žije.
                admitted = True
                with self.peers_lock:
                    self.peer_last_seen[peer_addr] = get_time()
            else:
                admitted = self.try_admit_peer(peer_addr)
                zmena_tabulky = admitted

            if not admitted:
                self.add_log(f"{Fore.YELLOW}Uzel {peer_addr[0]}:{peer_addr[1]} nepřijat do tabulky peerů (limit podsítě nebo plná tabulka).{Style.RESET_ALL}")
                client_socket.close()
                return False

            self.touch_listen_port(peer_addr[0], peer_addr[1])

            # OPRAVA AUDIT-2026-15 (nález 5), druhá polovina: i ÚSPĚŠNÁ cesta
            # spamovala, jen do logu místo do menu. Hláška "Obnoveno spojení
            # s uzlem ... (odeslán handshake)" se psala při každém průchodu, a
            # ten nastává každých 10 s pro peera, kterému značka handshake_sent
            # padá dokola - tedy u uzlu, který TCP spojení přijme, ale na
            # aplikační dotaz neodpoví (_sync_with_peer_inner značku při tichu
            # zahodí, viz OPRAVA AUDIT-2026-6). Potlačení v add_log() na to
            # nedosáhne, protože se hlášky v logu střídají s "Synchronizuji
            # blockchain a mempool..." z téhož kola.
            #
            # Přijetí NOVÉHO peera do tabulky je jednorázová událost, takže se
            # hlásí vždy. Opakovaný handshake známému peerovi je rutina a hlásí
            # se jen tehdy, když jde o přechod z offline (tj. peer se vrátil).
            if not already_peer:
                self.add_log(f"{Fore.GREEN}Úspěšně připojeno k uzlu {peer_addr}{Style.RESET_ALL}")
            self._oznac_peer_online(peer_addr)

            # OPRAVA #1: dřív tohle spálilo 4 spojení naráz (testovací
            # connect výše + tři samostatné send_to_peer), tedy 40 %
            # původního rozpočtu při jediném připojení. Handshake i oba
            # dotazy teď jdou po JEDNOM socketu - tom, který už máme
            # otevřený a jehož úspěšné navázání bylo celým smyslem testu.
            try:
                # OPRAVA F-04: request_mempool odchází i tudy, takže i tady
                # se musí otevřít branka pro odpověď.
                self.expect_mempool_from(peer_addr)
                client_socket.sendall(b''.join(self._frame(m) for m in [
                    {'type': 'handshake', 'protocol_version': PROTOCOL_VERSION, 'software_version': SOFTWARE_VERSION,
                     'chain_id': CHAIN_ID, 'listen_port': self.port, 'node_id': getattr(self, 'node_id', 'unknown')},
                    {'type': 'request_chain_info'},
                    {'type': 'request_mempool'},
                ]))
            finally:
                client_socket.close()

            # OPRAVA AUDIT-2026-6 (nález N1): poznamenáme si, že tenhle peer už
            # od nás handshake dostal. Periodická synchronizace se podle toho
            # rozhoduje, jestli se má představit, nebo rovnou ptát; značka se
            # zahodí, jakmile peer přestane odpovídat (viz _sync_with_peer_inner).
            #
            # OPRAVA AUDIT-2026-15 (nález 2): pod peers_lock. Mapu prochází
            # _uklid_evidence_peeru_locked() pod tímtéž zámkem, takže zápis
            # z tohohle vlákna mu měnil slovník pod rukama (naměřeno 57x
            # RuntimeError "dictionary changed size during iteration").
            with self.peers_lock:
                self.handshake_sent[peer_addr] = get_time()

            # OPRAVA AUDIT-2026-8: zápis se jen označí, na disk ho odnese
            # flush_peers() z periodického kola. Bez téhle podmínky by
            # OPRAVA AUDIT-2026-6 zápis na flash naopak ZESÍLILA - uzel vytáčí
            # peery z peers.json opakovaně a tabulka se přitom nemění.
            if zmena_tabulky:
                self.mark_peers_dirty()
            return True
        except Exception as e:
            # OPRAVA AUDIT-2026-15 (audit 27. 10. 2026, nález 5): dvě původní
            # větve (ConnectionRefusedError a catch-all) psaly obě přes print(),
            # tedy do MENU. Tahle metoda ale není jen obsluha volby 16 - volá ji
            # i _sync_with_peer_inner() pro každého peera bez značky
            # handshake_sent, tedy každých 10 s. Při selhání se značka
            # nenastaví, takže příští kolo zkusilo totéž a vypsalo totéž:
            # nedostupný peer v peers.json zahlcoval menu hláškou
            # "Chyba při připojování: timed out" donekonečna a uživatel u toho
            # nemohl pracovat.
            #
            # Správné místo je P2P log, a i tam jen PŘECHOD stavu - jednou při
            # odpojení, jednou při opětovném připojení. Obojí obstará
            # _oznac_peer_offline() / _oznac_peer_online().
            #
            # ConnectionRefusedError je podtřída OSError, takže jedna větev
            # stačí; na konkrétní text se překládá v _duvod_spojeni().
            duvod = self._duvod_spojeni(e)
            if manual:
                # Uživatel stojí u menu a čeká na odpověď, takže konkrétní důvod
                # dostane na konzoli - ale JEN on. Volba 16 k tomu vypisuje svou
                # vlastní hlášku o selhání, tohle je doplnění proč.
                print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Nelze se připojit k uzlu "
                      f"{self._peer_str(peer_addr)} - {duvod}.")
            # Vrací False, pokud o nedostupnosti už víme - pak se nelogovat nic,
            # a to ani u neočekávané výjimky: ta má typ v `duvod` a v logu je
            # od prvního výskytu.
            self._oznac_peer_offline(peer_addr, duvod)
        return False

    # OPRAVA T-4 (Nález 2): connect_to_all_peers() odstraněna - mrtvý kód.
    # Udržování spojení obstarává sync_chain_periodically() a perzistentní
    # spojení ve PeerConnection; hromadné vytáčení celé tabulky najednou by
    # navíc spálilo spojový rozpočet (is_connection_rate_limited) na jeden ráz.

    @staticmethod
    def _frame(data):
        message = json.dumps(data).encode('utf-8')
        return struct.pack('!I', len(message)) + message

    def _send_to_single_peer(self, peer, data):
        # OPRAVA #1: data smí být jedna zpráva NEBO seznam zpráv. Seznam se pošle
        # po jediném TCP spojení - tím se drasticky snižuje počet spojení, které
        # rate limiter na druhé straně vidí.
        if self.is_blacklisted(peer):
            return
        peer_str = f"[{peer[0]}]:{peer[1]}" if ':' in peer[0] else f"{peer[0]}:{peer[1]}"
        messages = data if isinstance(data, list) else [data]

        # ETAPA 1: pokud na peera držíme perzistentní spojení, použijeme ho -
        # ušetří to TCP handshake i token ve spojovém rozpočtu protistrany.
        conn = self.get_connection(peer)
        if conn is not None:
            # OPRAVA AUDIT-16: dřív tu stálo `all(conn.send(m) for m in messages)`.
            # all() nad generátorem zkratuje na první nepravdě, jenže zprávy
            # PŘED ní už odešly - a fallback níž pak poslal CELOU dávku znovu,
            # takže protistrana dostala prvních k-1 zpráv dvakrát. Protokol je
            # vůči duplicitám odolný (`new_block` i `transaction` jsou
            # idempotentní a dávky se de-duplikují v `response_blocks`), takže
            # to nikdy nic nerozbilo - je to ale zbytečný provoz a zbytečná
            # práce pro rate limiter protistrany.
            #
            # Počítá se proto, kolik zpráv spojení potvrdilo, a fallback pošle
            # jen zbytek. Zpráva, na které send() selhal, se posílá ZNOVU:
            # sendall() buď pošle vše, nebo vyhodí, a PeerConnection.send()
            # v takovém případě spojení zavře - protistrana tedy uvidí nanejvýš
            # useknutý rám na konci proudu a rámování ho zahodí. Nedoručená
            # zpráva se tak neztratí.
            odeslano = 0
            for m in messages:
                if not conn.send(m):
                    break
                odeslano += 1
            if odeslano == len(messages):
                # OPRAVA D-08: úspěšné doručení je jediné skóre, kterému se dá
                # věřit - útočník si ho nemůže deklarovat sám. Podle něj se
                # v try_admit_peer() rozhoduje, koho vytlačit.
                self.note_peer_activity(peer)
                # OPRAVA AUDIT-2026-15 (nálezy 2 a 5): přes pomocnou metodu,
                # která evidenci drží pod peers_lock a hlásí jen přechod stavu.
                self._oznac_peer_online(peer)
                return
            messages = messages[odeslano:]

        try:
            addr_info = socket.getaddrinfo(peer[0], peer[1], socket.AF_UNSPEC, socket.SOCK_STREAM)
            family, socktype, proto, _, sockaddr = addr_info[0]
            client_socket = socket.socket(family, socktype, proto)
            client_socket.settimeout(5)
            client_socket.connect(sockaddr)
            
            payload = b''.join(self._frame(m) for m in messages)
            client_socket.sendall(payload)
            client_socket.close()
            
            self.note_peer_activity(peer)
            self._oznac_peer_online(peer)
        except (ConnectionRefusedError, socket.timeout, OSError) as e:
            # OPRAVA AUDIT-2026-4 (audit 8. 10. 2026, nález 4): do offline_peers
            # smí jen peer, který JE v tabulce.
            #
            # Dřív to byl bezpodmínečný add() a množina neměla strop ani TTL -
            # jako jediná evidence v celém uzlu, zatímco p2p_log, blacklist,
            # peer_listen_ports i peers svůj strop mají. Útok byl levný: 400
            # cyklů handshake + request_chain_info BEZ request_id z jediné IP,
            # pokaždé s jiným deklarovaným listen_port. Bez request_id padne
            # _respond() na náhradní cestu, otevře odchozí spojení na deklarovaný
            # port, to selže - a množina vyrostla o 400 položek, zatímco všechny
            # ostatní evidence zůstaly na svých stropech.
            #
            # Množina slouží JEN k tomu, aby se hláška "uzel je offline" nepsala
            # do logu opakovaně. Pro adresu mimo tabulku je to evidence něčeho,
            # co uzel stejně nesleduje. Strop je tím implicitně tentýž jako
            # u self.peers.
            #
            # OPRAVA AUDIT-2026-15 (nálezy 2 a 5): test v tabulce, test přechodu
            # i zápis jsou nově v JEDNÉ kritické sekci uvnitř pomocné metody.
            # Dřív byl pod peers_lock jen `peer in self.peers` a samotná změna
            # množiny proběhla až za zámkem.
            self._oznac_peer_offline(peer, self._duvod_spojeni(e))
        except Exception as e:
            self.add_log(f"{Fore.RED}Neočekávaná chyba u uzlu {peer_str} - {e}{Style.RESET_ALL}")

    def _spawn_send(self, peer, data):
        """OPRAVA N2 (audit 10. 10. 2026, nález N2): jediná cesta, kudy se
        spouští odchozí vlákno, a je shora omezená semaforem.

        Odchozí stranu dosud neomezovalo NIC - MAX_INBOUND_CONNECTIONS platí
        jen pro příchozí. Jedna příchozí zpráva přitom uměla vyrobit právě
        jedno odchozí vlákno a socket na ~10 s (viz MAX_OUTBOUND_SEND_THREADS),
        takže z jediné IP vycházelo ~900 souběžně. Je to táž třída chyby jako
        OPRAVA N-2 u příchozích spojení, jen o patro vedle.

        Přetečení se jen ZAHODÍ: rozesílání i přeposílání (OPRAVA W-2) jsou
        best-effort a cokoli vynechaného doteče nejbližším kolem periodické
        synchronizace. Zahodit zprávu je tedy správná reakce - fronta by jen
        posunula tutéž paměť jinam a u bloku by navíc doručila data, která
        mezitím zastarala.

        Semafor se uvolňuje ve finally: uniklý token by uzel po několika
        selháních sám odřízl od sítě, což je přesně failure mode OPRAVY R-4
        u inbound_total.
        """
        if not self.outbound_semaphore.acquire(blocking=False):
            # add_log potlačuje opakování téže hlášky (viz _p2p_log_last),
            # takže ani při zaplavení z toho nebude tisíc řádků.
            self.add_log(f"{Fore.YELLOW}Odchozí zpráva pro {peer[0]}:{peer[1]} zahozena: "
                         f"vyčerpán strop souběžných odchozích pokusů "
                         f"({MAX_OUTBOUND_SEND_THREADS}).{Style.RESET_ALL}")
            return False

        def _prace():
            try:
                self._send_to_single_peer(peer, data)
            finally:
                self.outbound_semaphore.release()

        thread = threading.Thread(target=_prace)
        thread.daemon = True
        try:
            thread.start()
        except RuntimeError as e:
            # Došly systémové prostředky na vlákno. Token se musí vrátit -
            # jinak by se strop po několika takových selháních trvale snížil.
            self.outbound_semaphore.release()
            self.add_log(f"{Fore.YELLOW}Odchozí zprávu pro {peer[0]}:{peer[1]} se nepodařilo "
                         f"odeslat: vlákno nelze spustit ({e}).{Style.RESET_ALL}")
            return False
        return True

    def send_to_peer(self, peer_addr, data):
        # OPRAVA N2: přes _spawn_send(), tedy pod stropem souběžných vláken.
        self._spawn_send(peer_addr, data)

    def send_data_to_peers(self, data, vynechat_ip=None, vynechat_peer=None):
        # OPRAVA W-2 (audit 9. 10. 2026, nález N-2): vynechat_ip vypustí z
        # rozesílky jednu adresu - toho, od koho data přišla. Posílat blok zpět
        # jeho odesílateli je čistá duplicita: on ho má, jeho add_block() ho
        # odmítne a jen ho to stojí token v rate limiteru.
        #
        # OPRAVA AUDIT-2026-16 (audit 28. 10. 2026, nález 3): přidán PŘESNÝ
        # klíč vynechat_peer, tedy dvojice (IP, naslouchací port).
        #
        # Vynechávalo se výhradně podle IP a komentář to hájil tím, že "nejhorší
        # následek je, že se druhý uzel na téže IP dozví blok o jedno kolo syncu
        # později". To ale podhodnocuje cenu: po OPRAVĚ W-2 je přeposílání
        # HLAVNÍ cesta šíření (periodické kolo bylo právě proto shledáno
        # nedostatečným) a _uz_preposlano() si položku poznamená, takže druhé
        # kolo už ji nepřepošle. Dva uzly na jedné adrese - dvě instance na
        # jednom VPS nebo za jedním NATem, tedy přesně topologie, pro kterou se
        # dělala OPRAVA U-20 - si tak navzájem nepřeposlaly nikdy nic a byly
        # odkázané jen na periodický sync.
        #
        # Volající (preposli_sousedum) dodá přesný klíč, kdykoli jde odesílatele
        # jednoznačně určit přes resolve_peer_addr(); když to nejde (víc uzlů na
        # jedné IP a zpráva bez node_id), padá se zpátky na vynechat_ip, protože
        # hádat by znamenalo poslat data zpět jejich odesílateli.
        if vynechat_ip:
            vynechat_ip = self.normalize_ip(vynechat_ip)
        if vynechat_peer:
            vynechat_peer = (self.normalize_ip(vynechat_peer[0]), vynechat_peer[1])
        with self.peers_lock:
            peers_snapshot = [p for p in self.peers
                              if (vynechat_ip is None or self.normalize_ip(p[0]) != vynechat_ip)
                              and (vynechat_peer is None
                                   or (self.normalize_ip(p[0]), p[1]) != vynechat_peer)]
        # OPRAVA N2: i broadcast jde přes _spawn_send(). Právě tahle cesta
        # zesílení násobila - každá přijatá transakce i blok spustily vlákno na
        # každého peera, tedy až MAX_PEERS = 20 vláken naráz.
        for peer in peers_snapshot:
            self._spawn_send(peer, data)

    def _uz_preposlano(self, klic):
        """OPRAVA W-2 (audit 9. 10. 2026, nález N-2): krátkodobá evidence přeposlaného.

        Vrací True, když se položka pod tímhle klíčem už jednou přeposlala.
        Při False si ji zároveň poznamená, takže test i zápis jsou jeden krok -
        dvě vlákna, kterým tentýž blok dorazí současně, ho nerozešlou dvakrát.

        Hlavní ochranu proti smyčkám dělá samotný konsenzus: přeposílá se jen to,
        co add_block() / add_transaction() PŘIJALY, a ty tutéž položku podruhé
        nepřijmou. Tahle evidence je druhá linie pro případy, kdy se blok do
        řetězce dostane znovu (reorg tam a zpět), a hlavně záruka, že se smyčka
        nemůže roztočit ani při budoucí úpravě těch dvou metod.

        Je omezená shora (MAX_RELAY_SEEN_ENTRIES) a vyprazdňuje se FIFO. Deque
        vedle množiny je tu proto, že set sám pořadí nezná a "zahoď nejstarší"
        by bez něj znamenalo průchod celou množinou - táž úvaha jako
        u MAX_P2P_LOG_ENTRIES.
        """
        with self.relay_lock:
            if klic in self.relay_seen:
                return True
            self.relay_seen.add(klic)
            self.relay_order.append(klic)
            while len(self.relay_order) > MAX_RELAY_SEEN_ENTRIES:
                self.relay_seen.discard(self.relay_order.popleft())
            return False

    def preposli_sousedum(self, zprava, klic, addr, src_node_id=None):
        """OPRAVA W-2 (audit 9. 10. 2026, nález N-2): lavinové šíření (gossip relay).

        Uzel dosud přeposílal VÝHRADNĚ to, co sám vyrobil: mine() svůj blok
        a menu svou transakci. Přijatý blok se zapsal do řetězce a tím to
        skončilo, takže za první skok se data dostala jedině periodickým
        dotazem ze sync_chain_periodically(), tedy jednou za 10 s. Doba šíření
        bloku pak rostla lineárně s průměrem sítě - při 4 až 6 skocích 20 až
        60 s, což je 33 až 100 % BLOCK_TIME_SECONDS. Následek: vysoká míra
        osiřelých bloků, trvalé forky, promrhaný hashrate a systematická výhoda
        pro těžaře blíž zdroji bloku.

        Posílá se všem peerům kromě odesílatele, a jen jednou (viz
        _uz_preposlano). Volá se AŽ PO úspěšném přijetí do řetězce / mempoolu,
        takže se nikdy nešíří nic, co jsme sami nepřijali za platné.

        OPRAVA AUDIT-2026-16 (audit 28. 10. 2026, nález 3): odesílatel se
        vynechává PŘESNĚ, tedy podle dvojice (IP, naslouchací port), kdykoli ho
        resolve_peer_addr() umí jednoznačně určit - což u zprávy s node_id platí
        i tehdy, když je na té IP uzlů víc. Teprve když ho určit nelze, padá se
        na vynechání celé IP. Zdůvodnění je u send_data_to_peers().
        """
        if self._uz_preposlano(klic):
            return False
        # Stamp vlastní identity: příjemce z něj dohledá, od KOHO zpráva je,
        # i když dorazila jednorázovým socketem bez handshaku. Viz odůvodnění
        # u fallbacku v _handle_message_inner(). Nepřepisuje se, pokud už
        # zpráva node_id nese (handshake si ho plní sám).
        if isinstance(zprava, dict):
            vlastni_id = getattr(self, 'node_id', None)
            if isinstance(vlastni_id, str) and 0 < len(vlastni_id) <= MAX_NODE_ID_LEN:
                zprava.setdefault('node_id', vlastni_id)
        odesilatel = self.resolve_peer_addr(addr, src_node_id) if addr else None
        if odesilatel is not None:
            self.send_data_to_peers(zprava, vynechat_peer=odesilatel)
        else:
            self.send_data_to_peers(zprava, vynechat_ip=addr[0] if addr else None)
        return True

    def ohlas_noveho_peera(self, novy_peer):
        """OPRAVA AUDIT-2026-7 (audit 21. 10. 2026, nález N2): odesílací strana zprávy
        'new_peer'.

        Typ 'new_peer' měl dosud jen PŘIJÍMACÍ stranu, a to kompletní a
        udržovanou - handler, tvarovou branku _DATA_SHAPE['new_peer'] i vlastní
        rozpočet odchozích pokusů (NEW_PEER_CONNECT_CAPACITY z OPRAVY N-10).
        Jenže hledání `'type': 'new_peer'` v celém souboru nevrátilo jediný
        výskyt: zprávu nikdo neodesílal. Objevování peerů tedy neexistovalo a
        uzel se o cizí adrese dozvěděl jedině z peers.json nebo z handshaku,
        který mu někdo poslal sám. Topologie se proto nikdy nerozrostla nad to,
        co uživatelé zadali ručně.

        Ohlašuje se VÝHRADNĚ uzel, který právě nově vstoupil do naší tabulky
        (ne přestěhovaný známý uzel - ten má adresu, kterou sousedé už znají),
        a každá adresa nejvýš jednou: evidence _uz_preposlano() je táž, jakou
        pro bloky a transakce zavedla OPRAVA W-2, takže cyklus add/evict/add
        nemůže rozhoupat lavinu. Samotnému novému peerovi se jeho adresa
        neposílá - vynechat_ip.

        Zesílení je tím shora omezené na jednu zprávu na peera a adresu,
        odeslanou přes _spawn_send(), tedy pod semaforem MAX_OUTBOUND_SEND_THREADS.
        """
        if not self.running:
            return False
        zprava = {'type': 'new_peer', 'data': [novy_peer[0], novy_peer[1]]}
        return self.preposli_sousedum(zprava, ('peer', novy_peer[0], novy_peer[1]),
                                      (novy_peer[0], novy_peer[1]))

    def sync_chain_periodically(self):
        while self.running:
            time.sleep(10)
            try:
                self._sync_chain_periodically_kolo()
            except Exception as e:
                # OPRAVA R-3: tělo smyčky nemělo žádné ošetření, takže JEDINÁ
                # výjimka (typicky RuntimeError "can't start new thread"
                # z threading.Thread.start() níž) vlákno natrvalo ukončila.
                # Uzel běžel dál a tvářil se zdravě, ale ztratil periodický
                # sync, cleanup_mempool(), úklid blacklistu i watchdog fork
                # syncu - a zaseknutý syncing_fork=True už nikdo neuvolnil,
                # takže se uzel přestal synchronizovat úplně.
                # start_server() tentýž ochranný blok uvnitř své smyčky má;
                # tady chyběl.
                self.add_log(f"{Fore.RED}Chyba v periodické synchronizaci ({type(e).__name__}: {e}). Pokračuji dalším kolem.{Style.RESET_ALL}")

    def _sync_chain_periodically_kolo(self):
        # OPRAVA U-19 (audit 7. 10. 2026, nález 1): celý přechod watchdogu je pod
        # fork_lock - test timeoutu, vynulování příznaků, přečtení špičky bufferu
        # i jeho případné zahození. Bez zámku mohl handler response_blocks mezi
        # vynulováním a opětovným nastavením příznaku založit nový fork, který mu
        # tenhle kód vzápětí přepsal (nebo rovnou smazal buffer ve větvi "prázdný
        # buffer nemá cenu držet").
        with self.fork_lock:
            self._watchdog_fork_syncu()

        self.blockchain.cleanup_mempool()
        self._zbytek_periodickeho_kola()

    def _watchdog_fork_syncu(self):
        # OPRAVA U-19 (nález 1): vytaženo z _sync_chain_periodically_kolo(), aby
        # bylo na první pohled vidět, kam až sahá kritická sekce. Volá se VÝHRADNĚ
        # s drženým fork_lock.
        #
        # OPRAVA #6c: watchdog na NEČINNOST, ne na celkovou dobu. fork_sync_start
        # se obnovuje při každém úspěšném zápisu do bufferu (_store_fork_batch),
        # takže tenhle timeout hlídá jen to, že protistrana přestala odpovídat.
        #
        # Buffer se při timeoutu NEMAŽE. Původní kód ho smazal a init_sync_buffer()
        # navíc dělal DROP TABLE, takže další pokus začínal od stejného
        # fork_start_index s prázdným bufferem - nulový přenesený pokrok a nad
        # hraničním RTT se hluboký reorg nedotáhl nikdy, ať se opakoval kolikrát
        # chtěl. Nově se rovnou pošle žádost navazující na špičku bufferu.
        if getattr(self, 'syncing_fork', False):
            if time.time() - getattr(self, 'fork_sync_start', 0) > FORK_SYNC_IDLE_TIMEOUT:
                self.add_log(f"{Fore.YELLOW}Fork sync {FORK_SYNC_IDLE_TIMEOUT}s bez pokroku. Buffer ponechávám a zkusím navázat.{Style.RESET_ALL}")
                self.syncing_fork = False
                self.fork_sync_start = 0
                # OPRAVA N3 (audit 10. 10. 2026, nález N3): uzel, který slot
                # zabral a pak přestal dodávat, se o něj chvíli nesmí ucházet
                # znovu. Přesně tohle je útočníkův vzorec: zabrat slot jedním
                # přehrávaným blokem, mlčet, nechat watchdog vypršet a zabrat
                # znovu dřív, než se poctivý peer stihne ozvat.
                #
                # Netýká se to POKRAČOVÁNÍ rozpracovaného bufferu
                # (_resume_fork_sync níž ani větev `resuming` v handleru), takže
                # poctivý peer, kterému jednou vypadla linka, o dodávání
                # nepřijde - a běžná synchronizace bloků se neomezuje vůbec.
                self._zapis_fork_slot_cooldown(self.fork_peer_ip)
                self.fork_peer_ip = None
                tip = self.sync_buffer_tip()
                if tip:
                    # ETAPA 3: dřív tu byl BROADCAST všem uzlům. Odpovědělo
                    # jich víc, první posunula špičku bufferu a druhá už na ni
                    # nenavazovala - a poctivý uzel schytal 24hodinový ban.
                    # Obnovení proto vede řízený dialog s JEDNÍM uzlem.
                    # OPRAVA U-10 (audit 5. 10. 2026, nález 5): `or` bere nulu
                    # jako nepravdu, takže pro fork_start_index == 0 se vyhodnotil
                    # druhý operand a v logu se objevilo "1 blok" místo skutečného
                    # počtu. Nula je dosažitelná: fork_start_index se nastavuje na
                    # first_block_index dávky a větev "neznámý rodič" se pro
                    # first_block_index == 0 přeskakuje. Dopad je čistě kosmetický,
                    # ale je to tentýž vzorec, který OPRAVA F-13 odstraňovala
                    # u timestampů.
                    _fork_start = self.fork_start_index if self.fork_start_index is not None else tip[0]
                    self.add_log(f"{Fore.CYAN}V bufferu je {tip[0] - _fork_start + 1} bloků (do #{tip[0]}), obnovuji stahování.{Style.RESET_ALL}")
                    with self.peers_lock:
                        kandidati = list(self.peers)
                    if kandidati:
                        # OPRAVA D-17: příznak se zvedá JEŠTĚ PŘED startem
                        # vlákna. Tahle iterace watchdogu totiž o pár řádků
                        # níž testuje `not syncing_fork` a rozjela by
                        # souběžně i běžný sync se všemi uzly - dva locatory
                        # od dvou různých vrcholů naráz. _resume_fork_sync()
                        # si obojí hned nastaví znovu (a v finally uklidí),
                        # tohle jen zavírá okno mezi vynulováním výše
                        # a rozběhnutím vlákna.
                        self.syncing_fork = True
                        self.fork_sync_start = time.time()
                        t = threading.Thread(target=self._resume_fork_sync, args=(kandidati,))
                        t.daemon = True
                        t.start()
                else:
                    # Prázdný buffer nemá cenu držet.
                    self.fork_start_index = None
                    self.discard_sync_buffer()

    def _zbytek_periodickeho_kola(self):
        # OPRAVA G-06: úklid blacklistu jede ve stejném rytmu jako úklid
        # mempoolu. Obojí jsou struktury, které rostou z přijatých dat.
        # Vlastní perioda (BLACKLIST_PRUNE_INTERVAL) uvnitř metody hlídá,
        # aby se slovník neprocházel zbytečně každých 10 s.
        self.prune_blacklist()
        self.flush_blacklist()
        # OPRAVA AUDIT-2026-8 (nález N3): tabulka peerů se na disk zapisuje ve stejném
        # rytmu a ze stejného důvodu jako blacklist. Vlastní perioda
        # (PEERS_FLUSH_INTERVAL) uvnitř metody hlídá, aby se nezapisovalo
        # každých 10 s, když se tabulka nehnula.
        self.flush_peers()
        # OPRAVA K-2: kbelíky rychlostních limitů jsou
        # taktéž struktury, které rostou z přijatých dat, takže patří do
        # stejného úklidového kola. Vlastní perioda
        # (RATE_BUCKET_PRUNE_INTERVAL) uvnitř metody hlídá, aby se slovníky
        # neprocházely zbytečně každých 10 s.
        self.prune_rate_buckets()
        # OPRAVA AUDIT-2026-13 (audit 25. 10. 2026, nález 3): orphan pool patří
        # do stejného úklidového kola jako mempool, blacklist a kbelíky - je to
        # taky struktura, která roste z přijatých dat.
        #
        # Dřív měla expire_orphans() v celém souboru jediného volajícího:
        # add_orphan_block(). Záruka ORPHAN_EXPIRATION = 600 s tedy platila jen
        # tak dlouho, dokud chodili další sirotci. Po nárazu, který naplnil
        # 16 MiB poolu, se paměť neuvolnila, dokud nedorazil další sirotek,
        # něco se nevytěsnilo nebo se uzel nerestartoval - útočník, který
        # přestal posílat, držel paměť uzlu libovolně dlouho. Na telefonu, což
        # je cílová platforma, to není zanedbatelné.
        #
        # Volá se POD konsenzuálním zámkem: expire_orphans() si ho nebere sama
        # a mutuje tytéž struktury jako vytěsňovací smyčka v add_orphan_block()
        # (která ho od téže opravy drží taky). Bez toho by tohle volání vedlo
        # na `RuntimeError: dictionary changed size during iteration` v min()
        # nad orphan_pool - ověřeno testem.
        #
        # Průchod je O(velikost poolu), shora omezený MAX_ORPHAN_POOL_BYTES,
        # takže vlastní periodu jako BLACKLIST_PRUNE_INTERVAL nepotřebuje.
        with self.blockchain.lock:
            self.blockchain.expire_orphans()
        with self.peers_lock:
            # OPRAVA AUDIT-2026-4 (nález 4): peer_last_seen a offline_peers se
            # dorovnají k tabulce ve stejném rytmu jako blacklist. Obě mapy jsou
            # malé (shora omezené MAX_MANUAL_PEERS_TOTAL), takže průchod každých
            # 10 s nic nestojí a nepotřebuje vlastní periodu jako
            # BLACKLIST_PRUNE_INTERVAL.
            self._uklid_evidence_peeru_locked()
            has_peers = bool(self.peers)

        # Zamezíme odesílání klasických requestů pokud jsme uprostřed stahování forku
        if has_peers and not getattr(self, 'syncing_fork', False):
            self.add_log(f"{Fore.YELLOW}Synchronizuji blockchain a mempool se sousedními uzly...{Style.RESET_ALL}")
            # ETAPA 1: místo broadcastu a čekání na nevyžádané odpovědi se
            # s každým uzlem vede řízený dialog ve vlastním vlákně.
            with self.peers_lock:
                peers_snapshot = list(self.peers)
            for peer in peers_snapshot:
                t = threading.Thread(target=self.sync_with_peer, args=(peer,))
                t.daemon = True
                t.start()

    def check_peer_connectivity(self, peer, online_peers_list, lock):
        if self.is_blacklisted(peer):
            return
        try:
            addr_info = socket.getaddrinfo(peer[0], peer[1], socket.AF_UNSPEC, socket.SOCK_STREAM)
            family, socktype, proto, _, sockaddr = addr_info[0]
            client_socket = socket.socket(family, socktype, proto)
            client_socket.settimeout(2)
            client_socket.connect(sockaddr)
            client_socket.close()
            # OPRAVA D-08: úspěšná sonda je také důkaz, že peer žije.
            self.note_peer_activity(peer)
            with lock:
                online_peers_list.append(peer)
        except (socket.timeout, ConnectionRefusedError, OSError):
            pass

    def get_online_peers(self):
        online_peers = []
        threads = []
        lock = threading.Lock()
        with self.peers_lock:
            peers_snapshot = list(self.peers)
        for peer in peers_snapshot:
            thread = threading.Thread(target=self.check_peer_connectivity, args=(peer, online_peers, lock))
            thread.daemon = True
            threads.append(thread)
            thread.start()
        for thread in threads:
            thread.join()
        return online_peers

def is_valid_address(address):
    if not isinstance(address, str) or not address.startswith(TICKER):
        return False
    if len(address) != 75:
        return False
    base = address[:-8]
    expected_checksum = hashlib.sha3_256(base.encode()).hexdigest()[:8]
    return address[-8:] == expected_checksum and all(c in '0123456789abcdef' for c in address[3:])

def jen_ascii_cislice(s):
    """OPRAVA U-4 (audit 2. 10. 2026, nález 5): náhrada za str.isdigit().

    str.isdigit() je pravdivé pro celou řadu unicodových číslic, nejen pro
    ASCII - '١٢٣' (arabsko-indické) jím projde a Decimal/int ho pak přijme
    jako 123. Hláška u obou vstupních polí přitom tvrdí "Povolena jsou pouze
    čísla (0-9)" a branka to nevynucovala. Vstup se navíc choval
    nekonzistentně: jedna třída unicodových číslic prošla ('١٢٣'), druhá ne
    ('²' spadlo až na InvalidOperation v Decimal).

    Prázdný řetězec je False, takže ".5" i "5." zůstávají odmítnuté stejně
    jako dřív (''.isdigit() je rovněž False).
    """
    return bool(s) and all(ch in '0123456789' for ch in s)

def show_p2p_log():
    print(f"\n{Fore.YELLOW}--- Log P2P sítě (stiskněte Enter pro návrat) ---{Style.RESET_ALL}")
    # OPRAVA G-05: log je nově kruhový buffer, ne Queue. drain_log() ho
    # atomicky vybere a vyprázdní.
    for line in p2p_node.drain_log():
        print(line)
    input()

def get_mempool_size_bytes(unconfirmed_transactions):
    return sum(tx.get_size() for tx in unconfirmed_transactions)

def print_menu():
    print(f"\n{Fore.YELLOW}--- Menu ---{Style.RESET_ALL}")
    print(f"{Fore.GREEN}01{Style.RESET_ALL} - Zobrazit peněženky a zůstatky")
    print(f"{Fore.GREEN}02{Style.RESET_ALL} - Vytvořit transakci")
    print(f"{Fore.GREEN}03{Style.RESET_ALL} - Zobrazit nepotvrzené transakce")
    print(f"{Fore.GREEN}04{Style.RESET_ALL} - Vytěžit nový blok")
    print(f"{Fore.GREEN}05{Style.RESET_ALL} - Uložené adresy")
    print(f"{Fore.GREEN}06{Style.RESET_ALL} - Vytvořit novou peněženku")
    print(f"{Fore.GREEN}07{Style.RESET_ALL} - Importovat privátní klíč")
    print(f"{Fore.GREEN}08{Style.RESET_ALL} - Exportovat privátní klíč")
    print(f"{Fore.GREEN}09{Style.RESET_ALL} - Smazat peněženku")
    print(f"{Fore.GREEN}10{Style.RESET_ALL} - Zobrazit blockchain")
    print(f"{Fore.GREEN}11{Style.RESET_ALL} - Zobrazit blok")
    print(f"{Fore.GREEN}12{Style.RESET_ALL} - Zobrazit detaily transakce podle TX ID")
    print(f"{Fore.GREEN}13{Style.RESET_ALL} - Zobrazit historii transakcí pro adresu")
    print(f"{Fore.GREEN}14{Style.RESET_ALL} - Zobrazit celkovou nabídku mincí")
    print(f"{Fore.GREEN}15{Style.RESET_ALL} - Zobrazit stav uzlů")
    print(f"{Fore.GREEN}16{Style.RESET_ALL} - Manuálně přidat nový uzel")
    print(f"{Fore.GREEN}17{Style.RESET_ALL} - Smazat uzel")
    print(f"{Fore.GREEN}18{Style.RESET_ALL} - Zablokované IP adresy")
    print(f"{Fore.GREEN}19{Style.RESET_ALL} - Zobrazit log P2P sítě")
    print(f"{Fore.GREEN}20{Style.RESET_ALL} - Ukončit a uložit")

def verify_genesis_address():
    if not is_valid_address(GENESIS_ADDRESS):
        print(f"{Fore.RED}Chyba: Genesis adresa nemá platný formát (musí mít 75 znaků a správný checksum)! Program se ukončuje.{Style.RESET_ALL}")
        sys.exit(1)
    current_hash = hashlib.sha3_256(GENESIS_ADDRESS.encode()).hexdigest()
    if current_hash != GENESIS_ADDRESS_EXPECTED_HASH:
        print(f"{Fore.RED}Chyba: Genesis adresa byla změněna! Program se ukončuje.{Style.RESET_ALL}")
        sys.exit(1)

def verify_genesis_block(chain):
    genesis_block = chain.get_block_from_db(0)
    # OPRAVA #17: get_block_from_db(0) vrací None, pokud blok #0 v databázi není
    # (prázdná nebo useknutá DB). Původní kód na něm rovnou sáhl na .timestamp
    # a spadl na AttributeError místo srozumitelné hlášky.
    if genesis_block is None:
        print(f"{Fore.RED}Chyba: Genesis blok nebyl v databázi nalezen! Program se ukončuje.{Style.RESET_ALL}")
        sys.exit(1)
    if genesis_block.timestamp != GENESIS_TIMESTAMP or genesis_block.hash != GENESIS_BLOCK_EXPECTED_HASH:
        print(f"{Fore.RED}Chyba: Genesis blok byl změněn (timestamp nebo hash nesouhlasí)! Program se ukončuje.{Style.RESET_ALL}")
        sys.exit(1)

def enforce_mobile_environment(allow_any=False):
    # OPRAVA B-5: jako bezpečnostní opatření tahle kontrola nefunguje - obejde
    # se nastavením TERMUX_VERSION v prostředí, takže brání omylu, ne útočníkovi.
    # Zároveň znemožňovala jakékoli CI a regresní testy na běžném stroji.
    # Přepínač --allow-any-platform ji vypne výslovně a hlasitě; volá se
    # z if __name__ == "__main__", ne z main(), aby šel modul importovat
    # a testovat bez sys.exit(1).
    if allow_any:
        print(f"{Fore.YELLOW}Upozornění: kontrola prostředí přeskočena (--allow-any-platform).{Style.RESET_ALL}")
        print(f"{Fore.YELLOW}Uzel běží mimo podporovanou platformu (Termux, ARM/AArch64). Určeno pro testy, ne pro provoz.{Style.RESET_ALL}")
        return
    machine = platform.machine().lower()
    is_arm = 'arm' in machine or 'aarch' in machine
    is_termux = 'TERMUX_VERSION' in os.environ or '/com.termux/' in os.environ.get('PREFIX', '')
    if not (is_arm and is_termux):
        print(f"\n{Fore.RED}======================================================{Style.RESET_ALL}")
        print(f"{Fore.RED} CHYBA: Nepovolené prostředí pro běh uzlu!{Style.RESET_ALL}")
        print(f"{Fore.RED}======================================================{Style.RESET_ALL}")
        print(f"{Fore.YELLOW}Tento projekt je navržen výhradně pro mobilní zařízení.{Style.RESET_ALL}")
        print(f"{Fore.YELLOW}Podporované prostředí: Termux (ARM/AArch64).{Style.RESET_ALL}")
        print(f"\nDetekovaná architektura: {machine}")
        print(f"Detekován Termux: {'Ano' if is_termux else 'Ne'}\n")
        sys.exit(1)
    try:
        def getprop(prop):
            try:
                return subprocess.check_output(['getprop', prop], stderr=subprocess.DEVNULL).decode('utf-8').strip()
            except (FileNotFoundError, subprocess.CalledProcessError):
                return ""
        ro_kernel_qemu = getprop('ro.kernel.qemu')
        ro_hardware = getprop('ro.hardware').lower()
        ro_build_characteristics = getprop('ro.build.characteristics').lower()
        is_emulator = False
        if ro_kernel_qemu == '1':
            is_emulator = True
        if ro_hardware in ['ranchu', 'goldfish', 'vbox86', 'nox']:
            is_emulator = True
        if 'emulator' in ro_build_characteristics:
            is_emulator = True
        if is_emulator:
            print(f"\n{Fore.RED}======================================================{Style.RESET_ALL}")
            print(f"{Fore.RED} CHYBA: Detekován emulátor!{Style.RESET_ALL}")
            print(f"{Fore.RED}======================================================{Style.RESET_ALL}")
            print(f"{Fore.YELLOW}Spuštění uzlu na Android emulátorech je zablokováno.{Style.RESET_ALL}")
            sys.exit(1)
    except Exception:
        pass

def main():
    # OPRAVA B-5: volání enforce_mobile_environment() se přesunulo do
    # if __name__ == "__main__" níže.
    global wallets
    global p2p_node
    global password
    global read_only
    global address_book
    read_only = False
    
    if len(sys.argv) > 1:
        # OPRAVA AUDIT-5: `int(sys.argv[1])` bez try skončilo na `python
        # droid.py abc` tracebackem místo srozumitelné hlášky. Rozsah portu se
        # nekontroloval vůbec, takže 0, -1 i 99999 prošly a selhaly až při
        # bind() - tedy až po NTP synchronizaci a načtení celého řetězce, což
        # jsou na telefonu desítky sekund promarněné kvůli překlepu.
        try:
            p2p_port = int(sys.argv[1])
        except ValueError:
            print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Port '{sys.argv[1]}' není celé číslo.")
            print(f"{Fore.YELLOW}Použití: python {os.path.basename(sys.argv[0])} [port]{Style.RESET_ALL}")
            return
        if not (1 <= p2p_port <= 65535):
            print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Port {p2p_port} je mimo povolený rozsah 1-65535.")
            return
        if p2p_port < 1024:
            print(f"{Fore.YELLOW}Upozornění:{Style.RESET_ALL} Port {p2p_port} je privilegovaný; bez práv roota se bind() nezdaří.")
    else:
        p2p_port = 5001

    # OPRAVA AUDIT-5: kontrola argumentu je záměrně PŘED verify_genesis_address()
    # a sync_time_with_ntp(). Překlep v portu se tak ohlásí okamžitě, ne až po
    # NTP kolech a načtení celého řetězce z DB.
    verify_genesis_address()
    sync_time_with_ntp()
    
    droid_chain, wallets, peers, password = load_data()
    address_book = load_address_book(password)
    verify_genesis_block(droid_chain)
    
    p2p_node = P2PNode(droid_chain, P2P_HOST, p2p_port, peers)
    p2p_node.server_thread.daemon = True
    p2p_node.server_thread.start()
    p2p_node.bind_ready.wait()
    
    if not p2p_node.running:
        return
        
    p2p_node.sync_thread.start()
    
    print(f"\n{Fore.GREEN}Vítejte v {PROJECT_NAME} ({TICKER}) v{SOFTWARE_VERSION} {Style.RESET_ALL}")
    print(f"{Fore.CYAN}Tento uzel běží na portu {p2p_port} | Protokol v{PROTOCOL_VERSION} {Style.RESET_ALL}")
    
    while True:
        try:
            print_menu()
            try:
                choice = input(f"\n{Fore.BLUE}Zadejte číslo volby: {Style.RESET_ALL}").strip()
            except EOFError:
                choice = "20"

            # ZMĚNA (zobrazení menu): print_menu() vypisuje volby 1-9 s vedoucí
            # nulou ("01" až "09"), ale všechny větve níž porovnávají choice
            # s jednoznakovým tvarem ("1" až "9"). Bez téhle normalizace by
            # vstup OPSANÝ PŘESNĚ PODLE MENU neudělal nic: neodpovídal by žádné
            # větvi, nevypsala by se ani chybová hláška (ta tu není) a smyčka by
            # jen znovu vykreslila menu. Uživatel by z toho usoudil, že uzel
            # nereaguje.
            #
            # Normalizuje se VÝHRADNĚ dvouznakový tvar "0X", kde X je ASCII
            # číslice 1-9. Cokoli jiného prochází nedotčené, takže se nemění
            # chování 'clear', prázdného Enteru, "10" až "20" ani neplatných
            # vstupů. Číslice se testují proti doslovnému řetězci, ne přes
            # str.isdigit() - ze stejného důvodu, jaký popisuje OPRAVA U-4
            # u funkce jen_ascii_cislice() (isdigit() je pravdivé i pro
            # unicodové číslice, např. '٠١').
            #
            # Normalizace MUSÍ být před kontrolou read_only níž, protože ta
            # porovnává choice s ["4", "2"] - jinak by "04" a "02" tuhle branku
            # obešly a těžba i odesílání transakcí by v read-only režimu prošly.
            if len(choice) == 2 and choice[0] == '0' and choice[1] in '123456789':
                choice = choice[1]

            if choice.lower() == 'clear':
                os.system('cls' if os.name == 'nt' else 'clear')
                print(f"\n{Fore.GREEN}Vítejte v {PROJECT_NAME} ({TICKER}) v{SOFTWARE_VERSION} {Style.RESET_ALL}")
                print(f"{Fore.CYAN}Tento uzel běží na portu {p2p_port} | Protokol v{PROTOCOL_VERSION} {Style.RESET_ALL}")
                continue
                
            if read_only and choice in ["4", "2"]:
                print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Operace není povolena v read-only režimu.")
                continue
                
            if choice == "1":
                print(f"\n{Fore.YELLOW}--- Peněženky a zůstatky ---{Style.RESET_ALL}")
                if not wallets:
                    print(f"{Fore.CYAN}Žádné peněženky nebyly nalezeny.{Style.RESET_ALL}")
                else:
                    print(f"{Fore.YELLOW}--- Počet peněženek: {len(wallets)} ---{Style.RESET_ALL}\n")
                    # OPRAVA AUDIT-2026-5 (audit 8. 10. 2026, nález 5): snímek
                    # sdíleného stavu POD ZÁMKEM, a jeden pro celý výpis.
                    #
                    # Dřív se immature_rewards i mempool četly přímo a mimo
                    # droid_chain.lock, zatímco P2P vlákno týž slovník mění
                    # v update_state_with_block() (zralou odměnu vyjme, novou
                    # zapíše). Změna velikosti během iterace dává
                    # RuntimeError: dictionary changed size during iteration -
                    # naměřeno 746 pádů na 103 501 průchodů, tedy ~0,7 % výpisů.
                    # Obecný except v menu to sice zachytí, ale uživatel místo
                    # zůstatků uvidí "Došlo k chybě".
                    #
                    # Snímek se bere JEDNOU pro všechny peněženky, ne uvnitř
                    # cyklu: jinak by se zůstatky jednotlivých adres vztahovaly
                    # ke dvěma různým stavům řetězce a součty by si neodpovídaly.
                    # Mělká kopie stačí - položky jsou inty a vnitřní dicty
                    # immature odměn se nikdy nemutují, jen nahrazují celé
                    # (týž předpoklad, na kterém stojí make_state_shadow()).
                    with droid_chain.lock:
                        snapshot_mempool = list(droid_chain.unconfirmed_transactions)
                        snapshot_immature = list(droid_chain.immature_rewards.values())
                        snapshot_balance = dict(droid_chain.balance_map)
                    for address, wallet in wallets.items():
                        confirmed_balance = snapshot_balance.get(address, 0)
                        pending_outgoing = []
                        pending_incoming = []
                        pending_outgoing_sum = 0

                        for tx in snapshot_mempool:
                            if tx.from_address == address:
                                pending_outgoing.append(tx)
                                pending_outgoing_sum += tx.amount + tx.fee
                            if tx.to_address == address:
                                pending_incoming.append(tx)

                        total_balance = confirmed_balance - pending_outgoing_sum
                        pending_incoming_sum = sum(tx.amount for tx in pending_incoming)

                        immature_sum = sum(reward['amount'] for reward in snapshot_immature if reward['address'] == address)

                        confirmed_dec = Decimal(confirmed_balance) / Decimal(10 ** DECIMALS)
                        total_dec = Decimal(total_balance) / Decimal(10 ** DECIMALS)
                        pending_outgoing_dec = Decimal(pending_outgoing_sum) / Decimal(10 ** DECIMALS)
                        pending_incoming_dec = Decimal(pending_incoming_sum) / Decimal(10 ** DECIMALS)
                        immature_dec = Decimal(immature_sum) / Decimal(10 ** DECIMALS)
                        
                        print(f"Adresa: {Fore.CYAN}{address}{Style.RESET_ALL}")
                        if immature_sum > 0:
                            print(f" Nezralé odměny: {Fore.BLUE}{format(immature_dec, f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                        print(f" Celkový zůstatek: {Fore.MAGENTA}{format(total_dec, f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                        
                        if pending_outgoing:
                            print(f" Pending (-): {Fore.RED}-{format(pending_outgoing_dec, f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                            for tx in pending_outgoing:
                                tx_amount_dec = Decimal(tx.amount) / Decimal(10 ** DECIMALS)
                                tx_fee_dec = Decimal(tx.fee) / Decimal(10 ** DECIMALS)
                                print(f"  Příjemce: {tx.to_address}")
                                print(f"  Částka: {Fore.RED}-{format(tx_amount_dec, f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                                print(f"  Poplatek: {Fore.RED}-{format(tx_fee_dec, f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                                print(f"  TX ID: {tx.tx_id}")
                                print("  --------------------")
                                
                        if pending_incoming:
                            print(f" Pending (+): {Fore.GREEN}+{format(pending_incoming_dec, f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                            for tx in pending_incoming:
                                tx_amount_dec = Decimal(tx.amount) / Decimal(10 ** DECIMALS)
                                print(f"  Odesílatel: {tx.from_address}")
                                print(f"  Částka: {Fore.GREEN}+{format(tx_amount_dec, f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                                print(f"  Poplatek: {Fore.YELLOW}{format(Decimal(tx.fee) / Decimal(10 ** DECIMALS), f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                                print(f"  TX ID: {tx.tx_id}")
                                print("  --------------------")
                        print("-" * 40)
                        
            elif choice == "2":
                if not p2p_node.get_online_peers():
                    print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Vytvoření transakce není možné. Musíte být připojen k alespoň jednomu dalšímu uzlu.")
                    continue
                from_address = input("Zadejte ADRESU peněženky odesílatele: ").strip()
                if len(from_address) >= 3:
                    from_address = from_address[:3].upper() + from_address[3:].lower()
                if from_address not in wallets:
                    print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Peněženka s adresou '{from_address}' neexistuje. Nejdříve ji vytvořte nebo importujte.")
                    continue
                    
                to_address = input("Zadejte ADRESU příjemce: ").strip()
                if len(to_address) >= 3:
                    to_address = to_address[:3].upper() + to_address[3:].lower()
                if not is_valid_address(to_address):
                    print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Neplatný formát adresy příjemce.")
                    continue
                if from_address == to_address:
                    print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Nelze posílat peníze na stejnou adresu.")
                    continue
                    
                amount_str = input("Zadejte částku: ").strip()
                amount_str = amount_str.replace(',', '.')
                parts = amount_str.split('.')
                # OPRAVA U-4 (nález 5): .isdigit() nahrazeno jen_ascii_cislice().
                if len(parts) > 2 or not jen_ascii_cislice(parts[0]) or (len(parts) == 2 and (not jen_ascii_cislice(parts[1]) or len(parts[1]) > DECIMALS)):
                    print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Neplatný formát částky. Povolena jsou pouze čísla (0-9), jedna tečka a max. {DECIMALS} desetinných míst.")
                    continue
                    
                try:
                    # OPRAVA U-3 (audit 2. 10. 2026, nález 4): dřív
                    # `int(Decimal(amount_str) * (10 ** DECIMALS))`. Výchozí
                    # kontext modulu decimal má prec = 28, takže se násobení
                    # zaokrouhlilo na 28 platných číslic a delší vstup se TIŠE
                    # změnil: 12345678901234567890123.45678901 dalo
                    # ...45679000 místo ...45678901. Prakticky to nevadilo
                    # (taková částka neprojde kontrolou zůstatku o pár řádků
                    # níž), ale je to změna uživatelského vstupu v kódu, který
                    # jinak všude počítá v celých číslech.
                    #
                    # Čistě celočíselně: tvarová kontrola výš už zaručuje, že
                    # obě části jsou ASCII číslice a desetinná má nejvýš
                    # DECIMALS míst. int() nad řetězcem delším než
                    # sys.get_int_max_str_digits() vyhodí ValueError, kterou
                    # zachytí `except Exception` níž.
                    cela, _, des = amount_str.partition('.')
                    amount_in_decimal = int(cela + des.ljust(DECIMALS, '0'))
                    if amount_in_decimal < MIN_TX_AMOUNT:
                        print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Částka transakce je příliš malá. Minimální částka je {format(Decimal(MIN_TX_AMOUNT) / Decimal(10 ** DECIMALS), f'.{DECIMALS}f')} {TICKER}.")
                        continue
                except Exception:
                    print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Částka musí být platné číslo.")
                    continue
                    
                # OPRAVA AUDIT-2026-10 (audit 21. 10. 2026, nález N5): zůstatek i mempool se
                # čtou z JEDNOHO snímku pod zámkem - týž vzorec, jaký pro volby
                # 1, 9 a 13 zavedla OPRAVA AUDIT-2026-5; tahle dvě místa (a volba
                # 3 níž) v ní zůstala vynechaná.
                #
                # Živý seznam tu procházela smyčka, zatímco P2P vlákna do něj
                # zapisují. Seznam na rozdíl od slovníku výjimku nevyhodí, takže
                # se to neprojeví pádem - jen se odečte jiná množina transakcí,
                # než jaká odpovídá přečtenému zůstatku, a uživateli se ukáže
                # nekonzistentní "k dispozici". O prostředky jít nemůže:
                # add_transaction() si vše znovu ověří pod zámkem.
                with droid_chain.lock:
                    current_available_balance = droid_chain.get_confirmed_balance(from_address)
                    snapshot_mempool = list(droid_chain.unconfirmed_transactions)
                for tx_in_mempool in snapshot_mempool:
                    if tx_in_mempool.from_address == from_address:
                        current_available_balance -= (tx_in_mempool.amount + tx_in_mempool.fee)


                if current_available_balance < amount_in_decimal + TX_FEE_MIN:
                    print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Nedostatečný zůstatek pro tuto částku (včetně min. poplatku). K dispozici: {format(Decimal(current_available_balance) / Decimal(10**DECIMALS), f'.{DECIMALS}f')} {TICKER}")
                    continue
                    
                # ZMĚNA 1: prompt už neukazuje rozsah min-max, protože horní mez
                # poplatku neexistuje. Zobrazuje se jen minimum.
                fee_str = input(f"Zadejte poplatek (min. {format(Decimal(TX_FEE_MIN)/(10**DECIMALS), f'.{DECIMALS}f')} {TICKER}, prázdné pro {format(Decimal(TX_FEE_MIN)/(10**DECIMALS), f'.{DECIMALS}f')}): ").strip()
                if fee_str == "":
                    fee = TX_FEE_MIN
                else:
                    fee_str = fee_str.replace(',', '.')
                    parts_fee = fee_str.split('.')
                    # OPRAVA U-4 (nález 5): totéž co u částky výš.
                    if len(parts_fee) > 2 or not jen_ascii_cislice(parts_fee[0]) or (len(parts_fee) == 2 and (not jen_ascii_cislice(parts_fee[1]) or len(parts_fee[1]) > DECIMALS)):
                        print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Neplatný formát poplatku. Povolena jsou pouze čísla (0-9), jedna tečka a max. {DECIMALS} desetinných míst.")
                        continue
                    try:
                        # OPRAVA U-3 (nález 4): totéž co u částky výš -
                        # celočíselně, bez zaokrouhlení na prec = 28.
                        cela_f, _, des_f = fee_str.partition('.')
                        fee = int(cela_f + des_f.ljust(DECIMALS, '0'))
                        # ZMĚNA 1: kontroluje se jen dolní mez (fee >= TX_FEE_MIN).
                        if fee < TX_FEE_MIN:
                            print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Poplatek za transakci je nižší než minimum ({format(Decimal(TX_FEE_MIN) / Decimal(10 ** DECIMALS), f'.{DECIMALS}f')} {TICKER}).")
                            continue
                    except Exception:
                        print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Neplatný formát poplatku.")
                        continue

                # ZMĚNA 1: poplatek už nemá horní mez, shora ho omezuje jen
                # dostupný zůstatek. Kontrola výše pokrývala jen částku +
                # MINIMÁLNÍ poplatek; tahle pokrývá částku + ZADANÝ poplatek,
                # takže se uživatel nedostane k potvrzení transakce, kterou by
                # add_transaction() stejně odmítla. Zároveň to drží poplatek pod
                # rozsahem uint64, do kterého ho balí get_signing_data() - bez
                # téhle kontroly by nesmyslně vysoký poplatek shodil sestavení
                # transakce na struct.error.
                if current_available_balance < amount_in_decimal + fee:
                    print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Nedostatečný zůstatek pro tuto částku včetně zadaného poplatku. K dispozici: {format(Decimal(current_available_balance) / Decimal(10**DECIMALS), f'.{DECIMALS}f')} {TICKER}")
                    continue
                        
                with droid_chain.lock:
                    from_wallet = wallets[from_address]
                    nonce = droid_chain.get_next_nonce(from_address)
                    tx = Transaction(
                        from_wallet.address,
                        to_address,
                        amount_in_decimal,
                        fee,
                        nonce=nonce
                    )
                    tx.public_key = binascii.hexlify(from_wallet.public_key.to_string()).decode()
                    tx.signature = from_wallet.sign_transaction(tx)
                    tx.tx_id = tx.compute_hash()
                    # OPRAVA D-04: tohle je JEDINÉ místo v celém kódu, kde se
                    # transakce po vzniku ještě mění (doplní se veřejný klíč,
                    # podpis a přepočítá tx_id). Cache velikosti z get_size()
                    # by tu jinak zůstala z doby před podpisem, tedy o desítky
                    # bajtů menší, a mempool_bytes by se rozešel se skutečností.
                    tx.invalidate_size_cache()
                    
                    # OPRAVA AUDIT-2026-10 (nález N5): i tyhle dvě kontrolní
                    # smyčky jely nad ŽIVÝM seznamem, a dokonce dvakrát za sebou,
                    # takže se mohly vztahovat ke dvěma různým stavům mempoolu.
                    # Jeden snímek pro obě; rozhodující ověření dělá stejně
                    # add_transaction() pod zámkem, tohle je jen včasná hláška
                    # uživateli.
                    with droid_chain.lock:
                        snapshot_mempool = list(droid_chain.unconfirmed_transactions)
                    if any(t.tx_id == tx.tx_id for t in snapshot_mempool):
                        print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Duplicitní TX ID {tx.tx_id} po vytvoření. Transakce odmítnuta.")
                        continue
                    if tx.from_address != "COINBASE" and any(t.nonce == tx.nonce and t.from_address == tx.from_address for t in snapshot_mempool):
                        print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Duplicitní nonce {tx.nonce} pro adresu {tx.from_address} po vytvoření. Transakce odmítnuta.")
                        continue

                # ZMĚNA 1 (D, E): transakce je sestavená a podepsaná, ale do
                # mempoolu ani do P2P sítě se zatím NEDOSTALA. Odešle se až po
                # výslovném potvrzení "a".
                #
                # Dotaz na potvrzení běží záměrně MIMO droid_chain.lock. Čekání
                # na uživatele může trvat libovolně dlouho a po celou dobu by
                # P2P vlákna nemohla přijímat transakce ani bloky - add_block()
                # se o zámek pokusí jen ADD_BLOCK_LOCK_RETRIES krát po
                # ADD_BLOCK_LOCK_TIMEOUT sekundách a pak platný blok zahodí.
                # Bezpečnost tím netrpí: add_transaction() po potvrzení ověří
                # transakci znovu proti tehdy aktuálnímu stavu (nonce, zůstatek,
                # duplicity) a když se mezitím něco změnilo, transakci odmítne.
                print(f"\n{Fore.YELLOW}--- Shrnutí transakce ---{Style.RESET_ALL}")
                print(f" Odesílatel: {Fore.CYAN}{tx.from_address}{Style.RESET_ALL}")
                print(f" Příjemce: {Fore.CYAN}{tx.to_address}{Style.RESET_ALL}")
                print(f" Částka: {Fore.MAGENTA}{format(Decimal(tx.amount) / Decimal(10 ** DECIMALS), f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                print(f" Poplatek: {Fore.MAGENTA}{format(Decimal(tx.fee) / Decimal(10 ** DECIMALS), f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                print(f" Celkem (částka + poplatek): {Fore.MAGENTA}{format(Decimal(tx.amount + tx.fee) / Decimal(10 ** DECIMALS), f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                print(f" Nonce: {Fore.MAGENTA}{tx.nonce}{Style.RESET_ALL}")
                print(f" TX ID: {Fore.MAGENTA}{tx.tx_id}{Style.RESET_ALL}")

                # ZMĚNA 1 (E): varování při poplatku 1 DRX nebo vyšším. Práh je
                # čistě upozornění v rozhraní, NE limit - poplatek nad ním jde
                # po potvrzení odeslat úplně stejně jako jakýkoli jiný.
                prah_varovani_poplatku = 1 * (10 ** DECIMALS)
                if tx.fee >= prah_varovani_poplatku:
                    print(f"\n{Fore.RED}VAROVÁNÍ! TRANSAKČNÍ POPLATEK BYL NASTAVEN NA HODNOTU 1 {TICKER} NEBO VYŠŠÍ.{Style.RESET_ALL}")

                # ZMĚNA 1 (D): odešle se výhradně po odpovědi "a". Odpověď "n"
                # transakci zruší; na cokoli jiného se dotaz zopakuje, takže
                # překlep ani omylem stisknutý Enter transakci neodešle
                # a zároveň ji nezahodí. EOF na vstupu znamená zrušení.
                potvrzeno = False
                while True:
                    try:
                        odpoved = input(f"\n{Fore.YELLOW}Jste si jistí že chcete tuto transakci odeslat? (a/n): {Style.RESET_ALL}").strip().lower()
                    except EOFError:
                        odpoved = 'n'
                    if odpoved == 'a':
                        potvrzeno = True
                        break
                    if odpoved == 'n':
                        break
                    print(f"{Fore.RED}Neplatná odpověď.{Style.RESET_ALL} Zadejte 'a' pro odeslání transakce, nebo 'n' pro její zrušení.")

                if not potvrzeno:
                    # Transakce existuje jen v lokální proměnné: nic se nepřidalo
                    # do mempoolu, neuložilo do mempool.db ani neodeslalo peerům.
                    print(f"{Fore.YELLOW}Transakce byla zrušena. Nebyla přidána do mempoolu ani odeslána do sítě.{Style.RESET_ALL}")
                    continue

                with droid_chain.lock:
                    if droid_chain.add_transaction(tx):
                        print(f"{Fore.GREEN}Transakce byla úspěšně přidána do fronty.{Style.RESET_ALL}")
                        print(f" TX ID: {Fore.MAGENTA}{tx.tx_id}{Style.RESET_ALL}")
                        print(f" Nonce: {Fore.MAGENTA}{tx.nonce}{Style.RESET_ALL}")
                        print(f"{Fore.GREEN}Transakce byla podepsána privátním klíčem.{Style.RESET_ALL}")
                        save_mempool(droid_chain.unconfirmed_transactions)
                        # OPRAVA W-2 (nález N-2): viz mine() - vlastní transakce
                        # se taky zapíše do evidence přeposlaného, rozesílka
                        # zůstává všem peerům (addr=None).
                        p2p_node.preposli_sousedum({'type': 'transaction', 'data': tx.to_dict()},
                                                   ('tx', tx.tx_id), None)
                    else:
                        # Důvod vypsala add_transaction(). Typicky se během
                        # potvrzování změnil stav (např. dorazila jiná transakce
                        # téže adresy se stejnou nonce).
                        print(f"{Fore.RED}Transakce nebyla přidána do mempoolu ani odeslána do sítě. Vytvořte ji prosím znovu.{Style.RESET_ALL}")
                        
            elif choice == "3":
                print(f"\n{Fore.YELLOW}--- Mempool (nepotvrzené transakce) ---{Style.RESET_ALL}")
                # OPRAVA AUDIT-2026-10 (audit 21. 10. 2026, nález N5): jeden snímek
                # pod zámkem pro hlavičku i výpis. Dřív se živý seznam četl
                # TŘIKRÁT (velikost, počet, samotná smyčka) a P2P vlákna do něj
                # mezitím zapisují, takže hlavička mohla hlásit jiný počet
                # transakcí, než kolik se jich vypsalo.
                with droid_chain.lock:
                    snapshot_mempool = list(droid_chain.unconfirmed_transactions)
                mempool_size_bytes = get_mempool_size_bytes(snapshot_mempool)
                mempool_size_kb = mempool_size_bytes / 1024
                mempool_size_mb = mempool_size_kb / 1024
                tx_count = len(snapshot_mempool)
                print(f"Velikost mempoolu: {Fore.CYAN}{tx_count} TX / {mempool_size_kb:.2f} KB / {mempool_size_mb:.2f} MB{Style.RESET_ALL}")

                if not snapshot_mempool:
                    print("    Mempool je prázdný.")
                else:
                    for tx in snapshot_mempool:
                        print(f"TX ID: {Fore.CYAN}{tx.tx_id}{Style.RESET_ALL}")
                        print(f" Od: {tx.from_address}")
                        print(f" Komu: {tx.to_address}")
                        print(f" Částka: {Fore.MAGENTA}{format(Decimal(tx.amount) / Decimal(10 ** DECIMALS), f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                        print(f" Poplatek: {Fore.MAGENTA}{format(Decimal(tx.fee) / Decimal(10 ** DECIMALS), f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                        print(f" Nonce: {Fore.MAGENTA}{tx.nonce}{Style.RESET_ALL}")
                        print(f" Čas: {time.strftime('%d.%m.%Y %H:%M:%S UTC+00:00', time.gmtime(tx.timestamp))}")
                        if tx.signature:
                            print(f" Podpis: {Fore.BLUE}{tx.signature}{Style.RESET_ALL}")
                        else:
                            print(f" Podpis: {Fore.RED}žádný{Style.RESET_ALL}")
                        print("-" * 20)
                        
            elif choice == "4":
                if not p2p_node.get_online_peers():
                    print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Těžba není možná. Musíte být připojen k alespoň jednomu dalšímu uzlu.")
                    continue
                if not wallets:
                    print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Žádné peněženky nejsou dostupné. Nejdříve vytvořte nebo importujte peněženku.")
                    continue
                    
                print(f"{Fore.YELLOW}Dostupné peněženky pro těžbu:{Style.RESET_ALL}")
                wallet_list = list(wallets.keys())
                for i, addr in enumerate(wallet_list, 1):
                    print(f" {i}. {Fore.CYAN}{addr}{Style.RESET_ALL}")
                    
                try:
                    selected = int(input(f"{Fore.BLUE}Vyberte číslo peněženky těžaře: {Style.RESET_ALL}"))
                    if 1 <= selected <= len(wallet_list):
                        miner_address = wallet_list[selected - 1]
                        print(f"{Fore.GREEN}Těžím na adresu: {Fore.CYAN}{miner_address}{Style.RESET_ALL}")
                        droid_chain.mine(miner_address)
                        save_data(droid_chain, wallets, password, p2p_node.peers_snapshot())
                    else:
                        print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Neplatná volba.")
                except ValueError:
                    print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Neplatný vstup. Zadejte číslo.")
                    
            elif choice == "5":
                while True:
                    print(f"\n{Fore.YELLOW}--- Uložené adresy ---{Style.RESET_ALL}")
                    if not address_book:
                        print(f"{Fore.CYAN}Žádné uložené adresy.{Style.RESET_ALL}")
                    else:
                        for name, addr in address_book.items():
                            print(f" Jméno: {Fore.GREEN}{name}{Style.RESET_ALL} | Adresa: {Fore.CYAN}{addr}{Style.RESET_ALL}")
                            
                    print(f"\n{Fore.GREEN}1{Style.RESET_ALL} - Přidat adresu")
                    print(f"{Fore.GREEN}2{Style.RESET_ALL} - Smazat adresu")
                    sub_choice = input(f"{Fore.BLUE}Zadejte volbu (nebo stiskněte Enter pro návrat): {Style.RESET_ALL}").strip()
                    
                    if sub_choice == "":
                        break
                    elif sub_choice == "1":
                        name = input("Zadejte jméno (alias): ").strip()
                        addr = input("Zadejte adresu: ").strip()
                        if name in address_book:
                            print(f"{Fore.RED}Tento alias již existuje.{Style.RESET_ALL}")
                        elif addr in address_book.values():
                            print(f"{Fore.RED}Tato adresa je již v adresáři uložena.{Style.RESET_ALL}")
                        elif not is_valid_address(addr):
                            print(f"{Fore.RED}Neplatný formát adresy.{Style.RESET_ALL}")
                        else:
                            address_book[name] = addr
                            save_address_book(address_book, password)
                            print(f"{Fore.GREEN}Adresa '{name}' byla uložena.{Style.RESET_ALL}")
                    elif sub_choice == "2":
                        name = input("Zadejte jméno ke smazání: ").strip()
                        if name in address_book:
                            del address_book[name]
                            save_address_book(address_book, password)
                            print(f"{Fore.GREEN}Adresa '{name}' byla smazána.{Style.RESET_ALL}")
                        else:
                            print(f"{Fore.RED}Jméno '{name}' nenalezeno.{Style.RESET_ALL}")
                    else:
                        print(f"{Fore.RED}Neplatná volba.{Style.RESET_ALL}")
                        
            elif choice == "6":
                new_wallet = Wallet()
                wallets[new_wallet.address] = new_wallet
                print(f"{Fore.GREEN}Nová peněženka byla vytvořena!{Style.RESET_ALL}")
                print(f" Adresa: {Fore.CYAN}{new_wallet.address}{Style.RESET_ALL}")
                # OPRAVA R-5: hláška o uložení se tiskla PŘED samotným uložením a
                # bez ohledu na jeho výsledek. Při selhání zápisu žil klíč jen
                # v paměti a po restartu zanikl - včetně prostředků, které na
                # adresu mezitím přišly. Tvrzení proto smí padnout až po
                # potvrzeném zápisu; při neúspěchu se klíč vypíše k záloze.
                if save_data(droid_chain, wallets, password, p2p_node.peers_snapshot(), save_wallets=True):
                    print(f" {Fore.GREEN}Privátní klíč byl bezpečně uložen do souboru.{Style.RESET_ALL}")
                else:
                    kl = binascii.hexlify(new_wallet.private_key.to_string()).decode()
                    print(f"\n{Fore.RED}POZOR: peněženku se NEPODAŘILO uložit na disk!{Style.RESET_ALL}")
                    print(f"{Fore.RED}Klíč existuje jen v paměti a po ukončení programu zanikne.{Style.RESET_ALL}")
                    print(f"{Fore.YELLOW}Zálohujte si ho ručně:{Style.RESET_ALL} {Fore.RED}{kl}{Style.RESET_ALL}")
                    print(f"{Fore.YELLOW}Uvolněte místo na disku a zkuste uložení znovu (volba 20).{Style.RESET_ALL}")
                
            elif choice == "7":
                # OPRAVA AUDIT-12: chybělo .strip(). Volby 2, 8 i 9 vstup strippují
                # (8 a 9 výslovně kvůli normalizaci vloženého textu, viz OPRAVA
                # AUDIT-7), jen tahle ne. is_valid_private_key() přitom vyžaduje
                # přesnou délku 64 znaků, takže jediná mezera navíc - typicky
                # z kopírování ze zálohy - klíč odmítla. Uživatel obnovující
                # peněženku dostal hlášku "Neplatný formát privátního klíče",
                # přestože klíč měl správný; to je v okamžiku obnovy přístupu
                # k prostředkům zavádějící zpráva, která svádí k domněnce, že
                # je záloha poškozená.
                key_hex = input("Zadejte privátní klíč (hex): ").strip()
                if not is_valid_private_key(key_hex):
                    print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Neplatný formát privátního klíče.")
                    continue
                imported_wallet = Wallet(private_key=key_hex)
                if imported_wallet.address in wallets:
                    print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Privátní klíč k této adrese už existuje v seznamu peněženek.")
                    continue
                wallets[imported_wallet.address] = imported_wallet
                print(f"{Fore.GREEN}Peněženka byla úspěšně importována!{Style.RESET_ALL}")
                print(f" Adresa: {Fore.CYAN}{imported_wallet.address}{Style.RESET_ALL}")
                # OPRAVA R-5: viz volba 6 - výsledek uložení se musí ohlásit.
                if not save_data(droid_chain, wallets, password, p2p_node.peers_snapshot(), save_wallets=True):
                    print(f"{Fore.RED}POZOR: peněženku se NEPODAŘILO uložit na disk - po restartu zmizí.{Style.RESET_ALL}")
                    print(f"{Fore.YELLOW}Váš klíč máte, ale import bude nutné zopakovat.{Style.RESET_ALL}")
                
            elif choice == "8":
                address = input("Zadejte ADRESU peněženky, jejíž klíč chcete exportovat: ").strip()
                # OPRAVA AUDIT-7: stejná normalizace velikosti písmen jako ve
                # volbě 2. Bez ní adresa vložená ze schránky v jiném formátu
                # spadne na "peněženka neexistuje", přestože ji uživatel má.
                if len(address) >= 3:
                    address = address[:3].upper() + address[3:].lower()
                if address in wallets:
                    bezp_otazka = input(f"{Fore.YELLOW}Opravdu si přejete exportovat privátní klíč? (a/n): {Style.RESET_ALL}").strip().lower()
                    if bezp_otazka == 'a':
                        private_key_hex = binascii.hexlify(wallets[address].private_key.to_string()).decode()
                        print(f"{Fore.GREEN}Privátní klíč pro adresu '{address}':{Style.RESET_ALL} {Fore.RED}{private_key_hex}{Style.RESET_ALL}")
                    else:
                        print(f"{Fore.YELLOW}Export privátního klíče byl zrušen.{Style.RESET_ALL}")
                else:
                    print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Peněženka s adresou '{address}' neexistuje.")
                    
            elif choice == "9":
                address_to_delete = input("Zadejte ADRESU peněženky, kterou chcete smazat: ").strip()
                # OPRAVA AUDIT-7: stejná normalizace velikosti písmen jako ve volbě 2.
                if len(address_to_delete) >= 3:
                    address_to_delete = address_to_delete[:3].upper() + address_to_delete[3:].lower()
                if address_to_delete in wallets:
                    # OPRAVA AUDIT-6: smazáním zaniká privátní klíč a s ním
                    # nevratně i přístup k jakémukoli zůstatku na adrese. Před
                    # potvrzením se proto vypíše, o co přesně uživatel přijde
                    # (potvrzený zůstatek, čekající transakce i nezralé
                    # coinbase odměny), nabídne se export klíče a potvrzení
                    # vyžaduje opsání celé adresy, ne pouhé "a".
                    # OPRAVA AUDIT-2026-5 (nález 5): snímek pod zámkem, stejně
                    # jako ve volbě 1. Tady na tom záleží nejvíc ze všech tří
                    # míst: podle vypsané částky se uživatel rozhoduje, jestli
                    # nevratně smaže privátní klíč, takže se nesmí stát, že
                    # výpis spadne na RuntimeError a on ho přeskočí.
                    with droid_chain.lock:
                        snapshot_mempool = list(droid_chain.unconfirmed_transactions)
                        snapshot_immature = list(droid_chain.immature_rewards.values())
                        confirmed_balance = droid_chain.get_confirmed_balance(address_to_delete)
                    pending_outgoing_sum = 0
                    pending_incoming_sum = 0
                    for tx in snapshot_mempool:
                        if tx.from_address == address_to_delete:
                            pending_outgoing_sum += tx.amount + tx.fee
                        if tx.to_address == address_to_delete:
                            pending_incoming_sum += tx.amount
                    immature_sum = sum(
                        reward['amount']
                        for reward in snapshot_immature
                        if reward['address'] == address_to_delete
                    )
                    total_balance = confirmed_balance - pending_outgoing_sum
                    v_sazce = total_balance + pending_incoming_sum + immature_sum

                    print(f"\n{Fore.YELLOW}--- Peněženka ke smazání ---{Style.RESET_ALL}")
                    print(f" Adresa: {Fore.CYAN}{address_to_delete}{Style.RESET_ALL}")
                    print(f" Potvrzený zůstatek: {Fore.MAGENTA}{format(Decimal(confirmed_balance) / Decimal(10 ** DECIMALS), f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                    if pending_outgoing_sum > 0:
                        print(f" Pending (-): {Fore.RED}-{format(Decimal(pending_outgoing_sum) / Decimal(10 ** DECIMALS), f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                    if pending_incoming_sum > 0:
                        print(f" Pending (+): {Fore.GREEN}+{format(Decimal(pending_incoming_sum) / Decimal(10 ** DECIMALS), f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                    if immature_sum > 0:
                        print(f" Nezralé odměny: {Fore.BLUE}{format(Decimal(immature_sum) / Decimal(10 ** DECIMALS), f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                        print(f" {Fore.YELLOW}Pozor:{Style.RESET_ALL} nezralé odměny se na adresu připíšou až po {COINBASE_MATURITY} blocích.")
                    print(f" {Fore.YELLOW}V sázce celkem: {format(Decimal(v_sazce) / Decimal(10 ** DECIMALS), f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")

                    if v_sazce > 0:
                        print(f"\n{Fore.RED}VAROVÁNÍ:{Style.RESET_ALL} Na této adrese jsou prostředky. Smazáním peněženky")
                        print(f"{Fore.RED}         zanikne privátní klíč a prostředky budou NENÁVRATNĚ ztracené.{Style.RESET_ALL}")
                    else:
                        print(f"\n{Fore.YELLOW}Na adrese nejsou žádné prostředky, ale privátní klíč zanikne nevratně.{Style.RESET_ALL}")

                    export_otazka = input(f"\n{Fore.YELLOW}Chcete si před smazáním zobrazit privátní klíč k záloze? (a/n): {Style.RESET_ALL}").strip().lower()
                    if export_otazka == 'a':
                        private_key_hex = binascii.hexlify(wallets[address_to_delete].private_key.to_string()).decode()
                        print(f"{Fore.GREEN}Privátní klíč pro adresu '{address_to_delete}':{Style.RESET_ALL} {Fore.RED}{private_key_hex}{Style.RESET_ALL}")
                        print(f"{Fore.YELLOW}Uložte si ho na bezpečné místo. Po smazání už ho nikdo neobnoví.{Style.RESET_ALL}")
                        input(f"{Fore.BLUE}Až budete mít klíč zálohovaný, pokračujte stiskem Enter: {Style.RESET_ALL}")

                    print(f"\n{Fore.YELLOW}Tato akce je nevratná. Pro potvrzení opište celou adresu peněženky.{Style.RESET_ALL}")
                    potvrzeni = input(f"{Fore.BLUE}Adresa (prázdné pro zrušení): {Style.RESET_ALL}").strip()
                    if len(potvrzeni) >= 3:
                        potvrzeni = potvrzeni[:3].upper() + potvrzeni[3:].lower()
                    if potvrzeni == address_to_delete:
                        del wallets[address_to_delete]
                        # OPRAVA S-3 (Nález 5): OPRAVA R-5 doplnila kontrolu
                        # návratové hodnoty save_data() do voleb 6 a 7, ale ne
                        # sem. U voleb 6 a 7 míří selhání zápisu tak, že se klíč
                        # ZTRATÍ; tady opačně - klíč zmizí z paměti, ale
                        # v wallets.json.enc PŘEŽIJE a po restartu se vrátí.
                        # Uživatel, který peněženku maže před předáním zařízení,
                        # přitom četl "úspěšně smazána". Tvrzení proto padne až
                        # po ověřeném zápisu, stejně jako ve volbě 6.
                        if save_data(droid_chain, wallets, password, p2p_node.peers_snapshot(), save_wallets=True):
                            print(f"\n{Fore.GREEN}Peněženka '{address_to_delete}' byla úspěšně smazána.{Style.RESET_ALL}")
                        else:
                            print(f"\n{Fore.RED}POZOR: smazání se NEPODAŘILO uložit na disk!{Style.RESET_ALL}")
                            print(f"{Fore.RED}Klíč je pryč z paměti, ale v souboru peněženek ZŮSTÁVÁ{Style.RESET_ALL}")
                            print(f"{Fore.RED}a po restartu se peněženka vrátí. NEPOVAŽUJTE ji za smazanou.{Style.RESET_ALL}")
                            print(f"{Fore.YELLOW}Uvolněte místo na disku a uložte znovu (volba 20), nebo{Style.RESET_ALL}")
                            print(f"{Fore.YELLOW}smazání po restartu zopakujte.{Style.RESET_ALL}")
                    elif potvrzeni == "":
                        print(f"\n{Fore.YELLOW}Akce zrušena. Peněženka nebyla smazána.{Style.RESET_ALL}")
                    else:
                        print(f"\n{Fore.YELLOW}Zadaná adresa se neshoduje. Peněženka nebyla smazána.{Style.RESET_ALL}")
                else:
                    print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Peněženka s adresou '{address_to_delete}' neexistuje.")
                    
            elif choice == "10":
                print(f"\n{Fore.YELLOW}--- Blockchain ---{Style.RESET_ALL}")
                # OPRAVA AUDIT-11: týž vzorec jako ve find_transaction_by_id() -
                # conn.close() byl obyčejný řádek na konci větve, takže ho každá
                # výjimka přeskočila. V cyklu tu přitom běží json.loads()
                # i Block.from_dict(), tedy dvě místa, která nad poškozeným
                # řádkem v databázi spolehlivě vyhodí. Tělo proto obaluje
                # try/finally podle vzoru get_block_from_db().
                conn = None
                try:
                    conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
                    conn.execute("PRAGMA journal_mode=WAL;")
                    c = conn.cursor()
                    c.execute("SELECT block_index, timestamp, transactions, previous_hash, target_hex, nonce, block_hash, merkle_root, version, chain_id, state_root FROM blocks ORDER BY block_index")
                
                    total_size = 0
                    all_addresses = set()
                
                    for row in c:
                        block_data = {
                            'index': row[0],
                            'timestamp': row[1],
                            'transactions': json.loads(row[2]),
                            'previous_hash': row[3],
                            'target': row[4],
                            'nonce': row[5],
                            'hash': row[6],
                            'merkle_root': row[7],
                            'version': row[8],
                            'chain_id': row[9], 'state_root': row[10]
                        }
                        block = Block.from_dict(block_data)
                        total_size += block.get_size()
                    
                        for tx in block.transactions:
                            if tx.from_address != "COINBASE":
                                all_addresses.add(tx.from_address)
                            all_addresses.add(tx.to_address)
                        
                        target_hex = hex(block.target)[2:]
                        print(f"Blok #{block.index}")
                        print(f" Verze bloku: {Fore.CYAN}{block.version}{Style.RESET_ALL}")
                        print(f" Chain ID: {Fore.CYAN}{block.chain_id}{Style.RESET_ALL}")
                        print(f" Hash: {Fore.MAGENTA}{block.hash}{Style.RESET_ALL}")
                        print(f" Transaction root: {Fore.CYAN}{block.merkle_root}{Style.RESET_ALL}")
                        print(f" State root: {Fore.CYAN}{block.state_root}{Style.RESET_ALL}")
                        print(f" Target: {Fore.CYAN}{target_hex}{Style.RESET_ALL}")
                        print(f" Předchozí hash: {Fore.MAGENTA}{block.previous_hash}{Style.RESET_ALL}")
                        print(f" PoW nonce: {Fore.CYAN}{block.nonce}{Style.RESET_ALL}")
                        print(f" Čas: {Fore.CYAN}{time.strftime('%d.%m.%Y %H:%M:%S UTC+00:00', time.gmtime(block.timestamp))}{Style.RESET_ALL}")
                        print(f" Velikost bloku: {Fore.CYAN}{block.get_size() / 1024:.2f} KB{Style.RESET_ALL}")
                        print(f" Počet potvrzení: {format_confirmations(droid_chain.get_confirmations(block.hash))}")
                        print(f" Počet transakcí: {len(block.transactions)}")
                        if block.transactions:
                            print(f" {Fore.YELLOW}Transakce:{Style.RESET_ALL}")
                            for tx in block.transactions:
                                print(f" - TX ID: {Fore.CYAN}{tx.tx_id}{Style.RESET_ALL}")
                                print(f"   Od: {tx.from_address}")
                                print(f"   Komu: {tx.to_address}")
                                print(f"   Částka: {Fore.CYAN}{format(Decimal(tx.amount) / Decimal(10 ** DECIMALS), f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                                if tx.from_address != "COINBASE":
                                    print(f"   Poplatek: {format(Decimal(tx.fee) / Decimal(10 ** DECIMALS), f'.{DECIMALS}f')} {TICKER}")
                                    print(f"   TX nonce: {Fore.MAGENTA}{tx.nonce}{Style.RESET_ALL}")
                                if tx.signature:
                                    print(f"   Podpis: {Fore.BLUE}{tx.signature}{Style.RESET_ALL}")
                                else:
                                    print(f"   Podpis: {Fore.RED}žádný{Style.RESET_ALL}")
                                if tx.data:
                                    print(f"   Zpráva: {Fore.YELLOW}{tx.data}{Style.RESET_ALL}")
                        print("=" * 40)
                    
                    c.execute("SELECT COUNT(*) FROM transactions")
                    total_tx_count = c.fetchone()[0]
                
                finally:
                    if conn is not None:
                        try:
                            conn.close()
                        except Exception:
                            pass
                total_size_kb = total_size / 1024
                total_size_mb = total_size_kb / 1024
                print(f"Velikost blockchainu: {Fore.CYAN}{total_size_kb:.2f} KB / {total_size_mb:.2f} MB{Style.RESET_ALL}")
                print(f"Celková kumulativní práce: {Fore.CYAN}{droid_chain.get_cumulative_work()}{Style.RESET_ALL}")
                print(f"Celkový počet bloků: {Fore.CYAN}{droid_chain.max_block_index + 1}{Style.RESET_ALL}")
                print(f"Celkový počet transakcí: {Fore.CYAN}{total_tx_count}{Style.RESET_ALL}")
                print(f"Celkový počet adres: {Fore.CYAN}{len(all_addresses)}{Style.RESET_ALL}")
                
            elif choice == "11":
                search_input = input("Zadejte číslo bloku nebo jeho hash: ").strip()
                block = None
                # OPRAVA K-5 (audit 21. 10. 2026, nález 5): .isdigit() nahrazeno
                # jen_ascii_cislice() ze stejného důvodu, jaký popisuje OPRAVA
                # U-4 u částky a poplatku - '١٢٣'.isdigit() je True a int() to
                # převede na 123, takže volba přijímala unicodové číslice.
                # Dopad byl nulový (jen vyhledání bloku), ale pravidlo má
                # v souboru platit na jednom místě, ne na dvou ze tří.
                if jen_ascii_cislice(search_input):
                    try:
                        block_index = int(search_input)
                        if 0 <= block_index <= droid_chain.max_block_index:
                            block = droid_chain.get_block(block_index)
                        else:
                            print(f"{Fore.RED}Blok s číslem {block_index} neexistuje.{Style.RESET_ALL}")
                    except ValueError:
                        print(f"{Fore.RED}Neplatné číslo bloku.{Style.RESET_ALL}")
                else:
                    # OPRAVA AUDIT-11: close() sice stál správně PŘED json.loads()
                    # i Block.from_dict(), takže parsování poškozených dat spojení
                    # neuneslo - pořád ho ale přeskočila jakákoli sqlite3.Error
                    # z connect(), PRAGMA, execute() nebo fetchone(). Nad
                    # poškozeným souborem vyhodí execute() DatabaseError ("file
                    # is not a database") a deskriptor zůstane viset. Pořadí
                    # kroků se nemění, přibylo jen try/finally.
                    conn = None
                    row = None
                    try:
                        conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
                        conn.execute("PRAGMA journal_mode=WAL;")
                        c = conn.cursor()
                        c.execute("SELECT block_index, timestamp, transactions, previous_hash, target_hex, nonce, block_hash, merkle_root, version, chain_id, state_root FROM blocks WHERE block_hash = ?", (search_input,))
                        row = c.fetchone()
                    finally:
                        if conn is not None:
                            try:
                                conn.close()
                            except Exception:
                                pass
                    if row:
                        block_data = {
                            'index': row[0],
                            'timestamp': row[1],
                            'transactions': json.loads(row[2]),
                            'previous_hash': row[3],
                            'target': row[4],
                            'nonce': row[5],
                            'hash': row[6],
                            'merkle_root': row[7],
                            'version': row[8],
                            'chain_id': row[9], 'state_root': row[10]
                        }
                        block = Block.from_dict(block_data)
                    else:
                        print(f"{Fore.RED}Blok s hashem {search_input} nebyl nalezen.{Style.RESET_ALL}")
                        
                if block:
                    target_hex = hex(block.target)[2:]
                    print(f"\n{Fore.GREEN}Blok nalezen!{Style.RESET_ALL}")
                    print(f"Blok #{block.index}")
                    print(f" Verze bloku: {Fore.CYAN}{block.version}{Style.RESET_ALL}")
                    print(f" Chain ID: {Fore.CYAN}{block.chain_id}{Style.RESET_ALL}")
                    print(f" Hash: {Fore.MAGENTA}{block.hash}{Style.RESET_ALL}")
                    print(f" Transaction root: {Fore.CYAN}{block.merkle_root}{Style.RESET_ALL}")
                    print(f" State root: {Fore.CYAN}{block.state_root}{Style.RESET_ALL}")
                    print(f" Target: {Fore.CYAN}{target_hex}{Style.RESET_ALL}")
                    print(f" Předchozí hash: {Fore.MAGENTA}{block.previous_hash}{Style.RESET_ALL}")
                    print(f" PoW nonce: {Fore.CYAN}{block.nonce}{Style.RESET_ALL}")
                    print(f" Čas: {Fore.CYAN}{time.strftime('%d.%m.%Y %H:%M:%S UTC+00:00', time.gmtime(block.timestamp))}{Style.RESET_ALL}")
                    print(f" Velikost bloku: {Fore.CYAN}{block.get_size() / 1024:.2f} KB{Style.RESET_ALL}")
                    print(f" Počet potvrzení: {format_confirmations(droid_chain.get_confirmations(block.hash))}")
                    print(f" Počet transakcí: {len(block.transactions)}")
                    if block.transactions:
                        print(f" {Fore.YELLOW}Transakce:{Style.RESET_ALL}")
                        for tx in block.transactions:
                            print(f" - TX ID: {Fore.CYAN}{tx.tx_id}{Style.RESET_ALL}")
                            print(f"   Od: {tx.from_address}")
                            print(f"   Komu: {tx.to_address}")
                            print(f"   Částka: {Fore.CYAN}{format(Decimal(tx.amount) / Decimal(10 ** DECIMALS), f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                            if tx.from_address != "COINBASE":
                                print(f"   Poplatek: {format(Decimal(tx.fee) / Decimal(10 ** DECIMALS), f'.{DECIMALS}f')} {TICKER}")
                                print(f"   TX nonce: {Fore.MAGENTA}{tx.nonce}{Style.RESET_ALL}")
                            if tx.signature:
                                print(f"   Podpis: {Fore.BLUE}{tx.signature}{Style.RESET_ALL}")
                            else:
                                print(f"   Podpis: {Fore.RED}žádný{Style.RESET_ALL}")
                            if tx.data:
                                print(f"   Zpráva: {Fore.YELLOW}{tx.data}{Style.RESET_ALL}")
                    print("=" * 40)
                    
            elif choice == "12":
                # OPRAVA AUDIT-12: totéž jako ve volbě 7 - vstup se vkládá ze
                # schránky a mezera navíc znamenala "transakce nebyla nalezena",
                # protože tx_id se porovnává na přesnou shodu řetězce.
                tx_id = input("Zadejte TX ID transakce: ").strip()
                tx, location = droid_chain.find_transaction_by_id(tx_id)
                if tx:
                    print(f"\n{Fore.YELLOW}--- Detaily transakce (TX ID: {tx.tx_id}) ---{Style.RESET_ALL}")
                    print(f" Stav: {Fore.GREEN}Nalezena v {location}{Style.RESET_ALL}")
                    if "Blok #" in location:
                        block_index = int(location.split("#")[1])
                        confirmations = droid_chain.get_confirmations_by_index(block_index)
                        print(f" Potvrzení: {format_confirmations(confirmations)}")
                    else:
                        print(f" Potvrzení: {Fore.RED}0 (v mempoolu){Style.RESET_ALL}")
                    print(f" Od: {tx.from_address}")
                    print(f" Komu: {tx.to_address}")
                    print(f" Částka: {format(Decimal(tx.amount) / Decimal(10 ** DECIMALS), f'.{DECIMALS}f')} {TICKER}")
                    print(f" Poplatek: {format(Decimal(tx.fee) / Decimal(10 ** DECIMALS), f'.{DECIMALS}f')} {TICKER}")
                    print(f" Nonce: {tx.nonce}")
                    print(f" Čas: {time.strftime('%d.%m.%Y %H:%M:%S UTC+00:00', time.gmtime(tx.timestamp))}")
                    print(f" Veřejný klíč: {tx.public_key}")
                    print(f" Podpis: {tx.signature}")
                    if tx.data:
                        print(f" Zpráva: {Fore.YELLOW}{tx.data}{Style.RESET_ALL}")
                    print("-" * 20)
                else:
                    print(f"{Fore.RED}Transakce s TX ID '{tx_id}' nebyla nalezena.{Style.RESET_ALL}")
                    
            elif choice == "13":
                # OPRAVA AUDIT-12: chybělo .strip() i normalizace velikosti
                # písmen. Volby 2, 8 a 9 dělají obojí (viz OPRAVA AUDIT-7),
                # tahle jako jediná adresní volba ne - historie pak vyšla
                # prázdná, přestože adresa existuje. Adresa je TICKER velkými
                # a 72 hex znaků malými, viz is_valid_address().
                address = input("Zadejte ADRESU pro zobrazení historie transakcí: ").strip()
                if len(address) >= 3:
                    address = address[:3].upper() + address[3:].lower()
                print(f"\n{Fore.YELLOW}--- Historie transakcí pro adresu '{address}' ---{Style.RESET_ALL}")
                sent_amount = 0
                received_amount = 0
                sent_count = 0
                received_count = 0
                tx_list = []
                tx_found = False
                
                # OPRAVA A-07: conn.close() byl obyčejný řádek na konci větve,
                # takže ho každá výjimka přeskočila. Ve smyčce tu přitom běží
                # json.loads() i Transaction.from_dict(), tedy dvě místa, která
                # nad poškozeným řádkem spolehlivě vyhodí (komentář u volby 10
                # to takhle přímo pojmenovává). Naměřeno 41 deskriptorů po 20
                # voláních - dva na volání, samotný soubor plus WAL, přesně
                # jako v OPRAVĚ AUDIT-11. Sem se tehdy nedostala.
                #
                # Parsování zůstává UVNITŘ try (vzor volby 10), ne až za close()
                # jako ve find_transaction_by_id(): ta vyzvedává jediný řádek,
                # kdežto tady jde o celý řetězec. Materializovat ho do paměti
                # kvůli pořadí operací by na mobilu vyměnilo únik deskriptorů
                # za únik RAM. Kurzor se tak dál streamuje a finally zaručí
                # zavření i při výjimce.
                conn = None
                try:
                    conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
                    conn.execute("PRAGMA journal_mode=WAL;")
                    c = conn.cursor()
                    c.execute("SELECT block_index, transactions FROM blocks ORDER BY block_index")
                    for row in c:
                        transactions = json.loads(row[1])
                        for tx_data in transactions:
                            tx = Transaction.from_dict(tx_data)
                            if tx.from_address == address or tx.to_address == address:
                                tx_found = True
                                tx_list.append((tx.timestamp, tx, row[0]))
                                if tx.from_address == address:
                                    sent_amount += tx.amount + tx.fee
                                    sent_count += 1
                                else:
                                    received_amount += tx.amount
                                    received_count += 1
                finally:
                    if conn is not None:
                        try:
                            conn.close()
                        except Exception:
                            pass
                
                if not tx_found:
                    print(f"{Fore.CYAN}Žádné potvrzené transakce nebyly nalezeny.{Style.RESET_ALL}")
                else:
                    tx_list.sort(key=lambda x: x[0])
                    for _, tx, block_index in tx_list:
                        if tx.from_address == address:
                            direction = f"{Fore.RED}Odesláno{Style.RESET_ALL}"
                        else:
                            direction = f"{Fore.GREEN}Přijato{Style.RESET_ALL}"
                        confirmations = droid_chain.get_confirmations_by_index(block_index)
                        print(f"TX ID: {Fore.CYAN}{tx.tx_id}{Style.RESET_ALL}")
                        print(f" Blok: #{block_index}")
                        print(f" Potvrzení: {format_confirmations(confirmations)}")
                        print(f" Směr: {direction}")
                        print(f" Od: {tx.from_address}")
                        print(f" Komu: {tx.to_address}")
                        print(f" Částka: {format(Decimal(tx.amount) / Decimal(10 ** DECIMALS), f'.{DECIMALS}f')} {TICKER}")
                        if tx.from_address != "COINBASE":
                            print(f" Poplatek: {format(Decimal(tx.fee) / Decimal(10 ** DECIMALS), f'.{DECIMALS}f')} {TICKER}")
                        print(f" Čas: {time.strftime('%d.%m.%Y %H:%M:%S UTC+00:00', time.gmtime(tx.timestamp))}")
                        print("-" * 20)
                        
                # OPRAVA AUDIT-2026-5 (nález 5): snímek pod zámkem, stejně jako
                # ve volbách 1 a 9. Jeden pro celou zbývající část výpisu, aby
                # seznam čekajících transakcí odpovídal součtům pod ním - ty se
                # počítají z téhož snímku o pár řádků níž.
                with droid_chain.lock:
                    snapshot_mempool = list(droid_chain.unconfirmed_transactions)
                    snapshot_immature = list(droid_chain.immature_rewards.values())
                    confirmed_balance = droid_chain.get_confirmed_balance(address)
                pending_list = [
                    tx for tx in snapshot_mempool
                    if tx.from_address == address or tx.to_address == address
                ]
                if pending_list:
                    print(f"\n{Fore.YELLOW}--- Čekající transakce (mempool) ---{Style.RESET_ALL}")
                    for tx in pending_list:
                        if tx.from_address == address:
                            direction = f"{Fore.RED}Odesláno{Style.RESET_ALL}"
                        else:
                            direction = f"{Fore.GREEN}Přijato{Style.RESET_ALL}"
                        print(f"TX ID: {Fore.CYAN}{tx.tx_id}{Style.RESET_ALL}")
                        print(f" Blok: {Fore.YELLOW}čekající{Style.RESET_ALL}")
                        print(f" Potvrzení: {Fore.RED}0 (čekající){Style.RESET_ALL}")
                        print(f" Směr: {direction}")
                        print(f" Od: {tx.from_address}")
                        print(f" Komu: {tx.to_address}")
                        print(f" Částka: {format(Decimal(tx.amount) / Decimal(10 ** DECIMALS), f'.{DECIMALS}f')} {TICKER}")
                        print(f" Poplatek: {format(Decimal(tx.fee) / Decimal(10 ** DECIMALS), f'.{DECIMALS}f')} {TICKER}")
                        print(f" Čas: {time.strftime('%d.%m.%Y %H:%M:%S UTC+00:00', time.gmtime(tx.timestamp))}")
                        print("-" * 20)
                        
                # confirmed_balance a snapshot_immature pocházejí ze snímku
                # pořízeného výš (OPRAVA AUDIT-2026-5), ne z živého stavu.
                immature_sum = sum(reward['amount'] for reward in snapshot_immature if reward['address'] == address)
                total_coins = sent_amount + received_amount
                total_count = sent_count + received_count

                # OPRAVA S-5 (Nález 6): volba 13 jako jediná nazývala NEZRALÉ
                # COINBASE ODMĚNY "Nepotvrzeným zůstatkem" a čekající odchozí
                # platby v tomhle bloku nezobrazovala vůbec. Uživatel, který
                # právě odeslal platbu, tak četl "Nepotvrzený zůstatek: 200",
                # ačkoli nepotvrzeno měl -7. Názvosloví i výpočet jsou nově
                # shodné s volbami 1 a 9 - u finančních částek se dvě obrazovky
                # téhož uzlu nesmějí lišit ani slovem.
                pending_outgoing_sum = 0
                pending_incoming_sum = 0
                for tx in snapshot_mempool:
                    if tx.from_address == address:
                        pending_outgoing_sum += tx.amount + tx.fee
                    if tx.to_address == address:
                        pending_incoming_sum += tx.amount
                total_balance = confirmed_balance - pending_outgoing_sum

                confirmed_dec = Decimal(confirmed_balance) / Decimal(10 ** DECIMALS)
                immature_dec = Decimal(immature_sum) / Decimal(10 ** DECIMALS)
                total_balance_dec = Decimal(total_balance) / Decimal(10 ** DECIMALS)
                pending_outgoing_dec = Decimal(pending_outgoing_sum) / Decimal(10 ** DECIMALS)
                pending_incoming_dec = Decimal(pending_incoming_sum) / Decimal(10 ** DECIMALS)
                sent_dec = Decimal(sent_amount) / Decimal(10 ** DECIMALS)
                received_dec = Decimal(received_amount) / Decimal(10 ** DECIMALS)
                total_coins_dec = Decimal(total_coins) / Decimal(10 ** DECIMALS)
                
                print(f"\n{Fore.YELLOW}--- Statistiky historie transakcí ---{Style.RESET_ALL}")
                print(f"Potvrzený zůstatek: {Fore.MAGENTA}{format(confirmed_dec, f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                if immature_sum > 0:
                    print(f"Nezralé odměny: {Fore.BLUE}{format(immature_dec, f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                    print(f" {Fore.YELLOW}Pozor:{Style.RESET_ALL} nezralé odměny se na adresu připíšou až po {COINBASE_MATURITY} blocích.")
                print(f"Celkový zůstatek: {Fore.MAGENTA}{format(total_balance_dec, f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                if pending_outgoing_sum > 0:
                    print(f"Pending (-): {Fore.RED}-{format(pending_outgoing_dec, f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                if pending_incoming_sum > 0:
                    print(f"Pending (+): {Fore.GREEN}+{format(pending_incoming_dec, f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                print(f"Odeslané mince: {Fore.RED}{format(sent_dec, f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                print(f"Přijaté mince: {Fore.GREEN}{format(received_dec, f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                print(f"Součet mincí: {Fore.CYAN}{format(total_coins_dec, f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                print(f"Odeslané transakce: {Fore.RED}{sent_count}{Style.RESET_ALL}")
                print(f"Přijaté transakce: {Fore.GREEN}{received_count}{Style.RESET_ALL}")
                print(f"Celkový počet: {Fore.CYAN}{total_count}{Style.RESET_ALL}")
                if pending_list:
                    print(f"Čekající transakce: {Fore.YELLOW}{len(pending_list)}{Style.RESET_ALL}")
                    
            elif choice == "14":
                total_supply = droid_chain.get_total_supply()
                max_supply = MAX_SUPPLY
                print(f"\n{Fore.YELLOW}--- Celková nabídka mincí ---{Style.RESET_ALL}")
                print(f" Celková nabídka: {Fore.CYAN}{format(Decimal(total_supply) / Decimal(10 ** DECIMALS), f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                print(f" Maximální nabídka: {Fore.CYAN}{format(Decimal(max_supply) / Decimal(10 ** DECIMALS), f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                
                print()
                miner_addr = input("Zadejte ADRESU těžaře pro zobrazení coinbase odměn: ").strip()
                if miner_addr:
                    if not is_valid_address(miner_addr):
                        print(f"{Fore.RED}Chyba: Neplatný formát adresy.{Style.RESET_ALL}")
                    else:
                        print(f"\n{Fore.YELLOW}--- Historie coinbase odměn pro adresu '{miner_addr}' ---{Style.RESET_ALL}")
                        locked_rewards_count = 0
                        unlocked_rewards_count = 0
                        locked_coins = 0
                        unlocked_coins = 0
                        
                        # OPRAVA V-2 (audit 3. 10. 2026, nález 2): conn.close()
                        # tu leželo jako obyčejný řádek za smyčkou, ve které běží
                        # json.loads() i indexace dictu - tedy přesně vzorec, který
                        # OPRAVA AUDIT-11 (volba 10, find_transaction_by_id)
                        # a OPRAVA A-07 (volba 13) odstranily jinde. Volba 14 jako
                        # jediná adresní obrazovka zůstala bez try/finally.
                        # Naměřeno nad jediným poškozeným řádkem: 41 deskriptorů
                        # po 20 voláních, tedy dva na volání (soubor + WAL) -
                        # shodné s měřením u OPRAVY AUDIT-11.
                        conn = None
                        coinbase_txs = []
                        try:
                            conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
                            conn.execute("PRAGMA journal_mode=WAL;")
                            c = conn.cursor()
                            c.execute("SELECT block_index, timestamp, transactions FROM blocks ORDER BY block_index ASC")

                            for row in c:
                                b_idx = row[0]
                                b_ts = row[1]
                                b_txs = json.loads(row[2])
                                if b_txs:
                                    cb_tx = b_txs[0]
                                    if cb_tx['from_address'] == "COINBASE" and cb_tx['to_address'] == miner_addr:
                                        coinbase_txs.append((b_idx, b_ts, cb_tx))
                        finally:
                            if conn is not None:
                                try:
                                    conn.close()
                                except Exception:
                                    pass
                        
                        if not coinbase_txs:
                            print(f"{Fore.CYAN}Žádné coinbase odměny pro tuto adresu.{Style.RESET_ALL}")
                        else:
                            for b_idx, b_ts, cb_tx in coinbase_txs:
                                # Druhý systém potvrzení: počet bloků NAD tímto
                                # blokem, vrchol řetězce = 0. Odpovídá pravidlu
                                # zrání v konsenzu:
                                #   target_index = block.index - COINBASE_MATURITY
                                # (update_state_with_block). Odměna s 1000+ bloky
                                # nad sebou je utratitelná, protože ji reorg už
                                # nemůže smazat.
                                #
                                # NESJEDNOCOVAT s get_confirmations_by_index(),
                                # která počítá hloubku včetně bloku samotného
                                # (vrchol = 1) a slouží volbám 10-13 pro
                                # definitivnost. Použití té metody by tu přidalo
                                # +1 a odměna by se tvářila jako odemčená o blok
                                # dřív, než ji konsenzus zpřístupní.
                                # Podrobné odvození je u CONFIRMATIONS_THRESHOLD.
                                confirmations = droid_chain.max_block_index - b_idx
                                if confirmations < COINBASE_MATURITY:
                                    status = f"{Fore.RED}Uzamčeno{Style.RESET_ALL}"
                                    conf_str = f"{Fore.RED}{confirmations}/{COINBASE_MATURITY}{Style.RESET_ALL}"
                                    locked_rewards_count += 1
                                    locked_coins += cb_tx['amount']
                                else:
                                    status = f"{Fore.GREEN}Odemčeno{Style.RESET_ALL}"
                                    conf_str = f"{Fore.GREEN}{COINBASE_MATURITY}/{COINBASE_MATURITY}{Style.RESET_ALL}"
                                    unlocked_rewards_count += 1
                                    unlocked_coins += cb_tx['amount']
                                    
                                print(f"TX ID: {Fore.CYAN}{cb_tx['tx_id']}{Style.RESET_ALL}")
                                print(f" Blok: #{b_idx}")
                                print(f" Potvrzení: {conf_str}")
                                print(f" Stav: {status}")
                                print(f" Od: {cb_tx['from_address']}")
                                print(f" Komu: {cb_tx['to_address']}")
                                print(f" Částka: {format(Decimal(cb_tx['amount']) / Decimal(10 ** DECIMALS), f'.{DECIMALS}f')} {TICKER}")
                                print(f" Čas: {time.strftime('%d.%m.%Y %H:%M:%S UTC+00:00', time.gmtime(b_ts))}")
                                print("-" * 20)
                                
                            print(f"\n{Fore.YELLOW}--- Statistiky coinbase odměn ---{Style.RESET_ALL}")
                            print(f"Uzamčené odměny: {Fore.RED}{locked_rewards_count}{Style.RESET_ALL}")
                            print(f"Odemčené odměny: {Fore.GREEN}{unlocked_rewards_count}{Style.RESET_ALL}")
                            print(f"Uzamčené mince: {Fore.RED}{format(Decimal(locked_coins) / Decimal(10**DECIMALS), f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                            print(f"Odemčené mince: {Fore.GREEN}{format(Decimal(unlocked_coins) / Decimal(10**DECIMALS), f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                            print(f"Celkový počet odměn: {Fore.CYAN}{locked_rewards_count + unlocked_rewards_count}{Style.RESET_ALL}")
                            print(f"Celkový počet mincí: {Fore.CYAN}{format(Decimal(locked_coins + unlocked_coins) / Decimal(10**DECIMALS), f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                
            elif choice == "15":
                # OPRAVA AUDIT-15: tady se jako na jediném čtecím místě sahalo
                # na ŽIVÝ seznam p2p_node.peers bez peers_lock - jednou v `if`
                # a podruhé v `for`. Všechna ostatní místa (např. volba 17 hned
                # níž) si zámek berou a pořizují snímek. U seznamu to sice
                # výjimku nevyhodí, ale souběžný zápis z P2P vlákna může položku
                # přeskočit, takže výpis stavu uzlů vyšel neúplný. Navíc se mezi
                # `if` a `for` mohl seznam změnit, takže se testovalo něco
                # jiného, než se pak vypisovalo.
                with p2p_node.peers_lock:
                    peers_snapshot = list(p2p_node.peers)
                if not peers_snapshot:
                    print(f"\n{Fore.YELLOW}Žádné uzly nejsou uloženy.{Style.RESET_ALL}")
                else:
                    print(f"\n{Fore.YELLOW}--- Stav známých uzlů ---{Style.RESET_ALL}")
                    online_peers = p2p_node.get_online_peers()
                    for peer in peers_snapshot:
                        if peer in online_peers:
                            status = f"{Fore.GREEN}[ONLINE]{Style.RESET_ALL}"
                        else:
                            status = f"{Fore.RED}[OFFLINE]{Style.RESET_ALL}"
                        peer_str = f"[{peer[0]}]:{peer[1]}" if ':' in peer[0] else f"{peer[0]}:{peer[1]}"
                        print(f"  {Fore.CYAN}{peer_str}{Style.RESET_ALL} {status}")
                        
            elif choice == "16":
                peer_ip = input("Zadejte IP adresu uzlu k přidání: ").strip()
                # OPRAVA T-4 (Nález 1): adresa od uživatele se kanonizuje hned,
                # ne až někde uvnitř P2P vrstvy. Tohle je jediné místo, kde do
                # tabulky peerů vstupuje libovolný text, takže rozepsaná IPv6
                # odsud vytvářela záznam, se kterým se kanonická adresa
                # z accept() nikdy nespárovala. connect_to_peer() normalizuje
                # taky, ale uživatel má vidět ten tvar, který se opravdu uloží.
                peer_ip = normalize_ip_str(peer_ip)
                try:
                    peer_port = int(input("Zadejte port uzlu: ").strip())
                    # OPRAVA AUDIT-14: rozsah portu se tu nekontroloval vůbec.
                    # main() ho přitom kontroluje výslovně (OPRAVA AUDIT-5)
                    # a ze stejného důvodu: 0, -1 i 99999 se jinak projeví až
                    # obecnou hláškou "Připojení selhalo" z connect_to_peer(),
                    # která svádí k tomu hledat chybu na druhé straně.
                    if not (1 <= peer_port <= 65535):
                        print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Port {peer_port} je mimo povolený rozsah 1-65535.")
                        continue
                    new_peer = (peer_ip, peer_port)
                    print(f"{Fore.YELLOW}Pokouším se připojit k uzlu {new_peer}...{Style.RESET_ALL}")
                    # OPRAVA D-08: ručně zadaný peer je chráněný - nevytlačí ho
                    # síťový provoz a neplatí pro něj limit podsítě. Je to
                    # výslovné rozhodnutí uživatele a zároveň cesta, jak uzel
                    # dostat zpátky do sítě, kdyby mu tabulku obsadil útočník.
                    if p2p_node.connect_to_peer(new_peer, manual=True):
                        print(f"{Fore.GREEN}Požadavek na propojení odeslán! (Zkontrolujte stav uzlů přes volbu 15){Style.RESET_ALL}")
                    else:
                        print(f"{Fore.RED}Připojení selhalo. Uzel je možná offline, již existuje, nebo je blokován.{Style.RESET_ALL}")
                except ValueError:
                    print(f"{Fore.RED}Neplatný formát portu.{Style.RESET_ALL}")
                    
            elif choice == "17":
                with p2p_node.peers_lock:
                    current_peers = list(p2p_node.peers)
                if current_peers:
                    print("   --- Uložené uzly ---")
                    for i, peer in enumerate(current_peers, 1):
                        peer_str = f"[{peer[0]}]:{peer[1]}" if ':' in peer[0] else f"{peer[0]}:{peer[1]}"
                        print(f" {i}. {peer_str}")
                    try:
                        idx = int(input("   Zadejte číslo uzlu k odstranění: ").strip())
                        if 1 <= idx <= len(current_peers):
                            peer_to_remove = current_peers[idx - 1]
                            peer_str_rm = f"[{peer_to_remove[0]}]:{peer_to_remove[1]}" if ':' in peer_to_remove[0] else f"{peer_to_remove[0]}:{peer_to_remove[1]}"
                            block_ip = input(f"Chcete IP adresu uzlu ({peer_to_remove[0]}) před smazáním i zablokovat? (a/n): ").strip().lower()
                            with p2p_node.peers_lock:
                                if peer_to_remove in p2p_node.peers:
                                    p2p_node.peers.remove(peer_to_remove)
                                # OPRAVA U-20 (nález 2): evidence je klíčovaná
                                # dvojicí (IP, node_id), takže se maže záznam
                                # SMAZANÉHO uzlu. Pop podle samotné IP by na
                                # adrese s víc uzly vyhodil i ten, který si
                                # uživatel ponechal.
                                #
                                # OPRAVA D-08: s peerem musí zmizet i jeho skóre,
                                # ochrana a záznam v TTL evidenci - jinak by po
                                # smazání zůstal chráněný "duch", který blokuje
                                # místo v tabulce a nedá se vytlačit.
                                p2p_node._forget_listen_port_locked(peer_to_remove[0], peer_to_remove[1])
                                p2p_node.peer_last_seen.pop(peer_to_remove, None)
                                p2p_node.protected_peers.discard(peer_to_remove)
                            # OPRAVA AUDIT-2026-8 (nález N3): ruční zásah z menu se na disk
                            # propíše OKAMŽITĚ (force=True), stejně jako u
                            # blacklistu. Dávkuje se jen to, co přichází ze sítě.
                            p2p_node.mark_peers_dirty()
                            p2p_node.flush_peers(force=True)
                            if block_ip == 'a':
                                # Ruční ban od uživatele je jediný trvalý (duration=None).
                                p2p_node.ban_peer(peer_to_remove[0], "ruční zablokování uživatelem", duration=None)
                                print(f"{Fore.GREEN}Uzel {peer_str_rm} byl smazán a jeho IP zablokována.{Style.RESET_ALL}")
                            else:
                                print(f"{Fore.GREEN}Uzel {peer_str_rm} byl smazán.{Style.RESET_ALL}")
                        else:
                            print(f"{Fore.RED}Neplatné číslo uzlu.{Style.RESET_ALL}")
                    except ValueError:
                        print(f"{Fore.RED}Neplatný vstup.{Style.RESET_ALL}")
                else:
                    print(f"{Fore.YELLOW}Žádné uzly nejsou uloženy.{Style.RESET_ALL}")
                    
            elif choice == "18":
                # OPRAVA #1: blacklist je slovník {ip: expirace}; u dočasných banů
                # ukazujeme zbývající čas, u ručních "trvale".
                with p2p_node.blacklist_lock:
                    blacklist_snapshot = dict(p2p_node.blacklist)
                if blacklist_snapshot:
                    print("--- Zablokované IP adresy ---")
                    blocked_list = list(blacklist_snapshot.keys())
                    now_ts = time.time()
                    for i, ip in enumerate(blocked_list, 1):
                        expiry = blacklist_snapshot[ip]
                        if expiry is None:
                            print(f" {i}. {ip}  (trvale)")
                        else:
                            remaining = max(0, int(expiry - now_ts))
                            print(f" {i}. {ip}  (zbývá {remaining // 60} min {remaining % 60} s)")
                    try:
                        idx = int(input("   Zadejte číslo IP adresy k odblokování: ").strip())
                        if 1 <= idx <= len(blocked_list):
                            ip_to_remove = blocked_list[idx - 1]
                            confirm = input(f"\nChcete tuto IP adresu ({ip_to_remove}) odblokovat? (a/n): ").strip().lower()
                            if confirm == 'a':
                                with p2p_node.blacklist_lock:
                                    p2p_node.blacklist.pop(ip_to_remove, None)
                                    p2p_node.blacklist_dirty = True
                                # OPRAVA G-06: rozhodnutí uživatele se ukládá
                                # okamžitě, ne až s dávkou.
                                p2p_node.flush_blacklist(force=True)
                                print(f"{Fore.GREEN}IP adresa {ip_to_remove} byla odblokována.{Style.RESET_ALL}")
                            else:
                                print(f"{Fore.YELLOW}Akce zrušena. IP adresa zůstává zablokovaná.{Style.RESET_ALL}")
                        else:
                            print(f"{Fore.RED}Neplatné číslo IP adresy.{Style.RESET_ALL}")
                    except ValueError:
                        print(f"{Fore.RED}Neplatný vstup.{Style.RESET_ALL}")
                else:
                    print(f"{Fore.YELLOW}Žádné IP adresy nejsou zablokovány.{Style.RESET_ALL}")
                    
            elif choice == "19":
                show_p2p_log()
                
            elif choice == "20":
                p2p_node.running = False
                # ETAPA 1: perzistentní spojení je potřeba explicitně zavřít,
                # jinak čtecí vlákna visí až do timeoutu.
                p2p_node.close_all_connections()
                # OPRAVA G-06: zápis blacklistu je nově dávkovaný, takže se
                # při vypnutí musí dotlačit na disk ručně - jinak by se ztratily
                # bany udělené od posledního flushe.
                p2p_node.flush_blacklist(force=True)
                # OPRAVA AUDIT-2026-8 (nález N3): totéž pro tabulku peerů. save_data() níž
                # ji sice zapíše taky, ale tohle drží invariant "po čistém
                # vypnutí není nic rozpracovaného" nezávisle na tom, jestli
                # save_data() doběhne.
                p2p_node.flush_peers(force=True)
                print(f"\n{Fore.YELLOW}Ukládám a vypínám...{Style.RESET_ALL}")
                save_data(droid_chain, wallets, password, p2p_node.peers_snapshot(), full=True, save_wallets=True)
                # ZMĚNA 2: mempool.db se při vypnutí už NEMAŽE. Celý mempool
                # (všechny transakce, ne jen transakce tohoto uzlu) zůstává
                # uložený a při dalším startu se načte a ověří proti aktuálnímu
                # blockchainu (viz Blockchain.revalidate_stored_mempool).
                uloz_mempool_pri_vypnuti(droid_chain)
                break
                
        except KeyboardInterrupt:
            print(f"\n{Fore.YELLOW}Ukončuji program (CTRL+C)...{Style.RESET_ALL}")
            if 'p2p_node' in globals() and p2p_node:
                p2p_node.running = False
                # ETAPA 1: perzistentní spojení je potřeba explicitně zavřít,
                # jinak čtecí vlákna visí až do timeoutu.
                p2p_node.close_all_connections()
                # OPRAVA G-06: dotlačení dávkovaného blacklistu na disk.
                p2p_node.flush_blacklist(force=True)
                # OPRAVA AUDIT-2026-8 (nález N3): totéž pro tabulku peerů.
                p2p_node.flush_peers(force=True)
            save_data(droid_chain, wallets, password, p2p_node.peers_snapshot() if 'p2p_node' in globals() and p2p_node else [], full=True, save_wallets=True)
            # ZMĚNA 2: ani při CTRL+C se mempool.db už NEMAŽE - stejně jako
            # u volby 20 zůstává celý mempool uložený pro další start.
            uloz_mempool_pri_vypnuti(droid_chain)
            break
        except Exception as e:
            print(f"{Fore.RED}Došlo k chybě: {e}{Style.RESET_ALL}")

if __name__ == "__main__":
    # OPRAVA B-5: kontrola prostředí patří do vstupního bodu, ne do main().
    # Přepínač se z argv odstraní, aby main() dál mohl brát port z argv[1].
    povolit_jakoukoli_platformu = '--allow-any-platform' in sys.argv
    if povolit_jakoukoli_platformu:
        sys.argv = [a for a in sys.argv if a != '--allow-any-platform']
    enforce_mobile_environment(allow_any=povolit_jakoukoli_platformu)
    main()
